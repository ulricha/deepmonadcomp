{-# LANGUAGE ConstraintKinds      #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE UndecidableInstances #-}

-- Try to get rid of the Fun type and inline functions directly on the
-- main ast type

import           Control.Applicative
import           Control.Monad
import           Control.Monad.ConstrainedNormal

import           Data.Text                       (Text)
import           Prelude                         hiding (concatMap)
import           Text.PrettyPrint.ANSI.Leijen

--------------------------------------------------------------------------------
-- Typed query AST

data Exp :: * -> * where
  BoolE       :: Bool    -> Exp Bool
  IntegerE    :: Integer -> Exp Integer
  ListE       :: [Exp a] -> Exp (QList a)

  AndE        :: Exp (QList QBool) -> Exp QBool
  SngE        :: Exp a -> Exp (QList a)
  AppendE     :: Exp (QList a) -> Exp (QList a) -> Exp (QList a)
  ConcatMapE  :: Exp (a -> QList b) -> Exp (QList a) -> Exp (QList b)
  LamE        :: (Reify a, Reify b)  => (Exp a -> Exp b) -> Exp (a -> b)
  VarE        :: (Reify a)           => Integer -> Exp a

data Type :: * -> * where
  BoolT     :: Type QBool
  IntegerT  :: Type QInt
  ListT     :: (Reify a)          => Type a -> Type (QList a)
  ArrowT    :: (Reify a,Reify b)  => Type a -> Type b -> Type (a -> b)

instance Pretty (Type a) where
    pretty BoolT          = text "Bool"
    pretty IntegerT       = text "Integer"
    pretty (ListT t)      = brackets $ pretty t
    pretty (ArrowT t1 t2) = parens $ pretty t1 <+> text "->" <+> pretty t2

-- | A combination of column names that form a candidate key
newtype Key = Key [String] deriving (Eq, Ord, Show)

-- | Is the table guaranteed to be not empty?
data Emptiness = NonEmpty
               | PossiblyEmpty
               deriving (Eq, Ord, Show)

-- | Catalog information hints that users may give to DSH
data TableHints = TableHints
    { keysHint     :: [Key]
    , nonEmptyHint :: Emptiness
    } deriving (Eq, Ord, Show)

data Table = TableDB String TableHints

--------------------------------------------------------------------------------
-- Classes

class Reify a where
  reify :: a -> Type a

class BasicType a where

class TA a where

class View a where
  type ToView a
  view :: a -> ToView a

class Reify (Rep a) => Q a where
    type Rep a
    wrap   :: Exp (Rep a) -> a
    unwrap :: a -> Exp (Rep a)

--------------------------------------------------------------------------------
-- Reify instances

instance Reify QBool where
  reify _ = BoolT

instance Reify QInt where
  reify _ = IntegerT

instance (Reify a) => Reify (QList a) where
    reify _ = ListT (reify (undefined :: a))

instance (Reify a, Reify b) => Reify (a -> b) where
    reify _ = ArrowT (reify (undefined :: a)) (reify (undefined :: b))

newtype QInt      = QInt (Exp (Rep QInt))
newtype QBool     = QBool (Exp (Rep QBool))
newtype QList a   = QList (Exp (Rep (QList a)))

instance Q QInt where
    type Rep QInt = QInt

    wrap e = QInt e
    unwrap (QInt e) = e

instance Q QBool where
    type Rep QBool = QBool

    wrap e = QBool e
    unwrap (QBool e) = e

instance Q a => Q (QList a) where
    type Rep (QList a) = QList (Rep a)
    wrap e             = QList e
    unwrap (QList e)   = e

instance (Q a, Q (Rep a)) => Q (NM Q QList a) where
    type (Rep (NM Q QList a)) = QList (Rep a)
    wrap   = liftList . wrap
    unwrap = unwrap . lowerList

--------------------------------------------------------------------------------
-- Convert between actual list ASTs and the deep embedding of monadic
-- list computations

liftList :: Q a => QList a -> NM Q QList a
liftList = liftNM

lowerList :: (Q a, Q (Rep a)) => NM Q QList a -> QList a
lowerList = lowerNM sngRep bindRep

--------------------------------------------------------------------------------
-- List combinators on actual list ASTs

concatMapRep :: (Q a, Q b) => (a -> QList b) -> QList a -> QList b
concatMapRep f as = wrap $ ConcatMapE (LamE $ toLam f) (unwrap as)

bindRep :: (Q a, Q b) => QList a -> (a -> QList b) -> QList b
bindRep = flip concatMapRep

sngRep :: (Q a, Q (Rep a)) => a -> QList a
sngRep x = wrap $ SngE (unwrap x)

andRep :: QList QBool -> QBool
andRep bs = wrap $ AndE (unwrap bs)

appendRep :: Q a => QList a -> QList a -> QList a
appendRep as bs = wrap $ AppendE (unwrap as) (unwrap bs)

toLam :: (Q a, Q b) => (a -> b) -> Exp (Rep a) -> Exp (Rep b)
toLam f = unwrap . f . wrap

--------------------------------------------------------------------------------
-- User-facing list combinators on monadic lists

type QListM a = NM Q QList a

sng :: (Q a, Q (Rep a)) => a -> QListM a
sng = liftList . sngRep

and :: QListM QBool -> QBool
and = andRep . lowerList

append :: (Q a, Q (Rep a)) => QListM a -> QListM a -> QListM a
append as1 as2 = liftList $ appendRep (lowerList as1) (lowerList as2)

concatMap :: (Q a, Q (Rep a), Q b, Q (Rep b))
          => (a -> QListM b) -> QListM a -> QListM b
concatMap f as = liftList $ concatMapRep f' (lowerList as)
  where
    f' a = lowerList $ f a

--------------------------------------------------------------------------------
-- Literal values in queries

{-
class QLit a where
    type Lit a
    litQ :: a -> Lit a

instance QLit Bool where
    type Lit Bool = Rep QBool
    litQ = QBool . BoolE 
-}
    
-- [a] -> QListM (
