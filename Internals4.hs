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
  BoolE       :: Bool    -> Exp QBool
  IntegerE    :: Integer -> Exp QInt
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

-- Restrict type variables in queries (?) to query types
class Reify (Rep a) => QT a where
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

-- We have type-specific wrappers around the same AST. The motivation
-- is to have a distinct type for query lists so that we can define a
-- monad instance for them.
newtype QInt      = QInt (Exp (Rep QInt))
newtype QBool     = QBool (Exp (Rep QBool))
newtype QList a   = QList (Exp (Rep (QList a)))

instance QT QInt where
    type Rep QInt = QInt

    wrap e = QInt e
    unwrap (QInt e) = e

instance QT QBool where
    type Rep QBool = QBool

    wrap e = QBool e
    unwrap (QBool e) = e

instance QT a => QT (QList a) where
    type Rep (QList a) = QList (Rep a)
    wrap e             = QList e
    unwrap (QList e)   = e

instance (QT a, QT (Rep a)) => QT (NM QT QList a) where
    type (Rep (NM QT QList a)) = QList (Rep a)
    wrap   = liftList . wrap
    unwrap = unwrap . lowerList

--------------------------------------------------------------------------------
-- Convert between actual list ASTs and the deep embedding of monadic
-- list computations

liftList :: QT a => QList a -> NM QT QList a
liftList = liftNM

lowerList :: (QT a, QT (Rep a)) => NM QT QList a -> QList a
lowerList = lowerNM sngRep bindRep

--------------------------------------------------------------------------------
-- List combinators on actual list ASTs

concatMapRep :: (QT a, QT b) => (a -> QList b) -> QList a -> QList b
concatMapRep f as = wrap $ ConcatMapE (LamE $ toLam f) (unwrap as)

bindRep :: (QT a, QT b) => QList a -> (a -> QList b) -> QList b
bindRep = flip concatMapRep

sngRep :: (QT a, QT (Rep a)) => a -> QList a
sngRep x = wrap $ SngE (unwrap x)

andRep :: QList QBool -> QBool
andRep bs = wrap $ AndE (unwrap bs)

appendRep :: QT a => QList a -> QList a -> QList a
appendRep as bs = wrap $ AppendE (unwrap as) (unwrap bs)

toLam :: (QT a, QT b) => (a -> b) -> Exp (Rep a) -> Exp (Rep b)
toLam f = unwrap . f . wrap

--------------------------------------------------------------------------------
-- User-facing list combinators on monadic lists

type QListM a = NM QT QList a

sng :: (QT a, QT (Rep a)) => a -> QListM a
sng = liftList . sngRep

and :: QListM QBool -> QBool
and = andRep . lowerList

append :: (QT a, QT (Rep a)) => QListM a -> QListM a -> QListM a
append as1 as2 = liftList $ appendRep (lowerList as1) (lowerList as2)

concatMap :: (QT a, QT (Rep a), QT b, QT (Rep b))
          => (a -> QListM b) -> QListM a -> QListM b
concatMap f as = liftList $ concatMapRep f' (lowerList as)
  where
    f' a = lowerList $ f a

--------------------------------------------------------------------------------
-- Literal values in queries

{-

Problem: need a way to bring literal values into queries:

toQ :: [a] -> QListM (Foo a)

=> need a mapping between regular haskell types and values and Q types

[a]  --> QListM a
Int  --> QInt
Bool --> QBool

=> Type class

-}

{-        
class Q a where
    type QRep a
    toQ   :: a -> QRep a
    fromQ :: QRep a -> Maybe a

instance Q Bool where
    type QRep Bool = QBool
    toQ b = QBool $ BoolE b
    fromQ (QBool (BoolE b)) = Just b
    fromQ _                 = Nothing

instance Q Integer where
    type QRep Integer = QInt
    toQ b = QInt $ IntegerE b
    fromQ (QInt (IntegerE b)) = Just b
    fromQ _                   = Nothing

instance Q a => Q [a] where
    type QRep [a] = QListM a
    toQ as = liftList $ QList $ ListE (map toQ as)
    fromQ _ = undefined
-}


{-

class QLit a where
    type Lit a
    litQ :: a -> Lit a

instance QLit Bool where
    type Lit Bool = Rep QBool
    litQ :: Bool -> Lit Bool
    litQ = QBool . BoolE 

instance QLit Integer where
    type Lit Integer = Rep QInt
    litQ :: Integer -> Lit Integer
    litQ = QInt . IntegerE

instance QLit a => QLit [a] where
    type Lit [a] = QList (Lit a)
    litQ :: [a] -> Lit [a]
    litQ xs = wrap $ ListE $ map litQ xs

-}
    
-- [a] -> QListM (
