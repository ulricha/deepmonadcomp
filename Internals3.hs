{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TemplateHaskell  #-}

-- Try to get rid of the Fun type and inline functions directly on the
-- main ast type

import           Control.Applicative
import           Control.Monad
import           Control.Monad.ConstrainedNormal

import           Data.Text                        (Text)
import           Text.PrettyPrint.ANSI.Leijen
import           Prelude hiding (concatMap)

data Exp a where
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

--------------------------------------------------------------------------------
-- Classes

class Reify a where
  reify :: a -> Type a

class BasicType a where

class TA a where

class View a where
  type ToView a
  view :: a -> ToView a

{-
pairE :: (Reify a, Reify b) => Exp a -> Exp b -> Exp (a, b)
pairE a b = TupleConstE (Tuple2E a b)

tripleE :: (Reify a, Reify b, Reify c) => Exp a -> Exp b -> Exp c -> Exp (a, b, c)
tripleE a b c = TupleConstE (Tuple3E a b c)
-}

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

-- Reify instances

instance Reify QBool where
  reify _ = BoolT

instance Reify QInt where
  reify _ = IntegerT

instance (Reify a) => Reify (QList a) where
    reify _ = ListT (reify (undefined :: a))

instance (Reify a, Reify b) => Reify (a -> b) where
    reify _ = ArrowT (reify (undefined :: a)) (reify (undefined :: b))

instance Reify a => Reify (NM Q QList a) where
    -- reify _ = ListT (reify (undefined :: a))
    reify _ = reify (undefined :: a)


-- Utility functions

-- * Generate Reify instances for tuple types
-- mkReifyInstances 16

{-
[ undefined
| x <- xs :: Q (QList a)
]
-}

-- QInt: A query that returns an int
-- Exp *Int: A query AST that returns an int
-- Q*: type-specific wrappers around query ASTs

newtype QInt      = QInt (Exp (Rep QInt))
newtype QBool     = QBool (Exp (Rep QBool))
newtype QList a   = QList (Exp (Rep (QList a)))

class Reify (Rep a) => Q a where
    type Rep a
    wrap   :: Exp (Rep a) -> a
    unwrap :: a -> Exp (Rep a)

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

{-
instance (Reify a) => Reify (NM Q QList a) where
    reify _ = ListT (reify (undefined :: a))
-}
    
liftList :: Q a => QList a -> NM Q QList a
liftList = liftNM 

lowerList :: (Q a, Q (Rep a)) => NM Q QList a -> QList a
lowerList = lowerNM sng bind

concatMap :: (Q a, Q b) => (a -> QList b) -> QList a -> QList b
concatMap f as = wrap $ ConcatMapE (LamE $ toLam f) (unwrap as)

bind :: (Q a, Q b) => QList a -> (a -> QList b) -> QList b
bind = flip concatMap

sng :: (Q a, Q (Rep a)) => a -> QList a
sng x = wrap $ SngE (unwrap x)

toLam :: (Q a, Q b) => (a -> b) -> Exp (Rep a) -> Exp (Rep b)
toLam f = unwrap . f . wrap

{-
and :: QList QBool -> QBool
and bs = wrap $ AppE And (unwrap bs)

append :: Query a => QList a -> QList a -> QList a
append as bs = wrap $ AppE Append (PairE (unwrap as) (unwrap bs))


mapQ :: (Query a, Query b) => (a -> b) -> QList a -> QList b
mapQ = undefined

-}

{-
instance Monad QList where
    return = sng
    (>>=)  = concatMapQ
-}
