{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs            #-}
{-# LANGUAGE TypeFamilies     #-}
{-# LANGUAGE TemplateHaskell  #-}

import           Control.Applicative
import           Control.Monad
-- import           Control.Monad.ConstrainedNormal

import           Data.Text                        (Text)
import           Text.PrettyPrint.ANSI.Leijen

data Fun :: * -> * -> * where
    And       :: Fun (QList QBool) QBool
    Sng       :: Fun a (QList a)

data Fun2 :: * -> * -> * -> * where
    Append    :: Fun2 (QIList a) (QIList a) (QIList a)
    ConcatMap :: Fun2 (a -> QList b) (QList a) (QList b)

data Exp a where
  BoolE       :: Bool    -> Exp Bool
  IntegerE    :: Integer -> Exp Integer
  AppE        :: (Reify a, Reify b)  => Fun a b -> Exp a -> Exp b
  AppE2       :: (Reify a, Reify b, Reify c) => Fun2 a b c -> Exp a -> Exp b -> Exp c
  LamE        :: (Reify a, Reify b)  => (Exp a -> Exp b) -> Exp (a -> b)
  VarE        :: (Reify a)           => Integer -> Exp a

data Type :: * -> * where
  BoolT     :: Type QBool
  IntegerT  :: Type QInt
  ListT     :: (Reify a)          => Type a -> Type (QList a)
  ArrowT    :: (Reify a,Reify b)  => Type a -> Type b -> Type (a -> b)
  PairT     :: (Reify a, Reify b) => Type a -> Type b -> Type (QPair a b)

instance Pretty (Type a) where
    pretty BoolT          = text "Bool"
    pretty IntegerT       = text "Integer"
    pretty (ListT t)      = brackets $ pretty t
    pretty (ArrowT t1 t2) = parens $ pretty t1 <+> text "->" <+> pretty t2
    pretty (PairT t1 t2)  = tupled [pretty t1, pretty t2]

--------------------------------------------------------------------------------
-- Classes

class Reify a where
  reify :: a -> Type a

class (Reify (Rep a)) => QA a where
  type Rep a
  toExp :: a -> Exp (Rep a)
  frExp :: Exp (Rep a) -> a

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

instance (Reify a, Reify b) => Reify (QPair a b) where
  reify _ = PairT (reify (undefined :: a)) (reify (undefined :: b))

instance (Reify a, Reify b) => Reify (a -> b) where
  reify _ = ArrowT (reify (undefined :: a)) (reify (undefined :: b))

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

newtype QInt      = QInt (Exp QInt)
newtype QBool     = QBool (Exp QBool)
newtype QPair a b = QPair (Exp (QPair a b))
newtype QIList a  = QIList (Exp (QList a))

data QList :: * -> * where
    Return :: a -> QList a
    Bind   :: (Query a, Query b, Reify b, Reify a) => QIList a -> (a -> QList b) -> QList b

instance Monad QList where
    return :: a -> QList a
    return = Return
    
    (>>=) :: QList a -> (a -> QList b) -> QList b
    (Return a)  >>= k = k a
    (Bind vx h) >>= k = Bind vx (\x -> h x >>= k)

lowerQList :: (Reify a, Query a) => QList a -> QIList a
lowerQList (Return a)  = QIList (AppE Sng (unwrapQ a))
lowerQList (Bind (QIList vx) k) = QIList (AppE2 ConcatMap undefined vx) 
-- a -> QList b 
-- Exp a -> Exp (QList b)




instance (Reify (QList a), Reify a, Query a) => Query (QList a) where
    wrapQ :: Exp (QList a) -> QList a
    wrapQ e = Bind (QIList e) Return

    unwrapQ :: QList a -> Exp (QList a)
    unwrapQ = undefined

{-
data QList a where
    Prim   :: QIList a -> QList a
    Bind   :: QList a -> (a -> QList b) -> QList b
    Return :: a -> QList a
-}

class Reify a => Query a where
    wrapQ   :: Exp a -> a
    unwrapQ :: a -> Exp a

instance Query QInt where
    wrapQ e          = QInt e
    unwrapQ (QInt e) = e

instance Query QBool where
    wrapQ e = QBool e
    unwrapQ (QBool e) = e

{-
instance Query a => Query (QList a) where
    -- unwrapQ :: QList a -> Exp (QList a)
    unwrapQ (Bind as f)        = undefined ConcatMap (PairE undefined (unwrapQ as))
    unwrapQ (Return a)         = AppE Sng (unwrapQ a)
    unwrapQ (Prim (QIList as)) = as

    -- wrapQ :: Exp (QList a) -> QList a
    wrapQ = undefined  -- Either add a primitive combinator or use >>=
                       -- and return (right identity)

instance Functor QList where
    fmap = liftM

instance Applicative QList where
    pure  = return
    (<*>) = ap

instance Monad QList where
    (>>=)  = Bind
    return = Return
-}

{-
instance Reify a => Query (QList a) where
    wrapQ e = QList e
    unwrapQ (QList e) = e
-}

instance (Reify a, Reify b) => Query (QPair a b) where
    wrapQ e = QPair e
    unwrapQ (QPair e) = e

{-
and :: QList QBool -> QBool
and bs = wrapQ $ AppE And (unwrapQ bs)

append :: Query a => QList a -> QList a -> QList a
append as bs = wrapQ $ AppE Append (PairE (unwrapQ as) (unwrapQ bs))

toLam :: (Query a, Query b) => (a -> b) -> Exp a -> Exp b
toLam f = unwrapQ . f . wrapQ

concatMapQ :: (Query a, Query b) => (a -> QList b) -> QList a -> QList b
concatMapQ f as = wrapQ $ AppE ConcatMap (PairE (LamE $ toLam f) (unwrapQ as))

mapQ :: (Query a, Query b) => (a -> b) -> QList a -> QList b
mapQ = undefined

sng :: Query a => a -> QList a
sng x = wrapQ $ AppE Sng (unwrapQ x)
-}

{-
instance Monad QList where
    return = sng
    (>>=)  = concatMapQ
-}
