{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE RebindableSyntax  #-}
{-# LANGUAGE TypeFamilies      #-}

-- | An attempt to use monad comprehensions in a deep embedding of
-- NRC-like collection queries.
module DeepMonadComp where

import           Prelude

import           Control.Applicative
import           Control.Monad                   hiding (guard)
import           Control.Monad.ConstrainedNormal
import           Control.Monad.State             hiding (guard)

import           Text.PrettyPrint.ANSI.Leijen    hiding ((<$>))
import           Text.Printf

{-

Without RebindableSyntax, using comprehension guards will fail. GHC
apparently uses Control.Monad.guard to typecheck the
comprehension. However, the type of guard
'MonadPlus m => Bool -> m ()' is too restrictive as it demands a
proper Bool. As we create a deep embedding, we can't provide that.

λ> :set -XMonadComprehensions
λ> pretty [ fst_ a | a <- as ]
append (concatMap (\v0 -> append (sng (fst (v0))) ([])) (table(a))) ([])
λ> :t true_
true_ :: QBool
λ> pretty [ fst_ a | a <- as, true_ ]
<interactive>:12:28:
    Couldn't match type ‘Bool’ with ‘QBool’
    Expected type: QBool -> NMP Q QList ()
      Actual type: Bool -> NMP Q QList ()
    In a stmt of a monad comprehension: true_
    In the first argument of ‘pretty’, namely
      ‘[fst_ a | a <- as, true_]’
    In the expression: pretty [fst_ a | a <- as, true_]

What we can do instead is to provide our own 'guard' combinator and
use it with RebindableSyntax. Of course, that's rather unsatisfying as
RebindableSyntax is exactly the thing we wanted to avoid. At least,
comprehension desugaring uses proper (>>=), return, mzero and mplus
from Monad and MonadPlus.

-}

--------------------------------------------------------------------------------
-- Typed query AST

data Exp :: * -> * where
    BoolE       :: Bool    -> Exp QBool
    IntegerE    :: Integer -> Exp QInt
    ListE       :: [Exp a] -> Exp (QList a)
    TupE        :: Exp a -> Exp b -> Exp (QTup a b)

    AndE        :: Exp (QList QBool) -> Exp QBool
    SngE        :: Exp a -> Exp (QList a)
    AppendE     :: Exp (QList a) -> Exp (QList a) -> Exp (QList a)
    ConcatMapE  :: Exp (a -> QList b) -> Exp (QList a) -> Exp (QList b)
    LamE        :: (Exp a -> Exp b) -> Exp (a -> b)
    VarE        :: Integer -> Exp a
    FstE        :: Exp (QTup a b) -> Exp a
    SndE        :: Exp (QTup a b) -> Exp b
    TableE      :: String -> Exp (QList (QTup a b))

    GuardE      :: Exp QBool -> Exp (QList QUnit)

data Type :: * -> * where
    BoolT     :: Type QBool
    IntegerT  :: Type QInt
    ListT     :: Type a -> Type (QList a)
    TupT      :: Type a -> Type b -> Type (QTup a b)
    ArrowT    :: Type a -> Type b -> Type (a -> b)

--------------------------------------------------------------------------------
-- Classes

class Q a where
    type Rep a :: *
    wrap   :: Exp (Rep a) -> a
    unwrap :: a -> Exp (Rep a)

--------------------------------------------------------------------------------
-- Type-specific AST wrappers

newtype QUnit     = QUnit (Exp (Rep QUnit))
newtype QInt      = QInt (Exp (Rep QInt))
newtype QBool     = QBool (Exp (Rep QBool))
newtype QList a   = QList (Exp (Rep (QList a)))
newtype QTup a b  = QTup (Exp (Rep (QTup a b)))

instance Q QUnit where
    type Rep QUnit = QUnit
    wrap = QUnit
    unwrap (QUnit e) = e

instance (Q a, Q b) => Q (QTup a b) where
    type Rep (QTup a b) = QTup (Rep a) (Rep b)
    wrap = QTup
    unwrap (QTup e) = e

instance Q QInt where
    type Rep QInt = QInt

    wrap = QInt
    unwrap (QInt e) = e

instance Q QBool where
    type Rep QBool = QBool

    wrap = QBool
    unwrap (QBool e) = e

instance Q a => Q (QList a) where
    type Rep (QList a) = QList (Rep a)
    wrap = QList
    unwrap (QList e)   = e

instance (Q a, Q (Rep a)) => Q (NMP Q QList a) where
    type (Rep (NMP Q QList a)) = QList (Rep a)
    wrap   = liftList . wrap
    unwrap = unwrap . lowerList

--------------------------------------------------------------------------------
-- Convert between actual list ASTs and the deep embedding of monadic
-- list computations

liftList :: Q a => QList a -> NMP Q QList a
liftList = liftNMP

lowerList :: (Q a, Q (Rep a)) => NMP Q QList a -> QList a
lowerList = lowerNMP emptyRep appendRep sngRep bindRep

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

emptyRep :: Q a => QList a
emptyRep = wrap $ ListE []

guardRep :: QBool -> QList QUnit
guardRep b = wrap $ GuardE $ unwrap b

--------------------------------------------------------------------------------
-- User-facing list combinators on monadic lists

type QListM a = NMP Q QList a

fst_ :: (Q a, Q b) => QTup a b -> a
fst_ t = wrap $ FstE $ unwrap t

snd_ :: (Q a, Q b) => QTup a b -> b
snd_ t = wrap $ SndE $ unwrap t

sng_ :: (Q a, Q (Rep a)) => a -> QListM a
sng_ = liftList . sngRep

empty_ :: (Q a, Q (Rep a)) => QListM a
empty_ = liftList emptyRep

and_ :: QListM QBool -> QBool
and_ = andRep . lowerList

append_ :: (Q a, Q (Rep a)) => QListM a -> QListM a -> QListM a
append_ as1 as2 = liftList $ appendRep (lowerList as1) (lowerList as2)

concatMap_ :: (Q a, Q (Rep a), Q b, Q (Rep b))
           => (a -> QListM b) -> QListM a -> QListM b
concatMap_ f as = liftList $ concatMapRep f' (lowerList as)
  where
    f' a = lowerList $ f a

map_ :: (Q a, Q (Rep a), Q b, Q (Rep b)) => (a -> b) -> QListM a -> QListM b
map_ f = concatMap_ (sng_ . f)

guard :: QBool -> QListM QUnit
guard = liftList . guardRep

table_ :: (Q a, Q b, Q (Rep a), Q (Rep b)) => String -> QListM (QTup a b)
table_ tabName = wrap $ TableE tabName

true_ :: QBool
true_ = wrap $ BoolE True



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

--------------------------------------------------------------------------------
-- Pretty-printing of frontend ASTs

instance Pretty (Type a) where
    pretty BoolT          = text "Bool"
    pretty IntegerT       = text "Integer"
    pretty (ListT t)      = brackets $ pretty t
    pretty (ArrowT t1 t2) = parens $ pretty t1 <+> text "->" <+> pretty t2

ppApp1 :: String -> Exp a -> State Integer Doc
ppApp1 n e = (<+>) (text n) <$> (parens <$> pp e)

ppApp2 :: String -> Exp a -> Exp b -> State Integer Doc
ppApp2 n e1 e2 = do
    pe1 <- pp e1
    pe2 <- pp e2
    return $ text n <+> parens pe1 <+> parens pe2

pp :: Exp a -> State Integer Doc
pp (BoolE b) = return $ bool b
pp (IntegerE i) = return $ integer i
pp (ListE l) = list <$> mapM pp l
pp (TupE a b) = tupled <$> (pp a >>= \pa -> pp b >>= \pb -> return [pa, pb])
pp (AndE bs) = ppApp1 "and" bs
pp (FstE bs) = ppApp1 "fst" bs
pp (SndE bs) = ppApp1 "snd" bs
pp (SngE a) = ppApp1 "sng" a
pp (GuardE b) = ppApp1 "guard" b
pp (AppendE as1 as2) = ppApp2 "append" as1 as2
pp (ConcatMapE f as) = ppApp2 "concatMap" f as
pp (VarE i) = return $ text $ "v" ++ show i
pp (LamE f) = do
    i <- get
    put $ i + 1
    let v = "v" ++ show i
    pf <- pp (f (VarE i))
    return $ text (printf "\\%s ->" v) <+> pf
pp (TableE n) = return $ text $ printf "table(%s)" n

instance Pretty QInt where
    pretty (QInt e) = evalState (pp e) 0

instance Pretty QBool where
    pretty (QBool e) = evalState (pp e) 0

instance Pretty (QTup a b) where
    pretty (QTup e) = evalState (pp e) 0

instance Pretty (QList a) where
    pretty (QList e) = evalState (pp e) 0

instance (Q a, Q (Rep a)) => Pretty (QListM a) where
    pretty l = pretty $ lowerList l

--------------------------------------------------------------------------------
-- Comprehension examples

as :: QListM (QTup QInt QBool)
as = table_ "a"

comp :: QListM QInt
comp = [ fst_ a | a <- as, b <- as ] 

guardComp :: QListM QInt
guardComp = [ fst_ a | a <- as, true_ ]
