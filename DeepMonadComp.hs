{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE TypeFamilies        #-}

-- | An attempt to use monad comprehensions in a deep embedding of
-- NRC-like collection queries.
module DeepMonadComp where

import           Prelude

import           Data.List
import           Control.Applicative
import           Control.Monad                   hiding (guard)
import           Control.Monad.ConstrainedNormal
import           Control.Monad.Trans.State       hiding (guard)

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
    Expected type: QBool -> NMP QA QList ()
      Actual type: Bool -> NMP QA QList ()
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
    GtE         :: Exp a -> Exp a -> Exp QBool
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

class QA a where
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

instance QA QUnit where
    type Rep QUnit = QUnit
    wrap = QUnit
    unwrap (QUnit e) = e

instance (QA a, QA b) => QA (QTup a b) where
    type Rep (QTup a b) = QTup (Rep a) (Rep b)
    wrap = QTup
    unwrap (QTup e) = e

instance QA QInt where
    type Rep QInt = QInt

    wrap = QInt
    unwrap (QInt e) = e

instance QA QBool where
    type Rep QBool = QBool

    wrap = QBool
    unwrap (QBool e) = e

instance QA a => QA (QList a) where
    type Rep (QList a) = QList (Rep a)
    wrap = QList
    unwrap (QList e)   = e

instance (QA a, QA (Rep a)) => QA (NMP QA QList a) where
    type (Rep (NMP QA QList a)) = QList (Rep a)
    wrap   = liftList . wrap
    unwrap = unwrap . lowerList

--------------------------------------------------------------------------------
-- Convert between actual list ASTs and the deep embedding of monadic
-- list computations

liftList :: QA a => QList a -> NMP QA QList a
liftList = liftNMP

lowerList :: (QA a, QA (Rep a)) => NMP QA QList a -> QList a
lowerList = lowerNMP emptyRep appendRep sngRep bindRep

--------------------------------------------------------------------------------
-- List combinators on actual list ASTs

concatMapRep :: (QA a, QA b) => (a -> QList b) -> QList a -> QList b
concatMapRep f as = wrap $ ConcatMapE (LamE $ toLam f) (unwrap as)

bindRep :: (QA a, QA b) => QList a -> (a -> QList b) -> QList b
bindRep = flip concatMapRep

sngRep :: (QA a, QA (Rep a)) => a -> QList a
sngRep x = wrap $ SngE (unwrap x)

andRep :: QList QBool -> QBool
andRep bs = wrap $ AndE (unwrap bs)

appendRep :: QA a => QList a -> QList a -> QList a
appendRep as bs = wrap $ AppendE (unwrap as) (unwrap bs)

toLam :: (QA a, QA b) => (a -> b) -> Exp (Rep a) -> Exp (Rep b)
toLam f = unwrap . f . wrap

emptyRep :: QA a => QList a
emptyRep = wrap $ ListE []

guardRep :: QBool -> QList QUnit
guardRep b = wrap $ GuardE $ unwrap b

--------------------------------------------------------------------------------
-- User-facing list combinators on monadic lists

type QListM a = NMP QA QList a

(>.) :: QA a => a -> a -> QBool
(>.) a b = wrap $ GtE (unwrap a) (unwrap b)

fst_ :: (QA a, QA b) => QTup a b -> a
fst_ t = wrap $ FstE $ unwrap t

snd_ :: (QA a, QA b) => QTup a b -> b
snd_ t = wrap $ SndE $ unwrap t

sng_ :: (QA a, QA (Rep a)) => a -> QListM a
sng_ = liftList . sngRep

empty_ :: (QA a, QA (Rep a)) => QListM a
empty_ = liftList emptyRep

and_ :: QListM QBool -> QBool
and_ = andRep . lowerList

append_ :: (QA a, QA (Rep a)) => QListM a -> QListM a -> QListM a
append_ as1 as2 = liftList $ appendRep (lowerList as1) (lowerList as2)

concatMap_ :: (QA a, QA (Rep a), QA b, QA (Rep b))
           => (a -> QListM b) -> QListM a -> QListM b
concatMap_ f as = liftList $ concatMapRep f' (lowerList as)
  where
    f' a = lowerList $ f a

map_ :: (QA a, QA (Rep a), QA b, QA (Rep b)) => (a -> b) -> QListM a -> QListM b
map_ f = concatMap_ (sng_ . f)

guard :: QBool -> QListM QUnit
guard = liftList . guardRep

table_ :: (QA a, QA b, QA (Rep a), QA (Rep b)) => String -> QListM (QTup a b)
table_ tabName = wrap $ TableE tabName

true_ :: QBool
true_ = wrap $ BoolE True



--------------------------------------------------------------------------------
-- Literal values in queries

{-

Problem: Types like 'QListM QInt' look a bit awful. What we really
want is the original 'Q [Int]' instead. Additionally, we need a way to
use literal Haskell values in queries.

=> need a type function mapping between regular haskell types and
values and Q types

[a]  --> QListM a
Int  --> QInt
Bool --> QBool

=> Type class

class Query a where
    type Q a
    litQ :: a -> Q a
    fromQ :: Q a -> Maybe a

instance Query Bool where
    type Q Bool = QBool
    litQ b = wrap $ BoolE b
    fromQ (QBool (BoolE b)) = Just b
    fromQ _                 = Nothing

-}

--------------------------------------------------------------------------------
-- A simple pretty printer

type Doc = String

class Pretty a where
    pretty :: a -> Doc

(<+>) :: Doc -> Doc -> Doc
d1 <+> d2 = d1 ++ " " ++ d2

text :: String -> Doc
text = id

integer :: (Show a, Integral a) => a -> String
integer = show

parens :: Doc -> Doc
parens d = "(" ++ d ++ ")"

brackets :: Doc -> Doc
brackets d = "[" ++ d ++ "]"

bool :: Bool -> Doc
bool = show

list :: [Doc] -> Doc
list ds = brackets $ intercalate "," ds

tupled :: [Doc] -> Doc
tupled ds = parens $ intercalate "," ds

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

ppInfix :: String -> Exp a -> Exp b -> State Integer Doc
ppInfix n e1 e2 = do
    pe1 <- pp e1
    pe2 <- pp e2
    return $ parens pe1 <+> text n <+> parens pe2

pp :: Exp a -> State Integer Doc
pp (GtE a b ) = ppInfix ">" a b
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

instance (QA a, QA (Rep a)) => Pretty (QListM a) where
    pretty l = pretty $ lowerList l

--------------------------------------------------------------------------------
-- Comprehension examples

as :: QListM (QTup QInt QBool)
as = table_ "a"

bs :: QListM (QTup QInt QInt)
bs = table_ "b"

comp :: QListM QInt
comp = [ fst_ a | a <- as, b <- as ]

guardComp :: QListM QInt
guardComp = [ fst_ a | a <- as, true_ ]

guardComp2 :: QListM QInt
guardComp2 = [ fst_ a | a <- as, b <- bs, fst_ a >. snd_ b ]
