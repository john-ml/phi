module Phi where

import Prelude hiding ((!!))

import Debug.Trace
import Data.Set (Set); import qualified Data.Set as S
import Data.Map.Strict (Map); import qualified Data.Map.Strict as M

import qualified Data.List as L
import Data.Semigroup
import qualified Data.Foldable as F
import Data.Bifunctor
import Data.Functor
import Data.Maybe
import Data.String (IsString (..))
import Control.Monad
import Control.Monad.Except
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Writer.Strict
import Control.Applicative

import Data.Char
import Data.Void
import Text.Megaparsec (ParsecT, MonadParsec)
import qualified Text.Megaparsec as P
import Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer as L

import qualified Data.Graph as G

import Util

import Data.Data
import Data.Data.Lens
import Control.Lens

#define THEUSUAL Eq, Ord, Show, Data
#define THEUSUALA Eq, Ord, Show, Functor, Foldable, Traversable, Data

-- -------------------- Object language --------------------

data Bop = Add | Sub | Mul | Div deriving (THEUSUAL)

data IDir
  = Ieq | Ine
  | Islt | Isgt | Isle | Isge
  | Iult | Iugt | Iule | Iuge
  deriving (THEUSUAL)

data FDir
  = Foeq | Fogt | Foge | Folt | Fole | Fone | Ford
  | Fueq | Fugt | Fuge | Fult | Fule | Fune | Funo
  deriving (THEUSUAL)

-- Primitives
data Prim
  = BinArith Bop 
  | ICmp IDir
  | FCmp FDir
  | ShuffleVector
  deriving (THEUSUAL)

-- Primitive types
data PTy
  = I Word
  | Half | Float | Double | FP128
  | Ptr Ty
  deriving (THEUSUAL)
instance Plated PTy

-- Types
data Ty
  = Void
  | PTy PTy
  | Arr Word Ty
  | Tup [Ty]
  | TStruct String
  | Vec Word PTy
  | FPtr [Ty] Ty
  deriving (THEUSUAL)
instance Plated Ty

-- LLVM has 3 ways of reading substructures:
-- - extractvalue: works on structs or arrays with constant offset
-- - extractelement: works on vectors with variable offset
-- - gep: works on ptrs with arbitrary paths (struct offsets must be i32)
-- LLVM's version of C's a[i] is gep + load.

-- Access paths
newtype Path a = Path [Step a] deriving (THEUSUALA)
data Step a
  = Proj a Word -- extractvalue struct: e.n, n const
  | Elem (Exp a) -- extractelement: e<e>
  | IndexA a Word -- extractvalue array: e[n], n const
  | Index (Exp a) -- array offset: e[e] (e non-const)
  deriving (THEUSUALA)

type Var = Word
type Width = Word

-- Local function definition
data Func a = Func a Var [(a, Var, Ty)] Ty (Exp a) deriving (THEUSUALA)
instance Data a => Plated (Func a)

-- Case arms
data Arm a = Maybe Integer :=> Exp a deriving (THEUSUALA)
instance Data a => Plated (Arm a)

-- Expressions
data Exp a
  -- Primitives
  = Var a Var
  | Undef a
  | Null a
  | ExtVar a String
  | Alloca a (Exp a)
  | Int a Integer Width
  | Ann a (Exp a) Ty
  | Prim a Prim [Exp a]
  | Cast a (Exp a) Ty
  | Let a Var Ty (Exp a) (Exp a)
  -- Control flow / name binding
  | Call a (Exp a) [Exp a]
  | Case a (Exp a) [Arm a]
  | Rec a [Func a] (Exp a) -- Function bundle
  -- Aggregates
  | Array a [Exp a]
  | Tuple a [Exp a]
  | Struct a String [Exp a]
  | Vector a [Exp a]
  | Gep a (Exp a) (Path a) -- &e path (GEP)
  | Load a (Exp a) (Path a) -- e path (GEP+load, extractvalue, extractelement)
  | Store a (Exp a) (Path a) (Exp a) (Exp a) -- e path <- e; e (GEP+store)
  | Update a (Exp a) (Path a) (Exp a) -- e with path = e (insertvalue, insertelement)
  deriving (THEUSUALA)
instance Data a => Plated (Exp a)

-- For ANF
data Atom a
  = AVar a Var
  | AUndef a
  | ANull a
  | AExtVar a String
  | AInt a Integer Width
  | AArr a [Atom a]
  | ATup a [Atom a]
  | AStruct a String [Atom a]
  | AVec a [Atom a]
  deriving (THEUSUALA)
instance Data a => Plated (Atom a)

-- Since this is LLVM and not λ-calculus, every function must satisfy some conditions
-- so that they can be implemented as basic blocks using φ-nodes instead of closures.
-- - All functions f where some variables are live upon entry to f (i.e., f itself
--   closes over those variables or calls functions which do) must become basic blocks.
-- - Specifically, x is live at f if, assuming UB,
--     (1) x ∈ FV(body of f) OR
--     (2) f calls g, x is live at g, and x ∉ BV(body of f).
-- - All calls to SSA-block functions must be in tail position.
-- - These tail calls will become `br` instructions and the corresponding functions
--   will become basic blocks with φ-nodes.
-- If a function has no live variables upon entry, it can become a global function.
-- However, it may be beneficial to make some of these functions be basic blocks, because
-- `br` instructions + φ-nodes don't have to adhere to calling conventions (e.g. if
-- LLVM has to spill some of the arguments to tail call, it can't be a simple jump anymore.)
-- To do this, there's an invariant would be useful to preserve: every connected component
-- of basic blocks must have exactly one "entry point" which is a global function. That is,
-- if a function f calls a basic block g then for all functions f' and basic blocks h
-- reachable from g by `br` instructions only, f' calls g ==> f' = f.
-- - This invariant holds for the BB assignment yielded by liveness analysis: for all
--   functions f and BBs g where f calls g, f must have killed all variables live at g.
--   It's impossible for two distinct functions f and f' to call a BB g because both would
--   have to have killed the same set of variables (violating UB).

-- -------------------- Structure of the compiler --------------------

data Anno = Anno
  { -- Parsing ==> ASTs are labelled with source locations
    _loc :: P.SourcePos
  , -- After parsing, make bindings unique
    -- After UB, type check and annotate nodes with their types
    _typ :: Ty
  , -- After TC, convert to ANF and rewrite tail calls into Tail AST nodes.
    -- After ANF, label nodes with FV and BV sets...
    _fvSet :: Set Var
  , _bvSet :: Set Var
  } deriving (THEUSUAL)
makeLenses ''Anno

-- ...compute the call graph...
data FnCall a = FnCall
  { isTail :: Bool
  , callerOf :: Maybe Var -- Nothing ==> main
  , actualsOf :: [Atom a]
  , locOf :: P.SourcePos
  } deriving (THEUSUALA)
type CallGraph a = Map Var (Set (FnCall a))

-- ...and determine whether each function should be an SSA block or a CFG.
type BBs = Set Var

-- -------------------- Some boilerplate to work with annotations --------------------

emptyAnno :: Anno
emptyAnno = Anno
  { _loc = undefined
  , _typ = undefined
  , _fvSet = undefined
  , _bvSet = undefined
  }

-- Every expression node has an annotation
anno :: Exp a -> a
anno = \case
  Var a _ -> a
  Undef a -> a
  Null a -> a
  ExtVar a _ -> a
  Alloca a _ -> a
  Int a _ _ -> a
  Ann a _ _ -> a
  Prim a _ _ -> a
  Cast a _ _ -> a
  Let a _ _ _ _ -> a
  Call a _ _ -> a
  Case a _ _ -> a
  Rec a _ _ -> a
  Array a _ -> a
  Tuple a _ -> a
  Struct a _ _ -> a
  Vector a _ -> a
  Gep a _ _ -> a
  Load a _ _ -> a
  Store a _ _ _ _ -> a
  Update a _ _ _ -> a

raise a e = throwError (a ^. loc, e)

-- -------------------- Variables --------------------

-- Useful for generating fresh variable
gen :: MonadState Var m => m Var
gen = modify' succ *> get

-- Generic fold over variables
foldVars :: Monoid m => (Var -> m) -> Exp a -> m
foldVars f = \case
  Var _ x -> f x
  Undef _ -> mempty
  Null _ -> mempty
  ExtVar _ _ -> mempty
  Alloca _ e -> go e
  Int{} -> mempty
  Ann _ e _ -> go e
  Prim _ _ es -> foldMap go es
  Cast _ e _ -> go e
  Let _ x _ e1 e -> f x <> go e1 <> go e
  Call _ e es -> go e <> foldMap go es
  Case _ e pes ->
    go e <> foldMap (\ (_ :=> e) -> go e) pes
  Rec _ fs e -> foldMap goFunc fs <> go e where
    goFunc (Func _ f' axts _ e) =
      f f' <> foldMap (\ (_, x, _) -> f x) axts <> go e
  Array _ es -> foldMap go es
  Tuple _ es -> foldMap go es
  Struct _ _ es -> foldMap go es
  Vector _ es -> foldMap go es
  Gep _ e (Path ss) -> go e <> foldMap goStep ss
  Load _ e (Path ss) -> go e <> foldMap goStep ss
  Store _ dst (Path ss) src e -> go dst <> go src <> foldMap goStep ss <> go e
  Update _ e (Path ss) e1 -> go e <> foldMap goStep ss <> go e1
  where
    go = foldVars f
    goStep = \case
      Proj _ _ -> mempty
      Elem e -> go e
      IndexA _ _ -> mempty
      Index e -> go e

-- Smallest variable v such that {v + 1, v + 2, ..} are all unused
maxUsed :: Exp a -> Var
maxUsed = getMax . foldVars Max

-- Used variables
uv :: Exp a -> Set Var
uv = foldVars S.singleton

-- Rename bound variables for unique bindings
ub :: Exp Anno -> Exp Anno
ub e = go M.empty e `evalState` maxUsed e where
  go σ = \case
    Var a x -> return $ Var a (σ ! x)
    Undef a -> return $ Undef a
    Null a -> return $ Null a
    ExtVar a s -> return $ ExtVar a s
    Alloca a e -> Alloca a <$> go σ e
    Int a i w -> return $ Int a i w
    Ann a e ty -> Ann a <$> go σ e <*> pure ty
    Prim a p es -> Prim a p <$> mapM (go σ) es
    Cast a e t -> Cast a <$> go σ e <*> pure t
    Let a x t e1 e -> do
      x' <- gen
      Let a x' t <$> go σ e1 <*> go (M.insert x x' σ) e
    Call a e es -> Call a <$> go σ e <*> mapM (go σ) es
    Case a e pes ->
      Case a
        <$> go σ e
        <*> mapM (\ (p :=> e) -> (p :=>) <$> go σ e) pes
    Rec a helpers e -> do
      let fs = map (\ (Func _ f _ _ _) -> f) helpers
      fs' <- replicateM (length fs) gen
      let σ' = M.fromList (zip fs fs') `M.union` σ
      helpers' <- forM helpers $ \ (Func a f axts t e) -> do
        let xs = map (\ (_, x, _) -> x) axts
        xs' <- replicateM (length axts) gen
        let axts' = zipWith (\ x' (a, _, t) -> (a, x', t)) xs' axts
        let σ'' = M.fromList (zip xs xs') `M.union` σ'
        Func a (σ' ! f) axts' t <$> go σ'' e
      Rec a helpers' <$> go σ' e
    Array a es -> Array a <$> mapM (go σ) es
    Tuple a es -> Tuple a <$> mapM (go σ) es
    Struct a s es -> Struct a s <$> mapM (go σ) es
    Vector a es -> Vector a <$> mapM (go σ) es
    Gep a e (Path ss) -> Gep a <$> go σ e <*> (Path <$> mapM goStep ss)
    Load a e (Path ss) -> Load a <$> go σ e <*> (Path <$> mapM goStep ss)
    Store a dst (Path ss) src e ->
      Store a <$> go σ dst <*> (Path <$> mapM goStep ss) <*> go σ src <*> go σ e
    Update a e (Path ss) e1 -> Update a <$> go σ e <*> (Path <$> mapM goStep ss) <*> go σ e1
    where
      goStep = \case
        s@(Proj _ _) -> return s
        s@(IndexA _ _) -> return s
        Elem e -> Elem <$> go σ e
        Index e -> Index <$> go σ e
  σ ! x = M.findWithDefault x x σ

-- -------------------- Type checking --------------------

data TCErr
  = NotInScope Var
  | ExtNotInScope String
  | StructNotInScope String
  | ExGotShape String Ty
  | ExGot Ty Ty
  | CantCast Ty Ty
  | OutOfBounds Word Ty
  | Custom String

instance PP TCErr where
  pp = \case
    NotInScope x -> line $ "Variable not in scope: " <> show' x
    ExtNotInScope s -> line $ "Extern variable not in scope: " <> fromString s
    StructNotInScope s -> line $ "Unknown struct name: " <> fromString s
    ExGotShape shape ty ->
      line' $ "Expected " <> fromString shape <> " but got " <> pp ty
    ExGot ex got -> line' $ "Expected " <> pp ex <> " but got " <> pp got
    CantCast old new -> line' $ "Can't cast " <> pp old <> " to " <> pp new
    OutOfBounds n ty -> line' $ "Index " <> show'' n <> " is out of bounds for type " <> pp ty
    Custom s -> line' $ fromString s

data TCState = TCState
  { _tcLocals :: Map Var Ty
  , _tcExterns :: Map String Ty
  , _tcStructs :: Map String [Ty]
  }
makeLenses ''TCState

type TC = ExceptT (P.SourcePos, TCErr) (Reader TCState)

runTC' ::
  TC a -> Map Var Ty -> Map String Ty -> Map String [Ty] ->
  Either (P.SourcePos, TCErr) a
runTC' m env extEnv structEnv =
  runExceptT m `runReader` TCState
    { _tcLocals = M.empty
    , _tcExterns = extEnv
    , _tcStructs = structEnv
    }

runTC :: TC a -> Map String Ty -> Map String [Ty] -> Either String a
runTC m extEnv structEnv = first pretty $ runTC' m M.empty extEnv structEnv where
  pretty (pos, err) = P.sourcePosPretty pos ++ ": " ++ runDoc (pp err)

withBindings :: [Var] -> [Ty] -> TC a -> TC a
withBindings xs ts = local $ tcLocals %~ M.union (M.fromList $ zip xs ts)

withBinding :: Var -> Ty -> TC a -> TC a
withBinding x t = local $ tcLocals %~ M.insert x t

tcLookup :: Anno -> Var -> TC Ty
tcLookup a x = (M.!? x) . _tcLocals <$> ask >>= \case
  Just r -> return r
  Nothing -> raise a $ NotInScope x

extLookup :: Anno -> String -> TC Ty
extLookup a s = (M.!? s) . _tcExterns <$> ask >>= \case
  Just r -> return r
  Nothing -> raise a $ ExtNotInScope s

structLookup :: Anno -> String -> TC [Ty]
structLookup a s = (M.!? s) . _tcStructs <$> ask >>= \case
  Just r -> return r
  Nothing -> raise a $ StructNotInScope s

check :: Exp Anno -> Ty -> TC (Exp Anno)
check exp ty = case exp of
  Undef a -> return $ Undef (typ .~ ty $ a)
  Null a -> case ty of
    PTy (Ptr ty') -> return $ Null (typ .~ ty $ a)
    ty -> raise a $ ExGotShape "pointer" ty
  Case a e pes -> infer e >>= \case
    (PTy (I _), e') -> do
      pes' <- mapM (\ (p :=> e) -> (p :=>) <$> check e ty) pes
      return $ Case (typ .~ ty $ a) e' pes'
    (ty, _) -> raise a $ ExGotShape "integer" ty
  exp@(anno -> a) -> infer exp >>= \case
    (ty', exp')
      | ty' == ty -> return exp'
      | otherwise -> raise a $ ExGot ty ty'

checkNumOp :: Anno -> [Exp Anno] -> TC (Ty, [Exp Anno])
checkNumOp a = \case
  [] -> raise a . Custom $ "Expected at least one argument"
  (e:es) -> do
    (t, e') <- infer e
    unless (ok t) . raise a $ ExGotShape "numeric type or <_ x numeric type>" t
    es' <- mapM (`check` t) es
    return (t, e':es')
  where
    ok t = numeric t || case t of Vec _ t' -> numeric (PTy t'); _ -> False
    numeric = \case
      PTy (I _) -> True
      PTy Half -> True
      PTy Float -> True
      PTy Double -> True
      PTy FP128 -> True
      _ -> False

checkCmp :: Anno -> [Exp Anno] -> (Ty -> Bool) -> TC (Ty, [Exp Anno])
checkCmp a es ok = case es of
  [e1, e2] -> do
    (t, e1') <- infer e1
    unless (ok t) . raise a $ ExGotShape "one of {numeric type, pointer, <_ x numeric type>}" t
    e2' <- check e2 t
    return (PTy (I 1), [e1', e2'])

checkPrim :: Anno -> [Exp Anno] -> Prim -> TC (Ty, [Exp Anno])
checkPrim a es = \case
  BinArith _ -> checkNumOp a es
  ICmp _ -> checkCmp a es . fix $ \ go -> \case
    PTy (I _) -> True
    PTy (Ptr _) -> True
    Vec _ t' -> go (PTy t')
    _ -> False
  FCmp _ -> checkCmp a es . fix $ \ go -> \case
    PTy Half -> True
    PTy Float -> True
    PTy Double -> True
    PTy FP128 -> True
    Vec _ t' -> go (PTy t')
    _ -> False
  ShuffleVector -> case es of
    [v1, v2, mask] -> case mask of
      Vector a es -> do
        es' <- forM es $ \case
          Int a i 32 -> do
            let ty = PTy (I 32)
            return $ Int (typ .~ ty $ a) i 32
          (anno -> a) -> raise a $ Custom "shuffle mask must contain i32 constants"
        infer v1 >>= \case
          (t@(Vec _ elt), v1') -> do
            v2' <- check v2 t
            let n = L.genericLength es
            return (Vec n elt, [v1', v2', Vector (typ .~ Vec n (I 32) $ a) es'])
          (t, _) -> raise (anno v1) $ ExGotShape "vector" t
      (anno -> a) -> raise a $ Custom "shuffle mask must be a vector constant"
    _ -> raise a $ Custom "shufflevector expects 3 arguments: v1, v2, and shuffle mask"

var :: Anno -> Var -> TC (Ty, Exp Anno)
var a x = do
  ty <- tcLookup a x
  return (ty, Var (typ .~ ty $ a) x)

extVar :: Anno -> String -> TC (Ty, Exp Anno)
extVar a s = do
  ty <- extLookup a s
  return (ty, ExtVar (typ .~ ty $ a) s)

coercible :: Anno -> Ty -> Ty -> TC ()
coercible a = curry $ \case
  (PTy (Ptr _), PTy (Ptr _)) -> return ()
  (old, new) -> raise a $ CantCast old new

infer :: Exp Anno -> TC (Ty, Exp Anno)
infer = \case
  Var a x -> var a x
  ExtVar a s -> extVar a s
  Alloca a e -> do
    (t, e') <- infer e
    let ty = PTy (Ptr t)
    return (ty, Alloca (typ .~ ty $ a) e')
  Int a i w -> let t = PTy (I w) in return (t, Int (typ .~ t $ a) i w)
  Ann _ e ty -> (ty, ) <$> check e ty
  Prim a p es -> do
    (t, es') <- checkPrim a es p
    return (t, Prim (typ .~ t $ a) p es')
  Cast a e ty -> do
    (old, e') <- infer e
    coercible a old ty
    return (ty, Cast (typ .~ ty $ a) e' ty)
  Let a x t e1 e -> do
    e1' <- check e1 t
    (ty, e') <- withBinding x t (infer e)
    return (ty, Let (typ .~ ty $ a) x t e1' e')
  Call a e es -> infer e >>= \case
    (FPtr ts t, e') | length ts == length es -> do
      es' <- zipWithM check es ts
      return (t, Call (typ .~ t $ a) e' es')
    (FPtr ts _, _) ->
      raise a . Custom $
        "Function expects " ++ show (length ts) ++
        " arguments but got " ++ show (length es)
    (ty, _) -> raise a $ ExGotShape "function" ty
  Rec a funcs e -> do
    let fs = map (\ (Func _ f _ _ _) -> f) funcs
    let ts = map (\ (Func _ _ axts t _) -> FPtr (map (\ (_, _, t) -> t) axts) t) funcs
    withBindings fs ts $ do
      funcs' <- forM funcs $ \ (Func a f axts t e) -> do
        let xs = map (\ (_, x, _) -> x) axts
        let ts = map (\ (_, _, t) -> t) axts
        let axts' = map (\ (a, x, t) -> (typ .~ Void $ a, x, t)) axts
        current <- ask
        e' <- withBindings xs ts (check e t)
        return $ Func (typ .~ Void $ a) f axts' t e'
      (ty, e') <- infer e
      return (ty, Rec (typ .~ ty $ a) funcs' e')
  -- TODO: empty array
  Array a ((e:es) :∧: (L.genericLength -> n)) -> do
    (t, e') <- infer e
    es' <- mapM (`check` t) es
    let ty = Arr n t
    return (ty, Array (typ .~ ty $ a) (e':es'))
  Tuple a es -> do
    (ts, es') <- unzip <$> mapM infer es
    let ty = Tup ts
    return (ty, Tuple (typ .~ ty $ a) es')
  Struct a s es -> do
    (ts, es') <- unzip <$> mapM infer es
    let ty = TStruct s
    return (ty, Struct (typ .~ ty $ a) s es')
  Vector a [] -> raise a $ Custom "Zero-element vectors aren't allowed"
  Vector a ((e:es) :∧: (L.genericLength -> n)) -> infer e >>= \case
    (t@(PTy t'), e') -> do
      es' <- mapM (`check` t) es
      let ty = Vec n t'
      return (ty, Vector (typ .~ ty $ a) (e':es'))
    (t, _) -> raise a $ ExGotShape "primitive type" t
  Gep a e (Path ss) -> do
    ss' <- okForGep a ss
    infer e >>= \case
      (t@(PTy (Ptr _)), e') -> do
        (t', ss'') <- goPath True t ss'
        let ty = PTy (Ptr t')
        return (ty, Gep (typ .~ ty $ a) e' (Path ss''))
      (t, anno -> a) -> raise a $ ExGotShape "pointer" t
  Load a e (Path ss) -> infer e >>= \case
    (t@(PTy (Ptr _)), e') -> do
      ss' <- okForGep a ss
      (ty, ss'') <- goPath True t ss'
      return (ty, Load (typ .~ ty $ a) e' (Path ss''))
    (t, e') | isAgg t -> do
      (ty, ss') <- goPath False t ss
      return (ty, Load (typ .~ ty $ a) e' (Path ss'))
    (t, anno -> a) -> raise a $ ExGotShape "one of {pointer, tuple, array, vector}" t
  Store a dst (Path ss) src e -> do
    ss' <- okForGep a ss
    infer dst >>= \case
      (t@(PTy (Ptr _)), dst') -> do
        (t', ss'') <- goPath True t ss'
        src' <- check src t'
        (ty, e') <- infer e
        return (ty, Store (typ .~ ty $ a) dst' (Path ss'') src' e')
      (t, anno -> a) -> raise a $ ExGotShape "pointer" t
  Update a e (Path ss) e1 -> infer e >>= \case
    (ty, e') | isAgg ty -> do
      (t, ss') <- goPath False ty ss
      e1' <- check e1 t
      return (ty, Update (typ .~ ty $ a) e' (Path ss') e1')
    (t, anno -> a) -> raise a $ ExGotShape "one of {tuple, array, vector}" t
  e -> raise (anno e) $ Custom "Can't infer the type of this expression"
  where
    isAgg = \case
      Tup _ -> True
      TStruct _ -> True
      Arr _ _ -> True
      Vec _ _ -> True
      _ -> False
    okForGep a = \case
      ss@(Index _ : _) -> return ss
      IndexA a n : ss' -> return (Index (Int a (fromIntegral n) 32) : ss')
      _ -> raise a $ Custom "GEP must start with array index"
    goPath' = goPath False
    goPath lax t = \case
      [] -> return (t, [])
      path@(Proj a n : ss) -> case t of
        Tup ts
          | n < L.genericLength ts -> do
              (t', ss') <- goPath' (ts `L.genericIndex` n) ss
              return (t', Proj (typ .~ Void $ a) n : ss')
          | otherwise -> raise a $ OutOfBounds n t
        TStruct s -> do
          ts <- structLookup a s
          goPath lax (Tup ts) path
        t -> raise a $ ExGotShape "tuple or struct" t
      Elem e : ss -> case t of
        Vec _ pt -> infer e >>= \case
          (PTy (I _), e') -> do
            (t', ss') <- goPath' (PTy pt) ss
            return (t', Elem e' : ss')
          (te, anno -> a) -> raise a $ ExGotShape "integer" te
        t -> raise (anno e) $ ExGotShape "vector" t
      IndexA a n : ss -> case t of
        Arr m t'
          | n < m -> do
              (t'', ss') <- goPath' t' ss
              return (t'', IndexA (typ .~ Void $ a) n : ss')
          | otherwise -> raise a $ OutOfBounds n t
        t -> raise a $ ExGotShape "array" t
      Index e : ss -> case t of
        PTy (Ptr t) | lax -> go t
        Arr _ t -> go t
        t -> raise (anno e) $ ExGotShape ((if lax then "pointer or" else "") <> "array") t
        where
          go t = infer e >>= \case
            (PTy (I _), e') -> do
              (t', ss') <- goPath' t ss
              return (t', Index e' : ss')
            (te, anno -> a) -> raise a $ ExGotShape "integer" te

-- -------------------- Aggregate unfolding --------------------
-- LLVM has some unfortunate restrictions on aggregates that make it hard to
-- use as an expression language:
-- 1. Naively translating stores
--      .. <- e; ..
--    into `store` instructions won't work because `store` requires that `e` be
--    either a variable or a aggregate constant. For example,
--      .. <- {1, x}; ..
--    isn't allowed.
-- 2. A similar restrictions exists for return values:
--      rec f(x: i32): {i32, i32} = {1, x} in ...
--    can't be translated into a function ending in
--      ret {i32, i32} {i32 1, i32 %x}
--    because `ret`'s operand must be either a variable or an aggregate constant.
-- This pass gets around this issue as follows:
-- 1. Before conversion to ANF:
--    1a. Rewrite stores p <- e; .. ~~> p <- e' with {..}; ..
--    1b. Rewrite structure returns e ~~> e' with {..}
--    where:
--    - The `with` clause contains a path + expression for every non-constant hole
--    - e' is e with all non-constant holes replaced by `undef`
-- 2. Conversion to ANF will automatically generate intermediate instructions to fill out
--    holes etc. and ensure that `store`s and `ret`s only receive variables or aggregate
--    constants.

unfoldAggs :: Exp Anno -> Exp Anno
unfoldAggs = go where
  go = transform $ \ exp -> case exp of
    Array{} -> goAgg exp
    Tuple{} -> goAgg exp
    Struct{} -> goAgg exp
    Vector{} -> goAgg exp
    _ -> exp
  goAgg e = 
    let (e', pes) = goAgg' [] e `runState` [] in
    L.foldl' (\ e (ss, e') -> Update (anno e) e (Path (reverse ss)) (go e')) e' pes
  goAgg' ss = \case
    Array a es -> Array a <$> goChildren IndexA es
    Tuple a es -> Tuple a <$> goChildren Proj es
    Struct a s es -> Struct a s <$> goChildren Proj es
    Vector a es -> do
      es' <- foriM es $ \ i e -> case e of
        Int{} -> return $ go e
        ExtVar{} -> return $ go e
        Undef{} -> return $ go e
        Null{} -> return $ go e
        (anno -> a) -> add (Elem (Int a (fromIntegral i) 32) : ss) e $> Undef a
      return $ Vector a es'
    where
      add ss e = modify' ((ss, e) :)
      goChildren f es =
        foriM es $ \ i e -> let s = f (anno e) (fromIntegral i) in case e of
          Array{} -> goAgg' (s:ss) e
          Tuple{} -> goAgg' (s:ss) e
          Struct{} -> goAgg' (s:ss) e
          Int{} -> return $ go e
          ExtVar{} -> return $ go e
          Undef{} -> return $ go e
          Null{} -> return $ go e
          e -> add (s:ss) e $> Undef (anno e)

-- -------------------- Conversion to ANF --------------------

newtype APath a = APath [AStep a] deriving (THEUSUALA)
instance Data a => Plated (APath a)

data AStep a
  = AProj a Word -- extractvalue struct: e.n, n const
  | AElem (Atom a) -- extractelement: e<e>
  | AIndexA a Word -- extractvalue array: e.[n], n const
  | AIndex (Atom a) -- gep offset: e[e]
  deriving (THEUSUALA)
instance Data a => Plated (AStep a)

data AFunc a = AFunc a Var [(a, Var, Ty)] Ty (ANF a) deriving (THEUSUALA)
instance Data a => Plated (AFunc a)

-- In addition to normal ANF-y things, case arms and continuations of Rec blocks are labelled
-- with fresh variables (which will become the names of basic blocks in LLVM output)
data ANF a
  = AHalt (Atom a)
  | AAlloca a Var Ty (Atom a) (ANF a)
  | APrim a Var Ty Prim [Atom a] (ANF a)
  | ACast a Var Ty (Atom a) (ANF a)
  -- Control flow / name binding
  | ACall a Var Ty (Atom a) [Atom a] (ANF a)
  | ATail a Var Ty (Atom a) [Atom a]
  | ACase a (Atom a) [(Var, (Maybe Integer, ANF a))]
  | ARec a [AFunc a] Var (ANF a) -- Function bundle
  -- Aggregates
  | AGep a Var Ty (Atom a) (APath a) (ANF a) -- &e path (GEP)
  | ALoad a Var Ty (Atom a) (APath a) (ANF a) -- e path (GEP+load, extractvalue, extractelement)
  | AStore a (Atom a) (APath a) (Atom a) (ANF a) -- e path <- e; e (GEP+store)
  | AUpdate a Var Ty (Atom a) (APath a) (Atom a) (ANF a) -- e with path = e (insertvalue, insertelement)
  deriving (THEUSUALA)
instance Data a => Plated (ANF a)

-- Get names from a function bundle
bundleNames :: [AFunc a] -> [Var]
bundleNames = map (\ (AFunc _ f _ _ _) -> f)

toANF :: Exp Anno -> ANF Anno
toANF e = let (x, (_, k)) = go M.empty e `runState` (maxUsed e, id) in k (AHalt x) where
  go :: Map Var (Atom Anno) -> Exp Anno -> State (Var, ANF Anno -> ANF Anno) (Atom Anno)
  go σ = \case
    Var a x -> return $ M.findWithDefault (AVar a x) x σ
    Undef a -> return $ AUndef a
    Null a -> return $ ANull a
    ExtVar a s -> return $ AExtVar a s
    Alloca a e -> do
      e' <- go σ e
      x <- gen'
      push $ AAlloca a x (a^.typ) e'
      return $ AVar a x
    Int a i w -> return $ AInt a i w
    Ann _ e _ -> go σ e -- We have type annotations already
    Prim a p es -> do
      es' <- mapM (go σ) es
      x <- gen'
      push $ APrim a x (a^.typ) p es'
      return $ AVar a x
    Cast a e ty -> do
      e' <- go σ e
      x <- gen'
      push $ ACast a x ty e'
      return $ AVar a x
    Let a x t e1 e -> do
      e1' <- go σ e1
      go (M.insert x e1' σ) e
    Call a e es -> do
      e' <- go σ e
      es' <- mapM (go σ) es
      x <- gen'
      push $ ACall a x (a^.typ) e' es'
      return $ AVar a x
    Case a e pes -> do
      e' <- go σ e
      k <- get'
      pes' <- forM pes $ \ (p :=> e1) -> do
        (e1', k) <- goReset σ e1
        l <- gen'
        return (l, (p, k (AHalt e1')))
      put' $ const (k (ACase a e' pes'))
      return $ error "Tried to inspect return value of Case"
    Rec a helpers e -> do
      k <- get'
      helpers' <- forM helpers $ \ (Func a f axts t e1) -> do
        (e1', k) <- goReset σ e1
        return (AFunc a f axts t (k (AHalt e1')))
      l <- gen'
      put' $ k . ARec a helpers' l
      go σ e
    Array a es -> do es' <- mapM (go σ) es; return $ AArr a es'
    Tuple a es -> do es' <- mapM (go σ) es; return $ ATup a es'
    Struct a s es -> do es' <- mapM (go σ) es; return $ AStruct a s es'
    Vector a es -> do es' <- mapM (go σ) es; return $ AVec a es'
    Gep a e (Path ss) -> do
      (e', ss') <- goSteps e ss
      x <- gen'
      push $ AGep a x (a^.typ) e' (APath ss')
      return $ AVar a x
    Load a e (Path ss) -> do
      e' <- go σ e
      ss' <- mapM goStep ss
      x <- gen'
      push $ ALoad a x (a^.typ) e' (APath ss')
      return $ AVar a x
    Store a dst (Path ss) src e -> do
      src' <- go σ src
      (dst', ss') <- goSteps dst ss
      push $ AStore a dst' (APath ss') src'
      go σ e
    Update a e (Path ss) e1 -> do
      e' <- go σ e
      ss' <- mapM goStep ss
      e1' <- go σ e1
      x <- gen'
      push $ AUpdate a x (a^.typ) e' (APath ss') e1'
      return $ AVar a x
    where
      goReset σ e = put' id *> liftA2 (,) (go σ e) get'
      goSteps e ss = liftA2 (,) (go σ e) (mapM goStep ss)
      goStep = \case
        Proj a n -> return $ AProj a n
        Elem e -> AElem <$> go σ e
        IndexA a n -> return $ AIndexA a n
        Index e -> AIndex <$> go σ e
      gen' = modify' (first succ) >> fst <$> get
      push f = modify' (second (. f))
      put' = modify' . second . const
      get' = snd <$> get

-- -------------------- Put tail calls into ATail --------------------

toTails :: ANF Anno -> ANF Anno
toTails = transform $ \case
  ACall a x t f xs (AHalt (AVar _ x')) | x == x' -> ATail a x t f xs
  e -> e

-- -------------------- FV Annotation --------------------

atomAnno :: Atom a -> a
atomAnno = \case
  AVar a _ -> a
  AUndef a -> a
  ANull a -> a
  AExtVar a _ -> a
  AInt a _ _ -> a
  AArr a _ -> a
  ATup a _ -> a
  AStruct a _ _ -> a
  AVec a _ -> a

aStepAnno :: AStep a -> a
aStepAnno = \case
  AProj a _ -> a
  AElem x -> atomAnno x
  AIndexA a _ -> a
  AIndex x -> atomAnno x

aAnno :: ANF a -> a
aAnno = \case
  AHalt x -> atomAnno x
  AAlloca a _ _ _ _ -> a
  APrim a _ _ _ _ _  -> a
  ACast a _ _ _ _ -> a
  ACall a _ _ _ _ _ -> a
  ATail a _ _ _ _ -> a
  ACase a _ _ -> a
  ARec a _ _ _ -> a
  AGep a _ _ _ _ _ -> a
  ALoad a _ _ _ _ _ -> a
  AStore a _ _ _ _ -> a
  AUpdate a _ _ _ _ _ _ -> a

fvs e = aAnno e ^. fvSet

atomFVs :: Atom Anno -> Set Var
atomFVs x = atomAnno x ^. fvSet

afuncAnno :: AFunc a -> a
afuncAnno (AFunc a _ _ _ _) = a

afuncFVs :: AFunc Anno -> Set Var
afuncFVs f = afuncAnno f ^. fvSet

annoFV :: ANF Anno -> ANF Anno
annoFV = go where
  set s a = fvSet .~ s $ a
  names = S.fromList . bundleNames
  goAtom :: Atom Anno -> Atom Anno
  goAtom = \case
    AVar a x -> AVar (set (S.singleton x) a) x
    AUndef a -> AUndef (set S.empty a)
    ANull a -> ANull (set S.empty a)
    AExtVar a s -> AExtVar (set S.empty a) s
    AInt a i w -> AInt (set S.empty a) i w
    AArr a (map goAtom -> xs) -> AArr (set (foldMap atomFVs xs) a) xs
    ATup a (map goAtom -> xs) -> ATup (set (foldMap atomFVs xs) a) xs
    AStruct a s (map goAtom -> xs) -> AStruct (set (foldMap atomFVs xs) a) s xs
    AVec a (map goAtom -> xs) -> AVec (set (foldMap atomFVs xs) a) xs
  goAFuncs :: [AFunc Anno] -> [AFunc Anno]
  goAFuncs fs = map goAFunc fs where
    funcs = names fs
    goAFunc (AFunc a f (map (\ (a, x, t) -> (set S.empty a, x, t)) -> axts) t (go -> e)) =
      AFunc (set (fvs e S.\\ S.fromList (map (\ (_, x, _) -> x) axts) S.\\ funcs) a) f axts t e
  goStep :: AStep Anno -> AStep Anno
  goStep = \case
    AProj a n -> AProj (set S.empty a) n
    AElem x -> AElem (goAtom x)
    AIndexA a n -> AIndexA (set S.empty a) n
    AIndex x -> AIndex (goAtom x)
  stepFVs :: AStep Anno -> Set Var
  stepFVs s = aStepAnno s ^. fvSet
  go :: ANF Anno -> ANF Anno
  go = \case
    AHalt x -> AHalt (goAtom x)
    AAlloca a x t (goAtom -> y) (go -> e) ->
      AAlloca (set (S.delete x (fvs e) ∪ atomFVs y) a) x t y e
    APrim a x t p (map goAtom -> xs) (go -> e) ->
      APrim (set (S.delete x (fvs e) ∪ foldMap atomFVs xs) a) x t p xs e
    ACast a x t (goAtom -> y) (go -> e) ->
      ACast (set (S.delete x (fvs e) ∪ atomFVs y) a) x t y e
    ACall a x t (goAtom -> f) (map goAtom -> xs) (go -> e) ->
      ACall (set (S.delete x (fvs e) ∪ atomFVs f ∪ foldMap atomFVs xs) a) x t f xs e
    ATail a x t (goAtom -> f) (map goAtom -> xs) ->
      ATail (set (atomFVs f ∪ foldMap atomFVs xs) a) x t f xs
    ACase a (goAtom -> x) (map (fmap (fmap go)) -> pes) ->
      ACase (set (atomFVs x ∪ foldMap (fvs . snd . snd) pes) a) x pes
    ARec a (goAFuncs -> fs) l (go -> e) ->
      ARec (set ((foldMap afuncFVs fs ∪ fvs e) S.\\ names fs) a) fs l e
    AGep a x t (goAtom -> y) (APath (map goStep -> ss)) (go -> e) ->
      AGep (set (S.delete x (foldMap stepFVs ss ∪ fvs e)) a) x t y (APath ss) e
    ALoad a x t (goAtom -> y) (APath (map goStep -> ss)) (go -> e) ->
      ALoad (set (S.delete x (foldMap stepFVs ss ∪ fvs e)) a) x t y (APath ss) e
    AStore a (goAtom -> d) (APath (map goStep -> ss)) (goAtom -> s) (go -> e) ->
      AStore (set (atomFVs d ∪ foldMap stepFVs ss ∪ atomFVs s ∪ fvs e) a) d (APath ss) s e
    AUpdate a x t (goAtom -> y) (APath (map goStep -> ss)) (goAtom -> z) (go -> e) ->
      AUpdate
        (set (atomFVs y ∪ foldMap stepFVs ss ∪ atomFVs z ∪ S.delete x (fvs e)) a)
        x t y (APath ss) z e

-- -------------------- Annotate with variables bound under each subexpr --------------------

type BVMap = Map Var (Set Var)

bvs :: ANF Anno -> Set Var
bvs e = aAnno e ^. bvSet

atomBVs :: Atom Anno -> Set Var
atomBVs x = atomAnno x ^. bvSet

afuncBVs :: AFunc Anno -> Set Var
afuncBVs f = afuncAnno f ^. bvSet

annoBV :: ANF Anno -> ANF Anno
annoBV = go where
  set s a = bvSet .~ s $ a
  names = S.fromList . bundleNames
  goAtom :: Atom Anno -> Atom Anno
  goAtom = \case
    AVar a x -> AVar (set S.empty a) x
    AUndef a -> AUndef (set S.empty a)
    ANull a -> ANull (set S.empty a)
    AExtVar a s -> AExtVar (set S.empty a) s
    AInt a i w -> AInt (set S.empty a) i w
    AArr a (map goAtom -> xs) -> AArr (set S.empty a) xs
    ATup a (map goAtom -> xs) -> ATup (set S.empty a) xs
    AStruct a s (map goAtom -> xs) -> AStruct (set S.empty a) s xs
    AVec a (map goAtom -> xs) -> AVec (set S.empty a) xs
  goAFuncs :: [AFunc Anno] -> [AFunc Anno]
  goAFuncs fs = map goAFunc fs where
    funcs = names fs
    goAFunc (AFunc a f (map (\ (a, x, t) -> (set S.empty a, x, t)) -> axts) t (go -> e)) =
      AFunc (set (bvs e ∪ S.fromList (map (\ (_, x, _) -> x) axts) ∪ funcs) a) f axts t e
  goStep :: AStep Anno -> AStep Anno
  goStep = \case
    AProj a n -> AProj (set S.empty a) n
    AElem x -> AElem (goAtom x)
    AIndexA a n -> AIndexA (set S.empty a) n
    AIndex x -> AIndex (goAtom x)
  go :: ANF Anno -> ANF Anno
  go = \case
    AHalt x -> AHalt (goAtom x)
    AAlloca a x t (goAtom -> y) (go -> e) ->
      AAlloca (set (S.insert x (bvs e)) a) x t y e
    APrim a x t p (map goAtom -> xs) (go -> e) ->
      APrim (set (S.insert x (bvs e)) a) x t p xs e
    ACast a x t (goAtom -> y) (go -> e) ->
      ACast (set (S.insert x (bvs e)) a) x t y e
    ACall a x t (goAtom -> f) (map goAtom -> xs) (go -> e) ->
      ACall (set (S.insert x (bvs e)) a) x t f xs e
    ATail a x t (goAtom -> f) (map goAtom -> xs) ->
      ATail (set (S.singleton x) a) x t f xs
    ACase a (goAtom -> x) (map (fmap (fmap go)) -> pes) ->
      ACase (set (foldMap (bvs . snd . snd) pes) a) x pes
    ARec a (goAFuncs -> fs) l (go -> e) ->
      ARec (set (foldMap afuncBVs fs ∪ bvs e) a) fs l e
    AGep a x t (goAtom -> y) (APath (map goStep -> ss)) (go -> e) ->
      AGep (set (S.insert x (bvs e)) a) x t y (APath ss) e
    ALoad a x t (goAtom -> y) (APath (map goStep -> ss)) (go -> e) ->
      ALoad (set (S.insert x (bvs e)) a) x t y (APath ss) e
    AStore a (goAtom -> d) (APath (map goStep -> ss)) (goAtom -> s) (go -> e) ->
      AStore (set (bvs e) a) d (APath ss) s e
    AUpdate a x t (goAtom -> y) (APath (map goStep -> ss)) (goAtom -> z) (go -> e) ->
      AUpdate (set (S.insert x (bvs e)) a) x t y (APath ss) z e

-- Get names of bvs for each function/label
bvsOf :: ANF Anno -> BVMap
bvsOf = go M.empty where
  go m = \case
    AHalt _ -> m
    AAlloca _ _ _ _ e -> go m e
    APrim _ _ _ _ _ e -> go m e
    ACast _ _ _ _ e -> go m e
    ACall _ _ _ _ _ e -> go m e
    ATail{} -> m
    ACase _ _ xpes -> foldr (\ (x, (_, e)) m -> M.insert x (bvs e) (go m e)) m xpes
    ARec _ fs l e -> M.insert l (bvs e) $ foldr accAFunc m fs where
      accAFunc (AFunc a f axts t e) m = M.insert f (a^.bvSet) (go m e)
    AGep _ _ _ _ _ e -> go m e
    ALoad _ _ _ _ _ e -> go m e
    AStore _ _ _ _ e -> go m e
    AUpdate _ _ _ _ _ _ e -> go m e

-- -------------------- Call graph construction --------------------

graphOf :: ANF Anno -> CallGraph Anno
graphOf = go Nothing where
  union = M.unionWith (∪)
  gather = foldr union M.empty
  add f fnCall = M.alter add' f where
    add' = \case
      Just calls -> Just $ S.insert fnCall calls
      Nothing -> Just $ S.singleton fnCall
  goAFunc (AFunc _ f _ _ e) = go (Just f) e
  goAFuncs = foldr (union . goAFunc) M.empty
  go callerOf = \case
    AHalt _ -> M.empty
    AAlloca _ _ _ _ e -> go callerOf e
    APrim _ _ _ _ _ e -> go callerOf e
    ACast _ _ _ _ e -> go callerOf e
    ACall ((^. loc) -> locOf) x _ (AVar _ f) actualsOf e ->
      add f FnCall{locOf, isTail = False, callerOf, actualsOf} (go callerOf e)
    ACall _ _ _ _ _ e -> go callerOf e
    ATail ((^. loc) -> locOf) x _ (AVar _ f) actualsOf ->
      M.singleton f $ S.singleton FnCall{locOf, isTail = True, callerOf, actualsOf}
    ATail{} -> M.empty
    ACase ((^. loc) -> locOf) _ pes -> foldr goPes M.empty pes where
      goPes (x, (_, e)) r = add x fncall $ go (Just x) e `union` r
      fncall = FnCall{locOf, isTail = True, callerOf, actualsOf = []}
    ARec ((^. loc) -> locOf) fs l e -> add l fncall $ goAFuncs fs `union` go (Just l) e where
      fncall = FnCall{locOf, isTail = True, callerOf, actualsOf = []}
    AGep _ _ _ _ _ e -> go callerOf e
    ALoad _ _ _ _ _ e -> go callerOf e
    AStore _ _ _ _ e -> go callerOf e
    AUpdate _ _ _ _ _ _ e -> go callerOf e

-- -------------------- Determine which functions should be BBs --------------------

-- Liveness analysis maps a known function to variables live on entry
type Liveness = Map Var (Set Var)

-- Initially, liveness contains all free variables at every label
initLive :: ANF Anno -> Liveness
initLive = go where
  go = \case
    AHalt _ -> M.empty
    AAlloca _ _ _ _ e -> go e
    APrim _ _ _ _ _ e -> go e
    ACast _ _ _ _ e -> go e
    ACall _ _ _ _ _ e -> go e
    ATail{} -> M.empty
    ACase _ _ xpes -> foldMap (\ (x, (_, e)) -> M.insert x (fvs e) (go e)) xpes
    ARec _ fs l e -> foldr goAFunc (M.insert l (fvs e) (go e)) fs where
      goAFunc (AFunc a f _ _ e) m = M.insert f (a^.fvSet) (go e <> m)
    AGep _ _ _ _ _ e -> go e
    ALoad _ _ _ _ _ e -> go e
    AStore _ _ _ _ e -> go e
    AUpdate _ _ _ _ _ _ e -> go e

liveness :: BVMap -> CallGraph Anno -> ANF Anno -> Liveness
liveness bvs graph e = leastFlowAnno flow adjList (initLive e) where
  flow gen x = gen S.\\ (bvs !! x)
  adjList =
    [ (x, ys)
    | (x, callers) <- M.toList graph
    , let ys = [y | FnCall{callerOf = Just y} <- S.toList callers]
    ]

-- Determine which functions should be BBs based on liveness information
inferBBs :: Liveness -> BBs
inferBBs = M.keysSet . M.filter (not . S.null)

-- -------------------- Check that BBs only called in tail position --------------------

newtype BBErr = NotTail P.SourcePos

instance Show BBErr where
  show (NotTail pos) = P.sourcePosPretty pos ++ ": " ++ msg where
    msg = "this function belongs in a basic block and can only be called in tail position"

checkBBs :: CallGraph Anno -> BBs -> Either BBErr ()
checkBBs graph bbs =
  forM_ bbs $ \ x ->
    forM_ (graph !! x) $ \ FnCall{isTail, locOf} ->
      unless isTail . throwError $ NotTail locOf

-- -------------------- Code generation --------------------

data GenEnv = GenEnv
  { _genProto :: ([Ty], Ty) -- Current function's prototype
  , _genKnown :: Set Var
  , _genAllocas :: Bool -- Whether or not the current function owns any allocas
  }
makeLenses ''GenEnv

type GenM =
  WriterT Doc -- Accumulate global defns
  (ReaderT GenEnv
  (State Var)) -- Fresh label names

mainLabel :: Doc = "%start"

varG :: Var -> Doc
varG x = "%x" <> show'' x

gvarG :: Var -> Doc
gvarG x = "@f" <> show'' x

-- Instructions are always indented exactly once
inst :: Doc -> Doc
inst = indent . line' 

anfG :: CallGraph Anno -> BBs -> ANF Anno -> GenM Doc
anfG graph bbs = go where
  varG' :: Var -> GenM Doc
  varG' x = do
    known <- _genKnown <$> ask
    return $ if x ∉ bbs && x ∈ known then gvarG x else varG x
  args xs = do xs' <- mapM atomG xs; return $ "(" <> commaSep xs' <> ")"
  agg a l r xs = do xs' <- mapM atomG xs; return $ pp (a^.typ) <> " " <> l <> commaSep xs' <> r
  atomG = \case
    AVar a x -> do x' <- varG' x; return $ pp (a^.typ) <> " " <> x'
    AUndef a -> return $ pp (a^.typ) <> " undef"
    ANull a -> return $ pp (a^.typ) <> " null"
    AExtVar a s -> return $ pp (a^.typ) <> " @" <> fromString s
    AInt _ i w -> return $ "i" <> show'' w <> " " <> show'' i
    AArr a xs -> agg a "[" "]" xs
    ATup a xs -> agg a "{" "}" xs
    AStruct a s xs -> agg a "{" "}" xs
    AVec a xs -> agg a "<" ">" xs
  -- Like atomG, but omits the type annotation and can't do compound atoms
  opG = \case
    AVar _ x -> varG' x
    AUndef _ -> return "undef"
    ANull _ -> return "null"
    AExtVar _ s -> return $ "@" <> fromString s
    AInt _ i _ -> return $ show'' i
    a -> error $ "opG got compound atom: " ++ show a
  x .= doc = do x' <- varG' x; return . inst $ x' <> " = " <> doc
  (<:) :: Var -> Doc -> Doc
  lbl <: body = F.fold
    [ line' $ "x" <> show'' lbl <> ":"
    , body
    ]
  ret e line = (line <>) <$> go e
  storeG :: Atom Anno -> Doc -> GenM Doc
  storeG s p = do
    s' <- atomG s
    let ty = PTy (Ptr (atomAnno s ^. typ))
    return . inst $ "store " <> s' <> ", " <> pp ty <> " " <> p
  go :: ANF Anno -> GenM Doc
  go = \case
    AHalt x -> inst . ("ret " <>) <$> atomG x
    AAlloca a x pt y e -> do
      y' <- atomG y
      p <- gen
      let t = atomAnno y ^. typ
      alloca <- x .= ("alloca " <> pp t)
      store <- storeG y (varG x)
      local (genAllocas .~ True) . ret e $ alloca <> store
    APrim a x t p xs e -> case p of
      ShuffleVector -> do
        xs' <- commaSep <$> mapM atomG xs
        ret e =<< x .= (pp p <> " " <> xs')
      _ -> do
        xs' <- commaSep <$> mapM opG xs
        let ty = case xs of [] -> t; x:_ -> atomAnno x ^. typ
        ret e =<< x .= (pp p <> " " <> pp ty <> " " <> xs')
    ACast a x t y e ->
      case (t, atomAnno y ^. typ) of
        (t2@(PTy (Ptr _)), t1@(PTy (Ptr _))) -> do
          y' <- atomG y
          ret e =<< x .= ("bitcast " <> y' <> " to " <> pp t2)
        (t2, t1) ->
          error $ "Unsupported coercion from " ++ show t1 ++ " to " ++ show t2
    ACall a x t f xs e -> do
      f' <- opG f
      xs' <- args xs
      let call = "call " <> pp t <> " " <> f' <> xs'
      ret e =<< case t of
        Void -> pure $ inst call
        _ -> x .= call
    ATail a x t f xs -> case f of
      AVar _ f | f ∈ bbs -> return . inst $ "br label " <> varG f
      _ -> do
        xs' <- args xs
        f' <- opG f
        (ts', t') <- _genProto <$> ask
        let ts = map (\ x -> atomAnno x ^. typ) xs
        allocas <- _genAllocas <$> ask
        let
          must = if (ts, t) == (ts', t') then "must" else ""
          tail = if allocas then "" else must <> "tail "
        F.fold <$> sequence
          [ x .= (tail <> "call " <> pp t <> " " <> f' <> xs')
          , return . inst $ "ret " <> pp t <> " " <> varG x
          ]
    ACase a x lpes ->
      case [r | r@(_, (_, (Nothing, _))) <- zip [0..] lpes] of
        [] -> do
          l <- gen
          genSwitch (length lpes) ("fallback" <> show'' l) (inst "unreachable")
        (i, (l, (_, e))) : _ -> genSwitch i ("x" <> show'' l) =<< go e
      where
        genSwitch i defaultLabel defaultBody = do
          let ty = atomAnno x ^. typ
          let lpes' = take i lpes
          arms :: [Doc] <- forM lpes' $ \ (l, (_, e)) -> do
            e' <- go e
            return (l <: e')
          x' <- atomG x
          return $ F.fold
            [ inst $ "switch " <> x' <> ", label %" <> defaultLabel <> " ["
            , F.fold . for lpes' $ \ (l, (Just p, e)) ->
                indent . indent . line' $ pp ty <> " " <> show'' p <> ", label " <> varG l
            , indent $ line' "]"
            , F.fold arms
            , line' $ defaultLabel <> ":"
            , defaultBody
            ]
    ARec a fs l e -> do
      let s = S.fromList (bundleNames fs)
      (fs', e') <- local (genKnown %~ (s ∪)) $ (,) <$> mapM goAFunc fs <*> go e
      return $ F.fold
        [ inst $ "br label " <> varG l
        , F.fold fs'
        , l <: e'
        ]
    AGep a x t y (APath ss) e -> case atomAnno y ^. typ of
      (PTy (Ptr t)) -> do
        y' <- atomG y
        ss' <- gepPath ss
        ret e =<< x .= ("getelementptr " <> pp t <> ", " <> y' <> ", " <> ss')
      t -> error $ "GEP got type " ++ show t
    ALoad a x t y (APath ss) e -> case atomAnno y ^. typ of
      PTy (Ptr t') -> do
        y' <- atomG y
        ss' <- gepPath ss
        p <- gen
        load <- x .= ("load " <> pp t <> ", " <> pp (PTy (Ptr t)) <> " %ptr" <> show'' p)
        e' <- go e
        return $ F.fold
          [ inst $ "%ptr" <> show'' p <> " = getelementptr " <> pp t' <> ", " <> y' <> ", " <> ss'
          , load
          , e'
          ]
      Vec _ _ -> do
        y' <- atomG y
        ss' <- gepPath ss
        ret e =<< x .= ("extractelement " <> y' <> ", " <> ss')
      t | case t of Arr _ _ -> True; Tup _ -> True; TStruct _ -> True; _ -> False -> do
        y' <- atomG y
        let ss' = simplePath ss
        ret e =<< x .= ("extractvalue " <> y' <> ", " <> ss')
      t -> error $ "Load got type " ++ show t
    AStore a d (APath ss) s e -> case atomAnno d ^. typ of
      PTy (Ptr t) -> do
        d' <- atomG d
        ss' <- gepPath ss
        e' <- go e
        p <- gen
        store <- storeG s ("%ptr" <> show'' p)
        return $ F.fold
          [ inst $ "%ptr" <> show'' p <> " = getelementptr " <> pp t <> ", " <> d' <> ", " <> ss'
          , store
          , e'
          ]
      t -> error $ "Store got type " ++ show t
    AUpdate a x t y (APath ss) z e -> case atomAnno y ^. typ of
      Vec _ _ -> do
        y' <- atomG y
        ss' <- gepPath ss
        z' <- atomG z
        ret e =<< x .= ("insertelement " <> y' <> ", " <> z' <> ", " <> ss')
      t | case t of Arr _ _ -> True; Tup _ -> True; TStruct _ -> True; _ -> False -> do
        y' <- atomG y
        let ss' = simplePath ss
        z' <- atomG z
        ret e =<< x .= ("insertvalue " <> y' <> ", " <> z' <> ", " <> ss')
      t -> error $ "Update got type " ++ show t
    where
      simplePath ss = commaSep . for ss $ \case
        AProj _ n -> show'' n
        AIndexA _ n -> show'' n
        AElem _ -> error "simplePath: AElem"
        AIndex _ -> error "simplePath: AIndex"
      gepPath ss = fmap commaSep . forM ss $ \case
        AProj _ n -> return $ "i32 " <> show'' n
        AElem x -> atomG x
        AIndexA _ n -> return $ "i32 " <> show'' n
        AIndex x -> atomG x
  goAFunc (AFunc a f axts t e)
    | f ∈ bbs = do
        let
          calls :: [FnCall Anno] = S.toList $ graph !! f
          callers = callerOf <$> calls
          actualss = actualsOf <$> calls
          actualss' :: [[(Maybe Var, Atom Anno)]] =
            L.transpose (zipWith (\ caller actuals -> (caller,) <$> actuals) callers actualss)
          xts :: [(Var, Ty)] = map (\ (_, x, t) -> (x, t)) axts
          mkPhi (x, t) actuals = do
            actuals' <- mapM mkActual actuals
            x .= ("phi " <> pp t <> " " <> commaSep actuals')
          mkActual (caller, val) = do
            val' <- opG val
            return $ case caller of
              Just l -> "[" <> val' <> ", " <> varG l <> "]" :: Doc
              Nothing -> "[" <> val' <> ", " <> mainLabel <> "]"
        e' <- go e
        phis <- zipWithM mkPhi xts actualss'
        return $ f <: (F.fold phis <> e')
    | otherwise =
        let ts = map (\ (_, _, t) -> t) axts in 
        local (genAllocas .~ False) . local (genProto .~ (ts, t)) $ do
          e' <- go e
          tell $ F.fold
            [ let axts' = map (\ (_, x, t) -> pp t <> " " <> varG x) axts in
              line' $ "define " <> pp t <> " " <> gvarG f <> "(" <> commaSep axts' <> ") {"
            , e'
            , line' "}"
            ]
          return mempty

mainG :: Map String Ty -> Map String [Ty] -> CallGraph Anno -> BBs -> ANF Anno -> Doc
mainG extEnv structs graph bbs e =
  let
    (body, globals) = runWriterT (anfG graph bbs e)
      `runReaderT` GenEnv
        { _genProto = ([], PTy (I 32))
        , _genKnown = S.empty
        , _genAllocas = False
        }
      `evalState` 0
    extDecls = foldMap mkDecl (M.toList extEnv)
  in
  F.fold
    [ foldMap (line' . mkDecl) (M.toList extEnv)
    , foldMap (line' . mkStruct) (M.toList structs)
    , globals
    , line' "define i32 @main() {"
    , body
    , line' "}"
    ]
  where
    mkDecl = \case
      (f, FPtr ts t) ->
        "declare " <> pp t <> " @" <> fromString f <>
        "(" <> commaSep (map pp ts) <> ") nounwind"
      (x, t) -> error $ "Unsupported extern type: " ++ runDoc (pp t)
    mkStruct (x, ts) = "%" <> fromString x <> " = type {" <> commaSep (map pp ts) <> "}"

-- -------------------- Pretty printers --------------------

instance PP PTy where
  pp = \case
    I w -> "i" <> show'' w
    Half -> "half"
    Float -> "float"
    Double -> "double"
    FP128 -> "fp128"
    Ptr t -> pp t <> "*"

instance PP Ty where
  pp = \case
    Void -> "void"
    PTy t -> pp t
    Vec n t -> "<" <> show'' n <> " x " <> pp t <> ">"
    Arr n t -> "[" <> show'' n <> " x " <> pp t <> "]"
    Tup ts -> "{" <> commaSep (map pp ts) <> "}"
    TStruct s -> "%" <> fromString s
    FPtr ts t -> pp t <> "(" <> commaSep (map pp ts) <> ")*"

instance PP Bop where pp = fromString . map toLower . show

instance PP IDir where pp = fromString . tail . show
instance PP FDir where pp = fromString . tail . show

instance PP Prim where
  pp = \case
    BinArith bop -> pp bop
    ICmp dir -> "icmp " <> pp dir
    FCmp dir -> "fcmp " <> pp dir
    ShuffleVector -> "shufflevector"

instance PP (Func a) where
  pp (Func _ f xts t e) =
    let xts' = map (\ (_, x, t) -> show'' x <> ": " <> pp t) xts in
    show'' f <> "(" <> commaSep xts' <> "): " <> pp t <> " = " <> indent (pp e)

instance PP (Exp a) where
  pp = \case
    Var _ x -> show'' x
    Undef _ -> "undef"
    Null _ -> "null"
    ExtVar _ s -> fromString s
    Alloca _ e -> "ref (" <> pp e <> ")"
    Int _ i w -> show'' i <> "i" <> show'' w
    Ann _ e ty -> pp e <> ": " <> pp ty
    Prim _ p es -> pp p <> "(" <> commaSep (map (indent . pp) es) <> ")"
    Cast _ e ty -> pp e <> " as " <> pp ty
    Let _ x t e1 e -> F.fold
      [ line' $ "let " <> show'' x <> ": " <> pp t <> " = "
      , indent (pp e1)
      , line' "in "
      , pp e
      ]
    Call _ f es -> pp f <> "(" <> commaSep (map (indent . pp) es) <> ")"
    Case _ e apes -> F.fold
      [ line' $ "case " <> pp e <> " {"
      , indent $ commaSep (map goArm apes)
      , line' "}"
      ]
      where
        goArm = \case
          Just x :=> e -> line' $ show'' x <> " => " <> indent (pp e)
          Nothing :=> e -> line' $ "_ => " <> indent (pp e)
    Rec _ fs e -> F.fold
      [ line' $ goFuncs "rec " fs
      , line' "in "
      , pp e
      ]
      where
        goFuncs _ [] = ""
        goFuncs keyword [Func _ f axts t e] = F.fold
          [ keyword <> show'' f <> "(" <> commaSep (map goArg axts) <> "): " <> pp t <> " = "
          , indent $ pp e
          ]
          where goArg (_, x, t) = show'' x <> ": " <> pp t
        goFuncs keyword (f : fs) = F.fold
          [ goFuncs keyword [f]
          , line' $ goFuncs "and " fs
          ]
    Array _ es -> "[" <> commaSep (map (indent . pp) es) <> "]"
    Tuple _ es -> "{" <> commaSep (map (indent . pp) es) <> "}"
    Struct _ s es -> "%" <> fromString s <> " {" <> commaSep (map (indent . pp) es) <> "}"
    Vector _ es -> "<" <> commaSep (map (indent . pp) es) <> ">"
    Gep _ e p -> "&" <> pp e <> pp p
    Load _ e p -> pp e <> pp p
    Store _ d p s e -> F.fold
      [ line' $ pp d <> pp p <> " <- " <> indent (pp s) <> ";"
      , line' $ pp e
      ]
    Update _ e p e1 -> pp e <> " with " <> pp p <> " = " <> indent (pp e1)

instance PP (Path a) where
  pp (Path ss) = foldMap pp ss

instance PP (Step a) where
  pp = \case
    Proj _ n -> "." <> show'' n
    Elem e -> "<" <> indent (pp e) <> ">"
    IndexA _ n -> "[" <> show'' n <> "]"
    Index e -> "[" <> indent (pp e) <> "]"

instance PP (Atom a) where
  pp = \case
    AVar _ x -> show'' x
    AUndef _ -> "undef"
    ANull _ -> "null"
    AExtVar _ s -> fromString s
    AInt _ i w -> show'' i <> "i" <> show'' w
    AArr _ xs -> "[" <> commaSep (map (indent . pp) xs) <> "]"
    ATup _ xs -> "{" <> commaSep (map (indent . pp) xs) <> "}"
    AStruct _ s xs -> "%" <> fromString s <> " {" <> commaSep (map (indent . pp) xs) <> "}"
    AVec _ xs -> "<" <> commaSep (map (indent . pp) xs) <> ">"

instance PP (AFunc a) where
  pp (AFunc _ f xts t e) =
    let xts' = map (\ (_, x, t) -> show'' x <> ": " <> pp t) xts in
    show'' f <> "(" <> commaSep xts' <> "): " <> pp t <> " = " <> indent (pp e)

instance PP (ANF a) where
  pp = \case
    AHalt a -> line' $ "ret " <> pp a
    AAlloca _ x t y e -> bind x t ("alloca " <> pp y) e
    APrim _ x t p ys e -> bind x t (pp p <> "(" <> commaSep (map pp ys) <> ")") e
    ACast _ x t y e -> bind x t ("cast " <> pp y) e
    ACall _ x t f ys e -> bind x t (pp f <> "(" <> commaSep (map pp ys) <> ")") e
    ATail _ x t f ys ->
      line' $ "ret " <> show'' x <> ": " <> pp t <> " = "
        <> pp f <> "(" <> commaSep (map pp ys) <> ")"
    ACase _ x lpes -> F.fold
      [ line' $ "case " <> pp x <> " {"
      , indent $ commaSep (map goArm lpes)
      , line' "}"
      ]
      where
        goArm = \case
          (l, (Just x, e)) -> line' $ show'' x <> " => " <> show'' l <> ": " <> indent (pp e)
          (l, (Nothing, e)) -> line' $ "_ => " <> show'' l <> ": " <> indent (pp e)
    ARec _ fs l e -> F.fold
      [ line' $ goFuncs "rec " fs
      , line' "in "
      , line' $ show'' l <> ": "
      , indent $ pp e
      ]
      where
        goFuncs _ [] = ""
        goFuncs keyword [AFunc _ f axts t e] = F.fold
          [ keyword <> show'' f <> "(" <> commaSep (map goArg axts) <> "): " <> pp t <> " = "
          , indent $ pp e
          ] where goArg (_, x, t) = show'' x <> ": " <> pp t
        goFuncs keyword (f : fs) = F.fold
          [ goFuncs keyword [f]
          , line' $ goFuncs "and " fs
          ]
    where
      bind x t d1 e = line' $ "let " <> show'' x <> ": " <> pp t <> " = " <> d1 <> " in " <> pp e

-- -------------------- Parsing utils --------------------

newtype PError = PError String deriving (THEUSUAL)

data ParserState = ParserState
  { _pNames :: Map String Word -- Name -> internal id
  , _pExtEnv :: Map String Ty -- Extern name -> type
  , _pTyAliases :: Map String Ty -- Type aliases
  , _pStructs :: Map String [Ty] -- Struct definitions
  } deriving (THEUSUAL)

makeLenses ''ParserState

type Parser =
  ParsecT PError String
  (State ParserState)

instance P.ShowErrorComponent PError where showErrorComponent (PError s) = s

sc :: Parser ()
sc = L.space space1 empty empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme sc

symbol :: String -> Parser String
symbol = L.symbol sc

tryAll :: (Foldable f, MonadParsec e s m) => f (m a) -> m a
tryAll = foldr ((<|>) . P.try) empty

symbols :: [String] -> Parser String
symbols = tryAll . fmap symbol

parens :: Parser a -> Parser a
parens = P.between (symbol "(") (symbol ")")

braces :: Parser a -> Parser a
braces = P.between (symbol "{") (symbol "}")

brackets :: Parser a -> Parser a
brackets = P.between (symbol "[") (symbol "]")

angles :: Parser a -> Parser a
angles = P.between (symbol "<") (symbol ">")

listOf :: Parser a -> Parser [a]
listOf p = p `P.sepBy` symbol ","

tupleOf :: Parser a -> Parser [a]
tupleOf = parens . listOf

stringLiteral :: Parser String
stringLiteral = char '\"' *> P.manyTill L.charLiteral (char '\"')

-- -------------------- Parsing --------------------

keywords :: [String]
keywords = ["rec", "and", "in", "case", "as", "extern", "with", "type", "struct"]

word :: Parser String
word = do
  s <- lexeme $ (:) <$> (letterChar <|> char '_') <*> many (alphaNumChar <|> char '_')
  guard . not $ s `elem` keywords
  return s

varP :: Parser Var
varP = do
  x <- word
  (M.!? x) . _pNames <$> get >>= \case
    Nothing -> do
      n <- fromIntegral . M.size . _pNames <$> get
      modify' $ pNames %~ M.insert x n
      return n
    Just n -> return n

extVarP :: Parser String
extVarP = do
  x <- word
  exts <- _pExtEnv <$> get
  guard $ x `M.member` exts
  return x

tyAliasP :: Parser Ty
tyAliasP = do
  x <- word
  aliases <- _pTyAliases <$> get
  case aliases M.!? x of
    Just t -> return t
    Nothing -> empty

wordP :: Parser Word = read <$> lexeme (P.takeWhile1P (Just "digit") isDigit)

intP :: Parser Integer
intP = read <$> lexeme ((++) <$> tryAll ["-", ""] <*> P.takeWhile1P (Just "digit") isDigit)

ptyP :: Parser PTy
ptyP = tryAll
  [ "i" >> I <$> wordP
  , symbol "half" $> Half
  , symbol "float" $> Float
  , symbol "double" $> Double
  , symbol "fp128" $> FP128
  , parens ptyP
  , symbol "*" >> Ptr <$> tyP
  ]

tyP :: Parser Ty
tyP = tryAll
  [ symbol "void" $> Void
  , angles $ Vec <$> wordP <* symbol "x" <*> ptyP
  , brackets $ Arr <$> wordP <* symbol "x" <*> tyP
  , braces $ Tup <$> listOf tyP
  , symbol "fun" >> FPtr <$> tupleOf tyP <* symbol "->" <*> tyP
  , PTy <$> ptyP
  , parens tyP
  , tyAliasP
  , TStruct <$> word
  ]

widthP :: Parser Width = wordP

primP :: Parser Prim
primP = tryAll
  [ symbol "add" $> BinArith Add
  , symbol "mul" $> BinArith Mul
  , symbol "sub" $> BinArith Sub
  , symbol "div" $> BinArith Div
  , symbol "ieq" $> ICmp Ieq
  , symbol "ine" $> ICmp Ine
  , symbol "islt" $> ICmp Islt
  , symbol "isgt" $> ICmp Isgt
  , symbol "isle" $> ICmp Isle
  , symbol "isge" $> ICmp Isge
  , symbol "iult" $> ICmp Iult
  , symbol "iugt" $> ICmp Iugt
  , symbol "iule" $> ICmp Iule
  , symbol "iuge" $> ICmp Iuge
  , symbol "foeq" $> FCmp Foeq
  , symbol "fogt" $> FCmp Fogt
  , symbol "foge" $> FCmp Foge
  , symbol "folt" $> FCmp Folt
  , symbol "fole" $> FCmp Fole
  , symbol "fone" $> FCmp Fone
  , symbol "ford" $> FCmp Ford
  , symbol "fueq" $> FCmp Fueq
  , symbol "fugt" $> FCmp Fugt
  , symbol "fuge" $> FCmp Fuge
  , symbol "fult" $> FCmp Fult
  , symbol "fule" $> FCmp Fule
  , symbol "fune" $> FCmp Fune
  , symbol "funo" $> FCmp Funo
  , symbol "shufflevector" $> ShuffleVector
  ]

locP :: Parser Anno = (\ pos -> loc .~ pos $ emptyAnno) <$> P.getSourcePos

stepP :: Parser (Step Anno)
stepP = do
  loc <- locP
  tryAll
    [ symbol "." >> Proj loc <$> wordP
    , symbol "<" >> Elem <$> expP <* symbol ">"
    , symbol "[" >> tryAll
        [ IndexA loc <$> wordP
        , Index <$> expP
        ] <* symbol "]"
    ]

pathP :: Parser (Path Anno) = Path <$> some stepP

funcP :: Parser (Func Anno)
funcP =
  Func
    <$> locP <*> varP <*> tupleOf argP <* symbol ":" <*> tyP <* symbol "="
    <*> expP
  where
    argP = (,,) <$> locP <*> varP <* symbol ":" <*> tyP

armP :: Parser (Arm Anno)
armP = (:=>) <$> tryAll [Just <$> intP, symbol "_" $> Nothing] <* symbol "=>" <*> expP

externP :: Parser ()
externP = do
  (x, t) <- symbol "extern" >> (,) <$> word <* symbol ":" <*> tyP
  modify' $ pExtEnv %~ M.insert x t

aliasP :: Parser ()
aliasP = do
  (x, t) <- symbol "type" >> (,) <$> word <* symbol "=" <*> tyP
  modify' $ pTyAliases %~ M.insert x t

structP :: Parser ()
structP = do
  (x, ts) <- symbol "struct" >> (,) <$> word <*> braces (listOf tyP)
  modify' $ pStructs %~ M.insert x ts

expP' :: Bool -> Parser (Exp Anno)
expP' inGep = do
  many $ tryAll [externP, aliasP, structP]
  loc <- locP
  e <- tryAll
    [ Int loc <$> intP <*> (P.try (symbol "i" *> widthP) <|> pure 32)
    , Prim loc <$> primP <*> tupleOf expP
    , symbol "undef" $> Undef loc
    , symbol "null" $> Null loc
    , symbol "let" >> Let loc
        <$> varP <* symbol ":" <*> tyP <* symbol "="
        <*> expP <* symbol "in" <*> expP
    , symbol "case" >> Case loc <$> expP <*> braces (listOf armP)
    , symbol "rec" >> Rec loc <$> (funcP `P.sepBy` symbol "and") <* symbol "in" <*> expP
    , symbol "[" >> Array loc <$> listOf expP <* symbol "]"
    , symbol "{" >> Tuple loc <$> listOf expP <* symbol "}"
    , Struct loc <$> word <*> braces (listOf expP)
    , symbol "<" >> Vector loc <$> listOf expP <* symbol ">"
    , symbol "&" >> Gep loc <$> expP' True <*> pathP
    , symbol "ref" >> Alloca loc <$> parens expP
    , do
        bytes <- map (\ c -> Int loc (fromIntegral $ ord c) 8) <$> stringLiteral
        let cstr = bytes ++ [Int loc 0 8]
        return $ Cast loc (Alloca loc (Array loc cstr)) (PTy (Ptr (PTy (I 8))))
    , parens expP
    , ExtVar loc <$> extVarP
    , Var loc <$> varP
    ]
  e <- tryAll
    [ symbol ":" >> Ann loc e <$> tyP
    , symbol "as" >> Cast loc e <$> tyP
    , Call loc e <$> tupleOf expP
    , if inGep then empty else do
        p <- pathP
        tryAll
          [ symbol "<-" >> Store loc e p <$> expP <* symbol ";" <*> expP
          , pure (Load loc e p)
          ]
    , pure e
    ]
  tryAll
    [ symbol "with" >>
        L.foldl' (\ e (p, e1) -> Update loc e p e1) e
          <$> braces (listOf ((,) <$> pathP <* symbol "=" <*> expP))
    , pure e
    ]

expP :: Parser (Exp Anno)
expP = expP' False

parse' :: String -> String -> (Either String (Exp Anno), ParserState)
parse' fname s = prettyError $ mParse `runState` init where
  prettyError = first (first P.errorBundlePretty)
  mParse = P.runParserT (expP <* P.eof) fname s
  init = ParserState M.empty M.empty M.empty M.empty

parse :: String -> Either String (Exp Anno) = fst . parse' ""

parseFile :: FilePath -> IO (Either String (Exp Anno))
parseFile f = fst . parse' f <$> readFile f

-- -------------------- Full compilation --------------------

compile :: String -> Either String String
compile s = do
  let (r, pst) = parse' "" s
  e <- ub <$> r
  e <- runTC (check e (PTy (I 32))) (pst^.pExtEnv) (pst^.pStructs)
  let anf = annoBV . annoFV . toTails . toANF $ unfoldAggs e
  let graph = graphOf anf
  let bvs = bvsOf anf
  let l = liveness bvs graph anf
  let bbs = inferBBs l
  first show $ checkBBs graph bbs
  return . runDoc $ mainG (pst^.pExtEnv) (pst^.pStructs) graph bbs anf

compileFile :: FilePath -> IO (Either String String)
compileFile f = compile <$> readFile f
