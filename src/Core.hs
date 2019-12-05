module Core where

import qualified Data.List as L
import Data.Set (Set, (\\)); import qualified Data.Set as S
import Data.Map.Strict (Map); import qualified Data.Map.Strict as M
import Data.Semigroup
import qualified Data.Foldable as F
-- import Data.Bifunctor
import Data.Functor
-- import Data.Functor.Foldable
-- import Data.Functor.Foldable.TH
-- import Data.Functor.Classes
-- import Data.Functor.Compose
import Control.Monad
import Control.Monad.Except
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.Writer.Strict
-- import Control.Monad.Trans.Maybe
-- import Control.Applicative
-- import Text.Show.Deriving
-- 
-- import Data.SBV
-- import qualified Data.SBV.Internals as SBVI
-- 
import Data.String (IsString (..))
import Data.DList (DList); import qualified Data.DList as D
-- 
-- import Data.Char
-- import Data.Void
-- import Text.Megaparsec (ParsecT, MonadParsec)
-- import qualified Text.Megaparsec as P
-- import Text.Megaparsec.Char
-- import qualified Text.Megaparsec.Char.Lexer as L

type Var = Word
type Field = Word

data Binop
  = Add | Sub | Mul | Div
  deriving (Eq, Ord, Show)

data PTy
  = I Word
  | Half | Float | Double | FP128
  | Ptr Ty
  deriving (Eq, Ord, Show)

data Ty
  = Void
  | Prim PTy
  | Vec Integer PTy
  | Arr Integer Ty
  | Tup [Ty]
  | Fun [Ty] Ty
  deriving (Eq, Ord, Show)

data Helper a
  = Helper Var [(Var, Ty)] Ty (Exp a)
  deriving (Eq, Ord, Show)

data Arm a
  = Integer :=> Exp a
  deriving (Eq, Ord, Show)

type Ann a f = (a, f a)
type Exp a = Ann a Exp'
pattern Ann a x = (a, x)
pattern Ann_ x <- (_, x)
pattern Anno a <- (a, _)

type Width = Word
data Exp' a
  = Var Var
  | Int Integer Word
  | Unreachable
  | Tuple [Exp a]
  | Update (Exp a) [Field] (Exp a)
  | Proj (Exp a) Field
  | Elem (Exp a) (Exp a)
  | ElemV (Exp a) (Exp a)
  | Coerce (Exp a) Ty
  | Binop (Exp a) Binop (Exp a)
  | Let Var Ty (Exp a) (Exp a)
  | Call (Exp a) [Exp a]
  | Addr (Exp a)
  | Load (Exp a)
  | Store (Exp a) (Exp a) (Exp a)
  | Rec [Ann a Helper] (Exp a)
  | Case (Exp a) (Exp a) [Arm a]
  | Exp a ::: Ty
  deriving (Eq, Ord, Show)

pattern AVar a x = (a, Var x)
pattern AInt a i w = (a, Int i w)
pattern AUnreachable a = (a, Unreachable)
pattern ATuple a es = (a, Tuple es)
pattern AUpdate a e1 p e2 = (a, Update e1 p e2)
pattern AProj a e n = (a, Proj e n)
pattern AElem a e1 e2 = (a, Elem e1 e2)
pattern AElemV a e1 e2 = (a, ElemV e1 e2)
pattern ACoerce a e t = (a, Coerce e t)
pattern ABinop a e1 o e2 = (a, Binop e1 o e2)
pattern ALet a x t e1 e = (a, Let x t e1 e)
pattern ACall a e es = (a, Call e es)
pattern AAddr a e = (a, Addr e)
pattern ALoad a e = (a, Load e)
pattern AStore a d s e = (a, Store d s e)
pattern ARec a fs e = (a, Rec fs e)
pattern ACase a e d pes = (a, Case e d pes)
pattern AAnn a e ty = (a, e ::: ty)

pattern AHelper a f xts t e = (a, Helper f xts t e)

data Loc = Loc
  { locFile :: Maybe String
  , locLine :: Int
  , locCol :: Int
  } deriving (Eq, Ord, Show)

-- -- -------------------- Utils --------------------
-- 
-- for :: [a] -> (a -> b) -> [b]
-- for xs f = map f xs
-- 
-- for2 :: [a] -> [b] -> (a -> b -> c) -> [c]
-- for2 xs ys f = zipWith f xs ys
-- 
-- (∪) :: Ord a => Set a -> Set a -> Set a
-- (∪) = S.union
-- 
-- (∈) :: Ord a => a -> Set a -> Bool
-- (∈) = S.member
-- 
-- (∉) :: Ord a => a -> Set a -> Bool
-- (∉) = S.notMember
-- 
-- -- Fixed point computation
-- fixed :: (a -> Writer Any a) -> a -> a
-- fixed f x = if p then fixed f y else y where (y, Any p) = runWriter (f x)
-- 

-- -------------------- Some boilerplate to work with annotations --------------------

class Has t tup where π :: tup -> t
instance Has t t where π = id
instance Has t (t, tup) where π = fst
instance Has t tup => Has t (a, tup) where π = π . snd
proj :: Has t tup => tup -> t; proj = π

raise :: (Has Loc a, MonadError (Loc, e) m) => a -> e -> m r
raise a e = throwError (π a, e)

-- -------------------- Doc formatting utils --------------------

type Str = DList Char -- For efficient catenation

-- Indentation as input
type Doc = Reader Str Str
deriving instance Semigroup a => Semigroup (Reader r a)
deriving instance Monoid a => Monoid (Reader r a)

show' :: Show a => a -> Str
show' = D.fromList . show

show'' :: Show a => a -> Doc
show'' = pure . show'

runDoc :: Doc -> String
runDoc c = D.toList $ c `runReader` ""

instance IsString Doc where fromString = pure . D.fromList

indent :: Doc -> Doc
indent = local ("  " <>)

line :: Str -> Doc
line l = reader $ \ s -> s <> l <> "\n"

line' :: Doc -> Doc
line' l = reader $ \ s -> s <> runReader l s <> "\n"

calate :: Doc -> [Doc] -> Doc
calate sep ds = F.fold (L.intersperse sep ds)

commaSep :: [Doc] -> Doc
commaSep = calate ", "

class PP a where pp :: a -> Doc

instance PP PTy where
  pp = \case
    I w -> "i" <> show'' w
    Half -> "half"
    Float -> "float"
    Double -> "double"
    FP128 -> "FP128"
    Ptr t -> pp t <> "*"

instance PP Ty where
  pp = \case
    Void -> "void"
    Prim t -> pp t
    Vec n t -> "<" <> show'' n <> " x " <> pp t <> ">"
    Arr n t -> "[" <> show'' n <> " x " <> pp t <> "]"
    Tup ts -> "{" <> commaSep (map pp ts) <> "}"
    Fun ts t -> "((" <> commaSep (map pp ts) <> ") -> " <> pp t <> ")"

instance PP (Helper a) where
  pp (Helper f xts t e) =
    let xts' = map (\ (x, t) -> show'' x <> ": " <> pp t) xts in
    show'' f <> "(" <> commaSep xts' <> "): " <> pp t <> " =" <> indent (pp e)

instance PP Binop where
  pp = \case
    Add -> "+"
    Mul -> "*"
    Sub -> "-"
    Div -> "/"

instance PP (Exp a) where
  pp = \case
    AVar _ x -> show'' x
    AInt _ i w -> show'' i <> "i" <> show'' w
    AUnreachable _ -> "unreachable"
    ATuple _ es -> "{" <> commaSep (map pp es) <> "}"
    AUpdate _ e1 p e2 -> pp e1 <> " {" <> calate "." (show'' <$> p) <> " = " <> pp e2 <> "}"
    AProj _ e n -> pp e <> "." <> show'' n
    AElem _ e1 e2 -> pp e1 <> "[" <> pp e2 <> "]"
    AElemV _ e1 e2 -> pp e1 <> "<" <> pp e2 <> ">"
    ACoerce _ e t -> pp e <> " as " <> pp t
    ABinop _ e1 o e2 -> "(" <> pp e1 <> " " <> pp o <> " " <> pp e2 <> ")"
    ALet _ x t e1 e -> F.fold
      [ line' $ "let " <> show'' x <> ": " <> pp t <> " = "
      , indent (pp e1)
      , line $ " in "
      , pp e
      ]
    ACall _ e es -> pp e <> "(" <> commaSep (map pp es) <> ")"
    AAddr _ e -> "&" <> pp e
    ALoad _ e -> "*" <> pp e
    AStore _ d s e -> F.fold
      [ line' $ pp d <> " := " <> pp s <> ";"
      , pp e
      ]
    ARec _ fs e -> undefined -- TODO
    ACase _ e d pes -> undefined -- TODO
    AAnn _ e ty -> "(" <> pp e <> " : " <> pp ty <> ")"

-- -------------------- Variables --------------------

-- Generic fold over variables
foldVars :: Monoid m => (Var -> m) -> Exp a -> m
foldVars f = \case
  AVar _ x -> f x
  AInt _ _ _ -> mempty
  AUnreachable _ -> mempty
  ATuple _ es -> foldMap (foldVars f) es
  AUpdate _ e1 _ e2 -> foldVars f e1 <> foldVars f e2
  AProj _ e _ -> foldVars f e
  AElem _ e1 e2 -> foldVars f e1 <> foldVars f e2
  AElemV _ e1 e2 -> foldVars f e1 <> foldVars f e2
  ACoerce _ e _ -> foldVars f e
  ABinop _ e1 _ e2 -> foldVars f e1 <> foldVars f e2
  ALet _ x _ e1 e -> f x <> foldVars f e1 <> foldVars f e
  ACall _ e es -> foldVars f e <> foldMap (foldVars f) es
  AAddr _ e -> foldVars f e
  ALoad _ e -> foldVars f e
  AStore _ d s e -> foldVars f d <> foldVars f s <> foldVars f e
  ARec _ fs e ->
    foldMap (\ (AHelper _ f' xts _ e) -> f f' <> foldMap (f . fst) xts <> foldVars f e) fs <>
    foldVars f e
  ACase _ e d pes ->
    foldVars f e <> foldVars f d <> foldMap (\ (_ :=> e) -> foldVars f e) pes
  AAnn _ e _ -> foldVars f e

-- Smallest variable v such that {v + 1, v + 2, ..} are all unused
maxUsed :: Exp a -> Var
maxUsed = getMax . foldVars Max

-- Used variables
uv :: Exp a -> Set Var
uv = foldVars S.singleton

-- Rename bound variables for unique bindings
ub :: Exp a -> Exp a
ub p = go M.empty p `evalState` maxUsed p where
  go σ = \case
    AVar a x -> return $ AVar a (σ ! x)
    AInt a i w -> return $ AInt a i w
    AUnreachable a -> return $ AUnreachable a
    ATuple a es -> ATuple a <$> mapM (go σ) es
    AUpdate a e1 p e2 -> AUpdate a <$> go σ e1 <*> pure p <*> go σ e2
    AProj a e n -> AProj a <$> go σ e <*> pure n
    AElem a e1 e2 -> AElem a <$> go σ e1 <*> go σ e2
    AElemV a e1 e2 -> AElemV a <$> go σ e1 <*> go σ e2
    ACoerce a e t -> ACoerce a <$> go σ e <*> pure t
    ABinop a e1 (·) e2 -> ABinop a <$> go σ e1 <*> pure (·) <*> go σ e2
    ALet a x t e1 e -> do x' <- gen; ALet a x' t <$> go σ e1 <*> go (M.insert x x' σ) e
    ACall a e es -> ACall a <$> go σ e <*> mapM (go σ) es
    AAddr a e -> AAddr a <$> go σ e
    ALoad a e -> ALoad a <$> go σ e
    AStore a d s e -> AStore a <$> go σ d <*> go σ s <*> go σ e
    ARec a helpers e -> do
      let fs = map (\ (AHelper _ f _ _ _) -> f) helpers
      fs' <- replicateM (length fs) gen
      let σ' = foldr (uncurry M.insert) σ (zip fs fs')
      helpers' <- forM helpers $ \ (AHelper a f xts t e) -> do
        let xs = map fst xts
        xs' <- replicateM (length xts) gen
        let σ'' = foldr (uncurry M.insert) σ' (zip xs xs')
        AHelper a (σ ! f) (zip xs' (map snd xts)) t <$> go σ'' e
      ARec a helpers' <$> go σ' e
    ACase a e d pes ->
      ACase a
        <$> go σ e <*> go σ d
        <*> mapM (\ (p :=> e) -> (p :=>) <$> go σ e) pes
    AAnn a e ty -> AAnn a <$> go σ e <*> pure ty
  σ ! x = M.findWithDefault x x σ
  gen = modify' succ *> get

-- -- Free variables
-- fvF :: Base Process (Set Var) -> Set Var
-- fvF = \case
--   HaltF -> S.empty
--   NewF x vs -> S.delete x vs
--   SendF s d vs -> S.insert s (S.insert d vs)
--   RecvF d s vs -> S.insert s (S.delete d vs)
--   EvalF x e vs -> foldMap S.singleton e ∪ S.delete x vs
--   DoF e vs -> foldMap S.singleton e
--   vs :|:$ ws -> vs ∪ ws
--   vs :+:$ ws -> vs ∪ ws
--   LoopF vs -> vs
--   MatchF x (L.unzip -> (xs, vss)) -> S.fromList (x : xs) ∪ F.fold vss
--   ForeignF _ vs -> vs
-- 
-- fv :: Process -> Set Var
-- fv = cata fvF
-- 

-- -------------------- Type checking --------------------

data TCErr
  = NotInScope Var
  | ExGotShape String Ty
  | ExGot Ty Ty
  | BadPath [Field]
  | Custom String

instance PP TCErr where
  pp = \case
    NotInScope x -> line $ "Variable not in scope: " <> show' x
    ExGotShape shape ty ->
      line' $ "Expected " <> pure (D.fromList shape) <> " but got " <> pp ty
    ExGot ex got -> line' $ "Expected " <> pp ex <> " but got " <> pp got
    BadPath p -> line $ "Bad path: " <> F.fold (L.intersperse "." (show' <$> p))
    Custom s -> line $ D.fromList s

type TC = ExceptT (Loc, TCErr) (Reader (Map Var Ty))

var :: Has Loc a => a -> Var -> TC (Exp (Ty, a))
var a x = (M.!? x) <$> ask >>= \case
  Just ty -> return $ AVar (ty, a) x
  Nothing -> raise a $ NotInScope x

pattern AnnTy e ty <- ((\ x -> (x, x)) -> (e, Anno (ty, _)))
pattern AnnoTy ty <- Anno (ty, _)

check :: Has Loc a => Exp a -> Ty -> TC (Exp (Ty, a))
check exp ty = case exp of
  AUnreachable a -> return $ AUnreachable (ty, a)
  ACase a e d pes -> infer e >>= \case
    AnnTy e' (Prim (I _)) ->
      ACase (ty, a) e'
        <$> check d ty
        <*> mapM (\ (p :=> e) -> (p :=>) <$> check e ty) pes
    AnnoTy ty -> raise a $ ExGotShape "integer" ty
  exp@(Anno a) -> infer exp >>= \case
    AnnTy exp' ty'
      | ty' == ty -> return exp'
      | otherwise -> raise a $ ExGot ty ty'

infer :: Has Loc a => Exp a -> TC (Exp (Ty, a))
infer = \case
  AAnn _ e ty -> check e ty
  AVar a x -> var a x
  AInt a i w -> return $ AInt (Prim (I w), a) i w
  ATuple a es -> do
    es' <- mapM infer es
    return $ ATuple (Tup (map (\ (AnnoTy t) -> t) es'), a) es'
  AUpdate a e1 _ e2 -> undefined -- TODO
  AProj a e n -> infer e >>= \case
    AnnTy e' (Tup ts)
      | n < L.genericLength ts -> return $ AProj (ts!!fromIntegral n, a) e' n
      | otherwise -> raise a $ BadPath [n]
    AnnoTy ty -> raise a $ ExGotShape "tuple" ty
  AElem a e1@(Anno a1) e2@(Anno a2) -> (,) <$> infer e1 <*> infer e2 >>= \case
    (AnnTy e1' (Arr _ t), AnnTy e2' (Prim (I _))) -> return $ AElem (t, a) e1' e2'
    (AnnoTy (Arr _ _), AnnoTy ty) -> raise a2 $ ExGotShape "integer" ty
    (AnnoTy ty, _) -> raise a1 $ ExGotShape "array" ty
  AElemV a e1@(Anno a1) e2@(Anno a2) -> (,) <$> infer e1 <*> infer e2 >>= \case
    (AnnTy e1' (Vec _ t), AnnTy e2' (Prim (I _))) -> return $ AElemV (Prim t, a) e1' e2'
    (AnnoTy (Vec _ _), AnnoTy ty) -> raise a2 $ ExGotShape "integer" ty
    (AnnoTy ty, _) -> raise a1 $ ExGotShape "vector" ty
  ACoerce a e t -> ACoerce (t, a) <$> infer e <*> pure t
  ABinop a e1 o e2@(Anno a2) -> (,) <$> infer e1 <*> infer e2 >>= \case
    (AnnTy e1' t1, AnnTy e2' t2)
      | t1 == t2 -> return $ ABinop (t1, a) e1' o e2'
      | otherwise -> raise a2 $ ExGot t1 t2
  ALet a x t e1 e -> do
    e1' <- check e1 t
    AnnTy e' ty <- local (M.insert x t) (infer e)
    return $ ALet (ty, a) x t e1' e'
  ACall a e es -> infer e >>= \case
    AnnTy e' (Fun ts t) -> ACall (t, a) e' <$> zipWithM check es ts
    AnnoTy ty -> raise a $ ExGotShape "function" ty
  AAddr a e -> do
    AnnTy e' t <- infer e
    return $ AAddr (Prim (Ptr t), a) e'
  ALoad a e -> infer e >>= \case
    AnnTy e' (Prim (Ptr t)) -> return $ ALoad (t, a) e'
    AnnoTy ty -> raise a $ ExGotShape "pointer" ty
  AStore a d s e -> infer d >>= \case
    AnnTy d' (Prim (Ptr t)) -> do
      s' <- check s t
      AnnTy e' ty <- infer e
      return $ AStore (ty, a) d' s' e'
    AnnoTy ty -> raise a $ ExGotShape "pointer" ty
  ARec a helpers e -> do
    let fs = map (\ (AHelper _ f _ _ _) -> f) helpers
    let ts = map (\ (AHelper _ _ xts t _) -> Fun (map snd xts) t) helpers
    local (M.union . M.fromList $ zip fs ts) $ do
      helpers' <- forM helpers $ \ (AHelper a f xts t e) ->
        AHelper (Void, a) f xts t <$> local (M.union $ M.fromList xts) (check e t)
      AnnTy e' ty <- infer e
      return $ ARec (ty, a) helpers' e'

-- -- -------------------- Code generation utils --------------------
-- 
-- varG :: Var -> Doc
-- varG x = (M.! x) . fst <$> ask >>= \case
--   Rbx -> pure "rbx"
--   R12 -> pure "r12"
--   R13 -> pure "r13"
--   R14 -> pure "r14"
--   R15 -> pure "r15"
--   Spill n -> pure $ "spill" <> show' n
-- 
-- declG :: Str -> Var -> Doc
-- declG ty x = (M.! x) . fst <$> ask >>= \case
--   Spill _ -> pure ty <> " " <> varG x
--   _ -> varG x
-- 
-- procG :: Doc -> Doc -> Doc
-- procG name body = F.fold
--   [ line' ("void " <> name <> "(void) {")
--   , indent body
--   , indent $ line "asm (\"jmp gt_stop\\t\\n\");"
--   , line "}"
--   ]
-- 
-- spillProcG :: Set Var -> Doc -> Doc -> Doc
-- spillProcG spilled name body = procG name $ F.fold
--   [ line "gt_ch *rsp = (gt_ch *)gt_self()->rsp + 1;"
--   , F.fold . for2 [0..] (S.toAscList spilled) $ \ offset x ->
--       line' $ "gt_ch " <> varG x <> " = rsp[" <> show'' offset <> "];"
--   , body
--   ]
-- 
-- mainG :: Doc -> Doc
-- mainG body = F.fold
--   [ line "int main(void) {"
--   , indent $ F.fold
--     [ line "gt_init();"
--     , body
--     , line "gt_exit(0);"
--     ]
--   , line "}"
--   ]

-- -------------------- Code generation --------------------

varG :: Var -> Doc
varG x = "%" <> show'' x

type Gen =
  ReaderT (Set Var) -- Rec functions
  (StateT Var -- Fresh names for helper functions
  (Writer (Doc, Doc))) -- (Global definitions, code generated along the way)

fresh :: Gen Var
fresh = get <* modify' succ

gensym :: Doc -> Gen Doc
gensym name = ("%" <>) . (name <>) . show'' <$> fresh

instrG :: Doc -> Gen Var
instrG instr = do
  x <- fresh
  tell (mempty, line' $ "%" <> show'' x <> " = " <> instr)
  return x

gen :: Has Ty a => Exp a -> Gen Var
gen = \case
  AVar _ x -> return x
  -- AInt (π -> ty :: Ty) i _ -> instrG $ "add " <> pp ty <> " 0, " <> show'' i
  AUnreachable _ -> undefined -- TODO
  -- ATuple _ es -> "{" <> commaSep (map pp es) <> "}"
  -- AUpdate _ e1 p e2 -> pp e1 <> " {" <> calate "." (show'' <$> p) <> " = " <> pp e2 <> "}"
  -- AProj _ e n -> pp e <> "." <> show'' n
  -- AElem _ e1 e2 -> pp e1 <> "[" <> pp e2 <> "]"
  -- AElemV _ e1 e2 -> pp e1 <> "<" <> pp e2 <> ">"
  -- ACoerce _ e t -> pp e <> " as " <> pp t
  -- ABinop _ e1 o e2 -> "(" <> pp e1 <> " " <> pp o <> " " <> pp e2 <> ")"
  -- ALet _ x t e1 e -> F.fold
  --   [ line' $ "let " <> show'' x <> ": " <> pp t <> " = "
  --   , indent (pp e1)
  --   , line $ " in "
  --   , pp e
  --   ]
  -- ACall _ e es -> pp e <> "(" <> commaSep (map pp es) <> ")"
  -- AAddr _ e -> "&" <> pp e
  -- ALoad _ e -> "*" <> pp e
  -- AStore _ d s e -> F.fold
  --   [ line' $ pp d <> " := " <> pp s <> ";"
  --   , pp e
  --   ]
  -- ARec _ fs e -> undefined -- TODO
  -- ACase _ e d pes -> undefined -- TODO

-- genTop :: AnnProcess -> Gen Doc
-- genTop (FV vs p) = do
--   tell $ line "#include <stdlib.h>"
--   tell $ line "#include \"runtime.c\""
--   mainG <$> gen (ABoth (vs, Any False) (AHalt (S.empty, Any False)) p)
-- 
-- runGen :: Alloc -> Gen Doc -> String
-- runGen alloc m =
--   let (main, helpers) = runWriter $ m `runReaderT` alloc `evalStateT` 0 in
--   runDoc alloc (helpers <> main)
-- 
-- -- -------------------- AST Compilation --------------------
-- 
-- codeGen' :: Bool -> Process -> IO String
-- codeGen' sinking p = do
--   let p' = (if sinking then sinkNews else id) . fvAnno $ ub p
--   a <- alloc p'
--   return $ runGen a (genTop p')
-- 
-- codeGen :: Process -> IO String
-- codeGen = codeGen' True
-- 
-- -- -------------------- Parsing utils --------------------
-- 
-- newtype PError = PError String deriving (Eq, Ord)
-- 
-- type Parser = ParsecT PError String (State (Map String Word64))
-- 
-- instance P.ShowErrorComponent PError where
--   showErrorComponent (PError s) = s
-- 
-- sc :: Parser ()
-- sc = L.space space1 empty empty
-- 
-- lexeme :: Parser a -> Parser a
-- lexeme = L.lexeme sc
-- 
-- symbol :: String -> Parser String
-- symbol = L.symbol sc
-- 
-- tryAll :: (Foldable f, MonadParsec e s m) => f (m a) -> m a
-- tryAll = foldr ((<|>) . P.try) empty
-- 
-- symbols :: [String] -> Parser String
-- symbols = tryAll . fmap symbol
-- 
-- parens :: Parser a -> Parser a
-- parens = P.between (symbol "(") (symbol ")")
-- 
-- braces :: Parser a -> Parser a
-- braces = P.between (symbol "{") (symbol "}")
-- 
-- -- -------------------- Parsing --------------------
-- 
-- keywords :: [String]
-- keywords = ["new", "all", "any", "loop", "match", "foreign", "do"]
-- 
-- word :: Parser String
-- word = do
--   s <- lexeme $ some (alphaNumChar <|> char '_')
--   guard . not $ s `elem` keywords
--   return s
-- 
-- varP' :: Bool -> Parser Var
-- varP' strict = do
--   x <- word
--   (M.!? x) <$> get >>= \case
--     Nothing | strict ->
--       P.customFailure . PError $ "Variable not in scope: " ++ x
--     Nothing -> do
--       n <- fromIntegral . M.size <$> get
--       modify' (M.insert x n)
--       return n
--     Just n -> return n
-- 
-- varP :: Parser Var = varP' True
-- 
-- bindP :: Parser Var = varP' False
-- 
-- haltP :: Parser Process = Halt <$ symbol "."
-- 
-- contP :: Parser Process = P.try haltP <|> symbol ";" *> procP
-- 
-- newP :: Parser Process = symbol "new" >> mkNew <$> some bindP <*> contP where
--   mkNew xs p = foldr New p xs
-- 
-- sendP :: Parser Process = Send <$> varP <* symbol "->" <*> varP <*> contP
-- 
-- recvP :: Parser Process = Recv <$> bindP <* symbol "<-" <*> varP <*> contP
-- 
-- binopP :: String -> (Process -> Process -> Process) -> Parser Process
-- binopP keyword op = symbol keyword >> mk <$> braces (many procP) where
--   mk = \case
--     [] -> Halt
--     [p] -> p
--     x:xs -> L.foldl' op x xs
-- 
-- anyP :: Parser Process = binopP "any" (:+:)
-- 
-- allP :: Parser Process = binopP "all" (:|:)
-- 
-- loopP :: Parser Process = symbol "loop" >> Loop <$> procP
-- 
-- matchP :: Parser Process
-- matchP = symbol "match" >> Match <$> varP <*> braces (many armP) where
--   armP = (,) <$> varP <* symbol "=>" <*> procP
-- 
-- foreignP :: Parser Process
-- foreignP = symbol "foreign" >> symbol "{" >> Foreign <$> suffix 0 <*> procP where
--   suffix n = (++) <$> P.takeWhileP Nothing nonBrace <*> bodyP n
--   bodyP n = tryAll
--     [ (++) <$> string "{" <*> suffix (n + 1)
--     , string "}" >>
--         if n == 0
--         then sc $> ""
--         else (\ x y -> "}" ++ x ++ y) <$> spaces <*> suffix (n - 1)
--     ]
--   nonBrace = \case
--     '{' -> False
--     '}' -> False
--     _ -> True
--   spaces = P.takeWhileP Nothing isSpace
-- 
-- foreignExpP :: Parser ForeignExp
-- foreignExpP = Call <$> word <*> many argP where
--   argP = P.try (parens foreignExpP) <|> (Atom <$> varP)
-- 
-- evalP :: Parser Process
-- evalP = Eval <$> bindP <* symbol "<~" <*> foreignExpP <*> contP
-- 
-- doP :: Parser Process
-- doP = symbol "do" >> Do <$> foreignExpP <*> contP
-- 
-- procP :: Parser Process
-- procP = tryAll
--   [ -- Try stuff that starts with keywords first...
--     newP, doP, anyP, allP, loopP, matchP, foreignP
--   , -- ...before the stuff with arrows in them
--     sendP, recvP, evalP
--   ]
-- 
-- parse' :: String -> String -> Either String Process
-- parse' fname s =
--   first P.errorBundlePretty
--     $ P.runParserT (procP <* P.eof) fname s `evalState` M.empty
-- 
-- parse :: String -> Either String Process
-- parse s = parse' "" s
-- 
-- parseFile :: FilePath -> IO (Either String Process)
-- parseFile f = parse' f <$> readFile f
-- 
-- -- -------------------- Compilation to C --------------------
-- 
-- transpile :: String -> IO (Either String String)
-- transpile s = mapM codeGen (parse s)
-- 
-- transpileFile :: FilePath -> IO (Either String String)
-- transpileFile f = parseFile f >>= \case
--   Left err -> return $ Left err
--   Right p -> Right <$> codeGen p
-- 
-- -- -------------------- Full compilation --------------------
-- 
-- compile :: String -> FilePath -> FilePath -> IO ()
-- compile s cOut binOut = transpile s >>= \case
--   Left err -> putStrLn err
--   Right c -> do
--     writeFile cOut c
--     let flags = ["-O2", "-g", "-I", "runtime", "runtime/gt_switch.s", cOut, "-o", binOut]
--     P.createProcess (P.proc "gcc" flags)
--     return ()
-- 
-- compileFile :: FilePath -> FilePath -> FilePath -> IO ()
-- compileFile piIn cOut binOut = do
--   s <- readFile piIn
--   compile s cOut binOut
