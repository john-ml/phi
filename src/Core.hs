module Core where

import qualified Data.List as L
import Data.Set (Set, (\\)); import qualified Data.Set as S
import Data.Map.Strict (Map); import qualified Data.Map.Strict as M
import Data.Semigroup
-- import qualified Data.Foldable as F
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
-- import Control.Monad.Writer.Strict
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

pattern AHelper a f xts t e = (a, Helper f xts t e)

data Loc = Loc
  { locFile :: Maybe String
  , locLine :: Int
  , locCol :: Int
  } deriving (Eq, Ord, Show)

--  Syntax                               Restrictions         LLVM counterpart
--  p ∈ primitive type
--    = i1 | i2 | ..
--    | half | float | double | fp128
--    | t*
--  t ∈ type
--    = p
--    | void
--    | <n x p>                          n > 0
--    | [n x t]
--    | {t, ..}
--  e ∈ expr
--    = x                                Identifier
--    | true | false
--    | 0 | 1 | ..
--    | 'a' | 'b' | ..
--    | "" | "a" | ..
--    | null
--    | none
--    | unreachable
--    | {e, ..}
--    | e {n.m... = e}                                        updatevalue
--    | e.n                                                   extractvalue
--    | e[e]                                                  extractvalue
--    | e<e>                                                  extractelement
--    | e as t                                                bitcast, sext, strunc, ..
--    | e + e | e * e | ..
--    | let x = e in e
--    | e(e, ..)                                              call, tail call
--    | &e                                                    getelementptr
--    | *e                                                    load
--    | e := e; e                                             store
--    | rec f(x, ..) = e and .. in e     Tail calls only      Labelled blocks + phi nodes
--    | case e {n => e, .., n => e}                           switch

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

-- -------------------- Variables --------------------

-- Generic fold over variables
foldVars :: Monoid m => (Var -> m) -> Exp a -> m
foldVars f = \case
  (_, Var x) -> f x
  (_, Int _ _) -> mempty
  (_, Unreachable) -> mempty
  (_, Tuple es) -> foldMap (foldVars f) es
  (_, Update e1 _ e2) -> foldVars f e1 <> foldVars f e2
  (_, Proj e _) -> foldVars f e
  (_, Elem e1 e2) -> foldVars f e1 <> foldVars f e2
  (_, ElemV e1 e2) -> foldVars f e1 <> foldVars f e2
  (_, Coerce e _) -> foldVars f e
  (_, Binop e1 _ e2) -> foldVars f e1 <> foldVars f e2
  (_, Let x _ e1 e) -> f x <> foldVars f e1 <> foldVars f e
  (_, Call e es) -> foldVars f e <> foldMap (foldVars f) es
  (_, Addr e) -> foldVars f e
  (_, Load e) -> foldVars f e
  (_, Store d s e) -> foldVars f d <> foldVars f s <> foldVars f e
  (_, Rec fs e) ->
    foldMap (\ (_, Helper f' xts _ e) -> f f' <> foldMap (f . fst) xts <> foldVars f e) fs <>
    foldVars f e
  (_, Case e d pes) ->
    foldVars f e <> foldVars f d <> foldMap (\ (_ :=> e) -> foldVars f e) pes

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
      ACase a <$> go σ e <*> go σ d <*> mapM (\ (p :=> e) -> (p :=>) <$> go σ e) pes
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
  | Custom String

type TC = ExceptT (Loc, TCErr) (Reader (Map Var Ty))

var :: Has Loc a => a -> Var -> TC Ty
var a x = (M.!? x) <$> ask >>= \case
  Just ty -> return ty
  Nothing -> raise a $ NotInScope x

check :: Has Loc a => Exp a -> Ty -> TC ()
check exp ty = case exp of
  AUnreachable _ -> return ()
  ATuple a es -> case ty of
    Tup ts -> undefined
    ty -> raise a $ ExGotShape "tuple" ty
  AUpdate a e1 _ e2 -> undefined
  ABinop a e1 _ e2 -> undefined
  ARec a fs e -> undefined
  ACase a e d pes -> infer e >>= \case
    Prim (I _) -> check d ty *> mapM_ (\ (_ :=> e) -> check e ty) pes
    ty -> raise a $ ExGotShape "integer" ty

infer :: Has Loc a => Exp a -> TC Ty
infer = \case
  AVar a x -> var a x
  AInt _ _ w -> return $ Prim (I w)
  ATuple _ es -> Tup <$> mapM infer es
  AUpdate a e1 _ e2 -> undefined
  AProj a e n -> infer e >>= \case
    Tup ts
      | n < L.genericLength ts -> return $ ts!!fromIntegral n
      | otherwise -> raise a . Custom $ "tuple has no " ++ show n ++ "th element"
    ty -> raise a $ ExGotShape "tuple" ty
  AElem _ e1@(Anno a1) e2@(Anno a2) -> (,) <$> infer e1 <*> infer e2 >>= \case
    (Arr _ t, Prim (I _)) -> return t
    (Arr _ _, ty) -> raise a2 $ ExGotShape "integer" ty
    (ty, _) -> raise a1 $ ExGotShape "array" ty
  AElemV _ e1@(Anno a1) e2@(Anno a2) -> (,) <$> infer e1 <*> infer e2 >>= \case
    (Vec _ t, Prim (I _)) -> return $ Prim t
    (Vec _ _, ty) -> raise a2 $ ExGotShape "integer" ty
    (ty, _) -> raise a1 $ ExGotShape "vector" ty
  ACoerce a e t -> infer e $> t
  ABinop a e1 o e2 -> undefined
  ALet a x t e1 e -> check e1 t *> local (M.insert x t) (infer e)
  ACall a e es -> infer e >>= \case
    Fun ts t -> zipWithM check es ts $> t
    ty -> raise a $ ExGotShape "function" ty
  AAddr _ e -> Prim . Ptr <$> infer e
  ALoad a e -> infer e >>= \case
    Prim (Ptr t) -> return t
    ty -> raise a $ ExGotShape "pointer" ty
  AStore a d s e -> infer d >>= \case
    Prim (Ptr t) -> check s t *> infer e
    ty -> raise a $ ExGotShape "pointer" ty
  ARec a fs e -> undefined

-- -------------------- Code formatting utils --------------------

type Str = DList Char -- For efficient catenation

-- Indentation as input
type Code = Reader Str Str
deriving instance Semigroup a => Semigroup (Reader r a)
deriving instance Monoid a => Monoid (Reader r a)

show' :: Show a => a -> Str
show' = D.fromList . show

show'' :: Show a => a -> Code
show'' = pure . show'

runCode :: Code -> String
runCode c = D.toList $ c `runReader` ""

instance IsString Code where fromString = pure . D.fromList

indent :: Code -> Code
indent = local ("  " <>)

line :: Str -> Code
line l = reader $ \ s -> s <> l <> "\n"

line' :: Code -> Code
line' l = reader $ \ s -> s <> runReader l s <> "\n"

-- -- -------------------- Code generation utils --------------------
-- 
-- varG :: Var -> Code
-- varG x = (M.! x) . fst <$> ask >>= \case
--   Rbx -> pure "rbx"
--   R12 -> pure "r12"
--   R13 -> pure "r13"
--   R14 -> pure "r14"
--   R15 -> pure "r15"
--   Spill n -> pure $ "spill" <> show' n
-- 
-- declG :: Str -> Var -> Code
-- declG ty x = (M.! x) . fst <$> ask >>= \case
--   Spill _ -> pure ty <> " " <> varG x
--   _ -> varG x
-- 
-- procG :: Code -> Code -> Code
-- procG name body = F.fold
--   [ line' ("void " <> name <> "(void) {")
--   , indent body
--   , indent $ line "asm (\"jmp gt_stop\\t\\n\");"
--   , line "}"
--   ]
-- 
-- spillProcG :: Set Var -> Code -> Code -> Code
-- spillProcG spilled name body = procG name $ F.fold
--   [ line "gt_ch *rsp = (gt_ch *)gt_self()->rsp + 1;"
--   , F.fold . for2 [0..] (S.toAscList spilled) $ \ offset x ->
--       line' $ "gt_ch " <> varG x <> " = rsp[" <> show'' offset <> "];"
--   , body
--   ]
-- 
-- mainG :: Code -> Code
-- mainG body = F.fold
--   [ line "int main(void) {"
--   , indent $ F.fold
--     [ line "gt_init();"
--     , body
--     , line "gt_exit(0);"
--     ]
--   , line "}"
--   ]
-- 
-- -- -------------------- Code generation --------------------
-- 
-- type Gen =
--   ReaderT Alloc -- Result of allocation
--   (StateT Word64 -- Fresh names for helper functions
--   (Writer Code)) -- Maintain helper functions generated along the way
-- 
-- gensym :: Str -> Gen Str
-- gensym name = ("var_" <>) . (name <>) . show' <$> get <* modify' succ
-- 
-- newG :: Var -> Code
-- newG x = line' $ declG "gt_ch" x <> " = gt_chan();"
-- 
-- sendG :: Var -> Var -> Code
-- sendG s d = line' $ "gt_write(" <> varG d <> ", " <> varG s <> ");"
-- 
-- recvG :: Var -> Var -> Code
-- recvG d s = line' $ declG "gt_ch" d <> " = gt_read(" <> varG s <> ");"
-- 
-- foreignExpG :: ForeignExp -> Code
-- foreignExpG = \case
--   Atom x -> varG x
--   Call f xs ->
--     pure (D.fromList f) <> "(" <>
--       F.fold (L.intersperse "," (foreignExpG <$> xs)) <> ")"
-- 
-- evalG :: Var -> ForeignExp -> Code
-- evalG x e = line' $ declG "gt_ch" x <> " = " <> foreignExpG e <> ";"
-- 
-- doG :: ForeignExp -> Code
-- doG e = line' $ foreignExpG e <> ";"
-- 
-- bothG :: AnnProcess -> Set Var -> AnnProcess -> Gen Code
-- bothG p qs q = do
--   f <- gensym "f"
--   t <- gensym "t"
--   rsp <- gensym "rsp"
--   p' <- gen p
--   q' <- gen q
--   alloc <- ask
--   let (spilled, unspilled) = S.partition (wasSpilled alloc) qs
--   let pG = if S.null spilled then procG else spillProcG spilled
--   tell $ pG (pure f) q'
--   return $ F.fold
--     [ line $ "gt_t " <> t <> " = " <> call f spilled
--     , F.fold . for (S.toAscList unspilled) $ \ v ->
--         line' $ pure t <> "->" <> varG v <> " = " <> varG v <> ";"
--     , if not $ S.null spilled
--       then line $ "gt_ch *" <> rsp <> " = ((gt_ch *)" <> t <> "->rsp) + 1;"
--       else ""
--     , F.fold . for2 [0..] (S.toAscList spilled) $ \ offset v ->
--         line' $ pure rsp <> "[" <> show'' offset <> "] = " <> varG v <> ";"
--     , p'
--     ]
--   where
--     call :: Str -> Set Var -> Str
--     call f spilled
--       | S.null spilled = "gt_go(" <> f <> ", " <> show' (stackSize spilled q) <> ");"
--       | otherwise = "gt_go_alloca(" <>
--           f <> ", " <> show' (spillSize spilled) <> ", " <>
--           show' (stackSize spilled q) <> ");"
-- 
--     wasSpilled :: Alloc -> Var -> Bool
--     wasSpilled alloc q =
--       case alloc M.!? q of
--         Just (Spill _) -> True
--         _ -> False
-- 
--     spillSize :: Set Var -> Int
--     spillSize spilled = 16 * ((S.size spilled + 1) `div` 2)
--     
--     stackSize :: Set Var -> AnnProcess -> Int
--     stackSize spilled = \case
--       Evals True _ -> 0x100000 + spillSize spilled
--       Evals False _ -> 0x100 + spillSize spilled
-- 
-- gen :: AnnProcess -> Gen Code
-- gen = \case
--   AHalt _ -> pure ""
--   ANew _ x p -> (newG x <>) <$> gen p
--   ASend _ s d p -> (sendG s d <>) <$> gen p
--   ARecv _ d s p -> (recvG d s <>) <$> gen p
--   AEval _ x e p -> (evalG x e <>) <$> gen p
--   ADo _ e p -> (doG e <>) <$> gen p
--   ABoth _ p (FV qs q) -> bothG p qs q
--   APick _ p q -> do
--     p' <- gen p
--     q' <- gen q
--     return $ F.fold
--       [ line "if (rand() & 1) {"
--       , indent p'
--       , line "} else {"
--       , indent q'
--       , line "}"
--       ]
--   ALoop _ p -> do
--     p' <- gen p
--     return $ F.fold
--       [ line "for (;;) {"
--       , indent p'
--       , line "}"
--       ]
--   AMatch _ x yps -> do
--     let x' = varG x
--     yps' <- forM yps $ \ (y, p) -> (varG y, ) <$> gen p
--     return $ F.fold
--       [ line $ "if (0) {}"
--       , F.fold . for yps' $ \ (y', p') -> F.fold
--         [ line' $ "else if (" <> x' <> " == " <> y' <> ") {"
--         , indent p'
--         , line "}"
--         ]
--       ]
--   AForeign _ body p -> do
--     tell . foldMap (line . D.fromList) $ lines body
--     gen p
-- 
-- genTop :: AnnProcess -> Gen Code
-- genTop (FV vs p) = do
--   tell $ line "#include <stdlib.h>"
--   tell $ line "#include \"runtime.c\""
--   mainG <$> gen (ABoth (vs, Any False) (AHalt (S.empty, Any False)) p)
-- 
-- runGen :: Alloc -> Gen Code -> String
-- runGen alloc m =
--   let (main, helpers) = runWriter $ m `runReaderT` alloc `evalStateT` 0 in
--   runCode alloc (helpers <> main)
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
