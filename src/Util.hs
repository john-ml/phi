module Util where

import Prelude hiding ((!!))

import Data.Set (Set); import qualified Data.Set as S
import Data.Map.Strict (Map); import qualified Data.Map.Strict as M
import Control.Monad
import Control.Monad.Writer.Strict (Writer); import qualified Control.Monad.Writer.Strict as W
import Control.Monad.State.Strict
import Control.Monad.Reader
import Data.Functor
import qualified Data.Foldable as F
import qualified Data.List as L
import qualified Data.Graph as G
import Data.Semilattice.Join
import Data.Semilattice.Lower

import Data.String (IsString (..))
import Data.DList (DList); import qualified Data.DList as D

accM :: (Foldable t, Monad m) => t a -> b -> (b -> a -> m b) -> m b
accM xs e f = foldM f e xs

acciM :: (Num i, Foldable t, Monad m) => t a -> b -> (i -> b -> a -> m b) -> m b
acciM xs e f = snd <$> foldM (\ (i, b) a -> (i + 1, ) <$> f i b a) (0, e) xs

for2 :: [a] -> [b] -> (a -> b -> c) -> [c]
for2 xs ys f = zipWith f xs ys

foriM :: (Enum i, Num i, Monad m) => [a] -> (i -> a -> m b) -> m [b]
foriM xs f = zipWithM f [0..] xs

for :: [a] -> (a -> b) -> [b]
for xs f = map f xs

(∪) :: Ord a => Set a -> Set a -> Set a
(∪) = S.union

(∩) :: Ord a => Set a -> Set a -> Set a
(∩) = S.intersection

(∈) :: Ord a => a -> Set a -> Bool
(∈) = S.member

(∉) :: Ord a => a -> Set a -> Bool
(∉) = S.notMember

(⊆) :: Ord a => Set a -> Set a -> Bool
(⊆) = S.isSubsetOf

fixed :: (a -> Writer W.Any a) -> a -> a
fixed f x =
  let (y, W.Any p) = W.runWriter (f x) in
  if p then fixed f y else y

-- -------------------- Pattern synonyms --------------------

pattern p :∧: q <- (\ x -> (x, x) -> (p, q))

-- -------------------- Pretty-printing --------------------

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
line l = reader $ \ s -> "\n" <> s <> l

line' :: Doc -> Doc
line' l = reader $ \ s -> "\n" <> s <> runReader l s

calate :: Doc -> [Doc] -> Doc
calate sep ds = F.fold (L.intersperse sep ds)

commaSep :: [Doc] -> Doc
commaSep = calate ", "

class PP a where pp :: a -> Doc

-- -------------------- Graphs and flow algorithms --------------------

class PartialOrd a where (⊑) :: a -> a -> Bool
instance Ord a => PartialOrd (Set a) where (⊑) = S.isSubsetOf

type AdjList v = [(v, [v])]

(!!) :: (Lower a, Ord l) => Map l a -> l -> a
ann !! l = M.findWithDefault lowerBound l ann

leastFlowAnno :: forall loc lab ann. Ord loc =>
  -- Labels form a join semilattice
  (Lower lab, Join lab, PartialOrd lab) =>
  -- An annotation maps every location to a label
  (ann ~ Map loc lab) =>
  -- Flow function: arguments are label + location that it's flowing to
  -- e.g. for liveness, arguments are live-out + loc; returns live-out \\ killed-by-loc
  (lab -> loc -> lab) ->
  -- Graph over which to compute a least annotation
  AdjList loc -> 
  -- Initial and resulting annotation 
  ann -> ann 
leastFlowAnno f adjList ann = go sccs `execState` ann where
  -- Helpers to play nicely with Data.Graph + compute SCCs
  edges = [(k, k, ks) | (k, ks) <- adjList]
  (g, nodeOf, vertexOf) = G.graphFromEdges edges
  sccs = G.stronglyConnComp edges
  succs l = maybe [] ((\ (_, _, ls) -> ls) . nodeOf) (vertexOf l)
  anyM f xs = or <$> mapM f xs
  -- Run flow analysis over all SCCs
  go :: [G.SCC loc] -> State ann ()
  go = mapM_ $ \case
    G.AcyclicSCC l -> void $ goLoc l
    G.CyclicSCC ls -> goSCC ls
  -- Compute fixed point for each SCC of locations
  goSCC :: [loc] -> State ann ()
  goSCC ls = do
    p <- anyM goLoc ls
    when p (goSCC ls)
  -- Update all successors of a single location
  goLoc :: loc -> State ann Bool
  goLoc l = do
    lab <- (!! l) <$> get
    anyM (flow lab) (succs l)
  -- Update label at given location using flow function
  flow :: lab -> loc -> State ann Bool
  flow lab loc =
    let new = f lab loc in
    (!! loc) <$> get >>= \case
      old | new ⊑ old -> return False
          | otherwise -> modify' (M.insert loc (new \/ old)) $> True