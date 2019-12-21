module Util where

import Data.Set (Set); import qualified Data.Set as S
import Data.Map.Strict (Map); import qualified Data.Map.Strict as M
import Control.Monad
import Control.Monad.Writer.Strict (Writer); import qualified Control.Monad.Writer.Strict as W
import Control.Monad.Reader
import qualified Data.Foldable as F
import qualified Data.List as L

import Data.String (IsString (..))
import Data.DList (DList); import qualified Data.DList as D

accM :: (Foldable t, Monad m) => t a -> b -> (b -> a -> m b) -> m b
accM xs e f = foldM f e xs

acciM :: (Num i, Foldable t, Monad m) => t a -> b -> (i -> b -> a -> m b) -> m b
acciM xs e f = snd <$> foldM (\ (i, b) a -> (i + 1, ) <$> f i b a) (0, e) xs

for2 :: [a] -> [b] -> (a -> b -> c) -> [c]
for2 xs ys f = zipWith f xs ys

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