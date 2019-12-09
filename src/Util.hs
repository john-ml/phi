module Util where

import Data.Set (Set); import qualified Data.Set as S
import Data.Map.Strict (Map); import qualified Data.Map.Strict as M
import Control.Monad
import Control.Monad.Writer.Strict (Writer); import qualified Control.Monad.Writer.Strict as W

accM :: (Foldable t, Monad m) => t a -> b -> (b -> a -> m b) -> m b
accM xs e f = foldM f e xs

acciM :: (Num i, Foldable t, Monad m) => t a -> b -> (i -> b -> a -> m b) -> m b
acciM xs e f = snd <$> foldM (\ (i, b) a -> (i + 1, ) <$> f i b a) (0, e) xs

for2 :: [a] -> [b] -> (a -> b -> c) -> [c]
for2 xs ys f = zipWith f xs ys

(∪) :: Ord a => Set a -> Set a -> Set a
(∪) = S.union

(∩) :: Ord a => Set a -> Set a -> Set a
(∩) = S.intersection

(∈) :: Ord a => a -> Set a -> Bool
(∈) = S.member

(∉) :: Ord a => a -> Set a -> Bool
(∉) = S.notMember

fixed :: (a -> Writer W.Any a) -> a -> a
fixed f x =
  let (y, W.Any p) = W.runWriter (f x) in
  if p then fixed f y else y
