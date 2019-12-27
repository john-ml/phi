{-# LANGUAGE BangPatterns #-}

fib :: Int -> Integer
fib !n = go n 0 1 where
  go :: Int -> Integer -> Integer -> Integer
  go 0 !a _ = a
  go !n !a !b = go (n - 1) b (a + b)

main = print $ fib 250000 > 0
