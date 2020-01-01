module Main where

import Phi
import Data.Functor
import Control.Applicative
import System.Environment
import qualified Data.Map as M

print' :: (Functor f, Show (f ())) => f a -> IO ()
print' x = print (x $> ())

testTC :: String -> IO ()
testTC s = either putStrLn print' $ (\ x -> runTC x M.empty M.empty) . infer =<< (ub <$> parse s)

toANF' :: String -> Either String (ANF TyAnn)
toANF' s = fmap (toANF . snd) . (\ x -> runTC x M.empty M.empty) . infer =<< (ub <$> parse s)

testANF :: String -> IO ()
testANF s = either putStrLn print' (toANF' s)

tests :: IO ()
tests = do
  either putStrLn print' $ parse "3i32"
  either putStrLn print' $ parse "let x: i32 = 3i32 in 4i32"
  testTC "let x: i32 = 3i32 in mul(2i32, 3i32)"
  testTC "let x: i32 = 3i32 in mul(2i32, 3i64)"
  either putStrLn (print' . ub) $ parse "rec f(x: i32): i32 = x in f(x)"
  testTC "rec f(x: i32): i32 = x in f(4i32)"
  let tri = unlines
       [ "rec tri(n: i32): i32 ="
       , "  case n {"
       , "    0 => 0i32,"
       , "    _ => add(n, tri(sub(n, 1i32)))"
       , "  }"
       , "and trail(n: i32): i32 ="
       , "  rec go(n: i32, acc: i32): i32 ="
       , "    case n {"
       , "      0 => acc,"
       , "      _ => go(sub(n, 1i32), add(n, acc))"
       , "    }"
       , "  in"
       , "  go(n, 0i32)"
       , "in tri(4i32)"
       ]
  either putStrLn (print' . ub) $ parse tri
  testTC tri
  let tri' = toANF' tri
  either putStrLn print' tri'
  let tri'' = annoBV . annoFV . toTails <$> tri'
  either putStrLn print' tri''
  let graph = graphOf <$> tri''
  either putStrLn print graph
  either putStrLn putStrLn $ compile tri
  let bvs = bvsOf <$> tri''
  let l = liftA3 liveness bvs graph tri''
  let bbs = inferBBs <$> l
  either putStrLn print bbs
  let mult = unlines
       [ "rec mult(n: i32, m: i32): i32 ="
       , "  rec go(n: i32, acc: i32): i32 ="
       , "    case n {"
       , "      0 => acc,"
       , "      _ => go(sub(n, 1i32), add(m, acc))"
       , "    }"
       , "  in go(n, 0i32)"
       , "in mult(10i32, 11i32)"
       ]
  either putStrLn (print' . ub) $ parse mult
  testTC mult
  let mult' = annoBV . annoFV . toTails <$> toANF' mult
  either putStrLn print' mult'
  let graph = graphOf <$> mult'
  either putStrLn print graph
  let bvs = bvsOf <$> mult'
  let l = liftA3 liveness bvs graph mult'
  let bbs = inferBBs <$> l
  either putStrLn print bbs
  either putStrLn putStrLn $ compile mult
  let multBad = unlines
       [ "rec mult(n: i32, m: i32): i32 ="
       , "  rec go(n: i32, acc: i32): i32 ="
       , "    case n {"
       , "      0 => acc,"
       , "      _ => add(go(sub(n, 1i32), add(m, acc)), 0i32)"
       , "    }"
       , "  in go(n, 0i32)"
       , "in mult(10i32, 11i32)"
       ]
  let multBad' = annoBV . annoFV . toTails <$> toANF' multBad
  let graph = graphOf <$> multBad'
  let bvs = bvsOf <$> multBad'
  let l = liftA3 liveness bvs graph multBad'
  let bbs = inferBBs <$> l
  either putStrLn print bbs
  either putStrLn putStrLn $ compile multBad
  let fib = unlines
       [ "rec fib(n: i32): i256 ="
       , "  let x: i256 = add(0i256, 0i256) in" -- To force φ-nodes
       , "  rec go(n: i32, a: i256, b: i256): i256 ="
       , "    case n {"
       , "      0 => a,"
       , "      _ => go(sub(n, 1i32), add(x, b), add(a, b))"
       , "    }"
       , "  in go(n, 0i256, 1i256)"
       , "in"
       , "let res: i256 = fib(100i32) in"
       , "0i32"
       ]
  either putStrLn putStrLn $ compile fib
  either putStrLn putStrLn . compile $ unlines
    [ "rec fib(n: i32): i256 ="
    , "  rec go(n: i32, a: i256, b: i256): i256 ="
    , "    case n {"
    , "      0 => a,"
    , "      _ => go(sub(n, 1i32), b, add(a, b))"
    , "    }"
    , "  in go(n, 0i256, 1i256)"
    , "in"
    , "let res: i256 = fib(100i32) in"
    , "0i32"
    ]
  either putStrLn putStrLn . compile $ unlines
    [ "rec f(g: fun (i32, i32) -> i32, x: i32): i32 = g(x, x) in"
    , "rec k(n: i32, m: i32): i32 = add(mul(n, n), mul(m, m)) in"
    , "f(k, 3i32)"
    ]
  either putStrLn putStrLn . compile $ unlines
    [ "let x: i32 = add(0i32, 0i32) in"
    , "rec even(n: i32): i32 ="
    , "  case n {"
    , "    0 => add(x, 1),"
    , "    1 => add(x, 0),"
    , "    _ => odd(sub(n, 1))"
    , "  }"
    , "and odd(n: i32): i32 ="
    , "  case n {"
    , "    0 => 0,"
    , "    1 => 1,"
    , "    _ => even(sub(n, 1))"
    , "  }"
    , "in"
    , "even(4)"
    ]
  either putStrLn putStrLn . compile $ "rec f(_: <2 x i32>): i32 = f(<0, 1>) in 0i32"
  either putStrLn putStrLn . compile $ "rec f(_: {i32, i32}): i32 = f({0, 1}) in 0i32"
  either putStrLn putStrLn . compile $ unlines
    [ "rec f(_: {i64, {i32, i64}, {<2 x i32>, i32}}): i32 ="
    , "  f({0i64, {1i32, 2i64}, {<3i32, 4i32>, 5i32}})"
    , "in 0i32"
    ]
  either putStrLn putStrLn . compile $ unlines
    [ "rec f(_: {i64, {i32, i64}, {<2 x i32>, i32}}): i32 ="
    , "  f({0i64, {1, 2i64}, {<3, 4>, 5i33}})"
    , "in 0"
    ]
  either putStrLn putStrLn . compile $ unlines
    [ "rec f(_: {i64, {i32, i64}, {<2 x i32>, i32}}): i32 ="
    , "  let x: {i64, {i32, i64}, {<2 x i32>, i32}} = {0i64, {1, 2i64}, {<3, 4>, 5}} in"
    , "  f(x)"
    , "in 0"
    ]
  either putStrLn putStrLn . compile
    $ "rec f(xs: <4 x i32>, ys: <4 x i32>): <4 x i32> = add(xs, ys) in 0"
  either putStrLn putStrLn . compile
    $ "rec f(xs: <4 x i32>, ys: <4 x i64>): <4 x i32> = add(xs, ys) in 0"
  either putStrLn putStrLn . compile
    $ "rec f(xs: <4 x i32>, ys: <5 x i32>): <4 x i32> = add(xs, ys) in 0"
  either putStrLn putStrLn . compile $ "rec f(xs: [2 x i32]): [2 x i32] = [0, 1] in 0"
  either putStrLn putStrLn . compile
    $ "rec f(p: *{i32, [5 x <4 x i32>]}, i: i32): *i32 = &p[0].1[i]<i> in 0"
  either putStrLn putStrLn . compile
    $ "rec f(p: *{i32, [5 x <4 x *i32>]}, i: i32): **i32 = &p[0].1[i]<i>[2] in 0"
  either putStrLn putStrLn . compile
    $ "rec f(p: *{i32, [5 x <4 x *i32>]}, i: i32): **i32 = &p[0].1[i]<i> in 0"
  either putStrLn putStrLn . compile
    $ "rec f(a: [5 x [2 x i64]], i: i32): i64 = a[0][1] in 0"
  either putStrLn putStrLn . compile $ "rec f(v: <10 x i16>, i: i32): i16 = add(v, v)<i> in 0"
  either putStrLn putStrLn . compile
    $ "rec f(a: [4 x {i32, [2 x [3 x i32]]}]): i32 = add(a[1].0, a[2].1[1][0]) in 0"
  either putStrLn putStrLn . compile
    $ "rec f(a: [4 x {i32, [2 x [3 x i32]]}]): i32 = add(a[1].0, a[2].1[1][3]) in 0"
  either putStrLn putStrLn . compile
    $ "rec f(p: **i32): i32 = (p[0])[0] in 0"
  either putStrLn putStrLn . compile
    $ "rec f(p: *i32): i32 = p[0] <- 1; 0 in 0"
  either putStrLn putStrLn . compile $ unlines
    [ "rec f(a: *[4 x {i32, [2 x [3 x i32]]}]): i32 ="
    , "  a[0][3].0 <- add(a[0][1].0, a[0][2].1[1][2]);"
    , "  0"
    , "in 0"
    ]
  either putStrLn putStrLn . compile $ "rec f(x: [2 x i32]): [2 x i32] = x with {[0] = 1, [1] = 2} in 0"
  either putStrLn putStrLn . compile $ unlines
    [ "rec f(x: [2 x {i32, i32}]): {i32, i32} ="
    , "  x[0] with {.1 = add(x[1].0, x[1].1)}"
    , "in 0"
    ]
  either putStrLn putStrLn . compile $ unlines
    [ "rec f(x: [2 x {i32, i32}]): [2 x {i32, i32}] ="
    , "  x with {"
    , "    [0] = x[1] with {.1 = add(x[1].0, x[1].1)},"
    , "    [1] = x[0]"
    , "  }"
    , "in 0"
    ]
  either putStrLn putStrLn . compile $ unlines
    [ "extern foo : fun (i32) -> *i8"
    , "extern bar : fun (*i8) -> i32"
    , "bar(foo(0))"
    ]
  either putStrLn putStrLn . compile $ unlines
    [ "let xs: *{i32, *i32} = ref({3, ref(4)})"
    , "in (xs[0].1)[0]"
    ]
  either putStrLn putStrLn . compile $ unlines
    [ "rec f(xs: *{i32, [2 x i32]}): i32 ="
    , "  xs[0].1 <- [3, 4];"
    , "  0"
    , "in f(ref({2, [5, 6]}))"
    ]
  either putStrLn putStrLn . compile $ unlines
    [ "rec f(xs: *{i32, {[2 x i32], i32}}, i: i32): i32 ="
    , "  xs[0].1.0 <- [3, i];"
    , "  0"
    , "in f(ref({2, {[5, 6], 7}}), 1)"
    ]
  either putStrLn putStrLn . compile $ unlines
    [ "let xs: *{i32, *{i32, *{i32, *{i32, *{i32, *i32}}}}} ="
    , "  ref({3, ref({4, ref({5, ref({6, ref({7, null : *i32})})})})})"
    , "in ((((xs[0].1)[0].1)[0].1)[0].1)[0].0"
    ]
  either putStrLn putStrLn . compile
    $ "rec f(v: <4 x i8>): <4 x i8> = shufflevector(v, v, <3, 2, 1, 0>) in 0"
  either putStrLn putStrLn . compile $ unlines
    [ "rec u(v: <54 x i32>): <54 x i32> = shufflevector(v, v, <"
    , "    6,  3,  0,  7,  4,  1,  8,  5,  2,"
    , "    18, 19, 20, 12, 13, 14, 15, 16, 17,"
    , "    27, 28, 29, 21, 22, 23, 24, 25, 26,"
    , "    36, 37, 38, 30, 31, 32, 33, 34, 35,"
    , "    9, 10, 11, 39, 40, 41, 42, 43, 44,"
    , "    45, 46, 47, 48, 49, 50, 51, 52, 53"
    , "  >)"
    , "and x(v: <54 x i32>): <54 x i32> = shufflevector(v, v, <"
    , "    18, 19, 20, 21, 22, 23, 24, 25, 26,"
    , "    11, 14, 17, 10, 13, 16,  9, 12, 15,"
    , "    45, 46, 47, 48, 49, 50, 51, 52, 53,"
    , "    33, 30, 27, 34, 31, 28, 35, 32, 29,"
    , "    8,  7,  6,  5,  4,  3,  2,  1,  0,"
    , "    44, 43, 42, 41, 40, 39, 38, 37, 36"
    , "  >)"
    , "and y(v: <54 x i32>): <54 x i32> = shufflevector(v, v, <"
    , "    6,  3,  0,  7,  4,  1,  8,  5,  2,"
    , "    18, 19, 20, 21, 22, 23, 24, 25, 26,"
    , "    27, 28, 29, 30, 31, 32, 33, 34, 35,"
    , "    36, 37, 38, 39, 40, 41, 42, 43, 44,"
    , "    9, 10, 11, 12, 13, 14, 15, 16, 17,"
    , "    47, 50, 53, 46, 49, 52, 45, 48, 51"
    , "  >)"
    , "and pu(p: *<54 x i32>): *<54 x i32> ="
    , "  let v: <54 x i32> = p[0] in"
    , "  p[0] <- shufflevector(v, v, <"
    , "    6,  3,  0,  7,  4,  1,  8,  5,  2,"
    , "    18, 19, 20, 12, 13, 14, 15, 16, 17,"
    , "    27, 28, 29, 21, 22, 23, 24, 25, 26,"
    , "    36, 37, 38, 30, 31, 32, 33, 34, 35,"
    , "    9, 10, 11, 39, 40, 41, 42, 43, 44,"
    , "    45, 46, 47, 48, 49, 50, 51, 52, 53"
    , "  >);"
    , "  p"
    , "and id(p: *<54 x i32>): *<54 x i32> = pu(pu(pu(pu(p))))"
    , "in 0"
    ]
  either putStrLn putStrLn . compile $ unlines
    [ "extern puts : fun (*i8) -> void"
    , "let _: void = puts("
    , "  ref([104i8, 101i8, 108i8, 108i8, 111i8, 32i8, 119i8, 111i8, 114i8, 108i8, 100i8, 0i8]) as *i8)"
    , "in 0"
    ]
  either putStrLn putStrLn . compile $ "rec f(x: i32): {i32, i32} = {x, x} in 0"
  either putStrLn putStrLn . compile $ unlines
    [ "type Z32 = i32"
    , "type pi32 = {Z32, i32}"
    , "rec f(x: Z32): pi32 = {x, x} in 0"
    ]
  either putStrLn putStrLn . compile $ unlines
    [ "type Z32 = i32"
    , "struct point{Z32, i32}"
    , "rec f(x: Z32): point = point{x, x} in 0"
    ]
  either putStrLn putStrLn . compile $ unlines
    [ "extern puts : fun (*i8) -> void"
    , "let _: void = puts(\"hello world\")"
    , "in 0"
    ]
  either putStrLn putStrLn . compile $ unlines
    [ "struct cons{i32, *cons}"
    , "type list = *cons"
    , "rec f(xs: list): i32 ="
    , "  case ieq(xs, null) {"
    , "    1 => 0,"
    , "    _ => add(xs[0].0, f(xs[0].1))"
    , "  }"
    , "in f(ref(cons{1, ref(cons{2, ref(cons{3, null : *cons})})}))"
    ]

main = getArgs >>= \case
  ["test"] -> tests
  [phiIn] -> either putStrLn putStrLn =<< compileFile phiIn
  _ -> do
    putStrLn "Usage:"
    putStrLn "  phi test (run some tests)"
    putStrLn "  phi in.φ (compile in.φ to LLVM IR)"