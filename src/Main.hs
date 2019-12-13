import Core
import Data.Functor
import Control.Applicative

print' :: (Functor f, Show (f ())) => f a -> IO ()
print' x = print (x $> ())

testTC :: String -> IO ()
testTC s = either putStrLn print' $ (runTC . infer) =<< (ub <$> parse s)

toANF' :: String -> Either String (ANF TyAnn)
toANF' s = fmap (toANF . snd) . runTC . infer =<< (ub <$> parse s)

testANF :: String -> IO ()
testANF s = either putStrLn print' (toANF' s)

liftA4 :: Applicative f => (a -> b -> c -> d -> e) -> f a -> f b -> f c -> f d -> f e
liftA4 f a b c d = f <$> a <*> b <*> c <*> d

main = do
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
  let fvars = sortedVars <$> tri''
  either putStrLn print graph
  either putStrLn print fvars
  either putStrLn putStrLn $ compile tri
  let bvs = bvsOf <$> tri''
  let l = liftA4 liveness bvs graph fvars tri''
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
  let fvars = sortedVars <$> mult'
  either putStrLn print graph
  either putStrLn print fvars
  let bvs = bvsOf <$> mult'
  let l = liftA4 liveness bvs graph fvars mult'
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
  let fvars = sortedVars <$> multBad'
  let bvs = bvsOf <$> multBad'
  let l = liftA4 liveness bvs graph fvars multBad'
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
    , "    0 => add(x, 1i32),"
    , "    1 => add(x, 0i32),"
    , "    _ => odd(sub(n, 1i32))"
    , "  }"
    , "and odd(n: i32): i32 ="
    , "  case n {"
    , "    0 => 0i32,"
    , "    1 => 1i32,"
    , "    _ => even(sub(n, 1i32))"
    , "  }"
    , "in"
    , "even(4i32)"
    ]
