import Core
import Data.Functor

print' :: (Functor f, Show (f ())) => f a -> IO ()
print' x = print (x $> ())

testTC :: String -> IO ()
testTC s = either putStrLn print' $ (runTC . infer) =<< (ub <$> parse s)

toANF' :: String -> Either String (ANF TyAnn)
toANF' s = fmap (toANF . snd) . runTC . infer =<< (ub <$> parse s)

testANF :: String -> IO ()
testANF s = either putStrLn print' (toANF' s)

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
  let tri'' = annoFV . toTails <$> tri'
  either putStrLn print' tri''
  either putStrLn print (graphOf <$> tri'')
  either putStrLn print (sortedVars <$> tri'')
