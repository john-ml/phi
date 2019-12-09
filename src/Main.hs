import Core

testTC :: String -> IO ()
testTC s = either putStrLn (either putStr print . runTC . infer) (parse s)

main = do
  print "hi"
  either putStrLn print $ parse "3i32"
  either putStrLn print $ parse "let x: i32 = 3i32 in 4i32"
  testTC "let x: i32 = 3i32 in mul(2i32, 3i32)"
  testTC "let x: i32 = 3i32 in mul(2i32, 3i64)"
  either putStrLn print $ parse "rec f(x: i32): i32 = x in f(x)"
  testTC "rec f(x: i32): i32 = x in f(4i32)"
  let tri = unlines
       [ "rec tri(n: i32): i32 ="
       , "  case n {"
       , "    0 => 0i32,"
       , "    _ => add(n, tri(sub(n, 1i32)))"
       , "  }"
       , "in tri(4i32)"
       ]
  either putStrLn print $ parse tri
  testTC tri

