rec fib(n: i32): i131072 =
  let x: i131072 = add(0i131072, 0i131072) in
  rec go(n: i32, a: i131072, b: i131072): i131072 =
    case n {
      0 => a,
      _ => go(sub(n, 1i32), add(x, b), add(a, b))
    }
  in go(n, 0i131072, 1i131072)
in
let res: i131072 = fib(2000i32) in
0i32
