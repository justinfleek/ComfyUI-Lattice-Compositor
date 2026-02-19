-- Simple function
let identity = fun x => x

-- Function application
let result = (fun x => x) 42

-- Nested lambdas
let compose = fun f => fun g => fun x => f (g x)

-- Conditional
let abs = fun n => if n < 0 then -n else n

-- Let binding
let add = fun x =>
  let y = 10
  in x + y

-- Arrays
let numbers = [1, 2, 3]
let result = (fun x => x + 1) numbers.0!
