// Test 3: Wrong language (JavaScript instead of Haskell/PureScript/Lean4)
// This should be caught - JavaScript is not in the allowed language stack

function badFunction(x) {
  return x + 1;
}

const result = badFunction(42);
console.log(result);
