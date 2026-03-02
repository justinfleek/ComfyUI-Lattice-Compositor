# Test 8: Python file (wrong language)
# Should this be blocked entirely?

def bad_function():
    return None  # Python uses None, not null

if __name__ == "__main__":
    print("This is Python, not Haskell/PureScript/Lean4")
