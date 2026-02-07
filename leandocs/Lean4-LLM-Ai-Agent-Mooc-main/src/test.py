from lean_runner import execute_lean_code

def test_basic_lean_code():
    # Simple Lean 4 example
    lean_code = """
    import Mathlib
    import Aesop

    -- Implementation
    def ident (x : Nat) : Nat :=
    x

    def ident_spec (x : Nat) (result: Nat) : Prop :=
    result = x

    -- Proof
    theorem ident_spec_satisfied (x : Nat) :
    ident_spec x (ident x) := by
    unfold ident ident_spec
    rfl

    """
    
    result = execute_lean_code(lean_code)
    print("Execution result:", result)
    
    # You can add assertions to check the expected output
    # assert "8" in result, f"Expected '8' in result, but got: {result}"
    
if __name__ == "__main__":
    test_basic_lean_code()
