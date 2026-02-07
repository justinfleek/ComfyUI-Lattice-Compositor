import os
import argparse
from src.agents import Reasoning_Agent, LLM_Agent
from src.lean_runner import execute_lean_code
from typing import Dict, List, Tuple

type LeanCode = Dict[str, str]

def main_workflow(problem_description: str, task_lean_code: str = "") -> LeanCode:
    """
    Main workflow for the coding agent. This workflow takes in the problem description in natural language (description.txt) 
    and the corresponding Lean code template (task.lean). It returns the function implementation and the proof in Lean.
    
    Args:
        problem_description: Problem description in natural language. This file is read from "description.txt"
        task_lean_code: Lean code template. This file is read from "task.lean"
    
    Returns:
        LeanCode: Final generated solution, which is a dictionary with two keys: "code" and "proof".
    """
    # Initialize our agents
    reasoning_agent = Reasoning_Agent(model="o3-mini")
    llm_agent = LLM_Agent(model="gpt-4o")
    
    # Step 1: Let the reasoning agent analyze the problem
    reasoning_prompt = f"""
    you are a reasoning agent .Analyze this Lean4 programming problem and suggest an simple approach . think about it:

    Problem description:
    {problem_description}

    Lean code template:
    {task_lean_code}

    Your analysis should help develop code and proof to put in these specific sections:
    
    -- << CODE START >>
    {{code}}
    -- << CODE END >>
    
    -- << PROOF START >>
    {{proof}}
    -- << PROOF END >>
    """
    reasoning_analysis = reasoning_agent.get_response([{"role": "user", "content": reasoning_prompt}])
    
    # Step 2: Generate initial implementation and proof
    implementation_prompt = f"""
    you work as an agent .Based on the following problem and analysis, provide the Lean4 codes to do the task:
    
    'Lean code template' has a format code like this:
    def some_function (args) : ReturnType :=
    -- << CODE START >>
    maybe some code here
    {{code}}
    -- << CODE END >>

    somecode...
    
    theorem some_theorem (args) : ProofType :=
    -- << PROOF START >>
    some proof here
    {{proof}}
    -- << PROOF END >>

    and your task is to choose the right code for the {{code}} and {{proof}} parts. and at the end
    you should give me just the right code taht I can put in the {{code}} and {{proof}} parts noting less or more like this:
    
    the code you choose to put in the {{code}} and {{proof}} parts , you would give me like this:
    
    CODEPART:

    PROOFPART:

    (do not put any additional text )
    Lean code template:
    {task_lean_code}

    Analysis:
    {reasoning_analysis}
    
    Problem description:
    {problem_description}

    """
    
    initial_solution = llm_agent.get_response([{"role": "user", "content": implementation_prompt}])
    print("\n-- initial_solution --\n")
    print(initial_solution)
    print("\n---\n")

    # Extract code and proof based on the expected format:
    # CODEPART:
    # PROOFPART:
    
    code_part = ""
    proof_part = ""
    
    if "CODEPART:" in initial_solution and "PROOFPART:" in initial_solution:
        parts = initial_solution.split("CODEPART:")
        if len(parts) > 1:
            code_proof_parts = parts[1].split("PROOFPART:")
            if len(code_proof_parts) > 1:
                code_part = code_proof_parts[0].strip()
                proof_part = code_proof_parts[1].strip()
    
    # Function to properly clean code blocks
    def clean_code_block(text):
        if text.startswith("```lean"):
            text = text[len("```lean"):].strip()
        elif text.startswith("```"):
            text = text[len("```"):].strip()
        
        if text.endswith("```"):
            text = text[:-3].strip()
            
        text = text.replace("`", "")
        text = text.replace("·", "")
        text = text.replace("#", "")
        # text = text.replace("*", "")
        return text.strip()
    
    generated_function_implementation = clean_code_block(code_part)
    generated_proof = clean_code_block(proof_part)
    
    print("\n--- DEBUG: Extracted Function Implementation ---")
    print(f"Length: {len(generated_function_implementation)} chars")
    print(generated_function_implementation)
    
    print("\n--- DEBUG: Extracted Proof ---")
    print(f"Length: {len(generated_proof)} chars")
    print(generated_proof)
    

    # Now insert the code and proof into the template
    modified_task_code = task_lean_code.replace("{{code}}", generated_function_implementation).replace("{{proof}}", generated_proof)
    
    print("\n--- DEBUG: Complete Modified Lean Code ---")
    print(modified_task_code)
    print("\n" + "-"*50)

    # Step 3: Verify with Lean execution
    execution_result = execute_lean_code(modified_task_code)
    print("Execution result:", execution_result)
    print("\n\n\n\n")
    
    # Step 4: If execution failed, refine the solution
    if "error" in execution_result.lower():
        error_correction_prompt = f"""
        The Lean code execution failed with the following error:
        {execution_result}
        
        Please fix the implementation based on this error.
        
        Problem description:
        {problem_description}
        
        Lean code template:
        {task_lean_code}
        
        Your previous implementation:
        -- Function implementation --
        {generated_function_implementation}
        
        -- Proof implementation --
        {generated_proof}
        
        Provide corrected code in the same format as before:
        
        CODEPART:
        
        PROOFPART:
        
        (Remember to only provide the code and proof in the format above, without any additional text or explanation.)
        """
        
        correction_history = [
            {"role": "user", "content": implementation_prompt},
            {"role": "assistant", "content": initial_solution},
            {"role": "user", "content": error_correction_prompt}
        ]
        
        corrected_solution = llm_agent.get_response(correction_history)
        print("\n-- Corrected Solution --\n")
        print(corrected_solution)
        
        # Extract corrected code and proof
        if "CODEPART:" in corrected_solution and "PROOFPART:" in corrected_solution:
            parts = corrected_solution.split("CODEPART:")
            if len(parts) > 1:
                code_proof_parts = parts[1].split("PROOFPART:")
                if len(code_proof_parts) > 1:
                    code_part = code_proof_parts[0].strip()
                    proof_part = code_proof_parts[1].strip()
                    
                    code_part = clean_code_block(code_part)
                    proof_part = clean_code_block(proof_part)
                    
                    generated_function_implementation = code_part.strip()
                    generated_proof = proof_part.strip()
                    
                    # Try the corrected solution
                    modified_task_code = task_lean_code.replace("{{code}}", generated_function_implementation).replace("{{proof}}", generated_proof)
                    execution_result = execute_lean_code(modified_task_code)
                    print("Corrected execution result:", execution_result)
    
    
    return {
        "code": generated_function_implementation,
        "proof": generated_proof
    }


def get_problem_and_code_from_taskpath(task_path: str) -> Tuple[str, str]:
    """
    Reads a directory in the format of task_id_*. It will read the file "task.lean" and also read the file 
    that contains the task description, which is "description.txt".
    
    After reading the files, it will return a tuple of the problem description and the Lean code template.
    
    Args:
        task_path: Path to the task file
    """
    problem_description = ""
    lean_code_template = ""
    
    with open(os.path.join(task_path, "description.txt"), "r") as f:
        problem_description = f.read()

    with open(os.path.join(task_path, "task.lean"), "r") as f:
        lean_code_template = f.read()

    return problem_description, lean_code_template

def get_unit_tests_from_taskpath(task_path: str) -> List[str]:
    """
    Reads a directory in the format of task_id_*. It will read the file "tests.lean" and return the unit tests.
    """
    with open(os.path.join(task_path, "tests.lean"), "r") as f:
        unit_tests = f.read()
    
    return unit_tests

def get_task_lean_template_from_taskpath(task_path: str) -> str:
    """
    Reads a directory in the format of task_id_*. It will read the file "task.lean" and return the Lean code template.
    """
    with open(os.path.join(task_path, "task.lean"), "r") as f:
        task_lean_template = f.read()
    return task_lean_template