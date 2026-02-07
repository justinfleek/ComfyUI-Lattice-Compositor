# 🤖 Lean 4 Coding Agent

This repository contains an AI-powered agent system that automatically **generates and verifies Lean 4 code**, turning natural language problem statements into formally proven Lean programs. It's part of a project developed during the [LLM Agents Learning MOOC](https://llmagents-learning.org/sp25), focused on reasoning, theorem proving, and agent-based AI systems.

## 🧠 Overview

The Lean Coding Agent combines **multi-agent reasoning** with **code generation and verification**. Given:
- A natural language description (`description.txt`)
- A Lean code template (`task.lean`)

It outputs:
- An implemented function
- A formal proof of correctness

All in valid Lean syntax — ready to compile and check!

---

## ⚙️ Architecture Multi-Agent Collaboration

The workflow involves multiple distinct steps that illustrate the cooperation between the two agents:

### Step 1: Reasoning Agent Analysis
The Reasoning Agent (`o3-mini`) begins by receiving the problem description and the Lean code template. It:
- Breaks down the problem description into smaller components
- Suggests a general approach for solving the problem
- Prepares a structured analysis to guide the next step

### Step 2: LLM Agent Code Generation
The LLM Agent (`gpt-4o`) uses the Reasoning Agent's analysis to:
- Generate the Lean code required to solve the problem
- Produce the corresponding proof that supports the solution
- Insert the solution into the designated template sections

### Step 3: Execution and Verification
The generated code is executed in the Lean environment:
- If successful, the solution is considered complete
- If errors occur, the system collects the error messages

### Step 4: Iterative Refinement
When errors are detected, the system enters a refinement phase where the LLM Agent:
- Reanalyzes the problem and code
- Refines the implementation and proof to ensure correctness

full explanation is on [Lean4 Ai agent Doc](https://docs.google.com/document/d/1ScwWHvijSFzrAmYUOXGP3KVu7iOqBogSp147tebiYoc/edit?usp=sharing)

---

## 🧪 Main Workflow

Implemented in `src/main.py`, the key function is:

```python
def main_workflow(problem_description: str, task_lean_code: str = "") -> LeanCode:
    """
    Takes a problem description and a Lean template, and returns completed code and proof.

    """
```

The output is a `LeanCode` dictionary:
```python
{
  "code": "<function implementation>",
  "proof": "<formal proof>"
}
```

To run the agent and setup code you should follow the guidelines in `INSTRUCTIONS.md` for task setup and Lean 4 implementation.

Run the automated test suite to verify the agent against all test tasks:

```bash
make test
```

This command executes the agent on predefined problems and verifies that the generated code passes Lean's verification.




## 📦 Requirements

- Python 3.12+
- [Lean 4](https://leanprover.github.io/)
- OpenAI-compatible LLMs (for GPT-4o access)
- Dependencies in `requirements.txt`

---

## 📚 Related Course

This project was developed as part of the **LLM Agents MOOC** offered by [UC Berkeley](https://www.linkedin.com/school/uc-berkeley/), led by [Professor Dawn Song](https://www.linkedin.com/in/dawn-song-51586033), [Xinyun Chen](https://www.linkedin.com/in/xinyun-chen-b4ab79172/), and [Kaiyu Yang](https://www.linkedin.com/in/kaiyuy/). The course covers:

- Inference-time techniques for reasoning
- LLM post-training methods
- Code generation and verification
- Autoformalization and theorem proving

More details: [llmagents-learning.org/sp25](https://llmagents-learning.org/sp25)

---

## 🤝 Contributing

PRs are welcome! Whether it's bug fixes, improvements, or ideas — feel free to fork and open a Pull Request.
