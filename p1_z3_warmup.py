"""
CS292C Homework 2 — Problem 1: Z3 Warm-Up + EUF Puzzle (15 points)
===================================================================
Complete each function below. Run this file to check your answers.
"""

from z3 import *


# ---------------------------------------------------------------------------
# Part (a) — 3 pts
# Find integers x, y, z such that x + 2y = z, z > 10, x > 0, y > 0.
# ---------------------------------------------------------------------------
def part_a():
    x, y, z = Ints('x y z')
    s = Solver()

    s.add(x + 2 * y == z)
    s.add(z > 10)
    s.add(x > 0)
    s.add(y > 0)

    print("=== Part (a) ===")
    if s.check() == sat:
        m = s.model()
        print(f"SAT: x={m[x]}, y={m[y]}, z={m[z]}")
    else:
        print("UNSAT (unexpected!)")
    print()


# ---------------------------------------------------------------------------
# Part (b) — 3 pts
# Prove validity of: ∀x. x > 5 → x > 3
# Hint: A formula F is valid iff ¬F is unsatisfiable.
# ---------------------------------------------------------------------------
def part_b():
    x = Int('x')
    s = Solver()

    s.add(And(x > 5, x <=3))

    print("=== Part (b) ===")
    result = s.check()
    if result == unsat:
        print("Valid! (negation is UNSAT)")
    else:
        print(f"Not valid — counterexample: {s.model()}")
    print()


# ---------------------------------------------------------------------------
# Part (c) — 5 pts: The EUF Puzzle
#
# Formula:  f(f(x)) = x  ∧  f(f(f(x))) = x  ∧  f(x) ≠ x
#
# STEP 1: Check satisfiability with Z3. (2 pts)
#
# STEP 2: Use Z3 to derive WHY the result holds. (3 pts)
#   Write a series of Z3 validity checks that demonstrate the key reasoning
#   steps. For example, from f(f(x)) = x, what can you derive about f(f(f(x)))?
#   Each check should print what it's testing and whether it holds.
#   Hint: Apply f to both sides of the first equation.
# ---------------------------------------------------------------------------
def part_c():
    S = DeclareSort('S')
    x = Const('x', S)
    f = Function('f', S, S)
    s = Solver()

    # Claude caught I had f(f(f(f(x)))) here rather than 3 of them
    s.add(And(f(f(x)) == x, f(f(f(x))) == x, f(x) != x))

    print("=== Part (c) ===")
    result = s.check()
    if result == sat:
        print(f"SAT: {s.model()}")
    else:
        print("UNSAT")
        # Step 2: derive why — validity checks for each reasoning step.
        # (Validity check pattern: negate conclusion under premise; UNSAT means valid.)
        # [Claude rewrote these checks; originals were standalone SAT queries with no premises]

        # Step A: from f(f(x))=x, applying f to both sides gives f(f(f(x)))=f(x).
        s2 = Solver()
        s2.add(f(f(x)) == x)        # premise
        s2.add(f(f(f(x))) != f(x))  # negated conclusion
        print(f"  f(f(x))=x  →  f(f(f(x)))=f(x):  {'Valid' if s2.check() == unsat else 'Invalid'}")

        # Step B: combining f(f(f(x)))=f(x) with f(f(f(x)))=x forces f(x)=x.
        s3 = Solver()
        s3.add(f(f(f(x))) == f(x))  # from step A
        s3.add(f(f(f(x))) == x)     # second original equation
        s3.add(f(x) != x)           # negated conclusion
        print(f"  f(f(f(x)))=f(x) ∧ f(f(f(x)))=x  →  f(x)=x:  {'Valid' if s3.check() == unsat else 'Invalid'}")

        print("  f(x)=x contradicts f(x)≠x, so the conjunction is UNSAT.")
    print()


# ---------------------------------------------------------------------------
# Part (d) — 4 pts: Array Axioms
#
# Prove BOTH axioms (two separate solver checks):
#   (1) Read-over-write HIT:   i = j  →  Select(Store(a, i, v), j) = v
#   (2) Read-over-write MISS:  i ≠ j  →  Select(Store(a, i, v), j) = Select(a, j)
#
# [EXPLAIN] in a comment below: Why are these two axioms together sufficient
# to fully characterize Store/Select behavior? (2–3 sentences)
# ---------------------------------------------------------------------------
# These two axioms are toghether sufficient to fully characterize Store/Select behavior because
# they are valid for the full range of possible actions on an array. The first axiom asserts that for
# any value of i that the value is actually stored (as i = j), and as such ensures that the array stores
# as it is supposed to. The second axiom asserts that storing a value at an index leaves the rest of the 
# indexes unchanged. As a result, we can say this characterizes the entire range of behavior.
def part_d():
    a = Array('a', IntSort(), IntSort())
    i, j, v = Ints('i j v')

    print("=== Part (d) ===")

    # Axiom 1: Read-over-write HIT
    s1 = Solver()
    s1.add(And(i == j, Select(Store(a,i,v),j) != v))
    r1 = s1.check()
    print(f"Axiom 1 (hit):  {'Valid' if r1 == unsat else 'INVALID'}")

    # Axiom 2: Read-over-write MISS
    s2 = Solver()
    s2.add(And(i != j, Select(Store(a,i,v), j) != Select(a,j)))
    r2 = s2.check()
    print(f"Axiom 2 (miss): {'Valid' if r2 == unsat else 'INVALID'}")
    print()


# ---------------------------------------------------------------------------
if __name__ == "__main__":
    part_a()
    part_b()
    part_c()
    part_d()
