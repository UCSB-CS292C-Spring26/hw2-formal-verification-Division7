"""
CS292C Homework 2 — Problem 3: Agent Permission Policy Verification (25 points)
=================================================================================
Encode a realistic agent permission policy as SMT formulas and use Z3 to
analyze it for safety properties and privilege escalation vulnerabilities.
"""

from z3 import *

# ============================================================================
# Constants
# ============================================================================

FILE_READ = 0
FILE_WRITE = 1
SHELL_EXEC = 2
NETWORK_FETCH = 3

ADMIN = 0
DEVELOPER = 1
VIEWER = 2

# ============================================================================
# Sorts and Functions
#
# You will use these to build your policy encoding.
# Do NOT modify these declarations.
# ============================================================================

User = DeclareSort('User')
Resource = DeclareSort('Resource')

role         = Function('role', User, IntSort())          # 0=admin, 1=dev, 2=viewer
is_sensitive = Function('is_sensitive', Resource, BoolSort())
in_sandbox   = Function('in_sandbox', Resource, BoolSort())
owner        = Function('owner', Resource, User)

# The core predicate: is this (user, tool, resource) triple allowed?
allowed = Function('allowed', User, IntSort(), Resource, BoolSort())


# ============================================================================
# Part (a): Encode the Policy — 10 pts
#
# Encode rules R1–R5 from the README as Z3 constraints.
#
# You must design the encoding yourself. Consider:
# - Use ForAll to make rules apply to all users/resources.
# - Encode both what IS allowed and what is NOT allowed.
# - Rule R4 overrides R3 — handle this carefully.
#
# Return a list of Z3 constraints.
# ============================================================================

def make_policy():
    """
    Return a list of Z3 constraints encoding rules R1–R5.

    1. How to express "viewers may ONLY do X" (everything else is denied).
    2. How R4 overrides R3 for admins.
    3. Whether you need a closed-world assumption (if not explicitly
       allowed, it's denied).
    """
    u = Const('u', User)
    r = Const('r', Resource)
    t = Int('t')

    #

    constraints = [
        ForAll((u, t, r),
               If(And(is_sensitive(r), t == SHELL_EXEC), Not(allowed(u, t, r)),
                  If(role(u) == ADMIN, allowed(u, t, r),
                     If(And(Not(in_sandbox(r)), t == NETWORK_FETCH), Not(allowed(u, t, r)),
                        If(And(role(u) == DEVELOPER,
                               Or(t == FILE_READ, And(t == FILE_WRITE, Or(owner(r) == u, in_sandbox(r))))),
                           allowed(u, t, r),
                           If(And(role(u) == VIEWER, t == FILE_READ, Not(is_sensitive(r))), allowed(u, t, r),
                              Not(allowed(u, t, r)))))))
               )
    ]

    # Hint: Start with a default-deny rule, then add exceptions.
    # I explicitly decided to allow admins to network_fetch non sandbox resources as the rule doesn't specify it overrides
    # r3 like r4 does.

    return constraints


# ============================================================================
# Part (b): Policy Queries — 8 pts
# ============================================================================

def query(description, policy, extra):
    """Helper: check if extra constraints are SAT under the policy."""
    s = Solver()
    s.add(policy)
    s.add(extra)
    result = s.check()
    print(f"  {description}")
    print(f"  → {result}")
    if result == sat:
        m = s.model()
        print(f"    Model: {m}")
    print()
    return result


def part_b():
    """
    Answer the four queries from the README.
    For query 4, also demonstrate what becomes possible without R4.

    """
    policy = make_policy()
    print("=== Part (b): Policy Queries ===\n")

    u = Const('u', User)
    r = Const('r', Resource)
    t = Int('t')

    # Q1: Can a developer write to a sensitive file they don't own, in the sandbox?
    query("q1", policy, [
        role(u) == DEVELOPER,
        t == FILE_WRITE,
        is_sensitive(r) == True,
        owner(r) != u,
        in_sandbox(r) == True,
        allowed(u, t, r) == True
    ])
    # Answer: yes, explicitly allowed by policy.

    # Q2: Can an admin network_fetch a resource outside the sandbox?
    query(
        "Can an admin network_fetch a resource outside the sandbox?", policy, [
            role(u) == ADMIN,
            t == NETWORK_FETCH,
            in_sandbox(r) == False,
            allowed(u, t, r) == True
        ]
    )
    # Answer, yes, explicitly allowed by policy -- README does not say Overrides R3 like R4 does.

    # Q3: Is there ANY role that can shell_exec on a sensitive resource?
    query(
        "Is there ANY role that can shell_exec on a sensitive resource?", policy, [
            Exists([u], And(t == SHELL_EXEC, is_sensitive(r), allowed(u, t, r)))
        ]
    )

    # Answer: No, explicitly disallowed by policy. This is a specific override for R3.

    # Q4: Remove R4 — what dangerous action becomes possible?
    # [Claude: implemented the missing query; policy_no_r4 is make_policy() with the
    #  shell_exec-on-sensitive guard removed so the If-tree starts with the admin check.]
    policy_no_r4 = [
        ForAll((u, t, r),
               If(role(u) == ADMIN, allowed(u, t, r),
                  If(And(Not(in_sandbox(r)), t == NETWORK_FETCH), Not(allowed(u, t, r)),
                     If(And(role(u) == DEVELOPER,
                            Or(t == FILE_READ, And(t == FILE_WRITE, Or(owner(r) == u, in_sandbox(r))))),
                        allowed(u, t, r),
                        If(And(role(u) == VIEWER, t == FILE_READ, Not(is_sensitive(r))),
                           allowed(u, t, r),
                           Not(allowed(u, t, r)))))))
    ]
    query(
        "Q4 (no R4): Can an admin shell_exec on a sensitive resource?", policy_no_r4, [
            role(u) == ADMIN,
            t == SHELL_EXEC,
            is_sensitive(r) == True,
            allowed(u, t, r) == True,
        ]
    )
    # Answer: yes — without R4, the admin allow-all fires and permits shell_exec on sensitive
    # resources. This is the dangerous action R4 was specifically introduced to prevent.


# ============================================================================
# Part (c): Privilege Escalation — 7 pts
#
# New rule R6: Developers may shell_exec on non-sensitive sandbox resources.
#
# Attack scenario: A developer uses shell_exec on a non-sensitive sandbox
# resource to change ANOTHER resource's sensitivity flag (e.g., modifying
# a config file that controls access). This makes a previously sensitive
# resource become non-sensitive, bypassing R4 on the next step.
#
# Model this as a 2-step trace where a resource's sensitivity changes
# between steps.
# ============================================================================

def part_c():
    """
    TODO:
    1. Add rule R6 to the policy.
    2. Model a 2-step trace:
       - Step 1: developer calls shell_exec on resource r1
         (r1 is non-sensitive and in sandbox — allowed by R6)
         Side-effect: this command changes resource r2 from sensitive to
         non-sensitive (e.g., modifying an access-control config)
       - Step 2: developer calls shell_exec on resource r2
         (r2 is NOW non-sensitive — was it allowed before? is it allowed now?)
    3. The twist: r2's sensitivity changes BETWEEN steps. Encode this by
       using two copies of is_sensitive (before and after).
    4. Check if the developer can effectively access a previously-sensitive resource.
    5. [EXPLAIN] in a comment: Propose and implement a fix.
    """
    print("=== Part (c): Privilege Escalation ===\n")

    u = Const('u', User)
    r = Const('r', Resource)
    r_sensitive = Const('r_sensitive', Resource)
    t = Int('t')

    is_sensitive_before = Function("is_sensitive_before", Resource, BoolSort())
    is_sensitive_after = Function("is_sensitive_after", Resource, BoolSort())

    # initial policy list
    constraints = [
        ForAll((u, t, r),
               If(And(is_sensitive(r), t == SHELL_EXEC), Not(allowed(u, t, r)),
                  If(role(u) == ADMIN, allowed(u, t, r),
                     If(And(Not(in_sandbox(r)), t == NETWORK_FETCH), Not(allowed(u, t, r)),
                        If(And(role(u) == DEVELOPER,
                               Or(t == FILE_READ, And(t == FILE_WRITE, Or(owner(r) == u, in_sandbox(r))),
                                  And(t == SHELL_EXEC, in_sandbox(r), Not(is_sensitive(r))))), allowed(u, t, r),
                           If(And(role(u) == VIEWER, t == FILE_READ, Not(is_sensitive(r))), allowed(u, t, r),
                              Not(allowed(u, t, r)))))))
               )
    ]

    model_step_1 = [
        ForAll((u, t, r),
               If(And(is_sensitive_before(r), t == SHELL_EXEC), Not(allowed(u, t, r)),
                  If(role(u) == ADMIN, allowed(u, t, r),
                     If(And(Not(in_sandbox(r)), t == NETWORK_FETCH), Not(allowed(u, t, r)),
                        If(And(role(u) == DEVELOPER,
                               Or(t == FILE_READ, And(t == FILE_WRITE, Or(owner(r) == u, in_sandbox(r))),
                                  And(t == SHELL_EXEC, in_sandbox(r), Not(is_sensitive_before(r))))), allowed(u, t, r),
                           If(And(role(u) == VIEWER, t == FILE_READ, Not(is_sensitive_before(r))), allowed(u, t, r),
                              Not(allowed(u, t, r)))))))
               )
    ]

    model_step_2 = [
        ForAll((u, t, r_sensitive),
               If(And(is_sensitive_after(r_sensitive), t == SHELL_EXEC), Not(allowed(u, t, r_sensitive)),
                  If(role(u) == ADMIN, allowed(u, t, r_sensitive),
                     If(And(Not(in_sandbox(r_sensitive)), t == NETWORK_FETCH), Not(allowed(u, t, r_sensitive)),
                        If(And(role(u) == DEVELOPER, Or(t == FILE_READ, And(t == FILE_WRITE, Or(owner(r_sensitive) == u,
                                                                                                in_sandbox(
                                                                                                    r_sensitive))),
                                                        And(t == SHELL_EXEC, in_sandbox(r_sensitive),
                                                            Not(is_sensitive_after(r_sensitive))))),
                           allowed(u, t, r_sensitive),
                           If(And(role(u) == VIEWER, t == FILE_READ, Not(is_sensitive_after(r_sensitive))),
                              allowed(u, t, r_sensitive), Not(allowed(u, t, r_sensitive)))))))
               )
    ]
    # Hint: Use is_sensitive_before and is_sensitive_after as two separate
    # functions, or use a time-indexed model.

    completed_model = Solver()
    completed_model.add(model_step_1)
    completed_model.add(model_step_2)
    completed_model.add(
        [
            role(u) == DEVELOPER,
            t == SHELL_EXEC,
            is_sensitive_before(r) == False,
            in_sandbox(r) == True,
            is_sensitive_after(r_sensitive) == False,
            allowed(u, t, r) == True,
            allowed(u, t, r_sensitive) == True
        ]
    )

    print(completed_model.check())
    print(completed_model.model())

    # [EXPLAIN] My solution is to introduce a function that inspects SHELL_EXEC commands before running them.
    # It is called modifies_sensitive_files(), and when a tool call and resource are submitted, returns true if the tool call
    # attempts to modify files that are sensitive with SHELL_EXEC.
    # We add to the shell_exec rule to deny these calls.

    modifies_sensitive_files = Function("modifies_sensitive_files", IntSort(), Resource, BoolSort())

    model_step_1 = [
        ForAll((u, t, r),
               If(And(Or(is_sensitive_before(r), modifies_sensitive_files(t,r)), t == SHELL_EXEC), Not(allowed(u, t, r)),
                  If(role(u) == ADMIN, allowed(u, t, r),
                     If(And(Not(in_sandbox(r)), t == NETWORK_FETCH), Not(allowed(u, t, r)),
                        If(And(role(u) == DEVELOPER,
                               Or(t == FILE_READ, And(t == FILE_WRITE, Or(owner(r) == u, in_sandbox(r))),
                                  And(t == SHELL_EXEC, in_sandbox(r), Not(is_sensitive_before(r))))), allowed(u, t, r),
                           If(And(role(u) == VIEWER, t == FILE_READ, Not(is_sensitive_before(r))), allowed(u, t, r),
                              Not(allowed(u, t, r)))))))
               )
    ]

    model_step_2 = [
        ForAll((u, t, r_sensitive),
               If(And(Or(is_sensitive_after(r_sensitive), modifies_sensitive_files(t,r_sensitive)), t == SHELL_EXEC),
                  Not(allowed(u, t, r_sensitive)),
                  If(role(u) == ADMIN, allowed(u, t, r_sensitive),
                     If(And(Not(in_sandbox(r_sensitive)), t == NETWORK_FETCH), Not(allowed(u, t, r_sensitive)),
                        If(And(role(u) == DEVELOPER, Or(t == FILE_READ, And(t == FILE_WRITE, Or(owner(r_sensitive) == u,
                                                                                                in_sandbox(
                                                                                                    r_sensitive))),
                                                        And(t == SHELL_EXEC, in_sandbox(r_sensitive),
                                                            Not(is_sensitive_after(r_sensitive))))),
                           allowed(u, t, r_sensitive),
                           If(And(role(u) == VIEWER, t == FILE_READ, Not(is_sensitive_after(r_sensitive))),
                              allowed(u, t, r_sensitive), Not(allowed(u, t, r_sensitive)))))))
               )
    ]

    completed_model = Solver()
    completed_model.add(model_step_1)
    completed_model.add(model_step_2)
    # I leave is_sensitive_after as false for effect
    completed_model.add(
        [
            role(u) == DEVELOPER,
            t == SHELL_EXEC,
            is_sensitive_before(r) == False,
            in_sandbox(r) == True,
            is_sensitive_after(r_sensitive) == False,
            modifies_sensitive_files(t, r) == True,
            modifies_sensitive_files(t, r_sensitive) == False,
            allowed(u, t, r) == True,
            allowed(u, t, r_sensitive) == True
        ]
    )

    result = completed_model.check()
    print(result)
    if result == unsat:  # Claude: made conditional — README says "print on success"
        print("ESCALATION BLOCKED")


# ============================================================================
if __name__ == "__main__":
    part_b()
    part_c()
