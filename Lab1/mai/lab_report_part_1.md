# Task 3

SPIN cannot be used to prove starvation freedom because the philosopher problem may occur infinitely. With each philosopher repeatedly acquiring and releasing forks in an infinite sequence of states with an infinite number of possible infinite interleavings, SPIN cannot analyze all possible interleavings as SPIN can only verify properties in finite state spaces.

# Task 4

Risk 1: For the liveliness property to hold, I think my model guarantees that "something useful" happens infinitely often. I define that "something useful" to be that at least one philosopher gets to eat infinitely often. However, the liveliness property may be defined in another way, e.g. "all philosophers gets to eat infinitely often".

Risk 2: With an infinite number of possible state interleavings as N increases, SPIN's exploration of the state space may be limited by resource constraints or time limitations, preventing it from exhaustively verifying all possible behaviors. This risk can result in verification results that do not account for all edge cases and scenarios, potentially missing critical issues in the solution. Thus, this may lead to incomplete verification or verification results that do not cover all possible scenarios.
