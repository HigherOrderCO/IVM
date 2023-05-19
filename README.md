# IVM

## Understanding the code base
- Take a look at the [sum example](examples/sum.ivm) (or at the [tests](src/tests.rs)) to get a feeling for the syntax:
    - A `Connection` is written like `a ~ b`, where `a` and `b` are called `Connector`, which can be either a port or an agent
    - Agents are written like `A(a, b)`, where the auxiliary ports are written inside the parentheses, and the principal port is represented by the agent itself
        - E.g. `r ~ A(a, a)` means that `r` is connected to A's principal port, and A's auxiliary ports are connected to each other
        - Connections are transitive, so `r ~ A(a, b), a ~ b` would mean the same
    - The syntax allows nested agents in the RHS of rules, e.g. `n ~ Succ(Zero)` as a shorthand for `n ~ Succ(z), z ~ Zero` (also for the read back, the net's connections are transformed into nested form for improved readability)
        - E.g. `r ~ X(Y(a, b), Z(c, d))` is a shorthand for `r ~ X(y, z), y ~ Y(a, b), z ~ Z(c, d)`
    - The LHS of a rule must be an active pair of agents and cannot contain context beyond that:
        - E.g. `X(a, b) ~ Y(c, d)` is an active pair
        - No nested agents (e.g. `A(B(a, b), c) ~ B`) because reductions only work on the context of active pairs
        - For the agents in the active pair of a rule LHS, auxiliary ports cannot be specified to be connected:
            - neither within one agent of the active pair (e.g. `A(a, a) ~ B` is not allowed)
            - nor between the two agents of the active pair (e.g. `X(a, b) ~ Y(a, d)` is not allowed)
- Then look at [`src/parser/ast.rs`](src/parser/ast.rs) to see how the AST is structured, how it gets validated and turned into an `INetProgram` via `ValidatedAst::into_inet_program`
- Look at [`src/rule_book.rs`](src/rule_book.rs) to see how the rule book works
- Look at [`src/inet.rs`](src/inet.rs) to see how the interaction net is implemented

## Running the examples
```sh
cargo run -- examples/sum.ivm
```

## Running the tests
```sh
cargo test
```

---

## Possible Optimizations
- Optimize rule book by using agent/port ids instead of names
- Readback without storing agent names in nodes
- Eliminate memory allocations during reductions
- Only scan all active pairs in the beginning, check nodes created by rewritten sub-net for new active pairs
    - Even better: Don't look at all nodes created by rewritten sub-net for determining new active pairs:
        - Pre-reduce RHS of rules so that sub-net created by rewrite cannot contain active pairs in its interior, there can be only new active pairs on its boundary links to neighbor nodes
            - Only look at agents adjacent to rewritten sub-net for determining new active pairs
        - Or statically determine which created nodes inside rewritten sub-net contain active pairs, and store this info in `RuleRhs` so that not all interior nodes have to be scanned
- Parallel reduction using rayon
- When compiling: Pre-reduce `init` connections at compile-time
