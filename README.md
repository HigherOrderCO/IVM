# IVM

Interaction net virtual machine

## Rust Docs
https://higherorderco.github.io/IVM-doc/doc/ivm/index.html

## Understanding the code base
- Take a look at the [sum example](examples/sum.ivm) (or at the [tests](src/tests.rs)) to get a feeling for the syntax:
    - A `Connection` is written like `a ~ b`. The two ends of a `Connection` are `Connector`s, which can be either a port or an agent
    - Agents are written like `A(a, b)`, where the auxiliary ports are written inside the parentheses, and the principal port is represented by the agent itself
        - E.g. `r ~ A(a, a)` means that `r` is connected to A's principal port, and A's auxiliary ports are connected to each other
        - Connections are transitive, so `r ~ A(a, b), a ~ b` would mean the same
    - The syntax allows nested agents in the RHS of rules, e.g. `n ~ Succ(Zero)` as a shorthand for `n ~ Succ(z), z ~ Zero` (also for the read back, the net's connections are transformed into nested form for improved readability)
        - E.g. `r ~ A(a, B(C(b, c), D(d, e)))` gets internally flattened into `r ~ A(a, _0), _0 ~ B(_1, _2), _1 ~ C(b, c), _2 ~ D(d, e)` during parsing
    - The LHS of a rule must be an active pair of agents and cannot contain context beyond that:
        - E.g. `X(a, b) ~ Y(c, d)` is an active pair
        - No nested agents (e.g. `A(B(a, b), c) ~ B`) because reductions only work on the context of active pairs
        - For the agents in the active pair of a rule LHS, auxiliary ports cannot be specified to be connected:
            - neither within one agent of the active pair (e.g. `A(a, a) ~ B` is not allowed)
            - nor between the two agents of the active pair (e.g. `X(a, b) ~ Y(a, d)` is not allowed)
- Look at [`src/parser/ast.rs`](src/parser/ast.rs) to see how the AST is structured, how it gets validated and turned into an `INetProgram` via `ValidatedAst::into_inet_program`
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

## Further ideas
- Add type system for agents (e.g. `Zero` and `Succ(p)` are `Nat` constructors) and ports, distinguish input/output ports (constructors/destructors) and port partitions as suggested by Lafont
- Polymorphic rules, e.g. `rule[b: Nat] Eq(ret, a) ~ b = IsZero(ret) ~ d, AbsDiff(d, a) ~ b` is equivalent to spelling out the rule for each constructor of `Nat`:
    - `rule Eq(ret, a) ~ Zero = IsZero(ret) ~ d, AbsDiff(d, a) ~ Zero`
    - `rule Eq(ret, a) ~ Succ(b) = IsZero(ret) ~ d, AbsDiff(d, a) ~ Succ(b)`
- Syntactic sugar for return: `ret <- A(a, b)` as shorthand for `A(ret, a) ~ b`. This is useful for example for the sum example, in rules where the result is returned via a port:
    - E.g. for `Add`:
        - Currently: `rule Add(ret, a) ~ Succ(b) = ret ~ Succ(cnt), Add(cnt, a) ~ b`
        - With sugar: `rule Add(ret, a) ~ Succ(b) = ret ~ Succ(cnt), cnt <- Add(a, b)`
    - E.g. for `Mul`:
        - Currently: `rule Mul(ret, a) ~ Succ(b) = Dup(a2, a3) ~ a, Add(ret, a2) ~ cnt, Mul(cnt, a3) ~ b`
        - With sugar: `rule Mul(ret, a) ~ Succ(b) = Dup(a2, a3) ~ a, ret <- Add(a2, cnt), cnt <- Mul(a3, b)`
- Syntactic sugar for implicit wires, for FP-like nesting: `X(_ <- A(a, b))` as a shorthand for `X(cnt), cnt <- A(a, b))`. Then:
    - The `Add` rule becomes: `rule Add(ret, a) ~ Succ(b) = ret ~ Succ(_ <- Add(a, b))`, which is closer to FP syntax (`Succ(Add(a, b))`)
    - The `Mul` rule becomes: `rule Mul(ret, a) ~ Succ(b) = Dup(a2, a3) ~ a, ret <- Add(a2, _ <- Mul(a3, b))`, which is closer to FP syntax (`Add(a2, Mul(a3, b))`)
- Built-in DUP/SUP/ERA nodes & rules and brackets for lambda calculus

## Possible Optimizations
- Readback without storing agent names in nodes, map `agent_id` to `agent_name` for readback
- Using `smallvec` for `Node` ports to reduce heap allocations
- Eliminate memory allocations during rewrites
    - Optimize rule book by using agent/port ids instead of names in `RuleRhs::connections`
    - `RuleBook::apply`: Don't do port lookup by name, and don't allocate a HashMap every time
    - `INet::rewrite`: Reuse memory for `new_active_pairs`, `intermediary_nodes` etc.
- When determining newly created active pairs after a rewrite, don't look at all nodes created by rewritten sub-net for determining new active pairs:
    - Pre-reduce RHS of rules so that sub-net created by rewrite cannot contain active pairs in its interior, there can be only new active pairs on its boundary links to neighbor nodes
        - Only look at agents adjacent to rewritten sub-net for determining new active pairs
    - Or statically determine which created nodes inside rewritten sub-net form active pairs, and store this info in `RuleRhs` so that not all interior nodes have to be scanned
    - Statically determine which external links of the rewritten sub-net can form new active pairs
- Parallel reduction using rayon
    - Static analysis to determine which reductions benefit from parallelism vs which ones are blocked by previous reductions
- When compiling: Pre-reduce `init` connections at compile-time
