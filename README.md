# IVM

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
