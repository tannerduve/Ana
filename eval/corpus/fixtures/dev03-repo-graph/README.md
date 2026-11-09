# Find and repair the dependency planner

The public API is `planner.plan(graph)`; follow its import to the implementation. Graph keys are task names and values are prerequisite-name lists. Include prerequisites that are not keys as leaf tasks. Return a topological order, always choosing the lexicographically smallest currently ready task. Duplicate prerequisites count once. Empty graph returns []. A directed cycle (including a self-loop) raises ValueError. Do not mutate the graph.

Only edit: `project/scheduling/graph.py`. Keep README, public tests, and definitions/specification files unchanged. No third-party dependencies or network access are needed.

Run the visible checks:

```sh
python3 -m unittest test_public.py
```
