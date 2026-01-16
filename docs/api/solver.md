# Solver API

The `Solver` class is the main entry point for the Python SDK. It manages communication with the Lean kernel and handles the verification lifecycle.

## Solver Class

::: leancert.solver.Solver
    options:
      members:
        - __init__
        - find_bounds
        - find_roots
        - find_unique_root
        - verify_bound
        - integrate
      show_root_heading: true
      show_source: false

## Convenience Functions

These standalone functions use a default solver instance for quick scripting.

::: leancert.solver.find_bounds

::: leancert.solver.find_roots

::: leancert.solver.find_unique_root

::: leancert.solver.verify_bound

::: leancert.solver.integrate
