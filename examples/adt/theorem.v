Theorem optimize_preserves_semantics : forall (env : env) (e : expr),
    eval (optimize e) env = eval e env.
