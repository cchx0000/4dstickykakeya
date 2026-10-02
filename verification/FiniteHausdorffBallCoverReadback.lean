import Theorems.Thm_StickyKakeya4_finite_hausdorff_ball_cover

#check StickyKakeya4.exists_finite_radius_cost_ball_cover_of_compact_dimH_lt
#print axioms StickyKakeya4.exists_radius_inflation_with_rpow_cost
#print axioms StickyKakeya4.exists_finite_radius_cost_ball_cover_of_compact_dimH_lt
#print axioms StickyKakeya4.exists_fin_radius_cost_ball_cover_of_compact_dimH_lt

example {X : Type*} [MetricSpace X] [Nonempty X]
    (s : Set X) (hs : IsCompact s)
    {q : NNReal} (hdim : dimH s < (q : ENNReal))
    {rho epsilon : ℝ} (hrho : 0 < rho) (hepsilon : 0 < epsilon) :
    ∃ N : ℕ, ∃ center : Fin N → X, ∃ radius : Fin N → ℝ,
      s ⊆ ⋃ n, Metric.ball (center n) (radius n) ∧
      (∀ n, 0 < radius n ∧ radius n < rho) ∧
      (∑ n, radius n ^ (q : ℝ)) < epsilon := by
  exact StickyKakeya4.exists_fin_radius_cost_ball_cover_of_compact_dimH_lt
    s hs hdim hrho hepsilon
