import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
A density-growth budget with an explicit reference-capacity creation term.
This repairs the probability bookkeeping of a genuine filtration. It does not
assert that moving geometric caps form such a filtration or that their capacity
creation is controlled by the sticky hypotheses.
-/

open scoped BigOperators

namespace StickyKakeya4.FiltrationCapacityBudget

noncomputable def gainConstant (K : ℝ) : ℝ := Real.log K - 1 + 1 / K

noncomputable def entropyRemainder (q y : ℝ) : ℝ :=
  y * (Real.log y - Real.log q) - y + q

noncomputable def potential (L q c : ℝ) : ℝ :=
  c * q * (1 + Real.log L - Real.log q)

theorem gainConstant_pos {K : ℝ} (hK : 1 < K) : 0 < gainConstant K := by
  have hKpos : 0 < K := lt_trans zero_lt_one hK
  have hi : 0 < K⁻¹ := inv_pos.mpr hKpos
  have hine : K⁻¹ ≠ 1 := by
    intro h
    have := congrArg (fun x : ℝ => x * K) h
    simp [ne_of_gt hKpos] at this
    linarith
  have h := Real.log_lt_sub_one_of_pos hi hine
  rw [Real.log_inv] at h
  unfold gainConstant
  simpa [one_div] using (show 0 < Real.log K - 1 + K⁻¹ by linarith)

theorem entropyRemainder_nonneg {q y : ℝ} (hq : 0 < q) (hy : 0 ≤ y) :
    0 ≤ entropyRemainder q y := by
  by_cases hy0 : y = 0
  · simp [entropyRemainder, hy0, le_of_lt hq]
  have hyp : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  have h := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hq hyp)) hy
  rw [Real.log_div (ne_of_gt hq) hy0] at h
  have he : y * (q / y - 1) = q - y := by field_simp
  rw [he] at h
  unfold entropyRemainder
  nlinarith

theorem gain_le_entropyRemainder {K q y : ℝ} (hK : 1 < K) (hq : 0 < q)
    (hgain : K * q ≤ y) : gainConstant K * y ≤ entropyRemainder q y := by
  have hKp : 0 < K := lt_trans zero_lt_one hK
  have hyp : 0 < y := lt_of_lt_of_le (mul_pos hKp hq) hgain
  have h := mul_le_mul_of_nonneg_left
    (Real.one_sub_inv_le_log_of_pos (div_pos hyp (mul_pos hKp hq)))
    (le_of_lt hyp)
  rw [Real.log_div (ne_of_gt hyp) (ne_of_gt (mul_pos hKp hq)),
    Real.log_mul (ne_of_gt hKp) (ne_of_gt hq)] at h
  have he : y * (1 - (y / (K * q))⁻¹) = y - K * q := by
    field_simp
  rw [he] at h
  have hi : K * (1 / K) = 1 := by field_simp
  have hm := mul_nonneg (le_of_lt (sub_pos.mpr hK)) (sub_nonneg.mpr hgain)
  have hh := mul_le_mul_of_nonneg_left h (le_of_lt hKp)
  have hs : K * (gainConstant K * y) ≤ K * entropyRemainder q y := by
    unfold gainConstant entropyRemainder
    nlinarith
  nlinarith

theorem potential_nonneg {L q c : ℝ} (hq : 0 ≤ q)
    (hqL : q ≤ L) (hc : 0 ≤ c) : 0 ≤ potential L q c := by
  by_cases hq0 : q = 0
  · simp [potential, hq0]
  have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
  have hl := Real.log_le_log hqp hqL
  unfold potential
  exact mul_nonneg (mul_nonneg hc hq) (by linarith)

theorem node_growth_budget {ι : Type*} (s : Finset ι)
    (L K q c : ℝ) (y cap : ι → ℝ)
    (hK : 1 < K) (hq : 0 < q) (hqL : q ≤ L)
    (hy : ∀ i ∈ s, 0 ≤ y i) (hcap : ∀ i ∈ s, 0 ≤ cap i)
    (hmass : ∑ i ∈ s, cap i * y i ≤ c * q) :
    gainConstant K * (∑ i ∈ s, if K * q ≤ y i then cap i * y i else 0) ≤
      potential L q c - ∑ i ∈ s, potential L (y i) (cap i) +
        q * max 0 ((∑ i ∈ s, cap i) - c) := by
  classical
  have hlocal : ∀ i ∈ s,
      gainConstant K * (if K * q ≤ y i then cap i * y i else 0) ≤
        cap i * entropyRemainder q (y i) := by
    intro i hi
    by_cases hg : K * q ≤ y i
    · simp only [if_pos hg]
      have h := mul_le_mul_of_nonneg_left
        (gain_le_entropyRemainder hK hq hg) (hcap i hi)
      nlinarith
    · simp only [if_neg hg, mul_zero]
      exact mul_nonneg (hcap i hi) (entropyRemainder_nonneg hq (hy i hi))
  have hsum := Finset.sum_le_sum hlocal
  rw [← Finset.mul_sum] at hsum
  have hlog : 0 ≤ Real.log L - Real.log q :=
    sub_nonneg.mpr (Real.log_le_log hq hqL)
  have hkill := mul_nonneg (sub_nonneg.mpr hmass) hlog
  have hident :
      (∑ i ∈ s, cap i * entropyRemainder q (y i)) =
        potential L q c - (∑ i ∈ s, potential L (y i) (cap i)) +
          q * ((∑ i ∈ s, cap i) - c) -
          (c * q - ∑ i ∈ s, cap i * y i) * (Real.log L - Real.log q) := by
    simp only [entropyRemainder, potential, mul_add, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.sum_mul]
    simp_rw [← mul_assoc]
    rw [← Finset.sum_mul]
    ring
  rw [hident] at hsum
  have hcapmax := mul_le_mul_of_nonneg_left
    (le_max_right 0 ((∑ i ∈ s, cap i) - c)) (le_of_lt hq)
  linarith

theorem node_growth_budget_of_subcapacity {ι : Type*} (s : Finset ι)
    (L K q c : ℝ) (y cap : ι → ℝ)
    (hK : 1 < K) (hq : 0 < q) (hqL : q ≤ L)
    (hy : ∀ i ∈ s, 0 ≤ y i) (hcap : ∀ i ∈ s, 0 ≤ cap i)
    (hmass : ∑ i ∈ s, cap i * y i ≤ c * q)
    (hcapacity : ∑ i ∈ s, cap i ≤ c) :
    gainConstant K * (∑ i ∈ s, if K * q ≤ y i then cap i * y i else 0) ≤
      potential L q c - ∑ i ∈ s, potential L (y i) (cap i) := by
  have h := node_growth_budget s L K q c y cap hK hq hqL hy hcap hmass
  simpa [max_eq_left (sub_nonpos.mpr hcapacity)] using h

/-- Renormalizing only the reference capacities sharpens the overlap cost
from its linear excess to its logarithmic multiplicity. -/
theorem node_growth_budget_log_capacity {ι : Type*} (s : Finset ι)
    (L K q c : ℝ) (y cap : ι → ℝ)
    (hK : 1 < K) (hq : 0 < q) (hqL : q ≤ L) (hc : 0 < c)
    (hy : ∀ i ∈ s, 0 ≤ y i) (hcap : ∀ i ∈ s, 0 ≤ cap i)
    (hmass : ∑ i ∈ s, cap i * y i ≤ c * q) :
    gainConstant K * (∑ i ∈ s, if K * q ≤ y i then cap i * y i else 0) ≤
      potential L q c - ∑ i ∈ s, potential L (y i) (cap i) +
        c * q * Real.log (max c (∑ i ∈ s, cap i) / c) := by
  classical
  let C : ℝ := max c (∑ i ∈ s, cap i)
  have hcC : c ≤ C := le_max_left _ _
  have hC : 0 < C := lt_of_lt_of_le hc hcC
  have hq' : 0 < q * c / C := div_pos (mul_pos hq hc) hC
  have hq'q : q * c / C ≤ q := by
    apply (div_le_iff₀ hC).mpr
    exact mul_le_mul_of_nonneg_left hcC (le_of_lt hq)
  have hmass' : C * (q * c / C) = c * q := by field_simp
  have h := node_growth_budget_of_subcapacity s L K (q * c / C) C y cap
    hK hq' (hq'q.trans hqL) hy hcap (by simpa [hmass'] using hmass)
    (le_max_right _ _)
  have hsubset : (∑ i ∈ s, if K * q ≤ y i then cap i * y i else 0) ≤
      ∑ i ∈ s, if K * (q * c / C) ≤ y i then cap i * y i else 0 := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases hg : K * q ≤ y i
    · have hg' : K * (q * c / C) ≤ y i :=
        (mul_le_mul_of_nonneg_left hq'q (by linarith)).trans hg
      simp [hg, hg']
    · simp only [if_neg hg]
      split_ifs
      · exact mul_nonneg (hcap i hi) (hy i hi)
      · exact le_rfl
  have hweighted := mul_le_mul_of_nonneg_left hsubset (le_of_lt (gainConstant_pos hK))
  have hphi : potential L (q * c / C) C =
      potential L q c + c * q * Real.log (C / c) := by
    unfold potential
    rw [Real.log_div (ne_of_gt (mul_pos hq hc)) (ne_of_gt hC),
      Real.log_mul (ne_of_gt hq) (ne_of_gt hc),
      Real.log_div (ne_of_gt hC) (ne_of_gt hc)]
    field_simp
    ring
  rw [hphi] at h
  dsimp only [C] at h hweighted
  linarith

/-- Only the parent-incidence identity is needed for telescoping. A rooted tree
is a special case; no geometric capacity conservation is hidden here. -/
theorem sum_child_values {ι : Type*} [DecidableEq ι] (V : Finset ι)
    (root : ι) (parent : ι → ι) (F : ι → ℝ)
    (hparent : ∀ w ∈ V.erase root, parent w ∈ V) :
    (∑ v ∈ V, ∑ w ∈ (V.erase root).filter (fun w => parent w = v), F w) =
      ∑ w ∈ V.erase root, F w := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Finset.sum_eq_single (parent w)]
  · simp
  · intro v _ hv
    simp [Ne.symm hv]
  · intro hp
    exact False.elim (hp (hparent w hw))

theorem finite_tree_growth_budget {ι : Type*} [DecidableEq ι]
    (V : Finset ι) (root : ι) (parent : ι → ι) (L K : ℝ) (q cap : ι → ℝ)
    (hroot : root ∈ V) (hparent : ∀ w ∈ V.erase root, parent w ∈ V)
    (hK : 1 < K) (hq : ∀ v ∈ V, 0 < q v) (hqL : ∀ v ∈ V, q v ≤ L)
    (hcap : ∀ v ∈ V, 0 ≤ cap v)
    (hmass : ∀ v ∈ V,
      ∑ w ∈ (V.erase root).filter (fun w => parent w = v), cap w * q w ≤ cap v * q v) :
    gainConstant K *
        (∑ v ∈ V, ∑ w ∈ (V.erase root).filter (fun w => parent w = v),
          if K * q v ≤ q w then cap w * q w else 0) ≤
      potential L (q root) (cap root) +
        ∑ v ∈ V, q v * max 0
          ((∑ w ∈ (V.erase root).filter (fun w => parent w = v), cap w) - cap v) := by
  classical
  have hlocal : ∀ v ∈ V,
      gainConstant K *
          (∑ w ∈ (V.erase root).filter (fun w => parent w = v),
            if K * q v ≤ q w then cap w * q w else 0) ≤
        potential L (q v) (cap v) -
          (∑ w ∈ (V.erase root).filter (fun w => parent w = v),
            potential L (q w) (cap w)) +
          q v * max 0
            ((∑ w ∈ (V.erase root).filter (fun w => parent w = v), cap w) - cap v) := by
    intro v hv
    apply node_growth_budget _ L K (q v) (cap v) q cap hK (hq v hv) (hqL v hv)
    · intro w hw
      exact le_of_lt (hq w (Finset.mem_of_mem_erase (Finset.mem_filter.mp hw).1))
    · intro w hw
      exact hcap w (Finset.mem_of_mem_erase (Finset.mem_filter.mp hw).1)
    · exact hmass v hv
  have hsum := Finset.sum_le_sum hlocal
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_child_values V root parent (fun v => potential L (q v) (cap v)) hparent] at hsum
  have he := Finset.sum_erase_add V (fun v => potential L (q v) (cap v)) hroot
  linarith

theorem finite_tree_growth_budget_of_subcapacity {ι : Type*} [DecidableEq ι]
    (V : Finset ι) (root : ι) (parent : ι → ι) (L K : ℝ) (q cap : ι → ℝ)
    (hroot : root ∈ V) (hparent : ∀ w ∈ V.erase root, parent w ∈ V)
    (hK : 1 < K) (hq : ∀ v ∈ V, 0 < q v) (hqL : ∀ v ∈ V, q v ≤ L)
    (hcap : ∀ v ∈ V, 0 ≤ cap v)
    (hmass : ∀ v ∈ V,
      ∑ w ∈ (V.erase root).filter (fun w => parent w = v), cap w * q w ≤ cap v * q v)
    (hcapacity : ∀ v ∈ V,
      ∑ w ∈ (V.erase root).filter (fun w => parent w = v), cap w ≤ cap v) :
    gainConstant K *
        (∑ v ∈ V, ∑ w ∈ (V.erase root).filter (fun w => parent w = v),
          if K * q v ≤ q w then cap w * q w else 0) ≤
      potential L (q root) (cap root) := by
  have h := finite_tree_growth_budget V root parent L K q cap hroot hparent hK hq hqL hcap hmass
  have hz : (∑ v ∈ V, q v * max 0
      ((∑ w ∈ (V.erase root).filter (fun w => parent w = v), cap w) - cap v)) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    rw [max_eq_left (sub_nonpos.mpr (hcapacity v hv)), mul_zero]
  simpa [hz] using h

theorem finite_tree_growth_budget_log_capacity {ι : Type*} [DecidableEq ι]
    (V : Finset ι) (root : ι) (parent : ι → ι) (L K : ℝ) (q cap : ι → ℝ)
    (hroot : root ∈ V) (hparent : ∀ w ∈ V.erase root, parent w ∈ V)
    (hK : 1 < K) (hq : ∀ v ∈ V, 0 < q v) (hqL : ∀ v ∈ V, q v ≤ L)
    (hcap : ∀ v ∈ V, 0 < cap v)
    (hmass : ∀ v ∈ V,
      ∑ w ∈ (V.erase root).filter (fun w => parent w = v), cap w * q w ≤ cap v * q v) :
    gainConstant K *
        (∑ v ∈ V, ∑ w ∈ (V.erase root).filter (fun w => parent w = v),
          if K * q v ≤ q w then cap w * q w else 0) ≤
      potential L (q root) (cap root) +
        ∑ v ∈ V, cap v * q v * Real.log
          (max (cap v) (∑ w ∈ (V.erase root).filter (fun w => parent w = v), cap w) / cap v) := by
  classical
  have hlocal := fun v (hv : v ∈ V) => node_growth_budget_log_capacity
    ((V.erase root).filter (fun w => parent w = v)) L K (q v) (cap v) q cap
    hK (hq v hv) (hqL v hv) (hcap v hv)
    (fun w hw => le_of_lt (hq w (Finset.mem_of_mem_erase (Finset.mem_filter.mp hw).1)))
    (fun w hw => le_of_lt (hcap w (Finset.mem_of_mem_erase (Finset.mem_filter.mp hw).1)))
    (hmass v hv)
  have hsum := Finset.sum_le_sum hlocal
  rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    sum_child_values V root parent (fun v => potential L (q v) (cap v)) hparent] at hsum
  have he := Finset.sum_erase_add V (fun v => potential L (q v) (cap v)) hroot
  linarith

end StickyKakeya4.FiltrationCapacityBudget
