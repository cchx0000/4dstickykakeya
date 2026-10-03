import Theorems.Thm_StickyKakeya4_filtration_capacity_budget

/-!
Finite reference-capacity envelopes. The recursive construction is the least
superadditive majorant of the original node capacities. A bounded comparison
with these original capacities transfers genuine density growth to the
filtration budget without summing all positive local duplication costs.
No bound on this envelope for the geometric hairbrush tree is assumed as a
conclusion of the sticky datum.
-/

open scoped BigOperators

namespace StickyKakeya4.CapacityEnvelopeBudget

open FiltrationCapacityBudget

noncomputable def envelope {ι : Type*} (children : ι → Finset ι)
    (cap : ι → ℝ) : ℕ → ι → ℝ
  | 0, v => cap v
  | n + 1, v => max (cap v) (∑ w ∈ children v, envelope children cap n w)

theorem cap_le_envelope {ι : Type*} (children : ι → Finset ι)
    (cap : ι → ℝ) (n : ℕ) (v : ι) : cap v ≤ envelope children cap n v := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_left _ _

theorem envelope_le_majorant {ι : Type*} (children : ι → Finset ι)
    (cap R : ι → ℝ) (hcap : ∀ v, cap v ≤ R v)
    (hsub : ∀ v, ∑ w ∈ children v, R w ≤ R v) (n : ℕ) :
    ∀ v, envelope children cap n v ≤ R v := by
  induction n with
  | zero => exact hcap
  | succ n ih =>
      intro v
      apply max_le (hcap v)
      exact (Finset.sum_le_sum (fun w _ => ih w)).trans (hsub v)

theorem envelope_stabilizes {ι : Type*} (children : ι → Finset ι)
    (cap : ι → ℝ) (rank : ι → ℕ) (hcap : ∀ v, 0 ≤ cap v)
    (hdown : ∀ v, ∀ w ∈ children v, rank w < rank v) (n : ℕ) :
    ∀ v, rank v ≤ n → envelope children cap (n + 1) v = envelope children cap n v := by
  classical
  induction n with
  | zero =>
      intro v hv
      have hempty : children v = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        have := hdown v w hw
        omega
      simp [envelope, hempty, max_eq_left (hcap v)]
  | succ n ih =>
      intro v hv
      change max (cap v) (∑ w ∈ children v, envelope children cap (n + 1) w) =
        max (cap v) (∑ w ∈ children v, envelope children cap n w)
      congr 1
      apply Finset.sum_congr rfl
      intro w hw
      apply ih w
      have := hdown v w hw
      omega

theorem envelope_is_subcapacity {ι : Type*} (children : ι → Finset ι)
    (cap : ι → ℝ) (rank : ι → ℕ) (hcap : ∀ v, 0 ≤ cap v)
    (hdown : ∀ v, ∀ w ∈ children v, rank w < rank v) (N : ℕ)
    (hbound : ∀ v, rank v ≤ N) (v : ι) :
    (∑ w ∈ children v, envelope children cap N w) ≤ envelope children cap N v := by
  have hs := envelope_stabilizes children cap rank hcap hdown N v (hbound v)
  rw [← hs]
  exact le_max_right _ _

/-- The finite-height envelope is constructed, and is least among all capacity
majorants satisfying the required child-sum inequality. -/
theorem exists_least_capacity_majorant {ι : Type*} (children : ι → Finset ι)
    (cap : ι → ℝ) (rank : ι → ℕ) (hcap : ∀ v, 0 ≤ cap v)
    (hdown : ∀ v, ∀ w ∈ children v, rank w < rank v) (N : ℕ)
    (hbound : ∀ v, rank v ≤ N) :
    ∃ R : ι → ℝ, (∀ v, cap v ≤ R v) ∧
      (∀ v, ∑ w ∈ children v, R w ≤ R v) ∧
      ∀ S : ι → ℝ, (∀ v, cap v ≤ S v) →
        (∀ v, ∑ w ∈ children v, S w ≤ S v) → ∀ v, R v ≤ S v := by
  refine ⟨envelope children cap N, cap_le_envelope children cap N,
    envelope_is_subcapacity children cap rank hcap hdown N hbound, ?_⟩
  intro S hS hsum
  exact envelope_le_majorant children cap S hS hsum N

theorem rescaled_density_bounds {q c R B : ℝ} (hq : 0 < q) (hc : 0 < c)
    (hcR : c ≤ R) (hRc : R ≤ B * c) (hB : 0 < B) :
    0 < c * q / R ∧ c * q / R ≤ q ∧ q / B ≤ c * q / R := by
  have hR : 0 < R := lt_of_lt_of_le hc hcR
  refine ⟨div_pos (mul_pos hc hq) hR, ?_, ?_⟩
  · apply (div_le_iff₀ hR).mpr
    nlinarith
  · apply (div_le_div_iff₀ hB hR).mpr
    nlinarith

theorem rescaled_potential_eq {L q c R : ℝ} (hq : 0 < q) (hc : 0 < c)
    (hR : 0 < R) :
    potential L (c * q / R) R = potential L q c + c * q * Real.log (R / c) := by
  unfold potential
  rw [Real.log_div (ne_of_gt (mul_pos hc hq)) (ne_of_gt hR),
    Real.log_mul (ne_of_gt hc) (ne_of_gt hq),
    Real.log_div (ne_of_gt hR) (ne_of_gt hc)]
  field_simp
  ring

theorem rescaled_potential_le {L q c R B : ℝ} (hq : 0 < q) (hc : 0 < c)
    (hcR : c ≤ R) (hRc : R ≤ B * c) :
    potential L (c * q / R) R ≤ potential L q c + c * q * Real.log B := by
  have hR : 0 < R := lt_of_lt_of_le hc hcR
  rw [rescaled_potential_eq hq hc hR]
  have hratio : R / c ≤ B := (div_le_iff₀ hc).mpr hRc
  have hlog := Real.log_le_log (div_pos hR hc) hratio
  have h := mul_le_mul_of_nonneg_left hlog (le_of_lt (mul_pos hc hq))
  linarith

theorem finite_tree_budget_with_capacity_majorant {ι : Type*} [DecidableEq ι]
    (V : Finset ι) (root : ι) (parent : ι → ι)
    (L K B : ℝ) (q cap R : ι → ℝ)
    (hroot : root ∈ V) (hparent : ∀ w ∈ V.erase root, parent w ∈ V)
    (hB : 0 < B) (hK : B < K)
    (hq : ∀ v ∈ V, 0 < q v) (hqL : ∀ v ∈ V, q v ≤ L)
    (hcap : ∀ v ∈ V, 0 < cap v)
    (hcR : ∀ v ∈ V, cap v ≤ R v) (hRc : ∀ v ∈ V, R v ≤ B * cap v)
    (hRsub : ∀ v ∈ V,
      ∑ w ∈ (V.erase root).filter (fun w => parent w = v), R w ≤ R v)
    (hmass : ∀ v ∈ V,
      ∑ w ∈ (V.erase root).filter (fun w => parent w = v), cap w * q w ≤ cap v * q v) :
    gainConstant (K / B) *
        (∑ v ∈ V, ∑ w ∈ (V.erase root).filter (fun w => parent w = v),
          if K * q v ≤ q w then cap w * q w else 0) ≤
      potential L (cap root * q root / R root) (R root) := by
  classical
  let d : ι → ℝ := fun v => cap v * q v / R v
  have hbnds : ∀ v ∈ V, 0 < d v ∧ d v ≤ q v ∧ q v / B ≤ d v := by
    intro v hv
    exact rescaled_density_bounds (hq v hv) (hcap v hv) (hcR v hv) (hRc v hv) hB
  have hRpos : ∀ v ∈ V, 0 < R v := fun v hv => lt_of_lt_of_le (hcap v hv) (hcR v hv)
  have hident : ∀ v ∈ V, R v * d v = cap v * q v := by
    intro v hv
    dsimp [d]
    field_simp [ne_of_gt (hRpos v hv)]
  have hKB : 1 < K / B := (one_lt_div hB).mpr hK
  have hmass' : ∀ v ∈ V,
      ∑ w ∈ (V.erase root).filter (fun w => parent w = v), R w * d w ≤ R v * d v := by
    intro v hv
    rw [hident v hv]
    convert hmass v hv using 1
    apply Finset.sum_congr rfl
    intro w hw
    exact hident w (Finset.mem_of_mem_erase (Finset.mem_filter.mp hw).1)
  have hbudget := finite_tree_growth_budget_of_subcapacity V root parent L (K / B) d R
    hroot hparent hKB (fun v hv => (hbnds v hv).1)
    (fun v hv => (hbnds v hv).2.1.trans (hqL v hv))
    (fun v hv => le_of_lt (hRpos v hv)) hmass' hRsub
  have hgains :
      (∑ v ∈ V, ∑ w ∈ (V.erase root).filter (fun w => parent w = v),
        if K * q v ≤ q w then cap w * q w else 0) ≤
      ∑ v ∈ V, ∑ w ∈ (V.erase root).filter (fun w => parent w = v),
        if (K / B) * d v ≤ d w then R w * d w else 0 := by
    apply Finset.sum_le_sum
    intro v hv
    apply Finset.sum_le_sum
    intro w hw
    have hwV : w ∈ V := Finset.mem_of_mem_erase (Finset.mem_filter.mp hw).1
    by_cases hg : K * q v ≤ q w
    · have hkpos : 0 ≤ K / B := le_of_lt (lt_trans zero_lt_one hKB)
      have h1 := mul_le_mul_of_nonneg_left (hbnds v hv).2.1 hkpos
      have h2 := (div_le_div_iff_of_pos_right hB).mpr hg
      have h3 := (hbnds w hwV).2.2
      have hg' : (K / B) * d v ≤ d w := by
        have he : K * q v / B = (K / B) * q v := by ring
        rw [he] at h2
        linarith
      simp only [if_pos hg, if_pos hg', hident w hwV, le_refl]
    · simp only [if_neg hg]
      split_ifs
      · exact mul_nonneg (le_of_lt (hRpos w hwV)) (le_of_lt (hbnds w hwV).1)
      · exact le_rfl
  exact (mul_le_mul_of_nonneg_left hgains (le_of_lt (gainConstant_pos hKB))).trans hbudget

/-- End-to-end finite construction: the capacity majorant is the displayed
recursion, not an input certificate. Its comparison with geometric capacity
remains an explicit hypothesis. -/
theorem finite_tree_budget_with_envelope {ι : Type*} [DecidableEq ι]
    (V : Finset ι) (root : ι) (parent : ι → ι)
    (L K B : ℝ) (q cap : ι → ℝ) (rank : ι → ℕ) (N : ℕ)
    (hroot : root ∈ V) (hparent : ∀ w ∈ V.erase root, parent w ∈ V)
    (hB : 0 < B) (hK : B < K)
    (hq : ∀ v ∈ V, 0 < q v) (hqL : ∀ v ∈ V, q v ≤ L)
    (hcap : ∀ v, 0 < cap v)
    (hdown : ∀ v, ∀ w ∈ (V.erase root).filter (fun w => parent w = v), rank w < rank v)
    (hbound : ∀ v, rank v ≤ N)
    (hcomparison : ∀ v ∈ V,
      envelope (fun v => (V.erase root).filter (fun w => parent w = v)) cap N v ≤ B * cap v)
    (hmass : ∀ v ∈ V,
      ∑ w ∈ (V.erase root).filter (fun w => parent w = v), cap w * q w ≤ cap v * q v) :
    gainConstant (K / B) *
        (∑ v ∈ V, ∑ w ∈ (V.erase root).filter (fun w => parent w = v),
          if K * q v ≤ q w then cap w * q w else 0) ≤
      potential L (q root) (cap root) + cap root * q root * Real.log B := by
  let children := fun v => (V.erase root).filter (fun w => parent w = v)
  let R := envelope children cap N
  have hcR : ∀ v, cap v ≤ R v := cap_le_envelope children cap N
  have hsub : ∀ v, ∑ w ∈ children v, R w ≤ R v :=
    envelope_is_subcapacity children cap rank (fun v => le_of_lt (hcap v)) hdown N hbound
  have hbudget := finite_tree_budget_with_capacity_majorant V root parent L K B q cap R
    hroot hparent hB hK hq hqL (fun v _ => hcap v) (fun v _ => hcR v)
    hcomparison (fun v _ => hsub v) hmass
  exact hbudget.trans (rescaled_potential_le (hq root hroot) (hcap root)
    (hcR root) (hcomparison root hroot))

end StickyKakeya4.CapacityEnvelopeBudget
