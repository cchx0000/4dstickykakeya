import Theorems.Thm_StickyKakeya4_native_coarse_color_selection
import Theorems.Thm_StickyKakeya4_native_unit_parent_directions
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeCoarseDirectionThinning
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeOriginalCellChartGeometry
open NativeCoarseColorSelection NativeCoarseSlopeOccupancy NativeUnitParentDirections
open scoped BigOperators

/-- One actual original label in each occupied full parameter cell. -/
def representative {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ) (N : ℕ)
    (p : Parent) : Fin n :=
  if hp : p∈R.image (parentLabel D a N) then Classical.choose (mem_image.mp hp) else ⟨0,h.1.1⟩

lemma representative_spec {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ) (N : ℕ)
    {p : Parent} (hp : p∈R.image (parentLabel D a N)) :
    representative h R a N p∈R ∧ parentLabel D a N (representative h R a N p)=p := by
  rw [representative,dif_pos hp]
  exact Classical.choose_spec (mem_image.mp hp)

/-- One residue/rank color of actual occupied cells gives genuinely separated
original representative directions at thickness64/N. -/
theorem same_color_direction_separation {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (N : ℕ) (hN : 0 < N)
    (M : ℕ) (hM : ∀q : Fin 3 → ℤ,(slopeFiber (R.image (parentLabel D a N)) q).card ≤ M)
    {p q : Parent} (hp : p∈R.image (parentLabel D a N)) (hq : q∈R.image (parentLabel D a N))
    (hne : p ≠ q)
    (hc : color (R.image (parentLabel D a N)) M hM 512 p=
      color (R.image (parentLabel D a N)) M hM 512 q) :
    64/(N:ℝ) ≤ dist (direction (D.line (representative h R a N p)))
      (direction (D.line (representative h R a N q))) := by
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  by_contra hn
  have hd : dist (direction (D.line (representative h R a N p)))
      (direction (D.line (representative h R a N q))) < 64/(N:ℝ) := lt_of_not_ge hn
  have hdN := (lt_div_iff₀ hNr).mp hd
  have hps := (representative_spec h R a N hp).2
  have hqs := (representative_spec h R a N hq).2
  have hslope : p.1=q.1 := by
    funext j
    have hfp : ⌊(N:ℝ)*slope (D.line (representative h R a N p)) j⌋=p.1 j :=
      congrFun (congrArg Prod.fst hps) j
    have hfq : ⌊(N:ℝ)*slope (D.line (representative h R a N q)) j⌋=q.1 j :=
      congrFun (congrArg Prod.fst hqs) j
    have hmod := congrFun (congrArg Prod.snd hc) j
    change p.1 j%(512:ℤ)=q.1 j%(512:ℤ) at hmod
    rw [←hfp,←hfq] at hmod
    have hdiff := slope_sub_le_direction_dist
      (D.line (representative h R a N p)) (D.line (representative h R a N q))
      (h.1.2.2.2.2.1 _) (h.2.1.1 _) (h.2.1.1 _) j
    have hclose : |(N:ℝ)*slope (D.line (representative h R a N p)) j-
        (N:ℝ)*slope (D.line (representative h R a N q)) j| < (512:ℝ)-1 := by
      rw [←mul_sub,abs_mul,abs_of_pos hNr]
      have hm := mul_le_mul_of_nonneg_left hdiff hNr.le
      nlinarith
    have he := equal_floor_of_same_residue_close _ _ 512 hmod hclose
    rwa [hfp,hfq] at he
  exact hne (same_slope_color_injective _ M 512 hM hp hq hslope hc)

/-- The finite number of ranks is derived from the actual coarse angular
collision count. Its loss is kept at the ORIGINAL delta scale. -/
lemma original_rank_budget {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hzeta : 0 ≤ zeta)
    (R : Finset (Fin n)) (N : ℕ) (hN : 0 < N) (hscale : (N:ℝ)*D.thickness ≤ 1)
    (H : ∀p : Parent,(R.filter (fun i => parentLabel D a N i=p)).Nonempty →
      D.thickness^zeta*((1/(N:ℝ))/D.thickness)^3 ≤ ((R.filter (fun i => parentLabel D a N i=p)).card:ℝ)) :
    let M := ⌈5832*D.thickness^(-zeta)⌉₊
    (∀q : Fin 3 → ℤ,(slopeFiber (R.image (parentLabel D a N)) q).card ≤ M) ∧
      (M:ℝ) ≤ 11664*D.thickness^(-zeta) := by
  have hd := h.1.2.1
  have hp : 1 ≤ D.thickness^(-zeta) := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hd h.1.2.2.1 (neg_nonpos.mpr hzeta)
  have hC : (0:ℝ) ≤ 5832*D.thickness^(-zeta) := by positivity
  constructor
  · intro q
    have hh := (occupied_slope_cell_bound h R N hN hscale H q).trans
      (Nat.le_ceil (5832*D.thickness^(-zeta)))
    exact_mod_cast hh
  · have hh := Nat.ceil_lt_add_one hC
    nlinarith

/-- Actual original representatives are thinned by their shading weights,
with simultaneous retention of average shading/tube density. This constructs
direction separation, but does not assert lower AD survives the color.
The next pruning step must charge lost ACTUAL shading mass. -/
theorem exists_dense_direction_thinning {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hzeta : 0 ≤ zeta)
    (R : Finset (Fin n)) (N : ℕ) (hN : 0 < N) (hscale : (N:ℝ)*D.thickness ≤ 1)
    (H : ∀p : Parent,(R.filter (fun i => parentLabel D a N i=p)).Nonempty →
      D.thickness^zeta*((1/(N:ℝ))/D.thickness)^3 ≤ ((R.filter (fun i => parentLabel D a N i=p)).card:ℝ))
    (shading tube : Parent → ℝ)
    (hshade : ∀p∈R.image (parentLabel D a N),0 ≤ shading p)
    (htube : ∀p∈R.image (parentLabel D a N),0 ≤ tube p)
    (hSM : 0 < ∑p∈R.image (parentLabel D a N),shading p)
    (hTM : 0 < ∑p∈R.image (parentLabel D a N),tube p) :
    ∃Q ⊆ R.image (parentLabel D a N),Q.Nonempty ∧ 0 < ∑p∈Q,shading p ∧
      (∀p∈Q,representative h R a N p∈R ∧ parentLabel D a N (representative h R a N p)=p) ∧
      (∀p∈Q,∀q∈Q,p ≠ q → 64/(N:ℝ) ≤
        dist (direction (D.line (representative h R a N p)))
          (direction (D.line (representative h R a N q)))) ∧
      (∑p∈R.image (parentLabel D a N),shading p) ≤
        ((23328*512^3:ℝ)*D.thickness^(-zeta))*(∑p∈Q,shading p) ∧
      (∑p∈R.image (parentLabel D a N),shading p)*(∑p∈Q,tube p) ≤
        2*(∑p∈R.image (parentLabel D a N),tube p)*(∑p∈Q,shading p) := by
  let P := R.image (parentLabel D a N)
  let M := ⌈5832*D.thickness^(-zeta)⌉₊
  obtain ⟨hM,hMsize⟩ := original_rank_budget h hzeta R N hN hscale H
  obtain ⟨Q,hQP,hQn,hpos,hcolor,hret,hden⟩ := exists_dense_color P M 512 (by norm_num)
    hM shading tube hshade htube hSM hTM
  refine ⟨Q,hQP,hQn,hpos,fun p hp => representative_spec h R a N (hQP hp),?_,?_,hden⟩
  · intro p hp q hq hneq
    exact same_color_direction_separation h R N hN M hM (hQP hp) (hQP hq) hneq (hcolor p hp q hq)
  · have hcoef : 2*((M*512^3:ℕ):ℝ) ≤ (23328*512^3:ℝ)*D.thickness^(-zeta) := by
      norm_num only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
      have hh := mul_le_mul_of_nonneg_right hMsize (show (0:ℝ) ≤ 2*512^3 by positivity)
      nlinarith
    exact hret.trans (mul_le_mul_of_nonneg_right hcoef hpos.le)
end NativeCoarseDirectionThinning
