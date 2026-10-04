import Theorems.Thm_StickyKakeya4_native_coarse_slope_occupancy
import Theorems.Thm_StickyKakeya4_native_dyadic_parent_cells
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeCoarseAncestorCounts
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeDyadicParentCells
open NativeCoarseSlopeOccupancy NativeOriginalPrunedMass
open scoped BigOperators ENNReal

lemma fiber_in_ancestor_eq {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n)) (a : ℝ)
    {coarse fine : ℕ} (hcf : coarse ≤ fine) (p q : Parent)
    (hne : ((R.filter (fun i => parentLabel D a (2^coarse) i=p)).filter
      (fun i => parentLabel D a (2^fine) i=q)).Nonempty) :
    (R.filter (fun i => parentLabel D a (2^coarse) i=p)).filter
      (fun i => parentLabel D a (2^fine) i=q)=R.filter (fun i => parentLabel D a (2^fine) i=q) := by
  obtain ⟨i,hi⟩ := hne
  have hqp : ancestor fine coarse q=p := by
    rw [←(mem_filter.mp hi).2,parent_ancestor_eq D a hcf i]
    exact (mem_filter.mp (mem_filter.mp hi).1).2
  ext j
  constructor
  · intro hj
    exact mem_filter.mpr ⟨(mem_filter.mp (mem_filter.mp hj).1).1,(mem_filter.mp hj).2⟩
  · intro hj
    refine mem_filter.mpr ⟨mem_filter.mpr ⟨(mem_filter.mp hj).1,?_⟩,(mem_filter.mp hj).2⟩
    have hh := parent_ancestor_eq D a hcf j
    rw [(mem_filter.mp hj).2,hqp] at hh
    exact hh.symm

lemma descendant_fiber_sum {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n)) (a : ℝ)
    {coarse fine : ℕ} (hcf : coarse ≤ fine) (p : Parent) :
    (R.filter (fun i => parentLabel D a (2^coarse) i=p)).card=
      ∑q∈descendants D R a fine coarse p,(R.filter (fun i => parentLabel D a (2^fine) i=q)).card := by
  rw [←image_parent_fiber_eq_descendants D R a hcf p]
  let S := R.filter (fun i => parentLabel D a (2^coarse) i=p)
  calc
    S.card=∑q∈S.image (parentLabel D a (2^fine)),(S.filter (fun i => parentLabel D a (2^fine) i=q)).card :=
      card_eq_sum_card_image (parentLabel D a (2^fine)) S
    _ = _ := by
      apply sum_congr rfl
      intro q hq
      obtain ⟨i,hi,hiq⟩ := mem_image.mp hq
      rw [fiber_in_ancestor_eq D R a hcf p q ⟨i,mem_filter.mpr ⟨hi,hiq⟩⟩]

/-- Cross-multiplied ancestor estimates for ACTUAL occupied coarse cells,
obtained by summing their disjoint original label fibers. -/
theorem descendant_counts_cross {n : ℕ} (D : FiniteScaleSource n) (R : Finset (Fin n))
    (a zeta : ℝ) (level : ℕ)
    (H : ∀ell : Fin (level+1),∀p : Parent,
      (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
        D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ∧
        ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ≤
          D.thickness^(-zeta)*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3)
    {coarse fine : ℕ} (hcf : coarse ≤ fine) (hfl : fine ≤ level) (p : Parent)
    (hne : (descendants D R a fine coarse p).Nonempty) :
    D.thickness^zeta*((1/((2^coarse:ℕ):ℝ))/D.thickness)^3 ≤
      (D.thickness^(-zeta)*((1/((2^fine:ℕ):ℝ))/D.thickness)^3)*(descendants D R a fine coarse p).card ∧
    (D.thickness^zeta*((1/((2^fine:ℕ):ℝ))/D.thickness)^3)*(descendants D R a fine coarse p).card ≤
      D.thickness^(-zeta)*((1/((2^coarse:ℕ):ℝ))/D.thickness)^3 := by
  have hS : (R.filter (fun i => parentLabel D a (2^coarse) i=p)).Nonempty := by
    have hh := hne
    rw [←image_parent_fiber_eq_descendants D R a hcf p] at hh
    exact image_nonempty.mp hh
  have hAncestor := H ⟨coarse,by omega⟩ p hS
  have hFine (q : Parent) (hq : q∈descendants D R a fine coarse p) :
      D.thickness^zeta*((1/((2^fine:ℕ):ℝ))/D.thickness)^3 ≤
        ((R.filter (fun i => parentLabel D a (2^fine) i=q)).card:ℝ) ∧
      ((R.filter (fun i => parentLabel D a (2^fine) i=q)).card:ℝ) ≤
        D.thickness^(-zeta)*((1/((2^fine:ℕ):ℝ))/D.thickness)^3 := by
    have hqF := (mem_filter.mp hq).1
    obtain ⟨i,hi,hiq⟩ := mem_image.mp hqF
    exact H ⟨fine,by omega⟩ q ⟨i,mem_filter.mpr ⟨hi,hiq⟩⟩
  have hsum : ((R.filter (fun i => parentLabel D a (2^coarse) i=p)).card:ℝ)=
      ∑q∈descendants D R a fine coarse p,((R.filter (fun i => parentLabel D a (2^fine) i=q)).card:ℝ) := by
    exact_mod_cast descendant_fiber_sum D R a hcf p
  constructor
  · apply hAncestor.1.trans
    rw [hsum]
    calc
      _ ≤ ∑_q∈descendants D R a fine coarse p,
          D.thickness^(-zeta)*((1/((2^fine:ℕ):ℝ))/D.thickness)^3 :=
        sum_le_sum (fun q hq => (hFine q hq).2)
      _ = _ := by simp [mul_comm]
  · apply le_trans _ hAncestor.2
    rw [hsum]
    calc
      _ = ∑_q∈descendants D R a fine coarse p,
          D.thickness^zeta*((1/((2^fine:ℕ):ℝ))/D.thickness)^3 := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun q hq => (hFine q hq).1)

lemma scale_ratio (delta rho tau a b : ℝ) (hd : 0 < delta) (hr : 0 < rho) :
    (delta^a*(tau/delta)^3)/(delta^b*(rho/delta)^3)=delta^(a-b)*(tau/rho)^3 := by
  rw [Real.rpow_sub hd]
  field_simp [hd.ne',hr.ne',(Real.rpow_pos_of_pos hd b).ne']

/-- Actual occupied level-fine cells have the true coarse ancestor AD3 law
with coefficient delta^(-2*zeta). This is the complete coarse cell set before
any directional coloring; no lower bound is inferred for a chosen color. -/
theorem coarse_ancestor_AD {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n))
    (a zeta : ℝ) (level : ℕ)
    (H : ∀ell : Fin (level+1),∀p : Parent,
      (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
        D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ∧
        ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ≤
          D.thickness^(-zeta)*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3)
    {coarse fine : ℕ} (hcf : coarse ≤ fine) (hfl : fine ≤ level) (p : Parent)
    (hne : (descendants D R a fine coarse p).Nonempty) :
    D.thickness^(2*zeta)*(((2^fine:ℕ):ℝ)/((2^coarse:ℕ):ℝ))^3 ≤
      ((descendants D R a fine coarse p).card:ℝ) ∧
    ((descendants D R a fine coarse p).card:ℝ) ≤
      D.thickness^(-2*zeta)*(((2^fine:ℕ):ℝ)/((2^coarse:ℕ):ℝ))^3 := by
  have hd := h.1.2.1
  have hr : (0:ℝ) < 1/((2^fine:ℕ):ℝ) := by positivity
  have hh := descendant_counts_cross D R a zeta level H hcf hfl p hne
  have hlo : (D.thickness^zeta*((1/((2^coarse:ℕ):ℝ))/D.thickness)^3)/
      (D.thickness^(-zeta)*((1/((2^fine:ℕ):ℝ))/D.thickness)^3) ≤
      ((descendants D R a fine coarse p).card:ℝ) :=
    (div_le_iff₀ (show 0 < D.thickness^(-zeta)*((1/((2^fine:ℕ):ℝ))/D.thickness)^3 by positivity)).mpr
    (by simpa only [mul_comm] using hh.1)
  have hup : ((descendants D R a fine coarse p).card:ℝ) ≤
      (D.thickness^(-zeta)*((1/((2^coarse:ℕ):ℝ))/D.thickness)^3)/
        (D.thickness^zeta*((1/((2^fine:ℕ):ℝ))/D.thickness)^3) :=
    (le_div_iff₀ (show 0 < D.thickness^zeta*((1/((2^fine:ℕ):ℝ))/D.thickness)^3 by positivity)).mpr
    (by simpa only [mul_comm] using hh.2)
  rw [scale_ratio D.thickness _ _ zeta (-zeta) hd hr] at hlo
  rw [scale_ratio D.thickness _ _ (-zeta) zeta hd hr] at hup
  have he : (1/((2^coarse:ℕ):ℝ))/(1/((2^fine:ℕ):ℝ))=((2^fine:ℕ):ℝ)/((2^coarse:ℕ):ℝ) := by
    simp only [div_eq_mul_inv,one_mul,inv_inv]
    exact mul_comm _ _
  rw [he,show zeta-(-zeta)=2*zeta by ring] at hlo
  rw [he,show -zeta-zeta= -2*zeta by ring] at hup
  exact ⟨hlo,hup⟩
/-- Original compact native data yields the same retained labels, original
density and true dyadic ancestor populations, now with derived coarse angular
multiplicity at every level. No coarse separation certificate is assumed. -/
theorem compact_original_coarse_ancestor_counts (K : Set MarkedLine) (hK : IsCompact K)
    {zeta : ℝ} (hzeta : 0 < zeta) :
    ∃delta0 : ℝ,0 < delta0 ∧ ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ),
      IsWangZakharovNativeFiniteInput D eta → (∀i,D.line i∈K) →
      D.thickness ≤ delta0 → eta ≤ zeta/16 →
      ∃ (a : ℝ) (level : ℕ) (R : Finset (Fin n)),
        D.thickness=(2:ℝ)⁻¹^level ∧
        (∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) ∧
        R.Nonempty ∧ n ≤ 2*R.card ∧ wzTotalShadingVolume D ≤ 2*shadingMass D R ∧
        (ENNReal.ofReal D.thickness).rpow zeta*tubeMass D R ≤ shadingMass D R ∧
        (∀ell : Fin (level+1),∀p : Parent,
          (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
            D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
              ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ∧
            ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ) ≤
              D.thickness^(-zeta)*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3) ∧
        (∀ell : Fin (level+1),∀q : Fin 3 → ℤ,
          (((R.image (parentLabel D a (2^ell.val))).filter (fun p => p.1=q)).card:ℝ) ≤
            5832*D.thickness^(-zeta)) ∧
        (∀ coarse fine : ℕ,coarse ≤ fine → fine ≤ level → ∀p : Parent,
          (descendants D R a fine coarse p).Nonempty →
            D.thickness^(2*zeta)*(((2^fine:ℕ):ℝ)/((2^coarse:ℕ):ℝ))^3 ≤
              ((descendants D R a fine coarse p).card:ℝ) ∧
            ((descendants D R a fine coarse p).card:ℝ) ≤
              D.thickness^(-2*zeta)*(((2^fine:ℕ):ℝ)/((2^coarse:ℕ):ℝ))^3) := by
  obtain ⟨delta0,hdelta0,hbase⟩ := NativeCoarseSlopeOccupancy.compact_original_slope_occupancy K hK hzeta
  refine ⟨delta0,hdelta0,?_⟩
  intro n D eta h hDK hsmall heta
  obtain ⟨a,level,R,hdy,ha,hR,hhalf,hshade,hden,H,hSlope⟩ := hbase n D eta h hDK hsmall heta
  exact ⟨a,level,R,hdy,ha,hR,hhalf,hshade,hden,H,hSlope,
    fun coarse fine hcf hfl p hp => coarse_ancestor_AD h R a zeta level H hcf hfl p hp⟩
end NativeCoarseAncestorCounts
