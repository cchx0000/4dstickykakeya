import Theorems.Thm_StickyKakeya4_native_compact_ancestor_regularity
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2800000
noncomputable section
namespace NativeCoarseSlopeOccupancy
open Classical Finset MeasureTheory StickyKakeya4 NativeOriginalParentSelection NativeOriginalCellChartGeometry
open NativeOriginalSlopeCubePacking NativeOriginalPrunedMass NativeCompactAncestorRegularity
open scoped BigOperators ENNReal

/-- Actual fine direction packing and actual full-parameter ancestor lower
counts bound how many occupied coarse parameter cells can share one coarse
slope cell. This is the finite angular multiplicity needed before selecting
genuinely direction-separated coarse representatives. -/
theorem occupied_slope_cell_bound {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (N : ℕ)
    (hN : 0 < N) (hscale : (N:ℝ)*D.thickness ≤ 1)
    (H : ∀p : Parent,(R.filter (fun i => parentLabel D a N i=p)).Nonempty →
      D.thickness^zeta*((1/(N:ℝ))/D.thickness)^3 ≤ ((R.filter (fun i => parentLabel D a N i=p)).card:ℝ))
    (q : Fin 3 → ℤ) :
    (((R.image (parentLabel D a N)).filter (fun p => p.1=q)).card:ℝ) ≤
      5832*D.thickness^(-zeta) := by
  let A := R.filter (fun i => (parentLabel D a N i).1=q)
  let F := parentLabel D a N
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hd := h.1.2.1
  have hP : (R.image F).filter (fun p => p.1=q)=A.image F := by
    ext p
    simp only [A,F,mem_filter,mem_image]
    aesop
  have hsame (p : Parent) (hp : p∈A.image F) :
      A.filter (fun i => F i=p)=R.filter (fun i => F i=p) := by
    obtain ⟨i,hi,hip⟩ := mem_image.mp hp
    have hpq : p.1=q := by rw [←hip]; exact (mem_filter.mp hi).2
    ext j
    simp only [A,mem_filter]
    constructor
    · exact fun hj => ⟨hj.1.1,hj.2⟩
    · intro hj
      refine ⟨⟨hj.1,?_⟩,hj.2⟩
      change (F j).1=q
      rw [hj.2,hpq]
  have hbox : ∀i∈A,∀j : Fin 3,
      (q j:ℝ)/(N:ℝ) ≤ slope (D.line i) j ∧
        slope (D.line i) j ≤ (q j:ℝ)/(N:ℝ)+1/(N:ℝ) := by
    intro i hi j
    have hf : ⌊(N:ℝ)*slope (D.line i) j⌋=q j := congrFun (mem_filter.mp hi).2 j
    have hlo := Int.floor_le ((N:ℝ)*slope (D.line i) j)
    have hhi := Int.lt_floor_add_one ((N:ℝ)*slope (D.line i) j)
    rw [hf] at hlo hhi
    refine ⟨(div_le_iff₀ hNr).mpr (by nlinarith),?_⟩
    have hh : slope (D.line i) j ≤ ((q j:ℝ)+1)/(N:ℝ) :=
      (le_div_iff₀ hNr).mpr (by nlinarith)
    simpa only [add_div] using hh
  have hcap := native_cube_card_le_ratio h A
    (show D.thickness ≤ 1/(N:ℝ) from (le_div_iff₀ hNr).mpr (by nlinarith))
    (fun j => (q j:ℝ)/(N:ℝ)) hbox
  have hf : (A.card:ℝ)=∑p∈A.image F,((A.filter (fun i => F i=p)).card:ℝ) := by
    exact_mod_cast card_eq_sum_card_image F A
  have hlow : ((A.image F).card:ℝ)*(D.thickness^zeta*((1/(N:ℝ))/D.thickness)^3) ≤
      5832*((1/(N:ℝ))/D.thickness)^3 := by
    calc
      _ = ∑_p∈A.image F,D.thickness^zeta*((1/(N:ℝ))/D.thickness)^3 := by simp
      _ ≤ ∑p∈A.image F,((A.filter (fun i => F i=p)).card:ℝ) := by
        apply sum_le_sum
        intro p hp
        rw [hsame p hp]
        obtain ⟨i,hi,hip⟩ := mem_image.mp hp
        exact H p ⟨i,mem_filter.mpr ⟨(mem_filter.mp hi).1,hip⟩⟩
      _ = (A.card:ℝ) := hf.symm
      _ ≤ _ := hcap
  have hfactor : 0 < ((1/(N:ℝ))/D.thickness)^3 := by positivity
  have hc : ((A.image F).card:ℝ)*D.thickness^zeta ≤ 5832 := by
    apply (mul_le_mul_iff_left₀ hfactor).mp
    simpa only [mul_assoc] using hlow
  change (((R.image F).filter (fun p => p.1=q)).card:ℝ) ≤ _
  rw [hP,Real.rpow_neg hd.le,←div_eq_mul_inv]
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hd zeta)).mpr hc

/-- Consume the genuine original dyadic ancestors at every available level. -/
theorem original_dyadic_slope_occupancy {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (level : ℕ)
    (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (H : ∀ell : Fin (level+1),∀p : Parent,
      (R.filter (fun i => parentLabel D a (2^ell.val) i=p)).Nonempty →
        D.thickness^zeta*((1/((2^ell.val:ℕ):ℝ))/D.thickness)^3 ≤
          ((R.filter (fun i => parentLabel D a (2^ell.val) i=p)).card:ℝ)) :
    ∀ell : Fin (level+1),∀q : Fin 3 → ℤ,
      (((R.image (parentLabel D a (2^ell.val))).filter (fun p => p.1=q)).card:ℝ) ≤
        5832*D.thickness^(-zeta) := by
  intro ell q
  exact occupied_slope_cell_bound h R (2^ell.val) (by positivity)
    (dyadic_parent_scale hdy ell) (H ell) q

/-- Original compact native data yields the same retained labels, original
density and true dyadic ancestor populations, now with derived coarse angular
multiplicity at every level. No coarse separation certificate is assumed. -/
theorem compact_original_slope_occupancy (K : Set MarkedLine) (hK : IsCompact K)
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
            5832*D.thickness^(-zeta)) := by
  obtain ⟨delta0,hdelta0,hbase⟩ := compact_original_ancestor_regularization K hK hzeta
  refine ⟨delta0,hdelta0,?_⟩
  intro n D eta h hDK hsmall heta
  obtain ⟨a,level,R,hdy,ha,hR,hhalf,hshade,hden,_hCW,H⟩ := hbase n D eta h hDK hsmall heta
  exact ⟨a,level,R,hdy,ha,hR,hhalf,hshade,hden,H,
    original_dyadic_slope_occupancy h R level hdy (fun ell p hp => (H ell p hp).1)⟩
end NativeCoarseSlopeOccupancy
