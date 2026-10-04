import Theorems.Thm_StickyKakeya4_native_compact_parent_retention
import Theorems.Thm_StickyKakeya4_native_dense_original_parent
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000
noncomputable section
namespace NativeCompactParentExponent
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeDenseOriginalParent NativeCompactParentRetention

/-- Original compact-source constants are absorbed only after they are fixed.
The SAME dense parent retains delta^(epsilon+2*eta+3*nu) of original incidence
mass when N<=delta^(-nu). The physical intermediate-scale budget is explicit. -/
theorem compact_dense_parent_retention (K : Set MarkedLine) (hK : IsCompact K)
    {epsilon : ℝ} (hepsilon : 0<epsilon) :
    ∃ L delta0 : ℝ, 6≤L ∧ 0<delta0 ∧ ∀ (n : ℕ) (D : FiniteScaleSource n)
      (cells : Fin n→Finset Index) (eta a nu : ℝ) (N : ℕ),
      IsWangZakharovNativeFiniteInput D eta → (∀ i,D.line i∈K) →
      (∀ i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ)) →
      (incidences cells).Nonempty → D.thickness≤delta0 → 0<N →
      (N:ℝ)≤D.thickness^(-nu) → D.thickness*(L*N)≤1 →
      ∃ p∈parents D a N,(parentIncidences D cells a N p).Nonempty ∧
        (incidences cells).card*(backbone D a N p).card≤2*n*(data D cells a N p).incidences.card ∧
        ((incidences cells).card:ℝ)≤D.thickness^(-(epsilon+2*eta+3*nu))*
          (data D cells a N p).incidences.card := by
  obtain ⟨C,L,hC,hL,hparent⟩ := compact_parent_bound K hK
  obtain ⟨delta0,hd0,_hd1,habs⟩ := exists_positive_rpow_absorption_threshold
    hepsilon (show 0≤2*C by positivity) (show (0:ℝ)<1 by norm_num)
  refine ⟨L,delta0,hL,hd0,?_⟩
  intro n D cells eta a nu N h hDK ha hne hsmall hN hpower hscale
  have hd := h.1.2.1
  obtain ⟨p,hp,hnep,hret,hden⟩ := exists_dense_parent D cells a N h.1.1 hne
  refine ⟨p,hp,hnep,hden,?_⟩
  have hc := hparent n D eta a N h hDK ha hN hscale
  have ha' : 2*C≤D.thickness^(-epsilon) := by
    rw [Real.rpow_neg hd.le,←one_div]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hd epsilon)).mpr
    exact habs D.thickness hd hsmall
  have hN3 : (N:ℝ)^3≤D.thickness^(-3*nu) := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg N) hpower 3
    rw [←Real.rpow_mul_natCast hd.le (-nu) 3] at hh
    have he : (-nu)*(3:ℕ)= -3*nu := by push_cast; ring
    simpa only [he] using hh
  have hbound : 2*((parents D a N).card:ℝ)≤D.thickness^(-(epsilon+2*eta+3*nu)) := by
    calc
      _ ≤ 2*(C*D.thickness^(-2*eta)*(N:ℝ)^3) := mul_le_mul_of_nonneg_left hc (by norm_num)
      _ = (2*C)*(D.thickness^(-2*eta)*(N:ℝ)^3) := by ring
      _ ≤ D.thickness^(-epsilon)*(D.thickness^(-2*eta)*D.thickness^(-3*nu)) :=
        mul_le_mul ha' (mul_le_mul_of_nonneg_left hN3 (Real.rpow_pos_of_pos hd _).le)
          (by positivity) (by positivity)
      _ = _ := by
        rw [←Real.rpow_add hd,←Real.rpow_add hd]
        congr 1
        ring
  have hr : ((incidences cells).card:ℝ)≤2*(parents D a N).card*(data D cells a N p).incidences.card := by
    exact_mod_cast hret
  exact hr.trans (mul_le_mul_of_nonneg_right hbound (by positivity))

end NativeCompactParentExponent
