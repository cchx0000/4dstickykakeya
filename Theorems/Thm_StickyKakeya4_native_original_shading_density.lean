import Theorems.Thm_StickyKakeya4_native_dense_original_parent
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
namespace NativeOriginalShadingDensity
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open NativeOriginalParentSelection NativeDenseOriginalParent
open scoped ENNReal BigOperators

/-- The original shading-volume inequality becomes a count on the actual
common-mesh original cells. The factor sixteen is the exact mesh ratio. -/
theorem source_incidence_density {n : ℕ} {D : FiniteScaleSource n} {eta beta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀ i,D.shading i=wzCellShading (mesh D) cells i)
    (htube : ∀ i,(ENNReal.ofReal D.thickness).rpow (3+beta)≤
      volume (markedUnitTube (D.line i) D.thickness)) :
    16*D.thickness^(eta+beta)*(n:ℝ)≤D.thickness*(incidences cells).card := by
  have hd := h.1.2.1
  have hh := (mul_le_mul' (le_refl ((ENNReal.ofReal D.thickness).rpow eta))
    (NativeFiniteKakeyaCounts.total_tube_lower htube)).trans h.1.2.2.2.2.2.2.2.2.2.2.2.2
  rw [total_shading_eq_incidence_volume D (half_pos hd) cells hcells] at hh
  have hr := ENNReal.toReal_mono (by finiteness) hh
  simp only [ENNReal.rpow_eq_pow] at hr
  simp only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hd.le,
    ENNReal.toReal_ofReal (half_pos hd).le] at hr
  change D.thickness^eta*((n:ℝ)*D.thickness^(3+beta))≤
    (incidences cells).card*(D.thickness/2)^4 at hr
  have hp : D.thickness^eta*D.thickness^(3+beta)=D.thickness^(eta+beta)*D.thickness^3 := by
    rw [← Real.rpow_add hd, ← Real.rpow_natCast D.thickness 3, ← Real.rpow_add hd]
    congr 1
    ring
  apply (mul_le_mul_iff_right₀ (pow_pos hd 3)).mp
  calc
    _ = 16*(D.thickness^eta*((n:ℝ)*D.thickness^(3+beta))) := by rw [mul_left_comm (D.thickness^eta) (n:ℝ),hp]; ring
    _ ≤ 16*((incidences cells).card*(D.thickness/2)^4) := mul_le_mul_of_nonneg_left hr (by norm_num)
    _ = _ := by ring

/-- A genuinely dense original parent inherits the original density exponent
on its complete backbone, including any original empty rows. -/
theorem dense_parent_density {n : ℕ} {D : FiniteScaleSource n} {eta beta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (cells : Fin n → Finset Index)
    (hcells : ∀ i,D.shading i=wzCellShading (mesh D) cells i)
    (htube : ∀ i,(ENNReal.ofReal D.thickness).rpow (3+beta)≤
      volume (markedUnitTube (D.line i) D.thickness)) (a : ℝ) (N : ℕ)
    (p : Parent) (hp : p∈parents D a N) (hexp : 0≤eta+beta)
    (hden : (incidences cells).card*(backbone D a N p).card≤
      2*n*(data D cells a N p).incidences.card) :
    D.thickness^(eta+beta)≤(data D cells a N p).lam := by
  have hd := h.1.2.1
  have hn : (0:ℝ)<n := by exact_mod_cast h.1.1
  have hT : (0:ℝ)<(backbone D a N p).card := by
    exact_mod_cast card_pos.mpr (backbone_nonempty D a N hp)
  have hi := source_incidence_density h cells hcells htube
  have hc : ((incidences cells).card:ℝ)*(backbone D a N p).card≤
      2*n*(data D cells a N p).incidences.card := by exact_mod_cast hden
  have hmass : D.thickness^(eta+beta)*(backbone D a N p).card≤
      (D.thickness/8)*(data D cells a N p).incidences.card := by
    apply (mul_le_mul_iff_left₀ (show (0:ℝ)<16*n by positivity)).mp
    calc
      _ = (16*D.thickness^(eta+beta)*n)*(backbone D a N p).card := by ring
      _ ≤ (D.thickness*(incidences cells).card)*(backbone D a N p).card :=
        mul_le_mul_of_nonneg_right hi hT.le
      _ = D.thickness*((incidences cells).card*(backbone D a N p).card) := by ring
      _ ≤ D.thickness*(2*n*(data D cells a N p).incidences.card) :=
        mul_le_mul_of_nonneg_left hc hd.le
      _ = _ := by ring
  change D.thickness^(eta+beta)≤ min 1 ((mesh D/4)*
    (parentIncidences D cells a N p).card/(backbone D a N p).card)
  apply le_min
  · exact Real.rpow_le_one hd.le h.1.2.2.1 hexp
  · apply (le_div_iff₀ hT).mpr
    simpa only [data,chartIncidences_card,mesh,div_div,show (2:ℝ)*4=8 by norm_num] using hmass

/-- Only a genuine tube-volume theorem is needed to choose this cutoff;
there is no assumed source density or output exponent certificate. -/
theorem exists_source_density_cutoff {beta : ℝ} (hbeta : 0<beta) :
    ∃ delta0 : ℝ, 0<delta0 ∧ ∀ (n : ℕ) (D : FiniteScaleSource n) (eta : ℝ)
      (cells : Fin n → Finset Index), D.thickness≤delta0 →
      IsWangZakharovNativeFiniteInput D eta →
      (∀ i,D.shading i=wzCellShading (mesh D) cells i) →
      16*D.thickness^(eta+beta)*(n:ℝ)≤D.thickness*(incidences cells).card := by
  obtain ⟨delta0,hd0,htube⟩ := exists_markedUnitTube_admissible_scale hbeta
  refine ⟨delta0,hd0,?_⟩
  intro n D eta cells hsmall h hc
  exact source_incidence_density h cells hc (fun i=>htube (D.line i)
    (h.1.2.2.2.2.1 i) D.thickness h.1.2.1 hsmall)

end NativeOriginalShadingDensity
