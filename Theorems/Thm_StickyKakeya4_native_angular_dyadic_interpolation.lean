import Theorems.Thm_StickyKakeya4_native_conditional_reference_menu
import Theorems.Thm_StickyKakeya4_native_normalized_cell_angular_menu
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

noncomputable section
namespace NativeAngularDyadicInterpolation
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeLocalParentGeometry NativeNormalizedCellRelativeMenu NativeNormalizedCellAngularMenu
open NativeDyadicParentCells NativeTangentGridCoarsening
open scoped BigOperators

lemma angular_ancestor {n : ℕ} (D : FiniteScaleSource n) (N : ℕ) (p : Parent)
    {c s : ℕ} (hcs : c≤ s) (i : Fin n) :
    (fun j => angularCell D N (2^s) p i j/(2^(s-c):ℕ))=angularCell D N (2^c) p i := by
  funext j
  simpa only [angularCell,Nat.cast_pow,Nat.cast_ofNat,mul_div_assoc] using
    (floor_dyadic_ancestor (localSlope D N p i j/8) hcs).symm

/-- Every actual fine spatial cell has one exact coarser dyadic ancestor.
This includes the six bottom depths between Rho and the final mesh Rho/64. -/
lemma physical_ancestor {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ) (p : Parent)
    {c s : ℕ} (hcs : c≤ s) (k : Index) :
    (fun j => physicalCell D a N (2^s) p k j/(2^(s-c):ℕ))=physicalCell D a N (2^c) p k := by
  funext j
  simp only [physicalCell,wzDyadicCellIndex]
  have hc : physicalPoint D a N p k j/(64/((2^c:ℕ):ℝ))=
      (2:ℝ)^c*(physicalPoint D a N p k j/64) := by push_cast; field_simp
  have hs : physicalPoint D a N p k j/(64/((2^s:ℕ):ℝ))=
      (2:ℝ)^s*(physicalPoint D a N p k j/64) := by push_cast; field_simp
  rw [hc,hs]
  exact (floor_dyadic_ancestor _ hcs).symm

def descendants (d K : ℕ) (q : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun j => Ico ((K:ℤ)*q j) ((K:ℤ)*(q j+1)))

lemma descendants_card (d K : ℕ) (q : Fin d → ℤ) : (descendants d K q).card=K^d := by
  have hcard (j : Fin d) : (Ico ((K:ℤ)*q j) ((K:ℤ)*(q j+1))).card=K := by
    rw [Int.card_Ico,show (K:ℤ)*(q j+1)-(K:ℤ)*q j=K by ring,Int.toNat_natCast]
  simp only [descendants,Fintype.card_piFinset,hcard,prod_const,card_univ,Fintype.card_fin]

lemma mem_descendants {d K : ℕ} (hK : 0< K) (q v : Fin d → ℤ)
    (H : ∀j,v j/(K:ℤ)=q j) : v∈descendants d K q := by
  apply Fintype.mem_piFinset.mpr
  intro j
  have hKz : (0:ℤ)<K := by exact_mod_cast hK
  have hn := Int.emod_nonneg (v j) (ne_of_gt hKz)
  have hl := Int.emod_lt_of_pos (v j) hKz
  have he := Int.emod_add_ediv_mul (v j) (K:ℤ)
  rw [H j] at he
  exact mem_Ico.mpr ⟨by nlinarith only [hn,he],by nlinarith only [hl,he]⟩

/-- Exact geometric multiplicity: one coarser full angular bin contains
at most 2^(3(s-c)) finer bins. Incidence weights are never replaced by labels. -/
theorem angular_fiber_card {n : ℕ} (D : FiniteScaleSource n) (N : ℕ) (p : Parent)
    (E : Finset (Fin n × Index)) {c s : ℕ} (hcs : c≤ s) (q : Fin 3 → ℤ) :
    (((E.filter (fun z => angularCell D N (2^c) p z.1=q)).image
      (fun z => angularCell D N (2^s) p z.1)).card)≤ (2^(s-c))^3 := by
  have hs : (E.filter (fun z => angularCell D N (2^c) p z.1=q)).image
      (fun z => angularCell D N (2^s) p z.1)⊆ descendants 3 (2^(s-c)) q := by
    intro v hv
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hv
    apply mem_descendants (by positivity)
    intro j
    exact (congrFun (angular_ancestor D N p hcs z.1) j).trans (congrFun (mem_filter.mp hz).2 j)
  exact (card_le_card hs).trans_eq (descendants_card _ _ _)

theorem angular_image_interpolation {n : ℕ} (D : FiniteScaleSource n) (N : ℕ) (p : Parent)
    (E : Finset (Fin n × Index)) {c s : ℕ} (hcs : c≤ s) :
    ((E.image (fun z => angularCell D N (2^s) p z.1)).card:ℝ)≤
      (((2^(s-c))^3:ℕ):ℝ)*(E.image (fun z => angularCell D N (2^c) p z.1)).card := by
  exact image_card_le_real_mul_of_fiber_images E
    (fun z => angularCell D N (2^s) p z.1) (fun z => angularCell D N (2^c) p z.1) _
    (fun q _ => by exact_mod_cast angular_fiber_card D N p E hcs q)

/-- The final mesh is Rho/64. Its entire bottom scale interval is paid by
64^3 angular descendants and exact spatial containment, without extra E1 slots. -/
theorem bottom_angular_interpolation {n : ℕ} (D : FiniteScaleSource n) (N : ℕ) (p : Parent)
    (E : Finset (Fin n × Index)) {m s : ℕ} (hms : m≤ s) (hsm : s≤ m+6) :
    ((E.image (fun z => angularCell D N (2^s) p z.1)).card:ℝ)≤
      (64:ℝ)^3*(E.image (fun z => angularCell D N (2^m) p z.1)).card := by
  have hpow : (2^(s-m):ℕ)≤ 64 := by
    simpa only [show (2:ℕ)^6=64 by norm_num] using
      Nat.pow_le_pow_right (by norm_num : 0< (2:ℕ)) (show s-m≤ 6 by omega)
  have hcost : (((2^(s-m))^3:ℕ):ℝ)≤ (64:ℝ)^3 := by
    exact_mod_cast Nat.pow_le_pow_left hpow 3
  exact (angular_image_interpolation D N p E hms).trans
    (mul_le_mul_of_nonneg_right hcost (Nat.cast_nonneg _))

end NativeAngularDyadicInterpolation
