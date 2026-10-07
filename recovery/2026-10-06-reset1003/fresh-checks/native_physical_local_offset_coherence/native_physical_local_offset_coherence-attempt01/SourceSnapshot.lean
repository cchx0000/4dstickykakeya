import Theorems.Thm_StickyKakeya4_native_physical_matrix_palette
import Theorems.Thm_StickyKakeya4_native_fixed_offset_coherence

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2500000
noncomputable section

namespace NativePhysicalLocalOffsetCoherence
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeNormalizedCellRelativeMenu NativeNormalizedCellAngularMenu NativeHeightMetricMenu
open NativeTranslatedGrainHeightOverlap NativeIncidentAffineAnchorGeometry NativeGrainQuotientInjection
open NativeGrainQuotientBins NativeReferenceXYGridLinear NativeHorizontalGrainSlice
open NativeActualOffsetCellCaps NativeFinitePointCoherence NativeFixedOffsetCoherence
open NativeActualOffsetMenu NativePhysicalMatrixPalette NativeMatrixHeightWholePoint
open scoped BigOperators Matrix.Norms.Elementwise

/-- The actual native angular labels bound the offset image AFTER matrix
selection. Local variation is exactly rho and no global metric is inserted
into the offset width. -/
theorem actual_local_cell_offset_cap {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m M : ℕ) (hM : 0 < M) (p : Parent) (S : Finset (Fin n × Index))
    (hp : ∀z∈S,parentLabel D a (2^m) z.1=p)
    (P0 : Submodule ℝ E4) (hP0 : P0≤ heightKernel) (ell : ℕ)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P0=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (xi : Index → EuclideanSpace ℝ (Fin (4-ell))) (error d upper : ℝ)
    (he : 0 ≤ error) (hdpos : 0 < d)
    (hF : ∀k∈S.image Prod.snd,‖F (rawHeight D m k)‖ ≤ (1/4:ℝ))
    (hvar : ∀z∈S,∀u∈S,physicalCell D a (2^m) M p z.2=physicalCell D a (2^m) M p u.2 →
      ‖F (rawHeight D m z.2)-F (rawHeight D m u.2)‖ ≤ 64/(M:ℝ))
    (hres : ∀z∈S,‖quotientMap P0 hP0 ell hell hell4 hd (F (rawHeight D m z.2))
      (localHorizontalSlope D (2^m) p z.1)-xi z.2‖ ≤ error)
    (hlower : ∀k∈S.image Prod.snd,d ≤
      (((S.filter (fun z => z.2=k)).image (fun z => angularCell D (2^m) M p z.1)).card:ℝ))
    (hupper : ∀c,((angularMenu D a m M p S c).card:ℝ) ≤ upper) :
    let H := 2*error+48/(M:ℝ)+8*(64/(M:ℝ))
    ∀c,(((S.filter (fun z => physicalCell D a (2^m) M p z.2=c)).image
      (fun z => label H (xi z.2))).card:ℝ) ≤ ((4:ℝ)^(4-ell)*upper)/d := by
  intro H c
  let I := S.filter (fun z => physicalCell D a (2^m) M p z.2=c)
  have hIS : I⊆S := filter_subset _ _
  have hlowerI : ∀k∈I.image Prod.snd,d ≤
      (((I.filter (fun z => z.2=k)).image (fun z => angularCell D (2^m) M p z.1)).card:ℝ) := by
    intro k hk
    rw [point_fiber_in_cell S Prod.snd (physicalCell D a (2^m) M p) c k hk]
    exact hlower k (image_subset_image hIS hk)
  have hvarI : ∀k∈I.image Prod.snd,∀l∈I.image Prod.snd,
      ‖F (rawHeight D m k)-F (rawHeight D m l)‖ ≤ 64/(M:ℝ) := by
    intro k hk l hl
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hk
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hl
    exact hvar z (hIS hz) u (hIS hu) ((mem_filter.mp hz).2.trans (mem_filter.mp hu).2.symm)
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have hh := NativeActualOffsetMenu.actual_offset_count D a (2^m) M hM p I
    (fun z hz => hp z (hIS hz)) P0 hP0 ell hell hell4 hd
    (fun k => F (rawHeight D m k)) xi error (64/(M:ℝ)) d
    (fun k hk => hF k (image_subset_image hIS hk)) hvarI
    (fun z hz => hres z (hIS hz)) hlowerI (by positivity)
  have hbound : d*((I.image (fun z => label H (xi z.2))).card:ℝ) ≤ (4:ℝ)^(4-ell)*upper :=
    hh.trans (mul_le_mul_of_nonneg_left (hupper c) (by positivity))
  exact (le_div_iff₀ hdpos).mpr (by simpa only [mul_comm] using hbound)

/-- Two actual ORIGINAL-point choices before the sole third edge core:
first matrix palette, then a fresh local-variation offset choice. The source
matrix, offsets, native angular labels, parent, and literal incidence fibers
are unchanged. The final point set is lifted directly into the original S. -/
theorem select_actual_matrix_offset_menu {n K : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m : ℕ) (p : Parent) (S : Finset (Fin n × Index)) (hS : S.Nonempty)
    (hp : ∀z∈S,parentLabel D a (2^m) z.1=p)
    (P0 : Submodule ℝ E4) (hP0 : P0≤ heightKernel) (ell : ℕ) (hell23 : ell=2 ∨ ell=3)
    (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P0=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (xi : Index → EuclideanSpace ℝ (Fin (4-ell))) (error metric shift : ℝ)
    (he : 0 ≤ error) (hmetric : 0 ≤ metric)
    (M : Fin K → ℕ) (hM : ∀j,0 < M j)
    (hwindow : ∀j,meshWidth m/512 ≤ 64/(M j:ℝ))
    (hErrorWindow : ∀j,error ≤ 64/(M j:ℝ))
    (d upper : Fin K → ℝ) (hdpos : ∀j,0 < d j)
    (hF : ∀k∈S.image Prod.snd,‖F (rawHeight D m k)‖ ≤ (1/4:ℝ))
    (Hmetric : ∀z∈S,∀u∈S,‖F (rawHeight D m z.2)-F (rawHeight D m u.2)‖ ≤
      metric*|chartHeightCoordinate m shift (rawHeight D m z.2)-
        chartHeightCoordinate m shift (rawHeight D m u.2)|)
    (hres : ∀z∈S,‖quotientMap P0 hP0 ell hell hell4 hd (F (rawHeight D m z.2))
      (localHorizontalSlope D (2^m) p z.1)-xi z.2‖ ≤ error)
    (hlower : ∀j k,k∈S.image Prod.snd → d j ≤
      (((S.filter (fun z => z.2=k)).image (fun z => angularCell D (2^m) (M j) p z.1)).card:ℝ))
    (hupper : ∀j c,((angularMenu D a m (M j) p S c).card:ℝ) ≤ upper j) :
    let R := modulus (2*metric)
    ∃B⊆S.image Prod.snd,let T := NativeFinitePointCoherence.lift S Prod.snd B
      T.Nonempty ∧ T⊆S ∧
      S.card ≤ (R^(2*K)*(∏j,⌈((4:ℝ)^(4-ell)*upper j)/d j⌉₊))*T.card ∧
      (∀j z u,z∈T → u∈T → physicalCell D a (2^m) (M j) p z.2=
          physicalCell D a (2^m) (M j) p u.2 →
        ‖F (rawHeight D m z.2)-F (rawHeight D m u.2)‖ < 64/(M j:ℝ) ∧
        ‖xi z.2-xi u.2‖ ≤ (129/4:ℝ)*(64/(M j:ℝ))) ∧
      (∀k∈B,T.filter (fun z => z.2=k)=S.filter (fun z => z.2=k)) ∧
      (∀j k,k∈B → d j ≤ (((T.filter (fun z => z.2=k)).image
        (fun z => angularCell D (2^m) (M j) p z.1)).card:ℝ)) ∧
      (∀j z u,z∈T → u∈T → physicalCell D a (2^m) (M j) p z.2 (3:Fin 4)=
          physicalCell D a (2^m) (M j) p u.2 (3:Fin 4) →
        ‖F (rawHeight D m z.2)-F (rawHeight D m u.2)‖ < 64/(M j:ℝ)) := by
  intro R
  obtain ⟨Bmat,hBmat,hSmat,hMatrixCost,hMatrix,hMatrixFiber⟩ :=
    select_actual_raw_matrix_palette D a m p S hS ell hell23 F metric shift hmetric M hM hwindow Hmetric
  let Smat := NativeFinitePointCoherence.lift S Prod.snd Bmat
  have hMatSub : Smat⊆S := filter_subset _ _
  have hMatPoint (k : Index) (hk : k∈Smat.image Prod.snd) : k∈Bmat := by
    obtain ⟨z,hz,hzk⟩ := mem_image.mp hk
    simpa only [hzk] using (mem_filter.mp hz).2
  have hLowerMat : ∀j k,k∈Smat.image Prod.snd → d j ≤
      (((Smat.filter (fun z => z.2=k)).image (fun z => angularCell D (2^m) (M j) p z.1)).card:ℝ) := by
    intro j k hk
    rw [hMatrixFiber k (hMatPoint k hk)]
    exact hlower j k (image_subset_image hMatSub hk)
  have hUpperMat : ∀j c,((angularMenu D a m (M j) p Smat c).card:ℝ) ≤ upper j := by
    intro j c
    have hsub : angularMenu D a m (M j) p Smat c⊆angularMenu D a m (M j) p S c :=
      image_subset_image (filter_subset_filter _ hMatSub)
    exact (Nat.cast_le.mpr (card_le_card hsub)).trans (hupper j c)
  let H := fun j : Fin K => 2*error+48/(M j:ℝ)+8*(64/(M j:ℝ))
  have hH (j : Fin K) : 0 < H j := by
    have hMr : (0:ℝ) < M j := by exact_mod_cast hM j
    dsimp [H]
    positivity
  have hcap (j : Fin K) := actual_local_cell_offset_cap D a m (M j) (hM j) p Smat
    (fun z hz => hp z (hMatSub hz)) P0 hP0 ell hell hell4 hd F xi error (d j) (upper j) he (hdpos j)
    (fun k hk => hF k (image_subset_image hMatSub hk))
    (fun z hz u hu hcell => (hMatrix j z u hz hu (congrFun hcell (3:Fin 4))).le)
    (fun z hz => hres z (hMatSub hz)) (hLowerMat j) (hUpperMat j)
  obtain ⟨B,hB,hFinal,hOffsetCost,hOffset,hOffsetFiber⟩ := select_original_point_fibers Smat hSmat Prod.snd K
    (fun j => physicalCell D a (2^m) (M j) p) (fun j k => label (H j) (xi k))
    (fun j => ((4:ℝ)^(4-ell)*upper j)/d j) hcap
  have hBMat : B⊆Bmat := fun k hk => hMatPoint k (hB hk)
  have hBS : B⊆S.image Prod.snd := hB.trans (image_subset_image hMatSub)
  have hLift : NativeFinitePointCoherence.lift Smat Prod.snd B=
      NativeFinitePointCoherence.lift S Prod.snd B := by
    ext z
    simp only [NativeFinitePointCoherence.lift,mem_filter]
    constructor
    · exact fun hz => ⟨hz.1.1,hz.2⟩
    · exact fun hz => ⟨⟨hz.1,hBMat hz.2⟩,hz.2⟩
  have hFinalMat : NativeFinitePointCoherence.lift S Prod.snd B⊆Smat := by
    intro z hz
    exact mem_filter.mpr ⟨(mem_filter.mp hz).1,hBMat (mem_filter.mp hz).2⟩
  rw [hLift] at hFinal hOffsetCost hOffset hOffsetFiber
  refine ⟨B,hBS,hFinal,filter_subset _ _,?_,?_,fun k hk => lift_fiber S Prod.snd B k hk,?_,?_⟩
  · calc
      S.card ≤ R^(2*K)*Smat.card := hMatrixCost
      _ ≤ R^(2*K)*((∏j,⌈((4:ℝ)^(4-ell)*upper j)/d j⌉₊)*
          (NativeFinitePointCoherence.lift S Prod.snd B).card) := Nat.mul_le_mul_left _ hOffsetCost
      _ = _ := by ring
  · intro j z u hz hu hcell
    have hx := same_offset_norm hell (hH j) (xi z.2) (xi u.2) (hOffset j z u hz hu hcell)
    have hbound : 3*H j ≤ (129/4:ℝ)*(64/(M j:ℝ)) := by
      have hh := hErrorWindow j
      dsimp [H]
      nlinarith only [hh]
    exact ⟨hMatrix j z u (hFinalMat hz) (hFinalMat hu) (congrFun hcell (3:Fin 4)),hx.trans hbound⟩
  · intro j k hk
    rw [lift_fiber S Prod.snd B k hk]
    exact hlower j k (hBS hk)
  · intro j z u hz hu hheight
    exact hMatrix j z u (hFinalMat hz) (hFinalMat hu) hheight

end NativePhysicalLocalOffsetCoherence
