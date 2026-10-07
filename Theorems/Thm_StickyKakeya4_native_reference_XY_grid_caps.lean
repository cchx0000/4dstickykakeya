import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_menus

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 12000000
noncomputable section
namespace NativeReferenceXYGridCaps
open Classical Finset StickyKakeya4 NativeReferenceXYGridLinear NativeReferenceXYGridPoints NativeReferenceXYGridMaps
open NativeReferenceXYGridMenus NativeHorizontalGrainSlice NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeAnisotropicShortRowGeometry
open scoped Matrix.Norms.Elementwise

/-- Actual inverse coarse-grid capacity on every finite reference point set. -/
theorem inverse_capacity {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m ell : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖ ≤ (1/4:ℝ))
    (R : ℕ) (hR : 0 < R) (S : Finset Index) (z : XY ell) :
    (((S.filter (fun k => coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F k)=z)).image
      (fun k => coarseIndex R (pref D a m p k))).card) ≤ 201^3 := by
  let T := S.filter (fun k => coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F k)=z)
  by_cases hT : T.Nonempty
  · obtain ⟨l,hl⟩ := hT
    have hsub : T.image (fun k => coarseIndex R (pref D a m p k))⊆
        columnHalo 100 0 (coarseIndex R (pref D a m p l)) := by
      intro v hv
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hv
      exact inverse_menu h m ell hm p i hi P hP hell hell4 hd F hF R hR k l
        ((mem_filter.mp hk).2.trans (mem_filter.mp hl).2.symm)
    exact (card_le_card hsub).trans_eq (by rw [columnHalo_card]; norm_num)
  · rw [not_nonempty_iff_eq_empty] at hT
    change (T.image _).card ≤ _
    simp only [hT,image_empty,card_empty,Nat.zero_le]

/-- Actual forward coarse-grid capacity on the whole reference point set.
No XY regularity or subset uniformity is an input. -/
theorem forward_capacity {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m ell : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖ ≤ (1/4:ℝ))
    (R : ℕ) (hR : 0 < R) (S : Finset Index) (z : Index) :
    (((S.filter (fun k => coarseIndex R (pref D a m p k)=z)).image
      (fun k => coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F k))).card) ≤ 1201^3 := by
  let T := S.filter (fun k => coarseIndex R (pref D a m p k)=z)
  by_cases hT : T.Nonempty
  · obtain ⟨l,hl⟩ := hT
    have hsub : T.image (fun k => coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F k))⊆
        xyBox ell (coarseXY ell R (pxy D a m ell p P hP hell hell4 hd F l)) 600 := by
      intro v hv
      obtain ⟨k,hk,rfl⟩ := mem_image.mp hv
      exact forward_menu h m ell hm p i hi P hP hell hell4 hd F hF R hR k l
        ((mem_filter.mp hk).2.trans (mem_filter.mp hl).2.symm)
    exact (card_le_card hsub).trans_eq (by rw [xyBox_card ell hell hell4])
  · rw [not_nonempty_iff_eq_empty] at hT
    change (T.image _).card ≤ _
    simp only [hT,image_empty,card_empty,Nat.zero_le]

/-- C0: number of original pref labels in one actual fine XY fiber. -/
theorem fine_inverse_capacity {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m ell : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖ ≤ (1/4:ℝ))
    (S : Finset Index) (z : XY ell) :
    ((S.filter (fun k => pxy D a m ell p P hP hell hell4 hd F k=z)).image (pref D a m p)).card ≤ 201^3 := by
  simpa only [coarseXY_one,coarseIndex_one] using
    inverse_capacity h m ell hm p i hi P hP hell hell4 hd F hF 1 (by norm_num) S z

/-- C1: number of actual XYfine labels in one original pref-fine fiber. -/
theorem fine_forward_capacity {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (m ell : ℕ) (hm : 6 ≤ m) (p : Parent)
    (i : Fin n) (hi : parentLabel D a (2^m) i=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hF : ∀t,‖F t‖ ≤ (1/4:ℝ))
    (S : Finset Index) (z : Index) :
    ((S.filter (fun k => pref D a m p k=z)).image (pxy D a m ell p P hP hell hell4 hd F)).card ≤ 1201^3 := by
  simpa only [coarseXY_one,coarseIndex_one] using
    forward_capacity h m ell hm p i hi P hP hell hell4 hd F hF 1 (by norm_num) S z

/-- Exact incidence/point readback for lifting these geometric caps to the
same full reference incidence set, regardless of edge multiplicity. -/
lemma filtered_image_points {A B C : Type*} [DecidableEq B] [DecidableEq C]
    (I : Finset A) (point : A → Index) (f : Index → B) (g : Index → C) (b : B) :
    ((I.filter (fun z => f (point z)=b)).image (fun z => g (point z)))=
      (((I.image point).filter (fun k => f k=b)).image g) := by
  ext c
  simp only [mem_image,mem_filter]
  constructor
  · rintro ⟨z,⟨hz,hf⟩,hc⟩
    exact ⟨point z,⟨⟨z,hz,rfl⟩,hf⟩,hc⟩
  · rintro ⟨k,⟨⟨z,hz,rfl⟩,hf⟩,hc⟩
    exact ⟨z,⟨hz,hf⟩,hc⟩

theorem lift_incidence_capacity {A B C : Type*} [DecidableEq B] [DecidableEq C]
    (I : Finset A) (point : A → Index) (f : Index → B) (g : Index → C) (K : ℕ)
    (H : ∀S : Finset Index,∀b : B,((S.filter (fun k => f k=b)).image g).card ≤ K) (b : B) :
    ((I.filter (fun z => f (point z)=b)).image (fun z => g (point z))).card ≤ K := by
  rw [filtered_image_points]
  exact H (I.image point) b

end NativeReferenceXYGridCaps
