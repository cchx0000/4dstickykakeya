/- UNVERIFIED RECONSTRUCTION, 2026-10-06. Recovered from task context after
an execution-environment reset. This file has not been checked here. -/
import Theorems.Thm_StickyKakeya4_native_window_encoded_capacities
import Theorems.Thm_StickyKakeya4_native_fixed_horizontal_menu
import Theorems.Thm_StickyKakeya4_native_height_window_relations

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1400000
noncomputable section
namespace NativeWindowXYRelationMenu
open NativeHorizontalGrainSlice NativeConditionedPairMenu
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeSquaredGrainQueries NativeWindowEncodedCapacities NativeReferenceXYGridLinear
open NativeJointUniformCoarseRelations NativeSliceCountComparison NativeAnisotropicSliceLabels SelfUniform

/-- Truncate the already prepared horizontal menu at one prepared window. -/
def depth (J m f : ℕ) (j : Fin (J+1)) : ℕ := min f (NativeFixedHorizontalMenu.depths J m j)

lemma depth_first (J m f : ℕ) (hmf : m ≤ f) : depth J m f 0=m := by
  rw [depth,NativeFixedHorizontalMenu.depths_zero,min_eq_right hmf]

lemma depth_last (J m f : ℕ) (hJ : 0 < J) (hm : 6 ≤ m) (hfb : f ≤ phaseDepth m) :
    depth J m f (Fin.last J)=f := by
  rw [depth,NativeFixedHorizontalMenu.depths_last J m hJ hm,min_eq_left hfb]

lemma depth_bounds (J m f : ℕ) (hm : 6 ≤ m) (hmf : m ≤ f) (j : Fin (J+1)) :
    m ≤ depth J m f j ∧ depth J m f j ≤ f := by
  exact ⟨le_min hmf (NativeFixedHorizontalMenu.depths_bounds J m hm j).1,min_le_left _ _⟩

lemma depth_monotone (J m f : ℕ) : Monotone (depth J m f) := by
  intro i j hij
  exact min_le_min_left f (NativeFixedHorizontalMenu.depths_monotone J m hij)

lemma depth_gap (J m f : ℕ) (hJ : 0 < J) (j : Fin J) :
    depth J m f j.succ-depth J m f j.castSucc ≤ (phaseDepth m-m)/J+1 := by
  have hh := NativeFixedHorizontalMenu.depths_gap J m hJ j
  have hm := NativeFixedHorizontalMenu.depths_monotone J m (Fin.castSucc_le_succ j)
  unfold depth
  omega

/-- One equality slot per window/test pair, fixed in number before D.
The field is the single actual pre-third-core field. -/
def relations {n J : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ) (p : Parent)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) :
    Fin ((J+1)*(J+1)) → (Fin n × Index) → (Fin n × Index) → Prop :=
  fun j x y =>
    let ik : Fin (J+1) × Fin (J+1) := finProdFinEquiv.symm j
    let f := NativeFixedHorizontalMenu.depths J m ik.1
    xyPoint D a m ell f (depth J m f ik.2) p P hP hell hell4 hd F x.2=
      xyPoint D a m ell f (depth J m f ik.2) p P hP hell hell4 hd F y.2

lemma relations_refl {n J : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ) (p : Parent)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) :
    ∀j x,relations (J:=J) D a m ell p P hP hell hell4 hd F j x x := fun _ _ => rfl

lemma relations_symm {n J : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ) (p : Parent)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) :
    ∀j x y,relations (J:=J) D a m ell p P hP hell hell4 hd F j x y →
      relations (J:=J) D a m ell p P hP hell hell4 hd F j y x := fun _ _ _ H => H.symm

/-- Read all genuine window point/class uniformities from the SAME third
core's caller slots. The final menu entry supplies each fine point relation. -/
theorem caller_uniformities {n J : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (hm : 6 ≤ m) (hJ : 0 < J) (p : Parent)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (T : Finset (Fin n × Index)) (Q : ℕ)
    (H : ∀j x y,x∈T → y∈T →
      degree (fun _ : Fin n × Index => 1) (relations (J:=J) D a m ell p P hP hell hell4 hd F j) T x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (relations (J:=J) D a m ell p P hP hell hell4 hd F j) T y)
    (i : Fin (J+1)) :
    let f := NativeFixedHorizontalMenu.depths J m i
    HasUniformFibers T Q (fun z => xyPoint D a m ell f f p P hP hell hell4 hd F z.2) ∧
    ∀j,HasUniformFibers T Q (fun z => horizontalCoarsen f (depth J m f j)
      (xyPoint D a m ell f f p P hP hell hell4 hd F z.2)) := by
  intro f
  have hfb : f ≤ phaseDepth m := (NativeFixedHorizontalMenu.depths_bounds J m hm i).2
  have HU (j : Fin (J+1)) : HasUniformFibers T Q
      (fun z => xyPoint D a m ell f (depth J m f j) p P hP hell hell4 hd F z.2) := by
    intro x hx y hy
    have hrel : relations (J:=J) D a m ell p P hP hell hell4 hd F (finProdFinEquiv (i,j))=
        (fun x y : Fin n × Index =>
          xyPoint D a m ell f (depth J m f j) p P hP hell hell4 hd F x.2=
            xyPoint D a m ell f (depth J m f j) p P hP hell hell4 hd F y.2) := by
      funext x y
      simp only [NativeWindowXYRelationMenu.relations,Equiv.symm_apply_apply]
    have hh := H (finProdFinEquiv (i,j)) x y hx hy
    rw [hrel,unit_degree_eq_fiber,unit_degree_eq_fiber] at hh
    exact hh
  constructor
  · simpa only [depth_last J m f hJ hm hfb] using HU (Fin.last J)
  · intro j
    apply uniformity_congr _ _ _ Q (fun z _hz =>
      (xyPoint_coarsen D a m ell f (depth J m f j) (min_le_left _ _) hfb p P hP hell hell4 hd F z.2).symm)
    exact HU j

end NativeWindowXYRelationMenu
