import Theorems.Thm_StickyKakeya4_native_original_parent_physical_data
import Theorems.Thm_StickyKakeya4_native_coarse_slope_occupancy
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace NativePointAngularParentFibers
open Classical Finset StickyKakeya4 NativeOriginalCellChartGeometry NativeOriginalParentSelection
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts NativeOriginalParentPhysicalData
open scoped BigOperators

/-- The intercept center determined by one literal old cell and one slope cell. -/
def interceptCenter {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (k : Index) (q : Fin 3 → ℤ) (j : Fin 3) : ℝ :=
  (N:ℝ)*(ShearBinFibers.oldCenter (mesh D/4) (chartIndex (shift D a) k)).1 j-
    (ShearBinFibers.oldCenter (mesh D/4) (chartIndex (shift D a) k)).2*(q j:ℝ)

/-- A real error at most 5/2 permits exactly the seven neighboring integer bins. -/
lemma floor_mem_seven (x y : ℝ) (hxy : |x-y|≤(5/2:ℝ)) :
    ⌊x⌋∈Icc (⌊y⌋-3) (⌊y⌋+3) := by
  have ha := abs_le.mp hxy
  have hl := Int.floor_mono (show y-1-1-1≤x by linarith)
  have hu := Int.floor_mono (show x≤y+1+1+1 by linarith)
  rw [Int.floor_sub_one,Int.floor_sub_one,Int.floor_sub_one] at hl
  rw [Int.floor_add_one,Int.floor_add_one,Int.floor_add_one] at hu
  exact mem_Icc.mpr ⟨by omega,by omega⟩

/-- Actual original cell membership bounds intercept freedom inside one
angular cell. The constant is independent of any ancestor occupancy power. -/
theorem incident_intercept_error {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (hscale : (N:ℝ)*D.thickness≤1) (i : Fin n) (k : Index)
    (hk : k∈original i) (q : Fin 3 → ℤ) (hq : (parentLabel D a N i).1=q) (j : Fin 3) :
    |(N:ℝ)*shiftedIntercept (D.line i) (mesh D) (shift D a) j-
      interceptCenter D a N k q j|≤(5/2:ℝ) := by
  let x := ShearBinFibers.oldCenter (mesh D/4) (chartIndex (shift D a) k)
  have hb := original_cell_bounds h original horiginal a ha ((mem_incidences original i k).mpr hk)
  have ht : |x.2|≤1 := hb.1
  have hr : |x.1 j-shiftedIntercept (D.line i) (mesh D) (shift D a) j-
      slope (D.line i) j*x.2|≤12*(mesh D/4) := hb.2 j
  have hf : ⌊(N:ℝ)*slope (D.line i) j⌋=q j := congrFun hq j
  have hl := Int.floor_le ((N:ℝ)*slope (D.line i) j)
  have hu := Int.lt_floor_add_one ((N:ℝ)*slope (D.line i) j)
  rw [hf] at hl hu
  have hs : |(N:ℝ)*slope (D.line i) j-(q j:ℝ)|≤1 :=
    abs_le.mpr ⟨by linarith,by linarith⟩
  have hp := mul_le_mul ht hs (abs_nonneg _) (by norm_num : (0:ℝ)≤1)
  rw [←abs_mul,one_mul] at hp
  have hn : |-(N:ℝ)*(x.1 j-shiftedIntercept (D.line i) (mesh D) (shift D a) j-
      slope (D.line i) j*x.2)|≤(N:ℝ)*(12*(mesh D/4)) := by
    rw [abs_mul,abs_neg,abs_of_nonneg (Nat.cast_nonneg N)]
    exact mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg N)
  change |(N:ℝ)*shiftedIntercept (D.line i) (mesh D) (shift D a) j-
    ((N:ℝ)*x.1 j-x.2*(q j:ℝ))|≤(5/2:ℝ)
  have he : (N:ℝ)*shiftedIntercept (D.line i) (mesh D) (shift D a) j-
      ((N:ℝ)*x.1 j-x.2*(q j:ℝ)) =
      -(N:ℝ)*(x.1 j-shiftedIntercept (D.line i) (mesh D) (shift D a) j-
        slope (D.line i) j*x.2)-x.2*((N:ℝ)*slope (D.line i) j-(q j:ℝ)) := by ring
  rw [he]
  calc
    _ ≤ |-(N:ℝ)*(x.1 j-shiftedIntercept (D.line i) (mesh D) (shift D a) j-
        slope (D.line i) j*x.2)|+|x.2*((N:ℝ)*slope (D.line i) j-(q j:ℝ))| := abs_sub _ _
    _ ≤ (N:ℝ)*(12*(mesh D/4))+1 := add_le_add hn hp
    _ ≤ 5/2 := by dsimp [mesh]; nlinarith

/-- The tube-independent intercept menu at one genuine old cell and slope cell. -/
def interceptMenu {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (k : Index) (q : Fin 3 → ℤ) : Finset (Fin 3 → ℤ) :=
  Fintype.piFinset (fun j => Icc (⌊interceptCenter D a N k q j⌋-3)
    (⌊interceptCenter D a N k q j⌋+3))

lemma interceptMenu_card {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (k : Index) (q : Fin 3 → ℤ) : (interceptMenu D a N k q).card=343 := by
  have hi (j : Fin 3) : (Icc (⌊interceptCenter D a N k q j⌋-3)
      (⌊interceptCenter D a N k q j⌋+3)).card=7 := by
    have hh : ((Icc (⌊interceptCenter D a N k q j⌋-3)
        (⌊interceptCenter D a N k q j⌋+3)).card:ℤ)=7 := by
      rw [Int.card_Icc_of_le _ _ (by omega)]
      omega
    exact_mod_cast hh
  norm_num only [interceptMenu,Fintype.card_piFinset,hi,prod_const,card_univ,Fintype.card_fin]

theorem incident_parent_mem_menu {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (hscale : (N:ℝ)*D.thickness≤1) (i : Fin n) (k : Index)
    (hk : k∈original i) (q : Fin 3 → ℤ) (hq : (parentLabel D a N i).1=q) :
    (parentLabel D a N i).2∈interceptMenu D a N k q := by
  apply Fintype.mem_piFinset.mpr
  intro j
  exact floor_mem_seven _ _ (incident_intercept_error h original horiginal ha N hscale i k hk q hq j)

/-- Actual occupied full parent labels at one literal old E-cell. -/
def pointParents {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (E : Finset (Fin n × Index)) (k : Index) : Finset Parent :=
  (E.filter (fun z => z.2=k)).image (fun z => parentLabel D a N z.1)

/-- Actual angular labels are exactly the slope projection of those occupied parents. -/
def pointAngular {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (E : Finset (Fin n × Index)) (k : Index) : Finset (Fin 3 → ℤ) :=
  (pointParents D a N E k).image Prod.fst

lemma pointAngular_readback {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (N : ℕ)
    (E : Finset (Fin n × Index)) (k : Index) :
    pointAngular D a N E k=(E.filter (fun z => z.2=k)).image
      (fun z => (parentLabel D a N z.1).1) := by
  simp only [pointAngular,pointParents,image_image,Function.comp_def]

/-- Pointwise phase-to-angular fiber capacity343, on any literal retained E.
This uses incidence at k and does not consume a global slope occupancy bound. -/
theorem point_parent_fiber_card_le {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (hscale : (N:ℝ)*D.thickness≤1)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original) (k : Index) (q : Fin 3 → ℤ) :
    ((pointParents D a N E k).filter (fun p => p.1=q)).card≤343 := by
  have hs : (pointParents D a N E k).filter (fun p => p.1=q) ⊆
      (interceptMenu D a N k q).image (fun b => (q,b)) := by
    intro p hp
    obtain ⟨hp,hq⟩ := mem_filter.mp hp
    obtain ⟨⟨i,l⟩,hi,rfl⟩ := mem_image.mp hp
    obtain ⟨hi,hl⟩ := mem_filter.mp hi
    change l=k at hl
    subst l
    exact mem_image.mpr ⟨(parentLabel D a N i).2,
      incident_parent_mem_menu h original horiginal ha N hscale i k
        ((mem_incidences original i k).mp (hE hi)) q hq,Prod.ext hq.symm rfl⟩
  calc
    _ ≤ ((interceptMenu D a N k q).image (fun b => (q,b))).card := card_le_card hs
    _ ≤ (interceptMenu D a N k q).card := card_image_le
    _ = 343 := interceptMenu_card D a N k q

/-- The number of full parents through a literal point is at most343 times
its angular-cell count, independently of delta-power population estimates. -/
theorem pointParents_card_le_angular {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N : ℕ) (hscale : (N:ℝ)*D.thickness≤1)
    (E : Finset (Fin n × Index)) (hE : E⊆incidences original) (k : Index) :
    (pointParents D a N E k).card≤343*(pointAngular D a N E k).card := by
  apply card_le_mul_card_image_of_maps_to (f:=Prod.fst)
  · intro p hp
    exact mem_image_of_mem _ hp
  · intro q _hq
    exact point_parent_fiber_card_le h original horiginal ha N hscale E hE k q

end NativePointAngularParentFibers
