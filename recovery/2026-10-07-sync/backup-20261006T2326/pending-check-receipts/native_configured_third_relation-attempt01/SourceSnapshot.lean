import Theorems.Thm_StickyKakeya4_native_actual_configured_residue
import Theorems.Thm_StickyKakeya4_native_joint_uniform_coarse_relations
import Theorems.Thm_StickyKakeya4_native_relative_parent_labels

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeConfiguredThirdRelation
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open CanonicalGridRecoding CanonicalConfiguredE4Bridge NativeReferenceXYGridPoints
open NativeHorizontalGrainSlice NativeTranslatedGrainHeightOverlap
open NativeJointUniformCoarseRelations SelfUniform

/-- The actual final coarse-Y key, including its coarse height. Its values
are fixed after the field freeze; the one extra relation SLOT is reserved
before the native source and the unique third core are selected. -/
def coarseYKey {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤ heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R : ℕ) (k : Index) : ℤ × Grid (normalDim s) :=
  newY (mu m) R (fun t => t/((8*R:ℕ):ℤ)) F Fcfg
    (NativeActualConfiguredPoint.sourceLabel D a m p s P hP hd F k)

lemma coarseYKey_of_frozen {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤ heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R : ℕ) (k : Index)
    (hf : F (translatedHeight D a m k)=Fcfg (translatedHeight D a m k/((8*R:ℕ):ℤ))) :
    coarseYKey D a m p s P hP hd F Fcfg R k=
      (translatedHeight D a m k/((8*R:ℕ):ℤ),
        fun i => (NativeActualConfiguredPoint.sourceLabel D a m p s P hP hd F k).2.2 i/(R:ℤ)) := by
  simp only [coarseYKey,newY,errorMatrix,NativeActualConfiguredPoint.sourceLabel_height]
  rw [hf,sub_self,ExactHeightNoDeletionRecoding.recodedY_zero,coarseGrid_eq_ediv _ _ (mu_pos m)]

/-- The literal final representative phase key paired with the configured
point. It needs no selected fullIndex witness to be fixed before the core. -/
def geometricPairKey {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤ heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R u : ℕ) (z : Fin n × Index) : Parent × E4 :=
  (NativeRelativeParentLabels.relativeLabel D a (2^m) p (2^(u+12)) z.1,
    NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R z.2)

/-- Slot0 compares the final coarse-Y key. The unchanged caller extras
occupy successor indices; completeRelations adds geometric-pair and
configured-point slots through those extras without changing this API. -/
def relations {n d : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤ heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R : ℕ) (extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) :
    Fin (d+1) → (Fin n × Index) → (Fin n × Index) → Prop :=
  Fin.cases (fun x y => coarseYKey D a m p s P hP hd F Fcfg R x.2=
    coarseYKey D a m p s P hP hd F Fcfg R y.2) extra

lemma relations_refl {n d : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤ heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R : ℕ) (extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : ∀j x,extra j x x) : ∀j x,relations D a m p s P hP hd F Fcfg R extra j x x := by
  intro j
  refine Fin.cases (fun _ => rfl) (fun i => H i) j

lemma relations_symm {n d : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤ heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R : ℕ) (extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : ∀j x y,extra j x y → extra j y x) :
    ∀j x y,relations D a m p s P hP hd F Fcfg R extra j x y →
      relations D a m p s P hP hd F Fcfg R extra j y x := by
  intro j
  refine Fin.cases (fun _ _ h => h.symm) (fun i => H i) j

/-- Read the actual third-core caller comparison into exactly the final
coarse-Y fibers. This is the degree comparison of the same T, with no new cut
and no fine-Y or X-cardinality loss. -/
theorem caller_coarseY_uniformity {n d : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤ heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R : ℕ) (extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (T : Finset (Fin n × Index)) (Q : ℕ)
    (H : ∀j x y,x∈T → y∈T →
      degree (fun _ : Fin n × Index => 1) (relations D a m p s P hP hd F Fcfg R extra j) T x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (relations D a m p s P hP hd F Fcfg R extra j) T y) :
    HasUniformFibers T Q (fun z => coarseYKey D a m p s P hP hd F Fcfg R z.2) := by
  intro x hx y hy
  have hh:=H 0 x y hx hy
  change degree (fun _ : Fin n × Index => 1)
      (fun x y => coarseYKey D a m p s P hP hd F Fcfg R x.2=coarseYKey D a m p s P hP hd F Fcfg R y.2) T x ≤
    Q^2*degree (fun _ : Fin n × Index => 1)
      (fun x y => coarseYKey D a m p s P hP hd F Fcfg R x.2=coarseYKey D a m p s P hP hd F Fcfg R y.2) T y at hh
  simpa only [unit_degree_eq_fiber] using hh

/-- The actual combined table has coarse-Y at0, relative-phase/configured
point at1, the literal configured point at2, then all previously reserved
window/caller relations. All three extra slots are counted before D. -/
def completeRelations {n d : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤ heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R u : ℕ) (extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) :
    Fin (d+3) → (Fin n × Index) → (Fin n × Index) → Prop :=
  relations D a m p s P hP hd F Fcfg R
    (Fin.cases (fun x y => geometricPairKey D a m p s P hP hd F Fcfg R u x=
      geometricPairKey D a m p s P hP hd F Fcfg R u y)
      (Fin.cases (fun x y =>
        NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R x.2=
          NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R y.2) extra))

lemma completeRelations_refl {n d : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤ heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R u : ℕ) (extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : ∀j x,extra j x x) : ∀j x,completeRelations D a m p s P hP hd F Fcfg R u extra j x x := by
  exact relations_refl D a m p s P hP hd F Fcfg R _
    (fun j => Fin.cases (fun _ => rfl)
      (fun i => Fin.cases (fun _ => rfl) (fun k => H k) i) j)

lemma completeRelations_symm {n d : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤ heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R u : ℕ) (extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : ∀j x y,extra j x y → extra j y x) :
    ∀j x y,completeRelations D a m p s P hP hd F Fcfg R u extra j x y →
      completeRelations D a m p s P hP hd F Fcfg R u extra j y x := by
  exact relations_symm D a m p s P hP hd F Fcfg R _
    (fun j => Fin.cases (fun _ _ h => h.symm)
      (fun i => Fin.cases (fun _ _ h => h.symm) (fun k => H k) i) j)

/-- The second installed equality reads the ACTUAL geometric pair weights.
Deduplication can use this Q-squared law without confusing edge and pair
cardinalities or invoking a further core. -/
theorem caller_geometricPair_uniformity {n d : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤ heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R u : ℕ) (extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (T : Finset (Fin n × Index)) (Q : ℕ)
    (H : ∀j x y,x∈T → y∈T →
      degree (fun _ : Fin n × Index => 1) (completeRelations D a m p s P hP hd F Fcfg R u extra j) T x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (completeRelations D a m p s P hP hd F Fcfg R u extra j) T y) :
    HasUniformFibers T Q (geometricPairKey D a m p s P hP hd F Fcfg R u) := by
  intro x hx y hy
  have hh:=H (Fin.succ (0:Fin (d+2))) x y hx hy
  change degree (fun _ : Fin n × Index => 1)
      (fun x y => geometricPairKey D a m p s P hP hd F Fcfg R u x=geometricPairKey D a m p s P hP hd F Fcfg R u y) T x ≤
    Q^2*degree (fun _ : Fin n × Index => 1)
      (fun x y => geometricPairKey D a m p s P hP hd F Fcfg R u x=geometricPairKey D a m p s P hP hd F Fcfg R u y) T y at hh
  simpa only [unit_degree_eq_fiber] using hh


/-- The third installed equality is the literal configured-point map used
by geometricPairKey. Together with its pair comparison this supplies the
actual geometric point degrees; no scheduled-grid identification is used. -/
theorem caller_configuredPoint_uniformity {n d : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m : ℕ) (p : Parent)
    (s : Split) (P : Submodule ℝ E4) (hP : P≤ heightKernel)
    (hd : Module.finrank ℝ P=tangentDim s)
    (F Fcfg : ℤ → Matrix (Fin (normalDim s)) (Fin (tangentDim s)) ℝ)
    (R u : ℕ) (extra : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (T : Finset (Fin n × Index)) (Q : ℕ)
    (H : ∀j x y,x∈T → y∈T →
      degree (fun _ : Fin n × Index => 1) (completeRelations D a m p s P hP hd F Fcfg R u extra j) T x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (completeRelations D a m p s P hP hd F Fcfg R u extra j) T y) :
    HasUniformFibers T Q
      (fun z => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R z.2) := by
  intro x hx y hy
  have hh:=H (Fin.succ (Fin.succ (0:Fin (d+1)))) x y hx hy
  change degree (fun _ : Fin n × Index => 1)
      (fun x y => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R x.2=
        NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R y.2) T x ≤
    Q^2*degree (fun _ : Fin n × Index => 1)
      (fun x y => NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R x.2=
        NativeActualConfiguredPoint.point D a m p s P hP hd F Fcfg R y.2) T y at hh
  simpa only [unit_degree_eq_fiber] using hh

end NativeConfiguredThirdRelation
