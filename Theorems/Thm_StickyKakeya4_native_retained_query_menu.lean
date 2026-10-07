import Theorems.Thm_StickyKakeya4_native_actual_retained_rank_configuration
import Theorems.Thm_StickyKakeya4_native_spatial_angular_geometry

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
noncomputable section

namespace NativeRetainedQueryMenu
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeOriginalParentSelection NativeOriginalParentDensityCore NativeJointUniformCoarseRelations
open NativeCoarseShadingUniformity NativeCoarseDirectionThinning SelfUniform

/-- Append a fixed number of actual equality relations. Their maps may be
chosen after the source, while the menu cardinality is chosen before it. -/
def appendEqualities {n d K : ℕ} {B : Type*}
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (maps : Fin K → (Fin n × Index) → B) :
    Fin (d+K) → (Fin n × Index) → (Fin n × Index) → Prop :=
  Fin.addCases Rel (fun i x y => maps i x=maps i y)

lemma appendEqualities_refl {n d K : ℕ} {B : Type*}
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (maps : Fin K → (Fin n × Index) → B) (H : ∀i x,Rel i x x) :
    ∀i x,appendEqualities Rel maps i x x := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j x
    simpa only [appendEqualities,Fin.addCases_left] using H j x
  · intro j x
    simp only [appendEqualities,Fin.addCases_right]

lemma appendEqualities_symm {n d K : ℕ} {B : Type*}
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (maps : Fin K → (Fin n × Index) → B)
    (H : ∀i x y,Rel i x y → Rel i y x) :
    ∀i x y,appendEqualities Rel maps i x y → appendEqualities Rel maps i y x := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro j x y hh
    simpa only [appendEqualities,Fin.addCases_left] using
      H j x y (by simpa only [appendEqualities,Fin.addCases_left] using hh)
  · intro j x y hh
    simp only [appendEqualities,Fin.addCases_right] at hh ⊢
    exact hh.symm

theorem appendEqualities_uniformities {n d K : ℕ} {B : Type*} [DecidableEq B]
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (maps : Fin K → (Fin n × Index) → B) (E : Finset (Fin n × Index)) (Q : ℕ)
    (H : ∀i x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (appendEqualities Rel maps i) E x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (appendEqualities Rel maps i) E y) :
    (∀i x y,x∈E → y∈E → degree (fun _ : Fin n × Index => 1) (Rel i) E x ≤
      Q^2*degree (fun _ : Fin n × Index => 1) (Rel i) E y) ∧
    ∀i,HasUniformFibers E Q (maps i) := by
  constructor
  · intro i x y hx hy
    simpa only [appendEqualities,Fin.addCases_left] using H (Fin.castAdd K i) x y hx hy
  · intro i x hx y hy
    simpa only [appendEqualities,Fin.addCases_right,unit_degree_eq_fiber] using
      H (Fin.natAdd d i) x y hx hy

/-- The fine projected labels retain the globally fixed ORIGINAL R representative. -/
def fineQueryPair {n K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level : ℕ) (queries : Fin K → ℕ × ℕ) (i : Fin K) :
    (Fin n × Index) → Parent × Index :=
  fixedPair D a level (queries i).1 (queries i).1
    (representative h R a (2^(queries i).1))

/-- Spatial coarsening uses the SAME original fine-parent representative. -/
def shortQueryPair {n K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level : ℕ) (queries : Fin K → ℕ × ℕ) (i : Fin K) :
    (Fin n × Index) → Parent × Index :=
  fixedPair D a level (queries i).1 (queries i).2
    (representative h R a (2^(queries i).1))

/-- The raw point is the literal original microcell center in a physical cube
of width 64/2^b. It is never identified with a projected shadow label. -/
def rawQueryPoint {n K : ℕ} (D : FiniteScaleSource n)
    (queries : Fin K → ℕ × ℕ) (i : Fin K) (z : Fin n × Index) : Index :=
  NativeSpatialAngularGeometry.spatialLabel D (2^(queries i).2) z.2

def queryMenu {n d K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level : ℕ) (queries : Fin K → ℕ × ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) :
    Fin (d+K+K+K) → (Fin n × Index) → (Fin n × Index) → Prop :=
  appendEqualities
    (appendEqualities (appendEqualities Rel (fineQueryPair h R a level queries))
      (shortQueryPair h R a level queries)) (rawQueryPoint D queries)

lemma queryMenu_refl {n d K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level : ℕ) (queries : Fin K → ℕ × ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) (H : ∀i x,Rel i x x) :
    ∀i x,queryMenu h R a level queries Rel i x x :=
  appendEqualities_refl _ _ (appendEqualities_refl _ _ (appendEqualities_refl _ _ H))

lemma queryMenu_symm {n d K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level : ℕ) (queries : Fin K → ℕ × ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : ∀i x y,Rel i x y → Rel i y x) :
    ∀i x y,queryMenu h R a level queries Rel i x y → queryMenu h R a level queries Rel i y x :=
  appendEqualities_symm _ _ (appendEqualities_symm _ _ (appendEqualities_symm _ _ H))

/-- Decode the three literal query label maps on the SAME selected E2.
No off-menu uniformity, later cut, or native-source hypothesis on E2 is used. -/
theorem queryMenu_uniformities {n d K : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level : ℕ) (queries : Fin K → ℕ × ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (E2 : Finset (Fin n × Index)) (Q2 : ℕ)
    (H : ∀i x y,x∈E2 → y∈E2 →
      degree (fun _ : Fin n × Index => 1) (queryMenu h R a level queries Rel i) E2 x ≤
        Q2^2*degree (fun _ : Fin n × Index => 1) (queryMenu h R a level queries Rel i) E2 y) :
    (∀i x y,x∈E2 → y∈E2 → degree (fun _ : Fin n × Index => 1) (Rel i) E2 x ≤
      Q2^2*degree (fun _ : Fin n × Index => 1) (Rel i) E2 y) ∧
    (∀i,HasUniformFibers E2 Q2 (fineQueryPair h R a level queries i)) ∧
    (∀i,HasUniformFibers E2 Q2 (shortQueryPair h R a level queries i)) ∧
    ∀i,HasUniformFibers E2 Q2 (rawQueryPoint D queries i) := by
  obtain ⟨Htwo,Hraw⟩ := appendEqualities_uniformities _ (rawQueryPoint D queries) E2 Q2 H
  obtain ⟨Hone,Hshort⟩ := appendEqualities_uniformities _ (shortQueryPair h R a level queries) E2 Q2 Htwo
  obtain ⟨Hold,Hfine⟩ := appendEqualities_uniformities Rel (fineQueryPair h R a level queries) E2 Q2 Hone
  exact ⟨Hold,Hfine,Hshort,Hraw⟩

/-- The independent grain count J is an input, not the master-menu count g.
The selected stop depth is used only after the actual source is known. -/
def grainDepth (J stop : ℕ) (i : Fin (J+1)) : ℕ :=
  min 6 stop+(NativeFixedSizeScaleMenu.schedule J (stop-min 6 stop) i).val

lemma grainDepth_bounds (J stop : ℕ) (i : Fin (J+1)) :
    min 6 stop ≤ grainDepth J stop i ∧ grainDepth J stop i ≤ stop := by
  have hbound := Nat.le_of_lt_succ (NativeFixedSizeScaleMenu.schedule J (stop-min 6 stop) i).isLt
  have hmin : min 6 stop ≤ stop := min_le_right _ _
  dsimp only [grainDepth]
  omega

lemma grainDepth_zero (J stop : ℕ) : grainDepth J stop 0=min 6 stop := by
  simp only [grainDepth,NativeFixedSizeScaleMenu.schedule_zero,Nat.add_zero]

lemma grainDepth_last (J stop : ℕ) (hJ : 0 < J) : grainDepth J stop (Fin.last J)=stop := by
  rw [grainDepth,NativeFixedSizeScaleMenu.schedule_last J (stop-min 6 stop) hJ]
  have hmin : min 6 stop ≤ stop := min_le_right _ _
  omega

lemma grainDepth_mono (J stop : ℕ) (i j : Fin (J+1)) (hij : i ≤ j) :
    grainDepth J stop i ≤ grainDepth J stop j := by
  apply Nat.add_le_add_left
  exact Nat.div_le_div_right (Nat.mul_le_mul_right _ hij)

/-- Adjacent independent grain depths have one controlled rounding loss. -/
lemma grainDepth_succ_gap (J stop : ℕ) (hJ : 0 < J) (i : Fin J) :
    grainDepth J stop i.succ-grainDepth J stop i.castSucc ≤ (stop-min 6 stop)/J+1 ∧
    ((grainDepth J stop i.succ-grainDepth J stop i.castSucc:ℕ):ℝ) ≤
      ((stop-min 6 stop:ℕ):ℝ)/J+1 := by
  let len := stop-min 6 stop
  let lo := i.val*len/J
  let hi := (i.val+1)*len/J
  have hlo : i.val*len < J*(lo+1) := Nat.lt_mul_div_succ (i.val*len) hJ
  have hhi : hi*J ≤ (i.val+1)*len := Nat.div_mul_le_self ((i.val+1)*len) J
  have hmono : lo ≤ hi := Nat.div_le_div_right (Nat.mul_le_mul_right len (by omega))
  have hsub : hi-lo+lo=hi := Nat.sub_add_cancel hmono
  have hdiff : (hi-lo)*J < len+J := by nlinarith
  have hlen : len < J*(len/J+1) := Nat.lt_mul_div_succ len hJ
  have hgap : hi-lo ≤ len/J+1 := by nlinarith
  have hJR : (0:ℝ) < J := by exact_mod_cast hJ
  have hdiffR : ((hi-lo:ℕ):ℝ)*(J:ℝ) < (len:ℝ)+J := by exact_mod_cast hdiff
  have hgapR : ((hi-lo:ℕ):ℝ) ≤ (len:ℝ)/J+1 := by
    calc
      _ ≤ ((len:ℝ)+J)/J := (le_div_iff₀ hJR).mpr hdiffR.le
      _ = _ := by rw [add_div,div_self hJR.ne']
  have he : grainDepth J stop i.succ-grainDepth J stop i.castSucc=hi-lo := by
    dsimp only [grainDepth,NativeFixedSizeScaleMenu.schedule,Fin.val_succ,Fin.val_castSucc]
    dsimp [lo,hi,len]
    omega
  rw [he]
  exact ⟨hgap,hgapR⟩

def grainQueries (J stop : ℕ) (i : Fin (J+1)) : ℕ × ℕ := (stop,grainDepth J stop i)

lemma grainQueries_valid {level : ℕ} (J stop : ℕ) (hstop : stop ≤ level) :
    ∀i : Fin (J+1),(grainQueries J stop i).2 ≤ (grainQueries J stop i).1 ∧
      (grainQueries J stop i).1 ≤ level := by
  intro i
  exact ⟨(grainDepth_bounds J stop i).2,hstop⟩

lemma grainQueries_six_le (J stop : ℕ) (hstop : 6 ≤ stop) (i : Fin (J+1)) :
    6 ≤ (grainQueries J stop i).2 := by
  simpa only [grainQueries,min_eq_left hstop] using (grainDepth_bounds J stop i).1

end NativeRetainedQueryMenu
