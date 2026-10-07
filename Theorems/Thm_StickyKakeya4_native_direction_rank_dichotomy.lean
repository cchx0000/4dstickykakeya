import Theorems.Thm_StickyKakeya4_native_original_parent_physical_data
import Theorems.Thm_StickyKakeya4_actual_slope_source
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Topology.MetricSpace.HausdorffDistance
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000
noncomputable section
namespace NativeDirectionRankDichotomy
open Classical Finset StickyKakeya4 NativeOriginalCellChartGeometry
open NativeCommonCubicalMesh NativeCubicalIncidenceCounts
open scoped BigOperators

variable {α V : Type*} [DecidableEq α] [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Original label mass; weights are never changed during direction selection. -/
def mass {β : Type*} [DecidableEq β] (w : β → ℝ) (A : Finset β) : ℝ := ∑a∈A,w a

def spanOf (v : α → V) (xs : List α) : Submodule ℝ V :=
  Submodule.span ℝ (Set.range (fun i : Fin xs.length => v (xs.get i)))

def nearLabels (A : Finset α) (v : α → V) (r : ℝ) (P : Submodule ℝ V) : Finset α :=
  A.filter (fun a => Metric.infDist (v a) (P:Set V) ≤ r)

def farLabels (A : Finset α) (v : α → V) (r : ℝ) (P : Submodule ℝ V) : Finset α :=
  A.filter (fun a => r < Metric.infDist (v a) (P:Set V))

def children (A : Finset α) (v : α → V) (r : ℝ) (xs : List α) : Finset (List α) :=
  (farLabels A v r (spanOf v xs)).image (fun a => a::xs)

/-- Explicit ordered original-label chains, appended only outside the r-neighborhood
of the span already chosen. Lists store the latest choice first. -/
def chains (A : Finset α) (v : α → V) (r : ℝ) : ℕ → Finset (List α)
  | 0 => {[]}
  | n+1 => (chains A v r n).biUnion (children A v r)

def chainWeight (w : α → ℝ) (xs : List α) : ℝ := (xs.map w).prod

def chainMass (A : Finset α) (v : α → V) (r : ℝ) (w : α → ℝ) (n : ℕ) : ℝ :=
  mass (chainWeight w) (chains A v r n)

/-- Quantitative independence is recorded as actual distances to successive spans. -/
def Separated (v : α → V) (r : ℝ) : List α → Prop
  | [] => True
  | a::xs => Separated v r xs ∧ r < Metric.infDist (v a) (spanOf v xs:Set V)

omit [DecidableEq α] in
lemma spanOf_finrank_le (v : α → V) (xs : List α) :
    Module.finrank ℝ (spanOf v xs) ≤ xs.length := by
  change (Set.range (fun i : Fin xs.length => v (xs.get i))).finrank ℝ  ≤  xs.length
  have hh := finrank_range_le_card (R:=ℝ) (fun i : Fin xs.length => v (xs.get i))
  exact hh.trans_eq (Fintype.card_fin xs.length)

lemma mem_chains_succ (A : Finset α) (v : α → V) (r : ℝ) (n : ℕ) (xs : List α) :
    xs∈chains A v r (n+1) ↔
      ∃ys∈chains A v r n,∃a∈A,r < Metric.infDist (v a) (spanOf v ys:Set V) ∧ a::ys=xs := by
  simp only [chains,children,farLabels,mem_biUnion,mem_image,mem_filter]
  aesop

lemma chains_length (A : Finset α) (v : α → V) (r : ℝ) (n : ℕ)
    (xs : List α) (hxs : xs∈chains A v r n) : xs.length=n := by
  induction n generalizing xs with
  | zero =>
    have he : xs=[] := by simpa only [chains,mem_singleton] using hxs
    simp only [he,List.length_nil]
  | succ n ih =>
    obtain ⟨ys,hys,a,_ha,_hfar,rfl⟩ := (mem_chains_succ A v r n xs).mp hxs
    simp only [List.length_cons,ih ys hys]

lemma chains_labels (A : Finset α) (v : α → V) (r : ℝ) (n : ℕ)
    (xs : List α) (hxs : xs∈chains A v r n) : ∀a∈xs,a∈A := by
  induction n generalizing xs with
  | zero =>
    have he : xs=[] := by simpa only [chains,mem_singleton] using hxs
    simp [he]
  | succ n ih =>
    obtain ⟨ys,hys,a,ha,_hfar,rfl⟩ := (mem_chains_succ A v r n xs).mp hxs
    intro b hb
    rcases List.mem_cons.mp hb with hba|hb
    · simpa only [hba] using ha
    · exact ih ys hys b hb

lemma chains_separated (A : Finset α) (v : α → V) (r : ℝ) (n : ℕ)
    (xs : List α) (hxs : xs∈chains A v r n) : Separated v r xs := by
  induction n generalizing xs with
  | zero =>
    have he : xs=[] := by simpa only [chains,mem_singleton] using hxs
    rw [he]
    trivial
  | succ n ih =>
    obtain ⟨ys,hys,a,_ha,hfar,rfl⟩ := (mem_chains_succ A v r n xs).mp hxs
    exact ⟨ih ys hys,hfar⟩

/- Linear independence is proved from the positive separation certificate. -/
omit [DecidableEq α] in
theorem separated_linearIndependent (v : α → V) (r : ℝ) (hr : 0 < r)
    (xs : List α) (hxs : Separated v r xs) :
    LinearIndependent ℝ (fun i : Fin xs.length => v (xs.get i)) := by
  induction xs with
  | nil =>
    let : IsEmpty (Fin ([]:List α).length) := by
      change IsEmpty (Fin 0)
      infer_instance
    exact linearIndependent_empty_type
  | cons a xs ih =>
    apply linearIndependent_finSucc.mpr
    constructor
    · change LinearIndependent ℝ (fun i : Fin xs.length => v (xs.get i))
      exact ih hxs.1
    · change v a∉spanOf v xs
      intro ha
      have hz : Metric.infDist (v a) (spanOf v xs:Set V)=0 := Metric.infDist_zero_of_mem ha
      have hh := hxs.2
      rw [hz] at hh
      linarith

lemma chains_gram_det_ne_zero (A : Finset α) (v : α → V) (r : ℝ) (hr : 0 < r)
    (n : ℕ) (xs : List α) (hxs : xs∈chains A v r n) :
    (Matrix.gram ℝ (fun i : Fin xs.length => v (xs.get i))).det ≠ 0 :=
  Matrix.det_gram_ne_zero_iff_linearIndependent.mpr
    (separated_linearIndependent v r hr xs (chains_separated A v r n xs hxs))

omit [DecidableEq α] in
lemma chainWeight_nonneg (w : α → ℝ) (hw : ∀a,0 ≤ w a) (xs : List α) :
    0 ≤ chainWeight w xs := by
  apply List.prod_nonneg
  intro x hx
  obtain ⟨a,_ha,rfl⟩ := List.mem_map.mp hx
  exact hw a

lemma children_disjoint (A : Finset α) (v : α → V) (r : ℝ) (xs ys : List α)
    (hne : xs ≠ ys) : Disjoint (children A v r xs) (children A v r ys) := by
  apply disjoint_left.mpr
  intro zs hz hz'
  obtain ⟨a,_ha,rfl⟩ := mem_image.mp hz
  obtain ⟨b,_hb,he⟩ := mem_image.mp hz'
  exact hne (List.cons.inj he).2.symm

lemma children_weight (A : Finset α) (v : α → V) (r : ℝ) (w : α → ℝ) (xs : List α) :
    (∑ys∈children A v r xs,chainWeight w ys)=
      mass w (farLabels A v r (spanOf v xs))*chainWeight w xs := by
  rw [children,sum_image]
  · simp only [chainWeight,List.map_cons,List.prod_cons,mass,sum_mul]
  · intro a _ha b _hb he
    exact (List.cons.inj he).1

lemma chainMass_succ (A : Finset α) (v : α → V) (r : ℝ) (w : α → ℝ) (n : ℕ) :
    chainMass A v r w (n+1)=∑xs∈chains A v r n,
      mass w (farLabels A v r (spanOf v xs))*chainWeight w xs := by
  rw [chainMass,mass,chains,sum_biUnion]
  · exact sum_congr rfl (fun xs _hxs => children_weight A v r w xs)
  · intro xs _hxs ys _hys hne
    exact children_disjoint A v r xs ys hne

lemma far_mass_ge (A : Finset α) (v : α → V) (r : ℝ) (w : α → ℝ)
    (P : Submodule ℝ V) (B : ℝ) (hnear : mass w (nearLabels A v r P) ≤ B) :
    mass w A-B ≤ mass w (farLabels A v r P) := by
  have he : mass w (nearLabels A v r P)+mass w (farLabels A v r P)=mass w A := by
    simpa only [mass,nearLabels,farLabels,not_le] using
      sum_filter_add_sum_filter_not A (fun a => Metric.infDist (v a) (P:Set V) ≤ r) w
  linarith

/-- Failure of lower-rank concentration produces many explicitly separated
original-label tuples, weighted by products of their unchanged original weights. -/
theorem broad_chain_mass [FiniteDimensional ℝ V] {ell : ℕ} (A : Finset α) (v : α → V) (r : ℝ)
    (w : α → ℝ) (hw : ∀a,0 ≤ w a) (B : ℝ) (hB : B ≤ mass w A)
    (H : ∀P : Submodule ℝ V,Module.finrank ℝ P < ell → mass w (nearLabels A v r P) ≤ B)
    (n : ℕ) (hn : n ≤ ell) :
    (mass w A-B)^n ≤ chainMass A v r w n := by
  induction n with
  | zero => simp [chainMass,mass,chains,chainWeight]
  | succ n ih =>
    have hnl : n < ell := Nat.lt_of_succ_le hn
    have hstep : (mass w A-B)*chainMass A v r w n ≤ chainMass A v r w (n+1) := by
      rw [chainMass_succ]
      calc
        _ = ∑xs∈chains A v r n,(mass w A-B)*chainWeight w xs := by
          simp only [chainMass,mass,mul_sum]
        _  ≤  _ := by
          apply sum_le_sum
          intro xs hxs
          have hd : Module.finrank ℝ (spanOf v xs) < ell := by
            calc
              _  ≤  xs.length := spanOf_finrank_le v xs
              _ = n := chains_length A v r n xs hxs
              _  <  ell := hnl
          exact mul_le_mul_of_nonneg_right
            (far_mass_ge A v r w _ B (H _ hd)) (chainWeight_nonneg w hw xs)
    rw [pow_succ']
    exact (mul_le_mul_of_nonneg_left (ih (Nat.le_of_lt hnl)) (sub_nonneg.mpr hB)).trans hstep

/-- A concrete concentration-or-quantitative-independence dichotomy.
The broad branch constructs its tuple family and derives independence. -/
theorem concentration_or_many_chains [FiniteDimensional ℝ V] (A : Finset α) (v : α → V) (r : ℝ) (hr : 0 < r)
    (w : α → ℝ) (hw : ∀a,0 ≤ w a) (ell : ℕ) (B : ℝ) (hB : B ≤ mass w A) :
    (∃P : Submodule ℝ V,Module.finrank ℝ P < ell ∧ B < mass w (nearLabels A v r P)) ∨
    ((mass w A-B)^ell ≤ chainMass A v r w ell ∧
      ∀xs∈chains A v r ell,xs.length=ell ∧ (∀a∈xs,a∈A) ∧ Separated v r xs ∧
        LinearIndependent ℝ (fun i : Fin xs.length => v (xs.get i)) ∧
        (Matrix.gram ℝ (fun i : Fin xs.length => v (xs.get i))).det ≠ 0) := by
  by_cases H : ∀P : Submodule ℝ V,Module.finrank ℝ P < ell → mass w (nearLabels A v r P) ≤ B
  · right
    refine ⟨broad_chain_mass A v r w hw B hB H ell le_rfl,?_⟩
    intro xs hxs
    exact ⟨chains_length A v r ell xs hxs,chains_labels A v r ell xs hxs,
      chains_separated A v r ell xs hxs,
      separated_linearIndependent v r hr xs (chains_separated A v r ell xs hxs),
      chains_gram_det_ne_zero A v r hr ell xs hxs⟩
  · left
    push Not at H
    exact H

lemma near_mass_mono (A J : Finset α) (hJA : J⊆A) (v : α → V) (r : ℝ)
    (w : α → ℝ) (hw : ∀a,0 ≤ w a) (P : Submodule ℝ V) :
    mass w (nearLabels J v r P) ≤ mass w (nearLabels A v r P) := by
  apply sum_le_sum_of_subset_of_nonneg (filter_subset_filter _ hJA)
  intro a _ha _hnot
  exact hw a

/-- A previously chosen literal retained label family inherits the original
concentration budget. This theorem performs no new thinning of those labels. -/
theorem retained_broad_chain_mass [FiniteDimensional ℝ V] {ell : ℕ} (A J : Finset α) (hJA : J⊆A)
    (v : α → V) (r : ℝ) (w : α → ℝ) (hw : ∀a,0 ≤ w a) (B : ℝ) (hB : B ≤ mass w J)
    (H : ∀P : Submodule ℝ V,Module.finrank ℝ P < ell → mass w (nearLabels A v r P) ≤ B) :
    (mass w J-B)^ell ≤ chainMass J v r w ell := by
  apply broad_chain_mass J v r w hw B hB _ ell le_rfl
  intro P hP
  exact (near_mass_mono A J hJA v r w hw P).trans (H P hP)

/-- The graph vector used in WZ's tuple condition, constructed from the
actual original marked line: its last coordinate is literally one. -/
def slopeVector {n : ℕ} (D : FiniteScaleSource n) (i : Fin n) : E4 :=
  ActualSlopeSource.heightPoint (WithLp.toLp 2 (slope (D.line i))) 1

lemma slopeVector_last {n : ℕ} (D : FiniteScaleSource n) (i : Fin n) :
    slopeVector D i (3:Fin 4)=1 := rfl

/-- Original incident pairs at one literal old cell, with original weights,
are a direct input to the rank dichotomy. No Gram or independence hypothesis
and no pointwise phase-to-angular inference is used. -/
theorem incident_slope_dichotomy {n : ℕ} (D : FiniteScaleSource n)
    (E : Finset (Fin n × Index)) (k : Index) (w : (Fin n × Index) → ℝ)
    (hw : ∀z,0 ≤ w z) (ell : ℕ) (r : ℝ) (hr : 0 < r) (B : ℝ)
    (hB : B ≤ mass w (E.filter (fun z => z.2=k))) :
    let A := E.filter (fun z => z.2=k)
    let v := fun z : Fin n × Index => slopeVector D z.1
    (∃P : Submodule ℝ E4,Module.finrank ℝ P < ell ∧ B < mass w (nearLabels A v r P)) ∨
    ((mass w A-B)^ell ≤ chainMass A v r w ell ∧
      ∀xs∈chains A v r ell,xs.length=ell ∧ (∀z∈xs,z∈A) ∧ Separated v r xs ∧
        LinearIndependent ℝ (fun i : Fin xs.length => v (xs.get i)) ∧
        (Matrix.gram ℝ (fun i : Fin xs.length => v (xs.get i))).det ≠ 0) :=
  concentration_or_many_chains _ _ r hr w hw ell B hB

end NativeDirectionRankDichotomy
