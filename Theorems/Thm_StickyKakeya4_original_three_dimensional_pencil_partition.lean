import Theorems.Thm_StickyKakeya4_original_three_dimensional_pencil_overlap
import Mathlib.Combinatorics.Enumerative.DoubleCounting

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2800000

noncomputable section
open scoped BigOperators
namespace OriginalThreeDimensionalPencilPartition
open Classical OriginalThreeDimensionalBandGeometry OriginalThreeDimensionalHeavySlabs
open OriginalThreeDimensionalTubeSlab OriginalThreeDimensionalTubeParameters
open OriginalThreeDimensionalPencilGeometry OriginalThreeDimensionalPencilOverlap

def pencilCell (rho : ℝ) (stem : Pair3) (e : Equiv.Perm (Fin 3)) (z : Pair3) : Bool×ℤ :=
  (pencilChart stem z e,⌊pencilScalar stem z e/rho⌋)

def pencilGroup (B : Finset Pair3) (rho : ℝ) (stem : Pair3)
    (e : Equiv.Perm (Fin 3)) (v : Pair3) : Finset Pair3 :=
  B.filter (fun z => pencilCell rho stem e z=pencilCell rho stem e v)

def pencilShadeUnion (B : Finset Pair3) (rho : ℝ) (stem : Pair3)
    (e : Equiv.Perm (Fin 3)) (Y : Pair3 → Finset Point3) (v : Pair3) : Finset Point3 :=
  (pencilGroup B rho stem e v).biUnion Y

/-- Actual representatives of occupied scalar-chart cells retain every
whole original brush-tube fiber and partition its cardinality exactly. -/
theorem exists_original_pencil_representatives (B : Finset Pair3) (rho : ℝ)
    (stem : Pair3) (e : Equiv.Perm (Fin 3)) :
    ∃ R : Finset Pair3, R⊆B ∧ Set.InjOn (pencilCell rho stem e) R ∧
      R.image (pencilCell rho stem e)=B.image (pencilCell rho stem e) ∧
      B.card=∑ v∈R, (pencilGroup B rho stem e v).card ∧
      ∀ z∈B, ∃ v∈R, z∈pencilGroup B rho stem e v := by
  let f := pencilCell rho stem e
  obtain ⟨R,hRB,hinj,himage⟩ := Finset.exists_subset_injOn_image_eq_of_surjOn
    (↑B : Set Pair3) (B.image f) (by
      intro c hc
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hc
      exact ⟨z,hz,rfl⟩)
  refine ⟨R,hRB,hinj,himage,?_,?_⟩
  · rw [Finset.card_eq_sum_card_image f B,← himage]
    exact Finset.sum_image (fun u hu v hv heq => hinj hu hv heq)
  · intro z hz
    have hzcell : f z∈R.image f := by rw [himage]; exact Finset.mem_image.mpr ⟨z,hz,rfl⟩
    obtain ⟨v,hv,hvz⟩ := Finset.mem_image.mp hzcell
    exact ⟨v,hv,Finset.mem_filter.mpr ⟨hz,hvz.symm⟩⟩

/-- Every full original bounded tube population in a plane group belongs
to its actual representative's exact 100rho band. The common point is
an actual original point, and the plane is obtained from original slopes. -/
theorem original_pencil_group_full_population (P : Finset Point3) (B : Finset Pair3)
    (rho : ℝ) (stem v : Pair3) (e : Equiv.Perm (Fin 3)) (hrho : 0 < rho)
    (hs : stem.2 (e 2)-stem.1 (e 2) ≠ 0)
    (hsmax : ∀ j, |stem.2 j-stem.1 j| ≤ |stem.2 (e 2)-stem.1 (e 2)|)
    (hsbox : ∀ j, |stem.1 j| ≤ 1) (hbox : ∀ x∈P, ∀ j, |x j| ≤ 1)
    (hne : ∀ z∈B, z.2 (e 2)-z.1 (e 2) ≠ 0)
    (hmax : ∀ z∈B, ∀ j, |z.2 j-z.1 j| ≤ |z.2 (e 2)-z.1 (e 2)|)
    (htrans : ∀ z∈B, ∃ j, slope z (e 2) j ≠ slope stem (e 2) j)
    (hmeet : ∀ z∈B, ∃ p∈P, p∈physicalTube3 stem.1 stem.2 (8*rho) ∧
      p∈physicalTube3 z.1 z.2 (8*rho)) :
    ∀ z∈pencilGroup B rho stem e v, ∀ x∈physicalPairTube3 P (8*rho) z,
      |pencilValue stem e (pencilChart stem v e) (pencilScalar stem v e) x| ≤ 100*rho := by
  intro z hz x hx
  obtain ⟨hzB,hcell⟩ := Finset.mem_filter.mp hz
  obtain ⟨hxP,hxt⟩ := Finset.mem_filter.mp hx
  obtain ⟨p,_hp,hps,hpz⟩ := hmeet z hzB
  have hzt := original_transverse_coordinates stem z e hs (hne z hzB) (htrans z hzB)
  have hb := original_pencil_band_support stem z e rho p x hs (hne z hzB)
    hsmax (hmax z hzB) hzt hps hpz hxt
  have hc := congrArg Prod.fst hcell
  have ht := congrArg Prod.snd hcell
  change pencilChart stem z e=pencilChart stem v e at hc
  change ⌊pencilScalar stem z e/rho⌋=⌊pencilScalar stem v e/rho⌋ at ht
  rw [hc] at hb
  exact original_pencil_bin_transfer stem e (pencilChart stem v e)
    (pencilScalar stem z e) (pencilScalar stem v e) rho x hrho hs hsmax hsbox
    (hbox x hxP) ht hb

/-- Sum the actual group-union cardinalities using the proved geometric
pencil overlap. The shadings remain subsets of the same original source. -/
theorem original_pencil_shade_union_budget (P X : Finset Point3) (B R : Finset Pair3)
    (Y : Pair3 → Finset Point3) (rho s : ℝ) (stem : Pair3) (e : Equiv.Perm (Fin 3))
    (hrho : 0 < rho) (hs : 0 < s) (hs1 : s ≤ 1)
    (hR : R⊆B) (hinj : Set.InjOn (pencilCell rho stem e) R)
    (_hXP : X⊆P) (hout : ∀ x∈X, x∉physicalTube3 stem.1 stem.2 s)
    (hY : ∀ z∈B, Y z⊆X)
    (hYtube : ∀ z∈B, Y z⊆physicalPairTube3 P (8*rho) z)
    (hsne : stem.2 (e 2)-stem.1 (e 2) ≠ 0)
    (hsmax : ∀ j, |stem.2 j-stem.1 j| ≤ |stem.2 (e 2)-stem.1 (e 2)|)
    (hsbox : ∀ j, |stem.1 j| ≤ 1) (hbox : ∀ x∈P, ∀ j, |x j| ≤ 1)
    (hne : ∀ z∈B, z.2 (e 2)-z.1 (e 2) ≠ 0)
    (hmax : ∀ z∈B, ∀ j, |z.2 j-z.1 j| ≤ |z.2 (e 2)-z.1 (e 2)|)
    (htrans : ∀ z∈B, ∃ j, slope z (e 2) j ≠ slope stem (e 2) j)
    (hmeet : ∀ z∈B, ∃ p∈P, p∈physicalTube3 stem.1 stem.2 (8*rho) ∧
      p∈physicalTube3 z.1 z.2 (8*rho)) :
    (∑ v∈R, ((pencilShadeUnion B rho stem e Y v).card : ℝ)) ≤ 4000/s*X.card := by
  let U := pencilShadeUnion B rho stem e Y
  have hUX (v : Pair3) : U v⊆X := by
    intro x hx
    obtain ⟨z,hz,hxY⟩ := Finset.mem_biUnion.mp hx
    exact hY z (Finset.mem_filter.mp hz).1 hxY
  have hband (v : Pair3) (x : Point3) (hx : x∈U v) :
      |pencilValue stem e (pencilChart stem v e) (pencilScalar stem v e) x| ≤ 100*rho := by
    obtain ⟨z,hz,hxY⟩ := Finset.mem_biUnion.mp hx
    exact original_pencil_group_full_population P B rho stem v e hrho hsne hsmax hsbox
      hbox hne hmax htrans hmeet z hz x (hYtube z (Finset.mem_filter.mp hz).1 hxY)
  have ht : ∀ v∈R, |pencilScalar stem v e| ≤ 1 := by
    intro v hv
    exact (original_pencil_scalar_spec stem v e
      (original_transverse_coordinates stem v e hsne (hne v (hR hv)) (htrans v (hR hv)))).1
  have hpoint (x : Point3) (hx : x∈X) :
      ((R.filter (fun v => x∈U v)).card : ℝ) ≤ 4000/s := by
    have hsub : R.filter (fun v => x∈U v)⊆R.filter (fun v =>
        |pencilValue stem e (pencilChart stem v e) (pencilScalar stem v e) x| ≤ 100*rho) := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hv).1,hband v x (Finset.mem_filter.mp hv).2⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
      (original_pencil_band_overlap R (fun v => pencilChart stem v e)
        (fun v => pencilScalar stem v e) stem e x rho s hrho hs hs1 hsne
        (hout x hx) hinj ht)
  have hsum : (∑ v∈R, ((U v).card : ℝ))=
      ∑ x∈X, ((R.filter (fun v => x∈U v)).card : ℝ) := by
    have hc := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s:=R) (t:=X) (fun v x => x∈U v)
    have hu (v : Pair3) : X.bipartiteAbove (fun v x => x∈U v) v=U v := by
      ext x
      simp only [Finset.mem_bipartiteAbove]
      exact ⟨And.right,fun hx => ⟨hUX v hx,hx⟩⟩
    simp only [hu,Finset.bipartiteBelow] at hc
    exact_mod_cast hc
  change (∑ v∈R, ((U v).card : ℝ)) ≤ 4000/s*X.card
  rw [hsum]
  calc
    _ ≤ ∑ _x∈X, (4000/s) := Finset.sum_le_sum hpoint
    _ = _ := by simp [mul_comm]

end OriginalThreeDimensionalPencilPartition
