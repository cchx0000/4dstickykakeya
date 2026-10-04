import Theorems.Thm_StickyKakeya4_original_core_menu_density
import Theorems.Thm_StickyKakeya4_original_phase_grid_population

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalPhaseWindowGraph
open Classical
open scoped BigOperators

abbrev GrainLabel := ℤ × ℤ

def grainCell (width : ℝ) (p : ℝ × ℝ) : GrainLabel :=
  (⌊p.1/width⌋,⌊p.2/width⌋)

def neighborCells (k : GrainLabel) : Finset GrainLabel :=
  Finset.Icc (k.1-1) (k.1+1) ×ˢ Finset.Icc (k.2-1) (k.2+1)

lemma neighborCells_card (k : GrainLabel) : (neighborCells k).card=9 := by
  have hf (n : ℤ) : (Finset.Icc (n-1) (n+1)).card=3 := by
    have hh : ((Finset.Icc (n-1) (n+1)).card : ℤ)=3 := by
      rw [Int.card_Icc_of_le _ _ (by omega)]
      omega
    exact_mod_cast hh
  simp only [neighborCells,Finset.card_product,hf]

lemma self_mem_neighborCells (k : GrainLabel) : k ∈ neighborCells k := by
  simp only [neighborCells,Finset.mem_product,Finset.mem_Icc]
  omega

lemma grainCell_neighbor {width : ℝ} (hwidth : 0 < width) (p q : ℝ × ℝ)
    (hpq : ‖p-q‖ ≤ width) : grainCell width p ∈ neighborCells (grainCell width q) := by
  have hf {a b : ℝ} (hab : |a-b| ≤ width) :
      ⌊b/width⌋-1 ≤ ⌊a/width⌋ ∧ ⌊a/width⌋ ≤ ⌊b/width⌋+1 := by
    obtain ⟨hl,hu⟩ := abs_le.mp hab
    have hl' : b/width-1 ≤ a/width := by
      have hh := div_le_div_of_nonneg_right (show b-width ≤ a by linarith) hwidth.le
      simpa only [sub_div,div_self hwidth.ne'] using hh
    have hu' : a/width ≤ b/width+1 := by
      have hh := div_le_div_of_nonneg_right (show a ≤ b+width by linarith) hwidth.le
      simpa only [add_div,div_self hwidth.ne'] using hh
    exact ⟨by simpa only [Int.floor_sub_one] using Int.floor_mono hl',
      by simpa only [Int.floor_add_one] using Int.floor_mono hu'⟩
  have hh := max_le_iff.mp hpq
  exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr (hf hh.1),Finset.mem_Icc.mpr (hf hh.2)⟩

variable {V L J : Type*} [DecidableEq L] [DecidableEq J]

/-- Distinct phase labels in one physical grain cell, not the number of
 states or original points carrying those labels. -/
def occupied (E : Finset V) (grain : V → GrainLabel) (phase : V → L)
    (k : GrainLabel) : Finset L := (E.filter (fun v => grain v=k)).image phase

def expanded (E : Finset V) (grain : V → GrainLabel) (phase : V → L)
    (k : GrainLabel) : Finset L := (neighborCells k).biUnion (occupied E grain phase)

def menuGraph (A : Finset L) (pick : L → V) (menus : V → Finset J) : Finset (L × J) :=
  A.biUnion fun a => {a} ×ˢ menus (pick a)

lemma mem_menuGraph (A : Finset L) (pick : L → V) (menus : V → Finset J) (a : L) (j : J) :
    (a,j) ∈ menuGraph A pick menus ↔ a ∈ A ∧ j ∈ menus (pick a) := by
  simp only [menuGraph,Finset.mem_biUnion,Finset.mem_product,Finset.mem_singleton]
  aesop

lemma menuGraph_card (A : Finset L) (pick : L → V) (menus : V → Finset J) :
    (menuGraph A pick menus).card=∑ a ∈ A, (menus (pick a)).card := by
  unfold menuGraph
  rw [Finset.card_biUnion]
  · simp only [Finset.card_product,Finset.card_singleton,one_mul]
  · intro a _ha b _hb hab
    apply Finset.disjoint_left.mpr
    intro aj ha hb
    have h₁ := Finset.mem_singleton.mp (Finset.mem_product.mp ha).1
    have h₂ := Finset.mem_singleton.mp (Finset.mem_product.mp hb).1
    exact hab (h₁.symm.trans h₂)

/-- The maximizer is chosen from actual occupied grain cells. Every other
 cell's occupied phase count, including empty cells, is bounded by it. -/
theorem exists_maximal_occupied (E : Finset V) (hE : E.Nonempty)
    (grain : V → GrainLabel) (phase : V → L) :
    ∃ k, (occupied E grain phase k).Nonempty ∧
      ∀ q, (occupied E grain phase q).card ≤ (occupied E grain phase k).card := by
  obtain ⟨k,hk,hmax⟩ := Finset.exists_max_image (E.image grain)
    (fun q => (occupied E grain phase q).card) (hE.image grain)
  obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hk
  refine ⟨grain v,⟨phase v,Finset.mem_image.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,rfl⟩,rfl⟩⟩,?_⟩
  intro q
  by_cases hq : q ∈ E.image grain
  · exact hmax q hq
  · have hz : occupied E grain phase q=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      obtain ⟨w,hw,_⟩ := Finset.mem_image.mp ha
      obtain ⟨hwE,hwq⟩ := Finset.mem_filter.mp hw
      exact hq (Finset.mem_image.mpr ⟨w,hwE,hwq⟩)
    simp only [hz,Finset.card_empty,Nat.zero_le]

/-- Verified data of an occupied-window graph. Every set and edge remains
 the literal finite construction above. This is an output predicate. -/
def IsWindowGraph (E : Finset V) (grain : V → GrainLabel) (phase : V → L)
    (alphabet : Finset J) (menus : V → Finset J) (next : V → J → V)
    (degree : ℝ) (k : GrainLabel) (pick : L → V) : Prop :=
  (occupied E grain phase k).Nonempty ∧
  occupied E grain phase k ⊆ expanded E grain phase k ∧
  (expanded E grain phase k).card ≤ 9*(occupied E grain phase k).card ∧
  (∀ a ∈ occupied E grain phase k,
    pick a ∈ E ∧ grain (pick a)=k ∧ phase (pick a)=a) ∧
  menuGraph (occupied E grain phase k) pick menus ⊆
    (occupied E grain phase k) ×ˢ alphabet ∧
  degree*((expanded E grain phase k).card : ℝ) ≤
    9*((menuGraph (occupied E grain phase k) pick menus).card : ℝ) ∧
  ∀ a j, (a,j) ∈ menuGraph (occupied E grain phase k) pick menus →
    phase (next (pick a) j) ∈ expanded E grain phase k

/-- Occupied labels, deterministic original representatives, and retained
 menus produce the graph. The density loss is exactly the nine neighboring
 grain cells and is proved from cardinalities, never supplied as a premise. -/
theorem exists_maximal_window_graph
    (E : Finset V) (hE : E.Nonempty) (grain : V → GrainLabel) (phase : V → L)
    (alphabet : Finset J) (menus : V → Finset J) (next : V → J → V)
    {degree : ℝ} (hdegree : 0 ≤ degree)
    (hmenu : ∀ v ∈ E, menus v ⊆ alphabet)
    (hrich : ∀ v ∈ E, degree ≤ ((menus v).card : ℝ))
    (hnext : ∀ v ∈ E, ∀ j ∈ menus v,
      next v j ∈ E ∧ grain (next v j) ∈ neighborCells (grain v)) :
    ∃ k, ∃ pick : L → V,
      IsWindowGraph E grain phase alphabet menus next degree k pick := by
  obtain ⟨k,hk,hmax⟩ := exists_maximal_occupied E hE grain phase
  have hex : ∀ a ∈ occupied E grain phase k, ∃ v ∈ E, grain v=k ∧ phase v=a := by
    intro a ha
    obtain ⟨v,hv,hva⟩ := Finset.mem_image.mp ha
    obtain ⟨hvE,hvk⟩ := Finset.mem_filter.mp hv
    exact ⟨v,hvE,hvk,hva⟩
  let pick : L → V := fun a => if ha : a ∈ occupied E grain phase k then
    Classical.choose (hex a ha) else Classical.choose hE
  have hpick : ∀ a ∈ occupied E grain phase k,
      pick a ∈ E ∧ grain (pick a)=k ∧ phase (pick a)=a := by
    intro a ha
    simpa only [pick,dif_pos ha] using Classical.choose_spec (hex a ha)
  have hsub : occupied E grain phase k ⊆ expanded E grain phase k := by
    intro a ha
    exact Finset.mem_biUnion.mpr ⟨k,self_mem_neighborCells k,ha⟩
  have hcap : (expanded E grain phase k).card ≤ 9*(occupied E grain phase k).card := by
    calc
      _ ≤ ∑ q ∈ neighborCells k, (occupied E grain phase q).card := Finset.card_biUnion_le
      _ ≤ ∑ _q ∈ neighborCells k, (occupied E grain phase k).card :=
        Finset.sum_le_sum (fun q _hq => hmax q)
      _ = _ := by simp only [Finset.sum_const,smul_eq_mul,neighborCells_card]
  have hgraph : degree*((occupied E grain phase k).card : ℝ) ≤
      ((menuGraph (occupied E grain phase k) pick menus).card : ℝ) := by
    rw [menuGraph_card,Nat.cast_sum]
    calc
      _ = ∑ _a ∈ occupied E grain phase k, degree := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun a ha => hrich (pick a) (hpick a ha).1)
  refine ⟨k,pick,hk,hsub,hcap,hpick,?_,?_,?_⟩
  · intro aj haj
    have hh := (mem_menuGraph _ _ _ aj.1 aj.2).mp haj
    exact Finset.mem_product.mpr ⟨hh.1,hmenu _ (hpick _ hh.1).1 hh.2⟩
  · have hcap' : ((expanded E grain phase k).card : ℝ) ≤
        9*((occupied E grain phase k).card : ℝ) := by exact_mod_cast hcap
    have hh := mul_le_mul_of_nonneg_left hcap' hdegree
    nlinarith
  · intro a j haj
    obtain ⟨ha,hj⟩ := (mem_menuGraph _ _ _ a j).mp haj
    obtain ⟨hvE,hvk,_hva⟩ := hpick a ha
    obtain ⟨hnE,hnk⟩ := hnext (pick a) hvE j hj
    rw [hvk] at hnk
    exact Finset.mem_biUnion.mpr ⟨grain (next (pick a) j),hnk,
      Finset.mem_image.mpr ⟨next (pick a) j,Finset.mem_filter.mpr ⟨hnE,rfl⟩,rfl⟩⟩

end OriginalPhaseWindowGraph
