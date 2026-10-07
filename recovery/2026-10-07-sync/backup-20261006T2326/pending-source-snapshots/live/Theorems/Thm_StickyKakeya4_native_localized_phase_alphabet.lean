import Theorems.Thm_StickyKakeya4_original_phase_window_graph

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2200000
noncomputable section
namespace NativeLocalizedPhaseAlphabet
open Classical Finset OriginalPhaseWindowGraph

variable {V Cell Label Menu : Type*} [DecidableEq Cell] [DecidableEq Label]
  [DecidableEq Menu]

/-- Count distinct phase labels in a joint physical/grain cell. -/
def cellPhases (E : Finset V) (cell : V → Cell) (phase : V → Label) (c : Cell) :
    Finset Label := (E.filter (fun v => cell v=c)).image phase

/-- The alphabet contains the selected source labels and only labels of
actual successors. Unrelated states in neighboring cells are not added. -/
def reachable (A : Finset Label) (pick : Label → V) (menus : V → Finset Menu)
    (next : V → Menu → V) (phase : V → Label) : Finset Label :=
  A ∪ (menuGraph A pick menus).image (fun e => phase (next (pick e.1) e.2))

/-- The output records literal source and successor alphabets and the
proved density against their distinct labels. -/
def IsLocalizedGraph (E : Finset V) (cell : V → Cell) (phase : V → Label)
    (neighbors : Cell → Finset Cell) (N : ℕ) (alphabet : Finset Menu)
    (menus : V → Finset Menu) (next : V → Menu → V) (degree : ℝ)
    (c : Cell) (pick : Label → V) : Prop :=
  let A := cellPhases E cell phase c
  let G := menuGraph A pick menus
  let X := reachable A pick menus next phase
  A.Nonempty ∧ X.Nonempty ∧ A⊆X ∧
  (∀a∈A, pick a∈E ∧ cell (pick a)=c ∧ phase (pick a)=a) ∧
  G⊆A ×ˢ alphabet ∧ X.card ≤ N*A.card ∧
  degree*(X.card:ℝ) ≤ (N:ℝ)*(G.card:ℝ) ∧
  X⊆(neighbors c).biUnion (cellPhases E cell phase) ∧
  ∀a j, (a,j)∈G → phase (next (pick a) j)∈X

/-- Localization is performed on the already rich states, with the original
menus retained in full. The denominator is the deduplicated reachable phase
alphabet, not the number of states, old points, or original occurrences. -/
theorem exists_localized_graph
    (E : Finset V) (hE : E.Nonempty) (cell : V → Cell) (phase : V → Label)
    (neighbors : Cell → Finset Cell) (N : ℕ)
    (hself : ∀c, c∈neighbors c) (hN : ∀c, (neighbors c).card ≤ N)
    (alphabet : Finset Menu) (menus : V → Finset Menu) (next : V → Menu → V)
    {degree : ℝ} (hdegree : 0 ≤ degree)
    (hmenu : ∀v∈E, menus v⊆alphabet)
    (hrich : ∀v∈E, degree ≤ ((menus v).card:ℝ))
    (hnext : ∀v∈E, ∀j∈menus v, next v j∈E ∧ cell (next v j)∈neighbors (cell v)) :
    ∃c : Cell, ∃pick : Label → V,
      IsLocalizedGraph E cell phase neighbors N alphabet menus next degree c pick := by
  obtain ⟨c,hc,hmax⟩ := exists_max_image (E.image cell)
    (fun c => (cellPhases E cell phase c).card) (hE.image cell)
  obtain ⟨v,hv,hvc⟩ := mem_image.mp hc
  have hAne : (cellPhases E cell phase c).Nonempty :=
    ⟨phase v,mem_image.mpr ⟨v,mem_filter.mpr ⟨hv,hvc⟩,rfl⟩⟩
  have hmaxAll : ∀d, (cellPhases E cell phase d).card ≤ (cellPhases E cell phase c).card := by
    intro d
    by_cases hd : d∈E.image cell
    · exact hmax d hd
    · have hempty : cellPhases E cell phase d=∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro a ha
        obtain ⟨w,hw,_hwa⟩ := mem_image.mp ha
        exact hd (mem_image.mpr ⟨w,(mem_filter.mp hw).1,(mem_filter.mp hw).2⟩)
      simp only [hempty,card_empty,Nat.zero_le]
  have hex : ∀a∈cellPhases E cell phase c, ∃v∈E, cell v=c ∧ phase v=a := by
    intro a ha
    obtain ⟨w,hw,hwa⟩ := mem_image.mp ha
    exact ⟨w,(mem_filter.mp hw).1,(mem_filter.mp hw).2,hwa⟩
  let pick : Label → V := fun a => if ha : a∈cellPhases E cell phase c then
    (hex a ha).choose else hE.choose
  have hpick : ∀a∈cellPhases E cell phase c,
      pick a∈E ∧ cell (pick a)=c ∧ phase (pick a)=a := by
    intro a ha
    simpa only [pick,dif_pos ha] using (hex a ha).choose_spec
  let A := cellPhases E cell phase c
  let G := menuGraph A pick menus
  let X := reachable A pick menus next phase
  have hAX : A⊆X := subset_union_left
  have hXsub : X⊆(neighbors c).biUnion (cellPhases E cell phase) := by
    intro a ha
    rcases mem_union.mp ha with ha | ha
    · exact mem_biUnion.mpr ⟨c,hself c,ha⟩
    · obtain ⟨e,he,rfl⟩ := mem_image.mp ha
      obtain ⟨ha,hj⟩ := (mem_menuGraph A pick menus e.1 e.2).mp he
      obtain ⟨hpE,hpc,_hpPhase⟩ := hpick e.1 ha
      obtain ⟨hnE,hnc⟩ := hnext (pick e.1) hpE e.2 hj
      rw [hpc] at hnc
      exact mem_biUnion.mpr ⟨cell (next (pick e.1) e.2),hnc,
        mem_image.mpr ⟨next (pick e.1) e.2,mem_filter.mpr ⟨hnE,rfl⟩,rfl⟩⟩
  have hcap : X.card ≤ N*A.card := by
    calc
      X.card ≤ ((neighbors c).biUnion (cellPhases E cell phase)).card := card_le_card hXsub
      _ ≤ ∑d∈neighbors c, (cellPhases E cell phase d).card := card_biUnion_le
      _ ≤ ∑_d∈neighbors c, A.card := sum_le_sum (fun d _hd => hmaxAll d)
      _ = (neighbors c).card*A.card := by simp only [sum_const,smul_eq_mul]
      _ ≤ N*A.card := Nat.mul_le_mul_right _ (hN c)
  have hmass : degree*(A.card:ℝ) ≤ (G.card:ℝ) := by
    rw [show G=menuGraph A pick menus by rfl,menuGraph_card,Nat.cast_sum]
    calc
      _ = ∑_a∈A, degree := by simp [mul_comm]
      _ ≤ _ := sum_le_sum (fun a ha => hrich (pick a) (hpick a ha).1)
  refine ⟨c,pick,hAne,hAne.mono hAX,hAX,hpick,?_,hcap,?_,hXsub,?_⟩
  · intro e he
    obtain ⟨ha,hj⟩ := (mem_menuGraph A pick menus e.1 e.2).mp he
    exact mem_product.mpr ⟨ha,hmenu (pick e.1) (hpick e.1 ha).1 hj⟩
  · have hcR : (X.card:ℝ) ≤ (N:ℝ)*(A.card:ℝ) := by exact_mod_cast hcap
    have h1 := mul_le_mul_of_nonneg_left hcR hdegree
    have h2 := mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg N : (0:ℝ)≤N)
    nlinarith only [h1,h2]
  · intro a j haj
    exact mem_union_right _ (mem_image_of_mem _ haj)

end NativeLocalizedPhaseAlphabet
