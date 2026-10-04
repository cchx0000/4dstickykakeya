import Theorems.Thm_StickyKakeya4_original_w_successor_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

namespace OriginalWCoreDynamics
open OriginalWWitnessCounts OriginalWCoarseEscapeMenus OriginalWSuccessorSelection
open Classical
noncomputable section

variable {P T H A K : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq H]
  [DecidableEq A] [DecidableEq K]

/-- A core state retains both its exact original terminal height and tube. -/
abbrev Core (S : Finset (H × T)) := {v : H × T // v ∈ S}

omit [DecidableEq T] [DecidableEq H] in
theorem core_nonempty (S : Finset (H × T)) (hS : S.Nonempty) : Nonempty (Core S) := by
  obtain ⟨v,hv⟩ := hS
  exact ⟨⟨v,hv⟩⟩

/-- Every representative is an actual point incident to the state's original
terminal tube, at the state's exact original height. -/
def rep (I : Finset (P × T)) (height : P → H) (S : Finset (H × T))
    (hSV : S ⊆ vertices I height) (v : Core S) : P :=
  Classical.choose (vertex_has_original_terminal_point I height (hSV v.property))

theorem rep_spec (I : Finset (P × T)) (height : P → H) (S : Finset (H × T))
    (hSV : S ⊆ vertices I height) (v : Core S) :
    (rep I height S hSV v,v.val.2) ∈ I ∧ height (rep I height S hSV v)=v.val.1 :=
  Classical.choose_spec (vertex_has_original_terminal_point I height (hSV v.property))

/-- Occupied menus are exactly those of retained original witnesses. -/
def M (I : Finset (P × T)) (height : P → H) (cell : T → K) (angle : T → A)
    (S : Finset (H × T)) (v : Core S) : Finset ((H × H) × (A × A)) :=
  coarseMenus I height cell angle S v.val

/-- The original successor is selected once, with no subspace parameter. -/
def originalNext (I : Finset (P × T)) (height : P → H) (cell : T → K)
    (angle : T → A) (S : Finset (H × T)) :
    (H × T) → ((H × H) × (A × A)) → (H × T) :=
  Classical.choose (exists_deterministic_original_successors I height cell angle S)

theorem originalNext_spec (I : Finset (P × T)) (height : P → H) (cell : T → K)
    (angle : T → A) (S : Finset (H × T)) (v : Core S)
    (g : (H × H) × (A × A)) (hg : g ∈ M I height cell angle S v) :
    originalNext I height cell angle S v.val g ∈ S ∧
    (originalNext I height cell angle S v.val g).1=v.val.1 ∧
    ∃ w ∈ witnesses I height cell,
      endpoint height w.1=v.val ∧
      endpoint height w.2=originalNext I height cell angle S v.val g ∧
      menu height angle w=g :=
  Classical.choose_spec (exists_deterministic_original_successors I height cell angle S)
    v.val v.property g hg

/-- A total finite-state dynamics map. Unoccupied menus fix the state. The
selected successor of an occupied menu is the actual endpoint of an original
witness and remains in the retained core. -/
def next (I : Finset (P × T)) (height : P → H) (cell : T → K) (angle : T → A)
    (S : Finset (H × T)) (v : Core S) (g : (H × H) × (A × A)) : Core S :=
  if hg : g ∈ M I height cell angle S v then
    ⟨originalNext I height cell angle S v.val g,
      (originalNext_spec I height cell angle S v g hg).1⟩
  else v

theorem next_eq_self_of_not_mem (I : Finset (P × T)) (height : P → H)
    (cell : T → K) (angle : T → A) (S : Finset (H × T)) (v : Core S)
    (g : (H × H) × (A × A)) (hg : g ∉ M I height cell angle S v) :
    next I height cell angle S v g=v := by
  simp only [next,dif_neg hg]

theorem next_spec (I : Finset (P × T)) (height : P → H) (cell : T → K)
    (angle : T → A) (S : Finset (H × T)) (v : Core S)
    (g : (H × H) × (A × A)) (hg : g ∈ M I height cell angle S v) :
    (next I height cell angle S v g).val.1=v.val.1 ∧
    ∃ w ∈ witnesses I height cell,
      endpoint height w.1=v.val ∧ endpoint height w.2=(next I height cell angle S v g).val ∧
      menu height angle w=g := by
  simpa only [next,dif_pos hg] using (originalNext_spec I height cell angle S v g hg).2

theorem next_preserves_height (I : Finset (P × T)) (height : P → H)
    (cell : T → K) (angle : T → A) (S : Finset (H × T)) (v : Core S)
    (g : (H × H) × (A × A)) : (next I height cell angle S v g).val.1=v.val.1 := by
  by_cases hg : g ∈ M I height cell angle S v
  · exact (next_spec I height cell angle S v g hg).1
  · rw [next_eq_self_of_not_mem I height cell angle S v g hg]

/-- The angular alphabet is the image of original incident tube labels. -/
def angles (I : Finset (P × T)) (angle : T → A) : Finset A :=
  (TwoTubePathCollisionCount.tubes I).image angle

omit [DecidableEq P] in
theorem angles_nonempty (I : Finset (P × T)) (angle : T → A) (hI : I.Nonempty) :
    (angles I angle).Nonempty := by
  obtain ⟨pt,hpt⟩ := hI
  exact ⟨angle pt.2,Finset.mem_image_of_mem angle (Finset.mem_image_of_mem Prod.snd hpt)⟩

/-- Both height labels and both angular labels of every original witness
belong to the actual finite alphabets. -/
theorem witness_menu_mem_alphabet (I : Finset (P × T)) (height : P → H)
    (cell : T → K) (angle : T → A) (Z : Finset H)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z)
    {w : Path P T × Path P T} (hw : w ∈ witnesses I height cell) :
    menu height angle w ∈ (Z ×ˢ Z) ×ˢ ((angles I angle) ×ˢ (angles I angle)) := by
  obtain ⟨ha,hb,_⟩ := witness_conditions I height cell hw
  have haI := (TwoTubePathCollisionCount.mem_paths I w.1).mp ha
  have hbI := (TwoTubePathCollisionCount.mem_paths I w.2).mp hb
  refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨?_,?_⟩,
    Finset.mem_product.mpr ⟨?_,?_⟩⟩
  · exact hheight _ (Finset.mem_image_of_mem Prod.fst haI.1)
  · exact hheight _ (Finset.mem_image_of_mem Prod.fst haI.2.1)
  · exact Finset.mem_image_of_mem angle (Finset.mem_image_of_mem Prod.snd haI.1)
  · exact Finset.mem_image_of_mem angle (Finset.mem_image_of_mem Prod.snd hbI.1)

theorem M_subset_alphabet (I : Finset (P × T)) (height : P → H) (cell : T → K)
    (angle : T → A) (S : Finset (H × T)) (Z : Finset H)
    (hheight : ∀ p ∈ TwoTubePathCollisionCount.points I, height p ∈ Z) (v : Core S) :
    M I height cell angle S v ⊆ (Z ×ˢ Z) ×ˢ ((angles I angle) ×ˢ (angles I angle)) := by
  intro g hg
  obtain ⟨w,hw,_hl,_hr,hmenu⟩ :=
    coarse_menu_has_original_partner I height cell angle S v.val hg
  rw [← hmenu]
  exact witness_menu_mem_alphabet I height cell angle Z hheight hw

/-- Direct construction of the representative and finite dynamics needed by
growth. Its premises concern original incidences and the retained vertex set;
no supplied successor, representative, or displacement certificate occurs. -/
theorem exists_original_total_core_dynamics (I : Finset (P × T)) (height : P → H)
    (cell : T → K) (angle : T → A) (S : Finset (H × T))
    (hSV : S ⊆ vertices I height) :
    ∃ representative : Core S → P,
      ∃ successor : Core S → ((H × H) × (A × A)) → Core S,
        (∀ v, (representative v,v.val.2) ∈ I ∧ height (representative v)=v.val.1) ∧
        (∀ v g, g ∉ M I height cell angle S v → successor v g=v) ∧
        (∀ v g, (successor v g).val.1=v.val.1) ∧
        ∀ v g, g ∈ M I height cell angle S v →
          ∃ w ∈ witnesses I height cell,
            endpoint height w.1=v.val ∧ endpoint height w.2=(successor v g).val ∧
            menu height angle w=g := by
  exact ⟨rep I height S hSV,next I height cell angle S,
    rep_spec I height S hSV,next_eq_self_of_not_mem I height cell angle S,
    next_preserves_height I height cell angle S,
    fun v g hg => (next_spec I height cell angle S v g hg).2⟩

/-- Minimal interface for applying native displacement to the constructed
representatives and the original witnesses of the constructed successor. -/
theorem exists_original_core_dynamics (I : Finset (P × T)) (height : P → H)
    (cell : T → K) (angle : T → A) (S : Finset (H × T))
    (hSV : S ⊆ vertices I height) :
    ∃ representative : Core S → P,
      ∃ successor : Core S → ((H × H) × (A × A)) → Core S,
        (∀ v, (representative v,v.val.2) ∈ I ∧ height (representative v)=v.val.1) ∧
        ∀ v g, g ∈ coarseMenus I height cell angle S v.val →
          ∃ w ∈ witnesses I height cell,
            endpoint height w.1=v.val ∧ endpoint height w.2=(successor v g).val ∧
            menu height angle w=g := by
  exact ⟨rep I height S hSV,next I height cell angle S,
    rep_spec I height S hSV,
    fun v g hg => (next_spec I height cell angle S v g hg).2⟩

end
end OriginalWCoreDynamics

#print axioms OriginalWCoreDynamics.rep_spec
#print axioms OriginalWCoreDynamics.next_spec
#print axioms OriginalWCoreDynamics.next_preserves_height
#print axioms OriginalWCoreDynamics.angles_nonempty
#print axioms OriginalWCoreDynamics.M_subset_alphabet
#print axioms OriginalWCoreDynamics.exists_original_core_dynamics
#print axioms OriginalWCoreDynamics.exists_original_total_core_dynamics
