import Theorems.Thm_StickyKakeya4_original_w_coarse_escape_menus
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000
namespace OriginalWSuccessorSelection
open OriginalWWitnessCounts OriginalWCoarseEscapeMenus Classical
noncomputable section
variable {P T H A K : Type*} [DecidableEq P] [DecidableEq T] [DecidableEq H]
  [DecidableEq A] [DecidableEq K]
/-- A native terminal vertex has an actual incident original point at exactly
its original height. No nonincident representative is introduced. -/
theorem vertex_has_original_terminal_point (I : Finset (P × T)) (height : P → H)
    {v : H × T} (hv : v ∈ vertices I height) :
    ∃ p : P, (p,v.2) ∈ I ∧ height p=v.1 := by
  obtain ⟨a,ha,hav⟩ := Finset.mem_image.mp hv
  have hi := (TwoTubePathCollisionCount.mem_paths I a).mp ha
  have ht : a.tube₂=v.2 := congrArg Prod.snd hav
  refine ⟨a.point₂,?_,congrArg Prod.fst hav⟩
  rw [← ht]
  exact hi.2.2.2

/-- Choose one genuine original partner for each occupied menu ONCE. This
selection does not depend on the proper subspace used during neighborhood
growth, and it preserves the actual terminal height. -/
theorem exists_deterministic_original_successors (I : Finset (P × T)) (height : P → H)
    (cell : T → K) (angle : T → A) (S : Finset (H × T)) :
    ∃ next : (H × T) → ((H × H) × (A × A)) → (H × T),
      ∀ v ∈ S, ∀ g ∈ coarseMenus I height cell angle S v,
        next v g ∈ S ∧ (next v g).1=v.1 ∧
        ∃ w ∈ witnesses I height cell,
          endpoint height w.1=v ∧ endpoint height w.2=next v g ∧ menu height angle w=g := by
  let pick := fun (v : H × T) (g : (H × H) × (A × A))
      (hg : g ∈ coarseMenus I height cell angle S v) =>
    Classical.choose (coarse_menu_has_original_partner I height cell angle S v hg)
  have hpick : ∀ v g (hg : g ∈ coarseMenus I height cell angle S v),
      pick v g hg ∈ witnesses I height cell ∧
      endpoint height (pick v g hg).1=v ∧ endpoint height (pick v g hg).2 ∈ S ∧
      menu height angle (pick v g hg)=g := by
    intro v g hg
    exact Classical.choose_spec (coarse_menu_has_original_partner I height cell angle S v hg)
  let next := fun v g => if hg : g ∈ coarseMenus I height cell angle S v then
    endpoint height (pick v g hg).2 else v
  refine ⟨next,?_⟩
  intro v _hv g hg
  have hw := hpick v g hg
  have heq : next v g=endpoint height (pick v g hg).2 := by simp only [next,dif_pos hg]
  have hz := (witness_conditions I height cell hw.1).2.2.2.2.1
  refine ⟨by simpa only [heq] using hw.2.2.1,?_,pick v g hg,hw.1,hw.2.1,heq.symm,hw.2.2.2⟩
  rw [heq]
  exact hz.trans (congrArg Prod.fst hw.2.1)

end
end OriginalWSuccessorSelection
