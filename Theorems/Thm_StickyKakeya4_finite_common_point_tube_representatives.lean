import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

noncomputable section
namespace FiniteCommonPointTubeRepresentatives

def compatible {T P : Type*} [DecidableEq P]
    (S : T → Finset P) (distance : P → P → ℝ) (rho : ℝ) (i j : T) : Prop :=
  ∀ p∈S i∩S j, ∀ q∈S i∩S j, distance p q≤rho

theorem compatible_symm {T P : Type*} [DecidableEq P]
    (S : T → Finset P) (distance : P → P → ℝ) (rho : ℝ) (i j : T) :
    compatible S distance rho i j ↔ compatible S distance rho j i := by
  simp only [compatible,Finset.inter_comm]

/-- Choose finite ORIGINAL tube representatives. Every omitted candidate
has two actual common source points, farther than rho, in a representative.
No filled continuous intersection or compactness choice is used. -/
theorem exists_original_representatives
    {T P : Type*} [DecidableEq T] [DecidableEq P]
    (Candidates : Finset T) (S : T → Finset P)
    (distance : P → P → ℝ) (rho : ℝ) :
    ∃ F : Finset T, F⊆Candidates ∧
      ((F:Set T).Pairwise (compatible S distance rho)) ∧
      ∀ i∈Candidates, i∉F → ∃ j∈F, ∃ p∈S i∩S j, ∃ q∈S i∩S j,
        rho<distance p q := by
  classical
  let Family := Candidates.powerset.filter
    (fun F : Finset T => (F:Set T).Pairwise (compatible S distance rho))
  have hFamily : Family.Nonempty := by
    refine ⟨∅,Finset.mem_filter.mpr ⟨Finset.empty_mem_powerset _,?_⟩⟩
    simp
  obtain ⟨F,hFmax⟩ := Family.exists_maximal hFamily
  simp only [Family,Finset.mem_filter,Finset.mem_powerset] at hFmax
  obtain ⟨hFC,hFpair⟩ := hFmax.1
  refine ⟨F,hFC,hFpair,?_⟩
  intro i hi hnotF
  have hbad : ¬∀ j∈F, compatible S distance rho i j := by
    intro hall
    have hInsert : ((insert i F : Finset T):Set T).Pairwise (compatible S distance rho) := by
      intro a ha b hb hab
      simp only [Finset.coe_insert,Set.mem_insert_iff,Finset.mem_coe] at ha hb
      rcases ha with rfl|ha
      · rcases hb with rfl|hb
        · exact (hab rfl).elim
        · exact hall b hb
      · rcases hb with rfl|hb
        · exact (compatible_symm S distance rho b a).mp (hall a ha)
        · exact hFpair ha hb hab
    exact hFmax.not_gt ⟨Finset.insert_subset_iff.mpr ⟨hi,hFC⟩,hInsert⟩
      (Finset.ssubset_insert hnotF)
  push Not at hbad
  obtain ⟨j,hj,hij⟩ := hbad
  unfold compatible at hij
  push Not at hij
  obtain ⟨p,hp,q,hq,hd⟩ := hij
  exact ⟨j,hj,p,hp,q,hq,hd⟩

end FiniteCommonPointTubeRepresentatives
