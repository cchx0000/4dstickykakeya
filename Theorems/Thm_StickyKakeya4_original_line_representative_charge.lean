import Theorems.Thm_StickyKakeya4_original_unit_line_grid
import Mathlib.Combinatorics.Enumerative.DoubleCounting

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalLineRepresentativeCharge
open OriginalPairStripGeometry NativeRadialClassPruning OriginalTwoHopPairFamily
open OriginalUnitLineGrid

/-- The original pair graph pays for the actual parameter representatives.
The multiplicity 539 is proved from their literal fine-grid cells. -/
theorem original_representative_pair_charge
    (Pts : Finset Point) (G R : Finset Pair) (rho k : ℝ)
    (hrho : 0<rho) (hk : 0≤k) (hR : R⊆G)
    (hinj : Set.InjOn (lineCell rho) (↑R : Set Pair))
    (hGP : G⊆Pts.product Pts) (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hdistinct : ∀ u∈G, u.1≠u.2)
    (hrich : ∀ u∈G,
      2*k≤((G.filter (fun v => forwardClass rho v=forwardClass rho u)).card : ℝ) ∧
      2*k≤((G.filter (fun v => reverseClass rho v=reverseClass rho u)).card : ℝ)) :
    4*k^2*(R.card : ℝ)≤539*(G.card : ℝ) := by
  classical
  let rel := fun z v : Pair => v∈twoHopPairs G rho z
  have hlower : ∀ z∈R, 4*k^2≤((G.bipartiteAbove rel z).card : ℝ) := by
    intro z hz
    have heq : G.bipartiteAbove rel z=twoHopPairs G rho z := by
      ext v
      simp only [Finset.bipartiteAbove,Finset.mem_filter,rel]
      exact ⟨And.right,fun hv => ⟨((mem_two_hop_pairs G rho z v).mp hv).choose_spec.2.2.1,hv⟩⟩
    rw [heq]
    exact original_two_hop_pair_count G rho k z hk (hR hz) hrich
  have hupper : ∀ v∈G, ((R.bipartiteBelow rel v).card : ℝ)≤539 := by
    intro v _hv
    exact_mod_cast original_two_hop_representative_multiplicity Pts G R rho v
      hrho hR hinj hGP hbox hdistinct
  have hcount := Finset.card_nsmul_le_card_nsmul (R:=ℝ) (r:=rel) (s:=R) (t:=G)
    hlower hupper
  simpa only [nsmul_eq_mul,mul_comm] using hcount

/-- A localized count uses actual original endpoints in S. It retains the
same proved fine-grid multiplicity rather than postulating local overlap. -/
theorem localized_original_representative_pair_charge
    (Pts S : Finset Point) (G R : Finset Pair) (rho k : ℝ)
    (hrho : 0<rho) (hk : 0≤k) (hR : R⊆G)
    (hinj : Set.InjOn (lineCell rho) (↑R : Set Pair))
    (hGP : G⊆Pts.product Pts) (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hdistinct : ∀ u∈G, u.1≠u.2)
    (hrich : ∀ u∈G,
      2*k≤((G.filter (fun v => forwardClass rho v=forwardClass rho u)).card : ℝ) ∧
      2*k≤((G.filter (fun v => reverseClass rho v=reverseClass rho u)).card : ℝ))
    (hsupport : ∀ z∈R, twoHopPairs G rho z⊆S.product S) :
    4*k^2*(R.card : ℝ)≤539*(S.card : ℝ)^2 := by
  classical
  let rel := fun z v : Pair => v∈twoHopPairs G rho z
  have hlower : ∀ z∈R, 4*k^2≤(((S.product S).bipartiteAbove rel z).card : ℝ) := by
    intro z hz
    have heq : (S.product S).bipartiteAbove rel z=twoHopPairs G rho z := by
      ext v
      simp only [Finset.bipartiteAbove,Finset.mem_filter,rel]
      exact ⟨And.right,fun hv => ⟨hsupport z hz hv,hv⟩⟩
    rw [heq]
    exact original_two_hop_pair_count G rho k z hk (hR hz) hrich
  have hupper : ∀ v∈S.product S, ((R.bipartiteBelow rel v).card : ℝ)≤539 := by
    intro v _hv
    exact_mod_cast original_two_hop_representative_multiplicity Pts G R rho v
      hrho hR hinj hGP hbox hdistinct
  have hcount := Finset.card_nsmul_le_card_nsmul (R:=ℝ) (r:=rel) (s:=R) (t:=S.product S)
    hlower hupper
  simpa only [nsmul_eq_mul,Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul,pow_two,mul_comm] using hcount

/-- The family and the global count are both obtained from the original
pruned graph. Each occupied original line cell has an original representative. -/
theorem exists_charged_original_line_representatives
    (Pts : Finset Point) (G : Finset Pair) (rho k : ℝ)
    (hrho : 0<rho) (hk : 0≤k)
    (hGP : G⊆Pts.product Pts) (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hdistinct : ∀ u∈G, u.1≠u.2)
    (hrich : ∀ u∈G,
      2*k≤((G.filter (fun v => forwardClass rho v=forwardClass rho u)).card : ℝ) ∧
      2*k≤((G.filter (fun v => reverseClass rho v=reverseClass rho u)).card : ℝ)) :
    ∃ R : Finset Pair, R⊆G ∧ Set.InjOn (lineCell rho) (↑R : Set Pair) ∧
      R.image (lineCell rho)=G.image (lineCell rho) ∧
      4*k^2*(R.card : ℝ)≤539*(G.card : ℝ) := by
  obtain ⟨R,hR,hi,heq⟩ := exists_original_line_cell_representatives G rho
  exact ⟨R,hR,hi,heq,original_representative_pair_charge Pts G R rho k
    hrho hk hR hi hGP hbox hdistinct hrich⟩

end OriginalLineRepresentativeCharge
