import Theorems.Thm_StickyKakeya4_original_shading_representative_frostman
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

noncomputable section
open Classical
namespace OriginalCoarseShadingPreparation
local instance : DecidableEq (ℤ×ℤ) := Classical.decEq _
open DyadicOriginalFiberSelection OriginalShadingCellSelection OriginalShadingCellMass
open OriginalShadingGridGeometry OriginalShadingRepresentatives
open OriginalShadingRepresentativeFrostman

/-- Construct the common coarse-shading parameters on original tube labels.
Representatives are original points, retain their physical incidences, and
have an actual coarse Frostman profile. The union is charged to ORIGINAL
fine point mass by local occupancy, for every such representative choice. -/
theorem exists_original_coarse_shadings {X I : Type*}
    (P : Finset X) (T : Finset I) (Y : I → Finset X) (p : X → ℝ×ℝ)
    {h K s : ℝ} (hh : 0<h) (hK : 1≤K) (hs : 0≤s)
    (hT : T.Nonempty) (hsub : ∀ t∈T, Y t ⊆ P) (hY : ∀ t∈T, (Y t).Nonempty)
    (hpoint : ∀ t∈T, ∀ (x : ℝ×ℝ) (r : ℝ), h≤r → r≤1 →
      (((Y t).filter (fun y => InBox (p y) x r)).card : ℝ) ≤ K*r^s*(Y t).card) :
    ∃ j k : ℕ, ∃ S : Finset I, S ⊆ T ∧ S.Nonempty ∧
      j<levelCount P ∧ k<levelCount P ∧ T.card≤(levelCount P)^2*S.card ∧
      (∀ t∈S, (Y t).card ≤ 4*levelCount P*2^j*2^k ∧
        ∃ R : Finset X, R ⊆ bin (Y t) (fun y => grid h (p y)) j ∧
          R.Nonempty ∧ 2^k≤9*R.card ∧ R.card<2^(k+1) ∧
          (∀ a∈R, ∀ b∈R, a≠b →
            2*h < max |(p a).1-(p b).1| |(p a).2-(p b).2|) ∧
          (∀ (x : ℝ×ℝ) (r : ℝ), h≤r →
            ((R.filter (fun y => InBox (p y) x r)).card : ℝ) ≤
              18*(levelCount P : ℝ)*(K*(2*r)^s)*R.card)) ∧
      (∀ R : I → Finset X,
        (∀ t∈S, R t ⊆ bin (Y t) (fun y => grid h (p y)) j) →
        2^j*(S.biUnion (fun t => (R t).image (fun y => grid h (p y)))).card ≤P.card) := by
  let g := fun y => grid h (p y)
  obtain ⟨j,k,S,hST,hS,hj,hk,hpop,hbins,_hunion⟩ :=
    exists_uniform_original_shading_bins P T Y g hT hsub hY
  refine ⟨j,k,S,hST,hS,hj,hk,hpop,?_,?_⟩
  · intro t ht
    obtain ⟨_hbin,hretain,hlo,hhi⟩ := hbins t ht
    refine ⟨original_mass_le_four_log_occupancy_cells (Y t) g j k
      (levelCount P) hretain hhi,?_⟩
    obtain ⟨R,hR,hRcard,hinj,hsep⟩ :=
      exists_separated_original_representatives (bin (Y t) g j) p hh
    have hRpos : 0<R.card := by
      have hp : 0<2^k := by positivity
      have hc := hlo.trans hRcard
      nlinarith only [hp,hc]
    have hRupper : R.card≤((bin (Y t) g j).image g).card := by
      rw [← Finset.card_image_iff.mpr hinj]
      exact Finset.card_le_card (Finset.image_subset_image hR)
    refine ⟨R,hR,Finset.card_pos.mp hRpos,hlo.trans hRcard,hRupper.trans_lt hhi,hsep,?_⟩
    intro x r hr
    exact original_representative_frostman (Y t) R p j hh (by positivity) hK hs
      hR hinj (by exact_mod_cast hretain) hRcard (hpoint t (hST ht)) x hr
  · intro R hR
    apply original_union_cell_charge P S Y (fun t => (R t).image g) g (2^j)
      (fun t ht => hsub t (hST ht))
    intro t ht c hc
    have hcb : c∈(bin (Y t) g j).image g :=
      Finset.image_subset_image (hR t ht) hc
    have hm := (bin_fiber_bounds (Y t) g j hcb).1
    rw [fiber_bin_eq (Y t) g j hcb] at hm
    exact hm

end OriginalCoarseShadingPreparation
