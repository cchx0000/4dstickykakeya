import Theorems.Thm_StickyKakeya4_native_actual_mesoscopic_rank_configuration
import Theorems.Thm_StickyKakeya4_native_second_refinement_cost
import Theorems.Thm_StickyKakeya4_native_two_stage_transversality_budget
import Theorems.Thm_StickyKakeya4_native_rank_radius_rounding
import Theorems.Thm_StickyKakeya4_native_two_stage_plane_rank

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 5000000
noncomputable section

namespace NativeRetainedRankCutoffs
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeJointUniformCoarseRelations NativeLocalPairUniformCore SelfUniform
open NativeRankExponentHierarchy NativeTwoStageTransversalityBudget
open NativeMiddleWindowBalance NativeActualMesoscopicRankConfiguration

/-- The second refinement always installs equality of the original fine point,
in addition to every relation the caller fixed before choosing the source. -/
def finePointMenu {n d : ℕ}
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop) :
    Fin (d+1) → (Fin n × Index) → (Fin n × Index) → Prop :=
  Fin.addCases Rel (fun _ x y => x.2=y.2)

lemma finePointMenu_refl {n d : ℕ}
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : ∀j x,Rel j x x) : ∀j x,finePointMenu Rel j x x := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro k x
    simpa only [finePointMenu,Fin.addCases_left] using H k x
  · intro k x
    simp only [finePointMenu,Fin.addCases_right]

lemma finePointMenu_symm {n d : ℕ}
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (H : ∀j x y,Rel j x y → Rel j y x) :
    ∀j x y,finePointMenu Rel j x y → finePointMenu Rel j y x := by
  intro j
  refine Fin.addCases ?_ ?_ j
  · intro k x y hh
    simpa only [finePointMenu,Fin.addCases_left] using
      H k x y (by simpa only [finePointMenu,Fin.addCases_left] using hh)
  · intro k x y hh
    have heq : x.2=y.2 := by
      simpa only [finePointMenu,Fin.addCases_right] using hh
    simpa only [finePointMenu,Fin.addCases_right] using heq.symm

theorem finePointMenu_uniformities {n d : ℕ}
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (E : Finset (Fin n × Index)) (Q : ℕ)
    (H : ∀j x y,x∈E → y∈E →
      degree (fun _ : Fin n × Index => 1) (finePointMenu Rel j) E x ≤
        Q^2*degree (fun _ : Fin n × Index => 1) (finePointMenu Rel j) E y) :
    (∀j x y,x∈E → y∈E → degree (fun _ : Fin n × Index => 1) (Rel j) E x ≤
      Q^2*degree (fun _ : Fin n × Index => 1) (Rel j) E y) ∧
    HasUniformFibers E Q Prod.snd := by
  constructor
  · intro j x y hx hy
    simpa only [finePointMenu,Fin.addCases_left] using H (Fin.castAdd 1 j) x y hx hy
  · intro x hx y hy
    simpa only [finePointMenu,Fin.addCases_right,unit_degree_eq_fiber] using
      H (Fin.natAdd d (0 : Fin 1)) x y hx hy

/-- A single positive source cutoff works for every possible selected rank.
The two transfer costs are inputs to the later application, not assumed
half-mass or pointwise-retention certificates. -/
theorem exists_rank_half_mass_cutoff {eta0 c c1 c2 : ℝ}
    (he0 : 0 < eta0) (hc : 0 < c) (g : ℕ)
    (hgap : c1+c2 < commonBudget eta0 c) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
        ∀ ell : Fin 4, ∀ F1 F2 Q1 Q2 : ℕ, 0 < F1 →
          ∀ eta1 eta2 G r q beta previous : ℝ,
          0 ≤ eta1 → 0 ≤ eta2 → 0 ≤ G → G ≤ F2 →
          0 < r → r ≤ 1 → r ≤ delta^(cutoff c ell) → 0 ≤ q → 0 ≤ previous →
          q ≤ r^beta → 2*rankLoss eta0 c ell ≤ beta*previous →
          (125*175616*16384:ℝ)*(F1:ℝ)*(Q1:ℝ)^2*delta^(-eta1) ≤ delta^(-c1) →
          (125*175616*16384:ℝ)*(F2:ℝ)*(Q2:ℝ)^2*delta^(-eta2) ≤ delta^(-c2) →
          q^previous*G*(Q1:ℝ)^2*(Q2:ℝ)^2 ≤
            (r^(rankLoss eta0 c ell)/(4*((g:ℝ)+1)))/2 := by
  have hex := fun ell : Fin 4 => exists_half_mass_cutoff
    (a := cutoff c ell) (stop := rankLoss eta0 c ell) (c1 := c1) (c2 := c2)
    (menuCost := 4*((g:ℝ)+1)) (rankLoss_pos he0 hc ell) (by positivity)
    (by simpa only [cutoff_mul_rankLoss] using hgap)
  choose ds hds hds1 hcuts using hex
  let delta0 := min (ds 0) (min (ds 1) (min (ds 2) (ds 3)))
  have hd0 : 0 < delta0 := lt_min (hds 0) (lt_min (hds 1) (lt_min (hds 2) (hds 3)))
  have h0 : delta0 ≤ ds 0 := min_le_left _ _
  have h1 : delta0 ≤ ds 1 := (min_le_right _ _).trans (min_le_left _ _)
  have h2 : delta0 ≤ ds 2 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have h3 : delta0 ≤ ds 3 := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hall : ∀i : Fin 4,delta0 ≤ ds i := by
    intro i
    fin_cases i <;> assumption
  refine ⟨delta0,hd0,(hall 0).trans (hds1 0),?_⟩
  intro delta hd hsmall ell
  exact hcuts ell delta hd (hsmall.trans (hall ell))

/-- A uniform endpoint cutoff pays the rounding loss at every adjacent rank.
The extra bound on tau can be imposed before requesting the first source. -/
theorem exists_rank_rounding_cutoff {c tau : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (htau : 0 < tau) (htauC : tau ≤ c^3/8) :
    ∃ delta0 : ℝ, 0 < delta0 ∧ delta0 ≤ 1 ∧
      ∀ delta : ℝ, 0 < delta → delta ≤ delta0 →
      ∀ previous next : Fin 4, previous.val+1=next.val →
      delta^(cutoff c next*(2*c)-rankWindow tau/2) ≤ 1/96 := by
  have hw : rankWindow tau ≤ tau/1000 :=
    (min_le_left _ _).trans (min_le_left _ _)
  have ha : 0 < c^3/8 := by positivity
  have hexp : 0 < 2*(c^3/8)-rankWindow tau/2 := by linarith
  obtain ⟨delta0,hd0,hd1,hcut⟩ := exists_positive_rpow_absorption_threshold
    hexp (by norm_num : (0:ℝ)≤1) (by norm_num : (0:ℝ)<1/96)
  refine ⟨delta0,hd0,hd1,?_⟩
  intro delta hd hsmall previous next hnext
  have hbound := (cutoff_bounds hc hc1 previous).2.2
  have hid := (adjacent_identities 1 c previous next hnext).2
  have hexp' : 2*(c^3/8)-rankWindow tau/2 ≤ cutoff c next*(2*c)-rankWindow tau/2 := by
    rw [hid]
    linarith
  exact (Real.rpow_le_rpow_of_exponent_ge hd (hsmall.trans hd1) hexp').trans
    (by simpa only [one_mul] using hcut delta hd hsmall)

end NativeRetainedRankCutoffs
