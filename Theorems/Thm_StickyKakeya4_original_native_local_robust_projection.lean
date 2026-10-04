import Theorems.Thm_StickyKakeya4_original_native_projection_failure_comparison
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3200000
noncomputable section
open Classical

namespace OriginalNativeLocalRobustProjection
open ProjectionAnnulusEnergy GKZOriginalGapEnergy OriginalTwoProjectionCartesian
open OriginalFreshProjectionQueries OriginalNativeProjectionBSGCore OriginalNativeProjectionFailureComparison

/-- Pure numerical budgets close the actual local robust source theorem.
The returned original F and Good are constructed by negating literal failure;
all projection profiles and retained graph data are derived internally by
the genuine native comparison. -/
theorem exists_original_local_robust_projection (u gap : ℝ)
    (hu : 0<u) (hu1 : u≤1) (hgap : 0<gap) (hgap1 : gap≤1) :
    ∃ epsilon eta delta0 : ℝ, 0<epsilon ∧ 0<eta ∧ 0<delta0 ∧ delta0≤1 ∧
      ∀ (P : Finset Point) (C : Finset ℝ) (n : ℕ)
        (KP KC mass q beta eps h M : ℝ),
        P.Nonempty → C.Nonempty → 1≤KP → 1≤KC → 0 < mass → mass≤1 →
        0<q → 0<beta → beta≤1 → 0<eps → eps<1 → eps≤q^3/16 →
        0<h → h≤1 → mesh n≤h → 0<M →
        (∀ p∈P, |p.1|≤1 ∧ |p.2|≤1) → (∀ c∈C, |c|≤1) →
        (∀ p∈P, ∀ p'∈P, p≠p' → mesh n≤‖p-p'‖) →
        PointFrostman P (mesh n) KP u → ScalarFrostman C (mesh n) KC u →
        ((KC/beta)/(1-eps))*h^u≤q^3/16 → KC*h^u≤beta/4 →
        mass*(P.card:ℝ)≤originalRetention (q^3/16) P.card h M*M^2 →
        h*mesh n/64≤delta0 → M≤(h*mesh n/64)^(-1+gap) →
        originalAlphabetProfileCost n KP KC beta eps q P.card h M*(16/h)^u/
          originalRetention (q^3/16) P.card h M≤(h*mesh n/64)^(-eta) →
        (2*KC/beta)*(64/h^2)^u≤(h*mesh n/64)^(-eta) → 4/h^2≤(h*mesh n/64)^(-eta) →
        (2:ℝ)^242*fiberBound h*(restrictedSumLoss h)^15*(12672/h^5)≤
          q*(originalDensity (q^3/16) P.card h M)^77*(h*mesh n/64)^(-epsilon) →
        ∃ F : Finset Point, F⊆P ∧ F.Nonempty ∧ mass*(P.card:ℝ)≤F.card ∧
          ∃ Good : Finset ℝ, Good⊆C ∧ (1-beta)*(C.card:ℝ)≤Good.card ∧
            ∀ c∈Good, ∀ Q : Finset Point, Q⊆F → q*(F.card:ℝ)≤Q.card →
              M<(alphabet Q (mesh n) c).card := by
  obtain ⟨epsilon,eta,delta0,hepsilon,heta,hd0,hd01,hcompare⟩ :=
    exists_original_native_failure_comparison u gap hu hu1 hgap hgap1
  refine ⟨epsilon,eta,delta0,hepsilon,heta,hd0,hd01,?_⟩
  intro P C n KP KC mass q beta eps h M hP hC hKP hKC hmass hmass1 hq hbeta hbeta1
    heps heps1 hepsq hh hh1 hscale hM hPbox hCbox hsep hPprofile hCprofile
    hfirstbudget hfreshbudget hadmissible hsmall hcard hAbudget hDbudget hboxbudget hreverse
  have hnot : ¬Failure P C mass q beta M (fun c Q => (alphabet Q (mesh n) c).card) := by
    intro hfailure
    have hstrict := hcompare P C n KP KC mass q beta eps h M hP hC hKP hKC hmass1
      hq hbeta hbeta1 heps heps1 hepsq hh hh1 hscale hM hPbox hCbox hsep
      hPprofile hCprofile hfirstbudget hfreshbudget hadmissible hsmall hcard
      hAbudget hDbudget hboxbudget hfailure
    exact (not_lt_of_ge hreverse) hstrict
  obtain ⟨F,hFP,hFmass,Good,hGC,hGmass,hgood⟩ := local_robust_of_not_failure P C
    mass q beta M (fun c Q => (alphabet Q (mesh n) c).card) hnot
  have hFnon : F.Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp
    ((mul_pos hmass (Nat.cast_pos.mpr hP.card_pos)).trans_le hFmass))
  exact ⟨F,hFP,hFnon,hFmass,Good,hGC,hGmass.le,hgood⟩

end OriginalNativeLocalRobustProjection
