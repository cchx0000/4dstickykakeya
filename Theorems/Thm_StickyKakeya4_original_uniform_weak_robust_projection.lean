import Theorems.Thm_StickyKakeya4_original_native_uniform_budget
import Theorems.Thm_StickyKakeya4_original_native_local_robust_projection
import Theorems.Thm_StickyKakeya4_original_native_robust_global_assembly
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5200000
noncomputable section
open Classical

namespace OriginalUniformWeakRobustProjection
open ProjectionAnnulusEnergy OriginalTwoProjectionCartesian GKZOriginalGapEnergy
open OriginalNativeLocalRobustProjection OriginalNativeProjectionPowerCutoff
open OriginalNativeUniformBudget OriginalNativeCoverScaleBudget OriginalNativeRobustResiduals
open OriginalNativeRobustGlobalAssembly

/-- A positive local robust gain with every exponent and cutoff chosen
before the ORIGINAL point and slope sets. All numerical conditions are
proved from one original dyadic cutoff. -/
theorem exists_uniform_original_local_projection (u gap : ℝ)
    (hu : 0<u) (hu1 : u≤1) (hgap : 0<gap) (hgap1 : gap≤1/4) :
    ∃ e d : ℝ, 0<e ∧ 0<d ∧ d≤1 ∧
      (∀ n : ℕ,mesh n≤d → (mesh n)^(e/4)≤1/4) ∧
      ∀ (P : Finset Point) (C : Finset ℝ) (n : ℕ),
        P.Nonempty → C.Nonempty → mesh n≤d →
        (∀ p∈P,|p.1|≤1 ∧ |p.2|≤1) → (∀ c∈C,|c|≤1) →
        (∀ p∈P,∀ q∈P,p≠q → mesh n≤‖p-q‖) →
        PointFrostman P (mesh n) ((mesh n)^(-e)) u →
        ScalarFrostman C (mesh n) ((mesh n)^(-e)) u →
        (P.card:ℝ)≤(mesh n)^(-2+4*gap) →
        ∃ F : Finset Point,F⊆P ∧ F.Nonempty ∧
          ∃ Good : Finset ℝ,Good⊆C ∧ (1-(mesh n)^e)*(C.card:ℝ)≤Good.card ∧
            ∀ c∈Good,∀ Q : Finset Point,Q⊆F → (mesh n)^e*(F.card:ℝ)≤Q.card →
              (mesh n)^(-e)*Real.sqrt P.card < (alphabet Q (mesh n) c).card := by
  obtain ⟨epsilon,eta,scalarCutoff,hepsilon,heta,hscalar,_hscalar1,hlocal⟩ :=
    exists_original_local_robust_projection u gap hu hu1 hgap (by linarith only [hgap1])
  obtain ⟨e,d,he,hd,hd1,_hdscalar,hbudgets⟩ :=
    exists_original_native_uniform_budget hu hu1 hgap hgap1 heta hepsilon hscalar
  have hquarter : ∀ n : ℕ,mesh n≤d → (mesh n)^(e/4)≤1/4 := by
    intro n hn
    have hcard : (1:ℝ)≤(mesh n)^(-2+4*gap) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos (mesh_pos n) (hn.trans hd1)
        (by linarith only [hgap1])
    exact (hbudgets n 1 hn (by norm_num) hcard).1
  refine ⟨e,d,he,hd,hd1,hquarter,?_⟩
  intro P C n hP hC hn hPbox hCbox hsep hPprofile hCprofile hcard
  let delta := mesh n
  let t := delta^e
  let h := delta^(8*e/u)
  let M := delta^(-e)*Real.sqrt P.card
  let mass := delta^((20+64/u)*e)
  have hdelta : 0<delta := mesh_pos n
  have hN : (0:ℝ)<P.card := Nat.cast_pos.mpr hP.card_pos
  obtain ⟨_hquarter,B⟩ := hbudgets n P.card hn hN hcard
  have hmass : 0 < mass := Real.rpow_pos_of_pos hdelta _
  have hinverse : delta^(-e)=1/t := native_inverse_power hdelta
  have hPprofile' : PointFrostman P delta (1/t) u := by rw [← hinverse]; exact hPprofile
  have hCprofile' : ScalarFrostman C delta (1/t) u := by rw [← hinverse]; exact hCprofile
  obtain ⟨F,hFP,hFnon,_hFmass,Good,hGC,hGmass,hgood⟩ := hlocal P C n (1/t) (1/t) mass t t
    (t^4/32) h M hP hC B.coefficient_ge_one B.coefficient_ge_one hmass B.source_mass_le_one
    B.query_pos B.query_pos B.query_le_one B.host_pos B.host_lt_one B.host_budget B.angle_pos
    B.angle_le_one B.angle_mesh B.cover_pos hPbox hCbox hsep hPprofile' hCprofile'
    B.first_angles B.fresh_angles B.retained_admissibility B.scalar_mesh_small B.cover_cardinality
    B.alphabet_profile B.coefficient_profile B.coefficient_box B.reverse_comparison
  exact ⟨F,hFP,hFnon,Good,hGC,hGmass,hgood⟩

/-- Genuine uniform weak-profile robust projection. The gain and cutoff
precede the original separated planar set and original slopes. Most actual
slopes expand EVERY sufficiently dense original subquery. -/
theorem exists_uniform_original_robust_projection (u gap : ℝ)
    (hu : 0<u) (hu1 : u≤1) (hgap : 0<gap) (hgap1 : gap≤1/4) :
    ∃ nu d : ℝ, 0<nu ∧ 0<d ∧ d≤1 ∧
      ∀ (P : Finset Point) (C : Finset ℝ) (n : ℕ),
        P.Nonempty → C.Nonempty → mesh n≤d →
        (∀ p∈P,|p.1|≤1 ∧ |p.2|≤1) → (∀ c∈C,|c|≤1) →
        (∀ p∈P,∀ q∈P,p≠q → mesh n≤‖p-q‖) →
        PointFrostman P (mesh n) ((mesh n)^(-nu)) u →
        ScalarFrostman C (mesh n) ((mesh n)^(-nu)) u →
        (P.card:ℝ)≤(mesh n)^(-2+4*gap) →
        ∃ Good : Finset ℝ,Good⊆C ∧ (1-(mesh n)^nu)*(C.card:ℝ)≤Good.card ∧
          ∀ c∈Good,∀ Q : Finset Point,Q⊆P → (mesh n)^nu*(P.card:ℝ)≤Q.card →
            (mesh n)^(-nu)*Real.sqrt P.card < (alphabet Q (mesh n) c).card := by
  obtain ⟨e,d,he,hd,hd1,hquarter,hlocal⟩ := exists_uniform_original_local_projection u gap hu hu1 hgap hgap1
  refine ⟨e/4,d,by positivity,hd,hd1,?_⟩
  intro P C n hP hC hn hPbox hCbox hsep hPprofile hCprofile hcard
  have hdelta := mesh_pos n
  have hdelta1 := hn.trans hd1
  have hCprofile' : ScalarFrostman C (mesh n) ((mesh n)^(-e)) u :=
    original_scalar_profile_mono C hdelta (Real.rpow_nonneg hdelta.le _)
      (Real.rpow_le_rpow_of_exponent_ge hdelta hdelta1 (show -e≤-(e/4) by linarith only [he]))
      (le_refl u) hCprofile
  have hPprofile' : PointFrostman P (mesh n) ((mesh n)^(-e/4)) u := by
    simpa only [neg_div] using hPprofile
  have hresult := original_global_of_uniform_local P C hP hdelta hdelta1 he (hquarter n hn) hPprofile' ?_
  · simpa only [neg_div] using hresult
  · intro R hRnon hRP hRprofile
    exact hlocal R C n hRnon hC hn
      (fun p hp => hPbox p (hRP hp)) hCbox
      (fun p hp q hq hpq => hsep p (hRP hp) q (hRP hq) hpq)
      hRprofile hCprofile' ((Nat.cast_le.mpr (Finset.card_le_card hRP)).trans hcard)

end OriginalUniformWeakRobustProjection
