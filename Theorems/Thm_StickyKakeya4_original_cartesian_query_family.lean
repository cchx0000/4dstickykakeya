import Theorems.Thm_StickyKakeya4_original_native_transverse_queries
import Theorems.Thm_StickyKakeya4_original_two_projection_real_graph
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000
noncomputable section
open Classical

namespace OriginalCartesianQueryFamily
open ProjectionAnnulusEnergy OriginalNativeTransverseQueries
open OriginalTwoProjectionCartesian OriginalTwoProjectionCover OriginalTwoProjectionRealGraph
open ActualRoundedAdditiveEnergy

lemma real_alphabet_mono {P Q : Finset Point} (hQP : Q ⊆ P) (delta lam : ℝ) :
    realAlphabet Q delta lam ⊆ realAlphabet P delta lam :=
  Finset.image_subset_image (Finset.image_subset_image hQP)

lemma real_graph_mono {P Q : Finset Point} (hQP : Q ⊆ P) (delta a b : ℝ) :
    realGraph Q delta a b ⊆ realGraph P delta a b :=
  Finset.image_subset_image (Finset.image_subset_image hQP)

/-- A varying family of dense original planar queries produces one fixed
pair of separated real alphabets and many actual dense scalar graphs. The
third-image bounds and original point witnesses survive the whole selection. -/
theorem exists_original_cartesian_query_family
    (P : Finset Point) (C : Finset ℝ) (Q : ℝ → Finset Point)
    {q h delta K Kc s : ℝ} (hP : P.Nonempty) (hC : C.Nonempty) (hq : 0 < q)
    (hd : 0 < delta) (hd1 : delta ≤ 1) (hh : 0 < h) (hscale : delta ≤ h) (hh1 : h ≤ 1)
    (hK : 0 < K) (hprofile : SlopeFrostman C delta Kc s) (hbudget : Kc*h^s ≤ q^3/16)
    (hPbox : ∀ p ∈ P, |p.1| ≤ 1 ∧ |p.2| ≤ 1)
    (hCbox : ∀ c ∈ C, |c| ≤ 1)
    (hsep : ∀ p ∈ P, ∀ p' ∈ P, p≠p' → delta ≤ ‖p-p'‖)
    (hQ : ∀ c ∈ C, Q c ⊆ P) (hmass : ∀ c ∈ C, q*(P.card : ℝ) ≤ (Q c).card)
    (hcover : ∀ c ∈ C, ((alphabet (Q c) delta c).card : ℝ) ≤ K*Real.sqrt P.card) :
    ∃ a ∈ C, ∃ b ∈ C, h ≤ |a-b| ∧
      ∃ C' : Finset ℝ, C' ⊆ C ∧ (q^3/8)*(C.card : ℝ) ≤ C'.card ∧
        let A := realAlphabet (Q a ∩ Q b) delta a
        let B := realAlphabet (Q a ∩ Q b) delta b
        (∀ x ∈ A, |x| ≤ 1) ∧ (∀ y ∈ B, |y| ≤ 1) ∧
        (∀ x ∈ A, ∀ x' ∈ A, x≠x' → delta/4 ≤ |x-x'|) ∧
        (∀ y ∈ B, ∀ y' ∈ B, y≠y' → delta/4 ≤ |y-y'|) ∧
        ∀ c ∈ C', ∃ G : Finset Point, G ⊆ A.product B ∧
          (q^3/4)*(P.card : ℝ) ≤ fiberBound h*G.card ∧
          (q^3/4)*(A.card : ℝ)*B.card ≤ fiberBound h*K^2*G.card ∧
          ((G.image (fun z => rounded (delta/4) (linearValue a b c z))).card : ℝ) ≤
            (8/h+4)*K*Real.sqrt P.card ∧
          (h/2 ≤ |leftWeight a b c| ∧ h/2 ≤ |rightWeight a b c|) ∧
          ∀ z ∈ G, ∃ p ∈ P, p∈Q a ∧ p∈Q b ∧ p∈Q c ∧
            z=realPoint delta (code delta a b p) := by
  obtain ⟨a,ha,b,hb,hab,C',hC'C,hC'mass,hP0P,_hP0mass,hqueries⟩ :=
    exists_native_transverse_common_queries P C Q hP hC hq hscale hh1 hprofile hbudget hQ hmass
  let P0 := Q a ∩ Q b
  let A := realAlphabet P0 delta a
  let B := realAlphabet P0 delta b
  have hP0box : ∀ p ∈ P0, |p.1| ≤ 1 ∧ |p.2| ≤ 1 :=
    fun p hp => hPbox p (hP0P hp)
  have htrans : h ≤ |b-a| := by simpa only [abs_sub_comm] using hab
  have hA : (A.card : ℝ) ≤ K*Real.sqrt P.card := by
    have hsub : alphabet P0 delta a ⊆ alphabet (Q a) delta a :=
      Finset.image_subset_image Finset.inter_subset_left
    rw [real_alphabet_card P0 hd]
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcover a ha)
  have hB : (B.card : ℝ) ≤ K*Real.sqrt P.card := by
    have hsub : alphabet P0 delta b ⊆ alphabet (Q b) delta b :=
      Finset.image_subset_image Finset.inter_subset_right
    rw [real_alphabet_card P0 hd]
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcover b hb)
  have hprod : (A.card : ℝ)*B.card ≤ K^2*P.card := by
    have hm := mul_le_mul hA hB (Nat.cast_nonneg _) (by positivity : 0 ≤ K*Real.sqrt P.card)
    have hs := Real.sq_sqrt (Nat.cast_nonneg P.card : (0:ℝ) ≤ P.card)
    nlinarith only [hm,hs]
  refine ⟨a,ha,b,hb,hab,C',hC'C,hC'mass,?_⟩
  dsimp only
  refine ⟨real_alphabet_unit_box P0 hd hd1 (hCbox a ha) hP0box,
    real_alphabet_unit_box P0 hd hd1 (hCbox b hb) hP0box,
    real_alphabet_separated P0 hd,real_alphabet_separated P0 hd,?_⟩
  intro c hc
  let R := P0 ∩ Q c
  let G := realGraph R delta a b
  have hcC := hC'C hc
  obtain ⟨hca,hcb,hRmass⟩ := hqueries c hc
  have hRP0 : R ⊆ P0 := Finset.inter_subset_left
  have hRP : R ⊆ P := hRP0.trans hP0P
  have hRc : R ⊆ Q c := Finset.inter_subset_right
  have hGsub : G ⊆ A.product B := by
    exact (real_graph_mono hRP0 delta a b).trans (real_graph_subset_product P0 delta a b)
  have hGmass : (q^3/4)*(P.card : ℝ) ≤ fiberBound h*G.card := by
    have hm := original_query_graph_mass P hd hh hh1 htrans (hCbox a ha) hsep R hRP
    rw [← real_graph_card R hd] at hm
    exact hRmass.trans hm
  have hGdensity : (q^3/4)*(A.card : ℝ)*B.card ≤ fiberBound h*K^2*G.card := by
    have hleft := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ q^3/4)
    have hright := mul_le_mul_of_nonneg_left hGmass (sq_nonneg K)
    nlinarith only [hleft,hright]
  have hGcover : ((G.image (fun z => rounded (delta/4) (linearValue a b c z))).card : ℝ) ≤
      (8/h+4)*K*Real.sqrt P.card := by
    have hsub : alphabet R delta c ⊆ alphabet (Q c) delta c := Finset.image_subset_image hRc
    have hcc := (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hcover c hcC)
    have hv := real_query_cover R hd hh htrans (hCbox a ha) (hCbox b hb) (hCbox c hcC)
    calc
      _ ≤ (8/h+4)*(alphabet R delta c).card := hv
      _ ≤ (8/h+4)*(K*Real.sqrt P.card) := mul_le_mul_of_nonneg_left hcc (by positivity)
      _ = _ := by ring
  refine ⟨G,hGsub,hGmass,hGdensity,hGcover,
    weights_lower_of_three_transverse hh hab hca hcb (hCbox a ha) (hCbox b hb),?_⟩
  intro z hz
  obtain ⟨p,hp,hpz⟩ := real_graph_original_witness R delta a b hz
  have hqa := (Finset.mem_inter.mp (hRP0 hp)).1
  have hqb := (Finset.mem_inter.mp (hRP0 hp)).2
  exact ⟨p,hRP hp,hqa,hqb,hRc hp,hpz⟩

end OriginalCartesianQueryFamily
