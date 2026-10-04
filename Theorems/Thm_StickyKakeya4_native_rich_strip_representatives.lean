import Theorems.Thm_StickyKakeya4_planar_strip_intersection
import Theorems.Thm_StickyKakeya4_finite_common_point_tube_representatives
import Theorems.Thm_StickyKakeya4_rich_family_incidence_bound

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

noncomputable section
namespace NativeRichStripRepresentatives
open PlanarStripIntersection FiniteCommonPointTubeRepresentatives

def support {T : Type*} (Pts : Finset (ℝ × ℝ)) (a b c : T → ℝ) (w : ℝ) (i : T) :
    Finset (ℝ × ℝ) := by
  classical
  exact Pts.filter (fun p => |residual (a i) (b i) (c i) p|≤w)

/-- Actual point-diameter control is converted to the original point-centered
ball count, without transporting lower density through a restriction. -/
theorem diameter_support_card_bound
    {P : Type*} [DecidableEq P] (Pts A : Finset P) (distance : P → P → ℝ)
    (rho B : ℝ) (hB : 0≤B) (hAP : A⊆Pts)
    (hdiam : ∀ p∈A, ∀ q∈A, distance p q≤rho)
    (hballs : ∀ p∈Pts, ((Pts.filter (fun q => distance p q≤rho)).card : ℝ)≤B) :
    (A.card : ℝ)≤B := by
  classical
  rcases A.eq_empty_or_nonempty with hA|hA
  · simpa only [hA,Finset.card_empty,Nat.cast_zero] using hB
  · obtain ⟨p,hp⟩ := hA
    have hsub : A⊆Pts.filter (fun q => distance p q≤rho) := by
      intro q hq
      exact Finset.mem_filter.mpr ⟨hAP hq,hdiam p hp q hq⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hballs p (hAP hp))

/-- Native finite A.2 representative construction from literal strips and
original point-ball counts. Richness, pairwise overlaps, the representative
count, and the actual covering representative for every rich tube are all
derived. The exact widening is 11*w/rho on the bounded original square. -/
theorem finite_rich_strip_representatives
    {T : Type*} [DecidableEq T]
    (Candidates : Finset T) (Pts : Finset (ℝ × ℝ)) (a b c : T → ℝ)
    (w rho lam eps : ℝ) (hPts : Pts.Nonempty)
    (hw : 0≤w) (hrho : 0<rho) (hrho1 : rho≤1)
    (hlam : 0<lam) (heps : 0≤eps) (hsmall : eps≤lam^2/2)
    (hbox : ∀ p∈Pts, |p.1|≤1 ∧ |p.2|≤1)
    (hnorm : ∀ i∈Candidates, |a i|≤1 ∧ |b i|≤1 ∧ (|a i|=1 ∨ |b i|=1))
    (hballs : ∀ p∈Pts,
      ((Pts.filter (fun q => boxDistance p q≤rho)).card : ℝ)≤eps*Pts.card) :
    ∃ F : Finset T, F⊆Candidates ∧
      (∀ i∈F, lam*(Pts.card : ℝ)≤(support Pts a b c w i).card) ∧
      ((F:Set T).Pairwise (compatible (support Pts a b c w) boxDistance rho)) ∧
      ((RichFamilyIncidenceBound.incidences F (support Pts a b c w)).card : ℝ)≤2*Pts.card ∧
      lam*(F.card : ℝ)≤2 ∧
      ∀ i∈Candidates, lam*(Pts.card : ℝ)≤(support Pts a b c w i).card →
        ∃ j∈F, ∀ z∈Pts, |residual (a i) (b i) (c i) z|≤w →
          |residual (a j) (b j) (c j) z|≤11*w/rho := by
  classical
  let S := support Pts a b c w
  let Rich := Candidates.filter (fun i => lam*(Pts.card : ℝ)≤(S i).card)
  obtain ⟨F,hFR,hpair,hcover⟩ := exists_original_representatives Rich S boxDistance rho
  have hFC : F⊆Candidates := hFR.trans (Finset.filter_subset _ _)
  have hrichF : ∀ i∈F, lam*(Pts.card : ℝ)≤(S i).card :=
    fun i hi => (Finset.mem_filter.mp (hFR hi)).2
  have hsub (i : T) : S i⊆Pts := Finset.filter_subset _ _
  have hcross (i : T) (hi : i∈F) (j : T) (hj : j∈F) (hne : i≠j) :
      ((S i∩S j).card : ℝ)≤eps*Pts.card := by
    exact diameter_support_card_bound Pts (S i∩S j) boxDistance rho (eps*Pts.card)
      (mul_nonneg heps (Nat.cast_nonneg _)) (Finset.inter_subset_left.trans (hsub i))
      (hpair hi hj hne) hballs
  have hcounts := RichFamilyIncidenceBound.rich_family_cardinality F Pts S hPts
    hlam heps hsmall (fun i _ => hsub i) hrichF hcross
  refine ⟨F,hFC,hrichF,hpair,hcounts.1,hcounts.2,?_⟩
  intro i hi hri
  by_cases hiF : i∈F
  · refine ⟨i,hiF,?_⟩
    intro z _ hz
    have hwide : w≤11*w/rho := by
      apply (le_div_iff₀ hrho).mpr
      nlinarith only [mul_le_mul_of_nonneg_left hrho1 hw,hw]
    exact hz.trans hwide
  · have hiRich : i∈Rich := Finset.mem_filter.mpr ⟨hi,hri⟩
    obtain ⟨j,hj,p,hp,q,hq,hsep⟩ := hcover i hiRich hiF
    obtain ⟨hpi,hpj⟩ := Finset.mem_inter.mp hp
    obtain ⟨hqi,hqj⟩ := Finset.mem_inter.mp hq
    have hpP : p∈Pts := hsub i hpi
    have hpI : |residual (a i) (b i) (c i) p|≤w := (Finset.mem_filter.mp hpi).2
    have hqI : |residual (a i) (b i) (c i) q|≤w := (Finset.mem_filter.mp hqi).2
    have hpJ : |residual (a j) (b j) (c j) p|≤w := (Finset.mem_filter.mp hpj).2
    have hqJ : |residual (a j) (b j) (c j) q|≤w := (Finset.mem_filter.mp hqj).2
    obtain ⟨hai,hbi,hunit⟩ := hnorm i hi
    obtain ⟨haj,hbj,_hunitj⟩ := hnorm j (hFC hj)
    refine ⟨j,hj,?_⟩
    intro z hzP hzI
    have hdx : |z.1-p.1|≤2 := (abs_sub _ _).trans (by linarith [(hbox z hzP).1,(hbox p hpP).1])
    have hdy : |z.2-p.2|≤2 := (abs_sub _ _).trans (by linarith [(hbox z hzP).2,(hbox p hpP).2])
    exact long_overlap_containment (a i) (b i) (a j) (b j) (c i) (c j) w rho p q z
      hw hrho hrho1 hai hbi haj hbj hunit hpI hqI hpJ hqJ hzI hsep hdx hdy

end NativeRichStripRepresentatives
