import Theorems.Thm_StickyKakeya4_native_rich_strip_representatives

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

open scoped BigOperators
noncomputable section
namespace TransverseOriginalStripPoints
open PlanarStripIntersection NativeRichStripRepresentatives

def common {T : Type*} (Pts : Finset (ℝ × ℝ)) (a b c : T → ℝ)
    (W theta : ℝ) (i j : T) : Finset (ℝ × ℝ) := by
  classical
  exact Pts.filter (fun p => theta≤|determinant (a i) (b i) (a j) (b j)| ∧
    |PlanarStripIntersection.residual (a i) (b i) (c i) p|≤W ∧
    |PlanarStripIntersection.residual (a j) (b j) (c j) p|≤W)

def transverse {T : Type*} [DecidableEq T]
    (F : Finset T) (Pts : Finset (ℝ × ℝ)) (a b c : T → ℝ) (W theta : ℝ) :
    Finset (ℝ × ℝ) := F.biUnion (fun i => F.biUnion (fun j => common Pts a b c W theta i j))

/-- The actual transverse overlap is controlled by an ORIGINAL point ball. -/
theorem common_card_bound
    {T : Type*} (Pts : Finset (ℝ × ℝ)) (a b c : T → ℝ)
    (W theta zeta : ℝ) (hw : 0≤W) (htheta : 0<theta) (hzeta : 0≤zeta)
    (i j : T) (hai : |a i|≤1) (hbi : |b i|≤1) (haj : |a j|≤1) (hbj : |b j|≤1)
    (hballs : ∀ p∈Pts, ((Pts.filter (fun q => boxDistance p q≤4*W/theta)).card : ℝ)≤zeta*Pts.card) :
    ((common Pts a b c W theta i j).card : ℝ)≤zeta*Pts.card := by
  classical
  apply diameter_support_card_bound Pts (common Pts a b c W theta i j) boxDistance
    (4*W/theta) (zeta*Pts.card) (mul_nonneg hzeta (Nat.cast_nonneg _))
    (Finset.filter_subset _ _) ?_ hballs
  intro p hp q hq
  obtain ⟨_,hdet,hpi,hpj⟩ := Finset.mem_filter.mp hp
  obtain ⟨_,_hdetq,hqi,hqj⟩ := Finset.mem_filter.mp hq
  exact transverse_intersection_ball (a i) (b i) (a j) (b j) (c i) (c j)
    W theta p q hw htheta hai hbi haj hbj hpi hqi hpj hqj hdet

/-- Only the ACTUAL selected representatives enter this finite union bound. -/
theorem transverse_card_bound
    {T : Type*} [DecidableEq T]
    (F : Finset T) (Pts : Finset (ℝ × ℝ)) (a b c : T → ℝ)
    (W theta zeta : ℝ) (hw : 0≤W) (htheta : 0<theta) (hzeta : 0≤zeta)
    (hnorm : ∀ i∈F, |a i|≤1 ∧ |b i|≤1)
    (hballs : ∀ p∈Pts, ((Pts.filter (fun q => boxDistance p q≤4*W/theta)).card : ℝ)≤zeta*Pts.card) :
    ((transverse F Pts a b c W theta).card : ℝ)≤zeta*(Pts.card : ℝ)*(F.card : ℝ)^2 := by
  have hnat : (transverse F Pts a b c W theta).card ≤
      ∑ i∈F, ∑ j∈F, (common Pts a b c W theta i j).card := by
    apply (Finset.card_biUnion_le).trans
    exact Finset.sum_le_sum (fun _ _ => Finset.card_biUnion_le)
  have hr : ((transverse F Pts a b c W theta).card : ℝ) ≤
      ∑ i∈F, ∑ j∈F, ((common Pts a b c W theta i j).card : ℝ) := by exact_mod_cast hnat
  calc
    _ ≤ _ := hr
    _ ≤ ∑ _i∈F, ∑ _j∈F, zeta*(Pts.card : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact common_card_bound Pts a b c W theta zeta hw htheta hzeta i j
        (hnorm i hi).1 (hnorm i hi).2 (hnorm j hj).1 (hnorm j hj).2 hballs
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; ring

/-- Cross-multiplied native count, using the derived lambda*|F|<=2 bound. -/
theorem transverse_card_from_rich_family
    {T : Type*} [DecidableEq T]
    (F : Finset T) (Pts : Finset (ℝ × ℝ)) (a b c : T → ℝ)
    (W theta zeta lam : ℝ) (hw : 0≤W) (htheta : 0<theta) (hzeta : 0≤zeta)
    (hlam : 0≤lam) (hcount : lam*(F.card : ℝ)≤2)
    (hnorm : ∀ i∈F, |a i|≤1 ∧ |b i|≤1)
    (hballs : ∀ p∈Pts, ((Pts.filter (fun q => boxDistance p q≤4*W/theta)).card : ℝ)≤zeta*Pts.card) :
    lam^2*((transverse F Pts a b c W theta).card : ℝ)≤4*zeta*Pts.card := by
  have h := mul_le_mul_of_nonneg_left
    (transverse_card_bound F Pts a b c W theta zeta hw htheta hzeta hnorm hballs) (sq_nonneg lam)
  have hs := pow_le_pow_left₀ (mul_nonneg hlam (Nat.cast_nonneg _)) hcount 2
  have hs' := mul_le_mul_of_nonneg_left hs (mul_nonneg hzeta (Nat.cast_nonneg Pts.card))
  nlinarith only [h,hs']

/-- A nontransverse original point has one genuine representative strip
containing all rich partners, with exact width 3W+2theta. -/
theorem nontransverse_common_strip
    {T : Type*} [DecidableEq T]
    (F : Finset T) (Pts : Finset (ℝ × ℝ)) (a b c : T → ℝ)
    (W theta : ℝ) (p q : ℝ × ℝ) (hpP : p∈Pts) (hqP : q∈Pts)
    (hbox : ∀ z∈Pts, |z.1|≤1 ∧ |z.2|≤1)
    (hgood : p∉transverse F Pts a b c W theta)
    (i j : T) (hi : i∈F) (hj : j∈F)
    (hunit : |a i|=1 ∨ |b i|=1) (haj : |a j|≤1) (hbj : |b j|≤1)
    (hpi : |PlanarStripIntersection.residual (a i) (b i) (c i) p|≤W)
    (hqi : |PlanarStripIntersection.residual (a i) (b i) (c i) q|≤W)
    (hpj : |PlanarStripIntersection.residual (a j) (b j) (c j) p|≤W) :
    |PlanarStripIntersection.residual (a j) (b j) (c j) q|≤3*W+2*theta := by
  classical
  have hdet : |determinant (a i) (b i) (a j) (b j)|<theta := by
    by_contra hn
    apply hgood
    exact Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_biUnion.mpr
      ⟨j,hj,Finset.mem_filter.mpr ⟨hpP,le_of_not_gt hn,hpi,hpj⟩⟩⟩
  have hx : |q.1-p.1|≤2 := (abs_sub _ _).trans (by linarith [(hbox q hqP).1,(hbox p hpP).1])
  have hy : |q.2-p.2|≤2 := (abs_sub _ _).trans (by linarith [(hbox q hqP).2,(hbox p hpP).2])
  have h := bounded_strip_containment (a i) (b i) (a j) (b j) (c i) (c j)
    W p q hunit haj hbj hpi hqi hpj hx hy
  linarith

end TransverseOriginalStripPoints
