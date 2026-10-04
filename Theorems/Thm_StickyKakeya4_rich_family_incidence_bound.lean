import Theorems.Thm_StickyKakeya4_two_tube_path_collision_count
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

open scoped BigOperators
noncomputable section
namespace RichFamilyIncidenceBound
open TwoTubePathCollisionCount

def incidences {T P : Type*} (F : Finset T) (S : T → Finset P) : Finset (Σ _ : T, P) :=
  F.sigma S

/-- The second moment counts actual common original points of the supports. -/
theorem incidence_collision_count
    {T P : Type*} [DecidableEq T] [DecidableEq P]
    (F : Finset T) (S : T → Finset P) :
    (collisions (incidences F S) (fun z => z.2)).card =
      ∑ i∈F, ∑ j∈F, (S i∩S j).card := by
  have heq : (collisions (incidences F S) (fun z => z.2)).card =
      ((F.product F).sigma (fun ij => S ij.1∩S ij.2)).card := by
    apply Finset.card_bij (fun z _ => (⟨(z.1.1,z.2.1),z.1.2⟩ : Σ _ : T × T, P))
    · intro z hz
      obtain ⟨hz1,hz2,hp⟩ := (mem_collisions _ _ z).mp hz
      obtain ⟨hi,hpi⟩ := Finset.mem_sigma.mp hz1
      obtain ⟨hj,hpj⟩ := Finset.mem_sigma.mp hz2
      exact Finset.mem_sigma.mpr ⟨Finset.mem_product.mpr ⟨hi,hj⟩,
        Finset.mem_inter.mpr ⟨hpi,hp.symm ▸ hpj⟩⟩
    · intro z hz w hw h
      have hi : z.1.1=w.1.1 := congrArg (fun q : Σ _ : T × T, P => q.1.1) h
      have hj : z.2.1=w.2.1 := congrArg (fun q : Σ _ : T × T, P => q.1.2) h
      have hp : z.1.2=w.1.2 := congrArg (fun q : Σ _ : T × T, P => q.2) h
      have hzq := ((mem_collisions _ _ z).mp hz).2.2
      have hwq := ((mem_collisions _ _ w).mp hw).2.2
      have hq : z.2.2=w.2.2 := hzq.symm.trans (hp.trans hwq)
      exact Prod.ext (Sigma.ext hi (heq_of_eq hp)) (Sigma.ext hj (heq_of_eq hq))
    · intro q hq
      obtain ⟨hij,hp⟩ := Finset.mem_sigma.mp hq
      obtain ⟨hi,hj⟩ := Finset.mem_product.mp hij
      obtain ⟨hpi,hpj⟩ := Finset.mem_inter.mp hp
      exact ⟨(⟨q.1.1,q.2⟩,⟨q.1.2,q.2⟩),
        (mem_collisions _ _ _).mpr ⟨Finset.mem_sigma.mpr ⟨hi,hpi⟩,
          Finset.mem_sigma.mpr ⟨hj,hpj⟩,rfl⟩,rfl⟩
  rw [heq,Finset.card_sigma]
  rw [Finset.product_eq_sprod,Finset.sum_product]

/-- Cauchy uses the ACTUAL original point image, which lies in P. -/
theorem incidence_cauchy
    {T P : Type*} [DecidableEq T] [DecidableEq P]
    (F : Finset T) (Pts : Finset P) (S : T → Finset P)
    (hsub : ∀ i∈F, S i⊆Pts) :
    ((incidences F S).card : ℝ)^2 ≤ (Pts.card : ℝ)*
      ∑ i∈F, ∑ j∈F, ((S i∩S j).card : ℝ) := by
  have him : (incidences F S).image (fun z => z.2)⊆Pts := by
    intro p hp
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨hi,hp⟩ := Finset.mem_sigma.mp hz
    exact hsub z.1 hi hp
  have h := (square_card_le_image_mul_collisions (incidences F S) (fun z => z.2)).trans
    (Nat.mul_le_mul_right _ (Finset.card_le_card him))
  rw [incidence_collision_count] at h
  exact_mod_cast h

/-- Keep the diagonal term as total incidence I, not |F||P|. -/
theorem intersection_sum_upper
    {T P : Type*} [DecidableEq T] [DecidableEq P]
    (F : Finset T) (Pts : Finset P) (S : T → Finset P) {eps : ℝ} (heps : 0≤eps)
    (hcross : ∀ i∈F, ∀ j∈F, i≠j → ((S i∩S j).card : ℝ)≤eps*Pts.card) :
    (∑ i∈F, ∑ j∈F, ((S i∩S j).card : ℝ)) ≤
      (incidences F S).card+eps*(Pts.card : ℝ)*(F.card : ℝ)^2 := by
  have hpoint (i : T) (hi : i∈F) (j : T) (hj : j∈F) :
      ((S i∩S j).card : ℝ)≤(if j=i then ((S i).card : ℝ) else 0)+eps*Pts.card := by
    by_cases hij : j=i
    · subst j
      simp only [if_true,Finset.inter_self]
      exact le_add_of_nonneg_right (mul_nonneg heps (Nat.cast_nonneg _))
    · simpa only [hij,if_false,zero_add] using hcross i hi j hj (Ne.symm hij)
  have hsum := Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hpoint i hi j hj))
  have hrow (i : T) (hi : i∈F) :
      (∑ j∈F, ((if j=i then ((S i).card : ℝ) else 0)+eps*(Pts.card : ℝ))) =
        (S i).card+(F.card : ℝ)*(eps*Pts.card) := by
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_ite_eq',hi,if_true,Finset.sum_const,nsmul_eq_mul]
  have heq : (∑ i∈F, ∑ j∈F, ((if j=i then ((S i).card : ℝ) else 0)+eps*(Pts.card : ℝ))) =
      (incidences F S).card+eps*(Pts.card : ℝ)*(F.card : ℝ)^2 := by
    simp_rw [Finset.sum_congr rfl (fun i hi => hrow i hi)]
    rw [Finset.sum_add_distrib]
    have hc : (∑ i∈F, ((S i).card : ℝ))=((incidences F S).card : ℝ) := by
      exact_mod_cast (Finset.card_sigma F S).symm
    rw [hc]
    simp only [Finset.sum_const,nsmul_eq_mul]
    ring
  exact hsum.trans_eq heq

/-- Rich original supports with small pairwise overlap have total incidence
at most twice the original point count and at most 2/lambda representatives. -/
theorem rich_family_cardinality
    {T P : Type*} [DecidableEq T] [DecidableEq P]
    (F : Finset T) (Pts : Finset P) (S : T → Finset P) (hPts : Pts.Nonempty)
    {lam eps : ℝ} (hlam : 0<lam) (heps : 0≤eps) (hsmall : eps≤lam^2/2)
    (hsub : ∀ i∈F, S i⊆Pts)
    (hrich : ∀ i∈F, lam*(Pts.card : ℝ)≤(S i).card)
    (hcross : ∀ i∈F, ∀ j∈F, i≠j → ((S i∩S j).card : ℝ)≤eps*Pts.card) :
    ((incidences F S).card : ℝ)≤2*Pts.card ∧ lam*(F.card : ℝ)≤2 := by
  let I := ((incidences F S).card : ℝ)
  let M := (Pts.card : ℝ)
  let N := (F.card : ℝ)
  have hM : 0<M := by
    change (0:ℝ)<Pts.card
    exact_mod_cast hPts.card_pos
  have hI0 : 0≤I := Nat.cast_nonneg _
  have hN0 : 0≤N := Nat.cast_nonneg _
  have hlow : lam*M*N≤I := by
    have h := Finset.sum_le_sum hrich
    have hc : (∑ i∈F, ((S i).card : ℝ))=I := by
      dsimp [I,incidences]
      exact_mod_cast (Finset.card_sigma F S).symm
    rw [hc] at h
    simpa only [Finset.sum_const,nsmul_eq_mul,mul_comm,mul_left_comm,mul_assoc] using h
  have hcs := incidence_cauchy F Pts S hsub
  have hup := intersection_sum_upper F Pts S heps hcross
  have hupper : I^2≤M*I+eps*M^2*N^2 := by
    have h := hcs.trans (mul_le_mul_of_nonneg_left hup hM.le)
    nlinarith only [h]
  have hsquare := pow_le_pow_left₀ (mul_nonneg (mul_nonneg hlam.le hM.le) hN0) hlow 2
  have hsmall' := mul_le_mul_of_nonneg_right hsmall (by positivity : 0≤M^2*N^2)
  have hIquad : I^2≤2*M*I := by nlinarith only [hupper,hsquare,hsmall']
  have hI : I≤2*M := by
    by_contra h
    have hIpos : 0<I := (mul_pos (by norm_num) hM).trans (lt_of_not_ge h)
    have hprod := mul_pos hIpos (sub_pos.mpr (lt_of_not_ge h))
    nlinarith only [hIquad,hprod]
  have hN : lam*N≤2 := by
    apply (mul_le_mul_iff_right₀ hM).mp
    nlinarith only [hlow.trans hI]
  exact ⟨hI,hN⟩

end RichFamilyIncidenceBound
