import Theorems.Thm_StickyKakeya4_planar_original_dyadic_bsg
import Theorems.Thm_StickyKakeya4_planar_rounded_sumset_cover

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000
open scoped Pointwise
noncomputable section
namespace VectorIntegerBinRealBSG
open PlanarShiftedNearEnergy PlanarRoundedSumsetCover ActualPlanarRoundedEnergy
open TwoTubePathCollisionCount

/-- The literal realization of one coupled integer-vector bin. -/
def realGrid (eta : ℝ) (S : Finset (ℤ×ℤ)) : Finset (ℝ×ℝ) :=
  S.image (synthesis eta)

lemma synthesis_injective {eta : ℝ} (heta : 0 < eta) :
    Function.Injective (synthesis eta) := by
  intro s t h
  have h1 : eta*(s.1:ℝ) = eta*(t.1:ℝ) := congrArg Prod.fst h
  have h2 : eta*(s.2:ℝ) = eta*(t.2:ℝ) := congrArg Prod.snd h
  apply Prod.ext
  · exact_mod_cast mul_left_cancel₀ (ne_of_gt heta) h1
  · exact_mod_cast mul_left_cancel₀ (ne_of_gt heta) h2

lemma real_grid_card {eta : ℝ} (heta : 0 < eta) (S : Finset (ℤ×ℤ)) :
    (realGrid eta S).card = S.card :=
  Finset.card_image_of_injective _ (synthesis_injective heta)

private lemma scaled_integer_separation {eta : ℝ} (heta : 0 < eta)
    {s t : ℤ} (hst : s ≠ t) : eta ≤ |eta*(s:ℝ)-eta*(t:ℝ)| := by
  have hi : (1:ℤ) ≤ |s-t| := by
    rcases le_total s t with h|h
    · rw [abs_of_nonpos (sub_nonpos.mpr h)]
      omega
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      omega
  have hr : (1:ℝ) ≤ |(s:ℝ)-(t:ℝ)| := by exact_mod_cast hi
  calc
    eta = eta*1 := by ring
    _ ≤ eta*|(s:ℝ)-(t:ℝ)| := mul_le_mul_of_nonneg_left hr heta.le
    _ = _ := by rw [← mul_sub, abs_mul, abs_of_pos heta]

lemma real_grid_separated {eta : ℝ} (heta : 0 < eta) (S : Finset (ℤ×ℤ)) :
    ∀ x ∈ realGrid eta S, ∀ y ∈ realGrid eta S, x ≠ y → eta ≤ ‖x-y‖ := by
  intro x hx y hy hxy
  obtain ⟨s, _hs, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨t, _ht, rfl⟩ := Finset.mem_image.mp hy
  have hst : s ≠ t := fun h => hxy (congrArg (synthesis eta) h)
  change eta ≤ max |eta*(s.1:ℝ)-eta*(t.1:ℝ)| |eta*(s.2:ℝ)-eta*(t.2:ℝ)|
  by_cases h1 : s.1 = t.1
  · have h2 : s.2 ≠ t.2 := fun h => hst (Prod.ext h1 h)
    exact (scaled_integer_separation heta h2).trans (le_max_right _ _)
  · exact (scaled_integer_separation heta h1).trans (le_max_left _ _)

/-- Collision cardinality transport retains a single coupled label. -/
lemma collisions_image_card {P Q R : Type*}
    [DecidableEq P] [DecidableEq Q] [DecidableEq R]
    (A : Finset P) (g : P → Q) (f : Q → R) (hg : Set.InjOn g A) :
    (collisions A (fun p => f (g p))).card = (collisions (A.image g) f).card := by
  apply Finset.card_bij (fun p _ => (g p.1,g p.2))
  · intro p hp
    obtain ⟨hp₁,hp₂,heq⟩ := (mem_collisions A (fun p => f (g p)) p).mp hp
    exact (mem_collisions (A.image g) f _).mpr ⟨Finset.mem_image_of_mem g hp₁,
      Finset.mem_image_of_mem g hp₂,heq⟩
  · intro p hp q hq heq
    obtain ⟨hp₁,hp₂,_⟩ := (mem_collisions A (fun p => f (g p)) p).mp hp
    obtain ⟨hq₁,hq₂,_⟩ := (mem_collisions A (fun p => f (g p)) q).mp hq
    exact Prod.ext (hg hp₁ hq₁ (congrArg Prod.fst heq))
      (hg hp₂ hq₂ (congrArg Prod.snd heq))
  · intro q hq
    obtain ⟨hq₁,hq₂,heq⟩ := (mem_collisions (A.image g) f q).mp hq
    obtain ⟨a,ha,hea⟩ := Finset.mem_image.mp hq₁
    obtain ⟨b,hb,heb⟩ := Finset.mem_image.mp hq₂
    refine ⟨(a,b),(mem_collisions A (fun p => f (g p)) _).mpr ⟨ha,hb,?_⟩,?_⟩
    · simpa only [hea,heb] using heq
    · exact Prod.ext hea heb

/-- Coupled exact integer-sum energy lifts to actual original planar near-sum
energy. Only the difference of the original A rounding errors remains. -/
theorem integer_energy_le_original_near
    (A : Finset (ℝ×ℝ)) (S : Finset (ℤ×ℤ)) {delta : ℝ} (hdelta : 0 < delta)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → delta/2 ≤ ‖a-b‖) :
    Finset.addEnergy (A.image (roundPoint (delta/2))) S ≤
      (coordinateNearPairs ((realGrid (delta/2) S).product A)
        (fun p => p.1+p.2) delta).card := by
  classical
  have heta : 0 < delta/2 := by positivity
  let g : (ℝ×ℝ) × (ℤ×ℤ) → (ℤ×ℤ) × (ℤ×ℤ) :=
    fun p => (roundPoint (delta/2) p.1,p.2)
  have hinj : Set.InjOn g (A.product S) := by
    intro p hp q hq heq
    have hs : p.2=q.2 := by
      simpa only [g] using congrArg (fun r : (ℤ×ℤ)×(ℤ×ℤ) => r.2) heq
    have ha : roundPoint (delta/2) p.1=roundPoint (delta/2) q.1 := by
      simpa only [g] using congrArg (fun r : (ℤ×ℤ)×(ℤ×ℤ) => r.1) heq
    exact Prod.ext ((planar_rounding_injOn A hdelta hsep) (Finset.mem_product.mp hp).1
      (Finset.mem_product.mp hq).1 ha) hs
  have him : (A.product S).image g = (A.image (roundPoint (delta/2))).product S := by
    ext q
    constructor
    · intro hq
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨ha,hs⟩ := Finset.mem_product.mp hp
      exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ ha,hs⟩
    · intro hq
      obtain ⟨ha,hs⟩ := Finset.mem_product.mp hq
      obtain ⟨a,ha,heq⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image.mpr ⟨(a,q.2),Finset.mem_product.mpr ⟨ha,hs⟩,Prod.ext heq rfl⟩
  have hcoll := collisions_image_card (A.product S) g (fun p => p.1+p.2) hinj
  rw [him] at hcoll
  have heq : (collisions (A.product S) (fun p => roundPoint (delta/2) p.1+p.2)).card =
      Finset.addEnergy (A.image (roundPoint (delta/2))) S := by
    calc
      _ = _ := hcoll
      _ = _ := by simpa only [collisions,Finset.product_eq_sprod] using
        (Finset.addEnergy_eq_card_filter (A.image (roundPoint (delta/2))) S).symm
  rw [← heq]
  apply Finset.card_le_card_of_injOn
    (fun z : ((ℝ×ℝ)×(ℤ×ℤ)) × ((ℝ×ℝ)×(ℤ×ℤ)) =>
      ((synthesis (delta/2) z.1.2,z.1.1),(synthesis (delta/2) z.2.2,z.2.1)))
  · intro z hz
    obtain ⟨h1,h2,hlabel⟩ := (mem_collisions _ _ z).mp hz
    obtain ⟨ha,hs⟩ := Finset.mem_product.mp h1
    obtain ⟨hb,ht⟩ := Finset.mem_product.mp h2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ hs,ha⟩,Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ ht,hb⟩⟩,?_,?_⟩
    · have ea := ActualRoundedAdditiveEnergy.round_error heta z.1.1.1
      have eb := ActualRoundedAdditiveEnergy.round_error heta z.2.1.1
      have hreal := congrArg (fun q : ℤ×ℤ => (delta/2)*(q.1:ℝ)) hlabel
      simp only [Prod.fst_add,roundPoint,Int.cast_add] at hreal
      change |(delta/2)*(z.1.2.1:ℝ)+z.1.1.1-((delta/2)*(z.2.2.1:ℝ)+z.2.1.1)| ≤ delta
      exact abs_le.mpr ⟨by nlinarith only [ea.1, ea.2, eb.1, eb.2, hreal, hdelta],
        by nlinarith only [ea.1, ea.2, eb.1, eb.2, hreal, hdelta]⟩
    · have ea := ActualRoundedAdditiveEnergy.round_error heta z.1.1.2
      have eb := ActualRoundedAdditiveEnergy.round_error heta z.2.1.2
      have hreal := congrArg (fun q : ℤ×ℤ => (delta/2)*(q.2:ℝ)) hlabel
      simp only [Prod.snd_add,roundPoint,Int.cast_add] at hreal
      change |(delta/2)*(z.1.2.2:ℝ)+z.1.1.2-((delta/2)*(z.2.2.2:ℝ)+z.2.1.2)| ≤ delta
      exact abs_le.mpr ⟨by nlinarith only [ea.1, ea.2, eb.1, eb.2, hreal, hdelta],
        by nlinarith only [ea.1, ea.2, eb.1, eb.2, hreal, hdelta]⟩
  · intro z _ w _ h
    have ha : z.1.1=w.1.1 := congrArg (fun q => q.1.2) h
    have hb : z.2.1=w.2.1 := congrArg (fun q => q.2.2) h
    have hs := (synthesis_injective heta) (congrArg (fun q => q.1.1) h)
    have ht := (synthesis_injective heta) (congrArg (fun q => q.2.1) h)
    exact Prod.ext (Prod.ext ha hs) (Prod.ext hb ht)

/-- Integer-bin planar dyadic BSG, with K and the dyadic cutoff chosen before
nu, A and S. The real near-energy is derived from the coupled integer energy. -/
theorem integer_bin_planar_dyadic_bsg {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ K n0 : ℕ, 0 < K ∧ ∀ n : ℕ, n0 ≤ n →
      ∀ nu : ℝ, 0 < nu → nu ≤ 1 →
      ∀ A : Finset (ℝ×ℝ), ∀ S : Finset (ℤ×ℤ), A.Nonempty → S.Nonempty →
      (∀ a ∈ A, |a.1| ≤ 1 ∧ |a.2| ≤ 1) →
      (∀ x ∈ realGrid (((2 : ℝ)^n)⁻¹/2) S, |x.1| ≤ 4 ∧ |x.2| ≤ 4) →
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ((2 : ℝ)^n)⁻¹/2 ≤ ‖a-b‖) →
      nu*(A.card : ℝ)*(S.card : ℝ)^2 ≤
        (Finset.addEnergy (A.image (roundPoint (((2 : ℝ)^n)⁻¹/2))) S : ℝ) →
      ∃ X' A' : Finset (ℝ×ℝ),
        X' ⊆ realGrid (((2 : ℝ)^n)⁻¹/2) S ∧ A' ⊆ A ∧
        nu^K * (((2 : ℝ)^n)⁻¹)^epsilon * (S.card : ℝ) ≤ X'.card ∧
        nu^K * (((2 : ℝ)^n)⁻¹)^epsilon * (A.card : ℝ) ≤ A'.card ∧
        ∀ u v : ℕ,
          (((A'+u•X'-v•X').image (roundPoint (((2 : ℝ)^n)⁻¹/2))).card : ℝ) ≤
            ((((2 : ℝ)^n)⁻¹)^(-epsilon*((u+v : ℕ) : ℝ))/nu^(K*(u+v)))*
              (A.card : ℝ) := by
  classical
  obtain ⟨K,n0,hK,hmain⟩ := PlanarOriginalDyadicBSG.coordinate_planar_dyadic_bsg hepsilon
  refine ⟨K,n0,hK,?_⟩
  intro n hn nu hnu hnu1 A S hA hS hAbound hXbound hAsep he
  have hdelta : 0 < ((2 : ℝ)^n)⁻¹ := by positivity
  have heta : 0 < ((2 : ℝ)^n)⁻¹/2 := by positivity
  have hcard := real_grid_card heta S
  have henergy := integer_energy_le_original_near A S hdelta hAsep
  have hnear : nu*((realGrid (((2 : ℝ)^n)⁻¹/2) S).card : ℝ)^2*(A.card : ℝ) ≤
      ((coordinateNearPairs ((realGrid (((2 : ℝ)^n)⁻¹/2) S).product A)
        (fun p => p.1+p.2) (((2 : ℝ)^n)⁻¹)).card : ℝ) := by
    rw [hcard]
    calc
      _ = nu*(A.card : ℝ)*(S.card : ℝ)^2 := by ring
      _ ≤ _ := he.trans (Nat.cast_le.mpr henergy)
  obtain ⟨X',A',hX',hA',hXcard,hAcard,hcover⟩ :=
    hmain n hn nu hnu hnu1 (realGrid (((2 : ℝ)^n)⁻¹/2) S) A (hS.image _) hA
      hXbound hAbound (real_grid_separated heta S) hAsep hnear
  rw [hcard] at hXcard
  exact ⟨X',A',hX',hA',hXcard,hAcard,hcover⟩

end VectorIntegerBinRealBSG
