import Theorems.Thm_StickyKakeya4_native_selected_physical_multiplicity
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2600000
noncomputable section
namespace NativeUniformMultiplicityRestriction
open Classical Finset SelfUniform NativeWeightedPointPopulations NativeOriginalSlicePopulation
open NativeSelectedPhysicalMultiplicity IncidenceBinTransfer
open scoped BigOperators

lemma projectedWeight_mono {ι X : Type*} [DecidableEq ι] [DecidableEq X]
    (w : ι → ℕ) (p : ι → X) {J I : Finset ι} (hJI : J ⊆ I) (x : X) :
    projectedWeight w p J x ≤ projectedWeight w p I x := by
  exact sum_le_sum_of_subset hJI

lemma projectedWeight_total {ι X : Type*} [DecidableEq ι] [DecidableEq X]
    (w : ι → ℕ) (p : ι → X) (I : Finset ι) :
    mass (projectedWeight w p I) (I.image p)=mass w I := by
  rw [projectedWeight_mass_preimage]
  congr 1
  exact filter_eq_self.mpr (fun a ha => mem_image_of_mem p ha)

lemma uniform_point_mass_bound {ι X : Type*} [DecidableEq ι] [DecidableEq X]
    (w : ι → ℕ) (p : ι → X) (I : Finset ι) (C : ℕ)
    (hpoint : ∀x∈I.image p,∀y∈I.image p,projectedWeight w p I x ≤ C*projectedWeight w p I y)
    {x : X} (hx : x∈I.image p) :
    projectedWeight w p I x*(I.image p).card ≤ C*mass w I := by
  calc
    _ = ∑_y∈I.image p,projectedWeight w p I x := by simp [Nat.mul_comm]
    _ ≤ ∑y∈I.image p,C*projectedWeight w p I y := sum_le_sum (fun y hy => hpoint x hx y hy)
    _ = C*mass (projectedWeight w p I) (I.image p) := by rw [mass,mul_sum]
    _ = _ := by rw [projectedWeight_total]

/-- Uniform original point degrees control every genuine further restriction.
This is a finite replacement for the false general monotonicity of average
multiplicity under shading restriction. -/
theorem subset_weighted_mass_cross {ι X : Type*} [DecidableEq ι] [DecidableEq X]
    (w : ι → ℕ) (p : ι → X) (I J : Finset ι) (hJI : J ⊆ I) (C : ℕ)
    (hpoint : ∀x∈I.image p,∀y∈I.image p,projectedWeight w p I x ≤ C*projectedWeight w p I y) :
    mass w J*(I.image p).card ≤ C*mass w I*(J.image p).card := by
  rw [←projectedWeight_total w p J]
  change (∑x∈J.image p,projectedWeight w p J x)*(I.image p).card ≤ _
  rw [sum_mul]
  calc
    _ ≤ ∑_x∈J.image p,C*mass w I := by
      apply sum_le_sum
      intro x hx
      exact (Nat.mul_le_mul_right _ (projectedWeight_mono w p hJI x)).trans
        (uniform_point_mass_bound w p I C hpoint (image_subset_image hJI hx))
    _ = _ := by simp [Nat.mul_comm]

theorem weighted_card_cross {ι X : Type*} [DecidableEq ι] [DecidableEq X]
    (w : ι → ℕ) (p : ι → X) (I J : Finset ι) (hJI : J ⊆ I) (m N C : ℕ)
    (hlo : ∀a∈I,m ≤ w a) (hhi : ∀a∈I,w a ≤ N)
    (hpoint : ∀x∈I.image p,∀y∈I.image p,projectedWeight w p I x ≤ C*projectedWeight w p I y) :
    m*J.card*(I.image p).card ≤ C*N*I.card*(J.image p).card := by
  have hl : m*J.card ≤ mass w J := by
    calc
      _ = ∑_a∈J,m := by simp [Nat.mul_comm]
      _ ≤ _ := sum_le_sum (fun a ha => hlo a (hJI ha))
  have hu : mass w I ≤ N*I.card := by
    calc
      _ ≤ ∑_a∈I,N := sum_le_sum (fun a ha => hhi a ha)
      _ = _ := by simp [Nat.mul_comm]
  calc
    _ ≤ mass w J*(I.image p).card := Nat.mul_le_mul_right _ hl
    _ ≤ C*mass w I*(J.image p).card := subset_weighted_mass_cross w p I J hJI C hpoint
    _ ≤ C*(N*I.card)*(J.image p).card := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left C hu)
    _ = _ := by ring

/-- The actual heavy-fiber bounds and physical density pay for conversion
from weighted original point degrees to the coarse incidence multiplicity. -/
theorem selected_restriction_multiplicity {T : Type*}
    (P : PhysicalRescalingIncidenceTransfer.Data T) (hP : P.Hypotheses)
    (B : Finset (T × Cell)) (hB : B ⊆ P.newIncidences) (hBn : B.Nonempty)
    (Q : ℕ)
    (hpoint : ∀x∈B.image Prod.snd,∀y∈B.image Prod.snd,
      projectedWeight (originalWeight P) Prod.snd B x ≤ Q^2*projectedWeight (originalWeight P) Prod.snd B y)
    (J : Finset (T × Cell)) (hJB : J ⊆ B) :
    P.lam*multiplicity J ≤ (2*P.K*(Q:ℝ)^2)*multiplicity B := by
  by_cases hJn : J.Nonempty
  · have hcross := weighted_card_cross (originalWeight P) Prod.snd B J hJB P.m P.N (Q^2)
      (fun b hb => (mem_heavyBins.mp (hB hb)).2)
      (fun b _hb => P.incidence_fiber_bound hP b) hpoint
    have hBpos : (0:ℝ) < (B.image Prod.snd).card := by exact_mod_cast card_pos.mpr (hBn.image Prod.snd)
    have hJpos : (0:ℝ) < (J.image Prod.snd).card := by exact_mod_cast card_pos.mpr (hJn.image Prod.snd)
    have hratio : (P.m:ℝ)*multiplicity J ≤ (Q:ℝ)^2*P.N*multiplicity B := by
      dsimp [NativeSelectedPhysicalMultiplicity.multiplicity]
      rw [←mul_div_assoc,←mul_div_assoc]
      apply (div_le_div_iff₀ hJpos hBpos).mpr
      exact_mod_cast hcross
    have hm : (0:ℝ) < P.m := by exact_mod_cast P.m_pos
    have hmu : 0 ≤ multiplicity B := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    apply (mul_le_mul_iff_right₀ hm).mp
    calc
      _ = P.lam*((P.m:ℝ)*multiplicity J) := by ring
      _ ≤ P.lam*((Q:ℝ)^2*P.N*multiplicity B) := mul_le_mul_of_nonneg_left hratio hP.lambda_pos.le
      _ = (P.lam*P.N)*((Q:ℝ)^2*multiplicity B) := by ring
      _ ≤ (2*P.K*P.m)*((Q:ℝ)^2*multiplicity B) :=
        mul_le_mul_of_nonneg_right P.density_le_threshold (mul_nonneg (sq_nonneg _) hmu)
      _ = _ := by ring
  · rw [not_nonempty_iff_eq_empty.mp hJn]
    simp only [NativeSelectedPhysicalMultiplicity.multiplicity,card_empty,Nat.cast_zero,image_empty,div_zero,mul_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) P.K_pos.le) (sq_nonneg _))
      (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

/-- Construct the uniform coarse set from the actual physical incidences and
derive (110)'s restriction control on that very set. The point-uniformity
input is supplied internally by the existing simultaneous refinement. -/
theorem exists_restriction_control {T : Type*}
    (P : PhysicalRescalingIncidenceTransfer.Data T) (hP : P.Hypotheses)
    (hne : P.incidences.Nonempty) {L d : ℕ} (hL : 0 < L)
    (radii timeDiv : Fin d → ℕ) (offsetMesh slopeMesh : Fin d → ℝ) :
    ∃B ⊆ P.newIncidences,B.Nonempty ∧
      P.incidences.card ≤ refinementLoss d L*(originalPullback P B).card ∧
      (∀J ⊆ B,P.lam*multiplicity J ≤
        (2*P.K*(NativeSourceSizeBounds.radix P.incidences.card L:ℝ)^2)*multiplicity B) ∧
      (∀j : Fin d,∀a∈B,∀b∈B,
        degree (originalWeight P) (fun c e =>
          phaseLabel P (offsetMesh j) (slopeMesh j) (timeDiv j) c =
          phaseLabel P (offsetMesh j) (slopeMesh j) (timeDiv j) e) B a ≤
          NativeSourceSizeBounds.radix P.incidences.card L^2*
            degree (originalWeight P) (fun c e =>
              phaseLabel P (offsetMesh j) (slopeMesh j) (timeDiv j) c =
              phaseLabel P (offsetMesh j) (slopeMesh j) (timeDiv j) e) B b) := by
  obtain ⟨B,hB,hBn,hret,hpoint,_hspatial,hphase,_hcounts⟩ :=
    refine_original_incidence_labels P hP hne hL radii timeDiv offsetMesh slopeMesh
  exact ⟨B,hB,hBn,hret,fun J hJB => selected_restriction_multiplicity P hP B hB hBn _ hpoint J hJB,hphase⟩
end NativeUniformMultiplicityRestriction
