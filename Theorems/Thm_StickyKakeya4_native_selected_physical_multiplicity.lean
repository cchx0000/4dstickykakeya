import Theorems.Thm_StickyKakeya4_native_original_slice_ball_population
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000
noncomputable section
namespace NativeSelectedPhysicalMultiplicity
open Classical Finset SelfUniform IncidenceBinTransfer NativeOriginalSlicePopulation
open scoped BigOperators
variable {T : Type*}

def multiplicity (B : Finset (T × Cell)) : ℝ :=
  (B.card : ℝ) / (B.image Prod.snd).card

def refinementLoss (d L : ℕ) : ℕ := 4 * (4 * ((1 + d) + d)) ^ (((1 + d) + d) * L)

lemma refinementLoss_pos (d L : ℕ) : 0 < refinementLoss d L := by
  unfold refinementLoss
  positivity

/-- Full selected original fibers determine the original subset exactly. -/
lemma eq_pullback_of_whole_fibers
    (P : PhysicalRescalingIncidenceTransfer.Data T) (E B : Finset (T × Cell))
    (hE : E ⊆ P.incidences) (hbins : bins E P.cellBin = B)
    (hwhole : ∀ b ∈ B, binFiber E P.cellBin b = binFiber P.incidences P.cellBin b) :
    E = originalPullback P B := by
  ext a
  constructor
  · intro ha
    apply mem_filter.mpr
    refine ⟨hE ha, ?_⟩
    rw [← hbins]
    exact mem_image_of_mem _ ha
  · intro ha
    obtain ⟨haI, haB⟩ := mem_filter.mp ha
    have hf : a ∈ binFiber P.incidences P.cellBin (binLabel P.cellBin a) :=
      mem_binFiber.mpr ⟨haI, rfl⟩
    rw [← hwhole _ haB] at hf
    exact (mem_binFiber.mp hf).1

lemma selected_capacity (P : PhysicalRescalingIncidenceTransfer.Data T)
    (hP : P.Hypotheses) (B : Finset (T × Cell)) :
    (originalPullback P B).card ≤ P.N * B.card := by
  rw [originalPullback_mass]
  unfold mass originalWeight
  calc
    _ ≤ ∑ _b ∈ B, P.N := sum_le_sum (fun b _hb => P.incidence_fiber_bound hP b)
    _ = _ := by simp [Nat.mul_comm]

lemma selected_support_gain (P : PhysicalRescalingIncidenceTransfer.Data T)
    (B : Finset (T × Cell)) (hB : B ⊆ P.newIncidences) :
    P.m * (B.image Prod.snd).card ≤ P.oldSupport.card := by
  have hs : B.image Prod.snd ⊆ P.newSupport := Finset.image_subset_image hB
  exact (Nat.mul_le_mul_left _ (card_le_card hs)).trans
    (mul_card_newCells_le P.incidences P.cellBin P.m)

/-- Multiplicity transfer on the EXACT further selected support. Its only loss
is the actual retained original incidence mass; no new multiplicity premise. -/
theorem selected_cross_multiplicity
    (P : PhysicalRescalingIncidenceTransfer.Data T) (hP : P.Hypotheses)
    (B : Finset (T × Cell)) (hB : B ⊆ P.newIncidences) (F : ℕ)
    (hret : P.incidences.card ≤ F * (originalPullback P B).card) :
    P.m * P.incidences.card * (B.image Prod.snd).card ≤
      F * P.N * B.card * P.oldSupport.card := by
  calc
    _ = P.incidences.card * (P.m * (B.image Prod.snd).card) := by ring
    _ ≤ (F * (P.N * B.card)) * P.oldSupport.card :=
      Nat.mul_le_mul (hret.trans (Nat.mul_le_mul_left F (selected_capacity P hP B)))
        (selected_support_gain P B hB)
    _ = _ := by ring

/-- The physical density pays for the geometric capacity, also AFTER the
simultaneous spatial/phase selection. -/
theorem selected_density_cross_multiplicity
    (P : PhysicalRescalingIncidenceTransfer.Data T) (hP : P.Hypotheses)
    (B : Finset (T × Cell)) (hB : B ⊆ P.newIncidences) (F : ℕ)
    (hret : P.incidences.card ≤ F * (originalPullback P B).card) :
    P.lam * P.incidences.card * (B.image Prod.snd).card ≤
      2 * P.K * F * B.card * P.oldSupport.card := by
  have hN : (0 : ℝ) < P.N := by exact_mod_cast hP.N_pos
  have hcross : (P.m : ℝ) * P.incidences.card * (B.image Prod.snd).card ≤
      F * P.N * B.card * P.oldSupport.card := by
    exact_mod_cast selected_cross_multiplicity P hP B hB F hret
  apply (mul_le_mul_iff_right₀ hN).mp
  calc
    (P.N : ℝ) * (P.lam * P.incidences.card * (B.image Prod.snd).card) =
        (P.lam * P.N) * ((P.incidences.card : ℝ) * (B.image Prod.snd).card) := by ring
    _ ≤ (2 * P.K * P.m) * ((P.incidences.card : ℝ) * (B.image Prod.snd).card) :=
      mul_le_mul_of_nonneg_right P.density_le_threshold (by positivity)
    _ = (2 * P.K) * ((P.m : ℝ) * P.incidences.card * (B.image Prod.snd).card) := by ring
    _ ≤ (2 * P.K) * (F * P.N * B.card * P.oldSupport.card) :=
      mul_le_mul_of_nonneg_left hcross (mul_nonneg (by norm_num) P.K_pos.le)
    _ = (P.N : ℝ) * (2 * P.K * F * B.card * P.oldSupport.card) := by ring

/-- The original multiplicity lower bound survives on the very same selected
support on which the horizontal ball and phase populations are uniform. -/
theorem selected_density_multiplicity
    (P : PhysicalRescalingIncidenceTransfer.Data T) (hP : P.Hypotheses)
    (hne : P.incidences.Nonempty) (B : Finset (T × Cell))
    (hB : B ⊆ P.newIncidences) (hneB : B.Nonempty) (F : ℕ)
    (hret : P.incidences.card ≤ F * (originalPullback P B).card) :
    P.lam * P.oldMultiplicity ≤ (2 * P.K * F) * multiplicity B := by
  have hS : (0 : ℝ) < P.oldSupport.card := by
    exact_mod_cast card_pos.mpr (hne.image Prod.snd)
  have hS' : (0 : ℝ) < (B.image Prod.snd).card := by
    exact_mod_cast card_pos.mpr (hneB.image Prod.snd)
  dsimp [PhysicalRescalingIncidenceTransfer.Data.oldMultiplicity, multiplicity]
  rw [← mul_div_assoc, ← mul_div_assoc]
  exact (div_le_div_iff₀ hS hS').mpr (selected_density_cross_multiplicity P hP B hB F hret)

/-- A source count consequence of original shading density. This contains only
actual original tube/support cardinalities, not a postulated output exponent. -/
theorem source_count_lower_multiplicity
    (P : PhysicalRescalingIncidenceTransfer.Data T) (hP : P.Hypotheses)
    (hne : P.incidences.Nonempty) (B : Finset (T × Cell))
    (hB : B ⊆ P.newIncidences) (hneB : B.Nonempty) (F : ℕ) (hF : 0 < F)
    (hret : P.incidences.card ≤ F * (originalPullback P B).card) :
    P.lam ^ 2 * (usedTubes P.incidences).card /
        (2 * P.K * F * P.δ * P.oldSupport.card) ≤ multiplicity B := by
  have hS : (0 : ℝ) < P.oldSupport.card := by exact_mod_cast card_pos.mpr (hne.image Prod.snd)
  have hF' : (0 : ℝ) < F := by exact_mod_cast hF
  have hK := P.K_pos
  have hd := hP.delta_pos
  have hD : 0 < 2 * P.K * F * P.δ * P.oldSupport.card := by positivity
  apply (div_le_iff₀ hD).mpr
  have hmul := selected_density_multiplicity P hP hne B hB hneB F hret
  have hsource : P.lam * (usedTubes P.incidences).card ≤
      P.δ * P.oldMultiplicity * P.oldSupport.card := by
    calc
      _ ≤ P.δ * P.incidences.card := hP.density
      _ = _ := by
        dsimp [PhysicalRescalingIncidenceTransfer.Data.oldMultiplicity]
        rw [mul_assoc, div_mul_cancel₀ _ hS.ne']
  calc
    P.lam ^ 2 * (usedTubes P.incidences).card =
        P.lam * (P.lam * (usedTubes P.incidences).card) := by ring
    _ ≤ P.lam * (P.δ * P.oldMultiplicity * P.oldSupport.card) :=
      mul_le_mul_of_nonneg_left hsource hP.lambda_pos.le
    _ = (P.δ * P.oldSupport.card) * (P.lam * P.oldMultiplicity) := by ring
    _ ≤ (P.δ * P.oldSupport.card) * ((2 * P.K * F) * multiplicity B) :=
      mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = _ := by ring
end NativeSelectedPhysicalMultiplicity
