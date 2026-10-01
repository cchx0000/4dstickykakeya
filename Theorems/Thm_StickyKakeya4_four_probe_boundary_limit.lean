import Theorems.Thm_StickyKakeya4_four_probe_boundary_firewall

open Filter
open scoped Topology

namespace StickyKakeya4

/-- The determinant of the Reeb/Maslov pencil varies continuously with both
the limiting graph plane and the probe time. -/
theorem continuous_det_pencil :
    Continuous (fun z : (Mat3 × Mat3) × ℝ =>
      Matrix.det (pencil z.1.1 z.1.2 z.2)) := by
  apply Continuous.matrix_det
  unfold pencil
  fun_prop

theorem continuous_det_matrix :
    Continuous (fun A : Mat3 => Matrix.det A) := by
  exact Continuous.matrix_det continuous_id

/-- The normalized flag equation is continuous in the graph frame, the Reeb
time, and the flag coordinate. -/
theorem continuous_pencil_mulVec :
    Continuous (fun z : ((Mat3 × Mat3) × ℝ) × E3 =>
      (pencil z.1.1.1 z.1.1.2 z.1.2).mulVec z.2) := by
  unfold pencil
  fun_prop

/-- Euclidean horizontal component of a frame vector. -/
def horizontalFrameVector (A : Mat3) (c : E3) : E3 :=
  WithLp.toLp 2 (A.mulVec c.ofLp)

theorem continuous_horizontalFrameVector :
    Continuous (fun z : Mat3 × E3 => horizontalFrameVector z.1 z.2) := by
  unfold horizontalFrameVector
  fun_prop

/-- Coherent four-probe output of an infinite concentration branch.  The same
sequence of graph planes is used at all four probes; only the four Reeb times
and normalized flag coordinates vary.  Thus the object records compatibility
across the whole boundary tower, not four unrelated subsequences.  Its residual
field is the vector incidence error from the manuscript, rather than an assumed
determinant limit. -/
structure FourProbeConcentrationLimit where
  approxA : ℕ → Mat3
  approxB : ℕ → Mat3
  approxTime : ℕ → Fin 4 → ℝ
  approxCoeff : ℕ → Fin 4 → E3
  limitA : Mat3
  limitB : Mat3
  limitTime : Fin 4 → ℝ
  limitCoeff : Fin 4 → E3
  frameInjective :
    Function.Injective (fun c : E3 => (limitA.mulVec c, limitB.mulVec c))
  timeGap : ℝ
  timeGap_pos : 0 < timeGap
  timeSeparated : ∀ n i j, i ≠ j →
    timeGap ≤ |approxTime n i - approxTime n j|
  tendstoA : Tendsto approxA atTop (𝓝 limitA)
  tendstoB : Tendsto approxB atTop (𝓝 limitB)
  tendstoTime : ∀ i,
    Tendsto (fun n => approxTime n i) atTop (𝓝 (limitTime i))
  tendstoCoeff : ∀ i,
    Tendsto (fun n => approxCoeff n i) atTop (𝓝 (limitCoeff i))
  coeffUnit : ∀ n i, ‖approxCoeff n i‖ = 1
  residualTendsto : ∀ i,
    Tendsto
      (fun n =>
        (pencil (approxA n) (approxB n) (approxTime n i)).mulVec
          (approxCoeff n i))
      atTop (𝓝 0)

/-- The uniform finite-scale Reeb separation survives in the limit. -/
theorem FourProbeConcentrationLimit.limitTime_separated
    (packet : FourProbeConcentrationLimit) (i j : Fin 4) (hij : i ≠ j) :
    packet.timeGap ≤ |packet.limitTime i - packet.limitTime j| := by
  have hlimit :
      Tendsto
        (fun n => |packet.approxTime n i - packet.approxTime n j|)
        atTop
        (𝓝 |packet.limitTime i - packet.limitTime j|) :=
    ((packet.tendstoTime i).sub (packet.tendstoTime j)).abs
  apply isClosed_Ici.mem_of_tendsto hlimit
  filter_upwards [] with n
  exact packet.timeSeparated n i j hij

/-- Pairwise separation, rather than injectivity of the limiting tuple, is the
finite-scale datum.  Injectivity is a consequence of compactness. -/
theorem FourProbeConcentrationLimit.timeInjective
    (packet : FourProbeConcentrationLimit) :
    Function.Injective packet.limitTime := by
  intro i j hij
  by_contra hne
  have hsep := packet.limitTime_separated i j hne
  rw [hij, sub_self, abs_zero] at hsep
  exact (not_le_of_gt packet.timeGap_pos) hsep

/-- Unit normalization survives passage to the limiting flag. -/
theorem FourProbeConcentrationLimit.limitCoeff_norm
    (packet : FourProbeConcentrationLimit) (i : Fin 4) :
    ‖packet.limitCoeff i‖ = 1 := by
  have hnorm :
      Tendsto (fun n => ‖packet.approxCoeff n i‖) atTop
        (𝓝 ‖packet.limitCoeff i‖) :=
    tendsto_norm.comp (packet.tendstoCoeff i)
  have hone : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
    tendsto_const_nhds
  have hnormOne :
      Tendsto (fun n => ‖packet.approxCoeff n i‖) atTop (𝓝 1) := by
    apply hone.congr'
    filter_upwards [] with n
    exact (packet.coeffUnit n i).symm
  exact tendsto_nhds_unique hnorm hnormOne

theorem FourProbeConcentrationLimit.limitCoeff_ne_zero
    (packet : FourProbeConcentrationLimit) (i : Fin 4) :
    packet.limitCoeff i ≠ 0 := by
  intro hzero
  have hnorm := packet.limitCoeff_norm i
  simp [hzero] at hnorm

/-- Passing the genuine flag residual to the limit gives an exact kernel
vector for the limiting Maslov pencil. -/
theorem FourProbeConcentrationLimit.mulVec_zero_at_probe
    (packet : FourProbeConcentrationLimit) (i : Fin 4) :
    (pencil packet.limitA packet.limitB (packet.limitTime i)).mulVec
      (packet.limitCoeff i) = 0 := by
  have htuple :
      Tendsto
        (fun n =>
          (((packet.approxA n, packet.approxB n), packet.approxTime n i),
            packet.approxCoeff n i))
        atTop
        (𝓝 (((packet.limitA, packet.limitB), packet.limitTime i),
          packet.limitCoeff i)) :=
    (((packet.tendstoA.prodMk_nhds packet.tendstoB).prodMk_nhds
      (packet.tendstoTime i)).prodMk_nhds (packet.tendstoCoeff i))
  have hlimit :
      Tendsto
        (fun n =>
          (pencil (packet.approxA n) (packet.approxB n)
            (packet.approxTime n i)).mulVec (packet.approxCoeff n i))
        atTop
        (𝓝 ((pencil packet.limitA packet.limitB
          (packet.limitTime i)).mulVec (packet.limitCoeff i))) :=
    continuous_pencil_mulVec.continuousAt.tendsto.comp htuple
  exact tendsto_nhds_unique hlimit (packet.residualTendsto i)

/-- Every limiting probe in a coherent four-probe boundary packet is an exact
root of the limiting Maslov determinant. -/
theorem FourProbeConcentrationLimit.det_zero_at_probe
    (packet : FourProbeConcentrationLimit) (i : Fin 4) :
    Matrix.det
      (pencil packet.limitA packet.limitB (packet.limitTime i)) = 0 := by
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  have hcoeff : (packet.limitCoeff i).ofLp ≠ 0 := by
    intro hzero
    apply packet.limitCoeff_ne_zero i
    apply (WithLp.ext_iff 2).mpr
    simpa using hzero
  exact ⟨(packet.limitCoeff i).ofLp, hcoeff,
    packet.mulVec_zero_at_probe i⟩

/-- The coherent infinite-depth four-probe packet reaches the algebraic
terminal: its limiting graph plane meets every member of the Lagrangian pencil.
No finite-scale Wang--Zakharov estimate is used. -/
theorem FourProbeConcentrationLimit.forces_full_maslov_trapping
    (packet : FourProbeConcentrationLimit) :
    ∀ s : ℝ,
      ∃ point : E3 × E3,
        point ∈ graphPlane packet.limitA packet.limitB ∧
        point ∈ lagrangianPencil s ∧
        point ≠ 0 := by
  apply four_probe_boundary_forces_full_maslov_trapping
    packet.limitA packet.limitB packet.limitTime
    packet.frameInjective packet.timeInjective
  intro i
  exact (maslov_incidence_equivalence
    packet.limitA packet.limitB (packet.limitTime i)
    packet.frameInjective).1 (packet.det_zero_at_probe i)

/-- The limiting horizontal frame has a genuine nonzero kernel vector.  This
is the exact rank-loss conclusion of the manuscript's four-time firewall. -/
theorem FourProbeConcentrationLimit.forces_horizontal_kernel
    (packet : FourProbeConcentrationLimit) :
    ∃ c : E3, c ≠ 0 ∧ packet.limitA.mulVec c = 0 := by
  apply four_probe_boundary_forces_horizontal_kernel
    packet.limitA packet.limitB packet.limitTime packet.timeInjective
  exact packet.det_zero_at_probe

theorem FourProbeConcentrationLimit.horizontal_det_zero
    (packet : FourProbeConcentrationLimit) :
    Matrix.det packet.limitA = 0 := by
  apply full_maslov_polynomial_forces_horizontal_det_zero
    packet.limitA packet.limitB
  apply four_time_maslov_pencil_firewall
    packet.limitA packet.limitB packet.limitTime packet.timeInjective
  exact packet.det_zero_at_probe

theorem FourProbeConcentrationLimit.horizontal_map_not_injective
    (packet : FourProbeConcentrationLimit) :
    ¬ Function.Injective (fun c : E3 => packet.limitA.mulVec c) := by
  apply four_probe_boundary_horizontal_map_not_injective
    packet.limitA packet.limitB packet.limitTime packet.timeInjective
  exact packet.det_zero_at_probe

/-- A coherent four-time boundary cannot coexist with a uniform horizontal
noncollapse estimate.  The explicit limiting kernel vector has positive norm,
whereas convergence of the horizontal frames sends its image to zero. -/
theorem FourProbeConcentrationLimit.no_uniform_horizontal_noncollapse
    (packet : FourProbeConcentrationLimit) (kappa : ℝ)
    (hkappa : 0 < kappa)
    (hnoncollapse : ∀ (n : ℕ) (c : E3),
      kappa * ‖c‖ ≤ ‖horizontalFrameVector (packet.approxA n) c‖) :
    False := by
  obtain ⟨c, hcne, hc⟩ := packet.forces_horizontal_kernel
  have hcNorm : 0 < ‖c‖ := norm_pos_iff.mpr hcne
  have hvector :
      Tendsto
        (fun n => horizontalFrameVector (packet.approxA n) c)
        atTop
        (𝓝 (horizontalFrameVector packet.limitA c)) := by
    exact continuous_horizontalFrameVector.continuousAt.tendsto.comp
      (packet.tendstoA.prodMk_nhds tendsto_const_nhds)
  have hnorm :
      Tendsto
        (fun n => ‖horizontalFrameVector (packet.approxA n) c‖)
        atTop
        (𝓝 ‖horizontalFrameVector packet.limitA c‖) :=
    tendsto_norm.comp hvector
  have hlimitZero : horizontalFrameVector packet.limitA c = 0 := by
    unfold horizontalFrameVector
    apply (WithLp.ext_iff 2).mpr
    simpa using hc
  have hclosed :
      kappa * ‖c‖ ≤ ‖horizontalFrameVector packet.limitA c‖ := by
    apply isClosed_Ici.mem_of_tendsto hnorm
    filter_upwards [] with n
    exact hnoncollapse n c
  rw [hlimitZero, norm_zero] at hclosed
  have hpositive : 0 < kappa * ‖c‖ := mul_pos hkappa hcNorm
  exact (not_le_of_gt hpositive) hclosed

/-- Native determinant-layer form of the finite-scale firewall: a fixed
positive lower bound for every origin horizontal determinant cannot survive a
coherent four-separated-time limit. -/
theorem FourProbeConcentrationLimit.no_uniform_horizontal_det_lower_bound
    (packet : FourProbeConcentrationLimit) (Delta : ℝ)
    (hDelta : 0 < Delta)
    (hdet : ∀ n, Delta ≤ |Matrix.det (packet.approxA n)|) :
    False := by
  have hlimit :
      Tendsto (fun n => |Matrix.det (packet.approxA n)|) atTop
        (𝓝 |Matrix.det packet.limitA|) :=
    (continuous_det_matrix.continuousAt.tendsto.comp packet.tendstoA).abs
  have hclosed : Delta ≤ |Matrix.det packet.limitA| := by
    apply isClosed_Ici.mem_of_tendsto hlimit
    filter_upwards [] with n
    exact hdet n
  rw [packet.horizontal_det_zero, abs_zero] at hclosed
  exact (not_le_of_gt hDelta) hclosed

/-- Contrapositive terminal used by the stopping tree: one transverse time
excludes every coherent four-probe concentration limit with the same limiting
plane. -/
theorem no_four_probe_concentration_limit_of_transverse_time
    (packet : FourProbeConcentrationLimit) (s₀ : ℝ)
    (htransverse :
      ¬ ∃ point : E3 × E3,
          point ∈ graphPlane packet.limitA packet.limitB ∧
          point ∈ lagrangianPencil s₀ ∧
          point ≠ 0) :
    False := by
  exact htransverse (packet.forces_full_maslov_trapping s₀)

end StickyKakeya4
