import Theorems.Thm_StickyKakeya4_contact_symplectic_edge_flow_certificate_existence

namespace StickyKakeya4

/-- Four distinct physical Maslov probes do not merely make the determinant
vanish at the sampled Reeb times.  They force the limiting graph plane to
meet every member of the Lagrangian pencil.  This is the exact algebraic
terminal needed after an infinite concentration boundary has been upgraded
from two probes to four probes; no Wang--Zakharov estimate enters here. -/
theorem four_probe_boundary_forces_full_maslov_trapping
    (A B : Mat3) (time : Fin 4 → ℝ)
    (hframe : Function.Injective (fun c : E3 => (A.mulVec c, B.mulVec c)))
    (htime : Function.Injective time)
    (hprobe : ∀ i,
      ∃ point : E3 × E3,
        point ∈ graphPlane A B ∧
        point ∈ lagrangianPencil (time i) ∧
        point ≠ 0) :
    ∀ s : ℝ,
      ∃ point : E3 × E3,
        point ∈ graphPlane A B ∧
        point ∈ lagrangianPencil s ∧
        point ≠ 0 := by
  have hdetAtProbe : ∀ i, Matrix.det (pencil A B (time i)) = 0 := by
    intro i
    exact (maslov_incidence_equivalence A B (time i) hframe).2 (hprobe i)
  have hdetEverywhere : ∀ s : ℝ, Matrix.det (pencil A B s) = 0 :=
    four_time_maslov_pencil_det_zero_at_every_time A B time htime hdetAtProbe
  intro s
  exact (maslov_incidence_equivalence A B s hframe).1 (hdetEverywhere s)

/-- The top coefficient of the identically vanishing Maslov polynomial is the
horizontal determinant. -/
theorem full_maslov_polynomial_forces_horizontal_det_zero
    (A B : Mat3) (hzero : maslovPencilPolynomial A B = 0) :
    Matrix.det A = 0 := by
  calc
    Matrix.det A = (maslovPencilPolynomial A B).coeff 3 := by
      simpa [maslovPencilPolynomial] using
        (Polynomial.coeff_det_X_add_C_card A B).symm
    _ = 0 := by rw [hzero]; simp

/-- Vanishing of the whole Maslov determinant polynomial forces the horizontal
frame to lose rank.  We record rank loss by an explicit nonzero kernel vector,
which is the form needed to rule out a noncollapsed three-dimensional
horizontal blow-up. -/
theorem full_maslov_polynomial_forces_horizontal_kernel
    (A B : Mat3) (hzero : maslovPencilPolynomial A B = 0) :
    ∃ c : E3, c ≠ 0 ∧ A.mulVec c = 0 := by
  have hdetA : Matrix.det A = 0 :=
    full_maslov_polynomial_forces_horizontal_det_zero A B hzero
  obtain ⟨c, hcne, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetA
  let cE : E3 := WithLp.toLp 2 c
  have hcEne : cE ≠ 0 := by
    intro hcEzero
    apply hcne
    have hcEzero' := congrArg WithLp.ofLp hcEzero
    simpa [cE] using hcEzero'
  exact ⟨cE, hcEne, by simpa [cE] using hc⟩

theorem four_probe_boundary_forces_horizontal_kernel
    (A B : Mat3) (time : Fin 4 → ℝ)
    (htime : Function.Injective time)
    (hincidence : ∀ i, Matrix.det (pencil A B (time i)) = 0) :
    ∃ c : E3, c ≠ 0 ∧ A.mulVec c = 0 := by
  exact full_maslov_polynomial_forces_horizontal_kernel A B
    (four_time_maslov_pencil_firewall A B time htime hincidence)

theorem four_probe_boundary_horizontal_map_not_injective
    (A B : Mat3) (time : Fin 4 → ℝ)
    (htime : Function.Injective time)
    (hincidence : ∀ i, Matrix.det (pencil A B (time i)) = 0) :
    ¬ Function.Injective (fun c : E3 => A.mulVec c) := by
  obtain ⟨c, hcne, hc⟩ :=
    four_probe_boundary_forces_horizontal_kernel A B time htime hincidence
  intro hInjective
  apply hcne
  apply hInjective
  simpa using hc

/-- Contrapositive form used by the stopping tree: if one member of the
Lagrangian pencil is transverse to the limiting graph plane, then four
pairwise distinct probe times cannot all survive as genuine incidences. -/
theorem exists_missing_probe_of_one_transverse_maslov_time
    (A B : Mat3) (time : Fin 4 → ℝ) (s₀ : ℝ)
    (hframe : Function.Injective (fun c : E3 => (A.mulVec c, B.mulVec c)))
    (htime : Function.Injective time)
    (htransverse :
      ¬ ∃ point : E3 × E3,
          point ∈ graphPlane A B ∧
          point ∈ lagrangianPencil s₀ ∧
          point ≠ 0) :
    ∃ i,
      ¬ ∃ point : E3 × E3,
          point ∈ graphPlane A B ∧
          point ∈ lagrangianPencil (time i) ∧
          point ≠ 0 := by
  by_contra hall
  push_neg at hall
  exact htransverse
    (four_probe_boundary_forces_full_maslov_trapping
      A B time hframe htime hall s₀)

end StickyKakeya4
