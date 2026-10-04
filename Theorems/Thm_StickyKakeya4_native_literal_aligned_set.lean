import Theorems.Thm_StickyKakeya4_native_original_alignment_geometry
import Theorems.Thm_StickyKakeya4_native_uniform_output_bounds

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace NativeLiteralAlignedSet

open NativeDyadicTubeStopping ShearedGridADReference SmallFiberAlignment
open NativeSeparatedFractionalPatches NativeOriginalAlignmentGeometry
open NativeUniformOutputBounds LiteralAffineFiberCoordinates NormalizedQuantizedPatches
open FiniteVoronoiRealADCoarsening RealScalarADInterpolation NativeAmbientADGeometry
open ShearedGridTubeReference

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The planar aligned-set conclusion on literal scalar fibers. All AD bounds
use actual closed metric balls. Tube bounds range over every direction. -/
structure LiteralAligned (P : Finset Plane) (e t s C : ℝ) : Prop where
  mesh_pos : 0 < e
  nonempty : P.Nonempty
  separated : ∀ p ∈ P, ∀ q ∈ P, p ≠ q →
    e ≤ dist (EuclideanAlignmentPatches.euclidean p) (EuclideanAlignmentPatches.euclidean q)
  bounded : ∀ p ∈ P, ∀ i, |p i| ≤ 1
  ambient : ADBounds (P.image EuclideanAlignmentPatches.euclidean) e C t
  fibers : ∃ (angle : ℝ) (Y : Finset ℝ) (X : Y → Finset ℝ),
    |angle| ≤ 1 ∧ Y.Nonempty ∧
    (∀ y ∈ Y, |y| ≤ 1) ∧ ADBounds Y e C (t-s) ∧
    (∀ y, (X y).Nonempty ∧ (∀ x ∈ X y, |x| ≤ 1) ∧ ADBounds (X y) e C s) ∧
    P = Y.attach.biUnion (fun y => (X y).image (fun x => ![x, angle*x+(y:ℝ)]))
  tubes : ∀ rho tau, e ≤ rho → rho ≤ tau → TraceBound P rho tau (C*(tau/rho)^s)

/-- The scalar bound and the native AD predicate count exactly the same
closed ball, without metric comparison or changing the regularity constant. -/
lemma ballCount_eq_carrierBall {X : Type*} [PseudoMetricSpace X]
    (P : Finset X) (p : X) (r : ℝ) :
    ballCount P p r = ((FiniteVoronoiPopulation.carrierBall P p r).card : ℝ) := rfl

lemma quotient_fiber_nonempty (P : Finset Vertex) (mu angle L : ℝ) (c : Plane)
    {y : ℝ} (hy : y ∈ quotientCoordinates P mu angle L c) :
    (fiberAt P mu angle L c y).Nonempty := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
  exact ⟨timeCoord mu (c 0) L k.1,
    Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, rfl⟩, rfl⟩⟩

lemma normalizedImage_eq_vertex_image (Ω : Finset Plane) (mu angle b : ℝ) (c : Plane) :
    normalizedImage Ω mu angle b c =
      (Ω.image (vertex mu angle)).image (fun k => affine c (64*b) (realized mu angle k)) := by
  rw [Finset.image_image]
  rfl

lemma normalizedImage_euclidean_eq (Ω : Finset Plane) (mu angle b : ℝ) (c : Plane) :
    (normalizedImage Ω mu angle b c).image EuclideanAlignmentPatches.euclidean =
      (Ω.image (vertex mu angle)).image (actualPoint mu angle (64*b) c) := by
  rw [normalizedImage_eq_vertex_image, Finset.image_image]
  rfl

/-- Native real-radius estimates are actual AD bounds on the Euclidean image. -/
lemma uniform_ambient_AD {Ω : Finset Plane} {mu angle b t s C : ℝ} {c : Plane}
    (B : UniformBounds (Ω.image (vertex mu angle)) mu angle b t s C c) :
    ADBounds ((normalizedImage Ω mu angle b c).image EuclideanAlignmentPatches.euclidean)
      (64*mu/(64*b)) C t := by
  rw [normalizedImage_euclidean_eq]
  intro p hp r hrlo hrhi
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
  have he : 64*(mu/(64*b)) = 64*mu/(64*b) := by ring
  have h := B.ambient k hk r (by simpa only [he] using hrlo) hrhi
  simpa only [he, ballCount_eq_carrierBall] using h

/-- Construct the literal Definition 5.1 fibers and retain the stronger native
Euclidean AD conclusion, on precisely the previously constructed image. -/
theorem of_nearGraph_uniform {Ω : Finset Plane} {mu angle b t s C : ℝ} {c : Plane}
    (G : NearGraphImage Ω mu angle b c)
    (B : UniformBounds (Ω.image (vertex mu angle)) mu angle b t s C c)
    (hmu : 0 < mu) (hb : 0 < b) (hangle : |angle| ≤ 1) (hΩ : Ω.Nonempty) :
    LiteralAligned (normalizedImage Ω mu angle b c) (64*mu/(64*b)) t s C := by
  let V := Ω.image (vertex mu angle)
  let Y := quotientCoordinates V mu angle (64*b) c
  let X : Y → Finset ℝ := fun y => fiberAt V mu angle (64*b) c y.val
  have he : 64*(mu/(64*b)) = 64*mu/(64*b) := by ring
  have hY : Y.Nonempty :=
    (hΩ.image (vertex mu angle)).image Prod.snd |>.image (normalCoord mu angle (64*b) c)
  have hX (y : Y) : (X y).Nonempty := quotient_fiber_nonempty V mu angle (64*b) c y.property
  have hgraph_mem (y : Y) (x : ℝ) (hx : x ∈ X y) :
      ![x, angle*x+(y:ℝ)] ∈ normalizedImage Ω mu angle b c := by
    rw [G.graph]
    exact Finset.mem_biUnion.mpr ⟨y.val, y.property, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
  have hXbound (y : Y) (x : ℝ) (hx : x ∈ X y) : |x| ≤ 1/32 := by
    simpa only [Matrix.cons_val_zero] using G.bounded _ (hgraph_mem y x hx) 0
  have hYbound (y : Y) : |(y:ℝ)| ≤ 1 := by
    obtain ⟨x, hx⟩ := hX y
    have hy := G.bounded _ (hgraph_mem y x hx) 1
    change |angle*x+(y:ℝ)| ≤ 1/32 at hy
    have hxbound := hXbound y x hx
    have hprod : |angle*x| ≤ 1/32 := by
      rw [abs_mul]
      exact (mul_le_mul hangle hxbound (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
    have hsub := abs_sub (angle*x+(y:ℝ)) (angle*x)
    have hid : angle*x+(y:ℝ)-angle*x = (y:ℝ) := by ring
    rw [hid] at hsub
    linarith
  refine ⟨by positivity, hΩ.image _, G.separated, ?_, uniform_ambient_AD B, ?_, ?_⟩
  · intro p hp i
    exact (G.bounded p hp i).trans (by norm_num)
  · refine ⟨angle, Y, X, hangle, hY, ?_, ?_, ?_, ?_⟩
    · intro y hy
      exact hYbound ⟨y, hy⟩
    · intro y hy r hrlo hrhi
      have h := B.quotient y r hy (by simpa only [he] using hrlo) hrhi
      simpa only [he, ballCount_eq_carrierBall] using h
    · intro y
      refine ⟨hX y, ?_, ?_⟩
      · intro x hx
        exact (hXbound y x hx).trans (by norm_num)
      · intro x hx r hrlo hrhi
        have h := B.fibers y.val x r hx (by simpa only [he] using hrlo) hrhi
        simpa only [he, ballCount_eq_carrierBall] using h
    · rw [G.graph]
      ext p
      simp only [Finset.mem_biUnion, Finset.mem_attach, true_and, Finset.mem_image]
      constructor
      · rintro ⟨y, hy, x, hx, hxp⟩
        exact ⟨⟨y, hy⟩, x, hx, hxp⟩
      · rintro ⟨⟨y, hy⟩, x, hx, hxp⟩
        exact ⟨y, hy, x, hx, hxp⟩
  · intro rho tau hrho hrt
    rw [normalizedImage_eq_vertex_image]
    exact B.tubes rho tau (by simpa only [he] using hrho) hrt

/-- Two-way Euclidean proximity to a genuine literal aligned finite set. -/
structure NearlyLiteralAligned (A : Finset Plane) (e t s C : ℝ) : Prop where
  bounded : ∀ p ∈ A, ∀ i, |p i| ≤ 1
  aligned : ∃ P : Finset Plane, LiteralAligned P e t s C ∧
    (∀ p ∈ A, ∃ q ∈ P,
      dist (EuclideanAlignmentPatches.euclidean p) (EuclideanAlignmentPatches.euclidean q) < e) ∧
    (∀ q ∈ P, ∃ p ∈ A,
      dist (EuclideanAlignmentPatches.euclidean p) (EuclideanAlignmentPatches.euclidean q) < e)


/-- The nearby source also lies in the unit square when the normalized mesh
is at most one. The existing stronger e/10 proximity supplies the margin. -/
lemma nearGraph_source_bounded {Ω : Finset Plane} {mu angle b : ℝ} {c : Plane}
    (G : NearGraphImage Ω mu angle b c) (he : 64*mu/(64*b) ≤ 1) :
    ∀ p ∈ Ω.image (affine c (64*b)), ∀ i, |p i| ≤ 1 := by
  intro p hp i
  obtain ⟨q, hq, hpq⟩ := G.near p hp
  have hcoord : |p i-q i| < (64*mu/(64*b))/10 := by
    simpa only [Real.dist_eq] using
      (dist_le_pi_dist p q i).trans_lt ((EuclideanAlignmentPatches.sup_dist_le p q).trans_lt hpq)
  have hqbound := G.bounded q hq i
  have htri := abs_add_le (p i-q i) (q i)
  have hid : p i-q i+q i = p i := by ring
  rw [hid] at htri
  linarith

/-- The original normalized source is nearly aligned in the literal planar
sense, using the actual quantized image as its constructed witness. -/
theorem nearly_of_nearGraph_uniform {Ω : Finset Plane} {mu angle b t s C : ℝ} {c : Plane}
    (G : NearGraphImage Ω mu angle b c)
    (B : UniformBounds (Ω.image (vertex mu angle)) mu angle b t s C c)
    (hmu : 0 < mu) (hb : 0 < b) (hangle : |angle| ≤ 1) (hΩ : Ω.Nonempty)
    (he : 64*mu/(64*b) ≤ 1) :
    NearlyLiteralAligned (Ω.image (affine c (64*b))) (64*mu/(64*b)) t s C := by
  have hepos : 0 < 64*mu/(64*b) := by positivity
  have heten : (64*mu/(64*b))/10 < 64*mu/(64*b) := by linarith
  refine ⟨nearGraph_source_bounded G he,
    normalizedImage Ω mu angle b c, of_nearGraph_uniform G B hmu hb hangle hΩ, ?_, ?_⟩
  · intro p hp
    obtain ⟨q, hq, hpq⟩ := G.near p hp
    exact ⟨q, hq, hpq.trans heten⟩
  · intro q hq
    obtain ⟨p, hp, hpq⟩ := G.back q hq
    exact ⟨p, hp, hpq.trans heten⟩

end
end NativeLiteralAlignedSet
