import Theorems.Thm_StickyKakeya4_native_quotient_fiber_readback
import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_support

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 7000000
noncomputable section
namespace NativeActualQuotientDensity
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh
open NativeQuotientLatticeTransport NativeQuotientFiberReadback GridQuotientAD
open NativeReferenceXYGridMaps NativeReferenceXYGridPoints NativeReferenceXYGridField NativeReferenceXYGridSupport
open NativeTranslatedGrainHeightFibers NativeTranslatedGrainHeightSelection NativeTranslatedGrainHeightOverlap
open NativeHorizontalGrainSlice NativeHeightSlopeCoordinates NativeOriginalParentSelection NativeSpatialAngularGeometry

lemma rho_halfWidth (m : ℕ) (hm : 1 ≤ m) : rho m*(halfWidth m:ℝ)=32 := by
  have hh := mu_halfWidth m hm
  dsimp only [mu] at hh
  linarith only [hh]

lemma normalized_density (m k : ℕ) (hm : 1 ≤ m) {C X : ℝ} (hC : 0 < C)
    (H : (rho m)^(-(k:ℝ)) ≤ C*X) :
    (1/((32:ℝ)^k*C))*(halfWidth m:ℝ)^k ≤ X := by
  have hr := rho_pos m
  have he : (rho m)^k*(halfWidth m:ℝ)^k=(32:ℝ)^k := by
    rw [←mul_pow,rho_halfWidth m hm]
  rw [Real.rpow_neg hr.le,Real.rpow_natCast] at H
  have hl : (1/((32:ℝ)^k*C))*(halfWidth m:ℝ)^k=
      ((rho m)^k)⁻¹/C := by
    field_simp [hr.ne',hC.ne']
    nlinarith only [he]
  rw [hl]
  exact (div_le_iff₀ hC).mpr (by simpa only [mul_comm] using H)

/-- Convert the source's proved rho-power cross bound on the literal
referenceX sets into the exact full-fiber population used by the lattice
quotient theorem. There is no new selection or point-map identification. -/
theorem reference_cross_dense {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (m ell : ℕ)
    (hm : 1 ≤ m) (p : Parent) (plane : Index → Submodule ℝ E4)
    (S T : Finset (Fin n × Index)) (hT : T⊆second D a m ell plane S) (hTn : T.Nonempty)
    (hp : ∀x∈T,parentLabel D a (2^m) x.1=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1)
    (Fraw : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (Hread : ∀x∈second D a m ell plane S,Fraw (rawHeight D m x.2)=
      nodeSlope P hP ell hell hell4 hd (sliceSpace (plane (spatialLabel D (2^m) x.2)))
        (slice_horizontal (plane (spatialLabel D (2^m) x.2))))
    (C : ℝ)
    (HX : ∀x∈T,(rho m)^(-((ell:ℝ)-1)) ≤ C*
      (referenceX D a m ell plane T P hP hell hell4 hd (mu m)
        (referenceKey D a m ell plane P hP hell hell4 hd (mu m) x)).card) :
    0 < C ∧ ∀height : ℤ,∀y∈
      (productSlice (T.image (fun x => pxy D a m ell p P hP hell hell4 hd
        (fixedField D a m ell plane S Fraw) x.2)) height).image Prod.snd,
      (1/((32:ℝ)^(ell-1)*C))*(halfWidth m:ℝ)^(ell-1) ≤
        ((fiber (productSlice (T.image (fun x => pxy D a m ell p P hP hell hell4 hd
          (fixedField D a m ell plane S Fraw) x.2)) height) y).card:ℝ) := by
  have hC : 0 < C := by
    obtain ⟨x,hx⟩ := hTn
    have hh := HX x hx
    have hpos : 0 < (rho m)^(-((ell:ℝ)-1)) := Real.rpow_pos_of_pos (rho_pos m) _
    by_contra hn
    have hnC : C ≤ 0 := le_of_not_gt hn
    have hnR := mul_nonpos_of_nonpos_of_nonneg hnC
      (Nat.cast_nonneg (referenceX D a m ell plane T P hP hell hell4 hd (mu m)
        (referenceKey D a m ell plane P hP hell hell4 hd (mu m) x)).card)
    linarith only [hh,hpos,hnR]
  refine ⟨hC,?_⟩
  intro height y hy
  simp only [productSlice,mem_image,mem_filter] at hy
  obtain ⟨z,⟨u,⟨⟨x,hx,rfl⟩,hheight⟩,rfl⟩,rfl⟩ := hy
  have hr := fixed_pxy_readback D a m ell p plane S P hP hell hell4 hd Fraw Hread x (hT hx) (hp x hx)
  have hkey : referenceKey D a m ell plane P hP hell hell4 hd (mu m) x=
      (height,(pxy D a m ell p P hP hell hell4 hd (fixedField D a m ell plane S Fraw) x.2).2.2) := by
    rw [hr] at hheight ⊢
    exact Prod.ext hheight rfl
  rw [actual_referenceX_card D a m ell p plane S T hT hp P hP hell hell4 hd Fraw Hread]
  apply normalized_density m (ell-1) hm hC
  have hh := HX x hx
  rw [hkey] at hh
  have he : ((ell-1:ℕ):ℝ)=(ell:ℝ)-1 := by rw [Nat.cast_sub hell,Nat.cast_one]
  simpa only [he] using hh

end NativeActualQuotientDensity
