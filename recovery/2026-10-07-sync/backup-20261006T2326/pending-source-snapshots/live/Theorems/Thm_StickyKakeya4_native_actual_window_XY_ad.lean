import Theorems.Thm_StickyKakeya4_native_window_encoded_capacities
import Theorems.Thm_StickyKakeya4_native_window_quotient_transport
import Theorems.Thm_StickyKakeya4_native_supported_two_map_ad
import Theorems.Thm_StickyKakeya4_native_height_window_relations
import Theorems.Thm_StickyKakeya4_native_slice_ad_constant

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2200000
noncomputable section
namespace NativeActualWindowXYAD
open NativeHorizontalGrainSlice
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeOriginalParentDensityCore NativeCubicalIncidenceCounts
open NativeSquaredGrainQueries NativeReferenceXYGridPoints NativeReferenceXYGridMaps
open NativeWindowXYMetric NativeWindowXYLabels NativeWindowQuotientTransport NativeWindowEncodedCapacities
open NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightMetric NativeOffsetAngularGeometry
open NativeAnisotropicShortRowGeometry NativeAnisotropicSliceLabels NativeJointUniformCoarseRelations
open NativeSliceClassBalls NativeSliceRadiusInterpolation NativeParentSliceHeightGeometry
open NativeFixedCompactKakeyaExponent FiniteVoronoiRealADCoarsening
open scoped Matrix.Norms.Elementwise

lemma window_mesh_outer (m f : ℕ) (hm : 6 ≤ m) (hmf : m ≤ f) (hfb : f ≤ phaseDepth m) :
    (mu m*(NativeWindowQuotientTransport.factor m f:ℝ))*radius f m=1/64 := by
  have hh := window_mesh_halfWidth m f hm hmf hfb
  have he : (windowHalfWidth m f:ℝ)=32*radius f m := by
    unfold windowHalfWidth radius
    rw [pow_add]
    push_cast
    ring
  rw [he] at hh
  linarith only [hh]

/-- Paid XY constant for a true height window. The cubic power of the
actual geometric map capacity is explicit in its upper coefficient. -/
def windowConstant (L U lambda loss : ℝ) (Qref Qnew C gap : ℕ) : ℝ :=
  NativeSliceADConstant.constant
    (lambda*(L/U)/(loss*(Qref:ℝ)^2*C*C*(Qnew:ℝ)^4))
    ((27*(C:ℝ))*((C:ℝ)*C*((Qref:ℝ)^4*U/L)))
    (max 64 ((2^gap:ℕ):ℝ)) (3-extremalExponent)

/-- The same supported third core gains genuine window XY AD. Reference
counts are for the actual column(f,f-m+3) map; geometric capacities and the
endpoint cover are derived internally from the original parent geometry. -/
theorem of_reference_counts {n J : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level m ell f gap : ℕ) (hm : 12 ≤ m) (hdy : D.thickness=(2:ℝ)⁻¹^level)
    (hf : phaseDepth m ≤ level) (hmf : m ≤ f) (hfb : f ≤ phaseDepth m)
    (hJ : 0 < J) (depth : Fin (J+1) → ℕ)
    (hfirst : depth 0=m) (hlast : depth (Fin.last J)=f) (hdepth : ∀j,depth j ≤ f)
    (hmono : Monotone depth) (hgap : ∀j : Fin J,depth j.succ-depth j.castSucc ≤ gap)
    (E S T : Finset (Fin n × Index)) (hE : E⊆incidences original) (p : Parent)
    (hS : S⊆parentEdges D a (2^m) E p) (hT : T⊆S) (hTn : T.Nonempty)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1) (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (Lip : ℝ) (hLip0 : 0 ≤ Lip)
    (hF : ∀z∈S,‖F (translatedHeight D a m z.2)‖ ≤ (1/4:ℝ))
    (hLip : ∀z∈S,∀w∈S,‖F (translatedHeight D a m z.2)-F (translatedHeight D a m w.2)‖ ≤
      Lip*|referenceHeight m (translatedHeight D a m z.2)-referenceHeight m (translatedHeight D a m w.2)|)
    (Qref Qnew : ℕ)
    (HRef : HasUniformFibers (parentEdges D a (2^m) E p) Qref
      (fun z => referencePoint D a m f f p z.2))
    (HT : HasUniformFibers T Qnew (fun z => xyPoint D a m ell f f p P hP hell hell4 hd F z.2))
    (HC : ∀j,HasUniformFibers T Qnew
      (fun z => horizontalCoarsen f (depth j) (xyPoint D a m ell f f p P hP hell hell4 hd F z.2)))
    (L U lambda loss : ℝ) (hL : 0 < L) (hU : 0 < U) (hlambda : 0 < lambda) (hloss : 0 < loss)
    (hret : lambda*((parentEdges D a (2^m) E p).card:ℝ) ≤ loss*T.card)
    (Hratio : ∀j,(L/U)*(radius f (depth j))^(3-extremalExponent)*
      (NativeHeightWindowRelations.points D a m (depth j) (f-m+3) E p).card ≤
        (NativeHeightWindowRelations.points D a m f (f-m+3) E p).card)
    (Hupper : ∀j v,v∈NativeHeightWindowRelations.points D a m f (f-m+3) E p →
      ((preparedClass (NativeHeightWindowRelations.points D a m f (f-m+3) E p) f (depth j) v).card:ℝ) ≤
        ((Qref:ℝ)^4*U/L)*(radius f (depth j))^(3-extremalExponent)) :
    ∀height : ℤ,ADBounds
      (realizedSlice (T.image (fun z => xyPoint D a m ell f f p P hP hell hell4 hd F z.2))
        (mu m*(NativeWindowQuotientTransport.factor m f:ℝ)) height)
      (mu m*(NativeWindowQuotientTransport.factor m f:ℝ)) (windowConstant L U lambda loss Qref Qnew ((2*menuRadius Lip+1)^3) gap)
      (3-extremalExponent) := by
  let I := parentEdges D a (2^m) E p
  let pref := fun z : Fin n × Index => referencePoint D a m f f p z.2
  let xy := fun z : Fin n × Index => xyPoint D a m ell f f p P hP hell hell4 hd F z.2
  let C := (2*menuRadius Lip+1)^3
  have hCI : 0 < C := by dsimp [C]; positivity
  have hSI : S⊆incidences original := hS.trans ((filter_subset _ _).trans hE)
  have hpS : ∀z∈S,parentLabel D a (2^m) z.1=p := fun z hz => (mem_filter.mp (hS hz)).2
  have Hcaps := NativeWindowEncodedCapacities.encoded_capacities h original horiginal ha level m hm hdy hf
    p S hSI hpS P hP ell hell hell4 hd F Lip hLip0 hF hLip f hmf hfb
  have hIn := hTn.mono (hT.trans hS)
  have hQR : (0:ℝ)<Qref := by exact_mod_cast NativePaidParentScaleBudget.uniform_radix_pos I hIn pref Qref HRef
  have hQT : (0:ℝ)<Qnew := by exact_mod_cast NativePaidParentScaleBudget.uniform_radix_pos T hTn xy Qnew HT
  have hCr : (0:ℝ)<C := by exact_mod_cast hCI
  have hmesh : 0 < mu m*(NativeWindowQuotientTransport.factor m f:ℝ) := by have hh := mu_pos m; unfold NativeWindowQuotientTransport.factor; positivity
  have Hcap (z : ℤ) : (((I.image pref).image (horizontalCoarsen f m)).filter
      (fun q => q (3:Fin 4)=z)).card ≤ 27 := by
    change (((NativeHeightWindowRelations.points D a m f (f-m+3) E p).image (horizontalCoarsen f m)).filter
      (fun q => q (3:Fin 4)=z)).card ≤ 27
    rw [NativeHeightWindowRelations.points_horizontal_coarsen D a m f m (f-m+3) hmf E p]
    have hscale : ((2^m:ℕ):ℝ)*D.thickness ≤ 1 := by
      rw [NativeLocalParentScales.relative_scale hdy (hmf.trans (hfb.trans hf))]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    exact endpoint_height_card_le h original horiginal ha (2^m) (by positivity) hscale E hE p _ z
  have Hratio' (j : Fin (J+1)) : ((L/U)*(radius f (depth j))^(3-extremalExponent))*
      ((I.image pref).image (horizontalCoarsen f (depth j))).card ≤ (I.image pref).card := by
    change ((L/U)*(radius f (depth j))^(3-extremalExponent))*
      ((NativeHeightWindowRelations.points D a m f (f-m+3) E p).image (horizontalCoarsen f (depth j))).card ≤ _
    rw [NativeHeightWindowRelations.points_horizontal_coarsen D a m f (depth j) (f-m+3) (hdepth j) E p]
    exact Hratio j
  intro height
  apply NativeSliceADConstant.ADBounds_of_asymmetric_counts _ (mu m*(NativeWindowQuotientTransport.factor m f:ℝ))
    (lambda*(L/U)/(loss*(Qref:ℝ)^2*C*C*(Qnew:ℝ)^4))
    ((27*(C:ℝ))*((C:ℝ)*C*((Qref:ℝ)^4*U/L)))
    (max 64 ((2^gap:ℕ):ℝ)) (3-extremalExponent) hmesh (by positivity)
  intro x hx r hr hr1
  obtain ⟨u,hu,rfl⟩ := mem_image.mp hx
  obtain ⟨huP,hheight⟩ := mem_filter.mp hu
  have HH := NativeSupportedTwoMapAD.all_radius_bounds I S T hS hT hTn pref xy Qref Qnew C C hCI hCI
    HRef HT J f m gap hJ depth hfirst hlast hdepth hmono hgap HC Hcaps.1 Hcaps.2.1
    (fun j => (Hcaps.2.2 (depth j) (hdepth j)).1) (fun j => (Hcaps.2.2 (depth j) (hdepth j)).2)
    (fun z _hz => xyPoint_height D a m ell f f (by omega) hmf le_rfl hfb p P hP hell hell4 hd F z.2) Hcap
    (mu m*(NativeWindowQuotientTransport.factor m f:ℝ)) (L/U) ((Qref:ℝ)^4*U/L) (3-extremalExponent) lambda loss
    hmesh (by positivity) (by positivity) (sub_nonneg.mpr extremalExponent_le_three) hlambda.le hloss
    (window_mesh_outer m f (by omega) hmf hfb) hret Hratio' Hupper u huP r hr hr1
  simpa only [hheight] using HH

end NativeActualWindowXYAD
