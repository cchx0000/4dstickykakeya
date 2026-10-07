import Theorems.Thm_StickyKakeya4_native_reference_XY_grid_angular_cap
import Theorems.Thm_StickyKakeya4_native_incident_affine_anchor_source
import Theorems.Thm_StickyKakeya4_native_original_point_angular_lower

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
noncomputable section
namespace NativeReferenceXYGridSourceAngularCap
open Classical Finset StickyKakeya4 NativeReferenceXYGridAngularCap NativeReferenceXYGridLinear
open NativeOriginalPointAngularLower NativeOriginalParentSelection NativeSpatialAngularGeometry
open NativePointAngularParentFibers NativeGrainQuotientInjection NativeHorizontalGrainSlice
open NativeHeightSlopeCoordinates NativeIncidentAffineAnchorGeometry NativeIncidentAffineAnchorSource
open NativeDirectionRankDichotomy NativeProjectorCellChart NativeCompatibleNodeDirections
open NativeActualHorizontalGrainSlice NativeRankExponentHierarchy NativeRetainedQueryMenu
open NativeMiddleGrainParentBudget NativeSmallLossParentBudget
open NativeCommonCubicalMesh NativeActualHeightSlopeVariation NativeHorizontalGraphCoordinates NativeGrainQuotientGeometry
open scoped BigOperators Matrix.Norms.Elementwise

/-- A fixed numerical constant, independent of every source scale and q. -/
def angularCapConstant : ℝ := (50:ℝ)^3*(48:ℝ)^3

lemma dyadic_resolution (s : ℕ) (hs : 3 ≤ s) :
    (64/((2^s:ℕ):ℝ))/8=1/((2^(s-3):ℕ):ℝ) := by
  have hp : (2^s:ℕ)=8*2^(s-3) := by
    conv_lhs => rw [show s=3+(s-3) by omega]
    rw [pow_add]
    norm_num
  rw [hp]
  push_cast
  ring

lemma dyadic_cap_power (s d : ℕ) (hs : 3 ≤ s) (hd : d ≤ 3) :
    (50:ℝ)^3*(4*((2^(s-3):ℕ):ℝ)+2)^d ≤
      angularCapConstant*(64/((2^s:ℕ):ℝ))^(-(d:ℝ)) := by
  let rho : ℝ := 64/((2^s:ℕ):ℝ)
  let R : ℝ := ((2^(s-3):ℕ):ℝ)
  have hr : 0 < rho := by dsimp [rho]; positivity
  have hR : 0 < R := by dsimp [R]; positivity
  have hR1 : 1 ≤ R := by
    dsimp [R]
    exact_mod_cast (Nat.one_le_pow (s-3) 2 (by norm_num))
  have he : rho*R=8 := by
    have hh := dyadic_resolution s hs
    change rho/8=1/R at hh
    have hh' := (eq_div_iff (ne_of_gt hR)).mp hh
    linarith only [hh']
  have hb : 4*R+2 ≤ 48/rho := by
    apply (le_div_iff₀ hr).mpr
    have hr8 : rho ≤ 8 := by nlinarith only [he,hR1,hr]
    nlinarith only [he,hr8]
  have hp : (4*R+2)^d ≤ (48/rho)^d := by gcongr
  have hc : (48:ℝ)^d ≤ (48:ℝ)^3 := by
    gcongr
    norm_num
  change (50:ℝ)^3*(4*R+2)^d ≤ angularCapConstant*rho^(-(d:ℝ))
  calc
    _ ≤ (50:ℝ)^3*(48/rho)^d := mul_le_mul_of_nonneg_left hp (by positivity)
    _ = (50:ℝ)^3*(48:ℝ)^d*rho^(-(d:ℝ)) := by
      rw [div_pow,Real.rpow_neg hr.le,Real.rpow_natCast]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hc (by positivity)) (Real.rpow_nonneg hr.le _)

/-- The lower theorem's actual original-point angular menu is exactly the
standard original angular grid at depthm+s-3, with its original tube alphabet. -/
lemma pointMenu_original_card {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m s : ℕ) (hs : 3 ≤ s) (p : Parent) (H : Finset (Fin n × Index)) (k : Index) :
    (pointMenu D m s p H k).card=
      (((H.filter (fun z => z.2=k)).image Prod.fst).image
        (angularLabel D ((2^m)*(2^(s-3))))).card := by
  rw [pointMenu_card D a m s hs p H k,pointAngular_readback,image_image]
  have hp : (2^m:ℕ)*2^(s-3)=2^(m+s-3) := by
    rw [←pow_add]
    congr 1
    omega
  rw [hp]
  rfl

/-- Fixed-point geometric upper on the exact angular menu used by the
source lower. The source theorem below derives the affine residual itself. -/
theorem point_menu_cap {n : ℕ} (D : FiniteScaleSource n) (a : ℝ)
    (m s : ℕ) (hs : 3 ≤ s) (p : Parent) (H : Finset (Fin n × Index))
    (hparent : ∀z∈H,parentLabel D a (2^m) z.1=p) (k : Index)
    (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ) (hM : ‖M‖ ≤ (1/4:ℝ))
    (xi : EuclideanSpace ℝ (Fin (4-ell)))
    (hresidual : ∀i,(i,k)∈H →
      ‖quotientMap P hP ell hell hell4 hd M (localHorizontalSlope D (2^m) p i)-xi‖ ≤
        (64/((2^s:ℕ):ℝ))/8) :
    ((pointMenu D m s p H k).card:ℝ) ≤
      angularCapConstant*(64/((2^s:ℕ):ℝ))^(-((ell-1:ℕ):ℝ)) := by
  let S := (H.filter (fun z => z.2=k)).image Prod.fst
  have hmem : ∀i∈S,(i,k)∈H := by
    intro i hi
    obtain ⟨⟨j,l⟩,hz,hji⟩ := mem_image.mp hi
    obtain ⟨hz,hl⟩ := mem_filter.mp hz
    dsimp only at hji hl
    simpa only [hl,hji] using hz
  have hh := original_angular_cap D a (2^m) (2^(s-3)) (by positivity) p S
    (fun i hi => hparent (i,k) (hmem i hi)) P hP ell hell hell4 hd M hM xi
    (fun i hi => by simpa only [dyadic_resolution s hs] using hresidual i (hmem i hi))
  rw [pointMenu_original_card D a m s hs p H k]
  exact hh.trans (dyadic_cap_power s (ell-1) hs (by omega))

/-- Exact readback of the source anchor's affine expression in the same
fixed quotient coordinates; the matrix action is Euclidean. -/
lemma quotient_anchor_readback (P : Submodule ℝ E4) (hP : P≤heightKernel)
    (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4) (hd : Module.finrank ℝ P=ell-1)
    (M : Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (v : E4) (xi : EuclideanSpace ℝ (Fin (4-ell))) :
    quotientMap P hP ell hell hell4 hd M v-xi=
      NativeIncidentAffineAnchorGeometry.normalCoordinates P hP ell hell hell4 hd v-xi-
        matrixVector M (tangentCoordinates P ell hd v) := by
  simp only [quotientMap,LinearMap.sub_apply,LinearMap.comp_apply,
    Matrix.toLpLin_apply,matrixVector,
    NativeReferenceXYGridLinear.normalCoordinates,NativeIncidentAffineAnchorGeometry.normalCoordinates]
  abel

/-- Actual source small-loss geometry produces the angular cap on every
original point of the same pre-third graph. Anchors and matrix bounds are
derived internally, and no direction or affine-anchor certificate is assumed. -/
theorem actual_point_angular_cap {n : ℕ} {D : FiniteScaleSource n}
    {eta a q r eta0 c tau epsilon : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (hr : 0 < r) (hr1 : r ≤ 1)
    (he : 0 < epsilon) (heHalf : epsilon ≤ 1/2)
    (he0 : 0 ≤ eta0) (heSmall : eta0 ≤ epsilon)
    (hc : 0 < c) (hc1 : c ≤ 1) (hcSmall : c ≤ epsilon/24) (rank : Fin 4) (hrank : rank.val+1 ≤ 3)
    (hrdelta : r ≤ D.thickness^(cutoff c rank)) (htau : 0 ≤ tau) (g K stop m : ℕ)
    (hK : 0 < K) (hs : 6 ≤ stop) (hm : m=grainDepth (2*K) stop (middleIndex K))
    (hTau : tau ≤ commonBudget eta0 c/(1000*(((2*K:ℕ):ℝ)+1)))
    (hgrid : 1/(g:ℝ) < NativeActualMesoscopicRankConfiguration.rankWindow tau/4)
    (hq : 0 < q) (hq1 : q ≤ 1) (hqlow : r^(2*c)/(2*D.thickness^(-(1/(g:ℝ)))) ≤ q)
    (hidentity : 48*((2^stop:ℕ):ℝ)*r=1)
    (hsmall : D.thickness^(cutoff c rank*epsilon/2) ≤ 1/errorConstant)
    (E H : Finset (Fin n × Index)) (hHE : H⊆E) (S0 : Finset Index)
    (hpoints : ∀z∈H,z.2∈S0)
    (point : Index → Index) (tuple : Index → Fin (rank.val+1) → (Fin n × Index))
    (anchor : Index → Fin (rank.val+1) → Fin n)
    (Hsys : IsNodeDirectionSystem D a m E S0 q (rank.val+1) point tuple anchor)
    (oldPlane : Index → Submodule ℝ E4) (hOld : ∀k∈S0,Module.finrank ℝ (oldPlane k)=rank.val+1)
    (hnear : ∀z∈E,Metric.infDist (slopeVector D z.1) (oldPlane z.2:Set E4) ≤ r)
    (parent : Parent) (hparent : ∀z∈H,parentLabel D a (2^m) z.1=parent)
    (P0 : Submodule ℝ E4) (hP0 : P0≤heightKernel) (hd : Module.finrank ℝ P0=(rank.val+1)-1)
    (hCell : ∀k∈H.image Prod.snd,cell P0=cell (horizontalPlane D tuple (spatialLabel D (2^m) k)))
    (f : ℤ → Matrix (Fin (4-(rank.val+1))) (Fin ((rank.val+1)-1)) ℝ)
    (hread : ∀k∈H.image Prod.snd,f (spatialLabel D (2^m) k (3:Fin 4))=
      nodeSlope P0 hP0 (rank.val+1) (by omega) (by omega) hd
        (horizontalPlane D tuple (spatialLabel D (2^m) k))
        (horizontalPlane_le D tuple (spatialLabel D (2^m) k)))
    (s : ℕ) (hsAngle : 3 ≤ s)
    (herror : (5/4:ℝ)*((64:ℝ)/((2^m:ℕ):ℝ))^(1-2*epsilon) ≤ (64/((2^s:ℕ):ℝ))/8) :
    ∀k∈H.image Prod.snd,((pointMenu D m s parent H k).card:ℝ) ≤
      angularCapConstant*(64/((2^s:ℕ):ℝ))^(-(rank.val:ℝ)) := by
  obtain ⟨j,xi,hxi⟩ := exists_actual_incident_affine_anchors h hr hr1 he heHalf he0 heSmall
    hc hc1 hcSmall rank hrank hrdelta htau g K stop m hK hs hm hTau hgrid hq hq1 hqlow
    hidentity hsmall E H hHE S0 hpoints point tuple anchor Hsys oldPlane hOld hnear parent hparent
    P0 hP0 hd hCell f hread
  intro k hk
  have hM : ‖f (spatialLabel D (2^m) k (3:Fin 4))‖ ≤ (1/4:ℝ) := by
    rw [hread k hk]
    exact nodeSlope_norm P0 hP0 (rank.val+1) (by omega) (by omega) hd _ _
  have hres : ∀i,(i,k)∈H →
      ‖quotientMap P0 hP0 (rank.val+1) (by omega) (by omega) hd
          (f (spatialLabel D (2^m) k (3:Fin 4))) (localHorizontalSlope D (2^m) parent i)-xi k‖ ≤
        (64/((2^s:ℕ):ℝ))/8 := by
    intro i hi
    rw [quotient_anchor_readback]
    exact ((hxi k hk).2.2.2 i hi).trans herror
  simpa only [Nat.add_sub_cancel] using point_menu_cap D a m s hsAngle parent H hparent k
    P0 hP0 (rank.val+1) (by omega) (by omega) hd
    (f (spatialLabel D (2^m) k (3:Fin 4))) hM (xi k) hres

end NativeReferenceXYGridSourceAngularCap
