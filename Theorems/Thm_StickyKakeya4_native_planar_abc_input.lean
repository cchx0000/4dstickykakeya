import Theorems.Thm_StickyKakeya4_planar_abc_projected_profiles
import Theorems.Thm_StickyKakeya4_original_angular_balanced_frostman
import Theorems.Thm_StickyKakeya4_original_population_relative
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3500000
noncomputable section
namespace NativePlanarABCInput
open Classical FinitePlaneProjectionGrid FinitePlaneProjectionGraph
open FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening
open PlanarABCBalancedNormalization PlanarABCProjectedProfiles ActualABCImageAssembly
open OriginalAngularBalancedFrostman
abbrev Point := ℝ × ℝ
/-- Concrete finite hypotheses of planar ABC, produced as output. There is
 no such certificate among the original-data constructor's premises. -/
structure Data (mesh exponent ballK angularK density lineWidth lineFraction coverK : ℝ) where
  A : Finset Point
  B : Finset Point
  C : Finset ℝ
  G : Finset (Point × (Point × ℝ))
  nonemptyA : A.Nonempty
  nonemptyB : B.Nonempty
  nonemptyC : C.Nonempty
  graph_subset : G ⊆ A ×ˢ (B ×ˢ C)
  boxA : ∀ a ∈ A, ‖a‖ ≤ 1
  boxB : ∀ b ∈ B, ‖b‖ ≤ 1
  boxC : ∀ c ∈ C, |c| ≤ 1
  separatedA : Separated A mesh
  separatedB : Separated B mesh
  separatedC : Separated C mesh
  ballB : ∀ center : Point, ∀ R : ℝ, mesh ≤ R →
    ((B.filter (fun b => ‖b-center‖ ≤ R)).card : ℝ) ≤ ballK*R*(B.card : ℝ)
  lineB : ∀ a d c : ℝ, max |a| |d|=1 →
    ((B.filter (fun b => |a*b.1+d*b.2-c| ≤ lineWidth)).card : ℝ) ≤ lineFraction*(B.card : ℝ)
  frostmanC : ∀ center R : ℝ, mesh ≤ R →
    ((carrierBall C center R).card : ℝ) ≤ angularK*R^exponent*(C.card : ℝ)
  graph_density : density*(A.card : ℝ)*(B.card : ℝ)*(C.card : ℝ) ≤ (G.card : ℝ)
  output_cover : ((NativeTangentGridCoarsening.planarCells G (fun e => e.1+e.2.2 • e.2.1) mesh).card : ℝ) ≤ coverK*(A.card : ℝ)

/-- Original spatial populations, original B tube exclusion, the literal
 source-Phi AD law, and original endpoint witnesses construct actual planar
 ABC point sets and their actual dense graph. Graph-aware projection, the
 balanced box normalization, and the old-target cover cost are all executed. -/
theorem exists_actual_planar_ABC_input {X Y : Type*}
    (P : Finset X) (p : X → Point3) (B : Finset Y) (b : Y → Point3) (Phi : Finset ℝ)
    (G : Finset (X × (Y × ℝ))) (target : X × (Y × ℝ) → X)
    (anchor : Point3) (angleAnchor : ℝ) (n J : ℕ)
    {rho KP KB beta r0 w0 w kappa epsilon theta angularMesh angularK exponent error lambdaB : ℝ}
    (hP : P.Nonempty) (hBnon : B.Nonempty) (hPhi : Phi.Nonempty) (hmesh : mesh n ≤ rho)
    (hKP : 0 < KP) (hKB : 0 < KB) (hb : 0 < beta) (hr0 : 0 < r0) (hw0 : 0 < w0)
    (hw : 0 ≤ w) (hepsilon : 0 ≤ epsilon) (htheta : 0 ≤ theta) (herror : 0 ≤ error)
    (hscalar : 3*(kappa+epsilon+128*w/(r0*w0)+2*mesh n) ≤ theta^3)
    (hG : G ⊆ P ×ˢ (B ×ˢ Phi)) (hdense : beta*P.card*B.card*Phi.card ≤ (G.card : ℝ))
    (hJ : 2 ≤ 2^(J+1)*rho)
    (htopP : ∀ i ∈ P, ∀ k ∈ P, dist3 (p i) (p k) ≤ 2)
    (htopB : ∀ i ∈ B, ∀ k ∈ B, dist3 (b i) (b k) ≤ 2)
    (hKTP : ∀ i ∈ P, ∀ R : ℝ, rho ≤ R → ((P.filter (fun k => dist3 (p i) (p k) ≤ R)).card : ℝ) ≤ KP*R/rho)
    (hKTB : ∀ i ∈ B, ∀ R : ℝ, rho ≤ R → ((B.filter (fun k => dist3 (b i) (b k) ≤ R)).card : ℝ) ≤ KB*R/rho)
    (hB : ∀ i ∈ B, |(b i).1| ≤ 1 ∧ |(b i).2.1| ≤ 1 ∧ |(b i).2.2| ≤ 1)
    (hclose : ∀ i ∈ B, ((B.filter (fun j => dist3 (b i) (b j) ≤ r0)).card : ℝ) ≤ kappa*B.card)
    (hline : ∀ i ∈ B, ∀ j ∈ B, r0 < dist3 (b i) (b j) → ((originalCrossTube B b i j w0).card : ℝ) ≤ epsilon*B.card)
    (hlambdaB : 0 < lambdaB) (hOriginalBMass : lambdaB ≤ rho*(B.card : ℝ))
    (hPbox : ∀ i ∈ P, ‖p i‖ ≤ 1) (hAnchor : ‖anchor‖ ≤ 1)
    (hAngleAnchor : angleAnchor ∈ Phi) (hAngleBox : ∀ phi ∈ Phi, |phi| ≤ 1)
    (hAngMesh : 0 < angularMesh) (hAngMesh1 : angularMesh ≤ 1) (hAngScale : rho/4 ≤ angularMesh)
    (hAngK : 1 ≤ angularK) (hExponent : 0 ≤ exponent)
    (hAngAD : ADBounds Phi angularMesh angularK exponent) (hAngSep : Separated Phi angularMesh)
    (hTarget : ∀ e ∈ G, target e ∈ P)
    (hOriginal : ∀ e ∈ G, ‖p (target e)-p e.1-(e.2.2-angleAnchor) • (b e.2.1-anchor)‖ ≤ error) :
    let L := graphMassLoss J rho KP KB beta
    ∃ data : Data (rho/8) exponent (400*graphLoss J rho KB beta*L/(beta*lambdaB))
      ((2:ℝ)^exponent*((2:ℝ)^exponent*angularK^2*(angularMesh/(2*(rho/8)))^exponent))
      (beta/L) (w/4) (L/beta*theta) ((L/beta)*(4*error/rho+8)^2),
      data.C=balancedC Phi angleAnchor ∧
      beta*(P.card : ℝ) ≤ L*(data.A.card : ℝ) ∧ beta*(B.card : ℝ) ≤ L*(data.B.card : ℝ) ∧
      data.A.card ≤ P.card ∧ data.B.card ≤ B.card := by
  have hrho := (mesh_pos n).trans_le hmesh
  let L := graphMassLoss J rho KP KB beta
  have hL : 0 < L := graphMassLoss_pos J rho hKP hKB hb
  obtain ⟨uv,huv,S,T,E,hSP,hTB,hE,hMass,hRetP,hRetB,hDense,_hSI,_hTI,hSSep,hTSep,_hSBall,hTBall,hTLine,hWitness⟩ :=
    exists_graph_aware_projection P p B b Phi G n J hP hBnon hPhi hmesh hKP hKB hb
      hr0 hw0 hw hepsilon htheta hscalar hG hdense hJ htopP htopB hKTP hKTB hB hclose hline
  let pa := fun i => source (projectionLinear uv (p i))
  let pb := fun i => direction (projectionLinear uv anchor) (projectionLinear uv (b i))
  let pc := fun phi => scalar (phi-angleAnchor)
  let Aout := S.image pa
  let Bout := T.image pb
  let Cout := Phi.image pc
  let H := imageGraph E pa pb pc
  have haInj : Set.InjOn pa (↑S) := source_injOn S p uv hrho hSSep
  have hbInj : Set.InjOn pb (↑T) := direction_injOn T b uv anchor hrho hTSep
  have hcInj : Function.Injective pc := by
    intro x y he
    have hh := scalar_injective he
    change x-angleAnchor=y-angleAnchor at hh
    linarith
  have hAcard : Aout.card=S.card := Finset.card_image_of_injOn haInj
  have hBcard : Bout.card=T.card := Finset.card_image_of_injOn hbInj
  have hCeq : Cout=balancedC Phi angleAnchor := by
    simp only [Cout,balancedC,OriginalAngularAlphabetTranslation.shifted,Finset.image_image,Function.comp_def,pc]
  have hSne : S.Nonempty := by
    by_contra h
    have hz := Finset.not_nonempty_iff_eq_empty.mp h
    rw [hz,Finset.card_empty,Nat.cast_zero,mul_zero] at hRetP
    exact (not_le_of_gt (mul_pos hb (Nat.cast_pos.mpr hP.card_pos))) hRetP
  have hTne : T.Nonempty := by
    by_contra h
    have hz := Finset.not_nonempty_iff_eq_empty.mp h
    rw [hz,Finset.card_empty,Nat.cast_zero,mul_zero] at hRetB
    exact (not_le_of_gt (mul_pos hb (Nat.cast_pos.mpr hBnon.card_pos))) hRetB
  have hImgDense := imageGraph_density S T Phi E pa pb pc hE haInj hbInj hcInj.injOn hDense
  have hDensity : (beta/L)*(Aout.card : ℝ)*(Bout.card : ℝ)*(Cout.card : ℝ) ≤ (H.card : ℝ) := by
    have hh : (beta*(Aout.card : ℝ)*(Bout.card : ℝ)*(Cout.card : ℝ))/L ≤ (H.card : ℝ) :=
      (div_le_iff₀ hL).mpr (by nlinarith only [hImgDense])
    calc
      _ = (beta*(Aout.card : ℝ)*(Bout.card : ℝ)*(Cout.card : ℝ))/L := by ring
      _ ≤ _ := hh
  have hOld := retained_edges_original_error G E p b (fun e => p (target e))
    (fun phi => phi-angleAnchor) anchor huv hrho hOriginal hWitness
  have hTargetBalanced : ∀ e ∈ E, ∃ t ∈ P, ‖pa e.1+pc e.2.2 • pb e.2.1-pa t‖ ≤ (2*error+3*rho)/8 := by
    intro e he
    obtain ⟨old,hold,_hc,herr⟩ := hOld e he
    have hePhi := (Finset.mem_product.mp (Finset.mem_product.mp (hE he)).2).2
    have hc : |e.2.2-angleAnchor| ≤ 2 := (abs_sub _ _).trans (by linarith [hAngleBox _ hePhi,hAngleBox _ hAngleAnchor])
    exact ⟨target old,hTarget old hold,
      projected_balanced_error _ _ _ _ _ hrho.le hc herr⟩
  have hCover := actual_ABC_sumset_cover S E P pa pb pc pa haInj (show 0 < rho/8 by positivity)
    (show 0 ≤ (2*error+3*rho)/8 by positivity) hb hTargetBalanced hRetP
  rw [normalized_cover_factor hrho] at hCover
  have hCsep : Separated Cout (rho/8) := by
    rw [hCeq]
    intro c hc d hd hcd
    exact (show rho/8 ≤ angularMesh/2 by linarith).trans
      (balancedC_separated Phi angleAnchor hAngSep c hc d hd hcd)
  have hBnorm : ∀ i ∈ T, ‖b i‖ ≤ 1 := by
    intro i hi
    obtain ⟨hx,hy,hz⟩ := hB i (hTB hi)
    exact max_le hx (max_le hy hz)
  let data : Data (rho/8) exponent (400*graphLoss J rho KB beta*L/(beta*lambdaB))
      ((2:ℝ)^exponent*((2:ℝ)^exponent*angularK^2*(angularMesh/(2*(rho/8)))^exponent))
      (beta/L) (w/4) (L/beta*theta) ((L/beta)*(4*error/rho+8)^2) := {
    A := Aout, B := Bout, C := Cout, G := H,
    nonemptyA := hSne.image pa, nonemptyB := hTne.image pb, nonemptyC := hPhi.image pc,
    graph_subset := imageGraph_subset S T Phi E pa pb pc hE,
    boxA := by
      intro a ha
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
      apply source_box
      exact (projectionLinear_norm_le huv (p i)).trans (by linarith [hPbox i (hSP hi)]),
    boxB := by
      intro a ha
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
      apply direction_box
      · exact (projectionLinear_norm_le huv anchor).trans (by linarith [hAnchor])
      · exact (projectionLinear_norm_le huv (b i)).trans (by linarith [hBnorm i hi]),
    boxC := by rw [hCeq]; exact balancedC_box Phi angleAnchor hAngleAnchor hAngleBox,
    separatedA := source_image_separated S p uv hrho hSSep,
    separatedB := direction_image_separated T b uv anchor hrho hTSep,
    separatedC := hCsep,
    ballB := by
      intro center R hR
      have hDK := graphLoss_pos J rho hKB hb
      have hAbs := direction_image_ball_bound T b uv anchor hrho (by positivity : 0 ≤ 50*graphLoss J rho KB beta)
        hbInj hTBall center hR
      have hAbs' : ((Bout.filter (fun q => ‖q-center‖ ≤ R)).card : ℝ) ≤
          (400*graphLoss J rho KB beta)*R/rho := by
        convert hAbs using 1; field_simp; ring
      have hRet : (B.card : ℝ) ≤ (L/beta)*(Bout.card : ℝ) := by
        rw [hBcard]
        exact reciprocal_population_bound _ _ _ _ hb hRetB
      have hh := OriginalPopulationRelative.ball_from_original_mass hrho hlambdaB
        (by positivity : 0 ≤ 400*graphLoss J rho KB beta) (by linarith : 0 ≤ R)
        hOriginalBMass hRet hAbs'
      convert hh using 1; ring,
    lineB := direction_image_strip_bound T b uv anchor hbInj hTLine,
    frostmanC := by
      rw [hCeq]
      intro center R hR
      exact balancedC_frostman Phi angleAnchor hAngMesh hAngMesh1 (by positivity : 0 < rho/8)
        (by linarith : 2*(rho/8) ≤ angularMesh) hAngK hExponent hAngAD center R hR,
    graph_density := hDensity,
    output_cover := hCover }
  refine ⟨data,hCeq,?_,?_,?_,?_⟩
  · simpa only [data,hAcard] using hRetP
  · simpa only [data,hBcard] using hRetB
  · simpa only [data,hAcard] using Finset.card_le_card hSP
  · simpa only [data,hBcard] using Finset.card_le_card hTB
end NativePlanarABCInput
