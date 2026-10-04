import Theorems.Thm_StickyKakeya4_original_w_adapted_boxes

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 2400000

noncomputable section
namespace OriginalTubeAncestorSaturation
open TwoWalkBoxComparison OriginalWAdaptedBoxes

variable {T U V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Original bounded graph tubes in maximum-product residual coordinates. -/
def graphTube (baseU u : T → U) (baseV v : T → V) (delta : ℝ) (t : T) :
    Set (SpaceTime U V) :=
  {p | |p.2.2| ≤ 1 ∧ ‖p.1-baseU t-p.2.2 • u t‖ ≤ delta ∧
    ‖p.2.1-baseV t-p.2.2 • v t‖ ≤ delta}

/-- Equality of an actual parameter ancestor controls the point residual
 relative to any other original tube in that ancestor. -/
lemma ancestor_incidence_residual (position base₁ base₂ slope₁ slope₂ : U)
    {time delta sigma : ℝ} (htime : |time| ≤ 1)
    (hinc : ‖position-base₁-time • slope₁‖ ≤ delta)
    (hbase : ‖base₁-base₂‖ ≤ sigma) (hslope : ‖slope₁-slope₂‖ ≤ sigma) :
    ‖position-base₂-time • slope₂‖ ≤ delta+2*sigma := by
  have hsigma : 0 ≤ sigma := (norm_nonneg _).trans hslope
  calc
    _ = ‖(position-base₁-time • slope₁)+(base₁-base₂)+time • (slope₁-slope₂)‖ := by
      congr 1
      module
    _ ≤ (‖position-base₁-time • slope₁‖+‖base₁-base₂‖)+‖time • (slope₁-slope₂)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (delta+sigma)+sigma := by
      apply add_le_add (add_le_add hinc hbase)
      rw [norm_smul,Real.norm_eq_abs]
      simpa only [one_mul] using mul_le_mul htime hslope (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    _ = delta+2*sigma := by ring

/-- A realizer original tube and the retained terminal tube share the SAME
 pointwise affine direction graph. No comparison between distinct points'
 graph intercepts is used. -/
lemma same_point_normal_direction (F : U →L[ℝ] V) (offset v₁ v₂ : V) (u₁ u₂ : U)
    {error : ℝ} (h₁ : ‖v₁-offset-F u₁‖ ≤ error)
    (h₂ : ‖v₂-offset-F u₂‖ ≤ error) :
    ‖(v₂-v₁)-F (u₂-u₁)‖ ≤ 2*error := by
  calc
    _ = ‖(v₂-offset-F u₂)-(v₁-offset-F u₁)‖ := by
      rw [map_sub]
      congr 1
      abel
    _ ≤ ‖v₂-offset-F u₂‖+‖v₁-offset-F u₁‖ := norm_sub_le _ _
    _ ≤ 2*error := by linarith

/-- Every original fine tube in the literal sigma-parameter ancestor of a
 realizer fine-direction realizer is contained in a controlled adapted box.
 The hypotheses are primitive point incidences, same-point direction graphs,
 and parameter-coordinate gaps; box density is a derived later count. -/
theorem ancestor_fiber_inside_adapted_box
    (baseU u : T → U) (baseV v : T → V) (F : U →L[ℝ] V)
    (centerX : U) (centerY offset : V) (z : ℝ) (terminal realizer descendant : T)
    {delta sigma rho A IncErr DirErr Tang L : ℝ}
    (hd : 0 ≤ delta) (hdσ : delta ≤ sigma) (hσρ : sigma ≤ rho)
    (hA : 0 ≤ A) (hInc : 0 ≤ IncErr) (hDir : 0 ≤ DirErr)
    (hF : ‖F‖ ≤ A) (hz : |z| ≤ 1)
    (hcenterU : ‖centerX-baseU realizer-z • u realizer‖ ≤ IncErr*delta)
    (hcenterV : ‖centerY-baseV realizer-z • v realizer‖ ≤ IncErr*delta)
    (hdir₁ : ‖v terminal-offset-F (u terminal)‖ ≤ DirErr*delta)
    (hdir₂ : ‖v realizer-offset-F (u realizer)‖ ≤ DirErr*delta)
    (hlocal : ‖u realizer-u terminal‖ ≤ Tang*rho)
    (hbaseU : ‖baseU descendant-baseU realizer‖ ≤ sigma)
    (hbaseV : ‖baseV descendant-baseV realizer‖ ≤ sigma)
    (hslopeU : ‖u descendant-u realizer‖ ≤ sigma)
    (hslopeV : ‖v descendant-v realizer‖ ≤ sigma)
    (hLt : 2 ≤ L) (hLx : 3+IncErr+2*Tang ≤ L)
    (hLn : (1+A)*(3+IncErr)+4*DirErr ≤ L) :
    graphTube baseU u baseV v delta descendant ⊆
      box F (terminalWalk (fun _ : Unit => centerX) (fun _ : Unit => centerY)
        u v () terminal) z rho sigma L := by
  intro p hp
  obtain ⟨ht,hiU,hiV⟩ := hp
  have hsigma : 0 ≤ sigma := hd.trans hdσ
  have hrho : 0 ≤ rho := hsigma.trans hσρ
  have htlocalU := ancestor_incidence_residual p.1 (baseU descendant) (baseU realizer)
    (u descendant) (u realizer) ht hiU hbaseU hslopeU
  have htlocalV := ancestor_incidence_residual p.2.1 (baseV descendant) (baseV realizer)
    (v descendant) (v realizer) ht hiV hbaseV hslopeV
  have htime : |p.2.2-z| ≤ 2 := (abs_sub _ _).trans (by linarith)
  let eU := p.1-centerX-(p.2.2-z) • u realizer
  let eV := p.2.1-centerY-(p.2.2-z) • v realizer
  have heU : ‖eU‖ ≤ (1+IncErr)*delta+2*sigma := by
    calc
      _ = ‖(p.1-baseU realizer-p.2.2 • u realizer)-(centerX-baseU realizer-z • u realizer)‖ := by
        congr 1
        dsimp [eU]
        module
      _ ≤ ‖p.1-baseU realizer-p.2.2 • u realizer‖+‖centerX-baseU realizer-z • u realizer‖ := norm_sub_le _ _
      _ ≤ (1+IncErr)*delta+2*sigma := by linarith
  have heV : ‖eV‖ ≤ (1+IncErr)*delta+2*sigma := by
    calc
      _ = ‖(p.2.1-baseV realizer-p.2.2 • v realizer)-(centerY-baseV realizer-z • v realizer)‖ := by
        congr 1
        dsimp [eV]
        module
      _ ≤ ‖p.2.1-baseV realizer-p.2.2 • v realizer‖+‖centerY-baseV realizer-z • v realizer‖ := norm_sub_le _ _
      _ ≤ (1+IncErr)*delta+2*sigma := by linarith
  have hn := same_point_normal_direction F offset (v terminal) (v realizer) (u terminal) (u realizer) hdir₁ hdir₂
  have heUσ : ‖eU‖ ≤ (3+IncErr)*sigma := by
    have hh := mul_le_mul_of_nonneg_left hdσ (show 0 ≤ 1+IncErr by positivity)
    nlinarith
  have heVσ : ‖eV‖ ≤ (3+IncErr)*sigma := by
    have hh := mul_le_mul_of_nonneg_left hdσ (show 0 ≤ 1+IncErr by positivity)
    nlinarith
  refine ⟨htime.trans hLt,?_,?_⟩
  · change ‖p.1-centerX-(p.2.2-z) • u terminal‖ ≤ L*rho
    calc
      _ = ‖eU+(p.2.2-z) • (u realizer-u terminal)‖ := by congr 1; dsimp [eU]; module
      _ ≤ ‖eU‖+‖(p.2.2-z) • (u realizer-u terminal)‖ := norm_add_le _ _
      _ ≤ (3+IncErr)*sigma+2*(Tang*rho) := by
        apply add_le_add heUσ
        rw [norm_smul,Real.norm_eq_abs]
        exact mul_le_mul htime hlocal (norm_nonneg _) (by norm_num)
      _ ≤ (3+IncErr)*rho+2*(Tang*rho) := by gcongr
      _ = (3+IncErr+2*Tang)*rho := by ring
      _ ≤ L*rho := mul_le_mul_of_nonneg_right hLx hrho
  · change ‖p.2.1-centerY-(p.2.2-z) • v terminal-F (p.1-centerX-(p.2.2-z) • u terminal)‖ ≤ L*sigma
    calc
      _ = ‖(eV-F eU)+(p.2.2-z) • ((v realizer-v terminal)-F (u realizer-u terminal))‖ := by
        congr 1
        dsimp [eU,eV]
        simp only [map_sub,map_smul]
        module
      _ ≤ (‖eV‖+‖F eU‖)+‖(p.2.2-z) • ((v realizer-v terminal)-F (u realizer-u terminal))‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ ((3+IncErr)*sigma+A*((3+IncErr)*sigma))+2*(2*(DirErr*delta)) := by
        apply add_le_add
        · apply add_le_add heVσ
          exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hF heUσ (norm_nonneg _) hA)
        · rw [norm_smul,Real.norm_eq_abs]
          exact mul_le_mul htime hn (norm_nonneg _) (by norm_num)
      _ ≤ ((3+IncErr)*sigma+A*((3+IncErr)*sigma))+2*(2*(DirErr*sigma)) := by gcongr
      _ = ((1+A)*(3+IncErr)+4*DirErr)*sigma := by ring
      _ ≤ L*sigma := mul_le_mul_of_nonneg_right hLn hsigma

/-- The actual half-open scalar and planar parameter grids. -/
def grid₁ (sigma x : ℝ) : ℤ := ⌊x/sigma⌋
def grid₂ (sigma : ℝ) (x : ℝ × ℝ) : ℤ × ℤ := (grid₁ sigma x.1,grid₁ sigma x.2)

def parameterAncestor {CU CV : Type*} (gridU : U → CU) (gridV : V → CV)
    (baseU u : T → U) (baseV v : T → V) (t : T) : (CU × CV) × (CU × CV) :=
  ((gridU (baseU t),gridV (baseV t)),(gridU (u t),gridV (v t)))

lemma scalar_same_parameter_cell {sigma x y : ℝ} (hsigma : 0 < sigma)
    (h : grid₁ sigma x=grid₁ sigma y) : ‖x-y‖ ≤ sigma :=
  FiniteTransverseMenuGrowth.same_floor_abs_sub_le hsigma h

lemma planar_same_parameter_cell {sigma : ℝ} {x y : ℝ × ℝ} (hsigma : 0 < sigma)
    (h : grid₂ sigma x=grid₂ sigma y) : ‖x-y‖ ≤ sigma := by
  have h₁ := scalar_same_parameter_cell hsigma (congrArg Prod.fst h)
  have h₂ := scalar_same_parameter_cell hsigma (congrArg Prod.snd h)
  exact max_le h₁ h₂

/-- All four geometric parameter gaps in the a=1 original tube model follow
 from equality of the literal six-coordinate ancestor label. -/
theorem scalar_parameter_ancestor_gaps (baseU u : T → ℝ) (baseV v : T → ℝ × ℝ)
    {sigma : ℝ} (hsigma : 0 < sigma) (s t : T)
    (h : parameterAncestor (grid₁ sigma) (grid₂ sigma) baseU u baseV v s=
      parameterAncestor (grid₁ sigma) (grid₂ sigma) baseU u baseV v t) :
    ‖baseU s-baseU t‖ ≤ sigma ∧ ‖baseV s-baseV t‖ ≤ sigma ∧
      ‖u s-u t‖ ≤ sigma ∧ ‖v s-v t‖ ≤ sigma := by
  exact ⟨scalar_same_parameter_cell hsigma (congrArg (fun a => a.1.1) h),
    planar_same_parameter_cell hsigma (congrArg (fun a => a.1.2) h),
    scalar_same_parameter_cell hsigma (congrArg (fun a => a.2.1) h),
    planar_same_parameter_cell hsigma (congrArg (fun a => a.2.2) h)⟩

/-- The a=2 version uses the same full original tube parameter cell. -/
theorem planar_parameter_ancestor_gaps (baseU u : T → ℝ × ℝ) (baseV v : T → ℝ)
    {sigma : ℝ} (hsigma : 0 < sigma) (s t : T)
    (h : parameterAncestor (grid₂ sigma) (grid₁ sigma) baseU u baseV v s=
      parameterAncestor (grid₂ sigma) (grid₁ sigma) baseU u baseV v t) :
    ‖baseU s-baseU t‖ ≤ sigma ∧ ‖baseV s-baseV t‖ ≤ sigma ∧
      ‖u s-u t‖ ≤ sigma ∧ ‖v s-v t‖ ≤ sigma := by
  exact ⟨planar_same_parameter_cell hsigma (congrArg (fun a => a.1.1) h),
    scalar_same_parameter_cell hsigma (congrArg (fun a => a.1.2) h),
    planar_same_parameter_cell hsigma (congrArg (fun a => a.2.1) h),
    scalar_same_parameter_cell hsigma (congrArg (fun a => a.2.2) h)⟩

omit [NormedSpace ℝ U] in
/-- Actual fine-direction approximation transfers a rho-near fine label
 to a tangent gap between its original tube realizer and the terminal tube. -/
lemma fine_label_realizer_tangent_gap (terminalSlope realizerSlope phi₀ phi : U)
    {delta rho Error : ℝ} (hd : delta ≤ rho) (hError : 0 ≤ Error)
    (hterminal : ‖terminalSlope-phi₀‖ ≤ Error*delta)
    (hrealizer : ‖realizerSlope-phi‖ ≤ Error*delta)
    (hnear : ‖phi-phi₀‖ ≤ rho) :
    ‖realizerSlope-terminalSlope‖ ≤ (1+2*Error)*rho := by
  calc
    _ = ‖(realizerSlope-phi)+(phi-phi₀)-(terminalSlope-phi₀)‖ := by congr 1; abel
    _ ≤ (‖realizerSlope-phi‖+‖phi-phi₀‖)+‖terminalSlope-phi₀‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ (Error*delta+rho)+Error*delta := add_le_add (add_le_add hrealizer hnear) hterminal
    _ ≤ (Error*rho+rho)+Error*rho := by gcongr
    _ = (1+2*Error)*rho := by ring

end OriginalTubeAncestorSaturation
