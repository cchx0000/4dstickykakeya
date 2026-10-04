import Theorems.Thm_StickyKakeya4_native_scheduled_scale_selection
import Theorems.Thm_StickyKakeya4_original_coarse_height_population_ratio
import Theorems.Thm_StickyKakeya4_original_menu_bc_graph
import Theorems.Thm_StickyKakeya4_original_coarse_height_tube_transfer
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3000000
noncomputable section
namespace NativeScheduledHeightPopulation
open Classical NativeScheduledScaleSelection NativeDyadicMeshSelection
open DyadicOriginalFiberSelection OriginalCoarseHeightCurve OriginalCoarseHeightPopulationRatio
open OriginalHeightGraphDensity OriginalHeightGraphCoarsening OriginalMenuSection
open FinitePlaneProjectionGrid
/-- The original slope law uses actual floor cells only at scheduled scales. -/
def ScheduledSlopeOscillation (delta eta Lip : ℝ) (Z : Finset ℝ) (f : ℝ → ℝ × ℝ) : Prop :=
  ScheduledLaw delta eta (fun sigma => ∀ z ∈ Z, ∀ w ∈ Z,
    coarseHeight sigma z=coarseHeight sigma w → ‖f z-f w‖ ≤ Lip*sigma)
/-- The identical spatial normalization used for the phase population. -/
def normalizedGraph (rho S0 Lip z₀ : ℝ) (f₀ : ℝ × ℝ) (f : ℝ → ℝ × ℝ) : ℝ → Point3 :=
  heightGraph (rho*S0) Lip z₀ f₀ f
lemma normalizedGraph_eq_common_scaling (rho S0 Lip z₀ : ℝ)
    (f₀ : ℝ × ℝ) (f : ℝ → ℝ × ℝ) (z : ℝ) :
    normalizedGraph rho S0 Lip z₀ f₀ f z=S0⁻¹ • heightGraph rho Lip z₀ f₀ f z := by
  ext <;> simp only [normalizedGraph,heightGraph,Prod.smul_fst,Prod.smul_snd,
    Prod.fst_sub,Prod.snd_sub,smul_eq_mul,mul_inv_rev,div_eq_mul_inv] <;> ring
/-- Coarse labels have an absolute one-dimensional cap already at the
 target projection mesh. No separation or desired B profile is assumed. -/
theorem actual_labels_KT (Q : Finset ℤ) (sample : ℤ → ℝ)
    {rho S0 r sigma : ℝ} (hrho : 0 < rho) (hS : 0 < S0) (hr : 0 < r) (hrs : r ≤ sigma)
    (hlabel : ∀ k ∈ Q, coarseHeight sigma (sample k)=k)
    (Lip z₀ : ℝ) (f₀ : ℝ × ℝ) (f : ℝ → ℝ × ℝ)
    (center : Point3) {R : ℝ} (hR : r/(rho*S0) ≤ R) :
    ((Q.filter (fun k => ‖normalizedGraph rho S0 Lip z₀ f₀ f (sample k)-center‖ ≤ R)).card : ℝ)
      ≤ 4*R/(r/(rho*S0)) := by
  have hp : 0 < rho*S0 := mul_pos hrho hS
  have hs : 0 < sigma := hr.trans_le hrs
  have hR0 : 0 ≤ R := (div_pos hr hp).le.trans hR
  have hh := sampled_curve_ball_cap Q sample hp hs hlabel Lip z₀ f₀ f center hR0
  have hbase : 1 ≤ (rho*S0*R)/r := (le_div_iff₀ hr).mpr (by
    have ht := (div_le_iff₀ hp).mp hR
    nlinarith only [ht])
  have hmon := div_le_div_of_nonneg_left (mul_nonneg hp.le hR0) hr hrs
  have hid : 4*R/(r/(rho*S0))=4*((rho*S0*R)/r) := by field_simp
  rw [hid]
  change ((Q.filter (fun k => ‖heightGraph (rho*S0) Lip z₀ f₀ f (sample k)-center‖ ≤ R)).card : ℝ) ≤ _
  calc
    _ ≤ 2*(rho*S0)*R/sigma+2 := hh
    _ = 2*((rho*S0*R)/sigma)+2 := by ring
    _ ≤ _ := by linarith only [hbase,hmon]
/-- The graph-selected original height bin retains its literal floor-cell
 carrier under the common scaling and target-mesh choice. -/
theorem selected_labels_KT (Z : Finset ℝ) (j : ℕ)
    {rho S0 r sigma : ℝ} (hrho : 0 < rho) (hS : 0 < S0) (hr : 0 < r) (hrs : r ≤ sigma)
    (hbin : (bin Z (coarseHeight sigma) j).Nonempty)
    (Lip z₀ : ℝ) (f₀ : ℝ × ℝ) (f : ℝ → ℝ × ℝ) :
    let Q := (bin Z (coarseHeight sigma) j).image (coarseHeight sigma)
    let sample := representative (bin Z (coarseHeight sigma) j) hbin sigma
    let b := fun k => normalizedGraph rho S0 Lip z₀ f₀ f (sample k)
    ∀ i ∈ Q, ∀ R : ℝ, r/(rho*S0) ≤ R →
      ((Q.filter (fun k => dist3 (b i) (b k) ≤ R)).card : ℝ) ≤ 4*R/(r/(rho*S0)) := by
  dsimp only
  intro i _hi R hR
  have hh := actual_labels_KT ((bin Z (coarseHeight sigma) j).image (coarseHeight sigma))
    (representative (bin Z (coarseHeight sigma) j) hbin sigma) hrho hS hr hrs
    (fun k hk => (representative_spec _ hbin sigma k hk).2) Lip z₀ f₀ f
    (normalizedGraph rho S0 Lip z₀ f₀ f (representative (bin Z (coarseHeight sigma) j) hbin sigma i)) hR
  simpa only [dist3_eq_norm,norm_sub_rev] using hh
/-- Exact population transport. The scheduled overshoot and common
 spatial normalization appear as the explicit ratio r/(sigma*S0). -/
theorem selected_height_mass_exact (Z : Finset ℝ) (j : ℕ)
    {delta sigma rho S0 r beta lambda loss : ℝ}
    (hd : 0 < delta) (hsigma : delta ≤ sigma) (hrho : 0 < rho) (hS : 0 < S0)
    (hr : 0 < r) (hbeta : 0 ≤ beta) (hloss : 0 < loss)
    (hsep : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → delta ≤ |z-w|)
    (hdensity : lambda*rho ≤ (Z.card : ℝ)*delta)
    (hretention : beta*(Z.card : ℝ) ≤ loss*((bin Z (coarseHeight sigma) j).card : ℝ)) :
    beta*lambda*r/(3*loss*sigma*S0) ≤ (r/(rho*S0))*
      (((bin Z (coarseHeight sigma) j).image (coarseHeight sigma)).card : ℝ) := by
  have hs : 0 < sigma := hd.trans_le hsigma
  have hm := original_coarse_height_mass Z j hd hrho hsigma hbeta hloss hsep hdensity hretention
  have hh := mul_le_mul_of_nonneg_right hm (div_pos hr (mul_pos hs hS)).le
  calc
    _ = (beta*lambda/(3*loss))*(r/(sigma*S0)) := by ring
    _ ≤ (sigma/rho*(((bin Z (coarseHeight sigma) j).image (coarseHeight sigma)).card : ℝ))*(r/(sigma*S0)) := hh
    _ = _ := by field_simp
/-- Uniform lower mass after charging the actual scheduled overshoot. -/
theorem selected_height_mass (Z : Finset ℝ) (j : ℕ)
    {delta eta sigma rho S0 r beta lambda loss : ℝ}
    (hd : 0 < delta) (hsigma : delta ≤ sigma) (hrho : 0 < rho) (hS : 0 < S0)
    (hr : 0 < r) (hbeta : 0 ≤ beta) (hlambda : 0 ≤ lambda) (hloss : 0 < loss)
    (hover : sigma ≤ delta^(-eta)*r)
    (hsep : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → delta ≤ |z-w|)
    (hdensity : lambda*rho ≤ (Z.card : ℝ)*delta)
    (hretention : beta*(Z.card : ℝ) ≤ loss*((bin Z (coarseHeight sigma) j).card : ℝ)) :
    beta*lambda/(3*loss*S0*delta^(-eta)) ≤ (r/(rho*S0))*
      (((bin Z (coarseHeight sigma) j).image (coarseHeight sigma)).card : ℝ) := by
  have hs : 0 < sigma := hd.trans_le hsigma
  have hp : 0 < delta^(-eta) := Real.rpow_pos_of_pos hd _
  have hm := selected_height_mass_exact Z j hd hsigma hrho hS hr hbeta hloss hsep hdensity hretention
  have hden : 3*loss*sigma*S0 ≤ (3*loss*S0*delta^(-eta))*r := by
    have hh := mul_le_mul_of_nonneg_left hover (show 0 ≤ 3*loss*S0 by positivity)
    nlinarith only [hh]
  have hh := div_le_div_of_nonneg_left (show 0 ≤ beta*lambda*r by positivity)
    (show 0 < 3*loss*sigma*S0 by positivity) hden
  have heq : beta*lambda*r/((3*loss*S0*delta^(-eta))*r)=beta*lambda/(3*loss*S0*delta^(-eta)) := by
    field_simp
  rw [heq] at hh
  exact hh.trans hm
/-- Use the source law at the selected scheduled scale for the actual
 representative. An arbitrary r-cell oscillation premise is never used. -/
theorem scheduled_representative_error (Z : Finset ℝ) (j n : ℕ)
    {delta eta rho S0 Lip : ℝ} (hrho : 0 < rho) (hS : 0 < S0) (hLip : 0 < Lip)
    (hd : 0 < delta) (hslo : delta ≤ scheduledScale delta eta n)
    (hshi : scheduledScale delta eta n ≤ 1)
    (hbin : (bin Z (coarseHeight (scheduledScale delta eta n)) j).Nonempty)
    (z₀ : ℝ) (f₀ : ℝ × ℝ) (f : ℝ → ℝ × ℝ)
    (hsource : ScheduledSlopeOscillation delta eta Lip Z f)
    (z : ℝ) (hz : z ∈ bin Z (coarseHeight (scheduledScale delta eta n)) j) :
    let sigma := scheduledScale delta eta n
    let sample := representative (bin Z (coarseHeight sigma) j) hbin sigma
    ‖normalizedGraph rho S0 Lip z₀ f₀ f z-
      normalizedGraph rho S0 Lip z₀ f₀ f (sample (coarseHeight sigma z))‖ ≤ sigma/(rho*S0) := by
  let sigma := scheduledScale delta eta n
  let W := bin Z (coarseHeight sigma) j
  let k := coarseHeight sigma z
  have hk : k ∈ W.image (coarseHeight sigma) := Finset.mem_image_of_mem _ hz
  have hrep := representative_spec W hbin sigma k hk
  have hzZ : z ∈ Z := (Finset.mem_filter.mp hz).1
  have hwZ : representative W hbin sigma k ∈ Z := (Finset.mem_filter.mp hrep.1).1
  have hcell : coarseHeight sigma z=coarseHeight sigma (representative W hbin sigma k) := hrep.2.symm
  have hosc := scheduled_law_at_selected hsource n hslo hshi
  exact same_cell_graph_error (mul_pos hrho hS) hLip (hd.trans_le hslo) z₀ f₀ f hcell
    (hosc z hzZ _ hwZ hcell)
/-- At the paper's target r=rho^2, the scheduled replacement costs at most
 delta^(-eta) times the normalized target mesh. -/
theorem scheduled_error_ratio {delta eta sigma rho S0 r : ℝ}
    (hrho : 0 < rho) (hS : 0 < S0) (hover : sigma ≤ delta^(-eta)*r) :
    sigma/(rho*S0) ≤ delta^(-eta)*(r/(rho*S0)) := by
  calc
    _ ≤ (delta^(-eta)*r)/(rho*S0) := div_le_div_of_nonneg_right hover (mul_pos hrho hS).le
    _ = _ := by ring
/-- Transport this actual selected population to a COMMON nearby mesh,
 preserving the original carrier and charging only the factor two. -/
theorem selected_population_at_nearby_mesh (Z : Finset ℝ) (j : ℕ)
    {delta eta sigma rho S0 r beta lambda loss mu : ℝ}
    (hd : 0 < delta) (hsigma : delta ≤ sigma) (hrho : 0 < rho) (hS : 0 < S0)
    (hr : 0 < r) (hrs : r ≤ sigma) (hbeta : 0 ≤ beta) (hlambda : 0 ≤ lambda) (hloss : 0 < loss)
    (hover : sigma ≤ delta^(-eta)*r)
    (hhalf : (r/(rho*S0))/2 ≤ mu) (hmu : mu ≤ r/(rho*S0))
    (hsep : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → delta ≤ |z-w|)
    (hdensity : lambda*rho ≤ (Z.card : ℝ)*delta)
    (hretention : beta*(Z.card : ℝ) ≤ loss*((bin Z (coarseHeight sigma) j).card : ℝ))
    (hbin : (bin Z (coarseHeight sigma) j).Nonempty)
    (Lip z₀ : ℝ) (f₀ : ℝ × ℝ) (f : ℝ → ℝ × ℝ) :
    let Q := (bin Z (coarseHeight sigma) j).image (coarseHeight sigma)
    let sample := representative (bin Z (coarseHeight sigma) j) hbin sigma
    let b := fun k => normalizedGraph rho S0 Lip z₀ f₀ f (sample k)
    beta*lambda/(6*loss*S0*delta^(-eta)) ≤ mu*(Q.card : ℝ) ∧
      ∀ i ∈ Q, ∀ R : ℝ, mu ≤ R →
        ((Q.filter (fun k => dist3 (b i) (b k) ≤ R)).card : ℝ) ≤ 4*R/mu := by
  dsimp only
  have ht : 0 < r/(rho*S0) := div_pos hr (mul_pos hrho hS)
  have hmu0 : 0 < mu := (half_pos ht).trans_le hhalf
  have hm := selected_height_mass Z j hd hsigma hrho hS hr hbeta hlambda hloss hover hsep hdensity hretention
  have hm' := original_mass_at_nearby_mesh hhalf (Nat.cast_nonneg _) hm
  have heq : beta*lambda/(3*loss*S0*delta^(-eta))/2=beta*lambda/(6*loss*S0*delta^(-eta)) := by ring
  rw [heq] at hm'
  refine ⟨hm',?_⟩
  exact original_KT_at_finer_mesh _ _ ht hmu0 hmu (by norm_num : (0:ℝ)≤4)
    (selected_labels_KT Z j hrho hS hr hrs hbin Lip z₀ f₀ f)
/-- Exact dyadic lowering can be selected after the analytic index cutoff.
 The input mass and KT law are derived again from original height data. -/
theorem exists_dyadic_selected_population (Z : Finset ℝ) (j : ℕ)
    {delta eta sigma rho S0 r beta lambda loss : ℝ}
    (hd : 0 < delta) (hsigma : delta ≤ sigma) (hrho : 0 < rho) (hS : 0 < S0)
    (hr : 0 < r) (hrs : r ≤ sigma) (hbeta : 0 ≤ beta) (hlambda : 0 ≤ lambda) (hloss : 0 < loss)
    (hover : sigma ≤ delta^(-eta)*r)
    (ht1 : r/(rho*S0) ≤ 1) (n0 : ℕ) (hcutoff : r/(rho*S0) ≤ ((2:ℝ)^n0)⁻¹)
    (hsep : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → delta ≤ |z-w|)
    (hdensity : lambda*rho ≤ (Z.card : ℝ)*delta)
    (hretention : beta*(Z.card : ℝ) ≤ loss*((bin Z (coarseHeight sigma) j).card : ℝ))
    (hbin : (bin Z (coarseHeight sigma) j).Nonempty)
    (Lip z₀ : ℝ) (f₀ : ℝ × ℝ) (f : ℝ → ℝ × ℝ) :
    let Q := (bin Z (coarseHeight sigma) j).image (coarseHeight sigma)
    let sample := representative (bin Z (coarseHeight sigma) j) hbin sigma
    let b := fun k => normalizedGraph rho S0 Lip z₀ f₀ f (sample k)
    ∃ m : ℕ, n0 ≤ m ∧ (r/(rho*S0))/2 ≤ ((2:ℝ)^m)⁻¹ ∧ ((2:ℝ)^m)⁻¹ < r/(rho*S0) ∧
      beta*lambda/(6*loss*S0*delta^(-eta)) ≤ ((2:ℝ)^m)⁻¹*(Q.card : ℝ) ∧
      ∀ i ∈ Q, ∀ R : ℝ, ((2:ℝ)^m)⁻¹ ≤ R →
        ((Q.filter (fun k => dist3 (b i) (b k) ≤ R)).card : ℝ) ≤ 4*R/((2:ℝ)^m)⁻¹ := by
  dsimp only
  obtain ⟨m,hm,hlo,hhi⟩ := exists_nearby_dyadic_mesh (div_pos hr (mul_pos hrho hS)) ht1 n0 hcutoff
  exact ⟨m,hm,hlo,hhi,selected_population_at_nearby_mesh Z j hd hsigma hrho hS hr hrs hbeta
    hlambda hloss hover hlo hhi.le hsep hdensity hretention hbin Lip z₀ f₀ f⟩
/-- End-to-end original B supplier: select an admissible scheduled scale,
 then use the actual menu section and its graph-weighted height bin.
 The output retains literal original heights and their endpoint witnesses. -/
theorem exists_scheduled_actual_B_population {A C : Type*}
    [DecidableEq A] [DecidableEq C]
    (X : Finset A) (Z : Finset ℝ) (Phi : Finset C)
    (G : Finset (A × ((ℝ × ℝ) × (C × C))))
    {delta eta rho S0 r Lip beta lambda : ℝ}
    (hd : 0 < delta) (hd1 : delta < 1) (heta : 0 < eta)
    (hdr : delta ≤ r) (hr1 : r ≤ 1) (hrho : 0 < rho) (hS : 0 < S0) (hLip : 0 < Lip)
    (hbeta : 0 ≤ beta) (hlambda : 0 ≤ lambda)
    (hGne : G.Nonempty) (hG : G ⊆ X ×ˢ ((Z ×ˢ Z) ×ˢ (Phi ×ˢ Phi)))
    (hgraph : beta*(X.card : ℝ)*(Z.card : ℝ)^2*(Phi.card : ℝ)^2 ≤ (G.card : ℝ))
    (hsep : ∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → delta ≤ |z-w|)
    (hheight : lambda*rho ≤ (Z.card : ℝ)*delta)
    (z₀ : ℝ) (f₀ : ℝ × ℝ) (f : ℝ → ℝ × ℝ)
    (hsource : ScheduledSlopeOscillation delta eta Lip Z f) :
    ∃ n : ℕ, delta ≤ scheduledScale delta eta n ∧ scheduledScale delta eta n ≤ 1 ∧
      r ≤ scheduledScale delta eta n ∧ scheduledScale delta eta n ≤ delta^(-eta)*r ∧
      ∃ q ∈ Z ×ˢ Phi, ∃ j < levelCount Z,
      ∃ hbin : (bin Z (coarseHeight (scheduledScale delta eta n)) j).Nonempty,
      let sigma := scheduledScale delta eta n
      let W := bin Z (coarseHeight sigma) j
      let Q := W.image (coarseHeight sigma)
      let sample := representative W hbin sigma
      let b := fun k => normalizedGraph rho S0 Lip z₀ f₀ f (sample k)
      let H := coarseGraph (edgeBin (sectionGraph G q) Z (coarseHeight sigma) j) (coarseHeight sigma)
      (edgeBin (sectionGraph G q) Z (coarseHeight sigma) j).Nonempty ∧
      beta*(Z.card : ℝ) ≤ (levelCount Z : ℝ)*(W.card : ℝ) ∧
      beta*(X.card : ℝ)*(Q.card : ℝ)*(Phi.card : ℝ) ≤ 2*(levelCount Z : ℝ)*(H.card : ℝ) ∧
      H ⊆ X ×ˢ (Q ×ˢ Phi) ∧
      (∀ k ∈ Q, sample k ∈ Z ∧ coarseHeight sigma (sample k)=k) ∧
      beta*lambda/(3*(levelCount Z : ℝ)*S0*delta^(-eta)) ≤ (r/(rho*S0))*(Q.card : ℝ) ∧
      (∀ i ∈ Q, ∀ R : ℝ, r/(rho*S0) ≤ R →
        ((Q.filter (fun k => dist3 (b i) (b k) ≤ R)).card : ℝ) ≤ 4*R/(r/(rho*S0))) ∧
      ∀ a k c, (a,(k,c)) ∈ H → ∃ z ∈ W, coarseHeight sigma z=k ∧
        (a,((q.1,z),(q.2,c))) ∈ G ∧
        ‖normalizedGraph rho S0 Lip z₀ f₀ f z-b k‖ ≤ sigma/(rho*S0) := by
  obtain ⟨n,hslo,hshi,hrs,hover⟩ := exists_scheduled_scale_above hd hd1 heta hdr hr1
  let sigma := scheduledScale delta eta n
  obtain ⟨q,hq,j,hj,hne,hbin,hret,hden,hsub,_hfib,hwit⟩ :=
    OriginalMenuBCGraph.exists_actual_BC_graph X Z Phi G hGne hG (coarseHeight sigma) hbeta hgraph
  have hlevel : 0 < (levelCount Z : ℝ) := by unfold levelCount; positivity
  refine ⟨n,hslo,hshi,hrs,hover,q,hq,j,hj,hbin,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact hne
  · exact hret
  · exact hden
  · exact hsub
  · intro k hk
    have hh := representative_spec _ hbin sigma k hk
    exact ⟨(Finset.mem_filter.mp hh.1).1,hh.2⟩
  · exact selected_height_mass Z j hd hslo hrho hS (hd.trans_le hdr) hbeta hlambda hlevel
      hover hsep hheight hret
  · exact selected_labels_KT Z j hrho hS (hd.trans_le hdr) hrs hbin Lip z₀ f₀ f
  · intro a k c he
    obtain ⟨z,hz,hk,hGz⟩ := hwit a k c he
    refine ⟨z,hz,hk,hGz,?_⟩
    have herr := scheduled_representative_error Z j n hrho hS hLip hd hslo hshi hbin z₀ f₀ f hsource z hz
    dsimp only at herr ⊢
    change coarseHeight (scheduledScale delta eta n) z=k at hk
    simpa only [hk] using herr
/-- The original unnormalized field-coordinate replacement, before the
 slope-coordinate balancing, pays Lip times the scheduled overshoot. -/
theorem scheduled_field_error (Z : Finset ℝ) (n : ℕ)
    {delta eta rho S0 Lip r : ℝ} (hrho : 0 < rho) (hS : 0 < S0) (hLip : 0 ≤ Lip)
    (hslo : delta ≤ scheduledScale delta eta n) (hshi : scheduledScale delta eta n ≤ 1)
    (hover : scheduledScale delta eta n ≤ delta^(-eta)*r)
    (f : ℝ → ℝ × ℝ) (hsource : ScheduledSlopeOscillation delta eta Lip Z f)
    (z w : ℝ) (hz : z ∈ Z) (hw : w ∈ Z)
    (hcell : coarseHeight (scheduledScale delta eta n) z=coarseHeight (scheduledScale delta eta n) w) :
    ‖f z-f w‖/(rho*S0) ≤ Lip*delta^(-eta)*(r/(rho*S0)) := by
  have hosc := scheduled_law_at_selected hsource n hslo hshi z hz w hw hcell
  calc
    _ ≤ (Lip*scheduledScale delta eta n)/(rho*S0) :=
      div_le_div_of_nonneg_right hosc (mul_pos hrho hS).le
    _ ≤ (Lip*(delta^(-eta)*r))/(rho*S0) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hover hLip) (mul_pos hrho hS).le
    _ = _ := by ring
/-- With the paper's Lip=delta^(-eta), the source-coordinate error is
 delta^(-2*eta) times the actual normalized target mesh. -/
theorem paper_scheduled_field_error (Z : Finset ℝ) (n : ℕ)
    {delta eta rho S0 r : ℝ} (hd : 0 < delta) (hrho : 0 < rho) (hS : 0 < S0)
    (hslo : delta ≤ scheduledScale delta eta n) (hshi : scheduledScale delta eta n ≤ 1)
    (hover : scheduledScale delta eta n ≤ delta^(-eta)*r)
    (f : ℝ → ℝ × ℝ) (hsource : ScheduledSlopeOscillation delta eta (delta^(-eta)) Z f)
    (z w : ℝ) (hz : z ∈ Z) (hw : w ∈ Z)
    (hcell : coarseHeight (scheduledScale delta eta n) z=coarseHeight (scheduledScale delta eta n) w) :
    ‖f z-f w‖/(rho*S0) ≤ delta^(-2*eta)*(r/(rho*S0)) := by
  have hh := scheduled_field_error Z n hrho hS (Real.rpow_pos_of_pos hd (-eta)).le hslo hshi hover f hsource z w hz hw hcell
  have heq : delta^(-eta)*delta^(-eta)=delta^(-2*eta) := by
    rw [← Real.rpow_add hd]
    congr 1
    ring
  simpa only [heq] using hh
/-- A literal enclosing scheduled cell supplies the spatial envelope from
 the source slope law and its actual floor label. -/
theorem scheduled_graph_envelope (Z : Finset ℝ) (n : ℕ)
    {delta eta rho S0 Lip : ℝ} (hd : 0 < delta) (hrho : 0 < rho) (hS : 0 < S0) (hLip : 0 < Lip)
    (hslo : delta ≤ scheduledScale delta eta n) (hshi : scheduledScale delta eta n ≤ 1)
    (f : ℝ → ℝ × ℝ) (hsource : ScheduledSlopeOscillation delta eta Lip Z f)
    (z₀ : ℝ) (hz₀ : z₀ ∈ Z) (z : ℝ) (hz : z ∈ Z)
    (hcell : coarseHeight (scheduledScale delta eta n) z=coarseHeight (scheduledScale delta eta n) z₀) :
    ‖normalizedGraph rho S0 Lip z₀ (f z₀) f z‖ ≤ scheduledScale delta eta n/(rho*S0) := by
  have hosc := scheduled_law_at_selected hsource n hslo hshi z hz z₀ hz₀ hcell
  have hh := same_cell_graph_error (mul_pos hrho hS) hLip (hd.trans_le hslo) z₀ (f z₀) f hcell hosc
  have hzero : heightGraph (rho*S0) Lip z₀ (f z₀) f z₀=0 := by simp only [heightGraph,sub_self,zero_div,smul_zero,Prod.mk_zero_zero]
  simpa only [hzero,sub_zero,normalizedGraph] using hh
/-- The outer scheduled overshoot is charged once to the common S0. -/
theorem enclosing_schedule_fits_common_scaling {delta eta rho tau S0 : ℝ}
    (hrho : 0 ≤ rho) (hover : tau ≤ delta^(-eta)*rho) (hS : delta^(-eta) ≤ S0) :
    tau ≤ rho*S0 := by nlinarith only [hover,mul_le_mul_of_nonneg_right hS hrho]
/-- Actual graph-selected representatives inherit the unit box and diameter
 from an original enclosing scheduled cell, with no desired B envelope input. -/
theorem selected_scheduled_graph_envelope (Z : Finset ℝ) (j n : ℕ)
    {delta eta sigma rho S0 Lip : ℝ} (hd : 0 < delta) (hrho : 0 < rho) (hS : 0 < S0) (hLip : 0 < Lip)
    (hslo : delta ≤ scheduledScale delta eta n) (hshi : scheduledScale delta eta n ≤ 1)
    (hscale : scheduledScale delta eta n ≤ rho*S0)
    (hbin : (bin Z (coarseHeight sigma) j).Nonempty)
    (f : ℝ → ℝ × ℝ) (hsource : ScheduledSlopeOscillation delta eta Lip Z f)
    (z₀ : ℝ) (hz₀ : z₀ ∈ Z)
    (hcell : ∀ z ∈ Z, coarseHeight (scheduledScale delta eta n) z=coarseHeight (scheduledScale delta eta n) z₀) :
    let Q := (bin Z (coarseHeight sigma) j).image (coarseHeight sigma)
    let sample := representative (bin Z (coarseHeight sigma) j) hbin sigma
    let b := fun k => normalizedGraph rho S0 Lip z₀ (f z₀) f (sample k)
    (∀ k ∈ Q, ‖b k‖ ≤ 1) ∧ ∀ i ∈ Q, ∀ k ∈ Q, dist3 (b i) (b k) ≤ 2 := by
  dsimp only
  have hb : ∀ k ∈ (bin Z (coarseHeight sigma) j).image (coarseHeight sigma),
      ‖normalizedGraph rho S0 Lip z₀ (f z₀) f (representative (bin Z (coarseHeight sigma) j) hbin sigma k)‖ ≤ 1 := by
    intro k hk
    have hrep := representative_spec _ hbin sigma k hk
    have hz : representative (bin Z (coarseHeight sigma) j) hbin sigma k ∈ Z := (Finset.mem_filter.mp hrep.1).1
    exact (scheduled_graph_envelope Z n hd hrho hS hLip hslo hshi f hsource z₀ hz₀ _ hz (hcell _ hz)).trans
      ((div_le_one (mul_pos hrho hS)).mpr hscale)
  refine ⟨hb,?_⟩
  intro i hi k hk
  rw [dist3_eq_norm]
  exact (norm_sub_le _ _).trans (by linarith only [hb i hi,hb k hk])
end NativeScheduledHeightPopulation
