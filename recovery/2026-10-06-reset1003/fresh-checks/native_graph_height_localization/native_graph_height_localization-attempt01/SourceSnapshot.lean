import Theorems.Thm_StickyKakeya4_native_graph_point_cuts
import Theorems.Thm_StickyKakeya4_native_dense_original_parent
import Theorems.Thm_StickyKakeya4_native_quantized_line_packets
import Theorems.Thm_StickyKakeya4_native_tangent_grid_coarsening

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 2600000
noncomputable section
namespace NativeGraphHeightLocalization
open Classical Finset OriginalWWitnessCounts OriginalWCoarseEscapeMenus OriginalScalarCollisionMass
open NativeGraphPhysicalLocalization

variable {P T H B : Type*} [DecidableEq P] [DecidableEq T]
  [DecidableEq H] [DecidableEq B]

/-- A height-bin restriction is determined by the literal height/tube
vertex. Its vertex sets, unlike physical-cell vertex sets, form a partition. -/
lemma cut_vertices (I : Finset (P × T)) (height : P → H) (bin : H → B) (b : B) :
    vertices (cut I (fun p => bin (height p)) b) height =
      (vertices I height).filter (fun v => bin v.1=b) := by
  rw [vertices_eq_original_incidence_image,vertices_eq_original_incidence_image]
  ext v
  simp only [cut,mem_image,mem_filter]
  constructor
  · rintro ⟨e,⟨he,heb⟩,hev⟩
    exact ⟨⟨e,he,hev⟩,by simpa only [←hev] using heb⟩
  · rintro ⟨⟨e,he,hev⟩,hvb⟩
    exact ⟨e,⟨he,by simpa only [←hev] using hvb⟩,hev⟩

/-- Select a real height window by its full height-times-active-tube
denominator. The original lambda is preserved, including after earlier
whole-point degree cuts. No unweighted height-window choice is used. -/
theorem exists_height_bin (I : Finset (P × T)) (hI : I.Nonempty)
    (height : P → H) (bin : H → B) {lambda : ℝ} (hlambda : 0 ≤ lambda)
    (hmass : lambda*((I.image (fun e => height e.1)).card:ℝ)*
      (TwoTubePathCollisionCount.tubes I).card ≤ (vertices I height).card) :
    let Z := I.image (fun e => height e.1)
    ∃b∈Z.image bin,
      (cut I (fun p => bin (height p)) b).Nonempty ∧
      (∀p∈TwoTubePathCollisionCount.points (cut I (fun p => bin (height p)) b),
        tubesAt (cut I (fun p => bin (height p)) b) p=tubesAt I p) ∧
      lambda*((Z.filter (fun z => bin z=b)).card:ℝ)*
        (TwoTubePathCollisionCount.tubes (cut I (fun p => bin (height p)) b)).card ≤
        (vertices (cut I (fun p => bin (height p)) b) height).card := by
  intro Z
  let bins := Z.image bin
  have hbins : bins=I.image (fun e => bin (height e.1)) := by
    dsimp only [bins,Z]
    rw [image_image]
    rfl
  have hVertexBins : (vertices I height).image (fun v => bin v.1)=bins := by
    rw [vertices_eq_original_incidence_image,image_image]
    exact hbins.symm
  have hVsum : (∑b∈bins, ((vertices (cut I (fun p => bin (height p)) b) height).card:ℝ)) =
      ((vertices I height).card:ℝ) := by
    simp_rw [cut_vertices]
    have hh := (card_eq_sum_card_image (fun v : H × T => bin v.1) (vertices I height)).symm
    rw [hVertexBins] at hh
    exact_mod_cast hh
  have hZsum : (∑b∈bins, ((Z.filter (fun z => bin z=b)).card:ℝ))=(Z.card:ℝ) := by
    exact_mod_cast (card_eq_sum_card_image bin Z).symm
  have hTube (b : B) :
      ((TwoTubePathCollisionCount.tubes (cut I (fun p => bin (height p)) b)).card:ℝ) ≤
        (TwoTubePathCollisionCount.tubes I).card := by
    exact_mod_cast card_le_card (image_subset_image (cut_subset I (fun p => bin (height p)) b))
  have hsum : (∑b∈bins, lambda*((Z.filter (fun z => bin z=b)).card:ℝ)*
      (TwoTubePathCollisionCount.tubes (cut I (fun p => bin (height p)) b)).card) ≤
      ∑b∈bins, ((vertices (cut I (fun p => bin (height p)) b) height).card:ℝ) := by
    calc
      _ ≤ ∑b∈bins, lambda*((Z.filter (fun z => bin z=b)).card:ℝ)*
          (TwoTubePathCollisionCount.tubes I).card := sum_le_sum (fun b _hb =>
            mul_le_mul_of_nonneg_left (hTube b) (by positivity))
      _ = lambda*(Z.card:ℝ)*(TwoTubePathCollisionCount.tubes I).card := by
        rw [←sum_mul,←mul_sum,hZsum]
      _ ≤ (vertices I height).card := hmass
      _ = _ := hVsum.symm
  obtain ⟨b,hb,hden⟩ := exists_le_of_sum_le ((hI.image (fun e => height e.1)).image bin) hsum
  have hb' : b∈I.image (fun e => bin (height e.1)) := by rw [←hbins]; exact hb
  exact ⟨b,hb,cut_nonempty I _ b hb',
    fun p hp => cut_full_tube_fiber I _ b p (cut_point_cell I _ b p hp),hden⟩

/-- The source-facing choice preserves both height density and a quantitative
share of the global height/tube vertices. The resulting height lower bound
is explicit, so a tiny but very dense time window cannot silently replace
the actual populated source window required later. -/
theorem exists_massive_height_bin (I : Finset (P × T)) (hI : I.Nonempty)
    (height : P → H) (bin : H → B) {lambda : ℝ} (_hlambda : 0 ≤ lambda)
    (hmass : lambda*((I.image (fun e => height e.1)).card:ℝ)*
      (TwoTubePathCollisionCount.tubes I).card ≤ (vertices I height).card) :
    let Z := I.image (fun e => height e.1)
    let bins := Z.image bin
    ∃b∈bins,
      let J := cut I (fun p => bin (height p)) b
      let Zb := Z.filter (fun z => bin z=b)
      J.Nonempty ∧ J⊆I ∧
      (∀p∈TwoTubePathCollisionCount.points J, tubesAt J p=tubesAt I p) ∧
      ((vertices I height).card:ℝ) ≤ 2*(bins.card:ℝ)*(vertices J height).card ∧
      lambda*(Zb.card:ℝ)*(TwoTubePathCollisionCount.tubes J).card ≤ 2*(vertices J height).card ∧
      lambda*(Z.card:ℝ) ≤ 2*(bins.card:ℝ)*(Zb.card:ℝ) := by
  intro Z bins
  let J := fun b => cut I (fun p => bin (height p)) b
  let Zb := fun b => Z.filter (fun z => bin z=b)
  let mass := fun b => ((vertices (J b) height).card:ℝ)
  let weight := fun b => ((Zb b).card:ℝ)*(TwoTubePathCollisionCount.tubes (J b)).card
  have hbins : bins=I.image (fun e => bin (height e.1)) := by
    dsimp only [bins,Z]
    rw [image_image]
    rfl
  have hVertexBins : (vertices I height).image (fun v => bin v.1)=bins := by
    rw [vertices_eq_original_incidence_image,image_image]
    exact hbins.symm
  have hVsum : (∑b∈bins, mass b)=((vertices I height).card:ℝ) := by
    dsimp only [mass,J]
    simp_rw [cut_vertices]
    have hh := (card_eq_sum_card_image (fun v : H × T => bin v.1) (vertices I height)).symm
    rw [hVertexBins] at hh
    exact_mod_cast hh
  have hZsum : (∑b∈bins, ((Zb b).card:ℝ))=(Z.card:ℝ) := by
    exact_mod_cast (card_eq_sum_card_image bin Z).symm
  have hTube (b : B) : ((TwoTubePathCollisionCount.tubes (J b)).card:ℝ) ≤
      (TwoTubePathCollisionCount.tubes I).card := by
    exact_mod_cast card_le_card (image_subset_image (cut_subset I (fun p => bin (height p)) b))
  have hWeight : (∑b∈bins, weight b) ≤ (Z.card:ℝ)*(TwoTubePathCollisionCount.tubes I).card := by
    calc
      _ ≤ ∑b∈bins, ((Zb b).card:ℝ)*(TwoTubePathCollisionCount.tubes I).card :=
        sum_le_sum (fun b _hb => mul_le_mul_of_nonneg_left (hTube b) (Nat.cast_nonneg _))
      _ = _ := by rw [←sum_mul,hZsum]
  have hVpos : (0:ℝ)<(vertices I height).card := by
    rw [vertices_eq_original_incidence_image]
    exact Nat.cast_pos.mpr (hI.image _).card_pos
  have hMpos : (0:ℝ)<∑b∈bins, mass b := by rw [hVsum]; exact hVpos
  have hWpos : (0:ℝ)<∑b∈bins, weight b := by
    apply sum_pos'
    · intro b _hb
      dsimp [weight]
      positivity
    · obtain ⟨e,he⟩ := hI
      let b := bin (height e.1)
      have hb : b∈bins := by rw [hbins]; exact mem_image_of_mem _ he
      have hJ : (J b).Nonempty := ⟨e,mem_filter.mpr ⟨he,rfl⟩⟩
      have hZb : (Zb b).Nonempty :=
        ⟨height e.1,mem_filter.mpr ⟨mem_image_of_mem _ he,rfl⟩⟩
      exact ⟨b,hb,mul_pos (Nat.cast_pos.mpr hZb.card_pos)
        (Nat.cast_pos.mpr (hJ.image Prod.snd).card_pos)⟩
  obtain ⟨b,hb,_hmb,hRet,hDensity⟩ := NativeDenseOriginalParent.exists_mass_and_density bins mass weight
    (fun _ _ => Nat.cast_nonneg _) (fun b _ => by dsimp [weight]; positivity) hMpos hWpos
  rw [hVsum] at hRet hDensity
  have hTpos : (0:ℝ)<(TwoTubePathCollisionCount.tubes I).card :=
    Nat.cast_pos.mpr (hI.image Prod.snd).card_pos
  have hZpos : (0:ℝ)<Z.card := Nat.cast_pos.mpr (hI.image _).card_pos
  have hLocalDensity : lambda*weight b ≤ 2*mass b := by
    apply (mul_le_mul_iff_left₀ (mul_pos hZpos hTpos)).mp
    calc
      _ = (lambda*(Z.card:ℝ)*(TwoTubePathCollisionCount.tubes I).card)*weight b := by ring
      _ ≤ ((vertices I height).card:ℝ)*weight b :=
        mul_le_mul_of_nonneg_right hmass (by dsimp [weight]; positivity)
      _ ≤ 2*(∑b∈bins, weight b)*mass b := hDensity
      _ ≤ 2*((Z.card:ℝ)*(TwoTubePathCollisionCount.tubes I).card)*mass b :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWeight (by norm_num)) (Nat.cast_nonneg _)
      _ = _ := by ring
  have hVsub : vertices (J b) height ⊆ Zb b ×ˢ TwoTubePathCollisionCount.tubes I := by
    intro v hv
    rw [vertices_eq_original_incidence_image] at hv
    obtain ⟨e,he,rfl⟩ := mem_image.mp hv
    obtain ⟨heI,heb⟩ := mem_filter.mp he
    exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_image_of_mem _ heI,heb⟩,
      mem_image_of_mem Prod.snd heI⟩
  have hVbound : mass b ≤ ((Zb b).card:ℝ)*(TwoTubePathCollisionCount.tubes I).card := by
    have hh := card_le_card hVsub
    rw [card_product] at hh
    exact_mod_cast hh
  have hHeight : lambda*(Z.card:ℝ) ≤ 2*(bins.card:ℝ)*((Zb b).card:ℝ) := by
    apply (mul_le_mul_iff_left₀ hTpos).mp
    have hh := hmass.trans (hRet.trans
      (mul_le_mul_of_nonneg_left hVbound (by positivity)))
    nlinarith only [hh]
  have hb' : b∈I.image (fun e => bin (height e.1)) := by rw [←hbins]; exact hb
  refine ⟨b,hb,cut_nonempty I _ b hb',cut_subset I _ b,?_,hRet,?_,hHeight⟩
  · intro p hp
    exact cut_full_tube_fiber I _ b p (cut_point_cell I _ b p hp)
  · simpa only [weight,mul_assoc] using hLocalDensity

/-- Literal floor windows work for the configured midpoint/affine lattice
without moving the actual time coordinate or assuming a zero-origin grid. -/
lemma floor_window_diameter {rho : ℝ} (hrho : 0 < rho) (s t : ℝ)
    (he : ⌊s/rho⌋=⌊t/rho⌋) : |s-t| ≤ rho := by
  have h := NativeQuantizedLinePackets.abs_sub_le_of_floor_mem (x := s/rho) (y := t/rho) 0
    (by simp only [he,Nat.cast_zero,sub_zero,add_zero,mem_Icc,le_refl,and_self])
  rw [←sub_div,abs_div,abs_of_pos hrho] at h
  have hh := (div_le_iff₀ hrho).mp h
  simpa only [Nat.cast_zero,zero_add,one_mul] using hh

/-- The actual bounded time support turns the joint mass/density choice
into the scale-relative fine-height lower bound needed by the later B set.
Times and tubes remain unchanged; only whole height fibers are restricted. -/
theorem exists_massive_height_window (I : Finset (P × T)) (hI : I.Nonempty)
    (height : P → ℝ) {rho lambda : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hlambda : 0 ≤ lambda)
    (hbox : ∀z∈I.image (fun e => height e.1), |z| ≤ 1)
    (hmass : lambda*((I.image (fun e => height e.1)).card:ℝ)*
      (TwoTubePathCollisionCount.tubes I).card ≤ (vertices I height).card) :
    let Z := I.image (fun e => height e.1)
    let bins := Z.image (fun z => ⌊z/rho⌋)
    ∃b∈bins,
      let J := cut I (fun p => ⌊height p/rho⌋) b
      let Zb := Z.filter (fun z => ⌊z/rho⌋=b)
      J.Nonempty ∧ J⊆I ∧
      (∀p∈TwoTubePathCollisionCount.points J, tubesAt J p=tubesAt I p) ∧
      ((vertices I height).card:ℝ) ≤ 2*(bins.card:ℝ)*(vertices J height).card ∧
      lambda*(Zb.card:ℝ)*(TwoTubePathCollisionCount.tubes J).card ≤ 2*(vertices J height).card ∧
      rho*lambda*(Z.card:ℝ) ≤ 8*(Zb.card:ℝ) ∧
      ∀p∈TwoTubePathCollisionCount.points J, ∀q∈TwoTubePathCollisionCount.points J,
        |height p-height q| ≤ rho := by
  intro Z bins
  obtain ⟨b,hb,hJ,hJI,hFib,hRet,hDen,hHeight⟩ :=
    exists_massive_height_bin I hI height (fun z => ⌊z/rho⌋) hlambda hmass
  have hbinCard : (bins.card:ℝ) ≤ 4/rho := by
    have hc := NativeTangentGridCoarsening.scalar_interval_grid_card Z id (c := -1) hrho
      (by norm_num : (0:ℝ)≤2)
      (fun z hz => ⟨(abs_le.mp (hbox z hz)).1,
        by change z ≤ -1+2; linarith only [(abs_le.mp (hbox z hz)).2]⟩)
    have hInv : 1 ≤ 1/rho := (le_div_iff₀ hrho).mpr (by simpa using hrho1)
    apply hc.trans
    rw [show 2/rho=2*(1/rho) by ring,show 4/rho=4*(1/rho) by ring]
    linarith only [hInv]
  refine ⟨b,hb,hJ,hJI,hFib,hRet,hDen,?_,?_⟩
  · have hcard := (le_div_iff₀ hrho).mp hbinCard
    have h1 := mul_le_mul_of_nonneg_left hHeight hrho.le
    have h2 := mul_le_mul_of_nonneg_right hcard
      (Nat.cast_nonneg (Z.filter (fun z => ⌊z/rho⌋=b)).card :
        (0:ℝ) ≤ (Z.filter (fun z => ⌊z/rho⌋=b)).card)
    nlinarith only [h1,h2]
  · intro p hp q hq
    exact floor_window_diameter hrho (height p) (height q)
      ((cut_point_cell I _ b p hp).trans (cut_point_cell I _ b q hq).symm)

end NativeGraphHeightLocalization
