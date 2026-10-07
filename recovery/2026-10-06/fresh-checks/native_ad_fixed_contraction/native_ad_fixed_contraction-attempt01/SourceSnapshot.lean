import Theorems.Thm_StickyKakeya4_native_finite_slice_union_ad

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

noncomputable section
namespace NativeADFixedContraction
open Classical Finset FiniteVoronoiPopulation FiniteVoronoiRealADCoarsening

/-- The fixed final contraction uses source AD only through radius one.
Larger rescaled tests use its radius-one lower and its separate global
upper. This includes the final interval [1/C,1]. -/
theorem contract_AD {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (P : Finset X) (f : X → Y) (hf : Function.Injective f)
    {mu C K G s : ℝ} (hmu : 0 < mu) (hmu1 : mu ≤ 1) (hC : 1 ≤ C)
    (hK : 0 < K) (hs : 0 ≤ s)
    (hdist : ∀x y,dist (f x) (f y)=dist x y/C)
    (H : ADBounds P mu K s) (Hglobal : (P.card:ℝ) ≤ G*mu^(-s)) :
    ADBounds (P.image f) (mu/C) (C^s*max K G) s := by
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hCpow : 1 ≤ C^s := Real.one_le_rpow hC hs
  have hmax : 0 < max K G := hK.trans_le (le_max_left _ _)
  have hcost : 0 < C^s*max K G := mul_pos (Real.rpow_pos_of_pos hCp _) hmax
  have hKcost : K ≤ C^s*max K G :=
    (le_max_left _ _).trans (le_mul_of_one_le_left hmax.le hCpow)
  intro b hb r hr hr1
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hb
  have hrp : 0 < r := (div_pos hmu hCp).trans_le hr
  have htest : mu ≤ C*r := by
    have hh := (div_le_iff₀ hCp).mp hr
    simpa only [mul_comm] using hh
  have hratio : r/(mu/C)=(C*r)/mu := by field_simp
  have heq : carrierBall (P.image f) (f a) r=(carrierBall P a (C*r)).image f := by
    ext y
    simp only [mem_carrierBall,mem_image]
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,hd⟩
      rw [hdist] at hd
      exact ⟨x,⟨hx,by simpa only [mul_comm] using (div_le_iff₀ hCp).mp hd⟩,rfl⟩
    · rintro ⟨x,⟨hx,hd⟩,rfl⟩
      exact ⟨⟨x,hx,rfl⟩,by rw [hdist]; exact (div_le_iff₀ hCp).mpr (by simpa only [mul_comm] using hd)⟩
  rw [heq,card_image_of_injective _ hf,hratio]
  by_cases hsmall : C*r ≤ 1
  · have hh := H a ha (C*r) htest hsmall
    exact ⟨(div_le_div_of_nonneg_left (by positivity) hK hKcost).trans hh.1,
      hh.2.trans (mul_le_mul_of_nonneg_right hKcost (by positivity))⟩
  · have hunit := (H a ha 1 hmu1 le_rfl).1
    have hball : carrierBall P a 1 ⊆ carrierBall P a (C*r) := by
      intro x hx
      obtain ⟨hxP,hxd⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨hxP,hxd.trans (by linarith only [hsmall])⟩
    have hcount := (Nat.cast_le.mpr (card_le_card hball) :
      ((carrierBall P a 1).card:ℝ) ≤ (carrierBall P a (C*r)).card)
    have hpow : ((C*r)/mu)^s ≤ C^s*(1/mu)^s := by
      have hh := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (C*r)/mu)
        (div_le_div_of_nonneg_right (mul_le_of_le_one_right hCp.le hr1) hmu.le) hs
      rw [show C/mu=C*(1/mu) by ring,Real.mul_rpow hCp.le (by positivity)] at hh
      exact hh
    have hunitId : (1/mu)^s=mu^(-s) := by
      rw [Real.div_rpow (by norm_num) hmu.le,Real.one_rpow,Real.rpow_neg hmu.le,one_div]
    constructor
    · apply (div_le_iff₀ hcost).mpr
      have hl := (div_le_iff₀ hK).mp (hunit.trans hcount)
      have hcn : (0:ℝ) ≤ (carrierBall P a (C*r)).card := Nat.cast_nonneg _
      calc
        _ ≤ C^s*(1/mu)^s := hpow
        _ ≤ C^s*(((carrierBall P a (C*r)).card:ℝ)*K) :=
          mul_le_mul_of_nonneg_left hl (by positivity)
        _ ≤ C^s*(((carrierBall P a (C*r)).card:ℝ)*max K G) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_max_left _ _) hcn) (by positivity)
        _ = _ := by ring
    · have hsub : carrierBall P a (C*r) ⊆ P := filter_subset _ _
      have hc := (Nat.cast_le.mpr (card_le_card hsub) :
        ((carrierBall P a (C*r)).card:ℝ) ≤ P.card)
      have hp := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ 1/mu)
        (div_le_div_of_nonneg_right (by linarith only [hsmall] : (1:ℝ) ≤ C*r) hmu.le) hs
      rw [hunitId] at hp
      calc
        _ ≤ G*mu^(-s) := hc.trans Hglobal
        _ ≤ max K G*mu^(-s) := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
        _ ≤ max K G*((C*r)/mu)^s := mul_le_mul_of_nonneg_left hp hmax.le
        _ ≤ (C^s*max K G)*((C*r)/mu)^s :=
          mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hmax.le hCpow) (by positivity)

/-- Once the final mesh is at least 1/C, an actual global cardinal bound
and each tested center itself control every remaining radius. No source AD
statement is evaluated beyond its original upper endpoint. -/
theorem coarse_mesh_AD {X : Type*} [PseudoMetricSpace X] (P : Finset X)
    {rho C G s : ℝ} (hC : 1 ≤ C) (hrho : 1/C ≤ rho) (hs : 0 ≤ s)
    (Hglobal : (P.card:ℝ) ≤ G) :
    ADBounds P rho (C^s*max 1 G) s := by
  have hCp : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hrhop : 0 < rho := (one_div_pos.mpr hCp).trans_le hrho
  have hmax : 1 ≤ max 1 G := le_max_left _ _
  have hpow1 : 1 ≤ C^s := Real.one_le_rpow hC hs
  have hcost : 0 < C^s*max 1 G := by positivity
  intro a ha r hr hr1
  have hrp : 0 < r := hrhop.trans_le hr
  have hone : (1:ℝ) ≤ (carrierBall P a r).card := by
    exact Nat.one_le_cast.mpr (card_pos.mpr ⟨a,mem_filter.mpr ⟨ha,by simp [hrp.le]⟩⟩)
  have hratio : r/rho ≤ C := by
    apply (div_le_iff₀ hrhop).mpr
    have hh := (div_le_iff₀ hCp).mp hrho
    nlinarith only [hh,hr1]
  have hpower := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ r/rho) hratio hs
  have hratio1 : 1 ≤ (r/rho)^s :=
    Real.one_le_rpow ((le_div_iff₀ hrhop).mpr (by simpa only [one_mul] using hr)) hs
  constructor
  · exact ((div_le_one hcost).mpr
      (hpower.trans (le_mul_of_one_le_right (by positivity) hmax))).trans hone
  · have hsub : carrierBall P a r ⊆ P := filter_subset _ _
    have hc := (Nat.cast_le.mpr (card_le_card hsub) : ((carrierBall P a r).card:ℝ) ≤ P.card)
    calc
      _ ≤ G := hc.trans Hglobal
      _ ≤ max 1 G := le_max_right _ _
      _ ≤ C^s*max 1 G := le_mul_of_one_le_left (by positivity) hpow1
      _ ≤ (C^s*max 1 G)*(r/rho)^s := le_mul_of_one_le_right (by positivity) hratio1

end NativeADFixedContraction
