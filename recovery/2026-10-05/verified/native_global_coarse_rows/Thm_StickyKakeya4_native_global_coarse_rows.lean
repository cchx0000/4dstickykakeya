import Theorems.Thm_StickyKakeya4_native_original_parent_density_core
import Theorems.Thm_StickyKakeya4_native_coarse_representative_geometry
import Theorems.Thm_StickyKakeya4_native_fixed_size_scale_menu

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3200000

noncomputable section
namespace NativeGlobalCoarseRows
open Classical Finset MeasureTheory StickyKakeya4 NativeCommonCubicalMesh
open NativeCubicalIncidenceCounts NativeOriginalParentSelection
open NativeOriginalParentDensityCore NativeLocalPairFibers
open NativeCoarseShadingCapacity NativeCoarseRepresentativeGeometry
open scoped ENNReal BigOperators

/-- A rich local pair fiber lies on one literal original tube. Its cells
can therefore fill any projected row with capacity at most 175616 B,
independently of the target parent scale and representative choice. -/
theorem pair_fiber_le_projected_rows {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (E : Finset (Fin n × Index)) (hE : E ⊆ incidences original)
    (K N B : ℕ) (hB : 0 < B) (rep : Parent → Fin n) (e : Fin n × Index) :
    (pairFiber D a K E (localPair D a K e)).card ≤
      (175616*B)*(rows D a N B rep E (parentLabel D a N e.1)).card := by
  let S := pairFiber D a K E (localPair D a K e)
  let p := parentLabel D a N e.1
  let f : Fin n × Index → Index := fun z => projectedLabel D a B (rep p) z.2
  have hfst : ∀ z ∈ S, z.1 = e.1 := by
    intro z hz
    have hh := congrArg Prod.fst (mem_filter.mp hz).2
    exact hh
  have hm : ∀ z ∈ S, f z ∈ rows D a N B rep E p := by
    intro z hz
    have hp : parentLabel D a N z.1 = p := congrArg (parentLabel D a N) (hfst z hz)
    refine mem_image.mpr ⟨(p,f z),mem_filter.mpr ⟨?_,rfl⟩,rfl⟩
    refine mem_image.mpr ⟨z,(mem_filter.mp hz).1,?_⟩
    simp only [label,hp,f]
  have hc : ∀ q ∈ rows D a N B rep E p, (S.filter (fun z => f z = q)).card ≤ 175616*B := by
    intro q _hq
    let T := S.filter (fun z => f z = q)
    have hinj : Set.InjOn Prod.snd (T : Set (Fin n × Index)) := by
      intro z hz y hy hzy
      exact Prod.ext ((hfst z (mem_filter.mp hz).1).trans
        (hfst y (mem_filter.mp hy).1).symm) hzy
    have hsub : T.image Prod.snd ⊆
        (original e.1).filter (fun k => projectedLabel D a B (rep p) k = q) := by
      intro k hk
      obtain ⟨z,hz,rfl⟩ := mem_image.mp hk
      obtain ⟨hzS,hzq⟩ := mem_filter.mp hz
      refine mem_filter.mpr ⟨?_,hzq⟩
      have hzold := (mem_incidences original z.1 z.2).mp (hE (mem_filter.mp hzS).1)
      simpa only [hfst z hzS] using hzold
    calc
      T.card = (T.image Prod.snd).card := (card_image_iff.mpr hinj).symm
      _ ≤ ((original e.1).filter (fun k => projectedLabel D a B (rep p) k = q)).card :=
        card_le_card hsub
      _ ≤ 175616*B := projected_fiber_card_le h original horiginal ha B hB e.1 (rep p) q
  exact card_le_mul_card_image_of_maps_to hm (175616*B) hc

/-- Explicit same-core count bound. The local pair relation already present
in the core supplies the required individual original-tube richness. -/
theorem core_projected_row_lower {n : ℕ} {D : FiniteScaleSource n} {eta zeta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (d g L : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (scales : Fin g → ℕ) (E : Finset (Fin n × Index))
    (hcore : IsCore D original R a eta zeta d g L Rel scales E)
    (j : Fin g) (N B : ℕ) (hB : 0 < B) (rep : Parent → Fin n)
    (p : Parent) (hp : (parentEdges D a N E p).Nonempty) :
    D.thickness^eta * scales j /
      (16384*(factor d g L:ℝ)*(coreRadix original R L:ℝ)^2) ≤
        175616*(B:ℝ)*(rows D a N B rep E p).card := by
  obtain ⟨e,he⟩ := hp
  obtain ⟨heE,hep⟩ := mem_filter.mp he
  have hpair := hcore.2.2.2.2.2.2 j e heE
  have hcap := pair_fiber_le_projected_rows h original horiginal ha E
    (hcore.1.trans (filter_subset _ _)) (scales j) N B hB rep e
  rw [hep] at hcap
  exact hpair.trans (by exact_mod_cast hcap)

/-- The existing source transfer budget absorbs all retention and radix
costs. No extra relation or further edge selection is introduced. -/
theorem core_projected_row_lower_absorbed {n : ℕ} {D : FiniteScaleSource n}
    {eta zeta a gamma : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (R : Finset (Fin n)) (d g L : ℕ)
    (Rel : Fin d → (Fin n × Index) → (Fin n × Index) → Prop)
    (scales : Fin g → ℕ) (E : Finset (Fin n × Index))
    (hcore : IsCore D original R a eta zeta d g L Rel scales E)
    (hcost : (125*175616*16384:ℝ)*(factor d g L:ℝ)*(coreRadix original R L:ℝ)^2*
      D.thickness^(-eta) ≤ D.thickness^(-gamma))
    (j : Fin g) (N B : ℕ) (hB : 0 < B) (rep : Parent → Fin n)
    (p : Parent) (hp : (parentEdges D a N E p).Nonempty) :
    125*D.thickness^gamma*(scales j:ℝ)/(B:ℝ) ≤ (rows D a N B rep E p).card := by
  have hd := h.1.2.1
  have hg : 0 < g := Nat.zero_lt_of_lt j.isLt
  have hF : 0 < (factor d g L:ℝ) := by
    have hh : 0 < d+g+g := by omega
    dsimp [factor,NativeLocalPairUniformCore.retentionCost]
    positivity
  have hQ : 0 < (coreRadix original R L:ℝ) := by
    dsimp [coreRadix,NativeSourceSizeBounds.radix]
    positivity
  have hden : 0 < 16384*(factor d g L:ℝ)*(coreRadix original R L:ℝ)^2 := by positivity
  have hc := mul_le_mul_of_nonneg_right hcost
    (show 0 ≤ D.thickness^gamma*D.thickness^eta by positivity)
  have he1 : D.thickness^(-eta)*(D.thickness^gamma*D.thickness^eta) = D.thickness^gamma := by
    rw [←Real.rpow_add hd,←Real.rpow_add hd]
    congr 1
    ring
  have he2 : D.thickness^(-gamma)*(D.thickness^gamma*D.thickness^eta) = D.thickness^eta := by
    rw [←Real.rpow_add hd,←Real.rpow_add hd]
    congr 1
    ring
  rw [mul_assoc _ (D.thickness^(-eta)),he1,he2] at hc
  have hbase : 125*175616*D.thickness^gamma ≤
      D.thickness^eta/(16384*(factor d g L:ℝ)*(coreRadix original R L:ℝ)^2) := by
    apply (le_div_iff₀ hden).mpr
    convert hc using 1
    ring
  have hraw := core_projected_row_lower h original horiginal ha R d g L Rel scales E hcore
    j N B hB rep p hp
  have hh := (mul_le_mul_of_nonneg_right hbase (Nat.cast_nonneg (scales j))).trans
    (by simpa only [div_mul_eq_mul_div,mul_comm (scales j:ℝ)] using hraw)
  apply (div_le_iff₀ (show (0:ℝ) < B by exact_mod_cast hB)).mpr
  nlinarith only [hh]

/-- Every projected row is an actual front-meeting cube union inside the
marked representative tube, for any independent spatial mesh B. -/
theorem projected_row_volume_upper {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N B : ℕ) (hB : 0 < B) (hscale : (B:ℝ)*D.thickness/64 ≤ 1)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (hE : E ⊆ incidences original) (p : Parent) :
    (volume (wzCellShading ((B:ℝ)*D.thickness/128)
      (fun _ : Fin 1 => rows D a N B rep E p) 0)).toReal ≤
        NativeOriginalPrunedMass.volumeConstant*((B:ℝ)*D.thickness/64)^3 := by
  have hd := h.1.2.1
  have hs := projected_shading_subset_tube h original horiginal ha N B hB rep E
    (fun e he => (mem_incidences original e.1 e.2).mp (hE he)) p
  have ht := volume_markedUnitTube_upper_bound (zero_parent_valid_slab h a (rep p)).1
    (by positivity : 0 < (B:ℝ)*D.thickness/64) hscale
  have hh := ENNReal.toReal_mono (by finiteness) ((measure_mono hs).trans ht)
  simp only [ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_ofNat,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (B:ℝ)*D.thickness/64),
    ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi^2/2)] at hh
  exact hh.trans_eq (by dsimp [NativeOriginalPrunedMass.volumeConstant]; ring)

/-- Global occupied cube count has the expected reciprocal spatial scale.
This does not assert equal occupancy of the separate occupied cubes. -/
theorem projected_row_card_upper {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀ i, D.shading i = wzCellShading (mesh D) original i)
    (ha : ∀ i, wzGraphTime (D.line i) a - mark (D.line i) ∈
      Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (N B : ℕ) (hB : 0 < B) (hscale : (B:ℝ)*D.thickness/64 ≤ 1)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index))
    (hE : E ⊆ incidences original) (p : Parent) :
    ((B:ℝ)*D.thickness/64)*(rows D a N B rep E p).card ≤
      16*NativeOriginalPrunedMass.volumeConstant := by
  have hd := h.1.2.1
  have hb : 0 < (B:ℝ)*D.thickness/64 := by positivity
  have hh := projected_row_volume_upper h original horiginal ha N B hB hscale rep E hE p
  rw [volume_wzCellShading (by positivity)] at hh
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ (B:ℝ)*D.thickness/128)] at hh
  apply (mul_le_mul_iff_right₀ (pow_pos hb 3)).mp
  calc
    _ = 16*((rows D a N B rep E p).card*((B:ℝ)*D.thickness/128)^4) := by ring
    _ ≤ 16*(NativeOriginalPrunedMass.volumeConstant*((B:ℝ)*D.thickness/64)^3) :=
      mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = _ := by ring

end NativeGlobalCoarseRows
