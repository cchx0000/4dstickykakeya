import Theorems.Thm_StickyKakeya4_native_window_XY_menus

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 14000000
noncomputable section
namespace NativeWindowXYSourceCaps
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeOriginalParentSelection
open NativeOriginalCellChartGeometry NativeCubicalIncidenceCounts NativeSquaredGrainQueries
open NativeReferenceXYGridLinear NativeReferenceXYGridPoints NativeReferenceXYGridMaps NativeReferenceXYGridMenus
open NativeWindowXYReferenceMaps NativeWindowXYMetric NativeWindowXYLabels
open NativeHorizontalGrainSlice NativeGrainQuotientInjection NativeGrainQuotientBins
open NativeTranslatedGrainHeightOverlap NativeTranslatedGrainHeightMetric NativeOffsetAngularGeometry
open NativeAnisotropicShortRowGeometry NativeReferenceXYGridSupport
open scoped Matrix.Norms.Elementwise

/-- Both capacities on the actual retained original incidence set. The
source supplies unit raw support; F is bounded and Lipschitz only on I,
so no continuity of its zero extension on the rest of E2 is assumed. -/
theorem actual_window_capacities {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level m : ℕ) (hm : 12 ≤ m) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hf : phaseDepth m ≤ level)
    (p : Parent) (I : Finset (Fin n × Index)) (hI : I⊆incidences original)
    (hp : ∀z∈I,parentLabel D a (2^m) z.1=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1) (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (hF : ∀z∈I,‖F (translatedHeight D a m z.2)‖ ≤ (1/4:ℝ))
    (hLip : ∀z∈I,∀w∈I,‖F (translatedHeight D a m z.2)-F (translatedHeight D a m w.2)‖ ≤
      L*|referenceHeight m (translatedHeight D a m z.2)-referenceHeight m (translatedHeight D a m w.2)|)
    (T R : ℕ) (hT : 0 < T) (hTR : T ≤ R) :
    let prefW := fun k => windowIndex (8*T) R (pref D a m p k)
    let pxyW := fun k => window (8*T) R (pxy D a m ell p P hP hell hell4 hd F k)
    (∀z : NativeReferenceXYGridMaps.XY ell,
      ((I.filter (fun x => pxyW x.2=z)).image (fun x => prefW x.2)).card ≤ (2*menuRadius L+1)^3) ∧
    (∀z : Index,
      ((I.filter (fun x => prefW x.2=z)).image (fun x => pxyW x.2)).card ≤ (2*menuRadius L+1)^3) := by
  intro prefW pxyW
  have hm6 : 6 ≤ m := by omega
  have hscale := NativeActualSquaredGrainSelection.thickness_le_squared_scale m level hm6 hdy hf
  have hnorm : ∀z∈I,‖rawPoint D a m p z.2‖ ≤ 1 := by
    intro z hz
    exact (rawPoint_norm h original horiginal ha m hm hscale p z.1 z.2 (hI hz) (hp z hz)).trans (by norm_num)
  constructor
  · intro z
    let U := I.filter (fun x => pxyW x.2=z)
    change (U.image (fun x => prefW x.2)).card ≤ _
    by_cases hn : U.Nonempty
    · obtain ⟨w,hw⟩ := hn
      have hsub : U.image (fun x => prefW x.2)⊆columnHalo (menuRadius L) 0 (prefW w.2) := by
        intro b hb
        obtain ⟨x,hx,rfl⟩ := mem_image.mp hb
        have hxI := (mem_filter.mp hx).1
        have hwI := (mem_filter.mp hw).1
        exact NativeWindowXYMenus.inverse_menu h m ell hm6 p w.1 (hp w hwI) T R hT hTR
          P hP hell hell4 hd F x.2 w.2 (hF x hxI) L hL (hnorm w hwI) (hLip x hxI w hwI)
          ((mem_filter.mp hx).2.trans (mem_filter.mp hw).2.symm)
      exact (card_le_card hsub).trans_eq (by rw [columnHalo_card]; norm_num)
    · rw [not_nonempty_iff_eq_empty] at hn
      simp only [hn,image_empty,card_empty,Nat.zero_le]
  · intro z
    let U := I.filter (fun x => prefW x.2=z)
    change (U.image (fun x => pxyW x.2)).card ≤ _
    by_cases hn : U.Nonempty
    · obtain ⟨w,hw⟩ := hn
      have hsub : U.image (fun x => pxyW x.2)⊆xyBox ell (pxyW w.2) (menuRadius L) := by
        intro b hb
        obtain ⟨x,hx,rfl⟩ := mem_image.mp hb
        have hxI := (mem_filter.mp hx).1
        have hwI := (mem_filter.mp hw).1
        exact NativeWindowXYMenus.forward_menu h m ell hm6 p w.1 (hp w hwI) T R hT hTR
          P hP hell hell4 hd F x.2 w.2 (hF x hxI) L hL (hnorm w hwI) (hLip x hxI w hwI)
          ((mem_filter.mp hx).2.trans (mem_filter.mp hw).2.symm)
      exact (card_le_card hsub).trans_eq (xyBox_card ell hell hell4 _ _)
    · rw [not_nonempty_iff_eq_empty] at hn
      simp only [hn,image_empty,card_empty,Nat.zero_le]

/-- Exact scheduled caps for all g≤f, keeping the same f-height window. -/
theorem scheduled_window_capacities {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level m : ℕ) (hm : 12 ≤ m) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hf : phaseDepth m ≤ level)
    (p : Parent) (I : Finset (Fin n × Index)) (hI : I⊆incidences original)
    (hp : ∀z∈I,parentLabel D a (2^m) z.1=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1) (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (hF : ∀z∈I,‖F (translatedHeight D a m z.2)‖ ≤ (1/4:ℝ))
    (hLip : ∀z∈I,∀w∈I,‖F (translatedHeight D a m z.2)-F (translatedHeight D a m w.2)‖ ≤
      L*|referenceHeight m (translatedHeight D a m z.2)-referenceHeight m (translatedHeight D a m w.2)|)
    (f g : ℕ) (hmf : m ≤ f) (hgf : g ≤ f) (hfb : f ≤ phaseDepth m) :
    let prefW := fun k => columnLabel D a (2^m) p (64/((2^g:ℕ):ℝ)) (64/((2^(f-m+3):ℕ):ℝ)) k
    let pxyW := fun k => window (8*2^(phaseDepth m-f)) (2^(phaseDepth m-g))
      (pxy D a m ell p P hP hell hell4 hd F k)
    (∀z : NativeReferenceXYGridMaps.XY ell,
      ((I.filter (fun x => pxyW x.2=z)).image (fun x => prefW x.2)).card ≤ (2*menuRadius L+1)^3) ∧
    (∀z : Index,
      ((I.filter (fun x => prefW x.2=z)).image (fun x => pxyW x.2)).card ≤ (2*menuRadius L+1)^3) := by
  have hTR : (2^(phaseDepth m-f):ℕ) ≤ 2^(phaseDepth m-g) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have hh := actual_window_capacities h original horiginal ha level m hm hdy hf p I hI hp P hP ell
    hell hell4 hd F L hL hF hLip (2^(phaseDepth m-f)) (2^(phaseDepth m-g)) (by positivity) hTR
  simpa only [scheduled_reference_readback D a m f g (by omega) hmf hgf hfb p] using hh

/-- The two finest-window capacities, complementary to the two coarser
scheduled capacities. All four are on the same original I. -/
theorem finest_window_capacities {n : ℕ} {D : FiniteScaleSource n} {eta a : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (original : Fin n → Finset Index)
    (horiginal : ∀i,D.shading i=wzCellShading (mesh D) original i)
    (ha : ∀i,wzGraphTime (D.line i) a-mark (D.line i)∈Set.Icc (-(1/2:ℝ)) (1/2:ℝ))
    (level m : ℕ) (hm : 12 ≤ m) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hf : phaseDepth m ≤ level)
    (p : Parent) (I : Finset (Fin n × Index)) (hI : I⊆incidences original)
    (hp : ∀z∈I,parentLabel D a (2^m) z.1=p)
    (P : Submodule ℝ E4) (hP : P≤heightKernel) (ell : ℕ) (hell : 1 ≤ ell) (hell4 : ell ≤ 4)
    (hd : Module.finrank ℝ P=ell-1) (F : ℤ → Matrix (Fin (4-ell)) (Fin (ell-1)) ℝ)
    (L : ℝ) (hL : 0 ≤ L)
    (hF : ∀z∈I,‖F (translatedHeight D a m z.2)‖ ≤ (1/4:ℝ))
    (hLip : ∀z∈I,∀w∈I,‖F (translatedHeight D a m z.2)-F (translatedHeight D a m w.2)‖ ≤
      L*|referenceHeight m (translatedHeight D a m z.2)-referenceHeight m (translatedHeight D a m w.2)|)
    (f : ℕ) (hmf : m ≤ f) (hfb : f ≤ phaseDepth m) :
    let prefW := fun k => columnLabel D a (2^m) p (64/((2^f:ℕ):ℝ)) (64/((2^(f-m+3):ℕ):ℝ)) k
    let pxyW := fun k => window (8*2^(phaseDepth m-f)) (2^(phaseDepth m-f))
      (pxy D a m ell p P hP hell hell4 hd F k)
    (∀z : NativeReferenceXYGridMaps.XY ell,
      ((I.filter (fun x => pxyW x.2=z)).image (fun x => prefW x.2)).card ≤ (2*menuRadius L+1)^3) ∧
    (∀z : Index,
      ((I.filter (fun x => prefW x.2=z)).image (fun x => pxyW x.2)).card ≤ (2*menuRadius L+1)^3) :=
  scheduled_window_capacities h original horiginal ha level m hm hdy hf p I hI hp P hP ell
    hell hell4 hd F L hL hF hLip f f hmf le_rfl hfb

end NativeWindowXYSourceCaps
