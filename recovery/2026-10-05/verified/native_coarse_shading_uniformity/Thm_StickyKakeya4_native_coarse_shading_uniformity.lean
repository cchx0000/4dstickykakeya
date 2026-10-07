import Theorems.Thm_StickyKakeya4_native_coarse_scale_interpolation
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000
noncomputable section
namespace NativeCoarseShadingUniformity
open Classical Finset StickyKakeya4 NativeOriginalParentSelection NativeCommonCubicalMesh
open NativeOriginalPaddedCells NativeCubicalIncidenceCounts NativeCoarseShadingCapacity NativeCoarseDirectionThinning
open NativeCoarseDyadicShading NativeCoarsePointMultiplicity NativeCoarseScaleInterpolation
open scoped BigOperators

/-- Exact grouping of original mass by its occupied fine-label bins. -/
lemma nested_fiber_card_sum {A X Y : Type*} [DecidableEq A] [DecidableEq X] [DecidableEq Y]
    (E : Finset A) (f : A → X) (g : X → Y) (y : Y) :
    (E.filter (fun z => g (f z)=y)).card =
      ∑x∈(E.image f).filter (fun x => g x=y),(E.filter (fun z => f z=x)).card := by
  have himage : (E.filter (fun z => g (f z)=y)).image f=(E.image f).filter (fun x => g x=y) := by
    rw [filter_image]
  rw [card_eq_sum_card_image f,himage]
  apply sum_congr rfl
  intro x hx
  congr 1
  ext z
  simp only [mem_filter]
  constructor
  · exact fun hz => ⟨hz.1.1,hz.2⟩
  · intro hz
    exact ⟨⟨hz.1,by rw [hz.2]; exact (mem_filter.mp hx).2⟩,hz.2⟩

/-- Two original-E fiber comparison relations imply uniform numbers of
occupied fine bins in every occupied coarse bin. No bins are filled in. -/
theorem nested_image_fiber_card_comparable {A X Y : Type*}
    [DecidableEq A] [DecidableEq X] [DecidableEq Y]
    (E : Finset A) (f : A → X) (g : X → Y) (K L : ℕ)
    (hf : ∀a∈E,∀b∈E,(E.filter (fun z => f z=f a)).card ≤
      K*(E.filter (fun z => f z=f b)).card)
    (hg : ∀a∈E,∀b∈E,(E.filter (fun z => g (f z)=g (f a))).card ≤
      L*(E.filter (fun z => g (f z)=g (f b))).card)
    (x y : Y) (hx : x∈(E.image f).image g) (hy : y∈(E.image f).image g) :
    ((E.image f).filter (fun z => g z=x)).card ≤
      K*L*((E.image f).filter (fun z => g z=y)).card := by
  obtain ⟨u,hu,hux⟩ := mem_image.mp hx
  obtain ⟨a,ha,rfl⟩ := mem_image.mp hu
  obtain ⟨v,hv,hvy⟩ := mem_image.mp hy
  obtain ⟨b,hb,rfl⟩ := mem_image.mp hv
  obtain ⟨d,hd,hmin⟩ := exists_min_image E (fun d => (E.filter (fun z => f z=f d)).card) ⟨a,ha⟩
  let w := (E.filter (fun z => f z=f d)).card
  have hw : 0 < w := card_pos.mpr ⟨d,mem_filter.mpr ⟨hd,rfl⟩⟩
  have hlo : w*((E.image f).filter (fun z => g z=x)).card ≤
      (E.filter (fun z => g (f z)=x)).card := by
    rw [nested_fiber_card_sum E f g x]
    calc
      _ = ∑_z∈(E.image f).filter (fun z => g z=x),w := by simp [Nat.mul_comm]
      _ ≤ _ := by
        apply sum_le_sum
        intro z hz
        obtain ⟨t,ht,rfl⟩ := mem_image.mp (mem_filter.mp hz).1
        exact hmin t ht
  have hhi : (E.filter (fun z => g (f z)=y)).card ≤
      K*w*((E.image f).filter (fun z => g z=y)).card := by
    rw [nested_fiber_card_sum E f g y]
    calc
      _ ≤ ∑_z∈(E.image f).filter (fun z => g z=y),K*w := by
        apply sum_le_sum
        intro z hz
        obtain ⟨t,ht,rfl⟩ := mem_image.mp (mem_filter.mp hz).1
        exact hf t ht d hd
      _ = _ := by simp [Nat.mul_comm]
  have hcoarse : (E.filter (fun z => g (f z)=x)).card ≤
      L*(E.filter (fun z => g (f z)=y)).card := by
    simpa only [hux,hvy] using hg a ha b hb
  apply (mul_le_mul_iff_right₀ hw).mp
  calc
    _ ≤ (E.filter (fun z => g (f z)=x)).card := hlo
    _ ≤ L*(E.filter (fun z => g (f z)=y)).card := hcoarse
    _ ≤ L*(K*w*((E.image f).filter (fun z => g z=y)).card) := Nat.mul_le_mul_left L hhi
    _ = _ := by ring

/-- Spatial dyadic ancestor of a genuine cell index. -/
def cellAncestor (m b : ℕ) (q : Index) : Index := fun j => q j/(2^(m-b):ℕ)

def pairAncestor (m b : ℕ) (v : Parent × Index) : Parent × Index :=
  (v.1,cellAncestor m b v.2)

/-- Spatial coarsening keeps the same representative of the ORIGINAL m-parent. -/
def fixedPair {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (level m b : ℕ)
    (rep : Parent → Fin n) (z : Fin n × Index) : Parent × Index :=
  (parentLabel D a (2^m) z.1,
    projectedLabel D a (block level b) (rep (parentLabel D a (2^m) z.1)) z.2)

lemma projectedLabel_ancestor {n : ℕ} {D : FiniteScaleSource n} (a : ℝ)
    (level m b : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hbm : b ≤ m) (hml : m ≤ level)
    (j : Fin n) (k : Index) :
    cellAncestor m b (projectedLabel D a (block level m) j k)=
      projectedLabel D a (block level b) j k := by
  ext v
  change ⌊frontPoint D a (0,0) j k v/((block level m:ℝ)*D.thickness/128)⌋/(2^(m-b):ℕ)=
    ⌊frontPoint D a (0,0) j k v/((block level b:ℝ)*D.thickness/128)⌋
  rw [block_mesh hdy hml,block_mesh hdy (hbm.trans hml)]
  have he : (frontPoint D a (0,0) j k v/(32/((2^m:ℕ):ℝ)))/((2^(m-b):ℕ):ℝ)=
      frontPoint D a (0,0) j k v/(32/((2^b:ℕ):ℝ)) := by
    rw [coarse_mesh_ratio b m hbm]
    field_simp
  rw [←Int.floor_div_natCast,he]

lemma fixedPair_ancestor {n : ℕ} {D : FiniteScaleSource n} (a : ℝ)
    (level m b : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hbm : b ≤ m) (hml : m ≤ level)
    (rep : Parent → Fin n) (z : Fin n × Index) :
    pairAncestor m b (fixedPair D a level m m rep z)=fixedPair D a level m b rep z := by
  exact Prod.ext rfl (projectedLabel_ancestor a level m b hdy hbm hml _ _)

lemma fixedPair_image_ancestor {n : ℕ} {D : FiniteScaleSource n} (a : ℝ)
    (level m b : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hbm : b ≤ m) (hml : m ≤ level)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) :
    (E.image (fixedPair D a level m m rep)).image (pairAncestor m b)=
      E.image (fixedPair D a level m b rep) := by
  rw [image_image]
  apply image_congr
  intro z _hz
  exact fixedPair_ancestor a level m b hdy hbm hml rep z

/-- Literal occupied b-cells of the actual m-parent row. -/
def rowCells {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (level m b : ℕ)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (p : Parent) : Finset Index :=
  ((E.image (fixedPair D a level m b rep)).filter (fun z => z.1=p)).image Prod.snd

lemma rowCells_at_source {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (level m : ℕ)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (p : Parent) :
    rowCells D a level m m rep E p=rows D a (2^m) (block level m) rep E p := rfl

lemma mem_rowCells {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (level m b : ℕ)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (p : Parent) (q : Index) :
    q∈rowCells D a level m b rep E p ↔ (p,q)∈E.image (fixedPair D a level m b rep) := by
  constructor
  · intro hq
    obtain ⟨v,hv,hq⟩ := mem_image.mp hq
    obtain ⟨hv,hp⟩ := mem_filter.mp hv
    simpa only [←hp,←hq] using hv
  · intro hq
    exact mem_image.mpr ⟨(p,q),mem_filter.mpr ⟨hq,rfl⟩,rfl⟩

lemma rowCells_card_eq {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (level m b : ℕ)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (p : Parent) :
    (rowCells D a level m b rep E p).card=
      ((E.image (fixedPair D a level m b rep)).filter (fun z => z.1=p)).card := by
  apply card_image_iff.mpr
  intro z hz w hw he
  exact Prod.ext ((mem_filter.mp hz).2.trans (mem_filter.mp hw).2.symm) he

/-- Exact occupied-cell readback at every nested b-depth, with unchanged m-representatives. -/
theorem rowCells_eq_ancestor_image {n : ℕ} {D : FiniteScaleSource n} (a : ℝ)
    (level m b : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hbm : b ≤ m) (hml : m ≤ level)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (p : Parent) :
    rowCells D a level m b rep E p=(rowCells D a level m m rep E p).image (cellAncestor m b) := by
  unfold rowCells
  rw [←fixedPair_image_ancestor a level m b hdy hbm hml rep E]
  simp only [filter_image,image_image,Function.comp_def,pairAncestor]

/-- Actual fine row cells inside one occupied dyadic ancestor cell. -/
def rowChildren {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (level m b : ℕ)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (p : Parent) (q : Index) : Finset Index :=
  (rowCells D a level m m rep E p).filter (fun k => cellAncestor m b k=q)

lemma rowChildren_card_eq {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (level m b : ℕ)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (p : Parent) (q : Index) :
    (rowChildren D a level m b rep E p q).card=
      ((E.image (fixedPair D a level m m rep)).filter (fun z => pairAncestor m b z=(p,q))).card := by
  let C := E.image (fixedPair D a level m m rep)
  have hi : Set.InjOn Prod.snd (↑(C.filter (fun z => pairAncestor m b z=(p,q))) : Set (Parent × Index)) := by
    intro z hz w hw he
    have hz' := congrArg Prod.fst (mem_filter.mp hz).2
    have hw' := congrArg Prod.fst (mem_filter.mp hw).2
    exact Prod.ext (hz'.trans hw'.symm) he
  have he : (C.filter (fun z => pairAncestor m b z=(p,q))).image Prod.snd=
      rowChildren D a level m b rep E p q := by
    ext k
    constructor
    · intro hk
      obtain ⟨v,hv,hk⟩ := mem_image.mp hk
      obtain ⟨hv,hvq⟩ := mem_filter.mp hv
      have hp : v.1=p := congrArg Prod.fst hvq
      have hq : cellAncestor m b v.2=q := congrArg Prod.snd hvq
      exact mem_filter.mpr ⟨mem_image.mpr ⟨v,mem_filter.mpr ⟨hv,hp⟩,hk⟩,by rwa [←hk]⟩
    · intro hk
      obtain ⟨hk,hkq⟩ := mem_filter.mp hk
      obtain ⟨v,hv,hvk⟩ := mem_image.mp hk
      obtain ⟨hv,hvp⟩ := mem_filter.mp hv
      exact mem_image.mpr ⟨v,mem_filter.mpr ⟨hv,Prod.ext hvp (by simpa only [pairAncestor,hvk] using hkq)⟩,hvk⟩
  rw [←he,card_image_of_injOn hi]

/-- The two old relation comparisons at depths m and b imply literal
child-cell counts comparable by rad^4 in EVERY occupied b-cell. -/
theorem rowChildren_comparable {n : ℕ} {D : FiniteScaleSource n} (a : ℝ)
    (level m b : ℕ) (hdy : D.thickness=(2:ℝ)⁻¹^level) (hbm : b ≤ m) (hml : m ≤ level)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (rad : ℕ)
    (hf : ∀x∈E,∀y∈E,
      (E.filter (fun z => fixedPair D a level m m rep z=fixedPair D a level m m rep x)).card ≤
        rad^2*(E.filter (fun z => fixedPair D a level m m rep z=fixedPair D a level m m rep y)).card)
    (hg : ∀x∈E,∀y∈E,
      (E.filter (fun z => fixedPair D a level m b rep z=fixedPair D a level m b rep x)).card ≤
        rad^2*(E.filter (fun z => fixedPair D a level m b rep z=fixedPair D a level m b rep y)).card)
    (p p' : Parent) (q q' : Index)
    (hq : q∈rowCells D a level m b rep E p) (hq' : q'∈rowCells D a level m b rep E p') :
    (rowChildren D a level m b rep E p q).card ≤
      rad^4*(rowChildren D a level m b rep E p' q').card := by
  have hg' : ∀x∈E,∀y∈E,
      (E.filter (fun z => pairAncestor m b (fixedPair D a level m m rep z)=
        pairAncestor m b (fixedPair D a level m m rep x))).card ≤
      rad^2*(E.filter (fun z => pairAncestor m b (fixedPair D a level m m rep z)=
        pairAncestor m b (fixedPair D a level m m rep y))).card := by
    simpa only [fixedPair_ancestor a level m b hdy hbm hml] using hg
  have hx : (p,q)∈(E.image (fixedPair D a level m m rep)).image (pairAncestor m b) := by
    rw [fixedPair_image_ancestor a level m b hdy hbm hml]
    exact (mem_rowCells D a level m b rep E p q).mp hq
  have hy : (p',q')∈(E.image (fixedPair D a level m m rep)).image (pairAncestor m b) := by
    rw [fixedPair_image_ancestor a level m b hdy hbm hml]
    exact (mem_rowCells D a level m b rep E p' q').mp hq'
  rw [rowChildren_card_eq,rowChildren_card_eq]
  simpa only [show rad^2*rad^2=rad^4 by ring] using
    nested_image_fiber_card_comparable E (fixedPair D a level m m rep) (pairAncestor m b)
      (rad^2) (rad^2) hf hg' (p,q) (p',q') hx hy

/-- Parent-E mass and b-pair-E mass comparisons also control the total
number of occupied b-cells in each original m-parent row. -/
theorem rowCells_comparable {n : ℕ} (D : FiniteScaleSource n) (a : ℝ) (level m b : ℕ)
    (rep : Parent → Fin n) (E : Finset (Fin n × Index)) (rad : ℕ)
    (hf : ∀x∈E,∀y∈E,
      (E.filter (fun z => fixedPair D a level m b rep z=fixedPair D a level m b rep x)).card ≤
        rad^2*(E.filter (fun z => fixedPair D a level m b rep z=fixedPair D a level m b rep y)).card)
    (hg : ∀x∈E,∀y∈E,
      (E.filter (fun z => parentLabel D a (2^m) z.1=parentLabel D a (2^m) x.1)).card ≤
        rad^2*(E.filter (fun z => parentLabel D a (2^m) z.1=parentLabel D a (2^m) y.1)).card)
    (p p' : Parent) (hp : p∈E.image (fun z => parentLabel D a (2^m) z.1))
    (hp' : p'∈E.image (fun z => parentLabel D a (2^m) z.1)) :
    (rowCells D a level m b rep E p).card ≤rad^4*(rowCells D a level m b rep E p').card := by
  have hs : (E.image (fixedPair D a level m b rep)).image Prod.fst=
      E.image (fun z => parentLabel D a (2^m) z.1) := by
    simp only [image_image,Function.comp_def,fixedPair]
  rw [rowCells_card_eq,rowCells_card_eq]
  simpa only [show rad^2*rad^2=rad^4 by ring] using
    nested_image_fiber_card_comparable E (fixedPair D a level m b rep) Prod.fst
      (rad^2) (rad^2) hf hg p p' (by rwa [hs]) (by rwa [hs])

/-- The fine rows just counted are literally the shadings of the actual
full coarse source on the same original R and E. -/
theorem full_source_shading_readback {n : ℕ} {D : FiniteScaleSource n} {eta : ℝ}
    (h : IsWangZakharovNativeFiniteInput D eta) (R : Finset (Fin n)) (a : ℝ)
    (level m : ℕ) (E : Finset (Fin n × Index))
    (i : Fin (R.image (parentLabel D a (2^m))).card) :
    (NativeFullCoarseShadow.fullSource h R a level m E).shading i =
      wzCellShading (32/((2^m:ℕ):ℝ))
        (fun j : Fin (R.image (parentLabel D a (2^m))).card =>
          rowCells D a level m m (representative h R a (2^m)) E
            (NativeCoarseCellSource.parentIndex (R.image (parentLabel D a (2^m))) j)) i := rfl

end NativeCoarseShadingUniformity
