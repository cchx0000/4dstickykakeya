import Theorems.Thm_StickyKakeya4_native_lipschitz_coarse_height_selection

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000
noncomputable section
namespace NativeLipschitzLocalHeightSelection
open Classical Finset NativeMatrixHeightWholePoint SeparatedAlignmentPatches
open NativeLipschitzCoarseHeightSelection

/-- Deterministic witness readback after an actual fine-bin choice. The
coarse residue gives separation of distinct occupied coarse centers. -/
theorem selected_field_bounds {A V : Type*} [NormedAddCommGroup V]
    (S T : Finset A) (hTS : T⊆S) (height : A → ℝ) (F : A → V)
    (L R origin B : ℝ) (hL : 0 ≤ L) (hR : 0 < R) (hB : 0 ≤ B)
    (q : ℕ) (hq : 0 < q) (hLq : L ≤ (q:ℝ))
    (hF : ∀x∈S,‖F x‖ ≤ B)
    (hLip : ∀x∈S,∀y∈S,dist (F x) (F y) ≤ L*|height x-height y|)
    (hfine : ∀x∈T,∀y∈T,coarse R origin (height x)=coarse R origin (height y) →
      fine R origin q (height x)=fine R origin q (height y))
    (hcolor : ∀x∈T,∀y∈T,coarse R origin (height x)%8=coarse R origin (height y)%8) :
    (∀c,‖selectedField T height F R origin c‖ ≤ B) ∧
      (∀U⊆T,∀x∈U,
        dist (selectedField T height F R origin (coarse R origin (height x))) (F x) ≤ R) ∧
      ∀U⊆T,∀x∈U,∀y∈U,
        dist (selectedField T height F R origin (coarse R origin (height x)))
          (selectedField T height F R origin (coarse R origin (height y))) ≤
        ((9/8:ℝ)*L)*dist (center R origin (coarse R origin (height x)))
          (center R origin (coarse R origin (height y))) := by
  have hqR : 0 < (q:ℝ) := by exact_mod_cast hq
  have hsmall : L*(R/(q:ℝ)) ≤ R := by
    have hh := mul_le_mul_of_nonneg_right hLq (div_nonneg hR.le hqR.le)
    have he : (q:ℝ)*(R/(q:ℝ))=R := by field_simp
    rwa [he] at hh
  refine ⟨?_,?_,?_⟩
  · exact NativeFrozenTimeField.field_norm_le T (fun x => height x-origin) F R B hB
      (fun x hx => hF x (hTS hx))
  · intro U hUT x hx
    apply NativeFrozenTimeField.field_close_to_original T (fun x => height x-origin) F R R ?_ (hUT hx)
    intro y hy z hz he
    have hh := same_height_cell_close (div_pos hR hqR) (hfine y hy z hz he)
    exact (hLip y (hTS hy) z (hTS hz)).trans
      ((mul_le_mul_of_nonneg_left hh.le hL).trans hsmall)
  · intro U hUT x hx y hy
    obtain ⟨v,hv,hvheight,hvF⟩ := NativeFrozenTimeField.field_realization T
      (fun z => height z-origin) F R ⟨x,hUT hx,rfl⟩
    obtain ⟨z,hz,hzheight,hzF⟩ := NativeFrozenTimeField.field_realization T
      (fun z => height z-origin) F R ⟨y,hUT hy,rfl⟩
    change coarse R origin (height v)=coarse R origin (height x) at hvheight
    change coarse R origin (height z)=coarse R origin (height y) at hzheight
    change selectedField T height F R origin (coarse R origin (height x))=F v at hvF
    change selectedField T height F R origin (coarse R origin (height y))=F z at hzF
    by_cases he : coarse R origin (height x)=coarse R origin (height y)
    · rw [he,dist_self]
      positivity
    · rw [hvF,hzF]
      have hd := colored_height_distance hR
        (show coarse R origin (height v) ≠ coarse R origin (height z) by rwa [hvheight,hzheight])
        (hcolor v hv z hz)
      rw [hvheight,hzheight] at hd
      have hh := (hLip v (hTS hv) z (hTS hz)).trans (mul_le_mul_of_nonneg_left hd hL)
      simpa only [mul_assoc,mul_left_comm L (9/8:ℝ)] using hh

/-- Choose the heaviest fine bin separately in every actual coarse cell,
then one global coarse residue. Every surviving coarse cell retains its
own fraction 1/q of the original weight. No point weight is changed. -/
theorem select_locally_retained_field {A V : Type*} [NormedAddCommGroup V]
    (S : Finset A) (w : A → ℕ) (height : A → ℝ) (F : A → V)
    (L R origin B : ℝ) (hL : 0 ≤ L) (hR : 0 < R) (hB : 0 ≤ B)
    (hF : ∀x∈S,‖F x‖ ≤ B)
    (hLip : ∀x∈S,∀y∈S,dist (F x) (F y) ≤ L*|height x-height y|) :
    let q:=subdivisions L
    let hq:0 < q:=(subdivisions_bounds L).1
    ∃best : ℤ → Fin q,∃color : Fin 8,
      let T:=S.filter (fun x => residue q hq (fine R origin q (height x))=
        best (coarse R origin (height x)) ∧
        residue 8 (by decide) (coarse R origin (height x))=color)
      T⊆S ∧ mass S w ≤ (8*q)*mass T w ∧
      (mass S w:ℝ) ≤ (16*max 1 L)*(mass T w:ℝ) ∧
      (∀c∈T.image (fun x => coarse R origin (height x)),
        mass (S.filter (fun x => coarse R origin (height x)=c)) w ≤
          q*mass (T.filter (fun x => coarse R origin (height x)=c)) w) ∧
      (∀x∈T,∀y∈T,coarse R origin (height x)=coarse R origin (height y) →
        fine R origin q (height x)=fine R origin q (height y)) ∧
      (∀c,‖selectedField T height F R origin c‖ ≤ B) ∧
      (∀U⊆T,∀x∈U,
        dist (selectedField T height F R origin (coarse R origin (height x))) (F x) ≤ R) ∧
      ∀U⊆T,∀x∈U,∀y∈U,
        dist (selectedField T height F R origin (coarse R origin (height x)))
          (selectedField T height F R origin (coarse R origin (height y))) ≤
        ((9/8:ℝ)*L)*dist (center R origin (coarse R origin (height x)))
          (center R origin (coarse R origin (height y))) := by
  intro q hq
  let : Nonempty (Fin q) := ⟨⟨0,hq⟩⟩
  let cell := fun x : A => coarse R origin (height x)
  let bin := fun x : A => residue q hq (fine R origin q (height x))
  obtain ⟨best,h1S,hlocal,hret1,hbin⟩ := select_color_per_cell S w cell bin
  let S1 := S.filter (fun x => bin x=best (cell x))
  let colorMap := fun x : A => residue 8 (by decide) (cell x)
  obtain ⟨color,hret2⟩ := maximum_weight_color S1 w colorMap
  let T := S.filter (fun x => bin x=best (cell x) ∧ colorMap x=color)
  have hT_eq : T=S1.filter (fun x => colorMap x=color) := by
    ext x
    simp only [T,S1,mem_filter,and_assoc]
  have hT1 : T⊆S1 := hT_eq.symm ▸ filter_subset _ _
  have hTS : T⊆S := hT1.trans h1S
  have hret1' : mass S w ≤ q*mass S1 w := by
    simpa only [Fintype.card_fin] using hret1
  have hret2' : mass S1 w ≤ 8*mass T w := by
    rw [hT_eq]
    simpa only [Fintype.card_fin,mass] using hret2
  have hret : mass S w ≤ (8*q)*mass T w := by
    calc
      _ ≤ q*mass S1 w := hret1'
      _ ≤ q*(8*mass T w) := Nat.mul_le_mul_left q hret2'
      _ = _ := by ring
  have hfine (x : A) (hx : x∈T) (y : A) (hy : y∈T)
      (hc : cell x=cell y) : fine R origin q (height x)=fine R origin q (height y) := by
    have hp : paint R origin q hq (height x)=paint R origin q hq (height y) := by
      apply Prod.ext
      · exact congrArg (residue 8 (by decide)) hc
      · exact hbin x (hT1 hx) y (hT1 hy) hc
    exact same_coarse_same_fine hq hc hp
  have hcolor (x : A) (hx : x∈T) (y : A) (hy : y∈T) : cell x%8=cell y%8 := by
    exact residue_eq_emod (hL:=by decide) ((mem_filter.mp hx).2.2.trans (mem_filter.mp hy).2.2.symm)
  have hfield := selected_field_bounds S T hTS height F L R origin B hL hR hB q hq
    (subdivisions_bounds L).2.1 hF hLip hfine hcolor
  refine ⟨best,color,hTS,hret,?_,?_,hfine,hfield.1,hfield.2.1,hfield.2.2⟩
  · have hn : (mass S w:ℝ) ≤ ((8*q:ℕ):ℝ)*(mass T w:ℝ) := by exact_mod_cast hret
    exact hn.trans (mul_le_mul_of_nonneg_right (subdivisions_bounds L).2.2 (Nat.cast_nonneg _))
  · intro c hc
    obtain ⟨x,hx,hxc⟩ := mem_image.mp hc
    have hcc : residue 8 (by decide) c=color := by
      rw [←hxc]
      exact (mem_filter.mp hx).2.2
    have he : T.filter (fun x => cell x=c)=S1.filter (fun x => cell x=c) := by
      ext y
      simp only [T,S1,mem_filter]
      constructor
      · exact fun hy => ⟨⟨hy.1.1,hy.1.2.1⟩,hy.2⟩
      · rintro ⟨⟨hy,hbinY⟩,hyc⟩
        refine ⟨⟨hy,hbinY,?_⟩,hyc⟩
        change residue 8 (by decide) (cell y)=color
        rw [hyc]
        exact hcc
    rw [he]
    simpa only [Fintype.card_fin] using hlocal c

end NativeLipschitzLocalHeightSelection
