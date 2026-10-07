import Theorems.Thm_StickyKakeya4_native_direction_rank_dichotomy
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 3600000
noncomputable section
namespace NativeIncidentRankSelection
open Classical Finset StickyKakeya4 NativeCommonCubicalMesh NativeDirectionRankDichotomy
open scoped BigOperators

/-- Literal original incidence labels above one old cell. -/
def pointSet {n : ℕ} (E : Finset (Fin n × Index)) (k : Index) : Finset (Fin n × Index) :=
  E.filter (fun z => z.2=k)

/-- True graph-vector neighborhood inside that original point fiber. -/
def pointNear {n : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (k : Index) (r : ℝ) (P : Submodule ℝ E4) : Finset (Fin n × Index) :=
  nearLabels (pointSet E k) (fun z => slopeVector D z.1) r P

lemma pointNear_top {n : ℕ} (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (k : Index) (r : ℝ) (hr : 0 ≤ r) : pointNear D E k r ⊤=pointSet E k := by
  apply filter_eq_self.mpr
  intro z _hz
  rw [Metric.infDist_zero_of_mem (show slopeVector D z.1∈(⊤:Submodule ℝ E4) from Submodule.mem_top)]
  exact hr

/-- Rank four supplies existence, so a smallest admissible rank is genuinely
selected. Its radius is allowed, with no claim that this radius is minimal. -/
theorem point_minimal_rank {ι : Type*} [DecidableEq ι] {n : ℕ}
    (D : FiniteScaleSource n) (E : Finset (Fin n × Index))
    (radius : ι → ℝ) (eta : Fin 4 → ℝ) (allowed : Fin 4 → Finset ι)
    (heta : ∀ell,0 < eta ell)
    (hradius : ∀ell,∀j∈allowed ell,0 < radius j ∧ radius j ≤ 1)
    (htop : (allowed (3:Fin 4)).Nonempty) (k : Index) :
    ∃ell : Fin 4,∃j∈allowed ell,∃P : Submodule ℝ E4,
      Module.finrank ℝ P ≤ ell.val+1 ∧
      (radius j)^(eta ell)*((pointSet E k).card:ℝ) ≤ (pointNear D E k (radius j) P).card ∧
      ∀ell' : Fin 4,ell' < ell → ∀j'∈allowed ell',∀Q : Submodule ℝ E4,
        Module.finrank ℝ Q ≤ ell'.val+1 →
        ((pointNear D E k (radius j') Q).card:ℝ) <
          (radius j')^(eta ell')*((pointSet E k).card:ℝ) := by
  let S := (univ:Finset (Fin 4)).filter (fun ell => ∃j∈allowed ell,∃P : Submodule ℝ E4,
    Module.finrank ℝ P ≤ ell.val+1 ∧
      (radius j)^(eta ell)*((pointSet E k).card:ℝ) ≤ (pointNear D E k (radius j) P).card)
  have hS : S.Nonempty := by
    obtain ⟨j,hj⟩ := htop
    refine ⟨3,mem_filter.mpr ⟨mem_univ _,j,hj,⊤,?_,?_⟩⟩
    · simp [E4]
    · rw [pointNear_top D E k (radius j) (hradius 3 j hj).1.le]
      exact mul_le_of_le_one_left (Nat.cast_nonneg _)
        (Real.rpow_le_one (hradius 3 j hj).1.le (hradius 3 j hj).2 (heta 3).le)
  let ell := S.min' hS
  have hell : ell∈S := min'_mem S hS
  obtain ⟨j,hj,P,hP,hmass⟩ := (mem_filter.mp hell).2
  refine ⟨ell,j,hj,P,hP,hmass,?_⟩
  intro ell' hlt j' hj' Q hQ
  apply lt_of_not_ge
  intro hmass'
  have hm : ell ≤ ell' := min'_le S ell' (mem_filter.mpr ⟨mem_univ _,j',hj',Q,hQ,hmass'⟩)
  exact (not_le_of_gt hlt) hm

lemma point_category_value {ι : Type*} [DecidableEq ι] {n : ℕ}
    (E : Finset (Fin n × Index)) (category : Index → ι) (c : ι) (k : Index)
    (hk : k∈(E.filter (fun z => category z.2=c)).image Prod.snd) : category k=c := by
  obtain ⟨z,hz,rfl⟩ := mem_image.mp hk
  exact (mem_filter.mp hz).2

lemma point_category_fiber {ι : Type*} [DecidableEq ι] {n : ℕ}
    (E : Finset (Fin n × Index)) (category : Index → ι) (c : ι) (k : Index)
    (hk : category k=c) :
    pointSet (E.filter (fun z => category z.2=c)) k=pointSet E k := by
  ext z
  simp only [pointSet,mem_filter]
  constructor
  · exact fun hz => ⟨hz.1.1,hz.2⟩
  · intro hz
    exact ⟨⟨hz.1,by rw [hz.2]; exact hk⟩,hz.2⟩

lemma point_filter_near {n : ℕ} (D : FiniteScaleSource n)
    (J : Finset (Fin n × Index)) (r : ℝ) (P : Index → Submodule ℝ E4) (k : Index) :
    pointSet (J.filter (fun z => Metric.infDist (slopeVector D z.1) (P z.2:Set E4) ≤ r)) k=
      pointNear D J k r (P k) := by
  ext z
  simp only [pointSet,pointNear,nearLabels,mem_filter]
  constructor
  · rintro ⟨⟨hz,hr⟩,hk⟩
    exact ⟨⟨hz,hk⟩,by simpa only [hk] using hr⟩
  · rintro ⟨⟨hz,hk⟩,hr⟩
    exact ⟨⟨hz,by simpa only [hk] using hr⟩,hk⟩

lemma card_eq_sum_pointSet {n : ℕ} (E : Finset (Fin n × Index)) (K : Finset Index)
    (hK : ∀z∈E,z.2∈K) : (E.card:ℝ)=∑k∈K,((pointSet E k).card:ℝ) := by
  exact_mod_cast card_eq_sum_card_fiberwise hK

/-- Summing pointwise retained mass uses original incidence degree as the
point weight. Empty rows remain in the reference sum. -/
lemma pointwise_retention_sum {n : ℕ} (E J F : Finset (Fin n × Index))
    (hFJ : F⊆J) (hcomplete : ∀k∈J.image Prod.snd,pointSet J k=pointSet E k)
    (lambda : ℝ)
    (H : ∀k∈J.image Prod.snd,lambda*((pointSet E k).card:ℝ) ≤ (pointSet F k).card) :
    lambda*(J.card:ℝ) ≤ (F.card:ℝ) := by
  have hFsum := card_eq_sum_pointSet F (J.image Prod.snd)
    (fun z hz => mem_image_of_mem _ (hFJ hz))
  have hJsum : (J.card:ℝ)=∑k∈J.image Prod.snd,((pointSet E k).card:ℝ) := by
    calc
      _ = ∑k∈J.image Prod.snd,((pointSet J k).card:ℝ) :=
        card_eq_sum_pointSet J (J.image Prod.snd) (fun z hz => mem_image_of_mem _ hz)
      _ = _ := sum_congr rfl (fun k hk => by rw [hcomplete k hk])
  rw [hJsum,hFsum,mul_sum]
  exact sum_le_sum H

/-- Actual finite-menu Step1 producer. Rank four proves pointwise existence;
least-rank selection and degree-weighted pigeonholing select the category.
F is then exactly the original near-plane fiber at each surviving point.
No winning rank, plane, retained family, or retention estimate is an input. -/
theorem exists_rank_scale_retention {ι : Type*} [DecidableEq ι] {n : ℕ}
    (D : FiniteScaleSource n) (E : Finset (Fin n × Index)) (hEn : E.Nonempty)
    (menu : Finset ι) (radius : ι → ℝ) (eta : Fin 4 → ℝ)
    (allowed : Fin 4 → Finset ι) (hallowed : ∀ell,allowed ell⊆menu)
    (heta : ∀ell,0 < eta ell) (hradius : ∀j∈menu,0 < radius j ∧ radius j ≤ 1)
    (htop : (allowed (3:Fin 4)).Nonempty) :
    ∃ell : Fin 4,∃j∈allowed ell,∃F⊆E,F.Nonempty ∧
      ((radius j)^(eta ell)/(4*(menu.card:ℝ)))*(E.card:ℝ) ≤ (F.card:ℝ) ∧
      ∃P : Index → Submodule ℝ E4,
        (∀z∈F,Metric.infDist (slopeVector D z.1) (P z.2:Set E4) ≤ radius j) ∧
        ∀k∈F.image Prod.snd,
          Module.finrank ℝ (P k) ≤ ell.val+1 ∧
          pointSet F k=pointNear D E k (radius j) (P k) ∧
          (radius j)^(eta ell)*((pointSet E k).card:ℝ) ≤ (pointSet F k).card ∧
          ∀ell' : Fin 4,ell' < ell → ∀j'∈allowed ell',∀Q : Submodule ℝ E4,
            Module.finrank ℝ Q ≤ ell'.val+1 →
            ((pointNear D E k (radius j') Q).card:ℝ) <
              (radius j')^(eta ell')*((pointSet E k).card:ℝ) := by
  have hex := fun k => point_minimal_rank D E radius eta allowed heta
    (fun ell j hj => hradius j (hallowed ell hj)) htop k
  choose rank scale hscale plane hdim hrich hearlier using hex
  let category : Index → Fin 4 × ι := fun k => (rank k,scale k)
  let C : Finset (Fin 4 × ι) := (univ:Finset (Fin 4)) ×ˢ menu
  have hmenu : menu.Nonempty := htop.mono (hallowed 3)
  have hC : C.Nonempty := (univ_nonempty: (univ:Finset (Fin 4)).Nonempty).product hmenu
  obtain ⟨c,hc,hmax⟩ := exists_max_image C
    (fun c => (E.filter (fun z => category z.2=c)).card) hC
  let J := E.filter (fun z => category z.2=c)
  have hCcard : C.card=4*menu.card := by simp only [C,card_product,card_univ,Fintype.card_fin]
  have hcat : E.card ≤ J.card*C.card := by
    apply card_le_mul_card_image_of_maps_to (f:=fun z => category z.2)
    · intro z _hz
      exact mem_product.mpr ⟨mem_univ _,hallowed _ (hscale z.2)⟩
    · exact hmax
  have hJn : J.Nonempty := by
    apply card_pos.mp
    have hp := card_pos.mpr hEn
    by_contra hz
    have hz' : J.card=0 := by omega
    rw [hz',zero_mul] at hcat
    omega
  obtain ⟨z0,hz0⟩ := hJn
  have hzcat : category z0.2=c := (mem_filter.mp hz0).2
  have hj : c.2∈allowed c.1 := by
    have he : rank z0.2=c.1 := congrArg Prod.fst hzcat
    have hf : scale z0.2=c.2 := congrArg Prod.snd hzcat
    simpa only [he,hf] using hscale z0.2
  have hr : 0 < radius c.2 := (hradius c.2 (hallowed c.1 hj)).1
  have hp : 0 < (radius c.2)^(eta c.1) := Real.rpow_pos_of_pos hr _
  have hden : 0 < 4*(menu.card:ℝ) := by
    have hm : (0:ℝ) < menu.card := by exact_mod_cast card_pos.mpr hmenu
    positivity
  let F := J.filter (fun z => Metric.infDist (slopeVector D z.1) (plane z.2:Set E4) ≤ radius c.2)
  have hFJ : F⊆J := filter_subset _ _
  have hJE : J⊆E := filter_subset _ _
  have hvalue (k : Index) (hk : k∈J.image Prod.snd) : category k=c :=
    point_category_value E category c k hk
  have hcomplete (k : Index) (hk : k∈J.image Prod.snd) : pointSet J k=pointSet E k :=
    point_category_fiber E category c k (hvalue k hk)
  have hexact (k : Index) (hk : k∈J.image Prod.snd) :
      pointSet F k=pointNear D E k (radius c.2) (plane k) := by
    rw [point_filter_near]
    unfold pointNear
    rw [hcomplete k hk]
  have hret (k : Index) (hk : k∈J.image Prod.snd) :
      (radius c.2)^(eta c.1)*((pointSet E k).card:ℝ) ≤ (pointSet F k).card := by
    rw [hexact k hk]
    have he : rank k=c.1 := congrArg Prod.fst (hvalue k hk)
    have hf : scale k=c.2 := congrArg Prod.snd (hvalue k hk)
    simpa only [he,hf] using hrich k
  have hlocal := pointwise_retention_sum E J F hFJ hcomplete _ hret
  have hcatR : (E.card:ℝ) ≤ (4*(menu.card:ℝ))*(J.card:ℝ) := by
    rw [hCcard] at hcat
    exact_mod_cast (show E.card ≤ 4*menu.card*J.card by nlinarith [hcat])
  have hcross : (radius c.2)^(eta c.1)*(E.card:ℝ) ≤ (4*(menu.card:ℝ))*(F.card:ℝ) := by
    calc
      _ ≤ (radius c.2)^(eta c.1)*((4*(menu.card:ℝ))*(J.card:ℝ)) :=
        mul_le_mul_of_nonneg_left hcatR hp.le
      _ = (4*(menu.card:ℝ))*((radius c.2)^(eta c.1)*(J.card:ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlocal hden.le
  have hglobal : ((radius c.2)^(eta c.1)/(4*(menu.card:ℝ)))*(E.card:ℝ) ≤ (F.card:ℝ) := by
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hden).mpr (by simpa only [mul_comm] using hcross)
  have hFn : F.Nonempty := by
    apply card_pos.mp
    have he : (0:ℝ) < E.card := by exact_mod_cast card_pos.mpr hEn
    have hf : (0:ℝ) < F.card := (mul_pos (div_pos hp hden) he).trans_le hglobal
    exact_mod_cast hf
  refine ⟨c.1,c.2,hj,F,hFJ.trans hJE,hFn,hglobal,plane,?_,?_⟩
  · intro z hz
    exact (mem_filter.mp hz).2
  · intro k hk
    have hkJ := image_subset_image hFJ hk
    have he : rank k=c.1 := congrArg Prod.fst (hvalue k hkJ)
    have hd : Module.finrank ℝ (plane k) ≤ c.1.val+1 := by simpa only [he] using hdim k
    refine ⟨hd,hexact k hkJ,hret k hkJ,?_⟩
    simpa only [he] using hearlier k

end NativeIncidentRankSelection
