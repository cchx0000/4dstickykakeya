import Theorems.Thm_StickyKakeya4_native_htotal_implementation

/- Original-incidence retention through the literal planar Y selection.
Originally drafted without verification; consult current receipts. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 8192
set_option maxHeartbeats 3500000
noncomputable section
namespace NativeRawWholeYRetention
open Classical Finset NativeJointUniformCoarseRelations NativeConfiguredYWeightedRetention
open NativeLiteralYHeightAlignment NativeWholeYGraphRetention NativeYTotalEpsilonBudget
open scoped BigOperators

/-- The common class is selected using the actual planar witnesses and
original Y cardinalities. Only the installed Y-key radix is charged. -/
theorem select_actual_common_edges {A P : Type*} [DecidableEq A] [DecidableEq P]
    (T : Finset A) (hT : T.Nonempty) (point : A → P) (key : P → Key) (Q : ℕ)
    (HY : HasUniformFibers T Q (fun z => key (point z)))
    (u bins : ℕ) (t zeta chi : ℝ)
    (W : ∀h : {h : ℤ // h∈(T.image (fun z => key (point z))).image Prod.fst},
      HeightAlignment (T.image (fun z => key (point z))) u t zeta chi h.val)
    (bin : ℝ → Fin (bins+1)) :
    ∃c : NativeYCommonScaleSelection.Menu u bins,∃selected : Finset Key,
      selected⊆T.image (fun z => key (point z)) ∧ selected.Nonempty ∧
      let U := T.filter (fun z => key (point z)∈selected)
      menuFraction zeta c/(2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ))*(T.card:ℝ) ≤
        (Q:ℝ)^2*(U.card:ℝ) ∧
      U⊆T ∧ U.Nonempty ∧
      (∀p∈U.image point,U.filter (fun z => point z=p)=T.filter (fun z => point z=p)) ∧
      ∀h∈selected.image Prod.fst,∃hh : h∈(T.image (fun z => key (point z))).image Prod.fst,
        (W ⟨h,hh⟩).chart=c.1 ∧ (W ⟨h,hh⟩).rhoDepth=c.2.1 ∧
        (W ⟨h,hh⟩).tauDepth=c.2.2.1 ∧ bin (W ⟨h,hh⟩).exponent=c.2.2.2 ∧
        heightPoints selected ((2:ℝ)⁻¹^u/512) h=(W ⟨h,hh⟩).selected := by
  let f := fun z => key (point z)
  obtain ⟨c,selected,hsel,hsn,hret,hwhole⟩ :=
    select_aligned_common (T.image f) (hT.image f) u bins t zeta chi W bin
  let N : ℝ := 2*((u+10:ℕ):ℝ)^2*((bins+1:ℕ):ℝ)
  have hN : 0 < N := by dsimp [N]; positivity
  have hf : 0 < menuFraction zeta c := by unfold menuFraction; positivity
  have hret' : menuFraction zeta c*((T.image f).card:ℝ) ≤ N*(selected.card:ℝ) := by
    convert hret using 1
  have hfrac : menuFraction zeta c/N*((T.image f).card:ℝ) ≤ (selected.card:ℝ) := by
    have hh := (div_le_iff₀ hN).mpr (by simpa only [mul_comm] using hret')
    convert hh using 1
    ring
  have hm := uniform_subset_retention T f Q HY selected hsel
    (menuFraction zeta c/N) (div_nonneg hf.le hN.le) hfrac
  let U := T.filter (fun z => f z∈selected)
  have hUn : U.Nonempty := by
    obtain ⟨y,hy⟩ := hsn
    obtain ⟨z,hz,hzy⟩ := mem_image.mp (hsel hy)
    exact ⟨z,mem_filter.mpr ⟨hz,by rw [hzy]; exact hy⟩⟩
  refine ⟨c,selected,hsel,hsn,hm,filter_subset _ _,hUn,?_,hwhole⟩
  intro p hp
  obtain ⟨z,hz,hzp⟩ := mem_image.mp hp
  have hzsel := (mem_filter.mp hz).2
  ext w
  simp only [U,mem_filter]
  constructor
  · exact fun hw => ⟨hw.1.1,hw.2⟩
  · rintro ⟨hw,hwp⟩
    refine ⟨⟨hw,?_⟩,hwp⟩
    simpa only [f,hwp,hzp] using hzsel

/-- Normalize the actual original-edge retention; using Q^4 here is an
explicit conservative weakening of the sharper Q^2 supplied above. -/
theorem normalized_mass_transfer {nu eps sigma zeta eB N : ℝ}
    (Q : ℕ) (hQ : 1 ≤ Q) (T U : ℕ)
    (hnu : 0 ≤ nu) (hsigma : 0 < sigma) (hN : 0 < N)
    (Hbase : (16/(5:ℝ)^4)*eps^(5*eB/16) ≤ nu*T)
    (Hret : (sigma/32768)^zeta/N*(T:ℝ) ≤ (Q:ℝ)^2*(U:ℝ)) :
    (16/(5:ℝ)^4)*(sigma/32768)^zeta*eps^(5*eB/16) ≤ N*(Q:ℝ)^4*(nu*U) := by
  have hfrac : 0 ≤ (sigma/32768)^zeta := by positivity
  have hQr : (1:ℝ) ≤ Q := by exact_mod_cast hQ
  have hPow : (Q:ℝ)^2 ≤ (Q:ℝ)^4 := pow_le_pow_right₀ hQr (by decide)
  have hmass := mul_le_mul_of_nonneg_left Hret (mul_nonneg hnu hN.le)
  have hmass' : (sigma/32768)^zeta*(nu*T) ≤ N*(Q:ℝ)^2*(nu*U) := by
    convert hmass using 1 <;> field_simp [hN.ne'] <;> ring
  calc
    _ = (sigma/32768)^zeta*((16/(5:ℝ)^4)*eps^(5*eB/16)) := by ring
    _ ≤ (sigma/32768)^zeta*(nu*T) := mul_le_mul_of_nonneg_left Hbase hfrac
    _ ≤ N*(Q:ℝ)^2*(nu*U) := hmass'
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPow hN.le)
      (mul_nonneg hnu (Nat.cast_nonneg U))

/-- The existing epsilon budget pays the normalized raw total itself.
The temporary division by eps^4 is purely scalar and cancels exactly. -/
theorem pay_raw_mass_at_epsilon {eps sigma E zeta53 eB c3 window menuTax N mass : ℝ}
    (Q : ℕ) (heps : 0 < eps) (heps1 : eps ≤ 1)
    (hs : 0 < sigma) (hE : 0 < E) (hzeta : zeta53 ≤ E/16384)
    (heB : 0 ≤ eB) (chi : ℝ) (hchi : 0 < chi)
    (htax : 5*eB/16+2*c3/window+menuTax ≤ (chi/2)*(E/16384))
    (hMenu : N ≤ eps^(-menuTax)) (hQ : (Q:ℝ)^4 ≤ eps^(-(2*c3/window)))
    (hSigma : sigma ≤ eps^(chi/2))
    (hfixed : ((5:ℝ)^4*(32768:ℝ)^zeta53/16)*eps^((chi/2)*(E/8192)) ≤ 1)
    (hmass : 0 ≤ mass)
    (Hsource : (16/(5:ℝ)^4)*(sigma/32768)^zeta53*eps^(5*eB/16) ≤ N*(Q:ℝ)^4*mass) :
    sigma^(E/4096) ≤ mass := by
  have hCancel : eps^4*(mass/eps^4)=mass := by field_simp [heps.ne']
  have Hsource' : (16/(5:ℝ)^4)*(sigma/32768)^zeta53*eps^(5*eB/16) ≤
      N*(Q:ℝ)^4*eps^4*(mass/eps^4) := by
    calc
      _ ≤ N*(Q:ℝ)^4*mass := Hsource
      _ = _ := by rw [mul_assoc (N*(Q:ℝ)^4),hCancel]
  have hh := pay_actual_graph_mass_at_epsilon Q heps heps1 hs hE hzeta heB chi hchi
    htax hMenu hQ hSigma hfixed (div_nonneg hmass (pow_nonneg heps.le 4)) Hsource'
  simpa only [hCancel] using hh

end NativeRawWholeYRetention
