module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongLimit

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PParamPieceInt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

namespace ParamPieceInt

theorem analyticAt_of_differentiableOn {d m : ℕ} {U : Set (Fin d → ℂ)} {f : (Fin d → ℂ) → Fin m → ℂ}
    (hU : IsOpen U) (hf : DifferentiableOn ℂ f U) {x : Fin d → ℂ} (hx : x ∈ U) : AnalyticAt ℂ f x := by
  refine AnalyticAt.pi fun i => ?_
  refine IndefiniteRowSideFullHecke.ComplexSets.analyticOnNhd_of_continuousOn_of_separately hU
    ((continuous_apply i).comp_continuousOn hf.continuousOn) (fun z hz j => ?_) x hx
  have hfz : DifferentiableAt ℂ (fun w => f w i) z :=
    differentiableAt_pi.mp (hf.differentiableAt (hU.mem_nhds hz)) i
  have hu : DifferentiableAt ℂ (Function.update z j) (z j) :=
    (hasFDerivAt_update z (z j)).differentiableAt
  have hfz' : DifferentiableAt ℂ (fun w => f w i) (Function.update z j (z j)) := by
    rwa [Function.update_eq_self]
  exact hfz'.comp (z j) hu

variable {n d : ℕ}

theorem differentiable_mulVec (A : Matrix (Fin d) (Fin n) ℂ) :
    Differentiable ℂ (fun x : Fin n → ℂ => A *ᵥ x) := by
  have h := (Matrix.mulVecLin A).toContinuousLinearMap.differentiable
  convert h using 1
  ext x
  simp only [LinearMap.coe_toContinuousLinearMap', Matrix.mulVecLin_apply]

theorem exists_sheet {W : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {σ : (Fin d → ℂ) → Fin n → ℂ} {r r' : ℝ} {N : Set (Fin n → ℂ)}
    (hσ : DifferentiableOn ℂ σ (Metric.ball 0 r)) (hinj : Set.InjOn σ (Metric.ball 0 r))
    (hN : IsOpen N) (hrr : r' < r)
    (hprop : ∀ w ∈ Metric.ball (0 : Fin d → ℂ) r, σ w ∈ N → σ w ∈ zeroSet W ∧ ‖w‖ ≤ r')
    (hcov : zeroSet W ∩ N ⊆ σ '' Metric.ball 0 r)
    {w : Fin d → ℂ} (hw : w ∈ Metric.ball 0 r) (hwN : σ w ∈ N)
    (hdet : LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0) :
    ∃ s : (Fin d → ℂ) → Fin n → ℂ, IsSheetAt W A (σ w) s ∧
      ∀ᶠ v in 𝓝 w, s (A *ᵥ σ v) = σ v := by
  classical
  set g : (Fin d → ℂ) → Fin d → ℂ := fun v => A *ᵥ σ v with hg
  set Ω : Set (Fin d → ℂ) := Metric.ball 0 r ∩ σ ⁻¹' N with hΩ
  have hΩo : IsOpen Ω := hσ.continuousOn.isOpen_inter_preimage Metric.isOpen_ball hN
  have hgd : DifferentiableOn ℂ g (Metric.ball 0 r) :=
    (differentiable_mulVec A).comp_differentiableOn hσ
  have hgan : ∀ v ∈ Metric.ball (0 : Fin d → ℂ) r, AnalyticAt ℂ g v := fun v hv =>
    analyticAt_of_differentiableOn Metric.isOpen_ball hgd hv

  have hstrict : HasStrictFDerivAt g
      (((fderiv ℂ g w).toContinuousLinearEquivOfDetNeZero hdet : (Fin d → ℂ) ≃L[ℂ] Fin d → ℂ) :
        (Fin d → ℂ) →L[ℂ] Fin d → ℂ) w := by
    have he : (((fderiv ℂ g w).toContinuousLinearEquivOfDetNeZero hdet : (Fin d → ℂ) ≃L[ℂ] Fin d → ℂ) :
        (Fin d → ℂ) →L[ℂ] Fin d → ℂ) = fderiv ℂ g w := by
      ext1 v
      simp
    rw [he]
    exact (hgan w hw).hasStrictFDerivAt
  obtain ⟨e, heg, hwe⟩ : ∃ e : OpenPartialHomeomorph (Fin d → ℂ) (Fin d → ℂ),
      (e : (Fin d → ℂ) → Fin d → ℂ) = g ∧ w ∈ e.source :=
    ⟨hstrict.toOpenPartialHomeomorph g, hstrict.toOpenPartialHomeomorph_coe,
      hstrict.mem_toOpenPartialHomeomorph_source⟩

  have hdetc : ContinuousAt (fun v => (fderiv ℂ g v).det) w :=
    ContinuousLinearMap.continuous_det.continuousAt.comp (hgan w hw).fderiv.continuousAt
  have h1 : ∀ᶠ v in 𝓝 w, v ∈ Ω := hΩo.mem_nhds ⟨hw, hwN⟩
  have h2 : ∀ᶠ v in 𝓝 w, v ∈ e.source := e.open_source.mem_nhds hwe
  have hev : ∀ᶠ v in 𝓝 w, (v ∈ Ω ∧ v ∈ e.source) ∧ (fderiv ℂ g v).det ≠ 0 :=
    (h1.and h2).and (hdetc.eventually_ne hdet)
  obtain ⟨O, hOp, hOo, hwO⟩ := eventually_nhds_iff.1 hev
  have hsymm : ∀ v ∈ O, e.symm (g v) = v := fun v hv => by
    rw [← heg]; exact e.left_inv (hOp v hv).1.2
  set U : Set (Fin d → ℂ) := e.target ∩ e.symm ⁻¹' O with hU
  have hUo : IsOpen U := e.isOpen_inter_preimage_symm hOo
  have hgU : ∀ v ∈ O, g v ∈ U := fun v hv =>
    ⟨by rw [← heg]; exact e.map_source (hOp v hv).1.2, by
      show e.symm (g v) ∈ O; rw [hsymm v hv]; exact hv⟩
  have hright : ∀ y ∈ U, g (e.symm y) = y := fun y hy => by
    rw [← heg]; exact e.right_inv hy.1
  have hsymmd : ∀ y ∈ U, DifferentiableAt ℂ e.symm y := by
    intro y hy
    have hv : e.symm y ∈ O := hy.2
    have hd := (hOp _ hv).2
    have hf : HasFDerivAt (e : (Fin d → ℂ) → Fin d → ℂ)
        (((fderiv ℂ g (e.symm y)).toContinuousLinearEquivOfDetNeZero hd :
          (Fin d → ℂ) ≃L[ℂ] Fin d → ℂ) : (Fin d → ℂ) →L[ℂ] Fin d → ℂ) (e.symm y) := by
      have he : (((fderiv ℂ g (e.symm y)).toContinuousLinearEquivOfDetNeZero hd :
          (Fin d → ℂ) ≃L[ℂ] Fin d → ℂ) : (Fin d → ℂ) →L[ℂ] Fin d → ℂ) = fderiv ℂ g (e.symm y) := by
        ext1 v
        simp
      rw [he, heg]
      exact (hgan _ (hOp _ hv).1.1.1).differentiableAt.hasFDerivAt
    exact (e.hasFDerivAt_symm hy.1 hf).differentiableAt
  refine ⟨σ ∘ e.symm, ⟨U, hUo, hgU w hwO, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro y hy
    have hv : e.symm y ∈ O := hy.2
    exact ((hσ.differentiableAt (Metric.isOpen_ball.mem_nhds (hOp _ hv).1.1.1)).comp y
      (hsymmd y hy)).differentiableWithinAt
  · show σ (e.symm (g w)) = σ w
    rw [hsymm w hwO]
  · intro y hy
    have hv : e.symm y ∈ O := hy.2
    refine ⟨hright y hy, ?_⟩
    exact (hprop _ (hOp _ hv).1.1.1 (hOp _ hv).1.1.2).1
  ·
    set K : Set (Fin d → ℂ) := Metric.closedBall 0 r' \ O with hK
    have hKb : K ⊆ Metric.ball 0 r := fun v hv => Metric.closedBall_subset_ball hrr hv.1
    have hKc : IsCompact (σ '' K) :=
      ((isCompact_closedBall 0 r').diff hOo).image_of_continuousOn (hσ.continuousOn.mono hKb)
    have hwK : σ w ∉ σ '' K := by
      rintro ⟨k, hk, hkw⟩
      exact hk.2 (hinj (hKb hk) hw hkw ▸ hwO)
    refine ⟨N ∩ (σ '' K)ᶜ, (hN.inter hKc.isClosed.isOpen_compl).mem_nhds ⟨hwN, hwK⟩, ?_⟩
    rintro x' ⟨hx'Z, hx'N, hx'K⟩ -
    obtain ⟨v, hvb, rfl⟩ := hcov ⟨hx'Z, hx'N⟩
    have hvr : ‖v‖ ≤ r' := (hprop v hvb hx'N).2
    have hvO : v ∈ O := by
      by_contra hvO
      exact hx'K ⟨v, ⟨mem_closedBall_zero_iff.2 hvr, hvO⟩, rfl⟩
    show σ v = σ (e.symm (g v))
    rw [hsymm v hvO]
  · filter_upwards [hOo.mem_nhds hwO] with v hv
    show σ (e.symm (g v)) = σ v
    rw [hsymm v hv]

end ParamPieceInt


open ParamPieceInt in
theorem ParamPieceInt.proof : ParamPieceInt.Statement := by
  intro n d W A σ r r' N hσ hinj hN hrr hprop hcov f φ P hφ hPm hPb hPw hgP
  classical
  set g : (Fin d → ℂ) → Fin d → ℂ := fun v => A *ᵥ σ v with hg
  have hgd : DifferentiableOn ℂ g (Metric.ball 0 r) :=
    (differentiable_mulVec A).comp_differentiableOn hσ
  have hgan : ∀ v ∈ Metric.ball (0 : Fin d → ℂ) r, AnalyticAt ℂ g v := fun v hv =>
    analyticAt_of_differentiableOn Metric.isOpen_ball hgd hv

  have hdens : ∀ w ∈ P, Complex.normSq (ReciprocityTheory.AnForm.A.jacC g w).det *
      chartDens W A ((σ '' P).indicator f) φ (g w) =
        f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w := by
    intro w hw
    obtain ⟨s, hs, hsg⟩ := exists_sheet hσ hinj hN hrr hprop hcov (hPb hw) (hPw w hw).1 (hPw w hw).2
    have hex : ∃ s, IsSheetAt W A (σ w) s := ⟨s, hs⟩
    have hfib : σ w ∈ ComplexSets.fibre W A (g w) := ⟨(hprop w (hPb hw) (hPw w hw).1).1, rfl⟩
    have hsum : chartDens W A ((σ '' P).indicator f) φ (g w) =
        f (σ w) * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (g w) := by
      unfold chartDens sheetSum
      rw [finsum_eq_single _ (σ w), finsum_eq_if, if_pos hfib, dite_eq_left hex]
      · beta_reduce
        rw [Set.indicator_of_mem (Set.mem_image_of_mem σ hw), IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k =>
          (SheetSumMeasurable.sheet_eventuallyEq hs hex.choose_spec).fun_comp (φ k)]
      · intro x hxne
        rw [finsum_eq_if]
        split_ifs with hx h
        · beta_reduce
          rw [Set.indicator_of_notMem, zero_mul]
          rintro ⟨w', hw', rfl⟩
          exact hxne (by rw [hgP hw' hw hx.2])
        · rfl
        · rfl

    obtain ⟨U, hUo, hwU, hsd, hsx, -, -⟩ := hs
    have hsc : ContDiffAt ℝ 2 s (g w) :=
      (analyticAt_of_differentiableOn hUo hsd hwU).contDiffAt.restrict_scalars ℝ
    have hφs : ∀ k, ContDiffAt ℝ 2 (φ k ∘ s) (g w) := by
      intro k
      obtain ⟨Uk, hUko, hZU, hcd⟩ := hφ k
      have hmem : s (g w) ∈ Uk := by
        show s (A *ᵥ σ w) ∈ Uk
        rw [hsx]; exact hZU (hprop w (hPb hw) (hPw w hw).1).1
      exact ((hcd.contDiffAt (hUko.mem_nhds hmem)).of_le
        (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))).comp (g w) hsc
    have hcomp : ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ g) w =
        ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ s) (g w) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC g w).det :=
      ReciprocityTheory.AnForm.A.maDens_comp (fun k => φ k ∘ s) g w (hgan w (hPb hw)) hφs
    have hev : ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ σ) w =
        ReciprocityTheory.AnForm.maDens (fun k => (φ k ∘ s) ∘ g) w :=
      IndefiniteRowSideFullHecke.ComplexSets.maDens_congr_of_eventuallyEq fun k => by
        filter_upwards [hsg] with v hv
        simp only [Function.comp_apply, g]
        rw [hv]
    rw [hsum, hev, hcomp]
    ring

  have hzero : ∀ y, y ∉ g '' P → chartDens W A ((σ '' P).indicator f) φ y = 0 := by
    intro y hy
    unfold chartDens sheetSum
    refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx => ?_
    split_ifs with h
    · beta_reduce
      rw [Set.indicator_of_notMem, zero_mul]
      rintro ⟨w, hw, rfl⟩
      exact hy ⟨w, hw, hx.2⟩
    · rfl
  have hgdP : ∀ w ∈ P, DifferentiableAt ℂ g w := fun w hw => (hgan w (hPb hw)).differentiableAt
  unfold chartInt
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero,
    integral_image_eq_integral_abs_det_fderiv_smul volume hPm
      (fun x hx => ((hgdP x hx).restrictScalars ℝ).hasFDerivAt.hasFDerivWithinAt) hgP]
  refine setIntegral_congr_fun hPm fun w hw => ?_
  rw [ReciprocityTheory.AnForm.A.det_fderiv_real_eq_normSq g w (hgdP w hw),
    abs_of_nonneg (Complex.normSq_nonneg _), smul_eq_mul, hdens w hw]

end

end GroundTheory.Heights₂.Heights
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMaDensLogPow
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology Matrix

noncomputable section

namespace MaDensLogPow

variable {D : ℕ}

theorem det_eq_zero_of_rows_smul (M : Matrix (Fin D) (Fin D) ℂ) (w : Fin D → ℂ) {i j : Fin D}
    (hij : i ≠ j) (a b : ℂ) (hi : M i = a • w) (hj : M j = b • w) : M.det = 0 := by
  by_cases ha : a = 0
  · exact Matrix.det_eq_zero_of_row_eq_zero i fun k => by simp [hi, ha]
  · rw [← Matrix.det_updateRow_add_smul_self M hij.symm (-(b / a))]
    refine Matrix.det_eq_zero_of_row_eq_zero j fun k => ?_
    rw [updateRow_self, hi, hj]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring

theorem mdisc_eq_zero_of_two_rankOne (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (w : Fin D → ℂ)
    {a b : Fin D} (hab : a ≠ b) (x x' : Fin D → ℂ) (ha : A a = vecMulVec x w)
    (hb : A b = vecMulVec x' w) : mdisc A = 0 := by
  rw [mdisc_eq_sum_polCoef]
  refine mul_eq_zero_of_right _ (Finset.sum_eq_zero fun r _ => ?_)
  by_cases hr : Function.Surjective r
  · obtain ⟨i, hi⟩ := hr a
    obtain ⟨j, hj⟩ := hr b
    have hij : i ≠ j := fun h => hab (by rw [← hi, ← hj, h])
    refine mul_eq_zero_of_right _ (det_eq_zero_of_rows_smul _ w hij (x i) (x' j) ?_ ?_)
    · funext k; simp [hi, ha, vecMulVec_apply]
    · funext k; simp [hj, hb, vecMulVec_apply]
  · rw [polCoef_eq_zero r hr, zero_mul]

theorem mdisc_expand (α β : ℂ) (H G : Matrix (Fin D) (Fin D) ℂ)
    (hG : ∀ (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (i j : Fin D), i ≠ j → A i = G → A j = G →
      mdisc A = 0) :
    ∀ (s : Finset (Fin D)) (C : Fin D → Matrix (Fin D) (Fin D) ℂ), (∀ i ∈ s, C i = H) →
      mdisc (fun i => if i ∈ s then α • H + β • G else C i) =
        α ^ s.card * mdisc C + α ^ (s.card - 1) * β * ∑ i ∈ s, mdisc (Function.update C i G) := by
  classical
  intro s
  induction s using Finset.induction_on with
  | empty => intro C _; simp
  | insert j s hj ih =>
    intro C hC
    have hCj : C j = H := hC j (Finset.mem_insert_self j s)
    have hCs : ∀ i ∈ s, C i = H := fun i hi => hC i (Finset.mem_insert_of_mem hi)
    have e1 : (fun i => if i ∈ insert j s then α • H + β • G else C i) =
        Function.update (fun i => if i ∈ s then α • H + β • G else C i) j (α • H + β • G) := by
      funext i
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    have e2 : Function.update (fun i => if i ∈ s then α • H + β • G else C i) j H =
        (fun i => if i ∈ s then α • H + β • G else C i) := by
      funext i
      by_cases hij : i = j
      · subst hij; simp [hj, hCj]
      · simp [Function.update_of_ne hij]
    have e3 : Function.update (fun i => if i ∈ s then α • H + β • G else C i) j G =
        (fun i => if i ∈ s then α • H + β • G else Function.update C j G i) := by
      funext i
      by_cases hij : i = j
      · subst hij; simp [hj]
      · simp [Function.update_of_ne hij]
    have hCs' : ∀ i ∈ s, Function.update C j G i = H := fun i hi => by
      rw [Function.update_of_ne (by rintro rfl; exact hj hi)]; exact hCs i hi
    have hz : ∀ i ∈ s, mdisc (Function.update (Function.update C j G) i G) = 0 := fun i hi =>
      hG _ i j (by rintro rfl; exact hj hi) (by simp)
        (by rw [Function.update_of_ne (by rintro rfl; exact hj hi)]; simp)
    rw [e1, mdisc_update_add, mdisc_update_smul, mdisc_update_smul, e2, e3, ih C hCs,
      ih _ hCs', Finset.sum_eq_zero hz, Finset.card_insert_of_notMem hj, Finset.sum_insert hj]
    rcases Nat.eq_zero_or_pos s.card with h0 | hpos
    · rw [h0, Finset.card_eq_zero.mp h0]; simp
    · obtain ⟨m, hm⟩ : ∃ m, s.card = m + 1 := ⟨s.card - 1, by omega⟩
      rw [hm]
      simp only [Nat.add_sub_cancel]
      ring

theorem cons_const_apply {n : ℕ} (A₀ H : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) (k : Fin (n + 1 + 1)) :
    (Fin.cons A₀ (fun _ : Fin (n + 1) => H) : Fin (n + 1 + 1) → _) k = if k = 0 then A₀ else H := by
  refine Fin.cases ?_ (fun i => ?_) k
  · simp
  · simp [Fin.succ_ne_zero]

theorem cons_cons_const_apply {n : ℕ} (G A₀ H : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ)
    (k : Fin (n + 1 + 1)) :
    (Fin.cons G (Fin.cons A₀ (fun _ : Fin n => H)) : Fin (n + 1 + 1) → _) k =
      if k = 0 then G else if k = 1 then A₀ else H := by
  refine Fin.cases ?_ (fun i => ?_) k
  · simp
  · refine Fin.cases ?_ (fun l => ?_) i
    · simp
    · have h1 : (l.succ.succ : Fin (n + 1 + 1)) ≠ 1 := by
        rw [← Fin.succ_zero_eq_one]; exact fun h => Fin.succ_ne_zero l (Fin.succ_injective _ h)
      simp [Fin.succ_ne_zero, h1]

theorem mdisc_update_eq {n : ℕ} (G A₀ H : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) (i : Fin (n + 1 + 1))
    (hi : i ≠ 0) :
    mdisc (Function.update (Fin.cons A₀ (fun _ : Fin (n + 1) => H) : Fin (n + 1 + 1) → _) i G) =
      mdisc (Fin.cons G (Fin.cons A₀ (fun _ : Fin n => H)) : Fin (n + 1 + 1) → _) := by
  rw [← mdisc_comp_perm (Fin.cons G (Fin.cons A₀ (fun _ : Fin n => H)) : Fin (n + 1 + 1) → _)
    ((Equiv.swap 1 i).trans (Equiv.swap 0 1))]
  congr 1
  funext k
  simp only [Function.comp_apply, cons_const_apply, cons_cons_const_apply, Function.update_apply,
    Equiv.trans_apply, Equiv.swap_apply_def]
  have h01 : (0 : Fin (n + 1 + 1)) ≠ 1 := by
    rw [← Fin.succ_zero_eq_one]; exact (Fin.succ_ne_zero 0).symm
  by_cases hki : k = i
  · subst hki
    by_cases hk1 : k = 1
    · subst hk1; simp [Ne.symm h01]
    · simp [hk1]
  · by_cases hk0 : k = 0
    · subst hk0; simp [Ne.symm hi, h01]
    · by_cases hk1 : k = 1
      · subst hk1; simp [hki, Ne.symm hki, hi, Ne.symm h01]
      · simp [hki, hk0, hk1]

theorem hessC_log_comp {p : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (hp : ContDiffAt ℝ 2 p y) (hpos : 0 < p y) :
    hessC (Real.log ∘ p) y =
      (((p y)⁻¹ : ℝ) : ℂ) • hessC p y + ((-((p y) ^ 2)⁻¹ : ℝ) : ℂ) • gradMat p p y := by
  set c := p y / 2 with hc
  have hc0 : 0 < c := by positivity
  set h : ℝ → ℝ := fun t => c / 2 + Real.smoothTransition ((t - c / 2) / (c / 2)) * (t - c / 2) with hh
  have hhpos : ∀ t, 0 < h t := by
    intro t
    by_cases ht : t ≤ c / 2
    · have : (t - c / 2) / (c / 2) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      simp only [hh, Real.smoothTransition.zero_of_nonpos this, zero_mul, add_zero]; positivity
    · have := Real.smoothTransition.nonneg ((t - c / 2) / (c / 2))
      have : 0 ≤ Real.smoothTransition ((t - c / 2) / (c / 2)) * (t - c / 2) :=
        mul_nonneg this (by linarith)
      simp only [hh]; linarith
  have hhc : ContDiff ℝ 2 h := by
    have hs : ContDiff ℝ 2 Real.smoothTransition := Real.smoothTransition.contDiff (n := 2)
    exact contDiff_const.add ((hs.comp ((contDiff_id.sub contDiff_const).div_const _)).mul
      (contDiff_id.sub contDiff_const))
  set F : ℝ → ℝ := Real.log ∘ h with hF
  have hFc : ContDiff ℝ 2 F := hhc.log fun t => (hhpos t).ne'
  have hFeq : F =ᶠ[𝓝 (p y)] Real.log := by
    filter_upwards [Ioi_mem_nhds (show c < p y by rw [hc]; linarith)] with t ht
    have h1 : 1 ≤ (t - c / 2) / (c / 2) := by
      rw [le_div_iff₀ (by positivity)]; simp only [Set.mem_Ioi] at ht; linarith
    simp only [hF, hh, Function.comp_apply, Real.smoothTransition.one_of_one_le h1, one_mul]
    ring_nf
  have hgerm : Real.log ∘ p =ᶠ[𝓝 y] F ∘ p :=
    ((hp.continuousAt.tendsto.eventually hFeq).mono fun x hx => hx.symm)
  have hgerm2 : hessC (Real.log ∘ p) y = hessC (F ∘ p) y := by
    unfold hessC
    rw [hgerm.fderiv.fderiv_eq]
  have hd1 : deriv F (p y) = (p y)⁻¹ := by rw [hFeq.deriv_eq, Real.deriv_log]
  have hd2 : deriv (deriv F) (p y) = -((p y) ^ 2)⁻¹ := by
    rw [hFeq.deriv.deriv_eq, Real.deriv_log', deriv_inv]
  rw [hgerm2, MaDensChain.hessC_comp_real F p y hFc hp, hd1, hd2]

theorem proof : MaDensLogPow.Statement := by
  intro e φ₀ p y hp hpos
  set H := hessC p y with hH
  set G := gradMat p p y with hGdef
  set A₀ := hessC φ₀ y with hA₀
  set a : ℝ := (p y)⁻¹ with ha
  set b : ℝ := -((p y) ^ 2)⁻¹ with hb
  have hlog : hessC (Real.log ∘ p) y = (a : ℂ) • H + (b : ℂ) • G := hessC_log_comp hp hpos
  have hG : ∀ (A : Fin (e + 1 + 1) → Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ) (i j : Fin (e + 1 + 1)),
      i ≠ j → A i = G → A j = G → mdisc A = 0 := fun A i j hij hi hj =>
    mdisc_eq_zero_of_two_rankOne A _ hij _ _ (hi.trans (gradMat_eq_vecMulVec p p y))
      (hj.trans (gradMat_eq_vecMulVec p p y))
  set s : Finset (Fin (e + 1 + 1)) := Finset.univ.erase 0 with hs
  have hscard : s.card = e + 1 := by simp [hs]
  set C : Fin (e + 1 + 1) → Matrix (Fin (e + 1 + 1)) (Fin (e + 1 + 1)) ℂ :=
    Fin.cons A₀ (fun _ : Fin (e + 1) => H) with hC
  have hCs : ∀ i ∈ s, C i = H := fun i hi => by
    rw [hC, cons_const_apply, if_neg (Finset.ne_of_mem_erase hi)]
  have key := mdisc_expand (a : ℂ) (b : ℂ) H G hG s C hCs
  rw [Finset.sum_congr rfl fun i hi => mdisc_update_eq G A₀ H i (Finset.ne_of_mem_erase hi),
    Finset.sum_const, hscard, Nat.add_sub_cancel, nsmul_eq_mul] at key
  have hfam1 : (fun k => hessC ((Fin.cons φ₀ fun _ : Fin (e + 1) => Real.log ∘ p :
      Fin (e + 1 + 1) → (Fin (e + 1 + 1) → ℂ) → ℝ) k) y) =
      fun i => if i ∈ s then (a : ℂ) • H + (b : ℂ) • G else C i := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [hs, hC, hA₀]
    · simp [hs, Fin.succ_ne_zero, hlog]
  have hfam2 : (fun k => hessC ((Fin.cons φ₀ fun _ : Fin (e + 1) => p :
      Fin (e + 1 + 1) → (Fin (e + 1 + 1) → ℂ) → ℝ) k) y) = C := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [hC, hA₀]
    · simp [hC, hH]
  have hfam3 : (fun i => hessC ((Fin.cons φ₀ fun _ : Fin e => p :
      Fin (e + 1) → (Fin (e + 1 + 1) → ℂ) → ℝ) i) y) = Fin.cons A₀ (fun _ : Fin e => H) := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simp [hA₀]
    · simp [hH]
  unfold maDens gradDens
  rw [hfam1, hfam2, hfam3, key]
  have hp0 : p y ≠ 0 := hpos.ne'
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.add_re,
    Complex.re_ofReal_mul]
  rw [← hGdef, ha, hb]
  simp only [inv_pow, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

end MaDensLogPow

end

end GroundTheory.Heights₂.Heights
end
