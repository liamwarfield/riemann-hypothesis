module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsTwiceDifferentiableAt
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncBoundaryCoordinateChart
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.KillNoneFormPoly
public import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
public import ReciprocityTheory.AnalyticForms.LeviForms.HomDens
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.LintegralImageEqLintegralNormSqDetMul
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsHorizontalTwist

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralCongrPotentials
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralCongrPotentials
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

namespace SamePotInt

variable {D : ℕ}

theorem exists_fderiv_fderiv_re {H : (Fin D → ℂ) → ℂ} {y : Fin D → ℂ} (hH : AnalyticAt ℂ H y) :
    ∃ B : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ) →L[ℂ] ℂ, ∀ v w,
      fderiv ℝ (fderiv ℝ fun z => (H z).re) y v w = (B v w).re := by
  let Φ : ((Fin D → ℂ) →L[ℂ] ℂ) →L[ℝ] ((Fin D → ℂ) →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ (Fin D → ℂ) ℂ ℝ Complex.reCLM).comp
      (ContinuousLinearMap.restrictScalarsL ℂ (Fin D → ℂ) ℂ ℝ ℝ)
  have hev : (fderiv ℝ fun z => (H z).re) =ᶠ[𝓝 y] fun z => Φ (fderiv ℂ H z) := by
    filter_upwards [hH.eventually_analyticAt] with z hz
    have h1 : HasFDerivAt H ((fderiv ℂ H z).restrictScalars ℝ) z :=
      hz.differentiableAt.hasFDerivAt.restrictScalars ℝ
    exact (Complex.reCLM.hasFDerivAt.comp z h1).fderiv
  have hd : DifferentiableAt ℂ (fderiv ℂ H) y := hH.fderiv.differentiableAt
  refine ⟨fderiv ℂ (fderiv ℂ H) y, fun v w => ?_⟩
  have h2 : HasFDerivAt (fun z => Φ (fderiv ℂ H z))
      (Φ.comp ((fderiv ℂ (fderiv ℂ H) y).restrictScalars ℝ)) y :=
    Φ.hasFDerivAt.comp y (hd.hasFDerivAt.restrictScalars ℝ)
  rw [hev.fderiv_eq, h2.fderiv]
  rfl

theorem hessC_re_eq_zero {H : (Fin D → ℂ) → ℂ} {y : Fin D → ℂ} (hH : AnalyticAt ℂ H y) :
    hessC (fun z => (H z).re) y = 0 := by
  obtain ⟨B, hB⟩ := exists_fderiv_fderiv_re hH
  ext i j
  simp only [hessC, Matrix.zero_apply, hB, map_smul, _root_.smul_apply, smul_eq_mul,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  push_cast
  ring

theorem hessC_eq_of_eventuallyEq_add_re {a a' : (Fin D → ℂ) → ℝ} {H : (Fin D → ℂ) → ℂ}
    {y : Fin D → ℂ} (ha : ContDiffAt ℝ 2 a y) (hH : AnalyticAt ℂ H y)
    (hev : a' =ᶠ[𝓝 y] fun z => a z + (H z).re) : hessC a' y = hessC a y := by
  have hb : ContDiffAt ℝ 2 (fun z => (H z).re) y :=
    Complex.reCLM.contDiff.contDiffAt.comp y (hH.contDiffAt.restrict_scalars ℝ)
  have h2 : fderiv ℝ (fderiv ℝ a') y =
      fderiv ℝ (fderiv ℝ a) y + fderiv ℝ (fderiv ℝ fun z => (H z).re) y := by
    have hda : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ a z :=
      (ha.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
    have hdb : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ (fun z => (H z).re) z :=
      (hb.eventually (by simp)).mono fun z hz => hz.differentiableAt (by norm_num)
    have h1 : fderiv ℝ a' =ᶠ[𝓝 y] fun z => fderiv ℝ a z + fderiv ℝ (fun z => (H z).re) z := by
      filter_upwards [hev.eventuallyEq_nhds, hda, hdb] with z hz hza hzb
      rw [hz.fderiv_eq]
      exact fderiv_add hza hzb
    rw [h1.fderiv_eq]
    exact fderiv_add ((ha.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
      ((hb.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num))
  have h0 := hessC_re_eq_zero hH
  rw [← add_zero (hessC a y), ← h0]
  ext i j
  simp only [hessC, Matrix.add_apply, h2, _root_.add_apply]
  push_cast
  ring

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem locDens_eq_of_samePot (A : FinHolAtlas e X) {U : Set X} {P Q : Fin e → LocPot X}
    (hPQ : ∀ i, SamePot A U (P i) (Q i)) (hC : ∀ i, ∀ x ∈ U, IsTwiceDifferentiableAt A (Q i) x) (j : Fin A.n)
    {y : Fin e → ℂ} (hy : y ∈ (A.chart j).target) (hU : (A.chart j).symm y ∈ U) :
    locDens A P j y = locDens A Q j y := by
  have key : ∀ i, hessC (fun y' => (P i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y =
      hessC (fun y' => (Q i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
    intro i
    obtain ⟨V, hVo, hxV, G, hG, hPQV⟩ := hPQ i _ hU
    have hsrc : (A.chart j).symm y ∈ (A.chart j).source := (A.chart j).map_target hy
    have ha : ContDiffAt ℝ 2 (fun y' => (Q i).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
      have h := hC i _ hU j hsrc
      rw [(A.chart j).right_inv hy] at h
      exact h
    have hH : AnalyticAt ℂ (fun y' => G ((A.chart j).symm y')) y := hG j y ⟨hy, hxV⟩
    refine hessC_eq_of_eventuallyEq_add_re ha hH ?_
    have hV : (A.chart j).symm ⁻¹' V ∈ 𝓝 y :=
      ((A.chart j).continuousAt_symm hy).preimage_mem_nhds (hVo.mem_nhds hxV)
    filter_upwards [hV] with z hz
    exact sub_eq_iff_eq_add'.mp (hPQV _ hz)
  simp only [locDens, maDens, key]

end SamePotInt

theorem mInt_congr_samePot : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas e X) (U : Set X) (P Q : Fin e → LocPot X) (g g' : X → ℝ), IsNull A Uᶜ →
    (∀ i, SamePot A U (P i) (Q i)) → (∀ i, ∀ x ∈ U, IsTwiceDifferentiableAt A (Q i) x) → (∀ x ∈ U, g x = g' x) →
    mInt A P g = mInt A Q g' ∧ (MIntegrable A P g ↔ MIntegrable A Q g') := by
  intro e X _ _ _ A U P Q g g' hN hPQ hC hg
  have hpt : ∀ (j : Fin A.n) (y : Fin e → ℂ), y ∈ (A.chart j).target → (A.chart j).symm y ∈ U →
      g ((A.chart j).symm y) = g' ((A.chart j).symm y) ∧ locDens A P j y = locDens A Q j y :=
    fun j y hy hU => ⟨hg _ hU, SamePotInt.locDens_eq_of_samePot A hPQ hC j hy hU⟩
  have hae : ∀ (j : Fin A.n), ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin e → ℂ)),
      y ∈ (A.chart j).target → (A.chart j).symm y ∈ U := by
    intro j
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (hN j)
    intro y hy
    simp only [Set.mem_ofPred_eq, Classical.not_imp] at hy
    exact ⟨hy.1, hy.2⟩
  constructor
  · by_cases h : Nonempty (ChartPartition A)
    · simp only [mInt, dif_pos h, integralWith]
      refine Finset.sum_congr rfl fun j _ => ?_
      refine MeasureTheory.setIntegral_congr_ae (A.chart j).open_target.measurableSet ?_
      filter_upwards [hae j] with y hy hyt
      obtain ⟨h1, h2⟩ := hpt j y hyt (hy hyt)
      simp only [h1, h2]
    · simp only [mInt, dif_neg h]
  · unfold MIntegrable
    refine forall_congr' fun j => forall_congr' fun K => forall_congr' fun hK =>
      forall_congr' fun hKc => ?_
    refine MeasureTheory.integrableOn_congr_fun_ae ?_
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' hKc.isClosed.measurableSet]
    filter_upwards [hae j] with y hy hyK
    obtain ⟨h1, h2⟩ := hpt j y (hK hyK) (hy (hK hyK))
    simp only [h1, h2]

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MongeAmpereIntegralCongrPotentialsStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monge_ampere_integral_congr_potentials : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (U : Set X) (P Q : Fin e → LocPot X) (g g' : X → ℝ), IsNull A Uᶜ → (∀ i, SamePot A U (P i) (Q i)) → (∀ i, ∀ x ∈ U, IsTwiceDifferentiableAt A (Q i) x) → (∀ x ∈ U, g x = g' x) → mInt A P g = mInt A Q g' ∧ (MIntegrable A P g ↔ MIntegrable A Q g') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.mInt_congr_samePot | exact GlobalTheory.CompanionTheory.Ar.PB.mInt_congr_samePot | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.mInt_congr_samePot <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionBoundaryClosedAndCodense
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionBoundaryClosedAndCodense
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Bdry

theorem bdry_isClosed_dense_compl (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X)
    (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X)
    (hs : IsSection A L s) (hn : IsSNC A L s m W) : IsClosed (bdry s) ∧ Dense (bdry s)ᶜ := by
  have key := GlobalTheory.T.snc_boundary_coordinate_chart e X A L s nb m W hs hn
  constructor
  · rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro y hy
    obtain ⟨ψ, -, hyψ, S, hS⟩ := key y
    have hopen : IsOpen (ψ.source ∩ ψ ⁻¹' {z : Fin e → ℂ | ∀ i ∈ S, z i ≠ 0}) := by
      apply ψ.continuousOn.isOpen_inter_preimage ψ.open_source
      have : {z : Fin e → ℂ | ∀ i ∈ S, z i ≠ 0} = ⋂ i ∈ S, {z : Fin e → ℂ | z i ≠ 0} := by
        ext z; simp
      rw [this]
      exact isOpen_biInter_finset fun i _ =>
        isOpen_ne_fun (continuous_apply i) continuous_const
    have hmem : y ∈ ψ.source ∩ ψ ⁻¹' {z : Fin e → ℂ | ∀ i ∈ S, z i ≠ 0} := by
      refine ⟨hyψ, fun i hi h0 => hy ((hS y hyψ).2 ⟨i, hi, h0⟩)⟩
    refine Filter.mem_of_superset (hopen.mem_nhds hmem) ?_
    rintro y' ⟨h1, h2⟩ hb
    obtain ⟨i, hi, h0⟩ := (hS y' h1).1 hb
    exact h2 i hi h0
  · rw [dense_iff_inter_open]
    intro V hV ⟨x, hx⟩
    obtain ⟨ψ, -, hxψ, S, hS⟩ := key x
    have hsub : V ∩ ψ.source ⊆ ψ.source := Set.inter_subset_right
    have himg : IsOpen (ψ '' (V ∩ ψ.source)) :=
      ψ.isOpen_image_of_subset_source (hV.inter ψ.open_source) hsub
    have hne : (ψ '' (V ∩ ψ.source)).Nonempty := ⟨ψ x, x, ⟨hx, hxψ⟩, rfl⟩
    obtain ⟨z, hz, hz0⟩ := (GlobalTheory.T.dense_coordinate_torus e).inter_open_nonempty _ himg hne
    obtain ⟨y, ⟨hyV, hyψ⟩, rfl⟩ := hz
    refine ⟨y, hyV, fun hb => ?_⟩
    obtain ⟨i, -, h0⟩ := (hS y hyψ).1 hb
    exact hz0 i h0

end GlobalTheory.CompanionTheory.Ar.Bdry
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SectionBoundaryClosedAndCodenseStatement
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.section_boundary_closed_and_codense : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (L : LocPot X) (s : X → X → ℂ) (nb : ℕ) (m : Fin nb → ℕ) (W : Fin nb → Set X), IsSection A L s → IsSNC A L s m W → IsClosed (bdry s) ∧ Dense (bdry s)ᶜ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Bdry.bdry_isClosed_dense_compl | exact GlobalTheory.CompanionTheory.Ar.Bdry.bdry_isClosed_dense_compl | (intros; apply GlobalTheory.CompanionTheory.Ar.Bdry.bdry_isClosed_dense_compl <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.MixedDiscriminantCofactorExpansionStatement
section -- merged from Development.WeilBound.CoreStatements.PluriharmonicCharts.XFibMdisc
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

namespace PositivityTheory.Xgp.fib_mdisc

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Matrix

theorem fac_cancel (n : ℕ) (S : ℂ) : (n.factorial : ℂ) * ((1 / (n.factorial : ℂ)) * S) = S := by
  rw [← mul_assoc, mul_one_div_cancel (by exact_mod_cast n.factorial_ne_zero), one_mul]

theorem det_block {d : ℕ} (c : ℂ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (h0 : M 0 0 = c) (hcol : ∀ i : Fin d, M i.succ 0 = 0) :
    M.det = c * (M.submatrix Fin.succ Fin.succ).det := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [h0, hcol]

noncomputable def phi {d : ℕ} (x : Fin (d + 1) × Equiv.Perm (Fin d)) : Equiv.Perm (Fin (d + 1)) :=
  x.1.cycleRange.symm * Equiv.Perm.decomposeFin.symm (0, x.2)

theorem phi_zero {d : ℕ} (x : Fin (d + 1) × Equiv.Perm (Fin d)) : phi x 0 = x.1 := by
  simp [phi, Equiv.Perm.decomposeFin_symm_apply_zero, Fin.cycleRange_symm_zero]

theorem phi_succ {d : ℕ} (x : Fin (d + 1) × Equiv.Perm (Fin d)) (j : Fin d) :
    phi x j.succ = x.1.succAbove (x.2 j) := by
  simp [phi, Equiv.Perm.decomposeFin_symm_apply_succ, Fin.cycleRange_symm_succ]

theorem phi_bijective (d : ℕ) : Function.Bijective (phi (d := d)) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, ?_⟩
  · rintro ⟨r, τ⟩ ⟨r', τ'⟩ h
    have h0 : r = r' := by
      have := congrArg (fun σ : Equiv.Perm (Fin (d + 1)) => σ 0) h
      simpa [phi_zero] using this
    subst h0
    have h1 : Equiv.Perm.decomposeFin.symm ((0 : Fin (d + 1)), τ) =
        Equiv.Perm.decomposeFin.symm ((0 : Fin (d + 1)), τ') := mul_left_cancel h
    have := Equiv.Perm.decomposeFin.symm.injective h1
    simp only [Prod.mk.injEq, true_and] at this
    rw [this]
  · simp [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin, Nat.factorial_succ]

theorem part1 (d : ℕ) (f : Fin (d + 1) → ℂ) (Bm : Fin (d + 1) → Matrix (Fin d) (Fin d) ℂ) :
    ((d + 1).factorial : ℂ) * mdisc (fun r => Matrix.of fun p q : Fin (d + 1) =>
      Fin.cases (Fin.cases (f r) (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => Bm r p' q') q) p) =
      ∑ r, f r * ((d.factorial : ℂ) * mdisc fun s => Bm (r.succAbove s)) := by
  classical
  simp only [mdisc_eq_sum_perm, fac_cancel]
  have hterm : ∀ σ : Equiv.Perm (Fin (d + 1)),
      (Matrix.of fun i j => (Matrix.of fun p q : Fin (d + 1) =>
        Fin.cases (Fin.cases (f (σ j)) (fun _ => 0) q)
          (fun p' => Fin.cases 0 (fun q' => Bm (σ j) p' q') q) p : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) i j).det =
        f (σ 0) * (Matrix.of fun i j => Bm (σ j.succ) i j).det := by
    intro σ
    rw [det_block (f (σ 0))]
    · congr 1
    · simp
    · intro i; simp
  simp only [hterm]
  simp only [Finset.mul_sum]
  rw [← Fintype.sum_prod_type']
  symm
  refine Fintype.sum_bijective phi (phi_bijective d) _ _ fun x => ?_
  simp only [phi_zero, phi_succ]

end PositivityTheory.Xgp.fib_mdisc

theorem PositivityTheory.Xgp.t_fib_mdisc : ∀ (d : ℕ), (∀ (f : Fin (d + 1) → ℂ) (Bm : Fin (d + 1) → Matrix (Fin d) (Fin d) ℂ), ((d + 1).factorial : ℂ) * mdisc (fun r => Matrix.of fun p q : Fin (d + 1) => Fin.cases (Fin.cases (f r) (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => Bm r p' q') q) p) = ∑ r, f r * ((d.factorial : ℂ) * mdisc fun s => Bm (r.succAbove s))) ∧ ∃ Λ : MultilinearMap (RingHom.id ℂ) (fun _ : Fin d => Matrix (Fin d) (Fin d) ℂ) ℂ, (∀ Bm, Λ Bm = mdisc Bm) ∧ ∀ (π : Equiv.Perm (Fin d)) Bm, Λ (Bm ∘ π) = Λ Bm := by
  intro d
  refine ⟨PositivityTheory.Xgp.fib_mdisc.part1 d, ?_⟩
  obtain ⟨M, hM⟩ := (by
    show ∃ F : MultilinearMap (RingHom.id ℂ)
        (fun _ : Fin d => Matrix (Fin d) (Fin d) ℂ) ℂ,
        ⇑F = _root_.ReciprocityTheory.AnForm.mdisc
    refine ⟨MultilinearMap.mk' _root_.ReciprocityTheory.AnForm.mdisc
      _root_.ReciprocityTheory.AnForm.A.mdisc_update_add ?_, rfl⟩
    intro A k c B
    simpa only [RingHom.id_apply, smul_eq_mul] using
      (_root_.ReciprocityTheory.AnForm.A.mdisc_update_smul A k c B))
  exact ⟨M, fun Bm => by rw [hM], fun π Bm => by rw [hM, ReciprocityTheory.AnForm.A.mdisc_comp_perm]⟩
end

open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_discriminant_cofactor_expansion : ∀ (d : ℕ), (∀ (f : Fin (d + 1) → ℂ) (Bm : Fin (d + 1) → Matrix (Fin d) (Fin d) ℂ), ((d + 1).factorial : ℂ) * mdisc (fun r => Matrix.of fun p q : Fin (d + 1) => Fin.cases (Fin.cases (f r) (fun _ => 0) q) (fun p' => Fin.cases 0 (fun q' => Bm r p' q') q) p) = ∑ r, f r * ((d.factorial : ℂ) * mdisc fun s => Bm (r.succAbove s))) ∧ ∃ Λ : MultilinearMap (RingHom.id ℂ) (fun _ : Fin d => Matrix (Fin d) (Fin d) ℂ) ℂ, (∀ Bm, Λ Bm = mdisc Bm) ∧ ∀ (π : Equiv.Perm (Fin d)) Bm, Λ (Bm ∘ π) = Λ Bm := by
  have h := PositivityTheory.Xgp.t_fib_mdisc
  exact h
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialLeviFormCell
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialLeviFormCell
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

theorem gramLog_cellMat (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (z : Pairs N → ℂ) :
    gramLog hd m (cellMat N z) = logDetFlag N hd m hm z := by
  let e : Fin m ≃ {a : Fin N // (a : ℕ) < m} :=
    { toFun := fun i => ⟨Fin.castLE hm i, i.2⟩, invFun := fun a => ⟨a.1, a.2⟩,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  have hdet : (gramHead hd m (cellMat N z)).det =
      (((cellMat N z)ᴴ * diagonal (fun k => (hd k : ℂ)) * cellMat N z).submatrix
        (Fin.castLE hm) (Fin.castLE hm)).det := by
    rw [← Matrix.det_submatrix_equiv_self e (gramHead hd m (cellMat N z))]
    rfl
  delta GlobalTheory.CompanionTheory.Ar.PB.gramLog ReciprocityTheory.AnForm.P.logDetFlag
  rw [hdet]

theorem contDiffAt_gramLog_cellMat (N : ℕ) (hd : Fin N → ℝ) (hd0 : ∀ k, hd k ≠ 0) (m : ℕ) (hm : m ≤ N) :
    ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => gramLog hd m (cellMat N z)) 0 := by
  have hE : logDetFlag N hd m hm = fun z => 1 / 2 * Real.log |detGram N hd m hm z| :=
    logDetFlag_eq N hd m hm
  have hf : (fun z : Pairs N → ℂ => gramLog hd m (cellMat N z)) =
      fun z => 1 / 2 * Real.log (detGram N hd m hm z) := by
    funext z
    rw [gramLog_cellMat N hd m hm z, hE]
    simp only [Real.log_abs]
  rw [hf]
  obtain ⟨hC, h0, -⟩ := detGram_deriv N hd m hm
  have hne : detGram N hd m hm 0 ≠ 0 := by
    rw [h0]
    exact Finset.prod_ne_zero_iff.mpr fun a _ => hd0 _
  exact contDiffAt_const.mul (hC.contDiffAt.log hne)

theorem levi_gramLog_cellMat (N : ℕ) (hd : Fin N → ℝ) (hd0 : ∀ k, hd k ≠ 0) (m : ℕ) (hm : m ≤ N)
    (w : Pairs N → ℂ) :
    levi (fun z : Pairs N → ℂ => gramLog hd m (cellMat N z)) 0 w =
      ∑ p : Pairs N, if p.1.1.val < m ∧ m ≤ p.1.2.val then
        hd p.1.2 / (2 * hd p.1.1) * ‖w p‖ ^ 2 else 0 := by
  have hf : (fun z : Pairs N → ℂ => gramLog hd m (cellMat N z)) = logDetFlag N hd m hm := by
    funext z
    exact gramLog_cellMat N hd m hm z
  rw [hf]
  exact homDensity N hd hd0 m hm w

theorem sigForm_ne_zero (N j : ℕ) (k : Fin N) : sigForm N j k ≠ 0 := by
  delta GlobalTheory.CompanionTheory.Ar.PB.sigForm
  split_ifs <;> norm_num

theorem levi_stepPot_cell : ∀ (N j : ℕ), j ≤ N → ∀ (i : Fin N) (w : Pairs N → ℂ),
    let r : Fin N → ℕ := fun a => if (a : ℕ) < N - j then j + a else a - (N - j)
    ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) 0 ∧
      levi (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) 0 w =
        ∑ p : Pairs N, if min (r p.1.1) (r p.1.2) ≤ (i : ℕ) ∧ (i : ℕ) < max (r p.1.1) (r p.1.2)
          then (1 / 2 : ℝ) * ‖w p‖ ^ 2 else 0 := by
  intro N j hj i w
  dsimp only
  have hs := sigForm_ne_zero N j
  have hσ : ∀ k : Fin N, sigForm N j k = if (k : ℕ) < N - j then -1 else 1 := fun k => rfl
  have G : ∀ m, m ≤ N →
      ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => gramLog (sigForm N j) m (cellMat N z)) 0 :=
    fun m hm => contDiffAt_gramLog_cellMat N (sigForm N j) hs m hm
  have Lv : ∀ m, m ≤ N → levi (fun z : Pairs N → ℂ => gramLog (sigForm N j) m (cellMat N z)) 0 w =
      ∑ p : Pairs N, if p.1.1.val < m ∧ m ≤ p.1.2.val then
        sigForm N j p.1.2 / (2 * sigForm N j p.1.1) * ‖w p‖ ^ 2 else 0 :=
    fun m hm => levi_gramLog_cellMat N (sigForm N j) hs m hm w
  have hi := i.2
  by_cases hij : (i : ℕ) + 1 ≤ j
  · have h1 : N - j + ((i : ℕ) + 1) ≤ N := by omega
    have h0 : N - j ≤ N := by omega
    have hfun : (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) = fun z =>
        gramLog (sigForm N j) (N - j + ((i : ℕ) + 1)) (cellMat N z) +
          (-1) * gramLog (sigForm N j) (N - j) (cellMat N z) := by
      funext z
      delta GlobalTheory.CompanionTheory.Ar.PB.stepPot
      rw [if_pos hij]
      ring
    rw [hfun]
    refine ⟨(G _ h1).add (contDiffAt_const.mul (G _ h0)), ?_⟩
    refine (levi_add_smul (f := fun z : Pairs N → ℂ => gramLog (sigForm N j) (N - j + ((i : ℕ) + 1)) (cellMat N z))
      (g := fun z : Pairs N → ℂ => gramLog (sigForm N j) (N - j) (cellMat N z)) (-1) (G _ h1) (G _ h0) w).trans ?_
    rw [Lv _ h1, Lv _ h0, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases p with ⟨⟨a, b⟩, hab⟩
    have hab' : (a : ℕ) < b := hab
    have ha := a.2
    have hb := b.2
    dsimp only
    simp only [hσ]
    split_ifs <;> first | (exfalso; omega) | norm_num | ring
  · have h1 : N - j ≤ N := by omega
    have h2 : (i : ℕ) + 1 - j ≤ N := by omega
    have hN : N ≤ N := le_refl N
    have hfun : (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) = fun z =>
        (gramLog (sigForm N j) N (cellMat N z) + (-1) * gramLog (sigForm N j) (N - j) (cellMat N z)) +
          1 * gramLog (sigForm N j) ((i : ℕ) + 1 - j) (cellMat N z) := by
      funext z
      delta GlobalTheory.CompanionTheory.Ar.PB.stepPot
      rw [if_neg hij]
      ring
    have GA : ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => gramLog (sigForm N j) N (cellMat N z) +
        (-1) * gramLog (sigForm N j) (N - j) (cellMat N z)) 0 :=
      (G _ hN).add (contDiffAt_const.mul (G _ h1))
    rw [hfun]
    refine ⟨GA.add (contDiffAt_const.mul (G _ h2)), ?_⟩
    refine (levi_add_smul (f := fun z : Pairs N → ℂ => gramLog (sigForm N j) N (cellMat N z) +
        (-1) * gramLog (sigForm N j) (N - j) (cellMat N z))
      (g := fun z : Pairs N → ℂ => gramLog (sigForm N j) ((i : ℕ) + 1 - j) (cellMat N z)) 1 GA (G _ h2) w).trans ?_
    rw [levi_add_smul (f := fun z : Pairs N → ℂ => gramLog (sigForm N j) N (cellMat N z))
      (g := fun z : Pairs N → ℂ => gramLog (sigForm N j) (N - j) (cellMat N z)) (-1) (G _ hN) (G _ h1) w]
    rw [Lv _ hN, Lv _ h1, Lv _ h2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases p with ⟨⟨a, b⟩, hab⟩
    have hab' : (a : ℕ) < b := hab
    have ha := a.2
    have hb := b.2
    dsimp only
    simp only [hσ]
    split_ifs <;> first | (exfalso; omega) | norm_num | ring

end GlobalTheory.CompanionTheory.Ar.PB
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagPotentialLeviFormCellStatement
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_potential_levi_form_cell :
    ∀ (N j : ℕ), j ≤ N → ∀ (i : Fin N) (w : Pairs N → ℂ),
    let r : Fin N → ℕ := fun a => if (a : ℕ) < N - j then j + a else a - (N - j)
    ContDiffAt ℝ 2 (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) 0 ∧
      levi (fun z : Pairs N → ℂ => stepPot N j i (cellMat N z)) 0 w =
        ∑ p : Pairs N, if min (r p.1.1) (r p.1.2) ≤ (i : ℕ) ∧ (i : ℕ) < max (r p.1.1) (r p.1.2)
          then (1 / 2 : ℝ) * ‖w p‖ ^ 2 else 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.levi_stepPot_cell | exact GlobalTheory.CompanionTheory.Ar.PB.levi_stepPot_cell | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.levi_stepPot_cell <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothInCompatibleChart
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothInCompatibleChart
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Metric

theorem contDiffAt_comp_compatChart_symm :
    ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X)
      (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (U : Set X) (g : X → ℝ),
      IsCompatChart A ψ → IsOpen U → A.SmoothOn U g →
        ∀ z ∈ ψ.target, ψ.symm z ∈ U → ContDiffAt ℝ ∞ (g ∘ ψ.symm) z := by
  intro e X _ A ψ U g hψ hU hg z hz hzU
  obtain ⟨j, hj⟩ := A.cover (ψ.symm z)
  have hτ : ContDiffAt ℝ ∞ (⇑(A.chart j) ∘ ⇑ψ.symm) z :=
    (((hψ j).2 z ⟨hz, hj⟩).contDiffAt).restrict_scalars ℝ
  have hy : (A.chart j) (ψ.symm z) ∈ (A.chart j).target ∩ ⇑(A.chart j).symm ⁻¹' U := by
    refine ⟨(A.chart j).map_source hj, ?_⟩
    show (A.chart j).symm ((A.chart j) (ψ.symm z)) ∈ U
    rw [(A.chart j).left_inv hj]
    exact hzU
  have hgc : ContDiffAt ℝ ∞ (g ∘ ⇑(A.chart j).symm) ((A.chart j) (ψ.symm z)) :=
    (hg j).contDiffAt (((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds hy)
  have hcomp := hgc.comp z hτ
  apply hcomp.congr_of_eventuallyEq
  have hev : ∀ᶠ w in 𝓝 z, ψ.symm w ∈ (A.chart j).source :=
    (ψ.continuousAt_symm hz).preimage_mem_nhds ((A.chart j).open_source.mem_nhds hj)
  filter_upwards [hev] with w hw
  simp only [Function.comp_apply, (A.chart j).left_inv hw]

end GlobalTheory.CompanionTheory.Metric
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothInCompatibleChartStatement
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_in_compatible_chart : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (U : Set X) (g : X → ℝ), IsCompatChart A ψ → IsOpen U → A.SmoothOn U g → ∀ z ∈ ψ.target, ψ.symm z ∈ U → ContDiffAt ℝ ∞ (g ∘ ψ.symm) z := by
  first | exact @GlobalTheory.CompanionTheory.Metric.contDiffAt_comp_compatChart_symm | exact GlobalTheory.CompanionTheory.Metric.contDiffAt_comp_compatChart_symm | (intros; apply GlobalTheory.CompanionTheory.Metric.contDiffAt_comp_compatChart_symm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticAtMobiusDetJacobianEq
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticAtMobiusDetJacobianEq
open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.PB.FibPt

theorem analyticAt_entry_tail {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (z : Fin (d + 1) → ℂ) (p q : Fin 2) :
    AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ => g (Fin.tail z') p q) z := by
  have hT : AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ => (Fin.tail z' : Fin d → ℂ)) z := by
    rw [analyticAt_pi_iff]
    intro i
    exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) i.succ).analyticAt z
  have hA : AnalyticAt ℂ (fun y' => g y' p q) (Fin.tail z) :=
    ReciprocityTheory.AnForm.Osgood.osgood d Set.univ _ isOpen_univ (hg p q).differentiableOn _ (Set.mem_univ _)
  exact hA.comp hT

theorem analyticAt_mobius_first {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (z : Fin (d + 1) → ℂ)
    (h : den (g (Fin.tail z)) (z 0) ≠ 0) : AnalyticAt ℂ (mob1 g) z := by
  have hc0 : AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ => z' 0) z :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) 0).analyticAt z
  have e := analyticAt_entry_tail g hg z
  have hnum : AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ =>
      g (Fin.tail z') 1 0 + g (Fin.tail z') 1 1 * z' 0) z := (e 1 0).add ((e 1 1).mul hc0)
  have hden : AnalyticAt ℂ (fun z' : Fin (d + 1) → ℂ => den (g (Fin.tail z')) (z' 0)) z :=
    (e 0 0).add ((e 0 1).mul hc0)
  rw [analyticAt_pi_iff]
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hnum.div hden h
  · exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) j.succ).analyticAt z

theorem hasDerivAt_mob_shift (m : Matrix (Fin 2) (Fin 2) ℂ) (a : ℂ) (h : den m a ≠ 0) :
    HasDerivAt (fun t : ℂ => mob m (a + t)) (mobD m a) 0 := by
  have hl : HasDerivAt (fun t : ℂ => a + t) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).const_add a
  have hn : HasDerivAt (fun t : ℂ => m 1 0 + m 1 1 * (a + t)) (m 1 1 * 1) 0 :=
    (hl.const_mul (m 1 1)).const_add (m 1 0)
  have hd : HasDerivAt (fun t : ℂ => den m (a + t)) (m 0 1 * 1) 0 :=
    (hl.const_mul (m 0 1)).const_add (m 0 0)
  have h0 : den m (a + 0) ≠ 0 := by simpa using h
  have hq := hn.div hd h0
  have e1 : (m 1 1 * 1 * den m (a + 0) - (m 1 0 + m 1 1 * (a + 0)) * (m 0 1 * 1)) / den m (a + 0) ^ 2 =
      mobD m a := by
    simp only [add_zero, mobD, Matrix.det_fin_two]
    congr 1
    simp only [den]
    ring
  rw [e1] at hq
  exact hq

theorem det_jacobian_mobius_first {d : ℕ} (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ)
    (hg : ∀ p q, Differentiable ℂ fun y' => g y' p q) (y : Fin d → ℂ) (a : ℂ)
    (h : den (g y) a ≠ 0) :
    (ReciprocityTheory.AnForm.A.jacC (mob1 g) (Fin.cons a y : Fin (d + 1) → ℂ)).det = mobD (g y) a := by
  set z : Fin (d + 1) → ℂ := Fin.cons a y with hz
  have htail : (Fin.tail z : Fin d → ℂ) = y := Fin.tail_cons _ _
  have hz0 : z 0 = a := Fin.cons_zero _ _
  have hF : HasFDerivAt (mob1 g) (fderiv ℂ (mob1 g) z) z :=
    (analyticAt_mobius_first g hg z (by rwa [htail, hz0])).differentiableAt.hasFDerivAt

  have hrow : ∀ (i : Fin d) (v : Fin (d + 1) → ℂ), fderiv ℂ (mob1 g) z v i.succ = v i.succ := by
    intro i v
    have h1 := (hasFDerivAt_pi'.1 hF) i.succ
    have h2 : HasFDerivAt (fun z' : Fin (d + 1) → ℂ => mob1 g z' i.succ)
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) i.succ) z :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (d + 1) => ℂ) i.succ).hasFDerivAt
    exact DFunLike.congr_fun (h1.unique h2) v

  have hcorner : fderiv ℂ (mob1 g) z (Pi.single 0 1) 0 = mobD (g y) a := by
    have hc : HasDerivAt (fun t : ℂ => z + t • (Pi.single 0 1 : Fin (d + 1) → ℂ))
        (Pi.single 0 1) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const (Pi.single 0 1 : Fin (d + 1) → ℂ)).const_add z
    have hF' : HasFDerivAt (mob1 g) (fderiv ℂ (mob1 g) z)
        (z + (0 : ℂ) • (Pi.single 0 1 : Fin (d + 1) → ℂ)) := by simpa using hF
    have hcomp := hF'.comp_hasDerivAt (0 : ℂ) hc
    have h0 := (hasDerivAt_pi.1 hcomp) 0
    have hline : ∀ t : ℂ, (mob1 g ∘ fun t : ℂ => z + t • (Pi.single 0 1 : Fin (d + 1) → ℂ)) t 0 =
        mob (g y) (a + t) := by
      intro t
      have ht : (Fin.tail (z + t • (Pi.single 0 1 : Fin (d + 1) → ℂ)) : Fin d → ℂ) = y := by
        rw [← htail]
        funext i
        simp [Fin.tail, Pi.single_apply, Fin.succ_ne_zero]
      simp only [Function.comp, mob1, Fin.cons_zero, ht]
      simp [hz0]
    have h3 : HasDerivAt (fun t : ℂ => (mob1 g ∘ fun t : ℂ => z + t • (Pi.single 0 1 : Fin (d + 1) → ℂ)) t 0)
        (mobD (g y) a) 0 := by
      simpa only [hline] using hasDerivAt_mob_shift (g y) a h
    exact h0.unique h3
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hz1 : ∀ i : Fin d, ReciprocityTheory.AnForm.A.jacC (mob1 g) z i.succ 0 = 0 := by
    intro i
    simp [ReciprocityTheory.AnForm.A.jacC, hrow, Pi.single_apply, Fin.succ_ne_zero]
  have hminor : (ReciprocityTheory.AnForm.A.jacC (mob1 g) z).submatrix (Fin.succAbove 0) Fin.succ = 1 := by
    ext i j
    simp [ReciprocityTheory.AnForm.A.jacC, hrow, Pi.single_apply, Matrix.one_apply, Fin.succ_inj]
  simp only [hz1, hminor]
  simp [ReciprocityTheory.AnForm.A.jacC, hcorner]

theorem analyticAt_mobius_and_det_jacobian : ∀ (d : ℕ) (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ),
    (∀ p q, Differentiable ℂ fun y' => g y' p q) → ∀ (y : Fin d → ℂ) (a : ℂ),
    GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a ≠ 0 →
    AnalyticAt ℂ (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob1 g) (Fin.cons a y) ∧
      (ReciprocityTheory.AnForm.A.jacC (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob1 g) (Fin.cons a y)).det =
        GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a := by
  intro d g hg y a h
  refine ⟨analyticAt_mobius_first g hg _ ?_, det_jacobian_mobius_first g hg y a h⟩
  rwa [Fin.tail_cons, Fin.cons_zero]

end GlobalTheory.CompanionTheory.Ar.PB.FibPt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticAtMobiusDetJacobianEqStatement
open MeasureTheory Filter Topology Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.analyticAt_mobius_det_jacobian_eq : ∀ (d : ℕ) (g : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ), (∀ p q, Differentiable ℂ fun y' => g y' p q) → ∀ (y : Fin d → ℂ) (a : ℂ), GlobalTheory.CompanionTheory.Ar.PB.FibPt.den (g y) a ≠ 0 → AnalyticAt ℂ (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob1 g) (Fin.cons a y) ∧ (ReciprocityTheory.AnForm.A.jacC (GlobalTheory.CompanionTheory.Ar.PB.FibPt.mob1 g) (Fin.cons a y)).det = GlobalTheory.CompanionTheory.Ar.PB.FibPt.mobD (g y) a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FibPt.analyticAt_mobius_and_det_jacobian | exact GlobalTheory.CompanionTheory.Ar.PB.FibPt.analyticAt_mobius_and_det_jacobian | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FibPt.analyticAt_mobius_and_det_jacobian <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistIsPrime
section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistIsPrime
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw

namespace GlobalTheory.CompanionTheory.Ar.Tw

theorem exists_root_field {D : Type} [CommRing D] [IsDomain D] (p : ℕ)
    (h : ∀ a b : D, a ^ 2 + (p : D) * b ^ 2 = 0 → b = 0) :
    ∃ (E : Type) (_ : Field E) (i : D →+* E) (s : E), s ^ 2 = -(p : E) ∧
      ∀ u v : D, i u + i v * s = 0 → u = 0 ∧ v = 0 := by
  classical
  let F := FractionRing D
  let g : Polynomial F := Polynomial.X ^ 2 + Polynomial.C (p : F)
  have hmonic : g.Monic := Polynomial.monic_X_pow_add_C _ (by norm_num)
  have hdeg : g.natDegree = 2 := Polynomial.natDegree_X_pow_add_C
  have hinjF : Function.Injective (algebraMap D F) := IsFractionRing.injective D F
  have hnr : ∀ r : F, r ^ 2 + (p : F) ≠ 0 := by
    intro r hr
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := D) r
    have hb0 : algebraMap D F b ≠ 0 := by
      intro h0
      exact nonZeroDivisors.ne_zero hb (hinjF (by simpa using h0))
    have h1 : algebraMap D F (a ^ 2 + (p : D) * b ^ 2) = 0 := by
      simp only [map_add (f := _), map_mul, map_pow, map_natCast]
      have e : algebraMap D F a ^ 2 + (p : F) * algebraMap D F b ^ 2 =
          ((algebraMap D F a / algebraMap D F b) ^ 2 + (p : F)) * algebraMap D F b ^ 2 := by
        rw [div_pow, add_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hb0)]
      rw [e, hr, zero_mul]
    have h2 : a ^ 2 + (p : D) * b ^ 2 = 0 := hinjF (by simpa using h1)
    exact hb0 (by rw [h a b h2, map_zero])
  have hirr : Irreducible g := by
    rw [hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega)]
    refine Multiset.eq_zero_of_forall_notMem fun r hr => ?_
    have := (Polynomial.mem_roots'.mp hr).2
    simp [g, Polynomial.IsRoot] at this
    exact hnr r this
  haveI : Fact (Irreducible g) := ⟨hirr⟩
  refine ⟨AdjoinRoot g, inferInstance, (AdjoinRoot.of g).comp (algebraMap D F), AdjoinRoot.root g, ?_, ?_⟩
  · have h0 : AdjoinRoot.mk g (Polynomial.X ^ 2 + Polynomial.C (p : F)) = 0 := AdjoinRoot.mk_self
    rw [map_add (f := _), map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, map_natCast] at h0
    linear_combination h0
  · intro u v huv
    have h1 : AdjoinRoot.mk g (Polynomial.C (algebraMap D F u) +
        Polynomial.C (algebraMap D F v) * Polynomial.X) = 0 := by
      simpa using huv
    rw [AdjoinRoot.mk_eq_zero] at h1
    have h2 := Polynomial.eq_zero_of_dvd_of_degree_lt h1 (by
      rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hdeg]
      compute_degree
      exact_mod_cast (by norm_num : 1 < 2))
    have hu := congrArg (fun t => _root_.AddMonoidAlgebra.coeff (M := ℕ) t 0) h2
    have hv := congrArg (fun t => _root_.AddMonoidAlgebra.coeff (M := ℕ) t 1) h2
    simp at hu hv
    exact ⟨hu, hv⟩

theorem twist_isPrime (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ)
    (W : Ideal (MRing ι)) (hW : W.IsPrime) (hN : NoRoot p W) : (twist p W).IsPrime := by
  classical
  haveI : IsDomain (MRing ι ⧸ W) := Ideal.Quotient.isDomain W
  have hD : ∀ a b : MRing ι ⧸ W, a ^ 2 + (p : MRing ι ⧸ W) * b ^ 2 = 0 → b = 0 := by
    intro a b h
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.Quotient.eq_zero_iff_mem]
    apply hN a
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa using h
  obtain ⟨E, _, i, s, hs, hind⟩ := exists_root_field p hD
  let φ : MRing (Tb ι) →+* Polynomial E :=
    (aeval (fun q : Σ o, Tb ι o => match q with
      | ⟨none, j⟩ => if j = (0 : Fin 2) then Polynomial.C s * Polynomial.X else Polynomial.X
      | ⟨some k, l⟩ => Polynomial.C (i (Ideal.Quotient.mk W (X ⟨k, l⟩)))) :
        MRing (Tb ι) →ₐ[ℤ] Polynomial E).toRingHom
  have hinc : ∀ f : MRing ι, φ (inc f) = Polynomial.C (i (Ideal.Quotient.mk W f)) := by
    intro f
    have : (φ.comp inc) = (Polynomial.C.comp (i.comp (Ideal.Quotient.mk W))) := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp [φ, inc]
      · intro l; simp [φ, inc, oldIdx]
    exact congrArg (fun g => g f) this
  have hx : φ xN = Polynomial.C s * Polynomial.X := by
    simp only [φ, xN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
    exact if_pos rfl
  have hy : φ yN = Polynomial.X := by
    simp only [φ, yN, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
    exact if_neg (show ¬ ((1 : Fin 2) = 0) by decide)
  have hCp : φ (C (p : ℤ)) = (p : Polynomial E) := by
    simp [φ]
  have hle : twist p W ≤ RingHom.ker φ := by
    refine sup_le (Ideal.map_le_iff_le_comap.mpr fun f hf => ?_) ?_
    · rw [Ideal.mem_comap, RingHom.mem_ker, hinc, Ideal.Quotient.eq_zero_iff_mem.mpr hf]
      simp
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      show quad p ∈ RingHom.ker φ
      rw [RingHom.mem_ker]
      simp only [quad, map_add (f := _), map_mul, map_pow, hx, hy, hCp]
      have hs' : (Polynomial.C s) ^ 2 = -(p : Polynomial E) := by
        rw [← map_pow, hs]; simp
      linear_combination (Polynomial.X ^ 2 : Polynomial E) * hs'
  let φ' : (MRing (Tb ι) ⧸ twist p W) →+* Polynomial E :=
    Ideal.Quotient.lift _ φ (fun a ha => hle ha)
  let mk' := Ideal.Quotient.mk (twist p W)
  have hWle : ∀ a ∈ W, (mk'.comp inc) a = 0 := by
    intro a ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))
  let τ : (MRing ι ⧸ W) →+* (MRing (Tb ι) ⧸ twist p W) :=
    Ideal.Quotient.lift W (mk'.comp inc) hWle
  let σ : Polynomial (MRing ι ⧸ W) →+* (MRing (Tb ι) ⧸ twist p W) :=
    Polynomial.eval₂RingHom τ (mk' yN)
  have hσC : ∀ d, σ (Polynomial.C d) = τ d := fun d => by simp [σ]
  have hσX : σ Polynomial.X = mk' yN := by simp [σ]
  have hxx : mk' xN * mk' xN = σ (-(p : Polynomial (MRing ι ⧸ W)) * Polynomial.X ^ 2) := by
    have hq : mk' (quad p) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    simp only [quad, map_add (f := _), map_mul, map_pow] at hq
    have hc : mk' (C (p : ℤ)) = (p : MRing (Tb ι) ⧸ twist p W) := by simp [mk']
    rw [hc] at hq
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
      simp only [map_mul σ, map_neg σ, map_natCast σ, map_pow σ, hσX]
    linear_combination hq
  have hform : ∀ f : MRing (Tb ι), ∃ a b : Polynomial (MRing ι ⧸ W),
      mk' f = σ a + σ b * mk' xN := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C n =>
      refine ⟨(n : Polynomial (MRing ι ⧸ W)), 0, ?_⟩
      simp [mk']
    | add f g hf hg =>
      obtain ⟨a, b, h1⟩ := hf
      obtain ⟨a', b', h2⟩ := hg
      exact ⟨a + a', b + b', by set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
        rw [map_add mk', h1, h2, map_add σ, map_add σ]; ring⟩
    | mul_X f q hf =>
      obtain ⟨a, b, h1⟩ := hf
      rw [map_mul, h1]
      obtain ⟨o, l⟩ := q
      cases o with
      | none =>
        have aux : ∀ l : Fin 2, (X (⟨none, l⟩ : Σ o, Tb ι o) : MRing (Tb ι)) = xN ∨
            (X (⟨none, l⟩ : Σ o, Tb ι o) : MRing (Tb ι)) = yN := by
          intro l
          fin_cases l
          · exact Or.inl rfl
          · exact Or.inr rfl
        rcases aux l with hl | hl
        · rw [hl]
          refine ⟨b * (-(p : Polynomial (MRing ι ⧸ W)) * Polynomial.X ^ 2), a, ?_⟩
          rw [map_mul σ b, ← hxx]
          ring
        · rw [hl]
          refine ⟨a * Polynomial.X, b * Polynomial.X, ?_⟩
          rw [map_mul, map_mul, hσX]
          ring
      | some k =>
        refine ⟨a * Polynomial.C (Ideal.Quotient.mk W (X ⟨k, l⟩)),
          b * Polynomial.C (Ideal.Quotient.mk W (X ⟨k, l⟩)), ?_⟩
        have hτ : τ (Ideal.Quotient.mk W (X ⟨k, l⟩)) = mk' (X ⟨some k, l⟩) := by
          rw [show τ (Ideal.Quotient.mk W (X ⟨k, l⟩)) = mk' (inc (X ⟨k, l⟩)) from Ideal.Quotient.lift_mk _ _ _]
          simp [inc, oldIdx]
        rw [map_mul, map_mul, hσC, hτ]
        ring
  have hφ' : ∀ f, φ' (mk' f) = φ f := fun f => Ideal.Quotient.lift_mk _ _ _
  have hτ' : ∀ d, τ (Ideal.Quotient.mk W d) = mk' (inc d) := fun d => Ideal.Quotient.lift_mk _ _ _
  have hσ : ∀ a, φ' (σ a) = a.map (i : (MRing ι ⧸ W) →+* E) := by
    have : (φ'.comp σ) = Polynomial.mapRingHom i := by
      apply Polynomial.ringHom_ext
      · intro d
        obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective d
        show φ' (σ (Polynomial.C _)) = (Polynomial.C _).map i
        rw [hσC, hτ', hφ', hinc, Polynomial.map_C]
      · show φ' (σ Polynomial.X) = Polynomial.X.map i
        rw [hσX, hφ', hy, Polynomial.map_X]
    exact fun a => congrArg (fun g => g a) this
  have hφx : φ' (mk' xN) = Polynomial.C s * Polynomial.X := by
    rw [hφ', hx]
  have hinj : Function.Injective φ' := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro q hq
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨a, b, h1⟩ := hform f
    change φ' (mk' f) = 0 at hq
    change mk' f = 0
    rw [h1] at hq ⊢
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
      rw [map_add φ', map_mul φ', hσ, hσ, hφx] at hq
    have hcoef : ∀ n, (a.coeff (n + 1) = 0 ∧ b.coeff n = 0) := by
      intro n
      have := congrArg (fun t => _root_.AddMonoidAlgebra.coeff (M := ℕ) t (n + 1)) hq
      simp only [Polynomial.coeff_add, Polynomial.coeff_map, Polynomial.coeff_zero] at this
      have e : (Polynomial.map i b * (Polynomial.C s * Polynomial.X)).coeff (n + 1) =
          i (b.coeff n) * s := by
        rw [← mul_assoc, Polynomial.coeff_mul_X, mul_comm, Polynomial.coeff_C_mul,
          Polynomial.coeff_map, mul_comm]
      rw [e] at this
      exact hind _ _ this
    have ha0 : a.coeff 0 = 0 := by
      have := congrArg (fun t => _root_.AddMonoidAlgebra.coeff (M := ℕ) t 0) hq
      simp only [Polynomial.coeff_add, Polynomial.coeff_map, Polynomial.coeff_zero] at this
      have e : (Polynomial.map i b * (Polynomial.C s * Polynomial.X)).coeff 0 = 0 := by
        rw [← mul_assoc, Polynomial.coeff_mul_X_zero]
      rw [e, add_zero] at this
      have h3 := hind (a.coeff 0) 0 (by simpa using this)
      exact h3.1
    have ha : a = 0 := by
      ext n
      cases n with
      | zero => simpa using ha0
      | succ n => simpa using (hcoef n).1
    have hb : b = 0 := by
      ext n
      simpa using (hcoef n).2
    rw [ha, hb]; simp
  haveI : IsDomain (MRing (Tb ι) ⧸ twist p W) := hinj.isDomain φ'
  exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

end GlobalTheory.CompanionTheory.Ar.Tw
end

section -- merged from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistIsPrimeStatement
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo MeasureTheory GlobalTheory.CompanionTheory.Ar.Tw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_isPrime_of_isPrime_of_noRoot : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (p : ℕ) (W : Ideal (MRing ι)), W.IsPrime → NoRoot p W → (twist p W).IsPrime := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Tw.twist_isPrime | exact GlobalTheory.CompanionTheory.Ar.Tw.twist_isPrime | (intros; apply GlobalTheory.CompanionTheory.Ar.Tw.twist_isPrime <;> assumption)
end
end
