module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.MultivariableReproducingFormula
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MonicNormLtOne

@[expose] public section

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.KernelTraceBoundProof
open scoped ENNReal NNReal

open UpperTheory.Esk in
theorem UpperTheory.Esk.kernel_trace_bound_proof : UpperTheory.Esk.E0d → UpperTheory.Esk.E1 → UpperTheory.Esk.F5 := by
  intro _ hE1 F I Gf ι _ _ _ _ D k a hH
  obtain ⟨C, hC⟩ := hE1 F I Gf ι D k a hH 1 one_pos
  refine ⟨C, fun T hT y => ⟨fun hy γ s hs _ => hy s hs, fun hy => ?_⟩⟩
  simp only [Dat.abelian₂, Set.mem_ofPred_eq, not_forall, not_le] at hy
  obtain ⟨s, hs, hsT⟩ := hy
  calc ∑' γ : PG F, ‖(D.LamF T γ).indicator (D.kk k a γ) y‖ₑ
      ≤ ∑' γ, {γ : PG F | ¬ Fix s γ}.indicator (fun γ => ‖D.kk k a γ y‖ₑ) γ := by
        refine ENNReal.tsum_le_tsum fun γ => ?_
        by_cases hγ : y ∈ D.LamF T γ
        · have hnf : γ ∈ {γ : PG F | ¬ Fix s γ} := fun hf => absurd (hγ s hs hf) (not_le.2 hsT)
          rw [Set.indicator_of_mem hγ, Set.indicator_of_mem hnf]
        · rw [Set.indicator_of_notMem hγ]; simp
    _ = ∑' γ : {γ : PG F // ¬ Fix s γ}, ‖D.kk k a γ.1 y‖ₑ := (tsum_subtype _ _).symm
    _ ≤ C := hC y s hs (le_of_lt (hT.trans hsT))
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfFcen
open Matrix

namespace UpperTheory.Esk.CentralTermsContribution

theorem trace_conj {F : Type} [Field F] (γ δ : GL (Fin 2) F) :
    ((δ * γ * δ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace = (γ : Matrix (Fin 2) (Fin 2) F).trace := by
  simp only [Units.val_mul]
  rw [Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

end UpperTheory.Esk.CentralTermsContribution

theorem UpperTheory.Esk.pf_Fcen : UpperTheory.Esk.Fcen := by
  intro F _ γ δ htr h
  have h' : ((δ * γ * δ⁻¹ : GL (Fin 2) F) : UpperTheory.Esk.PG F) = (γ : UpperTheory.Esk.PG F) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]; exact h
  rw [QuotientGroup.eq] at h'
  set c := (δ * γ * δ⁻¹)⁻¹ * γ with hc
  obtain ⟨h1, h2, h3⟩ := UpperTheory.Esk.center_entries h'
  have hcv : (c : Matrix (Fin 2) (Fin 2) F) = c 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [h1, h2, h3]
  have hγ : γ = (δ * γ * δ⁻¹) * c := by rw [hc]; group
  have hv : (γ : Matrix (Fin 2) (Fin 2) F) = ((δ * γ * δ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (c : Matrix (Fin 2) (Fin 2) F) := by
    conv_lhs => rw [hγ]
    rw [Units.val_mul]
  have htr2 : c 0 0 * (γ : Matrix (Fin 2) (Fin 2) F).trace = 1 * (γ : Matrix (Fin 2) (Fin 2) F).trace := by
    conv_rhs => rw [hv, hcv, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul, smul_eq_mul, UpperTheory.Esk.CentralTermsContribution.trace_conj]
    ring
  have ht : c 0 0 = 1 := mul_right_cancel₀ htr htr2
  have hc1 : c = 1 := by
    ext : 1
    rw [hcv, ht, one_smul, Units.val_one]
  rw [hc1, mul_one] at hγ
  calc δ * γ = δ * γ * δ⁻¹ * δ := by group
    _ = γ * δ := by rw [← hγ]
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfKapSum
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

theorem UpperTheory.Esk.pf_KapSum : UpperTheory.Esk.Pack → UpperTheory.Esk.Mult → UpperTheory.Esk.KapInt → UpperTheory.Esk.KapSum := by
  intro hPack hMult hKap F I Gf _ _ _ D hD k hk c₀ hc₀
  obtain ⟨C₁, hC₁⟩ := hPack F I Gf D hD
  obtain ⟨C₃, A₃, hK⟩ := hKap I k hk
  obtain ⟨C₂, hC₂⟩ := hMult F I Gf D hD (1 / 16) c₀ (by norm_num) hc₀
  refine ⟨(C₁ : ℝ) * A₃ * max C₂ 0 * C₃, ?_⟩
  intro y s hs hy ω' z
  obtain ⟨hfin, hcard⟩ := hC₂ y s hs hy
  obtain ⟨hmeas, hint, -, hnear⟩ := hK z
  have hpos : 0 ≤ 1 + D.HtY s y := by linarith
  have key : ∀ n : ℕ, (n : ℝ) ≤ C₂ * (1 + D.HtY s y) →
      (n : ℝ≥0∞) ≤ ENNReal.ofReal (max C₂ 0 * (1 + D.HtY s y)) := by
    intro n hn
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos))
  have hA : ∀ w w' : D.Xs, Near (1 / 2) w w' →
      ENNReal.ofReal (Kap k z w) ≤ (A₃ : ℝ≥0∞) * ENNReal.ofReal (Kap k z w') := by
    intro w w' hww
    calc ENNReal.ofReal (Kap k z w) ≤ ENNReal.ofReal (A₃ * Kap k z w') :=
          ENNReal.ofReal_le_ofReal (hnear w w' hww).1
      _ = (A₃ : ℝ≥0∞) * ENNReal.ofReal (Kap k z w') := by
          rw [ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
  have hpack := hC₁ y ω' (fun w => ENNReal.ofReal (Kap k z w)) A₃
    (ENNReal.measurable_ofReal.comp hmeas) hA hfin
  refine hpack.trans ((mul_le_mul' (mul_le_mul' le_rfl (key _ hcard)) hint).trans (le_of_eq ?_))
  rw [show (C₁ : ℝ) * A₃ * max C₂ 0 * C₃ * (1 + D.HtY s y)
      = ((C₁ * A₃ * C₃ : ℝ≥0) : ℝ) * (max C₂ 0 * (1 + D.HtY s y)) by push_cast; ring,
    ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal]
  push_cast
  ring
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.SplitTsum
open MeasureTheory

namespace UpperTheory.Esk.CentralTermsContribution

open Classical in
theorem split_tsum {G : Type} (P : G → Prop) (f : G → ℂ) (hf : Summable fun g => ‖f g‖) :
    ∑' g, f g = (∑' g, if P g then f g else 0) + ∑' g, if P g then 0 else f g := by
  have h1 : Summable fun g => if P g then f g else 0 :=
    Summable.of_norm_bounded hf (fun g => by split_ifs <;> simp)
  have h2 : Summable fun g => if P g then 0 else f g :=
    Summable.of_norm_bounded hf (fun g => by split_ifs <;> simp)
  rw [← Summable.tsum_add h1 h2]
  congr 1; funext g; split_ifs <;> simp

end UpperTheory.Esk.CentralTermsContribution

open UpperTheory.Esk in
open Classical in
theorem UpperTheory.Esk.pf_TF : UpperTheory.Esk.E2 → UpperTheory.Esk.Ecut → UpperTheory.Esk.E6 → UpperTheory.Esk.Fell → UpperTheory.Esk.Fhyp → UpperTheory.Esk.TF := by
  intro hE2 hcut hE6 hFell hFhyp F I Gf _ _ _ D hAx ι _ a
  obtain ⟨S, hFam, hS⟩ := hFell F I Gf D hAx ι a
  refine ⟨S, hFam, fun k hH hfd h => ?_⟩
  obtain ⟨⟨b, hb⟩, -⟩ := hcut F I Gf D hAx
  obtain ⟨hi, htr⟩ := hE6 F I Gf ι D k a hH hfd h b hb
  obtain ⟨hie, hge⟩ := hS k hH b hb
  have hsplit : ∀ y, (∑' γ : PG F, D.kk k a γ y) = (∑' γ : PG F, if IsEll γ then D.kk k a γ y else 0) +
      ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y :=
    fun y => CentralTermsContribution.split_tsum _ _ ((hE2 F I Gf ι D k a hH).1 y)
  have hfun : (fun y => b y • ∑' γ : PG F, D.kk k a γ y) = fun y => b y • (∑' γ : PG F, if IsEll γ then D.kk k a γ y else 0) +
      b y • ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y := by
    funext y; rw [hsplit y, smul_add]
  have hih : Integrable (fun y => b y • ∑' γ : PG F, if IsEll γ then 0 else D.kk k a γ y) D.μY := by
    have := hi.sub hie
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]
    rw [hsplit y, smul_add, add_sub_cancel_left]
  have h0 := hFhyp F I Gf ι D k a hH b hb hih
  rw [htr, ← hge, hfun, integral_add hie hih, h0, add_zero]
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.OrbitCoverProof
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace UpperTheory.Esk.OrbitCoverLemmas

variable {G Y : Type} [Group G] [Countable G] [MeasurableSpace Y] [MulAction G Y]


omit [Countable G] [MeasurableSpace Y] in
theorem orbit_tsum_smul (u : Y → ℝ) (g : G) (y : Y) :
    ∑' h : G, u (h • g • y) = ∑' h : G, u (h • y) := by
  simp only [smul_smul]
  exact (Equiv.mulRight g).tsum_eq (fun h => u (h • y))

theorem exists_cut (hm : ∀ g : G, Measurable fun y : Y => g • y) (u : Y → ℝ) (hu : Measurable u)
    (h0 : ∀ y, 0 ≤ u y) (hpos : ∀ y, ∃ g : G, 0 < u (g • y))
    (hs : ∀ y, Summable fun g : G => u (g • y)) : ∃ b : Y → ℝ, IsCut G b := by
  have hsE : (fun y => ∑' g : G, u (g • y)) =
      fun y => (∑' g : G, ENNReal.ofReal (u (g • y))).toReal := by
    funext y
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun g => h0 _) (hs y), ENNReal.toReal_ofReal]
    exact tsum_nonneg fun g => h0 _
  have hsm : Measurable fun y => ∑' g : G, u (g • y) := by
    rw [hsE]
    exact (Measurable.tsum fun g => (hu.comp (hm g)).ennreal_ofReal).ennreal_toReal
  have hspos : ∀ y, 0 < ∑' g : G, u (g • y) := by
    intro y
    obtain ⟨g, hg⟩ := hpos y
    exact lt_of_lt_of_le hg ((hs y).le_tsum g fun h _ => h0 _)
  refine ⟨fun y => u y / ∑' g : G, u (g • y),
    ⟨hu.div hsm, fun y => div_nonneg (h0 y) (hspos y).le, fun y => ?_⟩⟩
  have : (fun g : G => u (g • y) / ∑' h : G, u (h • g • y)) =
      fun g => u (g • y) / ∑' h : G, u (h • y) := by
    funext g; rw [orbit_tsum_smul]
  show HasSum (fun g : G => u (g • y) / ∑' h : G, u (h • g • y)) 1
  rw [this, ← div_self (hspos y).ne']
  exact (hs y).hasSum.div_const _

theorem cover (μ : Measure Y) (hP : Pres G μ) (b : Y → ℝ) (hb : IsCut G b) (S : Set Y)
    (hS : MeasurableSet S) (hc : ∀ y : Y, ∃ g : G, g • y ∈ S) :
    ∫⁻ y, ENNReal.ofReal (b y) ∂μ ≤ μ S :=
  _root_.UpperTheory.Reformulated.B.Qf46.cover μ hP b hb S hS hc

end UpperTheory.Esk.OrbitCoverLemmas

theorem UpperTheory.Esk.orbit_cover_proof : UpperTheory.Esk.C2 := by
  intro G Y _ _ _ _
  exact ⟨fun hm u hu h0 hpos hs => UpperTheory.Esk.OrbitCoverLemmas.exists_cut hm u hu h0 hpos hs,
    fun μ hP b hb S hS hc => UpperTheory.Esk.OrbitCoverLemmas.cover μ hP b hb S hS hc⟩
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.ActionsPreserveMeasuresProof
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.ActionsPreserveMeasuresLemmas

open UpperTheory.Esk

theorem count_pres {α : Type} [MeasurableSpace α] [MeasurableSingletonClass α] [Countable α] (f : α → α)
    (hf : Function.Bijective f) : MeasurePreserving f Measure.count Measure.count := by
  refine ⟨measurable_of_countable f, ?_⟩
  ext s hs
  rw [Measure.map_apply (measurable_of_countable f) hs, Measure.count_apply hs,
    Measure.count_apply ((Set.to_countable _).measurableSet)]
  congr 1
  exact Set.encard_preimage_of_injective_subset_range hf.1 (hf.2.range_eq ▸ Set.subset_univ s)

theorem countable_PG (F : Type) [Field F] [Countable F] : Countable (PG F) := by
  have : Countable (Matrix (Fin 2) (Fin 2) F) := inferInstanceAs (Countable (Fin 2 → Fin 2 → F))
  have : Countable (GL (Fin 2) F) :=
    Function.Injective.countable (f := fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) fun a b h => Units.ext h
  exact QuotientGroup.mk_surjective.countable

theorem smulX {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf) (g : GL (Fin 2) F) (z : D.Xs) :
    ((g : PG F) • z) = (fun v => D.r v g • z v : I → P) := rfl

end UpperTheory.Esk.ActionsPreserveMeasuresLemmas

open UpperTheory.Esk.ActionsPreserveMeasuresLemmas in
theorem UpperTheory.Esk.actions_preserve_measures_proof : UpperTheory.Esk.B1a → UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.E0a := by
  intro h1 h2 h3 F I Gf _ _ _ D ax
  have : SigmaFinite (volume : Measure P) := h1.1
  have : (volume : Measure P).IsOpenPosMeasure := h1.2.1
  have : Countable F := ax.cF
  have hPG : Countable (PG F) := countable_PG F
  have : Countable D.Om := ax.cO
  have : Countable D.Cj := hPG
  have hXs : SigmaFinite (volume : Measure D.Xs) :=
    show SigmaFinite (Measure.pi fun _ : I => (volume : Measure P)) from inferInstance
  have presX : ∀ γ : PG F, MeasurePreserving (fun z : D.Xs => γ • z) volume volume := by
    intro γ
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
    simp only [smulX]
    exact measurePreserving_pi (fun _ : I => (volume : Measure P)) (fun _ : I => (volume : Measure P))
      (fun v => (h1.2.2 (D.r v g)).2)
  have contX : ∀ γ : PG F, Continuous fun z : D.Xs => γ • z := by
    intro γ
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective γ
    simp only [smulX]
    exact continuous_pi fun v => (h1.2.2 (D.r v g)).1.comp (continuous_apply v)
  refine ⟨hPG, hXs, presX, ?_, ?_, contX, inferInstanceAs (BorelSpace (I → P)), ?_⟩
  · intro γ
    exact (count_pres (fun ω : D.Om => γ • ω) (MulAction.bijective γ)).prod (presX γ)
  · intro γ
    exact (count_pres (fun ω : D.Cj × D.Om => γ • ω) (MulAction.bijective γ)).prod (presX γ)
  · intro δ hδ
    have hk : Continuous fun p : P × P => kap p.1 p.2 := h3.2.2.2.2.1
    have hk1 : ∀ z : P, Continuous fun w => kap z w := fun z => hk.comp (continuous_const.prodMk continuous_id)
    set U : Set P := {w | δ < kap iP w} with hU
    have hUo : IsOpen U := isOpen_lt continuous_const (hk1 iP)
    have hUp : 0 < volume U := hUo.measure_pos volume ⟨iP, by
      show δ < kap iP iP
      rw [h3.2.1 iP]; exact hδ⟩
    obtain ⟨c0, hc0, hc0U⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hUp
    have hS : ∀ z : P, MeasurableSet {w | δ ≤ kap z w} := fun z =>
      measurableSet_le measurable_const (hk1 z).measurable
    have hball : ∀ z : P, (c0 : ℝ≥0∞) ≤ volume {w | δ ≤ kap z w} := by
      intro z
      obtain ⟨g, -, -, hg⟩ := h3.2.2.2.2.2 z
      have hf := (h1.2.2 g).2
      have hpre : (fun w : P => g • w) ⁻¹' {w | δ ≤ kap z w} = {w | δ ≤ kap iP w} := by
        ext w
        show δ ≤ kap z (g • w) ↔ δ ≤ kap iP w
        rw [← hg, h2.2.2.2.1 g iP w]
      rw [← hf.measure_preimage (hS z).nullMeasurableSet, hpre]
      refine hc0U.le.trans (measure_mono fun w hw => ?_)
      exact le_of_lt (show δ < kap iP w from hw)
    refine ⟨c0 ^ Fintype.card I, pow_pos (by exact_mod_cast hc0) _, fun z => ?_⟩
    have hset : {w : X I | Near δ z w} = Set.univ.pi fun v => {w | δ ≤ kap (z v) w} := by
      ext w
      simp [Near, Set.mem_pi]
    rw [hset]
    refine ⟨MeasurableSet.univ_pi fun v => hS (z v), ?_⟩
    rw [volume_pi, Measure.pi_pi, ENNReal.coe_pow, ← Finset.card_univ, ← Finset.prod_const]
    exact Finset.prod_le_prod' fun v _ => hball (z v)
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfFsum
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace UpperTheory.Esk.SummedOrbitIntegrals

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]

theorem meas_pair [Countable α] {E : Type*} [MeasurableSpace E] {f : α → β → E} (hf : ∀ a, Measurable (f a)) :
    Measurable (fun q : α × β => f q.1 q.2) := by
  intro s hs
  have e : (fun q : α × β => f q.1 q.2) ⁻¹' s = ⋃ a : α, ({a} : Set α) ×ˢ (f a ⁻¹' s) := by
    ext ⟨a, b⟩
    simp
  rw [e]
  exact MeasurableSet.iUnion fun a => (measurableSet_singleton a).prod (hf a hs)

theorem lint_pair (μ : Measure β) [SFinite μ] (f : α × β → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ q, f q ∂(Measure.count.prod μ) = ∑' a, ∫⁻ y, f (a, y) ∂μ := by
  rw [lintegral_prod f hf.aemeasurable, lintegral_count]

theorem count_prod {A B : Type*} [MeasurableSpace A] [MeasurableSpace B] [Countable A] [Countable B]
    [MeasurableSingletonClass A] [MeasurableSingletonClass B] :
    (Measure.count : Measure A).prod (Measure.count : Measure B) = Measure.count := by
  refine Measure.ext_iff_singleton.2 fun p => ?_
  obtain ⟨a, b⟩ := p
  rw [Measure.count_singleton, ← Set.singleton_prod_singleton, Measure.prod_prod,
    Measure.count_singleton, Measure.count_singleton, one_mul]

end UpperTheory.Esk.SummedOrbitIntegrals

open UpperTheory.Esk.SummedOrbitIntegrals in
theorem UpperTheory.Esk.pf_Fsum : UpperTheory.Esk.E0a → UpperTheory.Esk.Fsum := by
  intro h0 F I Gf _ _ _ D hax
  obtain ⟨hcG, hsig, -⟩ := h0 F I Gf D hax
  haveI : Countable D.Cj := hcG
  haveI : Countable D.Om := hax.cO
  haveI : SigmaFinite (volume : Measure D.Xs) := hsig
  haveI : SFinite D.μY := by unfold UpperTheory.Esk.Dat.μY; infer_instance
  intro b hb
  refine ⟨⟨hb.meas.comp (measurable_fst.snd.prodMk measurable_snd), fun p => hb.nonneg _,
    fun p => hb.sum (p.1.2, p.2)⟩, ?_⟩
  intro u hu hfin
  have hgm : Measurable (fun q : D.Cj × D.Y => b q.2 • u (D.el q.1) q.2) :=
    meas_pair (f := fun (c : D.Cj) (y : D.Y) => b y • u (D.el c) y) fun c => hb.meas.smul (hu (D.el c))
  have hlin : ∫⁻ q, ‖b q.2 • u (D.el q.1) q.2‖ₑ ∂(Measure.count.prod D.μY) =
      ∫⁻ y, ENNReal.ofReal (b y) * ∑' γ, ‖u γ y‖ₑ ∂D.μY := by
    calc ∫⁻ q, ‖b q.2 • u (D.el q.1) q.2‖ₑ ∂(Measure.count.prod D.μY)
        = ∑' c : D.Cj, ∫⁻ y, ‖b y • u (D.el c) y‖ₑ ∂D.μY :=
          lint_pair D.μY (fun q : D.Cj × D.Y => ‖b q.2 • u (D.el q.1) q.2‖ₑ) hgm.enorm
      _ = ∫⁻ y, ∑' c : D.Cj, ‖b y • u (D.el c) y‖ₑ ∂D.μY :=
          (lintegral_tsum fun c => ((hb.meas.smul (hu (D.el c))).enorm).aemeasurable).symm
      _ = ∫⁻ y, ENNReal.ofReal (b y) * ∑' γ, ‖u γ y‖ₑ ∂D.μY := by
          refine lintegral_congr fun y => ?_
          simp only [enorm_smul, Real.enorm_of_nonneg (hb.nonneg y)]
          exact ENNReal.tsum_mul_left
  have hgi : Integrable (fun q : D.Cj × D.Y => b q.2 • u (D.el q.1) q.2) (Measure.count.prod D.μY) := by
    refine ⟨hgm.aestronglyMeasurable, ?_⟩
    show ∫⁻ q, ‖b q.2 • u (D.el q.1) q.2‖ₑ ∂(Measure.count.prod D.μY) < ⊤
    rw [hlin]
    exact hfin
  have hae : ∀ᵐ y ∂D.μY, ∫ c, b y • u (D.el c) y ∂(Measure.count : Measure D.Cj) = b y • ∑' γ, u γ y := by
    filter_upwards [hgi.prod_left_ae] with y hy
    have hy' : Integrable (fun c : D.Cj => b y • u (D.el c) y) Measure.count := hy
    rw [integral_countable hy']
    simp only [measureReal_def, Measure.count_singleton, ENNReal.toReal_one, one_smul]
    exact tsum_const_smul'' (b y)
  have hP : Integrable (fun y => b y • ∑' γ, u γ y) D.μY := hgi.integral_prod_right.congr hae
  have hm1 : Measurable (fun p : (D.Cj × D.Om) × D.Xs => u (D.el p.1.1) (p.1.2, p.2)) :=
    meas_pair (α := D.Cj × D.Om) (β := D.Xs) (f := fun a z => u (D.el a.1) (a.2, z))
      fun a => (hu (D.el a.1)).comp measurable_prodMk_left
  have hmp : MeasurePreserving (MeasurableEquiv.prodAssoc : (D.Cj × D.Om) × D.Xs ≃ᵐ D.Cj × D.Om × D.Xs)
      D.μC (Measure.count.prod D.μY) := by
    have e : D.μC = (Measure.count.prod Measure.count).prod volume := by
      unfold UpperTheory.Esk.Dat.μC
      rw [count_prod]
    rw [e]
    exact measurePreserving_prodAssoc _ _ _
  have hC : Integrable (fun p : (D.Cj × D.Om) × D.Xs => b (p.1.2, p.2) • u (D.el p.1.1) (p.1.2, p.2)) D.μC :=
    (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hgi
  have hint : ∫ y, b y • ∑' γ, u γ y ∂D.μY =
      ∫ p, b (p.1.2, p.2) • u (D.el p.1.1) (p.1.2, p.2) ∂D.μC := by
    calc ∫ y, b y • ∑' γ, u γ y ∂D.μY
        = ∫ y, ∫ c, b y • u (D.el c) y ∂(Measure.count : Measure D.Cj) ∂D.μY := (integral_congr_ae hae).symm
      _ = ∫ q, b q.2 • u (D.el q.1) q.2 ∂(Measure.count.prod D.μY) := (integral_prod_symm _ hgi).symm
      _ = ∫ p, b (p.1.2, p.2) • u (D.el p.1.1) (p.1.2, p.2) ∂D.μC :=
          (hmp.integral_comp' (fun q : D.Cj × D.Y => b q.2 • u (D.el q.1) q.2)).symm
  exact ⟨hm1, hC, hP, hint⟩
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.E6OfLinearTraceIdentity
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk.LinearTraceIdentity

open UpperTheory.Esk

theorem op_kern {F I Gf ι : Type} [Field F] [Group Gf] [Fintype I] [Fintype ι] (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf)
    (y : D.Y) (hs : ∀ i, Summable fun γ : PG F =>
      D.ee ((D.rep y.1)⁻¹ * (D.j γ.out)⁻¹ * (D.rep y.1 * a i)) * (qq k y.2 (D.act γ.out y.2) * D.J k γ.out y.2)) :
    Dat.Op a (D.Kern k y) (y.2, D.rep y.1) = ∑' γ : PG F, D.kk k a γ y := by
  show ∑ i, D.Kern k y (y.2, D.rep y.1 * a i) = ∑' γ : PG F, D.kk k a γ y
  simp only [Dat.Kern, Dat.kk, Dat.kt, Dat.Te]
  rw [← Summable.tsum_finsetSum (fun i _ => hs i)]
  refine tsum_congr fun γ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_assoc]

end UpperTheory.Esk.LinearTraceIdentity

theorem UpperTheory.Esk.e6_of_linear_trace_identity : UpperTheory.Esk.E0a → UpperTheory.Esk.FormsStableUnderOperators → UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E3 → UpperTheory.Esk.E4 → UpperTheory.Esk.faceMap_zero_comp_eq_one → UpperTheory.Esk.E5 → UpperTheory.Esk.LinTr → UpperTheory.Esk.E6 := by
  intro hE0a hE0b _ hE3 hE4 hE4b hE5 hLin
  intro F I Gf ι _ _ _ _ D k a hH hfd h b hb
  have hM : ∀ f, f ∈ D.M k ↔ D.IsForm k f := (hE0b F I Gf D hH.ax k).1
  have hE4' := hE4 F I Gf D hH.ax k hH.four hH.compat
  have hE4b' := hE4b F I Gf D hH.ax k hH.four hH.compat
  have hE5' := hE5 F I Gf D hH.ax k hH.four hH.compat b hb
  have hbm : Measurable fun y => (b y).toNNReal := hb.meas.real_toNNReal
  obtain ⟨ν, hν⟩ : ∃ ν : Measure D.Y, ν = D.μY.withDensity fun y => ((b y).toNNReal : ℝ≥0∞) := ⟨_, rfl⟩
  haveI : IsFiniteMeasure ν := by
    rw [hν]
    exact MeasureTheory.isFiniteMeasure_withDensity (hE3 F I Gf D hH.ax b hb).ne
  have hint : ∀ g : D.Y → ℂ, ∫ y, g y ∂ν = ∫ y, b y • g y ∂D.μY := by
    intro g
    rw [hν, integral_withDensity_eq_integral_smul hbm]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (hb.nonneg y)]
  obtain ⟨K, hK⟩ : ∃ K : D.Y → D.M k, ∀ y, (K y).1 = D.Kern k y :=
    ⟨fun y => ⟨D.Kern k y, (hM _).2 (hE4' y)⟩, fun _ => rfl⟩
  have hn0 : Measurable fun z : X I => nrm k z := by
    unfold nrm
    refine Finset.measurable_prod _ fun v _ => ?_
    exact (continuous_abs.measurable.comp
      (Complex.measurable_im.comp (measurable_subtype_coe.comp (measurable_pi_apply v)))).pow_const _
  have hn_meas : Measurable fun y : D.Y => nrm k y.2 := hn0.comp measurable_snd
  have hn_pos : ∀ y : D.Y, 0 < nrm k y.2 := fun y =>
    Finset.prod_pos fun v _ => Real.rpow_pos_of_pos (abs_pos.mpr (y.2 v).2) _
  have hK_meas : ∀ p, Measurable fun y => (K y).1 p := by
    intro p
    simp only [hK]
    exact (hE4b' p).2.1
  have hf_meas : ∀ f : D.M k, Measurable fun y : D.Y => f.1 (y.2, D.rep y.1) := by
    intro f
    have hF := (hM f.1).1 f.2
    haveI : Countable D.Om := hH.ax.cO
    refine measurable_from_prod_countable_right fun ω => ?_
    have hc : Measurable fun z : X I => f.1 (z, D.rep ω) := ((hF.hol (D.rep ω)).1).measurable
    exact hc
  have hK_bdd : ∀ p, ∃ C, ∀ y, ‖(K y).1 p‖ ≤ C * nrm k y.2 := by
    intro p
    simp only [hK]
    exact (hE4b' p).2.2
  have hf_bdd : ∀ f : D.M k, ∃ C, ∀ y : D.Y, ‖f.1 (y.2, D.rep y.1)‖ * nrm k y.2 ≤ C := by
    intro f
    obtain ⟨C, hC⟩ := ((hM f.1).1 f.2).bdd
    exact ⟨C, fun y => hC _ _⟩
  have hrep : ∀ (f : D.M k) p, ∫ y, (K y).1 p * f.1 (y.2, D.rep y.1) ∂ν = f.1 p := by
    intro f p
    rw [hint]
    simp only [hK]
    exact hE5' f.1 ((hM f.1).1 f.2) p
  obtain ⟨hmeas, ⟨C, hC⟩, htr⟩ := hLin (X I × Gf) D.Y ν (D.M k) ((Dat.Op a).restrict h) K
    (fun y => (y.2, D.rep y.1)) (fun y => nrm k y.2) hn_meas hn_pos hK_meas hf_meas hK_bdd hf_bdd hrep
  have hval : ∀ y : D.Y, ((Dat.Op a).restrict h (K y)).1 (y.2, D.rep y.1) = ∑' γ : PG F, D.kk k a γ y := by
    intro y
    rw [LinearMap.restrict_coe_apply, hK]
    exact LinearTraceIdentity.op_kern D k a y (fun i => ((hE4b' (y.2, D.rep y.1 * a i)).1 y).of_norm)
  have hm2 : Measurable fun y => ∑' γ : PG F, D.kk k a γ y := by
    simpa only [hval] using hmeas
  refine ⟨?_, ?_⟩
  · have hgi : Integrable (fun y => ∑' γ : PG F, D.kk k a γ y) ν := by
      refine (integrable_const C).mono' hm2.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
      have := hC y
      simp only [hval] at this
      exact this
    rw [hν, MeasureTheory.integrable_withDensity_iff_integrable_smul hbm] at hgi
    refine hgi.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [NNReal.smul_def, Real.coe_toNNReal _ (hb.nonneg y)]
  · rw [htr, hint]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [hval]
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.KernelSumBoundedProof
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace UpperTheory.Esk

namespace KernelSumBound

theorem kap_nonneg (z w : P) : 0 ≤ kap z w := by
  unfold kap
  split_ifs with h
  · exact div_nonneg (mul_nonneg (by norm_num) h.le) (by positivity)
  · exact le_rfl

theorem Kap_nonneg {I : Type} [Fintype I] (k : I → ℕ) (z w : X I) : 0 ≤ Kap k z w := by
  unfold Kap
  exact Finset.prod_nonneg fun v _ => Real.rpow_nonneg (kap_nonneg _ _) _

variable {F I Gf ι : Type} [Field F] [Group Gf] [Fintype I] [Fintype ι]

theorem bound (D : Dat F I Gf) (k : I → ℕ) (a : ι → Gf) (C₀ : ℝ)
    (hk : ∀ (γ : PG F) (y : D.Y), ‖D.kk k a γ y‖ ≤ C₀ * Kap k y.2 (γ • y.2 : D.Xs))
    (hsupp : ∀ (γ : PG F) (ω : D.Om), D.Te a γ.out (D.rep ω) ≠ 0 →
      ∃ i, γ • ω = ((D.rep ω * a i : Gf) : Gf ⧸ D.H))
    (y : D.Y) (B : ℝ)
    (hB : ∀ ω' : D.Om, ∑' γ : {γ : PG F // γ • y.1 = ω'},
      ENNReal.ofReal (Kap k y.2 (γ.1 • y.2 : D.Xs)) ≤ ENNReal.ofReal B) :
    ∑' γ : PG F, ‖D.kk k a γ y‖ₑ ≤ Fintype.card ι * (ENNReal.ofReal C₀ * ENNReal.ofReal B) := by
  classical
  have hpt : ∀ γ : PG F, ‖D.kk k a γ y‖ₑ ≤ ∑ i, Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ := by
    intro γ
    by_cases h0 : D.Te a γ.out (D.rep y.1) = 0
    · have hz : D.kk k a γ y = 0 := by
        simp only [Dat.kk, Dat.kt, h0, zero_mul]
      rw [hz, enorm_zero]
      exact zero_le
    · obtain ⟨i, hi⟩ := hsupp γ y.1 h0
      calc ‖D.kk k a γ y‖ₑ = ENNReal.ofReal ‖D.kk k a γ y‖ := (ofReal_norm _).symm
        _ ≤ ENNReal.ofReal (C₀ * Kap k y.2 (γ • y.2 : D.Xs)) := ENNReal.ofReal_le_ofReal (hk γ y)
        _ = ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs)) :=
            ENNReal.ofReal_mul' (Kap_nonneg k _ _)
        _ = Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ :=
            (Set.indicator_of_mem
              (show γ ∈ {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)} from hi)
              (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs)))).symm
        _ ≤ _ := Finset.single_le_sum
            (f := fun j => Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a j : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ)
            (fun _ _ => zero_le) (Finset.mem_univ i)
  have hsub : ∀ i : ι, ∑' γ : PG F, Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ ≤
      ENNReal.ofReal C₀ * ENNReal.ofReal B := by
    intro i
    rw [← tsum_subtype, ENNReal.tsum_mul_left]
    gcongr
    exact hB ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)
  calc ∑' γ : PG F, ‖D.kk k a γ y‖ₑ
      ≤ ∑' γ : PG F, ∑ i, Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ := ENNReal.tsum_le_tsum hpt
    _ = ∑ i, ∑' γ : PG F, Set.indicator {γ : PG F | γ • y.1 = ((D.rep y.1 * a i : Gf) : Gf ⧸ D.H)}
          (fun γ => ENNReal.ofReal C₀ * ENNReal.ofReal (Kap k y.2 (γ • y.2 : D.Xs))) γ :=
        Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ _i : ι, ENNReal.ofReal C₀ * ENNReal.ofReal B := Finset.sum_le_sum fun i _ => hsub i
    _ = Fintype.card ι * (ENNReal.ofReal C₀ * ENNReal.ofReal B) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end KernelSumBound

end UpperTheory.Esk

theorem UpperTheory.Esk.kernel_sum_bounded_proof : UpperTheory.Esk.KernelTermsInvariantBounded → UpperTheory.Esk.E0d → UpperTheory.Esk.KapSum → UpperTheory.Esk.E2 := by
  intro h0c h0d hks F I Gf ι _ _ _ _ D k a hyp
  obtain ⟨-, -, -, ⟨C₀, hC₀⟩, hsupp, -⟩ := h0c F I Gf ι D k a hyp
  obtain ⟨c₀, hc₀, hmink⟩ := hyp.ax.mink
  obtain ⟨C, hC⟩ := hks F I Gf D hyp.ax k hyp.four c₀ hc₀
  obtain ⟨-, -, -, -, -, -, -, -, hT, -, -⟩ := h0d F I Gf D hyp.ax
  have key : ∀ T : ℝ, ∀ y ∈ D.abelian₂ T, ∑' γ : UpperTheory.Esk.PG F, ‖D.kk k a γ y‖ₑ ≤
      Fintype.card ι * (ENNReal.ofReal C₀ * ENNReal.ofReal (max C 0 * (1 + T))) := by
    intro T y hy
    obtain ⟨s, hs, hcs⟩ := hmink y.2 (D.rep y.1)
    have hpos : 0 < D.HtY s y := lt_of_lt_of_le hc₀ hcs
    have hle : D.HtY s y ≤ T := hy s hs
    refine UpperTheory.Esk.KernelSumBound.bound D k a C₀ hC₀ hsupp y (max C 0 * (1 + T)) fun ω' => ?_
    refine (hC y s hs hcs ω' y.2).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul (le_max_left C 0) (by linarith) (by linarith) (le_max_right C 0)
  refine ⟨fun y => ?_, fun T => ⟨Fintype.card ι * (C₀.toNNReal * (max C 0 * (1 + T)).toNNReal), fun y hy => ?_⟩⟩
  · obtain ⟨T₀, hT₀⟩ := hT y
    have hfin : ∑' γ : UpperTheory.Esk.PG F, ‖D.kk k a γ y‖ₑ ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)) (key T₀ y (hT₀ T₀ le_rfl))
    exact (ENNReal.summable_toReal hfin).congr fun γ => toReal_enorm _
  · refine (key T y hy).trans (le_of_eq ?_)
    rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_natCast]
    all_goals rfl
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfPack
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal ComplexConjugate

namespace UpperTheory.Esk

namespace KappaPackingLemmas

variable {F I Gf : Type} [Field F] [Group Gf]

theorem kap_smul (hb : B1b) (D : Dat F I Gf) (δ : PG F) (a b : D.Xs) (v : I) :
    kap ((δ • a : D.Xs) v) ((δ • b : D.Xs) v) = kap (a v) (b v) := by
  induction δ using QuotientGroup.induction_on with
  | H g =>
    rw [Dat.mk_smulX, Dat.mk_smulX]
    exact hb.2.2.2.1 (D.r v g) (a v) (b v)

theorem near_sixteenth (hb : B1b) (hc : B1c) (D : Dat F I Gf) (γ₁ γ : PG F) (z w : D.Xs)
    (h₁ : Near (1 / 2) (γ₁ • z : D.Xs) w) (h : Near (1 / 2) (γ • z : D.Xs) w) :
    Near (1 / 16) z ((γ₁⁻¹ * γ) • z : D.Xs) := by
  intro v
  have e : kap (z v) (((γ₁⁻¹ * γ) • z : D.Xs) v) = kap ((γ₁ • z : D.Xs) v) ((γ • z : D.Xs) v) := by
    rw [← kap_smul hb D γ₁ z ((γ₁⁻¹ * γ) • z) v, smul_smul, mul_inv_cancel_left]
  rw [e]
  have a1 := h₁ v
  have a2 := h v
  have s := (hc.1 ((γ • z : D.Xs) v) (w v)).2.2
  have t := hc.2.2.1 ((γ₁ • z : D.Xs) v) (w v) ((γ • z : D.Xs) v)
  rw [← s] at t
  nlinarith

end KappaPackingLemmas

end UpperTheory.Esk

open UpperTheory.Esk UpperTheory.Esk.KappaPackingLemmas in
theorem UpperTheory.Esk.pf_Pack : UpperTheory.Esk.B1b → UpperTheory.Esk.B1c → UpperTheory.Esk.E0a → UpperTheory.Esk.Pack := by
  intro hb hc hE F I Gf _ _ _ D hax
  obtain ⟨hcnt, -, -, -, -, -, -, hnear⟩ := hE F I Gf D hax
  obtain ⟨c, hc0, hcz⟩ := hnear (1 / 2) (by norm_num)
  have := hcnt
  refine ⟨c⁻¹, ?_⟩
  intro y ω' h A hh hA hfin
  set S0 : Set (PG F) := {γ : PG F | γ • y.1 = y.1 ∧ Near (1 / 16) y.2 (γ • y.2 : D.Xs)} with hS0
  set N : ℝ≥0∞ := (S0.ncard : ℝ≥0∞) with hN
  let Sg : {γ : PG F // γ • y.1 = ω'} → Set D.Xs := fun γ => {w | Near (1 / 2) (γ.1 • y.2 : D.Xs) w}
  have hSm : ∀ γ, MeasurableSet (Sg γ) := fun γ => (hcz (γ.1 • y.2)).1

  have one : ∀ γ : {γ : PG F // γ • y.1 = ω'}, (c : ℝ≥0∞) * h (γ.1 • y.2) ≤ A * ∫⁻ w, (Sg γ).indicator h w := by
    intro γ
    have hv : (c : ℝ≥0∞) ≤ volume (Sg γ) := (hcz (γ.1 • y.2)).2
    calc (c : ℝ≥0∞) * h (γ.1 • y.2) ≤ h (γ.1 • y.2) * volume (Sg γ) := by
          rw [mul_comm]; gcongr
      _ = ∫⁻ _ in Sg γ, h (γ.1 • y.2) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ w in Sg γ, (A : ℝ≥0∞) * h w := setLIntegral_mono' (hSm γ) fun w hw => hA _ _ hw
      _ = A * ∫⁻ w in Sg γ, h w := lintegral_const_mul _ hh
      _ = A * ∫⁻ w, (Sg γ).indicator h w := by rw [lintegral_indicator (hSm γ)]

  have cnt : ∀ w : D.Xs, ∑' γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w ≤ N * h w := by
    intro w
    by_cases hT : ∃ γ₁ : {γ : PG F // γ • y.1 = ω'}, w ∈ Sg γ₁
    · obtain ⟨γ₁, hγ₁⟩ := hT
      let f : {γ : PG F // γ • y.1 = ω'} → PG F := fun γ => γ₁.1⁻¹ * γ.1
      have finj : Function.Injective f := fun a b hab => Subtype.ext (mul_left_cancel hab)
      let g : PG F → ℝ≥0∞ := S0.indicator fun _ => h w
      have le1 : ∀ γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w ≤ g (f γ) := by
        intro γ
        by_cases hw : w ∈ Sg γ
        · rw [Set.indicator_of_mem hw]
          have hmem : f γ ∈ S0 := by
            refine ⟨?_, near_sixteenth hb hc D γ₁.1 γ.1 y.2 w hγ₁ hw⟩
            change (γ₁.1⁻¹ * γ.1) • y.1 = y.1
            rw [mul_smul, γ.2, inv_smul_eq_iff]; exact γ₁.2.symm
          simp [g, Set.indicator_of_mem hmem]
        · rw [Set.indicator_of_notMem hw]; exact bot_le
      calc ∑' γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w ≤ ∑' γ, g (f γ) := ENNReal.tsum_le_tsum le1
        _ ≤ ∑' x, g x := ENNReal.tsum_comp_le_tsum_of_injective finj g
        _ = ∑' x : S0, h w := (tsum_subtype S0 fun _ => h w).symm
        _ = N * h w := by
          have : Fintype S0 := hfin.fintype
          rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hN, ← Nat.card_coe_set_eq,
            Nat.card_eq_fintype_card]
    · simp only [not_exists] at hT
      have : ∀ γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w = 0 := fun γ => Set.indicator_of_notMem (hT γ) _
      simp [this]

  have key : (c : ℝ≥0∞) * ∑' γ : {γ : PG F // γ • y.1 = ω'}, h (γ.1 • y.2) ≤ A * (N * ∫⁻ w, h w) := by
    rw [← ENNReal.tsum_mul_left]
    calc ∑' γ : {γ : PG F // γ • y.1 = ω'}, (c : ℝ≥0∞) * h (γ.1 • y.2)
        ≤ ∑' γ : {γ : PG F // γ • y.1 = ω'}, (A : ℝ≥0∞) * ∫⁻ w, (Sg γ).indicator h w := ENNReal.tsum_le_tsum one
      _ = A * ∑' γ : {γ : PG F // γ • y.1 = ω'}, ∫⁻ w, (Sg γ).indicator h w := ENNReal.tsum_mul_left
      _ = A * ∫⁻ w, ∑' γ : {γ : PG F // γ • y.1 = ω'}, (Sg γ).indicator h w := by
          rw [lintegral_tsum fun γ => (hh.indicator (hSm γ)).aemeasurable]
      _ ≤ A * ∫⁻ w, N * h w := by gcongr with w; exact cnt w
      _ = A * (N * ∫⁻ w, h w) := by rw [lintegral_const_mul _ hh]
  have hc' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0.ne'
  calc ∑' γ : {γ : PG F // γ • y.1 = ω'}, h (γ.1 • y.2)
      = (c : ℝ≥0∞)⁻¹ * ((c : ℝ≥0∞) * ∑' γ : {γ : PG F // γ • y.1 = ω'}, h (γ.1 • y.2)) := by
        rw [ENNReal.inv_mul_cancel_left hc' ENNReal.coe_ne_top]
    _ ≤ (c : ℝ≥0∞)⁻¹ * (A * (N * ∫⁻ w, h w)) := by gcongr
    _ = ((c⁻¹ : ℝ≥0) : ℝ≥0∞) * A * N * ∫⁻ w, h w := by
        rw [ENNReal.coe_inv hc0.ne']; ring
end
end

section -- merged from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfMult
noncomputable section

open MeasureTheory Matrix

namespace UpperTheory.Esk.ExponentialSlopeDerivatives

variable {F I Gf : Type} [Field F] [Group Gf] (D : Dat F I Gf)

def A (δ : ℝ) (y : D.Y) : Set (PG F) := {γ : PG F | γ • y.1 = y.1 ∧ Near δ y.2 (γ • y.2 : D.Xs)}

theorem near_smul (hB : B1b) (δ : ℝ) (g : PG F) (z w : D.Xs) :
    Near δ (g • z : D.Xs) (g • w : D.Xs) ↔ Near δ z w := by
  induction g using QuotientGroup.induction_on with
  | H γ =>
    rw [Dat.mk_smulX D γ z, Dat.mk_smulX D γ w]
    simp only [Near, Dat.act, hB.2.2.2.1]

theorem mem_conj (hB : B1b) (δ : ℝ) (g γ : PG F) (y : D.Y) :
    g * γ * g⁻¹ ∈ A D δ (g • y) ↔ γ ∈ A D δ y := by
  simp only [A, Set.mem_setOf_eq, Prod.smul_fst, Prod.smul_snd, mul_smul, inv_smul_smul,
    smul_left_cancel_iff, near_smul D hB]

theorem A_conj (hB : B1b) (δ : ℝ) (g : PG F) (y : D.Y) :
    A D δ (g • y) = (fun γ => g * γ * g⁻¹) '' A D δ y := by
  ext γ'
  constructor
  · intro h
    refine ⟨g⁻¹ * γ' * g, (mem_conj D hB δ g _ y).1 ?_, ?_⟩
    · rwa [show g * (g⁻¹ * γ' * g) * g⁻¹ = γ' by group]
    · show g * (g⁻¹ * γ' * g) * g⁻¹ = γ'
      group
  · rintro ⟨γ, hγ, rfl⟩
    exact (mem_conj D hB δ g γ y).2 hγ

theorem conj_inj (g : PG F) : Function.Injective (fun γ : PG F => g * γ * g⁻¹) := by
  intro a b h
  simpa using h

theorem fin_card (hB : B1b) (δ : ℝ) (g : PG F) (y : D.Y) :
    ((A D δ (g • y)).Finite ↔ (A D δ y).Finite) ∧ (A D δ (g • y)).ncard = (A D δ y).ncard := by
  rw [A_conj D hB δ g y]
  exact ⟨Set.finite_image_iff (conj_inj g).injOn, Set.ncard_image_of_injective _ (conj_inj g)⟩

theorem e01 : (![0, 1] : Fin 2 → F) ≠ 0 := by
  intro h
  have := congrFun h 1
  simp at this

theorem Ht01 [Fintype I] (z : X I) (x : Gf) : D.Ht ![0, 1] z x = (∏ v, |(z v).1.im|) * D.hf ![0, 1] x := by
  simp [Dat.Ht]

end UpperTheory.Esk.ExponentialSlopeDerivatives

open UpperTheory.Esk UpperTheory.Esk.ExponentialSlopeDerivatives

theorem UpperTheory.Esk.pf_Mult : UpperTheory.Esk.B1b → UpperTheory.Esk.E0d → UpperTheory.Esk.Mult := by
  intro hB hE F I Gf _ _ _ D hD δ c₀ hδ hc₀
  obtain ⟨-, h2, h3, -, -, -, -, -, -, h10, -⟩ := hE F I Gf D hD
  obtain ⟨S, C, c, hc, hnorm⟩ := hD.normal c₀ hc₀
  have hcnt : ∀ x' : Gf, ∃ C' : ℝ, ∀ z : D.Xs, Sg C c z →
      (A D δ (((x' : Gf ⧸ D.H), z) : D.Om × D.Xs)).Finite ∧
      ((A D δ (((x' : Gf ⧸ D.H), z) : D.Om × D.Xs)).ncard : ℝ) ≤ C' * (1 + ∏ v, |(z v).1.im|) :=
    fun x' => hD.count ((x' : Gf ⧸ D.H)) δ C c hδ hc
  choose C' hC' using hcnt
  have hapos : ∀ x : Gf, 0 < D.hf ![0, 1] (D.rep ((x : Gf ⧸ D.H))) := fun x => hD.pos _ e01 _
  have final : ∀ (N Cx P a H K : ℝ), N ≤ Cx * (1 + P) → 0 ≤ P → P * a = H → 0 < a → 0 ≤ H →
      max Cx 0 * (1 + 1 / a) ≤ K → N ≤ K * (1 + H) := by
    intro N Cx P a H K hN hP hPa ha hH hK
    have hP' : P = H / a := eq_div_of_mul_eq ha.ne' hPa
    have h1 : N ≤ max Cx 0 * (1 + P) :=
      hN.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
    have h2 : 1 + P ≤ (1 + 1 / a) * (1 + H) := by
      rw [hP']
      have h0 : 0 ≤ 1 / a := by positivity
      have he : (1 + 1 / a) * (1 + H) - (1 + H / a) = H + 1 / a := by ring
      linarith
    have hM : 0 ≤ max Cx 0 := le_max_right _ _
    calc N ≤ max Cx 0 * (1 + P) := h1
      _ ≤ max Cx 0 * ((1 + 1 / a) * (1 + H)) := mul_le_mul_of_nonneg_left h2 hM
      _ = (max Cx 0 * (1 + 1 / a)) * (1 + H) := by ring
      _ ≤ K * (1 + H) := mul_le_mul_of_nonneg_right hK (by linarith)
  refine ⟨∑ x ∈ S, max (C' x) 0 * (1 + 1 / D.hf ![0, 1] (D.rep ((x : Gf ⧸ D.H)))), ?_⟩
  intro y s hs hy
  obtain ⟨γ₀, hγ₀⟩ := h10 s hs
  have e1 : D.HtY ![0, 1] ((γ₀ : PG F) • y) = D.HtY s y := by
    rw [h2 _ e01 γ₀ y, hγ₀]
  have hn : c₀ ≤ D.Ht ![0, 1] ((γ₀ : PG F) • y).2 (D.rep ((γ₀ : PG F) • y).1) := by
    rw [← e1] at hy
    exact hy
  obtain ⟨b, hb10, ⟨x', hx'S, h, hh, hbx⟩, hsg⟩ := hnorm _ _ hn
  have hb11 : b.val 1 1 ≠ 0 := by
    intro h0
    apply b.det_ne_zero
    rw [Matrix.det_fin_two]
    simp [h0, hb10]
  have hvb : ![0, 1] ᵥ* b.val = b.val 1 1 • ![(0 : F), 1] := by
    ext i
    fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, hb10]
  have hsm : ∀ ω : D.Om, (b : PG F) • ω = (((D.j b * D.rep ω : Gf) : Gf ⧸ D.H) : D.Om) := by
    intro ω
    conv_lhs => rw [← QuotientGroup.out_eq' ω]
    rfl
  have hy'' : (b : PG F) • ((γ₀ : PG F) • y) =
      (((x' : Gf ⧸ D.H), D.act b ((γ₀ : PG F) • y).2) : D.Om × D.Xs) := by
    refine Prod.ext ?_ (D.mk_smulX b _)
    show (b : PG F) • ((γ₀ : PG F) • y).1 = _
    rw [hsm, hbx]
    exact QuotientGroup.eq.2 (by simpa using hh)
  obtain ⟨f1, c1⟩ := fin_card D hB δ (γ₀ : PG F) y
  obtain ⟨f2, c2⟩ := fin_card D hB δ (b : PG F) ((γ₀ : PG F) • y)
  rw [hy''] at f2 c2
  obtain ⟨hfin, hle⟩ := hC' x' _ hsg
  refine ⟨f1.1 (f2.1 hfin), ?_⟩
  have hHt : D.HtY ![0, 1] (((x' : Gf ⧸ D.H), D.act b ((γ₀ : PG F) • y).2) : D.Om × D.Xs) = D.HtY s y := by
    rw [← hy'', h2 _ e01 b _, hvb, h3 _ e01 _ hb11, e1]
  have hP : D.HtY ![0, 1] (((x' : Gf ⧸ D.H), D.act b ((γ₀ : PG F) • y).2) : D.Om × D.Xs)
      = (∏ v, |((D.act b ((γ₀ : PG F) • y).2) v).1.im|) * D.hf ![0, 1] (D.rep ((x' : Gf ⧸ D.H))) :=
    Ht01 D (D.act b ((γ₀ : PG F) • y).2) (D.rep ((x' : Gf ⧸ D.H)))
  have hH : 0 ≤ D.HtY s y := by linarith
  show ((A D δ y).ncard : ℝ) ≤ _
  rw [← c1, ← c2]
  exact final _ _ _ _ _ _ hle (Finset.prod_nonneg fun v _ => abs_nonneg _) (hP.symm.trans hHt) (hapos x') hH
    (Finset.single_le_sum (f := fun x => max (C' x) 0 * (1 + 1 / D.hf ![0, 1] (D.rep ((x : Gf ⧸ D.H)))))
      (fun x _ => mul_nonneg (le_max_right _ _) (add_nonneg zero_le_one (one_div_nonneg.2 (hapos x).le))) hx'S)
end
end
