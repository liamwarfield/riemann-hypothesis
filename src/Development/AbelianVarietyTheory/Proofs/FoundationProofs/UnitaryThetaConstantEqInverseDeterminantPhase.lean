module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FstMemClosureNatCast
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PhDetMulIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PullEqGaussSmulIntertwiner
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralKerSumGraphEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralGaussianUnitaryPos
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta

theorem integral_gaussian_unitary_pos : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ a : V ≃ₗ[ℂ] V, (∀ z w, H (a z) (a w) = H z w) → LinearMap.det (1 - (a : V →ₗ[ℂ] V)) ≠ 0 → ∃ κ : ℝ, 0 < κ ∧ ∀ y v : V, Integrable (fun z => cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v)) μ ∧ ∫ z, cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v) ∂μ = κ / LinearMap.det (1 - (a : V →ₗ[ℂ] V)) * cexp (π * H y v) := by
  intro V _ _ _ _ _ μ _ H hH a ha hdet
  obtain ⟨n, e, l, he, hl⟩ := GlobalTheory.UnitaryTheta.unitary_exists_orthonormal_eigenbasis V H hH a ha
  have hb : ∀ i, (1 - (a : V →ₗ[ℂ] V)) (e i) = (1 - l i) • e i := fun i => by
    simp [(hl i).2, sub_smul]
  have hd := det_of_eigen e _ _ hb
  have hr : ∀ z i, e.repr (z - a z) i = (1 - l i) * e.repr z i := fun z i => by
    simpa using repr_apply_of_eigen e _ _ hb z i
  have hne : ∀ i, 1 - l i ≠ 0 := fun i => by
    rw [hd] at hdet
    exact Finset.prod_ne_zero_iff.1 hdet i (Finset.mem_univ _)
  have hre : ∀ i, 0 < (1 - l i).re := fun i => by
    have h1 : (l i).re ≤ 1 := (hl i).1 ▸ re_le_norm (l i)
    have h2 : (l i).re ≠ 1 := by
      intro h
      apply hne i
      have h3 : (l i).re * (l i).re + (l i).im * (l i).im = 1 := by
        rw [← normSq_apply, normSq_eq_norm_sq, (hl i).1]; norm_num
      have h4 : (l i).im = 0 := by
        rw [h] at h3
        exact mul_self_eq_zero.1 (by linarith)
      apply Complex.ext <;> simp [h, h4]
    simp only [sub_re, one_re]
    exact sub_pos.2 (lt_of_le_of_ne h1 h2)
  let T : V ≃L[ℂ] (Fin n → ℂ) := e.equivFun.toContinuousLinearEquiv
  let Tm : V ≃ᵐ (Fin n → ℂ) := T.toHomeomorph.toMeasurableEquiv
  have hT : ∀ z i, Tm z i = e.repr z i := fun z i => rfl
  haveI : (μ.map Tm).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  have hν := Measure.isAddLeftInvariant_eq_smul (μ.map Tm) (volume : Measure (Fin n → ℂ))
  have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map Tm) (volume : Measure (Fin n → ℂ))
  set c := Measure.addHaarScalarFactor (μ.map Tm) (volume : Measure (Fin n → ℂ)) with hc
  refine ⟨(c : ℝ), by exact_mod_cast hpos, fun y v => ?_⟩
  let g : Fin n → ℂ → ℂ := fun i z => cexp (-(π : ℂ) * (1 - l i) * (z * conj z) +
    π * (((1 - l i) * e.repr y i) * conj z) + π * (z * conj (e.repr v i)))
  have hg := fun i => GlobalTheory.T.integral_cexp_complex_gaussian_linear (1 - l i) ((1 - l i) * e.repr y i) (e.repr v i) (hre i)
  have hF : (fun z => cexp (-(π : ℂ) * H (z - a z) z + π * H (y - a y) z + π * H z v)) =
      (fun x : Fin n → ℂ => ∏ i, g i (x i)) ∘ Tm := by
    funext z
    simp only [Function.comp, g, hT, ← Complex.exp_sum, sesq_eq_sum_repr H e he, hr, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hint : Integrable (fun x : Fin n → ℂ => ∏ i, g i (x i)) volume :=
    Integrable.fintype_prod (f := g) fun i => (hg i).1
  rw [hF]
  refine ⟨?_, ?_⟩
  · rw [← integrable_map_equiv, hν]
    exact hint.smul_measure_nnreal
  · have h1 := integral_map_equiv (μ := μ) Tm (fun x : Fin n → ℂ => ∏ i, g i (x i))
    simp only [Function.comp_def]
    rw [← h1, hν, integral_smul_nnreal_measure, integral_fintype_prod_volume_eq_prod, hd,
      sesq_eq_sum_repr H e he, Finset.mul_sum, Complex.exp_sum]
    have h2 : ∀ i, ∫ z, g i z = (1 - l i)⁻¹ * cexp (π * (e.repr y i * conj (e.repr v i))) := fun i => by
      rw [show ∫ z, g i z = _ from (hg i).2]
      congr 2
      field_simp [hne i]
    simp only [h2, Finset.prod_mul_distrib, Finset.prod_inv_distrib, NNReal.smul_def, real_smul]
    ring

end GlobalTheory.UnitaryTheta
end

open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta.Graph

theorem integral_kerSum_graph_eq : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ a : V ≃ₗ[ℂ] V, (∀ z w, H (a z) (a w) = H z w) → LinearMap.det (1 - (a : V →ₗ[ℂ] V)) ≠ 0 → ∀ (B : V →ₗ[ℂ] V), (∀ x, B x - a (B x) = x) → ∀ (Λ Λ' : AddSubgroup V) [DiscreteTopology Λ], Λ' ≤ Λ → (∀ y ∈ Λ', a y ∈ Λ) → ∀ α : V → ℂ, IsSemichar H Λ α → (∀ y ∈ Λ', α (a y) = α y) → ∀ Fd : Set V, IsAddFundamentalDomain Λ' Fd μ → ∀ (M : Type) [Fintype M] (s : M → V), (∀ m, s m ∈ Λ) → (∀ x ∈ Λ, ∃! p : M × Λ', x = s p.1 - ((p.2 : V) - a p.2)) → ∃ κ : ℝ, 0 < κ ∧ ∫ z in Fd, kerSum H Λ α z (a z) * cexp (-(π : ℂ) * H z z) ∂μ = κ / LinearMap.det (1 - (a : V →ₗ[ℂ] V)) * ∑ m, α (s m) * cexp (-((π : ℂ) * I) * ((H (B (s m)) (s m)).im : ℂ)) := by
  intro V _ _ _ _ _ μ _ H hH a ha hdet B hB1 Λ Λ' _ hle haΛ α hα hαa Fd hFd M _ s hs huniq
  haveI : ProperSpace V := FiniteDimensional.proper ℂ V
  haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : Countable Λ' := (AddSubgroup.inclusion_injective hle).countable
  obtain ⟨κ, hκ, hg⟩ := integral_gaussian_unitary_pos V μ H hH a ha hdet
  refine ⟨κ, hκ, ?_⟩
  have hint : ∀ x, Integrable (term H a α x) μ := fun x => by
    have : term H a α x = _ := funext fun z => term_eq H a ha α x (B x) z (hB1 x)
    rw [this]
    exact (hg (B x) _).1.const_mul _
  have hval : ∀ x, ∫ z, term H a α x z ∂μ = κ / LinearMap.det (1 - (a : V →ₗ[ℂ] V)) *
      (α x * cexp (-((π : ℂ) * I) * ((H (B x) x).im : ℂ))) := fun x => by
    simp only [fun z => term_eq H a ha α x (B x) z (hB1 x)]
    rw [integral_const_mul, (hg (B x) _).2, ← value_eq H hH a ha x (B x) (hB1 x)]
    ring
  let f : M × Λ' → Λ := fun p => ⟨s p.1 - ((p.2 : V) - a p.2),
    Λ.sub_mem (hs _) (Λ.sub_mem (hle p.2.2) (haΛ _ p.2.2))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q hpq
      exact (huniq _ (f p).2).unique rfl (congrArg Subtype.val hpq)
    · intro x
      obtain ⟨p, hp, -⟩ := huniq x x.2
      exact ⟨p, Subtype.ext hp.symm⟩
  have hsum : ∀ z, kerSum H Λ α z (a z) * cexp (-(π : ℂ) * H z z) =
      ∑ m, ∑' y : Λ', term H a α (s m) (z + y) := fun z => by
    have h1 : Summable (fun x : Λ => term H a α x z) :=
      ((GlobalTheory.UnitaryTheta.KerSum.kerSum_spec V H hH Λ α hα).1 (a z) z).mul_right _
    have h2 := (Equiv.ofBijective f hf).summable_iff.2 h1
    rw [kerSum, ← tsum_mul_right]
    change ∑' x : Λ, term H a α x z = _
    rw [← (Equiv.ofBijective f hf).tsum_eq]
    refine (h2.tsum_prod).trans ?_
    rw [tsum_fintype]
    refine Finset.sum_congr rfl fun m _ => tsum_congr fun y => ?_
    exact term_shift H hH a ha Λ α hα (s m) y z (hs m) (hle y.2) (haΛ _ y.2) (hαa _ y.2)
  have hu := fun m => GlobalTheory.integral_unfold_fundamentalDomain V μ Λ' Fd hFd _ (hint (s m))
  simp only [hsum]
  rw [integral_finsetSum _ (fun m _ => (hu m).1)]
  simp only [fun m => (hu m).2, hval]
  rw [← Finset.mul_sum]

end GlobalTheory.UnitaryTheta.Graph
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTransport
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ThetaIso

open MeasureTheory GlobalTheory.ThetaInter

section General

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]
  [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] (μ : Measure W) [μ.IsAddHaarMeasure]

theorem mean_transport {A A₁ : AddSubgroup W} (hA : DiscreteTopology A)
    (hsp : Submodule.span ℝ (A : Set W) = ⊤) (e : W ≃ₗ[ℝ] W) (he : ∀ x, x ∈ A ↔ e x ∈ A₁)
    {f : W → ℝ} (hf : ∀ x ∈ A, ∀ z, f (z + x) = f z) :
    mean μ A₁ (fun z => f (e.symm z)) = mean μ A f := by
  obtain ⟨n, b, hb⟩ := exists_basis hA hsp
  have hb₁ : (Submodule.span ℤ (Set.range (b.map e))).toAddSubgroup = A₁ := by
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← he, ← hb, Submodule.mem_toAddSubgroup, Submodule.mem_toAddSubgroup,
      Module.Basis.mem_span_iff_repr_mem, Module.Basis.mem_span_iff_repr_mem]
    simp
  rw [mean_eq μ b hb hf, mean_eq μ (b.map e) hb₁ fun x hx z => by
    rw [map_add (f := _), hf _ ((he _).2 (by simpa using hx))]]
  let ec : W ≃L[ℝ] W := e.toContinuousLinearEquiv
  let em : W ≃ᵐ W := ec.toHomeomorph.toMeasurableEquiv
  have hpre : ZSpan.fundamentalDomain b = em ⁻¹' ZSpan.fundamentalDomain (b.map e) := by
    ext x
    change _ ↔ e x ∈ ZSpan.fundamentalDomain (b.map e)
    simp [ZSpan.mem_fundamentalDomain]
  haveI : (μ.map em).IsAddHaarMeasure := ec.isAddHaarMeasure_map μ
  have hs := Measure.isAddLeftInvariant_eq_smul (μ.map em) μ
  have hc0 : Measure.addHaarScalarFactor (μ.map em) μ ≠ 0 :=
    (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne'
  have h1 : ⨍ z in em ⁻¹' ZSpan.fundamentalDomain (b.map e), f z ∂μ
      = ⨍ z in ZSpan.fundamentalDomain (b.map e), f (e.symm z) ∂(μ.map em) := by
    rw [setAverage_eq, setAverage_eq, setIntegral_map_equiv, measureReal_def, measureReal_def,
      em.map_apply]
    congr 2
    funext z
    exact congrArg f (e.symm_apply_apply z).symm
  rw [hpre, h1, hs, setAverage_eq, setAverage_eq, Measure.restrict_smul, integral_smul_nnreal_measure,
    measureReal_nnreal_smul_apply]
  have hc1 : ((Measure.addHaarScalarFactor (μ.map em) μ : NNReal) : ℝ) ≠ 0 := by
    exact_mod_cast hc0
  rw [NNReal.smul_def, smul_eq_mul, smul_eq_mul, smul_eq_mul, mul_inv]
  field_simp

theorem mean_pos {A : AddSubgroup W} (hA : DiscreteTopology A)
    (hsp : Submodule.span ℝ (A : Set W) = ⊤) {f : W → ℝ} (hc : Continuous f) (h0 : ∀ z, 0 ≤ f z)
    (hf : ∀ x ∈ A, ∀ z, f (z + x) = f z) {z₀ : W} (hz : f z₀ ≠ 0) : 0 < mean μ A f := by
  obtain ⟨n, b, hb⟩ := exists_basis hA hsp
  rw [mean_eq μ b hb hf, setAverage_eq, smul_eq_mul]
  have hbd := ZSpan.fundamentalDomain_isBounded b
  have hI : IntegrableOn f (ZSpan.fundamentalDomain b) μ :=
    (hc.continuousOn.integrableOn_compact hbd.isCompact_closure).mono_set subset_closure
  have hsupp : 0 < μ (Function.support f ∩ ZSpan.fundamentalDomain b) := by
    rw [pos_iff_ne_zero]
    intro h
    have hfd := ZSpan.isAddFundamentalDomain' b μ
    have hz0 := hfd.measure_zero_of_invariant (Function.support f) (fun g => ?_) h
    · exact (hc.isOpen_support.measure_pos μ ⟨z₀, hz⟩).ne' hz0
    · ext y
      rw [Set.mem_vadd_set_iff_neg_vadd_mem]
      change f (-(g : W) + y) ≠ 0 ↔ f y ≠ 0
      rw [add_comm, hf _ (A.neg_mem (hb.le g.2))]
  refine mul_pos (inv_pos.2 ?_) ?_
  · exact ENNReal.toReal_pos (hsupp.trans_le (measure_mono Set.inter_subset_right)).ne' hbd.measure_lt_top.ne
  · exact (setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall h0) hI).2 hsupp

end General

theorem theta_transport : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A A₁ : AddSubgroup (VC D N N')), KLat D (tor0 D cc δ) A → KLat D (tor0 D cc δ) A₁ → ∀ (u : VC D N N' ≃ₗ[ℂ] VC D N N'), (∀ z w, Hf D (tor0 D cc δ) (u z) (u w) = Hf D (tor0 D cc δ) z w) → (∀ x, x ∈ A ↔ u x ∈ A₁) → ∀ th ∈ ThSp D (tor0 D cc δ) A, (fun z => th (u.symm z)) ∈ ThSp D (tor0 D cc δ) A₁ ∧ normSq D (tor0 D cc δ) A₁ (fun z => th (u.symm z)) = normSq D (tor0 D cc δ) A th ∧ (th ≠ 0 → 0 < normSq D (tor0 D cc δ) A th) := by
  intro D cc δ hc N N' A A₁ h₁ _ u hu hA th hth
  obtain ⟨f₁, s₁, d₁, c₁⟩ := klat_facts hc h₁
  have hH := isHerm_sesqOf D (tor0 D cc δ) N N'
  have : (volume : Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (VC D N N')).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have t₁ := discrete_of_selfDual hH d₁ f₁
  have hF : th ∈ Formalism.L2.Th1.H.fixedBy (sesqOf D (tor0 D cc δ) N N') (al D (tor0 D cc δ)) A := hth.2
  have hper := fun x hx z => rho_add_of_fixed hH c₁ hF (x := x) hx z
  refine ⟨⟨hth.1.comp u.symm.toContinuousLinearEquiv.differentiable, fun x hx z => ?_⟩, ?_, fun hne => ?_⟩
  · obtain ⟨x, rfl⟩ := u.surjective x
    obtain ⟨z, rfl⟩ := u.surjective z
    have := hth.2 x ((hA x).2 hx) z
    simp only [al, U, hu, ← map_add (f := _), LinearEquiv.symm_apply_apply] at this ⊢
    exact this
  · have := mean_transport volume t₁ s₁ (u.restrictScalars ℝ) hA hper
    refine Eq.trans ?_ this
    change mean volume A₁ (rho (sesqOf D (tor0 D cc δ) N N') fun z => th (u.symm z)) = _
    congr 1
    funext z
    obtain ⟨z, rfl⟩ := u.surjective z
    change ‖th (u.symm (u z))‖ ^ 2 * Real.exp (-Real.pi * (Hf D _ (u z) (u z)).re) =
      ‖th (u.symm (u z))‖ ^ 2 * Real.exp (-Real.pi * (Hf D _ (u.symm (u z)) (u.symm (u z))).re)
    rw [hu, u.symm_apply_apply]
  · obtain ⟨z₀, hz⟩ := Function.ne_iff.1 hne
    refine mean_pos (f := rho (sesqOf D (tor0 D cc δ) N N') th) volume t₁ s₁ (continuous_rho hH hth.1.continuous) (fun z => by unfold rho; positivity) hper
      (z₀ := z₀) ?_
    have : 0 < ‖th z₀‖ := norm_pos_iff.2 hz
    unfold rho
    positivity

end GlobalTheory.ThetaIso
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.UnitaryTheta.Constant

section General

open Complex MeasureTheory
open scoped Real ComplexConjugate

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  [MeasurableSpace V] [BorelSpace V]

theorem const_eq (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V) (hH : IsPosHerm H) (a : V ≃ₗ[ℂ] V)
    (ha : ∀ z w, H (a z) (a w) = H z w) (hdet : LinearMap.det (1 - (a : V →ₗ[ℂ] V)) ≠ 0)
    (C : V →ₗ[ℂ] V) (hC : ∀ x, C (x - a x) = (1 / 2 : ℂ) • (x + a x))
    (A A₁ : AddSubgroup V) [DiscreteTopology A] (hfg : A.FG) (hsp : Submodule.span ℝ (A : Set V) = ⊤)
    [Finite (A₁ ⧸ A.addSubgroupOf A₁)] (hA₁ : ∀ y, a y ∈ A → y ∈ A₁)
    (hint : ∀ x ∈ A₁, ∀ y ∈ A₁, ∃ m : ℤ, (H x y).im = m)
    (α : V → ℂ) (hα : IsSemichar H A α) (hαa : ∀ y, α (a y) = α y) (hαn : ∀ y, α (-y) = α y)
    (m : ℕ) (hm : 0 < m) (hmA : ∀ x ∈ A, ∃ y ∈ A, a y ∈ A ∧ m • x = y - a y)
    (c : ℂ) (n : ℝ) (hn : 0 < n)
    (hc : ∀ z w, kerSum H A α z (a w) = c * ((n : ℂ) * ∑ᶠ q : A₁ ⧸ A.addSubgroupOf A₁,
      α ((q.out : A₁) : V) * Heisenberg₂ H ((q.out : A₁) : V) (kerSum H A α z) w)) :
    ∃ r : ℝ, 0 < r ∧ c = r * (LinearMap.det (1 - (a : V →ₗ[ℂ] V)))⁻¹ *
      ∑ᶠ q : A ⧸ (subLa m A).addSubgroupOf A, α ((q.out : A) : V) *
        cexp (-(π : ℂ) * H (C ((q.out : A) : V)) ((q.out : A) : V)) := by
  set B : V →ₗ[ℂ] V := C + (1 / 2 : ℂ) • LinearMap.id with hBdef
  have hB1 : ∀ y, B (y - a y) = y := by
    intro y
    simp only [hBdef, LinearMap.add_apply, hC, LinearMap.smul_apply, LinearMap.id_apply]
    module
  have hsurj : ∀ x, ∃ y, x = y - a y := by
    intro x
    have hu : IsUnit (1 - (a : V →ₗ[ℂ] V)) := (LinearMap.isUnit_iff_isUnit_det _).2 (Ne.isUnit hdet)
    obtain ⟨y, hy⟩ := ((Module.End.isUnit_iff _).1 hu).2 x
    exact ⟨y, by rw [← hy]; simp⟩
  have hB2 : ∀ x, B x - a (B x) = x := by
    intro x
    obtain ⟨y, rfl⟩ := hsurj x
    rw [hB1]
  have hCB : ∀ x, H (C x) x = I * ((H (B x) x).im : ℂ) := by
    intro x
    obtain ⟨y, rfl⟩ := hsurj x
    rw [hB1, hC]
    have h1 := hH.1 (a y) y
    have h2 : (H y y).im = 0 := Complex.conj_eq_iff_im.1 (hH.1 y y).symm
    simp only [map_smul, map_add (f := _), map_sub, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply, ha, h1,
      smul_eq_mul]
    apply Complex.ext <;> simp [h2] <;> ring
  let Λ : AddSubgroup V := (subLa m A).comap (1 - (a : V →ₗ[ℂ] V)).toAddMonoidHom
  have hΛ : ∀ y, y ∈ Λ ↔ y - a y ∈ subLa m A := fun y => by simp [Λ]
  have hΛ' : ∀ y ∈ Λ, y ∈ A ∧ a y ∈ A := by
    intro y hy
    obtain ⟨x, hx, e⟩ := (hΛ y).1 hy
    obtain ⟨y', h1, h2, h3⟩ := hmA x hx
    have : y = y' := by
      rw [← hB1 y, ← hB1 y', ← h3, ← e]; rfl
    rw [this]; exact ⟨h1, h2⟩
  have hle : Λ ≤ A := fun y hy => (hΛ' y hy).1
  have hdisc : DiscreteTopology Λ := DiscreteTopology.of_subset (s := (A : Set V)) inferInstance hle
  have hspan : Submodule.span ℝ (Λ : Set V) = ⊤ := by
    have h1 : ∀ x ∈ Submodule.span ℝ (A : Set V), B x ∈ Submodule.span ℝ (Λ : Set V) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        have h2 : B (m • x) ∈ Λ := by
          rw [hΛ, hB2]; exact ⟨x, hx, rfl⟩
        have h3 : B x = (m : ℝ)⁻¹ • B (m • x) := by
          rw [map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (by positivity), one_smul]
        rw [h3]
        exact Submodule.smul_mem _ _ (Submodule.subset_span h2)
      | zero => simp
      | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
      | smul t x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ hx
    rw [eq_top_iff]
    intro y _
    rw [← hB1 y]
    exact h1 _ (hsp ▸ Submodule.mem_top)
  obtain ⟨k, b, hb⟩ := GlobalTheory.ThetaInter.exists_basis hdisc hspan
  have hFd : IsAddFundamentalDomain Λ (ZSpan.fundamentalDomain b) μ := by
    rw [← hb]; exact ZSpan.isAddFundamentalDomain' b μ
  have hfin : μ (ZSpan.fundamentalDomain b) ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded b).measure_lt_top.ne
  have hpos : 0 < μ.real (ZSpan.fundamentalDomain b) :=
    ENNReal.toReal_pos (ZSpan.measure_fundamentalDomain_ne_zero b) hfin
  haveI : Finite (A ⧸ (subLa m A).addSubgroupOf A) :=
    GlobalTheory.ThetaInter.finite_quot hfg fun x hx => ⟨m, hm, x, hx, rfl⟩
  letI := Fintype.ofFinite (A ⧸ (subLa m A).addSubgroupOf A)
  letI := Fintype.ofFinite (A₁ ⧸ A.addSubgroupOf A₁)
  obtain ⟨κ, hκ, hL⟩ := Graph.integral_kerSum_graph_eq V μ H hH a ha hdet B hB2 A Λ hle (fun y hy => (hΛ' y hy).2) α hα
    (fun y _ => hαa y) _ hFd (A ⧸ (subLa m A).addSubgroupOf A) (fun q => ((q.out : A) : V)) (fun q => (q.out : A).2) (by
      intro x hx
      have h1 : ((((⟨x, hx⟩ : A) : A ⧸ (subLa m A).addSubgroupOf A).out : A) : V) - x ∈ subLa m A := by
        have := QuotientAddGroup.eq.1
          (Quotient.out_eq ((⟨x, hx⟩ : A) : A ⧸ (subLa m A).addSubgroupOf A)).symm
        rw [AddSubgroup.mem_addSubgroupOf] at this
        simpa [neg_add_eq_sub] using this
      refine ⟨(((⟨x, hx⟩ : A) : A ⧸ (subLa m A).addSubgroupOf A), ⟨B _, by rw [hΛ, hB2]; exact h1⟩), ?_, ?_⟩
      · simp only [hB2]; abel
      · rintro ⟨q, y, hy⟩ e
        simp only at e
        have hq : q = ((⟨x, hx⟩ : A) : A ⧸ (subLa m A).addSubgroupOf A) := by
          rw [← Quotient.out_eq q]
          refine (QuotientAddGroup.eq.2 ?_).symm
          rw [AddSubgroup.mem_addSubgroupOf]
          convert (hΛ y).1 hy using 1
          simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
          rw [e]; abel
        subst hq
        refine Prod.ext rfl (Subtype.ext ?_)
        simp only
        rw [← hB1 y]
        congr 1
        exact (sub_sub_cancel _ _).symm.trans (congrArg _ e.symm))
  have hR := fun q : A₁ ⧸ A.addSubgroupOf A₁ => integral_heis_kerSum_diag V μ H hH A Λ hle α hα _ hFd hfin
    ((q.out : A₁) : V) fun y hy => hint _ (q.out : A₁).2 y (hA₁ y (hΛ' y hy).2)
  have hsum : ∫ z in ZSpan.fundamentalDomain b, kerSum H A α z (a z) * cexp (-(π : ℂ) * H z z) ∂μ =
      c * n * (μ.real (ZSpan.fundamentalDomain b) : ℂ) := by
    have e : ∀ z, kerSum H A α z (a z) * cexp (-(π : ℂ) * H z z) = c * n * ∑ q : A₁ ⧸ A.addSubgroupOf A₁,
        α ((q.out : A₁) : V) * (Heisenberg₂ H ((q.out : A₁) : V) (kerSum H A α z) z * cexp (-(π : ℂ) * H z z)) := by
      intro z
      rw [hc, finsum_eq_sum_of_fintype]
      simp only [← mul_assoc, ← Finset.sum_mul]
    simp only [e]
    rw [integral_const_mul, integral_finsetSum _ fun q _ => (hR q).1.const_mul _]
    congr 1
    rw [Finset.sum_eq_single 0]
    · have h0 := (GlobalTheory.ThetaInter.out_mem_iff (A₁ := A) (A₂ := A₁) 0).2 rfl
      rw [integral_const_mul, (hR 0).2, if_pos h0, hαn, ← mul_assoc]
      rcases hα.1 _ h0 with h | h <;> simp [h]
    · intro q _ hq
      rw [integral_const_mul, (hR q).2, if_neg (fun h => hq ((GlobalTheory.ThetaInter.out_mem_iff q).1 h)), mul_zero]
    · simp
  refine ⟨κ / (n * μ.real (ZSpan.fundamentalDomain b)), by positivity, ?_⟩
  rw [finsum_eq_sum_of_fintype]
  simp only [hCB]
  have e : ∀ t : ℂ, -(π : ℂ) * (I * t) = -((π : ℂ) * I) * t := fun t => by ring
  simp only [e]
  rw [hsum] at hL
  have h1 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have h2 : (μ.real (ZSpan.fundamentalDomain b) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  push_cast
  field_simp
  field_simp at hL
  linear_combination hL

end General


open MeasureTheory GlobalTheory.ThetaInter in
theorem pull_eq_gauss_smul_intertwiner : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A A₁ : AddSubgroup (VC D N N')), KLat D (tor0 D cc δ) A → KLat D (tor0 D cc δ) A₁ → ∀ (u : VC D N N' ≃ₗ[ℂ] VC D N N'), (∀ z w, Hf D (tor0 D cc δ) (u z) (u w) = Hf D (tor0 D cc δ) z w) → (∀ x, x ∈ A ↔ u x ∈ A₁) → LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) ≠ 0 → ∀ (C : VC D N N' →ₗ[ℂ] VC D N N'), (∀ x, C (x - u.symm x) = (1 / 2 : ℂ) • (x + u.symm x)) → ∀ m : ℕ, 0 < m → (∀ x ∈ A, ∃ y ∈ A, u.symm y ∈ A ∧ m • x = y - u.symm y) → ∀ th ∈ ThSp D (tor0 D cc δ) A, th ≠ 0 → ∃ (c : ℂ) (r : ℝ), ‖c‖ = 1 ∧ 0 < r ∧ c = r * (LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')))⁻¹ * (∑ᶠ q : A ⧸ (subLa m A).addSubgroupOf A, al D (tor0 D cc δ) ((q.out : A) : VC D N N') * Complex.exp (-(Real.pi : ℂ) * Hf D (tor0 D cc δ) (C ((q.out : A) : VC D N N')) ((q.out : A) : VC D N N'))) ∧ (fun z => th (u.symm z)) = c • Iop D (tor0 D cc δ) A A₁ th := by
  intro D cc δ hc N N' A A₁ h₁ h₂ u hu hA hdet C hC m hm hmA th hth hne
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨f₁, s₁, d₁, c₁⟩ := klat_facts hc h₁
  obtain ⟨f₂, -, -, -⟩ := klat_facts hc h₂
  obtain ⟨l₁, -, i₁, -⟩ := GlobalTheory.ThetaLine.theta_line D hG cc δ hc N N' A h₁
  obtain ⟨l₂, -, i₂, -⟩ := GlobalTheory.ThetaLine.theta_line D hG cc δ hc N N' A₁ h₂
  have := klat_finite hG.1 hc.1.1 h₁ h₂ f₂
  have : (volume : Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have : (volume : Measure (VC D N N')).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have t₁ := discrete_of_selfDual (isHerm_sesqOf D (tor0 D cc δ) N N') d₁ f₁
  obtain ⟨L, hL⟩ := GlobalTheory.T.exists_periodPair_idealCurveLattice D cc δ hc
  have hH := isPosHerm_formV D (tor0 D cc δ) N N' (GlobalTheory.T.latticeCovolume_pos_and_selfDual L _ hL).1
  have hα : IsSemichar (formV D (tor0 D cc δ) N N') A (al D (tor0 D cc δ)) := by
    refine ⟨c₁.1, i₁, fun x hx y hy => ?_⟩
    rw [c₁.2 x hx y hy]
    obtain ⟨k, hk⟩ := i₁ x hx y hy
    congr 1
    change Complex.exp (_ * ((Hf D _ x y).im : ℂ)) = Complex.exp (_ * ((Hf D _ x y).im : ℂ))
    rw [hk, Complex.exp_eq_exp_iff_exists_int]
    exact ⟨k, by push_cast; ring⟩
  obtain ⟨p₁, p₂, p₃⟩ := GlobalTheory.ThetaIso.theta_transport D cc δ hc N N' A A₁ h₁ h₂ u hu hA th hth
  obtain ⟨-, q₁, q₂, q₃⟩ := GlobalTheory.theta_translation_intertwiner_unitary D cc δ hc N N' A A₁ h₁ h₂ th hth
  have hsm : ∀ (B B' : AddSubgroup (VC D N N')) [Finite (B' ⧸ B.addSubgroupOf B')] (t : ℂ) (G : VC D N N' → ℂ),
      Iop D (tor0 D cc δ) B B' (t • G) = t • Iop D (tor0 D cc δ) B B' G := by
    intro B B' _ t G
    letI := Fintype.ofFinite (B' ⧸ B.addSubgroupOf B')
    funext z
    simp only [Iop, U, finsum_eq_sum_of_fintype, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hI : Iop D (tor0 D cc δ) A A₁ th ≠ 0 := by
    intro h
    apply hne
    rw [← q₃, h]
    funext z
    simp [Iop, U]
  obtain ⟨c, hcI⟩ := l₂ _ p₁ _ q₁ hI
  have hnorm : ‖c‖ = 1 := by
    have h1 : normSq D (tor0 D cc δ) A₁ (c • Iop D (tor0 D cc δ) A A₁ th) =
        ‖c‖ ^ 2 * normSq D (tor0 D cc δ) A₁ (Iop D (tor0 D cc δ) A A₁ th) := by
      simp only [normSq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, mul_assoc, average_eq, integral_const_mul]
      ring
    rw [← hcI, p₂, q₂] at h1
    have h2 : ‖c‖ ^ 2 = 1 := by
      have := (p₃ hne).ne'
      field_simp at h1
      exact h1.symm
    exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).1 (by rw [h2, one_pow])
  have hu' : ∀ z w, Hf D (tor0 D cc δ) (u.symm z) (u.symm w) = Hf D (tor0 D cc δ) z w := fun z w => by
    rw [← hu, u.apply_symm_apply, u.apply_symm_apply]
  obtain ⟨-, k₁, k₂⟩ := KerSum.kerSum_spec _ _ hH A _ hα
  have hidx : 0 < ((A.addSubgroupOf A₁).index : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero AddSubgroup.index_ne_zero_of_finite
  obtain ⟨r, hr, hrc⟩ := const_eq volume (formV D (tor0 D cc δ) N N') hH u.symm hu' hdet C hC A A₁ f₁ s₁
    (fun y hy => by simpa using (hA _).1 hy) i₂ (al D (tor0 D cc δ)) hα (fun y => by simp only [al, hu'])
    (fun y => by simp [al, Hf]) m hm hmA c (Real.sqrt ((A.addSubgroupOf A₁).index : ℝ))⁻¹
    (inv_pos.2 (Real.sqrt_pos.2 hidx)) (by
      intro z w
      obtain ⟨t, ht⟩ := l₁ _ ⟨k₁ z, k₂ z⟩ th hth hne
      have h1 : kerSum (formV D (tor0 D cc δ) N N') A (al D (tor0 D cc δ)) z (u.symm w) =
          c * Iop D (tor0 D cc δ) A A₁ (kerSum (formV D (tor0 D cc δ) N N') A (al D (tor0 D cc δ)) z) w := by
        rw [ht, hsm]
        have := congrFun hcI w
        simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
        rw [this]; ring
      rw [h1, Iop, Complex.ofReal_inv]
      rfl)
  exact ⟨c, r, hnorm, hr, hrc, hcI⟩

end GlobalTheory.UnitaryTheta.Constant
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinsumQuotientNonnegOfSwapConj
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory

theorem sum_nonneg_of_swap_conj_fintype (Q : Type) [AddCommGroup Q] [Fintype Q] (ψ : Q → ℂ)
    (P S L : Q →+ Q) (hL : Function.Injective L)
    (hP : ∀ x, P (P x) = P x) (hS : ∀ x, S (S x) = x)
    (hSP : ∀ x, S (P x) = S x - P (S x)) (hLP : ∀ x, L (P x) = P (L x))
    (hψ : ∀ x, ψ x = ψ (P x) * ψ (x - P x)) (hψS : ∀ x, ψ (S x) = ψ x)
    (hψL : ∀ x, ψ (L x) = (starRingEnd ℂ) (ψ x)) :
    ∃ r : ℝ, 0 ≤ r ∧ ∑ q : Q, ψ q = (r : ℂ) := by
  set A : Finset Q := Finset.univ.filter (fun x => P x = x) with hA
  set A' : Finset Q := Finset.univ.filter (fun x => P x = 0) with hA'
  have mA : ∀ x, x ∈ A ↔ P x = x := by intro x; simp [hA]
  have mA' : ∀ x, x ∈ A' ↔ P x = 0 := by intro x; simp [hA']
  have h1 : ∑ q : Q, ψ q = ∑ p ∈ A ×ˢ A', ψ p.1 * ψ p.2 := by
    refine Finset.sum_nbij' (fun q => (P q, q - P q)) (fun p => p.1 + p.2) ?_ ?_ ?_ ?_ ?_
    · intro q _
      simp [Finset.mem_product, mA, mA', hP]
    · intro p _
      exact Finset.mem_univ _
    · intro q _
      simp
    · intro p hp
      rw [Finset.mem_product, mA, mA'] at hp
      ext <;> simp [hp.1, hp.2]
    · intro q _
      exact hψ q
  have h2 : ∑ x ∈ A', ψ x = ∑ x ∈ A, ψ x := by
    refine Finset.sum_nbij' S S ?_ ?_ ?_ ?_ ?_
    · intro x hx
      rw [mA'] at hx
      rw [mA]
      have := hSP x
      rw [hx, map_zero] at this
      exact (sub_eq_zero.mp this.symm).symm
    · intro x hx
      rw [mA] at hx
      rw [mA']
      have := hSP x
      rw [hx] at this
      exact sub_eq_self.mp this.symm
    · intro x _
      exact hS x
    · intro x _
      exact hS x
    · intro x _
      exact (hψS x).symm
  have h3 : (starRingEnd ℂ) (∑ x ∈ A, ψ x) = ∑ x ∈ A, ψ x := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_bij (fun x _ => L x) ?_ ?_ ?_ ?_
    · intro x hx
      rw [mA] at hx
      rw [mA, ← hLP, hx]
    · intro x _ y _ h
      exact hL h
    · intro y hy
      obtain ⟨x, rfl⟩ := (Finite.injective_iff_surjective.mp hL) y
      refine ⟨x, ?_, rfl⟩
      rw [mA] at hy ⊢
      apply hL
      rw [hLP, hy]
    · intro x _
      exact (hψL x).symm
  obtain ⟨t, ht⟩ := Complex.conj_eq_iff_real.mp h3
  refine ⟨t * t, mul_self_nonneg t, ?_⟩
  rw [h1, Finset.sum_product, ← Finset.sum_mul_sum, h2, ht]
  push_cast
  rfl

theorem finsum_quotient_nonneg_of_swap_conj :
    ∀ (G : Type) [AddCommGroup G] (B : AddSubgroup G) [Finite (G ⧸ B)] (φ : G → ℂ) (P S L : G →+ G), (∀ x, ∀ w ∈ B, φ (x + w) = φ x) → (∀ w ∈ B, P w ∈ B ∧ S w ∈ B) → (∀ x, L x ∈ B ↔ x ∈ B) → (∀ x, P (P x) = P x) → (∀ x, S (S x) = x) → (∀ x, S (P x) = S x - P (S x)) → (∀ x, L (P x) = P (L x)) → (∀ x, φ x = φ (P x) * φ (x - P x)) → (∀ x, φ (S x) = φ x) → (∀ x, φ (L x) = (starRingEnd ℂ) (φ x)) → ∃ r : ℝ, 0 ≤ r ∧ ∑ᶠ q : G ⧸ B, φ q.out = (r : ℂ) := by
  intro G _ B _ φ P S L hper hB hLB hP hS hSP hLP hφ hφS hφL
  haveI : Fintype (G ⧸ B) := Fintype.ofFinite _
  have hout : ∀ x : G, φ (QuotientAddGroup.mk x : G ⧸ B).out = φ x := by
    intro x
    obtain ⟨w, hw⟩ := QuotientAddGroup.mk_out_eq_mul B x
    rw [hw]
    exact hper x w w.2
  let P' : G ⧸ B →+ G ⧸ B := QuotientAddGroup.map B B P (fun w hw => (hB w hw).1)
  let S' : G ⧸ B →+ G ⧸ B := QuotientAddGroup.map B B S (fun w hw => (hB w hw).2)
  let L' : G ⧸ B →+ G ⧸ B := QuotientAddGroup.map B B L (fun w hw => (hLB w).2 hw)
  have eP : ∀ x : G, P' (x : G ⧸ B) = (P x : G) := fun x => rfl
  have eS : ∀ x : G, S' (x : G ⧸ B) = (S x : G) := fun x => rfl
  have eL : ∀ x : G, L' (x : G ⧸ B) = (L x : G) := fun x => rfl
  rw [finsum_eq_sum_of_fintype]
  refine sum_nonneg_of_swap_conj_fintype (G ⧸ B) (fun q => φ q.out) P' S' L' ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [injective_iff_map_eq_zero]
    intro q hq
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      rw [eL, QuotientAddGroup.eq_zero_iff] at hq
      exact (QuotientAddGroup.eq_zero_iff x).2 ((hLB x).1 hq)
  all_goals
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      simp only [eP, eS, eL, ← QuotientAddGroup.mk_sub, hout]
      first
        | rw [hP]
        | rw [hS]
        | rw [hSP]
        | rw [hLP]
        | exact hφ x
        | exact hφS x
        | exact hφL x

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryThetaConstantEqInverseDeterminantPhase
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.SymConst

def ex (t : ℝ) : ℂ := Complex.exp (Real.pi * Complex.I * t)

theorem ex_add (s t : ℝ) : ex (s + t) = ex s * ex t := by
  rw [ex, ex, ex, ← Complex.exp_add]; congr 1; push_cast; ring

theorem ex_int (n : ℤ) : ex n = (-1 : ℂ) ^ n := by
  rw [ex, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]; congr 1; push_cast; ring

theorem ex_congr {s t : ℝ} (k : ℤ) (h : s = t + 2 * k) : ex s = ex t := by
  have : (2 * k : ℝ) = ((2 * k : ℤ) : ℝ) := by push_cast; ring
  rw [h, ex_add, this, ex_int, zpow_mul]; simp

theorem ex_neg (t : ℝ) : ex (-t) = (starRingEnd ℂ) (ex t) := by
  rw [ex, ex, ← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal]

theorem ex_eq {s t : ℝ} (h : ex s = ex t) : ∃ k : ℤ, s = t + 2 * k := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.1 h
  refine ⟨k, ?_⟩
  have h2 := congrArg Complex.im hk
  simp at h2
  have := Real.pi_pos
  apply mul_left_cancel₀ this.ne'
  linarith

theorem gauss_nonneg {V : Type} [AddCommGroup V] [Module ℂ V] (H : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ)
    (hH : ∀ x y, H y x = (starRingEnd ℂ) (H x y)) (s : ℝ) (A : AddSubgroup V) (hFG : A.FG)
    (hint : ∀ x ∈ A, ∀ y ∈ A, ∃ n : ℤ, (H x y).im = n)
    (hsd : ∀ x, (∀ y ∈ A, ∃ n : ℤ, (H x y).im = n) → x ∈ A)
    (hq : ∀ x ∈ A, ∃ n : ℤ, s * (H x x).re = n)
    (hsemi : ∀ x ∈ A, ∀ y ∈ A, ∃ k : ℤ,
      s * (H (x + y) (x + y)).re = s * (H x x).re + s * (H y y).re - (H x y).im + 2 * k)
    (a C : V →ₗ[ℂ] V) (ha : ∀ x y, H (a x) (a y) = H x y)
    (hC : ∀ x, C (x - a x) = (1 / 2 : ℂ) • (x + a x)) (hsurj : ∀ x, ∃ z, x = z - a z)
    (m : ℕ) (hm0 : 0 < m) (hm : ∀ x ∈ A, ∃ y ∈ A, a y ∈ A ∧ m • x = y - a y)
    (P S L B : V →ₗ[ℂ] V) (hPS : ∀ x ∈ A, P x ∈ A ∧ S x ∈ A) (hPP : ∀ x, P (P x) = P x)
    (hPH : ∀ x y, H (P x) y = H x (P y)) (hSS : ∀ x, S (S x) = x) (hSH : ∀ x y, H (S x) (S y) = H x y)
    (hSP : ∀ x, S (P x) = S x - P (S x)) (hPa : ∀ x, P (a x) = a (P x)) (hSa : ∀ x, S (a x) = a (S x))
    (hLB : ∀ x ∈ A, L x ∈ A ∧ B x ∈ A) (hLa : ∀ x, L (a x) = a (L x)) (hLP : ∀ x, L (P x) = P (L x))
    (hLH : ∀ x y, H (L x) (L y) = -H x y + (4 * m : ℕ) * H (B x) y) :
    ∃ r : ℝ, 0 ≤ r ∧ ∑ᶠ q : A ⧸ (subLa m A).addSubgroupOf A,
      (-1 : ℂ) ^ (round (s * (H ((q.out : A) : V) ((q.out : A) : V)).re)) *
        Complex.exp (-(Real.pi : ℂ) * H (C ((q.out : A) : V)) ((q.out : A) : V)) = r := by
  have hcomm : ∀ Q : V →ₗ[ℂ] V, (∀ x, Q (a x) = a (Q x)) → ∀ x, Q (C x) = C (Q x) := by
    intro Q hQ x
    obtain ⟨z, rfl⟩ := hsurj x
    rw [hC, map_sub, hQ, hC, map_smul, map_add (f := _), hQ]
  have hskew : ∀ x y, H (C x) y = -H x (C y) := by
    intro x y
    obtain ⟨z, rfl⟩ := hsurj x
    obtain ⟨w, rfl⟩ := hsurj y
    rw [hC, hC]
    simp [ha, Complex.conj_ofNat]
    ring
  have him : ∀ x y, (H y x).im = -(H x y).im := fun x y => by rw [hH x y]; simp
  have hre : ∀ x y, (H y x).re = (H x y).re := fun x y => by rw [hH x y]; simp
  have him0 : ∀ x, (H x x).im = 0 := fun x => by have := him x x; linarith
  have hCim : ∀ x y, (H (C x) y).im = (H (C y) x).im := fun x y => by
    rw [hskew x y, him x (C y)]; simp
  have hCre : ∀ x, (H (C x) x).re = 0 := fun x => by
    have h1 := congrArg Complex.re (hskew x x)
    rw [Complex.neg_re, hre (C x) x] at h1
    linarith
  have hmem : ∀ w : A, w ∈ (subLa m A).addSubgroupOf A ↔ ∃ v ∈ A, m • v = (w : V) := fun w => by
    simp [AddSubgroup.mem_addSubgroupOf, subLa]
  haveI : AddGroup.FG A := (AddGroup.fg_iff_addSubgroup_fg A).2 hFG
  haveI : Finite (A ⧸ (subLa m A).addSubgroupOf A) := by
    refine AddCommGroup.finite_of_fg_torsion _ fun q => ?_
    induction q using QuotientAddGroup.induction_on with
    | H x =>
      refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨m, hm0, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, hmem]
      exact ⟨x, x.2, rfl⟩
  let ψ : V → ℝ := fun x => s * (H x x).re - (H (C x) x).im
  have hφ : ∀ x : A, (-1 : ℂ) ^ (round (s * (H (x : V) (x : V)).re)) *
      Complex.exp (-(Real.pi : ℂ) * H (C (x : V)) (x : V)) = ex (ψ x) := by
    intro x
    obtain ⟨n, hn⟩ := hq x x.2
    simp only [ψ]
    rw [hn, round_intCast, sub_eq_add_neg, ex_add, ex_int, ex]
    congr 2
    rw [← Complex.re_add_im (H (C x) x), hCre]
    simp
    ring
  simp only [hφ]
  have res : ∀ Q : V →ₗ[ℂ] V, (∀ x ∈ A, Q x ∈ A) → ∃ Q' : A →+ A, ∀ x : A, (Q' x : V) = Q x := fun Q hQ =>
    ⟨(Q.toAddMonoidHom.comp A.subtype).codRestrict A fun x => hQ x x.2, fun _ => rfl⟩
  obtain ⟨P', hP'⟩ := res P fun x hx => (hPS x hx).1
  obtain ⟨S', hS'⟩ := res S fun x hx => (hPS x hx).2
  obtain ⟨L', hL'⟩ := res L fun x hx => (hLB x hx).1
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
  refine GlobalTheory.finsum_quotient_nonneg_of_swap_conj A _ (fun x : A => ex (ψ x))
    P' S' L' ?_ ?_ ?_ (fun x => Subtype.ext (by simp [hP', hPP])) (fun x => Subtype.ext (by simp [hS', hSS]))
    (fun x => Subtype.ext (by simp [hP', hS', hSP])) (fun x => Subtype.ext (by simp [hP', hL', hLP])) ?_ ?_ ?_
  · intro x w hw
    obtain ⟨v, hv, hvw⟩ := (hmem w).1 hw
    obtain ⟨y, hy, hay, hyv⟩ := hm v hv
    have hw' : (w : V) = y - a y := hvw.symm.trans hyv
    obtain ⟨k1, h1⟩ := hsemi x x.2 w w.2
    obtain ⟨k2, h2⟩ := hsemi w w.2 _ hay
    obtain ⟨k3, h3⟩ := hint x x.2 y hy
    have e1 : (w : V) + a y = y := by rw [hw']; abel
    rw [e1, ha] at h2
    have e2 : (H (C w) x).im = -((H x y).im + (H x (a y)).im) / 2 := by
      rw [hw', hC, him y x, him (a y) x]; simp; ring
    have e3 : (H (C w) w).im = -(H y (a y)).im := by
      have := him y (a y)
      rw [hw', hC]; simp [ha, him0]; linarith
    have e4 : (H w (a y)).im = (H y (a y)).im := by rw [hw']; simp [him0]
    have e5 : (H x w).im = (H x y).im - (H x (a y)).im := by rw [hw']; simp
    have e6 : (H (C (x + w)) (x + w)).im = (H (C x) x).im + (H (C w) w).im + 2 * (H (C w) x).im := by
      have := hCim x w
      simp; linarith
    obtain ⟨k4, h4⟩ := hint x x.2 _ hay
    obtain ⟨k5, h5⟩ := hint y hy _ hay
    refine ex_congr (k1 - k2 + k4 + k5) ?_
    simp only [ψ, AddSubgroup.coe_add]
    push_cast
    linarith
  · intro w hw
    obtain ⟨v, hv, hvw⟩ := (hmem w).1 hw
    exact ⟨(hmem _).2 ⟨P v, (hPS v hv).1, by rw [hP', ← hvw, map_nsmul]⟩,
      (hmem _).2 ⟨S v, (hPS v hv).2, by rw [hS', ← hvw, map_nsmul]⟩⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨v, hv, hvw⟩ := (hmem _).1 hx
      rw [hL'] at hvw
      have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm0.ne'
      refine (hmem _).2 ⟨(m : ℂ)⁻¹ • (x : V), hsd _ fun y hy => ?_, ?_⟩
      · obtain ⟨k1, h1⟩ := hint v hv _ (hLB y hy).1
        obtain ⟨k2, h2⟩ := hint _ (hLB x x.2).2 y hy
        have h3 := congrArg Complex.im (hLH x y)
        rw [← hvw] at h3
        simp at h3
        refine ⟨4 * k2 - k1, ?_⟩
        have : ((m : ℂ))⁻¹ = ((m⁻¹ : ℝ) : ℂ) := by simp
        rw [map_smul, LinearMap.smul_apply, smul_eq_mul, this, Complex.im_ofReal_mul]
        push_cast
        field_simp
        rw [h1, h2] at h3
        linarith
      · rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hmC, one_smul]
    · intro hx
      obtain ⟨v, hv, hvw⟩ := (hmem _).1 hx
      exact (hmem _).2 ⟨L v, (hLB v hv).1, by rw [hL', ← hvw, map_nsmul]⟩
  · intro x
    rw [← ex_add]
    congr 1
    simp only [ψ, AddSubgroup.coe_sub, hP']
    have e1 : H (P x) (P x) = H x (P x) := by rw [hPH, hPP]
    have e2 : H (C (P x)) (P x) = H (C x) (P x) := by rw [← hcomm P hPa, hPH, hPP]
    have e3 : H (C (P x)) x = H (C x) (P x) := by rw [← hcomm P hPa, hPH]
    have e4 := hPH x x
    simp only [map_sub, LinearMap.sub_apply, e1, e2, e3, e4, Complex.sub_re, Complex.sub_im]
    ring
  · intro x
    simp only [ψ, hS']
    rw [← hcomm S hSa, hSH, hSH]
  · intro x
    rw [← ex_neg]
    simp only [ψ, hL']
    rw [← hcomm L hLa, hLH, hLH]
    obtain ⟨y, hy, hay, hyv⟩ := hm x x.2
    have e1 : (2 * m : ℂ) • C x = y + a y := by
      have := hC y
      rw [← hyv, ← Nat.cast_smul_eq_nsmul ℂ, map_smul] at this
      rw [mul_smul, this, smul_smul]; simp
    obtain ⟨k1, h1⟩ := hint _ (hLB _ (add_mem hy hay)).2 x x.2
    rw [← e1] at h1
    obtain ⟨k2, h2⟩ := hq _ (add_mem (hLB x x.2).2 x.2)
    obtain ⟨k3, h3⟩ := hq _ (hLB x x.2).2
    obtain ⟨k4, h4⟩ := hq _ x.2
    have e2 := hre (B x) x
    simp [e2] at h1 h2
    refine ex_congr (m * (k2 - k3 - k4) - k1) ?_
    simp
    rw [← h1, ← h2, ← h3, ← h4]
    ring

variable {D : D7} {N N' : ℕ}

def hfL (T : Tor D) : VC D N N' →ₗ[ℂ] VC D N N' →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (Hf D T)
    (fun x y z => by simp only [ThetaLine.Hf_eq, ThetaLine.sq_add_left, add_div])
    (fun c x y => by simp only [ThetaLine.Hf_eq, ThetaLine.sq_smul_left, RingHom.id_apply, smul_eq_mul, mul_div_assoc])
    (fun x y z => by simp only [ThetaLine.Hf_eq, ThetaLine.sq_add_right, add_div])
    (fun c x y => by simp only [ThetaLine.Hf_eq, ThetaLine.sq_smul_right, smul_eq_mul]; ring)

theorem hfL_apply (T : Tor D) (x y : VC D N N') : hfL T x y = Hf D T x y := rfl

theorem hfL_swap (T : Tor D) (x y : VC D N N') : hfL T y x = (starRingEnd ℂ) (hfL T x y) := by
  simp [hfL_apply, Hf, Complex.conj_ofReal, mul_comm]

theorem semi (T : Tor D) (A : AddSubgroup (VC D N N')) (hq : ∀ x ∈ A, ∃ m : ℤ, qH D T x = m)
    (th : VC D N N' → ℂ) (hth : th ∈ ThSp D T A) (h0 : th ≠ 0) :
    ∀ x ∈ A, ∀ y ∈ A, ∃ k : ℤ, qH D T (x + y) = qH D T x + qH D T y - (Hf D T x y).im + 2 * k := by
  intro x hx y hy
  have hal : ∀ x ∈ A, al D T x = ex (qH D T x) := fun x hx => by
    obtain ⟨n, hn⟩ := hq x hx
    have e : al D T x = (-1 : ℂ) ^ (round (qH D T x)) := rfl
    rw [e, hn, round_intCast, ex_int]
  obtain ⟨z, hz⟩ := Function.ne_iff.1 h0
  have h1 := hth.2 x hx z
  have h2 := hth.2 y hy (z + x)
  have h3 := hth.2 _ (add_mem hx hy) z
  rw [hal _ hx] at h1
  rw [hal _ hy] at h2
  rw [hal _ (add_mem hx hy)] at h3
  simp only [U, ← hfL_apply, ← add_assoc] at h1 h2 h3
  have h4 : th (z + x + y) ≠ 0 := by
    intro h; rw [h] at h3; apply hz; rw [← h3]; simp
  apply ex_eq
  rw [← h2, ← h3] at h1
  have e : Complex.exp (-(Real.pi : ℂ) * hfL T (z + x) y - Real.pi * hfL T y y / 2) *
      Complex.exp (-(Real.pi : ℂ) * hfL T z x - Real.pi * hfL T x x / 2) =
      ex (-(hfL T x y).im) * Complex.exp (-(Real.pi : ℂ) * hfL T z (x + y) - Real.pi * hfL T (x + y) (x + y) / 2) := by
    rw [ex, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have e1 := Complex.sub_conj (hfL T x y)
    rw [← hfL_swap] at e1
    simp only [map_add (f := _), LinearMap.add_apply]
    push_cast at e1 ⊢
    linear_combination (-(Real.pi : ℂ) / 2) * e1
  rw [sub_eq_add_neg, ex_add, ex_add, ← hfL_apply]
  apply mul_right_cancel₀ (mul_ne_zero h4 (Complex.exp_ne_zero
    (-(Real.pi : ℂ) * hfL T z (x + y) - Real.pi * hfL T (x + y) (x + y) / 2)))
  linear_combination -h1 + ex (qH D T x) * ex (qH D T y) * th (z + x + y) * e

theorem const_of_symm : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A A₁ : AddSubgroup (VC D N N')), KLat D (tor0 D cc δ) A → KLat D (tor0 D cc δ) A₁ → ∀ (u : VC D N N' ≃ₗ[ℂ] VC D N N'), (∀ z w, Hf D (tor0 D cc δ) (u z) (u w) = Hf D (tor0 D cc δ) z w) → (∀ x, x ∈ A ↔ u x ∈ A₁) → LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) ≠ 0 → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ A, ∃ y ∈ A, u.symm y ∈ A ∧ m • x = y - u.symm y) → ∀ (P S : VC D N N' →ₗ[ℂ] VC D N N'), (∀ x ∈ A, P x ∈ A ∧ S x ∈ A) → (∀ x, P (P x) = P x) → (∀ x y, Hf D (tor0 D cc δ) (P x) y = Hf D (tor0 D cc δ) x (P y)) → (∀ x, S (S x) = x) → (∀ x y, Hf D (tor0 D cc δ) (S x) (S y) = Hf D (tor0 D cc δ) x y) → (∀ x, S (P x) = S x - P (S x)) → (∀ x, P (u x) = u (P x)) → (∀ x, S (u x) = u (S x)) → (∀ M : ℕ, 0 < M → ∃ L B : VC D N N' →ₗ[ℂ] VC D N N', (∀ x ∈ A, L x ∈ A ∧ B x ∈ A) ∧ (∀ x, L (u x) = u (L x)) ∧ (∀ x, B (u x) = u (B x)) ∧ (∀ x, L (P x) = P (L x)) ∧ (∀ x y, Hf D (tor0 D cc δ) (B x) y = Hf D (tor0 D cc δ) x (B y)) ∧ ∀ x y, Hf D (tor0 D cc δ) (L x) (L y) = -Hf D (tor0 D cc δ) x y + M * Hf D (tor0 D cc δ) (B x) y) → ∀ th ∈ ThSp D (tor0 D cc δ) A, (fun z => th (u.symm z)) = ((‖LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N'))‖ : ℂ) / LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N'))) • Iop D (tor0 D cc δ) A A₁ th := by
  intro D cc δ hc N N' A A₁ hA hA₁ u hu huA hdt ⟨m, hm0, hm⟩ P S hPS hPP hPH hSS hSH hSP hPu hSu hLB th hth
  by_cases h0 : th = 0
  · subst h0
    funext z
    simp [Iop, U]
  obtain ⟨-, -, hint, hsd, hFG, -, hq⟩ :=
    ThetaLine.theta_line D (InducedType.induced_type D).1 cc δ hc N N' A hA
  obtain ⟨L, B, hL1, hLu, -, hLP, -, hLH⟩ := hLB (4 * m) (by omega)
  set a : VC D N N' →ₗ[ℂ] VC D N N' := (u.symm : VC D N N' →ₗ[ℂ] VC D N N') with ha
  let e := LinearMap.equivOfDetNeZero _ hdt
  have he : ∀ x, e x = x - u.symm x := fun x => rfl
  let C : VC D N N' →ₗ[ℂ] VC D N N' := ((1 / 2 : ℂ) • (LinearMap.id + a)) ∘ₗ (e.symm : VC D N N' →ₗ[ℂ] VC D N N')
  have hC : ∀ x, C (x - u.symm x) = (1 / 2 : ℂ) • (x + u.symm x) := fun x => by
    rw [← he]; simp [C, ha]
  have hcom : ∀ Q : VC D N N' →ₗ[ℂ] VC D N N', (∀ x, Q (u x) = u (Q x)) → ∀ x, Q (a x) = a (Q x) := by
    intro Q hQ x
    apply u.injective
    rw [← hQ]; simp [ha]
  obtain ⟨c, r, hc1, hr, hcr, hfin⟩ := GlobalTheory.UnitaryTheta.Constant.pull_eq_gauss_smul_intertwiner D cc δ hc N N' A A₁ hA hA₁ u hu huA hdt C hC m hm0 hm th hth h0
  obtain ⟨ρ, hρ, hsum⟩ := gauss_nonneg (hfL (tor0 D cc δ)) (hfL_swap _) (Real.sqrt D.host.d / 2) A hFG hint hsd hq
    (semi _ A hq th hth h0) a C (fun x y => by rw [hfL_apply, ← hu]; simp [ha, hfL_apply]) hC
    (fun x => ⟨e.symm x, (e.apply_symm_apply x).symm.trans (he _)⟩) m hm0 hm P S L B hPS hPP hPH hSS hSH hSP
    (hcom P hPu) (hcom S hSu) hL1 (hcom L hLu) hLP hLH
  have hcr' : c = r * (LinearMap.det (LinearMap.id - a))⁻¹ * ρ := by rw [hcr, ← hsum]; rfl
  rw [hfin]
  congr 1
  have hn : r * ρ = ‖LinearMap.det (LinearMap.id - a)‖ := by
    rw [hcr'] at hc1
    simp only [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, abs_of_nonneg hρ] at hc1
    have := norm_ne_zero_iff.2 hdt
    field_simp at hc1
    exact hc1
  rw [hcr', ← hn]
  push_cast
  ring

end GlobalTheory.SymConst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryThetaConstantEqInverseDeterminantPhaseStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryThetaConstant_eq_inverseDeterminantPhase : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (A A₁ : AddSubgroup (VC D N N')), KLat D (tor0 D cc δ) A → KLat D (tor0 D cc δ) A₁ → ∀ (u : VC D N N' ≃ₗ[ℂ] VC D N N'), (∀ z w, Hf D (tor0 D cc δ) (u z) (u w) = Hf D (tor0 D cc δ) z w) → (∀ x, x ∈ A ↔ u x ∈ A₁) → LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N')) ≠ 0 → (∃ m : ℕ, 0 < m ∧ ∀ x ∈ A, ∃ y ∈ A, u.symm y ∈ A ∧ m • x = y - u.symm y) → ∀ (P S : VC D N N' →ₗ[ℂ] VC D N N'), (∀ x ∈ A, P x ∈ A ∧ S x ∈ A) → (∀ x, P (P x) = P x) → (∀ x y, Hf D (tor0 D cc δ) (P x) y = Hf D (tor0 D cc δ) x (P y)) → (∀ x, S (S x) = x) → (∀ x y, Hf D (tor0 D cc δ) (S x) (S y) = Hf D (tor0 D cc δ) x y) → (∀ x, S (P x) = S x - P (S x)) → (∀ x, P (u x) = u (P x)) → (∀ x, S (u x) = u (S x)) → (∀ M : ℕ, 0 < M → ∃ L B : VC D N N' →ₗ[ℂ] VC D N N', (∀ x ∈ A, L x ∈ A ∧ B x ∈ A) ∧ (∀ x, L (u x) = u (L x)) ∧ (∀ x, B (u x) = u (B x)) ∧ (∀ x, L (P x) = P (L x)) ∧ (∀ x y, Hf D (tor0 D cc δ) (B x) y = Hf D (tor0 D cc δ) x (B y)) ∧ ∀ x y, Hf D (tor0 D cc δ) (L x) (L y) = -Hf D (tor0 D cc δ) x y + M * Hf D (tor0 D cc δ) (B x) y) → ∀ th ∈ ThSp D (tor0 D cc δ) A, (fun z => th (u.symm z)) = ((‖LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N'))‖ : ℂ) / LinearMap.det (LinearMap.id - (u.symm : VC D N N' →ₗ[ℂ] VC D N N'))) • Iop D (tor0 D cc δ) A A₁ th := by
  first | exact @GlobalTheory.SymConst.const_of_symm | exact GlobalTheory.SymConst.const_of_symm | (intros; apply GlobalTheory.SymConst.const_of_symm <;> assumption)
end
