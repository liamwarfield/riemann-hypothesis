module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIotaOQOfData
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlgClosureEmbeddingExtendingOnAlgebraic
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FstMemClosureNatCast
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationRingIntClosure
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.InertCompare Classical

namespace GlobalTheory.CompletedBasis

section General

variable {l : ℕ} [Fact l.Prime]

theorem isCompact_closure_range {A V : Type} [AddCommGroup A] [Module.Finite ℤ A] [NormedAddCommGroup V]
    [NormedSpace ℚ_[l] V] (f : A →+ V) : IsCompact (closure (Set.range f)) := by
  obtain ⟨n, b, hb⟩ := Module.Finite.exists_fin (R := ℤ) (M := A)
  let g : (Fin n → ℤ_[l]) → V := fun c => ∑ i, ((c i : ℤ_[l]) : ℚ_[l]) • f (b i)
  have hg : Continuous g := by
    refine continuous_finsetSum _ fun i _ => ?_
    exact (continuous_subtype_val.comp (continuous_apply i)).smul continuous_const
  have hc : IsCompact (Set.range g) := isCompact_range hg
  refine hc.of_isClosed_subset isClosed_closure (closure_minimal ?_ hc.isClosed)
  rintro _ ⟨a, rfl⟩
  have ha : a ∈ Submodule.span ℤ (Set.range b) := hb ▸ Submodule.mem_top
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 ha
  refine ⟨fun i => (c i : ℤ_[l]), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [g, map_sum, map_zsmul, PadicInt.coe_intCast, Int.cast_smul_eq_zsmul]

variable {K : Type} [Field K] [NumberField K] (ρ : K →+* ℂ_[l])

def intClosure : Subring ℂ_[l] := (ρ.comp (algebraMap (𝓞 K) K)).range.topologicalClosure

theorem coe_intClosure : (intClosure ρ : Set ℂ_[l]) = closure (Set.range fun a : 𝓞 K => ρ (a : K)) := rfl

theorem isCompact_intClosure : IsCompact (intClosure ρ : Set ℂ_[l]) :=
  isCompact_closure_range (l := l) (ρ.comp (algebraMap (𝓞 K) K)).toAddMonoidHom

theorem mem_intClosure (a : 𝓞 K) : ρ (a : K) ∈ intClosure ρ := subset_closure ⟨a, rfl⟩

theorem norm_le_one_of_mem {x : ℂ_[l]} (hx : x ∈ intClosure ρ) : ‖x‖ ≤ 1 := by
  by_contra h
  push Not at h
  obtain ⟨C, hC⟩ := (isCompact_intClosure ρ).isBounded.exists_norm_le
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
  have := hC _ ((intClosure ρ).pow_mem hx n)
  rw [norm_pow] at this
  exact absurd hn (not_lt.2 this)

variable {E : Type} [Field E] [NumberField E] [Algebra K E] {ι : Type} [Fintype ι] (σ : ι → E →+* ℂ_[l])

end General

section Host

variable (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l])

def rhoBase : D.host.E →+* ℂ_[l] :=
  lam.comp (D.host.φ₀.codRestrict Qbar fun x => by
    rw [mem_algebraicClosure_iff]
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.host.φ₀.toRatAlgHom)

theorem rhoBase_apply (x : D.host.E) : rhoBase D lam x = lamC lam (D.host.φ₀ x) := by
  unfold lamC
  rw [dite_eq_left]
  rfl

def rhoK : D.host.K →+* ℂ_[l] := (rhoBase D lam).comp (algebraMap D.host.K D.host.E)

theorem fst_image_OKp : Prod.fst '' GL3Theta.OKp D lam = (intClosure (rhoK D lam) : Set ℂ_[l]) := by
  let f : 𝓞 D.host.K →+ ℂ_[l] × ℂ_[l] :=
    (((rhoK D lam).prod (((rhoBase D lam).comp (D.host.conj : D.host.E →+* D.host.E)).comp
      (algebraMap D.host.K D.host.E))).comp (algebraMap (𝓞 D.host.K) D.host.K)).toAddMonoidHom
  have hf : (fun a : 𝓞 D.host.K => (GL3Theta.tauK D lam (a : D.host.K), GL3Theta.tauKc D lam (a : D.host.K))) = f := by
    funext a
    exact Prod.ext (rhoBase_apply D lam _).symm (rhoBase_apply D lam _).symm
  unfold GL3Theta.OKp
  rw [hf, image_closure_of_isCompact (isCompact_closure_range (l := l) f) continuous_fst.continuousOn,
    ← Set.range_comp, coe_intClosure]
  rfl

end Host

end GlobalTheory.CompletedBasis
end
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.TwoAdicFirst

theorem cont_coe : Continuous fun z : ℤ_[2] => algebraMap ℚ_[2] ℂ_[2] (z : ℚ_[2]) := by
  fun_prop

theorem coe_mem_closure (z : ℤ_[2]) :
    algebraMap ℚ_[2] ℂ_[2] (z : ℚ_[2]) ∈ closure (Set.range (Nat.cast : ℕ → ℂ_[2])) := by
  refine map_mem_closure (f := fun z : ℤ_[2] => algebraMap ℚ_[2] ℂ_[2] (z : ℚ_[2])) cont_coe
    (PadicInt.denseRange_natCast z) ?_
  rintro _ ⟨n, rfl⟩
  exact ⟨n, by simp⟩

theorem exists_root (k : ℕ) : ∃ z : ℤ_[2], z ^ 2 - z + 2 * (k : ℤ_[2]) = 0 := by
  let F : Polynomial ℤ_[2] := Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (2 * (k : ℤ_[2]))
  have h0 : F.eval 0 = 2 * (k : ℤ_[2]) := by simp [F]
  have h1 : F.derivative.eval 0 = -1 := by simp [F]
  have hn : ‖F.eval 0‖ < ‖F.derivative.eval 0‖ ^ 2 := by
    rw [h0, h1, norm_neg, norm_one, one_pow, norm_mul]
    have h2 : ‖(2 : ℤ_[2])‖ < 1 := by
      have := PadicInt.norm_p (p := 2)
      norm_num at this
      rw [this]; norm_num
    have hk : ‖(k : ℤ_[2])‖ ≤ 1 := PadicInt.norm_le_one _
    nlinarith [norm_nonneg (k : ℤ_[2]), norm_nonneg (2 : ℤ_[2])]
  obtain ⟨z, hz, -⟩ := hensels_lemma hn
  refine ⟨z, ?_⟩
  simpa [F] using hz

open GlobalTheory.CompletedBasis

theorem sq_neg_mem (d : ℕ) (hd : d % 8 = 7) {s : ℂ_[2]} (hs : s ^ 2 = -(d : ℂ_[2])) :
    s ∈ (algebraMap ℚ_[2] ℂ_[2]).fieldRange := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, d + 1 = 8 * k := ⟨(d + 1) / 8, by omega⟩
  obtain ⟨z, hz⟩ := exists_root k
  let φ : ℤ_[2] →+* ℂ_[2] := (algebraMap ℚ_[2] ℂ_[2]).comp PadicInt.Coe.ringHom
  set u : ℂ_[2] := φ (2 * z - 1) with hu
  have hz' : φ z ^ 2 - φ z + 2 * (k : ℂ_[2]) = 0 := by
    have := congrArg φ hz
    simpa only [map_add (f := _), map_sub, map_mul, map_pow, map_ofNat, map_natCast, map_zero] using this
  have hk' : (d : ℂ_[2]) + 1 = 8 * (k : ℂ_[2]) := by exact_mod_cast hk
  have hu2 : u ^ 2 = -(d : ℂ_[2]) := by
    rw [hu]
    simp only [map_sub, map_mul, map_ofNat, map_one]
    linear_combination 4 * hz' + hk'
  have h : (s - u) * (s + u) = 0 := by linear_combination hs - hu2
  rcases mul_eq_zero.1 h with h | h
  · exact ⟨_, (sub_eq_zero.1 h).symm⟩
  · refine ⟨-(PadicInt.Coe.ringHom (2 * z - 1)), ?_⟩
    rw [map_neg]
    change -u = s
    linear_combination -h

variable (D : D7) (lam : Qbar →+* ℂ_[2])

theorem rhoBase_mem_of_K (x : D.host.K) : rhoBase D lam (x : D.host.E) ∈ (algebraMap ℚ_[2] ℂ_[2]).fieldRange := by
  let S : Subfield D.host.E := ((algebraMap ℚ_[2] ℂ_[2]).fieldRange).comap (rhoBase D lam)
  let F : IntermediateField ℚ D.host.E := S.toIntermediateField fun q => by
    refine ⟨(q : ℚ_[2]), ?_⟩
    change _ = rhoBase D lam (algebraMap ℚ D.host.E q)
    rw [eq_ratCast, map_ratCast, map_ratCast]
  have hd16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  have hb : D.host.sqd ∈ F := by
    change rhoBase D lam (D.host.sqd) ∈ (algebraMap ℚ_[2] ℂ_[2]).fieldRange
    refine sq_neg_mem D.host.d (by omega) ?_
    rw [← map_pow, D.host.sqd_sq, map_neg, map_natCast]
  have hle : D.host.K ≤ F := IntermediateField.adjoin_simple_le_iff.2 hb
  exact hle x.2

theorem rhoK_mem (a : 𝓞 D.host.K) :
    rhoK D lam (a : D.host.K) ∈ closure (Set.range (Nat.cast : ℕ → ℂ_[2])) := by
  obtain ⟨q, hq⟩ := rhoBase_mem_of_K D lam (a : D.host.K)
  have hq' : algebraMap ℚ_[2] ℂ_[2] q = rhoK D lam (a : D.host.K) := hq
  have hn : ‖q‖ ≤ 1 := by
    have := norm_le_one_of_mem (rhoK D lam) (mem_intClosure (rhoK D lam) a)
    rwa [← hq', norm_algebraMap'] at this
  have := coe_mem_closure ⟨q, hn⟩
  rwa [show ((⟨q, hn⟩ : ℤ_[2]) : ℚ_[2]) = q from rfl, hq'] at this

theorem fst_mem_closure_natCast :
    ∀ (D : D7) (lam : Qbar →+* ℂ_[2]), ∀ α ∈ GL3Theta.OKp D lam,
      α.1 ∈ closure (Set.range (Nat.cast : ℕ → ℂ_[2])) := by
  intro D lam α hα
  have h1 : α.1 ∈ (intClosure (rhoK D lam) : Set ℂ_[2]) := by
    rw [← fst_image_OKp]
    exact ⟨α, hα, rfl⟩
  rw [coe_intClosure] at h1
  refine closure_minimal ?_ isClosed_closure h1
  rintro _ ⟨a, rfl⟩
  exact rhoK_mem D lam a

end GlobalTheory.TwoAdicFirst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralHeisKerSumDiag
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralCharImEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralCharImEqZero
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical Pointwise

namespace GlobalTheory.UnitaryTheta

theorem setIntegral_mul_char_eq_zero {V : Type} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [SecondCountableTopology V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (Λ : AddSubgroup V) [Countable Λ] (Fd : Set V)
    (hF : IsAddFundamentalDomain Λ Fd μ) (f : V → ℂ) (hf : ∀ x y, f (x + y) = f x * f y)
    (hΛ : ∀ y ∈ Λ, f y = 1) (t : V) (ht : f t = -1) : ∫ z in Fd, f z ∂μ = 0 := by
  have hq : MeasurePreserving (fun x => t + x) μ μ := measurePreserving_add_left μ t
  have hF' : IsAddFundamentalDomain Λ ((fun x => t + x) ⁻¹' Fd) μ :=
    hF.preimage_of_equiv hq.quasiMeasurePreserving (e := id) Function.bijective_id
      (fun g x => by simp [AddSubgroup.vadd_def, add_left_comm])
  have h1 : ∫ z in (fun x => t + x) ⁻¹' Fd, f z ∂μ = ∫ z in Fd, f z ∂μ :=
    hF'.setIntegral_eq hF (fun g x => by simp [AddSubgroup.vadd_def, hf, hΛ g g.2])
  have h2 : ∫ z in (fun x => t + x) ⁻¹' Fd, f (t + z) ∂μ = ∫ z in Fd, f z ∂μ :=
    hq.setIntegral_preimage_emb (measurableEmbedding_addLeft t) f Fd
  have h3 : ∫ z in (fun x => t + x) ⁻¹' Fd, f (t + z) ∂μ = - ∫ z in Fd, f z ∂μ := by
    simp only [hf, ht, neg_one_mul, integral_neg, h1]
  linear_combination (h3 - h2) / 2

theorem setIntegral_char_im_eq_zero :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [Countable Λ] (Fd : Set V), IsAddFundamentalDomain Λ Fd μ → ∀ v : V, v ≠ 0 → (∀ y ∈ Λ, ∃ m : ℤ, (H v y).im = m) → ∫ z in Fd, cexp (2 * π * I * ((H v z).im : ℂ)) ∂μ = 0 := by
  intro V _ _ _ _ _ μ _ H hH Λ _ Fd hF v hv hint
  haveI : ProperSpace V := FiniteDimensional.proper ℂ V
  have hpos := hH.2 v hv
  set r : ℝ := (H v v).re with hr
  refine setIntegral_mul_char_eq_zero μ Λ Fd hF (fun z => cexp (2 * π * I * ((H v z).im : ℂ)))
    (fun x y => ?_) (fun y hy => ?_) (((-(1 / (2 * r)) : ℝ) * I : ℂ) • v) ?_
  · simp only [map_add (f := _), add_im, ofReal_add, mul_add, Complex.exp_add]
  · obtain ⟨m, hm⟩ := hint y hy
    simp only [hm, ofReal_intCast]
    rw [mul_comm]
    exact Complex.exp_int_mul_two_pi_mul_I m
  · have e : (H v (((-(1 / (2 * r)) : ℝ) * I : ℂ) • v)).im = 1 / 2 := by
      rw [LinearMap.map_smulₛₗ, smul_eq_mul, map_mul, conj_ofReal, conj_I]
      simp only [mul_im, mul_re, ofReal_re, ofReal_im, neg_re, neg_im, I_re, I_im, ← hr]
      field_simp
      ring
    simp only [e]
    rw [← Complex.exp_pi_mul_I]
    congr 1
    push_cast
    ring

end GlobalTheory.UnitaryTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralCharImEqZeroStatement
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setIntegral_cexp_im_herm_eq_zero : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [Countable Λ] (Fd : Set V), IsAddFundamentalDomain Λ Fd μ → ∀ v : V, v ≠ 0 → (∀ y ∈ Λ, ∃ m : ℤ, (H v y).im = m) → ∫ z in Fd, cexp (2 * π * I * ((H v z).im : ℂ)) ∂μ = 0 := by
  first | exact @GlobalTheory.UnitaryTheta.setIntegral_char_im_eq_zero | exact GlobalTheory.UnitaryTheta.setIntegral_char_im_eq_zero | (intros; apply GlobalTheory.UnitaryTheta.setIntegral_char_im_eq_zero <;> assumption)
end
end

open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta

theorem heis_kerSum_diag {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (hH : IsPosHerm H)
    (Λ : AddSubgroup V) (α : V → ℂ) (r z : V) :
    Heisenberg₂ H r (kerSum H Λ α z) z * cexp (-(π : ℂ) * H z z) =
      ∑' x : Λ, (α x * cexp (-(π : ℂ) * H x r - (π : ℂ) * H x x / 2 - (π : ℂ) * H r r / 2
        + 2 * π * I * ((H x r).im : ℂ))) * cexp (2 * π * I * ((H (r + x) z).im : ℂ)) := by
  simp only [Heisenberg₂, kerSum]
  rw [← tsum_mul_right, ← tsum_mul_right]
  refine tsum_congr fun x => ?_
  simp only [kerTerm, mul_assoc, ← Complex.exp_add]
  congr 2
  have hc : ∀ w : ℂ, (starRingEnd ℂ) w = w - 2 * (w.im : ℂ) * I := by
    intro w
    apply Complex.ext <;> simp
    ring
  simp only [map_add (f := _), LinearMap.add_apply, Complex.add_im, Complex.ofReal_add]
  rw [hH.1 z r, hH.1 z x, hH.1 r x]
  simp only [hc]
  ring

theorem integral_heis_kerSum_diag : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ (Λ Λ' : AddSubgroup V) [DiscreteTopology Λ], Λ' ≤ Λ → ∀ α : V → ℂ, IsSemichar H Λ α → ∀ Fd : Set V, IsAddFundamentalDomain Λ' Fd μ → μ Fd ≠ ⊤ → ∀ r : V, (∀ y ∈ Λ', ∃ m : ℤ, (H r y).im = m) → IntegrableOn (fun z => Heisenberg₂ H r (kerSum H Λ α z) z * cexp (-(π : ℂ) * H z z)) Fd μ ∧ ∫ z in Fd, Heisenberg₂ H r (kerSum H Λ α z) z * cexp (-(π : ℂ) * H z z) ∂μ = if r ∈ Λ then α (-r) * (μ.real Fd : ℂ) else 0 := by
  intro V _ _ _ _ _ μ _ H hH Λ Λ' _ hle α hα Fd hFd hFdfin r hr
  have hΛc : Countable Λ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hΛ'c : Countable Λ' := by
    have h1 : (Λ : Set V).Countable := Set.countable_coe_iff.mp hΛc
    exact (h1.mono (fun y hy => hle hy)).to_subtype
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ x : V, ‖H x r‖ ≤ K * ‖x‖ :=
    ⟨‖LinearMap.toContinuousLinearMap (H.flip r)‖, fun x => by
      simpa using (LinearMap.toContinuousLinearMap (H.flip r)).le_opNorm x⟩
  have hcontH : ∀ v : V, Continuous fun z : V => H z v := fun v =>
    Continuous.congr (H.flip v).continuous_of_finiteDimensional
      (fun z => LinearMap.flip_apply _ _ _)
  have hcim : ∀ v : V, Continuous fun z : V => (H v z).im := by
    intro v
    have e : (fun z : V => (H v z).im) = fun z => -(H z v).im := by
      funext z
      rw [hH.1 v z, Complex.conj_im]
    rw [e]
    exact (Complex.continuous_im.comp (hcontH v)).neg
  have he1 : ∀ t : ℝ, ‖cexp (2 * π * I * (t : ℂ))‖ = 1 := by
    intro t
    rw [Complex.norm_exp]
    simp
  obtain ⟨c, hc⟩ : ∃ c : Λ → ℂ, ∀ x, c x = α x * cexp (-(π : ℂ) * H x r - (π : ℂ) * H x x / 2
      - (π : ℂ) * H r r / 2 + 2 * π * I * ((H x r).im : ℂ)) := ⟨_, fun _ => rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : Λ → V → ℂ, ∀ x z,
      F x z = c x * cexp (2 * π * I * ((H (r + x) z).im : ℂ)) := ⟨_, fun _ _ => rfl⟩
  have hfun : (fun z => Heisenberg₂ H r (kerSum H Λ α z) z * cexp (-(π : ℂ) * H z z)) =
      fun z => ∑' x : Λ, F x z := by
    funext z
    rw [heis_kerSum_diag H hH Λ α r z]
    simp only [hF, hc]
  have hre : ∀ x : Λ, (-(π : ℂ) * H x r - (π : ℂ) * H x x / 2 - (π : ℂ) * H r r / 2
      + 2 * π * I * ((H x r).im : ℂ)).re =
      -π * (H x r).re - π / 2 * (H x x).re - π / 2 * (H r r).re := by
    intro x
    simp [Complex.mul_re]
    ring
  have hcle : ∀ x : Λ, ‖c x‖ ≤ Real.exp (-(π / 2) * (H x x).re + π * K * ‖(x : V)‖) *
      Real.exp (-(π / 2) * (H r r).re) := by
    intro x
    have hα1 : ‖α x‖ = 1 := by
      rcases hα.1 x x.2 with h | h <;> simp [h]
    rw [hc, norm_mul, hα1, one_mul, Complex.norm_exp, hre, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : -(H x r).re ≤ K * ‖(x : V)‖ := by
      have := (abs_le.mp (Complex.abs_re_le_norm (H x r))).1
      linarith [hK x]
    have hπ : 0 ≤ π := Real.pi_pos.le
    nlinarith
  have hcsum : Summable fun x : Λ => ‖c x‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hcle
      ((GlobalTheory.T.summable_exp_neg_herm_add_norm V H hH Λ (π * K)).mul_right _)
  have hFnorm : ∀ x z, ‖F x z‖ = ‖c x‖ := by
    intro x z
    rw [hF, norm_mul, he1, mul_one]
  have hFcont : ∀ x : Λ, Continuous (F x) := by
    intro x
    have e : F x = fun z => c x * cexp (2 * π * I * ((H (r + x) z).im : ℂ)) := funext (hF x)
    rw [e]
    exact continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul (Complex.continuous_ofReal.comp (hcim _))))
  have hsumcont : Continuous fun z => ∑' x : Λ, F x z :=
    continuous_tsum hFcont hcsum (fun x z => (hFnorm x z).le)
  have hFs : ∀ z, Summable fun x : Λ => ‖F x z‖ := fun z => by
    simp only [hFnorm]
    exact hcsum
  have hbdd : ∀ z, ‖∑' x : Λ, F x z‖ ≤ ∑' x : Λ, ‖c x‖ := fun z => by
    refine (norm_tsum_le_tsum_norm (hFs z)).trans (le_of_eq ?_)
    simp only [hFnorm]
  have hFint : ∀ x : Λ, IntegrableOn (F x) Fd μ := fun x =>
    Measure.integrableOn_of_bounded hFdfin (hFcont x).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => (hFnorm x z).le)
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact Measure.integrableOn_of_bounded hFdfin hsumcont.aestronglyMeasurable
      (Filter.Eventually.of_forall hbdd)
  · rw [hfun]
    have hnormint : (fun x : Λ => ∫ z in Fd, ‖F x z‖ ∂μ) = fun x => μ.real Fd * ‖c x‖ := by
      funext x
      simp only [hFnorm]
      rw [setIntegral_const, smul_eq_mul]
    rw [← integral_tsum_of_summable_integral_norm hFint
      (by rw [hnormint]; exact hcsum.mul_left _)]
    have hint : ∀ x : Λ, ∫ z in Fd, F x z ∂μ =
        if (x : V) = -r then c x * (μ.real Fd : ℂ) else 0 := by
      intro x
      simp only [hF]
      rw [integral_const_mul]
      split_ifs with hx
      · have h0 : r + (x : V) = 0 := by
          rw [hx]
          abel
        simp only [h0, map_zero, LinearMap.zero_apply, Complex.zero_im, Complex.ofReal_zero,
          mul_zero, Complex.exp_zero]
        rw [setIntegral_const, Complex.real_smul, mul_one]
      · have hne : r + (x : V) ≠ 0 := by
          intro h
          apply hx
          rw [eq_neg_iff_add_eq_zero, add_comm]
          exact h
        rw [GlobalTheory.T.setIntegral_cexp_im_herm_eq_zero V μ H hH Λ' Fd hFd (r + x) hne ?_, mul_zero]
        intro y hy
        obtain ⟨m1, hm1⟩ := hr y hy
        obtain ⟨m2, hm2⟩ := hα.2.1 x x.2 y (hle hy)
        refine ⟨m1 + m2, ?_⟩
        rw [map_add (f := _), LinearMap.add_apply, Complex.add_im, hm1, hm2]
        push_cast
        ring
    simp only [hint]
    by_cases hrΛ : r ∈ Λ
    · rw [if_pos hrΛ, tsum_eq_single ⟨-r, neg_mem hrΛ⟩]
      · have hcoe : ((⟨-r, neg_mem hrΛ⟩ : Λ) : V) = -r := rfl
        have him : (H r r).im = 0 := Complex.conj_eq_iff_im.mp (hH.1 r r).symm
        have hA : cexp (-(π : ℂ) * H (-r) r - (π : ℂ) * H (-r) (-r) / 2 - (π : ℂ) * H r r / 2
            + 2 * π * I * ((H (-r) r).im : ℂ)) = 1 := by
          rw [← Complex.exp_zero]
          congr 1
          simp only [map_neg, LinearMap.neg_apply, neg_neg, Complex.neg_im, him, neg_zero,
            Complex.ofReal_zero, mul_zero, add_zero]
          ring
        rw [hc, hcoe, if_pos rfl, hA, mul_one]
      · intro x hx
        rw [if_neg]
        intro h
        apply hx
        exact Subtype.ext h
    · rw [if_neg hrΛ]
      have hno : ∀ x : Λ, ¬ ((x : V) = -r) := by
        intro x h
        apply hrΛ
        have hm := neg_mem x.2
        rw [h, neg_neg] at hm
        exact hm
      simp [hno]

end GlobalTheory.UnitaryTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinsumNormNeg
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.NormGauss

theorem exists_norm_eq {k : Type} [Field k] [Finite k] (s : k →+* k) (hs : ∀ a, s (s a) = a)
    (hne : ∃ a, s a ≠ a) (u : k) (hu : s u = u) : ∃ t, t * s t = u := by
  classical
  let F : Subfield k := RingHom.eqLocusField s (RingHom.id k)
  let σ : k ≃ₐ[F] k :=
    { toFun := s, invFun := s, left_inv := hs, right_inv := hs,
      map_mul' := map_mul s, map_add' := map_add s, commutes' := fun r => r.2 }
  have hσ_apply : ∀ x, σ x = s x := fun _ => rfl
  have hσ1 : σ ≠ 1 := by
    obtain ⟨a, ha⟩ := hne
    intro h
    apply ha
    have := AlgEquiv.ext_iff.1 h a
    rwa [hσ_apply, AlgEquiv.one_apply] at this
  have hσ2 : σ ^ 2 = 1 := by
    ext a
    rw [pow_two, AlgEquiv.mul_apply, hσ_apply, hσ_apply, hs, AlgEquiv.one_apply]
  have hfix : IntermediateField.fixedField (Subgroup.zpowers σ) = ⊥ := by
    ext x
    rw [IntermediateField.mem_fixedField_iff, IntermediateField.mem_bot]
    constructor
    · intro h
      exact ⟨⟨x, h σ (Subgroup.mem_zpowers σ)⟩, rfl⟩
    · rintro ⟨r, rfl⟩ τ _
      exact τ.commutes r
  have htop : Subgroup.zpowers σ = ⊤ := by
    rw [← IntermediateField.fixingSubgroup_fixedField (Subgroup.zpowers σ), hfix]
    ext τ
    simp only [Subgroup.mem_top, iff_true]
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.1 hx
    exact τ.commutes r
  have hcard : Fintype.card (k ≃ₐ[F] k) = 2 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.card_top, ← htop, Nat.card_zpowers,
      orderOf_eq_prime hσ2 hσ1]
  have huniv : (Finset.univ : Finset (k ≃ₐ[F] k)) = {1, σ} := by
    symm
    apply Finset.eq_univ_of_card
    rw [Finset.card_pair hσ1.symm, hcard]
  have hnorm : ∀ t : k, algebraMap F k (Algebra.norm F t) = t * s t := by
    intro t
    rw [Algebra.norm_eq_prod_automorphisms, huniv, Finset.prod_pair hσ1.symm]
    rfl
  obtain ⟨t, ht⟩ := FiniteField.norm_surjective F k (⟨u, hu⟩ : F)
  refine ⟨t, ?_⟩
  rw [← hnorm, ht]
  rfl

theorem sum_norm_neg {k : Type} [Field k] [Fintype k] (s : k →+* k) (hs : ∀ a, s (s a) = a)
    (hne : ∃ a, s a ≠ a) (ψ : AddChar k ℂ) (hψ : ∃ a, ψ (a + s a) ≠ 1) :
    ∃ m : ℝ, 0 < m ∧ ∑ t : k, ψ (t * s t) = -(m : ℂ) := by
  classical
  let F : Subfield k := RingHom.eqLocusField s (RingHom.id k)
  have hs0 : ∀ x : k, s x = 0 → x = 0 := by
    intro x h
    have := congrArg s h
    rwa [hs, map_zero] at this
  have hNF : ∀ t : k, t * s t ∈ F := fun t => by
    show s (t * s t) = t * s t
    rw [map_mul, hs, mul_comm]
  let N : k → F := fun t => ⟨t * s t, hNF t⟩
  have hN : ∀ t, ((N t : F) : k) = t * s t := fun _ => rfl
  let φ : AddChar F ℂ := ψ.compAddMonoidHom F.subtype.toAddMonoidHom
  have hφ_apply : ∀ u : F, φ u = ψ (u : k) := fun _ => rfl
  have hφ : φ ≠ 1 := by
    obtain ⟨a, ha⟩ := hψ
    intro h
    have hmem : a + s a ∈ F := by
      show s (a + s a) = a + s a
      rw [map_add (f := _), hs, add_comm]
    apply ha
    have := congrArg (fun χ : AddChar F ℂ => χ ⟨a + s a, hmem⟩) h
    simpa only [hφ_apply, AddChar.one_apply] using this
  have hsumφ : ∑ u : F, ψ (u : k) = 0 := by
    simpa only [hφ_apply] using AddChar.sum_eq_zero_of_ne_one hφ
  obtain ⟨c, hc⟩ : ∃ c : ℕ, c = (Finset.univ.filter (fun t : k => t * s t = 1)).card := ⟨_, rfl⟩
  have hfib : ∀ u : F,
      (Finset.univ.filter (fun t : k => N t = u)).card = if u = 0 then 1 else c := by
    intro u
    split_ifs with hu
    · subst hu
      rw [Finset.card_eq_one]
      refine ⟨0, ?_⟩
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        have h' : t * s t = 0 := congrArg Subtype.val h
        rcases mul_eq_zero.1 h' with h0 | h0
        · exact h0
        · exact hs0 t h0
      · rintro rfl
        apply Subtype.ext
        rw [hN, zero_mul]
        rfl
    · obtain ⟨t0, ht0⟩ := exists_norm_eq s hs hne (u : k) u.2
      have hu0 : (u : k) ≠ 0 := fun h => hu (Subtype.ext h)
      have ht0ne : t0 ≠ 0 := by
        rintro rfl
        apply hu0
        rw [← ht0, zero_mul]
      rw [hc]
      apply Finset.card_nbij' (fun t => t * t0⁻¹) (fun t => t * t0)
      · intro t ht
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
        have h' : t * s t = u := congrArg Subtype.val ht
        have e : t * t0⁻¹ * s (t * t0⁻¹) = (t * s t) * (t0 * s t0)⁻¹ := by
          rw [map_mul, map_inv₀, mul_inv]
          ring
        rw [e, h', ht0, mul_inv_cancel₀ hu0]
      · intro t ht
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ht ⊢
        apply Subtype.ext
        rw [hN]
        have e : t * t0 * s (t * t0) = (t * s t) * (t0 * s t0) := by
          rw [map_mul]
          ring
        rw [e, ht, ht0, one_mul]
      · intro t _
        exact inv_mul_cancel_right₀ ht0ne t
      · intro t _
        exact mul_inv_cancel_right₀ ht0ne t
  have hsplit : ∑ t : k, ψ (t * s t) =
      ∑ u : F, ((Finset.univ.filter (fun t : k => N t = u)).card : ℂ) * ψ (u : k) := by
    rw [← Finset.sum_fiberwise Finset.univ N (fun t => ψ (t * s t))]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [Finset.sum_congr rfl (g := fun _ => ψ (u : k)), Finset.sum_const, nsmul_eq_mul]
    intro t ht
    have := (Finset.mem_filter.1 ht).2
    rw [← this]
  have hψ0 : ψ ((0 : F) : k) = 1 := by
    rw [ZeroMemClass.coe_zero, AddChar.map_zero_eq_one]
  have key : ∀ u : F, (((if u = 0 then 1 else c : ℕ)) : ℂ) * ψ (u : k) =
      (c : ℂ) * ψ (u : k) + (if u = 0 then (1 - (c : ℂ)) else 0) := by
    intro u
    split_ifs with h
    · subst h
      rw [hψ0]
      push_cast
      ring
    · ring
  have hval : ∑ u : F, (((if u = 0 then 1 else c : ℕ)) : ℂ) * ψ (u : k) = 1 - c := by
    rw [Finset.sum_congr rfl (fun u _ => key u), Finset.sum_add_distrib, ← Finset.mul_sum, hsumφ,
      mul_zero, zero_add]
    simp
  have hc2 : 2 ≤ c := by
    obtain ⟨a, ha⟩ := hne
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact ha (map_zero s)
    have hsa0 : s a ≠ 0 := fun h => ha0 (hs0 a h)
    have hne1 : a * (s a)⁻¹ ≠ 1 := by
      intro h
      apply ha
      rw [mul_inv_eq_one₀ hsa0] at h
      exact h.symm
    rw [hc]
    calc 2 = ({1, a * (s a)⁻¹} : Finset k).card := (Finset.card_pair hne1.symm).symm
      _ ≤ _ := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hx with rfl | rfl
        · rw [map_one, one_mul]
        · rw [map_mul, map_inv₀, hs]
          field_simp
  refine ⟨(c : ℝ) - 1, ?_, ?_⟩
  · have : (2 : ℝ) ≤ c := by exact_mod_cast hc2
    linarith
  · rw [hsplit]
    simp_rw [hfib]
    rw [hval]
    push_cast
    ring

theorem finsum_norm_neg : ∀ (R : Type) [CommRing R] (σ : R →+* R) (P : Ideal R) [P.IsMaximal] [Finite (R ⧸ P)], (∀ a, σ (σ a) = a) → (∀ a ∈ P, σ a ∈ P) → (∃ a, a - σ a ∉ P) → ∀ χ : R → ℂ, (∀ a b, χ (a + b) = χ a * χ b) → (∀ a ∈ P, χ a = 1) → (∃ a, χ (a + σ a) ≠ 1) → ∃ m : ℝ, 0 < m ∧ ∑ᶠ q : R ⧸ P, χ (Quotient.out q * σ (Quotient.out q)) = -(m : ℂ) := by
  intro R _ σ P _ _ hσ hP hne χ hχ hχP hχa
  classical
  let _ : Field (R ⧸ P) := Ideal.Quotient.field P
  let _ : Fintype (R ⧸ P) := Fintype.ofFinite _
  have hle : P ≤ P.comap σ := fun a ha => hP a ha
  let s : R ⧸ P →+* R ⧸ P := Ideal.quotientMap P σ hle
  have hs_mk : ∀ a : R, s (Ideal.Quotient.mk P a) = Ideal.Quotient.mk P (σ a) :=
    fun a => Ideal.quotientMap_mk
  have hs : ∀ x, s (s x) = x := by
    intro x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hs_mk, hs_mk, hσ]
  have hsne : ∃ x, s x ≠ x := by
    obtain ⟨a, ha⟩ := hne
    refine ⟨Ideal.Quotient.mk P a, ?_⟩
    rw [hs_mk]
    intro h
    apply ha
    have h' := P.neg_mem (Ideal.Quotient.eq.1 h)
    rwa [neg_sub] at h'
  have hχ_congr : ∀ x y : R, x - y ∈ P → χ x = χ y := by
    intro x y h
    have e : x = y + (x - y) := by ring
    conv_lhs => rw [e]
    rw [hχ, hχP _ h, mul_one]
  let ψ : AddChar (R ⧸ P) ℂ :=
    { toFun := fun q => χ (Quotient.out q)
      map_zero_eq_one' := by
        apply hχP
        rw [← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_out]
      map_add_eq_mul' := by
        intro q₁ q₂
        rw [← hχ]
        apply hχ_congr
        rw [← Ideal.Quotient.eq, map_add (f := _), Ideal.Quotient.mk_out, Ideal.Quotient.mk_out,
          Ideal.Quotient.mk_out] }
  have hψ_mk : ∀ a, ψ (Ideal.Quotient.mk P a) = χ a := fun a =>
    hχ_congr _ _ (by rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out])
  have hψne : ∃ x, ψ (x + s x) ≠ 1 := by
    obtain ⟨a, ha⟩ := hχa
    exact ⟨Ideal.Quotient.mk P a, by rw [hs_mk, ← map_add (f := _), hψ_mk]; exact ha⟩
  obtain ⟨m, hm, hsum⟩ := sum_norm_neg s hs hsne ψ hψne
  refine ⟨m, hm, ?_⟩
  rw [finsum_eq_sum_of_fintype, ← hsum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  conv_rhs => rw [← Ideal.Quotient.mk_out q]
  rw [hs_mk, ← map_mul, hψ_mk]

end GlobalTheory.NormGauss
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TranslateLevelFour
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TranslateLevelFour
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.OddThetaTranslate

theorem coordB_add (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r)
    (z x : VC D N N') : coordB D T b k (z + x) = coordB D T b k z + coordB D T b k x := by
  simp only [coordB, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem coordB_nsmul (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (k : Fin r)
    (n : ℕ) (z : VC D N N') : coordB D T b k (n • z) = n * coordB D T b k z := by
  simp only [coordB, Pi.smul_apply, nsmul_eq_mul, mul_assoc, Finset.mul_sum]

theorem U_pullB (D : D7) (T : Tor D) {N N' r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (g : ℂ → ℂ)
    (hP : ∀ z w : VC D N N', ∑ τ, ∑ i, ∑ j, z τ i j * (starRingEnd ℂ) (w τ i j) =
      ∑ k, coordB D T b k z * (starRingEnd ℂ) (coordB D T b k w)) (x z : VC D N N') :
    U D T x (pullB D T b g) z = ∏ k, U1 T.abelian₂ (coordB D T b k x) g (coordB D T b k z) := by
  unfold U U1 pullB Hf
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum, hP, hP]
  simp only [coordB_add]
  congr 2
  rw [Finset.sum_div, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem half_not_mem {w₁ w₂ : ℂ} (h : LinearIndependent ℝ ![w₁, w₂]) :
    w₁ / 2 ∉ AddSubgroup.closure ({w₁, w₂} : Set ℂ) := by
  rw [AddSubgroup.mem_closure_pair]
  rintro ⟨m, n, hmn⟩
  have h0 := (LinearIndependent.pair_iff.1 h) (2 * (m : ℝ) - 1) (2 * (n : ℝ)) (by
    simp only [zsmul_eq_mul] at hmn
    simp only [Complex.real_smul]
    push_cast
    linear_combination 2 * hmn)
  have h1 : (2 * m - 1 : ℤ) = 0 := by exact_mod_cast h0.1
  omega

theorem exp_neg_pi_I_even (m : ℤ) (a : ℝ) (ha : a = 2 * m) :
    Complex.exp (-(Real.pi : ℂ) * Complex.I * (a : ℂ)) = 1 := by
  rw [ha, ← Complex.exp_int_mul_two_pi_mul_I (-m)]
  congr 1
  push_cast
  ring

theorem translate_level_four : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → Differentiable ℂ (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) ∧ ∃ t : VC D N N', 2 • t ∈ LaB D (tor0 D cc δ) b ∧ U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) 0 ≠ 0 ∧ ∀ ω ∈ LaB D (tor0 D cc δ) b, U D (tor0 D cc δ) (4 • ω) (U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)))) = U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) := by
  intro D hG cc δ hC N N' r b hb
  obtain ⟨w₁, w₂, hli, hΛ⟩ : ∃ w₁ w₂ : ℂ, LinearIndependent ℝ ![w₁, w₂] ∧
      lamOf D cc δ = AddSubgroup.closure {w₁, w₂} := by
    obtain ⟨L, hL⟩ := GlobalTheory.T.exists_periodPair_idealCurveLattice D cc δ hC
    refine ⟨L.ω₁, L.ω₂, L.indep, ?_⟩
    ext z
    rw [hL, PeriodPair.mem_lattice, AddSubgroup.mem_closure_pair]
    simp only [zsmul_eq_mul]
  obtain ⟨-, -, hP, hL, hbij⟩ := GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG cc δ N N' r b hb
  obtain ⟨⟨hd, -, -, hU⟩, hz, -⟩ := GlobalTheory.OddTheta.sgStar_laws (lamOf D cc δ) ⟨w₁, w₂, hli, hΛ⟩
  obtain ⟨-, -, hint, -⟩ := GlobalTheory.ThetaLine.theta_line D hG cc δ hC N N' (LaB D (tor0 D cc δ) b)
    (Or.inl ⟨r, b, hb, rfl⟩)
  have hw : w₁ ∈ lamOf D cc δ := by rw [hΛ]; exact AddSubgroup.subset_closure (by simp)
  have hw2 : w₁ / 2 ∉ lamOf D cc δ := by rw [hΛ]; exact half_not_mem hli
  obtain ⟨t, ht⟩ := hbij.2 (fun _ => w₁ / 2)
  have ht' : ∀ k, coordB D (tor0 D cc δ) b k t = w₁ / 2 := fun k => congrFun ht k
  have h2t : 2 • t ∈ LaB D (tor0 D cc δ) b := by
    rw [hL]
    intro k
    rw [coordB_nsmul, ht']
    have : ((2 : ℕ) : ℂ) * (w₁ / 2) = w₁ := by push_cast; ring
    rw [this]; exact hw
  refine ⟨?_, t, h2t, ?_, ?_⟩
  · have hc : ∀ k, Differentiable ℂ (coordB D (tor0 D cc δ) b k) := by
      intro k
      unfold coordB
      fun_prop
    unfold pullB
    fun_prop
  · simp only [U, zero_add, pullB, ht']
    refine mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => ?_) (Complex.exp_ne_zero _)
    exact fun h => hw2 ((hz _).1 h)
  · intro ω hω
    have hfix : U D (tor0 D cc δ) (4 • ω) (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) =
        pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)) := by
      funext z
      rw [U_pullB D _ b _ hP]
      refine Finset.prod_congr rfl fun k _ => ?_
      have hk := (hL ω).1 hω k
      have h4 : coordB D (tor0 D cc δ) b k (4 • ω) ∈ lamOf D cc δ :=
        (hL _).1 (AddSubgroup.nsmul_mem _ hω 4) k
      have h2 : coordB D (tor0 D cc δ) b k (4 • ω) / 2 ∈ lamOf D cc δ := by
        have : coordB D (tor0 D cc δ) b k (4 • ω) / 2 =
            coordB D (tor0 D cc δ) b k ω + coordB D (tor0 D cc δ) b k ω := by
          rw [coordB_nsmul]; push_cast; ring
        rw [this]; exact add_mem hk hk
      have := hU _ h4 (coordB D (tor0 D cc δ) b k z)
      rw [if_pos h2, one_mul] at this
      exact this
    obtain ⟨m, hm⟩ := hint ω hω _ h2t
    have ha : (Hf D (tor0 D cc δ) (4 • ω) t).im = 2 * m := by
      rw [Hf_nsmul_right] at hm
      rw [Hf_nsmul_left, ← hm]
      simp
      ring
    have hb' : (Hf D (tor0 D cc δ) t (4 • ω)).im = 2 * ((-m : ℤ) : ℝ) := by
      rw [Hf_im_swap, ha]; push_cast; ring
    funext z
    have e := U_U D (tor0 D cc δ) t (4 • ω) (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) z
    rw [hfix, exp_neg_pi_I_even _ _ hb', one_mul] at e
    rw [U_U, exp_neg_pi_I_even _ _ ha, one_mul, e, add_comm]

end GlobalTheory.OddThetaTranslate
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TranslateLevelFourStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.U_pullB_ne_zero_and_invariant_four_smul : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), OnB D b → Differentiable ℂ (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) ∧ ∃ t : VC D N N', 2 • t ∈ LaB D (tor0 D cc δ) b ∧ U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) 0 ≠ 0 ∧ ∀ ω ∈ LaB D (tor0 D cc δ) b, U D (tor0 D cc δ) (4 • ω) (U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ)))) = U D (tor0 D cc δ) t (pullB D (tor0 D cc δ) b (sgStar (lamOf D cc δ))) := by
  first | exact @GlobalTheory.OddThetaTranslate.translate_level_four | exact GlobalTheory.OddThetaTranslate.translate_level_four | (intros; apply GlobalTheory.OddThetaTranslate.translate_level_four <;> assumption)
end
end
