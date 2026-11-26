module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CharacterValueAtT
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NegGram
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRefill
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DifferentiableAtDerivAtZero
public import Formalism.GL3MeanSquares.HookFormulaTorsion.FourFoldOrthogonalSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalCharEqHeckeCharLocalComponentOfValues
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalCharEqHeckeCharLocalComponentOfValues
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

namespace GlobalTheory.LocCharComp

private theorem eventually_abs_le_half_add_of_doubling_bounds {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (π : 𝓞 E)
    (hπ : π ∈ P.asIdeal) (hπ2 : π ∉ P.asIdeal ^ 2) :
    ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∀ x ∈ P.asIdeal, ∃ x₂ : 𝓞 E, x * s = x₂ * π := by
  have hle : Ideal.span {π} ≤ P.asIdeal := (Ideal.span_singleton_le_iff_mem _).2 hπ
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hJP : ¬ J ≤ P.asIdeal := by
    intro h
    apply hπ2
    have hsub : Ideal.span {π} ≤ P.asIdeal ^ 2 := by
      rw [hJ, pow_two]
      exact Ideal.mul_mono_right h
    exact hsub (Ideal.mem_span_singleton_self π)
  obtain ⟨s, hsJ, hsP⟩ := SetLike.not_le_iff_exists.1 hJP
  refine ⟨s, hsP, fun x hx => ?_⟩
  have hmem : x * s ∈ Ideal.span {π} := hJ ▸ Ideal.mul_mem_mul hx hsJ
  obtain ⟨x₂, hx₂⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨x₂, hx₂.symm⟩

private theorem exists_unit_mul_eq_mul_uniformizer_pow {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (π : 𝓞 E)
    (hπ : π ∈ P.asIdeal) (hπ2 : π ∉ P.asIdeal ^ 2) :
    ∀ n : ℕ, ∀ x : 𝓞 E, x ∉ P.asIdeal ^ (n + 1) →
      ∃ (m : ℕ) (s x' : 𝓞 E), s ∉ P.asIdeal ∧ x' ∉ P.asIdeal ∧ s * x = x' * π ^ m := by
  obtain ⟨s₀, hs₀, hstep⟩ := eventually_abs_le_half_add_of_doubling_bounds P π hπ hπ2
  have h1 : (1 : 𝓞 E) ∉ P.asIdeal := (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  intro n
  induction n with
  | zero =>
    intro x hx
    exact ⟨0, 1, x, h1, by simpa using hx, by simp⟩
  | succ n ih =>
    intro x hx
    by_cases hxP : x ∈ P.asIdeal
    · obtain ⟨x₂, hx₂⟩ := hstep x hxP
      have hx₂n : x₂ ∉ P.asIdeal ^ (n + 1) := by
        intro h
        apply hx
        have hmem : x * s₀ ∈ P.asIdeal ^ (n + 1 + 1) := by
          rw [hx₂, pow_succ]
          exact Ideal.mul_mem_mul h hπ
        have hv := (P.intValuation_le_pow_iff_mem _ _).2 hmem
        rw [map_mul, HeightOneSpectrum.intValuation_eq_one_iff.2 hs₀, mul_one] at hv
        exact (P.intValuation_le_pow_iff_mem _ _).1 hv
      obtain ⟨m, s, x', hs, hx', he⟩ := ih x₂ hx₂n
      refine ⟨m + 1, s * s₀, x', fun h => (P.isPrime.mem_or_mem h).elim hs hs₀, hx', ?_⟩
      calc s * s₀ * x = s * (x * s₀) := by ring
        _ = s * x₂ * π := by rw [hx₂]; ring
        _ = x' * π ^ (m + 1) := by rw [he]; ring
    · exact ⟨0, 1, x, h1, hxP, by simp⟩

private theorem exists_notMem_pow_succ {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (x : 𝓞 E)
    (hx : x ≠ 0) : ∃ n : ℕ, x ∉ P.asIdeal ^ (n + 1) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, P.intValuation x = WithZero.exp (-(n : ℤ)) := ⟨_, P.intValuation_if_neg hx⟩
  refine ⟨n, fun h => ?_⟩
  have hv := (P.intValuation_le_pow_iff_mem _ _).2 h
  rw [hn, WithZero.exp_le_exp] at hv
  push_cast at hv
  omega

private theorem exists_zpow_uniformizer_factorization {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (π : 𝓞 E)
    (hπ : π ∈ P.asIdeal) (hπ2 : π ∉ P.asIdeal ^ 2) (a : E) (ha : a ≠ 0) :
    ∃ (z : ℤ) (r s : 𝓞 E), r ∉ P.asIdeal ∧ s ∉ P.asIdeal ∧
      algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r * algebraMap (𝓞 E) E π ^ z := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (𝓞 E) a
  have hinj := IsFractionRing.injective (𝓞 E) E
  have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at ha
  obtain ⟨n₁, hn₁⟩ := exists_notMem_pow_succ P x hx0
  obtain ⟨n₂, hn₂⟩ := exists_notMem_pow_succ P y hy0
  obtain ⟨m₁, s₁, x₁, hs₁, hx₁, e₁⟩ := exists_unit_mul_eq_mul_uniformizer_pow P π hπ hπ2 n₁ x hn₁
  obtain ⟨m₂, s₂, y₁, hs₂, hy₁, e₂⟩ := exists_unit_mul_eq_mul_uniformizer_pow P π hπ hπ2 n₂ y hn₂
  refine ⟨(m₁ : ℤ) - m₂, x₁ * s₂, y₁ * s₁, fun h => (P.isPrime.mem_or_mem h).elim hx₁ hs₂,
    fun h => (P.isPrime.mem_or_mem h).elim hy₁ hs₁, ?_⟩
  have e₁' := congrArg (algebraMap (𝓞 E) E) e₁
  have e₂' := congrArg (algebraMap (𝓞 E) E) e₂
  simp only [map_mul, map_pow] at e₁' e₂'
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact hπ2 (Submodule.zero_mem _)
  have hY : algebraMap (𝓞 E) E y ≠ 0 := (map_ne_zero_iff _ hinj).2 hy0
  have hpi : algebraMap (𝓞 E) E π ≠ 0 := (map_ne_zero_iff _ hinj).2 hπ0
  rw [zpow_sub₀ hpi, zpow_natCast, zpow_natCast, map_mul, map_mul]
  field_simp
  linear_combination (algebraMap (𝓞 E) E y₁ * algebraMap (𝓞 E) E π ^ m₂) * e₁' -
    (algebraMap (𝓞 E) E x₁ * algebraMap (𝓞 E) E π ^ m₁) * e₂'

private theorem exists_integer_ratio_of_isUnit_redP {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (b : E)
    (hb : IsUnit (redP P b)) :
    ∃ r s : 𝓞 E, r ∉ P.asIdeal ∧ s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * b = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * redP P b = Ideal.Quotient.mk P.asIdeal r := by
  have := P.isPrime
  unfold redP at hb ⊢
  split_ifs at hb ⊢ with h
  · obtain ⟨r, s, hs, hsb, hc⟩ := h.choose_spec
    refine ⟨r, s, fun hr => ?_, hs, hsb, hc⟩
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hr, hb.mul_left_eq_zero] at hc
    exact hs (Ideal.Quotient.eq_zero_iff_mem.1 hc)
  · exact absurd hb not_isUnit_zero

private theorem isUnit_redP_of_integer_ratio {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (b : E)
    (r s : 𝓞 E) (hr : r ∉ P.asIdeal) (hs : s ∉ P.asIdeal)
    (hsb : algebraMap (𝓞 E) E s * b = algebraMap (𝓞 E) E r) : IsUnit (redP P b) := by
  let := Ideal.Quotient.field P.asIdeal
  have hs' : Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hex : ∃ c : 𝓞 E ⧸ P.asIdeal, ∃ r s : 𝓞 E, s ∉ P.asIdeal ∧
      algebraMap (𝓞 E) E s * b = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r :=
    ⟨Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹, r, s, hs, hsb,
      by rw [mul_comm (Ideal.Quotient.mk P.asIdeal r), ← mul_assoc, mul_inv_cancel₀ hs', one_mul]⟩
  unfold redP
  rw [dite_eq_left hex]
  obtain ⟨r₂, s₂, hs₂, hsb₂, hc₂⟩ := hex.choose_spec
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  rw [h0, mul_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem] at hc₂
  have he : s * r₂ = s₂ * r := IsFractionRing.injective (𝓞 E) E (by
    simp only [map_mul]
    rw [← hsb₂, ← hsb]
    ring)
  have hmem : s₂ * r ∈ P.asIdeal := he ▸ Ideal.mul_mem_left _ s hc₂
  exact (P.isPrime.mem_or_mem hmem).elim hs₂ hr

theorem locChar_eq_locK : ∀ (E K : Type) [Field E] [NumberField E] [Field K] (σ : K →+* ℂ) (P : HeightOneSpectrum (𝓞 E)) (ψ : Formalism.L2.Host.HChar E) (cq : K) (t : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ), ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → (∀ q : Eˣ, (q : E) = ((Ideal.absNorm P.asIdeal : ℕ) : E) → σ cq = ((ψ.locK P q : ℂˣ) : ℂ)) → (∀ (x : Eˣ) (y : 𝓞 E) (c : (𝓞 E ⧸ P.asIdeal)ˣ), (x : E) = (y : E) → (c : 𝓞 E ⧸ P.asIdeal) = Ideal.Quotient.mk P.asIdeal y → σ ((t c : Kˣ) : K) = ((ψ.locK P x : ℂˣ) : ℂ)) → ∀ a : Eˣ, σ (LocE.locChar (Formalism.L2.Col.qOf P) cq t (a : E)) = ((ψ.locK P a : ℂˣ) : ℂ) := by
  intro E K _ _ _ σ P ψ cq t hq2 h1 h2 a
  have := P.isPrime
  let := Ideal.Quotient.field P.asIdeal
  have hinj := IsFractionRing.injective (𝓞 E) E
  have hπ : ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _
  have hπE : ((qOf P : ℕ) : E) = algebraMap (𝓞 E) E ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) := by
    rw [map_natCast]
    rfl
  have hπne : ((qOf P : ℕ) : E) ≠ 0 := by
    rw [hπE]
    refine (map_ne_zero_iff _ hinj).2 fun h0 => hq2 ?_
    rw [h0]
    exact Submodule.zero_mem _
  have hex : ∃ z : ℤ, IsUnit (redP P ((a : E) / ((qOf P : ℕ) : E) ^ z)) := by
    obtain ⟨z, r, s, hr, hs, hsa⟩ := exists_zpow_uniformizer_factorization P _ hπ hq2 (a : E) a.ne_zero
    refine ⟨z, isUnit_redP_of_integer_ratio P _ r s hr hs ?_⟩
    rw [hπE, mul_div_assoc', hsa, mul_div_assoc, div_self (zpow_ne_zero _ (hπE ▸ hπne)), mul_one]
  have hU : IsUnit (redP P ((a : E) / ((qOf P : ℕ) : E) ^ LocE.vP P (qOf P) (a : E))) :=
    Classical.epsilon_spec hex
  obtain ⟨r, s, hr, hs, hsb, hc⟩ := exists_integer_ratio_of_isUnit_redP P _ hU
  have hr0 : algebraMap (𝓞 E) E r ≠ 0 := (map_ne_zero_iff _ hinj).2 fun h0 => hr (h0 ▸ Submodule.zero_mem _)
  have hs0 : algebraMap (𝓞 E) E s ≠ 0 := (map_ne_zero_iff _ hinj).2 fun h0 => hs (h0 ▸ Submodule.zero_mem _)
  have hmr : Ideal.Quotient.mk P.asIdeal r ≠ 0 := fun h => hr (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hms : Ideal.Quotient.mk P.asIdeal s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.1 h)
  set w := LocE.vP P (qOf P) (a : E)
  let Q : Eˣ := Units.mk0 _ hπne
  let xr : Eˣ := Units.mk0 _ hr0
  let xs : Eˣ := Units.mk0 _ hs0
  let cr : (𝓞 E ⧸ P.asIdeal)ˣ := Units.mk0 _ hmr
  let cs : (𝓞 E ⧸ P.asIdeal)ˣ := Units.mk0 _ hms
  have hA : a = Q ^ w * xr * xs⁻¹ := by
    ext
    simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, Units.val_mk0, Q, xr, xs]
    rw [← hsb]
    field_simp
  have hB : hU.unit = cr * cs⁻¹ := by
    ext
    simp only [IsUnit.unit_spec, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, cr, cs]
    rw [← hc]
    field_simp
  have eQ := h1 Q rfl
  have er := h2 xr r cr rfl rfl
  have es := h2 xs s cs rfl rfl
  show σ (cq ^ w * LocE.unitV t ((a : E) / ((qOf P : ℕ) : E) ^ w)) = _
  unfold LocE.unitV
  rw [dite_eq_left hU, hB]
  conv_rhs => rw [hA]
  simp only [map_mul, map_inv, map_zpow, map_zpow₀, Units.val_mul, Units.val_inv_eq_inv_val,
    Units.val_zpow_eq_zpow_val, map_inv₀, eQ, er, es]
  ring

end GlobalTheory.LocCharComp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalCharEqHeckeCharLocalComponentOfValuesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localChar_eq_heckeChar_localComponent_of_values : ∀ (E K : Type) [Field E] [NumberField E] [Field K] (σ : K →+* ℂ) (P : HeightOneSpectrum (𝓞 E)) (ψ : Formalism.L2.Host.HChar E) (cq : K) (t : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ), ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 → (∀ q : Eˣ, (q : E) = ((Ideal.absNorm P.asIdeal : ℕ) : E) → σ cq = ((ψ.locK P q : ℂˣ) : ℂ)) → (∀ (x : Eˣ) (y : 𝓞 E) (c : (𝓞 E ⧸ P.asIdeal)ˣ), (x : E) = (y : E) → (c : 𝓞 E ⧸ P.asIdeal) = Ideal.Quotient.mk P.asIdeal y → σ ((t c : Kˣ) : K) = ((ψ.locK P x : ℂˣ) : ℂ)) → ∀ a : Eˣ, σ (LocE.locChar (Formalism.L2.Col.qOf P) cq t (a : E)) = ((ψ.locK P a : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.LocCharComp.locChar_eq_locK | exact GlobalTheory.LocCharComp.locChar_eq_locK | (intros; apply GlobalTheory.LocCharComp.locChar_eq_locK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianSpaceOppositeFormSignatureCondition
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianSpaceOppositeFormSignatureCondition
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Matrix

namespace GlobalTheory.NegSpace

theorem hasSignature_neg_swap {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature J p q) : Formalism.UG.HasSignature (-J) q p := by
  obtain ⟨e, P, hP⟩ := h
  let s := Equiv.sumComm (Fin p) (Fin q)
  refine ⟨e.trans s, Units.map (Matrix.reindexAlgEquiv ℂ ℂ s).toRingHom.toMonoidHom P, ?_⟩
  have e1 : Formalism.UG.Jpq q p = -(Formalism.UG.Jpq p q).submatrix s.symm s.symm := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Formalism.UG.Jpq, s]
  rw [e1, ← hP, ← submatrix_mul_equiv _ _ _ s.symm, ← submatrix_mul_equiv _ _ _ s.symm, ← Matrix.neg_mul, ← Matrix.mul_neg]
  rfl

theorem sigOK_neg : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (W : HSpace E), W.SigOK → (GlobalTheory.NegSpace.neg W).SigOK := by
  intro E _ _ _ W h τ
  have e : (neg W).gram.map τ = -W.gram.map τ := Matrix.ext fun i j => map_neg τ (W.gram i j)
  rw [e]
  exact hasSignature_neg_swap (h τ)

end GlobalTheory.NegSpace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianSpaceOppositeFormSignatureConditionStatement
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianSpaceOppositeForm_signatureCondition : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (W : HSpace E), W.SigOK → (GlobalTheory.NegSpace.neg W).SigOK := by
  first | exact @GlobalTheory.NegSpace.sigOK_neg | exact GlobalTheory.NegSpace.sigOK_neg | (intros; apply GlobalTheory.NegSpace.sigOK_neg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsWeightsInWindows
namespace GlobalTheory.EX

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

theorem exists_weights_in_windows : ∀ (eps : ℝ) (C : FC), 0 < eps → eps < 1 / 52 → Std C → ∃ x0 : ℝ,
    ∀ (s : Scale) (R : Ranks) (H : Host R), s.eps = eps → x0 ≤ s.x → RankVal s R →
      ∃ a b : R.A → ℤ, WinOK s C.GK H a b := by
  intro eps C h0 h1 hS
  have hLa : 1 ≤ C.GK.La := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  obtain ⟨CN, x1, hN⟩ := GlobalTheory.topCount_and_lambda_bounds eps h0 h1
  obtain ⟨x2, hP⟩ := GlobalTheory.scale_poly_comparison eps 17 1 h0 one_pos
  obtain ⟨x3, hR⟩ := GlobalTheory.EX.rank_basic_bounds eps h0 h1
  refine ⟨max x1 (max x2 x3), fun s R H he hx hRV => ?_⟩
  have hx1 : x1 ≤ s.x := le_trans (le_max_left _ _) hx
  have hx2 : x2 ≤ s.x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : x3 ≤ s.x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨-, -, hK⟩ := hN s he hx1
  have hLa1 := (hK C.GK hLa).1
  obtain ⟨-, -, hb, -, hb', -⟩ := hP s he hx2
  obtain ⟨-, -, hr, hkr, -⟩ := hR s R he hx3 hRV
  have hx1' : 1 ≤ s.x := s.one_lt_alt.le
  have hxp : 0 < s.x := lt_of_lt_of_le one_pos hx1'
  have hk5 : (R.k : ℝ) ≤ s.x ^ (5 : ℝ) := le_trans (by exact_mod_cast hkr) hr
  have hk0 : (0 : ℝ) < R.k := by
    have := R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < R.k)
  have hX : 1 ≤ s.X' := Real.one_le_exp (Real.rpow_nonneg hxp.le _)
  rw [Real.rpow_one] at hb
  rw [sub_self, Real.rpow_zero, one_mul] at hb'
  have h17 : 0 < s.x ^ (17 : ℝ) := Real.rpow_pos_of_pos hxp _
  have hb17 : s.x ^ (17 : ℝ) ≤ s.b := le_trans (le_mul_of_one_le_right h17.le hX) hb
  have hA : 1 ≤ s.a / ((R.k : ℝ) * s.x ^ (Scale.A / 2)) := by
    have h13 : 0 < s.x ^ (Scale.A / 2) := Real.rpow_pos_of_pos hxp _
    rw [le_div_iff₀ (mul_pos hk0 h13), one_mul]
    calc (R.k : ℝ) * s.x ^ (Scale.A / 2) ≤ s.x ^ (5 : ℝ) * s.x ^ (Scale.A / 2) :=
          mul_le_mul_of_nonneg_right hk5 h13.le
      _ = s.x * s.x ^ (17 : ℝ) := by
          rw [← Real.rpow_add hxp, ← Real.rpow_one_add' hxp.le (by norm_num)]
          congr 1
          unfold Scale.A
          norm_num
      _ ≤ s.a := mul_le_mul_of_nonneg_left hb17 hxp.le
  have hB : 1 ≤ 2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La C.GK s * s.b' / (R.k : ℝ) := by
    rw [le_div_iff₀ hk0, one_mul]
    have hn : (1 : ℝ) ≤ R.n := by
      have : 1 ≤ R.n := R.ord_pos
      exact_mod_cast this
    have hd : 1 ≤ s.delta1 * s.x ^ s.eps := by
      unfold Scale.delta1
      rw [← Real.rpow_add hxp]
      exact Real.one_le_rpow hx1' (by have := s.eps_pos; linarith)
    have hL : 1 ≤ G.La C.GK s := le_trans (Real.one_le_rpow hx1' s.eps_pos.le) hLa1
    have hkb : (R.k : ℝ) ≤ s.b' :=
      le_trans hk5 (le_trans (Real.rpow_le_rpow_of_exponent_le hx1' (by norm_num)) hb')
    have h2 : (1 : ℝ) ≤ 2 * (R.n : ℝ) * (s.delta1 * s.x ^ s.eps) * G.La C.GK s :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hd) hL
    calc (R.k : ℝ) ≤ s.b' := hkb
      _ ≤ (2 * (R.n : ℝ) * (s.delta1 * s.x ^ s.eps) * G.La C.GK s) * s.b' :=
          le_mul_of_one_le_left (le_trans hk0.le hkb) h2
      _ = _ := by ring
  refine ⟨fun _ => ⌈s.a⌉, fun _ => ⌈s.b'⌉, fun t _ => ⟨⟨Int.le_ceil _, ?_⟩, Int.le_ceil _, ?_⟩⟩
  · have := Int.ceil_lt_add_one s.a
    linarith
  · have := Int.ceil_lt_add_one s.b'
    linarith

end GlobalTheory.EX
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralClosureCompletedCMAlgebraCompactOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralClosureCompletedCMAlgebraCompactOpen
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.CompletedOrder

theorem eq_sum_trace {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (R : Type) [CommRing R] [Algebra F R] (z : R ⊗[F] E) :
    z = ∑ i, Algebra.trace R (R ⊗[F] E) (z * (1 : R) ⊗ₜ[F] b i) • ((1 : R) ⊗ₜ[F] b.traceDual i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [add_mul, map_add (f := _), add_smul, Finset.sum_add_distrib]
    rw [← hx, ← hy]
  | tmul a e =>
    have h3 : ∀ e : E, Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) =
        a * algebraMap F R (Algebra.trace F E e) := by
      intro e
      have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
        LinearMap.trace_baseChange, smul_eq_mul]
    conv_lhs => rw [← b.traceDual.sum_repr e, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, h3, Module.Basis.traceDual_repr_apply,
      Algebra.traceForm_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      ← TensorProduct.smul_tmul, mul_comm a, Algebra.smul_def]

theorem isCompact_isOpen_integralClosure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ v : HeightOneSpectrum (𝓞 F), IsCompact (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) : Set (Fv F v ⊗[F] E)) ∧ IsOpen (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) : Set (Fv F v ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ h v
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h.2.2.1
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral (𝓞 F) F E
  have hb' : ∀ i, IsIntegral (v.adicCompletionIntegers F) ((1 : Fv F v) ⊗ₜ[F] b i) := by
    intro i
    have h1 : IsIntegral ℤ (b i) := isIntegral_trans (b i) (hb i)
    exact h1.map_of_comp_eq (algebraMap ℤ _) (inclR (F := F) (E := E) (Fv F v))
      (RingHom.ext_int _ _)
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hC : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    isCompact_iff_compactSpace.2 (AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  have hopen : IsOpen (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :
      Set (Fv F v ⊗[F] E)) := by
    let B := Algebra.TensorProduct.basis (Fv F v) b
    have hc : Continuous B.equivFun := IsModuleTopology.continuous_of_linearMap B.equivFun.toLinearMap
    refine AddSubgroup.isOpen_of_mem_nhds
      (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E)).toSubring.toAddSubgroup
      (g := 0) ?_
    refine Filter.mem_of_superset (((isOpen_set_pi Set.finite_univ fun _ _ => hO).preimage hc).mem_nhds ?_) ?_
    · intro i _
      simp
    · intro z hz
      show IsIntegral _ z
      rw [← B.sum_equivFun z]
      refine IsIntegral.sum _ fun i _ => ?_
      have := (hb' i).smul (⟨_, hz i (Set.mem_univ i)⟩ : v.adicCompletionIntegers F)
      rw [Algebra.TensorProduct.basis_apply]
      exact this
  refine ⟨?_, hopen⟩
  have hclosed : IsClosed (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :
      Set (Fv F v ⊗[F] E)) :=
    AddSubgroup.isClosed_of_isOpen
      (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E)).toSubring.toAddSubgroup hopen
  have hcont : Continuous fun x : s → Fv F v => ∑ i, x i • ((1 : Fv F v) ⊗ₜ[F] b.traceDual i) := by
    fun_prop
  refine IsCompact.of_isClosed_subset ((isCompact_univ_pi fun _ => hC).image hcont) hclosed ?_
  intro z hz
  refine ⟨_, ?_, (eq_sum_trace b (Fv F v) z).symm⟩
  intro i _
  have h1 : IsIntegral (v.adicCompletionIntegers F) (z * (1 : Fv F v) ⊗ₜ[F] b i) :=
    IsIntegral.mul hz (hb' i)
  have h2 : IsIntegral (v.adicCompletionIntegers F) (sigR (Fv F v) σ (z * (1 : Fv F v) ⊗ₜ[F] b i)) :=
    h1.map ((Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ).restrictScalars
      (v.adicCompletionIntegers F))
  have h3 := h1.add h2
  rw [← SelfDualLatticeCompare.trace_tensor (Fv F v) h,
    isIntegral_algebraMap_iff ] at h3
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
  beta_reduce
  rw [← hy]
  exact y.2

end GlobalTheory.CompletedOrder
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralClosureCompletedCMAlgebraCompactOpenStatement
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralClosure_completedCMAlgebra_compact_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ v : HeightOneSpectrum (𝓞 F), IsCompact (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) : Set (Fv F v ⊗[F] E)) ∧ IsOpen (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) : Set (Fv F v ⊗[F] E)) := by
  first | exact @GlobalTheory.CompletedOrder.isCompact_isOpen_integralClosure | exact GlobalTheory.CompletedOrder.isCompact_isOpen_integralClosure | (intros; apply GlobalTheory.CompletedOrder.isCompact_isOpen_integralClosure <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ObjOnNarrowOfObjectsExist
section -- merged from Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.FewBadPrimes
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.FewBadPrimes

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab NumberField GlobalTheory.EX

variable {R : Ranks}

def condE (H : Host R) : ℕ := H.QS * H.q * H.d

def dlogH (H : Host R) : ℝ :=
  haveI : Fact H.d.Prime := ⟨H.hyp.2.1⟩
  haveI : NeZero H.d := ⟨H.hyp.2.1.ne_zero⟩
  (deriv (DirichletCharacter.LFunction
      ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ H.d)) 1 /
    DirichletCharacter.LFunction
      ((quadraticChar (ZMod H.d)).ringHomComp (Int.castRingHom ℂ) : DirichletCharacter ℂ H.d) 1).re

def frobH (H : Host R) (p : ℕ) : R.A :=
  R.iotaInv (Classical.epsilon (fun g : R.GG =>
    g ∈ {g : R.GG | ∃ (P : Ideal (𝓞 H.E)) (_ : P.IsPrime) (_ : P.LiesOver (Ideal.span {(p : ℤ)}))
      (σ : H.E ≃ₐ[ℚ] H.E), IsArithFrobAt ℤ σ P ∧ H.galE σ = g})).2

def logPowerBoundClassPrimes (H : Host R) (s : Scale) : ℕ :=
  2 * sSup {l | ∃ p : ℕ, p.Prime ∧ H.cls p = PrimeClass.inertClass ∧
    l = ⌈Real.logb p (((R.k : ℝ) * s.x ^ Scale.A) ^ 4)⌉₊}

def GoodH (H : Host R) (s : Scale) (p : ℕ) (t0 : R.A) : Prop :=
  G.IsGoodOrbit (addOrderOf (frobH H p))
    (Finset.univ.filter (fun i : Fin (addOrderOf (frobH H p)) => t0 + (i : ℕ) • frobH H p ∈ H.TT))
    (logPowerBoundClassPrimes H s) (G.KG s) (G.rG s) s.delta1 (G.hG s) s.x

def IsOrigins {φ : Formalism.HC.Frame} (bs : φ.A → φ.A → φ.A) : Prop :=
  (∀ h t, ∃ i : ℕ, bs h t + i • h = t) ∧ ∀ h t, bs h (t + h) = bs h t


open Classical in
def FewBad (H : Host R) (s : Scale) (bs : R.A → R.A → R.A) : Prop :=
  ∑ p ∈ (Finset.range ⌈s.X'⌉₊).filter (fun p => p.Prime ∧ H.cls p = PrimeClass.inertClass ∧
      s.x ^ (s.eps / 4) ≤ (addOrderOf (frobH H p) : ℝ)),
    Real.log p / p * ((H.TT.filter (fun t => ¬ GoodH H s p (bs (frobH H p) t))).card : ℝ) ≤
  (H.TT.card : ℝ) * s.x ^ (-2 + s.eps)

def CharOf (H : Host R) {N : ℕ} (χ : DirichletCharacter ℂ N) : Prop :=
  χ.IsPrimitive ∧ ∃ ψ : R.GG →* ℂˣ, ∀ (a : ℕ) (h : a.Coprime H.condN),
    χ (a : ZMod N) = ((ψ (H.art (ZMod.unitOfCoprime a h)) : ℂˣ) : ℂ)

def RealBoxes (H : Host R) (Y eps : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), CharOf H χ → GlobalTheoryTheory.IsRealChar χ →
    (H.d ∣ N → GlobalTheoryTheory.GoodFor (8 * ((ordCompl[2] H.QS : ℕ) : ℝ) * GlobalTheoryTheory.X1 Y eps * GlobalTheoryTheory.X2 Y eps) χ) ∧
    (H.q ∣ N → ¬ H.d ∣ N → GlobalTheoryTheory.GoodFor (8 * ((ordCompl[2] H.QS : ℕ) : ℝ) * GlobalTheoryTheory.X1 Y eps) χ)

def BoxesInWindow (s : Scale) (H : Host R) : Prop :=
  ∃ Y : ℝ, PairWin s Y ∧ PairRow Y s.eps H ∧ Boxq Y s.eps H.q H.d ∧ RealBoxes H Y s.eps

def ArithData (C : FC) (s : Scale) (H : Host R) (q0 : ℕ)
    (bs : R.A → R.A → R.A) : Prop :=
  HostVal s C.P.Cpde H ∧ H.CT2 = C.CT2 ∧
  BoxesInWindow s H ∧ |dlogH H| ≤ s.x ^ s.eps ∧ QDq s.x s.eps 4 H.q H.d ∧
  4 * H.Lw * H.T2.card ≤ R.n0 ∧
  IsOrigins bs ∧ FewBad H s bs ∧
  (∀ i, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g i : H.E) ∧
    π - 1 ∈ Ideal.span {((condE H : ℕ) : 𝓞 H.E)}) ∧
  Disjoint (Formalism.CyclotomicNorms.BB R.r (H.g 0)) (Formalism.CyclotomicNorms.BB R.r (H.g 1)) ∧
  (H.pde ≡ 1 [MOD Nat.lcm 15 (condE H)] ∧ H.pde' ≡ 1 [MOD Nat.lcm 15 (condE H)]) ∧
  (q0.Prime ∧ 5 ≤ q0 ∧ (q0 : ℝ) ≤ (condE H : ℝ) ^ C.P.Cpde ∧
    ∃ r' : ℕ, IsLeast {l : ℕ | l.Prime ∧ ¬ l ∣ condE H * (H.pde - 1) * (H.pde' - 1)} r' ∧
      q0 ≡ 1 [MOD r' * condE H]) ∧
  H.levelPrimes = {H.g 0, H.g 1, H.pde, H.pde', q0}

def hostAt (H : Host R) (hc : H.ccK = ⊤) (u0 : R.A) (S : Finset ℕ) (hS : ∀ l ∈ S, Nat.Coprime l H.QS) : Host R :=
  { H with
    u0 := u0
    levelPrimes := H.levelPrimes ∪ S
    g_level := fun i => Finset.mem_union_left _ (H.g_level i)
    pde_level := ⟨Finset.mem_union_left _ H.pde_level.1, Finset.mem_union_left _ H.pde_level.2⟩
    ccK_coprime := fun p _ => by rw [hc, Ideal.absNorm_top]; exact Nat.coprime_one_left p
    level_coprimeS := fun p hp => (Finset.mem_union.1 hp).elim (H.level_coprimeS p) (hS p) }

theorem ArithData.ccK_eq {C : FC} {s : Scale} {H : Host R} {q0 : ℕ}
    {bs : R.A → R.A → R.A} (h : ArithData C s H q0 bs) : H.ccK = ⊤ := by
  have h1 := h.1
  unfold HostVal at h1
  casesm* _ ∧ _
  assumption

def bTop (C : FC) (s : Scale) (R : Ranks) : ℝ :=
  s.b' + 2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La C.GK s * s.b' / (R.k : ℝ)

def numWords (C : FC) (s : Scale) (R : Ranks) : ℕ :=
  ⌈3 * Real.exp (C.CGam * (R.m : ℝ) ^ 5 * R.f * s.L) ^ 2 * s.x ^ C.P.CF⌉₊

def Over {C : FC} (p : Pt C) (s : Scale) (H : Host R) (hc : H.ccK = ⊤)
    (bs : R.A → R.A → R.A) (a b : ℕ → ℤ)
    (code : Finset (Fin (R.k - 2) → Bool)) (off : ℕ → ℕ → ℝ) (u0 : R.A) (T : code → ℕ) : Prop :=
  (∃ hS : ∀ l ∈ Finset.univ.image T, Nat.Coprime l H.QS,
    (⟨p.D.R, p.D.host⟩ : Σ R' : Ranks, Host R') = ⟨R, hostAt H hc u0 (Finset.univ.image T) hS⟩) ∧
  p.L.sc = s ∧
  (∀ (h t : G.HH p.D) (h' t' : R.A), h.val = h'.val → t.val = t'.val →
    (p.ta.Gx.bs h t).val = (bs h' t').val) ∧
  (∀ (j : ℕ) (t : G.HH p.D), p.ta.Gx.off j (false, t) = off j t.val) ∧
  (∀ t : p.D.host.TT, p.L.aT t = a (t : p.D.R.A).val ∧ p.L.bT t = b (t : p.D.R.A).val) ∧
  ∃ e : p.D.what₂.Word ≃ code,
    (∀ u (l : Fin (R.k - 2)), wordBits p.D u l.1 = (e u).1 l) ∧ ∀ u, (p.D.mem u).A.T = T (e u)

def ObjectsExist (Q : PtProp) : Prop :=
  ∃ Cdg : ℝ, 0 < Cdg ∧ ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∀ C8 : ℝ, 1 ≤ C8 → ∃ K0 : TransportedAlt,
    ∀ C : FC, Std C → C.P.Cpde = C8 → C.Large K0 C.P.CF → ∃ c1 : ℝ, ∀ cD ≥ c1, ∃ c2 : ℝ, ∀ ch ≥ c2, ∃ x0 : ℝ,
      ∀ s : Scale, s.eps = eps → x0 ≤ s.x →
        ∀ (R : Ranks), RankVal s R →
        ∀ (H : Host R) (q0 : ℕ) (bs : R.A → R.A → R.A)
          (hH : ArithData C s H q0 bs),
        ∀ a b : ℕ → ℤ, Win s R.k (H.TT.image Formalism.HC.Frame.A.val) (bTop C s R) a b →
        ∀ code : Finset (Fin (R.k - 2) → Bool), code.card = numWords C s R →
          ∃ off : ℕ → ℕ → ℝ, ∀ u0 : R.A, ∃ (T : code → ℕ) (p : Pt C),
            Over p s H hH.ccK_eq bs a b code off u0 T ∧
            (∀ u, p.L.AdmT u (p.D.mem u).A.T) ∧
            Val C cD ch p.L ∧ p.Has Q ∧ ChProviso_at p.L 3 ∧
            (∀ w, s.b ^ ((R.m : ℝ) / 2) ≤ (T w : ℝ) ∧ (T w : ℝ) ≤ s.b ^ (25 * (R.m : ℝ))) ∧
            FactDGam p.D Cdg

end GlobalTheory.IndefiniteRowSideFullHecke.FewBadPrimes

end
end

noncomputable section

namespace GlobalTheory.ObjExCompare

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory NumberField GlobalTheory.EX GlobalTheory.IndefiniteRowSideFullHecke.FewBadPrimes

variable {R : Ranks}

theorem one_lt_condE (H : Host R) : 1 < condE H := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.FewBadPrimes.condE
  exact lt_of_lt_of_le H.hyp.2.1.one_lt (Nat.le_mul_of_pos_left _ (Nat.mul_pos H.QS_pos H.hyp.1.pos))

theorem norm_modEq (H : Host R) (π : 𝓞 H.E) {T N : ℕ} (hN : N ≠ 0)
    (hn : (π : H.E) * H.conj (π : H.E) = (T : H.E)) (h1 : π - 1 ∈ Ideal.span {((N : ℕ) : 𝓞 H.E)}) :
    T ≡ 1 [MOD N] := by
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.1 h1
  have hyi : IsIntegral ℤ (a : H.E) := RingOfIntegers.isIntegral_coe a
  have hπ : (π : H.E) = 1 + N * (a : H.E) := by
    have := congrArg (fun z : 𝓞 H.E => (z : H.E)) ha
    simp only [map_mul, map_sub, map_one, map_natCast] at this
    linear_combination -this
  have hci : IsIntegral ℤ (H.conj (a : H.E)) := hyi.map ((H.conj : H.E →+* H.E).toIntAlgHom)
  rw [hπ, map_add (f := _), map_mul, map_one, map_natCast] at hn
  set z : H.E := a + H.conj (a : H.E) + N * (a * H.conj (a : H.E)) with hz
  have hzi : IsIntegral ℤ z :=
    (hyi.add hci).add ((isIntegral_natCast (R := ℤ) (B := H.E) N).mul (hyi.mul hci))
  have hM0 : (N : ℚ) ≠ 0 := by exact_mod_cast hN
  have h4 : z = algebraMap ℚ H.E (((T : ℚ) - 1) / N) := by
    have hM0' : (N : H.E) ≠ 0 := by exact_mod_cast hN
    rw [map_div₀, map_sub, map_one, map_natCast, map_natCast, eq_div_iff hM0', hz]
    linear_combination hn
  rw [h4, isIntegral_algebraMap_iff ] at hzi
  obtain ⟨n, hn'⟩ := IsIntegrallyClosed.isIntegral_iff.1 hzi
  have h5 : (((T : ℤ) - ((1 : ℕ) : ℤ) : ℤ) : ℚ) = ((N * n : ℤ) : ℚ) := by
    have : (n : ℚ) = ((T : ℚ) - 1) / N := by simpa using hn'
    push_cast
    rw [this]
    field_simp
  exact (Nat.modEq_iff_dvd.2 ⟨n, by exact_mod_cast h5⟩).symm

theorem T_modEq (D : D7) (u : D.what₂.Word) : (D.mem u).A.T ≡ 1 [MOD condE D.host] := by
  obtain ⟨π, -, h2, h3⟩ := D.T_norm u
  have h0 : condE D.host * (D.host.g 0 * D.host.g 1) ^ 2 ≠ 0 :=
    Nat.mul_ne_zero (by have := one_lt_condE D.host; omega)
      (pow_ne_zero _ (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero))
  exact (norm_modEq D.host π h0 h2 h3).of_mul_right _

end GlobalTheory.ObjExCompare

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HalfPeriodWeierstrassValueMemConj
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HalfPeriodWeierstrassValueMemConj
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

noncomputable section

namespace GlobalTheory.HalfPeriodValue

open Formalism.MainNotions.StandardLatticesGL3 (wpF cj FixK rhoBar StarPt w0 InRationalLattice)

theorem wpF_add_of_mem {Λ : AddSubgroup ℂ} (h : GlobalTheory.ThetaConj.IsLat Λ) {z ω : ℂ} (hz : z ∉ Λ)
    (hω : ω ∈ Λ) : wpF Λ (z + ω) = wpF Λ z := by
  obtain ⟨L, hL⟩ := h.exists_periodPair
  have hd := GlobalTheory.LatticeInvariants.invariants_dictionary L Λ hL
  have hzω : z + ω ∉ Λ := fun hh => hz (by simpa using Λ.sub_mem hh hω)
  rw [(hd.2.2.2.2.1 _ hzω).1, (hd.2.2.2.2.1 _ hz).1]
  exact L.weierstrassP_add_coe z ⟨ω, (hL ω).1 hω⟩

theorem cmGenerator_mul_mem_curveLattice {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ) :
    ∀ z ∈ lamOf D cc δ, w0 D * z ∈ lamOf D cc δ := by
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  rw [← ha]
  exact (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h).2.2.2.2 a

theorem key_of_fix {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ)
    (ρ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (hK : FixK D ⊤ ρ) {t t' : ℂ}
    (ht : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t)
    (ht' : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamConj ⊤ ρ (lamOf D cc δ)) t') :
    t' ∉ lamConj ⊤ ρ (lamOf D cc δ) ∧
      wpF (lamConj ⊤ ρ (lamOf D cc δ)) t' = cj ⊤ ρ (wpF (lamOf D cc δ) t) := by
  obtain ⟨hex, -, -, -, hmul, hord, -⟩ :=
    GlobalTheory.T.galStar_complexMultiplication_points D cc δ h ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top
  obtain ⟨cc', δ', h', -, hL⟩ :=
    GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D cc δ h ⊤ ρ hK IntermediateField.mem_top IntermediateField.mem_top 1 one_pos
  rw [GlobalTheory.ThetaConj.twoTorsionCMPoint_iff] at ht ht'
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have ha' : D.host.φ₀ ((((1 - a : 𝓞 D.host.K) : D.host.K) : D.host.E)) = 1 - w0 D := by
    rw [← ha]
    change D.host.φ₀ (algebraMap D.host.K D.host.E (algebraMap (𝓞 D.host.K) D.host.K (1 - a))) = _
    rw [map_sub, map_sub, map_sub, map_one, map_one, map_one]
    rfl
  have htn : t ∉ lamOf D cc δ := fun hh => ht.2.1 (cmGenerator_mul_mem_curveLattice h _ hh)
  obtain ⟨t'', ht''⟩ := hex t ⟨2, by norm_num, by exact_mod_cast ht.1⟩
    (Or.inr ⟨IntermediateField.mem_top, IntermediateField.mem_top⟩)
  have e2 := (hord 2 _ _ ht'').1 (by exact_mod_cast ht.1)
  have ea := (hord 1 _ _ (hmul a _ _ ht'')).2
  have eb := (hord 1 _ _ (hmul (1 - a) _ _ ht'')).2
  rw [ha] at ea
  rw [ha'] at eb
  simp only [Nat.cast_one, one_mul, Nat.cast_ofNat] at e2 ea eb
  obtain ⟨k, hk⟩ := GlobalTheory.ThetaConj.weylMatrix_mul_apply D
  have hlat : GlobalTheory.ThetaConj.IsLat (lamConj ⊤ ρ (lamOf D cc δ)) := hL ▸ GlobalTheory.ThetaConj.isLat_lamOf h'
  have hdiff : t' - t'' ∈ lamConj ⊤ ρ (lamOf D cc δ) :=
    GlobalTheory.ThetaConj.two_torsion_unique hlat (w0 D) k hk ht'.1 ht'.2.1 ht'.2.2 e2
      (fun hh => ht.2.1 (ea hh)) (fun hh => ht.2.2 (eb hh)) (by rw [hL]; exact cmGenerator_mul_mem_curveLattice h')
  rcases ht'' with ⟨hin, -⟩ | ⟨-, hn'', -, -, hwp, -⟩
  · exact absurd hin htn
  · refine ⟨fun hh => hn'' (by simpa using (lamConj ⊤ ρ (lamOf D cc δ)).sub_mem hh hdiff), ?_⟩
    rw [← hwp, ← wpF_add_of_mem hlat hn'' hdiff, add_sub_cancel]

theorem wpF_conj (Λ : AddSubgroup ℂ) (z : ℂ) :
    wpF (Λ.map (starRingEnd ℂ).toAddMonoidHom) (starRingEnd ℂ z) = starRingEnd ℂ (wpF Λ z) := by
  let e : {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃
      {w : ℂ // w ∈ Λ.map (starRingEnd ℂ).toAddMonoidHom ∧ w ≠ 0} :=
    { toFun := fun w => ⟨starRingEnd ℂ w, by rw [GlobalTheory.ThetaConj.mem_conj, Complex.conj_conj]; exact w.2.1,
        by simpa using w.2.2⟩
      invFun := fun w => ⟨starRingEnd ℂ w, GlobalTheory.ThetaConj.mem_conj.1 w.2.1, by simpa using w.2.2⟩
      left_inv := fun w => by ext; simp
      right_inv := fun w => by ext; simp }
  unfold wpF
  rw [map_add (f := _), Complex.conj_tsum, ← e.tsum_eq]
  simp [e, map_sub]

theorem key_top {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ)
    (ρ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) {t t' : ℂ}
    (ht : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t)
    (ht' : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamConj ⊤ ρ (lamOf D cc δ)) t') :
    t' ∉ lamConj ⊤ ρ (lamOf D cc δ) ∧
      wpF (lamConj ⊤ ρ (lamOf D cc δ)) t' = cj ⊤ ρ (wpF (lamOf D cc δ) t) := by
  obtain ⟨hK, hT, -⟩ := GlobalTheory.T.cmTheta_complexConjugation_compatible D cc δ h ⊤ ρ
    ⟨fun _ _ => IntermediateField.mem_top, IntermediateField.mem_top, IntermediateField.mem_top⟩
  rcases hK with hK | hK
  · exact key_of_fix h ρ hK ht ht'
  · have hL : lamConj ⊤ (rhoBar ⊤ ρ) (lamOf D cc δ) =
        (lamConj ⊤ ρ (lamOf D cc δ)).map (starRingEnd ℂ).toAddMonoidHom := congrArg Tor.abelian₂ hT
    obtain ⟨hn, hw⟩ := key_of_fix h _ hK (t' := starRingEnd ℂ t') ht (hL ▸ GlobalTheory.ThetaConj.twoTorsionCMPoint_complexConj ht')
    rw [hL, wpF_conj, GlobalTheory.ThetaConj.cj_rhoBar] at hw
    rw [hL, GlobalTheory.ThetaConj.mem_conj, Complex.conj_conj] at hn
    exact ⟨hn, (starRingEnd ℂ).injective hw⟩

theorem halfPeriod_value : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t →
    ∃ e g : M, (g : ℂ) = g2 (lamOf D cc δ) ∧ lamConj M M.val (lamOf D cc δ) = lamOf D cc δ ∧
      ∀ ρ : M →ₐ[ℚ] ℂ, Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧
        g2 (lamConj M ρ (lamOf D cc δ)) = ρ g ∧ t ρ ∉ lamConj M ρ (lamOf D cc δ) ∧
        Formalism.MainNotions.StandardLatticesGL3.wpF (lamConj M ρ (lamOf D cc δ)) (t ρ) = ρ e := by
  intro D cc δ M _ t hS
  obtain ⟨hcc, hδ, hdata, ht⟩ := hS
  have h : Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have hg2 : g2 (lamOf D cc δ) ∈ M := hdata.2.1
  have hg3 : g3 (lamOf D cc δ) ∈ M := hdata.2.2
  have hlat := GlobalTheory.ThetaConj.isLat_lamOf h
  have hdisc : Formalism.MainNotions.TaylorLogMetric.discr (lamOf D cc δ) = 1 :=
    (GlobalTheory.CurveLattice.lattice_of_curve D (GlobalTheory.InducedType.induced_type D).1 cc δ h).2.2.1
  have hself : lamConj M M.val (lamOf D cc δ) = lamOf D cc δ :=
    GlobalTheory.ThetaConj.lamConj_eq_self hlat
      (by unfold Formalism.MainNotions.StandardLatticesGL3.cj Formalism.MainNotions.TaylorLogMetric.liftM; rw [dite_eq_left hg2]; rfl)
      (by unfold Formalism.MainNotions.StandardLatticesGL3.cj Formalism.MainNotions.TaylorLogMetric.liftM; rw [dite_eq_left hg3]; rfl)
  have ht0 : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) (t M.val) := by
    have := ht M.val
    rw [hself] at this
    exact this
  have he : wpF (lamOf D cc δ) (t M.val) ∈ M := by
    obtain ⟨y, hy⟩ := GlobalTheory.GaloisDescent.complex_mem_range_of_forall_algEquiv (K := M)
      (wpF (lamOf D cc δ) (t M.val)) (fun σ => by
        have hσ : ∀ z ∈ M, cj ⊤ (GlobalTheory.ThetaConj.topHom (σ : ℂ →+* ℂ)) z = z := fun z hz => by
          rw [GlobalTheory.ThetaConj.cj_top]; exact σ.commutes ⟨z, hz⟩
        have hL := GlobalTheory.ThetaConj.lamConj_eq_self hlat (hσ _ hg2) (hσ _ hg3)
        have := (key_top h (GlobalTheory.ThetaConj.topHom (σ : ℂ →+* ℂ)) ht0 (by rw [hL]; exact ht0)).2
        rw [hL, GlobalTheory.ThetaConj.cj_top] at this
        exact this.symm)
    rw [← hy]
    exact y.2
  have hg2M : Formalism.MainNotions.TaylorLogMetric.liftM M (g2 (lamOf D cc δ)) = ⟨_, hg2⟩ := by simp [Formalism.MainNotions.TaylorLogMetric.liftM, hg2]
  have hg3M : Formalism.MainNotions.TaylorLogMetric.liftM M (g3 (lamOf D cc δ)) = ⟨_, hg3⟩ := by simp [Formalism.MainNotions.TaylorLogMetric.liftM, hg3]
  have hone : (⟨_, hg2⟩ : M) ^ 3 - 27 * (⟨_, hg3⟩ : M) ^ 2 = 1 :=
    by
    have := hdisc
    unfold Formalism.MainNotions.TaylorLogMetric.discr at this
    ext; push_cast; exact this
  refine ⟨⟨_, he⟩, ⟨_, hg2⟩, rfl, hself, fun ρ => ?_⟩
  have hρ1 : ρ ⟨_, hg2⟩ ^ 3 - 27 * ρ ⟨_, hg3⟩ ^ 2 = 1 := by
    rw [← map_pow, ← map_pow, ← map_ofNat ρ 27, ← map_mul, ← map_sub, hone, map_one]
  have hspec : g2 (lamConj M ρ (lamOf D cc δ)) = ρ ⟨_, hg2⟩ ∧
      g3 (lamConj M ρ (lamOf D cc δ)) = ρ ⟨_, hg3⟩ := by
    obtain ⟨L0, hL0⟩ := hlat.exists_periodPair
    obtain ⟨L', h2', h3'⟩ := (GlobalTheory.LatticeInvariants.invariants_dictionary L0 _ hL0).2.2.2.2.2.2 _ _
      (by rw [hρ1]; exact one_ne_zero)
    have hw := GlobalTheory.LatticeInvariants.invariants_dictionary L' L'.lattice.toAddSubgroup (fun _ => Iff.rfl)
    have hs := Classical.epsilon_spec (p := fun Λ' : AddSubgroup ℂ =>
      g2 Λ' = ρ (Formalism.MainNotions.TaylorLogMetric.liftM M (g2 (lamOf D cc δ))) ∧
        g3 Λ' = ρ (Formalism.MainNotions.TaylorLogMetric.liftM M (g3 (lamOf D cc δ))))
      ⟨L'.lattice.toAddSubgroup, by rw [hw.1, h2', hg2M], by rw [hw.2.1, h3', hg3M]⟩
    exact ⟨hs.1.trans (congrArg ρ hg2M), hs.2.trans (congrArg ρ hg3M)⟩
  have hcM : Set.Countable (M : Set ℂ) := (Algebraic.countable ℚ ℂ).mono fun x hx =>
    show IsAlgebraic ℚ x from
      (IntermediateField.isAlgebraic_iff (x := (⟨x, hx⟩ : M))).mp (Algebra.IsAlgebraic.isAlgebraic _)
  haveI : Countable M := hcM.to_subtype
  obtain ⟨σ, hσ⟩ := GlobalTheory.GaloisDescent.exists_complex_ringEquiv_comp_eq (K := M) M.val.toRingHom ρ.toRingHom
  have hcj : ∀ z (hz : z ∈ M), cj M ρ z = cj ⊤ (GlobalTheory.ThetaConj.topHom σ.toRingHom) z := fun z hz => by
    rw [GlobalTheory.ThetaConj.cj_of_mem _ _ hz, GlobalTheory.ThetaConj.cj_top]
    exact (hσ ⟨z, hz⟩).symm
  have hL : lamConj M ρ (lamOf D cc δ) = lamConj ⊤ (GlobalTheory.ThetaConj.topHom σ.toRingHom) (lamOf D cc δ) :=
    GlobalTheory.ThetaConj.lamConj_congr (hcj _ hg2) (hcj _ hg3)
  have ht' : Formalism.MainNotions.GL3Theta.IsTwoTorsionPointUnkilled D (lamConj ⊤ (GlobalTheory.ThetaConj.topHom σ.toRingHom) (lamOf D cc δ)) (t ρ) := by
    have := ht ρ
    rw [hL] at this
    exact this
  obtain ⟨hn, hw⟩ := key_top h (GlobalTheory.ThetaConj.topHom σ.toRingHom) ht0 ht'
  refine ⟨?_, hspec.1, hL ▸ hn, ?_⟩
  · unfold Formalism.MainNotions.TaylorLogMetric.discr
    rw [hspec.1, hspec.2, hρ1]
  · rw [hL, hw, GlobalTheory.ThetaConj.cj_top]
    exact hσ ⟨_, he⟩

end GlobalTheory.HalfPeriodValue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HalfPeriodWeierstrassValueMemConjStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric GlobalTheory.Glob.IntegralWittCoefficients GlobalTheory.IndefiniteRowSideFullHecke

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfPeriod_weierstrassValue_mem_conj : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (M : IntermediateField ℚ ℂ)
    [FiniteDimensional ℚ M] (t : (M →ₐ[ℚ] ℂ) → ℂ), SignedLogMeans.HidaSetting D cc δ M t →
    ∃ e g : M, (g : ℂ) = g2 (lamOf D cc δ) ∧ lamConj M M.val (lamOf D cc δ) = lamOf D cc δ ∧
      ∀ ρ : M →ₐ[ℚ] ℂ, Formalism.MainNotions.TaylorLogMetric.discr (lamConj M ρ (lamOf D cc δ)) = 1 ∧
        g2 (lamConj M ρ (lamOf D cc δ)) = ρ g ∧ t ρ ∉ lamConj M ρ (lamOf D cc δ) ∧
        Formalism.MainNotions.StandardLatticesGL3.wpF (lamConj M ρ (lamOf D cc δ)) (t ρ) = ρ e := by
  first | exact @GlobalTheory.HalfPeriodValue.halfPeriod_value | exact GlobalTheory.HalfPeriodValue.halfPeriod_value | (intros; apply GlobalTheory.HalfPeriodValue.halfPeriod_value <;> assumption)
end
end
