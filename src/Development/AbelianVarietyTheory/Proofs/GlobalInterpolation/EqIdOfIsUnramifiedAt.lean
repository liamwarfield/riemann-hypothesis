module

public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerCoefficientNormLeOneIffJetsBoundedMeasureM
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientMul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqIdOfIsUnramifiedAt
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.UnramifiedDiscriminant

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E}

private lemma isCMExt_conj_ne_id (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) : σ ≠ AlgHom.id F E := by
  obtain ⟨-, hE, -, hτ⟩ := h
  intro hσ
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  have hc := hE.isComplex (InfinitePlace.mk τ)
  rw [InfinitePlace.isComplex_mk_iff] at hc
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  have hx := hτ τ x
  rw [hσ, AlgHom.id_apply] at hx
  exact hx.symm

private lemma isCMExt_mem_range_of_conj_fixed (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) {x : E} (hx : σ x = x) :
    x ∈ Set.range (algebraMap F E) := by
  have hprime : (Module.finrank F E).Prime := by rw [h.2.2.1]; exact Nat.prime_two
  haveI := Subalgebra.isSimpleOrder_of_finrank_prime F E hprime
  rcases eq_bot_or_eq_top (AlgHom.equalizer σ (AlgHom.id F E)) with h0 | h1
  · have hmem : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := hx
    rw [h0] at hmem
    exact Algebra.mem_bot.mp hmem
  · exfalso
    apply isCMExt_conj_ne_id h
    ext y
    have hmem : y ∈ AlgHom.equalizer σ (AlgHom.id F E) := h1 ▸ Algebra.mem_top
    exact hmem

theorem _root_.GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (a : 𝓞 E) (ha : σ a = a) :
    ∃ t : 𝓞 F, algebraMap (𝓞 F) (𝓞 E) t = a := by
  obtain ⟨f, hf⟩ := isCMExt_mem_range_of_conj_fixed h ha
  have hint : IsIntegral ℤ f := by
    rw [← isIntegral_algebraMap_iff (B := E), hf]
    exact RingOfIntegers.isIntegral_coe a
  refine ⟨⟨f, hint⟩, ?_⟩
  ext
  exact hf

private lemma isCMExt_conj_conj (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨-, -, -, hτ⟩ := h
  let τ : E →+* ℂ := (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
  apply τ.injective
  rw [hτ, hτ, star_star]

theorem _root_.GlobalTheory.UnramifiedDiscriminant.exists_discr_notMem (F E : Type) [Field F] [NumberField F] [Field E]
    [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (h : _root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCMExt F E σ)
    (v : HeightOneSpectrum (𝓞 F)) (hv : _root_.GlobalTheory.IndefiniteRowSideFullHecke.SelfDualUnramifiedPlaces.UnramifiedPlace F E v) :
    ∃ (w : E) (t n : 𝓞 F), w + σ w = algebraMap F E (t : F) ∧ w * σ w = algebraMap F E (n : F) ∧
      t ^ 2 - 4 * n ∉ v.asIdeal := by
  have hinj : Function.Injective (algebraMap (𝓞 F) (𝓞 E)) := FaithfulSMul.algebraMap_injective _ _
  obtain ⟨P, -, hPp, hPv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 E))
    (by rw [(show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]; exact bot_le)
  have hPne : P ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hPv, (show Ideal.under _ ⊥ = ⊥ from Ideal.comap_bot_of_injective _ hinj)]
  haveI : P.LiesOver v.asIdeal := ⟨hPv.symm⟩
  haveI : Algebra.IsUnramifiedAt (𝓞 F) P := hv ⟨P, hPp, hPne⟩ ⟨hPv.symm⟩
  let σ' : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Function.Involutive.bijective (isCMExt_conj_conj h))
  haveI : IsGalois F E := by
    refine IsGalois.of_fixedField_eq_bot F E (eq_bot_iff.mpr fun x hx => ?_)
    exact IntermediateField.mem_bot.mpr (isCMExt_mem_range_of_conj_fixed h
      ((IntermediateField.mem_fixedField_iff _ _).mp hx σ' (Subgroup.mem_top _)))
  have hcard : Nat.card (P.inertia (E ≃ₐ[F] E)) = 1 := by
    rw [Ideal.card_inertia_eq_ramificationIdxIn v.asIdeal P,
      Ideal.ramificationIdxIn_eq_ramificationIdx v.asIdeal P (E ≃ₐ[F] E)]
    exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  obtain ⟨x, hx⟩ : ∃ x : 𝓞 E, σ' • x - x ∉ P := by
    by_contra hcon
    push_neg at hcon
    have hmem : σ' ∈ P.inertia (E ≃ₐ[F] E) := hcon
    haveI := (Nat.card_eq_one_iff_unique.mp hcard).1
    have h1 : σ' = 1 := congrArg Subtype.val (Subsingleton.elim (⟨σ', hmem⟩ : P.inertia _) 1)
    apply isCMExt_conj_ne_id h
    ext z
    exact DFunLike.congr_fun h1 z
  set y : 𝓞 E := σ' • x
  have hy : (y : E) = σ x := rfl
  obtain ⟨t, ht⟩ := _root_.GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq h (x + y) (by
    show σ ((x : E) + σ x) = (x : E) + σ x
    rw [map_add (f := _), isCMExt_conj_conj h, add_comm])
  obtain ⟨n, hn⟩ := _root_.GlobalTheory.UnramifiedDiscriminant.exists_int_of_conj_eq h (x * y) (by
    show σ ((x : E) * σ x) = (x : E) * σ x
    rw [map_mul, isCMExt_conj_conj h, mul_comm])
  refine ⟨x, t, n, ?_, ?_, ?_⟩
  · rw [← hy]
    exact (congrArg (fun z : 𝓞 E => (z : E)) ht).symm
  · rw [← hy]
    exact (congrArg (fun z : 𝓞 E => (z : E)) hn).symm
  · intro hmem
    have hP : algebraMap (𝓞 F) (𝓞 E) (t ^ 2 - 4 * n) ∈ P := by
      rw [← hPv] at hmem
      exact Ideal.mem_comap.mp hmem
    have heq : algebraMap (𝓞 F) (𝓞 E) (t ^ 2 - 4 * n) = (y - x) ^ 2 := by
      rw [map_sub, map_pow, map_mul, ht, hn, map_ofNat]
      ring
    rw [heq] at hP
    exact hx (hPp.mem_of_pow_mem 2 hP)

end GlobalTheory.UnramifiedDiscriminant
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeberFunctionsRootsOfCubicOfHalfPeriodDiff
open Complex

open Polynomial
open UpperHalfPlane hiding I

noncomputable section

namespace GlobalTheory.WeberCubicAlgebra

lemma half_root (L : PeriodPair) {t : ℂ} (h2 : 2 * t ∈ L.lattice) (ht : t ∉ L.lattice) :
    4 * L.weierstrassP t ^ 3 - L.g₂ * L.weierstrassP t - L.g₃ = 0 := by
  have e1 := L.derivWeierstrassP_add_coe (-t) ⟨2 * t, h2⟩
  rw [L.derivWeierstrassP_neg] at e1
  have e2 : -t + 2 * t = t := by ring
  simp only [e2] at e1
  have e3 : L.derivWeierstrassP t = 0 := by linear_combination e1 / 2
  rw [← L.derivWeierstrassP_sq t ht, e3]
  simp

lemma roots_alg {e1 e2 e3 g h P A B D : ℂ} (h12 : e1 ≠ e2) (h13 : e1 ≠ e3) (h23 : e2 ≠ e3)
    (r1 : 4 * e1 ^ 3 - g * e1 - h = 0) (r2 : 4 * e2 ^ 3 - g * e2 - h = 0)
    (r3 : 4 * e3 ^ 3 - g * e3 - h = 0)
    (d1 : e1 - e2 = P * A) (d2 : e1 - e3 = P * B) (d3 : e3 - e2 = P * D) :
    g = 2 / 3 * P ^ 2 * (A ^ 2 + B ^ 2 + D ^ 2) ∧
      g ^ 3 - 27 * h ^ 2 = 16 * P ^ 6 * (A * B * D) ^ 2 := by
  have a12 : 4 * (e1 ^ 2 + e1 * e2 + e2 ^ 2) = g :=
    mul_left_cancel₀ (sub_ne_zero.2 h12) (by linear_combination r1 - r2)
  have a13 : 4 * (e1 ^ 2 + e1 * e3 + e3 ^ 2) = g :=
    mul_left_cancel₀ (sub_ne_zero.2 h13) (by linear_combination r1 - r3)
  have s : e1 + e2 + e3 = 0 := by
    have : (e2 - e3) * (e1 + e2 + e3) = (e2 - e3) * 0 := by linear_combination (a12 - a13) / 4
    exact mul_left_cancel₀ (sub_ne_zero.2 h23) this
  have hh : h = 4 * e1 ^ 3 - g * e1 := by linear_combination -r1
  have k1 : (P * A) ^ 2 = (e1 - e2) ^ 2 := by rw [d1]
  have k2 : (P * B) ^ 2 = (e1 - e3) ^ 2 := by rw [d2]
  have k3 : (P * D) ^ 2 = (e3 - e2) ^ 2 := by rw [d3]
  obtain rfl : e3 = -e1 - e2 := by linear_combination s
  subst hh
  subst a12
  constructor
  · linear_combination (-2 / 3 : ℂ) * (k1 + k2 + k3)
  · have : 16 * P ^ 6 * (A * B * D) ^ 2 = 16 * ((P * A) ^ 2 * (P * B) ^ 2 * (P * D) ^ 2) := by ring
    rw [this, k1, k2, k3]
    ring

lemma coeffs (A B D j F0 F1 F2 : ℂ) (hA : A ≠ 0) (hB : B ≠ 0) (hD : D ≠ 0) (hs : A = B + D)
    (h0 : F0 * (B * D) = 16 * A ^ 2) (h1 : F1 * (A * D) = 16 * B ^ 2)
    (h2 : F2 * (A * B) = 16 * D ^ 2) (hj : j * (A * B * D) ^ 2 = 32 * (A ^ 2 + B ^ 2 + D ^ 2) ^ 3) :
    F0 - F1 - F2 = 48 ∧ -(F0 * F1) - F0 * F2 + F1 * F2 = 768 - j ∧ F0 * F1 * F2 = 4096 := by
  have e0 : F0 = 16 * A ^ 2 / (B * D) := by rw [eq_div_iff (mul_ne_zero hB hD)]; exact h0
  have e1 : F1 = 16 * B ^ 2 / (A * D) := by rw [eq_div_iff (mul_ne_zero hA hD)]; exact h1
  have e2 : F2 = 16 * D ^ 2 / (A * B) := by rw [eq_div_iff (mul_ne_zero hA hB)]; exact h2
  have ej : j = 32 * (A ^ 2 + B ^ 2 + D ^ 2) ^ 3 / (A * B * D) ^ 2 := by
    rw [eq_div_iff (pow_ne_zero _ (mul_ne_zero (mul_ne_zero hA hB) hD))]; exact hj
  subst e0 e1 e2 ej hs
  refine ⟨?_, ?_, ?_⟩ <;> field_simp <;> ring

lemma cubic_eq (j F0 F1 F2 : ℂ)
    (h : F0 - F1 - F2 = 48 ∧ -(F0 * F1) - F0 * F2 + F1 * F2 = 768 - j ∧ F0 * F1 * F2 = 4096) :
    ((X - C 16) ^ 3 - C j * X : ℂ[X]) = (X - C F0) * (X - C (-F1)) * (X - C (-F2)) := by
  obtain ⟨s1, s2, s3⟩ := h
  have e : ((X - C F0) * (X - C (-F1)) * (X - C (-F2)) : ℂ[X]) =
      X ^ 3 - C (F0 - F1 - F2) * X ^ 2 + C (-(F0 * F1) - F0 * F2 + F1 * F2) * X - C (F0 * F1 * F2) := by
    simp only [map_sub, map_neg, map_mul, map_add (f := _)]
    ring
  rw [e, s1, s2, s3]
  simp only [map_sub, map_ofNat]
  ring

end GlobalTheory.WeberCubicAlgebra

namespace GlobalTheory.WeberCubicAlgebra

open GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber in
theorem weberCubic_of_halfPeriodDiff : ∀ τ : UpperHalfPlane, GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.HalfPeriodDiff τ →
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.JacobiProduct τ → GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.ThetaWeber τ → GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.WeberCubic τ := by
  intro τ hd hj hw
  obtain ⟨d1, d2, d3⟩ := hd
  obtain ⟨w0, w1, w2⟩ := hw
  unfold JacobiProduct at hj
  have hη : ModularForm.eta (τ : ℂ) ≠ 0 := ModularForm.eta_ne_zero τ.2
  have hp : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hprod : thetaConst 0 0 τ * thetaConst 0 1 τ * thetaConst 1 0 τ ≠ 0 := by
    rw [hj]
    exact mul_ne_zero two_ne_zero (pow_ne_zero _ hη)
  have t0 : thetaConst 0 0 τ ≠ 0 := fun h => hprod (by simp [h])
  have t1 : thetaConst 0 1 τ ≠ 0 := fun h => hprod (by simp [h])
  have t2 : thetaConst 1 0 τ ≠ 0 := fun h => hprod (by simp [h])
  obtain ⟨n1, n2, n3⟩ := halfPeriods_notMem τ
  have mem : ∀ p q : ℤ, ((p : ℂ) * (τ : ℂ) + q) ∈ (GlobalTheory.periodPairOfTau τ).lattice := fun p q => by
    rw [GlobalTheory.mem_lattice_periodPairOfTau]
    exact ⟨p, q, by ring⟩
  have r1 := half_root (GlobalTheory.periodPairOfTau τ) (t := 1 / 2) (by simpa using mem 0 1) n1
  have r2 := half_root (GlobalTheory.periodPairOfTau τ) (t := (τ : ℂ) / 2) (by
    have := mem 1 0
    convert this using 1
    push_cast
    ring) n2
  have r3 := half_root (GlobalTheory.periodPairOfTau τ) (t := (1 + (τ : ℂ)) / 2) (by
    have := mem 1 1
    convert this using 1
    push_cast
    ring) n3
  have hP : ((Real.pi : ℂ) ^ 2) ≠ 0 := pow_ne_zero _ hp
  have h12 : wp τ (1 / 2) ≠ wp τ ((τ : ℂ) / 2) := by
    rw [← sub_ne_zero, d1]
    exact mul_ne_zero hP (pow_ne_zero _ t0)
  have h13 : wp τ (1 / 2) ≠ wp τ ((1 + (τ : ℂ)) / 2) := by
    rw [← sub_ne_zero, d2]
    exact mul_ne_zero hP (pow_ne_zero _ t1)
  have h23 : wp τ ((τ : ℂ) / 2) ≠ wp τ ((1 + (τ : ℂ)) / 2) := by
    intro h
    have h' : wp τ ((1 + (τ : ℂ)) / 2) - wp τ ((τ : ℂ) / 2) = 0 := by rw [h]; ring
    rw [d3] at h'
    exact mul_ne_zero hP (pow_ne_zero _ t2) h'
  have hw1 : wp τ (1 / 2) = (GlobalTheory.periodPairOfTau τ).weierstrassP (1 / 2) := rfl
  have hw2 : wp τ ((τ : ℂ) / 2) = (GlobalTheory.periodPairOfTau τ).weierstrassP ((τ : ℂ) / 2) := rfl
  have hw3 : wp τ ((1 + (τ : ℂ)) / 2) = (GlobalTheory.periodPairOfTau τ).weierstrassP ((1 + (τ : ℂ)) / 2) := rfl
  rw [← hw1] at r1
  rw [← hw2] at r2
  rw [← hw3] at r3
  obtain ⟨hg, hdisc⟩ := roots_alg h12 h13 h23 r1 r2 r3 d1 d2 d3
  have hjl : jLat τ * ((GlobalTheory.periodPairOfTau τ).g₂ ^ 3 - 27 * (GlobalTheory.periodPairOfTau τ).g₃ ^ 2) =
      1728 * (GlobalTheory.periodPairOfTau τ).g₂ ^ 3 := by
    rw [jLat_eq, div_mul_cancel₀ _ (disc_ne_zero τ)]
  rw [hdisc, hg] at hjl
  have hs : thetaConst 0 0 τ ^ 4 = thetaConst 0 1 τ ^ 4 + thetaConst 1 0 τ ^ 4 := by
    apply mul_left_cancel₀ hP
    linear_combination -d1 + d2 + d3
  have hJ4 : thetaConst 0 0 τ ^ 4 * thetaConst 0 1 τ ^ 4 * thetaConst 1 0 τ ^ 4 =
      16 * ModularForm.eta (τ : ℂ) ^ 12 := by
    have := congrArg (· ^ 4) hj
    linear_combination this
  have a0 : (thetaConst 0 0 τ ^ 4) ^ 3 = ModularForm.eta (τ : ℂ) ^ 12 * weberF τ ^ 24 := by
    rw [w0]; ring
  have a1 : (thetaConst 0 1 τ ^ 4) ^ 3 = ModularForm.eta (τ : ℂ) ^ 12 * weberF₁ τ ^ 24 := by
    rw [w1]; ring
  have a2 : (thetaConst 1 0 τ ^ 4) ^ 3 = ModularForm.eta (τ : ℂ) ^ 12 * weberF₂ τ ^ 24 := by
    rw [w2]; ring
  have A0 := pow_ne_zero 4 t0
  have B0 := pow_ne_zero 4 t1
  have D0 := pow_ne_zero 4 t2
  apply cubic_eq
  apply coeffs _ _ _ _ _ _ _ A0 B0 D0 hs
  · apply mul_left_cancel₀ A0
    linear_combination weberF τ ^ 24 * hJ4 - 16 * a0
  · apply mul_left_cancel₀ B0
    linear_combination weberF₁ τ ^ 24 * hJ4 - 16 * a1
  · apply mul_left_cancel₀ D0
    linear_combination weberF₂ τ ^ 24 * hJ4 - 16 * a2
  · have h16 : (16 : ℂ) * ((Real.pi : ℂ) ^ 2) ^ 6 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hP)
    apply mul_left_cancel₀ h16
    linear_combination hjl

end GlobalTheory.WeberCubicAlgebra
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsOfSpanImagQuadratic
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsOfSpanImagQuadratic
noncomputable section

namespace GlobalTheory.MomN

open GlobalTheory.MomOne PowerSeries
open scoped ComplexConjugate

theorem exists_padicInt_inv {q : ℕ} [Fact q.Prime] {s : ℕ} (h : Nat.Coprime s q) :
    ∃ u : ℤ_[q], (s : ℤ_[q]) * u = 1 := by
  have h1 : IsUnit (s : ℤ_[q]) := by
    rw [PadicInt.isUnit_iff]
    have hq : ¬ (q : ℤ) ∣ (s : ℤ) := by
      intro hd
      have hd' : q ∣ s := Int.natCast_dvd_natCast.mp hd
      have : q ∣ 1 := by
        have := Nat.dvd_gcd hd' (dvd_refl q)
        rwa [h] at this
      exact (Fact.out : q.Prime).one_lt.ne' (Nat.dvd_one.mp this)
    have h2 := (PadicInt.norm_int_lt_one_iff_dvd (p := q) (s : ℤ)).not.mpr hq
    have h3 : ‖((s : ℤ) : ℤ_[q])‖ ≤ 1 := PadicInt.norm_le_one _
    have h4 : ‖((s : ℤ) : ℤ_[q])‖ = 1 := le_antisymm h3 (not_lt.mp h2)
    simpa using h4
  obtain ⟨u, hu⟩ := h1
  exact ⟨((u⁻¹ : ℤ_[q]ˣ) : ℤ_[q]), by rw [← hu]; simp⟩

theorem latInt_of_span : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (d : ℕ) (ω : ℂ_[q]) (Λ : AddSubgroup V) (κ : Type) [Fintype κ] (b : κ → V) (G : V → ℂ), d.Prime → d % 16 = 7 → Split d q → (∀ x ∈ Λ, ∃ s : ℕ, Nat.Coprime s q ∧ ∃ c : κ → ℂ, (∀ i, InOK d (c i)) ∧ (s : ℂ) • x = ∑ i, c i • b i) → MomInt ι (fun i => ι.symm ω • b i) G → LatInt ι ω Λ G := by
  intro q _ ι V _ _ d ω Λ κ _ b G hd h16 hS hspan hM κ' _ v hv
  have hOK := GlobalTheory.MomOne.okArith d q ι hd h16 hS
  choose s hs c hc hx using fun i => hspan (v i) (hv i)
  have ha : ∀ i j, ∃ a : ℤ_[q], ι (c i j) = zc a := fun i j => (hOK.2.1 _ (hc i j)).1
  choose a ha using ha
  choose u hu using fun i => exists_padicInt_inv (q := q) (hs i)
  have hs0 : ∀ i, (s i : ℂ) ≠ 0 := by
    intro i h0
    have h1 : s i = 0 := by exact_mod_cast h0
    have := hu i
    rw [h1] at this
    simp at this
  have hzu : ∀ i, (s i : ℂ_[q]) * zc (u i) = 1 := by
    intro i
    have := congrArg (zc (q := q)) (hu i)
    simpa [zc] using this
  refine GlobalTheory.T.jetsAreBoundedMeasureMoments_padicInt_matrix_change q ι V κ κ' (fun i => ι.symm ω • b i) (fun i => ι.symm ω • v i)
    (fun i j => c i j / s i) (fun i j => a i j * u i) G ?_ ?_ hM
  · intro i j
    have hsq : (s i : ℂ_[q]) ≠ 0 := fun h0 => by
      have := hzu i
      rw [h0] at this
      simp at this
    have e1 : zc (a i j * u i) = zc (a i j) * zc (u i) := by simp [zc]
    rw [map_div₀, ha, map_natCast, e1, div_eq_iff hsq, mul_assoc, mul_comm (zc (u i)), hzu, mul_one]
  · intro i
    have e : v i = (s i : ℂ)⁻¹ • ∑ j, c i j • b j := by
      rw [← hx i, smul_smul, inv_mul_cancel₀ (hs0 i), one_smul]
    conv_lhs => rw [e]
    rw [Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [smul_smul]
    congr 1
    field_simp [hs0 i]

end GlobalTheory.MomN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsOfSpanImagQuadraticStatement
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeJetsAreBoundedMoments_of_span_imagQuadratic : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (d : ℕ) (ω : ℂ_[q]) (Λ : AddSubgroup V) (κ : Type) [Fintype κ] (b : κ → V) (G : V → ℂ), d.Prime → d % 16 = 7 → Split d q → (∀ x ∈ Λ, ∃ s : ℕ, Nat.Coprime s q ∧ ∃ c : κ → ℂ, (∀ i, InOK d (c i)) ∧ (s : ℂ) • x = ∑ i, c i • b i) → MomInt ι (fun i => ι.symm ω • b i) G → LatInt ι ω Λ G := by
  first | exact @GlobalTheory.MomN.latInt_of_span | exact GlobalTheory.MomN.latInt_of_span | (intros; apply GlobalTheory.MomN.latInt_of_span <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DirichletLZerosEqPrimitiveCharacterZeros
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DirichletLZerosEqPrimitiveCharacterZeros
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin

theorem _root_.GlobalTheory.Lin.zeros_eq_zeros_primitiveCharacter :
    ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 0 < s.re → (χ ≠ 1 ∨ s ≠ 1) →
      haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
      (LFunction χ s = 0 ↔ LFunction χ.primitiveCharacter s = 0) ∧
        _root_.GlobalTheory.Lin.ord χ s = _root_.GlobalTheory.Lin.ord χ.primitiveCharacter s := by
  intro q _ χ s hs hχs
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set E : ℂ → ℂ := fun z => ∏ p ∈ q.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-z))
    with hE
  have hform : ∀ z, (χ.primitiveCharacter ≠ 1 ∨ z ≠ 1) →
      LFunction χ z = LFunction χ.primitiveCharacter z * E z := by
    intro z hz
    have h := LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter hz
    rwa [changeLevel_primitiveCharacter] at h
  have hprim : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := by
    rcases hχs with h | h
    · left
      intro h1
      apply h
      calc χ = changeLevel χ.conductor_dvd_level χ.primitiveCharacter :=
            (changeLevel_primitiveCharacter χ).symm
        _ = 1 := by rw [h1, map_one]
    · exact Or.inr h
  have hEne : E s ≠ 0 := by
    rw [hE]
    refine Finset.prod_ne_zero_iff.2 (fun p hp => ?_)
    have hp1 : 1 < p := (Nat.prime_of_mem_primeFactors hp).one_lt
    have hlt : ‖χ.primitiveCharacter p * (p : ℂ) ^ (-s)‖ < 1 := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
      calc _ ≤ 1 * (p : ℝ) ^ (-s.re) :=
            mul_le_mul_of_nonneg_right (norm_le_one _ _) (by positivity)
        _ < 1 := by
            rw [one_mul]
            exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp1) (by linarith)
    intro h0
    rw [sub_eq_zero] at h0
    rw [← h0, norm_one] at hlt
    exact lt_irrefl _ hlt
  have hEd : Differentiable ℂ E := by
    have h : Differentiable ℂ (∏ p ∈ q.primeFactors,
        fun z : ℂ => 1 - χ.primitiveCharacter p * (p : ℂ) ^ (-z)) :=
      Differentiable.finsetProd (fun p hp => by
        have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
        fun_prop (disch := exact Or.inl hp0))
    rw [hE]
    convert h using 1
    ext z
    simp [Finset.prod_apply]
  have hEa : AnalyticAt ℂ E s := hEd.analyticAt s
  have hLa : AnalyticAt ℂ (LFunction χ.primitiveCharacter) s := by
    by_cases h1 : χ.primitiveCharacter = 1
    · have hs1 : s ≠ 1 := hprim.resolve_left (not_not.2 h1)
      exact DifferentiableOn.analyticAt (s := {z | z ≠ 1})
        (fun z hz => (differentiableAt_LFunction _ z (Or.inl hz)).differentiableWithinAt)
        (isOpen_ne.mem_nhds hs1)
    · exact (differentiable_LFunction h1).analyticAt s
  have hev : LFunction χ =ᶠ[𝓝 s] LFunction χ.primitiveCharacter * E := by
    rcases hprim with h1 | h1
    · exact Eventually.of_forall (fun z => hform z (Or.inl h1))
    · filter_upwards [isOpen_ne.mem_nhds h1] with z hz using hform z (Or.inr hz)
  refine ⟨?_, ?_⟩
  · rw [hform s hprim, mul_eq_zero]
    simp [hEne]
  · show (analyticOrderAt _ s).toNat = (analyticOrderAt _ s).toNat
    rw [analyticOrderAt_congr hev, analyticOrderAt_mul hLa hEa,
      analyticOrderAt_eq_zero.2 (Or.inr hEne), add_zero]

end GlobalTheory.Lin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DirichletLZerosEqPrimitiveCharacterZerosStatement
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dirichletL_zeros_eq_primitiveCharacter_zeros : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 0 < s.re → (χ ≠ 1 ∨ s ≠ 1) → haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩; (LFunction χ s = 0 ↔ LFunction χ.primitiveCharacter s = 0) ∧ ord χ s = ord χ.primitiveCharacter s := by
  first | exact @GlobalTheory.Lin.zeros_eq_zeros_primitiveCharacter | exact GlobalTheory.Lin.zeros_eq_zeros_primitiveCharacter | (intros; apply GlobalTheory.Lin.zeros_eq_zeros_primitiveCharacter <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsProdAndSum
section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsProdAndSum
noncomputable section

namespace GlobalTheory.MomN

open GlobalTheory.MomOne

variable {q : ℕ} [Fact q.Prime]

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem momInt_mul (ι : ℂ ≃+* ℂ_[q]) {κ : Type} [Fintype κ] (v : κ → V) {F G : V → ℂ}
    (hF : ContDiff ℂ ⊤ F) (hG : ContDiff ℂ ⊤ G) (mF : MomInt ι v F) (mG : MomInt ι v G) :
    MomInt ι v (fun z => F z * G z) := by
  classical
  have cF := (GlobalTheory.T.mahlerCoefficient_norm_le_one_iff_jets_boundedMeasureMoments q ι V κ v F hF).1 mF
  have cG := (GlobalTheory.T.mahlerCoefficient_norm_le_one_iff_jets_boundedMeasureMoments q ι V κ v G hG).1 mG
  refine (GlobalTheory.T.mahlerCoefficient_norm_le_one_iff_jets_boundedMeasureMoments q ι V κ v _ (hF.mul hG)).2 fun n => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [GlobalTheory.T.mahlerJetCoefficient_mul V κ v F G hF hG n, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun k _ => ?_
  rw [map_mul, norm_mul]
  exact mul_le_one₀ (cF k) (norm_nonneg _) (cG _)

theorem momInt_add (ι : ℂ ≃+* ℂ_[q]) {κ : Type} [Fintype κ] (v : κ → V) {F G : V → ℂ}
    (hF : ContDiff ℂ ⊤ F) (hG : ContDiff ℂ ⊤ G) (mF : MomInt ι v F) (mG : MomInt ι v G) :
    MomInt ι v (fun z => F z + G z) := by
  obtain ⟨μ, hμ, eμ⟩ := mF
  obtain ⟨ν, hν, eν⟩ := mG
  refine ⟨μ + ν, ?_, fun k j f hf => ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    rw [one_mul, ContinuousLinearMap.add_apply]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · simpa using μ.le_of_opNorm_le hμ f
    · simpa using ν.le_of_opNorm_le hν f
  · have h : iteratedFDeriv ℂ k (fun z => F z + G z) 0 =
        iteratedFDeriv ℂ k F 0 + iteratedFDeriv ℂ k G 0 :=
      iteratedFDeriv_add_apply (hF.contDiffAt.of_le (by exact_mod_cast le_top))
        (hG.contDiffAt.of_le (by exact_mod_cast le_top))
    rw [h, ContinuousMultilinearMap.add_apply, map_add (f := _), eμ k j f hf, eν k j f hf,
      ContinuousLinearMap.add_apply]

theorem momInt_const_mul (ι : ℂ ≃+* ℂ_[q]) {κ : Type} [Fintype κ] (v : κ → V) {c : ℂ} {G : V → ℂ}
    (hG : ContDiff ℂ ⊤ G) (hc : ‖ι c‖ ≤ 1) (mG : MomInt ι v G) :
    MomInt ι v (fun z => c * G z) := by
  obtain ⟨μ, hμ, eμ⟩ := mG
  refine ⟨ι c • μ, ?_, fun k j f hf => ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    rw [one_mul, ContinuousLinearMap.smul_apply, norm_smul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hc).trans (μ.le_of_opNorm_le hμ f |>.trans (by simp))
  · have h : iteratedFDeriv ℂ k (fun z => c * G z) 0 = c • iteratedFDeriv ℂ k G 0 := by
      have := iteratedFDeriv_const_smul_apply (𝕜 := ℂ) (a := c) (f := G) (i := k) (x := (0 : V))
        (hG.contDiffAt.of_le (by exact_mod_cast le_top))
      simpa [Pi.smul_def, smul_eq_mul] using this
    rw [h, ContinuousMultilinearMap.smul_apply, smul_eq_mul, map_mul, eμ k j f hf,
      ContinuousLinearMap.smul_apply, smul_eq_mul]

theorem latInt_mul (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (Λ : AddSubgroup V) {F G : V → ℂ}
    (hF : ContDiff ℂ ⊤ F) (hG : ContDiff ℂ ⊤ G) (mF : LatInt ι ω Λ F) (mG : LatInt ι ω Λ G) :
    LatInt ι ω Λ (fun z => F z * G z) :=
  fun κ _ v hv => momInt_mul ι _ hF hG (mF κ v hv) (mG κ v hv)

theorem latInt_add (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (Λ : AddSubgroup V) {F G : V → ℂ}
    (hF : ContDiff ℂ ⊤ F) (hG : ContDiff ℂ ⊤ G) (mF : LatInt ι ω Λ F) (mG : LatInt ι ω Λ G) :
    LatInt ι ω Λ (fun z => F z + G z) :=
  fun κ _ v hv => momInt_add ι _ hF hG (mF κ v hv) (mG κ v hv)

theorem latInt_const_mul (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (Λ : AddSubgroup V) {c : ℂ} {G : V → ℂ}
    (hG : ContDiff ℂ ⊤ G) (hc : ‖ι c‖ ≤ 1) (mG : LatInt ι ω Λ G) :
    LatInt ι ω Λ (fun z => c * G z) :=
  fun κ _ v hv => momInt_const_mul ι _ hG hc (mG κ v hv)

theorem latInt_prod_sum : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (ω : ℂ_[q]) (Λ : AddSubgroup V),
    (∀ (m : Type) [Fintype m] (G : m → V → ℂ), (∀ j, ContDiff ℂ ⊤ (G j)) → (∀ j, LatInt ι ω Λ (G j)) →
      LatInt ι ω Λ fun z => ∏ j, G j z) ∧
    ∀ (m : Type) (s : Finset m) (c : m → ℂ) (G : m → V → ℂ), (∀ j ∈ s, ContDiff ℂ ⊤ (G j)) →
      (∀ j ∈ s, ‖ι (c j)‖ ≤ 1) → (∀ j ∈ s, LatInt ι ω Λ (G j)) →
      LatInt ι ω Λ fun z => ∑ j ∈ s, c j * G j z := by
  intro q _ ι V _ _ ω Λ
  classical
  refine ⟨fun m _ G hd hl => ?_, fun m s c G hd hc hl => ?_⟩
  · have key : ∀ s : Finset m, ContDiff ℂ ⊤ (fun z => ∏ j ∈ s, G j z) ∧
        LatInt ι ω Λ (fun z => ∏ j ∈ s, G j z) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using ⟨contDiff_const, latInt_one ι ω Λ⟩
      | insert a s ha ih =>
        simp only [Finset.prod_insert ha]
        exact ⟨(hd a).mul ih.1, latInt_mul ι ω Λ (hd a) ih.1 (hl a) ih.2⟩
    exact (key Finset.univ).2
  · have key : ∀ t : Finset m, t ⊆ s → ContDiff ℂ ⊤ (fun z => ∑ j ∈ t, c j * G j z) ∧
        LatInt ι ω Λ (fun z => ∑ j ∈ t, c j * G j z) := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
        intro _
        simpa using ⟨contDiff_const, latInt_zero ι ω Λ⟩
      | insert a t ha ih =>
        intro hts
        have hat : a ∈ s := hts (by simp)
        obtain ⟨h1, h2⟩ := ih fun x hx => hts (by simp [hx])
        simp only [Finset.sum_insert ha]
        have h3 : ContDiff ℂ ⊤ (fun z => c a * G a z) := contDiff_const.mul (hd a hat)
        exact ⟨h3.add h1, latInt_add ι ω Λ h3 h1
          (latInt_const_mul ι ω Λ (hd a hat) (hc a hat) (hl a hat)) h2⟩
    exact (key s subset_rfl).2

end GlobalTheory.MomN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticeJetsAreBoundedMomentsProdAndSumStatement
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeJetsAreBoundedMoments_prod_and_sum : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ω : ℂ_[q]) (Λ : AddSubgroup V), (∀ (m : Type) [Fintype m] (G : m → V → ℂ), (∀ j, ContDiff ℂ ⊤ (G j)) → (∀ j, LatInt ι ω Λ (G j)) → LatInt ι ω Λ fun z => ∏ j, G j z) ∧ ∀ (m : Type) (s : Finset m) (c : m → ℂ) (G : m → V → ℂ), (∀ j ∈ s, ContDiff ℂ ⊤ (G j)) → (∀ j ∈ s, ‖ι (c j)‖ ≤ 1) → (∀ j ∈ s, LatInt ι ω Λ (G j)) → LatInt ι ω Λ fun z => ∑ j ∈ s, c j * G j z := by
  first | exact @GlobalTheory.MomN.latInt_prod_sum | exact GlobalTheory.MomN.latInt_prod_sum | (intros; apply GlobalTheory.MomN.latInt_prod_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuadricPointGaugePolarCoordinatesCompareTangentG
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

namespace GlobalTheory.PolarCompare

theorem abs_sqrt_sub_one_le (x : ℝ) : |Real.sqrt (1 - x) - 1| ≤ |x| := by
  rcases le_or_gt (1 - x) 0 with h | h
  · rw [Real.sqrt_eq_zero_of_nonpos h]
    have : |(0:ℝ) - 1| = 1 := by norm_num
    rw [this]
    exact le_trans (by linarith) (le_abs_self x)
  · have h1 := Real.sq_sqrt h.le
    have h2 := Real.sqrt_nonneg (1 - x)
    set a := Real.sqrt (1 - x)
    have h3 : x = (1 - a) * (1 + a) := by linarith
    rw [h3, abs_mul, abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ 1 + a)]
    have := abs_nonneg (1 - a)
    nlinarith

theorem abs_qf_le {P Q : ℕ} (z : Sp P Q) : |qf z| ≤ (∑ i, ‖z i‖) ^ 2 := by
  rw [qf_eq_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans (le_of_eq ?_) (Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => norm_nonneg (z i)))
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [abs_mul, Complex.normSq_eq_norm_sq, abs_of_nonneg (sq_nonneg ‖z i‖)]
  rcases sg_eq i with h | h <;> simp [h]

theorem norm_exp_eq (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ = 2 * |Real.sin (θ / 2)| := by
  rw [mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one]
  simp

theorem abs_sin_eq (x : ℝ) (h : |x| ≤ Real.pi) : |Real.sin x| = Real.sin |x| := by
  rcases le_total 0 x with h0 | h0
  · rw [abs_of_nonneg h0] at h ⊢
    exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0 h)
  · rw [abs_of_nonpos h0] at h ⊢
    rw [← abs_neg, ← Real.sin_neg]
    exact abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) h)

theorem exp_bounds (θ : ℝ) (h : |θ| ≤ Real.pi) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ≤ |θ| ∧
    |θ| ≤ 2 * ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖ ∧
    (|θ| ≤ 2 → |θ| - |θ| ^ 3 / 16 ≤ ‖Complex.exp ((θ : ℂ) * Complex.I) - 1‖) := by
  have hp := Real.pi_pos
  have h0 := abs_nonneg θ
  have e1 : |θ / 2| = |θ| / 2 := by rw [abs_div]; norm_num
  rw [norm_exp_eq, abs_sin_eq _ (by rw [e1]; linarith), e1]
  set T := |θ|
  refine ⟨?_, ?_, fun h2 => ?_⟩
  · have := Real.sin_le (x := T / 2) (by linarith)
    linarith
  · have h1 := Real.mul_le_sin (x := T / 2) (by linarith) (by linarith)
    have h2 : (1 / 2 : ℝ) ≤ 2 / Real.pi := by
      rw [div_le_div_iff₀ (by norm_num) hp]
      have := Real.pi_le_four
      linarith
    nlinarith
  · rcases h0.eq_or_lt with h3 | h3
    · rw [← h3]; simp
    · have := Real.sin_gt_sub_cube (x := T / 2) (by linarith)
      nlinarith [pow_nonneg h0 3]

theorem polar_compare (P Q P' Q' : ℕ) (e : Option (Fin P' ⊕ Fin Q') ≃ (Fin P ⊕ Fin Q)) (t : ℝ)
    (ht : 1 < t) : ∀ᶠ r in 𝓝[>] (0 : ℝ), ∀ u : ℝ × Sp P' Q',
      u.1 ∈ Set.Ioo (-Real.pi) Real.pi →
      (tanGauge u < t⁻¹ * r → ptGauge e (polarPt e u) < r) ∧
      (ptGauge e (polarPt e u) < r → tanGauge u < t * r) := by
  have hti : t⁻¹ < 1 := inv_lt_one_of_one_lt₀ ht
  have hti0 : 0 < t⁻¹ := inv_pos.2 (by linarith)
  have hd : (0 : ℝ) < min (1 / 2) (min ((t - 1) / 3) (1 - t⁻¹)) := by
    refine lt_min (by norm_num) (lt_min ?_ ?_) <;> linarith
  filter_upwards [Ioo_mem_nhdsGT hd] with r hr u hu
  obtain ⟨hr0, hr1⟩ := hr
  rw [lt_min_iff, lt_min_iff] at hr1
  obtain ⟨hr1, hr2, hr3⟩ := hr1
  obtain ⟨b1, b2, b3⟩ := exp_bounds u.1 (abs_le.2 ⟨hu.1.le, hu.2.le⟩)
  have hq := abs_qf_le u.2
  have ha : |Real.sqrt (1 - sg (e none) * qf u.2) - 1| ≤ (∑ i, ‖u.2 i‖) ^ 2 := by
    refine (abs_sqrt_sub_one_le _).trans (le_trans (le_of_eq ?_) hq)
    rw [abs_mul]
    rcases sg_eq (e none) with h | h <;> simp [h]
  have hN : |‖polarPt e u (e none) - 1‖ - ‖Complex.exp ((u.1 : ℂ) * Complex.I) - 1‖|
      ≤ (∑ i, ‖u.2 i‖) ^ 2 := by
    refine (abs_norm_sub_norm_le _ _).trans (le_trans (le_of_eq ?_) ha)
    rw [polarPt_none]
    set a := Real.sqrt (1 - sg (e none) * qf u.2)
    have : (a : ℂ) * Complex.exp ((u.1 : ℂ) * Complex.I) - 1 -
        (Complex.exp ((u.1 : ℂ) * Complex.I) - 1) =
        ((a - 1 : ℝ) : ℂ) * Complex.exp ((u.1 : ℂ) * Complex.I) := by
      push_cast; ring
    rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs]
  have hS : 0 ≤ ∑ i, ‖u.2 i‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hN0 := norm_nonneg (polarPt e u (e none) - 1)
  have hT := abs_nonneg u.1
  unfold tanGauge ptGauge
  simp only [polarPt_some]
  obtain ⟨n1, n2⟩ := abs_le.1 hN
  generalize ‖polarPt e u (e none) - 1‖ = N at *
  generalize ‖Complex.exp ((u.1 : ℂ) * Complex.I) - 1‖ = E at *
  generalize ∑ i, ‖u.2 i‖ = S at *
  generalize |u.1| = T at *
  constructor
  · intro h
    have h1 : t⁻¹ * r < r := by nlinarith
    have h2 : S ≤ r := by linarith
    have h3 : S ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hS h2 2
    nlinarith
  · intro h
    have h2 : S ≤ r := by linarith
    have h3 : S ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ hS h2 2
    have h4 : r ^ 2 ≤ r := by nlinarith
    have h5 : T ≤ 4 * r := by linarith
    have h6 := b3 (by linarith)
    have h7 : T ^ 3 ≤ (4 * r) ^ 3 := pow_le_pow_left₀ hT h5 3
    have h8 : r ^ 3 ≤ r ^ 2 / 2 := by nlinarith [sq_nonneg r]
    have h9 : 3 * r ^ 2 ≤ (t - 1) * r := by nlinarith
    nlinarith

end GlobalTheory.PolarCompare
end
