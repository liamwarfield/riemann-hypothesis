module

public import Development.AutomorphicArithmetic.WhittakerHecke.InertOrSplitOfGoodDeltaRat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Places
public import Development.AutomorphicArithmetic.WhittakerHecke.ExistsWhittakerHeckeEigenvaluesAtSplitPlace

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.HeightOneSpectrumRatCorrespondPrimes
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem cast_dvd {a b : ℕ} : (a : 𝓞 ℚ) ∣ (b : 𝓞 ℚ) ↔ a ∣ b := by
  refine ⟨fun h => ?_, fun h => Nat.cast_dvd_cast h⟩
  have h1 := map_dvd Rat.ringOfIntegersEquiv h
  rw [map_natCast, map_natCast] at h1
  exact Int.natCast_dvd_natCast.1 h1

private theorem mem_iff_dvd (N : ℕ) (v : HeightOneSpectrum (𝓞 ℚ)) :
    (N : 𝓞 ℚ) ∈ v.asIdeal ↔ normV v ∣ N := by
  rw [← cast_dvd, ← Ideal.mem_span_singleton, ← (UpperTheory.V.Af.Nf.places v).2.1]

theorem UpperTheory.heightOneSpectrum_rat_correspond_primes :
    (∀ v : H.P ℚ, (normV v).Prime) ∧ (∀ p : ℕ, p.Prime → ∃ v : H.P ℚ, normV v = p) ∧ (∀ v v' : H.P ℚ, normV v = normV v' → v = v') ∧
          (∀ (N : ℕ) (v : H.P ℚ), Bad N v ↔ normV v ∣ N) := by
  refine ⟨fun v => (UpperTheory.V.Af.Nf.places v).1, fun p hp => ?_, fun v v' h => ?_, fun N v => mem_iff_dvd N v⟩
  · have hnt : Ideal.span {(p : 𝓞 ℚ)} ≠ ⊤ := by
      rw [Ne, Ideal.span_singleton_eq_top, isUnit_iff_dvd_one, ← Nat.cast_one, cast_dvd, Nat.dvd_one]
      exact hp.ne_one
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hnt
    have hpM : (p : 𝓞 ℚ) ∈ M := hle (Ideal.mem_span_singleton_self _)
    have hM0 : M ≠ ⊥ := by
      rintro rfl
      exact hp.ne_zero (Nat.cast_eq_zero.1 (Ideal.mem_bot.1 hpM))
    let w : HeightOneSpectrum (𝓞 ℚ) := ⟨M, hM.isPrime, hM0⟩
    exact ⟨w, (Nat.prime_dvd_prime_iff_eq (UpperTheory.V.Af.Nf.places w).1 hp).1 ((mem_iff_dvd p w).1 hpM)⟩
  · apply HeightOneSpectrum.ext
    rw [(UpperTheory.V.Af.Nf.places v).2.1, (UpperTheory.V.Af.Nf.places v').2.1, h]
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.IdeleOfNatMulAndPrimePow
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.ideleOfNat_mul_and_prime_pow :
    (∀ m n : ℕ, 0 < m → 0 < n → pin (m * n) = pin m * pin n) ∧ (∀ (v : H.P ℚ) (k : ℕ), pin (normV v ^ k) = UpperTheory.ConvolutionTheory.RankTwoDescent.pv v ^ k) := by
  obtain ⟨hp, -, hinj, -⟩ := UpperTheory.heightOneSpectrum_rat_correspond_primes
  have hfin : ∀ n : ℕ, (Function.mulSupport fun v : H.P ℚ => UpperTheory.ConvolutionTheory.RankTwoDescent.pv v ^ (n.factorization (normV v))).Finite := by
    intro n
    have h1 : ((fun v : H.P ℚ => normV v) ⁻¹' (n.factorization.support : Set ℕ)).Finite :=
      Set.Finite.preimage (fun a _ b _ h => hinj a b h) (Finset.finite_toSet _)
    refine h1.subset fun v hv => ?_
    simp only [Set.mem_preimage, Finset.mem_coe, Finsupp.mem_support_iff]
    intro h0
    exact hv (by simp only [h0, pow_zero])
  refine ⟨fun m n hm hn => ?_, fun v k => ?_⟩
  · unfold pin
    rw [← finprod_mul_distrib (hfin m) (hfin n), Nat.factorization_mul hm.ne' hn.ne']
    exact finprod_congr fun v => by rw [Finsupp.add_apply, pow_add]
  · unfold pin
    rw [(hp v).factorization_pow, finprod_eq_single _ v]
    · rw [Finsupp.single_eq_same]
    · intro w hw
      rw [Finsupp.single_eq_of_ne (fun h => hw (hinj _ _ h)), pow_zero]
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.ExistsMultiplicativeOfPrimePowerValues
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.exists_multiplicative_of_prime_power_values :
    ∀ M : H.P ℚ → ℕ → ℂ, (∀ v, M v 0 = 1) → ∃ μ : ℕ → ℂ, μ 1 = 1 ∧
          (∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → μ (m * n) = μ m * μ n) ∧
          ∀ (v : H.P ℚ) (k : ℕ), μ (normV v ^ k) = M v k := by
  intro M hM
  obtain ⟨hp, -, hinj, -⟩ := UpperTheory.heightOneSpectrum_rat_correspond_primes
  let f : ℕ → ℕ → ℂ := fun p k =>
    if h : ∃ v : H.P ℚ, normV v = p then M h.choose k else 1
  have hf : ∀ (v : H.P ℚ) (k : ℕ), f (normV v) k = M v k := by
    intro v k
    have h : ∃ w : H.P ℚ, normV w = normV v := ⟨v, rfl⟩
    have h2 : h.choose = v := hinj _ _ h.choose_spec
    simp only [f]
    rw [dite_eq_left h, h2]
  refine ⟨fun n => n.factorization.prod f, by simp, ?_, ?_⟩
  · intro m n hm hn hmn
    show (m * n).factorization.prod f = m.factorization.prod f * n.factorization.prod f
    rw [Nat.factorization_mul hm.ne' hn.ne']
    exact Finsupp.prod_add_index_of_disjoint
      (by simpa using hmn.disjoint_primeFactors) f
  · intro v k
    show (normV v ^ k).factorization.prod f = M v k
    rw [(hp v).factorization_pow, Finsupp.prod_single_index (by rw [hf, hM]), hf]
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.ExistsWhittakerHeckeEigenvaluesAtInertPlace
section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.PowerSeriesCompleteHomogeneousTwoMulEqOne
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem UpperTheory.geometric_power_series_inverse (x : ℂ) :
    (PowerSeries.mk fun k : ℕ => x ^ k) * (1 - PowerSeries.C x * PowerSeries.X) = 1 := by
  ext n
  rw [mul_sub, mul_one, ← mul_assoc, map_sub]
  cases n with
  | zero => simp
  | succ n =>
    rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mul_C]
    simp [PowerSeries.coeff_one, pow_succ]

theorem UpperTheory.powerSeries_completeHomogeneous_two_mul_eq_one :
    ∀ x y : ℂ, (PowerSeries.mk fun k : ℕ => (∑ i ∈ Finset.range (k + 1), (x) ^ i * (y) ^ (k - i))) * ((1 - PowerSeries.C x * PowerSeries.X) * (1 - PowerSeries.C y * PowerSeries.X)) = 1 := by
  intro x y
  have h : (PowerSeries.mk fun k : ℕ => (∑ i ∈ Finset.range (k + 1), (x) ^ i * (y) ^ (k - i)))
      = (PowerSeries.mk fun k : ℕ => x ^ k) * (PowerSeries.mk fun k : ℕ => y ^ k) := by
    ext n
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simp
  rw [h, mul_mul_mul_comm, UpperTheory.geometric_power_series_inverse, UpperTheory.geometric_power_series_inverse, mul_one]
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.ExistsGoodCharacterOfInertCMDatum
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

theorem UpperTheory.exists_good_character_of_inert_CMDatum :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (v : H.P ℚ) (w : H.P E), H.Gd D.δ v → H.Inert D v w →
          ∃ χ : H.Kv w → ℂ, H.Good χ ∧ ∀ x, ∃ u t, H.sg w x = D.mkE u t ∧ ψ (-t) = χ x := by
  intro E _ _ D v w hG hI
  obtain ⟨e, h1, h2, h3, -⟩ := hI.coord
  obtain ⟨sa, sm, sc, -⟩ := H.sgLaws ℚ v
  obtain ⟨-, tm, tc, -⟩ := H.sgLaws E w
  obtain ⟨ga, gi, gm⟩ := hG.psi
  have hs : ∀ u, -(H.sg v u) = H.sg v (-u) := fun u => by
    rw [← neg_one_mul, sm, map_neg, map_one, neg_one_mul]
  have s0 : H.sg v (0 : H.Kv v) = 0 := by simpa using (sm 0 0).symm
  have h4 : ∀ c u t, e (0, c) * e (u, t) = e (H.cp v (rt D.δ) * (c * t), c * u) := fun c u t => by
    have a1 : ∀ x y, H.sg v (x * y) = H.sg v x * H.sg v y := fun x y => by rw [sm, sc]
    have a2 : ∀ x, H.sg v (H.cp v (rt D.δ) * x) = rt D.δ * H.sg v x := fun x => (sm (rt D.δ) x).symm
    have a3 : (rt D.θ : A E) ^ 2 = AdeleBaseChange.adeleMap ℚ E (rt D.δ) := by
      rw [← map_pow, D.sq]
      exact (AdeleBaseChange.adeleMap_algebraMap _).symm
    have : H.sg w (e (0, c) * e (u, t)) = H.sg w (e (H.cp v (rt D.δ) * (c * t), c * u)) := by
      rw [← tc (e (0, c)), ← tm, h1, h1, h1, s0, a2, a1, a1]
      simp only [Dat.mkE, map_mul, map_zero, ← a3]
      ring
    simpa only [tc] using congrArg (H.cp w) this
  have key : ∀ y : H.Kv v, (∀ c, H.IsInt c → ψ (H.sg v (-(c * y))) = 1) → H.IsInt y := fun y hy => by
    have : Valued.v (-y) ≤ 1 := gm _ fun c hc => by
      have := hy c hc
      rwa [show -(c * y) = c * -y by ring] at this
    rwa [Valuation.map_neg] at this
  refine ⟨fun x => ψ (H.sg v (-(e.symm x).2)), ⟨fun x y => ?_, fun x hx => ?_, fun x hx => ?_⟩, fun x => ?_⟩
  · beta_reduce
    rw [map_add (f := _), Prod.snd_add, neg_add]
    exact ga _ _
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    have ht : Valued.v t ≤ 1 := (le_max_right _ _).trans ((h2 u t).symm.le.trans hx)
    beta_reduce
    rw [e.symm_apply_apply]
    refine gi _ ?_
    show Valued.v _ ≤ 1
    rwa [Valuation.map_neg]
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    have ht : H.IsInt t := key t fun c hc => by
      have := hx (e (c, 0)) ((h2 c 0).le.trans (max_le hc (by simp)))
      beta_reduce at this
      rwa [h3, e.symm_apply_apply] at this
    have hu : H.IsInt u := key u fun c hc => by
      have := hx (e (0, c)) ((h2 0 c).le.trans (max_le (by simp) hc))
      beta_reduce at this
      rwa [h4, e.symm_apply_apply] at this
    exact (h2 u t).le.trans (max_le hu ht)
  · obtain ⟨⟨u, t⟩, rfl⟩ := e.surjective x
    exact ⟨_, _, h1 u t, by beta_reduce; rw [hs, e.symm_apply_apply]⟩
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem em_aE {E : Type} [Field E] [NumberField E] (y : (A ℚ)ˣ) (z : (A E)ˣ)
    (h : (z : A E) = AdeleBaseChange.adeleMap ℚ E (y : A ℚ)) : em E (aE y) = aE z := by
  apply Units.ext
  ext i j
  rw [UpperTheory.ConvolutionTheory.RankTwoDescent.em, Matrix.GeneralLinearGroup.map_apply]
  fin_cases i <;> fin_cases j <;> simp [aE, h]

theorem UpperTheory.exists_whittaker_heckeEigenvalues_at_inert_place :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2) (ω χ : HChar ℚ),
          CenN P ω → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → ∀ (L N : ℕ) φ, admitted D ω φ → Gd D P L N φ → ∀ a, IsAs P χ N a → ∀ v : H.P ℚ, ¬ Bad N v → ∀ w : H.P E, w.under (𝓞 ℚ) = v → H.Inert D v w →
          ∃ m : ℕ → ℂ, m 0 = 1 ∧
            (∀ (k : ℕ) g, (∀ w : H.P E, w.under (𝓞 ℚ) = v → H.KAt w g) → Wo D φ (em E (aE (UpperTheory.ConvolutionTheory.RankTwoDescent.pv v ^ k)) * g) = m k * Wo D φ g) ∧
            ((∃ h, Wo D φ h ≠ 0) → (PowerSeries.mk fun k => a (normV v ^ k)) * (1 - PowerSeries.X ^ 2) =
              PowerSeries.mk fun k => ((normV v ^ k : ℕ) : ℂ) * ((χ.val v : ℂˣ) : ℂ) ^ k * m k) := by
  intro E _ _ _ D P ω χ _ _ L N φ hA hG a hIs v hv w hw hI
  obtain ⟨-, B, hsat, hEig⟩ := hG.fix w (by rw [hw]; exact hv)
  obtain ⟨α, β, rfl⟩ := Multiset.card_eq_two.1 (GlobalTheory.LFun.HasSatGL.card ((CG.hasSat_mk P w B).1 hsat))
  obtain ⟨-, -, hleft, -⟩ := UpperTheory.whittakerFunction_continuous_bounded_equivariant E D ω φ hA
  have hEw := UpperTheory.eigAt_cmDatumOperator_of_eigAt E D φ w _ hA.cont hEig
  obtain ⟨χw, hχ, hχe⟩ := UpperTheory.exists_good_character_of_inert_CMDatum E D v w (hG.pl v hv) hI
  have hnl : ∀ b h, Wo D φ (H.lc w (H.nL b) * h) = χw b * Wo D φ h := fun b h => by
    obtain ⟨u, t, e1, e2⟩ := hχe b
    rw [(H.lcLaws E w).1, e1, ← e2]
    exact hleft ![u, t] h
  obtain ⟨ϖ', hϖ', hz, -⟩ := hI.unif (atFin v (unif v)) (unif_spec v)
  have hem : ∀ k : ℕ, em E (aE (UpperTheory.ConvolutionTheory.RankTwoDescent.pv v ^ k)) = aE (H.idl w ϖ' ^ k) := fun k => by
    refine em_aE _ _ ?_
    rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow, hz, Dat.mkE, map_zero, zero_mul, add_zero]
    rfl
  have hnv : 1 < normV v := by
    have := GlobalTheory.LFun.one_lt_absNorm v
    simpa [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply] using this
  have hqw : H.q w = (normV v : ℂ) ^ 2 := by
    have : H.q w = (normV w : ℂ) := by simp [H.q, normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [this, hI.norm]
    push_cast
    rfl
  have hqv : (normV v : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hsq : H.q w ^ (1 / 2 : ℂ) = (normV v : ℂ) := by
    rw [hqw]
    have e : ((normV v : ℂ) ^ 2) = ((((normV v : ℝ) ^ 2 : ℝ)) : ℂ) := by push_cast; rfl
    rw [e, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow (by positivity),
      ← Real.sqrt_eq_rpow, Real.sqrt_sq (by positivity)]
    simp
  refine ⟨fun k => ((normV v : ℂ) ^ k)⁻¹ * ∑ i ∈ Finset.range (k + 1), (α : ℂ) ^ i * (β : ℂ) ^ (k - i), by simp,
    fun k g hg => ?_, fun _ => ?_⟩
  · have h := UpperTheory.eigenform_shintani_formula_at_place E w ϖ' hϖ' χw hχ α β _ hEw hnl g (hg w hw) k
    rw [hsq] at h
    rw [hem, mul_assoc, ← h, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero k hqv), one_mul]
  · have h1 := hIs.inert v hv w hw hI.norm α β hsat
    have h2 := UpperTheory.powerSeries_completeHomogeneous_two_mul_eq_one ((α * χ.val v : ℂˣ) : ℂ) ((β * χ.val v : ℂˣ) : ℂ)
    have h3 : (PowerSeries.mk fun k => ((normV v ^ k : ℕ) : ℂ) * ((χ.val v : ℂˣ) : ℂ) ^ k *
        (((normV v : ℂ) ^ k)⁻¹ * ∑ i ∈ Finset.range (k + 1), (α : ℂ) ^ i * (β : ℂ) ^ (k - i))) =
        PowerSeries.mk fun k : ℕ => ∑ i ∈ Finset.range (k + 1),
          ((α * χ.val v : ℂˣ) : ℂ) ^ i * ((β * χ.val v : ℂˣ) : ℂ) ^ (k - i) := by
      congr 1
      funext k
      rw [Nat.cast_pow, mul_comm ((normV v : ℂ) ^ k), mul_assoc, ← mul_assoc ((normV v : ℂ) ^ k),
        mul_inv_cancel₀ (pow_ne_zero k hqv), one_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
      rw [Nat.add_sub_cancel_left, Units.val_mul, Units.val_mul]
      ring
    rw [h3]
    linear_combination (PowerSeries.mk fun k : ℕ => ∑ i ∈ Finset.range (k + 1),
          ((α * χ.val v : ℂˣ) : ℂ) ^ i * ((β * χ.val v : ℂˣ) : ℂ) ^ (k - i)) * h1 -
      (PowerSeries.mk fun k => a (normV v ^ k)) * (1 - PowerSeries.X ^ 2) * h2
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.EqConvolutionSquareIndicatorOfEulerFactors
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem sqN_eq (N n : ℕ) : sqN N n = if IsSquare n ∧ n.Coprime N then 1 else 0 := by
  unfold sqN
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨m, rfl, hm⟩
    exact ⟨⟨m, rfl⟩, Nat.Coprime.mul_left hm hm⟩
  · rintro ⟨⟨m, rfl⟩, hm⟩
    exact ⟨m, rfl, Nat.Coprime.coprime_mul_right hm⟩

private theorem isSquare_left {m n : ℕ} (h : m.Coprime n) (hs : IsSquare (m * n)) : IsSquare m := by
  obtain ⟨c, hc⟩ := hs
  have hu : IsUnit (gcd m n) := by
    rw [gcd_eq_nat_gcd, h.gcd_eq_one]; exact isUnit_one
  obtain ⟨d, hd⟩ := exists_eq_pow_of_mul_eq_pow (c := c) (k := 2) hu (by rw [hc, sq])
  exact ⟨d, by rw [hd, sq]⟩

private theorem sqN_mul (N : ℕ) {m n : ℕ} (h : m.Coprime n) :
    sqN N (m * n) = sqN N m * sqN N n := by
  have e : (IsSquare (m * n) ∧ (m * n).Coprime N) ↔
      ((IsSquare m ∧ m.Coprime N) ∧ (IsSquare n ∧ n.Coprime N)) := by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨isSquare_left h h1, Nat.Coprime.coprime_mul_right h2⟩,
        ⟨isSquare_left h.symm (by rwa [mul_comm]), Nat.Coprime.coprime_mul_left h2⟩⟩
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      exact ⟨h1.mul h3, Nat.Coprime.mul_left h2 h4⟩
  rw [sqN_eq, sqN_eq, sqN_eq]
  by_cases h1 : IsSquare m ∧ m.Coprime N
  · by_cases h2 : IsSquare n ∧ n.Coprime N
    · rw [if_pos h1, if_pos h2, if_pos (e.2 ⟨h1, h2⟩), mul_one]
    · rw [if_neg h2, if_neg (fun x => h2 (e.1 x).2), mul_zero]
  · rw [if_neg h1, if_neg (fun x => h1 (e.1 x).1), zero_mul]

private theorem sqN_one (N : ℕ) : sqN N 1 = 1 := by
  rw [sqN_eq, if_pos ⟨⟨1, rfl⟩, Nat.coprime_one_left N⟩]

private theorem isSquare_pow_iff {p : ℕ} (hp : p.Prime) (j : ℕ) : IsSquare (p ^ j) ↔ Even j := by
  constructor
  · rintro ⟨m, hm⟩
    have hd : m ∣ p ^ j := ⟨m, hm⟩
    obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd
    rw [← pow_add] at hm
    exact ⟨i, Nat.pow_right_injective hp.two_le hm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨p ^ i, pow_add p i i⟩

private theorem conv_pow (f g : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    LSeries.convolution f g (p ^ k) =
      PowerSeries.coeff k ((PowerSeries.mk fun i => f (p ^ i)) * PowerSeries.mk fun i => g (p ^ i)) := by
  rw [LSeries.convolution_def, PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_mk]
  rw [Nat.sum_divisorsAntidiagonal (fun x y => f x * g y), Nat.sum_divisors_prime_pow hp,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => f (p ^ i) * g (p ^ j))]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Nat.pow_div (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hp.pos]

private theorem sq_series (N : ℕ) {p : ℕ} (hp : p.Prime) (h : ¬ p ∣ N) :
    (1 - PowerSeries.X ^ 2) * (PowerSeries.mk fun i => sqN N (p ^ i)) = (1 : PowerSeries ℂ) := by
  have hc : p.Coprime N := (Nat.Prime.coprime_iff_not_dvd hp).2 h
  have hs : ∀ j, sqN N (p ^ j) = if Even j then 1 else 0 := by
    intro j
    rw [sqN_eq]
    refine if_congr ?_ rfl rfl
    rw [isSquare_pow_iff hp]
    exact ⟨fun x => x.1, fun x => ⟨x, Nat.Coprime.pow_left j hc⟩⟩
  ext k
  rw [sub_mul, one_mul, map_sub, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_one]
  simp only [PowerSeries.coeff_mk, hs]
  rcases k with _ | _ | k
  · simp
  · simp
  · have e : Even (k + 1 + 1) ↔ Even k := by
      rw [Nat.even_add_one, Nat.even_add_one, not_not]
    have e2 : k + 1 + 1 - 2 = k := by omega
    rw [if_pos (show 2 ≤ k + 1 + 1 by omega), e2, if_neg (show ¬ (k + 1 + 1 = 0) by omega)]
    simp only [e, sub_self]

private theorem isMul_of (f : ℕ → ℂ) (h1 : f 1 = 1)
    (h : ∀ m n, 0 < m → 0 < n → m.Coprime n → f (m * n) = f m * f n) :
    (toArithmeticFunction f).IsMultiplicative := by
  have key : ∀ n, toArithmeticFunction f n = if n = 0 then 0 else f n := fun _ => rfl
  refine ⟨by rw [key, if_neg one_ne_zero, h1], ?_⟩
  intro m n hmn
  rw [key, key, key]
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  rw [if_neg hm, if_neg hn, if_neg (mul_ne_zero hm hn),
    h m n (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn) hmn]

theorem UpperTheory.eq_convolution_squareIndicator_of_euler_factors :
    ∀ (N : ℕ) (a b : ℕ → ℂ), 0 < N → a 1 = 1 → (∀ m n, m.Coprime n → a (m * n) = a m * a n) →
          (∀ p k : ℕ, p.Prime → p ∣ N → a (p ^ (k + 1)) = 0) → b 1 = 1 →
          (∀ m n, 0 < m → 0 < n → m.Coprime n → b (m * n) = b m * b n) → (∀ n, ¬ n.Coprime N → b n = 0) →
          (∀ p : ℕ, p.Prime → ¬ p ∣ N → (PowerSeries.mk fun k => a (p ^ k)) * (1 - PowerSeries.X ^ 2) = PowerSeries.mk fun k => b (p ^ k)) →
          ∀ n, n ≠ 0 → a n = LSeries.convolution b (sqN N) n := by
  intro N a b _ ha1 ham hap hb1 hbm hb0 hps n hn
  have hA := isMul_of a ha1 (fun m n _ _ h => ham m n h)
  have hB := isMul_of b hb1 hbm
  have hS := isMul_of (sqN N) (sqN_one N) (fun m n _ _ h => sqN_mul N h)
  have hE : toArithmeticFunction a = toArithmeticFunction b * toArithmeticFunction (sqN N) := by
    rw [ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hA _ (hB.mul hS)]
    intro p i hp
    have e1 : toArithmeticFunction a (p ^ i) = a (p ^ i) := if_neg (pow_ne_zero i hp.ne_zero)
    rw [e1]
    change a (p ^ i) = LSeries.convolution b (sqN N) (p ^ i)
    rw [conv_pow _ _ hp]
    by_cases hd : p ∣ N
    · have hnc : ∀ j, ¬ (p ^ (j + 1)).Coprime N := fun j hc =>
        (Nat.Prime.coprime_iff_not_dvd hp).1
          (Nat.Coprime.coprime_dvd_left (dvd_pow_self p (Nat.succ_ne_zero j)) hc) hd
      have eb : (PowerSeries.mk fun i => b (p ^ i)) = 1 := by
        ext j
        rcases j with _ | j
        · simp [hb1]
        · rw [PowerSeries.coeff_mk, hb0 _ (hnc j), PowerSeries.coeff_one,
            if_neg (Nat.succ_ne_zero j)]
      rw [eb, one_mul, PowerSeries.coeff_mk]
      rcases i with _ | i
      · rw [pow_zero, ha1, sqN_one]
      · rw [hap p i hp hd, sqN_eq, if_neg (fun x => hnc i x.2)]
    · rw [← hps p hp hd, mul_assoc, sq_series N hp hd, mul_one, PowerSeries.coeff_mk]
  have e1 : toArithmeticFunction a n = a n := if_neg hn
  rw [← e1, hE]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.WhittakerHecke.KAtDiagIdeleOfNatMulRotationOfNotDvd
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem cp_iy (v : H.P ℚ) (r : ℝ) : H.cp v ((iy r : (A ℚ)ˣ) : A ℚ) = 1 := by
  unfold iy
  split_ifs
  · simp
  · change pLoc ℚ v ((1 : Af ℚ) - 0 + 0) = 1
    rw [sub_zero, add_zero, map_one]

private theorem cp_pin (v : H.P ℚ) (n : ℕ) (h : ¬ normV v ∣ n) :
    H.cp v ((pin n : (A ℚ)ˣ) : A ℚ) = 1 := by
  unfold pin
  refine finprod_induction (fun x : (A ℚ)ˣ => H.cp v (x : A ℚ) = 1) (by simp) ?_ ?_
  · intro x y hx hy
    rw [Units.val_mul, map_mul, hx, hy, one_mul]
  · intro v'
    by_cases hv : v = v'
    · subst hv
      rw [Nat.factorization_eq_zero_of_not_dvd h]
      simp
    · have : H.cp v ((pv v' : (A ℚ)ˣ) : A ℚ) = 1 := by
        classical
        exact Pi.mulSingle_eq_of_ne hv _
      rw [Units.val_pow_eq_pow_val, map_pow, this, one_pow]

private theorem cp_rot (v : H.P ℚ) (t : ℝ) :
    Matrix.GeneralLinearGroup.map (H.cp v) (rot t) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  have h := congrArg (fun y : GL (Fin 2) (Af ℚ) => pLoc ℚ v (y.val i j)) (TR.pFin_infGL (E := ℚ) (a := 2) _ :
    Matrix.GeneralLinearGroup.map (pFin ℚ) (rot t) = 1)
  refine h.trans ?_
  simp only [Units.val_one, Matrix.one_apply]
  split_ifs <;> simp

private theorem cp_aE (v : H.P ℚ) (a : (A ℚ)ˣ) (h : H.cp v (a : A ℚ) = 1) :
    Matrix.GeneralLinearGroup.map (H.cp v) (aE a) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  change H.cp v ((aE a).val i j) = _
  fin_cases i <;> fin_cases j <;> simp [aE, h]

theorem UpperTheory.kAt_diag_ideleOfNat_mul_rotation_of_not_dvd :
    ∀ (E : Type) [Field E] [NumberField E] (v : H.P ℚ) (n : ℕ) (r t : ℝ), 0 < n → ¬ normV v ∣ n → ∀ w : H.P E, w.under (𝓞 ℚ) = v →
          H.KAt w (em E (aE (iy r * pin n) * rot t)) := by
  intro E _ _ v n r t _ h w hw
  have hx : Matrix.GeneralLinearGroup.map (H.cp v) (aE (iy r * pin n) * rot t) = 1 := by
    rw [map_mul, cp_rot, cp_aE v _ (by rw [Units.val_mul, map_mul, cp_iy, cp_pin v n h, one_mul]), one_mul]
  generalize aE (iy r * pin n) * rot t = x at hx
  subst hw
  have : Matrix.GeneralLinearGroup.map (H.cp w) (em E x) = 1 := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    have e : H.cp (w.under (𝓞 ℚ)) (x.val i j) = (1 : Matrix (Fin 2) (Fin 2) _) i j :=
      congrArg (fun y : GL (Fin 2) _ => y.val i j) hx
    change GroundTheory.Global.SemiLocal.completionMap (GroundTheory.Global.AdeleBaseChange.below ℚ w) w (H.cp (w.under (𝓞 ℚ)) (x.val i j)) = (1 : Matrix (Fin 2) (Fin 2) _) i j
    rw [e, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact map_one (GroundTheory.Global.SemiLocal.completionMap (GroundTheory.Global.AdeleBaseChange.below ℚ w) w)
    · exact map_zero (GroundTheory.Global.SemiLocal.completionMap (GroundTheory.Global.AdeleBaseChange.below ℚ w) w)
  unfold H.KAt
  rw [this]
  exact one_mem _
end

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem aE_mul' {K : Type} [Field K] [NumberField K] (x y : (A K)ˣ) : aE (x * y) = aE x * aE y := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aE, Matrix.mul_apply, Fin.sum_univ_two]

theorem UpperTheory.exists_whittaker_hecke_eigenvalues_and_coeff_eq_convolution :
    ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (D : Dat ℚ E) (P : CuspSub E 2) (ω χ : HChar ℚ),
        CenN P ω → Unit1 ω → (∀ a, (χ.1 a * ω.1 a) ^ 2 = 1) → ∀ (L N : ℕ), ChOk χ L → ∀ φ, admitted D ω φ → Gd D P L N φ → ∀ a, IsAs P χ N a → ∃ μ : ℕ → ℂ,
        (∀ n, 0 < n → n.Coprime N → ∀ r t : ℝ, r ≠ 0 →
          Wo D φ (em E (aE (iy r * pin n) * rot t)) = μ n * Wo D φ (em E (aE (iy r) * rot t))) ∧
        ((∃ r t : ℝ, r ≠ 0 ∧ Wo D φ (em E (aE (iy r) * rot t)) ≠ 0) → ∀ n, n ≠ 0 → a n = LSeries.convolution (bN N χ μ) (sqN N) n) := by
  intro E _ _ _ D P ω χ hCen hU hχω L N hχ φ hA hG a hIs
  obtain ⟨hpr, hex, hinj, hbad⟩ := UpperTheory.heightOneSpectrum_rat_correspond_primes
  obtain ⟨pmul, ppow⟩ := UpperTheory.ideleOfNat_mul_and_prime_pow
  have pin1 : pin 1 = 1 := by
    have := pmul 1 1 one_pos one_pos
    rw [one_mul] at this
    exact mul_eq_left.1 this.symm
  have pack : ∀ v : H.P ℚ, ¬ Bad N v → ∃ m : ℕ → ℂ, m 0 = 1 ∧ (∀ (k : ℕ) g, (∀ w : H.P E, w.under (𝓞 ℚ) = v → H.KAt w g) → Wo D φ (em E (aE (UpperTheory.ConvolutionTheory.RankTwoDescent.pv v ^ k)) * g) = m k * Wo D φ g) ∧ ((∃ h, Wo D φ h ≠ 0) → (PowerSeries.mk fun k => a (normV v ^ k)) * (1 - PowerSeries.X ^ 2) = PowerSeries.mk fun k => ((normV v ^ k : ℕ) : ℂ) * ((χ.val v : ℂˣ) : ℂ) ^ k * m k) := fun v hv => by
    rcases UpperTheory.inert_or_split_of_good_delta_rat E D v (hG.pl v hv) with ⟨w, hw, hI⟩ | ⟨w, w', hne, hw, hw', hs, hs', hall⟩
    · exact UpperTheory.exists_whittaker_heckeEigenvalues_at_inert_place E D P ω χ hCen hχω L N φ hA hG a hIs v hv w hw hI
    · exact UpperTheory.exists_whittaker_heckeEigenvalues_at_split_place E D P ω χ hCen hχω L N φ hA hG a hIs v hv w w' hne hw hw' hs hs' hall
  choose! M hM0 hM1 hM2 using pack
  obtain ⟨μ, hμ1, hμm, hμp⟩ := UpperTheory.exists_multiplicative_of_prime_power_values (fun v k => if Bad N v then 1 else M v k) (fun v => by
    by_cases h : Bad N v
    · simp [h]
    · simp [h, hM0 v h])
  have hpN : ∀ v : H.P ℚ, ¬ normV v ∣ N → ¬ Bad N v := fun v h hb => h ((hbad N v).1 hb)
  have hμv : ∀ (v : H.P ℚ) (k : ℕ), ¬ Bad N v → μ (normV v ^ k) = M v k := fun v k h => by
    have := hμp v k
    simpa [h] using this
  refine ⟨μ, ?_, ?_⟩
  · intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn hc r t hr
      by_cases h1 : n = 1
      · subst h1
        rw [pin1, mul_one, hμ1, one_mul]
      have hp : n.minFac.Prime := Nat.minFac_prime h1
      obtain ⟨k, m, hnd, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' n.minFac hp.ne_one
      obtain ⟨v, hv⟩ := hex _ hp
      have hk : k ≠ 0 := by
        rintro rfl
        rw [pow_zero, one_mul] at hnm
        exact hnd (hnm ▸ Nat.minFac_dvd n)
      have hm0 : 0 < m := Nat.pos_of_ne_zero (by
        rintro rfl
        simp at hnm
        omega)
      have hmlt : m < n := by
        have h2 : 2 ≤ n.minFac ^ k := by
          calc 2 ≤ n.minFac := hp.two_le
            _ = n.minFac ^ 1 := (pow_one _).symm
            _ ≤ n.minFac ^ k := Nat.pow_le_pow_right hp.pos (Nat.pos_of_ne_zero hk)
        nlinarith
      have hmc : m.Coprime N := Nat.Coprime.coprime_dvd_left (Dvd.intro_left _ hnm.symm) hc
      have hvb : ¬ Bad N v := hpN v fun h =>
        Nat.not_coprime_of_dvd_of_dvd hp.one_lt (Nat.minFac_dvd n) (hv ▸ h) hc
      have hcop : (normV v ^ k).Coprime m :=
        Nat.Coprime.pow_left k (by rw [hv]; exact (Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
      have hpin : pin n = UpperTheory.ConvolutionTheory.RankTwoDescent.pv v ^ k * pin m := by
        rw [hnm, ← hv, pmul _ _ (pow_pos (hpr v).pos k) hm0, ppow]
      have hg : em E (aE (iy r * pin n) * rot t) = em E (aE (UpperTheory.ConvolutionTheory.RankTwoDescent.pv v ^ k)) * em E (aE (iy r * pin m) * rot t) := by
        rw [hpin, mul_left_comm, aE_mul', map_mul, map_mul, map_mul, mul_assoc]
      have hnv : n = normV v ^ k * m := by rw [hv]; exact hnm
      rw [hg, hM1 v hvb k _ (fun w hw => UpperTheory.kAt_diag_ideleOfNat_mul_rotation_of_not_dvd E v m r t hm0 (by rw [hv]; exact hnd) w hw), ih m hmlt hm0 hmc r t hr,
        ← mul_assoc, ← hμv v k hvb, ← hμm _ _ (pow_pos (hpr v).pos k) hm0 hcop, ← hnv]
  · rintro ⟨r, t, hr, hne⟩ n hn
    refine UpperTheory.eq_convolution_squareIndicator_of_euler_factors N a (bN N χ μ) hG.pos hIs.one hIs.mul hIs.bad ?_ ?_ ?_ ?_ n hn
    · simp [bN, pin1, hμ1]
    · intro x y hx hy hxy
      simp only [bN, Nat.coprime_mul_iff_left]
      by_cases h1 : x.Coprime N
      · by_cases h2 : y.Coprime N
        · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2, pmul x y hx hy, hμm x y hx hy hxy, map_mul, Units.val_mul]
          push_cast
          ring
        · rw [if_neg fun h => h2 h.2, if_neg h2, mul_zero]
      · rw [if_neg fun h => h1 h.1, if_neg h1, zero_mul]
    · intro x hx
      simp only [bN]
      rw [if_neg hx]
    · intro p hp hpn
      obtain ⟨v, rfl⟩ := hex p hp
      have hvb := hpN v hpn
      rw [hM2 v hvb ⟨_, hne⟩]
      congr 1
      funext k
      have hc : (normV v ^ k).Coprime N := Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 hpn)
      simp only [bN, if_pos hc]
      rw [ppow, map_pow, Units.val_pow_eq_pow_val, hμv v k hvb]
      rfl
