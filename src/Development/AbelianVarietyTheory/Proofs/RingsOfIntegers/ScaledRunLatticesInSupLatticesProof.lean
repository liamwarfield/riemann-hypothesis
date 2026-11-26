module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ShortGeneratorPlaceValuationBoundProof

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledShortLatticeLeOfShortGeneratorBound
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledShortLatticeLeOfShortGeneratorBound
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.PlaceTop
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.PullbackSections

namespace ShortClause

theorem val_mul {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    vLa la (a * b) = vLa la a + vLa la b := by
  unfold vLa
  rw [map_mul, WithZero.log_mul ((Valuation.ne_zero_iff _).2 ha) ((Valuation.ne_zero_iff _).2 hb)]
  ring

theorem val_pow {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (a : K) (n : ℕ) :
    vLa la (a ^ n) = n * vLa la a := by
  unfold vLa
  rw [map_pow, WithZero.log_pow]
  simp

theorem val_nat_nonneg {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (p : ℕ) :
    0 ≤ vLa la (p : K) := by
  unfold vLa
  have h1 : la.valuation K (p : K) ≤ 1 := by
    have := la.valuation_le_one (K := K) (p : 𝓞 K)
    simpa using this
  by_cases h0 : la.valuation K (p : K) = 0
  · rw [h0]; simp
  · have := (WithZero.log_le_log h0 one_ne_zero).2 h1
    rw [WithZero.log_one] at this
    omega

theorem thc_le_of_eq_zero {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j) (s : 𝓞 B.KO)
    (w : WeightFamilies.Wt D j)
    (hsc : s * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 B.KO) ^ (D.R.f * D.R.r * w.n) = 0) :
    X.Thc s w ≤ B.Mlat j w := by
  intro F hF
  obtain ⟨F1, hF1, rfl⟩ := Submodule.mem_map.mp hF
  obtain ⟨G, hG, rfl⟩ := Submodule.mem_map.mp hF1
  simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
  rw [hsc, zero_smul]
  exact (B.Mlat j w).zero_mem

end ShortClause


open ShortClause in
theorem thc_le_of_shortBound : ShortBoundSt → ∀ (D : D7) (T : Top D) (h : LawsP T) (_hs : LawsSh T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D), Oriented T EX → ∀ (w : WeightFamilies.Wt D j) (a b : ℕ) (s : 𝓞 T.Q.c.F), c2 D w ≤ a → Formalism.MainNotions.DIV.Cons.cHalf w ≤ b → s = (zOwnP D (T.dδ j w.n).pd w : 𝓞 T.Q.c.F) * nnW (recB h.toLawsCore) hinj EX w * (pPow D a b b : 𝓞 T.Q.c.F) → (recPJ h j hj).Thc s w ≤ (recB h.toLawsCore).Mlat j w := by
  intro hSB D T h hs j hj hinj EX hO w a b s ha hb hsE
  by_cases hsc : s * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 T.Q.c.F) ^ (D.R.f * D.R.r * w.n) = 0
  · exact thc_le_of_eq_zero (recPJ h j hj) s w hsc
  refine Pf.Thc_le_Mlat (recPJ h j hj) s w ?_
  intro G hG la y
  have hG' : G.1 ∈ Submodule.span (𝓞 T.Q.c.F) (T.sh j w) := hG
  have key := Pf.le_val_of_mem_span (isVal_vAt (y : T.PtA j la))
    (fun g hg => hSB D T h hs j hj hinj EX hO w g hg la y) _ hG'
  refine le_trans ?_ (key.trans (recPJ_vAt_inc h j hj la y w G).ge)
  rw [EReal.coe_le_coe_iff, neg_le_neg_iff]
  set nn : 𝓞 T.Q.c.F := nnW (recB h.toLawsCore) hinj EX w with hnn
  have e : ((s * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 T.Q.c.F) ^ (D.R.f * D.R.r * w.n) : 𝓞 T.Q.c.F) : T.Q.c.F) =
      (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) ^ (DF w + 2 * D.R.f * D.R.r * w.n) * (nn : T.Q.c.F) *
        ((pPow D a b b : ℕ) : T.Q.c.F) * ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F) ^ (D.R.f * D.R.r * w.n) := by
    rw [hsE, zOwnP]
    push_cast
    ring
  have hne : (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) ^ (DF w + 2 * D.R.f * D.R.r * w.n) * (nn : T.Q.c.F) *
        ((pPow D a b b : ℕ) : T.Q.c.F) * ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F) ^ (D.R.f * D.R.r * w.n) ≠ 0 := by
    rw [← e]
    exact fun h0 => hsc (RingOfIntegers.coe_eq_zero_iff.1 h0)
  have h4 := right_ne_zero_of_mul hne
  have h123 := left_ne_zero_of_mul hne
  have h3 := right_ne_zero_of_mul h123
  have h12 := left_ne_zero_of_mul h123
  have h2 := right_ne_zero_of_mul h12
  have h1 := left_ne_zero_of_mul h12
  have hv : vLa (la : HeightOneSpectrum (𝓞 T.Q.c.F))
      ((s * ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 T.Q.c.F) ^ (D.R.f * D.R.r * w.n) : 𝓞 T.Q.c.F) : T.Q.c.F) =
      ((DF w + 2 * D.R.f * D.R.r * w.n : ℕ) : ℤ) * vLa la (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) + vLa la (nn : T.Q.c.F) +
        vLa la ((pPow D a b b : ℕ) : T.Q.c.F) +
        ((D.R.f * D.R.r * w.n : ℕ) : ℤ) * vLa la ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F) := by
    rw [e, val_mul _ h123 h4, val_mul _ h12 h3, val_mul _ h1 h2, val_pow, val_pow]
  have hr := GlobalTheory.T.ramified_prime_loss_le_valuation_prime_power D T.Q.c.F la j w a b ha hb
  have hp : (0 : ℝ) ≤ ((vLa (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) : ℤ) : ℝ) := by
    exact_mod_cast val_nat_nonneg _ _
  have hk : (0 : ℝ) ≤ ((vLa (la : HeightOneSpectrum (𝓞 T.Q.c.F)) (((T.dδ j w.n).pd : ℕ) : T.Q.c.F) : ℤ) : ℝ) *
      ((D.R.f : ℝ) * D.R.r * w.n) := mul_nonneg hp (by positivity)
  refine le_trans ?_ (le_of_eq (congrArg (fun z : ℤ => (z : ℝ)) hv).symm)
  simp only [Int.cast_add, Int.cast_mul, Int.cast_natCast]
  generalize ((vLa (la : HeightOneSpectrum (𝓞 T.Q.c.F)) ((D.host.g 0 * D.host.g 1 : ℕ) : T.Q.c.F) : ℤ) : ℝ) = x
  push_cast
  nlinarith [hr, hk]

end GlobalTheory.PlaceTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledShortLatticeLeOfShortGeneratorBoundStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledShortLattice_le_of_shortGenerator_bound : ShortBoundSt → ∀ (D : D7) (T : Top D) (h : LawsP T) (_hs : LawsSh T) (j : ℕ) (hj : InR D j) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D), Oriented T EX → ∀ (w : WeightFamilies.Wt D j) (a b : ℕ) (s : 𝓞 T.Q.c.F), c2 D w ≤ a → Formalism.MainNotions.DIV.Cons.cHalf w ≤ b → s = (zOwnP D (T.dδ j w.n).pd w : 𝓞 T.Q.c.F) * nnW (recB h.toLawsCore) hinj EX w * (pPow D a b b : 𝓞 T.Q.c.F) → (recPJ h j hj).Thc s w ≤ (recB h.toLawsCore).Mlat j w := by
  first | exact @GlobalTheory.PlaceTop.thc_le_of_shortBound | exact GlobalTheory.PlaceTop.thc_le_of_shortBound | (intros; apply GlobalTheory.PlaceTop.thc_le_of_shortBound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.WeightNormalizerAndExponentsOfWeightSum
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.WeightNormalizerAndExponentsOfWeightSum
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PlaceScalar
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop

theorem ceil_mul_add_le (x y : ℝ) (k : ℕ) : ⌈(k : ℝ) * x + y⌉₊ ≤ k * ⌈x⌉₊ + ⌈y⌉₊ := by
  rw [Nat.ceil_le]
  push_cast
  have h1 := Nat.le_ceil x
  have h2 := Nat.le_ceil y
  have h3 : (k : ℝ) * x ≤ k * (⌈x⌉₊ : ℝ) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg k)
  linarith

theorem weight_normalizer_and_exponents_of_weight_sum :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (wL wF w : WeightFamilies.Wt D j) (k : ℕ), (∀ τ i, w.aP τ i = wF.aP τ i + k * wL.aP τ i) → (∀ τ i, w.aM τ i = wF.aM τ i + k * wL.aM τ i) → nnW B hinj EX w = nnW B hinj EX wL ^ k * nnW B hinj EX wF ∧ c2 D w ≤ k * c2 D wL + c2 D wF ∧ Formalism.MainNotions.DIV.Cons.cHalf w ≤ k * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF := by
  intro D B hinj EX j wL wF w k hP hM
  have hp : Formalism.MainNotions.DIV.Cons.Dplus w = k * Formalism.MainNotions.DIV.Cons.Dplus wL + Formalism.MainNotions.DIV.Cons.Dplus wF := by
    simp only [Formalism.MainNotions.DIV.Cons.Dplus, hP, Finset.sum_add_distrib, Finset.mul_sum]
    ring
  have hm : Formalism.MainNotions.DIV.Cons.Dminus w = k * Formalism.MainNotions.DIV.Cons.Dminus wL + Formalism.MainNotions.DIV.Cons.Dminus wF := by
    simp only [Formalism.MainNotions.DIV.Cons.Dminus, hM, Finset.sum_add_distrib, Finset.mul_sum]
    ring
  have hs : ∀ u : WeightFamilies.Wt D j, WeightAlgebra.DF u = Formalism.MainNotions.DIV.Cons.Dplus u + Formalism.MainNotions.DIV.Cons.Dminus u := by
    intro u
    simp only [WeightAlgebra.DF, WeightAlgebra.degP, Formalism.MainNotions.DIV.Cons.Dplus, Formalism.MainNotions.DIV.Cons.Dminus, Finset.sum_add_distrib]
  have hf : (WeightAlgebra.DF w : ℝ) = k * (WeightAlgebra.DF wL : ℝ) + (WeightAlgebra.DF wF : ℝ) := by
    rw [hs, hs, hs, hp, hm]
    push_cast
    ring
  refine ⟨?_, ?_, ?_⟩
  · simp only [nnW, hp, hm]
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    ring
  · unfold c2
    exact le_of_eq (by exact_mod_cast hf)
  · unfold Formalism.MainNotions.DIV.Cons.cHalf
    have : (WeightAlgebra.DF w : ℝ) / 2 = k * ((WeightAlgebra.DF wL : ℝ) / 2) + (WeightAlgebra.DF wF : ℝ) / 2 := by
      rw [hf]; ring
    rw [this]
    exact ceil_mul_add_le _ _ _

end GlobalTheory.PlaceScalar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.WeightNormalizerAndExponentsOfWeightSumStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nnW_eq_pow_mul_and_c2_cHalf_le_of_weight_sum : ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (wL wF w : WeightFamilies.Wt D j) (k : ℕ), (∀ τ i, w.aP τ i = wF.aP τ i + k * wL.aP τ i) → (∀ τ i, w.aM τ i = wF.aM τ i + k * wL.aM τ i) → nnW B hinj EX w = nnW B hinj EX wL ^ k * nnW B hinj EX wF ∧ c2 D w ≤ k * c2 D wL + c2 D wF ∧ Formalism.MainNotions.DIV.Cons.cHalf w ≤ k * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF := by
  first | exact @GlobalTheory.PlaceScalar.weight_normalizer_and_exponents_of_weight_sum | exact GlobalTheory.PlaceScalar.weight_normalizer_and_exponents_of_weight_sum | (intros; apply GlobalTheory.PlaceScalar.weight_normalizer_and_exponents_of_weight_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledRunLatticesInSupLatticesProof
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop
namespace GlobalTheory.PlaceTop


set_option maxHeartbeats 4000000 in
theorem integralityCondition_of_addedPoints_secondNorm {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (n : GlobalTheory.RunIn.SecNorm B) (X : PJ D B P j)
    (E : PtExt X) (hM : IntAtExt X E) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (hX : H2 X S ka wL wF) :
    H2 (PJ.tol2NormAlt n.N n.h0 n.h1 n.h2 n.h3 n.h4 (xplus X E hM)) (scalarsWithNorm n.N n.h0 n.h1 n.h2 n.h3 n.h4 S) ka wL wF := hX


set_option maxHeartbeats 4000000 in
theorem integralityCondition_algebraicPoints (D : D7) (T : Top D) (h : LawsP T) (hs : LawsSh T) (j : ℕ) (hj : InR D j)
    (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (ho : Oriented T EX) (p : ℕ) (hp : ∀ n, (T.dδ j n).pd = p)
    (ka wL wF : WeightFamilies.Wt D j) (T₀ nP : ℕ) (hF : IsF' ka wL wF T₀ nP) :
    H2 (recPJ h j hj) (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF T₀) ka wL wF := by
  have key : ∀ (w : WeightFamilies.Wt D j) (k : ℕ), (∀ τ i, w.aP τ i = wF.aP τ i + k * wL.aP τ i) →
      (∀ τ i, w.aM τ i = wF.aM τ i + k * wL.aM τ i) →
      (recPJ h j hj).Thc ((zOwnP D p w : 𝓞 (recB h.toLawsCore).KO) * nnW (recB h.toLawsCore) hinj EX wL ^ k *
        nnW (recB h.toLawsCore) hinj EX wF *
        (pPow D (k * c2 D wL + c2 D wF) (k * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF)
          (k * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF) : 𝓞 (recB h.toLawsCore).KO)) w ≤
        (recB h.toLawsCore).Mlat j w := by
    intro w k h1 h2
    obtain ⟨e, a, b⟩ := GlobalTheory.T.nnW_eq_pow_mul_and_c2_cHalf_le_of_weight_sum D (recB h.toLawsCore) hinj EX j wL wF w k h1 h2
    refine GlobalTheory.T.scaledShortLattice_le_of_shortGenerator_bound GlobalTheory.T.shortGeneratorPlaceValuationBound_proof D T h hs j hj hinj EX ho w _ _ _ a b ?_
    rw [hp, e]
    exact congrArg (· * _) (mul_assoc _ _ _)
  refine ⟨GlobalTheory.T.scaledThetaLattice_le_supLattice_every_weight D T h j hj hinj EX ho wL, ?_, ?_, ?_⟩
  · refine GlobalTheory.T.scaledShortLattice_le_of_shortGenerator_bound GlobalTheory.T.shortGeneratorPlaceValuationBound_proof D T h hs j hj hinj EX ho wF _ _ _ le_rfl le_rfl ?_
    rw [hp]
    rfl
  · exact key (wadd wF (wsmul (WeightFamilies.dimY D j) wL)) (WeightFamilies.dimY D j) (fun _ _ => rfl) (fun _ _ => rfl)
  · exact key ka T₀ (fun τ i => by have := hF.2.1 τ i; zify; linarith)
      (fun τ i => by have := hF.2.2 τ i; zify; linarith)

theorem scaledRunLatticesInSupLattices_proof : ScaledLatticesInSupLattices := by
  intro D T h hs j hj hinj EX ho p hp ka wL wF T₀ nP hF
  have H := integralityCondition_algebraicPoints D T h hs j hj hinj EX ho p hp ka wL wF T₀ nP hF
  exact ⟨H, fun n => integralityCondition_of_addedPoints_secondNorm n _ _ _ _ ka wL wF H⟩

end GlobalTheory.PlaceTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ScaledRunLatticesInSupLatticesProofStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaledRunLattices_in_supLattices : ScaledLatticesInSupLattices := by
  first | exact @GlobalTheory.PlaceTop.scaledRunLatticesInSupLattices_proof | exact GlobalTheory.PlaceTop.scaledRunLatticesInSupLattices_proof | (intros; apply GlobalTheory.PlaceTop.scaledRunLatticesInSupLattices_proof <;> assumption)
end
