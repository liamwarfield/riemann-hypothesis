module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicContinuousEvaluationExistsUniqueSubstNatura
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInvariantDerivationFormalGroupLawIterate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfFrobeniusSemilinearEquationExistsUnique
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassValuesLatticeTau
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryEqAdditiveLeadingTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspProdCharTransport
public import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceOfStrictlyHenselianSta
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFormalGroupCoboundaryHomogeneous

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartEvalSquareProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartEvalSquareProperties
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog.Chart

theorem isEval_comp {p : ℕ} {O A A' : Type} {σ : Type} [CommRing O] [CommRing A] [CommRing A']
    [Algebra O A] [Algebra O A'] {x : σ → A} {E : MvPowerSeries σ O →ₐ[O] A} (hE : IsEval p x E)
    (g : A →ₐ[O] A') : IsEval p (fun i => g (x i)) (g.comp E) := by
  refine ⟨fun i => by simp [hE.1 i], fun m => ?_⟩
  obtain ⟨N, hN⟩ := hE.2 m
  refine ⟨N, fun f hf => ?_⟩
  have := map_dvd g (hN f hf)
  rwa [map_pow, map_natCast] at this

theorem ev₂_eval : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O]
    (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n f,
    c.ev₂ n (inL f) = c.ev n f ⊗ₜ[O] 1 ∧ c.ev₂ n (inR f) = 1 ⊗ₜ[O] c.ev n f ∧
    c.ev₂ n (subst c.μ f) = Coalgebra.comul (R := O) (c.ev n f) ∧
    c.ev₂ n (cob1 c.μ f) = cobOne O (G.A n) (c.ev n f) := by
  intro p O _ _ G d c n f
  haveI : IsAdicComplete (Ideal.span {(p : G.A n ⊗[O] G.A n)}) (G.A n ⊗[O] G.A n) :=
    T.isAdicComplete_of_finite_projective_algebra p O (G.A n ⊗[O] G.A n)
  have hnil : ∀ i, ∃ N : ℕ, (p : G.A n ⊗[O] G.A n) ∣
      (Sum.elim (fun i => c.x n i ⊗ₜ[O] (1 : G.A n)) (fun i => (1 : G.A n) ⊗ₜ[O] c.x n i) i) ^ N := by
    rintro (i | i)
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
    · obtain ⟨N, hN⟩ := c.nil n i
      refine ⟨N, ?_⟩
      have := map_dvd (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)) hN
      simpa [map_pow, map_natCast] using this
  have H := ((CEval.continuous_eval p O (G.A n ⊗[O] G.A n) (Fin d ⊕ Fin d) _ hnil).2
    (c.ev₂ n) (c.isEval₂ n)).1
  have h1 : c.ev₂ n (inL f) = c.ev n f ⊗ₜ[O] 1 := by
    have hx : (fun j => c.ev₂ n ((fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) O)) j)) =
        fun j => Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n)
          (c.x n j) := funext fun j => (c.isEval₂ n).1 (Sum.inl j)
    have hE := isEval_comp (c.isEval n)
      (Algebra.TensorProduct.includeLeft (R := O) (S := O) (A := G.A n) (B := G.A n))
    rw [← hx] at hE
    exact H (Fin d) _ _ (fun _ => constantCoeff_X _) hE f
  have h2 : c.ev₂ n (inR f) = 1 ⊗ₜ[O] c.ev n f := by
    have hx : (fun j => c.ev₂ n ((fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) j)) =
        fun j => Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n)
          (c.x n j) := funext fun j => (c.isEval₂ n).1 (Sum.inr j)
    have hE := isEval_comp (c.isEval n)
      (Algebra.TensorProduct.includeRight (R := O) (A := G.A n) (B := G.A n))
    rw [← hx] at hE
    exact H (Fin d) _ _ (fun _ => constantCoeff_X _) hE f
  have h3 : c.ev₂ n (subst c.μ f) = Coalgebra.comul (R := O) (c.ev n f) := by
    have hx : (fun j => c.ev₂ n (c.μ j)) =
        fun j => Bialgebra.comulAlgHom O (G.A n) (c.x n j) := funext fun j => c.comul n j
    have hE := isEval_comp (c.isEval n) (Bialgebra.comulAlgHom O (G.A n))
    rw [← hx] at hE
    exact H (Fin d) _ _ c.isLaw.const hE f
  refine ⟨h1, h2, h3, ?_⟩
  rw [cob1, map_sub, map_sub, h1, h2, h3, cobOne_apply]

end GlobalTheory.QLog.Chart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartEvalSquarePropertiesStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalChart_evalSquare_properties : ∀ (p : ℕ) (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ n f, c.ev₂ n (inL f) = c.ev n f ⊗ₜ[O] 1 ∧ c.ev₂ n (inR f) = 1 ⊗ₜ[O] c.ev n f ∧ c.ev₂ n (subst c.μ f) = Coalgebra.comul (R := O) (c.ev n f) ∧ c.ev₂ n (cob1 c.μ f) = cobOne O (G.A n) (c.ev n f) := by
  first | exact @GlobalTheory.QLog.Chart.ev₂_eval | exact GlobalTheory.QLog.Chart.ev₂_eval | (intros; apply GlobalTheory.QLog.Chart.ev₂_eval <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfSquareZeroFrameInvariantEqZeroOfTauDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfSquareZeroFrameInvariantEqZeroOfTauDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TauUniq

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {ε : PreTilt O p} (F : BFrame ε)

theorem p_cancel {b c : F.B} (h : (p : F.B) * b = p * c) : b = c := by
  have h1 := congrArg (algebraMap F.B F.Q) h
  simp only [map_mul, map_natCast] at h1
  exact F.frame.inj (F.frame.unit_p.mul_left_cancel h1)

theorem frob_teich (x : PreTilt O p) :
    WittVector.frobenius (WittVector.teichmuller p x) = WittVector.teichmuller p x ^ p := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]

theorem sigma_tau : F.σ F.τ = p * F.τ := by
  apply p_cancel F
  have hS : WittVector.frobenius (Sandwich.mu ε) =
      Sandwich.mu ε * ∑ i ∈ Finset.range p, WittVector.teichmuller p ε ^ i := by
    unfold Sandwich.mu
    rw [map_sub, map_one, frob_teich, mul_comm, geom_sum_mul]
  have hd : Sandwich.mu ε ∣ ∑ i ∈ Finset.range p, WittVector.teichmuller p ε ^ i - (p : Ainf p O) := by
    have : ∑ i ∈ Finset.range p, WittVector.teichmuller p ε ^ i - (p : Ainf p O) =
        ∑ i ∈ Finset.range p, (WittVector.teichmuller p ε ^ i - 1) := by
      simp [Finset.sum_sub_distrib]
    rw [this]
    apply Finset.dvd_sum
    intro i _
    simpa [Sandwich.mu, one_pow] using sub_dvd_pow_sub_pow (WittVector.teichmuller p ε) 1 i
  have h0 := (F.τ_mul _).2 hd
  rw [map_sub, map_natCast] at h0
  have h1 : (p : F.B) * F.σ F.τ = F.a (WittVector.frobenius (Sandwich.mu ε)) := by
    rw [← F.σ_a, ← F.p_τ, map_mul, map_natCast]
  rw [h1, hS, map_mul, ← F.p_τ]
  linear_combination (p : F.B) * h0

theorem theta_tau [IsDomain O] : F.θ F.τ = 0 :=
  mul_self_eq_zero.1 (by rw [← map_mul, F.τ_sq, map_zero])

theorem dvd_tau {b : F.B} (h : F.τ ∣ b) : ∃ x, b = F.τ * F.a x := by
  obtain ⟨c, rfl⟩ := h
  obtain ⟨x, y, rfl⟩ := F.gen c
  exact ⟨x, by rw [mul_add, ← mul_assoc, F.τ_sq, zero_mul, add_zero]⟩

theorem lift_exists {ι : Type} (M : Matrix ι ι F.B) :
    ∃ m : Matrix ι ι (Ainf p O), ∀ i j, F.τ ∣ M i j - F.a (m i j) := by
  choose x y h using fun i j => F.gen (M i j)
  exact ⟨Matrix.of x, fun i j => ⟨F.a (y i j), by rw [h i j, Matrix.of_apply]; ring⟩⟩

theorem step {ι : Type} [Fintype ι] (M : Matrix ι ι F.B) (m : Matrix ι ι (Ainf p O))
    (hm : ∀ i j, F.τ ∣ M i j - F.a (m i j)) (u : ι → F.B) (u' : ι → Ainf p O)
    (hu : ∀ j, F.τ ∣ u j - F.a (u' j)) (i : ι) :
    F.τ ∣ M.mulVec (fun j => F.σ (u j)) i -
      F.a (m.mulVec (fun j => WittVector.frobenius (u' j)) i) := by
  have hI : Ideal.span {F.τ} ≤ (Ideal.span {F.τ}).comap F.σ := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, sigma_tau]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  simp only [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq] at hm hu ⊢
  have hs : ∀ j, Ideal.Quotient.mk (Ideal.span {F.τ}) (F.σ (u j)) =
      Ideal.Quotient.mk (Ideal.span {F.τ}) (F.a (WittVector.frobenius (u' j))) := by
    intro j
    rw [← F.σ_a, ← Ideal.quotientMap_mk (H := hI), hu j, Ideal.quotientMap_mk]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
  exact Finset.sum_congr rfl fun j _ => by rw [hm i j, hs j]

theorem iter {ι : Type} [Fintype ι] (M : Matrix ι ι F.B) (m : Matrix ι ι (Ainf p O))
    (hm : ∀ i j, F.τ ∣ M i j - F.a (m i j)) (w : ι → Ainf p O) (n : ℕ) (i : ι) :
    F.τ ∣ (fun v : ι → F.B => M.mulVec fun j => F.σ (v j))^[n] (fun j => F.a (w j)) i -
      F.a ((fun v : ι → Ainf p O => m.mulVec fun j => WittVector.frobenius (v j))^[n] w i) := by
  induction n generalizing i with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact step F M m hm _ _ ih i

theorem nil_lift [IsDomain O] {ι : Type} [Fintype ι] (M : Matrix ι ι F.B) (m : Matrix ι ι (Ainf p O))
    (hm : ∀ i j, F.τ ∣ M i j - F.a (m i j)) (hM : IsNil F.θ F.σ M) :
    IsNil (WittVector.fontaineTheta O p) (WittVector.frobenius : Ainf p O →+* Ainf p O) m := by
  obtain ⟨N, hN⟩ := hM
  refine ⟨N, fun w i hu => hN (fun j => F.a (w j)) i ?_⟩
  obtain ⟨c, hc⟩ := iter F M m hm w N i
  rw [sub_eq_iff_eq_add] at hc
  rw [hc, map_add (f := _), map_mul, theta_tau, zero_mul, zero_add, F.θ_a]
  exact hu

theorem core (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal)
    [Algebra O C] [IsDomain O] (hv : v.Integers O) (hε : IsPrimitiveSystem ε) {ι : Type} [Fintype ι]
    (M : Matrix ι ι F.B) (hM : IsNil F.θ F.σ M) (z : ι → Ainf p O)
    (hz : ∀ i, F.τ * F.a (z i) = F.τ * M.mulVec (fun j => F.σ (F.a (z j))) i) (i : ι) :
    F.τ * F.a (z i) = 0 := by
  obtain ⟨m, hm⟩ := lift_exists F M
  have key : ∀ i, Sandwich.mu ε ∣ z i - m.mulVec (fun j => WittVector.frobenius (z j)) i := by
    intro i
    rw [← F.τ_mul, map_sub, mul_sub, hz i]
    obtain ⟨c, hc⟩ := step F M m hm (fun j => F.a (z j)) z (fun j => by simp) i
    rw [sub_eq_iff_eq_add] at hc
    rw [hc, mul_add, ← mul_assoc, F.τ_sq, zero_mul, zero_add, sub_self]
  exact (F.τ_mul _).2 ((GlobalTheory.T.ainf_frobenius_semilinear_equation_existsUnique p C v O hv ε hε ι m (nil_lift F M m hm hM)).2 z key i)

theorem vec_eq {ι : Type} [Fintype ι] (M : Matrix ι ι F.B) (g : ι → F.B) (z : ι → Ainf p O)
    (hz : ∀ i, g i = F.τ * F.a (z i))
    (hg : ∀ i, M.mulVec (fun j => F.σ (g j)) i = (p : F.B) * g i) (i : ι) :
    F.τ * F.a (z i) = F.τ * M.mulVec (fun j => F.σ (F.a (z j))) i := by
  apply p_cancel F
  have e := hg i
  simp only [Matrix.mulVec, dotProduct, hz, map_mul, sigma_tau F] at e
  rw [← e]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem blk_mul_blk (d k : ℕ) (R : Type) [CommRing R] (u : R) :
    blk d k 1 u * blk d k u 1 = u • (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) R) := by
  rw [blk, blk, Matrix.diagonal_mul_diagonal, Matrix.smul_one_eq_diagonal]
  congr 1
  funext i
  rcases i with i | i <;> simp

theorem eq_zero_of_tau_dvd : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B), IsUnit U → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → (∀ Y : Matrix (Fin d ⊕ Fin k) (Fin h) F.B, Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y → (∀ i m, F.τ ∣ Y i m) → Y = 0) ∧ ∀ g : Fin d ⊕ Fin k → F.B, Matrix.mulVec (U * blk d k (p : F.B) 1) (fun i => F.σ (g i)) = (p : F.B) • g → (∀ i, F.τ ∣ g i) → g = 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε F d k h U hU hN1 hN2
  have hdet : IsUnit U.transpose.det := by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det U).1 hU
  refine ⟨fun Y hY hdiv => ?_, fun g hg hdiv => ?_⟩
  · choose z hz using fun i c => dvd_tau F (hdiv i c)
    have hM : U.transpose⁻¹ * blk d k 1 (p : F.B) * Y.map F.σ = (p : F.B) • Y := by
      rw [hY, Matrix.mul_assoc, ← Matrix.mul_assoc (blk d k 1 (p : F.B)),
        ← Matrix.mul_assoc (blk d k 1 (p : F.B)), blk_mul_blk, Matrix.smul_mul, Matrix.one_mul,
        Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet,
        Matrix.one_mul]
    ext i c
    rw [hz i c, Matrix.zero_apply]
    refine core F C v hv hε _ hN1 (fun j => z j c)
      (vec_eq F _ (fun j => Y j c) (fun j => z j c) (fun j => hz j c) (fun i => ?_)) i
    have e := congrArg (fun X => X i c) hM
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using e
  · choose z hz using fun i => dvd_tau F (hdiv i)
    funext i
    rw [hz i, Pi.zero_apply]
    exact core F C v hv hε _ hN2 z
      (vec_eq F _ g z hz (fun i => by simpa using congrFun hg i)) i

end GlobalTheory.TauUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfSquareZeroFrameInvariantEqZeroOfTauDvdStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainfSquareZeroFrame_invariant_eq_zero_of_tau_dvd : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k h : ℕ) (U : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B), IsUnit U → IsNil F.θ F.σ (U.transpose⁻¹ * blk d k 1 (p : F.B)) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → (∀ Y : Matrix (Fin d ⊕ Fin k) (Fin h) F.B, Y.map F.σ = blk d k (p : F.B) 1 * U.transpose * Y → (∀ i m, F.τ ∣ Y i m) → Y = 0) ∧ ∀ g : Fin d ⊕ Fin k → F.B, Matrix.mulVec (U * blk d k (p : F.B) 1) (fun i => F.σ (g i)) = (p : F.B) • g → (∀ i, F.τ ∣ g i) → g = 0 := by
  first | exact @GlobalTheory.TauUniq.eq_zero_of_tau_dvd | exact GlobalTheory.TauUniq.eq_zero_of_tau_dvd | (intros; apply GlobalTheory.TauUniq.eq_zero_of_tau_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionNonrealMultiplier
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionIntegralJ
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionIntegralJ
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.WpInt

theorem isIntegral_int_of_closure (y : ℂ)
    (hy : IsIntegral (integralClosure ℤ ℂ).toSubring y) : IsIntegral ℤ y := by
  set R : Subring ℂ := (integralClosure ℤ ℂ).toSubring
  haveI : Algebra.IsIntegral ℤ R := ⟨fun r => by
    have h : IsIntegral ℤ (r : ℂ) := r.2
    exact (isIntegral_algHom_iff (R.subtype.toIntAlgHom) Subtype.coe_injective).mp h⟩
  exact isIntegral_trans (R := ℤ) (A := R) y hy

theorem main : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (ω : ℂ), IsIntegral ℤ (jT τ) → ω ^ 12 = DD τ →
    ∀ x : Fin 2 → ZMod N, IsIntegral ℤ (12 * (N : ℂ) ^ 2 * wp N x τ / ω ^ 2) ∧
      IsIntegral ℤ ((N : ℂ) ^ 3 * wpd N x τ / ω ^ 3) := by
  intro N _ τ ω hj hω x
  set R : Subring ℂ := (integralClosure ℤ ℂ).toSubring with hR
  have hjR : IsIntegral R (jT τ) := hj.tower_top
  have hbij : ActBij (vact N) := (GlobalTheory.T.modularGroup_rowVec_and_conj_rightActions N).1.actBij
  have hfam := GlobalTheory.T.weierstrassP_torsion_isModularFamily N
  have halg := GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure (Fin 2 → ZMod N) (vact N)
  have hlin := GlobalTheory.T.hasQExpansionOfLevel_linear_operations N
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hNx : ∀ y : Fin 2 → ZMod N, N • y = 0 := fun y => by
    funext i; simp [nsmul_eq_mul]
  constructor
  · have hF : IsFam (vact N) ((2 : ℕ) : ℤ) (fun y t => (12 * (N : ℂ) ^ 2) * wp N y t) :=
      halg.2.2.1 2 _ (wp N) hfam.1
    have hQ : ∀ y, QAll (· ∈ R) N ((fun y t => (12 * (N : ℂ) ^ 2) * wp N y t) y) := fun y =>
      ⟨fun k => 12 * (N : ℂ) ^ 2 * cP N y k, hlin.2.2.1 _ _ _ (GlobalTheory.T.hasQExpansion_normalizedWeierstrassPTorsion N y),
        fun k => (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N N y k hN (hNx y)).2.2.1⟩
    have h := GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow _ (vact N) 2 N _ R τ ω hN hbij hF hQ hjR hω x
    exact isIntegral_int_of_closure _ h
  · have hF : IsFam (vact N) ((3 : ℕ) : ℤ) (fun y t => ((N : ℂ) ^ 3) * wpd N y t) :=
      halg.2.2.1 3 _ (wpd N) hfam.2
    have hQ : ∀ y, QAll (· ∈ R) N ((fun y t => ((N : ℂ) ^ 3) * wpd N y t) y) := fun y =>
      ⟨fun k => (N : ℂ) ^ 3 * cD N y k, hlin.2.2.1 _ _ _ (GlobalTheory.T.hasQExpansion_normalizedDerivWeierstrassPTorsion N y),
        fun k => (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N N y k hN (hNx y)).2.1⟩
    have h := GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow _ (vact N) 3 N _ R τ ω hN hbij hF hQ hjR hω x
    exact isIntegral_int_of_closure _ h

end GlobalTheory.WpInt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionIntegralJStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_weierstrassP_torsion_integral_j : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (ω : ℂ), IsIntegral ℤ (jT τ) → ω ^ 12 = DD τ → ∀ x : Fin 2 → ZMod N, IsIntegral ℤ (12 * (N : ℂ) ^ 2 * wp N x τ / ω ^ 2) ∧ IsIntegral ℤ ((N : ℂ) ^ 3 * wpd N x τ / ω ^ 3) := by
  first | exact @GlobalTheory.WpInt.main | exact GlobalTheory.WpInt.main | (intros; apply GlobalTheory.WpInt.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionDifference
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionDifference
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam

theorem isIntegral_sq_mul_wp_sub_div : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (ω : ℂ), IsIntegral ℤ (jT τ) → ω ^ 12 = DD τ →
    ∀ x y : Fin 2 → ZMod N, x ≠ 0 → y ≠ 0 →
      IsIntegral ℤ ((N : ℂ) ^ 2 * (wp N x τ - wp N y τ) / ω ^ 2) := by
  intro N _ τ ω hj hω x y hx hy
  obtain ⟨hR, -, -, -, hz, -⟩ := GlobalTheory.T.modularGroup_rowVec_and_conj_rightActions N
  have hvz : ∀ (v : Fin 2 → ZMod N) (γ : SL(2, ℤ)), vact N v γ = 0 ↔ v = 0 := fun v γ => hz v _
  let ι := {p : (Fin 2 → ZMod N) × (Fin 2 → ZMod N) // p.1 ≠ 0 ∧ p.2 ≠ 0}
  let act : ι → SL(2, ℤ) → ι := fun p γ =>
    ⟨(vact N p.1.1 γ, vact N p.1.2 γ), by simp only [ne_eq, hvz]; exact p.2⟩
  have hRA : IsRAct act :=
    ⟨fun p => Subtype.ext (Prod.ext (hR.1 _) (hR.1 _)),
     fun p γ δ => Subtype.ext (Prod.ext (hR.2 _ _ _) (hR.2 _ _ _))⟩
  have h1 : IsFam act 2 (fun p => wp N p.1.1) :=
    (GlobalTheory.QFam.isFam_algebra _ (vact N)).2.2.2.2.2.2.2 ι act (fun p => p.1.1) 2 (wp N) (fun _ _ => rfl) (GlobalTheory.T.weierstrassP_torsion_isModularFamily N).1
  have h2 : IsFam act 2 (fun p => wp N p.1.2) :=
    (GlobalTheory.QFam.isFam_algebra _ (vact N)).2.2.2.2.2.2.2 ι act (fun p => p.1.2) 2 (wp N) (fun _ _ => rfl) (GlobalTheory.T.weierstrassP_torsion_isModularFamily N).1
  have hsub := ((GlobalTheory.QFam.isFam_algebra ι act).2.1 2 _ _ h1 h2).2
  have hfam : IsFam act ((2 : ℕ) : ℤ) (fun p τ => (N : ℂ) ^ 2 * (wp N p.1.1 τ - wp N p.1.2 τ)) := by
    have := (GlobalTheory.QFam.isFam_algebra ι act).2.2.1 2 ((N : ℂ) ^ 2) _ hsub
    simpa using this
  let R : Subring ℂ := (integralClosure ℤ ℂ).toSubring
  have hmem : ∀ z : ℂ, z ∈ R ↔ IsIntegral ℤ z := fun z => by
    simp [R, Subalgebra.mem_toSubring, mem_integralClosure_iff]
  have hNx : ∀ v : Fin 2 → ZMod N, N • v = 0 := fun v => by
    funext i; simp [nsmul_eq_mul, ZMod.natCast_self]
  have hQ : ∀ p : ι, QAll (· ∈ R) N (fun τ => (N : ℂ) ^ 2 * (wp N p.1.1 τ - wp N p.1.2 τ)) := by
    intro p
    refine ⟨fun n => (N : ℂ) ^ 2 * (cP N p.1.1 n - cP N p.1.2 n), ?_, fun n => ?_⟩
    · exact (GlobalTheory.QFam.hasQ_linear N).2.2.1 _ _ _ ((GlobalTheory.QFam.hasQ_linear N).2.1 _ _ _ _ (GlobalTheory.T.hasQExpansion_normalizedWeierstrassPTorsion N _) (GlobalTheory.T.hasQExpansion_normalizedWeierstrassPTorsion N _))
    · show (N : ℂ) ^ 2 * (cP N p.1.1 n - cP N p.1.2 n) ∈ R
      rw [hmem]
      have e : (N : ℂ) ^ 2 * (cP N p.1.1 n - cP N p.1.2 n) =
          (N : ℂ) ^ 2 * cB N p.1.1 n - (N : ℂ) ^ 2 * cB N p.1.2 n := by
        simp only [cP, if_neg p.2.1, if_neg p.2.2]; ring
      rw [e]
      exact (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N N p.1.1 n (NeZero.pos N) (hNx _)).1.sub
        (GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N N p.1.2 n (NeZero.pos N) (hNx _)).1
  have hjR : IsIntegral R (jT τ) := hj.tower_top
  have hT := GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow ι act 2 N (fun p τ => (N : ℂ) ^ 2 * (wp N p.1.1 τ - wp N p.1.2 τ)) R τ ω
    (NeZero.pos N) hRA.actBij hfam hQ hjR hω ⟨(x, y), hx, hy⟩
  haveI : Algebra.IsIntegral ℤ R := ⟨fun r => by
    have h : IsIntegral ℤ ((r : ℂ)) := (hmem _).1 r.2
    exact (isIntegral_algHom_iff (R.subtype.toIntAlgHom) Subtype.coe_injective).1 h⟩
  exact isIntegral_trans _ hT

end GlobalTheory.WpFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionDifferenceStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_weierstrassP_torsion_difference : ∀ (N : ℕ) [NeZero N] (τ : ℍ) (ω : ℂ), IsIntegral ℤ (jT τ) → ω ^ 12 = DD τ → ∀ x y : Fin 2 → ZMod N, x ≠ 0 → y ≠ 0 → IsIntegral ℤ ((N : ℂ) ^ 2 * (wp N x τ - wp N y τ) / ω ^ 2) := by
  first | exact @GlobalTheory.WpFam.isIntegral_sq_mul_wp_sub_div | exact GlobalTheory.WpFam.isIntegral_sq_mul_wp_sub_div | (intros; apply GlobalTheory.WpFam.isIntegral_sq_mul_wp_sub_div <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionNonrealMultiplier
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam.LatTorsVal

theorem exists_tors {L : PeriodPair} {c : ℂ} {τ : ℍ} (hτ : IsTauOf L c τ) (M : ℕ) [NeZero M] (P : ℂ)
    (hP : (M : ℂ) * P ∈ L.lattice) :
    ∃ x : Fin 2 → ZMod M, P - c * tors M τ x ∈ L.lattice ∧ (P ∉ L.lattice → x ≠ 0) := by
  have hom := GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf L c τ hτ
  have tm := GlobalTheory.WpFam.TorsMem.main M τ
  have hc : c ≠ 0 := hτ.1
  have hPz : P = c * (P / c) := by field_simp
  have hMz : (M : ℂ) * (P / c) ∈ (tauPair τ).lattice := by
    rw [← hom.1]
    have : c * ((M : ℂ) * (P / c)) = (M : ℂ) * P := by rw [hPz]; field_simp
    rw [this]; exact hP
  obtain ⟨x, hx⟩ := tm.2.2.2.2 (P / c) hMz
  refine ⟨x, ?_, ?_⟩
  · have := (hom.1 _).2 hx
    rwa [mul_sub, ← hPz] at this
  · rintro hPL rfl
    apply hPL
    have h0 := (tm.2.2.1 0).2 rfl
    have : P / c ∈ (tauPair τ).lattice := by
      have := add_mem hx h0
      simpa using this
    rw [hPz]; exact (hom.1 _).2 this

theorem wp_eq {L : PeriodPair} {c : ℂ} {τ : ℍ} (M : ℕ) (P : ℂ) (x : Fin 2 → ZMod M)
    (h : P - c * tors M τ x ∈ L.lattice) :
    L.weierstrassP P = L.weierstrassP (c * tors M τ x) ∧
      L.derivWeierstrassP P = L.derivWeierstrassP (c * tors M τ x) := by
  have e : P = c * tors M τ x + ((⟨P - c * tors M τ x, h⟩ : L.lattice) : ℂ) := by simp
  constructor
  · rw [e, L.weierstrassP_add_coe]
  · rw [e, L.derivWeierstrassP_add_coe]

theorem main : ∀ (L : PeriodPair) (β Ω : ℂ) (M : ℕ), MulStable L β → β.im ≠ 0 → Ω ^ 12 = latDisc L → 0 < M → (∀ P, (M : ℂ) * P ∈ L.lattice → IsIntegral ℤ (12 * (M : ℂ) ^ 2 * L.weierstrassP P / Ω ^ 2) ∧ IsIntegral ℤ ((M : ℂ) ^ 3 * L.derivWeierstrassP P / Ω ^ 3)) ∧ ∀ P Q, P ∉ L.lattice → Q ∉ L.lattice → (M : ℂ) * P ∈ L.lattice → (M : ℂ) * Q ∈ L.lattice → IsIntegral ℤ ((M : ℂ) ^ 2 * (L.weierstrassP P - L.weierstrassP Q) / Ω ^ 2) := by
  intro L β Ω M hβ hβi hΩ hM
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨c, τ, hτ⟩ := latTau L
  have hj := GlobalTheory.T.isIntegral_jInvariant_of_complexMultiplication L c τ β hτ hβ hβi
  have hω := (GlobalTheory.QFam.jT_eq_and_pow_twelve_eq_DD L c τ hτ).2 Ω hΩ
  have st := (GlobalTheory.T.eisensteinWeierstrass_values_lattice_tau L c Ω τ hτ).2 M
  refine ⟨fun P hP => ?_, fun P Q hP hQ hMP hMQ => ?_⟩
  · obtain ⟨x, hx, -⟩ := exists_tors hτ M P hP
    obtain ⟨e1, e2⟩ := wp_eq M P x hx
    have hv := GlobalTheory.T.isIntegral_weierstrassP_torsion_integral_j M τ _ hj hω x
    rw [e1, e2, mul_div_assoc, mul_div_assoc, ← (st x).1, ← (st x).2, ← mul_div_assoc, ← mul_div_assoc]
    exact hv
  · obtain ⟨x, hx, hx0⟩ := exists_tors hτ M P hMP
    obtain ⟨y, hy, hy0⟩ := exists_tors hτ M Q hMQ
    have hv := GlobalTheory.T.isIntegral_weierstrassP_torsion_difference M τ _ hj hω x y (hx0 hP) (hy0 hQ)
    rw [(wp_eq M P x hx).1, (wp_eq M Q y hy).1, mul_div_assoc, sub_div, ← (st x).1, ← (st y).1, ← sub_div,
      ← mul_div_assoc]
    exact hv

end GlobalTheory.WpFam.LatTorsVal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralWeierstrassPTorsionNonrealMultiplierStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_weierstrassP_torsion_nonreal_multiplier : ∀ (L : PeriodPair) (β Ω : ℂ) (M : ℕ), MulStable L β → β.im ≠ 0 → Ω ^ 12 = latDisc L → 0 < M → (∀ P, (M : ℂ) * P ∈ L.lattice → IsIntegral ℤ (12 * (M : ℂ) ^ 2 * L.weierstrassP P / Ω ^ 2) ∧ IsIntegral ℤ ((M : ℂ) ^ 3 * L.derivWeierstrassP P / Ω ^ 3)) ∧ ∀ P Q, P ∉ L.lattice → Q ∉ L.lattice → (M : ℂ) * P ∈ L.lattice → (M : ℂ) * Q ∈ L.lattice → IsIntegral ℤ ((M : ℂ) ^ 2 * (L.weierstrassP P - L.weierstrassP Q) / Ω ^ 2) := by
  first | exact @GlobalTheory.WpFam.LatTorsVal.main | exact GlobalTheory.WpFam.LatTorsVal.main | (intros; apply GlobalTheory.WpFam.LatTorsVal.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryOneTeichmullerLiftIsCocycleModP
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryOneTeichmullerLiftIsCocycleModP
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

theorem cob2_cob1_lift_mem_intBy_and_swap_sub_mem : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ →
    ∀ f ∈ quasiInt p k (Fin d),
      cob2 (fun i => Katz.lift p (μ i)) (cob1 (fun i => Katz.lift p (μ i)) f) ∈ intBy p k _ p ∧
      swap (cob1 (fun i => Katz.lift p (μ i)) f) - cob1 (fun i => Katz.lift p (μ i)) f ∈
        intBy p k _ p := by
  intro p _ k _ _ _ d μ hμ f hf
  have hL : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0 := fun i => constantCoeff_lift p (hμ.const i)
  obtain ⟨hcc1, hcc2, -⟩ := GlobalTheory.T.formalGroupLawCoboundaryTwo_coboundaryOne (Fr p k) d (fun i => Katz.lift p (μ i)) hL f
  have hred := GlobalTheory.T.reduction_commutes_formalGroupLawCoboundaries p k d μ hμ.const
  have hr := GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k (Fin d ⊕ Fin d)

  have hX3 : ∀ (j : Fin d ⊕ (Fin d ⊕ Fin d)),
      constantCoeff (X j : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) (Fr p k)) = 0 :=
    fun j => constantCoeff_X j
  have hx1 : ∀ i, constantCoeff ((x1 : Fin d → MvPowerSeries _ (Fr p k)) i) = 0 := fun i => hX3 _
  have hx2 : ∀ i, constantCoeff ((x2 : Fin d → MvPowerSeries _ (Fr p k)) i) = 0 := fun i => hX3 _
  have hx3 : ∀ i, constantCoeff ((x3 : Fin d → MvPowerSeries _ (Fr p k)) i) = 0 := fun i => hX3 _
  have hop : ∀ (a b : Fin d → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) (Fr p k)),
      (∀ i, constantCoeff (a i) = 0) → (∀ i, constantCoeff (b i) = 0) →
      ∀ i, constantCoeff (op (fun i => Katz.lift p (μ i)) a b i) = 0 := by
    intro a b ha hb i
    exact ((GlobalTheory.T.powerSeriesEvalTwoGroups_rules (Fr p k) d _ Empty a b ha hb).2.2.2.1 _).trans (hL i)
  refine ⟨?_, ?_⟩
  · rw [hcc1]
    have hA := hop x1 _ hx1 (hop x2 x3 hx2 hx3)
    have hB := hop _ x3 (hop x1 x2 hx1 hx2) hx3
    refine GlobalTheory.T.subst_sub_subst_integral_of_integral_differential p k (Fin d) (Fin d ⊕ (Fin d ⊕ Fin d)) _ _ (op μ x1 (op μ x2 x3)) f
      hA hB (fun i => (hred.2.2.1 i).1) (fun i => ?_) hf
    rw [← hμ.assoc]
    exact (hred.2.2.1 i).2
  · rw [hcc2]
    have hXs : ∀ (j : Fin d ⊕ Fin d),
        constantCoeff (X j : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k)) = 0 :=
      fun j => constantCoeff_X j
    have hS : ∀ i, constantCoeff (swap (Katz.lift p (μ i))) = 0 := by
      intro i
      exact ((GlobalTheory.T.powerSeriesEvalTwoGroups_rules (Fr p k) d _ Empty _ _ (fun j => hXs _) (fun j => hXs _)).2.2.2.1 _).trans
        (hL i)
    refine GlobalTheory.T.subst_sub_subst_integral_of_integral_differential p k (Fin d) (Fin d ⊕ Fin d) _ _ μ f hS hL (fun i => ?_)
      (fun i => (hr.2.2.1 (μ i))) hf
    have := (hred.1 _ _ (hr.2.2.1 (μ i))).2
    rwa [hμ.comm i] at this

end GlobalTheory.Katz
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoboundaryOneTeichmullerLiftIsCocycleModPStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundaryOne_teichmullerLift_isCocycle_mod_p : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ f ∈ quasiInt p k (Fin d), cob2 (fun i => Katz.lift p (μ i)) (cob1 (fun i => Katz.lift p (μ i)) f) ∈ intBy p k _ p ∧ swap (cob1 (fun i => Katz.lift p (μ i)) f) - cob1 (fun i => Katz.lift p (μ i)) f ∈ intBy p k _ p := by
  first | exact @GlobalTheory.Katz.cob2_cob1_lift_mem_intBy_and_swap_sub_mem | exact GlobalTheory.Katz.cob2_cob1_lift_mem_intBy_and_swap_sub_mem | (intros; apply GlobalTheory.Katz.cob2_cob1_lift_mem_intBy_and_swap_sub_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIteratePInvariantDerivationMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIteratePInvariantDerivationMul
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

namespace GlobalTheory.LawDer

open MvPowerSeries in
set_option autoImplicit false in
private lemma iterate_mul_eq_sum_antidiagonal_choose {A : Type} [CommRing A] (D : A → A)
    (hadd : ∀ a b, D (a + b) = D a + D b) (hmul : ∀ a b, D (a * b) = D a * b + a * D b) (n : ℕ)
    (a b : A) :
    D^[n] (a * b) = ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal n, n.choose ij.1 • (D^[ij.1] a * D^[ij.2] b) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hsum : ∀ (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → A), D (∑ x ∈ s, f x) = ∑ x ∈ s, D (f x) :=
      fun s f => map_sum (AddMonoidHom.mk' D hadd) f s
    have hns : ∀ (m : ℕ) (x : A), D (m • x) = m • D x :=
      fun m x => map_nsmul (AddMonoidHom.mk' D hadd) m x
    have hc := Finset.sum_antidiagonal_choose_succ_nsmul (fun i j => D^[i] a * D^[j] b) n
    beta_reduce at hc
    rw [Function.iterate_succ_apply', ih, hsum, hc, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    rw [← Nat.choose_symm_of_eq_add hij.symm, hns, hmul, ← smul_add]
    simp only [Function.iterate_succ_apply']
    rw [add_comm]


open MvPowerSeries in
set_option autoImplicit false in
theorem _root_.GlobalTheory.LawDer.constantCoeff_iterate_invDer_mul : ∀ (p : ℕ) [Fact p.Prime] (R : Type)
    [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    (∀ i, constantCoeff (μ i) = 0) →
    _root_.GlobalTheory.Katz.op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) =
      (fun i => X i) →
    ∀ (u : Fin d → R) (F G : MvPowerSeries (Fin d) R), constantCoeff F = 0 → constantCoeff G = 0 →
      ∃ r : R, constantCoeff ((_root_.GlobalTheory.LawDer.invDer μ u)^[p] (F * G)) = p * r := by
  intro p hp R _ d μ hμ hid u F G hF hG
  have hlin := _root_.GlobalTheory.LawDer.Linear.invDer_linear R d μ hμ u
  set_option synthInstance.maxHeartbeats 100000 in
    rw [iterate_mul_eq_sum_antidiagonal_choose _ hlin.1
    (_root_.GlobalTheory.LawDer.invDer_mul R d μ hμ hid u), map_sum]
  refine Finset.dvd_sum fun ij hij => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
  rw [map_nsmul, map_mul, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos ij.1 with h1 | h1
  · rw [h1, Function.iterate_zero, id, hF]; simp
  rcases Nat.eq_zero_or_pos ij.2 with h2 | h2
  · rw [h2, Function.iterate_zero, id, hG]; simp
  have hdvd : p ∣ p.choose ij.1 := hp.out.dvd_choose_self h1.ne' (by omega)
  exact Dvd.dvd.mul_right (Nat.cast_dvd_cast hdvd) _

end GlobalTheory.LawDer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffIteratePInvariantDerivationMulStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantCoeff_iterate_p_invariantDerivation_mul : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → op μ (fun i => (X i : MvPowerSeries (Fin d) R)) (fun _ => 0) = (fun i => X i) → ∀ (u : Fin d → R) (F G : MvPowerSeries (Fin d) R), constantCoeff F = 0 → constantCoeff G = 0 → ∃ r : R, constantCoeff ((invDer μ u)^[p] (F * G)) = p * r := by
  first | exact @GlobalTheory.LawDer.constantCoeff_iterate_invDer_mul | exact GlobalTheory.LawDer.constantCoeff_iterate_invDer_mul | (intros; apply GlobalTheory.LawDer.constantCoeff_iterate_invDer_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtLevExistsPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'} {f : S' ⟶ S}

def secPush (m : ObjMap o' o f) (T : Over S') (u : T ⟶ o'.A) : Over.mk (T.hom ≫ f) ⟶ o.A :=
  Over.homMk (u.left ≫ m.φ) (by
    rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w]; rfl)

theorem secPush_left (m : ObjMap o' o f) (T : Over S') (u : T ⟶ o'.A) :
    (secPush m T u).left = u.left ≫ m.φ := rfl

theorem secPush_inj (m : ObjMap o' o f) (T : Over S') {u v : T ⟶ o'.A}
    (h : secPush m T u = secPush m T v) : u = v := by
  have h' := congrArg CommaMorphism.left h
  exact Over.OverMorphism.ext (m.cart.1.hom_ext h' (by rw [Over.w, Over.w]))

theorem secPush_mul (m : ObjMap o' o f) (T : Over S') (u v : T ⟶ o'.A) :
    secPush m T (u * v) = secPush m T u * secPush m T v := by
  apply Over.OverMorphism.ext
  rw [secPush_left]
  exact (m.cart.2 T u v (secPush m T u) (secPush m T v) rfl rfl).symm

theorem secPush_one (m : ObjMap o' o f) (T : Over S') :
    secPush m T 1 = 1 := by
  have h := secPush_mul m T 1 1
  rw [_root_.mul_one] at h
  exact (_root_.mul_eq_left.mp h.symm)

theorem secPush_act (m : ObjMap o' o f) (T : Over S') (u : T ⟶ o'.A) (c : D.O) :
    secPush m T (u ≫ o'.act.act c) = secPush m T u ≫ o.act.act c := by
  apply Over.OverMorphism.ext
  simp only [secPush_left, Over.comp_left, Category.assoc, m.act]

theorem isEtLev_exists_pull : ∀ {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : Obj b N s} {o' : Obj b N s'} {f : S' ⟶ S} (m : ObjMap o' o f) {w0 : Ideal (𝓞 D.F)} {r : ℕ} {lv : D.La → (𝟙_ (Over S) ⟶ o.A)}, IsEtLev o w0 r lv → ∃ lv' : D.La → (𝟙_ (Over S') ⟶ o'.A), IsEtLev o' w0 r lv' ∧ ∀ y, (lv' y).left ≫ m.φ = f ≫ (lv y).left := by
  intro p _ D R _ b N S S' s s' o o' f m w0 r lv hlv
  have hu : ∀ {X : Scheme.{0}} (T : Over X), (toUnit T).left = T.hom := fun T =>
    (Category.comp_id _).symm.trans (Over.w (toUnit T))
  have wα : ∀ y, (f ≫ (lv y).left) ≫ o.A.hom = 𝟙 S' ≫ f := fun y => by
    rw [Category.assoc, Over.w]; simp
  let lv' : D.La → (𝟙_ (Over S') ⟶ o'.A) := fun y =>
    Over.homMk (m.cart.1.lift (f ≫ (lv y).left) (𝟙 S') (wα y)) (m.cart.1.lift_snd _ _ _)
  have hα : ∀ y, (lv' y).left ≫ m.φ = f ≫ (lv y).left := fun y => m.cart.1.lift_fst _ _ _
  have hP1 : ∀ y, secPush m (𝟙_ (Over S')) (lv' y) =
      toUnit (Over.mk ((𝟙_ (Over S')).hom ≫ f)) ≫ lv y := fun y => by
    apply Over.OverMorphism.ext
    rw [secPush_left, hα, Over.comp_left, hu]; simp
  have hP : ∀ (T : Over S') y, secPush m T (toUnit T ≫ lv' y) =
      toUnit (Over.mk (T.hom ≫ f)) ≫ lv y := fun T y => by
    apply Over.OverMorphism.ext
    rw [secPush_left, Over.comp_left, Category.assoc, hα, Over.comp_left, hu, hu]; simp
  refine ⟨lv', ⟨fun x y => ?_, fun c x => ?_, fun x hx => ?_, fun k _ _ x' => ?_⟩, hα⟩
  · apply secPush_inj m
    rw [secPush_mul, hP1, hP1, hP1, hlv.1, MonObj.comp_mul]
  · apply secPush_inj m
    rw [secPush_act, hP1, hP1, hlv.2.1, Category.assoc]
  · apply secPush_inj m
    rw [hP1, secPush_one, hlv.2.2.1 x hx, MonObj.comp_one]
  · obtain ⟨hinj, hsurj⟩ := hlv.2.2.2 k (x' ≫ f)
    refine ⟨fun y hy => hinj y ?_, fun g hg => ?_⟩
    · have h := congrArg (secPush m (Over.mk x')) hy
      rw [hP, secPush_one] at h
      exact h
    · obtain ⟨y, hy⟩ := hsurj (secPush m (Over.mk x') g) (fun c hc => by
        rw [← secPush_act, hg c hc, secPush_one])
      refine ⟨y, secPush_inj m _ ?_⟩
      rw [hP]
      exact hy

end GlobalTheory.UPel.HT.EtLev
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfStalkwiseBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfStalkwiseBaseChange
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.LocGlobSp

def covSurj (S : Scheme.{0}) : MorphismProperty (S.Etale)ᵒᵖ := fun _ _ g => Surjective g.unop.left

instance (S : Scheme.{0}) : (covSurj S).IsStableUnderComposition := by
  constructor
  intro X Y Z f g hf hg
  have : Surjective f.unop.left := hf
  have : Surjective g.unop.left := hg
  exact (inferInstance : Surjective (g.unop.left ≫ f.unop.left))

theorem fst_isIso {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [IsIso g] [HasPullback f g] :
    IsIso (pullback.fst f g) := by
  have w : 𝟙 X ≫ f = (f ≫ inv g) ≫ g := by
    rw [Category.id_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  refine ⟨⟨pullback.lift (𝟙 _) (f ≫ inv g) w, ?_, pullback.lift_fst _ _ _⟩⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, pullback.condition, Category.assoc,
      IsIso.hom_inv_id, Category.comp_id, Category.id_comp]

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E E' : Spc) (α : E ⟶ E') (p : E' ⟶ sch.obj S), Finitary F → QcqsOver (α ≫ p) → QcqsOver p → (∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R ((bcMap α p).app (Over.mk s)) F) → Eqv R α F := by
  intro R _ F S E E' α p hF hq hq' hst
  let Φ : (S.Etale)ᵒᵖ ⥤ Spcᵒᵖ := (Scheme.Etale.forget S ⋙ bc (α ≫ p)).op
  let Φ' : (S.Etale)ᵒᵖ ⥤ Spcᵒᵖ := (Scheme.Etale.forget S ⋙ bc p).op
  let β : Φ' ⟶ Φ := NatTrans.op (Functor.whiskerLeft (Scheme.Etale.forget S) (bcMap α p))
  have hLG := GlobalTheory.T.etale_cohomology_equivalence_of_strictly_henselian_stalks R F S E E' α p hF hq hq' hst
  have hD := GlobalTheory.T.etaleSpace_descent_local_equivalence R F (S.Etale)ᵒᵖ (covSurj S) Φ Φ' β
    (GlobalTheory.refines_of_coAug _ (covSurj S) _ (fun U V g hg =>
      ⟨GlobalTheory.T.smallEtale_cechNerve_resolution_of_surjective R S E (α ≫ p) U V g hg, GlobalTheory.T.smallEtale_cechNerve_resolution_of_surjective R S E' p U V g hg⟩))
    (by
      intro U n x
      obtain ⟨V, h, y, hV, hs, hy⟩ := (hLG ((Scheme.Etale.forget S).obj U.unop) U.unop.prop n).1 x
      let V' : S.Etale := MorphismProperty.Over.mk ⊤ V.hom hV
      let h' : V' ⟶ U.unop := MorphismProperty.Over.homMk h.left (Over.w h) trivial
      exact ⟨op V', h'.op, hs, y, hy⟩)
    (by
      intro U n y hy
      obtain ⟨V, h, hV, hs, hy⟩ := (hLG ((Scheme.Etale.forget S).obj U.unop) U.unop.prop n).2 y hy
      let V' : S.Etale := MorphismProperty.Over.mk ⊤ V.hom hV
      let h' : V' ⟶ U.unop := MorphismProperty.Over.homMk h.left (Over.w h) trivial
      exact ⟨op V', h'.op, hs, hy⟩)
  have h1 := hD (op (Scheme.Etale.mk (𝟙 S)))
  let U0 : Over S := (Scheme.Etale.forget S).obj (Scheme.Etale.mk (𝟙 S))
  have h2 : Eqv R ((bcMap α p).app U0) F := h1
  obtain ⟨hiso, hcomp, -, -⟩ := GlobalTheory.EtC.eqv_basic R F
  have hsq : (bcMap α p).app U0 ≫ pullback.fst p (sch.map U0.hom) =
      pullback.fst (α ≫ p) (sch.map U0.hom) ≫ α := by
    simp only [bcMap, pullback.map]
    set_option synthInstance.maxHeartbeats 200000 in
      exact pullback.lift_fst _ _ _
  haveI hI : IsIso (sch.map U0.hom) := by
    change IsIso (sch.map (𝟙 S))
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  have key : Eqv R ((bcMap α p).app U0 ≫ pullback.fst p (sch.map U0.hom)) F :=
    (hcomp _ _ _ _ _).1 h2 (hiso _ _ _ (fst_isIso p (sch.map U0.hom)))
  rw [hsq] at key
  exact (hcomp _ _ _ _ _).2.1 (hiso _ _ _ (fst_isIso (α ≫ p) (sch.map U0.hom))) key

end GlobalTheory.EtC.LocGlobSp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfStalkwiseBaseChangeStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.equiv_of_stalkwise_base_change : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E E' : Spc) (α : E ⟶ E') (p : E' ⟶ sch.obj S), Finitary F → QcqsOver (α ≫ p) → QcqsOver p → (∀ (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S), IsStalk O s → Eqv R ((bcMap α p).app (Over.mk s)) F) → Eqv R α F := by
  first
  | exact @GlobalTheory.EtC.LocGlobSp.main
  | exact GlobalTheory.EtC.LocGlobSp.main
  | (intros; apply GlobalTheory.EtC.LocGlobSp.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreePartIntegralDifferentialOfCoboundary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreePartIntegralDifferentialOfCoboundary
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Katz.WDer

theorem X_mem_intBy (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] {τ : Type}
    (j : τ) : (X j : MvPowerSeries τ (Fr p k)) ∈ intBy p k τ 1 := by
  classical
  intro β
  refine ⟨if β = Finsupp.single j 1 then 1 else 0, ?_⟩
  rw [coeff_X, one_mul]
  split_ifs <;> simp

theorem lift_mem_intBy (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] {τ : Type}
    (f : MvPowerSeries τ k) : lift p f ∈ intBy p k τ 1 := by
  intro β
  exact ⟨WittVector.teichmuller p (coeff β f), by rw [coeff_lift, one_mul]⟩

theorem coboundaryOne_teichmullerLift_mem_integralDifferential (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (hμ : IsLaw μ)
    (g : MvPowerSeries (Fin d) (Fr p k)) (hg : g ∈ quasiInt p k (Fin d)) :
    cob1 (fun i => lift p (μ i)) g ∈ quasiInt p k (Fin d ⊕ Fin d) := by
  unfold cob1 inL inR
  refine sub_mem (sub_mem ?_ ?_) ?_
  · exact GlobalTheory.T.subst_mem_integralDifferentialSubmodule p k (Fin d) (Fin d ⊕ Fin d) _ g
      (fun i => constantCoeff_lift p (hμ.const i)) (fun i => lift_mem_intBy p k _) hg
  · exact GlobalTheory.T.subst_mem_integralDifferentialSubmodule p k (Fin d) (Fin d ⊕ Fin d) _ g
      (fun i => constantCoeff_X _) (fun i => X_mem_intBy p k _) hg
  · exact GlobalTheory.T.subst_mem_integralDifferentialSubmodule p k (Fin d) (Fin d ⊕ Fin d) _ g
      (fun i => constantCoeff_X _) (fun i => X_mem_intBy p k _) hg

theorem main : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ (N : ℕ) (g h : MvPowerSeries (Fin d) (Fr p k)), 2 ≤ N → g ∈ quasiInt p k (Fin d) → (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α h = 0) → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree = N → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) (g + h)) = algebraMap (WittVector p k) (Fr p k) w) → ∀ (α : Fin d →₀ ℕ) (i : Fin d), α.degree = N → ∃ w : WittVector p k, (α i : Fr p k) * coeff α h = algebraMap (WittVector p k) (Fr p k) w := by
  intro p _ k _ _ _ d μ hμ N g h hN hg hh hcob α i hα
  classical
  by_cases hi : α i = 0
  · exact ⟨0, by simp [hi]⟩
  set β : Fin d →₀ ℕ := α - Finsupp.single i 1 with hβdef
  have hαβ : α = β + Finsupp.single i 1 := by
    ext j
    simp only [hβdef, Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply,
      Finsupp.single_apply]
    split_ifs with hj
    · subst hj; omega
    · omega
  have hβdeg : β.degree + 1 = N := by
    rw [← hα, hαβ, map_add (f := _), Finsupp.degree_single]
  have hβ0 : β ≠ 0 := by
    rintro h0
    rw [h0, map_zero] at hβdeg
    omega
  set γ : Fin d ⊕ Fin d →₀ ℕ := β.mapDomain Sum.inl + Finsupp.single (Sum.inr i) 1 with hγdef
  have hγdeg : γ.degree = N := by
    rw [hγdef, map_add (f := _), Finsupp.degree_mapDomain, Finsupp.degree_single, hβdeg]
  have hγi : γ (Sum.inr i) = 1 := by
    rw [hγdef, Finsupp.add_apply, Finsupp.mapDomain_of_notMem_range, Finsupp.single_eq_same, zero_add]
    rintro ⟨j, hj⟩
    exact Sum.inl_ne_inr hj

  obtain ⟨wg, hwg⟩ := coboundaryOne_teichmullerLift_mem_integralDifferential p k d μ hμ g hg γ (Sum.inr i)
  rw [hγi, Nat.cast_one, one_mul] at hwg
  obtain ⟨wt, hwt⟩ := hcob γ hγdeg

  have hlin : ∀ j (a : Fin d ⊕ Fin d →₀ ℕ), a.degree ≤ 1 →
      coeff a (lift p (μ j)) = coeff a (addLaw (Fr p k) d j) :=
    fun j a ha => (GlobalTheory.T.formal_group_law_linear_coeff_additive p k d μ hμ j a ha).2
  have hlead := ((GlobalTheory.T.coboundary_eq_additive_leading_terms (Fr p k) d (fun j => lift p (μ j)) N hlin).1 h hh γ).2
    hγdeg.le
  have hhom := (GlobalTheory.T.additive_formal_group_coboundary_homogeneous (Fr p k) d N).2.2.2 h β i hβ0
  rw [formalCoboundary_add (fun j => constantCoeff_lift p (hμ.const j)), map_add (f := _), hwg, hlead,
    hhom, ← hαβ] at hwt
  refine ⟨wt - wg, ?_⟩
  have hai : α i = β i + 1 := by
    conv_lhs => rw [hαβ]
    rw [Finsupp.add_apply, Finsupp.single_eq_same]
  rw [map_sub, ← hwt, hai, add_sub_cancel_left]

end GlobalTheory.Katz.WDer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreePartIntegralDifferentialOfCoboundaryStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_part_integralDifferential_of_coboundary : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ (N : ℕ) (g h : MvPowerSeries (Fin d) (Fr p k)), 2 ≤ N → g ∈ quasiInt p k (Fin d) → (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α h = 0) → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree = N → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) (g + h)) = algebraMap (WittVector p k) (Fr p k) w) → ∀ (α : Fin d →₀ ℕ) (i : Fin d), α.degree = N → ∃ w : WittVector p k, (α i : Fr p k) * coeff α h = algebraMap (WittVector p k) (Fr p k) w := by
  first | exact @GlobalTheory.Katz.WDer.main | exact GlobalTheory.Katz.WDer.main | (intros; apply GlobalTheory.Katz.WDer.main <;> assumption)
end
end
