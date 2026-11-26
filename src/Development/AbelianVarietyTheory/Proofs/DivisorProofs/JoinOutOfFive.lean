module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeDividedPowerJetIntegralityOfPublishedStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueConjugationOfEllipticCMTheoremsStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricPeriodZetaStatementsOfJetIntegralityAlgebraStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricPeriodZetaOfJetIntegralityAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricPeriodZetaOfLatticeValueStatements
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricPeriodZetaOfLatticeValueStatements
theorem GlobalTheory.JoinFun.joinOut_of_lat : GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.LatVal.LatIntRam → GlobalTheory.LatVal.LatIntUnr → GlobalTheory.LatVal.LatAlg → GlobalTheory.LatVal.LatConj → GlobalTheory.Mem.LiteralAutomorphy.JoinOut := by
  intro hEM hHCF hSKDR hHT hRam hUnr hLatAlg hLatConj
  have hZD := GlobalTheory.ZetaDenom.zetaDenominators hSKDR
  have hField := GlobalTheory.SqTop.fieldDat
  have hAbs := GlobalTheory.Published.HeckeTateFunctionalEquation.abs hHT
  have hLNe := GlobalTheory.SqTop.lNe_of_functionalEquation hAbs GlobalTheory.HeckeStrip.completedLBoundedInStrips hField
  exact ⟨GlobalTheory.ToricDenomRow.toricDenominator hZD hRam hUnr,
    GlobalTheory.TransportProof.transport_of hHCF hLatAlg hLatConj,
    GlobalTheory.TwistedTransportProof.main (GlobalTheory.LatVal.periodEx_of_mainTheorem hEM) hLatAlg hLatConj, hZD,
    GlobalTheory.SqTop.refl_of_functionalEquation hHT hField hLNe⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricPeriodZetaOfLatticeValueStatementsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricPeriodZeta_of_latticeValue_statements : GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.LatVal.LatIntRam → GlobalTheory.LatVal.LatIntUnr → GlobalTheory.LatVal.LatAlg → GlobalTheory.LatVal.LatConj → GlobalTheory.Mem.LiteralAutomorphy.JoinOut := by
  first | exact @GlobalTheory.JoinFun.joinOut_of_lat | exact GlobalTheory.JoinFun.joinOut_of_lat | (intros; apply GlobalTheory.JoinFun.joinOut_of_lat <;> assumption)
end
end

theorem GlobalTheory.JoinFun.joinOut_of_jetInt : GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.LatJet.JetInt → GlobalTheory.LatVal.LatAlg → GlobalTheory.LatVal.LatConj → GlobalTheory.Mem.LiteralAutomorphy.JoinOut := by
  intro hEM hHCF hSKDR hPZ hHT hJetInt hLatAlg hLatConj
  have hS44 := GlobalTheory.T.cmLattice_derivClassInvariance_of_hecke (GlobalTheory.T.heckeWeightTwoContinuation_of_functionalEquation hPZ)
  exact GlobalTheory.T.toricPeriodZeta_of_latticeValue_statements hEM hHCF hSKDR hHT (GlobalTheory.T.latticeValueIntegrality_ramified_of_expansion hS44 (GlobalTheory.JetExp.expansion_of_jetInt hJetInt))
    (GlobalTheory.T.latticeValueIntegrality_unramified_of_jetIntegrality hS44 hJetInt) hLatAlg hLatConj
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricPeriodZetaStatements_of_jetIntegrality_algebraicity : GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.LatJet.JetInt → GlobalTheory.LatVal.LatAlg → GlobalTheory.LatVal.LatConj → GlobalTheory.Mem.LiteralAutomorphy.JoinOut := by
  first | exact @GlobalTheory.JoinFun.joinOut_of_jetInt | exact GlobalTheory.JoinFun.joinOut_of_jetInt | (intros; apply GlobalTheory.JoinFun.joinOut_of_jetInt <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIsAlgebraicOfEllipticCMTheorems
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QAllIsAlgebraicHfunTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetAlgebraicQCoefficients
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertDiagonalRestrictionCoeffIsAlgebraic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertDiagonalRestrictionCoeffIsAlgebraic
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma coeff_mul_mem_algebraicClosure {f g : PowerSeries ℂ}
    (hf : ∀ n, PowerSeries.coeff n f ∈ algebraicClosure ℚ ℂ)
    (hg : ∀ n, PowerSeries.coeff n g ∈ algebraicClosure ℚ ℂ) (n : ℕ) :
    PowerSeries.coeff n (f * g) ∈ algebraicClosure ℚ ℂ := by
  rw [PowerSeries.coeff_mul]
  exact sum_mem fun p _ ↦ mul_mem (hf _) (hg _)

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma coeff_pow_mem_algebraicClosure {f : PowerSeries ℂ}
    (hf : ∀ n, PowerSeries.coeff n f ∈ algebraicClosure ℚ ℂ) (e : ℕ) :
    ∀ n, PowerSeries.coeff n (f ^ e) ∈ algebraicClosure ℚ ℂ := by
  induction e with
  | zero =>
    intro n
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  | succ e ih =>
    rw [pow_succ]
    exact coeff_mul_mem_algebraicClosure ih hf

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma isAlgebraic_exp_two_pi_I_mul_rat (q : ℚ) :
    IsAlgebraic ℚ (Complex.exp (2 * ↑Real.pi * Complex.I * (q : ℂ))) := by
  refine (IsIntegral.of_pow q.den_pos ?_).isAlgebraic
  have h : Complex.exp (2 * ↑Real.pi * Complex.I * (q : ℂ)) ^ q.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have hq : (q : ℂ) * q.den = q.num := by exact_mod_cast Rat.mul_den_eq_num q
    have hmul : (q.den : ℂ) * (2 * ↑Real.pi * Complex.I * (q : ℂ)) =
        (q.num : ℂ) * (2 * ↑Real.pi * Complex.I) := by
      linear_combination (2 * ↑Real.pi * Complex.I) * hq
    rw [hmul, Complex.exp_int_mul_two_pi_mul_I]
  rw [h]
  exact isIntegral_one

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma isAlgebraic_realEmbedding_apply {F : Type} [Field F] [NumberField F]
    (i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) (y : F) : IsAlgebraic ℚ ((i y : ℝ) : ℂ) :=
  (Algebra.IsAlgebraic.isAlgebraic y).algHom (Complex.ofRealHom.comp i).toRatAlgHom

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma ecoef_mem_algebraicClosure_of_isCoef {F : Type} [Field F] [NumberField F] {k : ℕ}
    {𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} {a₀ : ℂ} {a : F → ℂ}
    (ha : _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a) (ha₀ : IsAlgebraic ℚ a₀) (N : ℕ)
    (x : F) (μ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (n : ℕ) :
    _root_.GlobalTheory.HilbFam.ecoef N a x μ n ∈ algebraicClosure ℚ ℂ := by
  unfold _root_.GlobalTheory.HilbFam.ecoef
  refine finsum_mem_induction _ (zero_mem _) (fun _ _ ↦ add_mem) fun ξ _ ↦ ?_
  refine mul_mem (mul_mem ?_ ?_) (prod_mem fun i _ ↦ pow_mem ?_ _)
  · rw [mem_algebraicClosure_iff]
    by_cases hξ : ξ = 0
    · rw [hξ, ha.1]
      exact ha₀
    · obtain ⟨m, hm⟩ := ha.2.1 ξ hξ
      rw [hm]
      exact isAlgebraic_int _
  · rw [mem_algebraicClosure_iff]
    unfold _root_.GlobalTheory.HilbFam.eTr
    exact isAlgebraic_exp_two_pi_I_mul_rat _
  · rw [mem_algebraicClosure_iff]
    exact isAlgebraic_realEmbedding_apply i ξ


open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.hser_coeff_isAlgebraic : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (s N : ℕ) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (c : ℕ → ℂ) (n : ℕ), k = 2 * s → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a → IsAlgebraic ℚ a₀ → (∀ m, IsAlgebraic ℚ (c m)) → IsAlgebraic ℚ (PowerSeries.coeff n (_root_.GlobalTheory.HilbFam.hser k N 𝔞 a x κ c)) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x s N κ c n hk ha ha₀ hc
  rw [← mem_algebraicClosure_iff]
  unfold _root_.GlobalTheory.HilbFam.hser
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, map_sum, smul_eq_mul]
  refine mul_mem ?_ (sum_mem fun μ _ ↦ mul_mem (intCast_mem _ _) ?_)
  · rw [hk, _root_.GlobalTheory.HilbFam.omegaFactor_pow_two_mul]
    exact SubfieldClass.ratCast_mem _ _
  · refine coeff_mul_mem_algebraicClosure
      (coeff_pow_mem_algebraicClosure (fun m ↦ ?_) _) (fun m ↦ ?_) n
    · rw [PowerSeries.coeff_mk, mem_algebraicClosure_iff]
      exact hc m
    · rw [PowerSeries.coeff_mk]
      exact ecoef_mem_algebraicClosure_of_isCoef ha ha₀ N x μ m

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertDiagonalRestrictionCoeffIsAlgebraicStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertDiagonalRestriction_coeff_isAlgebraic : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (s N : ℕ) (κ : Emb F → ℕ) (c : ℕ → ℂ) (n : ℕ), k = 2 * s → IsCoef k 𝔞 𝔟 a₀ a → IsAlgebraic ℚ a₀ → (∀ m, IsAlgebraic ℚ (c m)) → IsAlgebraic ℚ (PowerSeries.coeff n (hser k N 𝔞 a x κ c)) := by
  first | exact @GlobalTheory.HilbFam.hser_coeff_isAlgebraic | exact GlobalTheory.HilbFam.hser_coeff_isAlgebraic | (intros; apply GlobalTheory.HilbFam.hser_coeff_isAlgebraic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetAlgebraicQCoefficients
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem qAll_isAlgebraic_hfun : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F],
    2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L →
    ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (κ : Emb F → ℕ) (Ch : ℍ → ℂ),
    QAll (IsAlgebraic ℚ) N Ch → QAll (IsAlgebraic ℚ) N (hfun (2 * s) L κ Ch) := by
  intro hE F _ _ _ hf s N L hs hN hL z hz κ Ch hCh
  obtain ⟨c, hc, halg⟩ := hCh
  obtain ⟨𝔞, 𝔟, x, rfl⟩ := GlobalTheory.T.exists_split_of_hilbertLatticeHasLevel F N L hN hL
  obtain ⟨Z, a, hZ, ha⟩ := GlobalTheory.T.exists_hilbertEisenstein_fourierCoeffFamily hE F hf 𝔞 𝔟 s hs
  have hconst := GlobalTheory.T.partialZeta_constTerm_eq_rational_value F (2 * s) z _ Z (by omega) hz hZ
  have ha₀ : IsAlgebraic ℚ ((2 : ℂ)⁻¹ ^ Module.finrank ℚ F * Z (1 - ((2 * s : ℕ) : ℂ))) := by
    rw [hconst]
    exact isAlgebraic_algebraMap (R := ℚ) (A := ℂ) _
  exact ⟨_, GlobalTheory.T.hasQExpansionOfLevel_hilbertEisensteinQuasiPeriodJet F (2 * s) 𝔞 𝔟 _ a x N κ Ch c hN (even_two_mul s) ha hL hc,
    fun n ↦ GlobalTheory.T.hilbertDiagonalRestriction_coeff_isAlgebraic F (2 * s) 𝔞 𝔟 _ a x s N κ c n rfl ha ha₀ halg⟩

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetAlgebraicQCoefficientsStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_eisenstein_jet_algebraic_q_coefficients : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (κ : Emb F → ℕ) (Ch : ℍ → ℂ), QAll (IsAlgebraic ℚ) N Ch → QAll (IsAlgebraic ℚ) N (hfun (2 * s) L κ Ch) := by
  first | exact @GlobalTheory.HilbFam.qAll_isAlgebraic_hfun | exact GlobalTheory.HilbFam.qAll_isAlgebraic_hfun | (intros; apply GlobalTheory.HilbFam.qAll_isAlgebraic_hfun <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionIsAlgebraicWeierstrassTorsion
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionIsAlgebraicWeierstrassTorsion
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem isAlgebraic_of_isIntegral_natCast_mul (n : ℕ) (hn : n ≠ 0) (z : ℂ)
    (h : IsIntegral ℤ ((n : ℂ) * z)) : IsAlgebraic ℚ z := by
  have h1 : IsIntegral ℚ ((n : ℂ) * z) := h.tower_top
  have h2 : IsIntegral ℚ (algebraMap ℚ ℂ ((n : ℚ)⁻¹)) := isIntegral_algebraMap
  have h3 := h2.mul h1
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have : algebraMap ℚ ℂ ((n : ℚ)⁻¹) * ((n : ℂ) * z) = z := by
    rw [map_inv₀, map_natCast, ← mul_assoc, inv_mul_cancel₀ hn', one_mul]
  rw [this] at h3
  exact h3.isAlgebraic

theorem qAll_isAlgebraic_torsion : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N),
    QAll (IsAlgebraic ℚ) N (wp N x) ∧ QAll (IsAlgebraic ℚ) N (wpd N x) ∧
      (x ≠ 0 → QAll (IsAlgebraic ℚ) N (wB N x)) := by
  intro N _ x
  have hN : N ≠ 0 := NeZero.ne N
  have hx : N • x = 0 := by
    funext i
    simp [nsmul_eq_mul]
  have hc := fun k => GlobalTheory.T.isIntegral_weierstrassTorsion_qCoefficients N N x k (Nat.pos_of_ne_zero hN) hx
  refine ⟨⟨cP N x, GlobalTheory.T.hasQExpansion_normalizedWeierstrassPTorsion N x, fun k => ?_⟩, ⟨cD N x, GlobalTheory.T.hasQExpansion_normalizedDerivWeierstrassPTorsion N x, fun k => ?_⟩,
    fun h0 => ⟨cB N x, GlobalTheory.T.weierstrass_division_value_q_expansion N x h0, fun k => ?_⟩⟩
  · refine isAlgebraic_of_isIntegral_natCast_mul (12 * N ^ 2) (by positivity) _ ?_
    have := (hc k).2.2.1
    push_cast
    exact this
  · refine isAlgebraic_of_isIntegral_natCast_mul (N ^ 3) (by positivity) _ ?_
    have := (hc k).2.1
    push_cast
    exact this
  · refine isAlgebraic_of_isIntegral_natCast_mul (N ^ 2) (by positivity) _ ?_
    have := (hc k).1
    push_cast
    exact this

end GlobalTheory.WpFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionIsAlgebraicWeierstrassTorsionStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.qExpansion_isAlgebraic_weierstrassTorsion : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), QAll (IsAlgebraic ℚ) N (wp N x) ∧ QAll (IsAlgebraic ℚ) N (wpd N x) ∧ (x ≠ 0 → QAll (IsAlgebraic ℚ) N (wB N x)) := by
  first | exact @GlobalTheory.WpFam.qAll_isAlgebraic_torsion | exact GlobalTheory.WpFam.qAll_isAlgebraic_torsion | (intros; apply GlobalTheory.WpFam.qAll_isAlgebraic_torsion <;> assumption)
end
end

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam

namespace GlobalTheory.HilbFam

theorem qAll_isAlgebraic_hfun_twist : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (κ : Emb F → ℕ) (y : Fin 2 → ZMod N), y ≠ 0 → ∀ α : GL (Fin 2) (ZMod N), QAll (IsAlgebraic ℚ) N (hfun (2 * s) (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ (wB N (vmul y (α)))) := by
  intro hE F _ _ _ hF s N _ L hs hL z hz κ y hy α
  have hy' : vmul y α ≠ 0 := fun h => hy (((GlobalTheory.T.modularGroup_rowVec_and_conj_rightActions N).2.2.2.2.1 y α).1 h)
  exact GlobalTheory.T.hilbert_eisenstein_jet_algebraic_q_coefficients hE F hF s N _ hs (Nat.pos_of_ne_zero (NeZero.ne N)) (GlobalTheory.T.hilbertLatticeTwist_hasLevel F N L _ hL) z hz κ _
    ((GlobalTheory.T.qExpansion_isAlgebraic_weierstrassTorsion N (vmul y α)).2.2 hy')

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsSideAlt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicNormalizedWeierstrassValuesCm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicNormalizedWeierstrassValuesCm
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.AlgebraicitySecondEisenstein

theorem main : ∀ (L : PeriodPair) (β Ω : ℂ), MulStable L β → β.im ≠ 0 → Ω ^ 12 = latDisc L →
    IsAlgebraic ℚ (s2 L / Ω ^ 2) ∧ ∀ (M : ℕ) (P : ℂ), 0 < M → (M : ℂ) * P ∈ L.lattice →
      IsAlgebraic ℚ (L.weierstrassP P / Ω ^ 2) ∧ IsAlgebraic ℚ (L.derivWeierstrassP P / Ω ^ 3) := by
  intro L β Ω hst him hΩ
  have alg : ∀ x : ℂ, IsAlgebraic ℚ x ↔ x ∈ algebraicClosure ℚ ℂ := fun x => mem_algebraicClosure_iff.symm
  have intAlg : ∀ x : ℂ, IsIntegral ℤ x → x ∈ algebraicClosure ℚ ℂ := fun x hx =>
    (alg x).1 (hx.tower_top (A := ℚ)).isAlgebraic
  have natMem : ∀ k : ℕ, (k : ℂ) ∈ algebraicClosure ℚ ℂ := fun k => natCast_mem _ k
  have part2 : ∀ (M : ℕ) (P : ℂ), 0 < M → (M : ℂ) * P ∈ L.lattice →
      IsAlgebraic ℚ (L.weierstrassP P / Ω ^ 2) ∧ IsAlgebraic ℚ (L.derivWeierstrassP P / Ω ^ 3) := by
    intro M P hM hP
    obtain ⟨h1, -⟩ := GlobalTheory.T.isIntegral_weierstrassP_torsion_nonreal_multiplier L β Ω M hst him hΩ hM
    obtain ⟨i1, i2⟩ := h1 P hP
    have a1 := intAlg _ i1
    have a2 := intAlg _ i2
    have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    rw [mul_div_assoc] at a1 a2
    have c1 : (12 * (M : ℂ) ^ 2) = ((12 * M ^ 2 : ℕ) : ℂ) := by push_cast; ring
    have c2 : ((M : ℂ) ^ 3) = ((M ^ 3 : ℕ) : ℂ) := by push_cast; ring
    have n1 : (12 * (M : ℂ) ^ 2) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero _ hMc)
    have n2 : ((M : ℂ) ^ 3) ≠ 0 := pow_ne_zero _ hMc
    constructor
    · rw [alg]
      have := div_mem a1 (c1 ▸ natMem (12 * M ^ 2))
      rwa [mul_div_cancel_left₀ _ n1] at this
    · rw [alg]
      have := div_mem a2 (c2 ▸ natMem (M ^ 3))
      rwa [mul_div_cancel_left₀ _ n2] at this
  refine ⟨?_, part2⟩
  have hβ0 : β ≠ 0 := by rintro rfl; simp at him
  obtain ⟨S, hS⟩ := kernel_reps_exist L β hβ0 hst
  have hcard := kernel_reps_card L β S hβ0 hst hS
  obtain ⟨t, n, ht, hn, hq⟩ := mul_stable_integral L β hst
  have hs2 := cm_s2 L β S hst him hS
  have hconj : MulStable L (conj β) := fun ω hω => by
    have e : conj β * ω = t • ω - β * ω := by rw [zsmul_eq_mul, ← ht]; ring
    rw [e]
    exact sub_mem (Submodule.smul_mem _ t hω) (hst ω hω)
  have hM : ((S.card + 1 : ℕ) : ℂ) = conj β * β := by
    rw [← Complex.normSq_eq_conj_mul_self]
    have := congrArg (fun r : ℝ => (r : ℂ)) hcard
    push_cast at this ⊢
    exact this
  have hP : ∀ P ∈ S, L.weierstrassP P / Ω ^ 2 ∈ algebraicClosure ℚ ℂ := fun P hP => by
    have hmem : ((S.card + 1 : ℕ) : ℂ) * P ∈ L.lattice := by
      rw [hM, mul_assoc]; exact hconj _ (hS.1 P hP).1
    exact (alg _).1 (part2 _ P (Nat.succ_pos _) hmem).1
  have hβint : IsIntegral ℤ β := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C n, ?_, ?_⟩
    · monicity!
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
        Polynomial.eval₂_X, Polynomial.eval₂_C]
      simpa using hq
  have hβm := intAlg _ hβint
  have hcm : conj β ∈ algebraicClosure ℚ ℂ := by
    have e : conj β = (t : ℂ) - β := by rw [← ht]; ring
    rw [e]; exact sub_mem (intCast_mem _ t) hβm
  rw [alg, hs2, div_div, mul_comm (β * _), ← div_div, Finset.sum_div]
  exact div_mem (sum_mem hP) (mul_mem hβm (sub_mem hβm hcm))

end GlobalTheory.AlgebraicitySecondEisenstein
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicNormalizedWeierstrassValuesCmStatement
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_normalized_weierstrass_values_cm : ∀ (L : PeriodPair) (β Ω : ℂ), MulStable L β → β.im ≠ 0 → Ω ^ 12 = latDisc L → IsAlgebraic ℚ (s2 L / Ω ^ 2) ∧ ∀ (M : ℕ) (P : ℂ), 0 < M → (M : ℂ) * P ∈ L.lattice → IsAlgebraic ℚ (L.weierstrassP P / Ω ^ 2) ∧ IsAlgebraic ℚ (L.derivWeierstrassP P / Ω ^ 3) := by
  first | exact @GlobalTheory.AlgebraicitySecondEisenstein.main | exact GlobalTheory.AlgebraicitySecondEisenstein.main | (intros; apply GlobalTheory.AlgebraicitySecondEisenstein.main <;> assumption)
end
end

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.AlgTau

theorem main : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (Λ : PeriodPair) (c Ω : ℂ) (τ : ℍ), 0 < d → δ ^ 2 = -(d : K) → GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 𝔞 Λ → IsTauOf Λ c τ → Ω ^ 12 = latDisc Λ → (Ω * c / (2 * Real.pi * Complex.I)) ^ 12 = DD τ ∧ IsAlgebraic ℚ (jT τ) ∧ IsAlgebraic ℚ (G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2) ∧ ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N), IsAlgebraic ℚ (wp N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2) := by
  intro K _ _ d δ ι 𝔞 Λ c Ω τ hd hδ hlat htau hΩ
  obtain ⟨-, hmul, him, -⟩ := GlobalTheory.T.fractionalIdealLattice_has_nonreal_multiplier K d δ ι 𝔞 Λ hd hδ hlat
  have hval := GlobalTheory.T.eisensteinWeierstrass_values_lattice_tau Λ c Ω τ htau
  have halg := GlobalTheory.T.algebraic_normalized_weierstrass_values_cm Λ (ι δ) Ω hmul him hΩ
  refine ⟨(GlobalTheory.QFam.jT_eq_and_pow_twelve_eq_DD Λ c τ htau).2 Ω hΩ, ?_, ?_, ?_⟩
  · have hj : IsIntegral ℤ (jT τ) := GlobalTheory.T.isIntegral_jInvariant_of_complexMultiplication Λ c τ (ι δ) htau hmul him
    exact (hj.tower_top (A := ℚ)).isAlgebraic
  · rw [hval.1]; exact halg.1
  · intro N _ x
    rw [(hval.2 N x).1]
    have hN : (N : ℂ) * (c * tors N τ x) ∈ Λ.lattice := by
      have h1 := ((GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf Λ c τ htau).1 ((N : ℂ) * tors N τ x)).2
        ((GlobalTheory.T.torsionPointOfLatticeTau_lattice_membership N τ).2.2.2.1 x)
      simpa [mul_left_comm] using h1
    exact (halg.2 N (c * tors N τ x) (Nat.pos_of_ne_zero (NeZero.ne N)) hN).1

end GlobalTheory.AlgTau
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfIsIntegralAlgebraicNumbers
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem isAlgebraic_of_isIntegral_algebraicNumbers {x : ℂ}
    (hx : IsIntegral (integralClosure ℚ ℂ).toSubring x) : IsAlgebraic ℚ x := by
  have hx' : IsIntegral (integralClosure ℚ ℂ) x := hx
  exact (isIntegral_trans (R := ℚ) (A := integralClosure ℚ ℂ) x hx').isAlgebraic

theorem fam_value_isAlgebraic : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ) (f : ι → ℍ → ℂ) (τ₀ : ℍ) (Ω : ℂ), 0 < N → ActBij act → IsFam act w f → (∀ i, QAll (IsAlgebraic ℚ) N (f i)) → IsAlgebraic ℚ (jT τ₀) → Ω ^ 12 = DD τ₀ → ∀ i, IsAlgebraic ℚ (f i τ₀ / Ω ^ w) := by
  intro ι _ act w N f τ₀ Ω hN hb hf hq hj hΩ i
  refine isAlgebraic_of_isIntegral_algebraicNumbers
    (GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow ι act w N f (integralClosure ℚ ℂ).toSubring τ₀ Ω hN hb hf (fun k => ?_) ?_ hΩ i)
  · obtain ⟨a, ha, hal⟩ := hq k
    exact ⟨a, ha, fun n => (hal n).isIntegral⟩
  · exact isIntegral_algebraMap (R := (integralClosure ℚ ℂ).toSubring) (A := ℂ)
      (x := ⟨jT τ₀, hj.isIntegral⟩)

end GlobalTheory.QFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIsAlgebraicOfEllipticCMTheorems
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal UpperHalfPlane ReciprocityTheory.ChartRestriction.L1
open GlobalTheory.HilbFam GlobalTheory.QFam GlobalTheory.WpFam
open scoped UpperHalfPlane MatrixGroups

namespace GlobalTheory.RoadELatAlg

theorem isAlgebraic_of_sq_eq_ratCast {x : ℂ} (q : ℚ) (h : x ^ 2 = (q : ℂ)) : IsAlgebraic ℚ x := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.C q, ?_, ?_⟩
  · exact Polynomial.X_pow_sub_C_ne_zero (by norm_num) q
  · simp [h]

theorem exists_theta {K : Type} [Field K] [NumberField K] (ι : K →+* ℂ) (Λ : PeriodPair)
    (hΛ : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.IsLatOf ι 1 Λ) (c : ℂ) (τ : ℍ) (hτ : IsTauOf Λ c τ) :
    ∃ θ : K, ι θ = (τ : ℂ) ∧ IsAlgebraic ℚ c := by
  have hmem : ∀ z : ℂ, z ∈ Λ.lattice → ∃ a : K, ι a = z := by
    intro z hz
    have : z ∈ (Λ.lattice : Set ℂ) := hz
    rw [hΛ] at this
    obtain ⟨a, -, ha⟩ := this
    exact ⟨a, ha⟩
  obtain ⟨a, ha⟩ := hmem c ((hτ.2 c).2 ⟨0, 1, by simp⟩)
  obtain ⟨b, hb⟩ := hmem (c * τ) ((hτ.2 _).2 ⟨1, 0, by simp⟩)
  have hc : c ≠ 0 := hτ.1
  refine ⟨b / a, ?_, ?_⟩
  · rw [map_div₀, ha, hb]; field_simp
  · rw [← ha]; exact (Algebra.IsAlgebraic.isAlgebraic a).algHom ι.toRatAlgHom

theorem term_div_eq (r Y H ω : ℂ) (a w W : ℕ) (h : W = 2 * a + w) :
    r * Y ^ a * H / ω ^ W = r * ((Y / ω ^ 2) ^ a * (H / ω ^ w)) := by
  subst h
  rw [pow_add, pow_mul, div_pow]
  ring

theorem coord_id (c0 S0 D Ω c cW P pi im r p sg : ℂ) (W K : ℕ) (hsg : sg ≠ 0) (hD : D = cW * (sg * P) * S0)
    (hc0 : c0 = cW * P * (2 * pi / r) ^ K) (hΩ : Ω ≠ 0) (hc : c ≠ 0) (hp : p ≠ 0) (him : im ≠ 0) (hr : r ≠ 0) :
    c0 * S0 / Ω ^ W = sg⁻¹ * (2 * im / r) ^ K * c ^ W * (D * (pi / im) ^ K / p ^ W / (Ω * c / p) ^ W) := by
  have h2 : (2 * im / r) ^ K * (pi / im) ^ K = (2 * pi / r) ^ K := by
    rw [← mul_pow]; congr 1; field_simp
  have h3 : c ^ W / p ^ W / (Ω * c / p) ^ W = 1 / Ω ^ W := by
    rw [div_pow, mul_pow]; field_simp
  calc c0 * S0 / Ω ^ W = (sg⁻¹ * sg) * (cW * P * S0) * ((2 * im / r) ^ K * (pi / im) ^ K) *
        (c ^ W / p ^ W / (Ω * c / p) ^ W) := by
          rw [inv_mul_cancel₀ hsg, h2, h3, hc0]; ring
    _ = _ := by rw [hD]; ring

theorem latAlg_of_siegelKlingen : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation →
    GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.LatVal.LatAlg := by
  intro hSKDR hPZ _ _
  intro K _ _ d δ ι hK hd hδ Λ₀ Ω₀ hΛ hΩ E _ _ _ _ I _ φ s 𝔣 Q hDat κ y S hS
  classical
  obtain ⟨hUn, hCM, hφι, hs, h𝔣, hQ⟩ := hDat
  have hf2 : 2 ≤ Module.finrank ℚ (maximalRealSubfield E) := GlobalTheory.LatAlgebraic.two_le_finrank hUn
  have hc0 : condQ 𝔣 Q ≠ ⊥ := by
    show 𝔣 * ∏ q ∈ Q, q.asIdeal ≠ 0
    exact mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)
  have hΩ0 : Ω₀ ≠ 0 := by
    rintro rfl
    exact latDisc_ne_zero Λ₀ (by rw [← hΩ]; simp)
  have hW2 := GlobalTheory.T.heckeWeightTwoContinuation_of_functionalEquation hPZ
  have hSt := GlobalTheory.T.cmLattice_derivClassInvariance_of_hecke hW2
  have hEis := GlobalTheory.T.hilbertEisensteinExpansion_of_lipschitz_hecke_zeta GlobalTheory.T.lipschitz_formula_totally_real_poisson hW2 hPZ
  obtain ⟨⟨z, hz⟩, -⟩ := GlobalTheory.T.partialZetaDenominatorsCMField_of_siegelKlingenDeligneRibet hSKDR E s hs
  obtain ⟨⟨g, hg⟩, hD⟩ := (((hSt E I φ hf2 hCM).1 s hs).1 (condQ 𝔣 Q) y hc0).1
  obtain ⟨u, hu⟩ := GlobalTheory.LatAlgebraic.exists_list_count κ
  have hDg := ((hD g hg).2 κ u hu).1 S hS
  obtain ⟨c, τ, hτ⟩ := latTau Λ₀
  obtain ⟨θ, hθτ, hcalg⟩ := exists_theta ι Λ₀ hΛ c τ hτ
  have hc : c ≠ 0 := hτ.1
  have hφθ : ∀ i, φ i (algebraMap K E θ) = (τ : ℂ) := by
    intro i; rw [← RingHom.comp_apply, hφι i, hθτ]
  obtain ⟨e, he⟩ := GlobalTheory.CMTypeEmb.exists_equiv E I φ hCM
  have hcard : Fintype.card I = Module.finrank ℚ (maximalRealSubfield E) := GlobalTheory.LatAlgebraic.card_eq_finrank hCM
  have hI : Nonempty I := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨i₀⟩ := hI
  have hθF : algebraMap K E θ ∉ Set.range (fun x : maximalRealSubfield E => (x : E)) := by
    rintro ⟨x, hx⟩
    have h1 := he i₀ x
    change (x : E) = _ at hx
    rw [hx, hφθ i₀] at h1
    have h2 := congrArg Complex.im h1
    simp only [Complex.ofReal_im] at h2
    exact τ.im_pos.ne' h2
  obtain ⟨n, N, L, hn, hN, hN2, hL, hLΛ⟩ := GlobalTheory.RoadE.exists_level E (algebraMap K E θ) (condQ 𝔣 Q) y 2 hc0 hθF (by norm_num)
  have hN2' : 2 ≤ N := Nat.le_of_dvd hN hN2
  haveI : NeZero N := ⟨by omega⟩
  haveI : Fact (1 < N) := ⟨by omega⟩
  let y₁ : Fin 2 → ZMod N := ![1, 0]
  have hy₁ : y₁ ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [y₁] at this
  have hval := GlobalTheory.HilbFam.eValue_derivs hEis E I φ e (algebraMap K E θ) τ (lattice (condQ 𝔣 Q) y) L n s N g κ u
    (wB N y₁) hf2 hs hN hL he hφθ hn hLΛ hg hu
  obtain ⟨hωDD, hj, hG2, hwp⟩ := GlobalTheory.AlgTau.main K d δ ι 1 Λ₀ c Ω₀ τ hd hδ hΛ hτ hΩ

  set ω : ℂ := Ω₀ * c / (2 * Real.pi * Complex.I) with hω
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2piI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [hpi, Complex.I_ne_zero]
  have hω0 : ω ≠ 0 := div_ne_zero (mul_ne_zero hΩ0 hc) h2piI
  have hH : ∀ μ : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb (maximalRealSubfield E) → ℕ,
      IsAlgebraic ℚ (GlobalTheory.HilbFam.hfun (2 * s) L μ (wB N y₁) τ / ω ^ GlobalTheory.HilbFam.wt (2 * s) μ) := by
    intro μ
    have h := GlobalTheory.QFam.fam_value_isAlgebraic (GL (Fin 2) (ZMod N)) (GlobalTheory.WpFam.gact N 1) (GlobalTheory.HilbFam.wt (2 * s) μ) N
      (fun α ↦ GlobalTheory.HilbFam.hfun (2 * s) (GlobalTheory.HilbFam.twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) μ (wB N (GlobalTheory.WpFam.vmul y₁ α)))
      τ ω (by omega) (((GlobalTheory.T.modularGroup_rowVec_and_conj_rightActions N).2.1 1).actBij)
      (GlobalTheory.HilbFam.isFam_hfun_GL hEis (maximalRealSubfield E) hf2 s N L hs hL y₁ μ)
      (fun α ↦ GlobalTheory.HilbFam.qAll_isAlgebraic_hfun_twist hEis (maximalRealSubfield E) hf2 s N L hs hL z hz μ y₁ hy₁ α)
      hj hωDD 1
    simpa only [Units.val_one, GlobalTheory.HilbFam.twist_one_of_hasLevel _ N L hL, (GlobalTheory.T.modularGroup_rowVec_and_conj_rightActions N).2.2.2.1] using h
  have hX : IsAlgebraic ℚ ((((Real.pi / τ.im : ℝ) : ℂ) / (2 * Real.pi * Complex.I) ^ 2 - wB N y₁ τ) / ω ^ 2) := by
    rw [GlobalTheory.wB_nonhol_correction, neg_div, add_div]
    exact ((hG2.add (hwp N y₁))).neg
  set f := Module.finrank ℚ (maximalRealSubfield E) with hf
  set k := ∑ i, κ i with hk
  set P : ℂ := 2 * Real.pi * Complex.I with hP
  set Y : ℂ := ((Real.pi / τ.im : ℝ) : ℂ) / P ^ 2 - wB N y₁ τ with hY
  set κ' : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb (maximalRealSubfield E) → ℕ := fun j ↦ κ (e.symm j) with hκ'
  have hsum' : ∑ j, κ' j = k := Equiv.sum_comp e.symm κ
  have hA : ∀ x : ℂ, IsAlgebraic ℚ x → x ∈ algebraicClosure ℚ ℂ := fun x h ↦ mem_algebraicClosure_iff.2 h

  have hRalg : IsAlgebraic ℚ (((n : ℂ) ^ (2 * s * f) * ∑ μ ∈ Finset.Iic κ',
      ((∏ j, GlobalTheory.HilbFam.rco (2 * s) (κ' j) (μ j) : ℤ) : ℂ) * Y ^ (∑ j, (κ' j - μ j)) *
        GlobalTheory.HilbFam.hfun (2 * s) L μ (wB N y₁) τ) / ω ^ (2 * s * f + 2 * k)) := by
    have key : ((n : ℂ) ^ (2 * s * f) * ∑ μ ∈ Finset.Iic κ',
        ((∏ j, GlobalTheory.HilbFam.rco (2 * s) (κ' j) (μ j) : ℤ) : ℂ) * Y ^ (∑ j, (κ' j - μ j)) *
          GlobalTheory.HilbFam.hfun (2 * s) L μ (wB N y₁) τ) / ω ^ (2 * s * f + 2 * k) =
        (n : ℂ) ^ (2 * s * f) * ∑ μ ∈ Finset.Iic κ', ((∏ j, GlobalTheory.HilbFam.rco (2 * s) (κ' j) (μ j) : ℤ) : ℂ) *
          ((Y / ω ^ 2) ^ (∑ j, (κ' j - μ j)) * (GlobalTheory.HilbFam.hfun (2 * s) L μ (wB N y₁) τ / ω ^ GlobalTheory.HilbFam.wt (2 * s) μ)) := by
      rw [mul_div_assoc, Finset.sum_div]
      refine congrArg _ (Finset.sum_congr rfl fun μ hμ ↦ ?_)
      have hle : μ ≤ κ' := Finset.mem_Iic.1 hμ
      have hexp : 2 * s * f + 2 * k = 2 * (∑ j, (κ' j - μ j)) + GlobalTheory.HilbFam.wt (2 * s) μ := by
        have h1 : ∑ j, (κ' j - μ j) + ∑ j, μ j = ∑ j, κ' j := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ ↦ Nat.sub_add_cancel (hle j)
        change 2 * s * f + 2 * k = 2 * (∑ j, (κ' j - μ j)) + (2 * s * f + 2 * ∑ j, μ j)
        omega
      exact term_div_eq _ _ _ _ _ _ _ hexp
    rw [key, ← mem_algebraicClosure_iff]
    refine mul_mem (pow_mem (natCast_mem _ _) _) (sum_mem fun μ _ ↦ mul_mem (intCast_mem _ _)
      (mul_mem (pow_mem (hA _ hX) _) (hA _ (hH μ))))
  have hRalg' : IsAlgebraic ℚ (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0 * ((Real.pi / τ.im : ℝ) : ℂ) ^ k / P ^ (2 * s * f + 2 * k) /
      ω ^ (2 * s * f + 2 * k)) := by
    rw [hval]; exact hRalg
  rw [Complex.ofReal_div] at hRalg'
  have hsd : ((Real.sqrt d : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
    exact_mod_cast this.ne'
  have him : ((τ.im : ℝ) : ℂ) ≠ 0 := by exact_mod_cast τ.im_pos.ne'
  have hcW : (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt
      have h1 : (0 : ℝ) < |(discr (maximalRealSubfield E) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero _)
      exact mul_pos (pow_pos (by exact_mod_cast Nat.factorial_pos _) _) (Real.rpow_pos_of_pos h1 _)
    exact_mod_cast this.ne'
  have hP' : (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < ∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j) :=
      Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => by positivity
    exact_mod_cast this.ne'
  have hsgn : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hC0 : ((C0 E d (2 * s) κ : ℝ) : ℂ) = (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.cWt E (2 * s) : ℂ) *
      (((∏ i, ∏ j ∈ Finset.range (κ i), (((2 * s : ℕ) : ℝ) + j)) : ℝ) : ℂ) *
      (2 * (Real.pi : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ k := by
    rw [GlobalTheory.LatAlgebraic.cmPeriodConstant_eq_of_card_cmType hcard d s hs κ]; push_cast; ring
  rw [GlobalTheory.LatAlgebraic.risingFactor_eq] at hDg
  have key2 : GlobalTheory.ToricTransport.coordIn E d s κ Ω₀ (S 0) = ((-1 : ℂ) ^ k)⁻¹ *
      (2 * ((τ.im : ℝ) : ℂ) / ((Real.sqrt d : ℝ) : ℂ)) ^ k * c ^ (2 * s * f + 2 * k) *
      (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0 * ((Real.pi : ℂ) / ((τ.im : ℝ) : ℂ)) ^ k / P ^ (2 * s * f + 2 * k) /
        ω ^ (2 * s * f + 2 * k)) := by
    rw [GlobalTheory.ToricTransport.coordIn, hcard]
    exact coord_id _ (S 0) (GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.iterD u g 0) Ω₀ c _ _ (Real.pi : ℂ) ((τ.im : ℝ) : ℂ)
      ((Real.sqrt d : ℝ) : ℂ) P ((-1 : ℂ) ^ k) (2 * s * f + 2 * k) k hsgn hDg hC0 hΩ0 hc h2piI him hsd
  have hτalg : IsAlgebraic ℚ (τ : ℂ) := by
    rw [← hθτ]; exact (Algebra.IsAlgebraic.isAlgebraic θ).algHom ι.toRatAlgHom
  have hτc : IsAlgebraic ℚ (starRingEnd ℂ (τ : ℂ)) := by
    rw [← hθτ]; exact (Algebra.IsAlgebraic.isAlgebraic θ).algHom ((starRingEnd ℂ).comp ι).toRatAlgHom
  have hIalg : IsAlgebraic ℚ Complex.I := isAlgebraic_of_sq_eq_ratCast (-1) (by simp [Complex.I_sq])
  have himalg : IsAlgebraic ℚ ((τ.im : ℝ) : ℂ) := by
    rw [← UpperHalfPlane.coe_im, Complex.im_eq_sub_conj, ← mem_algebraicClosure_iff]
    exact div_mem (sub_mem (hA _ hτalg) (hA _ hτc)) (mul_mem (ofNat_mem _ 2) (hA _ hIalg))
  have hsdalg : IsAlgebraic ℚ ((Real.sqrt d : ℝ) : ℂ) := by
    refine isAlgebraic_of_sq_eq_ratCast (d : ℚ) ?_
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  rw [key2, ← mem_algebraicClosure_iff]
  exact mul_mem (mul_mem (mul_mem (inv_mem (pow_mem (neg_mem (one_mem _)) _))
    (pow_mem (div_mem (mul_mem (ofNat_mem _ 2) (hA _ himalg)) (hA _ hsdalg)) _)) (pow_mem (hA _ hcalg) _)) (hA _ hRalg')

end GlobalTheory.RoadELatAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeValueIsAlgebraicOfEllipticCMTheoremsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeValueIsAlgebraic_of_ellipticCM_theorems : GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.LatVal.LatAlg := by
  first | exact @GlobalTheory.RoadELatAlg.latAlg_of_siegelKlingen | exact GlobalTheory.RoadELatAlg.latAlg_of_siegelKlingen | (intros; apply GlobalTheory.RoadELatAlg.latAlg_of_siegelKlingen <;> assumption)
end
end

theorem GlobalTheory.JoinFun.joinOut_of_five : GlobalTheory.Published.EllipticMainTheoremCM → GlobalTheory.Published.HilbertClassFieldJ → GlobalTheory.Published.SiegelKlingenDeligneRibet → GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.Mem.LiteralAutomorphy.JoinOut :=
  fun hEM hHJ hSK hPZ hHT => GlobalTheory.T.toricPeriodZetaStatements_of_jetIntegrality_algebraicity hEM hHJ hSK hPZ hHT (GlobalTheory.T.cmLatticeDividedPowerJetIntegrality_of_ellipticCM hSK hPZ hHJ hEM)
    (GlobalTheory.T.latticeValueIsAlgebraic_of_ellipticCM_theorems hSK hPZ hHJ hEM) (GlobalTheory.T.latticeValueConjugation_of_ellipticCM_theorems hSK hPZ hHJ hEM)
