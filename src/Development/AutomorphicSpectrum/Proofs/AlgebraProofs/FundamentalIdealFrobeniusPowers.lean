module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.ProdDigits
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GdChartFin
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GcChart
public import Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsDenOfOpen
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericProjClosureDivisor
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartTestPoint

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusPowers
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusPowers
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_powers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable (F := F) AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ n, xIdeal AA.carrier (σ ^ p ^ n) = Ideal.span {c n}) → (∀ n, v (p : C) ≤ v (algebraMap R C (c n)) ^ (p - 1)) ∧ ∀ d : Fin f → Fin p, (∃ n, (d n : ℕ) ≠ 0) → xIdeal AA.carrier (σ ^ (∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ))) = Ideal.span {∏ n : Fin f, c n ^ (d n : ℕ)} := by
  first | exact @PositivityTheory.HtPt.Pmono.r_mono | exact PositivityTheory.HtPt.Pmono.r_mono
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FundamentalIdealFrobeniusPowersStatement
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_ideal_frobenius_powers : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (AA : HopfOrder (C := C) R F), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → ∀ c : ℕ → R, (∀ n, xIdeal AA.carrier (σ ^ p ^ n) = Ideal.span {c n}) → (∀ n, v (p : C) ≤ v (algebraMap R C (c n)) ^ (p - 1)) ∧ ∀ d : Fin f → Fin p, (∃ n, (d n : ℕ) ≠ 0) → xIdeal AA.carrier (σ ^ (∑ n : Fin f, (d n : ℕ) * p ^ (n : ℕ))) = Ideal.span {∏ n : Fin f, c n ^ (d n : ℕ)} := by
  first | exact @GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_powers | exact GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_powers | (intros; apply GlobalTheory.CompanionTheory.Relay.fundamental_ideal_frobenius_powers <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartSequenceHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDualPairing
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDualPairing
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem chart_comp_zero_mod : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d d' : A) (m : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), κ * (p : A) ^ m ∣ (p : A) ^ R → GeneratesDiff σ d → GeneratesDiff (σ.comp c.toRingHom) d' → (∀ x ∈ D.om, κ • x ∈ D.om') → Module.Projective A (D.omHT σ) → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → D.HasTestPoints κ → D.IsDualMap σ d m i → ∀ w, ∃ y ∈ D.omHT σ, D.q σ (i w) = ((p : A) ^ m) • y :=
  @PositivityTheory.HtPt.Gd.chart_comp_zero

end GlobalTheory.CompanionTheory.Ar.HT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDualPairingStatement
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_chart_dual_pairing : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d d' : A) (m : ℕ) (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), κ * (p : A) ^ m ∣ (p : A) ^ R → GeneratesDiff σ d → GeneratesDiff (σ.comp c.toRingHom) d' → (∀ x ∈ D.om, κ • x ∈ D.om') → Module.Projective A (D.omHT σ) → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → D.HasTestPoints κ → D.IsDualMap σ d m i → ∀ w, ∃ y ∈ D.omHT σ, D.q σ (i w) = ((p : A) ^ m) • y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.chart_comp_zero_mod | exact GlobalTheory.CompanionTheory.Ar.HT.chart_comp_zero_mod | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.chart_comp_zero_mod <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDifferentBound
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDifferentBound
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem dualMap_exists_unique_split : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d : A) (m : ℕ), (∀ (σ : E →+* K) (a : 𝓞 E), σ (a : E) ∈ (algebraMap A K).range) → GeneratesDiff σ d → κ * (p : A) ^ m ∣ (p : A) ^ R → (∀ x ∈ D.om, κ • x ∈ D.om') → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → (∃ (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), D.IsDualMap σ d m i) ∧ (∀ i i', D.IsDualMap σ d m i → D.IsDualMap σ d m i' → ∀ w, ∃ x : Fin N → A, i w = i' w + ((p : A) ^ m) • x) ∧ ∀ i, D.IsDualMap σ d m i → ∃ r : (Fin N → A) →ₗ[A] Module.Dual A (D.omHT (σ.comp c.toRingHom)), ∀ w, ∃ w', r (i w) = w + ((p : A) ^ m) • w' :=
  @PositivityTheory.HtPt.Ga.dual_map

end GlobalTheory.CompanionTheory.Ar.HT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDifferentBoundStatement
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_chart_different_bound : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d : A) (m : ℕ), (∀ (σ : E →+* K) (a : 𝓞 E), σ (a : E) ∈ (algebraMap A K).range) → GeneratesDiff σ d → κ * (p : A) ^ m ∣ (p : A) ^ R → (∀ x ∈ D.om, κ • x ∈ D.om') → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → (∃ (i : Module.Dual A (D.omHT (σ.comp c.toRingHom)) →ₗ[A] (Fin N → A)), D.IsDualMap σ d m i) ∧ (∀ i i', D.IsDualMap σ d m i → D.IsDualMap σ d m i' → ∀ w, ∃ x : Fin N → A, i w = i' w + ((p : A) ^ m) • x) ∧ ∀ i, D.IsDualMap σ d m i → ∃ r : (Fin N → A) →ₗ[A] Module.Dual A (D.omHT (σ.comp c.toRingHom)), ∀ w, ∃ w', r (i w) = w + ((p : A) ^ m) • w' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.dualMap_exists_unique_split | exact GlobalTheory.CompanionTheory.Ar.HT.dualMap_exists_unique_split | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.dualMap_exists_unique_split <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartTestPointStatement
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_chart_test_point : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A), κ ∣ (p : A) ^ R → Module.Projective A D.om' → D.HasTestPoints κ → D.om' ≤ D.om ∧ (∀ x ∈ D.om, κ • x ∈ D.om') := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.om'_between_of_testPoints | exact GlobalTheory.CompanionTheory.Ar.HT.om'_between_of_testPoints | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.om'_between_of_testPoints <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartNonUnitP
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartNonUnitP
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem chart_rank_add_conj : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d d' : A), ¬ IsUnit (p : A) → κ ∣ (p : A) ^ R → GeneratesDiff σ d → GeneratesDiff (σ.comp c.toRingHom) d' → Module.Projective A (D.omHT σ) → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → D.HasTestPoints κ → Module.finrank A (D.omHT σ) + Module.finrank A (D.omHT (σ.comp c.toRingHom)) = N :=
  @PositivityTheory.HtPt.Gb.chart_rank

end GlobalTheory.CompanionTheory.Ar.HT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartNonUnitPStatement
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_chart_non_unit_p : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] [CharZero K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (d d' : A), ¬ IsUnit (p : A) → κ ∣ (p : A) ^ R → GeneratesDiff σ d → GeneratesDiff (σ.comp c.toRingHom) d' → Module.Projective A (D.omHT σ) → Module.Projective A (D.omHT (σ.comp c.toRingHom)) → D.HasTestPoints κ → Module.finrank A (D.omHT σ) + Module.finrank A (D.omHT (σ.comp c.toRingHom)) = N := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.chart_rank_add_conj | exact GlobalTheory.CompanionTheory.Ar.HT.chart_rank_add_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.chart_rank_add_conj <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDivisibility
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDivisibility
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem q_onto_eigenpart_mod_pow : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (m : ℕ), (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → κ * (p : A) ^ m ∣ (p : A) ^ R → (∀ x ∈ D.om, κ • x ∈ D.om') → (∀ x, D.q σ x ∈ D.omHT σ) ∧ (D.omHT σ).FG ∧ ∀ y ∈ D.omHT σ, ∃ x : Fin N → A, ∃ y' ∈ D.omHT σ, y = D.q σ x + ((p : A) ^ m) • y' :=
  PositivityTheory.HtPt.Ga.q_surj

end GlobalTheory.CompanionTheory.Ar.HT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeTateChartDivisibilityStatement
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_chart_divisibility : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (hAK : Function.Injective (algebraMap A K)) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (p R N : ℕ) [Fact p.Prime] (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (D : HTChart A K c p R N Ω) (κ : A) (σ : E →+* K) (m : ℕ), (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → κ * (p : A) ^ m ∣ (p : A) ^ R → (∀ x ∈ D.om, κ • x ∈ D.om') → (∀ x, D.q σ x ∈ D.omHT σ) ∧ (D.omHT σ).FG ∧ ∀ y ∈ D.omHT σ, ∃ x : Fin N → A, ∃ y' ∈ D.omHT σ, y = D.q σ x + ((p : A) ^ m) • y' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.q_onto_eigenpart_mod_pow | exact GlobalTheory.CompanionTheory.Ar.HT.q_onto_eigenpart_mod_pow | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.q_onto_eigenpart_mod_pow <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjectiveSplitModuloElement
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjectiveSplitModuloElement
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem split_exact_mod : ∀ (A : Type) [CommRing A] [IsDomain A] (P₁ P₂ : Type) [AddCommGroup P₁] [Module A P₁] [Module.Finite A P₁] [Module.Projective A P₁] [AddCommGroup P₂] [Module A P₂] [Module.Finite A P₂] [Module.Projective A P₂] (N : ℕ) (a : A) (i : P₁ →ₗ[A] (Fin N → A)) (r : (Fin N → A) →ₗ[A] P₁) (q : (Fin N → A) →ₗ[A] P₂), Module.finrank A P₁ + Module.finrank A P₂ = N → (∀ w, ∃ w', r (i w) = w + a • w') → (∀ y, ∃ x y', y = q x + a • y') → (∀ w, ∃ y, q (i w) = a • y) → ∀ x, (∃ y, q x = a • y) → ∃ w x', x = i w + a • x' :=
  @PositivityTheory.HtPt.Gd.split_exact

end GlobalTheory.CompanionTheory.Ar.HT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjectiveSplitModuloElementStatement
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_split_modulo_element : ∀ (A : Type) [CommRing A] [IsDomain A] (P₁ P₂ : Type) [AddCommGroup P₁] [Module A P₁] [Module.Finite A P₁] [Module.Projective A P₁] [AddCommGroup P₂] [Module A P₂] [Module.Finite A P₂] [Module.Projective A P₂] (N : ℕ) (a : A) (i : P₁ →ₗ[A] (Fin N → A)) (r : (Fin N → A) →ₗ[A] P₁) (q : (Fin N → A) →ₗ[A] P₂), Module.finrank A P₁ + Module.finrank A P₂ = N → (∀ w, ∃ w', r (i w) = w + a • w') → (∀ y, ∃ x y', y = q x + a • y') → (∀ w, ∃ y, q (i w) = a • y) → ∀ x, (∃ y, q x = a • y) → ∃ w x', x = i w + a • x' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.split_exact_mod | exact GlobalTheory.CompanionTheory.Ar.HT.split_exact_mod | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.split_exact_mod <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartSequenceHolds
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.FinrankDualChartSequence

theorem finrank_dual_eq_of_projective (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (M : Type) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] : finrank A (Module.Dual A M) = finrank A M := by
  haveI : FaithfulSMul A K :=
    (faithfulSMul_iff_algebraMap_injective A K).2 (IsFractionRing.injective A K)
  rw [← (TensorProduct.isBaseChange A (Module.Dual A M) K).finrank_eq,
    ← (TensorProduct.isBaseChange A M K).finrank_eq]
  exact (GlobalTheory.DualFibreRank.finrank_dual_and_range_dualMap_baseChange A M M K LinearMap.id).1

theorem ringOfIntegers_mem_range (A K : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K]
    [Algebra A K] [IsFractionRing A K] {E : Type} [Field E] [NumberField E] (σ : E →+* K) (a : 𝓞 E) :
    σ (a : E) ∈ (algebraMap A K).range := by
  have h1 : IsIntegral ℤ (σ (a : E)) := (RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom
  have h2 : IsIntegral A (σ (a : E)) := h1.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h2
  exact ⟨y, hy⟩

def qLin {A K : Type} [CommRing A] [Field K] [Algebra A K] {E : Type} [Field E] [NumberField E]
    {c : E ≃+* E} {p R N : ℕ} {Ω : Type} [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω]
    (D : HTChart A K c p R N Ω) (σ : E →+* K) : (Fin N → A) →ₗ[A] Ω where
  toFun := D.q σ
  map_add' x y := by simp [HTChart.q, add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [HTChart.q, Finset.smul_sum, mul_smul]

theorem chartSequence : ChartSequence := by
  intro A K _ _ _ _ _ _ _ _ E _ _ c hc p R N _ Ω _ _ _ _ D κ m hdiv hT hproj
  have hκR : κ ∣ (p : A) ^ R := dvd_trans (dvd_mul_right _ _) hdiv
  have h1 := GlobalTheory.T.hodge_tate_chart_test_point A K E c hc p R N Ω D κ hκR hproj hT
  refine ⟨h1, ?_⟩
  intro σ d d' hd hd' hP1 hP2
  have hAK : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hnorm : ∀ (σ : E →+* K) (a : 𝓞 E), σ (a : E) ∈ (algebraMap A K).range :=
    fun σ a => ringOfIntegers_mem_range A K σ a
  obtain ⟨⟨i, hi⟩, -, hsplit⟩ := GlobalTheory.T.hodge_tate_chart_different_bound A K hAK E c hc p R N Ω D κ σ d m hnorm hd hdiv h1.2 hP2
  have hq := GlobalTheory.T.hodge_tate_chart_divisibility A K hAK E c hc p R N Ω D κ σ m (hnorm σ) hdiv h1.2
  have hq' := GlobalTheory.T.hodge_tate_chart_divisibility A K hAK E c hc p R N Ω D κ (σ.comp c.toRingHom) m (hnorm _) hdiv h1.2
  have hcomp := GlobalTheory.T.hodge_tate_chart_dual_pairing A K E c hc p R N Ω D κ σ d d' m i hdiv hd hd' h1.2 hP1 hP2 hT hi
  refine ⟨i, hi, hsplit i hi, fun x => ⟨?_, ?_⟩, hq.2.2⟩
  · rintro ⟨y, hy, hxy⟩
    by_cases hu : IsUnit (p : A)
    · obtain ⟨u, hu'⟩ := hu.pow m
      refine ⟨0, ((u⁻¹ : Aˣ) : A) • x, ?_⟩
      rw [map_zero, zero_add, ← hu', smul_smul, Units.mul_inv, one_smul]
    · haveI : Module.Finite A (D.omHT σ) := Module.Finite.iff_fg.2 hq.2.1
      haveI : Module.Finite A (D.omHT (σ.comp c.toRingHom)) := Module.Finite.iff_fg.2 hq'.2.1
      haveI := hP1
      haveI := hP2
      have hrank := GlobalTheory.T.hodge_tate_chart_non_unit_p A K E c hc p R N Ω D κ σ d d' hu hκR hd hd' hP1 hP2 hT
      rw [← finrank_dual_eq_of_projective A K (D.omHT (σ.comp c.toRingHom))] at hrank
      obtain ⟨r, hr⟩ := hsplit i hi
      let qL : (Fin N → A) →ₗ[A] D.omHT σ := LinearMap.codRestrict (D.omHT σ) (qLin D σ) hq.1
      refine GlobalTheory.T.projective_split_modulo_element A (Module.Dual A (D.omHT (σ.comp c.toRingHom))) (D.omHT σ) N ((p : A) ^ m)
        i r qL (by rw [add_comm]; exact hrank) hr ?_ ?_ x ⟨⟨y, hy⟩, Subtype.ext hxy⟩
      · rintro ⟨y, hy⟩
        obtain ⟨x, y', hy', e⟩ := hq.2.2 y hy
        exact ⟨x, ⟨y', hy'⟩, Subtype.ext e⟩
      · intro w
        obtain ⟨y, hy, e⟩ := hcomp w
        exact ⟨⟨y, hy⟩, Subtype.ext e⟩
  · rintro ⟨w, x', rfl⟩
    obtain ⟨y, hy, hy'⟩ := hcomp w
    refine ⟨y + D.q σ x', add_mem hy (hq.1 x'), ?_⟩
    have e1 := (qLin D σ).map_add (i w) (((p : A) ^ m) • x')
    have e2 := (qLin D σ).map_smul ((p : A) ^ m) x'
    change D.q σ _ = _
    change (qLin D σ) _ = _
    rw [e1, e2]
    change D.q σ (i w) + _ = _
    rw [hy', smul_add]
    rfl

end GlobalTheory.CompanionTheory.Ar.HT.FinrankDualChartSequence
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartSequenceHoldsStatement
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_sequence_holds : ChartSequence := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.FinrankDualChartSequence.chartSequence | exact GlobalTheory.CompanionTheory.Ar.HT.FinrankDualChartSequence.chartSequence | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.FinrankDualChartSequence.chartSequence <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MonomialRatioIntegralModel
section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XVertdivCommensurable
section -- merged from Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XFormsExist
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_forms_exist

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] [DecidableEq K]
  {ι : K → Type}

theorem shift (x : (Σ k, ι k) → Ω) (t : ∀ k, ι k) (e : K → ℕ) {F : MRing ι O} {d : K → ℕ}
    (hF : IsMultiHomog F d) :
    ∃ G : MRing ι O, IsMultiHomog G (d + e) ∧ aeval x G = aeval x F * ∏ k, x ⟨k, t k⟩ ^ e k := by
  have h := IsWeightedHomogeneous.prod (Finset.univ : Finset K)
    (fun k => (X ⟨k, t k⟩ : MRing ι O) ^ e k) (fun k => e k • blockWeight ι ⟨k, t k⟩)
    (w := blockWeight ι)
    (fun k _ => (isWeightedHomogeneous_X O (blockWeight ι) ⟨k, t k⟩).pow (e k))
  have he : ∑ k, e k • blockWeight ι ⟨k, t k⟩ = e := by
    ext k'
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [he] at h
  refine ⟨F * ∏ k, (X ⟨k, t k⟩ : MRing ι O) ^ e k, IsWeightedHomogeneous.mul hF h, ?_⟩
  simp [map_prod]

def fracs (O : Type) [CommRing O] [Algebra O Ω] (x : (Σ k, ι k) → Ω) (s : ∀ k, ι k) : Subalgebra O Ω where
  carrier := {v | ∃ (d : K → ℕ) (F : MRing ι O), IsMultiHomog F d ∧ aeval x F = v * ∏ k, x ⟨k, s k⟩ ^ d k}
  mul_mem' := by
    rintro v w ⟨d, F, hF, eF⟩ ⟨e, G, hG, eG⟩
    refine ⟨d + e, F * G, IsWeightedHomogeneous.mul hF hG, ?_⟩
    simp only [map_mul, eF, eG, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring
  add_mem' := by
    rintro v w ⟨d, F, hF, eF⟩ ⟨e, G, hG, eG⟩
    obtain ⟨F', hF', eF'⟩ := shift x s e hF
    obtain ⟨G', hG', eG'⟩ := shift x s d hG
    rw [add_comm e d] at hG'
    refine ⟨d + e, F' + G', IsWeightedHomogeneous.add hF' hG', ?_⟩
    simp only [map_add (f := _), eF', eG', eF, eG, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring
  algebraMap_mem' r := ⟨0, C r, isWeightedHomogeneous_C _ _, by simp⟩

theorem chartRing_le_fracs (x : (Σ k, ι k) → Ω) (s : ∀ k, ι k) (hs : mseg x s ≠ 0) :
    chartRing O (mseg x) s ≤ fracs O x s := by
  unfold chartRing
  rw [Algebra.adjoin_le_iff]
  rintro _ ⟨j, rfl⟩
  refine ⟨fun _ => 1, ∏ k, (X ⟨k, j k⟩ : MRing ι O), ?_, ?_⟩
  · have h := IsWeightedHomogeneous.prod (Finset.univ : Finset K)
      (fun k => (X ⟨k, j k⟩ : MRing ι O)) (fun k => blockWeight ι ⟨k, j k⟩)
      (w := blockWeight ι) (fun k _ => isWeightedHomogeneous_X O (blockWeight ι) ⟨k, j k⟩)
    have he : ∑ k, blockWeight ι ⟨k, j k⟩ = fun _ => 1 := by
      ext k'
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [he] at h
    exact h
  · simp only [map_prod, aeval_X, pow_one]
    have hm : ∏ k, x ⟨k, s k⟩ = mseg x s := rfl
    rw [hm, div_mul_cancel₀ _ hs]
    try rfl

end PositivityTheory.Xgn.A_forms_exist
end

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace PositivityTheory.Xgn.A_vertdiv_commensurable

variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω] {K : Type} [Fintype K] [DecidableEq K]
  {ι : K → Type} [∀ k, Fintype (ι k)]

def Pair (x : (Σ k, ι k) → Ω) (c : K → ℤ) (u : Ω) (f g : MRing ι O) : Prop :=
  (∃ bf bg : K → ℕ, IsMultiHomog f bf ∧ IsMultiHomog g bg ∧ (fun k => (bf k : ℤ) - bg k) = c) ∧
    aeval x f = u * aeval x g

theorem cross {x : (Σ k, ι k) → Ω} {c : K → ℤ} {u : Ω} {f g f' g' : MRing ι O}
    (h : Pair x c u f g) (h' : Pair x c u f' g') : f * g' - f' * g ∈ pointIdeal O x := by
  obtain ⟨⟨bf, bg, hf, hg, hd⟩, hv⟩ := h
  obtain ⟨⟨bf', bg', hf', hg', hd'⟩, hv'⟩ := h'
  have he : bf + bg' = bf' + bg := by
    funext k
    have h1 := congrFun hd k
    have h2 := congrFun hd' k
    simp only [Pi.add_apply] at h1 h2 ⊢
    omega
  have h1 : IsWeightedHomogeneous (blockWeight ι) (f * g') (bf + bg') := IsWeightedHomogeneous.mul hf hg'
  have h2 : IsWeightedHomogeneous (blockWeight ι) (f' * g) (bf + bg') := by
    rw [he]; exact IsWeightedHomogeneous.mul hf' hg
  refine GenericProjClosureDivisor.mem_of_homog (b := bf + bg') ?_ ?_
  · exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp
      (sub_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h1)
        ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h2))
  · rw [map_sub, map_mul, map_mul, hv, hv']
    ring

omit [∀ k, Fintype (ι k)] in
theorem mono_homog (s : ∀ k, ι k) (e : K → ℕ) :
    IsMultiHomog (∏ k, X ⟨k, s k⟩ ^ e k : MRing ι O) e := by
  have he : e = ∑ k, e k • blockWeight ι ⟨k, s k⟩ := by
    ext j
    simp [blockWeight, Pi.single_apply]
  unfold IsMultiHomog
  conv => enter [3]; rw [he]
  exact IsWeightedHomogeneous.prod _ _ _ fun k _ => (isWeightedHomogeneous_X O _ _).pow _

theorem product_powers_not_mem_prime {A : Type} [CommRing A] {W : Ideal A} (hW : W.IsPrime) {c : A} (hc : c ∉ W) (y : K → A)
    (hy : ∀ k, y k ∉ W) (n : ℕ) (e : K → ℕ) : c ^ n * ∏ k, y k ^ e k ∉ W := by
  intro hf
  rcases hW.mem_or_mem hf with h3 | h3
  · exact hc (hW.mem_of_pow_mem n h3)
  · obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff (p := W)).1 h3
    exact hy k (hW.mem_of_pow_mem (e k) hk)

theorem zpow_aux (y : K → Ω) (hy : ∀ k, y k ≠ 0) (b b' : K → ℤ) (p q : K → ℕ)
    (h : ∀ k, b k + q k = b' k + p k) :
    (∏ k, y k ^ b k) * ∏ k, y k ^ q k = (∏ k, y k ^ b' k) * ∏ k, y k ^ p k := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hy k), ← zpow_add₀ (hy k), h k]

theorem mul_eq_one_of_covolume_identity {m m' t D P Q r u : Ω} (hm : m' ≠ 0) (h : t * m = r * (u * m')) (hb : m * Q = m' * P) :
    t * (D * P) = u * (r * D * Q) := by
  apply mul_left_cancel₀ hm
  linear_combination D * Q * h - D * t * hb

omit [∀ k, Fintype (ι k)] in
theorem pair_num {x : (Σ k, ι k) → Ω} {ϖ : O} {b b' : K → ℤ} {u : Ω} {s : ∀ k, ι k} (hs : mseg x s ≠ 0)
    {W : Ideal (MRing ι O)} (hW : W.IsPrime) (hϖ : (C ϖ : MRing ι O) ∉ W)
    (hX : ∀ k, (X ⟨k, s k⟩ : MRing ι O) ∉ W) {n : ℕ} {r : Ω} (hr : r ∈ chartRing O (mseg x) s)
    (h : algebraMap O Ω ϖ ^ n * chartMon x s b = r * (u * chartMon x s b')) :
    ∃ f g : MRing ι O, Pair x (b - b') u f g ∧ f ∉ W := by
  obtain ⟨d, F, hF, eF⟩ := A_forms_exist.chartRing_le_fracs x s hs hr
  have hx : ∀ k, x ⟨k, s k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hs k (Finset.mem_univ k)
  have hm : chartMon x s b' ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hx k)
  obtain ⟨p, hp⟩ : ∃ p : K → ℕ, ∀ k, p k = (b k - b' k).toNat := ⟨_, fun _ => rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : K → ℕ, ∀ k, q k = (b' k - b k).toNat := ⟨_, fun _ => rfl⟩
  have hpq : ∀ k, b k + q k = b' k + p k := fun k => by
    have e1 := hp k
    have e2 := hq k
    omega
  have hb : chartMon x s b * ∏ k, x ⟨k, s k⟩ ^ q k = chartMon x s b' * ∏ k, x ⟨k, s k⟩ ^ p k :=
    zpow_aux (fun k => x ⟨k, s k⟩) hx b b' p q hpq
  have h0 : IsMultiHomog (C ϖ ^ n : MRing ι O) 0 := by
    rw [← map_pow]
    exact isWeightedHomogeneous_C _ _
  have h1 : IsMultiHomog (C ϖ ^ n * ∏ k, X ⟨k, s k⟩ ^ (d + p) k : MRing ι O) (0 + (d + p)) :=
    IsWeightedHomogeneous.mul h0 (mono_homog s (d + p))
  have h2 : IsMultiHomog (F * ∏ k, X ⟨k, s k⟩ ^ q k : MRing ι O) (d + q) :=
    IsWeightedHomogeneous.mul hF (mono_homog s q)
  refine ⟨_, _, ⟨⟨_, _, h1, h2, ?_⟩, ?_⟩, product_powers_not_mem_prime hW hϖ (fun k => X ⟨k, s k⟩) hX n (d + p)⟩
  · funext k
    have e1 := hpq k
    simp only [Pi.add_apply, Pi.sub_apply, Pi.zero_apply]
    omega
  · simp only [map_mul, map_prod, map_pow, aeval_X, aeval_C, eF, Pi.add_apply, pow_add,
      Finset.prod_mul_distrib]
    exact mul_eq_one_of_covolume_identity hm h hb

theorem pair_at {x : (Σ k, ι k) → Ω} {ϖ : O} {b b' : K → ℤ} {u : Ω} (hu : u ≠ 0)
    (H : ∀ s, mseg x s ≠ 0 → (∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * chartMon x s b = r * (u * chartMon x s b')) ∧ ∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * (u * chartMon x s b') = r * chartMon x s b)
    (W : Ideal (MRing ι O)) (hW : W.IsPrime) (hPW : pointIdeal O x ≤ W) (hrel : IsRelevant W)
    (hϖ : (C ϖ : MRing ι O) ∉ W) :
    ∃ f g : MRing ι O, Pair x (b - b') u f g ∧ f ∉ W ∧ g ∉ W := by
  choose s hX using hrel
  have hs : mseg x s ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun k _ h0 => hX k (hPW ?_)
    exact GenericProjClosureDivisor.mem_of_homog (isWeightedHomogeneous_X O _ _) (by rw [aeval_X, h0])
  obtain ⟨⟨n, r, hr, h⟩, n', r', hr', h'⟩ := H s hs
  obtain ⟨f, g, hp, hf⟩ := pair_num hs hW hϖ hX hr h
  have h'' : algebraMap O Ω ϖ ^ n' * chartMon x s b' = r' * (u⁻¹ * chartMon x s b) := by
    apply mul_left_cancel₀ hu
    rw [mul_left_comm r', ← mul_assoc u u⁻¹, mul_inv_cancel₀ hu, one_mul, ← h']
    ring
  obtain ⟨g', f', ⟨⟨bg, bf, hg1, hf1, hd⟩, hv⟩, hg'⟩ := pair_num hs hW hϖ hX hr' h''
  have hp' : Pair x (b - b') u f' g' := by
    refine ⟨⟨bf, bg, hf1, hg1, ?_⟩, ?_⟩
    · funext k
      have h1 := congrFun hd k
      simp only [Pi.sub_apply] at h1 ⊢
      omega
    · rw [hv, ← mul_assoc, mul_inv_cancel₀ hu, one_mul]
  refine ⟨f, g, hp, hf, fun hg => ?_⟩
  have h1 := W.add_mem (hPW (cross hp hp')) (W.mul_mem_left f' hg)
  rw [sub_add_cancel] at h1
  exact (hW.mem_or_mem h1).elim hf hg'

end PositivityTheory.Xgn.A_vertdiv_commensurable

theorem PositivityTheory.Xgn.t_vertdiv_commensurable : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, IsModelOver (pointIdeal O x) d → ∀ (b b' : K → ℤ) (u : Ω), u ≠ 0 → (∀ s, mseg x s ≠ 0 → (∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * chartMon x s b = r * (u * chartMon x s b')) ∧ ∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * (u * chartMon x s b') = r * chartMon x s b) → ∃ f g : MRing ι O, IsVerticalDivisor (pointIdeal O x) ϖ (b - b') f g ∧ aeval x f = u * aeval x g := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x ϖ hϖ d hM b b' u hu H
  have hϖP : (C ϖ : MRing ι O) ∉ pointIdeal O x := by
    intro hm
    have h1 : ϖ ∈ (pointIdeal O x).comap (C : O →+* MRing ι O) := hm
    rw [hM.noTorsion, Ideal.mem_bot] at h1
    exact hϖ.ne_zero h1
  obtain ⟨f, g, hp, hf, hg⟩ := A_vertdiv_commensurable.pair_at hu H _ hM.multiProj.isPrime le_rfl
    hM.multiProj.relevant hϖP
  refine ⟨f, g, IsVerticalDivisor.of_unit_off_special hp.1 hf hg fun W hW hPW hrel hϖW => ?_, hp.2⟩
  obtain ⟨f', g', hp', hf', hg'⟩ := A_vertdiv_commensurable.pair_at hu H W hW hPW hrel hϖW
  refine ⟨g', f', hg', hf', ?_⟩
  rw [mul_comm g' f]
  exact A_vertdiv_commensurable.cross hp hp'
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MonomialRatioIntegralModel
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.VertDiv

theorem commensurable_vertical : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, IsModelOver (pointIdeal O x) d → ∀ (b b' : K → ℤ) (u : Ω), u ≠ 0 → (∀ s, mseg x s ≠ 0 → (∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * chartMon x s b = r * (u * chartMon x s b')) ∧ ∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * (u * chartMon x s b') = r * chartMon x s b) → ∃ f g : MRing ι O, IsVerticalDivisor (pointIdeal O x) ϖ (b - b') f g ∧ aeval x f = u * aeval x g :=
  @PositivityTheory.Xgn.t_vertdiv_commensurable

end GlobalTheory.CompanionTheory.Ar.Num.VertDiv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MonomialRatioIntegralModelStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monomial_ratio_integral_model : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (ϖ : O), Irreducible ϖ → ∀ d : ℕ, IsModelOver (pointIdeal O x) d → ∀ (b b' : K → ℤ) (u : Ω), u ≠ 0 → (∀ s, mseg x s ≠ 0 → (∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * chartMon x s b = r * (u * chartMon x s b')) ∧ ∃ n : ℕ, ∃ r ∈ chartRing O (mseg x) s, algebraMap O Ω ϖ ^ n * (u * chartMon x s b') = r * chartMon x s b) → ∃ f g : MRing ι O, IsVerticalDivisor (pointIdeal O x) ϖ (b - b') f g ∧ aeval x f = u * aeval x g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.VertDiv.commensurable_vertical | exact GlobalTheory.CompanionTheory.Ar.Num.VertDiv.commensurable_vertical | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.VertDiv.commensurable_vertical <;> assumption)
end
end
