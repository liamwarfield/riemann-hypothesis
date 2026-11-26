module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MapDofIterate
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.MulVecBvecApply
public import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.BlockMinorSumCounterexample
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.FrameInvMulVecNegativeVector
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SymmetricMeasureL2NormEqResolutionL2

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasimirScalarOfCapelliDeterminantEigenvalue
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasimirScalarOfCapelliDeterminantEigenvalue
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CapelliCasimir
open Polynomial

noncomputable def rev {ι : Type} (s : Finset ι) (f : ι → ℂ) : ℂ[X] := ∏ l ∈ s, (1 + C (f l) * X)

theorem rev_coeff {ι : Type} (s : Finset ι) (f : ι → ℂ) :
    (rev s f).coeff 0 = 1 ∧ (rev s f).coeff 1 = ∑ l ∈ s, f l ∧
      2 * (rev s f).coeff 2 = (∑ l ∈ s, f l) ^ 2 - ∑ l ∈ s, f l ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rev, coeff_one]
  | insert a s ha ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have c1 : ∀ p : ℂ[X], (X * p).coeff 1 = p.coeff 0 := fun p => coeff_X_mul p 0
    have c2 : ∀ p : ℂ[X], (X * p).coeff 2 = p.coeff 1 := fun p => coeff_X_mul p 1
    have : rev (insert a s) f = rev s f + C (f a) * (X * rev s f) := by
      simp only [rev, prod_insert ha]; ring
    rw [this, sum_insert ha, sum_insert ha]
    simp only [coeff_add, coeff_C_mul]
    refine ⟨?_, ?_, ?_⟩
    · simp [h0]
    · rw [c1, h0, h1]; ring
    · rw [c2, h1]
      linear_combination h2

theorem rev_eval {ι : Type} (s : Finset ι) (f : ι → ℂ) (t : ℂ) (ht : t ≠ 0) :
    (rev s f).eval t = t ^ s.card * ∏ l ∈ s, (t⁻¹ + f l) := by
  rw [rev, eval_prod, ← prod_const, ← prod_mul_distrib]
  refine prod_congr rfl fun l _ => ?_
  simp; field_simp

theorem scalar_core (n : ℕ) (hn : 2 ≤ n) (ρ μ a : Fin n → ℂ) (b : Fin n → Fin n → ℂ) (r : ℕ → ℂ)
    (e c : ℂ)
    (h : ∀ Y : ℂ, (∏ l, (Y + ρ l)) * e + ∑ i, (∏ l ∈ univ.erase i, (Y + ρ l)) * a i
      + ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (∏ l ∈ (univ.erase i).erase j, (Y + ρ l)) * b i j
      + ∑ d ∈ range (n - 2), (Y + c) ^ d * r d = (∏ l, (Y + μ l)) * e) :
    (∑ l, ρ l) * e + ∑ i, a i = (∑ l, μ l) * e ∧
    ((∑ l, ρ l) ^ 2 - ∑ l, ρ l ^ 2) * e + 2 * ∑ i, (∑ l ∈ univ.erase i, ρ l) * a i
      + 2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), b i j
      = ((∑ l, μ l) ^ 2 - ∑ l, μ l ^ 2) * e := by
  have key : C e * rev univ ρ + X * ∑ i, C (a i) * rev (univ.erase i) ρ
      + X ^ 2 * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), C (b i j) * rev ((univ.erase i).erase j) ρ
      + X ^ 3 * ∑ d ∈ range (n - 2), C (r d) * X ^ (n - 3 - d) * (1 + C c * X) ^ d
      = C e * rev univ μ := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.Infinite.mono (s := {0}ᶜ) ?_ (Set.finite_singleton (0:ℂ)).infinite_compl
    intro t ht
    have ht : t ≠ 0 := ht
    simp only [Set.mem_setOf_eq, eval_add, eval_mul, eval_C, eval_X, eval_pow, Polynomial.eval_finsetSum,
      eval_one, rev_eval _ _ _ ht, card_univ, Fintype.card_fin]
    have := congrArg (fun z => t ^ n * z) (h t⁻¹)
    simp only [mul_add, mul_sum] at this ⊢
    refine Eq.trans ?_ (this.trans (by ring))
    congr 1
    · congr 1
      · congr 1
        · ring
        · refine sum_congr rfl fun i _ => ?_
          rw [card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fin]
          obtain ⟨m, hm⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
          have : t ^ n = t * t ^ (n - 1) := by
            rw [← pow_succ']; congr 1; omega
          rw [this]; ring
      · refine sum_congr rfl fun i _ => sum_congr rfl fun j hj => ?_
        have hij : j ≠ i := (mem_filter.1 hj).2.ne'
        rw [card_erase_of_mem (mem_erase.2 ⟨hij, mem_univ _⟩), card_erase_of_mem (mem_univ _),
          card_univ, Fintype.card_fin]
        have : t ^ n = t ^ 2 * t ^ (n - 1 - 1) := by
          rw [← pow_add]; congr 1; omega
        rw [this]; ring
    · refine sum_congr rfl fun d hd => ?_
      have hd := mem_range.1 hd
      have h1 : t ^ n = t ^ 3 * t ^ (n - 3 - d) * t ^ d := by
        rw [← pow_add, ← pow_add]; congr 1; omega
      have h2 : (1 + c * t) = t * (t⁻¹ + c) := by field_simp
      rw [h1, h2, mul_pow]; ring
  have k1 := congrArg (fun p => p.coeff 1) key
  have k2 := congrArg (fun p => p.coeff 2) key
  simp only [coeff_add, coeff_C_mul, coeff_X_pow_mul'] at k1 k2
  have c1 : ∀ p : ℂ[X], (X * p).coeff 1 = p.coeff 0 := fun p => coeff_X_mul p 0
  have c2 : ∀ p : ℂ[X], (X * p).coeff 2 = p.coeff 1 := fun p => coeff_X_mul p 1
  rw [c1] at k1
  rw [c2] at k2
  simp only [Polynomial.finsetSum_coeff, coeff_C_mul, (rev_coeff _ _).1, (rev_coeff _ _).2.1, le_refl, if_true,
    Nat.sub_self, mul_one] at k1 k2
  norm_num at k1 k2
  constructor
  · linear_combination k1
  · have p1 := (rev_coeff univ ρ).2.2
    have p2 := (rev_coeff univ μ).2.2
    have : ∑ i, (∑ l ∈ univ.erase i, ρ l) * a i = ∑ i, a i * (∑ l, ρ l - ρ i) := by
      refine sum_congr rfl fun i _ => ?_
      rw [sum_erase_eq_sub (mem_univ _), mul_comm]
    rw [this]
    linear_combination 2 * k2 - e * p1 + e * p2

theorem sum_sq_split {A : Type} [AddCommGroup A] {n : ℕ} (F : Fin n → Fin n → A) :
    ∑ i, ∑ j, F i j = ∑ i, F i i + ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (F i j + F j i) := by
  have h1 : ∀ i j, F i j = (if i = j then F i j else 0) + (if i < j then F i j else 0)
      + (if j < i then F i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, h.not_gt]
    · simp [h]
    · simp [h, h.ne', h.not_gt]
  rw [sum_congr rfl fun i _ => sum_congr rfl fun j _ => h1 i j]
  simp only [sum_add_distrib, sum_filter, sum_ite_eq, mem_univ, if_true]
  rw [add_assoc, sum_comm (f := fun i j => if j < i then F i j else 0)]

theorem sum_diff {A : Type} [AddCommGroup A] [Module ℂ A] {n : ℕ} (x : Fin n → A) :
    ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (x i - x j)
      = ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • x i := by
  simp only [sum_sub_distrib]
  have : ∑ i, ∑ j ∈ univ.filter (fun j => i < j), x j
      = ∑ j, ∑ i ∈ univ.filter (fun i => i < j), x j := by
    simp only [sum_filter]; exact sum_comm
  rw [this, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_const, sum_const, filter_lt_eq_Ioi, filter_gt_eq_Iio, Fin.card_Ioi, Fin.card_Iio,
    ← Nat.cast_smul_eq_nsmul ℂ, ← Nat.cast_smul_eq_nsmul ℂ, ← sub_smul]
  congr 1
  have := i.2
  rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
  push_cast; ring

theorem sq_sub_cas {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (hE : Formalism.REAL.GlRel E) :
    (∑ i, E i i) * (∑ i, E i i) - Formalism.REAL.Cas E
      = (2 : ℂ) • ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (E i i * E j j - E j i * E i j)
        - ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) • E i i := by
  rw [← sum_diff, Formalism.REAL.Cas, sum_mul_sum, ← sum_sub_distrib]
  simp only [← sum_sub_distrib]
  rw [sum_sq_split]
  simp only [sub_self, sum_const_zero, zero_add, smul_sum, ← sum_sub_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j hj => ?_
  have hij : i ≠ j := (mem_filter.1 hj).2.ne
  have h1 := hE i j j i
  have h2 := hE i i j j
  simp only [if_true, hij, hij.symm, if_false, sub_zero] at h1 h2
  rw [two_smul, ← h1, ← sub_eq_zero.1 h2]
  abel

theorem cas_of_capelli : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (mu : Fin n → ℝ), 2 ≤ n → Formalism.REAL.GlRel E → (∀ (Y : ℂ) (w : M), Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w) → ∀ w, Formalism.REAL.Cas E w = (casG mu : ℂ) • w := by
  intro M _ _ n E mu hn hE h
  obtain ⟨Rm, hR⟩ := _root_.GlobalTheory.qdet_top_three_orders (Module.End ℂ M) n E
  set ρ : Fin n → ℂ := fun l => ((n : ℂ) - 1) / 2 - ((l : ℕ) : ℂ) with hρ
  have hρ0 : ∑ l, ρ l = 0 := by
    have h1 : ∑ l, ρ l = ∑ l, ρ (Fin.rev l) := (Equiv.sum_comp Fin.revPerm ρ).symm
    have h2 : ∑ l, ρ (Fin.rev l) = - ∑ l, ρ l := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun l _ => ?_
      have := l.2
      simp only [hρ, Fin.val_rev]
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    linear_combination (h1.trans h2) / 2
  have core := fun φ : Module.Dual ℂ (Module.End ℂ M) =>
    scalar_core n hn ρ (fun s => (mu s : ℂ)) (fun i => φ (E i i))
      (fun i j => φ (E i i * E j j - E j i * E i j)) (fun d => φ (Rm d)) (φ 1) (((n : ℂ) - 1) / 2)
      (fun Y => by
        have h1 : Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2)
            = (∏ s, (Y + (mu s : ℂ))) • (1 : Module.End ℂ M) := by
          ext w; simpa using h Y w
        have h2 := congrArg φ ((hR _).symm.trans h1)
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_add (f := _), map_sum, map_smul, smul_eq_mul, add_sub_assoc] at h2
        exact h2)
  have e1 : ∑ i, E i i = (∑ l, (mu l : ℂ)) • (1 : Module.End ℂ M) := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    have := (core φ).1
    rw [hρ0] at this
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_smul, smul_eq_mul]
    linear_combination this
  have e2 : Formalism.REAL.Cas E = (casG mu : ℂ) • (1 : Module.End ℂ M) := by
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
    intro φ
    have h2 := (core φ).2
    have h3 := congrArg φ (sq_sub_cas E hE)
    rw [e1, smul_mul_smul_comm, mul_one] at h3
    simp only [sum_erase_eq_sub (mem_univ _), hρ0] at h2
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub φ, map_sum, map_smul, smul_eq_mul] at h3 h2 ⊢
    have h4 : (casG mu : ℂ) = ∑ l, (mu l : ℂ) ^ 2 - ∑ l, ρ l ^ 2 := by
      simp [casG, Formalism.QuantumDeterminants.rhoStd, hρ]
    have h5 : ∑ i : Fin n, ((n : ℂ) - 1 - 2 * (i : ℕ)) * φ (E i i)
        = - (2 * ∑ i, (0 - ρ i) * φ (E i i)) := by
      rw [mul_sum, ← sum_neg_distrib]
      refine sum_congr rfl fun i _ => ?_
      simp only [hρ]; ring
    rw [h4]
    rw [h5] at h3
    linear_combination -h3 - h2
  intro w
  rw [e2]; simp

end GlobalTheory.CapelliCasimir
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CasimirScalarOfCapelliDeterminantEigenvalueStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.casimir_scalar_of_capelliDeterminant_eigenvalue : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ M) (mu : Fin n → ℝ), 2 ≤ n → Formalism.REAL.GlRel E → (∀ (Y : ℂ) (w : M), Formalism.REAL.qdet E (Y + ((n : ℂ) - 1) / 2) w = (∏ s, (Y + (mu s : ℂ))) • w) → ∀ w, Formalism.REAL.Cas E w = (casG mu : ℂ) • w := by
  first | exact @GlobalTheory.CapelliCasimir.cas_of_capelli | exact GlobalTheory.CapelliCasimir.cas_of_capelli | (intros; apply GlobalTheory.CapelliCasimir.cas_of_capelli <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFunctionLocalityInvariantFactorFiniteSum
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFunctionLocalityInvariantFactorFiniteSum
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselFunctionBasic

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem _root_.GlobalTheory.BesselFunctionBasic.JF_basic : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : _root_.Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r), γ ∈ _root_.BranchingSupport.GG k r → (∀ F F' : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wq →L[ℂ] Wp), (∀ g ∈ _root_.BranchingSupport.GG k r, F g = F' g) → _root_.Formalism.FourierDecayAlt.B.JF D F γ = _root_.Formalism.FourierDecayAlt.B.JF D F' γ ∧ (Integrable (_root_.Formalism.FourierDecayAlt.JF.integrand D F γ) D.μSS → Integrable (_root_.Formalism.FourierDecayAlt.JF.integrand D F' γ) D.μSS)) ∧ (∀ (φ : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r → ℂ) (F : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wq →L[ℂ] Wp)), (∀ p, D.inSS p → φ (_root_.Formalism.FourierDecayAlt.B.sgs p γ) = φ γ) → _root_.Formalism.FourierDecayAlt.B.JF D (fun g => φ g • F g) γ = φ γ • _root_.Formalism.FourierDecayAlt.B.JF D F γ) ∧ (∀ (ι : Type) [Fintype ι] (F : ι → _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wq →L[ℂ] Wp)), (∀ i, Integrable (_root_.Formalism.FourierDecayAlt.JF.integrand D (F i) γ) D.μSS) → _root_.Formalism.FourierDecayAlt.B.JF D (fun g => ∑ i, F i g) γ = ∑ i, _root_.Formalism.FourierDecayAlt.B.JF D (F i) γ) ∧ ∀ᵐ p ∂D.μSS, D.inSS p := by
  intro k r Wp _ _ _ _ Wq _ _ _ _ D γ hγ
  have hJ : ∀ F : _root_.Formalism.FourierDecayAlt.ThreeDimData.Mx k r → (Wq →L[ℂ] Wp),
      _root_.Formalism.FourierDecayAlt.B.JF D F γ = ∫ p, _root_.Formalism.FourierDecayAlt.JF.integrand D F γ p ∂D.μSS := fun F => rfl
  have hae := _root_.Formalism.FourierDecayAlt.P.B6.ae_inSS D
  refine ⟨?_, ?_, ?_, hae⟩
  · intro F F' hF
    have heq : _root_.Formalism.FourierDecayAlt.JF.integrand D F γ =ᵐ[D.μSS] _root_.Formalism.FourierDecayAlt.JF.integrand D F' γ := by
      filter_upwards [hae] with p hp
      simp only [_root_.Formalism.FourierDecayAlt.JF.integrand, _root_.Formalism.FourierDecayAlt.P.B6.rho_eq, hF _ (_root_.Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group D hp hγ)]
    exact ⟨by rw [hJ, hJ]; exact integral_congr_ae heq, fun hi => hi.congr heq⟩
  · intro φ F hφ
    rw [hJ, hJ, ← integral_smul]
    apply integral_congr_ae
    filter_upwards [hae] with p hp
    simp only [_root_.Formalism.FourierDecayAlt.JF.integrand, _root_.Formalism.FourierDecayAlt.P.B6.rho_eq, hφ p hp, map_smul]
    rw [smul_comm]
  · intro ι _ F hF
    simp only [hJ]
    rw [← MeasureTheory.integral_finsetSum _ (fun i _ => hF i)]
    congr 1
    funext p
    simp only [JF.integrand, P.B6.rho_eq, map_sum, Finset.smul_sum]

end GlobalTheory.BesselFunctionBasic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselFunctionLocalityInvariantFactorFiniteSumStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselFunction_locality_invariantFactor_finiteSum : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (γ : Mx k r), γ ∈ GG k r → (∀ F F' : Mx k r → (Wq →L[ℂ] Wp), (∀ g ∈ GG k r, F g = F' g) → B.JF D F γ = B.JF D F' γ ∧ (Integrable (JF.integrand D F γ) D.μSS → Integrable (JF.integrand D F' γ) D.μSS)) ∧ (∀ (φ : Mx k r → ℂ) (F : Mx k r → (Wq →L[ℂ] Wp)), (∀ p, D.inSS p → φ (B.sgs p γ) = φ γ) → B.JF D (fun g => φ g • F g) γ = φ γ • B.JF D F γ) ∧ (∀ (ι : Type) [Fintype ι] (F : ι → Mx k r → (Wq →L[ℂ] Wp)), (∀ i, Integrable (JF.integrand D (F i) γ) D.μSS) → B.JF D (fun g => ∑ i, F i g) γ = ∑ i, B.JF D (F i) γ) ∧ ∀ᵐ p ∂D.μSS, D.inSS p := by
  first | exact @GlobalTheory.BesselFunctionBasic.JF_basic | exact GlobalTheory.BesselFunctionBasic.JF_basic | (intros; apply GlobalTheory.BesselFunctionBasic.JF_basic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNormSqHermTranslatesOrthonormal
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNormSqHermTranslatesOrthonormal
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.MomentParseval

lemma sum_norm_sq_eq {ι : Type} [Fintype ι] (v : ι → ℂ) :
    ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) = v ⬝ᵥ star v := by
  push_cast
  unfold dotProduct
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.mul_conj']

lemma sum_vecMul {ι : Type} [Fintype ι] [DecidableEq ι] (V : Matrix ι ι ℂ) (hV : V * Vᴴ = 1) (y : ι → ℂ) :
    ∑ e, ‖(star y ᵥ* V) e‖ ^ 2 = ∑ i, ‖y i‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [sum_norm_sq_eq, sum_norm_sq_eq, Matrix.star_vecMul, star_star, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, hV, Matrix.one_mulVec, dotProduct_comm]

lemma inv_mem {k r : ℕ} {g : Mx k r} (hg : g ∈ GG k r) : g⁻¹ ∈ GG k r := by
  have e : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  have h1 : g * g⁻¹ = 1 := PI.QuotSetU.UnitaryGroupMassFormula.SW.mul_inv_UH (k := k) (r := r) hg
  have h2 : (g⁻¹)ᴴ * gᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  show (g⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g⁻¹ = Formalism.QuantumDeterminants.Hpk k r
  calc (g⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) * g⁻¹ := by rw [e]
    _ = ((g⁻¹)ᴴ * gᴴ) * Formalism.QuantumDeterminants.Hpk k r * (g * g⁻¹) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

theorem sum_herm_sq : ∀ (k r : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : Mx k r → Matrix ι ι ℂ) (Γ U : Matrix ι ι ℂ) (d : ℕ) (om : ι → ℂ), IsFRep ρ Γ d → U ∈ Matrix.unitaryGroup ι ℂ → ∀ g ∈ GG k r, ∑ e, ‖Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ (fun c => U e c)) om‖ ^ 2 = ∑ i, ‖(ρ g⁻¹ *ᵥ om) i‖ ^ 2 := by
  intro k r ι _ _ ρ Γ U d om hρ hU g hg
  obtain ⟨hΓ, hΓ2, h1, hmul, hinv, -⟩ := hρ
  have hg' := inv_mem hg
  have hgg : g * g⁻¹ = 1 := PI.QuotSetU.UnitaryGroupMassFormula.SW.mul_inv_UH (k := k) (r := r) hg
  have hAB : ρ g * ρ g⁻¹ = 1 := by rw [← hmul g hg _ hg', hgg, h1]
  have hBA : (ρ g⁻¹)ᴴ * (ρ g)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hAB, Matrix.conjTranspose_one]
  have key : Γ * ρ g = (ρ g⁻¹)ᴴ * Γ := by
    calc Γ * ρ g = ((ρ g⁻¹)ᴴ * (ρ g)ᴴ) * Γ * ρ g := by rw [hBA, Matrix.one_mul]
      _ = (ρ g⁻¹)ᴴ * ((ρ g)ᴴ * Γ * ρ g) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hinv g hg]
  have hUU : Uᵀ * (Uᵀ)ᴴ = 1 := by
    have h0 : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff').1 hU
    have h3 := congrArg Matrix.transpose h0
    rw [Matrix.transpose_mul, Matrix.transpose_one] at h3
    exact h3
  have hV : (Γ * Uᵀ) * (Γ * Uᵀ)ᴴ = 1 := by
    rw [Matrix.conjTranspose_mul, hΓ, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hUU, Matrix.one_mul, hΓ2]
  rw [← sum_vecMul (Γ * Uᵀ) hV (ρ g⁻¹ *ᵥ om)]
  refine Finset.sum_congr rfl fun e _ => ?_
  congr 2
  unfold Formalism.QuantumDeterminants.herm
  rw [Matrix.mulVec_mulVec, key, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec,
    Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul]
  rfl

end GlobalTheory.MomentParseval
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SumNormSqHermTranslatesOrthonormalStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_norm_sq_herm_translates_orthonormal : ∀ (k r : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (ρ : Mx k r → Matrix ι ι ℂ) (Γ U : Matrix ι ι ℂ) (d : ℕ) (om : ι → ℂ), IsFRep ρ Γ d → U ∈ Matrix.unitaryGroup ι ℂ → ∀ g ∈ GG k r, ∑ e, ‖Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ (fun c => U e c)) om‖ ^ 2 = ∑ i, ‖(ρ g⁻¹ *ᵥ om) i‖ ^ 2 := by
  first | exact @GlobalTheory.MomentParseval.sum_herm_sq | exact GlobalTheory.MomentParseval.sum_herm_sq | (intros; apply GlobalTheory.MomentParseval.sum_herm_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProductMomentBoundDensityMassOne
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProductMomentBoundDensityMassOne
open MeasureTheory Finset
open scoped ENNReal

namespace GlobalTheory.MomentHolder

theorem lintegral_density {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) (Ph : Ω → ℝ)
    (hPh : AEMeasurable Ph ν) (h0 : ∀ x, 0 ≤ Ph x) (f : Ω → ℝ) (hf : Measurable f) :
    ∫⁻ x, ENNReal.ofReal (f x) ∂(ν.withDensity fun x => ENNReal.ofReal (Ph x))
      = ∫⁻ x, ENNReal.ofReal (f x * Ph x) ∂ν := by
  rw [lintegral_withDensity_eq_lintegral_mul₀ hPh.ennreal_ofReal
    hf.ennreal_ofReal.aemeasurable]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [mul_comm (f x), ENNReal.ofReal_mul (h0 x)]

theorem exists_pos_version {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω) (f : Ω → ℝ)
    (hf : AEMeasurable f ν) (hpos : ∀ᵐ x ∂ν, 0 < f x) :
    ∃ g : Ω → ℝ, Measurable g ∧ (∀ x, 0 < g x) ∧ f =ᵐ[ν] g := by
  classical
  refine ⟨fun x => if 0 < hf.mk f x then hf.mk f x else 1, ?_, ?_, ?_⟩
  · exact Measurable.ite (measurableSet_lt measurable_const hf.measurable_mk)
      hf.measurable_mk measurable_const
  · intro x
    by_cases h : 0 < hf.mk f x <;> simp [h]
  · filter_upwards [hf.ae_eq_mk, hpos] with x hx hp
    rw [← hx, if_pos hp]

theorem product_moment_le :
    ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r : ℕ) (len : Fin (r + 1) → Ω → ℝ)
      (Ph : Ω → ℝ) (A Rr : ℝ), (∀ a, AEMeasurable (len a) ν) → (∀ a, ∀ᵐ x ∂ν, 0 < len a x) →
      AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) → ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν = 1 → 0 ≤ A → 1 ≤ Rr →
      (∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal (len 0 x ^ (2 * q) * Ph x) ∂ν
        ≤ ENNReal.ofReal (A ^ q)) →
      (∀ a : Fin r, ∀ q ≤ (r + 1) ^ 2,
        ∫⁻ x, ENNReal.ofReal ((len a.succ x / len a.castSucc x) ^ (2 * q) * Ph x) ∂ν
          ≤ ENNReal.ofReal (Rr ^ (2 * q))) →
      ∫⁻ x, ENNReal.ofReal ((∏ a, len a x ^ 2) * Ph x) ∂ν
        ≤ ENNReal.ofReal ((A * Rr ^ (2 * r)) ^ (r + 1)) := by
  intro Ω _ ν r len Ph A Rr hm hpos hPh h0 hmass hA hR h1 h2
  choose l hlm hlp hle using fun a => exists_pos_version ν (len a) (hm a) (hpos a)
  have hall : ∀ᵐ x ∂ν, ∀ a, len a x = l a x := ae_all_iff.2 hle
  set μ : Measure Ω := ν.withDensity fun x => ENNReal.ofReal (Ph x) with hμ
  haveI : IsProbabilityMeasure μ := ⟨by
    rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hmass]⟩
  have hR0 : 0 ≤ Rr := zero_le_one.trans hR
  have hsq : ∀ q : ℕ, Real.sqrt A ^ (2 * q) = A ^ q := fun q => by
    rw [pow_mul, Real.sq_sqrt hA]
  have hup := Formalism.HermitianLatticeCounting.P.corollary_upper_estimate_holds Ω μ r (r + 1) l (Real.sqrt A) Rr hlm hlp
    (Real.sqrt_nonneg A) hR0
    (fun q hq => by
      rw [hμ, lintegral_density ν Ph hPh h0 _ ((hlm 0).pow_const _), hsq]
      refine le_of_eq_of_le (lintegral_congr_ae ?_) (h1 q (by rw [sq]; exact hq))
      filter_upwards [hall] with x hx
      rw [hx])
    (fun c q hq => by
      rw [hμ, lintegral_density ν Ph hPh h0
        (fun ω => (l c.succ ω / l c.castSucc ω) ^ (2 * q)) (((hlm _).div (hlm _)).pow_const _)]
      refine le_of_eq_of_le (lintegral_congr_ae ?_) (h2 c q (by rw [sq]; exact hq))
      filter_upwards [hall] with x hx
      rw [hx, hx])
  have hprod := Formalism.HermitianLatticeCounting.P.corollary_product_estimate_holds Ω μ r 1 (r + 1) l (Real.sqrt A * Rr ^ r) hlm hlp
    (by positivity) le_rfl
    (fun a _ => by
      rw [mul_one]
      refine (hup a).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [mul_pow, ← pow_mul Rr r]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR ?_) (by positivity)
      rw [mul_comm r]
      exact Nat.mul_le_mul_left _ (Nat.lt_succ_iff.1 a.isLt))
  have hfilt : univ.filter (fun a : Fin (r + 1) => a.val < r + 1) = univ :=
    filter_true_of_mem fun a _ => a.isLt
  rw [hfilt, hμ, lintegral_density ν Ph hPh h0 _
    ((Finset.measurable_prod _ fun a _ => hlm a).pow_const _)] at hprod
  refine le_of_eq_of_le (lintegral_congr_ae ?_) (hprod.trans_eq ?_)
  · filter_upwards [hall] with x hx
    simp only [hx, mul_one, Finset.prod_pow]
  · congr 1
    rw [mul_one, mul_pow, hsq, mul_pow, ← pow_mul, ← pow_mul]
    congr 2
    ring

end GlobalTheory.MomentHolder
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProductMomentBoundDensityMassOneStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_moment_bound_density_mass_one : ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r : ℕ) (len : Fin (r + 1) → Ω → ℝ) (Ph : Ω → ℝ) (A Rr : ℝ), (∀ a, AEMeasurable (len a) ν) → (∀ a, ∀ᵐ x ∂ν, 0 < len a x) → AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) → ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν = 1 → 0 ≤ A → 1 ≤ Rr → (∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal (len 0 x ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal (A ^ q)) → (∀ a : Fin r, ∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal ((len a.succ x / len a.castSucc x) ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * q))) → ∫⁻ x, ENNReal.ofReal ((∏ a, len a x ^ 2) * Ph x) ∂ν ≤ ENNReal.ofReal ((A * Rr ^ (2 * r)) ^ (r + 1)) := by
  first | exact @GlobalTheory.MomentHolder.product_moment_le | exact GlobalTheory.MomentHolder.product_moment_le | (intros; apply GlobalTheory.MomentHolder.product_moment_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrepDiscreteSeriesSum
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrepDiscreteSeriesSum
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.TensAdj

section
variable {k r : ℕ} {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem hh_sum_left (Γ : Matrix ι ι ℂ) (R : Rep k r) (f : κ → ι → R.H) (y : ι → R.H) :
    hh Γ R (fun c => ∑ I, f I c) y = ∑ I, hh Γ R (f I) y := by
  simp only [hh, inner_sum, Finset.mul_sum]
  rw [Finset.sum_comm (s := (univ : Finset κ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

omit [DecidableEq ι] [DecidableEq κ] in
theorem hh_sum_right (Γ : Matrix ι ι ℂ) (R : Rep k r) (f : κ → ι → R.H) (x : ι → R.H) :
    hh Γ R x (fun c => ∑ I, f I c) = ∑ I, hh Γ R x (f I) := by
  simp only [hh, sum_inner, Finset.mul_sum]
  rw [Finset.sum_comm (s := (univ : Finset κ))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

omit [DecidableEq ι] in
theorem sum_sm (R : Rep k r) (x : ι → R.H) (hx : ∀ c, x c ∈ R.sm) : ∑ c, x c ∈ R.sm :=
  R.smSub.sum_mem (t := univ) (f := x) fun c _ => hx c

omit [DecidableEq ι] in
theorem hh_tm (Γ : Matrix ι ι ℂ) (R : Rep k r) (a : ι → ℂ) (x : ι → R.H) (v : R.H) :
    hh Γ R x (tm R a v) = ⟪v, ev Γ R a x⟫_ℂ := by
  simp only [hh, tm, ev, inner_sum, inner_smul_left, inner_smul_right]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [RCLike.star_def]
  ring

theorem norm_sq_mul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {Γ : Matrix ι ι ℂ}
    (h : Γᴴ * Γ = 1) (x : ι → H) : ∑ i, ‖∑ j, Γ i j • x j‖ ^ 2 = ∑ i, ‖x i‖ ^ 2 := by
  have key : ∑ i, ⟪∑ j, Γ i j • x j, ∑ j, Γ i j • x j⟫_ℂ = ∑ i, ⟪x i, x i⟫_ℂ := by
    simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have h2 : ∀ j, ∑ i, Γ i l * ((starRingEnd ℂ) (Γ i j) * ⟪x j, x l⟫_ℂ)
        = (if j = l then 1 else 0) * ⟪x j, x l⟫_ℂ := by
      intro j
      have := congrFun (congrFun h j) l
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      rw [← this, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [conjTranspose_apply, RCLike.star_def]
      ring
    simp only [h2]
    simp
  simp only [inner_self_eq_norm_sq_to_K] at key
  exact_mod_cast key

theorem norm_hh_le {Γ : Matrix ι ι ℂ} (h : Γᴴ * Γ = 1) (R : Rep k r) (x : ι → R.H) :
    ‖hh Γ R x x‖ ≤ ∑ c, ‖x c‖ ^ 2 := by
  have e : hh Γ R x x = ∑ i, ⟪x i, ∑ j, Γ i j • x j⟫_ℂ := by
    simp only [hh, inner_sum, inner_smul_right]
  have h1 := norm_sq_mul h x
  have h2 : ‖hh Γ R x x‖ ≤ ∑ i, (‖x i‖ ^ 2 + ‖∑ j, Γ i j • x j‖ ^ 2) / 2 := by
    rw [e]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_inner_le_norm _ _).trans ?_
    nlinarith [sq_nonneg (‖x i‖ - ‖∑ j, Γ i j • x j‖)]
  rw [← Finset.sum_div, Finset.sum_add_distrib, h1] at h2
  linarith

variable {ρ : Mx k r → Matrix ι ι ℂ} {Γ : Matrix ι ι ℂ} {R : Rep k r} {RI : κ → Rep k r}
  {io : ∀ I, ι → (RI I).H → R.H} {pr : ∀ I, ι → R.H → (RI I).H} {ep : κ → ℝ}

theorem proj_sm (hT : TensH ρ Γ R RI io pr ep) (I : κ) {x : ι → R.H} (hx : ∀ c, x c ∈ R.sm) :
    ∑ c, pr I c (x c) ∈ (RI I).sm :=
  sum_sm (RI I) _ fun c => (hT.raw.pr_sm I c).mem _ (hx c)

theorem adj (hT : TensH ρ Γ R RI io pr ep) (I : κ) (y : (RI I).H) (hy : y ∈ (RI I).sm) (x : ι → R.H)
    (hx : ∀ c, x c ∈ R.sm) :
    hh Γ R (fun c => io I c y) x = (ep I : ℂ) * ⟪∑ c, pr I c (x c), y⟫_ℂ := by
  have e : (fun c => ∑ J, io J c (∑ d, pr J d (x d))) = x := funext (hT.raw.sum_io_pr x hx)
  conv_lhs => rw [← e]
  rw [hh_sum_right Γ R (fun J c => io J c (∑ d, pr J d (x d))), Finset.sum_eq_single I]
  · exact hT.iso I y hy _ (proj_sm hT I hx)
  · intro J _ hJ
    exact hT.orth I J hJ.symm y hy _ (proj_sm hT J hx)
  · simp

theorem parseval (hT : TensH ρ Γ R RI io pr ep) (x x' : ι → R.H) (hx : ∀ c, x c ∈ R.sm)
    (hx' : ∀ c, x' c ∈ R.sm) :
    hh Γ R x x' = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (x' c), ∑ c, pr I c (x c)⟫_ℂ := by
  have e : (fun c => ∑ J, io J c (∑ d, pr J d (x d))) = x := funext (hT.raw.sum_io_pr x hx)
  conv_lhs => rw [← e]
  rw [hh_sum_left Γ R (fun J c => io J c (∑ d, pr J d (x d)))]
  exact Finset.sum_congr rfl fun I _ => adj hT I _ (proj_sm hT I hx) x' hx'

end

theorem tens_adj : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ I, ∀ y ∈ (RI I).sm, ∀ x : ι → R.H, (∀ c, x c ∈ R.sm) → hh Γ R (fun c => io I c y) x = (ep I : ℂ) * ⟪∑ c, pr I c (x c), y⟫_ℂ) ∧ (∀ x x' : ι → R.H, (∀ c, x c ∈ R.sm) → (∀ c, x' c ∈ R.sm) → hh Γ R x x' = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (x' c), ∑ c, pr I c (x c)⟫_ℂ) ∧ (∀ (a : ι → ℂ) (x : ι → R.H) (v : R.H), hh Γ R x (tm R a v) = ⟪v, ev Γ R a x⟫_ℂ) ∧ (∀ I, ∀ y ∈ (RI I).sm, ‖y‖ ^ 2 ≤ ∑ c, ‖io I c y‖ ^ 2) ∧ ∀ (a a' : ι → ℂ), ∀ v ∈ R.sm, ∀ v' ∈ R.sm, ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ a') a * ⟪v, R.σ g v'⟫_ℂ = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (tm R a v c), (RI I).σ g (∑ c, pr I c (tm R a' v' c))⟫_ℂ := by
  intro _ k r ι κ _ _ _ _ ρ Γ d R RI io pr ep ε mu muI hR _ hF hT
  refine ⟨fun I y hy x hx => adj hT I y hy x hx, fun x x' hx hx' => parseval hT x x' hx hx',
    fun a x v => hh_tm Γ R a x v, ?_, ?_⟩
  · intro I y hy
    have h1 := norm_hh_le (Γ := Γ) (by rw [hF.1, hF.2.1]) R (fun c => io I c y)
    rw [hT.iso I y hy y hy, norm_mul, inner_self_eq_norm_sq_to_K] at h1
    have h2 : ‖(ep I : ℂ)‖ = 1 := by rcases hT.ep_sq I with h | h <;> simp [h]
    rw [h2] at h1
    simpa using h1
  · intro a a' v hv v' hv' g hg
    have ht : ∀ (b : ι → ℂ) (w : R.H), w ∈ R.sm → ∀ c, tm R b w c ∈ R.sm := fun b w hw c =>
      R.smSub.smul_mem (b c) hw
    have hact : ∀ c, act ρ R g (tm R a' v') c ∈ R.sm := fun c =>
      sum_sm R _ fun j => R.smSub.smul_mem _
        (PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε mu R.H R.σ hR.2 _ (ht a' v' hv' j) g hg)
    have hp := parseval hT _ _ hact (ht a v hv)
    simp only [hT.raw.pr_eq _ g hg _ (ht a' v' hv')] at hp
    rw [← hp]
    simp only [hh, act, tm, Formalism.QuantumDeterminants.herm, inner_sum, inner_smul_left, inner_smul_right, map_smul, smul_smul,
      dotProduct, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [Pi.star_apply, RCLike.star_def]
    ring

end GlobalTheory.TensAdj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrepDiscreteSeriesSumStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frep_discrete_series_sum : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ I, ∀ y ∈ (RI I).sm, ∀ x : ι → R.H, (∀ c, x c ∈ R.sm) → hh Γ R (fun c => io I c y) x = (ep I : ℂ) * ⟪∑ c, pr I c (x c), y⟫_ℂ) ∧ (∀ x x' : ι → R.H, (∀ c, x c ∈ R.sm) → (∀ c, x' c ∈ R.sm) → hh Γ R x x' = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (x' c), ∑ c, pr I c (x c)⟫_ℂ) ∧ (∀ (a : ι → ℂ) (x : ι → R.H) (v : R.H), hh Γ R x (tm R a v) = ⟪v, ev Γ R a x⟫_ℂ) ∧ (∀ I, ∀ y ∈ (RI I).sm, ‖y‖ ^ 2 ≤ ∑ c, ‖io I c y‖ ^ 2) ∧ ∀ (a a' : ι → ℂ), ∀ v ∈ R.sm, ∀ v' ∈ R.sm, ∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ a') a * ⟪v, R.σ g v'⟫_ℂ = ∑ I, (ep I : ℂ) * ⟪∑ c, pr I c (tm R a v c), (RI I).σ g (∑ c, pr I c (tm R a' v' c))⟫_ℂ := by
  first | exact @GlobalTheory.TensAdj.tens_adj | exact GlobalTheory.TensAdj.tens_adj | (intros; apply GlobalTheory.TensAdj.tens_adj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFrameConjUnitaryBlockEqUnitaryComplement
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFrameConjUnitaryBlockEqUnitaryComplement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselFrame

open Formalism.FourierDecayAlt.P.SettingConstruction

section forms
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)

lemma quasi_reflection (hH : Hᴴ = H) (u v : ι → ℂ)
    (huv : Formalism.QuantumDeterminants.herm H u u = Formalism.QuantumDeterminants.herm H v v)
    (hne : Formalism.QuantumDeterminants.herm H u u ≠ Formalism.QuantumDeterminants.herm H u v) :
    ∃ g : Matrix ι ι ℂ, gᴴ * H * g = H ∧ g *ᵥ u = v ∧
      ∀ x, Formalism.QuantumDeterminants.herm H x u = 0 → Formalism.QuantumDeterminants.herm H x v = 0 → g *ᵥ x = x := by
  set d := u - v with hd
  set s := Formalism.QuantumDeterminants.herm H u d with hs
  have hs' : s = Formalism.QuantumDeterminants.herm H u u - Formalism.QuantumDeterminants.herm H u v := by rw [hs, hd, herm_sub_right]
  have hs0 : s ≠ 0 := by rw [hs']; exact sub_ne_zero.mpr hne
  have hss : star s = Formalism.QuantumDeterminants.herm H u u - Formalism.QuantumDeterminants.herm H v u := by
    rw [hs, herm_symm H hH, hd, herm_sub_left]
  have hq : Formalism.QuantumDeterminants.herm H d d = s + star s := by
    rw [hss, hs', hd]
    simp only [herm_sub_left, herm_sub_right]
    linear_combination -huv
  set a : ℂ := s⁻¹ with ha'
  have ha : a * s = 1 := inv_mul_cancel₀ hs0
  have hsa : star a * star s = 1 := by rw [← star_mul', ha, star_one]
  refine ⟨rk H d 1 (-a), unitary_of_form H _ fun x y => ?_, ?_, fun x hxu hxv => ?_⟩
  · rw [rk_mulVec, rk_mulVec]
    have hY : star (Formalism.QuantumDeterminants.herm H y d) = Formalism.QuantumDeterminants.herm H d y := herm_symm H hH y d
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, star_mul', hY, hq,
      star_neg, star_one]
    linear_combination (star a * Formalism.QuantumDeterminants.herm H x d * Formalism.QuantumDeterminants.herm H d y) * ha +
      (a * Formalism.QuantumDeterminants.herm H x d * Formalism.QuantumDeterminants.herm H d y) * hsa
  · rw [rk_mulVec, ← hs, neg_mul, ha, hd]
    simp
  · rw [rk_mulVec, hd, herm_sub_right, hxu, hxv]
    simp

lemma exists_isometry (hH : Hᴴ = H) (u v : ι → ℂ)
    (huv : Formalism.QuantumDeterminants.herm H u u = Formalism.QuantumDeterminants.herm H v v) (h0 : Formalism.QuantumDeterminants.herm H u u ≠ 0) :
    ∃ g : Matrix ι ι ℂ, gᴴ * H * g = H ∧ g *ᵥ u = v ∧
      ∀ x, Formalism.QuantumDeterminants.herm H x u = 0 → Formalism.QuantumDeterminants.herm H x v = 0 → g *ᵥ x = x := by
  by_cases hne : Formalism.QuantumDeterminants.herm H u u = Formalism.QuantumDeterminants.herm H u v
  swap
  · exact quasi_reflection H hH u v huv hne
  have e1 : Formalism.QuantumDeterminants.herm H ((-1 : ℂ) • u) ((-1 : ℂ) • u) = Formalism.QuantumDeterminants.herm H u u := by
    simp only [herm_smul_left, herm_smul_right]; simp
  obtain ⟨g₁, h1, h2, h3⟩ := quasi_reflection H hH u ((-1 : ℂ) • u) e1.symm (by
    rw [herm_smul_right]
    intro h; apply h0
    simp only [star_neg, star_one] at h
    linear_combination h / 2)
  obtain ⟨g₂, k1, k2, k3⟩ := quasi_reflection H hH ((-1 : ℂ) • u) v (e1.trans huv) (by
    rw [e1, herm_smul_left, ← hne]
    intro h; apply h0
    linear_combination h / 2)
  refine ⟨g₂ * g₁, ?_, ?_, fun x hxu hxv => ?_⟩
  · calc (g₂ * g₁)ᴴ * H * (g₂ * g₁) = g₁ᴴ * (g₂ᴴ * H * g₂) * g₁ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [k1, h1]
  · rw [← Matrix.mulVec_mulVec, h2, k2]
  · have : Formalism.QuantumDeterminants.herm H x ((-1 : ℂ) • u) = 0 := by rw [herm_smul_right, hxu, mul_zero]
    rw [← Matrix.mulVec_mulVec, h3 x hxu this, k3 x this hxv]

end forms

open PI.UpqRep PI.HwUniqW

variable {k r : ℕ}

lemma herm_right_bvec (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    Formalism.QuantumDeterminants.herm (Hpk k r) y (bvec i) = epsI k r i * y (piI k r i) := by
  rw [← Hpk_mulVec_apply]
  simp [Formalism.QuantumDeterminants.herm, bvec, Pi.star_single]

lemma herm_bvec_eq_zero {y : Fin (2 * r + k + 1) → ℂ} (hy : inWb k r y) {i : Fin (2 * r + k + 1)}
    (hi : i.val < r ∨ r + k < i.val) : Formalism.QuantumDeterminants.herm (Hpk k r) (bvec i) y = 0 := by
  rw [← herm_symm _ Hpk_conjTranspose, herm_right_bvec, hy (piI k r i), mul_zero, star_zero]
  rw [piI_val]
  have := i.isLt
  split_ifs <;> omega

lemma exists_isFrameW (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z) :
    ∃ g, IsFrameW k r z g := by
  set T := Tz k r z with hTdef
  set u : Fin (2 * r + k + 1) → ℂ := ((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k)) with hu
  have hw : Formalism.QuantumDeterminants.herm (Hpk k r) (bvec (wI k r (Fin.last k))) (bvec (wI k r (Fin.last k))) = -1 := by
    have hp : piI k r (wI k r (Fin.last k)) = wI k r (Fin.last k) := by
      unfold piI; rw [if_pos (by simp [wI])]
    rw [herm_right_bvec, hp, bvec_apply, if_pos rfl]
    simp [epsI, wI]
  have huu : Formalism.QuantumDeterminants.herm (Hpk k r) u u = -(T : ℂ) := by
    rw [hu, herm_smul_left, herm_smul_right, hw]
    have h1 : star ((Real.sqrt T : ℝ) : ℂ) = ((Real.sqrt T : ℝ) : ℂ) := Complex.conj_ofReal _
    have h2 : ((Real.sqrt T : ℝ) : ℂ) * ((Real.sqrt T : ℝ) : ℂ) = (T : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hT.le]
    rw [h1]
    linear_combination -h2
  have hzz : Formalism.QuantumDeterminants.herm (Hpk k r) z z = -(T : ℂ) := by
    have h1 : star (Formalism.QuantumDeterminants.herm (Hpk k r) z z) = Formalism.QuantumDeterminants.herm (Hpk k r) z z :=
      herm_symm _ Hpk_conjTranspose z z
    have h2 : T = -(Formalism.QuantumDeterminants.herm (Hpk k r) z z).re := rfl
    rw [h2, Complex.ofReal_neg, neg_neg]
    exact (Complex.conj_eq_iff_re.mp h1).symm
  have huW : inWb k r u := by
    intro i hi
    rw [hu, Pi.smul_apply, bvec_apply, if_neg, smul_zero]
    rintro rfl
    simp [wI] at hi
  obtain ⟨g, h1, h2, h3⟩ := exists_isometry (Hpk k r) Hpk_conjTranspose u z (huu.trans hzz.symm) (by
    rw [huu, neg_ne_zero]; exact_mod_cast hT.ne')
  refine ⟨g, h1, fun a => ⟨?_, ?_⟩, h2⟩
  · have ha : (eI k r a).val < r ∨ r + k < (eI k r a).val := Or.inl a.isLt
    exact h3 _ (herm_bvec_eq_zero huW ha) (herm_bvec_eq_zero hz ha)
  · have ha : (esI k r a).val < r ∨ r + k < (esI k r a).val := by
      have := a.isLt
      right; simp only [esI]; omega
    exact h3 _ (herm_bvec_eq_zero huW ha) (herm_bvec_eq_zero hz ha)

lemma blockW_fix (x : Matrix (Fin k) (Fin k) ℂ) {j : Fin (2 * r + k + 1)} (hj : ¬ InB k r j) :
    blockW k r x *ᵥ bvec j = bvec j := by
  funext i
  rw [mulVec_bvec_apply, bvec_apply]
  by_cases hi : InB k r i
  · rw [blockW_in_out _ hi hj, if_neg (ne_of_inB hi hj)]
  · rw [blockW_out _ hi]

lemma blockW_mem_UH {x : Matrix (Fin k) (Fin k) ℂ} (hx : x ∈ UJset (allPos k)) :
    blockW k r x ∈ UH (Hpk k r) := by
  show (blockW k r x)ᴴ * Hpk k r * blockW k r x = Hpk k r
  rw [blockW_conjTranspose, ← Hpk_blockW_comm, Matrix.mul_assoc, blockW_mul, mem_UJset_allPos.mp hx,
    blockW_one, Matrix.mul_one]

lemma conj_mem_UW {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : IsFrameW k r z g) {x : Matrix (Fin k) (Fin k) ℂ} (hx : x ∈ UJset (allPos k)) :
    g * blockW k r x * g⁻¹ ∈ UWset k r z := by
  refine ⟨mul_mem_UH (mul_mem_UH hg.1 (blockW_mem_UH hx)) (inv_mem_UH hg.1), fun a => ⟨?_, ?_⟩, ?_⟩
  · have := a.isLt
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, inv_fix hg.1 (hg.2.1 a).1,
      blockW_fix x (by unfold InB eI; simp only; omega), (hg.2.1 a).1]
  · have := a.isLt
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, inv_fix hg.1 (hg.2.1 a).2,
      blockW_fix x (by unfold InB esI; simp only; omega), (hg.2.1 a).2]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, frame_inv_mulVec_negativeVector hg, Matrix.mulVec_smul,
      blockW_fix x (by unfold InB wI; simp), hg.2.2]

theorem frame_exists : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → ∃ g, PI.UpqRep.IsFrameW k r z g ∧ (∀ x ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), g * PI.UpqRep.blockW k r x * g⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z) ∧ ∀ y ∈ Formalism.QuantumDeterminants.UWset k r z, ∃ x ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), y = g * PI.UpqRep.blockW k r x * g⁻¹ := by
  intro k r z hz hT
  have hT' : 0 < PI.UpqRep.Tz k r z := hT
  obtain ⟨g, hg⟩ := exists_isFrameW z hz hT'
  refine ⟨g, hg, fun x hx => conj_mem_UW hg hx, fun y hy => ?_⟩
  obtain ⟨x, hx, -, e⟩ := UW_eq_conj hT' hg hy
  exact ⟨x, hx, e⟩

end GlobalTheory.BesselFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFrameConjUnitaryBlockEqUnitaryComplementStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_conj_unitaryBlock_eq_unitaryComplement : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → ∃ g, PI.UpqRep.IsFrameW k r z g ∧ (∀ x ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), g * PI.UpqRep.blockW k r x * g⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z) ∧ ∀ y ∈ Formalism.QuantumDeterminants.UWset k r z, ∃ x ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), y = g * PI.UpqRep.blockW k r x * g⁻¹ := by
  first | exact @GlobalTheory.BesselFrame.frame_exists | exact GlobalTheory.BesselFrame.frame_exists | (intros; apply GlobalTheory.BesselFrame.frame_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsKTypeNonzeroBessel
section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsKTypeNonzeroBessel
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem bessel_nonzero_on_translates : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (l : R.H → Wp), R.IsDS ε mu → IsBes R z π l → NzOn R l → ∃ v ∈ R.TK, l v ≠ 0 := by
  intro hH k r ε mu R Wp _ _ _ _ z π l hds hB hnz
  obtain ⟨⟨-, -, hKF, -⟩, hCyc, -⟩ := hH
  have hex : ∃ w0, PI.UpqRep.IsLowUnitH k r ε mu R.σ w0 := by
    obtain ⟨P, hP, -, -, -, -, -, ⟨S, hS⟩, -⟩ := hds.2
    obtain ⟨v, hvS, hv0, -⟩ := hS.2.2.2.1
    have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
    refine ⟨((‖v‖⁻¹ : ℝ) : ℂ) • v, P, hP, ?_, ?_⟩
    · rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    · exact Submodule.smul_mem _ _ (Submodule.mem_sSup.mpr fun N hN => hN S hS hvS)
  obtain ⟨w0, hlow⟩ := hex
  have hwK : R.KFin w0 := PI.UnitaryGroupMassFormula.LowSmooth.isKFinHpk_of_lowUnit hlow
  by_contra hcon
  push_neg at hcon
  obtain ⟨w, hw, hlw⟩ := hnz
  refine hlw (Formalism.FourierDecayAlt.P.bessel_ne_zero_of_cyclic_orbit hCyc hKF k r ε mu R.H R.σ w0 Wp z Formalism.QuantumDeterminants.cStd π hds.1 hds.2 hlow
    l hB (fun x hx => hcon x ?_) w hw)
  refine Submodule.span_mono ?_ hx
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g, hg, w0, hwK, rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsKTypeNonzeroBesselStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_K_type_nonzero_bessel : Hyps → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (l : R.H → Wp), R.IsDS ε mu → IsBes R z π l → NzOn R l → ∃ v ∈ R.TK, l v ≠ 0 := by
  first | exact @GlobalTheory.bessel_nonzero_on_translates | exact GlobalTheory.bessel_nonzero_on_translates | (intros; apply GlobalTheory.bessel_nonzero_on_translates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.EqSmulOfTwoSided
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.UnipotentRadicalHaar

theorem eq_smul_of_twoSided {k r : ℕ} {U : Set (B.Mat k r)} (hU : B2.IsClosedSubgroup U)
    {μ ν : Measure (Formalism.QuantumDeterminants.Mt k r)} (hμ : PI.BesselPeriodGGP.IsHaarOn U μ) (hν : B.IsHaarOn U ν) :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ μ = c • ν := by
  have : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => hν.finite_compact K hK⟩
  obtain ⟨c, -, c1, e⟩ := GlobalTheory.BesselPeriodCompare.haar_unique hU hμ
    (ν := ν) ⟨inferInstance, hν.ne_zero, hν.conc, hν.left⟩
  exact ⟨c, c1, e⟩

theorem unimodular_normal : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN → PI.IsRightInvM (Formalism.QuantumDeterminants.UWset k r z) μW ∧ IsFiniteMeasure μW ∧ PI.IsRightInvM (Formalism.QuantumDeterminants.Nset k r) μN ∧ (∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, ∀ m ∈ Formalism.QuantumDeterminants.Nset k r, h * m * h⁻¹ ∈ Formalism.QuantumDeterminants.Nset k r) ∧ ∀ h ∈ Formalism.QuantumDeterminants.UWset k r z, μN.map (fun x : Formalism.QuantumDeterminants.Mt k r => (fun i j => (h * Matrix.of x * h⁻¹) i j : Formalism.QuantumDeterminants.Mt k r)) = μN := by
  intro k r z μW μN hz hT hW hN
  obtain ⟨νW, hνW⟩ := P.weyl_haar_exists k r z hz hT
  obtain ⟨νN, hνN⟩ := P.unipotent_haar_exists k r
  obtain ⟨a, a1, ea⟩ := eq_smul_of_twoSided (P.B2x3.closedW k r z) hW hνW
  obtain ⟨b, -, eb⟩ := eq_smul_of_twoSided (P.B2x2.closedN k r) hN hνN
  refine ⟨fun s hs => ?_, ⟨?_⟩, fun s hs => ?_,
    fun h hh m hm => (Formalism.QuantumDeterminants.uWNormal k r z hz h hh m hm).1, fun h hh => ?_⟩
  · rw [ea, Measure.map_smul _ (by
      apply Continuous.aemeasurable
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [PI.rmulQ, Matrix.mul_apply, Matrix.of_apply]
      fun_prop)]
    exact congrArg (a • ·) (hνW.right s hs)
  · have hK : IsCompact (Formalism.QuantumDeterminants.UWset k r z) := P.weyl_subgroup_compact k r z hz hT
    have h1 : νW (Formalism.QuantumDeterminants.UWset k r z) < ⊤ := hνW.finite_compact _ hK
    have h2 : νW Set.univ ≤ νW (Formalism.QuantumDeterminants.UWset k r z) + νW (Formalism.QuantumDeterminants.UWset k r z)ᶜ :=
      measure_univ_le_add_compl _
    have h3 : νW (Formalism.QuantumDeterminants.UWset k r z)ᶜ = 0 := hνW.conc
    rw [h3, add_zero] at h2
    rw [ea, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top a1.lt_top (h2.trans_lt h1)
  · rw [eb, Measure.map_smul _ (by
      apply Continuous.aemeasurable
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [PI.rmulQ, Matrix.mul_apply, Matrix.of_apply]
      fun_prop)]
    exact congrArg (b • ·) (hνN.right s hs)
  · rw [eb, Measure.map_smul _ (by
      apply Continuous.aemeasurable
      refine continuous_pi fun i => continuous_pi fun j => ?_
      simp only [Matrix.mul_apply, Matrix.of_apply]
      fun_prop)]
    exact congrArg (b • ·) (P.b2_conjInvRaw_proof k r z νN hz hT hνN h hh)

end GlobalTheory.UnipotentRadicalHaar
end
