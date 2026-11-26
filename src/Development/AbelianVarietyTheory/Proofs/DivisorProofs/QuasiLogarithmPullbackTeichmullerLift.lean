module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstSubSubstIntegralOfIntegralDifferential
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffSubstLeadingOfAgreeDegreeOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompEqOneOfTransl
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JTEqAndPowTwelveEqDD
public import Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightMemWZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPullbackTeichmullerLift
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPullbackTeichmullerLift
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.KatzPull

open GlobalTheory.Katz

theorem lift_X (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p] {σ : Type} (s : σ) :
    Katz.lift p (X s : MvPowerSeries σ k) = X s := by
  classical
  ext α
  rw [coeff_lift, coeff_X, coeff_X]
  split_ifs
  · rw [map_one, map_one]
  · rw [WittVector.teichmuller_zero, map_zero]

theorem lin_subst {R : Type} [CommRing R] {d e : ℕ} (a : Fin e → MvPowerSeries (Fin d) R)
    (ha : ∀ j, constantCoeff (a j) = 0) (f : MvPowerSeries (Fin e) R) :
    lin (subst a f) = pullLin a (lin f) := by
  classical
  have ha' := hasSubst_of_constantCoeff_zero ha
  have hcard : ∀ α : Fin e →₀ ℕ, Multiset.card (Finsupp.toMultiset α) = α.degree := fun α => by
    rw [Finsupp.card_toMultiset, Finsupp.degree]; rfl
  have inj : Function.Injective (Finsupp.toMultiset : (Fin e →₀ ℕ) → Multiset (Fin e)) :=
    fun x y hxy => by simpa using congrArg Multiset.toFinsupp hxy
  set f1 : MvPowerSeries (Fin e) R := C (constantCoeff f) + ∑ j, C (lin f j) * X j with hf1
  have hf2 : ∀ α : Fin e →₀ ℕ, α.degree < 2 → coeff α (f - f1) = 0 := by
    intro α hα
    rcases (show α.degree = 0 ∨ α.degree = 1 by omega) with h | h
    · have h0 : α = 0 := by
        apply inj
        rw [map_zero, ← Multiset.card_eq_zero, hcard, h]
      subst h0
      simp [hf1, coeff_X]
    · obtain ⟨j, hj⟩ := Multiset.card_eq_one.1 ((hcard α).trans h)
      have h1 : α = Finsupp.single j 1 := by
        apply inj
        rw [hj, Finsupp.toMultiset_single, one_smul]
      subst h1
      simp [hf1, coeff_X, coeff_C, lin, Finsupp.single_eq_single_iff]
  funext i
  have key := (GlobalTheory.T.coeff_subst_leading_of_agree_degree_one R (Fin e) (Fin d) a a 2 (f - f1) ha ha (fun _ _ _ => rfl) hf2
    (Finsupp.single i 1)).1 (by rw [Finsupp.degree_single]; norm_num)
  rw [subst_sub ha', map_sub, sub_eq_zero] at key
  unfold lin pullLin
  set_option synthInstance.maxHeartbeats 100000 in
    rw [key, hf1, subst_add ha', subst_C, map_add (f := _), coeff_C, if_neg (Finsupp.single_ne_zero.2 one_ne_zero),
    zero_add, ← coe_substAlgHom ha', map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, coe_substAlgHom ha', subst_C, subst_X ha', coeff_C_mul]
  rfl

theorem quasiLog_pull : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d e : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k) (hμ : IsLaw μ) (hν : IsLaw ν) (φ : Fin e → MvPowerSeries (Fin d) k), IsHom μ ν φ → ∀ f ∈ quasiLog p hν, subst (fun j => Katz.lift p (φ j)) f ∈ quasiLog p hμ ∧ (∀ c, Red p (cob1 (fun j => Katz.lift p (ν j)) f) c → Red p (cob1 (fun i => Katz.lift p (μ i)) (subst (fun j => Katz.lift p (φ j)) f)) (pull2 φ c)) ∧ ∀ w, RedV p (lin f) w → RedV p (lin (subst (fun j => Katz.lift p (φ j)) f)) (pullLin φ w) := by
  intro p _ k _ _ _ d e μ ν hμ hν φ hφ f hf
  obtain ⟨hf1, hf2⟩ := hf
  have hΦ0 : ∀ j, constantCoeff (Katz.lift p (φ j)) = 0 := fun j => constantCoeff_lift p (hφ.const j)
  have hΦs : HasSubst (fun j => Katz.lift p (φ j)) := hasSubst_of_constantCoeff_zero hΦ0
  have hLμ0 : ∀ i, constantCoeff (Katz.lift p (μ i)) = 0 := fun i => constantCoeff_lift p (hμ.const i)
  have hLμs : HasSubst (fun i => Katz.lift p (μ i)) := hasSubst_of_constantCoeff_zero hLμ0
  have hLν0 : ∀ i, constantCoeff (Katz.lift p (ν i)) = 0 := fun i => constantCoeff_lift p (hν.const i)
  have hXl0 : ∀ i : Fin d, constantCoeff (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k)) = 0 :=
    fun _ => constantCoeff_X _
  have hXr0 : ∀ i : Fin d, constantCoeff (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) (Fr p k)) = 0 :=
    fun _ => constantCoeff_X _
  have hXls := hasSubst_of_constantCoeff_zero hXl0
  have hXrs := hasSubst_of_constantCoeff_zero hXr0
  have RR := fun σ => GlobalTheory.T.mvPowerSeries_reduction_mod_prime_rules p k σ
  have hRedΦ : ∀ j, Red p (Katz.lift p (φ j)) (φ j) := fun j => (RR _).2.2.1 (φ j)
  have redX : ∀ {σ : Type} (s : σ), Red p (X s : MvPowerSeries σ (Fr p k)) (X s) := fun s => by
    simpa [lift_X] using (RR _).2.2.1 (X s : MvPowerSeries _ k)
  have hIL := GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin d) (Fin d ⊕ Fin d) (fun i => X (Sum.inl i)) (fun i => X (Sum.inl i))
    hXl0 (fun i => redX _)
  have hIR := GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin d) (Fin d ⊕ Fin d) (fun i => X (Sum.inr i)) (fun i => X (Sum.inr i))
    hXr0 (fun i => redX _)

  set U : Fin e ⊕ Fin e → MvPowerSeries (Fin d ⊕ Fin d) (Fr p k) :=
    Sum.elim (fun j => inL (Katz.lift p (φ j))) (fun j => inR (Katz.lift p (φ j))) with hU
  set U' : Fin e ⊕ Fin e → MvPowerSeries (Fin d ⊕ Fin d) k :=
    Sum.elim (fun j => inL (φ j)) (fun j => inR (φ j)) with hU'
  have hinL0 : ∀ j, constantCoeff (inL (Katz.lift p (φ j))) = 0 := fun j =>
    constantCoeff_subst_eq_zero hXls hXl0 (hΦ0 j)
  have hinR0 : ∀ j, constantCoeff (inR (Katz.lift p (φ j))) = 0 := fun j =>
    constantCoeff_subst_eq_zero hXrs hXr0 (hΦ0 j)
  have hU0 : ∀ s, constantCoeff (U s) = 0 := by
    rintro (j | j)
    · exact hinL0 j
    · exact hinR0 j
  have hRedU : ∀ s, Red p (U s) (U' s) := by
    rintro (j | j)
    · exact hIL.1 _ _ (hRedΦ j)
    · exact hIR.1 _ _ (hRedΦ j)
  have hIU := GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin e ⊕ Fin e) (Fin d ⊕ Fin d) U U' hU0 hRedU
  have C6 := GlobalTheory.T.powerSeriesEvalTwoGroups_rules (Fr p k) e (Fin d ⊕ Fin d) (Fin d ⊕ Fin d)
    (fun j => inL (Katz.lift p (φ j))) (fun j => inR (Katz.lift p (φ j))) hinL0 hinR0

  set A : Fin e → MvPowerSeries (Fin d ⊕ Fin d) (Fr p k) :=
    fun j => subst (fun i => Katz.lift p (μ i)) (Katz.lift p (φ j)) with hA
  set B : Fin e → MvPowerSeries (Fin d ⊕ Fin d) (Fr p k) :=
    fun j => subst U (Katz.lift p (ν j)) with hB
  have hA0 : ∀ j, constantCoeff (A j) = 0 := fun j => constantCoeff_subst_eq_zero hLμs hLμ0 (hΦ0 j)
  have hB0 : ∀ j, constantCoeff (B j) = 0 := fun j =>
    constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hU0) hU0 (hLν0 j)
  have hRA : ∀ j, Red p (A j) (subst μ (φ j)) := fun j =>
    (GlobalTheory.T.isIntegralReducingToMvPowerSeries_subst p k (Fin d) (Fin d ⊕ Fin d) _ μ hLμ0 (fun i => (RR _).2.2.1 (μ i))).1 _ _ (hRedΦ j)
  have hRB : ∀ j, Red p (B j) (subst μ (φ j)) := fun j => by
    rw [hφ.hom j]
    exact hIU.1 _ _ ((RR _).2.2.1 (ν j))
  have hD := GlobalTheory.T.subst_sub_subst_integral_of_integral_differential p k (Fin e) (Fin d ⊕ Fin d) A B (fun j => subst μ (φ j)) f hA0 hB0 hRA hRB hf1

  have hid : cob1 (fun i => Katz.lift p (μ i)) (subst (fun j => Katz.lift p (φ j)) f) =
      (subst A f - subst B f) + subst U (cob1 (fun j => Katz.lift p (ν j)) f) := by
    have e1 : subst U (cob1 (fun j => Katz.lift p (ν j)) f) =
        subst B f - subst (fun j => inL (Katz.lift p (φ j))) f - subst (fun j => inR (Katz.lift p (φ j))) f := by
      change at2 (cob1 (fun j => Katz.lift p (ν j)) f) _ _ = _
      unfold cob1
      rw [(C6.2.2.1 _ _).2, (C6.2.2.1 _ _).2, C6.1, C6.2.1, C6.2.2.2.2.2.1 e _ hLν0]
      rfl
    rw [e1]
    unfold cob1 inL inR
    rw [subst_comp_subst_apply hΦs hLμs, subst_comp_subst_apply hΦs hXls,
      subst_comp_subst_apply hΦs hXrs]
    abel
  have part2 : ∀ c, Red p (cob1 (fun j => Katz.lift p (ν j)) f) c →
      Red p (cob1 (fun i => Katz.lift p (μ i)) (subst (fun j => Katz.lift p (φ j)) f)) (pull2 φ c) := by
    intro c hc
    rw [hid]
    have h1 := ((RR _).2.2.2.2.2.1 _).1 hD
    have h2 := hIU.1 _ _ hc
    have := ((RR _).2.2.2.1 _ _ _ _ h1 h2).1
    rwa [zero_add] at this
  refine ⟨⟨GlobalTheory.T.subst_mem_integralDifferentialSubmodule p k (Fin e) (Fin d) _ f hΦ0
      (fun j => ((RR _).1 _).2 ⟨φ j, hRedΦ j⟩) hf1, ?_⟩, part2, ?_⟩
  · obtain ⟨c, hc⟩ := ((RR _).1 _).1 hf2
    exact ((RR _).1 _).2 ⟨_, part2 c hc⟩
  · intro w hw i
    rw [lin_subst _ hΦ0]
    choose a ha ha' using hw
    refine ⟨∑ j, a j * WittVector.teichmuller p (lin (φ j) i), ?_, ?_⟩
    · simp only [pullLin, map_sum, map_mul, ha]
      simp only [lin, coeff_lift]
    · simp only [pullLin, ← WittVector.constantCoeff_apply, map_sum, map_mul,
        WittVector.constantCoeff_apply, ha', WittVector.teichmuller_coeff_zero]

end GlobalTheory.KatzPull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmPullbackTeichmullerLiftStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiLogarithm_pullback_teichmullerLift : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d e : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (ν : Fin e → MvPowerSeries (Fin e ⊕ Fin e) k) (hμ : IsLaw μ) (hν : IsLaw ν) (φ : Fin e → MvPowerSeries (Fin d) k), IsHom μ ν φ → ∀ f ∈ quasiLog p hν, subst (fun j => Katz.lift p (φ j)) f ∈ quasiLog p hμ ∧ (∀ c, Red p (cob1 (fun j => Katz.lift p (ν j)) f) c → Red p (cob1 (fun i => Katz.lift p (μ i)) (subst (fun j => Katz.lift p (φ j)) f)) (pull2 φ c)) ∧ ∀ w, RedV p (lin f) w → RedV p (lin (subst (fun j => Katz.lift p (φ j)) f)) (pullLin φ w) := by
  first | exact @GlobalTheory.KatzPull.quasiLog_pull | exact GlobalTheory.KatzPull.quasiLog_pull | (intros; apply GlobalTheory.KatzPull.quasiLog_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylRestrictionRowOperators
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylRestrictionRowOperators
open MvPolynomial Formalism.GradedWeylDivisibility TensorProduct

noncomputable section

namespace GlobalTheory.LeviCut

theorem rTensor_der_mul {A B : Type} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    (D : Derivation ℚ A A) (x y : A ⊗[ℚ] B) :
    LinearMap.rTensor B (D : A →ₗ[ℚ] A) (x * y) =
      x * LinearMap.rTensor B (D : A →ₗ[ℚ] A) y + y * LinearMap.rTensor B (D : A →ₗ[ℚ] A) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.rTensor_tmul, Derivation.coeFn_coe,
        Derivation.leibniz, smul_eq_mul, add_tmul]
      rw [mul_comm b' b]
    | add y y' hy hy' => simp only [mul_add, map_add (f := _), hy, hy', add_mul]; abel
  | add x x' hx hx' => simp only [add_mul, mul_add, map_add (f := _), hx, hx']; abel

theorem lTensor_der_mul {A B : Type} [CommRing A] [Algebra ℚ A] [CommRing B] [Algebra ℚ B]
    (D : Derivation ℚ B B) (x y : A ⊗[ℚ] B) :
    LinearMap.lTensor A (D : B →ₗ[ℚ] B) (x * y) =
      x * LinearMap.lTensor A (D : B →ₗ[ℚ] B) y + y * LinearMap.lTensor A (D : B →ₗ[ℚ] B) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a' b' =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.lTensor_tmul, Derivation.coeFn_coe,
        Derivation.leibniz, smul_eq_mul, tmul_add]
      rw [mul_comm a' a]
    | add y y' hy hy' => simp only [mul_add, map_add (f := _), hy, hy', add_mul]; abel
  | add x x' hx hx' => simp only [add_mul, mul_add, map_add (f := _), hx, hx']; abel

theorem natAdd_ne_castAdd' {p q : ℕ} (b : Fin q) (d : Fin p) : Fin.natAdd p b ≠ Fin.castAdd q d := by
  rw [Ne, Fin.ext_iff]; simp only [Fin.coe_natAdd, Fin.coe_castAdd]; omega

theorem castAdd_ne_natAdd' {p q : ℕ} (a : Fin p) (d : Fin q) : Fin.castAdd q a ≠ Fin.natAdd p d := by
  rw [Ne, Fin.ext_iff]; simp only [Fin.coe_natAdd, Fin.coe_castAdd]; omega

theorem resT_der_left_X (p q : ℕ) (c d : Fin p) (v : Fin (p + q) × Fin (p + q)) :
    resT ℚ p q (Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.castAdd q c) (Fin.castAdd q d) (X v)) =
      LinearMap.rTensor _ (Formalism.CohomologicalDescent.LR.der p p c d : Module.End ℚ (MvPolynomial (Fin p × Fin p) ℚ))
        (resT ℚ p q (X v)) := by
  obtain ⟨v1, v2⟩ := v
  rw [Formalism.CohomologicalDescent.LR.der_X]
  induction v1 using Fin.addCases with
  | left a =>
    induction v2 using Fin.addCases with
    | left s =>
      by_cases h : a = d
      · subst h; simp [resT, resVarT, Formalism.CohomologicalDescent.LR.der_X]
      · simp [resT, resVarT, Formalism.CohomologicalDescent.LR.der_X, h]
    | right t =>
      by_cases h : a = d
      · subst h; simp [resT, resVarT]
      · simp [resT, resVarT, h]
  | right b =>
    rw [if_neg (natAdd_ne_castAdd' b d)]
    induction v2 using Fin.addCases with
    | left s => simp [resT, resVarT]
    | right t => simp [resT, resVarT]

theorem resT_der_right_X (p q : ℕ) (c d : Fin q) (v : Fin (p + q) × Fin (p + q)) :
    resT ℚ p q (Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.natAdd p c) (Fin.natAdd p d) (X v)) =
      LinearMap.lTensor _ (Formalism.CohomologicalDescent.LR.der q q c d : Module.End ℚ (MvPolynomial (Fin q × Fin q) ℚ))
        (resT ℚ p q (X v)) := by
  obtain ⟨v1, v2⟩ := v
  rw [Formalism.CohomologicalDescent.LR.der_X]
  induction v1 using Fin.addCases with
  | left a =>
    rw [if_neg (castAdd_ne_natAdd' a d)]
    induction v2 using Fin.addCases with
    | left s => simp [resT, resVarT]
    | right t => simp [resT, resVarT]
  | right b =>
    induction v2 using Fin.addCases with
    | left s =>
      by_cases h : b = d
      · subst h; simp [resT, resVarT]
      · simp [resT, resVarT, h]
    | right t =>
      by_cases h : b = d
      · subst h; simp [resT, resVarT, Formalism.CohomologicalDescent.LR.der_X]
      · simp [resT, resVarT, Formalism.CohomologicalDescent.LR.der_X, h]

theorem weight_rowW_apply (N : ℕ) (m : Fin N × Fin N →₀ ℕ) (x : Fin N) :
    Finsupp.weight (rowW N N) m x = ∑ s, m (x, s) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  simp [rowW, Pi.single_apply]

theorem weight_colW_apply (N : ℕ) (m : Fin N × Fin N →₀ ℕ) (y : Fin N) :
    Finsupp.weight (colW N N) m y = ∑ a, m (a, y) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  simp [colW, Pi.single_apply]

theorem resT_monomial_eq_zero (p q : ℕ) (m : Fin (p + q) × Fin (p + q) →₀ ℕ) (a : ℚ)
    (v : Fin (p + q) × Fin (p + q)) (hv : resVarT ℚ p q v = 0) (hm : m v ≠ 0) : resT ℚ p q (monomial m a) = 0 := by
  rw [resT, aeval_monomial]
  apply mul_eq_zero_of_right
  exact Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hm) (by simp only [hv]; exact zero_pow hm)

theorem resVarT_castAdd_natAdd (p q : ℕ) (a : Fin p) (t : Fin q) :
    resVarT ℚ p q (Fin.castAdd q a, Fin.natAdd p t) = 0 := by simp [resVarT]

theorem resVarT_natAdd_castAdd (p q : ℕ) (b : Fin q) (s : Fin p) :
    resVarT ℚ p q (Fin.natAdd p b, Fin.castAdd q s) = 0 := by simp [resVarT]

theorem resT_wrong_degree (p q : ℕ) (f : MvPolynomial (Fin (p + q) × Fin (p + q)) ℚ) (ν : Fin (p + q) → ℕ) (t : ℚ)
    (hf : IsWeightedHomogeneous (colW (p + q) (p + q)) f ν)
    (hsum : ∑ c : Fin p, Formalism.CohomologicalDescent.LR.der (p + q) (p + q) (Fin.castAdd q c) (Fin.castAdd q c) f = t • f)
    (ht : t ≠ ∑ c : Fin p, (ν (Fin.castAdd q c) : ℚ)) : resT ℚ p q f = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [f.as_sum, map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hc : AddMonoidAlgebra.coeff f m ≠ 0 := mem_support_iff.1 hm
  by_contra hne
  have h1 : ∀ (a : Fin p) (t' : Fin q), m (Fin.castAdd q a, Fin.natAdd p t') = 0 := by
    intro a t'
    by_contra h0
    exact hne (resT_monomial_eq_zero p q m _ _ (resVarT_castAdd_natAdd p q a t') h0)
  have h2 : ∀ (b : Fin q) (s : Fin p), m (Fin.natAdd p b, Fin.castAdd q s) = 0 := by
    intro b s
    by_contra h0
    exact hne (resT_monomial_eq_zero p q m _ _ (resVarT_natAdd_castAdd p q b s) h0)
  have hw : Finsupp.weight (colW (p + q) (p + q)) m = ν := hf hc
  have ht' : t = ∑ c : Fin p, ((Finsupp.weight (rowW (p + q) (p + q)) m (Fin.castAdd q c) : ℕ) : ℚ) := by
    have h3 := congrArg (AddMonoidAlgebra.coeff · m) hsum
    rw [coeff_sum, coeff_smul, smul_eq_mul] at h3
    simp only [Formalism.CohomologicalDescent.LR.coeff_der_diag] at h3
    rw [← Finset.sum_mul] at h3
    exact (mul_right_cancel₀ hc h3).symm
  have key : ∑ c : Fin p, Finsupp.weight (rowW (p + q) (p + q)) m (Fin.castAdd q c) =
      ∑ c : Fin p, Finsupp.weight (colW (p + q) (p + q)) m (Fin.castAdd q c) := by
    simp only [weight_rowW_apply, weight_colW_apply, Fin.sum_univ_add, h1, h2, Finset.sum_const_zero, add_zero]
    exact Finset.sum_comm
  apply ht
  rw [ht', ← hw]
  exact_mod_cast key

theorem dualWeyl_resDer : ResDer := by
  intro p q f
  refine ⟨fun c d => ?_, fun c d => ?_, fun ν t hf hsum ht => resT_wrong_degree p q f ν t hf hsum ht⟩
  · induction f using MvPolynomial.induction_on with
    | C a =>
      rw [← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap, map_zero, AlgHom.commutes,
        Algebra.TensorProduct.algebraMap_apply, LinearMap.rTensor_tmul]
      simp
    | add g h hg hh => rw [map_add (f := _), map_add (f := _), map_add (f := _), hg, hh, map_add (f := _)]
    | mul_X g v hg =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul, map_mul, rTensor_der_mul, resT_der_left_X, hg]
  · induction f using MvPolynomial.induction_on with
    | C a =>
      rw [← MvPolynomial.algebraMap_eq, Derivation.map_algebraMap, map_zero, AlgHom.commutes,
        Algebra.TensorProduct.algebraMap_apply, LinearMap.lTensor_tmul]
      simp
    | add g h hg hh => rw [map_add (f := _), map_add (f := _), map_add (f := _), hg, hh, map_add (f := _)]
    | mul_X g v hg =>
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add (f := _), map_mul, map_mul, map_mul, lTensor_der_mul, resT_der_right_X, hg]

end GlobalTheory.LeviCut
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylRestrictionRowOperatorsStatement
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeyl_restriction_rowOperators : GlobalTheory.LeviCut.ResDer := by
  first | exact @GlobalTheory.LeviCut.dualWeyl_resDer | exact GlobalTheory.LeviCut.dualWeyl_resDer | (intros; apply GlobalTheory.LeviCut.dualWeyl_resDer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColumnCharacterEigenSubmoduleNeBot
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColumnCharacterEigenSubmoduleNeBot
noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem exists_eigenvector_of_stable {F : Type} [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : (ι → F) → V →ₗ[ℂ] V) (h0 : T 0 = LinearMap.id) (hT : ∀ x x' v, T x (T x' v) = T (x + x') v)
    (W : Submodule ℂ V) (hW : ∀ x, ∀ v ∈ W, T x v ∈ W) (hne : W ≠ ⊥) :
    ∃ l : ι → F, ∃ w ∈ W, w ≠ 0 ∧ ∀ x, T x w = ψ (∑ i, l i * x i) • w := by
  classical
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).1 hne
  let w : (ι → F) → V := fun l => ∑ x : ι → F, ψ (-∑ i, l i * x i) • T x v
  have hprim := AddChar.IsPrimitive.of_ne_one hψ
  have hs : ∀ x : ι → F, x ≠ 0 → ∑ l : ι → F, ψ (-∑ i, l i * x i) = 0 := by
    intro x hx
    have e : ∀ l : ι → F, ψ (-∑ i, l i * x i) = ∏ i, ψ (l i * (-x i)) := by
      intro l
      rw [← Finset.sum_neg_distrib]
      simp only [mul_neg]
      induction (Finset.univ : Finset ι) using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
    simp only [e]
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ => Finset.univ) (fun i t => ψ (t * (-x i)))]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    have := AddChar.sum_mulShift (ψ := ψ) (-x i) hprim
    rw [if_neg (by simpa using hi)] at this
    simpa using this
  have hsum : ∑ l, w l = (Fintype.card (ι → F) : ℂ) • v := by
    simp only [w]
    rw [Finset.sum_comm, Finset.sum_eq_single (0 : ι → F)]
    · simp [h0, Nat.cast_smul_eq_nsmul, -Fintype.card_pi]
    · intro x _ hx
      rw [← Finset.sum_smul, hs x hx, zero_smul]
    · simp
  have hex : ∃ l, w l ≠ 0 := by
    by_contra hc
    push Not at hc
    rw [Finset.sum_eq_zero fun l _ => hc l] at hsum
    rcases smul_eq_zero.1 hsum.symm with h | h
    · exact (Nat.cast_ne_zero.2 Fintype.card_ne_zero) h
    · exact hv0 h
  obtain ⟨l, hl⟩ := hex
  refine ⟨l, w l, W.sum_mem fun x _ => W.smul_mem _ (hW x v hv), hl, fun x => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [w, map_sum, map_smul, hT, Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.addLeft x) _ _ fun z => ?_
  simp only [Equiv.coe_addLeft, ← AddChar.map_add_eq_mul, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  congr 2
  ring

variable {F : Type} [Field F] {r : ℕ}

def colMat (k : Fin r) (x : Fin r → F) : Matrix (Fin r) (Fin r) F :=
  Matrix.of fun i j => if i < k ∧ j = k then x i else 0

theorem colMat_mul_apply (k : Fin r) (x : Fin r → F) (M : Matrix (Fin r) (Fin r) F) (i j : Fin r) :
    (colMat k x * M) i j = if i < k then x i * M k j else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · by_cases h : i < k <;> simp [colMat, h]
  · intro m _ hm
    simp [colMat, hm]
  · simp

theorem one_add_colMat_mul (k : Fin r) (x x' : Fin r → F) :
    (1 + colMat k x) * (1 + colMat k x') = 1 + colMat k (x + x') := by
  have : colMat k x * colMat k x' = 0 := by
    ext i j
    rw [colMat_mul_apply]
    simp [colMat]
  have h2 : colMat k (x + x') = colMat k x + colMat k x' := by
    ext i j
    simp only [colMat, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  rw [h2, add_mul, mul_add, mul_add, this]
  simp only [one_mul, mul_one]
  abel

theorem colMat_zero (k : Fin r) : colMat k (0 : Fin r → F) = 0 := by
  ext i j
  simp [colMat]

def colGL (k : Fin r) (x : Fin r → F) : GL (Fin r) F where
  val := 1 + colMat k x
  inv := 1 + colMat k (-x)
  val_inv := by rw [one_add_colMat_mul]; simp [colMat_zero]
  inv_val := by rw [one_add_colMat_mul]; simp [colMat_zero]

theorem colGL_mem_unip (k : Fin r) (x : Fin r → F) : colGL k x ∈ unip F r := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : j < i := hij
    have : ¬ (i < k ∧ j = k) := fun h => by
      obtain ⟨h1, rfl⟩ := h
      exact lt_asymm h1 hij'
    simp [colGL, colMat, this, Matrix.one_apply_ne hij'.ne']
  · have : ¬ (i < k ∧ i = k) := fun h => h.1.ne h.2
    simp [colGL, colMat, this]

def colEl {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) (x : Fin r → F) : blockTri (κ := F) b :=
  ⟨colGL k x, fun i j hij => (colGL_mem_unip k x).1 (show j < i from hb.reflect_lt hij)⟩

theorem colEl_val {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) (x : Fin r → F) :
    ((colEl hb k x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = 1 + colMat k x := rfl

theorem colEl_mul {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) (x x' : Fin r → F) :
    colEl hb k x * colEl hb k x' = colEl hb k (x + x') :=
  Subtype.ext (Units.ext (one_add_colMat_mul k x x'))

theorem colEl_zero {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) : colEl hb k (0 : Fin r → F) = 1 :=
  Subtype.ext (Units.ext (by rw [colEl_val, colMat_zero]; simp))

theorem colEl_neg_mul {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) (x : Fin r → F) {u : blockTri (κ := F) b}
    (hu : u ∈ colSet F b k.val)
    (hx : ∀ i, i < k → x i = ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k) :
    colEl hb k (-x) * u ∈ colSet F b (k.val + 1) ∧
      edgeSum (blkEdge b) ((colEl hb k (-x) * u : blockTri (κ := F) b) : GL (Fin r) F) =
        edgeSum (fun i j => blkEdge b i j ∧ k < j) (u : GL (Fin r) F) := by
  have e : ∀ i j, (((colEl hb k (-x) * u : blockTri (κ := F) b) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j =
      ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j +
        if i < k then -x i * ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) k j else 0 := by
    intro i j
    rw [Subgroup.coe_mul, Units.val_mul, colEl_val, add_mul, one_mul, Matrix.add_apply, colMat_mul_apply]
    rfl
  have hc : ∀ i j : Fin r, j.val < k.val + 1 →
      (((colEl hb k (-x) * u : blockTri (κ := F) b) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j =
        (1 : Matrix (Fin r) (Fin r) F) i j := by
    intro i j hj
    rw [e]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
    · rw [hu.2 i j h, hu.2 k j h, Matrix.one_apply_ne (i := k) (j := j) (fun h' => by simp [h'] at h)]
      simp
    · obtain rfl : j = k := Fin.ext h
      rw [hu.1.2 j]
      rcases lt_trichotomy i j with h' | h' | h'
      · rw [if_pos h', hx i h', Matrix.one_apply_ne h'.ne]; ring
      · subst h'; simp [hu.1.2 i]
      · rw [if_neg (lt_asymm h'), hu.1.1 (show j.val < i.val from h'), Matrix.one_apply_ne h'.ne']; simp
  refine ⟨⟨(unip F r).mul_mem (colGL_mem_unip k (-x)) hu.1, hc⟩, ?_⟩
  unfold edgeSum
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : blkEdge b i j
  · have h1 := hij.1
    by_cases hk : k < j
    · have : ¬ i < k := by rw [Fin.lt_def] at hk ⊢; omega
      rw [if_pos hij, if_pos ⟨hij, hk⟩, e, if_neg this, add_zero]
    · rw [if_pos hij, if_neg (fun h => hk h.2), hc i j (by rw [Fin.lt_def] at hk; omega),
        Matrix.one_apply_ne (fun h' => by simp [h'] at h1)]
  · rw [if_neg hij, if_neg (fun h => hij h.1)]

theorem mul_colEl_val {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) (x : Fin r → F) {u : blockTri (κ := F) b}
    (hu : u ∈ colSet F b (k.val + 1)) (i j : Fin r) :
    (((u * colEl hb k x : blockTri (κ := F) b) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j =
      ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j + if i < k ∧ j = k then x i else 0 := by
  rw [Subgroup.coe_mul, Units.val_mul, colEl_val, mul_add, mul_one, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  have : ∀ m, ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i m * colMat k x m j =
      (1 : Matrix (Fin r) (Fin r) F) i m * colMat k x m j := by
    intro m
    by_cases hm : m < k
    · rw [hu.2 i m (by rw [Fin.lt_def] at hm; omega)]
    · simp [colMat, hm]
  simp only [this]
  rw [← Matrix.mul_apply, one_mul]
  rfl

theorem colEl_stable {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : AddChar F ℂ) {b : Fin r → ℕ} (hb : Monotone b)
    (σ : Representation ℂ (blockTri (κ := F) b) V) (k : Fin r) (x : Fin r → F) (v : V)
    (hv : v ∈ eig σ (colSet F b (k.val + 1)) (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F)))) :
    σ (colEl hb k x) v ∈ eig σ (colSet F b (k.val + 1)) (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F))) := by
  rw [mem_eig] at hv ⊢
  intro u hu
  have hu' : u ∈ colSet F b k.val := ⟨hu.1, fun i j hj => hu.2 i j (by omega)⟩
  have hm : u * colEl hb k x ∈ colSet F b k.val := by
    refine ⟨(unip F r).mul_mem hu.1 (colGL_mem_unip k x), fun i j hj => ?_⟩
    rw [mul_colEl_val hb k x hu, hu.2 i j (by omega), if_neg (fun h => by simp [h.2] at hj), add_zero]
  obtain ⟨h1, h2⟩ := colEl_neg_mul hb k x hm (fun i hi => by
    rw [mul_colEl_val hb k x hu, hu.2 i k (by omega), if_pos ⟨hi, rfl⟩, Matrix.one_apply_ne hi.ne, zero_add])
  obtain ⟨-, h3⟩ := colEl_neg_mul hb k 0 hu' (fun i hi => by
    rw [hu.2 i k (by omega), Matrix.one_apply_ne hi.ne]; rfl)
  rw [neg_zero, colEl_zero, one_mul] at h3
  have h4 : edgeSum (fun i j => blkEdge b i j ∧ k < j) ((u * colEl hb k x : blockTri (κ := F) b) : GL (Fin r) F) =
      edgeSum (fun i j => blkEdge b i j ∧ k < j) (u : GL (Fin r) F) := by
    unfold edgeSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rw [mul_colEl_val hb k x hu, if_neg (fun h' => h.2.ne' h'.2), add_zero]
    · rfl
  have h5 := hv _ h1
  rw [h2, h4, ← h3] at h5
  have h6 : u * colEl hb k x = colEl hb k x * (colEl hb k (-x) * (u * colEl hb k x)) := by
    rw [← mul_assoc (colEl hb k x), colEl_mul, add_neg_cancel, colEl_zero, one_mul]
  rw [← Module.End.mul_apply, ← map_mul, h6, map_mul, Module.End.mul_apply, h5, map_smul]

theorem exists_colChar_eig_ne_bot : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), Monotone b → (∀ p : blockTri (κ := F) b, (∀ i j, b i = b j → ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) → σ p = 1) → ∀ k : Fin r, eig σ (colSet F b (k.val + 1)) (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F))) ≠ ⊥ → ∃ l : Fin r → F, (∀ i, l i ≠ 0 → i < k ∧ b i = b k) ∧ eig σ (colSet F b k.val) (colChar ψ b k l) ≠ ⊥ := by
  intro F _ _ ψ hψ r V _ _ b σ hb hinf k hne
  obtain ⟨l, w, hw, hw0, hl⟩ := exists_eigenvector_of_stable ψ hψ (fun x => σ (colEl hb k x))
    (by rw [colEl_zero, map_one]; rfl)
    (fun x x' v => by rw [← Module.End.mul_apply, ← map_mul, colEl_mul]) _
    (fun x v hv => colEl_stable ψ hb σ k x v hv) hne
  refine ⟨l, fun i hi => ?_, (Submodule.ne_bot_iff _).2 ⟨w, ?_, hw0⟩⟩
  · by_contra hc
    refine AddChar.IsPrimitive.of_ne_one hψ hi (AddChar.ext _ _ fun t => ?_)
    have h1 : σ (colEl hb k (Pi.single i t)) = 1 := by
      refine hinf _ fun a c hac => ?_
      rw [colEl_val, Matrix.add_apply, add_eq_left]
      simp only [colMat, Matrix.of_apply]
      split_ifs with h
      · refine Pi.single_eq_of_ne (fun h' => hc ?_) _
        rw [← h', hac, h.2]
        exact ⟨h.2 ▸ h.1, rfl⟩
      · rfl
    have h2 := hl (Pi.single i t)
    rw [h1, Finset.sum_eq_single i (fun a _ ha => by simp [ha]) (by simp), Pi.single_eq_same] at h2
    have h3 : (ψ (l i * t) - 1) • w = 0 := by rw [sub_smul, ← h2]; simp
    have h4 := (smul_eq_zero.1 h3).resolve_right hw0
    simpa [sub_eq_zero] using h4
  · rw [mem_eig] at hw ⊢
    intro u hu
    set x : Fin r → F := fun i => ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k with hx
    obtain ⟨h1, h2⟩ := colEl_neg_mul hb k x hu (fun i _ => rfl)
    have h5 := hw _ h1
    rw [h2] at h5
    have h6 : u = colEl hb k x * (colEl hb k (-x) * u) := by
      rw [← mul_assoc (colEl hb k x), colEl_mul, add_neg_cancel, colEl_zero, one_mul]
    calc σ u w = σ (colEl hb k x) (σ (colEl hb k (-x) * u) w) := by
          rw [← Module.End.mul_apply, ← map_mul, ← h6]
      _ = _ := by
          rw [h5, map_smul, hl x, smul_smul, colChar, AddChar.map_add_eq_mul, mul_comm]

end GlobalTheory.FinGL.LeviWh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColumnCharacterEigenSubmoduleNeBotStatement
open GlobalTheory.FinGL GlobalTheory.FinGL.LeviWh Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_columnCharacter_eigenSubmodule_ne_bot : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), Monotone b → (∀ p : blockTri (κ := F) b, (∀ i j, b i = b j → ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) → σ p = 1) → ∀ k : Fin r, eig σ (colSet F b (k.val + 1)) (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F))) ≠ ⊥ → ∃ l : Fin r → F, (∀ i, l i ≠ 0 → i < k ∧ b i = b k) ∧ eig σ (colSet F b k.val) (colChar ψ b k l) ≠ ⊥ := by
  first | exact @GlobalTheory.FinGL.LeviWh.exists_colChar_eig_ne_bot | exact GlobalTheory.FinGL.LeviWh.exists_colChar_eig_ne_bot | (intros; apply GlobalTheory.FinGL.LeviWh.exists_colChar_eig_ne_bot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdDivGroupChartFormsBasisAndDifferential
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdDivGroupChartFormsBasisAndDifferential
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartForm

variable {p : ℕ} {O : Type} [CommRing O] {G : PDivGroup p O} {d : ℕ} (c : QLog.Chart G d)

theorem ev_coe (n : ℕ) (P : MvPolynomial (Fin d) O) :
    c.ev n (P : MvPowerSeries (Fin d) O) = MvPolynomial.aeval (c.x n) P := by
  have h : (c.ev n).comp (MvPolynomial.coeToMvPowerSeries.algHom O) =
      MvPolynomial.aeval (c.x n) :=
    MvPolynomial.algHom_ext fun i => by
      simp [MvPolynomial.coeToMvPowerSeries.algHom_apply, (c.isEval n).1 i]
  have h2 := DFunLike.congr_fun h P
  simpa [MvPolynomial.coeToMvPowerSeries.algHom_apply] using h2

theorem exists_split (n m : ℕ) (f : MvPowerSeries (Fin d) O) :
    ∃ (P : MvPolynomial (Fin d) O) (a : G.A n),
      c.ev n f = MvPolynomial.aeval (c.x n) P + (p : G.A n) ^ m * a ∧
      MvPolynomial.constantCoeff P = constantCoeff f ∧
      ∀ i, AddMonoidAlgebra.coeff P (Finsupp.single i 1) = lin f i := by
  obtain ⟨N, hN⟩ := (c.isEval n).2 m
  set P := trunc' O (Finsupp.equivFunOnFinite.symm fun _ => max N 2) f with hP
  have hle : ∀ α : Fin d →₀ ℕ, α.degree < max N 2 →
      α ≤ Finsupp.equivFunOnFinite.symm fun _ => max N 2 := by
    intro α hα i
    show α i ≤ max N 2
    exact (Finsupp.le_degree i α).trans hα.le
  obtain ⟨a, ha⟩ := hN (f - P) fun α hα => by
    rw [map_sub, MvPolynomial.coeff_coe, hP, coeff_trunc',
      if_pos (hle α (lt_of_lt_of_le hα (le_max_left _ _))), sub_self]
  refine ⟨P, a, ?_, ?_, fun i => ?_⟩
  · rw [← ev_coe, ← ha, ← map_add (f := _), add_sub_cancel]
  · rw [MvPolynomial.constantCoeff_eq, hP, coeff_trunc',
      if_pos (hle 0 (by simp)), coeff_zero_eq_constantCoeff_apply]
  · rw [hP, coeff_trunc', if_pos (hle _ (lt_of_lt_of_le (by simp) (le_max_right N 2))), lin]

theorem eq_zero_of_dvd [IsAdicComplete (Ideal.span {(p : O)}) O] (x : O)
    (h : ∀ m, (p : O) ^ m ∣ x) : x = 0 :=
  IsHausdorff.haus' (I := Ideal.span {(p : O)}) x fun m => by
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton, sub_zero]
    exact h m

theorem counit_aeval (n : ℕ) (P : MvPolynomial (Fin d) O) :
    Bialgebra.counitAlgHom O (G.A n) (MvPolynomial.aeval (c.x n) P) =
      MvPolynomial.constantCoeff P := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have h : (fun i => Bialgebra.counitAlgHom O (G.A n) (c.x n i)) = 0 :=
    funext fun i => by simpa using c.aug n i
  rw [h, MvPolynomial.aeval_zero]
  rfl

theorem counit_ev [IsAdicComplete (Ideal.span {(p : O)}) O] (n : ℕ)
    (f : MvPowerSeries (Fin d) O) :
    Bialgebra.counitAlgHom O (G.A n) (c.ev n f) = constantCoeff f := by
  refine sub_eq_zero.1 (eq_zero_of_dvd (p := p) _ fun m => ?_)
  obtain ⟨P, a, h1, h2, -⟩ := (exists_split c) n m f
  rw [h1, map_add (f := _), counit_aeval, h2, map_mul, map_pow, map_natCast, add_sub_cancel_left]
  exact dvd_mul_right _ _

theorem d_aeval (n : ℕ) (P : MvPolynomial (Fin d) O) :
    PDiv.dUnit (R := O) (MvPolynomial.aeval (c.x n) P) =
      ∑ i, AddMonoidAlgebra.coeff P (Finsupp.single i 1) • PDiv.dUnit (R := O) (c.x n i) := by
  classical
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h0 : ∀ x : Fin d, ¬ (0 : Fin d →₀ ℕ) = Finsupp.single x 1 := fun x h =>
      (Finsupp.single_ne_zero.2 one_ne_zero) h.symm
    rw [MvPolynomial.aeval_C]
    simp [MvPolynomial.coeff_C, PDiv.dUnit, h0]
  | add P Q hP hQ =>
    unfold PDiv.dUnit at *
    rw [map_add (f := _), map_add (f := _), hP, hQ, ← Finset.sum_add_distrib]
    simp [add_smul]
  | mul_X P j h =>
    have hc : ∀ i, AddMonoidAlgebra.coeff (P * MvPolynomial.X j) (Finsupp.single i 1) =
        if j = i then MvPolynomial.constantCoeff P else 0 := by
      intro i
      rw [MvPolynomial.coeff_mul_X']
      by_cases hij : j = i
      · subst hij; simp [MvPolynomial.constantCoeff_eq]
      · simp [hij, Finsupp.support_single_ne_zero]
    simp only [hc, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hx : Bialgebra.counitAlgHom O (G.A n) (c.x n j) = 0 := by simpa using c.aug n j
    rw [map_mul, MvPolynomial.aeval_X, PDiv.dUnit, AugCot.d_mul, counit_aeval, hx, zero_smul,
      add_zero]

theorem d_ev (n : ℕ) (f : MvPowerSeries (Fin d) O) :
    PDiv.dUnit (R := O) (c.ev n f) = ∑ i, lin f i • PDiv.dUnit (R := O) (c.x n i) := by
  obtain ⟨P, a, h1, -, h3⟩ := (exists_split c) n n f
  have h4 : AugCot.d (Bialgebra.counitAlgHom O (G.A n)) ((p : G.A n) ^ n * a) = 0 := by
    rw [show (p : G.A n) ^ n * a = ((p : O) ^ n) • a by
      rw [Algebra.smul_def, map_pow, map_natCast], map_smul]
    exact G.pow_smul_cot n _
  rw [h1, PDiv.dUnit, map_add (f := _), h4, add_zero, ← PDiv.dUnit, (d_aeval c)]
  simp only [h3]

theorem coeff_single_of_mem_sq {h : MvPowerSeries (Fin d) O}
    (hh : h ∈ RingHom.ker (constantCoeff : MvPowerSeries (Fin d) O →+* O) ^ 2) (i : Fin d) :
    coeff (Finsupp.single i 1) h = 0 := by
  rw [pow_two] at hh
  refine Submodule.mul_induction_on hh (fun f hf g hg => ?_) (fun f g hf hg => ?_)
  · rw [coeff_mul]
    refine Finset.sum_eq_zero fun q hq => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hq
    have hdeg := congrArg Finsupp.degree hq
    rw [map_add (f := _), Finsupp.degree_single] at hdeg
    rcases (show q.1.degree = 0 ∨ q.2.degree = 0 by omega) with h0 | h0
    · rw [(Finsupp.degree_eq_zero_iff _).1 h0, coeff_zero_eq_constantCoeff_apply,
        RingHom.mem_ker.1 hf, zero_mul]
    · rw [(Finsupp.degree_eq_zero_iff _).1 h0, coeff_zero_eq_constantCoeff_apply,
        RingHom.mem_ker.1 hg, mul_zero]
  · rw [map_add (f := _), hf, hg, add_zero]

def lvl (n : ℕ) : (Fin d → O) →ₗ[O] PDiv.Cot O (G.A n) :=
  Fintype.linearCombination O fun i => PDiv.dUnit (R := O) (c.x n i)

theorem lvl_apply (n : ℕ) (a : Fin d → O) :
    lvl c n a = ∑ i, a i • PDiv.dUnit (R := O) (c.x n i) := Fintype.linearCombination_apply ..

theorem val_comb (a : Fin d → O) (n : ℕ) :
    (Fintype.linearCombination O c.form a).1 n = lvl c n a := by
  rw [Fintype.linearCombination_apply, lvl_apply]
  simp [QLog.Chart.form]

theorem res_lvl (n : ℕ) (a : Fin d → O) :
    PDiv.cotMap (G.res n) (lvl c (n + 1) a) = lvl c n a := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [lvl_apply, map_sum, map_smul, PDiv.cotMap_d, c.res]

theorem lvl_le (w : G.omega) (a : Fin d → O) {n k : ℕ} (h : n ≤ k)
    (hk : lvl c k a = w.1 k) : lvl c n a = w.1 n := by
  revert hk
  induction k, h using Nat.le_induction with
  | base => exact id
  | succ k hnk ih => exact fun hk => ih (by rw [← res_lvl c, hk, w.2 k])

theorem exists_level_dvd [IsAdicComplete (Ideal.span {(p : O)}) O] (m : ℕ) :
    ∃ n, ∀ a : Fin d → O, lvl c n a = 0 → ∀ i, (p : O) ^ m ∣ a i := by
  obtain ⟨n, hn⟩ := c.ker m 2
  refine ⟨n, fun a ha i => ?_⟩
  set y : G.A n := ∑ j, a j • c.x n j with hy0
  have hx : ∀ j, Bialgebra.counitAlgHom O (G.A n) (c.x n j) = 0 := fun j => by
    simpa using c.aug n j
  have hεy : Bialgebra.counitAlgHom O (G.A n) y = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hy0, map_sum, map_smul, hx]
  have hy : PDiv.dUnit (R := O) y = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hy0, PDiv.dUnit, map_sum]
    simpa [map_smul, lvl_apply] using ha
  rw [PDiv.dUnit, AugCot.d_eq_zero_iff, hεy, map_zero, sub_zero] at hy
  have hI : RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) ≤
      Ideal.map (c.ev n) (RingHom.ker (constantCoeff : MvPowerSeries (Fin d) O →+* O)) := by
    intro z hz
    obtain ⟨g, rfl⟩ := c.surj n z
    refine Ideal.mem_map_of_mem _ ?_
    rw [RingHom.mem_ker, ← counit_ev c]
    exact hz
  have hy2 : y ∈ Ideal.map (c.ev n)
      (RingHom.ker (constantCoeff : MvPowerSeries (Fin d) O →+* O) ^ 2) := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono hI 2 hy
  obtain ⟨h, hh, hev⟩ := (Ideal.mem_map_iff_of_surjective _ (c.surj n)).1 hy2
  have hz : c.ev n ((∑ j, a j • X j) - h) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, hev, map_sum, hy0]
    simp [map_smul, (c.isEval n).1]
  have := hn _ hz (Finsupp.single i 1) (by simp)
  rw [map_sub, coeff_single_of_mem_sq hh, sub_zero] at this
  classical
  simpa [coeff_X, Finsupp.single_left_inj one_ne_zero] using this

theorem comb_bijective [IsAdicComplete (Ideal.span {(p : O)}) O] :
    Function.Bijective (Fintype.linearCombination O c.form) := by
  choose nm hnm using (exists_level_dvd c)
  constructor
  · rw [injective_iff_map_eq_zero]
    intro a ha
    funext i
    refine eq_zero_of_dvd _ fun m => hnm m a ?_ i
    rw [← val_comb c, ha]
    rfl
  · intro w
    have hb : ∀ k, ∃ b : Fin d → O, lvl c k b = w.1 k := by
      intro k
      obtain ⟨y, hy⟩ := AugCot.d_surjective _ (w.1 k)
      obtain ⟨g, rfl⟩ := c.surj k y
      exact ⟨lin g, by rw [lvl_apply, ← d_ev c]; exact hy⟩
    choose b hb using hb
    let K : ℕ → ℕ := fun m => m + ∑ j ∈ Finset.range (m + 1), nm j
    have hK : ∀ {m n}, m ≤ n → K m ≤ K n := fun h =>
      add_le_add h (Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ h)))
    have hnK : ∀ m, nm m ≤ K m := fun m =>
      le_add_left (Finset.single_le_sum (fun j _ => Nat.zero_le (nm j))
        (Finset.self_mem_range_succ m))
    have hnK' : ∀ m, m ≤ K m := fun m => Nat.le_add_right _ _
    have hcauchy : ∀ {m n}, m ≤ n → ∀ i, (p : O) ^ m ∣ b (K m) i - b (K n) i := by
      intro m n hmn i
      refine hnm m (b (K m) - b (K n)) ?_ i
      rw [map_sub, (lvl_le c) w _ (hnK m) (hb _), (lvl_le c) w _ ((hnK m).trans (hK hmn)) (hb _),
        sub_self]
    have hL : ∀ i, ∃ L : O, ∀ n, (p : O) ^ n ∣ b (K n) i - L := by
      intro i
      obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : O)})
        (fun m => b (K m) i) fun {m n} hmn => by
          rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
            Ideal.mem_span_singleton]
          exact hcauchy hmn i
      refine ⟨L, fun n => ?_⟩
      have h1 := hL n
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton] at h1
      exact h1
    choose L hL using hL
    refine ⟨L, Subtype.ext (funext fun n => ?_)⟩
    change (Fintype.linearCombination O c.form L).1 n = w.1 n
    rw [(val_comb c)]
    choose v hv using fun i => hL i n
    have hLv : L = b (K n) - (p : O) ^ n • v := by
      funext i
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← hv i]
      ring
    rw [hLv, map_sub, map_smul, G.pow_smul_cot, sub_zero]
    exact (lvl_le c) w _ (hnK' n) (hb _)

end GlobalTheory.ChartForm

theorem GlobalTheory.chart_form_basis : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), Function.Bijective (Fintype.linearCombination O c.form) ∧ ∀ (n : ℕ) (f : MvPowerSeries (Fin d) O), constantCoeff f = 0 → PDiv.dUnit (R := O) (c.ev n f) = ∑ i, lin f i • PDiv.dUnit (R := O) (c.x n i) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ G d c
  exact ⟨ChartForm.comb_bijective c, fun n f _ => ChartForm.d_ev c n f⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PdDivGroupChartFormsBasisAndDifferentialStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pdDivGroupChart_forms_basis_and_differential : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), Function.Bijective (Fintype.linearCombination O c.form) ∧ ∀ (n : ℕ) (f : MvPowerSeries (Fin d) O), constantCoeff f = 0 → PDiv.dUnit (R := O) (c.ev n f) = ∑ i, lin f i • PDiv.dUnit (R := O) (c.x n i) := by
  first | exact @GlobalTheory.chart_form_basis | exact GlobalTheory.chart_form_basis | (intros; apply GlobalTheory.chart_form_basis <;> assumption)
end
end
