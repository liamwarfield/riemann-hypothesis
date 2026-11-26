module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalPointsIntegralPointsMembership
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCmIdempotentsSelectConjugatePrimes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemISupInfWeightSubmoduleOfDiagonalStable
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulVSubRight

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlgClosureEmbeddingExtendingOnAlgebraic
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlgClosureEmbeddingExtendingOnAlgebraic
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj

theorem exists_cj_Qbar_eq : ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ),
    ∃ ρ' : Qbar →ₐ[ℚ] ℂ, ∀ x : ℂ, x ∈ Qbar → x ∈ M → cj M ρ x = cj Qbar ρ' x := by
  intro M ρ
  let L : IntermediateField ℚ ℂ := M ⊓ Qbar
  have h1 : L ≤ M := inf_le_left
  have h2 : L ≤ Qbar := inf_le_right
  letI : Algebra L Qbar := (IntermediateField.inclusion h2).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ L Qbar := IsScalarTower.of_algebraMap_eq fun r => by
    apply Subtype.ext
    exact (map_ratCast (algebraMap ℚ ℂ) r).trans (by simp)
  haveI : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  haveI : Algebra.IsAlgebraic L Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) L
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ) (L := L) (M := ℂ)
    (E := Qbar) (ρ.comp (IntermediateField.inclusion h1))
  refine ⟨φ, fun x hx hM => ?_⟩
  rw [cj_mem ρ hM, cj_mem φ hx]
  have := DFunLike.congr_fun hφ (⟨x, ⟨hM, hx⟩⟩ : L)
  exact this.symm

end GlobalTheory.ThetaConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlgClosureEmbeddingExtendingOnAlgebraicStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algClosure_embedding_extending_on_algebraic : ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), ∃ ρ' : Qbar →ₐ[ℚ] ℂ, ∀ x : ℂ, x ∈ Qbar → x ∈ M → cj M ρ x = cj Qbar ρ' x := by
  first | exact @GlobalTheory.ThetaConj.exists_cj_Qbar_eq | exact GlobalTheory.ThetaConj.exists_cj_Qbar_eq | (intros; apply GlobalTheory.ThetaConj.exists_cj_Qbar_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorConjugateTangentSpacePadZeroColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorConjugateTangentSpacePadZeroColumns
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.ConjRestrict

theorem coeff_taylorDir_embDomain {σ σ' W : Type*} [Fintype σ] [Fintype σ'] [NormedAddCommGroup W]
    [NormedSpace ℂ W] (e : σ ↪ σ') (u : σ' → W) {f : W → ℂ} (hf : AnalyticAt ℂ f 0) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α (taylorDir (fun i => u (e i)) f) =
      MvPowerSeries.coeff (Finsupp.embDomain e α) (taylorDir u f) := by
  have h1 : ((α.toMultiset.toList : List σ) : Multiset σ) = Finsupp.toMultiset α := by simp
  have h2 : ((α.toMultiset.toList.map e : List σ') : Multiset σ') =
      Finsupp.toMultiset (Finsupp.embDomain e α) := by
    rw [← Multiset.map_coe, h1, Finsupp.toMultiset_map, Finsupp.embDomain_eq_mapDomain]
  have h3 : ∏ i, ((Finsupp.embDomain e α) i).factorial = ∏ i, (α i).factorial := by
    rw [← Finsupp.prod_fintype (Finsupp.embDomain e α) (fun _ n => n.factorial) (by simp),
      Finsupp.prod_embDomain, Finsupp.prod_fintype _ _ (by simp)]
  rw [coeff_taylorDir_eq_lineDerivList _ hf h1, coeff_taylorDir_eq_lineDerivList _ hf h2, h3,
    List.map_map]
  rfl

def colEmb (D : D7) (N N' m : ℕ) :
    D.what₂.Tau × Fin N' × Fin N ↪ D.what₂.Tau × Fin N' × Fin (N + m) :=
  ⟨fun k => (k.1, k.2.1, Fin.castAdd m k.2.2), by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [Prod.mk.injEq, Fin.castAdd_inj] at h
    simp [h]⟩

theorem colEmb_apply (D : D7) (N N' m : ℕ) (k : D.what₂.Tau × Fin N' × Fin N) :
    colEmb D N N' m k = (k.1, k.2.1, Fin.castAdd m k.2.2) := rfl

theorem pad_coordV (D : D7) {N N' : ℕ} (m : ℕ) (k : D.what₂.Tau × Fin N' × Fin N) :
    pad D m (coordV D k) = coordV D (colEmb D N N' m k) := by
  funext τ a i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [pad_left]; simp [coordV, colEmb_apply]
  · rw [pad_right]
    have : Fin.natAdd N i ≠ Fin.castAdd m k.2.2 := by
      intro h
      have := congrArg Fin.val h
      have := k.2.2.2
      simp at *
      omega
    simp [coordV, colEmb_apply, this]

theorem taylor_pad (D : D7) {N N' : ℕ} (m : ℕ) {G : VC D (N + m) N' → ℂ} (hG : Differentiable ℂ G)
    (α : Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (fun z : VC D N N' => G (pad D m z)) α =
      Formalism.MainNotions.TaylorLogMetric.taylor D G (Finsupp.embDomain (colEmb D N N' m) α) := by
  have han : AnalyticAt ℂ G 0 :=
    SCV.analyticAt_iff_eventually_differentiableAt.2 (Filter.Eventually.of_forall hG)
  rw [ConjSeries.taylor_eq_coeff, ConjSeries.taylor_eq_coeff, ← coeff_taylorDir_embDomain _ _ han]
  have h := taylorDir_comp_clm (LinearMap.toContinuousLinearMap (padL D m (N := N) (N' := N')))
    (coordV D) han
  simp only [LinearMap.coe_toContinuousLinearMap', padL_apply, pad_coordV] at h
  rw [h]

theorem mono_pad (D : D7) {N N' : ℕ} (m : ℕ) (α : Mono D N N') (z : VC D N N') :
    mono D (Finsupp.embDomain (colEmb D N N' m) α) (pad D m z) = mono D α z := by
  rw [mono, Finsupp.prod_embDomain]
  simp [mono, colEmb_apply]

theorem mem_range_of_mono_pad (D : D7) {N N' : ℕ} (m : ℕ) (β : Mono D (N + m) N') (z : VC D N N')
    (h : mono D β (pad D m z) ≠ 0) : β ∈ Set.range (Finsupp.embDomain (colEmb D N N' m)) := by
  rw [Finsupp.mem_range_embDomain_iff]
  rintro ⟨τ, a, i⟩ hk
  revert hk
  refine Fin.addCases (fun i _ => ⟨(τ, a, i), rfl⟩) (fun i hk => ?_) i
  refine absurd (Finset.prod_eq_zero hk ?_) h
  have : β (τ, a, Fin.natAdd N i) ≠ 0 := Finsupp.mem_support_iff.1 hk
  simp [this]

theorem fnConj_pad : ∀ (D : D7) (N N' m : ℕ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (G : VC D (N + m) N' → ℂ), Differentiable ℂ G → fnConj D M ρ (fun z : VC D N N' => G (pad D m z)) = fun z => fnConj D M ρ G (pad D m z) := by
  intro D N N' m M ρ G hG
  funext z
  simp only [fnConj]
  rw [← (Finsupp.embDomain_injective (colEmb D N N' m)).tsum_eq
    (f := fun β => ρ (TaylorLogMetric.liftM M (Formalism.MainNotions.TaylorLogMetric.taylor D G β)) * mono D β (pad D m z))
    (fun β hβ => mem_range_of_mono_pad D m β z (right_ne_zero_of_mul hβ))]
  simp only [taylor_pad D m hG, mono_pad]

end GlobalTheory.ConjRestrict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorConjugateTangentSpacePadZeroColumnsStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylorConjugate_tangentSpacePadZeroColumns : ∀ (D : D7) (N N' m : ℕ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (G : VC D (N + m) N' → ℂ), Differentiable ℂ G → fnConj D M ρ (fun z : VC D N N' => G (pad D m z)) = fun z => fnConj D M ρ G (pad D m z) := by
  first | exact @GlobalTheory.ConjRestrict.fnConj_pad | exact GlobalTheory.ConjRestrict.fnConj_pad | (intros; apply GlobalTheory.ConjRestrict.fnConj_pad <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOddPrimePhaseConjInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOddPrimePhaseConjInvariant
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.GalThetaSign

theorem sign_eq {p k k' : ℕ} {m m' : ℤ} {q : ℝ} (hp : Odd p) (h : (p : ℝ) ^ k * q = (m : ℝ))
    (h' : (p : ℝ) ^ k' * q = (m' : ℝ)) : (-1 : ℂ) ^ m' = (-1 : ℂ) ^ m := by
  have key : ∀ {a a' : ℕ} {b b' : ℤ}, a ≤ a' → (p : ℝ) ^ a * q = (b : ℝ) → (p : ℝ) ^ a' * q = (b' : ℝ) →
      (-1 : ℂ) ^ b' = (-1 : ℂ) ^ b := by
    intro a a' b b' hle hb hb'
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hle
    have hr : (b' : ℝ) = ((p : ℤ) ^ j * b : ℤ) := by
      rw [← hb', Int.cast_mul, Int.cast_pow, Int.cast_natCast, ← hb, pow_add]
      ring
    have hi : b' = (p : ℤ) ^ j * b := by exact_mod_cast hr
    have hoddp : Odd ((p : ℤ) ^ j) := (by exact_mod_cast hp : Odd (p : ℤ)).pow
    have hev : Even (b' - b) := by
      rw [hi, show (p : ℤ) ^ j * b - b = ((p : ℤ) ^ j - 1) * b by ring]
      exact (hoddp.sub_odd odd_one).mul_right b
    rw [show b' = b + (b' - b) by ring, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), hev.neg_one_zpow, mul_one]
  rcases le_total k k' with hle | hle
  · exact key hle h h'
  · exact (key hle h' h).symm

theorem wPh_eq (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') {p k : ℕ} {m : ℤ} (hp : p.Prime) (h2 : p ≠ 2)
    (h : (p : ℝ) ^ k * qH D T x = (m : ℝ)) : wPh D T p x = (-1 : ℂ) ^ m := by
  have hodd : Odd p := hp.odd_of_ne_two h2
  rw [wPh, if_neg h2]
  have hex : ∃ s : ℂ, ∃ (k : ℕ) (m : ℤ), (p : ℝ) ^ k * qH D T x = (m : ℝ) ∧ s = (-1 : ℂ) ^ m :=
    ⟨_, k, m, h, rfl⟩
  obtain ⟨k0, m0, h0, hs⟩ := Classical.epsilon_spec hex
  rw [hs]
  exact sign_eq hodd h h0

theorem ee_half_pow (q : ℝ) (n : ℕ) :
    ee (q / 2) ^ n = Complex.exp ((((n : ℝ) * q : ℝ) : ℂ) * ((Real.pi : ℂ) * Complex.I)) := by
  rw [ee, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem exp_int_pi (m : ℤ) : Complex.exp ((m : ℂ) * ((Real.pi : ℂ) * Complex.I)) = (-1 : ℂ) ^ m := by
  rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]

theorem cj_top_pow (σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (z : ℂ) (n : ℕ) :
    cj ⊤ σ (z ^ n) = cj ⊤ σ z ^ n := by
  have hl : ∀ w : ℂ, liftM ⊤ w = (⟨w, IntermediateField.mem_top⟩ : (⊤ : IntermediateField ℚ ℂ)) :=
    fun w => dif_pos IntermediateField.mem_top
  simp only [cj]
  rw [hl, hl, ← map_pow]
  congr 1

theorem cj_top_sign (σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (m : ℤ) :
    cj ⊤ σ ((-1 : ℂ) ^ m) = (-1 : ℂ) ^ m := by
  have hl : ∀ w : ℂ, liftM ⊤ w = (⟨w, IntermediateField.mem_top⟩ : (⊤ : IntermediateField ℚ ℂ)) :=
    fun w => dif_pos IntermediateField.mem_top
  have he : (⟨(-1 : ℂ) ^ m, IntermediateField.mem_top⟩ : (⊤ : IntermediateField ℚ ℂ)) = (-1) ^ m := by
    apply Subtype.ext
    change (-1 : ℂ) ^ m = (⊤ : IntermediateField ℚ ℂ).val ((-1) ^ m)
    rw [map_zpow₀, map_neg, map_one]
  simp only [cj]
  rw [hl, he, map_zpow₀, map_neg, map_one]

theorem wPh_conj : ∀ (D : D7) (T T' : Tor D) (N N' : ℕ) (x x' : VC D N N') (σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (p k : ℕ) (m : ℤ), p.Prime → p ≠ 2 → (p : ℝ) ^ k * qH D T x = (m : ℝ) → cj ⊤ σ (wdPh D T x) = wdPh D T' x' → wPh D T p x = (-1 : ℂ) ^ m ∧ wPh D T' p x' = (-1 : ℂ) ^ m := by
  intro D T T' N N' x x' σ p k m hp h2 h hcj
  refine ⟨wPh_eq D T x hp h2 h, ?_⟩
  have h1 : wdPh D T x ^ (p ^ k) = (-1 : ℂ) ^ m := by
    rw [wdPh, ee_half_pow, Nat.cast_pow, h, ← exp_int_pi m, Complex.ofReal_intCast]
  have h3 : wdPh D T' x' ^ (p ^ k) = (-1 : ℂ) ^ m := by
    rw [← hcj, ← cj_top_pow, h1, cj_top_sign]
  rw [wdPh, ee_half_pow, ← exp_int_pi m, Complex.exp_eq_exp_iff_exists_int] at h3
  obtain ⟨l, hl⟩ := h3
  have hπ : (Real.pi : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) Complex.I_ne_zero
  have hreal : (p : ℝ) ^ k * qH D T' x' = ((m + 2 * l : ℤ) : ℝ) := by
    have hc : (((p : ℝ) ^ k * qH D T' x' : ℝ) : ℂ) = (((m + 2 * l : ℤ) : ℝ) : ℂ) := by
      apply mul_right_cancel₀ hπ
      push_cast at hl ⊢
      linear_combination hl
    exact Complex.ofReal_injective hc
  rw [wPh_eq D T' x' hp h2 hreal, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), (even_two_mul l).neg_one_zpow, mul_one]

end GlobalTheory.GalThetaSign
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOddPrimePhaseConjInvariantStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaOddPrimePhase_conj_invariant : ∀ (D : D7) (T T' : Tor D) (N N' : ℕ) (x x' : VC D N N') (σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (p k : ℕ) (m : ℤ), p.Prime → p ≠ 2 → (p : ℝ) ^ k * qH D T x = (m : ℝ) → cj ⊤ σ (wdPh D T x) = wdPh D T' x' → wPh D T p x = (-1 : ℂ) ^ m ∧ wPh D T' p x' = (-1 : ℂ) ^ m := by
  first | exact @GlobalTheory.GalThetaSign.wPh_conj | exact GlobalTheory.GalThetaSign.wPh_conj | (intros; apply GlobalTheory.GalThetaSign.wPh_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumCoeffMonomial
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.MinorBound

theorem card_strictMono_le (a d : ℕ) [Fintype {s : Fin a → Fin d // StrictMono s}] :
    Fintype.card {s : Fin a → Fin d // StrictMono s} ≤ 2 ^ d := by
  have h : Function.Injective
      (fun s : {s : Fin a → Fin d // StrictMono s} => (Set.range s.1 : Set (Fin d))) := by
    intro s t hst
    exact Subtype.ext ((s.2.range_inj t.2).1 hst)
  have := Fintype.card_le_of_injective _ h
  simpa using this

theorem sum_coeff_monomial {σ : Type} (w : (σ →₀ ℕ) → ℂ) :
    ∃ L : MvPolynomial σ ℂ →ₗ[ℂ] ℂ, (∀ α c, L (MvPolynomial.monomial α c) = c * w α) ∧
      ∀ P, L P = ∑ α ∈ P.support, AddMonoidAlgebra.coeff P α * w α := by
  let L : MvPolynomial σ ℂ →ₗ[ℂ] ℂ := (MvPolynomial.basisMonomials σ ℂ).constr ℂ w
  have h1 : ∀ α c, L (MvPolynomial.monomial α c) = c * w α := by
    intro α c
    have : MvPolynomial.monomial α c = c • (MvPolynomial.basisMonomials σ ℂ) α := by
      simp [MvPolynomial.smul_monomial]
    rw [this, map_smul, Module.Basis.constr_basis, smul_eq_mul]
  refine ⟨L, h1, fun P => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [P.as_sum, map_sum]
  simp only [h1]

theorem prod_monomial {σ ι : Type} (s : Finset ι) (α : ι → σ →₀ ℕ) (c : ι → ℂ) :
    ∏ i ∈ s, MvPolynomial.monomial (α i) (c i) =
      MvPolynomial.monomial (∑ i ∈ s, α i) (∏ i ∈ s, c i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi, ih,
      MvPolynomial.monomial_mul]

noncomputable def expo (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n)
    (p : ∀ τ, Fin (n τ) → Equiv.Perm (Fin a)) : Mono D a d :=
  ∑ τ, ∑ j, ∑ i, Finsupp.single (τ, (T τ j).1 (p τ j i), i) 1

theorem minorPol_eq (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) :
    minorPol D T = ∑ p : (∀ τ, Fin (n τ) → Equiv.Perm (Fin a)),
      MvPolynomial.monomial (expo D T p) (∏ τ, ∏ j, (((Equiv.Perm.sign (p τ j) : ℤˣ) : ℤ) : ℂ)) := by
  unfold minorPol
  have hdet : ∀ τ (j : Fin (n τ)), (Matrix.of fun i i' : Fin a =>
      (MvPolynomial.X (τ, (T τ j).1 i, i') : MvPolynomial (GL3Theta.Idx D a d) ℂ)).det =
      ∑ σ : Equiv.Perm (Fin a), MvPolynomial.monomial
        (∑ i, Finsupp.single ((τ, (T τ j).1 (σ i), i) : GL3Theta.Idx D a d) 1)
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) := by
    intro τ j
    rw [Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Matrix.of_apply, MvPolynomial.X]
    rw [prod_monomial, ← map_intCast (MvPolynomial.C : ℂ →+* MvPolynomial (GL3Theta.Idx D a d) ℂ),
      MvPolynomial.C_mul_monomial]
    simp
  simp only [hdet]
  simp only [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr (by convert rfl) fun p _ => ?_
  simp only [prod_monomial, expo]

theorem expo_le (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n)
    (p : ∀ τ, Fin (n τ) → Equiv.Perm (Fin a)) (k : D.what₂.Tau × Fin d × Fin a) :
    expo D T p k ≤ n k.1 := by
  obtain ⟨τ0, r, c⟩ := k
  simp only [expo, Finset.sum_apply']
  rw [Finset.sum_eq_single τ0]
  · calc _ ≤ ∑ _j : Fin (n τ0), 1 := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [Finset.sum_eq_single c]
          · rw [Finsupp.single_apply]; split_ifs <;> simp
          · intro i _ hi
            rw [Finsupp.single_apply, if_neg]
            simp [hi]
          · simp
      _ = n τ0 := by simp
  · intro τ _ hτ
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    simp [hτ]
  · simp

theorem expo_sum (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n)
    (p : ∀ τ, Fin (n τ) → Equiv.Perm (Fin a)) :
    ((expo D T p).sum fun _ m => m) = a * ∑ τ, n τ := by
  have : ((expo D T p).sum fun _ m => m) = Finsupp.degree (expo D T p) := rfl
  rw [this]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [expo, map_sum, Finsupp.degree_single]
  simp [Finset.mul_sum, mul_comm]

theorem minor_bound : ∀ (D : D7) (a d : ℕ) (n : D.what₂.Tau → ℕ) (G : VC D a d → ℂ) (S A B : ℝ), 0 < A → 1 ≤ B → 0 ≤ S → (∀ τ, (n τ : ℝ) ≤ 2 * B) → Differentiable ℂ G → (∀ z, ‖G z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / A)) → (Fintype.card (Tup D a d n) ≤ 2 ^ (d * ∑ τ, n τ)) ∧ ∀ T : Tup D a d n, ‖GL3Theta.applyAt0 D (minorPol D T) G‖ ^ 2 ≤ ((a.factorial : ℝ) ^ (∑ τ, n τ)) ^ 2 * (S * (2 * Real.exp 1 * Real.pi * B / A) ^ (a * ∑ τ, n τ)) := by
  intro D a d n G S A B hA hB hS hn hG hbd
  constructor
  · simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [pow_mul, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod' fun τ _ => Nat.pow_le_pow_left (card_strictMono_le a d) _
  · intro T
    obtain ⟨L, hL1, hL2⟩ := sum_coeff_monomial
      (fun α : Mono D a d => (α.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G α)
    have h0 : GL3Theta.applyAt0 D (minorPol D T) G = L (minorPol D T) := by
      rw [hL2]; simp only [GL3Theta.applyAt0, mul_assoc]
    set M := S * (2 * Real.exp 1 * Real.pi * B / A) ^ (a * ∑ τ, n τ) with hM
    have hM0 : 0 ≤ M := by
      have : (0:ℝ) < B := by linarith
      have := Real.pi_pos
      positivity
    have hterm : ∀ p : (∀ τ, Fin (n τ) → Equiv.Perm (Fin a)),
        ‖L (MvPolynomial.monomial (expo D T p)
          (∏ τ, ∏ j, (((Equiv.Perm.sign (p τ j) : ℤˣ) : ℤ) : ℂ)))‖ ≤ Real.sqrt M := by
      intro p
      rw [hL1, norm_mul]
      have hs : ‖(∏ τ, ∏ j, (((Equiv.Perm.sign (p τ j) : ℤˣ) : ℤ) : ℂ))‖ = 1 := by
        rw [norm_prod]
        refine Finset.prod_eq_one fun τ _ => ?_
        rw [norm_prod]
        refine Finset.prod_eq_one fun j _ => ?_
        rcases Int.units_eq_one_or (Equiv.Perm.sign (p τ j)) with h | h <;> simp [h]
      rw [hs, one_mul]
      apply Real.le_sqrt_of_sq_le
      have := GlobalTheory.T.monomialDeriv_cauchy_bound_gaussianGrowth D a d G S A B hA hB hS hG hbd (expo D T p) (fun k =>
        le_trans (by exact_mod_cast expo_le D T p k) (hn k.1))
      rwa [expo_sum] at this
    have hcard : (Fintype.card (∀ τ, Fin (n τ) → Equiv.Perm (Fin a)) : ℝ) =
        (a.factorial : ℝ) ^ (∑ τ, n τ) := by
      simp [Fintype.card_pi, Fintype.card_perm, Finset.prod_pow_eq_pow_sum]
    have hle : ‖L (minorPol D T)‖ ≤ (a.factorial : ℝ) ^ (∑ τ, n τ) * Real.sqrt M := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [minorPol_eq, map_sum]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun p _ => hterm p).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    rw [h0]
    calc _ ≤ ((a.factorial : ℝ) ^ (∑ τ, n τ) * Real.sqrt M) ^ 2 := by gcongr
      _ = _ := by rw [mul_pow, Real.sq_sqrt hM0]

end GlobalTheory.MinorBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeriodThetaDifferentiableAndSignedTranslateI
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeriodThetaDifferentiableAndSignedTranslateI
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.HalfPeriodTheta

theorem parity_mod_two : ∀ a b c d s₁ s₂ x₁ x₂ : ZMod 2,
    a * a + b * c = a → a * b + b * d = b → c * a + d * c = c → c * b + d * d = d →
    ¬ (a * s₁ + c * s₂ = 0 ∧ b * s₁ + d * s₂ = 0) →
    ¬ (s₁ - (a * s₁ + c * s₂) = 0 ∧ s₂ - (b * s₁ + d * s₂) = 0) →
    (((a * x₁ + c * x₂) * x₂ - (b * x₁ + d * x₂) * x₁) + (x₁ * s₂ - x₂ * s₁) = 0 ↔ x₁ = 0 ∧ x₂ = 0) := by
  decide

theorem exists_orthonormal_basis_family (Λ : AddSubgroup ℂ) (ω t : ℂ) (G : ℂ → ℂ) (z : ℂ) :
    U1 Λ ω (U1 Λ t G) z =
      Complex.exp (-(Real.pi : ℂ) * Complex.I * (gl3FieldFirst Λ ω (2 * t) : ℂ)) * U1 Λ t (U1 Λ ω G) z := by
  have h : ((gl3FieldFirst Λ ω (2 * t) : ℝ) : ℂ) * Complex.I =
      (ω * (starRingEnd ℂ) t - t * (starRingEnd ℂ) ω) / (area Λ : ℂ) := by
    have h2 := Complex.sub_conj (ω * (starRingEnd ℂ) t)
    rw [map_mul, Complex.conj_conj, mul_comm ((starRingEnd ℂ) ω) t] at h2
    have h3 : (ω * (starRingEnd ℂ) (2 * t)).im = 2 * (ω * (starRingEnd ℂ) t).im := by
      simp; ring
    rw [h2, gl3FieldFirst, h3]
    push_cast
    ring
  have h' : -(Real.pi : ℂ) * Complex.I * (gl3FieldFirst Λ ω (2 * t) : ℂ) =
      -(Real.pi : ℂ) * ((ω * (starRingEnd ℂ) t - t * (starRingEnd ℂ) ω) / (area Λ : ℂ)) := by
    rw [← h]; ring
  rw [h']
  simp only [U1]
  rw [add_right_comm z t ω, mul_assoc (G _), mul_assoc (G _), ← Complex.exp_add, ← Complex.exp_add,
    mul_left_comm _ (G _), ← Complex.exp_add]
  congr 2
  ring

theorem even_im_hermitian_sub (Λ : AddSubgroup ℂ) (w₁ w₂ : ℂ) (hi : LinearIndependent ℝ ![w₁, w₂])
    (hΛ : Λ = AddSubgroup.closure {w₁, w₂})
    (hsd : ∀ z : ℂ, z ∈ Λ ↔ ∀ w ∈ Λ, ∃ m : ℤ, gl3FieldFirst Λ z w = m)
    (θ : ℂ) (N : ℤ) (hN : Even N) (hθ : θ * θ = θ - N) (hst : ∀ w ∈ Λ, θ * w ∈ Λ)
    (t : ℂ) (ht : 2 * t ∈ Λ) (h1 : θ * t ∉ Λ) (h2 : (1 - θ) * t ∉ Λ) (ω : ℂ) (hω : ω ∈ Λ) :
    ∃ m n : ℤ, gl3FieldFirst Λ (θ * ω) ω = m ∧ gl3FieldFirst Λ ω (2 * t) = n ∧ (Even (m + n) ↔ ω / 2 ∈ Λ) := by
  have mem : ∀ z, z ∈ Λ ↔ ∃ x y : ℤ, z = x * w₁ + y * w₂ := by
    intro z
    rw [hΛ, AddSubgroup.mem_closure_pair]
    simp only [zsmul_eq_mul, eq_comm]
  have uniq : ∀ x y : ℤ, (x : ℂ) * w₁ + y * w₂ = 0 → x = 0 ∧ y = 0 := by
    intro x y h
    have := LinearIndependent.pair_iff.1 hi (x : ℝ) (y : ℝ) (by simpa using h)
    exact_mod_cast this
  have half : ∀ x y : ℤ, ((x : ℂ) * w₁ + y * w₂) / 2 ∈ Λ ↔ (x : ZMod 2) = 0 ∧ (y : ZMod 2) = 0 := by
    intro x y
    rw [mem, ZMod.intCast_eq_zero_iff_even, ZMod.intCast_eq_zero_iff_even]
    constructor
    · rintro ⟨u, v, h⟩
      obtain ⟨e1, e2⟩ := uniq (x - 2 * u) (y - 2 * v) (by push_cast; linear_combination 2 * h)
      exact ⟨⟨u, by omega⟩, ⟨v, by omega⟩⟩
    · rintro ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩
      exact ⟨u, v, by push_cast; ring⟩
  have hw₁ : w₁ ∈ Λ := (mem _).2 ⟨1, 0, by simp⟩
  have hw₂ : w₂ ∈ Λ := (mem _).2 ⟨0, 1, by simp⟩
  obtain ⟨e, he⟩ := (hsd w₁).1 hw₁ w₂ hw₂
  have EFr : ∀ x y u v : ℝ, gl3FieldFirst Λ (x * w₁ + y * w₂) (u * w₁ + v * w₂) = (x * v - y * u) * e := by
    intro x y u v
    rw [← he]
    simp only [gl3FieldFirst]
    simp
    ring
  have EFi : ∀ x y u v : ℤ, gl3FieldFirst Λ (x * w₁ + y * w₂) (u * w₁ + v * w₂) = (((x * v - y * u) * e : ℤ) : ℝ) := by
    intro x y u v
    have := EFr x y u v
    push_cast at this ⊢
    exact this
  have hodd : (e : ZMod 2) = 1 := by
    rw [ZMod.intCast_eq_one_iff_odd, ← Int.not_even_iff_odd]
    rintro ⟨k, hk⟩
    have : (((1 : ℤ) : ℂ) * w₁ + ((0 : ℤ) : ℂ) * w₂) / 2 ∈ Λ := by
      rw [hsd]
      intro w hw
      obtain ⟨u, v, rfl⟩ := (mem _).1 hw
      refine ⟨v * k, ?_⟩
      have := EFr (1 / 2) 0 u v
      rw [hk] at this
      push_cast at this ⊢
      rw [show (1 * w₁ + 0 * w₂) / 2 = 1 / 2 * w₁ + 0 * w₂ by ring, this]
      ring
    rw [half] at this
    exact absurd this.1 (by decide)
  obtain ⟨a, b, hab⟩ := (mem _).1 (hst _ hw₁)
  obtain ⟨c, d, hcd⟩ := (mem _).1 (hst _ hw₂)
  obtain ⟨s₁, s₂, hs⟩ := (mem _).1 ht
  obtain ⟨x₁, x₂, rfl⟩ := (mem _).1 hω
  have mul : ∀ x y : ℤ, θ * ((x : ℂ) * w₁ + y * w₂) =
      ((a * x + c * y : ℤ) : ℂ) * w₁ + ((b * x + d * y : ℤ) : ℂ) * w₂ := by
    intro x y
    push_cast
    linear_combination (x : ℂ) * hab + (y : ℂ) * hcd
  obtain ⟨r1, r2⟩ := uniq (a * a + b * c - a + N) (a * b + b * d - b) (by
    push_cast
    linear_combination w₁ * hθ - (θ + a - 1) * hab - (b : ℂ) * hcd)
  obtain ⟨r3, r4⟩ := uniq (c * a + d * c - c) (c * b + d * d - d + N) (by
    push_cast
    linear_combination w₂ * hθ - (θ + d - 1) * hcd - (c : ℂ) * hab)
  have hN2 : (N : ZMod 2) = 0 := ZMod.intCast_eq_zero_iff_even.2 hN
  have q1 := congrArg (Int.cast : ℤ → ZMod 2) r1
  have q2 := congrArg (Int.cast : ℤ → ZMod 2) r2
  have q3 := congrArg (Int.cast : ℤ → ZMod 2) r3
  have q4 := congrArg (Int.cast : ℤ → ZMod 2) r4
  push_cast at q1 q2 q3 q4
  have e1 : θ * t = (((a * s₁ + c * s₂ : ℤ) : ℂ) * w₁ + ((b * s₁ + d * s₂ : ℤ) : ℂ) * w₂) / 2 := by
    rw [← mul, ← hs]; ring
  have e2 : (1 - θ) * t = (((s₁ - (a * s₁ + c * s₂) : ℤ) : ℂ) * w₁ + ((s₂ - (b * s₁ + d * s₂) : ℤ) : ℂ) * w₂) / 2 := by
    push_cast at e1 ⊢
    linear_combination (1 / 2) * hs - e1
  rw [e1, half] at h1
  rw [e2, half] at h2
  push_cast at h1 h2
  refine ⟨_, _, by rw [mul, EFi], by rw [hs, EFi], ?_⟩
  rw [half, ← ZMod.intCast_eq_zero_iff_even]
  push_cast
  rw [hodd, mul_one, mul_one]
  exact parity_mod_two _ _ _ _ _ _ _ _ (by linear_combination q1 - hN2) (by linear_combination q2)
    (by linear_combination q3) (by linear_combination q4 - hN2) h1 h2

theorem theta_signed_translation : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Differentiable ℂ (GL3Theta.th0 (lamOf D cc δ) t0) ∧ ∀ ω ∈ lamOf D cc δ, ∃ m : ℤ, q1 D (lamOf D cc δ) ω = (m : ℝ) ∧ ∀ z, (-1 : ℂ) ^ m * U1 (lamOf D cc δ) ω (GL3Theta.th0 (lamOf D cc δ) t0) z = GL3Theta.th0 (lamOf D cc δ) t0 z := by
  intro D hG cc δ hC t0 ht
  obtain ⟨hb, -, -, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hC
  set Λ := lamOf D cc δ
  obtain ⟨⟨hdiff, -, -, hlaw⟩, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hb
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hb
  obtain ⟨-, hsd⟩ := GlobalTheory.PlaneLattice.area_pos_and_selfDual L Λ hL
  obtain ⟨w₁, w₂, hi, hΛ⟩ := hb
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  have hd : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, D.host.d = 16 * k + 7 := ⟨D.host.d / 16, by omega⟩
  have hsq : ((Real.sqrt D.host.d : ℝ) : ℂ) * (Real.sqrt D.host.d : ℝ) = 16 * (k : ℂ) + 7 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), hk]
    push_cast; ring
  refine ⟨?_, fun ω hω => ?_⟩
  · unfold GL3Theta.th0 U1
    refine Differentiable.div_const (Differentiable.mul (hdiff.comp (differentiable_id.add_const _)) ?_) _
    fun_prop
  obtain ⟨m, n, hm, hn, hpar⟩ := even_im_hermitian_sub Λ w₁ w₂ hi hΛ hsd (w0 D) (4 * k + 2) ⟨2 * k + 1, by ring⟩
    (by
      unfold w0
      push_cast
      linear_combination (((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 / 4) * Complex.I_mul_I - (1 / 4) * hsq)
    (fun w hw => ha ▸ hst a w hw) t0 ht.1 ht.2.1
    (by
      have := ht.2.2
      convert this using 3
      unfold w0; ring) ω hω
  refine ⟨m, ?_, fun z => ?_⟩
  · rw [← hm, q1, gl3FieldFirst, mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, w0]
    rw [mul_comm ((1 + _) / 2 : ℂ), Complex.im_ofReal_mul]
    simp
    ring
  · have e1 : U1 Λ ω (GL3Theta.th0 Λ t0) z = U1 Λ ω (U1 Λ t0 (sgStar Λ)) z / U1 Λ t0 (sgStar Λ) 0 := by
      conv_lhs => rw [U1]
      conv_rhs => rw [U1]
      simp only [GL3Theta.th0]
      ring
    have e2 : U1 Λ t0 (U1 Λ ω (sgStar Λ)) z = (if ω / 2 ∈ Λ then 1 else -1) * U1 Λ t0 (sgStar Λ) z := by
      conv_lhs => rw [U1]
      rw [hlaw ω hω, mul_assoc]
      rfl
    have e3 : Complex.exp (-(Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ)) = (-1) ^ n := by
      rw [show -(Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ) = (n : ℂ) * (-(Real.pi * Complex.I)) by push_cast; ring,
        Complex.exp_int_mul, Complex.exp_neg, Complex.exp_pi_mul_I]
      norm_num
    have e4 : (-1 : ℂ) ^ m * (-1) ^ n * (if ω / 2 ∈ Λ then 1 else -1) = 1 := by
      rw [← zpow_add₀ (by norm_num)]
      split_ifs with h
      · rw [(hpar.2 h).neg_one_zpow]; simp
      · rw [(Int.not_even_iff_odd.1 (mt hpar.1 h)).neg_one_zpow]; simp
    rw [e1, exists_orthonormal_basis_family, hn, e2, e3]
    simp only [GL3Theta.th0]
    linear_combination (U1 Λ t0 (sgStar Λ) z / U1 Λ t0 (sgStar Λ) 0) * e4

end GlobalTheory.HalfPeriodTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HalfPeriodThetaDifferentiableAndSignedTranslateIStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfPeriodTheta_differentiable_and_signedTranslate_invariant : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 → Differentiable ℂ (GL3Theta.th0 (lamOf D cc δ) t0) ∧ ∀ ω ∈ lamOf D cc δ, ∃ m : ℤ, q1 D (lamOf D cc δ) ω = (m : ℝ) ∧ ∀ z, (-1 : ℂ) ^ m * U1 (lamOf D cc δ) ω (GL3Theta.th0 (lamOf D cc δ) t0) z = GL3Theta.th0 (lamOf D cc δ) t0 z := by
  first | exact @GlobalTheory.HalfPeriodTheta.theta_signed_translation | exact GlobalTheory.HalfPeriodTheta.theta_signed_translation | (intros; apply GlobalTheory.HalfPeriodTheta.theta_signed_translation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralUnfoldFundamentalDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralUnfoldFundamentalDomain
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory

theorem integral_unfold_fundamentalDomain : ∀ (V : Type) [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] (μ : Measure V) [μ.IsAddLeftInvariant] (Λ : AddSubgroup V) [Countable Λ] (Fd : Set V), IsAddFundamentalDomain Λ Fd μ → ∀ g : V → ℂ, Integrable g μ → IntegrableOn (fun z => ∑' y : Λ, g (z + y)) Fd μ ∧ ∫ z in Fd, ∑' y : Λ, g (z + y) ∂μ = ∫ z, g z ∂μ := by
  intro V _ _ _ _ μ _ Λ _ Fd hFd g hg
  have hv : ∀ (y : Λ) (z : V), y +ᵥ z = z + y := fun y z => by
    rw [add_comm]; rfl
  have hm : ∀ y : Λ, AEStronglyMeasurable (fun z => g (z + y)) (μ.restrict Fd) := fun y => by
    have h := (hg.comp_add_left (y : V)).aestronglyMeasurable
    simp only [add_comm (y : V)] at h
    exact h.restrict
  have hfin : ∑' y : Λ, ∫⁻ z in Fd, ‖g (z + y)‖ₑ ∂μ ≠ ⊤ := by
    have h := hFd.lintegral_eq_tsum'' (fun z => ‖g z‖ₑ)
    simp only [hv] at h
    rw [← h]
    exact hg.2.ne
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have : AEMeasurable (fun z => ∑' y : Λ, g (z + y)) (μ.restrict Fd) :=
      AEMeasurable.tsum fun y => (hm y).aemeasurable
    exact this.aestronglyMeasurable
  · refine lt_of_le_of_lt (lintegral_mono fun z => enorm_tsum_le_tsum_enorm) ?_
    rw [lintegral_tsum fun y => (hm y).enorm]
    exact hfin.lt_top
  · rw [integral_tsum hm hfin, hFd.integral_eq_tsum'' g hg]
    simp only [hv]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralUnfoldFundamentalDomainStatement
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setIntegral_tsum_translate_eq_integral : ∀ (V : Type) [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] (μ : Measure V) [μ.IsAddLeftInvariant] (Λ : AddSubgroup V) [Countable Λ] (Fd : Set V), IsAddFundamentalDomain Λ Fd μ → ∀ g : V → ℂ, Integrable g μ → IntegrableOn (fun z => ∑' y : Λ, g (z + y)) Fd μ ∧ ∫ z in Fd, ∑' y : Λ, g (z + y) ∂μ = ∫ z, g z ∂μ := by
  first | exact @GlobalTheory.integral_unfold_fundamentalDomain | exact GlobalTheory.integral_unfold_fundamentalDomain | (intros; apply GlobalTheory.integral_unfold_fundamentalDomain <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedTranslateClassInvariantOfMemThetaSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedTranslateClassInvariantOfMemThetaSpace
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj

theorem ee_intCast_half (n : ℤ) : ee ((n : ℝ) / 2) = (-1 : ℂ) ^ n := by
  unfold ee
  rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem al_of_qH (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (m : ℤ) (h : qH D T x = m) :
    al D T x = (-1 : ℂ) ^ m := by
  unfold qH at h
  unfold al
  rw [h, round_intCast]

theorem qH_add_im (D : D7) (T : Tor D) {N N' : ℕ} (y u : VC D N N') :
    qH D T (y + u) - qH D T y - qH D T u + (Hf D T y u).im = 2 * (Hf D T (w0 D • y) u).im := by
  unfold qH
  rw [Hf_smul_left, Hf_add_left, Hf_add_right, Hf_add_right, Hf_conj D T y u]
  have h1 : (w0 D).re = 1 / 2 := by simp [w0]
  have h2 : (w0 D).im = Real.sqrt D.host.d / 2 := by simp [w0]
  simp only [Complex.add_re, Complex.conj_re, Complex.mul_im, h1, h2]
  ring

theorem repInd_of_thSp (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ : AddSubgroup (VC D N N'))
    (F : VC D N N' → ℂ) (hq : ∀ x ∈ A₂, ∃ m : ℤ, qH D T x = m)
    (hw : ∀ x ∈ A₂, ∀ y ∈ A₂, ∃ m : ℤ, (Hf D T (w0 D • x) y).im = m) (hF : F ∈ ThSp D T A₁) :
    RepInd D T A₁ A₂ F := by
  intro x hx y hy hxy
  have hu2 : x - y ∈ A₂ := A₂.sub_mem hx hy
  obtain ⟨u, rfl⟩ : ∃ u, x = y + u := ⟨x - y, by abel⟩
  rw [add_sub_cancel_left] at hxy hu2
  obtain ⟨a, ha⟩ := hq _ hx
  obtain ⟨b, hb⟩ := hq _ hy
  obtain ⟨c, hc⟩ := hq _ hu2
  obtain ⟨k, hk⟩ := hw _ hy _ hu2
  have h1 := qH_add_im D T y u
  rw [ha, hb, hc, hk] at h1
  have h2 : -(Hf D T y u).im = ((a - b - c - 2 * k : ℤ) : ℝ) := by push_cast; linarith
  funext z
  have h3 := U_U D T y u F z
  rw [h2, ee_intCast_half] at h3
  have h4 : al D T u * U D T y (U D T u F) z = U D T y F z := by
    have := hF.2 u hxy (z + y)
    conv_lhs => rw [U]
    conv_rhs => rw [U]
    rw [← mul_assoc, this]
  unfold aU
  rw [← h4, h3, al_of_qH D T _ _ ha, al_of_qH D T _ _ hb, al_of_qH D T _ _ hc, ← mul_assoc,
    ← mul_assoc, ← zpow_add₀ (by norm_num), ← zpow_add₀ (by norm_num)]
  congr 1
  have : b + c + (a - b - c - 2 * k) = a + 2 * (-k) := by ring
  rw [this, zpow_add₀ (by norm_num), zpow_mul]
  norm_num

end GlobalTheory.ThetaConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedTranslateClassInvariantOfMemThetaSpaceStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedTranslateClassInvariant_of_mem_thetaSpace : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ : AddSubgroup (VC D N N')) (F : VC D N N' → ℂ), (∀ x ∈ A₂, ∃ m : ℤ, qH D T x = m) → (∀ x ∈ A₂, ∀ y ∈ A₂, ∃ m : ℤ, (Hf D T (w0 D • x) y).im = m) → F ∈ ThSp D T A₁ → RepInd D T A₁ A₂ F := by
  first | exact @GlobalTheory.ThetaConj.repInd_of_thSp | exact GlobalTheory.ThetaConj.repInd_of_thSp | (intros; apply GlobalTheory.ThetaConj.repInd_of_thSp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomLatticeCommensurableOrthonormal
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomLatticeCommensurableOrthonormal
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators

namespace GlobalTheory.ThetaConj

theorem exists_nat_common_denom {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] (c : ι → K) :
    ∃ k : ℕ, 0 < k ∧ ∀ i, ∃ a : 𝓞 K, (a : K) = (k : K) * c i := by
  obtain ⟨m, hm0, hm⟩ := exists_integral_multiples ℤ ℚ (L := K) (Finset.univ.image c)
  refine ⟨(m * m).natAbs, Int.natAbs_pos.2 (mul_ne_zero hm0 hm0), fun i => ?_⟩
  have h := hm (c i) (Finset.mem_image_of_mem _ (Finset.mem_univ i))
  refine ⟨(m : 𝓞 K) * ⟨m • c i, h⟩, ?_⟩
  have h2 : (((m * m).natAbs : ℕ) : K) = (m : K) * m := by
    rw [← Int.cast_natCast, Int.natAbs_of_nonneg (mul_self_nonneg m)]; push_cast; rfl
  rw [h2]
  change ((m : 𝓞 K) : K) * (m • c i) = _
  simp [mul_assoc]

theorem smul_mem_YYl (D : D7) {N N' : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (a : 𝓞 D.host.K)
    {y : Matrix (Fin N') (Fin N) D.host.E} (hy : y ∈ YYl D L L') : (a : D.host.K) • y ∈ YYl D L L' := by
  have h := (YYl D L L').smul_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) a) hy
  exact h

theorem exists_comm_YYl (D : D7) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)
    (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E))
    (hb : OnB D b) (hL : SD D L) (hL' : SD D L') :
    ∃ k : ℕ, 0 < k ∧ Comm D b k (YYl D L L' : Set (Matrix (Fin N') (Fin N) D.host.E)) := by
  obtain ⟨s, y, y', hy, hy', hexp⟩ := GlobalTheory.HomDual.exists_dual_family_hom D
    (GlobalTheory.exists_trace_dual_family_halfDifferent D) N N' L L' hL hL'
  have hc : ∀ i, ∃ c : Fin r → D.host.K, ∑ j, c j • b j = y i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun D.host.K).1 (by rw [hb.2]; trivial)
  choose c hc using hc
  obtain ⟨k, hk, hden⟩ := exists_nat_common_denom (K := D.host.K) (ι := (Fin s × Fin r) ⊕ (Fin s × Fin r))
    (Sum.elim (fun p => c p.1 p.2) (fun p => hYY D (b p.2) (y' p.1)))
  choose a ha using hden
  refine ⟨k, hk, fun x hx => ?_, fun j => ?_⟩
  · have hi : ∀ i, ∃ t : 𝓞 D.host.K, (t : D.host.K) = hYY D x (y' i) := fun i =>
      GlobalTheory.NormSum.TraceInt.hYY_integral D N N' L L' hL hL' x hx (y' i) (hy' i)
    choose t ht using hi
    refine ⟨fun j => ∑ i, t i * a (Sum.inl (i, j)), ?_⟩
    conv_lhs => rw [hexp x]
    rw [← Nat.cast_smul_eq_nsmul D.host.K]
    simp only [← hc, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_smul]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingOfIntegers.coe_eq_algebraMap, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← RingOfIntegers.coe_eq_algebraMap, ← RingOfIntegers.coe_eq_algebraMap, ha, ht]
    simp only [Sum.elim_inl]
    ring
  · apply AddSubgroup.subset_closure
    rw [hexp (b j), ← Nat.cast_smul_eq_nsmul D.host.K, Finset.smul_sum]
    refine (YYl D L L').sum_mem fun i _ => ?_
    rw [smul_smul]
    have := ha (Sum.inr (i, j))
    simp only [Sum.elim_inr] at this
    rw [← this]
    exact smul_mem_YYl D L L' _ (hy i)

end GlobalTheory.ThetaConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomLatticeCommensurableOrthonormalStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homLattice_commensurable_orthonormal : ∀ (D : D7) (N N' r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), OnB D b → SD D L → SD D L' → ∃ k : ℕ, 0 < k ∧ Comm D b k (YYl D L L' : Set (Matrix (Fin N') (Fin N) D.host.E)) := by
  first | exact @GlobalTheory.ThetaConj.exists_comm_YYl | exact GlobalTheory.ThetaConj.exists_comm_YYl | (intros; apply GlobalTheory.ThetaConj.exists_comm_YYl <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableExpNegHerm
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableExpNegHerm
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta.GaussSumm

theorem exists_mul_norm_sq_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    (H : Sesq V) (hH : IsPosHerm H) : ∃ c : ℝ, 0 < c ∧ ∀ x : V, c * ‖x‖ ^ 2 ≤ (H x x).re := by
  have hcont : Continuous fun x : V => (H x x).re := by
    let b := Module.finBasis ℂ V
    have e : (fun x : V => H x x) = fun x => ∑ i, H x (b i) * conj (b.repr x i) := by
      funext x
      conv_lhs => rw [show H x x = H x (∑ i, b.repr x i • b i) by rw [b.sum_repr]]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [LinearMap.map_smulₛₗ, smul_eq_mul, mul_comm]
    have : Continuous fun x : V => H x x := by
      rw [e]
      refine continuous_finsetSum _ fun i _ => ?_
      have h1 : Continuous fun x : V => H x (b i) :=
        (H.flip (b i)).continuous_of_finiteDimensional
      have h2 : Continuous fun x : V => b.repr x i :=
        (b.coord i).continuous_of_finiteDimensional
      exact h1.mul (continuous_conj.comp h2)
    exact continuous_re.comp this
  haveI : ProperSpace V := FiniteDimensional.proper ℂ V
  obtain ⟨c, hc, hle⟩ : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ Metric.sphere (0 : V) 1, c ≤ (H x x).re := by
    refine (isCompact_sphere (0 : V) 1).exists_forall_le' hcont.continuousOn fun x hx => hH.2 x ?_
    rintro rfl
    simp at hx
  refine ⟨c, hc, fun x => ?_⟩
  by_cases hx : x = 0
  · subst hx
    simp
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h1 := hle (((‖x‖⁻¹ : ℝ) : ℂ) • x) (by
    rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, norm_inv, norm_norm,
      inv_mul_cancel₀ hn.ne'])
  have e : H (((‖x‖⁻¹ : ℝ) : ℂ) • x) (((‖x‖⁻¹ : ℝ) : ℂ) • x) = ((‖x‖⁻¹ ^ 2 : ℝ) : ℂ) * H x x := by
    rw [LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, conj_ofReal, smul_eq_mul, smul_eq_mul]
    push_cast
    ring
  rw [e, re_ofReal_mul] at h1
  have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg ‖x‖)
  have e2 : ‖x‖⁻¹ ^ 2 * (H x x).re * ‖x‖ ^ 2 = (H x x).re := by field_simp
  rwa [e2] at h2

theorem exp_le_inv_pow {a : ℝ} (ha : 0 < a) (C : ℝ) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    Real.exp (-(a * t ^ 2) + C * t) ≤ (k.factorial * Real.exp ((C + 1) ^ 2 / (4 * a))) * t⁻¹ ^ k := by
  have h1 : t ^ k / k.factorial ≤ Real.exp t := Real.pow_div_factorial_le_exp t ht.le k
  have hk : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [div_le_iff₀ hk] at h1
  have h2 : -(a * t ^ 2) + C * t + t ≤ (C + 1) ^ 2 / (4 * a) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * a * t - (C + 1))]
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc Real.exp (-(a * t ^ 2) + C * t) * t ^ k
      ≤ Real.exp (-(a * t ^ 2) + C * t) * (Real.exp t * k.factorial) := by gcongr
    _ = k.factorial * Real.exp (-(a * t ^ 2) + C * t + t) := by rw [Real.exp_add _ t]; ring
    _ ≤ _ := by gcongr

theorem summable_exp_neg_herm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [DiscreteTopology Λ] (C : ℝ), Summable (fun x : Λ => Real.exp (-(π / 2) * (H x x).re + C * ‖(x : V)‖)) := by
  intro V _ _ _ H hH Λ _ C
  obtain ⟨c, hc, hle⟩ := exists_mul_norm_sq_le H hH
  letI : NormedSpace ℝ V := NormedSpace.complexToReal
  haveI : FiniteDimensional ℝ V := FiniteDimensional.complexToReal V
  let L : Submodule ℤ V := AddSubgroup.toIntSubmodule Λ
  haveI : DiscreteTopology L := ‹DiscreteTopology Λ›
  have hs : Summable fun x : Λ => ‖(x : V)‖⁻¹ ^ (Module.finrank ℤ L + 1) :=
    ZLattice.summable_norm_pow_inv L (Module.finrank ℤ L + 1) (Nat.lt_succ_self _)
  have ha : 0 < π / 2 * c := by have := Real.pi_pos; positivity
  refine Summable.of_norm_bounded_eventually (hs.mul_left
    ((Module.finrank ℤ L + 1).factorial * Real.exp ((C + 1) ^ 2 / (4 * (π / 2 * c))))) ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : Λ)] with x hx
  have hn : 0 < ‖(x : V)‖ := norm_pos_iff.2 fun h => hx (Subtype.ext h)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine le_trans (Real.exp_le_exp.2 ?_) (exp_le_inv_pow ha C _ hn)
  have := mul_le_mul_of_nonneg_left (hle x) (by have := Real.pi_pos; positivity : 0 ≤ π / 2)
  linarith

end GlobalTheory.UnitaryTheta.GaussSumm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SummableExpNegHermStatement
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_exp_neg_herm_add_norm : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V), IsPosHerm H → ∀ (Λ : AddSubgroup V) [DiscreteTopology Λ] (C : ℝ), Summable (fun x : Λ => Real.exp (-(π / 2) * (H x x).re + C * ‖(x : V)‖)) := by
  first | exact @GlobalTheory.UnitaryTheta.GaussSumm.summable_exp_neg_herm | exact GlobalTheory.UnitaryTheta.GaussSumm.summable_exp_neg_herm | (intros; apply GlobalTheory.UnitaryTheta.GaussSumm.summable_exp_neg_herm <;> assumption)
end
end
