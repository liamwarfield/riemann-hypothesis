module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeAdjointThLeSpanGood

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmallB
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

def IsSmallB (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type}
    (b : Module.Basis κ ℚ M) (y : v.adicCompletion ℚ ⊗[ℚ] M) : Prop :=
  ∀ i, Valued.v ((Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y i) < 1

end GlobalTheory.AdicSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedNormModMaxIdealAdicTensor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedNormModMaxIdealAdicTensor
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.ResidueNorm

variable (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type}
  (b : Module.Basis κ ℚ M)

theorem isIntB_add {x y : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsIntB v b x) (hy : IsIntB v b y) :
    IsIntB v b (x + y) := fun i => by
  rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (hx i) (hy i)

theorem isIntB_neg {x : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsIntB v b x) : IsIntB v b (-x) := fun i => by
  rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hx i)

theorem isSmallB_add {x y : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsSmallB v b x) (hy : IsSmallB v b y) :
    IsSmallB v b (x + y) := fun i => by
  rw [map_add (f := _), Finsupp.add_apply]; exact Valuation.map_add_lt _ (hx i) (hy i)

theorem isSmallB_zero : IsSmallB v b (0 : v.adicCompletion ℚ ⊗[ℚ] M) := fun i => by simp

theorem isSmallB_sub_of_residue_eq {x y : v.adicCompletion ℚ ⊗[ℚ] M} (hx : IsIntB v b x) (hy : IsIntB v b y)
    (h : ∀ i, IsLocalRing.residue (v.adicCompletionIntegers ℚ) ⟨_, hx i⟩ =
      IsLocalRing.residue (v.adicCompletionIntegers ℚ) ⟨_, hy i⟩) : IsSmallB v b (x - y) := fun i => by
  have h0 : IsLocalRing.residue (v.adicCompletionIntegers ℚ) (⟨_, hx i⟩ - ⟨_, hy i⟩) = 0 := by
    rw [map_sub, h i, sub_self]
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h0
  have h1 := Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp h0
  rw [map_sub, Finsupp.sub_apply]
  exact h1

theorem eq_neg_inv_of_mul_neg {R : Type*} [CommRing R] (u : Rˣ) (x : R) (h : x * -↑u = 1) : x = -↑u⁻¹ := by
  have k2 : (↑u : R) * ↑u⁻¹ = 1 := Units.mul_inv u
  linear_combination (-(↑u⁻¹ : R)) * h + (-x) * k2

theorem eq_inv_of_mul {R : Type*} [CommRing R] (u : Rˣ) (x : R) (h : x * ↑u = 1) : x = ↑u⁻¹ := by
  have k2 : (↑u : R) * ↑u⁻¹ = 1 := Units.mul_inv u
  linear_combination (↑u⁻¹ : R) * h - x * k2

theorem sq_mul_inv_sq {R : Type*} [CommRing R] (u : Rˣ) : (↑u * ↑u : R) * (↑u⁻¹ * ↑u⁻¹) = 1 := by
  rw [mul_mul_mul_comm, Units.mul_inv, one_mul]

theorem norm_expand {R : Type*} [CommRing R] (a b t e : R) :
    (a + b * t) * (a - b * t) - e = a ^ 2 - t * t * b ^ 2 - e := by ring

end GlobalTheory.ResidueNorm


open GlobalTheory.ResidueNorm in
theorem GlobalTheory.ResidueNorm.exists_norm_mod_small : ∀ (v : HeightOneSpectrum ℤ) (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) →
    ∀ (κ : Type) (bL : Module.Basis κ ℚ L),
    Valued.v (2 : v.adicCompletion ℚ) = 1 → IsIntB v bL 1 →
    (∀ x y, IsIntB v bL x → IsIntB v bL y → IsIntB v bL (x * y)) →
    (∀ x y, IsIntB v bL x → IsSmallB v bL y → IsSmallB v bL (x * y)) →
    (∀ x, IsIntB v bL x → IsIntB v bL (Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c x)) →
    ∀ θ : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, IsIntB v bL ↑θ → IsIntB v bL ↑θ⁻¹ →
    Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑θ = -↑θ →
    ∀ e : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑e = ↑e →
    IsIntB v bL ↑e → IsIntB v bL ↑e⁻¹ →
    ∃ z : v.adicCompletion ℚ ⊗[ℚ] L, IsIntB v bL z ∧
      IsSmallB v bL (z * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c z - ↑e) := by
  intro v L _ _ c _ κ bL h2 h1 hmul hsm _ θ hθ hθi hσθ e hσe he hei
  set σ := Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c with hσdef

  obtain ⟨P, hP⟩ : ∃ P : Subring (v.adicCompletion ℚ ⊗[ℚ] L), ∀ x, x ∈ P ↔ IsIntB v bL x ∧ σ x = x := ⟨
    { carrier := {x | IsIntB v bL x ∧ σ x = x}
      mul_mem' := fun {a b} ha hb => ⟨hmul a b ha.1 hb.1, by rw [map_mul, ha.2, hb.2]⟩
      one_mem' := ⟨h1, map_one σ⟩
      add_mem' := fun {a b} ha hb => ⟨isIntB_add v bL ha.1 hb.1, by rw [map_add (f := _), ha.2, hb.2]⟩
      zero_mem' := ⟨isIntB_zero v bL, map_zero σ⟩
      neg_mem' := fun {a} ha => ⟨isIntB_neg v bL ha.1, by rw [map_neg, ha.2]⟩ }, fun x => Iff.rfl⟩
  have hPi : ∀ x : P, IsIntB v bL (x : v.adicCompletion ℚ ⊗[ℚ] L) := fun x => ((hP _).1 x.2).1
  have hPs : ∀ x : P, σ (x : v.adicCompletion ℚ ⊗[ℚ] L) = x := fun x => ((hP _).1 x.2).2
  obtain ⟨I, hmemI⟩ : ∃ I : Ideal P, ∀ x : P, x ∈ I ↔ IsSmallB v bL (x : v.adicCompletion ℚ ⊗[ℚ] L) := ⟨
    { carrier := {x | IsSmallB v bL (x : v.adicCompletion ℚ ⊗[ℚ] L)}
      add_mem' := fun {a b} ha hb => isSmallB_add v bL ha hb
      zero_mem' := isSmallB_zero v bL
      smul_mem' := fun a b hb => hsm _ _ (hPi a) hb }, fun x => Iff.rfl⟩

  haveI : Finite κ := Module.Finite.finite_basis bL
  haveI : Finite (ℤ ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  haveI : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) :=
    Finite.of_equiv _ (GroundTheory.Global.residueFieldEquiv (K := ℚ) v).toEquiv
  let φ : P → κ → IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ) := fun x i =>
    IsLocalRing.residue _ ⟨_, hPi x i⟩
  let out := Function.surjInv (Ideal.Quotient.mk_surjective (I := I))
  haveI : Finite (P ⧸ I) := by
    refine Finite.of_injective (fun q => φ (out q)) fun q1 q2 h => ?_
    rw [← Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := I)) q1,
      ← Function.surjInv_eq (Ideal.Quotient.mk_surjective (I := I)) q2, Ideal.Quotient.eq, hmemI]
    exact isSmallB_sub_of_residue_eq v bL (hPi (out q1)) (hPi (out q2)) fun i => congrFun h i

  have hσθi : σ ↑θ⁻¹ = -↑θ⁻¹ :=
    eq_neg_inv_of_mul_neg θ _ (by rw [← hσθ, ← map_mul, Units.inv_mul, map_one])
  have hσei : σ ↑e⁻¹ = ↑e⁻¹ :=
    eq_inv_of_mul e _ (by rw [← hσe, ← map_mul, Units.inv_mul, map_one])

  have memP : ∀ x, IsIntB v bL x → σ x = x → x ∈ P := fun x h h' => (hP x).2 ⟨h, h'⟩
  have hθθ : σ (↑θ * ↑θ) = ↑θ * ↑θ := by rw [map_mul, hσθ, neg_mul_neg]
  have hθθi : σ (↑θ⁻¹ * ↑θ⁻¹) = ↑θ⁻¹ * ↑θ⁻¹ := by rw [map_mul, hσθi, neg_mul_neg]
  have dmem : (↑θ * ↑θ : v.adicCompletion ℚ ⊗[ℚ] L) ∈ P := memP _ (hmul _ _ hθ hθ) hθθ
  let dP : P := ⟨_, dmem⟩
  have dimem : (↑θ⁻¹ * ↑θ⁻¹ : v.adicCompletion ℚ ⊗[ℚ] L) ∈ P := memP _ (hmul _ _ hθi hθi) hθθi
  let diP : P := ⟨_, dimem⟩
  have emem : (↑e : v.adicCompletion ℚ ⊗[ℚ] L) ∈ P := memP _ he hσe
  let eP : P := ⟨_, emem⟩
  have eimem : (↑e⁻¹ : v.adicCompletion ℚ ⊗[ℚ] L) ∈ P := memP _ hei hσei
  let eiP : P := ⟨_, eimem⟩
  have hhalf : (2⁻¹ : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, h2, inv_one]
  have hmem2 : ((2⁻¹ : v.adicCompletion ℚ) • (1 : v.adicCompletion ℚ ⊗[ℚ] L)) ∈ P := memP _ (fun i => by
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]; exact mul_mem hhalf (h1 i)) (by
      rw [Algebra.smul_def, mul_one, Algebra.TensorProduct.algebraMap_apply, hσdef,
        Algebra.TensorProduct.map_tmul, map_one]; rfl)
  let hh : P := ⟨_, hmem2⟩
  have h2P : (2 : P) * hh = 1 := by
    apply Subtype.ext
    show (2 : v.adicCompletion ℚ ⊗[ℚ] L) * ((2⁻¹ : v.adicCompletion ℚ) • 1) = 1
    have h20 : (2 : v.adicCompletion ℚ) ≠ 0 := by
      intro h; rw [h, map_zero] at h2; exact zero_ne_one h2
    rw [mul_smul_comm, mul_one, ← map_ofNat (algebraMap (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L)) 2,
      Algebra.algebraMap_eq_smul_one, smul_smul, inv_mul_cancel₀ h20, one_smul]
  have hdP : dP * diP = 1 := by
    apply Subtype.ext
    show (↑θ * ↑θ : v.adicCompletion ℚ ⊗[ℚ] L) * (↑θ⁻¹ * ↑θ⁻¹) = 1
    exact sq_mul_inv_sq θ
  have heP : eP * eiP = 1 := Subtype.ext (Units.mul_inv e)
  obtain ⟨a', b', hab⟩ := GlobalTheory.FinRingNorm.exists_sq_sub_mul_sq_eq (P ⧸ I)
    (IsUnit.of_mul_eq_one (Ideal.Quotient.mk I hh) (by rw [← map_ofNat (Ideal.Quotient.mk I) 2, ← map_mul, h2P, map_one]))
    (Ideal.Quotient.mk I dP) (Ideal.Quotient.mk I eP)
    (IsUnit.of_mul_eq_one (Ideal.Quotient.mk I diP) (by rw [← map_mul, hdP, map_one]))
    (IsUnit.of_mul_eq_one (Ideal.Quotient.mk I eiP) (by rw [← map_mul, heP, map_one]))
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a'
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b'
  set_option synthInstance.maxHeartbeats 200000 in
  have hmem : a ^ 2 - dP * b ^ 2 - eP ∈ I := by
    refine Ideal.Quotient.eq.1 ?_
    simpa only [map_sub (Ideal.Quotient.mk I), map_mul (Ideal.Quotient.mk I),
      map_pow (Ideal.Quotient.mk I)] using hab
  rw [hmemI] at hmem
  refine ⟨(a : v.adicCompletion ℚ ⊗[ℚ] L) + (b : v.adicCompletion ℚ ⊗[ℚ] L) * (θ : v.adicCompletion ℚ ⊗[ℚ] L), isIntB_add v bL (hPi a) (hmul _ _ (hPi b) hθ), ?_⟩
  have hσz : σ ((a : v.adicCompletion ℚ ⊗[ℚ] L) + (b : v.adicCompletion ℚ ⊗[ℚ] L) * (θ : v.adicCompletion ℚ ⊗[ℚ] L)) = (a : v.adicCompletion ℚ ⊗[ℚ] L) - (b : v.adicCompletion ℚ ⊗[ℚ] L) * (θ : v.adicCompletion ℚ ⊗[ℚ] L) := by
    rw [map_add (f := _), map_mul, hPs a, hPs b, hσθ, mul_neg, ← sub_eq_add_neg]
  rw [hσz, norm_expand]
  exact hmem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwistedNormModMaxIdealAdicTensorStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_twistedNorm_mod_maxIdeal_adicTensor : ∀ (v : HeightOneSpectrum ℤ) (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) →
    ∀ (κ : Type) (bL : Module.Basis κ ℚ L),
    Valued.v (2 : v.adicCompletion ℚ) = 1 → IsIntB v bL 1 →
    (∀ x y, IsIntB v bL x → IsIntB v bL y → IsIntB v bL (x * y)) →
    (∀ x y, IsIntB v bL x → IsSmallB v bL y → IsSmallB v bL (x * y)) →
    (∀ x, IsIntB v bL x → IsIntB v bL (Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c x)) →
    ∀ θ : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, IsIntB v bL ↑θ → IsIntB v bL ↑θ⁻¹ →
    Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑θ = -↑θ →
    ∀ e : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑e = ↑e →
    IsIntB v bL ↑e → IsIntB v bL ↑e⁻¹ →
    ∃ z : v.adicCompletion ℚ ⊗[ℚ] L, IsIntB v bL z ∧
      IsSmallB v bL (z * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c z - ↑e) := by
  first | (exact @GlobalTheory.ResidueNorm.exists_norm_mod_small) | (exact GlobalTheory.ResidueNorm.exists_norm_mod_small) | (intros; apply GlobalTheory.ResidueNorm.exists_norm_mod_small  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisHenselExistsUniqueSqrt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisHenselExistsUniqueSqrt
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan.HenselSqrt

open IsDedekindDomain.HeightOneSpectrum WithZero

variable (v : HeightOneSpectrum ℤ) {L : Type} [Field L] [NumberField L] {κ : Type}
  (bL : Module.Basis κ ℚ L)

theorem isIntB_add {x y : v.adicCompletion ℚ ⊗[ℚ] L} (hx : IsIntB v bL x) (hy : IsIntB v bL y) :
    IsIntB v bL (x + y) := fun i => by
  rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (hx i) (hy i)

theorem isIntB_neg {x : v.adicCompletion ℚ ⊗[ℚ] L} (hx : IsIntB v bL x) : IsIntB v bL (-x) := fun i => by
  rw [map_neg, Finsupp.neg_apply]; exact neg_mem (hx i)

theorem isIntB_smul {a : v.adicCompletion ℚ} (ha : a ∈ v.adicCompletionIntegers ℚ)
    {x : v.adicCompletion ℚ ⊗[ℚ] L} (hx : IsIntB v bL x) : IsIntB v bL (a • x) := fun i => by
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul]; exact mul_mem ha (hx i)

theorem isSmallB_neg {x : v.adicCompletion ℚ ⊗[ℚ] L} (hx : IsSmallB v bL x) : IsSmallB v bL (-x) := fun i => by
  rw [map_neg, Finsupp.neg_apply, Valuation.map_neg]; exact hx i

variable (h1 : IsIntB v bL 1) (hmul : ∀ x y, IsIntB v bL x → IsIntB v bL y → IsIntB v bL (x * y))

def lam : Subring (v.adicCompletion ℚ ⊗[ℚ] L) where
  carrier := {x | IsIntB v bL x}
  mul_mem' := fun {x y} hx hy => hmul x y hx hy
  one_mem' := h1
  add_mem' := fun hx hy => isIntB_add v bL hx hy
  zero_mem' := isIntB_zero v bL
  neg_mem' := fun hx => isIntB_neg v bL hx

def unif (π : v.adicCompletionIntegers ℚ) : lam v bL h1 hmul :=
  ⟨(π : v.adicCompletion ℚ) • 1, isIntB_smul v bL π.2 h1⟩

variable (π : v.adicCompletionIntegers ℚ) (hπ : Valued.v (π : v.adicCompletion ℚ) = exp (-1 : ℤ))
include hπ

theorem mem_pow_iff (x : lam v bL h1 hmul) (n : ℕ) :
    x ∈ (Ideal.span {unif v bL h1 hmul π}) ^ n • (⊤ : Submodule (lam v bL h1 hmul) (lam v bL h1 hmul)) ↔
      ∀ i, Valued.v ((Algebra.TensorProduct.basis (v.adicCompletion ℚ) bL).repr (x : v.adicCompletion ℚ ⊗[ℚ] L) i)
        ≤ exp (-(n : ℤ)) := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  have hc : ((unif v bL h1 hmul π ^ n : lam v bL h1 hmul) : v.adicCompletion ℚ ⊗[ℚ] L) =
      (π : v.adicCompletion ℚ) ^ n • (1 : v.adicCompletion ℚ ⊗[ℚ] L) := by
    rw [SubmonoidClass.coe_pow]
    show ((π : v.adicCompletion ℚ) • (1 : v.adicCompletion ℚ ⊗[ℚ] L)) ^ n = _
    rw [smul_pow, one_pow]
  have hv : Valued.v ((π : v.adicCompletion ℚ) ^ n) = exp (-(n : ℤ)) := by
    rw [map_pow, hπ, ← WithZero.exp_nsmul]; congr 1; simp
  constructor
  · rintro ⟨y, rfl⟩ i
    rw [Subring.coe_mul, hc, mul_smul_comm, mul_one, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, hv]
    exact mul_le_of_le_one_right' ((mem_adicCompletionIntegers _ _ _).1 (y.2 i))
  · intro hx
    have hπ0 : (π : v.adicCompletion ℚ) ^ n ≠ 0 := by
      intro h; rw [h, map_zero] at hv; exact exp_ne_zero hv.symm
    refine ⟨⟨((π : v.adicCompletion ℚ) ^ n)⁻¹ • (x : v.adicCompletion ℚ ⊗[ℚ] L), fun i => ?_⟩, Subtype.ext ?_⟩
    · rw [mem_adicCompletionIntegers, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, map_inv₀, hv]
      calc (exp (-(n : ℤ)))⁻¹ * Valued.v _ ≤ (exp (-(n : ℤ)))⁻¹ * exp (-(n : ℤ)) :=
            by gcongr; exact hx i
        _ = 1 := inv_mul_cancel₀ exp_ne_zero
    · rw [Subring.coe_mul, hc, mul_smul_comm, mul_one, smul_smul, mul_inv_cancel₀ hπ0, one_smul]

theorem small_iff (x : lam v bL h1 hmul) :
    IsSmallB v bL (x : v.adicCompletion ℚ ⊗[ℚ] L) ↔ x ∈ Ideal.span {unif v bL h1 hmul π} := by
  have := mem_pow_iff v bL h1 hmul π hπ x 1
  rw [pow_one, smul_eq_mul, Ideal.mul_top] at this
  rw [this]
  simp only [Nat.cast_one]
  exact forall_congr' fun i => Formalism.BasicNotions.Examples₂.wz_lt_one_iff _

theorem isAdicComplete :
    IsAdicComplete (Ideal.span {unif v bL h1 hmul π}) (lam v bL h1 hmul) := by
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex bL
  have key := mem_pow_iff v bL h1 hmul π hπ
  haveI hO := Formalism.BasicNotions.Examples₂.adicInt_isAdicComplete (K := ℚ) v
  set e := Algebra.TensorProduct.basis (v.adicCompletion ℚ) bL with he
  refine { toIsHausdorff := ⟨fun x hx => ?_⟩, toIsPrecomplete := ⟨fun f hf => ?_⟩ }
  · suffices h : (x : v.adicCompletion ℚ ⊗[ℚ] L) = 0 from Subtype.ext h
    apply e.repr.injective
    refine Finsupp.ext fun i => ?_
    rw [map_zero, Finsupp.zero_apply]
    refine Formalism.BasicNotions.Examples₂.adicInt_eq_zero_of_forall (K := ℚ) v _ fun n => ?_
    have := (key x n).1 (by simpa using (SModEq.sub_mem.1 (hx n)))
    exact this i
  · have hcoord : ∀ i, ∃ Li : v.adicCompletionIntegers ℚ, ∀ n,
        Valued.v (e.repr (f n : v.adicCompletion ℚ ⊗[ℚ] L) i - Li) ≤ exp (-(n : ℤ)) := by
      intro i
      obtain ⟨Li, hLi⟩ := IsPrecomplete.prec' (I := IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ))
        (fun n => (⟨e.repr (f n : v.adicCompletion ℚ ⊗[ℚ] L) i, (f n).2 i⟩ : v.adicCompletionIntegers ℚ))
        (fun {m n} hmn => by
          rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Formalism.BasicNotions.Examples₂.adicInt_mem_pow_iff]
          have := (key (f m - f n) m).1 (SModEq.sub_mem.1 (hf hmn)) i
          simpa [map_sub] using this)
      refine ⟨Li, fun n => ?_⟩
      have := SModEq.sub_mem.1 (hLi n)
      rw [smul_eq_mul, Ideal.mul_top, Formalism.BasicNotions.Examples₂.adicInt_mem_pow_iff] at this
      simpa using this
    choose Lc hLc using hcoord
    have hrep : ∀ (w : κ → v.adicCompletion ℚ) i, e.repr (e.equivFun.symm w) i = w i := fun w i => by
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    have hLmem : IsIntB v bL (e.equivFun.symm fun i => (Lc i : v.adicCompletion ℚ)) := fun i => by
      rw [hrep]; exact (Lc i).2
    refine ⟨⟨_, hLmem⟩, fun n => ?_⟩
    rw [SModEq.sub_mem, key]
    intro i
    have h := hLc i n
    rw [AddSubgroupClass.coe_sub, map_sub, Finsupp.sub_apply]
    rw [show (e.repr ((⟨_, hLmem⟩ : lam v bL h1 hmul) : v.adicCompletion ℚ ⊗[ℚ] L)) i = (Lc i : v.adicCompletion ℚ) from hrep _ i]
    simpa using h

end GlobalTheory.AdicSpan.HenselSqrt

namespace GlobalTheory.AdicSpan.HenselSqrt

open IsDedekindDomain.HeightOneSpectrum WithZero

theorem exists_sqrt : ∀ (v : HeightOneSpectrum ℤ) (L : Type) [Field L] [NumberField L] (κ : Type)
    (bL : Module.Basis κ ℚ L),
    Valued.v (2 : v.adicCompletion ℚ) = 1 → IsIntB v bL 1 →
    (∀ x y, IsIntB v bL x → IsIntB v bL y → IsIntB v bL (x * y)) →
    (∀ x y, IsIntB v bL x → IsSmallB v bL y → IsSmallB v bL (x * y)) →
    ∀ u : v.adicCompletion ℚ ⊗[ℚ] L, IsIntB v bL u → IsSmallB v bL (u - 1) →
    ∃ f : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, IsIntB v bL ↑f ∧ IsIntB v bL ↑f⁻¹ ∧
      (f : v.adicCompletion ℚ ⊗[ℚ] L) ^ 2 = u ∧
      IsSmallB v bL (↑f - 1) ∧
      ∀ g : v.adicCompletion ℚ ⊗[ℚ] L, IsIntB v bL g → g ^ 2 = u → IsSmallB v bL (g - 1) → g = ↑f := by
  intro v L _ _ κ bL h2 h1 hmul _ u hu hsu
  obtain ⟨π, hπ⟩ := Formalism.BasicNotions.Examples₂.adicInt_exists_unif (K := ℚ) v
  haveI := isAdicComplete v bL h1 hmul π hπ
  haveI : HenselianRing (lam v bL h1 hmul) (Ideal.span {unif v bL h1 hmul π}) :=
    IsAdicComplete.henselianRing _ _
  have hI := small_iff v bL h1 hmul π hπ
  have hjac : ∀ x ∈ Ideal.span {unif v bL h1 hmul π}, IsUnit (x + 1) := fun x hx => by
    simpa using Ring.mem_jacobson_iff.1 (HenselianRing.jac hx) 1

  have h20 : (2 : v.adicCompletion ℚ) ≠ 0 := fun h => by rw [h, map_zero] at h2; exact zero_ne_one h2
  have h2O : (2 : v.adicCompletion ℚ)⁻¹ ∈ v.adicCompletionIntegers ℚ := by
    rw [mem_adicCompletionIntegers, map_inv₀, h2, inv_one]
  let t : lam v bL h1 hmul := ⟨(2 : v.adicCompletion ℚ)⁻¹ • 1, isIntB_smul v bL h2O h1⟩
  have ht : (2 : lam v bL h1 hmul) * t = 1 := by
    apply Subtype.ext
    show (2 : v.adicCompletion ℚ ⊗[ℚ] L) * ((2 : v.adicCompletion ℚ)⁻¹ • 1) = 1
    rw [mul_smul_comm, mul_one,
      show (2 : v.adicCompletion ℚ ⊗[ℚ] L) = (2 : v.adicCompletion ℚ) • (1 : v.adicCompletion ℚ ⊗[ℚ] L) by
        rw [two_smul, one_add_one_eq_two],
      smul_smul, inv_mul_cancel₀ h20, one_smul]
  have h2u : IsUnit (2 : lam v bL h1 hmul) := ⟨⟨2, t, ht, by rw [mul_comm]; exact ht⟩, rfl⟩

  let u' : lam v bL h1 hmul := ⟨u, hu⟩
  obtain ⟨a, ha, haI⟩ := HenselianRing.is_henselian (I := Ideal.span {unif v bL h1 hmul π})
    (Polynomial.X ^ 2 - Polynomial.C u') (Polynomial.monic_X_pow_sub_C _ two_ne_zero) 1 (by
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C, one_pow,
        ← hI]
      have := isSmallB_neg v bL hsu
      rwa [neg_sub] at this) (by
      have : Polynomial.eval 1 (Polynomial.derivative (Polynomial.X ^ 2 - Polynomial.C u')) = 2 := by
        set_option synthInstance.maxHeartbeats 200000 in
          simp; try norm_num
      rw [this]; exact h2u.map _)
  have ha2 : a ^ 2 = u' := by
    have := ha.eq_zero
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at this
    exact sub_eq_zero.1 this
  have haU : IsUnit a := by
    have := hjac _ haI
    rwa [sub_add_cancel] at this
  refine ⟨Units.map (lam v bL h1 hmul).subtype.toMonoidHom haU.unit, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Units.coe_map, IsUnit.unit_spec]; exact a.2
  · rw [← map_inv]; simp only [Units.coe_map]; exact (haU.unit⁻¹ : (lam v bL h1 hmul)ˣ).1.2
  · simp only [Units.coe_map, IsUnit.unit_spec]
    exact congrArg Subtype.val ha2
  · simp only [Units.coe_map, IsUnit.unit_spec]
    exact (hI (a - 1)).2 haI
  · intro g hg hg2 hgs
    simp only [Units.coe_map, IsUnit.unit_spec]
    let g' : lam v bL h1 hmul := ⟨g, hg⟩
    have hgI : g' - 1 ∈ Ideal.span {unif v bL h1 hmul π} := (hI (g' - 1)).1 hgs
    have hg'2 : g' ^ 2 = u' := Subtype.ext hg2
    have h0 : (g' - a) * (g' + a) = 0 := by
      have : (g' - a) * (g' + a) = g' ^ 2 - a ^ 2 := by ring
      rw [this, hg'2, ha2, sub_self]
    have hx := hjac _ (Ideal.mul_mem_right t _ (add_mem hgI haI))
    have hsum : g' + a = 2 * (((g' - 1) + (a - 1)) * t + 1) := by
      linear_combination (-(g' + a - 2)) * ht
    have hU : IsUnit (g' + a) := by rw [hsum]; exact h2u.mul hx
    have := (hU.mul_left_eq_zero).1 h0
    exact congrArg Subtype.val (sub_eq_zero.1 this)

end GlobalTheory.AdicSpan.HenselSqrt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisHenselExistsUniqueSqrtStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicIntegralTensorBasis_hensel_exists_unique_sqrt : ∀ (v : HeightOneSpectrum ℤ) (L : Type) [Field L] [NumberField L] (κ : Type) (bL : Module.Basis κ ℚ L),
    Valued.v (2 : v.adicCompletion ℚ) = 1 → IsIntB v bL 1 →
    (∀ x y, IsIntB v bL x → IsIntB v bL y → IsIntB v bL (x * y)) →
    (∀ x y, IsIntB v bL x → IsSmallB v bL y → IsSmallB v bL (x * y)) →
    ∀ u : v.adicCompletion ℚ ⊗[ℚ] L, IsIntB v bL u → IsSmallB v bL (u - 1) →
    ∃ f : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, IsIntB v bL ↑f ∧ IsIntB v bL ↑f⁻¹ ∧ (f : v.adicCompletion ℚ ⊗[ℚ] L) ^ 2 = u ∧
      IsSmallB v bL (↑f - 1) ∧
      ∀ g : v.adicCompletion ℚ ⊗[ℚ] L, IsIntB v bL g → g ^ 2 = u → IsSmallB v bL (g - 1) → g = ↑f := by
  first | (exact @GlobalTheory.AdicSpan.HenselSqrt.exists_sqrt) | (exact GlobalTheory.AdicSpan.HenselSqrt.exists_sqrt) | (intros; apply GlobalTheory.AdicSpan.HenselSqrt.exists_sqrt  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedUnitEqNormAlmostAllPlaces
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
noncomputable section

namespace GlobalTheory.LocNorm

theorem good_eventually : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L) (κ : Type) (bL : Module.Basis κ ℚ L) (θ : L),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      Valued.v (2 : v.adicCompletion ℚ) = 1 ∧ IsIntB v bL 1 ∧
      (∀ x y, IsIntB v bL x → IsIntB v bL y → IsIntB v bL (x * y)) ∧
      (∀ x y, IsIntB v bL x → IsSmallB v bL y → IsSmallB v bL (x * y)) ∧
      (∀ x, IsIntB v bL x → IsIntB v bL (Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c x)) ∧
      (∀ x, IsSmallB v bL x → IsSmallB v bL (Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c x)) ∧
      IsIntB v bL ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] θ) ∧ IsIntB v bL ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] θ⁻¹) := by
  intro L _ _ c κ bL θ
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex bL
  have ev := fun (q : ℚ) => rat_mem_adicCompletionIntegers_eventually q
  have hc : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (bL.repr (bL t.1 * bL t.2.1) t.2.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ev _
  have hs : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (bL.repr (c (bL t.1)) t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ev _
  have hl : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : Fin 3 × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (bL.repr (![1, θ, θ⁻¹] t.1) t.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => ev _
  have hfin := Filter.eventually_cofinite.1 (((hc.and hs).and hl).and (ev (1 / 2)))
  refine ⟨hfin.toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  obtain ⟨⟨⟨hcv, hsv⟩, hlv⟩, h2v⟩ := hv
  have hmem : ∀ a : v.adicCompletion ℚ, a ∈ v.adicCompletionIntegers ℚ ↔ Valued.v a ≤ 1 := fun a =>
    HeightOneSpectrum.mem_adicCompletionIntegers ..
  have hint : ∀ ℓ : L, (∀ k, algebraMap ℚ (v.adicCompletion ℚ) (bL.repr ℓ k) ∈ v.adicCompletionIntegers ℚ) →
      IsIntB v bL ((1 : v.adicCompletion ℚ) ⊗ₜ[ℚ] ℓ) := by
    intro ℓ hℓ k
    rw [repr_tmul_apply, one_mul]; exact hℓ k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hint θ (fun k => hlv (1, k)), hint θ⁻¹ (fun k => hlv (2, k))⟩
  · have hle : Valued.v (2 : v.adicCompletion ℚ) ≤ 1 := by
      have h := (v.adicCompletionIntegers ℚ).add_mem 1 1 (one_mem _) (one_mem _)
      rw [one_add_one_eq_two] at h
      exact (hmem _).1 h
    have hle' : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (1 / 2)) ≤ 1 := (hmem _).1 h2v
    have hprod : Valued.v (2 : v.adicCompletion ℚ) * Valued.v (algebraMap ℚ (v.adicCompletion ℚ) (1 / 2)) = 1 := by
      rw [← map_mul, show (2 : v.adicCompletion ℚ) * algebraMap ℚ (v.adicCompletion ℚ) (1 / 2) = 1 by
        rw [show (2 : v.adicCompletion ℚ) = algebraMap ℚ _ 2 from (map_ofNat _ 2).symm, ← map_mul]; norm_num, map_one]
    refine le_antisymm hle ?_
    calc (1 : _) = _ := hprod.symm
      _ ≤ Valued.v (2 : v.adicCompletion ℚ) * 1 := mul_le_mul' le_rfl hle'
      _ = _ := mul_one _
  · rw [Algebra.TensorProduct.one_def]; exact hint 1 (fun k => hlv (0, k))
  · intro y z hy hz k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_tmul bL v y, eq_sum_tmul bL v z, Finset.sum_mul_sum, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply]
    exact mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))
  · intro y z hy hz k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_tmul bL v y, eq_sum_tmul bL v z, Finset.sum_mul_sum, map_sum, Finsupp.finsetSum_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finsupp.finsetSum_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun j _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply, map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_mul' (mul_le_mul' ((hmem _).1 (hy i)) le_rfl) ((hmem _).1 (hcv (i, j, k))))
      (by simpa using hz j)
  · intro y hy k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_tmul bL v y, map_sum, map_sum, Finsupp.finsetSum_apply]
    refine sum_mem fun i _ => ?_
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, repr_tmul_apply]
    exact mul_mem (hy i) (hsv (i, k))
  · intro y hy k
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_tmul bL v y, map_sum, map_sum, Finsupp.finsetSum_apply]
    refine Valuation.map_sum_lt _ one_ne_zero fun i _ => ?_
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, repr_tmul_apply, map_mul]
    exact lt_of_le_of_lt (mul_le_mul' le_rfl ((hmem _).1 (hsv (i, k)))) (by simpa using hy i)

theorem unit_fixed_is_norm : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) → (∃ x, c x ≠ x) →
    ∀ (κ : Type) (bL : Module.Basis κ ℚ L), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      ∀ e : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
        Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑e = ↑e → IsIntB v bL ↑e →
        IsIntB v bL ↑e⁻¹ → ∃ y : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
          (e : v.adicCompletion ℚ ⊗[ℚ] L) = ↑y * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑y := by
  intro L _ _ c hc hne κ bL
  obtain ⟨x, hx⟩ := hne
  set θ : L := x - c x with hθdef
  have hθ : θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hcθ : c θ = -θ := by simp [θ, hc]
  obtain ⟨S, hS⟩ := good_eventually L c κ bL θ
  refine ⟨S, fun v hv e hee hei hei' => ?_⟩
  obtain ⟨h2, h1, hmul, hmulS, hσI, hσS, hθI, hθI'⟩ := hS v hv
  set σ := Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c with hσdef
  have hσσ : ∀ a, σ (σ a) = a := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul r l => simp [σ, hc]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have hσinv : ∀ g : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ, σ ↑g = ↑g → σ ↑g⁻¹ = ↑g⁻¹ := by
    intro g hg
    calc σ ↑g⁻¹ = σ ↑g⁻¹ * (↑g * ↑g⁻¹) := by simp
      _ = σ (↑g⁻¹ * ↑g) * ↑g⁻¹ := by rw [map_mul, hg]; ring
      _ = ↑g⁻¹ := by simp
  let θu : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ :=
    ⟨1 ⊗ₜ θ, 1 ⊗ₜ θ⁻¹,
      by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_inv_cancel₀ hθ, Algebra.TensorProduct.one_def],
      by rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, inv_mul_cancel₀ hθ, Algebra.TensorProduct.one_def]⟩
  have hσθ : σ ↑θu = -↑θu := by simp [θu, σ, hcθ, TensorProduct.tmul_neg]
  obtain ⟨z, hzI, hzS⟩ := GlobalTheory.T.exists_twistedNorm_mod_maxIdeal_adicTensor v L c hc κ bL h2 h1 hmul hmulS hσI θu hθI hθI' hσθ e hee hei hei'
  set w := z * σ z with hwdef
  have hwσ : σ w = w := by simp only [w, map_mul, hσσ]; ring
  set u : v.adicCompletion ℚ ⊗[ℚ] L := ↑e⁻¹ * w with hudef
  have huI : IsIntB v bL u := hmul _ _ hei' (hmul _ _ hzI (hσI _ hzI))
  have huS : IsSmallB v bL (u - 1) := by
    have : u - 1 = ↑e⁻¹ * (w - ↑e) := by simp [u, mul_sub]
    rw [this]; exact hmulS _ _ hei' hzS
  obtain ⟨f, hfI, hfI', hf2, hfS, huniq⟩ := GlobalTheory.T.adicIntegralTensorBasis_hensel_exists_unique_sqrt v L κ bL h2 h1 hmul hmulS u huI huS
  have hσu : σ u = u := by simp only [u, map_mul, hσinv e hee, hwσ]
  have hσf : σ ↑f = ↑f := by
    refine huniq _ (hσI _ hfI) (by rw [← map_pow, hf2, hσu]) ?_
    have := hσS _ hfS
    simpa using this
  have hw : w = ↑e * ↑f ^ 2 := by rw [hf2]; simp [u]
  have hzU : IsUnit z := isUnit_of_mul_isUnit_left (x := z) (y := σ z)
    (by rw [← hwdef, hw]; exact e.isUnit.mul (f.isUnit.pow 2))
  obtain ⟨zu, hzu⟩ := hzU
  refine ⟨zu * f⁻¹, ?_⟩
  have hf' := hσinv f hσf
  simp only [Units.val_mul, map_mul, hf', hzu]
  have : (↑e : v.adicCompletion ℚ ⊗[ℚ] L) = w * ↑f⁻¹ * ↑f⁻¹ := by
    rw [hw]; simp [pow_two, mul_assoc]
  rw [this, hwdef]; ring

end GlobalTheory.LocNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedUnitEqNormAlmostAllPlacesStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_unit_eq_norm_almost_all_places : ∀ (L : Type) [Field L] [NumberField L] (c : L →ₐ[ℚ] L), (∀ x, c (c x) = x) → (∃ x, c x ≠ x) →
    ∀ (κ : Type) (bL : Module.Basis κ ℚ L), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      ∀ e : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
        Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑e = ↑e → IsIntB v bL ↑e →
        IsIntB v bL ↑e⁻¹ → ∃ y : (v.adicCompletion ℚ ⊗[ℚ] L)ˣ,
          (e : v.adicCompletion ℚ ⊗[ℚ] L) = ↑y * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) c ↑y := by
  first | (exact @GlobalTheory.LocNorm.unit_fixed_is_norm) | (exact GlobalTheory.LocNorm.unit_fixed_is_norm) | (intros; apply GlobalTheory.LocNorm.unit_fixed_is_norm  <;> assumption)
end
