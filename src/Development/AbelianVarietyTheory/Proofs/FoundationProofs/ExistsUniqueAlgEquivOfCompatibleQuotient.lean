module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueAlgEquivOfCompatibleQuotient
noncomputable section

namespace GlobalTheory

open TensorProduct

theorem isPrecomplete_of_finite {R : Type*} [CommRing R] (I : Ideal R) [IsAdicComplete I R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨t, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction t with
  | tmul a m =>
    obtain ⟨r, rfl⟩ := AdicCompletion.of_surjective I R a
    refine ⟨r • m, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, show AdicCompletion.of I R r =
      algebraMap R (AdicCompletion I R) r by simp [AdicCompletion.algebraMap_apply],
      algebraMap_smul, map_smul]
  | add x y hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by simp [hu, hv]⟩

theorem isAdicComplete_of_finite {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    IsAdicComplete I M := by
  rw [isAdicComplete_iff]
  exact ⟨IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson I), isPrecomplete_of_finite I M⟩

theorem isAdicComplete_map_of_finite {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    [IsAdicComplete I R] (S : Type*) [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsAdicComplete (I.map (algebraMap R S)) S := by
  rw [IsAdicComplete.map_algebraMap_iff]
  exact isAdicComplete_of_finite I S

section Tower

variable {R : Type*} [CommRing R] (I : Ideal R)

end Tower

section Quotient

variable {R : Type*} [CommRing R] (I : Ideal R)

variable [IsNoetherianRing R] [IsAdicComplete I R] {A B : Type*} [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]

end Quotient

section Tensor

variable {R : Type*} [CommRing R] (I : Ideal R)

variable [IsNoetherianRing R] [IsAdicComplete I R]

section

variable {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]

end

section

variable {A B : Type*} [Ring A] [Ring B] [Bialgebra R A] [Bialgebra R B]

end

end Tensor

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
noncomputable section

open Classical
open scoped BigOperators

namespace GlobalTheory.FinWeil

variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]

structure IsHeis (σ : R →+* R) (w : R) (γ : X → X → ℂ) (W : X → M →ₗ[ℂ] M) : Prop where
  sg_sg : ∀ r, σ (σ r) = r
  w_add : w + σ w = 1
  add_left : ∀ x y z, γ (x + y) z = γ x z * γ y z
  add_right : ∀ x y z, γ x (y + z) = γ x y * γ x z
  alt : ∀ x, γ x x = 1
  adj : ∀ r x y, γ (r • x) y = γ x (σ r • y)
  zero : ∀ v, W 0 v = v
  comp : ∀ x y v, W x (W y v) = γ (w • x) y • W (x + y) v

def SelfDual (γ : X → X → ℂ) (A : Submodule R X) : Prop := ∀ x, x ∈ A ↔ ∀ a ∈ A, γ x a = 1

def Fixes (W : X → M →ₗ[ℂ] M) (A : Submodule R X) (v : M) : Prop := ∀ a ∈ A, W a v = v

def idx (A B : Submodule R X) : ℕ := A.toAddSubgroup.relIndex B.toAddSubgroup

def sumOp (W : X → M →ₗ[ℂ] M) (A B : Submodule R X) (v : M) : M :=
  ∑ᶠ q : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup, W ((Quotient.out q : B.toAddSubgroup) : X) v

def normOp (lam : ℕ →* ℂ) (W : X → M →ₗ[ℂ] M) (A B : Submodule R X) (v : M) : M :=
  (lam (idx A B))⁻¹ • sumOp W A B v

def GoodNorm (σ : R →+* R) (lam : ℕ →* ℂ) : Prop :=
  (∀ n, n ≠ 0 → lam n ≠ 0) ∧ ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) →
    lam (Nat.card (R ⧸ P)) ^ 2 = (Nat.card (R ⧸ P) : ℂ) ∧
    ((∀ r ∈ P, σ r ∈ P) → lam (Nat.card (R ⧸ P)) = -(Real.sqrt (Nat.card (R ⧸ P)) : ℂ) ∧ ∃ r, σ r - r ∉ P)

def Adj (A B : Submodule R X) : Prop :=
  ∃ x ∈ B, ∃ P : Ideal R, P.IsMaximal ∧ Finite (R ⧸ P) ∧ (∀ r : R, r • x ∈ A ↔ r ∈ P) ∧ B ≤ (A ⊓ B) ⊔ Submodule.span R {x}

namespace IsHeis

variable {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M} (h : IsHeis σ w γ W)
include h

theorem skew (x y : X) : γ x y * γ y x = 1 := by
  have h1 := h.alt (x + y)
  rw [h.add_left, h.add_right, h.add_right, h.alt, h.alt] at h1
  simpa using h1

theorem ne_zero (x y : X) : γ x y ≠ 0 := left_ne_zero_of_mul_eq_one (h.skew x y)

theorem zero_left (y : X) : γ 0 y = 1 := by
  have h1 := h.add_left 0 0 y
  rw [add_zero] at h1
  exact (mul_eq_left₀ (h.ne_zero 0 y)).1 h1.symm

theorem zero_right (x : X) : γ x 0 = 1 := by
  have h1 := h.add_right x 0 0
  rw [add_zero] at h1
  exact (mul_eq_left₀ (h.ne_zero x 0)).1 h1.symm

theorem neg_left (x y : X) : γ (-x) y = (γ x y)⁻¹ := by
  have h1 := h.add_left (-x) x y
  rw [neg_add_cancel, h.zero_left] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem neg_right (x y : X) : γ x (-y) = (γ x y)⁻¹ := by
  have h1 := h.add_right x (-y) y
  rw [neg_add_cancel, h.zero_right] at h1
  exact eq_inv_of_mul_eq_one_left h1.symm

theorem swap (x y : X) : γ y x = (γ x y)⁻¹ := eq_inv_of_mul_eq_one_right (h.skew x y)

theorem swap_eq_one {x y : X} (hxy : γ x y = 1) : γ y x = 1 := by rw [h.swap, hxy, inv_one]

theorem nsmul_left (n : ℕ) (x y : X) : γ (n • x) y = γ x y ^ n := by
  induction n with
  | zero => simp [h.zero_left]
  | succ n ih => rw [succ_nsmul, h.add_left, ih, pow_succ]

theorem nsmul_right (n : ℕ) (x y : X) : γ x (n • y) = γ x y ^ n := by
  induction n with
  | zero => simp [h.zero_right]
  | succ n ih => rw [succ_nsmul, h.add_right, ih, pow_succ]

theorem comm (x y : X) (v : M) : W x (W y v) = γ x y • W y (W x v) := by
  have h1 : γ (w • x) y = γ x y * γ (w • y) x := by
    have h2 : γ x y = γ (w • x) y * γ (σ w • x) y := by rw [← h.add_left, ← add_smul, h.w_add, one_smul]
    rw [h2, h.adj (σ w), h.sg_sg, mul_assoc, h.skew, mul_one]
  rw [h.comp, h.comp, smul_smul, h1, add_comm]

theorem iso {A : Submodule R X} (hA : SelfDual γ A) {x y : X} (hx : x ∈ A) (hy : y ∈ A) : γ x y = 1 := (hA x).1 hx y hy

theorem comp_of_mem {A : Submodule R X} (hA : SelfDual γ A) {x y : X} (hx : x ∈ A) (hy : y ∈ A) (v : M) :
    W x (W y v) = W (x + y) v := by
  rw [h.comp, h.iso hA (A.smul_mem w hx) hy, one_smul]

theorem neg_comp (x : X) (v : M) : W (-x) (W x v) = γ (w • -x) x • v := by
  rw [h.comp, neg_add_cancel, h.zero]

end IsHeis

end GlobalTheory.FinWeil
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCard
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BijectiveDualAddChar
namespace GlobalTheory.StandardAdditiveCharacter

theorem exists_stdAddChar_eq (n : ℕ) [NeZero n] (z : ℂ) (hz : z ^ n = 1) :
    ∃ j : ZMod n, ZMod.stdAddChar j = z := by
  obtain ⟨i, -, hi⟩ := (Complex.isPrimitiveRoot_exp n (NeZero.ne n)).eq_pow_of_pow_eq_one hz
  refine ⟨((i : ℤ) : ZMod n), ?_⟩
  rw [ZMod.stdAddChar_coe, ← hi, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem bijective_dual_addChar (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A]
    [Module (ZMod n) A] :
    Function.Bijective fun (φ : Module.Dual (ZMod n) A) ↦
      AddChar.compAddMonoidHom ZMod.stdAddChar (LinearMap.toAddMonoidHom φ) := by
  constructor
  · intro φ ψ h
    apply LinearMap.ext
    intro a
    have h' := congr_arg (fun χ : AddChar A ℂ => χ a) h
    simp only [AddChar.compAddMonoidHom_apply, LinearMap.toAddMonoidHom_coe] at h'
    exact ZMod.injective_stdAddChar h'
  · intro ψ
    have hroot : ∀ a : A, (ψ a) ^ n = 1 := by
      intro a
      rw [← AddChar.map_nsmul_eq_pow]
      have h0 : n • a = 0 := by
        rw [← Nat.cast_smul_eq_nsmul (ZMod n), ZMod.natCast_self, zero_smul]
      rw [h0, AddChar.map_zero_eq_one]
    choose j hj using fun a => exists_stdAddChar_eq n (ψ a) (hroot a)
    let F : A →+ ZMod n :=
      { toFun := j
        map_zero' := ZMod.injective_stdAddChar (by simp [hj])
        map_add' := fun a b => ZMod.injective_stdAddChar (by simp only [AddChar.map_add_eq_mul, hj]) }
    refine ⟨F.toZModLinearMap n, ?_⟩
    ext a
    simp [F, hj]

end GlobalTheory.StandardAdditiveCharacter
end

namespace GlobalTheory.ZModDual

theorem stdAddChar_comp_bijective (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A]
    [Module (ZMod n) A] :
    Function.Bijective fun φ : Module.Dual (ZMod n) A =>
      ((ZMod.stdAddChar (N := n)).compAddMonoidHom φ.toAddMonoidHom : AddChar A ℂ) := by
  apply _root_.GlobalTheory.StandardAdditiveCharacter.bijective_dual_addChar <;> assumption

theorem card_dual_eq (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A] [Module (ZMod n) A]
    [Finite A] : Nat.card (Module.Dual (ZMod n) A) = Nat.card A := by
  classical
  have := Fintype.ofFinite A
  rw [Nat.card_eq_of_bijective _ (stdAddChar_comp_bijective n A),
    Nat.card_eq_fintype_card (α := AddChar A ℂ), AddChar.card_eq, ← Nat.card_eq_fintype_card]

end GlobalTheory.ZModDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormPrimeIffInertiaDegEqOneAndFiniteRamified
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem _root_.GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified :
    ∀ (E : Type) [Field E] [NumberField E],
      (∀ P : HeightOneSpectrum (𝓞 E),
        (Ideal.absNorm P.asIdeal).Prime ↔ P.asIdeal.inertiaDeg ℤ = 1) ∧
      {P : HeightOneSpectrum (𝓞 E) | P.asIdeal.ramificationIdx ℤ ≠ 1}.Finite := by
  intro E _ _
  have key : ∀ P : HeightOneSpectrum (𝓞 E), (Ideal.absNorm (P.asIdeal.under ℤ)).Prime ∧
      Ideal.absNorm P.asIdeal = Ideal.absNorm (P.asIdeal.under ℤ) ^ P.asIdeal.inertiaDeg ℤ := by
    intro P
    haveI : NeZero P.asIdeal := ⟨P.ne_bot⟩
    exact ⟨Nat.absNorm_under_prime P.asIdeal,
      (Ideal.absNorm_pow_inertiaDeg (P.asIdeal.under ℤ) P.asIdeal).symm⟩
  refine ⟨fun P => ?_, ?_⟩
  · obtain ⟨hq, hN⟩ := key P
    rw [hN]
    constructor
    · intro hpow
      have hf0 : P.asIdeal.inertiaDeg ℤ ≠ 0 := by
        intro h0
        rw [h0, pow_zero] at hpow
        exact Nat.not_prime_one hpow
      rcases hpow.eq_one_or_self_of_dvd _ (dvd_pow_self _ hf0) with h1 | h1
      · exact absurd h1 hq.one_lt.ne'
      · exact Nat.pow_right_injective hq.two_le (by simpa using h1.symm)
    · intro h1
      rw [h1, pow_one]
      exact hq
  · set d := (discr E).natAbs with hd_def
    have hd : 0 < d := Int.natAbs_pos.mpr (discr_ne_zero E)
    refine ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 E) (d ^ Module.finrank ℤ (𝓞 E))).preimage
      (fun P _ Q _ h => HeightOneSpectrum.ext h)).subset ?_
    intro P hP
    simp only [Set.mem_setOf_eq, Set.mem_preimage] at hP ⊢
    obtain ⟨hq, -⟩ := key P
    set q := Ideal.absNorm (P.asIdeal.under ℤ) with hq_def
    have hmem := Int.absNorm_under_mem P.asIdeal
    rw [← hq_def] at hmem
    have hqZ : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
    have hqd : (q : ℤ) ∣ discr E := by
      by_contra hnd
      have hun := (not_dvd_discr_iff_isUnramifiedIn E (𝓞 E) hqZ).mp hnd
      have hlies : P.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) :=
        (Ideal.liesOver_span_iff P.isPrime.ne_top hqZ).mpr (by simpa using hmem)
      exact hP (hun.ramificationIdx_eq_one hlies)
    have hqle : q ≤ d := Nat.le_of_dvd hd (by simpa using Int.natAbs_dvd_natAbs.mpr hqd)
    have hdvd : Ideal.absNorm P.asIdeal ∣ q ^ Module.finrank ℤ (𝓞 E) := by
      have hle : Ideal.span {((q : ℤ) : 𝓞 E)} ≤ P.asIdeal := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        simpa using hmem
      have hnorm : Algebra.norm ℤ ((q : ℤ) : 𝓞 E) = (q : ℤ) ^ Module.finrank ℤ (𝓞 E) := by
        rw [← eq_intCast (algebraMap ℤ (𝓞 E)), Algebra.norm_algebraMap]
      have h := Ideal.absNorm_dvd_absNorm_of_le hle
      rw [Ideal.absNorm_span_singleton, hnorm, Int.natAbs_pow, Int.natAbs_natCast] at h
      exact h
    calc Ideal.absNorm P.asIdeal ≤ q ^ Module.finrank ℤ (𝓞 E) :=
          Nat.le_of_dvd (pow_pos hq.pos _) hdvd
      _ ≤ d ^ Module.finrank ℤ (𝓞 E) := Nat.pow_le_pow_left hqle _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
noncomputable section

open UpperHalfPlane Filter
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

def IsMF (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ) : Prop :=
  (∀ γ ∈ Γ, f ∣[k] γ = f) ∧ MDiff f ∧ ∀ x : SL(2, ℤ), IsBoundedAtImInfty (f ∣[k] x)

def IsCF (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f : ℍ → ℂ) : Prop :=
  (∀ γ ∈ Γ, f ∣[k] γ = f) ∧ MDiff f ∧ ∀ x : SL(2, ℤ), IsZeroAtImInfty (f ∣[k] x)

def IsReps (Γ : Subgroup SL(2, ℤ)) {r : ℕ} (s : Fin r → SL(2, ℤ)) : Prop :=
  (∀ x : SL(2, ℤ), ∃ i, ∃ γ ∈ Γ, x = γ * s i ∨ x = -(γ * s i)) ∧
    ∀ i j, ∀ γ ∈ Γ, (s i = γ * s j ∨ s i = -(γ * s j)) → i = j

def evM {r : ℕ} (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) (τ : ℍ) :
    Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j => (F j ∣[w j] s i) τ

def co (M : ℕ) (k : ℤ) (f : ℍ → ℂ) (x : SL(2, ℤ)) (n : ℕ) : ℂ :=
  (qExpansion (M : ℝ) (f ∣[k] x)).coeff n

def leadM (M : ℕ) {r : ℕ} (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) :
    Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun i j => ∑ n ∈ Finset.range M, co M (w j) (F j) (s i) n

def Reduces (Γ : Subgroup SL(2, ℤ)) {r : ℕ} (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ) : Prop :=
  ∃ (j₀ : Fin r) (w' : ℤ) (G E : ℍ → ℂ) (e : Fin r → ℍ → ℂ), w' < w j₀ ∧ Odd w' ∧ IsMF Γ w' G ∧
    (∀ j, MDiff (e j)) ∧ e j₀ ≠ 0 ∧
    ∀ (x : SL(2, ℤ)) (τ : ℍ), E τ * (G ∣[w'] x) τ = ∑ j, e j τ * (F j ∣[w j] x) τ

theorem mdiff_slash {f : ℍ → ℂ} (hf : MDiff f) (k : ℤ) (x : SL(2, ℤ)) : MDiff (f ∣[k] x) := by
  rw [ModularForm.SL_slash]
  exact hf.slash k _

theorem slash_neg (k : ℤ) (f : ℍ → ℂ) (x : SL(2, ℤ)) : f ∣[k] (-x) = ((-1 : ℂ) ^ k) • f ∣[k] x := by
  ext τ
  simp only [Pi.smul_apply, ModularForm.SL_slash_apply, smul_eq_mul, ModularGroup.SL_neg_smul]
  have hd : denom ((-x : SL(2, ℤ)) : GL (Fin 2) ℝ) τ = -denom (x : GL (Fin 2) ℝ) τ := by
    simp [denom]
    ring
  rw [hd]
  rcases Int.even_or_odd k with hk | hk
  · rw [hk.neg_one_zpow, hk.neg.neg_zpow]; ring
  · rw [hk.neg_one_zpow, hk.neg.neg_zpow]; ring

theorem slash_neg_of_odd {k : ℤ} (hk : Odd k) (f : ℍ → ℂ) (x : SL(2, ℤ)) : f ∣[k] (-x) = -(f ∣[k] x) := by
  rw [slash_neg, hk.neg_one_zpow, neg_one_smul]

theorem slash_neg_of_even {k : ℤ} (hk : Even k) (f : ℍ → ℂ) (x : SL(2, ℤ)) : f ∣[k] (-x) = f ∣[k] x := by
  rw [slash_neg, hk.neg_one_zpow, one_smul]

theorem slash_mul_apply (k : ℤ) (f : ℍ → ℂ) (x y : SL(2, ℤ)) (τ : ℍ) :
    (f ∣[k] (x * y)) τ = (f ∣[k] x) (y • τ) * denom (y : GL (Fin 2) ℝ) τ ^ (-k) := by
  rw [SlashAction.slash_mul, ModularForm.SL_slash_apply]

theorem IsCF.isMF {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f : ℍ → ℂ} (h : IsCF Γ k f) : IsMF Γ k f := ⟨h.1, h.2.1, fun x => (h.2.2 x).boundedAtFilter⟩

theorem IsMF.slash_mul {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f : ℍ → ℂ} (h : IsMF Γ k f) {γ : SL(2, ℤ)}
    (hγ : γ ∈ Γ) (x : SL(2, ℤ)) : f ∣[k] (γ * x) = f ∣[k] x := by
  rw [SlashAction.slash_mul, h.1 γ hγ]

theorem IsMF.slash_top {k : ℤ} {f : ℍ → ℂ} (h : IsMF ⊤ k f) (x : SL(2, ℤ)) : f ∣[k] x = f := h.1 x (Subgroup.mem_top x)

theorem IsMF.mono {Γ Γ' : Subgroup SL(2, ℤ)} {k : ℤ} {f : ℍ → ℂ} (h : IsMF Γ k f) (hle : Γ' ≤ Γ) :
    IsMF Γ' k f := ⟨fun γ hγ => h.1 γ (hle hγ), h.2.1, h.2.2⟩

theorem IsMF.zero (Γ : Subgroup SL(2, ℤ)) (k : ℤ) : IsMF Γ k 0 := by
  refine ⟨fun γ _ => SlashAction.zero_slash _ _, mdifferentiable_const, fun x => ?_⟩
  rw [SlashAction.zero_slash]
  exact zero_form_isBoundedAtImInfty

theorem IsMF.add {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f g : ℍ → ℂ} (hf : IsMF Γ k f) (hg : IsMF Γ k g) :
    IsMF Γ k (f + g) := by
  refine ⟨fun γ hγ => ?_, hf.2.1.add hg.2.1, fun x => ?_⟩
  · rw [SlashAction.add_slash, hf.1 γ hγ, hg.1 γ hγ]
  · rw [SlashAction.add_slash]
    exact (hf.2.2 x).add (hg.2.2 x)

theorem IsMF.smul {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f : ℍ → ℂ} (hf : IsMF Γ k f) (c : ℂ) :
    IsMF Γ k (c • f) := by
  refine ⟨fun γ hγ => ?_, hf.2.1.const_smul c, fun x => ?_⟩
  · rw [ModularForm.SL_smul_slash, hf.1 γ hγ]
  · rw [ModularForm.SL_smul_slash]
    exact (hf.2.2 x).smul c

theorem IsMF.neg {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f : ℍ → ℂ} (hf : IsMF Γ k f) : IsMF Γ k (-f) := by
  have h := hf.smul (-1)
  rwa [neg_one_smul] at h

theorem IsMF.sub {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f g : ℍ → ℂ} (hf : IsMF Γ k f) (hg : IsMF Γ k g) :
    IsMF Γ k (f - g) := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem IsMF.sum {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {ι : Type*} (t : Finset ι) {f : ι → ℍ → ℂ}
    (hf : ∀ i ∈ t, IsMF Γ k (f i)) : IsMF Γ k (∑ i ∈ t, f i) := Finset.sum_induction _ (IsMF Γ k) (fun _ _ ha hb => ha.add hb) (IsMF.zero Γ k) hf

theorem IsMF.mul {Γ : Subgroup SL(2, ℤ)} {k l m : ℤ} {f g : ℍ → ℂ} (hf : IsMF Γ k f) (hg : IsMF Γ l g)
    (hm : m = k + l) : IsMF Γ m (f * g) := by
  subst hm
  refine ⟨fun γ hγ => ?_, hf.2.1.mul hg.2.1, fun x => ?_⟩
  · rw [ModularForm.mul_slash_SL2, hf.1 γ hγ, hg.1 γ hγ]
  · rw [ModularForm.mul_slash_SL2]
    exact (hf.2.2 x).mul (hg.2.2 x)

theorem IsMF.mul_isCF {Γ : Subgroup SL(2, ℤ)} {k l m : ℤ} {f g : ℍ → ℂ} (hf : IsMF Γ k f) (hg : IsCF Γ l g)
    (hm : m = k + l) : IsCF Γ m (f * g) := by
  subst hm
  refine ⟨fun γ hγ => ?_, hf.2.1.mul hg.2.1, fun x => ?_⟩
  · rw [ModularForm.mul_slash_SL2, hf.1 γ hγ, hg.1 γ hγ]
  · rw [ModularForm.mul_slash_SL2]
    exact (hf.2.2 x).mul_zeroAtFilter (hg.2.2 x)

theorem IsMF.one (Γ : Subgroup SL(2, ℤ)) : IsMF Γ 0 1 := by
  refine ⟨fun γ _ => ModularForm.is_invariant_one γ, mdifferentiable_const, fun x => ?_⟩
  rw [ModularForm.is_invariant_one]
  exact Filter.const_boundedAtFilter _ (1 : ℂ)

theorem IsMF.pow {Γ : Subgroup SL(2, ℤ)} {k : ℤ} {f : ℍ → ℂ} (hf : IsMF Γ k f) (n : ℕ) :
    IsMF Γ (n * k) (f ^ n) := by
  induction n with
  | zero => simpa using IsMF.one Γ
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul hf (by push_cast; ring)

theorem isMF_coe {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} (f : ModularForm Γ k) : IsMF Γ k f := ⟨fun γ hγ => SlashInvariantFormClass.slash_action_eq f _ ⟨γ, hγ, rfl⟩, ModularFormClass.holo f,
    fun x => ModularFormClass.bdd_at_infty_slash f x⟩

theorem isMF_coe_top {k : ℤ} (f : ModularForm 𝒮ℒ k) : IsMF ⊤ k f := ⟨fun γ _ => SlashInvariantFormClass.slash_action_eq f _ ⟨γ, rfl⟩, ModularFormClass.holo f,
    fun x => ModularFormClass.bdd_at_infty_slash f x⟩

theorem isCF_coe_top {k : ℤ} (f : CuspForm 𝒮ℒ k) : IsCF ⊤ k f := ⟨fun γ _ => SlashInvariantFormClass.slash_action_eq f _ ⟨γ, rfl⟩, ModularFormClass.holo f,
    fun x => CuspFormClass.zero_at_infty_slash f x⟩

def IsMF.toMF {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {f : ℍ → ℂ} (h : IsMF Γ k f) :
    ModularForm Γ k where
  toFun := f
  slash_action_eq' := by rintro _ ⟨γ, hγ, rfl⟩; exact h.1 γ hγ
  holo' := h.2.1
  bdd_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
    exact fun γ _ => h.2.2 γ

@[simp] theorem IsMF.coe_toMF {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {f : ℍ → ℂ} (h : IsMF Γ k f) :
    ⇑h.toMF = f := rfl

def IsCF.toCF {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {f : ℍ → ℂ} (h : IsCF Γ k f) :
    CuspForm Γ k where
  toFun := f
  slash_action_eq' := by rintro _ ⟨γ, hγ, rfl⟩; exact h.1 γ hγ
  holo' := h.2.1
  zero_at_cusps' {c} hc := by
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hc]
    exact fun γ _ => h.2.2 γ

@[simp] theorem IsCF.coe_toCF {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {f : ℍ → ℂ} (h : IsCF Γ k f) :
    ⇑h.toCF = f := rfl

theorem finiteIndex_of_Gamma_le {M : ℕ} {Γ : Subgroup SL(2, ℤ)} (hM : 0 < M)
    (h : CongruenceSubgroup.Gamma M ≤ Γ) : Γ.FiniteIndex := by
  have : NeZero M := ⟨hM.ne'⟩
  exact Subgroup.finiteIndex_of_le h

theorem IsMF.eq_zero_of_neg {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ} {f : ℍ → ℂ} (h : IsMF Γ k f)
    (hk : k < 0) : f = 0 := by
  have h0 := ModularForm.isZero_of_neg_weight hk h.toMF
  rw [← h.coe_toMF, h0]
  rfl

private theorem exists_finite_residue_reps_mod_natCast {Γ : Subgroup SL(2, ℤ)} {x z y : SL(2, ℤ)}
    (h : ∃ γ ∈ Γ, x = γ * z ∨ x = -(γ * z)) : ∃ γ ∈ Γ, x * y = γ * (z * y) ∨ x * y = -(γ * (z * y)) := by
  obtain ⟨γ, hγ, h | h⟩ := h
  · exact ⟨γ, hγ, Or.inl (by rw [h, mul_assoc])⟩
  · exact ⟨γ, hγ, Or.inr (by rw [h, neg_mul, mul_assoc])⟩

private theorem exists_mem_mul_or_neg_mul_symm {Γ : Subgroup SL(2, ℤ)} {x z : SL(2, ℤ)}
    (h : ∃ γ ∈ Γ, x = γ * z ∨ x = -(γ * z)) : ∃ γ ∈ Γ, z = γ * x ∨ z = -(γ * x) := by
  obtain ⟨γ, hγ, h | h⟩ := h
  · exact ⟨γ⁻¹, Γ.inv_mem hγ, Or.inl (by rw [h, ← mul_assoc, inv_mul_cancel, one_mul])⟩
  · exact ⟨γ⁻¹, Γ.inv_mem hγ, Or.inr (by rw [h, mul_neg, ← mul_assoc, inv_mul_cancel, one_mul, neg_neg])⟩

private theorem exists_mem_mul_or_neg_mul_trans {Γ : Subgroup SL(2, ℤ)} {x z u : SL(2, ℤ)}
    (h₁ : ∃ γ ∈ Γ, x = γ * z ∨ x = -(γ * z)) (h₂ : ∃ γ ∈ Γ, z = γ * u ∨ z = -(γ * u)) :
    ∃ γ ∈ Γ, x = γ * u ∨ x = -(γ * u) := by
  obtain ⟨γ, hγ, h | h⟩ := h₁ <;> obtain ⟨δ, hδ, h' | h'⟩ := h₂
  · exact ⟨γ * δ, Γ.mul_mem hγ hδ, Or.inl (by rw [h, h', mul_assoc])⟩
  · exact ⟨γ * δ, Γ.mul_mem hγ hδ, Or.inr (by rw [h, h', mul_neg, mul_assoc])⟩
  · exact ⟨γ * δ, Γ.mul_mem hγ hδ, Or.inr (by rw [h, h', mul_assoc])⟩
  · exact ⟨γ * δ, Γ.mul_mem hγ hδ, Or.inl (by rw [h, h', mul_neg, neg_neg, mul_assoc])⟩

theorem IsReps.exists_perm {Γ : Subgroup SL(2, ℤ)} {r : ℕ} {s : Fin r → SL(2, ℤ)} (hs : IsReps Γ s)
    (y : SL(2, ℤ)) : ∃ π : Equiv.Perm (Fin r), ∀ i, ∃ γ ∈ Γ, s i * y = γ * s (π i) ∨ s i * y = -(γ * s (π i)) := by
  choose π γ hγ hπ using fun i => hs.1 (s i * y)
  have hinj : Function.Injective π := by
    intro i i' he
    have h1 : ∃ g ∈ Γ, s i * y = g * s (π i) ∨ s i * y = -(g * s (π i)) := ⟨γ i, hγ i, hπ i⟩
    have h2 : ∃ g ∈ Γ, s i' * y = g * s (π i) ∨ s i' * y = -(g * s (π i)) := by
      rw [he]; exact ⟨γ i', hγ i', hπ i'⟩
    obtain ⟨g, hg, h⟩ := exists_finite_residue_reps_mod_natCast (y := y⁻¹) (exists_mem_mul_or_neg_mul_trans h1 (exists_mem_mul_or_neg_mul_symm h2))
    simp only [mul_inv_cancel_right] at h
    exact hs.2 i i' g hg h
  exact ⟨Equiv.ofBijective π (Finite.injective_iff_bijective.mp hinj), fun i => ⟨γ i, hγ i, hπ i⟩⟩

theorem IsReps.sum_eq_zero {Γ : Subgroup SL(2, ℤ)} {r : ℕ} {s : Fin r → SL(2, ℤ)} (hs : IsReps Γ s)
    {ι : Type*} [Fintype ι] {w : ι → ℤ} {F : ι → ℍ → ℂ} (hF : ∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j))
    (c : ι → ℂ) (τ : ℍ) (h : ∀ i, ∑ j, c j * (F j ∣[w j] s i) τ = 0) (x : SL(2, ℤ)) :
    ∑ j, c j * (F j ∣[w j] x) τ = 0 := by
  obtain ⟨i, γ, hγ, hx | hx⟩ := hs.1 x
  · have e : ∀ j, (F j ∣[w j] x) τ = (F j ∣[w j] s i) τ := fun j => by
      rw [hx, (hF j).2.slash_mul hγ]
    simp only [e]
    exact h i
  · have e : ∀ j, (F j ∣[w j] x) τ = -(F j ∣[w j] s i) τ := fun j => by
      rw [hx, slash_neg_of_odd (hF j).1, (hF j).2.slash_mul hγ]
      rfl
    simp only [e, mul_neg, Finset.sum_neg_distrib, h i, neg_zero]

theorem mdiff_det_evM {r : ℕ} (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) {F : Fin r → ℍ → ℂ}
    (hF : ∀ j, MDiff (F j)) : MDiff (fun τ => (evM s w F τ).det) := by
  have he : ∀ i j, MDiff (fun τ => evM s w F τ i j) := fun i j => mdiff_slash (hF j) (w j) (s i)
  have e1 : (fun τ => (evM s w F τ).det) = ∑ σ : Equiv.Perm (Fin r), fun τ =>
      ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, evM s w F τ (σ i) i := by
    funext τ
    rw [Matrix.det_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [e1]
  refine MDifferentiable.sum fun σ _ => ?_
  refine mdifferentiable_const.mul ?_
  have e2 : (fun τ => ∏ i, evM s w F τ (σ i) i) = ∏ i, fun τ => evM s w F τ (σ i) i := by
    funext τ
    rw [Finset.prod_apply]
  rw [e2]
  exact MDifferentiable.prod fun i _ => he (σ i) i

end GlobalTheory.OddFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegrallyClosedInFractionFieldPowerSeries
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.OnePoint

universe u v w

section Algebra

variable {K : Type u} [Field K]

theorem exists_algHom_of_isIntegrallyClosedIn {L : Type w} [Field L] [Algebra K L]
    [IsIntegrallyClosedIn K L] {A : Type v} [CommRing A] [Algebra K A] [Algebra.IsIntegral K A]
    (φ : A →ₐ[K] L) : ∃ ψ : A →ₐ[K] K, (Algebra.ofId K L).comp ψ = φ := by
  have hmem : ∀ a : A, φ a ∈ (Algebra.ofId K L).range := fun a ↦
    (isIntegrallyClosedIn_iff.mp ‹_›).2 ((Algebra.IsIntegral.isIntegral (R := K) a).map φ)
  let e := AlgEquiv.ofInjective (Algebra.ofId K L) (algebraMap K L).injective
  refine ⟨(e.symm : _ →ₐ[K] K).comp (φ.codRestrict _ hmem), ?_⟩
  ext a
  exact congrArg Subtype.val (e.apply_symm_apply (φ.codRestrict _ hmem a))

end Algebra

section Scheme

variable {K : Type u} [Field K]

theorem epi_of_nonempty {T : Scheme.{u}} [Nonempty T] (g : T ⟶ Spec (.of K)) : Epi g :=
  have : Surjective g := ⟨Function.surjective_to_subsingleton _⟩
  Flat.epi_of_flat_of_surjective g

theorem point_ext {X T : Scheme.{u}} [Nonempty T] (g : T ⟶ Spec (.of K))
    {s s' : Spec (.of K) ⟶ X} (h : g ≫ s = g ≫ s') : s = s' :=
  have := epi_of_nonempty g
  (cancel_epi g).mp h

theorem exists_section_of_locallyQuasiFinite {F : Scheme.{u}} (f : F ⟶ Spec (.of K))
    [LocallyQuasiFinite f] (L : Type u) [Field L] [Algebra K L] [IsIntegrallyClosedIn K L]
    (x : Spec (.of L) ⟶ F) (hx : x ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    ∃ x₀ : Spec (.of K) ⟶ F, Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ x₀ = x ∧
      x₀ ≫ f = 𝟙 _ ∧
      ∀ x₁ : Spec (.of K) ⟶ F, Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ x₁ = x →
        x₁ = x₀ := by
  suffices H : ∃ x₀ : Spec (.of K) ⟶ F,
      Spec.map (CommRingCat.ofHom (algebraMap K L)) ≫ x₀ = x by
    obtain ⟨x₀, h₀⟩ := H
    refine ⟨x₀, h₀, point_ext (Spec.map (CommRingCat.ofHom (algebraMap K L))) ?_,
      fun x₁ h₁ ↦ point_ext _ (h₁.trans h₀.symm)⟩
    rw [reassoc_of% h₀, hx, Category.comp_id]
  obtain ⟨A, i, _, q, hq⟩ := Scheme.exists_Spec_apply_eq (x (Classical.arbitrary _))
  have hle : Set.range x ⊆ Set.range i := by
    rintro _ ⟨t, rfl⟩
    exact ⟨q, hq.trans (congrArg x (Subsingleton.elim _ _))⟩
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ i = x := ⟨_, IsOpenImmersion.lift_fac i x hle⟩
  obtain ⟨a, rfl⟩ := Spec.map_surjective l
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ f)
  have hqf : φ.hom.QuasiFinite := by
    have : LocallyQuasiFinite (Spec.map φ) := hφ ▸ inferInstance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mp this
  let : Algebra K A := φ.hom.toAlgebra
  have : Algebra.QuasiFinite K A := hqf
  have : Module.Finite K A := .of_quasiFinite
  rw [Category.assoc, ← hφ, ← Spec.map_comp] at hx
  have hc := congrArg CommRingCat.Hom.hom (Spec.map_injective hx)
  let a' : A →ₐ[K] L := ⟨a.hom, fun c ↦ DFunLike.congr_fun hc c⟩
  obtain ⟨ψ, hψ⟩ := exists_algHom_of_isIntegrallyClosedIn a'
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ i, ?_⟩
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext t
  exact DFunLike.congr_fun hψ t

end Scheme
end GlobalTheory.OnePoint
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicEmbeddingsConjugate
open scoped TensorProduct

namespace GlobalTheory.EmbUnitBallConj

variable {l : ℕ} [Fact l.Prime] {E : Type} [Field E]

theorem sum_eq_zero (a b : E →+* PadicAlgCl l) (h : ∀ x, ‖a x‖ < 1 ↔ ‖b x‖ < 1) {ι : Type}
    [Fintype ι] (y : ι → E) (c : ι → ℚ_[l]) (hc : ∑ k, c k • a (y k) = 0) :
    ∑ k, c k • b (y k) = 0 := by
  haveI : CharZero E := a.charZero
  have hd : DenseRange (Pi.map fun _ : ι => (Rat.cast : ℚ → ℚ_[l])) :=
    DenseRange.piMap fun _ => Padic.denseRange_ratCast l
  have hcl : ∀ f : E →+* PadicAlgCl l, IsClopen {c : ι → ℚ_[l] | ‖∑ k, c k • f (y k)‖ < 1} := by
    intro f
    have := (IsUltrametricDist.isClopen_ball (0 : PadicAlgCl l) 1).preimage
      (f := fun c : ι → ℚ_[l] => ∑ k, c k • f (y k)) (by fun_prop)
    convert this using 1
    ext c
    simp
  have key : ∀ c : ι → ℚ_[l], ‖∑ k, c k • a (y k)‖ < 1 → ‖∑ k, c k • b (y k)‖ < 1 := by
    intro c
    refine hd.induction_on c ?_ fun q => ?_
    · have := (hcl a).compl.isClosed.union (hcl b).isClosed
      convert this using 1
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff]
      exact imp_iff_not_or
    · have e : ∀ f : E →+* PadicAlgCl l,
          ∑ k, (Pi.map (fun _ : ι => (Rat.cast : ℚ → ℚ_[l])) q) k • f (y k) =
            f (∑ k, (q k : E) * y k) := by
        intro f
        simp [Algebra.smul_def]
      rw [e a, e b]
      exact (h _).1
  by_contra hne
  have hpos : 0 < ‖∑ k, c k • b (y k)‖ := norm_pos_iff.2 hne
  obtain ⟨r, hr⟩ := NormedField.exists_lt_norm ℚ_[l] ‖∑ k, c k • b (y k)‖⁻¹
  have h1 := key (r • c) (by
    simp only [Pi.smul_apply, smul_assoc, ← Finset.smul_sum, hc, smul_zero, norm_zero, zero_lt_one])
  simp only [Pi.smul_apply, smul_assoc, ← Finset.smul_sum, norm_smul] at h1
  rw [inv_lt_iff_one_lt_mul₀ hpos] at hr
  linarith

theorem exists_equiv_of_ker_le {F T K : Type} [Field F] [CommRing T] [Algebra F T] [Field K]
    [Algebra F K] [IsAlgClosed K] [Algebra.IsAlgebraic F K] (f g : T →ₐ[F] K)
    (h : RingHom.ker f ≤ RingHom.ker g) : ∃ σ : K ≃ₐ[F] K, ∀ x, σ (f x) = g x := by
  let S : IntermediateField F K :=
    Subalgebra.IsAlgebraic.toIntermediateField (S := f.range)
      (fun x _ => Algebra.IsAlgebraic.isAlgebraic x)
  let φ : f.range →ₐ[F] K :=
    (Ideal.Quotient.liftₐ (RingHom.ker f) g (fun a ha => h ha)).comp
      (Ideal.quotientKerEquivRange f).symm.toAlgHom
  have hφ : ∀ x, φ ⟨f x, x, rfl⟩ = g x := by
    intro x
    have : (Ideal.quotientKerEquivRange f).symm ⟨f x, x, rfl⟩ = Ideal.Quotient.mk _ x := by
      rw [AlgEquiv.symm_apply_eq]
      rfl
    change Ideal.Quotient.liftₐ (RingHom.ker f) g (fun a ha => h ha)
      ((Ideal.quotientKerEquivRange f).symm ⟨f x, x, rfl⟩) = g x
    rw [this]
    rfl
  let φ' : S →ₐ[F] K := φ
  obtain ⟨ψ, hψ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic (K := F) (L := S) (M := K)
    (E := K) φ'
  refine ⟨AlgEquiv.ofBijective ψ (Algebra.IsAlgebraic.algHom_bijective ψ), fun x => ?_⟩
  rw [← hφ x]
  exact DFunLike.congr_fun hψ (⟨f x, x, rfl⟩ : S)

noncomputable def ext (a : E →+* PadicAlgCl l) : ℚ_[l] ⊗[ℤ] E →ₐ[ℚ_[l]] PadicAlgCl l :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) a.toIntAlgHom (fun _ _ => Commute.all _ _)

theorem ext_tmul (a : E →+* PadicAlgCl l) (c : ℚ_[l]) (x : E) : ext a (c ⊗ₜ x) = c • a x := by
  simp [ext, Algebra.smul_def, Algebra.ofId_apply]

theorem exists_conj : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] (j₁ j₂ : Ω →+* PadicAlgCl l), (∀ x, ‖j₁ x‖ ≤ 1 ↔ ‖j₂ x‖ ≤ 1) → ∃ σ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l, ∀ x, σ (j₁ x) = j₂ x := by
  intro l _ Ω _ a b h
  have h' : ∀ x, ‖a x‖ < 1 ↔ ‖b x‖ < 1 := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have ha : 0 < ‖a x‖ := norm_pos_iff.2 ((map_ne_zero _).2 hx)
      have hb : 0 < ‖b x‖ := norm_pos_iff.2 ((map_ne_zero _).2 hx)
      have := h x⁻¹
      rw [map_inv₀, map_inv₀, norm_inv, norm_inv, inv_le_one₀ ha, inv_le_one₀ hb] at this
      rw [← not_le, ← not_le, this]
  obtain ⟨σ, hσ⟩ := exists_equiv_of_ker_le (ext a) (ext b) (by
    intro t ht
    obtain ⟨s, rfl⟩ := TensorProduct.exists_finset t
    set_option synthInstance.maxHeartbeats 100000 in
      rw [RingHom.mem_ker, map_sum] at ht ⊢
    simp only [ext_tmul] at ht ⊢
    rw [← Finset.sum_coe_sort] at ht ⊢
    exact sum_eq_zero a b h' _ _ ht)
  refine ⟨σ, fun x => ?_⟩
  simpa [ext_tmul] using hσ (1 ⊗ₜ x)

end GlobalTheory.EmbUnitBallConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AbsNormSqOfMulConjEqDifferentIdeal
open Real NumberField
namespace GlobalTheory

theorem absNorm_map_ringEquiv_self {R : Type} [CommRing R] [IsDedekindDomain R] [Module.Free ℤ R] (e : R ≃+* R) (J : Ideal R) :
    Ideal.absNorm (J.map e.toRingHom) = Ideal.absNorm J := by
  letI : Infinite R := Module.Free.infinite ℤ R
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv J (J.map e.toRingHom) e rfl).toEquiv).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicAutomorphismUnique
namespace GlobalTheory

open Polynomial

theorem denseRange_of_isAlgClosed_padicAlgCl (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω]
    [IsAlgClosed Ω] (j : Ω →+* PadicAlgCl l) : DenseRange j := by
  rw [Metric.denseRange_iff]
  intro a δ δpos
  haveI : CharZero Ω := j.charZero
  have hint : IsIntegral ℚ_[l] a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  set f : ℚ_[l][X] := minpoly ℚ_[l] a with hf
  have fmon : f.Monic := minpoly.monic hint
  have fnatdeg0 : f.natDegree ≠ 0 := (minpoly.natDegree_pos hint).ne'
  have fa0 : f.aeval a = 0 := minpoly.aeval _ _
  have hi : DenseRange (algebraMap ℚ ℚ_[l]) := Padic.denseRange_ratCast l
  have hε : (δ / (max ‖a‖ 1)) ^ f.natDegree / (f.natDegree + 1) > 0 := by positivity
  obtain ⟨g, gmon, gdeg, gcoeff⟩ :=
    exists_monic_and_natDegree_eq_and_norm_map_algebraMap_coeff_sub_lt hi fmon hε
  obtain ⟨b, hb, hab⟩ := exists_aroots_norm_sub_lt_of_norm_coeff_sub_lt
      hε fa0 fmon (gmon.map _) (gdeg ▸ (g.natDegree_map _)) gcoeff (IsAlgClosed.splits _)
  have hab : ‖a - b‖ < δ := by
    rw [← Real.rpow_natCast, ← mul_comm_div, div_self, one_mul,
        ← Real.rpow_mul (div_pos δpos (by positivity)).le, mul_inv_cancel₀] at hab
    · simpa [mul_assoc, div_mul_cancel₀ _ (by positivity : (max ‖a‖ 1) > 0).ne'] using hab
    · simp [fnatdeg0]
    · positivity
  have he : (g.map (algebraMap ℚ ℚ_[l])).map (algebraMap ℚ_[l] (PadicAlgCl l))
      = (g.map (algebraMap ℚ Ω)).map j := by
    rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    exact Subsingleton.elim _ _
  rw [Polynomial.aroots_def, he, Splits.roots_map (IsAlgClosed.splits _), Multiset.mem_map] at hb
  obtain ⟨c, -, hc⟩ := hb
  exact ⟨c, by rw [hc, dist_eq_norm]; exact hab⟩

theorem padicAlgCl_algEquiv_eq_of_eq_on_isAlgClosed :
    ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (j : Ω →+* PadicAlgCl l)
      (σ τ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l), (∀ x, σ (j x) = τ (j x)) → σ = τ := by
  intro l _ Ω _ _ j σ τ h
  have hc : ∀ g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l, Continuous g := fun g =>
    (AddMonoidHomClass.isometry_of_norm (g : PadicAlgCl l →+* PadicAlgCl l)
      fun x => (spectralNorm_eq_of_equiv g x).symm).continuous
  have := (denseRange_of_isAlgClosed_padicAlgCl l Ω j).equalizer (hc σ) (hc τ) (funext h)
  exact AlgEquiv.ext fun x => congrFun this x

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ImportsBis
namespace GlobalTheory.AlgebraicIntegerNormBound

theorem main : ∀ {A : Type} [inst : CommRing A] [IsDedekindDomain A] {Q : Ideal A} [Ideal.IsPrime Q], Q ≠ ⊥ → ∀ {π : A}, π ∈ Q → π ∉ Q ^ (2 : ℕ) → ∀ (m : ℕ), π ^ m ∉ Q ^ (m + (1 : ℕ)) := by
  intro A _ _ Q hQ hQ0 π h1 h2 m hm
  have hP : Prime Q := Ideal.prime_of_isPrime hQ0 hQ
  rw [← Ideal.dvd_span_singleton] at h1 h2 hm
  obtain ⟨J, hJ⟩ := h1
  have hJQ : ¬ Q ∣ J := by
    rintro ⟨K, hK⟩
    apply h2
    exact ⟨K, by rw [hJ, hK, pow_two, mul_assoc]⟩
  rw [← Ideal.span_singleton_pow, hJ, mul_pow, pow_succ] at hm
  have hQm : Q ^ m ≠ 0 := pow_ne_zero _ hQ0
  rw [mul_dvd_mul_iff_left hQm] at hm
  exact hJQ (hP.dvd_of_dvd_pow hm)

end GlobalTheory.AlgebraicIntegerNormBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PosDefExistsFrame
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem posDef_exists_frame :
    ∀ (d : ℕ) (G : Matrix (Fin d) (Fin d) ℂ), G.PosDef →
      ∃ X : Matrix (Fin d) (Fin d) ℂ, IsUnit X.det ∧ (X⁻¹)ᴴ * X⁻¹ = G := by
  intro d G hG
  open scoped MatrixOrder in
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hG.posSemidef.nonneg
  have hu : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit
  have hBu : IsUnit B.det := by
    rw [hB, Matrix.det_mul] at hu
    exact isUnit_of_mul_isUnit_right hu
  refine ⟨B⁻¹, Matrix.isUnit_nonsing_inv_det B hBu, ?_⟩
  rw [Matrix.nonsing_inv_nonsing_inv B hBu, hB, Matrix.star_eq_conjTranspose]

end GlobalTheory
end
