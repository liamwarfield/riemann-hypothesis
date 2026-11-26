module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGenerates
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGenerates
open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR.FundGen

theorem ringHom_eq_frob_pow (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Fintype F] [CharP F p]
    (f : ℕ) (hc : Fintype.card F = p ^ f) (α : F →+* F) :
    ∃ n < f, ∀ a, α a = a ^ p ^ n := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  let _ : Algebra (ZMod p) F := ZMod.algebra F p
  have hcomm : ∀ r : ZMod p, α (algebraMap (ZMod p) F r) = algebraMap (ZMod p) F r := fun r =>
    DFunLike.congr_fun
      (Subsingleton.elim (α.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) F)) r
  let β : F →ₐ[ZMod p] F := { α with commutes' := hcomm }
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgHom_pow (ZMod p) F).2 β
  have hrank : Module.finrank (ZMod p) F = f := by
    have h1 := Module.card_eq_pow_finrank (K := ZMod p) (V := F)
    rw [ZMod.card, hc] at h1
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h1).symm
  have key : ∀ k : ℕ, ∀ x : F, (FiniteField.frobeniusAlgHom (ZMod p) F ^ k) x = x ^ p ^ k := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ (FiniteField.frobeniusAlgHom (ZMod p) F) k, AlgHom.mul_apply, ih,
        FiniteField.frobeniusAlgHom_apply, ZMod.card, ← pow_mul, pow_succ' p k]
  refine ⟨(n : ℕ), lt_of_lt_of_eq n.isLt hrank, fun a => ?_⟩
  have h2 : (FiniteField.frobeniusAlgHom (ZMod p) F ^ (n : ℕ)) a = β a := DFunLike.congr_fun hn a
  rw [key] at h2
  exact h2.symm

def mIdeal {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (hv : v.Integers R) : Ideal R where
  carrier := {r | v (algebraMap R C r) < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add (f := _)] at *
    exact v.map_add_lt ha hb
  zero_mem' := by simp
  smul_mem' := by
    intro c x hx
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
    exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv.map_le_one c)) hx

theorem mem_mIdeal {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) (r : R) :
    r ∈ mIdeal v R hv ↔ v (algebraMap R C r) < 1 := by
  exact Iff.rfl

theorem mIdeal_ne_top {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) : mIdeal v R hv ≠ ⊤ := by
  intro h
  have h1 : (1 : R) ∈ mIdeal v R hv := by rw [h]; exact Submodule.mem_top
  rw [mem_mIdeal, map_one, map_one] at h1
  exact lt_irrefl _ h1

def toHom {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (hv : v.Integers R) {p : ℕ} (hp : v (p : C) < 1) (F : Type) [Field F]
    (σ : MulChar F R) (hσ : ∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) :
    F →+* R ⧸ mIdeal v R hv where
  toFun a := Ideal.Quotient.mk _ (σ a)
  map_one' := by rw [map_one, map_one]
  map_mul' a b := by rw [map_mul, map_mul]
  map_zero' := by rw [MulChar.map_zero, map_zero]
  map_add' a b := by
    have hle : Ideal.span {(p : R)} ≤ mIdeal v R hv := by
      rw [Ideal.span_singleton_le_iff_mem, mem_mIdeal]
      simpa using hp
    have := Ideal.Quotient.eq_zero_iff_mem.2 (hle (hσ a b))
    rw [map_sub, map_sub, sub_sub, sub_eq_zero] at this
    exact this

theorem toHom_apply {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) {p : ℕ} (hp : v (p : C) < 1) (F : Type) [Field F]
    (σ : MulChar F R) (hσ : ∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) (a : F) :
    toHom v R hv hp F σ hσ a = Ideal.Quotient.mk _ (σ a) := rfl

theorem toHom_injective {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (hv : v.Integers R) {p : ℕ} (hp : v (p : C) < 1) (F : Type) [Field F]
    (σ : MulChar F R) (hσ : ∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) :
    Function.Injective (toHom v R hv hp F σ hσ) := by
  have : Nontrivial (R ⧸ mIdeal v R hv) := Ideal.Quotient.nontrivial_iff.2 (mIdeal_ne_top v R hv)
  exact (toHom v R hv hp F σ hσ).injective

theorem mulChar_eq_of_gen {F R : Type} [Field F] [CommRing R] (g : Fˣ)
    (hg : ∀ y : Fˣ, y ∈ Submonoid.powers g) (χ χ' : MulChar F R)
    (h : χ (g : F) = χ' (g : F)) : χ = χ' := by
  apply MulChar.ext
  intro a
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 (hg a)
  rw [Units.val_pow_eq_pow_val, map_pow, map_pow, h]

theorem frob_pow_additive {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime] (F : Type) [Field F]
    [CharP F p] (σ : MulChar F R)
    (hσ : ∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) (n : ℕ) (a b : F) :
    (σ ^ p ^ n) (a + b) - (σ ^ p ^ n) a - (σ ^ p ^ n) b ∈ Ideal.span {(p : R)} := by
  have hpn : p ^ n ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  have e : ∀ x : F, (σ ^ p ^ n) x = σ (x ^ p ^ n) := fun x => by
    rw [MulChar.pow_apply' σ hpn, map_pow]
  rw [e, e, e, add_pow_char_pow]
  exact hσ _ _

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ σ : MulChar F R, (∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) → orderOf σ = p ^ f - 1 ∧ (∀ χ : MulChar F R, ∃ m, 1 ≤ m ∧ m ≤ p ^ f - 1 ∧ χ = σ ^ m) ∧ (∀ n, (∀ a b, (σ ^ p ^ n) (a + b) - (σ ^ p ^ n) a - (σ ^ p ^ n) b ∈ Ideal.span {(p : R)})) ∧ (∀ τ : MulChar F R, (∀ a b, τ (a + b) - τ a - τ b ∈ Ideal.span {(p : R)}) → ∃ n < f, τ = σ ^ p ^ n) ∧ (∀ a b : F, a ≠ b → v (algebraMap R C (σ a - σ b)) = 1) := by
  intro p _ C _ _ _ v R _ _ hv hp F _ _ _ _ f hc σ hσ
  have : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  have hinj : Function.Injective σ := fun a b hab =>
    toHom_injective v R hv hp F σ hσ (by rw [toHom_apply, toHom_apply, hab])
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hg' : ∀ y : Fˣ, y ∈ Submonoid.powers g := fun y => mem_powers_iff_mem_zpowers.2 (hg y)
  have hq : Fintype.card Fˣ = p ^ f - 1 := by rw [Fintype.card_units, hc]
  have hq1 : 1 ≤ p ^ f - 1 := hq ▸ Fintype.card_pos
  have hog : orderOf g = p ^ f - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hq]
  have hpowg : ∀ k : ℕ, (σ ^ k) (g : F) = σ (g : F) ^ k := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [pow_zero, pow_zero, MulChar.one_apply g.isUnit]
    · exact MulChar.pow_apply' σ hk.ne' _
  have hζ : IsPrimitiveRoot (σ (g : F)) (p ^ f - 1) := by
    refine ⟨?_, fun l hl => ?_⟩
    · rw [← map_pow, ← Units.val_pow_eq_pow_val, ← hog, pow_orderOf_eq_one, Units.val_one, map_one]
    · rw [← hog]
      apply orderOf_dvd_of_pow_eq_one
      apply Units.ext
      apply hinj
      rw [Units.val_pow_eq_pow_val, map_pow, hl, Units.val_one, map_one]
  have partB : ∀ χ : MulChar F R, ∃ m, 1 ≤ m ∧ m ≤ p ^ f - 1 ∧ χ = σ ^ m := by
    intro χ
    have hχ : χ (g : F) ^ (p ^ f - 1) = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, ← hq, pow_card_eq_one, Units.val_one, map_one]
    have : NeZero (p ^ f - 1) := ⟨by omega⟩
    obtain ⟨i, hi, hi'⟩ := hζ.eq_pow_of_pow_eq_one hχ
    by_cases hi0 : i = 0
    · refine ⟨p ^ f - 1, hq1, le_rfl, mulChar_eq_of_gen g hg' _ _ ?_⟩
      rw [hpowg, hζ.pow_eq_one, ← hi', hi0, pow_zero]
    · refine ⟨i, Nat.one_le_iff_ne_zero.2 hi0, hi.le, mulChar_eq_of_gen g hg' _ _ ?_⟩
      rw [hpowg, hi']
  refine ⟨?_, partB, fun n => frob_pow_additive p F σ hσ n, ?_, ?_⟩
  · rw [orderOf_eq_iff (by omega)]
    refine ⟨?_, fun m hm hm0 h => ?_⟩
    · apply MulChar.ext
      intro a
      rw [MulChar.pow_apply' σ (by omega), ← map_pow, ← Units.val_pow_eq_pow_val, ← hq,
        pow_card_eq_one, Units.val_one, map_one, MulChar.one_apply (Units.isUnit a)]
    · have h3 := DFunLike.congr_fun h (g : F)
      rw [hpowg, MulChar.one_apply g.isUnit] at h3
      exact hζ.pow_ne_one_of_pos_of_lt hm0.ne' hm h3
  · intro τ hτ
    obtain ⟨m, hm1, hmq, rfl⟩ := partB τ
    have e : ∀ x : F, (σ ^ m) x = σ (x ^ m) := fun x => by
      rw [MulChar.pow_apply' σ (by omega), map_pow]
    have hadd : ∀ a b : F, (a + b) ^ m = a ^ m + b ^ m := by
      intro a b
      apply toHom_injective v R hv hp F σ hσ
      have h3 := map_add (toHom v R hv hp F (σ ^ m) hτ) a b
      rw [toHom_apply, toHom_apply, toHom_apply, e, e, e] at h3
      rw [map_add (f := _), toHom_apply, toHom_apply, toHom_apply, h3]
    let α : F →+* F :=
      { toFun := fun x => x ^ m
        map_one' := one_pow m
        map_mul' := fun a b => mul_pow a b m
        map_zero' := zero_pow (by omega)
        map_add' := hadd }
    obtain ⟨n, hn, hα⟩ := ringHom_eq_frob_pow p F f hc α
    refine ⟨n, hn, ?_⟩
    apply MulChar.ext
    intro a
    rw [e, MulChar.pow_apply' σ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero), ← map_pow]
    congr 1
    exact hα a
  · intro a b hab
    have h1 : σ a - σ b ∉ mIdeal v R hv := by
      intro hmem
      apply hab
      apply toHom_injective v R hv hp F σ hσ
      rw [toHom_apply, toHom_apply]
      exact Ideal.Quotient.eq.2 hmem
    rw [mem_mIdeal, not_lt] at h1
    exact le_antisymm (hv.map_le_one _) h1

end GlobalTheory.CompanionTheory.Ar.GR.FundGen
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGeneratesStatement
open scoped Matrix TensorProduct
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_character_order_generates : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ σ : MulChar F R, (∀ a b, σ (a + b) - σ a - σ b ∈ Ideal.span {(p : R)}) → orderOf σ = p ^ f - 1 ∧ (∀ χ : MulChar F R, ∃ m, 1 ≤ m ∧ m ≤ p ^ f - 1 ∧ χ = σ ^ m) ∧ (∀ n, (∀ a b, (σ ^ p ^ n) (a + b) - (σ ^ p ^ n) a - (σ ^ p ^ n) b ∈ Ideal.span {(p : R)})) ∧ (∀ τ : MulChar F R, (∀ a b, τ (a + b) - τ a - τ b ∈ Ideal.span {(p : R)}) → ∃ n < f, τ = σ ^ p ^ n) ∧ (∀ a b : F, a ≠ b → v (algebraMap R C (σ a - σ b)) = 1) := by
  exact @GlobalTheory.CompanionTheory.Ar.GR.FundGen.main
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BlockGLSupportedMemMirabolicSupported
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

private theorem eq_of_forall_trace_mul_eq_trace_mul {E : Type} [Field E] [NumberField E] {b c : E}
    (h : ∀ a : E, Algebra.trace ℚ E (a * b) = Algebra.trace ℚ E (a * c)) : b = c := by
  apply ((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).injective
  ext a
  rw [LinearMap.BilinForm.toDual_def, LinearMap.BilinForm.toDual_def, Algebra.traceForm_apply,
    Algebra.traceForm_apply, mul_comm b, mul_comm c]
  exact h a

theorem existsUnique_sesq_of_trace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (V : Type) [AddCommGroup V] [Module E V] [Module ℚ V] [IsScalarTower ℚ E V] (B : LinearMap.BilinForm ℚ V), (∀ (a : E) x y, B (a • x) y = B x (IsCMField.complexConj E a • y)) → ∃! h : V → V → E, (∀ x y (a : E), Algebra.trace ℚ E (a * h x y) = B (a • x) y) ∧ (∀ x x' y, h (x + x') y = h x y + h x' y) ∧ (∀ x y y', h x (y + y') = h x y + h x y') ∧ (∀ (a : E) x y, h (a • x) y = a * h x y) ∧ (∀ (a : E) x y, h x (a • y) = IsCMField.complexConj E a * h x y) := by
  intro E _ _ _ V _ _ _ _ B hB
  obtain ⟨h, htr⟩ : ∃ h : V → V → E,
      ∀ x y (a : E), Algebra.trace ℚ E (a * h x y) = B (a • x) y := by
    refine ⟨fun x y => ((Algebra.traceForm ℚ E).toDual (traceForm_nondegenerate ℚ E)).symm
      { toFun := fun a => B (a • x) y
        map_add' := fun a b => by simp only [add_smul, map_add (f := _), LinearMap.add_apply]
        map_smul' := fun q a => by
          simp only [smul_assoc, map_smul, LinearMap.smul_apply, RingHom.id_apply] }, ?_⟩
    intro x y a
    dsimp only
    rw [mul_comm, ← Algebra.traceForm_apply, LinearMap.BilinForm.apply_toDual_symm_apply]
    rfl
  refine ⟨h, ⟨htr, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x x' y
    apply eq_of_forall_trace_mul_eq_trace_mul
    intro a
    rw [mul_add, map_add (f := _), htr, htr, htr, smul_add, map_add (f := _), LinearMap.add_apply]
  · intro x y y'
    apply eq_of_forall_trace_mul_eq_trace_mul
    intro a
    rw [mul_add, map_add (f := _), htr, htr, htr, map_add (f := _)]
  · intro b x y
    apply eq_of_forall_trace_mul_eq_trace_mul
    intro a
    rw [htr, ← mul_assoc, htr, mul_smul]
  · intro b x y
    apply eq_of_forall_trace_mul_eq_trace_mul
    intro a
    rw [htr, ← mul_assoc, htr, mul_comm a, mul_smul, hB (IsCMField.complexConj E b) (a • x) y,
      IsCMField.complexConj_apply_apply]
  · rintro h' ⟨htr', -⟩
    funext x y
    apply eq_of_forall_trace_mul_eq_trace_mul
    intro a
    rw [htr', htr]

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FiniteFreeHom
noncomputable section
namespace GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd

def FiniteFreeHom {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) : Prop :=
  letI := φ.toAlgebra
  Module.Free A B ∧ Module.Finite A B

end GlobalTheory.CompanionTheory.FreeQuotProof.Nbhd
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NormalNoethLocalDimOneIsDVR
open AlgebraicGeometry CategoryTheory Limits
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem normal_noeth_local_dim_one_isDVR : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R], ringKrullDim R = 1 → IsDiscreteValuationRing R := by
  intro R _ _ _ _ _ h1
  have hnf : ¬ IsField R := (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp h1).1
  have hdim : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by simp [h1])
  have h4 : IsIntegrallyClosed R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ P.IsPrime := by
    refine ⟨inferInstance, IsLocalRing.maximalIdeal R,
      ⟨fun h => hnf (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h), inferInstance⟩, ?_⟩
    rintro P ⟨hP, hPp⟩
    exact IsLocalRing.eq_maximalIdeal (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hdim P hP hPp)
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 1 4).mpr h4

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FcIndepDetNeZeroOfRank
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem fcIndep_det_ne_zero_of_rank {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (h : B.rank = n) :
    B.det ≠ 0 := by
  have hs : Function.Surjective B.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    simpa [Matrix.rank] using h
  have hu : IsUnit B := Matrix.mulVec_surjective_iff_isUnit.mp hs
  exact ((Matrix.isUnit_iff_isUnit_det B).mp hu).ne_zero

theorem fcIndep : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin q ⊕ Fin p) ℂ) (Φ : Matrix (Fin q ⊕ Fin p) (Fin q) ℂ), A * Φ = 0 → A.rank = p → Φ.rank = q → (Φᴴ * Φ).det ≠ 0 ∧ (fromRows Φᴴ A).det ≠ 0 ∧ ∀ N : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ, (fromRows N A).det * (Φᴴ * Φ).det = (fromRows Φᴴ A).det * (N * Φ).det := by
  intro p q A Φ h0 hA hΦ
  have h1 : (Φᴴ * Φ).det ≠ 0 := by
    apply fcIndep_det_ne_zero_of_rank
    open ComplexOrder in rw [Matrix.rank_conjTranspose_mul_self, hΦ]
  have h2 : (A * Aᴴ).det ≠ 0 := by
    apply fcIndep_det_ne_zero_of_rank
    open ComplexOrder in rw [Matrix.rank_self_mul_conjTranspose, hA]
  have key : ∀ N : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ,
      (fromRows N A).det * (fromCols Φ Aᴴ).det = (N * Φ).det * (A * Aᴴ).det := by
    intro N
    rw [← Matrix.det_mul, Matrix.fromRows_mul_fromCols, h0, Matrix.det_fromBlocks_zero₂₁]
  have h3 : (fromRows Φᴴ A).det * (fromCols Φ Aᴴ).det ≠ 0 := by
    rw [key]; exact mul_ne_zero h1 h2
  refine ⟨h1, left_ne_zero_of_mul h3, fun N => ?_⟩
  apply mul_right_cancel₀ (right_ne_zero_of_mul h3)
  have a := key N
  have b := key Φᴴ
  linear_combination (Φᴴ * Φ).det * a - (N * Φ).det * b

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ComapFgOfValuationRing
open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem comap_fg_of_valuationRing (R : Type) [CommRing R] [IsDomain R] [ValuationRing R]
    (ι κ : Type) [Fintype ι] [Fintype κ] (φ : (ι → R) →ₗ[R] (κ → R)) (W : Submodule R (κ → R))
    (hW : W.FG) : (W.comap φ).FG := by
  obtain ⟨c, w, hw⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hW
  let ψ : ((ι → R) × (Fin c → R)) →ₗ[R] (κ → R) := φ.coprod (Fintype.linearCombination R w)
  have hflat : Module.Flat R (LinearMap.range ψ) := by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout]
    exact Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance
  have hfree : Module.Free R (LinearMap.range ψ) := Module.free_of_flat_of_isLocalRing
  have hfp : Module.FinitePresentation R (LinearMap.range ψ) :=
    Module.finitePresentation_of_projective _ _
  have hsurj : Function.Surjective ψ.rangeRestrict := by
    rintro ⟨y, x, rfl⟩
    exact ⟨x, rfl⟩
  have hker : (LinearMap.ker ψ.rangeRestrict).FG :=
    Module.FinitePresentation.fg_ker _ hsurj
  have heq : W.comap φ = (LinearMap.ker ψ.rangeRestrict).map (LinearMap.fst R (ι → R) (Fin c → R)) := by
    ext l
    simp only [Submodule.mem_comap, Submodule.mem_map, LinearMap.mem_ker, LinearMap.fst_apply]
    constructor
    · intro hl
      rw [← hw, ← Fintype.range_linearCombination] at hl
      obtain ⟨a, ha⟩ := hl
      refine ⟨(l, -a), ?_, rfl⟩
      apply Subtype.ext
      simp [ψ, ha]
    · rintro ⟨⟨l', a⟩, h, rfl⟩
      have h' : φ l' + Fintype.linearCombination R w a = 0 := by
        simpa [ψ] using congrArg Subtype.val h
      have hm : Fintype.linearCombination R w a ∈ W := by
        rw [← hw, ← Fintype.range_linearCombination]
        exact ⟨a, rfl⟩
      rw [eq_neg_of_add_eq_zero_left h']
      exact W.neg_mem hm
  rw [heq]
  exact hker.map _

end GlobalTheory.CompanionTheory.Ar.GR
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProdNormEmbeddingsEqAbsNorm
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem prod_norm_embeddings_eq_abs_norm (F : Type) [Field F] [NumberField F] (α : F) :
    ∏ σ : F →+* ℂ, ‖σ α‖ = ((|Algebra.norm ℚ α| : ℚ) : ℝ) := by
  have h2 : ∏ σ : F →+* ℂ, σ α = ∏ σ : F →ₐ[ℚ] ℂ, σ α :=
    Fintype.prod_equiv (RingHom.equivRatAlgHom F ℂ) _ _ (fun σ => rfl)
  rw [← norm_prod, h2, ← Algebra.norm_eq_prod_embeddings ℚ ℂ α, eq_ratCast (algebraMap ℚ ℂ),
    Complex.norm_ratCast, Rat.cast_abs]

theorem norm_finite_embedding_eq_zpow (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (α : F) (k : ℤ)
    (h : v.valuation F α = WithZero.exp (-k)) :
    ‖FinitePlace.embedding v α‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-k) := by
  rw [FinitePlace.norm_embedding', h,
    WithZeroMulInt.toNNReal_neg_apply _ (WithZero.exp_ne_zero (a := -k)),
    WithZero.log_exp, NNReal.coe_zpow, NNReal.coe_natCast]

theorem sum_log_embeddings_eq (F : Type) [Field F] [NumberField F]
    (n : HeightOneSpectrum (𝓞 F) →₀ ℤ) (α : F) (hα : α ≠ 0)
    (hv : ∀ v : HeightOneSpectrum (𝓞 F), v.valuation F α = WithZero.exp (-(n v))) :
    ∑ σ : F →+* ℂ, Real.log ‖σ α‖ =
      n.sum fun v k => (k : ℝ) * Real.log (Ideal.absNorm v.asIdeal) := by
  have hσ : ∀ σ ∈ (Finset.univ : Finset (F →+* ℂ)), ‖σ α‖ ≠ 0 := fun σ _ =>
    norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr hα)
  rw [← Real.log_prod hσ, prod_norm_embeddings_eq_abs_norm]
  have hv2 : ∀ v : HeightOneSpectrum (𝓞 F),
      ‖FinitePlace.embedding v α‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n v)) :=
    fun v => norm_finite_embedding_eq_zpow F v α (n v) (hv v)
  have key : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v α‖
      = ∏ᶠ w : FinitePlace F, w α := by
    rw [← finprod_comp_equiv (FinitePlace.equivHeightOneSpectrum (K := F)).symm]
    simp only [FinitePlace.equivHeightOneSpectrum_symm_apply]
  have hprod : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖FinitePlace.embedding v α‖
      = ∏ v ∈ n.support, (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n v)) := by
    simp only [hv2]
    apply finprod_eq_prod_of_mulSupport_subset
    intro v hvs
    rw [Function.mem_mulSupport] at hvs
    by_contra hn
    simp only [Finset.mem_coe, Finsupp.mem_support_iff, not_not] at hn
    apply hvs
    simp [hn]
  have E0 := FinitePlace.prod_eq_inv_abs_norm hα
  rw [← key, hprod] at E0
  have hfac : ∀ v ∈ n.support, (Ideal.absNorm v.asIdeal : ℝ) ^ (-(n v)) ≠ 0 := by
    intro v _
    apply zpow_ne_zero
    exact_mod_cast (mt Ideal.absNorm_eq_zero_iff.mp v.ne_bot)
  have L := congrArg Real.log E0
  push_cast at L ⊢
  rw [Real.log_prod hfac, Real.log_inv] at L
  simp only [Real.log_zpow] at L
  rw [Finsupp.sum]
  have hneg : ∑ v ∈ n.support, ((-(n v) : ℤ) : ℝ) * Real.log (Ideal.absNorm v.asIdeal)
      = -∑ v ∈ n.support, (n v : ℝ) * Real.log (Ideal.absNorm v.asIdeal) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ => ?_
    push_cast
    ring
  linarith

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FrobeniusChainCarry
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.RaCarry
open scoped Matrix TensorProduct
open Matrix

namespace PositivityTheory.HtPt.Ra

theorem carry : ∀ (p f : ℕ), 2 ≤ p → 0 < f → ∀ (y : ℕ → NNReal), (∀ n, y (n + f) = y n) → (∀ n, y n ≤ 1) → (∀ n, y n ^ p ≤ y (n + 1)) → ∀ (e : Fin f → ℕ) (j : ℕ), 2 ≤ ∑ n, e n → (∑ n : Fin f, e n * p ^ (n : ℕ)) ≡ p ^ (j + 1) [MOD (p ^ f - 1)] → ∏ n : Fin f, y n ^ e n ≤ y j ^ p := by
  intro p f hp hf y hper hle1 hstep e j he hcong
  have hperm : ∀ a c, y (a + f * c) = y a := by
    intro a c
    induction c with
    | zero => simp
    | succ c ih => rw [Nat.mul_succ, ← Nat.add_assoc, hper, ih]
  have hiter : ∀ a k, y a ^ (p ^ k) ≤ y (a + k) := by
    intro a k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, pow_mul, ← Nat.add_assoc]
      exact (pow_le_pow_left₀ zero_le ih p).trans (hstep _)
  obtain ⟨q, s, hs, hj⟩ : ∃ q s, s < f ∧ j = s + f * q :=
    ⟨j / f, j % f, Nat.mod_lt _ hf, (Nat.mod_add_div j f).symm⟩
  have hk : ∀ n : Fin f, ∃ k c m c', k + m = f - 1 ∧ (n : ℕ) + k = s + f * c ∧
      m + (j + 1) = n + f * c' := by
    intro n
    have hn := n.isLt
    by_cases h : (n : ℕ) ≤ s
    · refine ⟨s - n, 0, f - 1 - (s - n), q + 1, by omega, by omega, ?_⟩
      rw [hj, Nat.mul_succ]
      omega
    · refine ⟨s + f - n, 1, f - 1 - (s + f - n), q, by omega, by omega, ?_⟩
      rw [hj]
      omega
  choose k c m c' hkm hkc hmc using hk
  have hyk : ∀ n : Fin f, y n ^ (p ^ k n) ≤ y j := by
    intro n
    have := hiter n (k n)
    rw [hkc, hperm] at this
    rw [hj, hperm]
    exact this
  have hpos : 1 ≤ p := by omega
  have hN : p ^ f - 1 + 1 = p ^ f := Nat.sub_add_cancel (Nat.one_le_pow _ _ hpos)
  have hT1 : (∑ n : Fin f, e n * p ^ m n) ≡ 1 [MOD (p ^ f - 1)] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    have hc := (ZMod.natCast_eq_natCast_iff _ _ _).2 hcong
    push_cast at hc ⊢
    set u : ZMod (p ^ f - 1) := (p : ZMod (p ^ f - 1)) with hu
    have huf : u ^ f = 1 := by
      rw [hu, ← Nat.cast_pow, ← hN, Nat.cast_add, ZMod.natCast_self, zero_add, Nat.cast_one]
    have hper' : ∀ a c, u ^ (a + f * c) = u ^ a := by
      intro a c
      rw [pow_add, pow_mul, huf, one_pow, mul_one]
    have hunit : IsUnit (u ^ (j + 1)) := by
      refine IsUnit.pow _ (isUnit_iff_exists_inv.2 ⟨u ^ (f - 1), ?_⟩)
      rw [← pow_succ', Nat.sub_add_cancel hf, huf]
    have hmul : (∑ n : Fin f, (e n : ZMod (p ^ f - 1)) * u ^ m n) * u ^ (j + 1) = u ^ (j + 1) := by
      refine (Finset.sum_mul _ _ _).trans ((Finset.sum_congr rfl fun n _ => ?_).trans hc)
      rw [mul_assoc, ← pow_add, hmc, hper']
    have h0 : ((∑ n : Fin f, (e n : ZMod (p ^ f - 1)) * u ^ m n) - 1) * u ^ (j + 1) = 0 := by
      rw [sub_mul, hmul, one_mul, sub_self]
    exact sub_eq_zero.1 (hunit.mul_left_eq_zero.1 h0)
  have hT2 : 2 ≤ ∑ n : Fin f, e n * p ^ m n :=
    le_trans he (Finset.sum_le_sum fun n _ => Nat.le_mul_of_pos_right _ (pow_pos (by omega) _))
  have hTf : p ^ f ≤ ∑ n : Fin f, e n * p ^ m n := by
    have hd := (Nat.modEq_iff_dvd' (by omega : 1 ≤ ∑ n : Fin f, e n * p ^ m n)).1 hT1.symm
    have hle := Nat.le_of_dvd (by omega) hd
    generalize p ^ f = P at *
    generalize ∑ n : Fin f, e n * p ^ m n = T at *
    omega
  have hP : 0 < p ^ (f - 1) := pow_pos (by omega) _
  refine (pow_le_pow_iff_left₀ zero_le zero_le hP.ne').1 ?_
  calc (∏ n : Fin f, y n ^ e n) ^ p ^ (f - 1)
      = ∏ n : Fin f, (y n ^ p ^ k n) ^ (e n * p ^ m n) := by
        rw [← Finset.prod_pow]
        refine Finset.prod_congr rfl fun n _ => ?_
        rw [← pow_mul, ← pow_mul]
        congr 1
        rw [← hkm n, pow_add]
        ring
    _ ≤ ∏ n : Fin f, y j ^ (e n * p ^ m n) :=
        Finset.prod_le_prod₀ (fun _ _ => zero_le) fun n _ => pow_le_pow_left₀ zero_le (hyk n) _
    _ = y j ^ (∑ n : Fin f, e n * p ^ m n) := Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ y j ^ p ^ f := pow_le_pow_of_le_one zero_le (hle1 j) hTf
    _ = (y j ^ p) ^ p ^ (f - 1) := by
        rw [← pow_mul, ← pow_succ']
        congr 2
        omega

end PositivityTheory.HtPt.Ra
end

open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem frobeniusChain_carry : ∀ (p f : ℕ), 2 ≤ p → 0 < f → ∀ (y : ℕ → NNReal), (∀ n, y (n + f) = y n) → (∀ n, y n ≤ 1) → (∀ n, y n ^ p ≤ y (n + 1)) → ∀ (e : Fin f → ℕ) (j : ℕ), 2 ≤ ∑ n, e n → (∑ n : Fin f, e n * p ^ (n : ℕ)) ≡ p ^ (j + 1) [MOD (p ^ f - 1)] → ∏ n : Fin f, y n ^ e n ≤ y j ^ p :=
  PositivityTheory.HtPt.Ra.carry

end GlobalTheory.CompanionTheory.Ar.GR
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SymplecticPeriodMatrixIntegrality
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.MulEqSmulOneSymm
open scoped Matrix TensorProduct
open Matrix

namespace PositivityTheory.HtPt.Rh

theorem mul_eq_smul_one_symm {R n : Type} [CommRing R] [IsDomain R] [Fintype n] [DecidableEq n]
    {A B : Matrix n n R} {c : R} (hc : c ≠ 0) (h : A * B = c • (1 : Matrix n n R)) :
    B * A = c • (1 : Matrix n n R) := by
  have hd : B.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det h
    rw [det_mul, h0, mul_zero, det_smul, det_one, mul_one] at this
    exact pow_ne_zero _ hc this.symm
  have h1 : (B * A - c • (1 : Matrix n n R)) * B = 0 := by
    rw [sub_mul, Matrix.mul_assoc, h]; simp
  have h2 : B.det • (B * A - c • (1 : Matrix n n R)) = 0 := by
    have := congrArg (· * B.adjugate) h1
    simpa only [Matrix.mul_assoc, mul_adjugate, Matrix.mul_smul, Matrix.mul_one, Matrix.zero_mul]
      using this
  exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_left hd)

theorem gp_mat : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → ∀ (g : ℕ) (Ht Bt : Matrix (Fin g) (Fin g ⊕ Fin g) R) (E : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) R) (cp : R), cp ≠ 0 → Eᵀ = -E → IsUnit E.det → Btᵀ * Ht - Htᵀ * Bt = cp • E → let φ := algebraMap R C; let intg : (Fin g → C) → Prop := fun w => ∀ k, v (w k) ≤ 1; let hb : Matrix (Fin g ⊕ Fin g) (Fin g) C := ((Eᵀ)⁻¹ * Htᵀ).map φ; v (φ (Matrix.fromRows Ht Bt).det) = v (φ cp) ^ g ∧ (∀ x : Fin g ⊕ Fin g → C, ((Ht.map φ) *ᵥ x = 0 ∧ intg ((Bt.map φ) *ᵥ x)) ↔ ∃ w, intg w ∧ x = (φ cp)⁻¹ • (hb *ᵥ w)) ∧ (∀ w, intg w → ∃ x : Fin g ⊕ Fin g → C, (Ht.map φ) *ᵥ x = w ∧ (Bt.map φ) *ᵥ x = 0) ∧ (∀ l : Fin g ⊕ Fin g → R, cp • l ∈ Submodule.span R (Set.range fun k => Matrix.fromRows Ht Bt k)) := by
  intro C _ v R _ _ hv g Ht Bt E cp hcp hE hEu hform φ intg hb
  have : IsDomain R := hv.hom_inj.isDomain _
  have hcp' : φ cp ≠ 0 := fun h => hcp (hv.hom_inj (by rw [map_zero]; exact h))
  have hEt : IsUnit (Eᵀ).det := by rwa [det_transpose]
  set U : Matrix (Fin g ⊕ Fin g) (Fin g) R := -((Eᵀ)⁻¹ * Btᵀ) with hU
  set W : Matrix (Fin g ⊕ Fin g) (Fin g) R := (Eᵀ)⁻¹ * Htᵀ with hW
  have h1 : U * Ht + W * Bt = cp • (1 : Matrix _ _ R) := by
    have : U * Ht + W * Bt = (Eᵀ)⁻¹ * (-(Btᵀ * Ht - Htᵀ * Bt)) := by
      rw [hU, hW, neg_sub, Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc]
      abel
    rw [this, hform, ← smul_neg, ← hE, Matrix.mul_smul, nonsing_inv_mul _ hEt]
  have h2 : fromCols U W * fromRows Ht Bt = cp • (1 : Matrix _ _ R) := by
    rw [fromCols_mul_fromRows, h1]
  have h3 := mul_eq_smul_one_symm hcp h2
  rw [fromRows_mul_fromCols, ← fromBlocks_one, fromBlocks_smul, fromBlocks_inj] at h3
  obtain ⟨a11, a12, a21, a22⟩ := h3
  rw [smul_zero] at a12 a21
  have hone : ∀ {n : Type} [DecidableEq n], (cp • (1 : Matrix n n R)).map φ = φ cp • (1 : Matrix n n C) := by
    intro n _
    ext i j
    by_cases h : i = j <;> simp [h]
  have b1 := congrArg (·.map φ) h1
  have b11 := congrArg (·.map φ) a11
  have b12 := congrArg (·.map φ) a12
  have b21 := congrArg (·.map φ) a21
  have b22 := congrArg (·.map φ) a22
  simp only [Matrix.map_add _ (map_add φ), Matrix.map_mul, hone, Matrix.map_zero _ (map_zero φ)]
    at b1 b11 b12 b21 b22
  refine ⟨?_, fun x => ⟨fun hx => ⟨_, hx.2, ?_⟩, ?_⟩, fun w _ => ⟨(φ cp)⁻¹ • (U.map φ *ᵥ w), ?_, ?_⟩,
    fun l => ?_⟩
  · have hJ : (fromRows Ht Bt)ᵀ * Matrix.J (Fin g) R * fromRows Ht Bt = cp • E := by
      rw [← hform, Matrix.J, transpose_fromRows, fromCols_mul_fromBlocks, fromCols_mul_fromRows]
      simp [sub_eq_add_neg]
    have hd := congrArg (fun M => v (φ M.det)) hJ
    simp only [det_mul, det_transpose, det_smul, map_mul, map_pow, Fintype.card_sum,
      Fintype.card_fin] at hd
    rw [hv.one_of_isUnit (Matrix.isUnit_det_J (Fin g) R), hv.one_of_isUnit hEu, mul_one, mul_one,
      pow_add] at hd
    exact (mul_self_inj zero_le zero_le).1 hd
  · have := congrArg (· *ᵥ x) b1
    simp only [add_mulVec, ← mulVec_mulVec, hx.1, mulVec_zero, zero_add, smul_mulVec,
      one_mulVec] at this
    change x = (φ cp)⁻¹ • (W.map φ *ᵥ _)
    rw [this, inv_smul_smul₀ hcp']
  · rintro ⟨w, hw, rfl⟩
    change Ht.map φ *ᵥ ((φ cp)⁻¹ • (W.map φ *ᵥ w)) = 0 ∧
      intg (Bt.map φ *ᵥ ((φ cp)⁻¹ • (W.map φ *ᵥ w)))
    rw [mulVec_smul, mulVec_smul, mulVec_mulVec, mulVec_mulVec, b12, b22, zero_mulVec, smul_zero,
      smul_mulVec, one_mulVec, inv_smul_smul₀ hcp']
    exact ⟨rfl, hw⟩
  · rw [mulVec_smul, mulVec_mulVec, b11, smul_mulVec, one_mulVec, inv_smul_smul₀ hcp']
  · rw [mulVec_smul, mulVec_mulVec, b21, zero_mulVec, smul_zero]
  · have : cp • l = (l ᵥ* fromCols U W) ᵥ* fromRows Ht Bt := by
      rw [vecMul_vecMul, h2, vecMul_smul, vecMul_one]
    rw [this, vecMul_eq_sum]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end PositivityTheory.HtPt.Rh
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SymplecticPeriodMatrixIntegrality
namespace GlobalTheory.CompanionTheory.Ar.GR
alias gp_mat_lattice := PositivityTheory.HtPt.Rh.gp_mat
end GlobalTheory.CompanionTheory.Ar.GR
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SymplecticPeriodMatrixIntegralityStatement
alias GlobalTheory.T.symplectic_period_matrix_integrality := GlobalTheory.CompanionTheory.Ar.GR.gp_mat_lattice
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DetFromColsFrameChange
namespace GlobalTheory.CompanionTheory.Ar.Flat

open Matrix

theorem det_fromCols_frame_change : ∀ (R : Type) [CommRing R] (p q : ℕ) (J J₂ : Matrix (Fin p ⊕ Fin q) (Fin p) R) (S S₂ : Matrix (Fin q) (Fin p ⊕ Fin q) R) (T T₂ : Matrix (Fin p ⊕ Fin q) (Fin q) R) (A : Matrix (Fin p) (Fin p) R) (B : Matrix (Fin q) (Fin q) R), S * J = 0 → S * T = 1 → IsUnit (Matrix.fromCols J T).det → S₂ * T₂ = 1 → J₂ = J * A → S = B * S₂ → (Matrix.fromCols J₂ T₂).det = (Matrix.fromCols J T).det * A.det * B.det := by
  intro R _ p q J J₂ S S₂ T T₂ A B hSJ hST hU hST₂ hJ hS
  set W : Matrix (Fin p ⊕ Fin q) (Fin q) R := (Matrix.fromCols J T)⁻¹ * T₂ with hW
  have h1 : Matrix.fromCols J T * W = T₂ := by
    rw [hW, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hU, Matrix.one_mul]
  have h2 : J * W.toRows₁ + T * W.toRows₂ = T₂ := by
    rw [← Matrix.fromCols_mul_fromRows, Matrix.fromRows_toRows, h1]
  have h3 : W.toRows₂ = B := by
    have h := congrArg (fun X => S * X) h2
    simp only [Matrix.mul_add, ← Matrix.mul_assoc, hSJ, hST, Matrix.zero_mul, Matrix.one_mul,
      zero_add] at h
    rw [h, hS, Matrix.mul_assoc, hST₂, Matrix.mul_one]
  have h4 : Matrix.fromCols J₂ T₂ =
      Matrix.fromCols J T * Matrix.fromBlocks A W.toRows₁ 0 B := by
    rw [Matrix.fromCols_mul_fromBlocks, Matrix.mul_zero, add_zero, ← hJ, ← h3, h2]
  rw [h4, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, mul_assoc]

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FromRowsMulFromColsSplit
namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem fromRows_mul_fromCols_split {R : Type} [CommRing R] {p q : ℕ}
    (J : Matrix (Fin p ⊕ Fin q) (Fin p) R) (S : Matrix (Fin q) (Fin p ⊕ Fin q) R)
    (J' : Matrix (Fin p) (Fin p ⊕ Fin q) R) (S' : Matrix (Fin p ⊕ Fin q) (Fin q) R)
    (h0 : S * J = 0) (hJ : J' * J = 1) (hS : S * S' = 1) :
    Matrix.fromRows (J' * (1 - S' * S)) S * Matrix.fromCols J S' = 1 := by
  rw [Matrix.fromRows_mul_fromCols]
  have e1 : J' * (1 - S' * S) * J = 1 := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
      h0, Matrix.mul_zero, sub_zero, hJ]
  have e2 : J' * (1 - S' * S) * S' = 0 := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc,
      hS, Matrix.mul_zero, sub_self]
  rw [e1, e2, h0, hS, Matrix.fromBlocks_one]

theorem splitExact_of_rank : ∀ (R : Type) [CommRing R] (p q : ℕ) (J : Matrix (Fin p ⊕ Fin q) (Fin p) R) (S : Matrix (Fin q) (Fin p ⊕ Fin q) R), S * J = 0 → (∃ J' : Matrix (Fin p) (Fin p ⊕ Fin q) R, J' * J = 1) → (∃ S' : Matrix (Fin p ⊕ Fin q) (Fin q) R, S * S' = 1) → (∀ S' : Matrix (Fin p ⊕ Fin q) (Fin q) R, S * S' = 1 → IsUnit (Matrix.fromCols J S').det) ∧ ∀ v, S.mulVec v = 0 ↔ ∃ w, J.mulVec w = v := by
  rintro R inst p q J S h0 ⟨J', hJ⟩ ⟨S₀, hS₀⟩
  refine ⟨fun S' hS => ?_, fun v => ⟨fun hv => ?_, ?_⟩⟩
  · exact Matrix.isUnit_det_of_left_inverse (fromRows_mul_fromCols_split J S J' S' h0 hJ hS)
  · have hMN := fromRows_mul_fromCols_split J S J' S₀ h0 hJ hS₀
    have hNM : Matrix.fromCols J S₀ * Matrix.fromRows (J' * (1 - S₀ * S)) S = 1 := by
      exact mul_eq_one_comm.mp hMN
    rw [Matrix.fromCols_mul_fromRows] at hNM
    refine ⟨(J' * (1 - S₀ * S)).mulVec v, ?_⟩
    calc J.mulVec ((J' * (1 - S₀ * S)).mulVec v)
        = J.mulVec ((J' * (1 - S₀ * S)).mulVec v) + S₀.mulVec (S.mulVec v) := by
          rw [hv, Matrix.mulVec_zero, add_zero]
      _ = (J * (J' * (1 - S₀ * S)) + S₀ * S).mulVec v := by
          rw [Matrix.add_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = v := by rw [hNM, Matrix.one_mulVec]
  · rintro ⟨w, rfl⟩
    rw [Matrix.mulVec_mulVec, h0, Matrix.zero_mulVec]

end GlobalTheory.CompanionTheory.Ar.Flat
end
