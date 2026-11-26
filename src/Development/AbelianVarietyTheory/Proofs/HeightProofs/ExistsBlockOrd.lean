module

public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.IsotypicSignedParameters
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PowEqPowIffModEqOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsBlockOrd
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Matrix

namespace GlobalTheory.RealPar

variable {p q n : ℕ}

def BlockOrd (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) : Prop :=
  (∀ i, ε (e (Sum.inl i)) = true) ∧ (∀ j, ε (e (Sum.inr j)) = false) ∧ ∀ a b, posC a b → e a < e b

def Factors {T : GrpData p q} (U : URep T) (e : Ix p q ≃ Fin n)
    (σ : Matrix (Fin n) (Fin n) ℂ → (U.H →L[ℂ] U.H)) : Prop :=
  ∀ x, U.π x = σ (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q))

theorem BlockOrd.sameBlock_iff {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (a b : Ix p q) :
    sameBlock a b ↔ ε (e a) = ε (e b) := by
  obtain ⟨h1, h2, -⟩ := h
  cases a <;> cases b <;> simp [sameBlock, h1, h2]

theorem BlockOrd.posC_iff {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (a b : Ix p q) :
    posC a b ↔ e a < e b ∧ ε (e a) = ε (e b) := by
  constructor
  · intro hab
    refine ⟨h.2.2 a b hab, ?_⟩
    rw [← h.sameBlock_iff]
    cases a <;> cases b <;> simp_all [posC, sameBlock]
  · rintro ⟨hlt, heq⟩
    rw [← h.sameBlock_iff] at heq
    have hne : a ≠ b := fun hab => by subst hab; exact lt_irrefl _ hlt
    have hnot : ¬ posC b a := fun hba => lt_asymm hlt (h.2.2 b a hba)
    cases a with
    | inl i =>
      cases b with
      | inl j =>
        simp only [posC] at hnot ⊢
        rcases lt_trichotomy i j with hij | hij | hij
        · exact hij
        · exact absurd (congrArg Sum.inl hij) hne
        · exact absurd hij hnot
      | inr j => simp [sameBlock] at heq
    | inr i =>
      cases b with
      | inl j => simp [sameBlock] at heq
      | inr j =>
        simp only [posC] at hnot ⊢
        rcases lt_trichotomy i j with hij | hij | hij
        · exact hij
        · exact absurd (congrArg Sum.inr hij) hne
        · exact absurd hij hnot

theorem exists_blockOrd (ε : Fin n → Bool) (hp : (Finset.univ.filter fun a => ε a = true).card = p)
    (hq : (Finset.univ.filter fun a => ε a = false).card = q) : ∃ e : Ix p q ≃ Fin n, BlockOrd e ε := by
  classical
  set S := Finset.univ.filter fun a => ε a = true with hS
  set T := Finset.univ.filter fun a => ε a = false with hT
  have hcard : p + q = n := by
    have h0 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (fun a => ε a = true)
    simp only [Bool.not_eq_true, Finset.card_univ, Fintype.card_fin] at h0
    rw [← hp, ← hq]
    exact h0
  let f : Ix p q → Fin n := fun x =>
    match x with
    | Sum.inl i => S.orderEmbOfFin hp i
    | Sum.inr j => T.orderEmbOfFin hq j
  have fS : ∀ i, ε (f (Sum.inl i)) = true := fun i =>
    (Finset.mem_filter.mp (S.orderEmbOfFin_mem hp i)).2
  have fT : ∀ j, ε (f (Sum.inr j)) = false := fun j =>
    (Finset.mem_filter.mp (T.orderEmbOfFin_mem hq j)).2
  have hinj : Function.Injective f := by
    intro x y hxy
    cases x with
    | inl i =>
      cases y with
      | inl j => exact congrArg Sum.inl ((S.orderEmbOfFin hp).injective hxy)
      | inr j =>
        have h1 := fS i
        rw [hxy, fT j] at h1
        exact absurd h1 (by simp)
    | inr i =>
      cases y with
      | inl j =>
        have h1 := fT i
        rw [hxy, fS j] at h1
        exact absurd h1 (by simp)
      | inr j => exact congrArg Sum.inr ((T.orderEmbOfFin hq).injective hxy)
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    simp [hcard]
  refine ⟨Equiv.ofBijective f hbij, ?_, ?_, ?_⟩
  · intro i
    exact fS i
  · intro j
    exact fT j
  · intro a b hab
    simp only [Equiv.ofBijective_apply]
    cases a with
    | inl i =>
      cases b with
      | inl j => exact (S.orderEmbOfFin hp).strictMono hab
      | inr j => exact absurd hab (by simp [posC])
    | inr i =>
      cases b with
      | inl j => exact absurd hab (by simp [posC])
      | inr j => exact (T.orderEmbOfFin hq).strictMono hab

theorem BlockOrd.reindex_Jm {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) :
    Matrix.reindex e e (Jm p q) = Formalism.REAL.Jm ε := by
  obtain ⟨h1, h2, -⟩ := h
  ext a b
  obtain ⟨a', rfl⟩ := e.surjective a
  obtain ⟨b', rfl⟩ := e.surjective b
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Formalism.REAL.Jm,
    Matrix.diagonal_apply, EmbeddingLike.apply_eq_iff_eq, Jm, Formalism.UG.Jpq]
  cases a' <;> cases b' <;> simp [h1, h2, Matrix.one_apply] <;> split_ifs <;> simp

theorem BlockOrd.inUJ_iff {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (g : Mat p q) :
    Formalism.REAL.inUJ ε (Matrix.reindex e e g) ↔ gᴴ * Jm p q * g = Jm p q := by
  have key : ∀ M N : Mat p q, Matrix.reindex e e M * Matrix.reindex e e N = Matrix.reindex e e (M * N) := by
    intro M N
    simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  unfold Formalism.REAL.inUJ
  rw [← h.reindex_Jm, Matrix.conjTranspose_reindex, key, key]
  exact (Matrix.reindex e e).injective.eq_iff

theorem mem_Upq (g : GL (Ix p q) ℂ) : g ∈ Formalism.UG.Upq p q ↔ (g : Mat p q)ᴴ * Jm p q * g = Jm p q := by
  unfold Formalism.UG.Upq Formalism.UG.UJ
  rw [Subgroup.mem_mk]
  show Formalism.UG.cT (starRingEnd ℂ) (g : Mat p q) * Formalism.UG.Jpq p q * (g : Mat p q) = Formalism.UG.Jpq p q ↔ _
  have hc : Formalism.UG.cT (starRingEnd ℂ) (g : Mat p q) = (g : Mat p q)ᴴ := by
    ext i j
    simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  rw [hc]
  rfl

theorem BlockOrd.cov_mem {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q) (x : T.G) :
    Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) ∈ UJset ε := by
  show Formalism.REAL.inUJ ε _
  exact (h.inUJ_iff _).mpr ((mem_Upq _).mp (T.cov_mem x))

theorem BlockOrd.cov_surj {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (T : GrpData p q)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    ∃ x : T.G, Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) = g := by
  have hg' : Formalism.REAL.inUJ ε g := hg
  set g' : Mat p q := (Matrix.reindex e e).symm g
  have hre : Matrix.reindex e e g' = g := (Matrix.reindex e e).apply_symm_apply g
  have hU : g'ᴴ * Jm p q * g' = Jm p q := by
    rw [← h.inUJ_iff, hre]
    exact hg'
  have hJJ : Jm p q * Jm p q = 1 := by
    simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_multiply]
  have hleft : (Jm p q * g'ᴴ * Jm p q) * g' = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc g'ᴴ, hU, hJJ]
  have hright : g' * (Jm p q * g'ᴴ * Jm p q) = 1 := mul_eq_one_comm.mp hleft
  let u : GL (Ix p q) ℂ := ⟨g', Jm p q * g'ᴴ * Jm p q, hright, hleft⟩
  have hu : u ∈ Formalism.UG.Upq p q := (mem_Upq u).mpr hU
  have hdet : (u : Mat p q).det ≠ 0 := by
    have := (Matrix.isUnit_iff_isUnit_det (u : Mat p q)).mp u.isUnit
    exact this.ne_zero
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : Mat p q).det (by norm_num : 0 < 2)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact hdet (by rw [← hz]; simp)
  obtain ⟨x, ⟨hx, -⟩, -⟩ := T.bij u hu (Units.mk0 z hz0) (by simpa using hz)
  refine ⟨x, ?_⟩
  rw [hx]
  exact hre

theorem exists_factors {T : GrpData p q} (U : URep T) (e : Ix p q ≃ Fin n)
    (h : ∀ x, T.cov x = 1 → U.π x = 1) : ∃ σ, Factors U e σ := by
  classical
  refine ⟨fun M => if hM : ∃ x, Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) = M
    then U.π hM.choose else 0, ?_⟩
  intro x
  have hM : ∃ y, Matrix.reindex e e ((T.cov y : GL (Ix p q) ℂ) : Mat p q) =
      Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) := ⟨x, rfl⟩
  simp only [dif_pos hM]
  set y := hM.choose with hy
  have hyx : T.cov y = T.cov x := Units.ext ((Matrix.reindex e e).injective hM.choose_spec)
  have h1 : T.cov (y⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, hyx, inv_mul_cancel]
  have h2 : U.π y⁻¹ * U.π x = 1 := by
    rw [← map_mul]
    exact h _ h1
  calc U.π x = U.π (y * y⁻¹) * U.π x := by simp
    _ = U.π y * (U.π y⁻¹ * U.π x) := by rw [map_mul, mul_assoc]
    _ = U.π y := by rw [h2, mul_one]

end GlobalTheory.RealPar

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.NatCastMulFinrankMemDifferentIdeal
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize Pointwise
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.DifferentBound

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

theorem algebraMap_intTrace_eq_sum (x : 𝓞 L) :
    algebraMap (𝓞 K) (𝓞 L) (Algebra.intTrace (𝓞 K) (𝓞 L) x) = ∑ σ : L ≃ₐ[K] L, σ • x := by
  apply FaithfulSMul.algebraMap_injective (𝓞 L) L
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 K) K L,
    Algebra.algebraMap_intTrace (L := L), trace_eq_sum_automorphisms, map_sum]
  rfl

theorem not_dvd_of_inertia (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥)
    (h : ∀ σ : L ≃ₐ[K] L, (∀ x : 𝓞 L, σ • x - x ∈ P) → σ = 1) :
    ¬ P ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  have hp : P.under (𝓞 K) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hP
  have := Ideal.IsPrime.isMaximal inferInstance hP
  have : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  have hcard := Ideal.card_inertia_eq_ramificationIdxIn (G := L ≃ₐ[K] L) (P.under (𝓞 K)) P
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (P.under (𝓞 K)) P (L ≃ₐ[K] L)] at hcard
  have hb : P.inertia (L ≃ₐ[K] L) = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    exact h σ hσ
  rw [hb, Subgroup.card_bot] at hcard
  rw [not_dvd_differentIdeal_iff]
  exact Ideal.ramificationIdx_eq_one_iff.1 hcard.symm

theorem not_pow_dvd (n : ℕ) (hn : 0 < n) (P Q : Ideal (𝓞 L)) [hP : P.IsMaximal] (m : ℕ) (hnP : (n : 𝓞 L) ∈ P)
    (hPQ : P ⊔ Q = ⊤) (h : Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)} = P ^ m * Q) :
    ¬ P ^ m ∣ differentIdeal (𝓞 K) (𝓞 L) := by
  classical
  have hco : IsCoprime (P ^ m) Q := (Ideal.isCoprime_iff_sup_eq.2 hPQ).pow_left
  obtain ⟨a, ha, x, hx, hax⟩ := Submodule.mem_sup.1
    ((Ideal.eq_top_iff_one _).1 (Ideal.isCoprime_iff_sup_eq.1 hco))
  refine not_dvd_differentIdeal_of_intTrace_not_mem (𝓞 K)
    (p := Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 K)}) (P ^ m) Q ?_ x hx ?_
  · rw [Ideal.map_span, Set.image_singleton, map_natCast, h]
  intro htr
  have hle : Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)} ≤ P ^ m := h ▸ Ideal.mul_le_left
  have h1 : ∑ σ : L ≃ₐ[K] L, σ • x ∈ P ^ m := by
    rw [← algebraMap_intTrace_eq_sum]
    apply hle
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 K) (𝓞 L)) htr
    rwa [Ideal.map_span, Set.image_singleton, map_natCast] at this
  set S := MulAction.stabilizer (L ≃ₐ[K] L) P
  have h2 : ∀ σ : L ≃ₐ[K] L, σ • x - (if σ ∈ S then 1 else 0) ∈ P ^ m := by
    intro σ
    split_ifs with hσ
    · have h3 : σ • a ∈ σ • P ^ m := Ideal.smul_mem_pointwise_smul σ a _ ha
      rw [smul_pow', MulAction.mem_stabilizer_iff.1 hσ] at h3
      have h4 : σ • x - 1 = -(σ • a) := by
        rw [← smul_one σ, ← hax, smul_add]; ring
      rw [h4]
      exact neg_mem h3
    · rw [sub_zero]
      have h3 : σ • x ∈ σ • Q := Ideal.smul_mem_pointwise_smul σ x _ hx
      have h4 : σ • Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)} =
          Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)} := by
        rw [Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton, map_natCast]
      have h5 : P ^ m ∣ (σ • P) ^ m * σ • Q := by
        rw [← smul_pow', ← smul_mul', ← h, h4]
        exact Ideal.dvd_iff_le.2 hle
      have hM : (σ • P).IsMaximal := by
        rw [Ideal.pointwise_smul_def]
        exact Ideal.map_isMaximal_of_equiv (MulSemiringAction.toRingEquiv (L ≃ₐ[K] L) (𝓞 L) σ)
      have h6 : IsCoprime P (σ • P) :=
        Ideal.isCoprime_iff_sup_eq.2 (hP.coprime_of_ne hM fun e => hσ (MulAction.mem_stabilizer_iff.2 e.symm))
      exact Ideal.dvd_iff_le.1 ((h6.pow).dvd_of_dvd_mul_left h5) h3
  have h7 : ((Nat.card S : ℕ) : 𝓞 L) ∈ P ^ m := by
    have h8 := sub_mem h1 (Ideal.sum_mem _ fun σ (_ : σ ∈ Finset.univ) => h2 σ)
    rw [Finset.sum_sub_distrib, sub_sub_cancel, Finset.sum_boole] at h8
    rwa [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h9 : ((Module.finrank K L : ℕ) : 𝓞 L) ∈ P ^ m := by
    obtain ⟨c, hc⟩ := S.card_subgroup_dvd_card
    rw [← IsGalois.card_aut_eq_finrank, hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ h7
  have h10 : P ^ m * P ∣ P ^ m * Q := by
    rw [← h, Ideal.dvd_span_singleton, Nat.cast_mul, mul_comm (n : 𝓞 L)]
    exact Ideal.mul_mem_mul h9 hnP
  have h0 : P ^ m ≠ 0 := by
    intro e
    rw [e, zero_mul, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero] at h
    exact (Nat.mul_pos hn Module.finrank_pos).ne' h
  have h11 := Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_left h0).1 h10)
  exact hP.ne_top (by rw [← hPQ, sup_eq_left.2 h11])

omit K L in
theorem natCast_mul_finrank_mem_differentIdeal :
    ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L] (n : ℕ), 0 < n →
      (∀ 𝔭 : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∉ 𝔭.asIdeal → GlobalTheory.NT.UnramIn L 𝔭) →
      ((n * Module.finrank K L : ℕ) : 𝓞 L) ∈ differentIdeal (𝓞 K) (𝓞 L) := by
  intro K L _ _ _ _ _ _ n hn hu
  classical
  have hD0 : differentIdeal (𝓞 K) (𝓞 L) ≠ 0 := differentIdeal_ne_bot
  have hI : Ideal.span {((n * Module.finrank K L : ℕ) : 𝓞 L)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (Nat.mul_pos hn Module.finrank_pos).ne'
  rw [← Ideal.dvd_span_singleton, UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hD0]
  intro P hP
  have hPp : P.IsPrime := Ideal.isPrime_of_prime hP
  have hP0 : P ≠ ⊥ := hP.ne_zero
  have hPm := hPp.isMaximal hP0
  by_cases hnP : (n : 𝓞 L) ∈ P
  · obtain ⟨Q, hPQ, h⟩ := Ideal.eq_prime_pow_mul_coprime hI P
    have h1 := not_pow_dvd K L n hn P Q _ hnP hPQ h
    exact (emultiplicity_lt_iff_not_dvd.2 h1).le.trans (le_emultiplicity_of_pow_dvd ⟨Q, h⟩)
  · have hp : P.under (𝓞 K) ≠ ⊥ := mt Ideal.eq_bot_of_comap_eq_bot hP0
    have h1 := hu ⟨P.under (𝓞 K), inferInstance, hp⟩ (fun e => hnP (by simpa using Ideal.mem_comap.1 e))
    have h2 := not_dvd_of_inertia K L P hP0 fun σ hσ => h1 σ ⟨P, hPp, ⟨rfl⟩, hσ⟩
    rw [emultiplicity_eq_zero.2 h2]
    exact zero_le

end GlobalTheory.DifferentBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.HeckeIdealEqOfRay
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.FieldSize GlobalTheory.NT
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.FieldSize.RayDegree

section General

variable {R : Type} [CommRing R] [IsDedekindDomain R] {m : Ideal R}

theorem isCoprime_span {a : R} (ha : a - 1 ∈ m) : IsCoprime (Ideal.span {a}) m :=
  Ideal.isCoprime_iff_exists.mpr ⟨a, Ideal.mem_span_singleton_self a, -(a - 1), m.neg_mem ha, by ring⟩

theorem exists_mem_sub_one {I : Ideal R} (hI0 : I ≠ ⊥) (h : IsCoprime I m) : ∃ a ∈ I, a ≠ 0 ∧ a - 1 ∈ m := by
  by_cases ht : m = ⊤
  · obtain ⟨a, haI, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
    exact ⟨a, haI, ha0, by simp [ht]⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.mp h
  have h1 : a - 1 ∈ m := by
    have : a - 1 = -b := by rw [← hab]; ring
    rw [this]
    exact m.neg_mem hb
  refine ⟨a, ha, ?_, h1⟩
  rintro rfl
  apply ht
  rw [Ideal.eq_top_iff_one]
  simpa using m.neg_mem h1

theorem exists_good {I J : Ideal R} (hI0 : I ≠ ⊥) (hJ0 : J ≠ ⊥) (hI : IsCoprime I m) (hJ : IsCoprime J m)
    {x y : R} (hy : y ≠ 0) (h : Ideal.span {x} * I = Ideal.span {y} * J) :
    ∃ a b : R, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ m ∧ IsCoprime (Ideal.span {b}) m ∧
      Ideal.span {a} * I = Ideal.span {b} * J := by
  obtain ⟨a, haJ, ha0, ha⟩ := exists_mem_sub_one hJ0 hJ
  have h1 : y * a ∈ Ideal.span {x} * I := by
    rw [h]; exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self y) haJ
  obtain ⟨b, -, hb⟩ := Ideal.mem_span_singleton_mul.mp h1
  have h2 : Ideal.span {a} * I = Ideal.span {b} * J := by
    have hy' : (Ideal.span {y} : Ideal R) ≠ 0 := by simpa using hy
    apply mul_left_cancel₀ hy'
    rw [← mul_assoc, Ideal.span_singleton_mul_span_singleton, ← hb, mul_left_comm, ← h, ← mul_assoc,
      Ideal.span_singleton_mul_span_singleton, mul_comm b x]
  refine ⟨a, b, ha0, ?_, ha, ?_, h2⟩
  · rintro rfl
    simp [ha0, hI0] at h2
  · have := (isCoprime_span ha).mul_left hI
    rw [h2] at this
    exact this.of_mul_left_left

end General

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] {𝔮 : Ideal (𝓞 K)}

theorem emb_ne_zero (φ : K →+* ℝ) {a : 𝓞 K} (ha : a ≠ 0) : φ (a : K) ≠ 0 := by
  simpa using ha

theorem heckeIdeal_eq_of_ray (hR : IsRay L 𝔮) {I J : Ideal (𝓞 K)} (hI0 : I ≠ ⊥) (hJ0 : J ≠ ⊥)
    (hI : IsCoprime I 𝔮) (hJ : IsCoprime J 𝔮) {α β : 𝓞 K} (hp : RayPair 𝔮 α β)
    (h : I * Ideal.span {β} = J * Ideal.span {α}) (χ : (L ≃ₐ[K] L) →* ℂˣ) :
    heckeIdeal L χ I = heckeIdeal L χ J := by
  obtain ⟨a, haJ, ha0, ha⟩ := exists_mem_sub_one hJ0 hJ
  have ha2 : a * a - 1 ∈ 𝔮 := by
    have : a * a - 1 = (a + 1) * (a - 1) := by ring
    rw [this]; exact 𝔮.mul_mem_left _ ha
  obtain ⟨M, hM⟩ : J ∣ Ideal.span {a * a} := Ideal.dvd_span_singleton.mpr (J.mul_mem_left _ haJ)
  have hM' : IsCoprime M 𝔮 := by
    have := isCoprime_span ha2
    rw [hM] at this
    exact this.of_mul_left_right
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    simp [ha0] at hM
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hp
  have e1 : heckeIdeal L χ (J * M) = 1 := by
    refine (hR.2.2 _ (mul_ne_zero hJ0 hM0) (hJ.mul_left hM')).2 ⟨a * a, 1, ⟨mul_ne_zero ha0 ha0, one_ne_zero,
      isCoprime_span ha2, isCoprime_span (by simp), ha2, fun φ => ?_⟩, by simp [hM]⟩ χ
    have := mul_self_pos.2 (emb_ne_zero φ ha0)
    simpa using this
  have e2 : heckeIdeal L χ (I * M) = 1 := by
    refine (hR.2.2 _ (mul_ne_zero hI0 hM0) (hI.mul_left hM')).2 ⟨a * a * α, β,
      ⟨mul_ne_zero (mul_ne_zero ha0 ha0) h1, h2, ?_, h4, ?_, fun φ => ?_⟩, ?_⟩ χ
    · rw [← Ideal.span_singleton_mul_span_singleton]
      exact (isCoprime_span ha2).mul_left h3
    · have : a * a * α - β = α * (a * a - 1) + (α - β) := by ring
      rw [this]
      exact 𝔮.add_mem (𝔮.mul_mem_left _ ha2) h5
    · have := mul_pos (mul_self_pos.2 (emb_ne_zero φ ha0)) (h6 φ)
      simpa [mul_assoc] using this
    · rw [mul_right_comm, h, mul_right_comm, ← hM, Ideal.span_singleton_mul_span_singleton]
  rw [GlobalTheory.NT.Model.heckeIdeal_mul L χ hJ0 hM0] at e1
  rw [GlobalTheory.NT.Model.heckeIdeal_mul L χ hI0 hM0] at e2
  exact mul_right_cancel₀ (right_ne_zero_of_mul_eq_one e1) (e2.trans e1.symm)

theorem exists_ideal [IsGalois K L] (hR : IsRay L 𝔮) (σ : L ≃ₐ[K] L) :
    ∃ I : Ideal (𝓞 K), I ≠ ⊥ ∧ IsCoprime I 𝔮 ∧ ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = (χ σ : ℂˣ) := by
  let S : Submonoid (L ≃ₐ[K] L) :=
    { carrier := {σ | ∃ I : Ideal (𝓞 K), I ≠ ⊥ ∧ IsCoprime I 𝔮 ∧
        ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, heckeIdeal L χ I = (χ σ : ℂˣ)}
      one_mem' := ⟨1, one_ne_zero, isCoprime_one_left, fun χ => by rw [GlobalTheory.NT.Model.heckeIdeal_top]; simp⟩
      mul_mem' := by
        rintro x y ⟨I, hI0, hI, hx⟩ ⟨J, hJ0, hJ, hy⟩
        refine ⟨I * J, mul_ne_zero hI0 hJ0, hI.mul_left hJ, fun χ => ?_⟩
        rw [GlobalTheory.NT.Model.heckeIdeal_mul L χ hI0 hJ0, hx, hy]; simp }
  have hσ : σ ∈ Subgroup.closure
      {σ : L ≃ₐ[K] L | ∃ 𝔭 : HeightOneSpectrum (𝓞 K), ¬ 𝔭.asIdeal ∣ 𝔮 ∧ GlobalTheory.NT.IsFrob L 𝔭 σ} := by
    rw [hR.2.1]; trivial
  change σ ∈ S
  induction hσ using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨v, hv, hx⟩ := hx
    refine ⟨v.asIdeal, v.ne_bot, ?_, fun χ => ?_⟩
    · rw [Ideal.isCoprime_iff_sup_eq]
      by_contra hne
      exact hv (Ideal.dvd_iff_le.2 (le_sup_right.trans (v.isMaximal.eq_of_le hne le_sup_left).ge))
    · rw [GlobalTheory.NT.Model.heckeIdeal_prime, heckeVal_of_unramIn L χ (hR.1 v hv) hx]
  | one => exact S.one_mem
  | mul x y _ _ hx hy => exact S.mul_mem hx hy
  | inv x _ hx =>
    have : x⁻¹ = x ^ (orderOf x - 1) := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
    rw [this]
    exact S.pow_mem hx _

theorem finrank_le : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsAbelianGalois K L] (𝔮 : Ideal (𝓞 K)), 𝔮 ≠ ⊥ → IsRay L 𝔮 →
    Module.finrank K L ≤ classNumber K * Ideal.absNorm 𝔮 * 2 ^ Fintype.card (K →+* ℝ) := by
  intro K L _ _ _ _ _ _ 𝔮 h𝔮 hR
  classical
  choose s hs0 hs hsx using exists_ideal hR
  let cl : (L ≃ₐ[K] L) → ClassGroup (𝓞 K) := fun x =>
    ClassGroup.mk0 ⟨s x, mem_nonZeroDivisors_of_ne_zero (hs0 x)⟩
  have key : ∀ x, ∃ a b : 𝓞 K, a ≠ 0 ∧ b ≠ 0 ∧ a - 1 ∈ 𝔮 ∧ IsCoprime (Ideal.span {b}) 𝔮 ∧
      Ideal.span {a} * s x = Ideal.span {b} * s (Function.invFun cl (cl x)) := by
    intro x
    have h : cl x = cl (Function.invFun cl (cl x)) := (Function.invFun_eq ⟨x, rfl⟩).symm
    obtain ⟨a, b, -, hb, hxy⟩ := ClassGroup.mk0_eq_mk0_iff.mp h
    exact exists_good (hs0 x) (hs0 _) (hs x) (hs _) hb hxy
  choose a b ha0 hb0 ha hb hab using key
  let F : (L ≃ₐ[K] L) → (ClassGroup (𝓞 K) × (𝓞 K ⧸ 𝔮)) × ((K →+* ℝ) → Prop) := fun x =>
    ((cl x, Ideal.Quotient.mk 𝔮 (b x)), fun φ => 0 < φ (a x : K) * φ (b x : K))
  have hF : Function.Injective F := by
    intro x y hxy
    obtain ⟨h12, h3⟩ := Prod.mk.inj hxy
    obtain ⟨h1, h2⟩ := Prod.mk.inj h12
    rw [Ideal.Quotient.eq] at h2
    have hp : RayPair 𝔮 (b x * a y) (a x * b y) := by
      refine ⟨mul_ne_zero (hb0 x) (ha0 y), mul_ne_zero (ha0 x) (hb0 y), ?_, ?_, ?_, fun φ => ?_⟩
      · rw [← Ideal.span_singleton_mul_span_singleton]
        exact (hb x).mul_left (isCoprime_span (ha y))
      · rw [← Ideal.span_singleton_mul_span_singleton]
        exact (isCoprime_span (ha x)).mul_left (hb y)
      · have : b x * a y - a x * b y = b x * (a y - 1) - b y * (a x - 1) + (b x - b y) := by ring
        rw [this]
        exact 𝔮.add_mem (𝔮.sub_mem (𝔮.mul_mem_left _ (ha y)) (𝔮.mul_mem_left _ (ha x))) h2
      · have h4 : 0 < φ (a x : K) * φ (b x : K) ↔ 0 < φ (a y : K) * φ (b y : K) := (congrFun h3 φ).to_iff
        have h5 := mul_ne_zero (emb_ne_zero φ (ha0 x)) (emb_ne_zero φ (hb0 x))
        have h6 := mul_ne_zero (emb_ne_zero φ (ha0 y)) (emb_ne_zero φ (hb0 y))
        have h7 : 0 < (φ (a x : K) * φ (b x : K)) * (φ (a y : K) * φ (b y : K)) := by
          by_cases h : 0 < φ (a x : K) * φ (b x : K)
          · exact mul_pos h (h4.1 h)
          · exact mul_pos_of_neg_of_neg (lt_of_le_of_ne (not_lt.1 h) h5)
              (lt_of_le_of_ne (not_lt.1 fun h' => h (h4.2 h')) h6)
        convert h7 using 1
        push_cast
        simp only [map_mul]
        ring
    have he : s x * Ideal.span {a x * b y} = s y * Ideal.span {b x * a y} := by
      have e1 := hab x
      have e2 := hab y
      rw [← h1] at e2
      rw [← Ideal.span_singleton_mul_span_singleton, ← Ideal.span_singleton_mul_span_singleton,
        ← mul_assoc, mul_comm (s x), e1, mul_comm (s y), mul_assoc _ _ (s y), e2]
      ring
    have hχ : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, χ x = χ y := fun χ => by
      apply Units.ext
      rw [← hsx, ← hsx]
      exact heckeIdeal_eq_of_ray hR (hs0 x) (hs0 y) (hs x) (hs y) hp he χ
    by_contra hne
    letI : CommGroup (L ≃ₐ[K] L) := IsMulCommutative.instCommGroup
    obtain ⟨χ, h⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity (L ≃ₐ[K] L) ℂ
      (a := x * y⁻¹) (by rwa [ne_eq, mul_inv_eq_one])
    apply h
    rw [map_mul, map_inv, hχ χ, mul_inv_cancel]
  haveI : Finite (𝓞 K ⧸ 𝔮) := Ideal.finiteQuotientOfFreeOfNeBot 𝔮 h𝔮
  rw [← IsGalois.card_aut_eq_finrank]
  refine (Nat.card_le_card_of_injective F hF).trans (le_of_eq ?_)
  rw [Nat.card_prod, Nat.card_prod, Ideal.absNorm_apply, Submodule.cardQuot_apply, classNumber,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := _ → Prop)]
  simp

end GlobalTheory.FieldSize.RayDegree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.LogRootDiscrLeOfNatCastMemDifferentIdeal
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory

theorem log_rootDiscr_le_of_natCast_mem_differentIdeal : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (N : ℕ), 0 < N → (N : 𝓞 L) ∈ differentIdeal (𝓞 K) (𝓞 L) → Real.log |((discr L : ℤ) : ℝ)| / Module.finrank ℚ L ≤ Real.log |((discr K : ℤ) : ℝ)| / Module.finrank ℚ K + Real.log N := by
  intro K L _ _ _ _ _ N hN hmem
  have h1 := NumberField.natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow K (𝓞 K) L (𝓞 L)
  have h2 : Ideal.absNorm (differentIdeal (𝓞 K) (𝓞 L)) ∣ Ideal.absNorm (Ideal.span {(N : 𝓞 L)}) :=
    Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).2 hmem)
  have h3 : Ideal.absNorm (Ideal.span {(N : 𝓞 L)}) = N ^ Module.finrank ℚ L := by
    rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank]
  rw [h3] at h2
  have h4 := Nat.le_of_dvd (pow_pos hN _) h2
  have h5 : (discr L).natAbs ≤ N ^ Module.finrank ℚ L * (discr K).natAbs ^ Module.finrank K L := by
    rw [h1]; exact Nat.mul_le_mul_right _ h4
  have hL : (0 : ℝ) < |((discr L : ℤ) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero L)
  have hK : (0 : ℝ) < |((discr K : ℤ) : ℝ)| := abs_pos.2 (by exact_mod_cast discr_ne_zero K)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h6 : |((discr L : ℤ) : ℝ)| ≤ (N : ℝ) ^ Module.finrank ℚ L * |((discr K : ℤ) : ℝ)| ^ Module.finrank K L := by
    have : (((discr L).natAbs : ℕ) : ℝ) ≤ ((N ^ Module.finrank ℚ L * (discr K).natAbs ^ Module.finrank K L : ℕ) : ℝ) := by
      exact_mod_cast h5
    simpa [Nat.cast_natAbs] using this
  have h7 := Real.log_le_log hL h6
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at h7
  have h8 : Module.finrank ℚ K * Module.finrank K L = Module.finrank ℚ L := Module.finrank_mul_finrank ℚ K L
  have hk : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hl : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have h9 : (Module.finrank ℚ K : ℝ) * Module.finrank K L = Module.finrank ℚ L := by exact_mod_cast h8
  rw [div_le_iff₀ hl]
  refine h7.trans (le_of_eq ?_)
  rw [← h9]
  field_simp
  ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.NcardEqIffStabilizer
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldSize.RaySplit

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize GlobalTheory.NT
open scoped IntermediateField Pointwise

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

set_option autoImplicit false in
theorem _root_.GlobalTheory.FieldSize.RaySplit.ncard_eq_primesOver (𝔭 : HeightOneSpectrum (𝓞 K)) :
    {Q : HeightOneSpectrum (𝓞 L) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 L)) = 𝔭.asIdeal}.ncard =
      (𝔭.asIdeal.primesOver (𝓞 L)).ncard := by
  have hinj : Function.Injective (fun Q : HeightOneSpectrum (𝓞 L) => Q.asIdeal) :=
    fun Q Q' h => HeightOneSpectrum.ext h
  rw [← Set.ncard_image_of_injective _ hinj]
  congr 1
  ext P
  simp only [Set.mem_image, Set.mem_setOf_eq, Ideal.primesOver]
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    exact ⟨Q.isPrime, ⟨hQ.symm⟩⟩
  · rintro ⟨hP, hlies⟩
    refine ⟨⟨P, hP, ?_⟩, hlies.over.symm, rfl⟩
    rintro rfl
    apply 𝔭.ne_bot
    rw [hlies.over, Ideal.under, Ideal.comap_bot_of_injective]
    exact FaithfulSMul.algebraMap_injective _ _

set_option autoImplicit false in
private theorem ncard_primesOver_eq_finrank_iff_frob_eq_one {F R : Type} [Field F]
    [NumberField F] [Field R] [NumberField R] [Algebra F R] [IsGalois F R]
    {𝔭 : HeightOneSpectrum (𝓞 F)} (hu : _root_.GlobalTheory.NT.UnramIn R 𝔭) {σ : Gal(R/F)}
    (hσ : _root_.GlobalTheory.NT.IsFrob R 𝔭 σ) :
    (𝔭.asIdeal.primesOver (𝓞 R)).ncard = Module.finrank F R ↔ σ = 1 := by
  obtain ⟨P, hPp, hPo, hfrob⟩ := hσ
  haveI := hPp
  haveI := hPo
  have hPne : P ≠ ⊥ := by
    rintro rfl
    apply 𝔭.ne_bot
    rw [hPo.over, Ideal.under, Ideal.comap_bot_of_injective]
    exact FaithfulSMul.algebraMap_injective _ _
  haveI : P.IsMaximal := hPp.isMaximal hPne
  haveI : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
  have he : 𝔭.asIdeal.ramificationIdxIn (𝓞 R) = 1 := by
    rw [← Ideal.card_inertia_eq_ramificationIdxIn (G := Gal(R/F)) 𝔭.asIdeal P]
    have hbot : Ideal.inertia Gal(R/F) P = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro τ hτ
      exact hu τ ⟨P, hPp, hPo, fun x => (AddSubgroup.mem_inertia.mp hτ) x⟩
    rw [hbot, Subgroup.card_bot]
  have hf : 𝔭.asIdeal.inertiaDegIn (𝓞 R) = Module.finrank (𝓞 F ⧸ 𝔭.asIdeal) (𝓞 R ⧸ P) := by
    rw [Ideal.inertiaDegIn_eq_inertiaDeg 𝔭.asIdeal P Gal(R/F), ← Ideal.inertiaDeg_eq_inertiaDeg' 𝔭.asIdeal P,
      Ideal.inertiaDeg'_algebraMap]
  have hcount :=
    Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝔭.asIdeal (𝓞 R) Gal(R/F)
  rw [he, one_mul, hf, IsGalois.card_aut_eq_finrank] at hcount
  have hdeg : 0 < Module.finrank F R := Module.finrank_pos
  letI : Field (𝓞 F ⧸ 𝔭.asIdeal) := Ideal.Quotient.field _
  letI : Field (𝓞 R ⧸ P) := Ideal.Quotient.field _
  letI : Fintype (𝓞 F ⧸ 𝔭.asIdeal) := Fintype.ofFinite _
  letI : Fintype (𝓞 R ⧸ P) := Fintype.ofFinite _
  have hq : Ideal.absNorm 𝔭.asIdeal = Fintype.card (𝓞 F ⧸ 𝔭.asIdeal) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hcard : Fintype.card (𝓞 R ⧸ P) =
      Fintype.card (𝓞 F ⧸ 𝔭.asIdeal) ^ Module.finrank (𝓞 F ⧸ 𝔭.asIdeal) (𝓞 R ⧸ P) :=
    Module.card_eq_pow_finrank
  have hq1 : 1 < Fintype.card (𝓞 F ⧸ 𝔭.asIdeal) := Fintype.one_lt_card
  have hsplit : (𝔭.asIdeal.primesOver (𝓞 R)).ncard = Module.finrank F R ↔
      Module.finrank (𝓞 F ⧸ 𝔭.asIdeal) (𝓞 R ⧸ P) = 1 := by
    constructor
    · intro h
      rw [h] at hcount
      exact Nat.eq_of_mul_eq_mul_left hdeg (hcount.trans (mul_one _).symm)
    · intro h
      rw [h, mul_one] at hcount
      exact hcount
  rw [hsplit]
  constructor
  · intro h1
    have hcq : Fintype.card (𝓞 R ⧸ P) = Fintype.card (𝓞 F ⧸ 𝔭.asIdeal) := by
      rw [hcard, h1, pow_one]
    apply hu σ
    refine ⟨P, hPp, hPo, fun x => ?_⟩
    have hxq : x ^ Ideal.absNorm 𝔭.asIdeal - x ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, sub_eq_zero, hq, ← hcq]
      exact FiniteField.pow_card _
    have hsum := P.add_mem (hfrob x) hxq
    rwa [sub_add_sub_cancel] at hsum
  · intro h1
    subst h1
    have hall : ∀ y : 𝓞 R ⧸ P, y ^ Fintype.card (𝓞 F ⧸ 𝔭.asIdeal) = y := by
      intro y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hx := hfrob x
      rw [one_smul, ← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, sub_eq_zero, hq] at hx
      exact hx.symm
    have hroots := Polynomial.card_le_degree_of_subset_roots
      (p := (X ^ Fintype.card (𝓞 F ⧸ 𝔭.asIdeal) - X : (𝓞 R ⧸ P)[X])) (Z := Finset.univ)
      (fun y _ => by
        rw [Polynomial.mem_roots (Polynomial.X_pow_sub_X_ne_zero hq1)]
        simp [hall y])
    rw [Finset.card_univ, Polynomial.natDegree_X_pow_sub_X hq1, hcard] at hroots
    have hle := (Nat.pow_le_pow_iff_right hq1).mp (hroots.trans (pow_one _).symm.le)
    have hpos : 0 < Module.finrank (𝓞 F ⧸ 𝔭.asIdeal) (𝓞 R ⧸ P) := by
      rcases Nat.eq_zero_or_pos (Module.finrank (𝓞 F ⧸ 𝔭.asIdeal) (𝓞 R ⧸ P)) with h0 | h0
      · rw [h0, mul_zero] at hcount
        omega
      · exact h0
    omega

set_option autoImplicit false in
private theorem eq_one_iff_forall_char_eq_one_of_finite_commutative {G : Type} [Group G] [Finite G]
    [IsMulCommutative G] (σ : G) : σ = 1 ↔ ∀ χ : G →* ℂˣ, χ σ = 1 := by
  refine ⟨fun h χ => by rw [h, map_one], fun h => ?_⟩
  letI : CommGroup G := { (inferInstance : Group G) with mul_comm := mul_comm' }
  by_contra hσ
  haveI : NeZero (Monoid.exponent G) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨χ, hχ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G ℂ hσ
  exact hχ (h χ)

set_option autoImplicit false in
private theorem heckeIdeal_asIdeal_eq_heckeVal {F R : Type} [Field F] [NumberField F]
    [Field R] [NumberField R] [Algebra F R] (χ : Gal(R/F) →* ℂˣ) (𝔭 : HeightOneSpectrum (𝓞 F)) :
    _root_.GlobalTheory.NT.heckeIdeal R χ 𝔭.asIdeal = _root_.GlobalTheory.NT.heckeVal R χ 𝔭 := by
  unfold _root_.GlobalTheory.NT.heckeIdeal
  have hirr : ∀ 𝔮 : HeightOneSpectrum (𝓞 F), Irreducible (Associates.mk 𝔮.asIdeal) := fun 𝔮 =>
    Associates.irreducible_mk.mpr (Ideal.prime_of_isPrime 𝔮.ne_bot 𝔮.isPrime).irreducible
  rw [finprod_eq_single _ 𝔭]
  · rw [Associates.count_self (hirr 𝔭), pow_one]
  · intro 𝔮 h𝔮
    rw [Associates.count_eq_zero_of_ne (hirr 𝔮) (hirr 𝔭), pow_zero]
    intro h
    exact h𝔮 (HeightOneSpectrum.ext (associated_iff_eq.mp (Associates.mk_eq_mk_iff_associated.mp h)))

set_option autoImplicit false in
private theorem false_of_ringHom_real_of_isTotallyComplex {F : Type} [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F]
    (φ : F →+* ℝ) : False := by
  have h := IsTotallyComplex.isComplex (InfinitePlace.mk ((algebraMap ℝ ℂ).comp φ))
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff] at h
  apply h
  rw [ComplexEmbedding.isReal_iff]
  ext x
  simp [ComplexEmbedding.conjugate_coe_eq]

set_option autoImplicit false in
theorem _root_.GlobalTheory.FieldSize.RaySplit.ncard_eq_finrank_iff : ∀ (K R : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field R] [NumberField R]
    [Algebra K R] [IsAbelianGalois K R] (n : ℕ), 0 < n → _root_.GlobalTheory.FieldSize.IsRay R (Ideal.span {(n : 𝓞 K)}) →
    ∀ 𝔭 : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∉ 𝔭.asIdeal →
      ({Q : HeightOneSpectrum (𝓞 R) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 R)) = 𝔭.asIdeal}.ncard = Module.finrank K R ↔
        ∃ π : 𝓞 K, 𝔭.asIdeal = Ideal.span {π} ∧ π - 1 ∈ Ideal.span {(n : 𝓞 K)}) := by
  intro K R _ _ _ _ _ _ _ n _ hray 𝔭 hn𝔭
  obtain ⟨hunr, -, hart⟩ := hray
  have hnot : ¬ 𝔭.asIdeal ∣ Ideal.span {(n : 𝓞 K)} := by
    rw [Ideal.dvd_span_singleton]
    exact hn𝔭
  have hcop : IsCoprime 𝔭.asIdeal (Ideal.span {(n : 𝓞 K)}) := by
    rw [Ideal.isCoprime_iff_sup_eq]
    by_contra h
    have heq := 𝔭.isMaximal.eq_of_le h le_sup_left
    apply hn𝔭
    rw [heq]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hu := hunr 𝔭 hnot
  obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.NT.exists_isFrob R 𝔭
  rw [_root_.GlobalTheory.FieldSize.RaySplit.ncard_eq_primesOver,
    ncard_primesOver_eq_finrank_iff_frob_eq_one hu hσ]
  have hchar : σ = 1 ↔
      ∀ χ : Gal(R/K) →* ℂˣ, _root_.GlobalTheory.NT.heckeIdeal R χ 𝔭.asIdeal = 1 := by
    refine (eq_one_iff_forall_char_eq_one_of_finite_commutative σ).trans (forall_congr' fun χ => ?_)
    rw [heckeIdeal_asIdeal_eq_heckeVal, _root_.GlobalTheory.NT.heckeVal_of_unramIn R χ hu hσ,
      Units.val_eq_one]
  rw [hchar, hart 𝔭.asIdeal 𝔭.ne_bot hcop]
  constructor
  · rintro ⟨α, β, ⟨-, hβ, -, hβcop, hαβ, -⟩, hI⟩
    have hdvd : β ∣ α := by
      rw [← Ideal.span_singleton_le_span_singleton, ← hI]
      exact Submodule.mul_le.mpr fun a _ b hb => Ideal.mul_mem_left _ a hb
    obtain ⟨π, rfl⟩ := hdvd
    refine ⟨π, ?_, ?_⟩
    · have hβ0 : Ideal.span {β} ≠ 0 := by
        rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      apply mul_right_cancel₀ hβ0
      rw [hI, ← Ideal.span_singleton_mul_span_singleton, mul_comm]
    · rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one, Submodule.mem_sup] at hβcop
      obtain ⟨u, hu', v, hv, huv⟩ := hβcop
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hu'
      have key : π - 1 = c * (β * π - β) + (π - 1) * v := by
        linear_combination (1 - π) * huv
      rw [key]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hαβ) (Ideal.mul_mem_left _ _ hv)
  · rintro ⟨π, hπ, hπ1⟩
    refine ⟨π, 1, ⟨?_, one_ne_zero, ?_, ?_, hπ1, fun φ => (false_of_ringHom_real_of_isTotallyComplex φ).elim⟩, ?_⟩
    · rintro rfl
      exact 𝔭.ne_bot (hπ.trans (Ideal.span_singleton_eq_bot.mpr rfl))
    · rw [← hπ]
      exact hcop
    · rw [Ideal.span_singleton_one, Ideal.isCoprime_iff_sup_eq]
      exact top_sup_eq _
    · rw [Ideal.span_singleton_one, Ideal.mul_top, hπ]

end GlobalTheory.FieldSize.RaySplit

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.HeightProofs.SzFieldRangeEmbedding
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField nonZeroDivisors

namespace GlobalTheory.FieldSize

theorem sz_fieldRange_embedding (K : Type) [Field K] [NumberField K] (φ : K →+* ℂ) :
    Sz φ.toRatAlgHom.fieldRange (Real.log (Module.finrank ℚ K))
      (Real.log |((discr K : ℤ) : ℝ)| / Module.finrank ℚ K) := by
  let e : K ≃ₐ[ℚ] φ.toRatAlgHom.fieldRange := AlgEquiv.ofInjectiveField φ.toRatAlgHom
  have hfd : FiniteDimensional ℚ φ.toRatAlgHom.fieldRange := e.toLinearEquiv.finiteDimensional
  refine ⟨hfd, ?_⟩
  let _ : NumberField φ.toRatAlgHom.fieldRange := NumberField.mk
  have h1 : Module.finrank ℚ φ.toRatAlgHom.fieldRange = Module.finrank ℚ K := e.toLinearEquiv.finrank_eq.symm
  have h2 : discr φ.toRatAlgHom.fieldRange = discr K := (NumberField.discr_eq_discr_of_algEquiv K e).symm
  rw [h1, h2]
  exact ⟨le_rfl, le_rfl⟩

end GlobalTheory.FieldSize
end
