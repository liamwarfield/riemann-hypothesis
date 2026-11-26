module

public import Formalism.HermitianCurvature.StatementWd
public import Formalism.HermitianCurvature.PrimeToDifferent
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.RealPowerIdentities
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockStartPoints
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FinitePointSets
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.FiniteClassesPositiveSums
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.Interlace
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.AntidiagMulDiagonal

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PositionInsertionDiagonalCompat
namespace Formalism.FourierDecayAlt.P.Wd1

open Matrix Formalism.FourierDecayAlt.Wd

variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]

theorem cond_iff (a : S) (i j : Fin 2) (x y : Ix S) :
    (x a = i ∧ y a = j ∧ ∀ b, b ≠ a → x b = y b) ↔ (x a = i ∧ y = Function.update x a j) := by
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_⟩
    funext b
    by_cases hb : b = a
    · subst hb; simp [h2]
    · simp [Function.update_apply, hb, h3 b hb]
  · rintro ⟨h1, rfl⟩
    exact ⟨h1, by simp, fun b hb => by simp [Function.update_apply, hb]⟩

theorem eU_apply (a : S) (i j : Fin 2) (x y : Ix S) :
    (eU a i j : SlopeTestRemainingChoices S A) x y = if x a = i ∧ y = Function.update x a j then 1 else 0 := by
  simp only [eU, Matrix.of_apply]
  exact if_congr (cond_iff a i j x y) rfl rfl

theorem eU_mul_apply (a : S) (i j : Fin 2) (B : SlopeTestRemainingChoices S A) (x y : Ix S) :
    ((eU a i j : SlopeTestRemainingChoices S A) * B) x y = if x a = i then B (Function.update x a j) y else 0 := by
  simp only [Matrix.mul_apply, eU_apply, ite_mul, one_mul, zero_mul]
  by_cases hx : x a = i <;> simp [hx]

theorem eU_mul_eU (a : S) (i j k l : Fin 2) :
    (eU a i j : SlopeTestRemainingChoices S A) * eU a k l = if j = k then eU a i l else 0 := by
  ext x y
  rw [eU_mul_apply]
  by_cases hx : x a = i <;> by_cases hjk : j = k <;> simp [hx, hjk, eU_apply, Function.update_idem]

theorem sum_eU_diag (a : S) : ∑ i, (eU a i i : SlopeTestRemainingChoices S A) = 1 := by
  ext x y
  rw [Matrix.sum_apply, Finset.sum_eq_single (x a)]
  · rw [eU_apply, Matrix.one_apply, Function.update_eq_self]
    by_cases h : x = y
    · subst h; simp
    · have h' : ¬ y = x := fun e => h e.symm
      simp [h, h']
  · intro i _ hi
    rw [eU_apply, if_neg]
    rintro ⟨h, _⟩
    exact hi h.symm
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem eU_comm_of_ne {a c : S} (hc : c ≠ a) (i j k l : Fin 2) :
    Commute (eU c i j : SlopeTestRemainingChoices S A) (eU a k l) := by
  show (eU c i j : SlopeTestRemainingChoices S A) * eU a k l = eU a k l * eU c i j
  ext x y
  rw [eU_mul_apply, eU_mul_apply, eU_apply, eU_apply]
  by_cases hxc : x c = i <;> by_cases hxa : x a = k <;>
    simp [Function.update_apply, hc, Ne.symm hc, hxc, hxa, Function.update_comm hc j l x]

theorem star_eU [StarRing A] (a : S) (i j : Fin 2) :
    star (eU a i j : SlopeTestRemainingChoices S A) = eU a j i := by
  ext x y
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  simp only [eU, Matrix.of_apply]
  rw [apply_ite star, star_one, star_zero]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h1, fun b hb => (h3 b hb).symm⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h2, h1, fun b hb => (h3 b hb).symm⟩

theorem ins_mul (a : S) (M N : M2 (SlopeTestRemainingChoices S A)) (hM : FreeOf2 a M) :
    ins a (M * N) = ins a M * ins a N := by
  have key : ∀ i j k l : Fin 2, (eU a i j : SlopeTestRemainingChoices S A) * M i j * (eU a k l * N k l) =
      if j = k then eU a i l * (M i j * N k l) else 0 := by
    intro i j k l
    have e1 : (eU a i j : SlopeTestRemainingChoices S A) * M i j * (eU a k l * N k l) =
        eU a i j * (M i j * eU a k l) * N k l := by
      simp only [mul_assoc]
    rw [e1, ← (hM i j k l).eq]
    have e2 : (eU a i j : SlopeTestRemainingChoices S A) * (eU a k l * M i j) * N k l =
        (eU a i j * eU a k l) * (M i j * N k l) := by
      simp only [mul_assoc]
    rw [e2, eU_mul_eU]
    split_ifs <;> simp
  simp only [ins, Fin.sum_univ_two, Matrix.mul_apply, add_mul, mul_add, key]
  simp
  abel

theorem ins_star [StarRing A] (a : S) (M : M2 (SlopeTestRemainingChoices S A)) (hM : FreeOf2 a M) :
    star (ins a M) = ins a Mᴴ := by
  have key : ∀ i j : Fin 2, star ((eU a i j : SlopeTestRemainingChoices S A) * M i j) = eU a j i * star (M i j) := by
    intro i j
    have h := congrArg star (hM i j i j).eq
    rw [star_mul, star_mul, star_eU] at h
    rw [star_mul, star_eU]
    exact h
  simp only [ins, Fin.sum_univ_two, star_add, key, Matrix.conjTranspose_apply]
  abel

theorem ins_one (a : S) : ins a (1 : M2 (SlopeTestRemainingChoices S A)) = 1 := by
  simp only [ins, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  exact sum_eU_diag a

theorem insert_diagonal_extract (a : S) (b : SlopeTestRemainingChoices S A) : ins a (d0 b) = b := by
  simp only [ins, d0, Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    if_true]
  rw [← Finset.sum_mul, sum_eU_diag, one_mul]

theorem ins_free {a c : S} (hc : c ≠ a) (M : M2 (SlopeTestRemainingChoices S A)) (hM : FreeOf2 c M) :
    FreeOf c (ins a M) := by
  intro k l
  unfold ins
  apply Commute.sum_right
  intro i _
  apply Commute.sum_right
  intro j _
  exact (eU_comm_of_ne hc k l i j).mul_right (hM i j k l)

theorem ins_comm (a : S) (M : M2 (SlopeTestRemainingChoices S A)) (b : SlopeTestRemainingChoices S A) (hb : FreeOf a b)
    (hbM : ∀ i j, Commute b (M i j)) : Commute b (ins a M) := by
  unfold ins
  apply Commute.sum_right
  intro i _
  apply Commute.sum_right
  intro j _
  exact (hb i j).symm.mul_right (hbM i j)

end Formalism.FourierDecayAlt.P.Wd1

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.Wd

theorem position_insertion_mul_compat : Formalism.FourierDecayAlt.Wd.InsMul := by
  intro K A S _ _ _ _ _ _ _ _ a M N hM
  exact Wd1.ins_mul a M N hM

theorem position_insertion_star_compat : Formalism.FourierDecayAlt.Wd.InsStar := by
  intro K A S _ _ _ _ _ _ _ _ a M hM
  exact Wd1.ins_star a M hM

theorem position_insertion_diagonal_compat : Formalism.FourierDecayAlt.Wd.InsDiag := by
  intro K A S _ _ _ _ _ _ _ _ a b
  exact ⟨Wd1.ins_one a, Wd1.insert_diagonal_extract a b⟩

theorem position_insertion_free_compat : Formalism.FourierDecayAlt.Wd.InsFree := by
  intro K A S _ _ _ _ _ _ _ _ a M
  exact ⟨fun c hc hM => Wd1.ins_free hc M hM, fun b hb hbM => Wd1.ins_comm a M b hb hbM⟩

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.PeriodLatticeFactsSplitOfGeneral
namespace Formalism.FourierDecayAlt.P.S6x1

open Formalism.FourierDecayAlt.S6
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors

theorem mem_twLat (E : Type) [Field E] [NumberField E] [IsCMField E] (A B : FI E) (s : ℕ) (t : E) :
    t ∈ twLat E A B s ↔ t ∈ A ∧ t - (-1) ^ s * complexConj E t ∈ B := by
  unfold twLat
  rw [Submodule.mem_inf, Submodule.mem_comap]
  have : ((LinearMap.id : E →ₗ[ℤ] E) - ((-1 : ℤ) ^ s) • conjZ E) t
      = t - (-1) ^ s * complexConj E t := by
    rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, zsmul_eq_mul]
    push_cast
    rfl
  rw [this]; rfl

theorem conj_real (E : Type) [Field E] [NumberField E] [IsCMField E]
    (a : 𝓞 (maximalRealSubfield E)) :
    complexConj E (algebraMap (𝓞 (maximalRealSubfield E)) E a)
      = algebraMap (𝓞 (maximalRealSubfield E)) E a :=
  complexConj_apply_eq_self E (a : maximalRealSubfield E)

theorem smul_mem_FI (E : Type) [Field E] [NumberField E] [IsCMField E] (A : FI E)
    (a : 𝓞 (maximalRealSubfield E)) (t : E) (ht : t ∈ A) :
    algebraMap (𝓞 (maximalRealSubfield E)) E a * t ∈ A := by
  have := (A : Submodule (𝓞 E) E).smul_mem (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E) a) ht
  rw [Algebra.smul_def] at this
  exact this

end Formalism.FourierDecayAlt.P.S6x1

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.S6 Formalism.FourierDecayAlt.P.S6x1
open NumberField NumberField.IsCMField Module
open scoped nonZeroDivisors

theorem unramRelative : Formalism.FourierDecayAlt.S6.UnramRelative := by
  intro E _ _ _ hU
  have h := differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 (maximalRealSubfield E)) (𝓞 E)
  unfold Unram at hU
  have h0 : (differentIdeal ℤ (𝓞 (maximalRealSubfield E))).map
      (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) ≠ ⊥ := by
    rw [← hU]; exact differentIdeal_ne_bot
  have h1 : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := by
    rw [hU] at h
    have h2 : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) *
        (differentIdeal ℤ (𝓞 (maximalRealSubfield E))).map
          (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) =
        1 * (differentIdeal ℤ (𝓞 (maximalRealSubfield E))).map
          (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) := by rw [one_mul]; exact h.symm
    simpa using mul_right_cancel₀ h0 h2
  refine ⟨h1, fun g => ?_⟩
  unfold UnramAbove
  rw [h1, Ideal.isCoprime_iff_sup_eq]; simp

theorem degreeFacts_statement : Formalism.FourierDecayAlt.S6.DegreeFacts := by
  intro E _ _ _
  have h2 : finrank (maximalRealSubfield E) E = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have h3 := finrank_mul_finrank ℚ (maximalRealSubfield E) E
  have h4 : 0 < finrank ℚ (maximalRealSubfield E) := finrank_pos
  rw [h2] at h3
  refine ⟨by unfold deg; omega, ?_, h4⟩
  have h5 := IsTotallyComplex.finrank E
  have h6 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E
  have h7 : InfinitePlace.nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
  unfold deg
  omega

theorem localAwayFromLevel : Formalism.FourierDecayAlt.S6.LocOrdinary := by
  intro E _ _ _ g k ν P hP hg
  have hg0 : (g : E) ≠ 0 := by
    intro h
    apply hg
    have : g = 0 := by exact_mod_cast h
    simp [this]
  have key : ∀ (k k' : ℤ) (t : E), t ∈ locAt E P (zsub E (idl E g k ν)) →
      t ∈ locAt E P (zsub E (idl E g k' ν)) := by
    intro k k' t
    rintro ⟨a, ha, h⟩
    obtain ⟨n, hn⟩ : ∃ n : ℕ, k' ≤ k + n := ⟨(k' - k).toNat, by omega⟩
    obtain ⟨m, hm⟩ : ∃ m : ℕ, k + n = k' + m := ⟨(k + n - k').toNat, by omega⟩
    refine ⟨(g : 𝓞 (maximalRealSubfield E)) ^ n * a,
      fun hh => (hP.mem_or_mem hh).elim (fun h' => hg (hP.mem_of_pow_mem _ h')) ha, ?_⟩
    change _ ∈ idl E g k ν at h
    show _ ∈ idl E g k' ν
    unfold idl at h ⊢
    rw [mul_comm, FractionalIdeal.mem_singleton_mul] at h ⊢
    obtain ⟨z, hz, hh⟩ := h
    refine ⟨(g : E) ^ m * z, ?_, ?_⟩
    · have := (dd E ^ ν : FI E).coeToSubmodule.smul_mem ((g : 𝓞 E) ^ m) hz
      rw [Algebra.smul_def] at this
      simpa using this
    · rw [map_mul, mul_assoc, hh, map_pow, map_natCast, ← mul_assoc, ← mul_assoc, ← zpow_natCast,
        ← zpow_natCast, ← zpow_add₀ hg0, ← zpow_add₀ hg0, add_comm (n : ℤ) k, hm]
  ext t
  exact ⟨key _ _ t, key _ _ t⟩

theorem localTwistedLattice : Formalism.FourierDecayAlt.S6.LocTw := by
  intro E _ _ _ A B s P hP t
  constructor
  · rintro ⟨a, ha, h⟩
    rw [mem_twLat] at h
    refine ⟨⟨a, ha, h.1⟩, ⟨a, ha, ?_⟩⟩
    have := h.2
    rw [map_mul, conj_real] at this
    show _ ∈ B
    convert this using 1; ring
  · rintro ⟨⟨a, ha, h1⟩, ⟨b, hb, h2⟩⟩
    refine ⟨a * b, fun h => (hP.mem_or_mem h).elim ha hb, ?_⟩
    rw [mem_twLat]
    constructor
    · have := smul_mem_FI E A b _ h1
      rw [map_mul]; convert this using 1; ring
    · have := smul_mem_FI E B a _ h2
      rw [map_mul, map_mul, map_mul, conj_real, conj_real]; convert this using 1; ring

theorem scaledIdealNorm : Formalism.FourierDecayAlt.S6.NormIdl := by
  intro E _ _ _ g k ν hg
  have hdeg := degreeFacts_statement E
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hD0 : (0 : ℝ) ≤ ((|discr E| : ℤ) : ℝ) := by exact_mod_cast abs_nonneg _
  have hrd : 0 < rd E := by
    unfold rd
    apply Real.rpow_pos_of_pos
    have : (0 : ℤ) < |discr E| := abs_pos.2 (discr_ne_zero E)
    exact_mod_cast this
  have hD : ((|discr E| : ℤ) : ℝ) = rd E ^ (2 * deg E) := by
    unfold rd
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD0, hdeg.1]
    have : ((2 * deg E : ℕ) : ℝ) ≠ 0 := by
      have := hdeg.2.2
      positivity
    rw [inv_mul_cancel₀ this, Real.rpow_one]
  have h1 : FractionalIdeal.absNorm (dd E) = ((|discr E| : ℤ) : ℚ) := by
    unfold dd
    rw [FractionalIdeal.coeIdeal_absNorm, absNorm_differentIdeal E, Nat.cast_natAbs]
  have h2 : FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 E)⁰ ((g : E) ^ k))
      = ((g : ℚ) ^ (2 * deg E)) ^ k := by
    rw [FractionalIdeal.absNorm_span_singleton,
      show (g : E) ^ k = algebraMap ℚ E ((g : ℚ) ^ k) by rw [map_zpow₀, map_natCast],
      Algebra.norm_algebraMap, hdeg.1, abs_of_nonneg (by positivity)]
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
  unfold idl
  rw [map_mul, map_zpow₀, h1, h2]
  push_cast
  have hD' : (|(discr E : ℝ)|) = rd E ^ (2 * deg E) := by rw [← hD]; push_cast; rfl
  rw [hD']
  have : (rd E ^ (2 * deg E)) ^ ν * ((g : ℝ) ^ (2 * deg E)) ^ k
      = (((g : ℝ) ^ k * rd E ^ ν) ^ deg E) ^ 2 := by
    rw [← zpow_natCast (rd E), ← zpow_natCast (g : ℝ), ← zpow_mul, ← zpow_mul, ← pow_mul, mul_pow,
      ← zpow_natCast (((g : ℝ) ^ k)), ← zpow_natCast ((rd E ^ ν)), ← zpow_mul, ← zpow_mul, mul_comm]
    congr 2 <;> (push_cast; ring)
  rw [this, Real.sqrt_sq (by positivity)]

theorem twistedLatticeBetween : Formalism.FourierDecayAlt.S6.Between := by
  intro E _ _ _ A B s hBA hB
  refine ⟨fun t ht => ?_, fun t ht => ((mem_twLat E A B s t).1 ht).1⟩
  rw [mem_twLat]
  refine ⟨hBA ht, ?_⟩
  have h1 : complexConj E t ∈ B := hB t ht
  have h2 : (-1 : E) ^ s * complexConj E t ∈ B := by
    rcases neg_one_pow_eq_or E s with h | h <;> rw [h]
    · simpa using h1
    · rw [neg_one_mul]; exact B.coeToSubmodule.neg_mem h1
  exact B.coeToSubmodule.sub_mem ht h2

theorem dualIdealEqLiftIdeal : Formalism.FourierDecayAlt.S6.IdealsMatch := by
  intro E _ _ _ g r i s
  refine ⟨?_, ?_, ?_⟩
  · unfold dualIdl liftIdl nuBlock; congr 1; ring
  · unfold dualIdl nuBlock; congr 1; ring
  · unfold nuBlock; ring

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.KroneckerEmbedMulApply
namespace Formalism.FourierDecayAlt.P.Wd2

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd

section Units

variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]

end Units

section Entries

variable {K B : Type} [CommRing K] [Ring B] [Algebra K B]

end Entries

section Slots

variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

end Slots

section Start

variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

theorem io_smul (c : K) (x : A) : (io (c • x) : SlopeTestRemainingChoices S A) = c • io x := by
  ext x y
  simp only [io, Matrix.scalar_apply, Matrix.smul_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem liftMatrix_eq_map_scalar (M : M2 A) : (lift0 M : M2 (SlopeTestRemainingChoices S A)) = M.map (Matrix.scalar (Ix S)) := rfl

theorem firstEmbed_liftMatrix (M : M2 A) :
    E1 (lift0 M : M2 (SlopeTestRemainingChoices S A)) = (E1 M).map (Matrix.scalar (Ix S)) := by
  ext p q
  simp only [E1, lift0, io, Matrix.of_apply, Matrix.map_apply, Matrix.map_apply]
  split_ifs <;> simp

theorem secondEmbed_liftMatrix (M : M2 A) :
    E2 (lift0 M : M2 (SlopeTestRemainingChoices S A)) = (E2 M).map (Matrix.scalar (Ix S)) := by
  ext p q
  simp only [E2, lift0, io, Matrix.of_apply, Matrix.map_apply]
  split_ifs <;> simp

theorem core_map (c : K) :
    c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A) =
      (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A).map (Matrix.scalar (Ix S)) := by
  have hsc : ∀ x : A, Matrix.scalar (Ix S) (c • x) = c • Matrix.scalar (Ix S) x := io_smul c
  ext p q : 1
  simp only [Pf, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.of_apply]
  split_ifs <;> simp [map_sub, map_neg, hsc]

theorem J_map : YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) = (YangianSpanCharacter.T.J A).map (Matrix.scalar (Ix S)) := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [YangianSpanCharacter.T.J] <;>
    (try (ext x y; simp only [Matrix.neg_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.smul_apply]; split_ifs <;> simp))

theorem smulJ_map (c : K) :
    algebraMap K (SlopeTestRemainingChoices S A) c • YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) =
      (algebraMap K A c • YangianSpanCharacter.T.J A).map (Matrix.scalar (Ix S)) := by
  have hsc : ∀ x : A, Matrix.scalar (Ix S) (c • x) = c • Matrix.scalar (Ix S) x := io_smul c
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [YangianSpanCharacter.T.J, Algebra.algebraMap_eq_smul_one, hsc] <;>
    (try (ext x y; simp only [Matrix.neg_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.smul_apply]; split_ifs <;> simp))

theorem rtt_lift0 (M N : M2 A) (c : K)
    (H : (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) * E1 M * E2 N =
      E2 N * E1 M * (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A)) :
    (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A)) *
        E1 (lift0 M) * E2 (lift0 N) =
      E2 (lift0 N) * E1 (lift0 M) *
        (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A)) := by
  rw [core_map, firstEmbed_liftMatrix, secondEmbed_liftMatrix, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul,
    ← Matrix.map_mul, H]

theorem det_lift0 (M M' : M2 A) (c : K) (H : M'ᵀ * YangianSpanCharacter.T.J A * M = algebraMap K A c • YangianSpanCharacter.T.J A) :
    (lift0 M' : M2 (SlopeTestRemainingChoices S A))ᵀ * YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * lift0 M = algebraMap K (SlopeTestRemainingChoices S A) c • YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) := by
  rw [smulJ_map, liftMatrix_eq_map_scalar, liftMatrix_eq_map_scalar, J_map, ← Matrix.transpose_map, ← Matrix.map_mul,
    ← Matrix.map_mul, H]

theorem det_lift0' (M M' : M2 A) (c : K) (H : M * YangianSpanCharacter.T.J A * M'ᵀ = algebraMap K A c • YangianSpanCharacter.T.J A) :
    (lift0 M : M2 (SlopeTestRemainingChoices S A)) * YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * (lift0 M')ᵀ = algebraMap K (SlopeTestRemainingChoices S A) c • YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) := by
  rw [smulJ_map, liftMatrix_eq_map_scalar, liftMatrix_eq_map_scalar, J_map, ← Matrix.transpose_map, ← Matrix.map_mul,
    ← Matrix.map_mul, H]

theorem liftMatrix_conjTranspose [StarRing A] (M : M2 A) :
    (lift0 M : M2 (SlopeTestRemainingChoices S A))ᴴ = lift0 Mᴴ := by
  ext i j x y
  simp [lift0, io, Matrix.conjTranspose_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    Matrix.star_apply]
  split_ifs <;> simp_all [@eq_comm _ y x]

theorem d0_one : (d0 (1 : SlopeTestRemainingChoices S A)) = 1 := by
  unfold d0
  exact Matrix.diagonal_one

end Start

end Formalism.FourierDecayAlt.P.Wd2

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd

theorem initial_module_structure : Formalism.FourierDecayAlt.Wd.StartModule := by
  intro K A S _ _ _ _ _ _ _ _ QQ q hS
  refine ⟨star_one _, fun Y _ hY => ?_, fun Y _ Y' _ => ?_, fun Y _ _ => ?_, hS.q_real⟩
  · rw [Formalism.FourierDecayAlt.P.Wd2.d0_one, one_mul, Formalism.FourierDecayAlt.P.Wd2.liftMatrix_conjTranspose, hS.herm Y hY]
  · exact Formalism.FourierDecayAlt.P.Wd2.rtt_lift0 (QQ Y') (QQ Y) (Y' - Y) (hS.rtt Y Y')
  · exact ⟨Formalism.FourierDecayAlt.P.Wd2.det_lift0 (QQ Y) (QQ (Y + 1)) (q Y) (hS.det Y).1,
      Formalism.FourierDecayAlt.P.Wd2.det_lift0' (QQ Y) (QQ (Y + 1)) (q Y) (hS.det Y).2⟩

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.SecondEmbedMulFirstEmbedApply
namespace Formalism.FourierDecayAlt.P.Wd3

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd

section

variable {K A S : Type} [Field K] [StarRing K] [Ring A] [StarRing A] [Algebra K A]
  [Fintype S] [DecidableEq S]

theorem eU_mul (a : S) (i j k l : Fin 2) :
    (eU a i j : SlopeTestRemainingChoices S A) * eU a k l = if j = k then eU a i l else 0 := by
  ext x y
  rw [Matrix.mul_apply, Finset.sum_eq_single (Function.update x a j)]
  · by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl]
      simp only [eU, Matrix.of_apply]
      by_cases hx : x a = i <;> by_cases hy : y a = l <;> by_cases hxy : ∀ b, b ≠ a → x b = y b <;>
        simp (config := {contextual := true}) [Function.update_apply, hx, hy, hxy]
    · rw [if_neg hjk]
      simp [eU, Function.update_apply, hjk]
  · intro z _ hz
    simp only [eU, Matrix.of_apply]
    rw [if_neg, zero_mul]
    rintro ⟨_, h2, h3⟩
    apply hz
    funext b
    by_cases hb : b = a
    · subst hb
      simp [h2]
    · rw [Function.update_of_ne hb]
      exact (h3 b hb).symm
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem mul_ins (a : S) (m : SlopeTestRemainingChoices S A) (N : M2 (SlopeTestRemainingChoices S A)) (hm : FreeOf a m) :
    m * ins a N = ∑ r, ∑ s, eU a r s * (m * N r s) := by
  have hm' : ∀ i j, Commute (eU a i j) m := hm
  rw [ins, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← mul_assoc, ← (hm' r s).eq, mul_assoc]

theorem ins_mul (a : S) (m : SlopeTestRemainingChoices S A) (N : M2 (SlopeTestRemainingChoices S A)) :
    ins a N * m = ∑ r, ∑ s, eU a r s * (N r s * m) := by
  rw [ins, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_assoc]

theorem eU_mul_ins (a : S) (k i : Fin 2) (m : SlopeTestRemainingChoices S A) (N : M2 (SlopeTestRemainingChoices S A)) (hm : FreeOf a m) :
    eU a k i * m * ins a N = ∑ s, eU a k s * (m * N i s) := by
  rw [mul_assoc, mul_ins a m N hm, Finset.mul_sum, Finset.sum_eq_single i]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← mul_assoc, eU_mul, if_pos rfl]
  · intro r _ hr
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [← mul_assoc, eU_mul, if_neg (Ne.symm hr), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem ins_mul_eU (a : S) (j k : Fin 2) (m : SlopeTestRemainingChoices S A) (N : M2 (SlopeTestRemainingChoices S A)) (hm : FreeOf a m)
    (hN : FreeOf2 a N) :
    ins a N * (m * eU a j k) = ∑ r, eU a r k * (N r j * m) := by
  have hm' : ∀ i j, Commute (eU a i j) m := hm
  have h1 : ∀ r s, FreeOf a (N r s) := hN
  have hN' : ∀ r s i j, Commute (eU a i j) (N r s) := fun r s => h1 r s
  rw [← mul_assoc, ins_mul a m N, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_mul, Finset.sum_eq_single j]
  · have hc : Commute (eU a j k) (N r j * m) := (hN' r j j k).mul_right (hm' j k)
    rw [mul_assoc, ← hc.eq, ← mul_assoc, eU_mul, if_pos rfl]
  · intro s _ hs
    have hc : Commute (eU a j k) (N r s * m) := (hN' r s j k).mul_right (hm' j k)
    rw [mul_assoc, ← hc.eq, ← mul_assoc, eU_mul, if_neg hs, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem firstEmbed_mul_secondEmbed_apply {B : Type} [Ring B] (M N : M2 B) (i r j s : Fin 2) :
    (E1 M * E2 N) (i, r) (j, s) = M i j * N r s := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [E1, E2, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem secondEmbed_mul_firstEmbed_apply {B : Type} [Ring B] (M N : M2 B) (i r j s : Fin 2) :
    (E2 N * E1 M) (i, r) (j, s) = N r s * M i j := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [E1, E2, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem Pf_mul {B : Type} [Ring B] (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (i r : Fin 2)
    (y : Fin 2 × Fin 2) : (Pf B * X) (i, r) y = X (r, i) y := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [Pf, ite_and, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem mul_Pf {B : Type} [Ring B] (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (j s : Fin 2)
    (x : Fin 2 × Fin 2) : (X * Pf B) x (j, s) = X x (s, j) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [Pf, ite_and, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem rtt_entry {B : Type} [Ring B] [Algebra K B] (M N : M2 B) (D : K)
    (h : (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B) * E1 M * E2 N =
      E2 N * E1 M * (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B))
    (i r j s : Fin 2) :
    D • (M i j * N r s) - M r j * N i s = D • (N r s * M i j) - N r j * M i s := by
  have h' := congrFun (congrFun h (i, r)) (j, s)
  rw [mul_assoc, sub_mul, Matrix.smul_mul, Matrix.one_mul, mul_sub, Matrix.mul_smul, Matrix.mul_one] at h'
  simp only [Matrix.sub_apply, Matrix.smul_apply, Pf_mul, mul_Pf, firstEmbed_mul_secondEmbed_apply, secondEmbed_mul_firstEmbed_apply] at h'
  exact h'

theorem plus_core (a : S) (M N : M2 (SlopeTestRemainingChoices S A)) (D : K) (hM : FreeOf2 a M) (hN : FreeOf2 a N)
    (h : ∀ i r j s, D • (M i j * N r s) - M r j * N i s = D • (N r s * M i j) - N r j * M i s) :
    (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) * M * d0 (ins a N) =
      d0 (ins a N) * M * (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) := by
  have hM' : ∀ i j, FreeOf a (M i j) := hM
  refine Matrix.ext fun i j => ?_
  have key : ∀ r s, D • (eU a r s * (M i j * N r s)) - eU a r s * (M r j * N i s) =
      D • (eU a r s * (N r s * M i j)) - eU a r s * (N r j * M i s) := fun r s => by
    have := congrArg (eU a r s * ·) (h i r j s)
    simp only [mul_sub, mul_smul_comm] at this
    exact this
  have hL : (((D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) * M * d0 (ins a N) : M2 (SlopeTestRemainingChoices S A))) i j =
      D • (M i j * ins a N) - ∑ k, eU a k i * M k j * ins a N := by
    rw [sub_mul, sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.sub_apply,
      Matrix.smul_apply, d0, Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul]
    rfl
  have hR : ((d0 (ins a N) * M * (D • (1 : M2 (SlopeTestRemainingChoices S A)) - P0 a) : M2 (SlopeTestRemainingChoices S A))) i j =
      D • (ins a N * M i j) - ∑ k, ins a N * (M i k * eU a j k) := by
    rw [mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.sub_apply, Matrix.smul_apply, d0,
      Matrix.diagonal_mul, Matrix.mul_apply]
    simp only [Matrix.diagonal_mul, mul_assoc]
    rfl
  rw [hL, hR, mul_ins a _ N (hM' i j), ins_mul,
    Finset.sum_congr rfl fun k _ => eU_mul_ins a k i (M k j) N (hM' k j),
    Finset.sum_congr rfl fun k _ => ins_mul_eU a j k (M i k) N (hM' i k) hN,
    Finset.sum_comm (f := fun k r => eU a r k * (N r j * M i k)),
    Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => key r s

theorem minus_core (b : S) (M N : M2 (SlopeTestRemainingChoices S A)) (d : K) (hM : FreeOf2 b M) (hN : FreeOf2 b N)
    (h : ∀ i r j s, d • (N i j * M r s) - N r j * M i s = d • (M r s * N i j) - M r j * N i s) :
    d0 (ins b Nᵀ) * (d • (1 : M2 (SlopeTestRemainingChoices S A)) - Q0 b) * M =
      M * (d • (1 : M2 (SlopeTestRemainingChoices S A)) - Q0 b) * d0 (ins b Nᵀ) := by
  have hM' : ∀ i j, FreeOf b (M i j) := hM
  have hC : ∀ i j k l, Commute (eU b k l) (M i j) := fun i j => hM' i j
  have h1 : ∀ r s, FreeOf b (N r s) := hN
  have hT : FreeOf2 b Nᵀ := fun r s => h1 s r
  refine Matrix.ext fun i j => ?_
  have key : ∀ r s, d • (eU b r s * (N s r * M i j)) - eU b r s * (N i r * M s j) =
      d • (eU b r s * (M i j * N s r)) - eU b r s * (M i r * N s j) := fun r s => by
    have := congrArg (eU b r s * ·) (h s i r j)
    simp only [mul_sub, mul_smul_comm] at this
    exact this
  have hL : ((d0 (ins b Nᵀ) * (d • (1 : M2 (SlopeTestRemainingChoices S A)) - Q0 b) * M : M2 (SlopeTestRemainingChoices S A))) i j =
      d • (ins b Nᵀ * M i j) - ∑ k, ins b Nᵀ * (M k j * eU b i k) := by
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.sub_apply,
      Matrix.smul_apply, d0, Matrix.diagonal_mul, Matrix.mul_apply]
    simp only [Matrix.diagonal_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc]
    exact congrArg (ins b Nᵀ * ·) (hC k j i k).eq
  have hR : ((M * (d • (1 : M2 (SlopeTestRemainingChoices S A)) - Q0 b) * d0 (ins b Nᵀ) : M2 (SlopeTestRemainingChoices S A))) i j =
      d • (M i j * ins b Nᵀ) - ∑ k, eU b k j * M i k * ins b Nᵀ := by
    rw [mul_sub, sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.sub_apply,
      Matrix.smul_apply, d0, Matrix.mul_diagonal, Matrix.mul_diagonal, Matrix.mul_apply, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hC i k k j).eq]
    rfl
  rw [hL, hR, ins_mul, mul_ins b _ _ (hM' i j),
    Finset.sum_congr rfl fun k _ => ins_mul_eU b i k (M k j) Nᵀ (hM' k j) hT,
    Finset.sum_congr rfl fun k _ => eU_mul_ins b k j (M i k) Nᵀ (hM' i k),
    Finset.sum_comm (f := fun k r => eU b r k * (Nᵀ r i * M k j)),
    Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => key r s

end

end Formalism.FourierDecayAlt.P.Wd3

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd

theorem exchange_relation_plus : Formalism.FourierDecayAlt.Wd.ExchPlus := by
  unfold Formalism.FourierDecayAlt.Wd.ExchPlus
  intro K A S _ _ _ _ _ _ _ _ Ω RR TT q a Y Ya hmod hfree hY hYa
  obtain ⟨_, _, hrtt, _, _⟩ := hmod
  have hr : RTTat TT Ya Y := hrtt Ya hYa Y hY
  have hc := Wd3.plus_core a (TT Y) (TT Ya) (Y - Ya) (hfree Y) (hfree Ya)
    (Wd3.rtt_entry (TT Y) (TT Ya) (Y - Ya) hr)
  rw [Rh0, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, hc]

theorem exchange_relation_minus : Formalism.FourierDecayAlt.Wd.ExchMinus := by
  unfold Formalism.FourierDecayAlt.Wd.ExchMinus
  intro K A S _ _ _ _ _ _ _ _ Ω RR TT q b Y Yb hmod hfree hY hYb
  obtain ⟨_, _, hrtt, _, _⟩ := hmod
  have hr : RTTat TT Y Yb := hrtt Y hY Yb hYb
  have hc := Wd3.minus_core b (TT Y) (TT Yb) (Yb - Y) (hfree Y) (hfree Yb)
    (Wd3.rtt_entry (TT Yb) (TT Y) (Yb - Y) hr)
  simp only [Rht0, Matrix.mul_smul, Matrix.smul_mul, hc]

end Formalism.FourierDecayAlt.P
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockEstimatesSumForm
open Finset

noncomputable section

namespace Formalism.FourierDecayAlt.P.BaseGramNonnegativity

open Formalism.FourierDecayAlt.crystallineComparison Formalism.FourierDecayAlt.TB

theorem sum_re_nonneg {α : Type} (Y : Finset α) (κ G : α → α → ℂ) (hκ : PSDOn Y κ) (hG : PSDOn Y G) :
    0 ≤ (∑ h ∈ Y, ∑ h' ∈ Y, κ h h' * G h h').re := by
  have H := (Matrix.PosSemidef.hadamard hκ hG).re_dotProduct_nonneg (fun _ => (1 : ℂ))
  simp only [dotProduct, Matrix.mulVec, Matrix.hadamard_apply, Matrix.of_apply, Pi.star_apply,
    star_one, one_mul, mul_one, RCLike.re_to_complex] at H
  convert H using 2
  rw [← Finset.sum_coe_sort Y]
  refine Finset.sum_congr rfl (fun h _ => ?_)
  rw [← Finset.sum_coe_sort Y]

variable {E W : Type} [Field E] (D : Data E W)

theorem baseGram_nonneg (hG : D.GramPSD) (hW : D.WordsPos) {ε : ℝ} (hε : 0 < ε) (k : ℕ) (w : W)
    (Y : Finset (Pt E)) (κ : Pt E → Pt E → ℂ) (hκ : PSDOn Y κ) : 0 ≤ D.N0 ε k w Y κ :=
  div_nonneg (sum_re_nonneg Y κ _ hκ (hG ε hε k w Y)) (hW w).le

theorem Wb_mono {n m : ℕ} (h : n ≤ m) : D.Wb n ⊆ D.Wb m := by
  intro x hx
  simp only [Data.Wb, Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.trans h⟩

theorem estBlockOfSumForm_ok : EstBlockOfSumForm := by
  intro E W _ D C₄ hG hW hSF ε hε i s hs hsi hir w hw hcnt hvol
  obtain ⟨Mv, hMv, θ, hθ, hb⟩ := hSF ε hε i s hs hsi hir w hw hcnt hvol
  have hsub : D.Wb (D.cnt w + s * D.K) ⊆ D.Wb (D.cnt w + (s + 1) * D.K) :=
    Wb_mono D (by nlinarith)
  have hext : ∀ g : W → ℝ, ∑ w' ∈ D.Wb (D.cnt w + (s + 1) * D.K), θ w' * g w' =
      ∑ w' ∈ D.Wb (D.cnt w + s * D.K), θ w' * g w' := by
    intro g
    symm
    refine Finset.sum_subset hsub (fun x _ hx => ?_)
    rw [hθ.2.1 x hx, zero_mul]
  refine ⟨θ, ⟨hθ.1, fun a ha => hθ.2.1 a (fun h => ha (hsub h)), ?_⟩, ?_⟩
  · have := hext (fun _ => 1)
    simp only [mul_one] at this
    rw [this, hθ.2.2]
  · intro Y hY κ hκ t₀ S hS
    have h := hb Y hY κ hκ t₀ S hS
    rw [hext]
    have hX : 0 ≤ ∑ w' ∈ D.Wb (D.cnt w + s * D.K), θ w' * D.N0 ε (i - s) w' Y κ :=
      Finset.sum_nonneg (fun w' _ => mul_nonneg (hθ.1 w') (baseGram_nonneg D hG hW hε _ _ Y κ hκ))
    exact h.trans (mul_le_mul_of_nonneg_right hMv hX)

end Formalism.FourierDecayAlt.P.BaseGramNonnegativity

theorem Formalism.FourierDecayAlt.P.blockEstimateOfCosetSum : Formalism.FourierDecayAlt.crystallineComparison.EstBlockOfSumForm :=
  Formalism.FourierDecayAlt.P.BaseGramNonnegativity.estBlockOfSumForm_ok
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.MajorantIntegrals
open MeasureTheory Set

noncomputable section

namespace Formalism.FourierDecayAlt.P.MajorantIntegrals

open Formalism.FourierDecayAlt.crystallineComparison

theorem radial_eq (K : ℕ) (x : ℝ) (hx : 0 < x) (y : ℝ) (hy : 0 < y) :
    y ^ (Module.finrank ℝ ℂ - 1) • mfac K x y =
      if y ≤ x then y else x ^ K * y ^ ((1 : ℝ) - K) := by
  rw [Complex.finrank_real_complex]
  simp only [mfac, hy.ne', if_false, smul_eq_mul, show 2 - 1 = 1 from rfl, pow_one]
  split_ifs with hxy
  · rw [min_eq_left (one_le_pow₀ ((one_le_div hy).mpr hxy)), mul_one]
  · push Not at hxy
    have h1 : (x / y) ^ K ≤ 1 :=
      pow_le_one₀ (div_nonneg hx.le hy.le) ((div_le_one hy).mpr hxy.le)
    rw [min_eq_right h1, Real.rpow_sub hy, Real.rpow_one, Real.rpow_natCast, div_pow]
    field_simp

theorem volC : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
  simp [Measure.real, Complex.volume_ball]

theorem majIntegral_ok : MajIntegral := by
  intro K x hK hx
  have hK' : (2 : ℝ) < K := by exact_mod_cast hK
  have hcongr : EqOn (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • mfac K x y)
      (fun y => if y ≤ x then y else x ^ K * y ^ ((1 : ℝ) - K)) (Ioi 0) :=
    fun y hy => radial_eq K x hx y hy
  have hIoc : IntegrableOn (fun y : ℝ => y) (Ioc 0 x) :=
    (continuous_id.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hIoi : IntegrableOn (fun y : ℝ => x ^ K * y ^ ((1 : ℝ) - K)) (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) hx).const_mul _
  have hA : IntegrableOn (fun y : ℝ => if y ≤ x then y else x ^ K * y ^ ((1 : ℝ) - K)) (Ioc 0 x) :=
    hIoc.congr_fun (fun y hy => by simp [hy.2]) measurableSet_Ioc
  have hB : IntegrableOn (fun y : ℝ => if y ≤ x then y else x ^ K * y ^ ((1 : ℝ) - K)) (Ioi x) :=
    hIoi.congr_fun (fun y hy => by simp [not_le.mpr (mem_Ioi.mp hy)]) measurableSet_Ioi
  have hint : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • mfac K x y) (Ioi 0) := by
    refine IntegrableOn.congr_fun ?_ hcongr.symm measurableSet_Ioi
    rw [← Ioc_union_Ioi_eq_Ioi hx.le]
    exact hA.union hB
  refine ⟨(integrable_fun_norm_addHaar volume (f := mfac K x)).mpr hint, ?_⟩
  rw [integral_fun_norm_addHaar volume (mfac K x), setIntegral_congr_fun measurableSet_Ioi hcongr,
    ← Ioc_union_Ioi_eq_Ioi hx.le,
    setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hA hB,
    setIntegral_congr_fun measurableSet_Ioc (fun y hy => if_pos hy.2),
    setIntegral_congr_fun measurableSet_Ioi (fun y hy => if_neg (not_le.mpr (mem_Ioi.mp hy))),
    ← intervalIntegral.integral_of_le hx.le, integral_id, integral_const_mul,
    integral_Ioi_rpow_of_lt (by linarith) hx, volC, Complex.finrank_real_complex]
  have e : x ^ K * x ^ ((1 : ℝ) - K + 1) = x ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hx]
    rw [show (K : ℝ) + (1 - K + 1) = ((2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  have hK2 : (K : ℝ) - 2 ≠ 0 := by linarith
  have hK3 : (1 : ℝ) - K + 1 ≠ 0 := by linarith
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat]
  rw [neg_div, mul_neg, ← mul_div_assoc, e]
  have hK4 : (1 : ℝ) - K + 1 = -((K : ℝ) - 2) := by ring
  rw [hK4]
  field_simp
  ring

theorem majIntegralProd_ok : MajIntegralProd := by
  intro f K x hK hx
  have h1 := fun v => (majIntegral_ok K (x v) hK (hx v))
  refine ⟨Integrable.fintype_prod (f := fun v (l : ℂ) => mfac K (x v) ‖l‖)
    (μ := fun _ => volume) (fun v => (h1 v).1), ?_⟩
  have h2 := integral_fintype_prod_volume_eq_prod (ι := Fin f) (E := fun _ => ℂ)
    (fun v (l : ℂ) => mfac K (x v) ‖l‖)
  exact h2.trans (Finset.prod_congr rfl (fun v _ => (h1 v).2))

end Formalism.FourierDecayAlt.P.MajorantIntegrals
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.OneLevelInequalitySplitBySize
namespace Formalism.FourierDecayAlt.P

theorem one_level_inequality_split_by_size : Formalism.FourierDecayAlt.TB.OneLevel :=
  levelInequalityOfSteps splitByLastSize schurRecursion_true diagStep
    singleBlockStep longBlockStep

end Formalism.FourierDecayAlt.P
end
