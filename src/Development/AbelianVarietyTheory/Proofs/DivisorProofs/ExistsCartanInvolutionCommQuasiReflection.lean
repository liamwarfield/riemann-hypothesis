module

public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlkEquivInl
public import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.LiftErrorLocal
public import Formalism.ArtinHasse.ArtinHasseProofs.SymmSeries
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionCommQuasiReflection
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionCommQuasiReflection
open Matrix Formalism.IndefR.Datum
open scoped ComplexOrder MatrixOrder

namespace GlobalTheory.CartanRefl

theorem exists_sign {k : ℕ} {G : Matrix (Fin k) (Fin k) ℂ} (hG : G.IsHermitian) (hd : G.det ≠ 0) :
    ∃ s, IsCartanInv G s ∧ ∀ u, u * G = G * u → u * s = s * u := by
  classical
  let U : Matrix (Fin k) (Fin k) ℂ := hG.eigenvectorUnitary.1
  have h1 : U * star U = 1 := hG.eigenvectorUnitary.2.2
  have h2 : star U * U = 1 := hG.eigenvectorUnitary.2.1
  have hs : G = U * diagonal (fun i => (hG.eigenvalues i : ℂ)) * star U := by
    have := hG.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hne : ∀ i, hG.eigenvalues i ≠ 0 := fun i hi => by
    rw [hG.det_eq_prod_eigenvalues] at hd
    exact hd (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]))
  have mul : ∀ a b : Fin k → ℂ, (U * diagonal a * star U) * (U * diagonal b * star U) =
      U * diagonal (fun i => a i * b i) * star U := fun a b => by
    calc _ = U * (diagonal a * (star U * U) * diagonal b) * star U := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.mul_one, diagonal_mul_diagonal]
  let e : Fin k → ℝ := fun i => if 0 < hG.eigenvalues i then 1 else -1
  have he : ∀ i, (e i : ℂ) * e i = 1 := fun i => by
    simp only [e]; split_ifs <;> simp
  have hh : (U * diagonal (fun i => (e i : ℂ)) * star U)ᴴ = U * diagonal (fun i => (e i : ℂ)) * star U := by
    simp [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc,
      Pi.star_def]
  refine ⟨U * diagonal (fun i => (e i : ℂ)) * star U, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [mul]
    simp only [he, diagonal_one, Matrix.mul_one, h1]
  · rw [hh]
    conv_lhs => rw [hs]
    conv_rhs => rw [hs]
    rw [mul, mul]
    congr 3
    funext i
    rw [mul_right_comm, he, one_mul]
  · conv => arg 1; arg 1; rw [hs]
    rw [mul]
    have hp : (diagonal fun i => (hG.eigenvalues i : ℂ) * e i).PosDef := by
      rw [Matrix.posDef_diagonal_iff]
      intro i
      rw [← Complex.ofReal_mul, Complex.zero_lt_real]
      simp only [e]
      split_ifs with h
      · simpa using h
      · have := lt_of_le_of_ne (not_lt.1 h) (hne i)
        linarith
    have hu : IsUnit (star U) := ⟨⟨star U, U, h2, h1⟩, rfl⟩
    have := hp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)
    rwa [Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose] at this
  · intro u hu
    obtain ⟨v, rfl⟩ : ∃ v, u = U * v * star U := ⟨star U * u * U, by
      calc u = (U * star U) * u * (U * star U) := by rw [h1, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]⟩
    have cm : ∀ a b : Matrix (Fin k) (Fin k) ℂ, (U * a * star U) * (U * b * star U) = U * (a * b) * star U := fun a b => by
      calc _ = U * (a * (star U * U) * b) * star U := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h2, Matrix.mul_one]
    have inj : ∀ a b : Matrix (Fin k) (Fin k) ℂ, U * a * star U = U * b * star U → a = b := fun a b h => by
      have key : ∀ a : Matrix (Fin k) (Fin k) ℂ, star U * (U * a * star U) * U = a := fun a => by
        calc _ = (star U * U) * a * (star U * U) := by simp only [Matrix.mul_assoc]
          _ = a := by rw [h2, Matrix.one_mul, Matrix.mul_one]
      rw [← key a, h, key]
    have hv : v * diagonal (fun i => (hG.eigenvalues i : ℂ)) = diagonal (fun i => (hG.eigenvalues i : ℂ)) * v := by
      apply inj
      rw [← cm, ← cm, ← hs, hu]
    rw [cm, cm]
    congr 2
    ext i j
    have hij := congrFun (congrFun hv i) j
    rw [mul_diagonal, diagonal_mul] at hij ⊢
    by_cases h0 : v i j = 0
    · simp [h0]
    · have : hG.eigenvalues j = hG.eigenvalues i := by
        rw [mul_comm] at hij
        exact_mod_cast mul_right_cancel₀ h0 hij
      simp only [e, this, mul_comm]

theorem exists_comm {k : ℕ} {G r : Matrix (Fin k) (Fin k) ℂ} (hG : Gᴴ = G) (hd : G.det ≠ 0)
    (hr : r * r = 1) (hrG : rᴴ * G * r = G) : ∃ s, IsCartanInv G s ∧ s * r = r * s := by
  classical
  have hH : (1 + rᴴ * r).PosDef := PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self r)
  obtain ⟨C, hC, hCH⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hH.isStrictlyPositive
  obtain ⟨⟨C, B, hCB, hBC⟩, rfl⟩ := hC
  simp only [star_eq_conjTranspose] at hCH
  have hCB' : Bᴴ * Cᴴ = 1 := by rw [← conjTranspose_mul, hCB, conjTranspose_one]
  have hBC' : Cᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, hBC, conjTranspose_one]
  have hr' : rᴴ * rᴴ = 1 := by rw [← conjTranspose_mul, hr, conjTranspose_one]
  have e1 : ∀ X : Matrix (Fin k) (Fin k) ℂ, C * (B * X) = X := fun X => by rw [← Matrix.mul_assoc, hCB, Matrix.one_mul]
  have e2 : ∀ X : Matrix (Fin k) (Fin k) ℂ, B * (C * X) = X := fun X => by rw [← Matrix.mul_assoc, hBC, Matrix.one_mul]
  have e3 : ∀ X : Matrix (Fin k) (Fin k) ℂ, Bᴴ * (Cᴴ * X) = X := fun X => by rw [← Matrix.mul_assoc, hCB', Matrix.one_mul]
  have e4 : ∀ X : Matrix (Fin k) (Fin k) ℂ, Cᴴ * (Bᴴ * X) = X := fun X => by rw [← Matrix.mul_assoc, hBC', Matrix.one_mul]
  have e5 : ∀ X : Matrix (Fin k) (Fin k) ℂ, r * (r * X) = X := fun X => by rw [← Matrix.mul_assoc, hr, Matrix.one_mul]
  have e6 : ∀ X : Matrix (Fin k) (Fin k) ℂ, rᴴ * (G * (r * X)) = G * X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hrG]
  have hinv : rᴴ * (Cᴴ * C) * r = Cᴴ * C := by
    rw [← hCH, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc, hr', Matrix.one_mul, hr, add_comm]
  have huu : (C * r * B) * (C * r * B) = 1 := by
    simp only [Matrix.mul_assoc, e2, e5, hCB]
  have hsu : (C * r * B)ᴴ * (C * r * B) = 1 := by
    calc _ = Bᴴ * (rᴴ * (Cᴴ * C) * r) * B := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hinv]; simp only [Matrix.mul_assoc, e3, hCB]
  have hu : (C * r * B)ᴴ = C * r * B := by
    calc _ = (C * r * B)ᴴ * ((C * r * B) * (C * r * B)) := by rw [huu, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hsu, Matrix.one_mul]
  have hG' : (Bᴴ * G * B).IsHermitian := isHermitian_conjTranspose_mul_mul B hG
  have hd' : (Bᴴ * G * B).det ≠ 0 := by
    intro h
    apply hd
    have : G = Cᴴ * (Bᴴ * G * B) * C := by simp only [Matrix.mul_assoc, e4, hBC, Matrix.mul_one]
    rw [this, det_mul, det_mul, h, mul_zero, zero_mul]
  have hc : (C * r * B) * (Bᴴ * G * B) = (Bᴴ * G * B) * (C * r * B) := by
    have : (C * r * B)ᴴ * (Bᴴ * G * B) * (C * r * B) = Bᴴ * G * B := by
      simp only [conjTranspose_mul, Matrix.mul_assoc, e4, e2, e6]
    rw [hu] at this
    conv_lhs => rw [← this]
    rw [← Matrix.mul_assoc (C * r * B), ← Matrix.mul_assoc (C * r * B), huu, Matrix.one_mul]
  obtain ⟨s, ⟨hs1, hs2, hs3⟩, hs4⟩ := exists_sign hG' hd'
  have hs5 := hs4 _ hc
  refine ⟨B * s * C, ⟨?_, ?_, ?_⟩, ?_⟩
  · calc _ = B * (s * s) * C := by simp only [Matrix.mul_assoc, e1]
      _ = 1 := by rw [hs1, Matrix.mul_one, hBC]
  · calc _ = Cᴴ * (sᴴ * (Bᴴ * G * B) * s) * C := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [hs2]; simp only [Matrix.mul_assoc, e4, hBC, Matrix.mul_one]
  · have hu : IsUnit C := ⟨⟨C, B, hCB, hBC⟩, rfl⟩
    have := hs3.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)
    simpa only [Matrix.mul_assoc, e4] using this
  · calc _ = B * (s * (C * r * B)) * C := by simp only [Matrix.mul_assoc, hBC, Matrix.mul_one]
      _ = _ := by rw [← hs5]; simp only [Matrix.mul_assoc, e2]

theorem exists_cartan_comm_quasiReflection : ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), Gᴴ = G → G.det ≠ 0 → ∀ x : Fin n → ℂ, star x ⬝ᵥ G *ᵥ x ≠ 0 → ∃ s, IsCartanInv G s ∧ ∀ c : ℂ, s * (1 + c • Matrix.vecMulVec x (star x ᵥ* G)) = (1 + c • Matrix.vecMulVec x (star x ᵥ* G)) * s := by
  intro n G hG hd x hx
  set q := star x ⬝ᵥ G *ᵥ x with hq
  have hM : Matrix.vecMulVec x (star x ᵥ* G) = Matrix.vecMulVec x (star x) * G := by
    rw [vecMulVec_mul]
  have hN : (Matrix.vecMulVec x (star x))ᴴ = Matrix.vecMulVec x (star x) := by
    rw [conjTranspose_vecMulVec, star_star]
  have hMM : Matrix.vecMulVec x (star x ᵥ* G) * Matrix.vecMulVec x (star x ᵥ* G) = q • Matrix.vecMulVec x (star x ᵥ* G) := by
    rw [vecMulVec_mul_vecMulVec, hq, dotProduct_mulVec, vecMulVec_smul]
  have hMG : (Matrix.vecMulVec x (star x ᵥ* G))ᴴ * G = G * Matrix.vecMulVec x (star x ᵥ* G) := by
    rw [hM, conjTranspose_mul, hN, hG, Matrix.mul_assoc]
  have hqs : star q = q := by
    rw [hq, ← star_dotProduct_star, star_star, star_mulVec, hG, dotProduct_mulVec]
  generalize Matrix.vecMulVec x (star x ᵥ* G) = M at hMM hMG ⊢
  have hr : (1 + (-2 / q) • M) * (1 + (-2 / q) • M) = 1 := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hMM,
      smul_smul, add_assoc, ← add_smul, smul_add]
    have : -2 / q + (-2 / q + -2 / q * (-2 / q * q)) = 0 := by field_simp; ring
    rw [this, zero_smul, add_zero]
  have hrG : (1 + (-2 / q) • M)ᴴ * G = G * (1 + (-2 / q) • M) := by
    have : star (-2 / q) = -2 / q := by rw [star_div₀, hqs]; simp
    rw [conjTranspose_add, conjTranspose_one, conjTranspose_smul, this, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hMG]
  obtain ⟨s, hs, hc⟩ := exists_comm hG hd hr (by rw [hrG, Matrix.mul_assoc, hr, Matrix.mul_one])
  refine ⟨s, hs, fun c => ?_⟩
  have hsM : s * M = M * s := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      add_right_inj] at hc
    exact smul_right_injective _ (div_ne_zero (by norm_num) hx) hc
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hsM]

end GlobalTheory.CartanRefl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanInvolutionCommQuasiReflectionStatement
open Matrix Formalism.IndefR.Datum
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cartanInvolution_comm_quasiReflection : ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), Gᴴ = G → G.det ≠ 0 → ∀ x : Fin n → ℂ, star x ⬝ᵥ G *ᵥ x ≠ 0 → ∃ s, IsCartanInv G s ∧ ∀ c : ℂ, s * (1 + c • Matrix.vecMulVec x (star x ᵥ* G)) = (1 + c • Matrix.vecMulVec x (star x ᵥ* G)) * s := by
  first | exact @GlobalTheory.CartanRefl.exists_cartan_comm_quasiReflection | exact GlobalTheory.CartanRefl.exists_cartan_comm_quasiReflection | (intros; apply GlobalTheory.CartanRefl.exists_cartan_comm_quasiReflection <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroSquaresSumEquivIcoModFour
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroSquaresSumEquivIcoModFour
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.SqSplit

theorem natCast_sub_eq_neg {p n : ℕ} (h : n ≤ p) : ((p - n : ℕ) : ZMod p) = -((n : ℕ) : ZMod p) := by
  rw [Nat.cast_sub h, ZMod.natCast_self, zero_sub]

theorem neg_one_not_isSquare {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3) : ¬ IsSquare (-1 : ZMod p) := by
  rw [ZMod.exists_sq_eq_neg_one_iff]; omega

theorem ringChar_ne_two {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]; omega

theorem isSquare_neg_of_not {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3) {a : ZMod p} (ha : a ≠ 0)
    (hs : ¬ IsSquare a) : IsSquare (-a) := by
  have hc := ringChar_ne_two h3
  have h1 : quadraticChar (ZMod p) a = -1 := (quadraticChar_neg_one_iff_not_isSquare).2 hs
  have h2 : quadraticChar (ZMod p) (-1) = -1 :=
    (quadraticChar_neg_one_iff_not_isSquare).2 (neg_one_not_isSquare h3)
  have hna : -a ≠ 0 := neg_ne_zero.2 ha
  rw [← quadraticChar_one_iff_isSquare hna, neg_eq_neg_one_mul, map_mul, h1, h2]; norm_num

theorem not_both {p : ℕ} [Fact p.Prime] (h3 : p % 4 = 3) {a : ZMod p} (ha : a ≠ 0)
    (h1 : IsSquare a) (h2 : IsSquare (-a)) : False := by
  apply neg_one_not_isSquare h3
  have : (-1 : ZMod p) = -a * a⁻¹ := by rw [neg_mul, mul_inv_cancel₀ ha]
  rw [this]; exact h2.mul h1.inv

end GlobalTheory.SqSplit

open GlobalTheory.SqSplit in
theorem GlobalTheory.sq_sum_equiv_Ico : ∀ (p : ℕ), p.Prime → p % 4 = 3 → ∃ e : Sq p ⊕ Sq p ≃ (Finset.Ico 1 p : Finset ℕ), ∀ k : Sq p, ((e (Sum.inl k) : ℕ) = (k.1 : ℕ)) ∧ ((e (Sum.inr k) : ℕ) = p - (k.1 : ℕ)) := by
  intro p hp h3
  haveI : Fact p.Prime := ⟨hp⟩
  have pos : ∀ k : Sq p, 1 ≤ (k.1 : ℕ) := by
    intro k
    rcases Nat.eq_zero_or_pos (k.1 : ℕ) with h | h
    · exact absurd (by rw [h]; simp) k.2.1
    · exact h
  let f : Sq p ⊕ Sq p → (Finset.Ico 1 p : Finset ℕ) := Sum.elim
    (fun k => ⟨(k.1 : ℕ), Finset.mem_Ico.2 ⟨pos k, k.1.2⟩⟩)
    (fun k => ⟨p - (k.1 : ℕ), Finset.mem_Ico.2 ⟨by have := k.1.2; omega, by have := pos k; omega⟩⟩)
  have hf : Function.Bijective f := by
    constructor
    · rintro (a | a) (b | b) hab <;> simp only [f, Sum.elim_inl, Sum.elim_inr, Subtype.mk.injEq] at hab
      · exact congrArg Sum.inl (Subtype.ext (Fin.ext hab))
      · exfalso
        have hb := b.1.2
        have e1 : ((a.1 : ℕ) : ZMod p) = -((b.1 : ℕ) : ZMod p) := by
          rw [hab, natCast_sub_eq_neg hb.le]
        exact not_both h3 b.2.1 b.2.2 (e1 ▸ a.2.2)
      · exfalso
        have ha := a.1.2
        have e1 : ((b.1 : ℕ) : ZMod p) = -((a.1 : ℕ) : ZMod p) := by
          rw [← hab, natCast_sub_eq_neg ha.le]
        exact not_both h3 a.2.1 a.2.2 (e1 ▸ b.2.2)
      · have ha := a.1.2; have hb := b.1.2
        exact congrArg Sum.inr (Subtype.ext (Fin.ext (by omega)))
    · rintro ⟨n, hn⟩
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 hn
      have hn0 : ((n : ℕ) : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd; exact absurd (Nat.le_of_dvd (by omega) hd) (by omega)
      by_cases hs : IsSquare ((n : ℕ) : ZMod p)
      · exact ⟨Sum.inl ⟨⟨n, h2⟩, hn0, hs⟩, rfl⟩
      · have hm : ((p - n : ℕ) : ZMod p) = -((n : ℕ) : ZMod p) := natCast_sub_eq_neg h2.le
        refine ⟨Sum.inr ⟨⟨p - n, by omega⟩, ?_, ?_⟩, ?_⟩
        · simp only; rw [hm]; exact neg_ne_zero.2 hn0
        · simp only; rw [hm]; exact isSquare_neg_of_not h3 hn0 hs
        · simp only [f, Sum.elim_inr]; apply Subtype.ext; simp only; omega
  exact ⟨Equiv.ofBijective f hf, fun k => ⟨rfl, rfl⟩⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroSquaresSumEquivIcoModFourStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonzeroSquares_sum_equiv_Ico_mod_four : ∀ (p : ℕ), p.Prime → p % 4 = 3 → ∃ e : Sq p ⊕ Sq p ≃ (Finset.Ico 1 p : Finset ℕ), ∀ k : Sq p, ((e (Sum.inl k) : ℕ) = (k.1 : ℕ)) ∧ ((e (Sum.inr k) : ℕ) = p - (k.1 : ℕ)) := by
  first | exact @GlobalTheory.sq_sum_equiv_Ico | exact GlobalTheory.sq_sum_equiv_Ico | (intros; apply GlobalTheory.sq_sum_equiv_Ico <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqrtNegPrimeKernelCyclic
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqrtNegPrimeKernelCyclic
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem ker_sqrtNegNat_cyclic : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → (∀ k : ℤ, (k : ℂ) * t ∈ L.lattice ↔ (p : ℤ) ∣ k) ∧ (∀ z, sqrtNegNat p * z ∈ L.lattice → ∃ k : ℕ, k < p ∧ z - (k : ℂ) * t ∈ L.lattice) ∧ IsKerReps L (sqrtNegNat p) ((Finset.Ico 1 p).image fun k : ℕ => (k : ℂ) * t) := by
  intro p F L t hp _ _ D
  have hsq : sqrtNegNat p ^ 2 = -(p : ℂ) := sqrtNegNat_sq p
  have hz : ∀ (n : ℤ) (x : ℂ), x ∈ L.lattice → (n : ℂ) * x ∈ L.lattice := fun n x hx => by
    simpa [zsmul_eq_mul] using L.lattice.smul_mem n hx
  have hpt : (p : ℂ) * t ∈ L.lattice := by
    have h := L.lattice.neg_mem (D.mul _ D.ker)
    have e : -(sqrtNegNat p * (sqrtNegNat p * t)) = (p : ℂ) * t := by
      linear_combination (-t) * hsq
    rwa [e] at h
  have h1 : ∀ k : ℤ, (k : ℂ) * t ∈ L.lattice ↔ (p : ℤ) ∣ k := by
    intro k
    constructor
    · intro hk
      by_contra hnd
      have hc : IsCoprime (p : ℤ) k := (Nat.prime_iff_prime_int.mp hp).irreducible.coprime_iff_not_dvd.mpr hnd
      obtain ⟨a, b, hab⟩ := hc
      apply D.notMem
      have h := L.lattice.add_mem (hz a _ hpt) (hz b _ hk)
      have hab' : (a : ℂ) * (p : ℂ) + (b : ℂ) * (k : ℂ) = 1 := by exact_mod_cast congrArg (Int.cast (R := ℂ)) hab
      have e : (a : ℂ) * ((p : ℂ) * t) + (b : ℂ) * ((k : ℂ) * t) = t := by
        linear_combination t * hab'
      rwa [e] at h
    · rintro ⟨c, rfl⟩
      have h := hz c _ hpt
      have e : (c : ℂ) * ((p : ℂ) * t) = (((p : ℤ) * c : ℤ) : ℂ) * t := by push_cast; ring
      rwa [e] at h
  have hker : ∀ k : ℕ, sqrtNegNat p * ((k : ℂ) * t) ∈ L.lattice := fun k => by
    have h := hz k _ D.ker
    have e : ((k : ℤ) : ℂ) * (sqrtNegNat p * t) = sqrtNegNat p * ((k : ℂ) * t) := by push_cast; ring
    rwa [e] at h
  have hnot : ∀ k ∈ Finset.Ico 1 p, (k : ℂ) * t ∉ L.lattice := fun k hk h => by
    rw [Finset.mem_Ico] at hk
    have h' : (p : ℤ) ∣ (k : ℤ) := (h1 k).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd hk.1 (Int.natCast_dvd_natCast.mp h')
    omega
  have hinj : ∀ k ∈ Finset.Ico 1 p, ∀ l ∈ Finset.Ico 1 p, (k : ℂ) * t - (l : ℂ) * t ∈ L.lattice → k = l := by
    intro k hk l hl h
    rw [Finset.mem_Ico] at hk hl
    have e : (k : ℂ) * t - (l : ℂ) * t = (((k : ℤ) - (l : ℤ) : ℤ) : ℂ) * t := by push_cast; ring
    rw [e, h1] at h
    have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hn : Complex.normSq (sqrtNegNat p) = p := by
    have h := congrArg Complex.normSq hsq
    rw [map_pow, Complex.normSq_neg, Complex.normSq_natCast, ← sq] at h
    exact (pow_left_inj₀ (Complex.normSq_nonneg _) hp0.le two_ne_zero).mp h
  have hα : sqrtNegNat p ≠ 0 := fun h => by
    rw [h, map_zero] at hn
    exact hp0.ne hn
  obtain ⟨S, hS⟩ := kerRepsExist L _ hα D.mul
  have hcard : S.card + 1 = p := by
    have h := kerRepsCard L _ S hα D.mul hS
    rw [hn] at h
    exact_mod_cast h
  choose f hfS hf using fun k (hk : k ∈ Finset.Ico 1 p) => hS.2.2 _ (hker k) (hnot k hk)
  have hsurj := Finset.surj_on_of_inj_on_of_card_le f hfS
    (fun k l hk hl h => hinj k hk l hl (by
      have h' := L.lattice.sub_mem (hf k hk) (hf l hl)
      rw [h] at h'
      simpa using h'))
    (by rw [Nat.card_Ico]; omega)
  have h3 : ∀ z, sqrtNegNat p * z ∈ L.lattice → z ∉ L.lattice →
      ∃ k ∈ Finset.Ico 1 p, z - (k : ℂ) * t ∈ L.lattice := by
    intro z hz1 hz2
    obtain ⟨P, hP, hzP⟩ := hS.2.2 z hz1 hz2
    obtain ⟨k, hk, rfl⟩ := hsurj P hP
    refine ⟨k, hk, ?_⟩
    simpa using L.lattice.sub_mem hzP (hf k hk)
  refine ⟨h1, fun z hz1 => ?_, ?_, ?_, ?_⟩
  · by_cases hz2 : z ∈ L.lattice
    · exact ⟨0, hp.pos, by simpa using hz2⟩
    · obtain ⟨k, hk, h⟩ := h3 z hz1 hz2
      exact ⟨k, (Finset.mem_Ico.mp hk).2, h⟩
  · intro P hP
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hP
    exact ⟨hker k, hnot k hk⟩
  · intro P hP Q hQ h
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hP
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hQ
    rw [hinj k hk l hl h]
  · intro z hz1 hz2
    obtain ⟨k, hk, h⟩ := h3 z hz1 hz2
    exact ⟨_, Finset.mem_image_of_mem _ hk, h⟩

end GlobalTheory.CMModel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqrtNegPrimeKernelCyclicStatement
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sqrtNegPrime_kernel_cyclic : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ), p.Prime → p % 4 = 3 → 3 < p → Datum p F L t → (∀ k : ℤ, (k : ℂ) * t ∈ L.lattice ↔ (p : ℤ) ∣ k) ∧ (∀ z, sqrtNegNat p * z ∈ L.lattice → ∃ k : ℕ, k < p ∧ z - (k : ℂ) * t ∈ L.lattice) ∧ IsKerReps L (sqrtNegNat p) ((Finset.Ico 1 p).image fun k : ℕ => (k : ℂ) * t) := by
  first | exact @GlobalTheory.CMModel.ker_sqrtNegNat_cyclic | exact GlobalTheory.CMModel.ker_sqrtNegNat_cyclic | (intros; apply GlobalTheory.CMModel.ker_sqrtNegNat_cyclic <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FloorCastOfInt
open Formalism.BasicNotions Formalism.BasicNotions.TH MeasureTheory NumberField IsDedekindDomain
open GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts GlobalTheory.BlockSizes
open Formalism.MainNotions.DIV.Inh (aPlusQ_anti aMinusQ_mono)

namespace GlobalTheory.BlockRows

theorem floor_cast_of_int {x : ℚ} (h : ∃ z : ℤ, x = z) (h1 : 1 ≤ x) : ((⌊x⌋₊ : ℕ) : ℚ) = x := by
  obtain ⟨z, rfl⟩ := h
  have hz : (0 : ℤ) ≤ z := by
    have : (1 : ℤ) ≤ z := by exact_mod_cast h1
    omega
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hz
  simp

theorem one_le_aPlusQ (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).1) : 1 ≤ DV.aPlusQ D j τ i := by
  have hk := D.R.m_add_three_le_k
  have hi : i.1 < D.R.k + j - 1 := i.2
  exact (DV.aPlusQ_last D j h1 h2 τ).trans
    (aPlusQ_anti D j τ (show i.1 ≤ D.R.k + j - 1 - 1 by omega) (by omega))

theorem one_le_aMinusQ (D : D7) (j : ℕ) (h1 : 1 ≤ j) (τ : D.what₂.Tau) (c : ℕ) (hc : j + c < D.R.m) :
    1 ≤ DV.aMinusQ D j τ c :=
  (DV.aMinusQ_last D j h1 (by omega) τ).trans (aMinusQ_mono D j τ (Nat.zero_le c) hc)

theorem one_le_b (s : Scale) : 1 ≤ s.b := by
  unfold Scale.b Scale.L
  have := s.one_lt_alt
  exact Real.one_le_exp (Real.rpow_nonneg (by linarith) _)

theorem aPlus_le (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) (L : SizeData₂ D)
    (hL : WindowsLe L) (i : Fin (D.R.sigW j).1) : DV.aPlus D j τ i ≤ 3 * L.sc.b ^ 2 := by
  have hk := D.R.m_add_three_le_k
  have hi : i.1 < D.R.k + j - 1 := i.2
  have h0 : 0 < D.R.k - 1 := by omega
  have a1 := aPlusQ_anti D j τ (Nat.zero_le i.1) (by omega)
  have hj : j - 1 < D.R.m := by omega
  have a2 : DV.aPlusQ D j τ 0 ≤ (D.hc τ).v ⟨0, h0⟩ + (D.hc τ).e ⟨j - 1, hj⟩ := by
    rw [DV.aPlusQ_eq]
    unfold DV.sigPar DV.eQ
    rw [dite_eq_left h0, dite_eq_left ⟨h1, h2⟩]
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    have hk' : (2 : ℚ) ≤ D.R.k := by exact_mod_cast (show 2 ≤ D.R.k by omega)
    have hj' : (0 : ℚ) ≤ j := Nat.cast_nonneg _
    push_cast
    linarith
  have a3 : DV.aPlus D j τ i ≤ (((D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) + (((D.hc τ).e ⟨j - 1, hj⟩ : ℚ) : ℝ) := by
    unfold DV.aPlus
    exact_mod_cast a1.trans a2
  have b1 := (L.cloud_v τ ⟨0, h0⟩).2
  have b2 := L.b_le τ ⟨j - 1, hj⟩
  have b3 := (abs_le.1 (L.be_close τ ⟨j - 1, hj⟩ ⟨j - 1, hj⟩)).1
  have b4 := one_le_b L.sc
  push_cast at b3
  have := hL.1
  have := hL.2
  nlinarith

theorem aMinus_le (D : D7) (j : ℕ) (h1 : 1 ≤ j) (τ : D.what₂.Tau) (L : SizeData₂ D)
    (hL : WindowsLe L) (c : ℕ) (hc : j + c < D.R.m) : DV.aMinus D j τ c ≤ 3 * L.sc.b ^ 2 := by
  have hj : j - 1 < D.R.m := by omega
  have a2 : DV.aMinusQ D j τ c ≤ (D.hc τ).b ⟨j + c, hc⟩ - (D.hc τ).e ⟨j - 1, hj⟩ := by
    unfold DV.aMinusQ DV.eQ
    rw [dite_eq_left hc, dite_eq_left ⟨h1, by omega⟩]
    have ht : (0 : ℚ) ≤ D.R.t := Nat.cast_nonneg _
    have hc' : (0 : ℚ) ≤ c := Nat.cast_nonneg _
    linarith
  have a3 : DV.aMinus D j τ c ≤ (((D.hc τ).b ⟨j + c, hc⟩ - (D.hc τ).e ⟨j - 1, hj⟩ : ℚ) : ℝ) := by
    unfold DV.aMinus
    exact_mod_cast a2
  have b3 := (abs_le.1 (L.be_close τ ⟨j + c, hc⟩ ⟨j - 1, hj⟩)).2
  have b4 := one_le_b L.sc
  have := hL.1
  nlinarith

theorem rows_sizes : ∀ (D : D7) (j : ℕ), 1 ≤ j → j ≤ D.R.m → ∀ τ : D.what₂.Tau, (Antitone (rowsP D j τ) ∧ (∀ i, 1 ≤ rowsP D j τ i) ∧ ∀ i, (rowsP D j τ i : ℝ) = DV.aPlus D j τ i) ∧ (Antitone (rowsM D j τ) ∧ (∀ i, 1 ≤ rowsM D j τ i) ∧ ∀ i, (rowsM D j τ i : ℝ) = DV.aMinus D j τ ((D.R.sigW j).2 - 1 - i)) ∧ ∀ L : SizeData₂ D, WindowsLe L → (∀ i, (rowsP D j τ i : ℝ) ≤ 3 * L.sc.b ^ 2) ∧ ∀ i, (rowsM D j τ i : ℝ) ≤ 3 * L.sc.b ^ 2 := by
  intro D j h1 h2 τ
  have hk := D.R.m_add_three_le_k
  have hq : (D.R.sigW j).2 = D.R.m - j := rfl
  have hM : ∀ i : Fin (D.R.sigW j).2, j + ((D.R.sigW j).2 - 1 - i) < D.R.m := by
    intro i
    have := i.2
    omega
  have eP : ∀ i, (rowsP D j τ i : ℝ) = DV.aPlus D j τ i := by
    intro i
    have := floor_cast_of_int (DV.aPlusQ_int D j τ i) (one_le_aPlusQ D j h1 h2 τ i)
    unfold DV.aPlus rowsP
    rw [← this]
    simp
  have eM : ∀ i, (rowsM D j τ i : ℝ) = DV.aMinus D j τ ((D.R.sigW j).2 - 1 - i) := by
    intro i
    have := floor_cast_of_int (DV.aMinusQ_int D j τ _) (one_le_aMinusQ D j h1 τ _ (hM i))
    unfold DV.aMinus rowsM
    rw [← this]
    simp
  refine ⟨⟨?_, ?_, eP⟩, ⟨?_, ?_, eM⟩, fun L hL => ⟨fun i => ?_, fun i => ?_⟩⟩
  · intro a b hab
    have hb : b.1 < D.R.k + j - 1 := b.2
    exact Nat.floor_le_floor (aPlusQ_anti D j τ (show a.1 ≤ b.1 from hab) (by omega))
  · intro i
    exact Nat.le_floor (by simpa using one_le_aPlusQ D j h1 h2 τ i)
  · intro a b hab
    have hab' : a.1 ≤ b.1 := hab
    exact Nat.floor_le_floor (aMinusQ_mono D j τ (by omega) (hM a))
  · intro i
    exact Nat.le_floor (by simpa using one_le_aMinusQ D j h1 τ _ (hM i))
  · rw [eP]
    exact aPlus_le D j h1 h2 τ L hL i
  · rw [eM]
    exact aMinus_le D j h1 τ L hL _ (hM i)

end GlobalTheory.BlockRows
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurMulDetEqDet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurMulDetEqDet
noncomputable section

open Finset
open scoped Classical

namespace GlobalTheory.JSW.Bialt

lemma coeff_prod_one_sub_eq_zero {R ι : Type*} [CommRing R] (a : ι → R) (s : Finset ι) :
    ∀ r, s.card < r →
      PowerSeries.coeff r (∏ k ∈ s, (1 - PowerSeries.C (a k) * PowerSeries.X : PowerSeries R)) = 0 := by
  induction s using Finset.induction_on with
  | empty =>
    intro r hr
    rw [prod_empty, PowerSeries.coeff_one, if_neg (by simp at hr; omega)]
  | insert k s hk ih =>
    intro r hr
    rw [card_insert_of_notMem hk] at hr
    obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    rw [prod_insert hk, sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_succ_X_mul, ih _ (by omega), ih _ (by omega), mul_zero, sub_zero]

def ec (n : ℕ) (i : Fin n) (r : ℕ) : MvPolynomial (Fin n) ℤ :=
  PowerSeries.coeff r (∏ k ∈ univ.erase i,
    (1 - PowerSeries.C (MvPolynomial.X k : MvPolynomial (Fin n) ℤ) * PowerSeries.X))

lemma ec_eq_zero {n : ℕ} (i : Fin n) {r : ℕ} (hr : n ≤ r) : ec n i r = 0 := by
  apply coeff_prod_one_sub_eq_zero
  rw [card_erase_of_mem (mem_univ i), card_univ, Fintype.card_fin]
  have := i.2
  omega

lemma sum_ec_hsymm {n : ℕ} (i : Fin n) (a : ℕ) :
    ∑ r ∈ range (a + 1), ec n i r * MvPolynomial.hsymm (Fin n) ℤ (a - r) = MvPolynomial.X i ^ a := by
  have hAB : (∏ k ∈ univ.erase i,
      (1 - PowerSeries.C (MvPolynomial.X k : MvPolynomial (Fin n) ℤ) * PowerSeries.X)) *
      (∏ j : Fin n, PowerSeries.mk (fun m => (MvPolynomial.X j : MvPolynomial (Fin n) ℤ) ^ m)) =
      PowerSeries.mk (fun m => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ m) := by
    rw [← prod_erase_mul _ _ (mem_univ i), ← mul_assoc, ← prod_mul_distrib,
      prod_eq_one fun j _ => Formalism.FT.SymmetricSeries.geom_mul _, one_mul]
  have h := congrArg (PowerSeries.coeff a) hAB
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mk, Nat.sum_antidiagonal_eq_sum_range_succ_mk] at h
  simpa only [Formalism.FT.SymmetricSeries.coeff_prod_geom, ec] using h

lemma sum_ec_hsymm' {n : ℕ} (i : Fin n) (a : ℕ) :
    ∑ r ∈ range n, ec n i r * (if a < r then 0 else MvPolynomial.hsymm (Fin n) ℤ (a - r)) =
      MvPolynomial.X i ^ a := by
  rw [← sum_ec_hsymm i a]
  have h1 : ∑ r ∈ range n, ec n i r * (if a < r then 0 else MvPolynomial.hsymm (Fin n) ℤ (a - r)) =
      ∑ r ∈ range (n + a + 1), ec n i r *
        (if a < r then 0 else MvPolynomial.hsymm (Fin n) ℤ (a - r)) := by
    refine sum_subset (range_subset_range.2 (by omega)) fun r _ hr => ?_
    rw [ec_eq_zero i (by simpa using hr), zero_mul]
  have h2 : ∑ r ∈ range (a + 1), ec n i r *
        (if a < r then 0 else MvPolynomial.hsymm (Fin n) ℤ (a - r)) =
      ∑ r ∈ range (n + a + 1), ec n i r *
        (if a < r then 0 else MvPolynomial.hsymm (Fin n) ℤ (a - r)) := by
    refine sum_subset (range_subset_range.2 (by omega)) fun r _ hr => ?_
    rw [if_pos (by simp at hr; omega), mul_zero]
  rw [h1, ← h2]
  refine sum_congr rfl fun r hr => ?_
  rw [if_neg (by simp at hr; omega)]

lemma pow_matrix_eq (n : ℕ) (α : Fin n → ℕ) :
    (Matrix.of fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (α j)) =
      (Matrix.of fun i m : Fin n => ec n i (n - 1 - m)) *
        (Matrix.of fun m j : Fin n => if α j < n - 1 - m then 0
          else MvPolynomial.hsymm (Fin n) ℤ (α j - (n - 1 - m))) := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Matrix.of_apply, ← sum_ec_hsymm' i (α j), ← sum_range_reflect,
    ← Fin.sum_univ_eq_sum_range (fun m => ec n i (n - 1 - m) * (if α j < n - 1 - m then 0
          else MvPolynomial.hsymm (Fin n) ℤ (α j - (n - 1 - m))))]
  rfl

lemma det_pow_matrix (n : ℕ) (l : Fin n → ℕ) :
    Matrix.det (Matrix.of fun i j : Fin n =>
      (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (l j + n - 1 - (j : ℕ))) =
      Matrix.det (Matrix.of fun i m : Fin n => ec n i (n - 1 - m)) * schur n l := by
  rw [pow_matrix_eq n (fun j => l j + n - 1 - (j : ℕ)), Matrix.det_mul, schur, ← Matrix.det_transpose (Matrix.of fun i j : Fin n =>
    if ((l i : ℤ) - i + j) < 0 then 0 else MvPolynomial.hsymm (Fin n) ℤ (((l i : ℤ) - i + j).toNat))]
  congr 2
  refine Matrix.ext fun m j => ?_
  simp only [Matrix.transpose_apply, Matrix.of_apply]
  have hm := m.2
  have hj := j.2
  by_cases h : ((l j : ℤ) - j + m) < 0
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]
    congr 1
    omega

lemma schur_zero (n : ℕ) : schur n (fun _ => 0) = 1 := by
  rw [schur, Matrix.det_of_upperTriangular]
  · refine prod_eq_one fun i _ => ?_
    simp [MvPolynomial.hsymm_zero]
  · intro i j hij
    have : (j : ℕ) < i := hij
    rw [Matrix.of_apply, if_pos (by push_cast; omega)]

end GlobalTheory.JSW.Bialt

namespace GlobalTheory.JSW

theorem schur_mul_det_eq_det (n : ℕ) (l : Fin n → ℕ) (_hl : Antitone l) :
    schur n l * Matrix.det (Matrix.of fun i j : Fin n =>
        (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) =
      Matrix.det (Matrix.of fun i j : Fin n =>
        (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (l j + n - 1 - (j : ℕ))) := by
  have h0 := Bialt.det_pow_matrix n (fun _ => 0)
  simp only [zero_add, Bialt.schur_zero, mul_one] at h0
  rw [h0, Bialt.det_pow_matrix n l, mul_comm]

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurMulDetEqDetStatement
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schur_mul_vandermonde_det_eq_det : ∀ (n : ℕ) (l : Fin n → ℕ), Antitone l → GlobalTheory.JSW.schur n l * Matrix.det (Matrix.of fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) = Matrix.det (Matrix.of fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (l j + n - 1 - (j : ℕ))) := by
  first | exact @GlobalTheory.JSW.schur_mul_det_eq_det | exact GlobalTheory.JSW.schur_mul_det_eq_det | (intros; apply GlobalTheory.JSW.schur_mul_det_eq_det <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerEqZeroOfNotAntitone
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerEqZeroOfNotAntitone
open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
open scoped Classical

noncomputable section

namespace GlobalTheory.JSW

theorem whittaker_eq_zero_of_not_antitone : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ), (∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (GlobalTheory.Whittaker.superDiag u) * W g) → (∀ g, ∀ k ∈ KGL w (n := n), W (g * k) = W g) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin n → ℕ, ¬ Antitone l → W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ (l) i)) = 0 := by
  intro E _ _ w n ψ hψ W hWN hWK ϖ hϖ l hl

  obtain ⟨i, j, hij, hlt⟩ : ∃ i j : Fin n, (j : ℕ) = i + 1 ∧ l i < l j := by
    by_contra h
    push_neg at h
    apply hl
    cases n with
    | zero => exact fun a => a.elim0
    | succ m =>
      rw [Fin.antitone_iff_succ_le]
      intro k
      exact h k.castSucc k.succ (by simp)
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  have hlt' : i < j := Fin.lt_def.2 (by omega)

  have hnot : ((ϖ : w.adicCompletion E))⁻¹ ∉ Ov E w := by
    intro h
    change Valued.v (((ϖ : w.adicCompletion E))⁻¹) ≤ 1 at h
    rw [map_inv₀, hϖ, ← WithZero.coe_inv, ← WithZero.coe_one, WithZero.coe_le_coe] at h
    exact absurd (Multiplicative.ofAdd_le.1 (h.trans_eq (ofAdd_zero).symm)) (by norm_num)
  obtain ⟨y, hy, hψy⟩ : ∃ y ∈ Ov E w, ψ (((ϖ : w.adicCompletion E))⁻¹ * y) ≠ 1 := by
    by_contra h
    push_neg at h
    exact hnot ((hψ _).1 h)
  set x : w.adicCompletion E := ((ϖ : w.adicCompletion E))⁻¹ * y with hx
  have hϖ0 : (ϖ : w.adicCompletion E) ≠ 0 := ϖ.ne_zero
  set m : ℕ := l j - l i with hm
  have hlj : l j = l i + m := by omega
  have hm1 : 1 ≤ m := by omega
  set c : w.adicCompletion E := (ϖ : w.adicCompletion E) ^ m * x with hc
  have hcO : c ∈ Ov E w := by
    have hϖO : (ϖ : w.adicCompletion E) ∈ Ov E w := mem_Ov_of_isUnifV hϖ
    have : c = (ϖ : w.adicCompletion E) ^ (m - 1) * y := by
      rw [hc, hx, ← mul_assoc, show m = (m - 1) + 1 by omega, pow_succ, mul_assoc _ (ϖ : w.adicCompletion E),
        mul_inv_cancel₀ hϖ0, mul_one, Nat.add_sub_cancel]
    rw [this]
    exact Subring.mul_mem _ (Subring.pow_mem _ hϖO _) hy

  let T : w.adicCompletion E → GL (Fin n) (w.adicCompletion E) := fun a =>
    ⟨Matrix.transvection i j a, Matrix.transvection i j (-a),
      by rw [Matrix.transvection_mul_transvection_same i j hne, add_neg_cancel, Matrix.transvection_zero],
      by rw [Matrix.transvection_mul_transvection_same i j hne, neg_add_cancel, Matrix.transvection_zero]⟩
  have hT : ∀ a, ((T a : GL (Fin n) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.transvection i j a := fun a => rfl
  have hentry : ∀ {R : Type} [CommRing R] (a : R) (p q : Fin n), Matrix.transvection i j a p q =
      (if p = q then 1 else 0) + (if i = p ∧ j = q then a else 0) := by
    intro R _ a p q
    simp [Matrix.transvection, Matrix.one_apply, Matrix.single_apply]

  have hu : T x ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n) := by
    refine (GlobalTheory.SmGL.mem_unipB _).2 ⟨fun p q hqp => ?_, fun p => ?_⟩
    · rw [hT, hentry, if_neg (fun h => by rw [h] at hqp; exact lt_irrefl _ hqp), if_neg, add_zero]
      rintro ⟨rfl, rfl⟩
      exact lt_asymm hqp hlt'
    · rw [hT, hentry, if_pos rfl, if_neg, add_zero]
      rintro ⟨rfl, h⟩
      exact hne h.symm
  have hsd : GlobalTheory.Whittaker.superDiag (T x) = x := by
    unfold GlobalTheory.Whittaker.superDiag
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · rw [hT, hentry, if_neg hne, if_pos ⟨rfl, rfl⟩, zero_add]
      · intro b hb hbj
        have hb' := (Finset.mem_filter.1 hb).2
        rw [hT, hentry, if_neg (fun h => by rw [← h] at hb'; omega), if_neg (fun h => hbj h.2.symm), add_zero]
      · intro hj
        exact absurd (Finset.mem_filter.2 ⟨Finset.mem_univ j, hij⟩) hj
    · intro a _ hai
      refine Finset.sum_eq_zero fun b hb => ?_
      have hb' := (Finset.mem_filter.1 hb).2
      rw [hT, hentry, if_neg (fun h => by rw [← h] at hb'; omega), if_neg (fun h => hai h.1.symm), add_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h

  have hk : T c ∈ KGL w (n := n) := by
    refine ⟨⟨Matrix.transvection i j ⟨c, hcO⟩, Matrix.transvection i j (-⟨c, hcO⟩),
      by rw [Matrix.transvection_mul_transvection_same i j hne, add_neg_cancel, Matrix.transvection_zero],
      by rw [Matrix.transvection_mul_transvection_same i j hne, neg_add_cancel, Matrix.transvection_zero]⟩, ?_⟩
    apply Units.ext
    ext p q
    simp only [Formalism.UG.bc, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply, hT]
    rw [hentry, hentry]
    split_ifs <;> simp

  set D := Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom
    (MulEquiv.piUnits.symm fun i => ϖ ^ (l) i) with hD
  have hDv : (D : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.diagonal fun a => (ϖ : w.adicCompletion E) ^ l a := by
    rw [hD]
    ext p q
    simp [Matrix.diagonal_apply]
  have hkey : D * T c = T x * D := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hDv, hT, hT]
    ext p q
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, hentry, hentry]
    by_cases hpq : i = p ∧ j = q
    · obtain ⟨rfl, rfl⟩ := hpq
      rw [if_neg hne, if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, zero_add, zero_add, hc, hlj, pow_add]
      congr 1
      ring
    · simp only [if_neg hpq, add_zero]
      split_ifs with h
      · subst h
        simp
      · simp
  have h1 := hWK D (T c) hk
  rw [hkey, hWN (T x) hu D, hsd] at h1
  have h2 : (ψ x - 1) * W D = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 hψy)

end GlobalTheory.JSW
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerEqZeroOfNotAntitoneStatement
open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_diagonal_eq_zero_of_not_antitone : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ), (∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (GlobalTheory.Whittaker.superDiag u) * W g) → (∀ g, ∀ k ∈ KGL w (n := n), W (g * k) = W g) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin n → ℕ, ¬ Antitone l → W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ (l) i)) = 0 := by
  first | exact @GlobalTheory.JSW.whittaker_eq_zero_of_not_antitone | exact GlobalTheory.JSW.whittaker_eq_zero_of_not_antitone | (intros; apply GlobalTheory.JSW.whittaker_eq_zero_of_not_antitone <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNormOne
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.PlaneNorm

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def gram2E (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x z : Fin M → E) : E :=
  hE σ J x x * hE σ J z z - hE σ J x z * hE σ J z x

def gram2R (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (a b : Fin M → R ⊗[F] E) : R ⊗[F] E :=
  hR R σ J a a * hR R σ J b b - hR R σ J a b * hR R σ J b a

def IsUnitNorm (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (a : R ⊗[F] E) : Prop :=
  ∃ s : R ⊗[F] E, IsUnit s ∧ s * sigR R σ s = a

theorem IsUnitNorm.isUnit {R : Type} [CommRing R] [Algebra F R] {σ : E →ₐ[F] E} {a : R ⊗[F] E}
    (h : IsUnitNorm R σ a) : IsUnit a := by
  obtain ⟨s, hs, rfl⟩ := h
  exact hs.mul (hs.map (sigR R σ))

end GlobalTheory.PlaneNorm
end
end
