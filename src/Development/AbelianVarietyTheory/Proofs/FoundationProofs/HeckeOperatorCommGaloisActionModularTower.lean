module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueModPrimePowDiamondIndepende
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesCoeffRingHomMapCoeff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisActionUpperTriangularHeckeReindexOnB
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpUpperInt
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem Tower.exp_upper_int {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (a b d : ℤ)
    (ha : 0 < a) (hd : 0 < d) (f : X.K) (r : ℚ) :
    (X.exp (X.sl (toGQ !![a, b; 0, d]) f)).coeff (r * a / d) = eOm ε (r * b / d) * (X.exp f).coeff r := by
  have hdet : (0 : ℤ) < (!![a, b; 0, d] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two]; positivity
  have e : ∀ i j, ent (toGQ !![a, b; 0, d]) i j = ((!![a, b; 0, d] : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) := by
    intro i j; rw [ent, toGQ, dite_eq_left hdet]; rfl
  have h := X.exp_upper (toGQ !![a, b; 0, d]) (by rw [e]; simp) f r
  simpa [e] using h

end GlobalTheory.KZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisActionUpperTriangularHeckeReindexOnB
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.GalUpper

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

theorem map_eq_zpow_of_pow_eq_one (s : Ω ≃ₐ[ℚ] Ω) {L : ℕ} (hL : 0 < L) {e : ℤ}
    (he : ∀ ζ : Ω, IsPrimitiveRoot ζ L → s ζ = ζ ^ e) {ω : Ω} (hω : ω ^ L = 1) : s ω = ω ^ e := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω L
  obtain ⟨i, -, rfl⟩ := hξ.eq_pow_of_pow_eq_one hω
  rw [map_pow, he ξ hξ, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]

theorem eOm_mul_int (ε : Ω →+* ℂ) (x : ℚ) (k : ℤ) : eOm ε (x * k) = eOm ε x ^ k := by
  apply ε.injective
  rw [map_zpow₀, eOm_spec ε ε.injective, eOm_spec ε ε.injective, ← Complex.exp_int_mul]
  congr 1; push_cast; ring

theorem gal_sl_upper (ε : Ω →+* ℂ) (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (M q : ℕ) (hq : 0 < q) (e : ℤ)
    (he : ∀ ω : Ω, ω ^ (M * q) = 1 → s ω = ω ^ e) (j : ℤ) (f : X.K)
    (hf : ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) :
    X.gal s (X.sl (toGQ !![1, j; 0, (q : ℤ)]) f) = X.sl (toGQ !![1, j * e; 0, (q : ℤ)]) (X.gal s f) := by
  have hq0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have key : ∀ (a : ℤ) (g : X.K) (t : ℚ), (X.exp (X.sl (toGQ !![1, a; 0, (q : ℤ)]) g)).coeff t =
      eOm ε (t * a) * (X.exp g).coeff (t * q) := by
    intro a g t
    have h := Tower.exp_upper_int ε X 1 a q one_pos (by exact_mod_cast hq) g (t * q)
    have e1 : t * q * ((1 : ℤ) : ℚ) / ((q : ℤ) : ℚ) = t := by push_cast; field_simp
    have e2 : t * q * (a : ℚ) / ((q : ℤ) : ℚ) = t * a := by push_cast; field_simp
    rwa [e1, e2] at h
  apply (X.exp : X.K →+* HahnSeries ℚ Ω).injective
  ext t
  change (X.exp (X.gal s _)).coeff t = (X.exp (X.sl _ _)).coeff t
  rw [X.gal_exp, key, key, X.gal_exp, map_mul]
  by_cases h0 : (X.exp f).coeff (t * q) = 0
  · rw [h0, map_zero, mul_zero, mul_zero]
  · congr 1
    have h1 := GlobalTheory.KroneckerCongruence.eOm_level X M f hf _ h0
    have h2 : eOm ε (t * j) ^ (M * q) = 1 := by
      rw [← zpow_natCast, ← eOm_mul_int,
        show t * j * (((M * q : ℕ) : ℤ) : ℚ) = t * q * M * j by push_cast; ring, eOm_mul_int, h1, _root_.one_zpow]
    rw [he _ h2, ← eOm_mul_int]
    congr 1; push_cast; ring


omit [IsAlgClosure ℚ Ω] in
theorem eval_eq_zero_of_mem {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n : ℕ) (φ : X.K ≃+* X.K)
    {x : X.Khat l} (hx : x ∈ (idl l) ^ n • (⊤ : Submodule ℤ_[l] (X.Khat l))) :
    AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ x) = 0 := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr y _
    rw [map_smul, map_smul]
    obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (idl l) (X.Kl l) n (X.kmap l φ y))
    rw [← hz, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro x y hx hy
    rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]


omit [IsAlgClosure ℚ Ω] in
theorem act_upper_add {ε : Ω →+* ℂ} (X : Tower Ω ε) {N l w : ℕ} [Fact l.Prime] {b : X.Fn l} (hb : b ∈ X.B N l w)
    (q : ℕ) (hq : 0 < q) (a t : ℤ) :
    X.act l !![1, a + t * q; 0, (q : ℤ)] b = X.act l !![1, a; 0, (q : ℤ)] b := by
  let γ : SL(2, ℤ) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hγ : γ ∈ Gam N l := by
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [CongruenceSubgroup.Gamma1_mem]; simp [γ]
    · rw [CongruenceSubgroup.Gamma0_mem]; simp [γ]
  have hinv : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
    induction hb using Submodule.span_induction with
    | mem x hx => exact hx.2 γ hγ
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  have hm : (!![1, a + t * q; 0, (q : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, a; 0, (q : ℤ)] := by
    simp [γ]
  rw [hm, ← Tower.act_act Ω ε X l _ _ (by rw [γ.det_coe]; exact one_pos)
    (by simp [Matrix.det_fin_two]; exact hq), hinv]

theorem galB_act_upper : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ (s : Ω ≃ₐ[ℚ] Ω) (q : ℕ) (e : ℤ), 0 < q → (∀ ζ : Ω, IsPrimitiveRoot ζ q → s ζ = ζ ^ e) → ∀ (j : ℤ), ∀ b ∈ X.B N l w, X.galB l s (X.act l !![1, j; 0, (q : ℤ)] b) = X.act l !![1, j * e; 0, (q : ℤ)] (X.galB l s b) := by
  intro Ω _ _ _ ε X hε hj N l w _ hl hN hNl hw s q e hq he j b hb
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero q := ⟨hq.ne'⟩
  have hlp : l.Prime := Fact.out
  have hb' := GlobalTheory.T.galB_mem_kummer_invariant_set ε X hε hj N l w hl hN hNl hw s b hb
  funext u
  apply AdicCompletion.ext
  intro n
  set χ : ℤ_[l] := (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) with hχ
  set v : Fin 2 → ℤ_[l] := mZl l !![1, j; 0, (q : ℤ)] *ᵥ ![u 0, χ * u 1] with hv
  obtain ⟨M, hM, hred⟩ := GlobalTheory.T.towerPadicCompletionMap_eval_depends_on_level X l (b v) n
  have hL : 0 < M * q * l ^ n := Nat.mul_pos (Nat.mul_pos hM hq) (pow_pos hlp.pos n)
  obtain ⟨d, hd, hdχ⟩ := GlobalTheory.T.exists_int_exponent_congr_cyclotomicCharacter l s n (M * q * l ^ n) hL (dvd_mul_left _ _)
  have hd' : ∀ ω : Ω, ω ^ (M * q) = 1 → s ω = ω ^ d := fun ω hω =>
    map_eq_zpow_of_pow_eq_one s hL hd (by rw [pow_mul, hω, one_pow])
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω q
  have hξ0 : ξ ≠ 0 := hξ.ne_zero hq.ne'
  have hde : (q : ℤ) ∣ d - e := by
    rw [← hξ.zpow_eq_one_iff_dvd, zpow_sub₀ hξ0, ← he ξ hξ,
      ← hd' ξ (by rw [mul_comm, pow_mul, hξ.pow_eq_one, one_pow])]
    exact div_self ((map_ne_zero s).2 hξ0)
  obtain ⟨t, ht⟩ := hde
  have hjd : j * d = j * e + (j * t) * q := by linear_combination j * ht
  rw [← act_upper_add X hb' q hq (j * e) (j * t), ← hjd]
  set v' : Fin 2 → ℤ_[l] := mZl l !![1, j * d; 0, (q : ℤ)] *ᵥ u with hv'
  change AdicCompletion.eval (idl l) (X.Kl l) n
      (X.kmap l (X.gal s) (X.kmap l (X.sl (toGQ !![1, j; 0, (q : ℤ)])).toRingEquiv (b v))) =
    AdicCompletion.eval (idl l) (X.Kl l) n
      (X.kmap l (X.sl (toGQ !![1, j * d; 0, (q : ℤ)])).toRingEquiv (X.kmap l (X.gal s) (b ![v' 0, χ * v' 1])))
  rw [Tower.kmap_kmap, Tower.kmap_kmap,
    hred _ ((X.gal s).trans (X.sl (toGQ !![1, j * d; 0, (q : ℤ)])).toRingEquiv)
      (fun f hf => gal_sl_upper ε X s M q hq d hd' j f hf), ← sub_eq_zero, ← map_sub, ← map_sub]
  apply eval_eq_zero_of_mem
  refine GlobalTheory.T.bettiFunction_sub_mem_of_columns_congr X N l w b hb n _ _ ?_
  intro i
  fin_cases i
  · have h := Ideal.mul_mem_left _ (-((j : ℤ_[l]) * u 1)) hdχ
    convert h using 1
    simp [hv, hv', mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · convert Ideal.zero_mem _
    simp [hv, hv', mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring

end GlobalTheory.KZ.GalUpper
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisActionUpperTriangularHeckeReindexOnBStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisAction_upperTriangular_hecke_reindex_on_B : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ (s : Ω ≃ₐ[ℚ] Ω) (q : ℕ) (e : ℤ), 0 < q → (∀ ζ : Ω, IsPrimitiveRoot ζ q → s ζ = ζ ^ e) → ∀ (j : ℤ), ∀ b ∈ X.B N l w, X.galB l s (X.act l !![1, j; 0, (q : ℤ)] b) = X.act l !![1, j * e; 0, (q : ℤ)] (X.galB l s b) := by
  first | exact @GlobalTheory.KZ.GalUpper.galB_act_upper | exact GlobalTheory.KZ.GalUpper.galB_act_upper | (intros; apply GlobalTheory.KZ.GalUpper.galB_act_upper <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBActDiagNatOneComm
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBActDiagNatOneComm
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem toGQ_diag_nat_one_ent (q : ℕ) (hq : 0 < q) :
    ent (toGQ !![(q : ℤ), 0; 0, 1]) 0 0 = (q : ℚ) ∧ ent (toGQ !![(q : ℤ), 0; 0, 1]) 0 1 = 0 ∧
    ent (toGQ !![(q : ℤ), 0; 0, 1]) 1 0 = 0 ∧ ent (toGQ !![(q : ℤ), 0; 0, 1]) 1 1 = 1 := by
  have h : (0 : ℤ) < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    rw [Matrix.det_fin_two_of]; omega
  unfold ent toGQ
  rw [dite_eq_left h]
  simp

theorem eOm_zero_of_injective_diag {Ω : Type} [Field Ω] (ε : Ω →+* ℂ) (hε : Function.Injective ε) : eOm ε 0 = 1 := by
  unfold eOm
  simp only [Rat.cast_zero, mul_zero, Complex.exp_zero]
  rw [← map_one ε]
  exact Function.leftInverse_invFun hε 1

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem Tower.exp_sl_diag_coeff (X : Tower Ω ε) (hε : Function.Injective ε) (q : ℕ) (hq : 0 < q) (f : X.K) (r : ℚ) :
    (X.exp (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) f)).coeff r = (X.exp f).coeff (r / q) := by
  obtain ⟨h00, h01, h10, h11⟩ := toGQ_diag_nat_one_ent q hq
  have hqQ : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  have h := X.exp_upper _ h10 f (r / q)
  rw [h00, h01, h11, mul_zero, zero_div, eOm_zero_of_injective_diag ε hε, one_mul, div_one, div_mul_cancel₀ r hqQ] at h
  exact h

theorem Tower.gal_sl_diag (X : Tower Ω ε) (hε : Function.Injective ε) (q : ℕ) (hq : 0 < q)
    (s : Ω ≃ₐ[ℚ] Ω) (f : X.K) :
    X.gal s (X.sl (toGQ !![(q : ℤ), 0; 0, 1]) f) = X.sl (toGQ !![(q : ℤ), 0; 0, 1]) (X.gal s f) := by
  apply RingHom.injective X.exp.toRingHom
  ext r
  show (X.exp _).coeff r = (X.exp _).coeff r
  rw [X.gal_exp, X.exp_sl_diag_coeff hε q hq, X.exp_sl_diag_coeff hε q hq, X.gal_exp]

theorem mZl_diag_nat_one_mulVec (l : ℕ) [Fact l.Prime] (q : ℕ) (c : ℤ_[l]) (u : Fin 2 → ℤ_[l]) :
    mZl l !![(q : ℤ), 0; 0, 1] *ᵥ ![u 0, c * u 1] =
      ![(mZl l !![(q : ℤ), 0; 0, 1] *ᵥ u) 0, c * (mZl l !![(q : ℤ), 0; 0, 1] *ᵥ u) 1] := by
  funext i
  fin_cases i <;> simp [mZl, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem Tower.galB_act_diag : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → ∀ (l : ℕ) [Fact l.Prime] (q : ℕ), 0 < q → ∀ (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l),
      X.galB l s (X.act l !![(q : ℤ), 0; 0, 1] b) = X.act l !![(q : ℤ), 0; 0, 1] (X.galB l s b) := by
  intro Ω _ _ ε X hε l _ q hq s b
  funext u
  simp only [Tower.galB, Tower.act, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Tower.kmap_kmap, Tower.kmap_kmap, mZl_diag_nat_one_mulVec]
  have hφ : (X.sl (toGQ !![(q : ℤ), 0; 0, 1])).toRingEquiv.trans (X.gal s) =
      (X.gal s).trans (X.sl (toGQ !![(q : ℤ), 0; 0, 1])).toRingEquiv :=
    RingEquiv.ext fun f => X.gal_sl_diag hε q hq s f
  rw [hφ]

end GlobalTheory.KZ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBActDiagNatOneCommStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galB_act_diagNatOne_comm : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → ∀ (l : ℕ) [Fact l.Prime] (q : ℕ), 0 < q → ∀ (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l), X.galB l s (X.act l !![(q : ℤ), 0; 0, 1] b) = X.act l !![(q : ℤ), 0; 0, 1] (X.galB l s b) := by
  first | exact @GlobalTheory.KZ.Tower.galB_act_diag | exact GlobalTheory.KZ.Tower.galB_act_diag | (intros; apply GlobalTheory.KZ.Tower.galB_act_diag <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiamondMatrixGamma1Gamma0OfCoprime
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiamondMatrixGamma1Gamma0OfCoprime
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem diam_exists : ∀ (N l d : ℕ), 0 < N → Nat.Coprime N l → Nat.Coprime d N → ∃ γ : SL(2, ℤ), IsDiam N l d γ := by
  intro N l d _ hNl hdN

  obtain ⟨d', hd'N, hd'l⟩ := Nat.chineseRemainder hNl d 1
  have h1 : Nat.Coprime d' N := by
    unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq hd'N]; exact hdN
  have h2 : Nat.Coprime d' l := by
    unfold Nat.Coprime; rw [Nat.ModEq.gcd_eq hd'l]; simp
  have h3 : Nat.Coprime d' (N * l) := Nat.Coprime.mul_right h1 h2
  have hg : Int.gcd (d' : ℤ) ((N * l : ℕ) : ℤ) = 1 := by rw [Int.gcd_natCast_natCast]; exact h3
  have hb := Int.gcd_eq_gcd_ab (d' : ℤ) ((N * l : ℕ) : ℤ)
  rw [hg] at hb
  set a := Int.gcdA (d' : ℤ) ((N * l : ℕ) : ℤ)
  set b := Int.gcdB (d' : ℤ) ((N * l : ℕ) : ℤ)
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![a, -b; ((N * l : ℕ) : ℤ), (d' : ℤ)]
  have hdet : M.det = 1 := by
    simp only [M, Matrix.det_fin_two_of]
    push_cast at hb ⊢
    linarith
  let γ : SL(2, ℤ) := ⟨M, hdet⟩
  have hγ : (γ : Matrix (Fin 2) (Fin 2) ℤ) = M := rfl
  refine ⟨γ, Subgroup.mem_inf.2 ⟨CongruenceSubgroup.Gamma0_mem.2 ?_, CongruenceSubgroup.Gamma0_mem.2 ?_⟩, ?_⟩
  · rw [hγ]; simp [M]
  · rw [hγ]; simp [M]
  · simp only [en, hγ, M]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_one, Matrix.head_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.cons_val_zero]
    push_cast
    exact (ZMod.natCast_eq_natCast_iff _ _ _).2 hd'N

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiamondMatrixGamma1Gamma0OfCoprimeStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isDiamondMatrixGamma1Gamma0_of_coprime : ∀ (N l d : ℕ), 0 < N → Nat.Coprime N l → Nat.Coprime d N → ∃ γ : SL(2, ℤ), IsDiam N l d γ := by
  first | exact @GlobalTheory.diam_exists | exact GlobalTheory.diam_exists | (intros; apply GlobalTheory.diam_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalAlgClosureRatPrimitiveRootEqPow
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalAlgClosureRatPrimitiveRootEqPow
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem algEquiv_primitiveRoot_pow :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (q : ℕ), 0 < q →
      ∃ e : ℤ, IsCoprime e (q : ℤ) ∧ ∀ ζ : Ω, IsPrimitiveRoot ζ q → s ζ = ζ ^ e := by
  intro Ω _ _ _ s q hq
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero q := ⟨hq.ne'⟩
  haveI : NeZero (q : Ω) := ⟨Nat.cast_ne_zero.mpr hq.ne'⟩
  obtain ⟨ζ₀, hζ₀⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic q Ω)
    (by rw [Polynomial.degree_cyclotomic]; exact_mod_cast (Nat.totient_pos.mpr hq).ne')
  have h0 : IsPrimitiveRoot ζ₀ q := (Polynomial.isRoot_cyclotomic_iff).mp hζ₀
  have h1 : IsPrimitiveRoot (s ζ₀) q := h0.map_of_injective s.injective
  obtain ⟨i, -, hi⟩ := h0.eq_pow_of_pow_eq_one h1.pow_eq_one
  have hcop : i.Coprime q := (h0.pow_iff_coprime hq i).mp (hi ▸ h1)
  refine ⟨(i : ℤ), Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd] using hcop), ?_⟩
  intro ζ hζ
  obtain ⟨k, -, hk⟩ := h0.eq_pow_of_pow_eq_one hζ.pow_eq_one
  subst hk
  rw [zpow_natCast, map_pow, ← hi, ← pow_mul, ← pow_mul, mul_comm]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalAlgClosureRatPrimitiveRootEqPowStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galAlgClosureRat_primitiveRoot_eq_pow : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (s : Ω ≃ₐ[ℚ] Ω) (q : ℕ), 0 < q → ∃ e : ℤ, IsCoprime e (q : ℤ) ∧ ∀ ζ : Ω, IsPrimitiveRoot ζ q → s ζ = ζ ^ e := by
  first | exact @GlobalTheory.algEquiv_primitiveRoot_pow | exact GlobalTheory.algEquiv_primitiveRoot_pow | (intros; apply GlobalTheory.algEquiv_primitiveRoot_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorCommGaloisActionModularTower
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.HeckeGal

theorem B_inv {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime]
    (b : X.Fn l) (hb : b ∈ X.B N l w) (γ : SL(2, ℤ)) (hγ : γ ∈ Gam N l) :
    X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx.2 γ hγ
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
  | smul a x _ hx => rw [map_smul, hx]

def trSL (t : ℤ) : SL(2, ℤ) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two_of]⟩

theorem trSL_mem_Gam (N l : ℕ) (t : ℤ) : trSL t ∈ Gam N l := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]; simp [trSL]
  · rw [CongruenceSubgroup.Gamma0_mem]; simp [trSL]

theorem B_inv_tr {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime]
    (b : X.Fn l) (hb : b ∈ X.B N l w) (t : ℤ) : X.act l !![1, t; 0, 1] b = b :=
  B_inv X N l w b hb (trSL t) (trSL_mem_Gam N l t)

theorem op_galB_comm : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ T : Letter, admitted N l T → ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ b ∈ X.B N l w, X.op N l T (X.galB l s b) = X.galB l s (X.op N l T b) := by
  intro Ω _ _ _ ε X hε hj N l w _ hl hN hNl hw T hT s b hb
  have hgb : X.galB l s b ∈ X.B N l w := GlobalTheory.T.galB_mem_kummer_invariant_set ε X hε hj N l w hl hN hNl hw s b hb
  have hinv := B_inv_tr X N l w _ hgb

  have hup : ∀ q : ℕ, 0 < q →
      (∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)]) (X.galB l s b) =
        X.galB l s ((∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)]) b) := by
    intro q hq
    obtain ⟨e, he, hζ⟩ := GlobalTheory.T.galAlgClosureRat_primitiveRoot_eq_pow s q hq
    set_option synthInstance.maxHeartbeats 100000 in
      rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
    rw [← GlobalTheory.T.sum_act_upperTriangular_hecke_reindex_coprime_unit X l _ hinv q e hq he]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (GlobalTheory.T.galoisAction_upperTriangular_hecke_reindex_on_B ε X hε hj N l w hl hN hNl hw s q e hq hζ (j : ℤ) b hb).symm

  have hdiam : ∀ d : ℕ, Nat.Coprime d N → sgD N l d ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l := by
    intro d hd
    have hex := GlobalTheory.T.exists_isDiamondMatrixGamma1Gamma0_of_coprime N l d (by omega) hNl hd
    exact (Classical.epsilon_spec hex).1
  cases T with
  | T q =>
    obtain ⟨hqp, hqd⟩ := hT
    have hqN : Nat.Coprime q N :=
      (Nat.Coprime.coprime_dvd_right (Dvd.intro l rfl) ((Nat.Prime.coprime_iff_not_dvd hqp).mpr hqd))
    have hq : 0 < q := hqp.pos
    simp only [Tower.op, Tower.heckeT, LinearMap.add_apply, map_add (f := _)]
    rw [hup q hq]
    congr 1
    have hdet1 : 0 < (sgD N l q : Matrix (Fin 2) (Fin 2) ℤ).det := by
      rw [(sgD N l q).2]; exact one_pos
    have hdet2 : 0 < (!![(q : ℤ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ).det := by
      simp [Matrix.det_fin_two_of]; exact_mod_cast hq
    rw [← Tower.act_act Ω ε X l _ _ hdet1 hdet2, ← Tower.act_act Ω ε X l _ _ hdet1 hdet2,
      GlobalTheory.T.galB_act_diagNatOne_comm ε X hε l q hq s,
      GlobalTheory.T.galB_act_comm_gamma0CapGamma0Level_shimuraReciprocity ε X hε hj N l w hl hN hNl hw (sgD N l q) (hdiam q hqN) s b hb]
  | U =>
    simp only [Tower.op, Tower.heckeU]
    exact hup l (Fact.out : l.Prime).pos
  | D d =>
    simp only [Tower.op, Tower.diam]
    exact (GlobalTheory.T.galB_act_comm_gamma0CapGamma0Level_shimuraReciprocity ε X hε hj N l w hl hN hNl hw (sgD N l d) (hdiam d hT) s b hb).symm

end GlobalTheory.KZ.HeckeGal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeOperatorCommGaloisActionModularTowerStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_operator_comm_galois_action_modular_tower : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ T : Letter, admitted N l T → ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ b ∈ X.B N l w, X.op N l T (X.galB l s b) = X.galB l s (X.op N l T b) := by
  first | exact @GlobalTheory.KZ.HeckeGal.op_galB_comm | exact GlobalTheory.KZ.HeckeGal.op_galB_comm | (intros; apply GlobalTheory.KZ.HeckeGal.op_galB_comm <;> assumption)
end
