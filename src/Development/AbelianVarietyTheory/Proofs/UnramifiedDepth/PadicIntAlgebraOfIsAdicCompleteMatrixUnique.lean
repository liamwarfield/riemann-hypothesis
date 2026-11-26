module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicIntAlgebraOfIsAdicCompleteMatrixUnique
namespace GlobalTheory.ChF

private theorem nonempty_padicInt_ringHom (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    (I : Ideal O) [IsAdicComplete I O] (hp : (p : O) ∈ I) : Nonempty (ℤ_[p] →+* O) := by
  have hd : ∀ n : ℕ, ringChar (O ⧸ I ^ n) ∣ p ^ n := fun n => by
    apply ringChar.dvd
    rw [← map_natCast (Ideal.Quotient.mk (I ^ n)), Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
    exact Ideal.pow_mem_pow hp n
  refine ⟨IsAdicComplete.liftRingHom I
    (fun n => (ZMod.castHom (hd n) (O ⧸ I ^ n)).comp (PadicInt.toZModPow n)) ?_⟩
  intro m n hle
  rw [← PadicInt.zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
  congr 1
  exact RingHom.ext_zmod _ _

private theorem padicInt_ringHom_matrix_ext (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    [IsHausdorff (Ideal.span {(p : O)}) O] (n : ℕ)
    (f g : ℤ_[p] →+* Matrix (Fin n) (Fin n) O) (c : ℤ_[p]) : f c = g c := by
  ext i j
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := Ideal.span {(p : O)}) inferInstance _ fun k => ?_
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec k c)
  have hc : c = (c.appr k : ℤ_[p]) + ((p ^ k : ℕ) : ℤ_[p]) * d := by
    rw [Nat.cast_pow, ← hd]; ring
  have h : f c - g c = (p ^ k : ℕ) • (f d - g d) := by
    rw [hc]
    simp only [map_add (f := _), map_mul, map_natCast, nsmul_eq_mul, mul_sub]
    abel
  have h' : f c i j - g c i j = (p : O) ^ k * (f d i j - g d i j) := by
    have := congrFun (congrFun h i) j
    rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.sub_apply, nsmul_eq_mul, Nat.cast_pow] at this
    exact this
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, h']
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem padicInt_algebra_of_isAdicComplete_and_matrix_unique :
    ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsAdicComplete (Ideal.span {(p : O)}) O],
      Nonempty (Algebra ℤ_[p] O) ∧ ∀ [Algebra ℤ_[p] O] (n : ℕ)
        (f : ℤ_[p] →+* Matrix (Fin n) (Fin n) O) (c : ℤ_[p]),
        f c = algebraMap ℤ_[p] O c • (1 : Matrix (Fin n) (Fin n) O) := by
  intro p _ O _ _
  refine ⟨?_, fun n f c => ?_⟩
  · obtain ⟨φ⟩ := nonempty_padicInt_ringHom p O _ (Ideal.mem_span_singleton_self _)
    exact ⟨φ.toAlgebra⟩
  · rw [padicInt_ringHom_matrix_ext p O n f
      ((algebraMap O (Matrix (Fin n) (Fin n) O)).comp (algebraMap ℤ_[p] O)) c,
      RingHom.comp_apply, Algebra.algebraMap_eq_smul_one (A := Matrix (Fin n) (Fin n) O)]

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FrobeniusPowerEmbeddings
namespace GlobalTheory

theorem exists_forall_eq_pow_of_finite_field (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Finite F]
    (k : Type) [Field k] [CharP k p] (a b : F →+* k) : ∃ n : ℕ, ∀ x, b x = a x ^ p ^ n := by
  have : CharP F p := RingHom.charP a a.injective p
  let : Algebra (ZMod p) F := ZMod.algebra F p
  let : Algebra (ZMod p) k := ZMod.algebra k p
  let : Algebra F k := a.toAlgebra
  have : IsScalarTower (ZMod p) F k :=
    IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let b' : F →ₐ[ZMod p] k :=
    { b with
      commutes' := fun r => RingHom.congr_fun
        (Subsingleton.elim (b.comp (algebraMap (ZMod p) F)) (algebraMap (ZMod p) k)) r }
  obtain ⟨n, hn⟩ := FiniteField.exists_forall_apply_eq_pow (ZMod p) p F (b'.restrictNormal' F)
  refine ⟨n, fun x => ?_⟩
  have h := AlgHom.restrictNormal_commutes b' F x
  have h2 : b'.restrictNormal F x = x ^ p ^ n := by
    have := hn x
    rw [Nat.card_zmod] at this
    exact this
  rw [h2, map_pow] at h
  exact h.symm

theorem exists_forall_eq_pow_of_ker_le (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE]
    [Module.Finite ℤ OE] (k : Type) [Field k] [CharP k p] (σ₀ σ : OE →+* k)
    (h : ∀ x, σ₀ x = 0 → σ x = 0) : ∃ n : ℕ, ∀ x, σ x = σ₀ x ^ p ^ n := by
  let I : Ideal OE := RingHom.ker σ₀
  have : I.IsPrime := RingHom.ker_isPrime σ₀
  have hp : (p : OE ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
    simp [I, RingHom.mem_ker]
  have : Module.Finite ℤ (OE ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mk I).toIntAlgHom.toLinearMap
      Ideal.Quotient.mk_surjective
  have : Finite (OE ⧸ I) := by
    refine Module.finite_of_fg_torsion _ (fun x => ⟨⟨(p : ℤ), ?_⟩, ?_⟩)
    · exact mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
    · change (p : ℤ) • x = 0
      rw [zsmul_eq_mul, Int.cast_natCast, hp, zero_mul]
  let : Field (OE ⧸ I) := (Finite.isField_of_domain (OE ⧸ I)).toField
  obtain ⟨n, hn⟩ := exists_forall_eq_pow_of_finite_field p (OE ⧸ I) k
    (Ideal.Quotient.lift I σ₀ (fun _ hx => hx)) (Ideal.Quotient.lift I σ (fun x hx => h x hx))
  exact ⟨n, fun x => hn (Ideal.Quotient.mk I x)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsMulInvolutionAddOneMemPow
namespace GlobalTheory.NormResidue

open Polynomial

theorem exists_mul_involution_eq_neg_one {k : Type*} [Field k] [Finite k] (σ : k →+* k)
    (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x) (h2 : (2 : k) ≠ 0) :
    ∃ z : k, z * σ z + 1 = 0 := by
  classical
  obtain ⟨x, hx⟩ := hne
  let F : Subfield k := σ.eqLocusField (RingHom.id k)
  let _ : Fintype F := Fintype.ofFinite F
  have memF : ∀ y : k, y ∈ F ↔ σ y = y := fun y => Iff.rfl
  have hθ : σ (x - σ x) = -(x - σ x) := by rw [map_sub, hσ]; ring
  have hθ0 : x - σ x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  let d : F := ⟨(x - σ x) * (x - σ x), (memF _).2 (by rw [map_mul, hθ]; ring)⟩
  have hd0 : d ≠ 0 := by
    intro h
    have h' : (x - σ x) * (x - σ x) = 0 := congrArg Subtype.val h
    exact hθ0 (mul_self_eq_zero.mp h')
  have hchar : ringChar F ≠ 2 := by
    intro hc
    apply h2
    have h0 : ((2 : ℕ) : F) = 0 := by rw [← hc]; exact ringChar.Nat.cast_ringChar
    have h0' := congrArg F.subtype h0
    rwa [map_natCast, map_zero, Nat.cast_ofNat] at h0'
  obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic (R := F)
    (f := Polynomial.X ^ 2 + Polynomial.C 1) (g := Polynomial.C (-d) * Polynomial.X ^ 2)
    (Polynomial.degree_X_pow_add_C (by norm_num) _)
    (Polynomial.degree_C_mul_X_pow 2 (neg_ne_zero.mpr hd0))
    (FiniteField.odd_card_of_char_ne_two hchar)
  have hab' := congrArg Subtype.val hab
  simp [d] at hab'
  have ha : σ a = a := (memF _).1 a.2
  have hb : σ b = b := (memF _).1 b.2
  refine ⟨a + b * (x - σ x), ?_⟩
  rw [map_add (f := _), map_mul, ha, hb, hθ]
  linear_combination hab'

theorem exists_mul_involution_add_one_mem_pow (O : Type) [CommRing O] (s : O →+* O)
    (hs : ∀ x, s (s x) = x) (P : Ideal O) [hP : P.IsMaximal] [Finite (O ⧸ P)]
    (hsP : ∀ x ∈ P, s x ∈ P) (hne : ∃ x, s x - x ∉ P) (h2 : (2 : O) ∉ P) (N : ℕ) (z0 : O)
    (hz : N = 0 ∨ z0 * s z0 + 1 ∈ P ^ N) :
    ∃ z : O, z * s z + 1 ∈ P ^ (N + 1) ∧ (N ≠ 0 → z - z0 ∈ P ^ N) := by
  classical
  have hPP : P ≤ P.comap s := fun x hx => hsP x hx
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    letI : Field (O ⧸ P) := Ideal.Quotient.field P
    let σ := Ideal.quotientMap P s hPP
    have hσ : ∀ x, σ (σ x) = x := by
      intro x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      simp only [σ, Ideal.quotientMap_mk, hs]
    have hne' : ∃ x, σ x ≠ x := by
      obtain ⟨x, hx⟩ := hne
      refine ⟨Ideal.Quotient.mk P x, fun h => hx ?_⟩
      rw [← Ideal.Quotient.eq]
      simpa only [σ, Ideal.quotientMap_mk] using h
    have h2' : (2 : O ⧸ P) ≠ 0 := by
      intro h
      apply h2
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_ofNat]
      exact h
    obtain ⟨w, hw⟩ := exists_mul_involution_eq_neg_one (k := O ⧸ P) σ hσ hne' h2'
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
    refine ⟨z, ?_, fun h => absurd rfl h⟩
    rw [zero_add, pow_one, ← Ideal.Quotient.eq_zero_iff_mem]
    simpa only [σ, Ideal.quotientMap_mk, map_add (f := _), map_mul, map_one] using hw
  · have hN0 : N ≠ 0 := hN.ne'
    obtain ⟨e, he_def⟩ : ∃ e, e = z0 * s z0 + 1 := ⟨_, rfl⟩
    have he : e ∈ P ^ N := he_def ▸ hz.resolve_left hN0
    have heP : e ∈ P := Ideal.pow_le_self hN0 he
    obtain ⟨y, i, hi, hyi⟩ := hP.exists_inv h2
    have hh : y + s y - 1 ∈ P := by
      have h1 : y * 2 - 1 ∈ P := by
        have h1e : y * 2 - 1 = -i := by linear_combination hyi
        rw [h1e]
        exact P.neg_mem hi
      have h1' : s y * 2 - 1 ∈ P := by
        have h1s := hsP _ h1
        simpa [map_sub, map_mul, map_ofNat] using h1s
      have h3 : 2 * (y + s y - 1) ∈ P := by
        have h3e : 2 * (y + s y - 1) = (y * 2 - 1) + (s y * 2 - 1) := by ring
        rw [h3e]
        exact P.add_mem h1 h1'
      rcases (Ideal.IsMaximal.isPrime hP).mem_or_mem h3 with h | h
      · exact absurd h h2
      · exact h
    refine ⟨z0 + y * z0 * e, ?_, fun _ => ?_⟩
    · have hse : s e = e := by rw [he_def, map_add (f := _), map_mul, hs, map_one]; ring
      have key : (z0 + y * z0 * e) * s (z0 + y * z0 * e) + 1
          = e * (1 - (y + s y) + (y + s y) * e) + e * (e * (y * z0 * s y * s z0)) := by
        rw [map_add (f := _), map_mul, map_mul, hse]
        rw [he_def]
        ring
      rw [key, pow_succ]
      refine Ideal.add_mem _ (Ideal.mul_mem_mul he ?_)
        (Ideal.mul_mem_mul he (Ideal.mul_mem_right _ _ heP))
      have hx : 1 - (y + s y) + (y + s y) * e = -(y + s y - 1) + (y + s y) * e := by ring
      rw [hx]
      exact P.add_mem (P.neg_mem hh) (Ideal.mul_mem_left _ _ heP)
    · have hx : z0 + y * z0 * e - z0 = y * z0 * e := by ring
      rw [hx]
      exact Ideal.mul_mem_left _ _ he

end GlobalTheory.NormResidue
end
