module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualSelmerClassesGiveNoncohomologousCochains

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardGaloisInvariantsOrdinaryRankTwoModPowBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardGaloisInvariantsOrdinaryRankTwoModPowBounded
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GwCard

variable {l : ℕ} [Fact l.Prime]

theorem natCast_not_isUnit (c : Coef l) : ¬ IsUnit ((l : ℕ) : c.O) := by
  rintro ⟨u, hu⟩
  have h2 : ‖(((u⁻¹ : c.Oˣ) : c.O) : Qbar l)‖ ≤ 1 := CupCob.norm_le_one_of_mem c ((u⁻¹ : c.Oˣ) : c.O).2
  have h3 : (((u : c.Oˣ) : c.O) : Qbar l) * (((u⁻¹ : c.Oˣ) : c.O) : Qbar l) = 1 := by
    rw [← Subalgebra.coe_mul, Units.mul_inv]; rfl
  have hu' : (((u : c.Oˣ) : c.O) : Qbar l) = ((l : ℕ) : Qbar l) := by rw [hu]; simp
  rw [hu'] at h3
  have hl : ‖((l : ℕ) : Qbar l)‖ < 1 := by
    have e : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) ((l : ℕ) : ℚ_[l]) := by simp
    rw [e, norm_algebraMap']
    exact Padic.norm_p_lt_one
  have := congrArg norm h3
  rw [norm_mul, norm_one] at this
  have : ‖((l : ℕ) : Qbar l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : Qbar l)‖ < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) h2) hl
  linarith

theorem exists_dvd_pow (c : Coef l) {d : c.O} (hd : d ≠ 0) : ∃ k : ℕ, d ∣ ((l : ℕ) : c.O) ^ k := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd hϖ
  refine ⟨k, ?_⟩
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h
    have h' := congrArg (fun x : c.O => (x : Qbar l)) h
    simp only [SubringClass.coe_natCast, ZeroMemClass.coe_zero, Nat.cast_eq_zero] at h'
    exact (Fact.out : l.Prime).ne_zero h'
  have hl : ϖ ∣ ((l : ℕ) : c.O) := by
    obtain ⟨m, hm⟩ := IsDiscreteValuationRing.associated_pow_irreducible hl0 hϖ
    rcases m with _ | m
    · exact absurd (hm.isUnit_iff.2 (by simp)) (natCast_not_isUnit c)
    · exact (dvd_pow_self ϖ (Nat.succ_ne_zero m)).trans hm.symm.dvd
  exact hk.dvd.trans (pow_dvd_pow_of_dvd hl k)

end GlobalTheory.Ord2.GwCard

noncomputable section

namespace GlobalTheory.Ord2.GwCard

variable {l : ℕ} [Fact l.Prime]

theorem card_ker_eq_index {R : Type} [Ring R] [Finite R] (x : R) :
    Nat.card (AddMonoidHom.mulLeft x).ker = (AddMonoidHom.mulLeft x).range.index := by
  set f := AddMonoidHom.mulLeft x
  have h1 := AddSubgroup.card_mul_index f.ker
  have h2 := AddSubgroup.card_mul_index f.range
  have h3 : f.ker.index = Nat.card f.range := by
    rw [AddSubgroup.index]
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv
  rw [h3] at h1
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  have := h1.trans h2.symm
  rw [mul_comm] at this
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem exists_card_ker_pow_le (c : Coef l) (k : ℕ) :
    ∃ B : ℕ, ∀ n : ℕ, Nat.card (AddMonoidHom.mulLeft (((l : ℕ) : Qn c n) ^ k)).ker ≤ B := by
  obtain ⟨g, s, hs⟩ := Module.Finite.exists_fin (R := ℤ_[l]) (M := c.O)
  refine ⟨Nat.card (Fin g → ZMod (l ^ k)), fun n => ?_⟩
  rw [card_ker_eq_index, AddSubgroup.index]
  set H := (AddMonoidHom.mulLeft (((l : ℕ) : Qn c n) ^ k)).range
  refine Nat.card_le_card_of_surjective
    (fun z : Fin g → ZMod (l ^ k) => (QuotientAddGroup.mk (∑ i, (z i).val • red c n (s i)) : Qn c n ⧸ H)) ?_
  intro q
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨x, rfl⟩ := red_surjective c n y
  have hx : x ∈ Submodule.span ℤ_[l] (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ_[l]).1 hx
  refine ⟨fun i => PadicInt.toZModPow k (a i), ?_⟩
  simp only
  set_option synthInstance.maxHeartbeats 100000 in
    rw [QuotientAddGroup.eq, ← ha, map_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  obtain ⟨w, hw⟩ : ∃ w : ℤ_[l], a i - (PadicInt.toZModPow k (a i)).val = (l : ℤ_[l]) ^ k * w := by
    have hm : a i - ((PadicInt.toZModPow k (a i)).val : ℤ_[l]) ∈ Ideal.span {(l : ℤ_[l]) ^ k} := by
      rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hm
    exact ⟨w, by rw [← hw, mul_comm]⟩
  refine ⟨red c n (w • s i), ?_⟩
  have e1 : (PadicInt.toZModPow k (a i)).val • red c n (s i) = red c n ((((PadicInt.toZModPow k (a i)).val : ℕ) : ℤ_[l]) • s i) := by
    rw [Nat.cast_smul_eq_nsmul, map_nsmul]
  rw [e1, ← map_neg, ← map_add (f := _), ← neg_smul, ← add_smul, neg_add_eq_sub, hw, mul_smul]
  simp only [AddMonoidHom.coe_mulLeft]
  rw [← map_natCast (red c n), ← map_pow, ← map_mul]
  congr 1
  rw [← Nat.cast_pow (α := ℤ_[l]), Nat.cast_smul_eq_nsmul, nsmul_eq_mul, Nat.cast_pow]

end GlobalTheory.Ord2.GwCard

namespace GlobalTheory.Ord2.GwCard

theorem exists_card_H0_rhoS_le : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ)
    (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l)
    (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1),
    ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → Nat.card (H0 (rhoS c n W hint S hN)) ≤ C := by
  intro l _ Ω _ _ _ e S A W hW c hint hN
  obtain ⟨φ, -, hφ⟩ := GlobalTheory.Ord2.commutator_H0_has_no_eigenvalue_one (l := l) (Ω := Ω) (e := e) (S := S) (A := A) (W := W) hW
  let M : Matrix (Fin 2) (Fin 2) c.O := Matrix.of fun i j => ⟨mat W φ i j, hint φ i j⟩
  have hM : (c.O.val : c.O →+* Qbar l).mapMatrix (M - 1) = mat W φ - 1 := by
    rw [map_sub, map_one]
    congr 1
  have hd : (M - 1).det ≠ 0 := by
    intro h
    apply hφ
    rw [← hM, ← RingHom.map_det, h, map_zero]
  obtain ⟨k, y, hy⟩ := exists_dvd_pow c hd
  obtain ⟨B, hB⟩ := exists_card_ker_pow_le c k
  refine ⟨B ^ 2, fun n _ => ?_⟩
  set K := (AddMonoidHom.mulLeft (((l : ℕ) : Qn c n) ^ k)).ker
  have hred : (red c n).mapMatrix (M - 1) = matQ c n W hint φ - 1 := by
    rw [map_sub, map_one]
    congr 1
  have hmem : ∀ m ∈ H0 (rhoS c n W hint S hN), ∀ i, m i ∈ K := by
    intro m hm i
    have h1 : matQ c n W hint φ *ᵥ m = m := (mem_riemannRochSpace_iff_regularAt_everywhere _ m).1 hm (toGS Ω (S : Set Pl) φ)
    have h2 : (matQ c n W hint φ - 1) *ᵥ m = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, h1, sub_self]
    have h3 : (matQ c n W hint φ - 1).det • m = 0 := by
      rw [← Matrix.one_mulVec m, ← Matrix.smul_mulVec, ← Matrix.adjugate_mul, ← Matrix.mulVec_mulVec, h2,
        Matrix.mulVec_zero]
    have h4 : red c n (M - 1).det * m i = 0 := by
      rw [RingHom.map_det, hred]
      have := congrFun h3 i
      simpa using this
    show ((l : ℕ) : Qn c n) ^ k * m i = 0
    rw [← map_natCast (red c n), ← map_pow, hy, map_mul, mul_comm (red c n _), mul_assoc, h4, mul_zero]
  let F : H0 (rhoS c n W hint S hN) → (Fin 2 → K) := fun m i => ⟨m.1 i, hmem m.1 m.2 i⟩
  have hF : Function.Injective F := by
    intro a b hab
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun hab i)
  calc Nat.card (H0 (rhoS c n W hint S hN)) ≤ Nat.card (Fin 2 → K) := Nat.card_le_card_of_injective F hF
    _ = Nat.card K ^ 2 := by simp [Nat.card_fun]
    _ ≤ B ^ 2 := Nat.pow_le_pow_left (hB n) 2

end GlobalTheory.Ord2.GwCard
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardGaloisInvariantsOrdinaryRankTwoModPowBoundedStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_galoisInvariants_ordinaryRankTwo_mod_pow_bounded : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1), ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → Nat.card (H0 (rhoS c n W hint S hN)) ≤ C := by
  first | exact @GlobalTheory.Ord2.GwCard.exists_card_H0_rhoS_le | exact GlobalTheory.Ord2.GwCard.exists_card_H0_rhoS_le | (intros; apply GlobalTheory.Ord2.GwCard.exists_card_H0_rhoS_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ArchimedeanInvariantsCard
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsUnitOfForallMaximal
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.OddInvolution

theorem exists_pos_pow_idem {M : Type} [Monoid M] [Finite M] (x : M) :
    ∃ m : ℕ, 0 < m ∧ IsIdempotentElem (x ^ m) := by
  have key : ∀ i d : ℕ, 0 < d → x ^ (i + d) = x ^ i → ∃ m : ℕ, 0 < m ∧ IsIdempotentElem (x ^ m) := by
    intro i d hd h
    have h1 : ∀ t k : ℕ, x ^ (i + k + t * d) = x ^ (i + k) := by
      intro t k
      induction t with
      | zero => simp
      | succ t ih =>
        have : i + k + (t + 1) * d = (i + d) + (k + t * d) := by ring
        rw [this, pow_add, h, ← pow_add, ← add_assoc, ih]
    have hle : i ≤ (i + 1) * d := by nlinarith
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    refine ⟨(i + 1) * d, by positivity, ?_⟩
    unfold IsIdempotentElem
    rw [← pow_add]
    have := h1 (i + 1) k
    rw [← hk] at this
    exact this
  obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => x ^ n)
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact key i (j - i) (by omega) (by rw [Nat.add_sub_cancel' hlt.le]; exact h.symm)
  · exact key j (i - j) (by omega) (by rw [Nat.add_sub_cancel' hlt.le]; exact h)

theorem pow_idem_field {F : Type} [Field F] {u : F} {m : ℕ} (hm : 0 < m)
    (he : IsIdempotentElem (u ^ m)) : (u = 0 → u ^ m = 0) ∧ (u ≠ 0 → u ^ m = 1) := by
  refine ⟨fun h => by rw [h, zero_pow hm.ne'], fun h => ?_⟩
  have h2 : u ^ m * u ^ m = u ^ m * 1 := by rw [mul_one]; exact he
  exact mul_left_cancel₀ (pow_ne_zero _ h) h2

theorem isUnit_of_forall_maximal {R : Type} [CommRing R] {s : R}
    (h : ∀ m : Ideal R, m.IsMaximal → Ideal.Quotient.mk m s ≠ 0) : IsUnit s := by
  by_contra hs
  obtain ⟨m, hm, hsm⟩ := exists_max_ideal_of_mem_nonunits (show s ∈ nonunits R from hs)
  exact h m hm (Ideal.Quotient.eq_zero_iff_mem.mpr hsm)

theorem exists_anticommuting {R : Type} [CommRing R] [Finite R] (h2 : IsUnit (2 : R))
    (a b c : R) (h : a * a + b * c = 1) :
    ∃ p q r : R, IsUnit (p * p + q * r) ∧ 2 * a * p + b * r + c * q = 0 := by
  obtain ⟨n1, hn1, he1⟩ := exists_pos_pow_idem (b * c)
  obtain ⟨n2, hn2, he2⟩ := exists_pos_pow_idem ((b + c) ^ 2 + 4 * a ^ 2)
  set e1 := (b * c) ^ n1 with he1d
  set e2 := ((b + c) ^ 2 + 4 * a ^ 2) ^ n2 with he2d
  refine ⟨(1 - e1) * e2 * (b + c) + (1 - e1) * (1 - e2) * (b - c),
    e1 * b + (1 - e1) * e2 * (-2 * a) + (1 - e1) * (1 - e2) * (2 * a),
    e1 * (-c) + (1 - e1) * e2 * (-2 * a) + (1 - e1) * (1 - e2) * (-2 * a), ?_, by ring⟩
  apply isUnit_of_forall_maximal
  intro m hm
  letI := Ideal.Quotient.field m
  have h2' : Ideal.Quotient.mk m (2 : R) ≠ 0 := (h2.map (Ideal.Quotient.mk m)).ne_zero
  have hh := congrArg (Ideal.Quotient.mk m) h
  have q1 : Ideal.Quotient.mk m e1 = (Ideal.Quotient.mk m (b * c)) ^ n1 := by rw [he1d, map_pow]
  have q2 : Ideal.Quotient.mk m e2 = (Ideal.Quotient.mk m ((b + c) ^ 2 + 4 * a ^ 2)) ^ n2 := by
    rw [he2d, map_pow]
  have k1 := pow_idem_field hn1 (q1 ▸ he1.map (Ideal.Quotient.mk m))
  have k2 := pow_idem_field hn2 (q2 ▸ he2.map (Ideal.Quotient.mk m))
  rw [← q1] at k1
  rw [← q2] at k2
  simp only [map_add (f := _), map_mul, map_sub, map_one, map_neg, map_pow, map_ofNat] at hh k1 k2 h2' ⊢
  generalize Ideal.Quotient.mk m e1 = E1 at k1 k2 ⊢
  generalize Ideal.Quotient.mk m e2 = E2 at k1 k2 ⊢
  generalize Ideal.Quotient.mk m a = A at hh k1 k2 ⊢
  generalize Ideal.Quotient.mk m b = B at hh k1 k2 ⊢
  generalize Ideal.Quotient.mk m c = C at hh k1 k2 ⊢
  have h8 : (2 : R ⧸ m) * 2 * 2 ≠ 0 := by simp [h2']
  by_cases hBC : B * C = 0
  · rw [k1.1 hBC]
    by_cases hU : (B + C) ^ 2 + 4 * A ^ 2 = 0
    · rw [k2.1 hU]
      intro hz
      apply h8
      linear_combination -hz + hU - 8 * hh + 4 * hBC
    · rw [k2.2 hU]
      intro hz
      apply hU
      linear_combination hz
  · rw [k1.2 hBC]
    intro hz
    apply hBC
    linear_combination -hz

theorem exists_swap {R : Type} [CommRing R] [Finite R] (X : Matrix (Fin 2) (Fin 2) R)
    (h2 : IsUnit (2 : R)) (hdet : X.det = -1) (htr : X.trace = 0) :
    ∃ (Y : Matrix (Fin 2) (Fin 2) R) (s : R), IsUnit s ∧ Y * Y = s • (1 : Matrix (Fin 2) (Fin 2) R) ∧
      X * Y = -(Y * X) := by
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two] at htr
  have hd : X 1 1 = -X 0 0 := by linear_combination htr
  have h : X 0 0 * X 0 0 + X 0 1 * X 1 0 = 1 := by
    rw [hd] at hdet; linear_combination -hdet
  obtain ⟨p, q, r, hs, hanti⟩ := exists_anticommuting h2 (X 0 0) (X 0 1) (X 1 0) h
  refine ⟨!![p, q; r, -p], p * p + q * r, hs, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hd, Matrix.vecMul, dotProduct] <;>
      first | linear_combination hanti | ring

theorem card_fixed_eq (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [Finite R]
    (X : Matrix (Fin 2) (Fin 2) R) (h2 : IsUnit (2 : R)) (hXX : X * X = 1) (hdet : X.det = -1)
    (htr : X.trace = 0) : Nat.card {v : Fin 2 → R // X *ᵥ v = v} = Nat.card R := by
  obtain ⟨Y, s, hs, hYY, hXY⟩ := exists_swap X h2 hdet htr
  have hXXv : ∀ v : Fin 2 → R, X *ᵥ (X *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hXX, Matrix.one_mulVec]
  have hYYv : ∀ v : Fin 2 → R, Y *ᵥ (Y *ᵥ v) = s • v := fun v => by
    rw [Matrix.mulVec_mulVec, hYY]
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply]
  have hXYv : ∀ v : Fin 2 → R, X *ᵥ (Y *ᵥ v) = -(Y *ᵥ (X *ᵥ v)) := fun v => by
    rw [Matrix.mulVec_mulVec, hXY, Matrix.neg_mulVec, Matrix.mulVec_mulVec]
  have hsu : ((hs.unit⁻¹ : Rˣ) : R) * s = 1 := by simp
  let e : {v : Fin 2 → R // X *ᵥ v = v} ≃ {v : Fin 2 → R // X *ᵥ v = -v} :=
    { toFun := fun v => ⟨Y *ᵥ v.1, by rw [hXYv, v.2]⟩
      invFun := fun w => ⟨((hs.unit⁻¹ : Rˣ) : R) • (Y *ᵥ w.1), by
        rw [Matrix.mulVec_smul, hXYv, w.2, Matrix.mulVec_neg, neg_neg]⟩
      left_inv := fun v => by
        apply Subtype.ext
        simp only [hYYv, smul_smul, hsu, one_smul]
      right_inv := fun w => by
        apply Subtype.ext
        simp only [Matrix.mulVec_smul, hYYv, smul_smul, hsu, one_smul] }
  have ht : ((h2.unit⁻¹ : Rˣ) : R) * 2 = 1 := by simp
  set t : R := ((h2.unit⁻¹ : Rˣ) : R)
  let f : (Fin 2 → R) ≃ {v : Fin 2 → R // X *ᵥ v = v} × {v : Fin 2 → R // X *ᵥ v = -v} :=
    { toFun := fun v => (⟨t • (v + X *ᵥ v), by
          rw [Matrix.mulVec_smul, Matrix.mulVec_add, hXXv, add_comm]⟩,
        ⟨t • (v - X *ᵥ v), by
          rw [Matrix.mulVec_smul, Matrix.mulVec_sub, hXXv, ← smul_neg, neg_sub]⟩)
      invFun := fun pq => pq.1.1 + pq.2.1
      left_inv := fun v => by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        linear_combination (v i) * ht
      right_inv := fun pq => by
        obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := pq
        ext i
        · simp only [Matrix.mulVec_add, hp, hq, Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
            smul_eq_mul]
          linear_combination (p i) * ht
        · simp only [Matrix.mulVec_add, hp, hq, Pi.add_apply, Pi.smul_apply, Pi.neg_apply,
            Pi.sub_apply, smul_eq_mul]
          linear_combination (q i) * ht }
  have h1 : Nat.card (Fin 2 → R) =
      Nat.card {v : Fin 2 → R // X *ᵥ v = v} * Nat.card {v : Fin 2 → R // X *ᵥ v = -v} := by
    rw [Nat.card_congr f, Nat.card_prod]
  have h3 : Nat.card (Fin 2 → R) = Nat.card R * Nat.card R := by
    rw [Nat.card_fun]; simp [sq]
  have hsq : Nat.card {v : Fin 2 → R // X *ᵥ v = v} * Nat.card {v : Fin 2 → R // X *ᵥ v = v} =
      Nat.card R * Nat.card R := by
    rw [← h3, h1, Nat.card_congr e]
  exact Nat.mul_self_inj.mp hsq

theorem card_fixed (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] [Finite R]
    (X : Matrix (Fin 2) (Fin 2) R) : IsUnit (2 : R) → X * X = 1 → X.det = -1 → X.trace = 0 →
      Nat.card {v : Fin 2 → R // X *ᵥ v = v} = Nat.card R :=
  fun h2 hXX hdet htr => card_fixed_eq l R X h2 hXX hdet htr

end GlobalTheory.OddInvolution
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ArchimedeanInvariantsCard
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

namespace GlobalTheory.Ord2.GwIneq.Arch

theorem isUnit_two (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (c : Coef l) (n : ℕ) : IsUnit (2 : Qn c n) := by
  have hodd : Odd (l ^ n) := ((Fact.out : l.Prime).odd_of_ne_two hl).pow
  obtain ⟨k, hk⟩ := hodd
  have h0 : ((l ^ n : ℕ) : Qn c n) = 0 := by
    have := kill c n (1 : Qn c n)
    rwa [nsmul_eq_mul, mul_one] at this
  have e : (2 : Qn c n) * ((k + 1 : ℕ) : Qn c n) = ((l ^ n : ℕ) : Qn c n) + 1 := by
    rw [hk]; push_cast; ring
  rw [h0, zero_add] at e
  exact isUnit_iff_exists_inv.mpr ⟨_, e⟩

theorem trace_eq_zero {R : Type} [CommRing R] (X : Matrix (Fin 2) (Fin 2) R) (hXX : X * X = 1)
    (hdet : X.det = -1) : X.trace = 0 := by
  rw [Matrix.det_fin_two] at hdet
  rw [Matrix.trace_fin_two]
  have e00 := congrFun (congrFun hXX 0) 0
  have e10 := congrFun (congrFun hXX 1) 0
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e10
  linear_combination (X 0 0 - (X 0 0 + X 1 1)) * e00 + X 0 0 * hdet + X 0 1 * e10

theorem card_fixed_cc (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l) (hW : Nf e S A W) (c : Coef l)
    (hint : ∀ s i j, mat W s i j ∈ c.O) (n : ℕ) (w : InfinitePlace ℚ) (s : G ℚ Ω) (hs : IsCCAt w s) :
    Nat.card {v : Mn c n // matQ c n W hint s *ᵥ v = v} = Nat.card (Qn c n) := by
  obtain ⟨j, hj, -⟩ := hs
  have hss : s * s = 1 := by
    ext x
    apply j.injective
    show j (s (s x)) = j x
    rw [hj, hj]; simp
  have hXX : matQ c n W hint s * matQ c n W hint s = 1 := by
    rw [← matQ_mul, hss, matQ_one]
  have hd : (mat W s).det = -1 := by
    have h := hW.odd s ⟨j, hj⟩
    have h2 : ((dt W s : (Qbar l)ˣ) : Qbar l) = (mat W s).det := by
      simp [dt, mat, Matrix.GeneralLinearGroup.val_det_apply]
    rw [← h2, h]; simp
  have hdet : (matQ c n W hint s).det = -1 := by
    rw [Matrix.det_fin_two] at hd ⊢
    simp only [matQ_apply]
    rw [← map_mul, ← map_mul, ← map_sub, ← map_one (red c n), ← map_neg]
    congr 1
    apply Subtype.ext
    simp only [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_neg, Subalgebra.coe_one]
    exact hd
  exact GlobalTheory.OddInvolution.card_fixed l (Qn c n) _ (isUnit_two l hW.l_odd c n) hXX hdet
    (trace_eq_zero _ hXX hdet)

theorem archimedean_h0_card_eq : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (n : ℕ), 1 ≤ n → ∀ cc : InfinitePlace ℚ → G ℚ Ω, (∀ w, w.IsReal → IsCCAt w (cc w)) → archH0Card S (rhoS c n W hint S hN) cc = Nat.card (Qn c n) := by
  intro l _ Ω _ _ _ e S A W hW c hint hN n _ cc hcc
  classical
  unfold archH0Card
  have hfil : (Finset.univ.filter (fun w : InfinitePlace ℚ => w.IsReal)) = {Rat.infinitePlace} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun _ => Subsingleton.elim _ _, fun h => h ▸ Rat.isReal_infinitePlace⟩
  rw [IsTotallyReal.nrComplexPlaces_eq_zero ℚ, pow_zero, mul_one]
  convert Finset.prod_singleton (fun w : InfinitePlace ℚ =>
    Nat.card {m : Mn c n // rhoS c n W hint S hN (toGS Ω _ (cc w)) m = m}) Rat.infinitePlace using 1
  · rw [hfil]
  · exact (card_fixed_cc l Ω e S A W hW c hint n _ _ (hcc _ Rat.isReal_infinitePlace)).symm

end GlobalTheory.Ord2.GwIneq.Arch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ArchimedeanInvariantsCardStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_invariants_card : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (n : ℕ), 1 ≤ n → ∀ cc : InfinitePlace ℚ → G ℚ Ω, (∀ w, w.IsReal → IsCCAt w (cc w)) → archH0Card S (rhoS c n W hint S hN) cc = Nat.card (Qn c n) := by
  first | exact @GlobalTheory.Ord2.GwIneq.Arch.archimedean_h0_card_eq | exact GlobalTheory.Ord2.GwIneq.Arch.archimedean_h0_card_eq | (intros; apply GlobalTheory.Ord2.GwIneq.Arch.archimedean_h0_card_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinarySelmerModPrimePowInjectsResidualSelmer
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinarySelmerModPrimePowInjectsResidualSelmer
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.SelLower

variable {l : ℕ} [Fact l.Prime]


open Classical in
def rv (c : Coef l) (n : ℕ) (v : Fin 2 → Qbar l) : Mn c n :=
  fun i => if h : v i ∈ c.O then red c n ⟨v i, h⟩ else 0

theorem rv_apply {c : Coef l} {n : ℕ} {v : Fin 2 → Qbar l} (hv : ∀ i, v i ∈ c.O) (i : Fin 2) :
    rv c n v i = red c n ⟨v i, hv i⟩ := by
  unfold rv; rw [dif_pos (hv i)]

theorem rv_eq_iff {c : Coef l} {n : ℕ} {a b : Fin 2 → Qbar l} (ha : ∀ i, a i ∈ c.O) (hb : ∀ i, b i ∈ c.O) :
    rv c n a = rv c n b ↔ Cv n a b := by
  rw [funext_iff]
  refine forall_congr' fun i => ?_
  rw [rv_apply ha, rv_apply hb, red_eq_iff]

theorem addV {c : Coef l} {a b : Fin 2 → Qbar l} (ha : ∀ i, a i ∈ c.O) (hb : ∀ i, b i ∈ c.O) :
    ∀ i, (a + b) i ∈ c.O := fun i => c.O.add_mem (ha i) (hb i)

theorem subV {c : Coef l} {a b : Fin 2 → Qbar l} (ha : ∀ i, a i ∈ c.O) (hb : ∀ i, b i ∈ c.O) :
    ∀ i, (a - b) i ∈ c.O := fun i => c.O.sub_mem (ha i) (hb i)

theorem zeroV (c : Coef l) : ∀ i, (0 : Fin 2 → Qbar l) i ∈ c.O := fun _ => c.O.zero_mem

theorem rv_add {c : Coef l} {n : ℕ} {a b : Fin 2 → Qbar l} (ha : ∀ i, a i ∈ c.O) (hb : ∀ i, b i ∈ c.O) :
    rv c n (a + b) = rv c n a + rv c n b := by
  funext i
  rw [rv_apply (addV ha hb)]
  show _ = rv c n a i + rv c n b i
  rw [rv_apply ha, rv_apply hb, ← map_add (f := _)]
  rfl

theorem rv_sub {c : Coef l} {n : ℕ} {a b : Fin 2 → Qbar l} (ha : ∀ i, a i ∈ c.O) (hb : ∀ i, b i ∈ c.O) :
    rv c n (a - b) = rv c n a - rv c n b := by
  funext i
  rw [rv_apply (subV ha hb)]
  show _ = rv c n a i - rv c n b i
  rw [rv_apply ha, rv_apply hb, ← map_sub]
  rfl

theorem rv_zero (c : Coef l) (n : ℕ) : rv c n 0 = 0 := by
  funext i
  rw [rv_apply (zeroV c)]
  show _ = (0 : Qn c n)
  rw [← map_zero (red c n)]
  rfl

theorem mulVec_mem {c : Coef l} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : ∀ i j, M i j ∈ c.O)
    {x : Fin 2 → Qbar l} (hx : ∀ i, x i ∈ c.O) (i : Fin 2) : (M *ᵥ x) i ∈ c.O := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact c.O.add_mem (c.O.mul_mem (hM _ _) (hx _)) (c.O.mul_mem (hM _ _) (hx _))

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem rv_mulVec (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (s : G ℚ Ω)
    {x : Fin 2 → Qbar l} (hx : ∀ i, x i ∈ c.O) :
    rv c n (mat W s *ᵥ x) = matQ c n W hint s *ᵥ rv c n x := by
  funext i
  rw [rv_apply (mulVec_mem (hint s) hx)]
  have e : (⟨(mat W s *ᵥ x) i, mulVec_mem (hint s) hx i⟩ : c.O) =
      ⟨mat W s i 0, hint s i 0⟩ * ⟨x 0, hx 0⟩ + ⟨mat W s i 1, hint s i 1⟩ * ⟨x 1, hx 1⟩ := by
    apply Subtype.ext
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [e, map_add (f := _), map_mul, map_mul]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, matQ_apply, rv_apply hx]

theorem continuous_rv (c : Coef l) (n : ℕ) {y : G ℚ Ω → Fin 2 → Qbar l} (hyc : Continuous y)
    (hO : ∀ s i, y s i ∈ c.O) : Continuous fun s => rv c n (y s) := by
  refine continuous_pi fun i => ?_
  refine continuous_discrete_rng.2 fun q => ?_
  obtain ⟨z, rfl⟩ := red_surjective c n q
  have e : (fun s => rv c n (y s) i) ⁻¹' {red c n z} =
      (fun s => y s i) ⁻¹' Metric.closedBall (z : Qbar l) ‖((l : ℕ) : Qbar l) ^ n‖ := by
    ext s
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Metric.mem_closedBall, dist_eq_norm, rv_apply (hO s)]
    exact red_eq_iff _ _
  rw [e]
  have hne : ‖((l : ℕ) : Qbar l) ^ n‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  exact (IsUltrametricDist.isOpen_closedBall _ hne).preimage ((continuous_apply i).comp hyc)

theorem eq_of_natCast_mem {v w : Pl} (hv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) :
    v = w := by
  have hp : Prime ((l : ℕ) : 𝓞 ℚ) := by
    have e : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr
      (Nat.prime_iff_prime_int.1 (Fact.out : l.Prime))
  have hmax : (Ideal.span {((l : ℕ) : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).2 hp).isMaximal
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hp.ne_zero)
  have h1 : Ideal.span {((l : ℕ) : 𝓞 ℚ)} = v.asIdeal :=
    hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hv)
  have h2 : Ideal.span {((l : ℕ) : 𝓞 ℚ)} = w.asIdeal :=
    hmax.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)
  exact HeightOneSpectrum.ext (h1.symm.trans h2)

theorem toGS_surjective (S : Finset Pl) : Function.Surjective (toGS Ω (S : Set Pl)) :=
  QuotientGroup.mk'_surjective _

def zOf (c : Coef l) (n : ℕ) (S : Finset Pl) (y : G ℚ Ω → Fin 2 → Qbar l) : GS Ω (S : Set Pl) → Mn c n :=
  fun g => rv c n (y (Function.surjInv (toGS_surjective S) g))

theorem rv_wd (c : Coef l) (n : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l)
    (hint : ∀ s i j, mat W s i j ∈ c.O) {y : G ℚ Ω → Fin 2 → Qbar l} (hy : GwCount.SelN c n S A W y)
    {s t : G ℚ Ω} (h : toGS Ω (S : Set Pl) s = toGS Ω (S : Set Pl) t) : rv c n (y s) = rv c n (y t) := by
  have hO : ∀ s i, y s i ∈ c.O := hy.1.2.1
  have ha : s⁻¹ * t ∈ (toGS Ω (S : Set Pl)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have e : s * (s⁻¹ * t) = t := by group
  have h1 := hy.1.2.2 s (Subgroup.mem_top _) (s⁻¹ * t) (Subgroup.mem_top _)
  rw [e] at h1
  have h2 := hy.2.1 _ ha
  rw [(rv_eq_iff (hO t) (addV (hO s) (mulVec_mem (hint s) (hO _)))).2 h1,
    rv_add (hO s) (mulVec_mem (hint s) (hO _)), rv_mulVec c n W hint s (hO _),
    (rv_eq_iff (hO _) (zeroV c)).2 h2, rv_zero, Matrix.mulVec_zero, add_zero]

theorem zOf_toGS (c : Coef l) (n : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l)
    (hint : ∀ s i j, mat W s i j ∈ c.O) {y : G ℚ Ω → Fin 2 → Qbar l} (hy : GwCount.SelN c n S A W y)
    (s : G ℚ Ω) : zOf c n S y (toGS Ω (S : Set Pl) s) = rv c n (y s) :=
  rv_wd c n S A W hint hy (Function.surjInv_eq (toGS_surjective S) _)

theorem zOf_mem (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (A : ValuationSubring Ω) {y : G ℚ Ω → Fin 2 → Qbar l}
    (hy : GwCount.SelN c n S A W y) : zOf c n S y ∈ Z1 (rhoS c n W hint S hN) := by
  have hO : ∀ s i, y s i ∈ c.O := hy.1.2.1
  refine ⟨?_, fun g h => ?_⟩
  · rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    have e : (zOf c n S y ∘ QuotientGroup.mk) = fun s => rv c n (y s) :=
      funext fun s => zOf_toGS c n S A W hint hy s
    rw [e]
    have h0 := hy.1.1
    rw [Subgroup.coe_top] at h0
    exact continuous_rv c n (continuousOn_univ.1 h0) hO
  · obtain ⟨s, rfl⟩ := toGS_surjective S g
    obtain ⟨t, rfl⟩ := toGS_surjective S h
    rw [← map_mul, zOf_toGS c n S A W hint hy, zOf_toGS c n S A W hint hy, zOf_toGS c n S A W hint hy,
      rhoS_toGS, ← rv_mulVec c n W hint s (hO t), ← rv_add (hO s) (mulVec_mem (hint s) (hO t))]
    exact (rv_eq_iff (hO _) (addV (hO s) (mulVec_mem (hint s) (hO t)))).2
      (hy.1.2.2 s (Subgroup.mem_top _) t (Subgroup.mem_top _))

end

theorem sel_lower : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (n : ℕ), 1 ≤ n → ∃ cls : (G ℚ Ω → Fin 2 → Qbar l) → H1 (rhoS c n W hint S hN), (∀ y, GwCount.SelN c n S A W y → cls y ∈ SelG c n W hint S hN A) ∧ ∀ y y', GwCount.SelN c n S A W y → GwCount.SelN c n S A W y' → cls y = cls y' → Cob1 c n W ⊤ (y - y') := by
  intro l _ Ω _ _ _ e S A W hW c hint hN n _
  classical
  refine ⟨fun y => if h : GwCount.SelN c n S A W y then
    Submodule.Quotient.mk ⟨zOf c n S y, zOf_mem c n W hint S hN A h⟩ else 0, ?_, ?_⟩
  · intro y hy
    have hO : ∀ s i, y s i ∈ c.O := hy.1.2.1
    simp only [dif_pos hy]
    rw [SelG, mem_Sel]
    intro v
    rw [resH1, Submodule.mapQ_apply]
    by_cases hv : IsPlaceOver A v.1
    · have hL : Lc c n W hint S hN A v = ordCond c n W hint S hN (Av A S v) := by
        unfold Lc; exact if_pos hv
      have hAv : Av A S v = A := by
        unfold Av; rw [if_pos hv]
      rw [hL]
      change Submodule.Quotient.mk (restrictCocycles1 (rhoS c n W hint S hN) (locHom (S : Set Pl) (Av A S v))
        (continuous_locHom _ _) ⟨zOf c n S y, zOf_mem c n W hint S hN A hy⟩) ∈ ordCond c n W hint S hN (Av A S v)
      rw [ordCond]
      have hmem : restrictCocycles1 (rhoS c n W hint S hN) (locHom (S : Set Pl) (Av A S v)) (continuous_locHom _ _)
          ⟨zOf c n S y, zOf_mem c n W hint S hN A hy⟩ ∈
          (ordZ c n W hint (Av A S v)).comap (Z1 ((rhoS c n W hint S hN).comp
            (locHom (S : Set Pl) (Av A S v)))).subtype := by
        rw [Submodule.mem_comap, mem_ordZ]
        obtain ⟨x, hx, hxs⟩ := hy.2.2.2
        refine ⟨red c n ⟨x, hx⟩, fun s => ?_⟩
        show zOf c n S y (toGS Ω (S : Set Pl) s.1) 1 = _
        have hs : (s : G ℚ Ω) ∈ Dec (F := ℚ) A := (le_of_eq (congrArg (Dec (F := ℚ)) hAv)) s.2
        rw [zOf_toGS c n S A W hint hy, rv_apply (hO s.1), matQ_apply, ← map_mul, ← map_sub, red_eq_iff]
        exact hxs s hs
      exact Submodule.mem_map_of_mem hmem
    · have hL : Lc c n W hint S hN A v = H1ur ((rhoS c n W hint S hN).comp (locFam S (Av A S) v))
          ((Ine (F := ℚ) (Av A S v)).subgroupOf (Dec (F := ℚ) (Av A S v))) := by
        unfold Lc; exact if_neg hv
      have hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.1.asIdeal := fun h => hv (by
        obtain ⟨v0, hA0, hl0⟩ := hW.atL
        rw [eq_of_natCast_mem h hl0]
        exact hA0)
      obtain ⟨B, hB, hcob⟩ := hy.2.2.1 v.1 v.2 hl
      obtain ⟨x, hxO, hx⟩ := CobConj.cob_conj l Ω W c n y v.1 B (Av A S v) hint hy.1 hB
        (isPlaceOver_Av A S v) hcob
      rw [hL, H1ur, LinearMap.mem_ker]
      refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨rv c n x, fun g => ?_⟩)
      show zOf c n S y (toGS Ω (S : Set Pl) g.1.1) = matQ c n W hint g.1.1 *ᵥ rv c n x - rv c n x
      have hg : (g.1.1 : G ℚ Ω) ∈ Ine (F := ℚ) (Av A S v) := Subgroup.mem_subgroupOf.1 g.2
      rw [zOf_toGS c n S A W hint hy, ← rv_mulVec c n W hint _ hxO, ← rv_sub (mulVec_mem (hint _) hxO) hxO]
      exact (rv_eq_iff (hO _) (subV (mulVec_mem (hint _) hxO) hxO)).2 (hx _ hg)
  · intro y y' hy hy' heq
    have hO : ∀ s i, y s i ∈ c.O := hy.1.2.1
    have hO' : ∀ s i, y' s i ∈ c.O := hy'.1.2.1
    simp only [dif_pos hy, dif_pos hy'] at heq
    rw [Submodule.Quotient.eq, Submodule.mem_comap, mem_coboundaries1] at heq
    obtain ⟨m, hm⟩ := heq
    choose x hx using fun i => red_surjective c n (m i)
    have hxO : ∀ i, (fun i => ((x i : c.O) : Qbar l)) i ∈ c.O := fun i => (x i).2
    have hm' : rv c n (fun i => ((x i : c.O) : Qbar l)) = m := funext fun i => by
      rw [rv_apply hxO]; exact hx i
    refine ⟨fun i => ((x i : c.O) : Qbar l), hxO, fun s _ => ?_⟩
    have h := hm (toGS Ω (S : Set Pl) s)
    change zOf c n S y (toGS Ω (S : Set Pl) s) - zOf c n S y' (toGS Ω (S : Set Pl) s) =
      rhoS c n W hint S hN (toGS Ω (S : Set Pl) s) m - m at h
    rw [zOf_toGS c n S A W hint hy, zOf_toGS c n S A W hint hy', rhoS_toGS, ← hm',
      ← rv_mulVec c n W hint s hxO, ← rv_sub (hO s) (hO' s), ← rv_sub (mulVec_mem (hint s) hxO) hxO] at h
    exact (rv_eq_iff (subV (hO s) (hO' s)) (subV (mulVec_mem (hint s) hxO) hxO)).1 h

end GlobalTheory.Ord2.SelLower
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinarySelmerModPrimePowInjectsResidualSelmerStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinarySelmerModPrimePow_injects_residualSelmer : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (n : ℕ), 1 ≤ n → ∃ cls : (G ℚ Ω → Fin 2 → Qbar l) → H1 (rhoS c n W hint S hN), (∀ y, GwCount.SelN c n S A W y → cls y ∈ SelG c n W hint S hN A) ∧ ∀ y y', GwCount.SelN c n S A W y → GwCount.SelN c n S A W y' → cls y = cls y' → Cob1 c n W ⊤ (y - y') := by
  first | exact @GlobalTheory.Ord2.SelLower.sel_lower | exact GlobalTheory.Ord2.SelLower.sel_lower | (intros; apply GlobalTheory.Ord2.SelLower.sel_lower <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GreenbergWilesDualSelmerLowerBoundModPrimePow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GwIneq

theorem exists_cc (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] :
    ∃ cc : InfinitePlace ℚ → G ℚ Ω, ∀ w, w.IsReal → IsCCAt w (cc w) := by
  have h : ∀ w : InfinitePlace ℚ, ∃ c : G ℚ Ω, w.IsReal → IsCCAt w c := fun w => by
    by_cases hw : w.IsReal
    · haveI : Module.IsTorsionFree ℚ Ω := DivisionSemiring.to_moduleIsTorsionFree
      haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
      haveI : IsGalois ℚ Ω := {}
      letI : Algebra ℚ ℂ := w.embedding.toAlgebra
      let j : Ω →ₐ[ℚ] ℂ := (by
        refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
        solve_by_elim* (maxDepth := 2) only [*,
          @_root_.DivisionSemiring.to_moduleIsTorsionFree,
          @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
      have hr : ComplexEmbedding.IsReal w.embedding := InfinitePlace.isReal_iff.1 hw
      let cj : ℂ →ₐ[ℚ] ℂ := { starRingEnd ℂ with commutes' := fun x => RingHom.congr_fun hr x }
      letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
      haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
      refine ⟨(cj.comp j).restrictNormal' Ω, fun _ => ⟨j.toRingHom, fun x => ?_, ?_⟩⟩
      · exact AlgHom.restrictNormal_commutes (cj.comp j) Ω x
      · rw [show j.toRingHom.comp (algebraMap ℚ Ω) = w.embedding from RingHom.ext fun x => j.commutes x]
        exact w.mk_embedding
    · exact ⟨1, fun h => absurd h hw⟩
  choose cc hcc using h
  exact ⟨cc, hcc⟩

theorem gw_ineq : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ (N : ℕ) (y : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, GwCount.SelN c n S A W (y i)) → (∀ i j, i ≠ j → ¬ Cob1 c n W ⊤ (y i - y j)) → ∃ (N' : ℕ) (z : Fin N' → G ℚ Ω → Fin 2 → Qbar l), N ≤ C * N' ∧ (∀ i, GwCount.SelN c n S A (dual1 W) (z i)) ∧ ∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j) := by
  classical
  intro hL l _ Ω _ _ _ e S A W hW c hint
  have hN := kills_NS hW
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.card_galoisInvariants_ordinaryRankTwo_mod_pow_bounded l Ω e S A W hW c hint hN
  obtain ⟨CA, hCA⟩ := GlobalTheory.T.card_ordinaryLocalConditionModPrimePow_le_const_mul hL l Ω e S A W hW c hint hN
  refine ⟨C0 * CA, fun n hn N y hy hyd => ?_⟩
  have hn0 : 0 < n := hn
  have hS := hW.above
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := ℚ) (Ω := Ω) (l := l) (r := n) (S := S) hS
  obtain ⟨cc, hcc⟩ := exists_cc Ω
  have hρ : ReciprocityTheory.Gal.ContAction (rhoS c n W hint S hN) := contAction_rhoS c n W hint S hN hW.cont
  have hgw := hL.gw ℚ Ω l n (Mn c n) S (rhoS c n W hint S hN) hn0 hW.l_odd hS hρ μ hμ (Av A S)
    (isPlaceOver_Av A S) cc hcc (Lc c n W hint S hN A)
  have hρd : ReciprocityTheory.Gal.ContAction (twDual μ (rhoS c n W hint S hN)) :=
    GlobalTheory.DualSide.contAction_twDual (GlobalTheory.Published.PoitouTate.contAction_charRep hμ) hρ
  haveI : Finite (TDual (ZMod (l ^ n)) (Mn c n)) := GlobalTheory.DualSide.finite_TDual
  haveI : Finite (H1 (rhoS c n W hint S hN)) := (hL.gf ℚ Ω l n (Mn c n) S _ hn0 hS hρ).2.1
  haveI : Finite (H1 (twDual μ (rhoS c n W hint S hN))) :=
    (hL.gf ℚ Ω l n (TDual (ZMod (l ^ n)) (Mn c n)) S _ hn0 hS hρd).2.1

  obtain ⟨v0, hA0, hl0⟩ := hW.atL
  let vA : S := ⟨v0, hS v0 hl0⟩
  have huniq : ∀ v w : Pl, IsPlaceOver A v → IsPlaceOver A w → v = w := fun v w hv hw =>
    HeightOneSpectrum.ext (Ideal.ext fun x => (hv x).symm.trans (hw x))
  have hLv : ∀ v : S, v ≠ vA → Nat.card (Lc c n W hint S hN A v) =
      Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) v))) := by
    intro v hv
    have hnp : ¬ IsPlaceOver A v.1 := fun h => hv (Subtype.ext (huniq _ _ h hA0))
    have e1 : Lc c n W hint S hN A v = H1ur ((rhoS c n W hint S hN).comp (locFam S (Av A S) v))
        ((Ine (F := ℚ) (Av A S v)).subgroupOf (Dec (F := ℚ) (Av A S v))) := if_neg hnp
    rw [e1]
    exact GlobalTheory.Ord2.UrCard.card_unramified_h1_eq_card_h0 ℚ Ω l n (Mn c n) (Av A S v) v.1 _
      (hρ.comp' (continuous_locFam S (Av A S) v)) (isPlaceOver_Av A S v)
  have harch := GlobalTheory.T.archimedean_invariants_card l Ω e S A W hW c hint hN n hn cc hcc
  rw [harch, ← Finset.mul_prod_erase _ _ (Finset.mem_univ vA),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ vA),
    Finset.prod_congr rfl fun v hv => hLv v (Finset.ne_of_mem_erase hv)] at hgw
  have hLA := hCA n hn vA hA0
  have hH0 := hC0 n hn
  have hP : 0 < ∏ v ∈ Finset.univ.erase vA, Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) v))) :=
    Finset.prod_pos fun v _ => Nat.card_pos
  have hq : 0 < Nat.card (Qn c n) := Nat.card_pos
  have h1d : 1 ≤ Nat.card (H0 (twDual μ (rhoS c n W hint S hN))) := Nat.card_pos
  have h1A : 1 ≤ Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) vA))) := Nat.card_pos
  set P := ∏ v ∈ Finset.univ.erase vA, Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) v)))
  have hsel : Nat.card (SelG c n W hint S hN A) ≤ C0 * CA * Nat.card (SelD c n W hint S hN A hW.cont μ) := by
    have key : Nat.card (SelG c n W hint S hN A) * (Nat.card (Qn c n) * P) ≤
        (C0 * CA * Nat.card (SelD c n W hint S hN A hW.cont μ)) * (Nat.card (Qn c n) * P) := by
      calc Nat.card (SelG c n W hint S hN A) * (Nat.card (Qn c n) * P)
          = Nat.card (SelG c n W hint S hN A) * 1 * (1 * P) * Nat.card (Qn c n) := by ring
        _ ≤ Nat.card (SelG c n W hint S hN A) * Nat.card (H0 (twDual μ (rhoS c n W hint S hN))) *
            (Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) vA))) * P) * Nat.card (Qn c n) := by
          gcongr
        _ = Nat.card (SelD c n W hint S hN A hW.cont μ) * Nat.card (H0 (rhoS c n W hint S hN)) *
            (Nat.card (Lc c n W hint S hN A vA) * P) := hgw
        _ ≤ Nat.card (SelD c n W hint S hN A hW.cont μ) * C0 * (CA * Nat.card (Qn c n) * P) := by
          gcongr
        _ = (C0 * CA * Nat.card (SelD c n W hint S hN A hW.cont μ)) * (Nat.card (Qn c n) * P) := by ring
    exact Nat.le_of_mul_le_mul_right key (Nat.mul_pos hq hP)

  obtain ⟨cls, hcls, hinj⟩ := GlobalTheory.T.ordinarySelmerModPrimePow_injects_residualSelmer l Ω e S A W hW c hint hN n hn
  have hN1 : N ≤ Nat.card (SelG c n W hint S hN A) := by
    let f : Fin N → SelG c n W hint S hN A := fun i => ⟨cls (y i), hcls _ (hy i)⟩
    have hf : Function.Injective f := by
      intro i j hij
      by_contra hne
      exact hyd i j hne (hinj _ _ (hy i) (hy j) (congrArg Subtype.val hij))
    simpa using Nat.card_le_card_of_injective f hf

  obtain ⟨z, hz, hzd⟩ := GlobalTheory.T.dualSelmer_classes_give_noncohomologous_cochains hL l Ω e S A W hW c hint hN n hn μ hμ
  let eqv := Finite.equivFin (SelD c n W hint S hN A hW.cont μ)
  refine ⟨Nat.card (SelD c n W hint S hN A hW.cont μ), fun i => z (eqv.symm i), ?_, fun i => hz _, ?_⟩
  · exact hN1.trans hsel
  · intro i j hij
    exact hzd _ _ (fun h => hij (eqv.symm.injective h))

end GlobalTheory.Ord2.GwIneq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GreenbergWilesDualSelmerLowerBoundModPrimePowStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
theorem _root_.GlobalTheory.T.greenbergWiles_dualSelmer_lower_bound_mod_prime_pow : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ (N : ℕ) (y : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, GwCount.SelN c n S A W (y i)) → (∀ i j, i ≠ j → ¬ Cob1 c n W ⊤ (y i - y j)) → ∃ (N' : ℕ) (z : Fin N' → G ℚ Ω → Fin 2 → Qbar l), N ≤ C * N' ∧ (∀ i, GwCount.SelN c n S A (dual1 W) (z i)) ∧ ∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j) := by
  first | exact @GlobalTheory.Ord2.GwIneq.gw_ineq | exact GlobalTheory.Ord2.GwIneq.gw_ineq | (intros; apply GlobalTheory.Ord2.GwIneq.gw_ineq <;> assumption) | exact @GlobalTheory.Ord2.GwIneq.exists_cc | exact GlobalTheory.Ord2.GwIneq.exists_cc | (intros; apply GlobalTheory.Ord2.GwIneq.exists_cc <;> assumption)
end
