module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HsCodiscreteNeBot

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormOpFrob
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOfRedEqZero
open GlobalTheory.Col PowerSeries

noncomputable section
namespace GlobalTheory.Col.NormFrob

theorem ringHom_ext_of_poly {R S : Type} [CommRing R] [CommRing S] (f g : PowerSeries R →+* PowerSeries S)
    (hfg : f.comp Polynomial.coeToPowerSeries.ringHom = g.comp Polynomial.coeToPowerSeries.ringHom)
    (hf : X ∣ f X) (hg : X ∣ g X) : f = g := by
  ext1 h
  ext n
  set P : Polynomial R := trunc (n + 1) h
  have hd : X ^ (n + 1) ∣ h - (P : PowerSeries R) := by
    rw [X_pow_dvd_iff]
    intro m hm
    simp [P, Polynomial.coeff_coe, coeff_trunc, hm]
  obtain ⟨q, hq⟩ := hd
  have hh : h = (P : PowerSeries R) + X ^ (n + 1) * q := by rw [← hq]; ring
  have hP : f (P : PowerSeries R) = g (P : PowerSeries R) := by
    have := congrArg (fun F => F P) hfg
    simpa using this
  have key : ∀ F : PowerSeries R →+* PowerSeries S, X ∣ F X → coeff n (F (X ^ (n + 1) * q)) = 0 := by
    intro F hF
    have : X ^ (n + 1) ∣ F (X ^ (n + 1) * q) := by
      rw [map_mul, map_pow]
      exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hF _) _
    exact (X_pow_dvd_iff.1 this) n (Nat.lt_succ_self n)
  rw [hh, map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hP, key f hf, key g hg]

end GlobalTheory.Col.NormFrob

namespace GlobalTheory.Col.NormFrob
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

abbrev red : PowerSeries R →+* PowerSeries (R ⧸ Ideal.span {(p : R)}) :=
  PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)}))

theorem exists_of_red_eq_zero (D : PowerSeries R) (hD : red p D = 0) :
    ∃ g : PowerSeries R, D = (p : PowerSeries R) * g := by
  have hc : ∀ n, ∃ c : R, coeff n D = (p : R) * c := by
    intro n
    have h1 : coeff n (red p D) = 0 := by rw [hD, map_zero]
    rw [coeff_map, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, by rw [← hc, mul_comm]⟩
  choose c hc using hc
  refine ⟨PowerSeries.mk c, ?_⟩
  ext n
  rw [hc n, show (p : PowerSeries R) = C (p : R) from (map_natCast C p).symm, coeff_C_mul, coeff_mk]

theorem red_pow_eq (σ : R ≃+* R) (hfl : FrobLift R p σ) (h : PowerSeries R) :
    red p h ^ p = red p (phi (R := R) p hp.out.pos (smap σ h)) := by
  haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p (hfl.prime.not_unit)
  haveI : CharP (PowerSeries (R ⧸ Ideal.span {(p : R)})) p :=
    charP_of_injective_algebraMap (R := R ⧸ Ideal.span {(p : R)}) (PowerSeries.C_injective) p
  have hX1 : ((frobenius (PowerSeries (R ⧸ Ideal.span {(p : R)})) p).comp (red p)) X = X ^ p := by
    simp [frobenius_def]
  have hX2 : ((red p).comp ((phi (R := R) p hp.out.pos).toRingHom.comp (smap σ))) X = X ^ p := by
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, smap, map_X, phi_X, map_sub, map_pow,
      map_add, map_one]
    rw [add_pow_char, one_pow, add_sub_cancel_left]
  suffices H : (frobenius (PowerSeries (R ⧸ Ideal.span {(p : R)})) p).comp (red p) =
      (red p).comp ((phi (R := R) p hp.out.pos).toRingHom.comp (smap σ)) by
    have := congrArg (fun F => F h) H
    simpa [frobenius_def] using this
  apply ringHom_ext_of_poly
  · apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coe_C, smap, map_C, frobenius_def, ← map_pow]
      have h1 : (phi (R := R) p hp.out.pos) (C (σ a)) = C (σ a) := (phi (R := R) p hp.out.pos).commutes (σ a)
      have h2 : Ideal.Quotient.mk (Ideal.span {(p : R)}) (σ a) = (Ideal.Quotient.mk (Ideal.span {(p : R)}) a) ^ p := by
        rw [← map_pow]; exact Ideal.Quotient.eq.2 (hfl.frob a)
      rw [h1, map_C, h2, map_pow]
    · simp only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
      rw [RingHom.comp_apply] at hX1 hX2
      rw [hX1, RingHom.comp_apply] at *
      rw [hX2]
  · rw [hX1]; exact dvd_pow_self _ hp.out.ne_zero
  · rw [hX2]; exact dvd_pow_self _ hp.out.ne_zero

end GlobalTheory.Col.NormFrob

namespace GlobalTheory.Col.NormFrob
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

theorem normOp_eq_smap_add (σ : R ≃+* R) (hfl : FrobLift R p σ)
    (b : @Module.Basis (Fin p) (PowerSeries R) (PowerSeries R) _ _
      ((phi (R := R) p hp.out.pos).toRingHom.toAlgebra.toModule)) (h : PowerSeries R) :
    ∃ r : PowerSeries R, normOp p h = smap σ h + (p : PowerSeries R) * r := by
  haveI := hfl.dom
  haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p (hfl.prime.not_unit)
  haveI : CharP (PowerSeries (R ⧸ Ideal.span {(p : R)})) p :=
    charP_of_injective_algebraMap (R := R ⧸ Ideal.span {(p : R)}) (PowerSeries.C_injective) p
  haveI : (Ideal.span {(p : R)}).IsPrime := (Ideal.span_singleton_prime hfl.prime.ne_zero).2 hfl.prime
  letI := (phi (R := R) p hp.out.pos).toRingHom.toAlgebra
  letI : Module (PowerSeries R) (PowerSeries R) := Algebra.toModule
  haveI : Module.Free (PowerSeries R) (PowerSeries R) := Module.Free.of_basis b
  have hrank : Module.finrank (PowerSeries R) (PowerSeries R) = p := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hred0 : red p (p : PowerSeries R) = 0 := by
    rw [map_natCast]; exact CharP.cast_eq_zero _ p

  have hcong : ∀ x g : PowerSeries R,
      red p (Algebra.norm (PowerSeries R) (x + (p : PowerSeries R) * g)) = red p (Algebra.norm (PowerSeries R) x) := by
    intro x g
    rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b, RingHom.map_det, RingHom.map_det, map_add (f := _),
      map_mul, map_natCast, map_add, map_mul, map_natCast]
    have hz : ((p : ℕ) : Matrix (Fin p) (Fin p) (PowerSeries (R ⧸ Ideal.span {(p : R)}))) = 0 := by
      ext i j
      rw [Matrix.natCast_apply]
      split_ifs <;> simp [CharP.cast_eq_zero]
    rw [hz, zero_mul, add_zero]
  obtain ⟨g, hg⟩ := exists_of_red_eq_zero p (h ^ p - phi (R := R) p hp.out.pos (smap σ h)) (by
    rw [map_sub, map_pow, red_pow_eq p σ hfl h, sub_self])
  have hpow : red p (normOp p h) ^ p = red p (smap σ h) ^ p := by
    have e1 : h ^ p = phi (R := R) p hp.out.pos (smap σ h) + (p : PowerSeries R) * g := by rw [← hg]; ring
    have e2 : Algebra.norm (PowerSeries R) (phi (R := R) p hp.out.pos (smap σ h)) = (smap σ h) ^ p := by
      have := Algebra.norm_algebraMap (S := PowerSeries R) (smap σ h)
      rw [hrank] at this; exact this
    unfold normOp
    rw [← map_pow, ← map_pow (Algebra.norm _), e1, hcong, e2, map_pow]
  have hinj := frobenius_inj (PowerSeries (R ⧸ Ideal.span {(p : R)})) p
  have heq : red p (normOp p h) = red p (smap σ h) := hinj (by simpa [frobenius_def] using hpow)
  obtain ⟨r, hr⟩ := exists_of_red_eq_zero p (normOp p h - smap σ h) (by rw [map_sub, heq, sub_self])
  exact ⟨r, by rw [← hr]; ring⟩

end GlobalTheory.Col.NormFrob
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormOpFrob
open GlobalTheory.Col PowerSeries

theorem GlobalTheory.Col.normOp_frob : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ →
    ∀ h : PowerSeries R, ∃ r : PowerSeries R, normOp p h = smap σ h + (p : PowerSeries R) * r := by
  intro R _ p _ σ hfl h
  obtain ⟨b, -⟩ := GlobalTheory.Col.exists_basis_one_add_X_pow R p hfl.complete
  exact GlobalTheory.Col.NormFrob.normOp_eq_smap_add p σ hfl b h
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormOpFrobStatement
open GlobalTheory.Col PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normOp_eq_smap_add_mul : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ → ∀ h : PowerSeries R, ∃ r : PowerSeries R, normOp p h = smap σ h + (p : PowerSeries R) * r := by
  first | exact @GlobalTheory.Col.normOp_frob | exact GlobalTheory.Col.normOp_frob | (intros; apply GlobalTheory.Col.normOp_frob <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormOpCongr
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormOpCongrOfBasis
noncomputable section

open PowerSeries

namespace GlobalTheory.Col

theorem trace_basis_pow {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (p : ℕ)
    (b : Module.Basis (Fin p) B A) (x : A) (y : B) (hb : ∀ i, b i = x ^ (i : ℕ))
    (hx : x ^ p = algebraMap B A y) (i : Fin p) :
    Algebra.trace B A (b i) = if (i : ℕ) = 0 then (p : B) else 0 := by
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  have hd : ∀ j : Fin p, Algebra.leftMulMatrix b (b i) j j = if (i : ℕ) = 0 then 1 else 0 := by
    intro j
    rw [Algebra.leftMulMatrix_eq_repr_mul, hb i, hb j, ← pow_add]
    by_cases h : (i : ℕ) + j < p
    · rw [← hb ⟨_, h⟩, b.repr_self, Finsupp.single_apply]
      by_cases hi : (i : ℕ) = 0
      · rw [if_pos hi, if_pos (Fin.ext (by simp only [Fin.val_mk]; omega))]
      · rw [if_neg hi, if_neg (fun h' => hi (by have := congrArg Fin.val h'; simp only [Fin.val_mk] at this; omega))]
    · have e : x ^ ((i : ℕ) + j) = y • b ⟨(i : ℕ) + j - p, by omega⟩ := by
        rw [hb, Algebra.smul_def, ← hx, ← pow_add]
        congr 1
        simp only [Fin.val_mk]
        omega
      rw [e, map_smul, b.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg, smul_zero, if_neg]
      · omega
      · simp only [Fin.ext_iff]
        omega
  simp only [Matrix.diag, hd]
  split_ifs <;> simp

theorem trace_eq_p_mul {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (p : ℕ) (hp : 0 < p)
    (b : Module.Basis (Fin p) B A) (x : A) (y : B) (hb : ∀ i, b i = x ^ (i : ℕ))
    (hx : x ^ p = algebraMap B A y) (s : A) :
    Algebra.trace B A s = (p : B) * b.repr s ⟨0, hp⟩ := by
  conv_lhs => rw [← b.sum_repr s]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, trace_basis_pow p b x y hb hx, smul_eq_mul]
  rw [Finset.sum_eq_single ⟨0, hp⟩]
  · simp [mul_comm]
  · intro j _ hj
    rw [if_neg, mul_zero]
    intro h0
    exact hj (Fin.ext h0)
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem norm_one_add_pow_mul {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (p : ℕ) (hp : 0 < p)
    (b : Module.Basis (Fin p) B A) (x : A) (y : B) (hb : ∀ i, b i = x ^ (i : ℕ))
    (hx : x ^ p = algebraMap B A y) (s : A) (k : ℕ) (hk : 1 ≤ k) :
    ∃ t : B, Algebra.norm B (1 + (p : A) ^ k * s) = 1 + (p : B) ^ (k + 1) * t := by
  have e : (p : A) ^ k * s = ((p : B) ^ k) • s := by
    rw [Algebra.smul_def, map_pow, map_natCast]
  rw [e, Algebra.norm_eq_matrix_det b, map_add (f := _), map_one, map_smul, Matrix.det_one_add_smul,
    ← Algebra.trace_eq_matrix_trace b, trace_eq_p_mul p hp b x y hb hx]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  refine ⟨b.repr s ⟨0, hp⟩ + (Matrix.det (1 + (Polynomial.X : Polynomial B) •
    (Algebra.leftMulMatrix b s).map Polynomial.C)).divX.divX.eval (((p : B)) ^ (m + 1)) * (p : B) ^ m, ?_⟩
  ring

theorem normOp_congr_of_basis (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime]
    (b : @Module.Basis (Fin p) (PowerSeries R) (PowerSeries R) _ _
      ((phi (R := R) p hp.out.pos).toRingHom.toAlgebra.toModule))
    (hb : ∀ i, b i = (1 + X : PowerSeries R) ^ (i : ℕ))
    (h₁ h₂ r : PowerSeries R) (k : ℕ) (hk : 1 ≤ k) (hu : IsUnit h₂)
    (he : h₁ = h₂ + (p : PowerSeries R) ^ k * r) :
    ∃ r' : PowerSeries R, normOp p h₁ = normOp p h₂ + (p : PowerSeries R) ^ (k + 1) * r' := by
  letI inst : Algebra (PowerSeries R) (PowerSeries R) := (phi (R := R) p hp.out.pos).toRingHom.toAlgebra
  have hx : (1 + X : PowerSeries R) ^ p = algebraMap (PowerSeries R) (PowerSeries R) (1 + X) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact (phi_one_add_X (R := R) p hp.out.pos).symm
  have hN : ∀ z, normOp p z = Algebra.norm (PowerSeries R) z := fun z => rfl
  obtain ⟨u, rfl⟩ := hu
  have h1 : h₁ = (u : PowerSeries R) * (1 + (p : PowerSeries R) ^ k * ((↑u⁻¹ : PowerSeries R) * r)) := by
    have hui := u.mul_inv
    linear_combination he - ((p : PowerSeries R) ^ k * r) * hui
  obtain ⟨t, ht⟩ := @norm_one_add_pow_mul (PowerSeries R) (PowerSeries R) _ _ inst p hp.out.pos b (1 + X) (1 + X)
    hb hx ((↑u⁻¹ : PowerSeries R) * r) k hk
  refine ⟨normOp p (u : PowerSeries R) * t, ?_⟩
  rw [h1, hN, hN, map_mul, ht]
  ring

end GlobalTheory.Col
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormOpCongr
open GlobalTheory.Col PowerSeries

namespace GlobalTheory.Col

theorem normOp_congr : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ →
    ∀ (h₁ h₂ r : PowerSeries R) (k : ℕ), 1 ≤ k → IsUnit h₂ → h₁ = h₂ + (p : PowerSeries R) ^ k * r →
    ∃ r' : PowerSeries R, normOp p h₁ = normOp p h₂ + (p : PowerSeries R) ^ (k + 1) * r' := by
  intro R _ p hp σ hF h₁ h₂ r k hk hu he
  obtain ⟨b, hb⟩ := exists_basis_one_add_X_pow R p hF.complete
  exact normOp_congr_of_basis R p b hb h₁ h₂ r k hk hu he

end GlobalTheory.Col
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormOpCongrStatement
open GlobalTheory.Col PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normOp_congr_mod_pow_succ : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ → ∀ (h₁ h₂ r : PowerSeries R) (k : ℕ), 1 ≤ k → IsUnit h₂ → h₁ = h₂ + (p : PowerSeries R) ^ k * r → ∃ r' : PowerSeries R, normOp p h₁ = normOp p h₂ + (p : PowerSeries R) ^ (k + 1) * r' := by
  first | exact @GlobalTheory.Col.normOp_congr | exact GlobalTheory.Col.normOp_congr | (intros; apply GlobalTheory.Col.normOp_congr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColemanNormOperatorPowerSeriesCoeffAutMapComm
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColemanNormOperatorPowerSeriesCoeffAutMapComm
open GlobalTheory.Col PowerSeries

noncomputable section

namespace GlobalTheory.Col.NormCoeff

variable {R : Type} [CommRing R]

def smapEquiv (σ : R ≃+* R) : PowerSeries R ≃+* PowerSeries R :=
  RingEquiv.ofRingHom (smap σ) (smap σ.symm)
    (by ext h n; simp [PowerSeries.coeff_map])
    (by ext h n; simp [PowerSeries.coeff_map])

theorem smapEquiv_apply (σ : R ≃+* R) (h : PowerSeries R) : smapEquiv σ h = smap σ h := rfl

theorem map_phi (p : ℕ) (hp : 0 < p) (f : R →+* R) (h : PowerSeries R) :
    PowerSeries.map f (phi (R := R) p hp h) = phi (R := R) p hp (PowerSeries.map f h) := by
  unfold phi
  rw [PowerSeries.coe_substAlgHom]
  have key := PowerSeries.map_subst (hasSubst_om (R := R) p hp) (h := f) h
  have e : (MvPowerSeries.map f) (((1 + PowerSeries.X : PowerSeries R) ^ p) - 1)
      = ((1 + PowerSeries.X : PowerSeries R) ^ p) - 1 := by
    change PowerSeries.map f _ = _
    simp
  rw [e] at key
  exact key

theorem normOp_smap (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R) (h : PowerSeries R) :
    normOp p (smap σ h) = smap σ (normOp p h) := by
  have key := @Algebra.norm_eq_of_equiv_equiv (PowerSeries R) (PowerSeries R) (PowerSeries R) (PowerSeries R)
    _ _ _ _ (phi (R := R) p hp.out.pos).toRingHom.toAlgebra (phi (R := R) p hp.out.pos).toRingHom.toAlgebra
    (smapEquiv σ) (smapEquiv σ) (by
      ext1 x
      exact (map_phi p hp.out.pos (σ : R →+* R) x).symm) h
  have key2 : normOp p h = (smapEquiv σ).symm (normOp p (smap σ h)) := key
  rw [key2, ← smapEquiv_apply, ← smapEquiv_apply, RingEquiv.apply_symm_apply]

end GlobalTheory.Col.NormCoeff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColemanNormOperatorPowerSeriesCoeffAutMapCommStatement
open GlobalTheory.Col PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colemanNormOperator_powerSeriesCoeffAutMap_comm : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R) (h : PowerSeries R), normOp p (smap σ h) = smap σ (normOp p h) := by
  first | exact @GlobalTheory.Col.NormCoeff.normOp_smap | exact GlobalTheory.Col.NormCoeff.normOp_smap | (intros; apply GlobalTheory.Col.NormCoeff.normOp_smap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColemanNormOperatorIterateSuccCongrFrobenius
open GlobalTheory.Col PowerSeries

namespace GlobalTheory

theorem normOp_isUnit {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime] {h : PowerSeries R} (hu : IsUnit h) :
    IsUnit (normOp p h) := by
  unfold normOp
  exact hu.map _

theorem normOp_iterate_isUnit {R : Type} [CommRing R] (p : ℕ) [Fact p.Prime] {h : PowerSeries R} (hu : IsUnit h)
    (j : ℕ) : IsUnit ((normOp p)^[j] h) := by
  induction j with
  | zero => simpa using hu
  | succ j ih => rw [Function.iterate_succ_apply']; exact normOp_isUnit p ih

theorem normOp_iterate_congr : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ →
    ∀ (h : PowerSeries R), IsUnit h → ∀ j : ℕ, ∃ r : PowerSeries R,
      (normOp p)^[j + 1] h = smap σ ((normOp p)^[j] h) + (p : PowerSeries R) ^ (j + 1) * r := by
  intro R _ p hp σ hσ h hu j
  induction j with
  | zero =>
    obtain ⟨r, hr⟩ := GlobalTheory.T.normOp_eq_smap_add_mul R p σ hσ h
    exact ⟨r, by simpa using hr⟩
  | succ j ih =>
    obtain ⟨r, hr⟩ := ih
    have hu2 : IsUnit (smap σ ((normOp p)^[j] h)) := (normOp_iterate_isUnit p hu j).map _
    obtain ⟨r', hr'⟩ := GlobalTheory.T.normOp_congr_mod_pow_succ R p σ hσ _ _ r (j + 1) (by omega) hu2 hr
    refine ⟨r', ?_⟩
    rw [Function.iterate_succ_apply' (normOp p) (j + 1), hr', GlobalTheory.T.colemanNormOperator_powerSeriesCoeffAutMap_comm R p σ, ← Function.iterate_succ_apply' (normOp p) j]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColemanNormOperatorIterateSuccCongrFrobeniusStatement
open GlobalTheory.Col PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.colemanNormOperator_iterate_succ_congr_frobenius : ∀ (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R), FrobLift R p σ → ∀ (h : PowerSeries R), IsUnit h → ∀ j : ℕ, ∃ r : PowerSeries R, (normOp p)^[j + 1] h = smap σ ((normOp p)^[j] h) + (p : PowerSeries R) ^ (j + 1) * r := by
  first | exact @GlobalTheory.normOp_iterate_congr | exact GlobalTheory.normOp_iterate_congr | (intros; apply GlobalTheory.normOp_iterate_congr <;> assumption)
end
