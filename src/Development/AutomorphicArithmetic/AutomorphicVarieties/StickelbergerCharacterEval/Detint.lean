module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.MemZpowersIff
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.BNzC

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.GroupRingCharEvalStickelbergerYNeZeroOfParity
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.Chitheta
open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.groupRingCharEval_stickelbergerTheta_eq_neg_genBernoulli :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] {N : ℕ} [NeZero N] {Γ : Type} [CommGroup Γ] (π : (ZMod N)ˣ →* Γ) (χ : Γ →* Ωˣ) (k : ℕ), 2 ≤ N → ev ℚ χ (thetaEl k π) = -genB k (dirOf π χ) / k := by
  intro Ω _ _ N _ Γ _ π χ k hN
  haveI : Fact (1 < N) := ⟨hN⟩
  have hsum : ∀ f : ZMod N → Ω, (∀ x, ¬ IsUnit x → f x = 0) →
      ∑ x, f x = ∑ u : (ZMod N)ˣ, f u := by
    intro f hf
    symm
    rw [show ∑ u : (ZMod N)ˣ, f u = ∑ x ∈ Finset.univ.map ⟨Units.val, Units.val_injective⟩, f x by
      rw [Finset.sum_map]; rfl]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro x _ hx
    apply hf
    rintro ⟨u, rfl⟩
    exact hx (Finset.mem_map.2 ⟨u, Finset.mem_univ _, rfl⟩)
  have h1 : ∑ a ∈ Icc 1 N, dirOf π χ (a : ZMod N) * algebraMap ℚ Ω (bcoef N k a) =
      ∑ a ∈ Icc 1 N, dirOf π χ (a : ZMod N) * algebraMap ℚ Ω (bcoef N k (a : ZMod N).val) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    obtain ⟨_, h2⟩ := Finset.mem_Icc.1 ha
    rcases h2.lt_or_eq with h | rfl
    · rw [ZMod.val_cast_of_lt h]
    · rw [ZMod.natCast_self, MulChar.map_nonunit _ not_isUnit_zero, zero_mul, zero_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [thetaEl, sumEl, map_neg, map_sum, ev_single, genB, Ek]
  rw [h1, b_sumicc (fun x : ZMod N => dirOf π χ x * algebraMap ℚ Ω (bcoef N k x.val)),
    hsum _ (fun x hx => by simp [MulChar.map_nonunit _ hx])]
  simp only [dirOf_unit]
  rw [neg_div, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_div₀, map_natCast]
  ring
end

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.groupRingCharEval_stickelbergerY_eq_euler_mul_genBernoulli :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] {N : ℕ} [NeZero N] {Γ : Type} [CommGroup Γ] (π : (ZMod N)ˣ →* Γ) (χ : Γ →* Ωˣ) (a : ℕ) (ha : a.Coprime N) (k : ℕ), 2 ≤ N → ev ℚ χ (yEl k a ha π) = (1 - (a : Ω) ^ k * dirOf π χ (a : ZMod N)) * (-genB k (dirOf π χ) / k) := by
  intro Ω _ _ N _ Γ _ π χ a ha k hN
  rw [yEl, map_mul, map_sub, map_one, ev_single, groupRingCharEval_stickelbergerTheta_eq_neg_genBernoulli π χ k hN, ← dirOf_unit, ZMod.coe_unitOfCoprime]
  simp

theorem UpperTheory.V.B5.groupRingCharEval_stickelbergerY_ne_zero_of_parity :
    ∀ {N : ℕ} [NeZero N] {Γ : Type} [CommGroup Γ] (π : (ZMod N)ˣ →* Γ) (χ : Γ →* ℂˣ) (a : ℕ) (ha : a.Coprime N) (k : ℕ), 2 ≤ N → 2 ≤ a → 2 ≤ k → ((χ (π (-1)) : ℂˣ) : ℂ) = (-1) ^ k → ev ℚ χ (yEl k a ha π) ≠ 0 := by
  intro N _ Γ _ π χ a ha k hN h2a hk hs
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hpar : dirOf π χ (-1) = (-1) ^ k := by
    have := dirOf_unit π χ (-1)
    rw [map_inv, Units.val_inv_eq_inv_val, hs, Units.val_neg, Units.val_one] at this
    rw [this, ← inv_pow, inv_neg, inv_one]
  rw [groupRingCharEval_stickelbergerY_eq_euler_mul_genBernoulli π χ a ha k hN]
  refine mul_ne_zero (fun h => ?_) (div_ne_zero (neg_ne_zero.2 ((b_nzC _ k (by omega) hpar).2 hk)) hk0)
  have h1 : ‖dirOf π χ (a : ZMod N)‖ = 1 := by
    rw [← ZMod.coe_unitOfCoprime a ha]; exact DirichletCharacter.unit_norm_eq_one _ _
  have h2 := congrArg norm (sub_eq_zero.1 h)
  rw [norm_one, norm_mul, h1, norm_pow, Complex.norm_natCast, mul_one] at h2
  have h3 : 1 < a ^ k := Nat.one_lt_pow (by omega) (by omega)
  exact h3.ne (by exact_mod_cast h2)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.Chcard
open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

private def chOne {Ω : Type} [Field Ω] {Γ : Type} [CommGroup Γ] (c : Γ) :
    Ch Ω c 1 ≃ ((Γ ⧸ Subgroup.zpowers c) →* Ωˣ) where
  toFun χ := QuotientGroup.lift (Subgroup.zpowers c) χ.1 (by
    have h : χ.1 c = 1 := Units.ext (by simpa using χ.2)
    rintro _ ⟨n, rfl⟩
    simp [h])
  invFun ψ := ⟨ψ.comp (QuotientGroup.mk' _), by
    have h : (QuotientGroup.mk c : Γ ⧸ Subgroup.zpowers c) = 1 :=
      (QuotientGroup.eq_one_iff c).2 (Subgroup.mem_zpowers c)
    simp [h]⟩
  left_inv χ := Subtype.ext (MonoidHom.ext fun g => rfl)
  right_inv ψ := MonoidHom.ext fun g => by
    induction g using QuotientGroup.induction_on with
    | H g => rfl

private def chMul {Ω : Type} [Field Ω] {Γ : Type} [CommGroup Γ] (c : Γ) (ε : ℤ) (χ₀ : Ch Ω c ε) :
    Ch Ω c 1 ≃ Ch Ω c ε where
  toFun χ := ⟨χ₀.1 * χ.1, by simp [χ₀.2, χ.2]⟩
  invFun χ := ⟨χ₀.1⁻¹ * χ.1, by
    have h : χ.1 c = χ₀.1 c := Units.ext (χ.2.trans χ₀.2.symm)
    simp [h]⟩
  left_inv χ := Subtype.ext (inv_mul_cancel_left _ _)
  right_inv χ := Subtype.ext (mul_inv_cancel_left _ _)

theorem UpperTheory.V.B5.card_signedInvolutionChar_eq_card_involutionQuotient :
    ∀ {Ω : Type} [Field Ω] {Γ : Type} [CommGroup Γ] [Finite Γ] [HasEnoughRootsOfUnity Ω (Monoid.exponent Γ)] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → Fintype.card (Ch Ω c ε) = Fintype.card (Qc c) := by
  intro Ω _ Γ _ _ _ c ε h2 hc hε
  classical
  have hne₀ : Nonempty (Ch Ω c ε) := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' hε with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact ⟨⟨1, by simp⟩⟩
    · obtain ⟨φ, hφ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity Γ Ω hc
      refine ⟨⟨φ, ?_⟩⟩
      have hsq : (φ c : Ω) * (φ c : Ω) = 1 := by
        rw [← Units.val_mul, ← map_mul, h2, map_one, Units.val_one]
      have hne : (φ c : Ω) ≠ 1 := fun h => hφ (Units.ext (by simpa using h))
      rcases mul_self_eq_one_iff.mp hsq with h | h
      · exact absurd h hne
      · simpa using h
  obtain ⟨χ₀⟩ := hne₀
  haveI : NeZero (Monoid.exponent Γ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  haveI : HasEnoughRootsOfUnity Ω (Monoid.exponent (Γ ⧸ Subgroup.zpowers c)) :=
    HasEnoughRootsOfUnity.of_dvd Ω (Group.exponent_quotient_dvd _)
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
    Nat.card_congr ((chMul c ε χ₀).symm.trans (chOne c)),
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity]
  rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.NormCharEvalHigherStickelbergerLe
open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.norm_charEval_higherStickelberger_le :
    ∀ {N : ℕ} [NeZero N] {Γ : Type} [CommGroup Γ] (π : (ZMod N)ˣ →* Γ) (χ : Γ →* ℂˣ) (a : ℕ) (ha : a.Coprime N) (k : ℕ), 2 ≤ N → 1 ≤ k → ‖ev ℚ χ (yEl k a ha π)‖ ≤ (sizeY N a k : ℝ) := by
  intro N _ Γ _ π χ a ha k hN hk
  have ha1 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h
      have h' := (Nat.coprime_zero_left N).mp ha
      omega
    · exact h
  rw [groupRingCharEval_stickelbergerY_eq_euler_mul_genBernoulli π χ a ha k hN]
  set d := dirOf π χ
  have hd : ∀ x, ‖d x‖ ≤ 1 := fun x => DirichletCharacter.norm_le_one d x
  have hB := b_upper k (⇑d) (by omega) hd
  have h1 : ‖(1 : ℂ) - (a : ℂ) ^ k * d (a : ZMod N)‖ ≤ 2 * (a : ℝ) ^ k := by
    calc ‖(1 : ℂ) - (a : ℂ) ^ k * d (a : ZMod N)‖
        ≤ ‖(1 : ℂ)‖ + ‖(a : ℂ) ^ k * d (a : ZMod N)‖ := norm_sub_le _ _
      _ ≤ 1 + (a : ℝ) ^ k * 1 := by
          rw [norm_one, norm_mul, norm_pow, Complex.norm_natCast]
          gcongr
          exact hd _
      _ ≤ 2 * (a : ℝ) ^ k := by
          have : (1 : ℝ) ≤ (a : ℝ) ^ k := one_le_pow₀ (by exact_mod_cast ha1)
          linarith
  have hpi : (4 : ℝ) ≤ (2 * Real.pi) ^ k := by
    calc (4 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
      _ = (2 * Real.pi) ^ 1 := (pow_one _).symm
      _ ≤ (2 * Real.pi) ^ k := pow_le_pow_right₀ (by linarith [Real.pi_gt_three]) hk
  have h2 : ‖genB k ⇑d‖ ≤ (N : ℝ) ^ k * k.factorial := by
    calc ‖genB k ⇑d‖ ≤ 4 * (N : ℝ) ^ k * k.factorial / (2 * Real.pi) ^ k := hB
      _ ≤ (N : ℝ) ^ k * k.factorial := by
        rw [div_le_iff₀ (by positivity)]
        have : 0 ≤ (N : ℝ) ^ k * k.factorial := by positivity
        nlinarith
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [norm_mul, norm_div, norm_neg, Complex.norm_natCast]
  calc ‖(1 : ℂ) - (a : ℂ) ^ k * d (a : ZMod N)‖ * (‖genB k ⇑d‖ / k)
      ≤ 2 * (a : ℝ) ^ k * ((N : ℝ) ^ k * k.factorial) := by
        apply mul_le_mul h1 _ (by positivity) (by positivity)
        rw [div_le_iff₀ (by linarith)]
        nlinarith [norm_nonneg (genB k ⇑d)]
    _ = (sizeY N a k : ℝ) := by
        rw [sizeY]
        push_cast
        ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.Detprod
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.LinearIndependentCharactersOnQuotientReps
open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.linearIndependent_characters_on_quotientReps :
    ∀ {Ω : Type} [Field Ω] {Γ : Type} [CommGroup Γ] (c : Γ) (ε : ℤ), c * c = 1 → LinearIndependent Ω (fun χ : Ch Ω c ε => fun i : Qc c => ((χ.1 (rep i) : Ωˣ) : Ω)) := by
  intro Ω _ Γ _ c ε h2
  classical
  have hw : LinearIndependent Ω (fun χ : Ch Ω c ε => fun g : Γ => ((χ.1 g : Ωˣ) : Ω)) := by
    have := (linearIndependent_monoidHom Γ Ω).comp
      (fun χ : Ch Ω c ε => (Units.coeHom Ω).comp χ.1) (by
        intro χ ψ h
        apply Subtype.ext
        ext g
        exact congrArg (fun f : Γ →* Ω => f g) h)
    exact this
  rw [linearIndependent_iff'] at hw ⊢
  intro s a hs
  apply hw s a
  funext g
  have hg := (mk_eq_mk h2 (rep (Qc.mk c g)) g).mp (mk_rep _)
  have hi := congrFun hs (Qc.mk c g)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hi ⊢
  generalize rep (Qc.mk c g) = r at hg hi
  rcases hg with rfl | rfl
  · exact hi
  · calc ∑ χ ∈ s, a χ * ((χ.1 (c * r) : Ωˣ) : Ω)
        = ∑ χ ∈ s, (ε : Ω) * (a χ * ((χ.1 r : Ωˣ) : Ω)) :=
          Finset.sum_congr rfl (fun χ _ => by rw [map_mul, Units.val_mul, χ.2]; ring)
      _ = (ε : Ω) * ∑ χ ∈ s, a χ * ((χ.1 r : Ωˣ) : Ω) := by rw [Finset.mul_sum]
      _ = 0 := by rw [hi, mul_zero]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.SumCharMulQuotientMatrixEqCharEvalMul
open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

private theorem ev_eq_sum {A : Type} [CommRing A] {Ω : Type} [Field Ω] [Algebra A Ω] {Γ : Type} [CommGroup Γ] [Fintype Γ]
    (χ : Γ →* Ωˣ) (z : MonoidAlgebra A Γ) :
    ev A χ z = ∑ g, algebraMap A Ω (z.coeff g) * ((χ g : Ωˣ) : Ω) := by
  classical
  induction z using MonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy, add_mul, Finset.sum_add_distrib]
  | single g n =>
    rw [ev_single, Finset.sum_eq_single g]
    · simp
    · intro b _ hb
      simp [Finsupp.single_apply, hb, hb.symm]
    · simp

theorem UpperTheory.V.B5.sum_char_mul_quotientMatrix_eq_charEval_mul :
    ∀ {A : Type} [CommRing A] {Ω : Type} [Field Ω] [Algebra A Ω] {Γ : Type} [CommGroup Γ] [Finite Γ] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ∀ (χ : Ch Ω c ε) (z : MonoidAlgebra A Γ) (j : Qc c), ∑ i : Qc c, ((χ.1 (rep i) : Ωˣ) : Ω) * algebraMap A Ω (mat c ε z i j) = ev A χ.1 z * ((χ.1 (rep j) : Ωˣ) : Ω) := by
  intro A _ Ω _ _ Γ _ _ c ε h2 h1 χ z j
  have := Fintype.ofFinite Γ
  have hc : ((χ.1 c : Ωˣ) : Ω) = (ε : Ω) := χ.2
  rw [ev_eq_sum, Finset.sum_mul, ← Equiv.sum_comp (Equiv.mulRight (rep j)⁻¹), sum_rep h2 h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hj : ((χ.1 (rep j) : Ωˣ) : Ω) ≠ 0 := Units.ne_zero _
  simp only [mat, Matrix.of_apply, Equiv.coe_mulRight, map_add (f := _), map_mul, map_intCast, mul_assoc, map_inv,
    Units.val_mul, Units.val_inv_eq_inv_val, hc, inv_mul_cancel₀ hj]
  ring
end

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.det_mul_quotientByOrderTwo_eq_prod_charEval :
    ∀ {A : Type} [CommRing A] {Ω : Type} [Field Ω] [Algebra A Ω] {Γ : Type} [CommGroup Γ] [Finite Γ] [HasEnoughRootsOfUnity Ω (Monoid.exponent Γ)] (c : Γ) (ε : ℤ), c * c = 1 → c ≠ 1 → ε * ε = 1 → ∀ z : MonoidAlgebra A Γ, algebraMap A Ω (detR c ε z) = ∏ χ : Ch Ω c ε, ev A χ.1 z := by
  intro A _ Ω _ _ Γ _ _ _ c ε hc hc1 hε z
  classical
  have hcard := card_signedInvolutionChar_eq_card_involutionQuotient (Ω := Ω) c ε hc hc1 hε
  let e : Ch Ω c ε ≃ Qc c := Fintype.equivOfCardEq hcard
  let P : Matrix (Qc c) (Qc c) Ω := Matrix.of fun k i => ((e.symm k).1 (rep i) : Ω)
  let M : Matrix (Qc c) (Qc c) Ω := (algebraMap A Ω).mapMatrix (mat c ε z)
  let d : Qc c → Ω := fun k => ev A (e.symm k).1 z
  have hPM : P * M = Matrix.diagonal d * P := by
    ext k j
    rw [Matrix.mul_apply, Matrix.diagonal_mul]
    simp only [P, M, d, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    exact sum_char_mul_quotientMatrix_eq_charEval_mul c ε hc hc1 (e.symm k) z j
  have hind : LinearIndependent Ω (fun k => P k) :=
    (linearIndependent_characters_on_quotientReps (Ω := Ω) c ε hc).comp e.symm e.symm.injective
  have hP : IsUnit P := Matrix.linearIndependent_rows_iff_isUnit.mp hind
  have hdet : P.det ≠ 0 := (Matrix.isUnit_iff_isUnit_det P |>.mp hP).ne_zero
  have h2 : P.det * M.det = (∏ k, d k) * P.det := by
    rw [← Matrix.det_mul, hPM, Matrix.det_mul, Matrix.det_diagonal]
  have h3 : M.det = ∏ k, d k := by
    have := h2
    rw [mul_comm ((∏ k, d k))] at this
    exact mul_left_cancel₀ hdet this
  have h4 : algebraMap A Ω (detR c ε z) = M.det := by
    unfold detR
    rw [RingHom.map_det]
  rw [h4, h3]
  exact Equiv.prod_comp e.symm (fun χ => ev A χ.1 z)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerCharacterEval.ExistsIntHigherStickelbergerDenomSmul
open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

private theorem primorial_dvd_fact (n : ℕ) : primorial n ∣ n.factorial := by
  rw [primorial, ← Finset.prod_Ico_id_eq_factorial]
  apply Finset.prod_dvd_prod_of_subset
  intro p hp
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  simp only [Finset.mem_Ico]
  exact ⟨hp.2.one_lt.le, hp.1⟩

private theorem denY_Ek (N k : ℕ) (hN : 0 < N) (hk : 1 ≤ k) (b : ZMod N) :
    ∃ z : ℤ, (z : ℚ) = (denY N k : ℚ) * Ek N k b := by
  obtain ⟨z, hz⟩ := b_denint N k b.val hN
  obtain ⟨c, hc⟩ := primorial_dvd_fact (k + 1)
  refine ⟨c * z, ?_⟩
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  simp only [denY, Ek, den] at hz ⊢
  push_cast [hc] at hz ⊢
  rw [← hz]
  field_simp

theorem UpperTheory.V.B5.exists_int_higherStickelbergerDenom_smul :
    ∀ {N : ℕ} [NeZero N] {Γ : Type} [CommGroup Γ] (π : (ZMod N)ˣ →* Γ) (a : ℕ) (ha : a.Coprime N) (k : ℕ), 1 ≤ k → ∃ z : MonoidAlgebra ℤ Γ, coefMap ℚ Γ z = (denY N k : ℚ) • yEl k a ha π := by
  intro N _ Γ _ π a ha k hk
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  choose w hw using fun b : ZMod N => denY_Ek N k hN hk b
  refine ⟨(1 - MonoidAlgebra.single (π (ZMod.unitOfCoprime a ha))⁻¹ ((a : ℤ) ^ k)) *
    -∑ b : (ZMod N)ˣ, MonoidAlgebra.single (π b)⁻¹ (w b), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [yEl, thetaEl, sumEl, map_mul, map_sub, map_one, map_neg, map_sum, coefMap_single, hw]
  push_cast
  rw [← mul_smul_comm, smul_neg, Finset.smul_sum]
  simp only [MonoidAlgebra.smul_single']
end

open Finset UpperTheory.V.Bern UpperTheory.V.B4 UpperTheory.V.B5

theorem UpperTheory.V.B5.higherStickelberger_det_exists_int_bounded :
    ∀ {N : ℕ} [NeZero N] {Γ : Type} [CommGroup Γ] [Finite Γ] (π : (ZMod N)ˣ →* Γ) (a : ℕ) (ha : a.Coprime N) (k : ℕ), 2 ≤ a → 2 ≤ k → π (-1) ≠ 1 → ∃ X : ℤ, X ≠ 0 ∧ X.natAbs ≤ bdX N a k ^ (Nat.card Γ / 2) ∧ (X : ℚ) = (denY N k : ℚ) ^ (Nat.card Γ / 2) * detR (π (-1)) ((-1) ^ k) (yEl k a ha π) := by
  intro N _ Γ _ _ π a ha k h2a hk hc
  have hN : 2 ≤ N := by
    by_contra h
    have h0 := NeZero.ne N
    obtain rfl : N = 1 := by omega
    exact hc (by rw [Subsingleton.elim (-1 : (ZMod 1)ˣ) 1, map_one])
  have hcc : π (-1) * π (-1) = 1 := by rw [← map_mul]; simp
  have hε : ((-1 : ℤ) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow]; simp
  haveI : NeZero (Monoid.exponent Γ : ℂ) := ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩
  obtain ⟨z, hz⟩ := exists_int_higherStickelbergerDenom_smul π a ha k (by omega)
  have hX : ((detR (π (-1)) ((-1) ^ k) z : ℤ) : ℚ) =
      (denY N k : ℚ) ^ (Nat.card Γ / 2) * detR (π (-1)) ((-1) ^ k) (yEl k a ha π) := by
    rw [← detR_coefMap, hz, detR_smul, card_Qc' hcc hc]
  have hp := det_mul_quotientByOrderTwo_eq_prod_charEval (A := ℚ) (Ω := ℂ) (π (-1)) ((-1) ^ k) hcc hc hε (yEl k a ha π)
  have hD : (0 : ℚ) < denY N k := by exact_mod_cast denY_pos (by omega) (by omega)
  refine ⟨_, ?_, ?_, hX⟩
  · have : algebraMap ℚ ℂ (detR (π (-1)) ((-1) ^ k) (yEl k a ha π)) ≠ 0 := by
      rw [hp]
      exact Finset.prod_ne_zero_iff.2 fun χ _ => groupRingCharEval_stickelbergerY_ne_zero_of_parity π χ.1 a ha k hN h2a hk (by simpa using χ.2)
    intro h
    rw [h, Int.cast_zero, eq_comm, mul_eq_zero] at hX
    rcases hX with h | h
    · exact (pow_pos hD _).ne' h
    · exact this (by rw [h, map_zero])
  · have h1 : ‖algebraMap ℚ ℂ (detR (π (-1)) ((-1) ^ k) (yEl k a ha π))‖ ≤ (sizeY N a k : ℝ) ^ (Nat.card Γ / 2) := by
      rw [hp, norm_prod, ← card_Qc' hcc hc, ← card_signedInvolutionChar_eq_card_involutionQuotient (Ω := ℂ) _ _ hcc hc hε, ← Finset.card_univ, ← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun χ _ => norm_charEval_higherStickelberger_le π χ.1 a ha k hN (by omega)
    have h2 : (((detR (π (-1)) ((-1) ^ k) z).natAbs : ℕ) : ℝ) = ‖algebraMap ℚ ℂ ((detR (π (-1)) ((-1) ^ k) z : ℤ) : ℚ)‖ := by
      rw [map_intCast, Complex.norm_intCast, Nat.cast_natAbs, Int.cast_abs]
    have h3 : (((detR (π (-1)) ((-1) ^ k) z).natAbs : ℕ) : ℝ) ≤ ((bdX N a k ^ (Nat.card Γ / 2) : ℕ) : ℝ) := by
      rw [h2, hX, map_mul, norm_mul, map_pow, norm_pow, map_natCast, Complex.norm_natCast, bdX]
      push_cast
      rw [mul_pow]
      gcongr
    exact_mod_cast h3
