module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LevelNFunctionGaloisConjQExpansion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisExponentRootOfUnityExpTwoPiI
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisExponentRootOfUnityExpTwoPiI
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.ZetaExp

theorem pow_mod_eq {M : Type*} [Monoid M] {w : M} {N : ℕ} (h : w ^ N = 1) (a : ℕ) : w ^ (a % N) = w ^ a := by
  conv_rhs => rw [← Nat.mod_add_div a N, pow_add, pow_mul, h, one_pow, mul_one]

theorem ch_eq_pow (N : ℕ) (j : ZMod N) :
    ch N j = Complex.exp (2 * Real.pi * Complex.I * (((1 : ℚ) / N : ℚ) : ℂ)) ^ j.val := by
  rw [ch, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem main : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (s : Ω ≃ₐ[ℚ] Ω) (N : ℕ), 0 < N → (∃ d : ℤ, s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d) ∧ ∀ d : ℤ, s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∃ u : (ZMod N)ˣ, (u : ZMod N) = d ∧ ∀ g : ℂ ≃+* ℂ, (∀ x, g (ε x) = ε (s x)) → ZetaAct g N u := by
  intro Ω _ _ _ ε s N hN
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨_, hval, _, _, hprim, _⟩ := GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties Ω ε
  set ζ := eOm ε (1 / N) with hζ
  have hp : IsPrimitiveRoot ζ N := hprim N hN
  have hsp : IsPrimitiveRoot (s ζ) N := hp.map_of_injective s.injective
  refine ⟨?_, ?_⟩
  · obtain ⟨i, -, hi⟩ := hp.eq_pow_of_pow_eq_one hsp.pow_eq_one
    exact ⟨i, by rw [← hi, zpow_natCast]⟩
  · intro d hd
    set i : ℕ := (d % (N : ℤ)).toNat with hi
    have hnn : 0 ≤ d % (N : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hN.ne')
    have hic : (i : ℤ) = d % (N : ℤ) := Int.toNat_of_nonneg hnn
    have hζi : ζ ^ d = ζ ^ i := by
      rw [← zpow_natCast, hic]
      have hz : ζ ≠ 0 := hp.ne_zero hN.ne'
      conv_lhs => rw [← Int.mul_ediv_add_emod d N, zpow_add₀ hz, zpow_mul, zpow_natCast, hp.pow_eq_one, one_zpow, one_mul]
    have hsi : s ζ = ζ ^ i := hd.trans hζi
    have hcop : i.Coprime N := (hp.pow_iff_coprime hN i).1 (hsi ▸ hsp)
    have hdi : ((d : ZMod N)) = (i : ZMod N) := by
      rw [← Int.cast_natCast, hic, ZMod.intCast_mod]
    have hu : IsUnit (i : ZMod N) := (ZMod.isUnit_iff_coprime i N).2 hcop
    refine ⟨hu.unit, by rw [IsUnit.unit_spec, hdi], ?_⟩
    intro g hg j
    have hεζ : ε ζ = Complex.exp (2 * Real.pi * Complex.I * (((1 : ℚ) / N : ℚ) : ℂ)) := hval _
    have hηN : (ε ζ) ^ N = 1 := by rw [← map_pow, hp.pow_eq_one, map_one]
    have hl : g ((ε ζ) ^ j.val) = (ε ζ) ^ (i * j.val) := by
      rw [map_pow, hg, hsi, map_pow, ← pow_mul]
    have hr : ((i : ZMod N) * j).val = (i * j.val) % N := by
      rw [ZMod.val_mul, ZMod.val_natCast, Nat.mod_mul_mod]
    rw [ch_eq_pow, ch_eq_pow, ← hεζ, hl, IsUnit.unit_spec, hr, pow_mod_eq hηN]

end GlobalTheory.ZetaExp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisExponentRootOfUnityExpTwoPiIStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_exponent_rootOfUnity_expTwoPiI : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (s : Ω ≃ₐ[ℚ] Ω) (N : ℕ), 0 < N → (∃ d : ℤ, s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d) ∧ ∀ d : ℤ, s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∃ u : (ZMod N)ˣ, (u : ZMod N) = d ∧ ∀ g : ℂ ≃+* ℂ, (∀ x, g (ε x) = ε (s x)) → ZetaAct g N u := by
  first | exact @GlobalTheory.ZetaExp.main | exact GlobalTheory.ZetaExp.main | (intros; apply GlobalTheory.ZetaExp.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoDiagConjCongruenceIffDiagOneUnitMatrixEq
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoDiagConjCongruenceIffDiagOneUnitMatrixEq
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNCong

theorem cong_iff_dg : ∀ (N : ℕ) (d : ℤ) (u : (ZMod N)ˣ), (u : ZMod N) = d → ∀ γ γ' : SL(2, ℤ),
    Cong N d γ γ' ↔ dg u * redGL N γ' = redGL N γ * dg u := by
  intro N d u hu γ γ'
  have key : (dg u * redGL N γ' = redGL N γ * dg u) ↔
      ((dg u : Matrix (Fin 2) (Fin 2) (ZMod N)) * (redGL N γ' : Matrix (Fin 2) (Fin 2) (ZMod N)) =
        (redGL N γ : Matrix (Fin 2) (Fin 2) (ZMod N)) * (dg u : Matrix (Fin 2) (Fin 2) (ZMod N))) := by
    constructor
    · intro h; rw [← Units.val_mul, h, Units.val_mul]
    · intro h; ext1; simpa using h
  rw [key]
  have hM : ∀ δ : SL(2, ℤ), (redGL N δ : Matrix (Fin 2) (Fin 2) (ZMod N)) =
      !![(en δ 0 0 : ZMod N), en δ 0 1; en δ 1 0, en δ 1 1] := by
    intro δ
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  have hD : (dg u : Matrix (Fin 2) (Fin 2) (ZMod N)) = !![1, 0; 0, (d : ZMod N)] := by
    show !![1, 0; 0, (u : ZMod N)] = _
    rw [hu]
  rw [hM, hM, hD, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp only [Cong, ← Matrix.ext_iff, Fin.forall_fin_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons, one_mul, zero_mul, add_zero,
    zero_add, mul_one, mul_zero]
  have hdu : IsUnit (d : ZMod N) := hu ▸ u.isUnit
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨⟨h1, ?_⟩, ?_, ?_⟩
    · rw [h2, mul_comm]
    · rw [h3]
    · rw [h4, mul_comm]
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, ?_, h3, ?_⟩
    · rw [h2, mul_comm]
    · rw [mul_comm] at h4
      exact hdu.mul_right_cancel h4

end GlobalTheory.FNCong
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoDiagConjCongruenceIffDiagOneUnitMatrixEqStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slTwoDiagConjCongruence_iff_diagOneUnit_matrix_eq : ∀ (N : ℕ) (d : ℤ) (u : (ZMod N)ˣ), (u : ZMod N) = d → ∀ γ γ' : SL(2, ℤ), Cong N d γ γ' ↔ dg u * redGL N γ' = redGL N γ * dg u := by
  first | exact @GlobalTheory.FNCong.cong_iff_dg | exact GlobalTheory.FNCong.cong_iff_dg | (intros; apply GlobalTheory.FNCong.cong_iff_dg <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReciprocityLargeLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisSlTwoActionModularFunctionRingOfCongr
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisSlTwoActionModularFunctionRingOfCongr
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem gal_sl_io_of_cong :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : GlobalTheory.FN.ring ε.range) (N w : ℕ), 0 < N → Lv ε.range N w a → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∀ γ γ' : SL(2, ℤ), Cong N d γ γ' → T.gal s (T.sl (ofSL γ) (T.io a)) = T.sl (ofSL γ') (T.gal s (T.io a)) := by
  intro Ω _ _ _ ε T a N w hN hLv s d hs γ γ' hC
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_complex_ringEquiv_extending_subfield_aut Ω ε s.toRingEquiv
  have hg' : ∀ x, g (ε x) = ε (s x) := hg
  obtain ⟨u, hu, hZ⟩ := (GlobalTheory.T.galois_exponent_rootOfUnity_expTwoPiI Ω ε s N hN).2 d hs
  have hE : ∀ x ∈ ε.range, g x ∈ ε.range := by
    rintro _ ⟨y, rfl⟩
    exact ⟨s y, (hg' y).symm⟩
  obtain ⟨f', hf'L, hf'C⟩ := GlobalTheory.T.levelN_function_galois_conj_qExpansion g ε.range N u w (a : ℍ → ℂ) hE (hZ g hg') hLv
  let a' : GlobalTheory.FN.ring ε.range := ⟨f', mem_ring_of_inR ⟨N, w, hN, hf'L⟩⟩
  obtain ⟨hext, hcmp, hexpinj, -⟩ := GlobalTheory.T.fractionField_ext_closure_injective Ω ε T
  obtain ⟨-, -, hSL, -⟩ := GlobalTheory.T.cmp_mul_ofSL_and_up_cmp_eq_up_mob

  have key : ∀ γ γ' : SL(2, ℤ), dg u * redGL N γ' = redGL N γ * dg u →
      T.gal s (T.sl (ofSL γ) (T.io a)) = T.sl (ofSL γ') (T.io a') := by
    intro γ γ' hM
    obtain ⟨b, hb, hbio⟩ := hcmp (ofSL γ) a
    obtain ⟨b', hb', hb'io⟩ := hcmp (ofSL γ') a'
    rw [hbio, hb'io]
    apply hexpinj
    ext r
    rw [T.gal_exp]
    have hb1 : (b : ℍ → ℂ) = fun τ => (a : ℍ → ℂ) (γ • τ) := by rw [hb, hSL]
    have hb2 : (b' : ℍ → ℂ) = fun τ => f' (γ' • τ) := by rw [hb', hSL]
    refine Eq.symm ?_
    refine GlobalTheory.T.cuspExpansion_coeff_conj_of_qExpansion_conj Ω ε s.toRingEquiv.toRingHom g N w b b' _ _ hg' hN ?_ ?_ (T.exp_io b) (T.exp_io b') r
    · rw [hb1]; exact hLv.2 γ
    · rw [hb1, hb2]; exact hf'C γ γ' hM
  have h1 : T.gal s (T.io a) = T.io a' := by
    have hM1 : dg u * redGL N 1 = redGL N 1 * dg u := by simp [redGL]
    have := key 1 1 hM1
    obtain ⟨c, hc, hcio⟩ := hcmp (ofSL 1) a
    obtain ⟨c', hc', hc'io⟩ := hcmp (ofSL 1) a'
    have e1 : c = a := Subtype.ext (by rw [hc, hSL]; funext τ; simp)
    have e2 : c' = a' := Subtype.ext (by rw [hc', hSL]; funext τ; simp [a'])
    rw [hcio, hc'io, e1, e2] at this
    exact this
  rw [h1]
  exact key γ γ' ((GlobalTheory.T.slTwoDiagConjCongruence_iff_diagOneUnit_matrix_eq N d u hu γ γ').mp hC)

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisSlTwoActionModularFunctionRingOfCongrStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_slTwo_action_modularFunctionRing_of_congr : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (a : GlobalTheory.FN.ring ε.range) (N w : ℕ), 0 < N → Lv ε.range N w a → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∀ γ γ' : SL(2, ℤ), Cong N d γ γ' → T.gal s (T.sl (ofSL γ) (T.io a)) = T.sl (ofSL γ') (T.gal s (T.io a)) := by
  first | exact @GlobalTheory.FN.gal_sl_io_of_cong | exact GlobalTheory.FN.gal_sl_io_of_cong | (intros; apply GlobalTheory.FN.gal_sl_io_of_cong <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReciprocityLargeLevel
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem reciprocity_large_level : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K), ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, 0 < N → N₀ ∣ N → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∀ γ γ' : SL(2, ℤ), Cong N d γ γ' → T.gal s (T.sl (ofSL γ) f) = T.sl (ofSL γ') (T.gal s f) := by
  intro Ω _ _ _ ε T f
  obtain ⟨a, b, hb, hab⟩ := T.io_surj f
  have hbK : T.io b ≠ 0 := by
    intro h
    exact hb (T.io_inj (by rw [h, map_zero]))
  have hf : f = T.io a / T.io b := by
    rw [eq_div_iff hbK, hab]
  obtain ⟨Na, wa, hNa, hLa⟩ := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 a).1 a.2
  obtain ⟨Nb, wb, hNb, hLb⟩ := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 b).1 b.2
  refine ⟨Na * Nb, Nat.mul_pos hNa hNb, ?_⟩
  intro N hN hdiv s d hs γ γ' hc
  have hLa' : Lv ε.range N wa a :=
    GlobalTheory.T.lv_mono_of_dvd_of_le ε.range Na N wa wa a hN (dvd_trans (dvd_mul_right Na Nb) hdiv) le_rfl hLa
  have hLb' : Lv ε.range N wb b :=
    GlobalTheory.T.lv_mono_of_dvd_of_le ε.range Nb N wb wb b hN (dvd_trans (dvd_mul_left Nb Na) hdiv) le_rfl hLb
  have ra := GlobalTheory.T.galois_slTwo_action_modularFunctionRing_of_congr Ω ε T a N wa hN hLa' s d hs γ γ' hc
  have rb := GlobalTheory.T.galois_slTwo_action_modularFunctionRing_of_congr Ω ε T b N wb hN hLb' s d hs γ γ' hc
  rw [hf, map_div₀, map_div₀, map_div₀, map_div₀, ra, rb]

end GlobalTheory.FN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ReciprocityLargeLevelStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_gal_sl_commute : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K), ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N : ℕ, 0 < N → N₀ ∣ N → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s (eOm ε (1 / N)) = eOm ε (1 / N) ^ d → ∀ γ γ' : SL(2, ℤ), Cong N d γ γ' → T.gal s (T.sl (ofSL γ) f) = T.sl (ofSL γ') (T.gal s f) := by
  first | exact @GlobalTheory.FN.reciprocity_large_level | exact GlobalTheory.FN.reciprocity_large_level | (intros; apply GlobalTheory.FN.reciprocity_large_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoDiagConjCongruenceLiftLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoDiagConjCongruenceLiftLevel
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNCongLift

theorem cong_of_dvd {M N : ℕ} (hMN : M ∣ N) {d : ℤ} {γ γ' : SL(2, ℤ)} (h : Cong N d γ γ') : Cong M d γ γ' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have key : ∀ x y : ZMod N, x = y → ZMod.castHom hMN (ZMod M) x = ZMod.castHom hMN (ZMod M) y :=
    fun x y hxy => by rw [hxy]
  have k1 := key _ _ h1
  have k2 := key _ _ h2
  have k3 := key _ _ h3
  have k4 := key _ _ h4
  simp only [map_mul, map_intCast] at k1 k2 k3 k4
  exact ⟨k1, k2, k3, k4⟩

theorem cong_congr_d {M : ℕ} {d d' : ℤ} (h : (d : ZMod M) = d') {γ γ' : SL(2, ℤ)} (hc : Cong M d γ γ') :
    Cong M d' γ γ' := by
  unfold Cong at hc ⊢
  rw [← h]
  exact hc

theorem en_eq_of_cong {M : ℕ} {d : ℤ} (hd : IsUnit (d : ZMod M)) {γ γ' γ'' : SL(2, ℤ)}
    (h' : Cong M d γ γ') (h'' : Cong M d γ γ'') :
    ∀ i j, (en γ' i j : ZMod M) = en γ'' i j := by
  obtain ⟨a1, a2, a3, a4⟩ := h'
  obtain ⟨b1, b2, b3, b4⟩ := h''
  intro i j
  fin_cases i <;> fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue]; rw [a1, b1]
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]; rw [a2, b2]
  · simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one]
    exact hd.mul_left_cancel (a3.trans b3.symm)
  · simp only [Fin.isValue, Fin.mk_one]; rw [a4, b4]

theorem mem_Gamma_iff_en {M : ℕ} (γ : SL(2, ℤ)) :
    γ ∈ CongruenceSubgroup.Gamma M ↔
      (en γ 0 0 : ZMod M) = 1 ∧ (en γ 0 1 : ZMod M) = 0 ∧ (en γ 1 0 : ZMod M) = 0 ∧ (en γ 1 1 : ZMod M) = 1 := by
  rw [CongruenceSubgroup.Gamma_mem]
  simp [en]

theorem mul_inv_mem_Gamma {M : ℕ} {γ' γ'' : SL(2, ℤ)} (h : ∀ i j, (en γ' i j : ZMod M) = en γ'' i j) :
    γ' * γ''⁻¹ ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem']
  have : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ' = Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ'' := by
    ext i j
    simpa [en] using h i j
  rw [map_mul, map_inv, this, mul_inv_cancel]

theorem cong_lift : ∀ (M N : ℕ) (d d' : ℤ), 0 < N → M ∣ N → (d : ZMod M) = d' → IsUnit (d' : ZMod N) → (∀ γ γ' : SL(2, ℤ), Cong M d γ γ' → ∃ γ'' : SL(2, ℤ), Cong N d' γ γ'' ∧ γ' * γ''⁻¹ ∈ CongruenceSubgroup.Gamma M) ∧ ∀ δ' ∈ CongruenceSubgroup.Gamma M, ∃ δ ∈ CongruenceSubgroup.Gamma M, Cong N d' δ δ' := by
  intro M N d d' hN hMN hdd' hu
  haveI : NeZero N := ⟨hN.ne'⟩
  have hdM : IsUnit (d : ZMod M) := by
    have := (hu.map (ZMod.castHom hMN (ZMod M)))
    rw [hdd']; simpa using this
  have hdM' : (d' : ZMod M) = d := hdd'.symm
  obtain ⟨u, hu'⟩ := hu
  obtain ⟨ex1, ex2⟩ := GlobalTheory.T.diagOneUnit_conj_lifts_sl2IntReductionMod N u
  refine ⟨fun γ γ' hγ => ?_, fun δ' hδ' => ?_⟩
  · obtain ⟨γ'', hγ''⟩ := ex1 γ
    have hc : Cong N d' γ γ'' := (GlobalTheory.T.slTwoDiagConjCongruence_iff_diagOneUnit_matrix_eq N d' u hu' γ γ'').2 hγ''
    refine ⟨γ'', hc, mul_inv_mem_Gamma (en_eq_of_cong hdM hγ ?_)⟩
    exact cong_congr_d hdM' (cong_of_dvd hMN hc)
  · obtain ⟨δ, hδ⟩ := ex2 δ'
    have hc : Cong N d' δ δ' := (GlobalTheory.T.slTwoDiagConjCongruence_iff_diagOneUnit_matrix_eq N d' u hu' δ δ').2 hδ
    refine ⟨δ, ?_, hc⟩
    have hcM := cong_congr_d hdM' (cong_of_dvd hMN hc)
    obtain ⟨c1, c2, c3, c4⟩ := hcM
    obtain ⟨g1, g2, g3, g4⟩ := (mem_Gamma_iff_en δ').1 hδ'
    rw [mem_Gamma_iff_en]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [← c1, g1]
    · have : (d : ZMod M) * en δ 0 1 = d * 0 := by rw [← c2, g2, mul_zero]
      exact hdM.mul_left_cancel this
    · rw [← c3, g3, mul_zero]
    · rw [← c4, g4]

end GlobalTheory.FNCongLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoDiagConjCongruenceLiftLevelStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slTwoDiagConjCongruence_lift_level : ∀ (M N : ℕ) (d d' : ℤ), 0 < N → M ∣ N → (d : ZMod M) = d' → IsUnit (d' : ZMod N) → (∀ γ γ' : SL(2, ℤ), Cong M d γ γ' → ∃ γ'' : SL(2, ℤ), Cong N d' γ γ'' ∧ γ' * γ''⁻¹ ∈ CongruenceSubgroup.Gamma M) ∧ ∀ δ' ∈ CongruenceSubgroup.Gamma M, ∃ δ ∈ CongruenceSubgroup.Gamma M, Cong N d' δ δ' := by
  first | exact @GlobalTheory.FNCongLift.cong_lift | exact GlobalTheory.FNCongLift.cong_lift | (intros; apply GlobalTheory.FNCongLift.cong_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShimuraReciprocityModularFunctionFractionField
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FNRecip

theorem main : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (M : ℕ) (f : T.K), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) f = f) → ∀ ζ : Ω, IsPrimitiveRoot ζ M → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s ζ = ζ ^ d → ∀ γ γ' : SL(2, ℤ), Cong M d γ γ' → T.gal s (T.sl (ofSL γ) f) = T.sl (ofSL γ') (T.gal s f) := by
  intro Ω _ _ _ ε T M f hM hf ζ hζ s d hsd γ γ' hc
  obtain ⟨N₀, hN₀, hrec⟩ := GlobalTheory.T.exists_level_gal_sl_commute Ω ε T f
  set N := N₀ * M with hNdef
  have hN : 0 < N := Nat.mul_pos hN₀ hM
  obtain ⟨⟨d', hd'⟩, hu⟩ := GlobalTheory.T.galois_exponent_rootOfUnity_expTwoPiI Ω ε s N hN
  obtain ⟨u, hu1, -⟩ := hu d' hd'
  have hunit : IsUnit ((d' : ℤ) : ZMod N) := hu1 ▸ u.isUnit
  set ω := eOm ε (1 / (N : ℚ)) with hω
  have hωp : IsPrimitiveRoot ω N := (GlobalTheory.T.expTwoPiIRatInField_roots_of_unity_properties Ω ε).2.2.2.2.1 N hN
  have hωM : IsPrimitiveRoot (ω ^ N₀) M := hωp.pow hN rfl
  haveI : NeZero M := ⟨hM.ne'⟩
  obtain ⟨i, -, hi⟩ := hωM.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hsζ : s ζ = ζ ^ d' := by
    rw [← hi, map_pow, map_pow, hd', ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast,
      ← zpow_mul, ← zpow_mul, ← zpow_mul, ← zpow_mul]
    ring_nf
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hM.ne'
  have hdd : (d : ZMod M) = d' := by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    have := (hζ.zpow_eq_one_iff_dvd (d' - d)).1 (by
      rw [zpow_sub₀ hζ0, ← hsd, ← hsζ, div_self]; exact (map_ne_zero s).2 hζ0)
    exact this
  obtain ⟨hl1, hl2⟩ := GlobalTheory.T.slTwoDiagConjCongruence_lift_level M N d d' hN (Dvd.intro_left N₀ rfl) hdd hunit
  obtain ⟨γ'', hc'', hκ⟩ := hl1 γ γ' hc
  have hact := GlobalTheory.T.modularFunctionFractionField_sl_rightAction Ω ε T
  have hinv : ∀ δ' ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL δ') (T.gal s f) = T.gal s f := by
    intro δ' hδ'
    obtain ⟨δ, hδ, hcδ⟩ := hl2 δ' hδ'
    have := hrec N hN (Dvd.intro M rfl) s d' hd' δ δ' hcδ
    rw [hf δ hδ] at this
    exact this.symm
  rw [hrec N hN (Dvd.intro M rfl) s d' hd' γ γ'' hc'']
  have hγ' : γ' = (γ' * γ''⁻¹) * γ'' := by group
  rw [hγ', map_mul, hact.2, hinv _ hκ]

end GlobalTheory.FNRecip
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShimuraReciprocityModularFunctionFractionFieldStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shimuraReciprocity_modularFunctionFractionField : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (M : ℕ) (f : T.K), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) f = f) → ∀ ζ : Ω, IsPrimitiveRoot ζ M → ∀ (s : Ω ≃ₐ[ℚ] Ω) (d : ℤ), s ζ = ζ ^ d → ∀ γ γ' : SL(2, ℤ), Cong M d γ γ' → T.gal s (T.sl (ofSL γ) f) = T.sl (ofSL γ') (T.gal s f) := by
  first | exact @GlobalTheory.FNRecip.main | exact GlobalTheory.FNRecip.main | (intros; apply GlobalTheory.FNRecip.main <;> assumption)
end
