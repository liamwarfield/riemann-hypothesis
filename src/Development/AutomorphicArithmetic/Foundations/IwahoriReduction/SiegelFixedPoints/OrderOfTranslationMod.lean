module

public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.OrderOfTranslationMod
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem exists_finite_residue_reps_mod_natCast (M K : ℕ) (hK : K ∣ M) (L γ : SL(2, ℤ))
    (h : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) L =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ) (i j : Fin 2) :
    ((L i j : ℤ) : ZMod K) = ((γ i j : ℤ) : ZMod K) := by
  have h1 : ((L i j : ℤ) : ZMod M) = ((γ i j : ℤ) : ZMod M) :=
    congrArg (fun g : SL(2, ZMod M) => g i j) h
  have h2 := congrArg (ZMod.castHom hK (ZMod K)) h1
  simpa only [map_intCast] using h2

private theorem exists_mem_mul_or_neg_mul_symm (M : ℕ) (a b : ℕ) : Tm M (a + b) = Tm M a * Tm M b := by
  simp only [Tm, pow_add, map_mul]

private theorem tm_apply_eq_cast_upper_unipotent (M k : ℕ) (i j : Fin 2) :
    (Tm M k) i j = (((!![1, (k : ℤ); 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod M) := by
  rw [← ModularGroup.coe_T_zpow, zpow_natCast]
  rfl

private theorem exists_mem_mul_or_neg_mul_trans (M : ℕ) (j : ℕ) : Tm M (M * j) = 1 := by
  ext i k
  rw [tm_apply_eq_cast_upper_unipotent]
  fin_cases i <;> fin_cases k <;> simp

private theorem tm_mod_eq (M : ℕ) (k : ℕ) : Tm M (k % M) = Tm M k := by
  conv_rhs => rw [← Nat.mod_add_div k M]
  rw [exists_mem_mul_or_neg_mul_symm, exists_mem_mul_or_neg_mul_trans, mul_one]

private theorem eq_of_tm_eq_of_lt (M : ℕ) (a b : ℕ) (ha : a < M) (hb : b < M) (h : Tm M a = Tm M b) : a = b := by
  have h1 := congrArg (fun g : SL(2, ZMod M) => g 0 1) h
  simp only [tm_apply_eq_cast_upper_unipotent] at h1
  simp at h1
  rw [ZMod.natCast_eq_natCast_iff'] at h1
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1

private theorem tm_mem_map_gam (N l M : ℕ) (k : ℕ) :
    Tm M k ∈ Subgroup.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))) (Gam N l) := by
  refine Subgroup.mem_map_of_mem _ (Subgroup.pow_mem _ ?_ k)
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.coe_T]
  · rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.coe_T]

private theorem liftSL_mem_gam_and_map_eq_of_mem_gs (N l M : ℕ) [NeZero M] (hM : N * l ∣ M) (γ : SL(2, ZMod M)) (hγ : γ ∈ Gs N l M) :
    liftSL M γ ∈ Gam N l ∧ Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (liftSL M γ) = γ := by
  have hγ' : γ ∈ Subgroup.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))) (Gam N l) := by
    simpa [Gs] using hγ
  obtain ⟨γ', hg', rfl⟩ := Subgroup.mem_map.1 hγ'
  have hL : Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (liftSL M
      (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ')) =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ' :=
    Classical.epsilon_spec (p := fun g => Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) g =
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) γ') ⟨γ', rfl⟩
  refine ⟨?_, hL⟩
  have eN := exists_finite_residue_reps_mod_natCast M N (dvd_trans (dvd_mul_right N l) hM) _ _ hL
  have el := exists_finite_residue_reps_mod_natCast M l (dvd_trans (dvd_mul_left l N) hM) _ _ hL
  obtain ⟨h1, h0⟩ := Subgroup.mem_inf.1 hg'
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem] at h1 ⊢
    rw [eN, eN, eN]
    exact h1
  · rw [CongruenceSubgroup.Gamma0_mem] at h0 ⊢
    rw [el]
    exact h0

theorem UpperTheory.Kd.L.reps :
    ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (M : ℕ) [NeZero M], N * l ∣ M → (∃ R, IsReps N l M R) ∧ ∀ γ ∈ Gs N l M, ∀ r₀, Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) (liftSL M γ) = γ ∧ gm r₀ * liftSL M γ ∈ CongruenceSubgroup.Gamma0 N ∧ ((en (gm r₀ * liftSL M γ) 0 0 : ℤ) : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N) ∧ ¬ (l : ℤ) ∣ en (gm r₀ * liftSL M γ) 0 0 ∧ ¬ (l : ℤ) ∣ en (gm r₀ * liftSL M γ) 1 0 := by
  intro l _ N _ c d gm hP M _ hM
  classical
  refine ⟨?_, ?_⟩
  · let orb : SL(2, ZMod M) → Set (SL(2, ZMod M)) := fun γ => Set.range (fun k : ℕ => γ * Tm M k)
    let rep : SL(2, ZMod M) → SL(2, ZMod M) := fun γ => Classical.epsilon (fun x => x ∈ orb γ)
    have h0 : Tm M 0 = 1 := by simpa using exists_mem_mul_or_neg_mul_trans M 0
    have self_mem : ∀ γ, γ ∈ orb γ := fun γ => ⟨0, show γ * Tm M 0 = γ by rw [h0, mul_one]⟩
    have rep_mem : ∀ γ, rep γ ∈ orb γ := fun γ => Classical.epsilon_spec ⟨γ, self_mem γ⟩
    have orb_eq : ∀ γ x, x ∈ orb γ → orb x = orb γ := by
      rintro γ _ ⟨j, rfl⟩
      ext y
      constructor
      · rintro ⟨k, rfl⟩
        exact ⟨j + k, show γ * Tm M (j + k) = γ * Tm M j * Tm M k by rw [mul_assoc, ← exists_mem_mul_or_neg_mul_symm]⟩
      · rintro ⟨k, rfl⟩
        refine ⟨k + (M - 1) * j, ?_⟩
        have hM1 : j + (k + (M - 1) * j) = k + M * j := by
          have : 1 ≤ M := NeZero.one_le
          obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          ring
        show γ * Tm M j * Tm M (k + (M - 1) * j) = γ * Tm M k
        rw [mul_assoc, ← exists_mem_mul_or_neg_mul_symm, hM1, exists_mem_mul_or_neg_mul_symm, exists_mem_mul_or_neg_mul_trans, mul_one]
    have rep_eq : ∀ γ x, x ∈ orb γ → rep x = rep γ := by
      intro γ x hx
      simp only [rep]
      rw [orb_eq γ x hx]
    have hGs : ∀ γ, γ ∈ Gs N l M ↔ γ ∈ Subgroup.map (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))) (Gam N l) := by
      intro γ
      simp [Gs]
    refine ⟨(Gs N l M).image rep, ?_, ?_⟩
    · intro x hx
      obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨j, hj⟩ := rep_mem γ
      rw [← hj, hGs]
      exact Subgroup.mul_mem _ ((hGs γ).1 hγ) (tm_mem_map_gam N l M j)
    · intro γ hγ
      have hin : γ ∈ orb (rep γ) := by
        rw [orb_eq γ (rep γ) (rep_mem γ)]
        exact self_mem γ
      obtain ⟨k, hk⟩ := hin
      have hk : rep γ * Tm M k = γ := hk
      refine ⟨(rep γ, k % M), ⟨Finset.mem_image_of_mem _ hγ, Nat.mod_lt _ (NeZero.pos M), ?_⟩, ?_⟩
      · show γ = rep γ * Tm M (k % M)
        rw [tm_mod_eq, hk]
      · rintro ⟨r, k'⟩ ⟨hr, hk', hγr⟩
        dsimp only at hr hk' hγr
        obtain ⟨γ1, -, rfl⟩ := Finset.mem_image.1 hr
        have hin1 : γ ∈ orb γ1 := by
          rw [← orb_eq γ1 (rep γ1) (rep_mem γ1)]
          exact ⟨k', hγr.symm⟩
        have hr1 : rep γ = rep γ1 := rep_eq γ1 γ hin1
        have hT : Tm M k' = Tm M (k % M) := by
          have e : rep γ1 * Tm M k' = rep γ1 * Tm M (k % M) := by
            rw [← hγr, tm_mod_eq, ← hr1, hk]
          exact mul_left_cancel e
        have := eq_of_tm_eq_of_lt M k' (k % M) hk' (Nat.mod_lt _ (NeZero.pos M)) hT
        simp only [Prod.mk.injEq]
        exact ⟨hr1.symm, this⟩
  · intro γ hγ r₀
    obtain ⟨hLG, hL⟩ := liftSL_mem_gam_and_map_eq_of_mem_gs N l M hM γ hγ
    obtain ⟨hL1, hL0⟩ := Subgroup.mem_inf.1 hLG
    rw [CongruenceSubgroup.Gamma1_mem] at hL1
    rw [CongruenceSubgroup.Gamma0_mem] at hL0
    have detL : (((liftSL M γ) 0 0 : ℤ) : ZMod l) * (((liftSL M γ) 1 1 : ℤ) : ZMod l) = 1 := by
      have h1 := (liftSL M γ).2
      rw [Matrix.det_fin_two] at h1
      have h2 := congrArg (Int.cast : ℤ → ZMod l) h1
      push_cast at h2
      rw [hL0, mul_zero, sub_zero] at h2
      exact h2
    have hL00 : (((liftSL M γ) 0 0 : ℤ) : ZMod l) ≠ 0 := left_ne_zero_of_mul_eq_one detL
    have hg00 : (((gm r₀) 0 0 : ℤ) : ZMod l) ≠ 0 := by
      intro h0
      have hc := hP.col r₀
      rw [h0, mul_zero] at hc
      have h1 := (gm r₀).2
      rw [Matrix.det_fin_two] at h1
      have h2 := congrArg (Int.cast : ℤ → ZMod l) h1
      push_cast at h2
      rw [h0, hc] at h2
      simp at h2
    refine ⟨hL, ?_, ?_, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (hP.g0 r₀) (by rw [CongruenceSubgroup.Gamma0_mem]; exact hL1.2.2)
    · have ga := hP.ga r₀
      simp only [en, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two] at ga ⊢
      push_cast
      rw [hL1.1, hL1.2.2, mul_one, mul_zero, add_zero]
      exact ga
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp only [en, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      push_cast
      rw [hL0, mul_zero, add_zero]
      exact mul_ne_zero hg00 hL00
    · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      simp only [en, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
      push_cast
      rw [hL0, mul_zero, add_zero, hP.col r₀]
      exact mul_ne_zero (mul_ne_zero (neg_ne_zero.2 r₀.ne_zero) hg00) hL00
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.Witalg
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem gal_mul' {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (s t : Ω ≃ₐ[ℚ] Ω) (f : X.K) :
    X.gal (s * t) f = X.gal s (X.gal t f) := by
  apply X.exp.toRingHom.injective
  show X.exp _ = X.exp _
  ext r
  simp [X.gal_exp]

private theorem kmap_comp' {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (φ ψ χ : X.K ≃+* X.K) (h : ∀ f, χ f = φ (ψ f)) (a : X.Khat l) : X.kmap l χ a = X.kmap l φ (X.kmap l ψ a) := by
  unfold Tower.kmap
  have e : (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map χ.toMonoidHom))) =
      (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map φ.toMonoidHom))) ∘ₗ
        (AddMonoidHom.toIntLinearMap (MonoidHom.toAdditive (Units.map ψ.toMonoidHom))) := by
    ext u
    exact h _
  show AdicCompletion.map (idl l) _ a = AdicCompletion.map (idl l) _ (AdicCompletion.map (idl l) _ a)
  rw [AdicCompletion.map_comp_apply, ← LinearMap.baseChange_comp, e]

theorem UpperTheory.Kd.L.witalg :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N n : ℕ), 1 ≤ N → (∀ (b b' : X.Fn l) (f f' : X.Kˣ), IsWit X N l n b f → IsWit X N l n b' f' → IsWit X N l n (b + b') (f * f')) ∧ IsWit X N l n 0 1 ∧ (∀ (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l) (f : X.Kˣ), IsWit X N l n b f → IsWit X N l n (X.galB l s b) (Units.map (X.gal s).toMonoidHom f)) ∧ ∀ s t : Ω ≃ₐ[ℚ] Ω, ∀ b : X.Fn l, X.galB l (s * t) b = X.galB l s (X.galB l t b) := by
  intro Ω _ _ _ _ ε X l _ N n _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl : 0 < l := (Fact.out : l.Prime).pos
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro b b' f f' ⟨h1, h2, h3⟩ ⟨k1, k2, k3⟩
    refine ⟨fun γ hγ => ?_, ?_, fun δ a c => ?_⟩
    · rw [Units.val_mul, map_mul, h1 γ hγ, k1 γ hγ]
    · rw [Pi.add_apply, map_add (f := _), h2, k2]
      unfold Tower.cls
      rw [← Submodule.Quotient.mk_add, ← TensorProduct.tmul_add, ofMul_mul]
    · obtain ⟨g, hg, e⟩ := h3 δ a c
      obtain ⟨g', hg', e'⟩ := k3 δ a c
      refine ⟨g * g', fun γ hγ => by rw [map_mul, hg γ hγ, hg' γ hγ], ?_⟩
      rw [Units.val_mul, map_mul, mul_pow, ← e, ← e']
      ring
  · refine ⟨fun γ _ => by simp, ?_, fun δ _ _ => ⟨1, fun γ _ => by simp, by simp⟩⟩
    simp [Tower.cls]
  · rintro s b f ⟨hfI, hcls, hδ⟩
    have hf : ((Units.map (X.gal s).toMonoidHom f : X.Kˣ) : X.K) = X.gal s f := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hf]; exact GlobalTheory.ThGal.inv_gal X s _ _ hfI
    · have hu : (![(![1, 0] : Fin 2 → ℤ_[l]) 0,
          (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (![1, 0] : Fin 2 → ℤ_[l]) 1] : Fin 2 → ℤ_[l]) = ![1, 0] := by
        funext i; fin_cases i <;> simp
      have hg : X.galB l s b ![1, 0] = X.kmap l (X.gal s) (b ![(![1, 0] : Fin 2 → ℤ_[l]) 0,
          (cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * (![1, 0] : Fin 2 → ℤ_[l]) 1]) := rfl
      rw [hu] at hg
      rw [AdicCompletion.eval_apply] at hcls
      rw [hg, AdicCompletion.eval_apply, Tower.kmap]
      erw [AdicCompletion.map_val_apply]
      rw [hcls]
      simp [Tower.cls, LinearMap.reduceModIdeal_apply]
    · intro δ hδ1 hδ2
      obtain ⟨δ', h1, h2, hrec⟩ := GlobalTheory.ThGal.exists_twist X s N l n hl f hfI δ hδ1 hδ2
      obtain ⟨g, hg, hfg⟩ := hδ δ' h1 h2
      refine ⟨X.gal s g, GlobalTheory.ThGal.inv_gal X s _ _ hg, ?_⟩
      rw [hf, ← hrec, ← map_mul, hfg, map_pow]
  · intro s t b
    funext u
    show X.kmap l (X.gal (s * t)) (b ![u 0, (cyclotomicCharacter Ω l (s * t).toRingEquiv : ℤ_[l]) * u 1]) =
      X.kmap l (X.gal s) (X.kmap l (X.gal t) (b ![u 0, (cyclotomicCharacter Ω l t.toRingEquiv : ℤ_[l]) *
        ((cyclotomicCharacter Ω l s.toRingEquiv : ℤ_[l]) * u 1)]))
    have hm : (s * t).toRingEquiv = s.toRingEquiv * t.toRingEquiv := rfl
    rw [kmap_comp' X l _ _ _ (gal_mul' X s t), hm, map_mul, Units.val_mul, mul_left_comm, mul_assoc]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsAdmissibleSmoothingFactorAddIntVector
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

namespace UpperTheory.Kd.L.AdmissibleUnits

open GlobalTheory.Sieg

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

private theorem ent_ext {g h : GQ} (e : ∀ i j, ent g i j = ent h i j) : g = h :=
  Subtype.ext (Matrix.GeneralLinearGroup.ext e)

private theorem ent_mul (g h : GQ) (i j : Fin 2) : ent (g * h) i j = ent g i 0 * ent h 0 j + ent g i 1 * ent h 1 j := by
  simp [ent, Matrix.mul_apply, Fin.sum_univ_two]

private theorem ent_dg {N : ℕ} (hN : 0 < N) (i j : Fin 2) :
    ent (toGQ !![(N : ℤ), 0; 0, 1]) i j = (!![(N : ℚ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℚ) i j := by
  fin_cases i <;> fin_cases j <;> simp [ent, toGQ, hN, Matrix.GeneralLinearGroup.mkOfDetNeZero]

private theorem ent_sl (γ : SL(2, ℤ)) (i j : Fin 2) : ent (ofSL γ) i j = (en γ i j : ℚ) := rfl

private theorem dg_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    toGQ !![(a : ℤ), 0; 0, 1] * toGQ !![(b : ℤ), 0; 0, 1] = toGQ !![((a * b : ℕ) : ℤ), 0; 0, 1] := by
  refine ent_ext fun i j => ?_
  rw [ent_mul, ent_dg (Nat.mul_pos ha hb)]
  simp only [ent_dg ha, ent_dg hb]
  fin_cases i <;> fin_cases j <;> simp

private theorem exists_conj {N : ℕ} (hN : 0 < N) (γ : SL(2, ℤ)) (k : ℤ) (hk : en γ 1 0 = N * k) :
    ∃ δ : SL(2, ℤ), en δ 0 0 = en γ 0 0 ∧ en δ 0 1 = N * en γ 0 1 ∧ en δ 1 0 = k ∧ en δ 1 1 = en γ 1 1 ∧
      toGQ !![(N : ℤ), 0; 0, 1] * ofSL γ = ofSL δ * toGQ !![(N : ℤ), 0; 0, 1] := by
  have hd : en γ 0 0 * en γ 1 1 - en γ 0 1 * en γ 1 0 = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  let δ : SL(2, ℤ) := ⟨!![en γ 0 0, N * en γ 0 1; k, en γ 1 1], by
    rw [Matrix.det_fin_two_of, ← hd, hk]; ring⟩
  have h00 : en δ 0 0 = en γ 0 0 := rfl
  have h01 : en δ 0 1 = N * en γ 0 1 := rfl
  have h10 : en δ 1 0 = k := rfl
  have h11 : en δ 1 1 = en γ 1 1 := rfl
  refine ⟨δ, h00, h01, h10, h11, ent_ext fun i j => ?_⟩
  rw [ent_mul, ent_mul]
  simp only [ent_dg hN, ent_sl]
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11, hk, mul_comm]

private theorem admissible_of_integral_conj_le {c D : ℕ} (hc : 1 < c) (h6 : Nat.Coprime c 6) (hcD : Nat.Coprime c D) (hD : 0 < D) {a b : ℤ}
    (hab : ¬ ((D : ℤ) ∣ a ∧ (D : ℤ) ∣ b)) : GlobalTheory.Sieg.admitted c ![(a : ℚ) / D, (b : ℚ) / D] := by
  have hq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hz : IsCoprime (D : ℤ) (c : ℤ) := Nat.isCoprime_iff_coprime.2 hcD.symm
  have key : ∀ z : ℤ, (c : ℚ) * ((z : ℚ) / D) ∈ Set.range ((↑) : ℤ → ℚ) → (D : ℤ) ∣ z := by
    rintro z ⟨k, hk⟩
    have e : (c : ℚ) * z = D * k := by rw [hk]; field_simp
    exact hz.dvd_of_dvd_mul_left ⟨k, by exact_mod_cast e⟩
  exact ⟨hc, h6, fun h => hab ⟨key a h.1, key b h.2⟩⟩

private theorem siegel_per {ε : Ω →+* ℂ} (X : Tower Ω ε) {c : ℕ} {x y : Fin 2 → ℚ} (hx : GlobalTheory.Sieg.admitted c x) (p q : ℤ)
    (h0 : y 0 = x 0 + p) (h1 : y 1 = x 1 + q) : siegel X c y = siegel X c x := by
  have hy : y = fun i => x i + ((![p, q] : Fin 2 → ℤ) i : ℚ) := by
    funext i
    fin_cases i
    · simpa using h0
    · simpa using h1
  have e : sgC c y = sgC c x := by
    funext z
    rw [hy]
    exact GlobalTheory.T.smoothedSiegelUnit_index_add_intVector c x _ _ hx
  unfold siegel
  rw [e]

private theorem isAdmissibleSmoothingFactor_add_intVector {c : ℕ} {x y : Fin 2 → ℚ} (hx : GlobalTheory.Sieg.admitted c x) (p q : ℤ)
    (h0 : y 0 = x 0 + p) (h1 : y 1 = x 1 + q) : GlobalTheory.Sieg.admitted c y := by
  refine ⟨hx.1, hx.2.1, fun ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ => hx.2.2 ⟨⟨u - c * p, ?_⟩, ⟨v - c * q, ?_⟩⟩⟩
  · push_cast; rw [hu, h0]; ring
  · push_cast; rw [hv, h1]; ring

private theorem admissible_act_SL2 {c : ℕ} {x : Fin 2 → ℚ} (hx : GlobalTheory.Sieg.admitted c x) (γ : SL(2, ℤ)) : GlobalTheory.Sieg.admitted c (act x γ) := by
  have hd : en γ 0 0 * en γ 1 1 - en γ 0 1 * en γ 1 0 = 1 := by
    have h := γ.det_coe
    rwa [Matrix.det_fin_two] at h
  have hq : (en γ 0 0 : ℚ) * en γ 1 1 - en γ 0 1 * en γ 1 0 = 1 := by exact_mod_cast hd
  refine ⟨hx.1, hx.2.1, fun ⟨⟨u, hu⟩, ⟨v, hv⟩⟩ =>
    hx.2.2 ⟨⟨u * en γ 1 1 - v * en γ 1 0, ?_⟩, ⟨v * en γ 0 0 - u * en γ 0 1, ?_⟩⟩⟩
  all_goals
    simp only [act, Fin.sum_univ_two] at hu hv
    simp only [en] at hq ⊢
    push_cast
    rw [hu, hv]
  · linear_combination (c * x 0) * hq
  · linear_combination (c * x 1) * hq

private theorem sl_dg_siegel [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {c N : ℕ} (hN : 0 < N) {x y : Fin 2 → ℚ}
    (hx : GlobalTheory.Sieg.admitted c x) (γ : SL(2, ℤ)) (k : ℤ) (hk : en γ 1 0 = N * k) (p q : ℤ)
    (h0 : y 0 = x 0 * en γ 0 0 + x 1 * k + p) (h1 : y 1 = x 0 * (N * en γ 0 1) + x 1 * en γ 1 1 + q) :
    X.sl (ofSL γ) (X.sl (toGQ !![(N : ℤ), 0; 0, 1]) (siegel X c x)) = X.sl (toGQ !![(N : ℤ), 0; 0, 1]) (siegel X c y) := by
  obtain ⟨δ, h00, h01, h10, h11, e⟩ := exists_conj hN γ k hk
  rw [← X.sl_mul, e, X.sl_mul, GlobalTheory.T.siegelUnitInTower_sl_action_rowVector Ω ε X c x δ hx]
  congr 1
  simp only [en] at h00 h01 h10 h11 h0 h1
  refine (siegel_per X (admissible_act_SL2 hx δ) p q ?_ ?_).symm
  · simp only [act, Fin.sum_univ_two]; rw [h0, h00, h10]
  · simp only [act, Fin.sum_univ_two]; rw [h1, h01, h11]; push_cast; ring

private theorem gal_siegel_fix [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {c D : ℕ} (hD : 0 < D) {a b : ℤ}
    (hx : GlobalTheory.Sieg.admitted c ![(a : ℚ) / D, (b : ℚ) / D]) (s : Ω ≃ₐ[ℚ] Ω) (hs : ∀ z : Ω, z ^ D = 1 → s z = z) :
    X.gal s (siegel X c ![(a : ℚ) / D, (b : ℚ) / D]) = siegel X c ![(a : ℚ) / D, (b : ℚ) / D] := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hz : (D : ℤ) ≠ 0 := by exact_mod_cast hD.ne'
  obtain ⟨a', ha'⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg a hz)
  obtain ⟨b', hb'⟩ := Int.eq_ofNat_of_zero_le (Int.emod_nonneg b hz)
  have hlt : a' < D := by
    have := Int.emod_lt_of_pos a (by exact_mod_cast hD : (0 : ℤ) < D)
    omega
  have ea : (a : ℚ) = a' + D * ((a / D : ℤ) : ℚ) := by
    have := Int.emod_add_mul_ediv a D
    rw [ha'] at this
    exact_mod_cast this.symm
  have eb : (b : ℚ) = b' + D * ((b / D : ℤ) : ℚ) := by
    have := Int.emod_add_mul_ediv b D
    rw [hb'] at this
    exact_mod_cast this.symm
  have f0 : (![(a' : ℚ) / D, (b' : ℚ) / D] : Fin 2 → ℚ) 0 = (![(a : ℚ) / D, (b : ℚ) / D] : Fin 2 → ℚ) 0 + ((-(a / D) : ℤ) : ℚ) := by
    show (a' : ℚ) / D = (a : ℚ) / D + ((-(a / D) : ℤ) : ℚ)
    rw [Int.cast_neg]; field_simp; linear_combination -ea
  have f1 : (![(a' : ℚ) / D, (b' : ℚ) / D] : Fin 2 → ℚ) 1 = (![(a : ℚ) / D, (b : ℚ) / D] : Fin 2 → ℚ) 1 + ((-(b / D) : ℤ) : ℚ) := by
    show (b' : ℚ) / D = (b : ℚ) / D + ((-(b / D) : ℤ) : ℚ)
    rw [Int.cast_neg]; field_simp; linear_combination -eb
  have hy := isAdmissibleSmoothingFactor_add_intVector hx _ _ f0 f1
  rw [← siegel_per X hx _ _ f0 f1]
  have := GlobalTheory.T.galois_action_siegelUnitInTower Ω ε X c D a' b' 1 s hD hlt
    (by rw [Nat.cast_one]; exact hs _ (isPrimitiveRoot_eOm ε hD.ne').pow_eq_one) hy (by rwa [one_mul])
  rwa [one_mul] at this

private theorem gal_dg {ε : Ω →+* ℂ} (X : Tower Ω ε) {N : ℕ} (hN : 0 < N) (s : Ω ≃ₐ[ℚ] Ω) {f : X.K} (hf : X.gal s f = f) :
    X.gal s (X.sl (toGQ !![(N : ℤ), 0; 0, 1]) f) = X.sl (toGQ !![(N : ℤ), 0; 0, 1]) f := by
  apply X.exp.toRingHom.injective
  ext r
  show (X.exp _).coeff r = (X.exp _).coeff r
  rw [X.gal_exp, GlobalTheory.DlRescale.exp_sl_diag ε X N hN, GlobalTheory.DlRescale.resc_coeff, ← X.gal_exp, hf]

private theorem sgN_mem [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {c N D M : ℕ} (hN : 0 < N) (hD : 0 < D)
    (hM : N * D ∣ M) {a b : ℤ} (hx : GlobalTheory.Sieg.admitted c ![(a : ℚ) / D, (b : ℚ) / D]) :
    sgN X c N D (a, b) ∈ topF X M ∧ sgN X c N D (a, b) ≠ 0 := by
  refine ⟨(mem_mdl_iff X _ _ _).2 ⟨?_, fun s hs => ?_⟩, ?_⟩
  · rw [mem_lev_iff]
    intro γ hγ
    obtain ⟨h00, h01, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.1 hγ
    have hMz : ((N * D : ℕ) : ℤ) ∣ (M : ℤ) := Int.natCast_dvd_natCast.2 hM
    obtain ⟨u, hu⟩ : ((N * D : ℕ) : ℤ) ∣ en γ 0 0 - 1 :=
      hMz.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (by push_cast; exact sub_eq_zero.2 h00))
    obtain ⟨v, hv⟩ : ((N * D : ℕ) : ℤ) ∣ en γ 0 1 := hMz.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 h01)
    obtain ⟨w, hw⟩ : ((N * D : ℕ) : ℤ) ∣ en γ 1 0 := hMz.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 h10)
    obtain ⟨t, ht⟩ : ((N * D : ℕ) : ℤ) ∣ en γ 1 1 - 1 :=
      hMz.trans ((ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 (by push_cast; exact sub_eq_zero.2 h11))
    have hq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
    refine sl_dg_siegel X hN hx γ (D * w) (by rw [hw]; push_cast; ring) (-(a * N * u + b * w)) (-(a * N * N * v + b * N * t)) ?_ ?_
    · show (a : ℚ) / D = (a : ℚ) / D * _ + (b : ℚ) / D * _ + _
      rw [sub_eq_iff_eq_add.1 hu]; push_cast; field_simp; ring
    · show (b : ℚ) / D = (a : ℚ) / D * _ + (b : ℚ) / D * _ + _
      rw [sub_eq_iff_eq_add.1 ht, hv]; push_cast; field_simp; ring
  · refine gal_dg X hN s (gal_siegel_fix X hD hx s fun z hz => (mem_fixMu_iff s).1 hs z ?_)
    obtain ⟨e, rfl⟩ := (Dvd.intro_left N rfl : D ∣ N * D).trans hM
    rw [pow_mul, hz, one_pow]
  · exact (map_ne_zero _).2 (GlobalTheory.T.siegelUnitInTower_ne_zero Ω ε X c _ hx)

end UpperTheory.Kd.L.AdmissibleUnits

open UpperTheory.Kd.L.AdmissibleUnits in
theorem UpperTheory.Kd.L.units :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (x : ZMod N) (m n : ℕ), 1 ≤ m → ((sgN X c N (N * l ^ (m + n)) ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), 0)) ∈ topF X (topMu l n m N) ∧ (sgN X c N (N * l ^ (m + n)) ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), 0)) ≠ 0 ∧ (sgN X d N (N * l ^ (m + n)) ((topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), (N : ℤ))) ∈ topF X (topMu l n m N) ∧ (sgN X d N (N * l ^ (m + n)) ((topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), (N : ℤ))) ≠ 0) ∧ ∀ g ∈ CongruenceSubgroup.Gamma0 N, X.sl (toGQ !![((N * N : ℕ) : ℤ), 0; 0, 1]) (X.sl (ofSL g) (sgN X c N (N * l ^ (m + n)) ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), 0))) = sgN X c (N ^ 3) (N ^ 3 * l ^ (m + n)) ((N : ℤ) ^ 2 * (en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n))), (N : ℤ) ^ 2 * ((N : ℤ) ^ 2 * en g 0 1)) ∧ X.sl (toGQ !![((N * N : ℕ) : ℤ), 0; 0, 1]) (X.sl (ofSL g) (sgN X d N (N * l ^ (m + n)) ((topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n), (N : ℤ)))) = sgN X d (N ^ 3) (N ^ 3 * l ^ (m + n)) ((N : ℤ) ^ 2 * (en g 0 0 * (topT l (m + n) N : ℤ) * (l : ℤ) ^ (m + n) + en g 1 0), (N : ℤ) ^ 2 * ((N : ℤ) * en g 1 1)) := by
  intro Ω _ _ _ _ ε X l _ N _ c d gm P x m n hm
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have hL : 0 < l ^ (m + n) := pow_pos hl _
  have hD : 0 < N * l ^ (m + n) := Nat.mul_pos hN hL
  have hlL : l ∣ l ^ (m + n) := dvd_pow_self l (by omega)
  have cop : ∀ e : ℕ, Nat.Coprime e (6 * l * N) → Nat.Coprime e 6 ∧ Nat.Coprime e (N * l ^ (m + n)) := fun e he =>
    ⟨he.coprime_mul_right_right.coprime_mul_right_right,
      Nat.Coprime.mul_right he.coprime_mul_left_right
        (Nat.Coprime.pow_right _ he.coprime_mul_right_right.coprime_mul_left_right)⟩
  have hlD : (l : ℤ) ∣ ((N * l ^ (m + n) : ℕ) : ℤ) := Int.natCast_dvd_natCast.2 (hlL.mul_left N)
  have hlN : ¬ (l : ℤ) ∣ (N : ℤ) := fun h => P.cop (Int.natCast_dvd_natCast.1 h)
  have hM : N * (N * l ^ (m + n)) ∣ topMu l n m N := ⟨1, by unfold topMu; ring⟩
  generalize (topT l (m + n) N : ℤ) = t
  have hu := admissible_of_integral_conj_le P.c1 (cop c P.cc).1 (cop c P.cc).2 hD
    (a := (N : ℤ) + (x.val : ℤ) * t * (l : ℤ) ^ (m + n)) (b := 0) (fun h => hlN
      ((dvd_add_left ((dvd_pow_self (l : ℤ) (by omega)).mul_left _)).1 (hlD.trans h.1)))
  have hv := admissible_of_integral_conj_le P.d1 (cop d P.dc).1 (cop d P.dc).2 hD
    (a := t * (l : ℤ) ^ (m + n)) (b := (N : ℤ)) (fun h => by
      have h2 := Nat.le_of_dvd hN (Int.natCast_dvd_natCast.1 h.2)
      have h3 : 1 < l ^ (m + n) := Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt
      nlinarith)
  refine ⟨⟨(sgN_mem X hN hD hM hu).1, (sgN_mem X hN hD hM hu).2, (sgN_mem X hN hD hM hv).1, (sgN_mem X hN hD hM hv).2⟩,
    fun g hg => ?_⟩
  obtain ⟨k, hk⟩ : (N : ℤ) ∣ en g 1 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).1 (CongruenceSubgroup.Gamma0_mem.1 hg)
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'
  have hlq : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne'
  have e3 : N * (N * N) = N ^ 3 := by ring
  unfold sgN
  constructor
  · rw [← e3, ← dg_mul hN (Nat.mul_pos hN hN), X.sl_mul]
    congr 1
    refine sl_dg_siegel X hN hu g k hk 0 (-(x.val * t * en g 0 1)) ?_ ?_
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast; field_simp; ring
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast; field_simp; ring
  · rw [← e3, ← dg_mul hN (Nat.mul_pos hN hN), X.sl_mul]
    congr 1
    refine sl_dg_siegel X hN hv g k hk 0 (-(t * en g 0 1)) ?_ ?_
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [hk]; push_cast; field_simp; ring
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      push_cast; field_simp; ring
end
