module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntModLevelPrimePowEqAddMul
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.SpecialLinearMulApplyZeroZero
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.OrderOfTranslationMod
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgClosureOfTower
public import Development.AbelianVarietyTheory.Definitions.Foundations.ActWBOfInvariant
public import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.PieceTDetFiberEqPieceTRootPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.PieceTLevelRaiseEqVp

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.TwistedEisensteinPieceTrivialCharacterEq
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.twistedEisensteinPiece_trivialCharacter_eq :
    ∀ {K : Type} [Field K] [CharZero K] (l : ℕ) [Fact l.Prime] (N L m w : ℕ) (c d : ℤ) (v v' : ℤ × ℤ) (ζ : K) (z₀ : ZMod (l ^ m)), 1 ≤ m → m ≤ L → ∀ r : ℕ, pieceT N l L m (w + 2) (1 : DirichletCharacter K (l ^ m)) c d v v' ζ ((unitSet l L).filter fun γ : GL (Fin 2) (ZMod (l ^ L)) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det.val : ℕ) : ZMod (l ^ m)) = z₀) r = -((l : K) ^ ((L : ℤ) * ((w : ℤ) - 2))) * ∑ γ ∈ ((unitSet l L).filter fun γ : GL (Fin 2) (ZMod (l ^ L)) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det.val : ℕ) : ZMod (l ^ m)) = z₀), cmul (smF c (w + 1) (N * l ^ L) ζ (rowT N l L γ 0 v).1 (rowT N l L γ 0 v).2) (smF d 1 (N * l ^ L) ζ (rowT N l L γ 1 v').1 (rowT N l L γ 1 v').2) r := by
  intro K _ _ l _ N L m w c d v v' ζ z₀ _ hmL r
  unfold pieceT
  have hd : l ^ m ∣ l ^ L := pow_dvd_pow l hmL
  have hexp : ((L : ℤ) * (((w + 2 : ℕ) : ℤ) - 4)) = (L : ℤ) * ((w : ℤ) - 2) := by
    push_cast
    ring
  have hk : w + 2 - 1 = w + 1 := by omega
  rw [hexp, hk]
  congr 1
  apply Finset.sum_congr rfl
  intro γ _
  have hu : IsUnit ((((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det.val : ℕ) : ZMod (l ^ m))) := by
    rw [ZMod.natCast_val]
    have hdet : IsUnit (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp γ.isUnit
    exact hdet.map (ZMod.castHom hd (ZMod (l ^ m)))
  rw [MulChar.one_apply hu, one_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.IsPrimitiveRootEOmAndPowCompatible
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.isPrimitiveRoot_eOm_and_pow_compatible :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N], (∀ L : ℕ, IsPrimitiveRoot (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) (N * l ^ L)) ∧ (∀ L : ℕ, eOm ε (1 / ((N * l ^ L : ℕ) : ℚ)) ^ N = zt ε l L) ∧ (∀ m n : ℕ, eOm ε (1 / ((N * l ^ (m + n) : ℕ) : ℚ)) ^ (l ^ n) = eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m))) := by
  intro Ω _ _ _ ε l hl N _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hN0 : N ≠ 0 := NeZero.ne N
  have hl1 : (l : ℚ) ≠ 0 := by exact_mod_cast hl0
  have hN1 : (N : ℚ) ≠ 0 := by exact_mod_cast hN0
  refine ⟨fun L => GlobalTheory.K4.isPrimitiveRoot_eOm ε (mul_ne_zero hN0 (pow_ne_zero L hl0)), fun L => ?_, fun m n => ?_⟩
  · rw [← GlobalTheory.UlCusp.eOm_nsmul]
    have h : (N : ℚ) * (1 / ((N * l ^ L : ℕ) : ℚ)) = 1 / (l : ℚ) ^ L := by
      push_cast; field_simp
    rw [h]; rfl
  · rw [← GlobalTheory.UlCusp.eOm_nsmul]
    have h : ((l ^ n : ℕ) : ℚ) * (1 / ((N * l ^ (m + n) : ℕ) : ℚ)) = 1 / ((N : ℚ) * (l : ℚ) ^ m) := by
      push_cast; rw [pow_add]; field_simp
    rw [h]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.InZlClosedAddMulAndCyclotomicGaloisStable
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.inZl_closed_add_mul_and_cyclotomic_galois_stable :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (l n : ℕ) [Fact l.Prime], (∀ k : ℕ, InZl ε l n (k : Ω)) ∧ (∀ F G : Ω, InZl ε l n F → InZl ε l n G → InZl ε l n (F + G)) ∧ (∀ F G : Ω, InZl ε l n F → InZl ε l n G → InZl ε l n (F * G)) ∧ ∀ (s : Ω ≃ₐ[ℚ] Ω) (k : ℕ), s (zt ε l n) = zt ε l n ^ k → ∀ F : Ω, InZl ε l n F → InZl ε l n (s F) := by
  intro Ω _ _ ε l n hl
  have hp : l.Prime := hl.out
  have hmul : ∀ D E : ℕ, ¬ l ∣ D → ¬ l ∣ E → ¬ l ∣ D * E := fun D E hD hE h =>
    ((Nat.Prime.dvd_mul hp).1 h).elim hD hE
  refine ⟨fun k => ⟨1, hp.not_dvd_one, ?_⟩, ?_, ?_, ?_⟩
  · rw [Nat.cast_one, one_mul]
    exact natCast_mem _ k
  · rintro F G ⟨D, hD, hF⟩ ⟨E, hE, hG⟩
    refine ⟨D * E, hmul D E hD hE, ?_⟩
    have h : ((D * E : ℕ) : Ω) * (F + G) = (E : Ω) * ((D : Ω) * F) + (D : Ω) * ((E : Ω) * G) := by
      push_cast; ring
    rw [h]
    exact add_mem (mul_mem (natCast_mem _ E) hF) (mul_mem (natCast_mem _ D) hG)
  · rintro F G ⟨D, hD, hF⟩ ⟨E, hE, hG⟩
    refine ⟨D * E, hmul D E hD hE, ?_⟩
    have h : ((D * E : ℕ) : Ω) * (F * G) = ((D : Ω) * F) * ((E : Ω) * G) := by
      push_cast; ring
    rw [h]
    exact mul_mem hF hG
  · rintro s k hs F ⟨D, hD, hF⟩
    refine ⟨D, hD, ?_⟩
    have key : ∀ y ∈ Subring.closure ({zt ε l n} : Set Ω), s y ∈ Subring.closure ({zt ε l n} : Set Ω) := by
      intro y hy
      have hle : Subring.closure ({zt ε l n} : Set Ω) ≤
          (Subring.closure ({zt ε l n} : Set Ω)).comap (s : Ω →+* Ω) := by
        rw [Subring.closure_le, Set.singleton_subset_iff]
        show s (zt ε l n) ∈ Subring.closure ({zt ε l n} : Set Ω)
        rw [hs]
        exact pow_mem (Subring.subset_closure (Set.mem_singleton _)) k
      exact hle hy
    have h := key _ hF
    rwa [map_mul, map_natCast] at h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.RepMApplyZtEqPowRedTop
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.repM_apply_zt_eq_pow_redTop :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime] (n m N : ℕ) [NeZero N] (y : (ZMod (topM l n m (N * N)))ˣ), (repM (topM l n m (N * N)) y : Ω ≃ₐ[ℚ] Ω) (zt ε l (m + n)) = zt ε l (m + n) ^ ((redTop l n m N y : (ZMod (l ^ (m + n)))ˣ) : ZMod (l ^ (m + n))).val := by
  intro Ω _ _ _ ε l hl n m N _ y
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hl0 : l ^ (m + n) ≠ 0 := pow_ne_zero _ hl.out.ne_zero
  haveI : NeZero (l ^ (m + n)) := ⟨hl0⟩
  have h1 : zt ε l (m + n) ^ (l ^ (m + n)) = 1 := by
    have h := (isPrimitiveRoot_eOm ε hl0).pow_eq_one
    rw [Nat.cast_pow] at h
    exact h
  have hd : l ^ (m + n) ∣ topM l n m (N * N) := Dvd.intro _ rfl
  have h2 : zt ε l (m + n) ^ topM l n m (N * N) = 1 := by
    obtain ⟨k, hk⟩ := hd
    rw [hk, pow_mul, h1, one_pow]
  rw [repM_apply _ y h2]
  have e : ((redTop l n m N y : (ZMod (l ^ (m + n)))ˣ) : ZMod (l ^ (m + n))) =
      (((y : ZMod (topM l n m (N * N))).val : ℕ) : ZMod (l ^ (m + n))) := by
    show ZMod.castHom hd (ZMod (l ^ (m + n))) (y : ZMod (topM l n m (N * N))) = _
    rw [ZMod.castHom_apply, ZMod.natCast_val]
  rw [e, ZMod.val_natCast, ← pow_eq_pow_mod _ h1]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.CongruenceActionInvariant
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

theorem UpperTheory.congruence_action_invariant :
    ∀ (l : ℕ) [Fact l.Prime] (L m : ℕ), 1 ≤ m → m ≤ L → ∀ (z : (ZMod (l ^ L))ˣ) (t : SL(2, ZMod (l ^ L)) → (ZMod (l ^ L))ˣ → GL (Fin 2) (ZMod (l ^ L))), (∀ h u i, ((t h u : GL (Fin 2) (ZMod (l ^ L))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 0 = h i 0) → (∀ h u i, ((t h u : GL (Fin 2) (ZMod (l ^ L))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 1 = (u : ZMod (l ^ L)) * h i 1) → ∀ (V : Type) [AddCommMonoid V] (f : GL (Fin 2) (ZMod (l ^ L)) → V), ∑ h ∈ Finset.univ.filter (fun h : SL(2, ZMod (l ^ L)) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val), ∑ a ∈ Finset.univ.filter (fun a : (ZMod (l ^ L))ˣ => (a : ZMod (l ^ L)).val ≡ 1 [MOD l ^ m]), f (t h (a * z)) = ∑ γ ∈ ((unitSet l L).filter fun γ : GL (Fin 2) (ZMod (l ^ L)) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det.val : ℕ) : ZMod (l ^ m)) = (((z : ZMod (l ^ L)).val : ℕ) : ZMod (l ^ m))), f γ := by
  intro l _ L m _ hmL z t ht0 ht1 V _ f
  have hd : l ^ m ∣ l ^ L := pow_dvd_pow l hmL
  set φ := ZMod.castHom hd (ZMod (l ^ m)) with hφ
  have hcast : ∀ x : ZMod (l ^ L), ((x.val : ℕ) : ZMod (l ^ m)) = φ x := by
    intro x
    rw [ZMod.natCast_val, hφ, ZMod.castHom_apply]
  have hmod : ∀ a : (ZMod (l ^ L))ˣ, (a : ZMod (l ^ L)).val ≡ 1 [MOD l ^ m] ↔ φ a = 1 := by
    intro a
    rw [← ZMod.natCast_eq_natCast_iff, hcast, Nat.cast_one]
  have hdet : ∀ h u, ((t h u : GL (Fin 2) (ZMod (l ^ L))) : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det
      = (u : ZMod (l ^ L)) := by
    intro h u
    have h1 : (h : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))).det = 1 := h.prop
    rw [Matrix.det_fin_two] at h1 ⊢
    rw [ht0, ht0, ht1, ht1]
    linear_combination (u : ZMod (l ^ L)) * h1
  rw [← Finset.sum_product']
  apply Finset.sum_bij (fun p _ => t p.1 (p.2 * z))
  · intro p hp
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [unitSet, Finset.mem_filter, Finset.mem_univ, true_and, ht0, hcast, hdet]
    refine ⟨hp.1, ?_⟩
    rw [Units.val_mul, map_mul, (hmod _).mp hp.2, one_mul]
  · intro p _ q _ hpq
    have hu : p.2 * z = q.2 * z := by
      apply Units.ext
      rw [← hdet p.1, ← hdet q.1, hpq]
    have ha : p.2 = q.2 := mul_right_cancel hu
    have hh : p.1 = q.1 := by
      ext i j
      fin_cases j
      · have := congrArg (fun g : GL (Fin 2) (ZMod (l ^ L)) => (g : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 0) hpq
        simpa [ht0] using this
      · have := congrArg (fun g : GL (Fin 2) (ZMod (l ^ L)) => (g : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 1) hpq
        simp only [ht1] at this
        rw [hu] at this
        exact (Units.mul_right_inj _).mp this
    exact Prod.ext hh ha
  · intro γ hγ
    simp only [unitSet, Finset.mem_filter, Finset.mem_univ, true_and, hcast] at hγ
    set g : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L)) := (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) with hg
    set u : (ZMod (l ^ L))ˣ := Matrix.GeneralLinearGroup.det γ with hu
    have hug : (u : ZMod (l ^ L)) = g.det := rfl
    set M : Matrix (Fin 2) (Fin 2) (ZMod (l ^ L)) :=
      !![g 0 0, (↑u⁻¹ : ZMod (l ^ L)) * g 0 1; g 1 0, (↑u⁻¹ : ZMod (l ^ L)) * g 1 1] with hM
    have hMdet : M.det = 1 := by
      rw [hM, Matrix.det_fin_two_of]
      have h2 : (↑u⁻¹ : ZMod (l ^ L)) * g.det = 1 := by
        rw [← hug, Units.inv_mul]
      rw [Matrix.det_fin_two] at h2
      linear_combination h2
    refine ⟨(⟨M, hMdet⟩, u * z⁻¹), ?_, ?_⟩
    · rw [Finset.mem_product]
      refine ⟨?_, ?_⟩
      · rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, hγ.1⟩
      · rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        rw [hmod, Units.val_mul, map_mul, hug, hγ.2, ← map_mul, ← Units.val_mul,
          mul_inv_cancel, Units.val_one, map_one]
    · apply Units.ext
      have hz : u * z⁻¹ * z = u := by group
      have e0 : ∀ i, ((t ⟨M, hMdet⟩ (u * z⁻¹ * z) : GL (Fin 2) (ZMod (l ^ L))) :
          Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 0 = g i 0 := by
        intro i
        refine (ht0 _ _ i).trans ?_
        fin_cases i <;> rfl
      have e1 : ∀ i, ((t ⟨M, hMdet⟩ (u * z⁻¹ * z) : GL (Fin 2) (ZMod (l ^ L))) :
          Matrix (Fin 2) (Fin 2) (ZMod (l ^ L))) i 1 = g i 1 := by
        intro i
        refine (ht1 _ _ i).trans ?_
        rw [hz]
        fin_cases i
        · change (u : ZMod (l ^ L)) * ((↑u⁻¹ : ZMod (l ^ L)) * g 0 1) = g 0 1
          rw [← mul_assoc, Units.mul_inv, one_mul]
        · change (u : ZMod (l ^ L)) * ((↑u⁻¹ : ZMod (l ^ L)) * g 1 1) = g 1 1
          rw [← mul_assoc, Units.mul_inv, one_mul]
      ext i j
      fin_cases j
      · exact e0 i
      · exact e1 i
  · intro p _
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.SumLevelSubgroupModEqSmulSumReps
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem T_mem_Gam (N l : ℕ) : ModularGroup.T ∈ Gam N l := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.T]
  · rw [CongruenceSubgroup.Gamma0_mem]
    simp [ModularGroup.T]

private theorem mul_Tm_mem (N l M : ℕ) [NeZero M] {γ : SL(2, ZMod M)} (h : γ ∈ Gs N l M) (b : ℕ) :
    γ * Tm M b ∈ Gs N l M := by
  simp only [Gs, Finset.mem_filter, Finset.mem_univ, true_and] at h ⊢
  exact Subgroup.mul_mem _ h (Subgroup.mem_map_of_mem _ (Subgroup.pow_mem _ (T_mem_Gam N l) b))

theorem UpperTheory.sum_levelSubgroupMod_eq_smul_sum_reps :
    ∀ (N l M : ℕ) [NeZero M] (R : Finset SL(2, ZMod M)), IsReps N l M R → ∀ (V : Type) [AddCommMonoid V] (f : SL(2, ZMod M) → V), (∀ γ ∈ R, ∀ b : ℕ, f (γ * Tm M b) = f γ) → ∑ γ ∈ Gs N l M, f γ = M • ∑ γ ∈ R, f γ := by
  intro N l M _ R hR V _ f hf
  obtain ⟨hsub, huniq⟩ := hR
  have key : ∑ p ∈ R ×ˢ Finset.range M, f p.1 = ∑ γ ∈ Gs N l M, f γ := by
    refine Finset.sum_bij (fun p _ => p.1 * Tm M p.2) ?_ ?_ ?_ ?_
    · intro p hp
      exact mul_Tm_mem N l M (hsub (Finset.mem_product.1 hp).1) _
    · intro p hp q hq hpq
      have hp' := Finset.mem_product.1 hp
      have hq' := Finset.mem_product.1 hq
      exact (huniq _ (mul_Tm_mem N l M (hsub hp'.1) p.2)).unique
        ⟨hp'.1, Finset.mem_range.1 hp'.2, rfl⟩ ⟨hq'.1, Finset.mem_range.1 hq'.2, hpq⟩
    · intro γ hγ
      obtain ⟨p, ⟨h1, h2, h3⟩, -⟩ := huniq γ hγ
      exact ⟨p, Finset.mem_product.2 ⟨h1, Finset.mem_range.2 h2⟩, h3.symm⟩
    · intro p hp
      exact (hf _ (Finset.mem_product.1 hp).1 _).symm
  rw [← key, Finset.sum_product, Finset.smul_sum]
  refine Finset.sum_congr rfl fun γ _ => ?_
  simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.EisensteinModularTowers.CardFiberReductionEqTotient
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem fib_card {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H] [DecidableEq H]
    (f : G →* H) (hf : Function.Surjective f) (z : H) :
    Fintype.card G = Fintype.card H * (Finset.univ.filter (fun y => f y = z)).card := by
  have h := Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  have hc : ∀ b ∈ (Finset.univ : Finset H),
      (Finset.univ.filter (fun a => f a = b)).card = (Finset.univ.filter (fun y => f y = z)).card :=
    fun b _ => MonoidHom.card_fiber_eq_of_mem_range f (hf b) (hf z)
  rw [Finset.card_univ, Finset.sum_congr rfl hc, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  exact h

theorem UpperTheory.card_fiber_reduction_eq_totient :
    ∀ (l : ℕ) [Fact l.Prime] (n m N : ℕ) [NeZero N], ¬ l ∣ N → ∀ z : (ZMod (l ^ (m + n)))ˣ, (Finset.univ.filter (fun y => redTop l n m N y = z)).card = Nat.totient (N * N) := by
  intro l _ n m N _ hN z
  have hl : l.Prime := Fact.out
  have hdvd : l ^ (m + n) ∣ topM l n m (N * N) := Dvd.intro _ rfl
  haveI : NeZero (l ^ (m + n)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  haveI : NeZero (topM l n m (N * N)) :=
    ⟨mul_ne_zero (pow_ne_zero _ hl.ne_zero) (mul_ne_zero (NeZero.ne N) (NeZero.ne N))⟩
  have key := fib_card (ZMod.unitsMap hdvd) (ZMod.unitsMap_surjective hdvd) z
  have hred : ∀ y, redTop l n m N y = ZMod.unitsMap hdvd y := fun y => rfl
  simp only [hred]
  rw [ZMod.card_units_eq_totient, ZMod.card_units_eq_totient] at key
  have hcop : (l ^ (m + n)).Coprime (N * N) := by
    have h1 : l.Coprime N := (Nat.Prime.coprime_iff_not_dvd hl).2 hN
    exact Nat.Coprime.pow_left _ (Nat.Coprime.mul_right h1 h1)
  have htot : (topM l n m (N * N)).totient = (l ^ (m + n)).totient * (N * N).totient :=
    Nat.totient_mul hcop
  rw [htot] at key
  have hpos : 0 < (l ^ (m + n)).totient := Nat.totient_pos.2 (pow_pos hl.pos _)
  exact (Nat.eq_of_mul_eq_mul_left hpos key).symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.MemClosureOfIsIntegral
open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

namespace UpperTheory.Kd.L.InertiaZetaPowers

open Finset

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]

private theorem zpow_mem_closure {x : Ω} {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1) (k : ℤ) :
    x ^ k ∈ Subring.closure {x} := by
  have hxm : x ∈ Subring.closure {x} := Subring.subset_closure (Set.mem_singleton x)
  have hinv : x⁻¹ = x ^ (m - 1) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', Nat.sub_add_cancel hm, hx]
  cases k with
  | ofNat a =>
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_mem hxm a
  | negSucc a =>
    rw [zpow_negSucc, ← inv_pow, hinv]
    exact pow_mem (pow_mem hxm _) _

private theorem zeta_pow (ε : Ω →+* ℂ) (l N L : ℕ) [NeZero l] [NeZero N] :
    eOm ε (1 / ((N * l ^ L : ℕ) : ℚ)) ^ N = zt ε l L := by
  have hl : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne l)
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  apply ε.injective
  rw [map_pow, zt, (eOm_props ε ε.injective).1, (eOm_props ε ε.injective).1, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

private theorem zeta_zpow_mem (ε : Ω →+* ℂ) (l N L : ℕ) [NeZero l] [NeZero N] (k : ℤ) :
    eOm ε (1 / ((N * l ^ L : ℕ) : ℚ)) ^ ((N : ℤ) * k) ∈ Subring.closure {zt ε l L} := by
  rw [zpow_mul, zpow_natCast, zeta_pow]
  exact zpow_mem_closure (Nat.pow_pos (Nat.pos_of_ne_zero (NeZero.ne l))) (IsNTr.isPrimitiveRoot_zt ε l L).pow_eq_one k

private theorem closure_le_adjoin (ε : Ω →+* ℂ) (l L : ℕ) {y : Ω} (h : y ∈ Subring.closure {zt ε l L}) :
    y ∈ IntermediateField.adjoin ℚ {zt ε l L} :=
  (Subring.closure_le (t := (IntermediateField.adjoin ℚ {zt ε l L}).toSubring)).2
    (IntermediateField.subset_adjoin ℚ _) h

private theorem eisF_mem (F : IntermediateField ℚ Ω) (j M N : ℕ) (ζ : Ω) (a₁ b : ℤ) (n : ℕ)
    (h : ∀ k : ℤ, ζ ^ ((N : ℤ) * k) ∈ F) : eisF j M ζ a₁ ((N : ℤ) * b) n ∈ F := by
  have hq : ∀ q : ℚ, (q : Ω) ∈ F := fun q => by simpa using F.algebraMap_mem q
  have hh : (1 / 2 : Ω) ∈ F := by simpa using hq (1 / 2)
  unfold eisF
  split_ifs with h0
  · unfold const0
    split_ifs
    · exact div_mem (mul_mem hh (add_mem (one_mem _) (h b))) (sub_mem (one_mem _) (h b))
    · exact hq _
    · exact neg_mem (hq _)
  · unfold coefPos
    refine sum_mem fun d _ => sub_mem ?_ ?_
    · split_ifs
      · refine mul_mem (pow_mem (div_mem (natCast_mem F _) (natCast_mem F _)) _) ?_
        rw [show (N : ℤ) * b * (d : ℤ) = (N : ℤ) * (b * d) by ring]
        exact h _
      · exact zero_mem _
    · split_ifs
      · refine mul_mem (pow_mem (neg_mem (div_mem (natCast_mem F _) (natCast_mem F _))) _) ?_
        rw [show -((N : ℤ) * b * (d : ℤ)) = (N : ℤ) * (-(b * d)) by ring]
        exact h _
      · exact zero_mem _

private theorem zpow_memF (F : IntermediateField ℚ Ω) {x : Ω} (hx : x ∈ F) (k : ℤ) : x ^ k ∈ F := by
  cases k with
  | ofNat a =>
    rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact pow_mem hx a
  | negSucc a =>
    rw [zpow_negSucc]
    exact inv_mem (pow_mem hx _)

private theorem smF_mem (F : IntermediateField ℚ Ω) (c : ℤ) (j M N : ℕ) (ζ : Ω) (a₁ a₂ : ℤ) (n : ℕ)
    (hd : (N : ℤ) ∣ a₂) (h : ∀ k : ℤ, ζ ^ ((N : ℤ) * k) ∈ F) : smF c j M ζ a₁ a₂ n ∈ F := by
  obtain ⟨b, rfl⟩ := hd
  unfold smF
  refine sub_mem (mul_mem (pow_mem (intCast_mem F c) _) (eisF_mem F j M N ζ a₁ b n h))
    (mul_mem (zpow_memF F (intCast_mem F c) _) ?_)
  rw [show c * ((N : ℤ) * b) = (N : ℤ) * (c * b) by ring]
  exact eisF_mem F j M N ζ _ _ n h

private theorem mem_closure_of_isIntegral (ε : Ω →+* ℂ) (l L : ℕ) [Fact l.Prime] [CharZero Ω] {y : Ω}
    (hy : y ∈ IntermediateField.adjoin ℚ {zt ε l L}) (hi : IsIntegral ℤ y) :
    y ∈ Subring.closure {zt ε l L} := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  haveI : NeZero (l ^ L) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hz := IsNTr.isPrimitiveRoot_zt ε l L
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  haveI hcyc : IsCyclotomicExtension {l ^ L} ℚ (IntermediateField.adjoin ℚ {zt ε l L}) :=
    by
      convert hz.intermediateField_adjoin_isCyclotomicExtension ℚ using 1 <;>
        exact Subsingleton.elim _ _
  let zF : IntermediateField.adjoin ℚ {zt ε l L} := ⟨zt ε l L, IntermediateField.mem_adjoin_simple_self ℚ _⟩
  have hzF : IsPrimitiveRoot zF (l ^ L) :=
    IsPrimitiveRoot.of_map_of_injective (f := (IntermediateField.adjoin ℚ {zt ε l L}).toSubfield.subtype) hz
      (IntermediateField.adjoin ℚ {zt ε l L}).toSubfield.subtype.injective
  have hcl := IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow
    (p := l) (k := L) (ζ := zF) hzF
  have hi' : IsIntegral ℤ (⟨y, hy⟩ : IntermediateField.adjoin ℚ {zt ε l L}) :=
    (isIntegral_algHom_iff ((IntermediateField.adjoin ℚ {zt ε l L}).toSubfield.subtype.toIntAlgHom)
      (IntermediateField.adjoin ℚ {zt ε l L}).toSubfield.subtype.injective).1 hi
  obtain ⟨t, ht⟩ := hcl.isIntegral_iff.1 hi'
  have key : ∀ s ∈ Algebra.adjoin ℤ ({zF} : Set (IntermediateField.adjoin ℚ {zt ε l L})),
      ((s : IntermediateField.adjoin ℚ {zt ε l L}) : Ω) ∈ Subring.closure {zt ε l L} := by
    intro s hs
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff.1 hx]
      exact Subring.subset_closure rfl
    | algebraMap r => simpa using intCast_mem (Subring.closure {zt ε l L}) r
    | add x y _ _ hx hy => simpa using add_mem hx hy
    | mul x y _ _ hx hy => simpa using mul_mem hx hy
  have e : y = (((t : IntermediateField.adjoin ℚ {zt ε l L})) : Ω) := by
    have := congrArg (fun s : IntermediateField.adjoin ℚ {zt ε l L} => (s : Ω)) ht
    exact this.symm
  rw [e]
  exact key _ t.2

private theorem inZl_of_mem {ε : Ω →+* ℂ} {l L : ℕ} [Fact l.Prime] {y : Ω} (h : y ∈ Subring.closure {zt ε l L}) :
    InZl ε l L y :=
  ⟨1, fun h1 => (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 h1), by simpa using h⟩

private theorem inZl_add {ε : Ω →+* ℂ} {l L : ℕ} [Fact l.Prime] {a b : Ω} (ha : InZl ε l L a) (hb : InZl ε l L b) :
    InZl ε l L (a + b) := by
  obtain ⟨D, hD, h⟩ := ha
  obtain ⟨D', hD', h'⟩ := hb
  refine ⟨D * D', fun hd => ((Fact.out : l.Prime).dvd_mul.1 hd).elim hD hD', ?_⟩
  have e : ((D * D' : ℕ) : Ω) * (a + b) = (D' : Ω) * ((D : Ω) * a) + (D : Ω) * ((D' : Ω) * b) := by
    push_cast
    ring
  rw [e]
  exact add_mem (mul_mem (natCast_mem _ _) h) (mul_mem (natCast_mem _ _) h')

private theorem inZl_mul {ε : Ω →+* ℂ} {l L : ℕ} [Fact l.Prime] {a b : Ω} (ha : InZl ε l L a) (hb : InZl ε l L b) :
    InZl ε l L (a * b) := by
  obtain ⟨D, hD, h⟩ := ha
  obtain ⟨D', hD', h'⟩ := hb
  refine ⟨D * D', fun hd => ((Fact.out : l.Prime).dvd_mul.1 hd).elim hD hD', ?_⟩
  have e : ((D * D' : ℕ) : Ω) * (a * b) = ((D : Ω) * a) * ((D' : Ω) * b) := by
    push_cast
    ring
  rw [e]
  exact mul_mem h h'

private theorem inZl_sum {ε : Ω →+* ℂ} {l L : ℕ} [Fact l.Prime] {ι : Type} (s : Finset ι) (f : ι → Ω)
    (h : ∀ i ∈ s, InZl ε l L (f i)) : InZl ε l L (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using inZl_of_mem (zero_mem _)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact inZl_add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

end UpperTheory.Kd.L.InertiaZetaPowers

namespace UpperTheory.Kd.L.InertiaZetaPowers

open Finset

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω]

private theorem smF_one_mem (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c L : ℕ) (hL : 1 ≤ L)
    (hc : Nat.Coprime c (6 * l * N)) (a a₂ : ℤ) (ha : ¬ (l : ℤ) ∣ a) (h₂ : (N : ℤ) ∣ a₂) (r : ℕ) :
    smF (c : ℤ) 1 (N * l ^ L) (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) a a₂ r ∈ Subring.closure {zt ε l L} := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨b, rfl⟩ := h₂
  have hcN : Nat.Coprime c N := hc.coprime_dvd_right (Dvd.intro_left _ rfl)
  have hcl : Nat.Coprime c l := hc.coprime_dvd_right ((Dvd.intro_left _ rfl : l ∣ 6 * l).mul_right N)
  refine smF_one_mem_subring Ω _ c (N * l ^ L) _ a _
    (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne N)) (Nat.pow_pos (Nat.pos_of_ne_zero (NeZero.ne l))))
    (Nat.Coprime.mul_right hcN (Nat.Coprime.pow_right L hcl)) ?_ (zeta_zpow_mem ε l N L b) ?_ r
  · intro h
    refine ha (dvd_trans ?_ h)
    exact_mod_cast Dvd.dvd.mul_left (dvd_pow_self l (by omega : L ≠ 0)) N
  · rw [show -((N : ℤ) * b) = (N : ℤ) * (-b) by ring]
    exact zeta_zpow_mem ε l N L _

private theorem cong_step (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c L w : ℕ) (hw : 1 ≤ w)
    (h2 : l ≠ 2) (hlN : ¬ l ∣ N) (hc : Nat.Coprime c (6 * l * N)) (hb : (w + 1) ^ 2 * l ≤ l ^ L)
    (α a₁ a₂ : ℤ) (h0 : 0 ≤ α) (hlt : α < (l : ℤ) ^ L) (hcong : a₁ ≡ N * α [ZMOD (l : ℤ) ^ L]) (h₂ : (N : ℤ) ∣ a₂) (r : ℕ) :
    ∃ β : Ω, InZl ε l L β ∧ (l : Ω) ^ (L - 1) * β =
      (α : Ω) ^ w * smF (c : ℤ) 1 (N * l ^ L) (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) a₁ a₂ r -
        (l : Ω) ^ (L * w) * smF (c : ℤ) (w + 1) (N * l ^ L) (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) a₁ a₂ r := by
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne l)
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hζ : IsPrimitiveRoot (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) (N * l ^ L) :=
    isPrimitiveRoot_eOm ε (Nat.mul_ne_zero (NeZero.ne N) (pow_ne_zero _ (NeZero.ne l)))
  have hcl : Nat.Coprime c l := hc.coprime_dvd_right ((Dvd.intro_left _ rfl : l ∣ 6 * l).mul_right N)
  have hlc : ¬ (l : ℤ) ∣ (c : ℤ) := fun h =>
    ((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).1 hcl.symm) (Int.natCast_dvd_natCast.1 h)
  obtain ⟨D, hD, hint⟩ := GlobalTheory.EisCongGen.smF_congr_gen l N L (w + 1) Ω _ h2 hζ
    (Nat.pos_of_ne_zero (NeZero.ne N)) hlN (by omega) hb (c : ℤ) hlc α a₁ a₂ h0 hlt hcong r
  rw [Nat.add_sub_cancel] at hint
  have hF : ∀ k : ℤ, eOm ε (1 / ((N * l ^ L : ℕ) : ℚ)) ^ ((N : ℤ) * k) ∈ IntermediateField.adjoin ℚ {zt ε l L} :=
    fun k => closure_le_adjoin ε l L (zeta_zpow_mem ε l N L k)
  refine ⟨_, ?_, mul_div_cancel₀ _ (pow_ne_zero _ hl0)⟩
  refine ⟨D, hD, mem_closure_of_isIntegral ε l L ?_ ?_⟩
  · refine mul_mem (natCast_mem _ _) (div_mem (sub_mem (mul_mem (pow_mem (intCast_mem _ _) _) ?_)
      (mul_mem (pow_mem (natCast_mem _ _) _) ?_)) (pow_mem (natCast_mem _ _) _))
    · exact smF_mem _ _ _ _ N _ _ _ _ h₂ hF
    · exact smF_mem _ _ _ _ N _ _ _ _ h₂ hF
  · rw [← mul_div_assoc]
    exact hint

private theorem comb (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime] (L n w m : ℕ) (hnL : n < L) (A₁ A₂ B : ℕ → Ω)
    (α u : ℤ) (e : ℕ) (he : (e : ℤ) = α ^ w + (l : ℤ) ^ n * u)
    (hA : ∀ r, A₁ r ∈ Subring.closure {zt ε l L}) (hB : ∀ r, B r ∈ Subring.closure {zt ε l L})
    (hβ : ∀ r, ∃ β : Ω, InZl ε l L β ∧ (l : Ω) ^ (L - 1) * β = (α : Ω) ^ w * A₁ r - (l : Ω) ^ (L * w) * A₂ r) :
    ∃ E : Ω, InZl ε l L E ∧ (e : Ω) * cmul A₁ B m = (l : Ω) ^ (L * w) * cmul A₂ B m + (l : Ω) ^ n * E := by
  choose β hβ₁ hβ₂ using hβ
  refine ⟨∑ i ∈ range (m + 1), ((u : Ω) * A₁ i + (l : Ω) ^ (L - 1 - n) * β i) * B (m - i), ?_, ?_⟩
  · refine inZl_sum _ _ fun i _ => inZl_mul (inZl_add (inZl_of_mem (mul_mem (intCast_mem _ _) (hA i)))
      (inZl_mul (inZl_of_mem (pow_mem (natCast_mem _ _) _)) (hβ₁ i))) (inZl_of_mem (hB _))
  · have e1 : (e : Ω) = (α : Ω) ^ w + (l : Ω) ^ n * (u : Ω) := by
      have := congrArg (Int.cast : ℤ → Ω) he
      push_cast at this
      exact this
    have e2 : (l : Ω) ^ n * (l : Ω) ^ (L - 1 - n) = (l : Ω) ^ (L - 1) := by
      rw [← pow_add]
      congr 1
      omega
    unfold cmul
    rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    linear_combination (A₁ i * B (m - i)) * e1 - B (m - i) * hβ₂ i - (β i * B (m - i)) * e2

private theorem coefQ_nat (M : ℕ) (f : ℕ → Ω) (i : ℕ) : coefQ M f (i : ℚ) = f (M * i) := by
  have e : (i : ℚ) * (M : ℚ) = ((M * i : ℕ) : ℚ) := by
    push_cast
    ring
  unfold coefQ
  rw [e, if_pos ⟨Nat.cast_nonneg _, Rat.den_natCast _⟩, Rat.num_natCast, Int.toNat_natCast]

private theorem ex_eq (l n L w : ℕ) [Fact l.Prime] (hnL : n < L) (g : SL(2, ℤ)) :
    ∃ u : ℤ, ((ex l n w g : ℕ) : ℤ) = (en g 0 0 % (l : ℤ) ^ L) ^ w + (l : ℤ) ^ n * u := by
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have h1 : (((((en g 0 0 : ℤ) : ZMod (l ^ n)).val : ℕ) : ℤ) : ZMod (l ^ n)) = ((en g 0 0 : ℤ) : ZMod (l ^ n)) := by
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have h2 := (ZMod.intCast_eq_intCast_iff _ _ (l ^ n)).1 h1
  have h3 : (l : ℤ) ^ n ∣ (l : ℤ) ^ L := pow_dvd_pow _ hnL.le
  have h4 : en g 0 0 % (l : ℤ) ^ L ≡ en g 0 0 [ZMOD (l : ℤ) ^ n] := Int.emod_emod_of_dvd _ h3
  have h5 : en g 0 0 % (l : ℤ) ^ L ≡ (((en g 0 0 : ℤ) : ZMod (l ^ n)).val : ℤ) [ZMOD (l : ℤ) ^ n] := by
    refine h4.trans (Int.ModEq.symm ?_)
    simpa using h2
  obtain ⟨u, hu⟩ := Int.modEq_iff_dvd.1 (h5.pow w)
  refine ⟨u, ?_⟩
  unfold ex
  push_cast
  linarith

end UpperTheory.Kd.L.InertiaZetaPowers

open UpperTheory.Kd.L.InertiaZetaPowers in
theorem UpperTheory.Kd.L.inzl :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (x : ZMod N) (L n w : ℕ), 1 ≤ w → n < L → ∀ g : SL(2, ℤ), ¬ (l : ℤ) ∣ en g 0 0 → ¬ (l : ℤ) ∣ en g 1 0 → ∀ i : ℕ, InZl ε l L (EE ε l L N x c d g (i : ℚ)) ∧ ((w + 1) ^ 2 * l ≤ l ^ L → ∃ E : Ω, InZl ε l L E ∧ (ex l n w g : Ω) * EE ε l L N x c d g (i : ℚ) = (l : Ω) ^ (L * w) * cmul (smF c (w + 1) (N * l ^ L) (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) (en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L)) ((N : ℤ) ^ 2 * en g 0 1)) (smF d 1 (N * l ^ L) (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) (en g 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g 1 0) ((N : ℤ) * en g 1 1)) (l ^ L * i) + (l : Ω) ^ n * E) := by
  intro Ω _ _ _ _ ε l _ N _ c d gm hP x L n w hw hnL g hg0 hg1 i
  have hL : 1 ≤ L := by omega
  have hlp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
  have hlL : (l : ℤ) ∣ (l : ℤ) ^ L := dvd_pow_self _ (by omega)
  have hNl : ¬ (l : ℤ) ∣ (N : ℤ) := fun h => hP.cop (Int.natCast_dvd_natCast.1 h)
  have ha : ¬ (l : ℤ) ∣ en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L) := by
    intro h
    rcases hlp.dvd_or_dvd h with h | h
    · exact hg0 h
    · exact hNl ((dvd_add_left (hlL.mul_left _)).1 h)
  have hb : ¬ (l : ℤ) ∣ en g 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g 1 0 := fun h =>
    hg1 ((dvd_add_right (hlL.mul_left _)).1 h)
  have hA := smF_one_mem ε l N c L hL hP.cc _ ((N : ℤ) ^ 2 * en g 0 1) ha ⟨(N : ℤ) * en g 0 1, by ring⟩
  have hB := smF_one_mem ε l N d L hL hP.dc _ ((N : ℤ) * en g 1 1) hb ⟨en g 1 1, rfl⟩
  have hEE : EE ε l L N x c d g (i : ℚ) = cmul (smF c 1 (N * l ^ L) (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) (en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L)) ((N : ℤ) ^ 2 * en g 0 1)) (smF d 1 (N * l ^ L) (eOm ε (1 / ((N * l ^ L : ℕ) : ℚ))) (en g 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g 1 0) ((N : ℤ) * en g 1 1)) (l ^ L * i) :=
    coefQ_nat _ _ _
  rw [hEE]
  refine ⟨inZl_of_mem (sum_mem fun r _ => mul_mem (hA r) (hB _)), fun hbd => ?_⟩
  obtain ⟨u, hu⟩ := ex_eq l n L w hnL g
  have hlpos : (0 : ℤ) < (l : ℤ) ^ L := by
    have := (Fact.out : l.Prime).pos
    positivity
  refine comb ε l L n w _ hnL _ _ _ (en g 0 0 % (l : ℤ) ^ L) u _ hu hA hB fun r => ?_
  refine cong_step ε l N c L w hw hP.odd hP.cop hP.cc hbd _ _ _ (Int.emod_nonneg _ hlpos.ne') (Int.emod_lt_of_pos _ hlpos) ?_
    ⟨(N : ℤ) * en g 0 1, by ring⟩ r
  refine Int.modEq_iff_dvd.2 ⟨-(N : ℤ) * (en g 0 0 / (l : ℤ) ^ L) - en g 0 0 * ((x.val : ℤ) * (topT l L N : ℤ)), ?_⟩
  rw [Int.emod_def]
  ring
end

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

noncomputable section
namespace UpperTheory.Kd.L

private def dgU {R : Type} [CommRing R] (u : Rˣ) : GL (Fin 2) R :=
  ⟨!![1, 0; 0, (u : R)], !![1, 0; 0, ((u⁻¹ : Rˣ) : R)], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

private def tw {R : Type} [CommRing R] (h : SL(2, R)) (u : Rˣ) : GL (Fin 2) R :=
  Matrix.SpecialLinearGroup.toGL h * dgU u

private theorem twist_column_zero {R : Type} [CommRing R] (h : SL(2, R)) (u : Rˣ) (i : Fin 2) :
    ((tw h u : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i 0 = h i 0 := by
  fin_cases i <;> simp [tw, dgU, Matrix.mul_apply, Fin.sum_univ_two]

private theorem twist_column_one {R : Type} [CommRing R] (h : SL(2, R)) (u : Rˣ) (i : Fin 2) :
    ((tw h u : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) i 1 = (u : R) * h i 1 := by
  fin_cases i <;> simp [tw, dgU, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

private abbrev kz {K : Type} [Field K] [CharZero K] (ζ : K) (l L N : ℕ) (x : ZMod N) (c d w : ℕ) (g : SL(2, ℤ)) : ℕ → K :=
  cmul (smF (c : ℤ) (w + 1) (N * l ^ L) ζ (en g 0 0 * ((N : ℤ) + (x.val : ℤ) * (topT l L N : ℤ) * (l : ℤ) ^ L)) ((N : ℤ) ^ 2 * en g 0 1))
    (smF (d : ℤ) 1 (N * l ^ L) ζ (en g 0 0 * (topT l L N : ℤ) * (l : ℤ) ^ L + en g 1 0) ((N : ℤ) * en g 1 1))

private abbrev kg {K : Type} [Field K] [CharZero K] (ζ : K) (l L N : ℕ) (c d : ℤ) (w : ℕ) (v v' : ℤ × ℤ)
    (γ : GL (Fin 2) (ZMod (l ^ L))) : ℕ → K :=
  cmul (smF c (w + 1) (N * l ^ L) ζ (rowT N l L γ 0 v).1 (rowT N l L γ 0 v).2)
    (smF d 1 (N * l ^ L) ζ (rowT N l L γ 1 v').1 (rowT N l L γ 1 v').2)

private theorem swap4 {V α β γ δ : Type} [AddCommMonoid V] (A : Finset α) (B : Finset β) (C : Finset γ) (D : Finset δ)
    (f : α → β → γ → δ → V) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ e ∈ D, f a b c e = ∑ e ∈ D, ∑ c ∈ C, ∑ a ∈ A, ∑ b ∈ B, f a b c e := by
  have h1 : ∀ a, ∑ b ∈ B, ∑ c ∈ C, ∑ e ∈ D, f a b c e = ∑ c ∈ C, ∑ e ∈ D, ∑ b ∈ B, f a b c e := fun a => by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
  simp_rw [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ c, ∑ a ∈ A, ∑ e ∈ D, ∑ b ∈ B, f a b c e = ∑ e ∈ D, ∑ a ∈ A, ∑ b ∈ B, f a b c e := fun c => Finset.sum_comm
  simp_rw [h2]
  exact Finset.sum_comm

private theorem sum_key {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (l : ℕ) [Fact l.Prime]
    (N : ℕ) [NeZero N] (c d w : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)) (hP : Par l N c d gm) (x : ZMod N) (a₀ : ℤ) (ha₀ : (a₀ : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N)) (m n : ℕ) (hm : 1 ≤ m)
    (R : Finset SL(2, ZMod (topMu l n m N))) (hR : IsReps N l (topMu l n m N) R) (z : (ZMod (l ^ (m + n)))ˣ)
    (τ : (ZMod (l ^ (m + n)))ˣ → (Ω ≃ₐ[ℚ] Ω))
    (hτ : ∀ a, τ a (zt ε l (m + n)) = zt ε l (m + n) ^ (a : ZMod (l ^ (m + n))).val)
    (μ : ℕ) (hμ : ∀ (Φ : SL(2, ZMod (l ^ (m + n))) → Ω) (Ψ : SL(2, ℤ) → Ω), (∀ g ∈ CongruenceSubgroup.Gamma0 N, ((en g 0 0 : ℤ) : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N) → ∀ h : SL(2, ZMod (l ^ (m + n))), h 0 0 = (en g 0 0 : ℤ) → h 0 1 = ((N : ℤ) * en g 0 1 : ℤ) → (N : ZMod (l ^ (m + n))) * h 1 0 = (en g 1 0 : ℤ) → h 1 1 = (en g 1 1 : ℤ) → Ψ g = Φ h) → ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ Gs N l (topMu l n m N), Ψ (gm r₀ * liftSL _ γ) = μ • ∑ h ∈ Finset.univ.filter (fun h : SL(2, ZMod (l ^ (m + n))) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val), Φ h)
    (i : ℕ) :
    ((topMu l n m N : ℕ) : Ω) * ∑ a ∈ Finset.univ.filter (fun a : (ZMod (l ^ (m + n)))ˣ => (a : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]),
      τ a (∑ y ∈ Finset.univ.filter (fun y => redTop l n m N y = z), ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ R,
        repM (topM l n m (N * N)) y (kz (eOm ε (1 / ((N * l ^ (m + n) : ℕ) : ℚ))) l (m + n) N x c d w (gm r₀ * liftSL _ γ) (l ^ (m + n) * i))) =
    (μ : Ω) * (Nat.totient (N * N) : Ω) * ∑ γ ∈ ((unitSet l (m + n)).filter fun γ : GL (Fin 2) (ZMod (l ^ (m + n))) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))).det.val : ℕ) : ZMod (l ^ m)) = (((z : ZMod (l ^ (m + n))).val : ℕ) : ZMod (l ^ m))),
      kg (eOm ε (1 / ((N * l ^ (m + n) : ℕ) : ℚ))) l (m + n) N (c : ℤ) (d : ℤ) w ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) γ (l ^ (m + n) * i) := by
  have hcop : ¬ l ∣ N := hP.cop
  have hroots := UpperTheory.isPrimitiveRoot_eOm_and_pow_compatible ε l N
  obtain ⟨hpr, hzN, -⟩ := hroots
  set ζ : Ω := eOm ε (1 / ((N * l ^ (m + n) : ℕ) : ℚ)) with hζdef
  have hζN : ζ ^ N = zt ε l (m + n) := hzN (m + n)
  have hζ1 : ζ ^ (N * l ^ (m + n)) = 1 := (hpr (m + n)).pow_eq_one
  have hzt1 : zt ε l (m + n) ^ (l ^ (m + n)) = 1 := by rw [← hζN, ← pow_mul, hζ1]
  set A := Finset.univ.filter (fun a : (ZMod (l ^ (m + n)))ˣ => (a : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]) with hA
  set Fy := Finset.univ.filter (fun y => redTop l n m N y = z) with hFy
  set r : ℕ := l ^ (m + n) * i with hr
  let Ψ : SL(2, ℤ) → Ω := fun g => ∑ a ∈ A, ∑ y ∈ Fy, τ a (repM (topM l n m (N * N)) y (kz ζ l (m + n) N x c d w g r))
  let Φ : SL(2, ZMod (l ^ (m + n))) → Ω := fun h => (Nat.totient (N * N)) • ∑ a ∈ A,
    kg ζ l (m + n) N (c : ℤ) (d : ℤ) w ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) (tw h (a * z)) r
  have hΨ : ∀ g ∈ CongruenceSubgroup.Gamma0 N, ((en g 0 0 : ℤ) : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N) → ∀ h : SL(2, ZMod (l ^ (m + n))), h 0 0 = (en g 0 0 : ℤ) → h 0 1 = ((N : ℤ) * en g 0 1 : ℤ) → (N : ZMod (l ^ (m + n))) * h 1 0 = (en g 1 0 : ℤ) → h 1 1 = (en g 1 1 : ℤ) → Ψ g = Φ h := by
    intro g hg hga h h00 h01 h10 h11
    show ∑ a ∈ A, ∑ y ∈ Fy, _ = (Nat.totient (N * N)) • ∑ a ∈ A, _
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hy : ∀ y ∈ Fy, τ a (repM (topM l n m (N * N)) y (kz ζ l (m + n) N x c d w g r)) =
        kg ζ l (m + n) N (c : ℤ) (d : ℤ) w ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) (tw h (a * z)) r := by
      intro y hy
      have hyz : redTop l n m N y = z := (Finset.mem_filter.1 hy).2
      let s : Ω →+* Ω := (τ a).toRingEquiv.toRingHom.comp (repM (Ω := Ω) (topM l n m (N * N)) y).toRingEquiv.toRingHom
      have hs : s (ζ ^ N) = (ζ ^ N) ^ (((a * z : (ZMod (l ^ (m + n)))ˣ) : ZMod (l ^ (m + n))).val) := by
        rw [hζN]
        show τ a (repM (topM l n m (N * N)) y (zt ε l (m + n))) = _
        rw [UpperTheory.repM_apply_zt_eq_pow_redTop ε l n m N y, hyz, map_pow, hτ a, ← pow_mul, Units.val_mul, ZMod.val_mul,
          ← pow_eq_pow_mod _ hzt1]
      exact UpperTheory.gamma0_diamond_action_eq ζ l (m + n) N x c d w a₀ s
        (((a * z : (ZMod (l ^ (m + n)))ˣ) : ZMod (l ^ (m + n)))) hcop hζ1 hs g hg (hga.trans ha₀.symm) (tw h (a * z))
        (by rw [twist_column_zero, h00]) (by rw [twist_column_one, h01]) (by rw [twist_column_zero, h10]) (by rw [twist_column_one, h11]) r
    rw [Finset.sum_congr rfl hy, Finset.sum_const, hFy, UpperTheory.card_fiber_reduction_eq_totient l n m N hcop z]
  have hcount := hμ Φ Ψ hΨ
  have hT : ∀ γ ∈ R, ∀ b : ℕ, (fun γ => ∑ r₀ : (ZMod l)ˣ, Ψ (gm r₀ * liftSL _ γ)) (γ * Tm (topMu l n m N) b) =
      (fun γ => ∑ r₀ : (ZMod l)ˣ, Ψ (gm r₀ * liftSL _ γ)) γ := by
    intro γ _ b
    refine Finset.sum_congr rfl fun r₀ _ => ?_
    have hk := UpperTheory.cmul_smF_invariant_of_congruent_mul_T_pow ζ l (m + n) N x c d w (topMu l n m N) (NeZero.pos N) (Fact.out : l.Prime).pos hζ1
      ⟨N, by unfold topMu; ring⟩ b (gm r₀ * liftSL _ γ) (gm r₀ * liftSL _ (γ * Tm (topMu l n m N) b))
      (by simp only [map_mul, GlobalTheory.K4.map_liftSL, Tm, mul_assoc]) i
    show ∑ a ∈ A, ∑ y ∈ Fy, _ = ∑ a ∈ A, ∑ y ∈ Fy, _
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun y _ => ?_
    exact congrArg (fun t => τ a (repM (topM l n m (N * N)) y t)) hk
  have hG := UpperTheory.sum_levelSubgroupMod_eq_smul_sum_reps N l (topMu l n m N) R hR Ω (fun γ => ∑ r₀ : (ZMod l)ˣ, Ψ (gm r₀ * liftSL _ γ)) hT
  have htw := UpperTheory.congruence_action_invariant l (m + n) m hm (by omega) z tw twist_column_zero twist_column_one Ω
    (kg ζ l (m + n) N (c : ℤ) (d : ℤ) w ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) · r)
  rw [← htw]
  have hl : ∑ a ∈ A, τ a (∑ y ∈ Fy, ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ R,
        repM (topM l n m (N * N)) y (kz ζ l (m + n) N x c d w (gm r₀ * liftSL _ γ) r)) =
      ∑ γ ∈ R, ∑ r₀ : (ZMod l)ˣ, Ψ (gm r₀ * liftSL _ γ) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    exact swap4 A Fy Finset.univ R _
  have hΦ : ∑ h ∈ Finset.univ.filter (fun h : SL(2, ZMod (l ^ (m + n))) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val), Φ h =
      (Nat.totient (N * N)) • ∑ h ∈ Finset.univ.filter (fun h : SL(2, ZMod (l ^ (m + n))) => ¬ l ∣ (h 0 0).val ∧ ¬ l ∣ (h 1 0).val), ∑ a ∈ A,
        kg ζ l (m + n) N (c : ℤ) (d : ℤ) w ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) (tw h (a * z)) r := by
    rw [Finset.smul_sum]
  rw [hl, ← nsmul_eq_mul, ← hG, Finset.sum_comm, hcount, hΦ]
  simp only [nsmul_eq_mul]
  ring

end UpperTheory.Kd.L

theorem UpperTheory.Kd.L.arith :
    ∀ (l : ℕ) [Fact l.Prime] (N : ℕ) [NeZero N] (w : ℕ), 1 ≤ w → ∃ κ : ℚ, κ ≠ 0 ∧ ∃ L₀ : ℕ, ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] [CharZero Ω] (ε : Ω →+* ℂ) (c d : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), Par l N c d gm → ∀ (x : ZMod N) (m n : ℕ), 1 ≤ m → ∀ R, IsReps N l (topMu l n m N) R → ∀ (z : (ZMod (l ^ (m + n)))ˣ), (∀ r : ℚ, InZl ε l (m + n) (Fsum ε l n m N x c d w gm R z r)) ∧ (L₀ ≤ m + n → ∀ (i : ℕ) (F' : Ω), IsNT ε l (m + n) m (Fsum ε l n m N x c d w gm R z (i : ℚ)) F' → ∀ (β : ℕ) (t a : ℤ), (a : ZMod N) = ((en (gm 1) 0 0 : ℤ) : ZMod N) → β ≡ (z : ZMod (l ^ (m + n))).val [MOD l ^ m] → (β : ZMod N) = 1 → (l : ℤ) ^ m * t ≡ 1 [ZMOD N] → ∃ E : Ω, InZl ε l m E ∧ F' = (κ : Ω) * (l : Ω) ^ m * toQ (l ^ m) (pieceT N l m m (w + 2) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ) ((x.val : ℤ) * a * t, 0) (a * t, 0) (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β) ((unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i + (l : Ω) ^ n * E) := by
  intro l _ N _ w hw
  obtain ⟨μ, hμ0, hμ⟩ := UpperTheory.Kd.L.count l N
  have hN0 : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hNN : 0 < N * N := Nat.mul_pos (NeZero.pos N) (NeZero.pos N)
  refine ⟨-((N : ℚ) * (Nat.totient (N * N) : ℚ) * (μ : ℚ)), neg_ne_zero.2 (mul_ne_zero (mul_ne_zero hN0
    (Nat.cast_ne_zero.2 (Nat.totient_pos.2 hNN).ne')) (Nat.cast_ne_zero.2 hμ0.ne')), (w + 1) ^ 2 * l, ?_⟩
  intro Ω _ _ _ _ ε c d gm hP x m n hm R hR z
  have hl : l.Prime := Fact.out
  have hNl : N * l ∣ topMu l n m N := by
    have h1 : l ∣ l ^ (m + n) := dvd_pow_self l (by omega)
    obtain ⟨e, he⟩ := h1
    exact ⟨e * N, by unfold topMu; rw [he]; ring⟩
  have hreps := (UpperTheory.Kd.L.reps l N c d gm hP (topMu l n m N) hNl).2
  have hcond : ∀ (r₀ : (ZMod l)ˣ) (γ : SL(2, ZMod (topMu l n m N))), γ ∈ R →
      ¬ (l : ℤ) ∣ en (gm r₀ * liftSL _ γ) 0 0 ∧ ¬ (l : ℤ) ∣ en (gm r₀ * liftSL _ γ) 1 0 :=
    fun r₀ γ hγ => (hreps γ (hR.1 hγ) r₀).2.2.2
  obtain ⟨inat, iadd, imul, igal⟩ := UpperTheory.inZl_closed_add_mul_and_cyclotomic_galois_stable ε l (m + n)
  have hi0 : InZl ε l (m + n) (0 : Ω) := by simpa using inat 0
  have isum : ∀ {α : Type} (s : Finset α) (f : α → Ω), (∀ a ∈ s, InZl ε l (m + n) (f a)) →
      InZl ε l (m + n) (∑ a ∈ s, f a) := fun s f h => Finset.sum_induction f _ iadd hi0 h
  have irep : ∀ (y : (ZMod (topM l n m (N * N)))ˣ) (F : Ω), InZl ε l (m + n) F →
      InZl ε l (m + n) (repM (topM l n m (N * N)) y F) := fun y F h => igal _ _ (UpperTheory.repM_apply_zt_eq_pow_redTop ε l n m N y) F h
  have iN3 : InZl ε l (m + n) ((N : Ω) ^ 3) := by have h := inat (N ^ 3); rwa [Nat.cast_pow] at h
  have hEE : ∀ (r₀ : (ZMod l)ˣ) (γ : SL(2, ZMod (topMu l n m N))), γ ∈ R → ∀ r : ℚ, r.den = 1 →
      InZl ε l (m + n) (EE ε l (m + n) N x c d (gm r₀ * liftSL _ γ) r) := by
    intro r₀ γ hγ r hden
    rcases lt_or_ge r 0 with hr | hr
    · have h0 : EE ε l (m + n) N x c d (gm r₀ * liftSL _ γ) r = 0 := by
        simp [EE, coefQ, not_le.2 hr]
      rw [h0]; exact hi0
    · have h1 : (r.num : ℚ) = r := Rat.coe_int_num_of_den_eq_one hden
      have h2 : 0 ≤ r.num := Rat.num_nonneg.2 hr
      have h3 : r = ((r.num.toNat : ℕ) : ℚ) := by
        calc r = (r.num : ℚ) := h1.symm
          _ = ((r.num.toNat : ℤ) : ℚ) := by rw [Int.toNat_of_nonneg h2]
          _ = _ := by push_cast; rfl
      rw [h3]
      exact (UpperTheory.Kd.L.inzl ε l N c d gm hP x (m + n) n w hw (by omega) _ (hcond r₀ γ hγ).1 (hcond r₀ γ hγ).2 _).1
  constructor
  · intro r
    unfold Fsum
    split_ifs with hden
    · exact imul _ _ iN3 (isum _ _ fun y _ => isum _ _ fun r₀ _ => isum _ _ fun γ hγ =>
        imul _ _ (inat _) (irep y _ (hEE r₀ γ hγ r hden)))
    · exact hi0
  intro hL i F' hNT β t a₀ ha₀ hβ hβN ht
  have hlarge : (w + 1) ^ 2 * l ≤ l ^ (m + n) := hL.trans (Nat.lt_pow_self hl.one_lt).le
  have hex : ∀ (r₀ : (ZMod l)ˣ) (γ : SL(2, ZMod (topMu l n m N))), γ ∈ R → ∃ E : Ω, InZl ε l (m + n) E ∧
      (ex l n w (gm r₀ * liftSL _ γ) : Ω) * EE ε l (m + n) N x c d (gm r₀ * liftSL _ γ) (i : ℚ) =
        (l : Ω) ^ ((m + n) * w) * kz (eOm ε (1 / ((N * l ^ (m + n) : ℕ) : ℚ))) l (m + n) N x c d w (gm r₀ * liftSL _ γ) (l ^ (m + n) * i) +
          (l : Ω) ^ n * E :=
    fun r₀ γ hγ => (UpperTheory.Kd.L.inzl ε l N c d gm hP x (m + n) n w hw (by omega) _ (hcond r₀ γ hγ).1 (hcond r₀ γ hγ).2 i).2 hlarge
  choose! E hE using hex
  set ζ : Ω := eOm ε (1 / ((N * l ^ (m + n) : ℕ) : ℚ)) with hζdef
  set S1 : Ω := ∑ y ∈ Finset.univ.filter (fun y => redTop l n m N y = z), ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ R,
    repM (topM l n m (N * N)) y (kz ζ l (m + n) N x c d w (gm r₀ * liftSL _ γ) (l ^ (m + n) * i)) with hS1
  set S2 : Ω := ∑ y ∈ Finset.univ.filter (fun y => redTop l n m N y = z), ∑ r₀ : (ZMod l)ˣ, ∑ γ ∈ R,
    repM (topM l n m (N * N)) y (E r₀ γ) with hS2
  have hF : Fsum ε l n m N x c d w gm R z (i : ℚ) = (N : Ω) ^ 3 * ((l : Ω) ^ ((m + n) * w) * S1 + (l : Ω) ^ n * S2) := by
    unfold Fsum
    rw [if_pos (by simp)]
    congr 1
    simp only [hS1, hS2, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun r₀ _ => Finset.sum_congr rfl fun γ hγ => ?_
    have h1 := (hE r₀ γ hγ).2
    calc (ex l n w (gm r₀ * liftSL _ γ) : Ω) * repM (topM l n m (N * N)) y (EE ε l (m + n) N x c d (gm r₀ * liftSL _ γ) (i : ℚ))
        = repM (topM l n m (N * N)) y ((ex l n w (gm r₀ * liftSL _ γ) : Ω) * EE ε l (m + n) N x c d (gm r₀ * liftSL _ γ) (i : ℚ)) := by
          rw [map_mul, map_natCast]
      _ = _ := by rw [h1, map_add (f := _), map_mul, map_mul, map_pow, map_pow, map_natCast]
  have hS2Z : InZl ε l (m + n) S2 := isum _ _ fun y _ => isum _ _ fun r₀ _ => isum _ _ fun γ hγ => irep y _ (hE r₀ γ hγ).1
  have hE0 : InZl ε l (m + n) ((N : Ω) ^ 3 * S2) := imul _ _ iN3 hS2Z
  obtain ⟨E', hNT', hE'Z, -⟩ := GlobalTheory.T.exists_unique_normalizedCyclotomicTrace ε l (m + n) m hm (by omega) _ hE0
  obtain ⟨τ, hτ, hsum⟩ := hNT
  obtain ⟨τ', hτ', hsum'⟩ := hNT'
  rw [Nat.add_sub_cancel_left] at hsum hsum'
  have hkey := sum_key ε l N c d w gm hP x a₀ ha₀ m n hm R hR z τ hτ μ (fun Φ Ψ h => hμ c d gm hP n m hm Ω Φ Ψ h) i
  have hterm : ∀ a, τ a ((N : Ω) ^ 3 * ((l : Ω) ^ ((m + n) * w) * S1 + (l : Ω) ^ n * S2)) =
      (N : Ω) ^ 3 * (l : Ω) ^ ((m + n) * w) * τ a S1 + (l : Ω) ^ n * τ' a ((N : Ω) ^ 3 * S2) := by
    intro a
    rw [← IsNTr.apply_eq_of_mem_adjoin hE0.mem_adjoin ((hτ a).trans (hτ' a).symm)]
    simp only [map_mul, map_add (f := _), map_pow, map_natCast]
    ring
  have hB : (l : Ω) ^ (m + n) = (l : Ω) ^ n * (l : Ω) ^ m := by rw [add_comm, pow_add]
  have hln : (l : Ω) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hl.ne_zero)
  have hprim := (UpperTheory.isPrimitiveRoot_eOm_and_pow_compatible ε l N).1 (m + n)
  have hzm := (UpperTheory.isPrimitiveRoot_eOm_and_pow_compatible ε l N).2.2 m n
  have hl0 : (l : Ω) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  set T : Ω := ∑ a ∈ Finset.univ.filter (fun a : (ZMod (l ^ (m + n)))ˣ => (a : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]), τ a S1 with hT
  have key4 : (l : Ω) ^ n * F' = (N : Ω) ^ 3 * (l : Ω) ^ ((m + n) * w) * T + (l : Ω) ^ n * ((l : Ω) ^ n * E') := by
    have h1 : ∑ a ∈ Finset.univ.filter (fun a : (ZMod (l ^ (m + n)))ˣ => (a : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]),
        τ a ((N : Ω) ^ 3 * ((l : Ω) ^ ((m + n) * w) * S1 + (l : Ω) ^ n * S2)) =
        (N : Ω) ^ 3 * (l : Ω) ^ ((m + n) * w) * T + (l : Ω) ^ n * ∑ a ∈ Finset.univ.filter (fun a : (ZMod (l ^ (m + n)))ˣ => (a : ZMod (l ^ (m + n))).val ≡ 1 [MOD l ^ m]), τ' a ((N : Ω) ^ 3 * S2) := by
      rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    rw [hsum, hF, h1, ← hsum']
  set z₀ : ZMod (l ^ m) := (((z : ZMod (l ^ (m + n))).val : ℕ) : ZMod (l ^ m)) with hz₀
  have hcp : Nat.Coprime (l ^ (m + n)) N := Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hl).2 hP.cop)
  have htop : (l : ℤ) ^ n * (topT l (m + n) N : ℤ) ≡ t [ZMOD N] := by
    have h1 : (l : ZMod N) ^ (m + n) * (topT l (m + n) N : ZMod N) = 1 := by
      unfold topT
      rw [ZMod.natCast_zmod_val]
      have h := ZMod.coe_mul_inv_eq_one (l ^ (m + n)) hcp
      simpa using h
    have h2 : (l : ZMod N) ^ m * (t : ZMod N) = 1 := by
      have h := (ZMod.intCast_eq_intCast_iff _ _ N).2 ht
      push_cast at h
      exact h
    apply (ZMod.intCast_eq_intCast_iff _ _ N).1
    push_cast
    rw [pow_add] at h1
    linear_combination (-((l : ZMod N) ^ n * (topT l (m + n) N : ZMod N))) * h2 + (t : ZMod N) * h1
  have e1 : (l : ℤ) ^ n * ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ)) ≡ (x.val : ℤ) * a₀ * t [ZMOD N] := by
    have h := htop.mul_left ((x.val : ℤ) * a₀)
    rwa [show (x.val : ℤ) * a₀ * ((l : ℤ) ^ n * (topT l (m + n) N : ℤ)) = (l : ℤ) ^ n * ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ)) by ring] at h
  have e3 : (l : ℤ) ^ n * (a₀ * (topT l (m + n) N : ℤ)) ≡ a₀ * t [ZMOD N] := by
    have h := htop.mul_left a₀
    rwa [show a₀ * ((l : ℤ) ^ n * (topT l (m + n) N : ℤ)) = (l : ℤ) ^ n * (a₀ * (topT l (m + n) N : ℤ)) by ring] at h
  have e0 : (l : ℤ) ^ n * (0 : ℤ) ≡ 0 [ZMOD N] := by rw [mul_zero]
  have hnd : ∀ e : ℕ, Nat.Coprime e (6 * l * N) → ¬ (l : ℤ) ∣ (e : ℤ) := by
    intro e he h
    have h' : l ∣ e := Int.natCast_dvd_natCast.1 h
    have h2 : l ∣ Nat.gcd e (6 * l * N) := Nat.dvd_gcd h' ⟨6 * N, by ring⟩
    rw [he.gcd_eq_one] at h2
    exact hl.one_lt.ne' (Nat.dvd_one.1 h2)
  have down := UpperTheory.pieceT_level_raise_eq_vp l N m (w + 2) (c : ℤ) (d : ℤ) z₀ (NeZero.pos N) hP.cop hm (by omega) (hnd c hP.cc) (hnd d hP.dc) n ζ
    ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) ((x.val : ℤ) * a₀ * t, 0) (a₀ * t, 0)
    hprim e1 e0 e3 e0 (l ^ (m + n) * i)
  have hzm' : ζ ^ (l ^ n) = eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) := hzm
  have hζm1 : (ζ ^ (l ^ n)) ^ (N * l ^ m) = 1 := by
    rw [← pow_mul, show l ^ n * (N * l ^ m) = N * l ^ (m + n) by rw [pow_add]; ring]
    exact hprim.pow_eq_one
  have hunit : IsUnit z₀ := by
    have hd : l ^ m ∣ l ^ (m + n) := pow_dvd_pow l (by omega)
    have h := z.isUnit.map (ZMod.castHom hd (ZMod (l ^ m)))
    rwa [ZMod.castHom_apply, ← ZMod.natCast_val] at h
  have hβ' : (β : ZMod (l ^ m)) = z₀ := (ZMod.natCast_eq_natCast_iff _ _ _).2 hβ
  have beta := UpperTheory.pieceT_det_fiber_eq_pieceT_root_pow l N m (w + 2) (c : ℤ) (d : ℤ) ((x.val : ℤ) * a₀ * t) (a₀ * t) (ζ ^ (l ^ n)) β z₀ (NeZero.pos N) hm hζm1 hunit hβ' (l ^ m * i)
  have hvp : ∀ f : ℕ → Ω, vp (l ^ n) f (l ^ (m + n) * i) = f (l ^ m * i) := by
    intro f
    have hdiv : l ^ (m + n) * i = l ^ n * (l ^ m * i) := by rw [pow_add]; ring
    rw [hdiv]
    unfold vp
    rw [if_pos (dvd_mul_right _ _), Nat.mul_div_cancel_left _ (pow_pos hl.pos n)]
  rw [hvp] at down
  set Ks : Ω := ∑ γ ∈ ((unitSet l (m + n)).filter fun γ : GL (Fin 2) (ZMod (l ^ (m + n))) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))).det.val : ℕ) : ZMod (l ^ m)) = z₀),
    kg ζ l (m + n) N (c : ℤ) (d : ℤ) w ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) γ (l ^ (m + n) * i) with hKs
  have key2 : pieceT N l (m + n) m (w + 2) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ) ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) ζ ((unitSet l (m + n)).filter fun γ : GL (Fin 2) (ZMod (l ^ (m + n))) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))).det.val : ℕ) : ZMod (l ^ m)) = z₀) (l ^ (m + n) * i) =
      -((l : Ω) ^ (((m + n : ℕ) : ℤ) * ((w : ℤ) - 2))) * Ks :=
    UpperTheory.twistedEisensteinPiece_trivialCharacter_eq l N (m + n) m w (c : ℤ) (d : ℤ) ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) ζ z₀ hm (by omega) (l ^ (m + n) * i)
  have hk' : ((topMu l n m N : ℕ) : Ω) * T = (μ : Ω) * (Nat.totient (N * N) : Ω) * Ks := hkey
  have key1 : (l : Ω) ^ (m + n) * (N : Ω) ^ 2 * T = (μ : Ω) * (Nat.totient (N * N) : Ω) * Ks := by
    rw [← hk']; unfold topMu; push_cast; ring
  have key3 : (l : Ω) ^ (((m + n : ℕ) : ℤ) * ((w : ℤ) - 2)) * ((l : Ω) ^ (m + n)) ^ 2 = (l : Ω) ^ ((m + n) * w) := by
    rw [← pow_mul, ← zpow_natCast (l : Ω) ((m + n) * 2), ← zpow_add₀ hl0, ← zpow_natCast (l : Ω) ((m + n) * w)]
    congr 1
    push_cast
    ring
  refine ⟨E', hE'Z, ?_⟩
  have hQ : toQ (l ^ m) (pieceT N l m m (w + 2) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ) ((x.val : ℤ) * a₀ * t, 0) (a₀ * t, 0) (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β) ((unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i =
      pieceT N l (m + n) m (w + 2) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ) ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) ζ ((unitSet l (m + n)).filter fun γ : GL (Fin 2) (ZMod (l ^ (m + n))) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))).det.val : ℕ) : ZMod (l ^ m)) = z₀) (l ^ (m + n) * i) := by
    rw [down, beta, hzm']
    rfl
  rw [hQ]
  apply mul_left_cancel₀ hln
  push_cast
  linear_combination key4 - (N : Ω) * (Nat.totient (N * N) : Ω) * (μ : Ω) * (pieceT N l (m + n) m (w + 2) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ) ((x.val : ℤ) * a₀ * (topT l (m + n) N : ℤ), 0) (a₀ * (topT l (m + n) N : ℤ), 0) ζ ((unitSet l (m + n)).filter fun γ : GL (Fin 2) (ZMod (l ^ (m + n))) => (((γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ (m + n)))).det.val : ℕ) : ZMod (l ^ m)) = z₀) (l ^ (m + n) * i)) * hB +
    (N : Ω) * (Nat.totient (N * N) : Ω) * (μ : Ω) * (l : Ω) ^ (m + n) * key2 - (N : Ω) ^ 3 * T * key3 +
    (N : Ω) * (l : Ω) ^ (((m + n : ℕ) : ℤ) * ((w : ℤ) - 2)) * (l : Ω) ^ (m + n) * key1
