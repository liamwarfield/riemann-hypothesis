module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsValuationSubringGaussModularFunction
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerUnitsFiniteModPowersAtLevel
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonLthPowerReductionAlmostAllPrimes
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerIntegrality
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BinaryFormCoeffOfGamma1CapGamma0Invariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerMemAdjoinJOfSlTwoIntInvariant
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSomeLevelOverOfIntegralInvariant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelFunctionsIntermediateField
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GammaLeKer
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN.LevelGal

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def act (T : Tower Ω ε) : SL(2, ℤ) →* (T.K ≃ₐ[Ω] T.K) where
  toFun γ := T.sl (ofSL γ⁻¹)
  map_one' := by ext f; simp [T.sl_one]
  map_mul' γ δ := by
    ext f
    rw [AlgEquiv.mul_apply, mul_inv_rev, map_mul, T.sl_mul]

theorem act_apply (T : Tower Ω ε) (γ : SL(2, ℤ)) (f : T.K) : act T γ f = T.sl (ofSL γ⁻¹) f := rfl

theorem sl_fix (T : Tower Ω ε) (γ : SL(2, ℤ)) :
    ∀ x ∈ IntermediateField.adjoin Ω {T.jK}, T.sl (ofSL γ) x = x := by
  have hle : IntermediateField.adjoin Ω {T.jK} ≤ IntermediateField.fixedField (act T).range := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    rintro σ ⟨δ, rfl⟩
    exact T.j_inv _
  intro x hx
  have := (IntermediateField.mem_fixedField_iff _ _).1 (hle hx) (act T γ⁻¹) ⟨γ⁻¹, rfl⟩
  rwa [act_apply, inv_inv] at this

def lvl (T : Tower Ω ε) (M : ℕ) : IntermediateField (IntermediateField.adjoin Ω {T.jK}) T.K where
  carrier := {f | ∀ γ ∈ CongruenceSubgroup.Gamma M, T.sl (ofSL γ) f = f}
  mul_mem' {a b} ha hb γ hγ := by rw [map_mul, ha γ hγ, hb γ hγ]
  one_mem' γ _ := map_one _
  add_mem' {a b} ha hb γ hγ := by rw [map_add (f := _), ha γ hγ, hb γ hγ]
  zero_mem' γ _ := map_zero _
  algebraMap_mem' c γ _ := by
    rw [IntermediateField.algebraMap_apply]
    exact sl_fix T γ _ c.2
  inv_mem' x hx γ hγ := by rw [map_inv₀, hx γ hγ]

theorem act_mem_lvl (T : Tower Ω ε) (M : ℕ) (γ : SL(2, ℤ)) {f : T.K} (hf : f ∈ lvl T M) :
    act T γ f ∈ lvl T M := by
  intro δ hδ
  have hc : γ⁻¹ * δ * γ⁻¹⁻¹ ∈ CongruenceSubgroup.Gamma M :=
    (CongruenceSubgroup.Gamma_normal M).conj_mem δ hδ γ⁻¹
  have e : γ⁻¹ * δ = (γ⁻¹ * δ * γ⁻¹⁻¹) * γ⁻¹ := by group
  rw [act_apply, ← T.sl_mul, ← map_mul, e, map_mul, T.sl_mul, hf _ hc]

def rho (T : Tower Ω ε) (M : ℕ) :
    SL(2, ℤ) →* (lvl T M ≃ₐ[IntermediateField.adjoin Ω {T.jK}] lvl T M) where
  toFun γ :=
    { toFun := fun x => ⟨act T γ x, act_mem_lvl T M γ x.2⟩
      invFun := fun x => ⟨act T γ⁻¹ x, act_mem_lvl T M γ⁻¹ x.2⟩
      left_inv := fun x => Subtype.ext (by
        show act T γ⁻¹ (act T γ x) = x
        rw [← AlgEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one, AlgEquiv.one_apply])
      right_inv := fun x => Subtype.ext (by
        show act T γ (act T γ⁻¹ x) = x
        rw [← AlgEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, AlgEquiv.one_apply])
      map_mul' := fun x y => Subtype.ext (map_mul (act T γ) (x : T.K) y)
      map_add' := fun x y => Subtype.ext (map_add (act T γ) (x : T.K) y)
      commutes' := fun c => Subtype.ext (by
        show act T γ (c : T.K) = (c : T.K)
        rw [act_apply]
        exact sl_fix T _ _ c.2) }
  map_one' := AlgEquiv.ext fun x => Subtype.ext (by
    show act T 1 x = x
    rw [map_one, AlgEquiv.one_apply])
  map_mul' γ δ := AlgEquiv.ext fun x => Subtype.ext (by
    show act T (γ * δ) x = act T γ (act T δ x)
    rw [map_mul, AlgEquiv.mul_apply])

theorem rho_val (T : Tower Ω ε) (M : ℕ) (γ : SL(2, ℤ)) (x : lvl T M) :
    ((rho T M γ x : lvl T M) : T.K) = T.sl (ofSL γ⁻¹) x := rfl

theorem gamma_le_ker (T : Tower Ω ε) (M : ℕ) : CongruenceSubgroup.Gamma M ≤ (rho T M).ker := by
  intro γ hγ
  rw [MonoidHom.mem_ker]
  refine AlgEquiv.ext fun x => Subtype.ext ?_
  show T.sl (ofSL γ⁻¹) x = x
  exact x.2 _ (inv_mem hγ)

theorem finite_range (T : Tower Ω ε) (M : ℕ) (hM : 0 < M) : Finite (rho T M).range := by
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : (CongruenceSubgroup.Gamma M).FiniteIndex := by
    show (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M))).ker.FiniteIndex
    exact Subgroup.finiteIndex_ker _
  haveI : (rho T M).ker.FiniteIndex := Subgroup.finiteIndex_of_le (gamma_le_ker T M)
  exact Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange (rho T M)).toEquiv

end GlobalTheory.FN.LevelGal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelFunctionsIntermediateField
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

noncomputable section

namespace GlobalTheory.KZ.LevelField

theorem finiteDimensional_adjoin_restrict {F K : Type} [Field F] [Field K] [Algebra F K] (α : K)
    (L : IntermediateField (IntermediateField.adjoin F {α}) K)
    (hL : FiniteDimensional (IntermediateField.adjoin F {α}) L) (hα : α ∈ L.restrictScalars F) :
    FiniteDimensional (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) (L.restrictScalars F) := by
  letI : Algebra (IntermediateField.adjoin F {α}) (L.restrictScalars F) :=
    inferInstanceAs (Algebra (IntermediateField.adjoin F {α}) L)
  haveI : Module.Finite (IntermediateField.adjoin F {α}) (L.restrictScalars F) := hL
  have hmap : (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}).map (L.restrictScalars F).val =
      IntermediateField.adjoin F {α} := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  have hmem : ∀ c : IntermediateField.adjoin F {α},
      algebraMap (IntermediateField.adjoin F {α}) (L.restrictScalars F) c ∈
        IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)} := by
    intro c
    have hc : (c : K) ∈ (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}).map
        (L.restrictScalars F).val := by rw [hmap]; exact c.2
    obtain ⟨y, hy, hyc⟩ := (IntermediateField.mem_map _).1 hc
    have e : algebraMap (IntermediateField.adjoin F {α}) (L.restrictScalars F) c = y := Subtype.ext hyc.symm
    rw [e]
    exact hy
  letI : Algebra (IntermediateField.adjoin F {α}) (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) :=
    ((algebraMap (IntermediateField.adjoin F {α}) (L.restrictScalars F)).codRestrict
      (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) hmem).toAlgebra
  haveI : IsScalarTower (IntermediateField.adjoin F {α})
      (IntermediateField.adjoin F {(⟨α, hα⟩ : L.restrictScalars F)}) (L.restrictScalars F) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite (IntermediateField.adjoin F {α}) _ _


open GlobalTheory.FN.LevelGal in
theorem finiteDimensional_lvl {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) (M : ℕ) (hM : 0 < M) :
    FiniteDimensional (IntermediateField.adjoin Ω {X.jK}) (lvl X M) := by
  let H := (rho X M).range
  haveI : Finite H := finite_range X M hM
  have hbot : IntermediateField.fixedField H = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hxF : (x : X.K) ∈ IntermediateField.adjoin Ω {X.jK} := by
      refine LevelOneFrac.mem_adjoin_of_sl_inv ε X hj x fun γ => ?_
      have h1 := congrArg Subtype.val (hx (rho X M γ⁻¹) ⟨γ⁻¹, rfl⟩)
      rw [rho_val, inv_inv] at h1
      exact h1
    rw [IntermediateField.mem_bot]
    exact ⟨⟨x, hxF⟩, Subtype.ext rfl⟩
  haveI hfd0 : FiniteDimensional (IntermediateField.fixedField H) (lvl X M) :=
    (inferInstance : FiniteDimensional (FixedPoints.subfield H (lvl X M)) (lvl X M))
  have : FiniteDimensional (⊥ : IntermediateField (IntermediateField.adjoin Ω {X.jK}) (lvl X M)) (lvl X M) :=
    hbot ▸ hfd0
  exact Module.Finite.trans (⊥ : IntermediateField (IntermediateField.adjoin Ω {X.jK}) (lvl X M)) (lvl X M)

theorem exists_level_field : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ M : ℕ, 0 < M →
    ∃ L : IntermediateField Ω X.K, (∀ f : X.K, f ∈ L ↔ ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) ∧
      ∃ hj : X.jK ∈ L, FiniteDimensional (IntermediateField.adjoin Ω {(⟨X.jK, hj⟩ : L)}) L := by
  intro Ω _ _ _ ε X _ hj M hM
  have hjL : X.jK ∈ (GlobalTheory.FN.LevelGal.lvl X M).restrictScalars Ω := fun γ _ => X.j_inv γ
  exact ⟨(GlobalTheory.FN.LevelGal.lvl X M).restrictScalars Ω, fun f => Iff.rfl, hjL,
    finiteDimensional_adjoin_restrict X.jK _ (finiteDimensional_lvl ε X hj M hM) hjL⟩

end GlobalTheory.KZ.LevelField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelFunctionsIntermediateFieldStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelFunctions_intermediateField : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ M : ℕ, 0 < M → ∃ L : IntermediateField Ω X.K, (∀ f : X.K, f ∈ L ↔ ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) ∧ ∃ hj : X.jK ∈ L, FiniteDimensional (IntermediateField.adjoin Ω {(⟨X.jK, hj⟩ : L)}) L := by
  first | exact @GlobalTheory.KZ.LevelField.exists_level_field | exact GlobalTheory.KZ.LevelField.exists_level_field | (intros; apply GlobalTheory.KZ.LevelField.exists_level_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerHeckeProductInvariantPrincipalLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeProductInvariant
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.HeckeCosetLevel

lemma toGQ_val (m : Matrix (Fin 2) (Fin 2) ℤ) (h : 0 < m.det) :
    (((toGQ m : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = m.map (Int.castRingHom ℚ) := by
  simp [toGQ, h]

lemma ofSL_val (γ : SL(2, ℤ)) :
    (((ofSL γ : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) := by
  rfl

lemma toGQ_mul (A B : Matrix (Fin 2) (Fin 2) ℤ) (hA : 0 < A.det) (hB : 0 < B.det) :
    toGQ (A * B) = toGQ A * toGQ B := by
  have hAB : 0 < (A * B).det := by rw [Matrix.det_mul]; exact mul_pos hA hB
  apply Subtype.ext; apply Units.ext
  rw [toGQ_val _ hAB]
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [toGQ_val _ hA, toGQ_val _ hB, Matrix.map_mul]

lemma toGQ_SL (γ : SL(2, ℤ)) : toGQ (γ : Matrix (Fin 2) (Fin 2) ℤ) = ofSL γ := by
  apply Subtype.ext; apply Units.ext
  rw [toGQ_val _ (by simp), ofSL_val]

lemma mem_Gamma_of_mul (M q : ℕ) (hqM : Nat.Coprime q M) (N : SL(2, ℤ)) (B m : Matrix (Fin 2) (Fin 2) ℤ)
    (hm : (N : Matrix (Fin 2) (Fin 2) ℤ) * B = m)
    (b00 : (B 0 0 : ZMod M) = 1) (b01 : (B 0 1 : ZMod M) = 0) (b10 : (B 1 0 : ZMod M) = 0) (b11 : (B 1 1 : ZMod M) = q)
    (h00 : (m 0 0 : ZMod M) = 1) (h01 : (m 0 1 : ZMod M) = 0) (h10 : (m 1 0 : ZMod M) = 0) (h11 : (m 1 1 : ZMod M) = q) :
    N ∈ CongruenceSubgroup.Gamma M := by
  have hu : IsUnit (q : ZMod M) := by
    have := (ZMod.unitOfCoprime q hqM).isUnit
    rwa [ZMod.coe_unitOfCoprime] at this
  have e : ∀ i j, ((m i j : ℤ) : ZMod M) = ((N : Matrix (Fin 2) (Fin 2) ℤ) i 0 : ZMod M) * (B 0 j : ZMod M) +
      ((N : Matrix (Fin 2) (Fin 2) ℤ) i 1 : ZMod M) * (B 1 j : ZMod M) := by
    intro i j; rw [← hm]; simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  have e11 := e 1 1
  rw [b00, b10, h00] at e00
  rw [b01, b11, h01] at e01
  rw [b00, b10, h10] at e10
  rw [b01, b11, h11] at e11
  simp only [mul_one, mul_zero, add_zero, zero_add] at e00 e01 e10 e11
  refine CongruenceSubgroup.Gamma_mem.mpr ⟨e00.symm, ?_, e10.symm, ?_⟩
  · exact (hu.mul_left_eq_zero).mp e01.symm
  · exact hu.mul_right_cancel (by rw [one_mul]; exact e11.symm)

lemma sigma_diag_mod (M q : ℕ) (σ : SL(2, ℤ))
    (hσ : (en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) :
    let B := (σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1];
    (B 0 0 : ZMod M) = 1 ∧ (B 0 1 : ZMod M) = 0 ∧ (B 1 0 : ZMod M) = 0 ∧ (B 1 1 : ZMod M) = q := by
  intro B
  obtain ⟨s01, s10, s11⟩ := hσ
  have hd : (σ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := σ.2
  rw [Matrix.det_fin_two] at hd
  have hd' := congrArg (fun x : ℤ => (x : ZMod M)) hd
  simp only [en] at s01 s10 s11
  push_cast at hd'
  rw [s01, s10, s11] at hd'
  simp [B, Matrix.mul_apply, Fin.sum_univ_two, s01, s10, s11]
  linear_combination hd'

def reps (M q : ℕ) (σ : SL(2, ℤ)) (i : Fin (q + 1)) : Matrix (Fin 2) (Fin 2) ℤ :=
  if (i : ℕ) < q then !![1, ((i : ℕ) * M : ℤ); 0, (q : ℤ)] else (σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]

lemma reps_det (M q : ℕ) (σ : SL(2, ℤ)) (i : Fin (q + 1)) : (reps M q σ i).det = q := by
  unfold reps; split_ifs <;> simp [Matrix.det_fin_two]

theorem exists_coset (M q : ℕ) (hM : 0 < M) (hq : q.Prime) (hqM : Nat.Coprime q M) (σ : SL(2, ℤ))
    (hσ : (en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q)
    (m : Matrix (Fin 2) (Fin 2) ℤ) (hdet : m.det = q) (h00 : (m 0 0 : ZMod M) = 1) (h01 : (m 0 1 : ZMod M) = 0)
    (h10 : (m 1 0 : ZMod M) = 0) (h11 : (m 1 1 : ZMod M) = q) :
    (∃ j < q, ∃ γ ∈ CongruenceSubgroup.Gamma M, m = (γ : Matrix (Fin 2) (Fin 2) ℤ) * !![1, (j * M : ℤ); 0, (q : ℤ)]) ∨
      ∃ γ ∈ CongruenceSubgroup.Gamma M, m = (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) := by
  haveI := Fact.mk hq
  have hq0 : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne_zero
  rw [Matrix.det_fin_two] at hdet
  by_cases hdiv : (q : ℤ) ∣ m 0 0 ∧ (q : ℤ) ∣ m 1 0
  · right
    obtain ⟨⟨a', ha⟩, ⟨c', hc⟩⟩ := hdiv
    have hd1 : a' * m 1 1 - m 0 1 * c' = 1 := by
      apply mul_left_cancel₀ hq0
      rw [ha, hc] at hdet; linear_combination hdet
    have hσd : (σ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := σ.2
    let N0 : Matrix (Fin 2) (Fin 2) ℤ := !![a', m 0 1; c', m 1 1] * (σ : Matrix (Fin 2) (Fin 2) ℤ).adjugate
    have hN : N0.det = 1 := by
      simp only [N0, Matrix.det_mul, Matrix.det_adjugate, hσd, Matrix.det_fin_two_of]
      simp [hd1]
    let N : SL(2, ℤ) := ⟨N0, hN⟩
    have hNm : (N : Matrix (Fin 2) (Fin 2) ℤ) * ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1]) = m := by
      show N0 * _ = m
      simp only [N0]
      rw [← Matrix.mul_assoc, Matrix.mul_assoc _ (σ : Matrix (Fin 2) (Fin 2) ℤ).adjugate, Matrix.adjugate_mul, hσd, one_smul,
        Matrix.mul_one]
      ext i j; fin_cases i <;> fin_cases j <;> simp [ha, hc] <;> ring
    obtain ⟨b00, b01, b10, b11⟩ := sigma_diag_mod M q σ hσ
    exact ⟨N, mem_Gamma_of_mul M q hqM N _ m hNm b00 b01 b10 b11 h00 h01 h10 h11, hNm.symm⟩
  · left
    have hMq : ((M : ℕ) : ZMod q) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hq).mp hqM
    have hz : ∀ x : ℤ, (q : ℤ) ∣ x ↔ ((x : ℤ) : ZMod q) = 0 := fun x => (ZMod.intCast_zmod_eq_zero_iff_dvd x q).symm
    have hdz : ((m 0 0 : ℤ) : ZMod q) * (m 1 1 : ZMod q) - (m 0 1 : ZMod q) * (m 1 0 : ZMod q) = 0 := by
      have := congrArg (fun x : ℤ => (x : ZMod q)) hdet
      push_cast at this; rw [this]; exact ZMod.natCast_self q
    set a : ZMod q := ((m 0 0 : ℤ) : ZMod q) with ha
    set b : ZMod q := ((m 0 1 : ℤ) : ZMod q) with hb
    set c : ZMod q := ((m 1 0 : ℤ) : ZMod q) with hc
    set d : ZMod q := ((m 1 1 : ℤ) : ZMod q) with hd
    have hac : a ≠ 0 ∨ c ≠ 0 := by
      by_contra hcon; push_neg at hcon
      exact hdiv ⟨(hz _).mpr hcon.1, (hz _).mpr hcon.2⟩
    obtain ⟨t, ht1, ht2⟩ : ∃ t : ZMod q, b = a * t * (M : ZMod q) ∧ d = c * t * (M : ZMod q) := by
      rcases hac with ha0 | hc0
      · refine ⟨b / (a * (M : ZMod q)), ?_, ?_⟩
        · field_simp
        · field_simp; linear_combination hdz
      · by_cases ha0 : a = 0
        · refine ⟨d / (c * (M : ZMod q)), ?_, ?_⟩
          · rw [ha0] at hdz ⊢
            have : b * c = 0 := by linear_combination -hdz
            rcases mul_eq_zero.mp this with h | h
            · rw [h]; ring
            · exact absurd h hc0
          · field_simp
        · refine ⟨b / (a * (M : ZMod q)), ?_, ?_⟩
          · field_simp
          · field_simp; linear_combination hdz
    refine ⟨t.val, ZMod.val_lt t, ?_⟩
    have ht : ((t.val : ℤ) : ZMod q) = t := by simp
    obtain ⟨t1, e1⟩ : (q : ℤ) ∣ m 0 1 - m 0 0 * ((t.val : ℤ) * M) := by
      rw [hz]; push_cast; rw [ZMod.natCast_zmod_val, ← hb, ← ha, ht1]; ring
    obtain ⟨t2, e2⟩ : (q : ℤ) ∣ m 1 1 - m 1 0 * ((t.val : ℤ) * M) := by
      rw [hz]; push_cast; rw [ZMod.natCast_zmod_val, ← hd, ← hc, ht2]; ring
    have hd1 : m 0 0 * t2 - t1 * m 1 0 = 1 := by
      apply mul_left_cancel₀ hq0
      linear_combination hdet - m 0 0 * e2 + m 1 0 * e1
    let N : SL(2, ℤ) := ⟨!![m 0 0, t1; m 1 0, t2], by rw [Matrix.det_fin_two_of]; exact hd1⟩
    have hNm : (N : Matrix (Fin 2) (Fin 2) ℤ) * !![1, ((t.val : ℕ) * M : ℤ); 0, (q : ℤ)] = m := by
      show !![m 0 0, t1; m 1 0, t2] * _ = m
      ext i j; fin_cases i <;> fin_cases j <;> simp [-ZMod.natCast_val] <;> first | linear_combination -e1 | linear_combination -e2
    refine ⟨N, mem_Gamma_of_mul M q hqM N _ m hNm (by simp) (by simp) (by simp) (by simp) h00 h01 h10 h11, hNm.symm⟩

theorem reps_distinct (M q : ℕ) (hq : q.Prime) (hqM : Nat.Coprime q M) (σ : SL(2, ℤ)) (i k : Fin (q + 1))
    (g : SL(2, ℤ)) (h : reps M q σ i = (g : Matrix (Fin 2) (Fin 2) ℤ) * reps M q σ k) : i = k := by
  have hq1 : ¬ (q : ℤ) ∣ 1 := by
    intro h
    have := Int.natCast_dvd_natCast.mp (by exact_mod_cast h)
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  have E : ∀ a b, reps M q σ i a b = ((g : Matrix (Fin 2) (Fin 2) ℤ) * reps M q σ k) a b := fun a b => by rw [h]
  have e00 := E 0 0
  have e01 := E 0 1
  have e10 := E 1 0
  have e11 := E 1 1
  unfold reps at e00 e01 e10 e11
  by_cases hi : (i : ℕ) < q <;> by_cases hk : (k : ℕ) < q <;>
    simp only [hi, hk, if_true, if_false] at e00 e01 e10 e11 <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10 e11
  ·
    have hdv : (q : ℤ) ∣ ((i : ℕ) - (k : ℕ) : ℤ) * M := ⟨(g : Matrix (Fin 2) (Fin 2) ℤ) 0 1, by
      rw [← e00] at e01; linear_combination e01⟩
    have hcop : IsCoprime (q : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.mpr hqM
    have hdv' := hcop.dvd_of_dvd_mul_right hdv
    have h0 := Int.eq_zero_of_abs_lt_dvd hdv' (by rw [abs_lt]; constructor <;> omega)
    exact Fin.ext (by omega)
  ·
    exact absurd ⟨(g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0, by linear_combination e00⟩ hq1
  ·
    have hσd : (σ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := σ.2
    rw [Matrix.det_fin_two] at hσd
    apply absurd _ hq1
    exact ⟨(σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0, by
      linear_combination -hσd + (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * e11 - (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * e01 -
        ((k : ℕ) : ℤ) * (M : ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * e10 + ((k : ℕ) : ℤ) * (M : ℤ) * (σ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 * e00⟩
  · exact Fin.ext (by omega)

end GlobalTheory.HeckeCosetLevel

open GlobalTheory.HeckeCosetLevel in
theorem GlobalTheory.hecke_product_invariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (M q : ℕ) (f : X.K), 0 < M → q.Prime → Nat.Coprime q M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) → ∀ σ : SL(2, ℤ), ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) = (∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f := by
  intro Ω _ _ ε X M q f hM hq hqM hf σ hσ γ hγ
  have hprod : (∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) *
      X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f =
      ∏ i : Fin (q + 1), X.sl (toGQ (reps M q σ i)) f := by
    rw [Fin.prod_univ_castSucc, Finset.prod_range]
    simp [reps]
  rw [hprod, map_prod]
  obtain ⟨g00, g01, g10, g11⟩ := CongruenceSubgroup.Gamma_mem.mp hγ
  have hpos : ∀ i, 0 < (reps M q σ i).det := fun i => by rw [reps_det]; exact_mod_cast hq.pos
  have hrM : ∀ i, ((reps M q σ i) 0 0 : ZMod M) = 1 ∧ ((reps M q σ i) 0 1 : ZMod M) = 0 ∧
      ((reps M q σ i) 1 0 : ZMod M) = 0 ∧ ((reps M q σ i) 1 1 : ZMod M) = q := by
    intro i
    unfold reps
    split_ifs with hi
    · simp
    · obtain ⟨s01, s10, s11⟩ := hσ
      have hd : (σ : Matrix (Fin 2) (Fin 2) ℤ).det = 1 := σ.2
      rw [Matrix.det_fin_two] at hd
      have hd' := congrArg (fun x : ℤ => (x : ZMod M)) hd
      simp only [en] at s01 s10 s11
      push_cast at hd'
      rw [s01, s10, s11] at hd'
      simp [Matrix.mul_apply, Fin.sum_univ_two, s01, s10, s11]
      linear_combination hd'
  have key : ∀ i, ∃ k, ∃ g ∈ CongruenceSubgroup.Gamma M,
      reps M q σ i * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (g : Matrix (Fin 2) (Fin 2) ℤ) * reps M q σ k := by
    intro i
    obtain ⟨a00, a01, a10, a11⟩ := hrM i
    have hdet : (reps M q σ i * (γ : Matrix (Fin 2) (Fin 2) ℤ)).det = q := by
      rw [Matrix.det_mul, reps_det]; simp
    rcases exists_coset M q hM hq hqM σ hσ _ hdet
      (by simp [Matrix.mul_apply, Fin.sum_univ_two, a00, a01, g00, g10])
      (by simp [Matrix.mul_apply, Fin.sum_univ_two, a00, a01, g01, g11])
      (by simp [Matrix.mul_apply, Fin.sum_univ_two, a10, a11, g00, g10])
      (by simp [Matrix.mul_apply, Fin.sum_univ_two, a10, a11, g01, g11]) with ⟨j, hj, g, hg, h⟩ | ⟨g, hg, h⟩
    · refine ⟨⟨j, by omega⟩, g, hg, ?_⟩
      rw [h]; simp [reps, hj]
    · refine ⟨Fin.last q, g, hg, ?_⟩
      rw [h]; simp [reps]
  choose π g hg hπ using key
  have inj : Function.Injective π := by
    intro i j hij
    have h1 := hπ i
    have h2 := hπ j
    rw [hij] at h1
    apply reps_distinct M q hq hqM σ i j (g i * (g j)⁻¹)
    have hγi : (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hgj : ((g j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (((g j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
    have hgj' : (((g j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * ((g j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
    calc reps M q σ i = reps M q σ i * (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [Matrix.mul_assoc, hγi, Matrix.mul_one]
      _ = (g i : Matrix (Fin 2) (Fin 2) ℤ) * (((g j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) *
            ((g j : Matrix (Fin 2) (Fin 2) ℤ) * reps M q σ (π j)) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) := by
          rw [h1]; simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (((g j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (g j : Matrix (Fin 2) (Fin 2) ℤ), hgj', Matrix.one_mul]
      _ = ((g i * (g j)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * reps M q σ j := by
          rw [← h2, Matrix.SpecialLinearGroup.coe_mul]
          simp only [Matrix.mul_assoc, hγi, Matrix.mul_one]
  let e := Equiv.ofBijective π (Finite.injective_iff_bijective.mp inj)
  calc ∏ i : Fin (q + 1), X.sl (ofSL γ) (X.sl (toGQ (reps M q σ i)) f)
      = ∏ i : Fin (q + 1), X.sl (toGQ (reps M q σ (e i))) f := by
        refine Finset.prod_congr rfl (fun i _ => ?_)
        rw [← X.sl_mul, ← toGQ_SL γ, ← toGQ_mul _ _ (hpos i) (by simp), hπ i,
          toGQ_mul _ _ (by simp) (hpos _), toGQ_SL, X.sl_mul, hf _ (hg i)]
        rfl
    _ = ∏ i : Fin (q + 1), X.sl (toGQ (reps M q σ i)) f := Equiv.prod_comp e (fun i => X.sl (toGQ (reps M q σ i)) f)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerHeckeProductInvariantPrincipalLevel
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

theorem GlobalTheory.kronecker_product_level : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M q : ℕ) (σ : SL(2, ℤ)) (f : X.K), 0 < M → q.Prime → Nat.Coprime q M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) → ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) = ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) := by
  intro Ω _ _ ε X M q σ f hM hq hqM hf hσ γ hγ
  exact GlobalTheory.hecke_product_invariant ε X M q f hM hq hqM hf σ hσ γ hγ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.KroneckerHeckeProductInvariantPrincipalLevelStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kroneckerHeckeProduct_invariant_principal_level : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M q : ℕ) (σ : SL(2, ℤ)) (f : X.K), 0 < M → q.Prime → Nat.Coprime q M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) → ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) = ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) := by
  first | exact @GlobalTheory.kronecker_product_level | exact GlobalTheory.kronecker_product_level | (intros; apply GlobalTheory.kronecker_product_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerJInvariantTranscendental
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerJInvariantTranscendental
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem hahnSeries_order_eq_neg_one_of_coeff {Ω : Type} [Field Ω] {h : HahnSeries ℚ Ω}
    (h1 : h.coeff (-1) = 1) (h0 : ∀ r : ℚ, r < -1 → h.coeff r = 0) : h.order = -1 := by
  have h1' : h.coeff (-1) ≠ 0 := by rw [h1]; exact one_ne_zero
  have hne : h ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero h1'
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1') ?_
  exact le_of_not_gt fun hlt => hne (HahnSeries.coeff_order_eq_zero.mp (h0 _ hlt))

theorem hahnSeries_pow_order_of_order_neg_one {Ω : Type} [Field Ω] {h : HahnSeries ℚ Ω}
    (h1 : h.coeff (-1) = 1) (ho : h.order = -1) (n : ℕ) :
    (h ^ n).order = -(n : ℚ) ∧ (h ^ n).coeff (-(n : ℚ)) = 1 := by
  have hord : ∀ k : ℕ, (h ^ k).order = -(k : ℚ) := fun k => by
    rw [HahnSeries.order_pow, ho]
    simp
  refine ⟨hord n, ?_⟩
  induction n with
  | zero => simp
  | succ k ih =>

    have hm := HahnSeries.coeff_mul_order_add_order (h ^ k) h
    rw [HahnSeries.leadingCoeff_eq, HahnSeries.leadingCoeff_eq, hord k, ho, ih, h1, mul_one] at hm
    have e : -((k + 1 : ℕ) : ℚ) = -(k : ℚ) + -1 := by push_cast; ring
    rw [pow_succ, e, hm]

private theorem hahnSeries_coeff_algebra_smul {Ω : Type} [Field Ω] [Algebra ℚ Ω] (r : Ω) (y : HahnSeries ℚ Ω) (a : ℚ) :
    (@HSMul.hSMul Ω (HahnSeries ℚ Ω) (HahnSeries ℚ Ω) (@instHSMul _ _ Algebra.toSMul) r y).coeff a =
      r * y.coeff a := by
  rw [Algebra.smul_def, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self_apply,
    HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]

theorem Tower.jK_transcendental {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) :
    Transcendental Ω X.jK := by
  unfold Transcendental IsAlgebraic
  rintro ⟨p, hp0, hp⟩
  obtain ⟨h1, h0, -⟩ := X.j_exp
  have ho := hahnSeries_order_eq_neg_one_of_coeff h1 h0
  have hz : Polynomial.aeval (X.exp X.jK) p = 0 := by
    rw [Polynomial.aeval_algHom_apply, hp, map_zero]

  have hc : (Polynomial.aeval (X.exp X.jK) p).coeff (-(p.natDegree : ℚ)) = p.leadingCoeff := by
    rw [Polynomial.aeval_eq_sum_range, HahnSeries.coeff_sum, Finset.sum_eq_single p.natDegree]
    · rw [hahnSeries_coeff_algebra_smul, (hahnSeries_pow_order_of_order_neg_one h1 ho _).2, mul_one]
      rfl
    · intro i hi hne
      have hlt : i < p.natDegree := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hne
      have hlt' : (i : ℚ) < p.natDegree := by exact_mod_cast hlt
      rw [hahnSeries_coeff_algebra_smul, HahnSeries.coeff_eq_zero_of_lt_order, mul_zero]
      rw [(hahnSeries_pow_order_of_order_neg_one h1 ho i).1]
      linarith
    · intro hn
      exact absurd (Finset.self_mem_range_succ _) hn
  rw [hz, HahnSeries.coeff_zero] at hc
  exact hp0 (Polynomial.leadingCoeff_eq_zero.mp hc.symm)

end GlobalTheory.KZ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerJInvariantTranscendentalStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerJInvariant_transcendental : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε), Transcendental Ω X.jK := by
  first | exact @GlobalTheory.KZ.Tower.jK_transcendental | exact GlobalTheory.KZ.Tower.jK_transcendental | (intros; apply GlobalTheory.KZ.Tower.jK_transcendental <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRootOfUnityCloseOfPowReducesOne
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRootOfUnityCloseOfPowReducesOne
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

open Polynomial

theorem exists_root_of_unity_close_of_pow_close : ∀ {Ω K : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Field K]
    [Algebra Ω K] (W : ValuationSubring K) (x : K) (N : ℕ), 0 < N → W.valuation (x ^ N - 1) < 1 →
    ∃ ζ : Ω, ζ ^ N = 1 ∧ W.valuation (x - algebraMap Ω K ζ) < 1 := by
  intro Ω K _ _ _ _ _ W x N hN hv
  classical
  set p : Polynomial Ω := X ^ N - C 1 with hp
  have hm : p.Monic := monic_X_pow_sub_C 1 hN.ne'
  have hs := (IsAlgClosed.splits p).eq_prod_roots_of_monic hm
  have hx : x ^ N - 1 = (p.roots.map (fun a => x - algebraMap Ω K a)).prod := by
    have := congrArg (Polynomial.aeval x) hs
    simpa [p, map_multiset_prod, Multiset.map_map, Function.comp_def] using this
  by_contra hcon
  push_neg at hcon
  refine (not_lt.mpr ?_) hv
  rw [hx, map_multiset_prod, Multiset.map_map]
  refine Multiset.one_le_prod_of_one_le ?_
  intro y hy
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hy
  have ha' : a ^ N = 1 := by
    have := (mem_roots hm.ne_zero).mp ha
    simpa [p, sub_eq_zero] using this
  exact hcon a ha'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRootOfUnityCloseOfPowReducesOneStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rootOfUnity_close_of_pow_reduces_one : ∀ {Ω K : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Field K] [Algebra Ω K] (W : ValuationSubring K) (x : K) (N : ℕ), 0 < N → W.valuation (x ^ N - 1) < 1 → ∃ ζ : Ω, ζ ^ N = 1 ∧ W.valuation (x - algebraMap Ω K ζ) < 1 := by
  first | exact @GlobalTheory.exists_root_of_unity_close_of_pow_close | exact GlobalTheory.exists_root_of_unity_close_of_pow_close | (intros; apply GlobalTheory.exists_root_of_unity_close_of_pow_close <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerGaloisActionPreservesGammaLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerGaloisActionPreservesGammaLevel
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

theorem Tower.gal_level {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ)
    (s : Ω ≃ₐ[ℚ] Ω) (f : X.K) (hM : 0 < M) (hf : ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) :
    ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (X.gal s f) = X.gal s f := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : NeZero (M : Ω) := ⟨by exact_mod_cast hM.ne'⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic M Ω) (Polynomial.degree_cyclotomic_pos M Ω hM).ne'
  rw [Polynomial.isRoot_cyclotomic_iff] at hζ
  have hsζ : IsPrimitiveRoot (s ζ) M := hζ.map_of_injective s.injective
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hsζ.pow_eq_one
  intro γ hγ
  have hγ' := hγ
  rw [CongruenceSubgroup.Gamma_mem] at hγ'
  obtain ⟨-, h01, h10, -⟩ := hγ'
  have key := X.recip M f hM hf ζ hζ s (i : ℤ) (by rw [zpow_natCast, hi]) γ γ
    ⟨rfl, by simp [en, h01], by simp [en, h10], rfl⟩
  rw [hf γ hγ] at key
  exact key.symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerGaloisActionPreservesGammaLevelStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.towerGaloisAction_preserves_gammaLevel : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ) (s : Ω ≃ₐ[ℚ] Ω) (f : X.K), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) → ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (X.gal s f) = X.gal s f := by
  first | exact @GlobalTheory.Tower.gal_level | exact GlobalTheory.Tower.gal_level | (intros; apply GlobalTheory.Tower.gal_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraKummerModularUnit
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.ESFun

theorem val_lt_one_iff {F : Type} [Field F] (A : ValuationSubring F) (x : F) :
    A.valuation x < 1 ↔ x = 0 ∨ ¬ A.valuation x⁻¹ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · have h0 : 0 < A.valuation x := by
      rw [zero_lt_iff]; simpa using hx
    rw [map_inv₀, inv_le_one₀ h0]; simp [hx]

theorem val_eq_one_iff {F : Type} [Field F] (A : ValuationSubring F) (x : F) :
    A.valuation x = 1 ↔ x ≠ 0 ∧ A.valuation x ≤ 1 ∧ A.valuation x⁻¹ ≤ 1 := by
  by_cases hx : x = 0
  · simp [hx]
  · have h0 : 0 < A.valuation x := by
      rw [zero_lt_iff]; simpa using hx
    rw [map_inv₀, inv_le_one₀ h0]; simp only [ne_eq, hx, not_false_eq_true, true_and]
    exact le_antisymm_iff

theorem comap_le_one {L K : Type} [Field L] [Field K] (φ : L →+* K) (W : ValuationSubring K) (x : L) :
    (W.comap φ).valuation x ≤ 1 ↔ W.valuation (φ x) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff, ValuationSubring.mem_comap]

theorem comap_lt_one {L K : Type} [Field L] [Field K] (φ : L →+* K) (W : ValuationSubring K) (x : L) :
    (W.comap φ).valuation x < 1 ↔ W.valuation (φ x) < 1 := by
  rw [val_lt_one_iff, val_lt_one_iff, comap_le_one, map_inv₀, map_eq_zero]

theorem comap_eq_one {L K : Type} [Field L] [Field K] (φ : L →+* K) (W : ValuationSubring K) (x : L) :
    (W.comap φ).valuation x = 1 ↔ W.valuation (φ x) = 1 := by
  rw [val_eq_one_iff, val_eq_one_iff, comap_le_one, comap_le_one, map_inv₀, ne_eq, ne_eq, map_eq_zero]

theorem frob_symm {Ω : Type} [Field Ω] [Algebra ℚ Ω] (q : ℕ) (hq : 0 < q) (s : Ω ≃ₐ[ℚ] Ω)
    (V : ValuationSubring Ω) (hs : ∀ x ∈ V, s x ∈ V ∧ V.valuation (s x - x ^ q) < 1) :
    ∀ x ∈ V, s.symm x ∈ V := by
  intro x hx
  by_contra hy
  have hy0 : s.symm x ≠ 0 := by intro h; apply hy; rw [h]; exact V.zero_mem
  have h1 : ¬ V.valuation (s.symm x) ≤ 1 := by rwa [V.valuation_le_one_iff]
  have hpos : 0 < V.valuation (s.symm x) := by rw [zero_lt_iff]; simpa using hy0
  have hyinv : V.valuation (s.symm x)⁻¹ < 1 := by
    rw [map_inv₀, inv_lt_one₀ hpos]; exact not_le.1 h1
  have hyV : (s.symm x)⁻¹ ∈ V := (V.valuation_le_one_iff _).1 hyinv.le
  obtain ⟨_, h2⟩ := hs _ hyV
  have h3 : V.valuation ((s.symm x)⁻¹ ^ q) < 1 := by
    rw [map_pow]; exact pow_lt_one₀ zero_le' hyinv hq.ne'
  have h4 : V.valuation (s (s.symm x)⁻¹) < 1 := by
    have e : s (s.symm x)⁻¹ = (s (s.symm x)⁻¹ - (s.symm x)⁻¹ ^ q) + (s.symm x)⁻¹ ^ q := by ring
    rw [e]; exact Valuation.map_add_lt _ h2 h3
  rw [map_inv₀, AlgEquiv.apply_symm_apply, map_inv₀] at h4
  have hx0 : x ≠ 0 := by intro h; apply hy0; simp [h]
  have hxpos : 0 < V.valuation x := by rw [zero_lt_iff]; simpa using hx0
  rw [inv_lt_one₀ hxpos] at h4
  exact absurd ((V.valuation_le_one_iff _).2 hx) (not_le.2 h4)

theorem lev_sl {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ) (σ : SL(2, ℤ)) (f : X.K)
    (hf : ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) :
    ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (X.sl (ofSL σ) f) = X.sl (ofSL σ) f := by
  intro γ hγ
  have hn : σ * γ * σ⁻¹ ∈ CongruenceSubgroup.Gamma M := (CongruenceSubgroup.Gamma_normal M).conj_mem γ hγ σ
  have e : σ * γ = (σ * γ * σ⁻¹) * σ := by group
  rw [← X.sl_mul, ← map_mul, e, map_mul, X.sl_mul, hf _ hn]

end GlobalTheory.KZ.ESFun

namespace GlobalTheory.KZ.ESFun
theorem levKron : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M q : ℕ) (σ : SL(2, ℤ)) (f : X.K), 0 < M → q.Prime → Nat.Coprime q M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) → ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) = ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) f) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) f) := GlobalTheory.T.kroneckerHeckeProduct_invariant_principal_level
theorem levGal : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (M : ℕ) (s : Ω ≃ₐ[ℚ] Ω) (f : X.K), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) → ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (X.gal s f) = X.gal s f := GlobalTheory.T.towerGaloisAction_preserves_gammaLevel
theorem unMap : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (m : ℕ) (f : X.Kˣ), f ∈ X.Un m → (∀ (g : GQ) (u : X.Kˣ), (u : X.K) = X.sl g (f : X.K) → u ∈ X.Un m) ∧ ∀ (s : Ω ≃ₐ[ℚ] Ω) (u : X.Kˣ), (u : X.K) = X.gal s (f : X.K) → u ∈ X.Un m := GlobalTheory.T.modularFunctionTower_unitGroup_stable_slash_galois
theorem red1 : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (M : ℕ) (f : X.Kˣ), 0 < M → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (f : X.K) = f) → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ (V : ValuationSubring Ω) (s : Ω ≃ₐ[ℚ] Ω), ((q : ℕ) : Ω) ∈ V.nonunits → (∀ x ∈ V, s x ∈ V ∧ s.symm x ∈ V ∧ V.valuation (s x - x ^ q) < 1) → ∀ σ : SL(2, ℤ), ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∀ W : ValuationSubring X.K, (∀ a : Ω, algebraMap Ω X.K a ∈ W ↔ a ∈ V) → (∀ g : X.K, (∀ r, (X.exp g).coeff r ∈ V) → (∀ r, r ≠ 0 → (X.exp g).coeff r ∈ V.nonunits) → W.valuation (g - algebraMap Ω X.K ((X.exp g).coeff 0)) < 1) → ∃ κ : Ω, κ ≠ 0 ∧ W.valuation (algebraMap Ω X.K κ * ((∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) (f : X.K)) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K)) / (X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q) - 1) < 1 := GlobalTheory.T.kroneckerRatio_reduces_to_const_mod_valuation
theorem finLev : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ M : ℕ, 0 < M → ∃ L : IntermediateField Ω X.K, (∀ f : X.K, f ∈ L ↔ ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) f = f) ∧ ∃ hj : X.jK ∈ L, FiniteDimensional (IntermediateField.adjoin Ω {(⟨X.jK, hj⟩ : L)}) L := GlobalTheory.T.exists_levelFunctions_intermediateField
theorem jTr : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε), Transcendental Ω X.jK := GlobalTheory.T.towerJInvariant_transcendental
theorem rootLift : ∀ {Ω K : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Field K] [Algebra Ω K] (W : ValuationSubring K) (x : K) (N : ℕ), 0 < N → W.valuation (x ^ N - 1) < 1 → ∃ ζ : Ω, ζ ^ N = 1 ∧ W.valuation (x - algebraMap Ω K ζ) < 1 := GlobalTheory.T.exists_rootOfUnity_close_of_pow_reduces_one
end GlobalTheory.KZ.ESFun

namespace GlobalTheory.KZ.ESFun

theorem prod_mem_Un {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (m : ℕ) {ι : Type}
    (t : Finset ι) (u : ι → X.Kˣ) (h : ∀ i ∈ t, u i ∈ X.Un m) : (∏ i ∈ t, u i) ∈ X.Un m := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using UnClosure.one_mem X m
  | insert a t ha ih =>
    rw [Finset.prod_insert ha]
    exact UnClosure.mul_mem X m _ _ (h a (by simp)) (ih fun i hi => h i (by simp [hi]))

theorem eichler_shimura_kummer : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l : ℕ) [Fact l.Prime] (M n : ℕ) (f : X.Kˣ), 0 < M → l ∣ M → f ∈ X.Un (l ^ n) → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (f : X.K) = f) → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ s : Ω ≃ₐ[ℚ] Ω, FrobAt q s → ∀ σ : SL(2, ℤ), ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∃ g : X.Kˣ, (∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) (f : X.K)) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) = X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q * (g : X.K) ^ (l ^ n) := by
  intro Ω _ _ _ ε X hε hj l hl M n f hM hlM hfU hfM
  classical
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : @Algebra.IsAlgebraic ℚ Ω _ _ DivisionRing.toRatAlgebra := by
    convert (IsAlgClosure.isAlgebraic : Algebra.IsAlgebraic ℚ Ω)
    exact Subsingleton.elim _ _
  have hl' : l.Prime := hl.out
  have hlpos : 0 < l := hl'.pos
  obtain ⟨L, hL, hjL, hfd⟩ := finLev ε X hε hj M hM
  have htr : Transcendental Ω (⟨X.jK, hjL⟩ : L) := by
    intro halg
    exact jTr X (by simpa using halg.algHom L.val)
  obtain ⟨R, hR⟩ := GlobalTheory.T.modularTower_units_finite_mod_powers_at_level ε X hε hj M (l ^ n) hM (pow_pos hlpos n)
  have key : ∀ r : X.Kˣ, ∃ S : Finset ℕ, (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (r : X.K) = r) →
      (¬ ∃ c : Ω, c ≠ 0 ∧ ∃ u : X.Kˣ, (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (u : X.K) = u) ∧
        (r : X.K) = algebraMap Ω X.K c * (u : X.K) ^ (l ^ n)) →
      ∀ q : ℕ, q.Prime → q ∉ S → ∀ V : ValuationSubring Ω, ((q : ℕ) : Ω) ∈ V.nonunits →
      ∀ W : ValuationSubring X.K, (∀ a : Ω, algebraMap Ω X.K a ∈ W ↔ a ∈ V) →
      (∀ P : Polynomial Ω, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) →
        W.valuation (Polynomial.aeval X.jK P) = 1) →
      ∀ h : X.K, h ∈ L → h ≠ 0 → ∀ C : Ω, C ≠ 0 →
        ¬ W.valuation (algebraMap Ω X.K C * (r : X.K) * h ^ (l ^ n) - 1) < 1 := by
    intro r
    by_cases hr : (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (r : X.K) = r) ∧
        ¬ ∃ c : Ω, c ≠ 0 ∧ ∃ u : X.Kˣ, (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (u : X.K) = u) ∧
          (r : X.K) = algebraMap Ω X.K c * (u : X.K) ^ (l ^ n)
    swap
    · exact ⟨∅, fun h1 h2 => absurd ⟨h1, h2⟩ hr⟩
    obtain ⟨hrM, hng⟩ := hr
    have hrL : (r : X.K) ∈ L := (hL _).2 hrM
    let Pa : ℕ → Prop := fun a => ∃ c : Ω, c ≠ 0 ∧ ∃ z : L, z ≠ 0 ∧
      (r : X.K) = algebraMap Ω X.K c * ((z : L) : X.K) ^ (l ^ a)
    have hP0 : Pa 0 := ⟨1, one_ne_zero, ⟨r, hrL⟩, by
        intro h; exact r.ne_zero (by simpa using congrArg Subtype.val h), by simp⟩
    have hPa : Pa (Nat.findGreatest Pa n) := Nat.findGreatest_spec (Nat.zero_le n) hP0
    have han : Nat.findGreatest Pa n ≤ n := Nat.findGreatest_le n
    have hmax : ¬ Pa (Nat.findGreatest Pa n + 1) ∨ n < Nat.findGreatest Pa n + 1 := by
      by_cases h : Nat.findGreatest Pa n + 1 ≤ n
      · exact Or.inl (Nat.findGreatest_is_greatest (Nat.lt_succ_self _) h)
      · exact Or.inr (by omega)
    generalize Nat.findGreatest Pa n = a at hPa han hmax
    obtain ⟨c1, hc1, z, hz, hrz⟩ := hPa
    have hlt : a < n := by
      rcases lt_or_eq_of_le han with h | h
      · exact h
      · exfalso; apply hng
        refine ⟨c1, hc1, Units.mk0 ((z : L) : X.K) (by simpa using hz), ?_, ?_⟩
        · exact (hL _).1 z.2
        · rw [← h]; simpa using hrz
    have hzl : ∀ u : L, u ^ l ≠ z := by
      intro u hu
      have hu0 : u ≠ 0 := by
        rintro rfl; exact hz (by rw [← hu, zero_pow hl'.ne_zero])
      have hPa1 : Pa (a + 1) := ⟨c1, hc1, u, hu0, by
        rw [hrz, ← hu]; push_cast; rw [← pow_mul, pow_succ, mul_comm l]⟩
      rcases hmax with h | h
      · exact h hPa1
      · omega
    obtain ⟨S, hS⟩ := GlobalTheory.T.nonLthPower_reduction_almost_all_primes (F := Ω) (K := L) (⟨X.jK, hjL⟩ : L) htr hfd l hl' z hzl
    refine ⟨S, fun _ _ q hq hqS V hqV W hWa hWb h hhL hh0 C hC hv => ?_⟩
    obtain ⟨k, hk⟩ : ∃ k, n = a + k + 1 := ⟨n - a - 1, by omega⟩
    have e1 : l ^ n = l ^ (k + 1) * l ^ a := by rw [← pow_add]; congr 1; omega
    let φ : L →+* X.K := algebraMap L X.K
    have hWLa : ∀ b : Ω, algebraMap Ω L b ∈ W.comap φ ↔ b ∈ V := fun b => by
      rw [ValuationSubring.mem_comap]; exact hWa b
    have hWLb : ∀ P : Polynomial Ω, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ∈ V ∧ P.coeff i ≠ 0 ∧ (P.coeff i)⁻¹ ∈ V) →
        (W.comap φ).valuation (Polynomial.aeval (⟨X.jK, hjL⟩ : L) P) = 1 := by
      intro P h1 h2
      rw [comap_eq_one]
      have e2 : φ (Polynomial.aeval (⟨X.jK, hjL⟩ : L) P) = Polynomial.aeval X.jK P := by
        have := Polynomial.aeval_algHom_apply L.val (⟨X.jK, hjL⟩ : L) P
        show ((Polynomial.aeval (⟨X.jK, hjL⟩ : L) P : L) : X.K) = _
        simpa using this.symm
      rw [e2]; exact hWb P h1 h2
    obtain ⟨e, he⟩ := IsAlgClosed.exists_pow_nat_eq (C * c1) (pow_pos hlpos a)
    have hx : W.valuation ((algebraMap Ω X.K e * ((z : L) : X.K) * h ^ (l ^ (k + 1))) ^ (l ^ a) - 1) < 1 := by
      have e3 : (algebraMap Ω X.K e * ((z : L) : X.K) * h ^ (l ^ (k + 1))) ^ (l ^ a)
          = algebraMap Ω X.K C * (r : X.K) * h ^ (l ^ n) := by
        rw [e1, hrz, mul_pow, mul_pow, ← map_pow, he, ← pow_mul, map_mul]; ring
      rw [e3]; exact hv
    obtain ⟨ζ, hζ, hv2⟩ := rootLift (Ω := Ω) W _ (l ^ a) (pow_pos hlpos a) hx
    obtain ⟨e₁, he₁⟩ := IsAlgClosed.exists_pow_nat_eq e hlpos
    have he₁0 : e₁ ≠ 0 := by
      rintro rfl
      rw [zero_pow hl'.ne_zero] at he₁
      rw [← he₁, zero_pow (pow_pos hlpos a).ne'] at he
      exact mul_ne_zero hC hc1 he.symm
    let H : L := ⟨algebraMap Ω X.K e₁ * h ^ (l ^ k), L.mul_mem (L.algebraMap_mem e₁) (pow_mem hhL _)⟩
    have hH0 : H ≠ 0 := by
      intro h0
      have := congrArg Subtype.val h0
      simp only [H, IntermediateField.coe_zero] at this
      rcases mul_eq_zero.1 this with h5 | h5
      · exact he₁0 (by simpa using h5)
      · exact hh0 (pow_eq_zero_iff (pow_pos hlpos k).ne' |>.1 h5)
    have hζ1 : V.valuation ζ = 1 :=
      UnClosure.val_eq_one_of_pow V ζ (l ^ a) (pow_pos hlpos a) (by rw [hζ, map_one])
    have hζ0 : ζ ≠ 0 := by
      rintro rfl; rw [zero_pow (pow_pos hlpos a).ne'] at hζ; exact zero_ne_one hζ
    have hζV : ζ ∈ V := (V.valuation_le_one_iff _).1 hζ1.le
    have hζV' : ζ⁻¹ ∈ V := (V.valuation_le_one_iff _).1 (by rw [map_inv₀, hζ1, inv_one])
    apply hS q hq hqS V hqV (W.comap φ) ⟨hWLa, fun P h1 h2 => hWLb P h1 (by obtain ⟨i, hi⟩ := h2; exact ⟨i, by tauto⟩)⟩ H ζ hH0 hζ0 hζV hζV'
    rw [comap_lt_one]
    convert hv2 using 2
    simp only [φ, H, map_sub, map_mul, map_pow]
    show ((z : L) : X.K) * (algebraMap Ω X.K e₁ * h ^ (l ^ k)) ^ l - algebraMap Ω X.K ζ = _
    rw [mul_pow, ← map_pow, he₁, ← pow_mul, ← pow_succ]; ring
  choose Sr hSr using key
  obtain ⟨SE, hSE⟩ := red1 ε X hε hj M f hM hfM
  refine ⟨SE ∪ M.primeFactors ∪ R.biUnion Sr, ?_⟩
  intro q hq hqS s hs σ hσ
  simp only [Finset.mem_union, Finset.mem_biUnion, not_or, not_exists, not_and] at hqS
  obtain ⟨⟨hqE, hqM⟩, hqR⟩ := hqS
  have hcop : Nat.Coprime q M := by
    rw [Nat.Prime.coprime_iff_not_dvd hq]
    intro hd; exact hqM (Nat.mem_primeFactors.2 ⟨hq, hd, hM.ne'⟩)
  obtain ⟨V, hqV, hsV⟩ := hs
  have hsymm := frob_symm q hq.pos s V hsV
  have hV' : ∀ x ∈ V, s x ∈ V ∧ s.symm x ∈ V ∧ V.valuation (s x - x ^ q) < 1 :=
    fun x hx => ⟨(hsV x hx).1, hsymm x hx, (hsV x hx).2⟩
  obtain ⟨W, hWa, hWb, hWc⟩ := GlobalTheory.T.exists_valuationSubring_gauss_modularFunction ε X hε hj q hq V hqV
  obtain ⟨κ, hκ, hred⟩ := hSE q hq hqE V s hqV hV' σ hσ W hWa hWc
  have hU := unMap ε X hε hj (l ^ n) f hfU
  have hne : ∀ g : GQ, X.sl g (f : X.K) ≠ 0 := fun g => (map_ne_zero (X.sl g)).2 f.ne_zero
  have hσU : Units.mk0 _ (hne (ofSL σ)) ∈ X.Un (l ^ n) := hU.1 _ _ rfl
  have hne2 : X.gal s.symm (X.sl (ofSL σ) (f : X.K)) ≠ 0 := (map_ne_zero (X.gal s.symm)).2 (hne _)
  have hne3 : X.gal s (f : X.K) ≠ 0 := (map_ne_zero (X.gal s)).2 f.ne_zero
  let PU : X.Kˣ := (∏ j ∈ Finset.range q, Units.mk0 _ (hne (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]))) *
    Units.mk0 _ (hne (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])))
  let BU : X.Kˣ := Units.mk0 _ hne3 * (Units.mk0 _ hne2) ^ q
  have hPU : PU ∈ X.Un (l ^ n) :=
    UnClosure.mul_mem X _ _ _ (prod_mem_Un X _ _ _ fun j _ => hU.1 _ _ rfl) (hU.1 _ _ rfl)
  have hBU : BU ∈ X.Un (l ^ n) :=
    UnClosure.mul_mem X _ _ _ (hU.2 _ _ rfl)
      (UnClosure.pow_mem X _ _ _ ((unMap ε X hε hj (l ^ n) _ hσU).2 s.symm _ rfl))
  have hPv : (PU : X.K) = (∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) (f : X.K)) *
      X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) := by
    simp only [PU, Units.val_mul, Units.coe_prod, Units.val_mk0]
  have hBv : (BU : X.K) = X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q := by
    simp only [BU, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0]
  let rU : X.Kˣ := PU * BU⁻¹
  have hrUn : rU ∈ X.Un (l ^ n) := UnClosure.mul_mem X _ _ _ hPU (UnClosure.inv_mem X _ _ hBU)
  have hrv : (rU : X.K) = (PU : X.K) / (BU : X.K) := by
    simp only [rU, Units.val_mul, Units.val_inv_eq_inv_val, div_eq_mul_inv]
  have hrM : ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (rU : X.K) = rU := by
    intro γ hγ
    rw [hrv, hPv, hBv, map_div₀, levKron X M q σ (f : X.K) hM hq hcop hfM hσ γ hγ, map_mul, map_pow,
      levGal X M s (f : X.K) hM hfM γ hγ, levGal X M s.symm _ hM (lev_sl X M σ _ hfM) γ hγ]
  obtain ⟨r0, hr0R, g, hgM, c, hc, hrep⟩ := hR rU hrUn hrM
  have hr0M : ∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (r0 : X.K) = r0 := by
    intro γ hγ
    have e : (r0 : X.K) = (rU : X.K) / ((g : X.K) ^ (l ^ n) * algebraMap Ω X.K c) := by
      have hc0 : algebraMap Ω X.K c ≠ 0 := by simpa using hc
      rw [hrep, mul_assoc, mul_div_assoc, div_self (mul_ne_zero (pow_ne_zero _ g.ne_zero) hc0), mul_one]
    rw [e, map_div₀, map_mul, map_pow, AlgEquiv.commutes, hrM γ hγ, hgM γ hγ]
  have hB0 : (BU : X.K) ≠ 0 := BU.ne_zero
  by_cases hgood : ∃ c' : Ω, c' ≠ 0 ∧ ∃ u : X.Kˣ, (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (u : X.K) = u) ∧
      (r0 : X.K) = algebraMap Ω X.K c' * (u : X.K) ^ (l ^ n)
  · obtain ⟨c', hc', u, -, hr0u⟩ := hgood
    obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq (c' * c) (pow_pos hlpos n)
    have hd0 : d ≠ 0 := by
      rintro rfl; rw [zero_pow (pow_pos hlpos n).ne'] at hd; exact mul_ne_zero hc' hc hd.symm
    refine ⟨Units.mk0 (algebraMap Ω X.K d * (u : X.K) * (g : X.K))
      (mul_ne_zero (mul_ne_zero (by simpa using hd0) u.ne_zero) g.ne_zero), ?_⟩
    rw [← hPv, ← hBv]
    calc (PU : X.K) = (BU : X.K) * ((PU : X.K) / (BU : X.K)) := (mul_div_cancel₀ _ hB0).symm
      _ = _ := by
        rw [← hrv, hrep, hr0u, Units.val_mk0, mul_pow, mul_pow, ← map_pow, hd, map_mul]; ring
  · exfalso
    refine hSr r0 hr0M hgood q hq (hqR r0 hr0R) V hqV W hWa (fun P h1 h2 => hWb P h1 (by obtain ⟨i, hi⟩ := h2; exact ⟨i, by tauto⟩)) (g : X.K) ((hL _).2 hgM) g.ne_zero (κ * c)
      (mul_ne_zero hκ hc) ?_
    have e : algebraMap Ω X.K (κ * c) * (r0 : X.K) * (g : X.K) ^ (l ^ n) =
        algebraMap Ω X.K κ * ((PU : X.K) / (BU : X.K)) := by
      rw [← hrv, hrep, map_mul]; ring
    rw [e, hPv, hBv, ← mul_div_assoc]
    exact hred

end GlobalTheory.KZ.ESFun
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.EichlerShimuraKummerModularUnitStatement
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eichlerShimura_kummer_modularUnit : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (l : ℕ) [Fact l.Prime] (M n : ℕ) (f : X.Kˣ), 0 < M → l ∣ M → f ∈ X.Un (l ^ n) → (∀ γ ∈ CongruenceSubgroup.Gamma M, X.sl (ofSL γ) (f : X.K) = f) → ∃ S : Finset ℕ, ∀ q : ℕ, q.Prime → q ∉ S → ∀ s : Ω ≃ₐ[ℚ] Ω, FrobAt q s → ∀ σ : SL(2, ℤ), ((en σ 0 1 : ZMod M) = 0 ∧ (en σ 1 0 : ZMod M) = 0 ∧ (en σ 1 1 : ZMod M) = q) → ∃ g : X.Kˣ, (∏ j ∈ Finset.range q, X.sl (toGQ !![1, (j * M : ℤ); 0, (q : ℤ)]) (f : X.K)) * X.sl (toGQ ((σ : Matrix (Fin 2) (Fin 2) ℤ) * !![(q : ℤ), 0; 0, 1])) (f : X.K) = X.gal s (f : X.K) * (X.gal s.symm (X.sl (ofSL σ) (f : X.K))) ^ q * (g : X.K) ^ (l ^ n) := by
  first | exact @GlobalTheory.KZ.ESFun.eichler_shimura_kummer | exact GlobalTheory.KZ.ESFun.eichler_shimura_kummer | (intros; apply GlobalTheory.KZ.ESFun.eichler_shimura_kummer <;> assumption)
end
