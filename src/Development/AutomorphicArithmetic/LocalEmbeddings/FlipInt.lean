module

public import Development.AutomorphicArithmetic.DivisorFrames.IntegralMemAddSubgroupOfRamifiedTwistedInvariant
public import Development.AutomorphicArithmetic.DivisorFrames.IsIntegralUnitCharOfConductorLe
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitThetaGridIsAdmissibleFlipTensor

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.ExistsMemKOEqStdFrameMulOfIsPrimFrame
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

theorem UpperTheory.exists_mem_KO_eq_stdFrame_mul_of_isPrimFrame :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A A' D : Type} [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] (σ : A ⊕ A' ≃ D) (X : Matrix A D k), IsPrimFrame (stdLat k D) X → ∃ u ∈ KO k D, X = X0 k σ * (invT u).val := by
  intro k _ _ _ _ A A' D _ _ _ _ _ _ σ X hX
  obtain ⟨R, hR, hXR⟩ := GlobalTheory.PrimFrameMove.exists_rightInverse hX
  let X' : Matrix A D 𝒪[k] := Matrix.of fun i j => ⟨X i j, mem_matLat_stdLat.1 hX.2.1 i j⟩
  let R' : Matrix D A 𝒪[k] := Matrix.of fun i j => ⟨R i j, hR i j⟩
  have h1 : X' * R' = 1 := by
    apply Matrix.map_injective (f := algebraMap 𝒪[k] k) Subtype.val_injective
    show (X' * R').map (algebraMap 𝒪[k] k) = (1 : Matrix A A 𝒪[k]).map (algebraMap 𝒪[k] k)
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact hXR
  let ρ := IsLocalRing.residue 𝒪[k]
  have h2 : X'.map ρ * R'.map ρ = 1 := by
    rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have h3 : (X'.map ρ).rank = Fintype.card A := by
    refine le_antisymm (Matrix.rank_le_card_height _) ?_
    have := Matrix.rank_mul_le_left (X'.map ρ) (R'.map ρ)
    rwa [h2, Matrix.rank_one] at this
  obtain ⟨h, hh⟩ := (rank_eq_card_iff_exists_frameMatrixFirstColumnBlock σ _).1 h3
  choose l hl using IsLocalRing.residue_surjective (R := 𝒪[k])
  let C : Matrix D D 𝒪[k] := Matrix.of fun r j =>
    Sum.elim (fun i => X' i j) (fun i => l ((invT h).val (σ (Sum.inr i)) j)) (σ.symm r)
  have h4 : ρ.mapMatrix C = (invT h).val := by
    ext r j
    obtain ⟨i | i, rfl⟩ := σ.surjective r
    · have := congrFun (congrFun hh i) j
      rw [frameMatrixFirstColumnBlock_mul_apply] at this
      simpa [C] using this
    · simp [C, ρ, hl]
  have hK : IsUnit C := by
    rw [Matrix.isUnit_iff_isUnit_det, ← IsLocalRing.residue_ne_zero_iff_isUnit, RingHom.map_det]
    rw [show (IsLocalRing.residue 𝒪[k]).mapMatrix C = _ from h4]
    exact (invT h).det_ne_zero
  obtain ⟨w, hw⟩ := hK
  refine ⟨invT (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) w), invT_mem_KO ⟨w, rfl⟩, ?_⟩
  rw [invT_invT]
  ext i j
  rw [frameMatrixFirstColumnBlock_mul_apply]
  show _ = ((w.val (σ (Sum.inl i)) j : 𝒪[k]) : k)
  rw [hw]
  simp [C, X']
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.FourierSumBlockTransposeInvEq
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

namespace UpperTheory.FourierBlockTranspose

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

set_option synthInstance.maxHeartbeats 200000 in
private theorem mk_eq_iff {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) (a b : 𝒪[k]) :
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal 𝒪[k] ^ e) a = Ideal.Quotient.mk _ b) ↔
      (((ϖ ^ e)⁻¹ : kˣ) : k) * ((a : k) - b) ∈ 𝒪[k] := by
  rw [Ideal.Quotient.eq, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  have hϖ0 : (ϖ : k) ≠ 0 := ϖ.ne_zero
  constructor
  · rintro ⟨c, hc⟩
    have hc' : (c : k) * (ϖ : k) ^ e = (a : k) - b := by
      simpa using congrArg Subtype.val hc
    rw [← hc', Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    have : ((ϖ : k) ^ e)⁻¹ * ((c : k) * (ϖ : k) ^ e) = c := by
      field_simp
    rw [this]
    exact c.2
  · intro h
    refine ⟨⟨_, h⟩, ?_⟩
    apply Subtype.ext
    simp only [MulMemClass.coe_mul, SubmonoidClass.coe_pow, AddSubgroupClass.coe_sub,
      Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    field_simp

private theorem mul_mem_int {A C B : Type} [Fintype C] {X : Matrix A C k} {Y : Matrix C B k}
    (hX : ∀ i j, X i j ∈ 𝒪[k]) (hY : ∀ i j, Y i j ∈ 𝒪[k]) (i : A) (j : B) : (X * Y) i j ∈ 𝒪[k] := by
  rw [Matrix.mul_apply]
  exact sum_mem fun c _ => mul_mem (hX i c) (hY c j)

private theorem sum_res_mul_left {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (ϖ : kˣ) (e : ℕ) (hϖ : IsUnif ϖ) (f : Matrix A B k → ℂ)
    (hf : ∀ Z Z' : Matrix A B k, (∀ i j, Z' i j ∈ 𝒪[k]) → f (Z + Z') = f Z)
    (M : GL A k) (hM : M ∈ KO k A) :
    ∑ S : A → B → Res (k := k) e, f (M.val * ((ϖ ^ e)⁻¹ • liftRes S)) =
      ∑ S : A → B → Res (k := k) e, f ((ϖ ^ e)⁻¹ • liftRes S) := by
  obtain ⟨hMi, hMinv⟩ := (mem_KO_iff M).1 hM
  have hint : ∀ (S : A → B → Res (k := k) e) (i : A) (j : B), (M.val * liftRes S) i j ∈ 𝒪[k] :=
    fun S i j => mul_mem_int hMi (liftRes_mem S) i j
  let σ : (A → B → Res (k := k) e) → (A → B → Res (k := k) e) := fun S i j =>
    Ideal.Quotient.mk _ ⟨(M.val * liftRes S) i j, hint S i j⟩
  have hclose : ∀ (S : A → B → Res (k := k) e) (i : A) (j : B),
      (((ϖ ^ e)⁻¹ : kˣ) : k) * (liftRes (σ S) i j - (M.val * liftRes S) i j) ∈ 𝒪[k] := by
    intro S i j
    have h := (mk_eq_iff hϖ e (Quotient.out (σ S i j)) ⟨_, hint S i j⟩).1
      (by rw [Ideal.Quotient.mk_out])
    simpa [liftRes] using h
  have hinj : Function.Injective σ := by
    intro S S' h
    funext i j
    have hd : ∀ a b, ((((ϖ ^ e)⁻¹ : kˣ) : k) • (M.val * (liftRes S - liftRes S'))) a b ∈ 𝒪[k] := by
      intro a b
      have h1 := (mk_eq_iff hϖ e _ _).1 (congrFun (congrFun h a) b)
      simpa [Matrix.mul_sub, Matrix.sub_apply, Matrix.smul_apply] using h1
    have h2 := mul_mem_int hMinv hd i j
    rw [Matrix.mul_smul, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h2
    have h3 := (mk_eq_iff hϖ e (Quotient.out (S i j)) (Quotient.out (S' i j))).2
      (by simpa [liftRes, Matrix.sub_apply, Matrix.smul_apply] using h2)
    rwa [Ideal.Quotient.mk_out, Ideal.Quotient.mk_out] at h3
  refine Fintype.sum_bijective σ (Finite.injective_iff_bijective.1 hinj) _ _ ?_
  intro S
  have hsplit : (ϖ ^ e)⁻¹ • liftRes (σ S) = M.val * ((ϖ ^ e)⁻¹ • liftRes S) +
      ((ϖ ^ e)⁻¹ • liftRes (σ S) - M.val * ((ϖ ^ e)⁻¹ • liftRes S)) := by abel
  rw [hsplit, hf]
  intro i j
  rw [Matrix.mul_smul]
  simp only [Units.smul_def, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, ← mul_sub]
  exact hclose S i j

end UpperTheory.FourierBlockTranspose

open UpperTheory.FourierBlockTranspose in
theorem UpperTheory.fourierSum_block_transpose_inv_eq :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A D₁ D₂ : Type} [Fintype A] [DecidableEq A] [Fintype D₁] [DecidableEq D₁] [Fintype D₂] [DecidableEq D₂] (ψ : AddChar k Circle) (ϖ : kˣ) (e : ℕ), IsUnif ϖ → HasConductor ψ 1 → ∀ Φ : Matrix A (D₁ ⊕ D₂) k → ℂ, IsNatDatum ϖ e Φ → ∀ u ∈ KO k A, ∀ Y : Matrix A (D₁ ⊕ D₂) k, fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) (fun Z => Φ (fromCols (u.valᵀ * Z.toCols₁) ((u⁻¹).val * Z.toCols₂))) Y = fourierSum ψ ϖ e (Assignment.one.block D₁ D₂) Φ ((u⁻¹).val * Y) := by
  intro k _ _ _ _ A D₁ D₂ _ _ _ _ _ _ ψ ϖ e hϖ hψ Φ hΦ u hu Y
  obtain ⟨huI, huinvI⟩ := (mem_KO_iff u).1 hu
  have hmulcond : ∀ g : Matrix A A k, (∀ i j, g i j ∈ 𝒪[k]) → ∀ Z : Matrix A (D₁ ⊕ D₂) k,
      (∀ i, ∀ j ∈ Assignment.one.block D₁ D₂, ((ϖ ^ e : kˣ) : k) * Z i j ∈ 𝒪[k]) →
      (∀ i, ∀ j ∈ Assignment.one.block D₁ D₂, ((ϖ ^ e : kˣ) : k) * (g * Z) i j ∈ 𝒪[k]) := by
    intro g hg Z hZ i j hj
    have h := mul_mem_int hg
      (Y := Matrix.of fun (a : A) (b : Assignment.one.block D₁ D₂) => ((ϖ ^ e : kˣ) : k) * Z a b)
      (fun a b => hZ a b b.2) i ⟨j, hj⟩
    rw [Matrix.mul_apply] at h
    rw [Matrix.mul_apply, Finset.mul_sum]
    convert h using 2 with l
    simp only [Matrix.of_apply]
    ring
  have hcond : (∀ i, ∀ j ∈ Assignment.one.block D₁ D₂, ((ϖ ^ e : kˣ) : k) * Y i j ∈ 𝒪[k]) ↔
      (∀ i, ∀ j ∈ Assignment.one.block D₁ D₂, ((ϖ ^ e : kˣ) : k) * ((u⁻¹).val * Y) i j ∈ 𝒪[k]) := by
    constructor
    · exact hmulcond _ huinvI Y
    · intro h
      have h2 := hmulcond _ huI _ h
      rwa [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul] at h2
  rw [fourierSum_apply, fourierSum_apply]
  by_cases hc : ∀ i, ∀ j ∈ Assignment.one.block D₁ D₂, ((ϖ ^ e : kˣ) : k) * Y i j ∈ 𝒪[k]
  swap
  · rw [if_neg hc, if_neg (mt hcond.2 hc)]
  rw [if_pos hc, if_pos (hcond.1 hc)]
  have hc' := hcond.1 hc
  congr 1
  have hψ1 : ∀ y : k, y ∈ 𝒪[k] → ψ y = 1 := by
    intro y hy
    have h := (hψ (1 : k)).2 (by simp)
    apply h
    rw [map_one]
    exact (Valuation.mem_integer_iff _ _).1 hy
  have hmat : ∀ L : Matrix A (Assignment.one.block D₁ D₂) k,
      fromCols (u.valᵀ * (setCols (Assignment.one.block D₁ D₂) Y L).toCols₁)
        ((u⁻¹).val * (setCols (Assignment.one.block D₁ D₂) Y L).toCols₂) =
      setCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) (u.valᵀ * L) := by
    intro L
    ext i j
    rcases j with d | d
    · simp [setCols, Assignment.block, Matrix.mul_apply]
      rfl
    · simp [setCols, Assignment.block, Matrix.mul_apply]
  have hpair : ∀ L : Matrix A (Assignment.one.block D₁ D₂) k,
      pairCols (Assignment.one.block D₁ D₂) Y L =
        pairCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) (u.valᵀ * L) := by
    intro L
    rw [pairCols_eq_trace, pairCols_eq_trace]
    have hs : ((u⁻¹).val * Y).submatrix id Subtype.val =
        (u⁻¹).val * Y.submatrix id (Subtype.val : Assignment.one.block D₁ D₂ → D₁ ⊕ D₂) := by
      ext i j
      simp [Matrix.mul_apply]
    rw [hs, Matrix.transpose_mul, ← Matrix.mul_assoc,
      Matrix.trace_mul_comm (u.valᵀ * L * (Y.submatrix id Subtype.val)ᵀ),
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.transpose_mul, Units.mul_inv,
      Matrix.transpose_one, Matrix.one_mul]
  let f : Matrix A (Assignment.one.block D₁ D₂) k → ℂ := fun W =>
    Φ (setCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • W)) *
      (ψ (pairCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • W)) : ℂ)
  have hΦ' : HasDepth ϖ e (stdLat k (D₁ ⊕ D₂)) Φ := hΦ
  obtain ⟨_, hΦinv⟩ := hΦ'
  have hf : ∀ Z Z' : Matrix A (Assignment.one.block D₁ D₂) k, (∀ i j, Z' i j ∈ 𝒪[k]) → f (Z + Z') = f Z := by
    intro Z Z' hZ'
    simp only [f]
    rw [smul_add]
    have hset : setCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • Z + (ϖ ^ e) • Z') =
        setCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • Z) +
          setCols (Assignment.one.block D₁ D₂) 0 ((ϖ ^ e) • Z') := by
      ext i j
      simp only [setCols, Matrix.of_apply, Matrix.add_apply]
      split_ifs <;> simp
    have hlat : setCols (Assignment.one.block D₁ D₂) 0 ((ϖ ^ e) • Z') ∈
        matLat A (ϖ ^ e • stdLat k (D₁ ⊕ D₂)) := by
      rw [FourierDepth.mem_matLat_smul_stdLat]
      intro i j
      simp only [setCols, Matrix.of_apply]
      split_ifs with h
      · rw [Matrix.smul_apply, Units.smul_def, smul_eq_mul, map_mul]
        exact mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (hZ' i ⟨j, h⟩))
      · simp
    have hpadd : pairCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • Z + (ϖ ^ e) • Z') =
        pairCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • Z) +
          pairCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • Z') := by
      simp only [pairCols, Matrix.add_apply, add_mul, Finset.sum_add_distrib]
    have hmemb : pairCols (Assignment.one.block D₁ D₂) ((u⁻¹).val * Y) ((ϖ ^ e) • Z') ∈ 𝒪[k] := by
      simp only [pairCols]
      refine sum_mem fun i _ => sum_mem fun j _ => ?_
      rw [Matrix.smul_apply, Units.smul_def, smul_eq_mul, mul_comm ((ϖ ^ e : kˣ) : k) _, mul_assoc]
      exact mul_mem (hZ' i j) (hc' i j j.2)
    rw [hset, hΦinv _ _ hlat, hpadd, AddChar.map_add_eq_mul, hψ1 _ hmemb, mul_one]
  have key := sum_res_mul_left ϖ e hϖ f hf (invT u⁻¹) (invT_mem_KO (inv_mem hu))
  calc _ = ∑ T : A → Assignment.one.block D₁ D₂ → Res (k := k) e,
        f ((invT u⁻¹).val * ((ϖ ^ e)⁻¹ • liftRes T)) := by
        refine Finset.sum_congr rfl fun T _ => ?_
        simp only [f]
        rw [invT_val, inv_inv, Matrix.mul_smul, smul_inv_smul, ← hmat, ← hpair]
    _ = ∑ T : A → Assignment.one.block D₁ D₂ → Res (k := k) e, f ((ϖ ^ e)⁻¹ • liftRes T) := key
    _ = _ := by
        refine Finset.sum_congr rfl fun T _ => ?_
        simp only [f, smul_inv_smul]
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.HaarVolSelfEqOneOfOpenSubgroupLeKO
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix

theorem UpperTheory.haarVol_self_eq_one_of_openSubgroup_le_KO :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] (J : Subgroup (GL n k)), IsOpen (J : Set (GL n k)) → J ≤ KO k n → haarVol (J.map invT) (J : Set (GL n k)) = 1 := by
  intro k _ _ _ _ _ _ n _ _ J hJ hJK
  have hc : Continuous (invT : GL n k →* GL n k) := by
    rw [Units.continuous_iff]
    constructor
    · exact (Units.continuous_coe_inv).matrix_transpose
    · exact (Units.continuous_val).matrix_transpose
  let e : GL n k ≃* GL n k :=
    { toFun := invT, invFun := invT, left_inv := invT_invT, right_inv := invT_invT,
      map_mul' := invT.map_mul }
  have hec : Continuous e := hc
  have hes : Continuous e.symm := hc
  have hem : Measurable e := hec.measurable
  haveI : (Measure.map e (Measure.haar : Measure (GL n k))).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map _ e hec hes
  have hKOpre : e ⁻¹' (KO k n : Set (GL n k)) = KO k n := by
    ext g
    constructor
    · intro hg
      have := invT_mem_KO (k := k) (g := invT g) hg
      rwa [invT_invT] at this
    · intro hg
      exact invT_mem_KO hg
  have hJpre : e ⁻¹' ((J.map invT : Subgroup (GL n k)) : Set (GL n k)) = J := by
    ext g
    simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, hxg⟩
      have hxg' : invT x = invT g := hxg
      have : x = g := by
        have h2 := congrArg invT hxg'
        rwa [invT_invT, invT_invT] at h2
      exact this ▸ hx
    · intro hg
      exact ⟨g, hg, rfl⟩
  obtain ⟨hA0, hAt⟩ := haar_ne_zero_ne_top (Measure.haar : Measure (GL n k)) (isOpen_KO (k := k) (n := n)) le_rfl
  set A := (Measure.haar : Measure (GL n k)) (KO k n) with hA
  have hmapKO : Measure.map e (Measure.haar : Measure (GL n k)) (KO k n) = A := by
    rw [Measure.map_apply hem isOpen_KO.measurableSet, hKOpre]
  have hinv0 : A⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hAt
  have hinvt : A⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hA0
  haveI : (A⁻¹ • Measure.map e (Measure.haar : Measure (GL n k))).IsHaarMeasure :=
    Measure.IsHaarMeasure.smul (μ := _) hinv0 hinvt
  haveI : (A⁻¹ • (Measure.haar : Measure (GL n k))).IsHaarMeasure :=
    Measure.IsHaarMeasure.smul (μ := _) hinv0 hinvt
  have h1 := eq_haarVol (A⁻¹ • Measure.map e (Measure.haar : Measure (GL n k))) (isOpen_KO (k := k) (n := n)) le_rfl
    (by rw [Measure.smul_apply, hmapKO, smul_eq_mul, ENNReal.inv_mul_cancel hA0 hAt])
  have h2 := eq_haarVol (A⁻¹ • (Measure.haar : Measure (GL n k))) (isOpen_KO (k := k) (n := n)) le_rfl
    (by rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hA0 hAt])
  have hmap : Measure.map e (Measure.haar : Measure (GL n k)) = Measure.haar := by
    have h3 := h1.trans h2.symm
    ext s hs
    have h4 := congrArg (fun μ : Measure (GL n k) => A • μ s) h3
    simp only [Measure.smul_apply, smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel hA0 hAt, one_mul] at h4
    exact h4
  have hJ' := (isOpen_map_invT hJ hJK).1
  have heq : (Measure.haar : Measure (GL n k)) ((J.map invT : Subgroup (GL n k)) : Set (GL n k)) =
      (Measure.haar : Measure (GL n k)) J := by
    rw [← hmap, Measure.map_apply hem hJ'.measurableSet, hJpre]
    rw [hmap]
  obtain ⟨hJ0, hJt⟩ := haar_ne_zero_ne_top (Measure.haar : Measure (GL n k)) hJ hJK
  unfold haarVol
  rw [Measure.smul_apply, smul_eq_mul, heq, ENNReal.inv_mul_cancel hJ0 hJt]
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.NuDetMulSliceBBlockAction
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip
open scoped Pointwise

private theorem not_touch_inner {γ : List Edge} {i j : ℕ} (hγ : IsPath γ) (hθ : Edge.theta i j ∈ γ)
    (hx : Edge.ex i j ∈ γ) {b : Edge} (hb : b ∈ γ) (h1 : b ≠ .theta i j) (h2 : b ≠ .ex i j) :
    b.src ≠ (i, j) ∧ b.tgt ≠ (i, j) := by
  refine ⟨fun hs => h2 (hγ.eq_of_vertexDiff_eq hb hx (by rw [hs])), fun ht => h1 ?_⟩
  have h3 := vertexDiff_tgt b
  have h4 := vertexDiff_tgt (.theta i j)
  rw [ht] at h3
  exact hγ.eq_of_vertexDiff_eq hb hθ (by simp only [Edge.tgt] at h4; omega)

private theorem nodup_of_isPath {γ : List Edge} (hγ : IsPath γ) : γ.Nodup :=
  hγ.pairwise_vertexDiff.imp fun {a b} h hab => by subst hab; exact lt_irrefl _ h

theorem UpperTheory.nu_det_mul_sliceB_block_action :
    ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {G : Grid k} (ϖ : kˣ) (e : ℕ) (St : G.PiLocalization₂) (i j : ℕ), PassesThrough i j St.path → St.IsAdmissible .one ϖ e → ∀ u ∈ St.level (i, j), ∀ (x : G.Args) (Z : Matrix (Fin (G.rank (i, j))) (G.Cols i j) k), (G.nu i j (gdet u⁻¹) : ℂ) * G.sliceB i j St.tensor x (fromCols (u.valᵀ * Z.toCols₁) ((u⁻¹).val * Z.toCols₂)) = G.sliceB i j St.tensor x Z := by
  intro k _ _ _ _ G ϖ e St i j hpt hadm u hu x Z
  obtain ⟨γ, J, T⟩ := St
  obtain ⟨hpath, hlev, htens, hinv⟩ := hadm
  simp only at hpt hlev hpath htens hinv hu ⊢
  have hθ : Edge.theta i j ∈ γ := hpt.subset (by simp)
  have hx : Edge.ex i j ∈ γ := hpt.subset (by simp)
  have hnt := fun b hb h1 h2 => not_touch_inner (b := b) hpath hθ hx hb h1 h2
  have hnd := nodup_of_isPath hpath
  obtain ⟨l₁, l₂, hγ⟩ := hpt
  have hin : (i, j) ∈ innerVertices γ := by
    subst hγ
    refine List.mem_map.2 ⟨.ex i j, ?_, rfl⟩
    cases l₁ <;> simp
  have huK : u ∈ KO k _ := (hlev _ hin).2 hu
  have h := congrFun (hinv _ hin u hu)
    (Function.update (Function.update x (.theta i j) Z.toCols₁) (.ex i j) Z.toCols₂ᵀ)
  set g : G.VertexGroup := Pi.mulSingle (i, j) u with hg
  have hg0 : g (i, j) = u := Pi.mulSingle_eq_same _ _
  have hg1 : ∀ Y, Y ≠ (i, j) → g Y = 1 := fun Y hY => Pi.mulSingle_eq_of_ne hY _
  have hoff : ∀ b ∈ γ, b ≠ .theta i j → b ≠ .ex i j → G.edgeFactor .one g b = 1 := fun b hb h1 h2 => by
    simp [Grid.edgeFactor, hg1 _ (hnt b hb h1 h2).1, hg1 _ (hnt b hb h1 h2).2]
  have ha : ∀ z : ℂ, apow (gdet (Assignment.one.read u)) z = 1 := fun z =>
    apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (Assignment.one.read_mem_KO huK)) z
  have hsq : G.edgeFactor .one g (.theta i j) * G.edgeFactor .one g (.ex i j) = (G.nu i j (gdet u⁻¹) : ℂ) := by
    have e1 : g (i, j + 1) = 1 := hg1 _ (by simp)
    have e2 : g (i + 1, j) = 1 := hg1 _ (by simp)
    simp only [Grid.edgeFactor, Edge.src, Edge.tgt, hg0, e1, e2, ha, map_one, apow_one, mul_one]
    simp only [Grid.kappa, Grid.blockChar, Grid.nu, gdet, map_one, map_inv, MonoidHom.div_apply,
      Units.val_div_eq_div_val, Units.val_inv_eq_inv_val, Units.val_one, inv_one, mul_one, one_mul]
    field_simp
  have hprod : (γ.map (G.edgeFactor .one g)).prod = (G.nu i j (gdet u⁻¹) : ℂ) := by
    have p : ∀ l : List Edge, (∀ b ∈ l, b ∈ γ ∧ b ≠ .theta i j ∧ b ≠ .ex i j) →
        (l.map (G.edgeFactor .one g)).prod = 1 := fun l hl => List.prod_eq_one fun c hc => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hc
      exact hoff b (hl b hb).1 (hl b hb).2.1 (hl b hb).2.2
    subst hγ
    have q₁ := p l₁ fun b hb => ⟨by simp [hb], by
      rintro rfl; exact (List.nodup_append.1 (List.nodup_append.1 hnd).1).2.2 _ hb _ (by simp) rfl, by
      rintro rfl; exact (List.nodup_append.1 (List.nodup_append.1 hnd).1).2.2 _ hb _ (by simp) rfl⟩
    have q₂ := p l₂ fun b hb => ⟨by simp [hb], by
      rintro rfl; exact (List.nodup_append.1 hnd).2.2 _ (by simp) _ hb rfl, by
      rintro rfl; exact (List.nodup_append.1 hnd).2.2 _ (by simp) _ hb rfl⟩
    simp only [List.map_append, List.prod_append, q₁, q₂, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, one_mul, hsq]
  rw [Grid.pathAct, hprod] at h
  simp only [Grid.sliceB]
  rw [← h]
  congr 1
  refine htens.1 fun b hb => ?_
  have hne : Edge.theta i j ≠ Edge.ex i j := by simp
  by_cases hb2 : b = .ex i j
  · subst hb2
    simp only [Function.update_self, Grid.moveArgs, Assignment.read, invT_inv_val, hg0, invT_val]
    simp [hg1 (i + 1, j) (by simp), Matrix.transpose_mul]
  · by_cases hb1 : b = .theta i j
    · subst hb1
      simp only [Function.update_of_ne hne, Function.update_self, Grid.moveArgs, Assignment.read, invT_inv_val, hg0]
      simp [hg1 (i, j + 1) (by simp)]
    · simp [Grid.moveArgs, Function.update_of_ne hb1, Function.update_of_ne hb2,
        hg1 _ (hnt b hb hb1 hb2).1, hg1 _ (hnt b hb hb1 hb2).2]
end

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix

noncomputable section

namespace UpperTheory.FlipInt

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise

def Lo (q n : ℕ) : AddSubgroup ℂ where
  carrier := {z | IsIntegral ℤ ((q : ℂ) ^ n * z)}
  add_mem' ha hb := by
    simp only [Set.mem_setOf_eq, mul_add] at *
    exact ha.add hb
  zero_mem' := by simpa using isIntegral_zero
  neg_mem' ha := by
    simp only [Set.mem_setOf_eq, mul_neg] at *
    exact ha.neg

theorem mem_Lo {q n : ℕ} {z : ℂ} : z ∈ Lo q n ↔ IsIntegral ℤ ((q : ℂ) ^ n * z) := Iff.rfl

theorem Lo_zero {q : ℕ} {z : ℂ} (h : IsIntegral ℤ z) : z ∈ Lo q 0 := by simpa [mem_Lo] using h

theorem Lo_mul {q a b : ℕ} {x y : ℂ} (hx : x ∈ Lo q a) (hy : y ∈ Lo q b) : x * y ∈ Lo q (a + b) := by
  rw [mem_Lo] at *
  have := hx.mul hy
  rwa [show (q : ℂ) ^ a * x * ((q : ℂ) ^ b * y) = (q : ℂ) ^ (a + b) * (x * y) by ring] at this

theorem Lo_mono {q a b : ℕ} {x : ℂ} (hx : x ∈ Lo q a) (h : a ≤ b) : x ∈ Lo q b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [mem_Lo] at *
  have h1 : IsIntegral ℤ ((q : ℂ) ^ c) := by
    have : IsIntegral ℤ (q : ℂ) := by simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (q : ℤ))
    exact this.pow c
  have := h1.mul hx
  rwa [show (q : ℂ) ^ c * ((q : ℂ) ^ a * x) = (q : ℂ) ^ (a + c) * x by ring] at this

theorem Lo_pow {q a : ℕ} {x : ℂ} (hx : x ∈ Lo q a) : ∀ n : ℕ, x ^ n ∈ Lo q (n * a)
  | 0 => by simpa using Lo_zero isIntegral_one
  | n + 1 => by rw [pow_succ, Nat.succ_mul]; exact Lo_mul (Lo_pow hx n) hx

theorem Lo_prod {q a : ℕ} {ι : Type} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, f i ∈ Lo q a) :
    ∏ i ∈ s, f i ∈ Lo q (s.card * a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Lo_zero isIntegral_one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi, Nat.succ_mul, add_comm]
    exact Lo_mul (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def chiZ (ν : kˣ →* ℂˣ) (z : ℂ) : kˣ →* ℂ where
  toFun x := (ν x : ℂ) * apow x z
  map_one' := by simp
  map_mul' x y := by rw [map_mul, apow_mul, Units.val_mul]; ring

theorem chiZ_apply (ν : kˣ →* ℂˣ) (z : ℂ) (x : kˣ) : chiZ ν z x = (ν x : ℂ) * apow x z := rfl

theorem chiZ_KO {n : Type} [Fintype n] [DecidableEq n] {ϖ : kˣ} {e : ℕ} {ν : kˣ →* ℂˣ} (hϖ : IsUnif ϖ)
    (hν : CondLE ϖ e ν) (q : ℕ) (z : ℂ) {u : GL n k} (hu : u ∈ KO k n) : chiZ ν z (gdet u) ∈ Lo q 0 := by
  have h := valuation_gdet_of_mem_KO hu
  rw [chiZ_apply, apow_of_valuation_eq_one h, mul_one]
  exact Lo_zero (UpperTheory.isIntegral_unitChar_of_conductor_le ϖ e ν hϖ hν _ h)

theorem val_mul_le {a b c : Type} [Fintype b] {M : Matrix a b k} {N : Matrix b c k} {r : ValueGroupWithZero k}
    (hM : ∀ i j, valuation k (M i j) ≤ r) (hN : ∀ i j, N i j ∈ 𝒪[k]) (i : a) (j : c) :
    valuation k ((M * N) i j) ≤ r := by
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul]
  exact (mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).1 (hN l j))).trans (hM i l)

theorem fourierSum_mem {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ψ : AddChar k Circle)
    (ϖ : kˣ) (e : ℕ) (P : Finset D) (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → IsIntegral ℤ (ψ x : ℂ))
    (hq : resCard k ≠ 0) {a : ℕ} {Φ : Matrix A D k → ℂ} (hΦ : ∀ X, Φ X ∈ Lo (resCard k) a) (Y : Matrix A D k) :
    fourierSum ψ ϖ e P Φ Y ∈ Lo (resCard k) (e * Fintype.card A * P.card + a) := by
  classical
  rw [fourierSum_apply]
  split_ifs with h
  · refine Lo_mul ?_ (sum_mem fun T _ => Lo_mul (b := 0) (hΦ _) (Lo_zero (hψ _ ?_)))
    · rw [mem_Lo, mul_inv_cancel₀ (pow_ne_zero _ (by exact_mod_cast hq))]
      exact isIntegral_one
    rw [← Valuation.mem_integer_iff]
    change _ ∈ 𝒪[k]
    rw [pairCols, Finset.mul_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [Finset.mul_sum]
    refine Subring.sum_mem _ fun j _ => ?_
    rw [mul_left_comm]
    exact Subring.mul_mem _ (liftRes_mem T i j) (h i j j.2)
  · exact zero_mem _

theorem invFourierSum_inv_mem {A D : Type} [Fintype A] [DecidableEq A] [DecidableEq D] (ψ : AddChar k Circle)
    (ϖ : kˣ) (e : ℕ) (P : Finset D) (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → IsIntegral ℤ (ψ x : ℂ))
    {q a : ℕ} {Φ : Matrix A D k → ℂ} (hΦ : ∀ X, Φ X ∈ Lo q a) (T : Matrix A D k) :
    invFourierSum ψ⁻¹ ϖ e P Φ T ∈ Lo q a := by
  classical
  rw [invFourierSum_inv_apply]
  split_ifs with h
  · refine sum_mem fun S _ => Lo_mul (b := 0) (hΦ _) (Lo_zero (hψ _ ?_))
    rw [← Valuation.mem_integer_iff]
    change _ ∈ 𝒪[k]
    have e1 : ((ϖ ^ e : kˣ) : k) * pairCols P T ((ϖ ^ e)⁻¹ • liftRes S) = ∑ i, ∑ j : P, liftRes S i j * T i j := by
      rw [pairCols, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Matrix.smul_apply, Units.smul_def, smul_eq_mul, ← mul_assoc, ← mul_assoc, ← Units.val_mul, mul_inv_cancel,
        Units.val_one, one_mul]
    rw [e1]
    exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => Subring.mul_mem _ (liftRes_mem S i j) (h i j j.2)
  · exact zero_mem _

variable [MeasurableSpace k] [BorelSpace k]

theorem smallF_mem {A D : Type} [Fintype A] [DecidableEq A] {n : ℕ} [Fintype D] [DecidableEq D]
    (μ : Measure (GL (Fin n) k)) [μ.IsHaarMeasure] {J : Subgroup (GL (Fin n) k)} (hJo : IsOpen (J : Set (GL (Fin n) k)))
    (hJK : J ≤ KO k (Fin n)) (hμ : μ (J : Set (GL (Fin n) k)) = 1)
    (σ : A ⊕ Fin n ≃ D) {ν : kˣ →* ℂˣ} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (hν : CondLE ϖ e ν) (hram : ¬ IsUnram ν)
    {q C a : ℕ} (hC : chiZ ν ((Fintype.card D : ℂ) / 2) ϖ⁻¹ ∈ Lo q C) (c c' : D → kˣ) (hcc : ∀ j, c j * c' j = (ϖ ^ e)⁻¹)
    {Ψ : Matrix (Fin n) D k → ℂ} (hΨ : HasDepth ϖ e (diagLat c) Ψ) (hΨa : ∀ X, Ψ X ∈ Lo q a)
    (hinv : ∀ j ∈ J, ∀ Y, Ψ (j.val * Y) * (ν (gdet j) : ℂ) = Ψ Y) {u : GL D k} (hu : u ∈ KO k D) :
    smallF μ ν Ψ (Y0 k σ * (u * diagGL fun j => (c' j)⁻¹).val) ∈ Lo q (a + n * (e * C)) := by
  have hu' := (mem_KO_iff u).1 hu
  have hY0 : ∀ i j, Y0 k σ i j ∈ 𝒪[k] := fun i j => by
    simp only [Y0, of_apply]; split_ifs <;> simp
  have hent : ∀ (g : Matrix (Fin n) (Fin n) k) i j, (g * (Y0 k σ * (u * diagGL fun j => (c' j)⁻¹).val)) i j =
      (g * Y0 k σ * u.val) i j * (((c' j)⁻¹ : kˣ) : k) := fun g i j => by
    rw [Units.val_mul, diagGL_val, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_diagonal]
  have hv0 : ∀ x : kˣ, 0 < valuation k (x : k) := fun x => zero_lt_iff.2 (by simp)
  refine UpperTheory.integral_mem_addSubgroup_of_ramified_twisted_invariant μ J hJo hJK hμ ϖ ν e hϖ hram hν _
    (fun g => Ψ (g * (Y0 k σ * (u * diagGL fun j => (c' j)⁻¹).val))) e ?_ ?_ ?_ _ ?_
  · intro g hg
    have h1 : g * (Y0 k σ * (u * diagGL fun j => (c' j)⁻¹).val) ∈ matLat (Fin n) (diagLat c) := by
      by_contra h; exact hg (hΨ.1 _ h)
    have h2 : ∀ i j, valuation k ((g * Y0 k σ * u.val) i j) ≤ valuation k ((ϖ ^ (-(e : ℤ)) : kˣ) : k) := fun i j => by
      have h3 : valuation k ((g * (Y0 k σ * (u * diagGL fun j => (c' j)⁻¹).val)) i j) ≤ valuation k (c j : k) := h1 i j
      rw [hent, map_mul, Units.val_inv_eq_inv_val, map_inv₀, mul_inv_le_iff₀ (hv0 _), ← map_mul, ← Units.val_mul, hcc] at h3
      rwa [_root_.zpow_neg, _root_.zpow_natCast]
    intro i j
    have h4 := val_mul_le h2 hu'.2 i (σ (.inr j))
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] at h4
    simpa [Matrix.mul_apply, Y0] using h4
  · intro X Z hZ
    simp only [Matrix.add_mul]
    refine hΨ.2 _ _ fun i => ?_
    rw [smul_diagLat]
    intro j
    have h1 : valuation k ((Z * Y0 k σ * u.val) i j) ≤ 1 :=
      val_mul_le (val_mul_le (r := 1) (fun i j => by simpa using hZ i j) hY0) hu'.1 i j
    show valuation k ((Z * (Y0 k σ * (u * diagGL fun j => (c' j)⁻¹).val)) i j) ≤ valuation k ((ϖ ^ e * c j : kˣ) : k)
    rw [hent, map_mul, show ϖ ^ e * c j = (c' j)⁻¹ by rw [eq_inv_iff_mul_eq_one, mul_assoc, hcc, mul_inv_cancel]]
    exact mul_le_of_le_one_left' h1
  · intro j hj g
    simp only [Matrix.mul_assoc]
    exact hinv j hj _
  · intro m hm g hg
    obtain ⟨x, hx, y, hy, rfl⟩ := mem_shellSet.1 hg
    rw [mul_assoc, ← chiZ_apply]
    refine Lo_mul (hΨa _) ?_
    rw [gdet_mul, gdet_mul, map_mul, map_mul]
    have h1 : chiZ ν ((Fintype.card D : ℂ) / 2) (gdet (diagGL fun i => ϖ ^ m i)) ∈ Lo q (n * (e * C)) := by
      rw [gdet, det_diagGL, map_prod]
      have := Lo_prod (q := q) (a := e * C) Finset.univ (fun i => chiZ ν ((Fintype.card D : ℂ) / 2) (ϖ ^ m i)) fun i _ => by
        obtain ⟨l, hl⟩ : ∃ l : ℕ, m i = -(l : ℤ) := ⟨(-m i).toNat, by have := hm i; omega⟩
        rw [hl, _root_.zpow_neg, _root_.zpow_natCast, ← inv_pow, map_pow]
        exact Lo_mono (Lo_pow hC l) (Nat.mul_le_mul_right _ (by have := hm i; omega))
      simpa using this
    simpa using Lo_mul (Lo_mul (chiZ_KO hϖ hν q _ hx) h1) (chiZ_KO hϖ hν q _ hy)

theorem phiA_mem {A D : Type} [Fintype A] [DecidableEq A] {n : ℕ} [Fintype D] [DecidableEq D]
    (μ : Measure (GL (Fin n) k)) [μ.IsHaarMeasure] {J : Subgroup (GL (Fin n) k)} (hJo : IsOpen (J : Set (GL (Fin n) k)))
    (hJK : J ≤ KO k (Fin n)) (hμ : μ (J : Set (GL (Fin n) k)) = 1)
    (σ : A ⊕ Fin n ≃ D) {ν : kˣ →* ℂˣ} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (hν : CondLE ϖ e ν) (hram : ¬ IsUnram ν)
    {q C a : ℕ} (hC : chiZ ν ((Fintype.card D : ℂ) / 2) ϖ⁻¹ ∈ Lo q C) (hC' : chiZ ν ((Fintype.card D : ℂ) / 2) ϖ ∈ Lo q C)
    (P : Finset D) {Ψ : Matrix (Fin n) D k → ℂ} (hΨ : HasDepth ϖ e (blockLat ϖ e P) Ψ) (hΨa : ∀ X, Ψ X ∈ Lo q a)
    (hinv : ∀ j ∈ J, ∀ Y, Ψ (j.val * Y) * (ν (gdet j) : ℂ) = Ψ Y) (X : Matrix A D k) :
    phiA μ σ ν ϖ e (blockLat ϖ e P) Ψ X ∈ Lo q (Fintype.card D * (e * C) + (a + n * (e * C))) := by
  classical
  unfold phiA
  split_ifs with hX
  swap
  · exact zero_mem _
  rw [latA_blockLat] at hX
  set g : GL D k := blockScale ϖ e Pᶜ with hg
  have h1 : ∀ x, x ᵥ* (g⁻¹).val ∈ stdLat k D ↔ x ∈ blockLat ϖ e Pᶜ := fun x => by
    rw [← vecMul_blockScale_mem ϖ e Pᶜ, vecMul_vecMul, Units.inv_mul, vecMul_one]
  obtain ⟨u, hu, hXu⟩ := UpperTheory.exists_mem_KO_eq_stdFrame_mul_of_isPrimFrame σ _ (GlobalTheory.SplitFlip.Model.isPrimFrame_mul hX g⁻¹ h1)
  have h2 : invT (diagGL fun j => (blockUnits ϖ e Pᶜ j)⁻¹) = g := by
    have : (diagGL fun j => (blockUnits ϖ e Pᶜ j)⁻¹) = g⁻¹ := by
      rw [eq_inv_iff_mul_eq_one]
      refine Units.ext ?_
      rw [Units.val_mul, hg, blockScale, diagGL_val, diagGL_val, diagonal_mul_diagonal]
      simp
    refine Units.ext ?_
    rw [this, invT_val, inv_inv, hg, blockScale, diagGL_val, diagonal_transpose]
  have h3 : X = X0 k σ * (invT (u * diagGL fun j => (blockUnits ϖ e Pᶜ j)⁻¹)).val := by
    rw [map_mul, h2, Units.val_mul, ← Matrix.mul_assoc, ← hXu, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one]
  rw [h3, splitTheta_fFun_frameFirstBlock_mul, ← chiZ_apply]
  refine Lo_mul ?_ (smallF_mem μ hJo hJK hμ σ hϖ hν hram hC (blockUnits ϖ e P) (blockUnits ϖ e Pᶜ) (fun j => ?_) hΨ hΨa hinv hu)
  · rw [gdet_mul, map_mul, gdet, gdet, det_diagGL, map_prod]
    have := Lo_prod (q := q) (a := e * C) Finset.univ
      (fun j => chiZ ν ((Fintype.card D : ℂ) / 2) (blockUnits ϖ e Pᶜ j)⁻¹) fun j _ => by
        unfold blockUnits
        split_ifs
        · rw [inv_inv, map_pow]; exact Lo_pow hC' e
        · rw [inv_one, map_one]; exact Lo_mono (Lo_zero isIntegral_one) (Nat.zero_le _)
    simpa using Lo_mul (chiZ_KO hϖ hν q ((Fintype.card D : ℂ) / 2) hu) this
  · by_cases h : j ∈ P <;> simp [blockUnits, h]


omit [MeasurableSpace k] [BorelSpace k] in
theorem chiZ_unif {ν : kˣ →* ℂˣ} {ϖ : kˣ} (hϖ : IsUnif ϖ) (hq : resCard k ≠ 0) {B : ℕ} (d : ℕ)
    (h1 : (ν ϖ : ℂ) ∈ Lo (resCard k) B) (h2 : (ν ϖ⁻¹ : ℂ) ∈ Lo (resCard k) B) :
    chiZ ν ((d : ℂ) / 2) ϖ⁻¹ ∈ Lo (resCard k) (B + d) ∧ chiZ ν ((d : ℂ) / 2) ϖ ∈ Lo (resCard k) (B + d) := by
  have hq' : (resCard k : ℂ) ≠ 0 := by exact_mod_cast hq
  have hi : IsIntegral ℤ (resCard k : ℂ) := by
    simpa using isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (resCard k : ℤ))
  have hs : ((resCard k : ℂ) ^ ((d : ℂ) / 2)) ^ 2 = (resCard k : ℂ) ^ d := by
    rw [← Complex.cpow_nat_mul, ← Complex.cpow_natCast]; congr 1; push_cast; ring
  have h3 : IsIntegral ℤ ((resCard k : ℂ) ^ ((d : ℂ) / 2)) := IsIntegral.of_pow two_pos (by rw [hs]; exact hi.pow d)
  refine ⟨Lo_mul h2 ?_, Lo_mul h1 ?_⟩
  · rw [apow_inv, hϖ.apow_eq, neg_neg]
    exact Lo_mono (Lo_zero h3) (Nat.zero_le _)
  · rw [hϖ.apow_eq, mem_Lo, ← hs, Complex.cpow_neg, sq, mul_assoc,
      mul_inv_cancel₀ ((Complex.cpow_ne_zero_iff).2 (Or.inl hq')), mul_one]
    exact h3

theorem flip_mem {G : Grid k} {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (hψc : HasConductor ψ 1)
    (hq : resCard k ≠ 0) (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → IsIntegral ℤ (ψ x : ℂ)) {i j B N a : ℕ}
    (hν : CondLE ϖ e (G.nu i j)) (hram : ¬ IsUnram (G.nu i j)) (h1 : (G.nu i j ϖ : ℂ) ∈ Lo (resCard k) B)
    (h2 : (G.nu i j ϖ⁻¹ : ℂ) ∈ Lo (resCard k) B) (hr : G.rank (i + 1, j + 1) ≤ N) (St : G.PiLocalization₂)
    (hp : PassesThrough i j St.path) (hJ : IsOpen (St.level (i, j) : Set (GL (Fin (G.rank (i, j))) k)))
    (hK : St.level (i, j) ≤ KO k _) (hT : St.IsAdmissible .one ϖ e) (hTa : ∀ x, St.tensor x ∈ Lo (resCard k) a)
    (x : G.Args) : G.flipTensor .one ψ ϖ e i j St.level St.tensor x ∈ Lo (resCard k) (a + e * N * (3 * B + 8 * N)) := by
  have hJ' := isOpen_map_invT hJ hK
  haveI := isHaarMeasure_haarVol hJ'.1 hJ'.2
  have hsub := hp.subset
  have hN := GlobalTheory.FunObj.isNatDatum_sliceB hT.tensor (hsub (by simp)) (hsub (by simp)) x (i := i) (j := j)
  obtain ⟨c1, c2⟩ := chiZ_unif hϖ hq (Fintype.card (G.Cols i j)) h1 h2
  unfold Grid.flipTensor squareFlip
  refine invFourierSum_inv_mem ψ ϖ e _ hψ (fun X => Lo_mono (phiA_mem _ hJ hK (UpperTheory.haarVol_self_eq_one_of_openSubgroup_le_KO _ hJ hK) _ hϖ hν hram c1 c2 _
    ((GlobalTheory.SplitFlip.FourierDepth.fourier_exchange k _ _ ψ ϖ e _ hϖ hψc).1 _ hN)
    (fun Y => fourierSum_mem ψ ϖ e _ hψ hq (fun Z => hTa _) Y) (fun u hu Y => ?_) X) ?_) _
  · have h3 := UpperTheory.fourierSum_block_transpose_inv_eq ψ ϖ e hϖ hψc _ hN u⁻¹ (inv_mem (hK hu)) Y
    rw [inv_inv] at h3
    have h4 : G.sliceB i j St.tensor x = (G.nu i j (gdet u) : ℂ) • fun Z => G.sliceB i j St.tensor x
        (fromCols ((u⁻¹).valᵀ * Z.toCols₁) (u.val * Z.toCols₂)) := by
      funext Z
      have := UpperTheory.nu_det_mul_sliceB_block_action ϖ e St i j hp hT u⁻¹ (inv_mem hu) x Z
      rw [inv_inv] at this
      exact this.symm
    rw [← h3]
    conv_rhs => rw [h4, map_smul]
    rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  · have r1 : G.rank (i, j) ≤ N := le_trans (by simp only [Grid.rank]; gcongr <;> omega) hr
    have r2 : G.rank (i, j + 1) ≤ N := le_trans (by simp only [Grid.rank]; gcongr; omega) hr
    have r3 : G.rank (i + 1, j) ≤ N := le_trans (by simp only [Grid.rank]; gcongr; omega) hr
    have r4 : Fintype.card (G.Cols i j) ≤ 2 * N := by simp only [Fintype.card_sum, Fintype.card_fin]; omega
    have r5 : (Assignment.one.block (Fin (G.rank (i, j + 1))) (Fin (G.rank (i + 1, j)))).card ≤ 2 * N :=
      (Finset.card_le_univ _).trans r4
    rw [Fintype.card_fin]
    calc _ ≤ 2 * N * (e * (B + 2 * N)) + (e * N * (2 * N) + a + N * (e * (B + 2 * N))) := by gcongr
      _ = _ := by ring

theorem flips_mem {G : Grid k} {ψ : AddChar k Circle} {ϖ : kˣ} {e : ℕ} (hϖ : IsUnif ϖ) (hψc : HasConductor ψ 1) (he : 1 ≤ e)
    (hq : resCard k ≠ 0) (hψ : ∀ x : k, valuation k (((ϖ ^ e : kˣ) : k) * x) ≤ 1 → IsIntegral ℤ (ψ x : ℂ)) {B N : ℕ} :
    ∀ (l : List (ℕ × ℕ)) (S : G.PiLocalization₂) (a : ℕ),
      (∀ x ∈ l, CondLE ϖ e (G.nu x.1 x.2) ∧ ¬ IsUnram (G.nu x.1 x.2) ∧ (G.nu x.1 x.2 ϖ : ℂ) ∈ Lo (resCard k) B ∧
        (G.nu x.1 x.2 ϖ⁻¹ : ℂ) ∈ Lo (resCard k) B ∧ G.rank (x.1 + 1, x.2 + 1) ≤ N) →
      CanFlip S.path l → (∀ X, IsOpen (S.level X : Set (GL (Fin (G.rank X)) k)) ∧ S.level X ≤ KO k _) →
      S.IsAdmissible .one ϖ e → (∀ z, S.tensor z ∈ Lo (resCard k) a) →
      ∀ z, (S.flips .one ψ ϖ e l).tensor z ∈ Lo (resCard k) (a + l.length * (e * N * (3 * B + 8 * N))) := by
  intro l
  induction l with
  | nil => intro S a _ _ _ _ hF; simpa [Grid.PiLocalization₂.flips] using hF
  | cons x l ih =>
    intro S a hν hc hJ hT hF z
    obtain _ | ⟨hp, hc'⟩ := hc
    obtain ⟨x1, x2, x3, x4, x5⟩ := hν x List.mem_cons_self
    have := ih (S.flip .one ψ ϖ e x) _ (fun y hy => hν y (List.mem_cons_of_mem _ hy)) hc' (fun X => ?_)
      (GlobalTheory.T.splitThetaGrid_isAdmissible_flipTensor ψ ϖ e hϖ hψc he S x x1 hp hJ hT)
      (flip_mem hϖ hψc hq hψ x1 x2 x3 x4 x5 S hp (hJ _).1 (hJ _).2 hT hF) z
    · rw [List.length_cons, Nat.succ_mul, add_comm (l.length * _), ← add_assoc]
      exact this
    change IsOpen (G.flipLevel x.1 x.2 S.level X : Set (GL (Fin (G.rank X)) k)) ∧ G.flipLevel x.1 x.2 S.level X ≤ _
    by_cases hX : X = (x.1 + 1, x.2 + 1)
    · subst hX; simp only [Grid.flipLevel, Function.update_self]; exact ⟨isOpen_KO, le_rfl⟩
    · simp only [Grid.flipLevel, Function.update_of_ne hX]; exact hJ X

end UpperTheory.FlipInt

end
