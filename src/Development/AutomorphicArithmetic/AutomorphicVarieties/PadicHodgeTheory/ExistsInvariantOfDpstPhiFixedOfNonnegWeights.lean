module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsRestrictionBlockEmbeddingIntertwinesLie
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateRat
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PtCont
public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsInvariantOfDpstPhiFixedOfNonnegWeights
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LineInv
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem coord_lTensor {K V B B' ι : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup B]
    [Module K B] [AddCommGroup B'] [Module K B'] [DecidableEq ι] (b : Basis ι K V) (f : B →ₗ[K] B')
    (x : V ⊗[K] B) (i : ι) :
    equivFinsuppOfBasisLeft b (LinearMap.lTensor V f x) i = f (equivFinsuppOfBasisLeft b x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simp [equivFinsuppOfBasisLeft_apply_tmul_apply]
  | add y z hy hz => simp only [map_add (f := _), Finsupp.add_apply, hy, hz]

private theorem line_abs {K V B B' : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup B]
    [Module K B] [AddCommGroup B'] [Module K B'] (φ : B →ₗ[K] B) (j : B →ₗ[K] B') (F : Submodule K B')
    (e : B) (he : e ≠ 0) (fund : ∀ y : B, φ y = y → j y ∈ F → ∃ c : K, c • e = y) (x : V ⊗[K] B)
    (h1 : LinearMap.lTensor V φ x = x)
    (h2 : ∃ z, LinearMap.lTensor V F.subtype z = LinearMap.lTensor V j x) :
    ∃! v : V, x = v ⊗ₜ[K] e := by
  classical
  let b := Basis.ofVectorSpace K V
  obtain ⟨z, hz⟩ := h2
  have hc : ∀ i, ∃ c : K, c • e = equivFinsuppOfBasisLeft b x i := fun i =>
    fund _ (by rw [← coord_lTensor, h1]) (by
      rw [← coord_lTensor, ← hz, coord_lTensor]; exact Submodule.coe_mem _)
  choose c hc using hc
  let c' := Finsupp.onFinset (equivFinsuppOfBasisLeft b x).support c (fun i hi => by
    rw [Finsupp.mem_support_iff, ← hc]; exact smul_ne_zero hi he)
  refine ⟨b.repr.symm c', ?_, ?_⟩
  · apply (equivFinsuppOfBasisLeft b).injective
    ext i
    rw [equivFinsuppOfBasisLeft_apply_tmul_apply, LinearEquiv.apply_symm_apply, ← hc]
    rfl
  · intro v hv
    rw [LinearEquiv.eq_symm_apply]
    ext i
    have h := hc i
    rw [hv, equivFinsuppOfBasisLeft_apply_tmul_apply] at h
    exact (smul_left_injective K he h).symm

theorem UpperTheory.V.Loc.lineInv :
    ∀ {l : ℕ} [Fact l.Prime] {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] (x : V ⊗[ℚ_[l]] Bcr l), LinearMap.lTensor V (PP l).φB.toLinearMap x = x → LinearMap.lTensor V (PP l).ιB.toLinearMap x ∈ FilT A V 0 → ∃! v : V, x = v ⊗ₜ[ℚ_[l]] (1 : Bcr l) := by
  intro l _ A _ _ V _ _ _ _ x h1 h2
  refine line_abs (PP l).φB.toLinearMap (PP l).ιB.toLinearMap
    ((((PP l).PD (botExt l)).Fil 0).restrictScalars ℚ_[l]) 1 ?_ ?_ x h1 ?_
  · intro h
    apply ((PP l).PD (botExt l)).not_mem_filtration_two
    rw [← mul_one ((PP l).PD (botExt l)).t, h, mul_zero, map_zero]
    exact Submodule.zero_mem _
  · intro y hy hF
    obtain ⟨c, hc⟩ := ((PP l).PD (botExt l)).fund y (by rw [(PP l).PD_φ]; exact hy)
      (by rw [(PP l).PD_ι]; exact hF)
    exact ⟨c, by rw [← hc, Algebra.algebraMap_eq_smul_one]⟩
  · obtain ⟨z, hz⟩ := h2
    exact ⟨z, hz⟩
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_invariant_of_dpst_phi_fixed_of_nonneg_weights :
    ∀ {l : ℕ} [Fact l.Prime] {K L : FinExt l}, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), τ x ∈ L.1) → ∀ {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK K) V), FiniteDimensional ↥L.1 ↥(DdR ((UpperTheory.V.Loc.PP l).PD K) ρ) → (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (c : ℤ), c < 0 → multV ((UpperTheory.V.Loc.PP l).PD K) ρ τ c = 0) → ∀ z : ↥(Dpst (UpperTheory.V.Loc.PP l) ρ), z ≠ 0 → monD (UpperTheory.V.Loc.PP l) ρ z = 0 → phiD (UpperTheory.V.Loc.PP l) ρ z = z → (∀ g, actD (UpperTheory.V.Loc.PP l) ρ g z = z) → ∃ v : V, v ≠ 0 ∧ ∀ g, ρ g v = v := by
  intro l _ K L key V _ _ _ _ _ ρ hfin hm z hz hN hφ hG
  let P := UpperTheory.V.Loc.PP l
  obtain ⟨y, hy, e⟩ := (mem_Dst_and_monV_eq_zero_iff l P K L V ρ z.1).mp
    ⟨(mem_Dst P ρ).mpr fun g => congrArg Subtype.val (hG g), congrArg Subtype.val hN⟩
  have hy' : ∀ g, actVB (P.PD K) ρ g y = y := by
    intro g
    have := (Submodule.mem_iInf _).mp hy g
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
  have c1 : ∀ x : TensorProduct ℚ_[l] V P.R.B, phiV P ↥L.1 V (crisIncl P ↥L.1 V x) =
      crisIncl P ↥L.1 V (LinearMap.lTensor V P.φB.toLinearMap x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have h1 : LinearMap.lTensor V P.φB.toLinearMap y = y := by
    apply crisIncl_injective (LL := ↥L.1) P
    rw [← c1, e]
    exact congrArg Subtype.val hφ
  have c2 : ∀ g (x : TensorProduct ℚ_[l] V P.R.B),
      actVdR (P.PD K) ρ g (LinearMap.lTensor V P.ιB.toLinearMap x) =
      LinearMap.lTensor V P.ιB.toLinearMap (actVB (P.PD K) ρ g x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      have := (P.PD K).ι_comm g b
      rw [P.PD_ι, P.PD_ι] at this
      simp [actVdR, actVB, this]
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
  have h2 : LinearMap.lTensor V P.ιB.toLinearMap y ∈ DdR (P.PD K) ρ := by
    refine (Submodule.mem_iInf _).mpr fun g => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero, c2, hy']
  have h3 := (UpperTheory.ddR_le_fil_and_inf_fil_eq_bot_of_hodgeTate_mult P key ρ hfin).1 0 hm h2
  have hF : ((P.PD (UpperTheory.V.Loc.botExt l)).Fil 0).restrictScalars ℚ_[l] =
      ((P.PD K).Fil 0).restrictScalars ℚ_[l] := SetLike.coe_injective (P.PD_Fil _ _ 0)
  have h4 : LinearMap.lTensor V P.ιB.toLinearMap y ∈ UpperTheory.V.Loc.FilT ↥L.1 V 0 := by
    unfold UpperTheory.V.Loc.FilT
    unfold FilV at h3
    rw [← hF] at h3
    exact h3
  obtain ⟨v, hv, hu⟩ := UpperTheory.V.Loc.lineInv (A := ↥L.1) y h1 h4
  refine ⟨v, ?_, fun g => hu _ ?_⟩
  · rintro rfl
    apply hz
    apply Subtype.ext
    rw [← e, hv]
    simp
  · have := hy' g
    rw [← this, hv]
    simp [actVB]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsCommonEigenline
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.BlockConjugation
noncomputable def UpperTheory.Reformulated.B.BlockConjugation.HasFlag :
    {H k : Type} → [inst : Group H] → [inst_1 : CommRing k] → {n : ℕ} → (H →* GL (Fin n) k) → (Fin n → H →* kˣ) → Prop :=
    fun {H k : Type} [Group H] [CommRing k] {n : ℕ} (r : H →* GL (Fin n) k) (κ : Fin n → H →* kˣ) ↦
      ∃ (g : GL (Fin n) k),
        ∀ (s : H),
          (∀ (i j : Fin n), j < i → (↑(g * (r : H → GL (Fin n) k) s * g⁻¹) : Matrix (Fin n) (Fin n) k) i j = (0 : k)) ∧
            ∀ (i : Fin n),
              (↑(g * (r : H → GL (Fin n) k) s * g⁻¹) : Matrix (Fin n) (Fin n) k) i i = (↑((κ i : H → kˣ) s) : k)

private def UpperTheory.Reformulated.B.BlockConjugation.blk {k : Type} [CommRing k] {n : ℕ} (A : Matrix (Fin n) (Fin n) k) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) k :=
  Matrix.of (Fin.cons (Fin.cons 1 0) (fun i => Fin.cons 0 (A i)))

private theorem UpperTheory.Reformulated.B.BlockConjugation.blk_mul {k : Type} [CommRing k] {n : ℕ} (A B : Matrix (Fin n) (Fin n) k) :
    UpperTheory.Reformulated.B.BlockConjugation.blk A * UpperTheory.Reformulated.B.BlockConjugation.blk B = UpperTheory.Reformulated.B.BlockConjugation.blk (A * B) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [UpperTheory.Reformulated.B.BlockConjugation.blk, Matrix.mul_apply, Fin.sum_univ_succ]

private theorem UpperTheory.Reformulated.B.BlockConjugation.blk_one {k : Type} [CommRing k] {n : ℕ} :
    UpperTheory.Reformulated.B.BlockConjugation.blk (1 : Matrix (Fin n) (Fin n) k) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [UpperTheory.Reformulated.B.BlockConjugation.blk, Matrix.one_apply, (Fin.succ_ne_zero _).symm]

private theorem UpperTheory.Reformulated.B.BlockConjugation.exists_col {k : Type} [Field k] {n : ℕ} (v : Fin (n + 1) → k) (hv : v ≠ 0) :
    ∃ Q : GL (Fin (n + 1)) k, ∀ i, (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i 0 = v i := by
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hv
  have hd : (((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateCol a v).submatrix id (Equiv.swap 0 a)).det ≠ 0 := by
    rw [Matrix.det_permute', ← Matrix.cramer_apply, Matrix.cramer_one]
    refine mul_ne_zero ?_ (by simpa using ha)
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap 0 a)) with h | h <;> simp [h]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd, fun i => ?_⟩
  change (((1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k).updateCol a v).submatrix id (Equiv.swap 0 a)) i 0 = v i
  simp

private theorem UpperTheory.Reformulated.B.BlockConjugation.conj_blk {k : Type} [CommRing k] {n : ℕ} (A B : Matrix (Fin n) (Fin n) k)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (hM : ∀ i : Fin n, M i.succ 0 = 0) :
    (UpperTheory.Reformulated.B.BlockConjugation.blk A * M * UpperTheory.Reformulated.B.BlockConjugation.blk B) 0 0 = M 0 0 ∧
    (∀ i : Fin n, (UpperTheory.Reformulated.B.BlockConjugation.blk A * M * UpperTheory.Reformulated.B.BlockConjugation.blk B) i.succ 0 = 0) ∧
    (∀ i j : Fin n, (UpperTheory.Reformulated.B.BlockConjugation.blk A * M * UpperTheory.Reformulated.B.BlockConjugation.blk B) i.succ j.succ =
      (A * M.submatrix Fin.succ Fin.succ * B) i j) := by
  refine ⟨?_, fun i => ?_, fun i j => ?_⟩ <;>
    simp [UpperTheory.Reformulated.B.BlockConjugation.blk, Matrix.mul_apply, Fin.sum_univ_succ, hM]

theorem UpperTheory.Reformulated.B.BlockConjugation.exists_common_eigenline :
    ∀ {H k : Type} [inst : Group H] [inst_1 : TopologicalSpace H] [inst_2 : Field k] [inst_3 : TopologicalSpace k]
      [IsTopologicalRing k] {n : ℕ} (r : H →* GL (Fin (n + (1 : ℕ))) k) (κ : Fin (n + (1 : ℕ)) → H →* kˣ)
      (v : Fin (n + (1 : ℕ)) → k),
      Continuous (⇑r : H → GL (Fin (n + (1 : ℕ))) k) →
        v ≠ (0 : Fin (n + (1 : ℕ)) → k) →
          (∀ (g : H),
              (↑((r : H → GL (Fin (n + (1 : ℕ))) k) g) : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k).mulVec v =
                (↑((κ (0 : Fin (n + (1 : ℕ))) : H → kˣ) g) : k) • v) →
            ∃ (p : GL (Fin (n + (1 : ℕ))) k) (r₁ : H →* GL (Fin (n + (1 : ℕ))) k) (r' : H →* GL (Fin n) k),
              (∀ (g : H), (r₁ : H → GL (Fin (n + (1 : ℕ))) k) g = p * (r : H → GL (Fin (n + (1 : ℕ))) k) g * p⁻¹) ∧
                Continuous (⇑r₁ : H → GL (Fin (n + (1 : ℕ))) k) ∧
                  Continuous (⇑r' : H → GL (Fin n) k) ∧
                    (∀ (g : H) (i : Fin n),
                        (↑((r₁ : H → GL (Fin (n + (1 : ℕ))) k) g) : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k) i.succ
                            (0 : Fin (n + (1 : ℕ))) =
                          (0 : k)) ∧
                      (∀ (g : H),
                          (↑((r₁ : H → GL (Fin (n + (1 : ℕ))) k) g) : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k)
                              (0 : Fin (n + (1 : ℕ))) (0 : Fin (n + (1 : ℕ))) =
                            (↑((κ (0 : Fin (n + (1 : ℕ))) : H → kˣ) g) : k)) ∧
                        (∀ (g : H) (i j : Fin n),
                            (↑((r₁ : H → GL (Fin (n + (1 : ℕ))) k) g) : Matrix (Fin (n + (1 : ℕ))) (Fin (n + (1 : ℕ))) k)
                                i.succ j.succ =
                              (↑((r' : H → GL (Fin n) k) g) : Matrix (Fin n) (Fin n) k) i j) ∧
                          ((UpperTheory.Reformulated.B.BlockConjugation.HasFlag r' fun (i : Fin n) ↦ κ i.succ) → UpperTheory.Reformulated.B.BlockConjugation.HasFlag r κ) := by
  intro H k _ _ _ _ _ n r κ v hr hv hev
  obtain ⟨Q, hQ⟩ := UpperTheory.Reformulated.B.BlockConjugation.exists_col v hv
  let r₁ : H →* GL (Fin (n + 1)) k := (MulAut.conj Q⁻¹).toMonoidHom.comp r
  have hr₁ : ∀ g, r₁ g = Q⁻¹ * r g * Q⁻¹⁻¹ := fun g => rfl
  have hc₁ : Continuous r₁ := by
    have : (⇑r₁) = fun g => Q⁻¹ * r g * Q⁻¹⁻¹ := funext hr₁
    rw [this]
    exact (continuous_const.mul hr).mul continuous_const
  have hQv : (Q : Matrix (Fin (n + 1)) (Fin (n + 1)) k).mulVec (Pi.single 0 1) = v := by
    ext i
    simp [hQ]
  have hcol : ∀ g i, (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i 0 =
      ((κ 0 g : k) • (Pi.single 0 1 : Fin (n + 1) → k)) i := by
    intro g i
    have h1 : (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k).mulVec (Pi.single 0 1) =
        ((κ 0 g : k) • (Pi.single 0 1 : Fin (n + 1) → k)) := by
      rw [hr₁, inv_inv, Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hQv, hev,
        Matrix.mulVec_smul, ← hQv, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [← h1]
    simp
  have h0 : ∀ g (i : Fin n), (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.succ 0 = 0 := by
    intro g i
    rw [hcol]
    simp
  have h00 : ∀ g, (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) 0 0 = (κ 0 g : k) := by
    intro g
    rw [hcol]
    simp
  let φ : H →* Matrix (Fin n) (Fin n) k :=
    { toFun := fun g => (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k).submatrix Fin.succ Fin.succ
      map_one' := by
        ext i j
        simp [Matrix.one_apply]
      map_mul' := fun a b => by
        ext i j
        rw [map_mul, Units.val_mul]
        simp only [Matrix.submatrix_apply, Matrix.mul_apply, Fin.sum_univ_succ, h0, zero_mul, zero_add] }
  have hφ : ∀ g, φ g = (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k).submatrix Fin.succ Fin.succ := fun g => rfl
  refine ⟨Q⁻¹, r₁, φ.toHomUnits, hr₁, hc₁, ?_, h0, h00, fun g i j => rfl, ?_⟩
  · rw [Units.continuous_iff]
    refine ⟨(Units.continuous_val.comp hc₁).matrix_submatrix _ _, ?_⟩
    have : (fun g => (((φ.toHomUnits g)⁻¹ : (Matrix (Fin n) (Fin n) k)ˣ) : Matrix (Fin n) (Fin n) k)) =
        fun g => (((r₁ g)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k).submatrix
          Fin.succ Fin.succ := by
      funext g
      rw [← map_inv, ← map_inv]
      rfl
    rw [this]
    exact (Units.continuous_coe_inv.comp hc₁).matrix_submatrix _ _
  · rintro ⟨a, ha⟩
    let b : GL (Fin (n + 1)) k :=
      ⟨UpperTheory.Reformulated.B.BlockConjugation.blk (a : Matrix (Fin n) (Fin n) k),
        UpperTheory.Reformulated.B.BlockConjugation.blk ((a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k),
        by rw [UpperTheory.Reformulated.B.BlockConjugation.blk_mul, Units.mul_inv, UpperTheory.Reformulated.B.BlockConjugation.blk_one],
        by rw [UpperTheory.Reformulated.B.BlockConjugation.blk_mul, Units.inv_mul, UpperTheory.Reformulated.B.BlockConjugation.blk_one]⟩
    refine ⟨b * Q⁻¹, fun s => ?_⟩
    have e : ((b * Q⁻¹ * r s * (b * Q⁻¹)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
        UpperTheory.Reformulated.B.BlockConjugation.blk (a : Matrix (Fin n) (Fin n) k) * (r₁ s : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *
          UpperTheory.Reformulated.B.BlockConjugation.blk ((a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
      have : b * Q⁻¹ * r s * (b * Q⁻¹)⁻¹ = b * r₁ s * b⁻¹ := by
        rw [hr₁]
        group
      rw [this]
      rfl
    obtain ⟨c1, c2, c3⟩ := UpperTheory.Reformulated.B.BlockConjugation.conj_blk (a : Matrix (Fin n) (Fin n) k)
      ((a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) _ (h0 s)
    obtain ⟨d1, d2⟩ := ha s
    have e' : ((a * φ.toHomUnits s * a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
        (a : Matrix (Fin n) (Fin n) k) *
          (r₁ s : Matrix (Fin (n + 1)) (Fin (n + 1)) k).submatrix Fin.succ Fin.succ *
          ((a⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := rfl
    rw [e'] at d1 d2
    rw [e]
    refine ⟨fun i j => ?_, fun i => ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · intro h
        exact absurd h (Fin.not_lt_zero _)
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro _
          exact c2 i
        · intro h
          rw [c3]
          exact d1 i j (Fin.succ_lt_succ_iff.mp h)
    · refine Fin.cases ?_ (fun i => ?_) i
      · rw [c1, h00]
      · rw [c3]
        exact d2 i
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_common_eigenline :
    ∀ {H k : Type} [Group H] [TopologicalSpace H] [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} (r : H →* GL (Fin (n + 1)) k) (κ : Fin (n + 1) → H →* kˣ) (v : Fin (n + 1) → k), Continuous r → v ≠ 0 → (∀ g, (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ v = (κ 0 g : k) • v) → ∃ (p : GL (Fin (n + 1)) k) (r₁ : H →* GL (Fin (n + 1)) k) (r' : H →* GL (Fin n) k), (∀ g, r₁ g = p * r g * p⁻¹) ∧ Continuous r₁ ∧ Continuous r' ∧ (∀ g (i : Fin n), (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.succ 0 = 0) ∧ (∀ g, (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) 0 0 = (κ 0 g : k)) ∧ (∀ g (i j : Fin n), (r₁ g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.succ j.succ = (r' g : Matrix (Fin n) (Fin n) k) i j) ∧ (HasFlag r' (fun i => κ i.succ) → HasFlag r κ) :=
  _root_.UpperTheory.Reformulated.B.BlockConjugation.exists_common_eigenline
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsFinrankTwoCocyclesCharRatio
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.HV UpperTheory.V.Base IsLocalRing

private theorem finrank_Z1_chRep_eq_two_of_ne_one_ne_cyc (hP : LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (φ : H →* Formalism.BasicNotions.Loc.GQ l) (hφ : Topology.IsOpenEmbedding φ) (hr : φ.range = ⊤)
    {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E]
    [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E]
    (κ : H →* Eˣ) (hκ : Continuous fun g => (κ g : E)) (h0 : ∃ g, κ g ≠ 1) (h2 : ∃ g, κ g ≠ cycA l l E (φ g)) :
    finrank E ↥(ReciprocityTheory.Gal.Z1 (chRep κ)) = 2 := by
  have hρ : ∀ g x, chRep κ g x = (κ g : E) * x := fun g x => by simp [chRep]
  have hc : ReciprocityTheory.Gal.ContAction (chRep κ) := by
    unfold ReciprocityTheory.Gal.ContAction
    simp only [hρ]
    exact (hκ.comp continuous_fst).mul continuous_snd
  obtain ⟨f1, -, e1, e2⟩ := tateRat hP (l := l) φ hφ (chRep κ) hc
  obtain ⟨g, hg⟩ := h0
  have hz : ∀ m : E, chRep κ g m - m = 0 → m = 0 := by
    intro m hm
    have h1 : ((κ g : E) - 1) * m = 0 := by
      rw [sub_mul, one_mul, ← hρ, hm]
    exact (mul_eq_zero.1 h1).resolve_left fun h => hg (Units.val_eq_one.1 (sub_eq_zero.1 h))
  have hH0 : ReciprocityTheory.Gal.H0 (chRep κ) = ⊥ :=
    eq_bot_iff.2 fun m hm => hz m (sub_eq_zero.2 ((mem_riemannRochSpace_iff_regularAt_everywhere _ _).1 hm g))
  have hB : finrank E ↥(ReciprocityTheory.Gal.B1 (chRep κ)) = 1 := by
    unfold ReciprocityTheory.Gal.B1
    rw [LinearMap.finrank_range_of_inj, finrank_self]
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    exact fun m hm => hz m (congrFun hm g)
  have hD : H0dual ((cycA l l E).comp φ) (chRep κ) = ⊥ := by
    obtain ⟨s, hs⟩ := h2
    refine eq_bot_iff.2 fun F hF => LinearMap.ext fun x => ?_
    have h1 := hF s x
    rw [hρ, ← smul_eq_mul, map_smul, smul_eq_mul, ← sub_eq_zero, ← sub_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left fun h => hs (Units.ext (sub_eq_zero.1 h))
  have hBZ : ReciprocityTheory.Gal.B1 (chRep κ) ≤ ReciprocityTheory.Gal.Z1 (chRep κ) := by
    rintro _ ⟨m, rfl⟩
    refine ⟨?_, fun g h => ?_⟩
    · show Continuous fun g => chRep κ g m - m
      simp only [hρ]
      exact (hκ.mul continuous_const).sub continuous_const
    · simp only [amitsur_d0_apply, hρ, map_mul κ, Units.val_mul]
      ring
  have eB := Submodule.comapSubtypeEquivOfLe hBZ
  rw [hD, finrank_bot] at e2
  rw [hH0, finrank_bot, e2, if_pos rfl, hr, Subgroup.index_top, finrank_self] at e1
  haveI : Module.Finite E ↥(ReciprocityTheory.Gal.B1 (chRep κ)) := finite_of_finrank_pos (by omega)
  haveI := Module.Finite.equiv eB.symm
  haveI : Module.Finite E ↥(ReciprocityTheory.Gal.Z1 (chRep κ)) :=
    Module.Finite.of_submodule_quotient ((ReciprocityTheory.Gal.B1 (chRep κ)).comap (ReciprocityTheory.Gal.Z1 (chRep κ)).subtype)
  have e3 := Submodule.finrank_quotient_add_finrank
    ((ReciprocityTheory.Gal.B1 (chRep κ)).comap (ReciprocityTheory.Gal.Z1 (chRep κ)).subtype)
  rw [eB.finrank_eq, hB, e1] at e3
  omega

private theorem dec_iso {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime]
    (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) :
    ∃ φ : ↥(Dec (F := ℚ) A) →* Formalism.BasicNotions.Loc.GQ l, Topology.IsOpenEmbedding φ ∧ φ.range = ⊤ ∧
      ∀ g, cyc l l (φ g) = cycZ ℚ Ω l (g : G ℚ Ω) := by
  obtain ⟨w, hw, hAw⟩ := GlobalTheory.DecLocal.exists_place_below (p := l) (F := ℚ) A hA
  obtain ⟨j, rfl⟩ := (decEmb (F := ℚ) (Ω := Ω) (v := l)).1 A w hAw hw
  obtain ⟨-, φ, h1, -, h3, -, h5, -⟩ := (decEmb (F := ℚ) (Ω := Ω) (v := l)).2 j
  exact ⟨φ, h1, eq_top_iff.2 fun σ _ => (h3 σ).2 fun x => by simp, h5 l⟩

theorem UpperTheory.exists_finrank_two_cocycles_char_ratio :
    LocalPublishedTheorems → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (hD : D.Good) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra ↥c.O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ↥c.O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [IsFractionRing ↥c.O E] (a b : Fin 4), a < b → ∃ T : Submodule E (D.Gp l → E), (∀ z, z ∈ T ↔ QCont l z ∧ ∀ g h : D.Gp l, z (g * h) = z g + algebraMap c.O E ((D.ps a g * (D.ps b g)⁻¹ : c.Oˣ) : c.O) * z h) ∧ finrank E ↥T = 2 := by
  intro hP Ω _ _ _ l _ c D hD E _ _ _ _ _ _ _ _ a b hab
  have facts := UpperTheory.V.GradeZeroInterpolatingElement.facts D hD
  have F2 := facts.2.1
  have F4 := facts.2.2.2.1
  have F7 := facts.2.2.2.2.2.2.1
  have LargeParameterEstimates := facts.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨φ, hφ, hr, hcy⟩ := dec_iso l (D.pl l) (hD.pl_over l Fact.out)
  letI : TopologicalSpace E := moduleTopology ℚ_[l] E
  haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
  haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E
  have hinj : Function.Injective (algebraMap c.O E) := IsFractionRing.injective _ _
  let f : (c.O)ˣ →* Eˣ := Units.map (algebraMap c.O E : c.O →* E)
  have hf : Function.Injective f := Units.map_injective hinj
  let κ : D.Gp l →* Eˣ := f.comp ((D.ps a * (D.ps b)⁻¹).comp (D.Gp l).subtype)
  have hκ : ∀ g : D.Gp l, κ g = f (D.ps a g * (D.ps b g)⁻¹) := fun _ => rfl
  have hps : ∀ i, Continuous fun g : G ℚ Ω => algebraMap c.O E (D.ps i g : c.O) := fun i =>
    (ptCont (l := l) (O := c.O) c.O E (Algebra.ofId c.O E)).1 _ _ (LargeParameterEstimates i)
  have hκc : Continuous fun g => (κ g : E) := by
    have : (fun g => (κ g : E)) = fun g : D.Gp l =>
        algebraMap c.O E (D.ps a g : c.O) * algebraMap c.O E (D.ps b (g : G ℚ Ω)⁻¹ : c.O) := funext fun g => by
      rw [hκ, map_inv (D.ps b), ← map_mul]
      rfl
    rw [this]
    exact ((hps a).comp continuous_subtype_val).mul ((hps b).comp (continuous_subtype_val.inv))
  have hce : ∀ g : D.Gp l, cycA l l E (φ g) = f (chiO ℚ Ω l c.O g) := fun g => Units.ext (by
    show algebraMap ℤ_[l] E (cyc l l (φ g) : ℤ_[l]ˣ) = algebraMap c.O E (algebraMap ℤ_[l] c.O (cycZ ℚ Ω l g : ℤ_[l]ˣ))
    rw [hcy, ← IsScalarTower.algebraMap_apply])
  have hord : ¬ IsOfFinOrder (chiO ℚ Ω l c.O D.s0) := by
    have hi : Function.Injective (algebraMap ℤ_[l] c.O) := by
      refine Function.Injective.of_comp (f := algebraMap c.O E) ?_
      rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq, IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] E]
      exact (algebraMap ℚ_[l] E).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
    exact fun h => hD.decompSigma_ord ((Units.map_injective (f := (algebraMap ℤ_[l] c.O).toMonoidHom) hi).isOfFinOrder_iff.1 h)
  refine ⟨ReciprocityTheory.Gal.Z1 (chRep κ), fun z => Iff.rfl, finrank_Z1_chRep_eq_two_of_ne_one_ne_cyc hP φ hφ hr κ hκc ⟨D.s0, fun h => ?_⟩ ?_⟩
  · rw [hκ, map_eq_one_iff f hf, mul_inv_eq_one] at h
    exact hab.ne (F7 (congrArg Units.val h))
  · by_cases hl : lamW a = lamW b
    · refine ⟨D.s0, fun h => ?_⟩
      rw [hκ, hce] at h
      have h1 := hf h
      rw [F4 a _ hD.decompSigma_mem, F4 b _ hD.decompSigma_mem, mul_inv_eq_iff_eq_mul, ← pow_succ'] at h1
      have h2 := injective_pow_iff_not_isOfFinOrder.2 hord h1
      have := hD.two_le
      fin_cases a <;> fin_cases b <;> simp [lamW, Raw.wts4] at hab hl h2 <;> omega
    · obtain ⟨h1, -, h3⟩ := F2 l (Finset.mem_insert_self _ _)
      refine ⟨⟨D.sg l, h1⟩, fun h => h3 a b hl ?_⟩
      rw [hκ, hce] at h
      have h4 : D.ps a (D.sg l) * (D.ps b (D.sg l))⁻¹ = 1 := (hf h).trans (by
        show Units.map _ (cycZ ℚ Ω l (D.sg l)) = 1
        rw [hD.sg_cyc, map_one])
      rw [mul_inv_eq_one] at h4
      exact congrArg (fun x : c.Oˣ => residue c.O (x : c.O)) h4
end
