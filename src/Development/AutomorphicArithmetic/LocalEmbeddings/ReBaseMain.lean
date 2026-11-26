module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction
public import Development.AutomorphicArithmetic.LocalEmbeddings.ReBaseReal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityPersistsRowColumnChanges
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryConjugate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanInvolutionSystemsConjArchimedeanUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFunctionFactorizableSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleTrivialOfSamePolarization
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedDataRestrictionUnique

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedLocalIsomorphismScalars
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PolIso

theorem modelI_smul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (om : Rep σ X W) (Λ : ℂ)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (h : UA σ W.J) : M.I om (Λ • Φ) h = Λ * M.I om Φ h := by
  unfold Model.I theta thetaSum
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  congr 1
  funext g
  exact tsum_mul_left

end GlobalTheory.PolIso
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProductMap
noncomputable def UpperTheory.Reformulated.B.IdempotentMatrixMonoidHom.prM :
    {R A : Type} →
      [inst : CommRing R] →
        [inst_1 : CommRing A] →
          [Algebra R A] →
            (e : R) → e * e = e → (ι : Type) → [inst : Fintype ι] → [inst_3 : DecidableEq ι] → Matrix ι ι A →* Matrix ι ι A :=
  fun {R A} _ _ _ e he ι _ _ =>
    { toFun := fun M => e • M + (1 - e) • (1 : Matrix ι ι A)
      map_one' := by rw [← add_smul, add_sub_cancel, one_smul]
      map_mul' := fun M N => by
        have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
        have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
        have h3 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, mul_one, h2, sub_zero]
        simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add,
          smul_smul, he, h1, h2, h3, zero_smul, add_zero, zero_add, Matrix.mul_one] }
end

section -- merged from Development.AutomorphicArithmetic.LocalEmbeddings.ReBaseZeta
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ReBase

section Local

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {A' D : Type} [Fintype A'] [DecidableEq A'] [Fintype D] [DecidableEq D] {a : ℕ}

theorem bigZetaIntegral_equivariant (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] (ϖ : kˣ) (σ : Fin a ⊕ A' ≃ D) (ν β : kˣ →* ℂˣ)
    {g : GL (Fin a) k} (hg : g ∈ KO k (Fin a)) {c : GL D k} (hc : c ∈ KO k D) (Φ : Matrix (Fin a) D k → ℂ) (h : GL D k) :
    (ν (gdet g) : ℂ) * bigP μ ϖ σ ν β (fun X => Φ (g.val * X * c.valᵀ)) h =
      β (gdet c) * bigP μ ϖ σ ν β Φ (h * c⁻¹) := by
  have e1 : (invT (h * c⁻¹)).val = (invT h).val * c.valᵀ := by rw [map_mul, map_inv, Units.val_mul, invT_inv_val]
  have e2 : gdet h = gdet (h * c⁻¹) * gdet c := by rw [← gdet_mul, inv_mul_cancel_right]
  rw [bigZetaIntegral_eq, bigZetaIntegral_eq, e1, e2, apow_mul, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hc), map_mul, Units.val_mul]
  unfold bigF
  rw [← GlobalTheory.FlipMatch.ZMat.shellSum_mul_left μ ϖ ν _ (fun x => Φ (x * (X0 k σ * ((invT h).val * c.valᵀ)))) hg]
  simp only [Matrix.mul_assoc]
  ring

theorem smallP_change {A : Type} (μ : Measure (GL A' k)) [μ.IsHaarMeasure] (σ : A ⊕ A' ≃ D) (ν α : kˣ →* ℂˣ)
    {g : GL A' k} (hg : g ∈ KO k A') {c : GL D k} (hc : c ∈ KO k D) (Ψ : Matrix A' D k → ℂ) (h : GL D k) :
    smallP μ σ ν α (fun Y => Ψ ((invT g).val * Y * (c⁻¹).val)) h =
      ν (gdet g) * α (gdet c) * smallP μ σ ν α Ψ (h * c⁻¹) := by
  have e2 : gdet h = gdet (h * c⁻¹) * gdet c := by rw [← gdet_mul, inv_mul_cancel_right]
  have e3 : ∀ Y : Matrix A' D k, smallF μ ν (fun Y => Ψ ((invT g).val * Y * (c⁻¹).val)) Y =
      ν (gdet g) * smallF μ ν Ψ (Y * (c⁻¹).val) := fun Y => by
    unfold smallF
    rw [← integral_mul_left_eq_self (fun x : GL A' k => Ψ (x.val * (Y * (c⁻¹).val)) * (ν (gdet x) : ℂ) *
      apow (gdet x) ((Fintype.card D : ℂ) / 2)) (invT g), ← integral_const_mul]
    congr 1
    funext x
    have h4 : (ν (gdet g) : ℂ) ≠ 0 := Units.ne_zero _
    rw [gdet_mul, apow_mul, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO (invT_mem_KO hg)), gdet_invT, map_mul,
      map_inv, Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val]
    simp only [Matrix.mul_assoc]
    field_simp
  unfold smallP
  rw [e3, e2, apow_mul, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hc), map_mul, Units.val_mul, Units.val_mul,
    Matrix.mul_assoc]
  ring

theorem bigZetaIntegral_smul (μ : Measure (GL (Fin a) k)) (ϖ : kˣ) (σ : Fin a ⊕ A' ≃ D) (ν β : kˣ →* ℂˣ) (z : ℂ)
    (Φ : Matrix (Fin a) D k → ℂ) (h : GL D k) : bigP μ ϖ σ ν β (z • Φ) h = z * bigP μ ϖ σ ν β Φ h := by
  simp only [bigZetaIntegral_eq, bigF, Pi.smul_apply, smul_eq_mul, shellSum_smul]
  ring

theorem zeta_change (μ : Measure (GL (Fin a) k)) [μ.IsHaarMeasure] (μ' : Measure (GL A' k)) [μ'.IsHaarMeasure] (ϖ : kˣ)
    (σ : Fin a ⊕ A' ≃ D) (ν α β : kˣ →* ℂˣ) (hν : ∀ x, α x = ν x * β x) {g : GL (Fin a) k} (hg : g ∈ KO k (Fin a))
    {g' : GL A' k} (hg' : g' ∈ KO k A') {c : GL D k} (hc : c ∈ KO k D) (Φ : Matrix (Fin a) D k → ℂ)
    (Ψ : Matrix A' D k → ℂ) (H : bigP μ ϖ σ ν β Φ = smallP μ' σ ν α Ψ) :
    bigP μ ϖ σ ν β (fun X => ((ν (gdet g * gdet g' * gdet c) : ℂ) • Φ) (g.val * X * c.valᵀ)) =
      smallP μ' σ ν α fun Y => Ψ ((invT g').val * Y * (c⁻¹).val) := by
  funext h
  have h1 := bigZetaIntegral_equivariant μ ϖ σ ν β hg hc ((ν (gdet g * gdet g' * gdet c) : ℂ) • Φ) h
  rw [bigZetaIntegral_smul, H] at h1
  rw [smallP_change μ' σ ν α hg' hc, hν]
  refine mul_left_cancel₀ (Units.ne_zero (ν (gdet g))) ?_
  rw [h1]
  simp only [map_mul, Units.val_mul]
  ring

end Local

section Lin

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.FlipMatch (coX coY pairM)
open scoped GlobalTheory.VacAny ValuativeRel

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d r s r' s' : ℕ} {X : Spc F E n} {W : Spc F E d} {B : Base F E} {v : Pl (F := F)}

theorem psiLoc_zero' (ψ : AddChar (AF F) ℂ) (v : Pl (F := F)) : psiLoc ψ v 0 = 1 := by
  rw [psiLoc, map_zero, map_zero]
  exact AddChar.map_zero_eq_one ψ

theorem coX_mul (t : E →ₐ[F] Fv F v) (b g : GL (Fin n) (Fv F v)) (c k : GL (Fin d) (Fv F v))
    (u : Matrix (Fin n) (Fin d) (AE F E)) : coX t b c u = g.val * coX t (b * g) (c * k) u * k.valᵀ := by
  simp only [coX, mul_inv_rev, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [← Matrix.transpose_mul k.val, Units.mul_inv, Matrix.transpose_one, Matrix.mul_one, ← Matrix.mul_assoc g.val,
    Units.mul_inv, Matrix.one_mul]

theorem coY_mul (t : E →ₐ[F] Fv F v) (b g : GL (Fin n) (Fv F v)) (c k : GL (Fin d) (Fv F v))
    (u : Matrix (Fin n) (Fin d) (AE F E)) : coY σ X W t (b * g) (c * k) u = g.valᵀ * coY σ X W t b c u * k.val := by
  simp only [coY, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_neg, Matrix.neg_mul]

theorem pairM_mul {K : Type} [CommRing K] {m n : Type} [Fintype m] [Fintype n]
    (A : Matrix m m K) (Y : Matrix m n K) (C : Matrix n n K) (P : Matrix m n K) :
    pairM (A * Y * C) P = pairM Y (Aᵀ * P * Cᵀ) := GlobalTheory.LinWShape.frob_mul A Y C P

theorem pairM_lin {K : Type} [Field K] {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (l : Matrix m n K →ₗ[K] K) (Y : Matrix m n K) : pairM Y (Matrix.of fun i j => l (Matrix.single i j 1)) = l Y :=
  (GlobalTheory.LinWShape.linForm_eq l Y).symm

theorem pairM_neg {K : Type} [CommRing K] {m n : Type} [Fintype m] [Fintype n] (Y P : Matrix m n K) :
    pairM Y (-P) = -pairM Y P := by simp [pairM]

theorem linW_change (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (M : Model σ X W)
    (t : E →ₐ[F] Fv F v) (b g : GL (Fin n) (Fv F v)) (c k : GL (Fin d) (Fv F v)) {ι ι₂} (hι : M.IsLinW B.ψ t b c ι)
    (hι₂ : M.IsLinW B.ψ t (b * g) (c * k) ι₂) :
    ∃ z : ℂ, ∀ φ ∈ SB (Fin n × Fin d → Fv F v), (fun Y => ι φ (g.val * Y * k.valᵀ)) = z • ι₂ φ := by
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt _ hB.std.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one _ hB.std v
  have hsb := fun (u : Matrix (Fin n) (Fin d) (AE F E)) φ hφ =>
    GlobalTheory.SchrSB.schr_mem_SB B.ψ hB.std.1 v (GlobalTheory.LatVac.locCo M.co v u) φ hφ
  have act := fun b c u hu hp φ hφ => (GlobalTheory.T.heisenbergOperator_isotropic_translation_char_split hB.cm X W hX.herm hW.skew (GlobalTheory.FinUniq.det_ne_zero_herm hX)
    (GlobalTheory.FinUniq.det_ne_zero_skew hW) M B.ψ hB.std t b c u hu hp φ hφ _ (hsb u φ hφ)
    (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hu φ)).1
  choose zX hzX using fun Z => (GlobalTheory.T.splitPlace_characterAndTranslationCoords_surjective F E σ B hB n d _ _ _ _ X W hX hW v t (b * g) (c * k) Z).1
  have hzX0 := fun Z => (hzX Z).2.1
  have hzXe := fun Z => (hzX Z).2.2
  have hzX := fun Z => (hzX Z).1
  choose zY hzY using fun Z => (GlobalTheory.T.splitPlace_characterAndTranslationCoords_surjective F E σ B hB n d _ _ _ _ X W hX hW v t (b * g) (c * k) Z).2
  have hzY0 := fun Z => (hzY Z).2.1
  have hzYe := fun Z => (hzY Z).2.2
  have hzY := fun Z => (hzY Z).1
  have y0 : ∀ b c Z, coY σ X W t b c (zX Z) = 0 := fun b c Z => by simp [coY, hzX0]
  have x0 : ∀ b c Z, coX t b c (zY Z) = 0 := fun b c Z => by simp [coX, hzY0]
  have p0 : ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), pairM Y 0 = 0 := fun Y => by simp [pairM]
  have p0' : ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), pairM 0 Y = 0 := fun Y => by simp [pairM]
  refine GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin n × Fin d → Fv F v)) (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1 ι₂
    (fun φ Y => ι φ (g.val * Y * k.valᵀ)) (Model.IsLin.bij hι₂) (fun x _ y _ a => by rw [map_add (f := _), map_smul]; rfl)
    (fun C φ => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (zX C)) φ)
    (fun l φ => schr (GlobalTheory.LatVac.psiAt B.ψ v)
      (GlobalTheory.LatVac.locCo M.co v (zY (Matrix.of fun i j => l (Matrix.single i j 1)))) φ)
    (fun C x hx => ⟨hsb _ x hx, funext fun Y => ?_, funext fun Y => ?_⟩)
    (fun l x hx => ⟨hsb _ x hx, funext fun Y => ?_, funext fun Y => ?_⟩)
  · rw [act _ _ _ (hzX C) (by rw [y0, p0]) x hx ι₂ hι₂, y0, p0, psiLoc_zero', one_mul, hzXe]
  · rw [act _ _ _ (hzX C) (by rw [y0, p0]) x hx ι hι, y0, p0, psiLoc_zero', one_mul, coX_mul t b g c k, hzXe,
      Matrix.mul_add, Matrix.add_mul]
  · rw [act _ _ _ (hzY _) (by rw [x0, p0']) x hx ι₂ hι₂, x0, add_zero, hzYe, pairM_lin]
    rfl
  · rw [act _ _ _ (hzY _) (by rw [x0, p0']) x hx ι hι, x0, add_zero, pairM_mul, Matrix.transpose_transpose, ← coY_mul,
      hzYe, pairM_lin]
    rfl

theorem linBar_change (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') (M : Model σ X W)
    (t : E →ₐ[F] Fv F v) (b g : GL (Fin n) (Fv F v)) (c k : GL (Fin d) (Fv F v)) {ι ι₂} (hι : M.IsLinBar B.ψ t b c ι)
    (hι₂ : M.IsLinBar B.ψ t (b * g) (c * k) ι₂) :
    ∃ z : ℂ, ∀ φ ∈ SB (Fin n × Fin d → Fv F v),
      (fun Y => ι φ ((GlobalTheory.SplitFlip.invT g).val * Y * (k⁻¹).val)) = z • ι₂ φ := by
  have hψc : Continuous (GlobalTheory.LatVac.psiAt B.ψ v) := GlobalTheory.SchrSB.continuous_psiAt _ hB.std.1 v
  have hψ1 : GlobalTheory.LatVac.psiAt B.ψ v ≠ 1 := GlobalTheory.PsiNontriv.psiAt_ne_one _ hB.std v
  have hsb := fun (u : Matrix (Fin n) (Fin d) (AE F E)) φ hφ =>
    GlobalTheory.SchrSB.schr_mem_SB B.ψ hB.std.1 v (GlobalTheory.LatVac.locCo M.co v u) φ hφ
  have act := fun b c u hu hp φ hφ => (GlobalTheory.T.heisenbergOperator_isotropic_translation_char_split hB.cm X W hX.herm hW.skew (GlobalTheory.FinUniq.det_ne_zero_herm hX)
    (GlobalTheory.FinUniq.det_ne_zero_skew hW) M B.ψ hB.std t b c u hu hp φ hφ _ (hsb u φ hφ)
    (GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v u hu φ)).2
  choose zX hzX using fun Z => (GlobalTheory.T.splitPlace_characterAndTranslationCoords_surjective F E σ B hB n d _ _ _ _ X W hX hW v t (b * g) (c * k) Z).1
  have hzX0 := fun Z => (hzX Z).2.1
  have hzXe := fun Z => (hzX Z).2.2
  have hzX := fun Z => (hzX Z).1
  choose zY hzY using fun Z => (GlobalTheory.T.splitPlace_characterAndTranslationCoords_surjective F E σ B hB n d _ _ _ _ X W hX hW v t (b * g) (c * k) Z).2
  have hzY0 := fun Z => (hzY Z).2.1
  have hzYe := fun Z => (hzY Z).2.2
  have hzY := fun Z => (hzY Z).1
  have y0 : ∀ b c Z, coY σ X W t b c (zX Z) = 0 := fun b c Z => by simp [coY, hzX0]
  have x0 : ∀ b c Z, coX t b c (zY Z) = 0 := fun b c Z => by simp [coX, hzY0]
  have p0 : ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), pairM Y 0 = 0 := fun Y => by simp [pairM]
  have p0' : ∀ Y : Matrix (Fin n) (Fin d) (Fv F v), pairM 0 Y = 0 := fun Y => by simp [pairM]
  have eY : ∀ u, coY σ X W t b c u = (GlobalTheory.SplitFlip.invT g).val * coY σ X W t (b * g) (c * k) u * (k⁻¹).val := fun u => by
    have := coY_mul (σ := σ) (X := X) (W := W) t (b * g) g⁻¹ (c * k) k⁻¹ u
    rwa [mul_inv_cancel_right, mul_inv_cancel_right] at this
  have eX : ∀ u, coX t (b * g) (c * k) u = (GlobalTheory.SplitFlip.invT g).valᵀ * coX t b c u * (k⁻¹).valᵀ := fun u => by
    have := coX_mul t (b * g) g⁻¹ (c * k) k⁻¹ u
    rwa [mul_inv_cancel_right, mul_inv_cancel_right] at this
  refine GlobalTheory.T.eq_smul_of_commute_heisenberg_linearModel_schwartzBruhat (SB (Fin n × Fin d → Fv F v)) (GlobalTheory.LatVac.psiAt B.ψ v) hψc hψ1 ι₂
    (fun φ Y => ι φ ((GlobalTheory.SplitFlip.invT g).val * Y * (k⁻¹).val)) (Model.IsLin.bij hι₂)
    (fun x _ y _ a => by rw [map_add (f := _), map_smul]; rfl)
    (fun C φ => schr (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.LatVac.locCo M.co v (zY C)) φ)
    (fun l φ => schr (GlobalTheory.LatVac.psiAt B.ψ v)
      (GlobalTheory.LatVac.locCo M.co v (zX (-Matrix.of fun i j => l (Matrix.single i j 1)))) φ)
    (fun C x hx => ⟨hsb _ x hx, funext fun Y => ?_, funext fun Y => ?_⟩)
    (fun l x hx => ⟨hsb _ x hx, funext fun Y => ?_, funext fun Y => ?_⟩)
  · rw [act _ _ _ (hzY C) (by rw [x0, p0']) x hx ι₂ hι₂, x0, p0, neg_zero, psiLoc_zero', one_mul, hzYe]
  · rw [act _ _ _ (hzY C) (by rw [x0, p0']) x hx ι hι, x0, p0, neg_zero, psiLoc_zero', one_mul, eY, hzYe,
      Matrix.mul_add, Matrix.add_mul]
  · rw [act _ _ _ (hzX _) (by rw [y0, p0]) x hx ι₂ hι₂, y0, add_zero, hzXe, pairM_neg, neg_neg, pairM_lin]
    rfl
  · rw [act _ _ _ (hzX _) (by rw [y0, p0]) x hx ι hι, y0, add_zero, pairM_mul, ← eX, hzXe, pairM_neg, neg_neg, pairM_lin]
    rfl

theorem mem_O_iff (v : Pl (F := F)) (a : Fv F v) : a ∈ 𝒪[Fv F v] ↔ a ∈ v.adicCompletionIntegers F := by
  rw [Valuation.mem_integer_iff, ← map_one (ValuativeRel.valuation (Fv F v)), ← Valuation.Compatible.vle_iff_le,
    IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
    ← map_one (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))]
  exact Iff.rfl

theorem mem_KO_of_bases {t : E →ₐ[F] Fv F v} {L : Submodule (𝓞 E) (Fin n → E)} {b b₂ : GL (Fin n) (Fv F v)}
    (h : IsSplitBasis t L b) (h₂ : IsSplitBasis t L b₂) : b⁻¹ * b₂ ∈ GlobalTheory.SplitWeil.KO (Fv F v) (Fin n) := by
  have := mem_GLint_iff.1 (h.iff_mem_GLint.1 h₂)
  rw [GlobalTheory.SplitFlip.mem_KO_iff]
  exact ⟨fun i j => (mem_O_iff v _).2 (this.1 i j), fun i j => (mem_O_iff v _).2 (this.2 i j)⟩

variable {a a' : ℕ}

def kap (G : Geo σ a a') (V : Spc F E a) (V' : Spc F E a') (Z : Spc F E (a + a')) (v : Pl (F := F)) : (Fv F v)ˣ :=
  GlobalTheory.SplitFlip.gdet ((G.V.bas v)⁻¹ * V.bas v) * GlobalTheory.SplitFlip.gdet ((G.V'.bas v)⁻¹ * V'.bas v) *
    GlobalTheory.SplitFlip.gdet ((G.W.bas v)⁻¹ * Z.bas v)

variable {G : Geo σ a a'} {V : Spc F E a} {V' : Spc F E a'} {Z : Spc F E (a + a')}

theorem valuation_kap (hG : G.IsGood B) (hG₂ : (reG G V V' Z).IsGood B) (v : B.P) :
    ValuativeRel.valuation (Fv F v.1) (kap G V V' Z v.1 : Fv F v.1) = 1 := by
  rw [kap, Units.val_mul, Units.val_mul, map_mul, map_mul,
    GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO (mem_KO_of_bases (b₂ := V.bas v) (hG.hV.bas v) (hG₂.hV.bas v)),
    GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO (mem_KO_of_bases (b₂ := V'.bas v) (hG.hV'.bas v) (hG₂.hV'.bas v)),
    GlobalTheory.SplitFlip.valuation_gdet_of_mem_KO (mem_KO_of_bases (b₂ := Z.bas v) (hG.hW.bas v) (hG₂.hW.bas v)), one_mul, one_mul]


attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL in
theorem zeta_rel (hB : B.IsGood σ) (hG : G.IsGood B) (hG₂ : (reG G V V' Z).IsGood B) {X : Chars F E}
    {Rf S : FinMaps F a a'} {v : B.P} (h : IsZetaAt B G X Rf v) (h₂ : IsZetaAt B (reG G V V' Z) X S v)
    {φ φ'} (hφ : φ ∈ SB (Fin a × Fin (a + a') → Fv F v.1)) (hφ' : φ' ∈ SB (Fin a' × Fin (a + a') → Fv F v.1))
    (e : Rf.p v φ = Rf.p' v φ') : S.p v ((chrW X.ν (B.τ v) (kap G V V' Z v.1) : ℂ) • φ) = S.p' v φ' := by
  obtain ⟨ι, ι', hι, hι', hv, hv', H⟩ := h
  obtain ⟨ι₂, ι₂', hι₂, hι₂', hv₂, hv₂', H₂⟩ := h₂
  have j₂ : G.M.IsLinW B.ψ (B.τ v) (G.V.bas v * ((G.V.bas v)⁻¹ * V.bas v)) (G.W.bas v * ((G.W.bas v)⁻¹ * Z.bas v)) ι₂ := by
    rw [mul_inv_cancel_left, mul_inv_cancel_left]
    exact ⟨hι₂.1, hι₂.2, hι₂.3⟩
  have j₂' : G.M'.IsLinBar B.ψ (B.τ v) (G.V'.bas v * ((G.V'.bas v)⁻¹ * V'.bas v))
      (G.W.bas v * ((G.W.bas v)⁻¹ * Z.bas v)) ι₂' := by
    rw [mul_inv_cancel_left, mul_inv_cancel_left]
    exact ⟨hι₂'.1, hι₂'.2, hι₂'.3⟩
  obtain ⟨z, hz⟩ := linW_change hB hG.hV hG.hW G.M (B.τ v) _ _ _ _ hι j₂
  obtain ⟨z', hz'⟩ := linBar_change hB hG.hV' hG.hW G.M' (B.τ v) _ _ _ _ hι' j₂'
  have z1 : z = 1 := by
    have := congrFun (hz _ (hG.hM.vac v).1) 0
    rw [show ι₂ (G.M.vac v) = _ from hv₂, hv, Matrix.mul_zero, Matrix.zero_mul, Pi.smul_apply,
      Set.indicator_of_mem (by intro i j; exact zero_mem _)] at this
    simpa using this.symm
  have z1' : z' = 1 := by
    have := congrFun (hz' _ (hG.hM'.vac v).1) 0
    rw [show ι₂' (G.M'.vac v) = _ from hv₂', hv', Matrix.mul_zero, Matrix.zero_mul, Pi.smul_apply,
      Set.indicator_of_mem (by intro i j; exact zero_mem _)] at this
    simpa using this.symm
  subst z1 z1'
  have hs := (SB _).smul_mem (chrW X.ν (B.τ v) (kap G V V' Z v.1) : ℂ) hφ
  rw [H₂ _ hs _ hφ', ← one_smul ℂ (ι₂ _), ← one_smul ℂ (ι₂' _), ← hz _ hs, ← hz' _ hφ', map_smul]
  letI : MeasurableSpace (Fv F v.1) := borel _
  haveI : BorelSpace (Fv F v.1) := ⟨rfl⟩
  exact zeta_change _ _ _ _ _ _ _ (fun x => by
      simp only [Chars.ν, chrW, locChar, MonoidHom.comp_apply, MonoidHom.div_apply, map_div, div_mul_cancel])
    (mem_KO_of_bases (hG.hV.bas v) (hG₂.hV.bas v)) (mem_KO_of_bases (hG.hV'.bas v) (hG₂.hV'.bas v))
    (mem_KO_of_bases (hG.hW.bas v) (hG₂.hW.bas v)) _ _ ((H _ hφ _ hφ').1 e)

end Lin

end GlobalTheory.ReBase

end
end

section -- merged from Development.AutomorphicArithmetic.LocalEmbeddings.ReBaseArch
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace GlobalTheory.ReBase

section Proj

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {ι : Type} [Fintype ι] [DecidableEq ι]

noncomputable def prM (e : R) (he : e * e = e) (ι : Type) [Fintype ι] [DecidableEq ι] : Matrix ι ι A →* Matrix ι ι A :=
  _root_.UpperTheory.Reformulated.B.IdempotentMatrixMonoidHom.prM e he ι

theorem prM_apply (e : R) (he : e * e = e) (M : Matrix ι ι A) : prM e he ι M = e • M + (1 - e) • 1 := rfl

def prU (c : A →ₐ[R] A) (J : Matrix ι ι A) (e : R) (he : e * e = e) : UG c J →* UG c J :=
  ((Units.map (prM e he ι)).comp (UG c J).subtype).codRestrict _ fun g => by
    have hg : g.1.1ᵀ * J * g.1.1.map c = J := g.2
    have h1 : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he, sub_self]
    have h2 : (1 - e) * e = 0 := by rw [mul_comm, h1]
    have h3 : (1 - e) * (1 - e) = 1 - e := by rw [mul_sub, mul_one, h2, sub_zero]
    show (e • g.1.1 + (1 - e) • 1)ᵀ * J * (e • g.1.1 + (1 - e) • (1 : Matrix ι ι A)).map c = J
    have hm : (e • g.1.1 + (1 - e) • (1 : Matrix ι ι A)).map c = e • g.1.1.map c + (1 - e) • 1 := by
      ext i j
      simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, map_add (f := _), map_smul, Matrix.one_apply]
      split_ifs <;> simp
    rw [hm]
    simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_one, Matrix.add_mul, Matrix.mul_add,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_add, he, h1, h2, h3,
      zero_smul, add_zero, zero_add, Matrix.one_mul, Matrix.mul_one, hg]
    rw [← add_smul, add_sub_cancel, one_smul]

theorem continuous_prU [TopologicalSpace A] [ContinuousAdd A] [ContinuousConstSMul R A] (c : A →ₐ[R] A)
    (J : Matrix ι ι A) (e : R) (he : e * e = e) : Continuous (prU c J e he) := by
  refine Continuous.subtype_mk ?_ _
  have h : Continuous (prM (A := A) e he ι) := (continuous_id.const_smul e).add continuous_const
  exact (Continuous.units_map _ h).comp continuous_subtype_val

theorem smul_det_prM (e : R) (he : e * e = e) (M : Matrix ι ι A) {u : R} (hu : u * e = 0) :
    u • ((prM e he ι M).det - 1) = 0 := by
  let I : Ideal A := Ideal.span {algebraMap R A e}
  have h0 : Ideal.Quotient.mk I (algebraMap R A e) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
  have h1 : (Ideal.Quotient.mk I).mapMatrix (prM e he ι M) = 1 := by
    ext i j
    simp only [prM_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply]
    simp only [map_add (f := _), Algebra.smul_def, map_mul, map_sub, h0, map_one, Matrix.one_apply]
    split_ifs <;> simp
  have h2 : (prM e he ι M).det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, RingHom.map_det, h1, Matrix.det_one, map_one, sub_self]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 h2
  rw [← hy, Algebra.smul_def, mul_left_comm, ← map_mul, hu, map_zero, mul_zero]

theorem prM_mul {κ : Type} [Fintype κ] [DecidableEq κ] (e : R) (he : e * e = e) {M : Matrix ι ι A} {N : Matrix κ κ A}
    {D : Matrix ι κ A} (h : M * D = D * N) : prM e he ι M * D = D * prM e he κ N := by
  rw [prM_apply, prM_apply, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.mul_smul, h, Matrix.one_mul, Matrix.mul_one]

theorem prM_fromBlocks (e : R) (he : e * e = e) {M : Matrix ι ι A} (h : (1 - e) • (M - 1) = 0) :
    prM e he (ι ⊕ ι) (Matrix.fromBlocks M 0 0 1) = Matrix.fromBlocks M 0 0 1 := by
  rw [smul_sub, sub_eq_zero] at h
  rw [prM_apply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_smul, Matrix.fromBlocks_add,
    ← add_smul e (1 - e) (1 : Matrix ι ι A), ← h]
  simp only [← add_smul, add_sub_cancel, one_smul]

end Proj

open GlobalTheory.WeilSchUnique

variable {F : Type} [Field F] [NumberField F] {E : Type} [Field E] [NumberField E] [Algebra F E]


variable (F) in
def eInf : AF F := ((1 : InfiniteAdeleRing F), (0 : FiniteAdeleRing (𝓞 F) F))

theorem eInf_mul : eInf F * eInf F = eInf F := Prod.ext (one_mul (1 : InfiniteAdeleRing F)) (zero_mul (0 : FiniteAdeleRing (𝓞 F) F))

theorem mul_eInf {u : AF F} (hu : evI F u = 0) : u * eInf F = 0 := by
  have h0 : u.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
  refine Prod.ext ?_ ?_
  · show u.1 * 1 = 0
    rw [h0, zero_mul]
  · show u.2 * 0 = 0
    rw [mul_zero]

theorem evI_one_sub_eInf : evI F (1 - eInf F) = 0 := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F (1 - 1) = 0
  rw [sub_self, map_zero]

theorem member_arch_eq (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) {a b : ℕ} (JA : Matrix (Fin a) (Fin a) E)
    (JB : Matrix (Fin b) (Fin b) E) (ε : ℤˣ) (hJ : ∀ i j, σ (JB j i) = ((ε : ℤ) : E) * JB i j) (hdet : JB.det ≠ 0)
    (ψ : AddChar (AF F) ℂ) (hψ : (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ)))) {κ : Type} [Fintype κ]
    (d : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ) (χ χ₁ : Chr F E)
    (hχ : ∀ z : (AE F E)ˣ, At (evI F) ((z : AE F E) - 1) → χ z = χ₁ z)
    (om om₁ : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) →* Module.End ℂ ((κ → AF F) → ℂ))
    (h : IsUWeilB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) d χ om)
    (h₁ : IsUWeilB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) d χ₁ om₁) :
    ∀ g, At (evI F) (g.1.1 - 1) → ∀ Φ ∈ schA F κ, om g Φ = om₁ g Φ := by
  obtain ⟨-, dd, omd, hdd, ⟨-, hS, hR⟩, hres⟩ := h
  obtain ⟨-, dd₁, omd₁, hdd₁, ⟨-, hS₁, hR₁⟩, hres₁⟩ := h₁
  have hee : ∀ w, dd₁.e w = dd.e w := fun w => by
    rw [← Matrix.fromCols_toCols w, hdd, hdd₁]
  have hrho : ∀ w, dd₁.rho ψ w = dd.rho ψ w := fun w => by simp only [Darboux.rho, hee]
  have inv_mul : ∀ (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB))) φ, omd p (omd p⁻¹ φ) = φ := fun p φ => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  obtain ⟨φz, hφz, hφz0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F (κ ⊕ κ)

  have key : ∀ p, ∃ c : ℂ, ∀ φ ∈ schA F (κ ⊕ κ), omd₁ p φ = c • omd p φ := fun p => by
    obtain ⟨c, hc⟩ := scalar_of_commute ψ hψ (omd p⁻¹ * omd₁ p)
      (fun l hl => by
        rw [Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
        exact hS₁.adm p _ (hS.adm p⁻¹ l hl))
      (fun w φ hφ => by
        obtain ⟨w', rfl⟩ := dd.e.surjective w
        have e1 : schr ψ (dd.e w') = dd.rho ψ w' := rfl
        rw [e1, Module.End.mul_apply, Module.End.mul_apply]
        calc omd p⁻¹ (omd₁ p (dd.rho ψ w' φ)) = omd p⁻¹ (omd₁ p (dd₁.rho ψ w' φ)) := by rw [hrho]
          _ = omd p⁻¹ (dd₁.rho ψ (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p w') (omd₁ p φ)) := by rw [hS₁.impl p w' φ hφ]
          _ = omd p⁻¹ (dd.rho ψ (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p w') (omd₁ p φ)) := by rw [hrho]
          _ = dd.rho ψ (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p⁻¹ (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) p w')) (omd p⁻¹ (omd₁ p φ)) :=
              hS.impl _ _ _ (hS₁.pres p φ hφ)
          _ = _ := by rw [actB_inv_actB])
    refine ⟨c, fun φ hφ => ?_⟩
    have := congrArg (omd p) (hc φ hφ)
    rwa [Module.End.mul_apply, inv_mul, map_smul] at this

  choose cf hcf using key
  have hsp : ∀ p, ∀ φ ∈ schA F (κ ⊕ κ), omd p φ ∈ schA F (κ ⊕ κ) := fun p φ hφ => hS.pres p φ hφ
  have huniq : ∀ p (c : ℂ), (∀ φ ∈ schA F (κ ⊕ κ), omd₁ p φ = c • omd p φ) → c = cf p := fun p c hc => by
    have h1 := hc _ (hsp p⁻¹ φz hφz)
    rw [hcf p _ (hsp p⁻¹ φz hφz), inv_mul] at h1
    have h2 := congrFun h1 0
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    exact (mul_right_cancel₀ hφz0 h2).symm
  have hmul : ∀ p q, cf (p * q) = cf p * cf q := fun p q => (huniq (p * q) _ fun φ hφ => by
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hcf q φ hφ, map_smul,
      hcf p _ (hsp q φ hφ), smul_smul, mul_comm]).symm
  have hone : cf 1 = 1 := (huniq 1 1 fun φ _ => by simp).symm
  let cM : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) →* ℂ := { toFun := cf, map_one' := hone, map_mul' := hmul }
  let c := cM.toHomUnits
  have hcv : ∀ p, ((c p : ℂˣ) : ℂ) = cf p := fun p => rfl
  have hcont_cf : Continuous cf := by
    refine continuous_iff_continuousAt.2 fun p₀ => ?_
    have hφ := hsp p₀⁻¹ φz hφz
    have hf := hS.cont _ (evalZero_mem_adelicSchwartzAdmittedForms (κ ⊕ κ)) _ hφ
    have hf₁ := hS₁.cont _ (evalZero_mem_adelicSchwartzAdmittedForms (κ ⊕ κ)) _ hφ
    simp only [LinearMap.proj_apply] at hf hf₁
    have h0 : omd p₀ (omd p₀⁻¹ φz) 0 ≠ 0 := by rw [inv_mul]; exact hφz0
    refine (hf₁.continuousAt.div hf.continuousAt h0).congr ?_
    filter_upwards [hf.continuousAt.eventually_ne h0] with p hp
    show omd₁ p _ 0 / omd p _ 0 = cf p
    rw [hcf p _ hφ]
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  have hcont : Continuous c := by
    refine Units.continuous_iff.2 ⟨hcont_cf, ?_⟩
    have : (fun p => ((c p)⁻¹ : ℂˣ).val) = fun p => (cf p)⁻¹ := funext fun p => by
      rw [Units.val_inv_eq_inv_val, hcv]
    rw [this]
    exact hcont_cf.inv₀ fun p => by rw [← hcv]; exact (c p).ne_zero
  obtain ⟨l, hl, hlinv, φ₀, hφ₀, hl0⟩ := GlobalTheory.T.exists_diagonalLagrangian_invariant_form F ψ κ
  have hP : ∀ (p : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB))) (t : GL (Fin b) (AE F E)),
      ((p : GL (Fin b ⊕ Fin b) (AE F E)) : Matrix _ _ (AE F E)) * diagCols (Fin b) = diagCols (Fin b) * t.1 →
        χ (Matrix.GeneralLinearGroup.det t) = χ₁ (Matrix.GeneralLinearGroup.det t) → c p = 1 := fun p t hpt hχt => by
    have hφ := hsp p⁻¹ φ₀ hφ₀
    have e1 := hR l hl (fun z φ hφ => by
      convert hlinv (d.e z).1 (d.e z).2 φ hφ using 2; exact congrFun (dd_rho_diag hdd ψ z) φ) p t hpt _ hφ
    have e2 := hR₁ l hl (fun z φ hφ => by
      convert hlinv (d.e z).1 (d.e z).2 φ hφ using 2; exact congrFun (dd_rho_diag hdd₁ ψ z) φ) p t hpt _ hφ
    rw [hχt, ← e2, hcf p _ hφ, inv_mul, map_smul, smul_eq_mul] at e1
    refine Units.ext ?_
    rw [hcv, Units.val_one]
    exact mul_right_cancel₀ hl0 (by rw [one_mul]; exact e1.symm)
  haveI : ContinuousAdd (AE F E) := IsModuleTopology.toContinuousAdd (AF F) (AE F E)
  haveI : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul (AF F) (AE F E)
  let π := prU (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) (eInf F) eInf_mul
  have hc1 := GlobalTheory.T.doubledUnitary_character_trivial_of_siegel F E σ hσ b JB ε hJ hdet (c.comp π) (hcont.comp (continuous_prU _ _ _ _)) (fun p t hpt => by
    refine hP (π p) (Units.map (prM (eInf F) eInf_mul (Fin b)) t) ?_ (hχ _ fun u hu => ?_)
    · exact prM_mul (eInf F) eInf_mul hpt
    · exact smul_det_prM (eInf F) eInf_mul t.1 (mul_eInf hu))
  intro g hg Φ hΦ
  obtain ⟨gd, hgd⟩ := GlobalTheory.T.exists_unitaryDoubled_blockDiag_one (AF F) (AE F E) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (Fin b) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB) g
  have hπ : π gd = gd := by
    refine Subtype.ext (Units.ext ?_)
    have h0 : (1 - eInf F) • (g.1.1 - 1) = 0 := hg _ evI_one_sub_eInf
    show prM (eInf F) eInf_mul _ gd.1.1 = gd.1.1
    rw [hgd]
    exact prM_fromBlocks _ _ h0
  have hcf1 : cf gd = 1 := by
    have := congrArg (fun f => f gd) hc1
    change c (π gd) = 1 at this
    rw [hπ] at this
    rw [← hcv, this]; rfl
  obtain ⟨φ₂, hφ₂, hφ₂0⟩ := GlobalTheory.T.exists_adelicSchwartz_ne_zero_at_origin F κ
  have hb := GlobalTheory.T.productFunctionOnSumCoords_mem_adelicSchwartzSpace F κ κ Φ hΦ φ₂ hφ₂
  have e := hres g gd hgd Φ hΦ φ₂ hφ₂
  have e₁ := hres₁ g gd hgd Φ hΦ φ₂ hφ₂
  rw [hcf gd _ hb, hcf1, one_smul, e] at e₁
  funext x
  have := congrFun e₁ (Sum.elim x 0)
  simp only [boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr] at this
  exact mul_right_cancel₀ hφ₂0 this

theorem weil_arch_eq {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
    {ψ : AddChar (AF F) ℂ} {χX χW χX₁ χW₁ : Chr F E} (hψ : (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ)))) (hX : ∀ i j, σ (X.J j i) = X.J i j) (hXd : X.J.det ≠ 0)
    (hW : ∀ i j, σ (W.J j i) = -W.J i j) (hWd : W.J.det ≠ 0)
    (hχX : ∀ z : (AE F E)ˣ, At (evI F) ((z : AE F E) - 1) → χX z = χX₁ z)
    (hχW : ∀ z : (AE F E)ˣ, At (evI F) ((z : AE F E) - 1) → χW z = χW₁ z)
    {om om₁ : Rep σ X W} (h : M.IsWeil ψ χX χW om) (h₁ : M.IsWeil ψ χX₁ χW₁ om₁)
    {g : UA σ X.J} (hg : g ∈ UAt σ X (evI F)) {k : UA σ W.J} (hk : k ∈ UAt σ W (evI F)) :
    ∀ Φ ∈ schA F (Fin n × Fin d), om (g, k) Φ = om₁ (g, k) Φ := by
  intro Φ hΦ
  obtain ⟨hB, ⟨d', hd', hA⟩, -⟩ := h
  obtain ⟨hB₁, ⟨d'₁, hd'₁, hA₁⟩, -⟩ := h₁
  have eW : ∀ i j, σ (W.J j i) = (((-1 : ℤˣ) : ℤ) : E) * W.J i j := fun i j => by simp [hW i j]
  have eX : ∀ i j, σ (X.J j i) = (((1 : ℤˣ) : ℤ) : E) * X.J i j := fun i j => by simp [hX i j]
  have uB := member_arch_eq σ hσ X.J W.J (-1) eW hWd ψ hψ M.co χX χX₁ hχX _ _ hB hB₁
  have he : d'₁.e = d'.e := LinearEquiv.ext fun y => by rw [← Matrix.transpose_transpose y, hd'₁, hd']
  obtain ⟨e₁, f₁⟩ := d'₁
  obtain ⟨e₂, f₂⟩ := d'
  simp only at he
  subst he
  have uA := member_arch_eq σ hσ W.J X.J 1 eX hXd ψ hψ _ χW χW₁ hχW _ _ hA hA₁
  have hx : ((g, k) : UA σ X.J × UA σ W.J) = (g, 1) * (1, k) := by simp
  rw [hx, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  have h1 : om (1, k) Φ = om₁ (1, k) Φ := uB k hk Φ hΦ
  rw [h1]
  exact uA g hg _ (hB₁.1.pres k Φ hΦ)

end GlobalTheory.ReBase

end
end

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ReBase

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {V : Spc F E a} {V' : Spc F E a'} {Z : Spc F E (a + a')}

theorem polMatch_iso {R R₃ : RealMaps F a a'} {Rf Rf₃ : FinMaps F a a'} {ψ₀ : R.Pi ≃ₗ[ℂ] R₃.Pi} {l₀ : ℂ}
    {ψ : ∀ v, Rf.Pi v ≃ₗ[ℂ] Rf₃.Pi v} {l : Pl (F := F) → ℂ} (hl1 : ∀ v ∉ X.T, l v = 1)
    (hR : ∀ f ∈ G.M.Pol B.ψ B.emb, R₃.p f = ψ₀ (R.p f)) (hR' : ∀ f ∈ G.M'.Pol B.ψ B.emb, R₃.p' f = l₀ • ψ₀ (R.p' f))
    (hRf : ∀ v, ∀ φ ∈ SB (Fin a × Fin (a + a') → Fv F v), Rf₃.p v φ = ψ v (Rf.p v φ))
    (hRf' : ∀ v, ∀ φ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Rf₃.p' v φ = l v • ψ v (Rf.p' v φ))
    {Φ Φ'} (hM : PolMatch B G X R Rf Φ Φ') : PolMatch B G X R₃ Rf₃ ((l₀ * ∏ v ∈ X.T, l v) • Φ) Φ' := by
  set Λ : ℂ := l₀ * ∏ v ∈ X.T, l v with hΛdef
  obtain ⟨T, hT, m, m', f, φ, f', φ', hf, hf', hΦ, hΦ', heq⟩ := hM
  have hΛT : l₀ * ∏ v ∈ T, l v = Λ := by
    rw [hΛdef, Finset.prod_subset hT (fun v _ hv => hl1 v hv)]
  refine ⟨T, hT, m, m', fun i => Λ • f i, φ, f', φ', fun i => ⟨Submodule.smul_mem _ _ (hf i).1, (hf i).2⟩, hf', ?_, hΦ', ?_⟩
  · rw [hΦ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
  · let L := TensorProduct.map ψ₀.toLinearMap (PiTensorProduct.map fun v : T => (ψ v).toLinearMap)
    have h1 := congrArg L heq
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, L, TensorProduct.map_tmul, PiTensorProduct.map_tprod, LinearEquiv.coe_coe] at h1
    have lhs : ∀ i, R₃.p (Λ • f i) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf₃.p v (φ i v)) =
        Λ • (ψ₀ (R.p (f i)) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => ψ v (Rf.p v (φ i v))) := by
      intro i
      have e : (fun v : T => Rf₃.p v (φ i v)) = fun v : T => ψ v (Rf.p v (φ i v)) :=
        funext fun v => hRf v _ ((hf i).2.1 v)
      rw [e, map_smul, hR _ (hf i).1, ← TensorProduct.smul_tmul']
    have rhs : ∀ j, R₃.p' (f' j) ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ fun v : T => Rf₃.p' v (φ' j v)) =
        Λ • (ψ₀ (R.p' (f' j)) ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ fun v : T => ψ v (Rf.p' v (φ' j v))) := by
      intro j
      have e : (fun v : T => Rf₃.p' v (φ' j v)) = fun v : T => l v • ψ v (Rf.p' v (φ' j v)) :=
        funext fun v => hRf' v _ ((hf' j).2.1 v)
      rw [e, MultilinearMap.map_smul_univ, hR' _ (hf' j).1, ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
      simp only [RingHom.id_apply]
      rw [Finset.prod_coe_sort, hΛT]
    simp only [lhs, rhs, ← Finset.smul_sum, h1]


variable (B G V V' Z) in
def kapId : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ :=
  ∏ v : B.P, locIdele F (splitPrime (B.τ v))
    (Units.map (complMap (splitPrime_under (B.τ v))).toMonoidHom (kap G V V' Z v.1))

theorem chr_kapId (χ : Chr F E) :
    (χ (kapId B G V V' Z) : ℂ) = ∏ v : B.P, (chrW χ (B.τ v) (kap G V V' Z v.1) : ℂ) := by
  rw [kapId, map_prod]
  exact map_prod Circle.coeHom _ _

variable {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}


theorem acts_pureA {κ : Type} [Fintype κ] {T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} {f f₁ : SInf F κ}
    (h : Acts (evI F) T f f₁) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) : T (pureA F f g) = pureA F f₁ g := by
  refine h (fun x => g fun i => (x i).2) ⟨fun x z hz => ?_, Submodule.subset_span ⟨f, g, hg, rfl⟩⟩
  show g (fun i => (x i + z i).2) = g (fun i => (x i).2)
  congr 1
  funext i
  show (x i).2 + (z i).2 = (x i).2
  rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz i, add_zero]

theorem pureA_smul {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ) (g : (κ → Af F) → ℂ) :
    pureA F (⇑(c • f)) g = c • pureA F f g := by
  funext x
  simp only [pureA, SchwartzMap.smul_apply, smul_eq_mul, Pi.smul_apply, mul_assoc]

theorem acts_congr {κ : Type} [Fintype κ] {T T₁ : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ} (e : ∀ Φ ∈ schA F κ, T Φ = T₁ Φ)
    {f f₁ : (κ → mixedEmbedding.mixedSpace F) → ℂ} (h : Acts (evI F) T f f₁) : Acts (evI F) T₁ f f₁ :=
  fun r hr => (e _ hr.2).symm.trans (h r hr)

end GlobalTheory.ReBase

end
