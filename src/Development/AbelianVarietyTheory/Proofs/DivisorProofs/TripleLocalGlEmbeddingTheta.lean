module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelLocalGoodPlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdempotentConjugationSign
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdempotentConjugationSign
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SwapAtSplit

open scoped TensorProduct
open GlobalTheory.EmbChart (atPlace tensAt compFin_tensAt tensAt_mul_right sigR_tensAt)

theorem exists_swap_elt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v), ∃ f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E),
      GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f ∧ f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) ∧
      f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) ∧ piW t f = 1 ∧ piW (t.comp σ) f = -1 := by
  intro F E _ _ _ _ _ σ h v t
  set y : Fv F v ⊗[F] E := (splitAlgEquiv h t).symm (1, -1) with hy
  have hQ : algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) = tensAt E v 1 := rfl
  have hpi : ∀ τ : E →ₐ[F] Fv F v, piW τ (tensAt E v y) = splitProj τ y := fun τ => by
    change splitProj τ (compFin F E v (tensAt E v y)) = _
    rw [compFin_tensAt]
  refine ⟨tensAt E v y, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Algebra.smul_def, mul_comm, tensAt_mul_right]
    have e : compFin F E v (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1)) = 1 := by
      change GlobalTheory.AdelicU.evFin F v (GlobalTheory.LatVac.liftV v 1) ⊗ₜ[F] (1 : E) = 1
      rw [GlobalTheory.LatVac.evFin_liftV]; rfl
    rw [e, mul_one]
  · rw [hQ, tensAt_mul_right, compFin_tensAt]
    congr 1
    exact split_ext h t (by simp [hy]) (by simp [hy])
  · have hc : cA σ (tensAt E v y) = tensAt E v (sigR (Fv F v) σ y) := sigR_tensAt v σ y
    rw [hc, hQ, tensAt_mul_right, compFin_tensAt, ← map_neg]
    congr 1
    refine split_ext h t ?_ ?_
    · rw [map_mul, ← splitProj_comp, map_neg, map_one]; simp [hy]
    · rw [map_mul, splitProj_comp_sigR h, map_neg, map_one]; simp [hy]
  · rw [hpi]; simp [hy]
  · rw [hpi]; simp [hy]

end GlobalTheory.SwapAtSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdempotentConjugationSignStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_idempotent_conjugation_sign : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v), ∃ f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E),
      GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f ∧ f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) ∧
      f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) ∧ piW t f = 1 ∧ piW (t.comp σ) f = -1 := by
  first | exact @GlobalTheory.SwapAtSplit.exists_swap_elt | exact GlobalTheory.SwapAtSplit.exists_swap_elt | (intros; apply GlobalTheory.SwapAtSplit.exists_swap_elt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeylElementDoubled
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeylElementDoubled
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblDiag

open Matrix

theorem swap_at_place : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl (F := F)) (f : AE F E),
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (AE F E) (GlobalTheory.LatVac.liftV v 1) →
    ∃ w : UG (cA σ) (dbl (incM F J)),
      ((w : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin n) (Fin n) (AE F E))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) ∧
      At (evFin F v) (((w : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) - 1) ∧
      w * w = 1 ∧
      ∀ k : UA σ J, At (evFin F v) (mat k - 1) → ∀ gd gd' : UG (cA σ) (dbl (incM F J)),
        ((gd : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = Matrix.fromBlocks (mat k) 0 0 1 →
        ((gd' : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) = Matrix.fromBlocks 1 0 0 (mat k) →
        w * gd * w = gd' := by
  intro F E _ _ _ _ _ σ n J v f hQf hff hfc
  set Q : AF F := GlobalTheory.LatVac.liftV v (1 : Fv F v) with hQdef
  have hQQ : Q * Q = Q := by
    have h := GlobalTheory.LatVac.at_liftV v (1 : Fv F v) (1 - Q)
      (by rw [map_sub, map_one, hQdef, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [← hQdef, smul_eq_mul, sub_mul, one_mul, sub_eq_zero] at h
    exact h.symm
  set q : AE F E := algebraMap (AF F) (AE F E) Q with hqdef
  set p : AE F E := algebraMap (AF F) (AE F E) (1 - Q) with hpdef
  have hp : p = 1 - q := by rw [hpdef, map_sub, map_one]
  have hqq : q * q = q := by rw [hqdef, ← map_mul, hQQ]
  have hqf : q * f = f := by rw [hqdef, ← Algebra.smul_def]; exact hQf
  have hcp : cA σ p = p := AlgHom.commutes _ _
  have hpp : p * p = p := by rw [hp]; linear_combination hqq
  have hpf : p * f = 0 := by rw [hp]; linear_combination -hqf
  have hpcf : p * cA σ f = 0 := by rw [← hcp, ← map_mul, hpf, map_zero]
  have hsm : ∀ (m : Type) [Fintype m] [DecidableEq m] (N : Matrix m m (AE F E)), (1 - Q) • N = p • N :=
    fun m _ _ N => (algebraMap_smul (AE F E) (1 - Q) N).symm
  have hmap : ∀ a : AE F E, (a • (1 : Matrix (Fin n) (Fin n) (AE F E))).map (cA σ) = cA σ a • 1 := by
    intro a; ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, Matrix.one_apply]
    split_ifs <;> simp
  set M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E) :=
    Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin n) (Fin n) (AE F E))) (f • 1) (f • 1)
      ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) with hMdef
  have hM : M = Matrix.fromBlocks (p • 1) (f • 1) (f • 1) (p • 1) := by
    rw [hMdef, ← hQdef, hsm]

  have hMM : M * M = 1 := by
    rw [hM, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
    congr 1 <;> ext i j <;> simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    · linear_combination (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (hpp + hff + hp)
    · linear_combination (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (2 * hpf)
    · linear_combination (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (2 * hpf)
    · linear_combination (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * (hpp + hff + hp)
  have hU : Mᵀ * dbl (incM F J) * M.map (cA σ) = dbl (incM F J) := by
    rw [hM, dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.transpose_smul, Matrix.transpose_one, hmap, hcp, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_neg,
      Matrix.neg_mul, smul_smul, smul_neg]
    congr 1 <;> ext i j <;>
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, Matrix.neg_apply]
    all_goals
      first
        | linear_combination incM F J i j * (hpp - hfc + hp)
        | linear_combination incM F J i j * (hfc - hpp - hp)
        | linear_combination incM F J i j * (hpcf - hpf)
        | linear_combination incM F J i j * (hpf - hpcf)
        | linear_combination incM F J i j * (hpcf + hpf)
        | linear_combination incM F J i j * (-hpcf - hpf)

  refine ⟨⟨⟨M, M, hMM, hMM⟩, hU⟩, rfl, ?_, Subtype.ext (Units.ext hMM), ?_⟩
  · intro u hu
    show u • (M - 1) = 0
    have hQu : u * Q = 0 := by
      have h := GlobalTheory.LatVac.at_liftV v (1 : Fv F v) u hu
      rwa [← hQdef, smul_eq_mul] at h
    set ua : AE F E := algebraMap (AF F) (AE F E) u with huadef
    have huq : ua * q = 0 := by rw [huadef, hqdef, ← map_mul, hQu, map_zero]
    have huf : ua * f = 0 := by rw [← hqf]; linear_combination f * huq
    rw [← algebraMap_smul (AE F E) u, ← huadef, hM, ← Matrix.fromBlocks_one]
    ext (i | i) (j | j) <;>
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, smul_eq_mul] <;>
      first
          | linear_combination 1 * ((ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp - (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)
          | linear_combination 1 * ((1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huf)
          | linear_combination 1 * (-((1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huf))
          | linear_combination 1 * (- (ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)
          | linear_combination 1 * ((ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)
          | linear_combination 1 * (-(ua * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j) * hp - (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * huq)
  · intro k hk gd gd' hgd hgd'
    apply Subtype.ext
    apply Units.ext
    show M * ((gd : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) * M =
      ((gd' : GL (Fin n ⊕ Fin n) (AE F E)) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E))
    have hK : p • (mat k - 1) = 0 := by
      rw [← hsm]
      exact hk (1 - Q) (by rw [map_sub, map_one, hQdef, GlobalTheory.LatVac.evFin_liftV, sub_self])
    have hKe : ∀ i j, p * mat k i j = p * (1 : Matrix (Fin n) (Fin n) (AE F E)) i j := by
      intro i j
      have h := congrFun (congrFun hK i) j
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, smul_eq_mul] at h
      linear_combination h
    rw [hgd, hgd', hM, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
      add_zero, zero_add, smul_smul, smul_zero]
    congr 1 <;> ext i j <;>
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply]
    all_goals
      first
        | linear_combination 1 * (mat k i j * hpp + hKe i j + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hff + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hp)
        | linear_combination 1 * (mat k i j * hpf + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hpf)
        | linear_combination 1 * (mat k i j * hff + (1 : Matrix (Fin n) (Fin n) (AE F E)) i j * hpp + mat k i j * hp - hKe i j)

end GlobalTheory.DblDiag
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeylElementDoubledStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_weyl_element_doubled : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v : Pl (F := F)) (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    ∃ w : UG (cA σ) (dbl (incM F J)),
      ((w : GL (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) ∧
      At (evFin F v) (((w : GL (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) ∧
      w * w = 1 ∧
      ∀ k : UA σ J, At (evFin F v) (mat k - 1) → ∀ gd gd' : UG (cA σ) (dbl (incM F J)),
        ((gd : GL (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = Matrix.fromBlocks (mat k) 0 0 1 →
        ((gd' : GL (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) = Matrix.fromBlocks 1 0 0 (mat k) →
        w * gd * w = gd' := by
  first | exact @GlobalTheory.DblDiag.swap_at_place | exact GlobalTheory.DblDiag.swap_at_place | (intros; apply GlobalTheory.DblDiag.swap_at_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalGlEmbeddingTheta
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblSwap

section Groups

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {β : Type} [Fintype β] [DecidableEq β]
  {J : Matrix β β E}

theorem unit_left (k : UG c J) : (Matrix.fromBlocks ((k : GL β E) : Matrix β β E) 0 0 1)ᵀ * dbl J *
    (Matrix.fromBlocks ((k : GL β E) : Matrix β β E) 0 0 1).map c = dbl J := by
  have hk : ((k : GL β E) : Matrix β β E)ᵀ * J * ((k : GL β E) : Matrix β β E).map c = J := k.2
  have h1 : (1 : Matrix β β E).map c = 1 := Matrix.map_one _ (map_zero c) (map_one c)
  rw [dbl, Matrix.fromBlocks_transpose, Matrix.fromBlocks_map, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.transpose_zero, Matrix.transpose_one, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.map_zero _ (map_zero c), h1, Matrix.one_mul, Matrix.mul_one, hk]

def leftDiag (k : UG c J) : UG c (dbl J) :=
  ⟨⟨Matrix.fromBlocks ((k : GL β E) : Matrix β β E) 0 0 1, Matrix.fromBlocks (((k : GL β E)⁻¹ : GL β E) : Matrix β β E) 0 0 1,
    by rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one],
    by rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one]⟩, unit_left c k⟩

end Groups

section Local

variable {F : Type} [Field F] [NumberField F]

theorem box_mem_SB {k : Type} [CommRing k] [TopologicalSpace k] [T2Space k] {κ κ' : Type}
    {φ₁ : (κ → k) → ℂ} {φ₂ : (κ' → k) → ℂ} (h₁ : φ₁ ∈ SB (κ → k)) (h₂ : φ₂ ∈ SB (κ' → k)) :
    boxFun φ₁ φ₂ ∈ SB (κ ⊕ κ' → k) := by
  have cl : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inl := continuous_pi fun i => continuous_apply _
  have cr : Continuous fun x : κ ⊕ κ' → k => x ∘ Sum.inr := continuous_pi fun i => continuous_apply _
  refine ⟨(h₁.1.comp_continuous cl).mul (h₂.1.comp_continuous cr), ?_⟩
  let e := (Homeomorph.sumArrowHomeomorphProdArrow (X := k) (ι := κ) (ι' := κ'))
  refine HasCompactSupport.intro ((h₁.2.prod h₂.2).image e.symm.continuous) fun x hx => ?_
  have hx' : e x ∉ tsupport φ₁ ×ˢ tsupport φ₂ := fun h => hx ⟨e x, h, e.symm_apply_apply x⟩
  rw [Homeomorph.sumArrowHomeomorphProdArrow_apply, Set.mem_prod, not_and_or] at hx'
  simp only [boxFun]
  rcases hx' with h | h
  · rw [image_eq_zero_of_notMem_tsupport h, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h, mul_zero]

theorem conjSB {Y : Type} [TopologicalSpace Y] {φ : Y → ℂ} (h : φ ∈ SB Y) :
    (fun y => starRingEnd ℂ (φ y)) ∈ SB Y :=
  ⟨h.1.comp _, h.2.comp_left (map_zero _)⟩

theorem negSB {Y : Type} [TopologicalSpace Y] [AddGroup Y] [IsTopologicalAddGroup Y] {φ : Y → ℂ} (h : φ ∈ SB Y) :
    (fun y => φ (-y)) ∈ SB Y :=
  ⟨h.1.comp_continuous continuous_neg, h.2.comp_homeomorph (Homeomorph.neg Y)⟩

theorem tens_box (v : Pl (F := F)) {κ κ' : Type} (φ₁ : (κ → Fv F v) → ℂ) (φ₂ : (κ' → Fv F v) → ℂ)
    (r₁ : (κ → AF F) → ℂ) (r₂ : (κ' → AF F) → ℂ) :
    tens (evFin F v) (boxFun φ₁ φ₂) (boxFun r₁ r₂) = boxFun (tens (evFin F v) φ₁ r₁) (tens (evFin F v) φ₂ r₂) := by
  funext x
  simp only [tens, boxFun, Function.comp_def]
  ring

theorem rest_box (v : Pl (F := F)) {κ κ' : Type} [Fintype κ] [Fintype κ'] {φ₁ : (κ → Fv F v) → ℂ} {φ₂ : (κ' → Fv F v) → ℂ}
    {r₁ : (κ → AF F) → ℂ} {r₂ : (κ' → AF F) → ℂ} (h₁ : Rest (evFin F v) φ₁ r₁) (h₂ : Rest (evFin F v) φ₂ r₂) :
    Rest (evFin F v) (boxFun φ₁ φ₂) (boxFun r₁ r₂) := by
  refine ⟨fun x z hz => ?_, ?_⟩
  · have hz1 : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
      funext i; exact congrFun (hz u hu) (Sum.inl i)
    have hz2 : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
      funext i; exact congrFun (hz u hu) (Sum.inr i)
    show r₁ ((x + z) ∘ Sum.inl) * r₂ ((x + z) ∘ Sum.inr) = r₁ (x ∘ Sum.inl) * r₂ (x ∘ Sum.inr)
    rw [show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl,
      show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, h₁.1 _ _ hz1, h₂.1 _ _ hz2]
  · rw [tens_box]
    exact GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ h₁.2 _ h₂.2

theorem eq_of_tens_ne (v : Pl (F := F)) {κ : Type} {ψ₁ ψ₂ : (κ → Fv F v) → ℂ} {r : (κ → AF F) → ℂ}
    (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x) {x₀ : κ → AF F} (h0 : r x₀ ≠ 0)
    (h : tens (evFin F v) ψ₁ r = tens (evFin F v) ψ₂ r) : ψ₁ = ψ₂ := by
  funext y
  let z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i - evFin F v (x₀ i))
  have hz : At (evFin F v) z := by
    intro u hu; funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu
  have hev : (fun i => evFin F v ((x₀ + z) i)) = y := by
    funext i
    simp only [Pi.add_apply, z, map_add (f := _), GlobalTheory.LatVac.evFin_liftV]
    abel
  have e := congrFun h (x₀ + z)
  simp only [tens, hev, hr x₀ z hz] at e
  exact mul_right_cancel₀ h0 e

theorem actsComp (v : Pl (F := F)) {κ : Type} [Fintype κ] {T₁ T₂ : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ}
    (hT₂ : ∀ f ∈ schA F κ, T₂ f ∈ schA F κ) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ}
    (h₂ : Acts (evFin F v) T₂ φ φ₁) (h₁ : Acts (evFin F v) T₁ φ₁ φ₂) :
    Acts (evFin F v) (fun f => T₁ (T₂ f)) φ φ₂ := by
  intro r hr
  have e := h₂ r hr
  have hr₁ : Rest (evFin F v) φ₁ r := ⟨hr.1, e ▸ hT₂ _ hr.2⟩
  show T₁ (T₂ _) = _
  rw [e, h₁ r hr₁]

theorem tens_smul (v : Pl (F := F)) {κ : Type} (c : ℂ) (φ : (κ → Fv F v) → ℂ) (r : (κ → AF F) → ℂ) :
    tens (evFin F v) (c • φ) r = c • tens (evFin F v) φ r := by
  funext x; simp only [tens, Pi.smul_apply, smul_eq_mul]; ring

theorem actsSmul (v : Pl (F := F)) {κ : Type} [Fintype κ] (T : Module.End ℂ ((κ → AF F) → ℂ)) {φ φ₁ : (κ → Fv F v) → ℂ}
    (h : Acts (evFin F v) T φ φ₁) (c : ℂ) : Acts (evFin F v) T (c • φ) (c • φ₁) := by
  intro r hr
  by_cases hc : c = 0
  · subst hc
    rw [tens_smul, tens_smul, zero_smul, zero_smul, map_zero]
  · have hr' : Rest (evFin F v) φ r := by
      refine ⟨hr.1, ?_⟩
      have e : tens (evFin F v) φ r = c⁻¹ • tens (evFin F v) (c • φ) r := by
        rw [tens_smul, smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [e]; exact (schA F κ).smul_mem _ hr.2
    rw [tens_smul, tens_smul, map_smul, h r hr']

end Local

end GlobalTheory.DblSwap

namespace GlobalTheory.DblSwap
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip

theorem conj_apow {F : Type} [Field F] [NumberField F] {v : Pl (F := F)} (x : (Fv F v)ˣ) (z : ℂ) (hz : starRingEnd ℂ z = z) :
    starRingEnd ℂ (apow x z) = apow x z := by
  unfold apow
  have harg : ((nabs (Fv F v) x : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (nabs_pos (Fv F v) x).le]; exact Real.pi_ne_zero.symm
  have e := Complex.cpow_conj _ z harg
  rw [hz, Complex.conj_ofReal] at e
  exact e.symm

theorem conj_omB {F : Type} [Field F] [NumberField F] {v : Pl (F := F)} {A' D : Type} [Fintype A'] [DecidableEq A'] [Fintype D]
    [DecidableEq D] (ν α : (Fv F v)ˣ →* ℂˣ) (g : GL A' (Fv F v)) (Ψ : Matrix A' D (Fv F v) → ℂ) (Y : Matrix A' D (Fv F v)) :
    starRingEnd ℂ (omB ν α g 1 Ψ Y) =
      (starRingEnd ℂ (ν (gdet g) : ℂ) / (ν (gdet g) : ℂ)) * omB ν α g 1 (fun Z => starRingEnd ℂ (Ψ Z)) Y := by
  have hν : (ν (gdet g) : ℂ) ≠ 0 := Units.ne_zero _
  have h1 : gdet (1 : GL D (Fv F v)) = 1 := map_one _
  have hz : starRingEnd ℂ ((Fintype.card D : ℂ) / 2) = (Fintype.card D : ℂ) / 2 := by
    rw [map_div₀, map_natCast, map_ofNat]
  simp only [omB, h1, map_one, Units.val_one, apow_one, mul_one, map_mul, conj_apow _ _ hz]
  field_simp

end GlobalTheory.DblSwap

namespace GlobalTheory.DblSwap
open Matrix

theorem diagR_acts : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (K : GL (Fin a') (Fv F v) →* UA σ G.V'.J), (∀ g, K g ∈ UAt σ G.V' (evFin F v) ∧
      (mat (K g)).map (piW t) = g.val ∧
      (mat (K g)).map (piW (t.comp σ)) = (G.V'.J.map t)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map t) →
    ∀ (S : GL (Fin a') (Fv F v) → (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) → ((Fin a' × Fin (a + a')) → Fv F v) → ℂ),
    (∀ g, ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), S g φ ∈ SB _ ∧ Acts (evFin F v) (om' (K g, 1)) φ (S g φ)) →
    ∀ (ν α : (Fv F v)ˣ →* ℂˣ) (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι → (∀ g, ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ι (S g φ) = GlobalTheory.SplitFlip.omB ν α g 1 (ι φ)) →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) d' dd →
    ∀ (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUSplitting (adeleClass F) B.ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd →
    (∀ (g : UA σ G.V'.J) (gd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))),
      ((gd : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
        Matrix.fromBlocks (mat g) 0 0 1 →
      ∀ φ₁ ∈ schA F (Fin a' × Fin (a + a')), ∀ φ₂ ∈ schA F (Fin a' × Fin (a + a')), omd gd (boxFun φ₁ φ₂) = boxFun (om' (g, 1) φ₁) φ₂) →
    ∀ (g : GL (Fin a') (Fv F v)) (gd' : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))),
      ((gd' : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
        Matrix.fromBlocks 1 0 0 (mat (K g)) →
    ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      Acts (evFin F v) (omd gd') (boxFun φ₁ φ₂) (boxFun φ₁ (fun x =>
        ((ν (GlobalTheory.SplitFlip.gdet g) : ℂ) / starRingEnd ℂ (ν (GlobalTheory.SplitFlip.gdet g) : ℂ)) *
          starRingEnd ℂ (S g (fun y => starRingEnd ℂ (φ₂ y)) x))) := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT v hv t K hK S hS ν α ι hι hint d' hd' dd hdd omd hspl hres g gd' hgd'
    φ₁ h₁ φ₂ h₂
  obtain ⟨f, hf1, hf2, hf3, hf4, hf5⟩ := GlobalTheory.T.local_idempotent_conjugation_sign σ hT.base.cm v t
  change UG (cA σ) (dbl (incM F G.V'.J)) →* _ at omd
  change UG (cA σ) (dbl (incM F G.V'.J)) at gd'
  obtain ⟨w, hwm, -, hww, hconj⟩ := GlobalTheory.T.local_weyl_element_doubled σ G.V'.J v f hf1 hf2 hf3
  obtain ⟨c, hc⟩ := GlobalTheory.T.linear_model_local_good_place F E σ B a a' G X om om' hT v hv t ι hι d' hd' dd hdd omd hspl f hf1 hf2 hf3 hf4 hf5 w hwm
  set k := K g with hk
  let gd := leftDiag (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) k
  have hgd : ((gd : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) =
      Matrix.fromBlocks (mat k) 0 0 1 := rfl
  have hAt : At (evFin F v) (((gd : GL (Fin a' ⊕ Fin a') (AE F E)) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (AE F E)) - 1) := by
    intro u hu
    have hk1 : u • (mat k - 1) = 0 := (hK g).1 u hu
    have e : Matrix.fromBlocks (mat k) 0 0 (1 : Matrix (Fin a') (Fin a') (AE F E)) - 1 =
        Matrix.fromBlocks (mat k - 1) 0 0 0 := by
      rw [← Matrix.fromBlocks_one, sub_eq_add_neg, Matrix.fromBlocks_neg, Matrix.fromBlocks_add]; simp [sub_eq_add_neg]
    rw [hgd, e, Matrix.fromBlocks_smul]
    simp [hk1]
  have hpres : ∀ p, ∀ Φ ∈ schA F ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a'))), omd p Φ ∈ schA F _ :=
    fun p Φ hΦ => hspl.pres p Φ hΦ

  have hL : ∀ ψ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ ψ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      Acts (evFin F v) (omd gd) (boxFun ψ₁ ψ₂) (boxFun (S g ψ₁) ψ₂) := by
    intro ψ₁ hψ₁ ψ₂ hψ₂
    obtain ⟨φ', -, hA⟩ := GlobalTheory.T.doubledUnitaryElement_acts_localOperatorAtPlace F E σ B a a' G hT.base dd omd hspl v gd hAt _ (box_mem_SB hψ₁ hψ₂)
    obtain ⟨r₁, hr₁, x₁, hx₁⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v ψ₁ hψ₁
    obtain ⟨r₂, hr₂, x₂, hx₂⟩ := GlobalTheory.RestComplement.exists_rest_ne_zero v ψ₂ hψ₂
    have hR := rest_box v hr₁ hr₂
    have e := hA _ hR
    rw [tens_box, hres k gd hgd _ hr₁.2 _ hr₂.2, (hS g ψ₁ hψ₁).2 r₁ hr₁, ← tens_box] at e
    have h0 : boxFun r₁ r₂ (Sum.elim x₁ x₂) ≠ 0 := by
      simp only [boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr]; exact mul_ne_zero hx₁ hx₂
    have e2 : φ' = boxFun (S g ψ₁) ψ₂ := eq_of_tens_ne v hR.1 h0 e.symm
    rw [e2] at hA; exact hA

  have pair : ∀ φa ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φb ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      ∃ ψa ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∃ ψb ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
        ι ψa = (fun Y => starRingEnd ℂ (ι (fun y => starRingEnd ℂ (φb y)) (-Y))) ∧
        ι (fun y => starRingEnd ℂ (ψb y)) = (fun Y => starRingEnd ℂ (ι φa (-Y))) := by
    intro φa ha φb hb
    have m1 : ι (fun y => starRingEnd ℂ (φb y)) ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) := hι.bij.mapsTo (conjSB hb)
    have m2 : ι φa ∈ SB (Matrix (Fin a') (Fin (a + a')) (Fv F v)) := hι.bij.mapsTo ha
    obtain ⟨ψa, hψa, ea⟩ := hι.bij.surjOn (conjSB (negSB m1))
    obtain ⟨χ, hχ, eb⟩ := hι.bij.surjOn (conjSB (negSB m2))
    refine ⟨ψa, hψa, fun y => starRingEnd ℂ (χ y), conjSB hχ, ea, ?_⟩
    have e : (fun y => starRingEnd ℂ (starRingEnd ℂ (χ y))) = χ := funext fun y => Complex.conj_conj _
    rw [e, eb]
  have inv : ∀ φa φb ψa ψb : ((Fin a' × Fin (a + a')) → Fv F v) → ℂ,
      ι ψa = (fun Y => starRingEnd ℂ (ι (fun y => starRingEnd ℂ (φb y)) (-Y))) →
      ι (fun y => starRingEnd ℂ (ψb y)) = (fun Y => starRingEnd ℂ (ι φa (-Y))) →
      ι φa = (fun Y => starRingEnd ℂ (ι (fun y => starRingEnd ℂ (ψb y)) (-Y))) ∧
      ι (fun y => starRingEnd ℂ (φb y)) = (fun Y => starRingEnd ℂ (ι ψa (-Y))) := by
    intro φa φb ψa ψb e1 e2
    refine ⟨?_, ?_⟩
    · rw [e2]; funext Y; simp only [neg_neg, Complex.conj_conj]
    · rw [e1]; funext Y; simp only [neg_neg, Complex.conj_conj]

  have hww' : ∀ Φ, omd w (omd w Φ) = Φ := fun Φ => by
    change (omd w * omd w) Φ = Φ
    rw [← omd.map_mul, hww, omd.map_one, Module.End.one_apply]
  have hc2 : c * c = 1 := by
    let φ0 : ((Fin a' × Fin (a + a')) → Fv F v) → ℂ := Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1
    have h0 : φ0 ∈ SB _ := GlobalTheory.StdVacuum.indicator_mem_SB v
    obtain ⟨ψa, ha, ψb, hb, e1, e2⟩ := pair φ0 h0 φ0 h0
    obtain ⟨e3, e4⟩ := inv _ _ _ _ e1 e2
    have A1 := hc φ0 h0 φ0 h0 ψa ha ψb hb e1 e2
    have A2 := actsSmul v (omd w) (hc ψa ha ψb hb φ0 h0 φ0 h0 e3 e4) c
    have A3 := actsComp v (fun Φ hΦ => hpres w Φ hΦ) A1 A2
    simp only [hww'] at A3
    have e5 := GlobalTheory.TensUniq.eq_of_tens_eq v (boxFun φ0 φ0) _ _ (box_mem_SB h0 h0) fun r hr => A3 r hr
    have e6 := congrFun e5 (fun _ => 0)
    have hv0 : φ0 (fun _ => 0) = 1 := by
      show Set.indicator _ _ _ = _
      rw [Set.indicator_of_mem (show (fun _ => (0 : Fv F v)) ∈
        {x : (Fin a' × Fin (a + a')) → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun i => zero_mem _)]
      rfl
    simp only [boxFun, Pi.smul_apply, smul_eq_mul] at e6
    rw [show ((fun _ => (0 : Fv F v)) : (Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) ∘ Sum.inl = fun _ => 0
      from rfl, show ((fun _ => (0 : Fv F v)) : (Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → Fv F v) ∘ Sum.inr =
      fun _ => 0 from rfl, hv0] at e6
    linear_combination -e6

  set cν : ℂ := (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) / starRingEnd ℂ (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) with hcν
  set T₂ : ((Fin a' × Fin (a + a')) → Fv F v) → ℂ :=
    fun x => cν * starRingEnd ℂ (S g (fun y => starRingEnd ℂ (φ₂ y)) x) with hT₂
  have hT₂sb : T₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v) :=
    (SB _).smul_mem cν (conjSB (hS g _ (conjSB h₂)).1)
  obtain ⟨ψ₁, hψ₁, ψ₂, hψ₂, e1, e2⟩ := pair φ₁ h₁ φ₂ h₂
  obtain ⟨e3, -⟩ := inv _ _ _ _ e1 e2
  have hSψ := (hS g ψ₁ hψ₁).1
  have key : ι (fun y => starRingEnd ℂ (T₂ y)) = (fun Y => starRingEnd ℂ (ι (S g ψ₁) (-Y))) := by
    have ec : (fun y => starRingEnd ℂ (T₂ y)) = starRingEnd ℂ cν • S g (fun y => starRingEnd ℂ (φ₂ y)) := by
      funext y; simp only [hT₂, map_mul, Complex.conj_conj, Pi.smul_apply, smul_eq_mul]
    rw [ec, map_smul, hint g _ (conjSB h₂), hint g ψ₁ hψ₁, e1]
    funext Y
    rw [conj_omB]
    simp only [Pi.smul_apply, smul_eq_mul, GlobalTheory.SplitFlip.omB, Complex.conj_conj, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    have hν : (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) ≠ 0 := Units.ne_zero _
    have hν' : starRingEnd ℂ (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) ≠ 0 := (map_ne_zero _).mpr hν
    rw [hcν, map_div₀, Complex.conj_conj]
  have A1 := hc φ₁ h₁ φ₂ h₂ ψ₁ hψ₁ ψ₂ hψ₂ e1 e2
  have A2 := actsSmul v (omd gd) (hL ψ₁ hψ₁ ψ₂ hψ₂) c
  have A3 := actsSmul v (omd w) (hc (S g ψ₁) hSψ ψ₂ hψ₂ φ₁ h₁ T₂ hT₂sb e3 key) c
  have A12 := actsComp v (fun Φ hΦ => hpres w Φ hΦ) A1 A2
  have A123 := actsComp v (fun Φ hΦ => hpres gd _ (hpres w Φ hΦ)) A12 A3
  rw [smul_smul, hc2, one_smul] at A123
  change UG (cA σ) (dbl (incM F G.V'.J)) at gd
  have eg : omd gd' = omd w * omd gd * omd w := by rw [← omd.map_mul, ← omd.map_mul, hconj k (hK g).1 gd gd' hgd hgd']
  change Acts (evFin F v) (omd gd') (boxFun φ₁ φ₂) (boxFun φ₁ T₂)
  rw [eg]
  exact A123

end GlobalTheory.DblSwap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalGlEmbeddingThetaStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_local_gl_embedding_theta : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v, X.Good v → ∀ (t : E →ₐ[F] Fv F v)
    (K : GL (Fin a') (Fv F v) →* UA σ G.V'.J), (∀ g, K g ∈ UAt σ G.V' (evFin F v) ∧
      (mat (K g)).map (piW t) = g.val ∧
      (mat (K g)).map (piW (t.comp σ)) = (G.V'.J.map t)⁻¹ * ((g⁻¹ : GL _ _).val)ᵀ * G.V'.J.map t) →
    ∀ (S : GL (Fin a') (Fv F v) → (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) → ((Fin a' × Fin (a + a')) → Fv F v) → ℂ),
    (∀ g, ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), S g φ ∈ SB _ ∧ Acts (evFin F v) (om' (K g, 1)) φ (S g φ)) →
    ∀ (ν α : (Fv F v)ˣ →* ℂˣ) (ι : (((Fin a' × Fin (a + a')) → Fv F v) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv F v) → ℂ)),
    G.M'.IsLinBar B.ψ t 1 1 ι → (∀ g, ∀ φ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ι (S g φ) = GlobalTheory.SplitFlip.omB ν α g 1 (ι φ)) →
    ∀ (d' : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) (Fin a' × Fin (a + a'))),
    (∀ x : Matrix (Fin a') (Fin (a + a')) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))) ((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')))),
    IsDblCoord (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.W.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J) d' dd →
    ∀ (omd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J)) →* Module.End ℂ (((Fin a' × Fin (a + a')) ⊕ (Fin a' × Fin (a + a')) → AF F) → ℂ)),
    IsUSplitting (adeleClass F) B.ψ dd (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) omd →
    (∀ (g : UA σ G.V'.J) (gd : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))),
      ((gd : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks (mat g) 0 0 1 →
      ∀ φ₁ ∈ schA F (Fin a' × Fin (a + a')), ∀ φ₂ ∈ schA F (Fin a' × Fin (a + a')), omd gd (boxFun φ₁ φ₂) = boxFun (om' (g, 1) φ₁) φ₂) →
    ∀ (g : GL (Fin a') (Fv F v)) (gd' : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (dbl ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) G.V'.J))),
      ((gd' : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks 1 0 0 (mat (K g)) →
    ∀ φ₁ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v), ∀ φ₂ ∈ SB ((Fin a' × Fin (a + a')) → Fv F v),
      Acts (evFin F v) (omd gd') (boxFun φ₁ φ₂) (boxFun φ₁ (fun x =>
        ((ν (GlobalTheory.SplitFlip.gdet g) : ℂ) / starRingEnd ℂ (ν (GlobalTheory.SplitFlip.gdet g) : ℂ)) *
          starRingEnd ℂ (S g (fun y => starRingEnd ℂ (φ₂ y)) x))) := by
  first | exact @GlobalTheory.DblSwap.diagR_acts | exact GlobalTheory.DblSwap.diagR_acts | (intros; apply GlobalTheory.DblSwap.diagR_acts <;> assumption)
end
