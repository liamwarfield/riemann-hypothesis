module

public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDict
public import Development.AutomorphicArithmetic.LocalEmbeddings.OppLagr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MultiplicationPackage
noncomputable def UpperTheory.Reformulated.B.MatrixHomeomorphOfGeneralLinearPair.mulH_pk :
    {K : Type} →
      [inst : Field K] →
        [inst_1 : TopologicalSpace K] →
          [IsTopologicalRing K] →
            {n d : ℕ} → GL (Fin n) K → GL (Fin d) K → Matrix (Fin n) (Fin d) K ≃ₜ Matrix (Fin n) (Fin d) K :=
  fun {K} _ _ _ {n d} a c =>
    { toFun := fun y => (a : Matrix (Fin n) (Fin n) K) * y * (c : Matrix (Fin d) (Fin d) K)
      invFun := fun y =>
        ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * y *
          ((c⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
      left_inv := fun y => by
        beta_reduce
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc,
          Units.inv_mul, Matrix.one_mul]
      right_inv := fun y => by
        beta_reduce
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc,
          Units.mul_inv, Matrix.one_mul]
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
end

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.FourierTransformBijective
open MeasureTheory Metric

section
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]

end

section
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [ProperSpace K]
  {κ : Type} [Fintype κ] [MeasurableSpace (κ → K)] [BorelSpace (κ → K)]
  (μ : Measure (κ → K)) [μ.IsAddHaarMeasure] (ψ : AddChar K ℂ)

variable {d : K} (hd : ∀ t : K, (∀ x : K, ‖x‖ ≤ 1 → ψ (x * t) = 1) ↔ ‖t‖ ≤ ‖d‖)
include hd

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ItemsKcoinvPfDict
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.DictXOfK
set_option synthInstance.maxHeartbeats 200000

section
set_option linter.unusedSectionVars false
noncomputable section
namespace PositivityTheory.KCo
open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {t : E →ₐ[F] Fv F v} {sec : Fv F v × Fv F v → AE F E} {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  [Fintype κ] {JA : Matrix α α (AE F E)} {JB : Matrix β β (AE F E)} {ψ : AddChar (AF F) ℂ}
variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W}
def DictX_k : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (B : Base F E)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W) (χX χW : Chr F E), _root_.UpperTheory.TP.W.GoodK σ B → (∃ r s, X.IsHerm σ B r s) →
    (∃ r s, W.IsSkew σ B r s) → M.IsWeil B.ψ χX χW om → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v), (∃ ι, M.IsLinBar B.ψ t 1 1 ι) ∧
      (∀ g₀ : GL (Fin n) (Fv F v), ∃ g ∈ UAt σ X (evFin F v), (mat g).map (piW t) = g₀) ∧
      (∀ h₀ : GL (Fin d) (Fv F v), ∃ h ∈ UAt σ W (evFin F v), (mat h).map (piW t) = h₀) ∧
      ∀ ι, M.IsLinBar B.ψ t 1 1 ι →
        (∀ g ∈ UAt σ X (evFin F v), ∀ g₀ : GL (Fin n) (Fv F v), (mat g).map (piW t) = g₀ →
          Reads v ι (om (g, 1)) (omB (chrW χW t) (chrW χX t) g₀ 1)) ∧
        ∀ h ∈ UAt σ W (evFin F v), ∀ h₀ : GL (Fin d) (Fv F v), (mat h).map (piW t) = h₀ →
          Reads v ι (om (1, h)) (omB (chrW χW t) (chrW χX t) 1 h₀)
theorem dictX_of_k (hM : ModelEx) (hC : Cyc) (hA : AdSt) (hS : SecSt) (hU : ActsUniq) : _root_.PositivityTheory.KCo.DictX_k := by
  intro F E _ _ _ _ _ σ n d B X W M om χX χW hB ⟨_, _, hX⟩ ⟨_, _, hW⟩ hom v t
  obtain ⟨⟨sec, h⟩, -⟩ := hS F E σ hB.cm v t
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have uu : ∀ {m : ℕ} {J : Matrix (Fin m) (Fin m) E}, IsUnit J.det → IsUnit ((incM F J).map (piW t)) := fun {m J} hJ => by
    rw [incM_map h]
    exact ((Matrix.isUnit_iff_isUnit_det J).2 hJ).map (t : E →+* Fv F v).mapMatrix
  have hG : Grams σ t (incM F X.J) (incM F W.J) := by
    refine ⟨uu (GlobalTheory.CompanionTheory.Ar.RT.isUnit_det_of_cartan (F := F) X.J (B.emb w).1 1 (X.θ w) (by rw [one_smul]; exact hX.cartan w)),
      uu (GlobalTheory.CompanionTheory.Ar.RT.isUnit_det_of_cartan (F := F) W.J (B.emb w).1 Complex.I (W.θ w) (hW.cartan w)), 1, one_mul _,
      Matrix.ext fun i j => ?_, Matrix.ext fun i j => ?_⟩
    · rw [incM_map' h, incM_map h, one_smul, hX.herm]; rfl
    · rw [incM_map' h, incM_map h, neg_smul, one_smul, hW.skew, map_neg]; rfl
  obtain ⟨ι₀, hι₀⟩ := exists_lm hM hA hB.std h hG M.co
  obtain ⟨hR, ⟨d', hd', hL⟩, -⟩ := hom
  obtain ⟨ε, -, hε, hε'⟩ := hG.sym
  refine ⟨⟨_, linBar_of_lm hA hU h hG hι₀⟩, fun g₀ => h.exists_ug hε hG.uA g₀, fun g₀ => h.exists_ug hε' hG.uB g₀, fun ι hι => ?_⟩
  have lm := lm_of_linBar hA hB.std h hG hι
  refine ⟨fun g hg g₀ e φ hφ => ?_, fun g hg g₀ e φ hφ => ?_⟩
  · obtain ⟨φ₁, h1, h2, h3⟩ := acts_formula hM hC hA hB.std h hG.swap (lm.swap hd') hL.isWeilB g hg g₀ e φ hφ
    refine ⟨φ₁, h1, h2, funext fun Y => ?_⟩
    have := congrFun h3 (ofM Yᵀ)
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Pi.smul_apply, rmL_apply, swH_apply, toM_ofM, smul_eq_mul] at this
    simp only [omB, gdet, map_one, Units.val_one, mul_one, apow_one, Matrix.mul_one]
    refine this.trans (congrArg _ (congrArg _ ?_))
    rw [← transpose_transpose (g₀.1ᵀ * Y), transpose_mul, transpose_transpose]
    rfl
  · obtain ⟨φ₁, h1, h2, h3⟩ := acts_formula hM hC hA hB.std h hG lm hR.isWeilB g hg g₀ e φ hφ
    refine ⟨φ₁, h1, h2, funext fun Y => ?_⟩
    have := congrFun h3 (ofM Y)
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, Pi.smul_apply, rmL_apply, toM_ofM, smul_eq_mul] at this
    simp only [omB, gdet, map_one, Units.val_one, mul_one, one_mul, apow_one, transpose_one, Matrix.one_mul]
    exact this
end PositivityTheory.KCo
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
namespace PositivityTheory.KCo
theorem dictX_proof_k : _root_.PositivityTheory.KCo.DictX_k := _root_.PositivityTheory.KCo.dictX_of_k model_existence cyclicity adjoint_statement section_statement action_uniqueness
end PositivityTheory.KCo
end
end

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace UpperTheory.TP
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private noncomputable def mulH_pk {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {n d : ℕ}
    (a : GL (Fin n) K) (c : GL (Fin d) K) : Matrix (Fin n) (Fin d) K ≃ₜ Matrix (Fin n) (Fin d) K :=
  _root_.UpperTheory.Reformulated.B.MatrixHomeomorphOfGeneralLinearPair.mulH_pk a c
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {X : Spc F E n} {W : Spc F E d}
private theorem linBar_of_linW_pk (hcm : IsCMExt F E σ) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {v : Pl F} (t : E →ₐ[F] Fv F v)
    (a : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (ha : a.1 * X.J.map (t.comp σ) = -1)
    (hc : (W.J.map (t.comp σ))ᵀ * c.1 = 1) {ι} (hι : M.IsLinW ψ t 1 1 ι) :
    M.IsLinBar ψ (t.comp σ) 1 1 (LinearMap.funLeft ℂ ℂ (mulH_pk a c) ∘ₗ ι) := by
  unfold Model.IsLinBar
  unfold Model.IsLinW at hι
  rw [GlobalTheory.OppLagr.comp_comp hcm]
  have cw : ∀ u : Matrix (Fin n) (Fin d) (Fv F v),
      ((1 : GL (Fin n) (Fv F v))⁻¹).1 * u * ((1 : GL (Fin d) (Fv F v))⁻¹).1ᵀ = u := fun u => by simp
  have co : ∀ u : Matrix (Fin n) (Fin d) (Fv F v),
      a.1 * (-((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map (t.comp σ) * u * (W.J.map (t.comp σ))ᵀ * (1 : GL (Fin d) (Fv F v)).1)) * c.1 = u := by
    intro u
    simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ha, Matrix.mul_assoc, Matrix.mul_assoc, hc]
    simp
  have hm : ∀ y, (mulH_pk a c) y = a.1 * y * c.1 := fun _ => rfl
  refine ⟨PositivityTheory.KCo.bij_comp hι.bij (mulH_pk a c), ?_, ?_⟩
  · intro u hu h0 φ hφ φ₁ hφ₁ hA Y
    have e := hι.trans u hu h0 φ hφ φ₁ hφ₁ hA (a.1 * Y * c.1)
    simp only [cw] at e
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, hm]
    rw [e, Matrix.mul_add, Matrix.add_mul, co]
  · intro u hu h0 φ hφ φ₁ hφ₁ hA x hx hx0
    have e := hι.mult u hu h0 φ hφ φ₁ hφ₁ hA x hx hx0
    simp only [cw] at e
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, hm]
    rw [co, e]
private theorem linW_of_linBar_pk (hcm : IsCMExt F E σ) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) {v : Pl F} (t : E →ₐ[F] Fv F v)
    (a : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)) (ha : a.1 = -(X.J.map (t.comp σ)))
    (hc : c.1 = (W.J.map (t.comp σ))ᵀ) {ι} (hι : M.IsLinBar ψ (t.comp σ) 1 1 ι) :
    M.IsLinW ψ t 1 1 (LinearMap.funLeft ℂ ℂ (mulH_pk a c) ∘ₗ ι) := by
  unfold Model.IsLinBar at hι
  unfold Model.IsLinW
  rw [GlobalTheory.OppLagr.comp_comp hcm] at hι
  have cw : ∀ u : Matrix (Fin n) (Fin d) (Fv F v),
      ((1 : GL (Fin n) (Fv F v))⁻¹).1 * u * ((1 : GL (Fin d) (Fv F v))⁻¹).1ᵀ = u := fun u => by simp
  have co : ∀ u : Matrix (Fin n) (Fin d) (Fv F v),
      -((1 : GL (Fin n) (Fv F v)).1ᵀ * X.J.map (t.comp σ) * u * (W.J.map (t.comp σ))ᵀ * (1 : GL (Fin d) (Fv F v)).1) = a.1 * u * c.1 := by
    intro u
    rw [ha, hc]
    simp only [Units.val_one, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, Matrix.neg_mul]
  have hm : ∀ y, (mulH_pk a c) y = a.1 * y * c.1 := fun _ => rfl
  refine ⟨PositivityTheory.KCo.bij_comp hι.bij (mulH_pk a c), ?_, ?_⟩
  · intro u hu h0 φ hφ φ₁ hφ₁ hA Y
    have e := hι.trans u hu h0 φ hφ φ₁ hφ₁ hA (a.1 * Y * c.1)
    simp only [co] at e
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, hm, cw]
    rw [e, Matrix.mul_add, Matrix.add_mul]
  · intro u hu h0 φ hφ φ₁ hφ₁ hA x hx hx0
    have e := hι.mult u hu h0 φ hφ φ₁ hφ₁ hA x hx hx0
    simp only [co] at e
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply, hm, cw]
    exact e
theorem exists_linW_k (B : Base F E) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    {r s r' s' : ℕ} (hp : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s') (v : Pl F) (t : E →ₐ[F] Fv F v) :
    ∃ ι, M.IsLinW B.ψ t 1 1 ι := by
  have hcm : IsCMExt F E σ := hp.base.cm
  have hJX : (X.J.map (t.comp σ)).det ≠ 0 := GlobalTheory.OppLagr.det_map_ne_zero (GlobalTheory.OppLagr.det_ne_zero_herm hp.herm) _
  have hJW : (W.J.map (t.comp σ)).det ≠ 0 := GlobalTheory.OppLagr.det_map_ne_zero (GlobalTheory.OppLagr.det_ne_zero_skew hp.skew) _
  let P : GL (Fin n) (Fv F v) := Matrix.nonsingInvUnit (-(X.J.map (t.comp σ))) (isUnit_iff_ne_zero.mpr (by
    rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hJX))
  let Q : GL (Fin d) (Fv F v) := Matrix.nonsingInvUnit (W.J.map (t.comp σ))ᵀ (isUnit_iff_ne_zero.mpr (by
    rw [Matrix.det_transpose]
    exact hJW))
  obtain ⟨⟨ι, hι⟩, -⟩ := _root_.PositivityTheory.KCo.dictX_proof_k F E σ n d B X W M om χX χW hp.base ⟨_, _, hp.herm⟩ ⟨_, _, hp.skew⟩ hp.weil v (t.comp σ)
  exact ⟨_, linW_of_linBar_pk hcm M B.ψ t P Q rfl rfl hι⟩
theorem split_formula_k (B : Base F E) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    {r s r' s' : ℕ} (hp : _root_.GlobalTheory.ThK.IsPair_k B M χX χW om r s r' s') (v : Pl F) (t : E →ₐ[F] Fv F v) {ι} (hι : M.IsLinW B.ψ t 1 1 ι)
    (g : UA σ X.J) (hg : g ∈ UAt σ X (evFin F v)) (h : UA σ W.J) (hh : h ∈ UAt σ W (evFin F v))
    (g₀ : GL (Fin n) (Fv F v)) (h₀ : GL (Fin d) (Fv F v)) (eg : g₀.1 = (mat g).map (piW t)) (eh : h₀.1 = (mat h).map (piW t))
    (φ) (hφ : φ ∈ SB (Fin n × Fin d → Fv F v)) (φ₁) (hφ₁ : φ₁ ∈ SB (Fin n × Fin d → Fv F v))
    (hA : Acts (evFin F v) (om (g, h)) φ φ₁) :
    ι φ₁ = GlobalTheory.SplitFlip.omA (chrW χW t)⁻¹ (chrW χX t) g₀ h₀ (ι φ) := by
  have hcm : IsCMExt F E σ := hp.base.cm
  have hJX : (X.J.map (t.comp σ)).det ≠ 0 := GlobalTheory.OppLagr.det_map_ne_zero (GlobalTheory.OppLagr.det_ne_zero_herm hp.herm) _
  have hJW : (W.J.map (t.comp σ)).det ≠ 0 := GlobalTheory.OppLagr.det_map_ne_zero (GlobalTheory.OppLagr.det_ne_zero_skew hp.skew) _
  let P : GL (Fin n) (Fv F v) := Matrix.nonsingInvUnit (-(X.J.map (t.comp σ))) (isUnit_iff_ne_zero.mpr (by
    rw [Matrix.det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hJX))
  let Q : GL (Fin d) (Fv F v) := Matrix.nonsingInvUnit (W.J.map (t.comp σ))ᵀ (isUnit_iff_ne_zero.mpr (by
    rw [Matrix.det_transpose]
    exact hJW))
  have hPv : P.1 = -(X.J.map (t.comp σ)) := rfl
  have hQv : Q.1 = (W.J.map (t.comp σ))ᵀ := rfl
  have ha : (P⁻¹).1 * X.J.map (t.comp σ) = -1 := by
    have := Units.inv_mul P
    rw [hPv, Matrix.mul_neg] at this
    exact neg_eq_iff_eq_neg.mp this
  have hc : (W.J.map (t.comp σ))ᵀ * (Q⁻¹).1 = 1 := by rw [← hQv]; exact Units.mul_inv Q
  have hι' := linBar_of_linW_pk hcm M B.ψ t P⁻¹ Q⁻¹ ha hc hι
  obtain ⟨-, -, -, k⟩ := _root_.PositivityTheory.KCo.dictX_proof_k F E σ n d B X W M om χX χW hp.base ⟨_, _, hp.herm⟩ ⟨_, _, hp.skew⟩ hp.weil v (t.comp σ)
  obtain ⟨kg, kh⟩ := k _ hι'
  let g₁ : GL (Fin n) (Fv F v) := Matrix.GeneralLinearGroup.map (piW (t.comp σ)) g.1
  let h₁ : GL (Fin d) (Fv F v) := Matrix.GeneralLinearGroup.map (piW (t.comp σ)) h.1
  obtain ⟨φ', hφ', hA', e'⟩ := kh h hh h₁ rfl φ hφ
  obtain ⟨φ'', hφ'', hA'', e''⟩ := kg g hg g₁ rfl φ' hφ'
  have hcomp : Acts (evFin F v) (om (g, h)) φ φ'' := by
    intro R hR
    have e : om (g, h) = om (g, 1) * om (1, h) := by rw [← map_mul]; simp
    have hR' : Rest (evFin F v) φ' R :=
      ⟨hR.1, by rw [← hA' R hR]; exact hp.weil.isUSplitting.pres (1, h) _ hR.2⟩
    rw [e, Module.End.mul_apply, hA' R hR, hA'' R hR']
  obtain ⟨hex, -, -⟩ := _root_.PositivityTheory.ThKF0.actsEx_k F E σ B n d X W M χX χW om r s r' s' hp v
  have e1 : φ₁ = φ'' := (hex g hg h hh φ hφ).unique ⟨hφ₁, hA⟩ ⟨hφ'', hcomp⟩
  have key : (LinearMap.funLeft ℂ ℂ (mulH_pk P⁻¹ Q⁻¹) ∘ₗ ι) φ'' =
      GlobalTheory.SplitFlip.omB (chrW χW (t.comp σ)) (chrW χX (t.comp σ)) g₁ h₁ ((LinearMap.funLeft ℂ ℂ (mulH_pk P⁻¹ Q⁻¹) ∘ₗ ι) φ) := by
    rw [e'', e', ← GlobalTheory.SplitFlip.omB_mul, mul_one, one_mul]
  have ug := GlobalTheory.Div.CoordOpp.unit_map σ g (t.comp σ)
  have uh := GlobalTheory.Div.CoordOpp.unit_map σ h (t.comp σ)
  rw [GlobalTheory.OppLagr.comp_comp hcm, ← eg] at ug
  rw [GlobalTheory.OppLagr.comp_comp hcm, ← eh] at uh
  have ug' : g₁.1ᵀ * X.J.map (t.comp σ) * g₀.1 = X.J.map (t.comp σ) := ug
  have uh' : h₁.1ᵀ * W.J.map (t.comp σ) * h₀.1 = W.J.map (t.comp σ) := uh
  have cg : g₀⁻¹ = P⁻¹ * (GlobalTheory.SplitFlip.invT g₁)⁻¹ * P := by
    symm
    rw [eq_inv_iff_mul_eq_one]
    apply Units.ext
    simp only [Units.val_mul, Units.val_one, GlobalTheory.SplitFlip.invT_inv_val]
    have e0 : g₁.1ᵀ * P.1 * g₀.1 = P.1 := by rw [hPv, Matrix.mul_neg, Matrix.neg_mul, ug']
    calc (P⁻¹).1 * g₁.1ᵀ * P.1 * g₀.1 = (P⁻¹).1 * (g₁.1ᵀ * P.1 * g₀.1) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e0]; exact Units.inv_mul P
  have ch : GlobalTheory.SplitFlip.invT h₀ = Q * h₁ * Q⁻¹ := by
    rw [← inv_mul_eq_one]
    apply Units.ext
    simp only [Units.val_mul, Units.val_one, GlobalTheory.SplitFlip.invT_inv_val]
    have e0 : h₀.1ᵀ * Q.1 * h₁.1 = Q.1 := by
      have := congrArg Matrix.transpose uh'
      simpa [hQv, Matrix.transpose_mul, Matrix.mul_assoc] using this
    calc h₀.1ᵀ * (Q.1 * h₁.1 * (Q⁻¹).1) = h₀.1ᵀ * Q.1 * h₁.1 * (Q⁻¹).1 := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [e0]; exact Units.mul_inv Q
  have gi : ∀ {m : ℕ} (x : GL (Fin m) (Fv F v)), GlobalTheory.SplitFlip.gdet x⁻¹ = (GlobalTheory.SplitFlip.gdet x)⁻¹ :=
    fun x => map_inv Matrix.GeneralLinearGroup.det x
  have dg : GlobalTheory.SplitFlip.gdet g₁ = (GlobalTheory.SplitFlip.gdet g₀)⁻¹ := by
    have e0 := congrArg GlobalTheory.SplitFlip.gdet cg
    rw [gi, GlobalTheory.SplitFlip.gdet_mul, GlobalTheory.SplitFlip.gdet_mul, gi, gi, GlobalTheory.SplitFlip.gdet_invT] at e0
    rw [e0, inv_inv, mul_comm, ← mul_assoc, mul_inv_cancel, one_mul]
  have dh : GlobalTheory.SplitFlip.gdet h₁ = (GlobalTheory.SplitFlip.gdet h₀)⁻¹ := by
    have e0 := congrArg GlobalTheory.SplitFlip.gdet ch
    rw [GlobalTheory.SplitFlip.gdet_invT, GlobalTheory.SplitFlip.gdet_mul, GlobalTheory.SplitFlip.gdet_mul, gi] at e0
    rw [e0, mul_comm (GlobalTheory.SplitFlip.gdet Q), mul_assoc, mul_inv_cancel, mul_one]
  rw [e1]
  funext Y
  have hm : ∀ (ψ' : (Fin n × Fin d → Fv F v) → ℂ) y, (LinearMap.funLeft ℂ ℂ (mulH_pk P⁻¹ Q⁻¹) ∘ₗ ι) ψ' y = ι ψ' ((P⁻¹).1 * y * (Q⁻¹).1) := fun _ _ => rfl
  have hy : ι φ'' Y = (LinearMap.funLeft ℂ ℂ (mulH_pk P⁻¹ Q⁻¹) ∘ₗ ι) φ'' (P.1 * Y * Q.1) := by
    rw [hm]
    congr 1
    simp only [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have c1 : (g₀⁻¹).1 = (P⁻¹).1 * g₁.1ᵀ * P.1 := by rw [cg]; rfl
  have c2 : (GlobalTheory.SplitFlip.invT h₀).1 = Q.1 * h₁.1 * (Q⁻¹).1 := by rw [ch]; rfl
  have am : (P⁻¹).1 * (g₁.1ᵀ * (P.1 * Y * Q.1) * h₁.1) * (Q⁻¹).1 = (P⁻¹).1 * g₁.1ᵀ * P.1 * Y * (Q.1 * h₁.1 * (Q⁻¹).1) := by
    simp only [Matrix.mul_assoc]
  rw [hy, key, GlobalTheory.OppLagr.chrW_comp hcm χW hp.resW, GlobalTheory.OppLagr.chrW_comp hcm χX hp.resX]
  simp only [GlobalTheory.SplitFlip.omA, GlobalTheory.SplitFlip.omB]
  rw [hm, am, c1, c2, dg, dh]
  simp only [map_inv, MonoidHom.inv_apply, inv_inv, GlobalTheory.SplitFlip.apow_inv, neg_div]
end UpperTheory.TP
end
theorem UpperTheory.TP.splitFree_k :
    _root_.GlobalTheory.ThK.Dbl.SplitModel_k := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp v t
  exact ⟨_root_.UpperTheory.TP.exists_linW_k B M χX χW om hp v t,
    fun ι hι g hg h hh g₀ h₀ eg eh φ hφ φ₁ hφ₁ hA =>
      _root_.UpperTheory.TP.split_formula_k B M χX χW om hp v t hι g hg h hh g₀ h₀ eg eh φ hφ φ₁ hφ₁ hA⟩
end
