module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatLevel
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatSDa
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieEigenspaceFrameCoordinatesUniqueInvertible
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelCompactEquivariance
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelCompactEquivariance
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblScalBox

open Matrix

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

theorem conj_mem_SB {Y : Type} [TopologicalSpace Y] {φ : Y → ℂ} (h : φ ∈ SB Y) :
    (fun y => starRingEnd ℂ (φ y)) ∈ SB Y :=
  ⟨h.1.comp _, h.2.comp_left (map_zero _)⟩

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

end Local

theorem scal_diag_one : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ κ : UA σ W.J → ℂ, (∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = κ h • fun Y => ι φ (Y * (GlobalTheory.SplitFlip.invT (locMat t c h)).val)) →
    ∀ (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
      (∀ (g : UA σ W.J) (gd : GlobalTheory.DblScal.UD σ W.J),
        ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
          Matrix.fromBlocks (mat g) 0 0 1 →
        ∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), omd gd (boxFun φ₁ φ₂) = boxFun (om (1, g) φ₁) φ₂) →
      GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd →
      (∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₂ ∈ SB (Fin n × Fin d → Fv F v),
        ιd (boxFun φ₁ φ₂) = fun Y => ι φ₁ (Y.submatrix id Sum.inl) *
          starRingEnd ℂ (ι (fun x => starRingEnd ℂ (φ₂ x)) (Y.submatrix id Sum.inr))) →
      ∀ cd, GlobalTheory.DblScal.IsShapeD omd t c ιd cd →
      ∀ h ∈ UAt σ W (evFin F v), ∀ gd : GlobalTheory.DblScal.UD σ W.J,
        ((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) =
          Matrix.fromBlocks (mat h) 0 0 1 → κ h = cd gd := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair v t b c ι hι κ hκ dd omd hdd hspl hres hloc ιd hιd hbox cd
    hcd h hh gd hgd
  have hιL : M.IsLin B.ψ (piW t) (piW (t.comp σ)) (fun u => (b⁻¹).1 * u.map (piW t) * (c⁻¹).1ᵀ) ι := hι

  set φ₀ : (Fin n × Fin d → Fv F v) → ℂ := Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 with hφ₀def
  have h0 : φ₀ ∈ SB (Fin n × Fin d → Fv F v) := GlobalTheory.StdVacuum.indicator_mem_SB v
  have hφ₀0 : φ₀ (fun _ => 0) = 1 := by
    rw [hφ₀def, Set.indicator_of_mem (show (fun _ => (0 : Fv F v)) ∈
      {x : Fin n × Fin d → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from fun i => zero_mem _)]
    rfl
  have hne : ι φ₀ ≠ 0 := by
    intro e
    have e0 : φ₀ = 0 := hιL.bij.injOn h0 (SB _).zero_mem (by rw [e, map_zero])
    have e1 := congrFun e0 (fun _ => 0)
    rw [hφ₀0] at e1
    exact one_ne_zero e1
  obtain ⟨Y₀, hY₀⟩ : ∃ Y, ι φ₀ Y ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hne (funext hc)
  set φ₂ : (Fin n × Fin d → Fv F v) → ℂ := fun x => starRingEnd ℂ (φ₀ x) with hφ₂def
  have h2 : φ₂ ∈ SB (Fin n × Fin d → Fv F v) := conj_mem_SB h0
  have hcc : (fun x => starRingEnd ℂ (φ₂ x)) = φ₀ := funext fun x => Complex.conj_conj _

  have h1mem : (1 : UA σ X.J) ∈ UAt σ X (evFin F v) := by
    intro u _
    have e : mat (1 : UA σ X.J) = 1 := rfl
    rw [e, sub_self, smul_zero]
  obtain ⟨φ₁, ⟨h1, hA1⟩, -⟩ := (GlobalTheory.T.theta_action_exists hP F E σ B n d X W M χX χW om r s r' s' hPair v).1 1 h1mem h hh φ₀ h0
  have hk := hκ h hh φ₀ h0 φ₁ h1 hA1

  have hgdAt : gd ∈ GlobalTheory.DblScal.UDAt σ W.J (evFin F v) := by
    intro u hu
    rw [hgd, GlobalTheory.DblScal.fromBlocks_sub_one, Matrix.fromBlocks_smul, hh u hu]
    simp
  obtain ⟨Φ₁, hΦ₁, hAd⟩ := hloc gd hgdAt (boxFun φ₀ φ₂) (box_mem_SB h0 h2)
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) (Fin n × Fin d) v
  have hRb := rest_box v (hR φ₀ h0) (hR φ₂ h2)
  have e := hAd _ hRb
  rw [tens_box, hres h gd hgd _ (hR φ₀ h0).2 _ (hR φ₂ h2).2, hA1 R (hR φ₀ h0), ← tens_box] at e
  have h0r : boxFun R R (0 : Fin n × Fin d ⊕ Fin n × Fin d → AF F) ≠ 0 := by
    show R 0 * R 0 ≠ 0
    exact mul_ne_zero hR0 hR0
  have eΦ : Φ₁ = boxFun φ₁ φ₂ := eq_of_tens_ne v hRb.1 h0r e.symm

  have hs := hcd gd hgdAt (boxFun φ₀ φ₂) (box_mem_SB h0 h2) Φ₁ hΦ₁ hAd
  rw [eΦ] at hs
  set L := locMat t c h with hL
  have hD : (GlobalTheory.DblScal.locMatD t c gd).val = Matrix.fromBlocks L.val 0 0 1 := by
    show ((GlobalTheory.DblScal.dsum c)⁻¹).val * (((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix _ _ _).map (piW t)) *
      (GlobalTheory.DblScal.dsum c).val = _
    rw [hgd, hL, locMat_val, fromBlocks_map]
    simp only [GlobalTheory.DblScal.dsum, Units.inv_mk, fromBlocks_multiply, Matrix.map_zero _ (map_zero (piW t)),
      Matrix.map_one _ (map_zero (piW t)) (map_one (piW t)), Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
      Matrix.mul_one, Matrix.one_mul]
    congr 1
    simp [Units.mul_inv]
  have hDinv : ((GlobalTheory.DblScal.locMatD t c gd)⁻¹).val = Matrix.fromBlocks (L⁻¹).val 0 0 1 := by
    have hm : Matrix.fromBlocks (L⁻¹).val 0 0 1 * (GlobalTheory.DblScal.locMatD t c gd).val = 1 := by
      rw [hD, fromBlocks_multiply]
      simp [← fromBlocks_one]
    calc ((GlobalTheory.DblScal.locMatD t c gd)⁻¹).val
        = (Matrix.fromBlocks (L⁻¹).val 0 0 1 * (GlobalTheory.DblScal.locMatD t c gd).val) *
            ((GlobalTheory.DblScal.locMatD t c gd)⁻¹).val := by rw [hm, Matrix.one_mul]
      _ = Matrix.fromBlocks (L⁻¹).val 0 0 1 := by
          rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hT : (GlobalTheory.SplitFlip.invT (GlobalTheory.DblScal.locMatD t c gd)).val =
      Matrix.fromBlocks (GlobalTheory.SplitFlip.invT L).val 0 0 1 := by
    rw [GlobalTheory.SplitFlip.invT_val, GlobalTheory.SplitFlip.invT_val, hDinv, fromBlocks_transpose]
    simp
  have hY : Y₀ * L.valᵀ * (GlobalTheory.SplitFlip.invT L).val = Y₀ := by
    rw [GlobalTheory.SplitFlip.invT_val, Matrix.mul_assoc, ← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one,
      Matrix.mul_one]
  have hsl : ∀ A Bm : Matrix (Fin n) (Fin d) (Fv F v), (Matrix.fromCols A Bm).submatrix id Sum.inl = A := by
    intro A Bm; ext i j; rfl
  have hsr : ∀ A Bm : Matrix (Fin n) (Fin d) (Fv F v), (Matrix.fromCols A Bm).submatrix id Sum.inr = Bm := by
    intro A Bm; ext i j; rfl
  have hmul : Matrix.fromCols (Y₀ * L.valᵀ) Y₀ * (GlobalTheory.SplitFlip.invT (GlobalTheory.DblScal.locMatD t c gd)).val =
      Matrix.fromCols Y₀ Y₀ := by
    rw [hT, Matrix.fromCols_mul_fromBlocks]
    simp [hY]
  have eY := congrFun hs (Matrix.fromCols (Y₀ * L.valᵀ) Y₀)
  rw [hbox φ₁ h1 φ₂ h2, Pi.smul_apply, smul_eq_mul, hmul, hbox φ₀ h0 φ₂ h2] at eY
  simp only [hsl, hsr, hcc, hk, Pi.smul_apply, smul_eq_mul, hY] at eY
  have hP0 : ι φ₀ Y₀ * starRingEnd ℂ (ι φ₀ Y₀) ≠ 0 := mul_ne_zero hY₀ ((map_ne_zero _).mpr hY₀)
  apply mul_right_cancel₀ hP0
  linear_combination eY

end GlobalTheory.DblScalBox

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelCompactEquivarianceStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_model_compact_equivariance : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ κ : UA σ W.J → ℂ, (∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = κ h • fun Y => ι φ (Y * (GlobalTheory.SplitFlip.invT (locMat t c h)).val)) →
    ∀ (dd : GlobalTheory.DblScal.DblCo σ X W) (omd : GlobalTheory.DblScal.DblRep σ (n := n) W),
      IsDblCoord (cA σ) (-1) (incM F X.J) (incM F W.J) M.co dd →
      IsUSplitting (adeleClass F) B.ψ dd (actB (cA σ)) omd →
      (∀ (g : UA σ W.J) (gd : GlobalTheory.DblScal.UD σ W.J),
        ((gd : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
          Matrix.fromBlocks (mat g) 0 0 1 →
        ∀ φ₁ ∈ schA F (Fin n × Fin d), ∀ φ₂ ∈ schA F (Fin n × Fin d), omd gd (boxFun φ₁ φ₂) = boxFun (om (1, g) φ₁) φ₂) →
      GlobalTheory.DblScal.LocOps omd v →
      ∀ ιd, GlobalTheory.DblScal.IsLinD B.ψ dd t b c ιd →
      (∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₂ ∈ SB (Fin n × Fin d → Fv F v),
        ιd (boxFun φ₁ φ₂) = fun Y => ι φ₁ (Y.submatrix id Sum.inl) *
          starRingEnd ℂ (ι (fun x => starRingEnd ℂ (φ₂ x)) (Y.submatrix id Sum.inr))) →
      ∀ cd, GlobalTheory.DblScal.IsShapeD omd t c ιd cd →
      ∀ h ∈ UAt σ W (evFin F v), ∀ gd : GlobalTheory.DblScal.UD σ W.J,
        ((gd : GL (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
          Matrix.fromBlocks (mat h) 0 0 1 → κ h = cd gd := by
  first | exact @GlobalTheory.DblScalBox.scal_diag_one | exact GlobalTheory.DblScalBox.scal_diag_one | (intros; apply GlobalTheory.DblScalBox.scal_diag_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergTranslateFixesThetaDeepLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergTranslateFixesThetaDeepLevel
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelTr
theorem exists_nat_mul_eq {E : Type} [Field E] [NumberField E] (w : 𝓞 E) (hw : w ≠ 0) :
    ∃ c : ℕ, 0 < c ∧ ∃ q : 𝓞 E, (c : 𝓞 E) = w * q := by
  refine ⟨Ideal.absNorm (Ideal.span {w}), Nat.pos_of_ne_zero fun h => hw ?_, ?_⟩
  · rwa [Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot] at h
  · obtain ⟨q, hq⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {w}))
    exact ⟨q, by rw [← hq, mul_comm]⟩

theorem inc_mem_OhE {D : D7} {e : D.host.E} (he : IsIntegral ℤ e) : Formalism.MainNotions.StandardLatticesGL3.inc D e ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D :=
  Formalism.UG.CS.incl_int (F := ℚ) (⟨e, he⟩ : 𝓞 D.host.E)

theorem exists_nat_IhE (D : D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) :
    ∃ c : ℕ, 0 < c ∧ ∀ t ∈ Formalism.MainNotions.StandardLatticesGL3.IhE D cc,
      Formalism.MainNotions.StandardLatticesGL3.inc D ((c : D.host.E) * r⁻¹) * t ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D := by
  obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 D.host.E)) r⁻¹
  obtain ⟨a0, ha0, hint⟩ := D.host.AA0.isFractional
  have hw : (s : 𝓞 D.host.E) * a0 ≠ 0 :=
    mul_ne_zero (nonZeroDivisors.ne_zero s.2) (nonZeroDivisors.ne_zero ha0)
  obtain ⟨c, hc, q, hq⟩ := exists_nat_mul_eq _ hw
  refine ⟨c, hc, fun t ht => ?_⟩
  induction ht using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨k, hk, a, ha, s', hs', rfl⟩ := hy
    obtain ⟨b, hb⟩ := hint a ha
    have hcE : (c : D.host.E) = ((s : 𝓞 D.host.E) : D.host.E) * (a0 : D.host.E) * (q : D.host.E) := by
      have := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) hq
      simpa using this
    have e1 : (c : D.host.E) * r⁻¹ * (((k : D.host.K) : D.host.E) * a) =
        (q : D.host.E) * (x : D.host.E) * ((k : D.host.K) : D.host.E) * (b : D.host.E) := by
      have h1 : r⁻¹ * ((s : 𝓞 D.host.E) : D.host.E) = (x : D.host.E) := hxs
      have h2 : (b : D.host.E) = (a0 : D.host.E) * a := by
        have := hb; rw [Algebra.smul_def] at this; exact this
      rw [hcE, h2, ← h1]; ring
    have hk' : IsIntegral ℤ ((k : D.host.K) : D.host.E) := by
      first
        | exact (NumberField.RingOfIntegers.isIntegral_coe k).algebraMap
        | exact IsIntegral.algebraMap k.2
        | exact (NumberField.RingOfIntegers.isIntegral_coe k).map (IsScalarTower.toAlgHom ℤ D.host.K D.host.E)
    rw [← mul_assoc, ← map_mul, e1]
    refine mul_mem (inc_mem_OhE ?_) hs'
    exact ((q.2.mul x.2).mul hk').mul b.2
  | zero => rw [mul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [mul_add]; exact add_mem ha hb
  | neg a _ ha => rw [mul_neg]; exact neg_mem ha
end GlobalTheory.LevelTr

namespace GlobalTheory.LevelTr
open GlobalTheory.BotClassDict

theorem finQ_mt_of_isFinPt {D : D7} (V : HSp D) (hG : V.gram = 1) {g : GA D V} {x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank}
    (hg : IsFinPt V g x) :
    (mt V g).map (finQ D) =
      ((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  refine Matrix.ext fun i j => ?_
  have := congrArg (fun k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank =>
    ((k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j)
    (finStd_of_isFinPt V hG hg)
  rw [finStd_apply] at this
  exact this

theorem finQ_mt_inv_of_isFinPt {D : D7} (V : HSp D) (hG : V.gram = 1) {g : GA D V} {x : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank}
    (hg : IsFinPt V g x) :
    (mt V g⁻¹).map (finQ D) =
      (((x : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
        Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) := by
  have h2 : finStd V hG g⁻¹ = x⁻¹ := by rw [map_inv, finStd_of_isFinPt V hG hg]
  refine Matrix.ext fun i j => ?_
  have := congrArg (fun k : Formalism.MainNotions.StandardLatticesGL3.GA D V.rank =>
    ((k : GL (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) i j) h2
  rw [finStd_apply] at this
  exact this

theorem finQ_finRat {D : D7} (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (i : Fin T.rank) (j : Fin S.rank) :
    finQ D (GlobalTheory.VacUnique.finRat S T γ i j) = Formalism.MainNotions.StandardLatticesGL3.inc D (γ i j) := by
  rw [← finQ_inclR]
  rfl

end GlobalTheory.LevelTr

namespace GlobalTheory.LevelTr
open GlobalTheory.BotClassDict

theorem finQ_finPt {D : D7} (S T : HSp D) (r : D.host.E) (z : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (finPt (S := S) (T := T) rfl rfl r z).map (finQ D) =
      -(Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ • z.map (Formalism.MainNotions.StandardLatticesGL3.inc D)) := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.map_apply, finPt, finQ_finRat]
  simp [Matrix.of_apply, map_neg, map_mul]

theorem finQ_actO_sub {D : D7} (S T : HSp D) (hGS : S.gram = 1) (hGT : T.gram = 1) (r : D.host.E)
    (x : Formalism.MainNotions.StandardLatticesGL3.GA D S.rank) (y : Formalism.MainNotions.StandardLatticesGL3.GA D T.rank) (g : GA D S) (h : GA D T)
    (hg : IsFinPt S g x) (hh : IsFinPt T h y) (z z' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (actO S T g h (finPt rfl rfl r z) - finPt rfl rfl r z').map (finQ D) =
      Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ • (z'.map (Formalism.MainNotions.StandardLatticesGL3.inc D) -
        ((y : GL (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin T.rank) (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) *
          z.map (Formalism.MainNotions.StandardLatticesGL3.inc D) *
          (((x : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
            Matrix (Fin S.rank) (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))) := by
  have e1 : (actO S T g h (finPt rfl rfl r z)).map (finQ D) =
      (mt T h).map (finQ D) * (finPt (S := S) (T := T) rfl rfl r z).map (finQ D) * (mt S g⁻¹).map (finQ D) := by
    rw [actO, Matrix.map_mul, Matrix.map_mul]
  rw [Matrix.map_sub _ (map_sub (finQ D)), e1, finQ_mt_of_isFinPt T hGT hh, finQ_mt_inv_of_isFinPt S hGS hg, finQ_finPt, finQ_finPt]
  simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, smul_sub]
  abel

end GlobalTheory.LevelTr

namespace GlobalTheory.LevelTr
open GlobalTheory.BotClassDict
open scoped TensorProduct

theorem infPart_mt_of_mem_GfC {D : D7} (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) :
    (mt V g).map (infPart D) = 1 := by
  have := congrArg (fun k : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E) =>
    k.val) (MonoidHom.mem_ker.1 hg)
  exact this

theorem infPart_actO_sub {D : D7} (S T : HSp D) (r : D.host.E) (g : GA D S) (h : GA D T) (hg : g ∈ GfC S)
    (hh : h ∈ GfC T) (z z' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    (actO S T g h (finPt rfl rfl r z) - finPt rfl rfl r z').map (infPart D) = 0 := by
  have h0 : ∀ w : Matrix (Fin T.rank) (Fin S.rank) D.host.E,
      (finPt (S := S) (T := T) rfl rfl r w).map (infPart D) = 0 := fun w => GlobalTheory.VacUnique.finRat_inf S T _
  rw [Matrix.map_sub _ (map_sub (infPart D)), actO, Matrix.map_mul, Matrix.map_mul, h0, h0,
    infPart_mt_of_mem_GfC T hh, infPart_mt_of_mem_GfC S (inv_mem hg)]
  simp

end GlobalTheory.LevelTr

namespace GlobalTheory.LevelTr
open GlobalTheory.BotClassDict

theorem ennreal_volume_ratio_step_cancel {R : Type} [CommRing R] (a b c k t : R) (h : a * k = 1) :
    a * (b * (c * k * t)) = c * b * t := by
  linear_combination (b * c * t) * h


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 160000 in
theorem level_translate : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F → ∀ z : Matrix (Fin d) (Fin a) D.host.E,
  ∃ n : ℕ, 0 < n ∧ ∀ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' →
    heisO ψ S T (actO S T g h (finPt hS hT r z) - finPt hS hT r z') F = F := by
  intro D ψ θ S T a d hS hT cc δ r hset x y g h hg hh F hF z
  subst hS
  subst hT
  obtain ⟨U, hUo, hU⟩ := hF.level
  have sdS := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have sdT := GlobalTheory.PlaceModel.isSelfDualC_latFrame T
  obtain ⟨m, hm, hmU⟩ := Formalism.IndefR.Fin.exists_nsmul_mem_cpt' _
    (Formalism.IndefR.Fin.latO_isCompact S T _ _ sdS sdT) (fun w hw n => AddSubgroup.nsmul_mem _ hw n) U hUo
  obtain ⟨N, hN, hNΛ⟩ := Formalism.IndefR.Fin.latO_nsmul_mem S T _ _ sdS sdT
  obtain ⟨c, hc, hcI⟩ := exists_nat_IhE D cc r
  refine ⟨c * (m * N), by positivity, fun z' hz' => ?_⟩
  have hinf := infPart_actO_sub S T r g h hg.1 hh.1 z z'
  have hfin := finQ_actO_sub S T hset.gS hset.gT r x y g h hg hh z z'
  set u := actO S T g h (finPt rfl rfl r z) - finPt rfl rfl r z' with hu
  have hk0 : ((m * N : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  set Y : WO S T := incA D ((m * N : ℕ) : D.host.E)⁻¹ • u with hY
  have hYinf : ∀ i j, infPart D (Y i j) = 0 := by
    intro i j
    have h1 : infPart D (u i j) = 0 := congrFun (congrFun hinf i) j
    rw [hY, Matrix.smul_apply, smul_eq_mul, map_mul, h1, mul_zero]
  have hYfin : ∀ i j, finPart D (Y i j) ∈ intAE D := by
    intro i j
    rw [GlobalTheory.IdemSupport.mem_intAE_iff]
    have e : finPart D (Y i j) = GlobalTheory.BotFormula.toAfE D (finQ D (Y i j)) := (toAfE_finQ _).symm
    rw [e]
    refine (toAfE_int_iff _).2 ?_
    have hu_ij : finQ D (u i j) = Formalism.MainNotions.StandardLatticesGL3.inc D r⁻¹ * (z'.map (Formalism.MainNotions.StandardLatticesGL3.inc D) -
        ((y : GL (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin T.rank) (Fin T.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) *
          z.map (Formalism.MainNotions.StandardLatticesGL3.inc D) *
          (((x : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))⁻¹ : GL (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D)) :
            Matrix (Fin S.rank) (Fin S.rank) (Formalism.MainNotions.StandardLatticesGL3.AE D))) i j :=
      congrFun (congrFun hfin i) j
    obtain ⟨t, ht, et⟩ := hz' i j
    have hkk' : Formalism.MainNotions.StandardLatticesGL3.inc D ((m * N : ℕ) : D.host.E)⁻¹ * ((m * N : ℕ) : Formalism.MainNotions.StandardLatticesGL3.AE D) = 1 := by
      rw [← map_natCast (Formalism.MainNotions.StandardLatticesGL3.inc D), ← map_mul, inv_mul_cancel₀ hk0, map_one]
    have e2 : finQ D (Y i j) = Formalism.MainNotions.StandardLatticesGL3.inc D ((c : D.host.E) * r⁻¹) * t := by
      rw [hY, Matrix.smul_apply, smul_eq_mul, map_mul, finQ_inclR, hu_ij, et, map_mul, map_natCast]
      rw [Nat.cast_mul c (m * N)]
      exact ennreal_volume_ratio_step_cancel _ _ _ _ _ hkk'
    rw [e2]
    exact hcI t ht
  have h1 := hmU _ (hNΛ Y hYfin hYinf)
  have hkY : m • N • Y = u := by
    refine Matrix.ext fun i j => ?_
    show m • N • Y i j = u i j
    rw [← mul_nsmul', nsmul_eq_mul, hY, Matrix.smul_apply, smul_eq_mul, ← mul_assoc]
    have hkk : ((m * N : ℕ) : AE D) * incA D ((m * N : ℕ) : D.host.E)⁻¹ = 1 := by
      rw [← map_natCast (incA D), ← map_mul, mul_inv_cancel₀ hk0, map_one]
    rw [hkk, one_mul]
  have hmem : u ∈ U := hkY ▸ h1
  exact hU u hmem hinf

end GlobalTheory.LevelTr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergTranslateFixesThetaDeepLevelStatement
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergTranslate_fixes_theta_deepLevel : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d)
  (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (r : D.host.E), Setup ψ θ S T cc δ r →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d) (g : GA D S) (h : GA D T), IsFinPt S g x → IsFinPt T h y →
  ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F → ∀ z : Matrix (Fin d) (Fin a) D.host.E,
  ∃ n : ℕ, 0 < n ∧ ∀ z', Formalism.MainNotions.StandardLatticesGL3.CloseTo D cc n (x : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) (y : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) z z' →
    heisO ψ S T (actO S T g h (finPt hS hT r z) - finPt hS hT r z') F = F := by
  first | exact @GlobalTheory.LevelTr.level_translate | exact GlobalTheory.LevelTr.level_translate | (intros; apply GlobalTheory.LevelTr.level_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionQuotientOfContinuousReading
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionQuotientOfContinuousReading
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SecDivision

open NumberField Topology Filter
open scoped Matrix

theorem dvd_of_locally_bounded {K A : Type} [Field K] [NumberField K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.Smooth K A] (σ : K →+* ℂ) {a b : A} (ha : a ≠ 0)
    (H : ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →+* ℂ)), IsOpen B →
      (∀ z ∈ B, (φ z).comp (algebraMap K A) = σ) → (∀ u : A, DifferentiableOn ℂ (fun z => φ z u) B) →
      ∀ z₀ ∈ B, ∃ n : ℕ, n ≠ 0 ∧ ∃ M : ℝ, ∀ᶠ z in 𝓝 z₀, ‖φ z b‖ ^ n ≤ M * ‖φ z a‖ ^ n) : a ∣ b := by
  haveI : IsIntegrallyClosed A := isIntegrallyClosed_of_smooth K A
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  by_contra hn
  obtain ⟨p, hp, s, r, hs, hr, h⟩ := GlobalTheory.ContinuousQuotient.exists_prime_of_not_dvd ha hn
  letI : Algebra K ℂ := σ.toAlgebra
  have h0 : Ideal.Quotient.mkₐ K p s ≠ 0 := fun h => hs (Ideal.Quotient.eq_zero_iff_mem.mp h)
  obtain ⟨e, he⟩ := not_forall.mp fun h => h0 (GlobalTheory.FiniteOrderRule.eq_zero_of_forall_algHom (K := K) (Ω := ℂ) _ h)
  obtain ⟨ι, -, m, B, φ, hB, hφσ, hd, hcov, hne⟩ := GlobalTheory.T.exists_countable_holomorphic_families_smooth K A σ
  let ψ : A →ₐ[K] ℂ := e.comp (Ideal.Quotient.mkₐ K p)
  obtain ⟨i, z₀, hz₀, hψ⟩ := hcov ψ.toRingHom (RingHom.ext fun k => ψ.commutes k)
  obtain ⟨n, hn0, M, hM⟩ := H _ _ _ (hB i) (hφσ i) (hd i) z₀ hz₀
  have hc : ∀ u, ContinuousAt (fun z => φ i z u) z₀ := fun u =>
    (hd i u).continuousOn.continuousAt ((hB i).mem_nhds hz₀)
  have hr0 : φ i z₀ r = 0 := by
    rw [hψ]
    change e (Ideal.Quotient.mk p r) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]
  have hs0 : φ i z₀ s ≠ 0 := by rw [hψ]; exact he
  have hlt : ∀ᶠ z in 𝓝 z₀, M * ‖φ i z r‖ ^ n < ‖φ i z s‖ ^ n := by
    refine ContinuousAt.eventually_lt (continuousAt_const.mul ((hc r).norm.pow n)) ((hc s).norm.pow n) ?_
    simp only [hr0, norm_zero, zero_pow hn0, mul_zero]
    exact pow_pos (norm_pos_iff.2 hs0) n
  obtain ⟨z, hz, h1, h2⟩ := ((hne i z₀ hz₀ a ha).and_eventually (hM.and hlt)).exists
  have h3 : ‖φ i z a‖ ^ n * ‖φ i z s‖ ^ n = ‖φ i z b‖ ^ n * ‖φ i z r‖ ^ n := by
    rw [← mul_pow, ← mul_pow, ← norm_mul, ← norm_mul, ← map_mul, ← map_mul, h]
  have h4 : 0 < ‖φ i z a‖ ^ n := pow_pos (norm_pos_iff.2 hz) n
  have h5 := mul_le_mul_of_nonneg_right h1 (pow_nonneg (norm_nonneg (φ i z r)) n)
  have h6 := mul_lt_mul_of_pos_left h2 h4
  nlinarith

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD _root_.Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.GenericFrames GlobalTheory.AllWt GlobalTheory.FlatLine
  GlobalTheory.CompHt GlobalTheory.FlagTan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem exists_near_frames (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) {A : Type} [CommRing A]
    [Algebra c.F A] (yA : FrPt Xo c A) {m : ℕ} {B : Set (Fin m → ℂ)} (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ))
    (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)) (hB : IsOpen B) (hφ : ∀ a, DifferentiableOn ℂ (fun b => toC (φ b a)) B)
    (hy : ∀ b ∈ B, FrMap (φ b) yA (y b)) {b₀ : Fin m → ℂ} (hb₀ : b₀ ∈ B) :
    ∃ (k : U.Comp) (x₀ : (U.X k).dom), (∃ t, FrBor t (U.un k x₀) (y b₀)) ∧ ∀ V ∈ 𝓝 x₀.1, ∀ᶠ b in 𝓝 b₀,
      ∃ x : (U.X k).dom, x.1 ∈ V ∧ ∃ t, FrBor t (U.un k x) (y b) ∧ ∀ i, t (some i) = 1 := by
  obtain ⟨hr, hty, hsur, -, -, g, e, F, ik, ψ, hef, hun⟩ := hU
  obtain ⟨B', k', P, hB', hb', hs, hP, hyP⟩ :=
    GlobalTheory.AdaptedPeriods.exists_holPeriods_adapted E H Dw l Xo c σ g e F A yA m B φ y hB hφ hy b₀ hb₀
  obtain ⟨k, ⟨x₁, hx₁⟩, t₁, ht₁⟩ := hsur (y b₀)
  obtain ⟨P₁, hP₁, hP₁', hu₁, -⟩ := hun k ⟨x₁, hx₁⟩
  obtain rfl : ik k = k' := F.disj _ _ _ _ hP₁' (hP.1 b₀ hb') (hu₁.symm.trans (ht₁.1.symm.trans (hyP b₀ hb').1))
  obtain ⟨idx, hper, -, honto⟩ := dictionary c σ e _ (U.X k) (ψ k) hσ (F.sig _).1 (F.sig _).2 hr
    (hty k).1 (hty k).2 (hef k) (GlobalTheory.FrameSign.im_neg_of_isPeriod E H Dw l c σ g e _ r (U.X k) (ψ k) hσ hr
      (hty k).1 (hty k).2 (hef k) x₁ hx₁ P₁ hP₁ hP₁')
  have hbor : ∀ x (hx : x ∈ (U.X k).dom), ∀ b ∈ B',
      (∀ a j, pc (U.X k) x (ψ k a : Fin r → E) (idx j).1 (idx j).2 = P b a j) →
      ∃ t, FrBor t (U.un k ⟨x, hx⟩) (y b) ∧ ∀ i, t (some i) = 1 := by
    intro x hx b hb hh
    obtain ⟨P₀, hP₀, hP₀', hux, hud, -⟩ := hun k ⟨x, hx⟩
    have hPS : ∀ v, P₀ v = (1 : Matrix (Fin g) (Fin g) ℂ) *ᵥ P b v := fun v => funext fun j => by
      rw [Matrix.one_mulVec]
      exact (hP₀ v j).trans ((hper _ _ j).trans (hh v j))
    obtain ⟨t, ht, ht1⟩ := GlobalTheory.FrameNorm.frBor_of_triangular_period E H Dw l Xo c σ g e F _ (P b) P₀ 1 (y b)
      (U.un k ⟨x, hx⟩) (hP.1 b hb) hP₀' hPS (fun j j' hj => by
        obtain rfl : j = j' := by
          by_contra hjj
          exact hj (Matrix.one_apply_ne hjj)
        exact ⟨rfl, le_rfl⟩) (hyP b hb).1 hux (hyP b hb).2 hud
    refine ⟨t, ht, fun i => Units.ext ?_⟩
    have := ht1 (e.symm i)
    rw [Equiv.apply_symm_apply, Matrix.one_apply_eq] at this
    exact this
  choose! x₂ hx₂ hr₂ using fun b (hb : b ∈ B') => honto (P b) (hP.1 b hb)
  have hBn : ∀ᶠ b in 𝓝 b₀, b ∈ B' := hB'.mem_nhds hb'
  refine ⟨k, ⟨x₂ b₀, hx₂ b₀ hb'⟩, (hbor _ _ b₀ hb' (hr₂ b₀ hb')).imp fun _ h => h.1, fun V hV => ?_⟩
  have key := GlobalTheory.T.period_coordinates_frames_lift_tendsto E r (U.X k) _ (𝓝 b₀) (x₂ b₀) x₂ (hx₂ b₀ hb') (hBn.mono hx₂) (fun v hv τ i => by
    obtain ⟨a, rfl⟩ : ∃ a, (ψ k a : Fin r → E) = v := ⟨(ψ k).symm ⟨v, hv⟩, by simp⟩
    obtain ⟨j, hj⟩ := idx.surjective (τ, i)
    obtain ⟨rfl, rfl⟩ : τ = (idx j).1 ∧ i = (idx j).2 := by rw [hj]; exact ⟨rfl, rfl⟩
    change Tendsto (fun b => pc (U.X k) (x₂ b) (ψ k a) _ _) _ (𝓝 (pc (U.X k) (x₂ b₀) (ψ k a) _ _))
    rw [hr₂ b₀ hb']
    have hc : ContinuousAt (fun b => P b a j) b₀ :=
      (continuous_apply j).continuousAt.comp ((hP.2 a).continuousOn.continuousAt hBn)
    exact hc.tendsto.congr' (hBn.mono fun b hb => (hr₂ b hb a j).symm)) _
    (inter_mem hV ((FourierCoefficientDomain.isOpen_dom _).mem_nhds (hx₂ b₀ hb')))
  filter_upwards [hBn, key] with b hb ⟨x, ⟨hxV, hx⟩, hxx⟩
  exact ⟨⟨x, hx⟩, hxV, hbor x hx b hb fun a j => (hxx _ _ _).trans (hr₂ b hb a j)⟩

theorem toC_evR_frBor {e : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ secZ Xo c e) {t : Ix Dw → (CAt σ)ˣ}
    {y y' : FrPt Xo c (CAt σ)} (h : FrBor t y y') (ht : ∀ i, t (some i) = 1) :
    toC (evR Xo c f y') = toC (t none : CAt σ) ^ e none * toC (evR Xo c f y) := by
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  rw [evR_frBor hf h, Finset.prod_eq_single none (fun i _ hi => by
    obtain ⟨j, rfl⟩ := Option.ne_none_iff_exists'.1 hi
    rw [ht, one_zpow]) (fun h => absurd (Finset.mem_univ _) h), Units.val_zpow_eq_zpow_val]
  rfl

theorem rdU_apply (U : Unf Xo c σ r) (f : Rul Xo c) (k : U.Comp) (x : (U.X k).dom) :
    rdU U f k x.1 = toC (evR Xo c f (U.un k x)) := dif_pos x.2

attribute [local instance 1100] Subalgebra.algebra in
attribute [local instance 100] IntermediateField.instAlgebraSubtypeMem in
theorem chart_dvd (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) {h : GenFrEx Xo c} (C : FChart h)
    {e e' : Ix Dw → ℤ} {f g : Rul Xo c} (hf : f ∈ secZ Xo c e) (hg : g ∈ secZ Xo c e') (q : FDSec U.X)
    (hq : ∀ k, ContinuousOn (q k) (U.X k).dom)
    (hfg : ∀ z ∈ framesOn U C.Z, rdU U g z.1 z.2 = q z.1 z.2 * rdU U f z.1 z.2) {a b : C.R} (ha0 : a ≠ 0)
    (ha : ∀ (ψ : C.R →ₐ[c.F] CAt σ) (z : FrPt Xo c (CAt σ)), FrMap ψ C.y z → evR Xo c f z = ψ a)
    (hb : ∀ (ψ : C.R →ₐ[c.F] CAt σ) (z : FrPt Xo c (CAt σ)), FrMap ψ C.y z → evR Xo c g z = ψ b) : a ∣ b := by
  classical
  haveI := C.sm
  refine dvd_of_locally_bounded σ ha0 fun m B φ hB hφσ hd z₀ hz₀ => ?_
  let mk : ∀ z ∈ B, C.R →ₐ[c.F] CAt σ := fun z hz =>
    { (show C.R →+* CAt σ from φ z) with commutes' := fun a => RingHom.congr_fun (hφσ z hz) a }
  let φ' : (Fin m → ℂ) → (C.R →ₐ[c.F] CAt σ) := fun z => if hz : z ∈ B then mk z hz else mk z₀ hz₀
  have hφ' : ∀ z ∈ B, ∀ u, toC (φ' z u) = φ z u := by
    intro z hz u
    simp only [φ', dif_pos hz]
    rfl
  choose y hy using fun z => exists_frMap (φ' z) C.y
  obtain ⟨k, x₀, ⟨t₀, ht₀⟩, hnear⟩ := exists_near_frames U hσ hU C.y φ' y hB
    (fun u => (hd u).congr fun z hz => hφ' z hz u) (fun z _ => hy z) hz₀
  obtain ⟨n, hn, hev, η, hη, hη0⟩ := exists_even_sec_evR_ne_zero E H Dw l Xo c σ (y z₀)
  have hηc : ContinuousOn (rdU U η k) (U.X k).dom :=
    (hU.2.2.2.2.1 0 n ⟨fun _ _ _ _ => le_rfl, hev⟩ η hη k).1.continuousOn
  rw [← secZ_nat] at hη
  obtain ⟨w, -, hw⟩ := GlobalTheory.DegCmp.fChart_exists_val C hη
  have hBn : ∀ᶠ z in 𝓝 z₀, z ∈ B := hB.mem_nhds hz₀
  have hdn : (U.X k).dom ∈ 𝓝 x₀.1 := (FourierCoefficientDomain.isOpen_dom _).mem_nhds x₀.2
  have hw0 : φ z₀ w ≠ 0 := by
    rw [← hφ' z₀ hz₀, ← hw _ _ _ (hy z₀)]; exact hη0
  have hx0 : rdU U η k x₀.1 ≠ 0 := by
    letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
    rw [rdU_apply]
    intro h0
    apply hη0
    rw [evR_frBor hη ht₀, show evR Xo c η (U.un k x₀) = 0 from h0, mul_zero]
  let G : (Fin m → ℂ) × Frame (U.X k).Ψ r → ℝ := fun p =>
    ‖(φ p.1 w / rdU U η k p.2) ^ (e' none - e none) * q k p.2 ^ n‖
  have hG : ContinuousAt G (z₀, x₀.1) := by
    have c1 : ContinuousAt (fun p : (Fin m → ℂ) × Frame (U.X k).Ψ r => φ p.1 w) (z₀, x₀.1) :=
      ContinuousAt.comp (g := fun z => φ z w) ((hd w).continuousOn.continuousAt hBn) continuousAt_fst
    have c2 : ContinuousAt (fun p : (Fin m → ℂ) × Frame (U.X k).Ψ r => rdU U η k p.2) (z₀, x₀.1) :=
      ContinuousAt.comp (g := rdU U η k) (hηc.continuousAt hdn) continuousAt_snd
    have c3 : ContinuousAt (fun p : (Fin m → ℂ) × Frame (U.X k).Ψ r => q k p.2) (z₀, x₀.1) :=
      ContinuousAt.comp (g := q k) ((hq k).continuousAt hdn) continuousAt_snd
    exact (((c1.div c2 hx0).zpow₀ _ (Or.inl (div_ne_zero hw0 hx0))).mul (c3.pow n)).norm
  have hlt : ∀ᶠ p in 𝓝 (z₀, x₀.1), G p < G (z₀, x₀.1) + 1 := hG.eventually_lt continuousAt_const (lt_add_one _)
  rw [nhds_prod_eq, eventually_prod_iff] at hlt
  obtain ⟨pa, hpa, pb, hpb, hlt⟩ := hlt
  have hV : ∀ᶠ x in 𝓝 x₀.1, pb x ∧ rdU U η k x ≠ 0 := hpb.and ((hηc.continuousAt hdn).eventually_ne hx0)
  refine ⟨n, hn.ne', G (z₀, x₀.1) + 1, ?_⟩
  filter_upwards [hBn, hpa, hnear _ hV] with z hz hza ⟨x, ⟨hx1, hx2⟩, t, ht, ht1⟩
  have hon : LiesOn C.Z (U.un k x) := fun s => by
    rw [← GlobalTheory.UnifComp.ptF_frBor ht, GlobalTheory.UnifComp.ptF_frMap (hy z), AlgebraicGeometry.Scheme.Hom.comp_apply]
    exact GlobalTheory.UnifComp.liesOn_chart C _
  have e0 : rdU U g k x.1 = q k x.1 * rdU U f k x.1 := hfg ⟨k, x.1⟩ ⟨x.2, hon⟩
  have e1 := toC_evR_frBor hf ht ht1
  have e2 := toC_evR_frBor hg ht ht1
  have e3 := toC_evR_frBor hη ht ht1
  rw [ha _ _ (hy z), hφ' z hz, ← rdU_apply] at e1
  rw [hb _ _ (hy z), hφ' z hz, ← rdU_apply] at e2
  rw [hw _ _ _ (hy z), hφ' z hz, ← rdU_apply] at e3
  have hT : toC (t none : CAt σ) ≠ 0 := (show ℂˣ from t none).ne_zero
  generalize toC (t none : CAt σ) = T at e1 e2 e3 hT
  have e4 : φ z w / rdU U η k x.1 = T ^ n := by
    rw [div_eq_iff hx2, e3, ← zpow_natCast]; rfl
  have e5 : φ z b = T ^ (e' none - e none) * q k x.1 * φ z a := by
    rw [e1, e2, e0, zpow_sub₀ hT]
    field_simp
  have e6 : ‖φ z b‖ ^ n = G (z, x.1) * ‖φ z a‖ ^ n := by
    simp only [G]
    rw [e4, e5, ← norm_pow, ← norm_pow, ← norm_mul, mul_pow, mul_pow, ← zpow_natCast T, ← zpow_mul,
      ← zpow_natCast (T ^ _), ← zpow_mul, mul_comm (n : ℤ)]
  rw [e6]
  exact mul_le_mul_of_nonneg_right (hlt hza hx1).le (pow_nonneg (norm_nonneg _) _)


open IsDedekindDomain Module Formalism.BasicNotions GlobalTheory.FlatCore in
theorem exists_quotient : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (e e' : Ix Dw → ℤ) (f g : Rul Xo c), f ∈ secZ Xo c e → f ∈ suppOn Z → g ∈ secZ Xo c e' → g ∈ suppOn Z → f ≠ 0 → ∀ σ, GoodEmb c σ → ∀ q : FDSec (U σ).X, (∀ k, ContinuousOn (q k) ((U σ).X k).dom) → (∀ z ∈ framesOn (U σ) Z, rdU (U σ) g z.1 z.2 = q z.1 z.2 * rdU (U σ) f z.1 z.2) → ∃ s ∈ secZ Xo c (e' - e), idem Z * s = s ∧ s * f = g := by
  intro E _ _ _ H Dw l Xo c r U x hL Z e e' f g hf hfZ hg hgZ hf0 σ hσ q hq hfg
  obtain ⟨-, -, h, -⟩ := evLaws_genFr_atlas E H Dw l Xo c
  have off : ∀ {u : Rul Xo c}, u ∈ suppOn Z → ∀ Z', Z' ≠ Z → genVal Z' u = 0 := fun hu Z' hZ => by
    rw [genVal_apply h]; exact evC_eq_zero h hZ hu
  have hfz : genVal Z f ≠ 0 := fun h0 => hf0 (secZ_eq_zero_of_genVal hf fun Z' => by
    by_cases hZ : Z' = Z
    · rw [hZ, h0]
    · exact off hfZ Z' hZ)
  obtain ⟨s, hs, hsv⟩ := GlobalTheory.SecGlueInt.exists_secZ_of_regular E H Dw l Xo c h (e' - e)
    (fun Z' => genVal Z' g / genVal Z' f) fun C => by
      by_cases hZ : C.Z = Z
      swap
      · rw [off hgZ _ hZ, zero_div, mul_zero]; exact zero_mem _
      subst hZ
      obtain ⟨a, ha1, ha2⟩ := GlobalTheory.DegCmp.fChart_exists_val C hf
      obtain ⟨b, hb1, hb2⟩ := GlobalTheory.DegCmp.fChart_exists_val C hg
      have ha0 : (a : Om C.Z) ≠ 0 := by rw [ha1]; exact mul_ne_zero (Units.ne_zero _) hfz
      obtain ⟨u, hu⟩ := chart_dvd (U σ) hσ (hL.unf σ hσ) C hf hg q hq hfg (fun h0 => ha0 (by rw [h0]; rfl))
        (ha2 _) (hb2 _)
      have hu' : (b : Om C.Z) = a * u := by rw [hu]; rfl
      have hp : (∏ i, C.t i ^ e' i) = (∏ i, C.t i ^ (e' - e) i) * ∏ i, C.t i ^ e i := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ => by rw [← zpow_add, Pi.sub_apply, sub_add_cancel]
      have : ((∏ i, C.t i ^ (e' - e) i : (Om C.Z)ˣ) : Om C.Z) * (genVal C.Z g / genVal C.Z f) = u := by
        refine mul_left_cancel₀ ha0 ?_
        rw [← hu', ha1, hb1, hp, Units.val_mul]
        field_simp
      rw [this]
      exact u.2
  have hsv' : ∀ Z' : Comp Xo c, genVal Z' s = genVal Z' g / genVal Z' f := fun Z' => (genVal_apply h Z' s).trans (hsv Z')
  refine ⟨s, hs, sub_eq_zero.1 (secZ_eq_zero_of_genVal (sub_mem (idem_mul_mem Z hs).1 hs) fun Z' => ?_),
    sub_eq_zero.1 (secZ_eq_zero_of_genVal (sub_mem (sub_add_cancel e' e ▸ mul_mem_secZ hs hf) hg) fun Z' => ?_)⟩
  · rw [map_sub, map_mul]
    by_cases hZ : Z' = Z
    · rw [hZ, GlobalTheory.DegCmp.genVal_idem_self, one_mul, sub_self]
    · rw [hsv', off hgZ _ hZ, zero_div, mul_zero, sub_self]
  · rw [map_sub, map_mul, hsv']
    by_cases hZ : Z' = Z
    · rw [hZ, div_mul_cancel₀ _ hfz, sub_self]
    · rw [off hgZ _ hZ, zero_div, zero_mul, sub_self]

end GlobalTheory.SecDivision
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionQuotientOfContinuousReadingStatement
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_quotient_of_continuous_reading : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (e e' : Ix Dw → ℤ) (f g : Rul Xo c), f ∈ secZ Xo c e → f ∈ suppOn Z → g ∈ secZ Xo c e' → g ∈ suppOn Z → f ≠ 0 → ∀ σ, GoodEmb c σ → ∀ q : FDSec (U σ).X, (∀ k, ContinuousOn (q k) ((U σ).X k).dom) → (∀ z ∈ framesOn (U σ) Z, rdU (U σ) g z.1 z.2 = q z.1 z.2 * rdU (U σ) f z.1 z.2) → ∃ s ∈ secZ Xo c (e' - e), idem Z * s = s ∧ s * f = g := by
  first | exact @GlobalTheory.SecDivision.exists_quotient | exact GlobalTheory.SecDivision.exists_quotient | (intros; apply GlobalTheory.SecDivision.exists_quotient <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormMulTwistingSectionEqConstMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormMulTwistingSectionEqConstMul
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatTw.PetTw

theorem homN_mul_sig_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
    {Z : Comp Xo c} {G₀ : WTZ E} (s : TwSec U x Z G₀) {G : WTZ E} (hG : Even G.2) {f : Rul Xo c} (hf : f ∈ suppOn Z)
    (σ : c.F →+* ℂ) (z : Σ k, Frame ((U (goodOf c σ)).X k).Ψ r) :
    homN (U (goodOf c σ)) x (G + G₀) (f * s.sig) z = s.cInf σ * homN (U (goodOf c σ)) x G f z := by
  by_cases hz : z ∈ framesOn (U (goodOf c σ)) Z
  · rw [s.homN_mul_sig hG f hz, mul_comm]
  · have h1 : rdU (U (goodOf c σ)) (f * s.sig) z.1 z.2 = 0 :=
      rdU_eq_zero _ (mul_mem_suppOn f s.sig_mem_suppOn) hz
    have h2 : rdU (U (goodOf c σ)) f z.1 z.2 = 0 := rdU_eq_zero _ hf hz
    show _ * (‖rdU (U (goodOf c σ)) (f * s.sig) z.1 z.2‖ * _) = s.cInf σ * (_ * (‖rdU (U (goodOf c σ)) f z.1 z.2‖ * _))
    rw [h1, h2, norm_zero, zero_mul, zero_mul, mul_zero, mul_zero, mul_zero]

theorem petAt_mul_sig : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (G₀ : WTZ E) (s : TwSec U x Z G₀) (G : WTZ E), Even G.2 → ∀ f ∈ suppOn Z, ∀ (σ : c.F →+* ℂ) (D : D7) (V : HSp D) (dict : GA D V → Σ k, Frame ((U (goodOf c σ)).X k).Ψ r) (μ : Measure (AutQ V)), petAt (U (goodOf c σ)) x V dict μ (G + G₀) (f * s.sig) = s.cInf σ * petAt (U (goodOf c σ)) x V dict μ G f := by
  intro E _ _ _ H Dw l Xo c r U x Z G₀ s G hG f hf σ D V dict μ
  rw [petAt_eq, petAt_eq]
  have e : (fun q : AutQ V => homN (U (goodOf c σ)) x (G + G₀) (f * s.sig) (dict q.out)) =
      s.cInf σ • fun q : AutQ V => homN (U (goodOf c σ)) x G f (dict q.out) :=
    funext fun q => homN_mul_sig_eq s hG hf σ (dict q.out)
  rw [e, eLpNorm'_const_smul _ (by norm_num), ENNReal.toReal_mul, Real.eNorm_eq_ofReal (s.cInf_pos σ).le,
    ENNReal.toReal_ofReal (s.cInf_pos σ).le]

end GlobalTheory.FlatTw.PetTw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormMulTwistingSectionEqConstMulStatement
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.petersson_norm_mul_twistingSection_eq_const_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (Z : Comp Xo c) (G₀ : WTZ E) (s : TwSec U x Z G₀) (G : WTZ E), Even G.2 → ∀ f ∈ suppOn Z, ∀ (σ : c.F →+* ℂ) (D : D7) (V : HSp D) (dict : GA D V → Σ k, Frame ((U (goodOf c σ)).X k).Ψ r) (μ : Measure (AutQ V)), petAt (U (goodOf c σ)) x V dict μ (G + G₀) (f * s.sig) = s.cInf σ * petAt (U (goodOf c σ)) x V dict μ G f := by
  first | exact @GlobalTheory.FlatTw.PetTw.petAt_mul_sig | exact GlobalTheory.FlatTw.PetTw.petAt_mul_sig | (intros; apply GlobalTheory.FlatTw.PetTw.petAt_mul_sig <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordOfIndep
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links

set_option autoImplicit false

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.BigOn.Exp

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_coord_of_indep {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    (e : K →+* ℂ) (rd : V →ₛₗ[e] W)
    (hF : ∀ (n : ℕ) (v : Fin n → V), LinearIndependent K v → LinearIndependent ℂ fun c => rd (v c))
    {μ : ℂ} {f f' : V} (hf : f ≠ 0) (h : rd f' = μ • rd f) : ∃ u : K, e u = μ := by
  have hrf : rd f ≠ 0 := (hF 1 (fun _ => f) (linearIndependent_unique_iff.2 hf)).ne_zero 0
  by_cases hli : LinearIndependent K ![f, f']
  · have h2 := hF 2 _ hli
    have h2' : LinearIndependent ℂ ![rd f, rd f'] := by
      convert h2 using 1
      funext c
      fin_cases c <;> rfl
    have := (LinearIndependent.pair_iff.1 h2') (-μ) 1 (by rw [h, one_smul, neg_smul, neg_add_cancel])
    exact absurd this.2 one_ne_zero
  · rw [LinearIndependent.pair_iff] at hli
    push_neg at hli
    obtain ⟨s, t, hst, hne⟩ := hli
    have ht : t ≠ 0 := by
      intro ht0
      rw [ht0, zero_smul, add_zero] at hst
      exact hne ((smul_eq_zero.1 hst).resolve_right hf) ht0
    have hf' : f' = (-(s / t)) • f := by
      have : t • f' = -(s • f) := eq_neg_of_add_eq_zero_right hst
      calc f' = t⁻¹ • (t • f') := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
        _ = _ := by rw [this, smul_neg, smul_smul, ← neg_smul, div_eq_inv_mul]
    refine ⟨-(s / t), ?_⟩
    have h3 : e (-(s / t)) • rd f = μ • rd f := by rw [← h, hf', map_smulₛₗ]
    exact smul_left_injective ℂ hrf h3

end GlobalTheory.BigOn.Exp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCountableCharts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open Filter Topology

noncomputable section

namespace GlobalTheory.CountableCharts

theorem isHolTo_finChart_symm {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    (c : GlobalTheory.AlgChart p σ D) : IsHolTo c.finChart.target fun z => (c.finChart.symm z).1 := by
  have h1 := GlobalTheory.LocLift.isHolTo_comp (GlobalTheory.TrueCx.TorHolo.isHolTo_symm c) c.finChart.open_target
    (β := fun z => (EuclideanSpace.equiv (Fin D) ℂ).symm z)
    (EuclideanSpace.equiv (Fin D) ℂ).symm.differentiable.differentiableOn fun z hz => hz
  refine GlobalTheory.LocLift.isHolTo_congr h1 fun v _ => ?_
  simp [GlobalTheory.AlgChart.finChart_symm_apply]

theorem exists_countable_charts : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (d : ℕ), SmoothOfRelativeDimension d s → QuasiCompact s → ∀ (Q : Set (Fin d → ℂ) → ((Fin d → ℂ) → (Sp ℂ ⟶ X)) → Prop), (∀ B y b₀, IsOpen B → b₀ ∈ B → (∀ b ∈ B, y b ≫ s = spMap (RingHom.id ℂ)) → IsHolTo B y → ∃ B', IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ Q B' y) → ∃ (K : Type) (_ : Countable K) (B : K → Set (Fin d → ℂ)) (y : K → (Fin d → ℂ) → (Sp ℂ ⟶ X)), (∀ i, IsOpen (B i) ∧ (∀ b ∈ B i, y i b ≫ s = spMap (RingHom.id ℂ)) ∧ IsHolTo (B i) (y i) ∧ Set.InjOn (y i) (B i) ∧ Q (B i) (y i)) ∧ ∀ x : Sp ℂ ⟶ X, x ≫ s = spMap (RingHom.id ℂ) → ∃ i, x ∈ y i '' B i := by
  intro X s d hs hq Q hQ
  haveI := hs
  haveI := hq
  haveI : Smooth s := SmoothOfRelativeDimension.smooth d s
  have hc : ∀ x : GlobalTheory.CxPts s (RingHom.id ℂ), ∃ c : GlobalTheory.AlgChart s (RingHom.id ℂ) d, x ∈ c.e.source :=
    fun x => GlobalTheory.AlgChart.exists_mem_source x
  choose c hc using hc
  have hB : ∀ x : GlobalTheory.CxPts s (RingHom.id ℂ), ∃ B', IsOpen B' ∧ (c x).finChart x ∈ B' ∧
      B' ⊆ (c x).finChart.target ∧ Q B' (fun z => ((c x).finChart.symm z).1) := fun x =>
    hQ _ _ _ (c x).finChart.open_target ((c x).finChart.map_source (hc x))
      (fun b _ => ((c x).finChart.symm b).2) (isHolTo_finChart_symm (c x))
  choose B' hB'o hB'm hB'sub hB'Q using hB
  have hN : ∀ x : GlobalTheory.CxPts s (RingHom.id ℂ),
      (c x).finChart.source ∩ (c x).finChart ⁻¹' B' x ∈ 𝓝 x := fun x =>
    ((c x).finChart.isOpen_inter_preimage (hB'o x)).mem_nhds ⟨hc x, hB'm x⟩
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.countable_cover_nhds hN
  refine ⟨T, hTc.to_subtype, fun i => B' i, fun i z => ((c i).finChart.symm z).1, fun i =>
    ⟨hB'o i, fun b _ => ((c i).finChart.symm b).2,
      GlobalTheory.LocLift.isHolTo_mono (isHolTo_finChart_symm (c i)) (hB'o i) (hB'sub i), ?_, hB'Q i⟩, ?_⟩
  · intro a ha b hb hab
    exact (c i).finChart.symm.injOn (by simpa using hB'sub i ha) (by simpa using hB'sub i hb)
      (Subtype.ext hab)
  · intro x hx
    have hmem : (⟨x, hx⟩ : GlobalTheory.CxPts s (RingHom.id ℂ)) ∈ ⋃ t ∈ T,
        (c t).finChart.source ∩ (c t).finChart ⁻¹' B' t := hTU ▸ Set.mem_univ _
    obtain ⟨t, ht, hm⟩ := Set.mem_iUnion₂.1 hmem
    exact ⟨⟨t, ht⟩, (c t).finChart ⟨x, hx⟩, hm.2, by
      show ((c t).finChart.symm ((c t).finChart ⟨x, hx⟩)).1 = x
      rw [(c t).finChart.left_inv hm.1]⟩

end GlobalTheory.CountableCharts
end
end
