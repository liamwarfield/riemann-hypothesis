module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilArchimedeanFactor
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleProductAlgebraWeilRepRangeEqTop

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleTwistTransportEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.TripleAssembly.Transport
end GlobalTheory.TripleAssembly.Transport
open GlobalTheory.TripleAssembly.Transport in
theorem GlobalTheory.TripleAssembly.triple_twist_transport_eq : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        ((∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb,
            GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Ψ) =
              GlobalTheory.TripleAssembly.liftPure Γ.M R.p Rf.p (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ) ∧
          ∀ Φ ∈ algF ψ θ true A B, ∃ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb,
            GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Ψ = Φ) ∧
        ((∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb,
            GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Ψ) =
              GlobalTheory.TripleAssembly.liftPure Γ.M' R.p' Rf.p' (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ) ∧
          ∀ Φ ∈ algF ψ θ false A₁ B, ∃ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb,
            GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Ψ = Φ) := by
  intro hHowe hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h htA htB R Rf hM
  have hgood : Γ.M.IsGood ψ := h.ψ ▸ hM.triple.geo.hM
  have hgood' : Γ.M'.IsGood ψ := h.ψ ▸ hM.triple.geo.hM'
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := h.ψ ▸ hM.triple.base.std
  have hZ : Γ.W.J.det ≠ 0 := by
    rw [h.JX, Matrix.det_smul, Matrix.det_submatrix_equiv_self, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit X).ne_zero
  have hY : Γ.V.J.det ≠ 0 := by
    rw [h.JW, one_smul]; exact (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W).ne_zero
  have hY' : Γ.V'.J.det ≠ 0 := by
    rw [h.JW₁, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W₁).ne_zero
  obtain ⟨T₁, hT₁, hi₁⟩ := GlobalTheory.ThetaTransformInj.linear_injective D Γ.M ψ (sgn true W).gram e hgood hstd hY hZ
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit (sgn true W)).ne_zero
  obtain ⟨T₂, hT₂, hi₂⟩ := GlobalTheory.ThetaTransformInj.linear_injective D Γ.M' ψ (sgn false W₁).gram e hgood' hstd hY' hZ
    (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit (sgn false W₁)).ne_zero
  have hle := GlobalTheory.TripleAssembly.darbAlg_le_schA _ _ _ Γ.M Bs.ψ Bs.emb hM.triple.geo.hM
  have hle' := GlobalTheory.TripleAssembly.darbAlg_le_schA _ _ _ Γ.M' Bs.ψ Bs.emb hM.triple.geo.hM'
  obtain ⟨hI, hI'⟩ := _root_.GlobalTheory.T.theta_image_eq_span_darboux hHowe hPr D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h htA htB R Rf hM
  have ex1 := exists_factor T₁ _ (fun Φ hΦ => hi₁ Φ (hle hΦ))
    (GlobalTheory.TripleAssembly.liftPure Γ.M R.p Rf.p (GlobalTheory.TripleAssembly.vacIm Γ Rf))
  have ex2 := exists_factor T₂ _ (fun Φ hΦ => hi₂ Φ (hle' hΦ))
    (GlobalTheory.TripleAssembly.liftPure Γ.M' R.p' Rf.p' (GlobalTheory.TripleAssembly.vacIm Γ Rf))
  refine ⟨⟨fun Ψ hΨ => ?_, fun Φ hΦ => ?_⟩, ⟨fun Ψ hΨ => ?_, fun Φ hΦ => ?_⟩⟩
  · have H : ∃ q : (Matrix (Fin X.rank) (Fin W.rank) (AE D) → ℂ) →ₗ[ℂ] _, ∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb,
        q (GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Ψ) =
          GlobalTheory.TripleAssembly.liftPure Γ.M R.p Rf.p (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ := by
      obtain ⟨q, hq⟩ := ex1
      exact ⟨q, fun Ψ hΨ => by rw [← hT₁ Ψ (hle hΨ)]; exact hq Ψ hΨ⟩
    unfold GlobalTheory.TripleAssembly.mapA GlobalTheory.TripleAssembly.thetaLift
    rw [dite_eq_left H]
    exact H.choose_spec Ψ hΨ
  · rw [← hI T₁ hT₁] at hΦ
    obtain ⟨Ψ, hΨ, rfl⟩ := Submodule.mem_map.1 hΦ
    exact ⟨Ψ, hΨ, (hT₁ Ψ (hle hΨ)).symm⟩
  · have H : ∃ q : (Matrix (Fin X.rank) (Fin W₁.rank) (AE D) → ℂ) →ₗ[ℂ] _, ∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb,
        q (GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Ψ) =
          GlobalTheory.TripleAssembly.liftPure Γ.M' R.p' Rf.p' (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ := by
      obtain ⟨q, hq⟩ := ex2
      exact ⟨q, fun Ψ hΨ => by rw [← hT₂ Ψ (hle' hΨ)]; exact hq Ψ hΨ⟩
    unfold GlobalTheory.TripleAssembly.mapB GlobalTheory.TripleAssembly.thetaLift
    rw [dite_eq_left H]
    exact H.choose_spec Ψ hΨ
  · rw [← hI' T₂ hT₂] at hΦ
    obtain ⟨Ψ, hΨ, rfl⟩ := Submodule.mem_map.1 hΦ
    exact ⟨Ψ, hΨ, (hT₂ Ψ (hle' hΨ)).symm⟩
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_twist_transport : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        ((∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb,
            GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Ψ) =
              GlobalTheory.TripleAssembly.liftPure Γ.M R.p Rf.p (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ) ∧
          ∀ Φ ∈ algF ψ θ true A B, ∃ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M Bs.ψ Bs.emb,
            GlobalTheory.TripleRead.thO Γ.M ψ (sgn true W).gram e Ψ = Φ) ∧
        ((∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb,
            GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Ψ) =
              GlobalTheory.TripleAssembly.liftPure Γ.M' R.p' Rf.p' (GlobalTheory.TripleAssembly.vacIm Γ Rf) Ψ) ∧
          ∀ Φ ∈ algF ψ θ false A₁ B, ∃ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb,
            GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e Ψ = Φ) := by
  first | exact @_root_.GlobalTheory.TripleAssembly.triple_twist_transport_eq | exact _root_.GlobalTheory.TripleAssembly.triple_twist_transport_eq | (intros; apply _root_.GlobalTheory.TripleAssembly.triple_twist_transport_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PlacewisePureTensorFinitePlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
open scoped Classical
namespace GlobalTheory.PlacePureFin
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.FinDecomp
theorem placewise_pure_tensor_finite_places : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (W W₁ X : HSp D) (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F W.rank W₁.rank) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F W.rank W₁.rank),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ (hJ : Γ.W.J = D.host.xi0 • (X.gramᵀ).submatrix e e), ∀ g ∈ GfC X,
    ∃ hv : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J,
      (∀ v, hv v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W (GlobalTheory.AdelicU.evFin D.host.F v)) ∧
      (∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)))
        (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) →
        ∃ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ,
          (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ₁ v = Γ.M.vac v) ∧
          (∀ v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin D.host.F v) (om (1, hv v)) (φ v) (φ₁ v)) ∧
          om (1, GlobalTheory.TripleRead.toUX X e hJ g) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ₁) ∧
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)))
        (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M'.vac v) →
        ∃ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ,
          (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ₁ v = Γ.M'.vac v) ∧
          (∀ v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin D.host.F v) (om' (1, hv v)) (φ v) (φ₁ v)) ∧
          om' (1, GlobalTheory.TripleRead.toUX X e hJ g) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ₁ := by
  intro hP D W W₁ X e Bs Γ Xc om om' R Rf hM hJ g hg
  have hT := hM.triple
  let h : UA D.sp.cm.sig Γ.W.J := GlobalTheory.TripleRead.toUX X e hJ g
  have harch : ∀ u : AF D.host.F, At (evI D.host.F) u → u • (mat h - 1) = 0 := GlobalTheory.T.finiteUnitaryPoint_darboux_trivial_archimedean D X e hJ g hg
  obtain ⟨S₀, hS₀⟩ := _root_.GlobalTheory.T.spherical_vector_fixes_vacua hP _ _ _ Bs _ _ Γ Xc om om' hT
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.idempotentCut_unitaryPoint_stabilizes_lattices _ _ _ Bs _ _ Γ hT.geo h
  have hfixB : ∀ (S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F))) (e : AF D.host.F) (he : e * e = e), S₀ ∪ S₁ ⊆ S →
      (∀ w ∈ S, ∀ u : AF D.host.F, At (evFin D.host.F w) u → u * e = 0) →
      (∀ w ∉ S, ∀ u : AF D.host.F, At (evFin D.host.F w) u → u * e = 0 ∨ u * e = u) →
      (∀ (f : SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank))) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), _ → ℂ),
        (∀ w, φ w ∈ GlobalTheory.WeilM.SB _) → (∀ w ∉ S, φ w = Γ.M.vac w) → om (1, loc e he h) (pure f φ) = pure f φ) ∧
      (∀ (f : SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank))) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), _ → ℂ),
        (∀ w, φ w ∈ GlobalTheory.WeilM.SB _) → (∀ w ∉ S, φ w = Γ.M'.vac w) → om' (1, loc e he h) (pure f φ) = pure f φ) := by
    intro S e he hS hin hout
    obtain ⟨hl, hl'⟩ := hS₁ S e he (Finset.subset_union_right.trans hS) hout
    refine hS₀ S (Finset.subset_union_left.trans hS) (loc e he h) ?_ ?_ hl hl'
    · intro u hu; rw [mat_loc, phi_sub_one, smul_comm, harch u hu, smul_zero]
    · intro w hw u hu; rw [mat_loc, phi_sub_one, smul_smul, hin w hw u hu, zero_smul]
  refine ⟨fun v => loc (idem _ v) (idem_mul_self v) h, fun v u hu => ?_, fun f φ hSB hvac => ?_, fun f φ hSB hvac => ?_⟩
  · show u • (mat (loc (idem _ v) (idem_mul_self v) h) - 1) = 0
    rw [mat_loc, phi_sub_one, smul_smul, mul_idem_of_evFin hu, zero_smul]
  · exact side Γ.M Bs.ψ hT.geo.hM om h (fun v hh hhv φ hφ => GlobalTheory.T.weilRepresentationLocality_unitaryGroupW_pairVW _ _ _ Bs _ _ Γ Xc om om' hT v hh hhv φ hφ)
      (S₀ ∪ S₁) (fun S e he hS hin hout => (hfixB S e he hS hin hout).1) f φ hSB hvac
  · exact side Γ.M' Bs.ψ hT.geo.hM' om' h (fun v hh hhv φ hφ => GlobalTheory.T.weilRepresentation_localAtFinitePlace_unitaryGroupW _ _ _ Bs _ _ Γ Xc om om' hT v hh hhv φ hφ)
      (S₀ ∪ S₁) (fun S e he hS hin hout => (hfixB S e he hS hin hout).2) f φ hSB hvac
end GlobalTheory.PlacePureFin
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_pure_tensor_placewise_finite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (W W₁ X : HSp D) (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
    (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps D.host.F W.rank W₁.rank) (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps D.host.F W.rank W₁.rank),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ (hJ : Γ.W.J = D.host.xi0 • (X.gramᵀ).submatrix e e), ∀ g ∈ GfC X,
    ∃ hv : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Γ.W.J,
      (∀ v, hv v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W (GlobalTheory.AdelicU.evFin D.host.F v)) ∧
      (∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W.rank × Fin (W.rank + W₁.rank)))
        (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) →
        ∃ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ,
          (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ₁ v = Γ.M.vac v) ∧
          (∀ v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin D.host.F v) (om (1, hv v)) (φ v) (φ₁ v)) ∧
          om (1, GlobalTheory.TripleRead.toUX X e hJ g) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ₁) ∧
      ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)))
        (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
        (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = Γ.M'.vac v) →
        ∃ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ,
          (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ₁ v = Γ.M'.vac v) ∧
          (∀ v, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin D.host.F v) (om' (1, hv v)) (φ v) (φ₁ v)) ∧
          om' (1, GlobalTheory.TripleRead.toUX X e hJ g) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ₁ := by
  first | exact @_root_.GlobalTheory.PlacePureFin.placewise_pure_tensor_finite_places | exact _root_.GlobalTheory.PlacePureFin.placewise_pure_tensor_finite_places | (intros; apply _root_.GlobalTheory.PlacePureFin.placewise_pure_tensor_finite_places <;> assumption)
end
end

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.TripleAssembly.EqFin
end GlobalTheory.TripleAssembly.EqFin
namespace GlobalTheory.TripleAssembly.EqFin
set_option maxHeartbeats 2000000 in
theorem theta_triple_maps_equivariant_on_finite_vectors : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        (∀ g ∈ GfC X, ∀ Φ ∈ algF ψ θ true A B, GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (ωA (1, g) Φ) = GlobalTheory.TripleAssembly.opFin ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) g (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ)) ∧
          ∀ g ∈ GfC X, ∀ Φ ∈ algF ψ θ false A₁ B, GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (ωB (1, g) Φ) = GlobalTheory.TripleAssembly.opFin ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) g (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ) := by
  intro hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨oA, -⟩ := _root_.GlobalTheory.T.triple_algebra_map_surjective hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨⟨dA, rA⟩, ⟨dB, rB⟩⟩ :=
    _root_.GlobalTheory.T.triple_twist_transport hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h hTA hTB R Rf hM
  have gM : Γ.M.IsGood Bs.ψ := hM.triple.geo.hM
  have gM' : Γ.M'.IsGood Bs.ψ := hM.triple.geo.hM'
  have c1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW 1 = 1 := Subtype.ext ((congrArg _ (map_one (matHom W))).trans (map_one _))
  have c1' : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁ 1 = 1 := Subtype.ext ((congrArg _ (map_one (matHom W₁))).trans (map_one _))
  have hsA : ∀ᶠ v in Filter.cofinite, Rf.p v (Γ.M.vac v) = GlobalTheory.TripleAssembly.vacIm Γ Rf v :=
    Filter.Eventually.of_forall fun v => rfl
  have hsB : ∀ᶠ v in Filter.cofinite, Rf.p' v (Γ.M'.vac v) = GlobalTheory.TripleAssembly.vacIm Γ Rf v := by
    refine Filter.eventually_cofinite.2 ((Xc.T.finite_toSet).subset fun v hv => ?_)
    by_contra hn
    exact hv (hM.fin.sph v hn).1.symm
  have key : ∀ g ∈ GfC X, ∃ T : Module.End ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf),
      (∀ Φ ∈ algF ψ θ true A B, GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (ωA (1, g) Φ) =
        T (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ)) ∧
      ∀ Φ ∈ algF ψ θ false A₁ B, GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (ωB (1, g) Φ) =
        T (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ) := by
    intro g hg
    obtain ⟨hv, hvU, fA, fB⟩ := _root_.GlobalTheory.T.theta_pure_tensor_placewise_finite hP D W W₁ X e Bs Γ Xc om om' R Rf hM h.JX g hg
    choose a ha using fun v => GlobalTheory.T.exists_localOperator_thetaQuotient_finitePlace D.sp.cm.sig W.rank W₁.rank Bs Γ Xc om om' R Rf hM v (hv v) (hvU v)
    obtain ⟨T₀, hT₀⟩ := GlobalTheory.TripleAssembly.exists_rtensOp (GlobalTheory.TripleAssembly.vacIm Γ Rf) a
    refine ⟨LinearMap.lTensor R.Pi T₀, ?_, ?_⟩
    · have st := GlobalTheory.TripleAssembly.EqFin.darbAlg_stable Γ.M Bs.ψ Bs.emb gM R.p Rf.p (GlobalTheory.TripleAssembly.vacIm Γ Rf) hsA
        (om (1, GlobalTheory.TripleRead.toUX X e h.JX g)) T₀ (fun f φ hφ hφv => by
          obtain ⟨φ₁, h1, h1v, hAct, hO⟩ := fA f φ hφ hφv
          refine ⟨φ₁, h1, h1v, hO, ?_⟩
          rw [hT₀ _ (Filter.eventually_cofinite.1 ((hφv.and hsA).mono fun v hv' => by rw [hv'.1, hv'.2]))]
          congr 1
          funext v
          exact (ha v).1 (φ v) (hφ v) (φ₁ v) (h1 v) (hAct v))
      intro Φ hΦ
      obtain ⟨Ψ, hΨ, rfl⟩ := rA Φ hΦ
      have hs := GlobalTheory.TripleAssembly.darbAlg_le_schA D.sp.cm.sig Γ.V Γ.W Γ.M Bs.ψ Bs.emb gM hΨ
      have e1 := hTA Ψ hs 1 g
      rw [c1] at e1
      have s1 := (st Ψ hΨ).1
      have s2 := (st Ψ hΨ).2
      have d1 := dA _ s1
      have d2 := dA Ψ hΨ
      have x1 := congrArg (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) e1.symm
      have x2 := congrArg (LinearMap.lTensor R.Pi T₀) d2.symm
      exact x1.trans (d1.trans (s2.trans x2))
    · have st := GlobalTheory.TripleAssembly.EqFin.darbAlg_stable Γ.M' Bs.ψ Bs.emb gM' R.p' Rf.p' (GlobalTheory.TripleAssembly.vacIm Γ Rf) hsB
        (om' (1, GlobalTheory.TripleRead.toUX X e h.JX g)) T₀ (fun f φ hφ hφv => by
          obtain ⟨φ₁, h1, h1v, hAct, hO⟩ := fB f φ hφ hφv
          refine ⟨φ₁, h1, h1v, hO, ?_⟩
          rw [hT₀ _ (Filter.eventually_cofinite.1 ((hφv.and hsB).mono fun v hv' => by rw [hv'.1, hv'.2]))]
          congr 1
          funext v
          exact (ha v).2 (φ v) (hφ v) (φ₁ v) (h1 v) (hAct v))
      intro Φ hΦ
      obtain ⟨Ψ, hΨ, rfl⟩ := rB Φ hΦ
      have hs := GlobalTheory.TripleAssembly.darbAlg_le_schA D.sp.cm.sig Γ.V' Γ.W Γ.M' Bs.ψ Bs.emb gM' hΨ
      have e1 := hTB Ψ hs 1 g
      rw [c1'] at e1
      exact (congrArg (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf) e1.symm).trans ((dB _ (st Ψ hΨ).1).trans
        (((st Ψ hΨ).2).trans (congrArg (LinearMap.lTensor R.Pi T₀) (dB Ψ hΨ).symm)))
  have opEq : ∀ g, ∀ T : Module.End ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf),
      (∀ Φ ∈ algF ψ θ true A B, GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (ωA (1, g) Φ) =
        T (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ)) →
      GlobalTheory.TripleAssembly.opFin ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) g = T := by
    intro g T hTg
    have H : ∃ T : Module.End ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf), ∀ Φ ∈ algF ψ θ true A B,
        GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (ωA (1, g) Φ) = T (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ) := ⟨T, hTg⟩
    unfold GlobalTheory.TripleAssembly.opFin
    rw [dite_eq_left H]
    apply LinearMap.ext
    intro y
    have hy : y ∈ (algF ψ θ true A B).map (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) := by rw [oA]; trivial
    obtain ⟨Φ, hΦ, rfl⟩ := hy
    rw [← H.choose_spec Φ hΦ, hTg Φ hΦ]
  refine ⟨fun g hg Φ hΦ => ?_, fun g hg Φ hΦ => ?_⟩
  · obtain ⟨T, h1, -⟩ := key g hg
    rw [opEq g T h1]
    exact h1 Φ hΦ
  · obtain ⟨T, h1, h2⟩ := key g hg
    rw [opEq g T h1]
    exact h2 Φ hΦ
end GlobalTheory.TripleAssembly.EqFin
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_triple_maps_equivariant : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        (∀ g ∈ GfC X, ∀ Φ ∈ algF ψ θ true A B, GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (ωA (1, g) Φ) = GlobalTheory.TripleAssembly.opFin ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) g (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ)) ∧
          ∀ g ∈ GfC X, ∀ Φ ∈ algF ψ θ false A₁ B, GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (ωB (1, g) Φ) = GlobalTheory.TripleAssembly.opFin ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) g (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ) := by
  first | exact @_root_.GlobalTheory.TripleAssembly.EqFin.theta_triple_maps_equivariant_on_finite_vectors | exact _root_.GlobalTheory.TripleAssembly.EqFin.theta_triple_maps_equivariant_on_finite_vectors | (intros; apply _root_.GlobalTheory.TripleAssembly.EqFin.theta_triple_maps_equivariant_on_finite_vectors <;> assumption)
end
