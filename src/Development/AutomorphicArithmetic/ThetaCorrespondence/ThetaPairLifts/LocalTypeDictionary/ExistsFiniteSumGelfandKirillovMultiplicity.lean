module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterSubgroupTransposeGramRealPlace
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IrreducibleGkLeMultiplicitySpan
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftOfCuspFormIsSmoothAutomorphic

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspFormsEqISupIrreducibleGK
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KTypeProjectionOfKFinite
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FiniteDimensionalSpanOfAdmissibleKType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
theorem GlobalTheory.KTypeAdm.finiteDimensional_span_of_admissible_KType : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    ∀ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W → ψ ∈ W → GlobalTheory.KTypeProj.KStable θ M W →
    ∀ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, x ≠ 0 → 0 < (b x x).re) →
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, star (b x y) = b y x) →
      (∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (rTr V (atTau θ V τ g) y) = b (rTr V (atTau θ V τ g⁻¹) x) y) →
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) →
    FiniteDimensional ℂ (GlobalTheory.KTypeProj.typeSpan (GlobalTheory.KTypeProj.rhoK θ M) (W ⊓ GlobalTheory.CuspGK.gkGen θ M ψ)
      (GlobalTheory.CuspGK.gkGen θ M ψ)) := by
  intro hP D θ V S M hθ ψ hψ _hcusp W hW hψW hWK b hpos hherm _hK hskew
  set G := GlobalTheory.CuspGK.gkGen θ M ψ with hGdef
  have hsm := GlobalTheory.KTypeAdm.isAutFunSm_of_mem_gkGen θ M hθ hψ
  obtain ⟨U, hU, hlev⟩ := GlobalTheory.KTypeAdm.level_gkGen θ M hψ
  have hY : GlobalTheory.KTypeProj.KStable θ M (W ⊓ G) :=
    GlobalTheory.KTypeProj.kStable_inf θ M hWK (GlobalTheory.KTypeProj.kStable_gkGen θ M ψ)
  haveI hYf : FiniteDimensional ℂ ↥(W ⊓ G) := Submodule.finiteDimensional_of_le inf_le_left
  have hcont : ∀ f ∈ W ⊓ G, Continuous f := fun f hf => (hsm f hf.2).cont
  choose ρ hρc hρT using GlobalTheory.T.exists_continuousRep_rightTranslation_maxCompactStable θ V S M hθ (W ⊓ G) hYf hY hcont
  have hGK := GlobalTheory.CuspGK.isGKSub_gkGen θ M ψ
  have hGsm : G ≤ GlobalTheory.Mem.AutSpace.SmFun θ V := fun f hf => (hsm f hf).smooth
  have hGC : ∀ τ Z, ∀ f ∈ G, RderC θ V τ Z f ∈ G := fun τ Z f hf => by
    obtain ⟨h1, h2⟩ := GlobalTheory.SmoothAutCheck.parts_mem (V := V) τ Z
    exact G.add_mem (hGK.lie τ _ h1 f hf) (G.smul_mem _ (hGK.lie τ _ h2 f hf))
  have hsym : ∀ τ k, ∀ x ∈ G, ∀ y ∈ G, b x (gelf θ V τ k y) = b (gelf θ V τ k x) y := fun τ =>
    GlobalTheory.T.gelfandInvariants_symmetric_of_derivativeAdjoint θ V hθ τ G hGsm (hGC τ) b (GlobalTheory.T.complexDerivative_adjoint_of_skew_form θ V τ G b (hskew τ))
  let F : D.what₂.Tau × ℕ → (GA D V → ℂ) → (GA D V → ℂ) := fun i => gelf θ V i.1 i.2
  have hFG : ∀ i, ∀ x ∈ G, F i x ∈ G := fun i => GlobalTheory.KTypeAdm.gelf_mem_of_isGKSub θ M hGK i.1 i.2
  have hFadd : ∀ i, ∀ x ∈ G, ∀ y ∈ G, F i (x + y) = F i x + F i y := fun i x hx y hy =>
    (GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) i.1 i.2).add x (hGsm hx) y (hGsm hy)
  have hFsmul : ∀ i (a : ℂ), ∀ x ∈ G, F i (a • x) = a • F i x := fun i a x _ =>
    (GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) i.1 i.2).smul a x
  have hFcomm : ∀ i j, ∀ x ∈ G, F i (F j x) = F j (F i x) := fun i j x hx =>
    GlobalTheory.CentreComm.comm_gelf (GlobalTheory.Mem.AutSpace.linOnSm_gelf (θ := θ) (V := V) i.1 i.2)
      (fun Z => GlobalTheory.CentreComm.gelf_RderC hθ i.1 j.1 i.2 Z) j.2 x (hGsm hx)
  obtain ⟨Wz, hWz, hψz, hWzst⟩ := hψ.zfin
  haveI := hWz
  haveI : FiniteDimensional ℂ ↥(Wz ⊓ G) := Submodule.finiteDimensional_of_le inf_le_left
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_jointEigenDecomposition_commuting_symmetricOps F (Wz ⊓ G) inferInstance
    (fun i x hx => ⟨hWzst i.1 i.2 x hx.1, hFG i x hx.2⟩) (fun i x hx y hy => hFadd i x hx.2 y hy.2)
    (fun i a x hx => hFsmul i a x hx.2) (fun i j x hx => hFcomm i j x hx.2) b (fun x hx => hpos x hx.2)
    (fun x hx y hy => hherm x hx.2 y hy.2) (fun i x hx y hy => hsym i.1 i.2 x hx.2 y hy.2)
  have hGS : G ≤ ⨆ c ∈ C, Submodule.span ℂ
      {h | h ∈ G ∧ ∀ i : D.what₂.Tau × ℕ, gelf θ V i.1 i.2 h = c i • h} := by
    refine GlobalTheory.CuspGK.gkGen_le θ M ?_ (GlobalTheory.T.isGKSubmodule_iSup_gelfandJointEigenspaces θ V S M hθ ψ hψ C)
    have := hC ψ ⟨hψz, GlobalTheory.CuspGK.mem_gkGen θ M ψ⟩
    refine (iSup₂_mono fun c _ => Submodule.span_mono ?_) this
    exact fun h hh => ⟨hh.1.2, hh.2⟩
  set P := GlobalTheory.KTypeProj.typeSpan (GlobalTheory.KTypeProj.rhoK θ M) (W ⊓ G) G with hPdef
  have hPG : P ≤ G := GlobalTheory.KTypeProj.typeSpan_le _ _ _
  have hPst : ∀ i, ∀ x ∈ P, F i x ∈ P := fun i => GlobalTheory.T.gelfandInvariant_mem_intertwinedTypeSpan θ V S M hθ ψ hψ (W ⊓ G) i.1 i.2
  have hdec := GlobalTheory.T.mem_iSup_jointEigenspaces_inf_of_stableSubmodule F G P C hFG hFadd hFsmul hPG hPst (fun x hx => hGS hx)
  have htype : ∀ τ, ∀ h ∈ P, GlobalTheory.Published.AutFin.HasTypeAt θ V τ (M.ε τ) (M.fr τ) (ρ τ) h := by
    intro τ
    let Q : Submodule ℂ (GA D V → ℂ) :=
      { carrier := {h | GlobalTheory.Published.AutFin.HasTypeAt θ V τ (M.ε τ) (M.fr τ) (ρ τ) h}
        add_mem' := fun ha hb x => Submodule.add_mem _ (ha x) (hb x)
        zero_mem' := fun x => Submodule.zero_mem _
        smul_mem' := fun c f hf x => Submodule.smul_mem _ c (hf x) }
    have hPQ : P ≤ Q := by
      refine iSup₂_le fun T hT => ?_
      rintro _ ⟨w, hw, rfl⟩
      exact hρT τ T hT.2 ⟨w, hw⟩
    exact fun h hh => hPQ hh
  have hfr : GlobalTheory.Published.AutFin.IsFrameFam V M.ε M.fr := fun τ => ⟨M.fr_unit τ, M.fr_gram τ⟩
  have hfin : ∀ c : D.what₂.Tau × ℕ → ℂ, FiniteDimensional ℂ
      (Submodule.span ℂ (GlobalTheory.Published.AutFin.forms θ V U M.ε M.fr ρ (fun τ k => c (τ, k)))) := fun c =>
    hP.harishChandraFinite D θ hθ V U hU M.ε M.fr hfr (fun _ => ↥(W ⊓ G)) ρ hρc _
  have hle : P ≤ C.sup fun c =>
      Submodule.span ℂ (GlobalTheory.Published.AutFin.forms θ V U M.ε M.fr ρ (fun τ k => c (τ, k))) := by
    intro x hx
    have := hdec x hx
    rw [← Finset.sup_eq_iSup] at this
    have key : ∀ c : D.what₂.Tau × ℕ → ℂ, Submodule.span ℂ {h | h ∈ P ∧ ∀ i, F i h = c i • h} ≤
        Submodule.span ℂ (GlobalTheory.Published.AutFin.forms θ V U M.ε M.fr ρ (fun τ k => c (τ, k))) := fun c =>
      Submodule.span_mono (by
        rintro h ⟨hP', hc⟩
        exact ⟨hsm h (hPG hP'), fun u hu hu' g => hlev h (hPG hP') u hu hu' g, fun τ => htype τ h hP',
          fun τ k => hc (τ, k)⟩)
    exact Finset.sup_mono_fun (fun c _ => key c) this
  haveI : ∀ c : D.what₂.Tau × ℕ → ℂ, FiniteDimensional ℂ
      (Submodule.span ℂ (GlobalTheory.Published.AutFin.forms θ V U M.ε M.fr ρ (fun τ k => c (τ, k)))) := hfin
  exact Submodule.finiteDimensional_of_le hle
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_KType_span_finiteDimensional : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    ∀ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W → ψ ∈ W → GlobalTheory.KTypeProj.KStable θ M W →
    ∀ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, x ≠ 0 → 0 < (b x x).re) →
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, star (b x y) = b y x) →
      (∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (rTr V (atTau θ V τ g) y) = b (rTr V (atTau θ V τ g⁻¹) x) y) →
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) →
    FiniteDimensional ℂ (GlobalTheory.KTypeProj.typeSpan (GlobalTheory.KTypeProj.rhoK θ M) (W ⊓ GlobalTheory.CuspGK.gkGen θ M ψ)
      (GlobalTheory.CuspGK.gkGen θ M ψ)) := by
  first | exact @_root_.GlobalTheory.KTypeAdm.finiteDimensional_span_of_admissible_KType | exact _root_.GlobalTheory.KTypeAdm.finiteDimensional_span_of_admissible_KType | (intros; apply _root_.GlobalTheory.KTypeAdm.finiteDimensional_span_of_admissible_KType <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
namespace GlobalTheory.KTypeProj
theorem kType_projection_mem : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ∀ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, x ≠ 0 → 0 < (b x x).re) →
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, star (b x y) = b y x) →
      (∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (rTr V (atTau θ V τ g) y) = b (rTr V (atTau θ V τ g⁻¹) x) y) →
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) →
    ∃ e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ), e ψ = ψ ∧
      (∀ A : Submodule ℂ (GA D V → ℂ), A ≤ GlobalTheory.CuspGK.gkGen θ M ψ → GlobalTheory.CuspGK.IsGKSub θ M A → ∀ x ∈ A, e x ∈ A) ∧
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, e (e x) = e x) ∧
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, b (e x) y = b x (e y)) ∧
      FiniteDimensional ℂ ((GlobalTheory.CuspGK.gkGen θ M ψ).map e) := by
  intro hP D θ V S M hθ ψ hψ hcusp hWex b hpos hherm hKadj hLie
  obtain ⟨W, hWfd, hψW, hWK⟩ := hWex
  have hWK' : KStable θ M W := fun τ g hg f hf => hWK τ g hg.1 hg.2 f hf
  set G := GlobalTheory.CuspGK.gkGen θ M ψ with hGdef
  set F := typeSpan (rhoK θ M) (W ⊓ G) G with hFdef
  haveI hFfd : FiniteDimensional ℂ F := _root_.GlobalTheory.T.admissible_KType_span_finiteDimensional hP θ V S M hθ ψ hψ hcusp W hWfd hψW hWK' b hpos hherm hKadj hLie
  have hFG : F ≤ G := typeSpan_le _ _ _
  have hprojG : ∀ F' : Submodule ℂ (GA D V → ℂ), F' ≤ G → FiniteDimensional ℂ F' →
      ∃ π : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ), (∀ x, π x ∈ F') ∧ ∀ x, ∀ f ∈ F', b (π x) f = b x f :=
    fun F' hF' hfd => GlobalTheory.T.exists_orthogonalProjection_posDef_sesquilinear_finiteDim b F' hfd (fun x hx => hpos x (hF' hx)) (fun x hx y hy => hherm x (hF' hx) y (hF' hy))
  obtain ⟨e, heF, hechar⟩ := hprojG F hFG hFfd
  have hfix : ∀ f ∈ F, e f = f := by
    intro f hf
    by_contra hne
    have hd : e f - f ∈ F := F.sub_mem (heF f) hf
    have h0 : b (e f - f) (e f - f) = 0 := by
      rw [show b (e f - f) = b (e f) - b f from map_sub b _ _, LinearMap.sub_apply, hechar f _ hd, sub_self]
    have := hpos _ (hFG hd) (sub_ne_zero.2 hne)
    rw [h0] at this
    simp at this
  have hψF : ψ ∈ F := le_typeSpan _ inf_le_right ⟨hψW, GlobalTheory.CuspGK.mem_gkGen θ M ψ⟩
  have hinvK : ∀ i : KIdx M, GlobalTheory.CuspGK.InK M i.1.1 i.1.2⁻¹ ∧ i.1.2⁻¹⁻¹ = i.1.2 := fun i => GlobalTheory.T.inMaxCompactOfModelFrame_inv M i.1.1 i.1.2 i.2
  let inv : KIdx M → KIdx M := fun i => ⟨(i.1.1, i.1.2⁻¹), (hinvK i).1⟩
  have hρG : ∀ i, ∀ x ∈ G, rhoK θ M i x ∈ G := (kStable_iff θ M G).1 (kStable_gkGen θ M ψ)
  have hadj : ∀ i, ∀ x ∈ G, ∀ y ∈ G, b (rhoK θ M i x) y = b x (rhoK θ M (inv i) y) := by
    intro i x hx y hy
    have h := hKadj i.1.1 i.1.2⁻¹ (hinvK i).1 x hx y hy
    rw [(hinvK i).2] at h
    exact h.symm
  refine ⟨e, hfix ψ hψF, ?_, fun x _ => hfix _ (heF x), ?_, ?_⟩
  · intro A hAG hA x hx
    obtain ⟨Y, hYfd, hxY, hYK⟩ := GlobalTheory.T.kFinite_of_mem_gKModuleGeneratedBy θ M hθ ψ hψ ⟨W, hWfd, hψW, hWK'⟩ x (hAG hx)
    haveI := hYfd
    have hst := (kStable_iff θ M (Y ⊓ A)).1 (kStable_inf θ M hYK (kStable_of_isGKSub θ M hA))
    have := GlobalTheory.T.typeSpanProjection_preserves_finiteDim_invariant_subspace b G (rhoK θ M) inv hpos hherm hρG hadj hprojG (W ⊓ G) e heF hechar (Y ⊓ A)
      inferInstance (inf_le_right.trans hAG) hst x ⟨hxY, hx⟩
    exact this.2
  · intro x hx y hy
    have h1 : b (e x) (y - e y) = 0 := by
      rw [← hherm _ (G.sub_mem hy (hFG (heF y))) _ (hFG (heF x)), map_sub, LinearMap.sub_apply,
        hechar y _ (heF x), sub_self, star_zero]
    have h2 : b (e x) y = b (e x) (e y) := by
      rw [map_sub] at h1
      exact sub_eq_zero.1 h1
    rw [h2, hechar x _ (heF y)]
  · refine Submodule.finiteDimensional_of_le (S₂ := F) ?_
    rintro _ ⟨x, -, rfl⟩
    exact heF x
end GlobalTheory.KTypeProj
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kType_projection_of_kFinite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ∀ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, x ≠ 0 → 0 < (b x x).re) →
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, star (b x y) = b y x) →
      (∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (rTr V (atTau θ V τ g) y) = b (rTr V (atTau θ V τ g⁻¹) x) y) →
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) →
    ∃ e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ), e ψ = ψ ∧
      (∀ A : Submodule ℂ (GA D V → ℂ), A ≤ GlobalTheory.CuspGK.gkGen θ M ψ → GlobalTheory.CuspGK.IsGKSub θ M A → ∀ x ∈ A, e x ∈ A) ∧
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, e (e x) = e x) ∧
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, b (e x) y = b x (e y)) ∧
      FiniteDimensional ℂ ((GlobalTheory.CuspGK.gkGen θ M ψ).map e) := by
  first | exact @_root_.GlobalTheory.KTypeProj.kType_projection_mem | exact _root_.GlobalTheory.KTypeProj.kType_projection_mem | (intros; apply _root_.GlobalTheory.KTypeProj.kType_projection_mem <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspFormPeterssonNonvanishingGelfandKirillov
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
namespace GlobalTheory.CuspGKPet
open Matrix GlobalTheory.PointAtPlaceHom GlobalTheory.Mem.RealTranslate GlobalTheory.CuspGK GlobalTheory.CuspDecay GlobalTheory.Mem.Lift
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
theorem exists_petersson_pairing_gelfandKirillov_generator : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ∃ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, x ≠ 0 → 0 < (b x x).re) ∧
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, star (b x y) = b y x) ∧
      (∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (rTr V (atTau θ V τ g) y) = b (rTr V (atTau θ V τ g⁻¹) x) y) ∧
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) := by
  intro hP D θ V S M hθ ψ h1 h2 _
  obtain ⟨b, b1, b2, b3, b4⟩ := exists_form_cuspSub (V := V) hP.cuspRapidDecay hθ
  have hle : gkGen θ M ψ ≤ cuspSub θ V := gkGen_le θ M (A := cuspSub θ V) ⟨h1, h2⟩
    ⟨fun _ _ hg _ hf => rTr_mem_cuspSub hθ hg.1 hf, fun _ _ hX _ hf => Rder_mem_cuspSub hθ hX hf⟩
  exact ⟨b, fun x hx => b1 x (hle hx), fun x hx y hy => b2 x (hle hx) y (hle hy),
    fun τ g hg x hx y hy => b3 τ g hg.1 x (hle hx) y (hle hy),
    fun τ X hX x hx y hy => b4 τ X hX x (hle hx) y (hle hy)⟩
end GlobalTheory.CuspGKPet
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_petersson_nonvanishing_gelfandKirillov : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ∃ b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ,
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, x ≠ 0 → 0 < (b x x).re) ∧
      (∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ, star (b x y) = b y x) ∧
      (∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (rTr V (atTau θ V τ g) y) = b (rTr V (atTau θ V τ g⁻¹) x) y) ∧
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ x ∈ GlobalTheory.CuspGK.gkGen θ M ψ, ∀ y ∈ GlobalTheory.CuspGK.gkGen θ M ψ,
        b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) := by
  first | exact @_root_.GlobalTheory.CuspGKPet.exists_petersson_pairing_gelfandKirillov_generator | exact _root_.GlobalTheory.CuspGKPet.exists_petersson_pairing_gelfandKirillov_generator | (intros; apply _root_.GlobalTheory.CuspGKPet.exists_petersson_pairing_gelfandKirillov_generator <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
namespace GlobalTheory.CuspGK
variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)
theorem cuspForm_mem_iSup_irreducible_gK : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ψ ∈ ⨆ (A : Submodule ℂ (GA D V → ℂ)) (_ : A ≤ GlobalTheory.CuspGK.gkGen θ M ψ ∧ GlobalTheory.CuspGK.IsIrrGKSub θ M A), A := by
  intro hP D θ V S M hθ ψ hA hC hW
  obtain ⟨b, hpos, hherm, hK, hL⟩ := _root_.GlobalTheory.T.cusp_form_petersson_nonvanishing_gelfandKirillov hP θ V S M hθ ψ hA hC hW
  obtain ⟨e, he1, he2, he3, he4, he5⟩ := _root_.GlobalTheory.T.kType_projection_of_kFinite hP θ V S M hθ ψ hA hC hW b hpos hherm hK hL
  refine GlobalTheory.T.mem_iSup_irreducible_of_fixed_projector (IsGKSub θ M) (isGKSub_sInf θ M) (gkGen θ M ψ) (isGKSub_gkGen θ M ψ) b
    hpos hherm (fun A hAle hAP => ?_) e he2 he3 he4 he5 ψ (mem_gkGen θ M ψ) he1
  have hperp : ∀ f ∈ gkGen θ M ψ ⊓ ⨅ a ∈ A, LinearMap.ker (b a),
      f ∈ gkGen θ M ψ ∧ ∀ a ∈ A, b a f = 0 := fun f hf => by
    rw [Submodule.mem_inf] at hf
    exact ⟨hf.1, fun a ha => LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hf.2 a) ha)⟩
  have hmk : ∀ f, f ∈ gkGen θ M ψ → (∀ a ∈ A, b a f = 0) → f ∈ gkGen θ M ψ ⊓ ⨅ a ∈ A, LinearMap.ker (b a) :=
    fun f h1 h2 => Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun a => (Submodule.mem_iInf _).2 fun ha =>
      LinearMap.mem_ker.2 (h2 a ha)⟩
  refine ⟨fun τ g hg f hf => ?_, fun τ X hX f hf => ?_⟩
  · obtain ⟨hfN, hf0⟩ := hperp f hf
    refine hmk _ ((isGKSub_gkGen θ M ψ).k τ g hg f hfN) fun a ha => ?_
    rw [hK τ g hg a (hAle ha) f hfN]
    exact hf0 _ (hAP.k τ g⁻¹ hg.inv a ha)
  · obtain ⟨hfN, hf0⟩ := hperp f hf
    refine hmk _ ((isGKSub_gkGen θ M ψ).lie τ X hX f hfN) fun a ha => ?_
    rw [hL τ X hX a (hAle ha) f hfN, hf0 _ (hAP.lie τ X hX a ha), neg_zero]
end GlobalTheory.CuspGK
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForms_eq_iSup_irreducible_gK : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ψ ∈ ⨆ (A : Submodule ℂ (GA D V → ℂ)) (_ : A ≤ GlobalTheory.CuspGK.gkGen θ M ψ ∧ GlobalTheory.CuspGK.IsIrrGKSub θ M A), A := by
  first | exact @_root_.GlobalTheory.CuspGK.cuspForm_mem_iSup_irreducible_gK | exact _root_.GlobalTheory.CuspGK.cuspForm_mem_iSup_irreducible_gK | (intros; apply _root_.GlobalTheory.CuspGK.cuspForm_mem_iSup_irreducible_gK <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspFormGKIsotypicDecomposition
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.StructureOfKFiniteVectors
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
namespace GlobalTheory.KFinStruct
section Model
open Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.KFinVec
variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
end Model
theorem kFinite_vector_structure : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau),
    (∃ p : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), p ≠ 0) ∧
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
      ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), M.rep τ g (v : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) ∧
    (∀ X ∈ lieAt V τ, ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), ∃ w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ),
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0) ∧
    ∀ B : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), B ≠ ⊥ →
      (∀ X ∈ lieAt V τ, ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), v ∈ B →
        HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 → w ∈ B) → B = ⊤ := by
  intro hPr D V S M τ
  rw [kFin_eq]
  obtain ⟨h1, h2, h3⟩ := model hPr.kFiniteVectorsUnitary (M.ds τ) (M.fr_unit τ) (M.fr_gram τ)
  exact ⟨h1, fun g _ hg v => GlobalTheory.KFinVec.isKStableOn_kFinSub _ _ _ hg _ v.2, h2, h3⟩
end GlobalTheory.KFinStruct
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.structure_of_kFinite_vectors : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau),
    (∃ p : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), p ≠ 0) ∧
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
      ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), M.rep τ g (v : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) ∧
    (∀ X ∈ lieAt V τ, ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), ∃ w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ),
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0) ∧
    ∀ B : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), B ≠ ⊥ →
      (∀ X ∈ lieAt V τ, ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), v ∈ B →
        HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 → w ∈ B) → B = ⊤ := by
  first | exact @_root_.GlobalTheory.KFinStruct.kFinite_vector_structure | exact _root_.GlobalTheory.KFinStruct.kFinite_vector_structure | (intros; apply _root_.GlobalTheory.KFinStruct.kFinite_vector_structure <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FiniteSumOfGKModuleMaps
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
namespace GlobalTheory.FiniteGKSum
open GlobalTheory.SeriesToClosure Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes
open Matrix Filter
open scoped InnerProductSpace Topology
section Sums
variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ε : Fin V.rank → Bool)
  (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (P : Matrix (Fin V.rank) (Fin V.rank) ℂ)
end Sums
section Closure
variable {D : D7} {V : HSp D}
end Closure
section Avg
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {τ : D.what₂.Tau}
  {ε : Fin V.rank → Bool} {P : Matrix (Fin V.rank) (Fin V.rank) ℂ}
end Avg
end GlobalTheory.FiniteGKSum
namespace GlobalTheory.FiniteGKSum
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.PointAtPlaceHom GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes GlobalTheory.SeriesToClosure
  GlobalTheory.FiniteGKSum in
theorem finite_sum_of_gKModule_maps : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (V : HSp D) (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ (τ : D.what₂.Tau) (φ : GA D V → ℂ), IsAutFunSm θ V φ → IsTypeAt θ V τ (S τ) φ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ φ ∈ W ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ h ∈ W, rTr V (atTau θ V τ g) h ∈ W) →
    ∃ (m : ℕ) (T : Fin m → (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] (GA D V → ℂ)))
      (p : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ (M.ε τ) (M.σ τ) (M.fr τ) (T j)) ∧ φ = ∑ j, T j (p j) := by
  intro hPr D θ V S M hθ τ φ hφ hT ⟨W, hWf, hφW, hWK⟩
  haveI := hWf
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  obtain ⟨H', i1, i2, σ', lam', ε', P', hE', hD', hP', hJ', hx⟩ := hT
  obtain ⟨rfl, rfl⟩ := GlobalTheory.SignedParTest.isEnum_unique (M.enum τ) hE'
  obtain ⟨U, hU⟩ := hPr.discreteSeriesHermitianUnique _ (M.ε τ) (M.lam τ)
    (GlobalTheory.Published.HermitianUnique.isHCParam_of_isDS (M.enum τ).1 (M.ds τ)) _ (M.fr τ) P' (M.fr_unit τ) hP'
    (M.fr_gram τ) hJ' _ _ (M.σ τ) σ' (M.ds τ) hD'
  haveI : CompleteSpace (M.H τ) := (M.ds τ).1
  have hσ : Std (M.ε τ) (M.σ τ) := std_of_isDS hPr.harishChandraModules (M.ds τ)
  have hP := M.fr_unit τ
  have hJ := M.fr_gram τ
  have hx' : ∀ x, HasTypeAll (lieSet (M.ε τ)) (UJset (M.ε τ)) (M.σ τ) (res θ V τ (M.fr τ) φ x) := fun x =>
    hasTypeAll_transport _ H' (M.H τ) _ (M.σ τ) (gramAt D V τ) (Jm (M.ε τ)) (M.fr τ) (isUnit_gram hP' hJ') hP hJ U
      hU (fun g => φ (x * atTau θ V τ g)) (hasTypeAll_iff.2 (hx x))
  choose Sx hS hc v ℓ C h using hx'
  have hZ : ∀ e, KFinFun (M.ε τ) e →
      avg θ V τ (M.ε τ) (M.fr τ) e φ ∈ gkSums θ V τ (M.ε τ) (M.σ τ) (M.fr τ) := by
    intro e he
    obtain ⟨m, a, c, ha, hQ, hA⟩ := exists_rank_one hθ hP hJ hσ he
    choose T hT hTv using fun j => exists_gkMap hθ hP hJ hσ hφ hS hc h (hA j)
    refine ⟨m, T, fun j => ⟨a j, mem_kFin_iff.2 (ha j)⟩, hT, funext fun x => ?_⟩
    have h1 := (moves_avg hθ hP hJ hσ he φ x _ _ _ _ (hS x) (hc x) (h x)).1.2.2.2.2 1 (one_mem_UJ _)
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [res_one hθ hP, sigma_one hσ.1, hQ, map_sum, map_smul, smul_eq_mul] at h1
    have h2 := h1.unique (hasSum_sum fun j _ => (Expn.summable_term (h x) (c j) (hσ.2.2.1 _ (ha j))).hasSum)
    simp only [Finset.sum_apply, hTv]
    exact h2
  have hk : Continuous fun k : KG (M.ε τ) => atTau θ V τ ((M.fr τ)⁻¹ * toMK k * M.fr τ) :=
    (continuousOn_atTau hθ V τ).comp_continuous continuous_conjK
      fun k => conj_inv_mem hP hJ (K_le_UJ (toMK_mem_K k))
  have hmem : φ ∈ gkSums θ V τ (M.ε τ) (M.σ τ) (M.fr τ) ⊓ W := by
    haveI : FiniteDimensional ℂ (gkSums θ V τ (M.ε τ) (M.σ τ) (M.fr τ) ⊓ W : Submodule ℂ _) :=
      Submodule.finiteDimensional_of_le inf_le_right
    refine mem_of_approx fun K hK δ hδ => ?_
    obtain ⟨e, he, hap⟩ := GlobalTheory.T.exists_compactFinite_approxIdentity _ (M.ε τ) (GA D V)
      (fun x k => φ (x * atTau θ V τ ((M.fr τ)⁻¹ * toMK k * M.fr τ)))
      (hφ.cont.comp (continuous_fst.mul (hk.comp continuous_snd))) K hK δ hδ
    refine ⟨avg θ V τ (M.ε τ) (M.fr τ) e φ, ⟨hZ e he, avg_mem hθ hP hJ hWK hφ.cont hφW he⟩, fun x hxK => ?_⟩
    have h4 : φ (x * atTau θ V τ ((M.fr τ)⁻¹ * toMK (1 : KG (M.ε τ)) * M.fr τ)) = φ x := res_one hθ hP φ x
    have h3 := hap x hxK
    rw [h4] at h3
    exact h3
  obtain ⟨m, T, p, hT, hsum⟩ := hmem.1
  exact ⟨m, T, p, hT, hsum⟩
end GlobalTheory.FiniteGKSum
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gKModule_map_finite_sum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (V : HSp D) (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ (τ : D.what₂.Tau) (φ : GA D V → ℂ), IsAutFunSm θ V φ → IsTypeAt θ V τ (S τ) φ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ φ ∈ W ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ h ∈ W, rTr V (atTau θ V τ g) h ∈ W) →
    ∃ (m : ℕ) (T : Fin m → (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] (GA D V → ℂ)))
      (p : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ (M.ε τ) (M.σ τ) (M.fr τ) (T j)) ∧ φ = ∑ j, T j (p j) := by
  first | exact @_root_.GlobalTheory.FiniteGKSum.finite_sum_of_gKModule_maps | exact _root_.GlobalTheory.FiniteGKSum.finite_sum_of_gKModule_maps | (intros; apply _root_.GlobalTheory.FiniteGKSum.finite_sum_of_gKModule_maps <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
namespace GlobalTheory.CuspGKId
theorem cuspForm_local_sum_model : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (V : HSp D) (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ (τ : D.what₂.Tau) (φ : GA D V → ℂ), IsAutFunSm θ V φ → IsTypeAt θ V τ (S τ) φ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ φ ∈ W ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ h ∈ W, rTr V (atTau θ V τ g) h ∈ W) →
    ∃ (m : ℕ) (T : Fin m → (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] (GA D V → ℂ)))
      (p : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ (M.ε τ) (M.σ τ) (M.fr τ) (T j)) ∧ φ = ∑ j, T j (p j) := _root_.GlobalTheory.T.gKModule_map_finite_sum
theorem cuspForm_kFinite_structure : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (V : HSp D) (S : D.what₂.Tau → SPar)
    (M : Formalism.IndefR.Mult.DSModel V S) (τ : D.what₂.Tau),
    (∃ p : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), p ≠ 0) ∧
    (∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
      ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), M.rep τ g (v : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) ∧
    (∀ X ∈ lieAt V τ, ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), ∃ w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ),
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0) ∧
    ∀ B : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), B ≠ ⊥ →
      (∀ X ∈ lieAt V τ, ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), v ∈ B →
        HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 → w ∈ B) → B = ⊤ := _root_.GlobalTheory.T.structure_of_kFinite_vectors
end GlobalTheory.CuspGKId
noncomputable section
namespace GlobalTheory.CuspGKId
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : Formalism.IndefR.Mult.DSModel V S}
end GlobalTheory.CuspGKId
noncomputable section
namespace GlobalTheory.CuspGKId
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}
theorem cuspForm_local_sum_generates : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
    (V : HSp D) (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ (τ : D.what₂.Tau) (φ : GA D V → ℂ), IsAutFunSm θ V φ → IsTypeAt θ V τ (S τ) φ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ φ ∈ W ∧ ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ h ∈ W, rTr V (atTau θ V τ g) h ∈ W) →
    ∃ (n : ℕ) (T : Fin n → (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] (GA D V → ℂ)))
      (p : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (∀ l, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ (M.ε τ) (M.σ τ) (M.fr τ) (T l)) ∧
      (∀ l v, T l v ∈ GlobalTheory.CuspGKId.locGen θ M τ φ) ∧ φ = ∑ l, T l (p l) := by
  intro hPr D θ V S M hθ τ φ hφ hty hW
  obtain ⟨m, T, p, hT, hsum⟩ := _root_.GlobalTheory.CuspGKId.cuspForm_local_sum_model hPr θ V S M hθ τ φ hφ hty hW
  obtain ⟨-, hKst, hder, hsimp⟩ := _root_.GlobalTheory.CuspGKId.cuspForm_kFinite_structure hPr V S M τ
  let P := GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)
  let kOp : {g // g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧ M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)} → Module.End ℂ P :=
    fun g => LinearMap.codRestrict P ((M.rep τ g.1 : M.H τ →ₗ[ℂ] M.H τ).comp P.subtype) fun v => hKst g.1 g.2.1 g.2.2 v
  have hdu : ∀ X ∈ lieAt V τ, ∀ v w w' : P,
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 →
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w' : M.H τ) 0 → w = w' :=
    fun X _ v w w' h h' => Subtype.ext (h.unique h')
  let dOp : {X // X ∈ lieAt V τ} → Module.End ℂ P := fun X =>
    { toFun := fun v => Classical.choose (hder X.1 X.2 v)
      map_add' := fun a b => by
        refine (hdu X.1 X.2 (a + b) _ _ (Classical.choose_spec (hder X.1 X.2 (a + b))) ?_)
        have h := (Classical.choose_spec (hder X.1 X.2 a)).add (Classical.choose_spec (hder X.1 X.2 b))
        have e : (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X.1)) ((a + b : P) : M.H τ)) =
            fun t => M.rep τ (NormedSpace.exp (t • X.1)) (a : M.H τ) + M.rep τ (NormedSpace.exp (t • X.1)) (b : M.H τ) :=
          funext fun t => by rw [Submodule.coe_add, map_add (f := _)]
        rw [e, Submodule.coe_add]
        exact h
      map_smul' := fun c a => by
        refine (hdu X.1 X.2 (c • a) _ _ (Classical.choose_spec (hder X.1 X.2 (c • a))) ?_)
        have h := (Classical.choose_spec (hder X.1 X.2 a)).const_smul c
        have e : (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X.1)) ((c • a : P) : M.H τ)) =
            fun t => c • M.rep τ (NormedSpace.exp (t • X.1)) (a : M.H τ) :=
          funext fun t => by rw [Submodule.coe_smul, map_smul]
        rw [e, Submodule.coe_smul]
        exact h }
  have hdOp : ∀ X : {X // X ∈ lieAt V τ}, ∀ v : P,
      HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X.1)) (v : M.H τ)) (dOp X v : M.H τ) 0 :=
    fun X v => Classical.choose_spec (hder X.1 X.2 v)
  let a : ({g // g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧ M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)} ⊕
      {X // X ∈ lieAt V τ}) → Module.End ℂ P := fun i => Sum.elim kOp dOp i
  have hsimple : ∀ B : Submodule ℂ P, (∀ i, ∀ v ∈ B, a i v ∈ B) → B ≠ ⊥ → B = ⊤ := fun B hB h0 =>
    hsimp B h0 fun X hX v w hv hd => by
      rw [hdu X hX v w _ hd (hdOp ⟨X, hX⟩ v)]
      exact hB (Sum.inr ⟨X, hX⟩) v hv
  let Ttot : (Fin m → P) →ₗ[ℂ] (GA D V → ℂ) := ∑ j, (T j).comp (LinearMap.proj j)
  have hTtot : ∀ y, Ttot y = ∑ j, T j (y j) := fun y => by
    simp [Ttot, LinearMap.sum_apply]
  have hTK : ∀ (g : {g // g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) ∧ M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ)})
      (y : Fin m → P), Ttot (fun j => kOp g (y j)) = rTr V (atTau θ V τ g.1) (Ttot y) := fun g y => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hTtot, hTtot, show rTr V (atTau θ V τ g.1) (∑ j, T j (y j)) = ∑ j, rTr V (atTau θ V τ g.1) (T j (y j))
      from map_sum (rTrL V (atTau θ V τ g.1)) (fun j => T j (y j)) Finset.univ]
    exact Finset.sum_congr rfl fun j _ => (hT j).mapK g.1 g.2.1 g.2.2 (y j) _ rfl
  have hTL : ∀ (X : {X // X ∈ lieAt V τ}) (y : Fin m → P), Ttot (fun j => dOp X (y j)) = Rder θ V τ X.1 (Ttot y) :=
    fun X y => by
      rw [hTtot, hTtot, Rder_sum X.2 _ fun j => (hT j).aut _]
      exact Finset.sum_congr rfl fun j _ => (hT j).mapLie X.1 X.2 (y j) _ (hdOp X (y j))
  have hloc := isLocSub_locGen θ M τ φ
  let N : Submodule ℂ (Fin m → P) := (locGen θ M τ φ).comap Ttot
  have hN : ∀ i, ∀ y ∈ N, (fun j => a i (y j)) ∈ N := by
    rintro (g | X) y hy
    · show Ttot (fun j => kOp g (y j)) ∈ locGen θ M τ φ
      rw [hTK]
      exact hloc.k g.1 g.2 _ hy
    · show Ttot (fun j => dOp X (y j)) ∈ locGen θ M τ φ
      rw [hTL]
      exact hloc.lie X.1 X.2 _ hy
  have hpN : p ∈ N := by
    show Ttot p ∈ locGen θ M τ φ
    rw [hTtot, ← hsum]
    exact mem_locGen θ M τ φ
  obtain ⟨n, Sm, q, hSa, hSN, hpq⟩ := sub_pow_sum a hsimple m N hN p hpN
  refine ⟨n, fun l => Ttot.comp (Sm l), q, fun l => ⟨fun v => ?_, fun g hg hk v w hw => ?_,
    fun X hX v w hw => ?_⟩, fun l v => hSN l v, ?_⟩
  · rw [LinearMap.comp_apply, hTtot]
    exact isAutFunSm_sum _ fun j => (hT j).aut _
  · have e : w = kOp ⟨g, hg, hk⟩ v := Subtype.ext hw
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    have := hSa l (Sum.inl ⟨g, hg, hk⟩) v
    simp only [a, Sum.elim_inl] at this
    rw [this, hTK]
  · have e : w = dOp ⟨X, hX⟩ v := hdu X hX v w _ hw (hdOp ⟨X, hX⟩ v)
    rw [LinearMap.comp_apply, LinearMap.comp_apply, e]
    have := hSa l (Sum.inr ⟨X, hX⟩) v
    simp only [a, Sum.elim_inr] at this
    rw [this, hTL]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [hsum, ← hTtot p, hpq, map_sum]
      rfl
end GlobalTheory.CuspGKId
noncomputable section
namespace GlobalTheory.CuspGKId
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : Formalism.IndefR.Mult.DSModel V S}
end GlobalTheory.CuspGKId
noncomputable section
namespace GlobalTheory.CuspGKId
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : Formalism.IndefR.Mult.DSModel V S}
end GlobalTheory.CuspGKId
noncomputable section
namespace GlobalTheory.CuspGKId
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : Formalism.IndefR.Mult.DSModel V S}
theorem IsPartMult.partialMultiplicity_decomposition (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hθ : IsInfFam (D := D) θ) {A : Submodule ℂ (GA D V → ℂ)}
    (hA : GlobalTheory.CuspGK.IsGKSub θ M A) (hAf : ∀ f ∈ A, GlobalTheory.CuspGK.IsKFinCuspOfType θ M f) {s : Finset D.what₂.Tau}
    {p0 : Tup M} {lam : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] ℂ} (hp0 : ∀ τ, p0 τ ≠ 0)
    (hsimple : ∀ τ, ∀ B : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), B ≠ ⊥ →
      (∀ X ∈ lieAt V τ, ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), v ∈ B →
        HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 → w ∈ B) → B = ⊤)
    {F : MMK M} (hF : IsPartMult θ M A s p0 lam F) {τ : D.what₂.Tau} (hτ : τ ∉ s) :
    ∃ (n : ℕ) (T : Fin n → (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] MMK M))
      (q : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (∀ m p, IsPartMult θ M A s p0 lam (T m p)) ∧
      (∀ m, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
        ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), (w : M.H τ) = M.rep τ g v →
          ∀ u, T m w u = rTr V (atTau θ V τ g) (T m v u)) ∧
      (∀ m, ∀ X ∈ lieAt V τ, ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ),
        HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 →
          ∀ u, T m w u = Rder θ V τ X (T m v u)) ∧
      F = ∑ m, T m (q m) := by
  have hsm : ∀ f ∈ A, IsAutFunSm θ V f := fun f hf => (hAf f hf).1
  set Hs := partSub θ M A hsm s p0 lam with hHs
  have hinj : ∀ F₁ ∈ Hs, ∀ F₂ ∈ Hs, F₁ p0 = F₂ p0 → F₁ = F₂ := by
    intro F₁ h₁ F₂ h₂ e
    have h3 : F₁ - F₂ ∈ Hs := Hs.sub_mem h₁ h₂
    have := IsPartMult.eq_zero h3 hp0 hsimple (by rw [MultilinearMap.sub_apply, e, sub_self])
    exact sub_eq_zero.1 this
  set E := Hs.map (evAt p0) with hE
  have hEloc : IsLocSub θ M τ E := by
    refine ⟨fun g hg y hy => ?_, fun X hX y hy => ?_⟩
    · obtain ⟨F', hF', rfl⟩ := hy
      exact ⟨_, IsPartMult.rTr_comp hθ hA hF' hτ hg, rfl⟩
    · obtain ⟨F', hF', rfl⟩ := hy
      exact ⟨_, IsPartMult.postRder_comp hθ hA hsm hF' hτ hX, rfl⟩
  have hx : F p0 ∈ A := hF.mem p0
  obtain ⟨hxa, -, hxt, W, hW1, hW2, hW3⟩ := hAf _ hx
  obtain ⟨n, T, p, hT, hTl, hsum⟩ :=
    _root_.GlobalTheory.CuspGKId.cuspForm_local_sum_generates hPr θ V S M hθ τ (F p0) hxa (hxt τ) ⟨W, hW1, hW2, hW3 τ⟩
  have hgen : locGen θ M τ (F p0) ≤ E := locGen_le θ M ⟨F, hF, rfl⟩ hEloc
  let f := (evAt p0).domRestrict Hs
  have hfi : Function.Injective f := fun a b e => Subtype.ext (hinj a a.2 b b.2 e)
  let e := LinearEquiv.ofInjective f hfi
  have hrange : ∀ l v, T l v ∈ LinearMap.range f := fun l v => by
    rw [LinearMap.range_domRestrict]
    exact hgen (hTl l v)
  let T' : Fin n → (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] MMK M) := fun l =>
    Hs.subtype.comp (e.symm.toLinearMap.comp ((T l).codRestrict (LinearMap.range f) (hrange l)))
  have hT'mem : ∀ l v, T' l v ∈ Hs := fun l v => (e.symm _).2
  have hT'ev : ∀ l v, T' l v p0 = T l v := fun l v => by
    have := LinearEquiv.ofInjective_apply (h := hfi) f (e.symm ⟨T l v, hrange l v⟩)
    have h2 : e (e.symm ⟨T l v, hrange l v⟩) = ⟨T l v, hrange l v⟩ := e.apply_symm_apply _
    exact (this.symm.trans (congrArg Subtype.val h2))
  refine ⟨n, T', p, fun m v => hT'mem m v, fun m g hg hk v w hw u => ?_, fun m X hX v w hw u => ?_, ?_⟩
  · have h1 : T' m w = (rTrL V (atTau θ V τ g)).compMultilinearMap (T' m v) :=
      hinj _ (hT'mem m w) _ (IsPartMult.rTr_comp hθ hA (hT'mem m v) hτ ⟨hg, hk⟩) (by
        rw [hT'ev, LinearMap.compMultilinearMap_apply, hT'ev]
        exact (hT m).mapK g hg hk v w hw)
    rw [h1]
    rfl
  · have h1 : T' m w = GlobalTheory.CuspGKId.postRder (θ := θ) τ X hX (T' m v) (fun u => hsm _ ((hT'mem m v).mem u)) :=
      hinj _ (hT'mem m w) _ (IsPartMult.postRder_comp hθ hA hsm (hT'mem m v) hτ hX) (by
        rw [hT'ev]
        show T m w = Rder θ V τ X (T' m v p0)
        rw [hT'ev]
        exact (hT m).mapLie X hX v w hw)
    rw [h1]
    rfl
  · refine hinj _ hF _ (Hs.sum_mem fun m _ => hT'mem m (p m)) ?_
    rw [MultilinearMap.sum_apply]
    simp only [hT'ev]
    exact hsum
end GlobalTheory.CuspGKId
noncomputable section
namespace GlobalTheory.CuspGKId
variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D} {S : D.what₂.Tau → SPar}
  {M : Formalism.IndefR.Mult.DSModel V S}
theorem mem_span_partialMultiplicity (hPr : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hθ : IsInfFam (D := D) θ) {A : Submodule ℂ (GA D V → ℂ)}
    (hA : GlobalTheory.CuspGK.IsGKSub θ M A) (hAf : ∀ f ∈ A, GlobalTheory.CuspGK.IsKFinCuspOfType θ M f)
    {p0 : Tup M} {lam : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] ℂ} (hp0 : ∀ τ, p0 τ ≠ 0)
    (hlam : ∀ τ, lam τ (p0 τ) = 1)
    (hsimple : ∀ τ, ∀ B : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), B ≠ ⊥ →
      (∀ X ∈ lieAt V τ, ∀ v w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ), v ∈ B →
        HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (v : M.H τ)) (w : M.H τ) 0 → w ∈ B) → B = ⊤)
    (s : Finset D.what₂.Tau) :
    A ≤ Submodule.span ℂ {y | ∃ (F : MMK M) (u : Tup M), IsPartMult θ M A s p0 lam F ∧ y = F u} := by
  induction s using Finset.induction_on with
  | empty =>
    intro f hf
    let F : MMK M := (MultilinearMap.mkPiRing ℂ D.what₂.Tau f).compLinearMap lam
    have hFu : ∀ u : Tup M, F u = (∏ τ, lam τ (u τ)) • f := fun u => by
      simp [F, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiRing_apply]
    refine Submodule.subset_span ⟨F, p0, ⟨fun u => by rw [hFu]; exact A.smul_mem _ hf,
      fun τ h => absurd h (Finset.notMem_empty τ), fun τ h => absurd h (Finset.notMem_empty τ),
      fun τ _ u w => ?_⟩, ?_⟩
    · rw [hFu, hFu, smul_smul]
      congr 1
      have h1 : ∀ w' : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ),
          (∏ τ', lam τ' (Function.update u τ w' τ')) = lam τ w' * ∏ τ' ∈ Finset.univ.erase τ, lam τ' (u τ') := by
        intro w'
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ τ), Function.update_self]
        congr 1
        refine Finset.prod_congr rfl fun τ' h' => ?_
        rw [Function.update_of_ne (Finset.ne_of_mem_erase h')]
      rw [h1, h1, hlam, one_mul]
    · rw [hFu, Finset.prod_congr rfl (fun τ _ => hlam τ), Finset.prod_const_one, one_smul]
  | insert τ s hτ ih =>
    refine ih.trans (Submodule.span_le.2 ?_)
    rintro y ⟨F, u, hF, rfl⟩
    obtain ⟨n, T, q, hT, hK, hL, hsum⟩ := _root_.GlobalTheory.CuspGKId.IsPartMult.partialMultiplicity_decomposition hPr hθ hA hAf hp0 hsimple hF hτ
    rw [hsum, MultilinearMap.sum_apply]
    refine Submodule.sum_mem _ fun m _ => ?_
    have h1 : T m (q m) u = lam τ (u τ) • glue τ (T m) (p0 τ) (Function.update u τ (q m)) := by
      rw [glue_apply, Function.update_self, Function.update_idem, ← (hT m (q m)).other τ hτ u (u τ),
        Function.update_eq_self]
    rw [h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, isPartMult_glue hτ (hT m) (hK m) (hL m), rfl⟩)
end GlobalTheory.CuspGKId
noncomputable section
namespace GlobalTheory.CuspGKId
theorem le_multiplicitySpan_cuspForm : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ A : Submodule ℂ (GA D V → ℂ), GlobalTheory.CuspGK.IsIrrGKSub θ M A → (∀ f ∈ A, GlobalTheory.CuspGK.IsKFinCuspOfType θ M f) →
    A ≤ GlobalTheory.CuspGK.multSpan θ M := by
  intro hPr D θ V S M hθ A hA hAf
  have hA1 := hA.1
  have hst := fun τ => _root_.GlobalTheory.CuspGKId.cuspForm_kFinite_structure hPr V S M τ
  choose p0 hp0 using fun τ => (hst τ).1
  have hl : ∀ τ, ∃ l : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ) →ₗ[ℂ] ℂ, l (p0 τ) = 1 := by
    intro τ
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)), φ (p0 τ) ≠ 0 := by
      by_contra h
      push_neg at h
      exact hp0 τ ((Module.forall_dual_apply_eq_zero_iff ℂ (p0 τ)).1 h)
    exact ⟨(φ (p0 τ))⁻¹ • φ, by simp [hφ]⟩
  choose lam hlam using hl
  have hsimple := fun τ => (hst τ).2.2.2
  refine (_root_.GlobalTheory.CuspGKId.mem_span_partialMultiplicity hPr hθ hA1 hAf (p0 := p0) (lam := lam) hp0 hlam hsimple Finset.univ).trans ?_
  refine Submodule.span_mono ?_
  rintro y ⟨F, u, hF, rfl⟩
  refine ⟨F, u, ⟨fun v => (hAf _ (hF.mem v)).1, fun v => (hAf _ (hF.mem v)).2.1,
    fun τ => hF.equivK τ (Finset.mem_univ τ), fun τ => hF.equivLie τ (Finset.mem_univ τ)⟩, rfl⟩
end GlobalTheory.CuspGKId
end
end
end
end
end
end
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_gK_isotypic_decomposition : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ A : Submodule ℂ (GA D V → ℂ), GlobalTheory.CuspGK.IsIrrGKSub θ M A → (∀ f ∈ A, GlobalTheory.CuspGK.IsKFinCuspOfType θ M f) →
    A ≤ GlobalTheory.CuspGK.multSpan θ M := by
  first | exact @_root_.GlobalTheory.CuspGKId.le_multiplicitySpan_cuspForm | exact _root_.GlobalTheory.CuspGKId.le_multiplicitySpan_cuspForm | (intros; apply _root_.GlobalTheory.CuspGKId.le_multiplicitySpan_cuspForm <;> assumption)
end
end

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
namespace GlobalTheory.CuspGK
theorem exists_finite_sum_gelfandKirillov_multiplicity : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ → (∀ τ, IsTypeAt θ V τ (S τ) ψ) →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ∃ (n : ℕ) (F : Fin n → MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (GA D V → ℂ))
      (u : Fin n → ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (∀ l, (∀ u, IsAutFunSm θ V (F l u)) ∧ (∀ u, IsCuspFun V (F l u)) ∧
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
        ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          (w : M.H τ) = M.rep τ g (u τ) → F l (Function.update u τ w) = rTr V (atTau θ V τ g) (F l u)) ∧
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (u τ : M.H τ)) (w : M.H τ) 0 →
          F l (Function.update u τ w) = Rder θ V τ X (F l u))) ∧ ∀ g, ψ g = ∑ l, F l (u l) g := by
  have I1 := _root_.GlobalTheory.T.cuspForms_eq_iSup_irreducible_gK
  have I2 := _root_.GlobalTheory.T.cuspForm_gK_submodule_of_type
  have I3 := _root_.GlobalTheory.T.cuspForm_gK_isotypic_decomposition
  intro hP D θ V S M hθ ψ hA hC hT hW
  have hψ : IsKFinCuspOfType θ M ψ := ⟨hA, hC, hT, hW⟩
  have h1 := I1 hP θ V S M hθ ψ hA hC hW
  have hle : (⨆ (A : Submodule ℂ (GA D V → ℂ)) (_ : A ≤ gkGen θ M ψ ∧ IsIrrGKSub θ M A), A) ≤ multSpan θ M :=
    iSup_le fun A => iSup_le fun hA' =>
      I3 hP θ V S M hθ A hA'.2 fun f hf => I2 hP θ V S M hθ ψ hψ f (hA'.1 hf)
  obtain ⟨n, F, u, hF, hsum⟩ := exists_sum_of_mem_multSpan θ M (hle h1)
  exact ⟨n, F, u, fun l => ⟨(hF l).aut, (hF l).cusp, (hF l).equivK, (hF l).equivLie⟩, hsum⟩
end GlobalTheory.CuspGK
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_gelfandKirillov_finite_decomposition : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ → (∀ τ, IsTypeAt θ V τ (S τ) ψ) →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ∃ (n : ℕ) (F : Fin n → MultilinearMap (RingHom.id ℂ) (fun τ : D.what₂.Tau => GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (GA D V → ℂ))
      (u : Fin n → ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
      (∀ l, (∀ u, IsAutFunSm θ V (F l u)) ∧ (∀ u, IsCuspFun V (F l u)) ∧
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) →
        ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          (w : M.H τ) = M.rep τ g (u τ) → F l (Function.update u τ w) = rTr V (atTau θ V τ g) (F l u)) ∧
      (∀ τ, ∀ X ∈ lieAt V τ, ∀ (u : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)) (w : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin (M.ε τ) (M.σ τ)),
          HasDerivAt (fun t : ℝ => M.rep τ (NormedSpace.exp (t • X)) (u τ : M.H τ)) (w : M.H τ) 0 →
          F l (Function.update u τ w) = Rder θ V τ X (F l u))) ∧ ∀ g, ψ g = ∑ l, F l (u l) g := by
  first | exact @_root_.GlobalTheory.CuspGK.exists_finite_sum_gelfandKirillov_multiplicity | exact _root_.GlobalTheory.CuspGK.exists_finite_sum_gelfandKirillov_multiplicity | (intros; apply _root_.GlobalTheory.CuspGK.exists_finite_sum_gelfandKirillov_multiplicity <;> assumption)
end
