module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KerPolarizationProjectionStableUnderStabilizerLi

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.LieActionMemKerPolarizationProjection
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeilCoinvariantsVanishOnLineDerivatives
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.CoinvLine
variable {D : D7}
theorem coinvariants_kill_line_derivative : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ωA : WRep W X) (ωB : WRep W₁ X) (Pi : ModuleCat.{0} ℂ)
    (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO W X → ℂ) →ₗ[ℂ] Pi) (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → IsTriple W W₁ X α β → IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W₁.rank) (hJ : Vs.J = (-1 : D.host.E) • W₁.gram),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Vs, ∀ Ψ ∈ algF ψ θ false A₁ B, ∀ Ψ₁ ∈ algF ψ θ false A₁ B,
    (∀ z, HasDerivAt (fun t : ℝ => ωB (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) (neg_ne_zero.2 one_ne_zero) hJ
      (γ (Multiplicative.ofAdd t)), 1) Ψ z) (Ψ₁ z) 0) → p' Ψ₁ = 0 := by
  intro _ D ψ θ W W₁ X A A₁ B α β ωA ωB Pi rf rl p p' hθ _ _ hM Vs hJ γ hγ Ψ hΨ Ψ₁ _ hder
  have hω : IsWeilDatumO ψ W₁ X α (α / β) ωB := hM.weilB
  have hψ : IsStdChar D ψ (-1) := hω.std
  have hc : (-1 : D.host.E) ≠ 0 := neg_ne_zero.2 one_ne_zero
  obtain ⟨g, h1, h2, h3, h4⟩ := GlobalTheory.OmegaDer.exists_line W₁ hc Vs hJ γ hγ
  have hg : ∀ t : ℝ, GlobalTheory.ConjUTransport.conjUInv W₁ (-1) (neg_ne_zero.2 one_ne_zero) hJ (γ (Multiplicative.ofAdd t)) = g t :=
    fun t => by rw [← h1 t]; exact (GlobalTheory.ConjUTransport.conjEquiv W₁ (-1) hc hJ).left_inv (g t)
  obtain ⟨Z, hZ⟩ := GlobalTheory.OmegaDer.exists_expInf hθ W₁ g h2 h3 h4
  have hst := fun τ => hM.mapB.stabM.2 τ (Z τ).1 (Z τ).2 Ψ hΨ
  choose Ψ' hΨ' hd using hst
  have hk : ∀ τ, p' (Ψ' τ) = 0 := fun τ => hM.mapB.invl τ (Z τ).1 (Z τ).2 Ψ hΨ (Ψ' τ) (hΨ' τ) (hd τ)
  have hsum : Ψ₁ = ∑ τ, Ψ' τ := by
    funext z
    rw [Finset.sum_apply]
    have e1 : (fun t : ℝ => ωB (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) (neg_ne_zero.2 one_ne_zero) hJ
        (γ (Multiplicative.ofAdd t)), 1) Ψ z) = fun t : ℝ => ωB (GlobalTheory.SmoothForms.expInf θ W₁ (t • Z), 1) Ψ z := by
      funext t; rw [hg t, hZ t]
    have hz := hder z
    rw [e1] at hz
    rcases isEmpty_or_nonempty D.what₂.Tau with h0 | h0
    · have e : ∀ t : ℝ, t • Z = Z := fun t => funext fun τ => isEmptyElim τ
      simp only [e] at hz
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      exact hz.unique (hasDerivAt_const _ _)
    · let 𝒮 : Set (GA D W₁ → ℂ) := {φ | ∃ f z, IsThetaFunO ψ W₁ X f ∧ φ = fun g => ωB (g, 1) f z}
      have hΘ := isThetaFunO_of_mem_algF hθ hψ A₁ B hΨ
      refine hz.unique (GlobalTheory.OmegaDer.der_sum hθ 𝒮 ?_ ?_ ⟨Ψ, z, hΘ, rfl⟩ Z (fun τ => Ψ' τ z) fun τ => hd τ z)
      · rintro _ ⟨f, z, hf, rfl⟩
        exact (hω.om_cont f hf z).comp (continuous_id.prodMk continuous_const)
      · rintro _ ⟨f, z, hf, rfl⟩ τ' Y hY
        obtain ⟨G, hG', h⟩ := GlobalTheory.LieScalar.genS hθ hω τ' Y hY f hf
        refine ⟨_, ⟨G, z, hG', rfl⟩, fun g => ?_⟩
        have := h (g, 1) z
        simpa only [MonoidHom.inl_apply, Prod.mk_mul_mk, mul_one] using this
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum]
  exact Finset.sum_eq_zero fun τ _ => hk τ
end GlobalTheory.CoinvLine
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_coinvariants_vanish_on_line_derivatives : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ωA : WRep W X) (ωB : WRep W₁ X) (Pi : ModuleCat.{0} ℂ)
    (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO W X → ℂ) →ₗ[ℂ] Pi) (p' : (WO W₁ X → ℂ) →ₗ[ℂ] Pi),
    IsInfFam θ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → IsTriple W W₁ X α β → IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ (Vs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W₁.rank) (hJ : Vs.J = (-1 : D.host.E) • W₁.gram),
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Vs, ∀ Ψ ∈ algF ψ θ false A₁ B, ∀ Ψ₁ ∈ algF ψ θ false A₁ B,
    (∀ z, HasDerivAt (fun t : ℝ => ωB (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) (neg_ne_zero.2 one_ne_zero) hJ
      (γ (Multiplicative.ofAdd t)), 1) Ψ z) (Ψ₁ z) 0) → p' Ψ₁ = 0 := by
  first | exact @_root_.GlobalTheory.CoinvLine.coinvariants_kill_line_derivative | exact _root_.GlobalTheory.CoinvLine.coinvariants_kill_line_derivative | (intros; apply _root_.GlobalTheory.CoinvLine.coinvariants_kill_line_derivative <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.KerLie
theorem lie_action_mem_ker_polarizationProjection : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.V', ∀ f ∈ Γ.M'.Pol Bs.ψ Bs.emb, ∀ f₁ ∈ Γ.M'.Pol Bs.ψ Bs.emb, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om' (γ (Multiplicative.ofAdd t), 1)) f f₁ → ∀ φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), ((Fin W₁.rank × Fin (W.rank + W₁.rank)) → Fv D.host.F w) → ℂ, (∀ w, φ w ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ w in Filter.cofinite, φ w = Γ.M'.vac w) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT Pi rf rl p p' hm γ hγ f hf f₁ hf₁
    hact φ hφ hv
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hT.base.std
  have hM : Γ.M'.IsGood ψ := hO.psi ▸ hT.geo.hM'
  have hW : Γ.M'.IsWeil ψ Xc.α (Xc.α / Xc.β) om' := hO.psi ▸ hT.weil'
  have hc : (-1 : D.host.E) ≠ 0 := neg_ne_zero.2 one_ne_zero
  have hD0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ algD Γ.M' Bs.ψ Bs.emb := Submodule.subset_span ⟨f, φ, hf, hφ, hv, rfl⟩
  have hD1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ ∈ algD Γ.M' Bs.ψ Bs.emb := Submodule.subset_span ⟨f₁, φ, hf₁, hφ, hv, rfl⟩
  obtain ⟨Ψ, hΨ, hΨD⟩ := hO.algB' _ hD0
  obtain ⟨Ψ₁, hΨ₁, hΨ₁D⟩ := hO.algB' _ hD1
  rw [mem_kerPD hstd]
  refine ⟨hD1, Ψ₁, hΨ₁, hΨ₁D, ?_⟩
  have hstd' : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers D.host.F v} 1 :=
    (hv.and hM.std).mono fun v h => h.1.trans h.2
  have hrest := GlobalTheory.ThK.EvUniqInf.rest_pure f φ hφ hstd'
  have hder : ∀ z, HasDerivAt (fun t : ℝ => ωB (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc hO.JW₁
      (γ (Multiplicative.ofAdd t)), 1) Ψ z) (Ψ₁ z) 0 := by
    intro z
    obtain ⟨u, rfl⟩ := cB.surjective z
    have h1 := _root_.GlobalTheory.T.thetaSum_differentiable_along_line hP Γ.M' ψ Xc.α (Xc.α / Xc.β) om' hstd hM hW γ hγ f f₁ _ hrest hact u
    have hval : ∀ t : ℝ, GlobalTheory.WeilM.thetaSum D.host.F (Γ.M'.co.rho ψ u (om' (γ (Multiplicative.ofAdd t), 1)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (⇑f) (fun x => ∏ᶠ v, φ v fun i => GlobalTheory.AdelicU.evFin D.host.F v (x i))))) =
        ωB (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc hO.JW₁ (γ (Multiplicative.ofAdd t)), 1) Ψ (cB u) := by
      intro t
      have h := (hO.weilB _ Ψ hΨD (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc hO.JW₁ (γ (Multiplicative.ofAdd t))) 1).2 u
      rw [GlobalTheory.KapXLine.kapX_one] at h
      have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc hO.JW₁ (γ (Multiplicative.ofAdd t))) =
          γ (Multiplicative.ofAdd t) := (GlobalTheory.ConjUTransport.conjEquiv W₁ (-1) hc hO.JW₁).apply_symm_apply _
      rw [e1] at h
      exact h
    have h2 := hΨ₁D.2 u
    have e3 : (fun t : ℝ => ωB (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc hO.JW₁ (γ (Multiplicative.ofAdd t)), 1) Ψ (cB u)) =
        fun t : ℝ => GlobalTheory.WeilM.thetaSum D.host.F (Γ.M'.co.rho ψ u (om' (γ (Multiplicative.ofAdd t), 1)
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (⇑f) (fun x => ∏ᶠ v, φ v fun i => GlobalTheory.AdelicU.evFin D.host.F v (x i))))) :=
      funext fun t => (hval t).symm
    rw [e3, ← h2]
    exact h1
  exact _root_.GlobalTheory.T.weil_coinvariants_vanish_on_line_derivatives hP D ψ θ W W₁ X A A₁ B α β ωA ωB Pi rf rl p p' hθ hstd hTr hm Γ.V' hO.JW₁ γ hγ Ψ hΨ Ψ₁ hΨ₁ hder
end GlobalTheory.SquareAgree.KerLie
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_polarizationProjection_lie_stable : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.V', ∀ f ∈ Γ.M'.Pol Bs.ψ Bs.emb, ∀ f₁ ∈ Γ.M'.Pol Bs.ψ Bs.emb, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (fun t => om' (γ (Multiplicative.ofAdd t), 1)) f f₁ → ∀ φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), ((Fin W₁.rank × Fin (W.rank + W₁.rank)) → Fv D.host.F w) → ℂ, (∀ w, φ w ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ w in Filter.cofinite, φ w = Γ.M'.vac w) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  first | exact @_root_.GlobalTheory.SquareAgree.KerLie.lie_action_mem_ker_polarizationProjection | exact _root_.GlobalTheory.SquareAgree.KerLie.lie_action_mem_ker_polarizationProjection | (intros; apply _root_.GlobalTheory.SquareAgree.KerLie.lie_action_mem_ker_polarizationProjection <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KerPolarizationProjectionStableUnderStabilizerCo
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.StabilizerOfKExponentialLine
section
open NumberField IsDedekindDomain
noncomputable section
namespace GlobalTheory.KExpLineW
section Abstract
variable {α : Type}
end Abstract
end GlobalTheory.KExpLineW
namespace GlobalTheory.KExpLineW
section Orbit
variable {α : Type}
end Orbit
end GlobalTheory.KExpLineW
namespace GlobalTheory.KExpLineW
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
end GlobalTheory.KExpLineW
namespace GlobalTheory.KExpLineW
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
theorem KExpLine_stabilizes_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W, (∀ t, γ t ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb) →
    ∀ N : Submodule ℂ (GlobalTheory.ThK.Fn F n d),
      (∀ Ψ ∈ N, ∀ Ψ₁ ∈ GlobalTheory.ThK.PolData B M,
        (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Ψ x) (Ψ₁ x) 0) → Ψ₁ ∈ N) →
      ∀ Φ ∈ N, Φ ∈ GlobalTheory.ThK.PolData B M → om (1, γ (Multiplicative.ofAdd (1 : ℝ))) Φ ∈ N := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP γ hγL hγK N hN Φ hΦN hΦ
  obtain ⟨-, -, hDer, hOp⟩ := _root_.GlobalTheory.T.dualPair_preserves_polarization hPr F E σ B n d X W M χX χW om r s r' s' hP
  obtain ⟨Dg, hDgP, hDg⟩ := hDer γ hγL
  choose D hDP hD using fun t : ℝ => hOp (γ (Multiplicative.ofAdd t)) (hγK _)
  let U : Multiplicative ℝ →* Module.End ℂ (Fn F n d) := om.comp ((MonoidHom.inr (UA σ X.J) (UA σ W.J)).comp γ)
  have hdiff : ∀ Ψ ∈ PolData B M, ∀ x (t : ℝ),
      DifferentiableAt ℝ (fun s : ℝ => U (Multiplicative.ofAdd s) Ψ x) t := by
    intro Ψ hΨ x
    induction hΨ using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, φ, hφ, hvac, rfl⟩ := hy
      intro t
      have hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
        (hvac.and hP.good.std).mono fun _ h => h.1.trans h.2
      have hpt : ∀ u : ℝ, U (Multiplicative.ofAdd u) (pure f φ) = pure (D u f) φ := fun u =>
        map_pure M B.ψ hP.good _ f (D u f) ((hD u f hf (D u f)).2 rfl) φ hφ hvac
      have hshift : ∀ s', U (Multiplicative.ofAdd (s' + t)) (pure f φ) =
          U (Multiplicative.ofAdd s') (pure (D t f) φ) := by
        intro s'
        rw [ofAdd_add, map_mul, Module.End.mul_apply, hpt t]
      have h0 := (hDg (D t f) (hDP t f hf) (Dg (D t f))).2 rfl _
        (GlobalTheory.ThK.EvUniqInf.rest_pure (D t f) φ hφ hstd) x
      have h0' : DifferentiableAt ℝ (fun s' : ℝ => U (Multiplicative.ofAdd s') (pure (D t f) φ) x) 0 :=
        h0.differentiableAt
      have e : (fun s : ℝ => U (Multiplicative.ofAdd s) (pure f φ) x) =
          (fun s' : ℝ => U (Multiplicative.ofAdd s') (pure (D t f) φ) x) ∘ fun s => s - t := by
        funext s
        show _ = U (Multiplicative.ofAdd (s - t)) (pure (D t f) φ) x
        rw [← hshift, sub_add_cancel]
      have h4 : DifferentiableAt ℝ (fun s' : ℝ => U (Multiplicative.ofAdd s') (pure (D t f) φ) x)
          ((fun s : ℝ => s - t) t) := by
        simp only [sub_self]
        exact h0'
      rw [e]
      exact DifferentiableAt.comp (f := fun s : ℝ => s - t) t h4 (differentiableAt_id.sub_const t)
    | zero =>
      intro t
      simp only [map_zero, Pi.zero_apply]
      exact differentiableAt_const _
    | add y z _ _ hy hz =>
      intro t
      simp only [map_add (f := _), Pi.add_apply]
      exact (hy t).add (hz t)
    | smul a y _ hy =>
      intro t
      simp only [map_smul, Pi.smul_apply, smul_eq_mul]
      exact (hy t).const_mul a
  obtain ⟨C, hCfin, hCP, hCk⟩ := polData_kfin F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  haveI := hCfin
  exact orbit_mem U (PolData B M) N C hCP (fun Ψ h Ψ₁ h₁ hd => hN Ψ h Ψ₁ h₁ hd) Φ hΦN
    (fun t => hCk _ (hγK _)) (hdiff Φ hΦ) 1
end GlobalTheory.KExpLineW
end
end

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilizer_of_K_exponential_line : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ W, (∀ t, γ t ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ W B.emb) →
    ∀ N : Submodule ℂ (GlobalTheory.ThK.Fn F n d),
      (∀ Ψ ∈ N, ∀ Ψ₁ ∈ GlobalTheory.ThK.PolData B M,
        (∀ x, HasDerivAt (fun t : ℝ => om (1, γ (Multiplicative.ofAdd t)) Ψ x) (Ψ₁ x) 0) → Ψ₁ ∈ N) →
      ∀ Φ ∈ N, Φ ∈ GlobalTheory.ThK.PolData B M → om (1, γ (Multiplicative.ofAdd (1 : ℝ))) Φ ∈ N := by
  first | exact @_root_.GlobalTheory.KExpLineW.KExpLine_stabilizes_line | exact _root_.GlobalTheory.KExpLineW.KExpLine_stabilizes_line | (intros; apply _root_.GlobalTheory.KExpLineW.KExpLine_stabilizes_line <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.KerStabCpt
theorem stabilizer_compact_mem_ker_polarizationProjection : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.W Bs.emb, ∀ Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p', om' (1, k) Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  intro hPr D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT Pi rf rl p p' hM k hk Φ hΦ
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hT.base.std
  obtain ⟨γ, hγ, h1, hK⟩ := GlobalTheory.T.exists_one_parameter_subgroup_maxCompact_skewHermitian D.host.F D.host.E D.sp.cm.sig Bs _ Γ.W _ _ hT.base hT.geo.hW k hk
  rw [← h1]
  have hAlg : Φ ∈ GlobalTheory.ThK.PolData Bs Γ.M' := by
    rw [← algD_eq_polData]
    exact ((mem_kerPD hstd θ A₁ B Bs Γ cB p' Φ).1 hΦ).1
  refine _root_.GlobalTheory.T.stabilizer_of_K_exponential_line hPr D.host.F D.host.E D.sp.cm.sig Bs _ _ Γ.V' Γ.W Γ.M' _ _ om' _ _ _ _ (isPair_small' hT) γ hγ hK
    (kerPD ψ θ A₁ B Bs Γ cB p') (fun Ψ hΨ Ψ₁ hΨ₁ hd => ?_) Φ hΦ hAlg
  rw [← algD_eq_polData] at hΨ₁
  exact _root_.GlobalTheory.T.ker_polarizationProjection_stable_under_stabilizer_lie hPr D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT Pi rf rl p p' hM
    γ hγ Ψ hΨ Ψ₁ hΨ₁ hd
end GlobalTheory.SquareAgree.KerStabCpt
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_polarizationProjection_stable_under_stabilizer_compact : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.W Bs.emb, ∀ Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p', om' (1, k) Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  first | exact @_root_.GlobalTheory.SquareAgree.KerStabCpt.stabilizer_compact_mem_ker_polarizationProjection | exact _root_.GlobalTheory.SquareAgree.KerStabCpt.stabilizer_compact_mem_ker_polarizationProjection | (intros; apply _root_.GlobalTheory.SquareAgree.KerStabCpt.stabilizer_compact_mem_ker_polarizationProjection <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CompactActionMemKerPolarizationProjection
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KInftyExponentialLineInDerivativeSpan
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FockVectorsKFinite
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.IsGaussianOfFockVacuumStabilizerActs
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
namespace GlobalTheory.FockVacStab
theorem isGaussian_of_fock_vacuum_stabilizer_acts : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ X B.emb, ∀ f₀ : SInf F (Fin n × Fin d),
    M.IsGauss B.ψ B.emb f₀ → ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (k, 1)) f₀ f₁ → M.IsGauss B.ψ B.emb f₁ := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k hk f₀ hG f₁ hact
  have hPA := _root_.GlobalTheory.T.dualPair_preserves_polarization hPr F E σ B n d X W M χX χW om r s r' s' hP
  obtain ⟨m, L, hD⟩ := GlobalTheory.T.heisenbergLine_derivative_finite_span F E σ n d X W M B.ψ hP.base.std
  choose! Dfun hDiff _ using hD
  obtain ⟨Dk, _, hDk⟩ := hPA.2.1 k hk
  have hGP : ∀ g, M.IsGauss B.ψ B.emb g → g ∈ M.Pol B.ψ B.emb := fun g h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 g h
  have hclos : ∀ u, At (evI F) u → ∀ g ∈ M.Pol B.ψ B.emb, Dfun u g ∈ M.Pol B.ψ B.emb := fun u hu g hg =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu g (Submodule.mem_sInf.1 hg N hN) _ ((hDiff u hu g _).2 rfl)
  have hAt : ∀ (a : Matrix (Fin n) (Fin n) (AE F E)) (u : Matrix (Fin n) (Fin d) (AE F E)), At (evI F) u →
      At (evI F) (a * u) := fun a u hu c hc => by rw [← Matrix.mul_smul, hu c hc, Matrix.mul_zero]
  obtain ⟨hkk, hkk'⟩ := mat_mul_mat_inv k
  have hcomm : ∀ w, (mat k⁻¹).map (piInf (B.emb w)) * X.θ w = X.θ w * (mat k⁻¹).map (piInf (B.emb w)) := by
    intro w
    set A := (mat k).map (piInf (B.emb w))
    set A' := (mat k⁻¹).map (piInf (B.emb w))
    have h1 : A * A' = 1 := by
      rw [← Matrix.map_mul, hkk]; exact Matrix.map_one _ (map_zero _) (map_one _)
    have h2 : A' * A = 1 := by
      rw [← Matrix.map_mul, hkk']; exact Matrix.map_one _ (map_zero _) (map_one _)
    have hc : A * X.θ w = X.θ w * A := hk.2 w
    calc A' * X.θ w = A' * X.θ w * (A * A') := by rw [h1, Matrix.mul_one]
      _ = A' * (X.θ w * A) * A' := by simp only [Matrix.mul_assoc]
      _ = A' * (A * X.θ w) * A' := by rw [hc]
      _ = (A' * A) * X.θ w * A' := by simp only [Matrix.mul_assoc]
      _ = X.θ w * A' := by rw [h2, Matrix.one_mul]
  obtain ⟨ε, hε⟩ := hG
  refine ⟨ε, fun u u' hu hu' huu' f f' hf hf' => ?_⟩
  set v := mat k⁻¹ * u
  set v' := mat k⁻¹ * u'
  have hv : At (evI F) v := hAt _ u hu
  have hv' : At (evI F) v' := hAt _ u' hu'
  have hvv' : ∀ w, v'.map (piInf (B.emb w)) =
      (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * v.map (piInf (B.emb w)) * (W.θ w)ᵀ) := by
    intro w
    simp only [v, v', Matrix.map_mul, huu' w, Matrix.mul_smul, ← Matrix.mul_assoc, hcomm w]
  have hkv : mat k * v = u := by simp only [v, ← Matrix.mul_assoc, hkk, Matrix.one_mul]
  have hkv' : mat k * v' = u' := by simp only [v', ← Matrix.mul_assoc, hkk, Matrix.one_mul]
  have hgg : Dfun v' f₀ = Complex.I • Dfun v f₀ :=
    hε v v' hv hv' hvv' _ _ ((hDiff v hv f₀ _).2 rfl) ((hDiff v' hv' f₀ _).2 rfl)
  have hf0 : f₀ ∈ M.Pol B.ψ B.emb := hGP f₀ ⟨ε, hε⟩
  have hmove : ∀ x, At (evI F) x → ActsD (evI F) (M.heisLine B.ψ (mat k * x)) f₁ (Dk (Dfun x f₀)) := by
    intro x hx
    exact GlobalTheory.T.compactUnitary_moves_heisenbergDerivative F E σ B n d X W M χX χW om r s r' s' hP k hk x hx f₀ (Dfun x f₀) f₁ (Dk (Dfun x f₀))
      ((hDiff x hx f₀ _).2 rfl) hact ((hDk _ (hclos x hx f₀ hf0) _).2 rfl)
  have e1 : f = Dk (Dfun v f₀) := by
    have a := (hDiff u hu f₁ f).1 hf
    have b := (hDiff u hu f₁ _).1 (hkv ▸ hmove v hv)
    rw [a, b]
  have e2 : f' = Dk (Dfun v' f₀) := by
    have a := (hDiff u' hu' f₁ f').1 hf'
    have b := (hDiff u' hu' f₁ _).1 (hkv' ▸ hmove v' hv')
    rw [a, b]
  rw [e2, e1, hgg, map_smul]
end GlobalTheory.FockVacStab
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_vacuum_stabilized_is_gaussian : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' → ∀ k ∈ KInf σ X B.emb, ∀ f₀ : SInf F (Fin n × Fin d),
    M.IsGauss B.ψ B.emb f₀ → ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (k, 1)) f₀ f₁ → M.IsGauss B.ψ B.emb f₁ := by
  first | exact @_root_.GlobalTheory.FockVacStab.isGaussian_of_fock_vacuum_stabilizer_acts | exact _root_.GlobalTheory.FockVacStab.isGaussian_of_fock_vacuum_stabilizer_acts | (intros; apply _root_.GlobalTheory.FockVacStab.isGaussian_of_fock_vacuum_stabilizer_acts <;> assumption)
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.FockKFin
theorem fock_space_kFinite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n)
    (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ f ∈ M.Pol B.ψ B.emb, ∃ S : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), FiniteDimensional ℂ S ∧
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) f f₁ → f₁ ∈ S := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP f hf
  have hPA := _root_.GlobalTheory.T.dualPair_preserves_polarization hPr F E σ B n d X W M χX χW om r s r' s' hP
  obtain ⟨m, L, hD⟩ := GlobalTheory.T.heisenbergLine_derivative_finite_span F E σ n d X W M B.ψ hP.base.std
  choose! Dfun hDiff hDspan using hD
  have hK := hPA.2.1
  simp only [GlobalTheory.RealActs.OpOn] at hK
  choose! Tk hTpres hTacts using hK
  have hGP : ∀ f₀, M.IsGauss B.ψ B.emb f₀ → f₀ ∈ M.Pol B.ψ B.emb := fun f₀ h =>
    Submodule.mem_sInf.2 fun N hN => hN.1 f₀ h
  have hclos : ∀ u, At (evI F) u → ∀ g ∈ M.Pol B.ψ B.emb, Dfun u g ∈ M.Pol B.ψ B.emb := fun u hu g hg =>
    Submodule.mem_sInf.2 fun N hN => hN.2 u hu g (Submodule.mem_sInf.1 hg N hN) _ ((hDiff u hu g _).2 rfl)
  have hmin : ∀ N : Submodule ℂ (SInf F (Fin n × Fin d)), {f₀ | M.IsGauss B.ψ B.emb f₀} ⊆ N →
      (∀ u ∈ {u : Matrix (Fin n) (Fin d) (AE F E) | At (evI F) u}, ∀ g ∈ N, Dfun u g ∈ N) → M.Pol B.ψ B.emb ≤ N := by
    intro N hG hN
    refine sInf_le ⟨fun f₀ h => hG h, fun u hu g hg g₁ hg₁ => ?_⟩
    rw [(hDiff u hu g g₁).1 hg₁]
    exact hN u hu g hg
  have hAt : ∀ k : UA σ X.J, ∀ u : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u → At (evI F) (mat k * u) :=
    fun k u hu c hc => by rw [← Matrix.mul_smul, hu c hc, Matrix.mul_zero]
  obtain ⟨S, hS, hSk⟩ := GlobalTheory.T.exists_finiteDimensional_orbit_of_boundedRank_generated (SInf F (Fin n × Fin d)) (Matrix (Fin n) (Fin d) (AE F E))
    {k // k ∈ KInf σ X B.emb} {u | At (evI F) u} {f₀ | M.IsGauss B.ψ B.emb f₀} (M.Pol B.ψ B.emb) Dfun m L
    (fun k => Tk k.1) (fun k u => mat k.1 * u) (GlobalTheory.T.fockVacua_span_finiteDimensional F E σ B n d X W M χX χW om r s r' s' hP)
    (fun u hu g => hDspan u hu g) (fun f₀ h => hGP f₀ h) (fun u hu g hg => hclos u hu g hg) hmin
    (fun k g hg => Submodule.subset_span
      (_root_.GlobalTheory.T.fock_vacuum_stabilized_is_gaussian hPr F E σ B n d X W M χX χW om r s r' s' hP k.1 k.2 g hg _
        ((hTacts k.1 k.2 g (hGP g hg) _).2 rfl)))
    (fun k u hu => hAt k.1 u hu)
    (fun k u hu g hg => (hDiff _ (hAt k.1 u hu) _ _).1
      (GlobalTheory.T.compactUnitary_moves_heisenbergDerivative F E σ B n d X W M χX χW om r s r' s' hP k.1 k.2 u hu g (Dfun u g) (Tk k.1 g)
        (Tk k.1 (Dfun u g)) ((hDiff u hu g _).2 rfl) ((hTacts k.1 k.2 g hg _).2 rfl)
        ((hTacts k.1 k.2 _ (hclos u hu g hg) _).2 rfl)))
    f hf
  exact ⟨S, hS, fun k hk f₁ hact => by rw [(hTacts k hk f hf f₁).1 hact]; exact hSk ⟨k, hk⟩⟩
end GlobalTheory.FockKFin
end

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_vectors_kFinite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n)
    (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ f ∈ M.Pol B.ψ B.emb, ∃ S : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)), FiniteDimensional ℂ S ∧
      ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) f f₁ → f₁ ∈ S := by
  first | exact @_root_.GlobalTheory.FockKFin.fock_space_kFinite | exact _root_.GlobalTheory.FockKFin.fock_space_kFinite | (intros; apply _root_.GlobalTheory.FockKFin.fock_space_kFinite <;> assumption)
end
end

section
open NumberField IsDedekindDomain
noncomputable section
namespace GlobalTheory.KExpLine
section Abstract
variable {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
end Abstract
end GlobalTheory.KExpLine
namespace GlobalTheory.KExpLine
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
theorem sub_mem_span_kInfty_exp_derivatives : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) f f₁ →
      f₁ - f ∈ Submodule.span ℂ {g₁ | g₁ ∈ M.Pol B.ψ B.emb ∧ ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, ∃ g ∈ M.Pol B.ψ B.emb,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) g g₁} := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP k hk f hf f₁ hact
  obtain ⟨hDer, hOp, -, -⟩ := _root_.GlobalTheory.T.dualPair_preserves_polarization hPr F E σ B n d X W M χX χW om r s r' s' hP
  obtain ⟨γ, hγL, hγ1, hγK⟩ := GlobalTheory.T.exists_oneParameter_in_unitaryArchimedeanMaxCompact F E σ B n X r s hP.base hP.herm k hk
  obtain ⟨S, hSfin, hS⟩ := _root_.GlobalTheory.T.fock_vectors_kFinite hPr F E σ B n d X W M χX χW om r s r' s' hP f hf
  haveI := hSfin
  obtain ⟨Dg, hDgP, hDg⟩ := hDer γ hγL
  choose D hDP hD using fun t : ℝ => hOp (γ (Multiplicative.ofAdd t)) (hγK _)
  let c : ℝ → SInf F (Fin n × Fin d) := fun t => D t f
  have hcP : ∀ t, c t ∈ M.Pol B.ψ B.emb := fun t => hDP t f hf
  have hcA : ∀ t, Acts (evI F) (om (γ (Multiplicative.ofAdd t), 1)) f (c t) := fun t => (hD t f hf (c t)).2 rfl
  have hc1 : c 1 = f₁ := ((hD 1 f hf f₁).1 (by rw [hγ1]; exact hact)).symm
  have hc0 : c 0 = f := by
    have h1 : γ (Multiplicative.ofAdd (0 : ℝ)) = 1 := by
      rw [ofAdd_zero, map_one]
    have hA : Acts (evI F) (om (γ (Multiplicative.ofAdd (0 : ℝ)), 1)) f f := by
      intro ρ _
      rw [h1]
      show om 1 _ = _
      rw [map_one]
      rfl
    exact ((hD 0 f hf f).1 hA).symm
  have hder : ∀ y t, HasDerivAt (fun u => c u y) (Dg (c t) y) t := by
    intro y t
    let ρ := GlobalTheory.ArchIsom.r0 F (Fin n × Fin d)
    let x := GlobalTheory.ArchIsom.splitEquiv F (Fin n × Fin d) (y, 0)
    have hx : (fun i => evI F (x i)) = y := funext fun i => GlobalTheory.ArchIsom.evI_splitEquiv _ _ i
    have hρ : ρ x = 1 := by
      show GlobalTheory.ArchIsom.g0 F (Fin n × Fin d) (fun i => (x i).2) = 1
      have : (fun i => (x i).2) = (0 : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) := rfl
      rw [this]
      exact Set.indicator_of_mem (GlobalTheory.ArchIsom.zero_mem_intPts _) _
    have htens : ∀ g : SInf F (Fin n × Fin d), tens (evI F) (⇑g) ρ x = g y := by
      intro g
      show g (fun i => evI F (x i)) * ρ x = g y
      rw [hx, hρ, mul_one]
    have hom : ∀ u, om (γ (Multiplicative.ofAdd u), 1) (tens (evI F) (⇑f) ρ) = tens (evI F) (⇑(c u)) ρ :=
      fun u => hcA u ρ (GlobalTheory.ArchIsom.restriction_at_standard_point _ f)
    have hsplit : ∀ s', om (γ (Multiplicative.ofAdd (s' + t)), 1) (tens (evI F) (⇑f) ρ) =
        om (γ (Multiplicative.ofAdd s'), 1) (tens (evI F) (⇑(c t)) ρ) := by
      intro s'
      have e : ((γ (Multiplicative.ofAdd (s' + t)), (1 : UA σ W.J)) : UA σ X.J × UA σ W.J) =
          (γ (Multiplicative.ofAdd s'), 1) * (γ (Multiplicative.ofAdd t), 1) := by
        rw [ofAdd_add, map_mul, Prod.mk_mul_mk, mul_one]
      rw [e, map_mul, Module.End.mul_apply, hom t]
    have h0 := (hDg (c t) (hcP t) (Dg (c t))).2 rfl ρ (GlobalTheory.ArchIsom.restriction_at_standard_point _ (c t)) x
    have h0' : HasDerivAt (fun s' => c (s' + t) y) (Dg (c t) y) 0 := by
      have e1 : (fun s' : ℝ => om (γ (Multiplicative.ofAdd s'), 1) (tens (evI F) (⇑(c t)) ρ) x) =
          fun s' => c (s' + t) y := by
        funext s'
        rw [← hsplit s', hom, htens]
      rw [e1, htens] at h0
      exact h0
    have h2' : HasDerivAt (fun u => c (u - t + t) y) (Dg (c t) y) t := by
      have := h0'
      rw [show (0 : ℝ) = t - t from (sub_self t).symm] at this
      exact this.comp_sub_const t t
    simpa only [sub_add_cancel] using h2'
  rw [← hc1, ← hc0]
  refine sub_mem_of_hasDerivAt S _ c (fun t => Dg (c t)) (fun u => hS _ (hγK _) (c u) (hcA u)) (fun t => ?_) hder
  exact Submodule.subset_span ⟨hDgP _ (hcP t), γ, hγL, c t, hcP t, (hDg (c t) (hcP t) _).2 rfl⟩
end GlobalTheory.KExpLine
end
end

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kInfty_exponential_line_in_derivative_span : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (n d : ℕ) (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n) (W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d)
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (χX χW : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chr F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ),
    GlobalTheory.ThK.IsPair B M χX χW om r s r' s' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf σ X B.emb, ∀ f ∈ M.Pol B.ψ B.emb, ∀ f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (om (k, 1)) f f₁ →
      f₁ - f ∈ Submodule.span ℂ {g₁ | g₁ ∈ M.Pol B.ψ B.emb ∧ ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines σ X, ∃ g ∈ M.Pol B.ψ B.emb,
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) g g₁} := by
  first | exact @_root_.GlobalTheory.KExpLine.sub_mem_span_kInfty_exp_derivatives | exact _root_.GlobalTheory.KExpLine.sub_mem_span_kInfty_exp_derivatives | (intros; apply _root_.GlobalTheory.KExpLine.sub_mem_span_kInfty_exp_derivatives <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.KerPCpt
end GlobalTheory.SquareAgree.KerPCpt
namespace GlobalTheory.SquareAgree.KerPCpt
theorem compact_action_mem_ker_polarizationProjection : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.V' Bs.emb, ∀ f ∈ Γ.M'.Pol Bs.ψ Bs.emb, ∀ f₁ ∈ Γ.M'.Pol Bs.ψ Bs.emb, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (om' (k, 1)) f f₁ → ∀ φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), ((Fin W₁.rank × Fin (W.rank + W₁.rank)) → Fv D.host.F w) → ℂ, (∀ w, φ w ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ w in Filter.cofinite, φ w = Γ.M'.vac w) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  intro hPr D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT Pi rf rl p p' hM k hk f hf f₁ hf₁
    hAct φ hφ hv
  have hS := _root_.GlobalTheory.T.kInfty_exponential_line_in_derivative_span hPr D.host.F D.host.E D.sp.cm.sig Bs W₁.rank (W.rank + W₁.rank) Γ.V' Γ.W Γ.M' Xc.α (Xc.α / Xc.β) om' _ _ _ _
    (isPair_small hT) k hk f hf f₁ hAct
  have key : ∀ g ∈ Submodule.span ℂ {g₁ | g₁ ∈ Γ.M'.Pol Bs.ψ Bs.emb ∧ ∃ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.V',
      ∃ g ∈ Γ.M'.Pol Bs.ψ Bs.emb, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ActsD (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F)
        (fun t => om' (γ (Multiplicative.ofAdd t), 1)) g g₁},
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨hx1, γ, hγ, g₀, hg₀, hD⟩ := hx
      exact _root_.GlobalTheory.T.ker_polarizationProjection_lie_stable hPr D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT Pi rf rl p p' hM
        γ hγ g₀ hg₀ x hx1 hD φ hφ hv
    | zero => rw [pure_zero']; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [pure_add']; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [pure_smul']; exact Submodule.smul_mem _ c hx
  have := key _ hS
  rwa [pure_sub'] at this
end GlobalTheory.SquareAgree.KerPCpt
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_polarizationProjection_compact_stable : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.V' Bs.emb, ∀ f ∈ Γ.M'.Pol Bs.ψ Bs.emb, ∀ f₁ ∈ Γ.M'.Pol Bs.ψ Bs.emb, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (om' (k, 1)) f f₁ → ∀ φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), ((Fin W₁.rank × Fin (W.rank + W₁.rank)) → Fv D.host.F w) → ℂ, (∀ w, φ w ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ w in Filter.cofinite, φ w = Γ.M'.vac w) → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f₁ φ - GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  first | exact @_root_.GlobalTheory.SquareAgree.KerPCpt.compact_action_mem_ker_polarizationProjection | exact _root_.GlobalTheory.SquareAgree.KerPCpt.compact_action_mem_ker_polarizationProjection | (intros; apply _root_.GlobalTheory.SquareAgree.KerPCpt.compact_action_mem_ker_polarizationProjection <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KerPolarizationProjectionFiniteDimensional
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.KerPFin
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM GlobalTheory.AdelicU
theorem ker_polarizationProjection_finiteDimensional : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank))) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), ((Fin W₁.rank × Fin (W.rank + W₁.rank)) → Fv D.host.F w) → ℂ), f ∈ Γ.M'.Pol Bs.ψ Bs.emb → (∀ w, φ w ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ w in Filter.cofinite, φ w = Γ.M'.vac w) → φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om' v → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB _hθ _hTr hO hT Pim rf rl p p' hMt v f φ hf hSB
    hvac hv
  classical
  have hψ : IsStd ψ := hO.psi ▸ hT.base.std
  have hM := hT.geo.hM'
  have hstd : ∀ᶠ w in Filter.cofinite, φ w = Set.indicator {x | ∀ i, x i ∈ w.adicCompletionIntegers D.host.F} 1 :=
    (hvac.and hM.std).mono fun w hw => hw.1.trans hw.2
  obtain ⟨r, hr, hrt⟩ := GlobalTheory.PureFactor.exists_rest_factor v f φ hstd
  have hc : (-1 : D.host.E) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have hk : kapX X e hO.JX 1 = 1 := by
    apply Subtype.ext
    simp [kapX]
  have halg : ∀ x ∈ SB _, tens (evFin D.host.F v) x r ∈ algD Γ.M' Bs.ψ Bs.emb := by
    intro x hx
    have hSBx : ∀ w, Function.update φ v x w ∈ SB _ := by
      intro w
      by_cases h : w = v
      · subst h; simpa using hx
      · rw [Function.update_of_ne h]; exact hSB w
    have hvacx : ∀ᶠ w in Filter.cofinite, Function.update φ v x w = Γ.M'.vac w :=
      (hvac.and (Filter.eventually_cofinite_ne v)).mono fun w hw => by rw [Function.update_of_ne hw.2]; exact hw.1
    rw [hrt]
    exact Submodule.subset_span ⟨f, _, hf, hSBx, hvacx, rfl⟩
  suffices H : ∀ x ∈ augAt om' v, tens (evFin D.host.F v) x r ∈ kerPD ψ θ A₁ B Bs Γ cB p' by
    have := H _ hv
    rwa [hrt, Function.update_eq_self] at this
  intro x hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨g, hg, φ₀, hφ₀, φ₁, hφ₁, hact, rfl⟩ := hz
    have hsub : tens (evFin D.host.F v) (φ₁ - φ₀) r = tens (evFin D.host.F v) φ₁ r - tens (evFin D.host.F v) φ₀ r := by
      funext y; simp only [tens, Pi.sub_apply, sub_mul]
    have hRest : Rest (evFin D.host.F v) φ₀ r := by
      refine ⟨hr, ?_⟩
      have hSB0 : ∀ w, Function.update φ v φ₀ w ∈ SB _ := by
        intro w
        by_cases h : w = v
        · subst h; simpa using hφ₀
        · rw [Function.update_of_ne h]; exact hSB w
      rw [hrt]
      exact GlobalTheory.TensUniq.pure_mem_schA f _ hSB0 (GlobalTheory.PureFactor.update_eventually φ v φ₀ hstd)
    have hmove : om' (g, 1) (tens (evFin D.host.F v) φ₀ r) = tens (evFin D.host.F v) φ₁ r := hact r hRest
    obtain ⟨Ψ, hΨ, hD0⟩ := hO.algB' _ (halg φ₀ hφ₀)
    have hgu : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc hO.JW₁ g) = g :=
      (GlobalTheory.ConjUTransport.conjEquiv W₁ (-1) hc hO.JW₁).right_inv g
    have hg0 := GlobalTheory.SquareAgree.CoinvPass.conjUInv_mem_GfC W₁ Γ.V' (-1) hc hO.JW₁ v g hg
    have hW := hO.weilB _ Ψ hD0 (GlobalTheory.ConjUTransport.conjUInv W₁ (-1) hc hO.JW₁ g) 1
    rw [hgu, hk, hmove] at hW
    have hDd := GlobalTheory.SquareAgree.CoinvPass.isDatum_sub hψ hW hD0
    rw [hsub, mem_kerPD hψ]
    refine ⟨Submodule.sub_mem _ (halg φ₁ hφ₁) (halg φ₀ hφ₀), _, Submodule.sub_mem _ (hMt.mapB.stabM.1 _ hg0 Ψ hΨ) hΨ, hDd, ?_⟩
    rw [map_sub, hMt.mapB.invf _ hg0 Ψ hΨ, sub_self]
  | zero =>
    have : tens (evFin D.host.F v) (0 : (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ) r = 0 := by
      funext y; simp [tens]
    rw [this]; exact Submodule.zero_mem _
  | add a b _ _ ha hb =>
    have : tens (evFin D.host.F v) (a + b) r = tens (evFin D.host.F v) a r + tens (evFin D.host.F v) b r := by
      funext y; simp only [tens, Pi.add_apply, add_mul]
    rw [this]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha =>
    have : tens (evFin D.host.F v) (c • a) r = c • tens (evFin D.host.F v) a r := by
      funext y; simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]
    rw [this]; exact Submodule.smul_mem _ c ha
end GlobalTheory.SquareAgree.KerPFin
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarization_kernel_finiteDimensional : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank))) (φ : ∀ w : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F), ((Fin W₁.rank × Fin (W.rank + W₁.rank)) → Fv D.host.F w) → ℂ), f ∈ Γ.M'.Pol Bs.ψ Bs.emb → (∀ w, φ w ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ w in Filter.cofinite, φ w = Γ.M'.vac w) → φ v ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.augAt om' v → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  first | exact @_root_.GlobalTheory.SquareAgree.KerPFin.ker_polarizationProjection_finiteDimensional | exact _root_.GlobalTheory.SquareAgree.KerPFin.ker_polarizationProjection_finiteDimensional | (intros; apply _root_.GlobalTheory.SquareAgree.KerPFin.ker_polarizationProjection_finiteDimensional <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.KerPolarizationProjectionStabilizerFinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.KerStabFin
private theorem inv_mem_local {D : D7} (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    {J : Matrix (Fin d) (Fin d) D.host.E} (hJ : J = D.host.xi0 • reindex e e X.gramᵀ)
    (x : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) :
    Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom x.1 ∈
      HR (AF D.host.F) D.sp.cm.sig X.gram := by
  have hx : (x.1.1 : Matrix (Fin d) (Fin d) (AE D))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J *
      (x.1.1 : Matrix (Fin d) (Fin d) (AE D)).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM J := x.2
  show (((x.1.1 : Matrix (Fin d) (Fin d) (AE D)).submatrix e e).map (cA D))ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram *
    (x.1.1 : Matrix (Fin d) (Fin d) (AE D)).submatrix e e = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram
  generalize (x.1.1 : Matrix (Fin d) (Fin d) (AE D)) = Y at hx ⊢
  rw [hJ, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul] at hx
  have hx' := congrArg (fun y => incA D (D.host.xi0)⁻¹ • y) hx
  simp only [smul_smul, ← map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), map_one, one_smul] at hx'
  have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (reindex e e X.gramᵀ) =
      reindex e e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gram)ᵀ := rfl
  rw [e1] at hx'
  have hs := congrArg (fun y => y.submatrix e e) hx'
  simp only [reindex_apply] at hs
  rw [← submatrix_mul_equiv _ _ _ e _, ← submatrix_mul_equiv _ _ _ e _] at hs
  simp only [submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id, ← transpose_submatrix,
    ← Matrix.submatrix_map] at hs
  have ht := congrArg transpose hs
  rw [transpose_mul, transpose_mul, transpose_transpose, transpose_transpose, ← Matrix.mul_assoc] at ht
  exact ht

set_option maxHeartbeats 1600000 in
private theorem kapX_onto_local : ∀ (D : D7) (X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d)
    (Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E d)
    (hJ : Wd.J = D.host.xi0 • reindex e e X.gramᵀ)
    (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)),
    ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Wd (GlobalTheory.AdelicU.evFin D.host.F v),
    ∃ h' ∈ GfC X, kapX X e hJ h' = h := by
  intro D X d e Wd hJ v h hh
  let h' : GA D X := ⟨Units.map (Matrix.reindexAlgEquiv (AE D) (AE D) e.symm).toMonoidHom h.1, inv_mem_local X e hJ h⟩
  refine ⟨h', ?_, ?_⟩
  · set a : AF D.host.F := 1 - GlobalTheory.EmbChart.atPlace v 1 with ha
    have h0 : GlobalTheory.AdelicU.evFin D.host.F v a = 0 := by
      rw [ha, map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
    have h1 : fstA D.host.F a = 1 := by
      show (1 : Ainf D.host.F) - (0 : Ainf D.host.F) = 1
      exact sub_zero 1
    let f := Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)
    have hf1 : f (a ⊗ₜ[D.host.F] (1 : D.host.E)) = 1 := by
      simp only [f, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, h1]
      rfl
    have hz : ∀ i j, f ((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h - 1) i j) = 0 := by
      intro i j
      have k := congrFun (congrFun (hh a h0) i) j
      rw [Matrix.smul_apply, Matrix.zero_apply, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
        Algebra.algebraMap_self, RingHom.id_apply] at k
      have k2 := congrArg f k
      rw [map_mul, map_zero, hf1, one_mul] at k2
      exact k2
    rw [GfC, MonoidHom.mem_ker]
    apply Units.ext
    ext i j
    show f (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h (e i) (e j)) = (1 : Matrix (Fin X.rank) (Fin X.rank) _) i j
    have e2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h (e i) (e j) =
        (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat h - 1) (e i) (e j) + (1 : Matrix (Fin d) (Fin d) (AE D)) (e i) (e j) := by
      rw [Matrix.sub_apply, sub_add_cancel]
    rw [e2, map_add (f := _), hz, zero_add]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq (α := AF D.host.F ⊗[D.host.F] D.host.E), map_one,
        Matrix.one_apply_eq (α := Ainf D.host.F ⊗[D.host.F] D.host.E)]
    · rw [Matrix.one_apply_ne (α := AF D.host.F ⊗[D.host.F] D.host.E) (e.injective.ne hij), map_zero,
        Matrix.one_apply_ne (α := Ainf D.host.F ⊗[D.host.F] D.host.E) hij]
  · apply Subtype.ext
    apply Units.ext
    ext i j
    show (h.1.1 : Matrix (Fin d) (Fin d) (AE D)) (e (e.symm i)) (e (e.symm j)) = h.1.1 i j
    simp only [Equiv.apply_symm_apply]

theorem stabilizer_finite_ker_polarization : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)), ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W (GlobalTheory.AdelicU.evFin D.host.F v), ∀ Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p', om' (1, h) Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  intro _ D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB _ _ hO hT Pi rf rl p p' hM v h hh Φ hΦ
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hT.base.std
  obtain ⟨g, hg, rfl⟩ := kapX_onto_local D X e Γ.W hO.JX v h hh
  rw [mem_kerPD hstd] at hΦ ⊢
  obtain ⟨_, Φ₀, hΦ₀, hDat, hp⟩ := hΦ
  have hW := hO.weilB Φ Φ₀ hDat 1 g
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) hO.JW₁ 1 = 1 :=
    Subtype.ext (by simp [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU, map_one])
  rw [h1] at hW
  have hmem : ωB (1, g) Φ₀ ∈ algF ψ θ false A₁ B := hM.mapB.stabX.1 g hg Φ₀ hΦ₀
  obtain ⟨ΦD, hΦD, hD'⟩ := hO.algB _ hmem
  have heq := GlobalTheory.ThetaInj.theta_inj Γ.M' ψ hstd cB _ _ _ hW hD'
  refine ⟨heq ▸ hΦD, _, hmem, hW, ?_⟩
  rw [hM.mapB.eqf g hg Φ₀ hΦ₀, hp, map_zero]
end GlobalTheory.SquareAgree.KerStabFin
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_polarizationProjection_stabilizer_finite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := D.host.F)), ∀ h ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt D.sp.cm.sig Γ.W (GlobalTheory.AdelicU.evFin D.host.F v), ∀ Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p', om' (1, h) Φ ∈ kerPD ψ θ A₁ B Bs Γ cB p' := by
  first | exact @_root_.GlobalTheory.SquareAgree.KerStabFin.stabilizer_finite_ker_polarization | exact _root_.GlobalTheory.SquareAgree.KerStabFin.stabilizer_finite_ker_polarization | (intros; apply _root_.GlobalTheory.SquareAgree.KerStabFin.stabilizer_finite_ker_polarization <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
theorem GlobalTheory.SquareAgree.exists_ker_projDerivation_thetaSubspace : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∃ N : Submodule ℂ ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ), (∀ Φ₀D, Φ₀D ∈ N ↔ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb ∧ ∃ Φ₀ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧ p' Φ₀ = 0) ∧
      IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N ∧ N ≠ algD Γ.M' Bs.ψ Bs.emb := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT Pi rf rl p p' hm
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hO.psi ▸ hT.base.std
  refine ⟨kerPD ψ θ A₁ B Bs Γ cB p', fun Φ₀D => mem_kerPD hstd θ A₁ B Bs Γ cB p' Φ₀D, ?_, ?_⟩
  · exact
      { le := fun Φ hΦ => ((mem_kerPD hstd θ A₁ B Bs Γ cB p' Φ).1 hΦ).1
        fin := _root_.GlobalTheory.T.polarization_kernel_finiteDimensional hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT Pi rf rl p p' hm
        lie := _root_.GlobalTheory.T.ker_polarizationProjection_lie_stable hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT Pi rf rl p p' hm
        cpt := _root_.GlobalTheory.T.ker_polarizationProjection_compact_stable hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT Pi rf rl p p' hm
        stabFin := _root_.GlobalTheory.T.ker_polarizationProjection_stabilizer_finite hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT Pi rf rl p p' hm
        stabLie := _root_.GlobalTheory.T.ker_polarizationProjection_stable_under_stabilizer_lie hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT Pi rf rl p p' hm
        stabCpt := _root_.GlobalTheory.T.ker_polarizationProjection_stable_under_stabilizer_compact hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hTr hO hT Pi rf rl p p' hm }
  · intro hEq
    haveI : Nontrivial Pi := hm.irred.1
    obtain ⟨x, hx⟩ := exists_ne (0 : Pi)
    have hxm : x ∈ (algF ψ θ false A₁ B).map p' := by rw [hm.mapB.onto]; trivial
    obtain ⟨Φ₀, hΦ₀, rfl⟩ := hxm
    obtain ⟨ΦD, hD, hDat⟩ := hO.algB Φ₀ hΦ₀
    have hD' : ΦD ∈ kerPD ψ θ A₁ B Bs Γ cB p' := hEq ▸ hD
    obtain ⟨-, Φ₁, -, hDat1, h0⟩ := (mem_kerPD hstd θ A₁ B Bs Γ cB p' ΦD).1 hD'
    have he : Φ₀ = Φ₁ := IsDatum.fun_eq Γ.M' ψ (⇑cB) cB.surjective hDat hDat1
    exact hx (he ▸ h0)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSubspace_eq_ker_projDerivation_of_square : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∃ N : Submodule ℂ ((Fin W₁.rank × Fin (W.rank + W₁.rank) → AF D.host.F) → ℂ), (∀ Φ₀D, Φ₀D ∈ N ↔ Φ₀D ∈ algD Γ.M' Bs.ψ Bs.emb ∧ ∃ Φ₀ ∈ algF ψ θ false A₁ B, IsDatum Γ.M' ψ cB Φ₀D Φ₀ ∧ p' Φ₀ = 0) ∧
      IsThetaSubG Γ.M' Bs.ψ Bs.emb om' N ∧ N ≠ algD Γ.M' Bs.ψ Bs.emb := by
  first | exact @_root_.GlobalTheory.SquareAgree.exists_ker_projDerivation_thetaSubspace | exact _root_.GlobalTheory.SquareAgree.exists_ker_projDerivation_thetaSubspace | (intros; apply _root_.GlobalTheory.SquareAgree.exists_ker_projDerivation_thetaSubspace <;> assumption)
end
