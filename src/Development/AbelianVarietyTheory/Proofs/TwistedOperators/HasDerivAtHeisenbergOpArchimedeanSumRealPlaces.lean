module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittFrameTorusEqLeviElement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationThetaFunctionSupLeQuotientHeig
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPcRatFMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumNormSqLeOfRootOfUnityAddCharCombination

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtHeisenbergOpArchimedeanSumRealPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtHeisenbergOpArchimedeanSumRealPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.ArchLineSum

open GlobalTheory.SplitScalar GlobalTheory.LatVac

variable {D : D7}

theorem fstA_realAd (t : ℝ) : fstA D.host.F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) = fstA D.host.F (GlobalTheory.WittLevi.realAd D t) := by
  apply (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).injective
  show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm _) = _
  rw [RingEquiv.apply_symm_apply, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  ext w
  · show t = InfinitePlace.Completion.extensionEmbeddingOfIsReal w.2
      ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w.1)).symm t)
    exact ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w.1)).apply_symm_apply t).symm
  · exact absurd (IsTotallyReal.isReal w.1) (InfinitePlace.not_isReal_iff_isComplex.2 w.2)

theorem infPart_realAd (t : ℝ) : infPart D (algebraMap (AF D.host.F) (AE D) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t)) =
    infPart D (GlobalTheory.WittLevi.realE D t) := by
  show fstA D.host.F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) ⊗ₜ[D.host.F] (1 : D.host.E) = fstA D.host.F (GlobalTheory.WittLevi.realAd D t) ⊗ₜ[D.host.F] (1 : D.host.E)
  rw [fstA_realAd]

theorem theta_realAd {θ : InfFam D} (hθ : IsInfFam θ) (ρ : D.what₂.Tau) (t : ℝ) :
    θ ρ (infPart D (algebraMap (AF D.host.F) (AE D) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t))) = t := by
  rw [infPart_realAd]; exact GlobalTheory.WittLevi.theta_realE hθ ρ t

theorem finPart_smul (u : AF D.host.F) (a : AE D) :
    finPart D (u • a) = (sndA D.host.F u ⊗ₜ[D.host.F] (1 : D.host.E)) * finPart D a := by
  rw [Algebra.smul_def, map_mul]; rfl

theorem infPart_smul (u : AF D.host.F) (a : AE D) :
    infPart D (u • a) = infPart D (algebraMap (AF D.host.F) (AE D) u) * infPart D a := by
  rw [Algebra.smul_def, map_mul]


set_option synthInstance.maxHeartbeats 400000 in
theorem realAd_smul_eq {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {w : WO S T}
    (hw : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) w) (t : ℝ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w = ∑ τ, lineAt θ τ (compAt θ τ w) t := by
  classical
  have hL : ∀ τ, IsLineAt θ τ (compAt θ τ w) (lineAt θ τ (compAt θ τ w)) := fun τ =>
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ τ _)
  ext i j
  rw [← sub_eq_zero]
  apply GlobalTheory.StdUnn.RealComp.eq_zero_of_parts
  · rw [← GlobalTheory.StdUnn.RealComp.theta_zero_iff hθ]
    intro ρ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [(infPart D).map_sub, (θ ρ).map_sub, sub_eq_zero, Matrix.sum_apply, map_sum (infPart D), map_sum (θ ρ)]
    have e1 : ∀ τ, θ ρ (infPart D (lineAt θ τ (compAt θ τ w) t i j)) =
        if ρ = τ then (t : ℂ) * θ ρ (infPart D (w i j)) else 0 := by
      intro τ
      have := congrFun (congrFun ((hL τ).2.2 t ρ) i) j
      change θ ρ (infPart D (lineAt θ τ (compAt θ τ w) t i j)) = _ at this
      rw [this]
      split_ifs with h
      · subst h; rfl
      · rfl
    rw [Finset.sum_congr rfl fun τ _ => e1 τ, Finset.sum_ite_eq Finset.univ ρ, if_pos (Finset.mem_univ _)]
    show θ ρ (infPart D (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w i j)) = _
    rw [infPart_smul, (θ ρ).map_mul, theta_realAd hθ]
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [(finPart D).map_sub, sub_eq_zero, Matrix.sum_apply, map_sum (finPart D)]
    show finPart D (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w i j) = _
    rw [finPart_smul, show sndA D.host.F (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t) = 0 from rfl, TensorProduct.zero_tmul,
      zero_mul]
    exact (Finset.sum_eq_zero fun τ _ => congrFun (congrFun ((hL τ).2.1 t) i) j).symm

end GlobalTheory.ArchLineSum

namespace GlobalTheory.ArchLineSum

open GlobalTheory.SplitScalar GlobalTheory.LatVac


set_option synthInstance.maxHeartbeats 400000 in
theorem hasDerivAt_realAd_smul : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (S T : HSp D) (f : WO S T → ℂ), IsThetaFunO ψ S T f →
    ∀ w : WO S T, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) w → ∀ x : WO S T,
      HasDerivAt (fun t : ℝ => heisO ψ S T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w) f x)
        (∑ τ, dRho (heisO ψ S T) θ τ (compAt θ τ w) f x) 0 := by
  intro D ψ θ hψ hθ S T f hf w hw x
  classical
  have hc : Continuous ψ := hψ.1.1
  have hL : ∀ τ, IsLineAt θ τ (compAt θ τ w) (lineAt θ τ (compAt θ τ w)) := fun τ =>
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ hθ _ _ τ _)
  let Λ : (D.what₂.Tau → ℝ) →+ WO S T :=
    ∑ τ, (lineAt θ τ (compAt θ τ w)).comp (Pi.evalAddMonoidHom (fun _ : D.what₂.Tau => ℝ) τ)
  have hΛ : ∀ s, Λ s = ∑ τ, lineAt θ τ (compAt θ τ w) (s τ) := fun s => by
    simp [Λ]
  have hΛc : Continuous Λ := by
    rw [show (Λ : (D.what₂.Tau → ℝ) → WO S T) = fun s => ∑ τ, lineAt θ τ (compAt θ τ w) (s τ) from funext hΛ]
    exact continuous_finsetSum _ fun τ _ => (hL τ).1.comp (continuous_apply τ)
  have hΛf : ∀ s, (Λ s).map (finPart D) = 0 := fun s => by
    ext i j
    rw [hΛ]
    show finPart D ((∑ τ, lineAt θ τ (compAt θ τ w) (s τ) : WO S T) i j) = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.sum_apply, map_sum (finPart D)]
    exact Finset.sum_eq_zero fun τ _ => congrFun (congrFun ((hL τ).2.1 (s τ)) i) j
  let G : (D.what₂.Tau → ℝ) → ℂ := fun s => heisO ψ S T (Λ s) f x
  have hχ : ∀ τ, Differentiable ℝ fun t : ℝ => ψ (symplOH S T x (lineAt θ τ (compAt θ τ w) t)) := fun τ => by
    refine GlobalTheory.FockTranslate.differentiable_of_char _
      (hc.comp (continuous_const.mul (continuous_symplO S T continuous_const (hL τ).1))) ?_ ?_
    · rw [map_zero, symplOH, symplO_zero_right, mul_zero, AddChar.map_zero_eq_one]
    · intro s t
      rw [map_add (f := _), symplOH_add_right, AddChar.map_add_eq_mul]
  have hpsi : ∀ s, ψ (symplOH S T x (Λ s)) = ∏ τ, ψ (symplOH S T x (lineAt θ τ (compAt θ τ w) (s τ))) := by
    intro s
    rw [hΛ]
    let φ : WO S T →+ AF D.host.F :=
      ⟨⟨symplOH S T x, by rw [symplOH, symplO_zero_right, mul_zero]⟩, symplOH_add_right S T x⟩
    have key : ∀ (s' : Finset D.what₂.Tau) (g : D.what₂.Tau → WO S T),
        ψ (φ (∑ τ ∈ s', g τ)) = ∏ τ ∈ s', ψ (φ (g τ)) := by
      intro s' g
      induction s' using Finset.induction_on with
      | empty => rw [Finset.sum_empty, Finset.prod_empty, map_zero, AddChar.map_zero_eq_one]
      | insert a s' ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, map_add (f := _), AddChar.map_add_eq_mul, ih]
    exact key Finset.univ _
  have hGd : Differentiable ℝ G := by
    have h1 : Differentiable ℝ fun s : D.what₂.Tau → ℝ => ψ (symplOH S T x (Λ s)) := by
      simp only [hpsi]
      have hp : ∀ s' : Finset D.what₂.Tau, Differentiable ℝ fun s : D.what₂.Tau → ℝ =>
          ∏ τ ∈ s', ψ (symplOH S T x (lineAt θ τ (compAt θ τ w) (s τ))) := by
        intro s'
        induction s' using Finset.induction_on with
        | empty => simp only [Finset.prod_empty]; exact differentiable_const _
        | insert a s' ha ih =>
          simp only [Finset.prod_insert ha]
          have hτ : Differentiable ℝ fun s : D.what₂.Tau → ℝ => s a := differentiable_apply a
          exact ((hχ a).comp hτ).mul ih
      exact hp Finset.univ
    have h2 : Differentiable ℝ fun s : D.what₂.Tau → ℝ => f (x + Λ s) := by
      let e := Fintype.equivFin D.what₂.Tau
      let ℓ : (Fin (Fintype.card D.what₂.Tau) → ℝ) ≃L[ℝ] (D.what₂.Tau → ℝ) :=
        (LinearEquiv.funCongrLeft ℝ ℝ e).toContinuousLinearEquiv
      have hs := hf.smooth _ (Λ.comp (ℓ : (Fin (Fintype.card D.what₂.Tau) → ℝ) →+ (D.what₂.Tau → ℝ)))
        (hΛc.comp ℓ.continuous) (fun t => hΛf _) x
      have : (fun s : D.what₂.Tau → ℝ => f (x + Λ s)) =
          (fun t => f (x + Λ.comp (ℓ : (Fin (Fintype.card D.what₂.Tau) → ℝ) →+ (D.what₂.Tau → ℝ)) t)) ∘ ℓ.symm := by
        funext s
        simp
      rw [this]
      exact (hs.differentiable (by simp)).comp ℓ.symm.differentiable
    exact h1.mul h2
  have hfun : (fun t : ℝ => heisO ψ S T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w) f x) =
      G ∘ (fun t : ℝ => fun _ : D.what₂.Tau => t) := by
    funext t
    simp only [Function.comp, G, hΛ]
    rw [realAd_smul_eq hθ hw t]
  have hdiag : HasDerivAt (fun t : ℝ => (fun _ : D.what₂.Tau => t)) (fun _ => (1 : ℝ)) 0 :=
    hasDerivAt_pi.2 fun _ => hasDerivAt_id 0
  have hG0 : HasFDerivAt G (fderiv ℝ G 0) ((fun t : ℝ => fun _ : D.what₂.Tau => t) 0) := (hGd 0).hasFDerivAt
  have hcomp := hG0.comp_hasDerivAt (0 : ℝ) hdiag
  rw [hfun]
  suffices key : fderiv ℝ G 0 (fun _ => 1) = ∑ τ, dRho (heisO ψ S T) θ τ (compAt θ τ w) f x by
    rw [← key]; exact hcomp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show (fun _ : D.what₂.Tau => (1 : ℝ)) = ∑ τ, Pi.single τ (1 : ℝ) from (Finset.univ_sum_single _).symm, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hline : HasDerivAt (fun t : ℝ => t • (Pi.single τ (1 : ℝ) : D.what₂.Tau → ℝ))
      ((1 : ℝ) • (Pi.single τ (1 : ℝ) : D.what₂.Tau → ℝ)) 0 := (hasDerivAt_id 0).smul_const _
  have hG0' : HasFDerivAt G (fderiv ℝ G 0) ((fun t : ℝ => t • (Pi.single τ (1 : ℝ) : D.what₂.Tau → ℝ)) 0) := by
    simpa using (hGd 0).hasFDerivAt
  have h3 := hG0'.comp_hasDerivAt (0 : ℝ) hline
  rw [one_smul] at h3
  have e : (G ∘ fun t : ℝ => t • (Pi.single τ (1 : ℝ) : D.what₂.Tau → ℝ)) =
      fun t => heisO ψ S T (lineAt θ τ (compAt θ τ w) t) f x := by
    funext t
    simp only [Function.comp, G, hΛ]
    rw [Finset.sum_eq_single τ (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
    simp
  rw [e] at h3
  exact h3.deriv.symm

end GlobalTheory.ArchLineSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtHeisenbergOpArchimedeanSumRealPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_heisenbergOp_archimedean_sum_realPlaces : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (S T : HSp D) (f : WO S T → ℂ), IsThetaFunO ψ S T f →
    ∀ w : WO S T, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) w → ∀ x : WO S T,
      HasDerivAt (fun t : ℝ => heisO ψ S T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd D.host.F t • w) f x)
        (∑ τ, dRho (heisO ψ S T) θ τ (compAt θ τ w) f x) 0 := by
  first | exact @GlobalTheory.ArchLineSum.hasDerivAt_realAd_smul | exact GlobalTheory.ArchLineSum.hasDerivAt_realAd_smul | (intros; apply GlobalTheory.ArchLineSum.hasDerivAt_realAd_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilKernelFunctionalSuperpositionIsTame
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilKernelFunctionalSuperpositionIsTame
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

noncomputable section

namespace GlobalTheory.KerTame

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}

theorem om_heis_apply (hom : IsWeilDatumO ψ S T χS χT om) (p : GA D S × GA D T) (u : WO S T) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (x : WO S T) :
    om p (heisO ψ S T u f) x = ψ (symplOH S T x (actO S T p.1 p.2 u)) * om p f (x + actO S T p.1 p.2 u) := by
  obtain ⟨g, h⟩ := p
  rw [hom.om_heis g h u f hf]; rfl

theorem om_heis_bound (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    ∃ (C : ℝ) (A : ℕ), ∀ g h u x, ‖om (g, h) (heisO ψ S T u f) x‖ ≤ C * (quotHeight S g * quotHeight T h) ^ A := by
  obtain ⟨C, A, hC⟩ := GlobalTheory.T.weilRepresentation_thetaFunction_sup_le_quotientHeight D ψ S T χS χT om hom f hf
  refine ⟨C, A, fun g h u x => ?_⟩
  rw [om_heis_apply hom (g, h) u hf x, norm_mul, hom.std.1.2.1, one_mul]
  exact hC g h _

theorem continuous_actO_gen {X : Type} [TopologicalSpace X] {g : X → GA D S} {h : X → GA D T} {u : X → WO S T}
    (hg : Continuous g) (hh : Continuous h) (hu : Continuous u) : Continuous fun t => actO S T (g t) (h t) (u t) := by
  have hmt : ∀ V : HSp D, Continuous (Formalism.L2.Theta.mt V) := fun V =>
    Units.continuous_val.comp continuous_subtype_val
  have hmti : ∀ V : HSp D, Continuous fun g : GA D V => Formalism.L2.Theta.mt V g⁻¹ := fun V =>
    Units.continuous_coe_inv.comp continuous_subtype_val
  unfold actO
  exact (((hmt T).comp hh).matrix_mul hu).matrix_mul ((hmti S).comp hg)

theorem continuous_om_heis (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Continuous fun q : ((GA D S × GA D T) × WO S T) × WO S T => om q.1.1 (heisO ψ S T q.2 f) q.1.2 := by
  have hJ : Continuous fun p : (GA D S × GA D T) × WO S T => om p.1 f p.2 :=
    (@GlobalTheory.Unf.jointCont_all D) ψ S T χS χT om hom f hf
  have hA : Continuous fun q : ((GA D S × GA D T) × WO S T) × WO S T => actO S T q.1.1.1 q.1.1.2 q.2 := by
    exact continuous_actO_gen (continuous_fst.comp (continuous_fst.comp continuous_fst))
      (continuous_snd.comp (continuous_fst.comp continuous_fst)) continuous_snd
  have hB : Continuous fun q : ((GA D S × GA D T) × WO S T) × WO S T =>
      ((q.1.1, q.1.2 + actO S T q.1.1.1 q.1.1.2 q.2) : (GA D S × GA D T) × WO S T) :=
    (continuous_fst.comp continuous_fst).prodMk ((continuous_snd.comp continuous_fst).add hA)
  have hc : Continuous fun q : ((GA D S × GA D T) × WO S T) × WO S T =>
      ψ (symplOH S T q.1.2 (actO S T q.1.1.1 q.1.1.2 q.2)) * om q.1.1 f (q.1.2 + actO S T q.1.1.1 q.1.1.2 q.2) :=
    (hom.std.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH (continuous_snd.comp continuous_fst) hA)).mul (hJ.comp hB)
  exact hc.congr fun q => (om_heis_apply hom q.1.1 q.2 hf q.1.2).symm

end GlobalTheory.KerTame

namespace GlobalTheory.KerTame

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}

theorem om_superpos (hom : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (p : GA D S × GA D T) (m' : Measure (WO S T)) [SFinite m'] (α : WO S T → ℂ) (hα : Integrable α m')
    (hI : IsThetaFunO ψ S T (fun x => ∫ u, α u * heisO ψ S T u f x ∂m')) (x : WO S T) :
    om p (fun x => ∫ u, α u * heisO ψ S T u f x ∂m') x = ∫ u, α u * om p (heisO ψ S T u f) x ∂m' := by
  obtain ⟨-, -, i3, -, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : SecondCountableTopology (WO S T) := i3
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  have hφ : AEMeasurable (fun u : WO S T => (u, α u)) m' := measurable_id.aemeasurable.prodMk hα.aemeasurable
  set ν : Measure (WO S T × ℂ) := m'.map (fun u => (u, α u)) with hν
  obtain ⟨C1, hC1⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hom.std f hf
  obtain ⟨C2, hC2⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hom.std _ (hom.om_pres p f hf)
  set F : WO S T × ℂ → WO S T → ℂ := fun z => z.2 • heisO ψ S T z.1 f with hF
  have hFth : ∀ z, IsThetaFunO ψ S T (F z) := fun z =>
    GlobalTheory.WeilVacMove.isTheta_smul _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hom.std hf z.1)
  have hc1 : Continuous (Function.uncurry F) := by
    have e : Function.uncurry F = fun q : (WO S T × ℂ) × WO S T => q.1.2 * (ψ (symplOH S T q.2 q.1.1) * f (q.2 + q.1.1)) := by
      funext q; rfl
    rw [e]
    exact (continuous_snd.comp continuous_fst).mul ((hom.std.1.1.comp (GlobalTheory.OrientedHeis.continuous_symplOH continuous_snd
      (continuous_fst.comp continuous_fst))).mul (hf.cont.comp (continuous_snd.add (continuous_fst.comp continuous_fst))))
  have hc2 : Continuous fun q : (WO S T × ℂ) × WO S T => om p (F q.1) q.2 := by
    have e : (fun q : (WO S T × ℂ) × WO S T => om p (F q.1) q.2) =
        fun q => q.1.2 * om p (heisO ψ S T q.1.1 f) q.2 := by
      funext q; simp only [hF, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact (continuous_snd.comp continuous_fst).mul ((continuous_om_heis hom hf).comp
      ((continuous_const.prodMk continuous_snd).prodMk (continuous_fst.comp continuous_fst)))
  have hβ : Integrable (fun z : WO S T × ℂ => ‖z.2‖ * max C1 C2) ν := by
    have hm : Continuous fun z : WO S T × ℂ => ‖z.2‖ * max C1 C2 := (continuous_norm.comp continuous_snd).mul continuous_const
    rw [hν, integrable_map_measure hm.measurable.aestronglyMeasurable hφ]
    exact hα.norm.mul_const _
  have hdom : ∀ z y, ‖F z y‖ ≤ ‖z.2‖ * max C1 C2 ∧ ‖om p (F z) y‖ ≤ ‖z.2‖ * max C1 C2 := by
    intro z y
    constructor
    · show ‖z.2 * (ψ (symplOH S T y z.1) * f (y + z.1))‖ ≤ _
      rw [norm_mul, norm_mul, hom.std.1.2.1, one_mul]
      exact mul_le_mul_of_nonneg_left ((hC1 _).trans (le_max_left _ _)) (norm_nonneg _)
    · simp only [hF, map_smul, Pi.smul_apply, smul_eq_mul]
      obtain ⟨g, h⟩ := p
      rw [norm_mul, om_heis_apply hom (g, h) z.1 hf y, norm_mul, hom.std.1.2.1, one_mul]
      exact mul_le_mul_of_nonneg_left ((hC2 _).trans (le_max_right _ _)) (norm_nonneg _)
  have hint : ∀ y, ∫ z, F z y ∂ν = ∫ u, α u * heisO ψ S T u f y ∂m' := by
    intro y
    rw [hν, integral_map hφ]
    · rfl
    · exact (hc1.comp (continuous_id.prodMk continuous_const)).measurable.aestronglyMeasurable
  have hint2 : ∫ z, om p (F z) x ∂ν = ∫ u, α u * om p (heisO ψ S T u f) x ∂m' := by
    rw [hν, integral_map hφ]
    · simp only [hF, map_smul, Pi.smul_apply, smul_eq_mul]
    · exact (hc2.comp (continuous_id.prodMk continuous_const)).measurable.aestronglyMeasurable
  have hI' : IsThetaFunO ψ S T (fun y => ∫ z, F z y ∂ν) := by
    simp only [hint]; exact hI
  have key := GlobalTheory.CommIntBdd.om_integral_comm_dom D ψ S T χS χT om hom (WO S T × ℂ) ν F p
    (fun z => ‖z.2‖ * max C1 C2) hFth hc1 hc2 hβ hdom hI' x
  have e : (fun w' => ∫ z, F z w' ∂ν) = fun y => ∫ u, α u * heisO ψ S T u f y ∂m' := funext hint
  rw [← hint2, ← key, e]

end GlobalTheory.KerTame

namespace GlobalTheory.KerTame

theorem kernel_tame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T),
    IsWeilDatumO ψ S T χS χT om → ∀ (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y]
    [BorelSpace Y] (m : Measure Y) [SFinite m] (c : Y → ℂ) (g : Y → GA D S) (h : Y → GA D T) (w : Y → WO S T),
    Measurable c → Continuous g → Continuous h → Continuous w →
    (∀ k : ℕ, Integrable (fun y => ‖c y‖ * (quotHeight S (g y) * quotHeight T (h y)) ^ k) m) →
    (∀ f, IsThetaFunO ψ S T f → Integrable (fun y => c y * om (g y, h y) f (w y)) m) ∧
      Tame ψ S T fun f => ∫ y, c y * om (g y, h y) f (w y) ∂m := by
  intro D ψ S T χS χT om hom Y _ _ _ _ m _ c g h w hc hg hh hw hint
  obtain ⟨-, -, i3, -, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D T.rank S.rank
  haveI : SecondCountableTopology (WO S T) := i3
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : FirstCountableTopology (WO S T) := @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ i3
  have hgh : Continuous fun y => ((g y, h y) : GA D S × GA D T) := hg.prodMk hh

  have hK : ∀ f, IsThetaFunO ψ S T f →
      Continuous fun q : Y × WO S T => om (g q.1, h q.1) (heisO ψ S T q.2 f) (w q.1) := fun f hf =>
    (continuous_om_heis hom hf).comp (((hgh.comp continuous_fst).prodMk (hw.comp continuous_fst)).prodMk continuous_snd)
  have hbd : ∀ f, IsThetaFunO ψ S T f → ∃ (C : ℝ) (A : ℕ), ∀ y u,
      ‖c y * om (g y, h y) (heisO ψ S T u f) (w y)‖ ≤ C * (‖c y‖ * (quotHeight S (g y) * quotHeight T (h y)) ^ A) := by
    intro f hf
    obtain ⟨C, A, hC⟩ := om_heis_bound hom hf
    refine ⟨C, A, fun y u => ?_⟩
    rw [norm_mul]
    calc ‖c y‖ * ‖om (g y, h y) (heisO ψ S T u f) (w y)‖
        ≤ ‖c y‖ * (C * (quotHeight S (g y) * quotHeight T (h y)) ^ A) :=
          mul_le_mul_of_nonneg_left (hC _ _ _ _) (norm_nonneg _)
      _ = C * (‖c y‖ * (quotHeight S (g y) * quotHeight T (h y)) ^ A) := by ring
  have hintH : ∀ f, IsThetaFunO ψ S T f → ∀ u,
      Integrable (fun y => c y * om (g y, h y) (heisO ψ S T u f) (w y)) m := by
    intro f hf u
    obtain ⟨C, A, hC⟩ := hbd f hf
    exact Integrable.mono' ((hint A).const_mul C)
      (hc.aestronglyMeasurable.mul ((hK f hf).comp (continuous_id.prodMk continuous_const)).measurable.aestronglyMeasurable)
      (ae_of_all _ fun y => hC y u)
  have hzero : ∀ f : WO S T → ℂ, heisO ψ S T 0 f = f := by
    intro f; funext x; simp [heisO, symplOH, symplO, hO]
  have hintK : ∀ f, IsThetaFunO ψ S T f → Integrable (fun y => c y * om (g y, h y) f (w y)) m := by
    intro f hf
    simpa only [hzero] using hintH f hf 0
  refine ⟨hintK, ?_, ?_, ?_, ?_, ?_⟩
  · intro f f' hf hf'
    simp only [map_add (f := _), Pi.add_apply, mul_add]
    exact integral_add (hintK f hf) (hintK f' hf')
  · intro a f hf
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  · intro f hf
    obtain ⟨C, A, hC⟩ := hbd f hf
    refine continuous_of_dominated (bound := fun y => C * (‖c y‖ * (quotHeight S (g y) * quotHeight T (h y)) ^ A))
      (fun u => (hintH f hf u).aestronglyMeasurable) (fun u => ae_of_all _ fun y => hC y u) ((hint A).const_mul C)
      (ae_of_all _ fun y => ?_)
    exact continuous_const.mul ((hK f hf).comp (continuous_const.prodMk continuous_id))
  · intro f hf
    obtain ⟨C, A, hC⟩ := hbd f hf
    exact ⟨∫ y, C * (‖c y‖ * (quotHeight S (g y) * quotHeight T (h y)) ^ A) ∂m, fun u =>
      norm_integral_le_of_norm_le ((hint A).const_mul C) (ae_of_all _ fun y => hC y u)⟩
  · intro f hf m' _ α hα hI
    have e1 : ∀ y, om (g y, h y) (fun x => ∫ u, α u * heisO ψ S T u f x ∂m') (w y) =
        ∫ u, α u * om (g y, h y) (heisO ψ S T u f) (w y) ∂m' := fun y =>
      om_superpos hom hf (g y, h y) m' α hα hI (w y)
    simp only [e1]
    simp only [← integral_const_mul]
    rw [integral_integral_swap]
    · refine integral_congr_ae (ae_of_all _ fun u => ?_)
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      simp only
      ring
    · obtain ⟨C, A, hC⟩ := hbd f hf
      refine Integrable.mono' (((hint A).const_mul C).mul_prod hα.norm) ?_ (ae_of_all _ fun q => ?_)
      · exact (hc.aestronglyMeasurable.comp_fst).mul (hα.aestronglyMeasurable.comp_snd.mul
          (hK f hf).measurable.aestronglyMeasurable)
      · calc ‖c q.1 * (α q.2 * om (g q.1, h q.1) (heisO ψ S T q.2 f) (w q.1))‖
            = ‖c q.1 * om (g q.1, h q.1) (heisO ψ S T q.2 f) (w q.1)‖ * ‖α q.2‖ := by
              simp only [norm_mul]; ring
          _ ≤ C * (‖c q.1‖ * (quotHeight S (g q.1) * quotHeight T (h q.1)) ^ A) * ‖α q.2‖ :=
              mul_le_mul_of_nonneg_right (hC _ _) (norm_nonneg _)

end GlobalTheory.KerTame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilKernelFunctionalSuperpositionIsTameStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilKernelFunctional_superposition_isTame : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (Y : Type) [TopologicalSpace Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (m : Measure Y) [SFinite m] (c : Y → ℂ) (g : Y → GA D S) (h : Y → GA D T) (w : Y → WO S T), Measurable c → Continuous g → Continuous h → Continuous w → (∀ k : ℕ, Integrable (fun y => ‖c y‖ * (quotHeight S (g y) * quotHeight T (h y)) ^ k) m) → (∀ f, IsThetaFunO ψ S T f → Integrable (fun y => c y * om (g y, h y) f (w y)) m) ∧ Tame ψ S T fun f => ∫ y, c y * om (g y, h y) f (w y) ∂m := by
  first | exact @GlobalTheory.KerTame.kernel_tame | exact GlobalTheory.KerTame.kernel_tame | (intros; apply GlobalTheory.KerTame.kernel_tame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedPlaceOfUnramifiedOnePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedPlaceOfUnramifiedOnePrime
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnramFromOnePrime

open GlobalTheory.IdemSupport GlobalTheory.ResLoc

variable {D : D7}

theorem eq_of_ev {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ) {a b : AE D}
    (hi : infPart D a = infPart D b) (hf : ∀ Q, Φ a Q = Φ b Q) : a = b := by
  refine sub_eq_zero.1 (hΦ.ext (a - b) (by rw [RingHom.map_sub, hi, sub_self]) (FiniteAdeleRing.ext _ fun Q => ?_))
  rw [ev_sub, hf Q, sub_self]
  rfl

theorem eq_one_of_supp {w : HeightOneSpectrum (𝓞 D.host.E)} {e f : AE D} {χ : (AE D)ˣ →* Circle}
    (h : Formalism.IndefR.Mult.IsPrimeIdem w e f) (hu : GlobalTheory.LFun.UnrAt χ w) (x : (AE D)ˣ)
    (hx : e * ((x : AE D) - 1) = (x : AE D) - 1) (h1 : finPart D (x : AE D) ∈ intAE D)
    (h2 : finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D) : χ x = 1 := by
  obtain ⟨y, hy, rfl⟩ := GlobalTheory.WeilAtPlace.exists_eq_locIdele (GlobalTheory.WeilAtPlace.isPrimeIdem_infPart h)
    (GlobalTheory.LFun.finPart_of_isPrimeIdem h) x hx
  have hy' : ((y⁻¹ : (w.adicCompletion D.host.E)ˣ) : w.adicCompletion D.host.E) =
      GlobalTheory.LFun.compAt D.host.F w (finPart D ((GlobalTheory.LFun.locIdele D.host.F w y)⁻¹ : (AE D)ˣ)) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hy, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have a1 : Valued.v (y : w.adicCompletion D.host.E) ≤ 1 := by
    rw [hy]; exact (GlobalTheory.LFun.mem_intAE_iff_compAt _).1 h1 w
  have a2 : Valued.v ((y⁻¹ : (w.adicCompletion D.host.E)ˣ) : w.adicCompletion D.host.E) ≤ 1 := by
    rw [hy']; exact (GlobalTheory.LFun.mem_intAE_iff_compAt _).1 h2 w
  have hun : Formalism.L2.Host.IsUnitAt w y :=
    GlobalTheory.UnramOver.val_eq_one_of_unit Valued.v (RingHom.id _) y a1 a2
  have := hu y hun
  exact Circle.ext (congrArg Units.val this)

end GlobalTheory.UnramFromOnePrime

namespace GlobalTheory.UnramFromOnePrime

open GlobalTheory.IdemSupport GlobalTheory.ResLoc


set_option maxHeartbeats 1000000 in
theorem unramAt_of_unrAt_one : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), IsHeckeChar D ν → ResEta D ν 0 →
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt ν w → GlobalTheory.WeilParts.UnramAt ε ν := by
  classical
  intro D ν _ hR v ε hε w hw hu x hx h1 h2
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨e, f, hp⟩ := exists_isPrimeIdem hΦ w
  obtain ⟨hd, ε', hε', hf⟩ := of_isPrimeIdem hΦ hp
  rw [hw] at hε'
  have pc := place_comp hΦ hε
  have pc' := place_comp hΦ hε'
  have hfε : f = algebraMap (AF D.host.F) (AE D) ε := by
    rw [hf]
    refine eq_of_ev hΦ (by rw [pc.1, pc'.1]) fun Q => ?_
    by_cases hQ : Q.under (𝓞 D.host.F) = v
    · rw [pc.2.1 Q hQ, pc'.2.1 Q hQ]
    · rw [pc.2.2 Q hQ, pc'.2.2 Q hQ]
  have hev : ∀ Q, Φ e Q = if Q = w then 1 else 0 := fun Q => by
    split_ifs with hQ
    · rw [hQ]; exact hd.2.1
    · exact hd.2.2 Q hQ
  have hee : e * e = e := eq_of_ev hΦ (by rw [RingHom.map_mul, hd.1, zero_mul]) fun Q => by
    rw [ev_mul, hev Q]
    split_ifs <;> simp
  have key : (1 - e) * (1 - cA D e) * f = 0 := by
    rcases hp with ⟨-, hfe⟩ | ⟨hfe, -, -⟩
    · have hc2 : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
      rw [hfe]
      linear_combination (cA D e - 1) * hee + (e - 1) * hc2
    · rw [hfe]
      linear_combination (cA D e - 1) * hee
  have hfc : cA D f = f := by rw [hfε]; exact cA_algebraMap ε
  have hx' : f * ((x : AE D) - 1) = (x : AE D) - 1 := by rw [hfε]; exact hx
  have int1 : ∀ Q, Φ (x : AE D) Q ∈ Q.adicCompletionIntegers D.host.E := (hΦ.int _).1 h1
  have int2 : ∀ Q, Φ ((x⁻¹ : (AE D)ˣ) : AE D) Q ∈ Q.adicCompletionIntegers D.host.E := (hΦ.int _).1 h2
  obtain ⟨y, hy, hys⟩ := GlobalTheory.UnrOffLevels.exists_glue hee x
  have hxx : (x : AE D) * ((x⁻¹ : (AE D)ˣ) : AE D) = 1 := Units.mul_inv x
  have hyi : ((y⁻¹ : (AE D)ˣ) : AE D) = e * ((x⁻¹ : (AE D)ˣ) : AE D) + (1 - e) := by
    refine Units.inv_eq_of_mul_eq_one_right ?_
    rw [hy]
    linear_combination (e * e) * hxx + (2 - (x : AE D) - ((x⁻¹ : (AE D)ˣ) : AE D)) * hee
  have cut_int : ∀ z : AE D, (∀ Q, Φ z Q ∈ Q.adicCompletionIntegers D.host.E) →
      ∀ Q, Φ (e * z + (1 - e)) Q ∈ Q.adicCompletionIntegers D.host.E := fun z hz Q => by
    rw [ev_add, ev_mul, ev_sub, ev_one, hev Q]
    split_ifs
    · rw [one_mul, sub_self, add_zero]; exact hz Q
    · rw [zero_mul, sub_zero, zero_add]; exact one_mem _
  have iy1 : ∀ Q, Φ (y : AE D) Q ∈ Q.adicCompletionIntegers D.host.E := by rw [hy]; exact cut_int _ int1
  have iy2 : ∀ Q, Φ ((y⁻¹ : (AE D)ˣ) : AE D) Q ∈ Q.adicCompletionIntegers D.host.E := by
    rw [hyi]; exact cut_int _ int2
  have hνy : ν y = 1 := eq_one_of_supp hp hu y hys ((hΦ.int _).2 iy1) ((hΦ.int _).2 iy2)
  obtain ⟨z, hzdef⟩ : ∃ z : (AE D)ˣ, z = x * y⁻¹ := ⟨_, rfl⟩
  have iz1 : finPart D (z : AE D) ∈ intAE D := (hΦ.int _).2 fun Q => by
    rw [hzdef, Units.val_mul, ev_mul]; exact mul_mem (int1 Q) (iy2 Q)
  have iz2 : finPart D ((z⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D := (hΦ.int _).2 fun Q => by
    have hzi : (z⁻¹ : (AE D)ˣ) = y * x⁻¹ := by rw [hzdef, _root_.mul_inv_rev, inv_inv y]
    rw [hzi, Units.val_mul, ev_mul]; exact mul_mem (iy1 Q) (int2 Q)
  have hz1 : (z : AE D) - 1 = (1 - e) * f * ((x : AE D) - 1) := by
    have hzv : (z : AE D) = (x : AE D) * ((y⁻¹ : (AE D)ˣ) : AE D) := by rw [hzdef, Units.val_mul]
    rw [hzv, hyi]
    linear_combination e * hxx - (1 - e) * hx'
  have hcz : cA D (z : AE D) - 1 = (1 - cA D e) * f * (cA D (x : AE D) - 1) := by
    have := congrArg (cA D) hz1
    simp only [RingHom.map_sub, RingHom.map_one, RingHom.map_mul, hfc] at this
    exact this
  have hconj : ν (Units.map (cA D : AE D →* AE D) z) = (ν z)⁻¹ := GlobalTheory.ConjAdjWeil.chi_conj hR z
  obtain ⟨cz, hczdef⟩ : ∃ cz : (AE D)ˣ, cz = Units.map (cA D : AE D →* AE D) z := ⟨_, rfl⟩
  rw [← hczdef] at hconj
  have hcv : (cz : AE D) = cA D (z : AE D) := by rw [hczdef]; rfl
  have hcvi : ((cz⁻¹ : (AE D)ˣ) : AE D) = cA D ((z⁻¹ : (AE D)ˣ) : AE D) := by rw [hczdef, ← map_inv]; rfl
  have hνcz : ν cz = 1 := by
    refine eq_one_of_supp hp hu cz ?_ ?_ ?_
    · rw [hcv, hcz]
      linear_combination (-(cA D (x : AE D) - 1)) * key
    · rw [hcv]; exact finPart_cA_mem iz1
    · rw [hcvi]; exact finPart_cA_mem iz2
  have hνz : ν z = 1 := inv_eq_one.1 (hconj.symm.trans hνcz)
  have hxyz : x = y * z := by rw [hzdef, mul_comm x, mul_inv_cancel_left]
  rw [hxyz, map_mul, hνy, hνz, one_mul]

end GlobalTheory.UnramFromOnePrime

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedPlaceOfUnramifiedOnePrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_unramified_place_of_unramified_one_prime : ∀ (D : D7) (ν : (AE D)ˣ →* Circle), IsHeckeChar D ν → ResEta D ν 0 →
    ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε →
    ∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → GlobalTheory.LFun.UnrAt ν w → GlobalTheory.WeilParts.UnramAt ε ν := by
  first | exact @GlobalTheory.UnramFromOnePrime.unramAt_of_unrAt_one | exact GlobalTheory.UnramFromOnePrime.unramAt_of_unrAt_one | (intros; apply GlobalTheory.UnramFromOnePrime.unramAt_of_unrAt_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSelfDualLatticeSplitPlaceDictionary
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSelfDualLatticeSplitPlaceDictionary
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.SplitDictHerm

open GlobalTheory.EmbChart

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem tensAt_compFin (v : Pl (F := F)) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : tensAt E v (compFin F E v z) = atPlace v 1 • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul a x =>
    show atPlace v (evFin F v a) ⊗ₜ[F] x = atPlace v 1 • (a ⊗ₜ[F] x)
    rw [TensorProduct.smul_tmul', smul_eq_mul, atPlace_mul_right, one_mul]

theorem at_atPlace (v : Pl (F := F)) (c : Fv F v) : At (evFin F v) (atPlace v c) := fun u hu => by
  rw [smul_eq_mul, mul_comm, atPlace_mul_right, hu, mul_zero, map_zero]

theorem at_tensAt (v : Pl (F := F)) (y : Fv F v ⊗[F] E) : At (evFin F v) (tensAt E v y) := fun u hu => by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), smul_add, hx, hy, add_zero]
  | tmul a x =>
    rw [tensAt_tmul, TensorProduct.smul_tmul', at_atPlace v a u hu, TensorProduct.zero_tmul]

theorem eq_tensAt_of_at {v : Pl (F := F)} {z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)} (hz : At (evFin F v) z) : z = tensAt E v (compFin F E v z) := by
  rw [tensAt_compFin]
  have h1 : (1 - atPlace v 1) • z = 0 := hz _ (by rw [map_sub, map_one, evFin_atPlace, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1

theorem compFin_cA (σ : E →ₐ[F] E) (v : Pl (F := F)) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    compFin F E v (cA σ z) = sigR (Fv F v) σ (compFin F E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem piW_apply {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) (z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) : piW τ z = splitProj τ (compFin F E v z) := rfl

theorem piW_inclR {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) (x : E) : piW τ (inclR (AF F) x) = τ x := by
  show splitProj τ (evFin F v 1 ⊗ₜ[F] x) = τ x
  rw [map_one, splitProj_tmul, one_mul]

theorem piW_algebraMap {v : Pl (F := F)} (τ : E →ₐ[F] Fv F v) (a : AF F) :
    piW τ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a := by
  show splitProj τ (evFin F v a ⊗ₜ[F] 1) = evFin F v a
  rw [splitProj_tmul, map_one, mul_one]

theorem compFin_smul_inclR (v : Pl (F := F)) (a : AF F) (x : E) :
    compFin F E v (a • inclR (AF F) x) = evFin F v a ⊗ₜ[F] x := by
  show compFin F E v (a • ((1 : AF F) ⊗ₜ[F] x)) = _
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

theorem mem_latAt_iff {d : ℕ} (W : Spc F E d) (v : Pl (F := F)) (z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧ (fun j => compFin F E v (z j)) ∈ latLoc F W.L v := by
  constructor
  · intro hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, hav, y, hy, rfl⟩ := hz
      refine ⟨fun u hu => ?_, ?_⟩
      · rw [smul_smul, ← smul_eq_mul, ha u hu, zero_smul]
      · convert tmul_mem_latLoc hav hy using 1
        funext j
        exact compFin_smul_inclR v a (y j)
    | zero => exact ⟨fun u _ => smul_zero u, by convert zero_mem (latLoc F W.L v) using 1; funext j; simp⟩
    | add x y _ _ hx hy =>
      refine ⟨fun u hu => by rw [smul_add, hx.1 u hu, hy.1 u hu, add_zero], ?_⟩
      convert add_mem hx.2 hy.2 using 1
      funext j; simp
    | neg x _ hx =>
      refine ⟨fun u hu => by rw [smul_neg, hx.1 u hu, neg_zero], ?_⟩
      convert neg_mem hx.2 using 1
      funext j; simp
  · rintro ⟨hz, hl⟩
    have e : z = fun j => tensAt E v (compFin F E v (z j)) := funext fun j => eq_tensAt_of_at (fun u hu => by
      have := congrFun (hz u hu) j
      simpa using this)
    rw [e]
    refine latLoc_induction (p := fun Y => (fun j => tensAt E v (Y j)) ∈ GlobalTheory.InertSph.latAt W v)
      (fun c hc x hx => ?_) (by convert zero_mem (GlobalTheory.InertSph.latAt W v) using 1; funext j; simp) (fun Y Y' hY hY' => ?_)
      (fun Y hY => ?_) hl
    · refine AddSubgroup.subset_closure ⟨atPlace v c, at_atPlace v c, by rwa [evFin_atPlace], x, hx, ?_⟩
      funext j
      rw [tensAt_tmul]
      show _ = atPlace v c • ((1 : AF F) ⊗ₜ[F] x j)
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    · convert add_mem hY hY' using 1
      funext j; simp
    · convert neg_mem hY using 1
      funext j; simp

theorem mem_latAt_iff_bases {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {d : ℕ} (W : Spc F E d) {v : Pl (F := F)}
    (τ : E →ₐ[F] Fv F v) {b₁ b₂ : GL (Fin d) (Fv F v)} (hb₁ : IsSplitBasis τ W.L b₁)
    (hb₂ : IsSplitBasis (τ.comp σ) W.L b₂) (z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
      (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => piW τ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
      (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => piW (τ.comp σ) (z j)) i ∈
          v.adicCompletionIntegers F) := by
  have key : ∀ {ρ : E →ₐ[F] Fv F v} {b : GL (Fin d) (Fv F v)}, IsSplitBasis ρ W.L b → ∀ u : Fin d → Fv F v,
      (∀ i, (((b⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ u) i ∈ v.adicCompletionIntegers F) ↔
        u ∈ splitLat ρ W.L := by
    intro ρ b hb u
    rw [hb, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  rw [mem_latAt_iff, mem_latLoc_iff_split τ h, key hb₁, key hb₂]
  exact Iff.rfl

theorem hE_transpose (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    hE σ Jᵀ x y = form σ J y x := by
  simp only [hE, Formalism.UG.hform, form, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    (by intro a b c; ring : ∀ a b c : E, a * b * c = c * (b * a)) _ _ _

theorem split_dict_herm : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v →
    ∃ (π₁ π₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
      ((∀ z, π₁ (cA σ z) = π₂ z) ∧ (∀ z, π₂ (cA σ z) = π₁ z) ∧
      (∀ a : AF F, π₁ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ a : AF F, π₂ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) ∧
      (∀ x₁ x₂ : Fv F v, ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) ∧
      (∀ z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z ∈ GlobalTheory.InertSph.latAt V v ↔ At (evFin F v) z ∧
        (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
        (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
          v.adicCompletionIntegers F))) ∧
      ∃ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S.det ∧
        S.map (fun x => (x : Fv F v)) =
          (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F V.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) := by
  intro F E _ _ _ _ _ σ B d V r s hB hV v hv _
  have h := hB.cm
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := hv
  obtain ⟨τ, -⟩ := (existsUnique_splitPrime_eq h hPQ (HeightOneSpectrum.ext hP) (HeightOneSpectrum.ext hQ)).exists
  haveI := hV.lat
  obtain ⟨b₁, hb₁⟩ := exists_isSplitBasis τ V.L h
  have hdet : V.J.det ≠ 0 := by
    intro h0
    obtain ⟨u⟩ : Nonempty (InfinitePlace F) := inferInstance
    apply GlobalTheory.SigDet.det_ne_zero_of_hasSig _ _ _ _ (hV.sig u)
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have hdetT : V.Jᵀ.det ≠ 0 := by rwa [Matrix.det_transpose]
  have hJ : IsHermND σ V.Jᵀ := ⟨fun i j => hV.herm j i, hdetT⟩
  have hL : IsSelfDualAt σ V.Jᵀ V.L v := by
    refine (SelfDual.forall_isSelfDualAt_iff hdetT hV.lat).2 (fun y => ?_) v
    rw [hV.dual y]
    refine forall₂_congr fun x _ => ?_
    rw [hE_transpose]
    exact ⟨fun hi => ⟨⟨_, hi⟩, rfl⟩, fun ⟨c, hc⟩ => hc ▸ RingOfIntegers.isIntegral_coe c⟩
  have hb₂ := IsSplitBasis.dual h hJ hL hb₁
  refine ⟨piW τ, piW (τ.comp σ), b₁, dualConj 1 (splitGram hJ τ * b₁), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, 1, by simp, ?_⟩
  · intro z; rw [piW_apply, piW_apply, compFin_cA, splitProj_comp]
  · intro z; rw [piW_apply, piW_apply, compFin_cA, splitProj_comp_sigR h]
  · exact piW_algebraMap τ
  · exact piW_algebraMap _
  · intro z hz h1 h2
    have e : compFin F E v z = 0 := split_ext h τ (by rw [map_zero]; exact h1) (by rw [map_zero]; exact h2)
    rw [eq_tensAt_of_at hz, e, map_zero]
  · intro x₁ x₂
    refine ⟨tensAt E v ((splitAlgEquiv h τ).symm (x₁, x₂)), at_tensAt v _, ?_, ?_⟩
    · rw [piW_apply, compFin_tensAt, splitProj_symm]
    · rw [piW_apply, compFin_tensAt, splitProj_comp_symm]
  · exact mem_latAt_iff_bases h V τ hb₁ hb₂
  · have eJ : (incM F V.J).map (piW τ) = V.J.map τ := by
      exact Matrix.ext fun i j => piW_inclR τ (V.J i j)
    have eT : V.J.map τ = ((splitGram hJ τ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))ᵀ := by
      exact Matrix.ext fun i j => rfl
    have eG : V.J.map τ * (((splitGram hJ τ)⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v))ᵀ = 1 := by
      rw [eT, ← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one]
    rw [Matrix.map_one _ (by simp) (by simp), eJ, dualConj_one_val, mul_inv_rev, Units.val_mul, Matrix.transpose_mul,
      ← Matrix.mul_assoc, Matrix.mul_assoc _ (V.J.map τ), eG, Matrix.mul_one, ← Matrix.transpose_mul, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Matrix.transpose_one]

end GlobalTheory.SplitDictHerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSelfDualLatticeSplitPlaceDictionaryStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_selfDual_lattice_split_place_dictionary : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (V : Spc F E d) (r s : ℕ), B.IsGood σ → V.IsHerm σ B r s →
    ∀ (v : Pl (F := F)), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → PsiUnr B.ψ v →
    ∃ (π₁ π₂ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
      ((∀ z, π₁ (cA σ z) = π₂ z) ∧ (∀ z, π₂ (cA σ z) = π₁ z) ∧
      (∀ a : AF F, π₁ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ a : AF F, π₂ (algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) a) = evFin F v a) ∧
      (∀ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) ∧
      (∀ x₁ x₂ : Fv F v, ∃ z : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) ∧
      (∀ z : Fin d → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), z ∈ GlobalTheory.InertSph.latAt V v ↔ At (evFin F v) z ∧
        (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
        (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
          v.adicCompletionIntegers F))) ∧
      ∃ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S.det ∧
        S.map (fun x => (x : Fv F v)) =
          (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F V.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) := by
  first | exact @GlobalTheory.SplitDictHerm.split_dict_herm | exact GlobalTheory.SplitDictHerm.split_dict_herm | (intros; apply GlobalTheory.SplitDictHerm.split_dict_herm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateUnitaryAdelicIsoMapHaarFundamentalDomai
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateUnitaryAdelicIsoMapHaarFundamentalDomai
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.HaarConjImage

theorem map_isHaarFD : ∀ (D : D7) (S : HSp D) (c : D.host.E) {J : Matrix (Fin S.rank) (Fin S.rank) D.host.E} (hJ : J = c • S.gram), c ≠ 0 →
    ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), IsHaarFD S ν 𝓕 →
      (ν.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ)).IsHaarMeasure ∧
      IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ '' 𝓕)
        (ν.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ)) := by
  intro D S c J hJ hc ν 𝓕 h
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig S.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig S.gram
  have : BorelSpace (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J) := ⟨rfl⟩
  have c1 : Continuous (GlobalTheory.HaarConj.conjE S c hc hJ) := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.continuous_conjU S c hJ
  have c2 : Continuous (GlobalTheory.HaarConj.conjE S c hc hJ).symm := GlobalTheory.HaarConj.continuous_conjInv S c hc hJ
  haveI := h.1
  exact ⟨MulEquiv.isHaarMeasure_map ν (GlobalTheory.HaarConj.conjE S c hc hJ) c1 c2,
    GlobalTheory.HaarConj.isFundamentalDomain_image (GlobalTheory.HaarConj.conjE S c hc hJ) c1.measurable c2.measurable (GQ S) _
      (GlobalTheory.HaarConj.mem_ratU_iff S c hc hJ) ν 𝓕 h.2⟩

end GlobalTheory.HaarConjImage

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateUnitaryAdelicIsoMapHaarFundamentalDomaiStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugateUnitaryAdelicIso_map_haar_fundamentalDomain : ∀ (D : D7) (S : HSp D) (c : D.host.E) {J : Matrix (Fin S.rank) (Fin S.rank) D.host.E} (hJ : J = c • S.gram), c ≠ 0 →
    ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), IsHaarFD S ν 𝓕 →
      (ν.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ)).IsHaarMeasure ∧
      IsFundamentalDomain (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ratU D.sp.cm.sig J) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ '' 𝓕)
        (ν.map (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU S c hJ)) := by
  first | exact @GlobalTheory.HaarConjImage.map_isHaarFD | exact GlobalTheory.HaarConjImage.map_isHaarFD | (intros; apply GlobalTheory.HaarConjImage.map_isHaarFD <;> assumption)
end
end
