module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAddEquivSymplecticCoordsOrientedModel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OtherInstanceCharacterEqConjInstancePsiValueInte
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OtherInstanceCharacterEqConjInstancePsiValueInte
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

namespace GlobalTheory.SeeConjChar


open Formalism.L2.SG.HidaSetting in
theorem argT_finE_eq {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (κ : GA D (Yc D 0)) :
    argT X h (finE (Yc D 0) κ) = cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) h)
      (GlobalTheory.FlagBasis.chiArg X.B.I X.e0 X.f0 X.z0 X.bw X.bwd ((iotaX X h).toMulEquiv κ).2) := by
  obtain ⟨⟨I⟩⟩ := X
  dsimp only at h
  subst h
  have e := Formalism.L2.SG.EvalTIota.finE_brg_i (Formalism.IndefR.RationalEmbedding.iota D κ)
  have e2 : finE (Yc D 0) κ = ((Formalism.IndefR.RationalEmbedding.iota D κ).2.1 : GL (Fin (D.sp.Y 0).rank) (EAf D)) :=
    (congrArg (finE (D.sp.Y 0)) ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply κ)).symm.trans e
  rw [e2]
  rfl

theorem intAf_cast {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (c : TensorProduct X.B.I.F X.B.I.E (Formalism.MainNotions.S.Af X.B.I.F)) (hc : c ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E) :
    cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) h) c ∈
      Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨⟨I⟩⟩ := X
  dsimp only at h
  subst h
  exact hc

theorem chiS_cast {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (c : TensorProduct X.B.I.F X.B.I.E (Formalism.MainNotions.S.Af X.B.I.F)) :
    chiS X h (cast (congrArg (fun I : Formalism.MainNotions.S.AutInst => TensorProduct I.F I.E (Formalism.MainNotions.S.Af I.F)) h) c) =
      X.psiEf (Formalism.L2.SG.HidaSetting.divN X.B.I X.B.g c) := by
  rw [chiS_rfl]
  congr 2
  exact cast_cast _ _ c |>.trans (cast_eq _ c)

end GlobalTheory.SeeConjChar

namespace GlobalTheory.SeeConjChar

theorem argT_mem_intAf_and_chi2_eq_chiS_of_mem_Kset : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (κ : GA D (Yc D 0)), ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset → GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ X.chi2 ((iotaX X h).toMulEquiv κ).2 = GlobalTheory.SeeConjChar.chiS X h (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ)) := by
  intro D X h κ hK
  rw [argT_finE_eq X h κ]
  refine ⟨intAf_cast X h _ ?_, ?_⟩
  · obtain ⟨hef, hz0, hb⟩ := X.vectorsInLattice
    have hnxt : ∀ a, Formalism.L2.SG.HidaSetting.nxt X.e0 X.z0 a ∈ X.B.I.Lf := fun a => by
      unfold Formalism.L2.SG.HidaSetting.nxt
      split_ifs
      exacts [(hef _).1, hz0]
    unfold GlobalTheory.FlagBasis.chiArg
    refine Subring.add_mem _ (Subring.sum_mem _ fun a _ => ?_) (Subring.sum_mem _ fun i _ => ?_)
    · exact Formalism.L2.SG.Pf.unitaryCongruence.hA_int _ (hef a).2 (Formalism.L2.SG.Pf.unitaryCongruence.K_mv _ hK (hnxt a))
    · split_ifs with hi
      · exact Formalism.L2.SG.Pf.unitaryCongruence.hA_int _ (hb i).2 (Formalism.L2.SG.Pf.unitaryCongruence.K_mv _ hK (hb _).1)
      · exact Subring.zero_mem _
  · exact (chiS_cast X h _).symm

end GlobalTheory.SeeConjChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OtherInstanceCharacterEqConjInstancePsiValueInteStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.otherInstanceCharacter_eq_conjInstancePsiValue_integral : ∀ {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (κ : GA D (Yc D 0)), ((iotaX X h).toMulEquiv κ).2 ∈ X.B.I.Kset → GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ∧ X.chi2 ((iotaX X h).toMulEquiv κ).2 = GlobalTheory.SeeConjChar.chiS X h (GlobalTheory.SeeConjChar.argT X h (finE (Yc D 0) κ)) := by
  first | exact @GlobalTheory.SeeConjChar.argT_mem_intAf_and_chi2_eq_chiS_of_mem_Kset | exact GlobalTheory.SeeConjChar.argT_mem_intAf_and_chi2_eq_chiS_of_mem_Kset | (intros; apply GlobalTheory.SeeConjChar.argT_mem_intAf_and_chi2_eq_chiS_of_mem_Kset <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorRightIntertwinesHeisenbergDerivative
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorRightIntertwinesHeisenbergDerivative
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit

namespace GlobalTheory.HeisOrbit

open GlobalTheory.WeilM

theorem weil_heisDeriv_intertw {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ)
    (χX χW : Chr F E) (om : Rep σ X W) (hψ : IsStd ψ) (hW : M.IsWeil ψ χX χW om) (h : UA σ W.J)
    (Th : SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d))
    (hTh : ∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) f (Th f)) (u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (hu : At (evI F) u) (f f₁ : SInf F (Fin n × Fin d)) (hf : ActsD (evI F) (M.heisLine ψ u) f f₁) (y) :
    Th f₁ y = GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co (u * (mat h)ᵀ)).1
      (GlobalTheory.HeisOrbit.archCo M.co (u * (mat h)ᵀ)).2 (Th f) y := by
  obtain ⟨D, hD⟩ := GlobalTheory.T.archHeisenbergDerivatives_exist F E σ (Fin n) (Fin d) (Fin n × Fin d) ψ (incM F X.J) (incM F W.J) M.co hψ
  have hS := hW.isUSplitting
  have laws := GlobalTheory.RealLift.actsLaws F (Fin n × Fin d)

  have h1 : f₁ = D u f := by
    have hAD : ActsD (evI F) (M.heisLine ψ u) f (D u f) :=
      (laws f (D u f) (D u f)).1 (M.heisLine ψ u) (fun t => by funext x; simp [Model.heisLine, Darboux.rho, schr])
        (hD u hu f).1
    exact (laws f f₁ (D u f)).2.2.1 _ hf hAD

  have h2 : ∀ (f' : SInf F (Fin n × Fin d)) (g : (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ), g ∈ SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) →
      om (1, h) (pureA F f' g) = pureA F (Th f') g := by
    intro f' g hg
    have hr : Rest (evI F) (⇑f') (fun x => g (fun i => (x i).2)) := by
      refine ⟨fun x z hz => ?_, Submodule.subset_span ⟨f', g, hg, rfl⟩⟩
      show g _ = g _
      congr 1
      funext i
      show (x i).2 + (z i).2 = (x i).2
      rw [GlobalTheory.RealLift.fin_eq_zero_of_at hz, add_zero]
    exact hTh f' _ hr

  set g₀ : (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) → ℂ := (GlobalTheory.RealLift.intPts F (Fin n × Fin d)).indicator 1 with hg₀def
  have hg₀ : g₀ ∈ SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) := GlobalTheory.RealLift.indicator_intPts_mem_SB
  have hg₀0 : g₀ 0 = 1 := by rw [hg₀def, Set.indicator_of_mem GlobalTheory.RealLift.zero_mem_intPts]; rfl
  set x₀ := GlobalTheory.RealLift.ptAt y (0 : Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) with hx₀
  set u' := u * (mat h)ᵀ with hu'def
  have hu' : At (evI F) u' := fun a ha => by rw [hu'def, ← Matrix.smul_mul, hu a ha, Matrix.zero_mul]
  have hl := GlobalTheory.RealLift.eval_mem_adm (F := F) x₀
  have hl' := hS.adm (1, h) _ hl
  have dA := (hD u hu f).1 g₀ hg₀ _ hl'
  have dB := (hD u' hu' (Th f)).1 g₀ hg₀ _ hl
  have hfun : (fun t : ℝ => (LinearMap.proj x₀ ∘ₗ om (1, h)) (M.co.rho ψ (realAd F t • u) (pureA F f g₀))) =
      fun t : ℝ => (LinearMap.proj x₀ : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ)
        (M.co.rho ψ (realAd F t • u') (pureA F (Th f) g₀)) := by
    funext t
    rw [LinearMap.comp_apply, hS.impl (1, h) _ _ (Submodule.subset_span ⟨f, g₀, hg₀, rfl⟩), h2 f g₀ hg₀]
    congr 3
    simp [actAB, hu'def, mat, Matrix.smul_mul]
  change HasDerivAt (fun t : ℝ => (LinearMap.proj x₀ ∘ₗ om (1, h))
    (M.co.rho ψ (realAd F t • u) (pureA F f g₀))) _ _ at dA
  rw [hfun] at dA
  have e := dA.unique dB
  simp only [LinearMap.comp_apply, LinearMap.proj_apply, h2 _ g₀ hg₀, hx₀, GlobalTheory.RealLift.pureA_ptAt, hg₀0,
    mul_one] at e
  rw [h1, e, (hD u' hu' (Th f)).2]
  rfl

end GlobalTheory.HeisOrbit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilOperatorRightIntertwinesHeisenbergDerivativeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical
open GlobalTheory.HeisOrbit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_operator_right_intertwines_heisenberg_derivative : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsStd ψ → M.IsWeil ψ χX χW om → ∀ (h : UA σ W.J) (Th : SInf F (Fin n × Fin d) → SInf F (Fin n × Fin d)),
    (∀ f : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) f (Th f)) → ∀ u : Matrix (Fin n) (Fin d) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evI F) u →
    ∀ f f₁ : SInf F (Fin n × Fin d), ActsD (evI F) (M.heisLine ψ u) f f₁ → ∀ y,
      Th f₁ y = GlobalTheory.HeisOrbit.dOp (GlobalTheory.HeisOrbit.archCo M.co (u * (mat h)ᵀ)).1 (GlobalTheory.HeisOrbit.archCo M.co (u * (mat h)ᵀ)).2 (Th f) y := by
  first | exact @GlobalTheory.HeisOrbit.weil_heisDeriv_intertw | exact GlobalTheory.HeisOrbit.weil_heisDeriv_intertw | (intros; apply GlobalTheory.HeisOrbit.weil_heisDeriv_intertw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearTensorPolyVacuumPureTensors
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearTensorPolyVacuumPureTensors
open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HoweGlobal.TensorMap

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F : Type} [Field F] [NumberField F]

theorem finite_nonint {κ : Type} [Finite κ] (x : κ → AF F) :
    {w : Pl F | ¬ ∀ i, evFin F w (x i) ∈ w.adicCompletionIntegers F}.Finite := by
  have h : ∀ i, {w : Pl F | evFin F w (x i) ∉ w.adicCompletionIntegers F}.Finite := fun i =>
    Filter.eventually_cofinite.1 (x i).2.2
  refine (Set.finite_iUnion h).subset ?_
  intro w hw
  push_neg at hw
  obtain ⟨i, hi⟩ := hw
  exact Set.mem_iUnion.2 ⟨i, hi⟩

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {W : Spc F E d}


open Classical in
def vacOff (M : Model σ Y W) (T : Finset (Pl F)) (x : Fin n × Fin d → AF F) : ℂ :=
  ∏ᶠ w, if w ∈ T then (1 : ℂ) else M.vac w fun i => evFin F w (x i)

def prodT (T : Finset (Pl F)) (x : Fin n × Fin d → AF F) :
    (Π v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) →ₘₗ[ℂ] ℂ :=
  (MultilinearMap.mkPiAlgebra ℂ T ℂ).compLinearMap fun v =>
    (LinearMap.proj (fun i => evFin F v.1 (x i)) : ((Fin n × Fin d → Fv F v.1) → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (SB _).subtype

theorem prodT_apply (T : Finset (Pl F)) (x : Fin n × Fin d → AF F) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    prodT T x φ = ∏ v : T, (φ v : (Fin n × Fin d → Fv F v.1) → ℂ) fun i => evFin F v.1 (x i) := by
  simp [prodT]

def multi (M : Model σ Y W) (T : Finset (Pl F)) (f : SInf F (Fin n × Fin d)) :
    (Π v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) →ₘₗ[ℂ] ((Fin n × Fin d → AF F) → ℂ) :=
  MultilinearMap.pi fun x => (f (fun i => evI F (x i)) * vacOff M T x) • prodT T x

theorem multi_apply (M : Model σ Y W) (T : Finset (Pl F)) (f : SInf F (Fin n × Fin d))
    (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) (x : Fin n × Fin d → AF F) :
    multi M T f φ x = f (fun i => evI F (x i)) * vacOff M T x * prodT T x φ := by
  simp [multi]

def multiL (M : Model σ Y W) (T : Finset (Pl F)) :
    SInf F (Fin n × Fin d) →ₗ[ℂ]
      ((Π v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) →ₘₗ[ℂ] ((Fin n × Fin d → AF F) → ℂ)) where
  toFun := multi M T
  map_add' f g := by
    ext φ x
    simp only [multi_apply, MultilinearMap.add_apply, Pi.add_apply, SchwartzMap.add_apply]
    ring
  map_smul' c f := by
    ext φ x
    simp only [multi_apply, MultilinearMap.smul_apply, Pi.smul_apply, SchwartzMap.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring


open Classical in
theorem finprod_split (M : Model σ Y W)
    (hstd : ∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (T : Finset (Pl F)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1)))
    (φ' : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ)
    (h1 : ∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) (h2 : ∀ v ∉ T, φ' v = M.vac v) (x : Fin n × Fin d → AF F) :
    ∏ᶠ w, φ' w (fun i => evFin F w (x i)) = vacOff M T x * prodT T x φ := by
  set ρ : Pl F → ℂ := fun w => if w ∈ T then (1 : ℂ) else M.vac w fun i => evFin F w (x i) with hρdef
  set θ : Pl F → ℂ := fun w => if w ∈ T then φ' w (fun i => evFin F w (x i)) else 1 with hθdef
  have e : (fun w => φ' w (fun i => evFin F w (x i))) = fun w => θ w * ρ w := by
    funext w
    by_cases hw : w ∈ T
    · simp [θ, ρ, hw]
    · simp [θ, ρ, hw, h2 w hw]
  have hρ : (Function.mulSupport ρ).Finite := by
    refine ((Filter.eventually_cofinite.1 hstd).union (finite_nonint x)).subset ?_
    intro w hw
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    apply hw
    by_cases hwT : w ∈ T
    · simp [ρ, hwT]
    · simp only [ρ, hwT, if_false, hc.1]
      exact Set.indicator_of_mem (s := {x : Fin n × Fin d → Fv F w | ∀ i, x i ∈ w.adicCompletionIntegers F}) hc.2 1
  have hθ : Function.mulSupport θ ⊆ (T : Set (Pl F)) := by
    intro w hw
    by_contra hc
    exact hw (by simp [θ, show w ∉ T from hc])
  rw [e, finprod_mul_distrib (T.finite_toSet.subset hθ) hρ, mul_comm]
  congr 1
  rw [finprod_eq_prod_of_mulSupport_subset θ hθ, prodT_apply, ← Finset.prod_coe_sort T]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp [θ, v.2, h1 v.1 v.2]

def tensL (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w) (T : Finset (Pl F)) :
    ↥(M.Pol ψ emb) ⊗[ℂ] (⨂[ℂ] v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) →ₗ[ℂ]
      ((Fin n × Fin d → AF F) → ℂ) :=
  TensorProduct.lift ((PiTensorProduct.lift.toLinearMap ∘ₗ multiL M T) ∘ₗ (M.Pol ψ emb).subtype)

theorem tensL_tmul (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, EmbOver E w)
    (T : Finset (Pl F)) (f : ↥(M.Pol ψ emb)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1))) :
    tensL M ψ emb T (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = multi M T (f : SInf F (Fin n × Fin d)) φ := by
  simp [tensL, multiL]

theorem exists_tensL : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y W)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w),
    (∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ L : ↥(M.Pol ψ emb) ⊗[ℂ] (⨂[ℂ] v : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1))) →ₗ[ℂ]
        ((Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ),
      (∀ (f : ↥(M.Pol ψ emb)) (φ : ∀ v : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1)))
        (φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = M.vac v) →
        L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ') ∧
      GlobalTheory.HoweGlobal.algAt M ψ emb T ≤ LinearMap.range L := by
  intro F E _ _ _ _ _ σ n d Y W M ψ emb hstd T
  have hchar : ∀ (f : ↥(M.Pol ψ emb)) (φ : ∀ v : T, ↥(SB (Fin n × Fin d → Fv F v.1)))
      (φ' : ∀ v : Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = M.vac v) →
      tensL M ψ emb T (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : SInf F (Fin n × Fin d)) φ' := by
    intro f φ φ' h1 h2
    funext x
    rw [tensL_tmul, multi_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, finprod_split M hstd T φ φ' h1 h2 x, mul_assoc]
  refine ⟨tensL M ψ emb T, hchar, Submodule.span_le.2 ?_⟩
  rintro Φ ⟨f, φ, hf, hφ, hv, rfl⟩
  exact ⟨⟨f, hf⟩ ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ (fun v : T => ⟨φ v.1, hφ v.1⟩),
    hchar ⟨f, hf⟩ _ φ (fun _ _ => rfl) hv⟩

end GlobalTheory.HoweGlobal.TensorMap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLinearTensorPolyVacuumPureTensorsStatement
open NumberField IsDedekindDomain
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_tensor_polyVacuum_pureTensors : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y W)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w),
    (∀ᶠ v in Filter.cofinite, M.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) →
    ∀ T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)),
    ∃ L : ↥(M.Pol ψ emb) ⊗[ℂ] (⨂[ℂ] v : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1))) →ₗ[ℂ]
        ((Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ),
      (∀ (f : ↥(M.Pol ψ emb)) (φ : ∀ v : T, ↥(GlobalTheory.WeilM.SB (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v.1)))
        (φ' : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (Fin n × Fin d → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ),
        (∀ v (h : v ∈ T), φ' v = φ ⟨v, h⟩) → (∀ v ∉ T, φ' v = M.vac v) →
        L (f ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ') ∧
      GlobalTheory.HoweGlobal.algAt M ψ emb T ≤ LinearMap.range L := by
  first | exact @GlobalTheory.HoweGlobal.TensorMap.exists_tensL | exact GlobalTheory.HoweGlobal.TensorMap.exists_tensL | (intros; apply GlobalTheory.HoweGlobal.TensorMap.exists_tensL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointExchangeLawsThetaHeisenberg
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointExchangeLawsThetaHeisenberg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ExchPf

open GlobalTheory.PairLift GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger

variable {D : D7}

def withForm (V : HSp D) (h : V.V →ₗ⋆[D.host.E] V.V →ₗ[D.host.E] D.host.E) (e : h = V.hT) : HSp D :=
  { V with hT := h, herm := e ▸ V.herm, nondeg := e ▸ V.nondeg, baseLattice_isUnimodular := e ▸ V.baseLattice_isUnimodular }

theorem HR_withForm (V : HSp D) (h : V.V →ₗ⋆[D.host.E] V.V →ₗ[D.host.E] D.host.E) (e : h = V.hT) :
    HR (AF D.host.F) D.sp.cm.sig V.gram = HR (AF D.host.F) D.sp.cm.sig (withForm V h e).gram := by
  subst e; rfl

theorem datum_withForm {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χ χ' : (AE D)ˣ →* Circle}
    (h : B.V →ₗ⋆[D.host.E] B.V →ₗ[D.host.E] D.host.E) (e : h = B.hT)
    (ω : GA D A × GA D (withForm B h e) →* Module.End ℂ (WO A (withForm B h e) → ℂ))
    (hd : IsWeilDatumO ψ A (withForm B h e) χ χ' ω) :
    IsWeilDatumO ψ A B χ χ' (ω.comp ((MonoidHom.id (GA D A)).prodMap (MulEquiv.subgroupCongr (HR_withForm B h e)).toMonoidHom)) := by
  subst e
  exact hd

theorem datum_negneg {ψ : AddChar (AF D.host.F) ℂ} {A B : HSp D} {χ χ' : (AE D)ˣ →* Circle}
    (ω : GA D A × GA D (negSp (negSp B)) →* Module.End ℂ (WO A (negSp (negSp B)) → ℂ))
    (hd : IsWeilDatumO ψ A (negSp (negSp B)) χ χ' ω) :
    IsWeilDatumO ψ A B χ χ' (ω.comp ((MonoidHom.id (GA D A)).prodMap ((negGA B).trans (negGA (negSp B))).toMonoidHom)) := by
  have key := datum_withForm (ψ := ψ) (A := A) (B := B) (χ := χ) (χ' := χ') (-(-B.hT)) (neg_neg _) ω hd
  have e : ((negGA B).trans (negGA (negSp B))).toMonoidHom =
      (MulEquiv.subgroupCongr (HR_withForm B (-(-B.hT)) (neg_neg _))).toMonoidHom := MonoidHom.ext fun _ => rfl
  rw [e]
  exact key

theorem exch_eq_cj (A B : HSp D) (f : WO A B → ℂ) : exch A B f = cj id (dag A B f) := by
  funext x; simp [GlobalTheory.CoreOnto.exch, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dag]

theorem theta_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D) (f : WO A B → ℂ) :
    IsThetaFunO ψ A B f ↔ IsThetaFunO ψ (negSp B) A (exch A B f) := by
  have hAB := GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B
  have hBA := GlobalTheory.AdjLawPf.adjLaw D ψ hψ B A
  rw [exch_eq_cj, ((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ B A).1 (dag A B f)).2]
  exact ⟨hAB.theta f, fun h => by simpa only [GlobalTheory.WeilConj.dag_dag hAB] using hBA.theta _ h⟩

theorem heis_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D) (x : WO (negSp B) A)
    (f : WO A B → ℂ) : heisO ψ (negSp B) A x (exch A B f) = exch A B (heisO ψ A B (adjO A B x) f) := by
  have hAB := GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B
  rw [exch_eq_cj, exch_eq_cj, ((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ B A).2 x (dag A B f)).2, hAB.Heisenberg₂]

theorem sympl_negB (A B : HSp D) (x x' : WO B A) : symplO (negSp B) A x x' = -symplO B A x x' := by
  have e : hO (negSp B) A x x' = -hO B A x x' := by
    unfold hO
    rw [negSp_gram, GlobalTheory.CjNeg.inv_neg_mat]
    simp only [Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
  unfold symplO
  rw [e, mul_neg, map_neg]

theorem sympl_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D) (x x' : WO (negSp B) A) :
    symplO (negSp B) A x x' = symplO A B (adjO A B x) (adjO A B x') := by
  rw [(GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B).sympl, sympl_negB]

theorem bij_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D) :
    Function.Bijective (adjO A B) :=
  Function.bijective_iff_has_inverse.2 ⟨adjO B A, fun x => (GlobalTheory.AdjLawPf.adjLaw D ψ hψ B A).invol x,
    fun y => (GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B).invol y⟩

theorem covol_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D)
    (m : Measure (Mx D B.rank A.rank)) (X : Set (Mx D B.rank A.rank)) (hX : IsCovolOne (ratL B A) m X) :
    ∃ m' X', IsCovolOne (ratL A (negSp B)) m' X' ∧ ∀ f f' : WO A B → ℂ,
      ∫ w in X, f w * starRingEnd ℂ (f' w) ∂m = ∫ w in X', exch A B f w * starRingEnd ℂ (exch A B f' w) ∂m' := by
  have hAB := GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B
  have hBA := GlobalTheory.AdjLawPf.adjLaw D ψ hψ B A
  obtain ⟨hμ, h𝓕, h1⟩ := hX
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.MixModel.lattice_Mx D B.rank A.rank
  obtain ⟨j1, j2, j3, j4, -⟩ := GlobalTheory.MixModel.lattice_Mx D A.rank B.rank
  haveI : BorelSpace (WO A B) := ⟨rfl⟩
  haveI : BorelSpace (WO B A) := ⟨rfl⟩
  let eA : WO A B ≃+ WO B A :=
    { toFun := adjO B A
      invFun := adjO A B
      left_inv := fun x => hAB.invol x
      right_inv := fun y => hBA.invol y
      map_add' := hBA.add }
  let eH : WO A B ≃ₜ WO B A := ⟨eA.toEquiv, hBA.cont, hAB.cont⟩
  let eM : WO A B ≃ᵐ WO B A := eH.toMeasurableEquiv
  have hHaar : (m.map eM).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map m eA hBA.cont hAB.cont
  have hmp : MeasurePreserving eM m (m.map eM) := ⟨eM.measurable, rfl⟩
  have hmp' : MeasurePreserving eM.symm (m.map eM) m := MeasurePreserving.symm eM hmp
  let eG : ratL B A → ratL A B := fun g => ⟨adjO B A g, (hBA.rat g).2 g.2⟩
  have hbij : Function.Bijective eG := by
    refine ⟨fun g g' hg => ?_, fun g => ⟨⟨adjO A B g, (hAB.rat g).2 g.2⟩, Subtype.ext (hBA.invol g)⟩⟩
    have e := congrArg (fun x : ratL A B => adjO A B (x : WO B A)) hg
    simp only [eG, hAB.invol] at e
    exact Subtype.ext e
  have hF : IsAddFundamentalDomain (ratL A B) (eM.symm ⁻¹' X) (m.map eM) := by
    refine h𝓕.preimage_of_equiv hmp'.quasiMeasurePreserving hbij fun g x => ?_
    show adjO A B (adjO B A g + x) = (g : WO A B) + adjO A B x
    rw [hAB.add, hAB.invol]
  have hpre : eM ⁻¹' (eM.symm ⁻¹' X) = X := by
    ext a; simp
  refine ⟨m.map eM, eM.symm ⁻¹' X, ⟨hHaar, hF, ?_⟩, fun f f' => ?_⟩
  · rw [MeasurableEquiv.map_apply, hpre, h1]
  · symm
    rw [MeasurableEquiv.restrict_map, integral_map_equiv, hpre]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show f (adjO A B (adjO B A x)) * starRingEnd ℂ (f' (adjO A B (adjO B A x))) = _
    rw [hAB.invol]

theorem weil_exch {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (A B : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (ω : GA D (negSp B) × GA D A →* Module.End ℂ (WO (negSp B) A → ℂ)) (hω : IsWeilDatumO ψ (negSp B) A χS χT ω) :
    ∃ ω', IsWeilDatumO ψ A B χT⁻¹ χS⁻¹ ω' ∧ Exch ψ ω ω' := by
  have hAB := GlobalTheory.AdjLawPf.adjLaw D ψ hψ A B
  have hBA := GlobalTheory.AdjLawPf.adjLaw D ψ hψ B A
  have h1 := GlobalTheory.ConjWeil.weil_conjSource D ψ (negSp B) A χS χT ω hω
  obtain ⟨ω₃, h3, R⟩ := GlobalTheory.WeilConj.exists_conj_weilDatum D ψ (negSp (negSp B)) A χS⁻¹ χT⁻¹ (conjSource ω) h1
  refine ⟨_, datum_negneg ω₃ h3, fun f _ g h => ?_⟩
  have hadj : ∀ y : WO A B, adjO (negSp (negSp B)) A y = adjO B A y := by
    intro y; simp only [adjO, negSp_gram, neg_neg]
  have hf : dag (negSp (negSp B)) A (cj id (exch A B f)) = f := by
    funext y
    simp only [dag, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id, GlobalTheory.CoreOnto.exch, Complex.conj_conj, hadj, hAB.invol]
  have R' := R ((negGA (negSp B)) (negGA B h)) g (cj id (exch A B f))
  rw [hf] at R'
  show _ = exch A B (ω₃ (g, (negGA (negSp B)) (negGA B h)) f)
  rw [R', GlobalTheory.ConjWeil.conjSource_apply]
  simp only [MulEquiv.symm_apply_apply, GlobalTheory.ConjWeil.cj_id_cj_id]
  funext x
  simp only [GlobalTheory.CoreOnto.exch, dag, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, id, Complex.conj_conj, hadj, hBA.invol]

theorem exchLaw : ∀ D : D7, ExchLaw D := by
  intro D ψ A B hψ
  exact ⟨theta_exch hψ A B, heis_exch hψ A B, sympl_exch hψ A B, bij_exch hψ A B,
    fun m X hX => covol_exch hψ A B m X hX, fun χS χT ω hω => weil_exch hψ A B χS χT ω hω⟩

end GlobalTheory.ExchPf

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointExchangeLawsThetaHeisenbergStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjointExchange_laws_thetaHeisenberg : ∀ D : D7, ExchLaw D := by
  first | exact @GlobalTheory.ExchPf.exchLaw | exact GlobalTheory.ExchPf.exchLaw | (intros; apply GlobalTheory.ExchPf.exchLaw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChiGridNumericalDataRealPlaceGapSizeBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChiGridNumericalDataRealPlaceGapSizeBounds
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridReal

open GlobalTheory.SignedHC

theorem num_real_bounds : ∀ (D : D7) (large₂ : SizeData₂ D), SizeRows large₂ → ∀ τ : D.what₂.Tau, (∀ i, 2 ≤ i → i < (GlobalTheory.ChiGrid.num D 1 τ).k → (GlobalTheory.ChiGrid.num D 1 τ).v (i + 1) + 2 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v i) ∧ 2 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v (GlobalTheory.ChiGrid.num D 1 τ).k + (GlobalTheory.ChiGrid.num D 1 τ).b 1 ∧ (∀ l, 1 ≤ l → l < (GlobalTheory.ChiGrid.num D 1 τ).m → ((GlobalTheory.ChiGrid.num D 1 τ).b l : ℝ) + 1000 * ((D.R.r : ℝ) + 1) ^ 3 ≤ (GlobalTheory.ChiGrid.num D 1 τ).b (l + 1)) ∧ 1000 * ((D.R.r : ℝ) + 1) ^ 3 ≤ (GlobalTheory.ChiGrid.num D 1 τ).ga ∧ 0 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v (GlobalTheory.ChiGrid.num D 1 τ).k ∧ 0 < (GlobalTheory.ChiGrid.num D 1 τ).b 1 ∧ (((GlobalTheory.ChiGrid.num D 1 τ).a 0 : ℚ) : ℝ) ≤ large₂.sc.b ^ 2 ∧ ((GlobalTheory.ChiGrid.num D 1 τ).b (GlobalTheory.ChiGrid.num D 1 τ).m : ℝ) ≤ large₂.sc.b ^ 2 ∧ 1 ≤ large₂.sc.b ∧ 8 * ((D.R.r : ℝ) + 1) ≤ large₂.sc.b ^ 4 := by
  intro D large₂ hS τ
  obtain ⟨⟨Pm, -, -⟩, -, -, hm44, -, -, -, -, -, -, -, hSb, hpos, -⟩ := hS
  set G := GlobalTheory.ChiGrid.num D 1 τ with hG
  have hk : G.k = D.R.k := rfl
  have hm : G.m = D.R.m := rfl
  have hga : G.ga = GlobalTheory.ChiGrid.gap D 1 := rfl
  obtain ⟨hv0, hb0, -⟩ := GridData.ofHCParam_spec (D.hc τ) (GlobalTheory.ChiGrid.sLen D) (GlobalTheory.ChiGrid.gap D 1)
    (GlobalTheory.ChiGrid.cen D 1 τ)
  have hv : ∀ i : Fin (D.R.k - 1), (((D.hc τ).v i : ℚ) : ℝ) = ((G.v (i.1 + 2) : ℤ) : ℝ) := by
    intro i
    have e : (D.hc τ).v i = ((G.v (i.1 + 2) : ℤ) : ℚ) := hv0 i
    rw [e, Rat.cast_intCast]
  have hb : ∀ l : Fin D.R.m, (((D.hc τ).b l : ℚ) : ℝ) = ((G.b (l.1 + 1) : ℤ) : ℝ) := by
    intro l
    have e : (D.hc τ).b l = ((G.b (l.1 + 1) : ℤ) : ℚ) := hb0 l
    rw [e, Rat.cast_intCast]
  have hm2 := D.R.two_le_m
  have hmk := D.R.m_add_three_le_k
  have hr6 : 6 ≤ D.R.r := by unfold Ranks.r; omega
  set X : ℝ := (D.R.r : ℝ) + 1 with hX
  have hX7 : 7 ≤ X := by
    have : (6 : ℝ) ≤ D.R.r := by exact_mod_cast hr6
    linarith
  have hX3 : 0 ≤ X ^ 3 := by positivity

  have hgapS : (2 : ℝ) ≤ Formalism.BasicNotions.LevelStarExponents.gapS D Pm.Cgap := by
    unfold Formalism.BasicNotions.LevelStarExponents.gapS
    have h1 : 0 ≤ Pm.Cgap * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 4 := by
      have := Pm.Cgap_pos; positivity
    have hN : (2 : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
      have : 2 ≤ D.R.N D.R.m := by unfold Ranks.N; exact le_trans (by omega) (Nat.le_add_right _ _)
      exact_mod_cast this
    have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ D.R.m))
    nlinarith

  have hgap : 1000 * X ^ 3 ≤ (G.ga : ℝ) := by
    have hB := ((GlobalTheory.ChiGrid.gapBound_iff D 1 (GlobalTheory.ChiGrid.gap D 1)).2 le_rfl).1
    have hn : ((GlobalTheory.ChiGrid.nRk D : ℕ) : ℝ) = X := by unfold GlobalTheory.ChiGrid.nRk; push_cast; rfl
    rw [hn] at hB
    have h1 : 0 ≤ (1 : ℝ) * (GlobalTheory.ChiGrid.bigN D : ℝ) ^ 3 := by positivity
    have h2 : 0 ≤ (1 : ℝ) * X ^ 3 * Real.sqrt (GlobalTheory.ChiGrid.cloudLen D) := by
      have := Real.sqrt_nonneg (GlobalTheory.ChiGrid.cloudLen D : ℝ); positivity
    have h4 : (1000 : ℝ) ≤ X ^ 4 := by
      have : (7 : ℝ) ^ 4 ≤ X ^ 4 := pow_le_pow_left₀ (by norm_num) hX7 4
      norm_num at this; linarith
    have h7 : 1000 * X ^ 3 ≤ X ^ 7 := by
      have : X ^ 7 = X ^ 4 * X ^ 3 := by ring
      rw [this]; exact mul_le_mul_of_nonneg_right h4 hX3
    rw [hga]; linarith
  have hX1 : (1 : ℝ) ≤ 1000 * X ^ 3 := by
    have : (1 : ℝ) ≤ X ^ 3 := one_le_pow₀ (by linarith)
    linarith

  have hga0 : (0 : ℝ) ≤ (G.ga : ℝ) := by positivity
  have hSb' : large₂.Sc + ((D.R.m : ℝ) + 1) * (G.ga : ℝ) + 1 / 2 ≤ large₂.sc.b := by rw [hga]; exact hSb
  have hSc := large₂.Sc_pos
  have hbga : (G.ga : ℝ) ≤ large₂.sc.b := by
    have : (G.ga : ℝ) ≤ ((D.R.m : ℝ) + 1) * (G.ga : ℝ) := by
      have : (0 : ℝ) ≤ (D.R.m : ℝ) := by positivity
      nlinarith
    linarith
  have hb1 : (1 : ℝ) ≤ large₂.sc.b := by linarith
  have hbsq : large₂.sc.b ≤ large₂.sc.b ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hb1, ?_⟩
  ·
    intro i hi1 hi2
    obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hi1
    have hlt : a + 1 < D.R.k - 1 := by rw [hk] at hi2; omega
    have h := (Pm.sig_gaps τ).1 a hlt
    have e := hv ⟨a, by omega⟩
    have e' := hv ⟨a + 1, hlt⟩
    push_cast at h
    simp only at e e'
    rw [e, e'] at h
    have : ((G.v (a + 2 + 1) : ℤ) : ℝ) + 2 ≤ ((G.v (a + 2) : ℤ) : ℝ) := by
      rw [show a + 2 + 1 = a + 1 + 2 by omega]; linarith
    exact_mod_cast this
  ·
    have h := (Pm.sig_gaps τ).2.1 (by omega) (by omega)
    have e := hv ⟨D.R.k - 2, by omega⟩
    have e' := hb ⟨0, by omega⟩
    push_cast at h
    simp only at e e'
    rw [e, e'] at h
    rw [hk, show D.R.k = D.R.k - 2 + 2 by omega]
    have : (2 : ℝ) ≤ ((G.v (D.R.k - 2 + 2) : ℤ) : ℝ) + ((G.b (0 + 1) : ℤ) : ℝ) := by linarith
    exact_mod_cast this
  ·
    intro l hl1 hl2
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' hl1
    have hlt : j + 1 < D.R.m := by rw [hm] at hl2; omega
    have h := (Pm.nodes_gap τ j hlt).1
    have hf := Pm.heightBound_ge_rank_cubic
    have e := hb ⟨j + 1, hlt⟩
    have e' := hb ⟨j, by omega⟩
    push_cast at h
    simp only at e e'
    rw [e, e'] at h
    have hY : 10 * X ≤ (D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1) := by
      have h44 : (44 : ℝ) ≤ D.R.m := by exact_mod_cast hm44
      have hk0 : (0 : ℝ) ≤ D.R.k := by positivity
      have ht0 : (0 : ℝ) ≤ D.R.t := by positivity
      nlinarith
    have hY3 : (10 * X) ^ 3 ≤ ((D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1)) ^ 3 :=
      pow_le_pow_left₀ (by linarith) hY 3
    have ht0 : (0 : ℝ) ≤ D.R.t := by positivity
    have : ((G.b (j + 1) : ℤ) : ℝ) + 1000 * X ^ 3 ≤ ((G.b (j + 1 + 1) : ℤ) : ℝ) := by nlinarith
    exact this
  · exact hgap
  ·
    have h := (large₂.cloud_v τ ⟨D.R.k - 2, by omega⟩).1
    rw [hv] at h
    simp only at h
    rw [hk, show D.R.k = D.R.k - 2 + 2 by omega]
    exact_mod_cast h
  ·
    have h := (hpos τ ⟨0, by omega⟩).1
    have e := hb ⟨0, by omega⟩
    have h' : (0 : ℝ) < (((D.hc τ).b ⟨0, by omega⟩ : ℚ) : ℝ) := by exact_mod_cast h
    rw [e] at h'
    exact_mod_cast h'
  ·
    have h := (large₂.cloud_v τ ⟨0, by omega⟩).2
    rw [hv] at h
    simp only [zero_add] at h
    have e : (((G.a 0 : ℚ)) : ℝ) = ((G.v 2 : ℤ) : ℝ) + 1 / 2 + ((D.R.m : ℝ) + 1) * (G.ga : ℝ) := by
      unfold GridData.a; rw [hm]; push_cast; ring
    rw [e]; linarith
  ·
    have h := large₂.b_le τ ⟨D.R.m - 1, by omega⟩
    rw [hb] at h
    simp only at h
    rw [hm, show D.R.m = D.R.m - 1 + 1 by omega]
    exact h
  ·
    have h8 : 8 * X ≤ 1000 * X ^ 3 := by
      have hX2 : (1 : ℝ) ≤ X ^ 2 := one_le_pow₀ (by linarith)
      have : X ^ 3 = X * X ^ 2 := by ring
      have hXX : X ≤ X ^ 3 := by rw [this]; nlinarith
      linarith
    have hb4 : large₂.sc.b ≤ large₂.sc.b ^ 4 := by
      have : large₂.sc.b ^ 4 = large₂.sc.b * large₂.sc.b ^ 3 := by ring
      rw [this]
      have : (1 : ℝ) ≤ large₂.sc.b ^ 3 := one_le_pow₀ hb1
      nlinarith
    linarith

end GlobalTheory.GridReal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChiGridNumericalDataRealPlaceGapSizeBoundsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chiGridNumericalData_realPlace_gap_size_bounds : ∀ (D : D7) (large₂ : SizeData₂ D), SizeRows large₂ → ∀ τ : D.what₂.Tau, (∀ i, 2 ≤ i → i < (GlobalTheory.ChiGrid.num D 1 τ).k → (GlobalTheory.ChiGrid.num D 1 τ).v (i + 1) + 2 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v i) ∧ 2 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v (GlobalTheory.ChiGrid.num D 1 τ).k + (GlobalTheory.ChiGrid.num D 1 τ).b 1 ∧ (∀ l, 1 ≤ l → l < (GlobalTheory.ChiGrid.num D 1 τ).m → ((GlobalTheory.ChiGrid.num D 1 τ).b l : ℝ) + 1000 * ((D.R.r : ℝ) + 1) ^ 3 ≤ (GlobalTheory.ChiGrid.num D 1 τ).b (l + 1)) ∧ 1000 * ((D.R.r : ℝ) + 1) ^ 3 ≤ (GlobalTheory.ChiGrid.num D 1 τ).ga ∧ 0 ≤ (GlobalTheory.ChiGrid.num D 1 τ).v (GlobalTheory.ChiGrid.num D 1 τ).k ∧ 0 < (GlobalTheory.ChiGrid.num D 1 τ).b 1 ∧ (((GlobalTheory.ChiGrid.num D 1 τ).a 0 : ℚ) : ℝ) ≤ large₂.sc.b ^ 2 ∧ ((GlobalTheory.ChiGrid.num D 1 τ).b (GlobalTheory.ChiGrid.num D 1 τ).m : ℝ) ≤ large₂.sc.b ^ 2 ∧ 1 ≤ large₂.sc.b ∧ 8 * ((D.R.r : ℝ) + 1) ≤ large₂.sc.b ^ 4 := by
  first | exact @GlobalTheory.GridReal.num_real_bounds | exact GlobalTheory.GridReal.num_real_bounds | (intros; apply GlobalTheory.GridReal.num_real_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalVectorNormAdelicPointTwoModelsEq
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalVectorNormAdelicPointTwoModelsEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormDict

theorem norm_dict : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : Fr V) (fr : Formalism.IndefR.Eqv.UI.Frames D V), (∀ τ, fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹) → ∀ (x : (Formalism.IndefR.Eqv.UI.instV fr).GA) (w : Fin V.rank → D.host.E), ∏ v, Real.sqrt (∑ i, ‖(Formalism.MainNotions.S.uMat (x.1 v)⁻¹ *ᵥ (((Formalism.IndefR.Eqv.UI.instV fr).P v)⁻¹ *ᵥ fun j => (Formalism.IndefR.Eqv.UI.instV fr).φ v (w j))) i‖ ^ 2) = ∏ τ, nrm θ A (Formalism.IndefR.Eqv.UI.brg fr x) τ w := by
  intro D θ hθ V A fr hP x w
  symm
  refine Fintype.prod_equiv (Formalism.L2.Host.tauPl D) _ _ fun τ => ?_
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)
  unfold nrm eu GlobalTheory.SepPer.cmp
  rw [← map_inv (Formalism.IndefR.Eqv.UI.brg fr) x, (GlobalTheory.BridgeDict.bridge_dict D θ hθ V fr).2.1 x⁻¹ τ _ rfl, hP τ]
  have key : ∀ (U Q : Matrix (Fin V.rank) (Fin V.rank) ℂ) (y : Fin V.rank → ℂ),
      A.fr τ *ᵥ (((A.fr τ)⁻¹ * U * Q) *ᵥ y) = U *ᵥ (Q *ᵥ y) := fun U Q y => by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  erw [key]
  have hP' : (Formalism.IndefR.Eqv.UI.instV fr).P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹ := hP τ
  have hφ : (Formalism.IndefR.Eqv.UI.instV fr).φ (Formalism.L2.Host.tauPl D τ) = tauE D τ := by
    show Formalism.IndefR.Eqv.UI.phiV D _ = _
    simp only [Formalism.IndefR.Eqv.UI.phiV, Equiv.symm_apply_apply]
  erw [hP', hφ]
  rfl

end GlobalTheory.NormDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalVectorNormAdelicPointTwoModelsEqStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalVectorNorm_adelicPoint_twoModels_eq : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (A : Fr V) (fr : Formalism.IndefR.Eqv.UI.Frames D V), (∀ τ, fr.P (Formalism.L2.Host.tauPl D τ) = (A.fr τ)⁻¹) → ∀ (x : (Formalism.IndefR.Eqv.UI.instV fr).GA) (w : Fin V.rank → D.host.E), ∏ v, Real.sqrt (∑ i, ‖(Formalism.MainNotions.S.uMat (x.1 v)⁻¹ *ᵥ (((Formalism.IndefR.Eqv.UI.instV fr).P v)⁻¹ *ᵥ fun j => (Formalism.IndefR.Eqv.UI.instV fr).φ v (w j))) i‖ ^ 2) = ∏ τ, nrm θ A (Formalism.IndefR.Eqv.UI.brg fr x) τ w := by
  first | exact @GlobalTheory.NormDict.norm_dict | exact GlobalTheory.NormDict.norm_dict | (intros; apply GlobalTheory.NormDict.norm_dict <;> assumption)
end
end
