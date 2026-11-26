module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselCharacterLocalElementEqSimpleEntrySum
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterIdeleCharacterMatchUnique

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaConstMul
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain

noncomputable section

namespace GlobalTheory.SeeSawFold

variable {D : D7}

theorem theta_add' {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f g : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g) : IsThetaFunO ψ S T (fun w => f w + g w) := {
  quasi γ w := by rw [hf.quasi, hg.quasi]; ring
  level := by
    obtain ⟨U, hU, hUf⟩ := hf.level
    obtain ⟨V, hV, hVg⟩ := hg.level
    refine ⟨U ⊓ V, hU.inter hV, fun u hu h0 => ?_⟩
    have e1 := hUf u hu.1 h0
    have e2 := hVg u hu.2 h0
    funext w
    have a1 := congrFun e1 w
    have a2 := congrFun e2 w
    simp only [heisO] at a1 a2 ⊢
    rw [mul_add, a1, a2]
  cont := hf.cont.add hg.cont
  smooth k L hL hL' w := (hf.smooth k L hL hL' w).add (hg.smooth k L hL hL' w) }

theorem theta_const_mul' {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ}
    (a : ℂ) (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ S T (fun w => a * f w) := {
  quasi γ w := by rw [hf.quasi]; ring
  level := by
    obtain ⟨U, hU, hUf⟩ := hf.level
    refine ⟨U, hU, fun u hu h0 => ?_⟩
    funext w
    have a1 := congrFun (hUf u hu h0) w
    simp only [heisO] at a1 ⊢
    rw [mul_left_comm, a1]
  cont := continuous_const.mul hf.cont
  smooth k L hL hL' w := contDiff_const.mul (hf.smooth k L hL hL' w) }

theorem theta_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : IsThetaFunO ψ S T (fun _ => 0) :=
  ⟨fun _ _ => by simp, ⟨⊤, isOpen_univ, fun a _ _ => by funext w; simp [heisO]⟩, continuous_const,
    fun _ _ _ _ _ => contDiff_const⟩

theorem theta_sum' {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {ι : Type*} (s : Finset ι) (F : ι → WO S T → ℂ)
    (hF : ∀ i ∈ s, IsThetaFunO ψ S T (F i)) : IsThetaFunO ψ S T (fun w => ∑ i ∈ s, F i w) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using theta_zero' ψ S T
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact theta_add' (hF i (Finset.mem_insert_self i s)) (ih fun j hj => hF j (Finset.mem_insert_of_mem hj))

section Ops

variable (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D)

def opL (a : WO A S →₀ ℂ) (C : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  fun u v => comb ψ A S a (fun u' => C u' v) u

def opR (b : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) : WO A S → WO S A' → ℂ :=
  fun u v => comb ψ S A' b (C u) v

theorem biComb_eq (a : WO A S →₀ ℂ) (b : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    biComb ψ A S A' a b C = opL ψ A S A' a (opR ψ A S A' b C) := rfl

theorem opL_opR (a : WO A S →₀ ℂ) (b : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    opL ψ A S A' a (opR ψ A S A' b C) = opR ψ A S A' b (opL ψ A S A' a C) := by
  funext u v
  simp only [opL, opR, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem foldL_opR (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))) (b : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) :
    l.foldr (fun p C => opL ψ A S A' p.1 C) (opR ψ A S A' b C) =
      opR ψ A S A' b (l.foldr (fun p C => opL ψ A S A' p.1 C) C) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.foldr_cons, ih, opL_opR]

theorem foldL_foldR (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))) (Y : WO A S → WO S A' → ℂ) :
    l.foldr (fun p C => opL ψ A S A' p.1 C) (l.foldr (fun p C => opR ψ A S A' p.2 C) Y) =
      l.foldr (fun p C => biComb ψ A S A' p.1 p.2 C) Y := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.foldr_cons, foldL_opR, ih, biComb_eq]

theorem foldR_apply (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))) (Y : WO A S → WO S A' → ℂ) (u : WO A S) :
    l.foldr (fun p C => opR ψ A S A' p.2 C) Y u = l.foldr (fun p f => comb ψ S A' p.2 f) (Y u) := by
  induction l with
  | nil => rfl
  | cons p l ih => simp only [List.foldr_cons, ← ih]; rfl

theorem foldL_apply (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))) (C : WO A S → WO S A' → ℂ) (u : WO A S)
    (v : WO S A') :
    l.foldr (fun p C => opL ψ A S A' p.1 C) C u v = l.foldr (fun p f => comb ψ A S p.1 f) (fun u' => C u' v) u := by
  induction l generalizing u with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldr_cons]
    show comb ψ A S p.1 (fun u' => l.foldr (fun p C => opL ψ A S A' p.1 C) C u' v) u = _
    congr 1
    funext u'
    rw [ih]

theorem theta_opR (b : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) (hC : ∀ v, IsThetaFunO ψ A S (fun u => C u v))
    (v : WO S A') : IsThetaFunO ψ A S (fun u => opR ψ A S A' b C u v) := by
  simp only [opR, comb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, heisO]
  refine theta_sum' _ _ fun y _ => ?_
  have h := theta_const_mul' (b y * ψ (symplOH S A' v y)) (hC (v + y))
  simpa only [mul_assoc] using h

theorem theta_foldR (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))) (Y : WO A S → WO S A' → ℂ)
    (hY : ∀ v, IsThetaFunO ψ A S (fun u => Y u v)) (v : WO S A') :
    IsThetaFunO ψ A S (fun u => l.foldr (fun p C => opR ψ A S A' p.2 C) Y u v) := by
  induction l generalizing v with
  | nil => exact hY v
  | cons p l ih => exact theta_opR ψ A S A' p.2 _ ih v

end Ops

end GlobalTheory.SeeSawFold


open GlobalTheory.SeeSawFold in
theorem GlobalTheory.SeeSaw.biComb_eq_foldr : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ)
    (c' : WO S A' →₀ ℂ) (l : List ((WO A S →₀ ℂ) × (WO S A' →₀ ℂ))),
    (∀ f, IsThetaFunO ψ A S f → comb ψ A S c f = l.foldr (fun p f' => comb ψ A S p.1 f') f) →
    (∀ f, IsThetaFunO ψ S A' f → comb ψ S A' c' f = l.foldr (fun p f' => comb ψ S A' p.2 f') f) →
    ∀ Y : WO A S → WO S A' → ℂ, (∀ v, IsThetaFunO ψ A S (fun u => Y u v)) → (∀ u, IsThetaFunO ψ S A' (Y u)) →
      biComb ψ A S A' c c' Y = l.foldr (fun p C => biComb ψ A S A' p.1 p.2 C) Y := by
  intro D ψ A S A' c c' l hc hc' Y hYv hYu
  have hR : opR ψ A S A' c' Y = l.foldr (fun p C => opR ψ A S A' p.2 C) Y := by
    funext u v
    show comb ψ S A' c' (Y u) v = _
    rw [hc' _ (hYu u), foldR_apply]
  rw [← foldL_foldR, biComb_eq, hR]
  funext u v
  rw [foldL_apply]
  exact congrFun (hc _ (theta_foldR ψ A S A' l Y hYv v)) u

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableStandardPairThetaWeilRange
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableStandardPairThetaWeilRange
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdThetaInt

theorem integrable_theta : GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (n : ℕ) (V : HSp D), 1 ≤ n → n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ (Φ : schwartzA θ V.rank n) (g : G D n), Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω Φ g)) (autMeasure V ν) := by
  intro hP D n V hn hr θ hθ ω ν hν Φ g
  set φ := ω g Φ with hφdef
  have hfin : GlobalTheory.SiegelFormula.absThetaInt V ν φ.1 < ⊤ := hP D n V hn (Or.inr hr) θ hθ ν hν φ
  have hcont : Continuous φ.1 := (GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ _ _ φ.1
    (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ _ _ φ.1 φ.2)).1
  have hleft := GlobalTheory.SiegelWeilLitCompare.leftInv_theta ω Φ g
  have hterm : ∀ h, theta ω Φ g h = ∑' ξ, φ.1 (GlobalTheory.SiegelFormula.invPt V h ξ) := fun h => rfl
  refine ⟨?_, ?_⟩
  · rw [autMeasure, aestronglyMeasurable_quotMeasure_iff_lift, hleft.lift_descend]
    have hae : ∀ᵐ q ∂autMeasure V ν, descend (GQ V) (GlobalTheory.SiegelFormula.absTheta V φ.1) q < ⊤ :=
      ae_lt_top (GlobalTheory.AbsThetaSemi.measurable_descend_absTheta V hcont) hfin.ne
    have hae' : ∀ᵐ h ∂ν, GlobalTheory.SiegelFormula.absTheta V φ.1 h < ⊤ := by
      have := (quasiMeasurePreserving_mk (Γ := GQ V) (μ := ν)).ae hae
      filter_upwards [this] with h hh
      rwa [(GlobalTheory.SiegelFormula.leftInv_absTheta V φ.1).descend_mk] at hh
    haveI := GlobalTheory.ThetaTransformMeas.countable_field D.host.E
    haveI : Countable (Matrix (Fin V.rank) (Fin n) D.host.E) :=
      inferInstanceAs (Countable (Fin V.rank → Fin n → D.host.E))
    have hsum : ∀ᵐ h ∂ν, Summable fun ξ : Matrix (Fin V.rank) (Fin n) D.host.E =>
        φ.1 (GlobalTheory.SiegelFormula.invPt V h ξ) :=
      hae'.mono fun h hh => Summable.of_enorm hh.ne
    have hlim := aestronglyMeasurable_of_tendsto_ae (μ := ν)
      (Filter.atTop : Filter (Finset (Matrix (Fin V.rank) (Fin n) D.host.E)))
      (f := fun F h => ∑ ξ ∈ F, φ.1 (GlobalTheory.SiegelFormula.invPt V h ξ))
      (fun F => (continuous_finsetSum F fun ξ _ =>
        hcont.comp (GlobalTheory.AbsThetaSemi.continuous_invPt V ξ)).aestronglyMeasurable)
      (hsum.mono fun h hh => hh.hasSum)
    exact hlim.congr (Filter.Eventually.of_forall fun h => (hterm h).symm)
  · refine lt_of_le_of_lt (lintegral_mono fun q => ?_) hfin
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, GlobalTheory.SiegelFormula.absTheta]
    exact enorm_tsum_le_tsum_enorm

end GlobalTheory.StdThetaInt

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegrableStandardPairThetaWeilRangeStatement
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_standardPair_theta_weilRange : GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (n : ℕ) (V : HSp D), 1 ≤ n → n + Formalism.MainNotions.SchurIrreducible.wittIdx V < V.rank → ∀ θ : InfFam D, IsInfFam θ → ∀ (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (ν : Measure (GA D V)), ν.IsHaarMeasure → ∀ (Φ : schwartzA θ V.rank n) (g : G D n), Integrable (GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (theta ω Φ g)) (autMeasure V ν) := by
  first | exact @GlobalTheory.StdThetaInt.integrable_theta | exact GlobalTheory.StdThetaInt.integrable_theta | (intros; apply GlobalTheory.StdThetaInt.integrable_theta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineContractionHeisenbergInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineContractionHeisenbergInvariant
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Unf.ContrHeis

variable {D : D7}

theorem symplOH_kappa {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    (w w' : WO S B'.L) : symplOH B.L S (l.κ S w) (l.κ S w') = -symplOH S B'.L w w' := by
  have hτ := (GlobalTheory.Unf.LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
  obtain ⟨-, -, -, -, hsym, -⟩ := GlobalTheory.LinkKappa.kappa_props D B.L B'.L S l.τ 1 hτ (l.κ S) (fun _ => rfl)
  rw [symplOH, symplOH, hsym, Int.cast_one, one_mul, mul_neg]

theorem kappa_add {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    (w w' : WO S B'.L) : l.κ S (w + w') = l.κ S w + l.κ S w' := by
  have hτ := (GlobalTheory.Unf.LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
  exact (GlobalTheory.LinkKappa.kappa_props D B.L B'.L S l.τ 1 hτ (l.κ S) (fun _ => rfl)).1 w w'

theorem kappa_rat {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D)
    (w : WO S B'.L) (hw : w ∈ ratMx D B'.L.rank S.rank) : l.κ S w ∈ ratMx D S.rank B.L.rank := by
  have hτ := (GlobalTheory.Unf.LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
  exact (GlobalTheory.LinkKappa.kappa_props D B.L B'.L S l.τ 1 hτ (l.κ S) (fun _ => rfl)).2.2.1 w hw

theorem contr_heisO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (Ξ₁ : WO B.V₀ S → ℂ) (Ξ₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ S Ξ₁ → IsThetaFunO ψ S B'.V₀ Ξ₂ → ∀ x : WO S B'.L, GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, l.κ S x)) Ξ₁) (heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, x)) Ξ₂) = GlobalTheory.Unf.contr l S vL Ξ₁ Ξ₂ := by
  intro D ψ _ ρ σ B B' l S vL Ξ₁ Ξ₂ h₁ h₂ x
  funext u v
  have hT : ∀ (a b : WO S B'.A) (c d : WO S B'.L), symplOH S B'.V₀ ((B'.o.resT S).symm (a, c)) ((B'.o.resT S).symm (b, d)) =
      symplOH S B'.A a b + symplOH S B'.L c d := by
    intro a b c d
    rw [B'.o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  have hS : ∀ (a b : WO B.A S) (c d : WO B.L S), symplOH B.V₀ S ((B.o.resS S).symm (a, c)) ((B.o.resS S).symm (b, d)) =
      symplOH B.A S a b + symplOH B.L S c d := by
    intro a b c d
    rw [B.o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  set G : WO S B'.L → ℂ := fun w => Ξ₂ ((B'.o.resT S).symm (v, w)) * Ξ₁ ((B.o.resS S).symm (u, l.κ S w)) with hG
  have step : ∀ w, heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, x)) Ξ₂ ((B'.o.resT S).symm (v, w)) *
      heisO ψ B.V₀ S ((B.o.resS S).symm (0, l.κ S x)) Ξ₁ ((B.o.resS S).symm (u, l.κ S w)) = G (w + x) := by
    intro w
    simp only [heisO, hG]
    rw [hT, hS, symplOH_zero_right, symplOH_zero_right, zero_add, zero_add, symplOH_kappa, ← map_add (f := _), ← map_add (f := _),
      Prod.mk_add_mk, Prod.mk_add_mk, add_zero, add_zero, ← kappa_add]
    have e : ψ (symplOH S B'.L w x) * ψ (-symplOH S B'.L w x) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    linear_combination (Ξ₂ ((B'.o.resT S).symm (v, w + x)) * Ξ₁ ((B.o.resS S).symm (u, l.κ S (w + x)))) * e
  have per : ∀ γ ∈ ratMx D B'.L.rank S.rank, ∀ a, G (γ + a) = G a := by
    intro γ hγ a
    have r2 : (B'.o.resT S).symm (0, γ) ∈ ratMx D B'.V₀.rank S.rank := by
      refine (B'.o.mem_ratL_resT S _).2 ?_
      rw [AddEquiv.apply_symm_apply]
      exact ⟨zero_mem _, hγ⟩
    have r1 : (B.o.resS S).symm (0, l.κ S γ) ∈ ratMx D S.rank B.V₀.rank := by
      refine (B.o.mem_ratL_resS S _).2 ?_
      rw [AddEquiv.apply_symm_apply]
      exact ⟨zero_mem _, kappa_rat l S γ hγ⟩
    obtain ⟨γ₂, hγ₂⟩ := r2
    obtain ⟨γ₁, hγ₁⟩ := r1
    have q2 := h₂.quasi γ₂ ((B'.o.resT S).symm (v, a))
    have q1 := h₁.quasi γ₁ ((B.o.resS S).symm (u, l.κ S a))
    have e2 : ratW B'.V₀ S γ₂ = (B'.o.resT S).symm (0, γ) := hγ₂
    have e1 : ratW S B.V₀ γ₁ = (B.o.resS S).symm (0, l.κ S γ) := hγ₁
    rw [e2, ← map_add (f := _), Prod.mk_add_mk, zero_add, hT, symplOH_zero_left, zero_add] at q2
    rw [e1, ← map_add (f := _), Prod.mk_add_mk, zero_add, hS, symplOH_zero_left, zero_add, symplOH_kappa, neg_neg] at q1
    simp only [hG]
    rw [kappa_add, q2, q1]
    have e : ψ (-symplOH S B'.L γ a) * ψ (symplOH S B'.L γ a) = 1 := by
      rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
    linear_combination (Ξ₂ ((B'.o.resT S).symm (v, a)) * Ξ₁ ((B.o.resS S).symm (u, l.κ S a))) * e
  simp only [contr]
  rw [show (fun w => heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, x)) Ξ₂ ((B'.o.resT S).symm (v, w)) *
      heisO ψ B.V₀ S ((B.o.resS S).symm (0, l.κ S x)) Ξ₁ ((B.o.resS S).symm (u, l.κ S w))) = fun w => G (w + x)
    from funext step]
  exact covolOne_integral_add vL.covol G per x

end GlobalTheory.Unf.ContrHeis

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineContractionHeisenbergInvariantStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselLineContraction_heisenberg_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (Ξ₁ : WO B.V₀ S → ℂ) (Ξ₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ S Ξ₁ → IsThetaFunO ψ S B'.V₀ Ξ₂ → ∀ x : WO S B'.L, GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, l.κ S x)) Ξ₁) (heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, x)) Ξ₂) = GlobalTheory.Unf.contr l S vL Ξ₁ Ξ₂ := by
  first | exact @GlobalTheory.Unf.ContrHeis.contr_heisO | exact GlobalTheory.Unf.ContrHeis.contr_heisO | (intros; apply GlobalTheory.Unf.ContrHeis.contr_heisO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastColumnDatumTensorMemSchwartzBruhat
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastColumnDatumTensorMemSchwartzBruhat
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocFlat.CFac
open scoped Topology

noncomputable section
namespace GlobalTheory.LocFlat.LastColumn

def colJoin (n n' k : Type) [TopologicalSpace k] : Matrix n n' k × (n → k) ≃ₜ Matrix n (n' ⊕ Unit) k where
  toFun p := fromCols p.1 (Matrix.of fun r _ => p.2 r)
  invFun M := (M.toCols₁, fun r => M r (Sum.inr ()))
  left_inv p := by
    obtain ⟨x, y⟩ := p
    refine Prod.ext ?_ ?_
    · ext r j; simp [toCols₁]
    · funext r; simp
  right_inv M := by
    ext r (j | u)
    · simp [toCols₁]
    · cases u; simp
  continuous_toFun := by
    refine continuous_matrix fun r j => ?_
    cases j with
    | inl j => simpa using continuous_fst.matrix_elem r j
    | inr u => simpa using (by fun_prop : Continuous fun a : Matrix n n' k × (n → k) => a.2 r)
  continuous_invFun := by
    refine Continuous.prodMk (continuous_matrix fun r j => ?_) (continuous_pi fun r => ?_)
    · simpa [toCols₁] using continuous_id.matrix_elem r (Sum.inl j)
    · exact continuous_id.matrix_elem r (Sum.inr ())

def colSplit (n n' k : Type) [TopologicalSpace k] :
    Matrix n (n' ⊕ Unit) k ≃ₜ Matrix n n' k × Matrix n Unit k where
  toFun x := (x.toCols₁, Matrix.of fun r _ => x r (Sum.inr ()))
  invFun p := fromCols p.1 p.2
  left_inv x := by
    ext r (j | u)
    · simp [toCols₁]
    · cases u; simp
  right_inv p := by
    obtain ⟨x, y⟩ := p
    refine Prod.ext ?_ ?_
    · ext r j; simp [toCols₁]
    · ext r u; cases u; simp
  continuous_toFun := by
    refine Continuous.prodMk (continuous_matrix fun r j => ?_) (continuous_matrix fun r u => ?_)
    · simpa [toCols₁] using continuous_id.matrix_elem r (Sum.inl j)
    · simpa using continuous_id.matrix_elem r (Sum.inr ())
  continuous_invFun := by
    refine continuous_matrix fun r j => ?_
    cases j with
    | inl j => simpa using continuous_fst.matrix_elem r j
    | inr u => simpa using continuous_snd.matrix_elem r u

def rowSplit (n n' Z k : Type) [TopologicalSpace k] :
    Matrix n n' k × Matrix (Z ⊕ Unit) n k ≃ₜ (Matrix n n' k × (n → k)) × Matrix Z n k where
  toFun q := ((q.1, q.2 (Sum.inr ())), q.2.toRows₁)
  invFun p := (p.1.1, fromRows p.2 (Matrix.of fun _ => p.1.2))
  left_inv q := by
    obtain ⟨x, M⟩ := q
    refine Prod.ext rfl ?_
    ext (i | u) j
    · simp [toRows₁]
    · cases u; simp
  right_inv p := by
    obtain ⟨⟨x, y⟩, A⟩ := p
    refine Prod.ext (Prod.ext rfl ?_) ?_
    · funext j; simp
    · ext i j; simp [toRows₁]
  continuous_toFun := by
    refine Continuous.prodMk (Continuous.prodMk continuous_fst (continuous_pi fun j => ?_))
      (continuous_matrix fun i j => ?_)
    · exact continuous_snd.matrix_elem (Sum.inr ()) j
    · simpa [toRows₁] using continuous_snd.matrix_elem (Sum.inl i) j
  continuous_invFun := by
    refine Continuous.prodMk (continuous_fst.comp continuous_fst) (continuous_matrix fun i j => ?_)
    cases i with
    | inl i => simpa using continuous_snd.matrix_elem i j
    | inr u => simpa using (by fun_prop : Continuous fun a : (Matrix n n' k × (n → k)) × Matrix Z n k => a.1.2 j)

theorem isLocallyConstant_integral {Q Y : Type} [TopologicalSpace Q] [TopologicalSpace Y] [MeasurableSpace Y]
    (μ : Measure Y) {H : Q × Y → ℂ} (hH : IsLocallyConstant H) {K : Set Y} (hK : IsCompact K)
    (hz : ∀ q, ∀ y ∉ K, H (q, y) = 0) : IsLocallyConstant fun q => ∫ y, H (q, y) ∂μ := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun q₀ => ?_
  have h1 : ∀ᶠ q in 𝓝 q₀, ∀ y ∈ K, H (q, y) = H (q₀, y) := by
    refine IsCompact.eventually_forall_of_forall_eventually hK fun y _ => ?_
    have h2 : IsLocallyConstant fun p : Q × Y => (H p, H (q₀, p.2)) :=
      hH.prodMk (hH.comp_continuous (by fun_prop))
    filter_upwards [h2.eventually_eq (q₀, y)] with p hp
    simp only [Prod.mk.injEq] at hp
    exact hp.1.trans hp.2.symm
  filter_upwards [h1] with q hq
  congr 1
  funext y
  by_cases hy : y ∈ K
  · exact hq y hy
  · rw [hz q y hy, hz q₀ y hy]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem hatCol_mem_SB (ψ : AddChar k Circle) (hψ : Continuous ψ) (hne : ψ ≠ 1) (ν : Measure k)
    [ν.IsAddHaarMeasure] {n n' : Type} [Fintype n] [DecidableEq n]
    {Ψ : Matrix n (n' ⊕ Unit) k → ℂ} (hΨ : Ψ ∈ SB (Matrix n (n' ⊕ Unit) k)) :
    (fun p : Matrix n n' k × (n → k) =>
      GlobalTheory.StepData.hat ψ ν (-1) (fun y => Ψ (fromCols p.1 (Matrix.of fun r _ => y r))) p.2) ∈
      SB (Matrix n n' k × (n → k)) := by
  classical
  have := secondCountable k
  have := t2Space k
  obtain ⟨c, hc⟩ := (conductor_exists k).1 ψ hψ hne
  set f : Matrix n n' k × (n → k) → ℂ := fun p => Ψ (colJoin n n' k p) with hfdef
  have hf : f ∈ SB (Matrix n n' k × (n → k)) :=
    ⟨hΨ.1.comp_continuous (colJoin n n' k).continuous, hΨ.2.comp_homeomorph _⟩
  obtain ⟨s, hs⟩ : ∃ s : kˣ, ∀ t ∈ FourierPi.box n s, ∀ x y, f (x, y + t) = f (x, y) := by
    have h1 := PartialFourier.eventually_add_invariant hf
    have h2 : Filter.Tendsto (fun t : n → k => ((0, t) : Matrix n n' k × (n → k))) (𝓝 0) (𝓝 0) := by
      have : Continuous (fun t : n → k => ((0, t) : Matrix n n' k × (n → k))) := by fun_prop
      exact this.tendsto 0
    obtain ⟨s, hs⟩ := FourierPi.exists_box_subset (h2.eventually h1)
    exact ⟨s, fun t ht x y => by simpa using hs ht (x, y)⟩
  have hfun : (fun p : Matrix n n' k × (n → k) =>
      GlobalTheory.StepData.hat ψ ν (-1) (fun y => Ψ (fromCols p.1 (Matrix.of fun r _ => y r))) p.2) =
      fun p => ∫ y, f (p.1, y) * (ψ (y ⬝ᵥ (-p.2)) : ℂ) ∂(Measure.pi fun _ => ν) := by
    funext p
    simp only [GlobalTheory.StepData.hat]
    congr 1
    funext y
    rw [dotProduct_neg, dotProduct_comm, neg_one_mul]
    rfl
  rw [hfun]
  refine ⟨?_, ?_⟩
  · refine isLocallyConstant_integral _
      (H := fun q : (Matrix n n' k × (n → k)) × (n → k) => f (q.1.1, q.2) * (ψ (q.2 ⬝ᵥ (-q.1.2)) : ℂ))
      ?_ (hf.2.image continuous_snd) ?_
    · refine (hf.1.comp_continuous (by fun_prop)).mul ?_
      exact (hc.isLocallyConstant.comp_continuous
        (continuous_snd.dotProduct (continuous_snd.comp continuous_fst).neg)).comp (fun z : Circle => (z : ℂ))
    · intro q y hy
      have : f (q.1, y) = 0 := image_eq_zero_of_notMem_tsupport fun h => hy ⟨_, h, rfl⟩
      simp [this]
  · refine HasCompactSupport.intro
      ((hf.2.image continuous_fst).prod (FourierPi.isCompact_box (n := n) (c * s⁻¹)).neg) fun p hp => ?_
    rw [Set.mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · have : ∀ y, f (p.1, y) = 0 := fun y => image_eq_zero_of_notMem_tsupport fun h => hp ⟨_, h, rfl⟩
      simp [this]
    · rw [Set.mem_neg] at hp
      exact FourierPi.fourier_eq_zero_pi _ hc (f := fun y => f (p.1, y)) (fun t ht y => hs t ht p.1 y) hp

theorem lastColumn_datum_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ (n n' Z : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype Z] [DecidableEq Z], (∀ (Ψ₁ : SB (Matrix n (n' ⊕ Unit) k)) (Ψ₂ : SB (Matrix Z n k)), ∃ Ξ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k), ∀ q, Ξ.1 q = Ψ₂.1 q.2.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => Ψ₁.1 (fromCols q.1 (Matrix.of fun r _ => y r))) (q.2 (Sum.inr ()))) ∧ ∀ (Ξ₁ : SB (Matrix n n' k)) (c : SB (Matrix n Unit k)), ∃ Ψ₁ : SB (Matrix n (n' ⊕ Unit) k), ∀ x, Ψ₁.1 x = Ξ₁.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ())) := by
  intro k _ _ _ _ _ _ ν hν ψk hψ hne n n' Z _ _ _ _ _ _
  haveI := hν
  refine ⟨fun Ψ₁ Ψ₂ => ?_, fun Ξ₁ c => ?_⟩
  · let F : SB (Matrix n n' k × (n → k)) := ⟨_, hatCol_mem_SB ψk hψ hne ν Ψ₁.2⟩
    exact ⟨comapH (rowSplit n n' Z k) (prodSB F Ψ₂), fun q => mul_comm _ _⟩
  · exact ⟨comapH (colSplit n n' k) (prodSB Ξ₁ c), fun x => rfl⟩

end GlobalTheory.LocFlat.LastColumn
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastColumnDatumTensorMemSchwartzBruhatStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.last_column_datum_tensor_mem_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψk : AddChar k Circle), Continuous ψk → ψk ≠ 1 → ∀ (n n' Z : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] [Fintype Z] [DecidableEq Z], (∀ (Ψ₁ : SB (Matrix n (n' ⊕ Unit) k)) (Ψ₂ : SB (Matrix Z n k)), ∃ Ξ : SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k), ∀ q, Ξ.1 q = Ψ₂.1 q.2.toRows₁ * GlobalTheory.StepData.hat ψk ν (-1) (fun y => Ψ₁.1 (fromCols q.1 (Matrix.of fun r _ => y r))) (q.2 (Sum.inr ()))) ∧ ∀ (Ξ₁ : SB (Matrix n n' k)) (c : SB (Matrix n Unit k)), ∃ Ψ₁ : SB (Matrix n (n' ⊕ Unit) k), ∀ x, Ψ₁.1 x = Ξ₁.1 x.toCols₁ * c.1 (Matrix.of fun r _ => x r (Sum.inr ())) := by
  first | exact @GlobalTheory.LocFlat.LastColumn.lastColumn_datum_mem_SB | exact GlobalTheory.LocFlat.LastColumn.lastColumn_datum_mem_SB | (intros; apply GlobalTheory.LocFlat.LastColumn.lastColumn_datum_mem_SB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NatCastNotMemUnderSq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open NumberField IsDedekindDomain Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.SplitDegOneChar

theorem absNorm_under {E F : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [Algebra (𝓞 F) (𝓞 E)] [Algebra.IsIntegral (𝓞 F) (𝓞 E)]
    (PP : HeightOneSpectrum (𝓞 E)) (p : ℕ) (hp : p.Prime) (hPP : Ideal.absNorm PP.asIdeal = p) :
    Ideal.absNorm (PP.under (𝓞 F)).asIdeal = p := by
  set v := PP.under (𝓞 F) with hvdef
  have hle : v.asIdeal ≤ PP.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E)) := le_rfl
  haveI := v.isMaximal
  haveI := PP.isMaximal
  letI := Ideal.Quotient.field v.asIdeal
  letI : Algebra (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ PP.asIdeal) := Ideal.Quotient.algebraQuotientOfLEComap hle
  have hE : Nat.card (𝓞 E ⧸ PP.asIdeal) = p := by rw [← hPP, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  haveI : Finite (𝓞 E ⧸ PP.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hE]; exact hp.ne_zero)
  haveI : Module.Finite (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ PP.asIdeal) := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := 𝓞 F ⧸ v.asIdeal) (V := 𝓞 E ⧸ PP.asIdeal)
  rw [hE] at h
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact ((hp.pow_eq_iff).1 h.symm).1

theorem natCast_not_mem_under_sq {E F : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra (𝓞 F) (𝓞 E)] [Algebra.IsIntegral (𝓞 F) (𝓞 E)]
    (PP : HeightOneSpectrum (𝓞 E)) (p : ℕ) (hsq : (p : 𝓞 E) ∉ PP.asIdeal ^ 2) :
    (p : 𝓞 F) ∉ (PP.under (𝓞 F)).asIdeal ^ 2 := by
  intro h
  apply hsq
  have h1 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) h
  rw [Ideal.map_pow, map_natCast] at h1
  exact Ideal.pow_right_mono (Ideal.map_comap_le) 2 h1

end GlobalTheory.SplitDegOneChar

namespace GlobalTheory.SplitDegOneChar

theorem psiE_sec_pr_eq_exp : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E) (p : ℕ), p.Prime → Ideal.absNorm PP.asIdeal = p → ((p : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ^ 2 → q.v = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) → (∀ x, (ofSplit q).pr x ∈ 𝒪[k] ↔ Formalism.L2.Col.IntAt PP x) → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (x : D.host.E) (b : ℤ), Formalism.L2.Col.IntAt PP (x - (b : D.host.E) / (p : D.host.E)) → psiE ψ (q.sec ((ofSplit q).pr x)) = Complex.exp (2 * Real.pi * Complex.I * b / (p : ℂ)) := by
  intro D k _ _ _ _ q PP p hp hPP hsq hv hint ψ hψ x b hx
  have hpr : ∀ y : D.host.E, (ofSplit q).pr y = q.pr (incA D y) := fun _ => rfl
  set c : D.host.F := (b : D.host.F) / (p : D.host.F) with hcdef
  have hc : algebraMap D.host.F D.host.E c = (b : D.host.E) / (p : D.host.E) := by
    rw [hcdef, map_div₀, map_intCast, map_natCast]
  have hxs : x = (x - (b : D.host.E) / (p : D.host.E)) + algebraMap D.host.F D.host.E c := by
    rw [hc]; ring
  have hadd : ∀ u w : AE D, psiE ψ (u + w) = psiE ψ u * psiE ψ w := by
    intro u w; simp only [GlobalTheory.MixPer.psiE, map_add (f := _), AddChar.map_add_eq_mul]
  rw [hxs, hpr, map_add (f := _), map_add (f := _), map_add (f := _), hadd]

  have hy : q.pr (incA D (x - (b : D.host.E) / (p : D.host.E))) ∈ 𝒪[k] := by
    rw [← hpr]; exact (hint _).2 hx
  have h1 : psiE ψ (q.sec (q.pr (incA D (x - (b : D.host.E) / (p : D.host.E))))) = 1 := by
    rw [GlobalTheory.MixPer.psiE, GlobalTheory.SplitCharCond.trace_sec q, GlobalTheory.SplitCharCond.snd_trace,
      GlobalTheory.SplitCharCond.char_int hψ (GlobalTheory.SplitCharCond.trace_int ((q.int_iff _).1 hy))]
  rw [h1, one_mul]

  obtain ⟨ε, hε, he⟩ := q.above
  have htr : Algebra.trace (AF D.host.F) (AE D) q.e = ε := by
    refine Algebra.TensorProduct.includeLeft_injective (S := AF D.host.F) (algebraMap D.host.F D.host.E).injective ?_
    change algebraMap (AF D.host.F) (AE D) _ = algebraMap (AF D.host.F) (AE D) _
    rw [GlobalTheory.FockCompare.SymplVal.trace_AE, he]
  have hinc : incA D (algebraMap D.host.F D.host.E c) =
      algebraMap (AF D.host.F) (AE D) (algebraMap D.host.F (AF D.host.F) c) := GlobalTheory.SplitCharCond.one_tmul_eq c
  rw [q.sec_pr, hinc, mul_comm, ← Algebra.smul_def, GlobalTheory.MixPer.psiE, map_smul, smul_eq_mul, htr, mul_comm]
  have hnorm : Ideal.absNorm q.v.asIdeal = p := by rw [hv]; exact absNorm_under PP p hp hPP
  have hsqv : (p : 𝓞 D.host.F) ∉ q.v.asIdeal ^ 2 := by rw [hv]; exact natCast_not_mem_under_sq PP p hsq
  have key := GlobalTheory.StdCharDegOne.stdChar_placeIdem_div D ψ hψ p hp q.v hnorm hsqv ε hε (b : 𝓞 D.host.F) b
    (by rw [sub_self]; exact zero_mem _)
  rw [← key, hcdef]
  push_cast
  rfl

end GlobalTheory.SplitDegOneChar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ReducedChainLocalIdentity
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData NumberField
open scoped Classical

noncomputable section

namespace GlobalTheory.ChainOnto

theorem one_add_idem_mul {R : Type} [CommRing R] {e A B : R} (he : e * e = e) (hAB : A * B = 1) :
    (1 + e * (A - 1)) * (1 + e * (B - 1)) = 1 := by
  linear_combination (A - 1) * (B - 1) * he + e * hAB

theorem one_add_idem_mul_eq {R : Type} [CommRing R] (e A : R) : 1 + e * (A - 1) = e * A + (1 - e) := by ring

theorem locE_mul_inv (D : D7) {e : AE D} (he : e * e = e) {z : D.host.E} (hz : z ≠ 0) :
    Formalism.L2.JoinChr.locE D e z * Formalism.L2.JoinChr.locE D e z⁻¹ = 1 := by
  have h3 : incA D z * incA D z⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hz, map_one]
  exact one_add_idem_mul he h3

theorem locE_eq (D : D7) (e : AE D) (z : D.host.E) : Formalism.L2.JoinChr.locE D e z = e * incA D z + (1 - e) :=
  one_add_idem_mul_eq _ _


open GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.StdFrames Formalism.L2.Host Formalism.L2.DIV in
set_option maxHeartbeats 2000000 in
theorem chi_compat_of_isComp : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (PP : Formalism.L2.DIV.Pl D.host.E), Formalism.L2.NTheta.IsIdemAt q.e PP → ∀ π' : EAf D →+* k, (∀ a, π' (toEAf D a) = q.pr a) → GlobalTheory.FunObj.Comparison₂.IsRed (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) → ∀ c : GlobalTheory.ChainOnto.Com D, c.Is → PP ∈ c.Pg → ∀ j : ℕ, 1 ≤ j → j ≤ D.R.m → ∀ μ : kˣ →* ℂˣ, IsTame μ → (ofSplit q).IsComp (c.chS j)⁻¹ μ → GlobalTheory.FunObj.Comparison₂.Compat (Formalism.L2.DIV.resS D.host.F PP) (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (c.chi j PP) μ := by
  intro D k _ _ _ _ q PP hI π' hπ hR c hc hP j hj1 hj2 μ hμ hC
  intro s u x hu hx
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : Formalism.L2.DIV.kP PP)
  have hoa : ((Formalism.L2.DIV.oToS D.host.F D.host.E a : Formalism.L2.Herm.intAf D.host.F D.host.E) : EAf D) =
      toEAf D (incA D (a : D.host.E)) := rfl
  have hψa : (π'.comp (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype) (Formalism.L2.DIV.oToS D.host.F D.host.E a) =
      q.pr (incA D (a : D.host.E)) := by
    rw [RingHom.comp_apply, Subring.coe_subtype, hoa, hπ]
  have hres : Formalism.L2.DIV.resS D.host.F PP (Formalism.L2.DIV.oToS D.host.F D.host.E a) = u := by
    rw [Formalism.L2.DIV.resS_oToS, ha]
  have h1 : valuation k (q.pr (incA D (a : D.host.E))) = 1 := by
    rw [← hψa, ← hR.isUnit_iff, hres]; exact u.isUnit
  have h2 : valuation k ((x : k) - q.pr (incA D (a : D.host.E))) < 1 := by
    rw [← hψa, hx, ← map_sub]
    refine (hR.ker _).1 ?_
    rw [map_sub, hres, ← hu, sub_self]
  have hp0 : q.pr (incA D (a : D.host.E)) ≠ 0 := fun h => by rw [h, map_zero] at h1; exact zero_ne_one h1
  have hμx : μ x = μ (Units.mk0 _ hp0) := by
    have : μ (x * (Units.mk0 _ hp0)⁻¹) = 1 := hμ _ (by
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_mk0, ← mul_inv_cancel₀ hp0, ← sub_mul, map_mul, map_inv₀, h1,
        inv_one, mul_one]
      exact h2)
    rw [map_mul, map_inv, mul_inv_eq_one] at this; exact this
  have ha0 : (a : D.host.E) ≠ 0 := fun h => by rw [h, map_zero, map_zero] at h1; exact zero_ne_one h1
  have hee : q.e * q.e = q.e := hI.1.1
  let y : (AE D)ˣ := ⟨Formalism.L2.JoinChr.locE D q.e (a : D.host.E), Formalism.L2.JoinChr.locE D q.e (a : D.host.E)⁻¹,
    GlobalTheory.ChainOnto.locE_mul_inv D hee ha0, by rw [mul_comm]; exact GlobalTheory.ChainOnto.locE_mul_inv D hee ha0⟩
  have hyι : (y : AE D) = (ofSplit q).ι ((Units.mk0 _ hp0 : kˣ) : k) + (1 - (ofSplit q).e) := by
    show Formalism.L2.JoinChr.locE D q.e (a : D.host.E) = q.sec (q.pr (incA D (a : D.host.E))) + (1 - q.e)
    rw [q.sec_pr, GlobalTheory.ChainOnto.locE_eq]
  have hcomp := hC _ y hyι
  have hinf : infPart D q.e = 0 := (GlobalTheory.IdemSupport.delta_of_isIdemAt (comp_toAd D) hI).1
  have hint : ∀ z : D.host.E, valuation k (q.pr (incA D z)) = 1 →
      finPart D (Formalism.L2.JoinChr.locE D q.e z) ∈ intAE D := by
    intro z hz
    rw [GlobalTheory.ChainOnto.locE_eq, ← q.sec_pr, map_add, (finPart D).map_sub, (finPart D).map_one]
    refine add_mem ((q.int_iff _).1 ?_) (sub_mem (GlobalTheory.AdIdem.idempotent_mem_intAE D 1 (mul_one 1))
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← (finPart D).map_mul, hee])))
    exact (Valuation.mem_integer_iff _ _).2 hz.le
  have hinv : q.pr (incA D (a : D.host.E)⁻¹) = (q.pr (incA D (a : D.host.E)))⁻¹ := map_inv₀ (q.pr.comp (incA D)) _
  have hη : c.η y = 1 := hc.chars.2.1 y (by
      show infPart D (Formalism.L2.JoinChr.locE D q.e (a : D.host.E)) = 1
      rw [GlobalTheory.ChainOnto.locE_eq, map_add, (infPart D).map_mul, (infPart D).map_sub, (infPart D).map_one, hinf,
        zero_mul, zero_add, sub_zero])
    (hint _ h1) (hint _ (by rw [hinv, map_inv₀, h1, inv_one]))
  have hS : c.chS j y = c.μ j y := by
    unfold GlobalTheory.ChainOnto.Com.chS Formalism.IndefR.Lift.chrStep
    split_ifs <;> simp [hη]
  obtain ⟨H, hH1, hH2⟩ := hc.res ⟨j - 1, by omega⟩
  have hj : j - 1 + 1 = j := Nat.sub_add_cancel hj1
  dsimp only at hH1 hH2
  rw [hj] at hH1 hH2
  have hIP : Formalism.L2.JoinChr.IsPlIdem D q.e PP := by
    obtain ⟨h1', h2', v, ε, h3', h4'⟩ := hI.1
    exact ⟨h1', ⟨v, ε, h3', Or.inl ⟨h2', h4'⟩⟩, hI.2⟩
  have e1 := hH1.2 PP q.e hIP (Units.mk0 _ ha0) y rfl
  have e2 := hH2 PP hP a (Units.mk0 _ ha0) u rfl ha.symm
  apply Units.ext
  rw [hμx, hcomp, MonoidHom.inv_apply, Circle.coe_inv, hS, e1, ← e2, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, inv_inv]

end GlobalTheory.ChainOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsModelChg
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod

noncomputable section

namespace GlobalTheory.LocMod.FrameChange

variable {k : Type} [Field k]
variable {N M : ℕ} {Y Y' Z Z' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
  [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z']

def chg (FS : Frame k M Y') (FT : Frame k N Y) (GS : Frame k M Z') (GT : Frame k N Z)
    (x : Matrix Y Y' k) : Matrix Z Z' k :=
  GT.γ * FT.β * x * (FS.γ * GS.β)

theorem chg_inv (FS : Frame k M Y') (FT : Frame k N Y) (GS : Frame k M Z') (GT : Frame k N Z)
    (x : Matrix Y Y' k) : chg GS GT FS FT (chg FS FT GS GT x) = x := by
  simp only [chg, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc GT.β GT.γ, GT.βγ, Matrix.one_mul, ← Matrix.mul_assoc FT.γ FT.β, FT.γβ, Matrix.one_mul,
    ← Matrix.mul_assoc GS.β GS.γ, GS.βγ, Matrix.one_mul, FS.γβ, Matrix.mul_one]

theorem frame_sandwich (FS : Frame k M Y') (FT : Frame k N Y) (GS : Frame k M Z') (GT : Frame k N Z)
    (x : Matrix Y Y' k) : GT.β * chg FS FT GS GT x * GS.γ = FT.β * x * FS.γ := by
  simp only [chg, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc GT.β GT.γ, GT.βγ, Matrix.one_mul, GS.βγ, Matrix.mul_one]

theorem chg_add (FS : Frame k M Y') (FT : Frame k N Y) (GS : Frame k M Z') (GT : Frame k N Z)
    (x y : Matrix Y Y' k) : chg FS FT GS GT (x + y) = chg FS FT GS GT x + chg FS FT GS GT y := by
  simp only [chg, Matrix.mul_add, Matrix.add_mul]

variable [TopologicalSpace k] [IsTopologicalRing k]

theorem continuous_chg (FS : Frame k M Y') (FT : Frame k N Y) (GS : Frame k M Z') (GT : Frame k N Z) :
    Continuous (chg FS FT GS GT) := by
  unfold chg
  exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

def chgH (FS : Frame k M Y') (FT : Frame k N Y) (GS : Frame k M Z') (GT : Frame k N Z) :
    Matrix Y Y' k ≃ₜ Matrix Z Z' k where
  toFun := chg FS FT GS GT
  invFun := chg GS GT FS FT
  left_inv := chg_inv FS FT GS GT
  right_inv := chg_inv GS GT FS FT
  continuous_toFun := continuous_chg FS FT GS GT
  continuous_invFun := continuous_chg GS GT FS FT

def pull (FS : Frame k M Y') (FT : Frame k N Y) (GS : Frame k M Z') (GT : Frame k N Z) :
    SB (Matrix Z Z' k) →ₗ[ℂ] SB (Matrix Y Y' k) where
  toFun Φ := ⟨fun x => Φ.1 (chg FS FT GS GT x),
    ⟨Φ.2.1.comp_continuous (continuous_chg FS FT GS GT),
     Φ.2.2.comp_homeomorph (chgH FS FT GS GT)⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end GlobalTheory.LocMod.FrameChange

namespace GlobalTheory.LocMod.Place

open GlobalTheory.LocMod.FrameChange

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : Place D k)

theorem up_chg {Y Y' Z Z' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y']
    [Fintype Z] [DecidableEq Z] [Fintype Z'] [DecidableEq Z'] {S T : HSp D}
    (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (GS : Frame k S.rank Z') (GT : Frame k T.rank Z)
    (x : Matrix Y Y' k) : p.up GS GT (chg FS FT GS GT x) = p.up FS FT x := by
  unfold up
  rw [frame_sandwich]

theorem exists_isModel_chg (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (p : Place D k) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y']
    [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (Z Z' : Type) [Fintype Z]
    [DecidableEq Z] [Fintype Z'] [DecidableEq Z'] (GS : Frame k S.rank Z') (GT : Frame k T.rank Z)
    (ψ : AddChar (AF D.host.F) ℂ) :
    ∀ Tm, p.IsModel ψ FS FT Tm → ∃ Tm', p.IsModel ψ GS GT Tm' ∧
      ∀ (Φ : SB (Matrix Y Y' k)) (Φ' : SB (Matrix Z Z' k)),
        (∀ x, Φ.1 x = Φ'.1 (GT.γ * FT.β * x * (FS.γ * GS.β))) → Tm' Φ' = Tm Φ := by
  intro Tm hTm
  refine ⟨Tm.comp (pull FS FT GS GT), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro Φ'
    exact hTm.theta _
  · intro x Φ' Φ'' h
    have := hTm.trans (chg GS GT FS FT x) (pull FS FT GS GT Φ') (pull FS FT GS GT Φ'') (by
      intro t
      change Φ''.1 (chg FS FT GS GT t) = Φ'.1 (chg FS FT GS GT (t + chg GS GT FS FT x))
      rw [h, chg_add, chg_inv])
    simpa [LinearMap.comp_apply, up_chg, chg_inv] using this
  · intro y hy Φ' Φ'' h
    have := hTm.modul y hy (pull FS FT GS GT Φ') (pull FS FT GS GT Φ'') (by
      intro t
      change Φ''.1 (chg FS FT GS GT t) = ψ (symplO S T (p.up FS FT t) y) * Φ'.1 (chg FS FT GS GT t)
      rw [h, up_chg])
    simpa [LinearMap.comp_apply] using this
  · intro Φ Φ' h
    change Tm (pull FS FT GS GT Φ') = Tm Φ
    congr 1
    exact Subtype.ext (funext fun x => (h x).symm)

end GlobalTheory.LocMod.Place
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsInjectiveModel
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil ValuativeRel GlobalTheory.LocMod Filter
open GlobalTheory.PlaceModel (half mem_half isHalf_iff heisL heisL_half heisL_comm hO_smul_left infPart_half)
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.LocMod.Inhab

namespace GlobalTheory.LocMod.Exist

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)

theorem e_mul_ι (x : k) : p.e * p.ι x = p.ι x := by rw [← p.ι_π, p.π_ι]

variable {Y Y' : Type} [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] {S T : HSp D}
  (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y)

def loc {m n : Type} (a : Matrix m n D.host.E) : Matrix m n k := a.map (p.π.comp (incA D))

theorem loc_gram_mul (V : HSp D) : loc p V.gram * loc p V.gram⁻¹ = 1 := by
  rw [loc, loc, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ (gram_det_ne V).isUnit, Matrix.map_one _ (map_zero _) (map_one _)]

theorem loc_mul_gram (V : HSp D) : loc p V.gram⁻¹ * loc p V.gram = 1 := mul_eq_one_comm.1 (loc_gram_mul p V)

def dual (b : Matrix Y Y' k) : WO S T :=
  (loc p S.gram * FS.β * bᵀ * FT.γ * loc p T.gram⁻¹)ᵀ.map fun z => cA D (p.ι z)

theorem up_mem (x : Matrix Y Y' k) : p.up FS FT x ∈ half S T p.e :=
  (isHalf_iff S T).1 fun _ _ => e_mul_ι p _

theorem dual_mem (b : Matrix Y Y' k) : dual p FS FT b ∈ half S T (cA D p.e) :=
  (isHalf_iff S T).1 fun _ _ => by
    simp only [dual, Matrix.map_apply]
    rw [← map_mul, e_mul_ι]

theorem up_add (x y : Matrix Y Y' k) : p.up FS FT (x + y) = p.up FS FT x + p.up FS FT y := by
  ext i j
  simp only [Place.up, Matrix.mul_add, Matrix.add_mul, Matrix.map_apply, Matrix.add_apply, map_add (f := _)]

theorem dual_add (x y : Matrix Y Y' k) : dual p FS FT (x + y) = dual p FS FT x + dual p FS FT y := by
  ext i j
  simp only [dual, Matrix.mul_add, Matrix.add_mul, Matrix.transpose_add, Matrix.map_apply, Matrix.add_apply, map_add (f := _)]

theorem up_zero : p.up FS FT 0 = 0 := by simpa using up_add p FS FT 0 0

theorem dual_zero : dual p FS FT 0 = 0 := by simpa using dual_add p FS FT 0 0

theorem continuous_up : Continuous (p.up FS FT) :=
  ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).matrix_map p.cont_ι

theorem continuous_dual : Continuous (dual p FS FT) :=
  ((((continuous_const.matrix_mul continuous_id.matrix_transpose).matrix_mul continuous_const).matrix_mul
    continuous_const).matrix_transpose).matrix_map ((GlobalTheory.DualPairCompare.continuous_cA D).comp p.cont_ι)

theorem π_hO (x y : WO S T) : p.π (hO S T x y) = Matrix.trace
    (loc p S.gram⁻¹ * (Matrix.map y fun z => p.π (cA D z))ᵀ * loc p T.gram * Matrix.map x p.π) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hO, map_sum, map_mul, Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul, loc, Matrix.map_apply,
    Matrix.transpose_apply, RingHom.comp_apply]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun c _ => Finset.sum_comm).trans Finset.sum_comm

theorem π_hO_dual (t b : Matrix Y Y' k) : p.π (hO S T (p.up FS FT t) (dual p FS FT b)) = ∑ r, ∑ q, b r q * t r q := by
  have h1 : (Matrix.map (dual p FS FT b) fun z => p.π (cA D z)) = (loc p S.gram * FS.β * bᵀ * FT.γ * loc p T.gram⁻¹)ᵀ := by
    ext i j
    simp only [dual, Matrix.map_apply, cA_cA, p.π_ι]
  have h2 : Matrix.map (p.up FS FT t) p.π = FT.β * t * FS.γ := by
    ext i j
    simp only [Place.up, Matrix.map_apply, p.π_ι]
  rw [π_hO, h1, h2, Matrix.transpose_transpose]
  simp only [← Matrix.mul_assoc]
  rw [loc_mul_gram, Matrix.one_mul, Matrix.mul_assoc _ _ (loc p T.gram), loc_mul_gram, Matrix.mul_one,
    Matrix.mul_assoc _ _ FT.β, FT.γβ, Matrix.mul_one, Matrix.trace_mul_comm]
  simp only [← Matrix.mul_assoc]
  rw [FS.γβ, Matrix.one_mul, Finset.sum_comm]
  rfl

theorem exists_dual {y : WO S T} (hy : IsHalf (cA D p.e) y) : ∃ b, dual p FS FT b = y := by
  refine ⟨(FS.γ * loc p S.gram⁻¹ * (Matrix.map y fun z => p.π (cA D z))ᵀ * loc p T.gram * FT.β)ᵀ, ?_⟩
  rw [dual, Matrix.transpose_transpose]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ FS.β, FS.βγ, Matrix.mul_one, loc_gram_mul, Matrix.one_mul, Matrix.mul_assoc _ FT.β, FT.βγ,
    Matrix.mul_one, Matrix.mul_assoc, loc_gram_mul, Matrix.mul_one, Matrix.transpose_transpose]
  ext i j
  simp only [Matrix.map_apply, p.ι_π, map_mul, cA_cA]
  exact hy i j

theorem char_sympl {ψ : AddChar (AF D.host.F) ℂ} {ψk : AddChar k Circle} (h : p.IsChar ψ ψk) (t b : Matrix Y Y' k) :
    ψ (symplO S T (p.up FS FT t) (dual p FS FT b)) = pairing ψk t b := by
  rw [pairing, ← π_hO_dual p FS FT, h, p.ι_π, ← hO_smul_left, (mem_half S T).1 (up_mem p FS FT t)]
  rfl

def thetaSub (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) : Submodule ℂ (WO S T → ℂ) where
  carrier := {f | IsThetaFunO ψ S T f}
  zero_mem' := GlobalTheory.OrientedHeis.theta_zero
  add_mem' := GlobalTheory.OrientedHeis.theta_add
  smul_mem' c _ h := GlobalTheory.OrientedHeis.theta_smul c h

end GlobalTheory.LocMod.Exist
end
end
