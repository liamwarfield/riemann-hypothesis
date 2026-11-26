module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureThird
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledSpaceMaximalLevelLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSeesawTensorMapPolynomialFockVector
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InducedSectionZFinite

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjIntertwinerPointValueSobolevContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjIntertwinerPointValueSobolevContinuous
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjRowCont

theorem reg_star {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (g : X.B.I.GA) (φ : L2X X) :
    X.B.R g (star φ) = star (X.B.R g φ) := by
  have := X.B.sf
  have := X.B.haar
  have := Formalism.MainNotions.LeviCoordinates.rr_muA_left X.B.I X.B.μf
  obtain ⟨-, hr, -⟩ := GlobalTheory.AdelicUnimod.adelic_unimodular X.B.I X.B.μf
  have hP : ∀ a : X.B.I.GA, Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) a := fun a => ⟨measurable_mul_const a, hr a⟩
  obtain ⟨h1, h2⟩ := Formalism.L2.SG.Pf.rp_map (Formalism.MainNotions.LeviCoordinates.rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec) (hP g) (hP g⁻¹)
  have e1 := X.B.R_spec g (star φ)
  have e2 := X.B.R_spec g φ
  have e3 : ∀ᵐ x ∂(muX X), ((star φ : L2X X) : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * g)) =
      star ((φ : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * g))) := by
    refine ae_of_ae_map (p := fun y => ((star φ : L2X X) : X.B.I.GA → ℂ) y = star ((φ : X.B.I.GA → ℂ) y)) h1 ?_
    rw [h2]
    filter_upwards [Lp.coeFn_star φ] with y hy
    rw [hy]
    rfl
  apply Lp.ext
  filter_upwards [e1, e2, e3, Lp.coeFn_star (X.B.R g φ)] with x a1 a2 a3 a4
  rw [a1, a4, Pi.star_apply, a2]
  exact a3

theorem iotaX_rat_iff {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (g : GA D (D.sp.Y 0)) : g ∈ GQ (D.sp.Y 0) ↔ iotaX X h g ∈ X.B.I.GFset := by
  have k : ∀ {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA), x ∈ I.GFset ↔ castGA e x ∈ I'.GFset := by
    intro I I' e x
    subst e; rfl
  exact (Formalism.IndefR.RationalEmbedding.iota_rat D g).trans (k h.symm _)

theorem exists_conj_multilinear {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {S : D.what₂.Tau → SPar}
    (M : DSModel (D.sp.Y 0) S) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (Φ : X.B.Hs →L[ℂ] L2X X) :
    ∃ Ψ : ContinuousMultilinearMap ℂ M.H (L2X X), ∀ y,
      Ψ y = star (Φ (X.B.tens (Equiv.piCongrLeft X.B.H X.pl.symm fun τ => c τ (y τ)))) := by
  obtain ⟨m, hm, -⟩ := GlobalTheory.exists_continuousMultilinearMap_of_inner_prod (H := X.B.H) X.B.tens
    X.B.tens_spec.1 X.B.tens_spec.2.2
  let C : (∀ τ, M.H τ) → ∀ v, X.B.H v := fun y => Equiv.piCongrLeft X.B.H X.pl.symm (fun τ => c τ (y τ))
  have hC : ∀ y τ, C y (X.pl.symm τ) = c τ (y τ) := fun y τ => Equiv.piCongrLeft_apply_apply _ _ _ _
  have hCu : ∀ y τ a, C (Function.update y τ a) = Function.update (C y) (X.pl.symm τ) (c τ a) := by
    intro y τ a
    rw [← GlobalTheory.ConjRowMult.piCongrLeft_update]
    refine congrArg (Equiv.piCongrLeft X.B.H X.pl.symm) (funext fun τ' => ?_)
    exact Function.apply_update (fun i (s : M.H i) => c i s) y τ a τ'
  have hCc : Continuous C := by
    refine continuous_pi fun v => ?_
    obtain ⟨τ, rfl⟩ := X.pl.symm.surjective v
    simp only [hC]
    exact (c τ).continuous.comp (continuous_apply τ)
  let Ψ₀ : MultilinearMap (RingHom.id ℂ) M.H (L2X X) := MultilinearMap.mk' (fun y => conjL (muX X) (Φ (m (C y))))
    (fun y τ a b => by rw [hCu, hCu, hCu, map_add (f := _), m.map_update_add, map_add (f := _), map_add (f := _)])
    (fun y τ a b => by
      rw [hCu, hCu, LinearIsometryEquiv.map_smulₛₗ, m.map_update_smul, map_smul, LinearIsometryEquiv.map_smulₛₗ,
        starRingEnd_self_apply]
      rfl)
  refine ⟨⟨Ψ₀, (conjL (muX X)).continuous.comp (Φ.continuous.comp (m.cont.comp hCc))⟩, fun y => ?_⟩
  show star (Φ (m (C y))) = _
  rw [hm]


set_option maxHeartbeats 1000000 in
theorem conjMap_cont : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → GlobalTheory.Core.Mi.IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ (τ : D.what₂.Tau) (v : M.Vec) (x : GA D (D.sp.Y 0)), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt (D.sp.Y 0) τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = GlobalTheory.ConjRowMult.conjMap X M c Φ h t (Function.update v τ w) x := by
  intro _ D X h θ S M J χ t c _ hθ _ hE _ hc Φ hΦ hrep τ₀ v₀ x₀
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (D.sp.Y 0)
  obtain ⟨hf, -, hat, -⟩ := GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D X h θ hθ hE
  obtain ⟨-, hcomm, g, hg, hfix⟩ := GlobalTheory.IdemProj.re_orth_proj X.B
  have := X.B.sf
  have := X.B.haar
  let T : GA D (D.sp.Y 0) ≃* X.B.I.GA := (iotaX X h).toMulEquiv
  have hT : Continuous T := (iotaX X h).continuous
  have hT' : Continuous T.symm := (iotaX X h).symm.continuous
  obtain ⟨μ, ρ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    GlobalTheory.TensRep.exists_transport X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec T hT hT'
  obtain ⟨U, hU, hUg⟩ := h11 g hg
  have hA : Φ ∈ X.B.I.HomS X.B.σs X.B.μf X.B.fund X.B.R := by
    obtain ⟨A, hA, rfl⟩ := hΦ
    intro g
    show (X.B.Re.comp A).comp (X.B.σs g) = (X.B.R (g, 1)).comp (X.B.Re.comp A)
    rw [ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  have hlev : ∀ k ∈ X.B.I.Kg g, ∀ w, X.B.R (1, k) (Φ w) = Φ w := by
    obtain ⟨A, -, rfl⟩ := hΦ
    intro k hk w
    exact congrArg (fun C : L2X X →L[ℂ] L2X X => C (A w)) (hfix k hk)
  obtain ⟨Ψ, hΨ⟩ := exists_conj_multilinear X M c Φ
  obtain ⟨N, hN1, hN2, hN3⟩ := GlobalTheory.TensRep.exists_mmap (ι := fun v x => X.B.I.ext v (T x)) hθ M h1 h2 h5 h6 h7 h8 h9
    (fun γ hγ v => h10 γ ((iotaX_rat_iff X h γ).1 hγ) v) hU Ψ
    (fun τ a ha y => by
      obtain ⟨q1, q2, -⟩ := hat τ a ha
      rw [h3, hΨ, hΨ, reg_star]
      congr 1
      refine GlobalTheory.TensRep.hom_tens X.B.I X.B.tens_spec hA q1 _ _ fun v => ?_
      obtain ⟨τ', rfl⟩ := X.pl.symm.surjective v
      rw [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]
      by_cases e : τ' = τ
      · subst e
        rw [Function.update_self]
        exact hc _ a ha _
      · rw [Function.update_of_ne e]
        have q : (iotaX X h (atTau θ (D.sp.Y 0) τ a)).1 (X.pl.symm τ') = 1 := q2 _ (X.pl.symm.injective.ne e)
        rw [q]
        have : X.B.σ (X.pl.symm τ') 1 = 1 := (X.ds _).2.2.1.1.1
        show _ = X.B.σ (X.pl.symm τ') 1 _
        rw [this]
        rfl)
    (fun y k hk hk' => by
      rw [h3, hΨ, reg_star]
      have e : T k = (1, (T k).2) := Prod.ext ((hf k).1 hk') rfl
      rw [e, hlev _ (hUg k hk)])
  have key : ∀ (u : M.Vec) y, GlobalTheory.ConjRowMult.conjMap X M c Φ h t u y = N u (y * t⁻¹) := by
    intro u y
    have r1 : GlobalTheory.Dec.IsContRep X.B (Ψ fun τ => (u τ : M.H τ)) (fun z => N u (T.symm z)) := by
      refine GlobalTheory.RepSmooth.isContRep_of_ae X.B ((hN2 u).3.comp hT') (fun γ hγ z => ?_) ?_
      · rw [map_mul]
        refine (hN2 u).1 _ ((iotaX_rat_iff X h _).2 ?_) _
        have : iotaX X h (T.symm γ) = γ := T.apply_symm_apply γ
        rwa [this]
      · filter_upwards [h4 _ (hN1 u)] with z hz
        rw [← hz, T.apply_symm_apply]
    have r2 : Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u)))
        (fun z => star (N u (T.symm z))) := by
      refine ⟨r1.1.star, fun γ hγ z => congrArg star (r1.2.1 γ hγ z), ?_⟩
      have r3 := r1.2.2
      rw [hΨ] at r3
      filter_upwards [r3, Lp.coeFn_star (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u)))] with z a1 a2
      rw [← a1]
      exact (star_star _).symm.trans (congrArg star a2.symm)
    rw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.contRepL_spec X r2, star_star]
    exact congrArg (N u) (T.symm_apply_apply _)
  obtain ⟨ℓ, hℓ1, hℓ2⟩ := hN3 τ₀ v₀ (x₀ * t⁻¹)
  exact ⟨ℓ, hℓ1, fun w => (hℓ2 w).trans (key _ _).symm⟩

end GlobalTheory.ConjRowCont

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjIntertwinerPointValueSobolevContinuousStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjIntertwiner_pointValue_sobolevContinuous : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → GlobalTheory.Core.Mi.IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ (τ : D.what₂.Tau) (v : M.Vec) (x : GA D (D.sp.Y 0)), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt (D.sp.Y 0) τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = GlobalTheory.ConjRowMult.conjMap X M c Φ h t (Function.update v τ w) x := by
  first | exact @GlobalTheory.ConjRowCont.conjMap_cont | exact GlobalTheory.ConjRowCont.conjMap_cont | (intros; apply GlobalTheory.ConjRowCont.conjMap_cont <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorOrthogonalBoxProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorOrthogonalBoxProduct
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox
open GlobalTheory.OrientedHeis GlobalTheory.Core.Rk.FockBox

noncomputable section

namespace GlobalTheory.Core.Rk.FockBoxT

theorem killed_of_leibniz₂ {P₁ P₂ Q U₁ U₂ V : Type} [Zero U₁] [Zero U₂] [AddCommGroup V] (a₁ : P₁ → U₁ → U₁)
    (a₂ : P₂ → U₂ → U₂) (b : Q → V → V) (T₁ : U₁ → Prop) (T₂ : U₂ → Prop)
    (TV : V → Prop) (δ : U₁ → U₂ → V) (c₁ : Q → P₁) (c₂ : Q → P₂) (ha₁ : ∀ p f, T₁ f → T₁ (a₁ p f))
    (ha₂ : ∀ p f, T₂ f → T₂ (a₂ p f)) (hb : ∀ q f, TV f → TV (b q f))
    (hadd : ∀ q f g, TV f → TV g → b q (f + g) = b q f + b q g) (hb0 : ∀ q, b q 0 = 0)
    (hδ : ∀ f g, T₁ f → T₂ g → TV (δ f g)) (h1 : ∀ g, δ 0 g = 0) (h2 : ∀ f, δ f 0 = 0)
    (hL : ∀ q f g, T₁ f → T₂ g → b q (δ f g) = δ (a₁ (c₁ q) f) g + δ f (a₂ (c₂ q) g)) (N : ℕ) :
    ∀ (N₁ N₂ : ℕ) (f : U₁) (g : U₂), N₁ + N₂ ≤ N → T₁ f → T₂ g →
      (∀ l : List P₁, l.length = N₁ → l.foldr a₁ f = 0) → (∀ l : List P₂, l.length = N₂ → l.foldr a₂ g = 0) →
      ∀ l : List Q, l.length = N → l.foldr b (δ f g) = 0 := by
  have w0 : ∀ l : List Q, l.foldr b 0 = 0 := fun l => by
    induction l with
    | nil => rfl
    | cons q l ih => rw [List.foldr_cons, ih, hb0]
  have wT : ∀ (l : List Q) f, TV f → TV (l.foldr b f) := fun l f hf => by
    induction l with
    | nil => exact hf
    | cons q l ih => exact hb _ _ ih
  have wadd : ∀ (l : List Q) f g, TV f → TV g → l.foldr b (f + g) = l.foldr b f + l.foldr b g := fun l f g hf hg => by
    induction l with
    | nil => rfl
    | cons q l ih => rw [List.foldr_cons, ih, hadd _ _ _ (wT l f hf) (wT l g hg)]; rfl
  have step : ∀ {P U : Type} [Zero U] (a : P → U → U) (M : ℕ) (f : U) (p : P),
      (∀ l : List P, l.length = M + 1 → l.foldr a f = 0) →
      ∀ l : List P, l.length = M → l.foldr a (a p f) = 0 := fun a M f p h l hl => by
    have := h (l ++ [p]) (by simp [hl])
    rwa [List.foldr_append] at this
  induction N with
  | zero =>
    intro N₁ N₂ f g hN _ _ k₁ _ l _
    have : f = 0 := k₁ [] (by simp; omega)
    rw [this, h1, w0]
  | succ N ih =>
    intro N₁ N₂ f g hN hf hg k₁ k₂ l hl
    rcases N₁ with _ | M₁
    · have : f = 0 := k₁ [] rfl
      rw [this, h1, w0]
    rcases N₂ with _ | M₂
    · have : g = 0 := k₂ [] rfl
      rw [this, h2, w0]
    obtain rfl | ⟨l', q, rfl⟩ := l.eq_nil_or_concat'
    · simp at hl
    have hl' : l'.length = N := by simpa using hl
    rw [List.foldr_append, List.foldr_cons, List.foldr_nil, hL q f g hf hg,
      wadd _ _ _ (hδ _ _ (ha₁ _ _ hf) hg) (hδ _ _ hf (ha₂ _ _ hg)),
      ih M₁ (M₂ + 1) _ _ (by omega) (ha₁ _ _ hf) hg (step _ _ _ _ k₁) k₂ l' hl',
      ih (M₁ + 1) M₂ _ _ (by omega) hf (ha₂ _ _ hg) k₁ (step _ _ _ _ k₂) l' hl', add_zero]

variable {D : D7} {θ : InfFam D} {ψ : AddChar (AF D.host.F) ℂ}

theorem lineAt_mul_left (hθ : IsInfFam θ) {k m n : ℕ} (p : Mx D k m) (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) :
    lineAt θ τ (Formalism.IndefR.Datum.compAt θ τ p * z) t = (HMul.hMul p (lineAt θ τ z t) : Mx D k n) := by
  have hL := isLineAt_lineAt hθ τ z
  let L : ℝ →+ Mx D k n :=
    { toFun := fun t => HMul.hMul p (lineAt θ τ z t)
      map_zero' := by rw [AddMonoidHom.map_zero, Matrix.mul_zero]
      map_add' := fun s t => by rw [AddMonoidHom.map_add (f := _), Matrix.mul_add] }
  have hL' : IsLineAt θ τ (Formalism.IndefR.Datum.compAt θ τ p * z) L := by
    refine ⟨continuous_const.matrix_mul hL.1, fun t => ?_, fun t τ' => ?_⟩
    · show (HMul.hMul p (lineAt θ τ z t) : Mx D k n).map (finPart D) = 0
      rw [Matrix.map_mul, hL.2.1, Matrix.mul_zero]
    · show Formalism.IndefR.Datum.compAt θ τ' (HMul.hMul p (lineAt θ τ z t) : Mx D k n) = _
      rw [GlobalTheory.OrientedHeis.compAt_mul, hL.2.2]
      split_ifs with e
      · rw [e, Matrix.mul_smul]
      · rw [Matrix.mul_zero]
  rw [GlobalTheory.RealLineAt.lineAt_unique D θ hθ _ _ τ _ _ _ (isLineAt_lineAt hθ τ _) hL']
  rfl

variable {A B W H : HSp D} (o : OrthDec B W H)

theorem compAt_pA (hθ : IsInfFam θ) (τ : D.what₂.Tau) :
    Formalism.IndefR.Datum.compAt θ τ o.pA = o.qA.map (tauE D τ) := by
  ext i j
  exact GlobalTheory.FockCompare.comp_incA hθ τ _

theorem compAt_pB (hθ : IsInfFam θ) (τ : D.what₂.Tau) :
    Formalism.IndefR.Datum.compAt θ τ o.pB = o.qB.map (tauE D τ) := by
  ext i j
  exact GlobalTheory.FockCompare.comp_incA hθ τ _

theorem dRho_boxT (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (z : Matrix (Fin B.rank) (Fin A.rank) ℂ) {f : WO A W → ℂ} {g : WO A H → ℂ} (hf : IsThetaFunO ψ A W f)
    (hg : IsThetaFunO ψ A H g) :
    Formalism.IndefR.Datum.dRho (heisO ψ A B) θ τ z (o.boxT A f g) =
      o.boxT A (Formalism.IndefR.Datum.dRho (heisO ψ A W) θ τ (o.qA.map (tauE D τ) * z) f) g +
        o.boxT A f (Formalism.IndefR.Datum.dRho (heisO ψ A H) θ τ (o.qB.map (tauE D τ) * z) g) := by
  funext x
  have d := (hasDerivAt_dRho hθ hψ τ (o.qA.map (tauE D τ) * z) hf (o.resT A x).1).mul
    (hasDerivAt_dRho hθ hψ τ (o.qB.map (tauE D τ) * z) hg (o.resT A x).2)
  simp only [map_zero, heisO_zero] at d
  refine Eq.trans ?_ d.deriv
  unfold Formalism.IndefR.Datum.dRho
  congr 1
  funext t
  rw [o.heisO_boxT, Pi.mul_apply, ← compAt_pA o hθ, ← compAt_pB o hθ, lineAt_mul_left hθ, lineAt_mul_left hθ]
  rfl

theorem qA_sumMat (sW : RealMat W) (sH : RealMat H) (τ : D.what₂.Tau) :
    o.qA.map (tauE D τ) * sumMat o sW sH τ = sW τ * o.qA.map (tauE D τ) := by
  simp only [sumMat_apply, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.map_mul, o.qA_iA, o.qA_iB,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), Matrix.one_mul, Matrix.zero_mul, add_zero]

theorem qB_sumMat (sW : RealMat W) (sH : RealMat H) (τ : D.what₂.Tau) :
    o.qB.map (tauE D τ) * sumMat o sW sH τ = sH τ * o.qB.map (tauE D τ) := by
  simp only [sumMat_apply, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.map_mul, o.qB_iA, o.qB_iB,
    Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_zero _ (map_zero _), Matrix.one_mul, Matrix.zero_mul, zero_add]

theorem mul_cplxO {k m n : ℕ} {q : Matrix (Fin k) (Fin m) ℂ} {s : Matrix (Fin m) (Fin m) ℂ}
    {s' : Matrix (Fin k) (Fin k) ℂ} (h : q * s = s' * q) (r : Matrix (Fin n) (Fin n) ℂ) (z : Matrix (Fin m) (Fin n) ℂ) :
    q * cplxO r s z = cplxO r s' (q * z) := by
  unfold cplxO
  rw [Matrix.mul_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h, Matrix.mul_assoc s']

theorem annih_boxT (hθ : IsInfFam θ) (hψ : IsStdChar D ψ (-1)) (τ : D.what₂.Tau)
    (s : Matrix (Fin A.rank) (Fin A.rank) ℂ) (sW : RealMat W) (sH : RealMat H)
    (z : Matrix (Fin B.rank) (Fin A.rank) ℂ) {f : WO A W → ℂ} {g : WO A H → ℂ} (hf : IsThetaFunO ψ A W f)
    (hg : IsThetaFunO ψ A H g) :
    annih (heisO ψ A B) θ τ (cplxO s (sumMat o sW sH τ)) z (o.boxT A f g) =
      o.boxT A (annih (heisO ψ A W) θ τ (cplxO s (sW τ)) (o.qA.map (tauE D τ) * z) f) g +
        o.boxT A f (annih (heisO ψ A H) θ τ (cplxO s (sH τ)) (o.qB.map (tauE D τ) * z) g) := by
  unfold annih
  rw [dRho_boxT o hθ hψ τ _ hf hg, dRho_boxT o hθ hψ τ _ hf hg, mul_cplxO (qA_sumMat o sW sH τ),
    mul_cplxO (qB_sumMat o sW sH τ)]
  funext x
  simp only [OrthDec.boxT, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem isFockVec_boxT : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B W H : HSp D) (o : OrthDec B W H) (sA : RealMat A) (sW : RealMat W) (sH : RealMat H), IsStdChar D ψ (-1) → IsInfFam θ → ∀ Φ Φ', IsFockVec ψ θ A W sA sW Φ → IsFockVec ψ θ A H sA sH Φ' → IsFockVec ψ θ A B sA (sumMat o sW sH) (o.boxT A Φ Φ') := by
  intro D ψ θ A B W H o sA sW sH hψ hθ Φ₁ Φ₂ ⟨t₁, N₁, k₁⟩ ⟨t₂, N₂, k₂⟩
  have hT : ∀ (S : HSp D) τ J z f, IsThetaFunO ψ A S f → IsThetaFunO ψ A S (annih (heisO ψ A S) θ τ J z f) :=
    fun S τ J z f hf => theta_add (theta_dRho hθ hψ τ z hf) (theta_smul _ (theta_dRho hθ hψ τ _ hf))
  refine ⟨o.isThetaFunO_boxT t₁ t₂, N₁ + N₂, ?_⟩
  refine killed_of_leibniz₂ (P₁ := D.what₂.Tau × Matrix (Fin W.rank) (Fin A.rank) ℂ)
    (P₂ := D.what₂.Tau × Matrix (Fin H.rank) (Fin A.rank) ℂ)
    (Q := D.what₂.Tau × Matrix (Fin B.rank) (Fin A.rank) ℂ)
    (fun p f => annih (heisO ψ A W) θ p.1 (cplxO (sA p.1) (sW p.1)) p.2 f)
    (fun p f => annih (heisO ψ A H) θ p.1 (cplxO (sA p.1) (sH p.1)) p.2 f)
    (fun p f => annih (heisO ψ A B) θ p.1 (cplxO (sA p.1) (sumMat o sW sH p.1)) p.2 f)
    (IsThetaFunO ψ A W) (IsThetaFunO ψ A H) (IsThetaFunO ψ A B) (o.boxT A)
    (fun q => (q.1, o.qA.map (tauE D q.1) * q.2)) (fun q => (q.1, o.qB.map (tauE D q.1) * q.2))
    (fun p f hf => hT W _ _ _ f hf) (fun p f hf => hT H _ _ _ f hf) (fun p f hf => hT B _ _ _ f hf)
    (fun q f g hf hg => ?_) (fun q => ?_)
    (fun f g hf hg => o.isThetaFunO_boxT hf hg) (fun g => ?_) (fun f => ?_)
    (fun q f g hf hg => annih_boxT o hθ hψ q.1 (sA q.1) sW sH q.2 hf hg)
    _ N₁ N₂ Φ₁ Φ₂ le_rfl t₁ t₂ k₁ k₂
  · simp only [annih]
    rw [GlobalTheory.Core.Rk.FockBox.dRho_add hθ hψ _ _ hf hg, GlobalTheory.Core.Rk.FockBox.dRho_add hθ hψ _ _ hf hg, smul_add]
    abel
  · funext x
    simp [annih, Formalism.IndefR.Datum.dRho, heisO]
  · funext x
    simp [OrthDec.boxT]
  · funext x
    simp [OrthDec.boxT]

end GlobalTheory.Core.Rk.FockBoxT

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPolynomialFockThetaVectorOrthogonalBoxProductStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPolynomialFockThetaVector_orthogonalBoxProduct : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B W H : HSp D) (o : OrthDec B W H) (sA : RealMat A) (sW : RealMat W) (sH : RealMat H), IsStdChar D ψ (-1) → IsInfFam θ → ∀ Φ Φ', IsFockVec ψ θ A W sA sW Φ → IsFockVec ψ θ A H sA sH Φ' → IsFockVec ψ θ A B sA (sumMat o sW sH) (o.boxT A Φ Φ') := by
  first | exact @GlobalTheory.Core.Rk.FockBoxT.isFockVec_boxT | exact GlobalTheory.Core.Rk.FockBoxT.isFockVec_boxT | (intros; apply GlobalTheory.Core.Rk.FockBoxT.isFockVec_boxT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResidueSupportSinglePlaceToConjugatePairSlotStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResidueSupportSinglePlaceToConjugatePairPosition
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjSlot

theorem resS_sigInt_eq_zero_iff (D : D7) (PP : Pl D.host.E) (s : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    resS D.host.F PP (sigInt (instOf D) s) = 0 ↔ resS D.host.F (conjPl PP) s = 0 :=
  resS_sigS_eq_zero_iff (instOf D).cm (isConjPl_conjPl PP).symm s

theorem mem_conjPl {E : Type} [Field E] [NumberField E] [StarRing E] (PP : Pl E) (a : 𝓞 E) :
    a ∈ (conjPl PP).asIdeal ↔ starO a ∈ PP.asIdeal := Iff.rfl

theorem natCast_mem_conjPl {E : Type} [Field E] [NumberField E] [StarRing E] (PP : Pl E) (N : ℕ) :
    (N : 𝓞 E) ∈ (conjPl PP).asIdeal ↔ (N : 𝓞 E) ∈ PP.asIdeal := by
  show starOHom (N : 𝓞 E) ∈ PP.asIdeal ↔ _
  rw [map_natCast]

theorem isConjPl_conjPl_lev (D : D7) (PP : Pl D.host.E) : Formalism.IndefR.Lev.IsConjPl (D := D) PP (conjPl PP) :=
  fun c hc => ⟨starO c, by rw [mem_conjPl, starO_starO]; exact hc, rfl⟩

theorem intersection_update_fsHerm_neg_one : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP') → ∀ R : Formalism.L2.Herm.intAf D.host.F D.host.E → Prop, (∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ Q' : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q'.asIdeal → Q' ≠ Q → resS D.host.F Q' s = 0) ∧ R s) → ∀ PP ∈ Pg, (∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ PP' ∈ Pg, (PP' ≠ PP → resS D.host.F PP' s = 0) ∧ resS D.host.F PP' (sigInt (instOf D) s) = 0) ∧ R s) ∧ ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ PP' ∈ Pg, resS D.host.F PP' s = 0 ∧ (PP' ≠ PP → resS D.host.F PP' (sigInt (instOf D) s) = 0)) ∧ R s := by
  intro D Pg hg hconj R hR PP hPP
  have hne : ∀ P ∈ Pg, ∀ P' ∈ Pg, conjPl P ≠ P' := fun P hP P' hP' h =>
    hconj P hP P' hP' (h ▸ isConjPl_conjPl_lev D P)
  constructor
  · obtain ⟨s, hs, hRs⟩ := hR PP (hg PP hPP)
    refine ⟨s, fun P hP => ⟨fun h => hs P (hg P hP) h, ?_⟩, hRs⟩
    rw [resS_sigInt_eq_zero_iff]
    exact hs _ ((natCast_mem_conjPl P _).2 (hg P hP)) (hne P hP PP hPP)
  · obtain ⟨s, hs, hRs⟩ := hR (conjPl PP) ((natCast_mem_conjPl PP _).2 (hg PP hPP))
    refine ⟨s, fun P hP => ⟨hs P (hg P hP) (hne PP hPP P hP).symm, fun h => ?_⟩, hRs⟩
    rw [resS_sigInt_eq_zero_iff]
    refine hs _ ((natCast_mem_conjPl P _).2 (hg P hP)) fun e => h ?_
    rw [← conjPl_conjPl P, e, conjPl_conjPl]

end GlobalTheory.ConjSlot
end

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residueSupport_single_place_to_conjugatePair_position : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP') → ∀ R : Formalism.L2.Herm.intAf D.host.F D.host.E → Prop, (∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ Q' : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q'.asIdeal → Q' ≠ Q → resS D.host.F Q' s = 0) ∧ R s) → ∀ PP ∈ Pg, (∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ PP' ∈ Pg, (PP' ≠ PP → resS D.host.F PP' s = 0) ∧ resS D.host.F PP' (sigInt (instOf D) s) = 0) ∧ R s) ∧ ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ PP' ∈ Pg, resS D.host.F PP' s = 0 ∧ (PP' ≠ PP → resS D.host.F PP' (sigInt (instOf D) s) = 0)) ∧ R s := by
  first | exact @GlobalTheory.ConjSlot.intersection_update_fsHerm_neg_one | exact GlobalTheory.ConjSlot.intersection_update_fsHerm_neg_one | (intros; apply GlobalTheory.ConjSlot.intersection_update_fsHerm_neg_one <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorSourceRealPointCommuteHeisenbergComb
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorSourceRealPointCommuteHeisenbergComb
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.SeeSaw.RealComm

variable {D : D7}

theorem map_mul_gen {A B m n : Type} [CommRing A] [CommRing B] [Fintype n] (φ : A →+* B) (u : Matrix m n A) (g : Matrix n n A) :
    (u * g).map φ = u.map φ * g.map φ := Matrix.map_mul

theorem actO_real_fin (S T : HSp D) {z : GA D S} (hz : z ∈ GinfC S) {u : WO S T} (hu : u.map (infPart D) = 0) :
    actO S T z 1 u = u := by
  have h1 : Formalism.L2.Theta.mt T 1 = 1 := rfl
  have hz' : finHom S z⁻¹ = 1 := (GinfC S).inv_mem hz
  have h2 : (Formalism.L2.Theta.mt S z⁻¹).map (finPart D) = 1 := congrArg Units.val hz'
  rw [actO, h1, Matrix.one_mul]
  have h3 := map_mul_gen (finPart D) u (Formalism.L2.Theta.mt S z⁻¹)
  have h4 := map_mul_gen (infPart D) u (Formalism.L2.Theta.mt S z⁻¹)
  rw [h2, Matrix.mul_one] at h3
  rw [hu, Matrix.zero_mul, ← hu] at h4
  exact Matrix.ext fun i j => GlobalTheory.SplitScalar.adele_ext (congrFun (congrFun h4 i) j) (congrFun (congrFun h3 i) j)

theorem om_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ z ∈ GinfC S, ∀ c : WO S T →₀ ℂ, IsFinComb c → ∀ g : WO S T → ℂ, IsThetaFunO ψ S T g → om (z, 1) (comb ψ S T c g) = comb ψ S T c (om (z, 1) g) := by
  intro D ψ S T χS χT om H z hz c hc g hg
  unfold comb
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [map_smul, H.om_heis z 1 u g hg, actO_real_fin S T hz (hc u hu)]

end GlobalTheory.SeeSaw.RealComm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorSourceRealPointCommuteHeisenbergCombStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_sourceRealPoint_commute_heisenbergComb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ z ∈ GinfC S, ∀ c : WO S T →₀ ℂ, IsFinComb c → ∀ g : WO S T → ℂ, IsThetaFunO ψ S T g → om (z, 1) (comb ψ S T c g) = comb ψ S T c (om (z, 1) g) := by
  first | exact @GlobalTheory.SeeSaw.RealComm.om_comb | exact GlobalTheory.SeeSaw.RealComm.om_comb | (intros; apply GlobalTheory.SeeSaw.RealComm.om_comb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevOfMem
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ValMoveProof

theorem lev_of_mem {D : D7} (θ : InfFam D) {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S)
    (J : Set (GA D V)) (χ : GA D V → ℂ) (T : MMap M) (hT : T ∈ Mult θ M J χ) :
    ∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  induction hT using Submodule.span_induction with
  | mem x hx => exact hx.lev
  | zero => intros; simp
  | add x y _ _ hx hy =>
    intro v k hk g
    simp only [MultilinearMap.add_apply, Pi.add_apply, hx v k hk g, hy v k hk g, mul_add]
  | smul a x _ hx =>
    intro v k hk g
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hx v k hk g]
    ring

theorem valMove : ∀ D : D7, ValMove D := by
  intro D θ hθ V S M J χ
  refine ⟨?_, ?_⟩
  · intro G hG x k hk
    rw [mem_multT] at hG
    have h := lev_of_mem θ M J χ _ hG
    have e : ∀ f, G (PiTensorProduct.tprod ℂ f) = (PiTensorProduct.lift.symm G) f := fun f => by
      simp [PiTensorProduct.lift_symm]
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r f =>
      funext g
      simp only [rTrans, map_smul, Pi.smul_apply, smul_eq_mul, e, h f k hk g]
      ring
    | add x y hx hy =>
      funext g
      have hx' := congrFun hx g
      have hy' := congrFun hy g
      simp only [rTrans, map_add (f := _), Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hx' hy' ⊢
      rw [hx', hy', mul_add]
  · intro a ha v
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.realTranslation_cuspFormMaps_eq_smooth_linear_map D θ V S M hθ a ha
    exact ⟨σ v, fun G hG => (hσ J χ G hG v).symm⟩

end GlobalTheory.ValMoveProof

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralAdelePrescribedResiduesAndConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralAdelePrescribedResiduesAndConj
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.ConjResidueSurj
open GlobalTheory.IdemSupport

theorem sigInt_oToS {D : D7} (a : 𝓞 D.host.E) :
    sigInt (instOf D) (oToS D.host.F D.host.E a) = oToS D.host.F D.host.E (cO D a) :=
  Subtype.ext (Formalism.L2.SG.Pf.unitaryCongruence.sigA_inclE (instOf D) (a : D.host.E))

theorem exists_res_and_conj (D : D7) (Pg : Finset (Pl D.host.E))
    (h : ∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP')
    (u u' : ∀ PP : Pl D.host.E, kP PP) :
    ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ PP ∈ Pg,
      resS D.host.F PP s = u PP ∧ resS D.host.F PP (sigInt (instOf D) s) = u' PP := by
  classical
  choose a ha using fun PP : Pl D.host.E => Ideal.Quotient.mk_surjective (I := PP.asIdeal) (u PP)
  choose a' ha' using fun PP : Pl D.host.E => Ideal.Quotient.mk_surjective (I := PP.asIdeal) (u' PP)
  have hout : ∀ PP ∈ Pg, cP PP ∉ Pg := fun PP hPP h' =>
    h PP hPP _ h' ((isConjPl_iff _ _).2 rfl)
  let T : Finset (Pl D.host.E) := Pg ∪ Pg.image cP
  let x : Pl D.host.E → 𝓞 D.host.E := fun Q => if Q ∈ Pg then a Q else cO D (a' (cP Q))
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := T)
    (fun Q : Pl D.host.E => Q.asIdeal) (fun _ => 1) (fun Q _ => Q.prime)
    (fun Q _ Q' _ hne e => hne (HeightOneSpectrum.ext e)) (fun Q => x Q.1)
  refine ⟨oToS D.host.F D.host.E y, fun PP hPP => ⟨?_, ?_⟩⟩
  · have h1 := hy PP (Finset.mem_union_left _ hPP)
    rw [pow_one] at h1
    have h2 : x PP = a PP := if_pos hPP
    rw [resS_oToS, ← ha PP, ← h2]
    exact Ideal.Quotient.eq.2 h1
  · have h1 := hy (cP PP) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hPP))
    rw [pow_one] at h1
    have h2 : x (cP PP) = cO D (a' PP) := by
      have : x (cP PP) = cO D (a' (cP (cP PP))) := if_neg (hout PP hPP)
      rw [this, GlobalTheory.StdFrames.cP_cP]
    have h3 : y - cO D (a' PP) ∈ (cP PP).asIdeal := h2 ▸ h1
    rw [mem_cP, map_sub, cO_cO] at h3
    rw [sigInt_oToS, resS_oToS, ← ha' PP]
    exact Ideal.Quotient.eq.2 h3

end GlobalTheory.ConjResidueSurj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralAdelePrescribedResiduesAndConjStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralAdele_prescribed_residues_and_conj : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP') → ∀ u u' : ∀ PP : Pl D.host.E, kP PP, ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, ∀ PP ∈ Pg, resS D.host.F PP s = u PP ∧ resS D.host.F PP (sigInt (instOf D) s) = u' PP := by
  first | exact @GlobalTheory.ConjResidueSurj.exists_res_and_conj | exact GlobalTheory.ConjResidueSurj.exists_res_and_conj | (intros; apply GlobalTheory.ConjResidueSurj.exists_res_and_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SummableOfCount
noncomputable section

open scoped NNReal TensorProduct
open NumberField Matrix Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.Eis.Conv GlobalTheory.MixModel GlobalTheory.RegSW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GodementSectionReduction


open GlobalTheory.SummCount in
theorem summable_of_count (ι : Type) (n N : ℕ) (b C t : ℝ) (k : ι → Fin n → ℕ)
    (h : ι → ℝ) (hb : 1 < b) (ht : (N : ℝ) < t)
    (hh : ∀ q, 0 ≤ h q ∧ h q ≤ C * ∏ i, (b ^ k q i)⁻¹)
    (hT : ∀ (m : Fin n → ℕ) (T : Finset ι), (∀ q ∈ T, k q = m) →
      (T.card : ℝ) ≤ C * ∏ i, b ^ (N * m i)) :
    Summable fun q => h q ^ t := by
  have hb0 : 0 < b := zero_lt_one.trans hb
  have ht0 : 0 ≤ t := le_trans (Nat.cast_nonneg N) ht.le
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨q0⟩⟩
  · exact .of_finite
  have hP : ∀ m : Fin n → ℕ, 0 < ∏ i, (b ^ m i)⁻¹ := fun m => by positivity
  have hC : 0 ≤ C := (mul_nonneg_iff_of_pos_right (hP (k q0))).1 ((hh q0).1.trans (hh q0).2)
  set r := b ^ ((N : ℝ) - t) with hr
  have hr0 : 0 ≤ r := Real.rpow_nonneg hb0.le _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg hb (by linarith)
  set g : (Fin n → ℕ) → ℝ := fun m => C * C ^ t * ∏ i, r ^ m i with hg_def
  have hg0 : ∀ m, 0 ≤ g m := fun m => by
    simp only [hg_def]; positivity
  have hg : Summable g :=
    (summable_prod_fin_tuple (summable_geometric_of_lt_one hr0 hr1) (fun _ => pow_nonneg hr0 _)
      n).mul_left _
  have key : ∀ q, h q ^ t ≤ C ^ t * ∏ i, ((b ^ k q i)⁻¹) ^ t := fun q => by
    rw [Real.finsetProd_rpow _ _ (fun i _ => by positivity), ← Real.mul_rpow hC (hP _).le]
    exact Real.rpow_le_rpow (hh q).1 (hh q).2 ht0
  refine summable_of_sum_le (c := ∑' m, g m) (fun q => Real.rpow_nonneg (hh q).1 _) fun T => ?_
  rw [← Finset.sum_fiberwise_of_maps_to (g := k) (t := T.image k)
    (fun q hq => Finset.mem_image_of_mem k hq)]
  refine le_trans (Finset.sum_le_sum fun m _ => ?_) (hg.sum_le_tsum _ (fun m _ => hg0 m))
  calc ∑ q ∈ T with k q = m, h q ^ t
      ≤ ∑ q ∈ T with k q = m, C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t :=
        Finset.sum_le_sum fun q hq => by
          have := key q
          rwa [(Finset.mem_filter.1 hq).2] at this
    _ = ((T.filter (k · = m)).card : ℝ) * (C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (C * ∏ i, b ^ (N * m i)) * (C ^ t * ∏ i, ((b ^ m i)⁻¹) ^ t) :=
        mul_le_mul_of_nonneg_right (hT m _ fun q hq => (Finset.mem_filter.1 hq).2)
          (mul_nonneg (Real.rpow_nonneg hC _)
            (Finset.prod_nonneg fun i _ => Real.rpow_nonneg (by positivity) _))
    _ = g m := by
        simp only [hg_def, hr, ← pow_mul_inv_rpow_eq hb0 N, Finset.prod_mul_distrib]
        ring


open GlobalTheory.Eis.Conv.CovSkew in
theorem cover_adele (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : IsCMExt F E σ) : ∃ (Ω : Set (AF F ⊗[F] E)) (C : ℝ), IsCompact Ω ∧ ∀ m : ℕ, ∃ Y : Finset (AF F ⊗[F] E),
      (Y.card : ℝ) ≤ C * ((4 : ℝ) ^ Fintype.card (InfinitePlace F)) ^ m ∧ ∀ z : AF F ⊗[F] E, ∃ x : E, ∃ y ∈ Y, ∃ ω ∈ Ω,
        z = inclR (F := F) (AF F) x + y + (halfE F E).1 ^ m * ω := by
  classical
  haveI := hσ.1
  obtain ⟨Ω₀, C₀, hΩ₀, hcov⟩ := GlobalTheory.T.exists_adele_cover_mod_field_shrunk_compact F
  obtain ⟨δ, -, hsp⟩ := exists_delta F E σ hσ
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := isTopologicalRing_tens
  have hcont : Continuous fun p : AF F × AF F => psi (F := F) δ p.1 p.2 := by
    unfold psi
    fun_prop
  refine ⟨_, C₀ ^ 2, (hΩ₀.prod hΩ₀).image hcont, fun m => ?_⟩
  obtain ⟨Y, hY, hYc⟩ := hcov m
  refine ⟨(Y ×ˢ Y).image fun y => psi δ y.1 y.2, ?_, fun z => ?_⟩
  · refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
    rw [Finset.card_product, Nat.cast_mul]
    refine (mul_self_le_mul_self (Nat.cast_nonneg _) hY).trans (le_of_eq ?_)
    rw [show (4 : ℝ) = 2 * 2 by norm_num, mul_pow, mul_pow]
    ring
  · obtain ⟨u, v, rfl⟩ := exists_coords δ hsp z
    set c : AF F := algebraMap F (AF F) 2⁻¹ with hc
    have h2 : 2 * c = 1 := by
      rw [hc, ← map_ofNat (algebraMap F (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
    obtain ⟨x, y, hy, ω, hω, e⟩ := hYc (c * (u + v))
    obtain ⟨x', y', hy', ω', hω', e'⟩ := hYc (c * (v - u))
    refine ⟨(x - x') • (1 : E) + (x + x') • δ, _, Finset.mem_image.mpr ⟨(y, y'), Finset.mem_product.2 ⟨hy, hy'⟩, rfl⟩,
      _, ⟨(ω, ω'), ⟨hω, hω'⟩, rfl⟩, ?_⟩
    have : (halfE F E).1 = algebraMap (AF F) (AF F ⊗[F] E) (halfInf F).1 := rfl
    rw [this, ← map_pow, ← psi_split, ← e, ← e', psi_eq]
    congr 2
    · linear_combination (-u) * h2
    · linear_combination (-v) * h2

variable {D : D7} {T T₀ : HSp D} {r : ℕ}

end GlobalTheory.GodementSectionReduction

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffOfHeisenbergDerivativeClosedClass
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffOfHeisenbergDerivativeClosedClass
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum NumberField
open GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ContDiff Topology

namespace GlobalTheory.HeisSmooth

open GlobalTheory.OrientedHeis GlobalTheory.FockCompare GlobalTheory.Unf.MatCoef

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} {S T : HSp D}

theorem differentiableAt_phase (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {M : ℝ →+ WO S T} (hM : Continuous M)
    (hMf : ∀ s, (M s).map (finPart D) = 0) (w : WO S T) :
    DifferentiableAt ℝ (fun s : ℝ => ψ (symplOH S T w (M s))) 0 := by
  have hlin : ∀ s : ℝ, piW θ T S (M s) = s • piW θ T S (M 1) := fun s => by
    have := map_real_smul ((piW θ T S).comp M) ((continuous_pi' h.inf T S).comp hM) s 1
    simpa using this
  have e : (fun s : ℝ => ψ (symplOH S T w (M s))) = fun s : ℝ =>
      Complex.exp (-(Real.pi * Complex.I) * ((s * omO S T (piW θ T S w) (piW θ T S (M 1)) : ℝ) : ℂ)) := by
    funext s
    rw [← h.iota_pi (hMf s), psi_symplOH h hψ, hlin, LinearMap.map_smul, smul_eq_mul]
  rw [e]
  exact ((((hasDerivAt_id (0 : ℝ)).mul_const (omO S T (piW θ T S w) (piW θ T S (M 1)))).ofReal_comp).const_mul
      (-(Real.pi * Complex.I))).cexp.differentiableAt

theorem hasDerivAt_line (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {M : ℝ →+ WO S T} (hM : Continuous M)
    (hMf : ∀ s, (M s).map (finPart D) = 0) {f : WO S T → ℂ} {w : WO S T} {c : ℂ}
    (hd : HasDerivAt (fun s : ℝ => heisO ψ S T (M s) f w) c 0) :
    HasDerivAt (fun s : ℝ => f (w + M s)) (c + -deriv (fun s : ℝ => ψ (symplOH S T w (M s))) 0 * f w) 0 := by
  have hp := (differentiableAt_phase h hψ hM hMf w).hasDerivAt
  have hne : ∀ s, ψ (symplOH S T w (M s)) ≠ 0 := fun s h0 => by
    have := AddChar.map_add_eq_mul ψ (symplOH S T w (M s)) (-(symplOH S T w (M s)))
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h0, zero_mul] at this
    exact one_ne_zero this
  have h0 : symplOH S T w (M 0) = 0 := by
    rw [map_zero]
    simp [symplOH, symplO, hO]
  have e : (fun s : ℝ => f (w + M s)) = fun s => heisO ψ S T (M s) f w / ψ (symplOH S T w (M s)) := by
    funext s
    rw [heisO, mul_div_cancel_left₀ _ (hne s)]
  rw [e]
  refine (hd.div hp (hne 0)).congr_deriv ?_
  have h1 : heisO ψ S T (M 0) f w = f w := by
    rw [heisO, h0, AddChar.map_zero_eq_one, one_mul, map_zero, add_zero]
  rw [h1, h0, AddChar.map_zero_eq_one]
  ring

theorem contDiff_of_heis_closed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (V : Set (WO S T → ℂ)), (∀ f ∈ V, Continuous f) →
    (∀ f ∈ V, ∀ M : ℝ →+ WO S T, Continuous M → (∀ t, (M t).map (finPart D) = 0) →
      ∃ f' ∈ V, ∀ w, HasDerivAt (fun t : ℝ => heisO ψ S T (M t) f w) (f' w) 0) →
    ∀ f ∈ V, ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) →
      ∀ w, ContDiff ℝ ∞ fun t => f (w + L t) := by
  intro D ψ hψ S T V hc hd f hf k L hL hLf u
  obtain ⟨⟨θ, hθ⟩, -⟩ := GlobalTheory.Ker.exists_infFam_and_stdChar D
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  haveI : IsTopologicalAddGroup (Formalism.L2.Theta.AE D) := IsTopologicalRing.to_topologicalAddGroup
  haveI : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
  haveI : ContinuousAdd (WO S T) := inferInstance
  let P : ((Fin k → ℝ) → ℂ) → Prop := fun F => ∃ f ∈ V, F = fun t => f (u + L t)
  refine contDiff_of_partials P ?_ ?_ _ ⟨f, hf, rfl⟩
  · rintro _ ⟨f, hf, rfl⟩
    exact (hc f hf).comp (continuous_const.add hL)
  · rintro _ ⟨f, hf, rfl⟩ i
    let E : ℝ →ₗ[ℝ] (Fin k → ℝ) := LinearMap.toSpanSingleton ℝ (Fin k → ℝ) (Pi.single i 1)
    let M : ℝ →+ WO S T := L.comp E.toAddMonoidHom
    have hM : Continuous M := hL.comp E.continuous_of_finiteDimensional
    have hMf : ∀ s, (M s).map (finPart D) = 0 := fun s => hLf _
    obtain ⟨f', hf', hD⟩ := hd f hf M hM hMf
    refine ⟨2, ![fun _ => 1, fun t => -deriv (fun s : ℝ => ψ (symplOH S T (u + L t) (M s))) 0],
      ![fun t => f' (u + L t), fun t => f (u + L t)], fun j => ?_, fun j => ?_, fun t => ?_⟩
    · fin_cases j
      · exact contDiff_const
      · exact contDiff_phase h hψ hL hM hMf u
    · fin_cases j
      · exact ⟨f', hf', rfl⟩
      · exact ⟨f, hf, rfl⟩
    · have e : (fun s : ℝ => f (u + L (t + s • Pi.single i 1))) = fun s => f ((u + L t) + M s) := by
        funext s
        have : E s = s • Pi.single i 1 := rfl
        rw [map_add (f := _), add_assoc, ← this]
        rfl
      rw [e]
      convert hasDerivAt_line h hψ hM hMf (hD (u + L t)) using 1
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_mul]

end GlobalTheory.HeisSmooth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffOfHeisenbergDerivativeClosedClassStatement
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiff_of_heisenbergDerivativeClosedClass : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (V : Set (WO S T → ℂ)), (∀ f ∈ V, Continuous f) → (∀ f ∈ V, ∀ M : ℝ →+ WO S T, Continuous M → (∀ t, (M t).map (finPart D) = 0) → ∃ f' ∈ V, ∀ w, HasDerivAt (fun t : ℝ => heisO ψ S T (M t) f w) (f' w) 0) → ∀ f ∈ V, ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∀ w, ContDiff ℝ ∞ fun t => f (w + L t) := by
  first | exact @GlobalTheory.HeisSmooth.contDiff_of_heis_closed | exact GlobalTheory.HeisSmooth.contDiff_of_heis_closed | (intros; apply GlobalTheory.HeisSmooth.contDiff_of_heis_closed <;> assumption)
end
end
