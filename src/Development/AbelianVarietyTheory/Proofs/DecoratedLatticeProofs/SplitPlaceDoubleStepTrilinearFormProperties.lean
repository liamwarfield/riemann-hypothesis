module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapBesselToFourierJacobiLocalModel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiToBesselLocalModel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineContractionSplitPlaceLocalModel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulas
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepLinearRelationsPeriods
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatHalfTensorSplitPlaceSelfDual

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftValueInvariantMiddleGL
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftValueInvariantMiddleGL
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TriStep.GlMid

variable {D : D7}

theorem comb_right_comm (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} (L : Module.End ℂ (WO A S → ℂ))
    (K : WO A S → WO S A' → ℂ) (c : WO S A' →₀ ℂ) (u : WO A S) (v : WO S A') :
    comb ψ S A' c (fun v' => L (fun u' => K u' v') u) v = L (fun u' => comb ψ S A' c (K u') v) u := by
  have e : (fun u' => comb ψ S A' c (K u') v) =
      ∑ t ∈ c.support, (c t * ψ (symplOH S A' v t)) • (fun u' => K u' (v + t)) := by
    funext u'
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun t _ => by ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_smul]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem comb_left_comm (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} (L : Module.End ℂ (WO S A' → ℂ))
    (K : WO A S → WO S A' → ℂ) (c : WO A S →₀ ℂ) (u : WO A S) (v : WO S A') :
    comb ψ A S c (fun u' => L (K u') v) u = L (fun v' => comb ψ A S c (fun u' => K u' v') u) v := by
  have e : (fun v' => comb ψ A S c (fun u' => K u' v') u) =
      ∑ t ∈ c.support, (c t * ψ (symplOH A S u t)) • (fun v' => K (u + t) v') := by
    funext v'
    simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun t _ => by ring
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_sum]
  simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_smul]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem comb_om_comm {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {ω : Om S T}
    (h : IsWeilDatumO ψ S T χS χT ω) (g : GA D S) (g' : GA D T) (c : WO S T →₀ ℂ)
    (hc : ∀ t ∈ c.support, actO S T g g' t = t) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    comb ψ S T c (ω (g, g') f) = ω (g, g') (comb ψ S T c f) := by
  unfold comb
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [map_smul, h.om_heis g g' t f hf, hc t ht]

theorem idem_mul {e : AE D} (he : IsSplitIdem D e) : (e + cA D e) * (1 - (e + cA D e)) = 0 := by
  have h1 := he.1
  have h2 := he.2.1
  have h3 : cA D e * cA D e = cA D e := by rw [← map_mul, h1]
  linear_combination -h1 - 2 * h2 - h3

theorem actO_fix_left {e : AE D} (he : IsSplitIdem D e) {S T : HSp D} {a : GA D T} (ha : SuppAt e T a) {t : WO S T}
    (ht : IsHalf (1 - (e + cA D e)) t) : actO S T 1 a t = t := by
  unfold actO
  rw [inv_one, show mt S (1 : GA D S) = 1 from rfl, Matrix.mul_one]
  ext i j
  rw [Matrix.mul_apply]
  have key : ∀ k, mt T a i k * t k j = (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) i k * t k j := fun k => by
    have ha' := ha i k
    rw [Matrix.sub_apply] at ha'
    have ht' := ht k j
    linear_combination (-(t k j)) * ha' +
      (-((e + cA D e) * (mt T a i k - (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) i k))) * ht' +
      ((mt T a i k - (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) i k) * t k j) * idem_mul he
  rw [Finset.sum_congr rfl fun k _ => key k, ← Matrix.mul_apply, Matrix.one_mul]

theorem actO_fix_right {e : AE D} (he : IsSplitIdem D e) {S T : HSp D} {a : GA D S} (ha : SuppAt e S a⁻¹) {t : WO S T}
    (ht : IsHalf (1 - (e + cA D e)) t) : actO S T a 1 t = t := by
  unfold actO
  rw [show mt T (1 : GA D T) = 1 from rfl, Matrix.one_mul]
  ext i j
  rw [Matrix.mul_apply]
  have key : ∀ k, t i k * mt S a⁻¹ k j = t i k * (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j := fun k => by
    have ha' := ha k j
    rw [Matrix.sub_apply] at ha'
    have ht' := ht i k
    linear_combination (-(t i k)) * ha' +
      (-((e + cA D e) * (mt S a⁻¹ k j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j))) * ht' +
      ((mt S a⁻¹ k j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) k j) * t i k) * idem_mul he
  rw [Finset.sum_congr rfl fun k _ => key k, ← Matrix.mul_apply, Matrix.mul_one]

end GlobalTheory.TriStep.GlMid

namespace GlobalTheory.TriStep
open GlobalTheory.TriStep.GlMid

theorem valK_glMid : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (g : GL Q.n₁ Q.k) (Ξ₁ Ξ₁' : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ Ξ₂' : SB (Matrix Q.n₂ Q.n₁ Q.k)), Ξ₁'.1 = om Q.μ₁ 1 g Ξ₁.1 → Ξ₂'.1 = om Q.μ₂ g 1 Ξ₂.1 → IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂))) → ∀ f ∈ GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂') f = GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) f := by
  intro D ψ hψ σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ g Ξ₁ Ξ₁' Ξ₂ Ξ₂' h₁ h₂ hC f _
  obtain ⟨a₁, ha₁⟩ := Witness.exists_isLoc (ofSplit Q.q) Q.F.F₁ g
  have hsplit : IsSplitIdem D (ofSplit Q.q).e := (ofSplit Q.q).split
  have comp₁ : (ofSplit Q.q).IsComp S.χ₁ Q.μ₁⁻¹ := fun x a hxa => by
    have e := Q.comp₁ x a hxa
    rw [MonoidHom.inv_apply, Circle.coe_inv] at e
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, e, inv_inv]
  have comp₂ : (ofSplit Q.q).IsComp S.χ₂ Q.μ₂⁻¹ := fun x a hxa => by
    have e := Q.comp₂ x a hxa
    rw [MonoidHom.inv_apply, Circle.coe_inv] at e
    rw [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, e, inv_inv]
  have hL : ∀ (X₂ : SB (Matrix Q.n₂ Q.n₁ Q.k)) (v : WO S.J.W₀ S.B'.A),
      IsThetaFunO ψ S.B.A S.J.W₀ (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ X₂) u v) ∧
      (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' X₂) u v) = S.oma (1, a₁) (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ X₂) u v) := by
    intro X₂ v
    obtain ⟨T₁, hT₁, hT⟩ := hΛ.1 X₂ v
    have e : ∀ X₁ : SB (Matrix Q.n₁ Q.n₀ Q.k), (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB X₁ X₂) u v) = T₁ X₁ :=
      fun X₁ => funext (hT X₁ _ (fun _ => rfl))
    rw [e, e]
    refine ⟨hT₁.theta Ξ₁, ?_⟩
    symm
    refine GlobalTheory.LocOm.omLoc D Q.k (ofSplit Q.q) ψ S.B.A S.J.W₀ S.χ₁ S.χ₁ S.oma S.weila Q.μ₁⁻¹ Q.μ₁⁻¹ comp₁ comp₁ Q.n₁ Q.n₀
      Q.F.F₀ Q.F.F₁ T₁ hT₁ 1 1 a₁ g (GlobalTheory.LocOm.isLoc_one_mul_inv D Q.k (ofSplit Q.q) S.B.A Q.n₀ Q.F.F₀).1 ha₁ Ξ₁ Ξ₁' ?_
    rw [h₁]
    simp
  have hR : ∀ (X₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (u : WO S.B.A S.J.W₀),
      IsThetaFunO ψ S.J.W₀ S.B'.A (Λ (GlobalTheory.LocFlat.CFac.prodSB X₁ Ξ₂) u) ∧
      Λ (GlobalTheory.LocFlat.CFac.prodSB X₁ Ξ₂') u = S.omb (a₁, 1) (Λ (GlobalTheory.LocFlat.CFac.prodSB X₁ Ξ₂) u) := by
    intro X₁ u
    obtain ⟨T₂, hT₂, hT⟩ := hΛ.2 X₁ u
    have e : ∀ X₂ : SB (Matrix Q.n₂ Q.n₁ Q.k), Λ (GlobalTheory.LocFlat.CFac.prodSB X₁ X₂) u = T₂ X₂ :=
      fun X₂ => funext (hT X₂ _ (fun _ => rfl))
    rw [e, e]
    refine ⟨hT₂.theta Ξ₂, ?_⟩
    symm
    refine GlobalTheory.LocOm.omLoc D Q.k (ofSplit Q.q) ψ S.J.W₀ S.B'.A S.χ₂ S.χ₂ S.omb S.weilb Q.μ₂⁻¹ Q.μ₂⁻¹ comp₂ comp₂ Q.n₂ Q.n₁
      Q.F.F₁ Q.F.F₂ T₂ hT₂ a₁ g 1 1 ha₁ (GlobalTheory.LocOm.isLoc_one_mul_inv D Q.k (ofSplit Q.q) S.B'.A Q.n₂ Q.F.F₂).1 Ξ₂ Ξ₂' ?_
    rw [h₂]
    simp
  have hA : ∀ t ∈ c₁.support, actO S.B.A S.J.W₀ 1 a₁ t = t := fun t ht =>
    actO_fix_left hsplit ha₁.1 (hc₁ t ht)
  have hB : ∀ t ∈ c₂.support, actO S.J.W₀ S.B'.A a₁ 1 t = t := fun t ht =>
    actO_fix_right hsplit ((GlobalTheory.LocOm.isLoc_one_mul_inv D Q.k (ofSplit Q.q) S.J.W₀ Q.n₁ Q.F.F₁).2.2 a₁ g ha₁).1 (hc₂ t ht)

  have hY : ∀ v', IsThetaFunO ψ S.B.A S.J.W₀ (fun u => comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) u) v') := by
    intro v'
    have e : (fun u => comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) u) v') =
        ∑ t ∈ c₂.support, (c₂ t * ψ (symplOH S.J.W₀ S.B'.A v' t)) •
          (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) u (v' + t)) := by
      funext u
      simp only [comb, heisO, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun t _ => by ring
    rw [e]
    exact GlobalTheory.Core.Rk.Collect.theta_sum _ _ _ fun t => (hL Ξ₂ (v' + t)).1
  have hC' : ∀ u v, biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂')) u v =
      S.omb (a₁, 1) (fun v' => S.oma (1, a₁)
        (fun u' => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u' v') u) v := by
    intro u v
    have s1 : ∀ u'', comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂') u'') =
        S.omb (a₁, 1) (comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂) u'')) := fun u'' => by
      rw [(hR Ξ₁' u'').2]
      exact comb_om_comm S.weilb a₁ 1 c₂ hB (hR Ξ₁' u'').1
    have s2 : ∀ v' u'', comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂) u'') v' =
        S.oma (1, a₁) (fun u => comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) u) v') u'' := fun v' u'' => by
      have e : Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂) u'' =
          fun w => S.oma (1, a₁) (fun u => Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) u w) u'' :=
        funext fun w => congrFun (hL Ξ₂ w).2 u''
      rw [e]
      exact comb_right_comm ψ (S.oma (1, a₁)) (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) c₂ u'' v'
    unfold biComb
    simp only [s1]
    rw [comb_left_comm ψ (S.omb (a₁, 1)) (fun u'' v' => comb ψ S.J.W₀ S.B'.A c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂) u'') v') c₁ u v]
    refine congrArg (fun F => S.omb (a₁, 1) F v) (funext fun v' => ?_)
    simp only [s2 v']
    rw [comb_om_comm S.weila 1 a₁ c₁ hA (hY v')]

  obtain ⟨b1, -, -, -⟩ := GlobalTheory.SeeSaw.biAct_all D ψ S.B.A S.J.W₀ S.B'.A S.χ₁ S.χ₁ S.χ₂ S.χ₂ S.oma S.omb S.weila S.weilb _ hC
  have hD := b1 (1, a₁)
  obtain ⟨-, -, d3, -⟩ := GlobalTheory.SeeSaw.biAct_all D ψ S.B.A S.J.W₀ S.B'.A S.χ₁ S.χ₁ S.χ₂ S.χ₂ S.oma S.omb S.weila S.weilb _ hD
  have integ : ∀ (h₂ : GA D S.B'.A) (h₁ : GA D S.J.W₀) (h₀ : GA D S.B.A),
      φ h₀ * S.omb (h₁, h₂) (fun v => S.oma (h₀, h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂')) u v) 0) 0 =
      φ h₀ * S.omb (h₁ * a₁, h₂) (fun v => S.oma (h₀, h₁ * a₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0) 0 := by
    intro h₂ h₁ h₀
    have e1 : (fun v => S.oma (h₀, h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂')) u v) 0) =
        S.omb (a₁, 1) (fun v => S.oma (h₀, h₁ * a₁)
          (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0) := by
      funext v
      simp only [hC']
      rw [← d3 (h₀, h₁) (a₁, 1) 0 v]
      refine congrArg (fun F => S.omb (a₁, 1) F v) (funext fun v' => ?_)
      change S.oma (h₀, h₁) (S.oma (1, a₁)
        (fun u' => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u' v')) 0 = _
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
    rw [e1, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have hinv : ∀ h₂ : GA D S.B'.A, ∀ γ ∈ GQ S.J.W₀, ∀ h₁ : GA D S.J.W₀,
      (fun h₁ => ∫ h₀ in S.B.vA.𝓕, φ h₀ * S.omb (h₁, h₂) (fun v => S.oma (h₀, h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0) 0 ∂S.B.vA.μ) (γ * h₁) =
      (fun h₁ => ∫ h₀ in S.B.vA.𝓕, φ h₀ * S.omb (h₁, h₂) (fun v => S.oma (h₀, h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0) 0 ∂S.B.vA.μ) h₁ := by
    intro h₂ γ hγ h₁
    refine congrArg (fun F : GA D S.B.A → ℂ => ∫ h₀ in S.B.vA.𝓕, F h₀ ∂S.B.vA.μ) (funext fun h₀ => ?_)
    have e1 : ∀ v, S.oma (h₀, γ * h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0 =
        S.oma (h₀, h₁) (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0 := fun v => by
      have := GlobalTheory.SeeSawLastValue.om_aut_mul S.weila (one_mem _) hγ h₀ h₁ (GlobalTheory.FrComb.slice_left hC v)
      rwa [one_mul] at this
    simp only [e1]
    have := GlobalTheory.SeeSawLastValue.om_aut_mul S.weilb hγ (one_mem _) h₁ h₂ (GlobalTheory.FrComb.slice_right (b1 (h₀, h₁)) 0)
    rw [one_mul] at this
    exact congrArg (φ h₀ * ·) this
  unfold valK
  congr 1
  funext h₂
  unfold biLift
  simp only [integ h₂]
  exact GlobalTheory.ChainOnto.setIntegral_fd_mul_right D S.J.W₀ S.J.v0.μ S.J.v0.𝓕 S.J.v0.haar S.J.v0.fund
    (fun h₁ => ∫ h₀ in S.B.vA.𝓕, φ h₀ * S.omb (h₁, h₂) (fun v => S.oma (h₀, h₁)
        (fun u => biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂)) u v) 0) 0 ∂S.B.vA.μ) (hinv h₂) a₁

end GlobalTheory.TriStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftValueInvariantMiddleGLStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleThetaLiftValue_invariant_middleGL : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (g : GL Q.n₁ Q.k) (Ξ₁ Ξ₁' : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ Ξ₂' : SB (Matrix Q.n₂ Q.n₁ Q.k)), Ξ₁'.1 = om Q.μ₁ 1 g Ξ₁.1 → Ξ₂'.1 = om Q.μ₂ g 1 Ξ₂.1 → IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂))) → ∀ f ∈ GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁' Ξ₂') f = GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) f := by
  first | exact @GlobalTheory.TriStep.valK_glMid | exact GlobalTheory.TriStep.valK_glMid | (intros; apply GlobalTheory.TriStep.valK_glMid <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftValueBilinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftValueBilinear
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TriStep.Lin

open GlobalTheory.Core.Mi.SepPer

variable {D : D7}

theorem per_int {ρ : ℕ} (B : BesLev D ρ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {φ : GA D B.A → ℂ} (hφ : IsContAut B.A φ) {f : GA D B.V → ℂ} (hf : f ∈ contLeft B.V) :
    (∀ h, IntegrableOn (GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h) B.vN.𝓝 B.vN.ν) ∧
      IntegrableOn (fun h => ∫ n in B.vN.𝓝, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν) B.vA.𝓕 B.vA.μ := by
  obtain ⟨-, -, ⟨Ω, hΩc, hΩ⟩, -⟩ := GlobalTheory.T.besselGroup_quotient_fundamentalDomain_cocompact D ρ B
  obtain ⟨Cφ, hCφ⟩ := GlobalTheory.Unf.EvalCont.bounded_of_contAut B.cpt hφ
  have hμ : B.vA.μ B.vA.𝓕 < ⊤ := GlobalTheory.Unf.vol_fund_lt_top B.cpt B.vA
  have hν1 : B.vN.ν B.vN.𝓝 = 1 := B.vN.unit.2.2
  have hν : B.vN.ν B.vN.𝓝 < ⊤ := by rw [hν1]; exact ENNReal.one_lt_top
  haveI : IsFiniteMeasure (B.vN.ν.restrict B.vN.𝓝) := isFiniteMeasure_restrict.2 hν.ne
  have hemb := GlobalTheory.Unf.BesSemi.continuous_embA B.d B.o
  have hpsi := GlobalTheory.CharLaws.continuous_psiBes ψ B.d hψ.1.1 1 (vecB B.o B.ζ)
  obtain ⟨K, hK⟩ := hΩc.exists_bound_of_continuousOn hf.1.continuousOn
  have hsup : ∀ (h : GA D B.A) (n : flagN B.d), ‖f (n.1 * embA B.d B.o h)‖ ≤ K := by
    intro h n
    have hs : n.1 * embA B.d B.o h ∈ besGrp B.d B.o :=
      mul_mem (Subgroup.mem_sup_left n.2) (Subgroup.mem_sup_right ⟨h, rfl⟩)
    obtain ⟨γ, hγ, hγs⟩ := hΩ _ hs
    rw [← hf.2 γ (Subgroup.mem_inf.1 hγ).1]
    exact hK _ hγs
  have hbd : ∀ h n, ‖GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n‖ ≤ Cφ * K := by
    intro h n
    simp only [GlobalTheory.MixPer.besFun, norm_mul, norm_star, norm_psiBes hψ, mul_one]
    exact mul_le_mul (hCφ h) (hsup h n) (norm_nonneg _) ((norm_nonneg _).trans (hCφ h))
  have hcont : ∀ h, Continuous (GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h) := by
    intro h
    change Continuous fun n : flagN B.d => φ h * f (n.1 * embA B.d B.o h) * star (psiBes ψ B.d 1 (vecB B.o B.ζ) n.1)
    exact (continuous_const.mul (hf.1.comp (continuous_subtype_val.mul continuous_const))).mul
      (continuous_star.comp (hpsi.comp continuous_subtype_val))
  have hcontH : ∀ n : flagN B.d, Continuous fun h => GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n := by
    intro n
    simp only [GlobalTheory.MixPer.besFun]
    exact (hφ.2.mul (hf.1.comp (continuous_const.mul hemb))).mul continuous_const
  have houtC : Continuous fun h => ∫ n in B.vN.𝓝, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν := by
    haveI := GlobalTheory.Unf.EvalCont.firstCountable_GA B.A
    exact continuous_of_dominated (bound := fun _ => Cφ * K)
      (fun h => (hcont h).aestronglyMeasurable)
      (fun h => Filter.Eventually.of_forall fun n => hbd h n) (integrable_const _)
      (Filter.Eventually.of_forall fun n => hcontH n)
  refine ⟨fun h => Measure.integrableOn_of_bounded hν.ne (hcont h).aestronglyMeasurable
    (Filter.Eventually.of_forall fun n => hbd h n), ?_⟩
  refine Measure.integrableOn_of_bounded (M := Cφ * K * B.vN.ν.real B.vN.𝓝) hμ.ne houtC.aestronglyMeasurable
    (Filter.Eventually.of_forall fun h => ?_)
  exact norm_setIntegral_le_of_norm_le_const hν fun n _ => hbd h n

theorem per_add_left {ρ : ℕ} (B : BesLev D ρ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {φ₁ φ₂ : GA D B.A → ℂ} (h₁ : IsContAut B.A φ₁) (h₂ : IsContAut B.A φ₂) {f : GA D B.V → ℂ} (hf : f ∈ contLeft B.V) :
    B.per ψ (φ₁ + φ₂) f = B.per ψ φ₁ f + B.per ψ φ₂ f := by
  obtain ⟨i₁, o₁⟩ := per_int B hψ h₁ hf
  obtain ⟨i₂, o₂⟩ := per_int B hψ h₂ hf
  have e : ∀ h n, GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ (φ₁ + φ₂) f h n =
      GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ₁ f h n + GlobalTheory.MixPer.besFun ψ 1 B.d B.o B.ζ φ₂ f h n := by
    intro h n; simp only [GlobalTheory.MixPer.besFun, Pi.add_apply]; ring
  simp only [GlobalTheory.Unf.BesLev.per, GlobalTheory.MixPer.besPer]
  simp_rw [e]
  rw [← integral_add o₁ o₂]
  exact integral_congr_ae (Filter.Eventually.of_forall fun h => integral_add (i₁ h) (i₂ h))

theorem biComb_add (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ)
    (K K' : WO A S → WO S A' → ℂ) : biComb ψ A S A' c c' (K + K') = biComb ψ A S A' c c' K + biComb ψ A S A' c c' K' := by
  funext u v
  simp only [biComb, GlobalTheory.FrComb.comb_apply, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem biComb_smul (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (c : WO A S →₀ ℂ) (c' : WO S A' →₀ ℂ)
    (a : ℂ) (K : WO A S → WO S A' → ℂ) : biComb ψ A S A' c c' (a • K) = a • biComb ψ A S A' c c' K := by
  funext u v
  simp only [biComb, GlobalTheory.FrComb.comb_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

end GlobalTheory.TriStep.Lin


open GlobalTheory.TriStep.Lin GlobalTheory.Core.Mi.SepPer in
theorem GlobalTheory.TriStep.valK_bilin : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → (∀ Ξ, IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (Λ Ξ)) → ∃ T : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] GlobalTheory.TriStep.space Q →ₗ[ℂ] ℂ, ∀ Ξ f, T Ξ f = GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ f.1 := by
  intro D ψ hψ σ S Q c₁ c₂ _ _ φ hφ Λ _ hΛ
  have hB : BiAct D := GlobalTheory.SeeSaw.biAct_all D
  have hC : ∀ Ξ, IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ)) :=
    fun Ξ => GlobalTheory.T.isJointlySmoothBiTheta_twoVarCombination D ψ hψ S.B.A S.J.W₀ S.B'.A (Λ Ξ) (hΛ Ξ) c₁ c₂
  have hA : ∀ Ξ, IsContAut S.B'.A (biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ))) :=
    fun Ξ => GlobalTheory.SeeSawLastValue.contAut_biLift hB S.weila S.weilb S.B.cpt S.J.cpt S.B.vA S.J.v0 hφ (hC Ξ)
  have hL : ∀ Ξ Ξ', biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ (Ξ + Ξ'))) =
      biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ)) +
        biLift S.oma S.omb S.B.vA S.J.v0 φ (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ')) := by
    intro Ξ Ξ'
    funext h₂
    have e := GlobalTheory.SeeSmallPf.biLift_sum hB S.weila S.weilb S.B.cpt S.J.cpt S.B.vA S.J.v0 hφ
      ![biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ), biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ')]
      (fun i => by fin_cases i <;> simp [hC]) h₂
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at e
    rw [map_add (f := _), biComb_add, e, Pi.add_apply]
  have hf : ∀ f : GlobalTheory.TriStep.space Q, f.1 ∈ contLeft S.B'.V := by
    intro f
    have := f.2.1 1
    rw [map_one, GlobalTheory.TriStep.rTrans_one] at this
    exact ⟨this.2, this.1⟩
  refine ⟨LinearMap.mk₂ ℂ (fun Ξ f => GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ f.1) ?_ ?_ ?_ ?_, fun Ξ f => rfl⟩
  · intro Ξ Ξ' f
    simp only [GlobalTheory.TriStep.valK]
    rw [hL, per_add_left S.B' hψ (hA Ξ) (hA Ξ') (hf f)]
  · intro a Ξ f
    simp only [GlobalTheory.TriStep.valK]
    rw [map_smul, biComb_smul, GlobalTheory.SeeSawRhs.biLift_smul, GlobalTheory.SeeSawStep.per_smul_left, smul_eq_mul]
  · intro Ξ f g
    simp only [GlobalTheory.TriStep.valK]
    obtain ⟨-, -, ⟨Ω, hΩc, hΩ⟩, -⟩ := GlobalTheory.T.besselGroup_quotient_fundamentalDomain_cocompact D σ S.B'
    obtain ⟨Cp, hadd, -⟩ := per_add_bound S.B' hψ (hA Ξ) Ω hΩc hΩ
    exact hadd _ _ (hf f) (hf g)
  · intro a Ξ f
    simp only [GlobalTheory.TriStep.valK]
    exact GlobalTheory.SeeSawStep.per_smul_right S.B' ψ _ a f.1
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftValueBilinearStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleThetaLiftValue_bilinear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → (∀ Ξ, IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (Λ Ξ)) → ∃ T : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] GlobalTheory.TriStep.space Q →ₗ[ℂ] ℂ, ∀ Ξ f, T Ξ f = GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ f.1 := by
  first | exact @GlobalTheory.TriStep.valK_bilin | exact GlobalTheory.TriStep.valK_bilin | (intros; apply GlobalTheory.TriStep.valK_bilin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AconvSingleList
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TriStep.IdempotentCombination

variable {D : D7}

section Idem
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem cA_idem (q : GlobalTheory.FinPl.SplitPt D k) : cA D (q.e + cA D q.e) = q.e + cA D q.e := by
  obtain ⟨ε, -, h4⟩ := q.above
  rw [h4]
  show cA D (ε ⊗ₜ[D.host.F] (1 : D.host.E)) = ε ⊗ₜ[D.host.F] (1 : D.host.E)
  simp [cA, sigR]

theorem idem_sq (q : GlobalTheory.FinPl.SplitPt D k) : (q.e + cA D q.e) * (q.e + cA D q.e) = q.e + cA D q.e := by
  have h1 := q.split.1
  have h2 := q.split.2.1
  have h3 : cA D q.e * cA D q.e = cA D q.e := by rw [← map_mul, h1]
  linear_combination h1 + 2 * h2 + h3

end Idem

variable {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem aconv_cons {G : Type} [AddMonoid G] (e : G →₀ ℂ) (l : List (G →₀ ℂ)) :
    aconv (e :: l) = ∑ g ∈ e.support, ∑ h ∈ (aconv l).support, Finsupp.single (g + h) (e g * aconv l h) := rfl

theorem comb_aconv_cons (e : WO S T →₀ ℂ) (l : List (WO S T →₀ ℂ))
    (h : ∀ x ∈ e.support, ∀ y ∈ (aconv l).support, symplO S T x y = 0) (f : WO S T → ℂ) :
    comb ψ S T (aconv (e :: l)) f = comb ψ S T e (comb ψ S T (aconv l) f) := by
  rw [GlobalTheory.HeisComb.comb_comb, GlobalTheory.HeisComb.comb_eq_sum, aconv_cons]
  rw [← Finsupp.sum_finsetSum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← Finsupp.sum_finsetSum_index (fun u => zero_smul ℂ (heisO ψ S T u f)) (fun u a b => add_smul a b (heisO ψ S T u f))]
  refine Finset.sum_congr rfl fun y hy => ?_
  have h0 : symplOH S T x y = 0 := by
    unfold symplOH
    rw [h x hx y hy, mul_zero]
  rw [Finsupp.sum_single_index (zero_smul ℂ (heisO ψ S T (x + y) f)), GlobalTheory.WeilVacMove.heisO_heisO, h0, AddChar.map_zero_eq_one,
    one_smul]

end GlobalTheory.TriStep.IdempotentCombination

namespace GlobalTheory.TriStep

theorem aconv_single_list {G : Type} [AddMonoid G] (d : G →₀ ℂ) : aconv [d] = d := by
  show d.sum (fun g a => (Finsupp.single 0 1 : G →₀ ℂ).sum fun h b => Finsupp.single (g + h) (a * b)) = d
  calc d.sum (fun g a => (Finsupp.single 0 1 : G →₀ ℂ).sum fun h b => Finsupp.single (g + h) (a * b))
        = d.sum (fun g a => Finsupp.single g a) := by
          congr 1; funext g a; rw [Finsupp.sum_single_index (by simp), add_zero, mul_one]
    _ = d := Finsupp.sum_single d

theorem comb_aconv_away {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ} (Q : QStep S) {A T : HSp D}
    (c d : WO A T →₀ ℂ) (hc : Q.Away c)
    (hd : ∀ u ∈ d.support, IsHalf ((ofSplit Q.q).e + cA D (ofSplit Q.q).e) u) (g : WO A T → ℂ) :
    comb ψ A T (aconv [c, d]) g = comb ψ A T c (comb ψ A T d g) := by
  rw [GlobalTheory.TriStep.IdempotentCombination.comb_aconv_cons c [d] ?_ g, aconv_single_list]
  intro x hx y hy
  rw [aconv_single_list] at hy
  have hy' : IsHalf (Q.q.e + cA D Q.q.e) y := hd y hy
  refine GlobalTheory.HeisComb.symplO_half A T (1 - (Q.q.e + cA D Q.q.e)) (Q.q.e + cA D Q.q.e) x y ?_ ?_ (hc x hx) hy'
  · rw [map_sub, map_one, GlobalTheory.TriStep.IdempotentCombination.cA_idem]
  · rw [sub_mul, one_mul, GlobalTheory.TriStep.IdempotentCombination.idem_sq, sub_self]

theorem valK_comb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (T₁ : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.B.V S.J.W → ℂ)) (T₂ : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.J.W S.B'.V → ℂ)), (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ → ∀ (U₁ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) →ₗ[ℂ] (WO S.B.V₀ S.J.W₀ → ℂ)) (U₂ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k) →ₗ[ℂ] (WO S.J.W₀ S.B'.V₀ → ℂ)), (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) Φ.1 → flatBF S.s₁ (T₁ Φ) = U₁ Ψ) → (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flRow Q.ψk Q.ν (σ + 1) Φ.1 → flatFB S.s₂ (T₂ Φ) = U₂ Ψ) → (∀ Ψ₁ Ψ₂, ∃ Ξ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k), Ξ.1 = GlobalTheory.LocFlat.contr Q.ψk Q.ν Ψ₁.1 Ψ₂.1 ∧ GlobalTheory.Unf.contr S.l S.J.W₀ S.vL (U₁ Ψ₁) (U₂ Ψ₂) = Λ Ξ) → ∀ (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ : SB (Matrix Q.n₂ Q.n₁ Q.k)) d₁ d₂, (ofSplit Q.q).IsCombAt ψ Q.F.F₀ Q.F.F₁ d₁ Ξ₁.1 → (ofSplit Q.q).IsCombAt ψ Q.F.F₁ Q.F.F₂ d₂ Ξ₂.1 → ∀ O₁ O₂, IsOne O₁ → IsOne O₂ → ∀ f ∈ GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) f = S.val (aconv [c₁, d₁]) (aconv [c₂, d₂]) (T₁ O₁) (T₂ O₂) φ f 1 1 1 := by
  intro D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ T₁ T₂ hT₁ hT₂ U₁ U₂ hU₁ hU₂ hcon Ξ₁ Ξ₂ d₁ d₂ hd₁ hd₂ O₁ O₂ hO₁ hO₂ f hf
  have hσc : Q.c = 2 * σ := by have := Q.F.bes.1; omega
  have hun := GlobalTheory.LocFlat.flat_contr_intIndicator Q.k Q.ψk Q.ν Q.cond Q.unitVol
  let P₁ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  let P₂ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  let R₁ : SB (Matrix Q.n₁ Q.n₀ Q.k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  let R₂ : SB (Matrix Q.n₂ Q.n₁ Q.k) := ⟨_, GlobalTheory.LocMod.GValProof.one_mem_SB _ _⟩
  have e₁ : flatBF S.s₁ (T₁ O₁) = U₁ P₁ := hU₁ O₁ P₁ (by
    rw [hO₁, (hun Q.n₁ Q.n₀ Q.n₀ (Q.c + 1 + 1) (σ + 1 + 1)).1, if_neg (by omega)])
  have e₂ : flatFB S.s₂ (T₂ O₂) = U₂ P₂ := hU₂ O₂ P₂ (by
    rw [hO₂, (hun Q.n₂ Q.n₁ Q.n₀ (Q.c + 1) (σ + 1)).2.1 (by omega) (by omega)])
  obtain ⟨ΞO, hΞO, eΛ⟩ := hcon P₁ P₂
  have hΞO' : ∀ q, ΞO.1 q = R₁.1 q.1 * R₂.1 q.2 := fun q => by
    rw [hΞO]; exact (hun Q.n₁ Q.n₀ Q.n₂ 0 0).2.2 q
  have hbi := (GlobalTheory.BiComb.comb_bimodel_and_line D Q.k (ofSplit Q.q) ψ Q.n₁ Q.n₀ Q.n₂).1 S.B.A S.J.W₀ S.B'.A
    Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ d₁ d₂ Ξ₁ R₁ Ξ₂ R₂ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) ΞO hΛ hd₁ hd₂ rfl rfl (fun q => rfl) hΞO'
  have hbc := GlobalTheory.ProdLocInv.biComb_comp ψ S.B.A S.J.W₀ S.B'.A c₁ d₁ (aconv [c₁, d₁]) c₂ d₂ (aconv [c₂, d₂])
    (comb_aconv_away Q c₁ d₁ hc₁ hd₁.1) (comb_aconv_away Q c₂ d₂ hc₂ hd₂.1) (Λ ΞO)
  have hom₁ : S.s₁.om (1, 1) = 1 := map_one _
  have hom₂ : S.s₂.om (1, 1) = 1 := map_one _
  simp only [GlobalTheory.TriStep.valK, Dbl2.val, Dbl2.con, GlobalTheory.TriStep.rTrans_one]
  rw [hom₁, hom₂, Module.End.one_apply, Module.End.one_apply, e₁, e₂, eΛ, ← hbc, hbi]

end GlobalTheory.TriStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepValueEqTrilinearTensorValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepValueEqTrilinearTensorValue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TriStep

theorem val_eq_tensorVal : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (T₁ : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.B.V S.J.W → ℂ)) (T₂ : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.J.W S.B'.V → ℂ)), (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ → ∀ (U₁ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) →ₗ[ℂ] (WO S.B.V₀ S.J.W₀ → ℂ)) (U₂ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k) →ₗ[ℂ] (WO S.J.W₀ S.B'.V₀ → ℂ)), (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) Φ.1 → flatBF S.s₁ (T₁ Φ) = U₁ Ψ) → (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flRow Q.ψk Q.ν (σ + 1) Φ.1 → flatFB S.s₂ (T₂ Φ) = U₂ Ψ) → (∀ Ψ₁ Ψ₂, ∃ Ξ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k), Ξ.1 = GlobalTheory.LocFlat.contr Q.ψk Q.ν Ψ₁.1 Ψ₂.1 ∧ GlobalTheory.Unf.contr S.l S.J.W₀ S.vL (U₁ Ψ₁) (U₂ Ψ₂) = Λ Ξ) → ∀ (T : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] GlobalTheory.TriStep.space Q →ₗ[ℂ] ℂ), (∀ Ξ f, T Ξ f = GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ f.1) → ∀ Φ₁ Φ₂ (f : GlobalTheory.TriStep.space Q), HasTensorVal (fun Ψ Φ₀ => app (((GlobalTheory.LocFlat.CFac.prodSBBil _ _).compr₂ T) Ψ) (opEFJ Q.ψk Q.ν (σ + 1) Φ₀.1 Φ₂.1) f) (fl Q.ψk Q.ν Q.μ₁ (σ + 1) Φ₁.1) (S.val c₁ c₂ (T₁ Φ₁) (T₂ Φ₂) φ f.1 1 1 1) := by
  intro D ψ hψ σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ T₁ T₂ hT₁ hT₂ U₁ U₂ hU₁ hU₂ hCL T hT Φ₁ Φ₂ f
  have hcQ : Q.c + 1 + 1 = 2 * (σ + 1) := by have := Q.F.bes.1; omega
  obtain ⟨hψc, hψ1⟩ := GlobalTheory.hasConductor_one_continuous_ne_one Q.k Q.ψk Q.cond
  have hsd : IsSelfDual Q.ψk Q.ν := ((GlobalTheory.SplitWeil.selfDual_measure Q.k Q.ψk hψc hψ1).2.1 Q.cond Q.ν).1 Q.unitVol
  obtain ⟨hcol, hrow, hop, ⟨m, Ψ, Φ₀, hfl⟩, hsum⟩ :=
    GlobalTheory.LocFlat.ContrSum.contr_flat_eq_sum Q.k Q.ψk hψc hψ1 Q.ν hsd Q.n₀ Q.n₁ Q.n₂ (Q.c + 1) (σ + 1) hcQ Q.μ₁ Φ₁ Φ₂
  obtain ⟨Ξ, hΞ, hΛΞ⟩ := hCL ⟨_, hcol⟩ ⟨_, hrow⟩
  refine ⟨m, Ψ, Φ₀, hfl, ?_⟩
  have e1 : S.val c₁ c₂ (T₁ Φ₁) (T₂ Φ₂) φ f.1 1 1 1 = valK S Q c₁ c₂ φ Λ Ξ f.1 := by
    unfold Dbl2.val Dbl2.con valK
    rw [show ((1 : GA D S.B.V), (1 : GA D S.J.W)) = 1 from rfl, show ((1 : GA D S.J.W), (1 : GA D S.B'.V)) = 1 from rfl,
      map_one, map_one, rTrans_one, Module.End.one_apply, Module.End.one_apply, hU₁ Φ₁ ⟨_, hcol⟩ rfl,
      hU₂ Φ₂ ⟨_, hrow⟩ rfl, hΛΞ]
  have e2 : Ξ = ∑ i, GlobalTheory.LocFlat.CFac.prodSB (Ψ i) ⟨_, hop (Φ₀ i)⟩ := by
    apply Subtype.ext
    funext x
    rw [hΞ, hsum m Ψ Φ₀ hfl x]
    simp [Submodule.coe_sum, Finset.sum_apply, GlobalTheory.LocFlat.CFac.prodSB_apply]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e1, ← hT, e2, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app_coe (((GlobalTheory.LocFlat.CFac.prodSBBil _ _).compr₂ T) (Ψ i)) ⟨_, hop (Φ₀ i)⟩
  exact (LinearMap.congr_fun h f).symm

end GlobalTheory.TriStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleStepValueEqTrilinearTensorValueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleStepValue_eq_trilinearTensorValue : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ (T₁ : SB (Matrix (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) (Q.n₀ ⊕ Fin (Q.c + 1 + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.B.V S.J.W → ℂ)) (T₂ : SB (Matrix (Q.n₂ ⊕ Fin (Q.c + 1)) (Q.n₁ ⊕ Fin (Q.c + 1 + 1)) Q.k) →ₗ[ℂ] (WO S.J.W S.B'.V → ℂ)), (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ → ∀ (U₁ : SB (Matrix Q.n₁ (Q.n₀ ⊕ Unit) Q.k) →ₗ[ℂ] (WO S.B.V₀ S.J.W₀ → ℂ)) (U₂ : SB (Matrix (Q.n₂ ⊕ Unit) Q.n₁ Q.k) →ₗ[ℂ] (WO S.J.W₀ S.B'.V₀ → ℂ)), (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol Q.ψk Q.ν (σ + 1 + 1) Φ.1 → flatBF S.s₁ (T₁ Φ) = U₁ Ψ) → (∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flRow Q.ψk Q.ν (σ + 1) Φ.1 → flatFB S.s₂ (T₂ Φ) = U₂ Ψ) → (∀ Ψ₁ Ψ₂, ∃ Ξ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k), Ξ.1 = GlobalTheory.LocFlat.contr Q.ψk Q.ν Ψ₁.1 Ψ₂.1 ∧ GlobalTheory.Unf.contr S.l S.J.W₀ S.vL (U₁ Ψ₁) (U₂ Ψ₂) = Λ Ξ) → ∀ (T : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] GlobalTheory.TriStep.space Q →ₗ[ℂ] ℂ), (∀ Ξ f, T Ξ f = GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ f.1) → ∀ Φ₁ Φ₂ (f : GlobalTheory.TriStep.space Q), HasTensorVal (fun Ψ Φ₀ => app (((GlobalTheory.LocFlat.CFac.prodSBBil _ _).compr₂ T) Ψ) (opEFJ Q.ψk Q.ν (σ + 1) Φ₀.1 Φ₂.1) f) (fl Q.ψk Q.ν Q.μ₁ (σ + 1) Φ₁.1) (S.val c₁ c₂ (T₁ Φ₁) (T₂ Φ₂) φ f.1 1 1 1) := by
  exact @GlobalTheory.TriStep.val_eq_tensorVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftValueEquivariantSymmetricUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftValueEquivariantSymmetricUnipotent
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TriStep


open GlobalTheory.NormalFramePeriod in
theorem valK_nEquiv : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ Ξ, ∀ g ∈ N Q.k Q.n₂ (Q.c + 1) (σ + 1), ∀ f ∈ GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ (rTrans (Q.gl₂ g) f) = (Q.ψk (simpleSum g) : ℂ) * GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ f := by
  intro D ψ hψ σ S Q c₁ c₂ _ _ φ _ Λ _ Ξ g hg f hf
  have hc : IsContAut S.B'.V f := by
    have := hf.1 1
    rwa [map_one, rTrans_one] at this
  unfold valK
  rw [per_flagN S.B' ψ hψ _ f hc.1 (GlobalTheory.LocGrp.mem_flagN_of_mem_N (ofSplit Q.q) S.B' _ Q.F.F₂ Q.F.G₂ Q.F.bes' (Q.gl₂ g) g hg (Q.loc₂ g)),
    GlobalTheory.LocBesChar.psiBes_isLoc D Q.k (ofSplit Q.q) ψ Q.ψk Q.char σ S.B' _ Q.n₂ (Q.c + 1) Q.F.F₂ Q.F.G₂ Q.F.bes' (Q.gl₂ g) g hg (Q.loc₂ g)]

end GlobalTheory.TriStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleLiftValueEquivariantSymmetricUnipotentStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleLiftValue_equivariant_symmetricUnipotent : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (c₁ : WO S.B.A S.J.W₀ →₀ ℂ) (c₂ : WO S.J.W₀ S.B'.A →₀ ℂ), Q.Away c₁ → Q.Away c₂ → ∀ φ, IsContAut S.B.A φ → ∀ (Λ : SB (Matrix Q.n₁ Q.n₀ Q.k × Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] (WO S.B.A S.J.W₀ → WO S.J.W₀ S.B'.A → ℂ)), (ofSplit Q.q).IsBiModel ψ Q.F.F₀ Q.F.F₁ Q.F.F₂ Λ → ∀ Ξ, ∀ g ∈ N Q.k Q.n₂ (Q.c + 1) (σ + 1), ∀ f ∈ GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ (rTrans (Q.gl₂ g) f) = (Q.ψk (simpleSum g) : ℂ) * GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ Ξ f := by
  first | exact @GlobalTheory.TriStep.valK_nEquiv | exact GlobalTheory.TriStep.valK_nEquiv | (intros; apply GlobalTheory.TriStep.valK_nEquiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpaceOfTypedAutomorphic
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqOneOfNormPowTwoPowSubOneLt
namespace GlobalTheory.NormPowerTwoUnity

lemma norm_sq_sub_one_ge (w : ℂ) (h : ‖w - 1‖ < (1 / 2 : ℝ)) :
    (3 / 2 : ℝ) * ‖w - 1‖ ≤ ‖w ^ 2 - 1‖ := by
  have e : w ^ 2 - 1 = (w + 1) * (w - 1) := by ring
  have h2 : ‖(2 : ℂ)‖ ≤ ‖w + 1‖ + ‖w - 1‖ := by
    have : (2 : ℂ) = (w + 1) - (w - 1) := by ring
    rw [this]
    exact norm_sub_le _ _
  have h3 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [e, norm_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  linarith

theorem eq_one_of_norm_pow_two_pow_sub_one_lt (z : ℂ)
    (h : ∀ (m : ℕ), ‖z ^ (2 : ℕ) ^ m - (1 : ℂ)‖ < (1 / 2 : ℝ)) : z = (1 : ℂ) := by
  have key : ∀ m : ℕ, (3 / 2 : ℝ) ^ m * ‖z - 1‖ ≤ ‖z ^ (2 : ℕ) ^ m - (1 : ℂ)‖ := by
    intro m
    induction m with
    | zero => simp
    | succ n ih =>
      have h1 := norm_sq_sub_one_ge _ (h n)
      rw [← pow_mul, ← pow_succ] at h1
      calc (3 / 2 : ℝ) ^ (n + 1) * ‖z - 1‖ = (3 / 2) * ((3 / 2 : ℝ) ^ n * ‖z - 1‖) := by ring
        _ ≤ (3 / 2) * ‖z ^ (2 : ℕ) ^ n - (1 : ℂ)‖ := by linarith
        _ ≤ _ := h1
  by_contra hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt ((1 / 2 : ℝ) / ‖z - 1‖) (show (1 : ℝ) < 3 / 2 by norm_num)
  rw [div_lt_iff₀ hpos] at hm
  have := key m
  have := h m
  linarith

end GlobalTheory.NormPowerTwoUnity
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpaceOfTypedAutomorphic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TriStepMem

theorem eq_one_of_pow_two_pow (z : ℂ) (h : ∀ m : ℕ, ‖z ^ (2 ^ m) - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt
  | exact _root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt
  | (apply _root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt <;> assumption)
  | (intros; apply _root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NormPowerTwoUnity.eq_one_of_norm_pow_two_pow_sub_one_lt ..)

end GlobalTheory.TriStepMem

namespace GlobalTheory.TriStep

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {σ : ℕ} {S : Dbl2 ψ σ}

theorem mem_space_of_typed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S)
    (f : GA D S.B'.V → ℂ), IsContAut S.B'.V f → Q.Typed f → f ∈ GlobalTheory.TriStep.space Q := by
  intro D ψ σ S Q f hf hT
  have hgl : Continuous Q.gl₂ := (GlobalTheory.T.splitPlace_local_group_closedEmbedding_integral D Q.k Q.q S.B'.V _ Q.F.G₂ Q.gl₂ Q.loc₂).1.continuous
  refine ⟨fun y => ⟨fun γ hγ x => ?_, ?_⟩, ?_⟩
  · simp only [rTrans]
    rw [mul_assoc, hf.1 γ hγ]
  · exact hf.2.comp (continuous_id.mul continuous_const)
  · by_cases h0 : ∃ x, f x ≠ 0
    · obtain ⟨x, hx⟩ := h0
      have hval : ∀ j : Q.L₂.J, f (x * Q.gl₂ j.1) = (Q.L₂.lam j : ℂ) * f x := fun j => by
        have := congrFun (hT j) x
        simpa [rTrans] using this
      let φ : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k → ℂ := fun g => f (x * Q.gl₂ g) / f x
      have hφc : Continuous φ := (hf.2.comp (continuous_const.mul hgl)).div_const _
      have hφ : ∀ j : Q.L₂.J, φ j.1 = (Q.L₂.lam j : ℂ) := fun j => by
        simp only [φ, hval j]; field_simp
      let U : Set (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) := (Q.L₂.J : Set _) ∩ φ ⁻¹' Metric.ball 1 (1 / 2)
      have hU : U ∈ nhds (1 : GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) := by
        refine (Q.co₂.1.inter (Metric.isOpen_ball.preimage hφc)).mem_nhds ⟨Q.L₂.J.one_mem, ?_⟩
        have := hφ 1
        simp only [OneMemClass.coe_one, map_one, Units.val_one] at this
        simp [this]
      obtain ⟨K, hKo, hKU, -, -⟩ := GlobalTheory.SmGL.exists_open_normalised_subgroup_subset Q.k (Q.n₂ ⊕ Fin (Q.c + 1)) U hU
      refine ⟨K, hKo, fun u hu => ?_⟩
      have huJ : u ∈ Q.L₂.J := (hKU hu).1
      have hlam : (Q.L₂.lam ⟨u, huJ⟩ : ℂ) = 1 := by
        apply GlobalTheory.TriStepMem.eq_one_of_pow_two_pow
        intro m
        have hm : u ^ (2 ^ m) ∈ K := K.pow_mem hu _
        have hmU := hKU hm
        have hmJ : u ^ (2 ^ m) ∈ Q.L₂.J := hmU.1
        have e : (⟨u ^ (2 ^ m), hmJ⟩ : Q.L₂.J) = (⟨u, huJ⟩ : Q.L₂.J) ^ (2 ^ m) := rfl
        have h2 : φ (u ^ (2 ^ m)) ∈ Metric.ball (1 : ℂ) (1 / 2) := hmU.2
        rw [show u ^ (2 ^ m) = ((⟨u ^ (2 ^ m), hmJ⟩ : Q.L₂.J) : GL _ _) from rfl, hφ, e, map_pow,
          Units.val_pow_eq_pow_val, Metric.mem_ball, dist_eq_norm] at h2
        exact h2
      have := hT ⟨u, huJ⟩
      rw [hlam, one_smul] at this
      exact this
    · push_neg at h0
      refine ⟨⊤, isOpen_univ, fun u _ => ?_⟩
      funext g
      simp [rTrans, h0]

end GlobalTheory.TriStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSpaceOfTypedAutomorphicStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_space_of_typed_automorphic : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) (f : GA D S.B'.V → ℂ), IsContAut S.B'.V f → Q.Typed f → f ∈ GlobalTheory.TriStep.space Q := by
  first | exact @GlobalTheory.TriStep.mem_space_of_typed | exact GlobalTheory.TriStep.mem_space_of_typed | (intros; apply GlobalTheory.TriStep.mem_space_of_typed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepTrilinearFormProperties
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TriStep

theorem isBiTheta_add' {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {f g : WO A S → WO S A' → ℂ}
    (hf : IsBiTheta ψ A S A' f) (hg : IsBiTheta ψ A S A' g) : IsBiTheta ψ A S A' (f + g) := by
  refine ⟨hf.cont.add hg.cont, ?_, fun γ u v => ?_, fun γ u v => ?_, ?_, ?_⟩
  · intro n L L' hL hL' hLf hL'f u v
    exact (hf.smooth n L L' hL hL' hLf hL'f u v).add (hg.smooth n L L' hL hL' hLf hL'f u v)
  · simp only [Pi.add_apply]; rw [hf.quasiL, hg.quasiL]; ring
  · simp only [Pi.add_apply]; rw [hf.quasiR, hg.quasiR]; ring
  · obtain ⟨U, hU, hUf⟩ := hf.levL
    obtain ⟨V, hV, hVf⟩ := hg.levL
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' v => ?_⟩
    funext u
    have h1 := congrFun (hUf a ha.1 ha' v) u
    have h2 := congrFun (hVf a ha.2 ha' v) u
    simp only [heisO, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]
  · obtain ⟨U, hU, hUf⟩ := hf.levR
    obtain ⟨V, hV, hVf⟩ := hg.levR
    refine ⟨U ⊓ V, hU.inter hV, fun a ha ha' u => ?_⟩
    funext v
    have h1 := congrFun (hUf a ha.1 ha' u) v
    have h2 := congrFun (hVf a ha.2 ha' u) v
    simp only [heisO, Pi.add_apply] at h1 h2 ⊢
    rw [mul_add, h1, h2]

theorem isBiTheta_zero' {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} : IsBiTheta ψ A S A' 0 := by
  refine ⟨?_, fun n L L' _ _ _ _ u v => ?_, fun γ u v => by simp, fun γ u v => by simp,
    ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun a _ _ v => ?_⟩,
    ⟨⊤, by rw [AddSubgroup.coe_top]; exact isOpen_univ, fun a _ _ u => ?_⟩⟩
  · simp only [Pi.zero_apply]; exact continuous_const
  · simp only [Pi.zero_apply]; exact contDiff_const
  · funext x; simp [heisO]
  · funext x; simp [heisO]

theorem isBiTheta_of_prod {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {A S A' : HSp D} {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X] [T2Space Y] [LocallyCompactSpace Y]
    [TotallyDisconnectedSpace Y] (Λ : SB (X × Y) →ₗ[ℂ] (WO A S → WO S A' → ℂ))
    (h : ∀ a b, IsBiTheta ψ A S A' (Λ (GlobalTheory.LocFlat.CFac.prodSB a b))) (Ξ : SB (X × Y)) : IsBiTheta ψ A S A' (Λ Ξ) := by
  have hmem : Ξ ∈ Submodule.span ℂ (Set.range fun q : SB X × SB Y => GlobalTheory.LocFlat.CFac.prodSB q.1 q.2) := by
    rw [GlobalTheory.T.span_schwartzBruhatProduct_eq_top X Y]; trivial
  have key : ∀ c : ℂ, IsBiTheta ψ A S A' (Λ (c • Ξ)) := by
    induction hmem using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, rfl⟩ := hx
      intro c
      have e : c • GlobalTheory.LocFlat.CFac.prodSB q.1 q.2 = GlobalTheory.LocFlat.CFac.prodSB (c • q.1) q.2 := by
        change c • GlobalTheory.LocFlat.CFac.prodSBBil X Y q.1 q.2 = GlobalTheory.LocFlat.CFac.prodSBBil X Y (c • q.1) q.2
        rw [map_smul, LinearMap.smul_apply]
      rw [e]; exact h _ _
    | zero => intro c; rw [smul_zero, map_zero]; exact isBiTheta_zero'
    | add x y _ _ hx hy => intro c; rw [smul_add, map_add (f := _)]; exact isBiTheta_add' (hx c) (hy c)
    | smul a x _ hx => intro c; rw [smul_smul]; exact hx _
  simpa using key 1

theorem tri : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) c₁ c₂, Q.Away c₁ → Q.Away c₂ → ∀ T₁ T₂, (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ → ∀ φ, IsContAut S.B.A φ → ∃ (A : Submodule ℂ (GA D S.B'.V → ℂ)) (τ : Representation ℂ (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) A) (T : SB (Matrix Q.n₁ Q.n₀ Q.k) →ₗ[ℂ] SB (Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), IsSmoothRep τ ∧ (∀ y (f : A), (τ y f).1 = rTrans (Q.gl₂ y) f.1) ∧ (∀ f, IsContAut S.B'.V f → Q.Typed f → f ∈ A) ∧ TriPos Q.ψk Q.μ₁ Q.μ₂ (σ + 1) τ T ∧ (∀ Φ₁ Φ₂ (f : A), HasTensorVal (fun Ψ Φ₀ => app (T Ψ) (opEFJ Q.ψk Q.ν (σ + 1) Φ₀.1 Φ₂.1) f) (fl Q.ψk Q.ν Q.μ₁ (σ + 1) Φ₁.1) (S.val c₁ c₂ (T₁ Φ₁) (T₂ Φ₂) φ f.1 1 1 1)) ∧ ∀ (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ : SB (Matrix Q.n₂ Q.n₁ Q.k)) d₁ d₂, (ofSplit Q.q).IsCombAt ψ Q.F.F₀ Q.F.F₁ d₁ Ξ₁.1 → (ofSplit Q.q).IsCombAt ψ Q.F.F₁ Q.F.F₂ d₂ Ξ₂.1 → ∀ O₁ O₂, IsOne O₁ → IsOne O₂ → ∀ f : A, T Ξ₁ Ξ₂ f = S.val (aconv [c₁, d₁]) (aconv [c₂, d₂]) (T₁ O₁) (T₂ O₂) φ f.1 1 1 1 := by
  intro D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ T₁ T₂ hT₁ hT₂ φ hφ
  have hBF := GlobalTheory.T.flatMap_besselToFourierJacobi_localModel D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D) (GlobalTheory.T.weilDatum_localModel_formula D)
  have hFB := GlobalTheory.T.flatMap_fourierJacobiToBessel_localModel D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D) (GlobalTheory.T.weilDatum_localModel_formula D)
  have hCL := GlobalTheory.T.lineContraction_splitPlace_localModel D GlobalTheory.LocFlat.contrFactor
  have hν : Q.ν.IsAddHaarMeasure := Q.unitVol.1
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.LocMod.GValProof.core_of_bes (ofSplit Q.q) S.B Q.F.s Q.F.F₀ Q.F.G₀ Q.F.bes
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.LocMod.GValProof.core_of_bes (ofSplit Q.q) S.B' (Q.F.s * (ofSplit Q.q).xi) Q.F.F₂ Q.F.G₂ Q.F.bes'
  have hjac : (ofSplit Q.q).IsJacFrame S.J Q.F.s (-(ofSplit Q.q).xi ^ 2 * (ofSplit Q.q).hz S.B') Q.F.F₁ Q.F.G₁ := by
    rw [← GlobalTheory.LocMod.GValProof.hz_link (ofSplit Q.q) S.B S.B' S.l]; exact Q.F.jac
  obtain ⟨U₁, hU₁, hU₁e⟩ := hBF Q.k (ofSplit Q.q) Q.ν hν ψ Q.ψk Q.char (σ + 1) S.B S.J S.s₁ Q.F.s Q.F.s_ne _ _ (Q.c + 1 + 1)
    Q.F.F₀ C₀ Q.F.G₀ Q.F.F₁ Q.F.G₁ hC₀ Q.F.bes Q.F.jac T₁ hT₁
  obtain ⟨U₂, hU₂, hU₂e⟩ := hFB Q.k (ofSplit Q.q) Q.ν hν ψ Q.ψk Q.char σ S.J S.B' S.s₂ Q.F.s Q.F.s_ne _ _ (Q.c + 1)
    Q.F.F₁ Q.F.G₁ Q.F.F₂ C₂ Q.F.G₂ hjac hC₂ Q.F.bes' T₂ hT₂
  obtain ⟨Λ, hΛ, hΛe⟩ := hCL Q.k (ofSplit Q.q) Q.ν hν ψ hstd Q.ψk Q.char (σ + 1) σ S.B S.B' S.l S.J.W₀ S.vL Q.F.s Q.F.s_ne
    _ _ _ Q.F.F₀ C₀ Q.F.F₁ Q.F.F₂ C₂ hC₀ hC₂ U₁ U₂ hU₁ hU₂
  have hψkc : Continuous Q.ψk := by
    obtain ⟨-, hψk, -, -, -⟩ := GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D Q.k (ofSplit Q.q) ψ hstd
    exact (hψk Q.ψk Q.char).1
  have hΛθ : ∀ Ξ, IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (Λ Ξ) := by
    haveI := GlobalTheory.SplitWeil.t2Space Q.k
    haveI : NonarchimedeanAddGroup Q.k := ⟨fun V hV => by
      obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
      exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
        GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
    haveI : TotallyDisconnectedSpace Q.k := inferInstance
    haveI : ∀ n n' : Type, T2Space (Matrix n n' Q.k) := fun n n' => inferInstanceAs (T2Space (n → n' → Q.k))
    haveI : ∀ n n' : Type, TotallyDisconnectedSpace (Matrix n n' Q.k) :=
      fun n n' => inferInstanceAs (TotallyDisconnectedSpace (n → n' → Q.k))
    haveI : LocallyCompactSpace (Matrix Q.n₁ Q.n₀ Q.k) := inferInstanceAs (LocallyCompactSpace (Q.n₁ → Q.n₀ → Q.k))
    haveI : LocallyCompactSpace (Matrix Q.n₂ Q.n₁ Q.k) := inferInstanceAs (LocallyCompactSpace (Q.n₂ → Q.n₁ → Q.k))
    refine isBiTheta_of_prod Λ fun Ξ₁ Ξ₂ => ?_
    obtain ⟨φ₀, φ₀', hφ₀⟩ := GlobalTheory.ContractionLocal.exists_normPair Q.ψk Q.ν hψkc hν Q.n₁
    obtain ⟨Ξ', h1, h2⟩ := hΛe (GlobalTheory.ContractionLocal.colTens φ₀ Ξ₁) (GlobalTheory.ContractionLocal.rowTens φ₀' Ξ₂)
    have e : Ξ' = GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂ :=
      Subtype.ext (funext fun q => by rw [h1, GlobalTheory.ContractionLocal.contr_tens, hφ₀, mul_one]; rfl)
    rw [← e, ← h2]
    exact (GlobalTheory.T.besselThetaContraction_extendByZero_vacuum_smooth D ψ hstd _ _ S.B S.B' S.l S.J.W₀ S.vL _ _ (hU₁.theta _) (hU₂.theta _)).1
  have hθ : ∀ Ξ, IsBiTheta ψ S.B.A S.J.W₀ S.B'.A (biComb ψ S.B.A S.J.W₀ S.B'.A c₁ c₂ (Λ Ξ)) :=
    fun Ξ => GlobalTheory.T.isJointlySmoothBiTheta_twoVarCombination D ψ hstd _ _ _ _ (hΛθ Ξ) c₁ c₂
  obtain ⟨T, hT⟩ := GlobalTheory.T.doubleThetaLiftValue_bilinear D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ hΛθ
  have key : ∀ Ξ₁ Ξ₂ (f : GlobalTheory.TriStep.space Q), (GlobalTheory.LocFlat.CFac.prodSBBil _ _).compr₂ T Ξ₁ Ξ₂ f =
      GlobalTheory.TriStep.valK S Q c₁ c₂ φ Λ (GlobalTheory.LocFlat.CFac.prodSB Ξ₁ Ξ₂) f.1 := fun Ξ₁ Ξ₂ f => hT _ f
  refine ⟨GlobalTheory.TriStep.space Q, GlobalTheory.TriStep.rep Q, (GlobalTheory.LocFlat.CFac.prodSBBil _ _).compr₂ T, GlobalTheory.TriStep.smooth Q,
    fun y f => rfl, GlobalTheory.T.mem_space_of_typed_automorphic D ψ σ S Q, ⟨fun Ψ₁ => ⟨fun Ψ₂ g hg v => ?_, fun g Ψ Ψ' v h => ?_⟩, fun g Ψ₁ Ψ₁' Ψ₂ Ψ₂' h₁ h₂ => ?_⟩,
    GlobalTheory.T.doubleStepValue_eq_trilinearTensorValue D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ T₁ T₂ hT₁ hT₂ U₁ U₂ hU₁e hU₂e hΛe T hT, fun Ξ₁ Ξ₂ d₁ d₂ h₁ h₂ O₁ O₂ hO₁ hO₂ f => ?_⟩
  · rw [key, key]
    exact GlobalTheory.T.doubleLiftValue_equivariant_symmetricUnipotent D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ _ g hg v.1 v.2
  · rw [key, key]
    exact GlobalTheory.T.local_bimodel_translation D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ g Ψ₁ Ψ Ψ' h (hθ _) v.1 v.2
  · ext1 f
    rw [key, key]
    exact GlobalTheory.T.doubleThetaLiftValue_invariant_middleGL D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ g Ψ₁ Ψ₁' Ψ₂ Ψ₂' h₁ h₂ (hθ _) f.1 f.2
  · rw [key]
    exact GlobalTheory.TriStep.valK_comb D ψ hstd σ S Q c₁ c₂ hc₁ hc₂ φ hφ Λ hΛ T₁ T₂ hT₁ hT₂ U₁ U₂ hU₁e hU₂e hΛe Ξ₁ Ξ₂ d₁ d₂ h₁ h₂ O₁ O₂ hO₁ hO₂ f.1 f.2

end GlobalTheory.TriStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepTrilinearFormPropertiesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_doubleStep_trilinearForm_properties : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (S : Dbl2 ψ σ) (Q : QStep S) c₁ c₂, Q.Away c₁ → Q.Away c₂ → ∀ T₁ T₂, (ofSplit Q.q).IsModel ψ Q.F.G₀ Q.F.G₁ T₁ → (ofSplit Q.q).IsModel ψ Q.F.G₁ Q.F.G₂ T₂ → ∀ φ, IsContAut S.B.A φ → ∃ (A : Submodule ℂ (GA D S.B'.V → ℂ)) (τ : Representation ℂ (GL (Q.n₂ ⊕ Fin (Q.c + 1)) Q.k) A) (T : SB (Matrix Q.n₁ Q.n₀ Q.k) →ₗ[ℂ] SB (Matrix Q.n₂ Q.n₁ Q.k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), IsSmoothRep τ ∧ (∀ y (f : A), (τ y f).1 = rTrans (Q.gl₂ y) f.1) ∧ (∀ f, IsContAut S.B'.V f → Q.Typed f → f ∈ A) ∧ TriPos Q.ψk Q.μ₁ Q.μ₂ (σ + 1) τ T ∧ (∀ Φ₁ Φ₂ (f : A), HasTensorVal (fun Ψ Φ₀ => app (T Ψ) (opEFJ Q.ψk Q.ν (σ + 1) Φ₀.1 Φ₂.1) f) (fl Q.ψk Q.ν Q.μ₁ (σ + 1) Φ₁.1) (S.val c₁ c₂ (T₁ Φ₁) (T₂ Φ₂) φ f.1 1 1 1)) ∧ ∀ (Ξ₁ : SB (Matrix Q.n₁ Q.n₀ Q.k)) (Ξ₂ : SB (Matrix Q.n₂ Q.n₁ Q.k)) d₁ d₂, (ofSplit Q.q).IsCombAt ψ Q.F.F₀ Q.F.F₁ d₁ Ξ₁.1 → (ofSplit Q.q).IsCombAt ψ Q.F.F₁ Q.F.F₂ d₂ Ξ₂.1 → ∀ O₁ O₂, IsOne O₁ → IsOne O₂ → ∀ f : A, T Ξ₁ Ξ₂ f = S.val (aconv [c₁, d₁]) (aconv [c₂, d₂]) (T₁ O₁) (T₂ O₂) φ f.1 1 1 1 := by
  first | exact @GlobalTheory.TriStep.tri | exact GlobalTheory.TriStep.tri | (intros; apply GlobalTheory.TriStep.tri <;> assumption)
end
