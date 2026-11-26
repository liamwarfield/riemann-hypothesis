module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawLevelPrimeLawAllTuples
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiToBesselLocalModel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineContractionSplitPlaceLocalModel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymCollapseOfAllPositions
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AllPositionsHolds
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLastTwoStepsValueFixedLevelPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawPlaceLawsGiveFiniteIntegralLaws
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelGroupReferenceTuple
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometrySubspaceProperty

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedSupportAndValueAtFixedLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedValueCommonConstantsFixedLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepValueFixedLevelPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepValueFixedLevelPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.GValMid

theorem one_place : ∀ (D : D7) (c : Comm D) (v : VCom c) (G : GLoc v), c.Is → v.Is → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ C : ℂ, C ≠ 0 ∧
  ∀ (s₁ : StepBF c.ψ (c.B j (σ + 1) h) (c.J j (σ + 1) h)) (s₂ : StepFB c.ψ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h))) f₁ f₂,
    Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = G.q.v) f₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· = G.q.v) f₂ →
    c.ctr j σ h s₁ s₂ (comb c.ψ _ _ (G.eg j) f₁) (comb c.ψ _ _ (G.eg (j + 1)) f₂) =
      C • biComb c.ψ _ _ _ (G.cg j) (G.cg (j + 1)) (c.ctr j σ h s₁ s₂ f₁ f₂) := by
  intro D c v G hc hv j σ h
  have hs := G.hs
  have H : j + 1 + 1 + 2 * σ = G.s := by omega
  obtain ⟨C, hC, key⟩ := GlobalTheory.LocMod.GValProof.gval_of_laws D (GlobalTheory.T.flatMap_besselToFourierJacobi_localModel D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D) (GlobalTheory.T.weilDatum_localModel_formula D))
    (GlobalTheory.T.flatMap_fourierJacobiToBessel_localModel D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D) (GlobalTheory.T.weilDatum_localModel_formula D)) (GlobalTheory.T.lineContraction_splitPlace_localModel D GlobalTheory.LocFlat.contrFactor)
    (GlobalTheory.LocFlat.symCollapse_of_allPositions GlobalTheory.SymChain.allPositions_holds) G.k G.ν G.unitVol (GlobalTheory.LocMod.ofSplit G.q) G.s D.R.k
    G.S (Fin D.R.t) c.ψ G.char j (2 * σ) H
  refine ⟨C, hC, fun s₁ s₂ f₁ f₂ h₁ h₂ => ?_⟩
  have a₀ : j + (2 * σ + 1 + 1 + 1) = G.s + 1 := by omega
  have a₁ : j + 1 + (2 * σ + 1 + 1) = G.s + 1 := by omega
  have a₂ : j + 1 + 1 + (2 * σ + 1) = G.s + 1 := by omega
  have hne : G.sc j ≠ 0 := fun e => by
    have := G.sc_unit j
    rw [e, map_zero] at this
    exact zero_ne_one this
  let F : GlobalTheory.LocMod.Dbl (GlobalTheory.LocMod.ofSplit G.q) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) _ _ _ (2 * σ) :=
    ⟨G.sc j, hne, G.FX j (by omega), G.FX (j + 1) (by omega), G.FX (j + 1 + 1) (by omega), G.FY j _ a₀, G.FY (j + 1) _ a₁,
      G.FY (j + 1 + 1) _ a₂, G.bes j (σ + 1) h _ a₀, G.jac j (σ + 1) h _ a₁,
      G.sc_step j ▸ G.bes (j + 1 + 1) σ (idx_step h) _ a₂⟩
  obtain ⟨T₁, m₁, e₁⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D G.k G.q G.unit _ _ _ _ (G.FY j _ a₀) (G.FY (j + 1) _ a₁) c.ψ G.S.ψ hc.std G.char G.S.cond
    _ _ (hv.sd j (by omega)) (hv.sd (j + 1) (by omega)) (G.latY j _ a₀) (G.latY (j + 1) _ a₁)).2 f₁ h₁
  obtain ⟨T₂, m₂, e₂⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D G.k G.q G.unit _ _ _ _ (G.FY (j + 1) _ a₁) (G.FY (j + 1 + 1) _ a₂) c.ψ G.S.ψ hc.std G.char
    G.S.cond _ _ (hv.sd (j + 1) (by omega)) (hv.sd (j + 1 + 1) (by omega)) (G.latY (j + 1) _ a₁) (G.latY (j + 1 + 1) _ a₂)).2 f₂ h₂
  obtain ⟨O₁, o₁, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := G.k)
    (Y := GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin (2 * σ + 1 + 1))
    (Y' := GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (2 * σ + 1 + 1 + 1))
  obtain ⟨O₂, o₂, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := G.k)
    (Y := GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1 + 1) ⊕ Fin (2 * σ + 1))
    (Y' := GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin (2 * σ + 1 + 1))
  have b₁ : j + (2 * σ + 1 + 1) = G.s := by omega
  have b₂ : j + 1 + (2 * σ + 1) = G.s := by omega
  have g₁ := (G.eg_is j _ b₁).2 T₁ m₁ O₁ ⟨_, (GModel.phi_sb G).1 j _ b₁⟩ o₁ rfl
  have g₂ := (G.eg_is (j + 1) _ b₂).2 T₂ m₂ O₂ ⟨_, (GModel.phi_sb G).1 (j + 1) _ b₂⟩ o₂ rfl
  have := key σ _ _ _ F s₁ s₂ (c.lnk j σ h) (c.vL j σ h) (G.cg j) (G.cg (j + 1)) (G.cg_mid j _ b₂) (G.cg_mid (j + 1) _ H)
    T₁ T₂ m₁ m₂ ⟨_, (GModel.phi_sb G).1 j _ b₁⟩ ⟨_, (GModel.phi_sb G).1 (j + 1) _ b₂⟩ O₁ O₂ rfl rfl o₁ o₂
  rw [← e₁ O₁ o₁, ← e₂ O₂ o₂, ← g₁, ← g₂]
  exact this

theorem vac_foldr : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → ∀ j, j + 1 + 1 ≤ D.R.m →
  ∀ (i : Fin n) (L : List (Fin n)), i ∉ L → ∀ Ψ, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) Ψ →
    Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (G i).q.v) (L.foldr (fun i' f => comb c.ψ _ _ ((G i').eg j) f) Ψ) := by
  intro D c v n G hc _ hG j hj i L hi Ψ hΨ
  induction L with
  | nil => exact GlobalTheory.SeeSawRhs.vac_mono (fun p hp => (hG.places p).2 ⟨i, hp⟩) hΨ
  | cons a L ih =>
    have hs := (G a).hs
    have hai : (G a).q.v ≠ (G i).q.v := fun e => hi (by rw [hG.inj e]; exact List.mem_cons_self)
    have hat : CombAt (· = (G a).q.v) ((G a).eg j) := fun u hu r s => by
      rw [← ((G a).eg_is j ((G a).s - j) (by omega)).1 u hu r s]
      exact Ideal.mul_mem_right _ _ (GlobalTheory.FinPl.FrameLat.sum_mem_idAt (G a).q)
    exact ((GlobalTheory.DisjComb.main D c.ψ hc.std _ _ (· = (G a).q.v) (· = (G i).q.v) fun p h1 h2 => hai (h1.symm.trans h2)).2.1 _ hat).2
      _ _ _ (ih fun hm => hi (List.mem_cons_of_mem _ hm))

section Alg

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {A S A' : HSp D} {ι : Type} (a : ι → WO A S →₀ ℂ) (b : ι → WO S A' →₀ ℂ)

theorem comb_foldr (d : WO S A' →₀ ℂ) (C : WO A S → WO S A' → ℂ) (L : List ι) (u : WO A S) (w : WO S A') :
    comb ψ S A' d (fun w' => L.foldr (fun i f => comb ψ A S (a i) f) (fun u' => C u' w') u) w =
      L.foldr (fun i f => comb ψ A S (a i) f) (fun u' => comb ψ S A' d (C u') w) u := by
  induction L generalizing u with
  | nil => rfl
  | cons i L ih =>
    simp only [List.foldr_cons]
    refine (GlobalTheory.SeeSawRhs.comb_comm2 ψ A S A' (a i) d
      (fun u'' w' => L.foldr (fun i f => comb ψ A S (a i) f) (fun u' => C u' w') u'') u w).trans ?_
    congr 1
    funext u''
    exact ih u''

theorem biComb_foldr (C : WO A S → WO S A' → ℂ) (L : List ι) (u : WO A S) (w : WO S A') :
    L.foldr (fun i C' => biComb ψ A S A' (a i) (b i) C') C u w =
      L.foldr (fun i f => comb ψ A S (a i) f) (fun u' => L.foldr (fun i f => comb ψ S A' (b i) f) (C u') w) u := by
  induction L generalizing u w with
  | nil => rfl
  | cons i L ih =>
    simp only [List.foldr_cons]
    unfold biComb
    congr 1
    funext u'
    refine Eq.trans ?_ (comb_foldr ψ a (b i) (fun u'' => L.foldr (fun i f => comb ψ S A' (b i) f) (C u'')) L u' w)
    congr 1
    funext w'
    exact ih u' w'

theorem theta_foldr (C : WO A S → WO S A' → ℂ) (hC : ∀ w, IsThetaFunO ψ A S fun u => C u w) (L : List ι) (w : WO S A') :
    IsThetaFunO ψ A S fun u => L.foldr (fun i f => comb ψ S A' (b i) f) (C u) w := by
  induction L generalizing w with
  | nil => exact hC w
  | cons i L ih => exact GlobalTheory.SeeSawRhs.theta_comb_left (fun u => L.foldr (fun i f => comb ψ S A' (b i) f) (C u)) ih (b i) w

variable {ψ}

theorem theta_left {C : WO A S → WO S A' → ℂ} (h : IsBiTheta ψ A S A' C) (w : WO S A') : IsThetaFunO ψ A S fun u => C u w := by
  obtain ⟨U, hU, hl⟩ := h.levL
  refine ⟨fun γ u => h.quasiL γ u w, ⟨U, hU, fun x hx h0 => hl x hx h0 w⟩,
    h.cont.comp (continuous_id.prodMk continuous_const), fun k L hL h0 u => ?_⟩
  simpa using h.smooth k L 0 hL continuous_const h0 (fun t => Matrix.map_zero _ (finPart D).map_zero) u w

theorem theta_right {C : WO A S → WO S A' → ℂ} (h : IsBiTheta ψ A S A' C) (u : WO A S) : IsThetaFunO ψ S A' (C u) := by
  obtain ⟨U, hU, hl⟩ := h.levR
  refine ⟨fun γ w => h.quasiR γ u w, ⟨U, hU, fun x hx h0 => hl x hx h0 u⟩,
    h.cont.comp (continuous_const.prodMk continuous_id), fun k L hL h0 w => ?_⟩
  simpa using h.smooth k 0 L continuous_const hL (fun t => Matrix.map_zero _ (finPart D).map_zero) h0 u w

end Alg

theorem biComb_dG : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), GPin G → ∀ j, j + 1 < D.R.m →
  ∀ C : WO (c.X j) (c.X (j + 1)) → WO (c.X (j + 1)) (c.X (j + 1 + 1)) → ℂ,
    (∀ w, IsThetaFunO c.ψ _ _ fun u => C u w) → (∀ u, IsThetaFunO c.ψ _ _ (C u)) →
    biComb c.ψ _ _ _ (v.dG j) (v.dG (j + 1)) C =
      (List.finRange n).foldr (fun i C' => biComb c.ψ _ _ _ ((G i).cg j) ((G i).cg (j + 1)) C') C := by
  intro D c v n G hG j hj C h₁ h₂
  funext u w
  rw [biComb_foldr, ← hG.dG j (by omega) _ (theta_foldr c.ψ (fun i => (G i).cg (j + 1)) C h₁ _ w)]
  unfold biComb
  congr 1
  funext u'
  rw [hG.dG (j + 1) hj _ (h₂ u')]

theorem gValue_mid : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G →
  ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ C : ℂ, C ≠ 0 ∧
  ∀ (s₁ : StepBF c.ψ (c.B j (σ + 1) h) (c.J j (σ + 1) h)) (s₂ : StepFB c.ψ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)))
    Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.gP) Ψ₂ →
    c.ctr j σ h s₁ s₂ (comb c.ψ _ _ (v.eG j) Ψ₁) (comb c.ψ _ _ (v.eG (j + 1)) Ψ₂) =
      C • biComb c.ψ _ _ _ (v.dG j) (v.dG (j + 1)) (c.ctr j σ h s₁ s₂ Ψ₁ Ψ₂) := by
  intro D c v n G hc hv hG j σ h
  choose C hC key using fun i => one_place D c v (G i) hc hv j σ h
  refine ⟨((List.finRange n).map C).prod, List.prod_ne_zero fun h0 => ?_, fun s₁ s₂ Ψ₁ Ψ₂ h₁ h₂ => ?_⟩
  · obtain ⟨i, -, hi⟩ := List.mem_map.1 h0
    exact hC i hi
  have ind : ∀ L : List (Fin n), L.Nodup →
      c.ctr j σ h s₁ s₂ (L.foldr (fun i f => comb c.ψ _ _ ((G i).eg j) f) Ψ₁)
          (L.foldr (fun i f => comb c.ψ _ _ ((G i).eg (j + 1)) f) Ψ₂) =
        (L.map C).prod • L.foldr (fun i C' => biComb c.ψ _ _ _ ((G i).cg j) ((G i).cg (j + 1)) C') (c.ctr j σ h s₁ s₂ Ψ₁ Ψ₂) := by
    intro L hL
    induction L with
    | nil => simp
    | cons i L ih =>
      obtain ⟨hi, hL'⟩ := List.nodup_cons.1 hL
      simp only [List.foldr_cons, List.map_cons, List.prod_cons]
      rw [key i s₁ s₂ _ _ (vac_foldr D c v n G hc hv hG j (by omega) i L hi Ψ₁ h₁)
        (vac_foldr D c v n G hc hv hG (j + 1) (by omega) i L hi Ψ₂ h₂), ih hL', GlobalTheory.SeeSawRhs.biComb_smul, smul_smul]
  have hb : IsBiTheta c.ψ _ _ _ (c.ctr j σ h s₁ s₂ Ψ₁ Ψ₂) :=
    (GlobalTheory.T.besselThetaContraction_extendByZero_vacuum_smooth D c.ψ hc.std _ _ (c.B j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)) (c.lnk j σ h) (c.X (j + 1)) (c.vL j σ h) (flatBF s₁ Ψ₁) (flatFB s₂ Ψ₂)
      (((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D c.ψ fun _ => True).1 _ _ _ s₁).Heisenberg₂.theta _ h₁.1)
      (((GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D c.ψ fun _ => True).2 _ _ _ s₂).Heisenberg₂.theta _ h₂.1)).1
  rw [hG.eG j (by omega) _ h₁.1, hG.eG (j + 1) (by omega) _ h₂.1, ind _ (List.nodup_finRange n),
    biComb_dG D c v n G hG j (by omega) _ (theta_left hb) (theta_right hb)]

end GlobalTheory.SeeSaw.GValMid

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepValueFixedLevelPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G →
  ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∃ C : ℂ, C ≠ 0 ∧
  ∀ (s₁ : StepBF c.ψ (c.B j (σ + 1) h) (c.J j (σ + 1) h)) (s₂ : StepFB c.ψ (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h)))
    Ψ₁ Ψ₂, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) Ψ₁ → Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ v.gP) Ψ₂ →
    c.ctr j σ h s₁ s₂ (comb c.ψ _ _ (v.eG j) Ψ₁) (comb c.ψ _ _ (v.eG (j + 1)) Ψ₂) =
      C • biComb c.ψ _ _ _ (v.dG j) (v.dG (j + 1)) (c.ctr j σ h s₁ s₂ Ψ₁ Ψ₂) := by
  first | exact @GlobalTheory.SeeSaw.GValMid.gValue_mid | exact GlobalTheory.SeeSaw.GValMid.gValue_mid | (intros; apply GlobalTheory.SeeSaw.GValMid.gValue_mid <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedValueCommonConstantsFixedLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.GValAll

theorem gValue_common : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → ∃ a : ℕ → ℂ, (∀ j, a j ≠ 0) ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → GValue (t := t) (v.withCG a) := by
  intro D c v n G hc hv hG
  classical
  refine ⟨fun j => if h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m then (GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places D c v n G hc hv hG j h1.choose h1.choose_spec).choose
    else if h2 : ∃ h : j + 2 * 0 + 2 = D.R.m, c.Lz.rank = 1 ∧
      (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram then
      (GlobalTheory.T.seeSaw_lastTwoSteps_value_fixedLevel_places D c v n G hc hv hG j h2.fst h2.snd.1 h2.snd.2).choose else 1, ?_, ?_⟩
  · intro j
    dsimp only
    by_cases h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m
    · rw [dite_eq_left h1]; exact (GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places D c v n G hc hv hG j h1.choose h1.choose_spec).choose_spec.1
    · rw [dite_eq_right h1]
      by_cases h2 : ∃ h : j + 2 * 0 + 2 = D.R.m, c.Lz.rank = 1 ∧
          (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram
      · rw [dite_eq_left h2]; exact (GlobalTheory.T.seeSaw_lastTwoSteps_value_fixedLevel_places D c v n G hc hv hG j h2.fst h2.snd.1 h2.snd.2).choose_spec.1
      · rw [dite_eq_right h2]; exact one_ne_zero
  · intro t _ hw
    refine ⟨fun j σ h Ψ₁ Ψ₂ h₁ h₂ => ?_, fun j h Ψ₁ Ψ₂ h₁ h₂ => ?_⟩
    · have h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m := ⟨σ, h⟩
      have hσ : h1.choose = σ := by have := h1.choose_spec; omega
      show _ = (if h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m then _ else _) • _
      rw [dite_eq_left h1]
      have key := (GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places D c v n G hc hv hG j h1.choose h1.choose_spec).choose_spec.2
      revert key
      generalize (GlobalTheory.T.seeSaw_doubleStep_value_fixedLevel_places D c v n G hc hv hG j h1.choose h1.choose_spec).choose = C
      intro key
      subst hσ
      exact key _ _ Ψ₁ Ψ₂ h₁ h₂
    · have h1 : ¬ ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m := by rintro ⟨σ, hσ⟩; omega
      obtain ⟨hr, hτ⟩ := hw.tau j h
      have h2 : ∃ h : j + 2 * 0 + 2 = D.R.m, c.Lz.rank = 1 ∧
          (v.τ j h)ᴴ * ((c.bes j 0 h).L.gram * v.τ j h) = (-(D.host.xi0 * star D.host.xi0)) • c.Lz.gram := ⟨h, hr, hτ⟩
      show _ = (if h1 : ∃ σ, j + 2 * (σ + 1) + 2 = D.R.m then _ else _) • _
      rw [dite_eq_right h1, dite_eq_left h2]
      exact (GlobalTheory.T.seeSaw_lastTwoSteps_value_fixedLevel_places D c v n G hc hv hG j h2.fst h2.snd.1 h2.snd.2).choose_spec.2 _ Ψ₁ Ψ₂ h₁ h₂

end GlobalTheory.SeeSaw.GValAll
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedValueCommonConstantsFixedLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_unfoldedValue_commonConstants_fixedLevel : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → ∃ a : ℕ → ℂ, (∀ j, a j ≠ 0) ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → GValue (t := t) (v.withCG a) := by
  first | exact @GlobalTheory.SeeSaw.GValAll.gValue_common | exact GlobalTheory.SeeSaw.GValAll.gValue_common | (intros; apply GlobalTheory.SeeSaw.GValAll.gValue_common <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedSupportFixedLevelPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFlatMapContractionSupportAtLevelPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFlatMapContractionSupportAtLevelPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.SeeSaw.PlaceSupp

theorem supp_ctr : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → GlobalTheory.LocMod.GSupp2 D → ∀ (t : Tup c), t.Is → ∀ (Gi : GLoc v), Gi.Chars t → ∀ (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (F₁ : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F₁ → ∀ (F₂ : WO (c.V (j + 1)) (c.V (j + 1 + 1)) → ℂ), Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· = Gi.q.v) F₂ → ∀ (x : GA D (c.V (j + 1 + 1))), SuppAt Gi.q.e (c.V (j + 1 + 1)) x → c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) (comb c.ψ _ _ (Gi.eg j) F₁) (t.om (j + 1) (1, x) (comb c.ψ _ _ (Gi.eg (j + 1)) F₂)) ≠ 0 → ∃ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o, SuppAt Gi.q.e (c.V (j + 1 + 1)) r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit Gi.q).IsLoc (Gi.FY (j + 1 + 1) (2 * σ + 1) (by have := Gi.hs; omega)) u uk ∧ uk ∈ ((Gi.S.T (Fin D.R.t)).lev (j + 1 + 1) (2 * σ + 1) (by have := Gi.hs; omega)).J ∧ x = r * u := by
  intro D c v hc hv hG t ht Gi hch j σ h F₁ hF₁ F₂ hF₂ x hx hne
  have hs := Gi.hs
  obtain ⟨μ, hμ, hμu, -, h2⟩ := hch
  obtain ⟨hPhi, hLev⟩ := GlobalTheory.SeeSaw.MuUnits.withMu_eq Gi.k _ _ Gi.S (Fin D.R.t) μ hμ hμu
  have a₀ : j + (2 * σ + 1 + 1 + 1) = Gi.s + 1 := by omega
  have a₁ : j + 1 + (2 * σ + 1 + 1) = Gi.s + 1 := by omega
  have a₂ : j + 1 + 1 + (2 * σ + 1) = Gi.s + 1 := by omega
  have b₀ : j + (2 * σ + 1 + 1) = Gi.s := by omega
  have b₁ : j + 1 + (2 * σ + 1) = Gi.s := by omega
  obtain ⟨T₁, hT₁, hO₁⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D Gi.k Gi.q Gi.unit _ _ (c.V j) (c.V (j + 1)) (Gi.FY j _ a₀) (Gi.FY (j + 1) _ a₁)
    c.ψ Gi.S.ψ hc.std Gi.char Gi.S.cond (v.N j) (v.N (j + 1)) (hv.sd j (by omega)) (hv.sd (j + 1) (by omega))
    (Gi.latY j _ a₀) (Gi.latY (j + 1) _ a₁)).2 F₁ hF₁
  obtain ⟨T₂, hT₂, hO₂⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D Gi.k Gi.q Gi.unit _ _ (c.V (j + 1)) (c.V (j + 1 + 1)) (Gi.FY (j + 1) _ a₁)
    (Gi.FY (j + 1 + 1) _ a₂) c.ψ Gi.S.ψ hc.std Gi.char Gi.S.cond (v.N (j + 1)) (v.N (j + 1 + 1)) (hv.sd (j + 1) (by omega))
    (hv.sd (j + 1 + 1) (by omega)) (Gi.latY (j + 1) _ a₁) (Gi.latY (j + 1 + 1) _ a₂)).2 F₂ hF₂
  obtain ⟨O₁, h1⟩ := GlobalTheory.BiComb.exists_isOne (k := Gi.k) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin (2 * σ + 1 + 1))
    (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (2 * σ + 1 + 1 + 1))
  obtain ⟨O₂, h1'⟩ := GlobalTheory.BiComb.exists_isOne (k := Gi.k) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1 + 1) ⊕ Fin (2 * σ + 1))
    (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin (2 * σ + 1 + 1))
  have m₁ : (Gi.S.T (Fin D.R.t)).Phi j _ b₀ ∈ GlobalTheory.SplitWeil.SB _ := (GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _).1 j _ b₀
  have m₂ : (Gi.S.T (Fin D.R.t)).Phi (j + 1) _ b₁ ∈ GlobalTheory.SplitWeil.SB _ :=
    (GlobalTheory.StepData.Chain.ofType_regular _ _ _ _ _).1 (j + 1) _ b₁
  have e₁ := (Gi.eg_is j _ b₀).2 T₁ hT₁ O₁ ⟨_, m₁⟩ h1 rfl
  have e₂ := (Gi.eg_is (j + 1) _ b₁).2 T₂ hT₂ O₂ ⟨_, m₂⟩ h1' rfl
  rw [hO₁ O₁ h1] at e₁
  rw [hO₂ O₂ h1'] at e₂
  rw [← e₁, ← e₂, ← (ht.sFB j σ h).1] at hne
  let F : GlobalTheory.LocMod.Dbl (GlobalTheory.LocMod.ofSplit Gi.q) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h))
      (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) j) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1))
      (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1 + 1)) (2 * σ) :=
    { s := Gi.sc j
      s_ne := fun h0 => by
        have h3 := Gi.sc_unit j
        rw [h0, map_zero] at h3
        exact zero_ne_one h3
      F₀ := Gi.FX j (by omega)
      F₁ := Gi.FX (j + 1) (by omega)
      F₂ := Gi.FX (j + 1 + 1) (by omega)
      G₀ := Gi.FY j _ a₀
      G₁ := Gi.FY (j + 1) _ a₁
      G₂ := Gi.FY (j + 1 + 1) _ a₂
      bes := Gi.bes j (σ + 1) h _ a₀
      jac := Gi.jac j (σ + 1) h _ a₁
      bes' := by
        rw [← Gi.sc_step j]
        exact Gi.bes (j + 1 + 1) σ (idx_step h) _ a₂ }
  obtain ⟨r, hr, hrs, u, uk, hu, huk, hxr⟩ := hG Gi.k (GlobalTheory.LocMod.ofSplit Gi.q) Gi.s D.R.k (withMu Gi.S μ hμ) (Fin D.R.t) c.ψ
    Gi.char j (2 * σ) (by omega) σ _ _ _ F (t.sBF j (σ + 1) h) (t.sFB j σ h) (c.lnk j σ h) (c.vL j σ h) (h2 j σ h).1
    T₁ T₂ hT₁ hT₂ ⟨_, m₁⟩ ⟨_, m₂⟩ (hPhi j _ b₀).symm (hPhi (j + 1) _ b₁).symm x hx hne
  rw [(hLev (j + 1 + 1) _ a₂).1] at huk
  exact ⟨r, hr, hrs, u, uk, hu, huk, hxr⟩

end GlobalTheory.SeeSaw.PlaceSupp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFlatMapContractionSupportAtLevelPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_flatMap_contraction_support_at_level_place : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → GlobalTheory.LocMod.GSupp2 D → ∀ (t : Tup c), t.Is → ∀ (Gi : GLoc v), Gi.Chars t → ∀ (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (F₁ : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F₁ → ∀ (F₂ : WO (c.V (j + 1)) (c.V (j + 1 + 1)) → ℂ), Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· = Gi.q.v) F₂ → ∀ (x : GA D (c.V (j + 1 + 1))), SuppAt Gi.q.e (c.V (j + 1 + 1)) x → c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) (comb c.ψ _ _ (Gi.eg j) F₁) (t.om (j + 1) (1, x) (comb c.ψ _ _ (Gi.eg (j + 1)) F₂)) ≠ 0 → ∃ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o, SuppAt Gi.q.e (c.V (j + 1 + 1)) r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit Gi.q).IsLoc (Gi.FY (j + 1 + 1) (2 * σ + 1) (by have := Gi.hs; omega)) u uk ∧ uk ∈ ((Gi.S.T (Fin D.R.t)).lev (j + 1 + 1) (2 * σ + 1) (by have := Gi.hs; omega)).J ∧ x = r * u := by
  first | exact @GlobalTheory.SeeSaw.PlaceSupp.supp_ctr | exact GlobalTheory.SeeSaw.PlaceSupp.supp_ctr | (intros; apply GlobalTheory.SeeSaw.PlaceSupp.supp_ctr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawFirstFlatMapSupportAtLevelPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawFirstFlatMapSupportAtLevelPlace
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.GSuppFirst

theorem gsupp1_at : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → GlobalTheory.LocMod.GSupp1 D → ∀ (t : Tup c), t.Is → ∀ (Gi : GLoc v), Gi.Chars t → ∀ (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (F : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F → ∀ (x : GA D (c.V (j + 1))), SuppAt Gi.q.e (c.V (j + 1)) x → flatBF (t.sBF j (σ + 1) h) (t.om j (1, x) (comb c.ψ _ _ (Gi.eg j) F)) ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, SuppAt Gi.q.e (c.V (j + 1)) r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit Gi.q).IsLoc (Gi.FY (j + 1) (2 * σ + 1 + 1) (by have := Gi.hs; omega)) u uk ∧ uk ∈ ((Gi.S.T (Fin D.R.t)).lev (j + 1) (2 * σ + 1 + 1) (by have := Gi.hs; omega)).J ∧ x = r * u := by
  intro D c v hc hv hG t ht Gi hch j σ h F hF x hx hflat
  have hs := Gi.hs
  obtain ⟨Tm, hTm, hTmO⟩ := (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D Gi.k Gi.q Gi.unit _ _ (c.V j) (c.V (j + 1))
    (Gi.FY j (2 * σ + 1 + 1 + 1) (by omega)) (Gi.FY (j + 1) (2 * σ + 1 + 1) (by omega)) c.ψ Gi.S.ψ hc.std Gi.char Gi.S.cond
    (v.N j) (v.N (j + 1)) (hv.sd j (by omega)) (hv.sd (j + 1) (by omega)) (Gi.latY j _ _) (Gi.latY (j + 1) _ _)).2 F hF
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := Gi.k)
    (Y := GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1) ⊕ Fin (2 * σ + 1 + 1))
    (Y' := GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (2 * σ + 1 + 1 + 1))
  have H2 : j + (2 * σ + 1 + 1) = Gi.s := by omega
  let Φ : GlobalTheory.SplitWeil.SB _ := ⟨_, (GModel.phi_sb Gi).1 j (2 * σ + 1 + 1) H2⟩
  have hcomb : Tm Φ = comb c.ψ _ _ (Gi.eg j) F := by
    rw [← hTmO O hO]; exact (Gi.eg_is j (2 * σ + 1 + 1) H2).2 Tm hTm O Φ hO rfl
  obtain ⟨μ, hμt, hμu, hBF, -⟩ := hch
  have hW := MuUnits.withMu_eq Gi.k Gi.s D.R.k Gi.S (Fin D.R.t) μ hμt hμu
  let Fd : GlobalTheory.LocMod.Dbl (GlobalTheory.LocMod.ofSplit Gi.q) (c.B j (σ + 1) h) (c.J j (σ + 1) h) (c.B (j + 1 + 1) σ (idx_step h))
      (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) j) (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1))
      (GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) (j + 1 + 1)) (2 * σ) :=
    { s := Gi.sc j
      s_ne := fun h0 => by have := Gi.sc_unit j; rw [h0, map_zero] at this; exact zero_ne_one this
      F₀ := Gi.FX j (by omega)
      F₁ := Gi.FX (j + 1) (by omega)
      F₂ := Gi.FX (j + 1 + 1) (by omega)
      G₀ := Gi.FY j (2 * σ + 1 + 1 + 1) (by omega)
      G₁ := Gi.FY (j + 1) (2 * σ + 1 + 1) (by omega)
      G₂ := Gi.FY (j + 1 + 1) (2 * σ + 1) (by omega)
      bes := Gi.bes j (σ + 1) h _ _
      jac := Gi.jac j (σ + 1) h _ _
      bes' := by rw [← Gi.sc_step j]; exact Gi.bes (j + 1 + 1) σ (idx_step h) _ _ }
  have hΦ : Φ.1 = ((withMu Gi.S μ hμt).T (Fin D.R.t)).Phi j (2 * σ + 1 + 1) (by omega) := (hW.1 j _ _).symm
  have hflat' : flatBF (t.sBF j (σ + 1) h) ((t.sBF j (σ + 1) h).om (1, x) (Tm Φ)) ≠ 0 := by
    rw [(ht.sBF j (σ + 1) h).1, hcomb]; exact hflat
  obtain ⟨r, hr, hrs, u, uk, hloc, huk, hxr⟩ := hG Gi.k (GlobalTheory.LocMod.ofSplit Gi.q) Gi.s D.R.k (withMu Gi.S μ hμt) (Fin D.R.t) c.ψ
    Gi.char j (2 * σ) (by omega) σ _ _ _ Fd (t.sBF j (σ + 1) h) (hBF j (σ + 1) h).1 Tm hTm Φ hΦ x hx hflat'
  refine ⟨r, hr, hrs, u, uk, hloc, ?_, hxr⟩
  rw [← (hW.2 (j + 1) (2 * σ + 1 + 1) (by omega)).1]; exact huk

end GlobalTheory.SeeSaw.GSuppFirst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawFirstFlatMapSupportAtLevelPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_first_flatMap_support_at_level_place : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → GlobalTheory.LocMod.GSupp1 D → ∀ (t : Tup c), t.Is → ∀ (Gi : GLoc v), Gi.Chars t → ∀ (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (F : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F → ∀ (x : GA D (c.V (j + 1))), SuppAt Gi.q.e (c.V (j + 1)) x → flatBF (t.sBF j (σ + 1) h) (t.om j (1, x) (comb c.ψ _ _ (Gi.eg j) F)) ≠ 0 → ∃ r ∈ jacGrp (c.jac j (σ + 1) h).d, SuppAt Gi.q.e (c.V (j + 1)) r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit Gi.q).IsLoc (Gi.FY (j + 1) (2 * σ + 1 + 1) (by have := Gi.hs; omega)) u uk ∧ uk ∈ ((Gi.S.T (Fin D.R.t)).lev (j + 1) (2 * σ + 1 + 1) (by have := Gi.hs; omega)).J ∧ x = r * u := by
  first | exact @GlobalTheory.SeeSaw.GSuppFirst.gsupp1_at | exact GlobalTheory.SeeSaw.GSuppFirst.gsupp1_at | (intros; apply GlobalTheory.SeeSaw.GSuppFirst.gsupp1_at <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrderedProdLocalPartsSeparatesPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrderedProdLocalPartsSeparatesPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.SepProd

variable {D : D7}

theorem list_ofFn_prod_eq {M : Type*} [Monoid M] : ∀ {n : ℕ} (f : Fin n → M) (i : Fin n), (∀ j, j ≠ i → f j = 1) →
    (List.ofFn f).prod = f i
  | 0, _, i, _ => i.elim0
  | n + 1, f, i, h => by
    rw [List.ofFn_succ, List.prod_cons]
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
    · have hprod : (List.ofFn fun j : Fin n => f j.succ).prod = 1 :=
        List.prod_eq_one (List.forall_mem_ofFn_iff.mpr fun j => h _ (Fin.succ_ne_zero j))
      rw [hprod, mul_one]
    · rw [h 0 (Fin.succ_ne_zero i').symm, one_mul]
      exact list_ofFn_prod_eq (fun j => f j.succ) i' fun j hj => h _ fun e => hj (Fin.succ_injective _ e)

theorem mem_grpOff_of_suppAt {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : GlobalTheory.FinPl.SplitPt D k) {V : HSp D} {g : GA D V} (hg : SuppAt p.e V g) {v : GlobalTheory.FinPl.Pl D} (hv : p.v ≠ v) :
    g ∈ grpOff V (· = v) := by
  rw [grpOff, congGrp, MonoidHom.mem_ker]
  ext i j
  change Ideal.Quotient.mk _ (Formalism.L2.Theta.mt V g i j) = (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j
  rw [← Matrix.map_one (Ideal.Quotient.mk (idOff D (· = v))) (map_zero _) (map_one _), Matrix.map_apply,
    Ideal.Quotient.eq]
  have hmem : Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ idAt D (· = p.v) := by
    have := hg i j
    rw [Matrix.sub_apply] at this
    rw [← this]
    exact Ideal.mul_mem_right _ _ (GlobalTheory.FinPl.FrameLat.sum_mem_idAt p)
  have h2 := (Ideal.mem_inf.1 hmem).2
  rw [Ideal.mem_iInf] at h2
  rw [idOff, Ideal.mem_iInf]
  rintro ⟨w, rfl⟩
  exact h2 ⟨w, fun e => hv e.symm⟩

end GlobalTheory.SeeSaw.SepProd


open GlobalTheory.SeeSaw.SepProd in
theorem GlobalTheory.SeeSaw.SepProd.prod_sep : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ} (G : Fin n → GLoc v), GPin G → ∀ (j' : ℕ) (xs : Fin n → GA D (c.V j')), (∀ i, SuppAt (G i).q.e (c.V j') (xs i)) → ∀ (i : Fin n), ∃ y ∈ grpOff (c.V j') (· = (G i).q.v), (List.ofFn xs).prod = xs i * y := by
  intro D c v n G hG j' xs hxs i
  refine ⟨(xs i)⁻¹ * (List.ofFn xs).prod, ?_, by rw [mul_inv_cancel_left]⟩
  have hoff : ∀ i', i' ≠ i → xs i' ∈ grpOff (c.V j') (· = (G i).q.v) := fun i' hi' =>
    mem_grpOff_of_suppAt (G i').q (hxs i') fun e => hi' (hG.inj e)
  rw [grpOff, congGrp, MonoidHom.mem_ker, map_mul, map_inv, map_list_prod, List.map_ofFn,
    list_ofFn_prod_eq (_ ∘ xs) i fun j hj => MonoidHom.mem_ker.1 (hoff j hj), Function.comp_apply, inv_mul_cancel]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OrderedProdLocalPartsSeparatesPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordered_prod_local_parts_separates_place : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ} (G : Fin n → GLoc v), GPin G → ∀ (j' : ℕ) (xs : Fin n → GA D (c.V j')), (∀ i, SuppAt (G i).q.e (c.V j') (xs i)) → ∀ (i : Fin n), ∃ y ∈ grpOff (c.V j') (· = (G i).q.v), (List.ofFn xs).prod = xs i * y := by
  first | exact @GlobalTheory.SeeSaw.SepProd.prod_sep | exact GlobalTheory.SeeSaw.SepProd.prod_sep | (intros; apply GlobalTheory.SeeSaw.SepProd.prod_sep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedSupportFixedLevelPlaces
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.GSuppAsm

theorem gsupp_of_local : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → GlobalTheory.LocMod.GSupp1 D → GlobalTheory.LocMod.GSupp2 D → FlatLaw D → ∀ t : Tup c, t.Is → (∀ i, (G i).Chars t) → GSupp (t := t) v := by
  intro D c v n G hc hv hG h1 h2 _hfl t ht hch j σ h Ψ₁ Ψ₂ hΨ₁ hΨ₂
  have hj : j + 1 < D.R.m := by omega
  have hj2 : j + 1 + 1 < D.R.m := by omega
  refine ⟨fun x hx hne => ?_, fun x hx hne => ?_⟩
  · obtain ⟨xs, hxs, rfl⟩ := GlobalTheory.T.seeSaw_fixedLevel_element_eq_prod_local_parts hc hv G hG (j + 1) x hx
    have hb : ∀ i, j + 1 + (2 * σ + 1 + 1) = (G i).s + 1 := fun i => by have := (G i).hs; omega
    refine GlobalTheory.T.seeSaw_prod_local_cells_distinct_places G hG (j + 1) hj (jacGrp (c.jac j (σ + 1) h).d) (fun _ => 2 * σ + 1 + 1) hb xs (fun i => ?_)
    obtain ⟨F, hF, hcomb⟩ := GlobalTheory.T.seeSaw_fixedLevel_combination_eq_single_place_on_vacuum hc hv G hG j hj Ψ₁ hΨ₁ i
    obtain ⟨y, hy, hprod⟩ := GlobalTheory.T.ordered_prod_local_parts_separates_place G hG (j + 1) xs hxs i
    have hw : IsWeilDatumO c.ψ (c.V j) (c.V (j + 1)) (t.sBF j (σ + 1) h).χV (t.sBF j (σ + 1) h).χW (t.om j) := by
      have := (t.sBF j (σ + 1) h).weil
      rw [(ht.sBF j (σ + 1) h).1] at this
      exact this
    obtain ⟨hF', hcm⟩ := GlobalTheory.T.trivialAtPlace_comm_seeSawCombination_keeps_vacuum hc hv (G i) j hj _ _ (t.om j) hw F hF y hy
    refine GlobalTheory.T.seesaw_first_flatMap_support_at_level_place hc hv h1 t ht (G i) (hch i) j σ h _ hF' (xs i) (hxs i) ?_
    rw [hprod, hcomb] at hne
    have e : t.om j (1, xs i * y) = t.om j (1, xs i) * t.om j (1, y) := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e, Module.End.mul_apply, hcm] at hne
    exact hne
  · obtain ⟨xs, hxs, rfl⟩ := GlobalTheory.T.seeSaw_fixedLevel_element_eq_prod_local_parts hc hv G hG (j + 1 + 1) x hx
    have hb : ∀ i, j + 1 + 1 + (2 * σ + 1) = (G i).s + 1 := fun i => by have := (G i).hs; omega
    refine GlobalTheory.T.seeSaw_prod_local_cells_distinct_places G hG (j + 1 + 1) (by omega) (besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o)
      (fun _ => 2 * σ + 1) hb xs (fun i => ?_)
    obtain ⟨F₁, hF₁, hcomb₁⟩ := GlobalTheory.T.seeSaw_fixedLevel_combination_eq_single_place_on_vacuum hc hv G hG j hj Ψ₁ hΨ₁ i
    obtain ⟨F₂, hF₂, hcomb₂⟩ := GlobalTheory.T.seeSaw_fixedLevel_combination_eq_single_place_on_vacuum hc hv G hG (j + 1) hj2 Ψ₂ hΨ₂ i
    obtain ⟨y, hy, hprod⟩ := GlobalTheory.T.ordered_prod_local_parts_separates_place G hG (j + 1 + 1) xs hxs i
    have hw : IsWeilDatumO c.ψ (c.V (j + 1)) (c.V (j + 1 + 1)) (t.sFB j σ h).χV (t.sFB j σ h).χW (t.om (j + 1)) := by
      have := (t.sFB j σ h).weil
      rw [(ht.sFB j σ h).1] at this
      exact this
    obtain ⟨hF₂', hcm⟩ := GlobalTheory.T.trivialAtPlace_comm_seeSawCombination_keeps_vacuum hc hv (G i) (j + 1) hj2 _ _ (t.om (j + 1)) hw F₂ hF₂ y hy
    refine GlobalTheory.T.seeSaw_flatMap_contraction_support_at_level_place hc hv h2 t ht (G i) (hch i) j σ h F₁ hF₁ _ hF₂' (xs i) (hxs i) ?_
    rw [hprod, hcomb₁, hcomb₂] at hne
    have e : t.om (j + 1) (1, xs i * y) = t.om (j + 1) (1, xs i) * t.om (j + 1) (1, y) := by
      rw [← map_mul, Prod.mk_mul_mk, one_mul]
    rw [e, Module.End.mul_apply, hcm] at hne
    exact hne

end GlobalTheory.SeeSaw.GSuppAsm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedSupportFixedLevelPlacesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_unfoldedSupport_fixedLevelPlaces : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → GlobalTheory.LocMod.GSupp1 D → GlobalTheory.LocMod.GSupp2 D → FlatLaw D → ∀ t : Tup c, t.Is → (∀ i, (G i).Chars t) → GSupp (t := t) v := by
  first | exact @GlobalTheory.SeeSaw.GSuppAsm.gsupp_of_local | exact GlobalTheory.SeeSaw.GSuppAsm.gsupp_of_local | (intros; apply GlobalTheory.SeeSaw.GSuppAsm.gsupp_of_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapSupportFirstHalfAtLevelPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapSupportFirstHalfAtLevelPlace
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.StepData GlobalTheory.SymChain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocMod.SuppFirst

theorem e_mul_ι {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (x : k) : p.e * p.ι x = p.ι x := by
  rw [← p.ι_π, p.π_ι]

theorem ι_mul' {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (x y : k) : p.ι (x * y) = p.ι x * p.ι y := by
  have h := p.ι_π (p.ι x * p.ι y)
  rw [map_mul, p.π_ι, p.π_ι, ← mul_assoc, e_mul_ι] at h
  exact h

theorem ι_one' {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : p.ι 1 = p.e := by
  have h := p.ι_π 1
  rwa [map_one, mul_one] at h

theorem shift_mul {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (x y : k) :
    (p.ι x + (1 - p.e)) * (p.ι y + (1 - p.e)) = p.ι (x * y) + (1 - p.e) := by
  have he : p.e * p.e = p.e := p.split.1
  have h1 : p.ι x * (1 - p.e) = 0 := by
    rw [mul_sub, mul_one, mul_comm, e_mul_ι, sub_self]
  have h2 : (1 - p.e) * p.ι y = 0 := by
    rw [sub_mul, one_mul, e_mul_ι, sub_self]
  have h3 : (1 - p.e) * (1 - p.e) = 1 - p.e := by
    rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
  rw [ι_mul', add_mul, mul_add, mul_add, h1, h2, h3, add_zero, zero_add]

def shiftU {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : kˣ →* (AE D)ˣ where
  toFun x := ⟨p.ι x + (1 - p.e), p.ι (x⁻¹ : kˣ) + (1 - p.e), by
      rw [shift_mul, Units.mul_inv, ι_one']; ring, by
      rw [shift_mul, Units.inv_mul, ι_one']; ring⟩
  map_one' := by ext; simp [ι_one']
  map_mul' x y := by ext; simp [shift_mul]

theorem exists_comp {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (χ : (AE D)ˣ →* Circle) : ∃ μ : kˣ →* ℂˣ, p.IsComp χ μ := by
  refine ⟨Circle.toUnits.comp (χ.comp (shiftU p)), fun x a ha => ?_⟩
  have : shiftU p x = a := Units.ext ha.symm
  simp [this]

theorem card_frame {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (Fr : Frame k N Y) :
    Fintype.card Y = N := by
  apply le_antisymm
  · have h := Matrix.rank_mul_le_left Fr.γ Fr.β
    rw [Fr.γβ, Matrix.rank_one] at h
    have h' := Matrix.rank_le_card_width Fr.γ
    rw [Fintype.card_fin] at h'
    exact h.trans h'
  · have h := Matrix.rank_mul_le_left Fr.β Fr.γ
    rw [Fr.βγ, Matrix.rank_one, Fintype.card_fin] at h
    exact h.trans (Matrix.rank_le_card_width Fr.β)

def prH {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) : D.host.E →+* k := p.π.comp (incA D)

theorem prH_apply {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) (a : D.host.E) : prH p a = p.pr a := rfl

theorem exists_coreFrame {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {σ : ℕ} {B : BesLev D (σ + 1)} {J : JacLev D (σ + 1)} {B' : BesLev D σ} {n₀ n₁ n₂ : Type}
    [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] {c : ℕ}
    (F : Dbl p B J B' n₀ n₁ n₂ c) : ∃ C : Frame k B.V₀.rank (n₀ ⊕ Unit), p.IsCoreFrame B F.s F.F₀ C := by
  obtain ⟨hc, hA, -, hz, -⟩ := F.bes
  let M : Matrix (Fin B.V₀.rank) (n₀ ⊕ Unit) k :=
    fromCols (B.o.iA.map p.pr * F.F₀.β) (Matrix.of fun r (_ : Unit) => F.s * p.pr (vecB B.o B.ζ r))
  let f : n₀ ⊕ Unit → n₀ ⊕ Fin (c + 1 + 1 + 1) := Sum.elim Sum.inl fun _ => Sum.inr ⟨σ + 1, by omega⟩
  have hf : Function.Injective f := by
    rintro (a | _) (b | _) h <;> simp_all [f]
  have key : B.d.i₀.map p.pr * M = F.G₀.β.submatrix id f := by
    ext r (a | _)
    · simp only [M, f, Matrix.mul_fromCols, fromCols_apply_inl, submatrix_apply, id, Sum.elim_inl]
      rw [hA r a, ← Matrix.mul_assoc]
      have hm : B.d.i₀.map p.pr * B.o.iA.map p.pr = (B.d.i₀ * B.o.iA).map p.pr :=
        (Matrix.map_mul (f := prH p)).symm
      rw [hm]
    · simp only [M, f, Matrix.mul_fromCols, fromCols_apply_inr, submatrix_apply, id, Sum.elim_inr]
      rw [hz ⟨σ + 1, by omega⟩ rfl r]
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, mulVec, dotProduct]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← prH_apply, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [map_mul, prH_apply, prH_apply]
      ring
  let L : Matrix (n₀ ⊕ Unit) (Fin B.V₀.rank) k := F.G₀.γ.submatrix f id * B.d.i₀.map p.pr
  have hLM : L * M = 1 := by
    simp only [L, Matrix.mul_assoc, key]
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, F.G₀.γβ]
    exact Matrix.submatrix_one _ hf
  have hcard : Fintype.card (n₀ ⊕ Unit) = B.V₀.rank := by
    have h1 := card_frame F.G₀
    have h2 := B.d.rank_add
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at h1 ⊢
    omega
  have hML : M * L = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (n₀ ⊕ Unit) (Fin B.V₀.rank) k (A := L) (B := M) (by simpa using hcard)).mp hLM
  refine ⟨⟨M, L, hML, hLM⟩, fun r a => ?_, fun r => ?_⟩
  · simp [M]
  · simp [M]

theorem isLoc_one {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {V : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (Fr : Frame k V.rank Y) : p.IsLoc Fr 1 1 := by
  obtain ⟨hloc, -, -⟩ := GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k p
  obtain ⟨g₀, hg₀, hu⟩ := (hloc V Y Fr).1 1
  have h2 := (hloc V Y Fr).2.2 _ _ _ _ hg₀ hg₀
  rw [mul_one] at h2
  have e : g₀ * g₀ = g₀ := hu _ h2
  have : g₀ = 1 := by
    have := congrArg (g₀⁻¹ * ·) e
    simpa [← mul_assoc] using this
  exact this ▸ hg₀

theorem gsupp1 : ∀ (D : D7), OmLoc D → FlatBF D → GlobalTheory.LocFlat.SymCollapse → GSupp1 D := by
  intro D hOm hFl hSym k _ _ _ _ p s κ S t _ _ ψ hψ j c H σ B J B' F s₁ hμ T₁ hT₁ Φ₁ hΦ₁ h hh hne
  obtain ⟨hloc, hjac, -⟩ := GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k p
  letI : MeasurableSpace k := borel k
  haveI : BorelSpace k := ⟨rfl⟩
  obtain ⟨ν, hν⟩ := exists_isUnitVol k
  haveI := hν.1
  obtain ⟨hk, hhk⟩ := (hloc J.W _ F.G₁).2.1 h hh
  have hc : c = 2 * σ := by have := F.bes.1; omega

  obtain ⟨μT, hT⟩ := exists_comp p s₁.χW
  have hS : p.IsComp s₁.χV (S.μ (j + 1))⁻¹ := by
    intro x a ha
    have := hμ x a ha
    simp only [MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Circle.coe_inv] at this ⊢
    rw [this, inv_inv]

  let Φ' : SB (Matrix (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1 + 1)) (XIx (Fin κ) t j ⊕ Fin (c + 1 + 1 + 1)) k) :=
    ⟨om (S.μ (j + 1)) 1 hk Φ₁.1, om_mem_SB (μ := S.μ (j + 1)) (1 : GL _ k) hk Φ₁.2⟩
  have hom : s₁.om (1, h) (T₁ Φ₁) = T₁ Φ' := by
    refine hOm k p ψ B.V J.W s₁.χV s₁.χW s₁.om s₁.weil _ μT hS hT _ _ F.G₀ F.G₁ T₁ hT₁ 1 1 h hk
      (isLoc_one p _) hhk Φ₁ Φ' ?_
    simp [Φ']

  obtain ⟨C, hC⟩ := exists_coreFrame p F
  obtain ⟨T₀, -, hT₀⟩ := hFl k p ν hν.1 ψ S.ψ hψ (σ + 1) B J s₁ F.s F.s_ne _ _ (c + 1 + 1) F.F₀ C F.G₀ F.F₁ F.G₁
    hC F.bes F.jac T₁ hT₁
  have hSB := ((GlobalTheory.T.flatMaps_preserve_schwartzBruhat_and_surjective k S.ψ ν S.cond.continuous hν.1 _ _ (c + 1 + 1) (σ + 1 + 1) (by omega)).1
    (by omega)).1 Φ'.1 Φ'.2
  have hflat := hT₀ Φ' ⟨_, hSB⟩ rfl
  rw [hom, hflat] at hne
  have hne' : GlobalTheory.LocFlat.flCol S.ψ ν (σ + 1 + 1) (om (S.μ (j + 1)) 1 hk ((S.T t).Phi j (c + 1 + 1) (by omega))) ≠ 0 := by
    intro h0
    apply hne
    have : (⟨_, hSB⟩ : SB _) = 0 := by
      ext1
      simpa [Φ', hΦ₁] using h0
    rw [this, map_zero]
  obtain ⟨β, q, hq, u, hu, hkeq⟩ := (hSym k ν hν s κ S t).1 j (c + 1) (by omega) (σ + 1) (by omega) hk hne'
  obtain ⟨r, hr, -⟩ := (hloc J.W _ F.G₁).1 (colE (c + 1 + 1) (σ + 1 + 1) β * q)
  obtain ⟨u', hu', -⟩ := (hloc J.W _ F.G₁).1 u
  have hprod := (hloc J.W _ F.G₁).2.2 _ _ _ _ hr hu'
  rw [← hkeq] at hprod
  obtain ⟨g', -, huniq⟩ := (hloc J.W _ F.G₁).1 hk
  refine ⟨r, hjac _ _ _ _ _ _ _ _ F.jac r β q hq hr, hr.1, u', u, hu', hu, ?_⟩
  exact (huniq _ hhk).trans (huniq _ hprod).symm

end GlobalTheory.LocMod.SuppFirst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapSupportFirstHalfAtLevelPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_map_support_first_half_at_level_place : ∀ (D : D7), OmLoc D → FlatBF D → GlobalTheory.LocFlat.SymCollapse → GSupp1 D := by
  first | exact @GlobalTheory.LocMod.SuppFirst.gsupp1 | exact GlobalTheory.LocMod.SuppFirst.gsupp1 | (intros; apply GlobalTheory.LocMod.SuppFirst.gsupp1 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedSupportAndValueAtFixedLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSawLaws

open GlobalTheory.LocMod

theorem gsupp2_all (D : D7) : GlobalTheory.LocMod.GSupp2 D := by
  have hFL : FlatLaw D := GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D
  have hFLs : GlobalTheory.FinPl.FlatLaws D := GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D
  have hOm : OmLoc D := GlobalTheory.T.weilDatum_localModel_formula D
  have hBF : FlatBF D := GlobalTheory.T.flatMap_besselToFourierJacobi_localModel D hFL hFLs hOm
  have hFB : FlatFB D := GlobalTheory.T.flatMap_fourierJacobiToBessel_localModel D hFL hFLs hOm
  have hC : ContrLoc D := GlobalTheory.T.lineContraction_splitPlace_localModel D GlobalTheory.LocFlat.contrFactor
  have hS : GlobalTheory.LocFlat.SymCollapse := GlobalTheory.LocFlat.symCollapse_of_allPositions GlobalTheory.SymChain.allPositions_holds
  intro k _ _ _ _ p s κ S t _ _ ψ hψ j c H σ B J B' F s₁ s₂ l vL hc T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ hΦ₁ hΦ₂ h hh hne
  exact GlobalTheory.T.support_levelPlace_symmetricChain_secondHalf D hOm hBF hFB hC hS k p s κ S t ψ s₁.weil.std hψ j c H σ B J B' F s₁ s₂ l vL hc T₁ T₂ hT₁ hT₂ Φ₁ Φ₂ hΦ₁ hΦ₂ h hh hne

theorem gsupp1_all (D : D7) : GlobalTheory.LocMod.GSupp1 D :=
  GlobalTheory.T.flat_map_support_first_half_at_level_place D (GlobalTheory.T.weilDatum_localModel_formula D)
    (GlobalTheory.T.flatMap_besselToFourierJacobi_localModel D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) (GlobalTheory.T.flatMapsSatisfyFlatLaws_finitePlaces D) (GlobalTheory.T.weilDatum_localModel_formula D))
    (GlobalTheory.LocFlat.symCollapse_of_allPositions GlobalTheory.SymChain.allPositions_holds)

theorem gLaws : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → ∃ a : ℕ → ℂ, (∀ j, a j ≠ 0) ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → (∀ i, (G i).Chars t) → GSupp (t := t) (v.withCG a) ∧ GValue (t := t) (v.withCG a) := by
  intro D c v n G hc hv hG
  obtain ⟨a, ha, hval⟩ := GlobalTheory.T.seeSaw_unfoldedValue_commonConstants_fixedLevel D c v n G hc hv hG
  refine ⟨a, ha, fun t ht hW hch => ⟨?_, hval t ht hW⟩⟩
  have hs : GSupp (t := t) v :=
    GlobalTheory.T.seeSaw_unfoldedSupport_fixedLevelPlaces D c v n G hc hv hG (gsupp1_all D) (gsupp2_all D) (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) t ht hch
  exact hs

end GlobalTheory.SeeSawLaws
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawUnfoldedSupportAndValueAtFixedLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawUnfolded_support_and_value_at_fixed_level : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), c.Is → v.Is → GPin G → ∃ a : ℕ → ℂ, (∀ j, a j ≠ 0) ∧ ∀ t : Tup c, t.Is → WeilOK (t := t) v → (∀ i, (G i).Chars t) → GSupp (t := t) (v.withCG a) ∧ GValue (t := t) (v.withCG a) := by
  first | exact @GlobalTheory.SeeSawLaws.gLaws | exact GlobalTheory.SeeSawLaws.gLaws | (intros; apply GlobalTheory.SeeSawLaws.gLaws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLatticeFramePinsFiniteIntegralLaws
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSawAll

variable {D : D7}

theorem real_pos_of_open_compact {X : Type} [TopologicalSpace X] [MeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts μ] {S : Set X} (ho : IsOpen S) (hc : IsCompact S) (hn : S.Nonempty) : 0 < μ.real S :=
  ENNReal.toReal_pos (ho.measure_ne_zero μ hn) hc.measure_lt_top.ne

theorem level_open_compact (V : HSp D) (L : Lat V) (hL : IsSelfDualC V L) (gP : Finset (Pl D)) (JG : Subgroup (GA D V))
    (hJ : JG ≤ grpAt V (· ∈ gP)) (hJc : IsCompact (JG : Set (GA D V)))
    (hJo : IsOpen (((JG.subgroupOf (grpAt V (· ∈ gP))) : Subgroup _) : Set (grpAt V (· ∈ gP)))) :
    IsOpen {g : GfC V | ∃ κ, InK V L (· ∉ gP) κ ∧ ∃ k ∈ JG, g.1 = κ * k} ∧
      IsCompact {g : GfC V | ∃ κ, InK V L (· ∉ gP) κ ∧ ∃ k ∈ JG, g.1 = κ * k} ∧
      (1 : GfC V) ∈ {g : GfC V | ∃ κ, InK V L (· ∉ gP) κ ∧ ∃ k ∈ JG, g.1 = κ * k} := by
  obtain ⟨-, -, -, -, hcomm, ⟨e, he⟩, -, -, hK, -⟩ := GlobalTheory.FinPl.SetCut.grp_split D V gP
  obtain ⟨⟨K₁, hK₁, hK₁c, hK₁o⟩, -⟩ := hK L hL (· ∉ gP)
  have hS : {g : GfC V | ∃ κ, InK V L (· ∉ gP) κ ∧ ∃ k ∈ JG, g.1 = κ * k} =
      e '' ((((JG.subgroupOf (grpAt V (· ∈ gP))) : Subgroup _) : Set (grpAt V (· ∈ gP))) ×ˢ
        (((K₁.subgroupOf (grpAt V (· ∉ gP))) : Subgroup _) : Set (grpAt V (· ∉ gP)))) := by
    ext g
    constructor
    · rintro ⟨κ, hκ, k, hk, hg⟩
      have hκ' : κ ∈ grpAt V (· ∉ gP) := hκ.1
      refine ⟨(⟨k, hJ hk⟩, ⟨κ, hκ'⟩), ⟨Subgroup.mem_subgroupOf.2 hk, Subgroup.mem_subgroupOf.2 ((hK₁ κ).2 hκ)⟩, ?_⟩
      apply Subtype.ext
      rw [he, hg, hcomm k (hJ hk) κ hκ']
    · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
      refine ⟨p.2.1, (hK₁ _).1 (Subgroup.mem_subgroupOf.1 hp2), p.1.1, Subgroup.mem_subgroupOf.1 hp1, ?_⟩
      rw [he, hcomm p.1.1 p.1.2 p.2.1 p.2.2]
  have hAc : IsCompact (((JG.subgroupOf (grpAt V (· ∈ gP))) : Subgroup _) : Set (grpAt V (· ∈ gP))) := by
    have h1 : ((JG.subgroupOf (grpAt V (· ∈ gP)) : Subgroup _) : Set (grpAt V (· ∈ gP))) =
        Subtype.val ⁻¹' (JG : Set (GA D V)) := rfl
    rw [h1, Topology.IsInducing.subtypeVal.isCompact_preimage_iff]
    · exact hJc
    · intro x hx; exact ⟨⟨x, hJ hx⟩, rfl⟩
  have hBc : IsCompact (((K₁.subgroupOf (grpAt V (· ∉ gP))) : Subgroup _) : Set (grpAt V (· ∉ gP))) := by
    have h1 : ((K₁.subgroupOf (grpAt V (· ∉ gP)) : Subgroup _) : Set (grpAt V (· ∉ gP))) =
        Subtype.val ⁻¹' (K₁ : Set (GA D V)) := rfl
    rw [h1, Topology.IsInducing.subtypeVal.isCompact_preimage_iff]
    · exact hK₁c
    · intro x hx; exact ⟨⟨x, ((hK₁ x).1 hx).1⟩, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hS]; exact e.isOpenMap _ (hJo.prod hK₁o)
  · rw [hS]; exact (hAc.prod hBc).image e.continuous
  · exact ⟨1, (hK₁ 1).1 (one_mem _), 1, one_mem _, by simp⟩

variable {c : Comm D}

theorem vr_ne_zero (v : VCom c) (hv : v.Is) (j : ℕ) (hj : j < D.R.m) (hμ : (c.μf j).IsHaarMeasure)
    (R : Subgroup (GA D (c.V j))) (hR : IsClosed (R : Set (GA D (c.V j))))
    (ρ : Measure (R.subgroupOf (GfC (c.V j)))) (hρ : ρ.IsHaarMeasure) : v.vr j R ρ ≠ 0 := by
  obtain ⟨hJle, hJc, hJo⟩ := hv.JG j hj
  obtain ⟨hSo, hSc, hS1⟩ := level_open_compact (c.V j) (v.N j) (hv.sd j hj) v.gP (v.JG j) hJle hJc hJo
  have h1 : 0 < (c.μf j).real {g | g.1 ∈ v.K j} := by
    exact real_pos_of_open_compact (c.μf j) hSo hSc ⟨1, hS1⟩
  have hT : IsClosed (((R.subgroupOf (GfC (c.V j))) : Subgroup _) : Set (GfC (c.V j))) :=
    hR.preimage continuous_subtype_val
  have h2 : 0 < ρ.real {g | g.1.1 ∈ v.K j} := by
    exact real_pos_of_open_compact ρ (hSo.preimage continuous_subtype_val)
      (hT.isClosedEmbedding_subtypeVal.isCompact_preimage hSc) ⟨1, hS1⟩
  unfold VCom.vr
  exact_mod_cast (div_pos h1 h2).ne'

theorem kap_ne_zero (v : VCom c) (hc : c.Is) (hv : v.Is) : ∀ j σ h, v.kap j σ h ≠ 0 := by
  intro j σ h
  unfold VCom.kap
  refine mul_ne_zero ?_ ?_
  · exact vr_ne_zero v hv (j + 1) (by omega) (hc.μf _) _ (GlobalTheory.jacGrp_isClosed _ _ _ _ _) _ (hc.ρJ _ _ _)
  · exact vr_ne_zero v hv (j + 1 + 1) (by omega) (hc.μf _) _ (GlobalTheory.BesClosed.besGrp_isClosed _ _ _ _ _ _ _ _) _ (hc.ρB _ _ _)

theorem is_withCG (v : VCom c) (a : ℕ → ℂ) (h : v.Is) : (v.withCG a).Is :=
  ⟨h.disj, h.sd, h.sdT, h.b, h.bT, h.Ψ, h.ΨT, h.JG, h.atG, h.atT, h.ram⟩

theorem weilOK_of_tau {t : Tup c} (v v' : VCom c) (hτ : v'.τ = v.τ) (h : WeilOK (t := t) v) : WeilOK (t := t) v' := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, by rw [hτ]; exact h3⟩

theorem unrOn_mono {t : Tup c} {P P' : Pl D → Prop} (h : t.UnrOn P) (hPP : ∀ x, P' x → P x) : t.UnrOn P' := by
  refine ⟨fun j ρ hh x hx => h.bf j ρ hh x (hPP x hx),
    fun j σ hh x hx => h.fb j σ hh x (hPP x hx), ?_⟩
  intro j hh
  obtain ⟨χS, χT, h1, h2⟩ := h.top j hh
  exact ⟨χS, χT, h1, fun x hx => h2 x (hPP x hx)⟩

end GlobalTheory.SeeSawAll

namespace GlobalTheory.SeeSaw

theorem pins_finiteIntegrals : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (n : ℕ) (G : Fin n → GLoc v), c.Is → c.VolLast → v.Is → ShapeOff v o → GPin G → ∃ (ε : ℕ → ι → 𝓀[k]ˣ) (op : ∀ j, BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ℕ → ι → ℝ) (e : ℕ → ι → ℤ) (a : ℕ → ℂ), (∀ j i, 0 < r j i) ∧ (∀ j, a j ≠ 0) ∧ (∀ j σ h, v.kap j σ h ≠ 0) ∧ ((v.withT (o.S ε) op).withCG a).Is ∧ ∀ (𝒯 : Type) (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)), (∀ s, (t s).Is ∧ VForm ((v.withT (o.S ε) op).withCG a) (w s) ∧ WeilOK (t := t s) v ∧ TopSph (t := t s) v ∧ (t s).UnrOn (offP v (w s)) ∧ (t s).UnrK (· ∈ v.tP) ∧ (∀ i, (G i).Chars (t s)) ∧ QLaw v (w s) ∧ QLast v (w s) ∧ QFin v (w s) ∧ (∀ j ρ h, (w s).cT j = o.mono (r j) (e j) ((t s).sBF j ρ h).χW) ∧ CVEq ((v.withT (o.S ε) op).withCG a) (w s)) → (∀ s, (t s).LocFin) ∧ ValX t ∧ ValLastX t := by
  intro D c v k _ _ _ _ ι o n G hc hvl hv hsh hG
  obtain ⟨ε, op, r, e, hr, hvT, hT⟩ := GlobalTheory.T.seesaw_levelPrime_law_all_tuples D c v k ι o hc hv hsh
  obtain ⟨a, ha, hGa⟩ := GlobalTheory.T.seeSawUnfolded_support_and_value_at_fixed_level D c v n G hc hv hG
  have hv' : ((v.withT (o.S ε) op).withCG a).Is := GlobalTheory.SeeSawAll.is_withCG _ a hvT
  refine ⟨ε, op, r, e, a, hr, ha, GlobalTheory.SeeSawAll.kap_ne_zero v hc hv, hv', ?_⟩
  intro 𝒯 t w hw
  refine GlobalTheory.T.seesaw_place_laws_give_finite_integral_laws D c ((v.withT (o.S ε) op).withCG a) 𝒯 t w hc hvl hv' (fun s => (hw s).1) (fun s => ?_)
  obtain ⟨hts, hform, hweil, hsph, hunr, hunrK, hch, hql, hqlast, hqfin, hcT, hcv⟩ := hw s
  have hdisjT : Disjoint (w s).Q v.tP := hform.disjT
  have hoff : OffLaw v (w s) := GlobalTheory.T.seesaw_support_off_level_of_lattice_shape D c v k ι o hc hv hsh (t s) (w s) hts hdisjT hunr
  have hvac : VacLaw (t := t s) v := GlobalTheory.T.seeSawUnfoldedVacuaOfShape_proof D c v k ι o hc hv hsh (t s)
  have hunrT : (t s).UnrOn (· ∈ v.tP) := GlobalTheory.SeeSawAll.unrOn_mono hunr fun x hx =>
    ⟨fun hg => Finset.disjoint_left.mp hv.disj hg hx, fun hq => Finset.disjoint_left.mp hdisjT hq hx⟩
  have htl : TLaw (v.withT (o.S ε) op) (w s) := hT (t s) (w s) hts hweil hunrT hunrK hcT
  obtain ⟨hgs, hgv⟩ := hGa (t s) hts hweil hch
  exact ⟨hform, GlobalTheory.SeeSawAll.weilOK_of_tau v _ rfl hweil, hoff, hgs, hgv, hvac, htl, hql, hqlast, hqfin, hcv, hsph⟩

end GlobalTheory.SeeSaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawLatticeFramePinsFiniteIntegralLawsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_latticeFramePins_finiteIntegralLaws : ∀ (D : D7) (c : Comm D) (v : VCom c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (n : ℕ) (G : Fin n → GLoc v), c.Is → c.VolLast → v.Is → ShapeOff v o → GPin G → ∃ (ε : ℕ → ι → 𝓀[k]ˣ) (op : ∀ j, BiOp (c.X j) (c.X (j + 1)) (c.X (j + 1 + 1))) (r : ℕ → ι → ℝ) (e : ℕ → ι → ℤ) (a : ℕ → ℂ), (∀ j i, 0 < r j i) ∧ (∀ j, a j ≠ 0) ∧ (∀ j σ h, v.kap j σ h ≠ 0) ∧ ((v.withT (o.S ε) op).withCG a).Is ∧ ∀ (𝒯 : Type) (t : 𝒯 → Tup c) (w : ∀ s, VTup (t s)), (∀ s, (t s).Is ∧ VForm ((v.withT (o.S ε) op).withCG a) (w s) ∧ WeilOK (t := t s) v ∧ TopSph (t := t s) v ∧ (t s).UnrOn (offP v (w s)) ∧ (t s).UnrK (· ∈ v.tP) ∧ (∀ i, (G i).Chars (t s)) ∧ QLaw v (w s) ∧ QLast v (w s) ∧ QFin v (w s) ∧ (∀ j ρ h, (w s).cT j = o.mono (r j) (e j) ((t s).sBF j ρ h).χW) ∧ CVEq ((v.withT (o.S ε) op).withCG a) (w s)) → (∀ s, (t s).LocFin) ∧ ValX t ∧ ValLastX t := by
  first | exact @GlobalTheory.SeeSaw.pins_finiteIntegrals | exact GlobalTheory.SeeSaw.pins_finiteIntegrals | (intros; apply GlobalTheory.SeeSaw.pins_finiteIntegrals <;> assumption)
end
