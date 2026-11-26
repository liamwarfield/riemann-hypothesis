module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushSupp

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DetNZHolds
noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.S Matrix

def wF {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) : Fin (D.R.rS + 1 + D.R.rS) → (VS D).V :=
  Fin.append (Fin.snoc X.eX (X.zu u')) X.fY

theorem tupH_eq {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) :
    tupH (frameOf X u') = fun i => X.crd (wF X u' i) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [tupH, F0, wF, Fin.append_left]
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [Fin.snoc_last]; rfl
    · simp only [Fin.snoc_castSucc]; rfl
  · simp only [tupH, wF, Fin.append_right]; rfl

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gram_eq {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (i j : Fin (D.R.rS + 1 + D.R.rS)) :
    gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j = X.ιE.symm ((VS D).hT (wF X u' i) (wF X u' j)) := by
  rw [tupH_eq, ← Formalism.L2.SG.PoincareInHH.Cut.hform_crd X, RingEquiv.symm_apply_apply]
  rfl

theorem hT_fe {D : D7} (X : HidaSetting D) (a b : Fin D.R.rS) :
    (VS D).hT (X.fY a) (X.eX b) = if b = a then 1 else 0 := by
  have h := (VS D).herm.eq (X.eX b) (X.fY a)
  rw [X.ef] at h
  rw [← h]
  split_ifs <;> simp

theorem hT_ze {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (a : Fin D.R.rS) :
    (VS D).hT (X.zu u') (X.eX a) = 0 := by
  have h := (VS D).herm.eq (X.eX a) (X.zu u')
  rw [(X.zu_orth u' a).1] at h
  rw [← h]; simp

theorem hT_zf {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (a : Fin D.R.rS) :
    (VS D).hT (X.zu u') (X.fY a) = 0 := by
  have h := (VS D).herm.eq (X.fY a) (X.zu u')
  rw [(X.zu_orth u' a).2] at h
  rw [← h]; simp

theorem row_eq {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (v : Fin (D.R.rS + 1 + D.R.rS) → X.B.I.E)
    (i : Fin (D.R.rS + 1 + D.R.rS)) :
    X.ιE ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) *ᵥ v) i) =
      ∑ j, (VS D).hT (wF X u' i) (wF X u' j) * X.ιE (v j) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, gram_eq, map_sum, map_mul, RingEquiv.apply_symm_apply]

theorem detNZ_holds : DetNZ := by
  intro D X u' ψ hT μinf νinf fibInf _
  rw [Ne, ← Matrix.exists_mulVec_eq_zero_iff]
  rintro ⟨v, hv0, hv⟩
  apply hv0
  have row : ∀ i, ∑ j, (VS D).hT (wF X u' i) (wF X u' j) * X.ιE (v j) = 0 := by
    intro i
    rw [← row_eq, hv]
    simp
  have hTne : ((((D.mem u').A.T : ℕ) : D.host.E)) ≠ 0 := by
    exact_mod_cast (D.mem u').A.T_prime.ne_zero
  have he : ∀ a, v (Fin.castAdd D.R.rS (Fin.castSucc a)) = 0 := by
    intro a
    have h := row (Fin.natAdd (D.R.rS + 1) a)
    rw [Fin.sum_univ_add, Fin.sum_univ_castSucc] at h
    simp [wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, hT_fe, X.ff,
      (X.zu_orth u' _).2] at h
    exact h
  have hf : ∀ a, v (Fin.natAdd (D.R.rS + 1) a) = 0 := by
    intro a
    have h := row (Fin.castAdd D.R.rS (Fin.castSucc a))
    rw [Fin.sum_univ_add, Fin.sum_univ_castSucc] at h
    simp [wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, X.ee, X.ef,
      (X.zu_orth u' _).1] at h
    exact h
  have hz : v (Fin.castAdd D.R.rS (Fin.last D.R.rS)) = 0 := by
    have h := row (Fin.castAdd D.R.rS (Fin.last D.R.rS))
    rw [Fin.sum_univ_add, Fin.sum_univ_castSucc] at h
    simp [wF, Fin.append_left, Fin.append_right, Fin.snoc_castSucc, Fin.snoc_last, hT_ze, hT_zf,
      X.zu_norm, hTne] at h
    exact h
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · refine Fin.lastCases ?_ (fun k => ?_) j
    · exact hz
    · exact he k
  · exact hf j

end PI.AprimeInfW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.JacCut
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Filter Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub
  Formalism.L2.SG.TypedSets Formalism.L2.SG.Pf.NcReal
open scoped TensorProduct

theorem rmulT_rmulT {D : D7} (X : HidaSetting D) (a b : MfI X) (Y : TupI X) :
    rmulT X b (rmulT X a Y) = rmulT X (a * b) Y := by
  funext d i
  simp only [rmulT, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem smul_rmulT {D : D7} (X : HidaSetting D) (g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) (a : MfI X)
    (Y : TupI X) : g • rmulT X a Y = rmulT X a (g • Y) := by
  funext b i
  change Matrix.mulVec (HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g).1 (rmulT X a Y b) i =
    ∑ c, a c b * Matrix.mulVec (HA.mat (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J g).1 (Y c) i
  simp only [rmulT, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

def BoxT {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (a : HmI X → MfI X)
    (V : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) (W : Set (HmI X)) : Set (TupI X) :=
  {y | ∃ T ∈ W, ∃ g ∈ V, y = g • rmulT X (a T) (Y0 X u')}

def TubeG {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (V : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) :
    Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
  {g | ∃ g' ∈ V, g • Y0 X u' = g' • Y0 X u'}

def ChartPred : Type 1 := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word),
    (∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j) →
    Measure (TupI X) → Measure (HmI X) → (HmI X → MfI X) → Prop

def JacOneFor (Pr : ChartPred) : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a → Pr X u' hT μinf νinf a →
    ∀ J : HmI X → ℝ, J (TI X u' hT) = 1 → ContinuousAt J (TI X u' hT) →
    ∀ Ω₂ ⊆ Ω, Ω₂ ∈ 𝓝 (TI X u' hT) → ∀ c₀ : ENNReal,
      PolId X u' μinf νinf a Ω₂ (fun T => c₀ * ENNReal.ofReal (J T)) → c₀ = (ENNReal.ofReal (KVal X u'))⁻¹

def LocRatioFor (Pr : ChartPred) : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a → Pr X u' hT μinf νinf a → ∀ Ω₂ ⊆ Ω, Ω₂ ∈ 𝓝 (TI X u' hT) →
    ∃ (V : ℕ → Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) (W : ℕ → Set (HmI X)),
      (∀ n, MeasurableSet (W n) ∧ W n ⊆ Ω₂ ∧ 0 < νinf (W n) ∧ νinf (W n) < ⊤ ∧ (∀ T ∈ W n, IsUnit (a T)) ∧
        MeasurableSet (BoxT X u' a (V n) (W n)) ∧ BoxT X u' a (V n) (W n) ⊆ IndI X ∧
        μinf (BoxT X u' a (V n) (W n)) < ⊤ ∧
        MeasurableSet (TubeG X u' (V n)) ∧ 0 < X.measG.μGinf (TubeG X u' (V n)) ∧
        X.measG.μGinf (TubeG X u' (V n)) < ⊤) ∧
      (∀ U ∈ 𝓝 (TI X u' hT), ∀ᶠ n in atTop, W n ⊆ U) ∧
      Tendsto (fun n => (μinf (BoxT X u' a (V n) (W n))).toReal /
        ((νinf (W n)).toReal * (X.measG.μGinf (TubeG X u' (V n))).toReal)) atTop (𝓝 (KVal X u')⁻¹)

theorem pre_box {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)
    (hT : ∀ i j, X.B.I.cm.sig (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) =
      gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) i j)
    {Ω : Set (HmI X)} {a : HmI X → MfI X} (hC : IsChart X u' hT Ω a)
    (V : Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) {W : Set (HmI X)} (hW : W ⊆ Ω)
    (hU : ∀ T ∈ W, IsUnit (a T)) (T : HmI X) (hTW : T ∈ W) :
    {g : HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J | g • rmulT X (a T) (Y0 X u') ∈ BoxT X u' a V W} =
      TubeG X u' V := by
  ext g
  constructor
  · rintro ⟨T₁, hT₁, g', hg', e⟩
    have hG : T = T₁ := by
      apply Subtype.ext
      have h2 := congrArg (gramR (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J) e
      rw [gramR_smul, gramR_smul, hC.2.2.2 T (hW hTW), hC.2.2.2 T₁ (hW hT₁)] at h2
      exact h2
    subst hG
    refine ⟨g', hg', ?_⟩
    obtain ⟨w, hw⟩ := hU T hTW
    rw [smul_rmulT, smul_rmulT] at e
    have h3 := congrArg (rmulT X (↑w⁻¹ : MfI X)) e
    rwa [rmulT_rmulT, rmulT_rmulT, ← hw, Units.mul_inv, rmulT_one, rmulT_one] at h3
  · rintro ⟨g', hg', e⟩
    refine ⟨T, hTW, g', hg', ?_⟩
    rw [smul_rmulT, smul_rmulT, e]

def SplitAsymFor (Pr : ChartPred) : Prop := ∀ {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ) hT μinf νinf fibInf,
    PushHyp X u' ψ hT μinf νinf fibInf → ∀ Ω a, IsChart X u' hT Ω a → Pr X u' hT μinf νinf a → ∀ Ω₂ ⊆ Ω, Ω₂ ∈ 𝓝 (TI X u' hT) →
    ∃ (V : ℕ → Set (HA (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J)) (W : ℕ → Set (HmI X)) (p : ℕ → ℝ),
      (∀ n, MeasurableSet (W n) ∧ W n ⊆ Ω₂ ∧ 0 < νinf (W n) ∧ νinf (W n) < ⊤ ∧ (∀ T ∈ W n, IsUnit (a T)) ∧
        MeasurableSet (BoxT X u' a (V n) (W n)) ∧ BoxT X u' a (V n) (W n) ⊆ IndI X ∧
        μinf (BoxT X u' a (V n) (W n)) < ⊤ ∧
        MeasurableSet (TubeG X u' (V n)) ∧ 0 < X.measG.μGinf (TubeG X u' (V n)) ∧
        X.measG.μGinf (TubeG X u' (V n)) < ⊤ ∧ 0 < p n) ∧
      (∀ U ∈ 𝓝 (TI X u' hT), ∀ᶠ n in atTop, W n ⊆ U) ∧
      Tendsto (fun n => (X.measG.μGinf (TubeG X u' (V n))).toReal / p n) atTop
        (𝓝 (Formalism.MainNotions.S.AutInst.gaugeU X.B.I * Formalism.MainNotions.S.UnitaryVolumeMass.volU D.R.k ^ Fintype.card (NumberField.InfinitePlace X.B.I.F))) ∧
      Tendsto (fun n => (μinf (BoxT X u' a (V n) (W n))).toReal / (p n * (νinf (W n)).toReal)) atTop
        (𝓝 (Tw u' ^ (D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F))))

theorem locRatioFor_of {Pr : ChartPred} (hK : KPos) (hS : SplitAsymFor Pr) : LocRatioFor Pr := by
  intro D X u' ψ hT μinf νinf fibInf hP Ω a hC hPr Ω₂ hΩ₂ hΩ₂n
  obtain ⟨V, W, p, hVW, hsh, hG, hTup⟩ := hS X u' ψ hT μinf νinf fibInf hP Ω a hC hPr Ω₂ hΩ₂ hΩ₂n
  have hK0 : 0 < KVal X u' := hK X u' ψ hT μinf νinf fibInf hP
  refine ⟨V, W, fun n => ?_, hsh, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -⟩ := hVW n
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  set g0 : ℝ := Formalism.MainNotions.S.AutInst.gaugeU X.B.I * Formalism.MainNotions.S.UnitaryVolumeMass.volU D.R.k ^ Fintype.card (NumberField.InfinitePlace X.B.I.F)
    with hg0
  set t0 : ℝ := Tw u' ^ (D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F)) with ht0
  have hKe : KVal X u' = g0 * t0⁻¹ := by
    simp only [KVal, hg0, ht0, zpow_neg, zpow_natCast]
  have hg0ne : g0 ≠ 0 := by
    intro h; rw [hKe, h, zero_mul] at hK0; exact lt_irrefl _ hK0
  have ht0ne : t0 ≠ 0 := by
    intro h; rw [hKe, h, inv_zero, mul_zero] at hK0; exact lt_irrefl _ hK0
  have hlim := hTup.div hG hg0ne
  have hval : t0 / g0 = (KVal X u')⁻¹ := by
    rw [hKe, mul_inv, inv_inv, div_eq_mul_inv, mul_comm]
  rw [hval] at hlim
  refine hlim.congr fun n => ?_
  obtain ⟨-, -, hB0, hBt, -, -, -, -, -, hM0, hMt, hp⟩ := hVW n
  have hBr : 0 < (νinf (W n)).toReal := ENNReal.toReal_pos hB0.ne' hBt.ne
  have hMr : 0 < (X.measG.μGinf (TubeG X u' (V n))).toReal := ENNReal.toReal_pos hM0.ne' hMt.ne
  simp only [Pi.div_apply]
  field_simp

end PI.AprimeInfW
end
end
