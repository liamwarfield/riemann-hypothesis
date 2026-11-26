module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpec

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSOpR
open MeasureTheory
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section comp

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def dcomp (T0 : B.DTerm k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) : B.DiffOp k r Wp Wq :=
  Θ.map fun T =>
    { coef := fun x => (T0.coef x).comp (T.coef x)
      coefAdj := fun x => (T.coefAdj x).comp (T0.coefAdj x)
      word := T.word
      word_lie := T.word_lie
      adj_id := fun x A B => by
        simp only [ContinuousLinearMap.comp_apply]
        rw [T0.adj_id, T.adj_id] }

theorem opApply_dcomp (T0 : B.DTerm k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (g : B.Mat k r) : B.opApply (dcomp T0 Θ) F g = T0.coef g (B.opApply Θ F g) := by
  unfold B.opApply dcomp
  rw [map_list_sum, List.map_map, List.map_map]
  rfl

def Good0 (D : B.RealPlaceData k r Wp Wq) (T0 : B.DTerm k r Wp Wq) : Prop :=
  T0.word = [] ∧ B.CkOn ⊤ (B.GPos D) T0.coef ∧ B.CkOn ⊤ (B.GPos D) T0.coefAdj ∧
    (∀ p, D.inSS p → ∀ g ∈ B.GPos D, ∀ A : Wq →L[ℂ] Wp,
      T0.coef g ((D.π (Matrix.of p.1.1)).comp (A.comp (D.π' (Matrix.of p.2.1)⁻¹))) =
        (D.π (Matrix.of p.1.1)).comp ((T0.coef (B.sgs p g) A).comp (D.π' (Matrix.of p.2.1)⁻¹))) ∧
    ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ C d : ℝ, 0 ≤ d ∧ ∀ u v : List (B.Mat k r), (∀ X ∈ u, B.unitLie k r X) →
      (∀ X ∈ v, B.unitLie k r X) → u.length + v.length ≤ m → ∀ g ∈ B.GV k r, ε ≤ Gf k r D.z D.z' g →
        ‖B.dLR u v T0.coef g‖ ≤ C * B.gN g ^ d ∧ ‖B.dLR u v T0.coefAdj g‖ ≤ C * B.gN g ^ d

end comp

def RDSOpRGrp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r : ℕ) (D : B.RealPlaceData k r Wp Wq)
    (Y σ : ℂ), ∃ Θ : B.DiffOp k r Wp Wq, OpProp1 D Θ ∧
      ∀ J : B.Mat k r → (Wq →L[ℂ] Wp), J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (JF.Om k r D.z D.z') →
        ∀ x ∈ DomR k r D.z D.z', resG k r (Fin.last r) (B.opApply Θ J) x.1 x.2 =
          σ • CutMP.rhGrp k r D.z D.z' Y (resG k r (Fin.last r) J) x.1 x.2

def RDSOpRvGrp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r : ℕ) (D : B.RealPlaceData k r Wp Wq)
    (Y σ : ℂ), ∃ Θ : B.DiffOp k r Wp Wq, OpProp1 D Θ ∧
      ∀ J : B.Mat k r → (Wq →L[ℂ] Wp), J ∈ Q.FFl k r D.z D.z' D.π D.π' 0 (JF.Om k r D.z D.z') →
        ∀ x ∈ DomR k r D.z D.z', resG k r (Fin.last r) (B.opApply Θ J) x.1 x.2 =
          σ • CutMP.rhvGrp k r D.z D.z' Y (resG k r (Fin.last r) J) x.1 x.2

def RDSOpX : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq), IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' →
    D.π = π → D.π' = π' → 0 < P.r →
    ∀ Y : ℂ, Y ∈ st.inv → ∃ T0 : B.DTerm P.k P.r Wp Wq, Good0 D T0 ∧
      ∀ (Ψ : RadSp P.k P.r z z' π π'), ∀ x ∈ DomR P.k P.r z z',
        (((GiR L * st.xi Y).1 Ψ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
          T0.coef (wCell P.k P.r (Fin.last P.r) x.1 * x.2) ((Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)

def RDSRhR : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → 0 < P.r →
    ∀ Y : ℂ, star Y = Y → ∃ σ : ℂ, ∀ J : B.Mat P.k P.r → (Wq →L[ℂ] Wp), J ∈ Q.FFl P.k P.r z z' π π' 0 (JF.Om P.k P.r z z') →
      ∀ Φ : RadSp P.k P.r z z' π π',
        (∀ x ∈ DomR P.k P.r z z', (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = resG P.k P.r (Fin.last P.r) J x.1 x.2) →
        ∀ x ∈ DomR P.k P.r z z',
          (((RhR L st Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
            σ • CutMP.rhGrp P.k P.r z z' Y (resG P.k P.r (Fin.last P.r) J) x.1 x.2

def RDSRhvR : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → 0 < P.r →
    ∀ Y : ℂ, star Y = Y → ∃ σ : ℂ, ∀ J : B.Mat P.k P.r → (Wq →L[ℂ] Wp), J ∈ Q.FFl P.k P.r z z' π π' 0 (JF.Om P.k P.r z z') →
      ∀ Φ : RadSp P.k P.r z z' π π',
        (∀ x ∈ DomR P.k P.r z z', (Φ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = resG P.k P.r (Fin.last P.r) J x.1 x.2) →
        ∀ x ∈ DomR P.k P.r z z',
          (((RhvR L st Y).1 Φ : RadSp P.k P.r z z' π π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 =
            σ • CutMP.rhvGrp P.k P.r z z' Y (resG P.k P.r (Fin.last P.r) J) x.1 x.2

def RDSComp0 : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r : ℕ) (D : B.RealPlaceData k r Wp Wq)
    (T0 : B.DTerm k r Wp Wq) (Θ : B.DiffOp k r Wp Wq), Good0 D T0 → OpProp1 D Θ → OpProp1 D (dcomp T0 Θ)

theorem rDSOpR_of_parts (hG : RDSOpRGrp) (hX : RDSOpX) (hR : RDSRhR) (hC : RDSComp0) : RDSOpR := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Y hY _ hY0 _
  obtain ⟨σ, hσ⟩ := hR Wp Wq P z z' π π' X μ L st l0 hD hl1 hl2 hr Y hY
  obtain ⟨T0, hT0, hT0e⟩ := hX Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Y hY0
  subst hz hz' hπ hπ'
  obtain ⟨Θ, hΘ, hΘe⟩ := hG Wp Wq P.k P.r D Y σ
  refine ⟨dcomp T0 Θ, hC Wp Wq P.k P.r D T0 Θ hT0 hΘ, ?_⟩
  intro J hJ Φ hΦ x hx
  have e1 : (((GiR L * st.xi Y * RhR L st Y).1 Φ : RadSp P.k P.r D.z D.z' D.π D.π') : Fn P.k P.r (Wq →L[ℂ] Wp))
      x.1 x.2 = (((GiR L * st.xi Y).1 ((RhR L st Y).1 Φ) : RadSp P.k P.r D.z D.z' D.π D.π') :
        Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 := rfl
  rw [e1, hT0e _ x hx, hσ J hJ Φ hΦ x hx, ← hΘe J hJ x hx]
  simp only [resG, opApply_dcomp, map_smul]

theorem rDSOpRv_of_parts (hG : RDSOpRvGrp) (hX : RDSOpX) (hR : RDSRhvR) (hC : RDSComp0) : RDSOpRv := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr Y hY _ _ hY1
  have hY' : star (Y + 1) = Y + 1 := by rw [star_add, hY, star_one]
  obtain ⟨σ, hσ⟩ := hR Wp Wq P z z' π π' X μ L st l0 hD hl1 hl2 hr (Y + 1) hY'
  obtain ⟨T0, hT0, hT0e⟩ := hX Wp Wq P z z' π π' X μ L st l0 D hD hl1 hl2 hz hz' hπ hπ' hr (Y + 1) hY1
  subst hz hz' hπ hπ'
  obtain ⟨Θ, hΘ, hΘe⟩ := hG Wp Wq P.k P.r D (Y + 1) σ
  refine ⟨dcomp T0 Θ, hC Wp Wq P.k P.r D T0 Θ hT0 hΘ, ?_⟩
  intro J hJ Φ hΦ x hx
  have e1 : (((GiR L * st.xi (Y + 1) * RhvR L st (Y + 1)).1 Φ : RadSp P.k P.r D.z D.z' D.π D.π') :
      Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = (((GiR L * st.xi (Y + 1)).1 ((RhvR L st (Y + 1)).1 Φ) :
        RadSp P.k P.r D.z D.z' D.π D.π') : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 := rfl
  rw [e1, hT0e _ x hx, hσ J hJ Φ hΦ x hx, ← hΘe J hJ x hx]
  simp only [resG, opApply_dcomp, map_smul]

end Formalism.FourierDecayAlt.P.CutSE
end
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDSIpInt
open MeasureTheory Filter Topology

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section IpInt

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] [FiniteDimensional ℂ Wp]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

instance rds_dxc_sFinite (r : ℕ) : SFinite (dxc r) := by unfold dxc; infer_instance

theorem rds_continuous_hsVec : Continuous (fun A : Wq →L[ℂ] Wp => B.hsVec A) := by
  unfold B.hsVec
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i => continuous_id.clm_apply continuous_const)

theorem rds_hsVec_add (A A' : Wq →L[ℂ] Wp) : B.hsVec (A + A') = B.hsVec A + B.hsVec A' := by
  unfold B.hsVec
  rw [← WithLp.toLp_add]
  rfl

theorem rds_hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  unfold B.hsVec
  rw [← WithLp.toLp_smul]
  rfl

theorem rds_hsVec_zero : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  simpa using rds_hsVec_smul (Wp := Wp) 0 (0 : Wq →L[ℂ] Wp)

theorem rds_dxc_compact {C : Set (Fin r → ℂ)} (hC : IsCompact C) (hCO : C ⊆ OmX r) : dxc r C < ⊤ := by
  have hcont : ContinuousOn (fun c : Fin r → ℂ => ∏ l, (‖c l‖ ^ 2)⁻¹) C := by
    refine continuousOn_finsetProd _ fun l _ => ?_
    refine ContinuousOn.inv₀ ((continuous_norm.comp (continuous_apply l)).pow 2).continuousOn fun c hc => ?_
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (hCO hc l))
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hcont
  unfold dxc
  rw [withDensity_apply' _ C]
  calc ∫⁻ c in C, ENNReal.ofReal (∏ l, (‖c l‖ ^ 2)⁻¹) ≤ ∫⁻ _ in C, ENNReal.ofReal M :=
        setLIntegral_mono' hC.measurableSet fun c hc => ENNReal.ofReal_le_ofReal
          ((Real.le_norm_self _).trans (hM c hc))
    _ = ENNReal.ofReal M * volume C := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC.measure_lt_top

def ipF (Φ Ψ : RadSp k r z z' π π') (p : (Fin r → ℂ) × Mt k r) : ℂ :=
  inner ℂ (B.hsVec ((Φ : Fn k r (Wq →L[ℂ] Wp)) p.1 (Matrix.of p.2)))
    (B.hsVec ((Ψ : Fn k r (Wq →L[ℂ] Wp)) p.1 (Matrix.of p.2)))

def DomRt (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Set ((Fin r → ℂ) × Mt k r) :=
  {p | ((p.1, Matrix.of p.2) : (Fin r → ℂ) × Mx k r) ∈ DomR k r z z'}

theorem rds_of_cont : Continuous (fun p : (Fin r → ℂ) × Mt k r => ((p.1, Matrix.of p.2) : (Fin r → ℂ) × Mx k r)) :=
  continuous_id

theorem rds_val_contOn (Φ : RadSp k r z z' π π') :
    ContinuousOn (fun p : (Fin r → ℂ) × Mt k r => (Φ : Fn k r (Wq →L[ℂ] Wp)) p.1 (Matrix.of p.2)) (DomRt k r z z') :=
  (radSp_continuousOn Φ).comp rds_of_cont.continuousOn fun _ hp => hp

theorem rds_val_zero (Φ : RadSp k r z z' π π') {p : (Fin r → ℂ) × Mt k r} (hp : p ∉ DomRt k r z z') :
    (Φ : Fn k r (Wq →L[ℂ] Wp)) p.1 (Matrix.of p.2) = 0 :=
  Φ.2.1 (p.1, Matrix.of p.2) hp

theorem rds_DomRt_meas : MeasurableSet (DomRt k r z z') := by
  have hO : IsOpen {c : Fin r → ℂ | c ∈ OmX r} := by
    have : {c : Fin r → ℂ | c ∈ OmX r} = ⋂ l, {c | c l ≠ 0} := by ext c; simp [OmX]
    rw [this]; exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
  have hG : IsClosed {x : Mt k r | (Matrix.of x : Mx k r) ∈ Glev k r (Fin.last r)} := Qx5.Glev_closed _
  have hD : IsOpen {x : Mt k r | 0 < GGl k r z z' (Matrix.of x)} :=
    isOpen_lt continuous_const (Qx5.GGl_continuous k r z z')
  have e : DomRt k r z z' = (Prod.fst ⁻¹' {c : Fin r → ℂ | c ∈ OmX r}) ∩
      ((Prod.snd ⁻¹' {x : Mt k r | (Matrix.of x : Mx k r) ∈ Glev k r (Fin.last r)}) ∩
        (Prod.snd ⁻¹' {x : Mt k r | 0 < GGl k r z z' (Matrix.of x)})) := by
    ext p; rfl
  rw [e]
  exact (hO.measurableSet.preimage measurable_fst).inter
    ((hG.measurableSet.preimage measurable_snd).inter (hD.measurableSet.preimage measurable_snd))

theorem ipF_contOn (Φ Ψ : RadSp k r z z' π π') : ContinuousOn (ipF Φ Ψ) (DomRt k r z z') :=
  ((rds_continuous_hsVec.comp_continuousOn (rds_val_contOn Φ)).inner
    (rds_continuous_hsVec.comp_continuousOn (rds_val_contOn Ψ)))

theorem ipF_measurable (Φ Ψ : RadSp k r z z' π π') : Measurable (ipF Φ Ψ) :=
  measurable_of_continuousOn_zero rds_DomRt_meas (ipF_contOn Φ Ψ) fun p hp => by
    simp [ipF, rds_val_zero Φ hp, rds_hsVec_zero]

theorem ipF_integrable {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    (Φ Ψ : RadSp k r z z' π π') (hΨ : RTest Ψ) : Integrable (ipF Φ Ψ) ((dxc r).prod μ) := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hμ
  obtain ⟨K, hK, hKD, hK0⟩ := hΨ
  let Kt : Set ((Fin r → ℂ) × Mt k r) := {p | ((p.1, Matrix.of p.2) : (Fin r → ℂ) × Mx k r) ∈ K}
  have hKt : IsCompact Kt := hK
  have hKtD : Kt ⊆ DomRt k r z z' := fun p hp => hKD hp
  have h0 : ∀ p, p ∉ Kt → ipF Φ Ψ p = 0 := fun p hp => by
    simp [ipF, hK0 (p.1, Matrix.of p.2) hp, rds_hsVec_zero]
  obtain ⟨M, hM⟩ := hKt.exists_bound_of_continuousOn ((ipF_contOn Φ Ψ).mono hKtD)
  have hfst : IsCompact (Prod.fst '' Kt) := hKt.image continuous_fst
  have hsnd : IsCompact (Prod.snd '' Kt) := hKt.image continuous_snd
  have hfstO : Prod.fst '' Kt ⊆ OmX r := by
    rintro c ⟨p, hp, rfl⟩; exact (hKtD hp).1
  have hfin : ((dxc r).prod μ) Kt ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono (Set.subset_prod (s := Kt)))
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top (rds_dxc_compact hfst hfstO).ne (hμ.finite_compact _ hsnd).ne
  have hOn : IntegrableOn (ipF Φ Ψ) Kt ((dxc r).prod μ) :=
    Measure.integrableOn_of_bounded hfin (ipF_measurable Φ Ψ).aestronglyMeasurable
      (ae_restrict_of_forall_mem hKt.measurableSet hM)
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 hOn
  intro p hp
  by_contra hn
  exact hp (h0 p hn)

theorem radIp_eq_prod {μ : Measure (Mt k r)} (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    (Φ Ψ : RadSp k r z z' π π') (hΨ : RTest Ψ) :
    radIp μ Φ Ψ = ∫ p, ipF Φ Ψ p ∂((dxc r).prod μ) := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hμ
  rw [integral_prod _ (ipF_integrable hμ Φ Ψ hΨ)]
  rfl

end IpInt

theorem spectral_inner_product_linear : RDSIpLin := by
  intro k r z z' Wp Wq _ _ _ _ _ _ π π' μ hμ
  refine ⟨fun Φ₁ Φ₂ Ψ hΨ => ?_, fun Φ Ψ₁ Ψ₂ h₁ h₂ => ?_, fun w Φ Ψ => ⟨?_, ?_⟩⟩
  · rw [radIp_eq_prod hμ _ _ hΨ, radIp_eq_prod hμ Φ₁ Ψ hΨ, radIp_eq_prod hμ Φ₂ Ψ hΨ,
      ← integral_add (ipF_integrable hμ Φ₁ Ψ hΨ) (ipF_integrable hμ Φ₂ Ψ hΨ)]
    congr 1; funext p
    simp only [ipF, Submodule.coe_add, Pi.add_apply, rds_hsVec_add, inner_add_left]
  · rw [radIp_eq_prod hμ _ _ (rTest_add h₁ h₂), radIp_eq_prod hμ Φ Ψ₁ h₁, radIp_eq_prod hμ Φ Ψ₂ h₂,
      ← integral_add (ipF_integrable hμ Φ Ψ₁ h₁) (ipF_integrable hμ Φ Ψ₂ h₂)]
    congr 1; funext p
    simp only [ipF, Submodule.coe_add, Pi.add_apply, rds_hsVec_add, inner_add_right]
  · unfold radIp
    simp only [Submodule.coe_smul, Pi.smul_apply, rds_hsVec_smul, inner_smul_left]
    rw [← integral_const_mul]
    congr 1; funext c
    rw [← integral_const_mul]
  · unfold radIp
    simp only [Submodule.coe_smul, Pi.smul_apply, rds_hsVec_smul, inner_smul_right]
    rw [← integral_const_mul]
    congr 1; funext c
    rw [← integral_const_mul]

end Formalism.FourierDecayAlt.P.CutSE
end
end
