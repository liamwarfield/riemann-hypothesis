module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLinePartitionContinuousCoe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelsAtRecordCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralBoundLtTop
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVBAndClsDetOfShortExact

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqOfRealUnitaryConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqOfRealUnitaryConj
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
open scoped ENNReal Matrix

namespace GlobalTheory.CovolConj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem mass_le (X : Data E r) {x0 x1 : Frame X.Ψ r} (h0 : IsOrth X x0) (h1 : IsOrth X x1)
    {F0 F1 : Set (V (nd X))} (hF0 : IsFundSet X x0 F0) (hF1 : IsFundSet X x1 F1) :
    muF X x0 F0 ≤ muF X x1 F1 := by
  classical
  have := FundSetPf.countable_GL (E := E) (r := r)
  have hM : MeasInvStatement (E := E) := measInv_holds
  have hle := GlobalTheory.Unfold.lintegral_fundSet_inter_le hM r X x0 x1 h0 h1 F0 hF0 (fun _ => 1)
    measurable_const (fun _ _ _ _ _ _ => rfl) F1 hF1.1 hF1.2.1
  simp only [setLIntegral_one] at hle
  refine le_trans (le_of_eq ?_) hle
  let S : Set (Frame X.Ψ r) :=
    ⋃ γ : X.Γ, (fun x => lact (γ.1)⁻¹ x) ⁻¹' GlobalTheory.Unfold.satFrames X x1 F1
  have hS : MeasurableSet S := MeasurableSet.iUnion fun γ =>
    (GlobalTheory.Unfold.continuous_lact X _).measurable (GlobalTheory.Unfold.measurableSet_satFrames X h1 hF1.1 hF1.2.1)
  have hSiff : ∀ x, x ∈ S ↔ ∃ y ∈ F1, ∃ γ ∈ X.Γ, ∃ b ∈ Bor X.Ψ r,
      x = lact γ (rmul (cpt X x1 y) b) := by
    intro x
    simp only [S, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨γ, y, hy, b, hb, h⟩
      refine ⟨y, hy, γ.1, γ.2, b, hb, ?_⟩
      rw [← h, ← FundSetPf.lact_mul, mul_inv_cancel, FundSetPf.lact_one]
    · rintro ⟨y, hy, γ, hγ, b, hb, h⟩
      exact ⟨⟨γ, hγ⟩, y, hy, b, hb, by rw [h, FundSetPf.lact_inv]⟩
  have hSB : ∀ x, ∀ b ∈ Bor X.Ψ r, rmul x b ∈ S ↔ x ∈ S := by
    intro x b hb
    simp only [S, Set.mem_iUnion, Set.mem_preimage, FundSetPf.lact_rmul,
      GlobalTheory.Unfold.rmul_mem_satFrames_iff X x1 F1 _ hb]
  have hI := hM r X x0 x1 h0 h1 (Sᶜ.indicator fun _ => 1) (measurable_const.indicator hS.compl)
    (fun x _ b hb => by simp only [Set.indicator, Set.mem_compl_iff, hSB x b hb])
  have hc : ∀ x : Frame X.Ψ r, ∫⁻ z, (Sᶜ.indicator fun _ => (1 : ℝ≥0∞)) (cpt X x z) ∂muF X x =
      muF X x (cpt X x ⁻¹' Sᶜ) := by
    intro x
    rw [← lintegral_indicator_one ((FundSetPf.cont_cpt X x).measurable hS.compl)]
    rfl
  rw [hc, hc] at hI
  have hz1 : muF X x1 (cpt X x1 ⁻¹' Sᶜ) = 0 := by
    have : ∀ᵐ z ∂muF X x1, cpt X x1 z ∈ S := by
      filter_upwards [hF1.2.2.2] with z hz using (hSiff _).2 hz
    exact this
  have hz0 : ∀ᵐ z ∂muF X x0, cpt X x0 z ∈ S := hI.trans hz1
  refine measure_congr ?_
  filter_upwards [hz0] with z hz
  exact ⟨fun h => ⟨h, (hSiff _).1 hz⟩, fun h => h.1⟩

theorem mass_eq (X : Data E r) {x0 x1 : Frame X.Ψ r} (h0 : IsOrth X x0) (h1 : IsOrth X x1)
    {F0 F1 : Set (V (nd X))} (hF0 : IsFundSet X x0 F0) (hF1 : IsFundSet X x1 F1) :
    muF X x0 F0 = muF X x1 F1 :=
  le_antisymm (mass_le X h0 h1 hF0 hF1) (mass_le X h1 h0 hF1 hF0)

omit [IsCMField E] [NumberField E] in
theorem gram_eq (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G x = xᵀ * G.map τ * x.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

omit [IsCMField E] [NumberField E] in
theorem gram_mul {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} {u : Matrix (Fin r) (Fin r) ℂ}
    (hu : gram τ G u = G.map τ) (x : Matrix (Fin r) (Fin r) ℂ) : gram τ G (u * x) = gram τ G x := by
  rw [gram_eq] at hu
  rw [gram_eq, gram_eq, Matrix.transpose_mul, Matrix.map_mul]
  conv_rhs => rw [← hu]
  simp only [Matrix.mul_assoc]

omit [IsCMField E] [NumberField E] in
theorem det_ne {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E} (hG : G.det ≠ 0)
    {u : Matrix (Fin r) (Fin r) ℂ} (hu : gram τ G u = G.map τ) : u.det ≠ 0 := by
  intro h
  rw [gram_eq] at hu
  have h2 := congrArg Matrix.det hu
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h, zero_mul, zero_mul] at h2
  have h3 : τ G.det = (G.map τ).det := RingHom.map_det τ G
  exact hG ((map_eq_zero τ).1 (h3.trans h2.symm))

noncomputable def umul {Ψ : Finset (E →+* ℂ)} (u : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (x : Frame Ψ r) : Frame Ψ r :=
  fun τ => (u τ.1 * mat x τ : Matrix (Fin r) (Fin r) ℂ)

section

variable (X : Data E r) {u : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ}

omit [IsCMField E] [NumberField E] in
theorem umul_rmul {Ψ : Finset (E →+* ℂ)} (x b : Frame Ψ r) :
    umul u (rmul x b) = rmul (umul u x) b := by
  funext τ
  exact (Matrix.mul_assoc (u τ.1) (mat x τ) (mat b τ)).symm

theorem cpt_umul (x0 : Frame X.Ψ r) (z : V (nd X)) :
    cpt X (umul u x0) z = umul u (cpt X x0 z) := (umul_rmul _ _).symm

theorem gram_umul (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    gram τ.1 X.Gm (mat (umul u x) τ) = gram τ.1 X.Gm (mat x τ) :=
  gram_mul (hu τ.1 τ.2) _

theorem umul_mem_dom (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) (x : Frame X.Ψ r) :
    umul u x ∈ X.dom ↔ x ∈ X.dom := by
  refine forall_congr' fun τ => and_congr ?_ ?_
  · have : mat (umul u x) τ = u τ.1 * mat x τ := rfl
    rw [this, Matrix.det_mul]
    exact ⟨right_ne_zero_of_mul, mul_ne_zero (det_ne X.Gm_det (hu τ.1 τ.2))⟩
  · simp only [dmin, gram_umul X hu]

theorem umul_inj (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) {x y : Frame X.Ψ r}
    (h : umul u x = umul u y) : x = y := by
  funext τ
  have h1 : u τ.1 * mat x τ = u τ.1 * mat y τ := congrFun h τ
  have hd : IsUnit (u τ.1).det := isUnit_iff_ne_zero.mpr (det_ne X.Gm_det (hu τ.1 τ.2))
  have := congrArg (fun M => (u τ.1)⁻¹ * M) h1
  simp only [Matrix.nonsing_inv_mul_cancel_left _ _ hd] at this
  exact this

theorem umul_lact {γ γ' : GL (Fin r) E}
    (h : ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ =
      (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ) (x : Frame X.Ψ r) :
    umul u (lact γ x) = lact γ' (umul u x) := by
  funext τ
  show u τ.1 * ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) =
    (γ' : Matrix (Fin r) (Fin r) E).map τ.1 * (u τ.1 * mat x τ)
  rw [← Matrix.mul_assoc, h τ.1 τ.2, Matrix.mul_assoc]

theorem isOrth_umul (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) {x0 : Frame X.Ψ r}
    (ho : IsOrth X x0) : IsOrth X (umul u x0) := fun τ => by
  rw [gram_umul X hu]; exact ho τ

theorem OmF_umul (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) (x0 : Frame X.Ψ r) :
    OmF X (umul u x0) = OmF X x0 := by
  ext z
  show cpt X (umul u x0) z ∈ X.dom ↔ cpt X x0 z ∈ X.dom
  rw [cpt_umul, umul_mem_dom X hu]

theorem muF_umul (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) (x0 : Frame X.Ψ r) :
    muF X (umul u x0) = muF X x0 := by
  have h2 : densF X (umul u x0) = densF X x0 := by
    funext z
    simp only [densF, dmin, cpt_umul, gram_umul X hu]
  simp only [muF, OmF_umul X hu, h2]

theorem fundSet_umul (hu : ∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ)
    (Γ' : Subgroup (GL (Fin r) E))
    (h1 : ∀ γ ∈ X.Γ, ∃ γ' ∈ Γ', ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ =
      (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ)
    (h2 : ∀ γ' ∈ Γ', ∃ γ ∈ X.Γ, ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ =
      (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ)
    {x0 : Frame X.Ψ r} {FF : Set (V (nd X))} (hF : IsFundSet X x0 FF) :
    MeasurableSet FF ∧ FF ⊆ OmF X (umul u x0) ∧
    (∀ z ∈ FF, ∀ z' ∈ FF, ∀ γ ∈ Γ', ∀ b ∈ Bor X.Ψ r,
      cpt X (umul u x0) z' = lact γ (rmul (cpt X (umul u x0) z) b) → z = z') ∧
    ∀ᵐ z ∂muF X (umul u x0), ∃ z' ∈ FF, ∃ γ ∈ Γ', ∃ b ∈ Bor X.Ψ r,
      cpt X (umul u x0) z = lact γ (rmul (cpt X (umul u x0) z') b) := by
  refine ⟨hF.1, by rw [OmF_umul X hu]; exact hF.2.1, ?_, ?_⟩
  · intro z hz z' hz' γ' hγ' b hb h
    obtain ⟨γ, hγ, hc⟩ := h2 γ' hγ'
    rw [cpt_umul, cpt_umul, ← umul_rmul, ← umul_lact X hc] at h
    exact hF.2.2.1 z hz z' hz' γ hγ b hb (umul_inj X hu h)
  · rw [muF_umul X hu]
    filter_upwards [hF.2.2.2] with z hz
    obtain ⟨z', hz', γ, hγ, b, hb, h⟩ := hz
    obtain ⟨γ', hγ', hc⟩ := h1 γ hγ
    refine ⟨z', hz', γ', hγ', b, hb, ?_⟩
    rw [cpt_umul, cpt_umul, ← umul_rmul, ← umul_lact X hc, h]

end

theorem muF_eq_of_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (hΨ : X'.Ψ = X.Ψ) (u : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (x0 : Frame X.Ψ r) (x0' : Frame X'.Ψ r) (FF : Set (V (nd X))) (FF' : Set (V (nd X'))), X'.Gm = X.Gm → X'.p0 = X.p0 → (∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) → (∀ γ ∈ X.Γ, ∃ γ' ∈ X'.Γ, ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ = (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ) → (∀ γ' ∈ X'.Γ, ∃ γ ∈ X.Γ, ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ = (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ) → IsOrth X x0 → IsOrth X' x0' → IsFundSet X x0 FF → IsFundSet X' x0' FF' → muF X x0 FF = muF X' x0' FF' := by
  intro E _ _ _ r X X' hΨ u x0 x0' FF FF' hG hp hu h1 h2 ho ho' hF hF'
  have k1 := isOrth_umul X hu ho
  have k2 := fundSet_umul X hu X'.Γ h1 h2 hF
  rw [← muF_umul X hu x0]
  have k3 := fun (y : Frame X'.Ψ r) (F : Set (V (nd X'))) (hy : IsOrth X' y) (hF0 : IsFundSet X' y F) =>
    mass_eq X' hy ho' hF0 hF'
  cases X
  cases X'
  dsimp only at hΨ hG hp
  subst hΨ hG hp
  exact k3 (umul u x0) FF k1 k2

end GlobalTheory.CovolConj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqOfRealUnitaryConjStatement
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_eq_of_realUnitary_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (hΨ : X'.Ψ = X.Ψ) (u : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (x0 : Frame X.Ψ r) (x0' : Frame X'.Ψ r) (FF : Set (V (nd X))) (FF' : Set (V (nd X'))), X'.Gm = X.Gm → X'.p0 = X.p0 → (∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) → (∀ γ ∈ X.Γ, ∃ γ' ∈ X'.Γ, ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ = (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ) → (∀ γ' ∈ X'.Γ, ∃ γ ∈ X.Γ, ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ = (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ) → IsOrth X x0 → IsOrth X' x0' → IsFundSet X x0 FF → IsFundSet X' x0' FF' → muF X x0 FF = muF X' x0' FF' := by
  first | exact @GlobalTheory.CovolConj.muF_eq_of_conj | exact GlobalTheory.CovolConj.muF_eq_of_conj | (intros; apply GlobalTheory.CovolConj.muF_eq_of_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportOutFinite
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TraceLevel

theorem apply_out_mk {L W : Type} [Group L] (H : Subgroup L) (ψ : L → W) (hψ : ∀ g, ∀ h ∈ H, ψ (g * h) = ψ g)
    (g : L) : ψ (QuotientGroup.mk g : L ⧸ H).out = ψ g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
  rw [hh, hψ g h h.2]

theorem finsum_out_left {L W : Type} [Group L] [AddCommMonoid W] (H : Subgroup L) (ψ : L → W)
    (hψ : ∀ g, ∀ h ∈ H, ψ (g * h) = ψ g) (l : L) :
    ∑ᶠ q : L ⧸ H, ψ (l * q.out) = ∑ᶠ q : L ⧸ H, ψ q.out := by
  rw [← finsum_comp_equiv (MulAction.toPerm l : Equiv.Perm (L ⧸ H)) (f := fun q : L ⧸ H => ψ q.out)]
  congr 1
  funext q
  have : (MulAction.toPerm l : Equiv.Perm (L ⧸ H)) q = (QuotientGroup.mk (l * q.out) : L ⧸ H) := by
    rw [MulAction.toPerm_apply]
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  show ψ (l * q.out) = ψ ((MulAction.toPerm l : Equiv.Perm (L ⧸ H)) q).out
  rw [this, apply_out_mk H ψ hψ]

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (H : Subgroup G) (v : V) : v ∈ fixed ρ H ↔ ∀ h ∈ H, ρ h v = v := by
  constructor
  · intro hv h hh
    have := hv ⟨h, hh⟩
    simpa using this
  · intro hv h
    show ρ (h : G) v = ((1 : H →* ℂˣ) h : ℂ) • v
    simpa using hv h h.2

theorem support_out_finite {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G)
    (hH : IsOpen (H : Set G)) (F : G → ℂ) (hF : HasCompactSupport F) :
    (Function.support fun q : G ⧸ H => F q.out).Finite := by
  haveI := QuotientGroup.discreteTopology hH
  refine ((HasCompactSupport.isCompact hF).image QuotientGroup.continuous_mk).finite_of_discrete.subset ?_
  intro q hq
  exact ⟨q.out, subset_tsupport _ hq, QuotientGroup.out_eq' q⟩

end GlobalTheory.TraceLevel

namespace GlobalTheory.TraceLevel

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem levOp_id_apply (ρ : Representation ℂ G V) (K H : Subgroup G) (F : G → ℂ)
    (hfin : (Function.support fun q : G ⧸ H => F q.out).Finite) (v : V) :
    levOp ρ K H F LinearMap.id v = ((H.relIndex K : ℕ) : ℂ)⁻¹ • ∑ᶠ q : G ⧸ H, F q.out • ρ q.out v := by
  unfold levOp
  rw [LinearMap.smul_apply]
  congr 1
  rw [finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (fun q hq => by
      rw [Set.Finite.coe_toFinset]
      exact Function.mem_support.2 fun h0 => (Function.mem_support.1 hq) (by simp [h0])),
    finsum_eq_sum_of_support_subset _ (s := hfin.toFinset) (fun q hq => by
      rw [Set.Finite.coe_toFinset]
      exact Function.mem_support.2 fun h0 => (Function.mem_support.1 hq) (by simp [h0])),
    LinearMap.sum_apply]
  simp

theorem levOp_mem_fixed (ρ : Representation ℂ G V) (K K₀ H : Subgroup G) (F : G → ℂ) (hF : IsHecke K₀ F)
    (hH : IsOpen (H : Set G)) (hle : H ≤ K₀) (v : V) (hv : v ∈ fixed ρ H) :
    levOp ρ K H F LinearMap.id v ∈ fixed ρ H := by
  have hfin := support_out_finite H hH F hF.1
  rw [mem_fixed_iff] at hv ⊢
  intro k hk
  rw [levOp_id_apply ρ K H F hfin, map_smul]
  congr 1
  have hfin' : (Function.support fun q : G ⧸ H => F q.out • ρ q.out v).Finite :=
    hfin.subset fun q hq => Function.mem_support.2 fun h0 => (Function.mem_support.1 hq) (by simp [h0])
  rw [map_finsum (ρ k) hfin']
  have := finsum_out_left H (fun g => F g • ρ g v) (fun g h hh => by
    rw [(hF.2 h (hle hh) g).2, map_mul, Module.End.mul_apply, hv h hh]) k
  rw [← this]
  congr 1
  funext q
  rw [map_smul, ← Module.End.mul_apply, ← map_mul, (hF.2 k (hle hk) q.out).1]

theorem twTr_level (ρ : Representation ℂ G V) (K K₀ K'' : Subgroup G) (F : G → ℂ) (hK''o : IsOpen (K'' : Set G))
    (hK : IsCompact (K : Set G)) (hle : K'' ≤ K₀) (hle' : K₀ ≤ K) (hF : IsHecke K₀ F)
    (hfd : FiniteDimensional ℂ (fixed ρ K'')) :
    twTr ρ K K'' F LinearMap.id = twTr ρ K K₀ F LinearMap.id := by
  have hK₀o : IsOpen (K₀ : Set G) := Subgroup.isOpen_mono hle hK''o
  have hc : K''.relIndex K ≠ 0 := by
    haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    have ho : IsOpen ((K''.subgroupOf K : Subgroup K) : Set K) := hK''o.preimage continuous_subtype_val
    haveI := Subgroup.quotient_finite_of_isOpen _ ho
    exact Subgroup.index_ne_zero_of_finite
  have hmul : K''.relIndex K₀ * K₀.relIndex K = K''.relIndex K :=
    Subgroup.relIndex_mul_relIndex (H := K'') (K := K₀) (L := K) hle hle'
  have hd : K''.relIndex K₀ ≠ 0 := left_ne_zero_of_mul (hmul ▸ hc)
  have hcard : Nat.card (↥K₀ ⧸ K''.subgroupOf K₀) ≠ 0 := hd
  haveI : Finite (↥K₀ ⧸ K''.subgroupOf K₀) := Nat.finite_of_card_ne_zero hcard
  letI := Fintype.ofFinite (↥K₀ ⧸ K''.subgroupOf K₀)
  set d : ℕ := K''.relIndex K₀ with hd_def
  obtain ⟨P, hPapp⟩ : ∃ P : V →ₗ[ℂ] V, ∀ v, P v =
      (d : ℂ)⁻¹ • ∑ k : ↥K₀ ⧸ K''.subgroupOf K₀, ρ ((k.out : K₀) : G) v :=
    ⟨(d : ℂ)⁻¹ • ∑ k : ↥K₀ ⧸ K''.subgroupOf K₀, ρ ((k.out : K₀) : G), fun v => by
      simp [LinearMap.sum_apply]⟩
  have hPfix : ∀ v ∈ fixed ρ K'', P v ∈ fixed ρ K₀ := by
    intro v hv
    rw [mem_fixed_iff] at hv ⊢
    intro k hk
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hPapp, map_smul, map_sum]
    congr 1
    have := finsum_out_left (K''.subgroupOf K₀) (fun x : K₀ => ρ (x : G) v) (fun g h hh => by
      simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
      rw [hv _ (Subgroup.mem_subgroupOf.1 hh)]) ⟨k, hk⟩
    simp only [finsum_eq_sum_of_fintype, Subgroup.coe_mul, map_mul, Module.End.mul_apply] at this
    exact this
  have hPid : ∀ v ∈ fixed ρ K₀, P v = v := by
    intro v hv
    rw [mem_fixed_iff] at hv
    rw [hPapp, Finset.sum_congr rfl (fun k _ => hv _ (k.out).2), Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    have : (Fintype.card (↥K₀ ⧸ K''.subgroupOf K₀) : ℂ) = d := by
      rw [← Nat.card_eq_fintype_card]
      rfl
    rw [this, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hd), one_smul]
  have key : ∀ v ∈ fixed ρ K'', levOp ρ K K'' F LinearMap.id v = levOp ρ K K₀ F LinearMap.id (P v) := by
    intro v hv
    have hv' := (mem_fixed_iff ρ K'' v).1 hv
    have hfin'' := support_out_finite K'' hK''o F hF.1
    have hfin₀ := support_out_finite K₀ hK₀o F hF.1
    rw [levOp_id_apply ρ K K'' F hfin'', levOp_id_apply ρ K K₀ F hfin₀]
    have hR : ∀ a : G ⧸ K₀, F a.out • ρ a.out (P v) =
        (d : ℂ)⁻¹ • ∑ᶠ b : ↥K₀ ⧸ K''.subgroupOf K₀, F a.out • ρ (a.out * ((b.out : K₀) : G)) v := by
      intro a
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hPapp, map_smul, map_sum, smul_comm, finsum_eq_sum_of_fintype, Finset.smul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro b _
      rw [map_mul, Module.End.mul_apply]
    simp_rw [hR]
    rw [← smul_finsum, smul_smul]
    have hL : ∑ᶠ q : G ⧸ K'', F q.out • ρ q.out v =
        ∑ᶠ a : G ⧸ K₀, ∑ᶠ b : ↥K₀ ⧸ K''.subgroupOf K₀, F a.out • ρ (a.out * ((b.out : K₀) : G)) v := by
      set e := Subgroup.quotientEquivProdOfLE hle
      rw [← finsum_comp_equiv e.symm]
      have hφ : ∀ g, ∀ h ∈ K'', (fun g => F g • ρ g v) (g * h) = (fun g => F g • ρ g v) g := fun g h hh => by
        simp only
        rw [(hF.2 h (hle hh) g).2, map_mul, Module.End.mul_apply, hv' h hh]
      have he : ∀ p : (G ⧸ K₀) × (↥K₀ ⧸ K''.subgroupOf K₀),
          e.symm p = (QuotientGroup.mk (p.1.out * ((p.2.out : K₀) : G)) : G ⧸ K'') := by
        rintro ⟨a, b⟩
        conv_lhs => rw [← QuotientGroup.out_eq' b]
        rfl
      have h2 : ∀ p : (G ⧸ K₀) × (↥K₀ ⧸ K''.subgroupOf K₀),
          F (e.symm p).out • ρ (e.symm p).out v = F p.1.out • ρ (p.1.out * ((p.2.out : K₀) : G)) v := by
        intro p
        rw [he p]
        have := apply_out_mk K'' (fun g => F g • ρ g v) hφ (p.1.out * ((p.2.out : K₀) : G))
        rw [this, (hF.2 _ (p.2.out).2 p.1.out).2]
      simp_rw [h2]
      rw [finsum_curry]
      refine (hfin₀.prod Set.finite_univ).subset ?_
      rintro ⟨a, b⟩ hp
      refine ⟨?_, Set.mem_univ _⟩
      exact Function.mem_support.2 fun h0 => (Function.mem_support.1 hp) (by simp [h0])
    rw [hL]
    congr 1
    rw [← hmul]
    push_cast
    rw [mul_inv, mul_comm]
  have hVle : fixed ρ K₀ ≤ fixed ρ K'' := by
    intro v hv
    rw [mem_fixed_iff] at hv ⊢
    exact fun h hh => hv h (hle hh)
  haveI : FiniteDimensional ℂ (fixed ρ K₀) := Submodule.finiteDimensional_of_le hVle
  have h'' : ∀ v ∈ fixed ρ K'', levOp ρ K K'' F LinearMap.id v ∈ fixed ρ K'' :=
    fun v hv => levOp_mem_fixed ρ K K₀ K'' F hF hK''o hle v hv
  have h0 : ∀ v ∈ fixed ρ K₀, levOp ρ K K₀ F LinearMap.id v ∈ fixed ρ K₀ :=
    fun v hv => levOp_mem_fixed ρ K K₀ K₀ F hF hK₀o le_rfl v hv
  unfold twTr
  rw [dite_eq_left h'', dite_eq_left h0]
  let Pr : fixed ρ K'' →ₗ[ℂ] fixed ρ K₀ :=
    (P.domRestrict (fixed ρ K'')).codRestrict (fixed ρ K₀) (fun v => hPfix v.1 v.2)
  let ι : fixed ρ K₀ →ₗ[ℂ] fixed ρ K'' := Submodule.inclusion hVle
  have h1 : (levOp ρ K K'' F LinearMap.id).restrict h'' =
      ι ∘ₗ (((levOp ρ K K₀ F LinearMap.id).restrict h0) ∘ₗ Pr) := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    show levOp ρ K K'' F LinearMap.id v = levOp ρ K K₀ F LinearMap.id (P v)
    exact key v v.2
  have h2 : Pr ∘ₗ ι = LinearMap.id := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    show P v = v
    exact hPid v v.2
  rw [h1, LinearMap.trace_comp_comm', LinearMap.comp_assoc, h2, LinearMap.comp_id]

end GlobalTheory.TraceLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothProjVarietyCompactManifold
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothProjVarietyCompactManifold
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
namespace GlobalTheory

theorem cxPts_var_compact_manifold : ∀ Y : Var ℂ, CompactSpace (CxPts Y.str (RingHom.id ℂ)) ∧ T2Space (CxPts Y.str (RingHom.id ℂ)) ∧ SecondCountableTopology (CxPts Y.str (RingHom.id ℂ)) ∧ ∃ A : FinHolAtlas Y.dim (CxPts Y.str (RingHom.id ℂ)), IsAlgAtlas A := fun Y =>
  haveI : CompactSpace (CxPts Y.str (RingHom.id ℂ)) := CxPts.compactSpace (RingHom.id ℂ) Y.isProjOver
  ⟨this, t2Space_cxPts_of_isProjOver _ Y.isProjOver, secondCountableTopology_of_isProjOver _ Y.isProjOver,
    (AnRead.all Y.str (RingHom.id ℂ) Y.dim).finAtlas, AnRead.isAlgAtlas_finAtlas _⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothProjVarietyCompactManifoldStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexPoints_smoothProjVariety_compact_manifold : ∀ Y : Var ℂ, CompactSpace (CxPts Y.str (RingHom.id ℂ)) ∧ T2Space (CxPts Y.str (RingHom.id ℂ)) ∧ SecondCountableTopology (CxPts Y.str (RingHom.id ℂ)) ∧ ∃ A : FinHolAtlas Y.dim (CxPts Y.str (RingHom.id ℂ)), IsAlgAtlas A := by
  first | exact @GlobalTheory.cxPts_var_compact_manifold | exact GlobalTheory.cxPts_var_compact_manifold | (intros; apply GlobalTheory.cxPts_var_compact_manifold <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingSumDegreeFormula
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare

namespace GlobalTheory

theorem card_embeddings_restrict_eq_finrank (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k']
    [Algebra k k'] (τ : k →+* ℂ) :
    Nat.card {σ : k' →+* ℂ // σ.comp (algebraMap k k') = τ} = Module.finrank k k' := by
  letI : Algebra k ℂ := τ.toAlgebra
  haveI : Module.Finite k k' := Module.Finite.of_restrictScalars_finite ℚ k k'
  rw [← AlgHom.card k k' ℂ, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr ⟨fun σ => { σ.1 with commutes' := fun x => RingHom.congr_fun σ.2 x },
    fun φ => ⟨φ.toRingHom, RingHom.ext fun x => φ.commutes x⟩, fun σ => rfl, fun φ => rfl⟩

theorem finrank_mul_sum_embeddings_comp (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k']
    (i : k →+* k') (f : (k →+* ℂ) → ℝ) :
    (Module.finrank ℚ k : ℝ) * ∑ σ : k' →+* ℂ, f (σ.comp i)
      = (Module.finrank ℚ k' : ℝ) * ∑ σ : k →+* ℂ, f σ := by
  classical
  letI : Algebra k k' := i.toAlgebra
  have h1 : ∑ σ : k' →+* ℂ, f (σ.comp i) = (Module.finrank k k' : ℝ) * ∑ σ : k →+* ℂ, f σ := by
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun σ : k' →+* ℂ => σ.comp i), Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => f τ) (fun σ hσ => by rw [(Finset.mem_filter.1 hσ).2]),
      Finset.sum_const, nsmul_eq_mul, ← card_embeddings_restrict_eq_finrank k k' τ,
      Nat.card_eq_fintype_card, Fintype.card_subtype]
    rfl
  rw [h1, ← _root_.mul_assoc, ← Module.finrank_mul_finrank ℚ k k', Nat.cast_mul]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AemeasurableChartOfLocallyContinuousDensity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AemeasurableChartOfLocallyContinuousDensity
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem aemeasurable_chart_of_locally_continuous {n : ℕ} {Y : Type} [TopologicalSpace Y]
    (e : OpenPartialHomeomorph Y (V n)) {S : Set Y} {d : Y → ℝ} (hS : IsOpen S)
    (h : ∀ y ∈ S, y ∈ e.source →
      ∃ g : V n → ℝ, ContinuousAt g (e y) ∧ ∀ᶠ z in 𝓝 y, d z = g (e z)) :
    AEMeasurable (fun v => d (e.symm v)) (volume.restrict (e.target ∩ e.symm ⁻¹' S)) := by
  have hO : IsOpen (e.target ∩ e.symm ⁻¹' S) := e.isOpen_inter_preimage_symm hS
  refine ContinuousOn.aemeasurable (fun v hv => ContinuousAt.continuousWithinAt ?_) hO.measurableSet
  obtain ⟨hvt, hvS⟩ := hv
  obtain ⟨g, hg, hev⟩ := h _ hvS (e.map_target hvt)
  rw [e.right_inv hvt] at hg
  refine hg.congr ?_
  have h1 := (e.continuousAt_symm hvt).eventually hev
  filter_upwards [h1, e.open_target.mem_nhds hvt] with w hw hwt
  rw [hw, e.right_inv hwt]

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AemeasurableChartOfLocallyContinuousDensityStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aemeasurable_chart_of_locally_continuous_density : ∀ {n : ℕ} {Y : Type} [TopologicalSpace Y] (e : OpenPartialHomeomorph Y (V n)) {S : Set Y} {d : Y → ℝ}, IsOpen S → (∀ y ∈ S, y ∈ e.source → ∃ g : V n → ℝ, ContinuousAt g (e y) ∧ ∀ᶠ z in 𝓝 y, d z = g (e z)) → AEMeasurable (fun v => d (e.symm v)) (volume.restrict (e.target ∩ e.symm ⁻¹' S)) := by
  first | exact @GlobalTheory.GoodTop.aemeasurable_chart_of_locally_continuous | exact GlobalTheory.GoodTop.aemeasurable_chart_of_locally_continuous | (intros; apply GlobalTheory.GoodTop.aemeasurable_chart_of_locally_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyMulLeftGeneratorEqMapSymm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyMulLeftGeneratorEqMapSymm
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory

theorem charpoly_mulLeft_eq_of_adjoin_eq_top {F A : Type*} [Field F] [CommRing A] [Algebra F A]
    [Module.Finite F A] (u : A) (P : F[X]) (hP : P.Monic) (hadj : Algebra.adjoin F {u} = ⊤)
    (hu : aeval u P = 0) (hdim : Module.finrank F A = P.natDegree) :
    (LinearMap.mulLeft F u).charpoly = P := by
  have hint : IsIntegral F u := ⟨P, hP, hu⟩
  let pb := PowerBasis.ofAdjoinEqTop hint hadj
  have hgen : pb.gen = u := PowerBasis.ofAdjoinEqTop_gen hint hadj
  have hmin : minpoly F u = P := by
    refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hP (minpoly.dvd F u hu) ?_).symm
    rw [← hdim, pb.finrank, PowerBasis.ofAdjoinEqTop_dim]
  have h1 := charpoly_leftMulMatrix pb
  rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix, hgen, hmin] at h1
  exact h1

theorem charpoly_mulLeft_eq_map_symm : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (R : Type) [Field R] (e : K.E ≃+* R) (u : B.A) (Q : R[X]), Q.Monic → Algebra.adjoin K.E {u} = ⊤ → aeval u (Q.map e.symm.toRingHom) = 0 → Module.finrank K.E B.A = Q.natDegree → (LinearMap.mulLeft K.E u).charpoly = Q.map e.symm.toRingHom := by
  intro K B R _ e u Q hQ hadj hu hdim
  exact charpoly_mulLeft_eq_of_adjoin_eq_top u _ (hQ.map _) hadj hu (by rw [hdim, hQ.natDegree_map])

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyMulLeftGeneratorEqMapSymmStatement
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charpoly_mulLeft_generator_eq_map_symm : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (R : Type) [Field R] (e : K.E ≃+* R) (u : B.A) (Q : R[X]), Q.Monic → Algebra.adjoin K.E {u} = ⊤ → aeval u (Q.map e.symm.toRingHom) = 0 → Module.finrank K.E B.A = Q.natDegree → (LinearMap.mulLeft K.E u).charpoly = Q.map e.symm.toRingHom := by
  first | exact @GlobalTheory.charpoly_mulLeft_eq_map_symm | exact GlobalTheory.charpoly_mulLeft_eq_map_symm | (intros; apply GlobalTheory.charpoly_mulLeft_eq_map_symm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralOneEqMongeAmpereIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralOneEqMongeAmpereIntegral
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
namespace GlobalTheory

theorem chernInt_one_eq_mInt : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → φ.ChernIntegrableOn Y.dim Set.univ (fun _ => 1) ∧ ∀ A : FinHolAtlas Y.dim (CxPts Y.str (RingHom.id ℂ)), IsAlgAtlas A → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = mInt A (fun _ => φ.locPot) (fun _ => 1) := by
  intro Y L φ h
  haveI : CompactSpace (CxPts Y.str (RingHom.id ℂ)) := CxPts.compactSpace _ Y.isProjOver
  haveI : T2Space (CxPts Y.str (RingHom.id ℂ)) := t2Space_cxPts_of_isProjOver _ Y.isProjOver
  haveI : SecondCountableTopology (CxPts Y.str (RingHom.id ℂ)) :=
    secondCountableTopology_of_isProjOver _ Y.isProjOver
  have hA₀ := AnRead.isAlgAtlas_finAtlas (AnRead.all Y.str (RingHom.id ℂ) Y.dim)
  have hi : φ.ChernIntegrableOn Y.dim Set.univ (fun _ => 1) :=
    (h.chernInt_eq_mInt_of_isAlgAtlas hA₀ measurable_const).1.2
      (mIntegrableCont _ _
        (fun _ => ((Weight.isCInf_iff_isSmooth hA₀.anRead).1 h).isPotential hA₀) _ continuous_const)
  exact ⟨hi, fun A hA => (h.chernInt_eq_mInt_of_isAlgAtlas hA measurable_const).2 hi⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegralOneEqMongeAmpereIntegralStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernIntegral_one_eq_mongeAmpereIntegral : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → φ.ChernIntegrableOn Y.dim Set.univ (fun _ => 1) ∧ ∀ A : FinHolAtlas Y.dim (CxPts Y.str (RingHom.id ℂ)), IsAlgAtlas A → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = mInt A (fun _ => φ.locPot) (fun _ => 1) := by
  first | exact @GlobalTheory.chernInt_one_eq_mInt | exact GlobalTheory.chernInt_one_eq_mInt | (intros; apply GlobalTheory.chernInt_one_eq_mInt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreDimensionLe
open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.FibreProj

namespace GlobalTheory.GenFibreDim

section

attribute [local instance low] specializationOrder

theorem le_height_of_specializingMap {X Z : Type*} [TopologicalSpace X] [TopologicalSpace Z]
    [T0Space X] [T0Space Z] {f : X → Z} (hf : SpecializingMap f) (n : ℕ) :
    ∀ y : X, (n : ℕ∞) ≤ Order.height (f y) → (n : ℕ∞) ≤ Order.height y := by
  induction n with
  | zero => intro y _; simp
  | succ n ih =>
    intro y hy
    have hex : ∃ b < f y, (n : ℕ∞) ≤ Order.height b := by
      by_contra hne
      push_neg at hne
      have h1 : Order.height (f y) ≤ n := by
        rw [Order.height_eq_iSup_lt_height]
        exact iSup₂_le fun b hb => Order.add_one_le_of_lt (hne b hb)
      have h2 : ((n + 1 : ℕ) : ℕ∞) ≤ n := hy.trans h1
      have h3 : n + 1 ≤ n := by exact_mod_cast h2
      omega
    obtain ⟨b, hb, hnb⟩ := hex
    obtain ⟨y', hyy', rfl⟩ := hf hb.le
    have hlt : y' < y := lt_of_le_of_ne hyy' (fun h => hb.ne (by rw [h]))
    have h4 := Order.height_add_one_le hlt
    have h5 := ih y' hnb
    calc ((n + 1 : ℕ) : ℕ∞) = (n : ℕ∞) + 1 := by push_cast; rfl
      _ ≤ Order.height y' + 1 := by gcongr
      _ ≤ Order.height y := h4

end

end GlobalTheory.GenFibreDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamificationWeightedLogNormSum
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare

namespace GlobalTheory.FlatDegreeCompare

theorem exists_under_valuation_sum_log_absNorm : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k'), ∃ (π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)) (ε : HeightOneSpectrum (𝓞 k') → ℕ), (∀ 𝔓 (z : k), 𝔓.valuation k' (i z) = (π 𝔓).valuation k z ^ ε 𝔓) ∧ ∀ 𝔭, ∃ s : Finset (HeightOneSpectrum (𝓞 k')), (∀ 𝔓, 𝔓 ∈ s ↔ π 𝔓 = 𝔭) ∧ s.Nonempty ∧ (Module.finrank ℚ k : ℝ) * ∑ 𝔓 ∈ s, (ε 𝔓 : ℝ) * Real.log (Ideal.absNorm 𝔓.asIdeal) = (Module.finrank ℚ k' : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal) := by
  intro k k' _ _ _ _ i
  letI : Algebra k k' := i.toAlgebra
  refine ⟨fun 𝔓 => 𝔓.under (𝓞 k), fun 𝔓 => 𝔓.asIdeal.ramificationIdx (𝓞 k), fun 𝔓 z => ?_, fun 𝔭 => ?_⟩
  · have : 𝔓.asIdeal.LiesOver (𝔓.under (𝓞 k)).asIdeal := ⟨rfl⟩
    have h := HeightOneSpectrum.valuation_liesOver k' (𝔓.under (𝓞 k)) 𝔓 z
    exact h.symm
  · have hs := GlobalTheory.Adelic.HeightExt.sum_locDeg (L := k') 𝔭
    have hpos : 0 < Module.finrank k k' := Module.finrank_pos
    refine ⟨(GlobalTheory.Adelic.HeightExt.finite_fiber (L := k') 𝔭).toFinset, fun 𝔓 => Set.Finite.mem_toFinset _, ?_, ?_⟩
    · rw [Finset.nonempty_iff_ne_empty]
      intro h0
      rw [h0, Finset.sum_empty] at hs
      omega
    · rw [← Module.finrank_mul_finrank ℚ k k', ← hs, Nat.cast_mul, _root_.mul_assoc, Nat.cast_sum, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun 𝔓 h𝔓 => ?_
      have hu : 𝔓.under (𝓞 k) = 𝔭 := ((GlobalTheory.Adelic.HeightExt.finite_fiber (L := k') 𝔭).mem_toFinset).1 h𝔓
      have : 𝔓.asIdeal.LiesOver 𝔭.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal hu).symm⟩
      have hn := Ideal.absNorm_eq_pow_inertiaDeg'_of_liesOver 𝔓.asIdeal 𝔭.asIdeal 𝔭.isPrime 𝔭.ne_bot
      rw [Ideal.inertiaDeg'_eq_inertiaDeg] at hn
      rw [hn, GlobalTheory.Adelic.HeightExt.locDeg]
      push_cast
      rw [Real.log_pow]
      ring

end GlobalTheory.FlatDegreeCompare
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupRowsEigenpartsPrincipalLevelEqTop
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupRowsEigenpartsPrincipalLevelEqTop
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.SpanParts

theorem iSup_rows_eigenparts_principal_level_eq_top : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) → (⨆ p, R.EEp3 p) = ⊤ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hW hEx hS hC
  obtain ⟨hCore, hSF, hE, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  obtain ⟨h, -, -, hTop, -⟩ := GlobalTheory.T.exists_sphericalOperators_rows_normal_eigenspaces R.toRealDat F.lv2 hCore hS R.SF hSF
  rw [eq_top_iff, ← hTop]
  refine iSup_le fun c => ?_
  by_cases h0 : R.EEc c = ⊥
  · rw [← hE c, h0]; exact bot_le
  · obtain ⟨p, hp⟩ := hC c h0
    rw [← hE c]
    refine le_trans ?_ (le_iSup _ p)
    exact le_iSup₂_of_le c hp le_rfl

end GlobalTheory.SpanParts
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupRowsEigenpartsPrincipalLevelEqTopStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iSup_eEp3_eq_whole_space_of_weakCharacterisation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) → (⨆ p, R.EEp3 p) = ⊤ := by
  first | exact @GlobalTheory.SpanParts.iSup_rows_eigenparts_principal_level_eq_top | exact GlobalTheory.SpanParts.iSup_rows_eigenparts_principal_level_eq_top | (intros; apply GlobalTheory.SpanParts.iSup_rows_eigenparts_principal_level_eq_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSimilitudeOfLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UPel.LocSim

theorem exists_open_eq_of_torsion_point : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ), IsUnit (n : Γ(S, ⊤)) → ∀ (σ σ' : 𝟙_ (Over S) ⟶ A), σ ^ n = 1 → σ' ^ n = 1 → ∀ (k : Type) [Field k] (y : Sp k ⟶ S), toUnit (Over.mk y) ≫ σ = toUnit (Over.mk y) ≫ σ' → ∃ V : S.Opens, Set.range y ⊆ (V : Set S) ∧ V.ι ≫ σ.left = V.ι ≫ σ'.left := by
  intro S A _ _ hA n hn σ σ' hσ hσ' k _ y hy
  haveI := hA.smooth
  haveI : FormallyUnramified (ReciprocityTheory.ChartRestriction.G.Out.mulA A n).left := GlobalTheory.formallyUnramified_mulA S A n hn
  haveI : LocallyOfFiniteType (ReciprocityTheory.ChartRestriction.G.Out.mulA A n).left := by
    have : LocallyOfFiniteType ((ReciprocityTheory.ChartRestriction.G.Out.mulA A n).left ≫ A.hom) := by rw [Over.w]; infer_instance
    exact locallyOfFiniteType_of_comp _ A.hom
  have hab : σ.left ≫ (ReciprocityTheory.ChartRestriction.G.Out.mulA A n).left = σ'.left ≫ (ReciprocityTheory.ChartRestriction.G.Out.mulA A n).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    show σ ≫ 𝟙 A ^ n = σ' ≫ 𝟙 A ^ n
    rw [MonObj.comp_pow, MonObj.comp_pow, Category.comp_id, Category.comp_id, hσ, hσ']
  haveI := GlobalTheory.isOpenImmersion_equalizer_ι_of_unramified (ReciprocityTheory.ChartRestriction.G.Out.mulA A n).left hab
  refine ⟨(equalizer.ι σ.left σ'.left).opensRange, ?_, ?_⟩
  · have hy' : y ≫ σ.left = y ≫ σ'.left := by
      have h := congrArg CommaMorphism.left hy
      simp only [Over.comp_left, GlobalTheory.ObjPull.toUnit_left'] at h
      exact h
    exact GlobalTheory.range_subset_range_equalizer_ι y hy'
  · rw [← cancel_epi (equalizer.ι σ.left σ'.left).isoOpensRange.hom, ← Category.assoc, ← Category.assoc,
      Scheme.Hom.isoOpensRange_hom_ι, equalizer.condition]

section
variable {F : Type} [Field F] [NumberField F] [IsCMField F] {D : GlobalTheory.UPel.Datum F} {p N : ℕ} {S : Scheme.{0}}
  {s : S ⟶ Sp (D.OEp p)} {o : GlobalTheory.UPel.Obj D p N s}

end

end GlobalTheory.UPel.LocSim
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightStabilizerConjBiinvariantFiniteIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightStabilizerConjBiinvariantFiniteIndex
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RStabFin

theorem rStab_conj_index_ne_zero : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K K' : Subgroup G)
    (f : G → ℂ) (δ : G), IsCompact (K : Set G) → IsOpen (K' : Set G) → K' ≤ K →
    (∀ k ∈ K', ∀ x, f (k * x) = f x ∧ f (x * k) = f x) → ∀ x : G,
    (rStab fun k : K => f ((x * k)⁻¹ * δ * (x * k))).index ≠ 0 := by
  intro G _ _ _ K K' f δ hK hK' _ hf x
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hopen : IsOpen ((K'.subgroupOf K : Subgroup K) : Set K) := hK'.preimage continuous_subtype_val
  have hfin : Finite (K ⧸ K'.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ hopen
  have h0 : (K'.subgroupOf K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hle : K'.subgroupOf K ≤ rStab fun k : K => f ((x * k)⁻¹ * δ * (x * k)) := by
    intro k hk y
    have hk' : ((k : K) : G) ∈ K' := hk
    show f ((x * ((y * k : K) : G))⁻¹ * δ * (x * ((y * k : K) : G))) = f ((x * (y : G))⁻¹ * δ * (x * (y : G)))
    have e : (x * ((y * k : K) : G))⁻¹ * δ * (x * ((y * k : K) : G))
        = ((k : G))⁻¹ * ((x * (y : G))⁻¹ * δ * (x * (y : G)) * (k : G)) := by
      simp only [Subgroup.coe_mul, _root_.mul_inv_rev]; group
    rw [e, (hf _ (inv_mem hk') _).1, (hf _ hk' _).2]
  exact fun h => h0 (Nat.eq_zero_of_zero_dvd (h ▸ Subgroup.index_dvd_of_le hle))

end GlobalTheory.RStabFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightStabilizerConjBiinvariantFiniteIndexStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightStabilizer_conj_biinvariant_finiteIndex : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K K' : Subgroup G) (f : G → ℂ) (δ : G), IsCompact (K : Set G) → IsOpen (K' : Set G) → K' ≤ K → (∀ k ∈ K', ∀ x, f (k * x) = f x ∧ f (x * k) = f x) → ∀ x : G, (rStab fun k : K => f ((x * k)⁻¹ * δ * (x * k))).index ≠ 0 := by
  first | exact @GlobalTheory.RStabFin.rStab_conj_index_ne_zero | exact GlobalTheory.RStabFin.rStab_conj_index_ne_zero | (intros; apply GlobalTheory.RStabFin.rStab_conj_index_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOnInvariantSubmoduleISupEqSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOnInvariantSubmoduleISupEqSum
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem trOn_iSup_eq_sum : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : Type) [Fintype ι] (M : ι → Submodule ℂ V)
    (L : V →ₗ[ℂ] V), iSupIndep M → (∀ i, FiniteDimensional ℂ (M i)) → (∀ i, ∀ v ∈ M i, L v ∈ M i) →
    trOn (⨆ i, M i) L = ∑ i, trOn (M i) L := by
  intro V _ _ ι _ M L hind hfin hinv
  haveI := hfin
  have hp : (⨆ i, M i) = ⨆ i ∈ (Finset.univ : Finset ι), M i := by simp
  have hs : iSupIndep (fun i : (Finset.univ : Finset ι) ↦ M i) :=
    hind.comp Subtype.val_injective
  have hf : ∀ i, Set.MapsTo L (M i) (M i) := fun i v hv ↦ hinv i v hv
  have hsup : ∀ v ∈ (⨆ i, M i), L v ∈ (⨆ i, M i) := by
    intro v hv
    refine Submodule.iSup_induction M (motive := fun v ↦ L v ∈ ⨆ i, M i) hv ?_ ?_ ?_
    · intro i x hx; exact Submodule.mem_iSup_of_mem i (hinv i x hx)
    · simp
    · intro x y hx hy; rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  have key := LinearMap.trace_eq_sum_trace_restrict_of_eq_biSup (N := M) Finset.univ hs hf
    (⨆ i, M i) hp hsup
  unfold trOn
  rw [dite_eq_left hsup, key]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [dite_eq_left (hinv i)]

end GlobalTheory.BCT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOnInvariantSubmoduleISupEqSumStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceOnInvariantSubmodule_iSup_eq_sum : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (ι : Type) [Fintype ι] (M : ι → Submodule ℂ V) (L : V →ₗ[ℂ] V), iSupIndep M → (∀ i, FiniteDimensional ℂ (M i)) → (∀ i, ∀ v ∈ M i, L v ∈ M i) → trOn (⨆ i, M i) L = ∑ i, trOn (M i) L := by
  first | exact @GlobalTheory.BCT.trOn_iSup_eq_sum | exact GlobalTheory.BCT.trOn_iSup_eq_sum | (intros; apply GlobalTheory.BCT.trOn_iSup_eq_sum <;> assumption)
end
end
