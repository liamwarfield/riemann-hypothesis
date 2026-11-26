module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroupA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSchurW

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroup
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroupB
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal NNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace InvGrp

variable {k r : ℕ}

theorem continuous_lmulM (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by
  unfold lmulM; fun_prop

theorem map_invol_eq (HU : HaarUnique) {U : Set (Mat k r)} (hU : IsClosedSubgroup U) {μ : Measure (Mt k r)}
    (hμ : IsHaarOn U μ) (f : Mt k r → Mt k r) (hf : Continuous f) (hff : ∀ x, f (f x) = x)
    (hfU : ∀ x : Mt k r, (x : Mat k r) ∈ U → (f x : Mat k r) ∈ U)
    (hl : ∀ a ∈ U, ∃ b ∈ U, ∀ x, lmulM a (f x) = f (lmulM b x)) : μ.map f = μ := by
  have hfm : Measurable f := hf.measurable
  have hUc : IsClosed (show Set (Mt k r) from U) := hU.closed
  have hUm : MeasurableSet (show Set (Mt k r) from U) := hUc.measurableSet
  have h1 : (μ.map f) Uᶜ = 0 := by
    rw [Measure.map_apply hfm hUm.compl]
    refine measure_mono_null (fun x hx => ?_) hμ.conc
    intro hxU
    exact hx (hfU x hxU)
  have h2 : ∀ a ∈ U, (μ.map f).map (lmulM a) = μ.map f := by
    intro a ha
    obtain ⟨b, hb, hab⟩ := hl a ha
    rw [Measure.map_map (continuous_lmulM a).measurable hfm]
    have : lmulM a ∘ f = f ∘ lmulM b := funext hab
    rw [this, ← Measure.map_map hfm (continuous_lmulM b).measurable, hμ.left b hb]
  have h3 : ∀ K : Set (Mt k r), IsCompact K → (μ.map f) K < ∞ := by
    intro K hK
    rw [Measure.map_apply hfm hK.measurableSet]
    have : f ⁻¹' K = f '' K := by
      ext x; constructor
      · intro hx; exact ⟨f x, hx, hff x⟩
      · rintro ⟨y, hy, rfl⟩; show f (f y) ∈ K; rw [hff]; exact hy
    rw [this]
    exact hμ.finite_compact _ (hK.image hf)
  obtain ⟨c, hc⟩ := HU k r U μ (μ.map f) hU hμ h1 h2 h3
  have hff' : f ∘ f = id := funext hff
  have hback : (μ.map f).map f = μ := by
    rw [Measure.map_map hfm hfm, hff', Measure.map_id]
  have hcc : (c * c) • μ = μ := by
    conv_rhs => rw [← hback]
    rw [hc, Measure.map_smul c hfm.aemeasurable, hc, smul_smul]

  obtain ⟨K, hK, hK0⟩ : ∃ K : Set (Mt k r), IsCompact K ∧ μ K ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hμ.ne_zero
    have : μ Set.univ = 0 := by
      rw [← Metric.iUnion_closedBall_nat (0 : Mt k r)]
      exact measure_iUnion_null fun n => hcon _ (isCompact_closedBall _ _)
    exact Measure.measure_univ_eq_zero.mp this
  have hKt : μ K ≠ ∞ := (hμ.finite_compact K hK).ne
  have hval : ((c * c : ℝ≥0) : ℝ≥0∞) * μ K = 1 * μ K := by
    have := congrArg (fun ν : Measure (Mt k r) => ν K) hcc
    simpa using this
  have hc1 : ((c * c : ℝ≥0) : ℝ≥0∞) = 1 := (ENNReal.mul_left_inj hK0 hKt).mp hval
  have hc2 : (c : ℝ) * c = 1 := by
    have : c * c = 1 := by exact_mod_cast hc1
    exact_mod_cast this
  have hcpos : (0 : ℝ) ≤ c := c.2
  have hc3 : c = 1 := by
    have : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  rw [hc, hc3, one_smul]

end InvGrp

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

noncomputable section

open MeasureTheory Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

theorem stInvGroup (h : UnitaryGroupStructuralFacts) : StInvGroup := by
  obtain ⟨hB2, -, -, -, hUWb, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hHU, hHI, -, hCG, hCN, hCW, -⟩ := hB2
  intro k r Wp _ _ _ D X _ _ γ hγ
  have hG := hCG k r
  have hEG : embWb k r γ ∈ GV k r := by
    have hmem : embWb k r γ ∈ UWb k r := by rw [(hUWb k r).1]; exact ⟨γ, hγ.1, rfl⟩
    exact hmem.1
  have hE := hG.unit _ hEG
  have hz := InvGrp.frame_conjugation_fixes_point hG hEG D.z D.T_pos hγ.2
  let gb : Mt k r → Mt k r := fun x i j => gbar k r γ (Matrix.of x) i j
  have hgb : Continuous gb := by
    simp only [gb, gbar]; fun_prop
  have hff : ∀ x, gb (gb x) = x := by
    intro x; funext i j
    change gbar k r γ (gbar k r γ (Matrix.of x)) i j = x i j
    rw [InvGrp.gbar_gbar hE]; rfl
  have hl : ∀ U : Set (Mat k r), (∀ a ∈ U, gbar k r γ a ∈ U) →
      ∀ a ∈ U, ∃ b ∈ U, ∀ x, lmulM a (gb x) = gb (lmulM b x) := by
    intro U hU a ha
    refine ⟨gbar k r γ a, hU a ha, fun x => ?_⟩
    funext i j
    change (a * gbar k r γ (Matrix.of x)) i j = gbar k r γ (gbar k r γ a * Matrix.of x) i j
    rw [InvGrp.gbar_mul hE, InvGrp.gbar_gbar hE]
  have hG1 : ∀ g ∈ GV k r, gbar k r γ g ∈ GV k r := InvGrp.gbar_mem_GV hG hEG
  have hN1 : ∀ m ∈ Nset k r, gbar k r γ m ∈ Nset k r := InvGrp.gbar_mem_N hG hEG
  have hW1 : ∀ h ∈ UWset k r D.z, gbar k r γ h ∈ UWset k r D.z := InvGrp.gbar_mem_UW hG hEG D.z hz
  have hmapG : D.μG.map gb = D.μG :=
    InvGrp.map_invol_eq hHU hG D.haarG gb hgb hff (fun x hx => hG1 _ hx) (hl _ hG1)
  refine ⟨hG1, hN1, hW1, InvGrp.gbar_mem_UU hG hEG D.z hz, ?_, ?_, ?_, ?_, ?_⟩
  · intro g _ g' _
    unfold th
    rw [InvGrp.gbar_mul hE, Matrix.mul_inv_rev]
  · intro g hg
    unfold th
    rw [InvGrp.gbar_inv hE _ (hG.unit _ (hG1 g hg)), InvGrp.gbar_gbar hE]
    exact Matrix.nonsing_inv_nonsing_inv g (hG.unit g hg)
  · have hth : (fun x : Mt k r => fun i j => th k r γ (Matrix.of x) i j) = invM ∘ gb := by
      funext x; rfl
    rw [hth, ← Measure.map_map InvGrp.measurable_invM hgb.measurable, hmapG, hHI k r (GV k r) D.μG hG D.haarG]
  · exact InvGrp.map_invol_eq hHU (hCN k r) D.haarN gb hgb hff (fun x hx => hN1 _ hx) (hl _ hN1)
  · exact InvGrp.map_invol_eq hHU (hCW k r D.z) D.haarW gb hgb hff (fun x hx => hW1 _ hx) (hl _ hW1)

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StCut1p
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

def StCut0 : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), ∀ g ∈ GV k r, ∀ v ∈ DDinf D X, X.σ g v ∈ DDinf D X

def StCut1p : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (A : ℝ) (m : ℕ) (f : Mat k r → ℂ) (X₀ : Wp →L[ℂ] Wp), InCC A m f → InCC A m (fun g => f g • X₀)

def StCut1 : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → ∀ d : ℝ, IsFdegG D X d →
    ∀ (f : Mat k r → ℂ) (x y a₂ b₂ : X.Hs) (X₀ : Wp →L[ℂ] Wp), (∀ g ∈ GV k r, f g = mc X x y g) →
    ∀ p : SS k r, D.inSS p →
      Ph D (scalF Wp f) (fun g => mc X a₂ b₂ g • X₀) p =
        hsInner ((D.π (Matrix.of p.1.1)).comp (D.π (Matrix.of p.2.1)⁻¹)) X₀ *
          (mc X x a₂ (Matrix.of p.2.2 * Matrix.of p.2.1) *
            star (mc X y b₂ (Matrix.of p.1.2 * Matrix.of p.1.1))) / (d : ℂ)

def StCut2 : Prop :=
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → ∀ d : ℝ, IsFdegG D X d →
    ∀ (f : Mat k r → ℂ) (x y a₂ b₂ : X.Hs) (X₀ : Wp →L[ℂ] Wp), (∀ g ∈ GV k r, f g = mc X x y g) →
    Integrable (beInt D X x a₂) (D.μW.prod D.μN) → Integrable (beInt D X y b₂) (D.μW.prod D.μN) →
      Integrable (Ph D (scalF Wp f) (fun g => mc X a₂ b₂ g • X₀)) D.μSS ∧
      ∫ p, xiTau D (1, 1) p * Ph D (scalF Wp f) (fun g => mc X a₂ b₂ g • X₀) p ∂D.μSS =
        hsInner ((ContinuousLinearMap.adjoint (beOp D X y b₂)).comp (beOp D X x a₂)) X₀ / (d : ℂ)

def StCut4 : Prop :=
  StSchurW →
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp), IsDiag D → ∀ (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (P₁ Q P₂ Q₂ : Wp →L[ℂ] Wp),
    (∀ h ∈ UWset k r D.z, (ContinuousLinearMap.adjoint P₁).comp ((D.π h).comp Q) =
      (ContinuousLinearMap.adjoint P₂).comp ((D.π (th k r γ h)).comp Q₂)) →
    ((∀ x y x' y' : Wp, ∫ h : Mt k r, ⟪y, D.π (th k r γ (Matrix.of h)) x⟫_ℂ *
        star ⟪y', D.π (Matrix.of h) x'⟫_ℂ ∂D.μW = 0) →
      ∀ x y ξ η : Wp, ⟪η, Q x⟫_ℂ * ⟪P₁ y, ξ⟫_ℂ = 0) ∧
    (∀ C₀ : Wp ≃ₗᵢ⋆[ℂ] Wp,
      (∀ h ∈ UWset k r D.z, ∀ x y : Wp, ⟪y, D.π (th k r γ h) x⟫_ℂ = ⟪C₀ x, D.π h (C₀ y)⟫_ℂ) →
      ∀ x y ξ η : Wp, ⟪η, Q x⟫_ℂ * ⟪P₁ y, ξ⟫_ℂ = ⟪η, C₀ (P₂ y)⟫_ℂ * ⟪C₀ (Q₂ x), ξ⟫_ℂ)

def StCut3 : Prop :=
  StInvGroup →
  ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (D : RealPlaceData k r Wp Wp) (X : SigData k r), IsDiag D → SqIntG D X →
    ∀ γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ, IsZFrame k r D.z γ →
    (∀ x y x' y' : X.Hs,
      ∫ g : Mt k r, ⟪y, X.σ (th k r γ (Matrix.of g)) x⟫_ℂ * star ⟪y', X.σ (Matrix.of g) x'⟫_ℂ ∂D.μG = 0) →
    ∀ (a₁ b₁ a₂ b₂ : X.Hs) (X₀ : Wp →L[ℂ] Wp) (p : SS k r), D.inSS p →
      Ph D (scalF Wp (mc X a₁ b₁ ∘ th k r γ)) (fun g => mc X a₂ b₂ g • X₀) p = 0

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoWA
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace MatrixSubsetMeasurability

variable {k r : ℕ} {U : Set (Mat k r)}

def SG (_hU : IsClosedSubgroup U) : Type := {x : Mt k r // (Matrix.of x : Mat k r) ∈ U}

def mat {hU : IsClosedSubgroup U} (g : SG hU) : Mat k r := Matrix.of g.1

theorem mat_mem {hU : IsClosedSubgroup U} (g : SG hU) : mat g ∈ U := by
  exact g.2

def mk (hU : IsClosedSubgroup U) (A : Mat k r) (hA : A ∈ U) : SG hU := ⟨Matrix.of.symm A, hA⟩

theorem mat_mk (hU : IsClosedSubgroup U) (A : Mat k r) (hA : A ∈ U) : mat (mk hU A hA) = A := rfl

variable {hU : IsClosedSubgroup U}

instance : One (SG hU) := ⟨mk hU 1 hU.one_mem⟩
instance : Mul (SG hU) := ⟨fun a b => mk hU (mat a * mat b) (hU.mul_mem _ a.2 _ b.2)⟩
instance : Inv (SG hU) := ⟨fun a => mk hU (mat a)⁻¹ (hU.inv_mem _ a.2)⟩

theorem mat_one : mat (1 : SG hU) = 1 := rfl
theorem mat_mul (a b : SG hU) : mat (a * b) = mat a * mat b := rfl
theorem mat_inv (a : SG hU) : mat a⁻¹ = (mat a)⁻¹ := rfl

theorem ext' {a b : SG hU} (h : mat a = mat b) : a = b := by
  exact Subtype.ext (Matrix.of.injective h)

instance : Group (SG hU) :=
  Group.ofLeftAxioms (fun a b c => ext' (Matrix.mul_assoc (mat a) (mat b) (mat c)))
    (fun a => ext' (Matrix.one_mul (mat a)))
    (fun a => ext' (Matrix.nonsing_inv_mul (mat a) (hU.unit _ a.2)))

instance : TopologicalSpace (SG hU) := instTopologicalSpaceSubtype
instance : MeasurableSpace (SG hU) := Subtype.instMeasurableSpace
instance : BorelSpace (SG hU) :=
  inferInstanceAs (BorelSpace ({x : Mt k r | (Matrix.of x : Mat k r) ∈ U} : Set (Mt k r)))

private theorem continuous_matrix_of_Mt : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) :=
  continuous_matrix (fun i j => (continuous_apply j).comp (continuous_apply i))

theorem continuous_mat : Continuous (fun g : SG hU => mat g) := by
  exact continuous_matrix_of_Mt.comp continuous_subtype_val

instance : ContinuousMul (SG hU) := by
  refine ⟨Continuous.subtype_mk ?_ _⟩
  exact (continuous_mat.comp continuous_fst).matrix_mul (continuous_mat.comp continuous_snd)

instance : ContinuousInv (SG hU) := by
  refine ⟨Continuous.subtype_mk ?_ _⟩
  have h : (fun a : SG hU => (mat a)⁻¹) = fun a => (mat a).det⁻¹ • (mat a).adjugate := by
    funext a; rw [Matrix.inv_def, Ring.inverse_eq_inv]
  show Continuous fun a : SG hU => (mat a)⁻¹
  rw [h]
  exact ((continuous_mat.matrix_det).inv₀ fun a => (hU.unit _ a.2).ne_zero).smul continuous_mat.matrix_adjugate

instance : IsTopologicalGroup (SG hU) := {}

theorem measurableSet_U (hU : IsClosedSubgroup U) : MeasurableSet {x : Mt k r | (Matrix.of x : Mat k r) ∈ U} := by
  exact (hU.closed.preimage continuous_matrix_of_Mt).measurableSet

theorem me_val (hU : IsClosedSubgroup U) : MeasurableEmbedding (fun g : SG hU => g.1) := by
  exact MeasurableEmbedding.subtype_coe (measurableSet_U hU)

def nu (hU : IsClosedSubgroup U) (μ : Measure (Mt k r)) : Measure (SG hU) := μ.comap (fun g : SG hU => g.1)

theorem map_nu {μ : Measure (Mt k r)} (hμ : IsHaarOn U μ) : (nu hU μ).map (fun g : SG hU => g.1) = μ := by
  unfold nu
  rw [(me_val hU).map_comap]
  first | rw [Subtype.range_coe_subtype] | rw [Subtype.range_val_subtype] | skip
  have hae : ∀ᵐ x ∂μ, (Matrix.of x : Mat k r) ∈ U := ae_iff.mpr hμ.conc
  exact Measure.restrict_eq_self_of_ae_mem (hae.mono fun x hx => ⟨⟨x, hx⟩, rfl⟩)

theorem nu_left {μ : Measure (Mt k r)} (hμ : IsHaarOn U μ) : (nu hU μ).IsMulLeftInvariant := by
  constructor
  intro g
  have hc : Continuous (lmulM (k := k) (r := r) (mat g)) :=
    (continuous_const.mul continuous_matrix_of_Mt : Continuous fun x : Mt k r => (mat g * Matrix.of x : Mat k r))
  have hm : Measurable (fun x : SG hU => g * x) := by
    refine Measurable.subtype_mk ?_
    exact hc.measurable.comp measurable_subtype_coe
  have hval : (fun g : SG hU => g.1) ∘ (fun x : SG hU => g * x) = lmulM (mat g) ∘ (fun g : SG hU => g.1) := rfl
  have hmap : ((nu hU μ).map (fun x : SG hU => g * x)).map (fun g : SG hU => g.1)
      = (nu hU μ).map (fun g : SG hU => g.1) := by
    rw [Measure.map_map (me_val hU).measurable hm, hval,
      ← Measure.map_map hc.measurable (me_val hU).measurable, map_nu hμ, hμ.left _ (mat_mem g)]
  ext s hs
  have h1 := congrArg (fun m : Measure (Mt k r) => m ((fun g : SG hU => g.1) '' s)) hmap
  rwa [(me_val hU).map_apply, (me_val hU).map_apply,
    Set.preimage_image_eq s (me_val hU).injective] at h1

theorem nu_inv (HI : HaarInv) {μ : Measure (Mt k r)} (hμ : IsHaarOn U μ) : (nu hU μ).IsInvInvariant := by
  have hae : AEMeasurable invM μ := InvGrp.measurable_invM.aemeasurable
  constructor
  ext s hs
  have hset : (fun g : SG hU => g.1) '' (Inv.inv ⁻¹' s) =
      invM ⁻¹' ((fun g : SG hU => g.1) '' s) ∩
      {x : Mt k r | (Matrix.of x : Mat k r) ∈ U} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(@id (SG hU) x)⁻¹, hx, rfl⟩, x.2⟩
    · rintro ⟨⟨x, hx, hxy⟩, hy⟩
      refine ⟨⟨y, hy⟩, ?_, rfl⟩
      have e : (@id (SG hU) ⟨y, hy⟩)⁻¹ = x := by
        apply ext'
        rw [mat_inv]
        show (Matrix.of y : Mat k r)⁻¹ = Matrix.of x.1
        rw [show x.1 = invM y from hxy]
        all_goals rfl
      show (@id (SG hU) ⟨y, hy⟩)⁻¹ ∈ s
      rw [e]
      exact hx
  rw [Measure.inv_def, Measure.map_apply measurable_inv hs]
  simp only [nu]
  rw [(me_val hU).comap_apply, (me_val hU).comap_apply, hset,
    measure_inter_conull (t := {x : Mt k r | (Matrix.of x : Mat k r) ∈ U}) hμ.conc,
    ← Measure.map_apply_of_aemeasurable hae ((me_val hU).measurableSet_image.mpr hs), HI k r U μ hU hμ]

end MatrixSubsetMeasurability

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JPairs
noncomputable section

open Matrix MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ConjugateNormInequalities

theorem stPairs (h : UnitaryGroupStructuralFacts) : StPairs := by
  have h' := h
  unfold UnitaryGroupStructuralFacts ReciprocityTheory.ChartRestriction.DS.Xi.InductiveHeisenbergInputs at h'
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hInt, hLow, -⟩, -⟩ := h'
  intro k r Wp _ _ _ D X _ _ d hd a₁ a₂ u hu v hv
  set a := min a₁ a₂ with ha_def
  set b := AG k r + 1 with hb_def
  have hone : (1 : Mat k r) ∈ GV k r := by
    show (1 : Mat k r)ᴴ * Hpk k r * 1 = Hpk k r
    simp
  have hlow : ∀ x ∈ GV k r, 1 ≤ gN x := fun x hx => hLow k r x hx
  have hb0 : 0 ≤ b := by
    have : 0 ≤ AG k r := by unfold AG; positivity
    linarith
  by_cases hab : b ≤ a
  swap
  · refine ⟨‖u‖ * ‖v‖, fun x hx => ?_⟩
    have h1 : ‖mc X u v x‖ ≤ ‖u‖ * ‖v‖ := by
      calc ‖mc X u v x‖ = ‖⟪v, X.σ x u⟫_ℂ‖ := rfl
        _ ≤ ‖v‖ * ‖X.σ x u‖ := norm_inner_le_norm _ _
        _ = ‖u‖ * ‖v‖ := by rw [X.rep.2.1 x hx u]; ring
    have h2 : 1 ≤ gN x ^ (-(min a₁ a₂ - AG k r - 1)) := by
      apply Real.one_le_rpow (hlow x hx)
      rw [← ha_def]
      linarith
    calc ‖mc X u v x‖ ≤ ‖u‖ * ‖v‖ := h1
      _ = ‖u‖ * ‖v‖ * 1 := by ring
      _ ≤ ‖u‖ * ‖v‖ * gN x ^ (-(min a₁ a₂ - AG k r - 1)) := by gcongr
  obtain ⟨C₁, hC₁⟩ := hu
  obtain ⟨C₂, hC₂⟩ := hv
  have hpos : ∀ x ∈ GV k r, 0 < gN x := fun x hx => lt_of_lt_of_le one_pos (hlow x hx)
  have hC₁0 : 0 ≤ C₁ := by
    have h1 := hC₁ 1 hone
    have h2 := Real.rpow_pos_of_pos (hpos 1 hone) (-a₁)
    by_contra hneg'
    have hneg := lt_of_not_ge hneg'
    have : C₁ * gN (1 : Mat k r) ^ (-a₁) < 0 := mul_neg_of_neg_of_pos hneg h2
    linarith [norm_nonneg (mc X u X.w 1)]
  have hC₂0 : 0 ≤ C₂ := by
    have h1 := hC₂ 1 hone
    have h2 := Real.rpow_pos_of_pos (hpos 1 hone) (-a₂)
    by_contra hneg'
    have hneg := lt_of_not_ge hneg'
    have : C₂ * gN (1 : Mat k r) ^ (-a₂) < 0 := mul_neg_of_neg_of_pos hneg h2
    linarith [norm_nonneg (mc X v X.w 1)]
  set c := gN (Hpk k r) ^ 2 with hc_def
  have hc : 0 < c := by
    have h1 : gN (1 : Mat k r) ≤ gN (Hpk k r) * gN (Hpk k r) := by
      have := gN_mul_le (Hpk k r) (Hpk k r)
      rwa [Hpk_sq] at this
    have h2 := hlow 1 hone
    rw [hc_def]
    nlinarith
  have hmeas : Measurable (fun g : Mt k r => gN (Matrix.of g)) := by
    unfold gN
    fun_prop
  have hae : ∀ᵐ g ∂D.μG, (Matrix.of g : Mat k r) ∈ GV k r := by
    rw [ae_iff]
    exact D.haarG.conc
  have hAB : AB k r ≤ b := AB_le_AG k r
  have hfin := hInt k r D.μG b D.haarG hAB
  have hI : Integrable (fun g : Mt k r => gN (Matrix.of g) ^ (-b)) D.μG := by
    refine ⟨(hmeas.pow_const _).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal]
    · exact hfin
    · exact Filter.Eventually.of_forall fun g => Real.rpow_nonneg (by unfold gN; positivity) _
  set I := ∫ g : Mt k r, gN (Matrix.of g) ^ (-b) ∂D.μG with hI_def
  refine ⟨d * (C₁ * C₂ * I * (c⁻¹) ^ (-(a - b))), fun x hx => ?_⟩
  have hd0 : 0 < d := hd.1
  obtain ⟨-, hEq⟩ := hd.2 (X.σ x u) X.w v X.w
  have hww : ⟪X.w, X.w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, X.w_norm]
    simp
  rw [hww, mul_one] at hEq
  set F : Mt k r → ℂ := fun g => mc X (X.σ x u) X.w (Matrix.of g) * star (mc X v X.w (Matrix.of g)) with hF_def
  have hmc : mc X u v x = (d : ℂ) * ∫ g, F g ∂D.μG := by
    rw [hEq]
    have : (d : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
    change ⟪v, X.σ x u⟫_ℂ = (d : ℂ) * (⟪v, X.σ x u⟫_ℂ / (d : ℂ))
    field_simp
  set G : Mt k r → ℝ := fun g => C₁ * C₂ * (gN x * c⁻¹) ^ (-(a - b)) * gN (Matrix.of g) ^ (-b) with hG_def
  have hGi : Integrable G D.μG := hI.const_mul _
  have hpt : ∀ᵐ g ∂D.μG, ‖F g‖ ≤ G g := by
    filter_upwards [hae] with g hg
    have hgx : Matrix.of g * x ∈ GV k r := GV_mul k r hg hx
    have hFg : ‖F g‖ = ‖mc X u X.w (Matrix.of g * x)‖ * ‖mc X v X.w (Matrix.of g)‖ := by
      rw [hF_def]
      simp only [norm_mul, norm_star]
      congr 1
      show ‖⟪X.w, X.σ (Matrix.of g) (X.σ x u)⟫_ℂ‖ = ‖⟪X.w, X.σ (Matrix.of g * x) u⟫_ℂ‖
      rw [X.rep.1.2 _ hg _ hx]
      rfl
    have hA1 := hlow _ hgx
    have hB1 := hlow _ hg
    have e1 : ‖mc X u X.w (Matrix.of g * x)‖ ≤ C₁ * gN (Matrix.of g * x) ^ (-a) := by
      refine (hC₁ _ hgx).trans ?_
      gcongr
      exact min_le_left a₁ a₂
    have e2 : ‖mc X v X.w (Matrix.of g)‖ ≤ C₂ * gN (Matrix.of g) ^ (-a) := by
      refine (hC₂ _ hg).trans ?_
      gcongr
      exact min_le_right a₁ a₂
    have key := real_key hA1 hB1 (hpos x hx) hc hb0 hab (gN_le_mul hg x)
    rw [hFg, hG_def]
    calc ‖mc X u X.w (Matrix.of g * x)‖ * ‖mc X v X.w (Matrix.of g)‖
        ≤ (C₁ * gN (Matrix.of g * x) ^ (-a)) * (C₂ * gN (Matrix.of g) ^ (-a)) :=
          mul_le_mul e1 e2 (norm_nonneg _) (mul_nonneg hC₁0 (Real.rpow_nonneg (hpos _ hgx).le _))
      _ = C₁ * C₂ * (gN (Matrix.of g * x) ^ (-a) * gN (Matrix.of g) ^ (-a)) := by ring
      _ ≤ C₁ * C₂ * ((gN x * c⁻¹) ^ (-(a - b)) * gN (Matrix.of g) ^ (-b)) := by
          gcongr
      _ = C₁ * C₂ * (gN x * c⁻¹) ^ (-(a - b)) * gN (Matrix.of g) ^ (-b) := by ring
  have hbound : ‖∫ g, F g ∂D.μG‖ ≤ ∫ g, G g ∂D.μG :=
    (norm_integral_le_integral_norm _).trans
      (integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hGi hpt)
  have hGint : ∫ g, G g ∂D.μG = C₁ * C₂ * (gN x * c⁻¹) ^ (-(a - b)) * I := by
    rw [hG_def, integral_const_mul]
  have hsplit : (gN x * c⁻¹) ^ (-(a - b)) = gN x ^ (-(a - b)) * (c⁻¹) ^ (-(a - b)) :=
    Real.mul_rpow (hpos x hx).le (inv_nonneg.mpr hc.le)
  have hexp : -(min a₁ a₂ - AG k r - 1) = -(a - b) := by
    rw [ha_def, hb_def]; ring
  rw [hmc, norm_mul, hexp]
  have hdn : ‖(d : ℂ)‖ = d := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hd0]
  rw [hdn]
  calc d * ‖∫ g, F g ∂D.μG‖ ≤ d * (C₁ * C₂ * (gN x * c⁻¹) ^ (-(a - b)) * I) := by
        rw [← hGint]; exact mul_le_mul_of_nonneg_left hbound hd0.le
    _ = d * (C₁ * C₂ * I * (c⁻¹) ^ (-(a - b))) * gN x ^ (-(a - b)) := by
        rw [hsplit]; ring

end ReciprocityTheory.ChartRestriction.DS.Mult1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JHaarSFA
open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.HaarSigmaFiniteUniqueness

section Grp

variable {G : Type*} [MeasurableSpace G] [Group G] [MeasurableMul₂ G] [MeasurableInv G]

theorem eq_smul_of_sigmaFinite (μ ν : Measure G) [SigmaFinite μ] [SigmaFinite ν]
    [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant] (hμ : μ ≠ 0) (hν : ν ≠ 0) :
    ∃ c : ℝ≥0, c ≠ 0 ∧ μ = c • ν := by
  obtain ⟨n, hn⟩ : ∃ n, ν (spanningSets (μ + ν) n) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hν
    have : ν Set.univ = 0 := by
      rw [← iUnion_spanningSets (μ + ν)]
      exact measure_iUnion_null h
    exact Measure.measure_univ_eq_zero.mp this
  have hS := measurableSet_spanningSets (μ + ν) n
  have hfin := measure_spanningSets_lt_top (μ + ν) n
  rw [Measure.add_apply] at hfin
  have hνf : ν (spanningSets (μ + ν) n) ≠ ∞ := (lt_of_le_of_lt le_add_self hfin).ne
  have hμf : μ (spanningSets (μ + ν) n) ≠ ∞ := (lt_of_le_of_lt le_self_add hfin).ne
  have heq : μ = (μ (spanningSets (μ + ν) n) / ν (spanningSets (μ + ν) n)) • ν := by
    first
    | exact measure_eq_div_smul μ ν (spanningSets (μ + ν) n) hn hνf
    | exact measure_eq_div_smul μ ν hS hn hνf
    | exact measure_eq_div_smul μ ν (spanningSets (μ + ν) n) hS hn hνf
    | (ext t ht
       have key := measure_mul_measure_eq μ ν (spanningSets (μ + ν) n) t hn hνf ht
       rw [Measure.smul_apply, smul_eq_mul, ENNReal.div_eq_inv_mul, mul_assoc, key, ← mul_assoc,
         ENNReal.inv_mul_cancel hn hνf, one_mul])
    | (ext t ht
       have key := measure_mul_measure_eq μ ν (spanningSets (μ + ν) n) t hn hνf
       rw [Measure.smul_apply, smul_eq_mul, ENNReal.div_eq_inv_mul, mul_assoc, key, ← mul_assoc,
         ENNReal.inv_mul_cancel hn hνf, one_mul])
    | (ext t ht
       have key := measure_mul_measure_eq μ ν (spanningSets (μ + ν) n) t hS ht hn hνf
       rw [Measure.smul_apply, smul_eq_mul, ENNReal.div_eq_inv_mul, mul_assoc, key, ← mul_assoc,
         ENNReal.inv_mul_cancel hn hνf, one_mul])
  have hμ0 : μ (spanningSets (μ + ν) n) ≠ 0 := by
    intro h0
    apply hμ
    rw [heq, h0, ENNReal.zero_div, zero_smul]
  refine ⟨(μ (spanningSets (μ + ν) n) / ν (spanningSets (μ + ν) n)).toNNReal, ?_, ?_⟩
  · intro h
    rw [ENNReal.toNNReal_eq_zero_iff, ENNReal.div_eq_zero_iff] at h
    rcases h with (h | h) | h
    · exact hμ0 h
    · exact hνf h
    · exact ENNReal.div_ne_top hμf hn h
  · rw [ENNReal.smul_def, ENNReal.coe_toNNReal (ENNReal.div_ne_top hμf hn)]
    exact heq

end Grp

section Mat

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

def Aset (U : Set (Mat k r)) : Set (Mt k r) := {x | Matrix.of x ∈ U}

variable {U : Set (Mat k r)}

private theorem continuous_matrix_of_Mt : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) :=
  continuous_matrix (fun i j => (continuous_apply j).comp (continuous_apply i))

theorem isClosed_Aset (hU : IsClosedSubgroup U) : IsClosed (Aset U) := by
  exact hU.closed.preimage continuous_matrix_of_Mt

theorem measurableSet_Aset (hU : IsClosedSubgroup U) : MeasurableSet (Aset U) := by
  exact (isClosed_Aset hU).measurableSet

def toM (a : Aset U) : Mat k r := Matrix.of a.1

theorem toM_inj {a b : Aset U} (h : toM a = toM b) : a = b := by
  exact Subtype.ext (Matrix.of.injective h)

variable [hU : Fact (IsClosedSubgroup U)]

instance : Mul (Aset U) := ⟨fun a b => ⟨(toM a * toM b : Mat k r), hU.out.mul_mem _ a.2 _ b.2⟩⟩
instance : One (Aset U) := ⟨⟨(1 : Mat k r), hU.out.one_mem⟩⟩
instance : Inv (Aset U) := ⟨fun a => ⟨((toM a)⁻¹ : Mat k r), hU.out.inv_mem _ a.2⟩⟩

theorem toM_mul (a b : Aset U) : toM (a * b) = toM a * toM b := rfl
theorem toM_one : toM (1 : Aset U) = 1 := rfl
theorem toM_inv (a : Aset U) : toM a⁻¹ = (toM a)⁻¹ := rfl

instance : Group (Aset U) where
  mul_assoc a b c := toM_inj (by simp only [toM_mul]; exact Matrix.mul_assoc _ _ _)
  one_mul a := toM_inj (by simp only [toM_mul, toM_one]; exact Matrix.one_mul _)
  mul_one a := toM_inj (by simp only [toM_mul, toM_one]; exact Matrix.mul_one _)
  inv_mul_cancel a := toM_inj (by
    simp only [toM_mul, toM_one, toM_inv]
    exact Matrix.nonsing_inv_mul _ (hU.out.unit _ a.2))

theorem continuous_toM : Continuous (toM : Aset U → Mat k r) := by
  exact continuous_matrix_of_Mt.comp continuous_subtype_val

theorem continuous_mulA : Continuous fun p : Aset U × Aset U => p.1 * p.2 := by
  refine Continuous.subtype_mk ?_ _
  show Continuous fun p : Aset U × Aset U => (toM p.1 * toM p.2 : Mat k r)
  exact (continuous_toM.comp continuous_fst).mul (continuous_toM.comp continuous_snd)

theorem continuous_invA : Continuous fun a : Aset U => a⁻¹ := by
  refine Continuous.subtype_mk ?_ _
  have h : (fun a : Aset U => (toM a)⁻¹) = fun a => (toM a).det⁻¹ • (toM a).adjugate := by
    funext a; rw [Matrix.inv_def, Ring.inverse_eq_inv]
  show Continuous fun a : Aset U => ((toM a)⁻¹ : Mat k r)
  rw [h]
  exact ((continuous_toM.matrix_det).inv₀ fun a => (hU.out.unit _ a.2).ne_zero).smul continuous_toM.matrix_adjugate

instance : MeasurableMul₂ (Aset U) := ⟨continuous_mulA.measurable⟩
instance : MeasurableInv (Aset U) := ⟨continuous_invA.measurable⟩

end Mat

section Transfer

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ} {U : Set (Mat k r)} [hU : Fact (IsClosedSubgroup U)]

theorem mEmb : MeasurableEmbedding (Subtype.val : Aset U → Mt k r) := by
  exact MeasurableEmbedding.subtype_coe (measurableSet_Aset hU.out)

theorem map_comap_val (μ : Measure (Mt k r)) (hc : μ (Aset U)ᶜ = 0) :
    (μ.comap (Subtype.val : Aset U → Mt k r)).map Subtype.val = μ := by
  rw [(mEmb (U := U)).map_comap μ]
  first | rw [Subtype.range_coe] | rw [Subtype.range_val] | skip
  exact Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hc)

theorem sigmaFinite_comap (μ : Measure (Mt k r)) [SigmaFinite μ] :
    SigmaFinite (μ.comap (Subtype.val : Aset U → Mt k r)) := by
  refine SigmaFinite.of_map _ (mEmb (U := U)).measurable.aemeasurable ?_
  rw [(mEmb (U := U)).map_comap μ]
  infer_instance

theorem continuous_lmulM (a : Mat k r) : Continuous (lmulM (k := k) (r := r) a) := by
  exact (continuous_const.mul continuous_matrix_of_Mt : Continuous fun x : Mt k r => (a * Matrix.of x : Mat k r))

theorem isMulLeftInvariant_comap (μ : Measure (Mt k r)) (hc : μ (Aset U)ᶜ = 0)
    (hl : ∀ a ∈ U, μ.map (lmulM a) = μ) :
    (μ.comap (Subtype.val : Aset U → Mt k r)).IsMulLeftInvariant := by
  constructor
  intro g
  have hm : Measurable (fun x : Aset U => g * x) := by
    refine Measurable.subtype_mk ?_
    exact (continuous_lmulM (toM g)).measurable.comp measurable_subtype_coe
  have hval : Subtype.val ∘ (fun x : Aset U => g * x) = lmulM (toM g) ∘ Subtype.val := rfl
  have hmap : ((μ.comap (Subtype.val : Aset U → Mt k r)).map (fun x : Aset U => g * x)).map Subtype.val
      = (μ.comap (Subtype.val : Aset U → Mt k r)).map Subtype.val := by
    rw [Measure.map_map (mEmb (U := U)).measurable hm, hval,
      ← Measure.map_map (continuous_lmulM (toM g)).measurable (mEmb (U := U)).measurable,
      map_comap_val μ hc, hl (toM g) g.2]
  ext s hs
  have h1 := congrArg (fun m : Measure (Mt k r) => m (Subtype.val '' s)) hmap
  rwa [(mEmb (U := U)).map_apply, (mEmb (U := U)).map_apply,
    Set.preimage_image_eq _ Subtype.val_injective] at h1

end Transfer

end ReciprocityTheory.ChartRestriction.DS.Mult1.HaarSigmaFiniteUniqueness

end
end
