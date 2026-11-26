module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeConstantEqProdCovolumes
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalisedMeasureEqProdBesselRootMeasures
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealOrbitalIntegralHsNormEqProdLocal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalAmplitudeWittLiftEqQuotientIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalisedLiftAmplitudeEqCovolumeMulLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsQuotientMeasureUnipotentStabilisers
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsQuotientMeasureUnipotentStabilisers
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.QuotExist

theorem bruhat_left (G H : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H]
    [MeasurableSpace H] [BorelSpace H] (ν : Measure H)
    [ν.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts ν] (hν : ν ≠ 0) (j : H →* G)
    (hj : Topology.IsClosedEmbedding j) :
    ∃ b : G → ℝ≥0∞, Measurable b ∧ ∀ g, ∫⁻ h, b ((j h)⁻¹ * g) ∂ν = 1 := by
  classical
  let K : ℕ → Set G := compactCovering G
  have hK : ∀ n, IsCompact (K n) := isCompact_compactCovering G
  have hKm : ∀ n, MeasurableSet (K n) := fun n => (hK n).isClosed.measurableSet
  let φ : ℕ → G → ℝ≥0∞ := fun n => (K n).indicator 1
  have hφ : ∀ n, Measurable (φ n) := fun n => measurable_one.indicator (hKm n)
  have hjm : Measurable j := hj.continuous.measurable
  let F : ℕ → G → ℝ≥0∞ := fun n g => ∫⁻ h, φ n ((j h)⁻¹ * g) ∂ν
  have hFm : ∀ n, Measurable (F n) := by
    intro n
    have : Measurable (fun p : G × H => φ n ((j p.2)⁻¹ * p.1)) :=
      (hφ n).comp ((hjm.comp measurable_snd).inv.mul measurable_fst)
    exact this.lintegral_prod_right'
  have key : ∀ n k g, F n ((j k)⁻¹ * g) = F n g := by
    intro n k g
    have := lintegral_mul_left_eq_self (μ := ν) (fun h => φ n ((j h)⁻¹ * g)) k
    simpa only [F, map_mul, _root_.mul_inv_rev, mul_assoc] using this
  have hpre : ∀ n g, MeasurableSet ((fun h => (j h)⁻¹ * g) ⁻¹' K n) := fun n g =>
    (hjm.inv.mul_const g) (hKm n)
  have hFeq : ∀ n g, F n g = ν ((fun h => (j h)⁻¹ * g) ⁻¹' K n) := by
    intro n g
    rw [← lintegral_indicator_one (hpre n g)]
    rfl
  have hFfin : ∀ n g, F n g ≠ ⊤ := by
    intro n g
    rw [hFeq]
    have hc : Topology.IsClosedEmbedding (fun h => (j h)⁻¹ * g) :=
      (Homeomorph.mulRight g).isClosedEmbedding.comp ((Homeomorph.inv G).isClosedEmbedding.comp hj)
    exact (hc.isCompact_preimage (hK n)).measure_lt_top.ne
  have hFpos : ∀ g, ∃ n, F n g ≠ 0 := by
    intro g
    by_contra hcon
    push Not at hcon
    have h0 : ν (⋃ n, (fun h => (j h)⁻¹ * g) ⁻¹' K n) = 0 :=
      measure_iUnion_null fun n => by rw [← hFeq]; exact hcon n
    rw [← Set.preimage_iUnion, iUnion_compactCovering, Set.preimage_univ] at h0
    exact hν (Measure.measure_univ_eq_zero.1 h0)
  obtain ⟨N, hN, hNinv, hNm⟩ : ∃ N : G → ℕ, (∀ g, F (N g) g ≠ 0) ∧ (∀ k g, N ((j k)⁻¹ * g) = N g) ∧
      Measurable (fun g => φ (N g) g * (F (N g) g)⁻¹) := by
    refine ⟨fun g => Nat.find (hFpos g), fun g => Nat.find_spec (hFpos g), ?_, ?_⟩
    · intro k g
      apply Nat.find_congr'
      intro n
      rw [key]
    · convert Measurable.find (p := fun n g => F n g ≠ 0) (f := fun n g => φ n g * (F n g)⁻¹)
        (fun n => (hφ n).mul (hFm n).inv)
        (fun n => ((hFm n) (measurableSet_singleton 0)).compl) hFpos using 4
  refine ⟨fun g => φ (N g) g * (F (N g) g)⁻¹, hNm, fun g => ?_⟩
  simp only [hNinv, key]
  have hm : Measurable fun h => φ (N g) ((j h)⁻¹ * g) := (hφ _).comp (hjm.inv.mul_const g)
  rw [lintegral_mul_const _ hm]
  exact ENNReal.mul_inv_cancel (hN g) (hFfin _ g)

theorem cutoff_left {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (R : Subgroup G) (μ : Measure G)
    [SigmaFinite μ] (hR : IsClosed (R : Set G)) (h0 : μ ≠ 0) (hc : μ (R : Set G)ᶜ = 0)
    (hi : ∀ s ∈ R, μ.map (fun x => s * x) = μ) :
    ∃ b : G → ℝ≥0∞, Measurable b ∧ ∀ g, ∫⁻ s, b (s⁻¹ * g) ∂μ = 1 := by
  have hce : Topology.IsClosedEmbedding R.subtype := hR.isClosedEmbedding_subtypeVal
  have hφ : MeasurableEmbedding R.subtype := hce.measurableEmbedding
  haveI : LocallyCompactSpace R := hce.locallyCompactSpace
  haveI : SecondCountableTopology R := hce.isEmbedding.secondCountableTopology
  have h2 : (μ.comap R.subtype).map R.subtype = μ := by
    rw [hφ.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    have : Set.range R.subtype = (R : Set G) := Subtype.range_coe
    rw [this]
    exact hc
  set ν : Measure R := μ.comap R.subtype with hν
  haveI : SigmaFinite ν := SigmaFinite.of_map _ hφ.measurable.aemeasurable (by rwa [h2])
  haveI : ν.IsMulLeftInvariant := ⟨fun g => by
    apply hφ.map_injective
    have hm : Measurable fun x : G => (g : G) * x := measurable_const_mul _
    rw [Measure.map_map hφ.measurable (measurable_const_mul g), h2]
    conv_rhs => rw [← hi g g.2, ← h2, Measure.map_map hm hφ.measurable]
    rfl⟩
  have hν0 : ν ≠ 0 := fun h => h0 (by rw [← h2, h, Measure.map_zero])
  haveI : ν.IsHaarMeasure := GlobalTheory.SnMass.ProdQuot.isHaarMeasure_of_sigmaFinite ν hν0
  obtain ⟨b, hb, h1⟩ := bruhat_left G R ν hν0 R.subtype hce
  refine ⟨b, hb, fun g => ?_⟩
  rw [← h2, hφ.lintegral_map]
  exact h1 g

theorem weil_of_cutoff {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (μG μ : Measure G) [SigmaFinite μG] [μG.IsMulLeftInvariant] [SigmaFinite μ] {b : G → ℝ≥0∞}
    (hb : Measurable b) (h2 : ∀ g, ∫⁻ s, b (s⁻¹ * g) ∂μ = 1) (f : G → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂μG = ∫⁻ x, ∫⁻ s, f (s * x) ∂μ ∂(μG.withDensity b) := by
  have hinv : Measurable (Inv.inv : G → G) := measurable_inv
  have hf2 : Measurable fun p : G × G => f (p.2 * p.1) := hf.comp (measurable_snd.mul measurable_fst)
  rw [lintegral_withDensity_eq_lintegral_mul _ hb hf2.lintegral_prod_right']
  calc ∫⁻ x, f x ∂μG = ∫⁻ x, ∫⁻ s, b (s⁻¹ * x) * f x ∂μ ∂μG := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_mul_const (f := fun s => b (s⁻¹ * x)) _ (hb.comp (hinv.mul_const x)), h2, one_mul]
    _ = ∫⁻ s, ∫⁻ x, b (s⁻¹ * x) * f x ∂μG ∂μ :=
        lintegral_lintegral_swap ((hb.comp (measurable_snd.inv.mul measurable_fst)).mul
          (hf.comp measurable_fst)).aemeasurable
    _ = ∫⁻ s, ∫⁻ x, b x * f (s * x) ∂μG ∂μ := by
        refine lintegral_congr fun s => ?_
        rw [← lintegral_mul_left_eq_self _ s]
        simp
    _ = ∫⁻ x, ∫⁻ s, b x * f (s * x) ∂μ ∂μG :=
        (lintegral_lintegral_swap ((hb.comp measurable_fst).mul hf2).aemeasurable).symm
    _ = _ := by
        refine lintegral_congr fun x => ?_
        rw [lintegral_const_mul (f := fun s => f (s * x)) _ (hf.comp (measurable_mul_const x))]
        rfl

section Sub

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ)

theorem spanLt_mono {a b : ℕ} (h : a ≤ b) : spanLt e a ≤ spanLt e b :=
  Submodule.span_mono (Set.image_mono fun c (hc : c.1 < a) => lt_of_lt_of_le hc h)

def Pres (M : Matrix (Fin n) (Fin n) ℂ) : Prop := ∀ a : ℕ, ∀ v ∈ spanLt e a, M *ᵥ v ∈ spanLt e a

theorem pres_of (M : Matrix (Fin n) (Fin n) ℂ) (h : ∀ b : Fin r, M *ᵥ e b ∈ spanLt e (b.1 + 1)) : Pres e M := by
  intro a v hv
  have : spanLt e a ≤ (spanLt e a).comap (Matrix.mulVecLin M) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨c, hc, rfl⟩
    show Matrix.mulVecLin M (e c) ∈ spanLt e a
    rw [Matrix.mulVecLin_apply]
    exact spanLt_mono e (Nat.succ_le_of_lt hc) (h c)
  have h2 := this hv
  rw [Submodule.mem_comap, Matrix.mulVecLin_apply] at h2
  exact h2

def Good (M : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ((∀ a : Fin r, M *ᵥ e a ∈ spanLt e a.1) ∧ M *ᵥ z ∈ spanLt e r) ∧
    ∀ y, (∀ a, hJ ε (e a) y = 0) → M *ᵥ y ∈ spanLt e r

variable {ε e z}

theorem Good.pres {M : Matrix (Fin n) (Fin n) ℂ} (hM : Good ε e z M) : Pres e M :=
  pres_of e M fun b => spanLt_mono e (Nat.le_succ _) (hM.1.1 b)

theorem Good.pres_mul {P M : Matrix (Fin n) (Fin n) ℂ} (hP : Pres e P) (hM : Good ε e z M) :
    Good ε e z (P * M) := by
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩ <;> rw [← Matrix.mulVec_mulVec]
  · exact hP _ _ (hM.1.1 a)
  · exact hP _ _ hM.1.2
  · exact hP _ _ (hM.2 y hy)

theorem Good.add {M M' : Matrix (Fin n) (Fin n) ℂ} (hM : Good ε e z M) (hM' : Good ε e z M') :
    Good ε e z (M + M') := by
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩ <;> rw [Matrix.add_mulVec]
  · exact add_mem (hM.1.1 a) (hM'.1.1 a)
  · exact add_mem hM.1.2 hM'.1.2
  · exact add_mem (hM.2 y hy) (hM'.2 y hy)

theorem Good.neg {M : Matrix (Fin n) (Fin n) ℂ} (hM : Good ε e z M) : Good ε e z (-M) := by
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩ <;> rw [Matrix.neg_mulVec]
  · exact neg_mem (hM.1.1 a)
  · exact neg_mem hM.1.2
  · exact neg_mem (hM.2 y hy)

theorem good_zero : Good ε e z (0 : Matrix (Fin n) (Fin n) ℂ) := by
  refine ⟨⟨fun a => ?_, ?_⟩, fun y _ => ?_⟩ <;> rw [Matrix.zero_mulVec] <;> exact zero_mem _

theorem pres_of_good {g : Matrix (Fin n) (Fin n) ℂ} (h : Good ε e z (g - 1)) : Pres e g := by
  refine pres_of e g fun b => ?_
  have e1 : g *ᵥ e b = (g - 1) *ᵥ e b + e b := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_add_cancel]
  rw [e1]
  exact add_mem (spanLt_mono e (Nat.le_succ _) (h.1.1 b)) (Submodule.subset_span ⟨b, Nat.lt_succ_self _, rfl⟩)

theorem pres_inv {g g' : Matrix (Fin n) (Fin n) ℂ} (h1 : g' * g = 1) (hP : Pres e g) : Pres e g' := by
  intro a v hv
  let f : spanLt e a →ₗ[ℂ] spanLt e a := (Matrix.mulVecLin g).restrict (fun x hx => hP a x hx)
  have hf : ∀ w : spanLt e a, ((f w : spanLt e a) : Fin n → ℂ) = g *ᵥ (w : Fin n → ℂ) := fun w => rfl
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have := congrArg (fun w : spanLt e a => g' *ᵥ (w : Fin n → ℂ)) hxy
    simp only [hf, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at this
    exact this
  obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective.1 hinj) ⟨v, hv⟩
  have : g' *ᵥ v = w := by
    have := congrArg (fun w : spanLt e a => g' *ᵥ (w : Fin n → ℂ)) hw
    simp only [hf, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at this
    exact this.symm
  rw [this]
  exact w.2

theorem Good.inv {g g' : Matrix (Fin n) (Fin n) ℂ} (h : Good ε e z (g - 1)) (h1 : g' * g = 1) :
    Good ε e z (g' - 1) := by
  have e1 : g' - 1 = -(g' * (g - 1)) := by rw [Matrix.mul_sub, h1, Matrix.mul_one, neg_sub]
  rw [e1]
  exact (Good.pres_mul (pres_inv h1 (pres_of_good h)) h).neg

theorem Good.mul {g g' : Matrix (Fin n) (Fin n) ℂ} (h : Good ε e z (g - 1)) (h' : Good ε e z (g' - 1)) :
    Good ε e z (g * g' - 1) := by
  have e1 : g * g' - 1 = (g - 1) * (g' - 1) + (g - 1) + (g' - 1) := by noncomm_ring
  rw [e1]
  exact ((Good.pres_mul h.pres h').add h).add h'

variable (ε e z)

def nSub : Subgroup (Formalism.REAL.UJ ε) where
  carrier := NLoc ε e z
  one_mem' := by
    show Good ε e z (uMat (1 : Formalism.REAL.UJ ε) - 1)
    have : uMat (1 : Formalism.REAL.UJ ε) - 1 = 0 := sub_self _
    rw [this]
    exact good_zero
  mul_mem' := fun {x y} hx hy => Good.mul hx hy
  inv_mem' := fun {x} hx => Good.inv hx (Units.inv_mul (x : (Matrix (Fin n) (Fin n) ℂ)ˣ))

theorem isClosed_nLoc : IsClosed (NLoc ε e z) := by
  have hW : ∀ a, IsClosed ((spanLt e a : Set (Fin n → ℂ))) := fun a => Submodule.closed_of_finiteDimensional _
  have hc : ∀ (v : Fin n → ℂ) (a : ℕ), IsClosed {M : Matrix (Fin n) (Fin n) ℂ | (M - 1) *ᵥ v ∈ spanLt e a} :=
    fun v a => (hW a).preimage ((continuous_id.sub continuous_const).matrix_mulVec continuous_const)
  have hM : IsClosed {M : Matrix (Fin n) (Fin n) ℂ | InN ε e z M} := by
    simp only [InN, InS, Set.setOf_and, Set.setOf_forall]
    exact ((isClosed_iInter fun a => hc _ _).inter (hc _ _)).inter
      (isClosed_iInter fun y => isClosed_iInter fun _ => hc _ _)
  exact hM.preimage (Units.continuous_val.comp continuous_subtype_val)

variable (z' : Fin n → ℂ) (γ : Formalism.REAL.UJ ε)

def stSub : Subgroup (Formalism.REAL.UJ ε) where
  carrier := StSet (NLoc ε e z) (NLoc ε e z') γ
  one_mem' := ⟨(nSub ε e z).one_mem, by
    have : γ⁻¹ * 1 * γ = 1 := by group
    rw [this]; exact (nSub ε e z').one_mem⟩
  mul_mem' := fun {x y} hx hy => ⟨(nSub ε e z).mul_mem hx.1 hy.1, by
    have : γ⁻¹ * (x * y) * γ = (γ⁻¹ * x * γ) * (γ⁻¹ * y * γ) := by group
    rw [this]; exact (nSub ε e z').mul_mem hx.2 hy.2⟩
  inv_mem' := fun {x} hx => ⟨(nSub ε e z).inv_mem hx.1, by
    have : γ⁻¹ * x⁻¹ * γ = (γ⁻¹ * x * γ)⁻¹ := by group
    rw [this]; exact (nSub ε e z').inv_mem hx.2⟩

theorem isClosed_stSub : IsClosed (stSub ε e z z' γ : Set (Formalism.REAL.UJ ε)) := by
  have h1 : (stSub ε e z z' γ : Set (Formalism.REAL.UJ ε)) =
      NLoc ε e z ∩ (fun y => γ⁻¹ * y * γ) ⁻¹' NLoc ε e z' := rfl
  have h2 : Continuous (fun y : Formalism.REAL.UJ ε => γ⁻¹ * y * γ) :=
    (continuous_mul_const γ).comp (continuous_const_mul γ⁻¹)
  rw [h1]
  exact (isClosed_nLoc ε e z).inter ((isClosed_nLoc ε e z').preimage h2)

end Sub

theorem quot_exists : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (μl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))), (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (γ v)) (μl v)) → (∀ v, ∃ νv, Formalism.L2.SG.RealObj.IsQuotLoc (μl v) νv) ∧ ∃ ν, IsQuotMeasS X.B.I (Measure.pi μl) ν := by
  intro D X u u' γ μl hμ
  have hloc : ∀ v, ∃ b : Formalism.REAL.UJ (X.B.I.ε v) → ℝ≥0∞, Measurable b ∧
      ∀ g, ∫⁻ s, b (s⁻¹ * g) ∂(μl v) = 1 := by
    intro v
    haveI := (hμ v).1
    exact cutoff_left (stSub (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))
      (rv X.B.I v (X.zR u')) (γ v)) (μl v) (isClosed_stSub _ _ _ _ _) (hμ v).2.1 (hμ v).2.2.1
      (fun s hs => (hμ v).2.2.2 s hs)
  choose b hb h1 using hloc
  haveI : ∀ v, SigmaFinite (μl v) := fun v => (hμ v).1
  refine ⟨fun v => ⟨(Formalism.REAL.muG _).withDensity (b v), fun f hf => weil_of_cutoff _ _ (hb v) (h1 v) f hf⟩,
    (Formalism.L2.SG.ProjRows.muInf X.B.I).withDensity (fun x => ∏ v, b v (x v)),
    fun f hf => weil_of_cutoff _ _ ?_ ?_ f hf⟩
  · exact Finset.measurable_prod _ fun v _ => (hb v).comp (measurable_pi_apply v)
  · intro g
    have := GlobalTheory.SnMass.Push.lintegral_fintype_prod (μ := μl) (fun v s => b v (s⁻¹ * g v))
      fun v => (hb v).comp (measurable_inv.mul_const _)
    simp only [Pi.mul_apply, Pi.inv_apply]
    rw [this]
    simp [h1]

end GlobalTheory.QuotExist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsQuotientMeasureUnipotentStabilisersStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotient_measure_unipotent_stabilisers : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (μl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))), (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (γ v)) (μl v)) → (∀ v, ∃ νv, Formalism.L2.SG.RealObj.IsQuotLoc (μl v) νv) ∧ ∃ ν, IsQuotMeasS X.B.I (Measure.pi μl) ν := by
  first | exact @GlobalTheory.QuotExist.quot_exists | exact GlobalTheory.QuotExist.quot_exists | (intros; apply GlobalTheory.QuotExist.quot_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalisedLiftAmplitudeEqCovolumeMulLocal
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.AmpLift.amp_lift : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (u u' : D.what₂.Word) (s : TT Y u u') (x : Point D.host.E (D.R.rS + 1) × Measure X.B.I.Ginf × Set X.B.I.Ginf), s.relevant → s.G ≠ 0 → s.toTerm.atPt x.1 → Formalism.L2.SG.VolPin.IsPinnedR s x.1 x.2.1 → IsFundR s x.2.2 → (∀ v, ∀ r ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v), ∀ y, Formalism.L2.SG.TermOp.rk1 (X.Wloc u v (r * y)) (X.Wloc u' v ((s.pt.1 v)⁻¹ * (r * y))) = Formalism.L2.SG.TermOp.rk1 (X.Wloc u v y) (X.Wloc u' v ((s.pt.1 v)⁻¹ * y))) → ∃ μl νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)), (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v)) (μl v)) ∧ (∀ v, Formalism.L2.SG.RealObj.IsQuotLoc (μl v) (νl v)) ∧ (∀ τ, ∃ p, IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) p (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) ((μl (vOf X τ)).map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * (s.pt.1 (vOf X τ))))))) ∧ hsNormSq (Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s) = (Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2) ^ 2 * (x.2.1 x.2.2).toReal ^ 2 * ∏ v, hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u' v) (s.pt.1 v)) := by
  intro D X Y θ C u u' s x hrel _hG _hat hpin hfund hinv
  obtain ⟨μl, hμeq, hHaar, hHR, hroot⟩ := GlobalTheory.T.normalisedMeasure_eq_prod_besselRootMeasures D X Y θ C u u' s x.1 x.2.1 hpin
  obtain ⟨hq, ν, hν⟩ := GlobalTheory.T.exists_quotient_measure_unipotent_stabilisers D X u u' s.pt.1 μl hHaar
  choose νl hνl using hq
  refine ⟨μl, νl, hHaar, hνl, hroot, ?_⟩
  have hν' : IsQuotMeasS X.B.I x.2.1 ν := hμeq ▸ hν
  have hOO := Formalism.L2.SG.Pf.formAllC_holds D X Y u u' s x.2.1 ν x.2.2
    (Formalism.L2.SG.Pf.RelChar.relCharC_holds D X Y u u' s hrel) hHR hν' hfund.1 hfund.2
  have hprod := GlobalTheory.T.realOrbitalIntegral_hsNorm_eq_prod_local D X u u' s.pt.1 μl νl ν hHaar hνl hν hinv
  unfold Formalism.L2.SG.TermOp.ampN
  rw [Formalism.L2.SG.LoopTerm.hsNormSq_smul, Formalism.L2.SG.LoopTerm.hsNormSq_smul, hOO,
    ← Complex.coe_smul, Formalism.L2.SG.LoopTerm.hsNormSq_smul, hprod]
  have hc : Complex.normSq (Formalism.L2.SG.TermOp.chiN X (Formalism.L2.SG.TermOp.kOf X u u' ((Y.cs u).h ((Y.cs u).base s.lam) : X.B.I.Gf) ((Y.cs u').h ((Y.cs u').base s.lam') : X.B.I.Gf) s.pt)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Formalism.L2.SG.Pf.FibreCounting.norm_chiN, one_pow]
  rw [hc, Complex.normSq_ofReal, Complex.normSq_ofReal]
  ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalisedLiftAmplitudeEqCovolumeMulLocalStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedLift_amplitude_eq_covolume_mul_local : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (θ : ℝ) (C : Choice X θ) (u u' : D.what₂.Word) (s : TT Y u u') (x : Point D.host.E (D.R.rS + 1) × Measure X.B.I.Ginf × Set X.B.I.Ginf), s.relevant → s.G ≠ 0 → s.toTerm.atPt x.1 → Formalism.L2.SG.VolPin.IsPinnedR s x.1 x.2.1 → IsFundR s x.2.2 → (∀ v, ∀ r ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v), ∀ y, Formalism.L2.SG.TermOp.rk1 (X.Wloc u v (r * y)) (X.Wloc u' v ((s.pt.1 v)⁻¹ * (r * y))) = Formalism.L2.SG.TermOp.rk1 (X.Wloc u v y) (X.Wloc u' v ((s.pt.1 v)⁻¹ * y))) → ∃ μl νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v)), (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (s.pt.1 v)) (μl v)) ∧ (∀ v, Formalism.L2.SG.RealObj.IsQuotLoc (μl v) (νl v)) ∧ (∀ τ, ∃ p, IsRootMeasR D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) p (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) ((μl (vOf X τ)).map (fun y => Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) ((s.pt.1 (vOf X τ))⁻¹ * y * (s.pt.1 (vOf X τ))))))) ∧ hsNormSq (Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') s) = (Formalism.L2.SG.TermOp.scl (Y.FN u) (Y.FN u') (X := X) (u := u) (u' := u') * X.volK2) ^ 2 * (x.2.1 x.2.2).toReal ^ 2 * ∏ v, hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u' v) (s.pt.1 v)) := by
  first | exact @GlobalTheory.AmpLift.amp_lift | exact GlobalTheory.AmpLift.amp_lift | (intros; apply GlobalTheory.AmpLift.amp_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelevantLiftNormalisedDataExist
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelevantLiftNormalisedDataExist
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem pinAll_all : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), PinAll (Y := Y) u u' :=
  fun _ _ _ u u' => Formalism.L2.SG.Pf.LoopBPin.pinAll_holds u u'

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelevantLiftNormalisedDataExistStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relevantLift_normalisedData_exist : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), PinAll (Y := Y) u u' := by
  first | exact @GlobalTheory.pinAll_all | exact GlobalTheory.pinAll_all | (intros; apply GlobalTheory.pinAll_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelevantTermHasRealRelativePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLoUniMul
universe u_1

namespace GlobalTheory.LowerUnipotentMul

open Matrix

theorem isLoUni_mul {R : Type*} [CommRing R] {n : ℕ} {l l' : Matrix (Fin n) (Fin n) R}
    (hl : Formalism.MainNotions.S.IsLoUni l) (hl' : Formalism.MainNotions.S.IsLoUni l') : Formalism.MainNotions.S.IsLoUni (l * l') := by
  intro i j
  constructor
  · intro hij
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge i k with hik | hki
    · rw [(hl i k).1 hik, zero_mul]
    · rw [(hl' k j).1 (lt_of_le_of_lt hki hij), mul_zero]
  · intro hij
    subst hij
    rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [(hl i i).2 rfl, (hl' i i).2 rfl, one_mul]
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with h | h
      · rw [(hl' k i).1 h, mul_zero]
      · rw [(hl i k).1 h, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h

theorem main : ∀ {R : Type u_1} [inst : CommRing R] {n : ℕ} {l l' : Matrix (Fin n) (Fin n) R},
    Formalism.MainNotions.S.IsLoUni l → Formalism.MainNotions.S.IsLoUni l' → Formalism.MainNotions.S.IsLoUni (l * l') :=
  fun hl hl' => isLoUni_mul hl hl'

end GlobalTheory.LowerUnipotentMul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelevantTermHasRealRelativePoint
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RelPtLift

section Uni

variable {R : Type*} [CommRing R] {n : ℕ}

theorem loUni_mul {l l' : Matrix (Fin n) (Fin n) R} (h : IsLoUni l) (h' : IsLoUni l') : IsLoUni (l * l') := by
  first
  | exact @_root_.GlobalTheory.LowerUnipotentMul.main
  | exact _root_.GlobalTheory.LowerUnipotentMul.main
  | (apply _root_.GlobalTheory.LowerUnipotentMul.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LowerUnipotentMul.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LowerUnipotentMul.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LowerUnipotentMul.main ..)

theorem upUni_mul {l l' : Matrix (Fin n) (Fin n) R} (h : IsUpUni l) (h' : IsUpUni l') : IsUpUni (l * l') := by
  first
  | exact @_root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul
  | exact _root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul
  | (apply _root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption)
  | (intros; apply _root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UpperUnipotentProductFlagMeasures.upUni_mul ..)

end Uni

variable {k r : ℕ}

def sgn (r : ℕ) : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ := Matrix.diagonal fun b => (-1 : ℂ) ^ (r - b.val)

theorem sgn_sq : sgn r * sgn r = 1 := by
  rw [sgn, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext b
  rw [← mul_pow]
  simp

theorem zhatO_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ZhatO k r z z' g = Formalism.QuantumDeterminants.Zhat k r z z' g * sgn r := by
  ext a b
  rw [sgn, Matrix.mul_diagonal, mul_comm]
  rfl

theorem upUni_sgn_conj {U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hU0 : ∀ c b, b < c → U c b = 0)
    (hU1 : ∀ c, U c c = 1) : IsUpUni (sgn r * U * sgn r) := by
  intro a b
  rw [sgn, Matrix.mul_diagonal, Matrix.diagonal_mul]
  refine ⟨fun hab => by rw [hU0 a b hab]; ring, fun hab => ?_⟩
  subst hab
  rw [hU1, mul_one, ← mul_pow]
  simp

theorem loUni_conjT {U : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hU0 : ∀ c b, b < c → U c b = 0)
    (hU1 : ∀ c, U c c = 1) : IsLoUni Uᴴ := by
  intro a b
  refine ⟨fun hab => by rw [conjTranspose_apply, hU0 b a hab, star_zero], fun hab => ?_⟩
  subst hab
  rw [conjTranspose_apply, hU1, star_one]

theorem det_Hpk : IsUnit (Formalism.QuantumDeterminants.Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (Formalism.QuantumDeterminants.hpkFacts k r).2.1

theorem mem_UH_of_Sset {z : Fin (2 * r + k + 1) → ℂ} {a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (ha : a ∈ Formalism.QuantumDeterminants.Sset k r z) : a ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) :=
  Formalism.QuantumDeterminants.Sset_UH ha

theorem zhat_dcoset {z z' : Fin (2 * r + k + 1) → ℂ} (hz : Formalism.QuantumDeterminants.inWb k r z) (hz' : Formalism.QuantumDeterminants.inWb k r z')
    {a a' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (ha : a ∈ Formalism.QuantumDeterminants.Sset k r z)
    (ha' : a' ∈ Formalism.QuantumDeterminants.Sset k r z') (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ∃ U U' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, (∀ c b, b < c → U c b = 0) ∧ (∀ c, U c c = 1) ∧
      (∀ c b, b < c → U' c b = 0) ∧ (∀ c, U' c c = 1) ∧
      Formalism.QuantumDeterminants.Zhat k r z z' (a * g * a'⁻¹) = Uᴴ * Formalism.QuantumDeterminants.Zhat k r z z' g * U' := by
  obtain ⟨-, -, hinv⟩ := Formalism.QuantumDeterminants.sGroup k r z hz
  obtain ⟨-, -, hinv'⟩ := Formalism.QuantumDeterminants.sGroup k r z' hz'
  obtain ⟨U, hU0, hU1, hF⟩ := Formalism.QuantumDeterminants.S_F hz (hinv a ha)
  obtain ⟨U', hU0', hU1', hF'⟩ := Formalism.QuantumDeterminants.S_F hz' (hinv' a' ha')
  have hdet : IsUnit a.det := ((Formalism.QuantumDeterminants.uHGroup _ _ det_Hpk).2.2 a (mem_UH_of_Sset ha)).1
  have hai : (a⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * a⁻¹ = Formalism.QuantumDeterminants.Hpk k r := Formalism.QuantumDeterminants.Sset_UH (hinv a ha)
  have hHa : Formalism.QuantumDeterminants.Hpk k r * a = (a⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r := by
    calc Formalism.QuantumDeterminants.Hpk k r * a = (a⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r * a⁻¹ * a := by rw [hai]
      _ = (a⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r := by
        rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
  refine ⟨U, U', hU0, hU1, hU0', hU1', ?_⟩
  rw [Formalism.QuantumDeterminants.Zhat_eq, Formalism.QuantumDeterminants.Zhat_eq]
  calc (Formalism.QuantumDeterminants.Fm k r z)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * g * a'⁻¹) * Formalism.QuantumDeterminants.Fm k r z'
      = (Formalism.QuantumDeterminants.Fm k r z)ᴴ * (Formalism.QuantumDeterminants.Hpk k r * a) * g * (a'⁻¹ * Formalism.QuantumDeterminants.Fm k r z') := by
        simp only [Matrix.mul_assoc]
    _ = (Formalism.QuantumDeterminants.Fm k r z)ᴴ * ((a⁻¹)ᴴ * Formalism.QuantumDeterminants.Hpk k r) * g * (Formalism.QuantumDeterminants.Fm k r z' * U') := by
        rw [hHa, hF']
    _ = (a⁻¹ * Formalism.QuantumDeterminants.Fm k r z)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g * Formalism.QuantumDeterminants.Fm k r z' * U' := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Uᴴ * ((Formalism.QuantumDeterminants.Fm k r z)ᴴ * Formalism.QuantumDeterminants.Hpk k r * g * Formalism.QuantumDeterminants.Fm k r z') * U' := by
        rw [hF, conjTranspose_mul]; simp only [Matrix.mul_assoc]

theorem relPt_dcoset (D : D7) {z z' : Fin (2 * D.R.rS + D.R.k + 1) → ℂ} (hz : Formalism.QuantumDeterminants.inWb D.R.k D.R.rS z)
    (hz' : Formalism.QuantumDeterminants.inWb D.R.k D.R.rS z') {a a' γ : MatKR D.R.k D.R.rS} (ha : a ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS z)
    (ha' : a' ∈ Formalism.QuantumDeterminants.Sset D.R.k D.R.rS z') {p : Point ℂ (D.R.rS + 1)} (h : RelPt D z z' γ p) :
    RelPt D z z' (a * γ * a'⁻¹) p := by
  obtain ⟨hUH, ⟨L, V, hL, hV, hZ⟩, hGf⟩ := h
  obtain ⟨-, -, hinv'⟩ := Formalism.QuantumDeterminants.sGroup _ _ z' hz'
  have hG := Formalism.QuantumDeterminants.uHGroup _ _ (det_Hpk (k := D.R.k) (r := D.R.rS))
  refine ⟨hG.2.1 _ (hG.2.1 _ (mem_UH_of_Sset ha) _ hUH) _ (mem_UH_of_Sset (hinv' a' ha')), ?_, ?_⟩
  · obtain ⟨U, U', hU0, hU1, hU0', hU1', he⟩ := zhat_dcoset hz hz' ha ha' γ
    have hZ' : Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS z z' γ = L * ptMat p * V * sgn D.R.rS := by
      rw [← hZ, zhatO_eq, Matrix.mul_assoc, sgn_sq, Matrix.mul_one]
    refine ⟨Uᴴ * L, V * (sgn D.R.rS * U' * sgn D.R.rS), loUni_mul (loUni_conjT hU0 hU1) hL,
      upUni_mul hV (upUni_sgn_conj hU0' hU1'), ?_⟩
    rw [zhatO_eq, he, hZ']
    simp only [Matrix.mul_assoc]
  · rw [Formalism.QuantumDeterminants.gInv _ _ z z' hz hz' a ha a'⁻¹ (hinv' a' ha') γ]
    exact hGf

end GlobalTheory.RelPtLift

theorem GlobalTheory.RelPtLift.relPt_lift : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (θ : ℝ) (C : Choice X θ) (u u' : D.what₂.Word) (t : D.s.Term u u') (s : TT Y u u'), s.toTerm = tc hI t → D.s.Gterm t ≠ 0 → D.s.relevant t → ∀ τ, ∃ p, RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) p := by
  intro D X Y hF hI θ C u u' t s hs hG hr τ
  obtain ⟨p, hp⟩ := relPtEx_holds hI C u u' t hG hr τ
  obtain ⟨a, ha, a', ha', heq⟩ := GlobalTheory.TermCoset.dcoset D X Y hF hI θ C u u' t s hs τ
  refine ⟨p, ?_⟩
  rw [heq]
  exact GlobalTheory.RelPtLift.relPt_dcoset D (Formalism.L2.SG.Pf.zTr C u τ).1 (Formalism.L2.SG.Pf.zTr C u' τ).1 ha ha' hp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RelevantTermHasRealRelativePointStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relevant_term_has_real_relative_point : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (θ : ℝ) (C : Choice X θ) (u u' : D.what₂.Word) (t : D.s.Term u u') (s : TT Y u u'), s.toTerm = tc hI t → D.s.Gterm t ≠ 0 → D.s.relevant t → ∀ τ, ∃ p, RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (s.pt.1 (vOf X τ))) p := by
  first | exact @GlobalTheory.RelPtLift.relPt_lift | exact GlobalTheory.RelPtLift.relPt_lift | (intros; apply GlobalTheory.RelPtLift.relPt_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UMatMulLoc
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StabInv

open Formalism.QuantumDeterminants PI.AmpRootCommon PI.AmpRelAtPt

variable {k r : ℕ}

theorem psi_rel (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z') (c : ℂ) (hc : star c = c)
    (p : Point ℂ (r + 1)) (g₀ : MatKR k r) (hg : g₀ ∈ UH (Hpk k r)) (hZ : ZhatO k r z z' g₀ = ptMat p)
    (a : MatKR k r) (ha : a ∈ RStab k r g₀) : psi k r z c a = psi k r z' c (g₀⁻¹ * a * g₀) := by
  have ha' : a ∈ Nset k r ∧ g₀⁻¹ * a * g₀ ∈ Nset k r := ha
  have hsum := sum_super (ptσ_invol p) (zhat_pt hZ) (ptζ_ne p) (fun i i1 h => pt_adj p i i1 h)
    (flagMat_upper (z := z) ha'.1) (flagMat_diag ha'.1) (flagMat_upper (z := z') ha'.2)
    (flagMat_diag ha'.2) (flag_rel hz hz' hg ha)
  have hell : ell k r z' (g₀⁻¹ * a * g₀) = star (ell k r z a) := by
    rw [ell_eq, ell_eq, hsum]
  have hcim : c.im = 0 := Complex.conj_eq_iff_im.mp hc
  have hre : (c * star (ell k r z a)).re = (c * ell k r z a).re := by
    simp [Complex.mul_re, hcim]
  simp only [Formalism.QuantumDeterminants.psi, hell, hre]

theorem psi_conj (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (c : ℂ) {n m : MatKR k r}
    (hn : n ∈ Nset k r) (hm : m ∈ Nset k r) : psi k r z c (n⁻¹ * m * n) = psi k r z c m := by
  obtain ⟨hone, hmulN, hinvN⟩ := Formalism.QuantumDeterminants.unipotent_subgroup_holds k r
  have hni : n⁻¹ ∈ Nset k r := hinvN n hn
  have h1 : psi k r z c 1 = 1 := by
    have hmul := Formalism.FourierDecayAlt.P.PBG.psi_mul_nset z hz c hone hone
    rw [Matrix.one_mul] at hmul
    have hne : psi k r z c 1 ≠ 0 := Complex.exp_ne_zero _
    exact mul_left_cancel₀ hne (hmul.symm.trans (mul_one _).symm)
  have hinv : n⁻¹ * n = 1 := uh_inv_mul hn.1
  have hpair := Formalism.FourierDecayAlt.P.PBG.psi_mul_nset z hz c hni hn
  rw [hinv, h1] at hpair
  rw [Formalism.FourierDecayAlt.P.PBG.psi_mul_nset z hz c (hmulN _ hni _ hm) hn,
    Formalism.FourierDecayAlt.P.PBG.psi_mul_nset z hz c hni hm]
  calc psi k r z c n⁻¹ * psi k r z c m * psi k r z c n
      = psi k r z c m * (psi k r z c n⁻¹ * psi k r z c n) := by ring
    _ = psi k r z c m := by rw [← hpair, mul_one]

theorem psi_cell (z z' : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hz' : inWb k r z')
    (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z') (c : ℂ) (hc : star c = c) (p : Point ℂ (r + 1)) (γ : MatKR k r)
    (hγ : γ ∈ UH (Hpk k r)) (hcell : IsInCell (ZhatO k r z z' γ) p) {m : MatKR k r} (hm : m ∈ Nset k r)
    (hm' : γ⁻¹ * m * γ ∈ Nset k r) : psi k r z c m = psi k r z' c (γ⁻¹ * m * γ) := by
  obtain ⟨n, hn, n', hn', g₀, hg₀, rfl, hZ⟩ := GlobalTheory.CellRep.cell_rep k r z z' γ p hz hz' hT hT' hγ hcell
  obtain ⟨_, hmulN, hinvN⟩ := Formalism.QuantumDeterminants.unipotent_subgroup_holds k r
  have e1 : n' * n'⁻¹ = 1 := uh_mul_inv hn'.1
  have key : n' * ((n * g₀ * n')⁻¹ * m * (n * g₀ * n')) * n'⁻¹ = g₀⁻¹ * (n⁻¹ * m * n) * g₀ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc n' n'⁻¹, e1, Matrix.one_mul, Matrix.mul_one]
  have hnmn : n⁻¹ * m * n ∈ Nset k r :=
    hmulN _ (hmulN _ (hinvN n hn) _ hm) _ hn
  have ha : n⁻¹ * m * n ∈ RStab k r g₀ := by
    refine ⟨hnmn, ?_⟩
    rw [← key]
    exact hmulN _ (hmulN _ hn' _ hm') _ (hinvN n' hn')
  have hback := psi_conj z' hz' c (hinvN n' hn') hm'
  rw [Matrix.nonsing_inv_nonsing_inv _ (Matrix.isUnit_det_of_right_inverse e1)] at hback
  calc psi k r z c m = psi k r z c (n⁻¹ * m * n) := (psi_conj z hz c hn hm).symm
    _ = psi k r z' c (g₀⁻¹ * (n⁻¹ * m * n) * g₀) := psi_rel z z' hz hz' c hc p g₀ hg₀ hZ _ ha
    _ = psi k r z' c (n' * ((n * g₀ * n')⁻¹ * m * (n * g₀ * n')) * n'⁻¹) := by rw [key]
    _ = psi k r z' c ((n * g₀ * n')⁻¹ * m * (n * g₀ * n')) := hback

end GlobalTheory.StabInv

namespace GlobalTheory.StabInv

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf.WuDec Formalism.L2.SG.Pf.EquivPf Formalism.L2.SG.Pf.Choice

theorem wloc_n {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F)
    (s x : Formalism.REAL.UJ (X.B.I.ε v)) (hs : s ∈ Nloc X u v) :
    X.Wloc u v (s * x) = psiV X u v (uMat s) • X.Wloc u v x := by
  have h1H : (1 : Formalism.REAL.UJ (X.B.I.ε v)) ∈ Hloc X u v := by
    intro y _
    rw [uMat_one', Matrix.one_mulVec]
  have h1N : (1 : Formalism.REAL.UJ (X.B.I.ε v)) ∈ Nloc X u v := by
    refine ⟨?_, ?_⟩
    · rw [uMat_one']
      exact inS_one
    · intro y _
      rw [uMat_one', sub_self, Matrix.zero_mulVec]
      exact Submodule.zero_mem _
  have hA := locEquiv X u v s hs 1 h1H x
  have hB := locEquiv X u v 1 h1N 1 h1H x
  simp only [mul_one] at hA
  simp only [mul_one, one_mul, uMat_one', psiV_one, one_smul] at hB
  rw [hA, ← hB]

theorem uMat_mul_loc {n : ℕ} {ε : Fin n → Bool} (a b : Formalism.REAL.UJ ε) : uMat (a * b) = uMat a * uMat b := rfl

theorem stab_inv : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ) (hB : WuBessel C) (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (p : Point ℂ (D.R.rS + 1)), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → RelPt D (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) γ) p → ∀ s ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε (vOf X τ)) (fun a => rv X.B.I (vOf X τ) (X.eR a)) (rv X.B.I (vOf X τ) (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε (vOf X τ)) (fun a => rv X.B.I (vOf X τ) (X.eR a)) (rv X.B.I (vOf X τ) (X.zR u'))) γ, ∀ x, Formalism.L2.SG.TermOp.rk1 (X.Wloc u (vOf X τ) (s * x)) (X.Wloc u' (vOf X τ) (γ⁻¹ * (s * x))) = Formalism.L2.SG.TermOp.rk1 (X.Wloc u (vOf X τ) x) (X.Wloc u' (vOf X τ) (γ⁻¹ * x)) := by
  intro D X θ C _ u u' τ γ p _ hrel s hs x
  obtain ⟨hQiQ, hQQi, hgram, hcol⟩ := C.isT τ
  have hs1 : s ∈ Nloc X u (vOf X τ) := hs.1
  have hs2 : γ⁻¹ * s * γ ∈ Nloc X u' (vOf X τ) := hs.2
  have hn : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := Formalism.L2.SG.Pf.Choice.n_eq' X
  have hc : ∀ a : Fin D.R.rS, frS D ^ (D.R.rS - (a : ℕ)) ≠ 0 :=
    fun a => pow_ne_zero _ (Formalism.L2.SG.Pf.Choice.frS_ne D)
  have hcolE : ∀ a : Fin D.R.rS, C.Q τ *ᵥ Pi.single (eI D.R.k D.R.rS a) 1 =
      frS D ^ (D.R.rS - (a : ℕ)) • Formalism.L2.SG.HidaSetting.rv X.B.I (vOf X τ) (X.eR a) :=
    fun a => (hcol a a rfl).1
  have hmN : ∀ (w : D.what₂.Word) (t : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))), t ∈ Nloc X w (vOf X τ) →
      C.Qi τ * uMat t * C.Q τ ∈ Nset D.R.k D.R.rS := by
    intro w t ht
    have hU : (uMat t)ᴴ * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * uMat t = Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) := t.2
    exact nset_loc hn _ _ _ hQiQ hQQi hgram _ _ hc hcolE _ hU ht
  have hpsi : ∀ (w : D.what₂.Word) (t : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))), t ∈ Nloc X w (vOf X τ) →
      psiV X w (vOf X τ) (uMat t) = psiS D (zB X (C.Qi τ) w τ) (C.Qi τ * uMat t * C.Q τ) := by
    intro w t ht
    have hback : C.Q τ * (C.Qi τ * uMat t * C.Q τ) * C.Qi τ = uMat t := by
      simp only [← Matrix.mul_assoc, hQQi, Matrix.one_mul]
      rw [Matrix.mul_assoc, hQQi, Matrix.mul_one]
    have h := Formalism.L2.SG.Pf.psiTr C w τ _ (hmN w t ht)
    rw [hback] at h
    exact h
  set g := Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) γ with hg
  have hginv : g⁻¹ = C.Qi τ * uMat γ⁻¹ * C.Q τ := by
    apply Matrix.inv_eq_left_inv
    rw [hg, Formalism.L2.SG.RealObj.trG]
    calc C.Qi τ * uMat γ⁻¹ * C.Q τ * (C.Qi τ * uMat γ * C.Q τ)
        = C.Qi τ * (uMat γ⁻¹ * (C.Q τ * C.Qi τ) * uMat γ) * C.Q τ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hQQi, Matrix.mul_one, uMat_inv_mul, Matrix.mul_one, hQiQ]
  have hconj : C.Qi τ * uMat (γ⁻¹ * s * γ) * C.Q τ = g⁻¹ * (C.Qi τ * uMat s * C.Q τ) * g := by
    rw [hginv, hg, Formalism.L2.SG.RealObj.trG, uMat_mul_loc, uMat_mul_loc]
    calc C.Qi τ * (uMat γ⁻¹ * uMat s * uMat γ) * C.Q τ
        = C.Qi τ * (uMat γ⁻¹ * 1 * uMat s * 1 * uMat γ) * C.Q τ := by
          rw [Matrix.mul_one, Matrix.mul_one]
      _ = C.Qi τ * uMat γ⁻¹ * C.Q τ * (C.Qi τ * uMat s * C.Q τ) * (C.Qi τ * uMat γ * C.Q τ) := by
          rw [← hQQi]
          simp only [Matrix.mul_assoc]
  obtain ⟨hz, hTz⟩ := Formalism.L2.SG.Pf.zTr C u τ
  obtain ⟨hz', hTz'⟩ := Formalism.L2.SG.Pf.zTr C u' τ
  have hT : 0 < Tz D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
    rw [hTz]; exact Formalism.L2.SG.Pf.Choice.Tr_pos D u
  have hT' : 0 < Tz D.R.k D.R.rS (zB X (C.Qi τ) u' τ) := by
    rw [hTz']; exact Formalism.L2.SG.Pf.Choice.Tr_pos D u'
  have hm' : g⁻¹ * (C.Qi τ * uMat s * C.Q τ) * g ∈ Nset D.R.k D.R.rS := by
    rw [← hconj]; exact hmN u' _ hs2
  have hkey : psiV X u (vOf X τ) (uMat s) = psiV X u' (vOf X τ) (uMat (γ⁻¹ * s * γ)) := by
    rw [hpsi u s hs1, hpsi u' _ hs2, hconj]
    exact psi_cell _ _ hz hz' hT hT' _ (Complex.conj_ofReal _) p g hrel.1 hrel.2.1 (hmN u s hs1) hm'
  have hx : γ⁻¹ * (s * x) = (γ⁻¹ * s * γ) * (γ⁻¹ * x) := by group
  rw [wloc_n X u (vOf X τ) s x hs1, hx, wloc_n X u' (vOf X τ) _ _ hs2, ← hkey]
  have hnorm : ‖psiV X u (vOf X τ) (uMat s)‖ = 1 := norm_psiR _ _ _ _ _ _
  have hcm : (starRingEnd ℂ) (psiV X u (vOf X τ) (uMat s)) * psiV X u (vOf X τ) (uMat s) = 1 := by
    rw [Complex.conj_mul', hnorm]; norm_num
  ext ξ
  rw [Formalism.L2.SG.TermOp.rankOneInnerOperator_apply, Formalism.L2.SG.TermOp.rankOneInnerOperator_apply, inner_smul_left, smul_smul]
  congr 1
  linear_combination (inner ℂ (X.Wloc u' (vOf X τ) (γ⁻¹ * x)) ξ) * hcm

end GlobalTheory.StabInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalBesselJFactorAllWordsOfGap
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.JFactTie

theorem jFactN_all : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (C : Choice X 1) (hB : WuBessel C) (u u' : D.what₂.Word), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → JFactN hI C hB u u' := by
  intro D X Y hF hI C hB u u' hGap t hG hr
  have hex : ∃ s : TT Y u u', s.toTerm = tc hI t :=
    Formalism.L2.SG.Pf.liftOntoC_of Formalism.L2.SG.Pf.WittFlags.LatIso_holds D X Y u u' (tc hI t)
  have hs : hex.choose.toTerm = tc hI t := hex.choose_spec
  have hrel : hex.choose.relevant := by
    show hex.choose.toTerm.relevant
    rw [hs]
    exact (hI.relevant t).1 hr
  have hsG : hex.choose.G ≠ 0 := by
    show hex.choose.toTerm.G ≠ 0
    rw [hs]
    intro h0
    apply hG
    apply (algebraMap D.host.F D.host.E).injective
    rw [gterm_val hI t, h0, map_zero]
  have hP : HasPin hex.choose := GlobalTheory.T.relevantLift_normalisedData_exist D X Y u u' hex.choose hrel hsG
  have hx := hP.choose_spec
  have hJ : JtOf hI t = Formalism.L2.SG.TermOp.ampN (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') hex.choose := by
    unfold JtOf; rw [dite_eq_left hex]
  have hV : volRC hI t = (hP.choose.2.1 hP.choose.2.2).toReal := by
    unfold volRC covR; rw [dite_eq_left ⟨hr, hG, hex⟩, dite_eq_left hP]
  have hinv : ∀ v, ∀ r ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (hex.choose.pt.1 v), ∀ y,
      Formalism.L2.SG.TermOp.rk1 (X.Wloc u v (r * y)) (X.Wloc u' v ((hex.choose.pt.1 v)⁻¹ * (r * y))) =
        Formalism.L2.SG.TermOp.rk1 (X.Wloc u v y) (X.Wloc u' v ((hex.choose.pt.1 v)⁻¹ * y)) := by
    intro v
    obtain ⟨τ, rfl⟩ : ∃ τ, vOf X τ = v := X.pl.symm.surjective v
    obtain ⟨p, hp⟩ := GlobalTheory.T.relevant_term_has_real_relative_point D X Y hF hI 1 C u u' t hex.choose hs hG hr τ
    exact GlobalTheory.StabInv.stab_inv D X 1 C hB u u' τ (hex.choose.pt.1 (vOf X τ)) p hGap hp
  obtain ⟨μl, νl, hH, hQ, hR, hA⟩ := GlobalTheory.T.normalisedLift_amplitude_eq_covolume_mul_local D X Y 1 C u u' hex.choose hP.choose hrel hsG hx.1 hx.2.1 hx.2.2 hinv
  have hloc : ∀ τ, j1 hI C hB t τ = Complex.normSq ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) *
      hsNormSq (haveI := FiniteDimensional.completeSpace ℂ (X.Vloc u (vOf X τ));
        Formalism.L2.SG.RealObj.Jv (νl (vOf X τ)) (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) (hex.choose.pt.1 (vOf X τ))) := by
    intro τ
    have : SigmaFinite (μl (vOf X τ)) := (hH (vOf X τ)).1
    exact GlobalTheory.T.localAmplitude_wittLift_eq_quotientIntegral D X Y hF hI C hB u u' t hex.choose hs hG hr hGap τ (μl (vOf X τ)) (νl (vOf X τ)) inferInstance
      (hQ (vOf X τ)) (hR τ)
  have hK := GlobalTheory.T.amplitudeConstant_eq_prod_covolumes D X Y hF 1 C hB u u' one_pos hGap
  have hre : (∏ τ, hsNormSq (haveI := FiniteDimensional.completeSpace ℂ (X.Vloc u (vOf X τ));
        Formalism.L2.SG.RealObj.Jv (νl (vOf X τ)) (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) (hex.choose.pt.1 (vOf X τ)))) =
      ∏ v, hsNormSq (haveI := FiniteDimensional.completeSpace ℂ (X.Vloc u v);
        Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u' v) (hex.choose.pt.1 v)) :=
    Fintype.prod_equiv X.pl.symm _ _ (fun τ => rfl)
  have hcov : covN (Y := Y) C u * covN (Y := Y) C u' =
      ((Measure.pi (fun _ : D.what₂.Tau => muNB D 1) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u)).toReal * (Measure.pi (fun _ : D.what₂.Tau => muNB D 1) ((fun (x : X.B.I.Ginf) (τ : D.what₂.Tau) => (Matrix.of.symm (Formalism.L2.SG.RealObj.trG (C.Q τ) (C.Qi τ) (x (vOf X τ))) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) '' Y.FN u')).toReal) := rfl
  rw [hJ, hV, hA, hcov]
  unfold P1
  rw [Finset.prod_congr rfl fun τ _ => hloc τ, Finset.prod_mul_distrib, hre, hK]
  ring

end GlobalTheory.JFactTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalBesselJFactorAllWordsOfGapStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.LoopTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBesselJFactor_all_words_of_gap : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (C : Choice X 1) (hB : WuBessel C) (u u' : D.what₂.Word), Formalism.L2.SG.ConcreteSettingExists.GapHyp D → JFactN hI C hB u u' := by
  first | exact @GlobalTheory.JFactTie.jFactN_all | exact GlobalTheory.JFactTie.jFactN_all | (intros; apply GlobalTheory.JFactTie.jFactN_all <;> assumption)
end
