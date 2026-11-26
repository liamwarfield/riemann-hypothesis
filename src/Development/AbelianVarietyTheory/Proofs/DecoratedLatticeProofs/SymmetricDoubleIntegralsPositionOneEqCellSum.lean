module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricPositionsDoubleIntegralExistsUnique
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EntriesWellDefined
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumOfRankOneGram

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OneDblIffSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.QuotIntPosOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsQuotIntCells
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsQuotIntCells
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
attribute [-instance] GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix Formalism.DoubleCosetMeasures.instMeasMat

namespace GlobalTheory.CellQuotInt

theorem isQuotInt_cells : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (J : Subgroup (GL (n ⊕ Fin c) k)) (_ : IsCO J) (f : GL (n ⊕ Fin c) k → ℂ) (_ : ∀ h, ∀ j ∈ J, f (h * j) = f h) (_ : ∀ (x : GL n k), ∀ u ∈ N k n c p, ∀ h, f (embX c x * u * h) = ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) : ℂ) * f h) (T : Finset (GL (n ⊕ Fin c) k)) (_ : Covers p J T f), (∀ h, volCell ν μX p J h ≠ 0 ∧ volCell ν μX p J h ≠ ⊤) ∧ ∀ z, IsQuotInt ν μX μG p f z ↔ z = ∑ h ∈ T, (((μG J).toReal / (volCell ν μX p J h).toReal : ℝ) : ℂ) * f h := by
  intro k _ _ _ _ _ _ n _ _ c p hp hpc ν _ μX _ μG _ J hJ f hfJ hfR T hT
  classical
  obtain ⟨bX, lX, sX, -, -, -, hXH, hXR⟩ := GlobalTheory.SplitWeil.volGL_haar k n ν
  obtain ⟨bG, lG, sG, -, -, -⟩ := GlobalTheory.SplitWeil.volGL_haar k (n ⊕ Fin c) ν
  obtain ⟨hN, -, hH, hRi, hconj⟩ := GlobalTheory.RootEx.VolN.volN_haar_and_modulus k n c p hp hpc ν
  haveI : LocallyCompactSpace (N k n c p) := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (N k n c p) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaFinite (volN ν n c p) := Measure.IsHaarMeasure.sigmaFinite _
  haveI : μX.IsMulRightInvariant := by
    rw [Measure.isMulLeftInvariant_eq_smul μX (volGL ν n)]
    infer_instance
  have hRm : ∀ (g : GL n k) (u : N k n c p), embX c g * (u : GL (n ⊕ Fin c) k) ∈ R k n c p :=
    fun g u => mul_mem (Subgroup.mem_sup_left ⟨g, rfl⟩) (Subgroup.mem_sup_right u.2)
  have hm : Continuous (fun z : GL n k × N k n c p => embX c z.1 * (z.2 : GL (n ⊕ Fin c) k)) :=
    (GlobalTheory.QuotInt.continuous_embX.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  let S : GL (n ⊕ Fin c) k → Set (GL n k × N k n c p) :=
    fun h => {z | h⁻¹ * (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k)) * h ∈ J}
  have hSo : ∀ h, IsOpen (S h) := fun h =>
    hJ.1.preimage ((continuous_const.mul hm).mul continuous_const)
  have hScomp : ∀ h, ∃ D, IsCompact D ∧ S h ⊆ D := by
    intro h
    have hK : IsCompact ((fun x => h * x * h⁻¹) '' (J : Set (GL (n ⊕ Fin c) k))) :=
      hJ.2.image (by fun_prop)
    obtain ⟨D, hD, hDm⟩ := GlobalTheory.QuotInt.compact_preimage hN hK
    exact ⟨D, hD, fun z hz => hDm z ⟨_, hz, by group⟩⟩
  have hvol : ∀ h, volCell ν μX p J h = (μX.prod (volN ν n c p)) (S h) := by
    intro h
    rw [Measure.prod_apply (hSo h).measurableSet]
    rfl
  have hvol0 : ∀ h, volCell ν μX p J h ≠ 0 ∧ volCell ν μX p J h ≠ ⊤ := by
    intro h
    obtain ⟨D, hD, hSD⟩ := hScomp h
    rw [hvol]
    exact ⟨(hSo h).measure_ne_zero _ ⟨(1, 1), by simp [S, J.one_mem]⟩,
      ((measure_mono hSD).trans_lt hD.measure_lt_top).ne⟩

  have hcell : ∀ h, ∫ g, (∫ u : N k n c p, (if h⁻¹ * (embX c g * (u : GL (n ⊕ Fin c) k)) * h ∈ J then (1 : ℂ) else 0)
      ∂(volN ν n c p)) ∂μX = (((volCell ν μX p J h).toReal : ℝ) : ℂ) := by
    intro h
    have e : (fun z : GL n k × N k n c p =>
        if h⁻¹ * (embX c z.1 * (z.2 : GL (n ⊕ Fin c) k)) * h ∈ J then (1 : ℂ) else 0) =
        (S h).indicator (fun _ => (1 : ℂ)) := by
      funext z
      simp [S, Set.indicator_apply]
    have hint : Integrable ((S h).indicator (fun _ => (1 : ℂ))) (μX.prod (volN ν n c p)) := by
      rw [integrable_indicator_iff (hSo h).measurableSet]
      exact integrableOn_const (by rw [← hvol]; exact (hvol0 h).2)
    rw [← e] at hint
    have h2 := integral_prod _ hint
    simp only at h2
    rw [← h2, e, integral_indicator_const _ (hSo h).measurableSet, Measure.real, ← hvol]
    simp
  have hmod : ∀ (φ : GL (n ⊕ Fin c) k → ℂ) (g₀ : GL n k) (u₁ : GL (n ⊕ Fin c) k), u₁ ∈ N k n c p →
      ∫ g, (∫ u : N k n c p, φ (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) ∂(volN ν n c p)) ∂μX
        = ((nabs k (Matrix.GeneralLinearGroup.det g₀) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) : ℂ) *
          ∫ g, (∫ u : N k n c p, φ (embX c g * (u : GL (n ⊕ Fin c) k)) ∂(volN ν n c p)) ∂μX := by
    intro φ g₀ u₁ hu₁
    have hpos : ∀ y : kˣ, 0 < nabs k y := fun y => (nabs_properties k).2.1 y
    have e3 : nabs k (Matrix.GeneralLinearGroup.det g₀⁻¹) ^ (-((c : ℝ) + 1 - 2 * p)) =
        nabs k (Matrix.GeneralLinearGroup.det g₀) ^ ((c : ℝ) + 1 - 2 * p) := by
      have h3 : nabs k (Matrix.GeneralLinearGroup.det g₀⁻¹) =
          (nabs k (Matrix.GeneralLinearGroup.det g₀))⁻¹ := by
        simp [nabs]
      rw [h3, Real.inv_rpow (hpos _).le, ← Real.rpow_neg (hpos _).le, neg_neg]
    have step : ∀ g : GL n k,
        ∫ u : N k n c p, φ (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) ∂(volN ν n c p) =
          (nabs k (Matrix.GeneralLinearGroup.det g₀) ^ ((c : ℝ) + 1 - 2 * p)) •
            ∫ u : N k n c p, φ (embX c (g * g₀) * (u : GL (n ⊕ Fin c) k)) ∂(volN ν n c p) := by
      intro g
      have e1 := hconj g₀⁻¹ (fun y => φ (embX c (g * g₀) * y * u₁))
      have e2 := integral_mul_right_eq_self (μ := volN ν n c p)
        (fun u : N k n c p => φ (embX c (g * g₀) * (u : GL (n ⊕ Fin c) k))) ⟨u₁, hu₁⟩
      simp only [Subgroup.coe_mul, ← mul_assoc] at e2
      rw [e3, e2] at e1
      rw [← e1]
      congr 1
      funext u
      congr 1
      simp only [map_mul, map_inv]
      group
    simp only [step]
    rw [integral_smul, Complex.real_smul]
    congr 1
    have := integral_mul_right_eq_self (μ := μX)
      (fun g => ∫ u : N k n c p, φ (embX c g * (u : GL (n ⊕ Fin c) k)) ∂(volN ν n c p)) g₀
    simpa using this

  have hv0 : ∀ h, (volCell ν μX p J h).toReal ≠ 0 := fun h =>
    ENNReal.toReal_ne_zero.2 (hvol0 h)
  let F : GL (n ⊕ Fin c) k → ℂ := fun x =>
    ∑ t ∈ T, if t⁻¹ * x ∈ J then f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0
  have hFsb : F ∈ SB (GL (n ⊕ Fin c) k) := by
    have := GlobalTheory.QuotInt.sb_of_quot J hJ.1 hJ.2 (T.image (QuotientGroup.mk : GL (n ⊕ Fin c) k → GL (n ⊕ Fin c) k ⧸ J))
      (fun q => ∑ t ∈ T, if (t : GL (n ⊕ Fin c) k ⧸ J) = q then
        f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0)
      (fun q hq => Finset.sum_eq_zero fun t ht => if_neg fun e => hq (Finset.mem_image.2 ⟨t, ht, e⟩))
    have hFeq : F = fun x : GL (n ⊕ Fin c) k => ∑ t ∈ T, if (t : GL (n ⊕ Fin c) k ⧸ J) = (x : GL (n ⊕ Fin c) k ⧸ J) then
        f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0 := by
      funext x
      simp only [F, QuotientGroup.eq]
    rw [hFeq]
    exact this
  have hFint : ∫ x, F x ∂μG =
      ∑ t ∈ T, ((((μG J).toReal / (volCell ν μX p J t).toReal : ℝ) : ℂ)) * f t := by
    have hind : ∀ t : GL (n ⊕ Fin c) k,
        Integrable (fun x => if t⁻¹ * x ∈ J then f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0) μG ∧
        ∫ x, (if t⁻¹ * x ∈ J then f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0) ∂μG =
          ((((μG J).toReal / (volCell ν μX p J t).toReal : ℝ) : ℂ)) * f t := by
      intro t
      have e : (fun x => if t⁻¹ * x ∈ J then f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ) else 0) =
          fun x => (J : Set (GL (n ⊕ Fin c) k)).indicator
            (fun _ => f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ)) (t⁻¹ * x) := by
        funext x
        simp [Set.indicator_apply]
      have hi : Integrable ((J : Set (GL (n ⊕ Fin c) k)).indicator
          (fun _ => f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ))) μG := by
        rw [integrable_indicator_iff hJ.1.measurableSet]
        exact integrableOn_const hJ.2.measure_lt_top.ne
      rw [e]
      refine ⟨hi.comp_mul_left t⁻¹, ?_⟩
      rw [integral_mul_left_eq_self (fun x => (J : Set (GL (n ⊕ Fin c) k)).indicator
          (fun _ => f t / (((volCell ν μX p J t).toReal : ℝ) : ℂ)) x) t⁻¹,
        integral_indicator_const _ hJ.1.measurableSet]
      simp only [Measure.real, Complex.real_smul]
      have := hv0 t
      push_cast
      field_simp
    show ∫ x, (∑ t ∈ T, _) ∂μG = _
    rw [MeasureTheory.integral_finsetSum _ (fun t _ => (hind t).1)]
    exact Finset.sum_congr rfl fun t _ => (hind t).2

  have hRinv : ∀ (y t : GL (n ⊕ Fin c) k), t⁻¹ * y ∈ J →
      DoubleCoset.mk (R k n c p) J y = DoubleCoset.mk (R k n c p) J t := by
    intro y t hy
    rw [DoubleCoset.eq]
    exact ⟨1, one_mem _, (t⁻¹ * y)⁻¹, J.inv_mem hy, by group⟩
  have hmkR : ∀ r ∈ R k n c p, ∀ y,
      DoubleCoset.mk (R k n c p) J (r * y) = DoubleCoset.mk (R k n c p) J y := by
    intro r hr y
    rw [DoubleCoset.eq]
    exact ⟨r⁻¹, inv_mem hr, 1, one_mem _, by group⟩
  have hFcell : ∀ t₀ ∈ T, ∀ y, DoubleCoset.mk (R k n c p) J y = DoubleCoset.mk (R k n c p) J t₀ →
      F y = if t₀⁻¹ * y ∈ J then f t₀ / (((volCell ν μX p J t₀).toReal : ℝ) : ℂ) else 0 := by
    intro t₀ ht₀ y hy
    show (∑ t ∈ T, _) = _
    rw [Finset.sum_eq_single t₀]
    · intro t ht hne
      rw [if_neg]
      intro hmem
      exact hne (hT.1 (Finset.mem_coe.2 ht) (Finset.mem_coe.2 ht₀) ((hRinv y t hmem).symm.trans hy))
    · intro h
      exact absurd ht₀ h
  have hFoff : ∀ y, (∀ t ∈ T, DoubleCoset.mk (R k n c p) J y ≠ DoubleCoset.mk (R k n c p) J t) → F y = 0 := by
    intro y hy
    exact Finset.sum_eq_zero fun t ht => if_neg fun hmem => hy t ht (hRinv y t hmem)
  have havg : ∀ x, f x = ∫ g, (∫ u : N k n c p, F (embX c g * (u : GL (n ⊕ Fin c) k) * x)
      ∂(volN ν n c p)) ∂μX := by
    intro x
    by_cases hx : ∃ t ∈ T, DoubleCoset.mk (R k n c p) J x = DoubleCoset.mk (R k n c p) J t
    · obtain ⟨t₀, ht₀, hxt⟩ := hx
      obtain ⟨r, hr, j, hj, rfl⟩ := (@DoubleCoset.eq _ _ _ _ _ _).1 hxt.symm
      obtain ⟨g₀, u₁, hu₁, rfl⟩ := Radical.exists_of_mem_R hr
      set φ : GL (n ⊕ Fin c) k → ℂ := fun y => f t₀ / (((volCell ν μX p J t₀).toReal : ℝ) : ℂ) *
              (if t₀⁻¹ * y * t₀ ∈ J then (1 : ℂ) else 0) with hφ
      have key : ∀ (g : GL n k) (u : N k n c p),
          F (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁ * t₀ * j)) =
            φ (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) := by
        intro g u
        have hw : embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁) ∈ R k n c p :=
          mul_mem (hRm g u) hr
        have e : embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁ * t₀ * j) =
            (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) * t₀ * j := by
          group
        have hmk : DoubleCoset.mk (R k n c p) J
            ((embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) * t₀ * j) =
            DoubleCoset.mk (R k n c p) J t₀ := by
          rw [DoubleCoset.eq]
          exact ⟨_, inv_mem hw, j⁻¹, J.inv_mem hj, by group⟩
        rw [e, hFcell t₀ ht₀ _ hmk]
        have e2 : t₀⁻¹ * ((embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) * t₀ * j) =
            t₀⁻¹ * (embX c g * (u : GL (n ⊕ Fin c) k) * (embX c g₀ * u₁)) * t₀ * j := by
          group
        simp only [hφ, e2, J.mul_mem_cancel_right hj]
        split_ifs <;> simp
      simp only [key]
      rw [hmod φ g₀ u₁ hu₁]
      simp only [hφ, integral_const_mul]
      rw [hcell t₀, hfJ _ j hj, hfR g₀ u₁ hu₁ t₀]
      rw [div_mul_cancel₀ _ (Complex.ofReal_ne_zero.2 (hv0 t₀))]
    · have hf0 : f x = 0 := by
        by_contra h0
        exact hx (hT.2 x h0)
      rw [hf0]
      have : ∀ (g : GL n k) (u : N k n c p), F (embX c g * (u : GL (n ⊕ Fin c) k) * x) = 0 := by
        intro g u
        apply hFoff
        intro t ht e
        exact hx ⟨t, ht, (hmkR _ (hRm g u) x).symm.trans e⟩
      simp [this]
  have hz₀ : IsQuotInt ν μX μG p f
      (∑ t ∈ T, ((((μG J).toReal / (volCell ν μX p J t).toReal : ℝ) : ℂ)) * f t) :=
    ⟨F, hFsb, havg, hFint.symm⟩
  have huniq := (GlobalTheory.QuotInt.quotInt_unique_exists k n c p hp hpc ν μX μG f).1
  exact ⟨hvol0, fun z => ⟨fun hz => huniq _ _ hz hz₀, fun e => by rw [e]; exact hz₀⟩⟩

end GlobalTheory.CellQuotInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsQuotIntCellsStatement
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
attribute [-instance] GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix Formalism.DoubleCosetMeasures.instMeasMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isQuotInt_cells_alt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p ≤ c) (ν : Measure k) [ν.IsAddHaarMeasure] (μX : Measure (GL n k)) [μX.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (J : Subgroup (GL (n ⊕ Fin c) k)) (_ : IsCO J) (f : GL (n ⊕ Fin c) k → ℂ) (_ : ∀ h, ∀ j ∈ J, f (h * j) = f h) (_ : ∀ (x : GL n k), ∀ u ∈ N k n c p, ∀ h, f (embX c x * u * h) = ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * p) : ℝ) : ℂ) * f h) (T : Finset (GL (n ⊕ Fin c) k)) (_ : Covers p J T f), (∀ h, volCell ν μX p J h ≠ 0 ∧ volCell ν μX p J h ≠ ⊤) ∧ ∀ z, IsQuotInt ν μX μG p f z ↔ z = ∑ h ∈ T, (((μG J).toReal / (volCell ν μX p J h).toReal : ℝ) : ℂ) * f h := by
  first | exact @GlobalTheory.CellQuotInt.isQuotInt_cells | exact GlobalTheory.CellQuotInt.isQuotInt_cells | (intros; apply GlobalTheory.CellQuotInt.isQuotInt_cells <;> assumption)
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents app_coe)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale volR)
attribute [-instance] GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix Formalism.DoubleCosetMeasures.instMeasMat

noncomputable section
namespace GlobalTheory.PosOneCell

section Lemmas
variable {X : Type} [TopologicalSpace X] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem app_smul (l : SB X →ₗ[ℂ] V) (z : ℂ) (f : X → ℂ) : app l (z • f) = z • app l f := by
  by_cases hz : z = 0
  · subst hz
    have : app l (0 : X → ℂ) = 0 := by
      rw [show (0 : X → ℂ) = ((0 : SB X) : X → ℂ) from rfl, app_coe, map_zero]
    rw [zero_smul, zero_smul, this]
  · by_cases hf : f ∈ SB X
    · have hzf : z • f ∈ SB X := (SB X).smul_mem z hf
      simp only [app, hf, hzf, dif_pos]
      rw [← map_smul]
      rfl
    · have hzf : z • f ∉ SB X := fun h => hf (((SB X).smul_mem_iff hz).1 h)
      simp [app, hf, hzf]

theorem app_zero (l : SB X →ₗ[ℂ] V) : app l (0 : X → ℂ) = 0 := by
  rw [show (0 : X → ℂ) = ((0 : SB X) : X → ℂ) from rfl, app_coe, map_zero]

end Lemmas

theorem quotInt_posOne : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (_ : 1 ≤ c) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : HasConductor ψ 1) (ν : Measure k) (_ : IsUnitVol ν) (μ : kˣ →* ℂˣ) (_ : IsOpen (μ.ker : Set kˣ)) (m : Measure (GL n k)) [m.IsHaarMeasure] (μG : Measure (GL (n ⊕ Fin c) k)) [μG.IsHaarMeasure] (L : Level (GL (n ⊕ Fin c) k)) (_ : IsCO L.J) (_ : μG L.J = 1) (b : GL (n ⊕ Fin c) k) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (B : SB (Matrix n n' k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : BilPos ψ μ 1 σ B) (F : A) (_ : ∀ j : L.J, σ (j : GL (n ⊕ Fin c) k) F = (L.lam j : ℂ) • F) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) (_ : ∀ j : L.J, om μ 1 (j : GL (n ⊕ Fin c) k) Φ.1 = (((L.lam j)⁻¹ : ℂˣ) : ℂ) • Φ.1) (h' : GL (n' ⊕ Fin (c + 1)) k) (T : Finset (GL (n ⊕ Fin c) k)) (_ : Covers 1 L.J T fun h => flat ψ ν μ Φ.1 h' h), IsQuotInt ν (rescale ν b m) μG 1 (tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1)) (∑ h ∈ T, (((m (prX (Cgrp L.J h))).toReal⁻¹ : ℝ) : ℂ) * app B (xi ψ ν μ Φ.1 L.J b h' h) (σ h F)) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c hc ψ hψ hψc ν hν μ hμ m _ μG _ L hJ hJ1 b A _ _ σ hσ B hB F hF Φ hΦ h' T hT
  haveI : ν.IsAddHaarMeasure := hν.1
  have hr := volN_stabLat (n := n) (c := c) ν b
  haveI : (rescale ν b m).IsHaarMeasure := by
    unfold rescale
    exact Measure.IsHaarMeasure.smul m (ENNReal.inv_ne_zero.2 (ENNReal.toReal_pos_iff.1 hr).2.ne)
      (ENNReal.inv_ne_top.2 (ENNReal.toReal_pos_iff.1 hr).1.ne')
  have hflat : ∀ h, tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1) h = app B (flat ψ ν μ Φ.1 h' h) (σ h F) := by
    intro h
    simp only [tInt, flat]
    rw [← om_mul]
    simp
  have hSB : ∀ h, flat ψ ν μ Φ.1 h' h ∈ SB (Matrix n n' k) := fun h =>
    (GlobalTheory.RootEx.opE_SB_and_linear k n n' c 1 ψ hψ ν).1 _ (om_mem_SB μ h' h Φ.2)
  have hinv : ∀ h, ∀ j ∈ L.J, tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1) (h * j) = tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1) h := by
    intro h j hj
    have hΦj : om μ 1 j Φ.1 = (((L.lam ⟨j, hj⟩)⁻¹ : ℂˣ) : ℂ) • Φ.1 := hΦ ⟨j, hj⟩
    have hFj : σ j F = (L.lam ⟨j, hj⟩ : ℂ) • F := hF ⟨j, hj⟩
    have e : flat ψ ν μ Φ.1 h' (h * j) = (((L.lam ⟨j, hj⟩)⁻¹ : ℂˣ) : ℂ) • flat ψ ν μ Φ.1 h' h := by
      unfold flat
      rw [show om μ h' (h * j) Φ.1 = om μ h' h (om μ 1 j Φ.1) by rw [← om_mul]; simp, hΦj,
        GlobalTheory.UnfoldedEntries.om_smul, GlobalTheory.UnfoldedEntries.opE_smul]
    rw [hflat, hflat, e, PosOneCell.app_smul, map_mul, Module.End.mul_apply, hFj, map_smul, map_smul,
      LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      one_mul]
  have hmod : ∀ (x : GL n k), ∀ u ∈ N k n c 1, ∀ h, tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1) (embX c x * u * h) =
      ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * ((1 : ℕ) : ℝ)) : ℝ) : ℂ) *
        tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1) h := by
    intro x u hu h
    have e : flat ψ ν μ Φ.1 h' (embX c x * u * h) =
        ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((1 : ℕ) : ℝ)) : ℝ) : ℂ) •
          om μ 1 x ((ψ (-simpleSum u) : ℂ) • flat ψ ν μ Φ.1 h' h) := by
      unfold flat
      rw [show om μ h' (embX c x * u * h) Φ.1 = om μ 1 (embX c x) (om μ 1 u (om μ h' h Φ.1)) by
          rw [← om_mul, ← om_mul]; simp,
        (GlobalTheory.RootEx.opE_om_embX k n n' c 1 le_rfl hc ψ ν μ _).1,
        GlobalTheory.RootEx.opE_om_target_unipotent k n n' c 1 le_rfl hc ψ ν μ _ u hu]
    let Ψ : SB (Matrix n n' k) := ⟨flat ψ ν μ Φ.1 h' h, hSB h⟩
    let Ψ₁ : SB (Matrix n n' k) := ⟨om μ 1 x (flat ψ ν μ Φ.1 h' h), om_mem_SB μ 1 x (hSB h)⟩
    have a0 : app B (flat ψ ν μ Φ.1 h' h) = B Ψ := app_coe B Ψ
    have a1 : app B (om μ 1 x (flat ψ ν μ Φ.1 h' h)) = B Ψ₁ := app_coe B Ψ₁
    rw [hflat, hflat, e, GlobalTheory.UnfoldedEntries.om_smul, smul_smul, PosOneCell.app_smul, map_mul, map_mul,
      Module.End.mul_apply, Module.End.mul_apply, a0, a1, LinearMap.smul_apply, hB.2 x Ψ Ψ₁ _ rfl,
      hB.1 Ψ u hu, smul_eq_mul]
    have key : (ψ (-simpleSum u) : ℂ) * (ψ (simpleSum u) : ℂ) = 1 := by
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, Circle.coe_one]
    have hp := GlobalTheory.RootEx.OpELevi.nabs_pos (Matrix.GeneralLinearGroup.det x)
    have rp : ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((1 : ℕ) : ℝ)) : ℝ) : ℂ) *
        ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((1 : ℕ) : ℝ)) : ℝ) : ℂ) =
        ((nabs k (Matrix.GeneralLinearGroup.det x) ^ ((c : ℝ) + 1 - 2 * ((1 : ℕ) : ℝ)) : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, ← Real.rpow_add hp]
      congr 2
      ring
    linear_combination (B Ψ (σ h F)) * (((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((1 : ℕ) : ℝ)) : ℝ) : ℂ) *
        ((nabs k (Matrix.GeneralLinearGroup.det x) ^ (((c : ℝ) + 1) / 2 - ((1 : ℕ) : ℝ)) : ℝ) : ℂ)) * key
      + (B Ψ (σ h F)) * rp
  have hcov : Covers 1 L.J T (tInt ψ ν μ 1 σ B F (om μ h' 1 Φ.1)) := by
    refine ⟨hT.1, fun h hh => hT.2 h ?_⟩
    intro h0
    apply hh
    simp only at h0
    rw [hflat, h0, PosOneCell.app_zero, LinearMap.zero_apply]
  obtain ⟨-, hiff⟩ := GlobalTheory.T.isQuotInt_cells_alt k n c 1 le_rfl hc ν (rescale ν b m) μG L.J hJ _ hinv hmod T hcov
  refine (hiff _).2 (Finset.sum_congr rfl fun h _ => ?_)
  obtain ⟨-, -, -, -, hm⟩ := GlobalTheory.UnfoldedEntries.cosetMeasure (ν := ν) n c hc L.J hJ h
  obtain ⟨-, -, -, hresc, -⟩ := hm m inferInstance
  have hvc : volCell ν (rescale ν b m) 1 L.J h = volR ν (rescale ν b m) (Cgrp L.J h) := by
    unfold volCell volR
    refine lintegral_congr fun g => ?_
    congr 1
    ext u
    simp only [Set.mem_setOf_eq, mem_Cgrp]
    refine ⟨fun H => ⟨?_, H⟩, fun H => H.2⟩
    exact (R k n c 1).mul_mem (Subgroup.mem_sup_left (MonoidHom.mem_range.2 ⟨g, rfl⟩)) (Subgroup.mem_sup_right u.2)
  have hxi : xi ψ ν μ Φ.1 L.J b h' h = (((volNat ν b (Cgrp L.J h))⁻¹ : ℝ) : ℂ) • flat ψ ν μ Φ.1 h' h := rfl
  rw [hxi, PosOneCell.app_smul, LinearMap.smul_apply, smul_eq_mul, hflat, hvc, hresc b, hJ1, ENNReal.toReal_one]
  push_cast
  ring

end GlobalTheory.PosOneCell
end
end

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.PosOne
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ IsFJ Represents)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO rescale)
attribute [-instance] GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix Formalism.DoubleCosetMeasures.instMeasMat

namespace GlobalTheory.PosOne

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}
  {A : Type} [AddCommGroup A] [Module ℂ A]

private lemma isHaarMeasure_framePositiveSum_rescale (ν : Measure k)
    [ν.IsAddHaarMeasure] (b : GL (n ⊕ Fin c) k) (m : Measure (GL n k)) [m.IsHaarMeasure] :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b m).IsHaarMeasure := by
  have hpos := ENNReal.toReal_pos_iff.mp (_root_.GlobalTheory.StepData.volN_stabLat ν b)
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale
  exact Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.mpr hpos.2.ne)
    (ENNReal.inv_ne_top.mpr hpos.1.ne')

private lemma posOne_toOne_zero (ν : Measure k)
    (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (P : ℕ) :
    _root_.GlobalTheory.PosOne.toOne ν σ P (fun _ => 0) = fun _ => 0 := by
  have hdown : ∀ p, _root_.GlobalTheory.RootEx.exDown ν p σ (fun _ => (0 : ℂ)) = fun _ => 0 := by
    intro p
    funext v
    simp [_root_.GlobalTheory.RootEx.exDown]
  have key : ∀ m : ℕ, _root_.GlobalTheory.PosOne.toOne ν σ (m + 1) (fun _ => 0) = fun _ => 0 := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [show m + 1 + 1 = m + 2 from rfl, _root_.GlobalTheory.PosOne.toOne_succ, hdown, ih]
  cases P with
  | zero => rfl
  | succ m => exact key m

private lemma fourierJacobiAverage_app_toOne_comm {X : Type} [TopologicalSpace X]
    (ν : Measure k) (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (P : ℕ)
    (B B₁ : _root_.GlobalTheory.SplitWeil.SB X →ₗ[ℂ] A →ₗ[ℂ] ℂ)
    (hB : ∀ Ψ v, B₁ Ψ v = _root_.GlobalTheory.PosOne.toOne ν σ P (B Ψ) v) (x : X → ℂ) (v : A) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app B₁ x v =
      _root_.GlobalTheory.PosOne.toOne ν σ P (fun w => _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app B x w) v := by
  by_cases hx : x ∈ _root_.GlobalTheory.SplitWeil.SB X
  · simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app, dif_pos hx]
    exact hB _ _
  · simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app, dif_neg hx, LinearMap.zero_apply]
    rw [posOne_toOne_zero]

private lemma fourierJacobiAverage_app_of_mem_SB {X V : Type} [TopologicalSpace X]
    [AddCommGroup V] [Module ℂ V] (B : _root_.GlobalTheory.SplitWeil.SB X →ₗ[ℂ] V) {x : X → ℂ}
    (hx : x ∈ _root_.GlobalTheory.SplitWeil.SB X) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app B x = B ⟨x, hx⟩ := by
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app, dif_pos hx]

private lemma fourierJacobiAverage_app_of_not_mem_SB {X V : Type} [TopologicalSpace X]
    [AddCommGroup V] [Module ℂ V] (B : _root_.GlobalTheory.SplitWeil.SB X →ₗ[ℂ] V) {x : X → ℂ}
    (hx : x ∉ _root_.GlobalTheory.SplitWeil.SB X) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app B x = 0 := by
  simp only [_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app, dif_neg hx]

private lemma fourierJacobiAverage_app_zero_map {X V : Type} [TopologicalSpace X]
    [AddCommGroup V] [Module ℂ V] (x : X → ℂ) :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app (0 : _root_.GlobalTheory.SplitWeil.SB X →ₗ[ℂ] V) x = 0 := by
  unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app
  split_ifs <;> rfl
end

theorem _root_.GlobalTheory.PosOne.oneDbl_iff_sum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ) (_ : c + 1 = 2 * ρ) (ψ : AddChar k Circle) (_ : Continuous ψ) (_ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) (ν : Measure k) (_ : _root_.GlobalTheory.SplitWeil.IsUnitVol ν) (μ₁ μ₂ : kˣ →* ℂˣ) (_ : IsOpen (μ₁.ker : Set kˣ)) (_ : IsOpen (μ₂.ker : Set kˣ)) (m₁ : Measure (GL n₁ k)) [m₁.IsHaarMeasure] (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) [G₁.IsHaarMeasure] (m₂ : Measure (GL n₂ k)) [m₂.IsHaarMeasure] (G₂ : Measure (GL (n₂ ⊕ Fin c) k)) [G₂.IsHaarMeasure] (L₁ : _root_.GlobalTheory.StepData.Level (GL (n₁ ⊕ Fin (c + 1)) k)) (L₂ : _root_.GlobalTheory.StepData.Level (GL (n₂ ⊕ Fin c) k)) (_ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO L₁.J) (_ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsCO L₂.J) (_ : G₁ L₁.J = 1) (_ : G₂ L₂.J = 1) (b₁ : GL (n₁ ⊕ Fin (c + 1)) k) (b₂ : GL (n₂ ⊕ Fin c) k) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A) (_ : _root_.GlobalTheory.SplitWeil.IsSmoothRep σ) (T : _root_.GlobalTheory.SplitWeil.SB (Matrix n₁ n₀ k) →ₗ[ℂ] _root_.GlobalTheory.SplitWeil.SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ) (_ : _root_.GlobalTheory.PosOne.TriPos ψ μ₁ μ₂ ρ σ T) (F : A) (_ : ∀ j : L₂.J, σ (j : GL (n₂ ⊕ Fin c) k) F = (L₂.lam j : ℂ) • F) (Φ₁ : _root_.GlobalTheory.SplitWeil.SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (Φ₂ : _root_.GlobalTheory.SplitWeil.SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)) (_ : ∀ j : L₁.J, _root_.GlobalTheory.SplitWeil.om μ₁ 1 (j : GL (n₁ ⊕ Fin (c + 1)) k) Φ₁.1 = (((L₁.lam j)⁻¹ : ℂˣ) : ℂ) • Φ₁.1) (_ : _root_.GlobalTheory.StepData.HasTypes μ₂ L₁ L₂ Φ₂.1) (α : GL (n₀ ⊕ Fin (c + 1 + 1)) k) (T₁ : Finset (GL (n₁ ⊕ Fin (c + 1)) k)) (T₂ : Finset (GL (n₂ ⊕ Fin c) k)) (_ : _root_.GlobalTheory.PosOne.Covers 1 L₁.J T₁ fun h => _root_.GlobalTheory.StepData.flat ψ ν μ₁ Φ₁.1 α h) (_ : ∀ γ ∈ T₁, _root_.GlobalTheory.PosOne.Covers 1 L₂.J T₂ fun h => _root_.GlobalTheory.StepData.flat ψ ν μ₂ Φ₂.1 γ h) (z : ℂ), _root_.GlobalTheory.PosOne.OneDbl ψ ν (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₁ m₁) G₁ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₂ m₂) G₂ μ₁ μ₂ ρ σ T F (_root_.GlobalTheory.SplitWeil.om μ₁ α 1 Φ₁.1) Φ₂.1 z ↔ z = ∑ γ ∈ T₁, ∑ β ∈ T₂, (((m₁ (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp L₁.J γ))).toReal⁻¹ * (m₂ (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp L₂.J β))).toReal⁻¹ : ℝ) : ℂ) * _root_.GlobalTheory.PosOne.toOne ν σ ρ (fun v => _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app T (_root_.GlobalTheory.StepData.xi ψ ν μ₁ Φ₁.1 L₁.J b₁ α γ)) (_root_.GlobalTheory.StepData.xi ψ ν μ₂ Φ₂.1 L₂.J b₂ γ β) v) (σ β F) := by
  intro k _ _ _ _ _ _ n₀ n₁ n₂ _ _ _ _ _ _ c ρ hcρ ψ hψ hcond ν hν μ₁ μ₂ hμ₁ hμ₂ m₁ _ G₁ _ m₂ _ G₂ _
    L₁ L₂ hL₁ hL₂ hG₁ hG₂ b₁ b₂ A _ _ σ hσ T hT F hF Φ₁ Φ₂ hΦ₁ hΦ₂ α T₁ T₂ hT₁ hT₂ z
  haveI : ν.IsAddHaarMeasure := hν.1
  have hψ1 : ψ ≠ 1 := hcond.ne_one
  have hsd : _root_.GlobalTheory.SplitWeil.IsSelfDual ψ ν :=
    _root_.GlobalTheory.SplitWeil.isSelfDual_of_isUnitVol ν hcond hν
  have hρ1 : 1 ≤ ρ := by omega
  have hρc : ρ ≤ c := by omega
  haveI : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₁ m₁).IsHaarMeasure :=
    isHaarMeasure_framePositiveSum_rescale ν b₁ m₁
  haveI : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₂ m₂).IsHaarMeasure :=
    isHaarMeasure_framePositiveSum_rescale ν b₂ m₂
  obtain ⟨ρ₁, hρ₁⟩ := (_root_.GlobalTheory.PosOne.isSrc_exists_isSmoothRep k (n₁ ⊕ Fin (c + 1)) (n₂ ⊕ Fin c) μ₂ hμ₂).1
  have hρ₁s := (_root_.GlobalTheory.PosOne.isSrc_exists_isSmoothRep k (n₁ ⊕ Fin (c + 1)) (n₂ ⊕ Fin c) μ₂ hμ₂).2 ρ₁ hρ₁
  obtain ⟨b, hb, -, hbone⟩ := _root_.GlobalTheory.PosOne.MidVertex.exists_bilPos_mid k n₀ n₁ n₂ c ρ hcρ ψ hψ hψ1 ν hsd
    μ₁ μ₂ hμ₁ hμ₂ m₁ G₁ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₂ m₂) G₂ A σ hσ T hT F ρ₁ hρ₁
  obtain ⟨B', hB'eq, hB'⟩ := (_root_.GlobalTheory.PosOne.toOne_isPosOne k n₁ n₀ (c + 1) ρ hρ1 (by omega)
    ψ hψ hψ1 ν _ ρ₁ hρ₁s).2 μ₁ hμ₁ b hb
  have hin : ∀ Ψ, ∃ B₁ : _root_.GlobalTheory.SplitWeil.SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ,
      (∀ Ψ' v, B₁ Ψ' v = _root_.GlobalTheory.PosOne.toOne ν σ ρ (T Ψ Ψ') v) ∧
        _root_.GlobalTheory.PosOne.BilPos ψ μ₂ 1 σ B₁ := fun Ψ =>
    (_root_.GlobalTheory.PosOne.toOne_isPosOne k n₂ n₁ c ρ hρ1 hρc ψ hψ hψ1 ν A σ hσ).2 μ₂ hμ₂ (T Ψ)
      (hT.1 Ψ)
  choose B₁ hB₁eq hB₁ using hin
  have uniq₁ := fun f => (_root_.GlobalTheory.QuotInt.quotInt_unique_exists k n₁ (c + 1) 1 le_rfl
    (by omega) ν (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₁ m₁) G₁ f).1
  have uniq₂ := fun f => (_root_.GlobalTheory.QuotInt.quotInt_unique_exists k n₂ c 1 le_rfl
    (by omega) ν (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₂ m₂) G₂ f).1
  have hinteg : ∀ Ψ Φb, _root_.GlobalTheory.PosOne.tIntOne ψ ν μ₂ ρ σ (T Ψ) F Φb =
      _root_.GlobalTheory.PosOne.tInt ψ ν μ₂ 1 σ (B₁ Ψ) F Φb := by
    intro Ψ Φb
    funext h
    simp only [_root_.GlobalTheory.PosOne.tIntOne, _root_.GlobalTheory.PosOne.tInt]
    exact (fourierJacobiAverage_app_toOne_comm ν σ ρ (T Ψ) (B₁ Ψ) (hB₁eq Ψ) _ _).symm
  have hinner : ∀ h Ψ, _root_.GlobalTheory.RootEx.IsQuotInt ν (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₂ m₂)
      G₂ 1 (_root_.GlobalTheory.PosOne.tInt ψ ν μ₂ 1 σ (B₁ Ψ) F (_root_.GlobalTheory.SplitWeil.om μ₂ h 1 Φ₂.1))
      (B' Ψ (ρ₁ h Φ₂)) := by
    intro h Ψ
    have := hbone Ψ (ρ₁ h Φ₂)
    rwa [hρ₁ h Φ₂, ← hB'eq Ψ, hinteg Ψ] at this
  have hF' : ∀ j : L₁.J, ρ₁ (j : GL (n₁ ⊕ Fin (c + 1)) k) Φ₂ = (L₁.lam j : ℂ) • Φ₂ := by
    intro j
    apply Subtype.ext
    rw [hρ₁, Submodule.coe_smul]
    exact hΦ₂.1 j
  have houter := _root_.GlobalTheory.PosOneCell.quotInt_posOne k n₁ n₀ (c + 1) (by omega) ψ hψ hcond ν hν
    μ₁ hμ₁ m₁ G₁ L₁ hL₁ hG₁ b₁ _ ρ₁ hρ₁s B' hB' Φ₂ hF' Φ₁ hΦ₁ α T₁ hT₁
  have hinner_sum : ∀ γ ∈ T₁, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app B' (_root_.GlobalTheory.StepData.xi ψ ν μ₁ Φ₁.1 L₁.J b₁ α γ) (ρ₁ γ Φ₂) = ∑ β ∈ T₂, (((m₂ (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp L₂.J β))).toReal⁻¹ : ℝ) : ℂ) * _root_.GlobalTheory.PosOne.toOne ν σ ρ (fun v => _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app T (_root_.GlobalTheory.StepData.xi ψ ν μ₁ Φ₁.1 L₁.J b₁ α γ)) (_root_.GlobalTheory.StepData.xi ψ ν μ₂ Φ₂.1 L₂.J b₂ γ β) v) (σ β F) := by
    intro γ hγ
    by_cases hx : _root_.GlobalTheory.StepData.xi ψ ν μ₁ Φ₁.1 L₁.J b₁ α γ ∈ _root_.GlobalTheory.SplitWeil.SB _
    · rw [fourierJacobiAverage_app_of_mem_SB B' hx, fourierJacobiAverage_app_of_mem_SB T hx]
      have hi := _root_.GlobalTheory.PosOneCell.quotInt_posOne k n₂ n₁ c (by omega) ψ hψ hcond ν hν
        μ₂ hμ₂ m₂ G₂ L₂ hL₂ hG₂ b₂ A σ hσ (B₁ ⟨_, hx⟩) (hB₁ _) F hF Φ₂ hΦ₂.2 γ T₂ (hT₂ γ hγ)
      rw [uniq₂ _ _ _ (hinner γ ⟨_, hx⟩) hi]
      refine Finset.sum_congr rfl fun β _ => ?_
      rw [fourierJacobiAverage_app_toOne_comm ν σ ρ (T ⟨_, hx⟩) (B₁ ⟨_, hx⟩) (hB₁eq _)]
    · simp only [fourierJacobiAverage_app_of_not_mem_SB B' hx,
        fourierJacobiAverage_app_of_not_mem_SB T hx, fourierJacobiAverage_app_zero_map,
        LinearMap.zero_apply, posOne_toOne_zero, mul_zero,
        Finset.sum_const_zero]
  have hsum : ∀ S, _root_.GlobalTheory.RootEx.IsQuotInt ν (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν b₁ m₁) G₁ 1
      (_root_.GlobalTheory.PosOne.tInt ψ ν μ₁ 1 ρ₁ B' Φ₂ (_root_.GlobalTheory.SplitWeil.om μ₁ α 1 Φ₁.1)) S →
      S = ∑ γ ∈ T₁, ∑ β ∈ T₂, (((m₁ (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp L₁.J γ))).toReal⁻¹ * (m₂ (_root_.GlobalTheory.StepData.prX (_root_.GlobalTheory.StepData.Cgrp L₂.J β))).toReal⁻¹ : ℝ) : ℂ) * _root_.GlobalTheory.PosOne.toOne ν σ ρ (fun v => _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app (_root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app T (_root_.GlobalTheory.StepData.xi ψ ν μ₁ Φ₁.1 L₁.J b₁ α γ)) (_root_.GlobalTheory.StepData.xi ψ ν μ₂ Φ₂.1 L₂.J b₂ γ β) v) (σ β F) := by
    intro S hS
    rw [uniq₁ _ _ _ hS houter]
    refine Finset.sum_congr rfl fun γ hγ => ?_
    rw [hinner_sum γ hγ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    push_cast
    ring
  have hf : ∀ w : GL (n₁ ⊕ Fin (c + 1)) k → _root_.GlobalTheory.SplitWeil.SB (Matrix n₁ n₀ k) →ₗ[ℂ] ℂ,
      (∀ h Ψ, w h Ψ = B' Ψ (ρ₁ h Φ₂)) →
      (fun h => _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app (w h) (_root_.GlobalTheory.RootEx.opE ψ ν 1
        (_root_.GlobalTheory.SplitWeil.om μ₁ 1 h (_root_.GlobalTheory.SplitWeil.om μ₁ α 1 Φ₁.1)))) =
      _root_.GlobalTheory.PosOne.tInt ψ ν μ₁ 1 ρ₁ B' Φ₂ (_root_.GlobalTheory.SplitWeil.om μ₁ α 1 Φ₁.1) := by
    intro w hw
    funext h
    simp only [_root_.GlobalTheory.PosOne.tInt, _root_.GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage.app]
    split_ifs
    · exact hw _ _
    · rfl
  unfold _root_.GlobalTheory.PosOne.OneDbl
  constructor
  · rintro ⟨w, hw, hz⟩
    have hwv : ∀ h Ψ, w h Ψ = B' Ψ (ρ₁ h Φ₂) := by
      intro h Ψ
      have hwh := hw h Ψ
      rw [hinteg] at hwh
      exact uniq₂ _ _ _ hwh (hinner h Ψ)
    rw [hf w hwv] at hz
    exact hsum z hz
  · intro hz
    refine ⟨fun h => B'.flip (ρ₁ h Φ₂), fun h Ψ => ?_, ?_⟩
    · rw [hinteg]
      exact hinner h Ψ
    · rw [hf _ (fun h Ψ => rfl), hz, ← hsum _ houter]
      exact houter

end GlobalTheory.PosOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricDoubleIntegralsPositionOneEqCellSum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix Formalism.DoubleCosetMeasures.instMeasMat

noncomputable section
namespace GlobalTheory.PosOne
open scoped ENNReal

attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace

section Scale
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
  [BorelSpace k]

theorem isQuotInt_smul_measure {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {ν : Measure k} {μX : Measure (GL n k)}
    {μG : Measure (GL (n ⊕ Fin c) k)} {p : ℕ} {f : GL (n ⊕ Fin c) k → ℂ} {z : ℂ} (a : ℝ≥0∞)
    (h : IsQuotInt ν μX μG p f z) : IsQuotInt ν μX (a • μG) p f ((a.toReal : ℂ) * z) := by
  obtain ⟨F, hF, hf, hz⟩ := h
  refine ⟨F, hF, hf, ?_⟩
  rw [integral_smul_measure, hz, Complex.real_smul]

theorem isQuotInt_const_mul {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {ν : Measure k} {μX : Measure (GL n k)}
    {μG : Measure (GL (n ⊕ Fin c) k)} {p : ℕ} {f : GL (n ⊕ Fin c) k → ℂ} {z : ℂ} (b : ℂ)
    (h : IsQuotInt ν μX μG p f z) : IsQuotInt ν μX μG p (fun x => b * f x) (b * z) := by
  obtain ⟨F, hF, hf, hz⟩ := h
  refine ⟨fun x => b * F x, (SB _).smul_mem b hF, fun x => ?_, ?_⟩
  · dsimp only
    rw [hf x, ← integral_const_mul]
    congr 1
    funext g
    exact (integral_const_mul _ _).symm
  · rw [hz, integral_const_mul]

theorem app_smul {X V : Type} [TopologicalSpace X] [AddCommGroup V] [Module ℂ V] (b : ℂ) (l : SB X →ₗ[ℂ] V)
    (f : X → ℂ) : app (b • l) f = b • app l f := by
  unfold app
  split_ifs <;> simp

theorem oneDbl_smul {n₀ n₁ n₂ : Type} [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂]
    [DecidableEq n₂] {c : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A] {ψ : AddChar k Circle} {ν : Measure k}
    {m₁ : Measure (GL n₁ k)} {G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)} {m₂ : Measure (GL n₂ k)}
    {G₂ : Measure (GL (n₂ ⊕ Fin c) k)} {μ₁ μ₂ : kˣ →* ℂˣ} {ρ : ℕ} {σ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A}
    {T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ} {F : A}
    {Φ₁ : Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ}
    {Φ₂ : Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k → ℂ} {z : ℂ} (a b : ℝ≥0∞)
    (h : OneDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ σ T F Φ₁ Φ₂ z) :
    OneDbl ψ ν m₁ (a • G₁) m₂ (b • G₂) μ₁ μ₂ ρ σ T F Φ₁ Φ₂ ((a.toReal : ℂ) * ((b.toReal : ℂ) * z)) := by
  obtain ⟨w, hw, hz⟩ := h
  refine ⟨fun x => (b.toReal : ℂ) • w x, fun x Ψ => ?_, ?_⟩
  · exact isQuotInt_smul_measure b (hw x Ψ)
  · have := isQuotInt_smul_measure a (isQuotInt_const_mul (b.toReal : ℂ) hz)
    convert this using 2 with x
    rw [app_smul, smul_eq_mul]

theorem relIndex_mul_measure_KO {Y : Type} [Fintype Y] [DecidableEq Y] (G : Measure (GL Y k)) [G.IsHaarMeasure]
    (hK : G (KO k Y) = 1) (J : Subgroup (GL Y k)) (hJ : IsCO J) (hle : J ≤ KO k Y) :
    (J.relIndex (KO k Y) : ℝ≥0∞) * G J = 1 ∧ J.relIndex (KO k Y) ≠ 0 := by
  haveI : BorelSpace (GL Y k) := GlobalTheory.SplitFlip.borel_GL
  have hc : IsCompact (KO k Y : Set (GL Y k)) := GlobalTheory.SplitFlip.isCompact_KO
  haveI : CompactSpace (KO k Y) := isCompact_iff_compactSpace.1 hc
  have ho : IsOpen ((J.subgroupOf (KO k Y) : Subgroup (KO k Y)) : Set (KO k Y)) :=
    hJ.1.preimage continuous_subtype_val
  haveI : Finite (KO k Y ⧸ J.subgroupOf (KO k Y)) := Subgroup.quotient_finite_of_isOpen _ ho
  haveI : (J.subgroupOf (KO k Y)).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine ⟨?_, Subgroup.FiniteIndex.index_ne_zero⟩
  rw [GlobalTheory.IndexVolume.relIndex_mul_measure_subgroup J (KO k Y) hle hJ.1.measurableSet G, hK]

theorem rescale_one_eq {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (hc : 1 ≤ c) {ν : Measure k} (hν : IsUnitVol ν)
    (m : Measure (GL n k)) : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale ν (1 : GL (n ⊕ Fin c) k) m = m := by
  have h := GlobalTheory.T.rootExchangeUnipotentHaar_integralPoints_eq_one k n c 1 le_rfl hc ν hν
  have e : (((stabLat (1 : GL (n ⊕ Fin c) k)).subgroupOf (N k n c 1) : Subgroup (N k n c 1)) : Set (N k n c 1)) =
      {u : N k n c 1 | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} := by
    ext u
    simp [Subgroup.mem_subgroupOf, mem_stabLat]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.rescale
  rw [e, h, inv_one, one_smul]

end Scale

set_option maxHeartbeats 4000000 in
theorem comb_eq_sum_cells : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ),
    c + 1 = 2 * ρ → ∀ (ψ : AddChar k Circle), Continuous ψ → HasConductor ψ 1 → ∀ (ν : Measure k), IsUnitVol ν →
  ∀ (μ₁ μ₂ : kˣ →* ℂˣ), IsOpen (μ₁.ker : Set kˣ) → IsOpen (μ₂.ker : Set kˣ) →
  ∀ (m₁ : Measure (GL n₁ k)) (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) (m₂ : Measure (GL n₂ k))
    (G₂ : Measure (GL (n₂ ⊕ Fin c) k)), m₁.IsHaarMeasure → G₁.IsHaarMeasure → m₂.IsHaarMeasure → G₂.IsHaarMeasure →
    G₁ (KO k (n₁ ⊕ Fin (c + 1))) = 1 → G₂ (KO k (n₂ ⊕ Fin c)) = 1 →
  ∀ (L₀ : Level (GL (n₀ ⊕ Fin (c + 1 + 1)) k)) (L₁ : Level (GL (n₁ ⊕ Fin (c + 1)) k)) (L₂ : Level (GL (n₂ ⊕ Fin c) k)),
    IsCO L₁.J → IsCO L₂.J → L₁.J ≤ KO k _ → L₂.J ≤ KO k _ →
  ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (τ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A), IsSmoothRep τ →
  ∀ (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), TriPos ψ μ₁ μ₂ ρ τ T →
  ∀ (F : A), (∀ j : L₂.J, τ (j : GL (n₂ ⊕ Fin c) k) F = (L₂.lam j : ℂ) • F) →
  ∀ (P₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (P₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)),
    HasTypes μ₁ L₀ L₁ P₁.1 → HasTypes μ₂ L₁ L₂ P₂.1 →
  ∀ (α : GL (n₀ ⊕ Fin (c + 1 + 1)) k) (A₁ : Finset (GL (n₁ ⊕ Fin (c + 1)) k)) (A₂ : Finset (GL (n₂ ⊕ Fin c) k)),
    Covers 1 L₁.J A₁ (fun h => GlobalTheory.StepData.flat ψ ν μ₁ P₁.1 α h) → (∀ γ ∈ A₁, Covers 1 L₂.J A₂ fun h => GlobalTheory.StepData.flat ψ ν μ₂ P₂.1 γ h) →
  ∀ (e₀ : GL (n₀ ⊕ Fin (c + 1 + 1)) k →₀ ℂ), IsOneComb ψ ν (ρ + 1) L₀ α e₀ →
  ∀ (e₂ : GL (n₂ ⊕ Fin c) k → (GL (n₂ ⊕ Fin c) k →₀ ℂ)), (∀ β ∈ A₂, IsOneComb ψ ν ρ L₂ β (e₂ β)) →
  ∀ (z : GL (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ),
    (∀ a ∈ e₀.support, SymDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ τ T F (om μ₁ a 1 P₁.1) P₂.1 (z a)) →
    comb e₀ z = ((L₁.J.relIndex (KO k _) : ℂ) * (L₂.J.relIndex (KO k _) : ℂ))⁻¹ *
      ∑ γ ∈ A₁, ∑ β ∈ A₂, ((((m₁ (prX (Cgrp L₁.J γ))).toReal⁻¹ * (m₂ (prX (Cgrp L₂.J β))).toReal⁻¹ : ℝ) : ℂ) *
        comb (e₂ β) fun b => app (app T (xi ψ ν μ₁ P₁.1 L₁.J 1 α γ)) (xi ψ ν μ₂ P₂.1 L₂.J 1 γ β) (τ b F)) := by
  intro k _ _ _ _ _ _ n₀ n₁ n₂ _ _ _ _ _ _ c ρ hcρ ψ hψ hcond ν hν μ₁ μ₂ ho₁ ho₂ m₁ G₁ m₂ G₂ hm₁ hG₁ hm₂ hG₂ hK₁ hK₂
    L₀ L₁ L₂ hco₁ hco₂ hle₁ hle₂ A _ _ τ hτ T hT F hF P₁ P₂ hty₁ hty₂ α A₁ A₂ hcov₁ hcov₂ e₀ he₀ e₂ he₂ z hz
  haveI := hm₁
  haveI := hG₁
  haveI := hm₂
  haveI := hG₂
  have hne : ψ ≠ 1 := hcond.ne_one
  have hsd : IsSelfDual ψ ν := ((GlobalTheory.SplitWeil.selfDual_measure k ψ hψ hne).2.1 hcond ν).1 hν
  obtain ⟨⟨ρ₀, hρ₀⟩, hsm⟩ := GlobalTheory.PosOne.isSrc_exists_isSmoothRep k (n₀ ⊕ Fin (c + 1 + 1)) (n₁ ⊕ Fin (c + 1)) μ₁ ho₁
  have hsm₀ := hsm ρ₀ hρ₀

  have hcomb : ∀ f : GL (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ,
      comb (e₀.mapDomain (· * α⁻¹)) (fun g => f (g * α)) = comb e₀ f := by
    intro f
    unfold comb
    rw [Finsupp.sum_mapDomain_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
    simp only [inv_mul_cancel_right]
  have hsrc : SrcComb ψ ν (ρ + 1) ρ₀ (ρ₀ α P₁) (e₀.mapDomain (· * α⁻¹)) := by
    intro L hL
    have hP : ∀ j : L₀.J, ρ₀ (j : GL (n₀ ⊕ Fin (c + 1 + 1)) k) P₁ = (L₀.lam j : ℂ) • P₁ := fun j =>
      Subtype.ext ((hρ₀ _ _).trans (hty₁.1 j))
    rw [he₀ _ ρ₀ hsm₀ L hL P₁ hP, ← hcomb]
    congr 1
    funext g
    rw [map_mul, Module.End.mul_apply]
  have hsym : ∀ g ∈ (e₀.mapDomain (· * α⁻¹)).support,
      SymDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ τ T F (om μ₁ g 1 (ρ₀ α P₁).1) P₂.1 (z (g * α)) := by
    intro g hg
    classical
    rw [Finsupp.mapDomain_support_of_injective (mul_left_injective α⁻¹)] at hg
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hg
    have e : om μ₁ (a * α⁻¹) 1 (ρ₀ α P₁).1 = om μ₁ (a * α⁻¹ * α) 1 P₁.1 := by
      rw [← hρ₀, ← hρ₀, map_mul ρ₀ (a * α⁻¹) α, Module.End.mul_apply]
    rw [e]
    simpa only [inv_mul_cancel_right] using hz a ha
  have h1 := GlobalTheory.T.positionOne_of_symmetricDoubleIntegral_finite k n₀ n₁ n₂ c ρ hcρ ψ hψ hne ν hsd μ₁ μ₂ ho₁ ho₂ m₁ G₁ m₂ G₂ A τ hτ T hT F ρ₀ hρ₀ (ρ₀ α P₁) P₂
    (e₀.mapDomain (· * α⁻¹)) hsrc (fun g => z (g * α)) hsym
  rw [hcomb, hρ₀] at h1

  obtain ⟨hi₁, hn₁⟩ := relIndex_mul_measure_KO G₁ hK₁ L₁.J hco₁ hle₁
  obtain ⟨hi₂, hn₂⟩ := relIndex_mul_measure_KO G₂ hK₂ L₂.J hco₂ hle₂
  set r₁ : ℝ≥0∞ := (L₁.J.relIndex (KO k (n₁ ⊕ Fin (c + 1))) : ℝ≥0∞) with hr₁
  set r₂ : ℝ≥0∞ := (L₂.J.relIndex (KO k (n₂ ⊕ Fin c)) : ℝ≥0∞) with hr₂
  haveI : (r₁ • G₁).IsHaarMeasure := Measure.IsHaarMeasure.smul G₁ (by simpa [hr₁] using hn₁) (by simp [hr₁])
  haveI : (r₂ • G₂).IsHaarMeasure := Measure.IsHaarMeasure.smul G₂ (by simpa [hr₂] using hn₂) (by simp [hr₂])
  have h2 := oneDbl_smul r₁ r₂ h1
  have hc : 1 ≤ c := by omega
  rw [← rescale_one_eq (n := n₁) (c := c + 1) (by omega) hν m₁, ← rescale_one_eq (n := n₂) hc hν m₂] at h2
  have h3 := (GlobalTheory.PosOne.oneDbl_iff_sum k n₀ n₁ n₂ c ρ hcρ ψ hψ hcond ν hν μ₁ μ₂ ho₁ ho₂ m₁ (r₁ • G₁) m₂ (r₂ • G₂) L₁ L₂
    hco₁ hco₂ (by rw [Measure.smul_apply, smul_eq_mul, hi₁]) (by rw [Measure.smul_apply, smul_eq_mul, hi₂]) 1 1 A τ hτ T hT F hF
    P₁ P₂ hty₁.2 hty₂ α A₁ A₂ hcov₁ hcov₂ _).1 h2

  have hex : ∀ γ ∈ A₁, ∀ β ∈ A₂, toOne ν τ ρ (fun v => app (app T (xi ψ ν μ₁ P₁.1 L₁.J 1 α γ)) (xi ψ ν μ₂ P₂.1 L₂.J 1 γ β) v)
      (τ β F) = comb (e₂ β) fun b => app (app T (xi ψ ν μ₁ P₁.1 L₁.J 1 α γ)) (xi ψ ν μ₂ P₂.1 L₂.J 1 γ β) (τ b F) := by
    intro γ _ β hβ
    refine he₂ β hβ A τ hτ _ ?_ F hF
    intro g hg v
    unfold app
    split_ifs with h₁ h₂
    · exact (hT.1 _).1 _ g hg v
    · simp
    · simp
  have hr : ((r₁.toReal : ℂ) * (r₂.toReal : ℂ)) = ((L₁.J.relIndex (KO k _) : ℂ) * (L₂.J.relIndex (KO k _) : ℂ)) := by
    simp [hr₁, hr₂]
  have hr0 : ((L₁.J.relIndex (KO k (n₁ ⊕ Fin (c + 1))) : ℂ) * (L₂.J.relIndex (KO k (n₂ ⊕ Fin c)) : ℂ)) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 hn₁) (Nat.cast_ne_zero.2 hn₂)
  rw [← mul_assoc, hr] at h3
  rw [eq_inv_mul_iff_mul_eq₀ hr0, h3]
  refine Finset.sum_congr rfl fun γ hγ => Finset.sum_congr rfl fun β hβ => ?_
  rw [hex γ hγ β hβ]

end GlobalTheory.PosOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricDoubleIntegralsPositionOneEqCellSumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [-instance] GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix Formalism.DoubleCosetMeasures.instMeasMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricDoubleIntegrals_positionOne_eq_cellSum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n₀ n₁ n₂ : Type) [Fintype n₀] [DecidableEq n₀] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂] (c ρ : ℕ),
    c + 1 = 2 * ρ → ∀ (ψ : AddChar k Circle), Continuous ψ → HasConductor ψ 1 → ∀ (ν : Measure k), IsUnitVol ν →
  ∀ (μ₁ μ₂ : kˣ →* ℂˣ), IsOpen (μ₁.ker : Set kˣ) → IsOpen (μ₂.ker : Set kˣ) →
  ∀ (m₁ : Measure (GL n₁ k)) (G₁ : Measure (GL (n₁ ⊕ Fin (c + 1)) k)) (m₂ : Measure (GL n₂ k))
    (G₂ : Measure (GL (n₂ ⊕ Fin c) k)), m₁.IsHaarMeasure → G₁.IsHaarMeasure → m₂.IsHaarMeasure → G₂.IsHaarMeasure →
    G₁ (KO k (n₁ ⊕ Fin (c + 1))) = 1 → G₂ (KO k (n₂ ⊕ Fin c)) = 1 →
  ∀ (L₀ : Level (GL (n₀ ⊕ Fin (c + 1 + 1)) k)) (L₁ : Level (GL (n₁ ⊕ Fin (c + 1)) k)) (L₂ : Level (GL (n₂ ⊕ Fin c) k)),
    IsCO L₁.J → IsCO L₂.J → L₁.J ≤ KO k _ → L₂.J ≤ KO k _ →
  ∀ (A : Type) [AddCommGroup A] [Module ℂ A] (τ : Representation ℂ (GL (n₂ ⊕ Fin c) k) A), IsSmoothRep τ →
  ∀ (T : SB (Matrix n₁ n₀ k) →ₗ[ℂ] SB (Matrix n₂ n₁ k) →ₗ[ℂ] A →ₗ[ℂ] ℂ), TriPos ψ μ₁ μ₂ ρ τ T →
  ∀ (F : A), (∀ j : L₂.J, τ (j : GL (n₂ ⊕ Fin c) k) F = (L₂.lam j : ℂ) • F) →
  ∀ (P₁ : SB (Matrix (n₁ ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k)) (P₂ : SB (Matrix (n₂ ⊕ Fin c) (n₁ ⊕ Fin (c + 1)) k)),
    HasTypes μ₁ L₀ L₁ P₁.1 → HasTypes μ₂ L₁ L₂ P₂.1 →
  ∀ (α : GL (n₀ ⊕ Fin (c + 1 + 1)) k) (A₁ : Finset (GL (n₁ ⊕ Fin (c + 1)) k)) (A₂ : Finset (GL (n₂ ⊕ Fin c) k)),
    Covers 1 L₁.J A₁ (fun h => GlobalTheory.StepData.flat ψ ν μ₁ P₁.1 α h) → (∀ γ ∈ A₁, Covers 1 L₂.J A₂ fun h => GlobalTheory.StepData.flat ψ ν μ₂ P₂.1 γ h) →
  ∀ (e₀ : GL (n₀ ⊕ Fin (c + 1 + 1)) k →₀ ℂ), IsOneComb ψ ν (ρ + 1) L₀ α e₀ →
  ∀ (e₂ : GL (n₂ ⊕ Fin c) k → (GL (n₂ ⊕ Fin c) k →₀ ℂ)), (∀ β ∈ A₂, IsOneComb ψ ν ρ L₂ β (e₂ β)) →
  ∀ (z : GL (n₀ ⊕ Fin (c + 1 + 1)) k → ℂ),
    (∀ a ∈ e₀.support, SymDbl ψ ν m₁ G₁ m₂ G₂ μ₁ μ₂ ρ τ T F (om μ₁ a 1 P₁.1) P₂.1 (z a)) →
    comb e₀ z = ((L₁.J.relIndex (KO k _) : ℂ) * (L₂.J.relIndex (KO k _) : ℂ))⁻¹ *
      ∑ γ ∈ A₁, ∑ β ∈ A₂, ((((m₁ (prX (Cgrp L₁.J γ))).toReal⁻¹ * (m₂ (prX (Cgrp L₂.J β))).toReal⁻¹ : ℝ) : ℂ) *
        comb (e₂ β) fun b => app (app T (xi ψ ν μ₁ P₁.1 L₁.J 1 α γ)) (xi ψ ν μ₂ P₂.1 L₂.J 1 γ β) (τ b F)) := by
  first | exact @GlobalTheory.PosOne.comb_eq_sum_cells | exact GlobalTheory.PosOne.comb_eq_sum_cells | (intros; apply GlobalTheory.PosOne.comb_eq_sum_cells <;> assumption)
end
