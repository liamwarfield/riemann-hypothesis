module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.FolnerAbs
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselLevi
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BesselLevi
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSAsm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSD
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NMeasInv

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSF
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubSH
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Measure NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Pointwise

namespace Formalism.L2.S.Pv.HaarSubS

section Abs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]

private theorem lintegral_comp_of_map_eq {μ : Measure G} {φ : G → G} {g : G → ℝ≥0∞} (hφ : Measurable φ) (hμ : μ.map φ = μ)
    (hg : Measurable g) : ∫⁻ x, g (φ x) ∂μ = ∫⁻ x, g x ∂μ := by
  conv_rhs => rw [← hμ]
  rw [lintegral_map hg hφ]

theorem eq_smul_inv {H : Set G} (hHm : MeasurableSet H) (hinvH : ∀ h ∈ H, h⁻¹ ∈ H) {μ ν : Measure G}
    [SFinite μ] [IsProbabilityMeasure ν] (hμc : μ Hᶜ = 0) (hμl : ∀ h ∈ H, μ.map (fun x => h * x) = μ)
    (hνc : ν Hᶜ = 0) (hνl : ∀ h ∈ H, ν.map (fun x => h * x) = ν) :
    μ = μ Set.univ • ν.map (fun x => x⁻¹) := by
  have hae_ν : ∀ᵐ y ∂ν, y ∈ H := (ae_iff (p := fun a => a ∈ H)).mpr hνc
  have hae_μ : ∀ᵐ x ∂μ, x ∈ H := (ae_iff (p := fun a => a ∈ H)).mpr hμc
  apply Measure.ext_of_lintegral
  intro f hf
  have hF : Measurable (Function.uncurry fun y x => f (y⁻¹ * x)) :=
    hf.comp (measurable_fst.inv.mul measurable_snd)
  rw [lintegral_smul_measure, lintegral_map hf (measurable_inv : Measurable fun x : G => x⁻¹)]
  calc ∫⁻ x, f x ∂μ = ∫⁻ y, ∫⁻ x, f x ∂μ ∂ν := by rw [lintegral_const, measure_univ, mul_one]
    _ = ∫⁻ y, ∫⁻ x, f (y⁻¹ * x) ∂μ ∂ν := by
        apply lintegral_congr_ae
        filter_upwards [hae_ν] with y hy
        exact (lintegral_comp_of_map_eq (φ := fun x => y⁻¹ * x) (g := f) (measurable_const_mul _)
          (hμl _ (hinvH y hy)) hf).symm
    _ = ∫⁻ x, ∫⁻ y, f (y⁻¹ * x) ∂ν ∂μ := lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ x, ∫⁻ y, f y⁻¹ ∂ν ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hae_μ] with x hx
        calc ∫⁻ y, f (y⁻¹ * x) ∂ν = ∫⁻ z, f ((x * z)⁻¹ * x) ∂ν :=
              (lintegral_comp_of_map_eq (φ := fun z => x * z) (g := fun y => f (y⁻¹ * x)) (measurable_const_mul x)
                (hνl x hx) (hf.comp (measurable_inv.mul_const x))).symm
          _ = ∫⁻ z, f z⁻¹ ∂ν := lintegral_congr fun z => by rw [show (x * z)⁻¹ * x = z⁻¹ by group]
    _ = μ Set.univ * ∫⁻ y, f y⁻¹ ∂ν := by rw [lintegral_const, mul_comm]

theorem finite_bi {H : Set G} (hHm : MeasurableSet H) (hinvH : ∀ h ∈ H, h⁻¹ ∈ H) {μ ν : Measure G}
    [SigmaFinite μ] [IsProbabilityMeasure ν] (hμc : μ Hᶜ = 0) (hμl : ∀ h ∈ H, μ.map (fun x => h * x) = μ)
    (hνc : ν Hᶜ = 0) (hνl : ∀ h ∈ H, ν.map (fun x => h * x) = ν) :
    IsFiniteMeasure μ ∧ (∀ h ∈ H, μ.map (fun x => x * h) = μ) ∧ μ.map (fun x => x⁻¹) = μ := by
  have hμeq := eq_smul_inv hHm hinvH hμc hμl hνc hνl
  have hνeq := eq_smul_inv hHm hinvH hνc hνl hνc hνl
  rw [measure_univ, one_smul] at hνeq
  have hS : ∀ S, μ S = μ Set.univ * (ν.map (fun x => x⁻¹)) S := by
    intro S
    conv_lhs => rw [hμeq]
    rw [Measure.smul_apply, smul_eq_mul]
  have hfin : μ Set.univ < ⊤ := by
    by_contra hinf
    rw [not_lt, top_le_iff] at hinf
    obtain ⟨i, hi⟩ : ∃ i, μ (spanningSets μ i) ≠ 0 := by
      by_contra hall
      push_neg at hall
      have h0 : μ Set.univ = 0 := by
        rw [← iUnion_spanningSets μ]
        exact measure_iUnion_null hall
      rw [h0] at hinf
      exact ENNReal.zero_ne_top hinf
    have hlt := measure_spanningSets_lt_top μ i
    rw [hS, hinf] at hlt hi
    have h0 : (ν.map (fun x => x⁻¹)) (spanningSets μ i) = 0 := by
      by_contra h
      rw [ENNReal.top_mul h] at hlt
      exact lt_irrefl _ hlt
    rw [h0, mul_zero] at hi
    exact hi rfl
  have hint : ∀ g : G → ℝ≥0∞, Measurable g → ∫⁻ x, g x ∂μ = μ Set.univ * ∫⁻ y, g y⁻¹ ∂ν := by
    intro g hg
    conv_lhs => rw [hμeq]
    simp only [lintegral_smul_measure, smul_eq_mul]
    rw [lintegral_map hg (measurable_inv : Measurable fun x : G => x⁻¹)]
  refine ⟨⟨hfin⟩, ?_, ?_⟩
  · intro h hh
    apply Measure.ext_of_lintegral
    intro f hf
    have hstep : ∫⁻ y, f (y⁻¹ * h) ∂ν = ∫⁻ y, f y⁻¹ ∂ν := by
      calc ∫⁻ y, f (y⁻¹ * h) ∂ν = ∫⁻ z, f ((h * z)⁻¹ * h) ∂ν :=
            (lintegral_comp_of_map_eq (φ := fun z => h * z) (g := fun y => f (y⁻¹ * h)) (measurable_const_mul h)
              (hνl h hh) (hf.comp (measurable_inv.mul_const h))).symm
        _ = ∫⁻ z, f z⁻¹ ∂ν := lintegral_congr fun z => by rw [show (h * z)⁻¹ * h = z⁻¹ by group]
    exact (lintegral_map hf (measurable_mul_const h)).trans
      ((hint (fun x => f (x * h)) (hf.comp (measurable_mul_const h))).trans
        ((congrArg (fun c => μ Set.univ * c) hstep).trans (hint f hf).symm))
  · apply Measure.ext_of_lintegral
    intro f hf
    have hstep2 : ∫⁻ y, f y⁻¹⁻¹ ∂ν = ∫⁻ y, f y⁻¹ ∂ν := by
      simp only [inv_inv]
      conv_lhs => rw [hνeq]
      rw [lintegral_map hf (measurable_inv : Measurable fun x : G => x⁻¹)]
    exact (lintegral_map hf measurable_inv).trans
      ((hint (fun x => f x⁻¹) (hf.comp measurable_inv)).trans
        ((congrArg (fun c => μ Set.univ * c) hstep2).trans (hint f hf).symm))

end Abs

section Glob

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def HuSub (hD : SDecomp) {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) :
    Subgroup X.B.I.Ginf where
  carrier := Hu X u
  mul_mem' {a b} ha hb := (hD D X u).2.2.2.2.2.2.2.2.2.1 a ha b hb
  one_mem' := (hD D X u).2.2.2.2.2.2.2.2.1
  inv_mem' {a} ha := (hD D X u).2.2.2.2.2.2.2.2.2.2.1 a ha

theorem measH_of (hD : SDecomp) : MeasH := by
  intro D X u
  obtain ⟨hsf, _, hc, hl⟩ := X.muH_haar u
  haveI := hsf
  have hd := hD D X u
  have hcomp : IsCompact (Hu X u) := hd.2.2.2.2.2.2.2.1
  have hinv : ∀ a ∈ Hu X u, a⁻¹ ∈ Hu X u := hd.2.2.2.2.2.2.2.2.2.2.1
  have hHm : MeasurableSet (Hu X u) := hcomp.isClosed.measurableSet
  let K := HuSub hD X u
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hcomp
  let μK : Measure K := haarMeasure ⊤
  have hμK1 : μK Set.univ = 1 := by
    have h := haarMeasure_self (G := K) (K₀ := ⊤)
    rwa [TopologicalSpace.PositiveCompacts.coe_top] at h
  let ν : Measure X.B.I.Ginf := μK.map Subtype.val
  haveI : IsProbabilityMeasure ν :=
    ⟨by rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, Set.preimage_univ]; exact hμK1⟩
  have hνc : ν (Hu X u)ᶜ = 0 := by
    rw [Measure.map_apply measurable_subtype_coe hHm.compl]
    have he : (Subtype.val ⁻¹' (Hu X u)ᶜ : Set K) = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
      exact x.2
    rw [he, measure_empty]
  have hνl : ∀ h ∈ Hu X u, ν.map (fun x => h * x) = ν := by
    intro h hh
    rw [Measure.map_map (measurable_const_mul h) measurable_subtype_coe]
    have he : (fun x => h * x) ∘ (Subtype.val : K → X.B.I.Ginf) =
        Subtype.val ∘ (fun y : K => (⟨h, hh⟩ : K) * y) := rfl
    rw [he, ← Measure.map_map measurable_subtype_coe (measurable_const_mul _), map_mul_left_eq_self]
  obtain ⟨h1, h2, h3⟩ := finite_bi hHm hinv hc hl hνc hνl
  exact ⟨h1, h2, h3⟩

end Glob

end Formalism.L2.S.Pv.HaarSubS
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.FolnerJ2
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.FolnerG2
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.FolnerS2
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal Pointwise

namespace Formalism.L2.S.Pv.FolnerS

open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW PI.QuotSetU.UnitaryGroupMassFormula.ModW PI.QuotSetU.UnitaryGroupMassFormula.ModW.MG
  Formalism.L2.S.Pv.FolnerAbs Formalism.L2.SG.Pf.EnergyAbs

variable {k r : ℕ}

abbrev GH (k r : ℕ) : Type := MG (UH (Hpk k r)) (unitary_hermitian_group k r)

def Sg (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Set (GH k r) := {g | g.toM ∈ Sset k r z}

def Cg (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : Set (GH k r) := {g | g.toM ∈ UWset k r z}

def nrm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖M i j‖

theorem continuous_nrm {n : ℕ} : Continuous (nrm (n := n)) :=
  continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    continuous_norm.comp ((continuous_apply j).comp (continuous_apply i))

theorem entry_le_nrm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ‖M i j‖ ≤ nrm M := by
  unfold nrm
  calc ‖M i j‖ ≤ ∑ j', ‖M i j'‖ := Finset.single_le_sum (f := fun j' => ‖M i j'‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', ‖M i' j'‖ := Finset.single_le_sum (f := fun i' => ∑ j', ‖M i' j'‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

def fG (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (g : GH k r) : ℝ :=
  sInf ((fun c : GH k r => nrm ((c * g).toM - 1)) '' Cg k r z)

variable {z : Fin (2 * r + k + 1) → ℂ}

theorem isClosedEmbedding_toM : Topology.IsClosedEmbedding (toM : GH k r → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  isClosedEmbedding_val

theorem isCompact_Cg (hz : inWb k r z) (hT : 0 < Tz k r z) : IsCompact (Cg k r z) :=
  isClosedEmbedding_toM.isCompact_preimage (unitary_weyl_compact k r z hz hT)

theorem isClosed_Sg (hz : inWb k r z) (hT : 0 < Tz k r z) : IsClosed (Sg k r z) :=
  (isClosed_S (unitary_weyl_compact k r z hz hT)).preimage continuous_toM

theorem one_mem_Cg : (1 : GH k r) ∈ Cg k r z := by
  show (1 : GH k r).toM ∈ UWset k r z; rw [toM_one]; exact one_mem_UW

theorem mul_mem_Cg {a b : GH k r} (ha : a ∈ Cg k r z) (hb : b ∈ Cg k r z) : a * b ∈ Cg k r z := by
  show (a * b).toM ∈ UWset k r z; rw [toM_mul]; exact mul_mem_UW ha hb

theorem inv_mem_Cg {a : GH k r} (ha : a ∈ Cg k r z) : a⁻¹ ∈ Cg k r z := by
  show a⁻¹.toM ∈ UWset k r z; rw [toM_inv]; exact inv_mem_UW ha

theorem continuous_fG (hz : inWb k r z) (hT : 0 < Tz k r z) : Continuous (fG k r z) := by
  have h : Continuous (fun p : GH k r × GH k r => nrm ((p.2 * p.1).toM - 1)) :=
    continuous_nrm.comp ((continuous_toM.comp (continuous_snd.mul continuous_fst)).sub continuous_const)
  exact (isCompact_Cg hz hT).continuous_sInf h

theorem fG_mul_left {c₀ : GH k r} (hc₀ : c₀ ∈ Cg k r z) (g : GH k r) : fG k r z (c₀ * g) = fG k r z g := by
  unfold fG
  congr 1
  ext t
  simp only [Set.mem_image]
  constructor
  · rintro ⟨c, hc, rfl⟩; exact ⟨c * c₀, mul_mem_Cg hc hc₀, by rw [mul_assoc]⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c * c₀⁻¹, mul_mem_Cg hc (inv_mem_Cg hc₀), by rw [mul_assoc, inv_mul_cancel_left]⟩

theorem isCompact_ball1 (ρ : ℝ) : IsCompact {x : GH k r | nrm (x.toM - 1) ≤ ρ} := by
  have hK : IsCompact {x : MtM (2 * r + k + 1) | nrm (Matrix.of x - 1) ≤ ρ} := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact isClosed_le (continuous_nrm.comp (continuous_id.sub continuous_const)) continuous_const
    · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨ρ + 1, fun x hx => ?_⟩
      rw [mem_closedBall_zero_iff]
      have hρ : 0 ≤ ρ := le_trans (by unfold nrm; positivity) hx
      refine (pi_norm_le_iff_of_nonneg (by linarith)).2 fun i => (pi_norm_le_iff_of_nonneg (by linarith)).2 fun j => ?_
      have h1 := le_trans (entry_le_nrm _ i j) hx
      have h2 : ‖(1 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) i j‖ ≤ 1 := by
        rw [Matrix.one_apply]; split_ifs <;> simp
      calc ‖x i j‖ = ‖(Matrix.of x - 1) i j + (1 : Matrix _ _ ℂ) i j‖ := by
            rw [Matrix.sub_apply, sub_add_cancel]; rfl
        _ ≤ ‖(Matrix.of x - 1) i j‖ + ‖(1 : Matrix _ _ ℂ) i j‖ := norm_add_le _ _
        _ ≤ ρ + 1 := add_le_add h1 h2
  exact (isClosedEmbedding_val (hG := unitary_hermitian_group k r)).isCompact_preimage hK

theorem isCompact_sublevel (hz : inWb k r z) (hT : 0 < Tz k r z) (ρ : ℝ) :
    IsCompact ({x | fG k r z x ≤ ρ} ∩ Sg k r z) := by
  have hC := isCompact_Cg (k := k) (r := r) hz hT
  have hB := isCompact_ball1 (k := k) (r := r) ρ
  have hL : IsCompact ((fun p : GH k r × GH k r => p.1⁻¹ * p.2) '' (Cg k r z ×ˢ {x : GH k r | nrm (x.toM - 1) ≤ ρ})) :=
    (hC.prod hB).image (continuous_fst.inv.mul continuous_snd)
  refine hL.of_isClosed_subset ((isClosed_le (continuous_fG hz hT) continuous_const).inter (isClosed_Sg hz hT)) ?_
  rintro g ⟨hg, -⟩
  have hF : Continuous (fun c : GH k r => nrm ((c * g).toM - 1)) :=
    continuous_nrm.comp ((continuous_toM.comp (continuous_id.mul continuous_const)).sub continuous_const)
  obtain ⟨c, hc, hmin⟩ := hC.exists_isMinOn ⟨1, one_mem_Cg⟩ hF.continuousOn
  have hle : nrm ((c * g).toM - 1) ≤ fG k r z g :=
    le_csInf (Set.Nonempty.image _ ⟨1, one_mem_Cg⟩) (by rintro _ ⟨c', hc', rfl⟩; exact hmin hc')
  exact ⟨(c, c * g), ⟨hc, show nrm ((c * g).toM - 1) ≤ ρ from le_trans hle hg⟩, by simp⟩

def aT (k r : ℕ) : GH k r :=
  MG.mk (unitary_hermitian_group k r) (dS k r 2) (dS_mem_UH (by norm_num))

theorem toM_pow (x : GH k r) (m : ℕ) : (x ^ m).toM = x.toM ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, toM_one]
  | succ m ih => rw [pow_succ, pow_succ, toM_mul, ih]

theorem dS_pow (s : ℝ) (m : ℕ) : (dS k r s) ^ m = dS k r (s ^ m) := by
  unfold dS
  rw [Matrix.diagonal_pow]
  congr 1
  funext i
  simp only [Pi.pow_apply]
  push_cast
  rw [← zpow_natCast ((s : ℂ) ^ fexp k r i) m, ← zpow_natCast (s : ℂ) m, ← _root_.zpow_mul, ← _root_.zpow_mul,
    mul_comm]

theorem toM_cjB_aT (m : ℕ) (g : GH k r) :
    (cjB (aT k r ^ m) g).toM = dS k r ((1 / 2 : ℝ) ^ m) * g.toM * (dS k r ((1 / 2 : ℝ) ^ m))⁻¹ := by
  have h2 : (2 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have hh : (1 / 2 : ℝ) ^ m ≠ 0 := pow_ne_zero _ (by norm_num)
  have e1 : (1 / 2 : ℝ) ^ m = ((2 : ℝ) ^ m)⁻¹ := by rw [one_div, inv_pow]
  unfold cjB
  rw [toM_mul, toM_mul, toM_inv, toM_pow, aT, toM_mk, dS_pow, dS_inv_eq h2, dS_inv_eq hh, e1, inv_inv]

theorem aT_iff (z : Fin (2 * r + k + 1) → ℂ) (s : GH k r) : s ∈ Sg k r z ↔ cjB (aT k r) s ∈ Sg k r z := by
  have e := toM_cjB_aT (k := k) (r := r) 1 s
  rw [pow_one, pow_one] at e
  show s.toM ∈ Sset k r z ↔ (cjB (aT k r) s).toM ∈ Sset k r z
  rw [e, dS_conj_S_iff (by norm_num : (1 / 2 : ℝ) ≠ 0)]

theorem contractV (hz : inWb k r z) (hT : 0 < Tz k r z) (K : Set (GH k r)) (hK : IsCompact K) (hKS : K ⊆ Sg k r z)
    (V : Set (GH k r)) (hV : V ∈ 𝓝 (1 : GH k r)) :
    ∀ᶠ m : ℕ in atTop, ∀ x ∈ K, cjB (aT k r ^ m) x ∈ Cg k r z * V := by
  have hC := isCompact_Cg (k := k) (r := r) hz hT
  have hI := (isClosedEmbedding_val (hG := unitary_hermitian_group k r)).isInducing
  rw [hI.nhds_eq_comap, Filter.mem_comap] at hV
  obtain ⟨t, ht, htV⟩ := hV
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 ht
  set L := (fun p : GH k r × GH k r => p.1⁻¹ * p.2) '' (Cg k r z ×ˢ K) with hLdef
  have hL : IsCompact L := (hC.prod hK).image (continuous_fst.inv.mul continuous_snd)
  obtain ⟨B, hB⟩ := hL.exists_bound_of_continuousOn (continuous_val (hG := unitary_hermitian_group k r)).continuousOn
  have hlim : Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m * B) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_const B
    rwa [zero_mul] at this
  filter_upwards [hlim.eventually (eventually_lt_nhds hδ)] with m hm
  intro x hx
  obtain ⟨h, hh, n, hn, hxn⟩ := (hKS hx : x.toM ∈ Sset k r z)
  set c : GH k r := MG.mk (unitary_hermitian_group k r) h hh.1 with hcdef
  have hcC : c ∈ Cg k r z := by show c.toM ∈ UWset k r z; rw [hcdef, toM_mk]; exact hh
  set ν : GH k r := c⁻¹ * x with hνdef
  have hνL : ν ∈ L := ⟨(c, x), ⟨hcC, hx⟩, rfl⟩
  have hdet : IsUnit h.det := by
    have := det_ne_zero c; rw [hcdef, toM_mk] at this; exact isUnit_iff_ne_zero.2 this
  have hνN : ν.toM = n := by
    rw [hνdef, toM_mul, toM_inv, hcdef, toM_mk, hxn, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  have hxe : x = c * ν := by rw [hνdef, mul_inv_cancel_left]
  have hs0 : (0 : ℝ) < (1 / 2) ^ m := by positivity
  have hs1 : ((1 / 2 : ℝ)) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hcfix : cjB (aT k r ^ m) c = c := by
    apply MG.toM_injective
    rw [toM_cjB_aT, dS_inv_eq hs0.ne', hcdef, toM_mk]
    exact dS_conj_UW hs0.ne' hh
  rw [hxe, cjB_mul, hcfix]
  refine Set.mul_mem_mul hcC (htV (hball ?_))
  rw [Metric.mem_ball, dist_pi_lt_iff hδ]
  intro i
  rw [dist_pi_lt_iff hδ]
  intro j
  show dist ((cjB (aT k r ^ m) ν).toM i j) ((1 : GH k r).toM i j) < δ
  rw [toM_one, dist_eq_norm, ← Matrix.sub_apply, toM_cjB_aT, hνN]
  have hbd : ‖n i j‖ ≤ B := by
    rw [← hνN]
    exact le_trans (le_trans (norm_le_pi_norm (ν.val i) j) (norm_le_pi_norm ν.val i)) (hB ν hνL)
  calc ‖(dS k r ((1 / 2 : ℝ) ^ m) * n * (dS k r ((1 / 2 : ℝ) ^ m))⁻¹ - 1) i j‖
      ≤ (1 / 2 : ℝ) ^ m * ‖n i j‖ := norm_dS_conj_le hs0 hs1 hn i j
    _ ≤ (1 / 2 : ℝ) ^ m * B := mul_le_mul_of_nonneg_left hbd hs0.le
    _ < δ := hm

end Formalism.L2.S.Pv.FolnerS
end
end

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal Pointwise

namespace Formalism.L2.S.Pv.FolnerG

open PI PI.QuotSetU PI.QuotSetU.UnitaryGroupMassFormula PI.QuotSetU.UnitaryGroupMassFormula.SW PI.QuotSetU.UnitaryGroupMassFormula.ModW PI.QuotSetU.UnitaryGroupMassFormula.ModW.MG
  Formalism.L2.S.Pv.FolnerAbs Formalism.L2.SG.Pf.EnergyAbs Formalism.L2.S.Pv.FolnerS

variable {k r : ℕ} {ι : Type} [Fintype ι] (z : ι → Fin (2 * r + k + 1) → ℂ)

def SP : Set (ι → GH k r) := {s | ∀ v, s v ∈ Sg k r (z v)}

def CP : Set (ι → GH k r) := {s | ∀ v, s v ∈ Cg k r (z v)}

def fP (s : ι → GH k r) : ℝ := ∑ v, fG k r (z v) (s v)

variable {z}

theorem fG_nonneg (z0 : Fin (2 * r + k + 1) → ℂ) (g : GH k r) : 0 ≤ fG k r z0 g := by
  unfold fG
  refine Real.sInf_nonneg ?_
  rintro _ ⟨c, -, rfl⟩
  unfold nrm; positivity

theorem cjB_pi (b s : ι → GH k r) (v : ι) : cjB b s v = cjB (b v) (s v) := rfl

theorem isFolner_pi (hz : ∀ v, inWb k r (z v)) (hT : ∀ v, 0 < Tz k r (z v)) (μS : Measure (ι → GH k r))
    (hμ : IsHaarSub (SP z) μS) : IsFolner (SP z) μS := by
  have hCc : IsCompact (CP z) := by
    have : CP z = Set.pi Set.univ (fun v => Cg k r (z v)) := by ext s; simp [CP, Set.mem_pi]
    rw [this]; exact isCompact_univ_pi fun v => isCompact_Cg (hz v) (hT v)
  refine isFolner_of_contract hμ (CP z) (fP z) ?_ ?_ ?_ (fun _ => aT k r) ?_ ?_
  · exact continuous_finsetSum _ fun v _ => (continuous_fG (hz v) (hT v)).comp (continuous_apply v)
  · intro c hc x
    unfold fP
    exact Finset.sum_congr rfl fun v _ => fG_mul_left (hc v) (x v)
  · intro ρ
    have hsub : {x | fP z x ≤ ρ} ∩ SP z ⊆ Set.pi Set.univ (fun v => {y | fG k r (z v) y ≤ ρ} ∩ Sg k r (z v)) := by
      rintro s ⟨hs, hsS⟩ v -
      refine ⟨?_, hsS v⟩
      show fG k r (z v) (s v) ≤ ρ
      refine le_trans ?_ hs
      exact Finset.single_le_sum (f := fun w => fG k r (z w) (s w)) (fun w _ => fG_nonneg _ _) (Finset.mem_univ v)
    refine (isCompact_univ_pi fun v => isCompact_sublevel (hz v) (hT v) ρ).of_isClosed_subset ?_ hsub
    refine (isClosed_le (continuous_finsetSum _ fun v _ => (continuous_fG (hz v) (hT v)).comp (continuous_apply v))
      continuous_const).inter ?_
    have : SP z = ⋂ v, (fun s : ι → GH k r => s v) ⁻¹' Sg k r (z v) := by ext s; simp [SP]
    rw [this]
    exact isClosed_iInter fun v => (isClosed_Sg (hz v) (hT v)).preimage (continuous_apply v)
  · intro s
    show (∀ v, s v ∈ Sg k r (z v)) ↔ ∀ v, cjB (fun _ => aT k r) s v ∈ Sg k r (z v)
    exact forall_congr' fun v => by rw [cjB_pi]; exact aT_iff (z v) (s v)
  · intro K hK hKS U hU hCU
    obtain ⟨V, hV, hCV⟩ := compact_open_separated_mul_right hCc hU hCU
    rw [nhds_pi, Filter.mem_pi'] at hV
    obtain ⟨I, t, ht, hIt⟩ := hV
    have hev : ∀ v, ∀ᶠ m : ℕ in atTop, ∀ x ∈ (fun s : ι → GH k r => s v) '' K,
        cjB (aT k r ^ m) x ∈ Cg k r (z v) * t v := fun v =>
      contractV (hz v) (hT v) _ (hK.image (continuous_apply v)) (by rintro _ ⟨s, hs, rfl⟩; exact hKS hs v) (t v) (ht v)
    filter_upwards [Filter.eventually_all.2 hev] with m hm x hx
    have hx' : ∀ v, cjB (aT k r ^ m) (x v) ∈ Cg k r (z v) * t v := fun v => hm v (x v) ⟨x, hx, rfl⟩
    choose c hc w hw hcw using hx'
    refine hCV ⟨c, hc, w, hIt (fun v _ => hw v), ?_⟩
    funext v
    show c v * w v = cjB ((fun _ => aT k r) ^ m) x v
    rw [cjB_pi, Pi.pow_apply]
    exact hcw v

end Formalism.L2.S.Pv.FolnerG
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.IsFolnerOfEquiv
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Measure Filter Topology
open scoped ENNReal

namespace Formalism.L2.S.Pv.FolnerT

open Formalism.L2.SG.Pf.EnergyAbs

variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] [SecondCountableTopology H]
  [MeasurableSpace H] [BorelSpace H]

theorem isHaarSub_comap (Φ : G ≃* H) (hΦ : Continuous Φ) (hΦ' : Continuous Φ.symm) {S : Set H} {μ : Measure H}
    (hμ : IsHaarSub S μ) : IsHaarSub (Φ ⁻¹' S) (μ.map Φ.symm) := by
  obtain ⟨hC, h1, hm, hi, hσ, h0, hc, hl, hK, hr, hinv⟩ := hμ
  have hs : Measurable Φ.symm := hΦ'.measurable
  let E : G ≃ₜ H := { Φ.toEquiv with continuous_toFun := hΦ, continuous_invFun := hΦ' }
  let M : G ≃ᵐ H := E.toMeasurableEquiv
  have hmap : ∀ A : Set G, (μ.map Φ.symm) A = μ (Φ.symm ⁻¹' A) := fun A => by
    exact MeasurableEquiv.map_apply M.symm A
  refine ⟨hC.preimage hΦ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show Φ 1 ∈ S
    rw [map_one]
    exact h1
  · intro a ha b hb
    show Φ (a * b) ∈ S
    rw [map_mul]
    exact hm _ ha _ hb
  · intro a ha
    show Φ a⁻¹ ∈ S
    rw [map_inv]
    exact hi _ ha
  · haveI := hσ
    show SigmaFinite (μ.map M.symm)
    first
      | exact M.symm.sigmaFinite_map
      | exact MeasurableEquiv.sigmaFinite_map M.symm
      | (refine SigmaFinite.of_map _ M.measurable.aemeasurable ?_
         rw [Measure.map_map M.measurable M.symm.measurable, M.self_comp_symm, Measure.map_id]
         exact hσ)
  · intro h
    exact h0 ((Measure.map_eq_zero_iff hs.aemeasurable).1 h)
  · rw [hmap]
    convert hc using 2
    ext x
    simp
  · intro s hsS
    rw [Measure.map_map (continuous_const_mul s).measurable hs]
    have e1 : (fun x => s * x) ∘ ⇑Φ.symm = ⇑Φ.symm ∘ (fun y => Φ s * y) := by
      funext y
      simp
    rw [e1, ← Measure.map_map hs (continuous_const_mul (Φ s)).measurable, hl _ hsS]
  · intro K hKc
    rw [hmap]
    exact hK _ ((E.symm.isCompact_preimage).2 hKc)
  · intro s hsS
    rw [Measure.map_map (continuous_mul_const s).measurable hs]
    have e1 : (fun x => x * s) ∘ ⇑Φ.symm = ⇑Φ.symm ∘ (fun y => y * Φ s) := by
      funext y
      simp
    rw [e1, ← Measure.map_map hs (continuous_mul_const (Φ s)).measurable, hr _ hsS]
  · rw [Measure.map_map continuous_inv.measurable hs]
    have e1 : (fun x : G => x⁻¹) ∘ ⇑Φ.symm = ⇑Φ.symm ∘ (fun y => y⁻¹) := by
      funext y
      simp
    rw [e1, ← Measure.map_map hs continuous_inv.measurable, hinv]

theorem isFolner_of_equiv (Φ : G ≃* H) (hΦ : Continuous Φ) (hΦ' : Continuous Φ.symm) {S : Set H} {μ : Measure H}
    (hμ : IsHaarSub S μ) (hF : IsFolner (Φ ⁻¹' S) (μ.map Φ.symm)) : IsFolner S μ := by
  have hs : Measurable Φ.symm := hΦ'.measurable
  let E : G ≃ₜ H := { Φ.toEquiv with continuous_toFun := hΦ, continuous_invFun := hΦ' }
  let M : G ≃ᵐ H := E.toMeasurableEquiv
  have hmap : ∀ A : Set G, (μ.map Φ.symm) A = μ (Φ.symm ⁻¹' A) := fun A => by
    exact MeasurableEquiv.map_apply M.symm A
  intro K hK hKS ε hε
  obtain ⟨Ω, hΩm, hΩS, hpos, hfin, hle⟩ :=
    hF (Φ ⁻¹' K) ((E.isCompact_preimage).2 hK) (Set.preimage_mono hKS) ε hε
  refine ⟨Φ.symm ⁻¹' Ω, hs hΩm, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have := hΩS hx
    simpa using this
  · rw [← hmap]
    exact hpos
  · rw [← hmap]
    exact hfin
  · have hset : {t | t ∈ ⇑Φ.symm ⁻¹' Ω ∧ ∀ k ∈ K, k * t ∈ ⇑Φ.symm ⁻¹' Ω} =
        ⇑Φ.symm ⁻¹' {t | t ∈ Ω ∧ ∀ k ∈ ⇑Φ ⁻¹' K, k * t ∈ Ω} := by
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun k hk => ?_⟩
        have := h2 (Φ k) hk
        rwa [MulEquiv.symm_apply_apply] at this
      · rintro ⟨h1, h2⟩
        refine ⟨h1, fun k hk => ?_⟩
        exact h2 (Φ.symm k) (by simpa using hk)
    rw [hset, ← hmap, ← hmap]
    exact hle

end Formalism.L2.S.Pv.FolnerT
end
end

noncomputable section

open MeasureTheory Topology Matrix
open scoped ENNReal

namespace Formalism.L2.S.Pv.FolnerJ

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf.EnergyAbs Formalism.L2.S.Pv.FolnerS Formalism.L2.S.Pv.FolnerG
  Formalism.L2.S.Pv.FolnerT PI.QuotSetU.UnitaryGroupMassFormula.ModW PI.QuotSetU.UnitaryGroupMassFormula.ModW.MG

open Formalism.MainNotions.S (uMat)

variable {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

theorem uMat_ext {a b : Formalism.REAL.UJ ε} (h : uMat a = uMat b) : a = b :=
  Subtype.ext (Units.ext h)

theorem continuous_uMat : Continuous (uMat : Formalism.REAL.UJ ε → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  Units.continuous_val.comp continuous_subtype_val

def ofM (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    GH k r :=
  mk (PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group k r) g hg

theorem toM_ofM (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hg : g ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) :
    (ofM g hg).toM = g := toM_mk g hg

def psiF (hF : IsFrameJ ε e f wf z0) : GH k r ≃* Formalism.REAL.UJ ε where
  toFun g := toUJ (Qm e f wf z0 * g.toM * Qi ε e f wf z0) (conjQ_UJ hF g.toM_mem)
  invFun s := ofM (Qi ε e f wf z0 * uMat s * Qm e f wf z0) (conj_mem_UH hF (uMat_mem s))
  left_inv g := by
    apply toM_injective
    rw [toM_ofM, uMat_toUJ]
    exact Qi_Qm_conj hF _
  right_inv s := by
    apply uMat_ext
    rw [uMat_toUJ, toM_ofM]
    simp only [← Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.one_mul]
    rw [Matrix.mul_assoc, Qm_mul_Qi hF, Matrix.mul_one]
  map_mul' g h := by
    apply uMat_ext
    rw [uMat_mul, uMat_toUJ, uMat_toUJ, uMat_toUJ, toM_mul]
    calc Qm e f wf z0 * (g.toM * h.toM) * Qi ε e f wf z0
        = Qm e f wf z0 * g.toM * (Qi ε e f wf z0 * Qm e f wf z0) * h.toM * Qi ε e f wf z0 := by
          rw [Qi_mul_Qm hF, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem continuous_psiF (hF : IsFrameJ ε e f wf z0) : Continuous (psiF hF) := by
  rw [(Formalism.REAL.isClosedEmbeddingMatrix _ ε).1.isEmbedding.continuous_iff]
  show Continuous (fun g : GH k r => Qm e f wf z0 * g.toM * Qi ε e f wf z0)
  exact (continuous_const.matrix_mul continuous_toM).matrix_mul continuous_const

theorem continuous_psiF_symm (hF : IsFrameJ ε e f wf z0) : Continuous (psiF hF).symm := by
  rw [continuous_iff_toM]
  have e1 : (fun s : Formalism.REAL.UJ ε => ((psiF hF).symm s).toM) = fun s => Qi ε e f wf z0 * uMat s * Qm e f wf z0 := by
    funext s; exact toM_ofM _ (conj_mem_UH hF (uMat_mem s))
  rw [e1]
  exact (continuous_const.matrix_mul continuous_uMat).matrix_mul continuous_const

theorem inS_psiF_iff {T : ℝ} {z : Fin (2 * r + k + 1) → ℂ} (hF : IsFrameJ ε e f wf (z0v T z)) (hT : 0 < T) (g : GH k r) :
    InS e z (uMat (psiF hF g)) ↔ g.toM ∈ Formalism.QuantumDeterminants.Sset k r (zBv k r T) := by
  have hz := Qm_zB (e := e) (f := f) (wf := wf) hT z
  have key : psiF hF g ∈ HNset ε e f wf (z0v T z) (zBv k r T) ↔ g.toM ∈ Formalism.QuantumDeterminants.Sset k r (zBv k r T) := by
    show Qi ε e f wf (z0v T z) * uMat (psiF hF g) * Qm e f wf (z0v T z) ∈ Formalism.QuantumDeterminants.Sset k r (zBv k r T) ↔ _
    show Qi ε e f wf (z0v T z) * (Qm e f wf (z0v T z) * g.toM * Qi ε e f wf (z0v T z)) * Qm e f wf (z0v T z) ∈ _ ↔ _
    rw [Qi_Qm_conj hF]
  rw [← key]
  constructor
  · intro hs
    exact HNset_of_inS (fun k r T hT s hs h1 h2 => bessel_levi_formula k r T hT s hs h1 h2) hF hT hz hs
  · intro hs
    exact inS_of_HNset hF hz (inWb_zB T) ⟨_, rfl⟩ hs

theorem isFolner_Sinf {ι : Type} [Fintype ι] {εv : ι → Fin (2 * r + k + 1) → Bool}
    (ev fv : ι → Fin r → Fin (2 * r + k + 1) → ℂ) (wv : ι → Fin k → Fin (2 * r + k + 1) → ℂ)
    (zv : ι → Fin (2 * r + k + 1) → ℂ) (T : ι → ℝ) (hT : ∀ v, 0 < T v)
    (hF : ∀ v, IsFrameJ (εv v) (ev v) (fv v) (wv v) (z0v (T v) (zv v)))
    (μS : Measure (∀ v, Formalism.REAL.UJ (εv v)))
    (hμ : IsHaarSub {s : ∀ v, Formalism.REAL.UJ (εv v) | ∀ v, InS (ev v) (zv v) (uMat (s v))} μS) :
    IsFolner {s : ∀ v, Formalism.REAL.UJ (εv v) | ∀ v, InS (ev v) (zv v) (uMat (s v))} μS := by
  let Φ : (ι → GH k r) ≃* (∀ v, Formalism.REAL.UJ (εv v)) := MulEquiv.piCongrRight fun v => psiF (hF v)
  have hΦ : Continuous Φ := continuous_pi fun v => (continuous_psiF (hF v)).comp (continuous_apply v)
  have hΦ' : Continuous Φ.symm := continuous_pi fun v => (continuous_psiF_symm (hF v)).comp (continuous_apply v)
  have hset : Φ ⁻¹' {s : ∀ v, Formalism.REAL.UJ (εv v) | ∀ v, InS (ev v) (zv v) (uMat (s v))} =
      SP (fun v => zBv k r (T v)) := by
    ext x
    show (∀ v, InS (ev v) (zv v) (uMat (psiF (hF v) (x v)))) ↔ ∀ v, (x v).toM ∈ PI.QuotSetU.Sset k r (zBv k r (T v))
    exact forall_congr' fun v => inS_psiF_iff (hF v) (hT v) (x v)
  refine isFolner_of_equiv Φ hΦ hΦ' hμ ?_
  have hμ' := isHaarSub_comap Φ hΦ hΦ' hμ
  rw [hset] at hμ' ⊢
  exact isFolner_pi (z := fun v => zBv k r (T v)) (fun v => inWb_zB (T v))
    (fun v => by show 0 < Formalism.QuantumDeterminants.Tz k r (zBv k r (T v)); rw [Tz_zB (hT v).le]; exact hT v) _ hμ'

end Formalism.L2.S.Pv.FolnerJ
end
end

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix

namespace Formalism.L2.S.Pv.HaarSubS

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.EnergyAbs Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.Pf.WFL

theorem isFolner_Sinf_gen {n r k : ℕ} (hn : n = 2 * r + k + 1) {ι : Type} [Fintype ι] {εv : ι → Fin n → Bool}
    (ev fv : ι → Fin r → Fin n → ℂ) (wv : ι → Fin k → Fin n → ℂ) (zv : ι → Fin n → ℂ) (T : ι → ℝ)
    (hT : ∀ v, 0 < T v)
    (hee : ∀ v a b, hJ (εv v) (ev v a) (ev v b) = 0) (hff : ∀ v a b, hJ (εv v) (fv v a) (fv v b) = 0)
    (hef : ∀ v a b, hJ (εv v) (ev v a) (fv v b) = if a = b then 1 else 0)
    (hez : ∀ v a, hJ (εv v) (ev v a) (z0v (T v) (zv v)) = 0)
    (hfz : ∀ v a, hJ (εv v) (fv v a) (z0v (T v) (zv v)) = 0)
    (hzz : ∀ v, hJ (εv v) (z0v (T v) (zv v)) (z0v (T v) (zv v)) = -1)
    (hww : ∀ v a b, hJ (εv v) (wv v a) (wv v b) = if a = b then 1 else 0)
    (hew : ∀ v c a, hJ (εv v) (ev v c) (wv v a) = 0) (hfw : ∀ v c a, hJ (εv v) (fv v c) (wv v a) = 0)
    (hzw : ∀ v a, hJ (εv v) (z0v (T v) (zv v)) (wv v a) = 0)
    (μS : Measure (∀ v, Formalism.REAL.UJ (εv v)))
    (hμ : IsHaarSub {s : ∀ v, Formalism.REAL.UJ (εv v) | ∀ v, InS (ev v) (zv v) (uMat (s v))} μS) :
    IsFolner {s : ∀ v, Formalism.REAL.UJ (εv v) | ∀ v, InS (ev v) (zv v) (uMat (s v))} μS := by
  subst hn
  exact Formalism.L2.S.Pv.FolnerJ.isFolner_Sinf ev fv wv zv T hT
    (fun v => ⟨hee v, hff v, hef v, hez v, hfz v, hzz v, hww v, hew v, hfw v, hzw v⟩) μS hμ

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hermitian_scaled_right {n : ℕ} (ε : Fin n → Bool) (T : ℝ) (x z : Fin n → ℂ) :
    hJ ε x (z0v T z) = (((Real.sqrt T)⁻¹ : ℝ) : ℂ) * hJ ε x z := by
  unfold z0v hJ
  simp [Matrix.mulVec_smul, dotProduct_smul]

theorem hermitian_scaled_left {n : ℕ} (ε : Fin n → Bool) (T : ℝ) (x z : Fin n → ℂ) :
    hJ ε (z0v T z) x = (((Real.sqrt T)⁻¹ : ℝ) : ℂ) * hJ ε z x := by
  unfold z0v hJ
  simp [Matrix.mulVec_smul, smul_dotProduct, star_smul]

theorem folner_of_haar {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word)
    (hμ : IsHaarSub (X.SinfU u) (Formalism.L2.SG.RealObj.muS X u)) :
    IsFolner (X.SinfU u) (Formalism.L2.SG.RealObj.muS X u) := by
  have hn : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := X.n_eq.trans (dimS_eq D.R).symm
  have hT : 0 < Tw (D := D) u := ProductExactness.Tw_pos u
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  refine isFolner_Sinf_gen hn (fun v a => rv X.B.I v (X.eR a)) (fun v a => rv X.B.I v (X.fR a))
    (fun v => X.wfr u v) (fun v => rv X.B.I v (X.zR u)) (fun _ => Tw u) (fun _ => hT) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    (Formalism.L2.SG.RealObj.muS X u) hμ
  · intro v a b
    exact (ProductExactness.hJ_X X v _ _).trans (by rw [X.ee]; simp)
  · intro v a b
    exact (ProductExactness.hJ_X X v _ _).trans (by rw [X.ff]; simp)
  · intro v a b
    exact (ProductExactness.hJ_X X v _ _).trans (by rw [X.ef]; split_ifs <;> simp)
  · intro v a
    rw [hermitian_scaled_right]
    have : hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) = 0 :=
      (ProductExactness.hJ_X X v _ _).trans (by rw [(X.zu_orth u a).1]; simp)
    rw [this, mul_zero]
  · intro v a
    rw [hermitian_scaled_right]
    have : hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) = 0 :=
      (ProductExactness.hJ_X X v _ _).trans (by rw [(X.zu_orth u a).2]; simp)
    rw [this, mul_zero]
  · intro v
    rw [hermitian_scaled_right, hermitian_scaled_left]
    have h5 : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) = -(Tw (D := D) u : ℂ) :=
      (ProductExactness.hJ_X X v _ _).trans (by rw [X.zu_norm u]; simp [Tw])
    rw [h5]
    have hs : ((Real.sqrt (Tw (D := D) u))⁻¹ : ℝ) * (Real.sqrt (Tw (D := D) u))⁻¹ * Tw (D := D) u = 1 := by
      rw [← mul_inv, Real.mul_self_sqrt hT.le, inv_mul_cancel₀ hT.ne']
    have : (((Real.sqrt (Tw (D := D) u))⁻¹ : ℝ) : ℂ) * ((((Real.sqrt (Tw (D := D) u))⁻¹ : ℝ) : ℂ) *
        -((Tw (D := D) u : ℝ) : ℂ)) = -(((Real.sqrt (Tw (D := D) u))⁻¹ * (Real.sqrt (Tw (D := D) u))⁻¹ *
          Tw (D := D) u : ℝ) : ℂ) := by push_cast; ring
    rw [this, hs]
    simp
  · intro v a b
    exact X.wfr_on u v a b
  · intro v c a
    exact ((X.wfr_perp u v a).1 c).1
  · intro v c a
    exact ((X.wfr_perp u v a).1 c).2
  · intro v a
    rw [hermitian_scaled_left]
    have h0 : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (X.wfr u v a) = 0 := (X.wfr_perp u v a).2
    rw [h0, mul_zero]

theorem stepSubG_of_MN (hN : MeasN) (hQ : NuQSFinite) : Formalism.L2.SG.RealObj.EnergyInst.StepSubG := by
  exact stepSubG_of sDecomp_holds hN (measH_of sDecomp_holds)
    (fun D X u => folner_of_haar X u (isHaarSub_SinfU sDecomp_holds hN (measH_of sDecomp_holds) X u)) hQ

end Formalism.L2.S.Pv.HaarSubS
end
end

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open scoped InnerProductSpace TensorProduct Classical ENNReal
open Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.L2.S.Pv.HaarSubS

theorem hform_crdX {D : D7} (X : HidaSetting D) (v w : (VS D).V) :
    X.ιE (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (crdOf X.B.I X.ιE X.bas v) (crdOf X.B.I X.ιE X.bas w)) =
      (VS D).hT v w := by
  conv_rhs => rw [← X.bas.sum_repr v, ← X.bas.sum_repr w]
  unfold Formalism.UG.hform crdOf
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, X.ιE_conj, X.J_eq, RingEquiv.apply_symm_apply, LinearMap.map_smulₛₗ,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, RingHom.id_apply, Finset.mul_sum]
  have hst : ∀ x : D.host.E, star x = D.host.conj x := fun x => Formalism.MainNotions.S.Inh.tie_star D x
  simp only [hst]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_eqX {D : D7} (X : HidaSetting D) (v w : (VS D).V) :
    Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (crdOf X.B.I X.ιE X.bas v) (crdOf X.B.I X.ιE X.bas w) =
      X.ιE.symm ((VS D).hT v w) := by
  rw [← hform_crdX X v w, RingEquiv.symm_apply_apply]

theorem frameRelX {D : D7} (X : HidaSetting D) (u : D.what₂.Word) :
    PI.NMeasInv.FrameRel X.B.I X.eR X.fR (X.zR u) := by
  have h : ∀ v w, Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J (X.crd v) (X.crd w) =
      X.ιE.symm ((VS D).hT v w) := fun v w => hform_eqX X v w
  unfold Formalism.L2.SG.HidaSetting.HidaSetting.eR Formalism.L2.SG.HidaSetting.HidaSetting.fR Formalism.L2.SG.HidaSetting.HidaSetting.zR
  refine ⟨fun a b => ?_, fun a b => ?_, fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [h, X.ee, map_zero]
  · rw [h, X.ff, map_zero]
  · rw [h, X.ef]
    split_ifs <;> simp
  · rw [h, (X.zu_orth u a).1, map_zero]
  · rw [h, (X.zu_orth u a).2, map_zero]
  · rw [h, X.zu_norm, map_neg, map_natCast, neg_ne_zero, Nat.cast_ne_zero]
    exact (D.mem u).A.T_prime.ne_zero

theorem measN_holds : MeasN := by
  obtain ⟨h1, h2, h3, h4⟩ := PI.n_measure_invariant
  intro D X u
  have hF := frameRelX X u
  have hμ : PI.NMeasInv.IsHaarOnSet X.B.I (PI.NMeasInv.Ninf X.B.I X.eR (X.zR u)) (X.muN u) := X.muN_haar u
  exact ⟨h1 _ _ _ _ _ hF _ hμ, h2 _ _ _ _ _ hF _ hμ, h3 _ _ _ _ _ hF _ hμ, h4 _ _ _ _ _ hF _ hμ⟩

theorem nuQSFinite_holds : NuQSFinite := by
  intro D X u
  haveI : SigmaFinite (X.nuQ u) :=
    quotient_sigma_finite X.B.I.Ginf (Formalism.L2.SG.ProjRows.muInf X.B.I) _ _ (X.muN u) (X.muH u) (X.nuQ u)
      (X.muN_haar u) (X.muH_haar u) (X.nuQ_weil u)
  infer_instance

theorem stepSubG_holds : Formalism.L2.SG.RealObj.EnergyInst.StepSubG := stepSubG_of_MN measN_holds nuQSFinite_holds

end Formalism.L2.S.Pv.HaarSubS
