module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.LabApply

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.OpnContinuous
noncomputable section

open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.SplitPrimeNormLemmas Matrix
open scoped ENNReal

namespace WlocSk

abbrev CSp (m d : ℕ) := (Fin m → ℂ) × (Fin d → ℝ)

instance instAddHaarCSp (m d : ℕ) : (volume : Measure (CSp m d)).IsAddHaarMeasure :=
  Measure.prod.instIsAddHaarMeasure _ _

def NCoordHaar : Prop :=
  ∀ (k r : ℕ) (μN : Measure (Formalism.QuantumDeterminants.Mt k r)), IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
    (∀ K : Set (Formalism.QuantumDeterminants.Mt k r), IsCompact K → μN K < ⊤) →
    ∃ (m d q : ℕ) (Φ : CSp m d → Formalism.QuantumDeterminants.Mt k r) (c : ℝ≥0∞) (κ : ℝ),
      1 ≤ q ∧ ((q * (2 * m + d) : ℕ) : ℝ) < N1H k r ∧ 0 < κ ∧ c ≠ ⊤ ∧ Measurable Φ ∧
      μN = c • (volume : Measure (CSp m d)).map Φ ∧
      ∀ t, 1 + ‖t‖ ≤ κ * Formalism.L2.SG.WuDecay.opn (Matrix.of (Φ t)) ^ q

def NChart : Prop :=
  ∀ (k r : ℕ), ∃ (m d q : ℕ) (Φ : CSp m d → Formalism.QuantumDeterminants.Mt k r) (κ : ℝ),
    1 ≤ q ∧ ((q * (2 * m + d) : ℕ) : ℝ) < N1H k r ∧ 0 < κ ∧ MeasurableEmbedding Φ ∧
    Set.range Φ = {x | Matrix.of x ∈ Formalism.QuantumDeterminants.Nset k r} ∧
    (∀ m₀ ∈ Formalism.QuantumDeterminants.Nset k r, ∃ T : CSp m d → CSp m d, MeasurePreserving T volume volume ∧
      ∀ t, Formalism.QuantumDeterminants.lmulM m₀ (Φ t) = Φ (T t)) ∧
    ∀ t, 1 + ‖t‖ ≤ κ * Formalism.L2.SG.WuDecay.opn (Matrix.of (Φ t)) ^ q

def NUniq : Prop :=
  ∀ (k r : ℕ) (μ μ' : Measure (Formalism.QuantumDeterminants.Mt k r)), IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ →
    IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μ' → ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ μ = c • μ'

theorem nCoordHaar_of (hC : NChart) (hU : NUniq) : NCoordHaar := by
  intro k r μN hN _
  obtain ⟨m, d, q, Φ, κ, hq, hD, hκ, hΦ, hrange, hT, hgrow⟩ := hC k r
  have hmeasL : ∀ a : Mat k r, Measurable (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) a) := fun a => by
    have : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) a) := by
      unfold Formalism.QuantumDeterminants.lmulM
      exact continuous_const.matrix_mul continuous_id
    exact this.measurable
  have hH : IsHaarOn (Formalism.QuantumDeterminants.Nset k r) ((volume : Measure (CSp m d)).map Φ) := by
    refine ⟨hΦ.sigmaFinite_map, ?_, ?_, ?_⟩
    · intro h0
      rw [Measure.map_eq_zero_iff hΦ.measurable.aemeasurable] at h0
      exact isOpen_univ.measure_ne_zero (volume : Measure (CSp m d)) Set.univ_nonempty
        (by rw [h0, Measure.coe_zero, Pi.zero_apply])
    · rw [Measure.map_apply hΦ.measurable]
      · have : Φ ⁻¹' {x | Matrix.of x ∉ Formalism.QuantumDeterminants.Nset k r} = ∅ := by
          ext t
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
          have : Φ t ∈ Set.range Φ := ⟨t, rfl⟩
          rw [hrange] at this
          exact this
        rw [this, measure_empty]
      · have hcl : MeasurableSet (Set.range Φ) := hΦ.measurableSet_range
        rw [hrange] at hcl
        exact hcl.compl
    · intro s hs
      obtain ⟨T, hTm, hTe⟩ := hT s hs
      rw [Measure.map_map (hmeasL s) hΦ.measurable]
      have : Formalism.QuantumDeterminants.lmulM s ∘ Φ = Φ ∘ T := funext hTe
      rw [this, ← Measure.map_map hΦ.measurable hTm.measurable, hTm.map_eq]
  obtain ⟨c, hc, hμ⟩ := hU k r μN _ hN hH
  exact ⟨m, d, q, Φ, c, κ, hq, hD, hκ, hc, hΦ.measurable, hμ, hgrow⟩

local instance instAlgCLM (n : ℕ) :
    Algebra ℂ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) := ContinuousLinearMap.algebra
local instance instModCLM (n : ℕ) :
    Module ℂ (EuclideanSpace ℂ (Fin n) →L[ℂ] EuclideanSpace ℂ (Fin n)) := ContinuousLinearMap.module

lemma opn_continuous (k r : ℕ) :
    Continuous fun m : Formalism.QuantumDeterminants.Mt k r => Formalism.L2.SG.WuDecay.opn (Matrix.of m) := by
  unfold Formalism.L2.SG.WuDecay.opn
  have : Continuous fun m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ =>
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin (2 * r + k + 1)) m := by
    let L : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →ₗ[ℂ]
        (EuclideanSpace ℂ (Fin (2 * r + k + 1)) →L[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1))) :=
      { toFun := fun m => Matrix.toEuclideanCLM (𝕜 := ℂ) m
        map_add' := fun a b => map_add _ a b
        map_smul' := fun a b => map_smul _ a b }
    exact L.continuous_of_finiteDimensional
  exact continuous_norm.comp (this.comp continuous_id)

lemma finrank_CSp (m d : ℕ) : Module.finrank ℝ (CSp m d) = 2 * m + d := by
  rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_fin_fun]
  simp [Complex.finrank_real_complex, mul_comm]

theorem nIntDecay_of (h : NCoordHaar) : NIntDecay := by
  intro k r μN hN hNc
  obtain ⟨m, d, q, Φ, c, κ, hq, hD, hκ, hc, hΦ, hμ, hgrow⟩ := h k r μN hN hNc
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hD' : (Module.finrank ℝ (CSp m d) : ℝ) < N1H k r / q := by
    rw [finrank_CSp, lt_div_iff₀ hq0, mul_comm]; exact_mod_cast hD
  have hF : Measurable fun x : Formalism.QuantumDeterminants.Mt k r =>
      ENNReal.ofReal (Formalism.L2.SG.WuDecay.opn (Matrix.of x) ^ (-N1H k r)) :=
    ENNReal.measurable_ofReal.comp ((opn_continuous k r).measurable.pow_const _)
  rw [hμ, lintegral_smul_measure, lintegral_map hF hΦ]
  refine ENNReal.mul_lt_top hc.lt_top ?_
  set s := N1H k r / q with hs
  have hbound : ∀ t : CSp m d,
      ENNReal.ofReal (Formalism.L2.SG.WuDecay.opn (Matrix.of (Φ t)) ^ (-N1H k r)) ≤
        ENNReal.ofReal (κ ^ s) * ENNReal.ofReal ((1 + ‖t‖) ^ (-s)) := by
    intro t
    set o := Formalism.L2.SG.WuDecay.opn (Matrix.of (Φ t)) with ho
    have ho0 : 0 ≤ o := norm_nonneg _
    have h1 : 0 < 1 + ‖t‖ := by positivity
    have h2 : (1 + ‖t‖) / κ ≤ o ^ q := by
      rw [div_le_iff₀ hκ, mul_comm]; exact hgrow t
    have h3 : 0 < (1 + ‖t‖) / κ := div_pos h1 hκ
    have hoq : o ^ (-N1H k r) = (o ^ q) ^ (-s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ho0, hs]
      congr 1
      field_simp
    rw [← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    rw [hoq]
    calc (o ^ q) ^ (-s)
        ≤ ((1 + ‖t‖) / κ) ^ (-s) :=
          Real.rpow_le_rpow_of_nonpos h3 h2 (by
            have : 0 < s := lt_of_le_of_lt (Nat.cast_nonneg _) hD'
            linarith)
      _ = κ ^ s * (1 + ‖t‖) ^ (-s) := by
          rw [Real.div_rpow h1.le hκ.le, div_eq_mul_inv, ← Real.rpow_neg hκ.le, neg_neg, mul_comm]
  calc ∫⁻ t, ENNReal.ofReal (Formalism.L2.SG.WuDecay.opn (Matrix.of (Φ t)) ^ (-N1H k r))
      ≤ ∫⁻ t : CSp m d, ENNReal.ofReal (κ ^ s) *
          ENNReal.ofReal ((1 + ‖t‖) ^ (-s)) := lintegral_mono hbound
    _ = ENNReal.ofReal (κ ^ s) *
          ∫⁻ t : CSp m d, ENNReal.ofReal ((1 + ‖t‖) ^ (-s)) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (finite_integral_one_add_norm hD')

end WlocSk
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.Unfold
noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S Formalism.MainNotions.CayleySignature Formalism.L2.SG.SplitPrimeNormLemmas
open scoped ENNReal

namespace WlocSk

namespace Grp

def sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if i.val < r ∨ r + k < i.val then ⟨2 * r + k - i.val, by omega⟩ else i

lemma sig_val (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (sig k r i).val = if i.val < r ∨ r + k < i.val then 2 * r + k - i.val else i.val := by
  unfold sig; split_ifs <;> rfl

lemma sig_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : sig k r (sig k r i) = i := by
  apply Fin.ext
  have hi := i.isLt
  have h1 := sig_val k r i
  have h2 := sig_val k r (sig k r i)
  split_ifs at h1 h2 <;> omega

def sgn (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

lemma sgn_sig (k r : ℕ) (i : Fin (2 * r + k + 1)) : sgn k r (sig k r i) = sgn k r i := by
  have hi := i.isLt
  have h1 := sig_val k r i
  unfold sgn
  split_ifs at h1 ⊢ <;> first | rfl | (exfalso; omega)

lemma Hpk_eq (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Formalism.QuantumDeterminants.Hpk k r i j = if j = sig k r i then sgn k r i else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  have hs := sig_val k r i
  have e1 : (j = sig k r i) ↔ j.val = (sig k r i).val := Fin.ext_iff
  have e2 : (i = j) ↔ i.val = j.val := Fin.ext_iff
  unfold Formalism.QuantumDeterminants.Hpk sgn
  simp only [e1, e2]
  split_ifs at * <;> first | rfl | (exfalso; omega)

lemma Hpk_sq (k r : ℕ) : Formalism.QuantumDeterminants.Hpk k r * Formalism.QuantumDeterminants.Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Hpk_eq k r i, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Hpk_eq, sig_sig, sgn_sig, Matrix.one_apply]
  by_cases h : j = i
  · rw [if_pos h, if_pos h.symm]; unfold sgn; split_ifs <;> norm_num
  · rw [if_neg h, if_neg (Ne.symm h), mul_zero]

variable {k r : ℕ}

lemma one_mem : (1 : Mat k r) ∈ Gr k r := by
  show (1 : Mat k r)ᴴ * Formalism.QuantumDeterminants.Hpk k r * 1 = Formalism.QuantumDeterminants.Hpk k r
  simp

lemma mul_mem {a b : Mat k r} (ha : a ∈ Gr k r) (hb : b ∈ Gr k r) : a * b ∈ Gr k r := by
  have ha' : aᴴ * Formalism.QuantumDeterminants.Hpk k r * a = Formalism.QuantumDeterminants.Hpk k r := ha
  have hb' : bᴴ * Formalism.QuantumDeterminants.Hpk k r * b = Formalism.QuantumDeterminants.Hpk k r := hb
  show (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = Formalism.QuantumDeterminants.Hpk k r
  calc (a * b)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (a * b) = bᴴ * (aᴴ * Formalism.QuantumDeterminants.Hpk k r * a) * b := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [ha', hb']

lemma of_mul_mem {s x : Mat k r} (hs : s ∈ Gr k r) (hsx : s * x ∈ Gr k r) : x ∈ Gr k r := by
  have hs' : sᴴ * Formalism.QuantumDeterminants.Hpk k r * s = Formalism.QuantumDeterminants.Hpk k r := hs
  have hsx' : (s * x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (s * x) = Formalism.QuantumDeterminants.Hpk k r := hsx
  show xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = Formalism.QuantumDeterminants.Hpk k r
  calc xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = xᴴ * (sᴴ * Formalism.QuantumDeterminants.Hpk k r * s) * x := by rw [hs']
    _ = (s * x)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (s * x) := by
        rw [conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := hsx'

lemma inv_left {g : Mat k r} (hg : g ∈ Gr k r) :
    (Formalism.QuantumDeterminants.Hpk k r * gᴴ * Formalism.QuantumDeterminants.Hpk k r) * g = 1 := by
  have hg' : gᴴ * Formalism.QuantumDeterminants.Hpk k r * g = Formalism.QuantumDeterminants.Hpk k r := hg
  calc Formalism.QuantumDeterminants.Hpk k r * gᴴ * Formalism.QuantumDeterminants.Hpk k r * g
      = Formalism.QuantumDeterminants.Hpk k r * (gᴴ * Formalism.QuantumDeterminants.Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', Hpk_sq]

lemma inv_eq {g : Mat k r} (hg : g ∈ Gr k r) : g⁻¹ = Formalism.QuantumDeterminants.Hpk k r * gᴴ * Formalism.QuantumDeterminants.Hpk k r :=
  Matrix.inv_eq_left_inv (inv_left hg)

lemma inv_mul {g : Mat k r} (hg : g ∈ Gr k r) : g⁻¹ * g = 1 := by
  rw [inv_eq hg]; exact inv_left hg

lemma mul_inv {g : Mat k r} (hg : g ∈ Gr k r) : g * g⁻¹ = 1 := by
  rw [inv_eq hg]; exact mul_eq_one_comm.mp (inv_left hg)

lemma inv_mem {g : Mat k r} (hg : g ∈ Gr k r) : g⁻¹ ∈ Gr k r := by
  apply of_mul_mem hg
  rw [mul_inv hg]; exact one_mem

lemma isClosed_Gr : IsClosed (Gr k r) := by
  have hc : Continuous (fun x : Mat k r => xᴴ * Formalism.QuantumDeterminants.Hpk k r * x) := by fun_prop
  exact isClosed_eq hc continuous_const

lemma continuous_of : Continuous (fun x : Formalism.QuantumDeterminants.Mt k r => (Matrix.of x : Mat k r)) := continuous_id

lemma measurableSet_Gr : MeasurableSet {x : Formalism.QuantumDeterminants.Mt k r | Matrix.of x ∈ Gr k r} :=
  (isClosed_Gr.preimage continuous_of).measurableSet

end Grp

section Unfold

variable {k r : ℕ}

lemma continuous_mulP : Continuous (mulP (k := k) (r := r)) := by
  have h1 : Continuous fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.1 : Mat k r) :=
    continuous_fst
  have h2 : Continuous fun p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => (Matrix.of p.2 : Mat k r) :=
    continuous_snd
  exact h1.matrix_mul h2

lemma measurable_mulP : Measurable (mulP (k := k) (r := r)) := continuous_mulP.measurable

lemma continuous_rmul (x : Formalism.QuantumDeterminants.Mt k r) :
    Continuous (fun s : Formalism.QuantumDeterminants.Mt k r => (fun i j => (Matrix.of s * Matrix.of x) i j : Formalism.QuantumDeterminants.Mt k r)) := by
  have h1 : Continuous fun s : Formalism.QuantumDeterminants.Mt k r => (Matrix.of s : Mat k r) := continuous_id
  exact h1.matrix_mul continuous_const

theorem unfold_weil {μG μS ν μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)} {cS : ℝ≥0∞} (hcS : cS ≠ ⊤)
    (hP : (μW.prod μN).map mulP = cS • μS) (hQ : IsQuotMeas μG μS ν)
    (f : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, ∫⁻ p, f (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) ∂(μW.prod μN) ∂ν =
      cS * ∫⁻ y, f y ∂μG := by
  have hin : ∀ x : Formalism.QuantumDeterminants.Mt k r,
      ∫⁻ p, f (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) ∂(μW.prod μN) =
        cS * ∫⁻ s, f (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS := by
    intro x
    have hm : Measurable (fun s : Formalism.QuantumDeterminants.Mt k r => f (fun i j => (Matrix.of s * Matrix.of x) i j)) :=
      hf.comp (continuous_rmul x).measurable
    have h := lintegral_map (μ := μW.prod μN) hm measurable_mulP
    rw [hP, lintegral_smul_measure, smul_eq_mul] at h
    exact h.symm
  rw [lintegral_congr hin, lintegral_const_mul' _ _ hcS, hQ f hf]

theorem nu_conc {μG μS ν : Measure (Formalism.QuantumDeterminants.Mt k r)} {T : Set (Mat k r)} (hQ : IsQuotMeas μG μS ν)
    (hG : μG {x | Matrix.of x ∉ Gr k r} = 0) (hS0 : μS ≠ 0) (hSc : μS {x | Matrix.of x ∉ T} = 0)
    (hTG : T ⊆ Gr k r) : ν {x | Matrix.of x ∉ Gr k r} = 0 := by
  set E : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∉ Gr k r} with hEdef
  have hE : MeasurableSet E := Grp.measurableSet_Gr.compl
  have hw := hQ (E.indicator 1) (measurable_one.indicator hE)
  rw [lintegral_indicator_one hE, hG] at hw
  have hlow : ∀ x, E.indicator (fun _ => μS Set.univ) x ≤
      ∫⁻ s, E.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS := by
    intro x
    by_cases hx : x ∈ E
    · rw [Set.indicator_of_mem hx]
      have hae : ∀ᵐ s ∂μS, Matrix.of s ∈ T := ae_iff.mpr hSc
      have h1 : ∀ᵐ s ∂μS, E.indicator 1 (fun i j => (Matrix.of s * Matrix.of x) i j) = (1 : ℝ≥0∞) := by
        filter_upwards [hae] with s hs
        apply Set.indicator_of_mem
        intro hsx
        exact hx (Grp.of_mul_mem (hTG hs) hsx)
      rw [lintegral_congr_ae h1, lintegral_one]
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  have h2 := lintegral_mono (μ := ν) hlow
  rw [lintegral_indicator_const hE, ← hw] at h2
  have hpos : μS Set.univ ≠ 0 := by
    intro h0; exact hS0 (Measure.measure_univ_eq_zero.mp h0)
  exact (mul_eq_zero.mp (le_zero_iff.mp h2)).resolve_left hpos

end Unfold

section FromSteps

variable {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} {c : Fin r → ℂ} {u : Fin k → ℝ} {v : Fin (k - 1) → ℝ}
  {b : Fin (2 * r + 2) → ℝ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {σ : Mat k r → (H →L[ℂ] H)} {Vp : Type} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp]
  [FiniteDimensional ℂ Vp] {π : Mat k r → (Vp →L[ℂ] Vp)} {w : H}
  {μG μS ν μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}

lemma S_sub_G (hSG : SGrp) (hyp : Hyp k r z c u v b σ π w μG μS ν μW μN) :
    Formalism.QuantumDeterminants.Sset k r z ⊆ Gr k r := by
  obtain ⟨hset, -⟩ := hyp
  obtain ⟨-, -, hz, hT, -⟩ := hset
  obtain ⟨hW, hN, -⟩ := hSG k r z c hz hT
  rintro s ⟨h, hh, m, hm, rfl⟩
  exact Grp.mul_mem (hW hh) (hN hm)

theorem unfold_of (hSP : SProd) (hyp : Hyp k r z c u v b σ π w μG μS ν μW μN) :
    ∃ cS : ℝ≥0∞, cS ≠ 0 ∧ cS ≠ ⊤ ∧ ∀ f : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞, Measurable f →
      ∫⁻ x, ∫⁻ p, f (fun i j => (Matrix.of (mulP p) * Matrix.of x) i j) ∂(μW.prod μN) ∂ν =
        cS * ∫⁻ y, f y ∂μG := by
  obtain ⟨cS, h0, htop, hP⟩ := hSP k r z c u v b H σ Vp π w μG μS ν μW μN hyp
  exact ⟨cS, h0, htop, fun f hf => unfold_weil htop hP hyp.2.2.2.2.2.2.1 f hf⟩

theorem nu_conc_of (hSG : SGrp) (hyp : Hyp k r z c u v b σ π w μG μS ν μW μN) :
    ν {x | Matrix.of x ∉ Gr k r} = 0 := by
  have hS := S_sub_G hSG hyp
  obtain ⟨-, -, -, -, hG, hSm, hQ, -⟩ := hyp
  exact nu_conc hQ hG.2.2.1 hSm.2.1 hSm.2.2.1 hS

end FromSteps

end WlocSk
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.SubgroupHypothesisHolds
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.MulVecApplyOfRow
open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S

noncomputable section

namespace WlocSk.UnitaryGroupBasics

variable {k r : ℕ}

theorem col_of_fix {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {c : Fin (2 * r + k + 1)} (hc : h *ᵥ bvec c = bvec c) (p : Fin (2 * r + k + 1)) :
    h p c = if p = c then 1 else 0 := by
  have := congrFun hc p
  simp only [bvec, Matrix.mulVec, dotProduct_single, mul_one, Pi.single_apply] at this
  exact this

theorem row_of_fixed_col {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hU : h ∈ UH (Hpk k r)) (c : Fin (2 * r + k + 1))
    (hc : ∀ p, h p c = if p = c then 1 else 0) (j : Fin (2 * r + k + 1)) :
    h (tau k r c) j = if tau k r c = j then 1 else 0 := by
  have hU' : hᴴ * Hpk k r * h = Hpk k r := hU
  have e := congrFun (congrFun hU' c) j
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single c] at e
  · rw [conjTranspose_apply, hc c, if_pos rfl, star_one, one_mul, hpk_mul_apply, hpk_row] at e
    have hs : sgn k r c ≠ 0 := by
      intro h0
      have := sgn_mul_self (k := k) (r := r) c
      rw [h0, zero_mul] at this
      exact zero_ne_one this
    by_cases hj : j = tau k r c
    · rw [if_pos hj] at e
      rw [if_pos hj.symm]
      exact mul_left_cancel₀ hs (e.trans (mul_one _).symm)
    · rw [if_neg hj] at e
      rw [if_neg (Ne.symm hj)]
      exact (mul_eq_zero.1 e).resolve_left hs
  · intro p _ hp
    rw [conjTranspose_apply, hc p, if_neg hp, star_zero, zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem uw_fixed_col {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (c : Fin (2 * r + k + 1)) (hc : c.val < r ∨ r + k < c.val) (p : Fin (2 * r + k + 1)) :
    h p c = if p = c then 1 else 0 := _root_.ReciprocityTheory.ChartRestriction.DS.Mult1.SymA.uw_fixed_col (z := z) (h := h) hh c hc p

theorem tau_out (i : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) :
    (tau k r i).val < r ∨ r + k < (tau k r i).val := by
  unfold tau
  simp only
  split_ifs
  omega

theorem uw_block {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    block k r h := by
  refine ⟨fun i j hj => uw_fixed_col hh j hj i, fun i j hi => ?_⟩
  have := row_of_fixed_col hh.1 (tau k r i) (uw_fixed_col hh _ (tau_out i hi)) j
  rw [tau_tau] at this
  exact this

theorem uw_inv {z : Fin (2 * r + k + 1) → ℂ}
    {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z) :
    h⁻¹ ∈ UWset k r z := by
  have hu := isUnit_of_uh hh.1
  have fix : ∀ v : Fin (2 * r + k + 1) → ℂ, h *ᵥ v = v → h⁻¹ *ᵥ v = v := by
    intro v hv
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  exact ⟨uh_inv hh.1, fun a => ⟨fix _ (hh.2.1 a).1, fix _ (hh.2.1 a).2⟩, fix _ hh.2.2⟩

theorem uw_mul {z : Fin (2 * r + k + 1) → ℂ}
    {h h' : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hh : h ∈ UWset k r z)
    (hh' : h' ∈ UWset k r z) : h * h' ∈ UWset k r z := by
  refine ⟨uh_mul hh.1 hh'.1, fun a => ⟨?_, ?_⟩, ?_⟩
  · rw [← Matrix.mulVec_mulVec, (hh'.2.1 a).1, (hh.2.1 a).1]
  · rw [← Matrix.mulVec_mulVec, (hh'.2.1 a).2, (hh.2.1 a).2]
  · rw [← Matrix.mulVec_mulVec, hh'.2.2, hh.2.2]

theorem block_mul_col {h g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : block k r h) (hg : col k r g) (i q : Fin (2 * r + k + 1)) (hq : q.val ≤ r + k)
    (hi : q.val ≤ i.val ∨ r ≤ i.val) : (h * g) i q = h i q := by
  rw [Matrix.mul_apply, Finset.sum_eq_single q]
  · rw [hg q q hq (by omega), if_pos rfl, mul_one]
  · intro p _ hpq
    by_cases hp : q.val ≤ p.val ∨ r ≤ p.val
    · rw [hg p q hq hp, if_neg hpq, mul_zero]
    · push Not at hp
      have hne : i ≠ p := by
        intro e
        subst e
        omega
      rw [hh.1 i p (by omega), if_neg hne, zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem conj_col {h h' g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : block k r h) (hh' : block k r h') (hinv : h * h' = 1) (hg : col k r g) :
    col k r (h * g * h') := by
  intro i j hj hi
  have term : ∀ q : Fin (2 * r + k + 1), (h * g) i q * h' q j = h i q * h' q j := by
    intro q
    by_cases h0 : h' q j = 0
    · rw [h0, mul_zero, mul_zero]
    · by_cases hjr : j.val < r
      · have hqj : q = j := by
          by_contra hne
          apply h0
          rw [hh'.1 q j (Or.inl hjr), if_neg hne]
        subst hqj
        rw [block_mul_col hh hg i q hj hi]
      · have hqW : r ≤ q.val ∧ q.val ≤ r + k := by
          by_contra hc
          apply h0
          have hne : q ≠ j := by
            intro e
            subst e
            omega
          rw [hh'.2 q j (by omega), if_neg hne]
        rw [block_mul_col hh hg i q hqW.2 (by omega)]
  rw [Matrix.mul_apply, Finset.sum_congr rfl (fun q _ => term q), ← Matrix.mul_apply, hinv,
    Matrix.one_apply]

theorem mul_apply_of_row {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hrow : ∀ p, h i p = if i = p then 1 else 0) : (h * M) i j = M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [hrow, if_pos rfl, one_mul]
  · intro p _ hp
    rw [hrow, if_neg (Ne.symm hp), zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem mul_apply_of_col {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hcol : ∀ q, h q j = if q = j then 1 else 0) : (M * h) i j = M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [hcol, if_pos rfl, mul_one]
  · intro q _ hq
    rw [hcol, if_neg hq, mul_zero]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem mulVec_apply_of_row {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1))
    (hrow : ∀ p, h i p = if i = p then 1 else 0) : (h *ᵥ v) i = v i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single i]
  · rw [hrow, if_pos rfl, one_mul]
  · intro p _ hp
    rw [hrow, if_neg (Ne.symm hp), zero_mul]
  · intro h'
    exact absurd (Finset.mem_univ _) h'

theorem ellA_conj (z : Fin (2 * r + k + 1) → ℂ)
    {h h' g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : block k r h) (hh' : block k r h') (hz : h' *ᵥ z = z) (a : Fin r) :
    ellA k r z (h * g * h') a = ellA k r z g a := by
  unfold ellA
  have hrow : ∀ p, h (eI k r a) p = if eI k r a = p then 1 else 0 :=
    fun p => hh.2 _ p (by simp only [eI]; omega)
  by_cases ha : a.val + 1 < r
  · rw [dite_eq_left ha, dite_eq_left ha, mul_apply_of_col _ _ _ (fun q => hh'.1 q _ (by simp only [eI]; omega)),
      mul_apply_of_row _ _ _ hrow]
  · rw [dite_eq_right ha, dite_eq_right ha, ← Matrix.mulVec_mulVec, hz, ← Matrix.mulVec_mulVec,
      mulVec_apply_of_row _ _ hrow]

theorem uw_conj_mem {z : Fin (2 * r + k + 1) → ℂ}
    {h m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) (hm : m ∈ Nset k r) : h⁻¹ * m * h ∈ Nset k r := by
  have hinv := uw_inv hh
  have hu := isUnit_of_uh hh.1
  have hm' := (nset_iff m).1 hm
  exact (nset_iff _).2 ⟨uh_mul (uh_mul hinv.1 hm'.1) hh.1,
    conj_col (uw_block hinv) (uw_block hh) (Matrix.nonsing_inv_mul _ hu) hm'.2⟩

theorem psiGen_conj (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ)
    {h m : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : psiGen k r z c (h⁻¹ * m * h) = psiGen k r z c m := by
  have hinv := uw_inv hh
  unfold psiGen
  congr 4
  apply Finset.sum_congr rfl
  intro a _
  rw [ellA_conj z (uw_block hinv) (uw_block hh) hh.2.2 a]

end WlocSk.UnitaryGroupBasics
end
end

open Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S WlocSk.UnitaryGroupBasics

noncomputable section

theorem subgroup_hypothesis_holds : WlocSk.SGrp := by
  intro k r z c hz _
  refine ⟨fun h hh => hh.1, fun m hm => hm.1, ?_, ?_, ?_⟩
  · intro h hh h' hh'
    exact ⟨uw_mul hh hh', uw_inv hh, Matrix.mul_nonsing_inv _ (isUnit_of_uh hh.1)⟩
  · intro m hm m' hm'
    exact ⟨mem_n_mul hm hm', mem_n_inv hm, Matrix.mul_nonsing_inv _ (isUnit_of_uh hm.1),
      psiGen_mul z c hz hm hm', psiGen_norm z c m⟩
  · intro h hh m hm
    exact ⟨uw_conj_mem hh hm, psiGen_conj z c hh⟩
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.RepresentationUnitary
open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace WlocSk.UnitaryRepLocal

open Formalism.QuantumDeterminants Formalism.MainNotions.S

variable {k r : ℕ}

abbrev Mx (k r : ℕ) := Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ

theorem uh_mul {a b : Mx k r} (ha : a ∈ UH (Hpk k r)) (hb : b ∈ UH (Hpk k r)) : a * b ∈ UH (Hpk k r) :=
  WlocSk.UnitaryGroupBasics.uh_mul ha hb

theorem uh_inv {a : Mx k r} (ha : a ∈ UH (Hpk k r)) :
    a * a⁻¹ = 1 ∧ a⁻¹ * a = 1 ∧ a⁻¹ ∈ UH (Hpk k r) := by
  have hu := WlocSk.UnitaryGroupBasics.isUnit_of_uh ha
  exact ⟨Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu, WlocSk.UnitaryGroupBasics.uh_inv ha⟩

theorem hpk_sq : Hpk k r * Hpk k r = 1 := WlocSk.UnitaryGroupBasics.hpk_sq

theorem col_eq (g : Mx k r) (j : Fin (2 * r + k + 1)) : g *ᵥ bvec j = fun i => g i j := by
  funext i
  simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]

def inB (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val < r + k

instance (i : Fin (2 * r + k + 1)) : Decidable (inB k r i) := by unfold inB; infer_instance

def eB (k r : ℕ) (m : Fin k) : Fin (2 * r + k + 1) := ⟨r + m.val, by omega⟩

theorem eB_inj : Function.Injective (eB k r) := by
  intro a b h; apply Fin.ext; have := congrArg Fin.val h; simp [eB] at this; omega

theorem eB_inB (m : Fin k) : inB k r (eB k r m) := by unfold inB eB; simp

theorem eq_eB_of_inB {i : Fin (2 * r + k + 1)} (hi : inB k r i) : i = eB k r ⟨i.val - r, by unfold inB at hi; omega⟩ := by
  apply Fin.ext; unfold inB at hi; simp [eB]; omega

def ub (c : Mx k r) : Matrix (Fin k) (Fin k) ℂ := fun m m' => c (eB k r m) (eB k r m')

theorem blockW_in {h : Matrix (Fin k) (Fin k) ℂ} {i j : Fin (2 * r + k + 1)} (hi : inB k r i) (hj : inB k r j) :
    blockW k r h i j = h ⟨i.val - r, by unfold inB at hi; omega⟩ ⟨j.val - r, by unfold inB at hj; omega⟩ := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  have hj' : r ≤ j.val ∧ j.val < r + k := hj
  unfold blockW; rw [dite_eq_left hi', dite_eq_left hj']

theorem blockW_in_out {h : Matrix (Fin k) (Fin k) ℂ} {i j : Fin (2 * r + k + 1)} (hi : inB k r i) (hj : ¬ inB k r j) :
    blockW k r h i j = 0 := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  have hj' : ¬ (r ≤ j.val ∧ j.val < r + k) := hj
  unfold blockW; rw [dite_eq_left hi', dite_eq_right hj']

theorem blockW_out {h : Matrix (Fin k) (Fin k) ℂ} {i j : Fin (2 * r + k + 1)} (hi : ¬ inB k r i) :
    blockW k r h i j = if i = j then 1 else 0 := by
  have hi' : ¬ (r ≤ i.val ∧ i.val < r + k) := hi
  unfold blockW; rw [dite_eq_right hi']

theorem blockW_eB (h : Matrix (Fin k) (Fin k) ℂ) (m m' : Fin k) : blockW k r h (eB k r m) (eB k r m') = h m m' := by
  rw [blockW_in (eB_inB m) (eB_inB m')]
  congr 1 <;> apply Fin.ext <;> simp [eB]

theorem sum_block (F : Fin (2 * r + k + 1) → ℂ) (hF : ∀ l, ¬ inB k r l → F l = 0) :
    ∑ l, F l = ∑ m : Fin k, F (eB k r m) := by
  symm
  refine Finset.sum_of_injOn (eB k r) eB_inj.injOn (fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _))
    (fun i _ hi => hF i ?_) (fun _ _ => rfl)
  intro hb
  exact hi ⟨_, by simp, (eq_eB_of_inB hb).symm⟩

theorem blockW_mul (h₁ h₂ : Matrix (Fin k) (Fin k) ℂ) :
    blockW k r (h₁ * h₂) = blockW k r h₁ * blockW k r h₂ := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : inB k r i
  · rw [sum_block _ (fun l hl => by rw [blockW_in_out hi hl, zero_mul])]
    by_cases hj : inB k r j
    · rw [eq_eB_of_inB hi, eq_eB_of_inB hj, blockW_eB, Matrix.mul_apply]
      exact Finset.sum_congr rfl fun m _ => by rw [blockW_eB, blockW_eB]
    · rw [blockW_in_out hi hj]
      exact (Finset.sum_eq_zero fun m _ => by rw [blockW_in_out (eB_inB m) hj, mul_zero]).symm
  · rw [blockW_out hi, Finset.sum_eq_single i (fun l _ hl => by rw [blockW_out hi, if_neg (Ne.symm hl), zero_mul])
      (fun h => absurd (Finset.mem_univ i) h), blockW_out hi, if_pos rfl, one_mul, blockW_out hi]

theorem hpk_in_col {i m : Fin (2 * r + k + 1)} (hm : inB k r m) : Hpk k r i m = if i = m then 1 else 0 := by
  unfold inB at hm
  unfold Hpk
  by_cases him : i = m
  · subst him; rw [if_pos rfl]
    rw [if_neg (by omega), if_neg (by omega), if_pos ⟨by omega, by omega, rfl⟩, if_neg (by omega)]
  · rw [if_neg him]
    have : i.val ≠ m.val := fun h => him (Fin.ext h)
    rw [if_neg (by omega), if_neg (by omega), if_neg (by tauto)]

theorem eq_blockW {c : Mx k r} (hc : c ∈ UH (Hpk k r))
    (hfix : ∀ l, ¬ inB k r l → c *ᵥ bvec l = bvec l) : c = blockW k r (ub c) := by
  have hcol : ∀ i l, ¬ inB k r l → c i l = if i = l then 1 else 0 := by
    intro i l hl
    have := congrFun (hfix l hl) i
    simp only [col_eq] at this
    rw [this]; simp [bvec, Pi.single_apply]

  have hHc : ∀ l j, ¬ inB k r l → inB k r j → (Hpk k r * c) l j = 0 := by
    intro l j hl hj
    have hU : cᴴ * Hpk k r * c = Hpk k r := hc
    have e1 := congrFun (congrFun hU l) j
    have e2 : (cᴴ * Hpk k r * c) l j = (Hpk k r * c) l j := by
      rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single l]
      · rw [Matrix.conjTranspose_apply, hcol l l hl, if_pos rfl, star_one, one_mul]
      · intro m _ hm
        rw [Matrix.conjTranspose_apply, hcol m l hl, if_neg hm, star_zero, zero_mul]
      · intro h; exact absurd (Finset.mem_univ l) h
    have hne : l ≠ j := fun h => hl (h ▸ hj)
    rw [← e2, e1, hpk_in_col hj, if_neg hne]
  have hoff : ∀ i j, ¬ inB k r i → inB k r j → c i j = 0 := by
    intro i j hi hj
    have hsq : Hpk k r * (Hpk k r * c) = c := by rw [← Matrix.mul_assoc, hpk_sq, Matrix.one_mul]
    rw [← hsq, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : inB k r m
    · have hne : i ≠ m := fun h => hi (h ▸ hm)
      rw [hpk_in_col hm, if_neg hne, zero_mul]
    · rw [hHc m j hm hj, mul_zero]
  ext i j
  by_cases hi : inB k r i
  · by_cases hj : inB k r j
    · rw [eq_eB_of_inB hi, eq_eB_of_inB hj, blockW_eB]; rfl
    · have hne : i ≠ j := fun h => hj (h ▸ hi)
      rw [blockW_in_out hi hj, hcol i j hj, if_neg hne]
  · rw [blockW_out hi]
    by_cases hj : inB k r j
    · have hne : i ≠ j := fun h => hi (h ▸ hj)
      rw [hoff i j hi hj, if_neg hne]
    · exact hcol i j hj

theorem ub_unitary {c : Mx k r} (hc : c ∈ UH (Hpk k r)) (hb : c = blockW k r (ub c)) :
    ub c ∈ UJset (allPos k) := by
  show (ub c)ᴴ * Formalism.REAL.Jm (allPos k) * ub c = Formalism.REAL.Jm (allPos k)
  have hJ : Formalism.REAL.Jm (allPos k) = 1 := by
    unfold Formalism.REAL.Jm allPos; simp
  rw [hJ, Matrix.mul_one]
  have hU : cᴴ * Hpk k r * c = Hpk k r := hc
  ext m m'
  have e := congrFun (congrFun hU (eB k r m)) (eB k r m')
  rw [hpk_in_col (eB_inB m')] at e
  rw [Matrix.one_apply]
  have hin : (eB k r m = eB k r m') ↔ (m = m') := eB_inj.eq_iff
  rw [Matrix.mul_apply] at e
  rw [sum_block _ (fun l hl => by
    have hne : l ≠ eB k r m' := fun h => hl (h ▸ eB_inB m')
    rw [hb, blockW_out hl, if_neg hne, mul_zero])] at e
  rw [Matrix.mul_apply]
  have hterm : ∀ t : Fin k, (cᴴ * Hpk k r) (eB k r m) (eB k r t) * c (eB k r t) (eB k r m') =
      (ub c)ᴴ m t * ub c t m' := by
    intro t
    rw [Matrix.mul_apply, Finset.sum_eq_single (eB k r t)]
    · rw [hpk_in_col (eB_inB t), if_pos rfl, mul_one]; rfl
    · intro l _ hl; rw [hpk_in_col (eB_inB t), if_neg hl, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  simp_rw [hterm] at e
  rw [e]
  by_cases h : m = m'
  · rw [if_pos (hin.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (hin.mp h')), if_neg h]

theorem piAll_loc (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ) (Wp : Type) [NormedAddCommGroup Wp]
    [InnerProductSpace ℂ Wp] (π : Mx k r → (Wp →L[ℂ] Wp)) (hz : inWb k r z) (hT : 0 < Tz k r z)
    (hπ : IsHCTypeW k r z u π) :
    π 1 = 1 ∧ (∀ a ∈ UWset k r z, ∀ b ∈ UWset k r z, π (a * b) = (π a).comp (π b)) ∧
      ∀ a ∈ UWset k r z, ∀ x : Wp, ‖π a x‖ = ‖x‖ := by
  obtain ⟨g, hg, hπU⟩ := hπ
  obtain ⟨hgU, hgfix, hgz⟩ := hg
  obtain ⟨-, -, ⟨⟨hπ1, hπmul⟩, hπiso, -⟩, -⟩ := hπU
  have hgi := uh_inv hgU

  have hfixg : ∀ a ∈ UWset k r z, ∀ l, ¬ inB k r l → a *ᵥ (g *ᵥ bvec l) = g *ᵥ bvec l := by
    intro a ha l hl
    unfold inB at hl
    by_cases h1 : l.val < r
    · have hl' : l = eI k r ⟨l.val, h1⟩ := Fin.ext rfl
      rw [hl', (hgfix ⟨l.val, h1⟩).1, (ha.2.1 ⟨l.val, h1⟩).1]
    · by_cases h2 : r + k < l.val
      · have hl' : l = esI k r ⟨2 * r + k - l.val, by omega⟩ := by apply Fin.ext; simp [esI]; omega
        rw [hl', (hgfix _).2, (ha.2.1 _).2]
      · have hl' : l = wI k r (Fin.last k) := by apply Fin.ext; simp [wI]; omega
        have hs : ((Real.sqrt (Tz k r z) : ℝ) : ℂ) ≠ 0 := by
          have := Real.sqrt_pos.mpr hT; exact_mod_cast this.ne'
        obtain ⟨t, ht⟩ : ∃ t : ℂ, t = ((Real.sqrt (Tz k r z) : ℝ) : ℂ) := ⟨_, rfl⟩
        rw [← ht] at hgz hs
        have hgw : g *ᵥ bvec (wI k r (Fin.last k)) = t⁻¹ • z := by
          calc g *ᵥ bvec (wI k r (Fin.last k)) = t⁻¹ • (t • g *ᵥ bvec (wI k r (Fin.last k))) := by
                rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
            _ = t⁻¹ • z := by rw [← Matrix.mulVec_smul, hgz]
        rw [hl', hgw, Matrix.mulVec_smul, ha.2.2]
  let hOf : Mx k r → Matrix (Fin k) (Fin k) ℂ := fun a => ub (g⁻¹ * a * g)
  have hstruct : ∀ a ∈ UWset k r z, g⁻¹ * a * g ∈ UH (Hpk k r) ∧
      g⁻¹ * a * g = blockW k r (hOf a) ∧ hOf a ∈ UJset (allPos k) ∧ a = g * blockW k r (hOf a) * g⁻¹ := by
    intro a ha
    have hc : g⁻¹ * a * g ∈ UH (Hpk k r) := uh_mul (uh_mul hgi.2.2 ha.1) hgU
    have hb : g⁻¹ * a * g = blockW k r (hOf a) := by
      refine eq_blockW hc fun l hl => ?_
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hfixg a ha l hl, Matrix.mulVec_mulVec, hgi.2.1,
        Matrix.one_mulVec]
    refine ⟨hc, hb, ub_unitary hc hb, ?_⟩
    rw [← hb]
    calc a = (g * g⁻¹) * a * (g * g⁻¹) := by rw [hgi.1, Matrix.one_mul, Matrix.mul_one]
      _ = g * (g⁻¹ * a * g) * g⁻¹ := by simp only [Matrix.mul_assoc]
  have hB1 : blockW k r (1 : Matrix (Fin k) (Fin k) ℂ) = 1 := by
    ext i j
    by_cases hi : inB k r i
    · by_cases hj : inB k r j
      · rw [blockW_in hi hj, Matrix.one_apply, Matrix.one_apply]
        by_cases h : i = j
        · subst h; simp
        · rw [if_neg h, if_neg]; intro h'; apply h; apply Fin.ext
          have := congrArg Fin.val h'; unfold inB at hi hj; simp at this; omega
      · have hne : i ≠ j := fun h => hj (h ▸ hi)
        rw [blockW_in_out hi hj, Matrix.one_apply, if_neg hne]
    · rw [blockW_out hi, Matrix.one_apply]
  refine ⟨?_, ?_, ?_⟩
  · have := hπ1
    simp only [hB1, Matrix.mul_one, hgi.1] at this
    exact this
  · intro a ha b hb
    obtain ⟨-, hba, hua, ea⟩ := hstruct a ha
    obtain ⟨-, hbb, hub, eb⟩ := hstruct b hb
    have hab : a * b = g * blockW k r (hOf a * hOf b) * g⁻¹ := by
      calc a * b = (g * blockW k r (hOf a) * g⁻¹) * (g * blockW k r (hOf b) * g⁻¹) := by rw [← ea, ← eb]
        _ = g * (blockW k r (hOf a) * blockW k r (hOf b)) * g⁻¹ := by
          simp only [Matrix.mul_assoc]; rw [← Matrix.mul_assoc g⁻¹ g, hgi.2.1, Matrix.one_mul]
        _ = g * blockW k r (hOf a * hOf b) * g⁻¹ := by rw [blockW_mul]
    have hm := hπmul _ hua _ hub
    simp only at hm
    rw [hab, hm, ← ea, ← eb]
  · intro a ha x
    obtain ⟨-, -, hua, ea⟩ := hstruct a ha
    rw [ea]
    exact hπiso _ hua x

end WlocSk.UnitaryRepLocal

open WlocSk.UnitaryRepLocal in
theorem representation_unitary : WlocSk.PiUnit := by
  intro k r z u Vp _ _ π hz hT hπ
  obtain ⟨h1, h2, h3⟩ := piAll_loc z u Vp π hz hT hπ
  exact ⟨⟨h1, h2⟩, h3⟩
end
end
