module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeIntegralUnipotentStabilizerOfTerm
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegerPointsCoverRealPointsRootCoordinates

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserCovolumeLeRootCoordinateCover
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserHaarRootCoordinatesLeLebesgue
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RatCoordConjEqStCoord
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopVol

private theorem hJ_smul_right_flag_measures {n : ℕ} (ε : Fin n → Bool) (c : ℂ) (x y : Fin n → ℂ) :
    Formalism.L2.SG.HidaSetting.hJ ε x (c • y) = c * Formalism.L2.SG.HidaSetting.hJ ε x y := by
  unfold Formalism.L2.SG.HidaSetting.hJ
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem ratCoord_conj_eq_stCoord : ∀ (D : D7) (X : HidaSetting D) (u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γ s y : X.B.I.Ginf) (τ : D.what₂.Tau) (q : GlobalTheory.LoopV.roots (ptMat w)) (p : Formalism.L2.SG.RealObj.FreeE w), p.1 = q.1 → GlobalTheory.LoopVol.ratCoord X u' w γ s (s * y * s⁻¹) τ q = ((D.host.rdE : ℂ) ^ (q.1.2.1 - q.1.1.1))⁻¹ * Formalism.L2.SG.RealObj.stCoord X u' w γ y (X.pl.symm τ) p := by
  intro D X u' w γ s y τ q p hpq
  obtain ⟨pq, hp⟩ := p
  obtain ⟨qq, hq⟩ := q
  simp only at hpq
  subst hpq

  have hconj : s⁻¹ * (s * y * s⁻¹) * s = y := by group
  have hab : pq.1.val < pq.2.val := hp.1
  have hbr : pq.2.val ≤ D.R.rS := Nat.lt_succ_iff.mp pq.2.isLt
  have hrd : (D.host.rdE : ℂ) ≠ 0 := by
    have h1 := GlobalTheory.RealPlaces.one_le_rdE D
    exact Complex.ofReal_ne_zero.mpr (by linarith)
  unfold GlobalTheory.LoopVol.ratCoord Formalism.L2.SG.RealObj.stCoord
  rw [hconj]
  unfold Formalism.L2.SG.RealObj.frm Formalism.L2.SG.RealObj.famSc
  simp only [Complex.ofReal_one, one_pow, inv_one, one_smul, Matrix.mulVec_smul, hJ_smul_right_flag_measures]

  have hsplit : D.R.rS - pq.1.val = (pq.2.val - pq.1.val) + (D.R.rS - pq.2.val) := by omega
  rw [hsplit, pow_add]
  field_simp

end GlobalTheory.LoopVol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreimageReindexScaleComplexLeStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreimageReindexScaleComplexLe
namespace GlobalTheory.CoordScale
open MeasureTheory

theorem sigmaFinite_smul {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] {c : ENNReal}
    (hc : c ≠ ⊤) : SigmaFinite (c • μ) := by
  have h : c • μ = c.toNNReal • μ := by
    rw [ENNReal.smul_def, ENNReal.coe_toNNReal hc]
  rw [h]
  infer_instance

theorem pi_smul_ne_top {ι : Type} [Fintype ι] {α : ι → Type} [∀ i, MeasurableSpace (α i)]
    (μ : ∀ i, Measure (α i)) [∀ i, SigmaFinite (μ i)] (c : ι → ENNReal) (hc : ∀ i, c i ≠ ⊤) :
    Measure.pi (fun i => c i • μ i) = (∏ i, c i) • Measure.pi μ := by
  have : ∀ i, SigmaFinite (c i • μ i) := fun i => sigmaFinite_smul (μ i) (hc i)
  refine Measure.pi_eq (fun s hs => ?_)
  simp only [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, Finset.prod_mul_distrib]

theorem measurePreserving_inv_mul (r : ℝ) (hr : 0 < r) :
    MeasurePreserving (fun z : ℂ => ((r : ℂ))⁻¹ * z) volume
      (ENNReal.ofReal (r ^ 2) • (volume : Measure ℂ)) := by
  refine ⟨measurable_id.const_mul _, ?_⟩
  have hfun : (fun z : ℂ => ((r : ℂ))⁻¹ * z) = fun z => (r⁻¹ : ℝ) • z := by
    funext z
    rw [Complex.real_smul, Complex.ofReal_inv]
  rw [hfun, Measure.map_addHaar_smul volume (inv_ne_zero hr.ne'), Complex.finrank_real_complex,
    inv_pow, inv_inv, abs_of_pos (by positivity)]

private theorem map_pi_reindex_eq_pi_of_map_eq {ι ι' β γ : Type} [Fintype ι] [Fintype ι'] [MeasurableSpace β]
    [MeasurableSpace γ] (e : ι ≃ ι') (μ : Measure β) [SigmaFinite μ] (ν : ι → Measure γ)
    [∀ i, SigmaFinite (ν i)] (h : ι → β → γ) (hh : ∀ i, Measurable (h i))
    (hmap : ∀ i, Measure.map (h i) μ = ν i) :
    Measure.map (fun (x : ι' → β) (i : ι) => h i (x (e i))) (Measure.pi fun _ => μ) =
      Measure.pi ν := by
  have hm : Measurable (fun (x : ι' → β) (i : ι) => h i (x (e i))) :=
    Measurable.of_eval (fun i => (hh i).comp (measurable_pi_apply (e i)))
  symm
  refine Measure.pi_eq (fun s hs => ?_)
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun (x : ι' → β) (i : ι) => h i (x (e i))) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i' => h (e.symm i') ⁻¹' s (e.symm i')) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi]
    constructor
    · intro hx i'
      have := hx (e.symm i')
      rwa [Equiv.apply_symm_apply] at this
    · intro hx i
      have := hx (e i)
      rwa [Equiv.symm_apply_apply] at this
  rw [hpre, Measure.pi_pi]
  refine (Finset.prod_congr rfl (fun i' _ => ?_)).trans (Equiv.prod_comp e.symm (fun i => ν i (s i)))
  rw [← hmap (e.symm i'), Measure.map_apply (hh _) (hs _)]

theorem measure_preimage_reindex_scale_le : ∀ (ι ι' κ κ' : Type) [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ'] (e : ι ≃ ι') (f : κ ≃ κ') (ρ c : ℝ) (d : κ → ℕ), 1 ≤ ρ → c ≤ 1 → ∀ A : Set (ι → κ → ℂ), MeasurableSet A → (MeasureTheory.Measure.pi fun _ : ι' => MeasureTheory.Measure.pi fun _ : κ' => ENNReal.ofReal c • (MeasureTheory.volume : MeasureTheory.Measure ℂ)) ((fun (x : ι' → κ' → ℂ) (i : ι) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * x (e i) (f q)) ⁻¹' A) ≤ MeasureTheory.volume A * ENNReal.ofReal (ρ ^ (2 * Fintype.card ι * ∑ q, d q)) := by
  intro ι ι' κ κ' _ _ _ _ e f ρ c d hρ hc A hA
  have hρ0 : 0 < ρ := lt_of_lt_of_le one_pos hρ
  set C : ENNReal := ENNReal.ofReal c with hCdef
  have hCt : C ≠ ⊤ := ENNReal.ofReal_ne_top
  have : SigmaFinite (C • (volume : Measure ℂ)) := sigmaFinite_smul _ hCt
  set w : κ → ENNReal := fun q => C * ENNReal.ofReal ((ρ ^ d q) ^ 2) with hwdef
  have hwt : ∀ q, w q ≠ ⊤ := fun q => ENNReal.mul_ne_top hCt ENNReal.ofReal_ne_top
  have : ∀ q, SigmaFinite (w q • (volume : Measure ℂ)) := fun q => sigmaFinite_smul _ (hwt q)
  have hin : Measure.map (fun (y : κ' → ℂ) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * y (f q))
      (Measure.pi fun _ : κ' => C • (volume : Measure ℂ)) =
      Measure.pi fun q : κ => w q • (volume : Measure ℂ) := by
    refine map_pi_reindex_eq_pi_of_map_eq f (C • (volume : Measure ℂ)) (fun q => w q • (volume : Measure ℂ))
      (fun q z => ((ρ : ℂ) ^ d q)⁻¹ * z) (fun q => measurable_const.mul measurable_id) (fun q => ?_)
    show Measure.map (fun z : ℂ => ((ρ : ℂ) ^ d q)⁻¹ * z) (C • volume) = w q • volume
    have hfun : (fun z : ℂ => ((ρ : ℂ) ^ d q)⁻¹ * z) = fun z => (((ρ ^ d q : ℝ) : ℂ))⁻¹ * z := by
      funext z
      rw [Complex.ofReal_pow]
    rw [hfun, Measure.map_smul (R := ENNReal) C
      (hf := (measurable_const_mul _).aemeasurable),
      (measurePreserving_inv_mul (ρ ^ d q) (pow_pos hρ0 _)).map_eq,
      smul_smul]
  set K : ENNReal := ∏ q, w q with hKdef
  have hKt : K ≠ ⊤ := ENNReal.prod_ne_top (fun q _ => hwt q)
  have hin' : Measure.map (fun (y : κ' → ℂ) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * y (f q))
      (Measure.pi fun _ : κ' => C • (volume : Measure ℂ)) = K • (volume : Measure (κ → ℂ)) := by
    rw [hin, pi_smul_ne_top (fun _ => (volume : Measure ℂ)) w hwt]
    rfl
  have : SigmaFinite (K • (volume : Measure (κ → ℂ))) := sigmaFinite_smul _ hKt
  have hinm : Measurable (fun (y : κ' → ℂ) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * y (f q)) :=
    Measurable.of_eval (fun q => (measurable_pi_apply (f q)).const_mul _)
  have hout : Measure.map (fun (x : ι' → κ' → ℂ) (i : ι) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * x (e i) (f q))
      (MeasureTheory.Measure.pi fun _ : ι' =>
        MeasureTheory.Measure.pi fun _ : κ' => ENNReal.ofReal c • (MeasureTheory.volume : MeasureTheory.Measure ℂ)) =
      (K ^ Fintype.card ι) • (volume : Measure (ι → κ → ℂ)) := by
    have h1 := map_pi_reindex_eq_pi_of_map_eq e (Measure.pi fun _ : κ' => C • (volume : Measure ℂ))
      (fun _ : ι => K • (volume : Measure (κ → ℂ)))
      (fun _ (y : κ' → ℂ) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * y (f q)) (fun _ => hinm) (fun _ => hin')
    refine h1.trans ?_
    rw [pi_smul_ne_top (fun _ : ι => (volume : Measure (κ → ℂ))) (fun _ => K) (fun _ => hKt),
      Finset.prod_const, Finset.card_univ]
    rfl
  have hgm : Measurable (fun (x : ι' → κ' → ℂ) (i : ι) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * x (e i) (f q)) :=
    Measurable.of_eval (fun i => hinm.comp (measurable_pi_apply (e i)))
  rw [← Measure.map_apply hgm hA, hout, Measure.smul_apply, smul_eq_mul, mul_comm]
  have hC1 : C ≤ 1 := ENNReal.ofReal_le_one.mpr hc
  have hK1 : K ≤ ∏ q, ENNReal.ofReal ((ρ ^ d q) ^ 2) := by
    refine Finset.prod_le_prod' (fun q _ => ?_)
    calc w q = C * ENNReal.ofReal ((ρ ^ d q) ^ 2) := rfl
      _ ≤ 1 * ENNReal.ofReal ((ρ ^ d q) ^ 2) := by gcongr
      _ = ENNReal.ofReal ((ρ ^ d q) ^ 2) := one_mul _
  have hprod : ∏ q, ENNReal.ofReal ((ρ ^ d q) ^ 2) = ENNReal.ofReal (∏ q, (ρ ^ d q) ^ 2) :=
    (ENNReal.ofReal_prod_of_nonneg (fun q _ => by positivity)).symm
  have hreal : (∏ q, (ρ ^ d q) ^ 2) ^ Fintype.card ι = ρ ^ (2 * Fintype.card ι * ∑ q, d q) := by
    rw [Finset.prod_pow, Finset.prod_pow_eq_pow_sum, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hK2 : K ^ Fintype.card ι ≤ ENNReal.ofReal (ρ ^ (2 * Fintype.card ι * ∑ q, d q)) := by
    rw [← hreal, ENNReal.ofReal_pow (by positivity), ← hprod]
    exact pow_le_pow_left' hK1 _
  gcongr

end GlobalTheory.CoordScale
end

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_preimage_reindex_scale_complex_le : ∀ (ι ι' κ κ' : Type) [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ'] (e : ι ≃ ι') (f : κ ≃ κ') (ρ c : ℝ) (d : κ → ℕ), 1 ≤ ρ → c ≤ 1 → ∀ A : Set (ι → κ → ℂ), MeasurableSet A → (MeasureTheory.Measure.pi fun _ : ι' => MeasureTheory.Measure.pi fun _ : κ' => ENNReal.ofReal c • (MeasureTheory.volume : MeasureTheory.Measure ℂ)) ((fun (x : ι' → κ' → ℂ) (i : ι) (q : κ) => ((ρ : ℂ) ^ d q)⁻¹ * x (e i) (f q)) ⁻¹' A) ≤ MeasureTheory.volume A * ENNReal.ofReal (ρ ^ (2 * Fintype.card ι * ∑ q, d q)) := by
  first | exact @GlobalTheory.CoordScale.measure_preimage_reindex_scale_le | exact GlobalTheory.CoordScale.measure_preimage_reindex_scale_le | (intros; apply GlobalTheory.CoordScale.measure_preimage_reindex_scale_le <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRootsPointMatrixIffSameBlock
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRootsPointMatrixIffSameBlock
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RootsBijection

open Formalism.L2.SG.RealObj in
theorem fwd {K : Type*} [Zero K] : ∀ (bs : List (K × ℕ)) (i j a b : ℕ), Formalism.MainNotions.S.ptEntry bs i a ≠ 0 →
    Formalism.MainNotions.S.ptEntry bs j b ≠ 0 → a < b → j < i → blkOf bs a = blkOf bs b
  | [], _, _, _, _, h, _, _, _ => by simp [Formalism.MainNotions.S.ptEntry] at h
  | (t, s) :: bs, i, j, a, b, h1, h2, hab, hji => by
    rw [Formalism.MainNotions.S.ptEntry] at h1 h2
    by_cases ha : a < s
    · by_cases hb : b < s
      · simp [blkOf, ha, hb]
      · exfalso
        rw [if_neg (show ¬ (j < s ∧ b < s) by omega)] at h2
        by_cases hj : s ≤ j
        · rw [if_neg (show ¬ (s ≤ i ∧ s ≤ a) by omega)] at h1
          by_cases hi : i < s
          · omega
          · rw [if_neg (show ¬ (i < s ∧ a < s) by omega)] at h1; exact h1 rfl
        · rw [if_neg (show ¬ (s ≤ j ∧ s ≤ b) by omega)] at h2; exact h2 rfl
    · have hb : ¬ b < s := by omega
      rw [if_neg (show ¬ (i < s ∧ a < s) by omega)] at h1
      rw [if_neg (show ¬ (j < s ∧ b < s) by omega)] at h2
      by_cases hi : s ≤ i
      · by_cases hj : s ≤ j
        · rw [if_pos ⟨hi, by omega⟩] at h1
          rw [if_pos ⟨hj, by omega⟩] at h2
          have := fwd bs (i - s) (j - s) (a - s) (b - s) h1 h2 (by omega) (by omega)
          simp [blkOf, ha, hb, this]
        · rw [if_neg (show ¬ (s ≤ j ∧ s ≤ b) by omega)] at h2; exact absurd rfl h2
      · rw [if_neg (show ¬ (s ≤ i ∧ s ≤ a) by omega)] at h1; exact absurd rfl h1

open Formalism.L2.SG.RealObj in
theorem bwd {K : Type*} [Zero K] : ∀ (bs : List (K × ℕ)), (∀ p ∈ bs, p.1 ≠ 0) → ∀ (a b : ℕ), a < b →
    b < (bs.map Prod.snd).sum → blkOf bs a = blkOf bs b →
    ∃ i j, j < i ∧ i < (bs.map Prod.snd).sum ∧ Formalism.MainNotions.S.ptEntry bs i a ≠ 0 ∧ Formalism.MainNotions.S.ptEntry bs j b ≠ 0
  | [], _, _, _, _, hb, _ => by simp at hb
  | (t, s) :: bs, hnz, a, b, hab, hbs, hbl => by
    have ht : t ≠ 0 := hnz (t, s) (by simp)
    simp only [List.map_cons, List.sum_cons] at hbs ⊢
    by_cases ha : a < s
    · have hb : b < s := by
        by_contra hb
        simp [blkOf, ha, hb] at hbl
      refine ⟨s - 1 - a, s - 1 - b, by omega, by omega, ?_, ?_⟩
      · rw [Formalism.MainNotions.S.ptEntry, if_pos ⟨by omega, ha⟩, if_pos (by omega)]; exact ht
      · rw [Formalism.MainNotions.S.ptEntry, if_pos ⟨by omega, hb⟩, if_pos (by omega)]; exact ht
    · have hb : ¬ b < s := by omega
      have hbl' : blkOf bs (a - s) = blkOf bs (b - s) := by
        simpa [blkOf, ha, hb] using hbl
      have htail :
          ∃ i j, j < i ∧ i < (bs.map Prod.snd).sum ∧
            Formalism.MainNotions.S.ptEntry bs i (a - s) ≠ 0 ∧
            Formalism.MainNotions.S.ptEntry bs j (b - s) ≠ 0 :=
        bwd bs (fun p hp => hnz p (List.mem_cons_of_mem _ hp)) (a - s) (b - s)
          (by omega) (by omega) hbl'
      rcases htail with ⟨i, j, hji, his, hi, hj⟩
      refine ⟨i + s, j + s, Nat.add_lt_add_right hji s, by omega, ?_, ?_⟩
      · simpa [Formalism.MainNotions.S.ptEntry, ha, Nat.le_of_not_gt ha] using hi
      · simpa [Formalism.MainNotions.S.ptEntry, hb, Nat.le_of_not_gt hb] using hj

end GlobalTheory.RootsBijection

theorem GlobalTheory.roots_ptMat_iff : ∀ (K : Type) [Field K] (n : ℕ) (w : Point K n) (a b : Fin n),
    (a, b) ∈ GlobalTheory.LoopV.roots (ptMat w) ↔ a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1 := by
  intro K _ n w a b
  unfold GlobalTheory.LoopV.roots
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [ptMat]
  constructor
  · rintro ⟨hab, i, j, hji, hi, hj⟩
    exact ⟨hab, GlobalTheory.RootsBijection.fwd w.1 i.1 j.1 a.1 b.1 hi hj hab hji⟩
  · rintro ⟨hab, hbl⟩
    obtain ⟨i, j, hji, hin, hi, hj⟩ := GlobalTheory.RootsBijection.bwd w.1 (fun p hp => (w.2.1 p hp).1) a.1 b.1 hab
      (by rw [w.2.2]; exact b.2) hbl
    rw [w.2.2] at hin
    exact ⟨hab, ⟨i, hin⟩, ⟨j, by omega⟩, hji, hi, hj⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemRootsPointMatrixIffSameBlockStatement
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_roots_point_matrix_iff_same_block : ∀ (K : Type) [Field K] (n : ℕ) (w : Point K n) (a b : Fin n), (a, b) ∈ GlobalTheory.LoopV.roots (ptMat w) ↔ a < b ∧ Formalism.L2.SG.RealObj.blkOf w.1 a.1 = Formalism.L2.SG.RealObj.blkOf w.1 b.1 := by
  first | exact @GlobalTheory.roots_ptMat_iff | exact GlobalTheory.roots_ptMat_iff | (intros; apply GlobalTheory.roots_ptMat_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserHaarRootCoordinatesLeLebesgue
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

namespace GlobalTheory.LoopVol

theorem pinned_ratCoord_le : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γw sf : X.B.I.Ginf) (μw : MeasureTheory.Measure X.B.I.Ginf), IsHaarOnSet X.B.I (Formalism.L2.SG.RealObj.StInf X u u' γw) μw → μw.map (Formalism.L2.SG.RealObj.stCoord X u' w γw) = Formalism.L2.SG.RealObj.muStab X w → D.host.ka / (X.B.g : ℝ) / Real.pi ≤ 1 → ∀ A : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), MeasurableSet A → (μw.map (fun y => sf * y * sf⁻¹)) (GlobalTheory.LoopVol.ratCoord X u' w γw sf ⁻¹' A) ≤ MeasureTheory.volume A * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) := by
  intro D X u u' w γw sf μw _hH hmap hc A hA
  classical

  let ι : GlobalTheory.LoopV.roots (ptMat w) ≃ Formalism.L2.SG.RealObj.FreeE w :=
    Equiv.subtypeEquivRight (fun p => GlobalTheory.T.mem_roots_point_matrix_iff_same_block D.host.E (D.R.rS + 1) w p.1 p.2)
  let d : GlobalTheory.LoopV.roots (ptMat w) → ℕ := fun q => q.1.2.1 - q.1.1.1
  let S : (NumberField.InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ) → (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ) :=
    fun x τ q => (((D.host.rdE : ℝ) : ℂ) ^ d q)⁻¹ * x (X.pl.symm τ) (ι q)
  have hS : Continuous S := by
    refine continuous_pi fun τ => continuous_pi fun q => continuous_const.mul ?_
    exact (continuous_apply _).comp (continuous_apply _)
  have hΦ : Continuous (fun y : X.B.I.Ginf => sf * y * sf⁻¹) :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hst := Formalism.L2.SG.Pf.LoopBPin.stCoord_cont (X := X) u' w γw
  have hrat := ratCoord_cont X u' w γw sf
  have hpre : (fun y : X.B.I.Ginf => sf * y * sf⁻¹) ⁻¹' (ratCoord X u' w γw sf ⁻¹' A) =
      Formalism.L2.SG.RealObj.stCoord X u' w γw ⁻¹' (S ⁻¹' A) := by
    ext y
    simp only [Set.mem_preimage]
    have : ratCoord X u' w γw sf (sf * y * sf⁻¹) = S (Formalism.L2.SG.RealObj.stCoord X u' w γw y) := by
      funext τ q
      exact ratCoord_conj_eq_stCoord D X u' w γw sf y τ q (ι q) rfl
    rw [this]
  have hB : MeasurableSet (S ⁻¹' A) := hS.measurable hA
  rw [Measure.map_apply hΦ.measurable (hrat.measurable hA), hpre,
    ← Measure.map_apply hst.measurable hB, hmap]
  have hrd : 1 ≤ D.host.rdE := GlobalTheory.RealPlaces.one_le_rdE (D := D)
  have key := GlobalTheory.T.measure_preimage_reindex_scale_complex_le D.what₂.Tau (NumberField.InfinitePlace X.B.I.F) (GlobalTheory.LoopV.roots (ptMat w)) (Formalism.L2.SG.RealObj.FreeE w)
    X.pl.symm ι D.host.rdE (D.host.ka / (X.B.g : ℝ) / Real.pi) d hrd hc A hA
  refine le_trans key ?_
  gcongr
  · rw [D.what₂.card_Tau]
  · have hsum : ∑ q : GlobalTheory.LoopV.roots (ptMat w), d q ≤ (D.R.rS + 1) ^ 3 := by
      calc ∑ q : GlobalTheory.LoopV.roots (ptMat w), d q ≤ ∑ _q : GlobalTheory.LoopV.roots (ptMat w), (D.R.rS + 1) :=
            Finset.sum_le_sum fun q _ => by
              have := q.1.2.2; simp only [d]; omega
        _ = Fintype.card (GlobalTheory.LoopV.roots (ptMat w)) * (D.R.rS + 1) := by simp
        _ ≤ (D.R.rS + 1) ^ 2 * (D.R.rS + 1) := by
            gcongr
            calc Fintype.card (GlobalTheory.LoopV.roots (ptMat w)) ≤ Fintype.card (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) :=
                  Fintype.card_subtype_le _
              _ = (D.R.rS + 1) ^ 2 := by simp [sq]
        _ = (D.R.rS + 1) ^ 3 := by ring
    exact hsum

end GlobalTheory.LoopVol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserHaarRootCoordinatesLeLebesgueStatement
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabiliserHaar_rootCoordinates_le_lebesgue : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (w : Point D.host.E (D.R.rS + 1)) (γw sf : X.B.I.Ginf) (μw : MeasureTheory.Measure X.B.I.Ginf), IsHaarOnSet X.B.I (Formalism.L2.SG.RealObj.StInf X u u' γw) μw → μw.map (Formalism.L2.SG.RealObj.stCoord X u' w γw) = Formalism.L2.SG.RealObj.muStab X w → D.host.ka / (X.B.g : ℝ) / Real.pi ≤ 1 → ∀ A : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), MeasurableSet A → (μw.map (fun y => sf * y * sf⁻¹)) (GlobalTheory.LoopVol.ratCoord X u' w γw sf ⁻¹' A) ≤ MeasureTheory.volume A * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) := by
  first | exact @GlobalTheory.LoopVol.pinned_ratCoord_le | exact GlobalTheory.LoopVol.pinned_ratCoord_le | (intros; apply GlobalTheory.LoopVol.pinned_ratCoord_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserCovolumeLeRootCoordinateCover
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar


open MeasureTheory in
theorem GlobalTheory.LoopVol.packing_pinned {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word} (s : TT Y u u')
    {γw g g' : X.B.I.Ginf} {μw : Measure X.B.I.Ginf} (hg : g ∈ X.SinfU u) (hg' : g' ∈ X.SinfU u')
    (hdec : s.pt.1 = g * γw * g'⁻¹) (hH : IsHaarOnSet X.B.I (Formalism.L2.SG.RealObj.StInf X u u' γw) μw)
    {K B : Set X.B.I.Ginf} (hK : Formalism.L2.SG.LoopTerm.IsFundR s K) (hB : MeasurableSet B)
    (hcov : ∀ r ∈ Formalism.L2.SG.TermOp.Vanish.Rset s, ∃ q ∈ Formalism.L2.SG.TermOp.ROinf s, q * r ∈ B) :
    (μw.map fun y => g * y * g⁻¹) K ≤ (μw.map fun y => g * y * g⁻¹) B := by
  obtain ⟨-, -, hconc, hinvw⟩ := hH
  obtain ⟨hKm, hKu⟩ := hK
  haveI := Formalism.L2.SG.TermOp.Vanish.ROsub_countable X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin
  set Γ := Formalism.L2.SG.TermOp.Vanish.ROsub X (X.Fu u) (X.Fu u') s.lam s.lam' s.lin with hΓ
  set μR := μw.map fun y => g * y * g⁻¹ with hμR
  have hcm : Measurable fun y : X.B.I.Ginf => g * y * g⁻¹ :=
    ((continuous_const.mul continuous_id).mul continuous_const).measurable
  have hRm : MeasurableSet (Formalism.L2.SG.TermOp.Vanish.Rset s) :=
    (Formalism.L2.SG.Pf.rClosedC_holds D X Y u u' s).measurableSet
  have hRc : μR (Formalism.L2.SG.TermOp.Vanish.Rset s)ᶜ = 0 := by
    rw [hμR, Measure.map_apply hcm hRm.compl]
    apply measure_mono_null _ hconc
    intro y hy
    exact fun hySt => hy (Formalism.L2.SG.LoopTerm.stInf_conj hg hg' hdec hySt)
  have hinv : ∀ q ∈ Γ, μR.map (fun x => q * x) = μR := by
    intro q hq
    have hq' := Formalism.L2.SG.LoopTerm.stInf_conj_inv hg hg' hdec (Formalism.L2.SG.Pf.LoopBPin.roinf_sub_rset s hq)
    rw [hμR, Measure.map_map (measurable_const_mul q) hcm]
    have e : (fun x => q * x) ∘ (fun y => g * y * g⁻¹) =
        (fun y => g * y * g⁻¹) ∘ (fun y => (g⁻¹ * q * g) * y) := by
      funext y; simp only [Function.comp]; group
    rw [e, ← Measure.map_map hcm (measurable_const_mul _), hinvw _ hq']
  have hpre : ∀ q ∈ Γ, ∀ C, MeasurableSet C → μR ((fun x => q * x) ⁻¹' C) = μR C := by
    intro q hq C hC
    rw [← Measure.map_apply (measurable_const_mul q) hC, hinv q hq]
  have h1 : μR K ≤ ∑' q : Γ, μR (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' B) := by
    calc μR K = μR (K ∩ Formalism.L2.SG.TermOp.Vanish.Rset s) := (measure_inter_conull hRc).symm
      _ ≤ μR (⋃ q : Γ, K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' B) := by
          refine measure_mono fun r hr => ?_
          obtain ⟨q, hq, hqr⟩ := hcov r hr.2
          exact Set.mem_iUnion.2 ⟨⟨q, hq⟩, hr.1, hqr⟩
      _ ≤ _ := measure_iUnion_le _
  have h2 : ∀ q : Γ, μR (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' B) =
      μR (B ∩ (fun x => ((q⁻¹ : Γ) : X.B.I.Ginf) * x) ⁻¹' K) := by
    intro q
    have hC : MeasurableSet (B ∩ (fun x => ((q⁻¹ : Γ) : X.B.I.Ginf) * x) ⁻¹' K) :=
      hB.inter (hKm.preimage (measurable_const_mul _))
    rw [← hpre q q.2 _ hC]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Subgroup.coe_inv, inv_mul_cancel_left]
    exact and_comm
  have h3 := Formalism.L2.SG.Pf.FormAllPf.decomp μR (Formalism.L2.SG.TermOp.Vanish.Rset s) hRc Γ B K hB hKm hKu
  have h4 : ∑' q : Γ, μR (K ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' B) = μR B := by
    rw [h3]
    simp_rw [h2]
    exact (Equiv.inv Γ).tsum_eq (fun q => μR (B ∩ (fun x => (q : X.B.I.Ginf) * x) ⁻¹' K))
  exact h1.trans_eq h4

theorem GlobalTheory.LoopVol.ka_div_le_one {D : D7} (X : HidaSetting D) {u u' : D.what₂.Word} (hSt : Formalism.MainNotions.S.Cnt.Stand D u u') :
    D.host.ka / (X.B.g : ℝ) / Real.pi ≤ 1 := by
  have hrd := GlobalTheory.RealPlaces.one_le_rdE D
  have hg0 := hSt.2.2.2.2.2.2.2.1.two_le
  have hg1 := hSt.2.2.2.2.2.2.2.2.1.two_le
  have h0 : (2 : ℝ) ≤ (D.host.g 0 : ℝ) := by exact_mod_cast hg0
  have h1 : (2 : ℝ) ≤ (D.host.g 1 : ℝ) := by exact_mod_cast hg1
  have hgR : (4 : ℝ) ≤ (X.B.g : ℝ) := by rw [X.g_eq]; push_cast; nlinarith
  have e : D.host.ka / (X.B.g : ℝ) / Real.pi = 2 / (D.host.rdE * X.B.g) := by
    rw [show D.host.ka = Real.pi / (D.host.rdE / 2) from rfl]
    have : (0 : ℝ) < D.host.rdE := by linarith
    have : (0 : ℝ) < (X.B.g : ℝ) := by linarith
    field_simp
  rw [e, div_le_one (by positivity)]
  nlinarith

theorem GlobalTheory.LoopVol.covolume_le_cover : ∀ Cg cb Cu cT CT C0 A : ℝ, ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ s : TT Y u u', s.relevant → s.G ≠ 0 → ∀ (w : Point D.host.E (D.R.rS + 1)) (μR : MeasureTheory.Measure X.B.I.Ginf) (K : Set X.B.I.Ginf), s.toTerm.atPt w → Formalism.L2.SG.VolPin.IsPinnedR s w μR → Formalism.L2.SG.LoopTerm.IsFundR s K → ∀ (L U : Formalism.MainNotions.S.Cnt.GramM D), IsLoUni L → IsUpUni U → ZhatOM (ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame)) = L * ptMat w * U → ∀ Ω : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), MeasurableSet Ω → (∀ c : D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ, ∃ n ∈ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u)) ∩ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame), ∃ a : Formalism.MainNotions.S.Cnt.GramM D, (∀ j : Fin (D.R.rS + 1), n (frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) j) = ∑ i : Fin (D.R.rS + 1), ((-1) ^ (i.val + j.val) * a i j) • frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) i) ∧ (fun τ (q : GlobalTheory.LoopV.roots (ptMat w)) => ((U * a * U⁻¹).map (embS D τ) * GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat w)) (c τ) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ) q.1.1 q.1.2) ∈ Ω) → μR K ≤ MeasureTheory.volume Ω * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) := by
  intro Cg cb Cu cT CT C0 A D X Y W large₂ u u' C' Cl hH s hrel hG w μR K hat hPin hK L U hL hU hZ Ω hΩ hcov
  obtain ⟨γw, sf, s', μw, hrep, hsf, hs', hdec, hμwH, hμwS, rfl⟩ := hPin
  obtain ⟨T, hT, hTc⟩ := GlobalTheory.T.integerPoints_cover_realPoints_rootCoordinates Cg cb Cu cT CT C0 A D X Y W large₂ u u' C' Cl hH s hrel hG w γw sf s' hat hrep hsf hs' hdec
    L U hL hU hZ Ω hcov
  have hTΩ : MeasurableSet (T ⁻¹' Ω) := hT.measurable hΩ
  have hBm : MeasurableSet (GlobalTheory.LoopVol.ratCoord X u' w γw sf ⁻¹' (T ⁻¹' Ω)) :=
    (GlobalTheory.LoopVol.ratCoord_cont X u' w γw sf).measurable hTΩ
  have hka := GlobalTheory.LoopVol.ka_div_le_one X hH.2.1
  calc (μw.map fun y => sf * y * sf⁻¹) K
      ≤ (μw.map fun y => sf * y * sf⁻¹) (GlobalTheory.LoopVol.ratCoord X u' w γw sf ⁻¹' (T ⁻¹' Ω)) :=
        GlobalTheory.LoopVol.packing_pinned s hsf hs' hdec hμwH hK hBm hTc
    _ ≤ MeasureTheory.volume (T ⁻¹' Ω) * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) :=
        GlobalTheory.T.stabiliserHaar_rootCoordinates_le_lebesgue D X u u' w γw sf μw hμwH hμwS hka _ hTΩ
    _ = MeasureTheory.volume Ω * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) := by
        rw [hT.measure_preimage hΩ.nullMeasurableSet]

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserCovolumeLeRootCoordinateCoverStatement
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabiliserCovolume_le_rootCoordinateCover : ∀ Cg cb Cu cT CT C0 A : ℝ, ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (W : WittDat X) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ s : TT Y u u', s.relevant → s.G ≠ 0 → ∀ (w : Point D.host.E (D.R.rS + 1)) (μR : MeasureTheory.Measure X.B.I.Ginf) (K : Set X.B.I.Ginf), s.toTerm.atPt w → Formalism.L2.SG.VolPin.IsPinnedR s w μR → Formalism.L2.SG.LoopTerm.IsFundR s K → ∀ (L U : Formalism.MainNotions.S.Cnt.GramM D), IsLoUni L → IsUpUni U → ZhatOM (ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame)) = L * ptMat w * U → ∀ Ω : Set (D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ), MeasurableSet Ω → (∀ c : D.what₂.Tau → GlobalTheory.LoopV.roots (ptMat w) → ℂ, ∃ n ∈ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u)) ∩ NLam (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame), ∃ a : Formalism.MainNotions.S.Cnt.GramM D, (∀ j : Fin (D.R.rS + 1), n (frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) j) = ∑ i : Fin (D.R.rS + 1), ((-1) ^ (i.val + j.val) * a i j) • frame (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) i) ∧ (fun τ (q : GlobalTheory.LoopV.roots (ptMat w)) => ((U * a * U⁻¹).map (embS D τ) * GlobalTheory.LoopV.ofRoots (GlobalTheory.LoopV.roots (ptMat w)) (c τ) : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) ℂ) q.1.1 q.1.2) ∈ Ω) → μR K ≤ MeasureTheory.volume Ω * ENNReal.ofReal (D.host.rdE ^ (2 * D.R.f * (D.R.rS + 1) ^ 3)) := by
  first | exact @GlobalTheory.LoopVol.covolume_le_cover | exact GlobalTheory.LoopVol.covolume_le_cover | (intros; apply GlobalTheory.LoopVol.covolume_le_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadMinorGramMatrixConstDoubleCoset
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadMinorGramMatrixConstDoubleCoset
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem leadMinorE_zhatL_dcrel :
    ∀ (D : D7) (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V) (T T' : D.host.E)
      (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS T'),
      Formalism.L2.SG.TermDef.DCRel Λ F F₁ F₂ → ∀ l : ℕ, leadMinorE (ZhatL F F₂) l = leadMinorE (ZhatL F F₁) l := by
  intro D Λ T T' F F₁ F₂ h l
  obtain ⟨A, B, hA0, hA1, hB0, hB1, hZ⟩ := Formalism.L2.SG.Pf.zhat_rel F h
  rw [hZ]
  exact Formalism.L2.SG.Pf.leadMinor_uni A _ B hA0 hA1 hB0 hB1 l

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadMinorGramMatrixConstDoubleCosetStatement
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leadMinor_gramMatrix_const_doubleCoset : ∀ (D : D7) (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V) (T T' : D.host.E) (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS T'), Formalism.L2.SG.TermDef.DCRel Λ F F₁ F₂ → ∀ l : ℕ, leadMinorE (ZhatL F F₂) l = leadMinorE (ZhatL F F₁) l := by
  first | exact @GlobalTheory.leadMinorE_zhatL_dcrel | exact GlobalTheory.leadMinorE_zhatL_dcrel | (intros; apply GlobalTheory.leadMinorE_zhatL_dcrel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserCovolumeRelevantTermLeHeightPow
noncomputable section

namespace GlobalTheory.LoopVol

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem hhz_dcrel {D : D7} (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V) {T T' : D.host.E}
    (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS T') (h : Formalism.L2.SG.TermDef.DCRel Λ F F₁ F₂) (b C : ℝ) :
    Formalism.MainNotions.S.Cnt.HHZ D b C (ZhatL F F₂) = Formalism.MainNotions.S.Cnt.HHZ D b C (ZhatL F F₁) := by

  have hm : ∀ l : ℕ, leadMinorE (ZhatL F F₂) l = leadMinorE (ZhatL F F₁) l :=
    GlobalTheory.T.leadMinor_gramMatrix_const_doubleCoset D Λ T T' F F₁ F₂ h
  simp only [Formalism.MainNotions.S.Cnt.HHZ, Formalism.MainNotions.S.Cnt.sizeZ, Formalism.MainNotions.S.Cnt.absDl, hm]

theorem volRC_le : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C : ℝ, ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (W : WittDat X) (H : TieHyp W hI) (Am : AmpDat X) (hV : PvalForm W hI Am) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t → Formalism.L2.SG.LoopTerm.volRC hI t ≤ Formalism.MainNotions.S.Cnt.HHZ D large₂.sc.b C (ZhatL ((termTieOf W hI H Am hV).fl t) ((termTieOf W hI H Am hV).fl' t)) ^ (C * (D.R.rS : ℝ) ^ 2) := by
  intro Cg cb Cu cT CT C0 A
  obtain ⟨C, hC1, hcov⟩ := GlobalTheory.T.covolume_integralUnipotentStabilizer_of_term Cg cb Cu cT CT C0 A
  refine ⟨C, ?_⟩
  intro D X Y hF hI W H Am hV large₂ u u' C' Cl hCl hHyp t hG hrel

  have hexp : (0 : ℝ) ≤ C * (D.R.rS : ℝ) ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
  have hone : ∀ Z : Formalism.MainNotions.S.Cnt.GramM D,
      (1 : ℝ) ≤ Formalism.MainNotions.S.Cnt.HHZ D large₂.sc.b C Z ^ (C * (D.R.rS : ℝ) ^ 2) := fun Z =>
    Real.one_le_rpow (Formalism.MainNotions.BridgeLemma₂.rows_one_le_HHZ D large₂ (by linarith) Z) hexp
  show Formalism.L2.SG.LoopTerm.volRC hI t ≤ Formalism.MainNotions.S.Cnt.HHZ D large₂.sc.b C
    (ZhatL (lf D (FlagOfWord W u)) (fl'Of W hI t)) ^ (C * (D.R.rS : ℝ) ^ 2)
  unfold Formalism.L2.SG.LoopTerm.volRC
  split_ifs with h
  swap
  · exact hone _
  have hs : h.2.2.choose.toTerm = tc hI t := h.2.2.choose_spec
  generalize h.2.2.choose = s at hs ⊢
  unfold Formalism.L2.SG.LoopTerm.covR
  split_ifs with hp
  swap
  · exact hone _
  have hat : s.toTerm.atPt hp.choose.1 := hp.choose_spec.1
  have hpin : Formalism.L2.SG.VolPin.IsPinnedR s hp.choose.1 hp.choose.2.1 := hp.choose_spec.2.1
  have hfund : Formalism.L2.SG.LoopTerm.IsFundR s hp.choose.2.2 := hp.choose_spec.2.2
  generalize hp.choose = x at hat hpin hfund ⊢
  obtain ⟨w, μR, K⟩ := x
  dsimp only at hat hpin hfund ⊢

  have htrel : (tc hI t).relevant := (hI.relevant t).1 hrel
  have hsrel : s.relevant := by
    show s.toTerm.relevant
    rw [hs]; exact htrel
  have hsG : s.G ≠ 0 := by
    show s.toTerm.G ≠ 0
    rw [hs, ← gterm_val hI t]
    exact (map_ne_zero _).2 hG

  have hP0 : Formalism.L2.SG.TermDef.PD D s.lam (lf D (X.Fu u)) u' s.frame := s.rep.2.2.2.2
  have hcls : s.toTerm.cls = Formalism.L2.SG.TermDef.mk _ _ _ ⟨s.frame, hP0⟩ := rfl
  have hEq := Formalism.L2.SG.TermTieOf.eqIff_base (Y := Y) (u' := u') s.lam s.mem
  obtain ⟨F₁, ⟨hP₁, hmk₁⟩, hG₁, hc₁⟩ := id hat
  have hR₁ : Formalism.L2.SG.TermDef.Rel s.lam (lf D (X.Fu u)) (Formalism.L2.SG.TermDef.PD D s.lam (lf D (X.Fu u)) u')
      ⟨F₁, hP₁⟩ ⟨s.frame, hP0⟩ := (hEq _ _).1 (hmk₁.trans hcls)
  have hcb := (Formalism.L2.SG.TermTieOf.cellQ s.toTerm w ⟨F₁, hP₁⟩ ⟨s.frame, hP0⟩ hR₁).1 ⟨hG₁, hc₁⟩

  have hlf := Formalism.L2.SG.TermTieOf.mapL_lf W u
  have hZ : ZhatL (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) =
      ZhatL (lf D (X.Fu u)) s.frame := by
    rw [← hlf]; exact Formalism.L2.SG.Saturated.zhat_mapL _ _ _ _
  have hGv : Gval (lf D (FlagOfWord W u)) (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) ≠ 0 := by
    rw [← hlf]
    exact (Formalism.L2.SG.Saturated.gval_mapL (W.δ u) (W.isom u) (lf D (X.Fu u)) s.frame).trans_ne hcb.1
  have hcell : IsInCell (ZhatOM (ZhatL (lf D (FlagOfWord W u))
      (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame))) w := by
    rw [hZ]; exact hcb.2
  obtain ⟨L, U, hL, hU, hLU⟩ := hcell
  have hPm : Formalism.L2.SG.TermDef.PD D (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u)) u'
      (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) := by
    rw [← hlf]
    exact (Formalism.L2.SG.Pf.positive_definite_isomorphism D u' (W.δ u) (W.isom u) s.lam (lf D (X.Fu u)) s.frame).2 hP0

  obtain ⟨Ω, hΩ, hvol, hcv⟩ := hcov D large₂ u u' C' Cl hCl hHyp (FlagOfWord W u) (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam)
    ⟨F0rec_e W u, F0rec_z_eq_zmOf W u⟩ (rowLat_rec H.lat s.lam s.mem)
    (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) ⟨⟨hPm.1, hPm.2.1, hGv⟩, hPm.2.2⟩ w L U hL hU hLU
  have hμ := GlobalTheory.T.stabiliserCovolume_le_rootCoordinateCover Cg cb Cu cT CT C0 A D X Y W large₂ u u' C' Cl hHyp s hsrel hsG w μR K hat hpin hfund
    L U hL hU hLU Ω hΩ hcv
  have hle := hμ.trans hvol

  have hout : Formalism.L2.SG.TermDef.DCRel s.lam (lf D (X.Fu u)) (Quot.out s.toTerm.cls).1 s.frame :=
    (hEq (Quot.out s.toTerm.cls) ⟨s.frame, hP0⟩).1 ((Quot.out_eq _).trans hcls)
  have hdc : Formalism.L2.SG.TermDef.DCRel (Formalism.HermitianLatticesTheory.gmap (W.δ u) s.lam) (lf D (FlagOfWord W u))
      (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) (Quot.out s.toTerm.cls).1)
      (Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) s.frame) := by
    rw [← hlf]
    exact (Formalism.L2.SG.Pf.double_coset_isomorphism _ _ (W.δ u) (W.isom u) s.lam (lf D (X.Fu u)) _ _).2 hout
  have hfl : fl'Of W hI t = Formalism.L2.SG.Saturated.mapL (W.δ u) (W.isom u) (Quot.out s.toTerm.cls).1 := by
    rw [hs]; rfl
  rw [hfl, ← hhz_dcrel _ _ _ _ hdc large₂.sc.b C]
  exact ENNReal.toReal_le_of_le_ofReal (le_trans zero_le_one (hone _)) hle

end GlobalTheory.LoopVol

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabiliserCovolumeRelevantTermLeHeightPowStatement
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf Formalism.L2.SG.LoopTieOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabiliserCovolume_relevantTerm_le_heightPow : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C : ℝ, ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (hF : FinX Y) (hI : SIso D.s (sOf hF)) (W : WittDat X) (H : TieHyp W hI) (Am : AmpDat X) (hV : PvalForm W hI Am) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Formalism.MainNotions.S.Cnt.Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t → Formalism.L2.SG.LoopTerm.volRC hI t ≤ Formalism.MainNotions.S.Cnt.HHZ D large₂.sc.b C (ZhatL ((termTieOf W hI H Am hV).fl t) ((termTieOf W hI H Am hV).fl' t)) ^ (C * (D.R.rS : ℝ) ^ 2) := by
  first | exact @GlobalTheory.LoopVol.volRC_le | exact GlobalTheory.LoopVol.volRC_le | (intros; apply GlobalTheory.LoopVol.volRC_le <;> assumption)
end
