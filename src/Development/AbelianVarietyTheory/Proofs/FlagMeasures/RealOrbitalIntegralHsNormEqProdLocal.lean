module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealUnipotentIntegralDiscreteSeriesVanish
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacExGoodOfN
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentRadicalInterConjugateClosedUnimodular

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlaceFlagUnipotentRadicalIsUnipotent
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlaceFlagUnipotentRadicalIsUnipotent
open Matrix

noncomputable section

namespace GlobalTheory.UnipRadNilp

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {n r : ℕ}

theorem hJ_sub_right (ε : Fin n → Bool) (x y w : Fin n → ℂ) : hJ ε x (y - w) = hJ ε x y - hJ ε x w := by
  unfold hJ; rw [mulVec_sub, dotProduct_sub]

theorem hJ_sub_left (ε : Fin n → Bool) (x y w : Fin n → ℂ) : hJ ε (x - y) w = hJ ε x w - hJ ε y w := by
  unfold hJ; rw [star_sub, sub_dotProduct]

theorem hJ_add_left (ε : Fin n → Bool) (x y w : Fin n → ℂ) : hJ ε (x + y) w = hJ ε x w + hJ ε y w := by
  unfold hJ; rw [star_add, add_dotProduct]

theorem hJ_smul_left (ε : Fin n → Bool) (c : ℂ) (x w : Fin n → ℂ) : hJ ε (c • x) w = star c * hJ ε x w := by
  unfold hJ; rw [star_smul, smul_dotProduct, smul_eq_mul]

theorem hJ_zero_left' (ε : Fin n → Bool) (w : Fin n → ℂ) : hJ ε 0 w = 0 := by
  unfold hJ; simp

theorem orth_span (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (b : ℕ) (w : Fin n → ℂ)
    (hw : ∀ c : Fin r, c.1 < b → hJ ε (e c) w = 0) : ∀ v ∈ spanLt e b, hJ ε v w = 0 := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    exact hw c hc
  | zero => exact hJ_zero_left' ε w
  | add x y _ _ hx hy => rw [hJ_add_left, hx, hy, add_zero]
  | smul c x _ hx => rw [hJ_smul_left, hx, mul_zero]

theorem spanLt_zero (e : Fin r → Fin n → ℂ) : spanLt e 0 = ⊥ := by
  unfold spanLt
  have : (e '' {b : Fin r | b.1 < 0}) = ∅ := by
    ext x; simp
  rw [this, Submodule.span_empty]

theorem pow_lower (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) {G : Matrix (Fin n) (Fin n) ℂ}
    (hG : InS e z G) (k : ℕ) : ∀ m, ∀ v ∈ spanLt e (m + k), (G - 1) ^ k *ᵥ v ∈ spanLt e m := by
  induction k with
  | zero => intro m v hv; simpa using hv
  | succ k ih =>
    intro m v hv
    have h1 : (G - 1) *ᵥ v ∈ spanLt e (m + k) := by
      have hle : spanLt e (m + (k + 1)) ≤ (spanLt e (m + k)).comap (Matrix.mulVecLin (G - 1)) := by
        unfold spanLt
        rw [Submodule.span_le]
        rintro _ ⟨b, hb, rfl⟩
        have hb' : (b : ℕ) < m + (k + 1) := hb
        simp only [SetLike.mem_coe, Submodule.mem_comap, Matrix.mulVecLin_apply]
        refine Submodule.span_mono ?_ (hG.1 b)
        rintro _ ⟨c, hc, rfl⟩
        have hc' : (c : ℕ) < b := hc
        exact ⟨c, show (c : ℕ) < m + k by omega, rfl⟩
      exact hle hv
    rw [pow_succ, ← mulVec_mulVec]
    exact ih m _ h1

theorem nilp (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Formalism.REAL.UJ ε)
    (hg : g ∈ NLoc ε e z) : (Formalism.MainNotions.S.uMat g - 1) ^ (2 * r + 1) = 0 := by
  set G := Formalism.MainNotions.S.uMat g with hGdef
  have hN : InN ε e z G := hg
  have hS' : InS e z (Formalism.MainNotions.S.uMat g⁻¹) :=
    (Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.RI.SG ε e z).inv_mem hg.1
  have hGG' : G * Formalism.MainNotions.S.uMat g⁻¹ = 1 := Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.uMat_mul_inv ε g
  have hiso := Formalism.L2.SG.RealObj.InfCut.UnitaryIsometries.isIsom_uMat ε g

  have adj : ∀ b : Fin r, ∀ w, hJ ε (e b) ((G - 1) *ᵥ w) = hJ ε ((Formalism.MainNotions.S.uMat g⁻¹ - 1) *ᵥ e b) w := by
    intro b w
    have h1 : hJ ε (e b) (G *ᵥ w) = hJ ε (Formalism.MainNotions.S.uMat g⁻¹ *ᵥ e b) w := by
      have := hiso (Formalism.MainNotions.S.uMat g⁻¹ *ᵥ e b) w
      rw [mulVec_mulVec, hGG', one_mulVec] at this
      exact this
    rw [sub_mulVec, one_mulVec, hJ_sub_right, h1, sub_mulVec, one_mulVec, hJ_sub_left]

  have step1 : ∀ k, ∀ x, ∀ b : Fin r, b.1 < k → hJ ε (e b) ((G - 1) ^ k *ᵥ x) = 0 := by
    intro k
    induction k with
    | zero => intro x b hb; omega
    | succ k ih =>
      intro x b hb
      rw [pow_succ', ← mulVec_mulVec, adj]
      refine orth_span ε e b.1 _ (fun c hc => ih x c (by omega)) _ (hS'.1 b)
  have step2 : ∀ x, (G - 1) ^ (r + 1) *ᵥ x ∈ spanLt e r := by
    intro x
    rw [pow_succ', ← mulVec_mulVec]
    exact hN.2 _ (fun a => step1 r x a a.2)
  have step3 : ∀ x, (G - 1) ^ (2 * r + 1) *ᵥ x = 0 := by
    intro x
    have : (G - 1) ^ (2 * r + 1) = (G - 1) ^ r * (G - 1) ^ (r + 1) := by
      rw [← pow_add]; ring_nf
    rw [this, ← mulVec_mulVec]
    have hm := pow_lower e z hN.1 r 0 _ (by rw [zero_add]; exact step2 x)
    rw [spanLt_zero] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  ext i j
  have := congrFun (step3 (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

end GlobalTheory.UnipRadNilp

theorem GlobalTheory.unipRad_pow_eq_zero : ∀ {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Formalism.REAL.UJ ε), g ∈ Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc ε e z → (Formalism.MainNotions.S.uMat g - 1) ^ (2 * r + 1) = 0 :=
  fun ε e z g hg => GlobalTheory.UnipRadNilp.nilp ε e z g hg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlaceFlagUnipotentRadicalIsUnipotentStatement
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceFlagUnipotentRadical_isUnipotent : ∀ {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Formalism.REAL.UJ ε), g ∈ Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc ε e z → (Formalism.MainNotions.S.uMat g - 1) ^ (2 * r + 1) = 0 := by
  first | exact @GlobalTheory.unipRad_pow_eq_zero | exact GlobalTheory.unipRad_pow_eq_zero | (intros; apply GlobalTheory.unipRad_pow_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentSubgroupUJHaarRightInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryJHaarEntryBoundedPolynomialGrowth
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryJHaarEntryBoundedPolynomialGrowth
noncomputable section

open MeasureTheory Metric
open scoped Matrix

namespace GlobalTheory.UJGrowth

variable {n : ℕ} {ε : Fin n → Bool}

def ent (g : Formalism.REAL.UJ ε) : Fin n → Fin n → ℂ := Matrix.of.symm (Formalism.MainNotions.S.uMat g)

theorem ent_closedEmb : Topology.IsClosedEmbedding (ent (ε := ε)) :=
  (Formalism.REAL.isClosedEmbeddingMatrix n ε).1

theorem mem_closedBall_iff_entries {x y : Fin n → Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R) :
    x ∈ closedBall y R ↔ ∀ i j, ‖x i j - y i j‖ ≤ R := by
  rw [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg hR]
  exact forall_congr' fun i => pi_norm_le_iff_of_nonneg hR

theorem mem_closedBall_zero_iff_entries {x : Fin n → Fin n → ℂ} {R : ℝ} (hR : 0 ≤ R) :
    x ∈ closedBall 0 R ↔ ∀ i j, ‖x i j‖ ≤ R := by
  rw [mem_closedBall_iff_entries hR]
  simp

theorem uMat_inv_mul' (g : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.uMat g⁻¹ * Formalism.MainNotions.S.uMat g = 1 := by
  rw [← show Formalism.MainNotions.S.uMat (g⁻¹ * g) = Formalism.MainNotions.S.uMat g⁻¹ * Formalism.MainNotions.S.uMat g from rfl, inv_mul_cancel]
  rfl

theorem uMat_mul_inv' (g : Formalism.REAL.UJ ε) : Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat g⁻¹ = 1 := by
  rw [← show Formalism.MainNotions.S.uMat (g * g⁻¹) = Formalism.MainNotions.S.uMat g * Formalism.MainNotions.S.uMat g⁻¹ from rfl, mul_inv_cancel]
  rfl

theorem uMat_inv_eq (g : Formalism.REAL.UJ ε) :
    Formalism.MainNotions.S.uMat g⁻¹ = Formalism.REAL.Jm ε * (Formalism.MainNotions.S.uMat g)ᴴ * Formalism.REAL.Jm ε := by
  have hf : (Formalism.MainNotions.S.uMat g)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat g = Formalism.REAL.Jm ε := g.2
  have h1 : (Formalism.REAL.Jm ε * (Formalism.MainNotions.S.uMat g)ᴴ * Formalism.REAL.Jm ε) * Formalism.MainNotions.S.uMat g = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (Formalism.MainNotions.S.uMat g)ᴴ, hf,
      Formalism.REAL.Jm_mul_self]
  calc Formalism.MainNotions.S.uMat g⁻¹
      = ((Formalism.REAL.Jm ε * (Formalism.MainNotions.S.uMat g)ᴴ * Formalism.REAL.Jm ε) * Formalism.MainNotions.S.uMat g) * Formalism.MainNotions.S.uMat g⁻¹ := by
        rw [h1, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, uMat_mul_inv', Matrix.mul_one]

theorem norm_inv_entry (g : Formalism.REAL.UJ ε) (i j : Fin n) :
    ‖Formalism.MainNotions.S.uMat g⁻¹ i j‖ = ‖Formalism.MainNotions.S.uMat g j i‖ := by
  rw [uMat_inv_eq]
  unfold Formalism.REAL.Jm
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  split_ifs <;> simp

theorem small_ball {S : Subgroup (Formalism.REAL.UJ ε)} {μ : Measure (Formalism.REAL.UJ ε)}
    (hμ : Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (h : (n : ℝ) * (R * (2 * δ)) ≤ 1) (x : Fin n → Fin n → ℂ) :
    μ (ent ⁻¹' (closedBall 0 R ∩ closedBall x δ)) ≤
      μ (ent ⁻¹' closedBall (ent (1 : Formalism.REAL.UJ ε)) 1) := by
  by_cases hex : ∃ s ∈ ent ⁻¹' (closedBall 0 R ∩ closedBall x δ), s ∈ S
  · obtain ⟨s, ⟨hs1, hs2⟩, hs⟩ := hex
    have hme : MeasurableEmbedding (fun t : Formalism.REAL.UJ ε => s * t) :=
      (Homeomorph.mulLeft s).isClosedEmbedding.measurableEmbedding
    conv_lhs => rw [← hμ.2.2.2 s hs]
    rw [hme.map_apply]
    refine measure_mono fun t ht => ?_
    have ht2 : ent (s * t) ∈ closedBall x δ := ht.2
    have h1 : ent (s * t) ∈ closedBall (ent s) (2 * δ) := by
      have := dist_triangle_right (ent (s * t)) (ent s) x
      rw [mem_closedBall]
      linarith [mem_closedBall.1 ht2, mem_closedBall.1 hs2]
    rw [Set.mem_preimage, mem_closedBall_iff_entries zero_le_one]
    intro i j
    have e : Formalism.MainNotions.S.uMat t = Formalism.MainNotions.S.uMat s⁻¹ * Formalism.MainNotions.S.uMat (s * t) := by
      rw [show Formalism.MainNotions.S.uMat (s * t) = Formalism.MainNotions.S.uMat s * Formalism.MainNotions.S.uMat t from rfl, ← Matrix.mul_assoc,
        uMat_inv_mul', Matrix.one_mul]
    have e2 : Formalism.MainNotions.S.uMat t - 1 =
        Formalism.MainNotions.S.uMat s⁻¹ * (Formalism.MainNotions.S.uMat (s * t) - Formalism.MainNotions.S.uMat s) := by
      rw [Matrix.mul_sub, ← e, uMat_inv_mul']
    have e3 : ent t i j - ent (1 : Formalism.REAL.UJ ε) i j = (Formalism.MainNotions.S.uMat t - 1) i j := rfl
    rw [e3, e2, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ l ∈ (Finset.univ : Finset (Fin n)),
        ‖Formalism.MainNotions.S.uMat s⁻¹ i l * (Formalism.MainNotions.S.uMat (s * t) - Formalism.MainNotions.S.uMat s) l j‖ ≤ R * (2 * δ) :=
      fun l _ => by
        rw [norm_mul]
        refine mul_le_mul ?_ ?_ (norm_nonneg _) hR
        · rw [norm_inv_entry]
          exact (mem_closedBall_zero_iff_entries hR).1 hs1 l i
        · exact (mem_closedBall_iff_entries (by linarith)).1 h1 l j
    refine (Finset.sum_le_card_nsmul _ _ _ hb).trans ?_
    simpa using h
  · rw [measure_mono_null (t := (S : Set (Formalism.REAL.UJ ε))ᶜ) (fun s hs hS => hex ⟨s, hs, hS⟩) hμ.2.2.1]
    exact zero_le

end GlobalTheory.UJGrowth

namespace GlobalTheory.UJGrowth

theorem growth : ∀ {n : ℕ} (ε : Fin n → Bool) (S : Subgroup (Formalism.REAL.UJ ε)),
    IsClosed (S : Set (Formalism.REAL.UJ ε)) → ∀ μ : Measure (Formalism.REAL.UJ ε),
    Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ → IsFiniteMeasureOnCompacts μ →
    ∃ (C : ℝ) (D : ℕ), ∀ R : ℝ, 1 ≤ R →
      μ {g : Formalism.REAL.UJ ε | ∀ i j, ‖Formalism.MainNotions.S.uMat g i j‖ ≤ R} ≤ ENNReal.ofReal (C * R ^ D) := by
  intro n ε S _ μ hμ hfin
  haveI := hμ.1
  have hemb : Topology.IsClosedEmbedding (ent (ε := ε)) := ent_closedEmb
  let ν : Measure (Fin n → Fin n → ℂ) := μ.map ent
  have hνA : ∀ A, MeasurableSet A → ν A = μ (ent ⁻¹' A) := fun A hA =>
    Measure.map_apply hemb.continuous.measurable hA
  have hcpt : ∀ y r, μ (ent ⁻¹' closedBall y r) < ⊤ := fun y r =>
    (hemb.isCompact_preimage (isCompact_closedBall y r)).measure_lt_top
  haveI : SigmaFinite ν := hemb.measurableEmbedding.sigmaFinite_map
  set M := μ (ent ⁻¹' closedBall (ent (1 : Formalism.REAL.UJ ε)) 1) with hM
  have hMf : M ≠ ⊤ := (hcpt _ _).ne
  set N : ℝ := (n : ℝ) + 1 with hN
  have hN1 : 1 ≤ N := by rw [hN]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  set d := Module.finrank ℝ (Fin n → Fin n → ℂ)
  let lam : Measure (Fin n → Fin n → ℂ) := Measure.addHaar
  refine ⟨M.toReal * (4 * N) ^ d, 2 * d, fun R hR => ?_⟩
  set δ := (2 * N * R)⁻¹ with hδ
  have hp : 1 ≤ 2 * N * R := by nlinarith
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := inv_le_one_of_one_le₀ hp
  have hcond : (n : ℝ) * (R * (2 * δ)) ≤ 1 := by
    have e : (n : ℝ) * (R * (2 * δ)) = n / N := by
      rw [hδ]; field_simp
    rw [e, div_le_one (by linarith)]
    linarith
  have hsb : ∀ x, ν (closedBall 0 R ∩ closedBall x δ) ≤ M := fun x => by
    rw [hνA _ (measurableSet_closedBall.inter measurableSet_closedBall)]
    exact small_ball hμ (by linarith) hδ0.le hcond x
  have hset : {g : Formalism.REAL.UJ ε | ∀ i j, ‖Formalism.MainNotions.S.uMat g i j‖ ≤ R} = ent ⁻¹' closedBall 0 R := by
    ext g
    rw [Set.mem_preimage, mem_closedBall_zero_iff_entries (by linarith)]
    rfl
  rw [hset, ← hνA _ measurableSet_closedBall]
  let W : Set ((Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)) := {p | p.1 ∈ closedBall 0 R ∧ dist p.1 p.2 ≤ δ}
  have hW : MeasurableSet W :=
    ((isClosed_closedBall.preimage continuous_fst).inter
      (isClosed_le continuous_dist continuous_const)).measurableSet
  have e1 : (ν.prod lam) W = lam (closedBall 0 δ) * ν (closedBall 0 R) := by
    rw [Measure.prod_apply hW, ← lintegral_indicator_const measurableSet_closedBall]
    refine lintegral_congr fun s => ?_
    by_cases hs : s ∈ closedBall (0 : Fin n → Fin n → ℂ) R
    · rw [Set.indicator_of_mem hs, ← Measure.addHaar_closedBall_center lam s]
      congr 1
      ext x
      exact ⟨fun h => mem_closedBall'.2 h.2, fun h => ⟨hs, mem_closedBall'.1 h⟩⟩
    · rw [Set.indicator_of_notMem hs]
      have : Prod.mk s ⁻¹' W = ∅ := by
        ext x
        simp only [W, Set.mem_preimage, Set.mem_setOf_eq, hs, false_and, Set.mem_empty_iff_false]
      rw [this, measure_empty]
  have e2 : (ν.prod lam) W ≤ M * lam (closedBall 0 (2 * R)) := by
    rw [Measure.prod_apply_symm hW, ← lintegral_indicator_const measurableSet_closedBall]
    refine lintegral_mono fun x => ?_
    by_cases hx : x ∈ closedBall (0 : Fin n → Fin n → ℂ) (2 * R)
    · rw [Set.indicator_of_mem hx]
      exact hsb x
    · have : (fun s => (s, x)) ⁻¹' W = ∅ := by
        ext s
        simp only [W, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, mem_closedBall]
        rintro ⟨h1, h2⟩
        apply hx
        have := dist_triangle_left x 0 s
        rw [mem_closedBall]; linarith
      simp [this]
  rw [e1, Measure.addHaar_closedBall lam _ hδ0.le, Measure.addHaar_closedBall lam _ (by linarith)] at e2
  have hb0 : 0 < (lam (ball 0 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos lam _ one_pos).ne' measure_ball_lt_top.ne
  have e3 := ENNReal.toReal_mono (ENNReal.mul_ne_top hMf
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)) e2
  simp only [ENNReal.toReal_mul] at e3
  rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at e3
  have e4 : δ ^ d * (ν (closedBall 0 R)).toReal ≤ M.toReal * (2 * R) ^ d := by
    refine le_of_mul_le_mul_right ?_ hb0
    calc _ = δ ^ d * (lam (ball 0 1)).toReal * (ν (closedBall 0 R)).toReal := by ring
      _ ≤ _ := e3
      _ = _ := by ring
  have e5 : M.toReal * (2 * R) ^ d = δ ^ d * (M.toReal * (4 * N) ^ d * R ^ (2 * d)) := by
    have : 2 * R = δ * (4 * N) * R ^ 2 := by rw [hδ]; field_simp; ring
    rw [this, mul_pow, mul_pow, pow_mul]; ring
  rw [e5] at e4
  have e6 := le_of_mul_le_mul_left e4 (by positivity)
  have hνf : ν (closedBall 0 R) ≠ ⊤ := by
    rw [hνA _ measurableSet_closedBall]; exact (hcpt _ _).ne
  rw [← ENNReal.ofReal_toReal hνf]
  exact ENNReal.ofReal_le_ofReal e6

end GlobalTheory.UJGrowth
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryJHaarEntryBoundedPolynomialGrowthStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryJ_haar_entryBounded_polynomial_growth : ∀ {n : ℕ} (ε : Fin n → Bool) (S : Subgroup (Formalism.REAL.UJ ε)), IsClosed (S : Set (Formalism.REAL.UJ ε)) → ∀ μ : Measure (Formalism.REAL.UJ ε), Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ → IsFiniteMeasureOnCompacts μ → ∃ (C : ℝ) (D : ℕ), ∀ R : ℝ, 1 ≤ R → μ {g : Formalism.REAL.UJ ε | ∀ i j, ‖Formalism.MainNotions.S.uMat g i j‖ ≤ R} ≤ ENNReal.ofReal (C * R ^ D) := by
  first | exact @GlobalTheory.UJGrowth.growth | exact GlobalTheory.UJGrowth.growth | (intros; apply GlobalTheory.UJGrowth.growth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentSubgroupUJHaarRightInvariant
open MeasureTheory

noncomputable section

open scoped ENNReal NNReal

namespace GlobalTheory.UJUnimod

variable {n : ℕ}

def Bd (a : Matrix (Fin n) (Fin n) ℂ) (R : ℝ) : Prop := ∀ i j, ‖a i j‖ ≤ R

theorem Bd.mul {a b : Matrix (Fin n) (Fin n) ℂ} {R R' : ℝ} (ha : Bd a R) (hb : Bd b R') :
    Bd (a * b) ((n : ℝ) * (R * R')) := by
  intro i j
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ l ∈ (Finset.univ : Finset (Fin n)), ‖a i l * b l j‖ ≤ R * R' := fun l _ => by
    rw [norm_mul]
    exact mul_le_mul (ha i l) (hb l j) (norm_nonneg _) ((norm_nonneg _).trans (ha i l))
  simpa using Finset.sum_le_card_nsmul _ _ _ this

theorem bd_pow {g : Matrix (Fin n) (Fin n) ℂ} {m : ℕ} (hg : (g - 1) ^ m = 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ j : ℕ, Bd (g ^ j) (B * ((j : ℝ) + 1) ^ (m + 1)) := by
  set X := g - 1 with hX
  have e : g = X + 1 := by simp [hX]
  refine ⟨∑ l ∈ Finset.range m, ∑ i, ∑ j, ‖(X ^ l) i j‖, by positivity, fun p i j => ?_⟩
  set B := ∑ l ∈ Finset.range m, ∑ i, ∑ j, ‖(X ^ l) i j‖ with hB
  have hB0 : 0 ≤ B := by positivity
  rw [e, (Commute.one_right X).add_pow, Matrix.sum_apply]
  refine (norm_sum_le _ _).trans ?_
  have : ∀ l ∈ Finset.range (p + 1), ‖(X ^ l * 1 ^ (p - l) * (p.choose l : Matrix (Fin n) (Fin n) ℂ)) i j‖ ≤
      B * ((p : ℝ) + 1) ^ m := fun l _ => by
    by_cases hl : l < m
    · have h1 : ‖(X ^ l) i j‖ ≤ B :=
        ((Finset.single_le_sum (f := fun j => ‖(X ^ l) i j‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)).trans
          (Finset.single_le_sum (f := fun i => ∑ j, ‖(X ^ l) i j‖) (fun _ _ => by positivity)
            (Finset.mem_univ i))).trans
          (Finset.single_le_sum (f := fun l => ∑ i, ∑ j, ‖(X ^ l) i j‖) (fun _ _ => by positivity)
            (Finset.mem_range.2 hl))
      have h2 : (p.choose l : ℝ) ≤ ((p : ℝ) + 1) ^ m := by
        have h3 : (p.choose l : ℝ) ≤ (p : ℝ) ^ l := by exact_mod_cast Nat.choose_le_pow p l
        have h4 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
        exact h3.trans ((pow_le_pow_left₀ h4 (by linarith) l).trans (pow_le_pow_right₀ (by linarith) hl.le))
      rw [one_pow, mul_one, ← nsmul_eq_mul', Matrix.smul_apply, nsmul_eq_mul, norm_mul, Complex.norm_natCast,
        mul_comm]
      exact mul_le_mul h1 h2 (Nat.cast_nonneg _) hB0
    · rw [pow_eq_zero_of_le (not_lt.1 hl) hg]
      simp only [zero_mul, Matrix.zero_apply, norm_zero]
      positivity
  refine (Finset.sum_le_card_nsmul _ _ _ this).trans (le_of_eq ?_)
  simp only [Finset.card_range, nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.UJUnimod

namespace GlobalTheory.UJUnimod

theorem unimodular_of_unipotent : ∀ {n : ℕ} (ε : Fin n → Bool) (m : ℕ) (S : Subgroup (Formalism.REAL.UJ ε)),
    IsClosed (S : Set (Formalism.REAL.UJ ε)) → (∀ g ∈ S, (Formalism.MainNotions.S.uMat g - 1) ^ m = 0) →
    ∀ μ : Measure (Formalism.REAL.UJ ε), Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ →
    ∀ s ∈ S, μ.map (fun x => x * s) = μ := by
  intro n ε m S hS hu μ hμ
  obtain ⟨hσ, h0, hc, hl⟩ := hμ
  have hce : Topology.IsClosedEmbedding S.subtype := hS.isClosedEmbedding_subtypeVal
  have hφ : MeasurableEmbedding S.subtype := hce.measurableEmbedding
  haveI : LocallyCompactSpace S := hce.locallyCompactSpace
  haveI : SecondCountableTopology S := hce.isEmbedding.secondCountableTopology
  have h2 : (μ.comap S.subtype).map S.subtype = μ := by
    rw [hφ.map_comap]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    have : Set.range S.subtype = (S : Set (Formalism.REAL.UJ ε)) := Subtype.range_coe
    rw [this]
    exact hc
  set ν : Measure S := μ.comap S.subtype with hν
  haveI : SigmaFinite ν := SigmaFinite.of_map _ hφ.measurable.aemeasurable (by rwa [h2])
  haveI : ν.IsMulLeftInvariant := ⟨fun g => by
    apply hφ.map_injective
    have hm : Measurable fun x : Formalism.REAL.UJ ε => (g : Formalism.REAL.UJ ε) * x := measurable_const_mul _
    rw [Measure.map_map hφ.measurable (measurable_const_mul g), h2]
    conv_rhs => rw [← hl g g.2, ← h2, Measure.map_map hm hφ.measurable]
    rfl⟩
  haveI : ν.IsHaarMeasure :=
    GlobalTheory.SnMass.ProdQuot.isHaarMeasure_of_sigmaFinite ν fun h => h0 (by rw [← h2, h, Measure.map_zero])
  have hfin : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => by
    rw [← h2, hφ.map_apply]
    exact (hce.isCompact_preimage hK).measure_lt_top⟩

  have hmod : ∀ s : S, μ.map (fun x => x * (s : Formalism.REAL.UJ ε)) =
      (Measure.modularCharacter s : ℝ≥0∞) • μ := by
    intro s
    have e1 : ν.map (· * s) = (Measure.modularCharacter s : ℝ≥0∞) • ν := by
      rw [show (Measure.modularCharacter s : ℝ≥0) = Measure.modularCharacterFun s from rfl,
        Measure.modularCharacterFun_eq_haarScalarFactor ν s]
      exact Measure.isMulLeftInvariant_eq_smul _ ν
    conv_lhs => rw [← h2]
    rw [Measure.map_map (measurable_mul_const _) hφ.measurable]
    have : (fun x : Formalism.REAL.UJ ε => x * (s : Formalism.REAL.UJ ε)) ∘ S.subtype = S.subtype ∘ (· * s) := by
      funext x; rfl
    rw [this, ← Measure.map_map hφ.measurable (measurable_mul_const _), e1, Measure.map_smul, h2]
    exact hφ.measurable.aemeasurable

  have key : ∀ s : S, Measure.modularCharacter s ≤ 1 := by
    intro s
    set Δ := Measure.modularCharacter s with hΔ
    obtain ⟨C, D, hgr⟩ := GlobalTheory.T.unitaryJ_haar_entryBounded_polynomial_growth ε S hS μ ⟨hσ, h0, hc, hl⟩ hfin
    obtain ⟨B, hB, hpow⟩ := bd_pow (hu _ (S.inv_mem s.2))
    let Bx : ℝ → Set (Formalism.REAL.UJ ε) := fun R => {g | ∀ i j, ‖Formalism.MainNotions.S.uMat g i j‖ ≤ R}
    obtain ⟨ρ, hρ⟩ : ∃ ρ : ℕ, μ (Bx ((ρ : ℝ) + 1)) ≠ 0 := by
      by_contra! h
      apply h0
      rw [← Measure.measure_univ_eq_zero]
      have : (Set.univ : Set (Formalism.REAL.UJ ε)) = ⋃ ρ : ℕ, Bx ((ρ : ℝ) + 1) := by
        ext g
        simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
        obtain ⟨N, hN⟩ := exists_nat_ge (∑ i, ∑ j, ‖Formalism.MainNotions.S.uMat g i j‖)
        refine ⟨N, fun i j => ?_⟩
        have := (Finset.single_le_sum (f := fun j => ‖Formalism.MainNotions.S.uMat g i j‖) (fun _ _ => norm_nonneg _)
          (Finset.mem_univ j)).trans (Finset.single_le_sum (f := fun i => ∑ j, ‖Formalism.MainNotions.S.uMat g i j‖)
          (fun _ _ => by positivity) (Finset.mem_univ i))
        linarith
      rw [this]
      exact measure_iUnion_null h
    set ρ' : ℝ := (ρ : ℝ) + 1 with hρ'
    have hρ1 : 1 ≤ ρ' := by rw [hρ']; linarith [Nat.cast_nonneg (α := ℝ) ρ]
    obtain ⟨C', hC', hgr'⟩ : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ R : ℝ, 1 ≤ R → (μ (Bx R)).toReal ≤ C' * R ^ D ∧ μ (Bx R) < ⊤ := by
      refine ⟨max C 0, le_max_right _ _, fun R hR => ?_⟩
      have h1 : μ (Bx R) ≤ ENNReal.ofReal (max C 0 * R ^ D) :=
        (hgr R hR).trans (ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_left _ _))
      refine ⟨?_, h1.trans_lt ENNReal.ofReal_lt_top⟩
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    have hv : 0 < (μ (Bx ρ')).toReal := ENNReal.toReal_pos hρ (hgr' ρ' hρ1).2.ne
    set K : ℝ := ((n : ℝ) + 1) * ρ' * (B + 1) with hK
    have hK1 : 1 ≤ K := by
      rw [hK]
      have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have h2 : (1 : ℝ) ≤ B + 1 := by linarith
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ _ := by gcongr
    have hU : ∀ (a : Formalism.REAL.UJ ε) (j : ℕ), Formalism.MainNotions.S.uMat (a ^ j) = Formalism.MainNotions.S.uMat a ^ j := fun a j =>
      map_pow ((Units.coeHom (Matrix (Fin n) (Fin n) ℂ)).comp (Formalism.REAL.UJ ε).subtype) a j
    have em : ∀ j : ℕ, μ.map (fun x => x * ((s : Formalism.REAL.UJ ε) ^ j)) = ((Δ : ℝ≥0∞) ^ j) • μ := by
      intro j
      have := hmod (s ^ j)
      rw [map_pow] at this
      simpa using this
    have key2 : ∀ j : ℕ, (Δ : ℝ) ^ j * (μ (Bx ρ')).toReal ≤ C' * K ^ D * ((j : ℝ) + 1) ^ ((m + 1) * D) := by
      intro j
      have ht : (1 : ℝ) ≤ ((j : ℝ) + 1) ^ (m + 1) := one_le_pow₀ (by linarith [Nat.cast_nonneg (α := ℝ) j])
      have hme : MeasurableEmbedding (fun x : Formalism.REAL.UJ ε => x * ((s : Formalism.REAL.UJ ε) ^ j)) :=
        (Homeomorph.mulRight ((s : Formalism.REAL.UJ ε) ^ j)).measurableEmbedding
      have h1 : (((Δ : ℝ≥0∞) ^ j) • μ) (Bx ρ') ≤ μ (Bx (K * ((j : ℝ) + 1) ^ (m + 1))) := by
        rw [← em, hme.map_apply]
        refine measure_mono fun x hx => ?_
        have hx' : x = (x * (s : Formalism.REAL.UJ ε) ^ j) * ((s : Formalism.REAL.UJ ε)⁻¹) ^ j := by
          rw [mul_assoc, inv_pow, mul_inv_cancel, mul_one]
        have h2 := (show Bd (Formalism.MainNotions.S.uMat (x * (s : Formalism.REAL.UJ ε) ^ j)) ρ' from hx).mul (hpow j)
        have h3 : Formalism.MainNotions.S.uMat x = Formalism.MainNotions.S.uMat (x * (s : Formalism.REAL.UJ ε) ^ j) *
            Formalism.MainNotions.S.uMat (((s : S)⁻¹ : S) : Formalism.REAL.UJ ε) ^ j := by
          rw [← hU]
          conv_lhs => rw [hx']
          rfl
        intro i k
        rw [h3]
        refine (h2 i k).trans ?_
        rw [hK]
        have hB' : B ≤ B + 1 := by linarith
        have hn' : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
        have h0ρ : 0 ≤ ρ' := by linarith
        calc (n : ℝ) * (ρ' * (B * ((j : ℝ) + 1) ^ (m + 1))) = (n : ℝ) * ρ' * B * ((j : ℝ) + 1) ^ (m + 1) := by ring
          _ ≤ ((n : ℝ) + 1) * ρ' * (B + 1) * ((j : ℝ) + 1) ^ (m + 1) := by gcongr
      have hR1 : 1 ≤ K * ((j : ℝ) + 1) ^ (m + 1) := by nlinarith
      have h2 := (ENNReal.toReal_mono (hgr' _ hR1).2.ne h1).trans (hgr' _ hR1).1
      rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_pow, mul_pow, ← pow_mul,
        ← mul_assoc] at h2
      simpa using h2
    by_contra! h1
    have h2 : 1 < (Δ : ℝ) := by exact_mod_cast h1
    have h3 := ((tendsto_pow_const_div_const_pow_of_one_lt ((m + 1) * D) h2).comp
      (Filter.tendsto_add_atTop_nat 1)).const_mul (C' * K ^ D * (Δ : ℝ))
    rw [mul_zero] at h3
    obtain ⟨j, hj⟩ := (h3.eventually (gt_mem_nhds hv)).exists
    have h4 := key2 j
    have h5 : 0 < (Δ : ℝ) ^ j := by positivity
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one] at hj
    have h6 : C' * K ^ D * (Δ : ℝ) * (((j : ℝ) + 1) ^ ((m + 1) * D) / (Δ : ℝ) ^ (j + 1)) =
        C' * K ^ D * ((j : ℝ) + 1) ^ ((m + 1) * D) / (Δ : ℝ) ^ j := by
      have : (Δ : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    rw [h6, div_lt_iff₀ h5] at hj
    linarith
  intro s hs
  have e1 := key ⟨s, hs⟩
  have e2 := key (⟨s, hs⟩ : S)⁻¹
  have e3 : Measure.modularCharacter (⟨s, hs⟩ : S) = 1 := by
    have := map_mul Measure.modularCharacter (⟨s, hs⟩ : S) (⟨s, hs⟩ : S)⁻¹
    rw [mul_inv_cancel, map_one] at this
    refine le_antisymm e1 ?_
    calc (1 : ℝ≥0) = _ := this
      _ ≤ Measure.modularCharacter (⟨s, hs⟩ : S) * 1 := mul_le_mul_of_nonneg_left e2 zero_le
      _ = _ := mul_one _
  have := hmod ⟨s, hs⟩
  rw [e3] at this
  simpa using this

end GlobalTheory.UJUnimod
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentSubgroupUJHaarRightInvariantStatement
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_subgroup_UJ_haar_right_invariant : ∀ {n : ℕ} (ε : Fin n → Bool) (m : ℕ) (S : Subgroup (Formalism.REAL.UJ ε)), IsClosed (S : Set (Formalism.REAL.UJ ε)) → (∀ g ∈ S, (Formalism.MainNotions.S.uMat g - 1) ^ m = 0) → ∀ μ : Measure (Formalism.REAL.UJ ε), Formalism.L2.SG.RealObj.IsHaarLoc (S : Set (Formalism.REAL.UJ ε)) μ → ∀ s ∈ S, μ.map (fun x => x * s) = μ := by
  first | exact @GlobalTheory.UJUnimod.unimodular_of_unipotent | exact GlobalTheory.UJUnimod.unimodular_of_unipotent | (intros; apply GlobalTheory.UJUnimod.unimodular_of_unipotent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealOrbitalIntegralHsNormEqProdLocal
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.OrbQuotProd

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

theorem norm_rankOneInnerOperator {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] (a : V) (b : V') : ‖Formalism.L2.SG.TermOp.rk1 a b‖ = ‖a‖ * ‖b‖ := by
  unfold Formalism.L2.SG.TermOp.rk1
  rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, mul_comm]

theorem continuous_rankOneOperator {Y V V' : Type*} [TopologicalSpace Y] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] {f : Y → V} {g : Y → V'} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun y => Formalism.L2.SG.TermOp.rk1 (f y) (g y) := by
  unfold Formalism.L2.SG.TermOp.rk1
  have h1 : Continuous fun y => innerSL ℂ (g y) := (innerSL ℂ).continuous.comp hg
  exact ((ContinuousLinearMap.smulRightL ℂ V' V).continuous.comp h1).clm_apply hf

def stG {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (γ : Formalism.REAL.UJ ε) :
    Subgroup (Formalism.REAL.UJ ε) where
  carrier := StSet (NLoc ε e z) (NLoc ε e z') γ
  one_mem' := ⟨(Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.NG ε e z).one_mem, by
    have h : γ⁻¹ * 1 * γ = 1 := by group
    show γ⁻¹ * 1 * γ ∈ Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.NG ε e z'
    rw [h]; exact (Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.NG ε e z').one_mem⟩
  mul_mem' {a b} ha hb := ⟨(Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.NG ε e z).mul_mem ha.1 hb.1, by
    have := (Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.NG ε e z').mul_mem ha.2 hb.2
    have h : γ⁻¹ * (a * b) * γ = γ⁻¹ * a * γ * (γ⁻¹ * b * γ) := by group
    show γ⁻¹ * (a * b) * γ ∈ Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.NG ε e z'
    rw [h]; exact this⟩
  inv_mem' {a} ha := ⟨(Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.NG ε e z).inv_mem ha.1, by
    have := (Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.NG ε e z').inv_mem ha.2
    have h : γ⁻¹ * a⁻¹ * γ = (γ⁻¹ * a * γ)⁻¹ := by group
    show γ⁻¹ * a⁻¹ * γ ∈ Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.NG ε e z'
    rw [h]; exact this⟩

theorem stG_closed {n r : ℕ} (ε : Fin n → Bool) (e : Fin r → Fin n → ℂ) (z z' : Fin n → ℂ) (γ : Formalism.REAL.UJ ε) :
    IsClosed (stG ε e z z' γ : Set (Formalism.REAL.UJ ε)) := by
  have h1 := Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.NG_closed ε e z
  have h2 := Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH.NG_closed ε e z'
  have hc : Continuous fun y : Formalism.REAL.UJ ε => γ⁻¹ * y * γ := by fun_prop
  exact h1.inter (h2.preimage hc)

end GlobalTheory.OrbQuotProd

namespace GlobalTheory.OrbQuotProd

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates
open scoped InnerProductSpace NNReal

theorem lint_eq {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul G] (μG μ ν : Measure G) {b : G → ℝ≥0}
    (hb : Measurable b) (h1 : ∀ g, ∫⁻ s, (b (s * g) : ℝ≥0∞) ∂μ = 1)
    (hν : ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ x, f x ∂μG = ∫⁻ x, ∫⁻ s, f (s * x) ∂μ ∂ν)
    {f : G → ℝ≥0∞} (hf : Measurable f) (hi : ∀ᵐ s ∂μ, ∀ x, f (s * x) = f x) :
    ∫⁻ x, f x ∂ν = ∫⁻ x, (b x : ℝ≥0∞) * f x ∂μG := by
  have hb' : Measurable fun x => (b x : ℝ≥0∞) := hb.coe_nnreal_ennreal
  have hm : Measurable fun x => (b x : ℝ≥0∞) * f x := hb'.mul hf
  rw [hν _ hm]
  refine lintegral_congr fun x => ?_
  have e : ∫⁻ s, (b (s * x) : ℝ≥0∞) * f (s * x) ∂μ = ∫⁻ s, (b (s * x) : ℝ≥0∞) * f x ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards [hi] with s hs
    rw [hs x]
  rw [e, lintegral_mul_const (f := fun s => (b (s * x) : ℝ≥0∞)) _ (hb'.comp (measurable_mul_const x)), h1, one_mul]

theorem quot_prod {ι : Type} [Fintype ι] {n : ℕ} (ε : ι → Fin n → Bool) (R : ∀ i, Subgroup (Formalism.REAL.UJ (ε i)))
    (μl νl : ∀ i, Measure (Formalism.REAL.UJ (ε i))) (ν : Measure (∀ i, Formalism.REAL.UJ (ε i)))
    (hR : ∀ i, IsClosed (R i : Set (Formalism.REAL.UJ (ε i))))
    (hH : ∀ i, IsHaarLoc (R i : Set (Formalism.REAL.UJ (ε i))) (μl i))
    (hr : ∀ i, ∀ s ∈ R i, (μl i).map (fun x => x * s) = μl i) (hQl : ∀ i, IsQuotLoc (μl i) (νl i))
    (hQ : ∀ f : (∀ i, Formalism.REAL.UJ (ε i)) → ℝ≥0∞, Measurable f →
      ∫⁻ x, f x ∂(Measure.pi fun i => Formalism.REAL.muG (ε i)) = ∫⁻ x, ∫⁻ s, f (s * x) ∂(Measure.pi μl) ∂ν) :
    (∀ F : ∀ i, Formalism.REAL.UJ (ε i) → ℝ≥0∞, (∀ i, Measurable (F i)) → (∀ i, ∀ s ∈ R i, ∀ x, F i (s * x) = F i x) →
      ∫⁻ x, ∏ i, F i (x i) ∂ν = ∏ i, ∫⁻ x, F i x ∂(νl i)) ∧
    (∀ F : ∀ i, Formalism.REAL.UJ (ε i) → ℂ, (∀ i, Measurable (F i)) → (∀ i, ∀ s ∈ R i, ∀ x, F i (s * x) = F i x) →
      ∫ x, ∏ i, F i (x i) ∂ν = ∏ i, ∫ x, F i x ∂(νl i)) := by
  have : ∀ i, SigmaFinite (μl i) := fun i => (hH i).1
  choose b hb h1 using fun i => GlobalTheory.SnMass.ProdQuot.exists_cutoff (R i) (μl i) (hR i) (hH i).2.1 (hH i).2.2.1
    (fun s hs => ⟨(hH i).2.2.2 s hs, hr i s hs⟩)
  have hbm : Measurable fun x : (∀ i, Formalism.REAL.UJ (ε i)) => ∏ i, b i (x i) :=
    Finset.measurable_prod _ fun i _ => (hb i).comp (measurable_pi_apply i)
  have hB : ∀ g : (∀ i, Formalism.REAL.UJ (ε i)), ∫⁻ s, ((fun x => ∏ i, b i (x i)) (s * g) : ℝ≥0∞) ∂(Measure.pi μl) = 1 :=
    fun g => by
      have := GlobalTheory.SnMass.Push.lintegral_fintype_prod (μ := μl) (fun i s => (b i (s * g i) : ℝ≥0∞))
        fun i => (hb i).coe_nnreal_ennreal.comp (measurable_mul_const (g i))
      simpa [h1] using this
  have hmem : ∀ i, ∀ᵐ s ∂(μl i), s ∈ (R i : Set (Formalism.REAL.UJ (ε i))) := fun i => (hH i).2.2.1
  refine ⟨fun F hF hFi => ?_, fun F hF hFi => ?_⟩
  · have hl := fun i => lint_eq (Formalism.REAL.muG (ε i)) (μl i) (νl i) (hb i) (h1 i) (hQl i) (hF i)
      (by filter_upwards [hmem i] with s hs using hFi i s hs)
    have hg := lint_eq (Measure.pi fun i => Formalism.REAL.muG (ε i)) (Measure.pi μl) ν hbm hB hQ
      (f := fun x => ∏ i, F i (x i)) (Finset.measurable_prod _ fun i _ => (hF i).comp (measurable_pi_apply i))
      (by
        have : ∀ᵐ s ∂(Measure.pi μl), ∀ i, s i ∈ (R i : Set (Formalism.REAL.UJ (ε i))) :=
          Filter.eventually_all.2 fun i => (Measure.tendsto_eval_ae_ae (μ := μl) (i := i)).eventually (hmem i)
        filter_upwards [this] with s hs x
        exact Finset.prod_congr rfl fun i _ => hFi i (s i) (hs i) (x i))
    rw [hg]
    have e : (fun x : (∀ i, Formalism.REAL.UJ (ε i)) => ((∏ i, b i (x i) : ℝ≥0) : ℝ≥0∞) * ∏ i, F i (x i)) =
        fun x => ∏ i, ((b i (x i) : ℝ≥0∞) * F i (x i)) := by
      ext x
      rw [Finset.prod_mul_distrib]
      push_cast
      rfl
    rw [e, GlobalTheory.SnMass.Push.lintegral_fintype_prod (fun i y => (b i y : ℝ≥0∞) * F i y)
      fun i => (hb i).coe_nnreal_ennreal.mul (hF i)]
    exact Finset.prod_congr rfl fun i _ => (hl i).symm
  · have hl := fun i => GlobalTheory.SnMass.ProdQuot.integral_eq (Formalism.REAL.muG (ε i)) (μl i) (νl i) (hb i) (h1 i) (hQl i)
      (hF i) (by filter_upwards [hmem i] with s hs using hFi i s hs)
    have hg := GlobalTheory.SnMass.ProdQuot.integral_eq (Measure.pi fun i => Formalism.REAL.muG (ε i)) (Measure.pi μl) ν hbm hB hQ
      (F := fun x => ∏ i, F i (x i)) (Finset.measurable_prod _ fun i _ => (hF i).comp (measurable_pi_apply i))
      (by
        have : ∀ᵐ s ∂(Measure.pi μl), ∀ i, s i ∈ (R i : Set (Formalism.REAL.UJ (ε i))) :=
          Filter.eventually_all.2 fun i => (Measure.tendsto_eval_ae_ae (μ := μl) (i := i)).eventually (hmem i)
        filter_upwards [this] with s hs x
        exact Finset.prod_congr rfl fun i _ => hFi i (s i) (hs i) (x i))
    have e : (fun x : (∀ i, Formalism.REAL.UJ (ε i)) => ((∏ i, b i (x i) : ℝ≥0) : ℂ) * ∏ i, F i (x i)) =
        fun x => ∏ i, ((b i (x i) : ℂ) * F i (x i)) := by
      ext x
      rw [Finset.prod_mul_distrib]
      push_cast
      rfl
    rw [hg.1, e, integral_fintype_prod_eq_prod fun i y => (b i y : ℂ) * F i y]
    exact Finset.prod_congr rfl fun i _ => (hl i).1.symm

end GlobalTheory.OrbQuotProd

namespace GlobalTheory.OrbQuotProd

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates
open scoped InnerProductSpace NNReal

theorem hsNormSq_eq_hs2 {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] (A : V' →L[ℂ] V) :
    Formalism.MainNotions.S.hsNormSq A = Formalism.L2.SG.RealObj.hs2 A := by
  unfold Formalism.MainNotions.S.hsNormSq Formalism.MainNotions.S.hsInner Formalism.L2.SG.RealObj.hs2
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_self_eq_norm_sq_to_K]
  norm_cast

theorem hsNormSq_zero {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] [FiniteDimensional ℂ V'] : Formalism.MainNotions.S.hsNormSq (0 : V' →L[ℂ] V) = 0 := by
  rw [hsNormSq_eq_hs2]
  unfold Formalism.L2.SG.RealObj.hs2
  simp

theorem hs_tens {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (A : X.Vpi u' →L[ℂ] X.Vpi u)
    (J : ∀ v, X.Vloc u' v →L[ℂ] X.Vloc u v) (hA : ∀ y, A (X.tensU u' y) = X.tensU u (fun v => J v (y v))) :
    Formalism.MainNotions.S.hsNormSq A = ∏ v, Formalism.MainNotions.S.hsNormSq (J v) := by
  obtain ⟨hon, hsp⟩ := Formalism.L2.SG.RealObj.EnergyCut.tens_onb X u'
  let B := OrthonormalBasis.mk hon hsp
  have hB : ∀ i, B i = X.tensU u' (fun v => stdOrthonormalBasis ℂ (X.Vloc u' v) (i v)) := fun i => by simp [B]
  rw [hsNormSq_eq_hs2]
  simp only [hsNormSq_eq_hs2]
  unfold hs2
  rw [Formalism.L2.SG.RealObj.InfCut.hsb_indep (stdOrthonormalBasis ℂ (X.Vpi u')) B]
  simp only [hB, hA, Formalism.L2.SG.RealObj.RankOneTensors.norm_tens (X.tensU u) (X.tensU_inner u), ← Finset.prod_pow]
  rw [Fintype.prod_sum]

end GlobalTheory.OrbQuotProd

namespace GlobalTheory.OrbQuotProd

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates
open scoped InnerProductSpace NNReal

theorem oo_quot : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (μl νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) (ν : Measure X.B.I.Ginf), (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (γ v)) (μl v)) → (∀ v, Formalism.L2.SG.RealObj.IsQuotLoc (μl v) (νl v)) → IsQuotMeasS X.B.I (Measure.pi μl) ν → (∀ v, ∀ s ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (γ v), ∀ x, Formalism.L2.SG.TermOp.rk1 (X.Wloc u v (s * x)) (X.Wloc u' v ((γ v)⁻¹ * (s * x))) = Formalism.L2.SG.TermOp.rk1 (X.Wloc u v x) (X.Wloc u' v ((γ v)⁻¹ * x))) → hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vpi u); Formalism.L2.SG.TermOp.OO ν Set.univ (X.Wu u) (X.Wu u') γ) = ∏ v, hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u' v) (γ v)) := by
  intro D X u u' γ μl νl ν hH hQl hQ hinv
  let R : ∀ v, Subgroup (Formalism.REAL.UJ (X.B.I.ε v)) := fun v =>
    stG (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u')) (γ v)
  have hRc : ∀ v, IsClosed (R v : Set (Formalism.REAL.UJ (X.B.I.ε v))) := fun v => stG_closed _ _ _ _ _
  have hr : ∀ v, ∀ s ∈ R v, (μl v).map (fun x => x * s) = μl v := fun v s hs =>
    GlobalTheory.T.unipotent_subgroup_UJ_haar_right_invariant (X.B.I.ε v) (2 * D.R.rS + 1) (R v) (hRc v) (fun g hg => GlobalTheory.T.realPlaceFlagUnipotentRadical_isUnipotent _ _ _ g hg.1) (μl v)
      (hH v) s hs
  have hq := quot_prod X.B.I.ε R μl νl ν hRc hH hr hQl hQ
  let ψ : ∀ v, Formalism.REAL.UJ (X.B.I.ε v) → (X.Vloc u' v →L[ℂ] X.Vloc u v) := fun v z =>
    Formalism.L2.SG.TermOp.rk1 (X.Wloc u v z) (X.Wloc u' v ((γ v)⁻¹ * z))
  let Φ : X.B.I.Ginf → (X.Vpi u' →L[ℂ] X.Vpi u) := fun x =>
    Formalism.L2.SG.TermOp.rk1 (X.Wu u x) (X.Wu u' (γ⁻¹ * x))
  have hψc : ∀ v, Continuous (ψ v) := fun v =>
    continuous_rankOneOperator (X.Wloc_cont u v) ((X.Wloc_cont u' v).comp (continuous_const.mul continuous_id))
  have hΦc : Continuous Φ :=
    continuous_rankOneOperator (X.Wu_spec u).2.2.1 ((X.Wu_spec u').2.2.1.comp (continuous_const.mul continuous_id))
  have hψi : ∀ v, ∀ s ∈ R v, ∀ x, ψ v (s * x) = ψ v x := fun v s hs x => hinv v s hs x
  have hΦr : ∀ x, ‖Φ x‖ = ∏ v, ‖ψ v (x v)‖ := by
    intro x
    simp only [Φ, ψ, norm_rankOneInnerOperator, X.Wu_tens, Formalism.L2.SG.RealObj.RankOneTensors.norm_tens (X.tensU u) (X.tensU_inner u),
      Formalism.L2.SG.RealObj.RankOneTensors.norm_tens (X.tensU u') (X.tensU_inner u'), ← Finset.prod_mul_distrib]
    rfl
  have hΦn : ∀ x, ‖Φ x‖ₑ = ∏ v, ‖ψ v (x v)‖ₑ := by
    intro x
    rw [← ofReal_norm, hΦr, ENNReal.ofReal_prod_of_nonneg fun v _ => norm_nonneg _]
    simp only [ofReal_norm]
  have hL : ∫⁻ x, ‖Φ x‖ₑ ∂ν = ∏ v, ∫⁻ z, ‖ψ v z‖ₑ ∂(νl v) := by
    simp_rw [hΦn]
    exact hq.1 (fun v z => ‖ψ v z‖ₑ) (fun v => (hψc v).measurable.enorm) fun v s hs x => by
      simp only [hψi v s hs x]
  have hOO : Formalism.L2.SG.TermOp.OO ν Set.univ (X.Wu u) (X.Wu u') γ = ∫ x, Φ x ∂ν := by
    unfold Formalism.L2.SG.TermOp.OO
    rw [Measure.restrict_univ]
  have hJv : ∀ v, Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u' v) (γ v) = ∫ z, ψ v z ∂(νl v) := by
    intro v
    unfold Formalism.L2.SG.RealObj.Jv Formalism.L2.SG.TermOp.OO
    rw [Measure.restrict_univ]
  rw [hOO]
  simp only [hJv]
  by_cases h0 : ∃ v, ∫⁻ z, ‖ψ v z‖ₑ ∂(νl v) = 0
  · obtain ⟨v0, hv0⟩ := h0
    have hrhs : ∏ v, Formalism.MainNotions.S.hsNormSq (∫ z, ψ v z ∂(νl v)) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ v0) ?_
      have hz : ψ v0 =ᵐ[νl v0] 0 := by
        have := (lintegral_eq_zero_iff (hψc v0).measurable.enorm).1 hv0
        filter_upwards [this] with z hz
        simpa using hz
      rw [integral_eq_zero_of_ae hz, hsNormSq_zero]
    have hlhs : ∫ x, Φ x ∂ν = 0 := by
      have hg : ∫⁻ x, ‖Φ x‖ₑ ∂ν = 0 := by
        rw [hL]; exact Finset.prod_eq_zero (Finset.mem_univ v0) hv0
      have hz : Φ =ᵐ[ν] 0 := by
        have := (lintegral_eq_zero_iff hΦc.measurable.enorm).1 hg
        filter_upwards [this] with z hz
        simpa using hz
      exact integral_eq_zero_of_ae hz
    rw [hrhs, hlhs, hsNormSq_zero]
  push_neg at h0
  by_cases hT : ∃ v, ∫⁻ z, ‖ψ v z‖ₑ ∂(νl v) = ⊤
  · obtain ⟨v0, hv0⟩ := hT
    have hrhs : ∏ v, Formalism.MainNotions.S.hsNormSq (∫ z, ψ v z ∂(νl v)) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ v0) ?_
      have hni : ¬ Integrable (ψ v0) (νl v0) := fun hi => hi.2.ne hv0
      rw [integral_undef hni, hsNormSq_zero]
    have hg : ∫⁻ x, ‖Φ x‖ₑ ∂ν = ⊤ := by
      rw [hL, ← Finset.mul_prod_erase _ _ (Finset.mem_univ v0), hv0]
      exact ENNReal.top_mul (Finset.prod_ne_zero_iff.2 fun v _ => h0 v)
    have hlhs : ∫ x, Φ x ∂ν = 0 := integral_undef fun hi => hi.2.ne hg
    rw [hrhs, hlhs, hsNormSq_zero]
  push_neg at hT
  have hψI : ∀ v, Integrable (ψ v) (νl v) := fun v =>
    ⟨(hψc v).aestronglyMeasurable, lt_top_iff_ne_top.2 (hT v)⟩
  have hΦI : Integrable Φ ν := ⟨hΦc.aestronglyMeasurable, by
    show ∫⁻ x, ‖Φ x‖ₑ ∂ν < ⊤
    rw [hL]; exact ENNReal.prod_lt_top fun v _ => lt_top_iff_ne_top.2 (hT v)⟩
  refine hs_tens X u u' _ _ fun y => ?_
  have hent : ∀ e : ∀ v, X.Vloc u v, ⟪X.tensU u e, (∫ x, Φ x ∂ν) (X.tensU u' y)⟫_ℂ =
      ⟪X.tensU u e, X.tensU u (fun v => (∫ z, ψ v z ∂(νl v)) (y v))⟫_ℂ := by
    intro e
    rw [X.tensU_inner]
    let L : (X.Vpi u' →L[ℂ] X.Vpi u) →L[ℂ] ℂ :=
      (innerSL ℂ (X.tensU u e)).comp (ContinuousLinearMap.apply ℂ (X.Vpi u) (X.tensU u' y))
    have h1 : L (∫ x, Φ x ∂ν) = ∫ x, L (Φ x) ∂ν := (L.integral_comp_comm hΦI).symm
    have h2 : ∀ v, ⟪e v, (∫ z, ψ v z ∂(νl v)) (y v)⟫_ℂ = ∫ z, ⟪e v, ψ v z (y v)⟫_ℂ ∂(νl v) := by
      intro v
      let Lv : (X.Vloc u' v →L[ℂ] X.Vloc u v) →L[ℂ] ℂ :=
        (innerSL ℂ (e v)).comp (ContinuousLinearMap.apply ℂ (X.Vloc u v) (y v))
      exact (Lv.integral_comp_comm (hψI v)).symm
    have h3 : ∀ x, L (Φ x) = ∏ v, ⟪e v, ψ v (x v) (y v)⟫_ℂ := by
      intro x
      show ⟪X.tensU u e, Φ x (X.tensU u' y)⟫_ℂ = _
      simp only [Φ, ψ, Formalism.L2.SG.TermOp.rankOneInnerOperator_apply, inner_smul_right, X.Wu_tens, X.tensU_inner,
        ← Finset.prod_mul_distrib]
      rfl
    have h4 := hq.2 (fun v z => ⟪e v, ψ v z (y v)⟫_ℂ)
      (fun v => (continuous_const.inner ((hψc v).clm_apply continuous_const)).measurable)
      (fun v s hs x => by simp only [hψi v s hs x])
    show L (∫ x, Φ x ∂ν) = _
    rw [h1, integral_congr_ae (Filter.Eventually.of_forall h3), h4]
    exact Finset.prod_congr rfl fun v _ => (h2 v).symm
  set d := (∫ x, Φ x ∂ν) (X.tensU u' y) - X.tensU u (fun v => (∫ z, ψ v z ∂(νl v)) (y v)) with hd
  have hw : ∀ w ∈ Submodule.span ℂ (Set.range (X.tensU u)), ⟪w, d⟫_ℂ = 0 := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨e, rfl⟩ := hw
      rw [hd, inner_sub_right, hent, sub_self]
    | zero => exact inner_zero_left _
    | add a b _ _ ha hb => rw [inner_add_left, ha, hb, add_zero]
    | smul c a _ ha => rw [inner_smul_left, ha, mul_zero]
  have := hw d (by rw [X.tensU_span u]; exact Submodule.mem_top)
  exact sub_eq_zero.1 (inner_self_eq_zero.1 this)

end GlobalTheory.OrbQuotProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealOrbitalIntegralHsNormEqProdLocalStatement
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2 Formalism.L2.SG.LocWSOf
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realOrbitalIntegral_hsNorm_eq_prod_local : ∀ (D : D7) (X : HidaSetting D) (u u' : D.what₂.Word) (γ : X.B.I.Ginf) (μl νl : ∀ v, Measure (Formalism.REAL.UJ (X.B.I.ε v))) (ν : Measure X.B.I.Ginf), (∀ v, Formalism.L2.SG.RealObj.IsHaarLoc (Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (γ v)) (μl v)) → (∀ v, Formalism.L2.SG.RealObj.IsQuotLoc (μl v) (νl v)) → IsQuotMeasS X.B.I (Measure.pi μl) ν → (∀ v, ∀ s ∈ Formalism.L2.SG.RealObj.StSet (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u))) (Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates.NLoc (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u'))) (γ v), ∀ x, Formalism.L2.SG.TermOp.rk1 (X.Wloc u v (s * x)) (X.Wloc u' v ((γ v)⁻¹ * (s * x))) = Formalism.L2.SG.TermOp.rk1 (X.Wloc u v x) (X.Wloc u' v ((γ v)⁻¹ * x))) → hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vpi u); Formalism.L2.SG.TermOp.OO ν Set.univ (X.Wu u) (X.Wu u') γ) = ∏ v, hsNormSq (haveI := FiniteDimensional.complete ℂ (X.Vloc u v); Formalism.L2.SG.RealObj.Jv (νl v) (X.Wloc u v) (X.Wloc u' v) (γ v)) := by
  first | exact @GlobalTheory.OrbQuotProd.oo_quot | exact GlobalTheory.OrbQuotProd.oo_quot | (intros; apply GlobalTheory.OrbQuotProd.oo_quot <;> assumption)
end
