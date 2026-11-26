module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselUnipotentMulVecMiddleVec
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberAndFibreSetsMeasurableStatement
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RadicalCoordinatesBoundedMajorantLengths
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MovedDualVectorPairingBoundedMajorant

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeGramConditionCodimTwoThree
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeGramConditionCodimTwoThree
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.GramVol

theorem vol_gram_codim_three : ∀ (k r : ℕ), 1 ≤ r → 2 * r + 6 ≤ k → ∀ m ∈ UH (Hb k), ∀ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), (Module.finrank ℂ P₀ = k - 2 ∨ Module.finrank ℂ P₀ = k - 1) → volume {B : Fin r → Fin (k + 1) → ℂ | gramProj P₀ (fun b => m⁻¹ *ᵥ B b) = 0} = 0 ∧ ∀ R' y : ℝ, 1 ≤ R' → 0 < y → volume {B : Fin r → Fin (k + 1) → ℂ | (∀ b, eucl (m⁻¹ *ᵥ B b) ≤ R') ∧ y < gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ∧ gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ≤ 2 * y} ≤ ENNReal.ofReal ((Real.pi * R' ^ 2) ^ (3 * r) * 4 * R' ^ (2 * r ^ 2 + 2 * r) * Real.pi ^ (r ^ 2) * (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) * (2 * y) ^ (2 * (k - 2 - r))) := by
  intro k j _ hjk m hm P hP0
  have hP : k - 2 ≤ Module.finrank ℂ P := by omega
  obtain ⟨d, rfl⟩ : ∃ d, k = d + 2 := ⟨k - 2, by omega⟩
  have hd : d + 2 - 2 = d := by omega
  rw [hd] at hP ⊢
  have key := vol_le d 3 j (by omega) m⁻¹ (norm_det_inv_eq_one hm) P hP
  obtain ⟨s, hs⟩ : ∃ s, d = j + s := ⟨d - j, by omega⟩
  have hs1 : 1 ≤ s := by omega
  have hs2 : d - j = s := by omega
  rw [hs2] at key ⊢
  refine ⟨?_, fun M y hM hy => ?_⟩
  · have hz : ∀ N : ℕ, volume {B : Fin j → Fin (d + 2 + 1) → ℂ | (∀ b, eucl (m⁻¹ *ᵥ B b) ≤ (N : ℝ) + 1) ∧
        gramProj P (fun b => m⁻¹ *ᵥ B b) ≤ 0} = 0 := fun N => by
      have := key ((N : ℝ) + 1) 0 (by positivity) le_rfl
      rw [zero_pow (by omega)] at this
      simpa using this
    refine measure_mono_null ?_ (measure_iUnion_null hz)
    intro B hB
    obtain ⟨N, hN⟩ := exists_nat_ge (∑ b, eucl (m⁻¹ *ᵥ B b))
    refine Set.mem_iUnion.2 ⟨N, fun b => ?_, le_of_eq hB⟩
    have : eucl (m⁻¹ *ᵥ B b) ≤ ∑ b, eucl (m⁻¹ *ᵥ B b) :=
      Finset.single_le_sum (f := fun b => eucl (m⁻¹ *ᵥ B b)) (fun _ _ => Real.sqrt_nonneg _) (Finset.mem_univ b)
    linarith
  · refine le_trans (measure_mono fun B hB => ?_)
      (le_trans (key M (2 * y) (by positivity) (by positivity)) (ENNReal.ofReal_le_ofReal ?_))
    · exact ⟨hB.1, hB.2.2⟩
    have hpi := Real.pi_pos
    have h1 : (1 / (s.factorial : ℝ)) ^ j ≤ ((Real.exp 1 / s) ^ s) ^ j :=
      pow_le_pow_left₀ (by positivity) (inv_factorial_le s hs1) j
    have h2 : M ^ (2 * j ^ 2) ≤ 4 * M ^ (2 * j ^ 2 + 2 * j) := by
      have h3 : M ^ (2 * j ^ 2) ≤ M ^ (2 * j ^ 2 + 2 * j) := pow_le_pow_right₀ hM (Nat.le_add_right _ _)
      have h4 : 0 ≤ M ^ (2 * j ^ 2 + 2 * j) := by positivity
      linarith
    calc _ = (Real.pi * M ^ 2) ^ (3 * j) * M ^ (2 * j ^ 2) * Real.pi ^ (j ^ 2) *
          (Real.pi ^ (j * s) * (1 / (s.factorial : ℝ)) ^ j) * (2 * y) ^ (2 * s) := by
          rw [hs, mul_add j j s, pow_add, ← sq j, one_div, inv_pow, div_eq_mul_inv]; ring
      _ ≤ (Real.pi * M ^ 2) ^ (3 * j) * (4 * M ^ (2 * j ^ 2 + 2 * j)) * Real.pi ^ (j ^ 2) *
          (Real.pi ^ (j * s) * ((Real.exp 1 / s) ^ s) ^ j) * (2 * y) ^ (2 * s) := by gcongr
      _ = _ := by
          rw [← pow_mul (Real.exp 1 / s), mul_comm s j, ← mul_pow, mul_div_assoc, mul_assoc _ (4 : ℝ)]

end GlobalTheory.Amp.GramVol
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeGramConditionCodimTwoThreeStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_gramCondition_codim_two_three : ∀ (k r : ℕ), 1 ≤ r → 2 * r + 6 ≤ k → ∀ m ∈ UH (Hb k), ∀ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), (Module.finrank ℂ P₀ = k - 2 ∨ Module.finrank ℂ P₀ = k - 1) → volume {B : Fin r → Fin (k + 1) → ℂ | gramProj P₀ (fun b => m⁻¹ *ᵥ B b) = 0} = 0 ∧ ∀ R' y : ℝ, 1 ≤ R' → 0 < y → volume {B : Fin r → Fin (k + 1) → ℂ | (∀ b, eucl (m⁻¹ *ᵥ B b) ≤ R') ∧ y < gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ∧ gramProj P₀ (fun b => m⁻¹ *ᵥ B b) ≤ 2 * y} ≤ ENNReal.ofReal ((Real.pi * R' ^ 2) ^ (3 * r) * 4 * R' ^ (2 * r ^ 2 + 2 * r) * Real.pi ^ (r ^ 2) * (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) * (2 * y) ^ (2 * (k - 2 - r))) := by
  first | exact @GlobalTheory.Amp.GramVol.vol_gram_codim_three | exact GlobalTheory.Amp.GramVol.vol_gram_codim_three | (intros; apply GlobalTheory.Amp.GramVol.vol_gram_codim_three <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberNormalFormEqGramProjection
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberNormalFormEqGramProjection
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Amp.Rad
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.NormGram

variable {k r : ℕ}

def rE (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Fin r → ℂ := fun a => v (eI k r a)

def rW (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Fin (k + 1) → ℂ := fun j => v (wI k r j)

def rS (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Fin r → ℂ := fun a => v (esI k r a)

def iW (k r : ℕ) (w : Fin (k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := ∑ j, w j • bvec (wI k r j)

theorem iW_e (w : Fin (k + 1) → ℂ) (a : Fin r) : iW k r w (eI k r a) = 0 := by
  simp [iW, Finset.sum_apply, bvec_apply, eI_ne_wI]
theorem middleSpaceEmbedding_apply_dualIsotropicIndex (w : Fin (k + 1) → ℂ) (a : Fin r) : iW k r w (esI k r a) = 0 := by
  simp [iW, Finset.sum_apply, bvec_apply, esI_ne_wI]
theorem iW_w (w : Fin (k + 1) → ℂ) (j : Fin (k + 1)) : iW k r w (wI k r j) = w j := by
  simp [iW, Finset.sum_apply, bvec_apply, wI_inj]

theorem H_e (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : (Hpk k r *ᵥ v) (eI k r a) = v (esI k r a) := by
  simp [Matrix.mulVec, dotProduct, sum3, H_ee, H_ew, H_es]
theorem H_w (v : Fin (2 * r + k + 1) → ℂ) (j : Fin (k + 1)) :
    (Hpk k r *ᵥ v) (wI k r j) = sg k j * v (wI k r j) := by
  simp [Matrix.mulVec, dotProduct, sum3, H_we, H_ww, H_ws]
theorem besselHermForm_mulVec_dualIsotropicIndex (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : (Hpk k r *ᵥ v) (esI k r a) = v (eI k r a) := by
  simp [Matrix.mulVec, dotProduct, sum3, H_se, H_sw, H_ss]

theorem herm3 (v w : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) v w =
    star (rE k r w) ⬝ᵥ rS k r v + herm (Hb k) (rW k r v) (rW k r w) + star (rS k r w) ⬝ᵥ rE k r v := by
  rw [herm_Hb]
  unfold herm
  rw [dotProduct, sum3]
  simp [H_e, H_w, besselHermForm_mulVec_dualIsotropicIndex, rE, rW, rS, dotProduct]

theorem herm_e (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (eI k r a)) = v (esI k r a) := by
  unfold herm
  rw [← H_e v a]
  simp [bvec, dotProduct, Pi.single_apply, apply_ite]

theorem HH : Hpk k r * Hpk k r = 1 := by
  ext x y
  rw [Matrix.mul_apply, sum3]
  induction x using cases3 <;> induction y using cases3 <;>
    simp [H_ee, H_ew, H_es, H_we, H_ww, H_ws, H_se, H_sw, H_ss, Matrix.one_apply,
      eI_inj, wI_inj, esI_inj, eI_ne_wI, eI_ne_esI, wI_ne_esI, wI_ne_eI, esI_ne_eI, esI_ne_wI]
  unfold sg; split_ifs <;> simp_all

theorem HbHb : Hb k * Hb k = 1 := by
  unfold Hb; rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1; funext j; split_ifs <;> simp

theorem unit_of_UH {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hH : H * H = 1) (hg : g ∈ UH H) : IsUnit g.det := by
  have hm' : gᴴ * H * g = H := hg
  have h1 : (H * gᴴ * H) * g = 1 := by
    rw [← hH]; nth_rewrite 4 [← hm']; simp only [Matrix.mul_assoc]
  exact Matrix.isUnit_det_of_left_inverse h1

theorem herm_iso {n : ℕ} {H g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UH H) (v w : Fin n → ℂ) :
    herm H (g *ᵥ v) (g *ᵥ w) = herm H v w := by
  have hm' : gᴴ * H * g = H := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hm']

theorem herm_inv {g : Mat k r} (hg : g ∈ GG k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v (g⁻¹ *ᵥ w) = herm (Hpk k r) (g *ᵥ v) w := by
  rw [← herm_iso hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (unit_of_UH HH hg), Matrix.one_mulVec]

theorem herm_inv' {g : Mat k r} (hg : g ∈ GG k r) (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (g⁻¹ *ᵥ v) w = herm (Hpk k r) v (g *ᵥ w) := by
  rw [← herm_iso hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (unit_of_UH HH hg), Matrix.one_mulVec]

theorem of_Xst {v : Fin (2 * r + k + 1) → ℂ} (hv : v ∈ Xst k r) : rE k r v = 0 ∧ rW k r v = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, rfl⟩ := hx
    constructor <;> funext j <;> simp [rE, rW, bvec_apply, eI_ne_esI, wI_ne_esI]
  | zero => exact ⟨rfl, rfl⟩
  | add x y _ _ hx hy =>
    constructor <;> funext j
    · have := congrFun hx.1 j; have := congrFun hy.1 j; simp_all [rE]
    · have := congrFun hx.2 j; have := congrFun hy.2 j; simp_all [rW]
  | smul c x _ hx =>
    constructor <;> funext j
    · have := congrFun hx.1 j; simp_all [rE]
    · have := congrFun hx.2 j; simp_all [rW]

theorem mem_Xsp {v : Fin (2 * r + k + 1) → ℂ} : v ∈ Xsp k r ↔ rW k r v = 0 ∧ rS k r v = 0 := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      constructor <;> funext j <;> simp [rS, rW, bvec_apply, esI_ne_eI, wI_ne_eI]
    | zero => exact ⟨rfl, rfl⟩
    | add x y _ _ hx hy =>
      constructor <;> funext j
      · have := congrFun hx.1 j; have := congrFun hy.1 j; simp_all [rW]
      · have := congrFun hx.2 j; have := congrFun hy.2 j; simp_all [rS]
    | smul c x _ hx =>
      constructor <;> funext j
      · have := congrFun hx.1 j; simp_all [rW]
      · have := congrFun hx.2 j; simp_all [rS]
  · rintro ⟨h1, h2⟩
    have : v = ∑ a, v (eI k r a) • bvec (eI k r a) := by
      funext x
      induction x using cases3 with
      | h1 a => simp [Finset.sum_apply, bvec_apply, eI_inj]
      | h2 j => simpa [Finset.sum_apply, bvec_apply, wI_ne_eI, rW] using congrFun h1 j
      | h3 a => simpa [Finset.sum_apply, bvec_apply, esI_ne_eI, rS] using congrFun h2 a
    rw [this]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

theorem of_inWb {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : rE k r z = 0 ∧ rS k r z = 0 := by
  constructor <;> funext a
  · exact hz _ (Or.inl a.2)
  · have := a.2
    exact hz _ (Or.inr (by simp only [esI]; omega))

theorem rW_u (u : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    rW k r (uEmb k r u *ᵥ v) = rW k r v := by
  funext j
  have := j.2
  have h : ∀ y, uEmb k r u (wI k r j) y = if wI k r j = y then 1 else 0 := fun y => by
    unfold uEmb; rw [dite_eq_right (by simp only [wI]; omega), dite_eq_right (by simp only [wI]; omega)]
  simp [rW, Matrix.mulVec, dotProduct, h]

theorem rS_u (u : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    rS k r (uEmb k r u *ᵥ v) = (u⁻¹)ᴴ *ᵥ rS k r v := by
  funext a
  have := a.2
  have hb : ∀ (b : Fin r) h, (⟨2 * r + k - (esI k r b).val, h⟩ : Fin r) = b := fun b h =>
    Fin.ext (by have := b.2; simp only [esI]; omega)
  have h1 : ∀ b, uEmb k r u (esI k r a) (eI k r b) = 0 := fun b => by
    have := b.2
    unfold uEmb; rw [dite_eq_right (by simp only [esI]; omega), dite_eq_right (by simp only [eI]; omega), if_neg (esI_ne_eI _ _)]
  have h2 : ∀ b, uEmb k r u (esI k r a) (wI k r b) = 0 := fun b => by
    have := b.2
    unfold uEmb; rw [dite_eq_right (by simp only [esI]; omega), dite_eq_right (by simp only [wI]; omega), if_neg (esI_ne_wI _ _)]
  have h3 : ∀ b, uEmb k r u (esI k r a) (esI k r b) = star (u⁻¹ b a) := fun b => by
    have := b.2
    unfold uEmb; rw [dite_eq_right (by simp only [esI]; omega), dite_eq_left (by simp only [esI]; omega)]
    simp only [hb]
  simp [rS, Matrix.mulVec, dotProduct, sum3, h1, h2, h3]

theorem rW_p (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    rW k r (pEl k r B S *ᵥ v) = rW k r v + ∑ b, rS k r v b • B b := by
  funext j
  simp [rW, rS, Matrix.mulVec, dotProduct, sum3, pEl_we, pEl_ww, pEl_ws, Finset.sum_apply, mul_comm]

theorem rS_p (B : Fin r → Fin (k + 1) → ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    rS k r (pEl k r B S *ᵥ v) = rS k r v := by
  funext j
  simp [rS, Matrix.mulVec, dotProduct, sum3, pEl_se, pEl_sw, pEl_ss]

theorem rW_m (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    rW k r (mEmb k r m *ᵥ v) = m *ᵥ rW k r v := by
  funext j
  simp [rW, Matrix.mulVec, dotProduct, sum3, m_we, m_ww, m_ws]

theorem rS_m (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v : Fin (2 * r + k + 1) → ℂ) :
    rS k r (mEmb k r m *ᵥ v) = rS k r v := by
  funext j
  simp [rS, Matrix.mulVec, dotProduct, middleSpaceLeviEmbedding_apply_es_row]

theorem gramProj_mid (P : Submodule ℂ (EuclideanSpace ℂ (Fin (2 * r + k + 1))))
    (P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))))
    (hP : ∀ p, p ∈ P ↔ rE k r p.ofLp = 0 ∧ rS k r p.ofLp = 0 ∧ WithLp.toLp 2 (rW k r p.ofLp) ∈ P₀)
    {n : ℕ} (v : Fin n → Fin (2 * r + k + 1) → ℂ) : gramProj P v = gramProj P₀ fun a => rW k r (v a) := by
  have hin : ∀ x p : EuclideanSpace ℂ (Fin (2 * r + k + 1)), rE k r p.ofLp = 0 → rS k r p.ofLp = 0 →
      ⟪x, p⟫_ℂ = ⟪(WithLp.toLp 2 (rW k r x.ofLp) : EuclideanSpace ℂ _), WithLp.toLp 2 (rW k r p.ofLp)⟫_ℂ := by
    intro x p h1 h2
    have h1' : ∀ a, p.ofLp (eI k r a) = 0 := congrFun h1
    have h2' : ∀ a, p.ofLp (esI k r a) = 0 := congrFun h2
    simp [PiLp.inner_apply, sum3, h1', h2', rW]
  have hW : ∀ w, rW k r (iW k r w) = w := fun w => funext (iW_w w)
  have hE : ∀ w, rE k r (iW k r w) = 0 := fun w => funext (iW_e w)
  have hS : ∀ w, rS k r (iW k r w) = 0 := fun w => funext (middleSpaceEmbedding_apply_dualIsotropicIndex w)
  have hpr : ∀ x : Fin (2 * r + k + 1) → ℂ, P.starProjection (WithLp.toLp 2 x) =
      WithLp.toLp 2 (iW k r (P₀.starProjection (WithLp.toLp 2 (rW k r x))).ofLp) := by
    intro x
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · rw [hP]; refine ⟨hE _, hS _, ?_⟩
      simp only [hW]
      exact Submodule.starProjection_apply_mem _ _
    · intro w hw
      obtain ⟨h1, h2, h3⟩ := (hP w).1 hw
      rw [inner_sub_left, hin _ _ h1 h2, hin _ _ h1 h2, ← inner_sub_left]
      simp only [hW]
      exact Submodule.starProjection_inner_eq_zero _ _ h3
  unfold gramProj
  congr 3
  ext a b
  simp only [Matrix.gram_apply, hpr]
  rw [hin _ (WithLp.toLp 2 (iW k r _)) (hE _) (hS _)]
  simp only [hW]

theorem gramProj_comb {n : ℕ} (P : Submodule ℂ (EuclideanSpace ℂ (Fin n))) (T : Matrix (Fin r) (Fin r) ℂ)
    (w : Fin r → Fin n → ℂ) : gramProj P (fun c => ∑ b, T b c • w b) = ‖T.det‖ * gramProj P w := by
  unfold gramProj
  have : (Matrix.gram ℂ fun c => P.starProjection (WithLp.toLp 2 (∑ b, T b c • w b))) =
      Tᴴ * (Matrix.gram ℂ fun a => P.starProjection (WithLp.toLp 2 (w a))) * T := by
    ext a b
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.gram_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, WithLp.toLp_sum, WithLp.toLp_smul,
      map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp; ring
  rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, norm_mul, norm_mul, norm_star,
    mul_right_comm, Real.sqrt_mul (by positivity), Real.sqrt_mul_self (norm_nonneg _)]

def Cm (k r : ℕ) (g : Mat k r) : Matrix (Fin r) (Fin r) ℂ := fun b c => (g⁻¹ *ᵥ bvec (eI k r c)) (esI k r b)

section normal
variable {z z' : Fin (2 * r + k + 1) → ℂ} {g : Mat k r} {β : Fin r → ℕ}

theorem herm_Cm (hn : IsNormal k r β g) (w : Fin (2 * r + k + 1) → ℂ) (c : Fin r) :
    herm (Hpk k r) w (g⁻¹ *ᵥ bvec (eI k r c)) = ((Cm k r g)ᴴ *ᵥ rE k r w) c := by
  obtain ⟨h1, h2⟩ := of_Xst (hn.2.1 c).1
  rw [herm3, h1, h2]
  simp [herm, Matrix.mulVec, dotProduct, Cm, rS]

theorem fvec_cast (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) : fvec k r z a.castSucc = bvec (eI k r a) := by
  simp [fvec]
theorem fvec_last (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by
  simp [fvec]

theorem Dmin_r (hn : IsNormal k r β g) : Dmin k r z z' g ⟨r, by omega⟩ = ((Cm k r g)ᴴ).det := by
  unfold Dmin
  congr 1
  ext a b
  show herm (Hpk k r) (g *ᵥ fvec k r z' (Fin.castSucc b)) (fvec k r z (Fin.castSucc a)) = _
  rw [fvec_cast, fvec_cast, ← herm_inv hn.1, herm_Cm hn]
  simp [Matrix.mulVec, dotProduct, rE, bvec_apply, eI_inj]

theorem Dmin_last (hn : IsNormal k r β g) (hz : inWb k r z) : Dmin k r z z' g (Fin.last (r + 1)) =
    herm (Hpk k r) (g *ᵥ z') z * Dmin k r z z' g ⟨r, by omega⟩ := by
  have h1 : Dmin k r z z' g (Fin.last (r + 1)) = (Zhat k r z z' g).det := rfl
  have h2 : Dmin k r z z' g ⟨r, by omega⟩ = ((Zhat k r z z' g).submatrix Fin.castSucc Fin.castSucc).det := rfl
  have h3 : ∀ b : Fin r, Zhat k r z z' g (Fin.last r) b.castSucc = 0 := by
    intro b
    obtain ⟨h1, h2⟩ := of_Xst (hn.2.1 b).2
    obtain ⟨h3, h4⟩ := of_inWb hz
    unfold Formalism.QuantumDeterminants.Zhat
    rw [fvec_cast, fvec_last, herm3, h1, h2, h3]
    simp [herm]
  rw [h1, h2, Matrix.det_succ_row _ (Fin.last r), Fin.sum_univ_castSucc]
  simp only [h3, mul_zero, zero_mul, Finset.sum_const_zero, zero_add, Fin.succAbove_last, Fin.val_last]
  rw [← two_mul, pow_mul]
  simp [Formalism.QuantumDeterminants.Zhat, fvec_last]

theorem mem_Hcom (hn : IsNormal k r β g) (hC : (Cm k r g).det ≠ 0) (w : Fin (2 * r + k + 1) → ℂ) :
    w ∈ Hcom k r z z' g ↔ rE k r w = 0 ∧ rS k r w = 0 ∧ herm (Hb k) (rW k r w) (rW k r z') = 0 ∧
      herm (Hb k) (rW k r w) (rW k r (g⁻¹ *ᵥ z)) = 0 := by
  show (∀ a : Fin (r + 1), _ ∧ _) ↔ _
  rw [Fin.forall_fin_succ']
  simp only [fvec_cast, fvec_last, herm_e, herm_Cm hn]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hS : rS k r w = 0 := funext fun a => (h1 a).1
    have hE : rE k r w = 0 := by
      apply Matrix.eq_zero_of_mulVec_eq_zero (M := (Cm k r g)ᴴ)
      · rw [Matrix.det_conjTranspose]; exact star_ne_zero.2 hC
      · exact funext fun a => (h1 a).2
    rw [herm3, hS, hE] at h2 h3
    exact ⟨hE, hS, by simpa using h2, by simpa using h3⟩
  · rintro ⟨hE, hS, h2, h3⟩
    refine ⟨fun a => ⟨congrFun hS a, by simp [hE]⟩, ?_, ?_⟩ <;> rw [herm3, hS, hE] <;> simpa

theorem mem_sup (hn : IsNormal k r β g) (hC : (Cm k r g).det ≠ 0) (v : Fin (2 * r + k + 1) → ℂ) :
    v ∈ Hcom k r z z' g ⊔ Xsp k r ↔ rS k r v = 0 ∧ herm (Hb k) (rW k r v) (rW k r z') = 0 ∧
      herm (Hb k) (rW k r v) (rW k r (g⁻¹ *ᵥ z)) = 0 := by
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨w, hw, x, hx, rfl⟩
    obtain ⟨-, h2, h3, h4⟩ := (mem_Hcom hn hC w).1 hw
    obtain ⟨h5, h6⟩ := mem_Xsp.1 hx
    have e1 : rW k r (w + x) = rW k r w + rW k r x := rfl
    have e2 : rS k r (w + x) = rS k r w + rS k r x := rfl
    rw [e1, e2, h2, h5, h6, add_zero, add_zero]
    exact ⟨rfl, h3, h4⟩
  · rintro ⟨h1, h2, h3⟩
    have hW : ∀ w, rW k r (iW k r w) = w := fun w => funext (iW_w w)
    have hE : ∀ w, rE k r (iW k r w) = 0 := fun w => funext (iW_e w)
    have hS : ∀ w, rS k r (iW k r w) = 0 := fun w => funext (middleSpaceEmbedding_apply_dualIsotropicIndex w)
    refine ⟨iW k r (rW k r v), (mem_Hcom hn hC _).2 ⟨hE _, hS _, by rwa [hW], by rwa [hW]⟩,
      v - iW k r (rW k r v), mem_Xsp.2 ⟨?_, ?_⟩, by abel⟩
    · show rW k r v - rW k r (iW k r (rW k r v)) = 0
      rw [hW, sub_self]
    · show rS k r v - rS k r (iW k r (rW k r v)) = 0
      rw [hS, h1, sub_self]

theorem Cm_det (ht : TwoFl k r z z' g) (hn : IsNormal k r β g) :
    Dr k r z z' g = ‖(Cm k r g).det‖ ∧ (Cm k r g).det ≠ 0 := by
  have h : Dr k r z z' g = ‖(Cm k r g).det‖ := by
    unfold Dr; rw [Dmin_r hn, Matrix.det_conjTranspose, norm_star]
  exact ⟨h, fun h0 => ht.2.2.2.2.2.2 (by rw [h, h0, norm_zero])⟩

theorem gram_ne (ht : TwoFl k r z z' g) (hn : IsNormal k r β g) :
    herm (Hb k) (rW k r z') (rW k r z') * herm (Hb k) (rW k r (g⁻¹ *ᵥ z)) (rW k r (g⁻¹ *ᵥ z)) -
      herm (Hb k) (rW k r z') (rW k r (g⁻¹ *ᵥ z)) * herm (Hb k) (rW k r (g⁻¹ *ᵥ z)) (rW k r z') ≠ 0 := by
  obtain ⟨hz, hz', -, -, hg, hG, -⟩ := ht
  obtain ⟨z1, z2⟩ := of_inWb hz
  obtain ⟨z1', z2'⟩ := of_inWb hz'
  have hy : rS k r (g⁻¹ *ᵥ z) = 0 := by
    funext a
    obtain ⟨h1, h2⟩ := of_Xst (hn.2.1 a).2
    show (g⁻¹ *ᵥ z) (esI k r a) = 0
    rw [← herm_e (g⁻¹ *ᵥ z) a, herm_inv' hg, herm3, h1, h2, z1]
    simp [herm]
  have real : ∀ v : Fin (k + 1) → ℂ, herm (Hb k) v v = ((herm (Hb k) v v).re : ℂ) := fun v =>
    (Complex.conj_eq_iff_re.1 (herm_star v v)).symm
  have e1 : herm (Hb k) (rW k r z') (rW k r z') = -(Tz k r z' : ℂ) := by
    rw [real, Tz, herm3, z1', z2']; simp
  have e2 : herm (Hb k) (rW k r (g⁻¹ *ᵥ z)) (rW k r (g⁻¹ *ᵥ z)) = -(Tz k r z : ℂ) := by
    have : herm (Hpk k r) z z = herm (Hpk k r) (g⁻¹ *ᵥ z) (g⁻¹ *ᵥ z) := by
      rw [herm_inv hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (unit_of_UH HH hg), Matrix.one_mulVec]
    rw [real, Tz, this, herm3, hy]; simp
  have e3 : herm (Hb k) (rW k r z') (rW k r (g⁻¹ *ᵥ z)) = herm (Hpk k r) (g *ᵥ z') z := by
    rw [← herm_inv hg, herm3, z1', z2']; simp
  rw [← herm_star (rW k r z') (rW k r (g⁻¹ *ᵥ z)), e1, e2, e3]
  intro h0
  apply hG
  unfold Gf
  rw [Dmin_last hn hz, map_mul]
  have : Complex.normSq (herm (Hpk k r) (g *ᵥ z') z) = Tz k r z * Tz k r z' := by
    apply Complex.ofReal_injective
    rw [← Complex.mul_conj]
    push_cast
    simp only [Complex.star_def] at h0
    linear_combination -h0
  rw [this, sub_self]

end normal

def pair2 (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (s t : Fin (k + 1) → ℂ) :
    EuclideanSpace ℂ (Fin (k + 1)) →ₗ[ℂ] ℂ × ℂ where
  toFun p := (herm (Hb k) (m *ᵥ p.ofLp) s, herm (Hb k) (m *ᵥ p.ofLp) t)
  map_add' p q := by simp [herm, Matrix.mulVec_add]
  map_smul' c p := by simp [herm, Matrix.mulVec_smul]

def Pz (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (s t : Fin (k + 1) → ℂ) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))) :=
  LinearMap.ker ((pair2 m s t).prod (EuclideanSpace.projₗ (Fin.last k)))

theorem mem_Pz (m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (s t p : Fin (k + 1) → ℂ) :
    WithLp.toLp 2 p ∈ Pz m s t ↔ (herm (Hb k) (m *ᵥ p) s = 0 ∧ herm (Hb k) (m *ᵥ p) t = 0) ∧ p (Fin.last k) = 0 := by
  simp [Pz, pair2]

theorem finrank_Pz {m : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hm : IsUnit m.det) {s t : Fin (k + 1) → ℂ}
    (h : herm (Hb k) s s * herm (Hb k) t t - herm (Hb k) s t * herm (Hb k) t s ≠ 0) :
    Module.finrank ℂ (Pz m s t) = k - 2 ∨ Module.finrank ℂ (Pz m s t) = k - 1 := by
  have hsurj : LinearMap.range (pair2 m s t) = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨x, y⟩
    set D := herm (Hb k) s s * herm (Hb k) t t - herm (Hb k) s t * herm (Hb k) t s with hD
    refine ⟨WithLp.toLp 2 (m⁻¹ *ᵥ (((x * herm (Hb k) t t - y * herm (Hb k) t s) / D) • s +
      ((y * herm (Hb k) s s - x * herm (Hb k) s t) / D) • t)), ?_⟩
    have hs : ∀ (c : ℂ) v w, herm (Hb k) (c • v) w = c * herm (Hb k) v w := fun c v w => by
      simp [herm, Matrix.mulVec_smul]
    simp only [pair2, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hm,
      Matrix.one_mulVec, herm_add_left, hs, Prod.mk.injEq]
    constructor <;> field_simp <;> rw [hD] <;> ring
  have h1 := LinearMap.finrank_range_add_finrank_ker (pair2 m s t)
  rw [hsurj] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker ((pair2 m s t).prod (EuclideanSpace.projₗ (Fin.last k)))
  have h3 := Submodule.finrank_le (LinearMap.range ((pair2 m s t).prod (EuclideanSpace.projₗ (Fin.last k))))
  have h4 : Module.finrank ℂ (Pz m s t) ≤ Module.finrank ℂ (LinearMap.ker (pair2 m s t)) := by
    apply Submodule.finrank_mono
    unfold Pz; rw [LinearMap.ker_prod]; exact inf_le_left
  simp only [finrank_top, Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace, Fintype.card_fin]
    at h1 h2 h3
  unfold Pz at *
  omega

theorem mem_pos (p : Fin (2 * r + k + 1) → ℂ) : p ∈ LinearMap.ker (Matrix.toLin' (Hpk k r - 1)) ↔
    rE k r p = rS k r p ∧ rW k r p (Fin.last k) = 0 := by
  rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero]
  constructor
  · intro h
    refine ⟨funext fun a => ?_, ?_⟩
    · have := congrFun h (esI k r a); rwa [besselHermForm_mulVec_dualIsotropicIndex] at this
    · have := congrFun h (wI k r (Fin.last k)); rw [H_w] at this
      simp only [sg, if_true] at this
      show p _ = 0
      linear_combination (-1 / 2 : ℂ) * this
  · rintro ⟨h1, h2⟩
    funext x
    induction x using cases3 with
    | h1 a => rw [H_e]; exact (congrFun h1 a).symm
    | h2 j =>
      rw [H_w]; unfold sg; split_ifs with h
      · subst h; have : p (wI k r (Fin.last k)) = 0 := h2
        simp [this]
      · simp
    | h3 a => rw [besselHermForm_mulVec_dualIsotropicIndex]; exact congrFun h1 a

theorem Yv_normal : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ), 2 ≤ k → TwoFl k r z z' g₀ → IsNormal k r β g₀ → ∀ m ∈ UH (Hb k), ∃ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), (Module.finrank ℂ P₀ = k - 2 ∨ Module.finrank ℂ P₀ = k - 1) ∧ ∀ (u : UT r → ℂ) (q : PPar k r) (a : Fin r → ℝ), (∀ b, 0 < a b) → Yv k r z z' g₀ (uEmb k r (upper u) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) = gramProj P₀ fun b => m⁻¹ *ᵥ q.1 b := by
  intro k r z z' g β _ ht hn m hm
  have hmu := unit_of_UH HbHb hm
  obtain ⟨hD, hC⟩ := Cm_det ht hn
  refine ⟨Pz m (rW k r z') (rW k r (g⁻¹ *ᵥ z)), finrank_Pz hmu (gram_ne ht hn), fun u q a ha => ?_⟩
  obtain ⟨-, -, hU, hup⟩ := GlobalTheory.Amp.UEmb.uEmb_hom k r
  set U := upper u with hUdef
  set A : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun b => (a b : ℂ) with hA
  have hUd : U.det = 1 := (hup u).1
  have hUu : IsUnit U.det := by rw [hUd]; exact isUnit_one
  have hAu : IsUnit A.det := by
    rw [hA, Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun b _ => Complex.ofReal_ne_zero.2 (ha b).ne'
  set x := uEmb k r U * pOf k r q * uEmb k r A * mEmb k r m with hx
  have hxu : IsUnit x.det := by
    simp only [hx, Matrix.det_mul]
    exact (((unit_of_UH HH (hU U hUu).1).mul (unit_of_UH HH (pEl_mem_UH _ _ (skewM_skew _ _)))).mul
      (unit_of_UH HH (hU A hAu).1)).mul (unit_of_UH HH (mEmb_mem m hm))
  have xS : ∀ v, rS k r (x *ᵥ v) = (U⁻¹)ᴴ *ᵥ ((A⁻¹)ᴴ *ᵥ rS k r v) := fun v => by
    simp only [hx, ← Matrix.mulVec_mulVec, pOf, rS_u, rS_p, rS_m]
  have xW : ∀ v, rW k r (x *ᵥ v) = m *ᵥ rW k r v + ∑ b, ((A⁻¹)ᴴ *ᵥ rS k r v) b • q.1 b := fun v => by
    simp only [hx, ← Matrix.mulVec_mulVec, pOf, rW_u, rW_p, rW_m, rS_u, rS_m]
  have hinv : ∀ M : Matrix (Fin r) (Fin r) ℂ, IsUnit M.det → ((M⁻¹)ᴴ).det ≠ 0 := fun M hM => by
    rw [Matrix.det_conjTranspose]
    exact star_ne_zero.2 (Matrix.isUnit_nonsing_inv_det M hM).ne_zero
  have hP : ∀ p, p ∈ Ppos k r z z' g x ↔ rE k r p.ofLp = 0 ∧ rS k r p.ofLp = 0 ∧
      WithLp.toLp 2 (rW k r p.ofLp) ∈ Pz m (rW k r z') (rW k r (g⁻¹ *ᵥ z)) := by
    intro p
    show (p.ofLp ∈ LinearMap.ker (Matrix.toLin' (Hpk k r - 1)) ∧
      Matrix.toLin' x p.ofLp ∈ Hcom k r z z' g ⊔ Xsp k r) ↔ _
    rw [mem_pos, Matrix.toLin'_apply, mem_sup hn hC, mem_Pz, xS, xW]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3, h4⟩
      have h5 := Matrix.eq_zero_of_mulVec_eq_zero (hinv A hAu)
        (Matrix.eq_zero_of_mulVec_eq_zero (hinv U hUu) h3)
      rw [h5] at h4 h1
      exact ⟨h1, h5, by simpa using h4, h2⟩
    · rintro ⟨h1, h2, h3, h4⟩
      rw [h1, h2]
      exact ⟨⟨rfl, h4⟩, by simp, by simpa using h3⟩
  set T : Matrix (Fin r) (Fin r) ℂ := -(Uᴴ * Cm k r g) with hT
  have hv : ∀ c, rW k r (x⁻¹ *ᵥ (g⁻¹ *ᵥ bvec (eI k r c))) = ∑ b, T b c • (m⁻¹ *ᵥ q.1 b) := by
    intro c
    set v := g⁻¹ *ᵥ bvec (eI k r c) with hv
    set y := x⁻¹ *ᵥ v with hy
    have hxy : x *ᵥ y = v := by
      rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hxu, Matrix.one_mulVec]
    have h1 := xS y
    have h2 := xW y
    rw [hxy] at h1 h2
    rw [(of_Xst (hn.2.1 c).1).2] at h2
    have h3 : (A⁻¹)ᴴ *ᵥ rS k r y = Uᴴ *ᵥ rS k r v := by
      rw [h1, Matrix.mulVec_mulVec, ← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hUu]
      simp
    have h4 : ∀ b, (Uᴴ *ᵥ rS k r v) b = -T b c := fun b => by
      simp [hT, Matrix.mul_apply, Matrix.mulVec, dotProduct, Cm, rS, hv]
    rw [h3] at h2
    have h5 : m *ᵥ rW k r y = ∑ b, T b c • q.1 b := by
      simp only [h4, neg_smul, Finset.sum_neg_distrib] at h2
      exact (eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; exact h2.symm))
    have h6 : rW k r y = m⁻¹ *ᵥ (m *ᵥ rW k r y) := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hmu, Matrix.one_mulVec]
    rw [h6, h5, Matrix.mulVec_sum]
    simp only [Matrix.mulVec_smul]
  have hTd : ‖T.det‖ = ‖(Cm k r g).det‖ := by
    rw [hT, Matrix.det_neg, Matrix.det_mul, Matrix.det_conjTranspose, hUd]
    simp
  unfold Yv
  rw [gramProj_mid _ _ hP]
  simp only [hv]
  rw [gramProj_comb, hTd, hD]
  have := norm_ne_zero_iff.2 hC
  field_simp

end GlobalTheory.Amp.NormGram
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TwoFlagsGramNumberNormalFormEqGramProjectionStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoFlagsGramNumber_normalForm_eq_gram_projection : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ), 2 ≤ k → TwoFl k r z z' g₀ → IsNormal k r β g₀ → ∀ m ∈ UH (Hb k), ∃ P₀ : Submodule ℂ (EuclideanSpace ℂ (Fin (k + 1))), (Module.finrank ℂ P₀ = k - 2 ∨ Module.finrank ℂ P₀ = k - 1) ∧ ∀ (u : UT r → ℂ) (q : PPar k r) (a : Fin r → ℝ), (∀ b, 0 < a b) → Yv k r z z' g₀ (uEmb k r (upper u) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) = gramProj P₀ fun b => m⁻¹ *ᵥ q.1 b := by
  first | exact @GlobalTheory.Amp.NormGram.Yv_normal | exact GlobalTheory.Amp.NormGram.Yv_normal | (intros; apply GlobalTheory.Amp.NormGram.Yv_normal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThreeBoxesVolumeProductLeExplicitPower
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThreeBoxesVolumeProductLeExplicitPower
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

theorem volume_product_le : ∀ (r : ℕ) (R₀ De : ℝ), 1 ≤ r → 1 ≤ R₀ → 1 ≤ De → (Real.pi * (R₀ ^ (2 * r) * De) ^ 2) ^ (r * (r - 1) / 2) * ((Real.pi * (r * R₀ ^ (4 * r - 2) * De ^ 2) ^ 2) ^ (r * (r - 1) / 2) * (2 * (r * R₀ ^ (4 * r - 2) * De ^ 2)) ^ r) * ((Real.pi * (r * R₀ ^ (2 * r - 1) * De) ^ 2) ^ (3 * r) * 4 * (r * R₀ ^ (2 * r - 1) * De) ^ (2 * r ^ 2 + 2 * r) * Real.pi ^ (r ^ 2)) ≤ (4 * r : ℝ) ^ (11 * r ^ 2) * R₀ ^ (20 * r ^ 3) * De ^ (12 * r ^ 2) := by
  intro r R₀ De hr hR hD
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hm : 2 * ((s + 1) * (s + 1 - 1) / 2) ≤ (s + 1) * s := by
    rw [Nat.add_sub_cancel]; omega
  generalize (s + 1) * (s + 1 - 1) / 2 = m at hm ⊢
  have e1 : 4 * (s + 1) - 2 = 4 * s + 2 := by omega
  have e2 : 2 * (s + 1) - 1 = 2 * s + 1 := by omega
  rw [e1, e2]
  have hx : (1 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by exact_mod_cast hr
  generalize ((s + 1 : ℕ) : ℝ) = x at hx ⊢
  have hpi : Real.pi ≤ 4 := Real.pi_le_four
  have hpi0 : 0 ≤ Real.pi := Real.pi_pos.le
  have h24 : (2 : ℝ) ≤ 4 := by norm_num
  have hms : 2 * m * s ≤ (s + 1) * s * s := Nat.mul_le_mul_right s hm
  calc _ ≤ ((4 : ℝ) * (R₀ ^ (2 * (s + 1)) * De) ^ 2) ^ m * ((4 * (x * R₀ ^ (4 * s + 2) * De ^ 2) ^ 2) ^ m * (4 * (x * R₀ ^ (4 * s + 2) * De ^ 2)) ^ (s + 1)) * ((4 * (x * R₀ ^ (2 * s + 1) * De) ^ 2) ^ (3 * (s + 1)) * 4 * (x * R₀ ^ (2 * s + 1) * De) ^ (2 * (s + 1) ^ 2 + 2 * (s + 1)) * 4 ^ ((s + 1) ^ 2)) := by
        gcongr
    _ = (4 : ℝ) ^ (2 * m + (s + 1) + 3 * (s + 1) + 1 + (s + 1) ^ 2) *
          x ^ (2 * m + (s + 1) + 6 * (s + 1) + (2 * (s + 1) ^ 2 + 2 * (s + 1))) *
          R₀ ^ (4 * (s + 1) * m + (4 * s + 2) * 2 * m + (4 * s + 2) * (s + 1) + (2 * s + 1) * 2 * (3 * (s + 1)) + (2 * s + 1) * (2 * (s + 1) ^ 2 + 2 * (s + 1))) *
          De ^ (6 * m + 2 * (s + 1) + 6 * (s + 1) + (2 * (s + 1) ^ 2 + 2 * (s + 1))) := by
        simp only [mul_pow, ← pow_mul]
        generalize (4 : ℝ) = c
        ring
    _ ≤ (4 : ℝ) ^ (11 * (s + 1) ^ 2) * x ^ (11 * (s + 1) ^ 2) * R₀ ^ (20 * (s + 1) ^ 3) * De ^ (12 * (s + 1) ^ 2) := by
        have h4 : (1 : ℝ) ≤ 4 := by norm_num
        gcongr
        · nlinarith [Nat.zero_le s, Nat.zero_le (s * s)]
        · nlinarith [Nat.zero_le s, Nat.zero_le (s * s)]
        · nlinarith [Nat.zero_le s, Nat.zero_le (s * s), Nat.zero_le (s * s * s)]
        · nlinarith [Nat.zero_le s, Nat.zero_le (s * s)]
    _ = _ := by rw [mul_pow]

end GlobalTheory.Amp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ThreeBoxesVolumeProductLeExplicitPowerStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.threeBoxesVolumeProduct_le_explicitPower : ∀ (r : ℕ) (R₀ De : ℝ), 1 ≤ r → 1 ≤ R₀ → 1 ≤ De → (Real.pi * (R₀ ^ (2 * r) * De) ^ 2) ^ (r * (r - 1) / 2) * ((Real.pi * (r * R₀ ^ (4 * r - 2) * De ^ 2) ^ 2) ^ (r * (r - 1) / 2) * (2 * (r * R₀ ^ (4 * r - 2) * De ^ 2)) ^ r) * ((Real.pi * (r * R₀ ^ (2 * r - 1) * De) ^ 2) ^ (3 * r) * 4 * (r * R₀ ^ (2 * r - 1) * De) ^ (2 * r ^ 2 + 2 * r) * Real.pi ^ (r ^ 2)) ≤ (4 * r : ℝ) ^ (11 * r ^ 2) * R₀ ^ (20 * r ^ 3) * De ^ (12 * r ^ 2) := by
  first | exact @GlobalTheory.Amp.volume_product_le | exact GlobalTheory.Amp.volume_product_le | (intros; apply GlobalTheory.Amp.volume_product_le <;> assumption)
end
end

section -- local restoration of offBlock_le
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.Amp.NfComp
open scoped InnerProductSpace ENNReal

private lemma exists_blockEnd_local {r : ℕ} {β : Fin r → ℕ} (hβ : Monotone β) (c : Fin r) :
    ∃ l, l ≤ r ∧ ∀ i : Fin r, i.val < l ↔ β i ≤ β c := by
  obtain ⟨d, hd, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun i : Fin r => β i ≤ β c) id
    ⟨c, by simp⟩
  refine ⟨d.val + 1, d.2, fun i => ⟨fun h => ?_, fun h => ?_⟩⟩
  · exact (hβ (show i ≤ d from Nat.le_of_lt_succ h)).trans (Finset.mem_filter.1 hd).2
  · exact Nat.lt_succ_of_le (hmax i (by simpa using h))

private lemma minor_ne_zero_local {r l : ℕ} (hl : l ≤ r) (Z : Matrix (Fin r) (Fin r) ℂ) (hZ : Z.det ≠ 0)
    (h : ∀ i : Fin r, ¬ i.val < l → ∀ j : Fin r, j.val < l → Z i j = 0) :
    (Z.submatrix (Fin.castLE hl) (Fin.castLE hl)).det ≠ 0 := by
  rw [Matrix.twoBlockTriangular_det Z (fun i => i.val < l) h] at hZ
  have h1 := left_ne_zero_of_mul hZ
  let e : Fin l ≃ {i : Fin r // i.val < l} :=
    ⟨fun i => ⟨Fin.castLE hl i, i.2⟩, fun i => ⟨i.1.val, i.2⟩, fun _ => rfl, fun _ => rfl⟩
  rw [← Matrix.det_submatrix_equiv_self e] at h1
  exact h1

private lemma Zr_mul_uEmb_local {k r : ℕ} (g : Mat k r) (u : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit u.det) :
    Zr k r (g * uEmb k r u) = Zr k r g * u := by
  ext a b
  have h := ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.1 u hu).2.2.1 b
  have h2 : Zr k r (g * uEmb k r u) a b = (g *ᵥ (uEmb k r u *ᵥ bvec (eI k r b))) (esI k r a) := by
    rw [Matrix.mulVec_mulVec]; simp [bvec, Zr]
  rw [h2, h, Matrix.mulVec_sum, Finset.sum_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp [bvec, Zr, Matrix.mulVec_smul, mul_comm]

private lemma N_sub_S_local {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, ⟨(uHGroup _ _ (Hunit k r)).1, by simp, by simp⟩, _, hn, (one_mul _).symm⟩

private theorem offBlock_le_local : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De R₀ : ℝ), TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → 1 ≤ R₀ → ∀ m ∈ UH (Hb k), ∀ (y : UToff β → ℂ) (q : PPar k r) (a : Fin r → ℝ), (∀ b, 0 < a b) → Sg k r z' (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) ≤ R₀ → Sg k r z (g₀ * (uEmb k r (upperOff β y) * pOf k r q * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) ≤ R₀ → ∀ p, ‖y p‖ ≤ R₀ ^ (2 * r) * De := by
  intro k r z z' g₀ β De R₀ hT hN hDe hR m hm y q a ha hS' hS p
  obtain ⟨hz, hz', -⟩ := hT
  obtain ⟨hg, -, hβ, hdet, hblk, -⟩ := hN
  obtain ⟨⟨⟨c, b⟩, hcb⟩, hβcb⟩ := p
  simp only at hcb hβcb
  obtain ⟨hg1, he⟩ := levi_diag_middle_mem_bessel_unitary_eucl (r := r) hm a ha
  have hU1 : (upperOff β y).det = 1 := ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.2 _).1
  have hUu : IsUnit (upperOff β y).det := by rw [hU1]; exact isUnit_one
  have hUN : uEmb k r (upperOff β y) ∈ Nset k r := ((GlobalTheory.Amp.UEmb.uEmb_hom k r).2.2.2 _).2
  have hPN : pOf k r q ∈ Nset k r :=
    (((GlobalTheory.Amp.Rad.radical k r).1 _ _).2.2.2 ((GlobalTheory.Amp.Rad.radical k r).2.1 _ _)).1
  have hPe : ∀ d : Fin r, pOf k r q *ᵥ bvec (eI k r d) = bvec (eI k r d) := ((GlobalTheory.Amp.Rad.radical k r).1 _ _).1
  have hs : uEmb k r (upperOff β y) * pOf k r q ∈ Nset k r := (nSubgroup k r).2.1 _ hUN _ hPN
  rw [Matrix.mul_assoc (uEmb k r (upperOff β y) * pOf k r q)] at hS hS'
  have hlen : ∀ d : Fin r, (a d)⁻¹ ≤ R₀ := by
    intro d
    have h1 := (((GlobalTheory.Amp.LInv.lengths_basic k r z' hz').1 _ hg1 _ (N_sub_S_local z' hs) 1
      ⟨(uHGroup _ _ (Hunit k r)).1, one_mem _⟩).1 d.castSucc)
    rw [mul_one, (GlobalTheory.Amp.LInv.lengths_basic k r z' hz').2.1 a ha m hm] at h1
    rw [← h1]
    exact ((((GlobalTheory.Amp.LInv.lengths_basic k r z' hz').2.2 _).2.1 _).2).trans hS'
  set g₁ := uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m with hg₁
  set U := upperOff β y with hU
  obtain ⟨l, hl, hlβ⟩ := exists_blockEnd_local hβ c
  have hcl : c.val < l := (hlβ c).2 le_rfl
  have hZ0 : ∀ i j : Fin r, (i.val < l ↔ ¬ j.val < l) → Zr k r g₀ i j = 0 := by
    intro i j hij
    by_contra h
    have := hblk i j h
    rw [hlβ, hlβ, this] at hij
    tauto
  have hcr := Formalism.HermitianLatticeCounting.Final.LatticeSumBounds.cramerUpper ℂ r l hl 1 (Zr k r g₀) U (by simp)
    (fun i j h => Matrix.one_apply_ne h.ne) (fun i => by simp [hU, upperOff, upper])
    (fun i j h => by
      simp only [hU, upperOff, upper]
      rw [dite_eq_right (not_lt.2 h.le), if_neg h.ne'])
    (fun i j hi hj => hZ0 i j ⟨fun _ => not_lt.2 hj, fun _ => hi⟩) ⟨c.val, hcl⟩ b
    (fun c' hc' => by
      by_contra h
      rcases upperOff_ne hβ y _ _ h with h' | h'
      · exact hc'.ne (Fin.castLE_injective hl h')
      · exact absurd ((hlβ (Fin.castLE hl c')).1 c'.2) (not_le.2 h'))
  have hUcb : U (Fin.castLE hl ⟨c.val, hcl⟩) b = y ⟨⟨(c, b), hcb⟩, hβcb⟩ := by
    show upperOff β y c b = _
    simp only [upperOff, upper]
    rw [dite_eq_left hcb, dite_eq_left hβcb]
  rw [Matrix.one_mul, hUcb, ← Zr_mul_uEmb_local g₀ U hUu] at hcr
  have hD1 : ((Zr k r (g₀ * uEmb k r U)).submatrix (Fin.castLE hl) (Fin.castLE hl)).det =
      Dmin k r z z' g₀ ⟨l, by omega⟩ := by
    have h1 := dInv k r z z' hz hz' 1 (N_sub_S_local z (nSubgroup k r).1) _ (N_sub_S_local z' hUN) g₀ ⟨l, by omega⟩
    rw [Matrix.one_mul] at h1
    rw [← h1, Dmin_eq le_rfl z z' _ l hl]
    rfl
  have hD0 : Dmin k r z z' g₀ ⟨l, by omega⟩ ≠ 0 := by
    rw [Dmin_eq le_rfl z z' _ l hl]
    exact minor_ne_zero_local hl _ hdet fun i hi j hj => hZ0 i j ⟨fun h => absurd h hi, fun h => absurd hj h⟩
  have hDb := hDe.2 ⟨l, by omega⟩ hl hD0
  rw [hD1] at hcr
  set σ : Fin l → Fin r := fun j => if j = ⟨c.val, hcl⟩ then b else Fin.castLE hl j with hσ
  have hx := G_mul hg (G_mul hs.1 hg1)
  have hp := pluck_flag hl z hz _ hx R₀ hS (fun i => g₁⁻¹ *ᵥ bvec (eI k r (σ i))) (fun i => by
    rw [he]; exact hlen _)
  have hmat : (Matrix.of fun i i' : Fin l =>
      herm (Hpk k r) ((g₀ * (uEmb k r U * pOf k r q * g₁))⁻¹ *ᵥ bvec (eI k r (Fin.castLE hl i')))
        (g₁⁻¹ *ᵥ bvec (eI k r (σ i)))) = ((Zr k r (g₀ * uEmb k r U)).submatrix (Fin.castLE hl) σ)ᴴ := by
    ext i i'
    rw [Matrix.of_apply, herm_inv_left hx, herm_symm, herm_e, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (G_unit hg1), Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mulVec_mulVec, hPe]
    simp [bvec, Zr]
  rw [hmat, Matrix.det_conjTranspose, norm_star, hcr, norm_mul] at hp
  have hP0 : 0 < ‖Dmin k r z z' g₀ ⟨l, by omega⟩‖ := norm_pos_iff.2 hD0
  have hpow : R₀ ^ l * R₀ ^ l ≤ R₀ ^ (2 * r) := by
    rw [← pow_add]; exact pow_le_pow_right₀ hR (by omega)
  calc _ ≤ R₀ ^ (2 * r) * ‖Dmin k r z z' g₀ ⟨l, by omega⟩‖⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀' hP0]; exact hp.trans hpow
    _ ≤ _ := mul_le_mul_of_nonneg_left hDb (by positivity)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreGramNumberNullAndCutoffIntegralBound
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.FibNf

theorem card_UT (r : ℕ) : Fintype.card (UT r) = r * (r - 1) / 2 := by
  rw [Fintype.card_subtype, ← Nat.choose_two_right]
  have := Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin r)))
  simpa using this

theorem vol_polydisc (ι : Type) [Fintype ι] {R : ℝ} (hR : 0 ≤ R) :
    volume {y : ι → ℂ | ∀ p, ‖y p‖ ≤ R} = ENNReal.ofReal ((Real.pi * R ^ 2) ^ Fintype.card ι) := by
  have h : {y : ι → ℂ | ∀ p, ‖y p‖ ≤ R} = Set.pi Set.univ fun _ => Metric.closedBall (0 : ℂ) R := by
    ext y; simp
  rw [h, volume_pi_pi]
  simp only [Complex.volume_closedBall, Finset.prod_const, Finset.card_univ]
  rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hR, mul_comm]
  congr 2
  rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]

theorem vol_cube (r : ℕ) {R : ℝ} (hR : 0 ≤ R) :
    volume {y : Fin r → ℝ | ∀ p, |y p| ≤ R} = ENNReal.ofReal ((2 * R) ^ r) := by
  have h : {y : Fin r → ℝ | ∀ p, |y p| ≤ R} = Set.pi Set.univ fun _ => Metric.closedBall (0 : ℝ) R := by
    ext y; simp
  rw [h, volume_pi_pi]
  simp only [Real.volume_closedBall, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [ENNReal.ofReal_pow (by positivity)]

theorem sfinite_PPar (k r : ℕ) : SFinite (volume : Measure (PPar k r)) := by
  have : SFinite (volume : Measure (Fin r → Fin (k + 1) → ℂ)) := inferInstance
  have : SFinite (volume : Measure ((UT r → ℂ) × (Fin r → ℝ))) := inferInstance
  infer_instance

theorem vol_PPar (k r : ℕ) (S : Set (Fin r → Fin (k + 1) → ℂ)) (T : Set (UT r → ℂ)) (U : Set (Fin r → ℝ)) :
    (volume : Measure (PPar k r)) (S ×ˢ (T ×ˢ U)) = volume S * (volume T * volume U) := by
  rw [Measure.volume_eq_prod, Measure.prod_prod, Measure.volume_eq_prod, Measure.prod_prod]

theorem coords_upper {r : ℕ} (u : UT r → ℂ) : USplit.coords (upper u) = u := by
  funext p
  exact USplit.upper_of_lt u p.2

theorem measurable_coord (k r : ℕ) : Measurable fun q : (UT r → ℂ) × PPar k r =>
    (Matrix.of.symm (uEmb k r (upper q.1) * pOf k r q.2) : Mt k r) :=
  (show Continuous fun q : (UT r → ℂ) × PPar k r =>
    (Matrix.of.symm (uEmb k r (upper q.1) * pOf k r q.2) : Mt k r) from (NCoord.coord_homeo k r).2.1).measurable

theorem coord_mem (k r : ℕ) (u : UT r → ℂ) (q : PPar k r) : uEmb k r (upper u) * pOf k r q ∈ Nset k r := by
  have := (NCoord.coord_homeo k r).1.mapsTo (Set.mem_univ (u, q))
  simpa only using this

theorem coord_off_mem (k r : ℕ) (β : Fin r → ℕ) (y : UToff β → ℂ) (q : PPar k r) :
    uEmb k r (upperOff β y) * pOf k r q ∈ Nset k r := by
  unfold upperOff
  exact coord_mem k r _ q

theorem cut_le {k r : ℕ} {β : Fin r → ℕ} (φ : Mt k r → ℝ≥0∞) (hφ : SubCut (Nset k r) (lebR k r β) φ)
    (n : Mat k r) (hN : n ∈ Nset k r) :
    ∫⁻ x : UTin β → ℂ, φ (Matrix.of.symm (uEmb k r (upperIn β x) * n)) ≤ 1 := by
  have h1 := hφ.2 (Matrix.of.symm n) hN
  have hl : Measurable fun ρ : Mt k r => φ (lmulM (Matrix.of ρ) (Matrix.of.symm n : Mt k r)) :=
    hφ.1.comp (continuous_rmulM n).measurable
  have hi : Measurable fun x : UTin β → ℂ => (Matrix.of.symm (uEmb k r (upperIn β x)) : Mt k r) := by
    have : Continuous fun x : UTin β → ℂ => uEmb k r (upperIn β x) := by
      unfold upperIn
      refine (NCoord.cont_uEmb k r).comp (continuous_pi fun p => ?_)
      split_ifs
      · exact continuous_apply _
      · exact continuous_const
    exact Continuous.measurable (γ := Mt k r) this
  unfold lebR at h1
  rw [lintegral_map hl hi] at h1
  exact h1

theorem lintegral_le {k r : ℕ} {β : Fin r → ℕ} (hβ : Monotone β) (φ : Mt k r → ℝ≥0∞)
    (hφ : SubCut (Nset k r) (lebR k r β) φ) (E : Set (Mt k r)) (hE : MeasurableSet E)
    (A : Set (UToff β → ℂ)) (B : Set (PPar k r))
    (h : ∀ x y q, (Matrix.of.symm (uEmb k r (upperIn β x) * (uEmb k r (upperOff β y) * pOf k r q)) : Mt k r) ∈ E →
      y ∈ A ∧ q ∈ B) :
    ∫⁻ n, φ n * E.indicator 1 n ∂(lebN k r) ≤ volume A * volume B := by
  have hm : Measurable fun n => φ n * E.indicator 1 n := hφ.1.mul (measurable_one.indicator hE)
  have hF := measurable_coord k r
  have := sfinite_PPar k r
  unfold lebN
  rw [lintegral_map hm hF, Measure.volume_eq_prod]
  refine le_trans (lintegral_prod_symm' _ (hm.comp hF)).le ?_
  refine le_trans (lintegral_mono fun q => ?_) (lintegral_indicator_const_le B (volume A))
  have hc : Measurable fun U : Fin r → Fin r → ℂ => USplit.coords (Matrix.of U) :=
    measurable_pi_iff.2 fun p => (measurable_pi_apply p.1.2).comp (measurable_pi_apply p.1.1)
  have hs := (USplit.lebesgue_split r β hβ).2 _ ((hm.comp hF).comp (hc.prodMk (measurable_const (a := q))))
  simp only [Function.comp_apply, Equiv.apply_symm_apply, coords_upper] at hs
  have hp : ∀ x y, uEmb k r (upper (USplit.coords (upperIn β x * upperOff β y))) * pOf k r q =
      uEmb k r (upperIn β x) * (uEmb k r (upperOff β y) * pOf k r q) := by
    intro x y
    have : upper (USplit.coords (upperIn β x * upperOff β y)) = upperIn β x * upperOff β y :=
      USplit.upper_coords_mul _ _
    rw [this, UEmb.uEmb_mul, Matrix.mul_assoc]
  simp only [hp] at hs
  simp only [Function.comp_apply]
  rw [hs]
  have key : ∀ y, ∫⁻ x : UTin β → ℂ,
      φ (Matrix.of.symm (uEmb k r (upperIn β x) * (uEmb k r (upperOff β y) * pOf k r q))) *
        E.indicator 1 (Matrix.of.symm (uEmb k r (upperIn β x) * (uEmb k r (upperOff β y) * pOf k r q)) : Mt k r) ≤
      A.indicator (fun _ => B.indicator 1 q) y := by
    intro y
    by_cases hy : y ∈ A ∧ q ∈ B
    · rw [Set.indicator_of_mem hy.1, Set.indicator_of_mem hy.2]
      refine le_trans (lintegral_mono fun x => ?_) (cut_le φ hφ _ (coord_off_mem k r β y q))
      exact mul_le_of_le_one_right' (Set.indicator_le_self' (fun _ _ => zero_le) _)
    · refine le_trans (le_of_eq ?_) zero_le
      have : ∀ x : UTin β → ℂ, E.indicator (1 : Mt k r → ℝ≥0∞)
          (Matrix.of.symm (uEmb k r (upperIn β x) * (uEmb k r (upperOff β y) * pOf k r q)) : Mt k r) = 0 :=
        fun x => Set.indicator_of_notMem (fun hx => hy (h x y q hx)) _
      simp only [this, mul_zero, lintegral_zero]
  refine le_trans (lintegral_mono key) (le_trans (lintegral_indicator_const_le A _) (le_of_eq ?_))
  by_cases hq : q ∈ B <;> simp [hq]

theorem arith {a b c d e f g : ℝ} (hpos : 0 ≤ e * f) (har : a * (b * c) * d ≤ g) :
    a * (d * e * f * (b * c)) ≤ g * e * f := by
  have := mul_le_mul_of_nonneg_right har hpos
  refine le_trans (le_of_eq ?_) (le_trans this (le_of_eq ?_)) <;> ring

theorem null_of {k r : ℕ} (Z : Set (Mt k r)) (hZ : MeasurableSet Z) (S : Set (Fin r → Fin (k + 1) → ℂ))
    (hS : volume S = 0)
    (h : ∀ u q, (Matrix.of.symm (uEmb k r (upper u) * pOf k r q) : Mt k r) ∈ Z → q.1 ∈ S) : lebN k r Z = 0 := by
  have := sfinite_PPar k r
  unfold lebN
  rw [Measure.map_apply (measurable_coord k r) hZ]
  refine measure_mono_null (t := Set.univ ×ˢ (S ×ˢ (Set.univ ×ˢ Set.univ))) (fun q hq => ?_) ?_
  · exact ⟨trivial, h q.1 q.2 hq, trivial, trivial⟩
  · rw [Measure.volume_eq_prod, Measure.prod_prod, vol_PPar, hS, zero_mul, mul_zero]

theorem mem_of_mul {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {g₀ ρ x : Mat k r} {R₀ y : ℝ}
    (hz : inWb k r z) (hz' : inWb k r z') (hg : g₀ ∈ GG k r) (hρ : ρ ∈ Rset k r g₀) (hx0 : x ∈ GG k r)
    (hx : (Matrix.of.symm (ρ * x) : Mt k r) ∈ Eset k r z z' g₀ R₀ y) :
    Sg k r z' x ≤ R₀ ∧ Sg k r z (g₀ * x) ≤ R₀ ∧ y < Yv k r z z' g₀ x ∧ Yv k r z z' g₀ x ≤ 2 * y := by
  have hx' : Sg k r z' (ρ * x) ≤ R₀ ∧ Sg k r z (g₀ * (ρ * x)) ≤ R₀ ∧ y < Yv k r z z' g₀ (ρ * x) ∧
      Yv k r z z' g₀ (ρ * x) ≤ 2 * y := hx.2
  have h1 : (1 : Mat k r) ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))) :=
    ⟨(nSubgroup k r).1.1, one_mem _⟩
  have e1 := ((LInv.lengths_basic k r z' hz').1 _ hx0 _ (YInv.N_sub_S z' hρ.1) 1 h1).2
  have e2 := ((LInv.lengths_basic k r z hz).1 _ (YInv.mul_mem hg hx0) _ (YInv.N_sub_S z hρ.2) 1 h1).2
  have e3 := (YInv.yv_invariant k r z z' g₀ hz hz' hg _ hx0).2.2 _ hρ
  rw [Matrix.mul_one] at e1 e2
  rw [Matrix.mul_assoc _ g₀⁻¹, ← Matrix.mul_assoc g₀⁻¹, Matrix.nonsing_inv_mul _ (YInv.det_unit hg),
    Matrix.one_mul, Matrix.mul_assoc g₀] at e2
  rwa [e1, e2, e3] at hx'

theorem vol_bound {k r : ℕ} (β : Fin r → ℕ) {R₀ De y : ℝ} (hr : 1 ≤ r) (hR : 1 ≤ R₀) (h1De : 1 ≤ De) (hy : 0 < y)
    (S : Set (Fin r → Fin (k + 1) → ℂ))
    (hS : volume S ≤ ENNReal.ofReal ((Real.pi * (r * R₀ ^ (2 * r - 1) * De) ^ 2) ^ (3 * r) * 4 *
      (r * R₀ ^ (2 * r - 1) * De) ^ (2 * r ^ 2 + 2 * r) * Real.pi ^ (r ^ 2) *
      (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) * (2 * y) ^ (2 * (k - 2 - r)))) :
    volume {y : UToff β → ℂ | ∀ p, ‖y p‖ ≤ R₀ ^ (2 * r) * De} *
      (volume : Measure (PPar k r)) (S ×ˢ ({s : UT r → ℂ | ∀ p, ‖s p‖ ≤ r * R₀ ^ (4 * r - 2) * De ^ 2} ×ˢ
          {t : Fin r → ℝ | ∀ p, |t p| ≤ r * R₀ ^ (4 * r - 2) * De ^ 2})) ≤ ENNReal.ofReal (fibVol k r R₀ De y) := by
  have hR1 : 1 ≤ R₀ ^ (2 * r) * De := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hR) h1De
  have hR3 : 0 ≤ r * R₀ ^ (4 * r - 2) * De ^ 2 := by positivity
  rw [vol_PPar, vol_polydisc _ (zero_le_one.trans hR1), vol_polydisc _ hR3, vol_cube _ hR3, card_UT]
  have hcard : Fintype.card (UToff β) ≤ r * (r - 1) / 2 := card_UT r ▸ Fintype.card_subtype_le _
  have hb : 1 ≤ Real.pi * (R₀ ^ (2 * r) * De) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (by linarith [Real.pi_gt_three]) (one_le_pow₀ hR1)
  refine le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (pow_le_pow_right₀ hb hcard))
    (mul_le_mul' hS le_rfl)) ?_
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have har := GlobalTheory.T.threeBoxesVolumeProduct_le_explicitPower r R₀ De hr hR h1De
  have hpos : 0 ≤ (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) *
    (2 * y) ^ (2 * (k - 2 - r)) := by positivity
  unfold fibVol
  exact arith hpos har

theorem fibre_bound : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De : ℝ), 1 ≤ r → 2 * r + 6 ≤ k → TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → ∀ m ∈ UH (Hb k), ∀ a : Fin r → ℝ, (∀ b, 0 < a b) → lebN k r {n | Yv k r z z' g₀ (Matrix.of n * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) = 0} = 0 ∧ ∀ φ, SubCut (Nset k r) (lebR k r β) φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ n * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol k r R₀ De y) := by
  intro k r z z' g₀ β De hr hk hT hN hD m hm a ha
  obtain ⟨P₀, hP₀, hY⟩ := GlobalTheory.T.twoFlagsGramNumber_normalForm_eq_gram_projection k r z z' g₀ β (by omega) hT hN m hm
  obtain ⟨hV0, hV⟩ := GlobalTheory.T.volume_gramCondition_codim_two_three k r hr hk m hm P₀ hP₀
  obtain ⟨hM1, hM2⟩ := GlobalTheory.T.twoFlagsGramNumber_and_fibre_sets_measurable k r z z' g₀ hN.1
  have hU := fun R₀ hR => offBlock_le_local k r z z' g₀ β De R₀ hT hN hD hR m hm
  have hB := fun R₀ hR => GlobalTheory.T.radical_coordinates_bounded_majorant_lengths k r z z' g₀ β De R₀ hT hN hD hR m hm
  have hdG : uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) ∈ GG k r := by
    apply UEmb.uEmb_mem
    rw [Matrix.det_diagonal, isUnit_iff_ne_zero]
    exact Finset.prod_ne_zero_iff.2 fun b _ => by exact_mod_cast (ha b).ne'
  have hmG : mEmb k r m ∈ GG k r := Rad.mEmb_mem m hm
  have hNq := coord_mem k r
  have hY' := fun u q => hY u q a ha
  have hU' := fun R₀ hR w q => hU R₀ hR w q a ha
  have hB' := fun R₀ hR w q => hB R₀ hR w q a ha
  have hcG := YInv.mul_mem hdG hmG
  simp only [Matrix.mul_assoc _ (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)))] at hY' hU' hB'
  clear hY hU hB
  generalize uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m = c at *
  have hrm : Measurable (rmulM c) := (continuous_rmulM c).measurable
  constructor
  · have hZ : MeasurableSet ((Set.indicator {x : Mt k r | Matrix.of x ∈ GG k r}
        (fun x => Yv k r z z' g₀ (Matrix.of x)) ∘ rmulM c) ⁻¹' {0}) := (hM1.comp hrm) (measurableSet_singleton 0)
    refine measure_mono_null (fun n hn => ?_) (null_of _ hZ _ hV0 fun u q hq => ?_)
    · exact Set.indicator_apply_eq_zero.2 fun _ => hn
    · have := Set.indicator_apply_eq_zero.1 hq (YInv.mul_mem (hNq u q).1 hcG)
      exact (hY' u q).symm.trans this
  · intro φ hφ R₀ y hR hy
    have h1De : 1 ≤ De := hD.1
    have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have hR2 : 1 ≤ r * R₀ ^ (2 * r - 1) * De :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hr' (one_le_pow₀ hR)) h1De
    refine le_trans ?_ (vol_bound β hr hR h1De hy _ (hV _ y hR2 hy))
    refine le_trans (le_of_eq ?_) (lintegral_le hN.2.2.1 φ hφ (rmulM c ⁻¹' Eset k r z z' g₀ R₀ y) (hrm (hM2 R₀ y)) _ _ ?_)
    · refine lintegral_congr fun n => ?_
      congr 1
    · intro x w q hx
      have hρ : uEmb k r (upperIn β x) ∈ Rset k r g₀ := by
        rw [(GlobalTheory.T.commonStabilizer_normalForm_blockUnitriangular k r g₀ β hN).1]; exact ⟨x, rfl⟩
      have hn0 : uEmb k r (upperOff β w) * pOf k r q ∈ Nset k r := coord_off_mem k r β w q
      have hx0 : uEmb k r (upperOff β w) * pOf k r q * c ∈ GG k r := YInv.mul_mem hn0.1 hcG
      have hx1 : (Matrix.of.symm (uEmb k r (upperIn β x) * (uEmb k r (upperOff β w) * pOf k r q * c)) : Mt k r) ∈
          Eset k r z z' g₀ R₀ y := by
        rw [← Matrix.mul_assoc]; exact hx
      obtain ⟨s1, s2, s3, s4⟩ := mem_of_mul hT.1 hT.2.1 hN.1 hρ hx0 hx1
      have e4 : Yv k r z z' g₀ (uEmb k r (upperOff β w) * pOf k r q * c) = gramProj P₀ fun b => m⁻¹ *ᵥ q.1 b := by
        unfold upperOff
        exact hY' _ q
      rw [e4] at s3 s4
      obtain ⟨b1, b2, b3⟩ := hB' R₀ hR w q s1 s2
      exact ⟨hU' R₀ hR w q s1 s2, ⟨b1, s3, s4⟩, b2, b3⟩

end GlobalTheory.Amp.FibNf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FibreGramNumberNullAndCutoffIntegralBoundStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_gramNumber_null_and_cutoff_integral_bound : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g₀ : Mat k r) (β : Fin r → ℕ) (De : ℝ), 1 ≤ r → 2 * r + 6 ≤ k → TwoFl k r z z' g₀ → IsNormal k r β g₀ → DeOK k r z z' g₀ De → ∀ m ∈ UH (Hb k), ∀ a : Fin r → ℝ, (∀ b, 0 < a b) → lebN k r {n | Yv k r z z' g₀ (Matrix.of n * (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m)) = 0} = 0 ∧ ∀ φ, SubCut (Nset k r) (lebR k r β) φ → ∀ R₀ y : ℝ, 1 ≤ R₀ → 0 < y → ∫⁻ n, φ n * (Eset k r z z' g₀ R₀ y).indicator 1 (rmulM (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) n) ∂(lebN k r) ≤ ENNReal.ofReal (fibVol k r R₀ De y) := by
  first | exact @GlobalTheory.Amp.FibNf.fibre_bound | exact GlobalTheory.Amp.FibNf.fibre_bound | (intros; apply GlobalTheory.Amp.FibNf.fibre_bound <;> assumption)
end
