module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NChartP

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXECPfC
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXECPfB
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXECPfA
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXEC
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

def ExpChart : Prop :=
  ∀ k r : ℕ, Formalism.MainNotions.S.haarLie (Formalism.QuantumDeterminants.Nset k r) 1 =
    ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k)) •
      (volume : Measure ((WlocSk.NB.CI k r → ℂ) × (Fin r → ℝ))).map (fun t => WlocSk.NB.phi0 t.1 t.2)

end Formalism.L2.SG.Pf.NcReal.JX
end
end

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.EC

open Formalism.QuantumDeterminants WlocSk.NB
open Formalism.MainNotions.BridgeCSB (Fil lieN adjH adjH_apply dg)

variable {k r : ℕ}

abbrev J (k r : ℕ) := (CI k r ⊕ CI k r) ⊕ Fin r

def toC (y : J k r → ℝ) : (CI k r → ℂ) × (Fin r → ℝ) :=
  (fun i => ⟨y (Sum.inl (Sum.inl i)), y (Sum.inl (Sum.inr i))⟩, fun a => y (Sum.inr a))

def Lm (t : (CI k r → ℂ) × (Fin r → ℝ)) : Mx k r :=
  mkM (cA t.1 - 1) (cB t.1) (cK t.1 t.2) (-(dD k * (cB t.1)ᴴ)) (-(cA t.1 - 1)ᴴ) - mkM 0 0 0 0 0

def ShearStep : Prop := ∀ k r : ℕ, ∃ σ : (J k r → ℝ) → (CI k r → ℂ) × (Fin r → ℝ),
  MeasurePreserving σ volume volume ∧ ∀ y, phi0 (σ y).1 (σ y).2 = NormedSpace.exp (Lm (toC y))

def ConstStep : Prop := ∀ k r : ℕ, ∃ Λ : (J k r → ℝ) → Formalism.MainNotions.S.lieE (Nset k r), Measurable Λ ∧
  (∀ y, ((Λ y : Formalism.MainNotions.S.lieE (Nset k r)) : EuclideanSpace ℝ _) = Formalism.MainNotions.BridgeCSB.RL (k := k) (r := r) (Lm (toC y))) ∧
  (volume : Measure (Formalism.MainNotions.S.lieE (Nset k r))) = ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k)) • volume.map Λ

theorem dg_eI (a : Fin r) : dg k r (eI k r a) = a.val := by
  have := a.isLt; unfold dg eI; simp only; split_ifs <;> omega
theorem dg_wI (j : Fin (k + 1)) : dg k r (wI k r j) = r := by
  have := j.isLt; unfold dg wI; simp only; split_ifs <;> omega
theorem dg_esI (a : Fin r) : dg k r (esI k r a) = 2 * r - a.val := by
  have := a.isLt; unfold dg esI; simp only; split_ifs <;> omega

theorem gtau_eI (a : Fin r) : Formalism.QuantumDeterminants.WeylGroupFacts.tau k r (eI k r a) = esI k r a := by
  unfold Formalism.QuantumDeterminants.WeylGroupFacts.tau eI esI; apply Fin.ext; simp only; split_ifs <;> omega
theorem gtau_esI (a : Fin r) : Formalism.QuantumDeterminants.WeylGroupFacts.tau k r (esI k r a) = eI k r a := by
  unfold Formalism.QuantumDeterminants.WeylGroupFacts.tau eI esI; apply Fin.ext; simp only; split_ifs <;> omega
theorem gtau_wI (j : Fin (k + 1)) : Formalism.QuantumDeterminants.WeylGroupFacts.tau k r (wI k r j) = wI k r j := by
  unfold Formalism.QuantumDeterminants.WeylGroupFacts.tau wI; apply Fin.ext; simp only; split_ifs <;> omega
theorem gsgn_eI (a : Fin r) : Formalism.QuantumDeterminants.WeylGroupFacts.sgn k r (eI k r a) = 1 := by
  unfold Formalism.QuantumDeterminants.WeylGroupFacts.sgn eI; simp only; split_ifs <;> first | rfl | omega
theorem gsgn_esI (a : Fin r) : Formalism.QuantumDeterminants.WeylGroupFacts.sgn k r (esI k r a) = 1 := by
  unfold Formalism.QuantumDeterminants.WeylGroupFacts.sgn esI; simp only; split_ifs <;> first | rfl | omega
theorem gsgn_wI (j : Fin (k + 1)) : Formalism.QuantumDeterminants.WeylGroupFacts.sgn k r (wI k r j) = dD k j j := by
  unfold Formalism.QuantumDeterminants.WeylGroupFacts.sgn wI dD
  simp only [Matrix.diagonal_apply_eq]
  split_ifs <;> first | rfl | omega

theorem dD_star (j : Fin (k + 1)) : star (dD k j j) = dD k j j := by
  simp only [dD, Matrix.diagonal_apply_eq]; split_ifs <;> simp
theorem dD_sq' (j : Fin (k + 1)) : dD k j j * dD k j j = 1 := by
  simp only [dD, Matrix.diagonal_apply_eq]; split_ifs <;> simp

theorem chart_matrix_lower (x : CI k r → ℂ) {a b : Fin r} (h : b ≤ a) : (cA x - 1) a b = 0 := by
  rw [Matrix.sub_apply, Matrix.one_apply]; unfold cA; rw [dite_eq_right (not_lt.2 h)]; split_ifs <;> simp

theorem chart_matrix_upper (x : CI k r → ℂ) {a b : Fin r} (h : a < b) : (cA x - 1) a b = x (Sum.inl ⟨(a, b), h⟩) := by
  rw [Matrix.sub_apply, Matrix.one_apply, if_neg (ne_of_lt h)]; unfold cA; rw [dite_eq_left h, sub_zero]

theorem cK_skew (x : CI k r → ℂ) (s : Fin r → ℝ) (a b : Fin r) : cK x s a b + star (cK x s b a) = 0 := by
  unfold cK
  rcases lt_trichotomy a b with h | h | h
  · rw [dite_eq_left h, dite_eq_right (not_lt.2 h.le), dite_eq_left h, star_neg, star_star, add_neg_cancel]
  · subst h
    rw [dite_eq_right (lt_irrefl _), dite_eq_right (lt_irrefl _), star_mul', Complex.star_def,
      Complex.conj_ofReal, Complex.conj_I]
    ring
  · rw [dite_eq_right (not_lt.2 h.le), dite_eq_left h, dite_eq_left h, neg_add_cancel]

section entries

variable (t : (CI k r → ℂ) × (Fin r → ℝ))

@[simp] theorem Lm_ee (a b : Fin r) : Lm t (eI k r a) (eI k r b) = (cA t.1 - 1) a b := by
  simp only [Lm, Matrix.sub_apply, mk_ee, Matrix.zero_apply, sub_zero]
@[simp] theorem Lm_ew (a : Fin r) (j : Fin (k + 1)) : Lm t (eI k r a) (wI k r j) = cB t.1 a j := by
  simp only [Lm, Matrix.sub_apply, mk_ew, Matrix.zero_apply, sub_zero]
@[simp] theorem Lm_es (a b : Fin r) : Lm t (eI k r a) (esI k r b) = cK t.1 t.2 a b := by
  simp only [Lm, Matrix.sub_apply, mk_es, Matrix.zero_apply, sub_zero]
@[simp] theorem Lm_we (j : Fin (k + 1)) (b : Fin r) : Lm t (wI k r j) (eI k r b) = 0 := by
  simp only [Lm, Matrix.sub_apply, mk_we, sub_zero]
@[simp] theorem Lm_ww (j c : Fin (k + 1)) : Lm t (wI k r j) (wI k r c) = 0 := by
  simp only [Lm, Matrix.sub_apply, mk_ww, sub_self]
@[simp] theorem Lm_ws (j : Fin (k + 1)) (b : Fin r) :
    Lm t (wI k r j) (esI k r b) = -(dD k j j * star (cB t.1 b j)) := by
  simp only [Lm, Matrix.sub_apply, mk_ws, Matrix.zero_apply, sub_zero, Matrix.neg_apply, dD_mul_apply,
    conjTranspose_apply]
@[simp] theorem Lm_se (a b : Fin r) : Lm t (esI k r a) (eI k r b) = 0 := by
  simp only [Lm, Matrix.sub_apply, mk_se, sub_zero]
@[simp] theorem Lm_sw (a : Fin r) (j : Fin (k + 1)) : Lm t (esI k r a) (wI k r j) = 0 := by
  simp only [Lm, Matrix.sub_apply, mk_sw, sub_zero]
@[simp] theorem Lm_ss (a b : Fin r) : Lm t (esI k r a) (esI k r b) = -star ((cA t.1 - 1) b a) := by
  simp only [Lm, Matrix.sub_apply, mk_ss, Matrix.zero_apply, sub_zero, Matrix.neg_apply, conjTranspose_apply]

end entries

theorem chart_filtration_one (t : (CI k r → ℂ) × (Fin r → ℝ)) : Fil 1 (Lm t) := by
  intro i j h
  obtain ⟨p, rfl⟩ := (posE k r).surjective i
  obtain ⟨q, rfl⟩ := (posE k r).surjective j
  rcases p with a | c | a <;> rcases q with b | c' | b <;>
    simp only [posE_apply, pos, dg_eI, dg_wI, dg_esI] at h <;>
    simp only [posE_apply, pos, Lm_ee, Lm_ew, Lm_es, Lm_we, Lm_ww, Lm_ws, Lm_se, Lm_sw, Lm_ss]
  all_goals first
    | rfl
    | exact chart_matrix_lower _ (Fin.le_iff_val_le_val.2 (by omega))
    | (rw [neg_eq_zero, star_eq_zero]
       exact chart_matrix_lower _ (Fin.le_iff_val_le_val.2 (by have := a.isLt; have := b.isLt; omega)))
    | (exfalso; first
        | (have := a.isLt; have := b.isLt; omega)
        | (have := a.isLt; omega)
        | (have := b.isLt; omega))

theorem Lm_adj (t : (CI k r → ℂ) × (Fin r → ℝ)) : adjH (Lm t) + Lm t = 0 := by
  ext i j
  rw [Matrix.add_apply, adjH_apply, Matrix.zero_apply]
  obtain ⟨p, rfl⟩ := (posE k r).surjective i
  obtain ⟨q, rfl⟩ := (posE k r).surjective j
  rcases p with a | c | a <;> rcases q with b | c' | b <;>
    simp only [posE_apply, pos, gtau_eI, gtau_esI, gtau_wI, gsgn_eI, gsgn_esI, gsgn_wI,
      Lm_ee, Lm_ew, Lm_es, Lm_we, Lm_ww, Lm_ws, Lm_se, Lm_sw, Lm_ss, star_zero, mul_zero, zero_mul,
      add_zero, one_mul, mul_one, star_neg, star_star, neg_add_cancel, star_mul', dD_star]
  all_goals first
    | rw [add_neg_cancel]
    | linear_combination cK_skew t.1 t.2 a b
    | linear_combination (-(cB t.1 a c')) * dD_sq' c'

theorem Lm_mem (t : (CI k r → ℂ) × (Fin r → ℝ)) : Lm t ∈ lieN k r := ⟨chart_filtration_one t, Lm_adj t⟩

def hC : CI k r → ℕ
  | Sum.inl p => p.1.2.val - p.1.1.val
  | Sum.inr (Sum.inl q) => r - q.1.val
  | Sum.inr (Sum.inr p) => 2 * r - p.1.1.val - p.1.2.val

def ht : J k r → ℕ
  | Sum.inl (Sum.inl c) => hC c
  | Sum.inl (Sum.inr c) => hC c
  | Sum.inr a => 2 * r - 2 * a.val

theorem coordinate_first_eq {y y' : J k r → ℝ} {p : ℕ} (h : ∀ j, ht j < p → y j = y' j) {c : CI k r} (hc : hC c < p) :
    (toC y).1 c = (toC y').1 c := by
  simp only [toC]; rw [h (Sum.inl (Sum.inl c)) hc, h (Sum.inl (Sum.inr c)) hc]

theorem coordinate_second_eq {y y' : J k r → ℝ} {p : ℕ} (h : ∀ j, ht j < p → y j = y' j) {a : Fin r}
    (ha : 2 * r - 2 * a.val < p) : (toC y).2 a = (toC y').2 a := by
  simp only [toC]; rw [h (Sum.inr a) ha]

theorem Lm_fil_sub {y y' : J k r → ℝ} {p : ℕ} (h : ∀ j, ht j < p → y j = y' j) :
    Fil p (Lm (toC y) - Lm (toC y')) := by
  intro i j hij
  rw [Matrix.sub_apply, sub_eq_zero]
  obtain ⟨P, rfl⟩ := (posE k r).surjective i
  obtain ⟨Q, rfl⟩ := (posE k r).surjective j
  rcases P with a | c | a <;> rcases Q with b | c' | b <;>
    simp only [posE_apply, pos, dg_eI, dg_wI, dg_esI] at hij <;>
    simp only [posE_apply, pos, Lm_ee, Lm_ew, Lm_es, Lm_we, Lm_ww, Lm_ws, Lm_se, Lm_sw, Lm_ss]
  · by_cases hab : a < b
    · rw [chart_matrix_upper _ hab, chart_matrix_upper _ hab]
      exact coordinate_first_eq h (by simp only [hC]; omega)
    · rw [chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab)]
  · exact coordinate_first_eq h (by simp only [hC]; omega)
  · unfold cK
    split_ifs with h1 h2
    · exact coordinate_first_eq h (by simp only [hC]; have := b.isLt; omega)
    · rw [coordinate_first_eq h (by simp only [hC]; have := a.isLt; omega)]
    · have e : a = b := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
      subst e
      rw [coordinate_second_eq h (by have := a.isLt; omega)]
  · simp only [cB]
    rw [coordinate_first_eq h (c := Sum.inr (Sum.inl (b, c))) (by simp only [hC]; have := b.isLt; omega)]
  · by_cases hab : b < a
    · rw [chart_matrix_upper _ hab, chart_matrix_upper _ hab]
      rw [coordinate_first_eq h (by simp only [hC]; have := a.isLt; have := b.isLt; omega)]
    · rw [chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab)]

theorem Lm_add (t t' : (CI k r → ℂ) × (Fin r → ℝ)) : Lm (t + t') = Lm t + Lm t' := by
  ext i j
  rw [Matrix.add_apply]
  obtain ⟨P, rfl⟩ := (posE k r).surjective i
  obtain ⟨Q, rfl⟩ := (posE k r).surjective j
  rcases P with a | c | a <;> rcases Q with b | c' | b <;>
    simp only [posE_apply, pos, Lm_ee, Lm_ew, Lm_es, Lm_we, Lm_ww, Lm_ws, Lm_se, Lm_sw, Lm_ss, add_zero]
  · by_cases hab : a < b
    · rw [chart_matrix_upper _ hab, chart_matrix_upper _ hab, chart_matrix_upper _ hab]; rfl
    · rw [chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab), add_zero]
  · rfl
  · unfold cK
    split_ifs
    · rfl
    · simp only [Prod.fst_add, Pi.add_apply, star_add]; ring
    · simp only [Prod.snd_add, Pi.add_apply]; push_cast; ring
  · simp only [cB, Prod.fst_add, Pi.add_apply, star_add]; ring
  · by_cases hab : b < a
    · rw [chart_matrix_upper _ hab, chart_matrix_upper _ hab, chart_matrix_upper _ hab]
      simp only [Prod.fst_add, Pi.add_apply, star_add]; ring
    · rw [chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab)]; simp

theorem Lm_smul (c : ℝ) (t : (CI k r → ℂ) × (Fin r → ℝ)) : Lm (c • t) = c • Lm t := by
  ext i j
  rw [Matrix.smul_apply, Complex.real_smul]
  obtain ⟨P, rfl⟩ := (posE k r).surjective i
  obtain ⟨Q, rfl⟩ := (posE k r).surjective j
  rcases P with a | c | a <;> rcases Q with b | c' | b <;>
    simp only [posE_apply, pos, Lm_ee, Lm_ew, Lm_es, Lm_we, Lm_ww, Lm_ws, Lm_se, Lm_sw, Lm_ss, mul_zero]
  · by_cases hab : a < b
    · rw [chart_matrix_upper _ hab, chart_matrix_upper _ hab]; simp [Complex.real_smul]
    · rw [chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab), mul_zero]
  · simp [cB, Complex.real_smul]
  · unfold cK
    split_ifs
    · simp [Complex.real_smul]
    · simp only [Prod.smul_fst, Pi.smul_apply, Complex.real_smul, star_mul', Complex.star_def,
        Complex.conj_ofReal]; ring
    · simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]; push_cast; ring
  · simp only [cB, Prod.smul_fst, Pi.smul_apply, Complex.real_smul, star_mul', Complex.star_def,
      Complex.conj_ofReal]; ring
  · by_cases hab : b < a
    · rw [chart_matrix_upper _ hab, chart_matrix_upper _ hab]
      simp only [Prod.smul_fst, Pi.smul_apply, Complex.real_smul, star_mul', Complex.star_def,
        Complex.conj_ofReal]; ring
    · rw [chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab)]; simp

theorem toC_add (y y' : J k r → ℝ) : toC (y + y') = toC y + toC y' := by
  ext i
  · rfl
  · rfl

theorem toC_smul (c : ℝ) (y : J k r → ℝ) : toC (c • y) = c • toC y := by
  ext i
  · apply Complex.ext <;> simp [toC]
  · rfl

def LJ : (J k r → ℝ) →ₗ[ℝ] Mx k r where
  toFun y := Lm (toC y)
  map_add' y y' := by rw [toC_add, Lm_add]
  map_smul' c y := by rw [toC_smul, Lm_smul]; rfl

theorem continuous_LJ : Continuous (LJ (k := k) (r := r)) := LinearMap.continuous_of_finiteDimensional _

end Formalism.L2.SG.Pf.NcReal.JX.EC
end
end

noncomputable section

open MeasureTheory Matrix

namespace Formalism.L2.SG.Pf.NcReal.JX.EC

open Formalism.QuantumDeterminants WlocSk.NB
open Formalism.MainNotions.BridgeCSB (Fil lieN dg)

variable {k r : ℕ}

theorem mp_toC : MeasurePreserving (toC (k := k) (r := r)) volume volume := by
  have h1 := volume_measurePreserving_sumPiEquivProdPi (fun _ : J k r => ℝ)
  have h2 := volume_measurePreserving_sumPiEquivProdPi (fun _ : CI k r ⊕ CI k r => ℝ)
  have h3 := (volume_measurePreserving_arrowProdEquivProdArrow ℝ ℝ (CI k r)).symm
  have h4 : MeasurePreserving (fun (w : CI k r → ℝ × ℝ) (i : CI k r) =>
      Complex.measurableEquivRealProd.symm (w i)) volume volume :=
    volume_preserving_pi (fun _ => Complex.volume_preserving_equiv_real_prod.symm)
  have h5 := ((h4.comp h3).comp h2).prod (MeasurePreserving.id (volume : Measure (Fin r → ℝ)))
  have h6 := h5.comp h1
  convert h6 using 1
  all_goals first | rfl | (funext y; rfl)

def fromC (t : (CI k r → ℂ) × (Fin r → ℝ)) : J k r → ℝ
  | Sum.inl (Sum.inl c) => (t.1 c).re
  | Sum.inl (Sum.inr c) => (t.1 c).im
  | Sum.inr a => t.2 a

theorem toC_fromC (t : (CI k r → ℂ) × (Fin r → ℝ)) : toC (fromC t) = t := by
  rfl

theorem continuous_fromC : Continuous (fromC (k := k) (r := r)) := by
  refine continuous_pi fun j => ?_
  rcases j with (c | c) | a
  · exact Complex.continuous_re.comp ((continuous_apply c).comp continuous_fst)
  · exact Complex.continuous_im.comp ((continuous_apply c).comp continuous_fst)
  · exact (continuous_apply a).comp continuous_snd

section Cont

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

theorem continuous_expLJ : Continuous fun y : J k r → ℝ => (NormedSpace.exp (LJ y) : Mx k r) :=
  NormedSpace.exp_continuous.comp continuous_LJ

end Cont

def sJ (y : J k r → ℝ) : J k r → ℝ := fromC (psiC (NormedSpace.exp (LJ y)), psiR (NormedSpace.exp (LJ y)))

theorem continuous_sJ : Continuous (sJ (k := k) (r := r)) :=
  continuous_fromC.comp ((continuous_psiC.comp continuous_expLJ).prodMk (continuous_psiR.comp continuous_expLJ))

theorem entry_of_fil {D E : Mx k r} {p : ℕ} (h : Fil (p + 1) (D - E)) {i j : Fin (2 * r + k + 1)}
    (hij : dg k r j ≤ dg k r i + p) : D i j = E i j := by
  have h1 := h i j (by omega)
  rw [Matrix.sub_apply, sub_eq_zero] at h1
  exact h1

theorem mof_sub {g g' : Mx k r} (hg : g ∈ Nset k r) (hg' : g' ∈ Nset k r) (a b : Fin r)
    (hG : Fil (2 * r - a.val - b.val) (g - g')) :
    mof g a b - mof g' a b = g (eI k r a) (esI k r b) - g' (eI k r a) (esI k r b) := by
  have h1 := ((Formalism.MainNotions.BridgeCSB.mem_N_iff g).1 hg).2
  have h1' := ((Formalism.MainNotions.BridgeCSB.mem_N_iff g').1 hg').2
  have key : ∀ c : Fin r, star (g (esI k r c) (esI k r a)) * g (eI k r c) (esI k r b) -
      star (g' (esI k r c) (esI k r a)) * g' (eI k r c) (esI k r b) =
      if c = a then g (eI k r a) (esI k r b) - g' (eI k r a) (esI k r b) else 0 := by
    intro c
    have ha := a.isLt; have hb := b.isLt; have hc := c.isLt
    rcases lt_trichotomy c a with h | rfl | h
    · have hca : c.val < a.val := h
      have e1 := h1 (esI k r c) (esI k r a) (by rw [dg_esI, dg_esI]; omega)
      have e2 := h1' (esI k r c) (esI k r a) (by rw [dg_esI, dg_esI]; omega)
      rw [Matrix.sub_apply, Matrix.one_apply, if_neg (fun e => (ne_of_lt h) (esI_inj.1 e)), sub_zero] at e1 e2
      rw [e1, e2, if_neg (ne_of_lt h)]; simp
    · have e1 := h1 (esI k r c) (esI k r c) (by rw [dg_esI]; omega)
      have e2 := h1' (esI k r c) (esI k r c) (by rw [dg_esI]; omega)
      rw [Matrix.sub_apply, Matrix.one_apply, if_pos rfl, sub_eq_zero] at e1 e2
      rw [e1, e2, if_pos rfl]; simp
    · have hac : a.val < c.val := h
      have e1 := hG (esI k r c) (esI k r a) (by rw [dg_esI, dg_esI]; omega)
      have e2 := hG (eI k r c) (esI k r b) (by rw [dg_esI, dg_eI]; omega)
      rw [Matrix.sub_apply, sub_eq_zero] at e1 e2
      rw [e1, e2, if_neg (ne_of_gt h), sub_self]
  simp only [mof, Matrix.mul_apply, conjTranspose_apply, bF, bC]
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl (fun c _ => key c)]
  simp

theorem psiC_sub (t t' : (CI k r → ℂ) × (Fin r → ℝ)) (c : CI k r)
    (hG : Fil (hC c) (NormedSpace.exp (Lm t) - NormedSpace.exp (Lm t')))
    (hE : Fil (hC c + 1) ((NormedSpace.exp (Lm t) - NormedSpace.exp (Lm t')) - (Lm t - Lm t'))) :
    psiC (NormedSpace.exp (Lm t)) c - psiC (NormedSpace.exp (Lm t')) c = t.1 c - t'.1 c := by
  have hg := Formalism.MainNotions.BridgeCSB.exp_mem_N (Lm_mem t)
  have hg' := Formalism.MainNotions.BridgeCSB.exp_mem_N (Lm_mem t')
  have ent : ∀ i j, dg k r j ≤ dg k r i + hC c →
      (NormedSpace.exp (Lm t) - NormedSpace.exp (Lm t')) i j = (Lm t - Lm t') i j :=
    fun i j h => entry_of_fil hE h
  rcases c with ⟨⟨a, b⟩, h⟩ | ⟨a, j⟩ | ⟨⟨a, b⟩, h⟩
  · have hab : a.val < b.val := h
    have := ent (eI k r a) (eI k r b) (by rw [dg_eI, dg_eI]; simp only [hC]; omega)
    simp only [Matrix.sub_apply, Lm_ee, chart_matrix_upper _ h] at this
    exact this
  · have := ent (eI k r a) (wI k r j) (by rw [dg_eI, dg_wI]; simp only [hC]; omega)
    simp only [Matrix.sub_apply, Lm_ew] at this
    exact this
  · have hab' : a.val < b.val := h
    have hb := b.isLt
    have eh : hC (Sum.inr (Sum.inr ⟨(a, b), h⟩) : CI k r) = 2 * r - a.val - b.val := rfl
    have hab := mof_sub hg hg' a b (by rw [← eh]; exact hG)
    have hba := mof_sub hg hg' b a (by
      have : 2 * r - b.val - a.val = 2 * r - a.val - b.val := by omega
      rw [this, ← eh]; exact hG)
    have e1 := ent (eI k r a) (esI k r b) (by rw [dg_eI, dg_esI, eh]; omega)
    have e2 := ent (eI k r b) (esI k r a) (by rw [dg_eI, dg_esI, eh]; omega)
    simp only [Matrix.sub_apply, Lm_es] at e1 e2
    have hba' := congrArg star hba
    have e2' := congrArg star e2
    simp only [star_sub] at hba' e2'
    have sk := cK_skew t.1 t.2 a b
    have sk' := cK_skew t'.1 t'.2 a b
    have hx : ∀ x : CI k r → ℂ, ∀ s, cK x s a b = x (Sum.inr (Sum.inr ⟨(a, b), h⟩)) := by
      intro x s; unfold cK; rw [dite_eq_left h]
    show kof _ a b - kof _ a b = _
    rw [← hx t.1 t.2, ← hx t'.1 t'.2]
    simp only [kof]
    linear_combination (1 / 2 : ℂ) * hab + (1 / 2 : ℂ) * e1 - (1 / 2 : ℂ) * hba' - (1 / 2 : ℂ) * e2' -
      (1 / 2 : ℂ) * sk + (1 / 2 : ℂ) * sk'

theorem psiR_sub (t t' : (CI k r → ℂ) × (Fin r → ℝ)) (a : Fin r)
    (hG : Fil (2 * r - 2 * a.val) (NormedSpace.exp (Lm t) - NormedSpace.exp (Lm t')))
    (hE : Fil (2 * r - 2 * a.val + 1) ((NormedSpace.exp (Lm t) - NormedSpace.exp (Lm t')) - (Lm t - Lm t'))) :
    psiR (NormedSpace.exp (Lm t)) a - psiR (NormedSpace.exp (Lm t')) a = t.2 a - t'.2 a := by
  have hg := Formalism.MainNotions.BridgeCSB.exp_mem_N (Lm_mem t)
  have hg' := Formalism.MainNotions.BridgeCSB.exp_mem_N (Lm_mem t')
  have ha := a.isLt
  have hm := mof_sub hg hg' a a (by
    have : 2 * r - a.val - a.val = 2 * r - 2 * a.val := by omega
    rw [this]; exact hG)
  have e1 := entry_of_fil hE (i := eI k r a) (j := esI k r a) (by rw [dg_eI, dg_esI]; omega)
  simp only [Matrix.sub_apply, Lm_es] at e1
  have hk : ∀ (x : CI k r → ℂ) (s : Fin r → ℝ), cK x s a a = (s a : ℂ) * Complex.I := by
    intro x s; unfold cK; rw [dite_eq_right (lt_irrefl a), dite_eq_right (lt_irrefl a)]
  rw [hk, hk] at e1
  have := congrArg Complex.im (hm.trans e1)
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, mul_zero, add_zero] at this
  simp only [psiR]
  linarith

theorem sJ_shear (i : J k r) (y y' : J k r → ℝ) (h : ∀ j, ht j < ht i → y j = y' j) :
    sJ y i - y i = sJ y' i - y' i := by
  have hF := Lm_fil_sub h
  have hE := Formalism.MainNotions.BridgeCSB.Fil.exp_sub_exp (chart_filtration_one (toC y)) (chart_filtration_one (toC y')) hF
  have hG : Fil (ht i) (NormedSpace.exp (Lm (toC y)) - NormedSpace.exp (Lm (toC y'))) := by
    have := (hE.mono (Nat.le_succ _)).add hF
    rwa [sub_add_cancel] at this
  rcases i with (c | c) | a
  · have := congrArg Complex.re (psiC_sub (toC y) (toC y') c hG hE)
    simp only [Complex.sub_re] at this
    show (psiC (NormedSpace.exp (Lm (toC y))) c).re - ((toC y).1 c).re =
      (psiC (NormedSpace.exp (Lm (toC y'))) c).re - ((toC y').1 c).re
    linarith
  · have := congrArg Complex.im (psiC_sub (toC y) (toC y') c hG hE)
    simp only [Complex.sub_im] at this
    show (psiC (NormedSpace.exp (Lm (toC y))) c).im - ((toC y).1 c).im =
      (psiC (NormedSpace.exp (Lm (toC y'))) c).im - ((toC y').1 c).im
    linarith
  · have := psiR_sub (toC y) (toC y') a hG hE
    show psiR (NormedSpace.exp (Lm (toC y))) a - (toC y).2 a =
      psiR (NormedSpace.exp (Lm (toC y'))) a - (toC y').2 a
    linarith

theorem shear_change_holds : ShearStep := by
  intro k r
  refine ⟨fun y => (psiC (NormedSpace.exp (LJ y)), psiR (NormedSpace.exp (LJ y))), ?_, ?_⟩
  · have hS := Formalism.MainNotions.BridgeCSB.shearMP (J k r) ht sJ continuous_sJ.measurable
      (fun i y y' h => sJ_shear i y y' h)
    have := mp_toC.comp hS
    convert this using 1
    funext y
    exact (toC_fromC _).symm
  · intro y
    exact nilpotent_chart_left_inverse (Formalism.MainNotions.BridgeCSB.exp_mem_N (Lm_mem (toC y)))

end Formalism.L2.SG.Pf.NcReal.JX.EC
end
end

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.EC

open Formalism.QuantumDeterminants WlocSk.NB
open Formalism.MainNotions.BridgeCSB (Fil lieN adjH adjH_apply dg)

variable {k r : ℕ}

theorem sum_up {M : Type*} [AddCommMonoid M] (f : UP r → M) :
    ∑ a : Fin r, ∑ b : Fin r, (if h : a < b then f ⟨(a, b), h⟩ else 0) = ∑ p : UP r, f p := by
  classical
  rw [← Fintype.sum_prod_type' (fun a b => if h : a < b then f ⟨(a, b), h⟩ else 0)]
  rw [Finset.sum_dite]
  simp only [Finset.sum_const_zero, add_zero]
  refine Finset.sum_bij' (fun x _ => ⟨x.1, (Finset.mem_filter.mp x.2).2⟩)
    (fun p _ => ⟨p.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, p.2⟩⟩) ?_ ?_ ?_ ?_ ?_ <;> simp

theorem card_up : 2 * Fintype.card (UP r) + r = r * r := by
  classical
  have h1 := sum_up (M := ℕ) (r := r) (fun _ => 1)
  have h2 : ∑ a : Fin r, ∑ b : Fin r, (if h : b < a then (1 : ℕ) else 0) = Fintype.card (UP r) := by
    rw [Finset.sum_comm]
    simpa using h1
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h1
  have key : ∀ a b : Fin r, (if h : a < b then (1 : ℕ) else 0) + (if h : b < a then (1 : ℕ) else 0) +
      (if a = b then 1 else 0) = 1 := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, not_lt.mpr h.le, ne_of_lt h]
    · simp [h]
    · simp [h, not_lt.mpr h.le, (ne_of_lt h).symm]
  have htot : ∑ a : Fin r, ∑ b : Fin r, ((if h : a < b then (1 : ℕ) else 0) + (if h : b < a then (1 : ℕ) else 0) +
      (if a = b then 1 else 0)) = r * r := by
    simp only [key, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]
  simp only [Finset.sum_add_distrib] at htot
  rw [h1, h2] at htot
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at htot
  omega

theorem card_CI : Fintype.card (CI k r) = r ^ 2 + r * k := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  have h := card_up (r := r)
  nlinarith [h]

theorem nsq_star (z : ℂ) : Complex.normSq (star z) = Complex.normSq z := Complex.normSq_conj z

theorem nsq_dD (j : Fin (k + 1)) : Complex.normSq (dD k j j) = 1 := by
  simp only [dD, Matrix.diagonal_apply_eq]
  split_ifs <;> simp

theorem nsq_A (x : CI k r → ℂ) (a b : Fin r) : Complex.normSq ((cA x - 1) a b) =
    if h : a < b then Complex.normSq (x (Sum.inl ⟨(a, b), h⟩)) else 0 := by
  simp only [Matrix.sub_apply, cA, Matrix.one_apply]
  by_cases h : a < b
  · simp [h, ne_of_lt h]
  · by_cases hab : a = b <;> simp [h, hab]

theorem nsq_K (x : CI k r → ℂ) (s : Fin r → ℝ) (a b : Fin r) : Complex.normSq (cK x s a b) =
    (if h : a < b then Complex.normSq (x (Sum.inr (Sum.inr ⟨(a, b), h⟩))) else 0) +
    (if h : b < a then Complex.normSq (x (Sum.inr (Sum.inr ⟨(b, a), h⟩))) else 0) +
    (if a = b then s a ^ 2 else 0) := by
  unfold cK
  by_cases h1 : a < b
  · have h2 : ¬ b < a := not_lt.mpr h1.le
    have h3 : a ≠ b := ne_of_lt h1
    simp [h1, h2, h3]
  · by_cases h2 : b < a
    · simp [h1, h2, (ne_of_lt h2).symm, Complex.normSq_neg, Complex.star_def, Complex.normSq_conj]
    · have h3 : a = b := le_antisymm (not_lt.mp h2) (not_lt.mp h1)
      subst h3
      simp [Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal]
      ring

theorem sum_pos (F : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℝ) :
    ∑ i, ∑ j, F i j = ∑ p : Ix k r, ∑ q : Ix k r, F (posE k r p) (posE k r q) := by
  rw [← Equiv.sum_comp (posE k r) (fun i => ∑ j, F i j)]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Equiv.sum_comp (posE k r) (fun j => F (posE k r p) j)]

section blocks

variable (t : (CI k r → ℂ) × (Fin r → ℝ))

theorem b_ee : ∑ a : Fin r, ∑ b : Fin r, Complex.normSq (Lm t (eI k r a) (eI k r b)) =
    ∑ p : UP r, Complex.normSq (t.1 (Sum.inl p)) := by
  have hL : ∀ a b : Fin r, Lm t (eI k r a) (eI k r b) = (cA t.1 - 1) a b := by
    intro a b
    unfold Lm
    rw [Matrix.sub_apply, mk_ee, mk_ee, Matrix.zero_apply, sub_zero]
  simp only [hL, nsq_A]
  exact sum_up (fun p => Complex.normSq (t.1 (Sum.inl p)))

theorem b_ss : ∑ a : Fin r, ∑ b : Fin r, Complex.normSq (Lm t (esI k r a) (esI k r b)) =
    ∑ p : UP r, Complex.normSq (t.1 (Sum.inl p)) := by
  have hL : ∀ a b : Fin r, Complex.normSq (Lm t (esI k r a) (esI k r b)) = Complex.normSq ((cA t.1 - 1) b a) := by
    intro a b
    unfold Lm
    rw [Matrix.sub_apply, mk_ss, mk_ss, Matrix.zero_apply, sub_zero, Matrix.neg_apply,
      Matrix.conjTranspose_apply, Complex.normSq_neg, nsq_star]
  simp only [hL, nsq_A]
  rw [Finset.sum_comm]
  exact sum_up (fun p => Complex.normSq (t.1 (Sum.inl p)))

theorem b_ws : ∑ j : Fin (k + 1), ∑ b : Fin r, Complex.normSq (Lm t (wI k r j) (esI k r b)) =
    ∑ a : Fin r, ∑ j : Fin (k + 1), Complex.normSq (t.1 (Sum.inr (Sum.inl (a, j)))) := by
  simp only [Lm_ws, Complex.normSq_neg, Complex.normSq_mul, nsq_dD, nsq_star, one_mul]
  exact Finset.sum_comm

theorem b_es : ∑ a : Fin r, ∑ b : Fin r, Complex.normSq (Lm t (eI k r a) (esI k r b)) =
    2 * ∑ p : UP r, Complex.normSq (t.1 (Sum.inr (Sum.inr p))) + ∑ a : Fin r, t.2 a ^ 2 := by
  have hL : ∀ a b : Fin r, Lm t (eI k r a) (esI k r b) = cK t.1 t.2 a b := by
    intro a b
    unfold Lm
    rw [Matrix.sub_apply, mk_es, mk_es, Matrix.zero_apply, sub_zero]
  simp only [hL, nsq_K, Finset.sum_add_distrib]
  have h1 := sum_up (fun p => Complex.normSq (t.1 (Sum.inr (Sum.inr p))))
  have h2 : ∑ a : Fin r, ∑ b : Fin r, (if h : b < a then Complex.normSq (t.1 (Sum.inr (Sum.inr ⟨(b, a), h⟩))) else 0) =
      ∑ p : UP r, Complex.normSq (t.1 (Sum.inr (Sum.inr p))) := by
    rw [Finset.sum_comm]
    exact sum_up (fun p => Complex.normSq (t.1 (Sum.inr (Sum.inr p))))
  have h3 : ∑ a : Fin r, ∑ b : Fin r, (if a = b then t.2 a ^ 2 else 0) = ∑ a : Fin r, t.2 a ^ 2 := by
    simp
  rw [h1, h2, h3]
  ring

end blocks

theorem normLm (t : (CI k r → ℂ) × (Fin r → ℝ)) :
    ∑ i, ∑ j, Complex.normSq (Lm t i j) = 2 * ∑ c, Complex.normSq (t.1 c) + ∑ a, t.2 a ^ 2 := by
  rw [sum_pos]
  simp only [Fintype.sum_sum_type, posE_apply, pos, Fintype.sum_prod_type, Finset.sum_add_distrib]
  simp only [b_ee, b_ss, b_ws, b_es]
  simp only [Lm_ew, Lm_we, Lm_ww, Lm_se, Lm_sw, Complex.normSq_zero, Finset.sum_const_zero, cB]
  ring

def xsL (Z : Mx k r) : CI k r → ℂ
  | Sum.inl p => Z (eI k r p.1.1) (eI k r p.1.2)
  | Sum.inr (Sum.inl q) => Z (eI k r q.1) (wI k r q.2)
  | Sum.inr (Sum.inr p) => Z (eI k r p.1.1) (esI k r p.1.2)

def ssL (Z : Mx k r) : Fin r → ℝ := fun a => (Z (eI k r a) (esI k r a)).im

theorem Lm_read {Z : Mx k r} (hZ : Z ∈ lieN k r) : Lm (xsL Z, ssL Z) = Z := by
  have hF := hZ.1
  have adj : ∀ i j, Formalism.QuantumDeterminants.WeylGroupFacts.sgn k r i *
      star (Z (Formalism.QuantumDeterminants.WeylGroupFacts.tau k r j) (Formalism.QuantumDeterminants.WeylGroupFacts.tau k r i)) * Formalism.QuantumDeterminants.WeylGroupFacts.sgn k r j +
      Z i j = 0 := by
    intro i j
    have := congrFun (congrFun hZ.2 i) j
    rwa [Matrix.add_apply, adjH_apply, Matrix.zero_apply] at this
  ext i j
  obtain ⟨P, rfl⟩ := (posE k r).surjective i
  obtain ⟨Q, rfl⟩ := (posE k r).surjective j
  rcases P with a | c | a <;> rcases Q with b | c' | b <;>
    simp only [posE_apply, pos, Lm_ee, Lm_ew, Lm_es, Lm_we, Lm_ww, Lm_ws, Lm_se, Lm_sw, Lm_ss]
  · by_cases hab : a < b
    · rw [chart_matrix_upper _ hab]; rfl
    · rw [chart_matrix_lower _ (not_lt.1 hab)]
      have : b.val ≤ a.val := not_lt.1 hab
      exact (hF _ _ (by rw [dg_eI, dg_eI]; omega)).symm
  · rfl
  · unfold cK
    split_ifs with h1 h2
    · rfl
    · have := adj (eI k r a) (esI k r b)
      simp only [gtau_eI, gtau_esI, gsgn_eI, gsgn_esI, one_mul, mul_one] at this
      show -star (Z (eI k r b) (esI k r a)) = _
      linear_combination (-1 : ℂ) * this
    · have e : a = b := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
      subst e
      have := adj (eI k r a) (esI k r a)
      simp only [gtau_eI, gtau_esI, gsgn_eI, gsgn_esI, one_mul, mul_one] at this
      have hre := congrArg Complex.re this
      simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.zero_re] at hre
      apply Complex.ext
      · simp [ssL]; linarith
      · simp [ssL]
  · exact (hF _ _ (by rw [dg_wI, dg_eI]; have := b.isLt; omega)).symm
  · exact (hF _ _ (by rw [dg_wI, dg_wI]; omega)).symm
  · have := adj (wI k r c) (esI k r b)
    simp only [gtau_wI, gtau_esI, gsgn_wI, gsgn_esI, mul_one] at this
    show -(dD k c c * star (Z (eI k r b) (wI k r c))) = _
    linear_combination (-1 : ℂ) * this
  · exact (hF _ _ (by rw [dg_esI, dg_eI]; have := a.isLt; have := b.isLt; omega)).symm
  · exact (hF _ _ (by rw [dg_esI, dg_wI]; have := a.isLt; omega)).symm
  · by_cases hab : b < a
    · rw [chart_matrix_upper _ hab]
      have := adj (esI k r a) (esI k r b)
      simp only [gtau_esI, gsgn_esI, one_mul, mul_one] at this
      show -star (Z (eI k r b) (eI k r a)) = _
      linear_combination (-1 : ℂ) * this
    · rw [chart_matrix_lower _ (not_lt.1 hab), star_zero, neg_zero]
      have : a.val ≤ b.val := not_lt.1 hab
      exact (hF _ _ (by rw [dg_esI, dg_esI]; have := b.isLt; omega)).symm

theorem norm_RL_sq (X : Mx k r) :
    ‖Formalism.MainNotions.BridgeCSB.RL (k := k) (r := r) X‖ ^ 2 = ∑ i, ∑ j, Complex.normSq (X i j) := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [Formalism.MainNotions.BridgeCSB.RL, Formalism.MainNotions.S.realifyFun, Complex.normSq_apply, Real.norm_eq_abs, sq_abs]
  ring

def cw : J k r → ℝ := Sum.elim (fun _ => (Real.sqrt 2)⁻¹) (fun _ => 1)

theorem cw_ne (j : J k r) : cw j ≠ 0 := by
  rcases j with j | j <;> simp [cw]

def dL : (J k r → ℝ) →ₗ[ℝ] (J k r → ℝ) := Matrix.toLin' (Matrix.diagonal cw)

theorem dL_apply (y : J k r → ℝ) (j : J k r) : dL y j = cw j * y j := by
  simp [dL, Matrix.toLin'_apply, Matrix.mulVec_diagonal]

theorem RL_LJ_mem (y : J k r → ℝ) : Formalism.MainNotions.BridgeCSB.RL (LJ y) ∈ Formalism.MainNotions.S.lieE (Nset k r) := by
  rw [Formalism.MainNotions.BridgeCSB.lieE_N]; exact ⟨LJ y, Lm_mem _, rfl⟩

def TL : (J k r → ℝ) →ₗ[ℝ] Formalism.MainNotions.S.lieE (Nset k r) :=
  (Formalism.MainNotions.BridgeCSB.RL ∘ₗ LJ).codRestrict _ RL_LJ_mem

def Psl : EuclideanSpace ℝ (J k r) →ₗ[ℝ] Formalism.MainNotions.S.lieE (Nset k r) :=
  TL ∘ₗ dL ∘ₗ (WithLp.linearEquiv 2 ℝ (J k r → ℝ)).toLinearMap

theorem norm_Psl (z : EuclideanSpace ℝ (J k r)) : ‖Psl z‖ = ‖z‖ := by
  have hs : (Real.sqrt 2)⁻¹ ^ 2 = 1 / 2 := by rw [inv_pow, Real.sq_sqrt (by norm_num)]; norm_num
  set w : J k r → ℝ := WithLp.ofLp z with hw
  have hp : ∀ c, 2 * Complex.normSq ((toC (dL w)).1 c) =
      w (Sum.inl (Sum.inl c)) ^ 2 + w (Sum.inl (Sum.inr c)) ^ 2 := by
    intro c
    simp only [toC, dL_apply, cw, Sum.elim_inl, Complex.normSq_mk]
    linear_combination (2 * (w (Sum.inl (Sum.inl c)) ^ 2 + w (Sum.inl (Sum.inr c)) ^ 2)) * hs
  have hq : ∀ a, (toC (dL w)).2 a ^ 2 = w (Sum.inr a) ^ 2 := by
    intro a; simp [toC, dL_apply, cw]
  have h1 : ‖Psl z‖ ^ 2 = ‖z‖ ^ 2 := by
    change ‖Formalism.MainNotions.BridgeCSB.RL (k := k) (r := r) (Lm (toC (dL w)))‖ ^ 2 = _
    rw [norm_RL_sq, normLm, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    simp only [Real.norm_eq_abs, sq_abs]
    rw [Fintype.sum_sum_type (fun j : J k r => w j ^ 2),
      Fintype.sum_sum_type (fun j : CI k r ⊕ CI k r => w (Sum.inl j) ^ 2), ← Finset.sum_add_distrib,
      Finset.mul_sum, Finset.sum_congr rfl (fun c _ => hp c), Finset.sum_congr rfl (fun a _ => hq a)]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h1

theorem Psl_injective : Function.Injective (Psl (k := k) (r := r)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have h := norm_Psl z
  rw [hz, norm_zero] at h
  exact norm_eq_zero.mp h.symm

theorem Psl_surjective : Function.Surjective (Psl (k := k) (r := r)) := by
  rintro ⟨v, hv⟩
  have hv' := hv
  rw [Formalism.MainNotions.BridgeCSB.lieE_N] at hv'
  obtain ⟨Z, hZ, rfl⟩ := hv'
  refine ⟨WithLp.toLp 2 (fun j => fromC (xsL Z, ssL Z) j / cw j), ?_⟩
  apply Subtype.ext
  change Formalism.MainNotions.BridgeCSB.RL (Lm (toC (dL (fun j => fromC (xsL Z, ssL Z) j / cw j)))) = _
  have e : dL (fun j => fromC (xsL (k := k) (r := r) Z, ssL Z) j / cw j) = fromC (xsL Z, ssL Z) := by
    funext j; rw [dL_apply, mul_div_cancel₀ _ (cw_ne j)]
  rw [e, toC_fromC, Lm_read hZ]

def Psi : EuclideanSpace ℝ (J k r) ≃ₗᵢ[ℝ] Formalism.MainNotions.S.lieE (Nset k r) :=
  { LinearEquiv.ofBijective Psl ⟨Psl_injective, Psl_surjective⟩ with norm_map' := norm_Psl }

theorem det_dL : LinearMap.det (dL (k := k) (r := r)) = ((Real.sqrt 2)⁻¹) ^ (2 * Fintype.card (CI k r)) := by
  rw [dL, LinearMap.det_toLin', Matrix.det_diagonal]
  simp [cw, Fintype.prod_sum_type, Finset.prod_const]
  ring

theorem inv_det_dL : (LinearMap.det (dL (k := k) (r := r)))⁻¹ = (2 : ℝ) ^ (r ^ 2 + r * k) := by
  rw [det_dL, card_CI, pow_mul, inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  simp

theorem constant_change_holds : ConstStep := by
  intro k r
  have hTc : Continuous (TL (k := k) (r := r)) := LinearMap.continuous_of_finiteDimensional _
  have hdc : Continuous (dL (k := k) (r := r)) := LinearMap.continuous_of_finiteDimensional _
  refine ⟨TL, hTc.measurable, fun y => rfl, ?_⟩
  have h1 := (Psi (k := k) (r := r)).measurePreserving.comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (J k r)).symm
  have e1 : (⇑(Psi (k := k) (r := r)) ∘ ⇑(MeasurableEquiv.toLp 2 (J k r → ℝ)).symm.symm) = ⇑TL ∘ ⇑dL := by
    funext y; rfl
  have hdet : LinearMap.det (dL (k := k) (r := r)) ≠ 0 := by
    intro h
    have := inv_det_dL (k := k) (r := r)
    rw [h, _root_.inv_zero] at this
    exact pow_ne_zero _ two_ne_zero this.symm
  rw [← h1.map_eq, e1, ← Measure.map_map hTc.measurable hdc.measurable,
    Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet, Measure.map_smul, inv_det_dL,
    abs_of_pos (by positivity)]
  exact hTc.aemeasurable

end Formalism.L2.SG.Pf.NcReal.JX.EC
end
end

noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.EC

open Formalism.QuantumDeterminants WlocSk.NB

theorem expChart_of (hS : ShearStep) (hC : ConstStep) : ExpChart := by
  intro k r
  obtain ⟨σ, hσ, hσe⟩ := hS k r
  obtain ⟨Λ, hΛm, hΛ, hvol⟩ := hC k r
  have hE := Formalism.MainNotions.BridgeCSB.continuous_expLie (k := k) (r := r) (Nset k r)
  let Φ : (CI k r → ℂ) × (Fin r → ℝ) → Mt k r := fun t => phi0 t.1 t.2
  have hφ : Continuous Φ := continuous_nilpotent_chart
  unfold Formalism.MainNotions.S.haarLie
  rw [one_smul, hvol, Measure.map_smul, Measure.map_map hE.measurable hΛm, ← hσ.map_eq]
  congr 1
  have e : ((fun x : Formalism.MainNotions.S.lieE (Nset k r) => fun i j =>
      NormedSpace.exp (Formalism.MainNotions.S.unrealify (x : EuclideanSpace ℝ _)) i j) ∘ Λ : (J k r → ℝ) → Mt k r) = Φ ∘ σ := by
    funext y
    simp only [Function.comp, Φ]
    rw [hσe y, hΛ y, Formalism.MainNotions.BridgeCSB.unrealify_RL]
  rw [e]
  exact (Measure.map_map hφ.measurable hσ.measurable).symm
  exact hE.measurable.aemeasurable

end Formalism.L2.SG.Pf.NcReal.JX.EC

namespace Formalism.L2.SG.Pf.NcReal.JX

theorem exponential_chart_haar : ExpChart := EC.expChart_of EC.shear_change_holds EC.constant_change_holds

end Formalism.L2.SG.Pf.NcReal.JX
