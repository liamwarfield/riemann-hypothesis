module

public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalSer
public import Formalism.TorsionNormIteration.LubinTateExample
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModEvalMF
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem qm_eq_qParam (m : ℕ) (τ : ℍ) : qm m τ = Function.Periodic.qParam (m : ℝ) τ := by
  simp [qm, Function.Periodic.qParam]

theorem qm_norm_lt_one {m : ℕ} (hm : 0 < m) (τ : ℍ) : ‖qm m τ‖ < 1 := by
  rw [qm_eq_qParam]
  exact Function.Periodic.norm_qParam_lt_one (by exact_mod_cast hm) τ.im_pos

theorem qm_surj {m : ℕ} (hm : 0 < m) {x : ℂ} (h0 : 0 < ‖x‖) (h1 : ‖x‖ < 1) : ∃ τ : ℍ, qm m τ = x := by
  have hlog : Real.log ‖x‖ < 0 := Real.log_neg h0 h1
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have him : 0 < (Function.Periodic.invQParam (m : ℝ) x).im := by
    rw [Function.Periodic.im_invQParam]
    refine mul_pos_of_neg_of_neg ?_ hlog
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  refine ⟨⟨_, him⟩, ?_⟩
  rw [qm_eq_qParam]
  exact Function.Periodic.qParam_right_inv hmR.ne' (norm_pos_iff.mp h0)

theorem qm_pow {m : ℕ} (hm : 0 < m) (τ : ℍ) : qm m τ ^ m = qm 1 τ := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [qm, qm, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp

theorem qm_one_eq (τ : ℍ) : qm 1 τ = Function.Periodic.qParam 1 τ := by
  simpa using qm_eq_qParam 1 τ

theorem qm_pt {a e : ℕ} (ha : 0 < a) (he : 0 < e) (b : ℕ) (τ : ℍ) :
    qm 1 (pt a b e τ) = zetaC e ^ b * qm (a * e) τ ^ (a ^ 2) := by
  have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have he' : (e : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  rw [qm, qm, zetaC, pt_coe ha he, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
    ← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

theorem IsMF.hasSum {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (τ : ℍ) :
    HasSum (fun n => PowerSeries.coeff n (qExpansion 1 f) * qm 1 τ ^ n) (f τ) := by
  obtain ⟨g, hg⟩ := hf
  have hgf : (⇑g : ℍ → ℂ) = f := funext hg
  have h := ModularForm.hasSum_qExpansion (f := g) one_pos one_mem_strictPeriods_SL τ
  rw [hgf, ← qm_one_eq] at h
  exact h

theorem IsMF.conv {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) : Conv (qExpansion 1 f) := by
  apply conv_of_hasSum
  intro x hx
  by_cases h0 : x = 0
  · subst h0
    exact (hasSum_single 0 fun n hn => by simp [zero_pow hn]).summable
  · obtain ⟨τ, hτ⟩ := qm_surj one_pos (norm_pos_iff.mpr h0) hx
    rw [← hτ]
    exact (hf.hasSum τ).summable

theorem IsMF.ev_eq {k : ℤ} {f : ℍ → ℂ} (hf : IsMF k f) (τ : ℍ) : ev (qExpansion 1 f) (qm 1 τ) = f τ := by
  exact (hf.hasSum τ).tsum_eq

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.FgDefs
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open PowerSeries Formalism.G Formalism.LT Formalism.L2.Th1.CM

section Abstract

variable {K : Type} [NormedField K]

structure LawD (lam : PowerSeries K) (Φ : MvPowerSeries (Fin 2) K) : Prop where
  lam0 : constantCoeff lam = 0
  lam1 : coeff 1 lam = 1
  Φ0 : MvPowerSeries.constantCoeff Φ = 0
  Φint : IntegralMv Φ
  log : lam.subst Φ = atX lam + atY lam

structure HD (σ : K →+* K) (lam : PowerSeries K) (Φ : MvPowerSeries (Fin 2) K) (A : PowerSeries K)
    (a : K) : Prop extends LawD lam Φ where
  A0 : constantCoeff A = 0
  Aint : IntegralPS A
  Alog : lam.subst A = C a * lam
  a_ne : ‖σ a - a‖ = 1
  a_sq : σ (σ a) = a

structure QCls (l : ℕ) (Φ : MvPowerSeries (Fin 2) K) (A : PowerSeries K) (b : K)
    (D : PowerSeries K) : Prop where
  D0 : constantCoeff D = 0
  dInt : IntegralPS (PowerSeries.derivative D)
  add : DivByMv (l : K) (D.subst Φ - atX D - atY D)
  eig : DivBy (l : K) (D.subst A - C b * D)

structure HomCls (l : ℕ) (Φ₁ : MvPowerSeries (Fin 2) K) (A₁ : PowerSeries K)
    (Φ₂ : MvPowerSeries (Fin 2) K) (A₂ : PowerSeries K) (g : PowerSeries K) : Prop where
  g0 : constantCoeff g = 0
  gInt : IntegralPS g
  add : DivByMv (l : K) (g.subst Φ₁ - Φ₂.subst ![atX g, atY g])
  eig : DivBy (l : K) (g.subst A₁ - A₂.subst g)

def desc (l : ℕ) (D : PowerSeries K) : PowerSeries K := PowerSeries.mk fun m => coeff (l * m) D

def d2 (Φ : MvPowerSeries (Fin 2) K) : PowerSeries K :=
  PowerSeries.mk fun n => MvPowerSeries.coeff (Finsupp.single 0 n + Finsupp.single 1 1) Φ

end Abstract


open Classical in
def lgS {K : Type} [Field K] (g2 g3 : K) : PowerSeries K :=
  if h : ∃ t : PowerSeries K, constantCoeff t = 0 ∧ (uSer g2 g3).subst t = X then h.choose else 0

end ReciprocityTheory.ChartRestriction.L1
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.TchOfIntegral
noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

variable (l : ℕ) [Fact l.Prime]

theorem tch_of_integral (δ : ℂ_[l]) (hδ : IsIntegral (Rmu l) δ) : ∃ ξ ∈ Tch l, ‖δ - ξ‖ < 1 := by
  have hZ := KE.isIntegral_int_of_rmu (l := l) δ hδ
  have h1 : ‖δ‖ ≤ 1 := KE.norm_le_one_of_integral_int δ hZ
  have hl : ‖(l : ℂ_[l])‖ < 1 := by
    rw [norm_l_Cl (l := l)]
    have h1l : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    exact inv_lt_one_of_one_lt₀ h1l
  obtain ⟨f, hf, hfr⟩ := KE.frob_fix_of_integral l (Fact.out : l.Prime) hl δ hZ
  obtain ⟨ξ, hξ, hd⟩ := tch_near (l := l) δ h1 f hf _ hfr le_rfl
  exact ⟨ξ, hξ, lt_of_le_of_lt hd hfr⟩

open Polynomial in
theorem kur_resClosed : ResClosed (MaximalUnramifiedExtension l) l := by
  classical
  intro P hPm hPd hPc
  have hrep : ∀ i : ℕ, ∃ ξ ∈ Tch l, ‖((P.coeff i : MaximalUnramifiedExtension l) : ℂ_[l]) - ξ‖ ≤ ‖(l : ℂ_[l])‖ :=
    fun i => kur_rep (l := l) (P.coeff i).2 (hPc i)
  choose g hgT hgd using hrep
  have hgR : ∀ i, g i ∈ Rmu l := fun i => KE.tch_mem_rmu (l := l) (hgT i)
  have hQ'deg : (∑ i : Fin P.natDegree, C (⟨g i, hgR i⟩ : Rmu l) * X ^ (i : ℕ)).degree
      < (P.natDegree : WithBot ℕ) := degree_sum_fin_lt _
  let Q' : Polynomial (Rmu l) :=
    X ^ P.natDegree + ∑ i : Fin P.natDegree, C (⟨g i, hgR i⟩ : Rmu l) * X ^ (i : ℕ)
  have hQ'm : Q'.Monic := monic_X_pow_add hQ'deg
  let Qc : Polynomial ℂ_[l] := Q'.map (algebraMap (Rmu l) ℂ_[l])
  have hQcdeg : Qc.degree ≠ 0 := by
    have hX : (X ^ P.natDegree : Polynomial (Rmu l)).degree = P.natDegree := degree_X_pow _
    have hQ'd : Q'.degree = P.natDegree := by
      rw [← hX]
      exact degree_add_eq_left_of_degree_lt (hX ▸ hQ'deg)
    rw [hQ'm.degree_map, hQ'd]
    first | exact_mod_cast hPd.ne' | simpa using hPd.ne'
  obtain ⟨δ, hδ⟩ := IsAlgClosed.exists_root Qc hQcdeg
  have hδint : IsIntegral (Rmu l) δ := ⟨Q', hQ'm, by rw [← eval_map]; exact hδ⟩
  have hQeval : ∀ y : ℂ_[l],
      Qc.eval y = y ^ P.natDegree + ∑ i : Fin P.natDegree, g i * y ^ (i : ℕ) := by
    intro y
    simp [Qc, Q', eval_map, Polynomial.eval₂_finsetSum] <;> rfl
  obtain ⟨ξ, hξT, hξd⟩ := tch_of_integral l δ hδint
  have hξ1 : ‖ξ‖ ≤ 1 := tch_norm_le (l := l) hξT
  have hξK : ξ ∈ MaximalUnramifiedExtension l := tch_mem_kur (l := l) hξT
  have hδ1 : ‖δ‖ ≤ 1 :=
    KE.norm_le_one_of_integral (fun r : Rmu l => rmu_norm_le (l := l) r.2) δ hδint
  have hQc : ∀ i, ‖Qc.coeff i‖ ≤ 1 := by
    intro i
    rw [coeff_map]
    exact rmu_norm_le (l := l) (Q'.coeff i).2
  set F : ℂ_[l] := ξ ^ P.natDegree + ∑ i : Fin P.natDegree, g i * ξ ^ (i : ℕ) with hF
  have hFK : F ∈ MaximalUnramifiedExtension l :=
    add_mem (pow_mem hξK _)
      (sum_mem fun i _ => mul_mem (tch_mem_kur (l := l) (hgT i)) (pow_mem hξK _))
  have hFlt : ‖F‖ < 1 := by
    have h := KE.norm_eval_sub_eval_le Qc hQc hξ1 hδ1
    rw [hQeval ξ, hδ.eq_zero, sub_zero, norm_sub_rev] at h
    exact lt_of_le_of_lt h hξd
  have hFl : ‖F‖ ≤ ‖(l : ℂ_[l])‖ := kur_discrete (l := l) hFK hFlt

  have hsum : ∀ (s : Finset (Fin P.natDegree)) (f : Fin P.natDegree → ℂ_[l]),
      (∀ i ∈ s, ‖f i‖ ≤ ‖(l : ℂ_[l])‖) → ‖∑ i ∈ s, f i‖ ≤ ‖(l : ℂ_[l])‖ := by
    intro s f
    refine Finset.induction_on s (fun _ => by simp) ?_
    intro a s ha ih h
    rw [Finset.sum_insert ha]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))
  have hS : ‖∑ i : Fin P.natDegree, (((P.coeff i : MaximalUnramifiedExtension l) : ℂ_[l]) - g i) * ξ ^ (i : ℕ)‖
      ≤ ‖(l : ℂ_[l])‖ := by
    apply hsum
    intro i _
    rw [norm_mul, norm_pow]
    calc ‖((P.coeff i : MaximalUnramifiedExtension l) : ℂ_[l]) - g i‖ * ‖ξ‖ ^ (i : ℕ) ≤ ‖(l : ℂ_[l])‖ * 1 :=
          mul_le_mul (hgd i) (pow_le_one₀ (norm_nonneg _) hξ1) (by positivity) (norm_nonneg _)
      _ = ‖(l : ℂ_[l])‖ := mul_one _
  refine ⟨⟨ξ, hξK⟩, tch_norm_le (l := l) hξT, ?_⟩
  have hPx : ((P.eval (⟨ξ, hξK⟩ : MaximalUnramifiedExtension l) : MaximalUnramifiedExtension l) : ℂ_[l]) =
      ξ ^ P.natDegree + ∑ i : Fin P.natDegree, ((P.coeff i : MaximalUnramifiedExtension l) : ℂ_[l]) * ξ ^ (i : ℕ) := by
    conv_lhs => rw [hPm.as_sum]
    simp [Polynomial.eval_finsetSum, Finset.sum_range]
  have hlK : ((l : MaximalUnramifiedExtension l) : ℂ_[l]) = (l : ℂ_[l]) := by simp
  show ‖((P.eval (⟨ξ, hξK⟩ : MaximalUnramifiedExtension l) : MaximalUnramifiedExtension l) : ℂ_[l])‖ ≤ ‖((l : MaximalUnramifiedExtension l) : ℂ_[l])‖
  rw [hPx, hlK]
  have hsplit : ξ ^ P.natDegree + ∑ i : Fin P.natDegree, ((P.coeff i : MaximalUnramifiedExtension l) : ℂ_[l]) * ξ ^ (i : ℕ)
      = (∑ i : Fin P.natDegree, (((P.coeff i : MaximalUnramifiedExtension l) : ℂ_[l]) - g i) * ξ ^ (i : ℕ)) + F := by
    rw [hF]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [hsplit]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hS hFl)

end ReciprocityTheory.ChartRestriction.L1
end
end
