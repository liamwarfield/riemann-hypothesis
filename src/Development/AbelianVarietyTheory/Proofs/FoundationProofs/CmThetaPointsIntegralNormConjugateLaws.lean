module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaCubeRelationIntegralFormalGroupBiadditive
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OmEqPullOfVacuum
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FstMemClosureNatCast
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormPrime
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionPointPadicAbscissaNormLeOne
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastMemOfPrimeDvdAbsNorm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PhAtMulByNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormPadicModelAbscissaLeOneOfTorsionCoprime
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormPadicModelAbscissaLeOneOfTorsionCoprime
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.TorsionAbscissa

theorem norm_xAt_le_of_mul : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → ∀ (N : ℕ) (v : ℂ), 0 < N → Nat.Coprime N p → (N : ℂ) * v ∈ g.abelian₂ → v ∉ g.abelian₂ → ‖GlobalTheory.EvenTheta.xAt g v‖ ≤ 1 := by
  intro D p _ cc δ g hg N v hN hcop hNv hv
  exact norm_xAt_le D p cc δ g hg v ⟨hv, N, hN, hcop, hNv⟩

end GlobalTheory.TorsionAbscissa
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormPadicModelAbscissaLeOneOfTorsionCoprimeStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_padicModelAbscissa_le_one_of_torsion_coprime : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → ∀ (N : ℕ) (v : ℂ), 0 < N → Nat.Coprime N p → (N : ℂ) * v ∈ g.abelian₂ → v ∉ g.abelian₂ → ‖GlobalTheory.EvenTheta.xAt g v‖ ≤ 1 := by
  first | exact @GlobalTheory.TorsionAbscissa.norm_xAt_le_of_mul | exact GlobalTheory.TorsionAbscissa.norm_xAt_le_of_mul | (intros; apply GlobalTheory.TorsionAbscissa.norm_xAt_le_of_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarMulSqEqProdKernelQuotients
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarMulSqEqProdKernelQuotients
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

open Filter Topology

noncomputable section

namespace GlobalTheory.EvenTheta.MulLat

variable {Λ : AddSubgroup ℂ}

theorem trFac_ne (z ω : ℂ) : GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ≠ 0 := Complex.exp_ne_zero _

theorem differentiable_trFac (ω : ℂ) : Differentiable ℂ fun z => GlobalTheory.EvenTheta.Fibres.trFac Λ z ω := by
  unfold GlobalTheory.EvenTheta.Fibres.trFac
  fun_prop

theorem exists_sg_mul_sq (h : IsLat Λ) {β : ℂ} (hβ : ∀ ω ∈ Λ, β * ω ∈ Λ) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ ∀ z, sgStar Λ (β * z) ^ 2 = sgStar Λ z ^ 2 * G z := by
  have hσ := h.differentiable
  have hne : ∀ z ∉ Λ, sgStar Λ z ≠ 0 := fun z hz => (h.sg_eq_zero z).not.2 hz
  set u := dslope (sgStar Λ) 0 with hu_def
  have hU : Differentiable ℂ u :=
    differentiableOn_univ.1 ((Complex.differentiableOn_dslope Filter.univ_mem).2 hσ.differentiableOn)
  have hu0 : u 0 = 1 := by
    rw [hu_def, dslope_same, (GlobalTheory.OddTheta.sgStar_laws Λ h).1.2.1]
  have eu : ∀ z, sgStar Λ z = z * u z := fun z => by
    have := sub_smul_dslope (sgStar Λ) 0 z
    rw [(h.sg_eq_zero 0).2 Λ.zero_mem] at this
    simpa using this.symm
  refine exists_entire_of_locally_dvd (F := fun z => sgStar Λ (β * z) ^ 2) (S := fun z => sgStar Λ z ^ 2)
    (h.dense_compl.mono fun z hz => pow_ne_zero 2 (hne z hz)) fun w => ?_
  by_cases hw : w ∈ Λ
  · have hT := differentiable_trFac (Λ := Λ) w
    have hT' := differentiable_trFac (Λ := Λ) (β * w)
    set D : ℂ → ℂ := fun z => u (z - w) ^ 2 * GlobalTheory.EvenTheta.Fibres.trFac Λ (β * (z - w)) (β * w) ^ 2
      with hD_def
    have hD : Differentiable ℂ D := by
      rw [hD_def]
      have h1 : Differentiable ℂ fun z => u (z - w) := hU.comp (by fun_prop)
      have h2 : Differentiable ℂ fun z => GlobalTheory.EvenTheta.Fibres.trFac Λ (β * (z - w)) (β * w) :=
        hT'.comp (by fun_prop)
      fun_prop
    have hD0 : D w ≠ 0 := by
      simp only [hD_def, sub_self, hu0]
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 (trFac_ne _ _))
    set N : ℂ → ℂ := fun z => β ^ 2 * u (β * (z - w)) ^ 2 * GlobalTheory.EvenTheta.Fibres.trFac Λ (z - w) w ^ 2
      with hN_def
    have hN : Differentiable ℂ N := by
      rw [hN_def]
      have h1 : Differentiable ℂ fun z => u (β * (z - w)) := hU.comp (by fun_prop)
      have h2 : Differentiable ℂ fun z => GlobalTheory.EvenTheta.Fibres.trFac Λ (z - w) w :=
        hT.comp (by fun_prop)
      fun_prop
    refine ⟨fun z => N z / D z, (hN.analyticAt w).div (hD.analyticAt w) hD0, ?_⟩
    filter_upwards [hD.continuous.continuousAt.eventually_ne hD0] with z hz
    have hz1 : u (z - w) ≠ 0 := fun h0 => hz (by simp [hD_def, h0])
    have e1 := GlobalTheory.EvenTheta.Fibres.sg_sq h hw (z - w)
    have e2 := GlobalTheory.EvenTheta.Fibres.sg_sq h (hβ w hw) (β * (z - w))
    rw [sub_add_cancel] at e1
    rw [show β * (z - w) + β * w = β * z by ring] at e2
    have t1 := trFac_ne (Λ := Λ) (z - w) w
    have t2 := trFac_ne (Λ := Λ) (β * (z - w)) (β * w)
    simp only [hN_def, hD_def]
    rw [eu (z - w)] at e1
    rw [eu (β * (z - w))] at e2
    have hz' : u (z - w) ^ 2 * GlobalTheory.EvenTheta.Fibres.trFac Λ (β * (z - w)) (β * w) ^ 2 ≠ 0 := hz
    rw [mul_div_assoc', eq_div_iff hz']
    linear_combination u (z - w) ^ 2 * e2 - β ^ 2 * u (β * (z - w)) ^ 2 * e1
  · refine ⟨fun z => sgStar Λ (β * z) ^ 2 / sgStar Λ z ^ 2,
      (((hσ.comp (by fun_prop : Differentiable ℂ fun z => β * z)).pow 2).analyticAt w).div
        ((hσ.analyticAt w).pow 2) (pow_ne_zero 2 (hne w hw)), ?_⟩
    filter_upwards [hσ.continuous.continuousAt.eventually_ne (hne w hw)] with y hy
    field_simp

end GlobalTheory.EvenTheta.MulLat

namespace GlobalTheory.EvenTheta.MulLat

variable {Λ : AddSubgroup ℂ}

theorem val_zero (h : IsLat Λ) {β : ℂ} {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (eG : ∀ z, sgStar Λ (β * z) ^ 2 = sgStar Λ z ^ 2 * G z) : G 0 = β ^ 2 := by
  have hσ := h.differentiable
  set u := dslope (sgStar Λ) 0 with hu_def
  have hU : Differentiable ℂ u :=
    differentiableOn_univ.1 ((Complex.differentiableOn_dslope Filter.univ_mem).2 hσ.differentiableOn)
  have hu0 : u 0 = 1 := by
    rw [hu_def, dslope_same, (GlobalTheory.OddTheta.sgStar_laws Λ h).1.2.1]
  have eu : ∀ z, sgStar Λ z = z * u z := fun z => by
    have := sub_smul_dslope (sgStar Λ) 0 z
    rw [(h.sg_eq_zero 0).2 Λ.zero_mem] at this
    simpa using this.symm
  have hGc := hG.continuous
  have hUc := hU.continuous
  have key := congrFun (Continuous.ext_on (dense_compl_singleton (0 : ℂ))
    (f := fun z => u z ^ 2 * G z) (g := fun z => β ^ 2 * u (β * z) ^ 2) (by fun_prop)
    (by fun_prop) fun z hz => by
      have hz : z ≠ 0 := hz
      have e := eG z
      rw [eu, eu z] at e
      refine mul_left_cancel₀ (pow_ne_zero 2 hz) ?_
      beta_reduce
      linear_combination -e) 0
  simpa [hu0] using key

theorem sg_mul_sq : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ (β : ℂ) (k : ℕ), (∀ ω ∈ Λ, β * ω ∈ Λ) → β * starRingEnd ℂ β = ((k + 1 : ℕ) : ℂ) → ∃ Q : Fin k → ℂ, (∀ i, Q i ∉ Λ ∧ β * Q i ∈ Λ) ∧ ∀ z, sgStar Λ (β * z) ^ 2 = β ^ 2 * sgStar Λ z ^ 2 * ∏ i, sqTh Λ (Q i) z := by
  intro Λ h β k hβ hN
  have hβ0 : β ≠ 0 := by
    rintro rfl
    norm_num at hN
    exact Nat.cast_add_one_ne_zero k hN.symm
  have hσ := h.differentiable
  have hσc := hσ.continuous
  have hne : ∀ z ∉ Λ, sgStar Λ z ≠ 0 := fun z hz => (h.sg_eq_zero z).not.2 hz
  obtain ⟨G, hG, eG⟩ := exists_sg_mul_sq h hβ
  have hGc := hG.continuous
  have hG0 := val_zero h hG eG
  have hev : ∀ z, G (-z) = G z := fun z => by
    refine congrFun (Continuous.ext_on h.dense_compl (f := fun z => G (-z)) (by fun_prop) hGc
      fun z hz => ?_) z
    refine mul_left_cancel₀ (pow_ne_zero 2 (hne z hz)) ?_
    have h1 := eG (-z)
    rw [h.sg_neg, neg_sq, mul_neg, h.sg_neg, neg_sq] at h1
    exact h1.symm.trans (eG z)
  have hlaw : ∀ ω ∈ Λ, ∀ z, G (z + ω) * GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ^ (2 * k) = G z := by
    intro ω hω z
    have hTc : Continuous fun z => GlobalTheory.EvenTheta.Fibres.trFac Λ z ω :=
      (differentiable_trFac ω).continuous
    refine congrFun (Continuous.ext_on h.dense_compl
      (f := fun z => G (z + ω) * GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ^ (2 * k)) (by fun_prop) hGc
      fun z hz => ?_) z
    refine mul_left_cancel₀ (pow_ne_zero 2 (hne z hz)) ?_
    have ea := GlobalTheory.EvenTheta.Fibres.sg_sq h hω z
    have eb := GlobalTheory.EvenTheta.Fibres.sg_sq h (hβ ω hω) (β * z)
    rw [GlobalTheory.EvenTheta.Fibres.trFac_mul hN] at eb
    have egz := eG z
    have egw := eG (z + ω)
    rw [mul_add] at egw
    beta_reduce
    linear_combination egz + eb - GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ^ (2 * k + 2) * egw -
      G (z + ω) * GlobalTheory.EvenTheta.Fibres.trFac Λ z ω ^ (2 * k) * ea
  obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.EvenTheta.exists_eq_prod_sqTh Λ h k (fun z => G z / β ^ 2)
    (hG.div_const _) (fun z => by simp only [hev]) (by simp only [hG0]; exact div_self (pow_ne_zero 2 hβ0))
    (fun ω hω z => GlobalTheory.EvenTheta.Fibres.law_of_fac h (F := fun z => G z / β ^ 2) (k := k) hω z (by
      show G (z + ω) / β ^ 2 * _ = G z / β ^ 2
      rw [div_mul_eq_mul_div, hlaw ω hω z]))
  have hfac : ∀ z, sgStar Λ (β * z) ^ 2 = β ^ 2 * sgStar Λ z ^ 2 * ∏ i, sqTh Λ (Q i) z := fun z => by
    rw [eG z, ← hQe z]
    field_simp
  refine ⟨Q, fun i => ⟨hQ i, ?_⟩, hfac⟩
  refine (h.sg_eq_zero _).1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 ?_)
  rw [hfac, Finset.prod_eq_zero (Finset.mem_univ i)
    ((h.sqTh_eq_zero (hQ i) _).2 (Or.inr (by rw [sub_self]; exact Λ.zero_mem))), mul_zero]

end GlobalTheory.EvenTheta.MulLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarMulSqEqProdKernelQuotientsStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sigmaStar_mul_sq_eq_prod_kernel_quotients : ∀ (Λ : AddSubgroup ℂ), IsLat Λ → ∀ (β : ℂ) (k : ℕ), (∀ ω ∈ Λ, β * ω ∈ Λ) → β * starRingEnd ℂ β = ((k + 1 : ℕ) : ℂ) → ∃ Q : Fin k → ℂ, (∀ i, Q i ∉ Λ ∧ β * Q i ∈ Λ) ∧ ∀ z, sgStar Λ (β * z) ^ 2 = β ^ 2 * sgStar Λ z ^ 2 * ∏ i, sqTh Λ (Q i) z := by
  first | exact @GlobalTheory.EvenTheta.MulLat.sg_mul_sq | exact GlobalTheory.EvenTheta.MulLat.sg_mul_sq | (intros; apply GlobalTheory.EvenTheta.MulLat.sg_mul_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpMvPhiSeriesSubNsmulEqDiv
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpMvPhiSeriesSubNsmulEqDiv
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.ExpLogShift

open MvPowerSeries

theorem expMv_phAt_sub_nsmul : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (h : PowerSeries ℂ_[p]) (n : ℕ), PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1 → PowerSeries.constantCoeff h = 0 → MvPowerSeries.constantCoeff ((g.phAt h : MvPowerSeries Unit ℂ_[p]) - MvPowerSeries.C (n : ℂ_[p]) * g.phAt (GL3Theta.Xv ())) = 0 ∧ expMv ((g.phAt h : MvPowerSeries Unit ℂ_[p]) - MvPowerSeries.C (n : ℂ_[p]) * g.phAt (GL3Theta.Xv ())) = ((PowerSeries.subst h (ePhi1 g.lam g.abelian₂ g.C g.wq))⁻¹ * ePhi1 g.lam g.abelian₂ g.C g.wq ^ n : PowerSeries ℂ_[p]) := by
  intro p _ g h n hE hh
  have exp_add {f g : MvPowerSeries Unit ℂ_[p]} (hf : constantCoeff f = 0)
      (hg : constantCoeff g = 0) : expMv (f + g) = expMv f * expMv g := by
    rw [GlobalTheory.ExpLogMv.expMv_eq_subst hf, GlobalTheory.ExpLogMv.expMv_eq_subst hg,
      GlobalTheory.ExpLogMv.expMv_eq_subst (by simp [hf, hg])]
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_add hf hg
  have exp_zero : expMv (0 : MvPowerSeries Unit ℂ_[p]) = 1 := by
    rw [GlobalTheory.ExpLogMv.expMv_eq_subst (by simp)]
    exact ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.exp_zero
  have cc_ph : PowerSeries.constantCoeff g.ph = 0 := by
    have ht := (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul p Unit _ hE).1
    show constantCoeff (-GL3Theta.logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)) = 0
    rw [map_neg, ht, neg_zero]
  have cc_phAt {y : MvPowerSeries Unit ℂ_[p]} (hy : constantCoeff y = 0) :
      constantCoeff (g.phAt y) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hy _ cc_ph
  have exp_sum {ι : Type} (s : Finset ι) {f : ι → MvPowerSeries Unit ℂ_[p]}
      (hf : ∀ i, constantCoeff (f i) = 0) : expMv (∑ i ∈ s, f i) = ∏ i ∈ s, expMv (f i) := by
    induction s using Finset.induction_on with
    | empty => simpa using exp_zero
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, exp_add (hf i) (by simp [map_sum, hf]), ih]
  have subst_exp {a : Unit → MvPowerSeries Unit ℂ_[p]} (ha : ∀ i, constantCoeff (a i) = 0)
      {f : MvPowerSeries Unit ℂ_[p]} (hf : constantCoeff f = 0) : subst a (expMv f) = expMv (subst a f) := by
    have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
    rw [GlobalTheory.ExpLogMv.expMv_eq_subst hf, GlobalTheory.ExpLogMv.expMv_eq_subst (constantCoeff_subst_eq_zero hs ha hf)]
    rw [PowerSeries.subst_def, subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hf).const hs]
    rfl
  have inv_ePhi1 {y : MvPowerSeries Unit ℂ_[p]} (hy : constantCoeff y = 0) :
      (PowerSeries.subst y (ePhi1 g.lam g.abelian₂ g.C g.wq))⁻¹ = expMv (g.phAt y) := by
    have hs : HasSubst (fun _ : Unit => y) := hasSubst_of_constantCoeff_zero fun _ => hy
    have ht := congrArg (subst (fun _ : Unit => y)) (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul p Unit _ hE).2
    rw [subst_mul hs, subst_exp (f := -GL3Theta.logMv (ePhi1 g.lam g.abelian₂ g.C g.wq)) (fun _ => hy) cc_ph, ← coe_substAlgHom hs (R := ℂ_[p]), map_one,
      coe_substAlgHom] at ht
    have h1 : constantCoeff (PowerSeries.subst y (ePhi1 g.lam g.abelian₂ g.C g.wq)) ≠ 0 := by
      rw [ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.constantCoeff_psubst hy, hE]; exact one_ne_zero
    rw [MvPowerSeries.inv_eq_iff_mul_eq_one h1]
    exact ht
  have hh' : MvPowerSeries.constantCoeff (h : MvPowerSeries Unit ℂ_[p]) = 0 := hh
  have hX : MvPowerSeries.constantCoeff (GL3Theta.Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := by
    simp [GL3Theta.Xv]
  have ha : MvPowerSeries.constantCoeff (g.phAt (h : MvPowerSeries Unit ℂ_[p])) = 0 :=
    cc_phAt hh'
  have hb : MvPowerSeries.constantCoeff (g.phAt (GL3Theta.Xv () : MvPowerSeries Unit ℂ_[p])) = 0 :=
    cc_phAt hX
  refine ⟨by simp [map_sub, map_mul, ha, hb], ?_⟩
  set b : MvPowerSeries Unit ℂ_[p] := g.phAt (GL3Theta.Xv ()) with hbdef
  set F : PowerSeries ℂ_[p] := ePhi1 g.lam g.abelian₂ g.C g.wq with hF

  have hbph : b = (g.ph : MvPowerSeries Unit ℂ_[p]) := by
    show PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[p]) g.ph = g.ph
    rw [← PowerSeries.map_algebraMap_eq_subst_X]; simp

  have hbF : expMv b * (F : MvPowerSeries Unit ℂ_[p]) = 1 := by
    rw [hbph]; exact (GlobalTheory.ExpLogMv.expMv_neg_logMv_mul p Unit _ hE).2
  have hnb : MvPowerSeries.constantCoeff (-b) = 0 := by simp [hb]

  have hneg : expMv (-b) = (F : MvPowerSeries Unit ℂ_[p]) := by
    have h0 : expMv b * expMv (-b) = 1 := by
      rw [← exp_add hb hnb, add_neg_cancel, exp_zero]
    calc expMv (-b) = expMv (-b) * (expMv b * (F : MvPowerSeries Unit ℂ_[p])) := by rw [hbF, mul_one]
      _ = (expMv b * expMv (-b)) * F := by ring
      _ = F := by rw [h0, one_mul]
  have hsum : (g.phAt (h : MvPowerSeries Unit ℂ_[p])) - MvPowerSeries.C (n : ℂ_[p]) * b =
      g.phAt (h : MvPowerSeries Unit ℂ_[p]) + ∑ _i ∈ Finset.range n, -b := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, sub_eq_add_neg, ← neg_mul]
    congr 1
    rw [neg_mul, mul_neg]
    congr 1
  have hsum0 : MvPowerSeries.constantCoeff (∑ _i ∈ Finset.range n, -b) = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]; simp [hb]
  rw [hsum, exp_add ha hsum0,
    exp_sum _ (fun _ => hnb), Finset.prod_const, Finset.card_range, hneg,
    ← inv_ePhi1 hh']

end GlobalTheory.ExpLogShift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpMvPhiSeriesSubNsmulEqDivStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expMv_phiSeries_sub_nsmul_eq_div : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p) (h : PowerSeries ℂ_[p]) (n : ℕ), PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1 → PowerSeries.constantCoeff h = 0 → MvPowerSeries.constantCoeff ((g.phAt h : MvPowerSeries Unit ℂ_[p]) - MvPowerSeries.C (n : ℂ_[p]) * g.phAt (GL3Theta.Xv ())) = 0 ∧ expMv ((g.phAt h : MvPowerSeries Unit ℂ_[p]) - MvPowerSeries.C (n : ℂ_[p]) * g.phAt (GL3Theta.Xv ())) = ((PowerSeries.subst h (ePhi1 g.lam g.abelian₂ g.C g.wq))⁻¹ * ePhi1 g.lam g.abelian₂ g.C g.wq ^ n : PowerSeries ℂ_[p]) := by
  first | exact @GlobalTheory.ExpLogShift.expMv_phAt_sub_nsmul | exact GlobalTheory.ExpLogShift.expMv_phAt_sub_nsmul | (intros; apply GlobalTheory.ExpLogShift.expMv_phAt_sub_nsmul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralOfSqIntegralOdd
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralOfSqIntegralOdd
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem norm_two_Cp_eq_one (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) : ‖(2 : ℂ_[p])‖ = 1 := by
  have h : ((2 : ℕ) : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] ((2 : ℕ) : ℚ_[p]) := (map_natCast _ 2).symm
  have h2 : (2 : ℂ_[p]) = ((2 : ℕ) : ℂ_[p]) := by norm_num
  rw [h2, h, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.coprime_primes (Fact.out) Nat.prime_two).2 hp

theorem intSer_of_sq (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (H : PowerSeries ℂ_[p])
    (h0 : PowerSeries.constantCoeff H = 1) (hH : IntSer (H ^ 2)) : IntSer H := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [PowerSeries.coeff_zero_eq_constantCoeff, h0]
    set f : ℕ × ℕ → ℂ_[p] := fun q => PowerSeries.coeff q.1 H * PowerSeries.coeff q.2 H with hf
    have hsq : PowerSeries.coeff n (H ^ 2) = ∑ q ∈ Finset.HasAntidiagonal.antidiagonal n, f q := by
      rw [pow_two, PowerSeries.coeff_mul]
    have m1 : ((0 : ℕ), n) ∈ Finset.HasAntidiagonal.antidiagonal n := by simp
    have m2 : (n, (0 : ℕ)) ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (0, n) := by
      simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, add_zero, and_true, ne_eq, Prod.mk.injEq]
      omega
    have c0 : PowerSeries.coeff 0 H = 1 := by rw [PowerSeries.coeff_zero_eq_constantCoeff]; exact h0
    set S := ∑ q ∈ ((Finset.HasAntidiagonal.antidiagonal n).erase (0, n)).erase (n, 0), f q with hS
    have hdec : PowerSeries.coeff n (H ^ 2) = 2 * PowerSeries.coeff n H + S := by
      rw [hsq, ← Finset.add_sum_erase _ _ m1, ← Finset.add_sum_erase _ _ m2]
      simp only [hf, c0, one_mul, mul_one]
      ring
    have hSle : ‖S‖ ≤ 1 := by
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one ?_
      intro q hq
      simp only [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal, ne_eq] at hq
      obtain ⟨hq1, hq2, hq3⟩ := hq
      obtain ⟨a, b⟩ := q
      simp only [Prod.mk.injEq, Finset.HasAntidiagonal.mem_antidiagonal] at hq1 hq2 hq3
      have ha : a < n := by omega
      have hb : b < n := by omega
      simp only [hf, norm_mul]
      exact mul_le_one₀ (ih a ha) (norm_nonneg _) (ih b hb)
    have h2 : ‖2 * PowerSeries.coeff n H‖ = ‖PowerSeries.coeff n H‖ := by
      rw [norm_mul, norm_two_Cp_eq_one p hp, one_mul]
    have e : 2 * PowerSeries.coeff n H = PowerSeries.coeff n (H ^ 2) - S := by rw [hdec]; ring
    rw [← h2, e]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hH n) ?_)
    rw [norm_neg]; exact hSle

theorem intSer_of_sq_main : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ H : PowerSeries ℂ_[p],
    PowerSeries.constantCoeff H = 1 → IntSer (H ^ 2) → IntSer H :=
  fun p _ hp H h0 hH => intSer_of_sq p hp H h0 hH

end GlobalTheory.EvenTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicComplexIntegralOfSqIntegralOddStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicComplex_integral_of_sq_integral_odd : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ H : PowerSeries ℂ_[p], PowerSeries.constantCoeff H = 1 → IntSer (H ^ 2) → IntSer H := by
  first | exact @GlobalTheory.EvenTheta.intSer_of_sq_main | exact GlobalTheory.EvenTheta.intSer_of_sq_main | (intros; apply GlobalTheory.EvenTheta.intSer_of_sq_main <;> assumption)
end
end

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

noncomputable section
namespace GlobalTheory.CMNormPhi

open PowerSeries

variable {p : ℕ} [Fact p.Prime]

theorem intSer_iff' {f : PowerSeries ℂ_[p]} : IntegralMv f ↔ IntSer f := by
  constructor
  · intro h n; exact h (Finsupp.single () n)
  · intro h n
    have := h (n ())
    rwa [PowerSeries.coeff_def (s := n) rfl] at this

theorem intSer_sq_of_eq (h F f L : PowerSeries ℂ_[p]) (τ : ℂ_[p]) (n : ℕ) (hh : IntSer h)
    (hh0 : constantCoeff h = 0) (hh1 : coeff 1 h = τ) (hτ : ‖τ‖ = 1) (hF : constantCoeff F = 1)
    (hL : IntSer L) (hL0 : constantCoeff L = 1)
    (e : h ^ 2 * F ^ 2 = C (τ ^ 2) * X ^ 2 * (f ^ n) ^ 2 * L) : IntSer ((F⁻¹ * f ^ n) ^ 2) := by
  obtain ⟨v, rfl⟩ := (PowerSeries.X_dvd_iff).2 hh0
  have hv : IntSer v := fun m => by simpa [PowerSeries.coeff_succ_X_mul] using hh (m + 1)
  have e' : v ^ 2 * F ^ 2 = C (τ ^ 2) * (f ^ n) ^ 2 * L := by
    have hX : (X : PowerSeries ℂ_[p]) ^ 2 ≠ 0 := pow_ne_zero _ X_ne_zero
    apply mul_left_cancel₀ hX
    linear_combination e
  have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ
  have hFi : F⁻¹ * F = 1 := PowerSeries.inv_mul_cancel _ (by rw [hF]; exact one_ne_zero)
  have hLi : L * L⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by rw [hL0]; exact one_ne_zero)
  have hc : C (τ⁻¹ ^ 2) * C (τ ^ 2) = (1 : PowerSeries ℂ_[p]) := by
    rw [← map_mul, ← mul_pow, inv_mul_cancel₀ hτ0, one_pow, map_one]
  have key : (F⁻¹ * f ^ n) ^ 2 = C (τ⁻¹ ^ 2) * v ^ 2 * L⁻¹ := by
    linear_combination (-(C (τ⁻¹ ^ 2)) * F⁻¹ ^ 2 * L⁻¹) * e' +
      (C (τ⁻¹ ^ 2) * v ^ 2 * L⁻¹ * (F⁻¹ * F + 1)) * hFi -
      (F⁻¹ ^ 2 * (f ^ n) ^ 2 * L * L⁻¹) * hc - (F⁻¹ ^ 2 * (f ^ n) ^ 2) * hLi
  obtain ⟨hr, -, hC, -, hinv, -⟩ := GlobalTheory.EvenTheta.SerRing.series_ring_laws p
  rw [key]
  refine (hr _ _ (hr _ _ ((hC _).2 ?_) (by rw [sq]; exact (hr _ _ hv hv).2.2)).2.2
    (hinv L hL (by rw [hL0, norm_one]))).2.2
  rw [norm_pow, norm_inv, hτ]; simp

theorem atU_prod' (g : GL3Theta.G1 p) {ι : Type} (s : Finset ι) {F : ι → ℂ → ℂ} (hF : ∀ i, AlgEnt (F i)) :
    AlgEnt (fun z => ∏ i ∈ s, F i z) ∧ g.atU (fun z => ∏ i ∈ s, F i z) = ∏ i ∈ s, g.atU (F i) := by
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨h1, h2⟩ := (GlobalTheory.SerTransport.transport p g).2.1 1 (one_mem _)
    simp only [Finset.prod_empty]
    refine ⟨h1, ?_⟩
    rw [h2, lamC, dite_eq_left (one_mem _)]
    exact congrArg C (map_one g.lam)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    rw [← ih.2]
    exact ((GlobalTheory.SerTransport.transport p g).1 _ _ (hF a) ih.1).1

theorem phAt_mulBy_norm : ∀ (D : D7), GL3Theta.endInt D → GL3Theta.addInt D → ∀ (p : ℕ) [Fact p.Prime]
    (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p), GL3Theta.At D cc δ g → p ≠ 2 →
    ∀ a : 𝓞 D.host.K, Nat.Coprime (Algebra.norm ℤ a).natAbs p →
    GL3Theta.Simeq (g.phAt (g.mulBy (GL3Theta.tauK D g.lam (a : D.host.K)) (GL3Theta.Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (GL3Theta.tauK D g.lam (a : D.host.K) * GL3Theta.tauKc D g.lam (a : D.host.K)) *
        g.phAt (GL3Theta.Xv ())) := by
  intro D hend _ p _ cc δ g hg hp a hcop
  have hg' := hg
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, hdisc, -, hst⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat hdisc hst h2 h3 hwp huse
  have hlat' : IsLat g.abelian₂ := hlat
  have halgσ : AlgEnt (sgStar g.abelian₂) := by
    have e : U1 g.abelian₂ 0 (sgStar g.abelian₂) = sgStar g.abelian₂ := by funext z; simp [U1]
    have := huse 0 ⟨1, one_pos, by simp⟩
    rw [e] at this
    exact ⟨hlat'.differentiable, this⟩

  set β : ℂ := D.host.φ₀ ((a : D.host.K) : D.host.E) with hβdef
  have hβQ : β ∈ Qbar := Formalism.MainNotions.Ext.test_vector_mem_schwartz_bruhat D _
  have hβst : ∀ ω ∈ g.abelian₂, β * ω ∈ g.abelian₂ := hst a
  let a' : 𝓞 D.host.K := ⟨Formalism.MainNotions.Ext.conjK D (a : D.host.K),
    (RingOfIntegers.isIntegral_coe a).map (Formalism.MainNotions.Ext.conjK D).toIntAlgHom⟩
  have hconj : D.host.φ₀ ((a' : D.host.K) : D.host.E) = starRingEnd ℂ β := by
    show D.host.φ₀ ((Formalism.MainNotions.Ext.conjK D (a : D.host.K) : D.host.K) : D.host.E) = _
    rw [Formalism.MainNotions.Ext.conjK_coe]
    exact D.host.conjE_apply D.host.φ₀ _
  have hN : β * starRingEnd ℂ β = ((Algebra.norm ℤ a : ℤ) : ℂ) := by
    have h := Formalism.MainNotions.UnusedSlot33.HK.norm_int D.host a
    rw [Algebra.intNorm_eq_norm] at h
    have h' := congrArg D.host.φ₀ h
    have hc : D.host.φ₀ (D.host.conj ((a : D.host.K) : D.host.E)) = starRingEnd ℂ β :=
      D.host.conjE_apply D.host.φ₀ _
    rw [map_intCast, map_mul, hc] at h'
    exact h'.symm
  have hnn : 0 ≤ (Algebra.norm ℤ a : ℤ) := by
    have e1 : ((Algebra.norm ℤ a : ℤ) : ℂ) = ((Complex.normSq β : ℝ) : ℂ) := by
      rw [← hN, Complex.mul_conj]
    have e2 : ((Algebra.norm ℤ a : ℤ) : ℝ) = Complex.normSq β := by exact_mod_cast e1
    have := Complex.normSq_nonneg β
    rw [← e2] at this
    exact_mod_cast this
  have hn0 : (Algebra.norm ℤ a).natAbs ≠ 0 := by
    intro h0
    rw [h0, Nat.coprime_zero_left] at hcop
    exact (Fact.out : p.Prime).one_lt.ne' hcop
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  have hnk : (Algebra.norm ℤ a : ℤ) = ((k + 1 : ℕ) : ℤ) := by
    have := Int.natAbs_of_nonneg hnn
    rw [hk] at this
    exact this.symm
  have hβN : β * starRingEnd ℂ β = ((k + 1 : ℕ) : ℂ) := by rw [hN, hnk]; push_cast; ring
  have hcop' : Nat.Coprime (k + 1) p := by
    have := hcop
    rwa [hk] at this

  set τ := GL3Theta.tauK D g.lam (a : D.host.K) with hτdef
  have hτβ : τ = lamC g.lam β := rfl
  have htn : τ * GL3Theta.tauKc D g.lam (a : D.host.K) = ((k + 1 : ℕ) : ℂ_[p]) := by
    rw [hτdef, Formalism.MainNotions.Ext.CutA.tau_norm, hnk]; push_cast; ring
  have hτ1 : ‖τ‖ ≤ 1 := by
    rw [hτβ, hβdef, ← Formalism.MainNotions.Ext.tauKp_apply]; exact PI.OkpW.norm_tau_le _ a
  have hτc1 : ‖GL3Theta.tauKc D g.lam (a : D.host.K)‖ ≤ 1 := by
    have e : GL3Theta.tauKc D g.lam (a : D.host.K) = Formalism.MainNotions.Ext.tauKp D g.lam (a' : D.host.K) := by
      rw [Formalism.MainNotions.Ext.tauKp_apply]
      show _ = lamC g.lam (D.host.φ₀ ((Formalism.MainNotions.Ext.conjK D (a : D.host.K) : D.host.K) : D.host.E))
      rw [Formalism.MainNotions.Ext.conjK_coe]; rfl
    rw [e]; exact PI.OkpW.norm_tau_le _ a'
  have hn1 : ‖((k + 1 : ℕ) : ℂ_[p])‖ = 1 := by
    rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap']
    exact Padic.norm_natCast_eq_one_iff.2 hcop'.symm
  have hτu : ‖τ‖ = 1 := by
    have := congrArg norm htn
    rw [norm_mul, hn1] at this
    nlinarith [norm_nonneg τ, norm_nonneg (GL3Theta.tauKc D g.lam (a : D.host.K))]

  obtain ⟨hmul, hconst, -, hscale⟩ := GlobalTheory.SerTransport.transport p g
  obtain ⟨h, hh, hh0, hh1, hsub⟩ := hscale hok β hβQ
  obtain ⟨hu, hw, hw0, hE, hσ⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc
  have hhI : IntSer h := by
    have := hend p cc δ g hg' (τ, GL3Theta.tauKc D g.lam (a : D.host.K)) (subset_closure ⟨a, rfl⟩)
    have h' : IntegralMv (h : MvPowerSeries Unit ℂ_[p]) := by rw [hh]; exact this
    exact intSer_iff'.1 h'

  set f := ePhi1 g.lam g.abelian₂ g.C g.wq with hfdef
  have hε0 : ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) ≠ 0 := Units.ne_zero _
  obtain ⟨Q, hQ, hfac⟩ := GlobalTheory.T.sigmaStar_mul_sq_eq_prod_kernel_quotients g.abelian₂ hlat' β k hβst hβN
  have hLaQ : ∀ i, ((k + 1 : ℕ) : ℂ) * Q i ∈ g.abelian₂ := fun i => by
    have e : ((k + 1 : ℕ) : ℂ) * Q i = D.host.φ₀ ((a' : D.host.K) : D.host.E) * (β * Q i) := by
      rw [hconj, ← hβN]; ring
    rw [e]; exact hst a' _ (hQ i).2
  have hsq : ∀ i, AlgEnt (sqTh g.abelian₂ (Q i)) ∧
      g.atU (sqTh g.abelian₂ (Q i)) = f ^ 2 * lineSer g.wq⁻¹ (xAt g (Q i)) :=
    fun i => GlobalTheory.EvenTheta.Param.sqTh_atU p g hok.2.1 hlat' h2 h3 halgσ (Q i) (hQ i).1
      (hwp _ ⟨k + 1, Nat.succ_pos k, hLaQ i⟩ (hQ i).1).1
  have hx : ∀ i, ‖xAt g (Q i)‖ ≤ 1 := fun i =>
    GlobalTheory.T.norm_padicModelAbscissa_le_one_of_torsion_coprime D p cc δ g hg' (k + 1) (Q i) (Nat.succ_pos k) hcop' (hLaQ i) (hQ i).1
  obtain ⟨hr, -, hC, hXI, -, -⟩ := GlobalTheory.EvenTheta.SerRing.series_ring_laws p
  have hlineI : ∀ x : ℂ_[p], ‖x‖ ≤ 1 → IntSer (lineSer g.wq⁻¹ x) := fun x hx =>
    (hr _ _ hw ((hr _ _ ((hC x).2 hx) (by rw [sq]; exact (hr _ _ hXI hXI).2.2)).2.2)).2.1
  have hLI : IntSer (∏ i, lineSer g.wq⁻¹ (xAt g (Q i))) :=
    Finset.prod_induction _ IntSer (fun _ _ h1 h2 => (hr _ _ h1 h2).2.2)
      (fun n => by rw [coeff_one]; split_ifs <;> simp) (fun i _ => hlineI _ (hx i))
  have hL0 : constantCoeff (∏ i, lineSer g.wq⁻¹ (xAt g (Q i))) = 1 := by
    rw [map_prod]; refine Finset.prod_eq_one fun i _ => ?_
    simp only [lineSer, map_sub, map_mul, map_pow, constantCoeff_X, hw0, constantCoeff_C]; simp

  have hA := hsub _ halgσ
  have hs : HasSubst h := HasSubst.of_constantCoeff_zero' hh0
  have lhs : g.atU (fun z => sgStar g.abelian₂ (β * z) ^ 2) =
      (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * h * subst h f) ^ 2 := by
    have e := (hmul _ _ hA.1 hA.1).1.2
    have e2 : (fun z => sgStar g.abelian₂ (β * z) ^ 2) = fun z => sgStar g.abelian₂ (β * z) * sgStar g.abelian₂ (β * z) := by
      funext z; ring
    rw [e2, e, hA.2, hσ, subst_mul hs, subst_mul hs, subst_C, subst_X hs, sq]
    rfl
  have hτ2 : lamC g.lam (β ^ 2) = τ ^ 2 := by
    have e : β ^ 2 = D.host.φ₀ (((a : D.host.K) * (a : D.host.K) : D.host.K) : D.host.E) := by
      rw [IntermediateField.coe_mul, map_mul, sq]
    rw [e, sq]
    exact Formalism.MainNotions.Ext.CutA.tauK_mul D g.lam _ _
  have hG2 : AlgEnt (fun z => sgStar g.abelian₂ z ^ 2) ∧
      g.atU (fun z => sgStar g.abelian₂ z ^ 2) = g.atU (sgStar g.abelian₂) ^ 2 := by
    have e2 : (fun z => sgStar g.abelian₂ z ^ 2) = fun z => sgStar g.abelian₂ z * sgStar g.abelian₂ z := by funext z; ring
    rw [e2, sq]; exact (hmul _ _ halgσ halgσ).1
  have hP := atU_prod' g Finset.univ (fun i => (hsq i).1)
  have hGP := (hmul _ _ hG2.1 hP.1).1
  have hc := hconst (β ^ 2) (pow_mem hβQ 2)
  have hcGP := (hmul _ _ hc.1 hGP.1).1
  have rhs : g.atU (fun z => β ^ 2 * sgStar g.abelian₂ z ^ 2 * ∏ i, sqTh g.abelian₂ (Q i) z) =
      C (τ ^ 2) * ((C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * X * f) ^ 2 *
        ∏ i, (f ^ 2 * lineSer g.wq⁻¹ (xAt g (Q i)))) := by
    have e2 : (fun z => β ^ 2 * sgStar g.abelian₂ z ^ 2 * ∏ i, sqTh g.abelian₂ (Q i) z) =
        fun z => β ^ 2 * (sgStar g.abelian₂ z ^ 2 * ∏ i, sqTh g.abelian₂ (Q i) z) := by funext z; ring
    rw [e2, hcGP.2, hc.2, hGP.2, hG2.2, hP.2, hσ, hτ2, Finset.prod_congr rfl fun i _ => (hsq i).2]
  have E1 := congrArg g.atU (funext hfac : (fun z => sgStar g.abelian₂ (β * z) ^ 2) =
    fun z => β ^ 2 * sgStar g.abelian₂ z ^ 2 * ∏ i, sqTh g.abelian₂ (Q i) z)
  rw [lhs, rhs, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at E1
  have e : h ^ 2 * (subst h f : PowerSeries ℂ_[p]) ^ 2 =
      C (τ ^ 2) * X ^ 2 * (f ^ (k + 1)) ^ 2 * ∏ i, lineSer g.wq⁻¹ (xAt g (Q i)) := by
    have hε2 : (C ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) : PowerSeries ℂ_[p]) ^ 2 ≠ 0 :=
      pow_ne_zero _ fun h0 => hε0 (by simpa using congrArg constantCoeff h0)
    apply mul_left_cancel₀ hε2
    linear_combination E1
  have hF0 : constantCoeff (subst h f : PowerSeries ℂ_[p]) = 1 := by
    rw [GlobalTheory.SerTransport.const_subst hh0, hE]
  have hI2 := intSer_sq_of_eq h (subst h f) f _ τ (k + 1) hhI hh0 hh1 hτu hF0 hLI hL0 e
  have hH0 : constantCoeff ((subst h f : PowerSeries ℂ_[p])⁻¹ * f ^ (k + 1)) = 1 := by
    rw [map_mul, PowerSeries.constantCoeff_inv, hF0, map_pow, hE]; simp
  have hI := GlobalTheory.T.padicComplex_integral_of_sq_integral_odd p hp _ hH0 hI2
  obtain ⟨c0, ex⟩ := GlobalTheory.T.expMv_phiSeries_sub_nsmul_eq_div p g h (k + 1) hE hh0
  have hmb : (g.mulBy τ (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) = h := hh.symm
  rw [hmb, htn]
  refine ⟨c0, ?_⟩
  rw [ex]
  exact intSer_iff'.2 hI
end GlobalTheory.CMNormPhi
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaPointsIntegralNormConjugateLaws
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.CMEndo

section Series
open Formalism.MainNotions.GL3Theta

variable {p : ℕ} [Fact p.Prime] (g : G1 p) {σ : Type*}

theorem const_l : PowerSeries.constantCoeff g.l = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [GL3Theta.G1.l, flog]

theorem ex_l (h : g.Ok) : PowerSeries.subst g.l g.ex = PowerSeries.X := by
  obtain ⟨-, -, h0, h1⟩ := h
  have hl : ∀ _ : Unit, MvPowerSeries.constantCoeff (g.l : MvPowerSeries Unit ℂ_[p]) = 0 := fun _ => const_l g
  have he : ∀ _ : Unit, MvPowerSeries.constantCoeff (g.ex : MvPowerSeries Unit ℂ_[p]) = 0 := fun _ => h0
  have h2 : ∀ i : Unit, MvPowerSeries.subst (fun _ : Unit => (g.ex : MvPowerSeries Unit ℂ_[p]))
      (g.l : MvPowerSeries Unit ℂ_[p]) = MvPowerSeries.X i := fun _ => h1
  have h3 := GlobalTheory.FormalInv.eq_substInv_of_right hl he h2
  have h4 := GlobalTheory.FormalInv.subst_substInv_left hl
    (IsUnit.of_mul_eq_one _ (GlobalTheory.FormalInv.linearPart_mul_eq_one hl he h2)) ()
  rw [← h3] at h4
  exact h4

theorem pt_lg (h : g.Ok) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.pt (g.lg a) = a := by
  have ha' := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [GL3Theta.G1.pt, GL3Theta.G1.lg, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' (const_l g)) ha', ex_l g h, PowerSeries.subst_X ha']

theorem subst_zero {f : PowerSeries ℂ_[p]} (hf : PowerSeries.constantCoeff f = 0) :
    PowerSeries.subst (0 : MvPowerSeries σ ℂ_[p]) f = 0 := by
  obtain ⟨k, rfl⟩ := PowerSeries.X_dvd_iff.2 hf
  have h0 : PowerSeries.HasSubst (0 : MvPowerSeries σ ℂ_[p]) := PowerSeries.HasSubst.of_constantCoeff_zero (map_zero _)
  rw [PowerSeries.subst_mul h0, PowerSeries.subst_X h0, zero_mul]

theorem mulBy_one (h : g.Ok) (i : σ) : g.mulBy 1 (GL3Theta.Xv i) = GL3Theta.Xv i := by
  rw [GL3Theta.G1.mulBy, map_one, one_mul, pt_lg g h (MvPowerSeries.constantCoeff_X i)]

theorem mulBy_zero (h : g.Ok) (a : MvPowerSeries σ ℂ_[p]) : g.mulBy 0 a = 0 := by
  rw [GL3Theta.G1.mulBy, map_zero, zero_mul, GL3Theta.G1.pt, subst_zero h.2.2.1]

theorem constantCoeff_subst_zero {f : PowerSeries ℂ_[p]} (hf : PowerSeries.constantCoeff f = 0)
    {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (PowerSeries.subst a f) = 0 := by
  obtain ⟨k, rfl⟩ := PowerSeries.X_dvd_iff.2 hf
  have h0 : PowerSeries.HasSubst a := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [PowerSeries.subst_mul h0, PowerSeries.subst_X h0, map_mul, ha, zero_mul]

theorem constantCoeff_lg {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (g.lg a) = 0 :=
  constantCoeff_subst_zero (const_l g) ha

theorem constantCoeff_pt (h : g.Ok) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (g.pt a) = 0 :=
  constantCoeff_subst_zero h.2.2.1 ha

theorem lg_pt (h : g.Ok) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.lg (g.pt a) = a := by
  have ha' := PowerSeries.HasSubst.of_constantCoeff_zero ha
  rw [G1.lg, G1.pt, ← PowerSeries.subst_comp_subst_apply
    (PowerSeries.HasSubst.of_constantCoeff_zero' h.2.2.1) ha', h.2.2.2, PowerSeries.subst_X ha']

theorem lg_mulBy (h : g.Ok) (c : ℂ_[p]) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.lg (g.mulBy c a) = MvPowerSeries.C c * g.lg a := by
  rw [G1.mulBy, lg_pt g h]
  rw [map_mul, constantCoeff_lg g ha, mul_zero]

theorem mulBy_add (h : g.Ok) (c c' : ℂ_[p]) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.mulBy (c + c') a = g.add (g.mulBy c a) (g.mulBy c' a) := by
  rw [G1.add, lg_mulBy g h c ha, lg_mulBy g h c' ha, G1.mulBy, map_add (f := _), add_mul]

theorem add_eq_subst (h : g.Ok) (A B : MvPowerSeries σ ℂ_[p]) (hA : MvPowerSeries.constantCoeff A = 0)
    (hB : MvPowerSeries.constantCoeff B = 0) :
    g.add A B = MvPowerSeries.subst ![A, B] (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) := by
  have hab : MvPowerSeries.HasSubst ![A, B] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [hA, hB])
  have hs : MvPowerSeries.constantCoeff (g.lg (Xv 0) + g.lg (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [map_add (f := _), constantCoeff_lg g (MvPowerSeries.constantCoeff_X _),
      constantCoeff_lg g (MvPowerSeries.constantCoeff_X _), add_zero]
  have hsl : ∀ i : Fin 2, MvPowerSeries.subst ![A, B] (g.lg (Xv i) : MvPowerSeries (Fin 2) ℂ_[p]) =
      g.lg (![A, B] i) := by
    intro i
    have hX : PowerSeries.HasSubst (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X _)
    rw [G1.lg, G1.lg, PowerSeries.subst, PowerSeries.subst,
      MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => MvPowerSeries.constantCoeff_X i)) hab]
    congr 1
    funext _
    exact MvPowerSeries.subst_X hab i
  rw [G1.add, G1.add, G1.pt, G1.pt, PowerSeries.subst, PowerSeries.subst,
    MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => hs)) hab]
  congr 1
  funext _
  rw [MvPowerSeries.subst_add hab, hsl 0, hsl 1]
  rfl

theorem integralMv_zero : IntegralMv (0 : MvPowerSeries σ ℂ_[p]) := fun n => by
  simp [IsIntP]

theorem integralMv_X (i : σ) : IntegralMv (Xv i : MvPowerSeries σ ℂ_[p]) := fun n => by
  unfold IsIntP
  rw [MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem integral_mulBy_semiring : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), g.Ok →
    IntegralMv (g.add (GL3Theta.Xv 0) (GL3Theta.Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) →
    IntegralMv (g.mulBy 0 (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) ∧
    IntegralMv (g.mulBy 1 (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) ∧
    ∀ c c' : ℂ_[p], IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) →
      IntegralMv (g.mulBy c' (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) →
      IntegralMv (g.mulBy (c + c') (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
  intro p _ g h hadd
  have hX : MvPowerSeries.constantCoeff (Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := MvPowerSeries.constantCoeff_X _
  refine ⟨?_, ?_, ?_⟩
  · rw [mulBy_zero g h]; exact integralMv_zero
  · rw [mulBy_one g h]; exact integralMv_X ()
  · intro c c' hc hc'
    have h0 : ∀ d : ℂ_[p], MvPowerSeries.constantCoeff (g.mulBy d (Xv ()) : MvPowerSeries Unit ℂ_[p]) = 0 :=
      fun d => constantCoeff_pt g h (by rw [map_mul, constantCoeff_lg g hX, mul_zero])
    rw [mulBy_add g h c c' hX, add_eq_subst g h _ _ (h0 c) (h0 c')]
    exact ReciprocityTheory.ChartRestriction.L1.integralMv_subst2 (fun d => hadd d)
      (fun i => by fin_cases i <;> simp [h0]) (fun i => by
        fin_cases i
        · exact fun d => hc d
        · exact fun d => hc' d)

end Series

theorem endInt_all (D : D7) : GL3Theta.endInt D := by
  intro p _ cc δ g hA α hα
  have hok : g.Ok := hA.2.2.2.2
  have hadd := ((GlobalTheory.ThetaCube.cube_addInt_beBiadd D).2.1 p cc δ g hA).1
  obtain ⟨h0, h1, hplus⟩ := integral_mulBy_semiring p g hok hadd
  set S : Set ℂ_[p] := {c | IntegralMv (g.mulBy c (GL3Theta.Xv ()) : MvPowerSeries Unit ℂ_[p])} with hS
  have hcl : IsClosed S := GlobalTheory.mulBy_integral_isClosed p g
  have hnat : ∀ n : ℕ, (n : ℂ_[p]) ∈ S := by
    intro n
    induction n with
    | zero => rw [Nat.cast_zero]; exact h0
    | succ n ih =>
      rw [Nat.cast_succ]; exact hplus _ _ ih h1
  by_cases hp : p = 2
  · subst hp
    have h2 := GlobalTheory.TwoAdicFirst.fst_mem_closure_natCast D g.lam α hα
    have hsub : closure (Set.range (Nat.cast : ℕ → ℂ_[2])) ⊆ S :=
      closure_minimal (by rintro _ ⟨n, rfl⟩; exact hnat n) hcl
    exact hsub h2
  · obtain ⟨β, hβ, γ, hγ, hb1, hb2, hc1, hc2, rfl⟩ := Formalism.MainNotions.Ext.CutA.okpTwoUnits2_holds D p g.lam hp α hα
    have hunit : ∀ β ∈ GL3Theta.OKp D g.lam, ‖β.1‖ = 1 → ‖β.2‖ = 1 → β.1 ∈ S := by
      intro β hβ h1 h2
      have hc := Formalism.MainNotions.Ext.CutA.okpUnitsDense_holds D p g.lam hp β hβ h1 h2
      have hm := map_mem_closure continuous_fst hc (t := S) (by
        rintro _ ⟨a, ha, rfl⟩
        exact GlobalTheory.CMUnit.unit_endo D p cc δ g hA hp a ha)
      rwa [hcl.closure_eq] at hm
    exact hplus _ _ (hunit β hβ hb1 hb2) (hunit γ hγ hc1 hc2)

theorem endo_all : ∀ D : D7, GL3Theta.endInt D ∧ GL3Theta.phNorm D ∧ GL3Theta.beConj D := by
  intro D
  have he := endInt_all D
  have ha := (GlobalTheory.ThetaCube.cube_addInt_beBiadd D).2.1
  have hB := (GlobalTheory.ThetaCube.cube_addInt_beBiadd D).2.2
  have hok : Formalism.MainNotions.Ext.CutA.PhNormOK D := GlobalTheory.CMNormPhi.phAt_mulBy_norm D he ha
  have hn := Formalism.MainNotions.Ext.CutA.phNorm_of' Formalism.MainNotions.Ext.CutA.phNormOfUnits_holds Formalism.MainNotions.Ext.CutA.phNormClosed_holds D hok he ha hB
  exact ⟨he, hn, Formalism.MainNotions.Ext.CutA.beConj_of' Formalism.MainNotions.Ext.CutA.beConjOfNorm_holds D he ha hn hB⟩

end GlobalTheory.CMEndo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaPointsIntegralNormConjugateLawsStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmThetaPoints_integral_norm_conjugate_laws : ∀ D : D7, GL3Theta.endInt D ∧ GL3Theta.phNorm D ∧ GL3Theta.beConj D := by
  first | exact @GlobalTheory.CMEndo.endo_all | exact GlobalTheory.CMEndo.endo_all | (intros; apply GlobalTheory.CMEndo.endo_all <;> assumption)
end
