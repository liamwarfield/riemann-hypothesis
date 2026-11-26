module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCentralFlipTranslateHalfPlacesThetaPair
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraicFormsLevelGroupEqTwistLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HalfTranslatesLeLevelHalfTranslatesOfDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HalfTranslatesLeLevelHalfTranslatesOfDvd
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

theorem trSp_le_of_subhalf : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (l₂ : Geo.Tor.Level H) (e₂ e' : AE D) (P' : Finset (Formalism.L2.DIV.Pl D.host.E)), IsHalfIdem l₂ e₂ → IsIdemSum e' P' → (∀ PP ∈ P', l₂.Mb ≤ PP.asIdeal) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (f₀ : WO V W → ℂ) (M : ℕ) (O : Subring ℂ), trSp ψ V W ΛV ΛW f₀ e' M O ≤ trSp ψ V W ΛV ΛW f₀ e₂ M O := by
  intro D H l₂ e₂ e' P' h₂ h' hP ψ V W ΛV ΛW f₀ M O
  obtain ⟨P₂, ⟨⟨es₂, hes₂, rfl⟩, -⟩, hP₂⟩ := h₂
  obtain ⟨⟨es', hes', rfl⟩, -⟩ := h'
  have hsub : P' ⊆ P₂ := fun PP h => (hP₂ PP).2 (hP PP h)
  have key := GlobalTheory.PartialIdemSum.sum_mul_sum_of_subset P' P₂ es' es₂ hes' hes₂ hsub
  unfold trSp
  refine Submodule.span_mono ?_
  rintro f ⟨y, hy, hM, rfl⟩
  refine ⟨y, fun i j => ?_, hM, rfl⟩
  rw [← hy i j, ← mul_assoc, mul_comm (∑ P ∈ P₂, es₂ P), key]

end GlobalTheory.LevelSeries

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HalfTranslatesLeLevelHalfTranslatesOfDvdStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfTranslates_le_levelHalfTranslates_of_dvd : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (l₂ : Geo.Tor.Level H) (e₂ e' : AE D) (P' : Finset (Formalism.L2.DIV.Pl D.host.E)), IsHalfIdem l₂ e₂ → IsIdemSum e' P' → (∀ PP ∈ P', l₂.Mb ≤ PP.asIdeal) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (f₀ : WO V W → ℂ) (M : ℕ) (O : Subring ℂ), trSp ψ V W ΛV ΛW f₀ e' M O ≤ trSp ψ V W ΛV ΛW f₀ e₂ M O := by
  first | exact @GlobalTheory.LevelSeries.trSp_le_of_subhalf | exact GlobalTheory.LevelSeries.trSp_le_of_subhalf | (intros; apply GlobalTheory.LevelSeries.trSp_le_of_subhalf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipScalarPrimePowIntegralAtLevelPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipScalarMemCoefficientField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipScalarMemCoefficientField
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.FlipScalField

open _root_.Formalism.L2.Host

def sqN {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) : ℝ :=
  Real.sqrt ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)

theorem absNorm_pos {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  have : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero this

theorem sqN_pos {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) : 0 < sqN v :=
  Real.sqrt_pos.2 (absNorm_pos v)

theorem sqN_sq {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) :
    sqN v ^ 2 = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) :=
  Real.sq_sqrt (absNorm_pos v).le

theorem cpow_neg_half (n : ℕ) :
    ((n : ℕ) : ℂ) ^ (-(((-1 / 2 : ℝ)) : ℂ)) = ((Real.sqrt n : ℝ) : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _)]
  push_cast
  congr 1
  ring

theorem ordF_natCast {E : Type} [Field E] [NumberField E] (v : HeightOneSpectrum (𝓞 E)) (u : Eˣ) (M₀ : ℕ)
    (hu : (u : E) = ((M₀ : ℕ) : E)) :
    ordF v u = ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {((M₀ : ℕ) : 𝓞 E)})).factors : ℤ) := by
  have h0 : ((M₀ : ℕ) : 𝓞 E) ≠ 0 := by
    intro h
    have : ((M₀ : ℕ) : E) = 0 := by
      have := congrArg (algebraMap (𝓞 E) E) h
      simpa using this
    exact u.ne_zero (hu.trans this)
  have e : (u : E) = algebraMap (𝓞 E) E ((M₀ : ℕ) : 𝓞 E) := by rw [hu, map_natCast]
  rw [ordF, e, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg v h0,
    WithZero.log_exp, neg_neg]

end GlobalTheory.FlipScalField

namespace GlobalTheory.FlipScalField
open _root_.Formalism.L2.Host


set_option maxHeartbeats 800000 in
theorem mem_fieldRange : ∀ (E : Type) [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (M₀ r w : ℕ) (u a : Eˣ) (T : Finset (HeightOneSpectrum (𝓞 E))) (k : Type) [Field k] (σ : k →+* ℂ), Odd w → (u : E) = ((M₀ : ℕ) : E) → IsIntegral ℤ (a : E) → (∀ v ∈ T, ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal) → (∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∉ v.asIdeal → χ.UnrAt v) → χ.ValuesIn (-1 / 2) σ → (∃ y : k, ((χ.inf a : ℂˣ) : ℂ) = σ y * ((|((Algebra.norm ℚ (a : E) : ℚ) : ℝ)| ^ (-(w : ℝ) / 2) : ℝ) : ℂ)) → (∀ v ∈ T, χ.locK v a = χ.locK v u ∧ v.valuation E (a : E) = v.valuation E ((M₀ : ℕ) : E)) → (∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T → χ.locK v a = 1 ∧ v.valuation E (a : E) = 1) → (∏ PP ∈ T, ((χ.locK PP u : ℂˣ) : ℂ) ^ r) * ((Real.sqrt ((∏ PP ∈ T, Ideal.absNorm (PP.maxPowDividing (Ideal.span {((M₀ : ℕ) : 𝓞 E)})) ^ (r * w) : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ ∈ σ.fieldRange := by
  intro E _ _ χ M₀ r w u a T k _ σ hw hu ha hT hunr hval hinf hTa hST
  classical
  have hM0 : ((M₀ : ℕ) : 𝓞 E) ≠ 0 := by
    intro h
    have : ((M₀ : ℕ) : E) = 0 := by
      have := congrArg (algebraMap (𝓞 E) E) h
      simpa using this
    exact u.ne_zero (hu.trans this)
  have hSfin : {v : HeightOneSpectrum (𝓞 E) | ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {((M₀ : ℕ) : 𝓞 E)}) ?_).subset fun v hv => ?_
    · rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    · exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hv)
  set S := hSfin.toFinset with hSdef
  have hmemS : ∀ v, v ∈ S ↔ ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal := fun v => Set.Finite.mem_toFinset _
  set R := (GlobalTheory.HeckeProduct.finite_ordF a).toFinset with hRdef
  have hR : ∀ v, v ∉ R → ordF v a = 0 := fun v hv => by
    by_contra h; exact hv ((Set.Finite.mem_toFinset _).2 h)
  have hTS : T ⊆ S := fun v hv => (hmemS v).2 (hT v hv)
  have hoST : ∀ v ∈ S, v ∉ T → ordF v a = 0 := fun v hv hvT => by
    rw [ordF, (hST v ((hmemS v).1 hv) hvT).2, WithZero.log_one, neg_zero]
  have hoT : ∀ v ∈ T, ordF v a = ordF v u := fun v hv => by
    rw [ordF, ordF, (hTa v hv).2, hu]
  have hPR := Formalism.L2.Host.HChar.productRule χ S (fun v hv => hunr v (fun h => hv ((hmemS v).2 h))) a
  have hloc : ∏ v ∈ S, χ.locK v a = ∏ v ∈ T, χ.locK v u := by
    rw [← Finset.prod_subset hTS (fun v hv hvT => (hST v ((hmemS v).1 hv) hvT).1)]
    exact Finset.prod_congr rfl fun v hv => (hTa v hv).1
  have hfin : (∏ᶠ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ S), χ.val v ^ ordF v a) =
      ∏ v ∈ R \ S, χ.val v ^ ordF v a := by
    apply finprod_mem_eq_prod_of_subset (s := {v | v ∉ S})
    · rintro v ⟨hv1, hv2⟩
      simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe]
      refine ⟨?_, hv1⟩
      by_contra h
      exact hv2 (by simp [hR v h])
    · intro v hv
      simp only [Finset.coe_sdiff, Set.mem_diff, Finset.mem_coe] at hv
      exact hv.2
  rw [hloc, hfin] at hPR
  choose! y hy using hval
  have hvalv : ∀ v, v ∉ S → ((χ.val v : ℂˣ) : ℂ) = σ (y v) / ((sqN v : ℝ) : ℂ) := fun v hv => by
    have h1 := hy v (hunr v fun h => hv ((hmemS v).2 h))
    have h2 : ((sqN v : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sqN_pos v).ne'
    rw [h1, HChar.valTw, cpow_neg_half, ← sqN, mul_div_assoc, div_self h2, mul_one]
  obtain ⟨y0, hy0⟩ := hinf
  set Q : ℝ := ∏ v ∈ R, sqN v ^ ordF v a with hQ
  have hQpos : 0 < Q := Finset.prod_pos fun v _ => zpow_pos (sqN_pos v) _
  have hNa : |((Algebra.norm ℚ (a : E) : ℚ) : ℝ)| = Q ^ 2 := by
    rw [← PI.AlgValsFin.W.prod_norm_emb, PI.AlgValsFin.W.prodNorm a R hR, hQ, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [← sqN_sq v, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
  have hinfv : ((χ.inf a : ℂˣ) : ℂ) = σ y0 * (((Q ^ w)⁻¹ : ℝ) : ℂ) := by
    rw [hy0, hNa]
    congr 2
    rw [← Real.rpow_natCast Q 2, ← Real.rpow_mul hQpos.le, ← Real.rpow_natCast, ← Real.rpow_neg hQpos.le]
    congr 1
    push_cast
    ring
  set A : ℝ := ∏ v ∈ T, sqN v ^ ordF v a with hA
  set B : ℝ := ∏ v ∈ R \ S, sqN v ^ ordF v a with hB
  have hApos : 0 < A := Finset.prod_pos fun v _ => zpow_pos (sqN_pos v) _
  have hBpos : 0 < B := Finset.prod_pos fun v _ => zpow_pos (sqN_pos v) _
  have hQAB : Q = A * B := by
    rw [hQ, ← Finset.prod_inter_mul_prod_diff R S]
    congr 1
    have e1 : ∏ v ∈ R ∩ S, sqN v ^ ordF v a = ∏ v ∈ S, sqN v ^ ordF v a :=
      Finset.prod_subset Finset.inter_subset_right fun v hv hv' => by
        rw [hR v (fun h => hv' (Finset.mem_inter.2 ⟨h, hv⟩)), zpow_zero]
    have e2 : ∏ v ∈ T, sqN v ^ ordF v a = ∏ v ∈ S, sqN v ^ ordF v a :=
      Finset.prod_subset hTS fun v hv hvT => by rw [hoST v hv hvT, zpow_zero]
    rw [e1, ← e2]
  have hprodval : ∏ v ∈ R \ S, ((χ.val v : ℂˣ) : ℂ) ^ ordF v a =
      σ (∏ v ∈ R \ S, y v ^ ordF v a) / ((B : ℝ) : ℂ) := by
    rw [map_prod, hB, Complex.ofReal_prod, ← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [hvalv v (Finset.mem_sdiff.1 hv).2, map_zpow₀, Complex.ofReal_zpow, div_zpow]
  have key := congrArg (fun z : ℂˣ => (z : ℂ)) hPR
  simp only [Units.val_mul, Units.val_one, Units.coe_prod, Units.val_zpow_eq_zpow_val] at key
  rw [hinfv, hprodval, hQAB] at key
  set P : ℂ := ∏ v ∈ T, ((χ.locK v u : ℂˣ) : ℂ) with hPdef
  set Y : k := ∏ v ∈ R \ S, y v ^ ordF v a with hY
  have h1 : σ y0 ≠ 0 := fun h => by rw [h] at key; simp at key
  have h2 : σ Y ≠ 0 := fun h => by rw [h] at key; simp at key
  have hA0 : ((A : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hApos.ne'
  have hB0 : ((B : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hBpos.ne'
  have hP : P = ((A : ℝ) : ℂ) ^ w * ((B : ℝ) : ℂ) ^ (w + 1) / (σ y0 * σ Y) := by
    rw [eq_div_iff (mul_ne_zero h1 h2)]
    push_cast at key
    field_simp at key
    linear_combination key

  have hsqrt : Real.sqrt ((∏ PP ∈ T, Ideal.absNorm (PP.maxPowDividing (Ideal.span {((M₀ : ℕ) : 𝓞 E)})) ^ (r * w) : ℕ) : ℝ) =
      A ^ (r * w) := by
    rw [← Real.sqrt_sq (pow_nonneg hApos.le _)]
    congr 1
    push_cast
    rw [hA, ← Finset.prod_pow, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [hoT v hv, ordF_natCast v u M₀ hu, HeightOneSpectrum.maxPowDividing, map_pow, zpow_natCast]
    push_cast
    rw [← sqN_sq v]
    ring
  set q : ℚ := ∏ v ∈ R \ S, ((Ideal.absNorm v.asIdeal : ℕ) : ℚ) ^ ordF v a with hq
  have hqB : ((q : ℚ) : ℂ) = ((B : ℝ) : ℂ) ^ 2 := by
    have : ((q : ℚ) : ℝ) = B ^ 2 := by
      rw [hq, hB, ← Finset.prod_pow]
      push_cast
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [← sqN_sq v, ← zpow_natCast, ← zpow_natCast, ← _root_.zpow_mul, ← _root_.zpow_mul, mul_comm]
    rw [← Complex.ofReal_ratCast, this, Complex.ofReal_pow]
  obtain ⟨m, rfl⟩ := hw
  have heq : (∏ PP ∈ T, ((χ.locK PP u : ℂˣ) : ℂ) ^ r) *
      ((Real.sqrt ((∏ PP ∈ T, Ideal.absNorm (PP.maxPowDividing (Ideal.span {((M₀ : ℕ) : 𝓞 E)})) ^ (r * (2 * m + 1)) : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ =
      (((q : ℚ) : ℂ) ^ (m + 1)) ^ r * ((σ y0 * σ Y)⁻¹) ^ r := by
    rw [hsqrt, Finset.prod_pow, ← hPdef, hP, hqB]
    push_cast
    field_simp
    ring
  rw [heq]
  refine mul_mem (pow_mem (pow_mem (SubfieldClass.ratCast_mem _ q) _) _) (pow_mem (inv_mem (mul_mem ?_ ?_)) _)
  · exact ⟨y0, rfl⟩
  · exact ⟨Y, rfl⟩

end GlobalTheory.FlipScalField
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipScalarMemCoefficientFieldStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralFlipScalar_mem_coefficientField : ∀ (E : Type) [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (M₀ r w : ℕ) (u a : Eˣ) (T : Finset (HeightOneSpectrum (𝓞 E))) (k : Type) [Field k] (σ : k →+* ℂ), Odd w → (u : E) = ((M₀ : ℕ) : E) → IsIntegral ℤ (a : E) → (∀ v ∈ T, ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal) → (∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∉ v.asIdeal → χ.UnrAt v) → χ.ValuesIn (-1 / 2) σ → (∃ y : k, ((χ.inf a : ℂˣ) : ℂ) = σ y * ((|((Algebra.norm ℚ (a : E) : ℚ) : ℝ)| ^ (-(w : ℝ) / 2) : ℝ) : ℂ)) → (∀ v ∈ T, χ.locK v a = χ.locK v u ∧ v.valuation E (a : E) = v.valuation E ((M₀ : ℕ) : E)) → (∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T → χ.locK v a = 1 ∧ v.valuation E (a : E) = 1) → (∏ PP ∈ T, ((χ.locK PP u : ℂˣ) : ℂ) ^ r) * ((Real.sqrt ((∏ PP ∈ T, Ideal.absNorm (PP.maxPowDividing (Ideal.span {((M₀ : ℕ) : 𝓞 E)})) ^ (r * w) : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ ∈ σ.fieldRange := by
  first | exact @GlobalTheory.FlipScalField.mem_fieldRange | exact GlobalTheory.FlipScalField.mem_fieldRange | (intros; apply GlobalTheory.FlipScalField.mem_fieldRange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldElementLocalComponentsLevelNumber
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldElementLocalComponentsLevelNumber
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelFieldApprox

open _root_.Formalism.L2.Host

theorem val_eq_one_of_close {E : Type} [Field E] [NumberField E] {v : HeightOneSpectrum (𝓞 E)} {y : E}
    (h : v.valuation E (y - 1) < 1) : v.valuation E y = 1 := by
  have e : y = (y - 1) + 1 := by ring
  rw [e, Valuation.map_add_eq_of_lt_right _ (by rwa [map_one])]
  exact map_one _

theorem locK_eq_one {E : Type} [Field E] [NumberField E] (χ : HChar E) (v : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (hn : χ.LevelLe v n) (y : Eˣ) (h : v.valuation E ((y : E) - 1) ≤ WithZero.exp (-((n : ℤ) + 1))) :
    χ.locK v y = 1 ∧ v.valuation E (y : E) = 1 := by
  have hlt : v.valuation E ((y : E) - 1) < 1 :=
    lt_of_le_of_lt h (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
  have hv := val_eq_one_of_close hlt
  have e1 : ((atFin v y : (v.adicCompletion E)ˣ) : v.adicCompletion E) = algebraMap E (v.adicCompletion E) (y : E) := rfl
  have hval : ∀ x : E, Valued.v (algebraMap E (v.adicCompletion E) x) = v.valuation E x :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  refine ⟨?_, hv⟩
  show χ.loc v (atFin v y) = 1
  refine hn _ ?_ ?_
  · show Valued.v ((atFin v y : (v.adicCompletion E)ˣ) : v.adicCompletion E) = 1
    rw [e1, hval, hv]
  · rw [e1, ← map_one (algebraMap E (v.adicCompletion E)), ← map_sub, hval]
    exact h.trans (WithZero.exp_le_exp.mpr (by omega))

theorem exists_approx : ∀ (E : Type) [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (M₀ : ℕ) (u : Eˣ), (u : E) = ((M₀ : ℕ) : E) → ∀ (T : Finset (HeightOneSpectrum (𝓞 E))), ∃ a : Eˣ, IsIntegral ℤ (a : E) ∧ (∀ v ∈ T, χ.locK v a = χ.locK v u ∧ v.valuation E (a : E) = v.valuation E ((M₀ : ℕ) : E)) ∧ ∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T → χ.locK v a = 1 ∧ v.valuation E (a : E) = 1 := by
  intro E _ _ χ M₀ u hu T
  classical
  have hM0 : M₀ ≠ 0 := by
    rintro rfl
    exact u.ne_zero (by rw [hu]; simp)
  have hM : ((M₀ : ℕ) : 𝓞 E) ≠ 0 := by exact_mod_cast hM0
  have hMe : ((M₀ : ℕ) : E) ≠ 0 := by exact_mod_cast hM0
  have hfin : {v : HeightOneSpectrum (𝓞 E) | ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {((M₀ : ℕ) : 𝓞 E)}) ?_).subset fun v hv => ?_
    · rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    · exact Ideal.dvd_span_singleton.2 hv
  set S : Finset (HeightOneSpectrum (𝓞 E)) := T ∪ hfin.toFinset with hS
  choose n hn using GlobalTheory.Mem.UnrAe.exists_levelLe χ
  have hm : ∀ v : HeightOneSpectrum (𝓞 E), ∃ m : ℕ, v.intValuation ((M₀ : ℕ) : 𝓞 E) = WithZero.exp (-(m : ℤ)) :=
    fun v => ⟨_, v.intValuation_if_neg hM⟩
  choose m hm using hm
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal)
    (fun v => if v ∈ T then m v + n v + 1 else n v + 1)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h'))
    (fun v => if (v : HeightOneSpectrum (𝓞 E)) ∈ T then ((M₀ : ℕ) : 𝓞 E) else 1)
  have hvz : ∀ v : HeightOneSpectrum (𝓞 E), ∀ z : 𝓞 E, v.valuation E (z : E) = v.intValuation z :=
    fun v z => HeightOneSpectrum.valuation_of_algebraMap (K := E) v z
  have hT : ∀ v ∈ T, v.valuation E ((y : E) - ((M₀ : ℕ) : E)) ≤ WithZero.exp (-((m v : ℤ) + n v + 1)) := by
    intro v hv
    have h1 := (v.intValuation_le_pow_iff_mem _ _).2 (hy v (Finset.mem_union_left _ hv))
    simp only [hv, if_true] at h1
    have e : (y : E) - ((M₀ : ℕ) : E) = ((y - ((M₀ : ℕ) : 𝓞 E) : 𝓞 E) : E) := by push_cast; rfl
    rw [e, hvz]
    convert h1 using 2
    push_cast; ring
  have hO : ∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T →
      v.valuation E ((y : E) - 1) ≤ WithZero.exp (-((n v : ℤ) + 1)) := by
    intro v hv hvT
    have h1 := (v.intValuation_le_pow_iff_mem _ _).2
      (hy v (Finset.mem_union_right _ (hfin.mem_toFinset.2 hv)))
    simp only [hvT, if_false] at h1
    have e : (y : E) - 1 = ((y - 1 : 𝓞 E) : E) := by push_cast; rfl
    rw [e, hvz]
    convert h1 using 2
    push_cast; ring
  have hMv : ∀ v, v.valuation E ((M₀ : ℕ) : E) = WithZero.exp (-(m v : ℤ)) := by
    intro v
    rw [← hm v, ← hvz]; simp
  have hTv : ∀ v ∈ T, v.valuation E (y : E) = v.valuation E ((M₀ : ℕ) : E) := by
    intro v hv
    have e : (y : E) = ((y : E) - ((M₀ : ℕ) : E)) + ((M₀ : ℕ) : E) := by ring
    rw [e, Valuation.map_add_eq_of_lt_right]
    rw [hMv]
    exact lt_of_le_of_lt (hT v hv) (WithZero.exp_lt_exp.mpr (by omega))
  have hOv : ∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T → v.valuation E (y : E) = 1 :=
    fun v hv hvT => val_eq_one_of_close (lt_of_le_of_lt (hO v hv hvT)
      (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega))
  by_cases hy0 : (y : E) = 0
  · refine ⟨1, by simpa using isIntegral_one, fun v hv => ?_, fun v hv hvT => ?_⟩
    · exact absurd (hTv v hv) (by rw [hy0, map_zero, hMv]; exact (WithZero.exp_ne_zero).symm)
    · exact absurd (hOv v hv hvT) (by rw [hy0, map_zero]; exact zero_ne_one)
  set a : Eˣ := Units.mk0 (y : E) hy0 with ha
  refine ⟨a, y.isIntegral_coe, fun v hv => ?_, fun v hv hvT => ?_⟩
  · have hw := (locK_eq_one χ v (hn v) (a * u⁻¹) ?_).1
    · refine ⟨?_, hTv v hv⟩
      have : a = (a * u⁻¹) * u := by group
      rw [this, map_mul, hw, one_mul]
    · rw [Units.val_mul, Units.val_inv_eq_inv_val, hu, ha, Units.val_mk0]
      have e : (y : E) * ((M₀ : ℕ) : E)⁻¹ - 1 = ((y : E) - ((M₀ : ℕ) : E)) / ((M₀ : ℕ) : E) := by
        field_simp
      rw [e, map_div₀, hMv]
      calc _ ≤ WithZero.exp (-((m v : ℤ) + n v + 1)) / WithZero.exp (-(m v : ℤ)) :=
            div_le_div_of_nonneg_right (hT v hv) zero_le'
        _ = _ := by rw [div_eq_mul_inv, ← WithZero.exp_neg, ← WithZero.exp_add]; congr 1; ring
  · exact locK_eq_one χ v (hn v) a (by rw [ha, Units.val_mk0]; exact hO v hv hvT)

end GlobalTheory.LevelFieldApprox
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFieldElementLocalComponentsLevelNumberStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_field_element_local_components_level_number : ∀ (E : Type) [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (M₀ : ℕ) (u : Eˣ), (u : E) = ((M₀ : ℕ) : E) → ∀ (T : Finset (HeightOneSpectrum (𝓞 E))), ∃ a : Eˣ, IsIntegral ℤ (a : E) ∧ (∀ v ∈ T, χ.locK v a = χ.locK v u ∧ v.valuation E (a : E) = v.valuation E ((M₀ : ℕ) : E)) ∧ ∀ v : HeightOneSpectrum (𝓞 E), ((M₀ : ℕ) : 𝓞 E) ∈ v.asIdeal → v ∉ T → χ.locK v a = 1 ∧ v.valuation E (a : E) = 1 := by
  first | exact @GlobalTheory.LevelFieldApprox.exists_approx | exact GlobalTheory.LevelFieldApprox.exists_approx | (intros; apply GlobalTheory.LevelFieldApprox.exists_approx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipScalarPrimePowIntegralAtLevelPlaces
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

theorem exists_pow_mul_mem_of_mem_fieldRange (z : ℂ) (l : ℕ) (hl : l.Prime) : ∃ c : ℕ, ∀ (k : Type) [Field k] [NumberField k]
    (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O →
    z ∈ σ.fieldRange → (l : ℂ) ^ c * z ∈ O := by
  classical
  by_cases h : ∃ m : ℕ, m ≠ 0 ∧ IsIntegral ℤ ((m : ℂ) * z)
  · obtain ⟨m, hm0, hint⟩ := h
    obtain ⟨c, m', hm', hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 l hl.ne_one
    refine ⟨c, fun k _ _ σ la O hla hO hz => ?_⟩
    obtain ⟨y, rfl⟩ := hz
    have hti : IsIntegral ℤ ((m : k) * y) := by
      rw [← isIntegral_algHom_iff σ.toIntAlgHom σ.injective]
      simpa using hint
    have hm'0 : (m' : k) ≠ 0 := by
      rintro h0
      rw [Nat.cast_eq_zero] at h0
      subst h0
      simp at hmeq
      exact hm0 hmeq
    have hcop : IsCoprime (m' : ℤ) (l : ℤ) :=
      Nat.isCoprime_iff_coprime.2 (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hl).2 hm'))
    have hnot : ((m' : ℕ) : 𝓞 k) ∉ la.asIdeal := by
      intro hmem
      obtain ⟨s, t, hst⟩ := hcop
      apply la.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have : ((s : 𝓞 k) * ((m' : ℕ) : 𝓞 k) + (t : 𝓞 k) * ((l : ℕ) : 𝓞 k)) = 1 := by
        have := congrArg (Int.cast : ℤ → 𝓞 k) hst
        push_cast at this
        exact this
      rw [← this]
      exact la.asIdeal.add_mem (la.asIdeal.mul_mem_left _ hmem) (la.asIdeal.mul_mem_left _ hla)
    have hv1 : la.valuation k (m' : k) = 1 := by
      have e : ((m' : ℕ) : k) = algebraMap (𝓞 k) k ((m' : ℕ) : 𝓞 k) := (map_natCast _ _).symm
      rw [e, HeightOneSpectrum.valuation_of_algebraMap]
      exact HeightOneSpectrum.intValuation_eq_one_iff.2 hnot
    have hvt : la.valuation k ((m : k) * y) ≤ 1 := by
      have := HeightOneSpectrum.valuation_le_one (K := k) la (⟨(m : k) * y, hti⟩ : 𝓞 k)
      exact this
    have heq : ((l : k) ^ c * y) = ((m : k) * y) / (m' : k) := by
      rw [hmeq]; push_cast; field_simp
    have hmem := hO ((l : k) ^ c * y) (by rw [heq, map_div₀, hv1, div_one]; exact hvt)
    simpa using hmem
  · refine ⟨0, fun k _ _ σ la O hla hO hz => ?_⟩
    exfalso
    obtain ⟨y, rfl⟩ := hz
    have hy : IsAlgebraic ℤ y := (IsFractionRing.isAlgebraic_iff ℤ ℚ k).2 (Algebra.IsAlgebraic.isAlgebraic y)
    obtain ⟨m, hm0, hmi⟩ := hy.exists_integral_multiple
    apply h
    refine ⟨m.natAbs, by simpa using hm0, ?_⟩
    have h2 : IsIntegral ℤ (σ (m • y)) := hmi.map σ.toIntAlgHom
    rcases Int.natAbs_eq m with hm | hm
    · rw [hm] at h2; simpa [zsmul_eq_mul] using h2
    · rw [hm] at h2
      have h3 := h2.neg
      simpa [zsmul_eq_mul, neg_mul] using h3

theorem flipScal_pow_mem : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (M₀ l : ℕ), ChiData χW χ M₀ → l.Prime → M₀ ≠ 0 → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)), ∃ c : ℕ, ∀ (eT : AE D) (x : (AE D)ˣ), IsIdemSum eT T → (∀ PP ∈ T, ((M₀ : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsFlipDet V eT M₀ x → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → ConjIn D σ → χ.ValuesIn (-1 / 2) σ → Odd M₀ → Nat.Coprime M₀ (GlobalTheory.Tow.badN D) → (l : ℂ) ^ c * flipScal χW V W T M₀ x ∈ O := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hVP hW χ M₀ l hχ hl hM T
  have hM' : ((M₀ : ℕ) : D.host.E) ≠ 0 := by exact_mod_cast hM
  set u : D.host.Eˣ := Units.mk0 _ hM' with hu
  set z : ℂ := (∏ PP ∈ T, ((χ.locK PP u : ℂˣ) : ℂ) ^ V.rank) *
    ((Real.sqrt (flipIdx V W T M₀ : ℝ) : ℝ) : ℂ)⁻¹ with hz
  obtain ⟨c, hc⟩ := exists_pow_mul_mem_of_mem_fieldRange z l hl
  refine ⟨c, fun eT x hT hTM hx k _ _ σ la O hla hO hconj hval _ _ => ?_⟩
  have hfl : flipScal χW V W T M₀ x = z := by
    unfold flipScal
    rw [GlobalTheory.T.char_inv_centralFlipIdele_eq_prod_local_components D V χW χ M₀ u T eT x hχ.1 rfl hT hx]
  rw [hfl]
  refine hc k σ la O hla hO ?_
  obtain ⟨a, hai, hA1, hA2⟩ := GlobalTheory.T.exists_field_element_local_components_level_number D.host.E χ M₀ u rfl T
  have hinf := GlobalTheory.T.heckeChar_infinity_eq_coeff_mul_halfNorm_pow D ψ θ V W χV χW om ΛV ΛW sW f₀ hVP χ hχ.1 k σ hconj a
  have := GlobalTheory.T.centralFlipScalar_mem_coefficientField D.host.E χ M₀ V.rank W.rank u a T k σ hW rfl hai hTM (fun v hv => hχ.2.1 v hv) hval hinf hA1 hA2
  simpa [hz, flipIdx] using this

end GlobalTheory.LevelSeries

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FlipScalarPrimePowIntegralAtLevelPlacesStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flipScalar_primePow_integral_at_levelPlaces : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (M₀ l : ℕ), ChiData χW χ M₀ → l.Prime → M₀ ≠ 0 → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)), ∃ c : ℕ, ∀ (eT : AE D) (x : (AE D)ˣ), IsIdemSum eT T → (∀ PP ∈ T, ((M₀ : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsFlipDet V eT M₀ x → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → ConjIn D σ → χ.ValuesIn (-1 / 2) σ → Odd M₀ → Nat.Coprime M₀ (GlobalTheory.Tow.badN D) → (l : ℂ) ^ c * flipScal χW V W T M₀ x ∈ O := by
  first | exact @GlobalTheory.LevelSeries.flipScal_pow_mem | exact GlobalTheory.LevelSeries.flipScal_pow_mem | (intros; apply GlobalTheory.LevelSeries.flipScal_pow_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaKernelFockVectorEqOfFinitePointMove
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaKernelFockVectorEqOfFinitePointMove
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

theorem thetaKO_flip : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (z : GA D V), z ∈ GfC V → ∀ (e e₂ : AE D) (M : ℕ) (O : Subring ℂ) (f f' : WO V W → ℂ) (a : ℂ), f ∈ trSp ψ V W ΛV ΛW f₀ e M O → f' ∈ trSp ψ V W ΛV ΛW f₀ e₂ M O → om (z, 1) f' = a • f → ∀ (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (Q : MvPolynomial (FVar D W.rank V.rank) ℂ) (s : GA D V) (g : GA D W), a * thetaKO om s g (stdF ψ θ V W sW BW f Q) = thetaKO om (s * z) g (stdF ψ θ V W sW BW f' Q) := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP z hz e e₂ M O f f' a _ hf' hom BW Q s g
  have hw := hP.1.weil
  have hf₀ : IsThetaFunO ψ V W f₀ := hP.2.2.2.2.2.2.2.2.2.theta
  have hth : IsThetaFunO ψ V W f' := by
    clear hom
    induction hf' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, -, -, rfl⟩ := hx
      exact GlobalTheory.TwistFactorCompare.isTheta_heisO hw.std hf₀ y
    | zero => simpa using GlobalTheory.OrientedHeis.theta_smul (0 : ℂ) hf₀
    | add x y _ _ hx hy => exact GlobalTheory.OrientedHeis.theta_add hx hy
    | smul c x _ hx => exact GlobalTheory.OrientedHeis.theta_smul (c : ℂ) hx
  have h1 := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ V W χV χW om hw hP.1.inf (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) sW sW BW BW z 1
    (fun τ => by simp only [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hz, Matrix.mul_one, Matrix.one_mul])
    (fun τ => by simp only [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.mul_one, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ hz, Matrix.one_mul])
    (fun τ => by rw [GlobalTheory.FiniteFock.compAt_mt_of_finite θ τ (one_mem _), Matrix.one_mul]) f' hth Q).2
  have hp : ((s * z, g) : GA D V × GA D W) = (s, g) * (z, 1) := by simp
  unfold thetaKO stdF
  rw [hp, map_mul, Module.End.mul_apply, h1, hom, GlobalTheory.FiniteFock.pureTensorO_smul, map_smul, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.LevelSeries

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaKernelFockVectorEqOfFinitePointMoveStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernel_fockVector_eq_of_finite_point_move : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (z : GA D V), z ∈ GfC V → ∀ (e e₂ : AE D) (M : ℕ) (O : Subring ℂ) (f f' : WO V W → ℂ) (a : ℂ), f ∈ trSp ψ V W ΛV ΛW f₀ e M O → f' ∈ trSp ψ V W ΛV ΛW f₀ e₂ M O → om (z, 1) f' = a • f → ∀ (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (Q : MvPolynomial (FVar D W.rank V.rank) ℂ) (s : GA D V) (g : GA D W), a * thetaKO om s g (stdF ψ θ V W sW BW f Q) = thetaKO om (s * z) g (stdF ψ θ V W sW BW f' Q) := by
  first | exact @GlobalTheory.LevelSeries.thetaKO_flip | exact GlobalTheory.LevelSeries.thetaKO_flip | (intros; apply GlobalTheory.LevelSeries.thetaKO_flip <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelHalfLeConjPlaceOfNotLe
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelHalfLeConjPlaceOfNotLe
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

namespace GlobalTheory.LevelSeries

theorem mb_le_conjPl_of_not_le : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (l₂ : Geo.Tor.Level H) (Q : Formalism.L2.DIV.Pl D.host.E), ((l₂.M : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ¬ l₂.Mb ≤ Q.asIdeal → l₂.Mb ≤ (Formalism.L2.DIV.conjPl Q).asIdeal := by
  intro D H l₂ Q hM hnot
  have hprod : l₂.Mb * l₂.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ Q.asIdeal := by
    rw [l₂.prod, Ideal.span_le, Set.singleton_subset_iff]; exact hM
  rcases Ideal.IsPrime.mul_le Q.isPrime |>.1 hprod with h | h
  · exact absurd h hnot
  · rw [Ideal.map_le_iff_le_comap] at h
    intro x hx
    have hx' := h hx
    show Formalism.L2.DIV.starOHom x ∈ Q.asIdeal
    have e : Formalism.L2.DIV.starOHom x = (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) x := by
      apply RingOfIntegers.ext
      have hb := H.bar_eq x
      simp only [RingEquiv.coe_toRingHom] at hb ⊢
      rw [hb]
      exact Formalism.L2.DIV.starO_coe x
    rw [e]; exact hx'

end GlobalTheory.LevelSeries
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelHalfLeConjPlaceOfNotLeStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelHalf_le_conj_place_of_not_le : ∀ (D : D7) (H : Geo.Tor.Host D.host.E) (l₂ : Geo.Tor.Level H) (Q : Formalism.L2.DIV.Pl D.host.E), ((l₂.M : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ¬ l₂.Mb ≤ Q.asIdeal → l₂.Mb ≤ (Formalism.L2.DIV.conjPl Q).asIdeal := by
  first | exact @GlobalTheory.LevelSeries.mb_le_conjPl_of_not_le | exact GlobalTheory.LevelSeries.mb_le_conjPl_of_not_le | (intros; apply GlobalTheory.LevelSeries.mb_le_conjPl_of_not_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCentralFlipThetaTranslateHalfLevel
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

variable {D : D7}

theorem not_mem_of_coprime {a b : ℕ} (h : Nat.Coprime a b) {PP : Formalism.L2.DIV.Pl D.host.E}
    (ha : ((a : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : ((b : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun hb => by
  have h1 : IsCoprime ((a : ℤ) : 𝓞 D.host.E) ((b : ℤ) : 𝓞 D.host.E) :=
    (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom (𝓞 D.host.E))
  obtain ⟨u, v, huv⟩ := h1
  push_cast at huv
  apply PP.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← huv]
  exact add_mem (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)

theorem exists_flip_theta : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (M₀ l : ℕ), ChiData χW χ M₀ → l.Prime → M₀ ≠ 0 → ∃ (Z : Finset (GA D V)) (c : ℕ), (∀ z ∈ Z, z ∈ GfC V) ∧ ∀ (H : Geo.Tor.Host D.host.E) (l₂ : Geo.Tor.Level H) (pd : ℕ), l₂.M = M₀ * pd → Nat.Coprime pd M₀ → Nat.Coprime pd l → Nat.Coprime l₂.M (GlobalTheory.Tow.badN D) → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → ConjIn D σ → χ.ValuesIn (-1 / 2) σ → zeta l₂.M ∈ O → ∀ (e e₂ : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → (∀ PP ∈ P, ((l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsHalfIdem l₂ e₂ → ∃ z₂ ∈ Z, ∃ z₁ ∈ GfC V, OneAt V l z₁ ∧ ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e l₂.M O, ∃ f' ∈ trSp ψ V W ΛV ΛW f₀ e₂ l₂.M O, ∀ (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (Q : MvPolynomial (FVar D W.rank V.rank) ℂ) (s : GA D V) (g : GA D W), (l : ℂ) ^ c * thetaKO om s g (stdF ψ θ V W sW BW f Q) = thetaKO om (s * z₂ * z₁) g (stdF ψ θ V W sW BW f' Q) := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP hodd χ M₀ l hχ hl hM₀
  have hfin : {PP : Formalism.L2.DIV.Pl D.host.E | ((M₀ : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal}.Finite := by
    have h0 : Ideal.span {((M₀ : ℕ) : 𝓞 D.host.E)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hM₀
    refine (Ideal.finite_factors h0).subset fun PP hPP => ?_
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hPP)
  choose zOf hzG hzOne hzFlip using fun T : Finset (Formalism.L2.DIV.Pl D.host.E) =>
    GlobalTheory.T.exists_central_flip_translate_halfPlaces_thetaPair D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T M₀
  choose cOf hcOf using fun T => GlobalTheory.T.flipScalar_primePow_integral_at_levelPlaces D ψ θ V W χV χW om ΛV ΛW sW f₀ hP hodd χ M₀ l hχ hl hM₀ T
  refine ⟨hfin.toFinset.powerset.image zOf, hfin.toFinset.powerset.sup cOf, ?_, ?_⟩
  · intro z hz
    obtain ⟨T, -, rfl⟩ := Finset.mem_image.1 hz
    exact hzG T
  intro H l₂ pd hM hc1 hc2 hbad k _ _ σ la O hla hO hconj hval hz e e₂ P he hPM he₂
  have hoddM : Odd (M₀ * pd) := hM ▸ l₂.odd
  have hoddM₀ : Odd M₀ := (Nat.odd_mul.1 hoddM).1
  have hoddpd : Odd pd := (Nat.odd_mul.1 hoddM).2
  set T₀ := P.filter fun PP => ((M₀ : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∧ ¬ l₂.Mb ≤ PP.asIdeal with hT₀
  set T₁ := P.filter fun PP => ((pd : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal ∧ ¬ l₂.Mb ≤ PP.asIdeal with hT₁
  set P₁ := (P \ T₀) ∪ T₀.image Formalism.L2.DIV.conjPl with hP₁
  have hT₁P₁ : T₁ ⊆ P₁ := fun PP hPP => by
    obtain ⟨h1, h2, -⟩ := Finset.mem_filter.1 hPP
    refine Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨h1, fun h3 => ?_⟩)
    exact not_mem_of_coprime hc1 h2 (Finset.mem_filter.1 h3).2.1
  obtain ⟨⟨eT₀, heT₀⟩, e₁, he₁⟩ := GlobalTheory.T.exists_idempotentSum_subset_and_conjugate_flip D e P T₀ he (Finset.filter_subset _ _)
  obtain ⟨⟨eT₁, heT₁⟩, e₃, he₃⟩ := GlobalTheory.T.exists_idempotentSum_subset_and_conjugate_flip D e₁ P₁ T₁ he₁ hT₁P₁
  have hT₀S : T₀ ∈ hfin.toFinset.powerset :=
    Finset.mem_powerset.2 fun PP hPP => hfin.mem_toFinset.2 (Finset.mem_filter.1 hPP).2.1
  obtain ⟨x₂, hx₂, hstep₂⟩ := hzFlip T₀ eT₀ heT₀ hoddM₀ (Nat.Coprime.coprime_mul_right (hM ▸ hbad)) fun PP hPP => (Finset.mem_filter.1 hPP).2.1
  obtain ⟨z₁, hz₁G, hz₁One, hz₁F⟩ := GlobalTheory.T.exists_central_flip_translate_halfPlaces_thetaPair D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T₁ pd
  obtain ⟨x₁, hx₁, hstep₁⟩ := hz₁F eT₁ heT₁ hoddpd (Nat.Coprime.coprime_mul_left (hM ▸ hbad)) fun PP hPP => (Finset.mem_filter.1 hPP).2.1
  have hsub := GlobalTheory.T.halfTranslates_le_levelHalfTranslates_of_dvd D H l₂ e₂ e₃ _ he₂ he₃ (fun PP hPP => by
    rcases Finset.mem_union.1 hPP with h1 | h1
    · obtain ⟨h2, h3⟩ := Finset.mem_sdiff.1 h1
      rcases Finset.mem_union.1 h2 with h4 | h4
      · obtain ⟨h5, h6⟩ := Finset.mem_sdiff.1 h4
        by_contra h7
        have h8 := hPM PP h5
        rw [hM, Nat.cast_mul] at h8
        rcases PP.isPrime.mem_or_mem h8 with h9 | h9
        · exact h6 (Finset.mem_filter.2 ⟨h5, h9, h7⟩)
        · exact h3 (Finset.mem_filter.2 ⟨h5, h9, h7⟩)
      · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 h4
        obtain ⟨hQ1, -, hQ2⟩ := Finset.mem_filter.1 hQ
        exact GlobalTheory.T.levelHalf_le_conj_place_of_not_le D H l₂ Q (hPM Q hQ1) hQ2
    · obtain ⟨Q, hQ, rfl⟩ := Finset.mem_image.1 h1
      obtain ⟨hQ1, -, hQ2⟩ := Finset.mem_filter.1 hQ
      exact GlobalTheory.T.levelHalf_le_conj_place_of_not_le D H l₂ Q (hPM Q hQ1) hQ2) ψ V W ΛV ΛW f₀ l₂.M O
  have hlO : ((l : ℕ) : ℂ) ∈ O := natCast_mem O l
  have ha : (l : ℂ) ^ (hfin.toFinset.powerset.sup cOf) * flipScal χW V W T₀ M₀ x₂ ∈ O := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le' (Finset.le_sup (f := cOf) hT₀S)
    rw [hd, pow_add, mul_assoc]
    exact mul_mem (pow_mem hlO _) (hcOf T₀ eT₀ x₂ heT₀ (fun PP hPP => (Finset.mem_filter.1 hPP).2.1) hx₂ k σ la O hla hO
      hconj hval hoddM₀ (Nat.Coprime.coprime_mul_right (hM ▸ hbad)))
  have hb : flipScal χW V W T₁ pd x₁ ∈ O :=
    GlobalTheory.T.flipScalar_mem_coefficientRing_auxiliaryLevel D ψ θ V W χV χW om ΛV ΛW sW f₀ hP hodd χ M₀ l pd hχ hl hc1 hc2 (Nat.Coprime.coprime_mul_left (hM ▸ hbad))
      k σ la O hla hO hconj hval T₁ eT₁ x₁ heT₁ (fun PP hPP => (Finset.mem_filter.1 hPP).2.1) hx₁
  refine ⟨zOf T₀, Finset.mem_image_of_mem _ hT₀S, z₁, hz₁G,
    hz₁One l (fun PP hPP => not_mem_of_coprime hc2 (Finset.mem_filter.1 hPP).2.1), fun f hf => ?_⟩
  obtain ⟨F₁, hF₁, hF₁eq⟩ := hstep₂ l₂.M pd e e₁ P O hM
    (fun PP hPP => not_mem_of_coprime (Nat.Coprime.symm hc1) (Finset.mem_filter.1 hPP).2.1) he (Finset.filter_subset _ _) he₁ hz f hf
  obtain ⟨F₂, hF₂, hF₂eq⟩ := hstep₁ l₂.M M₀ e₁ e₃ P₁ O (by rw [hM, mul_comm])
    (fun PP hPP => not_mem_of_coprime hc1 (Finset.mem_filter.1 hPP).2.1) he₁ hT₁P₁ he₃ hz F₁ hF₁
  set c := hfin.toFinset.powerset.sup cOf
  refine ⟨(⟨_, mul_mem ha hb⟩ : O) • F₂, Submodule.smul_mem _ _ (hsub hF₂), fun BW Q s g => ?_⟩
  have hom : om (zOf T₀ * z₁, 1) ((⟨_, mul_mem ha hb⟩ : O) • F₂) = ((l : ℂ) ^ c) • f := by
    have e1 : ((zOf T₀ * z₁, 1) : GA D V × GA D W) = (zOf T₀, 1) * (z₁, 1) := by simp
    rw [e1, map_mul, Module.End.mul_apply, Subring.smul_def]
    change om (zOf T₀, 1) (om (z₁, 1) (((l : ℂ) ^ c * flipScal χW V W T₀ M₀ x₂ * flipScal χW V W T₁ pd x₁) • F₂)) = _
    rw [← smul_smul, map_smul, hF₂eq, ← smul_smul, map_smul, hF₁eq]
  have := GlobalTheory.T.thetaKernel_fockVector_eq_of_finite_point_move D ψ θ V W χV χW om ΛV ΛW sW f₀ hP (zOf T₀ * z₁) (mul_mem (hzG T₀) hz₁G) e e₂ l₂.M O f _ _ hf
    (Submodule.smul_mem _ _ (hsub hF₂)) hom BW Q s g
  rw [← mul_assoc] at this
  exact this

end GlobalTheory.LevelSeries

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCentralFlipThetaTranslateHalfLevelStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_centralFlip_thetaTranslate_halfLevel : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → Odd W.rank → ∀ (χ : Formalism.L2.Host.HChar D.host.E) (M₀ l : ℕ), ChiData χW χ M₀ → l.Prime → M₀ ≠ 0 → ∃ (Z : Finset (GA D V)) (c : ℕ), (∀ z ∈ Z, z ∈ GfC V) ∧ ∀ (H : Geo.Tor.Host D.host.E) (l₂ : Geo.Tor.Level H) (pd : ℕ), l₂.M = M₀ * pd → Nat.Coprime pd M₀ → Nat.Coprime pd l → Nat.Coprime l₂.M (GlobalTheory.Tow.badN D) → ∀ (k : Type) [Field k] [NumberField k] (σ : k →+* ℂ) (la : HeightOneSpectrum (𝓞 k)) (O : Subring ℂ), ((l : ℕ) : 𝓞 k) ∈ la.asIdeal → ValRing σ la O → ConjIn D σ → χ.ValuesIn (-1 / 2) σ → zeta l₂.M ∈ O → ∀ (e e₂ : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e P → (∀ PP ∈ P, ((l₂.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → IsHalfIdem l₂ e₂ → ∃ z₂ ∈ Z, ∃ z₁ ∈ GfC V, OneAt V l z₁ ∧ ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e l₂.M O, ∃ f' ∈ trSp ψ V W ΛV ΛW f₀ e₂ l₂.M O, ∀ (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (Q : MvPolynomial (FVar D W.rank V.rank) ℂ) (s : GA D V) (g : GA D W), (l : ℂ) ^ c * thetaKO om s g (stdF ψ θ V W sW BW f Q) = thetaKO om (s * z₂ * z₁) g (stdF ψ θ V W sW BW f' Q) := by
  first | exact @GlobalTheory.LevelSeries.exists_flip_theta | exact GlobalTheory.LevelSeries.exists_flip_theta | (intros; apply GlobalTheory.LevelSeries.exists_flip_theta <;> assumption)
end
