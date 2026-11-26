module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAddHaarCompletionIntegralMatricesVolOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesEqIffReductionEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyDeterminant
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.ResidueLocPlace

theorem norm_le_one_of_finite {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] (f : O →+* Qbar p)
    (hf : ∀ z : ℤ_[p], f (algebraMap ℤ_[p] O z) = algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p])) (y : O) :
    ‖f y‖ ≤ 1 := by
  have hy : IsIntegral ℤ_[p] y := Algebra.IsIntegral.isIntegral y
  let v := NormedField.valuation (K := Qbar p)
  have hmem : ∀ z : ℤ_[p], ((algebraMap ℚ_[p] (Qbar p)).comp PadicInt.Coe.ringHom) z ∈ v.integer := by
    intro z
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
    have : ‖algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p])‖ ≤ 1 := by
      rw [PadicAlgCl.norm_extends p]; exact PadicInt.norm_le_one z
    exact_mod_cast this
  let φ : ℤ_[p] →+* v.integer := ((algebraMap ℚ_[p] (Qbar p)).comp PadicInt.Coe.ringHom).codRestrict v.integer hmem
  have hI : IsIntegral v.integer (f y) := by
    refine IsIntegral.map_of_comp_eq φ f ?_ hy
    ext z
    simp only [RingHom.comp_apply, hf]
    rfl
  have h := (Valuation.integer.integers v).mem_of_integral hI
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_lt_one_of_mem_maximalIdeal {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Algebra ℤ_[p] O]
    [Module.Finite ℤ_[p] O] (f : O →+* Qbar p)
    (hf : ∀ z : ℤ_[p], f (algebraMap ℤ_[p] O z) = algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p])) {y : O}
    (hy : y ∈ IsLocalRing.maximalIdeal O) : ‖f y‖ < 1 := by
  have hle : ∀ z : O, ‖f z‖ ≤ 1 := norm_le_one_of_finite f hf
  have hfp : ‖f (p : O)‖ = (p : ℝ)⁻¹ := by
    have h1 := hf (p : ℤ_[p])
    rw [map_natCast] at h1
    rw [h1, PadicAlgCl.norm_extends p]
    simp [Padic.norm_p]
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hp0 : (p : O) ≠ 0 := by
    intro h; rw [h, map_zero, norm_zero] at hfp
    have : (0 : ℝ) < (p : ℝ)⁻¹ := by
      have := (Fact.out : p.Prime).pos; positivity
    linarith
  have hpu : ¬ IsUnit (p : O) := by
    rintro ⟨u, hu⟩
    have h2 : f (u : O) * f ((u⁻¹ : Oˣ) : O) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have h3 := congrArg norm h2
    rw [norm_mul, norm_one, hu, hfp] at h3
    have h4 := hle ((u⁻¹ : Oˣ) : O)
    have h5 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h4 h5]
  by_cases hy0 : y = 0
  · rw [hy0, map_zero, norm_zero]; exact zero_lt_one
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨e, u, hpe⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hπ
  obtain ⟨k, w, hyk⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hπ
  have he : e ≠ 0 := by
    rintro rfl; apply hpu; rw [hpe, pow_zero, mul_one]; exact u.isUnit
  have hk : k ≠ 0 := by
    rintro rfl
    rw [hyk, pow_zero, mul_one] at hy
    exact (IsLocalRing.mem_maximalIdeal _).1 hy w.isUnit
  have hu1 : ‖f (u : O)‖ = 1 := by
    have h2 : f (u : O) * f ((u⁻¹ : Oˣ) : O) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
    have h3 := congrArg norm h2
    rw [norm_mul, norm_one] at h3
    have h4 := hle ((u⁻¹ : Oˣ) : O)
    have h6 := hle (u : O)
    have h5 : 0 ≤ ‖f (u : O)‖ := norm_nonneg _
    nlinarith [mul_le_mul_of_nonneg_left h4 h5]
  have key : y ^ e * (u : O) ^ k = (p : O) ^ k * (w : O) ^ e := by
    rw [hpe, hyk]; ring
  have hn := congrArg (fun z => ‖f z‖) key
  simp only [map_mul, map_pow, norm_mul, norm_pow, hu1, one_pow, mul_one, hfp] at hn
  have hw := hle (w : O)
  have hA : ‖f y‖ ^ e ≤ ((p : ℝ)⁻¹) ^ k := by
    rw [hn]
    calc ((p : ℝ)⁻¹) ^ k * ‖f (w : O)‖ ^ e ≤ ((p : ℝ)⁻¹) ^ k * 1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) hw
      _ = _ := mul_one _
  have hB : ((p : ℝ)⁻¹) ^ k < 1 := pow_lt_one₀ (by positivity) hp1 hk
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) he).1 (lt_of_le_of_lt hA hB)

end GlobalTheory.ResidueLocPlace

namespace GlobalTheory.ResidueLocPlace

theorem exists_residue_lift {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (h : p = q) (hp : p.Prime)
    (hq : q.Prime) (ι : Qbar p ≃+* ℂ) (B : ValuationSubring ℂ) (hB : ∀ z, z ∈ B ↔ ‖ι.symm z‖ ≤ 1)
    (κB : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar p)
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[q] O]
    [Module.Finite ℤ_[q] O] (iq : FractionRing O →+* Qbar q)
    (iq_alg : ∀ z : ℤ_[q], iq (algebraMap O (FractionRing O) (algebraMap ℤ_[q] O z)) =
      algebraMap ℚ_[q] (Qbar q) (z : ℚ_[q])) :
    ∃ κ : IsLocalRing.ResidueField O →+* Formalism.CyclotomicNorms.Fbar q, ∀ y : O,
      ∃ hy : (((qCast h ι).toRingHom.comp iq).comp (algebraMap O (FractionRing O))) y ∈ B,
        fbCast h hp hq (κB (IsLocalRing.residue B ⟨_, hy⟩)) = κ (IsLocalRing.residue O y) := by
  subst h
  let f : O →+* Qbar p := iq.comp (algebraMap O (FractionRing O))
  have hf : ∀ z : ℤ_[p], f (algebraMap ℤ_[p] O z) = algebraMap ℚ_[p] (Qbar p) (z : ℚ_[p]) := iq_alg
  have hmem : ∀ y, ι (f y) ∈ B := fun y =>
    (hB _).2 (by rw [RingEquiv.symm_apply_apply]; exact norm_le_one_of_finite f hf y)
  let g : O →+* B := (ι.toRingHom.comp f).codRestrict B.toSubring hmem
  let F : O →+* Formalism.CyclotomicNorms.Fbar p := κB.toRingHom.comp ((IsLocalRing.residue B).comp g)
  have hF : ∀ a ∈ IsLocalRing.maximalIdeal O, F a = 0 := by
    intro a ha
    have hlt := norm_lt_one_of_mem_maximalIdeal f hf ha
    have hg : g a ∈ IsLocalRing.maximalIdeal B := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      rintro ⟨u, hu⟩
      have h1 : ((u : B) : ℂ) * (((u⁻¹ : Bˣ) : B) : ℂ) = 1 := by
        rw [← Subring.coe_mul, Units.mul_inv]; rfl
      rw [hu] at h1
      have h2 : ι (f a) = ((g a : B) : ℂ) := rfl
      rw [← h2] at h1
      have h3 := congrArg (fun z => ‖ι.symm z‖) h1
      simp only [map_mul, RingEquiv.symm_apply_apply, norm_mul, map_one, norm_one] at h3
      have h4 : ‖ι.symm (((u⁻¹ : Bˣ) : B) : ℂ)‖ ≤ 1 := (hB _).1 (((u⁻¹ : Bˣ) : B)).2
      have h5 : 0 ≤ ‖f a‖ := norm_nonneg _
      nlinarith [mul_le_mul_of_nonneg_left h4 h5]
    show κB (IsLocalRing.residue B (g a)) = 0
    rw [(IsLocalRing.residue_eq_zero_iff _).2 hg, map_zero]
  exact ⟨Ideal.Quotient.lift (IsLocalRing.maximalIdeal O) F hF, fun y => ⟨hmem y, rfl⟩⟩

end GlobalTheory.ResidueLocPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InfOfLamLdefEqParamV
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2 Formalism.L2.Host Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.Mem GlobalTheory.Mem.R3
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.WtPar

lemma univ_map_eq_range {α : Type} (n : ℕ) (f : ℕ → α) :
    (Finset.univ : Finset (Fin n)).val.map (fun i : Fin n => f (i : ℕ)) = (Multiset.range n).map f := by
  rw [Fin.univ_val_map, List.ofFn_eq_map, Multiset.range, Multiset.map_coe, ← List.map_coe_finRange_eq_range,
    List.map_map]
  rfl

lemma transport {D : D7} {j : ℕ} {τ : D.what₂.Tau} {n n' : ℕ} (h : n = n')
    (hx : ∃ lam : DomWeight n, Bridge.IsLamPrime (D := D) lam j τ) :
    ∃ lam : DomWeight n', Bridge.IsLamPrime (D := D) lam j τ := by
  subst h; exact hx

lemma lamPrime_add_rho (W : Formalism.IndefR.IndefiniteWeightData.WeightData) (hk : 1 ≤ W.k) (hj : 1 ≤ W.j) (hjm : W.j ≤ W.m)
    (i : ℕ) (hi1 : 1 ≤ i) (hin : i ≤ W.nV) :
    W.lamPrime i + W.rhoNV i = W.uSideTarget i - 1 / 2 := by
  have hN : W.nV = W.p + W.q + W.t := by
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.nV, Formalism.IndefR.IndefiniteWeightData.WeightData.r,
      Formalism.IndefR.IndefiniteWeightData.WeightData.p, Formalism.IndefR.IndefiniteWeightData.WeightData.q]; omega
  have hNq : (W.nV : ℚ) = W.p + W.q + W.t := by exact_mod_cast hN
  simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.lamPrime, Formalism.IndefR.IndefiniteWeightData.WeightData.thetaWt,
    Formalism.IndefR.IndefiniteWeightData.WeightData.dTau, Formalism.IndefR.IndefiniteWeightData.WeightData.rhoNV,
    Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, Formalism.IndefR.IndefiniteWeightData.WeightData.aPlus,
    Formalism.IndefR.IndefiniteWeightData.WeightData.aMinus]
  split_ifs with h1 h2
  · ring
  · rw [hNq]; ring
  · have hc : W.q + 1 - (W.q + 1 - (i - W.p - W.t)) = i - W.p - W.t := by omega
    rw [hc]
    have hc' : ((i - W.p - W.t : ℕ) : ℚ) = i - W.p - W.t := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    rw [hc', hNq]; ring

end GlobalTheory.Mem.WtPar

namespace GlobalTheory.Mem.WtPar

theorem infOf_lamLdef_eq_paramV : ∀ (D : D7) (j : Fin D.R.m) (τ : D.what₂.Tau),
    NG.infOf (Bridge.lamLdef (D := D) D.R.nV ((j : ℕ) + 1) τ).w = NG.paramV D.R (D.hc τ) j (1 / 2) := by
  intro D j τ
  have hk := D.R.m_add_three_le_k
  have hjm := j.2
  have hex : ∃ lam : DomWeight D.R.nV, Bridge.IsLamPrime (D := D) lam ((j : ℕ) + 1) τ := by
    have h0 := GlobalTheory.ForcedWeights.lamLForced D ((j : ℕ) + 1) (by omega) (by omega) τ
    have hr : (D.sp.V ((j : ℕ) + 1)).rank = D.R.nV := D.sp.V_rank _ (by omega) (by omega)
    exact transport hr ⟨_, h0⟩
  have hl : Bridge.IsLamPrime (D := D) (Bridge.lamLdef (D := D) D.R.nV ((j : ℕ) + 1) τ) ((j : ℕ) + 1) τ := by
    unfold Bridge.lamLdef; rw [dite_eq_left hex]; exact hex.choose_spec
  set lam := Bridge.lamLdef (D := D) D.R.nV ((j : ℕ) + 1) τ
  obtain ⟨hj, W, hWk, hWm, hWt, hWj, hWe, hWv, hWb, hw⟩ := hl
  have hWn : W.nV = D.R.nV := by
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.nV, Formalism.IndefR.IndefiniteWeightData.WeightData.r, Ranks.nV, Ranks.r, hWk, hWm, hWt]
  have hWp : W.p = D.R.k + (j : ℕ) := by
    simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.p, hWk, hWj]; omega
  let g : ℕ → ℚ := fun i => W.uSideTarget (i + 1) - 1 / 2

  have hL : NG.infOf lam.w = (Multiset.range D.R.nV).map (fun i => ((g i : ℚ) : ℂ)) := by
    unfold NG.infOf
    rw [← univ_map_eq_range]
    refine Multiset.map_congr rfl fun i _ => ?_
    have h1 := lamPrime_add_rho W (by omega) (by omega) (by omega) ((i : ℕ) + 1) (by omega)
      (by have := i.2; omega)
    have h2 := hw i
    have key : ((lam.w i : ℤ) : ℚ) + ((D.R.nV : ℚ) - 1) / 2 - ((i : ℕ) : ℚ) = g i := by
      simp only [g]
      rw [h2, ← h1]
      simp only [Formalism.IndefR.IndefiniteWeightData.WeightData.rhoNV, hWn]
      push_cast; ring
    have := congrArg (fun x : ℚ => (x : ℂ)) key
    push_cast at this ⊢
    exact this

  let gv : ℕ → ℚ := fun n => (W.v (n + 2) : ℚ) - 1 / 2
  let gb : ℕ → ℚ := fun n => -(W.b (n + 1) : ℚ) - 1 / 2
  let ge : ℕ → ℚ := fun c => -(W.e : ℚ) - 1 / 2 + ((D.R.t : ℚ) - 1 - 2 * c) / 2
  have hR : NG.paramV D.R (D.hc τ) j (1 / 2) =
      ((Multiset.range (D.R.k - 1)).map gv + (Multiset.range D.R.m).map gb
        + (Multiset.range D.R.t).map ge).map (fun x : ℚ => (x : ℂ)) := by
    simp only [Multiset.map_add (f := _), Multiset.map_map]
    unfold NG.paramV
    congr 1
    · congr 1
      · rw [← univ_map_eq_range]
        refine Multiset.map_congr rfl fun i _ => ?_
        simp only [Function.comp, gv, hWv i]
        push_cast; ring
      · rw [← univ_map_eq_range]
        refine Multiset.map_congr rfl fun i _ => ?_
        simp only [Function.comp, gb, hWb i]
        push_cast; ring
    · refine Multiset.map_congr rfl fun c _ => ?_
      have he : (D.hc τ).e j = (W.e : ℚ) := by
        rw [hWe]; congr 1; try (ext; simp)
      simp only [Function.comp, ge, he]
      push_cast; ring
  rw [hL, hR, show (fun i => ((g i : ℚ) : ℂ)) = (fun x : ℚ => (x : ℂ)) ∘ g from rfl, ← Multiset.map_map]
  congr 1

  have hsplit : D.R.nV = ((D.R.k - 1) + ((j : ℕ) + 1)) + D.R.t + (D.R.m - ((j : ℕ) + 1)) := by
    simp only [Ranks.nV, Ranks.r]; omega
  have hmsplit : D.R.m = ((j : ℕ) + 1) + (D.R.m - ((j : ℕ) + 1)) := by omega
  rw [hsplit, Multiset.range_add, Multiset.range_add, Multiset.range_add]
  conv_rhs => rw [hmsplit, Multiset.range_add]
  simp only [Multiset.map_add (f := _), Multiset.map_map]
  have e1 : (Multiset.range (D.R.k - 1)).map g = (Multiset.range (D.R.k - 1)).map gv := by
    refine Multiset.map_congr rfl fun n hn => ?_
    rw [Multiset.mem_range] at hn
    simp only [g, gv, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, Formalism.IndefR.IndefiniteWeightData.WeightData.lam, hWp, hWk]
    rw [if_pos (by omega), if_pos (by omega)]
  have e2 : (Multiset.range ((j : ℕ) + 1)).map (g ∘ fun x => D.R.k - 1 + x) =
      (Multiset.range ((j : ℕ) + 1)).map gb := by
    refine Multiset.map_congr rfl fun n hn => ?_
    rw [Multiset.mem_range] at hn
    simp only [Function.comp, g, gb, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, Formalism.IndefR.IndefiniteWeightData.WeightData.lam,
      hWp, hWk]
    rw [if_pos (by omega), if_neg (by omega)]
    have hh : D.R.k - 1 + n + 1 - (D.R.k - 1) = n + 1 := by omega
    rw [hh]; push_cast; ring
  have e3 : (Multiset.range D.R.t).map (g ∘ fun x => D.R.k - 1 + ((j : ℕ) + 1) + x) =
      (Multiset.range D.R.t).map ge := by
    refine Multiset.map_congr rfl fun c hc => ?_
    rw [Multiset.mem_range] at hc
    simp only [Function.comp, g, ge, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, hWp, hWt]
    rw [if_neg (by omega), if_pos (by omega)]
    have : ((D.R.k - 1 + ((j : ℕ) + 1) + c + 1 : ℕ) : ℚ) - ((D.R.k + (j : ℕ) : ℕ) : ℚ) = c + 1 := by
      rw [show D.R.k - 1 + ((j : ℕ) + 1) + c + 1 = (D.R.k + (j : ℕ)) + (c + 1) by omega]
      push_cast; ring
    rw [this]; ring
  have e4 : (Multiset.range (D.R.m - ((j : ℕ) + 1))).map (g ∘ fun x => D.R.k - 1 + ((j : ℕ) + 1) + D.R.t + x) =
      (Multiset.range (D.R.m - ((j : ℕ) + 1))).map (gb ∘ fun x => (j : ℕ) + 1 + x) := by
    refine Multiset.map_congr rfl fun c hc => ?_
    rw [Multiset.mem_range] at hc
    simp only [Function.comp, g, gb, Formalism.IndefR.IndefiniteWeightData.WeightData.uSideTarget, hWp, hWt, hWj]
    rw [if_neg (by omega), if_neg (by omega)]
    have hh : (j : ℕ) + 1 + (D.R.k - 1 + ((j : ℕ) + 1) + D.R.t + c + 1 - (D.R.k + (j : ℕ)) - D.R.t) = (j : ℕ) + 1 + c + 1 := by omega
    rw [hh]
  rw [e1, e2, e3, e4]
  abel

end GlobalTheory.Mem.WtPar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalEqOfClassesRelatedAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalEqOfClassesRelatedAtPlace
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.HAt.FvOff
open Formalism.L2.GlobalTheoryTheory.LocalLatticeBases


set_option maxHeartbeats 1000000 in
theorem fT_move {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (w : HeightOneSpectrum (𝓞 F)) (hw : (T : 𝓞 F) ∈ w.asIdeal)
    (y y' η κ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E)
    (hκ : κ ∈ S.U) (hη : bc (prV (E := E) w) η = 1)
    (he : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y' = y * η * κ) (z' : Fin n → E)
    (hx : ((bc (prV (E := E) w) y)⁻¹).1 *ᵥ (fun a => inclE (F := F) (w.adicCompletion F) ((γ.1 *ᵥ z') a)) ∈
      latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)))
    (hx' : ((bc (prV (E := E) w) y')⁻¹).1 *ᵥ (fun a => inclE (F := F) (w.adicCompletion F) (z' a)) ∈
      latS (F := F) (w.adicCompletion F) (intV E w) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) :
    S.fT w hw ⟨_, hx'⟩ = S.fT w hw ⟨_, hx⟩ := by
  have hk : y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y' = η * κ := by
    rw [mul_assoc, he]; group
  have hkw : bc (prV (E := E) w) (y⁻¹ * bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y') =
      bc (prV (E := E) w) κ := by
    rw [hk, map_mul, hη, one_mul]
  have hm := GlobalTheory.LevelHecke.MovePair.mov_mulVec w y y' γ z'
  rw [hkw] at hm
  have hloc : bc (prV (E := E) w) κ ∈ S.Uloc w := ((S.U_eq κ).1 hκ).2 w
  rw [S.UlocAlt w hw] at hloc
  obtain ⟨hg, hf⟩ := (Subgroup.mem_inf.1 hloc).2
  rw [← hf ⟨_, hx'⟩]
  congr 1
  exact Subtype.ext hm


set_option maxHeartbeats 1000000 in
theorem fT_adStep {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : StepLevel F E σ J T f bad) (w w' : HeightOneSpectrum (𝓞 F)) (hw : (T : 𝓞 F) ∈ w'.asIdeal) (hne : w' ≠ w)
    (y y' : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E)
    (hA : Formalism.L2.Herm.AdStep σ J S.U y y' γ w) (z z' : Fin n → E) (hz : z = γ.1 *ᵥ z')
    (hx : ((bc (prV (E := E) w') y)⁻¹).1 *ᵥ (fun a => inclE (F := F) (w'.adicCompletion F) (z a)) ∈
      latS (F := F) (w'.adicCompletion F) (intV E w') (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)))
    (hx' : ((bc (prV (E := E) w') y')⁻¹).1 *ᵥ (fun a => inclE (F := F) (w'.adicCompletion F) (z' a)) ∈
      latS (F := F) (w'.adicCompletion F) (intV E w') (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb))) :
    S.fT w' hw ⟨_, hx'⟩ = S.fT w' hw ⟨_, hx⟩ := by
  obtain ⟨κ, hκ, η, -, hη, he⟩ := hA
  subst hz
  exact fT_move S w' hw y y' η κ γ hκ (hη _ hne) he z' hx hx'


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem ld_loc_ch {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)]
    {cc : cl → (D.mem u).C.cls i}
    (K : LevelChart D (D.mem u).A.T (badG D) i hi stab (fun c => clsCrd D u i hi (cc c)))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (c : cl)
    (x : Fin (D.R.N i) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :
    x ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v) (Ld D u i hi (cc c)) ↔
      ((bc (prV (E := D.host.E) v) (K.y c).1)⁻¹).1 *ᵥ x ∈
        latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
          (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb)) := by
  let φ := (D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm)
  letI : Submodule.IsLattice D.host.E (clsCrd D u i hi (cc c)) := bwB_clsCrd_lat D u i hi (cc c)
  have hL : Submodule.IsFullLattice D.host.E (clsCrd D u i hi (cc c)) := by
    constructor
    change Submodule.span D.host.E (((D.clsLat u i (cc c)).map
      (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) = ⊤
    rw [show Submodule.span D.host.E (((D.clsLat u i (cc c)).map
        (φ.toLinearMap.restrictScalars (𝓞 D.host.E)) : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)) : Set (Fin (D.R.N i) → D.host.E)) =
        (Submodule.span D.host.E (D.clsLat u i (cc c) : Set _)).map φ.toLinearMap by
          rw [Submodule.map_span]; rfl,
      (D.clsLat_lat u i (cc c)).span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact φ.surjective
  letI : Submodule.IsLattice D.host.E K.lev.Lb :=
    Submodule.IsLattice.of_fg D.host.E (Module.Finite.iff_fg.1 K.lev.Lb_fin)
  have hLb : Submodule.IsFullLattice D.host.E K.lev.Lb := ⟨K.lev.Lb_span⟩
  refine GlobalTheory.DualCompletion.dual_move D.host.F D.host.E (sigD D) _ (gramN D i hi) v (clsCrd D u i hi (cc c)) K.lev.Lb
    (bc (prV (E := D.host.E) v) (K.y c).1) (bwB_gramN_det D i hi) hL hLb
    (Formalism.UG.P.afsplit_bc_mem _ _ _ _ (K.y c).2) (fun x => ?_) x
  rw [← map_inv]
  exact rlv_yloc v (K.y c).1 (K.y_lat c) x


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem ld_in {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)]
    {cc : cl → (D.mem u).C.cls i}
    (K : LevelChart D (D.mem u).A.T (badG D) i hi stab (fun c => clsCrd D u i hi (cc c)))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (c : cl) (z : Fin (D.R.N i) → D.host.E) (hz : z ∈ Ld D u i hi (cc c)) :
      ((bc (prV (E := D.host.E) v) (K.y c).1)⁻¹).1 *ᵥ (fun a => inclE (F := D.host.F) (v.adicCompletion D.host.F) (z a)) ∈
        latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
          (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb)) :=
  (ld_loc_ch K v c _).1 (Submodule.subset_span ⟨z, hz, rfl⟩)


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem fv_off_cls {D : D7} {u : D.what₂.Word} {A : AtTTied u} {i : ℕ} {hi : i ≤ D.R.m} (P : LvTied u A i hi)
    (K : ClsTied u i hi) (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v) (hT : FvTie P K fMe)
    (v v' : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (γ : GL (Fin (D.R.N i)) D.host.E)
    (hA : Formalism.L2.Herm.AdStep (sigD D) (gramN D i hi) K.lev.U (K.y c).1 (K.y c').1 γ (A.eV v).1) (hv : v' ≠ v)
    (z : Ld D u i hi c) (z' : Ld D u i hi c') (hz : z.1 = γ.1 *ᵥ z'.1) :
    (D.fm u).fv i v' c' (P.pr v' c' z') = (D.fm u).fv i v' c (P.pr v' c z) := by
  have hw : (A.eV v').1 ≠ (A.eV v).1 := fun h => hv (A.eV.injective (Subtype.ext h))
  have hx := ld_in (cc := fun c => c) K.toChart (A.eV v').1 c z.1 z.2
  have hx' := ld_in (cc := fun c => c) K.toChart (A.eV v').1 c' z'.1 z'.2
  have e := fT_adStep K.lev (A.eV v).1 (A.eV v').1 (A.eV v').2 hw (K.y c).1 (K.y c').1 γ hA z.1 z'.1 hz hx hx'
  exact (hT v' c' z' hx').trans ((congrArg (fMe v') e).trans (hT v' c z hx).symm)


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem fv_off_ch {D : D7} {u : D.what₂.Word} {i : ℕ} {hi : i ≤ D.R.m} {Ch : Type} {chOf : (D.mem u).C.cls i → Ch}
    {res : ∀ v, 𝓞 D.host.E →+* (D.mem u).A.Fv v}
    (L : LevelCompatibleLattices (D.fm u) (D.mem u).A.T res i hi (fun c => clsCrd D u i hi c))
    (eV : (D.mem u).A.vT ≃ {v : HeightOneSpectrum (𝓞 D.host.F) // (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal})
    (K : ∀ β : Ch, LevelChart D (D.mem u).A.T (badG D) i hi (fun c : {c // chOf c = β} => (D.mem u).C.stab i c.1)
      (fun c => clsCrd D u i hi c.1))
    (fMe : ∀ β v, (K β).lev.fM (eV v).1 (eV v).2 ≃+ (D.mem u).A.Fv v) (hT : FvTieG L eV K fMe)
    (v v' : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (hβ : chOf c' = chOf c) (γ : GL (Fin (D.R.N i)) D.host.E)
    (hA : Formalism.L2.Herm.AdStep (sigD D) (gramN D i hi) (K (chOf c)).lev.U ((K (chOf c)).y ⟨c, rfl⟩).1
      ((K (chOf c)).y ⟨c', hβ⟩).1 γ (eV v).1) (hv : v' ≠ v)
    (z : LdG D i hi (clsCrd D u i hi c)) (z' : LdG D i hi (clsCrd D u i hi c')) (hz : z.1 = γ.1 *ᵥ z'.1) :
    (D.fm u).fv i v' c' (L.pr v' c' z') = (D.fm u).fv i v' c (L.pr v' c z) := by
  have hw : (eV v').1 ≠ (eV v).1 := fun h => hv (eV.injective (Subtype.ext h))
  have hx := ld_in (cc := fun c : {c' // chOf c' = chOf c} => c.1) (K (chOf c)) (eV v').1 ⟨c, rfl⟩ z.1 z.2
  have hx' := ld_in (cc := fun c : {c' // chOf c' = chOf c} => c.1) (K (chOf c)) (eV v').1 ⟨c', hβ⟩ z'.1 z'.2
  have e := fT_adStep (K (chOf c)).lev (eV v).1 (eV v').1 (eV v').2 hw _ _ γ hA z.1 z'.1 hz hx hx'
  exact (hT v' (chOf c) ⟨c', hβ⟩ z' hx').trans ((congrArg (fMe (chOf c) v') e).trans (hT v' (chOf c) ⟨c, rfl⟩ z hx).symm)


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem fv_eq_of_adC : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (hi : i ≤ (I.rec7 l Z).R.m) v v' (c c' : ((I.rec7 l Z).mem u).C.cls i) (γ : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), AdC (F u) i hi c c' γ ((F u).atT.eV v).1 → v' ≠ v → ∀ (z : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi c) (z' : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi c'), z.1 = γ.1 *ᵥ z'.1 → ((I.rec7 l Z).fm u).fv i v' c' (((F u).lv i hi).pr v' c' z') = ((I.rec7 l Z).fm u).fv i v' c (((F u).lv i hi).pr v' c z) := by
  intro B X I hI hP l Z H F hF hC u i hi v v' c c' γ hA hv z z' hz
  by_cases h : i = 0 ∨ i = (I.rec7 l Z).R.m
  · exact fv_off_cls ((F u).lv i hi) ((F u).cls i hi h) ((F u).fMe i hi h) ((F u).fv i hi h) v v' c c' γ (hA.1 h) hv z z' hz
  · have h1 : 1 ≤ i := by omega
    have h2 : i + 1 ≤ (I.rec7 l Z).R.m := by omega
    obtain ⟨hβ, hA'⟩ := hA.2 h1 h2
    have e := fv_off_ch ((F u).lvC i h1 h2) (F u).atT.eV ((F u).ch i h1 h2) ((F u).fMeC i h1 h2) ((F u).fvC i h1 h2)
      v v' c c' hβ γ hA' hv z z' hz
    have e1 := (pr_lvC_eq_lv I hI hP l Z H F hF hC u i h1 h2 v' c).1 z z rfl
    have e2 := (pr_lvC_eq_lv I hI hP l Z H F hF hC u i h1 h2 v' c').1 z' z' rfl
    exact (congrArg _ e2).symm.trans (e.trans (congrArg _ e1))

end GlobalTheory.Mem.Col2.HAt.FvOff
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalEqOfClassesRelatedAtPlaceStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelFunctional_eq_of_classes_related_at_place : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u i (hi : i ≤ (I.rec7 l Z).R.m) v v' (c c' : ((I.rec7 l Z).mem u).C.cls i) (γ : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E), AdC (F u) i hi c c' γ ((F u).atT.eV v).1 → v' ≠ v → ∀ (z : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi c) (z' : Formalism.L2.Forms.Ld (I.rec7 l Z) u i hi c'), z.1 = γ.1 *ᵥ z'.1 → ((I.rec7 l Z).fm u).fv i v' c' (((F u).lv i hi).pr v' c' z') = ((I.rec7 l Z).fm u).fv i v' c (((F u).lv i hi).pr v' c z) := by
  first | exact @GlobalTheory.Mem.Col2.HAt.FvOff.fv_eq_of_adC | exact GlobalTheory.Mem.Col2.HAt.FvOff.fv_eq_of_adC | (intros; apply GlobalTheory.Mem.Col2.HAt.FvOff.fv_eq_of_adC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValSqNonsplit
noncomputable section

namespace GlobalTheory.HeightCounting.FitTw

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2 _root_.Formalism.L2.Host NumberField IsDedekindDomain Neutral.B1

theorem val_mem_of_ae {L : Type} [Field L] [NumberField L] (χ : HChar L) (Λ : Subgroup ℂˣ)
    (S : Finset (HeightOneSpectrum (𝓞 L))) (ht : ∀ v, χ.TameAt v)
    (hi : ∀ k, χ.inf k = 1) (hu : ∀ v, v ∉ S → χ.UnrAt v) (hv : ∀ v, v ∉ S → χ.val v ∈ Λ)
    {P : HeightOneSpectrum (𝓞 L)} (hPu : χ.UnrAt P) : χ.val P ∈ Λ := by
  classical
  by_cases hP : P ∈ S
  swap
  · exact hv P hP
  obtain ⟨b, hb1, hb2⟩ : ∃ a ∈ P.asIdeal, a ∉ P.asIdeal ^ 2 := by
    have := Ideal.pow_succ_lt_pow P.ne_bot 1 (P := P.asIdeal)
    rw [pow_one] at this
    exact SetLike.exists_of_lt this
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := S) (fun v => v.asIdeal) (fun _ => 2)
    (fun v _ => v.prime) (fun v _ w _ h h' => h (HeightOneSpectrum.ext h')) (fun v => if v.1 = P then b else 1)
  have h1 := ha P hP
  rw [if_pos rfl] at h1
  have ha2 : a ∉ P.asIdeal ^ 2 := fun h => hb2 (by simpa using (P.asIdeal ^ 2).sub_mem h h1)
  have ha1 : a ∈ P.asIdeal := by
    have := P.asIdeal.add_mem (Ideal.pow_le_self two_ne_zero h1) hb1
    simpa using this
  have ha0 : (a : L) ≠ 0 := by
    intro h0
    have h1 : a = 0 := by exact_mod_cast h0
    exact ha2 (h1 ▸ zero_mem _)
  have hval : χ.locK P (Units.mk0 _ ha0) = χ.val P := χ.val_eq hPu _ (by
    unfold IsUnifAt
    rw [TypeValues.val_atFin P _ a rfl, TypeValues.intValuation_eq_of_mem ha1 ha2])
  have h := TypeValues.productRule χ S hu (Units.mk0 _ ha0)
  rw [hi, one_mul, Finset.prod_eq_single_of_mem P hP (fun v hvS hvP => TypeValues.locK_eq_one (ht v) _ a rfl (by
    have h1 := ha v hvS
    rw [if_neg hvP] at h1
    exact Ideal.pow_le_self two_ne_zero h1)), hval] at h
  rw [eq_inv_of_mul_eq_one_left h]
  refine Λ.inv_mem (finprod_induction (· ∈ Λ) Λ.one_mem (fun _ _ => Λ.mul_mem) fun v => ?_)
  exact finprod_induction (· ∈ Λ) Λ.one_mem (fun _ _ => Λ.mul_mem) fun hvS => Λ.zpow_mem (hv v hvS) _

def toHC {E : Type} [Field E] [NumberField E] (χ : HChar E) : NC.HC E := ⟨χ.1, χ.2.1, χ.2.2⟩

theorem of_at {E : Type} [Field E] [NumberField E] (χ : HChar E) (h : NC.HC E) (e : ∀ x, h.χ x = χ.1 x)
    {v : HeightOneSpectrum (𝓞 E)} {α : ℂ} (ha : h.At v α) : χ.UnrAt v ∧ ((χ.val v : ℂˣ) : ℂ) = α := by
  have k := GlobalTheory.HeckeUnifVal.at_val_and_unr_iff χ h (MonoidHom.ext e) v
  have hu : χ.UnrAt v := k.2.2 ha.1
  exact ⟨hu, (k.1 hu).unique ha⟩

attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem val_sq_nonsplit (D : D7) {χ : HChar D.host.E} (ht : χ.TrivOn D.host.F) {v : PlE D.host} (hu : χ.UnrAt v)
    (hv : ¬ IsSplitPl D.host v) : χ.val v ^ 2 = 1 := by
  refine TypeValues.val_sq_eq_one D.sp.cm ht hu ?_
  have h : ∀ x ∈ v.asIdeal, Formalism.L2.Col.cO D.host.E x ∈ v.asIdeal := fun x hx => by
    by_contra hn
    refine hv ⟨x, hx, fun y hy hm => hn ?_⟩
    have : Formalism.L2.Col.cO D.host.E x = y := RingOfIntegers.ext ((Formalism.BasicNotions.bridge_star_holds D.R D.host (x : D.host.E)).trans hy.symm)
    rwa [this]
  refine HeightOneSpectrum.ext (Ideal.ext fun a => ?_)
  rw [Formalism.L2.Col.mem_conjP]
  refine ⟨fun h1 => ?_, h a⟩
  have := h _ h1
  rwa [Formalism.L2.Col.cO_cO] at this

theorem cpow_sqrt (q r t : ℕ) :
    ((q : ℕ) : ℂ) ^ ((((t : ℝ) - 1) / 2 + (1 - ((r + t : ℕ) : ℝ)) / 2 : ℝ) : ℂ) = (Real.sqrt q : ℂ) ^ (-(r : ℤ)) := by
  have h0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have e : (((t : ℝ) - 1) / 2 + (1 - ((r + t : ℕ) : ℝ)) / 2 : ℝ) = (1 / 2 : ℝ) * ((-(r : ℤ) : ℤ) : ℝ) := by
    push_cast; ring
  rw [e, ← Complex.ofReal_natCast, ← Complex.ofReal_cpow h0, Real.rpow_mul h0, Real.rpow_intCast, Real.sqrt_eq_rpow,
    Complex.ofReal_zpow]


set_option maxHeartbeats 1000000 in
theorem psiL_gal {D : D7} {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C} (T : NCharTied D cf C tp)
    (nct : NChTie D C) (hψ : PsiChoiceCompatible D cf C tp) (a : D.nd.Loc) (H1 : NC.HC D.host.E)
    (hH : ∀ (j : Fin D.R.m), j.1 + 1 = D.nd.j a → ∀ x, H1.χ x = (cf.mu0 j * cf.delAt (D.nd.l a) * cf.eta⁻¹).1 x)
    (hr : NC.Read D.nd.plOm.1 (D.ntw.chi1 (D.ntw.twOf a) (D.nd.j a) (D.ntw.twSide a))
      (algebraMap (D.ntw.O0 (D.ntw.twOf a)) (FractionRing (D.ntw.O0 (D.ntw.twOf a))))
      (if D.ntw.twSide a then D.ntw.emb0 (D.ntw.twOf a) else D.ntw.emb0b (D.ntw.twOf a)) (NC.complexEmbeddingRestrictedToSubfield D) H1 (-(D.R.r : ℤ))) :
    IsGalOf D a Set.univ (D.ntw.psiL a) (tp.psi (D.nd.w a)) 0 := by
  classical
  obtain ⟨ψ0, -, h2, h3⟩ := nct.psi_eq
  have hto : ∀ g, toC D a ((D.ntw.psiL a g : (D.nd.O a)ˣ) : D.nd.O a) =
      D.what₂.embLL ((ψ0 (D.nd.w a) g : (D.what₂.LL)ˣ) : D.what₂.LL) := fun g => by
    rw [← D.naut.iota_LL a, h3 a g]
    rfl
  have hP := tp.psi_is (D.nd.w a) (D.nd.w_tw a)
  obtain ⟨B1, h1⟩ := hr
  let j : Fin D.R.m := ⟨D.nd.j a - 1, by have := D.nd.j_range a; omega⟩
  have hj : j.1 + 1 = D.nd.j a := by have := D.nd.j_range a; show D.nd.j a - 1 + 1 = _; omega
  have hone := T.chi_one a j hj
  have htup : tp.tup (D.nd.mu a) j * cf.eta⁻¹ = (cf.mu0 j * cf.delAt (D.nd.l a) * cf.eta⁻¹) * tp.psi (D.nd.w a) := by
    rw [TupTied.tup, D.nd.mu_w, tp.xi_tw, D.nd.w_l]
    rw [← mul_assoc, mul_right_comm _ (tp.psi (D.nd.w a))]
  rw [htup] at hone
  have hfin := NC.finite_placesOver (E := D.host.E) (D.nd.l a)
  let S : Finset (PlE D.host) := B1 ∪ hfin.toFinset ∪ D.nd.S a ∪ D.nd.Q a
  have hu : ∀ v, v ∉ S → (tp.psi (D.nd.w a)).UnrAt v := fun v hv =>
    (hP.ram v).2 (by rw [← nct.Q_eq a]; exact fun h => hv (Finset.mem_union_right _ h))
  have hv : ∀ v, v ∉ S → (tp.psi (D.nd.w a)).val v ∈ RationalValues.unitsIn D.what₂.embLL.fieldRange := fun v hv => by
    show (((tp.psi (D.nd.w a)).val v : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange
    by_cases hs : IsSplitPl D.host v
    swap
    · have h1 : (((tp.psi (D.nd.w a)).val v : ℂˣ) : ℂ) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, val_sq_nonsplit D hP.triv (hu v hv) hs, Units.val_one]
      rcases sq_eq_one_iff.1 h1 with h2 | h2
      · rw [h2]; exact one_mem _
      · rw [h2]; exact neg_mem (one_mem _)
    simp only [S, Finset.mem_union, not_or, Set.Finite.mem_toFinset] at hv
    obtain ⟨⟨⟨v1, v2⟩, v3⟩, v4⟩ := hv
    obtain ⟨α, hα, x1, hx1, hσ1⟩ := h1 v v1
    obtain ⟨σ, hσ⟩ := NC.frob_exists D v
    obtain ⟨hu1, hval⟩ := of_at _ H1 (hH j hj) hα
    have hup : (tp.psi (D.nd.w a)).UnrAt v := (hP.ram v).2 (by rw [← nct.Q_eq a]; exact v4)
    have k := hone v ⟨hs, v2, v3, v4⟩ v2 (fun x hx => by
        change (cf.mu0 j * cf.delAt (D.nd.l a) * cf.eta⁻¹).loc v x * (tp.psi (D.nd.w a)).loc v x = 1
        rw [hu1 x hx, hup x hx, one_mul])
      _ σ (D.nd.plOm.2 v) hσ
    have tw := D.ntw.twO_emb a x1 _ (hσ1 σ hσ)
    have hc : (D.nd.chi a 1 σ : D.nd.O a) =
        D.ntw.twist₂ a (D.ntw.chi1 (D.ntw.twOf a) (D.nd.j a) (D.ntw.twSide a) σ : D.ntw.O0 (D.ntw.twOf a)) *
          (D.ntw.psiL a σ : D.nd.O a) := by
      rw [D.ntw.chi_tw a]
      rfl
    have h4 : toC D a (D.ntw.twist₂ a (D.ntw.chi1 (D.ntw.twOf a) (D.nd.j a) (D.ntw.twSide a) σ :
        D.ntw.O0 (D.ntw.twOf a))) = NC.complexEmbeddingRestrictedToSubfield D x1 := by
      simp only [toC, RingHom.comp_apply, NC.complexEmbeddingRestrictedToSubfield]
      rw [← tw]
      exact D.naut.iota_LL a (x1 : D.what₂.LL)
    have hq := cpow_sqrt (normV v) D.R.r D.R.t
    rw [hc, map_mul, h4, hx1, hto, HChar.val_mul, Units.val_inv_eq_inv_val, Units.val_mul, hval] at k
    have k' : α⁻¹ * (Real.sqrt (normV v) : ℂ) ^ (-(D.R.r : ℤ)) *
        D.what₂.embLL ((ψ0 (D.nd.w a) σ : (D.what₂.LL)ˣ) : D.what₂.LL) =
        (α * (((tp.psi (D.nd.w a)).val v : ℂˣ) : ℂ))⁻¹ * (Real.sqrt (normV v) : ℂ) ^ (-(D.R.r : ℤ)) := by
      rw [← hq]; rw [← hq] at k; exact k
    have hs0 : ((Real.sqrt (normV v) : ℝ) : ℂ) ^ (-(D.R.r : ℤ)) ≠ 0 := by
      have : 0 < Real.sqrt (normV v) := Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero (NC.normV_ne_zero v)))
      exact zpow_ne_zero _ (by exact_mod_cast this.ne')
    have hα0 : α ≠ 0 := by rw [← hval]; exact Units.ne_zero _
    have k2 : D.what₂.embLL ((ψ0 (D.nd.w a) σ : (D.what₂.LL)ˣ) : D.what₂.LL) = (((tp.psi (D.nd.w a)).val v : ℂˣ) : ℂ)⁻¹ := by
      rw [mul_inv, mul_right_comm] at k'
      exact mul_left_cancel₀ (inv_ne_zero hα0) (mul_right_cancel₀ hs0 k')
    rw [← inv_inv (((tp.psi (D.nd.w a)).val v : ℂˣ) : ℂ), ← k2]
    exact inv_mem ⟨_, rfl⟩
  intro v _ hl huv B σ hB hσ
  have : IsTotallyComplex D.host.E := by
    letI := D.host.cmStar
    exact D.sp.cm.cmUnram.1
  obtain ⟨n, hn⟩ := hP.ord
  have hm := val_mem_of_ae _ _ S hP.tame
    (TypeValues.inf_eq_one _ (pow_pos (D.what₂.places.resChar_prime _).pos n) hn) hu hv huv
  obtain ⟨y, hy⟩ : ((((tp.psi (D.nd.w a)).val v)⁻¹ : ℂˣ) : ℂ) ∈ D.what₂.embLL.fieldRange := inv_mem hm
  have k := hψ (D.nd.w a) (D.nd.w_tw a) v ((hP.ram v).1 huv) (by rw [D.nd.w_l]; exact hl) B σ hB hσ y hy
  rw [← h2] at k
  rw [hto, ← (C.embW (D.nd.w a)).injective k]
  simp only [Complex.ofReal_zero, Complex.cpow_zero, mul_one]
  exact hy

theorem psiL_read {D : D7} {χ : HChar D.host.E} (a : D.nd.Loc) (Q : Finset (PlE D.host)) (hQ : ∀ v, v ∉ Q → χ.UnrAt v)
    (h : IsGalOf D a Set.univ (D.ntw.psiL a) χ 0) :
    NC.ReadC D.nd.plOm.1 (D.ntw.psiL a) (NC.iotaC D a) (toHC χ) 0 := by
  classical
  have hfin := NC.finite_placesOver (E := D.host.E) (D.nd.l a)
  refine ⟨hfin.toFinset ∪ Q, fun P hP => ?_⟩
  simp only [Finset.mem_union, not_or, Set.Finite.mem_toFinset] at hP
  have hu := hQ P hP.2
  refine ⟨_, (GlobalTheory.HeckeUnifVal.at_val_and_unr_iff χ (toHC χ) rfl P).1 hu, _, rfl, fun σ hσ => ?_⟩
  have k := h P (Set.mem_univ _) hP.1 hu _ σ (D.nd.plOm.2 P) hσ
  simp only [Complex.ofReal_zero, Complex.cpow_zero, mul_one, Units.val_inv_eq_inv_val] at k
  exact k.trans (mul_one _).symm

theorem psi_is {D : D7} {cf : CharFrame D} {C : NChoice D} (tp : TupTied D cf C) (nct : NChTie D C) (a : D.nd.Loc) :
    IsPsi (D.nd.l a) (D.nd.Q a) (tp.psi (D.nd.w a)) := by
  rw [nct.Q_eq a, ← D.nd.w_l a]
  exact tp.psi_is _ (D.nd.w_tw a)

theorem etaT_link {D : D7} {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C} (T : NCharTied D cf C tp)
    (η : NC.HC D.host.E) (h : ∀ x, η.χ x = cf.eta.1 x) (w : PlE D.host) (α : ℂ) (ha : η.At w α) :
    D.naut.frobEig (D.naut.locG D.naut.etaT w) = {α⁻¹} := by
  obtain ⟨hu, hv⟩ := of_at _ _ h ha
  rw [T.frob _ w (by rw [T.etaT]; exact hu), T.etaT, Units.val_inv_eq_inv_val, hv]

theorem muC_link {D : D7} {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C} (T : NCharTied D cf C tp)
    (K : NC.NChiData D) (h1 : ∀ (j : Fin D.R.m) x, (K.mu0 (j.1 + 1)).χ x = (cf.mu0 j).1 x)
    (h2 : ∀ s x, (K.del s).χ x = (cf.delAt (D.ntw.l s)).1 x) (h3 : ∀ a x, (K.psi a).χ x = (tp.psi (D.nd.w a)).1 x)
    (i : D.nd.Loc) (w : PlE D.host) (α : ℂ) (ha : (K.mu0 (D.nd.j i) * K.del (D.ntw.twOf i) * K.psi i).At w α) :
    D.naut.frobEig (D.naut.locG (D.naut.muC i) w) = {α⁻¹} := by
  let j : Fin D.R.m := ⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩
  have hj : j.1 + 1 = D.nd.j i := by have := D.nd.j_range i; show D.nd.j i - 1 + 1 = _; omega
  have e := T.muC i j hj
  have htup : tp.tup (D.nd.mu i) j = cf.mu0 j * cf.delAt (D.nd.l i) * tp.psi (D.nd.w i) := by
    rw [TupTied.tup, D.nd.mu_w, tp.xi_tw, D.nd.w_l, ← mul_assoc]
  obtain ⟨hu, hv⟩ := of_at (tp.tup (D.nd.mu i) j) _ (fun x => by
    rw [htup]
    change ((K.mu0 (D.nd.j i)).χ x * (K.del (D.ntw.twOf i)).χ x) * (K.psi i).χ x = _
    rw [← hj, h1, h2, h3, D.ntw.twOf_l]
    rfl) ha
  rw [T.frob _ w (by rw [e]; exact hu), e, Units.val_inv_eq_inv_val, hv]

theorem psiL_gal' {D : D7} {cf : CharFrame D} {C : NChoice D} {tp : TupTied D cf C} (T : NCharTied D cf C tp)
    (nct : NChTie D C) (hψ : PsiChoiceCompatible D cf C tp) (K : NC.NChiData D) (h0 : ∀ x, K.etaT.χ x = cf.eta.1 x)
    (h1 : ∀ (j : Fin D.R.m) x, (K.mu0 (j.1 + 1)).χ x = (cf.mu0 j).1 x)
    (h2 : ∀ s x, (K.del s).χ x = (cf.delAt (D.ntw.l s)).1 x)
    (hr : ∀ s j (b : Bool), 1 ≤ j → j ≤ D.R.m → NC.Read D.nd.plOm.1 (D.ntw.chi1 s j b)
      (algebraMap (D.ntw.O0 s) (FractionRing (D.ntw.O0 s))) (if b then D.ntw.emb0 s else D.ntw.emb0b s) (NC.complexEmbeddingRestrictedToSubfield D)
      (K.firstHeckeCharacter s j) (-(D.R.r : ℤ))) (a : D.nd.Loc) :
    IsGalOf D a Set.univ (D.ntw.psiL a) (tp.psi (D.nd.w a)) 0 :=
  psiL_gal T nct hψ a _ (fun j hj x => by
    change ((K.mu0 (D.nd.j a)).χ x * (K.del (D.ntw.twOf a)).χ x) * (K.etaT.χ x)⁻¹ = _
    rw [← hj, h1, h2, h0, D.ntw.twOf_l]
    rfl) (hr _ _ _ (D.nd.j_range a).1 (D.nd.j_range a).2)

end GlobalTheory.HeightCounting.FitTw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MuZeroCharLocKCongruentRationalInteger
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MuZeroCharLocKCongruentRationalInteger
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.MuZeroCong

theorem locK_eq_of_sub_mem : ∀ {R : Ranks} {H : Host R} (P : PiBar H) (W : Omg H) (e : ↥(R.Psi) → ℚ) (j : ℕ) (χ : HChar H.E), IsMu0 P W e j χ → ∀ (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)), P.Div k w → ∀ (u : 𝓞 H.E) (hu : (u : H.E) ≠ 0) (a : ℕ) (ha : a.Coprime (H.g k)), u - (a : 𝓞 H.E) ∈ w.asIdeal → χ.locK w (Units.mk0 (u : H.E) hu) = (W.om k (ZMod.unitOfCoprime a ha) ^ (2 * (j + 1)))⁻¹ := by
  intro R H P W e j χ hχ k w hw u hu a ha hua
  have hg : ((H.g k : ℕ) : 𝓞 H.E) ∈ w.asIdeal := by
    have h1 := P.pb_over k
    rw [← hw, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at h1
    exact h1
  have ha_nm : ((a : ℕ) : 𝓞 H.E) ∉ w.asIdeal := by
    intro haw
    apply w.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have hb := Nat.gcd_eq_gcd_ab a (H.g k)
    rw [Nat.Coprime.gcd_eq_one ha, Nat.cast_one] at hb
    have h1 : (1 : 𝓞 H.E) = ((a : ℕ) : 𝓞 H.E) * ((Nat.gcdA a (H.g k) : ℤ) : 𝓞 H.E)
        + ((H.g k : ℕ) : 𝓞 H.E) * ((Nat.gcdB a (H.g k) : ℤ) : 𝓞 H.E) := by
      have := congrArg (Int.cast : ℤ → 𝓞 H.E) hb
      push_cast at this
      exact this
    rw [h1]
    exact add_mem (Ideal.mul_mem_right _ _ haw) (Ideal.mul_mem_right _ _ hg)
  have hu_nm : u ∉ w.asIdeal := by
    intro huw
    apply ha_nm
    have := Ideal.sub_mem _ huw hua
    simpa using this
  have ha0 : ((a : ℕ) : H.E) ≠ 0 := by
    intro h0
    apply ha_nm
    have : ((a : ℕ) : 𝓞 H.E) = 0 := by
      apply RingOfIntegers.coe_injective
      push_cast
      exact h0
    rw [this]
    exact zero_mem _
  set A : H.Eˣ := Units.mk0 ((a : ℕ) : H.E) ha0 with hA
  set U : H.Eˣ := Units.mk0 (u : H.E) hu with hU
  have hsplit : U = (U * A⁻¹) * A := by group
  have hval : ∀ r : 𝓞 H.E, Valued.v (((r : H.E)) : w.adicCompletion H.E) = w.intValuation r := by
    intro r
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact w.valuation_of_algebraMap r
  have hYval : ((U * A⁻¹ : H.Eˣ) : H.E) = (u : H.E) * ((a : ℕ) : H.E)⁻¹ := by
    simp [hA, hU]
  have hvu : w.intValuation u = 1 := (w.intValuation_eq_one_iff_mem_primeCompl u).mpr hu_nm
  have hva : w.intValuation ((a : ℕ) : 𝓞 H.E) = 1 :=
    (w.intValuation_eq_one_iff_mem_primeCompl _).mpr ha_nm
  have hvd : w.intValuation (u - ((a : ℕ) : 𝓞 H.E)) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) := by
    rw [w.intValuation_le_pow_iff_mem, pow_one]
    exact hua
  have hacoe : (((a : ℕ) : 𝓞 H.E) : H.E) = ((a : ℕ) : H.E) := by push_cast; rfl
  have hv' : ∀ x : H.E, Valued.v (algebraMap H.E (w.adicCompletion H.E) x) = w.valuation H.E x :=
    fun x => w.valuedAdicCompletion_eq_valuation' x
  have hY1 : χ.locK w (U * A⁻¹) = 1 := by
    show χ.loc w (atFin w (U * A⁻¹)) = 1
    apply hχ.tame w
    · show Valued.v (algebraMap H.E (w.adicCompletion H.E) ((U * A⁻¹ : H.Eˣ) : H.E)) = 1
      rw [hv', hYval, Valuation.map_mul, Valuation.map_inv, ← hacoe]
      rw [show (u : H.E) = algebraMap (𝓞 H.E) H.E u from rfl,
        show (((a : ℕ) : 𝓞 H.E) : H.E) = algebraMap (𝓞 H.E) H.E ((a : ℕ) : 𝓞 H.E) from rfl,
        w.valuation_of_algebraMap, w.valuation_of_algebraMap, hvu, hva, inv_one, mul_one]
    · show Valued.v (algebraMap H.E (w.adicCompletion H.E) ((U * A⁻¹ : H.Eˣ) : H.E) - 1) ≤ _
      rw [← map_one (algebraMap H.E (w.adicCompletion H.E)), ← map_sub, hv', hYval]
      have hq : (u : H.E) * ((a : ℕ) : H.E)⁻¹ - 1
          = algebraMap (𝓞 H.E) H.E (u - ((a : ℕ) : 𝓞 H.E)) * (algebraMap (𝓞 H.E) H.E ((a : ℕ) : 𝓞 H.E))⁻¹ := by
        rw [map_sub, map_natCast]
        field_simp
      rw [hq, Valuation.map_mul, Valuation.map_inv, w.valuation_of_algebraMap, w.valuation_of_algebraMap, hva,
        inv_one, mul_one]
      exact hvd
  have hAv := hχ.atg k w hw a ha A rfl
  rw [hsplit, map_mul, hY1, one_mul, hAv]

end GlobalTheory.MuZeroCong
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MuZeroCharLocKCongruentRationalIntegerStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.muZeroChar_locK_congruent_rational_integer : ∀ {R : Ranks} {H : Host R} (P : PiBar H) (W : Omg H) (e : ↥(R.Psi) → ℚ) (j : ℕ) (χ : HChar H.E), IsMu0 P W e j χ → ∀ (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)), P.Div k w → ∀ (u : 𝓞 H.E) (hu : (u : H.E) ≠ 0) (a : ℕ) (ha : a.Coprime (H.g k)), u - (a : 𝓞 H.E) ∈ w.asIdeal → χ.locK w (Units.mk0 (u : H.E) hu) = (W.om k (ZMod.unitOfCoprime a ha) ^ (2 * (j + 1)))⁻¹ := by
  first | exact @GlobalTheory.MuZeroCong.locK_eq_of_sub_mem | exact GlobalTheory.MuZeroCong.locK_eq_of_sub_mem | (intros; apply GlobalTheory.MuZeroCong.locK_eq_of_sub_mem <;> assumption)
end
end
