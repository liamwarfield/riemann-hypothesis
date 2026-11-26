module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeDegree
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDehomCharpolyForms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.CSandwichStD
public import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.IntegralMonoInnerEqZero
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ChangeOfModel
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameFibrePt

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPullConeDegreeInt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def PullConeDegreeInt.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι) (N M : ℕ),
    (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) → (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (L j) e) →
    (∀ c : ∀ k, ι k, (M : MRing ι) * (∏ k, (X ⟨k, c k⟩ : MRing ι)) ^ N ∈ coneNullIdealZ y L) →
    ∀ (d : K → ℕ) (g : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g d → (∀ k, e k + N * Fintype.card (ι k) ≤ d k) →
      ∃ a : Fin (D + 1) → MRing ι, (∀ j, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (a j) (d - e)) ∧
        (M : Ω) * aeval y g = ∑ j, aeval y (a j) * aeval y (L j)

section Inhabitants

open ProjLine

end Inhabitants

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PDehomNormPIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

namespace DehomNormPIntegral

theorem padicValRat_nonneg_of_mem {p : ℕ} [Fact p.Prime] {q : ℚ}
    (hq : q ∈ (Rat.padicValuation p).valuationSubring) : 0 ≤ padicValRat p q := by
  rw [Valuation.mem_valuationSubring_iff, Rat.padicValuation_le_one_iff] at hq
  rw [padicValRat_def, padicValNat.eq_zero_of_not_dvd hq]
  simp

theorem inv_natCast_mem {p : ℕ} [Fact p.Prime] {M : ℕ} (hM : ¬ p ∣ M) :
    ((M : ℚ)⁻¹) ∈ (Rat.padicValuation p).valuationSubring := by
  have hM0 : M ≠ 0 := fun h => hM (h ▸ dvd_zero p)
  rw [Valuation.mem_valuationSubring_iff, Rat.padicValuation_le_one_iff, Rat.inv_natCast_den, if_neg hM0]
  exact hM

theorem mem_range_map_iff {τ : Type*} (V : Subring ℚ) (F : MvPolynomial τ ℚ) :
    F ∈ (map V.subtype).range ↔ ∀ ν, F.coeff ν ∈ V := by
  classical
  constructor
  · rintro ⟨F', rfl⟩ ν
    rw [coeff_map]
    exact (F'.coeff ν).2
  · intro h
    refine ⟨∑ ν ∈ F.support, monomial ν ⟨F.coeff ν, h ν⟩, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [map_monomial]
    exact F.support_sum_monomial_coeff

theorem isIntegral_of_le_range {R Ω : Type*} [CommRing R] [CommRing Ω] [Algebra R Ω] (B : Subalgebra ℤ Ω)
    (hB : ∀ b ∈ B, ∃ r, algebraMap R Ω r = b) {x : Ω} (hx : IsIntegral B x) : IsIntegral R x := by
  obtain ⟨Q, hQm, hQ⟩ := hx
  have hl : Q.map (algebraMap B Ω) ∈ Polynomial.lifts (algebraMap R Ω) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro k
    rw [Polynomial.coeff_map]
    exact hB _ (Q.coeff k).2
  obtain ⟨Q', hQ', -, hQ'm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hQm.map _)
  refine ⟨Q', hQ'm, ?_⟩
  rw [← Polynomial.eval_map, hQ', Polynomial.eval_map]
  exact hQ

theorem coeff_mem_of_dehom_coeff_mem {Ω : Type} [Field Ω] [CharZero Ω] {D : ℕ} {l : Fin (D + 1) → Ω}
    (hgen : ∀ (d : ℕ) (F : MvPolynomial (Fin (D + 1)) ℚ), F.IsHomogeneous d → aeval l F = 0 → F = 0)
    (j : Fin (D + 1)) {N : ℕ} {F : MvPolynomial (Fin (D + 1)) ℚ} (hF : F.IsHomogeneous N) (V : Subring ℚ)
    (hG : ∀ ν, (PullFormsGeneric.dehom j F).coeff ν ∈ V) (μ : Fin (D + 1) →₀ ℕ) : F.coeff μ ∈ V := by
  classical
  have hl := DehomCharpolyForms.ne_zero_of_generic hgen
  have hlj := hl j
  set H := rename Subtype.val (PullFormsGeneric.dehom j F) with hHdef
  set N2 := max N H.totalDegree with hN2
  have hHW : H ∈ (map V.subtype).range := by
    obtain ⟨G', hG'⟩ := (mem_range_map_iff V _).mpr hG
    exact ⟨rename Subtype.val G', by rw [map_rename, hG']⟩
  have hK : DehomCharpolyForms.homog j N2 H = X j ^ (N2 - N) * F := by
    have hF2 : (X j ^ (N2 - N) * F).IsHomogeneous N2 := by
      have := (isHomogeneous_X_pow (R := ℚ) j (N2 - N)).mul hF
      rwa [Nat.sub_add_cancel (le_max_left _ _)] at this
    refine sub_eq_zero.mp (hgen N2 _ ((DehomCharpolyForms.isHomogeneous_homog j N2 H).sub hF2) ?_)
    have hfun : (fun i => if h : i = j then (1 : Ω) else ((fun i => l i / l j) ∘ (Subtype.val : {i // i ≠ j} → Fin (D + 1))) ⟨i, h⟩) =
        fun i => l i / l j := by
      funext i
      split_ifs with h
      · subst h
        exact (div_self (hl _)).symm
      · rfl
    have hval : aeval (fun i => l i / l j) H = aeval (fun i => l i / l j) F := by
      rw [hHdef, aeval_rename, PullFormsGeneric.aeval_dehom, hfun]
    rw [map_sub, DehomCharpolyForms.aeval_homog l j hlj H (le_max_right _ _), hval,
      DehomCharpolyForms.aeval_div_of_isHomogeneous l j hF, map_mul, map_pow, aeval_X, sub_eq_zero]
    have : l j ^ N2 = l j ^ (N2 - N) * l j ^ N := by rw [← pow_add, Nat.sub_add_cancel (le_max_left _ _)]
    rw [this, inv_pow]
    field_simp
  have hKW : X j ^ (N2 - N) * F ∈ (map V.subtype).range := by
    rw [← hK, DehomCharpolyForms.homog]
    refine Subring.sum_mem _ fun e _ => Subring.mul_mem _ ⟨X j ^ (N2 - e), by simp⟩ ?_
    rw [mem_range_map_iff]
    intro ν
    rw [coeff_homogeneousComponent]
    split_ifs
    · exact (mem_range_map_iff V H).mp hHW ν
    · exact V.zero_mem
  have h1 : AddMonoidAlgebra.coeff (X j ^ (N2 - N) * F) (μ + Finsupp.single j (N2 - N)) = AddMonoidAlgebra.coeff F μ := by
    rw [X_pow_eq_monomial, mul_comm, coeff_mul_monomial, mul_one]
  rw [← h1]
  exact (mem_range_map_iff V _).mp hKW _

end DehomNormPIntegral


open DehomCharpolyForms DehomNormPIntegral in
theorem DehomNormPIntegral.proof : DehomNormPIntegral.Statement := by
  intro Ω _ _ D l P _ hP hgen p hp M hM j m u hu c hchom hcp μ
  classical
  have := Fact.mk hp
  have hl := ne_zero_of_generic hgen
  set n := Module.finrank P Ω with hn
  set f := LinearMap.charpoly (Algebra.lmul P Ω u) with hf

  have h0 : algebraMap P Ω (f.coeff 0) = aeval (fun i => l i / l j) (c n) := by
    have := congrArg (fun g => _root_.AddMonoidAlgebra.coeff (M := ℕ) g 0) hcp
    simp only [Polynomial.coeff_map, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow] at this
    rw [this, Finset.sum_eq_single n]
    · simp
    · intro b hb hbn
      have : b < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)) hbn
      rw [if_neg (by omega)]
    · intro h
      simp at h

  have hdet := LinearMap.det_eq_sign_charpoly_coeff (Algebra.lmul P Ω u)
  rw [← Algebra.norm_apply, ← hf] at hdet
  have hc0 : f.coeff 0 = (-1) ^ n * Algebra.norm P u := by
    rw [hdet, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

  let V := (Rat.padicValuation p).valuationSubring
  let σ := {i // i ≠ j}
  have hmemP : ∀ i, l i / l j ∈ P := fun i => hP ▸ IntermediateField.subset_adjoin ℚ _ ⟨i, j, hl j, rfl⟩
  let tP : σ → P := fun i => ⟨l i / l j, hmemP i⟩
  let ω : σ → Ω := fun i => l i / l j
  let _ : Algebra (MvPolynomial σ V) (MvPolynomial σ ℚ) := MvPolynomial.algebraMvPolynomial
  let ψP : MvPolynomial σ V →+* P :=
    (aeval tP : MvPolynomial σ ℚ →ₐ[ℚ] P).toRingHom.comp (algebraMap (MvPolynomial σ V) (MvPolynomial σ ℚ))
  let _ : Algebra (MvPolynomial σ V) P := ψP.toAlgebra
  let _ : Algebra (MvPolynomial σ V) Ω := (P.val.toRingHom.comp ψP).toAlgebra
  have _ : IsScalarTower (MvPolynomial σ V) P Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let fA : MvPolynomial σ ℚ →ₐ[MvPolynomial σ V] Ω :=
    { (aeval ω : MvPolynomial σ ℚ →ₐ[ℚ] Ω).toRingHom with
      commutes' := fun r => by
        show aeval ω _ = P.val (aeval tP _)
        exact (DFunLike.congr_fun (comp_aeval (f := tP) P.val) _).symm }
  have hfA : ∀ G, fA G = aeval ω G := fun _ => rfl
  have hinj : Function.Injective fA := by
    intro a b hab
    exact injective_chart hgen j (by rw [← hfA, ← hfA]; exact hab)
  have halg : ∀ r, algebraMap (MvPolynomial σ V) Ω r =
      aeval ω (map (algebraMap V ℚ) r) := fun r => ((fA.commutes r).symm.trans (hfA _)).trans rfl

  have hB : ∀ b ∈ Algebra.adjoin ℤ (insert ((M : Ω)⁻¹) (Set.range fun i => l i / l j)),
      ∃ r, algebraMap (MvPolynomial σ V) Ω r = b := by
    intro b hb
    have hle : Algebra.adjoin ℤ (insert ((M : Ω)⁻¹) (Set.range fun i => l i / l j)) ≤
        ((Algebra.ofId (MvPolynomial σ V) Ω).range).restrictScalars ℤ := by
      refine Algebra.adjoin_le ?_
      rintro _ (rfl | ⟨i, rfl⟩)
      · refine ⟨C ⟨(M : ℚ)⁻¹, inv_natCast_mem hM⟩, ?_⟩
        show algebraMap _ Ω _ = _
        rw [halg]
        simp
      · by_cases h : i = j
        · subst h
          refine ⟨1, ?_⟩
          show algebraMap _ Ω _ = _
          rw [map_one]
          exact (div_self (hl i)).symm
        · refine ⟨X ⟨i, h⟩, ?_⟩
          show algebraMap _ Ω _ = _
          rw [halg]
          simp [ω]
    obtain ⟨r, hr⟩ := hle hb
    exact ⟨r, hr⟩
  have hu' : IsIntegral (MvPolynomial σ V) u := isIntegral_of_le_range _ hB ((mem_integralClosure_iff _ _).mp hu)
  have hN : IsIntegral (MvPolynomial σ V) (algebraMap P Ω (Algebra.norm P u)) :=
    (Algebra.isIntegral_norm P hu').algebraMap
  have hx : IsIntegral (MvPolynomial σ V) (aeval (fun i => l i / l j) (c n)) := by
    rw [← h0, hc0, map_mul, map_pow, map_neg, map_one]
    exact (isIntegral_one.neg.pow n).mul hN

  have hdeh : aeval ω (PullFormsGeneric.dehom j (c n)) = aeval (fun i => l i / l j) (c n) := by
    rw [PullFormsGeneric.aeval_dehom]
    refine congrArg (fun g => aeval g (c n)) (funext fun i => ?_)
    split_ifs with h
    · subst h
      exact (div_self (hl _)).symm
    · rfl
  have hG : IsIntegral (MvPolynomial σ V) (PullFormsGeneric.dehom j (c n)) :=
    (isIntegral_algHom_iff fA hinj).mp (by rw [hfA, hdeh]; exact hx)
  have hGc : ∀ ν, (PullFormsGeneric.dehom j (c n)).coeff ν ∈ V.toSubring := by
    intro ν
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp (MvPolynomial.isIntegral_iff_isIntegral_coeff.mp hG ν)
    rw [← hy]
    exact y.2
  exact padicValRat_nonneg_of_mem (coeff_mem_of_dehom_coeff_mem hgen j (hchom) V.toSubring hGc μ)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseChi
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory

noncomputable section

theorem VeroneseChi.proof (hB : VeroneseMonoBasis.Statement) (hG : VeroneseGramMono.Statement) :
    VeroneseChi.Statement := by
  classical
  intro D _ n
  obtain ⟨bM, hM, hMv⟩ := hB D n
  have h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix (Veronese.Idx D)) ℚ), IsSecBasis (Veronese.x D) n p.2 :=
    ⟨⟨_, bM⟩, hM⟩
  unfold Veronese.chi
  rw [dite_eq_left h]
  have hp := h.choose_spec
  generalize h.choose = p at hp ⊢
  obtain ⟨r', b'⟩ := p
  have hp' : IsSecBasis (Veronese.x D) n b' := hp
  have hr : r' = (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card := hp'.card_eq.trans hM.card_eq.symm
  subst hr
  have hA : ∀ k, ∃ c : Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card → ℤ,
      ∑ l, c l • aeval (Veronese.x D) (bM l) = aeval (Veronese.x D) (b' k) := fun k =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp
      (by rw [hM.2.2, ← hp'.2.2]; exact Submodule.subset_span ⟨k, rfl⟩)
  have hB' : ∀ l, ∃ c : Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card → ℤ,
      ∑ m, c m • aeval (Veronese.x D) (b' m) = aeval (Veronese.x D) (bM l) := fun l =>
    (Submodule.mem_span_range_iff_exists_fun ℤ).mp
      (by rw [hp'.2.2, ← hM.2.2]; exact Submodule.subset_span ⟨l, rfl⟩)
  choose A hA using hA
  choose B hB' using hB'
  have hAB : Matrix.of A * Matrix.of B = 1 := by
    ext k m
    have h1 : ∑ m, (Matrix.of A * Matrix.of B) k m • aeval (Veronese.x D) (b' m) =
        aeval (Veronese.x D) (b' k) := by
      simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_smul, mul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum, hB']
      exact hA k
    have h2 : ∑ m, (1 : Matrix (Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card)
        (Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card) ℤ) k m • aeval (Veronese.x D) (b' m) =
        aeval (Veronese.x D) (b' k) := by
      simp [Matrix.one_apply]
    have hli := Fintype.linearIndependent_iff.mp hp'.2.1
      (fun m => (Matrix.of A * Matrix.of B) k m - (1 : Matrix _ _ ℤ) k m)
      (by simp only [sub_smul, Finset.sum_sub_distrib, h1, h2, sub_self]) m
    exact sub_eq_zero.mp hli
  have hdet : (Matrix.of A).det ^ 2 = 1 := by
    have hd := congrArg Matrix.det hAB
    rw [Matrix.det_mul, Matrix.det_one] at hd
    exact Int.isUnit_sq (isUnit_iff_exists_inv.mpr ⟨_, hd⟩)
  have hGb := hG D n _ b' (Matrix.of A) fun k => by
    rw [← hA k]
    simp only [hMv, zsmul_eq_mul, Matrix.of_apply]
  rw [hGb]
  have hdA : ((Matrix.of A).map (Int.cast : ℤ → ℝ)).det = ((Matrix.of A).det : ℝ) :=
    ((Int.castRingHom ℝ).map_det (Matrix.of A)).symm
  have hdet' : ((Matrix.of A).det : ℝ) ^ 2 = 1 := by exact_mod_cast hdet
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, hdA]
  have hprod : ((Matrix.of A).det : ℝ) * (∏ k, monoNormSq (adtEnum D (2 * n) k)) * ((Matrix.of A).det : ℝ) =
      ∏ k, monoNormSq (adtEnum D (2 * n) k) := by
    linear_combination (∏ k, monoNormSq (adtEnum D (2 * n) k)) * hdet'
  rw [hprod, Real.log_prod (fun k _ => (monoNormSq_pos (adtEnum D (2 * n) k)).ne'), chiP,
    sum_adtEnum D (2 * n) (fun a => Real.log (monoNormSq a))]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFibreNormDehomIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

namespace FibreNormDehomIntegral

theorem den_eq_one_of_padicValRat_nonneg {a : ℚ} (h : ∀ p : ℕ, p.Prime → 0 ≤ padicValRat p a) : a.den = 1 := by
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have := Fact.mk hp
  have hnum : ¬ (p : ℤ) ∣ a.num := by
    intro hn
    have h1 : p ∣ Nat.gcd a.num.natAbs a.den := Nat.dvd_gcd (Int.ofNat_dvd_left.mp hn) hpd
    rw [a.reduced.gcd_eq_one] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have h0 := h p hp
  rw [padicValRat, padicValInt.eq_zero_of_not_dvd hnum] at h0
  have h2 : 1 ≤ multiplicity p a.den := one_le_multiplicity_of_dvd a.den_ne_zero hpd
  omega

end FibreNormDehomIntegral


open FibreNormDehomIntegral in
theorem FibreNormDehomIntegral.proof (hF : FibreNormBadPrimesFinite.Statement)
    (hG : FibreNormGoodPrimeIntegral.Statement) (hB : FibreNormPrimeBound.Statement) :
    FibreNormDehomIntegral.Statement := by
  classical
  intro K _ ι _ Ω _ _ y D e L q hV hBir he hL hz
  have hSf := hF K ι Ω y D e L hV hBir he hL hz
  set T := hSf.toFinset with hT
  choose! C hC using hB K ι Ω y D e L q hV hBir he hL hz
  have hTp : ∀ p ∈ T, p.Prime := fun p hp => ((Set.Finite.mem_toFinset hSf).mp hp).1
  set M₀ : ℕ := ∏ p ∈ T, p ^ C p with hM
  have hM0 : M₀ ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => pow_ne_zero _ (hTp p hp).ne_zero
  refine ⟨M₀, Nat.one_le_iff_ne_zero.mpr hM0, ?_⟩
  intro τ s hs j c hc

  have hcoef : ∀ m, (((M₀ : ℚ) ^ τ) * (c (Module.finrank (pullField y L) Ω)).coeff m).den = 1 := by
    intro m
    by_cases ha : (c (Module.finrank (pullField y L) Ω)).coeff m = 0
    · rw [ha, mul_zero]; rfl
    refine den_eq_one_of_padicValRat_nonneg fun p hp => ?_
    have := Fact.mk hp
    have hMq : ((M₀ : ℚ) ^ τ) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hM0)
    rw [padicValRat.mul hMq ha, padicValRat.pow, padicValRat.of_nat]
    by_cases hpT : p ∈ T
    · have hle : C p ≤ multiplicity p M₀ :=
        (multiplicity_dvd_iff_le hM0).mp (Finset.dvd_prod_of_mem (fun p => p ^ C p) hpT)
      have hb := hC p hp τ s hs j c hc m
      have hle' : ((C p * τ : ℕ) : ℤ) ≤ (τ : ℤ) * (multiplicity p M₀ : ℤ) := by
        push_cast
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast hle) (by positivity)
      linarith
    · have hgood : ¬ HasCommonZeroModP y L p hp := fun h =>
        hpT ((Set.Finite.mem_toFinset hSf).mpr ⟨hp, h⟩)
      have hg := hG K ι Ω y D e L q hV hBir he hL hz p hp hgood τ s hs j c hc m
      have : (0 : ℤ) ≤ (τ : ℤ) * (multiplicity p M₀ : ℤ) := by positivity
      linarith

  have hmem : ((M₀ : ℚ) ^ τ) • c (Module.finrank (pullField y L) Ω) ∈
      Set.range (map (Int.castRingHom ℚ) : MvPolynomial (Fin (D + 1)) ℤ → MvPolynomial (Fin (D + 1)) ℚ) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro a ha
    obtain ⟨m, -, rfl⟩ := mem_coeffs_iff.mp ha
    refine ⟨(((M₀ : ℚ) ^ τ) * (c (Module.finrank (pullField y L) Ω)).coeff m).num, ?_⟩
    rw [coeff_smul, smul_eq_mul, eq_intCast]
    exact Rat.coe_int_num_of_den_eq_one (hcoef m)
  obtain ⟨F, hF'⟩ := hmem
  exact ⟨F, hF'⟩

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseGramMono
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory
open GroundTheory.Heights₂.Heights.SectionsLatticeFS.L2MonomialOrthogonality

noncomputable section

namespace VeroneseGramMono

variable {D : ℕ}

theorem sum_wt_mul (a : Fin (D + 1) → ℝ) :
    ∑ q : Ix (Veronese.Idx D), Veronese.wt q * (a q.2.1.1 * a q.2.1.2) = (∑ i, a i) ^ 2 := by
  classical
  have hs : ∀ g : Fin (D + 1) × Fin (D + 1) → ℝ,
      ∑ q : Ix (Veronese.Idx D), g q.2.1 = ∑ p, if p.1 ≤ p.2 then g p else 0 := by
    intro g
    rw [Fintype.sum_sigma, Fintype.sum_unique, ← Finset.sum_filter]
    exact (Finset.sum_subtype _ (fun p => by simp) g).symm
  have hw : ∀ q : Ix (Veronese.Idx D), Veronese.wt q = if q.2.1.1 = q.2.1.2 then 1 else 2 := fun q => rfl
  simp only [hw]
  rw [hs (fun p => (if p.1 = p.2 then 1 else 2) * (a p.1 * a p.2)), sq, Finset.sum_mul_sum,
    ← Fintype.sum_prod_type']
  have hswap : ∑ p : Fin (D + 1) × Fin (D + 1), (if p.2 < p.1 then a p.1 * a p.2 else 0) =
      ∑ p : Fin (D + 1) × Fin (D + 1), (if p.1 < p.2 then a p.1 * a p.2 else 0) := by
    rw [← (Equiv.prodComm _ _).sum_comp]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap, mul_comm]
  have hsplit : ∑ p : Fin (D + 1) × Fin (D + 1), a p.1 * a p.2 =
      ∑ p : Fin (D + 1) × Fin (D + 1), ((if p.1 ≤ p.2 then a p.1 * a p.2 else 0) +
        (if p.2 < p.1 then a p.1 * a p.2 else 0)) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rcases le_or_gt p.1 p.2 with h | h
    · simp [h, not_lt.mpr h]
    · simp [h, not_le.mpr h]
  rw [hsplit, Finset.sum_add_distrib, hswap, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rcases lt_trichotomy p.1 p.2 with h | h | h
  · simp [h.le, h.ne, h]
    ring
  · simp [h]
  · simp [not_le.mpr h, not_lt.mpr h.le]

theorem rho_map (w : Fin (D + 1) → ℂ) :
    (Veronese.metric D).ρ (Veronese.map D w) = normSq2 w := by
  change ‖WithLp.toLp 2 (Veronese.scale D (Veronese.map D w))‖ = _
  rw [EuclideanSpace.norm_eq]
  have h : ∀ q : Ix (Veronese.Idx D), ‖Veronese.scale D (Veronese.map D w) q‖ ^ 2 =
      Veronese.wt q * (‖w q.2.1.1‖ ^ 2 * ‖w q.2.1.2‖ ^ 2) := fun q => by
    simp only [Veronese.scale, Veronese.map, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (Veronese.wt_pos q).le]
  simp only [h]
  rw [sum_wt_mul (fun i => ‖w i‖ ^ 2)]
  exact Real.sqrt_sq (normSq2_nonneg w)

theorem rho_conj_map (w : Fin (D + 1) → ℂ) :
    (Veronese.metric D).ρ (conjPt (Veronese.map D w)) = normSq2 w := by
  have h : conjPt (Veronese.map D w) = Veronese.map D (fun i => starRingEnd ℂ (w i)) := by
    funext q
    simp [conjPt, Veronese.map, map_mul]
  rw [h, rho_map]
  simp [normSq2]

theorem conjPt_map (w : Fin (D + 1) → ℂ) :
    conjPt (Veronese.map D w) = Veronese.map D (fun i => starRingEnd ℂ (w i)) := by
  funext q
  simp [conjPt, Veronese.map, map_mul]

def phi (D : ℕ) : MvPolynomial (Ix (Veronese.Idx D)) ℚ →ₐ[ℚ] MvPolynomial (Fin (D + 1)) ℚ :=
  bind₁ fun q => X q.2.1.1 * X q.2.1.2

theorem aeval_alt (f : MvPolynomial (Ix (Veronese.Idx D)) ℚ) :
    aeval (Veronese.x D) f = algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D) (phi D f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, phi, bind₁_C_right]
    exact congrArg (fun g : ℚ →+* Veronese.Fld D => g a)
      (Subsingleton.elim _ ((algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D)).comp C))
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
  | mul_X p q hp =>
    rw [map_mul, map_mul, map_mul, hp, aeval_X]
    simp [phi, Veronese.x, Veronese.t]

theorem phi_eq {N : ℕ} (b : MvPolynomial (Ix (Veronese.Idx D)) ℚ)
    (c : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card → ℤ)
    (h : aeval (Veronese.x D) b = ∑ l, (c l : Veronese.Fld D) * ∏ i, Veronese.t D i ^ adtEnum D N l i) :
    phi D b = ∑ l, (c l : MvPolynomial (Fin (D + 1)) ℚ) * ∏ i, X i ^ adtEnum D N l i := by
  apply IsFractionRing.injective (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D)
  rw [← aeval_alt, h]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_mul, map_prod, map_pow, Veronese.t]

theorem eval_map_phi (w : Fin (D + 1) → ℂ) (f : MvPolynomial (Ix (Veronese.Idx D)) ℚ) :
    eval (Veronese.map D w) (MvPolynomial.map (algebraMap ℚ ℂ) f) = aeval w (phi D f) := by
  rw [phi, aeval_bind₁, eval_map, aeval_def]
  congr 1
  funext q
  simp [Veronese.map]

theorem eval_b {N : ℕ} (w : Fin (D + 1) → ℂ) (b : MvPolynomial (Ix (Veronese.Idx D)) ℚ)
    (c : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card → ℤ)
    (h : aeval (Veronese.x D) b = ∑ l, (c l : Veronese.Fld D) * ∏ i, Veronese.t D i ^ adtEnum D N l i) :
    eval (Veronese.map D w) (MvPolynomial.map (algebraMap ℚ ℂ) b) =
      ∑ l, (c l : ℂ) * ∏ i, w i ^ adtEnum D N l i := by
  rw [eval_map_phi, phi_eq b c h]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_mul, map_prod, map_pow]

theorem eval_conj_b {N : ℕ} (w : Fin (D + 1) → ℂ) (b : MvPolynomial (Ix (Veronese.Idx D)) ℚ)
    (c : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card → ℤ)
    (h : aeval (Veronese.x D) b = ∑ l, (c l : Veronese.Fld D) * ∏ i, Veronese.t D i ^ adtEnum D N l i) :
    eval (conjPt (Veronese.map D w)) (MvPolynomial.map (algebraMap ℚ ℂ) b) =
      starRingEnd ℂ (∑ l, (c l : ℂ) * ∏ i, w i ^ adtEnum D N l i) := by
  rw [conjPt_map, eval_b _ b c h]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, map_mul, map_prod, map_pow]

def ex (D N : ℕ) (l : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card) : Fin (D + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (adtEnum D N l)

theorem ex_degree {N : ℕ} (l : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card) : (ex D N l).degree = N := by
  rw [Finsupp.degree_eq_sum]
  simpa [ex] using adtEnum_sum D N l

theorem eval_ex {N : ℕ} (l : Fin (Finset.Nat.antidiagonalTuple (D + 1) N).card) (w : Fin (D + 1) → ℂ) :
    eval w (monomial (ex D N l) (1 : ℂ)) = ∏ i, w i ^ adtEnum D N l i := by
  rw [eval_monomial, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  simp [ex]

theorem veroneseMetric_pow_eq (w : Fin (D + 1) → ℂ) (n : ℕ) :
    (Veronese.metric D).ρ (Veronese.map D w) ^ (2 * n) = norm2 w ^ (2 * (2 * n)) := by
  rw [rho_map, pow_mul (norm2 w), norm2, Real.sq_sqrt (normSq2_nonneg w)]

theorem veroneseMetric_conj_pow_eq (w : Fin (D + 1) → ℂ) (n : ℕ) :
    (Veronese.metric D).ρ (conjPt (Veronese.map D w)) ^ (2 * n) = norm2 w ^ (2 * (2 * n)) := by
  rw [rho_conj_map, pow_mul (norm2 w), norm2, Real.sq_sqrt (normSq2_nonneg w)]

variable {n r : ℕ} (b : Fin r → MvPolynomial (Ix (Veronese.Idx D)) ℚ)
  (A : Matrix (Fin r) (Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card) ℤ)
  (hA : ∀ k, aeval (Veronese.x D) (b k) =
    ∑ l, (A k l : Veronese.Fld D) * ∏ i, Veronese.t D i ^ adtEnum D (2 * n) l i)
include hA

theorem pairVal_map (k l : Fin r) (w : Fin (D + 1) → ℂ) :
    pairVal (Veronese.metric D) n (b k) (b l) (Veronese.map D w) =
      ∑ i, ∑ j, ((A k i : ℂ) * (A l j : ℂ)) * monoInner (2 * n) (ex D (2 * n) j) (ex D (2 * n) i) w := by
  unfold pairVal
  rw [veroneseMetric_pow_eq, eval_b w (b k) _ (hA k), eval_b w (b l) _ (hA l)]
  simp only [monoInner, eval_ex]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, map_intCast]
  ring

theorem pairVal_conj_map (k l : Fin r) (w : Fin (D + 1) → ℂ) :
    pairVal (Veronese.metric D) n (b k) (b l) (conjPt (Veronese.map D w)) =
      ∑ i, ∑ j, ((A k i : ℂ) * (A l j : ℂ)) * monoInner (2 * n) (ex D (2 * n) i) (ex D (2 * n) j) w := by
  unfold pairVal
  rw [veroneseMetric_conj_pow_eq, eval_conj_b w (b k) _ (hA k), eval_conj_b w (b l) _ (hA l), Complex.conj_conj]
  simp only [monoInner, eval_ex]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, map_intCast, map_prod, map_pow]
  ring

omit hA in
theorem integrable_monoInner_ex (i j : Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card) :
    Integrable (fun p : CP D => monoInner (2 * n) (ex D (2 * n) i) (ex D (2 * n) j) p.rep) (CP.fsMeasure D) :=
  (continuous_monoInner_rep (ex_degree i) (ex_degree j)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)


omit hA in
theorem integral_monoInner_ex (i j : Fin (Finset.Nat.antidiagonalTuple (D + 1) (2 * n)).card) :
    ∫ p : CP D, monoInner (2 * n) (ex D (2 * n) i) (ex D (2 * n) j) p.rep ∂CP.fsMeasure D =
      if i = j then ((monoNormSq (adtEnum D (2 * n) i) : ℝ) : ℂ) else 0 := by
  split_ifs with h
  · subst h
    have e := integral_monoInner_self (N := D) (ex D (2 * n) i)
    rw [ex_degree] at e
    rw [e, monoNormSq, adtEnum_sum]
    push_cast
    simp [ex]
  · have hne : ex D (2 * n) i ≠ ex D (2 * n) j := fun e =>
      h (adtEnum_injective D _ (by simpa [ex] using e))
    have e := integral_monoInner_eq_zero hne ((ex_degree j).trans (ex_degree i).symm)
    rwa [ex_degree] at e

theorem integral_pairVal (k l : Fin r) :
    ∫ p : CP D, pairVal (Veronese.metric D) n (b k) (b l) (Veronese.map D p.rep) ∂CP.fsMeasure D =
      ((∑ i, (A k i : ℝ) * monoNormSq (adtEnum D (2 * n) i) * (A l i : ℝ) : ℝ) : ℂ) := by
  have hi : ∀ i j, Integrable (fun p : CP D => ((A k i : ℂ) * (A l j : ℂ)) *
      monoInner (2 * n) (ex D (2 * n) j) (ex D (2 * n) i) p.rep) (CP.fsMeasure D) := fun i j =>
    (integrable_monoInner_ex j i).const_mul _
  simp_rw [pairVal_map b A hA k l]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hi i j]
  simp only [integral_const_mul, integral_monoInner_ex, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  push_cast
  ring

theorem integral_pairVal_conj (k l : Fin r) :
    ∫ p : CP D, pairVal (Veronese.metric D) n (b k) (b l) (conjPt (Veronese.map D p.rep)) ∂CP.fsMeasure D =
      ((∑ i, (A k i : ℝ) * monoNormSq (adtEnum D (2 * n) i) * (A l i : ℝ) : ℝ) : ℂ) := by
  have hi : ∀ i j, Integrable (fun p : CP D => ((A k i : ℂ) * (A l j : ℂ)) *
      monoInner (2 * n) (ex D (2 * n) i) (ex D (2 * n) j) p.rep) (CP.fsMeasure D) := fun i j =>
    (integrable_monoInner_ex i j).const_mul _
  simp_rw [pairVal_conj_map b A hA k l]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hi i j, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hi i j]
  simp only [integral_const_mul, integral_monoInner_ex, mul_ite, mul_zero, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
  push_cast
  ring

end VeroneseGramMono

theorem VeroneseGramMono.proof : VeroneseGramMono.Statement := by
  intro D n r b A hA
  ext k l
  change (1 / 2) * ((∫ p : CP D, pairVal (Veronese.metric D) n (b k) (b l) (Veronese.map D p.rep)
      ∂CP.fsMeasure D).re + (∫ p : CP D, pairVal (Veronese.metric D) n (b k) (b l)
        (conjPt (Veronese.map D p.rep)) ∂CP.fsMeasure D).re) = _
  rw [VeroneseGramMono.integral_pairVal b A hA, VeroneseGramMono.integral_pairVal_conj b A hA,
    Complex.ofReal_re]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.map_apply]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCurveSmallCountLower
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace CurveSmallCountLower

theorem statement_iff : CurveSmallCountLower.Statement ↔ Targets.CurveCountLower.Statement :=
  Iff.rfl

end CurveSmallCountLower

theorem CurveSmallCountLower.proof (hD : Targets.CurveDegreeVert.Statement) (hV : Targets.CurveVertIndex.Statement)
    (hL : Targets.CurveIndexLinear.Statement) (hN : Targets.CurveBoxCount.Statement) :
    CurveSmallCountLower.Statement :=
  CurveSmallCountLower.statement_iff.mpr (Targets.CurveCountLower.proof hD hV hL hN)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameFibreDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

theorem ProjFrameFibreDeg.proof (hPt : ProjFrameFibrePt.Statement) (hRel : ProjFrameGenPtRel.Statement)
    (hTr : ProjFrameGenPtTransc.Statement) (hDeg : TranscRatioDeg.Statement) (hRat : RatioFieldDeg.Statement) :
    ProjFrameFibreDeg.Statement := by
  intro D Ω _ _ κ _ x e hP hF G i hi
  obtain ⟨hc, hcoord, hrel, hrange⟩ := hRel D Ω κ x e hP hF G
  have : CharZero G.Φ' := charZero_of_inj_zero hc

  have hz : ∀ k, G.x' ⟨k.1, i k⟩ ≠ 0 := fun k h => hi k (by
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]; exact h)
  have hch := Inter.ChartRankAdjoin.proof (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) Sum.inr) G.Φ G.Φ' (fun q => G.x' ⟨q.1.1, q.2⟩) i hz
    (hPt D Ω κ x e hP hF G).1.2.1
  let k₀ : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit) := ⟨Sum.inl (), fun ⟨_, h⟩ => Sum.inr_ne_inl h⟩
  let u : Ix κ → G.Φ' := fun p => G.x' ⟨Sum.inl p.1, p.2⟩
  have hset : (Set.range fun q : (Σ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit),
      fibreIdx (Sum.elim (GlobalTheory κ) (GlobalTheory (Fin (D + 1)))) Sum.inr k) =>
        G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, i q.1⟩) = Set.range fun p : Ix κ => u p / u ⟨(), i k₀⟩ := by
    ext c
    constructor
    · rintro ⟨⟨⟨(t | t), h⟩, j⟩, rfl⟩
      · exact ⟨⟨(), j⟩, rfl⟩
      · exact absurd ⟨t, rfl⟩ h
    · rintro ⟨⟨_, j⟩, rfl⟩
      exact ⟨⟨k₀, j⟩, rfl⟩
  change ptDeg (RingHom.ker _) i = _
  rw [hch, hset]
  rw [hDeg (Ix κ) G.Φ' u D e (fun k => G.x' ⟨Sum.inr (), k⟩) ⟨(), i k₀⟩ G.Φ (hz k₀)
    (fun k => ProjFrameGraph.genFibre_x'_ne_zero G (e k).2 (ProjFrameGraph.frame_ne_zero hF k)) hrel
    (hTr D Ω κ x e hP hF G) hrange]
  exact hRat (Ix κ) G.Φ' Ω u x D e hcoord

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PProjFrameGenPtTransc
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace ProjFrameGenPtTransc

open ProjFrameFibrePt

theorem proof : ProjFrameGenPtTransc.Statement := by
  intro D Ω _ _ κ _ x e _hA hF G
  classical
  have := coordIdeal_isPrime ℤ x
  rw [transcendental_iff]
  intro q hq
  have hc : ∀ n, ∃ g : MvPolynomial (Ix κ) ℤ,
      aeval (fun p : Ix κ => G.x' (aV D p.2)) g = ((q.coeff n : _) : G.Φ') := by
    intro n
    have h : ((q.coeff n : _) : G.Φ') ∈
        (aeval (fun p : Ix κ => G.x' ⟨Sum.inl p.1, p.2⟩) : MvPolynomial (Ix κ) ℤ →ₐ[ℤ] G.Φ').range := by
      rw [← Algebra.adjoin_range_eq_range_aeval]
      exact (q.coeff n).2
    obtain ⟨g, hg⟩ := h
    exact ⟨g, hg⟩
  choose g hg using hc
  have hFΓ : (∑ n ∈ q.support, rename (fun p : Ix κ => aV D p.2) (g n) * X (bV κ 0) ^ n) ∈ graphP x e := by
    have key : ∀ F, aeval G.x' F = 0 → F ∈ graphP x e := fun F h => by
      rw [graphP, ← G.genericFibre_ker_target, RingHom.mem_ker]; exact h
    refine key _ ?_
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def] at hq
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hq, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_mul, map_pow, aeval_X, aeval_rename]
    exact congrArg (· * _) (hg n)
  replace hFΓ : graphMap (coordIdeal ℤ x) (ReciprocityTheory.ChartRestriction.G.AI.I4.linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e))
      (∑ n ∈ q.support, rename (fun p : Ix κ => aV D p.2) (g n) * X (bV κ 0) ^ n) = 0 := hFΓ
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum] at hFΓ
  simp only [map_mul, map_pow, graphMap_rename_inl, graphMap_inr, ProjFrameGraph.linForm_projMat] at hFΓ
  simp only [mul_pow, ← mul_assoc, ← C_pow, ← C_mul] at hFΓ
  have hX : Ideal.Quotient.mk (coordIdeal ℤ x) (X (e 0)) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem, X_mem_coordIdeal_iff]
    exact ProjFrameGraph.frame_ne_zero hF 0
  have hcoef : ∀ m, q.coeff m = 0 := by
    intro m
    by_cases hm : m ∈ q.support
    · have h1 := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single () m)) hFΓ
      rw [coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, Finset.sum_eq_single m] at h1
      · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one] at h1
        have h2 := (mul_eq_zero.1 h1).resolve_right (pow_ne_zero _ hX)
        rw [Ideal.Quotient.eq_zero_iff_mem] at h2
        have h3 := aeval_inl_eq_zero G h2
        rw [hg m] at h3
        exact Subtype.ext h3
      · intro n _ hn
        rw [coeff_C_mul, coeff_X_pow, if_neg, mul_zero]
        intro h
        exact hn (Finsupp.single_injective () h)
      · intro h
        exact absurd hm h
    · exact Polynomial.notMem_support_iff.1 hm
  apply AddMonoidAlgebra.ext
  ext m
  simpa using congrArg Subtype.val (hcoef m)

end ProjFrameGenPtTransc

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
