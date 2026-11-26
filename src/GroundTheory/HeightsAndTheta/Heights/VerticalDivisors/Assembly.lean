module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.AssemblyPartial
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGenSecDomain
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormIrreducible
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecBTorsionFree
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsFreeParAlgIndep
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncidenceZeroLocus

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowSecDvd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

theorem ChowSecDvd.proof (h₁ : IncidenceNull.Statement) : ChowSecDvd.Statement := by
  intro k E _ _ _ n e Q g y _ hg
  set QE := Q.map (MvPolynomial.map (algebraMap k E)) with hQE
  set I := secIdeal QE y with hI
  set ι : E →+* SecAlg QE y := algebraMap E (SecAlg QE y) with hι
  set x : Fin n → SecAlg QE y := secCoord QE y with hx
  have hmk : ∀ p : MvPolynomial (Fin n) E, Ideal.Quotient.mk I p = eval₂ ι x p := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => rw [eval₂_C, hι]; rfl
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => rw [map_mul, hp, eval₂_mul, eval₂_X]; rfl
  have hlin : ∀ u : Fin n → E, ∑ j, ι (u j) * x j = Ideal.Quotient.mk I (linForm u) := by
    intro u
    simp [hmk, linForm, eval₂_sum, mul_comm]
  have hchart : ∑ j, ι (y (.inr j)) * x j = 1 := by
    rw [hlin, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  have hform : ∀ i, ∑ j, ι (y (.inl (i, j))) * x j = 0 := by
    intro i
    rw [hlin, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
  set θ : MvPolynomial (Fin n) (SecAlg QE y) := ∑ j, X j * C (x j) with hθ
  set c : k →+* MvPolynomial (Fin n) (SecAlg QE y) := (C : SecAlg QE y →+* _).comp (ι.comp (algebraMap k E))
    with hc
  let vφ : Fin n ⊕ (Fin (e + 1) × Fin n) → MvPolynomial (Fin n) (SecAlg QE y) :=
    Sum.elim (fun j => C (x j)) fun ij => Fin.cases (motive := fun _ => MvPolynomial (Fin n) (SecAlg QE y))
      (X ij.2 - θ * C (ι (y (.inr ij.2)))) (fun i => C (ι (y (.inl (i, ij.2))))) ij.1
  let vψ : Fin n ⊕ (Fin (e + 1) × Fin n) → MvPolynomial (Fin n) (SecAlg QE y) :=
    Sum.elim (fun j => C (x j)) fun ij => Fin.cases (motive := fun _ => MvPolynomial (Fin n) (SecAlg QE y))
      (X ij.2) (fun i => C (ι (y (.inl (i, ij.2))))) ij.1
  set φ := eval₂Hom c vφ with hφ
  set ψ := eval₂Hom c vψ with hψ

  have hker : incIdeal Q (e + 1) ≤ RingHom.ker φ := by
    refine sup_le ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro q hq
      rw [Ideal.mem_comap, RingHom.mem_ker, hφ, coe_eval₂Hom, eval₂_rename]
      have h : eval₂ c (vφ ∘ Sum.inl) q = C (Ideal.Quotient.mk I (q.map (algebraMap k E))) := by
        rw [hmk, eval₂_map, eval₂_comp_left]
        rfl
      rw [h, Ideal.Quotient.eq_zero_iff_mem.mpr, map_zero]
      exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hq))
    · rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [SetLike.mem_coe, RingHom.mem_ker, map_sum]
      simp only [map_mul, hφ, eval₂Hom_X', vφ, Sum.elim_inl, Sum.elim_inr]
      refine Fin.cases ?_ (fun i => ?_) i
      · show ∑ j, (X j - θ * C (ι (y (.inr j)))) * C (x j) = 0
        have h : ∑ j, (X j - θ * C (ι (y (.inr j)))) * C (x j) =
            θ - θ * C (∑ j, ι (y (.inr j)) * x j) := by
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [map_sum, map_mul, Finset.mul_sum]
          rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
          conv_rhs => rw [hθ]
          exact Finset.sum_congr rfl fun j _ => by ring
        rw [h, hchart, map_one, mul_one, sub_self]
      set_option synthInstance.maxHeartbeats 100000 in
        · simp only [Fin.cases_succ, ← map_mul, ← map_sum, hform, map_zero]
  obtain ⟨M, hM⟩ := h₁ k n (e + 1) Q g hg
  set G := φ (rename Sum.inr g) with hG
  have hGx : ∀ j, G ^ M * C (x j) ^ M = 0 := by
    intro j
    have := hker (hM j)
    rw [RingHom.mem_ker, map_pow, map_mul, hφ, eval₂Hom_X'] at this
    rw [← mul_pow]
    exact this
  have hG0 : G ^ M = 0 := by
    have h1 : Ideal.span (Set.range fun j => (C (x j) : MvPolynomial (Fin n) (SecAlg QE y))) = ⊤ := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Ideal.eq_top_iff_one, ← map_one C, ← hchart, map_sum]
      exact sum_mem fun j _ => by
        rw [map_mul]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)
    have h2 := Ideal.span_pow_eq_top _ h1 M
    have h3 : (1 : MvPolynomial (Fin n) (SecAlg QE y)) ∈
        Ideal.span ((fun z => z ^ M) '' Set.range fun j => C (x j)) := by
      rw [h2]; exact Submodule.mem_top
    have key : ∀ z ∈ Ideal.span ((fun z => z ^ M) '' Set.range fun j =>
        (C (x j) : MvPolynomial (Fin n) (SecAlg QE y))), G ^ M * z = 0 := by
      intro z hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨_, ⟨j, rfl⟩, rfl⟩ := hz
        exact hGx j
      | zero => exact mul_zero _
      | add a b _ _ ha hb => rw [mul_add, ha, hb, add_zero]
      | smul a b _ hb => rw [smul_eq_mul, mul_left_comm, hb, mul_zero]
    simpa using key 1 h3

  set π := Ideal.Quotient.mk (Ideal.span {θ}) with hπ
  have hπθ : π θ = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self θ)
  have hcomp : π.comp φ = π.comp ψ := by
    apply MvPolynomial.ringHom_ext
    · intro a; simp [hφ, hψ]
    · intro v
      rcases v with j | ⟨i, j⟩
      · simp [hφ, hψ, vφ, vψ]
      · refine Fin.cases ?_ (fun i => ?_) i
        · set_option synthInstance.maxHeartbeats 100000 in
            simp [hφ, hψ, vφ, vψ, hπθ]
        · simp [hφ, hψ, vφ, vψ]
  have hspec : ψ (rename Sum.inr g) =
      (specRest (algebraMap k E) g y).map (algebraMap E (SecAlg QE y)) := by
    rw [hψ, coe_eval₂Hom, eval₂_rename]
    unfold specRest
    rw [eval₂_comp_left]
    congr 1
    · exact RingHom.ext fun a => by simp [hc, hι]
    · funext ij
      obtain ⟨i, j⟩ := ij
      refine Fin.cases ?_ (fun i => ?_) i <;> simp [vψ, hι]
  refine ⟨M + 1, M.succ_pos, ?_⟩
  have hz : π (ψ (rename Sum.inr g) ^ (M + 1)) = 0 := by
    rw [map_pow, ← RingHom.comp_apply, ← hcomp, RingHom.comp_apply, pow_succ, ← map_pow, ← hG, hG0,
      map_zero, zero_mul]
  rw [← hspec, ← Ideal.mem_span_singleton]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hz

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGaussDVR
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain WithZero

noncomputable section

section Dedekind

variable {A : Type*} [CommRing A] [IsDedekindDomain A] (v : HeightOneSpectrum A)

theorem exists_C_mul_eq_C_pow_mul {a : A} (ha : v.intValuation a = exp (-1 : ℤ)) {σ : Type*}
    (j : ℕ) {p : MvPolynomial σ A} (hp : p ∈ Ideal.map (C : A →+* MvPolynomial σ A) (v.asIdeal ^ j)) :
    ∃ t ∉ v.asIdeal, ∃ h : MvPolynomial σ A, C t * p = C a ^ j * h := by
  have hlt : v.intValuation a < 1 := by
    rw [ha, ← exp_zero, exp_lt_exp]
    norm_num
  obtain ⟨J, hJ⟩ := (v.intValuation_lt_one_iff_dvd a).mp hlt
  have hJv : ¬ J ≤ v.asIdeal := by
    intro hle
    obtain ⟨J', hJ'⟩ := Ideal.dvd_iff_le.mpr hle
    have h2 : v.asIdeal ^ 2 ∣ Ideal.span {a} := ⟨J', by rw [hJ, hJ', sq, mul_assoc]⟩
    have h3 := (v.intValuation_le_pow_iff_dvd a 2).mpr h2
    rw [ha, exp_le_exp] at h3
    norm_num at h3
  have hJj : ¬ J ^ j ≤ v.asIdeal := fun h => hJv (Ideal.IsPrime.le_of_pow_le h)
  obtain ⟨t, htJ, htv⟩ := SetLike.not_le_iff_exists.mp hJj
  have hid : J ^ j * v.asIdeal ^ j = Ideal.span {a ^ j} := by
    rw [← mul_pow, mul_comm, ← hJ, Ideal.span_singleton_pow]
  have hmem : C t * p ∈ Ideal.span {(C a ^ j : MvPolynomial σ A)} := by
    have h1 : C t * p ∈ Ideal.map (C : A →+* MvPolynomial σ A) (J ^ j) *
        Ideal.map (C : A →+* MvPolynomial σ A) (v.asIdeal ^ j) :=
      Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ htJ) hp
    rw [← Ideal.map_mul, hid, Ideal.map_span, Set.image_singleton, map_pow] at h1
    exact h1
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.mp hmem
  exact ⟨t, htv, h, by rw [← hh, mul_comm]⟩

end Dedekind

section NumberField

variable {K : Type*} [Field K] [NumberField K]

theorem gaussNorm_map_of_coeff_notMem (v : HeightOneSpectrum (𝓞 K)) {σ : Type*}
    (g : MvPolynomial σ (𝓞 K)) (hg : ∃ m, g.coeff m ∉ v.asIdeal) :
    gaussNorm v (g.map (algebraMap (𝓞 K) K)) = 1 := by
  obtain ⟨m, hm⟩ := hg
  apply le_antisymm
  · refine gaussNormOf_le _ zero_le_one fun d => ?_
    rw [coeff_map, ← FinitePlace.norm_embedding]
    exact FinitePlace.norm_le_one K (v := v) (g.coeff d)
  · have h1 := le_gaussNormOf (NumberField.HeightOneSpectrum.adicAbv K v)
      (g.map (algebraMap (𝓞 K) K)) m
    rw [coeff_map, ← FinitePlace.norm_embedding,
      (FinitePlace.norm_eq_one_iff_notMem K (v := v) _).mpr hm] at h1
    exact h1

theorem adicAbv_of_intValuation_eq (v : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K}
    (ha : v.intValuation a = exp (-1 : ℤ)) :
    NumberField.HeightOneSpectrum.adicAbv K v (algebraMap (𝓞 K) K a) =
      (Ideal.absNorm v.asIdeal : ℝ)⁻¹ := by
  rw [NumberField.HeightOneSpectrum.adicAbv_def, HeightOneSpectrum.valuation_of_algebraMap, ha,
    WithZeroMulInt.toNNReal_neg_apply _ exp_ne_zero]
  rw [WithZero.log_exp, zpow_neg_one, NNReal.coe_inv, NNReal.coe_natCast]

theorem irreducible_algebraMap_C (e n : ℕ) (v : HeightOneSpectrum (𝓞 K))
    [IsDiscreteValuationRing (ParDVR e n v)] {a : 𝓞 K} (ha : v.intValuation a = exp (-1 : ℤ)) :
    Irreducible (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (C a)) := by
  set φ := algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) with hφ
  have hav : a ∈ v.asIdeal := (v.intValuation_lt_one_iff_mem a).mp (by
    rw [ha, ← exp_zero, exp_lt_exp]
    norm_num)
  have hnu : ¬ IsUnit (φ (C a)) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]
    exact fun h => h (Ideal.mem_map_of_mem _ hav)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (ParDVR e n v)
  obtain ⟨x, s, rfl⟩ : ∃ (x : MvPolynomial (Par e n) (𝓞 K)) (s : (parPrime e n v).primeCompl),
      IsLocalization.mk' (ParDVR e n v) x s = ϖ := by
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.mk'_surjective (parPrime e n v).primeCompl ϖ
    exact ⟨x, s, hxs⟩
  have hx : x ∈ Ideal.map (C : 𝓞 K →+* MvPolynomial (Par e n) (𝓞 K)) (v.asIdeal ^ 1) := by
    rw [pow_one]
    by_contra hx
    exact hϖ.not_isUnit
      ((IsLocalization.AtPrime.isUnit_mk'_iff (ParDVR e n v) (parPrime e n v) x s).mpr hx)
  obtain ⟨t, ht, h, hth⟩ := exists_C_mul_eq_C_pow_mul v ha 1 hx
  have htu : IsUnit (φ (C t)) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]
    intro htP
    exact ht (by simpa using (MvPolynomial.mem_map_C_iff (I := v.asIdeal)).mp htP 0)
  have hx2 : φ x = φ (C a) * (↑htu.unit⁻¹ * φ h) := by
    have h2 := congrArg φ hth
    rw [map_mul, map_mul, pow_one] at h2
    calc φ x = ↑htu.unit⁻¹ * (φ (C t) * φ x) := by
          rw [← mul_assoc, IsUnit.val_inv_mul, one_mul]
      _ = φ (C a) * (↑htu.unit⁻¹ * φ h) := by rw [h2]; ring
  have hϖ' : IsLocalization.mk' (ParDVR e n v) x s =
      φ (C a) * (↑htu.unit⁻¹ * φ h * IsLocalization.mk' (ParDVR e n v) 1 s) := by
    rw [IsLocalization.mk'_eq_mul_mk'_one, hx2]
    ring
  rw [hϖ'] at hϖ
  rcases hϖ.isUnit_or_isUnit rfl with hu | hu
  · exact (hnu hu).elim
  · exact (irreducible_mul_isUnit hu).mp hϖ

end NumberField

theorem GaussDVR.proof (h1 : ParDVRIsDVR.Statement) : GaussDVR.Statement := by
  intro K _ _ e n v g hg
  have := h1 K e n v
  classical
  obtain ⟨a, ha⟩ := v.intValuation_exists_uniformizer
  set φ := algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) with hφ
  have hav : a ∈ v.asIdeal := (v.intValuation_lt_one_iff_mem a).mp (by
    rw [ha, ← exp_zero, exp_lt_exp]
    norm_num)
  let μ : 𝓞 K → ℕ := fun b => multiplicity v.asIdeal (Ideal.span {b})
  have hval : ∀ b : 𝓞 K, b ≠ 0 → ∀ k : ℕ, b ∈ v.asIdeal ^ k ↔ k ≤ μ b := by
    intro b hb k
    rw [← v.intValuation_le_pow_iff_mem, v.intValuation_eq_exp_neg_multiplicity hb, exp_le_exp]
    simp only [μ]
    omega
  have hne : g.support.Nonempty := Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp hg)
  obtain ⟨d0, hd0, hmin⟩ := g.support.exists_mem_eq_inf' hne (fun d => μ (g.coeff d))
  set m := g.support.inf' hne (fun d => μ (g.coeff d)) with hm
  have hgm : g ∈ Ideal.map (C : 𝓞 K →+* MvPolynomial (Par e n) (𝓞 K)) (v.asIdeal ^ m) := by
    rw [MvPolynomial.mem_map_C_iff]
    intro d
    by_cases hd : g.coeff d = 0
    · rw [hd]
      exact Ideal.zero_mem _
    · exact (hval _ hd m).mpr (Finset.inf'_le _ (mem_support_iff.mpr hd))
  obtain ⟨t, ht, h, hth⟩ := exists_C_mul_eq_C_pow_mul v ha m hgm
  have hb0 : g.coeff d0 ≠ 0 := mem_support_iff.mp hd0
  have hh : h.coeff d0 ∉ v.asIdeal := by
    intro hmem
    have hc := congrArg (AddMonoidAlgebra.coeff · d0) hth
    rw [coeff_C_mul, ← C_pow, coeff_C_mul] at hc
    have h3 : t * g.coeff d0 ∈ v.asIdeal ^ (m + 1) := by
      rw [hc, pow_succ]
      exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hav m) hmem
    have h4 := (v.intValuation_le_pow_iff_mem _ _).mpr h3
    rw [map_mul, HeightOneSpectrum.intValuation_eq_one_iff.mpr ht, one_mul, v.intValuation_le_pow_iff_mem,
      hval _ hb0] at h4
    omega
  have htu : IsUnit (φ (C t)) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]
    intro htP
    exact ht (by simpa using (MvPolynomial.mem_map_C_iff (I := v.asIdeal)).mp htP 0)
  have hhu : IsUnit (φ h) := by
    rw [IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v)]
    intro hP
    exact hh ((MvPolynomial.mem_map_C_iff (I := v.asIdeal)).mp hP d0)
  have hord : Ring.ord (ParDVR e n v) (φ g) = m := by
    rw [Ring.ord_eq_addVal]
    have h0 := congrArg φ hth
    rw [map_mul φ, map_mul φ, map_pow φ] at h0
    have h2 := congrArg (IsDiscreteValuationRing.addVal (ParDVR e n v)) h0
    rw [IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_uniformizer (irreducible_algebraMap_C e n v ha),
      IsDiscreteValuationRing.addVal_eq_zero_iff.mpr htu,
      IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hhu] at h2
    simpa using h2
  have hK0 := congrArg (MvPolynomial.map (algebraMap (𝓞 K) K)) hth
  rw [map_mul (MvPolynomial.map (algebraMap (𝓞 K) K)), map_mul (MvPolynomial.map (algebraMap (𝓞 K) K)),
    map_pow (MvPolynomial.map (algebraMap (𝓞 K) K)), MvPolynomial.map_C, MvPolynomial.map_C] at hK0
  have hK := congrArg (gaussNorm v) hK0
  rw [← C_pow, gaussNorm_C_mul, gaussNorm_C_mul, map_pow,
    adicAbv_of_intValuation_eq v ha, gaussNorm_map_of_coeff_notMem v h ⟨d0, hh⟩, ← FinitePlace.norm_embedding,
    (FinitePlace.norm_eq_one_iff_notMem K (v := v) _).mpr ht, one_mul, mul_one] at hK
  have hN : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := by
    exact_mod_cast (NumberField.HeightOneSpectrum.absNorm_ne_zero v)
  rw [hord, ENat.toNat_natCast, hK, inv_pow, inv_mul_cancel₀ (pow_ne_zero _ hN)]

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PVertSpec
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem not_lt_lt_of_mem_minimalPrimes_sup_span {A : Type*} [CommRing A] [IsNoetherianRing A]
    {P Q W : Ideal A} [hP : P.IsPrime] [hQ : Q.IsPrime] [hW : W.IsPrime] {x : A}
    (hmin : W ∈ (P ⊔ Ideal.span {x}).minimalPrimes) (hPQ : P < Q) (hQW : Q < W) : False := by
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hmin
  have hsurj : Function.Surjective (Ideal.Quotient.mk P) := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (Ideal.Quotient.mk P) = P := Ideal.mk_ker
  have prime_map : ∀ J : Ideal A, J.IsPrime → P ≤ J → (J.map (Ideal.Quotient.mk P)).IsPrime :=
    fun J _ hPJ => Ideal.map_isPrime_of_surjective hsurj (hker.trans_le hPJ)
  have strict : ∀ J₁ J₂ : Ideal A, P ≤ J₁ → J₁ < J₂ →
      J₁.map (Ideal.Quotient.mk P) < J₂.map (Ideal.Quotient.mk P) := by
    intro J₁ J₂ h₁ h₁₂
    refine lt_of_le_of_ne (Ideal.map_mono h₁₂.le) fun h => h₁₂.ne ?_
    have := congrArg (Ideal.comap (Ideal.Quotient.mk P)) h
    rwa [Ideal.comap_map_of_surjective' _ hsurj, Ideal.comap_map_of_surjective' _ hsurj, hker,
      sup_eq_left.mpr h₁, sup_eq_left.mpr (h₁.trans h₁₂.le)] at this
  have := prime_map P hP le_rfl
  have := prime_map Q hQ hPQ.le
  have := prime_map W hW (hPQ.le.trans hQW.le)
  have a := Ideal.height_add_one_le_of_lt_of_isPrime (strict P Q le_rfl hPQ)
  have b := Ideal.height_add_one_le_of_lt_of_isPrime (strict Q W hPQ.le hQW)
  have : (2 : ℕ∞) ≤ 1 :=
    calc (2 : ℕ∞) = 0 + 1 + 1 := by norm_num
      _ ≤ (P.map (Ideal.Quotient.mk P)).height + 1 + 1 := by gcongr; exact zero_le
      _ ≤ (Q.map (Ideal.Quotient.mk P)).height + 1 := by gcongr
      _ ≤ (W.map (Ideal.Quotient.mk P)).height := b
      _ ≤ 1 := h1
  exact absurd this (by norm_num)

variable {K : Type*} [Field K] {n : ℕ}

theorem eq_zero_of_C_mem_integralModel {I : Ideal (MvPolynomial (Fin n) K)} (hI : I.IsPrime)
    {c : 𝓞 K} (hc : C c ∈ integralModel I) : c = 0 := by
  by_contra h
  apply hI.ne_top
  simp only [integralModel, Ideal.mem_comap, map_C] at hc
  have hu : IsUnit (C (algebraMap (𝓞 K) K c) : MvPolynomial (Fin n) K) :=
    (isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 K) K)).mpr h)).map C
  exact Ideal.eq_top_of_isUnit_mem _ hc hu

theorem linForm_mem_integralModel {I : Ideal (MvPolynomial (Fin n) K)} {u : Fin n → 𝓞 K}
    (h : linForm u ∈ integralModel I) : linForm (fun j => (u j : K)) ∈ I := by
  simp only [integralModel, Ideal.mem_comap] at h
  convert h using 1
  set_option synthInstance.maxHeartbeats 100000 in
    simp [linForm, map_sum, map_mul, map_C, map_X]

theorem VertSpec.proof : VertSpec.Statement := by
  intro K _ _ n e I f u v hI _ hu
  have : I.IsPrime := hI.isPrime
  have hP : (integralModel I).IsPrime := by unfold integralModel; infer_instance
  have hl : linForm u ∉ integralModel I := fun h => hu (linForm_mem_integralModel h)
  obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hCa : C a ∉ integralModel I := fun h => ha0 (eq_zero_of_C_mem_integralModel hI.isPrime h)
  ext W
  constructor
  · rintro ⟨⟨hWmin, hWrel⟩, hWv⟩
    have : W.IsPrime := Ideal.IsMinimalPrime.isPrime hWmin
    have hvW : Ideal.map C v.asIdeal ≤ W := Ideal.map_le_iff_le_comap.mpr hWv.ge
    refine ⟨⟨⟨⟨inferInstance, sup_le (le_sup_left.trans hWmin.1.2) hvW⟩, fun Q hQ hQW => ?_⟩,
      hWrel⟩, hWmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))⟩
    by_contra hWQ
    have := hQ.1
    have hPQ : integralModel I < Q := lt_of_le_of_ne (le_sup_left.trans hQ.2) fun h =>
      hCa (by rw [h]; exact hQ.2 (Ideal.mem_sup_right (Ideal.mem_map_of_mem C ha)))
    exact not_lt_lt_of_mem_minimalPrimes_sup_span hWmin hPQ
      (lt_of_le_of_ne hQW fun h => hWQ h.ge)
  · rintro ⟨⟨hWmin, hWrel⟩, hlW⟩
    have : W.IsPrime := Ideal.IsMinimalPrime.isPrime hWmin
    have hvW : Ideal.map C v.asIdeal ≤ W := le_sup_right.trans hWmin.1.2
    have hPW : integralModel I ≤ W := le_sup_left.trans hWmin.1.2
    have hcomap : W.comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) = v.asIdeal :=
      (v.isMaximal.eq_of_le (Ideal.IsPrime.comap C).ne_top
        (Ideal.map_le_iff_le_comap.mp hvW)).symm
    have hWa : W ∈ (integralModel I ⊔ Ideal.span {C a}).minimalPrimes := by
      refine ⟨⟨inferInstance, sup_le hPW (Ideal.span_le.mpr
        (Set.singleton_subset_iff.mpr (hvW (Ideal.mem_map_of_mem C ha))))⟩, fun Q hQ hQW => ?_⟩
      have := hQ.1
      have hQv : Q.comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) = v.asIdeal := by
        have hle : Q.comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) ≤ v.asIdeal :=
          hcomap ▸ Ideal.comap_mono hQW
        have hmem : a ∈ Q.comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) :=
          hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
        have hne : Q.comap (C : 𝓞 K →+* MvPolynomial (Fin n) (𝓞 K)) ≠ ⊥ := fun h =>
          ha0 (by rwa [h, Ideal.mem_bot] at hmem)
        exact (Ideal.IsPrime.isMaximal (Ideal.IsPrime.comap C) hne).eq_of_le
          v.isPrime.ne_top hle
      exact hWmin.2 ⟨hQ.1, sup_le (le_sup_left.trans hQ.2)
        (Ideal.map_le_iff_le_comap.mpr hQv.ge)⟩ hQW
    refine ⟨⟨⟨⟨inferInstance, sup_le hPW (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hlW))⟩,
      fun Q hQ hQW => ?_⟩, hWrel⟩, hcomap⟩
    by_contra hWQ
    have := hQ.1
    have hPQ : integralModel I < Q := lt_of_le_of_ne (le_sup_left.trans hQ.2) fun h =>
      hl (by rw [h]; exact hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
    exact not_lt_lt_of_mem_minimalPrimes_sup_span hWa hPQ
      (lt_of_le_of_ne hQW fun h => hWQ h.ge)

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGenericFibreDrop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem GenericFibreDrop.proof : GenericFibreDrop.Statement := by
  intro O _ _ _ F _ _ _ n P P' f hP hP'C hfP hP'
  let A := MvPolynomial (Fin n) O
  let T := MvPolynomial (Fin n) F
  let M : Submonoid A := (nonZeroDivisors O).map (C : O →+* A)
  have hφ : (algebraMap A T) = MvPolynomial.map (algebraMap O F) := rfl
  have : IsLocalization M T := MvPolynomial.isLocalization (nonZeroDivisors O) F
  have hP'p : P'.IsPrime := hP'.1.1
  have hPP' : P ≤ P' := le_sup_left.trans hP'.1.2
  have hfP' : f ∈ P' := hP'.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hdisj' : Disjoint (M : Set A) (P' : Set A) := by
    rw [Set.disjoint_left]
    rintro _ ⟨o, ho, rfl⟩ hmem
    have h1 : o ∈ P'.comap (C : O →+* A) := hmem
    rw [hP'C, Ideal.mem_bot] at h1
    exact nonZeroDivisors.ne_zero ho h1
  have hdisj : Disjoint (M : Set A) (P : Set A) :=
    Set.disjoint_of_subset_right hPP' hdisj'

  let I : Ideal T := P.map (algebraMap A T)
  let I' : Ideal T := P'.map (algebraMap A T)
  have hI : I.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M T P hP hdisj
  have hI' : I'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M T P' hP'p hdisj'
  have hII' : I ≤ I' := Ideal.map_mono hPP'

  let Q : Ideal (A ⧸ P) := P'.map (Ideal.Quotient.mk P)
  have hQ : Q.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hQne : Q ≠ ⊥ := by
    intro h
    have h1 : Ideal.Quotient.mk P f ∈ Q := Ideal.mem_map_of_mem _ hfP'
    rw [h, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at h1
    exact hfP h1
  have hQ1 : Q.height = 1 := by
    refine le_antisymm (Ideal.map_height_le_one_of_mem_minimalPrimes hP') ?_
    have := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.2 hQne)
    simpa using this

  let M' : Submonoid (A ⧸ P) := Algebra.algebraMapSubmonoid (A ⧸ P) M
  have hQdisj : Disjoint (M' : Set (A ⧸ P)) (Q : Set (A ⧸ P)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hmem
    have h1 : Ideal.Quotient.mk P a ∈ Q := hmem
    rw [Ideal.mem_quotient_iff_mem hPP'] at h1
    exact Set.disjoint_left.1 hdisj' ha h1
  have hh := IsLocalization.height_map_of_disjoint (S := T ⧸ I) M' Q hQdisj
  have hmap : Q.map (algebraMap (A ⧸ P) (T ⧸ I)) = I'.map (Ideal.Quotient.mk I) := by
    simp only [Q, I', Ideal.map_map]
    rfl
  rw [hmap, hQ1] at hh
  have _ : (I'.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])

  have key := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (k := F)
    (I'.map (Ideal.Quotient.mk I))
  rw [hh, ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hII')] at key
  show ringKrullDim (T ⧸ I) = ringKrullDim (T ⧸ I') + 1
  rw [← key, add_comm]
  rfl

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PFibreCut
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial IsDedekindDomain

theorem not_lt_of_mem_minimalPrimes_sup_span {R : Type*} [CommRing R] [IsNoetherianRing R]
    {P W Q : Ideal R} {f : R} [P.IsPrime] [W.IsPrime] (hPW : P < W)
    (hQ : Q ∈ (P ⊔ Ideal.span {f}).minimalPrimes) : ¬ W < Q := by
  intro hWQ
  have : Q.IsPrime := hQ.isPrime
  have hPQ : P ≤ Q := le_sup_left.trans hQ.le
  have h1 := Ideal.map_height_le_one_of_mem_minimalPrimes hQ
  have hπ : Function.Surjective (Ideal.Quotient.mk P) := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (Ideal.Quotient.mk P) = P := Ideal.mk_ker
  have hWm : (W.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective hπ (hker.le.trans hPW.le)
  have hQm : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective hπ (hker.le.trans hPQ)
  have hinj : ∀ {I J : Ideal R}, P ≤ I → P ≤ J →
      I.map (Ideal.Quotient.mk P) = J.map (Ideal.Quotient.mk P) → I = J := by
    intro I J hI hJ h
    have := congrArg (Ideal.comap (Ideal.Quotient.mk P)) h
    rwa [Ideal.comap_map_of_surjective' _ hπ, Ideal.comap_map_of_surjective' _ hπ, hker,
      sup_eq_left.mpr hI, sup_eq_left.mpr hJ] at this
  have hlt1 : (⊥ : Ideal (R ⧸ P)) < W.map (Ideal.Quotient.mk P) := by
    refine bot_lt_iff_ne_bot.mpr fun h => hPW.ne ?_
    exact hinj le_rfl hPW.le (by rw [h, Ideal.map_quotient_self])
  have hlt2 : W.map (Ideal.Quotient.mk P) < Q.map (Ideal.Quotient.mk P) :=
    lt_of_le_of_ne (Ideal.map_mono hWQ.le) fun h => hWQ.ne (hinj hPW.le hPQ h)
  have a := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt1
  have b := Ideal.height_strict_mono_of_isPrime_of_isPrime hlt2
  rw [Ideal.height_bot] at a
  have c : (W.map (Ideal.Quotient.mk P)).height < 1 := lt_of_lt_of_le b h1
  rw [Order.lt_one_iff] at c
  rw [c] at a
  exact lt_irrefl _ a

theorem FibreCut.proof (hAvoid : CodimOnePrimeAvoid.Statement) : FibreCut.Statement := by
  intro O _ _ n P W v hP hPC hW hWmax
  classical
  set vX : Ideal (MvPolynomial (Fin n) O) :=
    Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal with hvX
  have hWp : W.IsPrime := hW.isPrime
  have hPW : P ≤ W := le_sup_left.trans hW.le
  have hvW : vX ≤ W := le_sup_right.trans hW.le
  have hfin := (P ⊔ vX).finite_minimalPrimes_of_isNoetherianRing

  obtain ⟨h, hhQ, hhW⟩ : ∃ h, (∀ Q ∈ (P ⊔ vX).minimalPrimes, Q ≠ W → h ∈ Q) ∧ h ∉ W := by
    have hnot : ¬ (hfin.toFinset.erase W).inf id ≤ W := by
      rw [hWp.inf_le']
      rintro ⟨Q, hQs, hQW⟩
      obtain ⟨hQW', hQ⟩ := Finset.mem_erase.mp hQs
      rw [Set.Finite.mem_toFinset] at hQ
      exact hQW' (le_antisymm hQW (hW.2 ⟨hQ.isPrime, hQ.le⟩ hQW))
    obtain ⟨h, hh, hhW⟩ := SetLike.not_le_iff_exists.mp hnot
    exact ⟨h, fun Q hQ hQW => Finset.inf_le (f := id)
      (Finset.mem_erase.mpr ⟨hQW, hfin.mem_toFinset.mpr hQ⟩) hh, hhW⟩

  have hvmax : v.asIdeal.IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hWC : W.comap (C : O →+* MvPolynomial (Fin n) O) = v.asIdeal :=
    (hvmax.eq_of_le (Ideal.comap_ne_top _ hWp.ne_top) (Ideal.map_le_iff_le_comap.mp hvW)).symm
  have : W.LiesOver v.asIdeal := ⟨hWC.symm⟩
  let _ : Field (O ⧸ v.asIdeal) := Ideal.Quotient.field _
  have hBnf : ¬ IsField (MvPolynomial (Fin n) O ⧸ W) :=
    fun hf => hWmax (Ideal.Quotient.maximal_of_isField W hf)
  obtain ⟨I, hIbot, hItop⟩ := Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp hBnf
  have hdim1 : 1 ≤ ringKrullDim (MvPolynomial (Fin n) O ⧸ W) := by
    have : Nontrivial (_ ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop.ne
    have h2 := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le I hIbot.ne'
    have h0 := ringKrullDim_nonneg_of_nontrivial (R := (MvPolynomial (Fin n) O ⧸ W) ⧸ I)
    calc (1 : WithBot ℕ∞) = 0 + 1 := by simp
      _ ≤ ringKrullDim ((MvPolynomial (Fin n) O ⧸ W) ⧸ I) + 1 := add_le_add h0 le_rfl
      _ ≤ _ := h2
  obtain ⟨N₀, hN₀, hhN₀, hdimN₀⟩ := hAvoid (O ⧸ v.asIdeal) (MvPolynomial (Fin n) O ⧸ W)
    (Ideal.Quotient.mk W h) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]) hdim1

  set φ : MvPolynomial (Fin n) O →+* (MvPolynomial (Fin n) O ⧸ W) ⧸ N₀ :=
    (Ideal.Quotient.mk N₀).comp (Ideal.Quotient.mk W) with hφ
  have hφs : Function.Surjective φ :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  set N := RingHom.ker φ with hNdef
  have hNp : N.IsPrime := RingHom.ker_isPrime φ
  have hmemN : ∀ a, a ∈ N ↔ Ideal.Quotient.mk W a ∈ N₀ := fun a => by
    simp [N, φ, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  have hWN : W ≤ N := fun a ha => (hmemN a).mpr (by
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]; exact N₀.zero_mem)
  have hhN : h ∉ N := fun hh => hhN₀ ((hmemN h).mp hh)
  have hdimN : ringKrullDim (MvPolynomial (Fin n) O ⧸ N) + 1 =
      ringKrullDim (MvPolynomial (Fin n) O ⧸ W) := by
    rw [ringKrullDim_eq_of_ringEquiv (RingHom.quotientKerEquivOfSurjective hφs)]
    exact hdimN₀
  have hNW : ¬ N ≤ W := by
    intro hle
    have hN₀bot : N₀ = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact Ideal.mem_bot.mpr (Ideal.Quotient.eq_zero_iff_mem.mpr (hle ((hmemN a).mpr hx)))
    subst hN₀bot
    rw [ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)] at hdimN₀
    obtain ⟨m, hm, -⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg
      (k := O ⧸ v.asIdeal) (A := MvPolynomial (Fin n) O ⧸ W)
    rw [hm] at hdimN₀
    have : ((m + 1 : ℕ) : WithBot ℕ∞) = (m : WithBot ℕ∞) := by push_cast; exact hdimN₀
    have : m + 1 = m := by exact_mod_cast this
    omega

  have hNQ : ∀ Q ∈ (P ⊔ vX).minimalPrimes, ¬ N ≤ Q := fun Q hQ hle =>
    hNW (hle.trans (hQ.2 ⟨hWp, hW.le⟩ (hWN.trans hle)))
  obtain ⟨f, hfN, hfQ⟩ : ∃ f ∈ N, ∀ Q ∈ (P ⊔ vX).minimalPrimes, f ∉ Q := by
    have hns : ¬ ((N : Set (MvPolynomial (Fin n) O)) ⊆
        ⋃ Q ∈ (↑hfin.toFinset : Set (Ideal (MvPolynomial (Fin n) O))), ((id Q : Ideal _) : Set _)) := by
      rw [Ideal.subset_union_prime (f := id) ⊥ ⊥
        (fun Q hQ _ _ => (hfin.mem_toFinset.mp hQ).isPrime)]
      rintro ⟨Q, hQ, hle⟩
      exact hNQ Q (hfin.mem_toFinset.mp hQ) hle
    obtain ⟨f, hfN, hf⟩ := Set.not_subset.mp hns
    refine ⟨f, hfN, fun Q hQ hfQ => hf ?_⟩
    exact Set.mem_biUnion (Finset.mem_coe.mpr (hfin.mem_toFinset.mpr hQ)) hfQ
  have hfW : f ∉ W := hfQ W hW
  have hfP : f ∉ P := fun hf => hfW (hPW hf)

  have hPfN : P ⊔ Ideal.span {f} ≤ N :=
    sup_le (hPW.trans hWN) ((Ideal.span_singleton_le_iff_mem _).mpr hfN)
  obtain ⟨P', hP', hP'N⟩ := Ideal.exists_minimalPrimes_le hPfN
  have hP'p : P'.IsPrime := hP'.isPrime
  have hPP' : P ≤ P' := le_sup_left.trans hP'.le
  have hfP' : f ∈ P' := hP'.le (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  have hQN : ∀ Q ∈ (P ⊔ vX).minimalPrimes, Q ≤ N → Q = W := fun Q hQ hle => by
    by_contra hne
    exact hhN (hle (hhQ Q hQ hne))
  have hPltW : P < W := lt_of_le_of_ne hPW fun hPW' => v.ne_bot (by
    rw [eq_bot_iff, ← hPC, hPW']
    exact Ideal.map_le_iff_le_comap.mp hvW)
  have hvP' : ¬ vX ≤ P' := by
    intro hle
    obtain ⟨Q, hQ, hQP'⟩ := Ideal.exists_minimalPrimes_le (sup_le hPP' hle)
    rw [hQN Q hQ (hQP'.trans hP'N)] at hQP'
    rcases hQP'.lt_or_eq with hlt | heq
    · exact not_lt_of_mem_minimalPrimes_sup_span hPltW hP' hlt
    · exact hfW (heq ▸ hfP')
  have hP'C : P'.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ := by
    by_contra hne
    have hmax : (P'.comap (C : O →+* MvPolynomial (Fin n) O)).IsMaximal :=
      Ideal.IsPrime.isMaximal inferInstance hne
    have heq : P'.comap (C : O →+* MvPolynomial (Fin n) O) = N.comap C :=
      hmax.eq_of_le (Ideal.comap_ne_top _ hNp.ne_top) (Ideal.comap_mono hP'N)
    apply hvP'
    rw [hvX, Ideal.map_le_iff_le_comap, heq]
    exact Ideal.map_le_iff_le_comap.mp (hvW.trans hWN)

  obtain ⟨W', hW', hW'N⟩ := Ideal.exists_minimalPrimes_le
    (sup_le hP'N (hvW.trans hWN) : P' ⊔ vX ≤ N)
  have : W'.IsPrime := hW'.isPrime
  have hWW' : W ≤ W' := by
    obtain ⟨Q, hQ, hQW'⟩ := Ideal.exists_minimalPrimes_le
      (sup_le (hPP'.trans (le_sup_left.trans hW'.le)) (le_sup_right.trans hW'.le) : P ⊔ vX ≤ W')
    rw [← hQN Q hQ (hQW'.trans hW'N)]
    exact hQW'
  have hfW' : f ∈ W' := hW'.le (Ideal.mem_sup_left hfP')
  refine ⟨P', W', f, hfP, hP', hP'C, hW', le_antisymm ?_ ?_⟩
  · have hne : W'.map (Ideal.Quotient.mk W) ≠ ⊥ := by
      intro hb
      apply hfW
      have hm : Ideal.Quotient.mk W f ∈ W'.map (Ideal.Quotient.mk W) := Ideal.mem_map_of_mem _ hfW'
      rw [hb, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hm
      exact hm
    have h2 := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le _ hne
    rwa [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hWW')] at h2
  · rw [← hdimN]
    exact add_le_add (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hW'N)
      (Ideal.Quotient.factor_surjective hW'N)) le_rfl

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PFibreCompDim
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial IsDedekindDomain

section Residue

variable {O : Type} [CommRing O] [IsDedekindDomain O] {n : ℕ} (v : HeightOneSpectrum O)
  (W : Ideal (MvPolynomial (Fin n) O))

noncomputable def quotientResidueEquiv (hW : Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal ≤ W) :
    (MvPolynomial (Fin n) O ⧸ W) ≃+*
      (MvPolynomial (Fin n) v.asIdeal.ResidueField ⧸
        W.map (MvPolynomial.map (algebraMap O v.asIdeal.ResidueField))) :=
  let φ : MvPolynomial (Fin n) O →+* MvPolynomial (Fin n) v.asIdeal.ResidueField :=
    MvPolynomial.map (algebraMap O v.asIdeal.ResidueField)
  have hφ : Function.Surjective φ :=
    MvPolynomial.map_surjective _ (Ideal.algebraMap_residueField_surjective _)
  have hψ : Function.Surjective ((Ideal.Quotient.mk (W.map φ)).comp φ) :=
    Ideal.Quotient.mk_surjective.comp hφ
  have hker : RingHom.ker ((Ideal.Quotient.mk (W.map φ)).comp φ) = W := by
    have : RingHom.ker φ = Ideal.map C v.asIdeal := by
      rw [MvPolynomial.ker_map, Ideal.ker_algebraMap_residueField]
    rw [← RingHom.comap_ker, Ideal.mk_ker, Ideal.comap_map_of_surjective _ hφ,
      ← RingHom.ker_eq_comap_bot, this, sup_eq_left.mpr hW]
  (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hψ)

theorem exists_ringKrullDim_quotient_eq_nat (hWp : W.IsPrime)
    (hW : Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal ≤ W) :
    ∃ m : ℕ, ringKrullDim (MvPolynomial (Fin n) O ⧸ W) = m := by
  let φ : MvPolynomial (Fin n) O →+* MvPolynomial (Fin n) v.asIdeal.ResidueField :=
    MvPolynomial.map (algebraMap O v.asIdeal.ResidueField)
  have hφ : Function.Surjective φ :=
    MvPolynomial.map_surjective _ (Ideal.algebraMap_residueField_surjective _)
  have hkerW : RingHom.ker φ ≤ W := by
    rw [MvPolynomial.ker_map, Ideal.ker_algebraMap_residueField]
    exact hW
  have : (W.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ hkerW
  obtain ⟨m, hm, -⟩ := GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg
    (k := v.asIdeal.ResidueField) (A := MvPolynomial (Fin n) v.asIdeal.ResidueField ⧸ W.map φ)
  exact ⟨m, (ringKrullDim_eq_of_ringEquiv (quotientResidueEquiv v W hW)).trans hm⟩

end Residue

theorem FibreCompDim.proof (hBase : FibreClosedComponent.Statement) (hCut : FibreCut.Statement)
    (hDrop : GenericFibreDrop.Statement) : FibreCompDim.Statement := by
  intro O _ _ F _ _ _ n P W v hP hPC hW
  have key : ∀ (m : ℕ) (P W : Ideal (MvPolynomial (Fin n) O)), P.IsPrime →
      P.comap (C : O →+* MvPolynomial (Fin n) O) = ⊥ →
      W ∈ (P ⊔ Ideal.map (C : O →+* MvPolynomial (Fin n) O) v.asIdeal).minimalPrimes →
      ringKrullDim (MvPolynomial (Fin n) O ⧸ W) = m →
      ringKrullDim (MvPolynomial (Fin n) O ⧸ W) =
        ringKrullDim (MvPolynomial (Fin n) F ⧸ P.map (MvPolynomial.map (algebraMap O F))) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro P W hP hPC hW hm
    by_cases hmax : W.IsMaximal
    · rw [hBase O F n P W v hP hPC hW hmax]
      let _ := Ideal.Quotient.field W
      exact ringKrullDim_eq_zero_of_field _
    · obtain ⟨P', W', f, hfP, hP', hP'C, hW', hdim⟩ := hCut O n P W v hP hPC hW hmax
      have : W'.IsPrime := hW'.1.1
      have : P'.IsPrime := hP'.1.1
      obtain ⟨m', hm'⟩ := exists_ringKrullDim_quotient_eq_nat v W' hW'.1.1
        (le_sup_right.trans hW'.1.2)
      have hmm : m' + 1 = m := by
        rw [hm', hm] at hdim
        exact_mod_cast hdim
      rw [hDrop O F n P P' f hP hP'C hfP hP', ← ih m' (by omega) P' W' hP'.1.1 hP'C hW' hm', hdim]
  have : W.IsPrime := hW.1.1
  obtain ⟨m, hm⟩ := exists_ringKrullDim_quotient_eq_nat v W hW.1.1 (le_sup_right.trans hW.1.2)
  rw [← ringKrullDim_eq_of_ringEquiv (quotientResidueEquiv v W (le_sup_right.trans hW.1.2))]
  exact key m P W hP hPC hW hm

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PCodimOnePrimeAvoid
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open GroundTheory.Arith.Abelian.Jacobian

theorem CodimOnePrimeAvoid.proof : CodimOnePrimeAvoid.Statement := by
  intro k B _ _ _ _ _ h hh hdim
  let Bh := Localization.Away h
  have hle : Submonoid.powers h ≤ nonZeroDivisors B :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hh
  have : IsDomain Bh := IsLocalization.isDomain_localization hle
  have : Algebra.FinitePresentation B Bh := IsLocalization.Away.finitePresentation (S := Bh) h
  have : Algebra.FiniteType B Bh := inferInstance
  have : Algebra.FiniteType k Bh := Algebra.FiniteType.trans (S := B) inferInstance inferInstance
  have : IsNoetherianRing Bh := Algebra.FiniteType.isNoetherianRing k Bh
  let K := FractionRing B
  have hu : ∀ y : Submonoid.powers h, IsUnit (algebraMap B K y) := fun y =>
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective B K)).2
      (nonZeroDivisors.ne_zero (hle y.2)))
  let _ : Algebra Bh K := (IsLocalization.lift (M := Submonoid.powers h) (S := Bh) hu).toAlgebra
  have : IsScalarTower B Bh K := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.lift_eq (M := Submonoid.powers h) (S := Bh) hu x).symm
  have : IsScalarTower k Bh K := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply k B K, IsScalarTower.algebraMap_apply k B Bh,
      ← IsScalarTower.algebraMap_apply B Bh K]
  have : IsFractionRing Bh K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers h) Bh K
  have hdimh : ringKrullDim Bh = ringKrullDim B := by
    rw [ringKrullDim_eq_trdeg_fractionRing k K, ringKrullDim_eq_trdeg_fractionRing k K]
  have hnf : ¬ IsField Bh := fun hf => by
    have h0 := ringKrullDim_eq_zero_of_isField hf
    rw [hdimh] at h0
    rw [h0] at hdim
    exact absurd hdim (by decide)
  obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.1 hnf
  obtain ⟨x, hxp, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
  obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le ((Ideal.span_singleton_le_iff_mem p).2 hxp)
  have hqp : q.IsPrime := hq.isPrime
  have hxq : x ∈ q := (Ideal.span_singleton_le_iff_mem q).1 hq.1.2
  have hq1 : q.height = 1 := by
    refine le_antisymm (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ q hq) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    rintro rfl
    exact hx0 hxq
  refine ⟨q.comap (algebraMap B Bh), hqp.comap _, fun hhN => hqp.ne_top ?_, ?_⟩
  · exact Ideal.eq_top_of_isUnit_mem _ hhN (IsLocalization.Away.algebraMap_isUnit h)
  · have hN := IsLocalization.height_under (Submonoid.powers h) q
    rw [hq1] at hN
    have := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient k (q.comap (algebraMap B Bh))
    rw [Ideal.under] at hN
    rw [hN] at this
    rw [← this, add_comm]
    rfl

end GroundTheory.Heights₂.Heights.Vertical
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

theorem SecAlgFinite.full : SecAlgFinite.Statement := SecAlgFinite.proof IncidenceNull.full
theorem ChartDomain.full : ChartDomain.Statement := ChartDomain.proof
theorem GenSecDomain.full : GenSecDomain.Statement :=
  GenSecDomain.proof ChartDomain.full GroundTheory.Heights₂.Heights.IncidenceGeneric.full
    (GroundTheory.Heights₂.Heights.IncIdealBelow.proof GroundTheory.Heights₂.Heights.ChowFormMultiHomog.full)
theorem SecAlgField.full : SecAlgField.Statement := SecAlgField.proof SecAlgFinite.full GenSecDomain.full
theorem ChowSecDvd.full : ChowSecDvd.Statement := ChowSecDvd.proof IncidenceNull.full
theorem NormFormIrreducible.full : NormFormIrreducible.Statement := NormFormIrreducible.proof
theorem NormFormDvd.full : NormFormDvd.Statement := NormFormDvd.proof
theorem SecAlgFieldChange.full : SecAlgFieldChange.Statement := SecAlgFieldChange.proof
theorem GenChowIrreducible.full : GenChowIrreducible.Statement :=
  GenChowIrreducible.proof GroundTheory.Heights₂.Heights.IncIdealPrime.full
    GroundTheory.Heights₂.Heights.ChowFormMultiHomog.full

theorem SpecFirstNeField.full : SpecFirstNeField.Statement :=
  have hDim : GroundTheory.Heights₂.Heights.IncIdealDim.Statement :=
    GroundTheory.Heights₂.Heights.IncIdealDim.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full
      GroundTheory.Heights₂.Heights.GenericLinearTrdeg.full GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof
  SpecFirstNeField.proof
    (GroundTheory.Heights₂.Heights.ConeDimOfChowForm.proof hDim GroundTheory.Heights₂.Heights.IncIdealPrime.full)
    GroundTheory.Heights₂.Heights.ConeDimComponent.full
    (GroundTheory.Heights₂.Heights.ChowFormExists.proof hDim GroundTheory.Heights₂.Heights.IncIdealPrime.full)
    GroundTheory.Heights₂.Heights.IncidenceZeroLocus.proof

theorem SecBTorsionFree.full : SecBTorsionFree.Statement := SecBTorsionFree.proof ParDVRIsDVR.full
theorem GaussDVR.full : GaussDVR.Statement := GaussDVR.proof ParDVRIsDVR.full
theorem VertSpec.full : VertSpec.Statement := VertSpec.proof
theorem ResidueAlgIndep.full : ResidueAlgIndep.Statement := ResidueAlgIndep.proof

theorem CodimOnePrimeAvoid.full : CodimOnePrimeAvoid.Statement := CodimOnePrimeAvoid.proof
theorem FibreCut.full : FibreCut.Statement := FibreCut.proof CodimOnePrimeAvoid.full
theorem GenericFibreDrop.full : GenericFibreDrop.Statement := GenericFibreDrop.proof

theorem ChowFormSectionVertical.of_remaining
    (hGenSep : GenSecSeparable.Statement) (hFibre : FibreClosedComponent.Statement)
    (hKer : GenSecKer.Statement) (hChart : SpecChart.Statement) (hOrd : FiniteOrd.Statement) :
    ChowFormSectionVertical.Statement := by
  have hDim : GroundTheory.Heights₂.Heights.IncIdealDim.Statement :=
    GroundTheory.Heights₂.Heights.IncIdealDim.proof GroundTheory.Heights₂.Heights.IncidenceGeneric.full
      GroundTheory.Heights₂.Heights.GenericLinearTrdeg.full GroundTheory.Heights₂.Heights.AffineChartTrdeg.proof
  have hCone : GroundTheory.Heights₂.Heights.ConeDimOfChowForm.Statement :=
    GroundTheory.Heights₂.Heights.ConeDimOfChowForm.proof hDim GroundTheory.Heights₂.Heights.IncIdealPrime.full
  have hExist : GroundTheory.Heights₂.Heights.ChowFormExists.Statement :=
    GroundTheory.Heights₂.Heights.ChowFormExists.proof hDim GroundTheory.Heights₂.Heights.IncIdealPrime.full
  have cnf : ChowNormForm.Statement :=
    ChowNormForm.proof
      (ChowNormFormGeneric.proof SecAlgFinite.full GenSecDomain.full hGenSep ChowSecDvd.full
        NormFormIrreducible.full GenChowIrreducible.full NormFormDvd.full)
      SecAlgFieldChange.full
  have csd : ChowSecDegree.Statement := ChowSecDegree.proof cnf ChowFormHomog.full NormFormEval.full
  have nzd : SecLinNZD.Statement := SecLinNZD.proof cnf NormFormEval.full SpecFirstNeField.full
  have lininj : SecBLinInj.Statement :=
    SecBLinInj.proof SecBGeneric.full SecBTorsionFree.full nzd ParAlgIndep.full
  have fcd : FibreCompDim.Statement := FibreCompDim.proof hFibre FibreCut.full GenericFibreDrop.full
  have scd : SpecCompDim.Statement := SpecCompDim.proof hCone fcd
  have sip : SecIdealOfPrime.Statement :=
    SecIdealOfPrime.proof scd hExist ResidueAlgIndep.full SecAlgField.full hKer
  have smax : SpecMax.Statement := SpecMax.proof SecBFinite.full sip
  have sres : SpecResidue.Statement := SpecResidue.proof csd cnf scd hExist ResidueAlgIndep.full
  have slen : SpecLength.Statement :=
    SpecLength.proof hChart hOrd ParDVRIsDVR.full SecBFinite.full lininj
  have nid : NormIdentity.Statement :=
    NormIdentity.proof cnf SecBFinite.full SecBTorsionFree.full SecBGeneric.full NormFormLocalization.full
      NormFormEval.full ParAlgIndep.full ParFracIsFractionRing.full ParDVRIsDVR.full
  have oeq : OrdEq.Statement :=
    OrdEq.proof nid NormLength.full LengthDecomp.full smax slen sres VertSpec.full lininj
      SecBFinite.full SecBTorsionFree.full ParDVRIsDVR.full
  have geq : GaussEq.Statement := GaussEq.proof oeq GaussDVR.full ParDVRIsDVR.full
  exact Main.proof geq PrimitiveScale.full VertTermEq.full

end GroundTheory.Heights₂.Heights.Vertical
