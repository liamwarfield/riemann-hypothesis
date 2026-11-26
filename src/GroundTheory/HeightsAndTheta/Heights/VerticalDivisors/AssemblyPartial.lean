module

public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowFormHomog
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.POrdEq
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecAlgField
public import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
public import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChowNorm

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecBFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

namespace SecBFinite

section Homog

variable {σ R S : Type*} [CommRing R] [CommRing S]

theorem map_homogeneousComponent (f : R →+* S) (d : ℕ) (p : MvPolynomial σ R) :
    MvPolynomial.map f (homogeneousComponent d p) = homogeneousComponent d (MvPolynomial.map f p) := by
  ext m
  rw [coeff_map, coeff_homogeneousComponent, coeff_homogeneousComponent, coeff_map]
  split_ifs <;> simp

theorem isHomogeneous_linForm {n : ℕ} (u : Fin n → R) : (linForm u).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun j _ => isHomogeneous_C_mul_X (u j) j

attribute [local instance] MvPolynomial.gradedAlgebra

theorem homogeneousComponent_mul_of_deg_one (c t : MvPolynomial σ R) (ht : t.IsHomogeneous 1) (d : ℕ) :
    homogeneousComponent (d + 1) (c * t) = homogeneousComponent d c * t := by
  have key : ∀ (x : MvPolynomial σ R) (i : ℕ),
      (DirectSum.decompose (homogeneousSubmodule σ R) x i : MvPolynomial σ R) =
        homogeneousComponent i x :=
    fun x i => decomposition.decompose'_apply x i
  have h := DirectSum.coe_decompose_mul_of_right_mem_of_le (𝒜 := homogeneousSubmodule σ R) (a := c)
    (n := d + 1) ((mem_homogeneousSubmodule 1 t).mpr ht) (by omega)
  rw [key, key, Nat.add_sub_cancel] at h
  exact h

theorem isHomogeneous_span_of {s : Set (MvPolynomial σ R)} (h : ∀ x ∈ s, ∃ d, x.IsHomogeneous d) :
    (Ideal.span s).IsHomogeneous (homogeneousSubmodule σ R) :=
  Ideal.homogeneous_span _ _ fun x hx =>
    let ⟨d, hd⟩ := h x hx
    ⟨d, (mem_homogeneousSubmodule d x).mpr hd⟩

theorem isHomogeneous_map_of (f : R →+* S) (P : Ideal (MvPolynomial σ R))
    (hP : ∀ p ∈ P, ∀ d, homogeneousComponent d p ∈ P) :
    (P.map (MvPolynomial.map f)).IsHomogeneous (homogeneousSubmodule σ S) := by
  have hspan : P.map (MvPolynomial.map f) =
      Ideal.span {x | ∃ p ∈ P, ∃ d, x = MvPolynomial.map f (homogeneousComponent d p)} := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro p hp
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Ideal.mem_comap, ← sum_homogeneousComponent p, map_sum]
      exact Ideal.sum_mem _ fun d _ => Ideal.subset_span ⟨p, hp, d, rfl⟩
    · rw [Ideal.span_le]
      rintro _ ⟨p, hp, d, rfl⟩
      exact Ideal.mem_map_of_mem _ (hP p hp d)
  rw [hspan]
  refine isHomogeneous_span_of ?_
  rintro _ ⟨p, -, d, rfl⟩
  exact ⟨d, by rw [map_homogeneousComponent]; exact homogeneousComponent_isHomogeneous _ _⟩

end Homog

theorem finite_of_pow_mem {R : Type*} [CommRing R] {n : ℕ} (Q : Ideal (MvPolynomial (Fin n) R))
    (M : Fin n → ℕ) (q : Fin n → MvPolynomial (Fin n) R) (hq : ∀ j, (q j).totalDegree < M j)
    (hQ : ∀ j, X j ^ M j - q j ∈ Q) : Module.Finite R (MvPolynomial (Fin n) R ⧸ Q) := by
  classical
  let S : Set (MvPolynomial (Fin n) R ⧸ Q) :=
    Set.range fun α : (j : Fin n) → Fin (M j) =>
      Ideal.Quotient.mk Q (monomial (Finsupp.equivFunOnFinite.symm fun j => (α j : ℕ)) 1)
  have hC : ∀ (r : R) (p : MvPolynomial (Fin n) R),
      Ideal.Quotient.mk Q (C r * p) = r • Ideal.Quotient.mk Q p := by
    intro r p
    rw [← MvPolynomial.smul_eq_C_mul, ← Ideal.Quotient.mkₐ_eq_mk R, map_smul]
  have key : ∀ d (s : Fin n →₀ ℕ), s.degree ≤ d →
      Ideal.Quotient.mk Q (monomial s 1) ∈ Submodule.span R S := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
    intro s hs
    by_cases hsmall : ∀ j, s j < M j
    · refine Submodule.subset_span ⟨fun j => ⟨s j, hsmall j⟩, ?_⟩
      show Ideal.Quotient.mk Q (monomial (Finsupp.equivFunOnFinite.symm fun j => s j) 1) = _
      rw [Finsupp.equivFunOnFinite_symm_coe]
    · push Not at hsmall
      obtain ⟨j, hj⟩ := hsmall
      obtain ⟨s', rfl⟩ : ∃ s', s = s' + Finsupp.single j (M j) :=
        ⟨s - Finsupp.single j (M j), (tsub_add_cancel_of_le (Finsupp.single_le_iff.mpr hj)).symm⟩
      have hmk : Ideal.Quotient.mk Q (monomial (s' + Finsupp.single j (M j)) 1) =
          Ideal.Quotient.mk Q (monomial s' 1 * q j) := by
        have hmono : monomial (s' + Finsupp.single j (M j)) (1 : R) = monomial s' 1 * X j ^ M j := by
          rw [X_pow_eq_monomial, monomial_mul, one_mul]
        rw [hmono, Ideal.Quotient.eq, ← mul_sub]
        exact Q.mul_mem_left _ (hQ j)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hmk, (q j).as_sum, Finset.mul_sum, map_sum]
      refine Submodule.sum_mem _ fun m hm => ?_
      have hprod : monomial s' (1 : R) * monomial m (AddMonoidAlgebra.coeff (q j) m) =
          C (AddMonoidAlgebra.coeff (q j) m) * monomial (s' + m) 1 := by
        rw [monomial_mul, C_mul_monomial, one_mul, mul_one]
      rw [hprod, hC]
      refine Submodule.smul_mem _ _ (ih _ ?_ _ le_rfl)
      have hm' : m.degree ≤ (q j).totalDegree := le_totalDegree hm
      have hqj := hq j
      rw [map_add (f := _), Finsupp.degree_single] at hs
      rw [map_add (f := _)]
      omega
  refine ⟨(Submodule.fg_def).mpr ⟨S, Set.finite_range _, ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  set_option synthInstance.maxHeartbeats 100000 in
    rw [p.as_sum, map_sum]
  refine Submodule.sum_mem _ fun s _ => ?_
  rw [← mul_one (AddMonoidAlgebra.coeff p s), ← C_mul_monomial, hC]
  exact Submodule.smul_mem _ _ (key _ s le_rfl)

section NumberField

variable {K : Type*} [Field K] [NumberField K]

theorem map_integralModel {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) :
    (integralModel I).map (MvPolynomial.map (algebraMap (𝓞 K) K)) = I := _root_.GroundTheory.Heights₂.Heights.Vertical.SecBGeneric.map_integralModel (n := n) I


omit [NumberField K] in
theorem homogeneousComponent_mem_integralModel {n : ℕ} {I : Ideal (MvPolynomial (Fin n) K)}
    (hI : IsHomogIdeal I) : ∀ p ∈ integralModel I, ∀ d, homogeneousComponent d p ∈ integralModel I := by
  intro p hp d
  show MvPolynomial.map (algebraMap (𝓞 K) K) (homogeneousComponent d p) ∈ I
  rw [map_homogeneousComponent]
  exact hI _ hp d


attribute [local instance] MvPolynomial.algebraMvPolynomial in
theorem exists_C_mul_mem {σ : Type*} (J : Ideal (MvPolynomial σ (𝓞 K))) (h : MvPolynomial σ (𝓞 K))
    (hh : MvPolynomial.map (algebraMap (𝓞 K) K) h ∈ J.map (MvPolynomial.map (algebraMap (𝓞 K) K))) :
    ∃ d : 𝓞 K, d ≠ 0 ∧ C d * h ∈ J := by
  obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, hx⟩ := (IsLocalization.mem_map_algebraMap_iff
    ((nonZeroDivisors (𝓞 K)).map (C (σ := σ))) (MvPolynomial σ K)).mp hh
  obtain ⟨d, hd, rfl⟩ := Submonoid.mem_map.mp hs
  refine ⟨d, nonZeroDivisors.ne_zero hd, ?_⟩
  have hda : C d * h = a := by
    apply MvPolynomial.map_injective _ (IsFractionRing.injective (𝓞 K) K)
    rw [map_mul, mul_comm]
    exact hx
  rw [hda]
  exact ha

theorem incIdeal_le_map {n k : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) :
    incIdeal I k ≤ (incIdeal (integralModel I) k).map (MvPolynomial.map (algebraMap (𝓞 K) K)) := by
  apply sup_le
  · have hI : I.map (rename (R := K) (Sum.inl : Fin n → Fin n ⊕ (Fin k × Fin n))) =
        ((integralModel I).map (MvPolynomial.map (algebraMap (𝓞 K) K))).map (rename Sum.inl) := by
      rw [map_integralModel]
    rw [hI, Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, Ideal.mem_comap, ← map_rename]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp))
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have hform : (∑ j, X (Sum.inr (i, j)) * X (Sum.inl j) : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) K) =
        MvPolynomial.map (algebraMap (𝓞 K) K) (∑ j, X (Sum.inr (i, j)) * X (Sum.inl j)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum]
    show (∑ j, X (Sum.inr (i, j)) * X (Sum.inl j) : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) K) ∈ _
    rw [hform]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))

def parIdx (e n : ℕ) (ij : Fin (e + 1) × Fin n) : Par e n :=
  Fin.cases (motive := fun _ => Par e n) (Sum.inr ij.2) (fun i => Sum.inl (i, ij.2)) ij.1

theorem parIdx_injective (e n : ℕ) : Function.Injective (parIdx e n) := by
  rintro ⟨i, j⟩ ⟨i', j'⟩ h
  induction i using Fin.cases <;> induction i' using Fin.cases <;> simp_all [parIdx]

def specHom (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    MvPolynomial (Fin n ⊕ (Fin (e + 1) × Fin n)) (𝓞 K) →+* MvPolynomial (Fin n) (ParDVR e n v) :=
  eval₂Hom (C.comp (algebraMap (𝓞 K) (ParDVR e n v)))
    (Sum.elim X fun ij => C (parY e n v (parIdx e n ij)))

omit [NumberField K] in
theorem specHom_X_inl (e : ℕ) {n : ℕ} (v : HeightOneSpectrum (𝓞 K)) (j : Fin n) :
    specHom e n v (X (Sum.inl j)) = X j := by
  simp [specHom]

omit [NumberField K] in
theorem specHom_rename_inl (e : ℕ) {n : ℕ} (v : HeightOneSpectrum (𝓞 K))
    (p : MvPolynomial (Fin n) (𝓞 K)) :
    specHom e n v (rename Sum.inl p) = MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v)) p := by
  rw [specHom, coe_eval₂Hom, eval₂_rename, Sum.elim_comp_inl]
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [eval₂_add, hp, hq, map_add (f := _)]
  | mul_X p i hp => rw [eval₂_mul, hp, eval₂_X, map_mul, map_X]

omit [NumberField K] in
theorem specHom_form (e : ℕ) {n : ℕ} (v : HeightOneSpectrum (𝓞 K)) (i : Fin (e + 1)) :
    specHom e n v (∑ j, X (Sum.inr (i, j)) * X (Sum.inl j)) =
      linForm fun j => parY e n v (parIdx e n (i, j)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [specHom, linForm, map_sum]

omit [NumberField K] in
theorem specHom_rename_inr (e : ℕ) {n : ℕ} (v : HeightOneSpectrum (𝓞 K))
    (g : MvPolynomial (Fin (e + 1) × Fin n) (𝓞 K)) :
    specHom e n v (rename Sum.inr g) =
      C (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (rename (parIdx e n) g)) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    rw [rename_C, rename_C, specHom, eval₂Hom_C, RingHom.comp_apply,
      IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v),
      MvPolynomial.algebraMap_eq]
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hp, hq, C_add]
  | mul_X p ij hp =>
    rw [map_mul, map_mul, map_mul, map_mul, hp, C_mul, rename_X, rename_X]
    congr 1
    simp [specHom, parY]


omit [NumberField K] in
theorem incIdeal_le_comap_specHom (e : ℕ) {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K))
    (v : HeightOneSpectrum (𝓞 K)) :
    incIdeal (integralModel I) (e + 1) ≤
      (modelR e I v ⊔ Ideal.span (Set.range (secForm (parY e n v))) ⊔
        Ideal.span {chartForm (parY e n v)}).comap (specHom e n v) := by
  apply sup_le
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, Ideal.mem_comap, specHom_rename_inl]
    exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp))
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, Ideal.mem_comap, specHom_form]
    induction i using Fin.cases with
    | zero =>
      exact Ideal.mem_sup_right (Ideal.subset_span (by simp [chartForm, parIdx]))
    | succ i =>
      exact Ideal.mem_sup_left (Ideal.mem_sup_right (Ideal.subset_span ⟨i, by simp [secForm, parIdx]⟩))

end NumberField

end SecBFinite


attribute [local instance] MvPolynomial.gradedAlgebra in
open SecBFinite in
theorem SecBFinite.proof (hIN : IncidenceNull.Statement) (hCT : ChartTorsion.Statement)
    (hPS : PrimitiveScale.Statement) : SecBFinite.Statement := by
  intro K _ _ n e I f v hI hf
  obtain ⟨c, g, -, hg, m0, hm0⟩ := hPS K v _ f hf.1
  obtain ⟨m, hm⟩ := hIN K n (e + 1) I f hf
  have := hI.isPrime
  have hPprime : (integralModel I).IsPrime := by
    show (I.comap _).IsPrime
    infer_instance
  have hPC : ∀ a : 𝓞 K, C a ∈ integralModel I → a = 0 := by
    intro a ha
    by_contra h0
    have haI : (C (algebraMap (𝓞 K) K a) : MvPolynomial (Fin n) K) ∈ I := by
      simpa [integralModel] using ha
    have hu : IsUnit (C (algebraMap (𝓞 K) K a) : MvPolynomial (Fin n) K) :=
      (isUnit_iff_ne_zero.mpr
        ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).mpr h0)).map C
    exact hI.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ haI hu)

  set γ := algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (rename (parIdx e n) g) with hγdef
  have hγ : IsUnit γ := by
    rw [hγdef, IsLocalization.AtPrime.isUnit_to_map_iff (ParDVR e n v) (parPrime e n v),
      Ideal.mem_primeCompl_iff]
    intro hmem
    rw [parPrime, MvPolynomial.mem_map_C_iff] at hmem
    have h0 := hmem (m0.mapDomain (parIdx e n))
    rw [coeff_rename_mapDomain _ (parIdx_injective e n)] at h0
    exact hm0 h0
  obtain ⟨w, hw⟩ := hγ

  have hpow : ∀ j, ∃ M, X j ^ (M + 1) ∈ modelR e I v ⊔ Ideal.span (Set.range (secForm (parY e n v))) ⊔
      Ideal.span {chartForm (parY e n v)} := by
    intro j
    have hmapped : MvPolynomial.map (algebraMap (𝓞 K) K) ((rename Sum.inr g * X (Sum.inl j)) ^ m) ∈
        (incIdeal (integralModel I) (e + 1)).map (MvPolynomial.map (algebraMap (𝓞 K) K)) := by
      apply incIdeal_le_map I
      have hmap : MvPolynomial.map (algebraMap (𝓞 K) K) ((rename Sum.inr g * X (Sum.inl j)) ^ m) =
          C c ^ m * (rename Sum.inr f * X (Sum.inl j)) ^ m := by
        rw [map_pow, map_mul, map_rename, hg, map_X, map_mul, rename_C]
        ring
      rw [hmap]
      exact Ideal.mul_mem_left _ _ (hm j)
    obtain ⟨d, hd, hdh⟩ := exists_C_mul_mem _ _ hmapped
    obtain ⟨N, hN⟩ := hCT (𝓞 K) n (e + 1) (integralModel I) hPprime hPC d _ hd hdh j
    have hsp := incIdeal_le_comap_specHom e I v hN
    rw [Ideal.mem_comap, map_mul, map_pow, map_pow, map_mul, specHom_X_inl, specHom_rename_inr,
      ← hγdef, ← hw] at hsp
    refine ⟨N + m, ?_⟩
    set u : ParDVR e n v := ((w : (ParDVR e n v)ˣ) : ParDVR e n v) with hu
    set u' : ParDVR e n v := ((w⁻¹ : (ParDVR e n v)ˣ) : ParDVR e n v) with hu'
    have h1 : (C u' : MvPolynomial (Fin n) (ParDVR e n v)) * C u = 1 := by
      rw [← C_mul, hu, hu', Units.inv_mul, C_1]
    have hX : X j ^ (N + m + 1) = (X j * C u' ^ m) * (X j ^ N * (C u * X j) ^ m) := by
      rw [show (X j * C u' ^ m) * (X j ^ N * (C u * X j) ^ m) =
          X j ^ (N + m + 1) * ((C u' : MvPolynomial (Fin n) (ParDVR e n v)) * C u) ^ m
          by ring, h1, one_pow, mul_one]
    rw [hX]
    exact Ideal.mul_mem_left _ _ hsp

  have hJ0 : (modelR e I v ⊔ Ideal.span (Set.range (secForm (parY e n v)))).IsHomogeneous
      (homogeneousSubmodule (Fin n) (ParDVR e n v)) := by
    refine (isHomogeneous_map_of _ _ (homogeneousComponent_mem_integralModel hI.isHomog)).sup
      (isHomogeneous_span_of ?_)
    rintro _ ⟨i, rfl⟩
    exact ⟨1, isHomogeneous_linForm _⟩
  have hq : ∀ j, ∃ M : ℕ, ∃ q : MvPolynomial (Fin n) (ParDVR e n v), q.totalDegree < M ∧
      X j ^ M - q ∈ secIdeal (modelR e I v) (parY e n v) := by
    intro j
    obtain ⟨M, hM⟩ := hpow j
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hM
    obtain ⟨c', rfl⟩ := Ideal.mem_span_singleton'.mp hb
    refine ⟨M + 1, homogeneousComponent M c', ?_, ?_⟩
    · exact lt_of_le_of_lt (homogeneousComponent_isHomogeneous M c').totalDegree_le (Nat.lt_succ_self M)
    · have hXM : homogeneousComponent (M + 1) (X j ^ (M + 1) : MvPolynomial (Fin n) (ParDVR e n v)) =
          X j ^ (M + 1) := homogeneousComponent_eq_self (isHomogeneous_X_pow _ _)
      have h2 := congrArg (homogeneousComponent (M + 1)) hab
      rw [map_add (f := _), homogeneousComponent_mul_of_deg_one _ (chartForm (parY e n v)) (isHomogeneous_linForm _), hXM] at h2
      have ha' : homogeneousComponent (M + 1) a ∈
          modelR e I v ⊔ Ideal.span (Set.range (secForm (parY e n v))) :=
        homogeneousComponent_mem_of_mem hJ0 ha _
      rw [← h2, show homogeneousComponent (M + 1) a + homogeneousComponent M c' * chartForm (parY e n v) -
          homogeneousComponent M c' = homogeneousComponent (M + 1) a +
            homogeneousComponent M c' * (chartForm (parY e n v) - 1) by ring]
      exact Ideal.add_mem _ (Ideal.mem_sup_left ha')
        (Ideal.mem_sup_right (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)))
  choose M q hqdeg hqmem using hq
  exact finite_of_pow_mem _ M q hqdeg hqmem

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PVertTermEq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

theorem vertComps_finite {K : Type*} [Field K] [NumberField K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (u : Fin n → 𝓞 K) (v : HeightOneSpectrum (𝓞 K)) :
    (vertComps I u v).Finite :=
  (Ideal.finite_minimalPrimes_of_isNoetherianRing _ _).subset fun _ hW => hW.1.1

theorem VertTermEq.proof : VertTermEq.Statement := by
  intro K _ _ n e I u v
  have hfin := vertComps_finite I u v
  unfold vertTermAt vertDeg
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun W _ => ?_
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PPrimitiveScale
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain nonZeroDivisors

noncomputable section

theorem PrimitiveScale.proof : PrimitiveScale.Statement := by
  intro K _ _ v σ f hf
  classical
  set J : FractionalIdeal (𝓞 K)⁰ K := FractionalIdeal.spanFinset (𝓞 K) f.support (fun m => f.coeff m)
    with hJdef
  have hJ : J ≠ 0 := by
    rw [hJdef, FractionalIdeal.spanFinset_ne_zero]
    obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hf
    exact ⟨m, MvPolynomial.mem_support_iff.mpr hm, hm⟩
  have hJJ : J * J⁻¹ = 1 := mul_inv_cancel₀ hJ
  have hcoeff : ∀ m, f.coeff m ∈ J := by
    intro m
    by_cases hm : f.coeff m = 0
    · rw [hm, ← FractionalIdeal.mem_coe]; exact Submodule.zero_mem _
    · rw [← FractionalIdeal.mem_coe, hJdef, FractionalIdeal.spanFinset_coe]
      exact Submodule.subset_span ⟨m, MvPolynomial.mem_support_iff.mpr hm, rfl⟩
  have hint : ∀ c ∈ J⁻¹, ∀ m, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = c * f.coeff m := by
    intro c hc m
    have h1 : f.coeff m * c ∈ J * J⁻¹ := FractionalIdeal.mul_mem_mul (hcoeff m) hc
    rw [hJJ, FractionalIdeal.mem_one_iff] at h1
    obtain ⟨y, hy⟩ := h1
    exact ⟨y, by rw [hy, mul_comm]⟩

  have hex : ∃ c ∈ J⁻¹, ∃ m, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = c * f.coeff m ∧ y ∉ v.asIdeal := by
    by_contra hne
    push Not at hne
    let S : Submodule (𝓞 K) K := Submodule.map (Algebra.linearMap (𝓞 K) K) v.asIdeal
    have hle : ((J * J⁻¹ : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) ≤ S := by
      rw [FractionalIdeal.coe_mul, Submodule.mul_le]
      intro j hj c hc
      have hJS : (J : Submodule (𝓞 K) K) ≤ S.comap (LinearMap.mulRight (𝓞 K) c) := by
        rw [hJdef, FractionalIdeal.spanFinset_coe, Submodule.span_le]
        rintro _ ⟨m, -, rfl⟩
        obtain ⟨y, hy⟩ := hint c hc m
        refine Submodule.mem_map.mpr ⟨y, hne c hc m y hy, ?_⟩
        simp only [Algebra.linearMap_apply, LinearMap.mulRight_apply]
        rw [hy, mul_comm]
      exact hJS hj
    have h1 : (1 : K) ∈ S := by
      apply hle
      rw [hJJ, FractionalIdeal.mem_coe, FractionalIdeal.mem_one_iff]
      exact ⟨1, map_one _⟩
    obtain ⟨y, hy, hy1⟩ := Submodule.mem_map.mp h1
    have : y = 1 := by
      apply IsFractionRing.injective (𝓞 K) K
      simpa using hy1
    rw [this] at hy
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr hy)
  obtain ⟨c, hc, m0, y0, hy0, hy0v⟩ := hex
  have hcoeffs : ((C c * f).coeffs : Set K) ⊆ Set.range (algebraMap (𝓞 K) K) := by
    intro a ha
    obtain ⟨m, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp ha
    obtain ⟨y, hy⟩ := hint c hc m
    exact ⟨y, by rw [hy, MvPolynomial.coeff_C_mul]⟩
  obtain ⟨g, hg⟩ := MvPolynomial.mem_range_map_iff_coeffs_subset.mpr hcoeffs
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hy0v
    have : algebraMap (𝓞 K) K y0 = 0 := by rw [hy0, zero_mul]
    rw [(IsFractionRing.injective (𝓞 K) K).eq_iff.mp (this.trans (map_zero _).symm)]
    exact zero_mem _
  refine ⟨c, g, hc0, hg, m0, ?_⟩
  have hgm : algebraMap (𝓞 K) K (g.coeff m0) = algebraMap (𝓞 K) K y0 := by
    rw [hy0, ← MvPolynomial.coeff_map, hg, MvPolynomial.coeff_C_mul]
  rwa [(IsFractionRing.injective (𝓞 K) K) hgm]

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PIncidenceNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

theorem IncidenceNull.proof : IncidenceNull.Statement := by
  intro F _ n k I f hf
  have hvan : ∀ j : Fin n, rename Sum.inr f * X (Sum.inl j) ∈
      MvPolynomial.vanishingIdeal F
        (MvPolynomial.zeroLocus (AlgebraicClosure F) (incIdeal I k)) := by
    intro j z hz
    have hI : ∀ g ∈ I, aeval (z ∘ Sum.inl) g = 0 := by
      intro g hg
      have hmem : rename Sum.inl g ∈ incIdeal I k :=
        Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hg)
      have h := hz _ hmem
      rwa [aeval_rename] at h
    have hlin : ∀ i : Fin k, ∑ j, (z ∘ Sum.inr) (i, j) * (z ∘ Sum.inl) j = 0 := by
      intro i
      have hmem : (∑ j, X (Sum.inr (i, j)) * X (Sum.inl j) :
          MvPolynomial (Fin n ⊕ (Fin k × Fin n)) F) ∈ incIdeal I k :=
        Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
      have h := hz _ hmem
      simpa using h
    rw [map_mul, aeval_rename, aeval_X]
    by_cases hx : z ∘ Sum.inl = 0
    · have h0 : z (Sum.inl j) = 0 := congrFun hx j
      rw [h0, mul_zero]
    · have hu : z ∘ Sum.inr ∈ incidence I k := ⟨z ∘ Sum.inl, hx, hI, hlin⟩
      rw [(hf.2 f).2 dvd_rfl _ hu, zero_mul]
  have hrad : ∀ j : Fin n, ∃ m, (rename Sum.inr f * X (Sum.inl j)) ^ m ∈ incIdeal I k := by
    intro j
    have h := hvan j
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical] at h
    exact h
  choose m hm using hrad
  exact ⟨Finset.univ.sup m, fun j =>
    Ideal.pow_mem_of_pow_mem _ (hm j) (Finset.le_sup (Finset.mem_univ j))⟩

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChartTorsion
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

namespace ChartTorsion

variable {D : Type} [CommRing D] {n : ℕ} (k : ℕ) (P : Ideal (MvPolynomial (Fin n) D)) (j : Fin n)

abbrev Base := Localization.Away (Ideal.Quotient.mk P (X j))

def toBase : MvPolynomial (Fin n) D →+* Base P j :=
  (algebraMap (MvPolynomial (Fin n) D ⧸ P) (Base P j)).comp (Ideal.Quotient.mk P)

def solve (i : Fin k) (m : Fin n) : MvPolynomial (Fin k × Fin n) (Base P j) :=
  if m = j then
    -(C (IsLocalization.Away.invSelf (Ideal.Quotient.mk P (X j))) *
      ∑ l ∈ Finset.univ.erase j, C (toBase P j (X l)) * X (i, l))
  else X (i, m)

def toChart : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) D →+* MvPolynomial (Fin k × Fin n) (Base P j) :=
  eval₂Hom (C.comp ((toBase P j).comp C))
    (Sum.elim (fun m => C (toBase P j (X m))) (fun im => solve k P j im.1 im.2))

theorem toChart_rename (p : MvPolynomial (Fin n) D) :
    toChart k P j (rename Sum.inl p) = C (toBase P j p) := by
  induction p using MvPolynomial.induction_on with
  | C d => simp [toChart]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p m hp => simp only [map_mul, hp, rename_X]; simp [toChart]

theorem incIdeal_le_ker : incIdeal P k ≤ RingHom.ker (toChart k P j) := by
  refine sup_le (Ideal.map_le_iff_le_comap.2 fun p hp => ?_)
    (Ideal.span_le.2 (Set.range_subset_iff.2 fun i => ?_))
  · show toChart k P j (rename Sum.inl p) = 0
    rw [toChart_rename]
    simp [toBase, Ideal.Quotient.eq_zero_iff_mem.2 hp]
  · show toChart k P j _ = 0
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_mul]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have hs : ∀ l ∈ Finset.univ.erase j,
        toChart k P j (X (Sum.inr (i, l))) * toChart k P j (X (Sum.inl l)) =
          C (toBase P j (X l)) * X (i, l) := by
      intro l hl
      simp [toChart, solve, Finset.ne_of_mem_erase hl, mul_comm]
    rw [Finset.sum_congr rfl hs]
    have h1 : C (IsLocalization.Away.invSelf (Ideal.Quotient.mk P (X j))) * C (toBase P j (X j)) =
        (1 : MvPolynomial (Fin k × Fin n) (Base P j)) := by
      rw [← C_mul, mul_comm, toBase, RingHom.comp_apply, IsLocalization.Away.mul_invSelf, C_1]
    simp only [toChart, eval₂Hom_X', Sum.elim_inl, Sum.elim_inr, solve, ↓reduceIte]
    linear_combination (-(∑ l ∈ Finset.univ.erase j, C (toBase P j (X l)) * X (i, l))) * h1

abbrev Loc := Localization.Away (Ideal.Quotient.mk (incIdeal P k) (X (Sum.inl j)))

def toLoc : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) D →+* Loc k P j :=
  (algebraMap _ (Loc k P j)).comp (Ideal.Quotient.mk (incIdeal P k))

theorem toLoc_mem {g : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) D} (hg : g ∈ incIdeal P k) :
    toLoc k P j g = 0 := by
  simp [toLoc, Ideal.Quotient.eq_zero_iff_mem.2 hg]

def quotToLoc : MvPolynomial (Fin n) D ⧸ P →+* Loc k P j :=
  Ideal.Quotient.lift P ((toLoc k P j).comp (rename Sum.inl).toRingHom) fun _ hp =>
    toLoc_mem k P j (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp))

theorem quotToLoc_mk (p : MvPolynomial (Fin n) D) :
    quotToLoc k P j (Ideal.Quotient.mk P p) = toLoc k P j (rename Sum.inl p) := rfl

theorem isUnit_quotToLoc : IsUnit (quotToLoc k P j (Ideal.Quotient.mk P (X j))) := by
  rw [quotToLoc_mk, rename_X]
  exact IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk (incIdeal P k) (X (Sum.inl j)))

def baseToLoc : Base P j →+* Loc k P j :=
  IsLocalization.Away.lift _ (isUnit_quotToLoc k P j)

theorem baseToLoc_toBase (p : MvPolynomial (Fin n) D) :
    baseToLoc k P j (toBase P j p) = toLoc k P j (rename Sum.inl p) := by
  simp [baseToLoc, toBase, quotToLoc_mk]

def back : MvPolynomial (Fin k × Fin n) (Base P j) →+* Loc k P j :=
  eval₂Hom (baseToLoc k P j) fun im => toLoc k P j (X (Sum.inr im))

theorem back_toChart (g : MvPolynomial (Fin n ⊕ (Fin k × Fin n)) D) :
    back k P j (toChart k P j g) = toLoc k P j g := by
  suffices h : (back k P j).comp (toChart k P j) = toLoc k P j from congrArg (· g) h
  apply MvPolynomial.ringHom_ext
  · intro d
    have := baseToLoc_toBase k P j (C d)
    simpa [back, toChart] using this
  · rintro (m | ⟨i, m⟩)
    · have := baseToLoc_toBase k P j (X m)
      simpa [back, toChart] using this
    · by_cases hm : m = j
      · subst hm
        have hinc : toLoc k P m (∑ l, X (Sum.inr (i, l)) * X (Sum.inl l)) = 0 :=
          toLoc_mem k P m (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m), map_add (f := _), map_sum] at hinc
        have hinv : baseToLoc k P m (IsLocalization.Away.invSelf (Ideal.Quotient.mk P (X m))) *
            toLoc k P m (X (Sum.inl m)) = 1 := by
          have e := baseToLoc_toBase k P m (X m)
          rw [rename_X] at e
          rw [← e, toBase, RingHom.comp_apply, ← map_mul, mul_comm, IsLocalization.Away.mul_invSelf,
            map_one]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [RingHom.comp_apply, toChart, eval₂Hom_X', Sum.elim_inr, solve, ↓reduceIte,
          back, map_neg, map_mul, map_sum, eval₂Hom_C, eval₂Hom_X', baseToLoc_toBase, rename_X]
        simp only [map_mul] at hinc
        set u := toLoc k P m (X (Sum.inr (i, m)))
        set xm := toLoc k P m (X (Sum.inl m))
        set inv := baseToLoc k P m (IsLocalization.Away.invSelf (Ideal.Quotient.mk P (X m)))
        have hS : ∑ l ∈ Finset.univ.erase m, toLoc k P m (X (Sum.inl l)) *
              toLoc k P m (X (Sum.inr (i, l))) =
            ∑ l ∈ Finset.univ.erase m, toLoc k P m (X (Sum.inr (i, l))) *
              toLoc k P m (X (Sum.inl l)) :=
          Finset.sum_congr rfl fun _ _ => mul_comm _ _
        rw [hS]
        linear_combination (-inv) * hinc + u * hinv
      · simp [back, toChart, solve, hm]

end ChartTorsion


open ChartTorsion in
theorem ChartTorsion.proof : ChartTorsion.Statement := by
  intro D _ _ n k P hP hPD c g hc hcg j
  by_cases hj : (X j : MvPolynomial (Fin n) D) ∈ P
  · refine ⟨1, Ideal.mul_mem_right _ _ (Ideal.mem_sup_left ?_)⟩
    simpa using Ideal.mem_map_of_mem (rename (R := D) (Sum.inl (β := Fin k × Fin n))) hj
  have hx : Ideal.Quotient.mk P (X j) ≠ 0 := fun h => hj (Ideal.Quotient.eq_zero_iff_mem.1 h)
  have hle : Submonoid.powers (Ideal.Quotient.mk P (X j)) ≤ nonZeroDivisors _ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hx
  have : IsDomain (Base P j) := IsLocalization.isDomain_localization hle
  have hcz : toChart k P j (C c) ≠ 0 := by
    simp only [toChart, eval₂Hom_C, RingHom.comp_apply, ne_eq, C_eq_zero, toBase]
    rw [map_eq_zero_iff _ (IsLocalization.injective (Base P j) hle)]
    intro h
    exact hc (hPD c (Ideal.Quotient.eq_zero_iff_mem.1 h))
  have hg0 : toChart k P j g = 0 := by
    have h := incIdeal_le_ker k P j hcg
    rw [RingHom.mem_ker, map_mul] at h
    exact (mul_eq_zero.1 h).resolve_left hcz
  have hl : toLoc k P j g = 0 := by
    rw [← back_toChart, hg0, map_zero]
  obtain ⟨⟨_, N, rfl⟩, hN⟩ := (IsLocalization.map_eq_zero_iff
    (Submonoid.powers (Ideal.Quotient.mk (incIdeal P k) (X (Sum.inl j)))) _ _).1 hl
  refine ⟨N, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
  simpa [map_mul, map_pow] using hN

end

end GroundTheory.Heights₂.Heights.Vertical
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormLength
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open Module

noncomputable section

section NormLength

variable {R B : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing B]
  [Algebra R B] [Module.Free R B] [Module.Finite R B]

theorem ord_prod {ι : Type*} (s : Finset ι) (a : ι → R) (ha : ∀ i ∈ s, a i ≠ 0) :
    Ring.ord R (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord R (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, Ring.ord_mul, ih fun i hi => ha i (by simp [hi])]
    exact mem_nonZeroDivisors_of_ne_zero
      (Finset.prod_ne_zero_iff.mpr fun i hi => ha i (by simp [hi]))

theorem ord_norm_eq_length {b : B} (hb : Function.Injective (fun x : B => b * x)) :
    Ring.ord R (Algebra.norm R b) = Module.length R (B ⧸ Ideal.span {b}) := by
  classical
  let bs := Module.Free.chooseBasis R B
  let ι := Module.Free.ChooseBasisIndex R B
  let N : Submodule R B := (Ideal.span {b}).restrictScalars R
  let m : B →ₗ[R] B := Algebra.lmul R B b
  have hm : Function.Injective m := hb
  have hrange : LinearMap.range m = N := by
    ext x
    simp only [LinearMap.mem_range, Submodule.restrictScalars_mem, Ideal.mem_span_singleton', N, m]
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, mul_comm y b⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, mul_comm b y⟩
  let φ : B ≃ₗ[R] N := (LinearEquiv.ofInjective m hm).trans (LinearEquiv.ofEq _ _ hrange)
  have h : Module.finrank R N = Module.finrank R B := φ.finrank_eq.symm
  let a := Submodule.smithNormalFormCoeffs bs h
  let b' := Submodule.smithNormalFormTopBasis bs h
  let ab := Submodule.smithNormalFormBotBasis bs h
  have ab_eq : ∀ i, (ab i : B) = a i • b' i := Submodule.smithNormalFormBotBasis_def bs h
  have ha : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero bs h

  have hlen : Module.length R (B ⧸ Ideal.span {b}) = ∑ i, Ring.ord R (a i) := by
    rw [← (Submodule.Quotient.restrictScalarsEquiv R (Ideal.span {b})).length_eq,
      (Submodule.quotientEquivPiSpan N bs h).length_eq, Module.length_pi_of_fintype]
    rfl

  let E : B ≃ₗ[R] N := b'.equiv ab (Equiv.refl ι)
  let D : B →ₗ[R] B := N.subtype ∘ₗ E.toLinearMap
  let u : B ≃ₗ[R] B := φ.trans E.symm
  have hmDu : m = D ∘ₗ u.toLinearMap := by
    ext x
    simp [D, u, φ]
  have hDb : ∀ j, D (b' j) = a j • b' j := fun j => by
    simp only [D, E, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      LinearEquiv.coe_coe, Basis.equiv_apply]
    exact ab_eq j
  have hD : LinearMap.toMatrix b' b' D = Matrix.diagonal a := by
    ext i j
    rw [LinearMap.toMatrix_apply, Matrix.diagonal_apply, hDb, map_smul, Basis.repr_self]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  have hdet : Algebra.norm R b = (∏ i, a i) * LinearMap.det (u : B →ₗ[R] B) := by
    rw [Algebra.norm_apply, show Algebra.lmul R B b = m from rfl, hmDu, LinearMap.det_comp,
      ← LinearMap.det_toMatrix b' D, hD, Matrix.det_diagonal]
  rw [hdet, Ring.ord_mul_of_isUnit_right (LinearEquiv.isUnit_det' u), ord_prod _ _ fun i _ => ha i,
    hlen]

end NormLength

theorem NormLength.proof : NormLength.Statement := by
  intro R B _ _ _ _ _ _ _ b hb
  exact ord_norm_eq_length hb

end

end GroundTheory.Heights₂.Heights.Vertical
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

theorem NormLength.full : NormLength.Statement := NormLength.proof
theorem VertTermEq.full : VertTermEq.Statement := VertTermEq.proof
theorem ParAlgIndep.full : ParAlgIndep.Statement := ParAlgIndep.proof
theorem NormFormEval.full : NormFormEval.Statement := NormFormEval.proof
theorem ChartTorsion.full : ChartTorsion.Statement := ChartTorsion.proof
theorem ChowFormHomog.full : ChowFormHomog.Statement := ChowFormHomog.proof
theorem IncidenceNull.full : IncidenceNull.Statement := IncidenceNull.proof
theorem LengthDecomp.full : LengthDecomp.Statement := LengthDecomp.proof
theorem NormFormLocalization.full : NormFormLocalization.Statement := NormFormLocalization.proof
theorem ParDVRIsDVR.full : ParDVRIsDVR.Statement := ParDVRIsDVR.proof
theorem ParFracIsFractionRing.full : ParFracIsFractionRing.Statement := ParFracIsFractionRing.proof
theorem PrimitiveScale.full : PrimitiveScale.Statement := PrimitiveScale.proof
theorem SecBGeneric.full : SecBGeneric.Statement := SecBGeneric.proof
theorem SecBFinite.full : SecBFinite.Statement :=
  SecBFinite.proof IncidenceNull.full ChartTorsion.full PrimitiveScale.full

end GroundTheory.Heights₂.Heights.Vertical
