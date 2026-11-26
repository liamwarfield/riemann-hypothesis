module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HeightLowerBoundChartNorm
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsVerticalBound
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitCenterChart
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitConjSum
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.POrbitChartMult
public import GroundTheory.HeightsAndTheta.Heights.HeightComparison.PPlaceCentredSum
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveDegree

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AmpleLineBundles.PtsIntegralMap
section -- merged from Development.WeilBound.CoreStatements.AmpleLineBundles.HeightRecRFull
namespace CoverDenseAlt
open GroundTheory.Heights₂.Heights

theorem heightRecR_full : HeightRecR.Statement :=
  have hM : OrbitChartMax.Statement := OrbitChartMax.proof
  have hQ : OrbitChartQuot.Statement := OrbitChartQuot.proof
  have hIff : OrbitCenterMemIff.Statement := OrbitCenterMemIff.proof
  HeightRecR.proof OrbitDivVertical.proof
    (OrbitFiniteSum.proof OrbitDegreeRatio.proof
      (OrbitLocalSum.proof OrbitChartRing.proof hM
        (OrbitChartResidue.proof hM hQ (OrbitChartDehom.proof hM hQ))
        OrbitChartMult.proof
        (LocalLengthPlaces.proof LocalQuotCard.proof CentredPlacesFinite.proof
          (LocalQuotCentred.proof CentredRingNormal.proof LocalNormalIndex.proof) PlacesRingQuot.proof)
        OrbitCenterChart.proof PlaceCentredSum.proof OrbitChartTerm.proof)
      (OrbitCenterZero.proof OrbitCenterLe.proof hIff
        (OrbitCenterDivSupp.proof hIff (OrbitCenterPrime.proof hIff) SubringPrimeMaximal.proof)))
    (OrbitArchSum.of_conjSum OrbitConjSum.proof)

theorem chartDehom_full : OrbitChartDehom.Statement :=
  OrbitChartDehom.proof OrbitChartMax.proof OrbitChartQuot.proof

end CoverDenseAlt
end

noncomputable section

namespace CoverDenseAlt.Rename₂

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights

variable {K : Type} [Fintype K] {ι ι' : K → Type} [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)]
  (e : ∀ k, ι k ≃ ι' k)

def ren : MRing ι ≃+* MRing ι' := (renameEquiv ℤ (Equiv.sigmaCongrRight e)).toRingEquiv

omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem ren_apply (f : MRing ι) : ren e f = rename (Equiv.sigmaCongrRight e) f := rfl

omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem ren_X (k : K) (i : ι k) : ren e (X ⟨k, i⟩) = X ⟨k, e k i⟩ := by
  rw [ren_apply, rename_X]
  rfl

omit [Fintype K] in
theorem homog_ren {g : MRing ι} {a : K → ℕ} (hg : IsMultiHomog g a) : IsMultiHomog (ren e g) a := by
  classical
  intro m hm k
  rw [ren_apply, support_rename_of_injective (Equiv.sigmaCongrRight e).injective, Finset.mem_image] at hm
  obtain ⟨m0, hm0, rfl⟩ := hm
  have h1 : ∀ i : ι' k, Finsupp.mapDomain (Equiv.sigmaCongrRight e) m0 ⟨k, i⟩ = m0 ⟨k, (e k).symm i⟩ := by
    intro i
    have : (⟨k, i⟩ : Σ k, ι' k) = Equiv.sigmaCongrRight e ⟨k, (e k).symm i⟩ := by simp
    rw [this, Finsupp.mapDomain_apply_of_injective (Equiv.sigmaCongrRight e).injective]
  simp only [h1]
  rw [Equiv.sum_comp (e k).symm (fun j => m0 ⟨k, j⟩)]
  exact hg m0 hm0 k

omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem relevant_iff (V : Ideal (MRing ι)) : IsRelevant (V.map (ren e)) ↔ IsRelevant V := by
  refine forall_congr' fun k => ⟨?_, ?_⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ := (e k).surjective i
    exact ⟨j, by rwa [← ren_X, mem_map_ringEquiv_iff] at hi⟩
  · rintro ⟨j, hj⟩
    exact ⟨e k j, by rwa [← ren_X, mem_map_ringEquiv_iff]⟩

omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem comap_C (V : Ideal (MRing ι)) :
    (V.map (ren e)).comap (C : ℤ →+* MRing ι') = V.comap (C : ℤ →+* MRing ι) := by
  ext n
  rw [Ideal.mem_comap, Ideal.mem_comap, ← mem_map_ringEquiv_iff (ren e) V, ren_apply, rename_C]

omit [Fintype K] in
theorem homogIdeal_map {V : Ideal (MRing ι)} (h : IsMultiHomogIdeal V) : IsMultiHomogIdeal (V.map (ren e)) := by
  obtain ⟨S, hS, rfl⟩ := h
  refine ⟨ren e '' S, ?_, Ideal.map_span _ _⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨a, homog_ren e ha⟩

theorem arithVar_map {V : Ideal (MRing ι)} {d : ℕ} (h : IsArithVar V d) : IsArithVar (V.map (ren e)) d := by
  obtain ⟨hne, ⟨hp, hh, hr⟩, hhor, hdim⟩ := h
  refine ⟨hne, ⟨(isPrime_map_ringEquiv_iff _ V).2 hp, homogIdeal_map e hh, (relevant_iff e V).2 hr⟩, ?_, ?_⟩
  · unfold IsHorizontal
    rw [comap_C]
    exact hhor
  · rw [ringKrullDim_quotient_map, hdim]

omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem sup_map (V : Ideal (MRing ι)) (s : MRing ι) :
    V.map (ren e) ⊔ Ideal.span {ren e s} = (V ⊔ Ideal.span {s}).map (ren e) := by
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]

omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem divSupp_map (V : Ideal (MRing ι)) (s : MRing ι) :
    divSupp (V.map (ren e)) (ren e s) = Ideal.map (ren e) '' divSupp V s := by
  ext W'
  simp only [divSupp, Set.mem_setOf_eq, Set.mem_image, sup_map, minimalPrimes_map_ringEquiv]
  constructor
  · rintro ⟨⟨W, hW, rfl⟩, hrel⟩
    exact ⟨W, ⟨hW, (relevant_iff e W).1 hrel⟩, rfl⟩
  · rintro ⟨W, ⟨hW, hrel⟩, rfl⟩
    exact ⟨⟨W, hW, rfl⟩, (relevant_iff e W).2 hrel⟩

omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem multAt_map (J V : Ideal (MRing ι)) : multAt (J.map (ren e)) (V.map (ren e)) = multAt J V := by
  unfold multAt
  by_cases hV : V.IsPrime
  · have hV' : (V.map (ren e)).IsPrime := (isPrime_map_ringEquiv_iff (ren e) V).2 hV
    rw [dite_eq_left hV, dite_eq_left hV']
    exact congrArg ENat.toNat (length_localizedModule_quotient_map (ren e) J V)
  · have hV' : ¬ (V.map (ren e)).IsPrime := fun h' => hV ((isPrime_map_ringEquiv_iff (ren e) V).1 h')
    rw [dite_eq_right hV, dite_eq_right hV']

def chartId (V : Ideal (MRing ι)) (c : ∀ k, ι k) : Ideal (MRing ι) :=
  V ⊔ Ideal.span (Set.range fun k => (X ⟨k, c k⟩ : MRing ι) - 1)

omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem chartId_map (V : Ideal (MRing ι)) (c : ∀ k, ι k) :
    (chartId V c).map (ren e) = chartId (V.map (ren e)) fun k => e k (c k) := by
  unfold chartId
  rw [Ideal.map_sup, Ideal.map_span, ← Set.range_comp]
  congr 3
  funext k
  simp [ren_X]

theorem geoNum_map (V : Ideal (MRing ι)) (hV : IsRelevant V) (a b : Fin 0 → K → ℤ)
    (hc : ∀ c c' : ∀ k, ι' k, (∀ k, (X ⟨k, c k⟩ : MRing ι') ∉ V.map (ren e)) →
      (∀ k, (X ⟨k, c' k⟩ : MRing ι') ∉ V.map (ren e)) →
      Nonempty ((MRing ι' ⧸ chartId (V.map (ren e)) c) ≃+* (MRing ι' ⧸ chartId (V.map (ren e)) c'))) :
    geoNum 0 (V.map (ren e)) a = geoNum 0 V b := by
  have hV' := (relevant_iff e V).2 hV
  have h1 : geoNum 0 V b = ((Module.length ℤ (MRing ι ⧸ chartId V fun k => (hV k).choose)).toNat : ℤ) := by
    simp only [geoNum]
    rw [dite_eq_left hV]
    rfl
  have h2 : geoNum 0 (V.map (ren e)) a =
      ((Module.length ℤ (MRing ι' ⧸ chartId (V.map (ren e)) fun k => (hV' k).choose)).toNat : ℤ) := by
    simp only [geoNum]
    rw [dite_eq_left hV']
    rfl
  obtain ⟨φ⟩ := hc (fun k => (hV' k).choose) (fun k => e k (hV k).choose) (fun k => (hV' k).choose_spec)
    (fun k => by
      rw [← ren_X, mem_map_ringEquiv_iff]
      exact (hV k).choose_spec)
  rw [h1, h2, φ.toAddEquiv.toIntLinearEquiv.length_eq, ← chartId_map, length_int_quotient_map]

def pull {F : Type} (z : (Σ k, ι' k) → F) : (Σ k, ι k) → F := fun p => z ⟨p.1, e p.1 p.2⟩

omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem eval_ren (z : (Σ k, ι' k) → ℂ) (f : MRing ι) :
    eval z (map (Int.castRingHom ℂ) (ren e f)) = eval (pull e z) (map (Int.castRingHom ℂ) f) := by
  rw [ren_apply, map_rename, eval_rename]
  rfl

omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem nz_pull {F : Type} [Zero F] (z : (Σ k, ι' k) → F) :
    (∀ k, ∃ i, pull e z ⟨k, i⟩ ≠ 0) ↔ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
  refine forall_congr' fun k => ⟨?_, ?_⟩
  · rintro ⟨i, hi⟩
    exact ⟨e k i, hi⟩
  · rintro ⟨i, hi⟩
    obtain ⟨j, rfl⟩ := (e k).surjective i
    exact ⟨j, hi⟩

omit [Fintype K] [∀ k, Fintype (ι k)] [∀ k, Fintype (ι' k)] in
theorem mem_mcPts (V : Ideal (MRing ι)) (z : (Σ k, ι' k) → ℂ) :
    z ∈ mcPts (V.map (ren e)) ↔ pull e z ∈ mcPts V := by
  refine and_congr (nz_pull e z).symm ⟨fun h f hf => ?_, fun h f hf => ?_⟩
  · rw [← eval_ren]
    exact h _ ((mem_map_ringEquiv_iff _ V f).2 hf)
  · obtain ⟨g, rfl⟩ := (ren e).surjective f
    rw [eval_ren]
    exact h _ ((mem_map_ringEquiv_iff _ V g).1 hf)

def ptsEquiv (V : Ideal (MRing ι)) : mcPts (V.map (ren e)) ≃ mcPts V where
  toFun z := ⟨pull e z.1, (mem_mcPts e V z.1).1 z.2⟩
  invFun z := ⟨fun p => z.1 ⟨p.1, (e p.1).symm p.2⟩, (mem_mcPts e V _).2 (by
    have : pull e (fun p : Σ k, ι' k => z.1 ⟨p.1, (e p.1).symm p.2⟩) = z.1 := by
      funext p
      simp [pull]
    rw [this]
    exact z.2)⟩
  left_inv z := by
    apply Subtype.ext
    funext p
    simp [pull]
  right_inv z := by
    apply Subtype.ext
    funext p
    simp [pull]

def projEquiv (V : Ideal (MRing ι)) : projPts (V.map (ren e)) ≃ projPts V :=
  Quot.congr (ptsEquiv e V) fun z z' => by
    refine exists_congr fun c => and_congr Iff.rfl ⟨fun h => ?_, fun h => ?_⟩
    · funext p
      exact congrFun h ⟨p.1, e p.1 p.2⟩
    · funext ⟨k, i⟩
      obtain ⟨j, rfl⟩ := (e k).surjective i
      exact congrFun h ⟨k, j⟩

theorem degC_map (V : Ideal (MRing ι)) : degC (V.map (ren e)) = degC V :=
  Nat.card_congr (projEquiv e V)

theorem out_eq (V : Ideal (MRing ι)) (g : ((Σ k, ι k) → ℂ) → ℝ)
    (hg : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → z ∈ mcPts V → g (fun p => c p.1 * z p) = g z)
    (z : mcPts V) : g (Quot.out (Quot.mk _ z : projPts V) : mcPts V) = g z := by
  let G : projPts V → ℝ := Quot.lift (fun z : mcPts V => g z) (by
    rintro z z' ⟨c, hc, h⟩
    rw [h, hg c z hc z.2])
  have h1 : ∀ w : mcPts V, g w = G (Quot.mk _ w) := fun _ => rfl
  rw [h1, h1, Quot.out_eq]

theorem ptsIntegral_map [Nonempty K] (V : Ideal (MRing ι)) (hV : IsMultiHomogIdeal V)
    (hfin : Finite (projPts V)) (g : ((Σ k, ι k) → ℂ) → ℝ) (g' : ((Σ k, ι' k) → ℂ) → ℝ)
    (hg : ∀ (c : K → ℂ) (z : (Σ k, ι' k) → ℂ), (∀ k, c k ≠ 0) → z ∈ mcPts (V.map (ren e)) →
      g' (fun p => c p.1 * z p) = g' z)
    (hgg : ∀ z ∈ mcPts (V.map (ren e)), g' z = g (pull e z)) :
    ptsIntegral (V.map (ren e)) (Fin.elim0 : Fin 0 → ((Σ k, ι' k) → ℂ) → ℝ) g' =
      ptsIntegral V (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) g := by
  have hg0 : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → z ∈ mcPts V →
      g (fun p => c p.1 * z p) = g z := by
    intro c z hc hz
    obtain ⟨z', hz'⟩ := (ptsEquiv e V).surjective ⟨z, hz⟩
    have hz'' : pull e z'.1 = z := congrArg Subtype.val hz'
    have hmem : (fun p : Σ k, ι' k => c p.1 * z'.1 p) ∈ mcPts (V.map (ren e)) := by
      obtain ⟨S, hS, hVS⟩ := homogIdeal_map e hV
      refine ⟨fun k => ?_, fun f hf => ?_⟩
      · obtain ⟨i, hi⟩ := z'.2.1 k
        exact ⟨i, mul_ne_zero (hc k) hi⟩
      · have hle : Ideal.span S ≤ RingHom.ker ((eval fun p : Σ k, ι' k => c p.1 * z'.1 p).comp
            (map (Int.castRingHom ℂ))) := by
          refine Ideal.span_le.2 fun t ht => ?_
          obtain ⟨a, ha⟩ := hS t ht
          have h0 := z'.2.2 t (hVS ▸ Ideal.subset_span ht)
          change eval _ (map _ t) = 0
          rw [eval_map, eval₂_eq'] at h0 ⊢
          have : ∀ m ∈ t.support, (Int.castRingHom ℂ) (AddMonoidAlgebra.coeff t m) * ∏ p : Σ k, ι' k, (c p.1 * z'.1 p) ^ m p =
              (∏ k, c k ^ a k) * ((Int.castRingHom ℂ) (AddMonoidAlgebra.coeff t m) * ∏ p, z'.1 p ^ m p) := by
            intro m hm
            have h1 : ∏ p : Σ k, ι' k, c p.1 ^ m p = ∏ k, c k ^ a k := by
              rw [Fintype.prod_sigma]
              refine Finset.prod_congr rfl fun k _ => ?_
              show ∏ i, c k ^ m ⟨k, i⟩ = _
              rw [Finset.prod_pow_eq_pow_sum, ha m hm k]
            simp only [mul_pow, Finset.prod_mul_distrib, h1]
            ring
          rw [Finset.sum_congr rfl this, ← Finset.mul_sum, h0, mul_zero]
        exact hle (hVS ▸ hf)
    rw [← hz'', ← hgg _ z'.2, ← hg c _ hc z'.2, hgg _ hmem]
    rfl
  haveI := hfin
  rw [PtsIntegralPoints.homogProof K ι V g hV hfin hg0,
    PtsIntegralPoints.homogProof K ι' _ g' (homogIdeal_map e hV) (Finite.of_equiv _ (projEquiv e V).symm) hg,
    ← finsum_comp_equiv (projEquiv e V)]
  refine finsum_congr fun q => ?_
  induction q using Quot.ind with
  | mk z =>
    rw [out_eq _ g' hg z, hgg _ z.2]
    exact (out_eq V g hg0 (ptsEquiv e V z)).symm

theorem recR_map [Nonempty K] (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ)
    (I' : Ideal (MRing ι') → (n : ℕ) → (Fin n → HermLine ι') → ℝ)
    (W : Ideal (MRing ι)) (hW : IsMultiHomogIdeal W) (hfin : Finite (projPts W))
    (A : HermLine ι) (A' : HermLine ι') (s : MRing ι)
    (hinv : ∀ (c : K → ℂ) (z : (Σ k, ι' k) → ℂ), (∀ k, c k ≠ 0) → z ∈ mcPts (W.map (ren e)) →
      logNorm A' (ren e s) (fun p => c p.1 * z p) = logNorm A' (ren e s) z)
    (hA : ∀ z, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → A'.h z = A.h (pull e z))
    (hvert : ∀ V ∈ divSupp (W.map (ren e)) (ren e s), ¬ IsHorizontal V)
    (hc : ∀ V ∈ divSupp (W.map (ren e)) (ren e s), ∀ c c' : ∀ k, ι' k, (∀ k, (X ⟨k, c k⟩ : MRing ι') ∉ V) →
      (∀ k, (X ⟨k, c' k⟩ : MRing ι') ∉ V) → Nonempty ((MRing ι' ⧸ chartId V c) ≃+* (MRing ι' ⧸ chartId V c'))) :
    recR I' (W.map (ren e)) (Fin.elim0 : Fin 0 → HermLine ι') A' (ren e s) =
      recR I W (Fin.elim0 : Fin 0 → HermLine ι) A s := by
  unfold recR
  congr 1
  · rw [divSupp_map] at hvert hc ⊢
    rw [finsum_mem_image (map_ringEquiv_injective (ren e)).injOn]
    refine finsum_mem_congr rfl fun V hV => ?_
    have h1 := hvert _ ⟨V, hV, rfl⟩
    have h2 : ¬ IsHorizontal V := by
      intro h
      apply h1
      unfold IsHorizontal
      rw [comap_C]
      exact h
    have h3 : charOf (V.map (ren e)) = charOf V := by simp only [charOf, comap_C]
    rw [if_neg h1, if_neg h2, sup_map, multAt_map, h3, geoNum_map e V hV.2 _ _ (hc _ ⟨V, hV, rfl⟩)]
  · have e0 : (fun j z => Real.log (((Fin.elim0 : Fin 0 → HermLine ι) j).h z)) =
        (Fin.elim0 : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) := funext fun j => j.elim0
    have e1 : (fun j z => Real.log (((Fin.elim0 : Fin 0 → HermLine ι') j).h z)) =
        (Fin.elim0 : Fin 0 → ((Σ k, ι' k) → ℂ) → ℝ) := funext fun j => j.elim0
    rw [arInt, arInt, e0, e1]
    refine ptsIntegral_map e W hW hfin _ _ hinv fun z hz => ?_
    rw [logNorm, logNorm, eval_ren, hA z hz.1]

end CoverDenseAlt.Rename₂
end
end

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

noncomputable section

namespace CoverDenseAlt.HtF

open CoverDenseAlt.Rename₂
open GroundTheory.Heights₂.Heights (blockIdx flatCone unflatCone Cone BlockNonzero orbitIdeal coordField coordVec height
  blockNonzero_unflatCone_iff chartMonomial)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def stdLine (m : K → ℕ) : HermLine ι where
  a k := ((2 * m k : ℕ) : ℤ)
  h z := ∏ k, (∑ i, ‖z ⟨k, i⟩‖ ^ 2) ^ m k
  pos z hz := Finset.prod_pos fun k _ => pow_pos (by
    obtain ⟨i, hi⟩ := hz k
    exact Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hi) 2⟩) _
  smul c z _ := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    simp only [norm_mul, mul_pow, zpow_natCast]
    rw [← Finset.mul_sum, mul_pow, pow_mul]

theorem stdLine_smooth (m : K → ℕ) : IsSmoothHerm (stdLine (ι := ι) m) := by
  refine ContDiff.contDiffOn ?_
  refine contDiff_prod fun k _ => ContDiff.pow (ContDiff.sum fun i _ => ?_) _
  exact (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ (fun _ => ℂ) (⟨k, i⟩ : Σ k, ι k))

theorem tensor_smooth {A B : HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) :
    IsSmoothHerm (A.tensor B) := ContDiffOn.mul hA hB

theorem lineHt_tensor (A B : HermLine ι) (L : Type) [Field L] [NumberField L] (w : (Σ k, ι k) → L)
    (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) : lineHt (A.tensor B) L w = lineHt A L w + lineHt B L w := by
  have hA := SecLow.support_finite w hw fun k => (A.a k : ℝ)
  have hB := SecLow.support_finite w hw fun k => (B.a k : ℝ)
  have hfin : (∑ᶠ v : FinitePlace L, ∑ k, ((A.tensor B).a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))) =
      (∑ᶠ v : FinitePlace L, ∑ k, (A.a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩))) +
      ∑ᶠ v : FinitePlace L, ∑ k, (B.a k : ℝ) * Real.log (⨆ i, v (w ⟨k, i⟩)) := by
    rw [← finsum_add_distrib hA hB]
    refine finsum_congr fun v => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [HermLine.tensor, Pi.add_apply, Int.cast_add]
    ring
  have hinf : (∑ σ : L →+* ℂ, Real.log ((A.tensor B).h fun p => σ (w p))) =
      (∑ σ : L →+* ℂ, Real.log (A.h fun p => σ (w p))) + ∑ σ : L →+* ℂ, Real.log (B.h fun p => σ (w p)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hz : ∀ k, ∃ i, (fun p => σ (w p)) ⟨k, i⟩ ≠ 0 := fun k =>
      let ⟨i, hi⟩ := hw k; ⟨i, (map_ne_zero σ).2 hi⟩
    exact Real.log_mul (A.pos _ hz).ne' (B.pos _ hz).ne'
  unfold lineHt ptHt
  beta_reduce
  rw [hfin, hinf]
  ring

variable [DecidableEq K] {n : K → ℕ} (e : ∀ k, ι k ≃ blockIdx n k)

def toNum (A : HermLine ι) (hA : IsSmoothHerm A) : GroundTheory.Heights₂.Heights.HermLine n where
  deg := A.a
  metric z := A.h (pull e (flatCone z))
  metric_pos z hz := A.pos _ ((nz_pull e _).2 ((blockNonzero_unflatCone_iff (flatCone z)).1 hz))
  metric_smul c z hc _ := A.smul c (pull e (flatCone z)) hc
  metric_smooth := by
    have hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Cone n ℂ => pull e (flatCone z)) :=
      contDiff_pi.2 fun p => contDiff_pi.1 (contDiff_pi.1 contDiff_id p.1) (e p.1 p.2)
    exact ContDiffOn.comp hA hu.contDiffOn fun z hz =>
      (nz_pull e _).2 ((blockNonzero_unflatCone_iff (flatCone z)).1 hz)

theorem height_toNum (A : HermLine ι) (hA : IsSmoothHerm A) (x : Cone n (AlgebraicClosure ℚ)) :
    height (toNum e A hA) x = lineHt A (coordField x) (pull e (flatCone (coordVec x))) := by
  have h : ∀ (v : FinitePlace (coordField x)) (k : K),
      (⨆ i, v (coordVec x k i)) = ⨆ i, v (pull e (flatCone (coordVec x)) ⟨k, i⟩) :=
    fun v k => ((e k).iSup_comp (g := fun i => v (coordVec x k i))).symm
  unfold height lineHt ptHt
  simp only [h]
  rfl

omit [DecidableEq K] in
theorem coordIdeal_eq (x : Cone n (AlgebraicClosure ℚ)) (f : MRing ι) :
    f ∈ mCoordIdeal (pull e (flatCone (coordVec x))) ↔ ren e f ∈ orbitIdeal x := by
  classical
  have key : (MvPolynomial.map (algebraMap (coordField x) (AlgebraicClosure ℚ))).comp
      (mConeMap (pull e (flatCone (coordVec x)))).toRingHom =
      (mConeMap (flatCone x)).toRingHom.comp (ren e).toRingHom := by
    refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => ?_
    simp [mConeMap, ren, pull, flatCone, coordVec]
  have hf : MvPolynomial.map (algebraMap (coordField x) (AlgebraicClosure ℚ))
      (mConeMap (pull e (flatCone (coordVec x))) f) = mConeMap (flatCone x) (ren e f) :=
    RingHom.congr_fun key f
  simp only [mCoordIdeal, orbitIdeal, RingHom.mem_ker]
  constructor
  · intro h
    rw [← hf, h, map_zero]
  · intro h
    refine MvPolynomial.map_injective _ (algebraMap (coordField x) (AlgebraicClosure ℚ)).injective ?_
    rw [hf, h, map_zero]

end CoverDenseAlt.HtF

open CoverDenseAlt.Rename₂ CoverDenseAlt.HtF in
open GroundTheory.Heights₂.Heights (blockIdx flatCone unflatCone Cone BlockNonzero orbitIdeal coordField coordVec height
  blockNonzero_unflatCone_iff chartMonomial) in
theorem CoverDenseAlt.intersection_number_eq_line_height : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (II : IntersectionSystem), IsIntersectionSystem II → ∀ W : Ideal (MRing ι), IsArithVar W 1 → ∃ (L : Type) (_ : Field L) (_ : NumberField L) (w : (Σ k, ι k) → L), W = mCoordIdeal w ∧ w ∈ ptsOver L W ∧ ∀ A : HermLine ι, IsSmoothHerm A → II K ι W 1 ![A] / (degC W : ℝ) = lineHt A L w := by
  intro K _ ι _ II hII W hW
  classical
  obtain ⟨hK, ⟨-, hhomW, hrelW⟩, -, -⟩ := id hW
  haveI := hK
  obtain ⟨-, hadd, hrec⟩ : IsIntersectionFamily (II K ι) := hII K ι
  have hne : ∀ k, Nonempty (ι k) := fun k => let ⟨i, _⟩ := hrelW k; ⟨i⟩
  obtain ⟨n, hn⟩ : ∃ n : K → ℕ, ∀ k, Fintype.card (ι k) = n k + 1 :=
    ⟨fun k => Fintype.card (ι k) - 1, fun k => by
      have := Fintype.card_pos_iff.2 (hne k)
      show Fintype.card (ι k) = Fintype.card (ι k) - 1 + 1
      omega⟩
  obtain ⟨e⟩ : Nonempty (∀ k, ι k ≃ blockIdx n k) :=
    ⟨fun k => (Fintype.equivFin (ι k)).trans (finCongr (hn k))⟩
  obtain ⟨x, hx, hWx⟩ := GroundTheory.Heights₂.Heights.CurveIsOrbit.full K n (Ideal.map (ren e) W) (arithVar_map e hW)
  have hxc : ∀ k, ∃ i, x k i ≠ 0 := fun k => by
    by_contra h
    push_neg at h
    exact hx k (funext h)
  choose c hc using hxc
  have hdeg : degC W = degC (orbitIdeal x) := by rw [← hWx, degC_map]
  have hdpos : 0 < degC W := hdeg ▸ GroundTheory.Heights₂.Heights.OrbitDegree.full K n x hx
  have hfin : Finite (GroundTheory.Heights₂.Heights.projPts W) :=
    Nat.finite_of_card_ne_zero (by rw [← GroundTheory.Heights₂.Heights.degC_eq_card_projPts]; omega)
  have hWeq : W = mCoordIdeal (pull e (flatCone (coordVec x))) := by
    ext f
    rw [coordIdeal_eq e x f, ← hWx]
    constructor
    · exact fun h => Ideal.mem_map_of_mem _ h
    · intro h
      rw [Ideal.mem_map_of_equiv] at h
      obtain ⟨g, hg, hge⟩ := h
      rwa [← (ren e).injective hge]
  have hwnz : ∀ k, ∃ i, pull e (flatCone (coordVec x)) ⟨k, i⟩ ≠ 0 := fun k =>
    ⟨(e k).symm (c k), fun h => hc k (by
      have h' := congrArg (fun y : coordField x => (y : AlgebraicClosure ℚ)) h
      simpa [pull, flatCone, coordVec] using h')⟩
  have hsnoc : ∀ B : HermLine ι, (Fin.snoc (Fin.elim0 : Fin 0 → HermLine ι) B : Fin 1 → HermLine ι) = ![B] :=
    fun B => by
      funext i
      fin_cases i
      rfl
  have key : ∀ A : HermLine ι, IsSmoothHerm A → ∀ a : K → ℕ, (∀ k, A.a k = a k) →
      II K ι W 1 ![A] = degC W * lineHt A (coordField x) (pull e (flatCone (coordVec x))) := by
    intro A hA a ha
    have hsec : IsSectionOn (orbitIdeal x) (toNum e A hA).toGeo (chartMonomial c a) :=
      GroundTheory.Heights₂.Heights.isSectionOn_chartMonomial (toNum e A hA) x c hc a ha
    obtain ⟨a0, ha0, hhom', hnot'⟩ := id hsec
    obtain ⟨s, hsdef⟩ : ∃ s : MRing ι, s = ren (fun k => (e k).symm) (chartMonomial c a) := ⟨_, rfl⟩
    have hid : (⇑(Equiv.sigmaCongrRight e) ∘ ⇑(Equiv.sigmaCongrRight fun k => (e k).symm)) = id :=
      funext fun p => by simp
    have hs : ren e s = chartMonomial c a := by
      rw [hsdef, ren_apply, ren_apply, rename_rename, hid, rename_id]
      rfl
    have hsW : s ∉ W := by
      intro hmem
      apply hnot'
      rw [← hWx, ← hs]
      exact Ideal.mem_map_of_mem _ hmem
    have hhom : IsMultiHomog s a0 := by
      rw [hsdef]
      exact homog_ren _ hhom'
    have h0 : II K ι W 1 ![A] = recR (II K ι) W Fin.elim0 A s := by
      have := hrec W 0 Fin.elim0 A s a0 hW (fun j => j.elim0) hA ha0 hhom hsW
      simpa only [hsnoc] using this
    have h1 : ∀ (c' : K → ℂ) (z : (k : K) × blockIdx n k → ℂ), (∀ k, c' k ≠ 0) →
        z ∈ mcPts (Ideal.map (ren e) W) →
        (logNorm (toNum e A hA).toGeo (ren e s) fun p => c' p.fst * z p) =
          logNorm (toNum e A hA).toGeo (ren e s) z := by
      intro c' z hc' _
      rw [hs]
      unfold logNorm
      have hprod : (∏ k, ‖c' k‖ ^ ((toNum e A hA).toGeo.a k)) = ∏ k, ‖c' k‖ ^ a0 k :=
        Finset.prod_congr rfl fun k _ => by rw [ha0 k, zpow_natCast]
      have hpos : (∏ k, ‖c' k‖ ^ a0 k) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (norm_ne_zero_iff.2 (hc' k))
      rw [GroundTheory.Heights₂.Heights.eval_smul_of_isMultiHomog _ a0 hhom' c' z,
        (toNum e A hA).toGeo.smul c' z hc', hprod, norm_mul, norm_prod]
      simp only [norm_pow]
      rw [mul_div_mul_left _ _ hpos]
    have h2 : ∀ z : (k : K) × blockIdx n k → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
        (toNum e A hA).toGeo.h z = A.h (pull e z) := by
      intro z hz
      rw [GroundTheory.Heights₂.Heights.HermLine.toGeo_h_of_blockNonzero (toNum e A hA)
        ((blockNonzero_unflatCone_iff z).2 hz)]
      rfl
    have h3 : ∀ V ∈ divSupp (Ideal.map (ren e) W) (ren e s), ¬IsHorizontal V := by
      intro V hV
      rw [hs, hWx] at hV
      exact GroundTheory.Heights₂.Heights.OrbitDivVertical.proof K n (toNum e A hA) x _ hx hsec V hV
    have h4 : ∀ V ∈ divSupp (Ideal.map (ren e) W) (ren e s), ∀ (c1 c2 : (k : K) → blockIdx n k),
        (∀ k, X ⟨k, c1 k⟩ ∉ V) → (∀ k, X ⟨k, c2 k⟩ ∉ V) →
        Nonempty (MRing (blockIdx n) ⧸ chartId V c1 ≃+* MRing (blockIdx n) ⧸ chartId V c2) :=
      open GroundTheory.Heights₂.Heights in by
      intro V hV c1 c2 hc1 hc2
      have hvertical := h3 V hV
      rw [hs, hWx] at hV
      have hVprime : V.IsPrime := hV.1.1.1
      have hWV : orbitIdeal x ≤ V := le_sup_left.trans hV.1.1.2
      have hVh : ∀ f ∈ V, ∀ b, weightedHomogeneousComponent (coordDeg n) b f ∈ V :=
        fun _ hf b => weightedHomogeneousComponent_mem_of_mem_divSupp x
          ((geoMultiHomog_iff _ a0).mp hhom') hV hf b
      have hfield (d : (k : K) → blockIdx n k) (hd : ∀ k, X ⟨k, d k⟩ ∉ V) :
          IsField (dehomFrac V d).range := by
        have hxd : ∀ k, x k (d k) ≠ 0 := by
          intro k hxk
          apply hd k (hWV ?_)
          rw [orbitIdeal, mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X]
          simp [flatCone, hxk]
        obtain ⟨eQ⟩ := OrbitChartQuot.proof K n x d hxd V hWV
        let eRange := eQ.trans (quotEquivRange hVh hd)
        have hprime : (chartPoint x d V).IsPrime :=
          (Ideal.Quotient.isDomain_iff_prime _).mp (Function.Injective.isDomain eRange eRange.injective)
        have hne : chartPoint x d V ≠ ⊥ := by
          intro hbot
          apply hvertical
          refine le_antisymm (fun m hm => Ideal.mem_bot.mpr ?_) bot_le
          have hmem : chartEval x d (C m) ∈ chartPoint x d V := Ideal.mem_map_of_mem _ hm
          rw [hbot, Ideal.mem_bot] at hmem
          simpa using hmem
        have hmax := SubringPrimeMaximal.proof (ratioField x) _ _ hprime hne
        exact MulEquiv.isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp hmax)
          eRange.symm.toMulEquiv
      have hr : (dehomFrac V c1).range = (dehomFrac V c2).range :=
        le_antisymm (range_dehomFrac_le hc2 hc1 (hfield c2 hc2))
          (range_dehomFrac_le hc1 hc2 (hfield c1 hc1))
      exact ⟨(quotEquivRange hVh hc1).trans
        ((Subalgebra.equivOfEq _ _ hr).toRingEquiv.trans (quotEquivRange hVh hc2).symm)⟩
    rw [h0, ← recR_map e (II K ι) (II K (blockIdx n)) W hhomW hfin A (toNum e A hA).toGeo s h1 h2 h3 h4,
      hs, hWx, CoverDenseAlt.heightRecR_full K n (II K (blockIdx n)) (toNum e A hA) x _ hx hsec,
      height_toNum e A hA x, hdeg]
  refine ⟨coordField x, inferInstance, inferInstance, pull e (flatCone (coordVec x)), hWeq, ⟨hwnz, ?_⟩, ?_⟩
  · intro f hf
    have hf' : f ∈ mCoordIdeal (pull e (flatCone (coordVec x))) := hWeq ▸ hf
    have h0 : mConeMap (pull e (flatCone (coordVec x))) f = 0 := RingHom.mem_ker.1 hf'
    have key2 : (MvPolynomial.eval (fun _ : K => (1 : coordField x))).comp
        (mConeMap (pull e (flatCone (coordVec x)))).toRingHom =
        (aeval (pull e (flatCone (coordVec x)))).toRingHom :=
      MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun p => by simp [mConeMap]
    have h2 : MvPolynomial.eval (fun _ : K => (1 : coordField x)) (mConeMap (pull e (flatCone (coordVec x))) f) =
        aeval (pull e (flatCone (coordVec x))) f := RingHom.congr_fun key2 f
    have h3 : MvPolynomial.eval (fun _ : K => (1 : coordField x)) (mConeMap (pull e (flatCone (coordVec x))) f) = 0 := by
      rw [h0, map_zero]
    exact h2.symm.trans h3
  · intro A hA
    obtain ⟨m, hm⟩ : ∃ m : K → ℕ, m = fun k => (A.a k).natAbs := ⟨_, rfl⟩
    have hS : IsSmoothHerm (stdLine (ι := ι) m) := stdLine_smooth m
    have hAS : IsSmoothHerm (A.tensor (stdLine m)) := tensor_smooth hA hS
    have hnn : ∀ k, 0 ≤ A.a k + ((2 * m k : ℕ) : ℤ) := fun k => by
      rw [hm]
      push_cast
      linarith [neg_abs_le (A.a k), abs_nonneg (A.a k)]
    have e1 := key (A.tensor (stdLine m)) hAS (fun k => (A.a k + ((2 * m k : ℕ) : ℤ)).toNat)
      (fun k => (Int.toNat_of_nonneg (hnn k)).symm)
    have e2 := key (stdLine m) hS (fun k => 2 * m k) (fun k => rfl)
    have hadd' : II K ι W 1 ![A.tensor (stdLine m)] = II K ι W 1 ![A] + II K ι W 1 ![stdLine m] := by
      have := hadd W 0 Fin.elim0 A (stdLine m) hW (fun j => j.elim0) hA hS
      simpa only [hsnoc] using this
    have hl := lineHt_tensor A (stdLine m) (coordField x) (pull e (flatCone (coordVec x))) hwnz
    have hdne : (degC W : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
    rw [div_eq_iff hdne]
    linear_combination e1 - hadd' - e2 + (degC W : ℝ) * hl
