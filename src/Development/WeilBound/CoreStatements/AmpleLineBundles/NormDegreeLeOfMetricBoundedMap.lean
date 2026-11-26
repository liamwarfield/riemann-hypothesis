module

public import Development.WeilBound.CoreStatements.AmpleLineBundles.SpanLeOfMem
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PLocalChange
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCoordCurveDegree

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.AmpleLineBundles.NormDegreeLeOfMetricBoundedMap
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace CoverDenseAlt

variable {K : Type} [Field K] [NumberField K]

theorem norm_sq_eq_sqAt (E : HermitianBundle.{0} K) (σ : K →+* ℂ) (x : Fibre σ E.carrier) :
    ‖FibreSpace.equiv E.metric σ x‖ ^ 2 = sqAt E σ x := by
  rw [@norm_sq_eq_re_inner ℂ]
  rfl

theorem gram_map_le (E E' : HermitianBundle.{0} K) (φ : E.carrier →ₗ[𝓞 K] E'.carrier) (c : ℝ)
    (hφ : Function.Injective φ) (hc : 0 < c) (σ : K →+* ℂ)
    (h : ∀ x : Fibre σ E.carrier, sqAt E' σ (φ.lTensor (ComplexAt σ) x) ≤ c * sqAt E σ x)
    {r : ℕ} {s : Fin r → E.carrier} (hs : LinearIndependent (𝓞 K) s) :
    gramDet E'.metric σ (fun i => φ (s i)) ≤ c ^ r * gramDet E.metric σ s := by
  have hnorm : ∀ x : Fibre σ E.carrier,
      ‖FibreSpace.equiv (E'.metric.comap φ hφ) σ x‖ ≤ Real.sqrt c * ‖FibreSpace.equiv E.metric σ x‖ := by
    intro x
    have h1 : ‖FibreSpace.equiv (E'.metric.comap φ hφ) σ x‖ ^ 2 = sqAt E' σ (φ.lTensor (ComplexAt σ) x) := by
      rw [← CoverDenseAlt.norm_sq_eq_sqAt, @norm_sq_eq_re_inner ℂ, @norm_sq_eq_re_inner ℂ, FibreSpace.inner_equiv,
        FibreSpace.inner_equiv, HermitianMetric.comap_inner E'.metric φ hφ σ]
      rfl
    have h2 := h x
    rw [← h1, ← CoverDenseAlt.norm_sq_eq_sqAt] at h2
    have h3 : ‖FibreSpace.equiv (E'.metric.comap φ hφ) σ x‖ ^ 2 ≤
        (Real.sqrt c * ‖FibreSpace.equiv E.metric σ x‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hc.le]
      exact h2
    exact (pow_le_pow_iff_left₀ (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) two_ne_zero).mp h3
  have key := LatticeLemmas.gramDet_le_of_norm_le E.metric (E'.metric.comap φ hφ) σ (Real.sqrt c) hnorm hs
  rw [gramDet_comap] at key
  rwa [max_eq_left (Real.sqrt_nonneg c), Real.sq_sqrt hc.le] at key

theorem normDeg_map (E E' : HermitianBundle.{0} K) (φ : E.carrier →ₗ[𝓞 K] E'.carrier) (c : ℝ)
    (hφ : Function.Injective φ) (hc : 0 < c)
    (h : ∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier),
      sqAt E' σ (φ.lTensor (ComplexAt σ) x) ≤ c * sqAt E σ x) (F : Submodule (𝓞 K) E.carrier) :
    E.normDegree F ≤ E'.normDegree (F.map φ) + E.rank F / 2 * Real.log c := by
  classical
  obtain ⟨s, hs⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 K) (M := F) (n := E.rank F) le_rfl
  have hv : LinearIndependent (𝓞 K) (fun i => (s i : E.carrier)) := hs.map' F.subtype F.ker_subtype
  have hw : LinearIndependent (𝓞 K) (fun i => φ (s i : E.carrier)) :=
    hv.map' φ (LinearMap.ker_eq_bot.mpr hφ)
  let e := Submodule.equivMapOfInjective φ hφ F
  let t : Fin (E.rank F) → F.map φ := fun i => e (s i)
  have ht : LinearIndependent (𝓞 K) t := hs.map' e.toLinearMap e.ker
  have hrank : E'.rank (F.map φ) = E.rank F := (LinearEquiv.finrank_eq e).symm
  have hdF := E.degree_eq_of_linearIndependent F hs (Fintype.card_fin _)
  have hdG : E'.degree (F.map φ) = Real.log (Nat.card (F.map φ ⧸ Submodule.span (𝓞 K) (Set.range t))) -
      1 / 2 * ∑ σ : K →+* ℂ, Real.log (gramDet E'.metric σ fun i => φ (s i : E.carrier)) :=
    E'.degree_eq_of_linearIndependent (F.map φ) ht (by rw [Fintype.card_fin, hrank])
  have hcard : Nat.card (F.map φ ⧸ Submodule.span (𝓞 K) (Set.range t)) =
      Nat.card (F ⧸ Submodule.span (𝓞 K) (Set.range s)) := by
    refine (Nat.card_congr (Submodule.Quotient.equiv _ _ e ?_).toEquiv).symm
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  have hgram : ∀ σ : K →+* ℂ, Real.log (gramDet E'.metric σ fun i => φ (s i : E.carrier)) ≤
      E.rank F * Real.log c + Real.log (gramDet E.metric σ fun i => (s i : E.carrier)) := by
    intro σ
    have hle := gram_map_le E E' φ c hφ hc σ (h σ) hv
    have hpos' := gramDet_pos E'.metric σ hw
    have hpos := gramDet_pos E.metric σ hv
    calc _ ≤ Real.log (c ^ E.rank F * gramDet E.metric σ fun i => (s i : E.carrier)) :=
          Real.log_le_log hpos' hle
      _ = _ := by rw [Real.log_mul (pow_pos hc _).ne' hpos.ne', Real.log_pow]
  have hsum := Finset.sum_le_sum fun σ (_ : σ ∈ Finset.univ) => hgram σ
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, NumberField.Embeddings.card K ℂ,
    nsmul_eq_mul] at hsum
  have hq : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  unfold HermitianBundle.normDegree
  rw [div_add' _ _ _ hq.ne', div_le_div_iff_of_pos_right hq, hdF, hdG, hcard]
  linarith

theorem normDegree_le_of_metric_bounded_map : ∀ (K : Type) [Field K] [NumberField K] (E E' : HermitianBundle.{0} K) (φ : E.carrier →ₗ[𝓞 K] E'.carrier) (c : ℝ), Function.Injective φ → 0 < c → (∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier), sqAt E' σ (φ.lTensor (ComplexAt σ) x) ≤ c * sqAt E σ x) → (∀ F : Submodule (𝓞 K) E.carrier, E.normDegree F ≤ E'.normDegree (F.map φ) + E.rank F / 2 * Real.log c) ∧ E.slopeMax ≤ E'.slopeMax + ((Real.log c / 2 : ℝ) : EReal) := by
  intro K _ _ E E' φ c hφ hc h
  refine ⟨normDeg_map E E' φ c hφ hc h, iSup₂_le fun F hF => ?_⟩
  have hne : F.map φ ≠ ⊥ := by
    intro h0
    have := rank_map E E' φ hφ F
    rw [h0] at this
    have h1 := rank_pos E hF
    rw [← this] at h1
    simp [HermitianBundle.rank] at h1
  have hle : ((E'.slope (F.map φ) : ℝ) : EReal) ≤ E'.slopeMax := le_iSup₂_of_le (F.map φ) hne le_rfl
  refine le_trans ?_ (add_le_add_left hle _)
  rw [← EReal.coe_add, EReal.coe_le_coe_iff]
  have hr : (0 : ℝ) < E.rank F := by exact_mod_cast rank_pos E hF
  have hd := normDeg_map E E' φ c hφ hc h F
  unfold HermitianBundle.slope
  rw [rank_map E E' φ hφ, div_add' _ _ _ hr.ne']
  refine div_le_div_of_nonneg_right ?_ hr.le
  linarith

end CoverDenseAlt
end

section -- merged from Development.WeilBound.CoreStatements.AmpleLineBundles.ExistsPointsBoundedLineHeights
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Ht

namespace CoverDenseAlt.Dense0

open GroundTheory.Heights₂.Heights (Coord Cone blockIdx ArithVariety BlockNonzero coordField coordVec evalCone coordDeg)

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : K → ℕ}
  (e : ∀ k, ι k ≃ Fin (n k + 1))

def E : (Σ k, ι k) ≃ Coord n := Equiv.sigmaCongrRight e

def φ : MRing ι ≃+* MvPolynomial (Coord n) ℤ := (renameEquiv ℤ (E e)).toRingEquiv

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem φ_apply (f : MRing ι) : φ e f = rename (E e) f := rfl

omit [Fintype K] [DecidableEq K] in
theorem homog_rename {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) :
    IsMultiHomog (ι := blockIdx n) (φ e f) a := by
  classical
  intro m hm k
  rw [φ_apply, support_rename_of_injective (E e).injective] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := Finset.mem_image.mp hm
  rw [← hf m₀ hm₀ k]
  refine (Fintype.sum_equiv (e k) _ _ fun i => ?_).symm
  exact (Finsupp.mapDomain_apply_of_injective (E e).injective m₀ ⟨k, i⟩).symm

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem mem_map_iff (P : Ideal (MRing ι)) (f : MRing ι) : φ e f ∈ P.map (φ e) ↔ f ∈ P :=
  Ideal.apply_mem_of_equiv_iff

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem horiz {P : Ideal (MRing ι)} (hP : IsHorizontal P) (a : ℤ)
    (ha : (C a : MvPolynomial (Coord n) ℤ) ∈ P.map (φ e)) : a = 0 := by
  have h1 : φ e (C a) = C a := rename_C (E e) a
  rw [← h1, mem_map_iff] at ha
  have h : a ∈ P.comap (C : ℤ →+* MRing ι) := Ideal.mem_comap.mpr ha
  rw [hP] at h
  exact Ideal.mem_bot.mp h

def var {P : Ideal (MRing ι)} {d : ℕ} (hP : IsArithVar P d) : ArithVariety n where
  ideal := P.map (φ e)
  isPrime := by
    have := hP.2.1.1
    exact Ideal.map_isPrime_of_equiv (φ e)
  homogeneous f hf m := by
    refine GroundTheory.Heights₂.Heights.CurveIsOrbit.component_mem ?_ hf m
    obtain ⟨S, hS, rfl⟩ := hP.2.1.2.1
    refine ⟨φ e '' S, ?_, Ideal.map_span _ _⟩
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨a, ha⟩ := hS g hg
    exact ⟨a, homog_rename e ha⟩
  relevant k := by
    obtain ⟨i, hi⟩ := hP.2.1.2.2 k
    refine ⟨e k i, fun h => hi ?_⟩
    have h1 : φ e (X ⟨k, i⟩) = X ⟨k, e k i⟩ := by
      rw [φ_apply, rename_X]
      rfl
    rw [← h1] at h
    exact (mem_map_iff e P _).mp h
  horizontal a ha := horiz e hP.2.2.1 a ha

def back {F : Type} (z : Cone n F) : (Σ k, ι k) → F := fun p => z p.1 (e p.1 p.2)

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem back_nonzero {F : Type} [Zero F] {z : Cone n F} (hz : BlockNonzero z) (k : K) :
    ∃ i, back e z ⟨k, i⟩ ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp (hz k)
  refine ⟨(e k).symm i, ?_⟩
  simpa [back] using hi

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem evalCone_φ {F : Type} [CommRing F] (z : Cone n F) (f : MRing ι) :
    evalCone z (φ e f) = aeval (back e z) f := by
  rw [φ_apply, evalCone, eval₂_rename, aeval_def]
  congr 1

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem aeval_back_eq_zero_iff {L F : Type} [Field L] [Field F] (τ : L →+* F) (z : Cone n L) (f : MRing ι) :
    aeval (back e z) f = 0 ↔ evalCone (fun k i => τ (z k i)) (φ e f) = 0 := by
  have h : τ (aeval (back e z) f) = evalCone (fun k i => τ (z k i)) (φ e f) := by
    rw [evalCone_φ]
    exact comp_aeval_apply (R := ℤ) (back e z) τ.toIntAlgHom f
  rw [← h]
  exact (map_eq_zero τ).symm

def line (A : HermLine ι) (hA : IsSmoothHerm A) : GroundTheory.Heights₂.Heights.HermLine n where
  deg := A.a
  metric z := A.h (back e z)
  metric_pos z hz := A.pos _ (back_nonzero e hz)
  metric_smul c z hc _ := A.smul c (back e z) hc
  metric_smooth := by
    have hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Cone n ℂ => back e z) :=
      contDiff_pi.2 fun p => contDiff_pi.1 (contDiff_pi.1 contDiff_id p.1) (e p.1 p.2)
    exact ContDiffOn.comp hA hu.contDiffOn fun z hz => back_nonzero e hz

omit [DecidableEq K] in
theorem height_eq (A : HermLine ι) (hA : IsSmoothHerm A) (x : Cone n (AlgebraicClosure ℚ)) :
    lineHt A (coordField x) (back e (coordVec x)) = GroundTheory.Heights₂.Heights.height (line e A hA) x := by
  unfold lineHt ptHt GroundTheory.Heights₂.Heights.height
  have h1 : ∀ (v : FinitePlace (coordField x)) (k : K),
      (⨆ i, v (back e (coordVec x) ⟨k, i⟩)) = ⨆ i, v (coordVec x k i) := fun v k =>
    (e k).iSup_comp (g := fun i => v (coordVec x k i))
  simp only [h1]
  congr 1

end CoverDenseAlt.Dense0

open CoverDenseAlt.Dense0 GroundTheory.Heights₂.Heights in
theorem CoverDenseAlt.exists_points_bounded_line_heights : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ), IsArithVar P d → ∀ (J : Type) [Fintype J] (A : J → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι), (∀ j, IsSmoothHerm (A j)) → ∃ C : ℝ, ∀ f : MRing ι, (∃ a, IsMultiHomog f a) → f ∉ P → ∃ (L : Type) (_ : Field L) (_ : NumberField L), ∃ w ∈ ptsOver L P, aeval w f ≠ 0 ∧ ∀ j, |lineHt (A j) L w| ≤ C := by
  intro K _ ι _ P d hP J _ A hA
  classical
  have hcard : ∀ k, Fintype.card (ι k) = (Fintype.card (ι k) - 1) + 1 := fun k => by
    obtain ⟨i, -⟩ := hP.2.1.2.2 k
    have : 0 < Fintype.card (ι k) := Fintype.card_pos_iff.mpr ⟨i⟩
    omega
  let n : K → ℕ := fun k => Fintype.card (ι k) - 1
  let e : ∀ k, ι k ≃ Fin (n k + 1) := fun k => Fintype.equivFinOfCardEq (hcard k)
  obtain ⟨S, C₀, hS, hdense, hC₀⟩ := DenseBoundedHeight.main K n (var e hP)
  choose m C hC using fun j => HeightComparison.main K n (var e hP) (line e (A j) (hA j))
  refine ⟨∑ j, |m j * C₀ + C j|, ?_⟩
  rintro f ⟨a, ha⟩ hf
  have hex : ∃ x ∈ S, evalCone x (φ e f) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hf ((mem_map_iff e P _).mp
      (hdense a (φ e f) ((geoMultiHomog_iff _ _).mp (homog_rename e ha)) hcon))
  obtain ⟨x, hxS, hx⟩ := hex
  have hxP := hS hxS
  have hval := aeval_back_eq_zero_iff e (algebraMap (coordField x) (AlgebraicClosure ℚ)) (coordVec x)
  refine ⟨coordField x, inferInstance, inferInstance, back e (coordVec x), ⟨fun k => ?_, fun g hg => ?_⟩, ?_,
    fun j => ?_⟩
  · obtain ⟨i, hi⟩ := back_nonzero e hxP.1 k
    exact ⟨i, fun h => hi (congrArg Subtype.val h)⟩
  · exact (hval g).mpr (hxP.2 _ (Ideal.mem_map_of_mem _ hg))
  · exact fun h => hx ((hval f).mp h)
  · rw [height_eq e (A j) (hA j)]
    have h1 := hC j x hxP
    have h2 : (m j : ℝ) * height (GroundTheory.Heights₂.Heights.HermLine.standard n) x ≤ m j * C₀ :=
      mul_le_mul_of_nonneg_left (hC₀ x hxS) (Nat.cast_nonneg _)
    have h3 : |m j * C₀ + C j| ≤ ∑ j, |m j * C₀ + C j| :=
      Finset.single_le_sum (f := fun j => |m j * C₀ + C j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    have h4 := le_abs_self (m j * C₀ + C j)
    linarith
end
end
