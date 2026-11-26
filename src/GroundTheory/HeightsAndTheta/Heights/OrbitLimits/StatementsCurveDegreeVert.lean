module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveCountObjects
public import GroundTheory.HeightsAndTheta.Heights.Intersections.NotMemOfNonZeroDivisor
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockImageInverse
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsCurveDegreeVert
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter

def CurveDegreeVert.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (II : IntersectionSystem) (c : ∀ k, ι k)
    (R : Finset ((Σ k, ι k) → ℂ)) (b d : K → ℕ),
    IsIntersectionSystem II → IsArithVar P 1 → IsSmoothHerm A → (∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) →
    (∀ t ∈ R, t ∈ mcPts P) → (∀ z ∈ mcPts P, ∃! t, t ∈ R ∧ SameOrbit z t) →
    (∀ k, (d k : ℤ) = A.a k + b k) →
    II K ι P 1 (fun _ => A) =
      vertR P (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (curveChartMono c d) -
        vertR P (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (curveChartMono c b) +
        ∑ t ∈ R, Real.log (chartRadius A c t)

namespace CurveDegreeVert

end CurveDegreeVert

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLiftGraphFactor
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

def LiftGraphFactor.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (N : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a r : ℕ) (v : Fin r → Ω),
    (∀ j, v j ∈ chartLat y (a • N.a) 1) → KH.GeneratesOn y (a • N.a) v →
    ∃ Φ : ((Σ k, ι k) → ℂ) → ℝ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ {w | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} ∧
      (∀ w : (Σ k, ι k) → ℂ, (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → 0 < Φ w) ∧
      (∀ (c : K → ℂ) (w : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) →
        Φ (fun p => c p.1 * w p) = (∏ k, ‖c k‖ ^ ((a • N.a) k)) ^ 2 * Φ w) ∧
      (∀ w : (Σ k, ι k) → ℂ, Φ (fun p => (starRingEnd ℂ) (w p)) = Φ w) ∧
      (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ j : Fin r,
        secNormAt y N a (v j) (basePart₂ z) * N.h (basePart₂ z) ^ a * Real.sqrt (∑ i : Fin r, ‖z ⟨none, i⟩‖ ^ 2) =
          ‖z ⟨none, j⟩‖ * Real.sqrt (Φ (basePart₂ z))) ∧
      (∀ z ∈ mcPts (mCoordIdeal (addBlock y v)), ∀ ξ : (Σ k, addIdx ι r k) → ℂ,
        IsConeTangent (Int.castRingHom ℂ) (mCoordIdeal (addBlock y v)) z ξ →
        leviForm (fun z => Real.log (Φ (basePart₂ z))) z ξ =
          leviForm (fun z : (Σ k, addIdx ι r k) → ℂ => Real.log (∑ i : Fin r, ‖z ⟨none, i⟩‖ ^ 2)) z ξ)

end

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PCoordFibreDeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem CoordFibreDeg.proof (hM : FibreMultiHomog.Statement) (hD : GenFibreChartDeg.Statement)
    (hR : CoordRatioDeg.Statement) : CoordFibreDeg.Statement := by
  intro K _ ι _ K' _ ι' _ κ v Ω _ _ y d G i hb hZ' hZ hi
  have : CharZero G.Φ' := by
    refine charZero_of_inj_zero fun n hn => ?_
    have hmem : (C (n : ℤ) : MRing ι') ∈ mCoordIdeal y := by
      rw [← G.genericFibre_ker_target, RingHom.mem_ker]
      simpa using hn
    simp only [mCoordIdeal, RingHom.mem_ker, mConeMap] at hmem
    simpa using hmem
  have hMH : IsMultiHomogIdeal (mCoordIdeal y) := hZ'.2.1.2.1
  choose c hc using hZ.2.1.2.2
  have hx : ∀ k, G.x ⟨k, c k⟩ ≠ 0 := fun k h => hc k (by
    rw [← G.ker_x, RingHom.mem_ker, aeval_X]
    exact h)
  have hi' : ∀ k : FibreBlock κ, G.x' ⟨k.1, i k⟩ ≠ 0 := fun k h => hi k (by
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]
    exact h)
  have h1 := Inter.ChartRankAdjoin.proof (FibreBlock κ) (fibreIdx ι' κ) G.Φ G.Φ'
    (fun q : Σ k : FibreBlock κ, fibreIdx ι' κ k => G.x' ⟨q.1.1, q.2⟩) i hi'
    (hM K ι K' ι' κ v (mCoordIdeal y) G hb hMH)
  exact h1.trans ((hD K ι K' ι' κ v (mCoordIdeal y) G c i hb hMH hx hi').trans
    (hR K ι K' ι' κ v Ω y G.Φ' G.x' hb G.genericFibre_ker_target))

end GroundTheory.Heights₂.Heights.Targets
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.CurveOrbitEmbedding
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GroundTheory.Heights₂.Heights.Inter

noncomputable section

namespace CurveOrbit

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]


omit [Fintype K] in
theorem isMultiHomog_mul {f g : MRing ι} {a b : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g b) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]


omit [Fintype K] in
theorem isMultiHomog_add {f g : MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k


omit [Fintype K] in
theorem isMultiHomog_sub {f g : MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (f - g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_sub _ f g hm) with h | h
  · exact hf m h k
  · exact hg m h k


omit [Fintype K] in
theorem isMultiHomog_one : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.support_one] at hm
  rcases Finset.mem_singleton.mp hm with rfl
  simp

theorem mem_of_aeval_eq_zero (y : (Σ k, ι k) → Ω) {f : MRing ι} {d : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f d)
    (h0 : aeval y f = 0) : f ∈ mCoordIdeal y := by
  show mConeMap y f = 0
  rw [ConeTrdeg.mConeMap_of_isMultiHomog y hf, h0, map_zero, zero_mul]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem aeval_eq_zero_of_mem (y : (Σ k, ι k) → Ω) {f : MRing ι} (hf : f ∈ mCoordIdeal y) : aeval y f = 0 := by
  have hc : (MvPolynomial.eval (fun _ : K => (1 : Ω))).comp (mConeMap y).toRingHom = (aeval y).toRingHom :=
    MvPolynomial.ringHom_ext (fun n => by simp) (fun p => by simp [mConeMap])
  have h0 : mConeMap y f = 0 := hf
  have := congrArg (fun φ => φ f) hc
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h0, map_zero] at this
  exact this.symm


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem eval_map_eq_aeval (w : (Σ k, ι k) → ℂ) (f : MRing ι) :
    eval w (map (Int.castRingHom ℂ) f) = aeval w f := by
  rw [eval_map, aeval_def, algebraMap_int_eq]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem eval_comp (σ : Ω →+* ℂ) (y : (Σ k, ι k) → Ω) (f : MRing ι) :
    eval (fun p => σ (y p)) (map (Int.castRingHom ℂ) f) = σ (aeval y f) := by
  have : (eval (fun p => σ (y p))).comp (map (Int.castRingHom ℂ)) = σ.comp (aeval y : MRing ι →ₐ[ℤ] Ω).toRingHom :=
    MvPolynomial.ringHom_ext (fun n => by simp) (fun p => by simp)
  exact congrArg (fun φ => φ f) this


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem mem_mcPts (σ : Ω →+* ℂ) (y : (Σ k, ι k) → Ω) {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    (fun p => σ (y p)) ∈ mcPts (mCoordIdeal y) :=
  ⟨fun k => ⟨c k, (map_ne_zero σ).mpr (hc k)⟩, fun f hf => by rw [eval_comp, aeval_eq_zero_of_mem y hf, map_zero]⟩

theorem eval_smul (w : (Σ k, ι k) → ℂ) (l : K → ℂ) {f : MRing ι} {d : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f d) :
    eval (fun p => l p.1 * w p) (map (Int.castRingHom ℂ) f) = (∏ k, l k ^ d k) * eval w (map (Int.castRingHom ℂ) f) := by
  have hc : (MvPolynomial.eval l).comp (mConeMap w).toRingHom = (aeval (fun p => l p.1 * w p)).toRingHom :=
    MvPolynomial.ringHom_ext (fun n => by simp) (fun p => by simp [mConeMap, mul_comm])
  have h1 := congrArg (MvPolynomial.eval l) (ConeTrdeg.mConeMap_of_isMultiHomog w hf)
  have h2 := congrArg (fun φ => φ f) hc
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h2
  rw [eval_map_eq_aeval, eval_map_eq_aeval, ← h2, h1, map_mul, eval_C, map_prod]
  simp only [map_pow, eval_X]
  ring

theorem exists_sameOrbit {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) (hB : Birational y)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) : ∃ σ : Ω →+* ℂ, SameOrbit z (fun p => σ (y p)) := by
  classical
  set P := mCoordIdeal y
  let φ : MRing ι →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ))
  have hne : ∀ (v : MRing ι) (a : K → ℕ), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog v a → aeval y v ≠ 0 → φ v ≠ 0 := fun v a hv hv0 =>
    eval_ne_zero_of_dimOne arithVarZero hP
      (A := ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun k => (a k : ℤ)))
      ⟨a, fun _ => rfl, hv, fun hm => hv0 (aeval_eq_zero_of_mem y hm)⟩ hz
  choose d g h hg hh hh0 hgh using hB
  let σf : Ω → ℂ := fun s => φ (g s) / φ (h s)
  have hhz : ∀ s, φ (h s) ≠ 0 := fun s => hne _ _ (hh s) (hh0 s)

  have rep : ∀ (s : Ω) (e : K → ℕ) (G H : MRing ι), ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog G e → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog H e → aeval y H ≠ 0 →
      aeval y G = s * aeval y H → σf s * φ H = φ G := by
    intro s e G H hG hH hH0 hGs
    have hmem : G * h s - H * g s ∈ P :=
      mem_of_aeval_eq_zero y (isMultiHomog_sub (isMultiHomog_mul hG (hh s)) (isMultiHomog_mul hH (hg s)))
        (by rw [map_sub, map_mul, map_mul, hGs, hgh s]; ring)
    have h1 : φ G * φ (h s) = φ H * φ (g s) := by
      have : φ (G * h s - H * g s) = 0 := hz.2 _ hmem
      rw [map_sub, map_mul, map_mul] at this
      exact sub_eq_zero.mp this
    simp only [σf]
    field_simp [hhz s]
    linear_combination h1.symm
  have hsub : ∀ s t, aeval y (h s * h t) ≠ 0 := fun s t => by rw [map_mul]; exact mul_ne_zero (hh0 s) (hh0 t)
  let σ : Ω →+* ℂ :=
    { toFun := σf
      map_one' := by
        have := rep 1 0 1 1 isMultiHomog_one isMultiHomog_one (by simp) (by simp)
        simpa using this
      map_mul' := fun s t => by
        have := rep (s * t) (d s + d t) (g s * g t) (h s * h t) (isMultiHomog_mul (hg s) (hg t)) (isMultiHomog_mul (hh s) (hh t)) (hsub s t)
          (by rw [map_mul, map_mul, hgh s, hgh t]; ring)
        have hs := rep s _ _ _ (hg s) (hh s) (hh0 s) (hgh s)
        have ht := rep t _ _ _ (hg t) (hh t) (hh0 t) (hgh t)
        rw [map_mul, map_mul, ← hs, ← ht] at this
        exact mul_right_cancel₀ (mul_ne_zero (hhz s) (hhz t)) (by linear_combination this)
      map_zero' := by
        have := rep 0 0 0 1 (fun m hm => by simp at hm) isMultiHomog_one (by simp) (by simp)
        simpa using this
      map_add' := fun s t => by
        have := rep (s + t) (d s + d t) (g s * h t + h s * g t) (h s * h t) (isMultiHomog_add (isMultiHomog_mul (hg s) (hh t)) (isMultiHomog_mul (hh s) (hg t)))
          (isMultiHomog_mul (hh s) (hh t)) (hsub s t)
          (by rw [map_add (f := _), map_mul, map_mul, map_mul, hgh s, hgh t]; ring)
        have hs := rep s _ _ _ (hg s) (hh s) (hh0 s) (hgh s)
        have ht := rep t _ _ _ (hg t) (hh t) (hh0 t) (hgh t)
        rw [map_add (f := _), map_mul, map_mul, map_mul, ← hs, ← ht] at this
        exact mul_right_cancel₀ (mul_ne_zero (hhz s) (hhz t)) (by linear_combination this) }
  obtain ⟨j, -, hj⟩ := exists_chart hP
  have hzj : ∀ k, z ⟨k, j k⟩ ≠ 0 := fun k => by
    simpa [φ] using hne _ _ (regularityEmbedding_holds.isMultiHomog_X_single k (j k)) (by simpa using hj k)
  refine ⟨σ, fun k => z ⟨k, j k⟩ / σ (y ⟨k, j k⟩), fun k => div_ne_zero (hzj k) ((map_ne_zero σ).mpr (hj k)), ?_⟩
  funext p
  have hr := rep (y p / y ⟨p.1, j p.1⟩) _ _ _ (regularityEmbedding_holds.isMultiHomog_X_single p.1 p.2)
    (regularityEmbedding_holds.isMultiHomog_X_single p.1 (j p.1)) (by simpa using hj p.1) (by simp [div_mul_cancel₀ _ (hj p.1)])
  have hσ : σf (y p / y ⟨p.1, j p.1⟩) = σ (y p) / σ (y ⟨p.1, j p.1⟩) := map_div₀ σ _ _
  rw [hσ] at hr
  simp only [φ, RingHom.comp_apply, map_X, eval_X] at hr
  have hr' : σ (y p) / σ (y ⟨p.1, j p.1⟩) * z ⟨p.1, j p.1⟩ = z p := hr
  show z p = z ⟨p.1, j p.1⟩ / σ (y ⟨p.1, j p.1⟩) * σ (y p)
  rw [← hr']
  ring

end CurveOrbit

end

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftGraphPoints
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace LiftGraphPoints

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem aeval_scale {S : Type} [CommRing S] {g : MRing ι} {a : K → ℕ} (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a)
    (t : K → S) (x z : (Σ k, ι k) → S) (hz : ∀ p, z p = t p.1 * x p) :
    aeval z g = (∏ k, t k ^ a k) * aeval x g := by
  obtain rfl : z = fun p => t p.1 * x p := funext hz
  rw [aeval_def, aeval_def, eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hprod : ∏ p, (t p.1 * x p) ^ m p = (∏ k, t k ^ a k) * ∏ p, x p ^ m p := by
    simp only [mul_pow, Finset.prod_mul_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, t k ^ m ⟨k, i⟩ = t k ^ a k
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  rw [hprod]
  ring

theorem eval_map_int {σ : Type} (z : σ → ℂ) (f : MvPolynomial σ ℤ) :
    eval z (map (Int.castRingHom ℂ) f) = aeval z f := by
  rw [eval_map, aeval_def, algebraMap_int_eq]

def homogAt (c : ∀ k, ι k) (M : ℕ) (F : MRing ι) : MRing ι :=
  ∑ m ∈ F.support, monomial m (AddMonoidAlgebra.coeff F m) * ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (M - ∑ i, m ⟨k, i⟩)

theorem homogAt_isMultiHomog (c : ∀ k, ι k) (M : ℕ) (F : MRing ι)
    (hM : ∀ m ∈ F.support, ∀ k, ∑ i, m ⟨k, i⟩ ≤ M) : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (homogAt c M F) (fun _ => M) := by
  classical
  intro m' hm' k
  obtain ⟨m, hm, hm'⟩ := Finset.mem_biUnion.mp (support_sum hm')
  have h := Inter.ThmIUnique.isMultiHomog_mul' (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_monomial m (AddMonoidAlgebra.coeff F m))
    (Inter.ThmIUnique.isMultiHomog_coordMonomial c (fun k => M - ∑ i, m ⟨k, i⟩)) m' hm' k
  simp only [Pi.add_apply] at h
  have := hM m hm k
  show _ = M
  omega

theorem aeval_homogAt {S : Type} [CommRing S] (c : ∀ k, ι k) (M : ℕ) (F : MRing ι)
    (x : (Σ k, ι k) → S) (hx : ∀ k, x ⟨k, c k⟩ = 1) : aeval x (homogAt c M F) = aeval x F := by
  conv_rhs => rw [F.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [homogAt, map_sum, map_mul, map_prod, map_pow, aeval_X, hx, one_pow, Finset.prod_const_one, mul_one]

theorem aeval_ratio_eq_zero {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} {w : (Σ k, ι k) → ℂ}
    (hw : w ∈ mcPts (mCoordIdeal y)) (c : ∀ k, ι k) (hyc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hwc : ∀ k, w ⟨k, c k⟩ ≠ 0) {F : MRing ι} (hF : aeval (fun p => y p / y ⟨p.1, c p.1⟩) F = 0) :
    aeval (fun p => w p / w ⟨p.1, c p.1⟩) F = 0 := by
  classical
  set M := ∑ m ∈ F.support, ∑ p, m p
  have hM : ∀ m ∈ F.support, ∀ k, ∑ i, m ⟨k, i⟩ ≤ M := by
    intro m hm k
    calc ∑ i, m ⟨k, i⟩ ≤ ∑ k, ∑ i, m ⟨k, i⟩ :=
          Finset.single_le_sum (f := fun k => ∑ i, m ⟨k, i⟩) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      _ = ∑ p, m p := (Fintype.sum_sigma _).symm
      _ ≤ M := Finset.single_le_sum (f := fun m : (Σ k, ι k) →₀ ℕ => ∑ p, m p) (fun _ _ => Nat.zero_le _) hm
  have hG := homogAt_isMultiHomog c M F hM
  have hyG : aeval y (homogAt c M F) = 0 := by
    rw [aeval_scale hG (fun k => y ⟨k, c k⟩) (fun p => y p / y ⟨p.1, c p.1⟩) y
      (fun p => by field_simp [hyc p.1]), aeval_homogAt c M F _ (fun k => div_self (hyc k)), hF, mul_zero]
  have hmem : homogAt c M F ∈ mCoordIdeal y := (BlockImageInverse.mem_mCoordIdeal_iff y hG).mpr hyG
  have hwG := hw.2 _ hmem
  rw [eval_map_int, aeval_scale hG (fun k => w ⟨k, c k⟩) (fun p => w p / w ⟨p.1, c p.1⟩) w
    (fun p => by field_simp [hwc p.1]), aeval_homogAt c M F _ (fun k => div_self (hwc k))] at hwG
  exact (mul_eq_zero.mp hwG).resolve_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hwc k))

end LiftGraphPoints


open LiftGraphPoints in
theorem LiftGraphPoints.proof : LiftGraphPoints.Statement := by
  classical
  intro K _ ι _ Ω _ y n r v hv hgen w hw
  choose c hwc using hw.1
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := by
    intro k h0
    apply hwc k
    have hX : (X ⟨k, c k⟩ : MRing ι) ∈ mCoordIdeal y := by
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul]
    simpa using hw.2 _ hX
  have hrange : chartRingZ y c = (aeval fun p => y p / y ⟨p.1, c p.1⟩).range := by
    rw [chartRingZ, Algebra.adjoin_range_eq_range_aeval]
  have hQ : ∀ j, ∃ Q : MRing ι, aeval (fun p => y p / y ⟨p.1, c p.1⟩) Q = v j * ∏ k, y ⟨k, c k⟩ ^ (-n k) := by
    intro j
    have h := hv j c hyc
    simp only [Nat.cast_one, one_mul] at h
    rw [hrange] at h
    exact (AlgHom.mem_range _).mp h
  choose Q hQ using hQ
  set σ : Fin r → ℂ := fun j => aeval (fun p => w p / w ⟨p.1, c p.1⟩) (Q j) with hσ
  refine ⟨addBlock w σ, ⟨fun k => ?_, fun f hf => ?_⟩, rfl⟩
  · cases k with
    | some k => exact ⟨c k, hwc k⟩
    | none =>
      obtain ⟨u, hu, hsum⟩ := hgen c hyc
      have hU : ∀ j, ∃ U : MRing ι, aeval (fun p => y p / y ⟨p.1, c p.1⟩) U = u j := fun j =>
        (AlgHom.mem_range _).mp (hrange ▸ hu j)
      choose U hU using hU
      by_contra hcon
      push Not at hcon
      have hF : aeval (fun p => y p / y ⟨p.1, c p.1⟩) (∑ j, U j * Q j - 1) = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sub, map_sum, map_mul, hU, hQ, map_one, hsum, sub_self]
      have h1 := aeval_ratio_eq_zero hw c hyc hwc hF
      have hσ0 : ∀ j, aeval (fun p => w p / w ⟨p.1, c p.1⟩) (Q j) = 0 := fun j => hcon j
      simp [hσ0] at h1
  · obtain ⟨S, hS, hspan⟩ := CoordinateConeArithVar.isMultiHomogIdeal (addBlock y v)
    rw [hspan] at hf
    induction hf using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, ha⟩ := hS g hg
      have hg0 : aeval (addBlock y v) g = 0 :=
        (BlockImageInverse.mem_mCoordIdeal_iff _ ha).mp (hspan ▸ Ideal.subset_span hg)
      have hP : (∏ k, y ⟨k, c k⟩ ^ (-n k)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hyc k)
      have hY : ∀ o : Option K, (o.elim (∏ k, y ⟨k, c k⟩ ^ (-n k))⁻¹ fun k => y ⟨k, c k⟩) ≠ 0 := by
        intro o
        cases o with
        | none => exact inv_ne_zero hP
        | some k => exact hyc k
      rw [aeval_scale ha (fun o => o.elim (∏ k, y ⟨k, c k⟩ ^ (-n k))⁻¹ fun k => y ⟨k, c k⟩)
        (addBlock (fun p => y p / y ⟨p.1, c p.1⟩) fun j => aeval (fun p => y p / y ⟨p.1, c p.1⟩) (Q j)) _
        (by
          rintro ⟨o, i⟩
          cases o with
          | none =>
            exact (show ∀ j : Fin r, v j = (∏ k, y ⟨k, c k⟩ ^ (-n k))⁻¹ *
                aeval (fun p => y p / y ⟨p.1, c p.1⟩) (Q j) from fun j => by rw [hQ]; field_simp) i
          | some k =>
            show y ⟨k, i⟩ = y ⟨k, c k⟩ * (y ⟨k, i⟩ / y ⟨k, c k⟩)
            field_simp [hyc k])] at hg0
      have hg1 := (mul_eq_zero.mp hg0).resolve_left (Finset.prod_ne_zero_iff.mpr fun o _ => pow_ne_zero _ (hY o))
      have hsub : ∀ (T : Type) [CommRing T] [Algebra ℤ T] (x : (Σ k, ι k) → T),
          aeval x (aeval (addBlock (fun p => (X p : MRing ι)) Q) g) =
            aeval (addBlock x fun j => aeval x (Q j)) g := by
        intro T _ _ x
        rw [comp_aeval_apply]
        have hfun : (fun q => aeval x (addBlock (fun p => (X p : MRing ι)) Q q)) =
            addBlock x fun j => aeval x (Q j) := by
          funext q
          obtain ⟨o, i⟩ := q
          cases o with
          | none => rfl
          | some k => exact aeval_X _ _
        rw [hfun]
      rw [← hsub] at hg1
      have h2 := aeval_ratio_eq_zero hw c hyc hwc hg1
      rw [hsub] at h2
      rw [eval_map_int, aeval_scale ha (fun o => o.elim 1 fun k => w ⟨k, c k⟩)
        (addBlock (fun p => w p / w ⟨p.1, c p.1⟩) σ) _
        (by
          rintro ⟨o, i⟩
          cases o with
          | none => exact (one_mul _).symm
          | some k =>
            show w ⟨k, i⟩ = w ⟨k, c k⟩ * (w ⟨k, i⟩ / w ⟨k, c k⟩)
            field_simp [hwc k]), h2, mul_zero]
    | zero => simp
    | add x₁ x₂ _ _ h₁ h₂ => simp [map_add (f := _), h₁, h₂]
    | smul a x _ hx => simp [smul_eq_mul, map_mul, hx]

end

end GroundTheory.Heights₂.Heights.Targets
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftBlockDatum
section -- merged from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.LiftBlockGraph
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4
open GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

namespace LiftBlockGraph

variable {K : Type} {ι : K → Type} {Ω : Type} [Field Ω]

theorem generatesOn_liftCoords [Fintype K] {ι' : Type} [Fintype ι'] (y : (Σ k, ι k) → Ω) (n : K → ℤ) (x' : ι' → Ω)
    (h : KH.GeneratesOn y n x') : KH.GeneratesOn y n (liftCoords x') := by
  intro c hc
  obtain ⟨u, hu, hs⟩ := h c hc
  refine ⟨fun j => u ((Fintype.equivFin ι').symm j), fun j => hu _, ?_⟩
  rw [← hs]
  exact Fintype.sum_equiv (Fintype.equivFin ι').symm _ _ (fun j => rfl)

theorem exists_ne_zero_of_generatesOn [Fintype K] {r : ℕ} (y : (Σ k, ι k) → Ω) (n : K → ℤ) (v : Fin r → Ω)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (h : KH.GeneratesOn y n v) : ∃ j, v j ≠ 0 := by
  obtain ⟨u, -, hs⟩ := h c hc
  by_contra h0
  simp only [not_exists, not_not] at h0
  simp [h0] at hs

variable [CharZero Ω] [Fintype K] [∀ k, Fintype (ι k)]


omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem chartRingZ_le_blockFnField (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {x : Ω} (hx : x ∈ chartRingZ y c) :
    x ∈ blockFnField y := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact IntermediateField.subset_adjoin _ _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
  | algebraMap m =>
    rw [eq_intCast]
    exact intCast_mem _ m
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

theorem blockFnField_addBlock (y : (Σ k, ι k) → Ω) (n : K → ℤ) {r : ℕ} (v : Fin r → Ω)
    (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hv : ∀ j, v j ∈ chartLat y n 1) :
    blockFnField (addBlock y v) = blockFnField y := by
  apply le_antisymm
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro t ⟨⟨pk, pi⟩, ⟨qk, qi⟩, hpq, rfl⟩
    simp only at hpq
    subst hpq
    cases pk with
    | none =>
      set P : Ω := ∏ k, y ⟨k, c k⟩ ^ (-(((1 : ℕ) : ℤ) * n k)) with hP
      have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
      have h1 := chartRingZ_le_blockFnField y c (hv pi c hc)
      have h2 := chartRingZ_le_blockFnField y c (hv qi c hc)
      have : v pi / v qi = (v pi * P) / (v qi * P) := (mul_div_mul_right _ _ hP0).symm
      change v pi / v qi ∈ blockFnField y
      rw [this]
      exact div_mem h1 h2
    | some k =>
      exact IntermediateField.subset_adjoin _ _ ⟨⟨k, pi⟩, ⟨k, qi⟩, rfl, rfl⟩
  · refine IntermediateField.adjoin_le_iff.mpr ?_
    rintro t ⟨p, q, hpq, rfl⟩
    exact IntermediateField.subset_adjoin _ _
      ⟨⟨some p.1, p.2⟩, ⟨some q.1, q.2⟩, by simp [hpq], rfl⟩

theorem isArithVar_addBlock {D : ℕ} (y : (Σ k, ι k) → Ω) (n : K → ℤ) {r : ℕ} (v : Fin r → Ω)
    (hA : IsArithVar (mCoordIdeal y) (D + 1)) (hv : ∀ j, v j ∈ chartLat y n 1) (hg : KH.GeneratesOn y n v) :
    IsArithVar (mCoordIdeal (addBlock y v)) (D + 1) := by
  obtain ⟨c, hc⟩ := CoordArithOfFnField.nonzero_of_relevant y hA.2.1.2.2
  refine CoordArithOfFnField.proof K ι (Option K) (addIdx ι r) Ω y (addBlock y v) (D + 1) ⟨none⟩ ?_
    (blockFnField_addBlock y n v c hc hv).symm hA
  rintro (_ | k)
  · obtain ⟨j, hj⟩ := exists_ne_zero_of_generatesOn y n v c hc hg
    exact ⟨j, hj⟩
  · exact ⟨c k, hc k⟩


omit [CharZero Ω] in
theorem isMultiHomog_rename_none [DecidableEq K] {ι' : Type} [Fintype ι'] {g : MRing (fun _ : Unit => ι')} {e : Unit → ℕ}
    (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g e) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (rename (fun p : Σ _ : Unit, ι' =>
      (⟨none, Fintype.equivFin ι' p.2⟩ : Σ k, addIdx ι (Fintype.card ι') k)) g)
      (blockDeg (none : Option K) (e ())) := by
  classical
  set φ : (Σ _ : Unit, ι') → (Σ k, addIdx ι (Fintype.card ι') k) :=
    fun p => ⟨none, Fintype.equivFin ι' p.2⟩ with hφ
  have hinj : Function.Injective φ := by
    rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
    obtain ⟨-, h2⟩ := Sigma.mk.inj h
    exact congrArg (Sigma.mk ()) ((Fintype.equivFin ι').injective (eq_of_heq h2))
  intro m hm k
  rw [support_rename_of_injective hinj] at hm
  obtain ⟨m0, hm0, rfl⟩ := Finset.mem_image.mp hm
  cases k with
  | none =>
    have hterm : ∀ i : Fin (Fintype.card ι'),
        (Finsupp.mapDomain φ m0) ⟨none, i⟩ = m0 ⟨(), (Fintype.equivFin ι').symm i⟩ := by
      intro i
      have : (⟨none, i⟩ : Σ k, addIdx ι (Fintype.card ι') k) = φ ⟨(), (Fintype.equivFin ι').symm i⟩ := by
        simp [hφ]
      rw [this, Finsupp.mapDomain_apply_of_injective hinj]
    change ∑ i : Fin (Fintype.card ι'), (Finsupp.mapDomain φ m0) ⟨none, i⟩ = _
    simp only [hterm]
    rw [Fintype.sum_equiv (Fintype.equivFin ι').symm (fun i => m0 ⟨(), (Fintype.equivFin ι').symm i⟩)
      (fun j => m0 ⟨(), j⟩) (fun _ => rfl)]
    have := hg m0 hm0 ()
    simp only [blockDeg, if_true]
    rw [← this]
  | some k =>
    have hterm : ∀ i, (Finsupp.mapDomain φ m0) ⟨some k, i⟩ = 0 := by
      intro i
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨p, hp⟩
      simp only [hφ] at hp
      exact absurd (congrArg Sigma.fst hp) (by simp)
    simp [hterm, blockDeg]


omit [CharZero Ω] in
theorem blockBirational_addBlock [DecidableEq K] {ι' : Type} [Fintype ι'] (y : (Σ k, ι k) → Ω) (x' : ι' → Ω)
    (hb : Birational (fun p : Σ _ : Unit, ι' => x' p.2)) :
    BlockBirational (addBlock y (liftCoords x')) (none : Option K) := by
  intro d g h hg hh hne
  obtain ⟨e, g', h', hg', hh', hne', hs⟩ :=
    hb (aeval (addBlock y (liftCoords x')) g / aeval (addBlock y (liftCoords x')) h)
  set φ : (Σ _ : Unit, ι') → (Σ k, addIdx ι (Fintype.card ι') k) :=
    fun p => ⟨none, Fintype.equivFin ι' p.2⟩ with hφ
  have hev : ∀ f : MRing (fun _ : Unit => ι'), aeval (addBlock y (liftCoords x')) (rename φ f) =
      aeval (fun p : Σ _ : Unit, ι' => x' p.2) f := by
    intro f
    have hc : addBlock y (liftCoords x') ∘ φ = fun p => x' p.2 := by
      funext p
      simp [hφ, addBlock, liftCoords]
    rw [aeval_rename, hc]
  refine ⟨e (), rename φ g', rename φ h', isMultiHomog_rename_none hg', isMultiHomog_rename_none hh', ?_, ?_⟩
  · rw [hev]
    exact hne'
  · rw [hev, hev, hs]
    field_simp


omit [CharZero Ω] in
theorem isMultiHomogIdeal_top : IsMultiHomogIdeal (⊤ : Ideal (MRing ι)) :=
  ⟨{1}, fun f hf => ⟨0, by rw [Set.mem_singleton_iff.mp hf]; exact Inter.AvoidRing.isMultiHomog_one⟩,
    Ideal.span_singleton_one.symm⟩

end LiftBlockGraph

end

end GroundTheory.Heights₂.Heights.Targets
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel LiftBlockGraph

noncomputable section

theorem LiftBlockDatum.proof (hE : ResExistsStatement) (hVol : ResVolume.Statement)
    (hPts : LiftGraphPoints.Statement) (hMet : LiftGraphMetric.Statement) : LiftBlockDatum.Statement := by
  intro K _ _ ι _ Ω _ _ y D N P0 a ι' _ x' hD harith _ hP0 hsemi hconj _ hx' hgen hbir'
  have hv : ∀ j, liftCoords x' j ∈ chartLat y (a • N.a) 1 := fun j => hx' _
  have hgv := generatesOn_liftCoords y (a • N.a) x' hgen
  have harith' := isArithVar_addBlock y (a • N.a) (liftCoords x') harith hv hgv
  obtain ⟨A, hAdeg, hAconj, hAsemi, hrel⟩ :=
    hMet K ι Ω y N P0 a (Fintype.card ι') (liftCoords x') hP0 hsemi hconj hv hgv
  have hnot : ¬ (⊤ : Ideal (MRing (addIdx ι (Fintype.card ι')))) ≤ mCoordIdeal (addBlock y (liftCoords x')) :=
    fun h => harith'.2.1.1.ne_top (top_le_iff.mp h)
  obtain ⟨J, -, -, -, ⟨R⟩⟩ := hE (Option K) (addIdx ι (Fintype.card ι')) _ ⊤ D harith'
    isMultiHomogIdeal_top hnot
  let _ : MeasurableSpace R.toAnRes.X := borel _
  have : BorelSpace R.toAnRes.X := ⟨rfl⟩
  obtain ⟨dV, hdV⟩ := hVol (Option K) (addIdx ι (Fintype.card ι')) _ J D R.toAnRes harith'
  refine ⟨
    { y := addBlock y (liftCoords x'), k₀ := none, A := A, P0 := mCoordIdeal (addBlock y (liftCoords x')),
      J := J, R := R.toAnRes, meas := borel _, borel := ⟨rfl⟩, dV := dV, one_le := hD, arith := harith',
      birat := blockBirational_addBlock y x' hbir', deg := hAdeg, conjInv := hAconj, normalForm_baseLattice_le_dualSpan_sup_line := le_rfl,
      semipos := hAsemi, vol := hdV }, rfl, rfl, hrel, ?_⟩
  exact hPts K ι Ω y (a • N.a) (Fintype.card ι') (liftCoords x') hv hgv

end

end GroundTheory.Heights₂.Heights.Targets
end
