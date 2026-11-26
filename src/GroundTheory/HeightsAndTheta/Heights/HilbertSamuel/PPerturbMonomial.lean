module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PQuotPartGraded
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SupBoundCountLattice
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenSESStep
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiProjPrimeImageZ
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMixSt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageCoord
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionPointValue

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPerturbMonomial
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry SectionBoundedMul SmallGenTwist

noncomputable section

namespace PerturbedMonomialBound

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem chartMono_exponent (c : ∀ k, ι k) (d : K → ℕ) :
    ∃ μ : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, μ ⟨k, i⟩ = d k) ∧
      ∀ z : (Σ k, ι k) → ℂ, ∏ p, z p ^ μ p = ∏ k, z ⟨k, c k⟩ ^ d k := by
  classical
  refine ⟨∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k), fun k => ?_, fun z => ?_⟩
  · simp only [Finsupp.finsetSum_apply]
    rw [Finset.sum_comm]
    simp only [sum_single_apply, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have h : chartMono c d = monomial (∑ k, Finsupp.single (⟨k, c k⟩ : Σ k, ι k) (d k)) (1 : ℤ) := by
      rw [chartMono, monomial_sum_one]
      exact Finset.prod_congr rfl fun k _ => X_pow_eq_monomial
    have e1 := eval_chartMono z c d
    rw [h, map_monomial, eval_monomial, Finsupp.prod_fintype _ _ (fun i => by simp)] at e1
    simpa using e1

theorem smallGen_of_monomialsBounded (y : (Σ k, ι k) → Ω) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a : K → ℕ)
    (ha : A.a = fun k => (a k : ℤ)) (hB : MonomialsBounded (mCoordIdeal y) A a) : SmallGen y A := by
  classical
  set e := Fintype.equivFin (∀ k, ι k) with he_def
  refine ⟨Fintype.card (∀ k, ι k), fun j => aeval y (chartMono (e.symm j) a), fun j => ?_, ?_, fun j => ?_⟩
  · intro c hc
    beta_reduce
    rw [aeval_chartMono, ← Finset.prod_mul_distrib]
    refine prod_mem fun k _ => ?_
    have hmem : y ⟨k, (e.symm j) k⟩ / y ⟨k, c k⟩ ∈ chartRingZ y c :=
      Algebra.subset_adjoin ⟨⟨k, (e.symm j) k⟩, rfl⟩
    convert pow_mem hmem (a k) using 1
    simp [ha, div_eq_mul_inv, zpow_neg, zpow_natCast, mul_pow, inv_pow]
  · intro c hc
    refine ⟨fun j => if e.symm j = c then 1 else 0, fun j => by beta_reduce; split_ifs <;> simp, ?_⟩
    rw [Fintype.sum_equiv e.symm _ (fun i => (if i = c then (1 : Ω) else 0) *
      (aeval y (chartMono i a) * ∏ k, y ⟨k, c k⟩ ^ (-A.a k))) (fun _ => rfl)]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [aeval_chartMono, ← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun k _ => by
      simp [ha, zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ (hc k))]
  · intro dg dh g h z hg hh hdeg he hz
    have hd : dg = a + dh := funext fun k => by
      have := hdeg k
      simp only [ha, Nat.cast_one, one_mul] at this
      simp only [Pi.add_apply]
      omega
    have hF : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (g - chartMono (e.symm j) a * h) dg :=
      isMultiHomog_sub hg (by rw [hd]; exact isMultiHomog_mul (isMultiHomog_chartMono _ a) hh)
    have h0 : aeval y (g - chartMono (e.symm j) a * h) = 0 := by
      rw [map_sub, map_mul, he, sub_self]
    have hz0 := hz.2 _ (mem_mCoordIdeal_of_aeval_eq_zero y hF h0)
    simp only [map_sub, map_mul, sub_eq_zero] at hz0
    rw [hz0, norm_mul, eval_chartMono, pow_one, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    obtain ⟨μ, hμ, hzμ⟩ := chartMono_exponent (e.symm j) a
    rw [← hzμ z]
    exact hB z hz μ hμ

end PerturbedMonomialBound


open PerturbedMonomialBound in
theorem PerturbMonomial.proof (hDeg : GenDegAmple.Statement) : PerturbMonomial.Statement := by
  intro K _ ι _ Ω _ y D a A P0 q _ hV _ ha hP0 hsemi hmono _
  have hBa : (HermLine.zcomb A (fsH ι) q 1).a = fun k => (q : ℤ) * a k + 1 := by
    funext k
    simp [HermLine.zcomb, ha, fsH_a]
  refine ⟨hP0, ?_, ?_, ?_⟩
  · exact PerturbSemipos.proof K ι P0 (mCoordIdeal y) A q 1 hsemi (by positivity) zero_le_one
  · rw [hBa]
    refine hDeg K ι Ω y D _ hV fun k => ?_
    have : (0 : ℤ) ≤ (q : ℤ) * a k := by positivity
    omega
  · have h := smallGen_zcomb y A (smallGen_of_monomialsBounded y A a ha hmono) q 1
    rw [Nat.cast_one] at h
    exact h

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSupBoundCount
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Matrix

noncomputable section

namespace SupBoundCount

theorem main {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type}
    [Field Ω] [CharZero Ω] (d : HSMBlockDatum D K ι Ω) (n : ℕ) {c : ℝ} (hc : 0 < c)
    (hsup : ∀ f : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (blockDeg d.k₀ n) → ∀ z ∈ mcPts (mCoordIdeal d.y),
      ‖eval z (map (Int.castRingHom ℂ) f)‖ / d.A.h z ^ n ≤ c * blockL2Norm d n f)
    {r : ℕ} {b : Fin r → MvPolynomial (Σ k, ι k) ℚ} (hb : IsSecBasisM d.y d.k₀ n b) :
    (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) ≤ 2 * c ^ 2 ∧
      -(1 / 2) * Real.log (blockGram d n b).det - (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)) : ℝ) *
          Real.log (c * Real.sqrt (Module.finrank ℤ (secM d.y (blockDeg d.k₀ n)))) ≤
        smallSectionCount (IsSmallH (mCoordIdeal d.y) d.y d.A) (fun τ => secM d.y (blockDeg d.k₀ τ)) n := by
  classical
  rw [finrank_secM hb]
  have hb' := hb
  choose f hf hbf using hb.1
  have hbe : b = fun j => map (Int.castRingHom ℚ) (f j) := funext hbf
  subst hbe
  have hli : LinearIndependent ℤ fun k => aeval d.y (f k) := by
    have := hb'.2.1
    simpa [aeval_map_int] using this
  have hG := gram_posDef d n f hf hli hc hsup
  refine ⟨rank_le d n f hf hli hc hsup, ?_⟩

  set Q : (Fin r → ℤ) → ℝ := fun m => (fun k => (m k : ℝ)) ⬝ᵥ
    (blockGram d n (fun j => map (Int.castRingHom ℚ) (f j)) *ᵥ fun k => (m k : ℝ)) with hQ
  set P : (Fin r → ℤ) → Prop := fun m =>
    IsSmallH (mCoordIdeal d.y) d.y d.A n (aeval d.y (∑ k, m k • f k)) with hPdef
  have hP1 : ∀ m, Q m ≤ (1 / c) ^ 2 → P m := by
    intro m hm
    have hF := isMultiHomog_zsum f m hf
    refine (isSmallH_iff d n hF).2 fun z hz => ?_
    have h1 := hsup _ hF z hz
    rw [blockL2Norm_sum_eq_sqrt_gram d n f hf m] at h1
    have h2 : Real.sqrt (Q m) ≤ 1 / c := by
      calc Real.sqrt (Q m) ≤ Real.sqrt ((1 / c) ^ 2) := Real.sqrt_le_sqrt hm
        _ = 1 / c := Real.sqrt_sq (by positivity)
    have h3 : c * Real.sqrt (Q m) ≤ 1 := by
      calc c * Real.sqrt (Q m) ≤ c * (1 / c) := mul_le_mul_of_nonneg_left h2 hc.le
        _ = 1 := by field_simp
    have hp : 0 < d.A.h z ^ n := pow_pos (d.A.pos z hz.1) n
    exact (div_le_one hp).1 (h1.trans h3)
  have hP2 : ∀ m, P m → Q m ≤ 1 := by
    intro m hm
    have hF := isMultiHomog_zsum f m hf
    have h1 := blockL2Norm_le_one_of_sup_bound d n hF ((isSmallH_iff d n hF).1 hm)
    rw [blockL2Norm_sum_eq_sqrt_gram d n f hf m] at h1
    by_contra h
    push_neg at h
    have := Real.sqrt_lt_sqrt zero_le_one h
    rw [Real.sqrt_one] at this
    linarith
  obtain ⟨-, hcount⟩ := count_of_gram hG (by positivity : (0 : ℝ) < 1 / c) P hP1 hP2

  have hmem : ∀ m : Fin r → ℤ, aeval d.y (∑ k, m k • f k) ∈ secM d.y (blockDeg d.k₀ n) := by
    intro m
    rw [← hb'.2.2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨k, by simp [aeval_map_int]⟩)
  have hinj : Function.Injective fun m : Fin r → ℤ => aeval d.y (∑ k, m k • f k) := by
    intro m m' h
    have h0 : ∑ k, (m k - m' k) • aeval d.y (f k) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_zsmul] at h
      simp only [sub_smul, Finset.sum_sub_distrib]
      exact sub_eq_zero.2 h
    funext k
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h0 k)
  let E : {m // P m} → {s : secM d.y (blockDeg d.k₀ n) // IsSmallH (mCoordIdeal d.y) d.y d.A n (s : Ω)} :=
    fun m => ⟨⟨_, hmem m.1⟩, m.2⟩
  have hE : Function.Bijective E := by
    refine ⟨fun m m' h => Subtype.ext (hinj (congrArg (fun s => ((s.1 : secM d.y _) : Ω)) h)), ?_⟩
    rintro ⟨⟨s, hs⟩, hsm⟩
    have hs' := hs
    rw [← hb'.2.2] at hs'
    obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hs'
    have hms : aeval d.y (∑ k, m k • f k) = s := by
      rw [← hm]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, aeval_map_int]
    refine ⟨⟨m, ?_⟩, ?_⟩
    · show IsSmallH _ _ _ _ _
      rw [hms]
      exact hsm
    · exact Subtype.ext (Subtype.ext hms)
  have hcard := Nat.card_congr (Equiv.ofBijective E hE)
  simp only [smallSectionCount]
  rw [← hcard]

  have hV : (r : ℝ) * Real.log (2 / Real.sqrt r) ≤ Real.log (unitBallVolume r) := by
    have hpos : 0 < (2 / Real.sqrt r) ^ r := by
      rcases Nat.eq_zero_or_pos r with h0 | h0
      · simp [h0]
      · exact pow_pos (div_pos two_pos (Real.sqrt_pos.2 (by exact_mod_cast h0))) r
    rw [← Real.log_pow]
    exact Real.log_le_log hpos (MinkowskiCount.cube_le_unitBallVolume r)
  have halg : (r : ℝ) * Real.log (2 / Real.sqrt r) + r * Real.log (1 / c / 2) =
      -((r : ℝ) * Real.log (c * Real.sqrt r)) := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · simp [h0]
    · have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 (by exact_mod_cast h0)
      rw [← mul_add, ← Real.log_mul (by positivity) (by positivity)]
      have : 2 / Real.sqrt r * (1 / c / 2) = (c * Real.sqrt r)⁻¹ := by
        field_simp
      rw [this, Real.log_inv]
      ring
  linarith

end SupBoundCount

theorem SupBoundCount.proof : SupBoundCount.Statement := by
  intro D K _ _ ι _ Ω _ _ d n c hc hsup
  have hex := SupBoundCount.exists_isSecBasisM d.y d.k₀ n
  have h := SupBoundCount.main d n hc hsup hex.choose_spec
  refine ⟨h.1, ?_⟩
  rw [blockChi, dite_eq_left hex]
  exact h.2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseGraphDeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

namespace VeroneseGraphDeg

theorem isMultiHomog_forms (D : ℕ) (q : Ix (Veronese.Idx D)) :
    ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (Veronese.forms D q) ((fun _ _ => 2 : Unit → Unit → ℕ) q.1) := by
  have h := Inter.AvoidRing.isMultiHomog_mul
    (Inter.AvoidRing.isMultiHomog_X (R := ℤ) (ι := GlobalTheory (Fin (D + 1))) () q.2.1.1)
    (Inter.AvoidRing.isMultiHomog_X (R := ℤ) (ι := GlobalTheory (Fin (D + 1))) () q.2.1.2)
  have e : ((fun _ _ => 2 : Unit → Unit → ℕ) q.1) = Pi.single () 1 + Pi.single () 1 := by
    funext k
    cases k
    simp
  rw [e]
  exact h

def xc {D : ℕ} (i : Fin (D + 1)) : Σ k, Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)) k := ⟨Sum.inl (), i⟩

def yc {D : ℕ} (i j : Fin (D + 1)) (h : i ≤ j) : Σ k, Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)) k :=
  ⟨Sum.inr (), ⟨(i, j), h⟩⟩

abbrev Γ (D : ℕ) : Ideal (MRing (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)))) :=
  graphIdeal ⊥ (Veronese.forms D)

theorem graphMap_xc {D : ℕ} (i : Fin (D + 1)) :
    graphMap (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) (Veronese.forms D) (X (xc i)) =
      C (Ideal.Quotient.mk ⊥ (X ⟨(), i⟩)) :=
  eval₂Hom_X' _ _ _

theorem graphMap_yc {D : ℕ} (i j : Fin (D + 1)) (h : i ≤ j) :
    graphMap (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) (Veronese.forms D) (X (yc i j h)) =
      C (Ideal.Quotient.mk ⊥ (X ⟨(), i⟩ * X ⟨(), j⟩)) * X () :=
  eval₂Hom_X' _ _ _

theorem rel_mem (D : ℕ) (i : Fin (D + 1)) :
    (X (xc 0) * X (yc 0 i (Fin.zero_le i)) - X (xc i) * X (yc 0 0 le_rfl) :
        MRing (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)))) ∈ Γ D := by
  rw [Γ, graphIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, graphMap_xc, graphMap_xc, graphMap_yc,
    graphMap_yc]
  simp only [map_mul]
  ring

theorem veroneseFirstCoordinate_not_mem_graph (D : ℕ) :
    (X (yc 0 0 le_rfl) : MRing (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)))) ∉ Γ D := by
  rw [Γ, graphIdeal, RingHom.mem_ker, graphMap_yc]
  refine mul_ne_zero ?_ (X_ne_zero _)
  rw [Ne, C_eq_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
  exact mul_ne_zero (X_ne_zero _) (X_ne_zero _)

theorem x_not_mem (D : ℕ) (i : Fin (D + 1)) :
    (X (xc i) : MRing (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)))) ∉ Γ D := by
  rw [Γ, graphIdeal, RingHom.mem_ker, graphMap_xc, C_eq_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
  exact X_ne_zero _

theorem x'_ne_zero {D : ℕ} (G : GenFibre (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) (Γ D))
    (p : Σ k, Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)) k) (hp : (X p : MRing _) ∉ Γ D) :
    G.x' p ≠ 0 := by
  intro h
  apply hp
  rw [← G.genericFibre_ker_target, RingHom.mem_ker, aeval_X]
  exact h

theorem ratio_mem {D : ℕ} (G : GenFibre (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) (Γ D))
    (i : Fin (D + 1)) : G.x' (xc i) / G.x' (xc 0) ∈ (⊥ : IntermediateField G.Φ G.Φ') := by
  have h0 := x'_ne_zero G _ (x_not_mem D 0)
  have h00 := x'_ne_zero G _ (veroneseFirstCoordinate_not_mem_graph D)
  have hr : aeval G.x' (X (xc 0) * X (yc 0 i (Fin.zero_le i)) - X (xc i) * X (yc 0 0 le_rfl) :
        MRing (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D)))) = 0 := by
    rw [← RingHom.mem_ker, G.genericFibre_ker_target]
    exact rel_mem D i
  simp only [map_sub, map_mul, aeval_X, sub_eq_zero] at hr
  have c1 : G.x' (yc 0 i (Fin.zero_le i)) = algebraMap G.Φ G.Φ' (G.x ⟨(), ⟨(0, i), Fin.zero_le i⟩⟩) :=
    G.compat ⟨(), ⟨(0, i), Fin.zero_le i⟩⟩
  have c2 : G.x' (yc 0 0 le_rfl) = algebraMap G.Φ G.Φ' (G.x ⟨(), ⟨(0, 0), le_rfl⟩⟩) :=
    G.compat ⟨(), ⟨(0, 0), le_rfl⟩⟩
  rw [IntermediateField.mem_bot]
  refine ⟨G.x ⟨(), ⟨(0, i), Fin.zero_le i⟩⟩ / G.x ⟨(), ⟨(0, 0), le_rfl⟩⟩, ?_⟩
  rw [map_div₀, ← c1, ← c2, div_eq_div_iff h00 h0]
  rw [mul_comm] at hr
  rw [hr, mul_comm]

end VeroneseGraphDeg


open VeroneseGraphDeg in
theorem VeroneseGraphDeg.proof (hGr : GraphStatement) (hImg : VeroneseGraphImage.Statement)
    (hDim : FibreDimStatement)
    (hEU : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι) :
    VeroneseGraphDeg.Statement := by
  intro D hD
  have hP : IsArithVar (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) (D + 1) := IndefiniteRowSideFullHecke.Inter.isArithVar_bot D
  have hnv : ∀ u : Unit, ∃ j, Veronese.forms D ⟨u, j⟩ ∉ (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) := by
    intro u
    refine ⟨⟨(0, 0), le_rfl⟩, ?_⟩
    rw [Ideal.mem_bot]
    exact mul_ne_zero (X_ne_zero _) (X_ne_zero _)
  have hΓ : IsArithVar (Γ D) (D + 1) :=
    (hGr Unit (GlobalTheory (Fin (D + 1))) Unit (GlobalTheory (Veronese.Idx D)) ⊥ (D + 1) (Veronese.forms D) (fun _ _ => 2) hP
      (isMultiHomog_forms D) hnv).1
  have hIm : IsArithVar (imageZ (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) (Γ D)) (D + 1) := by
    rw [Γ, hImg D]
    exact VeroneseArith.proof D hD
  have : (Γ D).IsPrime := hΓ.2.1.1
  let G : GenFibre (inrV (ι := GlobalTheory (Fin (D + 1))) (ι₂ := GlobalTheory (Veronese.Idx D))) (Γ D) := Inter.genFibreOf _ _
  obtain ⟨J, hJ, -⟩ := hEU G.Φ (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr)
  have hpt : IsProjVarF (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) 0 :=
    hDim Unit (GlobalTheory (Veronese.Idx D)) (Unit ⊕ Unit) (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr
      inrV _ (D + 1) 0 G isBlockMap_inr hΓ hIm

  let ch : (k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit)) →
      fibreIdx (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr k := fun
    | ⟨Sum.inl _, _⟩ => (0 : Fin (D + 1))
    | ⟨Sum.inr u, h⟩ => absurd ⟨u, rfl⟩ h
  have hz : ∀ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit), G.x' ⟨k.1, ch k⟩ ≠ 0 := by
    rintro ⟨(u | u), h⟩
    · cases u
      exact x'_ne_zero G _ (x_not_mem D 0)
    · exact absurd ⟨u, rfl⟩ h
  have hch : IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch := by
    intro k
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]
    exact hz k
  refine ⟨G, J, hJ, ?_⟩
  rw [hJ.1 _ _ _ hpt hch]
  have hdeg := Inter.ChartRankAdjoin.proof (FibreBlock (Sum.inr : Unit → Unit ⊕ Unit))
    (fibreIdx (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr) G.Φ G.Φ'
    (fun q => G.x' ⟨q.1.1, q.2⟩) ch hz hpt.1.2.1
  have hbot : IntermediateField.adjoin G.Φ (Set.range fun q : Σ k : FibreBlock (Sum.inr : Unit → Unit ⊕ Unit),
      fibreIdx (Sum.elim (GlobalTheory (Fin (D + 1))) (GlobalTheory (Veronese.Idx D))) Sum.inr k =>
        G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, ch q.1⟩) = ⊥ := by
    rw [eq_bot_iff, IntermediateField.adjoin_le_iff]
    rintro _ ⟨⟨⟨(u | u), h⟩, i⟩, rfl⟩
    · cases u
      exact ratio_mem G i
    · exact absurd ⟨u, rfl⟩ h
  change ((ptDeg (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) ch : ℕ) : ℤ) = 1
  rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, hdeg, hbot, IntermediateField.finrank_bot, Nat.cast_one]

end GroundTheory.Heights₂.Heights.HilbertSamuel

end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PBlockResolutionInterpIntegral
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Filter Topology

noncomputable section

namespace BlockResolutionInterpIntegral

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

theorem locDens_interp (d : HSMBlockDatum D K ι Ω) {A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA' : IsSmoothHerm A')
    (t : ℝ) (j : Fin d.R.A.n) {y : Fin D → ℂ} (hy : y ∈ (d.R.A.chart j).target) :
    locDens d.R.A (fun _ => blockInterpPot d d.A A' t) j y =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        locDens d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
          else AnResBridge.potOf d.R d.A) j y := by
  set x0 := (d.R.A.chart j).symm y with hx0
  set a : (Fin D → ℂ) → ℝ := fun y' => Real.log (d.A.h (d.R.lift x0 ((d.R.A.chart j).symm y'))) with ha
  set b : (Fin D → ℂ) → ℝ := fun y' => Real.log (A'.h (d.R.lift x0 ((d.R.A.chart j).symm y'))) with hb
  have hV : IsOpen ((d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x0) :=
    (d.R.A.chart j).isOpen_inter_preimage_symm (d.R.isOpen_U x0)
  have hyV : y ∈ (d.R.A.chart j).target ∩ (d.R.A.chart j).symm ⁻¹' d.R.U x0 := ⟨hy, d.R.mem_U x0⟩
  have hsm : ∀ {L : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}, IsSmoothHerm L → ∀ᶠ y' in 𝓝 y,
      ContDiffAt ℝ 2 (fun y'' => Real.log (L.h (d.R.lift x0 ((d.R.A.chart j).symm y'')))) y' := by
    intro L hL
    filter_upwards [hV.mem_nhds hyV] with y' hy'
    exact_mod_cast contDiffAt_infty.mp
      ((AnResBridge.contDiffOn_potOf d.R hL x0 j).contDiffAt (hV.mem_nhds hy')) 2
  have hH := gaamix_cxHessian_comb (ψ := fun y' => (1 - t) * a y' + t * b y') (1 - t) t
    (hsm d.semipos.1) (hsm hA') (Filter.EventuallyEq.refl _ _)
  set H₀ := cxHessian a y
  set H₁ := cxHessian b y
  have hL : locDens d.R.A (fun _ => blockInterpPot d d.A A' t) j y =
      ReciprocityTheory.AnForm.maDens (fun _ y' => (1 - t) * a y' + t * b y') y := rfl
  have hR : ∀ i, locDens d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
      else AnResBridge.potOf d.R d.A) j y =
      ReciprocityTheory.AnForm.maDens (fun k => if k.val < i then b else a) y := by
    intro i
    show ReciprocityTheory.AnForm.maDens _ y = _
    congr 1
    funext k y'
    by_cases hk : k.val < i
    · simp only [hk, if_true]; rfl
    · simp only [hk, if_false]; rfl
  have hpure : (fun _ : Fin D => ReciprocityTheory.AnForm.hessC (fun y' => (1 - t) * a y' + t * b y') y) =
      fun _ => (t : ℂ) • H₁ + (1 - (t : ℂ)) • H₀ := by
    funext k
    show cxHessian _ y = _
    rw [hH, add_comm]
    push_cast
    rfl
  have hmix : ∀ i, (fun k : Fin D => ReciprocityTheory.AnForm.hessC (if k.val < i then b else a) y) =
      fun k : Fin D => if k.val < i then H₁ else H₀ := by
    intro i
    funext k
    by_cases hk : k.val < i
    · simp only [hk, if_true]; rfl
    · simp only [hk, if_false]; rfl
  rw [hL]
  simp only [hR]
  unfold ReciprocityTheory.AnForm.maDens
  rw [hpure, ReciprocityTheory.AnForm.A.mdisc_const, ReciprocityTheory.AnForm.A.det_smul_add_smul_eq_sum_mdisc,
    Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hmix i]
  have e : (D.choose i : ℂ) * (t : ℂ) ^ i * (1 - (t : ℂ)) ^ (D - i) =
      ((D.choose i * t ^ i * (1 - t) ^ (D - i) : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.re_ofReal_mul]
  ring

theorem continuous_logRatio (d : HSMBlockDatum D K ι Ω) {A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hdeg : A'.a = unitDeg d.k₀)
    (hA' : IsSmoothHerm A') :
    Continuous fun x => Real.log (A'.h (blockPt d x) / d.A.h (blockPt d x)) := by
  have hA : IsSmoothHerm d.A := d.semipos.1
  have hE : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    have e : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z | z ⟨k, i⟩ ≠ 0} := by
      ext z; simp
    rw [e]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  have hΦ : ContinuousOn (fun z : (Σ k, ι k) → ℂ => Real.log (A'.h z / d.A.h z))
      {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (hA'.continuousOn.div hA.continuousOn fun z hz => (d.A.pos z hz).ne').log fun z hz =>
      (div_pos (A'.pos z hz) (d.A.pos z hz)).ne'
  have hdeg' : A'.a = d.A.a := hdeg.trans d.deg.symm
  refine continuous_iff_continuousAt.2 fun x₀ => ?_
  have hU := (d.R.isOpen_U x₀).mem_nhds (d.R.mem_U x₀)
  have hl : ContinuousAt (d.R.lift x₀) x₀ :=
    (continuousOn_pi.2 fun p => AnResBridge.continuousOn_lift d.R x₀ p).continuousAt hU
  have h0 : d.R.lift x₀ x₀ ∈ {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (d.R.mem x₀ x₀ (d.R.mem_U x₀)).1
  have h2 : ContinuousAt (fun x => Real.log (A'.h (d.R.lift x₀ x) / d.A.h (d.R.lift x₀ x))) x₀ :=
    (hΦ.continuousAt (hE.mem_nhds h0)).comp hl
  refine h2.congr ?_
  filter_upwards [hU] with x hx
  obtain ⟨c, hc0, he⟩ := d.R.compat x x₀ x ⟨d.R.mem_U x, hx⟩
  show _ = Real.log (A'.h (d.R.lift x x) / d.A.h (d.R.lift x x))
  have hp : (∏ k, ‖c k‖ ^ d.A.a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.mpr (hc0 k))
  rw [he, A'.smul c _ hc0, d.A.smul c _ hc0, hdeg', mul_div_mul_left _ _ hp]

theorem mInt_interp (d : HSMBlockDatum D K ι Ω) {A' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hdeg : A'.a = unitDeg d.k₀)
    (hA' : IsSmoothHerm A') (t : ℝ) :
    mInt d.R.A (fun _ => blockInterpPot d d.A A' t)
        (fun x => Real.log (A'.h (blockPt d x) / d.A.h (blockPt d x))) =
      ∑ i ∈ Finset.range (D + 1), (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
        mInt d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
            else AnResBridge.potOf d.R d.A)
          (fun x => Real.log (A'.h (blockPt d x) / d.A.h (blockPt d x))) := by
  have hg := continuous_logRatio d hdeg hA'
  have hΦ : ∀ (i : ℕ) (k : Fin D), IsPotential d.R.A
      (if k.val < i then AnResBridge.potOf d.R A' else AnResBridge.potOf d.R d.A) := by
    intro i k
    split_ifs
    · exact AnResBridge.isPotential_potOf d.R hA'
    · exact AnResBridge.isPotential_potOf d.R d.semipos.1
  unfold mInt
  by_cases hP : Nonempty (ChartPartition d.R.A)
  · simp only [dif_pos hP]
    unfold integralWith
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hint : ∀ i ∈ Finset.range (D + 1), Integrable (fun y =>
        (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
          (hP.some.χ j ((d.R.A.chart j).symm y) *
            Real.log (A'.h (blockPt d ((d.R.A.chart j).symm y)) / d.A.h (blockPt d ((d.R.A.chart j).symm y))) *
            locDens d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
              else AnResBridge.potOf d.R d.A) j y))
        (volume.restrict (d.R.A.chart j).target) := fun i _ =>
      (integrableOn_weight d.R.A hP.some _ _ (mIntegrableCont d.R.A _ (hΦ i) _ hg) j).const_mul _
    calc _ = ∫ y in (d.R.A.chart j).target, ∑ i ∈ Finset.range (D + 1),
          (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) *
            (hP.some.χ j ((d.R.A.chart j).symm y) *
              Real.log (A'.h (blockPt d ((d.R.A.chart j).symm y)) /
                d.A.h (blockPt d ((d.R.A.chart j).symm y))) *
              locDens d.R.A (fun k : Fin D => if k.val < i then AnResBridge.potOf d.R A'
                else AnResBridge.potOf d.R d.A) j y) := by
          refine setIntegral_congr_fun (d.R.A.chart j).open_target.measurableSet fun y hy => ?_
          rw [locDens_interp d hA' t j hy, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by
          rw [integral_finsetSum _ hint]
          exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  · simp only [dif_neg hP, mul_zero, Finset.sum_const_zero]

theorem proof : BlockResolutionInterpIntegral.Statement := by
  intro D K _ _ ι _ Ω _ _ d A' hdeg hA'
  unfold blockMetricInt
  simp only [mInt_interp d hdeg hA']
  rw [intervalIntegral.integral_finsetSum fun i _ =>
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [intervalIntegral.integral_mul_const,
    ReciprocityTheory.GeometryOfNumbersTheory.integral_bernstein D i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))]
  have hD : (D : ℝ) + 1 ≠ 0 := by positivity
  field_simp

end BlockResolutionInterpIntegral

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPowerBlockTop
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace PowerBlockTop

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def tensorPowH (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) : ℕ → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι
  | 0 => A
  | n + 1 => (tensorPowH A n).tensor A

omit [∀ k, Fintype (ι k)] in
theorem tensorPowH_a (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (n : ℕ) : (tensorPowH A n).a = fun k => ((n + 1 : ℕ) : ℤ) * A.a k := by
  induction n with
  | zero => funext k; simp [tensorPowH]
  | succ n ih =>
    funext k
    show (tensorPowH A n).a k + A.a k = _
    rw [ih]
    push_cast
    ring

omit [∀ k, Fintype (ι k)] in
theorem tensorPowH_h (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (n : ℕ) (z : (Σ k, ι k) → ℂ) : (tensorPowH A n).h z = A.h z ^ (n + 1) := by
  induction n with
  | zero => simp [tensorPowH]
  | succ n ih =>
    show (tensorPowH A n).h z * A.h z = _
    rw [ih, pow_succ _ (n + 1)]

theorem isSmoothHerm_tensorPowH {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (n : ℕ) : IsSmoothHerm (tensorPowH A n) := by
  induction n with
  | zero => exact hA
  | succ n ih => exact isSmoothHerm_tensor ih hA

theorem update_tensorPowH {I : AllFam} (hI : I.IsFamily) {P : Ideal (MRing ι)} {n : ℕ} (hP : IsArithVar P n)
    {L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hL : ∀ j, IsSmoothHerm (L j)) (j : Fin n) {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A)
    (t : ℕ) :
    I K ι P n (Function.update L j (tensorPowH A t)) = ((t + 1 : ℕ) : ℝ) * I K ι P n (Function.update L j A) := by
  induction t with
  | zero => simp [tensorPowH]
  | succ t ih =>
    have h := GroundTheory.Heights₂.Heights.Targets.ArithIntersectionSystem.multilin_of_isFamily hI K ι P n L j
      (tensorPowH A t) A hP hL (isSmoothHerm_tensorPowH hA t) hA
    show I K ι P n (Function.update L j ((tensorPowH A t).tensor A)) = _
    rw [h, ih]
    push_cast
    ring

theorem const_tensorPowH {I : AllFam} (hI : I.IsFamily) {P : Ideal (MRing ι)} {n : ℕ} (hP : IsArithVar P n)
    {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (t : ℕ) :
    I K ι P n (fun _ => tensorPowH A t) = ((t + 1 : ℕ) : ℝ) ^ n * I K ι P n (fun _ => A) := by
  classical
  let Lr : ℕ → Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun r i => if (i : ℕ) < r then tensorPowH A t else A
  have hLr : ∀ r j, IsSmoothHerm (Lr r j) := fun r j => by
    simp only [Lr]
    split_ifs
    · exact isSmoothHerm_tensorPowH hA t
    · exact hA
  have step : ∀ r, r ≤ n → I K ι P n (Lr r) = ((t + 1 : ℕ) : ℝ) ^ r * I K ι P n (Lr 0) := by
    intro r
    induction r with
    | zero => intro _; simp
    | succ r ih =>
      intro hr
      let j : Fin n := ⟨r, hr⟩
      have e1 : Lr (r + 1) = Function.update (Lr r) j (tensorPowH A t) := by
        funext i
        by_cases hi : i = j
        · subst hi; simp [Lr, j]
        · have : (i : ℕ) ≠ r := fun h => hi (Fin.ext h)
          rw [Function.update_of_ne hi]
          simp only [Lr]
          congr 1
          exact propext ⟨fun h => by omega, fun h => by omega⟩
      have e2 : Lr r = Function.update (Lr r) j A := by
        funext i
        by_cases hi : i = j
        · subst hi; simp [Lr, j]
        · rw [Function.update_of_ne hi]
      rw [e1, update_tensorPowH hI hP (hLr r) j hA t, ← e2, ih (by omega), pow_succ]
      ring
  have hn := step n le_rfl
  have e3 : Lr n = fun _ => tensorPowH A t := by funext i; simp [Lr, i.2]
  have e4 : Lr 0 = fun _ => A := by funext i; simp [Lr]
  rw [e3, e4] at hn
  exact hn


omit [∀ k, Fintype (ι k)] in
theorem blockFnField_addBlock {Ω : Type} [Field Ω] [CharZero Ω] {y : (Σ k, ι k) → Ω}
    {A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {m N : ℕ} {v : Fin N → Ω} (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0)
    (hv : ∀ j, v j ∈ chartLat y A.a m) : blockFnField (addBlock y v) = blockFnField y := by
  have hZ : ∀ s ∈ chartRingZ y c, s ∈ blockFnField y := by
    intro s hs
    have : chartRingZ y c ≤ (blockFnField y).toSubalgebra.restrictScalars ℤ := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨p, rfl⟩
      exact IntermediateField.subset_adjoin ℚ _ ⟨p, ⟨p.1, c p.1⟩, rfl, rfl⟩
    exact this hs
  apply le_antisymm
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro t ⟨⟨_ | k, i⟩, ⟨_ | k', i'⟩, hpq, rfl⟩
    · have hP0 : (∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k))) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
      have e : addBlock y v ⟨none, i⟩ / addBlock y v ⟨none, i'⟩ =
          (v i * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k))) / (v i' * ∏ k, y ⟨k, c k⟩ ^ (-((m : ℤ) * A.a k))) := by
        rw [mul_div_mul_right _ _ hP0]
        rfl
      rw [e]
      exact div_mem (hZ _ (hv i c hc)) (hZ _ (hv i' c hc))
    · exact absurd hpq (by simp)
    · exact absurd hpq (by simp)
    · obtain rfl : k = k' := Option.some_injective _ hpq
      exact IntermediateField.subset_adjoin ℚ _ ⟨⟨k, i⟩, ⟨k, i'⟩, rfl, rfl⟩
  · rw [blockFnField, IntermediateField.adjoin_le_iff]
    rintro t ⟨p, q, hpq, rfl⟩
    exact IntermediateField.subset_adjoin ℚ _ ⟨oldV N p, oldV N q, by simp [oldV, hpq], rfl⟩

end PowerBlockTop


open PowerBlockTop in
theorem PowerBlockTop.proof (hPF : PFCoordStatement) (hIso : IsomInvariance.Statement)
    (hAB : AddBlockIsometric.Statement) : PowerBlockTop.Statement := by
  classical
  intro K _ _ ι _ Ω _ _ y D A m N v B I hI hy hA hm hv hgen hBa hBs hmet

  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hy.2.1.2.2 k
    refine ⟨i, fun h0 => hi ?_⟩
    show mConeMap _ (X _) = 0
    simp [mConeMap, h0]
  choose c hc using hnz

  obtain ⟨j₀, hj₀⟩ : ∃ j, v j ≠ 0 := by
    obtain ⟨u, -, hu⟩ := hgen c hc
    by_contra h
    simp only [not_exists, not_not] at h
    simp [h] at hu
  have hFn := blockFnField_addBlock c hc hv
  have hbm := isBlockMap_oldV (ι := ι) N
  have hyv : IsArithVar (mCoordIdeal (addBlock y v)) (D + 1) :=
    CoordArithOfFnField.proof K ι (Option K) (addIdx ι N) Ω y (addBlock y v) (D + 1) ⟨none⟩
      (fun k => by
        cases k with
        | none => exact ⟨j₀, hj₀⟩
        | some k => exact ⟨c k, hc k⟩) hFn.symm hy
  have hcomp : addBlock y v ∘ oldV N = y := rfl
  have himg : imageZ (oldV N) (mCoordIdeal (addBlock y v)) = mCoordIdeal y := by
    rw [GroundTheory.Heights₂.Heights.Targets.ImageCoord.proof K ι (Option K) (addIdx ι N) some (oldV N) Ω (addBlock y v) hbm,
      hcomp]
  have hAm : IsSmoothHerm (tensorPowH A (m - 1)) := isSmoothHerm_tensorPowH hA _
  have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have hpull := GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.isPullHerm_pullHerm hbm (tensorPowH A (m - 1))

  have hPFe := hPF I hI K ι (Option K) (addIdx ι N) some (oldV N) Ω (addBlock y v) (D + 1)
    (fun _ => tensorPowH A (m - 1)) (fun _ => GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.pullHerm hbm (tensorPowH A (m - 1)))
    hbm hyv (by rw [himg]; exact hy) (fun _ => hAm) (fun _ => hpull)
  rw [IntermediateField.relfinrank_eq_one_iff.mpr (by rw [hcomp, hFn]), Nat.cast_one, one_mul, himg] at hPFe

  have hiso : ∀ _ : Fin (D + 1), IsIsometricOn (mCoordIdeal (addBlock y v)) B
      (GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.pullHerm hbm (tensorPowH A (m - 1))) := fun _ =>
    hAB K ι Ω y D A m N v B _ hy hm hv hgen hBa
      (by
        show pullDeg some (tensorPowH A (m - 1)).a = _
        rw [tensorPowH_a, hm'])
      (fun z => by
        show (tensorPowH A (m - 1)).h (fun p => z (oldV N p)) = _
        rw [tensorPowH_h, hm']
        rfl) hmet
  have e1 := hIso (Option K) (addIdx ι N) (I (Option K) (addIdx ι N)) (hI _ _) (mCoordIdeal (addBlock y v)) (D + 1)
    (fun _ => B) (fun _ => GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.pullHerm hbm (tensorPowH A (m - 1))) hyv (fun _ => hBs)
    (fun _ => GroundTheory.Heights₂.Heights.Inter.IsPullHerm.isSmoothHerm hbm hpull hAm) hiso
  rw [e1, hPFe, const_tensorPowH hI hy hA, hm']

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
