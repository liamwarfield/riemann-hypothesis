module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftBirationalNef
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSectionsDimZero
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsTwistIntersectionInt
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PEmbeddingWeight
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionsRank
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombLimit

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenDegAmple
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1

noncomputable section

namespace GenDegAmple

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem hilbFn_nonneg {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (m : K → ℤ) : 0 ≤ hilbFn q m := by
  unfold hilbFn
  split_ifs
  · exact Int.natCast_nonneg _
  · exact le_rfl

theorem eventualValue_nonneg {K : Type} [Fintype K] (f : (K → ℤ) → ℤ) (hf : ∀ m, 0 ≤ f m) :
    0 ≤ eventualValue f := by
  unfold eventualValue
  split_ifs with h
  · obtain ⟨m, hm⟩ := h.choose_spec.exists
    rw [← hm]
    exact hf m
  · exact le_rfl

theorem unit_nonneg {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
    [∀ k, Fintype (ι k)] (e : ℕ) : ∀ q : Ideal (MRing ι F), NumbersDVR.IsMultiProjPrime q →
    ringKrullDim (MRing ι F ⧸ q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) →
    ∀ r : Fin e → K, 0 ≤ intNum F q (fun j => unitDeg (r j)) := by
  induction e with
  | zero =>
    intro q _ _ r
    unfold intNum mixedDiff
    rw [List.ofFn_zero, List.foldr_nil]
    exact eventualValue_nonneg _ (hilbFn_nonneg q)
  | succ e ih =>
    intro q hq hd r
    obtain ⟨i, hX⟩ := hq.relevant (r 0)
    have hd' : ringKrullDim (MRing ι F ⧸ q) = ((e + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := hd
    have hsplit : (fun j : Fin (e + 1) => unitDeg (r j)) =
        Matrix.vecCons (unitDeg (r 0)) (fun j : Fin e => unitDeg (r j.succ)) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j <;> simp
    rw [hsplit, IntersectionRecursion.proof F K ι q e hq hd' (r 0) i hX]
    refine finsum_nonneg fun W => ?_
    split_ifs with h
    · exact mul_nonneg (Int.natCast_nonneg _) (ih W h.1 h.2.2 _)
    · exact le_rfl

end GenDegAmple

theorem GenDegAmple.proof (hVar : GenericFibreVar.Statement) (hPos : MultiDegreePositive.Statement) :
    GenDegAmple.Statement := by
  intro K _ ι _ Ω _ y D d hV hd
  classical
  have hPV := hVar K ι Ω y D hV
  have hP := (Bridge.isMultiProjPrime_iff _).mpr hPV.1
  have hrel : FieldNumbers.relDim (KH.genIdeal y) = D := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq _ _ hPV.2]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  set f := intNumMultilinear (KH.genIdeal y) D hP.multiHomog hP.relevant hrel with hf
  have hg : ∀ b, genDeg (mCoordIdeal y) D b = f (fun _ => b) := fun b => by
    rw [hf, intNumMultilinear_apply, genDeg]
    congr
  have hN : ∀ r : Fin D → K, 0 ≤ f (fun j => unitDeg (r j)) := fun r => by
    rw [hf, intNumMultilinear_apply]
    exact GenDegAmple.unit_nonneg D _ hP hPV.2 r
  have hH : 0 < f (fun _ => fun _ => (1 : ℤ)) := by
    rw [hf, intNumMultilinear_apply]
    exact hPos ℚ K ι _ D hP hPV.2
  have hsum : ∀ b : K → ℤ, (fun _ : Fin D => b) = fun _ => ∑ k, b k • unitDeg k := fun b => by
    funext _ k'
    simp [unitDeg, Finset.sum_apply, Pi.single_apply]
  have expand : ∀ b : K → ℤ,
      f (fun _ => b) = ∑ r : Fin D → K, (∏ j, b (r j)) * f (fun j => unitDeg (r j)) := fun b => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hsum b, f.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [f.map_smul_univ (fun j => b (r j)) (fun j => unitDeg (r j)), smul_eq_mul]
    simp only [RingHom.id_apply]
  rw [hg, expand d]
  have hH' := hH
  rw [expand (fun _ => (1 : ℤ))] at hH'
  simp only [Finset.prod_const_one, one_mul] at hH'
  refine lt_of_lt_of_le hH' (Finset.sum_le_sum fun r _ => ?_)
  have hp : (1 : ℤ) ≤ ∏ j, d (r j) := by
    calc (1 : ℤ) = ∏ _j : Fin D, (1 : ℤ) := Finset.prod_const_one.symm
      _ ≤ ∏ j, d (r j) := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun j _ => hd (r j))
  exact le_mul_of_one_le_left (hN r) hp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ImportsTer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory

noncomputable section

theorem L2GramLattice.proof : L2GramLattice.Statement := by
  intro E _ _ _ X _ μ _ w hmeas hbdd hind
  classical
  set n := Module.finrank ℤ E
  let b : Module.Basis (Fin n) ℤ E := Module.finBasis ℤ E
  have hmem : ∀ s, MemLp (w s) 2 μ := fun s => by
    obtain ⟨C, hC⟩ := hbdd s
    exact (memLp_top_of_bound (hmeas s) C hC).mono_exponent le_top
  let F : Fin n → Lp ℂ 2 μ := fun i => (hmem (b i)).toLp _
  let ψ : (Fin n → ℝ) →ₗ[ℝ] Lp ℂ 2 μ :=
    { toFun := fun c => ∑ i, c i • F i
      map_add' := fun c d => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun a c => by simp [Finset.smul_sum, smul_smul] }

  have hψ : ∀ c : Fin n → ℝ, (ψ c : X → ℂ) =ᵐ[μ] fun z => ∑ i, (c i : ℂ) * w (b i) z := by
    intro c
    show ((∑ i, c i • F i : Lp ℂ 2 μ) : X → ℂ) =ᵐ[μ] _
    induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      filter_upwards [Lp.coeFn_zero ℂ 2 μ] with z h
      rw [h]
      rfl
    | insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      filter_upwards [Lp.coeFn_add (c i • F i) (∑ j ∈ s, c j • F j), Lp.coeFn_smul (c i) (F i),
        (hmem (b i)).coeFn_toLp, ih] with z h1 h2 h3 h4
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, h3, h4, Complex.real_smul]
  have hinj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    apply hind n b b.linearIndependent c
    filter_upwards [hψ c, hc ▸ Lp.coeFn_zero ℂ 2 μ] with z h1 h2
    rw [← h1]
    exact h2

  have hcoord : ∀ s : E, ψ (fun i => (b.equivFun s i : ℝ)) = (hmem s).toLp _ := by
    intro s
    ext1
    filter_upwards [hψ (fun i => (b.equivFun s i : ℝ)), (hmem s).coeFn_toLp] with z h1 h2
    have hs : w s = ∑ i, b.repr s i • w (b i) := by
      conv_lhs => rw [← b.sum_repr s]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [map_zsmul]
    rw [h1, h2, hs, Finset.sum_apply]
    simp [zsmul_eq_mul]
  let W := LinearMap.range ψ
  let e₁ : (Fin n → ℝ) ≃ₗ[ℝ] W := LinearEquiv.ofInjective ψ hinj
  have hW : Module.finrank ℝ W = n := by
    rw [← e₁.finrank_eq, Module.finrank_fin_fun]
  let o := (stdOrthonormalBasis ℝ W).reindex (finCongr hW)
  let T : (Fin n → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) := e₁.trans o.repr.toLinearEquiv
  have hT : ∀ c, ‖T c‖ = ‖ψ c‖ := by
    intro c
    simp only [T, e₁, LinearEquiv.trans_apply, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.norm_map]
    rw [Submodule.coe_norm, LinearEquiv.ofInjective_apply]
  let cast : (Fin n → ℤ) →+ (Fin n → ℝ) := AddMonoidHom.compLeft (Int.castAddHom ℝ) (Fin n)
  let φ : E →+ EuclideanSpace ℝ (Fin n) :=
    (T.toLinearMap.toAddMonoidHom.comp cast).comp b.equivFun.toLinearMap.toAddMonoidHom
  have hφ : ∀ s, φ s = T (fun i => (b.equivFun s i : ℝ)) := fun s => rfl
  let v : Module.Basis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)) := (Pi.basisFun ℝ (Fin n)).map T
  have hφb : ∀ i, φ (b i) = v i := by
    intro i
    rw [hφ]
    simp only [v, Module.Basis.map_apply, Pi.basisFun_apply, Module.Basis.equivFun_self]
    congr 1
    funext j
    by_cases h : i = j <;> simp [h, eq_comm]
  have hL : imageLattice φ = Submodule.span ℤ (Set.range v) := by
    apply le_antisymm
    · rintro _ ⟨s, rfl⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← b.sum_repr s, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_zsmul, hφb]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨b i, hφb i⟩
  have key : ∀ L : Submodule ℤ (EuclideanSpace ℝ (Fin n)), L = Submodule.span ℤ (Set.range v) →
      DiscreteTopology L ∧ ∀ [DiscreteTopology L], IsZLattice ℝ L := by
    rintro _ rfl
    exact ⟨inferInstance, by intro _; infer_instance⟩
  refine ⟨φ, ?_, (key _ hL).1, (key _ hL).2, ?_⟩
  · intro s t hst
    rw [hφ, hφ] at hst
    apply b.equivFun.injective
    funext i
    exact_mod_cast congrFun (T.injective hst) i
  · intro s
    rw [hφ, hT, hcoord, Lp.norm_toLp,
      MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top (hmem s),
      ENNReal.toReal_ofReal (by positivity), Real.sqrt_eq_rpow]
    norm_num

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSupBoundBlock
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MeasureTheory Filter Topology

noncomputable section

section Invariance

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem SupBoundBlock.eval_torus_blockDeg {f : MRing ι} {k₀ : K} {n : ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (blockDeg k₀ n))
    (c : K → ℂ) (z : (Σ k, ι k) → ℂ) :
    eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) f) =
      c k₀ ^ n * eval z (map (Int.castRingHom ℂ) f) := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hf m (support_map_subset _ _ hm)
  have hc : ∏ p : (Σ k, ι k), c p.1 ^ m p = c k₀ ^ n := by
    rw [Fintype.prod_sigma]
    simp_rw [Finset.prod_pow_eq_pow_sum, hdeg]
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [blockDeg, hk]]
    simp [blockDeg]
  simp_rw [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem SupBoundBlock.normRatio_torus {f : MRing ι} {k₀ : K} {n : ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f (blockDeg k₀ n)) (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι)
    (hA : A.a = unitDeg k₀) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    ‖eval z (map (Int.castRingHom ℂ) f)‖ / A.h z ^ n = ‖eval z' (map (Int.castRingHom ℂ) f)‖ / A.h z' ^ n := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [SupBoundBlock.eval_torus_blockDeg hf, A.smul c z' hc, hA]
  have hprod : ∏ k, ‖c k‖ ^ unitDeg k₀ k = ‖c k₀‖ := by
    rw [Fintype.prod_eq_single k₀ fun k hk => by simp [unitDeg, hk]]
    simp [unitDeg]
  rw [hprod, norm_mul, norm_pow, mul_pow]
  have : ‖c k₀‖ ^ n ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 (hc k₀))
  rw [mul_div_mul_left _ _ this]


omit [DecidableEq K] [∀ k, Fintype (ι k)] in
theorem SupBoundBlock.isOpen_blockNonzero : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

end Invariance

theorem SupBoundBlock.proof (hS : SupNormAgainstL2.Statement) (hR : ResolutionPullback.Statement)
    (hN : NonvanishingDense.Statement) : SupBoundBlock.Statement := by
  intro D K _ _ ι _ Ω _ _ d
  obtain ⟨A, L, W, dV, -, hW, hμ, hsec⟩ := hR D K ι Ω d
  obtain ⟨⟨C, hC⟩, -⟩ := hS A L W dV hW
  refine ⟨max C 0 * Real.sqrt 2, fun n hn f hf z hz => ?_⟩
  set g : ((Σ k, ι k) → ℂ) → ℝ := fun w => ‖eval w (map (Int.castRingHom ℂ) f)‖ / d.A.h w ^ n with hg
  set M := max C 0 * Real.sqrt 2 * (n : ℝ) ^ ((D : ℝ) / 2) * blockL2Norm d n f with hM
  obtain ⟨s, hs, hps⟩ := hsec n f hf

  have hL2 : Real.sqrt (sectionL2NormSq W dV n s) ≤ Real.sqrt 2 * blockL2Norm d n f := by
    have hI : sectionL2NormSq W dV n s = ∫ x, g (blockPt d x) ^ 2 ∂d.dV := by
      rw [sectionL2NormSq, hμ]
      exact integral_congr_ae (Eventually.of_forall hps)
    have h2 : 0 ≤ ∫ x, (‖eval (conjPt (blockPt d x)) (map (Int.castRingHom ℂ) f)‖ /
        d.A.h (conjPt (blockPt d x)) ^ n) ^ 2 ∂d.dV := integral_nonneg fun _ => sq_nonneg _
    rw [hI, blockL2Norm, ← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    linarith
  have hpow : Real.sqrt ((n : ℝ) ^ D) = (n : ℝ) ^ ((D : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n)]
    ring_nf

  have hres : ∀ x, g (blockPt d x) ≤ M := by
    intro x
    have h1 : g (blockPt d x) ≤ Real.sqrt (ptNormSq W n s x) := by
      rw [hps x, Real.sqrt_sq_eq_abs]
      exact le_abs_self _
    have h3 := hC n hn s hs x
    rw [hpow] at h3
    have ha : 0 ≤ (n : ℝ) ^ ((D : ℝ) / 2) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    calc g (blockPt d x) ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * Real.sqrt (sectionL2NormSq W dV n s) := h1.trans h3
      _ ≤ max C 0 * (n : ℝ) ^ ((D : ℝ) / 2) * Real.sqrt (sectionL2NormSq W dV n s) := by
          gcongr
          exact le_max_left _ _
      _ ≤ max C 0 * (n : ℝ) ^ ((D : ℝ) / 2) * (Real.sqrt 2 * blockL2Norm d n f) := by
          gcongr
      _ = M := by rw [hM]; ring

  have hoff : ∀ w ∈ mcPts (mCoordIdeal d.y), w ∉ mcPts d.J → g w ≤ M := by
    intro w hw hwJ
    obtain ⟨x, hx⟩ := d.R.surj w hw hwJ
    calc g w = g (blockPt d x) := (SupBoundBlock.normRatio_torus hf d.A d.deg hx).symm
      _ ≤ M := hres x

  obtain ⟨F, hFJ, hFP⟩ := SetLike.not_le_iff_exists.1 d.R.nondeg
  set S := {w | w ∈ mcPts (mCoordIdeal d.y) ∧ eval w (map (Int.castRingHom ℂ) F) ≠ 0} with hSdef
  have hcl : z ∈ closure S := hN K ι (mCoordIdeal d.y) (D + 1) F d.arith hFP hz
  have hSM : ∀ w ∈ S, g w ≤ M := fun w hw => hoff w hw.1 fun hJ => hw.2 (hJ.2 F hFJ)
  have hcont : ContinuousAt g z := by
    have hh : ContinuousAt d.A.h z :=
      d.semipos.1.continuousOn.continuousAt (SupBoundBlock.isOpen_blockNonzero.mem_nhds hz.1)
    exact (continuous_norm.comp (MvPolynomial.continuous_eval _)).continuousAt.div (hh.pow n)
      (pow_ne_zero _ (d.A.pos z hz.1).ne')
  have := mem_closure_iff_nhdsWithin_neBot.1 hcl
  exact le_of_tendsto (hcont.tendsto.mono_left nhdsWithin_le_nhds) (eventually_nhdsWithin_of_forall hSM)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSpanStepLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace SpanStepLocal

def powMulSub {Ω : Type*} [Field Ω] (R : Subalgebra ℤ Ω) (v : Ω) (hv : v ∈ R) : Subalgebra ℤ Ω where
  carrier := {x | ∃ E : ℕ, x * v ^ E ∈ R}
  mul_mem' := by
    rintro x z ⟨E₁, h₁⟩ ⟨E₂, h₂⟩
    refine ⟨E₁ + E₂, ?_⟩
    have e : x * z * v ^ (E₁ + E₂) = (x * v ^ E₁) * (z * v ^ E₂) := by ring
    rw [e]; exact R.mul_mem h₁ h₂
  add_mem' := by
    rintro x z ⟨E₁, h₁⟩ ⟨E₂, h₂⟩
    refine ⟨E₁ + E₂, ?_⟩
    have e : (x + z) * v ^ (E₁ + E₂) = (x * v ^ E₁) * v ^ E₂ + (z * v ^ E₂) * v ^ E₁ := by ring
    rw [e]; exact R.add_mem (R.mul_mem h₁ (R.pow_mem hv _)) (R.mul_mem h₂ (R.pow_mem hv _))
  algebraMap_mem' r := ⟨0, by rw [pow_zero, mul_one]; exact R.algebraMap_mem r⟩

theorem pow_twist {K : Type*} [Fintype K] {ι : K → Type*} {Ω : Type*} [Field Ω] (y : (Σ k, ι k) → Ω)
    (a : K → ℤ) (c : ∀ k, ι k) (g w : Ω) (n : ℕ) :
    g * w ^ n * ∏ k, y ⟨k, c k⟩ ^ (-((n : ℤ) * a k)) = g * (w * ∏ k, y ⟨k, c k⟩ ^ (-a k)) ^ n := by
  rw [mul_pow, ← Finset.prod_pow, mul_assoc]
  congr 3; funext k
  rw [← zpow_natCast, ← zpow_mul]; ring_nf

end SpanStepLocal


open SpanStepLocal in
theorem SpanStepLocal.proof (hR : RelLatticeFinite.Statement) : SpanStepLocal.Statement := by
  intro K _ ι _ Ω _ y a q w hy hw hgen j hj
  classical
  set P := Algebra.adjoin ℤ (Set.range fun i => w i / w j) with hPdef

  set v : (∀ k, ι k) → Fin q → Ω := fun c i => w i * ∏ k, y ⟨k, c k⟩ ^ (-a k) with hvdef
  have hv : ∀ c, (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ i, v c i ∈ chartRingZ y c := fun c hc i => by
    simpa [hvdef] using hw i c hc
  have hv0 : ∀ c, (∀ k, y ⟨k, c k⟩ ≠ 0) → v c j ≠ 0 := fun c hc =>
    mul_ne_zero hj (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k))
  have hquot : ∀ c i, w i / w j * v c j = v c i := fun c i => by
    simp only [hvdef]; rw [← mul_assoc, div_mul_cancel₀ _ hj]
  have hrel : ∀ (g : Ω) (c : ∀ k, ι k), (∀ k, y ⟨k, c k⟩ ≠ 0) → (g ∈ Algebra.adjoin P
      (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) ↔
      g * ∏ k, y ⟨k, c k⟩ ^ (-(((0 : ℕ) : ℤ) * (fun _ => (0 : ℤ)) k)) ∈ Algebra.adjoin P
      (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) := fun g c _ => by simp

  have incl₁ : ∀ (g : Ω) (n : ℕ), g * w j ^ n ∈ chartLat y a n → g ∈ relChartLat P y (fun _ => 0) 0 := by
    intro g n hg c hc
    rw [← hrel g c hc]
    set S := Algebra.adjoin P (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)
    have hRS : ∀ x ∈ chartRingZ y c, x ∈ S := fun x hx =>
      (Algebra.adjoin_le Algebra.subset_adjoin : chartRingZ y c ≤ S.restrictScalars ℤ) hx
    have hPS : ∀ x ∈ P, x ∈ S := fun x hx => S.algebraMap_mem (⟨x, hx⟩ : P)
    obtain ⟨u, hu, hsum⟩ := hgen c hc
    have hinv : (∑ i, u i * (w i / w j)) = (v c j)⁻¹ := by
      refine eq_inv_of_mul_eq_one_left ?_
      rw [Finset.sum_mul, ← hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [mul_assoc, hquot]
    have hinvS : (v c j)⁻¹ ∈ S := hinv ▸ S.sum_mem fun i _ =>
      S.mul_mem (hRS _ (hu i)) (hPS _ (Algebra.subset_adjoin ⟨i, rfl⟩))
    have hgv : g * v c j ^ n ∈ S := hRS _ (by rw [← pow_twist]; exact hg c hc)
    have e : g = g * v c j ^ n * (v c j)⁻¹ ^ n := by
      rw [mul_assoc, ← mul_pow, mul_inv_cancel₀ (hv0 c hc), one_pow, mul_one]
    rw [e]; exact S.mul_mem hgv (S.pow_mem hinvS n)
  have incl₂ : ∀ g ∈ relChartLat P y (fun _ => 0) 0, ∃ n : ℕ, g * w j ^ n ∈ chartLat y a n := by
    intro g hg
    have hE : ∀ c, ∃ E : ℕ, (∀ k, y ⟨k, c k⟩ ≠ 0) → g * v c j ^ E ∈ chartRingZ y c := by
      intro c
      by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
      swap; · exact ⟨0, fun h => absurd h hc⟩
      have hgS := (hrel g c hc).2 (hg c hc)
      have hg' : g ∈ Algebra.adjoin ℤ ((Set.range fun i => w i / w j) ∪
          Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) := by
        rw [Algebra.adjoin_union_eq_adjoin_adjoin]; exact hgS
      have hle : Algebra.adjoin ℤ ((Set.range fun i => w i / w j) ∪
          Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) ≤ powMulSub _ _ (hv c hc j) := by
        refine Algebra.adjoin_le (Set.union_subset ?_ ?_)
        · rintro _ ⟨i, rfl⟩; exact ⟨1, by rw [pow_one, hquot]; exact hv c hc i⟩
        · rintro _ ⟨p, rfl⟩; exact ⟨0, by rw [pow_zero, mul_one]; exact Algebra.subset_adjoin ⟨p, rfl⟩⟩
      obtain ⟨E, hE⟩ := hle hg'
      exact ⟨E, fun _ => hE⟩
    choose E hE using hE
    refine ⟨∑ c, E c, fun c hc => ?_⟩
    rw [pow_twist]
    have e : g * v c j ^ (∑ c, E c) = g * v c j ^ E c * v c j ^ (∑ c, E c - E c) := by
      rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ c))]
    rw [e]; exact (chartRingZ y c).mul_mem (hE c hc) ((chartRingZ y c).pow_mem (hv c hc j) _)

  obtain ⟨r, b, hb⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (hR K ι Ω y (fun _ => 0) 0 q (fun i => w i / w j) hy)
  have hbmem : ∀ l, b l ∈ relChartLat P y (fun _ => 0) 0 := fun l =>
    hb ▸ Submodule.subset_span ⟨l, rfl⟩
  refine ⟨r, b, fun l => incl₂ _ (hbmem l), fun g n hg => ?_⟩
  have hgN := incl₁ g n hg
  rw [← hb, Submodule.mem_span_range_iff_exists_fun] at hgN
  obtain ⟨c, hc⟩ := hgN
  exact ⟨fun l => (c l : Ω), fun l => (c l).2, by rw [← hc]; rfl⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPiecesAdditive
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology Set MeasureTheory Manifold EmbeddingWeight

noncomputable section

namespace PiecesAdditiveAlt

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_weight {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {J : Type} [Fintype J]
    {S : J → Set ((Σ k, ι k) → ℂ)} (hS : ∀ i, IsClosed (S i))
    (hsm : ∀ i (t : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, t k ≠ 0) → z ∈ S i →
      (fun p => t p.1 * z p) ∈ S i)
    (huniq : ∀ z ∈ mcPts P, ∃! i, z ∈ S i) (i : J) :
    ∃ u : ((Σ k, ι k) → ℂ) → ℝ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} ∧
      (∀ (c : K → ℂ) z, (∀ k, c k ≠ 0) → u (fun p => c p.1 * z p) = u z) ∧
      ∀ z ∈ mcPts P, u z = (S i).indicator (fun _ => (1 : ℝ)) z := by
  classical
  let T : J → Set ((Σ k, ι k) → ℂ) := fun j => mcPts P ∩ S j ∩ {z | ∀ k, blockNormSq z k = 1}
  let C : J → Set ((Σ k, ι k × ι k) → ℂ) := fun j => projPt '' T j
  have hT : ∀ j, IsCompact (T j) := by
    intro j
    refine isCompact_sphere.of_isClosed_subset ?_ inter_subset_right
    have : T j = ({z | ∀ f ∈ P, eval z (map (Int.castRingHom ℂ) f) = 0} ∩ S j) ∩
        {z | ∀ k, blockNormSq z k = 1} := by
      ext z
      simp only [T, mcPts, mem_inter_iff, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨⟨-, h1⟩, h2⟩, h3⟩
        exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨⟨⟨fun k => ?_, h1⟩, h2⟩, h3⟩
        by_contra hcon
        push Not at hcon
        have := h3 k
        simp [blockNormSq, hcon] at this
    rw [this]
    exact ((isClosed_zeros P).inter (hS j)).inter isCompact_sphere.isClosed
  have hC : ∀ j, IsCompact (C j) := fun j =>
    (hT j).image_of_continuousOn (contDiffOn_projPt.continuousOn.mono fun z hz => hz.1.1.1)
  have hmem : ∀ j, ∀ z ∈ mcPts P, z ∈ S j → projPt z ∈ C j := by
    intro j z hz hzj
    obtain ⟨c, hc, hc1⟩ := exists_smul_sphere hz.1
    exact ⟨_, ⟨⟨mcPts_smul hP c hc hz, hsm j c z hc hzj⟩, hc1⟩, projPt_smul c hc z⟩
  have hdisj : ∀ j j', j ≠ j' → Disjoint (C j) (C j') := by
    intro j j' hne
    rw [Set.disjoint_left]
    rintro e ⟨z, ⟨⟨hzP, hzs⟩, -⟩, rfl⟩ ⟨w, ⟨⟨hwP, hwt⟩, -⟩, hw⟩
    obtain ⟨c, hc, rfl⟩ := exists_smul_of_projPt_eq hzP.1 hwP.1 hw.symm
    exact hne ((huniq _ hwP).unique (hsm j c z hc hzs) hwt)
  obtain ⟨f, h0, h1, -⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    𝓘(ℝ, (Σ k, ι k × ι k) → ℂ) (n := ⊤)
    (isClosed_biUnion_finset fun j _ => (hC j).isClosed) (hC i).isClosed
    (Set.disjoint_iUnion₂_left.2 fun j hj => hdisj j i (Finset.ne_of_mem_erase hj))
  refine ⟨fun z => f (projPt z), ?_, fun c z hc => by simp only [projPt_smul c hc], ?_⟩
  · exact (contMDiff_iff_contDiff.mp f.contMDiff).comp_contDiffOn contDiffOn_projPt
  · intro z hz
    obtain ⟨j, hj, -⟩ := huniq z hz
    by_cases hji : j = i
    · subst hji
      rw [Set.indicator_of_mem hj]
      exact h1.self_of_nhdsSet _ (hmem j z hz hj)
    · have hzi : z ∉ S i := fun h => hji ((huniq z hz).unique hj h)
      rw [Set.indicator_of_notMem hzi]
      exact h0.self_of_nhdsSet _
        (Set.mem_iUnion₂.2 ⟨j, Finset.mem_erase.2 ⟨hji, Finset.mem_univ _⟩, hmem j z hz hj⟩)


omit [∀ k, Fintype (ι k)] in
theorem sheetDensity_sum (P : Ideal (MRing ι)) {e : ℕ}
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    {J : Type} [Fintype J] (c : J → ℝ) (g : J → ((Σ k, ι k) → ℂ) → ℝ) (y : Fin e → ℂ)
    (w : ((k : K) → ι k) → ℂ) :
    sheetDensity P Ψ φ (fun z => ∑ i, c i * g i z) y w = ∑ i, c i * sheetDensity P Ψ φ (g i) y w := by
  unfold sheetDensity
  split_ifs with hγ
  · rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  · simp

theorem integrable_piece (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hL : ∀ j, IsSmoothHerm (L j))
    {J : Type} [Fintype J] {S : J → Set ((Σ k, ι k) → ℂ)} (hS : ∀ i, IsClosed (S i))
    (hsm : ∀ i (t : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, t k ≠ 0) → z ∈ S i →
      (fun p => t p.1 * z p) ∈ S i)
    (huniq : ∀ z ∈ mcPts P, ∃! i, z ∈ S i) (i : J) :
    Integrable (fun y => ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P Ψ y,
      sheetDensity P Ψ (pot L) ((S i).indicator fun _ => (1 : ℝ)) y w) := by
  obtain ⟨u, hus, hui, hu⟩ := exists_weight hP.2.1.2.1 hS hsm huniq i
  let B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight u hui
  have hB : IsSmoothHerm B := Real.contDiff_exp.comp_contDiffOn hus.neg
  have hlog : ∀ z, logNorm B 1 z = u z := by
    intro z
    simp [logNorm, B, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight]
  have hhom : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (1 : MRing ι) 0 := by
    intro m hm k
    rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
    subst hm
    simp
  have hnot : (1 : MRing ι) ∉ P := fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).2 h)
  have hsec : IsSectionOn P B 1 := ⟨0, fun k => by simp [B, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.ofWeight], hhom, hnot⟩
  refine (hInt K ι P e Ψ L B 1 hP hΨ hL hB hsec).congr (Eventually.of_forall fun y => ?_)
  refine finsum_mem_congr rfl fun w _ => ?_
  exact GroundTheory.Heights₂.Heights.Inter.DiagRAux.sheetDensity_congr_mcPts P Ψ (fun _ _ _ => rfl)
    (fun z hz => (hlog z).trans (hu z hz)) y w

end PiecesAdditiveAlt


open PiecesAdditiveAlt in
theorem PiecesAdditive.proof (hInt : PtsIntegrableStatement) : PiecesAdditive.Statement := by
  intro K _ ι _ P e L J _ S c hP hL hS hsm huniq
  classical
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have hlin : ∀ y, (∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P hΨ.choose y, sheetDensity P hΨ.choose (pot L)
        (fun z => ∑ i, c i * (S i).indicator (fun _ => (1 : ℝ)) z) y w) =
        ∑ i, c i * ∑ᶠ w ∈ ReciprocityTheory.ChartRestriction.G.Geo.fibre P hΨ.choose y,
          sheetDensity P hΨ.choose (pot L) ((S i).indicator fun _ => (1 : ℝ)) y w := by
      intro y
      have hfin := fibreFinite K ι P e _ hP hΨ.choose_spec y
      simp only [finsum_mem_eq_finite_toFinset_sum _ hfin, sheetDensity_sum, Finset.mul_sum]
      exact Finset.sum_comm
    simp only [hlin]
    rw [integral_finsetSum _ fun i _ =>
      (integrable_piece hInt hP hΨ.choose_spec hL hS hsm huniq i).const_mul (c i)]
    simp only [integral_const_mul]
  · simp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseGenDeg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter fwdDiff
open scoped Pointwise

noncomputable section

namespace VeroneseGenDeg

theorem finrank_homog (D n : ℕ) :
    Module.finrank ℤ (homogeneousSubmodule (Fin (D + 1)) ℤ n) = (n + D).choose D := by
  have hs : {d : Fin (D + 1) →₀ ℕ | d.degree = n} =
      ((Finset.univ.finsuppAntidiag n : Finset (Fin (D + 1) →₀ ℕ)) : Set (Fin (D + 1) →₀ ℕ)) := by
    ext d; simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported, hs,
    (AddMonoidAlgebra.supportedEquivFinsupp _).finrank_eq, Module.finrank_finsupp_self]
  simp only [Finset.coe_sort_coe, Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose,
    Finset.card_univ, Fintype.card_fin]
  rw [show D + 1 + n - 1 = n + D by omega]
  exact Nat.choose_symm_add

theorem range_alt (D : ℕ) : Set.range (Veronese.x D) = Set.range (Veronese.t D) ^ 2 := by
  ext y
  rw [pow_two, Set.mem_mul]
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨_, ⟨_, rfl⟩, _, ⟨_, rfl⟩, rfl⟩
  · rintro ⟨a, ⟨i, rfl⟩, b, ⟨j, rfl⟩, rfl⟩
    rcases le_total i j with hij | hij
    · exact ⟨⟨(), ⟨(i, j), hij⟩⟩, rfl⟩
    · exact ⟨⟨(), ⟨(j, i), hij⟩⟩, mul_comm _ _⟩

theorem aeval_t_injective (D : ℕ) :
    Function.Injective (aeval (Veronese.t D) : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] Veronese.Fld D) := by
  have h : (aeval (Veronese.t D) : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] Veronese.Fld D).toRingHom =
      (algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D)).comp
        (MvPolynomial.map (Int.castRingHom ℚ)) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp
    · simp [Veronese.t]
  have hinj : Function.Injective ((algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D)).comp
      (MvPolynomial.map (Int.castRingHom ℚ))) :=
    (IsFractionRing.injective (MvPolynomial (Fin (D + 1)) ℚ) (Veronese.Fld D)).comp
      (MvPolynomial.map_injective _ (RingHom.injective_int _))
  rw [← h] at hinj
  exact hinj

theorem finrank_sec (D n : ℕ) :
    Module.finrank ℤ (sec ℤ (Veronese.x D) n) = (2 * n + D).choose D := by
  have h1 : sec ℤ (Veronese.x D) n = sec ℤ (Veronese.t D) (2 * n) := by
    rw [SectionsRank.sec_eq_span, SectionsRank.sec_eq_span, range_alt, ← pow_mul]
  rw [h1, ← finrank_homog D (2 * n)]
  exact (Submodule.equivMapOfInjective _ (aeval_t_injective D) _).finrank_eq.symm

theorem mixedDiff_const {K : Type*} (D : ℕ) (b : K → ℤ) (h : (K → ℤ) → ℤ) :
    GroundTheory.Heights₂.Heights.NumbersDVR.mixedDiff (fun _ : Fin D => b) h =
      (GroundTheory.Heights₂.Heights.NumbersDVR.diffStep b)^[D] h := by
  unfold GroundTheory.Heights₂.Heights.NumbersDVR.mixedDiff
  rw [List.ofFn_const]
  induction D with
  | zero => rfl
  | succ D ih => rw [List.replicate_succ, List.foldr_cons, ih, Function.iterate_succ_apply']

theorem iterate_diffStep (D : ℕ) (H : (Unit → ℤ) → ℤ) (k : ℤ) :
    (GroundTheory.Heights₂.Heights.NumbersDVR.diffStep 1)^[D] H (fun _ => k) =
      (fwdDiff (1 : ℤ))^[D] (fun j : ℤ => H (fun _ => j)) (k - D) := by
  induction D generalizing H with
  | zero => simp
  | succ D ih =>
    rw [Function.iterate_succ_apply, ih]
    have hg : (fun j : ℤ => GroundTheory.Heights₂.Heights.NumbersDVR.diffStep 1 H (fun _ => j)) =
        fun j : ℤ => fwdDiff 1 (fun j : ℤ => H (fun _ => j)) (j + -1) := by
      funext j
      have e1 : (fun _ : Unit => j + -1 + 1) = fun _ => j := by funext u; ring
      have e2 : ((fun _ : Unit => j) - 1) = fun _ => j + -1 := by funext u; simp; ring
      simp only [GroundTheory.Heights₂.Heights.NumbersDVR.diffStep, fwdDiff, e1, e2]
    rw [hg, fwdDiff_iter_comp_add, ← Function.iterate_succ_apply,
      show k - (D : ℤ) + -1 = k - ((D + 1 : ℕ) : ℤ) by push_cast; ring]

def hilbPoly (D : ℕ) : Polynomial ℚ :=
  (Polynomial.preHilbertPoly ℚ D 0).comp (Polynomial.C 2 * Polynomial.X)

theorem hilbPoly_eval (D n : ℕ) : (hilbPoly D).eval (n : ℚ) = ((2 * n + D).choose D : ℚ) := by
  rw [hilbPoly, Polynomial.eval_comp]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  have := Polynomial.preHilbertPoly_eq_choose_sub_add ℚ D (k := 0) (n := 2 * n) (Nat.zero_le _)
  push_cast at this
  rw [this, Nat.sub_zero]

theorem fwdDiff_hilbPoly (D : ℕ) (y : ℚ) : (fwdDiff (1 : ℚ))^[D] (hilbPoly D).eval y = 2 ^ D := by
  have hdeg : (hilbPoly D).natDegree = D := by
    rw [hilbPoly, Polynomial.natDegree_comp, Polynomial.natDegree_preHilbertPoly,
      Polynomial.natDegree_C_mul_X _ two_ne_zero, mul_one]
  have hlc : (hilbPoly D).leadingCoeff = (D.factorial : ℚ)⁻¹ * 2 ^ D := by
    rw [hilbPoly, Polynomial.leadingCoeff_comp (by rw [Polynomial.natDegree_C_mul_X _ two_ne_zero]; exact one_ne_zero),
      Polynomial.leadingCoeff_preHilbertPoly, Polynomial.leadingCoeff_C_mul_X,
      Polynomial.natDegree_preHilbertPoly]
  have h := congrFun (Polynomial.fwdDiff_iter_degree_eq_factorial (hilbPoly D)) y
  rw [hdeg, hlc] at h
  rw [h]
  have hf : (D.factorial : ℚ) ≠ 0 := by positivity
  simp only [Pi.smul_apply, Pi.natCast_apply, smul_eq_mul]
  field_simp

theorem eventualValue_eq {K : Type*} (F : (K → ℤ) → ℤ) (c : ℤ)
    (h : ∀ᶠ m in atTop, F m = c) : GroundTheory.Heights₂.Heights.NumbersDVR.eventualValue F = c := by
  unfold GroundTheory.Heights₂.Heights.NumbersDVR.eventualValue
  have hex : ∃ c, ∀ᶠ m in atTop, F m = c := ⟨c, h⟩
  rw [dite_eq_left hex]
  obtain ⟨m, h1, h2⟩ := (hex.choose_spec.and h).exists
  rw [← h1, h2]

end VeroneseGenDeg


open VeroneseGenDeg in
theorem VeroneseGenDeg.proof : VeroneseGenDeg.Statement := by
  intro D _
  set q := (coordIdeal ℤ (Veronese.x D)).map (MvPolynomial.map (Int.castRingHom ℚ)) with hq
  set g : ℤ → ℤ := fun j => GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory (Veronese.Idx D)) q (fun _ => j)
    with hgdef

  have hg : ∀ j : ℤ, 0 ≤ j → (g j : ℚ) = (hilbPoly D).eval (j : ℚ) := by
    intro j hj
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hj
    have h := SectionsRank.proof (Veronese.Fld D) (Veronese.Idx D) (Veronese.x D) n
    rw [finrank_sec] at h
    simp only [hgdef]
    rw [← hq] at h
    rw [h, Int.cast_natCast, Int.cast_natCast, hilbPoly_eval]
  have hev : ∀ᶠ m in atTop, GroundTheory.Heights₂.Heights.NumbersDVR.mixedDiff (fun _ : Fin D => (1 : Unit → ℤ))
      (GroundTheory.Heights₂.Heights.NumbersDVR.hilbFn (ι := GlobalTheory (Veronese.Idx D)) q) m = 2 ^ D := by
    filter_upwards [eventually_ge_atTop (fun _ : Unit => (D : ℤ))] with m hm
    have hm' : m = fun _ => m () := funext fun u => rfl
    have hD : (D : ℤ) ≤ m () := hm ()
    rw [mixedDiff_const, hm', iterate_diffStep]
    have key : (((fwdDiff (1 : ℤ))^[D] g (m () - D) : ℤ) : ℚ) = 2 ^ D := by
      rw [← fwdDiff_hilbPoly D ((m () - D : ℤ) : ℚ), fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
      push_cast
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [nsmul_eq_mul, mul_one, smul_eq_mul, zsmul_eq_mul]
      push_cast
      rw [hg _ (by omega)]
      push_cast
      ring
    exact_mod_cast key
  unfold genDeg GroundTheory.Heights₂.Heights.NumbersDVR.intNum
  apply eventualValue_eq
  convert hev

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftIntersectionPolynomial
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.Inter (famExt famExt_apply)

noncomputable section

namespace ShiftIntersectionPolynomial

theorem prod_weights {n : ℕ} (q : ℝ) (s : Fin n → Fin 2) :
    ∏ j, (![q, 1] : Fin 2 → ℝ) (s j) = q ^ (Finset.univ.filter fun j => s j = 0).card := by
  have h : ∀ j, (![q, 1] : Fin 2 → ℝ) (s j) = if s j = 0 then q else 1 := by
    intro j
    rcases Fin.exists_fin_two.mp ⟨s j, rfl⟩ with h | h <;> rw [h] <;> simp
  simp only [h, Finset.prod_ite, Finset.prod_const, one_pow, mul_one]

theorem proof : ShiftIntersectionPolynomial.Statement := by
  intro K _ ι _ II P n A B hII hP hA hB
  have hI : IsIntersectionFamily (II K ι) := hII K ι
  set e : Fin 2 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := ![A, B] with he_def
  have he : ∀ i, IsSmoothHerm (e i) := by
    intro i
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with h | h <;> rw [h] <;> simpa [e]
  refine ⟨∑ s : Fin n → Fin 2, Polynomial.C (II K ι P n (e ∘ s)) *
      Polynomial.X ^ (Finset.univ.filter fun j => s j = 0).card, ?_, ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s _ => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    exact (Finset.card_filter_le _ _).trans (by simp)
  · rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single (fun _ => 0)]
    · rw [Polynomial.coeff_C_mul_X_pow]
      have hc : (Finset.univ.filter fun j : Fin n => (fun _ : Fin n => (0 : Fin 2)) j = 0).card = n := by simp
      rw [if_pos hc.symm]
      rfl
    · intro s _ hs
      rw [Polynomial.coeff_C_mul_X_pow, if_neg]
      intro hc
      apply hs
      have hu : (Finset.univ.filter fun j => s j = 0) = Finset.univ :=
        Finset.eq_univ_of_card _ (by rw [← hc, Fintype.card_fin])
      funext j
      have := Finset.filter_eq_self.mp hu j (Finset.mem_univ j)
      exact this
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro q
    set Z := HermLine.zcomb A B (q : ℤ) 1 with hZ_def
    have hZ : IsSmoothHerm Z := ZCombLimit.isSmoothHerm_zcomb_int hA hB _ _
    have hposition : ∀ (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (a : Fin n), (∀ j, IsSmoothHerm (L j)) →
        II K ι P n (Function.update L a Z) =
          (![(q : ℝ), 1] : Fin 2 → ℝ) 0 * II K ι P n (Function.update L a (e 0)) +
            (![(q : ℝ), 1] : Fin 2 → ℝ) 1 * II K ι P n (Function.update L a (e 1)) := by
      intro L a hL
      cases n with
      | zero => exact a.elim0
      | succ m =>
        have h := ZCombLimit.fam_update_zcomb_int hI hP L hL a hA hB (q : ℤ) 1
        simp only [Int.cast_natCast, Int.cast_one, one_mul] at h
        simpa [e] using h
    have key := ZCombLimit.eq_famExt_of_position (J := II K ι) (P := P) IsSmoothHerm e Z ![(q : ℝ), 1] he hZ hposition
      Finset.univ (fun _ => 0)
    simp only [Finset.mem_univ, if_true] at key
    rw [key, famExt_apply, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [prod_weights, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

end ShiftIntersectionPolynomial

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
