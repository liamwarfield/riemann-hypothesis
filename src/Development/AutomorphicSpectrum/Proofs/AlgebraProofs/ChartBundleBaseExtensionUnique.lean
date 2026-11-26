module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TrivFlagMod
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.SameGenericSymm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.Avoid
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import GroundTheory.FunctionField.DivisorDegree
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentGeneratorDualIntegral
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeGoodBaseChange
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeTestPointMembership

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtensionUnique
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsExtraRest
theorem UpperTheory.Reformulated.B.Ydb6.main :
    ∀ {O Ω V : Type} [inst : CommRing O] [inst_1 : Field Ω] [inst_2 : Algebra O Ω] [inst_3 : AddCommGroup V]
      [inst_4 : _root_.Module Ω V] (R : Subalgebra O Ω) (A B : AddSubgroup V) (c : Ω),
      (∀ (v : V), v ∈ B ↔ ∃ e ∈ A, v = c • e) →
        ∀ (v : V),
          v ∈ AddSubgroup.closure {v : V | ∃ a ∈ R, ∃ e ∈ B, v = a • e} ↔
            ∃ e ∈ AddSubgroup.closure {v : V | ∃ a ∈ R, ∃ e ∈ A, v = a • e}, v = c • e := by
  intro O Ω V _ _ _ _ _ R A B c hB v
  let f : V →+ V := DistribSMul.toAddMonoidHom V c
  have hS : {v : V | ∃ a ∈ R, ∃ e ∈ B, v = a • e} =
      f '' {v : V | ∃ a ∈ R, ∃ e ∈ A, v = a • e} := by
    ext w
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · rintro ⟨a, ha, e, he, rfl⟩
      obtain ⟨e', he', rfl⟩ := (hB e).1 he
      refine ⟨a • e', ⟨a, ha, e', he', rfl⟩, ?_⟩
      show c • a • e' = a • c • e'
      rw [smul_smul, smul_smul, mul_comm]
    · rintro ⟨x, ⟨a, ha, e, he, rfl⟩, rfl⟩
      refine ⟨a, ha, c • e, (hB _).2 ⟨e, he, rfl⟩, ?_⟩
      show c • a • e = a • c • e
      rw [smul_smul, smul_smul, mul_comm]
  rw [hS, ← AddMonoidHom.map_closure, AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtensionUnique
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.PullPreserve

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (restrictChart)

section Closure

variable {O Ω V : Type} [CommRing O] [Field Ω] [Algebra O Ω] [AddCommGroup V] [Module Ω V]

theorem const_smul_mem (R : Subalgebra O Ω) (A : AddSubgroup V) (c : O) {v : V}
    (hv : v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ A, v = a • e}) :
    algebraMap O Ω c • v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ A, v = a • e} := by
  induction hv using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, e, he, rfl⟩ := hw
    exact AddSubgroup.subset_closure
      ⟨algebraMap O Ω c * a, mul_mem (R.algebraMap_mem c) ha, e, he, by rw [mul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add w₁ w₂ _ _ h₁ h₂ => rw [smul_add]; exact add_mem h₁ h₂
  | neg w _ h => rw [smul_neg]; exact neg_mem h

theorem exists_const_smul_mem [IsDomain O] (R : Subalgebra O Ω) (A B : AddSubgroup V)
    (h : ∀ v ∈ A, ∃ c : O, c ≠ 0 ∧ algebraMap O Ω c • v ∈ B) {v : V}
    (hv : v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ A, v = a • e}) :
    ∃ c : O, c ≠ 0 ∧
      algebraMap O Ω c • v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ B, v = a • e} := by
  induction hv using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨a, ha, e, he, rfl⟩ := hw
    obtain ⟨c, hc, hce⟩ := h e he
    exact ⟨c, hc, AddSubgroup.subset_closure ⟨a, ha, _, hce, smul_comm _ _ _⟩⟩
  | zero => exact ⟨1, one_ne_zero, by rw [smul_zero]; exact zero_mem _⟩
  | add w₁ w₂ _ _ h₁ h₂ =>
    obtain ⟨c₁, hc₁, m₁⟩ := h₁
    obtain ⟨c₂, hc₂, m₂⟩ := h₂
    refine ⟨c₁ * c₂, mul_ne_zero hc₁ hc₂, ?_⟩
    have e : algebraMap O Ω (c₁ * c₂) • (w₁ + w₂) =
        algebraMap O Ω c₂ • (algebraMap O Ω c₁ • w₁) +
          algebraMap O Ω c₁ • (algebraMap O Ω c₂ • w₂) := by
      rw [map_mul, smul_add, smul_smul, smul_smul, mul_comm]
    rw [e]
    exact add_mem (const_smul_mem R B c₂ m₁) (const_smul_mem R B c₁ m₂)
  | neg w _ h =>
    obtain ⟨c, hc, m⟩ := h
    exact ⟨c, hc, by rw [smul_neg]; exact neg_mem m⟩

theorem mem_span_scaled (R : Subalgebra O Ω) (A B : AddSubgroup V) (c : Ω)
    (h : ∀ v, v ∈ B ↔ ∃ e ∈ A, v = c • e) (v : V) :
    v ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ B, v = a • e} ↔
      ∃ e ∈ AddSubgroup.closure {v | ∃ a ∈ R, ∃ e ∈ A, v = a • e}, v = c • e :=
  _root_.UpperTheory.Reformulated.B.Ydb6.main R A B c h v

end Closure

theorem pull_preserve : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V) (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB E'B : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsPull O x z E' E'B → (LatLE O x E E' → LatLE O (joinCoord x z) EB E'B) ∧ (SameGeneric O x E E' → SameGeneric O (joinCoord x z) EB E'B) ∧ (∀ c : Ω, IsScaled x c E.lat E'.lat → IsScaled (joinCoord x z) c EB.lat E'B.lat) := by
  intro O _ _ _ Ω _ _ K _ _ ι _ x N V _ _ E E' K' _ _ ι' _ z EB E'B hE hE'
  have hx : ∀ s, mseg (joinCoord x z) s ≠ 0 → mseg x (restrictChart s) ≠ 0 := by
    intro s hs h
    apply hs
    have e : mseg (joinCoord x z) s =
        mseg x (restrictChart s) * mseg z (fun k => s (.inr k)) := by
      simp only [mseg, Fintype.prod_sum_type]
      rfl
    rw [e, h, zero_mul]
  refine ⟨fun h s hs => ?_, fun h s hs => ⟨fun v hv => ?_, fun v hv => ?_⟩,
    fun c h s hs v => ?_⟩
  · rw [hE s hs, hE' s hs]
    refine AddSubgroup.closure_mono ?_
    rintro _ ⟨a, ha, e, he, rfl⟩
    exact ⟨a, ha, e, h _ (hx s hs) he, rfl⟩
  · rw [hE s hs] at hv
    rw [hE' s hs]
    exact exists_const_smul_mem _ _ _ (h _ (hx s hs)).1 hv
  · rw [hE' s hs] at hv
    rw [hE s hs]
    exact exists_const_smul_mem _ _ _ (h _ (hx s hs)).2 hv
  · rw [hE s hs, hE' s hs]
    exact mem_span_scaled _ _ _ c (h _ (hx s hs)) v

end GlobalTheory.CompanionTheory.Ar.Num.PullPreserve
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ChartBundleBaseExtensionUniqueStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_bundle_base_extension_unique : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (E E' : ChartBundle O (mseg x) N V) (K' : Type) [Fintype K'] [DecidableEq K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (z : (Σ k, ι' k) → Ω) (EB E'B : ChartBundle O (mseg (joinCoord x z)) N V), IsPull O x z E EB → IsPull O x z E' E'B → (LatLE O x E E' → LatLE O (joinCoord x z) EB E'B) ∧ (SameGeneric O x E E' → SameGeneric O (joinCoord x z) EB E'B) ∧ (∀ c : Ω, IsScaled x c E.lat E'.lat → IsScaled (joinCoord x z) c EB.lat E'B.lat) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.PullPreserve.pull_preserve | exact GlobalTheory.CompanionTheory.Ar.Num.PullPreserve.pull_preserve | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.PullPreserve.pull_preserve <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TopAvoid
namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem topAvoid : ReciprocityTheory.ChartRestriction.G.AI.I2.AvoidStatement :=
  GroundTheory.Heights₂.Heights.ForSecondHalf.avoid

end GlobalTheory.CompanionTheory.Ar.Giv
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwistedModuleFiniteProjectiveRank
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwistedModuleFiniteProjectiveRank
namespace GlobalTheory.CompanionTheory.Ar.TwModule

open GlobalTheory.CompanionTheory.Ar

variable {O : Type} [CommRing O] (s : O ≃+* O) (L : Type) [AddCommGroup L] [Module O L]

def twOut {n : ℕ} (f : (Fin n → O) →ₗ[O] L) : (Fin n → O) →ₗ[O] TwMod s L where
  toFun v := (show TwMod s L from f (fun i => s (v i)))
  map_add' v w := by
    have : (fun i => s ((v + w) i)) = (fun i => s (v i)) + (fun i => s (w i)) := by
      funext i; simp
    show f (fun i => s ((v + w) i)) = f (fun i => s (v i)) + f (fun i => s (w i))
    rw [this, map_add (f := _)]
  map_smul' c v := by
    have : (fun i => s ((c • v) i)) = s c • (fun i => s (v i)) := by
      funext i; simp
    show f (fun i => s ((c • v) i)) = s c • f (fun i => s (v i))
    rw [this, map_smul]

def twIn {n : ℕ} (r : L →ₗ[O] (Fin n → O)) : TwMod s L →ₗ[O] (Fin n → O) where
  toFun x := fun i => s.symm (r (show L from x) i)
  map_add' x y := by
    funext i
    have h : r (show L from x + y) i = r (show L from x) i + r (show L from y) i :=
      congrFun (map_add r (show L from x) (show L from y)) i
    exact (congrArg s.symm h).trans (map_add s.symm _ _)
  map_smul' c x := by
    funext i
    have h : r (show L from c • x) i = s c * r (show L from x) i :=
      congrFun (map_smul r (s c) (show L from x)) i
    refine (congrArg s.symm h).trans ?_
    show s.symm (s c * r (show L from x) i) = c * s.symm (r (show L from x) i)
    rw [map_mul, s.symm_apply_apply]

theorem twOut_twIn {n : ℕ} (f : (Fin n → O) →ₗ[O] L) (r : L →ₗ[O] (Fin n → O)) (h : f ∘ₗ r = LinearMap.id)
    (x : TwMod s L) : twOut s L f (twIn s L r x) = x := by
  have hx : f (r (show L from x)) = (show L from x) := LinearMap.congr_fun h _
  show f (fun i => s (s.symm (r (show L from x) i))) = (show L from x)
  simpa using hx

theorem twOut_surjective {n : ℕ} (f : (Fin n → O) →ₗ[O] L) (hf : Function.Surjective f) :
    Function.Surjective (twOut s L f) := by
  intro x
  obtain ⟨v, hv⟩ := hf (show L from x)
  refine ⟨fun i => s.symm (v i), ?_⟩
  show f (fun i => s (s.symm (v i))) = (show L from x)
  simpa using hv

theorem finite_twMod [Module.Finite O L] : Module.Finite O (TwMod s L) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O L
  exact Module.Finite.of_surjective _ (twOut_surjective s L f hf)

theorem projective_twMod [Module.Finite O L] [Module.Projective O L] : Module.Projective O (TwMod s L) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' O L
  obtain ⟨r, hr⟩ := Module.projective_lifting_property f LinearMap.id hf
  exact Module.Projective.of_split (twIn s L r) (twOut s L f)
    (LinearMap.ext (twOut_twIn s L f r hr))

theorem rank_twMod : Module.rank O (TwMod s L) = Module.rank O L :=
  (rank_eq_of_equiv_equiv (s : O → O) (AddEquiv.refl (TwMod s L) : TwMod s L ≃+ L) s.bijective
    (fun _ _ => rfl))

theorem finrank_twMod : Module.finrank O (TwMod s L) = Module.finrank O L := by
  rw [Module.finrank, Module.finrank, rank_twMod]

end GlobalTheory.CompanionTheory.Ar.TwModule

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem GlobalTheory.CompanionTheory.Ar.TwModule.twMod_finite_projective_finrank :
    ∀ (O : Type) [CommRing O] [IsDomain O] (s : O ≃+* O) (L : Type) [AddCommGroup L] [Module O L]
      [Module.Finite O L] [Module.Projective O L],
      Module.Finite O (TwMod s L) ∧ Module.Projective O (TwMod s L) ∧
        Module.finrank O (TwMod s L) = Module.finrank O L := by
  intro O _ _ s L _ _ _ _
  exact ⟨finite_twMod s L, projective_twMod s L, finrank_twMod s L⟩
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwistedModuleFiniteProjectiveRankStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_module_finite_projective_rank : ∀ (O : Type) [CommRing O] [IsDomain O] (s : O ≃+* O) (L : Type) [AddCommGroup L] [Module O L] [Module.Finite O L] [Module.Projective O L], Module.Finite O (TwMod s L) ∧ Module.Projective O (TwMod s L) ∧ Module.finrank O (TwMod s L) = Module.finrank O L := by
  first | exact @GlobalTheory.CompanionTheory.Ar.TwModule.twMod_finite_projective_finrank | exact GlobalTheory.CompanionTheory.Ar.TwModule.twMod_finite_projective_finrank | (intros; apply GlobalTheory.CompanionTheory.Ar.TwModule.twMod_finite_projective_finrank <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsCurveOfFunctionField
noncomputable section

open GroundTheory.FunctionField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isFunctionField_of_fg_trdeg {k κ : Type} [Field k] [Field κ] [Algebra k κ]
    (hfg : (⊤ : IntermediateField k κ).FG) (htr : Algebra.trdeg k κ = 1) :
    IsFunctionField k κ := by
  classical
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k κ
  have hcard : Cardinal.mk s = 1 := by rw [hs.cardinalMk_eq_trdeg, htr]
  obtain ⟨⟨x, hx⟩⟩ : Nonempty s := by
    rw [← Cardinal.mk_ne_zero_iff, hcard]
    exact one_ne_zero
  have hsx : s = {x} := by
    have hsub : Subsingleton s := by
      rw [← Cardinal.le_one_iff_subsingleton, hcard]
    ext y
    constructor
    · intro hy
      have := Subsingleton.elim (⟨y, hy⟩ : s) ⟨x, hx⟩
      simpa using congrArg Subtype.val this
    · rintro rfl
      exact hx
  have htrx : Transcendental k x := hs.1.transcendental ⟨x, hx⟩
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin k {x}) κ := by
    have := hs.isAlgebraic_field
    rwa [Subtype.range_coe, hsx] at this
  obtain ⟨t, ht⟩ := hfg
  have hfd : ∀ F : IntermediateField k κ, Algebra.IsAlgebraic F κ → FiniteDimensional F κ := by
    intro F hF
    have hle : IntermediateField.adjoin k (↑t : Set κ) ≤
        (IntermediateField.adjoin F (↑t : Set κ)).restrictScalars k :=
      IntermediateField.adjoin_le_iff.2 (IntermediateField.subset_adjoin F _)
    have htop : IntermediateField.adjoin F (↑t : Set κ) = ⊤ := by
      rw [eq_top_iff]
      intro y _
      have hy : y ∈ IntermediateField.adjoin k (↑t : Set κ) := by
        rw [ht]
        exact IntermediateField.mem_top
      exact hle hy
    have h1 : FiniteDimensional F (IntermediateField.adjoin F (↑t : Set κ)) :=
      IntermediateField.finiteDimensional_adjoin fun y _ => (hF.isAlgebraic y).isIntegral
    rw [htop] at h1
    exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional
  exact ⟨⟨x, htrx, hfd _ halg⟩⟩

section

variable (k κ : Type) [Field k] [Field κ] [Algebra k κ] [IsFunctionField k κ]

def placesCurve : GlobalTheory.CompanionTheory.Ar.Crv.ACurve κ where
  I := Place k κ
  v := fun i => i.valuation
  w := fun i => i.deg
  fin := fun x hx => by
    refine (Place.finite_ord_ne_zero (k := k) x).subset fun i hi h0 => hi ?_
    have h := i.valuation_eq_exp_neg_ord hx
    rw [h, h0]
    simp
  prod := fun x hx => by
    classical
    have h := Divisor.deg_divisor (k := k) x
    rw [Divisor.deg_eq_sum] at h
    rw [finsum_eq_sum_of_support_subset (s := (divisor x : Divisor k κ).support)]
    · have : ∑ i ∈ (divisor x : Divisor k κ).support,
          ((i.deg : ℤ) * WithZero.log (i.valuation x)) =
          - ∑ i ∈ (divisor x : Divisor k κ).support, (divisor x : Divisor k κ) i * (i.deg : ℤ) := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [divisor_apply, Place.ord]
        ring
      rw [this, h, neg_zero]
    · intro i hi
      simp only [Function.mem_support] at hi
      simp only [Finset.mem_coe, Finsupp.mem_support_iff, divisor_apply, Place.ord]
      intro h0
      apply hi
      have : WithZero.log (i.valuation x) = 0 := by omega
      rw [this, mul_zero]

end

theorem exists_curve_of_function_field :
    ∀ (k κ : Type) [Field k] [Field κ] [Algebra k κ], (⊤ : IntermediateField k κ).FG →
      Algebra.trdeg k κ = 1 → ∃ C : GlobalTheory.CompanionTheory.Ar.Crv.ACurve κ, (∀ i, 0 < C.w i) ∧
        (∀ i (a : k), a ≠ 0 → C.v i (algebraMap k κ a) = 1) ∧
        (∀ i, Function.Surjective (C.v i)) ∧
        ∀ W : ValuationSubring κ, W ≠ ⊤ → (∀ a : k, algebraMap k κ a ∈ W) →
          ∃! i, (C.v i).valuationSubring = W := by
  intro k κ _ _ _ hfg htr
  haveI : IsFunctionField k κ := isFunctionField_of_fg_trdeg hfg htr
  have key : ∀ i : Place k κ, (i.valuation).valuationSubring = i.ring := fun i => by
    ext y
    rw [Valuation.mem_valuationSubring_iff]
    exact Place.valuation_le_one_iff i y
  refine ⟨placesCurve k κ, fun i => ?_, fun i a ha => ?_, fun i => ?_, fun W hW hk => ?_⟩
  · exact Place.deg_pos i
  · exact Place.valuation_algebraMap' i ha
  · exact Place.valuation_surjective i
  · refine ⟨⟨W, hW, hk⟩, key _, fun j hj => ?_⟩
    exact Place.ext ((key j).symm.trans hj)

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeImageBaseChange
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeImageBaseChange
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeImageBaseChange

open GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness

theorem map_snd_spanOver {o C V Z Vc Zc : Type} [CommRing o] [Field C] [Algebra o C]
    (RC : Subalgebra o C) [AddCommGroup V] [AddCommGroup Z] [AddCommGroup Vc] [AddCommGroup Zc]
    [Module C Vc] [Module C Zc] (b : V → Vc) (b' : Z → Zc) (G : AddSubgroup (V × Z)) :
    (spanOver RC (Prod.map b b' '' G)).map (AddMonoidHom.snd Vc Zc) =
      spanOver RC (b' '' G.map (AddMonoidHom.snd V Z)) := by
  unfold spanOver
  rw [AddMonoidHom.map_closure]
  congr 1
  ext v
  constructor
  · rintro ⟨_, ⟨a, ha, _, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
    exact ⟨a, ha, b' y.2, ⟨y.2, AddSubgroup.mem_map.mpr ⟨y, hy, rfl⟩, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨z, hz, rfl⟩, rfl⟩
    obtain ⟨y, hy, rfl⟩ := AddSubgroup.mem_map.mp hz
    exact ⟨a • Prod.map b b' y, ⟨a, ha, Prod.map b b' y, ⟨y, hy, rfl⟩, rfl⟩, rfl⟩

theorem hh_le_divLat {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] {n : ℕ}
    {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω)
    (χ : F → Ω) (hw : mulLat w (stdLat R _) ≤ D.af R p χ) :
    D.hh R p χ ≤ divLat w (stdLat R (Fin n)) := by
  intro v hv
  change v ∈ dotDual R (D.af R p χ) at hv
  unfold dotDual at hv
  simp only [divLat, AddSubgroup.mem_comap, DistribSMul.toAddMonoidHom_apply]
  rw [stdLat, AddSubgroup.mem_pi]
  intro i _
  have he : (Pi.single i (1 : Ω) : Fin n → Ω) ∈ stdLat R (Fin n) := by
    rw [stdLat, AddSubgroup.mem_pi]
    intro j _
    rw [Pi.single_apply]
    split_ifs
    · exact R.one_mem
    · exact R.zero_mem
  have hwe : w • (Pi.single i (1 : Ω) : Fin n → Ω) ∈ D.af R p χ :=
    hw (AddSubgroup.mem_map_of_mem (DistribSMul.toAddMonoidHom (Fin n → Ω) w) he)
  have h := AddSubgroup.mem_iInf.mp
    (AddSubgroup.mem_iInf.mp hv (w • (Pi.single i (1 : Ω) : Fin n → Ω))) hwe
  have h2 : (w • (Pi.single i (1 : Ω) : Fin n → Ω)) ⬝ᵥ v ∈ R := h
  have h3 : (w • v) i = (w • (Pi.single i (1 : Ω) : Fin n → Ω)) ⬝ᵥ v := by
    simp [dotProduct, Pi.single_apply]
  show (w • v) i ∈ R
  rw [h3]
  exact h2

theorem imH_bc : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ, (D.bc RC).imH RC p τ (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.imH R p τ (χ τ)) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hB hG hw C _ _ _ _ RC hR τ
  have hw0 : w ≠ 0 := by
    rintro rfl
    obtain ⟨hp, -, ⟨c, -, hpc⟩, -⟩ := hc
    exact hp (by rw [hpc, mul_zero])
  have hfst : (D.Del τ).map (AddMonoidHom.fst _ _) = divLat w (stdLat R (Fin n)) := by
    ext b
    rw [AddSubgroup.mem_map]
    constructor
    · rintro ⟨⟨b', c⟩, h, rfl⟩
      exact ((hB.del τ).1 b').mp ⟨c, h⟩
    · intro h
      obtain ⟨c, hcc⟩ := ((hB.del τ).1 b).mpr h
      exact ⟨(b, c), hcc, rfl⟩
  have hstab : ∀ a ∈ R, ∀ v ∈ D.hh R p (χ τ), a • v ∈ D.hh R p (χ τ) := by
    intro a ha v hv
    change v ∈ dotDual R (D.af R p (χ τ)) at hv
    change a • v ∈ dotDual R (D.af R p (χ τ))
    unfold dotDual at hv ⊢
    rw [AddSubgroup.mem_iInf]
    intro l
    rw [AddSubgroup.mem_iInf]
    intro hl
    have h1 : l ⬝ᵥ v ∈ R := AddSubgroup.mem_iInf.mp (AddSubgroup.mem_iInf.mp hv l) hl
    have h2 : l ⬝ᵥ (a • v) = a * (l ⬝ᵥ v) := by
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    show l ⬝ᵥ (a • v) ∈ R
    rw [h2]
    exact R.mul_mem ha h1
  have hhh : (D.bc RC).hh RC p (fun a => algebraMap Ω C (χ τ a)) =
      spanOver RC (bcMap Ω C (Fin n) '' D.hh R p (χ τ)) :=
    (((GlobalTheory.T.lattice_good_base_change D R p w χ hc hB hG).2 C RC hR).2 τ).2.1
  have key := (GlobalTheory.T.locally_free_base_change_quotient R RC hR (bcMap Ω C (Fin n)) (bcMap Ω C (Fin (s τ)))
    (isBaseChange_bcMap Ω C _) (isBaseChange_bcMap Ω C _) (D.Del τ) (D.hh R p (χ τ)) n
    (fun a ha v hv => (hB.stable τ a ha).2.1 v hv)
    (by rw [hfst]; exact locFree_divLat R hw0 (locFree_stdLat R n))
    (by rw [hfst]; exact hh_le_divLat D R p w (χ τ) (hw τ)) hstab).1
  have hDel : (D.bc RC).Del τ =
      spanOver RC (Prod.map (bcMap Ω C (Fin n)) (bcMap Ω C (Fin (s τ))) '' D.Del τ) := rfl
  unfold LieLatticeData.imH
  rw [hhh, hDel, key]
  exact map_snd_spanOver RC _ _ _

end GlobalTheory.CompanionTheory.Ar.Num.LatticeImageBaseChange
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeImageBaseChangeStatement
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_image_base_change : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → (∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ)) → ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ, (D.bc RC).imH RC p τ (fun a => algebraMap Ω C (χ τ a)) = spanOver RC (bcMap Ω C _ '' D.imH R p τ (χ τ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LatticeImageBaseChange.imH_bc | exact GlobalTheory.CompanionTheory.Ar.Num.LatticeImageBaseChange.imH_bc | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LatticeImageBaseChange.imH_bc <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeAnnihilatorLatticeHolds
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeAnnihilatorLatticeHolds
namespace GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_stdLat_iff_algebra (R : Subalgebra o Ω) {ι : Type} (v : ι → Ω) :
    v ∈ stdLat R ι ↔ ∀ i, v i ∈ R := by
  simp [stdLat, AddSubgroup.mem_pi]

theorem linMap_mem_stdLat {F : Type} [Zero F] [Fintype F] {n : ℕ} (R : Subalgebra o Ω) (χ : F → Ω)
    (hχ : ∀ a, χ a ∈ R) (v : Fin n → Ω) (hv : v ∈ stdLat R (Fin n)) :
    linMap n χ v ∈ stdLat R (Fin n → F) := by
  rw [mem_stdLat_iff_algebra] at hv ⊢
  intro x
  simp only [linMap, Fintype.linearCombination_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hv i) (hχ _)

theorem hodge_annihilator_lattice {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F]
    [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω)
    (p : ℕ) (w : Ω) (χ : Sg → F → Ω) (hC : CharData R p w χ) (hB : D.Base R p w) (hp : p.Prime)
    (hN : IsNoetherianRing R) (hF : IsFractionRing R Ω) (hI : IsIntegrallyClosedIn R Ω)
    (φ : Equiv.Perm Sg) (hT : D.TestFacts R p w χ φ) (hG : D.Good₁ R p χ) (τ : Sg) :
    mulLat w (stdLat R _) ≤ D.af R p (χ τ) := by
  have H := GlobalTheory.T.lattice_good_base_change D R p w χ hC hB hG
  obtain ⟨hp0, hwR, -, -, hχ⟩ := hC
  intro x hx
  obtain ⟨u, hu, rfl⟩ := AddSubgroup.mem_map.mp hx
  have hu' : ∀ i, u i ∈ R := (mem_stdLat_iff_algebra R u).mp hu
  refine GlobalTheory.T.locally_free_test_point_membership R p hp hp0 hN hF hI n (D.af R p (χ τ)) (H.1 τ).1 _ ⟨1, ?_⟩ ?_
  · have hy : linMap n (χ τ) (w • u) ∈ stdLat R (Fin n → F) :=
      linMap_mem_stdLat R (χ τ) (hχ τ).2.2 _ ((mem_stdLat_iff_algebra R _).mpr fun i => by
        simpa using R.mul_mem hwR (hu' i))
    rw [LieLatticeData.af, AddSubgroup.mem_comap]
    refine AddSubgroup.mem_sup_right (AddSubgroup.mem_map.mpr ⟨_, hy, ?_⟩)
    simp [map_smul]
  · intro C _ _ _ _ RC hTP
    have hRC : ∀ a ∈ R, algebraMap Ω C a ∈ RC := hTP.2.2.2
    rw [← ((H.2 C RC hRC).2 τ).1]
    have hFa := hT C RC hTP
    refine hFa.le_af τ (AddSubgroup.mem_map.mpr ⟨bcMap Ω C (Fin n) u, ?_, ?_⟩)
    · exact (mem_stdLat_iff_algebra RC _).mpr fun i => by simpa [bcMap] using hRC _ (hu' i)
    · ext i
      simp [bcMap]

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeAnnihilatorLatticeHoldsStatement
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_annihilator_lattice_holds : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → ∀ τ, mulLat w (stdLat R _) ≤ D.af R p (χ τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.hodge_annihilator_lattice | exact GlobalTheory.CompanionTheory.Ar.Num.hodge_annihilator_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.hodge_annihilator_lattice <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeFlagFrame
section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeFlagFrame
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)

namespace GlobalTheory.CompanionTheory.Ar.Num.FlagDual

section Linear

variable {O Ω : Type*} [CommRing O] [Field Ω] [Algebra O Ω]
variable {V V₁ : Type*} [AddCommGroup V] [Module Ω V] [AddCommGroup V₁] [Module Ω V₁] {N : ℕ}

theorem form_eq_sum {W : Type*} [AddCommGroup W] [Module Ω W] (w : Module.Basis (Fin N) Ω W)
    (φ : W →ₗ[Ω] Ω) (v : W) : φ v = ∑ j, w.repr v j * φ (w j) := by
  conv_lhs => rw [← w.sum_repr v]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, smul_eq_mul]

theorem exists_coeffs (R : Subalgebra O Ω) (L : AddSubgroup V)
    (hst : ∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) (w : Module.Basis (Fin N) Ω V) (m : Fin N → Ω)
    (hg : ∀ i s, (∃ v ∈ L, (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = s) ↔ ∃ a ∈ R, s = a * m i)
    (e : Fin N → V) (heL : ∀ i, e i ∈ L) (hez : ∀ i j, i < j → w.repr (e i) j = 0)
    (hed : ∀ i, w.repr (e i) i = m i) (k : ℕ) :
    ∀ v ∈ L, (∀ j : Fin N, k ≤ j.val → w.repr v j = 0) →
      ∃ c : Fin N → Ω, (∀ i, c i ∈ R) ∧ v = ∑ i, c i • e i := by
  induction k with
  | zero =>
    intro v _ hv
    refine ⟨0, fun _ => zero_mem _, ?_⟩
    have : v = 0 := by
      apply w.repr.injective
      ext j
      simpa using hv j (Nat.zero_le _)
    simp [this]
  | succ k ih =>
    intro v hvL hv
    by_cases hk : k < N
    · set i : Fin N := ⟨k, hk⟩ with hi
      obtain ⟨a, haR, ha⟩ := (hg i (w.repr v i)).1
        ⟨v, hvL, fun j hj => hv j (by
          have : i.val < j.val := hj
          simpa [hi] using this), rfl⟩
      have hv' : v - a • e i ∈ L := sub_mem hvL (hst a haR _ (heL i))
      obtain ⟨c, hcR, hc⟩ := ih _ hv' (fun j hj => by
        rcases Nat.lt_or_eq_of_le hj with hlt | heq
        · have hij : i < j := by
            show i.val < j.val
            simpa [hi] using hlt
          have h1 : w.repr v j = 0 := hv j hlt
          simp [h1, hez i j hij]
        · have hij : j = i := Fin.ext (by simp [hi, heq])
          subst hij
          simp [hed, ha])
      refine ⟨fun l => c l + (if l = i then a else 0), fun l => ?_, ?_⟩
      · refine add_mem (hcR l) ?_
        split_ifs
        · exact haR
        · exact zero_mem _
      · have : v = (v - a • e i) + a • e i := by abel
        rw [this, hc]
        simp [add_smul, Finset.sum_add_distrib, ite_smul]
    · exact ih v hvL (fun j _ => hv j (by have := j.isLt; omega))

theorem exists_basis (w : Module.Basis (Fin N) Ω V) (m : Fin N → Ω) (hm : ∀ i, m i ≠ 0)
    (e : Fin N → V) (hez : ∀ i j, i < j → w.repr (e i) j = 0) (hed : ∀ i, w.repr (e i) i = m i) :
    ∃ e' : Module.Basis (Fin N) Ω V, ∀ i, e' i = e i := by
  have hdet : IsUnit (w.det e) := by
    rw [Module.Basis.det_apply, isUnit_iff_ne_zero,
      Matrix.det_of_upperTriangular (M := w.toMatrix e)]
    · refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
      simpa [Module.Basis.toMatrix_apply, hed] using hm i
    · intro i j hij
      simpa [Module.Basis.toMatrix_apply] using hez j i hij
  obtain ⟨hli, hsp⟩ := (Module.Basis.is_basis_iff_det w).2 hdet
  exact ⟨Module.Basis.mk hli hsp.ge, fun i => by simp⟩

theorem coord_w (w e' : Module.Basis (Fin N) Ω V) (m : Fin N → Ω) (hm : ∀ i, m i ≠ 0)
    (hez : ∀ i j, i < j → w.repr (e' i) j = 0) (hed : ∀ i, w.repr (e' i) i = m i) (r : Fin N) :
    (∀ l, l < r → e'.repr (w l) r = 0) ∧ e'.repr (w r) r = (m r)⁻¹ := by
  have hexp : ∀ l, (∀ j, j < l → e'.repr (w j) r = 0) →
      e'.repr (e' l) r = m l * e'.repr (w l) r := by
    intro l hl
    have h0 : e'.repr (e' l) r = ∑ j, w.repr (e' l) j * e'.repr (w j) r :=
      form_eq_sum w (e'.coord r) (e' l)
    rw [h0, Finset.sum_eq_single l]
    · rw [hed]
    · intro j _ hjl
      rcases lt_or_gt_of_ne hjl with h | h
      · simp [hl j h]
      · simp [hez l j h]
    · simp
  have hlow : ∀ n : ℕ, ∀ l : Fin N, l.val = n → l < r → e'.repr (w l) r = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro l hln hlr
      have h1 := hexp l (fun j hj => ih j.val (by rw [← hln]; exact hj) j rfl (hj.trans hlr))
      have h2 : e'.repr (e' l) r = 0 := by
        simp [Module.Basis.repr_self, Finsupp.single_apply, hlr.ne]
      rw [h2] at h1
      exact (mul_eq_zero.1 h1.symm).resolve_left (hm l)
  have hlow' : ∀ l, l < r → e'.repr (w l) r = 0 := fun l hl => hlow _ l rfl hl
  refine ⟨hlow', ?_⟩
  have h1 := hexp r hlow'
  have h2 : e'.repr (e' r) r = 1 := by simp
  rw [h2] at h1
  exact eq_inv_of_mul_eq_one_right h1.symm

theorem dual_graded (R : Subalgebra O Ω) (L : AddSubgroup V) (L₁ : AddSubgroup V₁)
    (hst : ∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) (w : Module.Basis (Fin N) Ω V) (m : Fin N → Ω)
    (hm : ∀ i, m i ≠ 0)
    (hg : ∀ i s, (∃ v ∈ L, (∀ j, i < j → w.repr v j = 0) ∧ w.repr v i = s) ↔ ∃ a ∈ R, s = a * m i)
    (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω) (hβ : Function.Surjective β.flip)
    (hL₁ : ∀ u, u ∈ L₁ ↔ ∀ v ∈ L, β v u ∈ R) (w₁ : Module.Basis (Fin N) Ω V₁)
    (hw : ∀ i j, β (w i) (w₁ j) = if i = j.rev then 1 else 0) (j : Fin N) (s : Ω) :
    (∃ u ∈ L₁, (∀ l, j < l → w₁.repr u l = 0) ∧ w₁.repr u j = s) ↔
      ∃ a ∈ R, s = a * (m j.rev)⁻¹ := by
  have hcoord : ∀ u l, w₁.repr u l = β (w l.rev) u := by
    intro u l
    rw [form_eq_sum w₁ (β (w l.rev)) u]
    simp [hw, Fin.rev_inj]
  have hex : ∀ i, ∃ v, v ∈ L ∧ (∀ l, i < l → w.repr v l = 0) ∧ w.repr v i = m i := by
    intro i
    obtain ⟨v, hv, h1, h2⟩ := (hg i (m i)).2 ⟨1, one_mem _, by simp⟩
    exact ⟨v, hv, h1, h2⟩
  choose e heL hez hed using hex
  obtain ⟨e', he'⟩ := exists_basis w m hm e hez hed
  have hez' : ∀ i l, i < l → w.repr (e' i) l = 0 := fun i l h => by rw [he']; exact hez i l h
  have hed' : ∀ i, w.repr (e' i) i = m i := fun i => by rw [he']; exact hed i
  set r := j.rev with hr
  obtain ⟨hlow, htop⟩ := coord_w w e' m hm hez' hed' r
  constructor
  · rintro ⟨u, hu, hz, rfl⟩
    refine ⟨m r * w₁.repr u j, ?_, ?_⟩
    · have hmem := (hL₁ u).1 hu _ (heL r)
      have hsum : β (e r) u = m r * w₁.repr u j := by
        have h0 : β (e r) u = ∑ l, w.repr (e r) l * β (w l) u :=
          form_eq_sum w (β.flip u) (e r)
        rw [h0, Finset.sum_eq_single r]
        · rw [hed, hcoord u j]
        · intro l _ hlr
          rcases lt_or_gt_of_ne hlr with h | h
          · have hl : j < l.rev := by
              rw [hr] at h
              have := Fin.rev_lt_rev.2 h
              simpa using this
            have h2 := hcoord u l.rev
            rw [Fin.rev_rev] at h2
            rw [← h2, hz _ hl, mul_zero]
          · simp [hez r l h]
        · simp
      rwa [hsum] at hmem
    · field_simp [hm r]
  · rintro ⟨a, haR, rfl⟩
    obtain ⟨u, hu⟩ := hβ (a • e'.coord r)
    have hβu : ∀ v, β v u = a * e'.repr v r := fun v => by
      have := LinearMap.congr_fun hu v
      simpa using this
    refine ⟨u, (hL₁ u).2 fun v hv => ?_, fun l hl => ?_, ?_⟩
    · obtain ⟨c, hcR, hc⟩ := exists_coeffs R L hst w m hg e heL hez hed N v hv
        (fun l hl => by have := l.isLt; omega)
      have hcoef : e'.repr v r = c r := by
        have : v = ∑ i, c i • e' i := by simpa [he'] using hc
        rw [this]
        set_option synthInstance.maxHeartbeats 100000 in
          simp [map_sum, Finsupp.finsetSum_apply, Finsupp.single_apply]
      rw [hβu, hcoef]
      exact mul_mem haR (hcR r)
    · rw [hcoord, hβu, hlow _ (by simpa [hr] using Fin.rev_lt_rev.2 hl), mul_zero]
    · rw [hcoord, hβu, ← hr, htop]

end Linear

theorem main : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E : ChartBundle O (mseg x) N V) (F : ChartBundle O (mseg x) N V₁) (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω), IsDualLat O x β E.lat F.lat → ∀ (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ), IsFlagFrame x E w b → ∀ w₁ : Module.Basis (Fin N) Ω V₁, (∀ i j, β (w i) (w₁ j) = if i = j.rev then 1 else 0) → IsFlagFrame x F w₁ (fun j => -b j.rev) := by
  intro O _ Ω _ _ K _ _ ι _ x N V _ _ V₁ _ _ E F β hdual w b hE w₁ hw
  refine ⟨fun c hc i => ?_⟩
  have hc' : mseg x c ≠ 0 := hc
  have hx : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc' k (Finset.mem_univ k)
  have hm : ∀ l, (∏ k, x ⟨k, c k⟩ ^ b l k) ≠ 0 := fun l =>
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hx k)
  ext s
  have key := dual_graded (chartRing O (mseg x) c) (E.lat c) (F.lat c)
    (fun a ha v hv => E.stable c a ha v hv) w (fun l => ∏ k, x ⟨k, c k⟩ ^ b l k) hm
    (fun l s => by
      have := Set.ext_iff.1 (hE.graded c hc l) s
      exact this)
    β hdual.1.2 (hdual.2 c hc') w₁ hw i s
  have hinv : (∏ k, x ⟨k, c k⟩ ^ b i.rev k)⁻¹ = ∏ k, x ⟨k, c k⟩ ^ (-b i.rev) k := by
    rw [← Finset.prod_inv_distrib]
    exact Finset.prod_congr rfl fun k _ => by simp [zpow_neg]
  rw [hinv] at key
  exact key

end GlobalTheory.CompanionTheory.Ar.Num.FlagDual
end

section -- merged from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DualLatticeFlagFrameStatement
open MvPolynomial GlobalTheory.CompanionTheory.Ar.Num GroundTheory.Heights₂.Heights.NumbersDVR
open ReciprocityTheory.ChartRestriction.G.Geo (ChartBundle chartRing)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg mcIdeal chartMon joinCoord bcCoord pullDeg liftVar fnField ck rootNum SameGeneric LatLE IsPull IsPullBC IsSubQuot QuotIso IsFrobPres FlagModel modelDeg)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dual_lattice_flag_frame : ∀ (O : Type) [CommRing O] (Ω : Type) [Field Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (x : (Σ k, ι k) → Ω) (N : ℕ) (V : Type) [AddCommGroup V] [Module Ω V] (V₁ : Type) [AddCommGroup V₁] [Module Ω V₁] (E : ChartBundle O (mseg x) N V) (F : ChartBundle O (mseg x) N V₁) (β : V →ₗ[Ω] V₁ →ₗ[Ω] Ω), IsDualLat O x β E.lat F.lat → ∀ (w : Module.Basis (Fin N) Ω V) (b : Fin N → K → ℤ), IsFlagFrame x E w b → ∀ w₁ : Module.Basis (Fin N) Ω V₁, (∀ i j, β (w i) (w₁ j) = if i = j.rev then 1 else 0) → IsFlagFrame x F w₁ (fun j => -b j.rev) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FlagDual.main | exact GlobalTheory.CompanionTheory.Ar.Num.FlagDual.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FlagDual.main <;> assumption)
end
end
