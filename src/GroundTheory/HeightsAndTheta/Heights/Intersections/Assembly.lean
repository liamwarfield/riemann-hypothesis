module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBridge
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPFFibreMult
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PValCentreZ
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Assembly
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PProjBundleFibre
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PPtsAbsMeasurable
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PChartNormPts
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PThmISymm
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFibreMultiHomog
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedE

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagMinorsTrdeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

section

variable (F : Type) [Field F] (n : ℕ)

abbrev PivotIdx := Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) ≤ b}

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisTail
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

theorem VerticalEmbedding.proof (hD : regularityDehomogenization_holds.Statement) (hC : regularityLocalCardinality_holds.Statement) (hL : RegularityLocalProduct.Statement) :
    VerticalEmbedding.Statement := by
  classical
  intro K _ ι _ P f g a x hP hf hg hfP hgP hx
  have : P.IsPrime := hP.2.1.1

  let t : Ideal (MRing ι) → MRing ι := fun W =>
    if h : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W then ∏ k, (X ⟨k, (h k).choose⟩ : MRing ι) ^ a k else 1
  have ht : ∀ W : Ideal (MRing ι), W.IsPrime → ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W → ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (t W) a ∧ t W ∉ W := by
    intro W hWp hW
    simp only [t, dif_pos hW]
    refine ⟨AvoidRing.isMultiHomog_coordProd _ _, fun hmem => ?_⟩
    obtain ⟨k, -, hk⟩ := hWp.prod_mem_iff.mp hmem
    exact (hW k).choose_spec (hWp.mem_of_pow_mem _ hk)
  have hne : ∀ W : Ideal (MRing ι), P ≤ W → t W ∉ W →
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W)) ≠ 0 := by
    intro W hPW htW h0
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h0
    exact htW (hPW h0)

  let y : MRing ι → Ideal (MRing ι) → FractionRing (MRing ι ⧸ P) := fun s W =>
    algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s) /
      algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W))
  have hdata : ∀ (s : MRing ι), ∀ W ∈ divSupp P s, P ≤ W ∧ W.IsPrime ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (t W) a ∧ t W ∉ W ∧
      ∀ s' : MRing ι, y s' W * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (t W)) =
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P s') := by
    intro s W hW
    have hPW : P ≤ W := le_trans le_sup_left hW.1.1.2
    obtain ⟨h1, h2⟩ := ht W hW.1.1.1 hW.2
    exact ⟨hPW, hW.1.1.1, h1, h2, fun s' => div_mul_cancel₀ _ (hne W hPW h2)⟩

  have term : ∀ s : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a → s ∉ P → ∀ W ∈ divSupp P s,
      (multAt (P ⊔ Ideal.span {s}) W : ℝ) *
          (if IsHorizontal W then 0 else
            (geoNum 0 W (fun j => ((Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j).a) : ℝ) * Real.log (charOf W)) =
        Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y s W))) := by
    intro s hs hsP W hW
    have hA : IsSectionOn P (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun k => (a k : ℤ))) s :=
      ⟨a, fun _ => rfl, hs, hsP⟩
    rw [if_neg (not_isHorizontal_of_dimOne arithVarZero hP hA hW)]
    obtain ⟨-, -, hta, htW, hy⟩ := hdata s W hW
    obtain ⟨hyW, hm⟩ := hD K ι P s (t W) a W (y s W) hP.2.1 hs hsP hW hta htW (hy s)
    have hy0 : y s W ≠ 0 := by
      intro h0
      have h1 := hy s
      rw [h0, zero_mul, eq_comm, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h1
      exact hsP h1
    rw [hm]
    exact hC K ι P s a W _ (y s W) hP hs hsP hW hyW hy0
  have hvert : ∀ s : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s a → s ∉ P →
      vertR P (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) s =
        ∑ᶠ W ∈ divSupp P s, Real.log (Nat.card (locRing P W ⧸ locIdeal P W (y s W))) := by
    intro s hs hsP
    unfold vertR
    exact finsum_mem_congr rfl fun W hW => term s hs hsP W hW
  rw [hvert f hf hfP, hvert g hg hgP]
  refine hL K ι P f g a x t (y f) (y g) hP hf hg hfP hgP hx fun W hW => ?_
  obtain ⟨-, -, hta, htW, hy⟩ : P ≤ W ∧ W.IsPrime ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (t W) a ∧ t W ∉ W ∧ _ := by
    rcases hW with hW | hW
    · exact hdata f W hW
    · exact hdata g W hW
  exact ⟨hta, htW, hy f, hy g⟩

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisLast
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

theorem VerticalClosedPoints.proof (hE : regularityEmbedding_holds.Statement) (hV : VerticalEmbedding.Statement) : VerticalClosedPoints.Statement := by
  intro K _ ι _ P f g a R hP hf hg hfP hgP hR hRu
  have : P.IsPrime := hP.2.1.1
  obtain ⟨x, hx⟩ := exists_funField_mul_eq hf hg hgP
  obtain ⟨e, he⟩ := hE K ι P R hP hR hRu
  rw [hV K ι P f g a x hP hf hg hfP hgP hx]
  have hA : IsSectionOn P (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun k => (a k : ℤ))) g :=
    ⟨a, fun _ => rfl, hg, hgP⟩
  have key : ∀ t : R, Real.log ‖e t x‖ =
      Real.log (‖eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) f)‖ /
        ‖eval (t : (Σ k, ι k) → ℂ) (map (Int.castRingHom ℂ) g)‖) := by
    intro t
    have hg0 := eval_ne_zero_of_dimOne arithVarZero hP hA (hR t t.2)
    rw [← he t f g a hf hg hgP x hx, norm_mul, mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hg0)]
  rw [← finsum_comp_equiv e, finsum_eq_sum_of_fintype, Fintype.sum_congr _ _ key]
  exact Finset.sum_coe_sort R (fun t => Real.log (‖eval t (map (Int.castRingHom ℂ) f)‖ /
    ‖eval t (map (Int.castRingHom ℂ) g)‖))

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagArith
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Flag

variable {K : Type} {ι : K → Type}

end Flag

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PProjBundleMultiHomogSpan
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]



def genMap (P : Ideal (MRing ι)) {N1 : ℕ} {S : Type} [Fintype S] (v : S → Fin N1 → FnField P) :
    MRing (PBlk ι N1) →+* MvPolynomial S (FnField P) :=
  eval₂Hom (Int.castRingHom _) fun
    | ⟨.inl k, i⟩ => C (genPt P ⟨k, i⟩)
    | ⟨.inr _, j⟩ => ∑ s, C (v s j) * X s



end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.LogNormDivSameOrbit
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

theorem log_norm_div_sameOrbit {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {f g : MRing ι} {a : K → ℕ} (hf : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f a) (hg : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog g a)
    {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    Real.log (‖eval z (map (Int.castRingHom ℂ) f)‖ / ‖eval z (map (Int.castRingHom ℂ) g)‖) =
      Real.log (‖eval z' (map (Int.castRingHom ℂ) f)‖ / ‖eval z' (map (Int.castRingHom ℂ) g)‖) := by
  obtain ⟨c, hc, rfl⟩ := h
  have hc0 : ‖∏ k, c k ^ a k‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))
  rw [eval_smul_homog f a hf c z', eval_smul_homog g a hg c z', norm_mul, norm_mul,
    mul_div_mul_left _ _ hc0]

theorem RegularityProductFormula.proof (hPts : regularityPointsSum_holds.Statement) (hVert : VerticalClosedPoints.Statement) :
    RegularityProductFormula.Statement := by
  intro K _ ι _ P f g a hP hf hg hfP hgP
  obtain ⟨R, hRP, hRu, hsum⟩ := hPts K ι P hP
  rw [hVert K ι P f g a R hP hf hg hfP hgP hRP hRu]
  exact (hsum _ fun z z' _ h => log_norm_div_sameOrbit hf hg h).symm

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PIntClosureLocFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

theorem IntClosureLocFinite.proof (h : RelAlgClosureFinite.Statement) :
    IntClosureLocFinite.Statement := by
  classical
  intro F L _ _ φ S hS A T hDA hloc
  let : Algebra A L := (φ.comp A.subtype).toAlgebra

  let D : Subring F := Subring.closure (T : Set F)
  have : Algebra.FiniteType ℤ D :=
    Algebra.FiniteType.equiv ((Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset T))
      (Subring.closureEquivAdjoinInt _).symm
  let : Algebra D L := (φ.comp D.subtype).toAlgebra
  let : Algebra D A := (Subring.inclusion hDA).toAlgebra
  have : IsScalarTower D A L := IsScalarTower.of_algebraMap_eq fun _ => rfl

  let K := FractionRing D
  have hinj : Function.Injective (φ.comp D.subtype) := φ.injective.comp Subtype.val_injective
  let : Algebra K L := (IsFractionRing.lift hinj).toAlgebra
  have : IsScalarTower D K L :=
    IsScalarTower.of_algebraMap_eq fun d => (IsFractionRing.lift_algebraMap hinj d).symm
  have hKS : IntermediateField.adjoin K (S : Set L) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : x ∈ Subfield.closure (S : Set L) := hS ▸ Subfield.mem_top x
    exact (Subfield.closure_le (t := (IntermediateField.adjoin K (S : Set L)).toSubfield)).mpr
      (IntermediateField.subset_adjoin K _) hx

  let M := algebraicClosure K L
  have : FiniteDimensional K M := h K L S hKS
  have : IsScalarTower D M L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfin : Module.Finite D (integralClosure D M) :=
    GroundTheory.Heights₂.Heights.Model.FiniteIntegralClosure.full D K M
  obtain ⟨s, hs⟩ := hfin.fg_top
  refine ⟨s.image fun g : integralClosure D M => ((g : M) : L), fun x hx => ?_⟩

  let U : Submonoid D := (IsUnit.submonoid A).comap (Subring.inclusion hDA)
  have : IsLocalization U A := by
    rw [isLocalization_iff]
    refine ⟨fun y => y.2, fun z => ?_, fun {d₁ d₂} hd => ⟨1, ?_⟩⟩
    · obtain ⟨b, hb, c, hc, hc0, hcA, hzc⟩ := hloc z z.2
      have hunit : IsUnit (Subring.inclusion hDA ⟨c, hc⟩) :=
        IsUnit.of_mul_eq_one (⟨c⁻¹, hcA⟩ : A) (Subtype.ext (mul_inv_cancel₀ hc0))
      exact ⟨(⟨b, hb⟩, ⟨⟨c, hc⟩, hunit⟩), Subtype.ext hzc⟩
    · rw [Subring.inclusion_injective hDA hd]
  obtain ⟨⟨m, hm⟩, hmx⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (Rₘ := A) U x hx

  obtain ⟨y, hy⟩ : ∃ y : L, y = (⟨m, hm⟩ : U) • x := ⟨_, rfl⟩
  rw [← hy] at hmx
  have hyK : IsIntegral K y := hmx.tower_top
  let yM : M := ⟨y, hyK⟩
  have hyMint : IsIntegral D yM := by
    rw [← isIntegral_algHom_iff (IsScalarTower.toAlgHom D M L) (fun a b hab => Subtype.ext hab)]
    exact hmx
  have hyspan : (⟨yM, hyMint⟩ : integralClosure D M) ∈ Submodule.span D (s : Set _) :=
    hs ▸ Submodule.mem_top
  let f : integralClosure D M →ₗ[D] L :=
    (IsScalarTower.toAlgHom D M L).toLinearMap ∘ₗ (integralClosure D M).val.toLinearMap
  have hyD : y ∈ Submodule.span D ((s.image fun g : integralClosure D M => ((g : M) : L)) : Set L) := by
    have hmap := Submodule.mem_map_of_mem (f := f) hyspan
    rw [Submodule.map_span] at hmap
    rw [Finset.coe_image]
    exact hmap
  have hyA := Submodule.span_subset_span D A _ hyD

  have hu : IsUnit (algebraMap D A m) := hm
  have hyu : y = (hu.unit : A) • x := by
    rw [hy, Submonoid.smul_def, IsUnit.unit_spec, algebraMap_smul]
  have hx' : x = ((hu.unit⁻¹ : Aˣ) : A) • y := by
    rw [hyu, smul_smul, Units.inv_mul, one_smul]
  rw [hx']
  exact Submodule.smul_mem _ _ hyA

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PFnDegAdjoin
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1

namespace FnDegAdjoin

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {σ : Type}

def quotEquiv (g : σ → Ω) (I : Ideal (MvPolynomial σ F))
    (h : I = RingHom.ker (aeval g : MvPolynomial σ F →ₐ[F] Ω)) :
    (MvPolynomial σ F ⧸ I) ≃ₐ[F] Algebra.adjoin F (Set.range g) :=
  let e1 := Ideal.quotientEquivAlgOfEq F h
  let e2 := Ideal.quotientKerEquivRange (aeval g : MvPolynomial σ F →ₐ[F] Ω)
  let e3 := Subalgebra.equivOfEq _ _ (aeval_range (R := F) g)
  (e1.trans e2).trans e3

theorem quotEquiv_mk (g : σ → Ω) (I : Ideal (MvPolynomial σ F))
    (h : I = RingHom.ker (aeval g : MvPolynomial σ F →ₐ[F] Ω)) (p : MvPolynomial σ F) :
    (quotEquiv g I h (Ideal.Quotient.mk I p) : Ω) = aeval g p :=
  rfl

theorem incl_apply {S T : Subalgebra F Ω} (h : S ≤ T) (x : S) :
    ((Subalgebra.inclusion h).toRingHom x : Ω) = x :=
  rfl

theorem toRingHom_apply {A B : Type} [CommRing A] [CommRing B] [Algebra F A] [Algebra F B] (f : A →ₐ[F] B) (a : A) :
    f.toRingHom a = f a :=
  rfl

end FnDegAdjoin

theorem FnDegAdjoin.proof : FnDegAdjoin.Statement := by
  classical
  intro F Ω _ _ _ K _ ι _ K' _ ι' _ v x' i' hx hV
  have hker : ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal (RingHom.ker (aeval x' : MRingOver F ι' →ₐ[F] Ω)) i' =
      RingHom.ker (aeval (fun q => x' q / x' ⟨q.1, i' q.1⟩) : MRingOver F ι' →ₐ[F] Ω) :=
    ChartRankAdjoin.chartIdeal_eq_ker hx hV
  have hcomap : (ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal (RingHom.ker (aeval x' : MRingOver F ι' →ₐ[F] Ω)) i').comap
      (rename v : MRingOver F ι →ₐ[F] MRingOver F ι').toRingHom =
      RingHom.ker (aeval ((fun q => x' q / x' ⟨q.1, i' q.1⟩) ∘ v) : MRingOver F ι →ₐ[F] Ω) := by
    rw [hker]
    ext p
    simp only [Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_rename]
  let _ := adjoinInclAlgebra F (Set.range_comp_subset_range v fun q => x' q / x' ⟨q.1, i' q.1⟩)
  unfold fnDeg
  let _ := (chartMap v (RingHom.ker (aeval x' : MRingOver F ι' →ₐ[F] Ω)) i').toAlgebra
  have key := Algebra.finrank_eq_of_equiv_equiv (FnDegAdjoin.quotEquiv _ _ hcomap).toRingEquiv
    (FnDegAdjoin.quotEquiv _ _ hker).toRingEquiv
  refine key ?_
  refine RingHom.ext fun a => ?_
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  apply Subtype.ext
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv]
  rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra, chartMap, Ideal.quotientMap_mk]
  rw [FnDegAdjoin.incl_apply, FnDegAdjoin.toRingHom_apply, FnDegAdjoin.quotEquiv_mk, FnDegAdjoin.quotEquiv_mk,
    aeval_rename]

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PRankAdjoinFrac
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open Module IntermediateField IntermediateField.algebraAdjoinAdjoin

namespace RankAdjoinFrac

theorem finrank_algebraAdjoin_eq_finrank_adjoin {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] (T : Set Ω) :
    finrank K (Algebra.adjoin K T) = finrank K (IntermediateField.adjoin K T) := by
  by_cases hT : ∀ x ∈ T, IsAlgebraic K x
  · rw [← IntermediateField.finrank_eq_finrank_subalgebra, adjoin_toSubalgebra_of_isAlgebraic hT]
  · push Not at hT
    obtain ⟨x, hx, hnx⟩ := hT
    have h1 : finrank K (Algebra.adjoin K T) = 0 := by
      by_contra h0
      have := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h0)
      exact hnx ((Algebra.IsAlgebraic.isAlgebraic
        (⟨x, Algebra.subset_adjoin hx⟩ : Algebra.adjoin K T)).algHom (Algebra.adjoin K T).val)
    have h2 : finrank K (IntermediateField.adjoin K T) = 0 := by
      by_contra h0
      have := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h0)
      exact hnx ((Algebra.IsAlgebraic.isAlgebraic
        (⟨x, subset_adjoin K T hx⟩ : IntermediateField.adjoin K T)).algHom (IntermediateField.adjoin K T).val)
    rw [h1, h2]

theorem exists_mul_mem_of_mem {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {S T : Set Ω} (h : S ⊆ T) {y : Ω}
    (hy : y ∈ Algebra.adjoin (IntermediateField.adjoin F S) T) :
    ∃ a ∈ Algebra.adjoin F S, a ≠ 0 ∧ a * y ∈ Algebra.adjoin F T := by
  have hST := Algebra.adjoin_mono (R := F) h
  induction hy using Algebra.adjoin_induction with
  | mem x hx => exact ⟨1, one_mem _, one_ne_zero, by rw [one_mul]; exact Algebra.subset_adjoin hx⟩
  | algebraMap k =>
    obtain ⟨r, hr, s, hs, hk⟩ := mem_adjoin_iff_div.mp k.2
    by_cases hs0 : s = 0
    · refine ⟨1, one_mem _, one_ne_zero, ?_⟩
      have : (algebraMap (IntermediateField.adjoin F S) Ω k) = 0 := by
        change (k : Ω) = 0
        rw [hk, hs0, div_zero]
      rw [this, mul_zero]
      exact zero_mem _
    · refine ⟨s, hs, hs0, ?_⟩
      change s * (k : Ω) ∈ _
      rw [hk, mul_div_cancel₀ _ hs0]
      exact hST hr
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, ha0, hax⟩ := hx
    obtain ⟨b, hb, hb0, hby⟩ := hy
    refine ⟨a * b, mul_mem ha hb, mul_ne_zero ha0 hb0, ?_⟩
    have : a * b * (x + y) = b * (a * x) + a * (b * y) := by ring
    rw [this]
    exact add_mem (mul_mem (hST hb) hax) (mul_mem (hST ha) hby)
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, ha0, hax⟩ := hx
    obtain ⟨b, hb, hb0, hby⟩ := hy
    refine ⟨a * b, mul_mem ha hb, mul_ne_zero ha0 hb0, ?_⟩
    have : a * b * (x * y) = (a * x) * (b * y) := by ring
    rw [this]
    exact mul_mem hax hby

theorem finrank_eq_finrank_algebraAdjoin {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] {S T : Set Ω}
    (h : S ⊆ T) :
    letI := adjoinInclAlgebra F h
    finrank (Algebra.adjoin F S) (Algebra.adjoin F T) =
      finrank (IntermediateField.adjoin F S) (Algebra.adjoin (IntermediateField.adjoin F S) T) := by
  let _ := adjoinInclAlgebra F h
  let _ : Algebra (Algebra.adjoin F S) (Algebra.adjoin (IntermediateField.adjoin F S) T) :=
    ((algebraMap (IntermediateField.adjoin F S) (Algebra.adjoin (IntermediateField.adjoin F S) T)).comp
      (algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S))).toAlgebra
  have : IsScalarTower (Algebra.adjoin F S) (IntermediateField.adjoin F S)
      (Algebra.adjoin (IntermediateField.adjoin F S) T) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hle : Algebra.adjoin F T ≤ (Algebra.adjoin (IntermediateField.adjoin F S) T).restrictScalars F :=
    Algebra.adjoin_le (Algebra.subset_adjoin (R := IntermediateField.adjoin F S))
  let f : Algebra.adjoin F T →ₗ[Algebra.adjoin F S] Algebra.adjoin (IntermediateField.adjoin F S) T :=
    { toFun := fun m => ⟨m.1, hle m.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun r m => by
        apply Subtype.ext
        simp only [Algebra.smul_def, RingHom.id_apply, Subalgebra.coe_mul, RingHom.algebraMap_toAlgebra,
          RingHom.comp_apply, Subalgebra.coe_algebraMap, IntermediateField.algebraMap_apply,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Subalgebra.coe_inclusion] }
  have : IsLocalizedModule (nonZeroDivisors (Algebra.adjoin F S)) f := by
    refine ⟨fun x => ?_, fun y => ?_, fun {x₁ x₂} hx => ?_⟩
    · rw [Module.End.isUnit_iff]
      have hx0 : algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S) x ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective (Algebra.adjoin F S) (IntermediateField.adjoin F S))).mpr
          (nonZeroDivisors.coe_ne_zero x)
      refine ⟨fun u v huv => ?_, fun v => ?_⟩
      · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply,
          ← algebraMap_smul (IntermediateField.adjoin F S) (x : Algebra.adjoin F S) u,
          ← algebraMap_smul (IntermediateField.adjoin F S) (x : Algebra.adjoin F S) v] at huv
        calc u = (algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S) x)⁻¹ •
              (algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S) x • u) := by
                rw [smul_smul, inv_mul_cancel₀ hx0, one_smul]
          _ = v := by rw [huv, smul_smul, inv_mul_cancel₀ hx0, one_smul]
      · refine ⟨(algebraMap (Algebra.adjoin F S) (IntermediateField.adjoin F S) x)⁻¹ • v, ?_⟩
        rw [Module.algebraMap_end_apply, ← algebraMap_smul (IntermediateField.adjoin F S), smul_smul,
          mul_inv_cancel₀ hx0, one_smul]
    · obtain ⟨a, ha, ha0, hay⟩ := exists_mul_mem_of_mem h y.2
      refine ⟨(⟨a * y, hay⟩, ⟨⟨a, ha⟩, mem_nonZeroDivisors_of_ne_zero ?_⟩), ?_⟩
      · exact fun h0 => ha0 (congrArg Subtype.val h0)
      · apply Subtype.ext
        simp only [Submonoid.smul_def, Algebra.smul_def, Subalgebra.coe_mul, RingHom.algebraMap_toAlgebra,
          RingHom.comp_apply, Subalgebra.coe_algebraMap, IntermediateField.algebraMap_apply]
        rfl
    · refine ⟨1, ?_⟩
      rw [one_smul, one_smul]
      exact Subtype.ext (congrArg (fun z : Algebra.adjoin (IntermediateField.adjoin F S) T => (z : Ω)) hx)
  rw [← IsLocalizedModule.finrank_eq (nonZeroDivisors (Algebra.adjoin F S)) f le_rfl,
    IsLocalization.finrank_eq (IntermediateField.adjoin F S) (nonZeroDivisors (Algebra.adjoin F S)) le_rfl]

theorem proof : RankAdjoinFrac.Statement := by
  intro F Ω _ _ _ S T h
  have hKL : IntermediateField.adjoin F S ≤ IntermediateField.adjoin F T := adjoin.mono F S T h
  have hE : extendScalars hKL = IntermediateField.adjoin (IntermediateField.adjoin F S) T :=
    restrictScalars_injective F (by
      rw [extendScalars_restrictScalars, adjoin_adjoin_left, Set.union_eq_self_of_subset_left h])
  have key : IntermediateField.relfinrank (IntermediateField.adjoin F S) (IntermediateField.adjoin F T) =
      finrank (IntermediateField.adjoin F S) (Algebra.adjoin (IntermediateField.adjoin F S) T) := by
    rw [relfinrank_eq_finrank_of_le hKL, hE, finrank_algebraAdjoin_eq_finrank_adjoin]
  exact (finrank_eq_finrank_algebraAdjoin h).trans key.symm

end RankAdjoinFrac

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PRankFracDegree
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

theorem RankFracDegree.isFractionRing_of_closure {F Ω A : Type} [Field F] [Field Ω] [Algebra F Ω] [CommRing A]
    (K : IntermediateField F Ω) (f : A →+* Ω) (hf : Function.Injective f) (hK : ∀ a, f a ∈ K)
    (hcl : K.toSubfield ≤ Subfield.closure (Set.range f)) :
    @IsFractionRing A _ K _ (f.codRestrict K hK).toAlgebra := by
  let _ : Algebra A K := (f.codRestrict K hK).toAlgebra
  have hmap : ∀ a, ((algebraMap A K a : K) : Ω) = f a := fun _ => rfl
  have hnz : ∀ a : A, a ∈ nonZeroDivisors A → f a ≠ 0 := by
    intro a ha h0
    have h10 : (1 : A) = 0 :=
      mem_nonZeroDivisors_iff_right.mp ha 1 (by rw [one_mul]; exact hf (by rw [h0, map_zero]))
    exact one_ne_zero (by simpa using congrArg f h10 : (1 : Ω) = 0)
  show IsLocalization (nonZeroDivisors A) K
  rw [isLocalization_iff]
  refine ⟨fun y => IsUnit.mk0 _ fun h => hnz y y.2 (by rw [← hmap, h]; rfl), fun z => ?_, fun {x y} h => ?_⟩
  · obtain ⟨y, hy, w, hw, hyw⟩ := Subfield.mem_closure_iff.mp (hcl z.2)
    rw [← RingHom.coe_range, Subring.closure_eq] at hy hw
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨a', rfl⟩ := hw
    by_cases h0 : f a' = 0
    · refine ⟨(0, 1), Subtype.ext ?_⟩
      simp only [OneMemClass.coe_one, map_zero, map_one, mul_one, ZeroMemClass.coe_zero]
      rw [← hyw, h0, div_zero]
    · have ha' : a' ∈ nonZeroDivisors A :=
        mem_nonZeroDivisors_of_injective hf (mem_nonZeroDivisors_of_ne_zero h0)
      refine ⟨(a, ⟨a', ha'⟩), Subtype.ext ?_⟩
      simp only [MulMemClass.coe_mul, hmap]
      rw [← hyw, div_mul_cancel₀ _ h0]
  · refine ⟨1, ?_⟩
    have hxy : x = y := hf (by rw [← hmap x, ← hmap y, h])
    rw [hxy]

theorem RankFracDegree.proof : RankFracDegree.Statement := by
  intro F Ω A B _ _ _ _ _ _ L₀ L f g hf hg hfg hfL₀ hgL hL₀ hL _
  have hle : L₀ ≤ L := by
    intro x hx
    have h1 : x ∈ Subfield.closure (Set.range g) := by
      refine Subfield.closure_mono ?_ (hL₀ hx)
      rintro _ ⟨a, rfl⟩
      exact ⟨algebraMap A B a, hfg a⟩
    exact (Subfield.closure_le (t := L.toSubfield)).mpr (by rintro _ ⟨b, rfl⟩; exact hgL b) h1
  let L' := IntermediateField.extendScalars hle
  let _ : Algebra A L₀ := (f.codRestrict L₀ hfL₀).toAlgebra
  let _ : Algebra B L' := (g.codRestrict L' hgL).toAlgebra
  let _ : Algebra A L' := ((algebraMap L₀ L').comp (algebraMap A L₀)).toAlgebra
  have _ : IsScalarTower A L₀ L' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower A B L' := IsScalarTower.of_algebraMap_eq fun a => Subtype.ext (hfg a).symm
  have _ : IsFractionRing A L₀ := RankFracDegree.isFractionRing_of_closure L₀ f hf hfL₀ hL₀
  have _ : IsFractionRing B L' := RankFracDegree.isFractionRing_of_closure L' g hg hgL hL
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]
  exact (IsFractionRing.finrank_eq A L₀ B L').symm

end GroundTheory.Heights₂.Heights.Inter
end
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

theorem RegularityFunctionFieldNumber.full : GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber.proof

theorem RegularityDivisorSupportClosed.full : GroundTheory.Heights₂.Heights.Inter.RegularityDivisorSupportClosed.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityDivisorSupportClosed.proof

theorem LocRingPow.full : GroundTheory.Heights₂.Heights.Inter.LocRingPow.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingPow.proof

theorem RegularityDenominator.full : GroundTheory.Heights₂.Heights.Inter.RegularityDenominator.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityDenominator.proof GroundTheory.Heights₂.Heights.Inter.RegularityDivisorSupportClosed.full GroundTheory.Heights₂.Heights.Inter.LocRingPow.full

theorem RegularityValuationCentre.full : GroundTheory.Heights₂.Heights.Inter.RegularityValuationCentre.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityValuationCentre.proof

theorem RegularityRelativeClosedPoint.full : GroundTheory.Heights₂.Heights.Inter.RegularityRelativeClosedPoint.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityRelativeClosedPoint.proof

theorem RegularityIntegral.full : GroundTheory.Heights₂.Heights.Inter.RegularityIntegral.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityIntegral.proof GroundTheory.Heights₂.Heights.Inter.RegularityValuationCentre.full GroundTheory.Heights₂.Heights.Inter.RegularityRelativeClosedPoint.full

theorem RegularityOrder.full : GroundTheory.Heights₂.Heights.Inter.RegularityOrder.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityOrder.proof GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber.full GroundTheory.Heights₂.Heights.Inter.RegularityDenominator.full GroundTheory.Heights₂.Heights.Inter.RegularityIntegral.full

theorem RegularityLocalPrime.full : GroundTheory.Heights₂.Heights.Inter.RegularityLocalPrime.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityLocalPrime.proof GroundTheory.Heights₂.Heights.Inter.RegularityOrder.full

theorem RegularityLocalize.full : GroundTheory.Heights₂.Heights.Inter.RegularityLocalize.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityLocalize.proof GroundTheory.Heights₂.Heights.Inter.RegularityLocalPrime.full

theorem regularityLocalDimension_holds.full : GroundTheory.Heights₂.Heights.Inter.regularityLocalDimension_holds.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.regularityLocalDimension_holds

theorem RegularityLocalFinite.full : GroundTheory.Heights₂.Heights.Inter.RegularityLocalFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityLocalFinite.proof GroundTheory.Heights₂.Heights.Inter.regularityLocalDimension_holds.full

theorem LocRingNoeth.full : GroundTheory.Heights₂.Heights.Inter.LocRingNoeth.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.LocRingNoeth

theorem pointForm_holds.full : GroundTheory.Heights₂.Heights.Inter.pointForm_holds.Statement :=
  GroundTheory.Heights₂.Heights.Targets.Contract.pulledBackForms_topDensity_vanish

theorem PullbackEliminationOfVariable.full : GroundTheory.Heights₂.Heights.Inter.PullbackEliminationOfVariable.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PullbackEliminationOfVariable.proof

theorem PullbackVanishingOfNullCycle.full : GroundTheory.Heights₂.Heights.Inter.PullbackVanishingOfNullCycle.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PullbackVanishingOfNullCycle.proof GroundTheory.Heights₂.Heights.Inter.PullbackEliminationOfVariable.full

theorem RankAdjoinFrac.full : GroundTheory.Heights₂.Heights.Inter.RankAdjoinFrac.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RankAdjoinFrac.proof

theorem regularityEmbedding_holds.full : GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds.proof

theorem ProjectivePointVertical.full : GroundTheory.Heights₂.Heights.Inter.ProjectivePointVertical.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ProjectivePointVertical.proof (by intros; exact GroundTheory.Heights₂.Heights.geoNumStatement _) (by intros; exact GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full _ _) (by intros; exact GroundTheory.Heights₂.Heights.Targets.ProjContract.full _ _ _ _ _)

theorem PushforwardProjectivePoint.full : GroundTheory.Heights₂.Heights.Inter.PushforwardProjectivePoint.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PushforwardProjectivePoint.proof GroundTheory.Heights₂.Heights.imageArith GroundTheory.Heights₂.Heights.Inter.pointForm_holds.full GroundTheory.Heights₂.Heights.Inter.ProjectivePointVertical.full

theorem ArithmeticIntersectionHorizontal.full : GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal.proof ReciprocityTheory.ChartRestriction.G.Geo.divSuppArith GroundTheory.Heights₂.Heights.imageArith GroundTheory.Heights₂.Heights.Inter.PushforwardProjectivePoint.full

theorem ArithmeticIntersectionFibreMultiHomogeneous.full : GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionFibreMultiHomogeneous.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionFibreMultiHomogeneous.proof

theorem EvalKerKrullDim.full : GroundTheory.Heights₂.Heights.Inter.EvalKerKrullDim.Statement :=
  GroundTheory.Heights₂.Heights.Inter.EvalKerKrullDim.proof

theorem FibreTranscendenceDegreeAlt.full : GroundTheory.Heights₂.Heights.Inter.FibreTranscendenceDegreeAlt.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FibreTranscendenceDegreeAlt.proof GroundTheory.Heights₂.Heights.Inter.EvalKerKrullDim.full

theorem FibreDimensionZero.full : GroundTheory.Heights₂.Heights.Inter.FibreDimensionZero.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FibreDimensionZero.proof GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionFibreMultiHomogeneous.full GroundTheory.Heights₂.Heights.Inter.EvalKerKrullDim.full GroundTheory.Heights₂.Heights.Inter.FibreTranscendenceDegreeAlt.full

theorem ChartRankAdjoin.full : GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin.proof

theorem FnDegAdjoin.full : GroundTheory.Heights₂.Heights.Inter.FnDegAdjoin.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FnDegAdjoin.proof

theorem ChartScalingIndep.full : GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.proof

theorem AdjoinIndepRelfinrank.full : GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.Statement :=
  GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.proof

theorem FinrankAdjoinRange.full : GroundTheory.Heights₂.Heights.Inter.FinrankAdjoinRange.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FinrankAdjoinRange.proof

theorem VerticalDegreeAfterAdjoining.full : GroundTheory.Heights₂.Heights.Inter.VerticalDegreeAfterAdjoining.Statement :=
  GroundTheory.Heights₂.Heights.Inter.VerticalDegreeAfterAdjoining.proof GroundTheory.Heights₂.Heights.Inter.RankAdjoinFrac.full GroundTheory.Heights₂.Heights.Inter.FnDegAdjoin.full GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.full GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.full GroundTheory.Heights₂.Heights.Inter.FinrankAdjoinRange.full

theorem VerticalDegree.full : GroundTheory.Heights₂.Heights.Inter.VerticalDegree.Statement :=
  GroundTheory.Heights₂.Heights.Inter.VerticalDegree.proof GroundTheory.Heights₂.Heights.Inter.FibreDimensionZero.full GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin.full GroundTheory.Heights₂.Heights.Inter.VerticalDegreeAfterAdjoining.full

theorem ValCentreZ.full : GroundTheory.Heights₂.Heights.Inter.ValCentreZ.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ValCentreZ.proof

theorem CentreOverW.full : GroundTheory.Heights₂.Heights.Inter.CentreOverW.Statement :=
  GroundTheory.Heights₂.Heights.Inter.CentreOverW.proof

theorem SemilocIntegral.full : GroundTheory.Heights₂.Heights.Inter.SemilocIntegral.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocIntegral.proof GroundTheory.Heights₂.Heights.Inter.ValCentreZ.full GroundTheory.Heights₂.Heights.Inter.CentreOverW.full

theorem LocRingChartLoc.full : GroundTheory.Heights₂.Heights.Inter.LocRingChartLoc.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingChartLoc.proof

theorem RelAlgClosureFinite.full : GroundTheory.Heights₂.Heights.Inter.RelAlgClosureFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RelAlgClosureFinite.proof

theorem IntClosureLocFinite.full : GroundTheory.Heights₂.Heights.Inter.IntClosureLocFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.IntClosureLocFinite.proof GroundTheory.Heights₂.Heights.Inter.RelAlgClosureFinite.full

theorem LocRingIntClosureFinite.full : GroundTheory.Heights₂.Heights.Inter.LocRingIntClosureFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingIntClosureFinite.proof GroundTheory.Heights₂.Heights.Inter.LocRingChartLoc.full GroundTheory.Heights₂.Heights.Inter.IntClosureLocFinite.full

theorem LocRingFrac.full : GroundTheory.Heights₂.Heights.Inter.LocRingFrac.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingFrac.proof

theorem LocRingLocal.full : GroundTheory.Heights₂.Heights.Inter.LocRingLocal.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.LocRingLocal

theorem LocRingDimOne.full : GroundTheory.Heights₂.Heights.Inter.LocRingDimOne.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingDimOne.proof GroundTheory.Heights₂.Heights.Inter.LocRingFrac.full GroundTheory.Heights₂.Heights.Inter.LocRingNoeth.full GroundTheory.Heights₂.Heights.Inter.LocRingLocal.full GroundTheory.Heights₂.Heights.Inter.LocRingPow.full

theorem SemilocFinite.full : GroundTheory.Heights₂.Heights.Inter.SemilocFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocFinite.proof GroundTheory.Heights₂.Heights.Inter.SemilocIntegral.full GroundTheory.Heights₂.Heights.Inter.LocRingIntClosureFinite.full GroundTheory.Heights₂.Heights.Inter.LocRingDimOne.full

theorem LocRingInj.full : GroundTheory.Heights₂.Heights.Inter.LocRingInj.Statement :=
  GroundTheory.Heights₂.Heights.Inter.LocRingInj.proof

theorem regularityDehomogenization_holds.full : GroundTheory.Heights₂.Heights.Inter.regularityDehomogenization_holds.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.regularityDehomogenization_holds

theorem GenericPointExists.full : GroundTheory.Heights₂.Heights.Inter.GenericPointExists.Statement :=
  GroundTheory.Heights₂.Heights.Inter.GenericPointExists.proof

theorem ThmIUnique.full : GroundTheory.Heights₂.Heights.Inter.ThmIUnique.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ThmIUnique.proof GroundTheory.Heights₂.Heights.Inter.arithVarZero

theorem ArithmeticIntersectionChartFinite.full : GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionChartFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionChartFinite.proof

theorem pullbackBadImage_holds.full : GroundTheory.Heights₂.Heights.Inter.pullbackBadImage_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.pullbackBadImage_holds.proof

theorem regularityLocalCardinality_holds.full : GroundTheory.Heights₂.Heights.Inter.regularityLocalCardinality_holds.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.regularityLocalCardinality_holds

theorem pullbackPushforward_holds.full : GroundTheory.Heights₂.Heights.Inter.pullbackPushforward_holds.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.pullbackPushforward_holds

theorem SemiPosTwist.full : GroundTheory.Heights₂.Heights.Inter.SemiPosTwist.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.SemiPosTwist

theorem RankFracDegree.full : GroundTheory.Heights₂.Heights.Inter.RankFracDegree.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RankFracDegree.proof

theorem regularityPointsSum_holds.full : GroundTheory.Heights₂.Heights.Inter.regularityPointsSum_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.regularityPointsSum_holds.proof

theorem HorizNotMem.full : GroundTheory.Heights₂.Heights.Inter.HorizNotMem.Statement :=
  GroundTheory.Heights₂.Heights.Inter.HorizNotMem.proof

theorem SheetHessPSD.full : GroundTheory.Heights₂.Heights.Inter.SheetHessPSD.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SheetHessPSD.proof

theorem RegCurvBound.full : GroundTheory.Heights₂.Heights.Inter.RegCurvBound.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.Closed.Inter.RegCurvBound

theorem OrbitCompNonvanish.full : GroundTheory.Heights₂.Heights.Inter.OrbitCompNonvanish.Statement :=
  GroundTheory.Heights₂.Heights.Inter.OrbitCompNonvanish.proof

theorem pullbackDensity_holds.full : GroundTheory.Heights₂.Heights.Inter.pullbackDensity_holds.Statement :=
  GroundTheory.Heights₂.Heights.Inter.pullbackDensity_holds.proof

theorem Closed.ReciprocityTheory.ChartRestriction.G.AI.I2.Unique : ReciprocityTheory.ChartRestriction.G.AI.I2.UniqueStatement :=
  GroundTheory.Heights₂.Heights.Inter.ThmIUnique.full

theorem Closed.Targets.GenFibreChartDeg : GroundTheory.Heights₂.Heights.Targets.GenFibreChartDeg.Statement :=
  GroundTheory.Heights₂.Heights.Targets.GenFibreChartDeg.proof GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.full GroundTheory.Heights₂.Heights.Inter.AdjoinIndepRelfinrank.full

theorem Closed.Targets.CoordFibreDeg : GroundTheory.Heights₂.Heights.Targets.CoordFibreDeg.Statement :=
  GroundTheory.Heights₂.Heights.Targets.CoordFibreDeg.proof GroundTheory.Heights₂.Heights.Targets.FibreMultiHomog.proof GroundTheory.Heights₂.Heights.Inter.Closed.Targets.GenFibreChartDeg GroundTheory.Heights₂.Heights.Targets.CoordRatioDeg.proof

theorem ArithmeticIntersectionVertical.of_remaining
    (hProjDeg : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [(k : K) → Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [(k : K') → Fintype (ι' k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement F ι ι') :
    GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionVertical.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionVertical.proof (by intros; exact GroundTheory.Heights₂.Heights.geoNumStatement _) (by intros; exact GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full _ _) (by intros; exact GroundTheory.Heights₂.Heights.Targets.ProjContract.full _ _ _ _ _) hProjDeg GroundTheory.Heights₂.Heights.Inter.VerticalDegree.full

theorem FibreOverFinite.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement) :
    GroundTheory.Heights₂.Heights.Inter.FibreOverFinite.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FibreOverFinite.proof hFibreIncomp

theorem SemilocChartRatio.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement) :
    GroundTheory.Heights₂.Heights.Inter.SemilocChartRatio.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocChartRatio.proof (GroundTheory.Heights₂.Heights.Inter.FibreOverFinite.of_remaining hFibreIncomp)

theorem SemilocRankFrac.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement) :
    GroundTheory.Heights₂.Heights.Inter.SemilocRankFrac.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocRankFrac.proof GroundTheory.Heights₂.Heights.Inter.RankFracDegree.full GroundTheory.Heights₂.Heights.Inter.SemilocFinite.full (GroundTheory.Heights₂.Heights.Inter.SemilocChartRatio.of_remaining hFibreIncomp)

theorem SemilocRankAdjoin.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement) :
    GroundTheory.Heights₂.Heights.Inter.SemilocRankAdjoin.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocRankAdjoin.proof (GroundTheory.Heights₂.Heights.Inter.SemilocRankFrac.of_remaining hFibreIncomp) GroundTheory.Heights₂.Heights.Inter.ChartScalingIndep.full

theorem SemilocRank.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement)
    (hFibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement) :
    GroundTheory.Heights₂.Heights.Inter.SemilocRank.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocRank.proof hFibreDim (GroundTheory.Heights₂.Heights.Inter.SemilocRankAdjoin.of_remaining hFibreIncomp)

theorem FibreDivSupp.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement) :
    GroundTheory.Heights₂.Heights.Inter.FibreDivSupp.Statement :=
  GroundTheory.Heights₂.Heights.Inter.FibreDivSupp.proof hFibreIncomp

theorem SemilocLengthSum.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement)
    (hSemilocMaxIdeals : GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals.Statement)
    (hSemilocResidueDeg : GroundTheory.Heights₂.Heights.Inter.SemilocResidueDeg.Statement) :
    GroundTheory.Heights₂.Heights.Inter.SemilocLengthSum.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocLengthSum.proof GroundTheory.Heights₂.Heights.Inter.SemilocFinite.full hSemilocMaxIdeals hSemilocResidueDeg (GroundTheory.Heights₂.Heights.Inter.FibreDivSupp.of_remaining hFibreIncomp) GroundTheory.Heights₂.Heights.Inter.LocRingDimOne.full (GroundTheory.Heights₂.Heights.Inter.FibreOverFinite.of_remaining hFibreIncomp)

theorem SemilocLength.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement)
    (hSemilocMaxIdeals : GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals.Statement)
    (hSemilocResidueDeg : GroundTheory.Heights₂.Heights.Inter.SemilocResidueDeg.Statement) :
    GroundTheory.Heights₂.Heights.Inter.SemilocLength.Statement :=
  GroundTheory.Heights₂.Heights.Inter.SemilocLength.proof (GroundTheory.Heights₂.Heights.Inter.SemilocLengthSum.of_remaining hFibreIncomp hSemilocMaxIdeals hSemilocResidueDeg) (GroundTheory.Heights₂.Heights.Inter.FibreDivSupp.of_remaining hFibreIncomp) GroundTheory.Heights₂.Heights.Inter.regularityDehomogenization_holds.full

theorem ArithmeticIntersectionDivisorPushforward.of_remaining
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement)
    (hSemilocMaxIdeals : GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals.Statement)
    (hSemilocResidueDeg : GroundTheory.Heights₂.Heights.Inter.SemilocResidueDeg.Statement)
    (hFibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement) :
    GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionDivisorPushforward.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionDivisorPushforward.proof GroundTheory.Heights₂.Heights.Inter.regularityDehomogenization_holds.full GroundTheory.Heights₂.Heights.Inter.LocRingDimOne.full GroundTheory.Heights₂.Heights.Inter.SemilocFinite.full (GroundTheory.Heights₂.Heights.Inter.SemilocRank.of_remaining hFibreIncomp hFibreDim) (GroundTheory.Heights₂.Heights.Inter.SemilocLength.of_remaining hFibreIncomp hSemilocMaxIdeals hSemilocResidueDeg)

theorem ArithmeticIntersectionCycle.of_remaining
    (hProjDeg : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [(k : K) → Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [(k : K') → Fintype (ι' k)], ReciprocityTheory.ChartRestriction.G.AI.I1.ProjDegStatement F ι ι')
    (hFibreIncomp : GroundTheory.Heights₂.Heights.Inter.FibreIncomp.Statement)
    (hSemilocMaxIdeals : GroundTheory.Heights₂.Heights.Inter.SemilocMaxIdeals.Statement)
    (hSemilocResidueDeg : GroundTheory.Heights₂.Heights.Inter.SemilocResidueDeg.Statement)
    (hFibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement) :
    GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionCycle.Statement :=
  GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionCycle.proof GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionHorizontal.full (GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionVertical.of_remaining hProjDeg) (GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionDivisorPushforward.of_remaining hFibreIncomp hSemilocMaxIdeals hSemilocResidueDeg hFibreDim) GroundTheory.Heights₂.Heights.Inter.GenericPointExists.full (by intros; exact GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full _ _)

theorem GenericPointsInAffineChart.of_remaining
    (hAI3ChartNormCount : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement) :
    GroundTheory.Heights₂.Heights.Inter.GenericPointsInAffineChart.Statement :=
  GroundTheory.Heights₂.Heights.Inter.GenericPointsInAffineChart.proof GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionChartFinite.full hAI3ChartNormCount GroundTheory.Heights₂.Heights.Inter.OrbitCompNonvanish.full

theorem GenericPointsAvoidBadLocus.of_remaining
    (hAI3ChartNormCount : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement) :
    GroundTheory.Heights₂.Heights.Inter.GenericPointsAvoidBadLocus.Statement :=
  GroundTheory.Heights₂.Heights.Inter.GenericPointsAvoidBadLocus.proof (GroundTheory.Heights₂.Heights.Inter.GenericPointsInAffineChart.of_remaining hAI3ChartNormCount)

theorem GenericPointsCount.of_remaining
    (hAI3ChartNormCount : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement) :
    GroundTheory.Heights₂.Heights.Inter.GenericPointsCount.Statement :=
  GroundTheory.Heights₂.Heights.Inter.GenericPointsCount.proof (GroundTheory.Heights₂.Heights.Inter.GenericPointsAvoidBadLocus.of_remaining hAI3ChartNormCount)

theorem PullbackDegreeCount.of_remaining
    (hAI3ChartNormCount : GroundTheory.Heights₂.Heights.Inter.ChartNormCount.Statement)
    (hFibreDim : ReciprocityTheory.ChartRestriction.G.AI.I4.FibreDimStatement) :
    GroundTheory.Heights₂.Heights.Inter.PullbackDegreeCount.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PullbackDegreeCount.proof hFibreDim GroundTheory.Heights₂.Heights.Inter.ChartRankAdjoin.full (GroundTheory.Heights₂.Heights.Inter.GenericPointsCount.of_remaining hAI3ChartNormCount) GroundTheory.Heights₂.Heights.Inter.PullbackVanishingOfNullCycle.full GroundTheory.Heights₂.Heights.Inter.pullbackBadImage_holds.full

theorem RegularityMaximalSpectrum.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSpectrum.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSpectrum.proof GroundTheory.Heights₂.Heights.Inter.RegularityOrder.full GroundTheory.Heights₂.Heights.Inter.RegularityLocalize.full GroundTheory.Heights₂.Heights.Inter.LocRingInj.full hR1RegMaxSurj

theorem RegularityLocal.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.RegularityLocal.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityLocal.proof GroundTheory.Heights₂.Heights.Inter.RegularityOrder.full (GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSpectrum.of_remaining hR1RegMaxSurj)

theorem RegularityFormula.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.RegularityFormula.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityFormula.proof GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber.full GroundTheory.Heights₂.Heights.Inter.RegularityOrder.full (GroundTheory.Heights₂.Heights.Inter.RegularityLocal.of_remaining hR1RegMaxSurj)

theorem RegularityLocalProduct.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.RegularityLocalProduct.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityLocalProduct.proof GroundTheory.Heights₂.Heights.Inter.RegularityFunctionFieldNumber.full (GroundTheory.Heights₂.Heights.Inter.RegularityFormula.of_remaining hR1RegMaxSurj) GroundTheory.Heights₂.Heights.Inter.RegularityDenominator.full GroundTheory.Heights₂.Heights.Inter.RegularityDivisorSupportClosed.full GroundTheory.Heights₂.Heights.Inter.RegularityLocalFinite.full

theorem VerticalEmbedding.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.VerticalEmbedding.Statement :=
  GroundTheory.Heights₂.Heights.Inter.VerticalEmbedding.proof GroundTheory.Heights₂.Heights.Inter.regularityDehomogenization_holds.full GroundTheory.Heights₂.Heights.Inter.regularityLocalCardinality_holds.full (GroundTheory.Heights₂.Heights.Inter.RegularityLocalProduct.of_remaining hR1RegMaxSurj)

theorem VerticalClosedPoints.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.VerticalClosedPoints.Statement :=
  GroundTheory.Heights₂.Heights.Inter.VerticalClosedPoints.proof GroundTheory.Heights₂.Heights.Inter.regularityEmbedding_holds.full (GroundTheory.Heights₂.Heights.Inter.VerticalEmbedding.of_remaining hR1RegMaxSurj)

theorem RPositionAdd.of_remaining
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    GroundTheory.Heights₂.Heights.Inter.RPositionAdd.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RPositionAdd.proof ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite hPtsIntegrable

theorem PtsMonoSemiPos.of_remaining
    (hPtsIntegrable : ReciprocityTheory.ChartRestriction.G.Geo.PtsIntegrableStatement) :
    GroundTheory.Heights₂.Heights.Inter.PtsMonoSemiPos.Statement :=
  GroundTheory.Heights₂.Heights.Inter.PtsMonoSemiPos.proof hPtsIntegrable GroundTheory.Heights₂.Heights.Inter.SheetHessPSD.full

theorem RegularityProductFormula.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.RegularityProductFormula.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityProductFormula.proof GroundTheory.Heights₂.Heights.Inter.regularityPointsSum_holds.full (GroundTheory.Heights₂.Heights.Inter.VerticalClosedPoints.of_remaining hR1RegMaxSurj)

theorem RegularityIndependence.of_remaining
    (hR1RegMaxSurj : GroundTheory.Heights₂.Heights.Inter.RegularityMaximalSurjective.Statement) :
    GroundTheory.Heights₂.Heights.Inter.RegularityIndependence.Statement :=
  GroundTheory.Heights₂.Heights.Inter.RegularityIndependence.proof GroundTheory.Heights₂.Heights.Inter.arithVarZero ReciprocityTheory.ChartRestriction.G.Geo.fibreFinite (GroundTheory.Heights₂.Heights.Inter.RegularityProductFormula.of_remaining hR1RegMaxSurj)

end GroundTheory.Heights₂.Heights.Inter
