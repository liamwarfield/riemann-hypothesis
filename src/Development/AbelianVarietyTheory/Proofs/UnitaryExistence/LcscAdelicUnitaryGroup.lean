module

public import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ConjInvariantCharacterMem
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.GlobalBasisAlgebra
public import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPfS
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsObjOfUniformisedTripleComplex
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct RestrictedProduct

namespace GlobalTheory.AdelicUnitaryTop

section Restricted

theorem secondCountable_restrictedProduct {ι : Type} [Countable ι] (R : ι → Type)
    [∀ i, TopologicalSpace (R i)] [∀ i, SecondCountableTopology (R i)] (A : ∀ i, Set (R i))
    (hA : ∀ i, IsOpen (A i)) : SecondCountableTopology (Πʳ i, [R i, A i]) := by
  have hS : ∀ T : Finset ι, cofinite ≤ 𝓟 ((T : Set ι)ᶜ) := fun T =>
    le_principal_iff.2 (T.finite_toSet.compl_mem_cofinite)
  have hsc : ∀ T : Finset ι, SecondCountableTopology (Πʳ i, [R i, A i]_[𝓟 ((T : Set ι)ᶜ)]) :=
    fun T => RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
  have he := fun T : Finset ι => RestrictedProduct.isOpenEmbedding_inclusion_principal hA (hS T)
  haveI : ∀ T : Finset ι, SecondCountableTopology
      (Set.range (RestrictedProduct.inclusion R A (hS T))) := fun T =>
    (he T).isEmbedding.toHomeomorph.symm.secondCountableTopology
  refine TopologicalSpace.secondCountableTopology_of_countable_cover
    (fun T => (he T).isOpen_range) ?_
  refine Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ?_
  have hx : {i | ¬ x i ∈ A i}.Finite := eventually_cofinite.1 x.2
  refine ⟨hx.toFinset, ?_⟩
  refine RestrictedProduct.exists_inclusion_eq_of_eventually R A (hS _) ?_
  intro i hi
  by_contra h
  exact hi (by simpa using h)

end Restricted

section Adeles

variable (F : Type) [Field F] [NumberField F]

theorem properSpace_adicCompletion (v : HeightOneSpectrum (𝓞 F)) :
    ProperSpace (v.adicCompletion F) := by
  refine Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.2
    ⟨inferInstance, ?_, ?_⟩
  · exact inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers F))
  · exact Formalism.UG.P.glint_finite_residueField v

theorem compactSpace_adicCompletionIntegers (v : HeightOneSpectrum (𝓞 F)) :
    CompactSpace (v.adicCompletionIntegers F) :=
  Valued.integer.properSpace_iff_compactSpace_integer.1 (properSpace_adicCompletion F v)

theorem countable_heightOneSpectrum : Countable (HeightOneSpectrum (𝓞 F)) := by
  haveI : Countable (𝓞 F) := by
    haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    exact RingOfIntegers.coe_injective.countable
  haveI : Countable (Ideal (𝓞 F)) := by
    refine Function.Surjective.countable
      (f := fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) ?_
    intro I
    exact (IsNoetherian.noetherian I : I.FG)
  exact Function.Injective.countable (f := fun la : HeightOneSpectrum (𝓞 F) => la.asIdeal)
      fun a b h => HeightOneSpectrum.ext h

theorem locallyCompact_finiteAdele : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := by
  haveI : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  haveI := properSpace_adicCompletion F
  exact RestrictedProduct.locallyCompactSpace_of_addGroup
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (.of_forall fun v => isCompact_iff_compactSpace.2 (compactSpace_adicCompletionIntegers F v))

theorem secondCountable_finiteAdele : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := by
  haveI := properSpace_adicCompletion F
  haveI := countable_heightOneSpectrum F
  exact secondCountable_restrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    fun _ ↦ Valued.isOpen_valuationSubring _

theorem t2Space_finiteAdeleRing_of_numberField : T2Space (FiniteAdeleRing (𝓞 F) F) :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum (𝓞 F),
    [v.adicCompletion F, v.adicCompletionIntegers F]))

theorem secondCountable_infiniteAdele : SecondCountableTopology (InfiniteAdeleRing F) := by
  haveI : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion := fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology (∀ v : InfinitePlace F, v.Completion))

theorem t2Space_infiniteAdeleRing_of_numberField_field : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))

theorem locallyCompact_adele : LocallyCompactSpace (AdeleRing (𝓞 F) F) :=
  haveI := locallyCompact_finiteAdele F
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem secondCountable_adele : SecondCountableTopology (AdeleRing (𝓞 F) F) :=
  haveI := secondCountable_finiteAdele F
  haveI := secondCountable_infiniteAdele F
  inferInstanceAs (SecondCountableTopology (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

theorem t2Space_adeleRing_numberField : T2Space (AdeleRing (𝓞 F) F) :=
  haveI := t2Space_finiteAdeleRing_of_numberField F
  haveI := t2Space_infiniteAdeleRing_of_numberField_field F
  inferInstanceAs (T2Space (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))

end Adeles

section Tensor

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

theorem nonempty_homeomorph :
    Nonempty (R ⊗[F] E ≃ₜ (Fin (Module.finrank F E) → R)) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  let e := (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun
  exact ⟨{ e.toEquiv with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }⟩

theorem continuous_sigR (σ : E →ₐ[F] E) : Continuous (sigR R σ) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  exact IsModuleTopology.continuous_of_linearMap
    (Algebra.TensorProduct.map (AlgHom.id R R) σ).toLinearMap

theorem lcsc_HA [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) :
    LocallyCompactSpace (HA R σ J) ∧ SecondCountableTopology (HA R σ J) ∧ T2Space (HA R σ J) :=
  by apply _root_.UpperTheory.Reformulated.B.Yzd4.lcsc_HA <;> assumption

end Tensor

theorem lcsc_adelicUnitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), LocallyCompactSpace (HA (AF F) σ J) ∧ SecondCountableTopology (HA (AF F) σ J) ∧ T2Space (HA (AF F) σ J) := by
  intro F E _ _ _ _ _ σ M J
  haveI := locallyCompact_adele F
  haveI := secondCountable_adele F
  haveI := t2Space_adeleRing_numberField F
  exact lcsc_HA (AF F) σ M J

end GlobalTheory.AdelicUnitaryTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroupStatement
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lcsc_adelic_unitary_group : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), LocallyCompactSpace (HA (AF F) σ J) ∧ SecondCountableTopology (HA (AF F) σ J) ∧ T2Space (HA (AF F) σ J) := by
  first | exact @GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary | exact GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary | (intros; apply GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec
noncomputable section

namespace GlobalTheory.TangentLinear

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameTangent

attribute [local instance] Over.cartesianMonoidalCategory

section Comb

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) {G : Over X0} [GrpObj G] [IsCommMonObj G]

theorem smT_prod {κ : Type} (s : Finset κ) (a : S) (u : κ → (overAt x0 (DualNumber S) ⟶ G)) :
    smT x0 a (∏ i ∈ s, u i) = ∏ i ∈ s, smT x0 a (u i) := map_prod (smHom x0 a) u s

theorem smT_sum {κ : Type} (s : Finset κ) (c : κ → S) (v : overAt x0 (DualNumber S) ⟶ G) (h0 : smT x0 0 v = 1) :
    smT x0 (∑ i ∈ s, c i) v = ∏ i ∈ s, smT x0 (c i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, smT_add x0 v h0, ih]

theorem combT_combT {m m' : ℕ} (v : Fin m → (overAt x0 (DualNumber S) ⟶ G)) (hv : ∀ j, smT x0 0 (v j) = 1)
    (A : Matrix (Fin m) (Fin m') S) (N : Fin m' → S) :
    combT x0 (fun i => combT x0 v (fun j => A j i)) N = combT x0 v (A.mulVec N) := by
  simp only [combT, smT_prod, smT_smT]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← smT_sum x0 _ _ _ (hv j)]
  congr 1
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun i _ => _root_.mul_comm _ _

end Comb

section Group

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
variable {S : Type} [CommRing S] {x0 : Sp S ⟶ X0}

theorem isCombAtG_mulVec {m m' : ℕ} (v : Fin m → (Sp (DualNumber S) ⟶ t.G.left)) (hv : ∀ j, IsTanAtG t x0 (v j))
    (w : Fin m' → (Sp (DualNumber S) ⟶ t.G.left)) (A : Matrix (Fin m) (Fin m') S) (N : Fin m' → S)
    (w' : Sp (DualNumber S) ⟶ t.G.left) (h1 : ∀ i, IsCombAtG t x0 v (fun j => A j i) (w i))
    (h2 : IsCombAtG t x0 w N w') : IsCombAtG t x0 v (A.mulVec N) w' := by
  have hw : w = fun i => (combT x0 (fun j => ovT (hv j)) (fun j => A j i)).left :=
    funext fun i => ((isCombAtG_iff t x0 (fun j => ovT (hv j)) _ _).1 (h1 i)).symm
  subst hw
  rw [isCombAtG_iff, combT_combT x0 _ (fun j => smT_zero_ovT (hv j))] at h2
  exact (isCombAtG_iff t x0 (fun j => ovT (hv j)) _ _).2 h2

end Group

theorem isCombAt_mulVec (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) {m : ℕ}
    (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (hv : ∀ j, IsTanAt x (v j)) {m' : ℕ}
    (w : Fin m' → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (A : Matrix (Fin m) (Fin m') S) (N : Fin m' → S)
    (w' : (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (hw : ∀ i, IsCombAt x v (fun j => A j i) (w i))
    (hw' : IsCombAt x w N w') : IsCombAt x v (A.mulVec N) w' :=
  isCombAtG_mulVec (t := Xo.univ.t) (x0 := x) v hv w A N w' hw hw'

end GlobalTheory.TangentLinear
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecValuesComplexFibreAbelianScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecValuesComplexFibreAbelianScheme
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open Formalism.L2.PjFree hiding gxSnd
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory

theorem sec_values_complex_fibre : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (y : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx y)), (∀ (a : ℂ) i (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U i) (scal y a i * s.f i) = a * valAt' pt ((PPx y).U i) (s.f i)) ∧ (SecGen y s ↔ ∃ (i : (PPx y).ι) (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ ∧ valAt' pt ((PPx y).U i) (s.f i) ≠ 0) ∧ ∀ s' : LB.Sec (PPx y), (∀ i (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U i) (s'.f i) = valAt' pt ((PPx y).U i) (s.f i)) → ∀ i, s'.f i = s.f i := by
  intro hT E _ _ _ H Dw l Xo y s
  have hsm : Smooth (gxSnd y) := by
    have := Xo.univ.t.semi.smooth
    exact inferInstanceAs (Smooth (pullback.fst y Xo.univ.t.G.hom))
  have hred : IsReduced (Gx y) :=
    (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field ℂ _ (gxSnd y) hsm).1
  have h1 : ∀ (a : ℂ) i (f : Γ(Gx y, (PPx y).U i)) (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ →
      valAt' pt ((PPx y).U i) (scal y a i * f) = a * valAt' pt ((PPx y).U i) f := fun a i f pt hp => by
    by_cases h : ⊤ ≤ pt ⁻¹ᵁ (PPx y).U i
    · rw [valAt'_mul]
      exact congrArg (· * _) (valAt'_constFn pt (gxSnd y) hp _ a h)
    · rw [valAt'_of_not_le pt h, valAt'_of_not_le pt h, mul_zero]
  have h3 : ∀ i (f g : Γ(Gx y, (PPx y).U i)), (∀ pt : Sp ℂ ⟶ Gx y, pt ≫ gxSnd y = 𝟙 _ →
      valAt' pt ((PPx y).U i) f = valAt' pt ((PPx y).U i) g) → f = g := fun i f g h =>
    ComplexPoints.eq_of_valAt'_eq (gxSnd y) _ f g fun pt hp _ => h pt hp
  refine ⟨fun a i pt hp => h1 a i _ pt hp, ⟨fun hs => ?_, ?_⟩, fun s' h i => h3 i _ _ (h i)⟩
  · by_contra hne
    have h0 : ∀ i (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U i) (s.f i) = 0 := fun i pt hp => by
      by_contra h
      exact hne ⟨i, pt, hp, h⟩
    have hall : ∀ (a : ℂ) i, s.f i = scal y a i * s.f i := fun a i => h3 i _ _ fun pt hp => by
      rw [h1 a i _ pt hp, h0 i pt hp, mul_zero]
    exact zero_ne_one ((hs s).unique (hall 0) (hall 1))
  · rintro ⟨j, q, hq, hv⟩ s'
    obtain ⟨s₀, hs₀⟩ := gfp_gen hT y
    obtain ⟨c, hc, -⟩ := hs₀ s
    have hc0 : c ≠ 0 := fun h => hv (by rw [hc j, h1 c j _ q hq, h, zero_mul])
    obtain ⟨b, hb, hu⟩ := hs₀ s'
    refine ⟨b / c, fun i => h3 i _ _ fun pt hp => ?_, fun a ha => ?_⟩
    · rw [h1 _ i _ pt hp, hb i, hc i, h1 _ i _ pt hp, h1 _ i _ pt hp, ← mul_assoc, div_mul_cancel₀ _ hc0]
    · rw [eq_div_iff hc0]
      refine hu _ fun i => h3 i _ _ fun pt hp => ?_
      rw [h1 _ i _ pt hp, ha i, hc i, h1 _ i _ pt hp, h1 _ i _ pt hp, mul_assoc]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecValuesComplexFibreAbelianSchemeStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open Formalism.L2.PjFree hiding gxSnd
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sec_values_complex_fibre_abelianScheme : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (y : Sp ℂ ⟶ Xo.X) (s : LB.Sec (PPx y)), (∀ (a : ℂ) i (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U i) (scal y a i * s.f i) = a * valAt' pt ((PPx y).U i) (s.f i)) ∧ (SecGen y s ↔ ∃ (i : (PPx y).ι) (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ ∧ valAt' pt ((PPx y).U i) (s.f i) ≠ 0) ∧ ∀ s' : LB.Sec (PPx y), (∀ i (pt : Sp ℂ ⟶ Gx y), pt ≫ gxSnd y = 𝟙 _ → valAt' pt ((PPx y).U i) (s'.f i) = valAt' pt ((PPx y).U i) (s.f i)) → ∀ i, s'.f i = s.f i := by
  first | exact @GlobalTheory.sec_values_complex_fibre | exact GlobalTheory.sec_values_complex_fibre | (intros; apply GlobalTheory.sec_values_complex_fibre <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLocalGeneratorStableBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLocalSectionNonzeroAllFibresModuli
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLocalSectionNonzeroAllFibresModuli
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.PushLoc

open LBGerm PushInv ReciprocityTheory.ChartRestriction.G.Out

theorem exists_sec_lpow {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left) (T : Over S) {V : S.Opens}
    (hV : ∀ y, T.hom y ∈ V) {θ : ∀ i, Γ(A.left, A.hom ⁻¹ᵁ V ⊓ L.U i)} (hθ : θ ∈ secOn L (A.hom ⁻¹ᵁ V))
    (hne : ∀ y ∈ V, ∃ (g : A.left) (i : L.ι), A.hom g = y ∧ g ∈ A.left.basicOpen (θ i)) :
    ∃ s : LB.Sec (LPow A L (1 : ℕ) T), ∀ p : T.left, ∃ (q : (T ⊗ A).left) (i : (LPow A L (1 : ℕ) T).ι),
      (fst T A).left q = p ∧ q ∈ (T ⊗ A).left.basicOpen (s.f i) := by
  have hz : ∀ z, A.hom ((snd T A).left z) ∈ V := fun z => by
    rw [← Scheme.Hom.comp_apply, w_snd, Scheme.Hom.comp_apply]; exact hV _
  have le : ∀ j : Fin 1 → L.ι, (LPow A L (1 : ℕ) T).U j ≤ (snd T A).left ⁻¹ᵁ (A.hom ⁻¹ᵁ V ⊓ L.U (j 0)) :=
    fun j z h => ⟨hz z, (mem_chart A L T _ z j).1 h⟩
  have v : ∀ (j : Fin 1 → L.ι) z, z ∈ (LPow A L (1 : ℕ) T).U j →
      gs (𝟙 _) z _ (((snd T A).left.appLE _ _ (le j)).hom (θ (j 0))) =
        ((snd T A).left.stalkMap z).hom (gs (𝟙 _) _ _ (θ (j 0))) := fun j z h => by
    rw [gs_appLE _ _ _ (le j) (𝟙 _) z h, Category.id_comp]
    exact gs_stalkMap _ z (A.hom ⁻¹ᵁ V ⊓ L.U (j 0)) (le j h) _
  refine ⟨secOfGerm (fun j => ((snd T A).left.appLE _ _ (le j)).hom (θ (j 0)))
    fun z i j hi hj => by
      rw [v i z hi, v j z hj, gm_lpow A L T (𝟙 _) z i j hi hj, Category.id_comp,
        gs_secOn hθ _ (i 0) (j 0) (hz z) (le i hi).2 (le j hj).2, map_mul,
        ← gm_comp _ (𝟙 _) z (L.U (i 0) ⊓ L.U (j 0)) ⟨(le i hi).2, (le j hj).2⟩, Category.comp_id], fun p => ?_⟩
  obtain ⟨g, i, hg, hi⟩ := hne (T.hom p) (hV p)
  obtain ⟨q, h₁, h₂⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback T.hom A.hom) p g hg.symm
  obtain rfl : (snd T A).left q = g := h₂
  refine ⟨q, fun _ => i, h₁, ?_⟩
  show q ∈ (T ⊗ A).left.basicOpen (((snd T A).left.appLE _ _ (le fun _ => i)).hom (θ i))
  rw [Scheme.basicOpen_appLE]
  exact ⟨(mem_chart A L T _ q _).2 (A.left.basicOpen_le _ hi).2, hi⟩

theorem exists_secNZ : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (z : Xo.X), ∃ (R : Type) (_ : CommRing R) (_ : IsNoetherianRing R) (j : Sp R ⟶ Xo.X) (θ : LB.Sec (PPx j)), IsOpenImmersion j ∧ z ∈ Set.range j ∧ SecNZ j θ := by
  intro hS E _ _ _ H D l Xo z
  have := Xo.smooth
  have hsm : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have : IsLocallyNoetherian Xo.X := LocallyOfFiniteType.isLocallyNoetherian Xo.s
  obtain ⟨V, hV, θ, hθ, -, hne⟩ := pushInvertible hS Xo.X (Obj.toPolAV Xo.univ) z
  obtain ⟨B, j, hj, hp, hsub⟩ := Scheme.exists_affine_mem_range_and_range_subset (X := Xo.X) (x := z) (U := V) hV
  have hN : IsLocallyNoetherian (Spec B) := isLocallyNoetherian_of_isOpenImmersion j
  obtain ⟨s, hs⟩ := exists_sec_lpow Xo.univ.t.G Xo.univ.t.PP.L (Over.mk j) (V := V) (fun y => hsub ⟨y, rfl⟩) hθ hne
  exact ⟨B, inferInstance, (isLocallyNoetherian_Spec (R := B)).1 hN, j, s, hj, hp, hs⟩

end GlobalTheory.PushLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLocalSectionNonzeroAllFibresModuliStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_section_nonzero_all_fibres_moduli : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (z : Xo.X), ∃ (R : Type) (_ : CommRing R) (_ : IsNoetherianRing R) (j : Sp R ⟶ Xo.X) (θ : LB.Sec (PPx j)), IsOpenImmersion j ∧ z ∈ Set.range j ∧ SecNZ j θ := by
  first | exact @GlobalTheory.PushLoc.exists_secNZ | exact GlobalTheory.PushLoc.exists_secNZ | (intros; apply GlobalTheory.PushLoc.exists_secNZ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLocalGeneratorStableBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem exists_away_lift {X : Scheme.{0}} {S R : Type} [CommRing S] [CommRing R]
    (x : Spec (CommRingCat.of S) ⟶ X) (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
    (p : Spec (CommRingCat.of S)) (hp : x p ∈ Set.range j) :
    ∃ g : S, g ∉ p.asIdeal ∧ ∃ φ : R →+* Localization.Away g,
      Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))) ≫ x =
        Spec.map (CommRingCat.ofHom φ) ≫ j := by
  have hopen : IsOpen ((fun q : PrimeSpectrum S => x q) ⁻¹' Set.range j) :=
    j.isOpenEmbedding.isOpen_range.preimage x.continuous
  obtain ⟨_, ⟨g, rfl⟩, hg, hsub⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open (a := p) hp hopen
  refine ⟨g, hg, ?_⟩
  have hr : Set.range (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away g))) ≫ x) ⊆
      Set.range j := by
    rintro _ ⟨q, rfl⟩
    rw [Scheme.Hom.comp_apply]
    apply hsub
    have : PrimeSpectrum.comap (algebraMap S (Localization.Away g)) q ∈
        Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := ⟨q, rfl⟩
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g] at this
    exact this
  refine ⟨(Spec.preimage (IsOpenImmersion.lift j _ hr)).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

theorem exists_local_generator : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (p : Sp S), ∃ g : S, g ∉ p.asIdeal ∧ ∃ θ : LB.Sec (PPx (spMap (algebraMap S (Localization.Away g)) ≫ x)), ∀ (T : Type) [CommRing T] (ψ : Localization.Away g →+* T) (x' : Sp T ⟶ Xo.X) (θ' : LB.Sec (PPx x')), x' = spMap ψ ≫ spMap (algebraMap S (Localization.Away g)) ≫ x → SecBC ψ 1 _ x' θ θ' → SecGen x' θ' ∧ SecNZ x' θ' := by
  intro hB E _ _ _ H Dw l Xo S _ x p
  obtain ⟨R, _, _, j, θ₀, hj, hz, hnz⟩ := GlobalTheory.T.exists_local_section_nonzero_all_fibres_moduli hB E H Dw l Xo (x p)
  obtain ⟨g, hg, φ, hφ⟩ := exists_away_lift x j p hz
  have hφ' : spMap (algebraMap S (Localization.Away g)) ≫ x = spMap φ ≫ j := hφ
  obtain ⟨θ, hθ, -⟩ := GlobalTheory.T.existsUnique_scaledBaseChange_fibreSection E H Dw l Xo R (Localization.Away g) φ 1 j _ hφ' θ₀
  refine ⟨g, hg, θ, ?_⟩
  intro T _ ψ x' θ' hx' hbc
  have h1 : SecBC (ψ.comp φ) 1 j x' θ₀ θ' :=
    ((GlobalTheory.T.scaledBaseChange_fibreSection_calculus E H Dw l Xo R (Localization.Away g) T φ ψ j _ x' hφ' hx').1 1 θ₀ θ θ' hθ).1 hbc
  have hx'' : x' = spMap (ψ.comp φ) ≫ j := by
    rw [hx', hφ', ← Category.assoc]
    congr 1
    exact (Spec.map_comp (CommRingCat.ofHom φ) (CommRingCat.ofHom ψ)).symm
  exact ⟨GlobalTheory.T.fibreSectionGenerates_of_nowhereZero_noetherian_baseChange hB E H Dw l Xo R j θ₀ hnz T (ψ.comp φ) x' θ' hx'' h1,
    fun p' => (GlobalTheory.T.scaledBaseChange_fibreSection_nonvanishing_iff E H Dw l Xo R T (ψ.comp φ) j x' hx'' θ₀ θ' h1 p').2 (hnz _)⟩

end GlobalTheory.Frames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLocalGeneratorStableBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_generator_stable_baseChange : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (p : Sp S), ∃ g : S, g ∉ p.asIdeal ∧ ∃ θ : LB.Sec (PPx (spMap (algebraMap S (Localization.Away g)) ≫ x)), ∀ (T : Type) [CommRing T] (ψ : Localization.Away g →+* T) (x' : Sp T ⟶ Xo.X) (θ' : LB.Sec (PPx x')), x' = spMap ψ ≫ spMap (algebraMap S (Localization.Away g)) ≫ x → SecBC ψ 1 _ x' θ θ' → SecGen x' θ' ∧ SecNZ x' θ' := by
  first | exact @GlobalTheory.Frames.exists_local_generator | exact GlobalTheory.Frames.exists_local_generator | (intros; apply GlobalTheory.Frames.exists_local_generator <;> assumption)
end
end
