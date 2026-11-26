module

public import Development.AbelianVarietyTheory.Definitions.Divisors.BaseRankDimension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfIsSmoothModerate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegIdxOfIsStd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupportedAtInfinityAdeleEqZeroOfComplexComponent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantDoubledFormConjProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantHeisenbergLatticeVacuumFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPairDecomposition

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFunctionFieldOfOneVariableOfGenericPointOfCurv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgFunctionField
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

namespace GlobalTheory.FGFun

theorem fg_functionField : ∀ (F : Type) [Field F] (G : Scheme.{0}) [IsIntegral G] (sG : G ⟶ Sp F), IsProjOver sG → ∀ (P Ω : Type) [Field P] [Field Ω] (φ : P →+* G.functionField) (t : Sp P ⟶ Sp F) (ι : G.functionField →+* Ω), spMap ι ≫ G.fromSpecStalk (genericPoint G) ≫ sG = spMap ι ≫ spMap φ ≫ t → (letI := φ.toAlgebra; (⊤ : IntermediateField P G.functionField).FG) := by
  intro F _ G _ sG hproj P Ω _ _ φ t ι h
  letI := φ.toAlgebra
  obtain ⟨τ, rfl⟩ := Spec.map_surjective t
  obtain ⟨β, hβ⟩ := Spec.map_surjective (G.fromSpecStalk (genericPoint G) ≫ sG)
  have hβτ : ∀ c : F, β.hom c = φ (τ.hom c) := by
    rw [← hβ] at h
    simp only [← Spec.map_comp] at h
    have h' := Spec.map_injective h
    intro c
    apply ι.injective
    have := congrArg (fun f => f.hom c) h'
    simpa using this
  have hft : LocallyOfFiniteType sG := by
    obtain ⟨N, i, hi, rfl⟩ := hproj
    haveI := isProper_str F N
    infer_instance
  obtain ⟨U, hU, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 G.isBasis_affineOpens
    (TopologicalSpace.Opens.mem_top (genericPoint G))
  haveI : Nonempty U := ⟨⟨_, hx⟩⟩
  have e : U ≤ sG ⁻¹ᵁ ⊤ := by simp
  have hfin := HasRingHomProperty.appLE (P := @LocallyOfFiniteType) sG hft ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ e
  have key : sG.appLE ⊤ U e ≫ G.presheaf.germ U _ hx = (Scheme.ΓSpecIso (.of F)).hom ≫ β := by
    rw [← Scheme.ΓSpecIso_naturality, hβ, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop,
      Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
    have h3 : (Spec (G.presheaf.stalk (genericPoint G))).presheaf.map
        (homOfLE (le_top : (⊤ : (Spec (G.presheaf.stalk (genericPoint G))).Opens) ≤ ⊤)).op = 𝟙 _ := by
      rw [Subsingleton.elim (homOfLE _) (𝟙 _)]; exact CategoryTheory.Functor.map_id _ _
    rw [h3]
    simp
  classical
  letI : Algebra Γ(Sp F, ⊤) Γ(G, U) := (sG.appLE ⊤ U e).hom.toAlgebra
  have hfin' : Algebra.FiniteType Γ(Sp F, ⊤) Γ(G, U) := hfin
  obtain ⟨s, hs⟩ := hfin'.out
  have hmem : ∀ a : Γ(G, U), (G.presheaf.germ U _ hx).hom a ∈
      IntermediateField.adjoin P ((s.image (G.presheaf.germ U _ hx).hom : Finset _) : Set G.functionField) := by
    intro a
    have ha : a ∈ Algebra.adjoin Γ(Sp F, ⊤) (s : Set Γ(G, U)) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx' =>
      exact IntermediateField.subset_adjoin _ _ (by rw [Finset.coe_image]; exact ⟨x, hx', rfl⟩)
    | algebraMap r =>
      have := congrArg (fun f => f.hom r) key
      simp only [CommRingCat.hom_comp, RingHom.comp_apply] at this
      rw [RingHom.algebraMap_toAlgebra, this, hβτ]
      exact IntermediateField.algebraMap_mem _ _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨s.image (G.presheaf.germ U _ hx).hom, eq_top_iff.2 fun f _ => ?_⟩
  have := functionField_isFractionRing_of_isAffineOpen G U hU
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := Γ(G, U)) f
  exact div_mem (hmem a) (hmem b)

end GlobalTheory.FGFun
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFunctionFieldOfOneVariableOfGenericPointOfCurv
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc IntermediateField

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Nef.CurveFF

theorem isFF_of_trdeg_eq_one {k F : Type} [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F]
    (h : Algebra.trdeg k F = 1) : IsFF k F := by
  have hna : ¬ Algebra.IsAlgebraic k F := fun ha => by
    rw [trdeg_eq_zero_iff.mpr ha] at h; exact zero_ne_one h
  obtain ⟨x, hx⟩ : ∃ x : F, Transcendental k x := by
    by_contra hc
    push_neg at hc
    exact hna ⟨fun x => by simpa [Transcendental] using hc x⟩
  exact ⟨x, hx, finiteDimensional_adjoin_of_trdeg_le_one h.le x hx⟩

theorem isFF_of_stalk (k K : Type) [Field k] [Field K] [Algebra k K] (C : Scheme.{0}) [IsIntegral C]
    [Algebra k Γ(C, ⊤)] (hp : IsProjOver (strHom k (X := C))) (hd : topologicalKrullDim C = 1)
    (y : C) (hy : y = genericPoint C) (ψ : C.presheaf.stalk y ⟶ CommRingCat.of K)
    (hψ : Function.Surjective ψ.hom)
    (hc : Spec.map ψ ≫ C.fromSpecStalk y ≫ strHom k C = spMap (algebraMap k K)) : IsFF k K := by
  subst hy
  let φ : k →+* C.functionField := (Spec.preimage (C.fromSpecStalk (genericPoint C) ≫ strHom k C)).hom
  have hφ : C.fromSpecStalk (genericPoint C) ≫ strHom k C = spMap φ := (Spec.map_preimage _).symm
  letI : Algebra k C.functionField := φ.toAlgebra
  have htr : Algebra.trdeg k C.functionField = 1 := by
    have := FunctionFieldTrdeg.trdeg_functionField_eq k C (strHom k C) 1 hp (by simpa using hd) φ hφ
    simpa using this
  have hfg : (⊤ : IntermediateField k C.functionField).FG :=
    FGFun.fg_functionField k C (strHom k C) hp k C.functionField φ (𝟙 _) (RingHom.id _) (by simp [hφ])
  haveI : Algebra.EssFiniteType k C.functionField := IntermediateField.fg_top_iff.mp hfg
  let ψ' : C.functionField →+* K := ψ.hom
  have hinj : Function.Injective ψ' := ψ'.injective
  have hcomm : ∀ c : k, ψ' (φ c) = algebraMap k K c := by
    rw [hφ] at hc
    have h1 : Spec.map (CommRingCat.ofHom φ ≫ ψ) = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
      rw [Spec.map_comp]; exact hc
    have h2 := Spec.map_injective h1
    intro c
    exact congrArg (fun f => f.hom c) h2
  let e : C.functionField ≃ₐ[k] K :=
    AlgEquiv.ofBijective { ψ' with commutes' := hcomm } ⟨hinj, hψ⟩
  haveI : Algebra.EssFiniteType k K := (Algebra.EssFiniteType.iff_of_algEquiv e).mp inferInstance
  exact isFF_of_trdeg_eq_one (e.trdeg_eq ▸ htr)

theorem isFF_of_isGenOver : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  IsFF k K := by
  intro k K _ _ _ _ _ C _ x hx
  obtain ⟨⟨hs, hp, hg⟩, ⟨hdom, hpre⟩, hxs⟩ := hx
  haveI : IsIntegral C := LieSemineg.isIntegral_curve hs hg
  let p : Sp K := IsLocalRing.closedPoint (CommRingCat.of K)
  haveI : Nonempty C := ⟨x p⟩
  have hd : topologicalKrullDim C = 1 := LieSemineg.dim_curve hs
  have hgen : x p = genericPoint C := by
    have hr : Set.range x = {x p} := by
      ext w
      constructor
      · rintro ⟨v, rfl⟩
        rw [Set.mem_singleton_iff, Subsingleton.elim v p]
      · rintro rfl
        exact ⟨p, rfl⟩
    refine ((genericPoint_spec C).eq ?_).symm
    rw [isGenericPoint_def, ← hr]
    exact x.denseRange.closure_range
  have hsurj : Function.Surjective (Scheme.stalkClosedPointTo x).hom := by
    unfold Scheme.stalkClosedPointTo
    exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (.of K)).hom).2.comp
      (x.stalkMap_surjective _)
  refine isFF_of_stalk k K C hp hd _ hgen (Scheme.stalkClosedPointTo x) hsurj ?_
  rw [← Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hxs]

end GlobalTheory.Nef.CurveFF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFunctionFieldOfOneVariableOfGenericPointOfCurvStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFunctionFieldOfOneVariable_of_genericPointOfCurve : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  IsFF k K := by
  first | exact @GlobalTheory.Nef.CurveFF.isFF_of_isGenOver | exact GlobalTheory.Nef.CurveFF.isFF_of_isGenOver | (intros; apply GlobalTheory.Nef.CurveFF.isFF_of_isGenOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompInfRTensorInlA
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSum
namespace GlobalTheory.ColumnSumLemma
open Matrix
theorem colSum {A : Type} [CommRing A] {n r : ℕ} (C : Matrix (Fin n) (Fin r) A) (a : Fin r → A) :
    Matrix.mulVec C a = ∑ i, a i • Matrix.transpose C i := by
  ext j
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

theorem main : ∀ {A : Type} [inst : CommRing A] {n r : ℕ} (C : Matrix (Fin n) (Fin r) A) (I : Set (Fin r)) (y : Fin n → A), y ∈ Submodule.span A ((fun (i : Fin r) ↦ Matrix.transpose C i) '' I) ↔ ∃ (a : Fin r → A), (∀ l ∉ I, a l = (0 : A)) ∧ Matrix.mulVec C a = y := by
  intro A _ n r C I y
  rw [Finsupp.mem_span_image_iff_linearCombination]
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨l, fun k hk => ?_, ?_⟩
    · exact Finsupp.notMem_support_iff.mp (fun h => hk (hl h))
    · rw [colSum, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      intro i; simp
  · rintro ⟨a, ha, rfl⟩
    refine ⟨Finsupp.equivFunOnFinite.symm a, fun k hk => ?_, ?_⟩
    · by_contra h
      exact (Finsupp.mem_support_iff.mp hk) (ha k h)
    · rw [colSum, Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      · rfl
      · intro i; simp
end GlobalTheory.ColumnSumLemma
end

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open scoped TensorProduct

noncomputable section
open Matrix
namespace GlobalTheory.StdPar.UnipArch

section Lin

variable {A : Type} [CommRing A] {n r : ℕ}

theorem mem_span_cols_iff (C : Matrix (Fin n) (Fin r) A) (I : Set (Fin r)) (y : Fin n → A) :
    y ∈ Submodule.span A ((fun i => Cᵀ i) '' I) ↔ ∃ a : Fin r → A, (∀ l, l ∉ I → a l = 0) ∧ C *ᵥ a = y := by
  first
  | exact @_root_.GlobalTheory.ColumnSumLemma.main
  | exact _root_.GlobalTheory.ColumnSumLemma.main
  | (apply _root_.GlobalTheory.ColumnSumLemma.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ColumnSumLemma.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ColumnSumLemma.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ColumnSumLemma.main ..)

variable (P : Fin r → Fin r → Prop) (hPt : ∀ i l j, P i l → P l j → P i j) (hPlt : ∀ i l, P i l → i < l)
include hPt



end Lin

section Glue

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

open GlobalTheory.AutFunCompare (evW sgW)


variable (F) in
def inlA : Ainf F →ₗ[F] AF F := LinearMap.inl F (Ainf F) (Af F)


variable (F) in
def inrA : Af F →ₗ[F] AF F := LinearMap.inr F (Ainf F) (Af F)


variable (F E) in
def glueInf (c : ∀ w : InfinitePlace F, w.Completion ⊗[F] E) : AF F ⊗[F] E :=
  (inlA F).rTensor E (∑ w, (sgW w).rTensor E (c w))

theorem map_evW_sum_sgW (c : ∀ w : InfinitePlace F, w.Completion ⊗[F] E) (w : InfinitePlace F) :
    Algebra.TensorProduct.map (evW w) (AlgHom.id F E) (∑ w', (sgW w').rTensor E (c w')) = c w := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single w]
  · induction c w using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      show (evW w (sgW w a)) ⊗ₜ[F] x = a ⊗ₜ[F] x
      congr 1
      exact Pi.single_eq_same w a
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  · intro w' _ hw'
    induction c w' using TensorProduct.induction_on with
    | zero => simp
    | tmul a x =>
      show (evW w (sgW w' a)) ⊗ₜ[F] x = 0
      rw [show evW w (sgW w' a) = 0 from Pi.single_eq_of_ne (Ne.symm hw') a, TensorProduct.zero_tmul]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]
  · simp

theorem compInf_rTensor_inlA (z : Ainf F ⊗[F] E) (w : InfinitePlace F) :
    compInf F E w ((inlA F).rTensor E z) = Algebra.TensorProduct.map (evW w) (AlgHom.id F E) z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a x => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

theorem compInf_glueInf (c : ∀ w : InfinitePlace F, w.Completion ⊗[F] E) (w : InfinitePlace F) :
    compInf F E w (glueInf F E c) = c w := by
  rw [glueInf, compInf_rTensor_inlA, map_evW_sum_sgW]

theorem sndA_rTensor_inlA (z : Ainf F ⊗[F] E) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) ((inlA F).rTensor E z) = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a x =>
    show (sndA F (inlA F a)) ⊗ₜ[F] x = 0
    rw [show sndA F (inlA F a) = 0 from rfl, TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, add_zero]

theorem sndA_glueInf (c : ∀ w : InfinitePlace F, w.Completion ⊗[F] E) :
    Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (glueInf F E c) = 0 :=
  sndA_rTensor_inlA _

@[simp] theorem glueInf_zero : glueInf F E (fun _ => 0) = 0 := by
  simp only [glueInf, map_zero, Finset.sum_const_zero]

theorem tens_ext {z z' : AF F ⊗[F] E} (h1 : ∀ w, compInf F E w z = compInf F E w z')
    (h2 : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z = Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z') :
    z = z' := by
  have hz : ∀ z : AF F ⊗[F] E, z = (inlA F).rTensor E (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) +
      (inrA F).rTensor E (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero, map_zero, add_zero]
    | tmul x y =>
      show x ⊗ₜ[F] y = (inlA F (fstA F x)) ⊗ₜ[F] y + (inrA F (sndA F x)) ⊗ₜ[F] y
      rw [← TensorProduct.add_tmul]
      congr 1
      exact Prod.ext (add_zero _).symm (zero_add _).symm
    | add x y hx hy =>
      simp only [map_add (f := _)]
      rw [add_add_add_comm, ← hx, ← hy]
  have hc : ∀ (w : InfinitePlace F) (z : AF F ⊗[F] E), compInf F E w z =
      Algebra.TensorProduct.map (evW w) (AlgHom.id F E) (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) := by
    intro w z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul x y => rfl
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]
  rw [hz z, hz z', h2, GlobalTheory.AutFunCompare.infTens_ext (fun w => (hc w z).symm.trans ((h1 w).trans (hc w z')))]

end Glue

section Main

end Main

end GlobalTheory.StdPar.UnipArch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicAddCharEqArchimedeanMulFinprodLocal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicAddCharEqArchimedeanMulFinprodLocal
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.PsiProd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

variable {F : Type} [Field F] [NumberField F]

def intFin (y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) : Af F :=
  RestrictedProduct.structureMap (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite
    (fun v => ⟨(y v).1, (y v).2⟩)

theorem continuous_intFin : Continuous (intFin (F := F)) :=
  RestrictedProduct.isEmbedding_structureMap.continuous

theorem evalV_intFin (y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F))
    (w : HeightOneSpectrum (𝓞 F)) : evalV F w (intFin y) = (y w : Fv F w) := rfl

theorem intFin_nsmul (n : ℕ) (y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) :
    intFin (n • y) = n • intFin y := by
  refine GlobalTheory.AdelicU.af_ext fun w => ?_
  rw [map_nsmul, evalV_intFin, evalV_intFin]
  rfl

theorem exists_finset_trivial (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) :
    ∃ I : Finset (HeightOneSpectrum (𝓞 F)), ∀ y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F),
      (∀ v ∈ I, y v = 0) → ψ (LinearMap.inr F (Ainf F) (Af F) (intFin y)) = 1 := by
  let ι : (∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) → AF F := fun y =>
    LinearMap.inr F (Ainf F) (Af F) (intFin y)
  have hι : Continuous ι := continuous_const.prodMk continuous_intFin
  have hopen : IsOpen {y | ‖ψ (ι y) - 1‖ < 1 / 2} :=
    isOpen_lt ((hψ.comp hι).sub continuous_const).norm continuous_const
  have h0 : (0 : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) ∈ {y | ‖ψ (ι y) - 1‖ < 1 / 2} := by
    have : ι 0 = 0 := by
      have h : intFin (0 : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F)) = 0 := by
        simpa using intFin_nsmul (F := F) 0 0
      show LinearMap.inr F (Ainf F) (Af F) (intFin 0) = (0 : AF F)
      rw [h, map_zero]
    simp [this, AddChar.map_zero_eq_one]
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hopen 0 h0
  refine ⟨I, fun y hy => GlobalTheory.eq_one_of_forall_norm_pow_sub_one_lt _ fun n => ?_⟩
  have hmem : n • y ∈ (I : Set _).pi u := by
    intro a ha
    have : (n • y) a = 0 := by rw [Pi.smul_apply, hy a ha, smul_zero]
    rw [this]; exact (hu a ha).2
  have e : (ι (n • y) : AF F) = n • (ι y : AF F) := by
    show LinearMap.inr F (Ainf F) (Af F) (intFin (n • y)) = _
    rw [intFin_nsmul, map_nsmul]
  have h := hsub hmem
  simp only [Set.mem_setOf_eq] at h
  rwa [e, AddChar.map_nsmul_eq_pow] at h

end GlobalTheory.PsiProd

namespace GlobalTheory.PsiProd

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem addChar_sum {A ι : Type} [AddCommMonoid A] (χ : AddChar A ℂ) (s : Finset ι) (f : ι → A) :
    χ (∑ i ∈ s, f i) = ∏ i ∈ s, χ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [AddChar.map_zero_eq_one]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

theorem psiAt_eq_one_of_integral {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (I : Finset (HeightOneSpectrum (𝓞 F)))
    (hI : ∀ y : ∀ v : HeightOneSpectrum (𝓞 F), ↥(v.adicCompletionIntegers F),
      (∀ v ∈ I, y v = 0) → ψ (LinearMap.inr F (Ainf F) (Af F) (intFin y)) = 1)
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ I) (a : Fv F v) (ha : a ∈ v.adicCompletionIntegers F) :
    GlobalTheory.LatVac.psiAt ψ v a = 1 := by
  classical
  let y : ∀ u : HeightOneSpectrum (𝓞 F), ↥(u.adicCompletionIntegers F) := Pi.single v ⟨a, ha⟩
  have hy : ∀ u ∈ I, y u = 0 := fun u hu => Pi.single_eq_of_ne (by rintro rfl; exact hv hu) _
  have hfin : intFin y = GlobalTheory.AdelicU.singleFin v a := by
    refine GlobalTheory.AdelicU.af_ext fun w => ?_
    rw [evalV_intFin]
    by_cases e : w = v
    · subst e
      rw [GlobalTheory.AdelicU.evalV_singleFin_self]
      simp [y]
    · rw [GlobalTheory.AdelicU.evalV_singleFin_ne e]
      simp [y, Pi.single_eq_of_ne e]
  have := hI y hy
  rw [hfin] at this
  exact this

theorem psi_prod : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ x : AF F,
    (Function.mulSupport fun v : Pl F => GlobalTheory.LatVac.psiAt ψ v (evFin F v x)).Finite ∧
    ψ x = ψ (pairA F (fstA F x) 0) * ∏ᶠ v : Pl (F := F), GlobalTheory.LatVac.psiAt ψ v (evFin F v x) := by
  intro F _ _ ψ hψ x
  classical
  obtain ⟨I, hI⟩ := exists_finset_trivial ψ hψ
  set xf : Af F := sndA F x with hxf
  have hT : {v : HeightOneSpectrum (𝓞 F) | evalV F v xf ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 xf.2
  let S : Finset (HeightOneSpectrum (𝓞 F)) := I ∪ hT.toFinset
  have hev : ∀ v, evFin F v x = evalV F v xf := fun v => rfl
  have hsupp : (Function.mulSupport fun v : Pl F => GlobalTheory.LatVac.psiAt ψ v (evFin F v x)) ⊆ (S : Set _) := by
    intro v hv
    by_contra hvS
    apply hv
    simp only [S, Finset.coe_union, Set.mem_union, Finset.mem_coe, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
      not_or, not_not] at hvS
    show GlobalTheory.LatVac.psiAt ψ v (evFin F v x) = 1
    rw [hev]
    exact psiAt_eq_one_of_integral ψ I hI v hvS.1 _ hvS.2
  refine ⟨(S.finite_toSet).subset hsupp, ?_⟩
  let j : Af F →ₗ[F] AF F := LinearMap.inr F (Ainf F) (Af F)
  let χ : AddChar (Af F) ℂ := ψ.compAddMonoidHom j.toAddMonoidHom
  have hχ : ∀ a, χ a = ψ (j a) := fun a => rfl
  have hloc : ∀ v (a : Fv F v), GlobalTheory.LatVac.psiAt ψ v a = χ (GlobalTheory.AdelicU.singleFin v a) := fun v a => rfl
  have hx : x = pairA F (fstA F x) 0 + j xf := by
    refine Prod.ext ?_ ?_
    · show x.1 = x.1 + (0 : Ainf F)
      rw [add_zero]
    · show x.2 = (0 : Af F) + x.2
      rw [zero_add]
  let r : ∀ w : HeightOneSpectrum (𝓞 F), ↥(w.adicCompletionIntegers F) := fun w =>
    if hw : w ∈ S then 0 else ⟨evalV F w xf, by
      have : w ∉ hT.toFinset := fun h => hw (Finset.mem_union_right _ h)
      simpa using this⟩
  have hr : ∀ v ∈ I, r v = 0 := fun v hv => dif_pos (Finset.mem_union_left _ hv)
  have hdec : xf = ∑ v ∈ S, GlobalTheory.AdelicU.singleFin v (evalV F v xf) + intFin r := by
    refine GlobalTheory.AdelicU.af_ext fun w => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_add (f := _), map_sum, evalV_intFin]
    by_cases hw : w ∈ S
    · rw [Finset.sum_eq_single w (fun b _ hb => GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hb) _)
        (fun h => absurd hw h), GlobalTheory.AdelicU.evalV_singleFin_self]
      simp [r, hw]
    · rw [Finset.sum_eq_zero (fun b hb => GlobalTheory.AdelicU.evalV_singleFin_ne (by rintro rfl; exact hw hb) _)]
      simp [r, hw]
  have hrr : χ (intFin r) = 1 := hI r hr
  rw [finprod_eq_prod_of_mulSupport_subset _ hsupp]
  conv_lhs => rw [hx]
  rw [AddChar.map_add_eq_mul]
  congr 1
  rw [← hχ, hdec, AddChar.map_add_eq_mul, hrr, mul_one, addChar_sum]
  exact Finset.prod_congr rfl fun v _ => by rw [hloc, hev]

end GlobalTheory.PsiProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicAddCharEqArchimedeanMulFinprodLocalStatement
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicAddChar_eq_archimedean_mul_finprod_local : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ → ∀ x : AF F,
    (Function.mulSupport fun v : Pl F => GlobalTheory.LatVac.psiAt ψ v (evFin F v x)).Finite ∧
    ψ x = ψ (pairA F (fstA F x) 0) * ∏ᶠ v : Pl (F := F), GlobalTheory.LatVac.psiAt ψ v (evFin F v x) := by
  first | exact @GlobalTheory.PsiProd.psi_prod | exact GlobalTheory.PsiProd.psi_prod | (intros; apply GlobalTheory.PsiProd.psi_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearModelArchimedeanSchroedingerStandard
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearModelArchimedeanSchroedingerStandard
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped RealInnerProductSpace

noncomputable section

namespace GlobalTheory.WeilAdm.RealModel

variable {F : Type} [Field F] [NumberField F]

def pt (a : mixedEmbedding.mixedSpace F) : AdeleRing (𝓞 F) F :=
  ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0)

def fstH : AdeleRing (𝓞 F) F →+* InfiniteAdeleRing F := RingHom.fst _ _

def sndH : AdeleRing (𝓞 F) F →+* FiniteAdeleRing (𝓞 F) F := RingHom.snd _ _

theorem pt_ext {x y : AdeleRing (𝓞 F) F} (h1 : fstH x = fstH y) (h2 : sndH x = sndH y) : x = y :=
  Prod.ext h1 h2

theorem dot_infE_infE {κ : Type} [Fintype κ] (z y : κ → mixedEmbedding.mixedSpace F) :
    infE F z ⬝ᵥ infE F y = pt (∑ i, z i * y i) := by
  refine pt_ext ?_ ?_
  · simp only [dotProduct, map_sum, map_mul]
    change ∑ i, (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (z i) *
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y i) =
      (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (∑ i, z i * y i)
    simp only [map_sum, map_mul]
  · simp only [dotProduct, map_sum, map_mul]
    change ∑ i, (0 : FiniteAdeleRing (𝓞 F) F) * 0 = 0
    simp

theorem invOf_two_mul_pt (S : mixedEmbedding.mixedSpace F) :
    ∃ t, ⅟(2 : AdeleRing (𝓞 F) F) * pt S = pt t ∧ t + t = S := by
  set c : InfiniteAdeleRing F := fstH (⅟(2 : AdeleRing (𝓞 F) F))
  refine ⟨InfiniteAdeleRing.ringEquiv_mixedSpace F (c * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm S), ?_, ?_⟩
  · refine pt_ext ?_ ?_
    · rw [map_mul]
      show c * (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm S = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _
      rw [RingEquiv.symm_apply_apply]
    · rw [map_mul]
      show _ * (0 : FiniteAdeleRing (𝓞 F) F) = 0
      exact mul_zero _
  · have hc : c * 2 = 1 := by
      have h := congrArg fstH (invOf_mul_self (2 : AdeleRing (𝓞 F) F))
      rwa [map_mul, map_ofNat, map_one] at h
    rw [← map_add (f := _), ← add_mul, ← mul_two, hc, one_mul, RingEquiv.apply_symm_apply]

theorem schrInf_eq (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ)
    (hψ : ∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) =
      Complex.exp (2 * Real.pi * Complex.I * β a))
    {κ : Type} [Fintype κ] (v : (κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))
    (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ) (z : κ → mixedEmbedding.mixedSpace F) :
    schrInf F ψ v φ z = Complex.exp (2 * Real.pi * Complex.I *
      (β (∑ i, z i * v.2 i) + β (∑ i, v.1 i * v.2 i) / 2)) * φ (z + v.1) := by
  have hψ' : ∀ a, ψ (pt a) = Complex.exp (2 * Real.pi * Complex.I * β a) := hψ
  obtain ⟨t, ht, htt⟩ := invOf_two_mul_pt (F := F) (∑ i, v.1 i * v.2 i)
  have hsum : ∀ a b : mixedEmbedding.mixedSpace F, pt (F := F) a + pt b = pt (a + b) := by
    intro a b
    refine pt_ext ?_ ?_
    · rw [map_add (f := _)]
      exact (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm _ _).symm
    · rw [map_add (f := _)]
      exact add_zero (0 : FiniteAdeleRing (𝓞 F) F)
  have hbt : β t = β (∑ i, v.1 i * v.2 i) / 2 := by
    rw [← htt, map_add (f := _)]; ring
  show ψ (infE F z ⬝ᵥ infE F v.2 + ⅟(2 : AdeleRing (𝓞 F) F) * (infE F v.1 ⬝ᵥ infE F v.2)) * φ (z + v.1) = _
  rw [dot_infE_infE, dot_infE_infE, ht, hsum, hψ', map_add (f := _), hbt]
  push_cast
  ring_nf

end GlobalTheory.WeilAdm.RealModel

namespace GlobalTheory.WeilAdm.RealModel

variable {F : Type} [Field F] [NumberField F]

def bil (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) (κ : Type) [Fintype κ] :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z y => β (∑ i, z i * y i))
    (fun z z' y => by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, map_add (f := _)])
    (fun c z y => by simp only [Pi.smul_apply, smul_mul_assoc, ← Finset.smul_sum, map_smul, smul_eq_mul])
    (fun z y y' => by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)])
    (fun c z y => by simp only [Pi.smul_apply, mul_smul_comm, ← Finset.smul_sum, map_smul, smul_eq_mul])

theorem bil_apply (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) {κ : Type} [Fintype κ]
    (z y : κ → mixedEmbedding.mixedSpace F) : bil β κ z y = β (∑ i, z i * y i) := rfl

def qmap (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) {κ : Type} [Fintype κ] {n : ℕ}
    (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)) :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) where
  toFun y := (InnerProductSpace.toDual ℝ _).symm
    (LinearMap.toContinuousLinearMap (((bil β κ).flip y).comp (Q : EuclideanSpace ℝ (Fin n) →L[ℝ] _).toLinearMap))
  map_add' y y' := by
    refine ext_inner_right ℝ fun x => ?_
    simp [InnerProductSpace.toDual_symm_apply, inner_add_left]
  map_smul' c y := by
    refine ext_inner_right ℝ fun x => ?_
    simp [InnerProductSpace.toDual_symm_apply, real_inner_smul_left]

theorem inner_qmap (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) {κ : Type} [Fintype κ] {n : ℕ}
    (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)) (y : κ → mixedEmbedding.mixedSpace F)
    (x : EuclideanSpace ℝ (Fin n)) : ⟪qmap β Q y, x⟫ = bil β κ (Q x) y := by
  simp [qmap, InnerProductSpace.toDual_symm_apply]

theorem qmap_injective (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) (hβ : ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0)
    {κ : Type} [Fintype κ] {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)) :
    Function.Injective (qmap β Q) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro y hy
  by_contra hne
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  obtain ⟨b, hb⟩ := hβ (y i) hi
  have h := inner_qmap β Q y (Q.symm (Pi.single i b))
  rw [hy, inner_zero_left, ContinuousLinearEquiv.apply_symm_apply, bil_apply] at h
  have hs : ∑ j, (Pi.single i b : κ → mixedEmbedding.mixedSpace F) j * y j = y i * b := by
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_eq_of_ne hj]) (by simp)]
    simp [mul_comm]
  rw [hs] at h
  exact hb h.symm

def qEquiv (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) (hβ : ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0)
    {κ : Type} [Fintype κ] {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F)) :
    (κ → mixedEmbedding.mixedSpace F) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.linearEquivOfInjective (qmap β Q) (qmap_injective β hβ Q) Q.toLinearEquiv.finrank_eq.symm

theorem qmap_qEquiv_symm (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ) (hβ : ∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0)
    {κ : Type} [Fintype κ] {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F))
    (q : EuclideanSpace ℝ (Fin n)) : qmap β Q ((qEquiv β hβ Q).symm q) = q := by
  exact (qEquiv β hβ Q).apply_symm_apply q

def Peq {V : Type} [AddCommGroup V] [Module ℝ V] {n : ℕ} (Q : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] V)
    (Y : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] V) : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] V × V where
  toFun w := (Q (GlobalTheory.RealWeil.pPart w), Y (GlobalTheory.RealWeil.qPart w))
  invFun p := Sum.elim (WithLp.ofLp (Q.symm p.1)) (WithLp.ofLp (Y.symm p.2))
  map_add' w w' := by simp [GlobalTheory.RealWeil.pPart_add, GlobalTheory.RealWeil.qPart_add]
  map_smul' c w := by simp [GlobalTheory.RealWeil.pPart_smul, GlobalTheory.RealWeil.qPart_smul]
  left_inv w := by
    funext j
    cases j <;> simp [GlobalTheory.RealWeil.pPart, GlobalTheory.RealWeil.qPart]
  right_inv p := by
    have h1 : GlobalTheory.RealWeil.pPart (Sum.elim (WithLp.ofLp (Q.symm p.1)) (WithLp.ofLp (Y.symm p.2))) = Q.symm p.1 := by
      simp [GlobalTheory.RealWeil.pPart]
    have h2 : GlobalTheory.RealWeil.qPart (Sum.elim (WithLp.ofLp (Q.symm p.1)) (WithLp.ofLp (Y.symm p.2))) = Y.symm p.2 := by
      simp [GlobalTheory.RealWeil.qPart]
    simp only [h1, h2, LinearEquiv.apply_symm_apply]

theorem exists_model : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) =
      Complex.exp (2 * Real.pi * Complex.I * β a)) →
    (∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0) → ∀ (κ : Type) [Fintype κ],
    ∃ (n : ℕ) (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F))
      (P : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))),
      ∀ w (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ),
        GlobalTheory.WeilAdm.schrInf F ψ (P w) φ ∘ Q = GlobalTheory.RealWeil.rhoFun w (φ ∘ Q) := by
  intro F _ _ ψ β hψ hβ κ _
  let Q : EuclideanSpace ℝ (Fin (Module.finrank ℝ (κ → mixedEmbedding.mixedSpace F))) ≃L[ℝ]
      (κ → mixedEmbedding.mixedSpace F) :=
    (LinearEquiv.ofFinrankEq _ _ finrank_euclideanSpace_fin).toContinuousLinearEquiv
  let Y := (qEquiv β hβ Q).symm
  refine ⟨_, Q, Peq Q.toLinearEquiv Y, fun w φ => ?_⟩
  funext x
  have hq := qmap_qEquiv_symm β hβ Q (GlobalTheory.RealWeil.qPart w)
  have h1 := inner_qmap β Q (Y (GlobalTheory.RealWeil.qPart w)) x
  have h2 := inner_qmap β Q (Y (GlobalTheory.RealWeil.qPart w)) (GlobalTheory.RealWeil.pPart w)
  rw [hq, bil_apply] at h1 h2
  simp only [Function.comp_apply, GlobalTheory.RealWeil.rhoFun, GlobalTheory.RealWeil.phase]
  rw [schrInf_eq ψ β hψ]
  show Complex.exp (2 * Real.pi * Complex.I * (β (∑ i, Q x i * Y (GlobalTheory.RealWeil.qPart w) i) +
      β (∑ i, Q (GlobalTheory.RealWeil.pPart w) i * Y (GlobalTheory.RealWeil.qPart w) i) / 2)) *
      φ (Q x + Q (GlobalTheory.RealWeil.pPart w)) = _
  rw [← h1, ← h2, ← map_add (f := _), real_inner_comm (GlobalTheory.RealWeil.pPart w)]
  congr 2
  push_cast
  ring

end GlobalTheory.WeilAdm.RealModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearModelArchimedeanSchroedingerStandardStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_model_archimedean_schroedinger_standard : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (β : mixedEmbedding.mixedSpace F →ₗ[ℝ] ℝ),
    (∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm a, 0) : AdeleRing (𝓞 F) F) =
      Complex.exp (2 * Real.pi * Complex.I * β a)) →
    (∀ a, a ≠ 0 → ∃ b, β (a * b) ≠ 0) → ∀ (κ : Type) [Fintype κ],
    ∃ (n : ℕ) (Q : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F))
      (P : (Fin n ⊕ Fin n → ℝ) ≃ₗ[ℝ] ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F))),
      ∀ w (φ : (κ → mixedEmbedding.mixedSpace F) → ℂ),
        GlobalTheory.WeilAdm.schrInf F ψ (P w) φ ∘ Q = GlobalTheory.RealWeil.rhoFun w (φ ∘ Q) := by
  first | exact @GlobalTheory.WeilAdm.RealModel.exists_model | exact GlobalTheory.WeilAdm.RealModel.exists_model | (intros; apply GlobalTheory.WeilAdm.RealModel.exists_model <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewIdealLatticePointRationalNormKills
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewIdealLatticePointRationalNormKills
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.StdDatum.SkewPoints

theorem absNorm_galois_smul {E : Type} [Field E] [NumberField E] (c : E ≃ₐ[ℚ] E) (B : Ideal (𝓞 E)) :
    Ideal.absNorm (c • B) = Ideal.absNorm B := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv B (c • B) (MulSemiringAction.toRingEquiv _ _ c) rfl).toEquiv).symm

theorem points : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ {a d : ℕ}, ∀ y ∈ (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)), ∃ z : Matrix (Fin d) (Fin a) D.host.E, y = pt D (tor0 D ⊤ δ) δ z ∧ Ideal.absNorm 𝔪 • pt D (tor0 D ⊤ δ) δ z ∈ (La0 D (tor0 D ⊤ δ) a d) := by
  intro D δ _ 𝔪 h𝔪 a d y hy
  have hrange : La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d) ≤ (GlobalTheory.ThetaLatticePoints.ptHom D ⊤ δ a d).range := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨w, hw, A, -, rfl⟩
    obtain ⟨c, -, rfl⟩ := (GlobalTheory.CurveLattice.mem_lamOf D ⊤ δ w).1 hw
    exact ⟨((c : D.host.K) : D.host.E) • A, GlobalTheory.ThetaLatticePoints.ptHom_smul D ⊤ δ a d c A⟩
  obtain ⟨z, hz⟩ := hrange hy
  rw [GlobalTheory.ThetaLatticePoints.ptHom_apply] at hz
  refine ⟨z, hz.symm, ?_⟩
  rw [hz, ← absNorm_galois_smul (D.host.conj : D.host.E ≃ₐ[ℚ] D.host.E) 𝔪]
  exact GlobalTheory.FunObj.CosetTheta.absNormConj_smul_mem_stdThetaLattice h𝔪 hy

end GlobalTheory.FunObj.StdDatum.SkewPoints

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewIdealLatticePointRationalNormKillsStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skewIdealLattice_point_rational_normKills : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ {a d : ℕ}, ∀ y ∈ (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)), ∃ z : Matrix (Fin d) (Fin a) D.host.E, y = pt D (tor0 D ⊤ δ) δ z ∧ Ideal.absNorm 𝔪 • pt D (tor0 D ⊤ δ) δ z ∈ (La0 D (tor0 D ⊤ δ) a d) := by
  first | exact @GlobalTheory.FunObj.StdDatum.SkewPoints.points | exact GlobalTheory.FunObj.StdDatum.SkewPoints.points | (intros; apply GlobalTheory.FunObj.StdDatum.SkewPoints.points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticFormUnitaryGroupActionInvariant
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticFormUnitaryGroupActionInvariant
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix

namespace GlobalTheory.DblVacEigen.SympAct

theorem hTens_eq_mat {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (JA : Matrix α α E) (JB : Matrix β β E) (x y : Matrix α β E) :
    hTens c JA JB x y = ∑ i, ∑ k, JA i k * (x * JB * (y.map c)ᵀ) i k := by
  unfold hTens
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem symp_actB {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (g : UG c JB)
    (x y : Matrix α β E) : symp c ξ JA JB (actB c g x) (actB c g y) = symp c ξ JA JB x y := by
  have hg : ((g : GL β E) : Matrix β β E)ᵀ * JB * ((g : GL β E) : Matrix β β E).map c = JB := g.2
  have key : actB c g x * JB * ((actB c g y).map c)ᵀ = x * JB * (y.map c)ᵀ := by
    unfold actB
    set_option synthInstance.maxHeartbeats 100000 in
      rw [show (y * ((g : GL β E) : Matrix β β E)ᵀ).map c = y.map c * (((g : GL β E) : Matrix β β E).map c)ᵀ by
      ext i j; simp [Matrix.mul_apply, map_sum, map_mul]]
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]
    calc x * ((g : GL β E) : Matrix β β E)ᵀ * JB * (((g : GL β E) : Matrix β β E).map c * (y.map c)ᵀ)
        = x * (((g : GL β E) : Matrix β β E)ᵀ * JB * ((g : GL β E) : Matrix β β E).map c) * (y.map c)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg]
  unfold symp
  rw [hTens_eq_mat, hTens_eq_mat, key]

end GlobalTheory.DblVacEigen.SympAct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticFormUnitaryGroupActionInvariantStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.DblVacEigen
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceSymplecticForm_unitaryGroupAction_invariant : ∀ {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {α β : Type} [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (ξ : E) (JA : Matrix α α E) (JB : Matrix β β E) (g : UG c JB)
    (x y : Matrix α β E), symp c ξ JA JB (actB c g x) (actB c g y) = symp c ξ JA JB x y := by
  first | exact @GlobalTheory.DblVacEigen.SympAct.symp_actB | exact GlobalTheory.DblVacEigen.SympAct.symp_actB | (intros; apply GlobalTheory.DblVacEigen.SympAct.symp_actB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeHermitianPairing
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open MeasureTheory

namespace GlobalTheory.MultPetersson

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

theorem integrableOn_star_mul (μ : Measure (GA D V)) (𝓕 C : Set (GA D V)) (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (hC : IsCompact C)
    (hcov : ∀ h : GA D V, ∃ γ ∈ GQ V, ∃ c ∈ C, h = γ * c)
    {f f' : GA D V → ℂ} (hf : Continuous f) (hf' : Continuous f')
    (hl : ∀ γ ∈ GQ V, ∀ g, f (γ * g) = f g) (hl' : ∀ γ ∈ GQ V, ∀ g, f' (γ * g) = f' g) :
    IntegrableOn (fun g => star (f g) * f' g) 𝓕 μ :=
  GlobalTheory.CocompactIntegrable.integrableOn_fundamentalDomain V μ 𝓕 C hμ h𝓕 hC hcov _
    ((continuous_star.comp hf).mul hf') (fun γ hγ g => by simp only [hl γ hγ, hl' γ hγ])

variable (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) {ι : Type} [Fintype ι] (M : DSModel V S) (w : ι → M.Vec)

end GlobalTheory.MultPetersson

namespace GlobalTheory.MultPetersson

open MeasureTheory

end GlobalTheory.MultPetersson
end
end
