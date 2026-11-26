module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadsZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridNuUnitTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemPolarizationIdealOfMemConj
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevRowSuccInfUA
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesOverSplitPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneZeroInsertionLinearApply
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyPcRatFMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertIntegralTwistedConjugatesTwistedCentralizer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfIsSmoothModerate
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
open scoped ContDiff

noncomputable section

namespace GlobalTheory.ThK.SmoothLev

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure IsSmModOn (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (Γ : Set (GAd σ J)) (φ : GAd σ J → ℂ) :
    Prop where
  left : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g
  level : ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, φ (g * k) = φ g
  cont : Continuous φ
  smooth : ∀ (k : ℕ) (γ : Fin k → ℝ → GAd σ J), (∀ i, GlobalTheory.SiegelSet.IsRealLine σ J (γ i)) → ∀ g,
    ContDiff ℝ ∞ fun t : Fin k → ℝ => φ (g * (List.ofFn fun i => γ i (t i)).prod)
  growth : ∃ N : ℕ, ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, GlobalTheory.SiegelSet.IsRealLine σ J γ) →
    ∃ C : ℝ, ∀ g, ‖l.foldr GlobalTheory.SiegelSet.lineDer φ g‖ ≤ C * (GlobalTheory.AdelicU.height σ J g : ℝ) ^ N

theorem IsSmModOn.of_isSmoothModerate {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {Γ : Set (GAd σ J)}
    {φ : GAd σ J → ℂ} (h : GlobalTheory.SiegelSet.IsSmoothModerate σ J φ) (hΓ : Γ ⊆ ratPts σ J) : IsSmModOn σ J Γ φ :=
  ⟨fun γ hγ g => h.left γ (hΓ hγ) g, h.level, h.cont, h.smooth, h.growth⟩

theorem isSmModOn_const (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (Γ : Set (GAd σ J)) (c : ℂ) :
    IsSmModOn σ J Γ fun _ => c :=
  have h := GlobalTheory.SiegelSet.isSmoothModerate_const σ J c
  ⟨fun _ _ _ => rfl, h.level, h.cont, h.smooth, h.growth⟩

end GlobalTheory.ThK.SmoothLev

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegFunctionFieldEq
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.FunctionFieldTrdeg

theorem trdeg_functionField_eq : ∀ (F : Type) [Field F] (G : Scheme.{0}) [IsIntegral G] (s : G ⟶ Sp F) (d : ℕ), IsProjOver s → topologicalKrullDim G = d → ∀ (φ : F →+* G.functionField), G.fromSpecStalk (genericPoint G) ≫ s = spMap φ → (letI := φ.toAlgebra; Algebra.trdeg F G.functionField = d) := by
  intro F _ G _ s d hs hd φ hφ
  obtain ⟨N, i, hi, hcomp⟩ := hs
  haveI : IsProper (PSpace.str F N) := isProper_str F N
  haveI : LocallyOfFiniteType s := by rw [← hcomp]; infer_instance
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := G.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint G)) isOpen_univ
  have hU : IsAffineOpen U := hU
  haveI : Nonempty U := ⟨⟨_, hxU⟩⟩
  let ψ := Spec.preimage (hU.fromSpec ≫ s)
  have hψ : Spec.map ψ = hU.fromSpec ≫ s := Spec.map_preimage _
  letI : Algebra F Γ(G, U) := ψ.hom.toAlgebra
  haveI hft : Algebra.FiniteType F Γ(G, U) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (φ := ψ)).mp (hψ ▸ inferInstance)
  have hA : Algebra.trdeg F Γ(G, U) = d :=
    GlobalTheory.GenFinite.trdeg_affineOpen_eq F s hU ⟨_, hxU⟩ d hd
  letI : Algebra F G.functionField := φ.toAlgebra
  have key : CommRingCat.ofHom φ = ψ ≫ G.germToFunctionField U := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    change spMap φ = _
    rw [← hφ, hψ, ← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk, Category.assoc]
  haveI : IsScalarTower F Γ(G, U) G.functionField :=
    IsScalarTower.of_algebraMap_eq' congr($(key).hom)
  haveI := functionField_isFractionRing_of_isAffineOpen G U hU
  haveI : FaithfulSMul F Γ(G, U) := (faithfulSMul_iff_algebraMap_injective _ _).mpr (algebraMap F Γ(G, U)).injective
  haveI : FaithfulSMul Γ(G, U) G.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective Γ(G, U) G.functionField)
  haveI : Algebra.IsAlgebraic Γ(G, U) G.functionField := IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(G, U))
  show Algebra.trdeg F G.functionField = d
  rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top F Γ(G, U) G.functionField, hA]

end GlobalTheory.FunctionFieldTrdeg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLogHomIsMultipleOfLogAbs
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

open scoped GroundTheory.Global.AdeleBaseChange NumberField.AdeleRing

noncomputable section

namespace GlobalTheory.IdeleLogHom

open GroundTheory.Global GroundTheory.Global.AdeleBaseChange

section Transfer

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def toE : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ →* IdeleGroup E :=
  Units.map (adeleTensorAlgEquivLeft F E : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →ₐ[AF F] AdeleRing (𝓞 E) E).toMonoidHom

theorem absE_eq_ideleModule (x : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))ˣ) :
    (absE F E x : ℝ) = (IdeleGroup.ideleModule E (toE F E x) : ℝ) := by
  rw [← GroundTheory.Automorphic.EllipticTorus.ideleModule_ideleNorm (K := F), ← GlobalTheory.ModuAdele.modu_norm_eq_absE]
  have h2 : ∀ u : (AF F)ˣ, (((adeleClass F).modu u : ℝ≥0) : ℝ) = (IdeleGroup.ideleModule F u : ℝ) := fun u => by
    change (distribHaarChar (AdeleRing (𝓞 F) F) u : ℝ) = _
    exact GlobalTheory.ModuAdele.distribHaarChar_adeleRing F u
  have h3 : Units.map (Algebra.norm (AF F) : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E) →* AF F) x = ideleNorm F E (toE F E x) := by
    ext
    simp [toE, ideleNorm, Algebra.norm_eq_of_algEquiv]
  rw [h2, h3]

end Transfer

section OnE

variable {E : Type} [Field E] [NumberField E]

end OnE

end GlobalTheory.IdeleLogHom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleQuotientCompactFundamentalSet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleQuotientCompactFundamentalSet
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
namespace GlobalTheory.AdeleCocompactExt

theorem exists_compact_adeleE : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E],
    ∃ K : Set (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), IsCompact K ∧ ∀ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), ∃ e : E, a - inclR (F := F) (AF F) e ∈ K := by
  intro F E _ _ _ _ _
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨K₀, hK₀, hK⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele F
  haveI : IsModuleTopology (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := ⟨rfl⟩
  haveI : IsTopologicalRing (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) := IsModuleTopology.isTopologicalRing (AF F) _
  let b := Module.finBasis F E
  let B := Algebra.TensorProduct.basis (AF F) b
  have hφ : Continuous B.equivFun.symm :=
    IsModuleTopology.continuous_of_linearMap B.equivFun.symm.toLinearMap
  refine ⟨B.equivFun.symm '' Set.pi Set.univ (fun _ => K₀),
    (isCompact_univ_pi fun _ => hK₀).image hφ, ?_⟩
  intro a
  choose x hx using fun k => hK (B.equivFun a k)
  refine ⟨∑ k, x k • b k, fun k => B.equivFun a k - algebraMap F (AF F) (x k), fun k _ => hx k, ?_⟩
  rw [LinearEquiv.symm_apply_eq]
  funext k
  have h1 : B.equivFun (inclR (F := F) (AF F) (∑ k, x k • b k)) k = algebraMap F (AF F) (x k) := by
    rw [Module.Basis.equivFun_apply]
    show (B.repr ((1 : AF F) ⊗ₜ[F] (∑ k, x k • b k))) k = _
    rw [Algebra.TensorProduct.basis_repr_tmul]
    simp [b, Module.Basis.repr_sum_self]
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [Finsupp.single_apply, hj]) (by simp)]
    simp
  simp only [map_sub, Pi.sub_apply, h1]

end GlobalTheory.AdeleCocompactExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdeleQuotientCompactFundamentalSetStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adele_quotient_compact_fundamental_set : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ K : Set (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), IsCompact K ∧ ∀ a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E), ∃ e : E, a - inclR (F := F) (AF F) e ∈ K := by
  first | exact @GlobalTheory.AdeleCocompactExt.exists_compact_adeleE | exact GlobalTheory.AdeleCocompactExt.exists_compact_adeleE | (intros; apply GlobalTheory.AdeleCocompactExt.exists_compact_adeleE <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAbsMatrixProductLeHeights
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAbsMatrixProductLeHeights
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory

theorem absFin_mul_mul_transpose_le : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (g : GL (Fin n) (AF F ⊗[F] E)) (X : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)) (v : HeightOneSpectrum (𝓞 F)) (i : Fin n) (j : Fin d), absFin F v (compFin F E v (((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * X * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ) i j)) ≤ htFin F v (bc (compFin F E v) g) * (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2))) * htFin F v (bc (compFin F E v) h) := by
  intro F E _ _ _ _ _ n d g X h v i j
  have hg : ∀ a b, ((bc (compFin F E v) g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a b = compFin F E v ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a b) := by
    intro a b; rfl
  have hh : ∀ a b, ((bc (compFin F E v) h : GL (Fin d) (Fv F v ⊗[F] E)) : Matrix (Fin d) (Fin d) (Fv F v ⊗[F] E)) a b = compFin F E v ((h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) a b) := by
    intro a b; rfl
  have hG : ∀ a b, absFin F v (compFin F E v ((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) a b)) ≤ htFin F v (bc (compFin F E v) g) := by
    intro a b
    have h1 := absFin_le_normFin F v ((bc (compFin F E v) g : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) a b
    rw [hg] at h1
    exact h1.trans (le_htOf (normFin F v) _)
  have hH : ∀ a b, absFin F v (compFin F E v ((h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) a b)) ≤ htFin F v (bc (compFin F E v) h) := by
    intro a b
    have h1 := absFin_le_normFin F v ((bc (compFin F E v) h : GL (Fin d) (Fv F v ⊗[F] E)) : Matrix (Fin d) (Fin d) (Fv F v ⊗[F] E)) a b
    rw [hh] at h1
    exact h1.trans (le_htOf (normFin F v) _)
  have hX : ∀ a b, absFin F v (compFin F E v (X a b)) ≤ Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2)) := by
    intro a b
    exact Finset.le_sup (f := fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2))) (b := (a, b)) (Finset.mem_univ _)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.mul_apply, map_sum]
  refine absFin_sum_le F v _ _ fun l _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.transpose_apply, Matrix.mul_apply, map_mul, map_sum]
  refine (absFin_mul_le F v _ _).trans (mul_le_mul' (absFin_sum_le F v _ _ fun k _ => ?_) (hH _ _))
  rw [map_mul]
  exact (absFin_mul_le F v _ _).trans (mul_le_mul' (hG _ _) (hX _ _))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAbsMatrixProductLeHeightsStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_abs_matrix_product_le_heights : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ} (g : GL (Fin n) (AF F ⊗[F] E)) (X : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)) (h : GL (Fin d) (AF F ⊗[F] E)) (v : HeightOneSpectrum (𝓞 F)) (i : Fin n) (j : Fin d), absFin F v (compFin F E v (((g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) * X * (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E))ᵀ) i j)) ≤ htFin F v (bc (compFin F E v) g) * (Finset.univ.sup fun p : Fin n × Fin d => absFin F v (compFin F E v (X p.1 p.2))) * htFin F v (bc (compFin F E v) h) := by
  first | exact @GlobalTheory.absFin_mul_mul_transpose_le | exact GlobalTheory.absFin_mul_mul_transpose_le | (intros; apply GlobalTheory.absFin_mul_mul_transpose_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeviProjTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlParabolicOrbitRepresentatives
open Matrix

namespace GlobalTheory.OrbitsGLParab

variable {k : Type} [Field k]

variable {n m : ℕ}



end GlobalTheory.OrbitsGLParab
end

noncomputable section

namespace GlobalTheory.LocRankBig

open GlobalTheory.SmGL GlobalTheory.SplitWeil

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem totallyDisconnected : TotallyDisconnectedSpace k := by
  obtain ⟨_, _⟩ := Model.secondCountable_and_t2_local_field (k := k)
  haveI : NonarchimedeanAddGroup k := ⟨fun V hV => by
    obtain ⟨s, hs⟩ := GlobalTheory.SplitWeil.exists_cball_subset hV
    exact ⟨⟨⟨⟨⟨GlobalTheory.SplitWeil.cball s, GlobalTheory.SplitWeil.add_mem_cball⟩, by simp [GlobalTheory.SplitWeil.cball]⟩,
      GlobalTheory.SplitWeil.neg_mem_cball⟩, GlobalTheory.SplitWeil.isOpen_cball s⟩, hs⟩⟩
  infer_instance

theorem nonarchimedeanGroup_GL (n : ℕ) : NonarchimedeanGroup (GL (Fin n) k) := by
  haveI := totallyDisconnected (k := k)
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  haveI : TotallyDisconnectedSpace (GL (Fin n) k) :=
    ⟨isTotallyDisconnected_of_image (f := fun g : GL (Fin n) k => g.val) Units.continuous_val.continuousOn
      Units.val_injective (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  haveI : CompactSpace (KO k (Fin n)) := isCompact_iff_compactSpace.1 GlobalTheory.SplitFlip.isCompact_KO
  haveI : NonarchimedeanGroup (KO k (Fin n)) := ⟨fun U hU => by
    obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one (isOpen_interior (s := U))
      (mem_interior_iff_mem_nhds.2 hU)
    exact ⟨N.toOpenSubgroup, hN.trans interior_subset⟩⟩
  exact NonarchimedeanGroup.nonarchimedean_of_emb (KO k (Fin n)).subtype
    GlobalTheory.SplitFlip.isOpen_KO.isOpenEmbedding_subtypeVal

end Local

end GlobalTheory.LocRankBig
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceEmbeddingExists
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceEmbeddingExists
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology

namespace GlobalTheory.SplitEmbed

theorem exists_algHom_of_splitsFully : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ v : Pl (F := F), SplitsFully E v → Nonempty (E →ₐ[F] Fv F v) := by
  intro F E _ _ _ _ _ σ h v hs
  classical
  haveI hprime : (v.asIdeal.under ℤ).IsPrime := Ideal.IsPrime.under ℤ v.asIdeal
  have hne : v.asIdeal.under ℤ ≠ ⊥ := by
    intro hb
    exact v.ne_bot (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) hb)
  obtain ⟨q, hq⟩ := (Submodule.IsPrincipal.principal (v.asIdeal.under ℤ))
  have hq' : v.asIdeal.under ℤ = Ideal.span {q} := hq
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact hne (by rw [hq']; simp)
  have hqp : Prime q := by
    rw [← Ideal.span_singleton_prime hq0, ← hq']
    exact hprime
  set p := q.natAbs with hpdef
  have hp : p.Prime := Int.prime_iff_natAbs_prime.1 hqp
  have hspan : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [hq', hpdef, Int.span_natAbs]
  have hpv : (p : 𝓞 F) ∈ v.asIdeal := by
    have : (p : ℤ) ∈ v.asIdeal.under ℤ := by rw [hspan]; exact Ideal.mem_span_singleton_self _
    rw [Ideal.under_def, Ideal.mem_comap] at this
    simpa using this
  have hcount : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E := by
    have := hs
    unfold SplitsFully at this
    rw [hspan] at this
    exact this
  rw [GlobalTheory.AdelicU.nonempty_split_iff h]
  exact GlobalTheory.GoodPlace.ncard_primesOver_eq_two h.2.2.1 hp hcount v hpv

end GlobalTheory.SplitEmbed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceEmbeddingExistsStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_embedding_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ v : Pl (F := F), SplitsFully E v → Nonempty (E →ₐ[F] Fv F v) := by
  first | exact @GlobalTheory.SplitEmbed.exists_algHom_of_splitsFully | exact GlobalTheory.SplitEmbed.exists_algHom_of_splitsFully | (intros; apply GlobalTheory.SplitEmbed.exists_algHom_of_splitsFully <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTranslatesKernelRouteSmallVertex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTranslatesKernelRouteSmallVertex
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SmallRoute

theorem continuous_translates_kerSmall : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j))
    (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))) (z : GA D (G.V (.grid i j)) →₀ ℂ),
    Continuous (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) =>
      translates z (kerSmall W Θ' p.1 g₁) p.2) := by
  intro D T L sc G μ₀ hL W B ρ t i j Θ Θ' hΘ g₁ z
  obtain ⟨_, _, _, _, hTG, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid i j))
  have hc := W.om_is (.chi (i : ℕ) j) ⟨i.2, j.2.le⟩
  have hm := W.om_is (.mu t (i : ℕ) j) ⟨i.2.le, j.2⟩
  have hK : ∀ d ∈ Θ'.support, Continuous (fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) =>
      W.kerA (.down t i j) d.1.2 q.1 q.2 * W.kerA (.right i j) d.2 q.2 g₁) := by
    intro d hd
    obtain ⟨h2, h1⟩ := theta_of_matched hΘ hd
    refine Continuous.mul ?_ ?_
    · show Continuous fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) =>
        thetaKO (W.om (.mu t (i : ℕ) j)) q.2 q.1 d.1.2
      exact (hm.om_cont _ h1 0).comp (continuous_snd.prodMk continuous_fst)
    · show Continuous fun q : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) =>
        thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) q.2 d.2
      exact (hc.om_cont _ h2 0).comp (continuous_const.prodMk continuous_snd)
  unfold translates kerSmall
  simp only [Finsupp.sum]
  refine continuous_finsetSum _ fun k _ => continuous_const.mul ?_
  refine continuous_finsetSum _ fun d hd => continuous_const.mul ?_
  exact (hK d hd).comp (continuous_fst.prodMk (continuous_snd.mul continuous_const))

end GlobalTheory.SmallRoute
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTranslatesKernelRouteSmallVertexStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_translates_kernel_route_small_vertex : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j))
    (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))) (z : GA D (G.V (.grid i j)) →₀ ℂ),
    Continuous (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) =>
      translates z (kerSmall W Θ' p.1 g₁) p.2) := by
  first | exact @GlobalTheory.SmallRoute.continuous_translates_kerSmall | exact GlobalTheory.SmallRoute.continuous_translates_kerSmall | (intros; apply GlobalTheory.SmallRoute.continuous_translates_kerSmall <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumAdjointNegSourceKernelsAgree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumAdjointNegSourceKernelsAgree
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.RouteSeesaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.AdjSwap

theorem dagger_eq_adjM {D : D7} (S B : HSp D) (y : Mx D B.rank S.rank) :
    GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S B y = adjM S B y := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger, adjM]
  rw [← Matrix.mul_assoc]
  rfl

theorem weil_adjoint_negSource : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S B : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (ω₂ : GA D B × GA D S →* Module.End ℂ (WO B S → ℂ)), IsWeilDatumO ψ B S χS χT ω₂ →
    ∃ (ω : GA D (negSp S) × GA D B →* Module.End ℂ (WO (negSp S) B → ℂ)) (χ χ' : (AE D)ˣ →* Circle),
      IsWeilDatumO ψ (negSp S) B χ χ' ω ∧ ∀ f : WO B S → ℂ, IsThetaFunO ψ B S f →
        IsThetaFunO ψ (negSp S) B (fun y => f (adjM S B y)) ∧
        ∀ g₁ u, thetaKO ω (negGA S u) g₁ (fun y => f (adjM S B y)) = thetaKO ω₂ g₁ u f := by
  intro D ψ hψ S B χS χT ω₂ H
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint ω₂), χT⁻¹, χS⁻¹,
    GlobalTheory.ConjWeil.weil_conjSource D ψ S B _ _ _ (GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ B S _ _ ω₂ H),
    fun f hf => ?_⟩
  have e : (fun y : WO (negSp S) B => f (adjM S B y)) =
      GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S B) f) := by
    funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_eq_adjM]
  rw [e]
  have h1 : IsThetaFunO ψ S B (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S B) f) :=
    ((GlobalTheory.AdjointPair.adjoint_clauses D ψ hψ B S).2.2.1 f).2 hf
  refine ⟨((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S B).1 _).2.2 h1, fun g₁ u => ?_⟩
  show GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint ω₂) (negGA S u, g₁) _ 0 = ω₂ (g₁, u) f 0
  rw [GlobalTheory.ConjWeil.conjSource_apply]
  simp only [MulEquiv.symm_apply_apply, GlobalTheory.ConjWeil.cj_id_cj_id]
  rw [GlobalTheory.TensorTargetRule.conjAdjoint_cj]
  simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_eq_adjM, adjM_zero]

end GlobalTheory.AdjSwap
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumAdjointNegSourceKernelsAgreeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.RouteSeesaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilDatum_adjoint_negSource_kernels_agree : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S B : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (ω₂ : GA D B × GA D S →* Module.End ℂ (WO B S → ℂ)), IsWeilDatumO ψ B S χS χT ω₂ →
    ∃ (ω : GA D (negSp S) × GA D B →* Module.End ℂ (WO (negSp S) B → ℂ)) (χ χ' : (AE D)ˣ →* Circle),
      IsWeilDatumO ψ (negSp S) B χ χ' ω ∧ ∀ f : WO B S → ℂ, IsThetaFunO ψ B S f →
        IsThetaFunO ψ (negSp S) B (fun y => f (adjM S B y)) ∧
        ∀ g₁ u, thetaKO ω (negGA S u) g₁ (fun y => f (adjM S B y)) = thetaKO ω₂ g₁ u f := by
  first | exact @GlobalTheory.AdjSwap.weil_adjoint_negSource | exact GlobalTheory.AdjSwap.weil_adjoint_negSource | (intros; apply GlobalTheory.AdjSwap.weil_adjoint_negSource <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPlacesPrimeToLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPlacesPrimeToLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlacesPrime

theorem not_both_mem {R : Type} [CommRing R] {I : Ideal R} (hI : I.IsPrime) {a b : ℕ} (h : Nat.Coprime a b)
    (ha : (a : R) ∈ I) : (b : R) ∉ I := by
  intro hb
  obtain ⟨u, v, e⟩ := (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom R)
  apply hI.ne_top
  rw [Ideal.eq_top_iff_one, ← e]
  simp only [eq_intCast, Int.cast_natCast]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ ha) (Ideal.mul_mem_left _ _ hb)

theorem coprime_level {D : D7} {large₂ : SizeData₂ D} (h : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) {p : ℕ} (hp : p.Prime)
    (hl : p ∈ D.host.levelPrimes) : Nat.Coprime p (D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK) := by
  obtain ⟨⟨P, -, -⟩, -⟩ := h
  exact Nat.Coprime.mul_right (UpperTheory.Ram.Fun.coprime_condN_of_splitK D.host hp (P.level_split p hl))
    (D.host.ccK_coprime p (by simp [hl])).symm

theorem leastSplitAuxiliaryPrime_coprime_host_invariants (D : D7) : Nat.Coprime (q0 D) (D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK) := by
  obtain ⟨hp, hm, hn⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
  have hM : Nat.Coprime (q0 D) (Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D) := by
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hm, Nat.gcd_one_left]
  have hdvd : D.host.QS * D.host.q * D.host.d ∣ Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D :=
    Dvd.dvd.mul_left dvd_rfl _
  exact Nat.Coprime.mul_right (hM.coprime_dvd_right hdvd) ((Nat.Prime.coprime_iff_not_dvd hp).2 hn)

theorem places_prime_to_level : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ w ∈ ch.G.pl.W0,
    ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _ => ?_⟩⟩
  intro w hw
  classical
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
  have hunder := ch.G.pl.under_w hv

  have lift : ∀ n : ℕ, ((n : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal → ((n : ℕ) : 𝓞 D.host.E) ∈ (ch.G.pl.w v).asIdeal := by
    intro n hn
    rw [← hunder] at hn
    have := Ideal.mem_comap.1 hn
    simpa using this
  obtain ⟨p, hp, hcop⟩ : ∃ p : ℕ, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∧
      Nat.Coprime p (D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK) := by
    rcases ch.G.pl.mem_S0_of_sum_eq.1 hv with rfl | h1
    · exact ⟨q0 D, ch.G.pl.basePlace_over_qZero, leastSplitAuxiliaryPrime_coprime_host_invariants D⟩
    · rcases (S1_mem_OmF D).1 h1 with h | h | h | h
      · exact ⟨_, h, coprime_level hS.size (D.host.g_prime 0) (D.host.g_level 0)⟩
      · exact ⟨_, h, coprime_level hS.size (D.host.g_prime 1) (D.host.g_level 1)⟩
      · exact ⟨_, h, coprime_level hS.size D.host.pde_prime D.host.pde_level.1⟩
      · exact ⟨_, h, coprime_level hS.size D.host.pde'_prime D.host.pde_level.2⟩
  exact not_both_mem (ch.G.pl.w v).isPrime hcop (lift p hp)

end GlobalTheory.PlacesPrime
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TestPlacesPrimeToLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_places_prime_to_level : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ w ∈ ch.G.pl.W0,
    ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := by
  first | exact @GlobalTheory.PlacesPrime.places_prime_to_level | exact GlobalTheory.PlacesPrime.places_prime_to_level | (intros; apply GlobalTheory.PlacesPrime.places_prime_to_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimTranslationRepUnitaryModel
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitarisableOfCompact
open MeasureTheory GlobalTheory.Dec
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace GlobalTheory.UniTrick

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

theorem continuous_lin {ι : Type} [Fintype ι] (ρ : Representation ℂ G V)
    (hρ : ∀ (φ : V →ₗ[ℂ] ℂ) (v : V), Continuous fun g => φ (ρ g v))
    (f : V →ₗ[ℂ] EuclideanSpace ℂ ι) (v : V) : Continuous fun g => f (ρ g v) := by
  have h : ∀ i, Continuous fun g => (f (ρ g v)) i := fun i =>
    hρ ((EuclideanSpace.proj i : EuclideanSpace ℂ ι →L[ℂ] ℂ).toLinearMap ∘ₗ f) v
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi h)

variable [MeasurableSpace G] [BorelSpace G]

variable [CompactSpace G]

end GlobalTheory.UniTrick

namespace GlobalTheory

end GlobalTheory
end
end

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.ThetaCplV.UnitaryTrick

theorem exists_isURep_of_core {K : Type} [Group K] [TopologicalSpace K] [IsTopologicalGroup K] {V : Type} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ K V)
    (hρ : ∀ (φ : V →ₗ[ℂ] ℂ) (v : V), Continuous fun k => φ (ρ k v))
    (c : InnerProductSpace.Core ℂ V) (hc : ∀ k u v, c.inner (ρ k u) (ρ k v) = c.inner u v) :
    ∃ (d : ℕ) (τ : K → (EuclideanSpace ℂ (Fin d) →L[ℂ] EuclideanSpace ℂ (Fin d)))
      (e : V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin d)), GlobalTheory.Dec.IsURep τ ∧ ∀ k v, e (ρ k v) = τ k (e v) := by
  letI cd : InnerProductSpace.Core ℂ V := c
  letI : NormedAddCommGroup V := @InnerProductSpace.Core.toNormedAddCommGroup ℂ V _ _ _ cd
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore cd.toCore
  let b := stdOrthonormalBasis ℂ V
  let e : V ≃ₗ[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) := b.repr.toLinearEquiv
  let τ : K → (EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →L[ℂ] EuclideanSpace ℂ (Fin (Module.finrank ℂ V))) :=
    fun g => LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ ρ g ∘ₗ e.symm.toLinearMap)
  have hτ : ∀ g x, τ g x = e (ρ g (e.symm x)) := fun _ _ => rfl
  have hn : ∀ g (y : V), ‖ρ g y‖ = ‖y‖ := by
    intro g y
    have h1 : inner ℂ (ρ g y) (ρ g y) = inner ℂ y y := hc g y y
    rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, h1]
  refine ⟨_, τ, e, ⟨?_, fun a c => ?_, fun g x => ?_, fun x => ?_⟩, fun g v => ?_⟩
  · ext1 x; simp [hτ]
  · ext1 x; simp [hτ, map_mul]
  · rw [hτ]
    change ‖b.repr (ρ g (b.repr.symm x))‖ = ‖x‖
    rw [LinearIsometryEquiv.norm_map, hn, ← LinearIsometryEquiv.norm_map b.repr,
      LinearIsometryEquiv.apply_symm_apply]
  · simp only [hτ]
    exact GlobalTheory.UniTrick.continuous_lin ρ hρ e.toLinearMap _
  · rw [hτ, LinearEquiv.symm_apply_apply]

end GlobalTheory.ThetaCplV.UnitaryTrick

namespace GlobalTheory.ThetaCplV


end GlobalTheory.ThetaCplV
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModTSupConj
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open GlobalTheory.SqTop (twPl Qn modT)

noncomputable section

namespace GlobalTheory.SqTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem modT_sup_conj : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (t : T),
    modT G t ⊔ D.host.conj • modT G t = ⊤ := by
  intro D T L sc μ₀ hL G t
  classical
  have hcc : ∀ x : D.host.E, GlobalTheory.Member.cF D x = D.host.conj x := fun x => Formalism.BasicNotions.bridge_star_holds D.R D.host x
  have hund : ∀ PP PP' : HeightOneSpectrum (𝓞 D.host.E), PP.asIdeal = D.host.conj • PP'.asIdeal →
      (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') := by
    intro PP PP' h
    have hc : GlobalTheory.Mem.Chr.ConjPl (GlobalTheory.Member.cF D).toRingEquiv PP' PP := by
      rw [GlobalTheory.Mem.Chr.conjPl_iff_mem]
      intro x y hxy
      have hy : y = D.host.conj • x := RingOfIntegers.ext (by rw [hxy]; exact hcc _)
      rw [hy, h]
      exact Ideal.smul_mem_pointwise_smul_iff.symm
    exact (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (GlobalTheory.Member.cF D) D.sp.cm.deg2 (GlobalTheory.IdeleNinety.conj_ne_one D) PP' PP).2
      (Or.inr hc)
  have hmax' : ∀ PP : HeightOneSpectrum (𝓞 D.host.E), (D.host.conj • PP.asIdeal).IsMaximal := by
    intro PP
    have := PP.isPrime
    refine Ideal.IsPrime.isMaximal inferInstance fun h0 => PP.ne_bot ?_
    have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h0
    simpa using this
  have hmem : ∀ w ∈ twPl G t, w ∈ L.Q t ∧ w ∉ G.pl.W0 := by
    intro w hw
    rw [twPl, Finset.mem_filter, GlobalTheory.FunObj.locPl, Finset.mem_union] at hw
    exact ⟨hw.1.resolve_left hw.2, hw.2⟩
  have hoff : ∀ w ∈ twPl G t, w.under (𝓞 D.host.F) ∉ G.pl.S0 := by
    intro w hw hS
    obtain ⟨hQ, hW⟩ := hmem w hw
    rcases G.pl.mem_S0_of_sum_eq.1 hS with h0 | h1
    · exact G.pl.levelPlace_ne_basePlace t w hQ h0
    · apply hW
      rw [G.pl.w_Q t w hQ h1]
      exact Finset.mem_image_of_mem _ hS
  have hAB : ∀ v ∈ G.pl.S0, ∀ w ∈ twPl G t, (G.pl.w v).asIdeal ≠ D.host.conj • w.asIdeal := by
    intro v hv w hw h
    exact hoff w hw (by rw [← hund _ _ h, G.pl.under_w hv]; exact hv)
  have hBA : ∀ w ∈ twPl G t, ∀ v ∈ G.pl.S0, w.asIdeal ≠ D.host.conj • (G.pl.w v).asIdeal := by
    intro w hw v hv h
    exact hoff w hw (by rw [hund _ _ h, G.pl.under_w hv]; exact hv)
  have hBB : ∀ w ∈ twPl G t, ∀ w' ∈ twPl G t, w.asIdeal ≠ D.host.conj • w'.asIdeal := by
    intro w hw w' hw' h
    refine (hL.Q_pl t w' (hmem w' hw').1).2 w (hmem w hw).1 fun c hc => ⟨D.host.conj • c, ?_, ?_⟩
    · rw [h]; exact Ideal.smul_mem_pointwise_smul _ _ _ hc
    · exact (Formalism.BasicNotions.bridge_star_holds D.R D.host _).symm
  rw [modT, smul_mul', ← Ideal.isCoprime_iff_sup_eq]
  refine IsCoprime.mul_left (IsCoprime.mul_right ?_ ?_) (IsCoprime.mul_right ?_ ?_) <;> rw [Ideal.isCoprime_iff_sup_eq]
  · exact condE_sup_conj G.pl
  · rw [Finset.smul_prod']
    refine Ideal.prod_sup_eq_top fun v hv => Ideal.sup_prod_eq_top fun w hw => ?_
    exact Ideal.pow_sup_eq_top (Ideal.IsMaximal.coprime_of_ne (G.pl.w v).isMaximal (hmax' w) (hAB v hv w hw))
  · rw [GlobalTheory.FunObj.SqNum.condE, Finset.smul_prod']
    simp only [smul_pow']
    refine Ideal.prod_sup_eq_top fun w hw => Ideal.sup_prod_eq_top fun v hv => ?_
    exact Ideal.sup_pow_eq_top (Ideal.IsMaximal.coprime_of_ne w.isMaximal (hmax' _) (hBA w hw v hv))
  · rw [Finset.smul_prod']
    exact Ideal.prod_sup_eq_top fun w hw => Ideal.sup_prod_eq_top fun w' hw' =>
      Ideal.IsMaximal.coprime_of_ne w.isMaximal (hmax' w') (hBB w hw w' hw')

end GlobalTheory.SqTop

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCommutingTwistedConjCompactMemTwistedCentral
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCommutingTwistedConjCompactMemTwistedCentral
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.NormOneProper

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∀ C : Set (GLw n w), IsCompact C → ∃ D : Set (GLw n w), IsCompact D ∧ ∀ z : GLw n w, z * nrmL n w y = nrmL n w y * z → z⁻¹ * y * thL n w z ∈ C → ∃ t ∈ twCent (thL n w) y, ∃ d ∈ D, z = t * d := by
  intro E _ _ _ hU n w y hy C hC
  by_cases hs : IsSplitAt w
  · refine ⟨{1}, isCompact_singleton, fun z hz _ => ⟨z, ?_, 1, rfl, (mul_one z).symm⟩⟩
    have h1 : thL n w = MonoidHom.id _ := by rw [thL, if_pos hs]
    have h2 : nrmL n w y = y := by rw [nrmL, if_pos hs]
    rw [h2] at hz
    change z * y = y * thL n w z
    rw [h1, MonoidHom.id_apply, hz]
  · set K := w.adicCompletion E
    obtain ⟨-, hinv, hv, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
    letI : StarRing K :=
      { star := cj w
        star_involutive := hinv
        star_mul := fun a b => by rw [map_mul, mul_comm]
        star_add := map_add (cj w) }
    have hse : starRingEnd K = cj w := RingHom.ext fun _ => rfl
    have hθ : thL n w = thetaGL n (starRingEnd K) := by rw [thL, if_neg hs, hse]
    have hθv : ∀ g : GLw n w, (thL n w g).val = GlobalTheory.Tw.theta g.val := fun g => by
      rw [hθ]; exact thetaGL_val g
    have hN : (nrmL n w y).val = GlobalTheory.Tw.nrm y.val := by
      rw [nrmL, if_neg hs, ← hse, Units.val_mul, thetaGL_val]; rfl
    have hReg : GlobalTheory.Tw.Reg (y.val) := ⟨y.isUnit, by rw [← hN]; exact hy⟩
    have TC := GlobalTheory.Tw.twisted_centraliser n K y.val hReg
    letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField _ _
    haveI : ProperSpace K := ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace _
    have hnorm : ∀ x : K, ‖star x‖ = ‖x‖ := fun x => by
      simp only [Valued.toNormedField.norm_def]
      have h1 := Valuation.embedding_restrict (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) (star x)
      have h2 := Valuation.embedding_restrict (Valued.v : Valuation K (WithZero (Multiplicative ℤ))) x
      have h3 : (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).restrict (star x) =
          (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).restrict x :=
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective (h1.trans ((hv x).trans h2.symm))
      rw [h3]
    set C' : Set (GLw n w) := (fun c : GLw n w => y * c⁻¹) '' C
    have hC' : IsCompact C' := hC.image (by fun_prop)
    obtain ⟨D, hD, hDp⟩ := GlobalTheory.T.exists_normOne_mul_compact_of_twistedNorm_compact K hnorm n y.val hReg C' hC'
    refine ⟨D, hD, fun z hz hzC => ?_⟩
    have hzv : z.val * GlobalTheory.Tw.nrm y.val = GlobalTheory.Tw.nrm y.val * z.val := by
      rw [← hN, ← Units.val_mul, hz, Units.val_mul]
    have hzA : z.val ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm y.val} := (TC.2.2.2.2.1 z.val).1 hzv
    have hcomm : ∀ x ∈ Algebra.adjoin K {GlobalTheory.Tw.nrm y.val}, z.val * x = x * z.val := by
      intro x hx
      have hle : Algebra.adjoin K {GlobalTheory.Tw.nrm y.val} ≤ Subalgebra.centralizer K {z.val} := by
        rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
        intro g hg
        rw [Set.mem_singleton_iff] at hg
        subst hg
        exact hzv
      exact hle hx z.val (Set.mem_singleton _)
    have hadj : GlobalTheory.Tw.adj y.val z.val = (y * (thL n w z)⁻¹ * y⁻¹).val := by
      rw [Units.val_mul, Units.val_mul, ← map_inv, hθv, GlobalTheory.Tw.theta, GlobalTheory.Tw.adj]
      have hzi : ((z⁻¹ : GLw n w).val)⁻¹ = z.val := by
        rw [Matrix.coe_units_inv, Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 z.isUnit)]
      rw [hzi, Matrix.coe_units_inv y]
      simp only [Matrix.mul_assoc]
    have hu : (y * (z⁻¹ * y * thL n w z)⁻¹).val = z.val * GlobalTheory.Tw.adj y.val z.val := by
      rw [hcomm _ (TC.2.2.2.1 _ hzA).1, hadj]
      simp only [_root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
    obtain ⟨t, htA, ht1, d, hd, rfl⟩ := hDp z hzA _ ⟨_, hzC, rfl⟩ hu
    refine ⟨t, ?_, d, hd, rfl⟩
    have htc : t.val ∈ GlobalTheory.Tw.cent y.val := by rw [TC.2.2.2.2.2]; exact ⟨htA, ht1⟩
    change t * y = y * thL n w t
    exact Units.ext (by rw [Units.val_mul, Units.val_mul, hθv]; exact htc.2)

end GlobalTheory.NormOneProper
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCommutingTwistedConjCompactMemTwistedCentralStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normCommuting_twistedConj_compact_mem_twistedCentralizer_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : GLw n w), (nrmL n w y).val.charpoly.Separable → ∀ C : Set (GLw n w), IsCompact C → ∃ D : Set (GLw n w), IsCompact D ∧ ∀ z : GLw n w, z * nrmL n w y = nrmL n w y * z → z⁻¹ * y * thL n w z ∈ C → ∃ t ∈ twCent (thL n w) y, ∃ d ∈ D, z = t * d := by
  first | exact @GlobalTheory.NormOneProper.main | exact GlobalTheory.NormOneProper.main | (intros; apply GlobalTheory.NormOneProper.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocGLMemKglob
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.EulerTwSplit
open GlobalTheory.EulerTw GlobalTheory.EulerTwU
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem theta_mem {v w : Pl E} (f : v.adicCompletion E →+* w.adicCompletion E) (hf : ∀ x, Valued.v (f x) = Valued.v x)
    {g : GLw n v} (hg : g ∈ GlobalTheory.LFun.KGL v (n := n)) :
    thetaGL n (RingHom.id _) (GeneralLinearGroup.map f g) ∈ GlobalTheory.LFun.KGL w (n := n) := by
  have hid : GeneralLinearGroup.map (RingHom.id (w.adicCompletion E)) (GeneralLinearGroup.map f g) =
      GeneralLinearGroup.map f g := Units.ext (Matrix.ext fun _ _ => rfl)
  change PhiU n _ * invT n _ (GeneralLinearGroup.map (RingHom.id _) (GeneralLinearGroup.map f g)) * (PhiU n _)⁻¹ ∈ _
  rw [hid]
  exact mul_mem (mul_mem (GlobalTheory.ThetaSatake.phiU_mem _ n) (GlobalTheory.BCT.LocGlue.intst E n v w f hf g hg))
    (inv_mem (GlobalTheory.ThetaSatake.phiU_mem _ n))


end GlobalTheory.EulerTwSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelAtEqSumDOne
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.DelForm

variable {n : ℕ}

def dOne (f : V n → ℂ) (v : V n) : Alt n := ∑ a, del f v (coordVec a) • dz a

theorem delAt_eq_sum_dOne (β : V n → Alt n) (u : V n) :
    delAt β u = ∑ T, dOne (fun x => (bas n).repr (β x) T) u * bas n T := by
  simp only [delAt, coefwise, dOne, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  exact Finset.sum_comm

theorem delAt_congr {F G : V n → Alt n} {v : V n} (h : F =ᶠ[𝓝 v] G) : delAt F v = delAt G v := by
  unfold delAt coefwise
  refine Finset.sum_congr rfl fun a _ => congrArg _ (Finset.sum_congr rfl fun S _ => ?_)
  have e : del (fun x => (bas n).repr (F x) S) v = del (fun x => (bas n).repr (G x) S) v :=
    del_congr (h.fun_comp fun y => (bas n).repr y S)
  simp only [e]

end GlobalTheory.CxForm.DelForm
end
end
