module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasNormGroups
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexifiedDerivedActionIsLieAction
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
public import Formalism.LocalToGlobal.IndefiniteReal.BridgeSeed

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormContinuous
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem adicCompletion_trace_norm_continuous : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), Continuous f → letI := f.toAlgebra; FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) → Continuous (Algebra.trace (v.adicCompletion K) (v'.adicCompletion L)) ∧ Continuous (Algebra.norm (v.adicCompletion K) : v'.adicCompletion L → v.adicCompletion K) := by
  intro K L _ _ _ _ v v' f hf
  letI := f.toAlgebra
  intro hfd
  letI : NontriviallyNormedField (v.adicCompletion K) := Valued.toNontriviallyNormedField _ _
  haveI : CompleteSpace (v.adicCompletion K) := inferInstance
  haveI : ContinuousSMul (v.adicCompletion K) (v'.adicCompletion L) := continuousSMul_of_algebraMap _ _ hf
  refine ⟨LinearMap.continuous_of_finiteDimensional _, ?_⟩
  let b := Module.finBasis (v.adicCompletion K) (v'.adicCompletion L)
  have hn : (Algebra.norm (v.adicCompletion K) : v'.adicCompletion L → v.adicCompletion K) = fun y => (Algebra.leftMulMatrix b y).det := by
    funext y; exact Algebra.norm_eq_matrix_det b y
  rw [hn]
  have hl : Continuous (fun y => Algebra.leftMulMatrix b y) :=
    (LinearMap.continuous_of_finiteDimensional (Algebra.leftMulMatrix b).toLinearMap)
  exact hl.matrix_det

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdicCompletionTraceNormContinuousStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicCompletion_trace_norm_continuous_alt : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), Continuous f → letI := f.toAlgebra; FiniteDimensional (v.adicCompletion K) (v'.adicCompletion L) → Continuous (Algebra.trace (v.adicCompletion K) (v'.adicCompletion L)) ∧ Continuous (Algebra.norm (v.adicCompletion K) : v'.adicCompletion L → v.adicCompletion K) := by
  first | exact @GlobalTheory.adicCompletion_trace_norm_continuous | exact GlobalTheory.adicCompletion_trace_norm_continuous | (intros; apply GlobalTheory.adicCompletion_trace_norm_continuous <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermitianJmBracket
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem isHermitian_Jm_bracket {n : ℕ} (ε : Fin n → Bool) : (Jm ε).IsHermitian := by
  unfold Jm
  refine Matrix.isHermitian_diagonal_of_self_adjoint _ ?_
  funext i
  simp only [Pi.star_apply]
  split_ifs <;> simp

theorem dRep_bracket : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ w, Sm ε σ w → ∀ X ∈ lieSet ε, ∀ Y ∈ lieSet ε, dRep σ X (dRep σ Y w) - dRep σ Y (dRep σ X w) = dRep σ (X * Y - Y * X) w := by
  intro n ε H _ _ _ σ h w hw X hX Y hY
  have hd : (Jm ε).det ≠ 0 := ((isUnit_iff_isUnit_det _).1 (isUnit_Jm ε)).ne_zero
  have key := fun v (hv : Sm ε σ v) =>
    GlobalTheory.HolDict.LieAct.main n (Jm ε) H σ (isHermitian_Jm_bracket ε) hd h.1 v v hv hv
  have hB : X * Y - Y * X ∈ lieSet ε := by
    have h1 : Xᴴ * Jm ε = -(Jm ε * X) := eq_neg_of_add_eq_zero_left hX
    have h2 : Yᴴ * Jm ε = -(Jm ε * Y) := eq_neg_of_add_eq_zero_left hY
    show (X * Y - Y * X)ᴴ * Jm ε + Jm ε * (X * Y - Y * X) = 0
    rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, sub_mul, mul_assoc, mul_assoc, h1, h2,
      mul_neg, mul_neg, ← mul_assoc, ← mul_assoc, h1, h2]
    noncomm_ring
  have hXw : Sm ε σ (dRep σ X w) := dRep_mem (isUnit_Jm ε) h.1 hw hX
  have hYw : Sm ε σ (dRep σ Y w) := dRep_mem (isUnit_Jm ε) h.1 hw hY
  have e := ((key w hw).1 0 X Y).2.2
  rw [(key w hw).2.1 _ hB, (key w hw).2.1 X hX, (key w hw).2.1 Y hY, (key _ hXw).2.1 Y hY,
    (key _ hYw).2.1 X hX] at e
  exact e.symm

end GlobalTheory.TypeSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgHomFunctionFieldOfSpecializesGenericPoi
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgHomFunctionFieldOfSpecializesGenericPoi
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

theorem exists_algHom_of_specializes_genericPoint :
    ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] [Algebra F K] (q : Sp K ⟶ Y.X),
      q (IsLocalRing.closedPoint K) ⤳ genericPoint Y.X → q ≫ Y.str = spMap (algebraMap F K) →
        ∃ ψ : Y.Fn →ₐ[F] K, q = spMap ψ.toRingHom ≫ (ratOf Y).pt := by
  intro F _ Y K _ _ q h hq
  let ψ₀ : Y.Fn →+* K := (Y.X.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (R := .of K) q).hom
  have e : spMap ψ₀ ≫ (ratOf Y).pt = q := by
    change Spec.map (CommRingCat.ofHom ψ₀) ≫ Y.X.fromSpecStalk (genericPoint Y.X) = q
    rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    exact spMap_stalkClosedPointTo q
  have hc : ψ₀.comp (algebraMap F Y.Fn) = algebraMap F K := by
    have h1 : spMap (ψ₀.comp (algebraMap F Y.Fn)) = spMap (algebraMap F K) := by
      have hs := (ratOf Y).pt_s
      calc spMap (ψ₀.comp (algebraMap F Y.Fn)) = spMap ψ₀ ≫ spMap (algebraMap F Y.Fn) := by
            change Spec.map (CommRingCat.ofHom (ψ₀.comp (algebraMap F Y.Fn))) = _
            rw [CommRingCat.ofHom_comp, Spec.map_comp]
        _ = spMap ψ₀ ≫ ((ratOf Y).pt ≫ (ratOf Y).s) := by rw [hs]
        _ = (spMap ψ₀ ≫ (ratOf Y).pt) ≫ (ratOf Y).s := (Category.assoc _ _ _).symm
        _ = q ≫ Y.str := by
            change (spMap ψ₀ ≫ (ratOf Y).pt) ≫ Y.str = q ≫ Y.str
            rw [e]
            rfl
        _ = spMap (algebraMap F K) := hq
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  refine ⟨{ ψ₀ with commutes' := fun a => congrArg (fun g : F →+* K => g a) hc }, ?_⟩
  exact e.symm

end GlobalTheory.FlagBundle
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgHomFunctionFieldOfSpecializesGenericPoiStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algHom_functionField_of_specializes_genericPoint : ∀ (F : Type) [Field F] (Y : Var F) (K : Type) [Field K] [Algebra F K] (q : Sp K ⟶ Y.X), q (IsLocalRing.closedPoint K) ⤳ genericPoint Y.X → q ≫ Y.str = spMap (algebraMap F K) → ∃ ψ : Y.Fn →ₐ[F] K, q = spMap ψ.toRingHom ≫ (ratOf Y).pt := by
  first | exact @GlobalTheory.FlagBundle.exists_algHom_of_specializes_genericPoint | exact GlobalTheory.FlagBundle.exists_algHom_of_specializes_genericPoint | (intros; apply GlobalTheory.FlagBundle.exists_algHom_of_specializes_genericPoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanBasisImageAdicCompletionEqTop
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanBasisImageAdicCompletionEqTop
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem span_basis_image_adicCompletion_eq_top
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L))
    (f : v.adicCompletion K →+* v'.adicCompletion L) (hfc : Continuous f)
    (hf : ∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) :
    letI := f.toAlgebra; ∀ (n : ℕ) (b : Module.Basis (Fin n) K L),
      Submodule.span (v.adicCompletion K)
        (Set.range fun i => algebraMap L (v'.adicCompletion L) (b i)) = ⊤ := by
  letI := f.toAlgebra
  intro n b
  letI : NontriviallyNormedField (v.adicCompletion K) := Valued.toNontriviallyNormedField _ _
  set S := Submodule.span (v.adicCompletion K)
    (Set.range fun i => algebraMap L (v'.adicCompletion L) (b i)) with hS
  haveI : ContinuousSMul (v.adicCompletion K) (v'.adicCompletion L) := by
    constructor
    have : (fun p : v.adicCompletion K × v'.adicCompletion L => p.1 • p.2)
        = fun p => f p.1 * p.2 := by
      funext p; exact Algebra.smul_def _ _
    rw [this]
    exact (hfc.comp continuous_fst).mul continuous_snd
  haveI : FiniteDimensional (v.adicCompletion K) S :=
    FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have hclosed : IsClosed (S : Set (v'.adicCompletion L)) := S.closed_of_finiteDimensional
  have hmem : ∀ z : L, algebraMap L (v'.adicCompletion L) z ∈ S := by
    intro z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr z, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : algebraMap L (v'.adicCompletion L) (b.repr z i • b i)
        = (algebraMap K (v.adicCompletion K) (b.repr z i)) •
            algebraMap L (v'.adicCompletion L) (b i) := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, RingHom.algebraMap_toAlgebra, hf]
    rw [this]
    exact S.smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  have hdense := HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 L) L v'
  have hsub : Set.range (algebraMap L (v'.adicCompletion L)) ⊆ (S : Set _) := by
    rintro _ ⟨z, rfl⟩; exact hmem z
  have huniv : (S : Set (v'.adicCompletion L)) = Set.univ := by
    have := closure_minimal hsub hclosed
    rw [hdense.closure_range] at this
    exact Set.univ_subset_iff.mp this
  exact eq_top_iff.mpr fun x _ => by
    have : x ∈ (S : Set (v'.adicCompletion L)) := huniv ▸ Set.mem_univ x
    exact this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanBasisImageAdicCompletionEqTopStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_basis_image_adicCompletion_eq_top_alt : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (f : v.adicCompletion K →+* v'.adicCompletion L), Continuous f → (∀ x : K, f (algebraMap K _ x) = algebraMap L _ (algebraMap K L x)) → letI := f.toAlgebra; ∀ (n : ℕ) (b : Module.Basis (Fin n) K L), Submodule.span (v.adicCompletion K) (Set.range fun i => algebraMap L (v'.adicCompletion L) (b i)) = ⊤ := by
  first | exact @GlobalTheory.span_basis_image_adicCompletion_eq_top | exact GlobalTheory.span_basis_image_adicCompletion_eq_top | (intros; apply GlobalTheory.span_basis_image_adicCompletion_eq_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LongElementConjUnipotentRadical
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LongElementConjUnipotentRadical
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ThetaRad

theorem mem_unipRad_iff_entries {R : Type} [CommRing R] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
    {e : (Σ a, m a) ≃ n} {g : GL n R} :
    g ∈ unipRad R e ↔ ∀ i j, blk e j ≤ blk e i → (g : Matrix n n R) i j = (1 : Matrix n n R) i j := by
  rw [mem_unipRad]
  constructor
  · rintro ⟨hp, hd⟩ i j hij
    obtain ⟨⟨c, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨d, j⟩, rfl⟩ := e.surjective j
    simp only [blk_apply] at hij
    rcases hij.lt_or_eq with hlt | rfl
    · rw [mem_parab_iff.1 hp c d i j hlt, Matrix.one_apply_ne]
      intro hh
      have := congrArg Sigma.fst (e.injective hh)
      exact hlt.ne' this
    · rw [hd]
      simp only [Matrix.one_apply, e.injective.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and]
  · intro h
    refine ⟨mem_parab.2 fun i j hij => ?_, fun c i j => ?_⟩
    · rw [h i j hij.le, Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ hij
    · rw [h _ _ (by simp)]
      simp only [Matrix.one_apply, e.injective.eq_iff, Sigma.mk.inj_iff, heq_eq_eq, true_and]

theorem blk_stdBlocks_two {a b n : ℕ} (h : ∑ i, ![a, b] i = n) (p : Fin n) :
    blk (stdBlocks ![a, b] h) p = if (p : ℕ) < a then 0 else 1 := by
  obtain ⟨⟨c, i⟩, rfl⟩ := (stdBlocks ![a, b] h).surjective p
  rw [blk_apply, stdBlocks_val]
  fin_cases c
  · simpa using i.2
  · simp

theorem longElt_conj_apply {R : Type} [CommRing R] (n : ℕ) (g : GL (Fin n) R) (i j : Fin n) :
    ((longElt n R * g * longElt n R : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j =
      (g : Matrix (Fin n) (Fin n) R) i.rev j.rev := by
  simp only [longElt, Units.val_mul, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single j.rev (fun x _ hx => by rw [if_neg (fun hh => hx (by rw [hh, Fin.rev_rev])), mul_zero]) (by simp)]
  simp

end GlobalTheory.ThetaRad

theorem GlobalTheory.ThetaRad.longElt_invT_conj_mem_unipRad : ∀ (R : Type) [CommRing R] (n a b : ℕ) (h : ∑ i, ![a, b] i = n) (h' : ∑ i, ![b, a] i = n) (u : GL (Fin n) R), u ∈ unipRad R (stdBlocks ![a, b] h) → longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R ∈ unipRad R (stdBlocks ![b, a] h') := by
  intro R _ n a b h h' u hu
  have hn : a + b = n := by simpa [Fin.sum_univ_two] using h
  have hv := GlobalTheory.ThetaRad.mem_unipRad_iff_entries.1 (inv_mem hu)
  refine GlobalTheory.ThetaRad.mem_unipRad_iff_entries.2 fun i j hij => ?_
  rw [GlobalTheory.ThetaRad.longElt_conj_apply]
  change ((u⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)ᵀ i.rev j.rev = _
  rw [Matrix.transpose_apply]
  rw [hv j.rev i.rev ?_]
  · simp [Matrix.one_apply, Fin.rev_inj, eq_comm]
  · rw [GlobalTheory.ThetaRad.blk_stdBlocks_two, GlobalTheory.ThetaRad.blk_stdBlocks_two] at *
    have hi := i.2; have hj := j.2
    simp only [Fin.val_rev] at *
    split_ifs at hij ⊢ <;> first | exact le_refl _ | decide | (exfalso; omega) | (exfalso; revert hij; decide)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LongElementConjUnipotentRadicalStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.long_element_conj_unipotent_radical : ∀ (R : Type) [CommRing R] (n a b : ℕ) (h : ∑ i, ![a, b] i = n) (h' : ∑ i, ![b, a] i = n) (u : GL (Fin n) R), u ∈ unipRad R (stdBlocks ![a, b] h) → longElt n R * GlobalTheory.CuspRep.invT n R u * longElt n R ∈ unipRad R (stdBlocks ![b, a] h') := by
  first | exact @GlobalTheory.ThetaRad.longElt_invT_conj_mem_unipRad | exact GlobalTheory.ThetaRad.longElt_invT_conj_mem_unipRad | (intros; apply GlobalTheory.ThetaRad.longElt_invT_conj_mem_unipRad <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroFockVacuumOfNonzeroThetaFunction
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroFockVacuumOfNonzeroThetaFunction
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.VacReal

open GlobalTheory.ChainFr GlobalTheory.Size

theorem ptF_zero {D : D7} {V W : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : Fr V) (B : Fr W)
    (P : PolF D W.rank V.rank) : ptF ψ θ A B 0 P = 0 := by
  have hd : ∀ τ z, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z 0 = 0 := by
    intro τ z
    funext w
    simp [Formalism.IndefR.Datum.dRho, heisO]
  have : pureTensorO ψ θ V W A.cart B.cart A.onb B.onb 0 = 0 := by
    unfold pureTensorO pureTensorL
    refine (MvPolynomial.basisMonomials _ ℂ).ext fun k => ?_
    rw [Module.Basis.constr_basis]
    show opPow _ k 0 = 0
    unfold opPow
    induction Multiset.toList (Finsupp.toMultiset k) with
    | nil => rfl
    | cons a l ih => rw [List.foldr_cons, ih]; simp [aPlusAll, aPlus, crea, hd]
  unfold ptF
  rw [this]
  rfl

theorem exists_isVacF_ne_zero : ∀ (D : D7) (V W : HSp D) (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) (θ : InfFam D)
    (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsThetaFunO ψ V W f → f ≠ 0 →
      ∃ f₀, GlobalTheory.ChainFr.IsVacF ψ θ A B f₀ ∧ f₀ ≠ 0 := by
  intro D V W A B θ ψ hψ hθ f hf hf0
  by_contra hno
  push_neg at hno
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  have i6 : BorelSpace (WO V W) := ⟨rfl⟩
  obtain ⟨μ, 𝓕, hμ, h𝓕, h1⟩ :=
    (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WO V W) (ratL W V) K hK hKc).1
  obtain ⟨U, -, -, hd⟩ := GlobalTheory.T.fockVectors_overVacua_dense_thetaFunctions D V W A B θ ψ hψ hθ μ 𝓕 ⟨hμ, h𝓕, h1⟩ f hf
  have hspan : fockSpan ψ θ A B U = ⊥ := by
    unfold fockSpan
    rw [Submodule.span_eq_bot]
    rintro g ⟨f₀, P, hv, -, rfl⟩
    rw [hno f₀ hv]
    exact ptF_zero ψ θ A B P
  have hl : l2O μ 𝓕 f = 0 := by
    by_contra hne
    obtain ⟨g, hg, -, hlt⟩ := hd 0 (l2O μ 𝓕 f) (pos_iff_ne_zero.2 hne)
    rw [hspan, Submodule.mem_bot] at hg
    rw [hg, sub_zero] at hlt
    have e : sobO ψ θ μ 𝓕 0 f = l2O μ 𝓕 f := wordSum_zero _ _ _
    rw [e] at hlt
    exact lt_irrefl _ hlt
  have h0 : ∀ᵐ x ∂μ.restrict 𝓕, f x = 0 :=
    (eLpNorm_eq_zero_iff two_ne_zero).1 hl
  exact hf0 (GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratL W V) μ 𝓕 h𝓕 f hf.cont
    (GlobalTheory.WeilVacMove.norm_periodic hψ hf) h0)

end GlobalTheory.Mem.VacReal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNonzeroFockVacuumOfNonzeroThetaFunctionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_fockVacuum_of_nonzero_thetaFunction : ∀ (D : D7) (V W : HSp D) (A : GlobalTheory.ChainFr.Fr V) (B : GlobalTheory.ChainFr.Fr W) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → IsInfFam θ → ∀ f, IsThetaFunO ψ V W f → f ≠ 0 → ∃ f₀, GlobalTheory.ChainFr.IsVacF ψ θ A B f₀ ∧ f₀ ≠ 0 := by
  first | exact @GlobalTheory.Mem.VacReal.exists_isVacF_ne_zero | exact GlobalTheory.Mem.VacReal.exists_isVacF_ne_zero | (intros; apply GlobalTheory.Mem.VacReal.exists_isVacF_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunctionFieldIntegralModelExistsIsHomOfMapLocalR
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunctionFieldIntegralModelExistsIsHomOfMapLocalR
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open ReciprocityTheory.ChartRestriction.G GlobalTheory.Points
open Classical

noncomputable section
namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

def constHom (M : RatModel o Ω) (U : M.Z.Opens) : o →+* Γ(M.Z, U) :=
  (M.s.appLE ⊤ U (fun _ _ => trivial)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom

theorem finiteType_constHom (M : RatModel o Ω) {U : M.Z.Opens} (hU : IsAffineOpen U) :
    (M.constHom U).FiniteType := by
  have := M.lft
  have h1 : (M.s.appLE ⊤ U (fun _ _ => trivial)).hom.FiniteType :=
    M.s.finiteType_appLE (isAffineOpen_top _) hU _
  have h2 : (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom.FiniteType :=
    RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of o)).symm.commRingCatIsoToRingEquiv.surjective
  exact h1.comp h2

variable {Ω' : Type} [Field Ω'] [Algebra o Ω']

theorem exists_nbhd_of_map_O (M : RatModel o Ω) (M' : RatModel o Ω') (φ : Ω →ₐ[o] Ω') {z' : M'.Z} {z : M.Z}
    (hz : ∀ a ∈ M.O z, φ a ∈ M'.O z') :
    ∃ (V : M'.Z.Opens) (U : M.Z.Opens), z' ∈ V ∧ IsAffineOpen U ∧ (U : Set M.Z).Nonempty ∧
      ∀ x ∈ M.ringOn U, φ x ∈ M'.ringOn V := by
  obtain ⟨U, hU, hzU, -⟩ := exists_isAffineOpen_mem_and_subset (U := (⊤ : M.Z.Opens)) (x := z) trivial
  have hUne : (U : Set M.Z).Nonempty := ⟨z, hzU⟩
  letI := (M.constHom U).toAlgebra
  obtain ⟨s, hs⟩ := (M.finiteType_constHom hU).out
  let V : M'.Z.Opens := ⟨⋂ f ∈ s, {w | φ (valF M.pt U f) ∈ M'.O w},
    isOpen_biInter_finset fun f _ => M'.isOpen_setOf_mem_O _⟩
  have hzV : z' ∈ V := Set.mem_iInter₂.2 fun f _ => hz _ (valF_mem_O hzU f)
  have hsV : ∀ f ∈ s, φ (valF M.pt U f) ∈ M'.ringOn V := fun f hf =>
    mem_ringOn.2 fun w hw => Set.mem_iInter₂.1 hw f hf
  have key : ∀ f : Γ(M.Z, U), φ (valF M.pt U f) ∈ M'.ringOn V := by
    intro f
    have hf : f ∈ Algebra.adjoin o (s : Set Γ(M.Z, U)) := hs ▸ Algebra.mem_top
    induction hf using Algebra.adjoin_induction with
    | mem x hx => exact hsV x hx
    | algebraMap r =>
      have e : valF M.pt U (algebraMap o Γ(M.Z, U) r) = algebraMap o Ω r := M.valF_constFn hUne r
      rw [e, AlgHom.commutes]
      exact Subalgebra.algebraMap_mem _ r
    | add x y _ _ hx hy =>
      rw [← M.res_apply U hUne, map_add (f := _), map_add (f := _), res_apply, res_apply]
      exact add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [← M.res_apply U hUne, map_mul, map_mul, res_apply, res_apply]
      exact mul_mem hx hy
  refine ⟨V, U, hzV, hU, hUne, fun x hx => ?_⟩
  obtain ⟨f, rfl⟩ := (mem_ringOn_iff_exists hUne).1 hx
  exact key f

theorem exists_isHom_of_map_O :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω']
      (M' : RatModel o Ω') (φ : Ω →ₐ[o] Ω'), (∀ z' : M'.Z, ∃ z : M.Z, ∀ a ∈ M.O z, φ a ∈ M'.O z') →
        ∃ f : M'.Z ⟶ M.Z, M.IsHom M' φ f := by
  intro o Ω _ _ _ M Ω' _ _ M' φ h
  refine exists_isHom_of_local fun z' => ?_
  obtain ⟨z, hz⟩ := h z'
  exact exists_nbhd_of_map_O M M' φ hz

end GlobalTheory.ZH.RatModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FunctionFieldIntegralModelExistsIsHomOfMapLocalRStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.functionFieldIntegralModel_exists_isHom_of_map_localRing : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (M' : RatModel o Ω') (φ : Ω →ₐ[o] Ω'), (∀ z' : M'.Z, ∃ z : M.Z, ∀ a ∈ M.O z, φ a ∈ M'.O z') → ∃ f : M'.Z ⟶ M.Z, M.IsHom M' φ f := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isHom_of_map_O | exact GlobalTheory.ZH.RatModel.exists_isHom_of_map_O | (intros; apply GlobalTheory.ZH.RatModel.exists_isHom_of_map_O <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipRadStdBlocksTwoNeBot
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipRadStdBlocksTwoNeBot
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem unipRad_stdBlocks_two_ne_bot : ∀ (R : Type) [CommRing R] [Nontrivial R] (n a b : ℕ) (h : ∑ i, ![a, b] i = n), 0 < a → 0 < b → unipRad R (stdBlocks ![a, b] h) ≠ ⊥ := by
  intro R _ _ n a b h ha hb
  set e := stdBlocks ![a, b] h with he
  let i : Fin n := e ⟨0, ⟨0, by simpa using ha⟩⟩
  let j : Fin n := e ⟨1, ⟨0, by simpa using hb⟩⟩
  have hij : i ≠ j := by
    intro hh
    have := congrArg Sigma.fst (e.injective hh)
    simp at this
  let g : GL (Fin n) R :=
    ⟨Matrix.transvection i j 1, Matrix.transvection i j (-1),
      by
        show Matrix.transvection i j (1 : R) * Matrix.transvection i j (-1) = 1
        rw [Matrix.transvection_mul_transvection_same i j hij]; simp,
      by
        show Matrix.transvection i j (-1 : R) * Matrix.transvection i j 1 = 1
        rw [Matrix.transvection_mul_transvection_same i j hij]; simp⟩
  have hg : (g : Matrix (Fin n) (Fin n) R) = 1 + Matrix.single i j 1 := rfl
  have hmem : g ∈ unipRad R e := by
    rw [mem_unipRad]
    refine ⟨?_, ?_⟩
    · rw [mem_parab]
      intro p q hpq
      have hne : p ≠ q := by rintro rfl; exact lt_irrefl _ hpq
      rw [hg, Matrix.add_apply, Matrix.one_apply_ne hne, zero_add]
      by_cases hp : p = i
      · by_cases hq : q = j
        · subst hp; subst hq
          rw [blk_apply, blk_apply] at hpq
          exact absurd hpq (by decide)
        · rw [Matrix.single_apply, if_neg]
          rintro ⟨_, h'⟩; exact hq h'.symm
      · rw [Matrix.single_apply, if_neg]
        rintro ⟨h', _⟩; exact hp h'.symm
    · intro c x y
      rw [hg, Matrix.add_apply]
      have h1 : (1 : Matrix (Fin n) (Fin n) R) (e ⟨c, x⟩) (e ⟨c, y⟩) = (1 : Matrix _ _ R) x y := by
        by_cases hxy : x = y
        · subst hxy; simp
        · rw [Matrix.one_apply_ne, Matrix.one_apply_ne hxy]
          intro hh
          have := e.injective hh
          simp at this
          exact hxy this
      rw [h1]
      have h2 : Matrix.single i j (1 : R) (e ⟨c, x⟩) (e ⟨c, y⟩) = 0 := by
        rw [Matrix.single_apply]
        split_ifs with hh
        · obtain ⟨h3, h4⟩ := hh
          have e3 := congrArg Sigma.fst (e.injective h3)
          have e4 := congrArg Sigma.fst (e.injective h4)
          simp only at e3 e4
          rw [← e3] at e4
          exact absurd e4 (by decide)
        · rfl
      rw [h2, add_zero]
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hmem
  have := congrArg (fun u : GL (Fin n) R => (u : Matrix (Fin n) (Fin n) R) i j) hmem
  simp [hg, Matrix.one_apply_ne hij] at this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnipRadStdBlocksTwoNeBotStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipRad_stdBlocks_two_ne_bot' : ∀ (R : Type) [CommRing R] [Nontrivial R] (n a b : ℕ) (h : ∑ i, ![a, b] i = n), 0 < a → 0 < b → unipRad R (stdBlocks ![a, b] h) ≠ ⊥ := by
  first | exact @GlobalTheory.unipRad_stdBlocks_two_ne_bot | exact GlobalTheory.unipRad_stdBlocks_two_ne_bot | (intros; apply GlobalTheory.unipRad_stdBlocks_two_ne_bot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeedAtReadingKeeping
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeedChoices

set_option maxHeartbeats 1000000 in
theorem seed_at_reading_keeping : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (F : Face3 D A3) (L : LevCh D T) (eG : G ≃* G0 L.Pg D.R.r) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T) (twPl : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) (ψ : AddChar (AF D.host.F) ℂ) (MW : ∀ i σ, DSModel (Wc D i) (parAt (Wc D i) σ)), L.Is A3.A.μ0 → Seed.TupL A3 L mu twPl → Seed.RecL A3 L eG → Seed.LevelsL A3 L eG F.lv2 → Seed.ModY D → Seed.ModWAt D.what₂.embLL MW → Seed.VPos D → IsStdChar D ψ (-1) → ∀ Qb : ∀ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)), (∀ t, A3.A.fam.amb.FR t → Bridge.Gf D.sp.X' → cX.W) → (∀ i t, A3.A.fam.amb.FL i t → Bridge.Gf (Vc D i) → (cV i).W) → Prop, (∀ θ : InfFam D, IsInfFam θ → ∀ MX : DSModel D.sp.X' (parB (Ptw D) D.R.m), ∃ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)) (pl : Pl0 → Pl D.host.E) (Sb : Finset (Pl D.host.E)) (B : Seed.BType A3 L cX cV pl) (plI : I0 → Pl D.host.E) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ), cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ Seed.PrIso MX cX prX ∧ Seed.BrgL A3 L eG cX cV pl Sb B plI SF ∧ Qb cX cV (fun t φ => B.jR t φ) fun i t φ => B.jL i t φ) → ∃ R : RealDat3 D A3 Ks, R.toRealDat.toLevCh = L ∧ R.ψ = ψ ∧ R.MW = MW ∧ HEq R.eG eG ∧ R.mu = mu ∧ R.twPl = twPl ∧ Seed.PrIso R.MX R.cX R.prX ∧ R.toRealDat.Pre0 F.lv2 ∧ R.IsInert ∧ R.IsTup ∧ R.AllPlaces ∧ Qb R.cX R.cV (fun t φ => R.B.jR t φ) fun i t φ => R.B.jL i t φ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ F L eG mu twPl ψ MW hL hmu hrec hlev hY hMW hV hψ Qb hB
  obtain ⟨θ, hθ⟩ := Formalism.IndefR.Eqv.infFamExists_holds D
  obtain ⟨hMY, ⟨MX⟩⟩ := hY
  let MY := fun j => (hMY j).some
  obtain ⟨cX, cV, pl, Sb, B, plI, SF, prX, hcX, hcV, hpr, hPr, hb, hQ⟩ := hB θ hθ MX
  obtain ⟨gramR, c0R, c0L, htie⟩ := hb.tie
  have hMW' : Seed.ModWAt (D := D) (sg0 D A3.A) MW := by
    rw [show sg0 D A3.A = D.what₂.embLL from sgAt_mk _ htie.v0]; exact hMW
  let R : RealDat D A3.A Ks :=
    { toLevCh := L
      hv0 := htie.v0
      eG := eG
      pl := pl
      Sb := Sb
      θ := θ
      ψ := ψ
      MY := MY
      MX := MX
      MW := MW
      cX := cX
      cV := cV
      B := B
      prX := prX
      HX := fun _ => Seed.hZ _
      HV := fun _ _ => Seed.hZ _
      HE := Seed.hZ _
      HW := fun _ _ => Seed.hZ _
      gE := 1
      gW := fun _ _ => 1
      jX := fun _ => 0
      jV := fun _ _ => 0
      νY := fun _ _ => 0
      fdY := fun _ _ => ∅
      ν0 := 0
      fd0 := ∅
      νX := fun _ => 0
      fdX := fun _ => ∅
      νV := fun _ _ => 0
      fdV := fun _ _ => ∅
      νW := fun _ => 0
      fdW := fun _ => ∅
      ωY := fun _ _ => 1
      ωX := fun _ => 1
      ωP := fun _ _ => 1
      vac := fun _ => 0
      vacX := 0
      vacP := fun _ => 0
      vY := fun _ _ => 0
      vX := fun _ => 0
      vP := fun _ _ => 0
      ItY := fun _ => 0
      ItX := 0
      ioY := fun _ _ => 0
      ioX := fun _ => 0
      Th := fun _ => 0
      BV := fun _ _ => 0
      ioP := fun _ => 0
      thF := fun _ _ => 0
      thG := fun _ _ => 0
      nW := fun _ => 0
      FW := fun _ =>
        { WK := ⊥
          Pt := fun _ => PEmpty
          nrm := fun _ y _ => PEmpty.elim y
          nrm_nonneg := fun _ y _ => PEmpty.elim y
          nrm_zero := fun _ y => PEmpty.elim y
          nrm_add := fun _ y _ _ => PEmpty.elim y
          nrm_smul := fun _ y _ _ => PEmpty.elim y
          towKs := inferInstance
          ρ := 1
          chi := 1
          j := fun _ => 0 }
      mu := mu
      twPl := twPl
      kap := 0
      lam := fun _ _ _ _ => 0
      err0 := fun _ _ => 0 }
  refine ⟨{ toRealDat := R, plI := plI, SF := SF, lam3 := fun _ _ _ _ => 0, phs := fun _ => 1 }, rfl, rfl, rfl, HEq.rfl, rfl, rfl,
    hPr, ?_, ?_, ?_, hb.sb, hQ⟩
  · have hsub : L.Pg ⊆ Sb := by rw [hb.sb]
    exact ⟨hL, hb.red_R, hb.red_L, hlev, hrec, ⟨⟨gramR, c0R, c0L, htie⟩, hsub, hb.roots, hb.pl_onto, hb.degR, hb.degL, hb.muVal,
      hb.etaVal⟩, hθ, hV, hcX, hcV, hpr, hMW', hψ⟩
  · exact ⟨hb.in_tie, hb.in_onto, hb.in_R, hb.in_L, hb.in_SF⟩
  · exact ⟨hmu.1, hmu.2.1, hmu.2.2.1, hmu.2.2.2.1, hmu.2.2.2.2⟩

end GlobalTheory.SeedChoices
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WhittakerFunctionalTorusValuationBound
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WhittakerFunctionalTorusValuationBound
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Topology

noncomputable section
namespace GlobalTheory.RootUp

variable {k : Type} [Field k]

theorem single_sq {n : ℕ} {i j : Fin n} (h : i ≠ j) (y : k) :
    Matrix.single i j y * Matrix.single i j y = 0 := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.single_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  split_ifs with h1 h2 <;> first | rfl | exact absurd (h2.2.trans h1.1.symm) h.symm | exact absurd (h2.1.trans h1.2.symm) h | simp

def elem {n : ℕ} {i j : Fin n} (h : i ≠ j) (y : k) : GL (Fin n) k :=
  ⟨1 + Matrix.single i j y, 1 - Matrix.single i j y, by
    rw [add_mul, one_mul, mul_sub, mul_one, single_sq h]; abel,
   by
    rw [sub_mul, one_mul, mul_add, mul_one, single_sq h]; abel⟩

theorem val_elem {n : ℕ} {i j : Fin n} (h : i ≠ j) (y : k) :
    (elem h y : Matrix (Fin n) (Fin n) k) = 1 + Matrix.single i j y := rfl

theorem continuous_elem [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    Continuous (elem (k := k) h) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun a b => ?_
    simp only [Function.comp_apply, val_elem, Matrix.add_apply, Matrix.single_apply]
    split_ifs <;> fun_prop
  · refine continuous_matrix fun a b => ?_
    show Continuous fun y => (1 - Matrix.single i j y : Matrix (Fin n) (Fin n) k) a b
    simp only [Matrix.sub_apply, Matrix.single_apply]
    split_ifs <;> fun_prop

theorem val_conj_elem {n : ℕ} (t : Fin n → kˣ) {i j : Fin n} (h : i ≠ j) (y : k) :
    ((diagT k (Fin n) t * elem h y * (diagT k (Fin n) t)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      1 + Matrix.single i j ((t i : k) / t j * y) := by
  rw [← map_inv, Units.val_mul, Units.val_mul, val_diagT, val_diagT, val_elem]
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Pi.inv_apply]
  by_cases hab : a = b
  · subst hab
    have : ¬ (i = a ∧ j = a) := fun h' => h (h'.1.trans h'.2.symm)
    simp [this]
  · by_cases hh : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hh
      simp [hab]
      field_simp
    · simp [hab, hh]

theorem elem_conj_mem {n : ℕ} (t : Fin n → kˣ) {i j : Fin n} (hij : i < j) (y : k) :
    diagT k (Fin n) t * elem hij.ne y * (diagT k (Fin n) t)⁻¹ ∈ unipB k (Fin n) := by
  refine (mem_unipB k).2 ⟨fun a b hba => ?_, fun a => ?_⟩
  · rw [val_conj_elem]
    have hab : a ≠ b := (ne_of_lt hba).symm
    have : ¬ (i = a ∧ j = b) := by
      rintro ⟨rfl, rfl⟩; exact absurd hij (not_lt.2 hba.le)
    simp [Matrix.one_apply, Matrix.single_apply, hab, this]
  · rw [val_conj_elem]
    have : ¬ (i = a ∧ j = a) := fun h' => hij.ne (h'.1.trans h'.2.symm)
    simp [Matrix.single_apply, this]

theorem superDiag_conj_elem {n : ℕ} (t : Fin n → kˣ) {i j : Fin n} (hij : j.val = i.val + 1) (hne : i ≠ j) (y : k) :
    superDiag (diagT k (Fin n) t * elem hne y * (diagT k (Fin n) t)⁻¹) = (t i : k) / t j * y := by
  rw [superDiag, val_conj_elem]
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [Matrix.one_apply, hne]
    · intro b hb hbj
      have hib : i ≠ b := by
        rintro rfl; simp at hb
      simp [Matrix.one_apply, Matrix.single_apply, hib, Ne.symm hbj]
    · intro hj; simp [hij] at hj
  · intro a _ hai
    refine Finset.sum_eq_zero fun b hb => ?_
    have hab : a ≠ b := by
      rintro rfl; simp at hb
    simp [Matrix.one_apply, Matrix.single_apply, hab, Ne.symm hai]
  · simp

theorem whittaker_torus_root_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V), IsSmooth ρ → ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l → ∀ x : V, ∃ r : kˣ, ∀ (t : Fin n → kˣ) (i j : Fin n), j.val = i.val + 1 → l (ρ (diagT k (Fin n) t) x) ≠ 0 → valuation k ((t i : k) / t j) ≤ valuation k (r : k) := by
  intro k _ _ _ _ ψ hψ hψ1 n V _ _ ρ hρ l hl x
  obtain ⟨c, hc⟩ := exists_hasConductor_of_continuous ψ hψ hψ1
  have hU : {g : GL (Fin n) k | ρ g x = x} ∈ 𝓝 (1 : GL (Fin n) k) := (hρ x).mem_nhds (by simp)
  have hall : ∀ᶠ y in 𝓝 (0 : k), ∀ i j : Fin n, ∀ h : i ≠ j, ρ (elem h y) x = x := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
      Filter.eventually_all.2 fun h => ?_
    have hc0 : elem h (0 : k) = 1 := Units.ext (by simp [val_elem])
    exact (continuous_elem h).continuousAt.preimage_mem_nhds (by rw [hc0]; exact hU)
  obtain ⟨s, hs⟩ := exists_cball_subset hall
  refine ⟨c * s⁻¹, fun t i j hij hne0 => ?_⟩
  have hlt : i < j := by rw [Fin.lt_iff_val_lt_val]; omega
  have key : ∀ y ∈ cball s, ψ (y * ((t i : k) / t j)) = 1 := by
    intro y hy
    have hfix : ρ (elem hlt.ne y) x = x := hs hy i j hlt.ne
    have h1 := hl _ (elem_conj_mem t hlt y) (ρ (diagT k (Fin n) t) x)
    rw [superDiag_conj_elem t hij hlt.ne, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right,
      map_mul, Module.End.mul_apply, hfix] at h1
    have h2 : ((ψ ((t i : k) / t j * y) : Circle) : ℂ) = 1 := (mul_eq_right₀ hne0).1 h1.symm
    rw [mul_comm]
    exact Circle.coe_eq_one.1 h2
  by_contra hv
  obtain ⟨y, hy, hne⟩ := hc.exists_ne_one s (x := (t i : k) / t j) hv
  exact hne (key y hy)
end GlobalTheory.RootUp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WhittakerFunctionalTorusValuationBoundStatement
open NumberField IsDedekindDomain ValuativeRel Matrix MeasureTheory TensorProduct Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Whittaker GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocDict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_functional_torus_valuation_bound : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin n) k) V), IsSmooth ρ → ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l → ∀ x : V, ∃ r : kˣ, ∀ (t : Fin n → kˣ) (i j : Fin n), j.val = i.val + 1 → l (ρ (diagT k (Fin n) t) x) ≠ 0 → valuation k ((t i : k) / t j) ≤ valuation k (r : k) := by
  first | exact @GlobalTheory.RootUp.whittaker_torus_root_bound | exact GlobalTheory.RootUp.whittaker_torus_root_bound | (intros; apply GlobalTheory.RootUp.whittaker_torus_root_bound <;> assumption)
end
end
