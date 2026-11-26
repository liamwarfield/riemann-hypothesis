module

public import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapTop
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import GroundTheory.AutomorphicForms.AnisotropicUnitaryCompact
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
public import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHecke

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactStandardMaximal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactStandardMaximal
noncomputable section

namespace GlobalTheory.CompanionTheory.StdK

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_intBasis : ∃ b : Module.Basis (Fin (Module.finrank F E)) F E, ∀ i, IsIntegral ℤ (b i) := by
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have h : ∀ x : E, ∃ m : ℤ, m ≠ 0 ∧ IsIntegral ℤ (m • x) := fun x => by
    obtain ⟨m, hm, hi⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).2
      (Algebra.IsAlgebraic.isAlgebraic x)).exists_integral_multiple
    exact ⟨m, hm, hi⟩
  choose m hm hi using h
  let b := Module.finBasis F E
  let u : Fin (Module.finrank F E) → Fˣ := fun i => Units.mk0 (m (b i) : F) (by exact_mod_cast hm _)
  refine ⟨b.unitsSMul u, fun i => ?_⟩
  rw [Module.Basis.unitsSMul_apply]
  have e : u i • b i = m (b i) • b i := by
    change ((m (b i) : F)) • b i = _
    exact Int.cast_smul_eq_zsmul F _ _
  rw [e]
  exact hi _

theorem isOpen_intAd : IsOpen {a : AF F | ∀ v, evFin F v a ∈ v.adicCompletionIntegers F} := by
  have h : IsOpen {f : FiniteAdeleRing (𝓞 F) F | ∀ v, f v ∈ v.adicCompletionIntegers F} :=
    RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)
  exact h.preimage continuous_snd

theorem evFin_finOne (v : HeightOneSpectrum (𝓞 F)) : evFin F v (finOne F) = 1 := rfl

theorem evI_finOne_mul (a : AF F) : evI F (finOne F * a) = 0 := by
  have e : (finOne F * a).1 = 0 := by
    change (0 : Ainf F) * a.1 = 0
    exact zero_mul _
  unfold evI
  rw [e, map_zero]


variable (F E) in
def finInt : AddSubgroup (AE F E) :=
  (intHat F E).comap (DistribSMul.toAddMonoidHom (AE F E) (finOne F))

theorem mem_finInt {z : AE F E} : z ∈ finInt F E ↔ finOne F • z ∈ intHat F E := Iff.rfl

theorem smul_incl_mem_finInt {a : AF F} (ha : ∀ v, evFin F v a ∈ v.adicCompletionIntegers F) (o : 𝓞 E) :
    a • inclR (F := F) (E := E) (AF F) (o : E) ∈ finInt F E := by
  rw [mem_finInt, smul_smul]
  refine AddSubgroup.subset_closure ⟨finOne F * a, evI_finOne_mul a, fun v => ?_, o, rfl⟩
  rw [map_mul, evFin_finOne, one_mul]
  exact ha v

theorem isOpen_finInt : IsOpen (finInt F E : Set (AE F E)) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨b, hb⟩ := exists_intBasis (F := F) (E := E)
  let e := (Algebra.TensorProduct.basis (AF F) b).equivFun
  have he : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hS : IsOpen {z : AE F E | ∀ i, ∀ v, evFin F v (e z i) ∈ v.adicCompletionIntegers F} := by
    have e0 : {z : AE F E | ∀ i, ∀ v, evFin F v (e z i) ∈ v.adicCompletionIntegers F} =
        ⋂ i, (fun z => e z i) ⁻¹' {a : AF F | ∀ v, evFin F v a ∈ v.adicCompletionIntegers F} := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [e0]
    exact isOpen_iInter_of_finite fun i => (isOpen_intAd (F := F)).preimage ((continuous_apply i).comp he)
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0) (Filter.mem_of_superset (hS.mem_nhds ?_) ?_)
  · intro i v
    simp
  · intro z hz
    have e1 : z = ∑ i, e z i • (Algebra.TensorProduct.basis (AF F) b i) :=
      ((Algebra.TensorProduct.basis (AF F) b).sum_equivFun z).symm
    rw [e1]
    refine sum_mem fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply]
    exact smul_incl_mem_finInt (hz i) ⟨b i, hb i⟩

theorem isClosed_finInt : IsClosed (finInt F E : Set (AE F E)) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact AddSubgroup.isClosed_of_isOpen _ isOpen_finInt

theorem compFin_finOne_smul (v : HeightOneSpectrum (𝓞 F)) (z : AE F E) :
    compFin F E v (finOne F • z) = compFin F E v z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]
  | tmul a e =>
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    simp [compFin, map_mul, evFin_finOne]

theorem absFin_le_one_of_mem {z : AE F E} (hz : z ∈ intHat F E) (v : HeightOneSpectrum (𝓞 F)) :
    absFin F v (compFin F E v z) ≤ 1 := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, -, ha, o, rfl⟩ := hz
    have e : compFin F E v (a • inclR (F := F) (E := E) (AF F) (o : E)) = evFin F v a ⊗ₜ[F] (o : E) := by
      simp [compFin, inclR, TensorProduct.smul_tmul']
    rw [e]
    refine (absFin_tmul_le F v _ o).trans ?_
    exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 (ha v)
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]
    exact (absFin_add_le F v _ _).trans (max_le hx hy)
  | neg x _ hx =>
    rw [map_neg, absFin_neg]
    exact hx

theorem opNorm_le_one {ι : Type} [Fintype ι] [DecidableEq ι] {M : Matrix ι ι ℂ} (h : M * Mᴴ = 1) : opNorm M ≤ 1 := by
  have e : Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M * star (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M) = 1 := by
    rw [← map_star, ← map_mul, Matrix.star_eq_conjTranspose, h, map_one]
  have h2 := CStarRing.norm_self_mul_star (x := Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M)
  rw [e] at h2
  have h3 : ‖(1 : EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have h4 := norm_nonneg (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M)
  change ‖Matrix.toEuclideanCLM (n := ι) (𝕜 := ℂ) M‖₊ ≤ 1
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]
  nlinarith

variable {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem heightGL_eq_one {ι : Type} [Fintype ι] [DecidableEq ι] (B : Base F E) (hcm : IsCMExt F E σ)
    (g : GL ι (AE F E)) (hu : ∀ w, (g.1.map (piInf (B.emb w))) * (g.1.map (piInf (B.emb w)))ᴴ = 1)
    (hf : ∀ i j, g.1 i j ∈ finInt F E) (hf' : ∀ i j, (g⁻¹).1 i j ∈ finInt F E) : heightGL F g = 1 := by
  rw [heightGL_eq_one_iff]
  refine ⟨fun w => htOf_eq_one.2 ⟨?_, ?_⟩, fun v => htOf_eq_one.2 ⟨?_, ?_⟩⟩
  · rw [normInf_eq_opNorm hcm (B.emb w)]
    exact opNorm_le_one (hu w)
  · rw [normInf_eq_opNorm hcm (B.emb w), ← map_inv]
    change opNorm ((g⁻¹).1.map (piInf (B.emb w))) ≤ 1
    have hM : g.1.map (piInf (B.emb w)) * (g⁻¹).1.map (piInf (B.emb w)) = 1 := by
      rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
    have h1 := mul_eq_one_comm.1 (hu w)
    have h2 : (g⁻¹).1.map (piInf (B.emb w)) = (g.1.map (piInf (B.emb w)))ᴴ := by
      calc _ = (g.1.map (piInf (B.emb w)))ᴴ * g.1.map (piInf (B.emb w)) * (g⁻¹).1.map (piInf (B.emb w)) := by
            rw [h1, Matrix.one_mul]
        _ = _ := by rw [Matrix.mul_assoc, hM, Matrix.mul_one]
    rw [h2]
    exact opNorm_le_one (by rw [Matrix.conjTranspose_conjTranspose]; exact h1)
  · refine (normFin_le_iff F v).2 fun i j => ?_
    change absFin F v (compFin F E v (g.1 i j)) ≤ 1
    rw [← compFin_finOne_smul]
    exact absFin_le_one_of_mem (hf i j) v
  · refine (normFin_le_iff F v).2 fun i j => ?_
    rw [← map_inv]
    change absFin F v (compFin F E v ((g⁻¹).1 i j)) ≤ 1
    rw [← compFin_finOne_smul]
    exact absFin_le_one_of_mem (hf' i j) v

theorem isCompact_of_isStdK (B : Base F E) (hcm : IsCMExt F E σ) (b : GL (Fin n ⊕ Fin n) E)
    (K : Subgroup (G2 σ Y)) (hK : IsStdK (σ := σ) (Y := Y) B b K) : IsCompact (K : Set (G2 σ Y)) := by
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  let bA : GL (Fin n ⊕ Fin n) (AE F E) := Formalism.UG.bc (inclR (F := F) (E := E) (AF F)) b
  let m : G2 σ Y → GL (Fin n ⊕ Fin n) (AE F E) := fun x => bA⁻¹ * x.1 * bA
  have hm : ∀ x, (m x).1 = inFrame b x := fun x => rfl
  have hv : Continuous fun x : G2 σ Y => (x.1.1 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :=
    Units.continuous_val.comp continuous_subtype_val
  have hfr : Continuous fun x : G2 σ Y => inFrame b x := (continuous_const.matrix_mul hv).matrix_mul continuous_const
  have hfi : Continuous fun x : G2 σ Y => inFrame b x⁻¹ := hfr.comp continuous_inv
  have hcl : IsClosed (K : Set (G2 σ Y)) := by
    have e1 : (K : Set (G2 σ Y)) = (⋂ w, {k : G2 σ Y | (inFrame b k).map (piInf (B.emb w)) *
          ((inFrame b k).map (piInf (B.emb w)))ᴴ = 1}) ∩
        ((⋂ i, ⋂ j, (fun k : G2 σ Y => inFrame b k i j) ⁻¹' (finInt F E : Set (AE F E))) ∩
          ⋂ i, ⋂ j, (fun k : G2 σ Y => inFrame b k⁻¹ i j) ⁻¹' (finInt F E : Set (AE F E))) := by
      ext k
      simp only [SetLike.mem_coe, hK k, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq, Set.mem_preimage,
        Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq, mem_finInt]
    rw [e1]
    refine (isClosed_iInter fun w => isClosed_eq ?_ continuous_const).inter
      ((isClosed_iInter fun i => isClosed_iInter fun j => isClosed_finInt.preimage ?_).inter
        (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_finInt.preimage ?_))
    · have h := hfr.matrix_map (GlobalTheory.ContMapReal.continuous_piInf (B.emb w))
      exact h.matrix_mul h.matrix_conjTranspose
    · exact (continuous_apply j).comp ((continuous_apply i).comp hfr)
    · exact (continuous_apply j).comp ((continuous_apply i).comp hfi)
  have hσ : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hUG : IsClosed (UG (cA σ) (dbl (incM F Y.J)) : Set (GL (Fin n ⊕ Fin n) (AE F E))) := by
    have hg : Continuous fun g : GL (Fin n ⊕ Fin n) (AE F E) => (g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (AE F E)) :=
      Units.continuous_val
    exact isClosed_eq ((hg.matrix_transpose.matrix_mul continuous_const).matrix_mul (hg.matrix_map hσ)) continuous_const
  have hC := hUG.isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_heightGL_le (E := E) (n := Fin n ⊕ Fin n) F (heightGL F bA * heightGL F bA⁻¹))
  refine hC.of_isClosed_subset hcl fun k hk => ?_
  obtain ⟨hu, hf⟩ := (hK k).1 hk
  have hinv : (m k)⁻¹ = m k⁻¹ := by
    change (bA⁻¹ * k.1 * bA)⁻¹ = bA⁻¹ * (k.1)⁻¹ * bA
    group
  have h1 : heightGL F (m k) = 1 := heightGL_eq_one B hcm (m k) hu
    (fun i j => mem_finInt.2 (hf k (by simp) i j))
    (fun i j => by
      rw [hinv]
      exact mem_finInt.2 (hf k⁻¹ (by simp) i j))
  have e2 : k.1 = bA * m k * bA⁻¹ := by
    change k.1 = bA * (bA⁻¹ * k.1 * bA) * bA⁻¹
    group
  change heightGL F k.1 ≤ _
  rw [e2]
  refine (heightGL_mul_le F _ _).trans ?_
  rw [(heightGL_mul_of_eq_one F h1 bA).1]

theorem isCompact_K : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → IsCompact (K : Set (G2 σ Y)) := by
  intro F E _ _ _ _ _ σ B n Y r s hB _ _ b K a _ hK _
  exact isCompact_of_isStdK B hB.cm b K hK

end GlobalTheory.CompanionTheory.StdK

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCompactStandardMaximalStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_standard_maximal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → IsCompact (K : Set (G2 σ Y)) := by
  first | exact @GlobalTheory.CompanionTheory.StdK.isCompact_K | exact GlobalTheory.CompanionTheory.StdK.isCompact_K | (intros; apply GlobalTheory.CompanionTheory.StdK.isCompact_K <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipMinSubsetMinParOne
set_option linter.unusedSectionVars false

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.ParCocompact

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def rowOf (C : Matrix (Fin n) (Fin r) E) (i : Fin r) : Fin n → E := (cT (σ : E →+* E) C * J) i

def lineProj (C D : Matrix (Fin n) (Fin r) E) (i : Fin r) : Matrix (Fin n) (Fin n) E :=
  Matrix.vecMulVec (fun k => C k i) (rowOf σ J D i)

def projFam (X Y : Matrix (Fin n) (Fin r) E) : Fin r ⊕ Fin r → Matrix (Fin n) (Fin n) E :=
  Sum.elim (lineProj σ J X Y) (lineProj σ J Y X)

def anisoProj (X Y : Matrix (Fin n) (Fin r) E) : Matrix (Fin n) (Fin n) E :=
  1 - ∑ k, projFam σ J X Y k

def normMat (l : Fin n → E) : Matrix (Fin n) (Fin n) E := Matrix.vecMulVec (fun k => σ (l k)) l

def hermFam (X Y : Matrix (Fin n) (Fin r) E) : Option (Fin r ⊕ Fin r) → Matrix (Fin n) (Fin n) E
  | none => cT (σ : E →+* E) (anisoProj σ J X Y) * J * anisoProj σ J X Y
  | some (Sum.inl i) => normMat σ (rowOf σ J Y i)
  | some (Sum.inr i) => normMat σ (rowOf σ J X i)

variable {σ J} {X Y : Matrix (Fin n) (Fin r) E}

theorem leviMin_subset (X Y : Matrix (Fin n) (Fin r) E) : leviMin σ J X Y ⊆ minPar σ J X :=
  fun _ ⟨d, _, e, _⟩ => ⟨_, Matrix.blockTriangular_diagonal _, e⟩

theorem unipMin_subset_minParOne (X : Matrix (Fin n) (Fin r) E) : unipMin σ J X ⊆ minParOne σ J X := by
  rintro u ⟨B, hB, h1, e, -⟩
  exact ⟨B, hB, e, fun i => ⟨1, by rw [h1]; rfl, map_one _⟩⟩

theorem minParOne_props (h : IsCMExt F E σ) (hJ : IsHermND σ J) (hW : IsWittFrame σ J X Y) :
    IsClosed (minParOne σ J X) ∧ ∀ p ∈ minParOne σ J X, ∀ q ∈ minParOne σ J X, p * q ∈ minParOne σ J X := by
  obtain ⟨a, ha⟩ := exists_isTorus h hJ hW
  obtain ⟨τ, hc, hm, -, h0, h1⟩ := exists_tau h hJ hW ha
  have ha0 : a 0 = 1 := by
    have e := ha.add 0 0
    rw [add_zero] at e
    exact mul_left_cancel (e.symm.trans (mul_one _).symm)
  have key : ∀ p : minParSub X h hJ hW, p.1 ∈ minParOne σ J X ↔ τ p = 0 := fun p => by
    refine ⟨fun hp => h0 p.1 hp, fun hp => ?_⟩
    have := h1 p
    rwa [hp, ha0, inv_one, mul_one] at this
  constructor
  · have hcl : IsClosed (minPar σ J X) := isClosed_minPar h hJ hW
    have e : minParOne σ J X = Subtype.val '' (τ ⁻¹' {0}) := by
      ext p
      constructor
      · intro hp
        exact ⟨⟨p, minParOne_subset hp⟩, (key _).1 hp, rfl⟩
      · rintro ⟨q, hq, rfl⟩
        exact (key q).2 hq
    rw [e]
    exact (hcl.isClosedEmbedding_subtypeVal.isClosedMap) _ (isClosed_singleton.preimage hc)
  · intro p hp q hq
    have := (key (⟨p, minParOne_subset hp⟩ * ⟨q, minParOne_subset hq⟩)).2 (by
      rw [hm, (key _).1 hp, (key _).1 hq, add_zero])
    exact this

end GlobalTheory.CompanionTheory.ParCocompact

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralPointsOpenCompactStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralPointsOpenCompact
open NumberField IsDedekindDomain Matrix

namespace GlobalTheory.CompanionTheory.IntegralPoints

theorem isOpen_isCompact_intGL {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R]
    (O : Subring R) (ho : IsOpen (O : Set R)) (hc : IsCompact (O : Set R)) (n : ℕ) :
    IsOpen {g : GL (Fin n) R | (∀ i j, (g : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ O} ∧
    IsCompact {g : GL (Fin n) R | (∀ i j, (g : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ O} := by
  constructor
  · have e : {g : GL (Fin n) R | (∀ i j, (g : Matrix (Fin n) (Fin n) R) i j ∈ O) ∧
        ∀ i j, ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j ∈ O} =
        (⋂ i, ⋂ j, (fun g : GL (Fin n) R => (g : Matrix (Fin n) (Fin n) R) i j) ⁻¹' (O : Set R)) ∩
        (⋂ i, ⋂ j, (fun g : GL (Fin n) R => ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j) ⁻¹' (O : Set R)) := by
      ext g
      simp [Set.mem_iInter]
    rw [e]
    refine IsOpen.inter ?_ ?_
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        ho.preimage (Units.continuous_val.matrix_elem i j)
    · exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
        ho.preimage (Units.continuous_coe_inv.matrix_elem i j)
  · have hM : IsCompact {A : Matrix (Fin n) (Fin n) R | ∀ i j, A i j ∈ O} := by
      have := isCompact_univ_pi fun _ : Fin n => isCompact_univ_pi fun _ : Fin n => hc
      have e : {A : Matrix (Fin n) (Fin n) R | ∀ i j, A i j ∈ O} =
          Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => (O : Set R) :=
        Set.ext fun A => ⟨fun h i _ j _ => h i j, fun h i j => h i trivial j trivial⟩
      exact e ▸ this
    have := (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) R)).isCompact_preimage
      (hM.prod (hM.image MulOpposite.continuous_op))
    convert this using 1
    ext g
    exact ⟨fun h => ⟨h.1, _, h.2, rfl⟩, fun ⟨h1, A, hA, e⟩ => ⟨h1, fun i j => by
      have : A = ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := MulOpposite.op_injective e
      exact this ▸ hA i j⟩⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem coe_Kf (n : ℕ) : (PositivityTheory.Rg.BcB.G8.Kf E n : Set (GL (Fin n) (FiniteAdeleRing (𝓞 E) E))) =
    {g : GL (Fin n) (FiniteAdeleRing (𝓞 E) E) | (∀ i j, (g : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j ∈ Formalism.UG.intAd E) ∧
      ∀ i j, ((g⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) i j ∈
        Formalism.UG.intAd E} := by
  ext g
  simp only [SetLike.mem_coe, PositivityTheory.Rg.BcB.G8.Kf, Subgroup.mem_iInf, Subgroup.mem_comap, Set.mem_setOf_eq]
  constructor
  · intro h
    refine ⟨fun i j w => ?_, fun i j w => ?_⟩
    · have h1 := h w
      rw [← SetLike.mem_coe, GlobalTheory.LFun.KGL, GlobalTheory.LFun.IntPtsUnitary.coe_GLint] at h1
      exact h1.1 i j
    · have h1 := h w
      rw [← SetLike.mem_coe, GlobalTheory.LFun.KGL, GlobalTheory.LFun.IntPtsUnitary.coe_GLint] at h1
      have h2 := h1.2 i j
      rw [← map_inv] at h2
      exact h2
  · rintro ⟨h1, h2⟩ w
    rw [← SetLike.mem_coe, GlobalTheory.LFun.KGL, GlobalTheory.LFun.IntPtsUnitary.coe_GLint]
    refine ⟨fun i j => h1 i j w, fun i j => ?_⟩
    rw [← map_inv]
    exact h2 i j w

theorem kfOC : PositivityTheory.Rg.BcB.G8.KfOC := by
  intro E _ _ _ n
  haveI : T2Space (FiniteAdeleRing (𝓞 E) E) := Formalism.MainNotions.Gaps.LevGap.t2Space_adeleRing_numberField
  rw [coe_Kf]
  exact isOpen_isCompact_intGL (Formalism.UG.intAd E) Formalism.MainNotions.Gaps.LevGap.isOpen_intAd
    Formalism.MainNotions.Gaps.LevGap.isCompact_intAd n

end GlobalTheory.CompanionTheory.IntegralPoints
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_kernel_compact_open : PositivityTheory.Rg.BcB.G8.KfOC := by
  first | exact @GlobalTheory.CompanionTheory.IntegralPoints.kfOC | exact GlobalTheory.CompanionTheory.IntegralPoints.kfOC | (intros; apply GlobalTheory.CompanionTheory.IntegralPoints.kfOC <;> assumption)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CvecSurjective
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic

namespace GlobalTheory.CompanionTheory.RedCov.Bridge

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)


variable (F E n) in
abbrev dimN : ℕ := Fintype.card (Fin n × Fin (Module.finrank F E))

def trG : GAd σ J →* GL (Fin (dimN F E n)) (AF F) :=
  (trHom (ι := Fin n) (Module.finBasis F E) (AF F)).comp (matHom (AF F) σ J)


variable (F) in
def cvec (v : Fin n → E) : Fin (dimN F E n) → F := fun p =>
  (Module.finBasis F E).repr (v ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).1)
    ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).2

theorem cvec_injective : Function.Injective (cvec F : (Fin n → E) → Fin (dimN F E n) → F) := by
  intro u v h
  funext i
  apply (Module.finBasis F E).repr.injective
  ext k
  simpa [cvec] using congrFun h (Fintype.equivFin (Fin n × Fin (Module.finrank F E)) (i, k))

theorem cvec_surjective : Function.Surjective (cvec F : (Fin n → E) → Fin (dimN F E n) → F) := by
  intro x
  refine ⟨fun i => (Module.finBasis F E).equivFun.symm fun k => x (Fintype.equivFin _ (i, k)), ?_⟩
  funext p
  simp [cvec, Module.Basis.equivFun_symm_apply, Finsupp.single_apply]

theorem cvec_ne_zero {v : Fin n → E} (hv : v ≠ 0) : cvec F v ≠ 0 := by
  intro h
  apply hv
  apply cvec_injective (F := F)
  rw [h]
  funext p
  simp [cvec]

theorem ratVec_cvec (v : Fin n → E) :
    Reduction.ratVec (cvec F v) = resVec (ι := Fin n) (Module.finBasis F E) (AF F) (ratV F v) := by
  funext p
  simp only [Reduction.ratVec, cvec, resVec, Function.comp_apply, coordsVec, coords, ratV, inclR]
  simp [Algebra.TensorProduct.basis_repr_tmul]

theorem hv_eq (ξ : Fin n → AF F ⊗[F] E) :
    hv ξ = Reduction.adelicNorm (resVec (ι := Fin n) (Module.finBasis F E) (AF F) ξ) := rfl

theorem hgt_eq (g : GAd σ J) (v : Fin n → E) : hgt σ J g v = Reduction.height (trG σ J g) (cvec F v) := by
  rw [Reduction.height, ratVec_cvec, trG, MonoidHom.comp_apply, resVec_vecMul_trHom, hgt, hv_eq, map_inv]

section Top

attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

theorem continuous_trG : Continuous (trG σ J) :=
  (continuous_trHom (ι := Fin n) (Module.finBasis F E) (AF F)).comp (isEmbedding_matHom (AF F) σ J).continuous

end Top

theorem exists_hgt_le {C : Set (GAd σ J)} (hC : IsCompact C) {v : Fin n → E} (hv : v ≠ 0) :
    ∃ B : ℝ, ∀ c ∈ C, hgt σ J c v ≤ B := by
  obtain ⟨P, -, hP⟩ := Reduction.exists_adelicNorm_vecMul_le_mul (hC.image (continuous_trG σ J))
  refine ⟨P * Reduction.adelicNorm (Reduction.ratVec (cvec F v)), fun c hc => ?_⟩
  rw [hgt_eq]
  exact hP _ ⟨c, hc, rfl⟩ _ (Reduction.hasFiniteContent_ratVec (cvec_ne_zero hv))

end GlobalTheory.CompanionTheory.RedCov.Bridge
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftExistence
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftExistence
open NumberField IsDedekindDomain GroundTheory.Global GroundTheory.LocalField Ad3 Ad3.R
open GroundTheory.Global.RationalSymbol (prime unitAt)
open GroundTheory.Automorphic.GodementSection (adeleAt)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.RankinSelbergQ

open DirichletHecke
open _root_.GroundTheory.Global.Cyclotomic GroundTheory.LocalField.Abstract RationalSymbol

theorem mem_adicCompletionIntegers_of_ord_nonneg (v : Pl) {x : Qv v} (hx : x ≠ 0) (h : 0 ≤ ord x) :
    x ∈ v.adicCompletionIntegers ℚ := by
  have h1 : normalizedValuation (Qv v) x ≤ normalizedValuation (Qv v) 1 := by
    rw [map_one, normalizedValuation_eq_exp_ord hx, ← WithZero.exp_zero, WithZero.exp_le_exp]
    omega
  have h2 := normalizedValuation_le_iff.1 h1
  rw [map_one] at h2
  exact (mem_valuationInteger_iff v x).1 h2

theorem norm_padicRingEquiv_of_ord_eq_zero (v : Pl) (a : (Qv v)ˣ) (h : ord (a : Qv v) = 0) :
    ‖padicRingEquiv v (a : Qv v)‖ = 1 := by
  refine norm_padicRingEquiv_eq_one ((Submonoid.mem_units_iff _ _).2 ⟨?_, ?_⟩)
  · exact mem_adicCompletionIntegers_of_ord_nonneg v a.ne_zero h.ge
  · refine mem_adicCompletionIntegers_of_ord_nonneg v (a⁻¹).ne_zero ?_
    rw [ord_units_inv, h]
    simp

theorem ofFinite_mem_positiveSubgroup (e : Afˣ) (h : ∀ v, ord (lf v e : Qv v) = 0) :
    IdeleGroup.ofFinite e ∈ RationalIdeles.positiveSubgroup := by
  refine mem_positiveSubgroup_of (fun w => norm_padicRingEquiv_of_ord_eq_zero w (lf w e) (h w)) ?_
  change 0 < ((RationalIdeles.realUnitsEquiv.toMulEquiv.toMonoidHom
    (IdeleGroup.toInfinite ℚ (IdeleGroup.ofFinite e)) : ℝˣ) : ℝ)
  rw [IdeleGroup.toInfinite_ofFinite, map_one, Units.val_one]
  exact one_pos

theorem toZModPow_eq_of_congr {N : ℕ} [NeZero N] (w : Pl) (x : Qv w) (u : ℤ_[prime w]) (n : ℤ)
    (hu : (u : ℚ_[prime w]) = padicRingEquiv w x)
    (hx : ((N : Qv w))⁻¹ * (x - n) ∈ 𝒪[Qv w]) :
    PadicInt.toZModPow (N.factorization (prime w)) u =
      ZMod.castHom (Nat.ordProj_dvd N (prime w)) _ (n : ZMod N) := by
  have hO := (mem_valuationInteger_iff w _).1 hx
  have hn : ‖padicRingEquiv w (((N : Qv w))⁻¹ * (x - n))‖ ≤ 1 :=
    (PadicInt.mem_subring_iff _).1 ((Rat.HeightOneSpectrum.adicCompletion.padicEquiv_bijOn w).mapsTo hO)
  let z : ℤ_[prime w] := ⟨_, hn⟩
  have hN : ((N : ℕ) : ℚ_[prime w]) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hz : u = (n : ℤ_[prime w]) + (N : ℤ_[prime w]) * z := by
    apply PadicInt.ext
    have hzc : ((z : ℤ_[prime w]) : ℚ_[prime w]) = ((N : ℚ_[prime w]))⁻¹ * (padicRingEquiv w x - n) := by
      change padicRingEquiv w (((N : Qv w))⁻¹ * (x - n)) = _
      simp only [map_mul, map_inv₀, map_sub, map_natCast, map_intCast]
    rw [PadicInt.coe_add, PadicInt.coe_mul, hzc, hu]
    push_cast
    field_simp
    ring
  have h0 : ((N : ℕ) : ZMod (prime w ^ N.factorization (prime w))) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).2 (Nat.ordProj_dvd N (prime w))
  rw [hz, map_add (f := _), map_mul, map_natCast, map_intCast, map_intCast, h0, zero_mul, add_zero]

theorem heckeCharacter_ofFinite_mul {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (d : Afˣ) (n : ℤ)
    (h0 : ∀ v, ord (lf v d : Qv v) = 0)
    (h1 : ∀ v, pOf v ∣ N → ((N : Qv v))⁻¹ * ((lf v d : Qv v) - n) ∈ 𝒪[Qv v]) :
    ((heckeCharacter χ).toIdele (IdeleGroup.ofFinite d) : ℂ) * χ (n : ZMod N) = 1 := by
  have hinv : ∀ v, ord (lf v d⁻¹ : Qv v) = 0 := fun v => by
    have : lf v d⁻¹ = (lf v d)⁻¹ := map_inv (Units.map (adeleAt v).toMonoidHom) d
    rw [this, ord_units_inv, h0 v]
    simp
  let y : RationalIdeles.positiveSubgroup :=
    ⟨IdeleGroup.ofFinite d⁻¹, ofFinite_mem_positiveSubgroup d⁻¹ hinv⟩
  have key : (heckeCharacter χ (IdeleClassGroup.mk ℚ (y : IdeleGroup ℚ)) : ℂ) = χ (n : ZMod N) := by
    refine coe_heckeCharacter_mk_of_forall χ y fun w hw => ?_
    refine toZModPow_eq_of_congr w (lf w d : Qv w) _ n ?_ (h1 w ?_)
    · have hc := coe_unitAt y w
      have hy : (IdeleGroup.finiteProj w (y : IdeleGroup ℚ) : Qv w) = ((lf w d : Qv w))⁻¹ := by
        have : lf w d⁻¹ = (lf w d)⁻¹ := map_inv (Units.map (adeleAt w).toMonoidHom) d
        change ((lf w d⁻¹ : (Qv w)ˣ) : Qv w) = _
        rw [this, Units.val_inv_eq_inv_val]
      have hm : ((((unitAt y w)⁻¹ : ℤ_[prime w]ˣ) : ℤ_[prime w]) : ℚ_[prime w]) *
          ((unitAt y w : ℤ_[prime w]) : ℚ_[prime w]) = 1 := by
        rw [← PadicInt.coe_mul, Units.inv_mul, PadicInt.coe_one]
      rw [hc, hy, map_inv₀] at hm
      have hne : padicRingEquiv w (lf w d : Qv w) ≠ 0 := (map_ne_zero _).2 (lf w d).ne_zero
      field_simp at hm
      exact hm
    · rw [show pOf w = prime w from absNorm_asIdeal w]
      exact hw
  rw [← key, HeckeCharacter.toIdele_apply, ← Circle.coe_mul, ← map_mul, ← map_mul, ← map_mul]
  simp [y]

private theorem isOfFinOrder_heckeCharacter {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) :
    IsOfFinOrder (heckeCharacter χ) :=
  isOfFinOrder_iff_pow_eq_one.2 ⟨Fintype.card (ZMod N)ˣ, Fintype.card_pos, by
    ext x
    rw [ContinuousMonoidHom.pow_apply, heckeCharacter_apply, galoisCharacter, MonoidHom.comp_apply,
      ← map_pow, pow_card_eq_one, map_one]
    rfl⟩

theorem f0 : Ad3.R.B0 → Ad3.R.F0 := fun _ _ _ χ =>
  ⟨heckeCharacter χ, ⟨isOfFinOrder_heckeCharacter χ, fun d n h0 h1 =>
    heckeCharacter_ofFinite_mul χ d n h0 h1⟩⟩

end GlobalTheory.CompanionTheory.RankinSelbergQ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftExistenceStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.newform_lift_existence : Ad3.R.B0 → Ad3.R.F0 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelbergQ.f0 | exact GlobalTheory.CompanionTheory.RankinSelbergQ.f0 | (intros; apply GlobalTheory.CompanionTheory.RankinSelbergQ.f0 <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainDescription
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainDescription
open NumberField MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain

open Ad3.R

theorem pri_eq_diagonal (α : ℚˣ) : pri α = diagonal ℚ α := rfl

theorem md_eq (a : Jd) : md a = (ideleModule ℚ a : ℝ) := rfl

theorem lintegral_posReal_weight_lt_top (τ : ℝ) (M : ℕ) (h0 : 0 < τ) (h1 : τ < M) :
    ∫⁻ t : {r : ℝ // 0 < r}, ENNReal.ofReal (min 1 (t : ℝ)⁻¹ ^ M * (t : ℝ) ^ τ) ∂posRealMeasure < ∞ := by
  have hF : Measurable (fun t : {r : ℝ // 0 < r} => ENNReal.ofReal (min 1 (t : ℝ)⁻¹ ^ M * (t : ℝ) ^ τ)) := by
    fun_prop
  rw [posRealMeasure_eq_map_expPos, lintegral_map hF measurable_expPos]
  simp only [coe_expPos]
  rw [← lintegral_add_compl _ (measurableSet_Iic (a := (0 : ℝ))), Set.compl_Iic]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · refine (setLIntegral_mono (g := fun x => ENNReal.ofReal (Real.exp (τ * x))) (by fun_prop)
      fun x hx => ?_).trans_lt ?_
    · apply ENNReal.ofReal_le_ofReal
      have hm : min 1 (Real.exp x)⁻¹ ^ M ≤ 1 :=
        pow_le_one₀ (le_min zero_le_one (inv_nonneg.2 (Real.exp_pos x).le)) (min_le_left _ _)
      calc min 1 (Real.exp x)⁻¹ ^ M * Real.exp x ^ τ ≤ 1 * Real.exp x ^ τ :=
            mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (Real.exp_pos x).le _)
        _ = Real.exp (τ * x) := by rw [one_mul, mul_comm, Real.exp_mul]
    · exact Integrable.lintegral_lt_top (integrableOn_exp_mul_Iic h0 0)
  · refine (setLIntegral_mono (g := fun x => ENNReal.ofReal (Real.exp (-((M : ℝ) - τ) * x))) (by fun_prop)
      fun x hx => ?_).trans_lt ?_
    · apply ENNReal.ofReal_le_ofReal
      have hm : min 1 (Real.exp x)⁻¹ ^ M ≤ (Real.exp x)⁻¹ ^ M :=
        pow_le_pow_left₀ (le_min zero_le_one (inv_nonneg.2 (Real.exp_pos x).le)) (min_le_right _ _) M
      calc min 1 (Real.exp x)⁻¹ ^ M * Real.exp x ^ τ ≤ (Real.exp x)⁻¹ ^ M * Real.exp x ^ τ :=
            mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg (Real.exp_pos x).le _)
        _ = Real.exp (-((M : ℝ) - τ) * x) := by
          rw [← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_mul, ← Real.exp_add]
          congr 1
          ring
    · exact Integrable.lintegral_lt_top (exp_neg_integrableOn_Ioi 0 (sub_pos.2 h1))

def fundD (w : InfinitePlace ℚ) : Set Jd :=
  (fun a => (normOneSplitting w a).1) ⁻¹' normOneFundamentalDomain ℚ

theorem measurableSet_fundD (w : InfinitePlace ℚ) : MeasurableSet (fundD w) := by
  exact (measurableSet_normOneFundamentalDomain ℚ).preimage (measurePreserving_normOneSplitting w).measurable.fst

theorem split_pri_mul (w : InfinitePlace ℚ) (α : ℚˣ) (a : Jd) :
    (normOneSplitting w (pri α * a)).1 = (normOneSplitting w a).1 * diagonalToNormOne ℚ α := by
  have hp : pri α = (normOneSplitting w).symm (diagonalToNormOne ℚ α, 1) := by
    simp only [normOneSplitting_symm_apply, map_one, mul_one, coe_diagonalToNormOne, pri_eq_diagonal]
  have key : normOneSplitting w (pri α) = (diagonalToNormOne ℚ α, 1) := by
    rw [hp]
    exact (normOneSplitting w).apply_symm_apply _
  rw [map_mul, Prod.fst_mul, key]
  exact mul_comm _ _

theorem existsUnique_pri_mul_mem (w : InfinitePlace ℚ) (a : Jd) :
    ∃! α : ℚˣ, pri α * a ∈ fundD w := by
  have h : ∀ α : ℚˣ, pri α * a ∈ fundD w ↔
      (normOneSplitting w a).1 * diagonalToNormOne ℚ α ∈ normOneFundamentalDomain ℚ := by
    intro α
    show (normOneSplitting w (pri α * a)).1 ∈ normOneFundamentalDomain ℚ ↔ _
    rw [split_pri_mul]
  exact (existsUnique_congr h).2 (existsUnique_mul_mem_normOneFundamentalDomain ℚ _)

theorem lintegral_fundD_lt_top (w : InfinitePlace ℚ) (τ : ℝ) (M : ℕ) (h0 : 0 < τ) (h1 : τ < M) :
    ∫⁻ a in fundD w, ENNReal.ofReal (min 1 (md a)⁻¹ ^ M * md a ^ τ) ∂ideleMeasure ℚ < ∞ := by
  have hφm : Measurable (fun t : {r : ℝ // 0 < r} => ENNReal.ofReal (min 1 (t : ℝ)⁻¹ ^ M * (t : ℝ) ^ τ)) := by
    fun_prop
  have hIm : Measurable ((normOneFundamentalDomain ℚ).indicator (1 : normOneSubgroup ℚ → ℝ≥0∞)) :=
    measurable_one.indicator (measurableSet_normOneFundamentalDomain ℚ)
  have hpt : ∀ a : Jd, (fundD w).indicator (fun a => ENNReal.ofReal (min 1 (md a)⁻¹ ^ M * md a ^ τ)) a =
      (fun p : normOneSubgroup ℚ × {r : ℝ // 0 < r} => (normOneFundamentalDomain ℚ).indicator 1 p.1 *
        ENNReal.ofReal (min 1 (p.2 : ℝ)⁻¹ ^ M * (p.2 : ℝ) ^ τ)) (normOneSplitting w a) := by
    intro a
    by_cases ha : a ∈ fundD w
    · have ha' : (normOneSplitting w a).1 ∈ normOneFundamentalDomain ℚ := ha
      simp [Set.indicator_of_mem ha, Set.indicator_of_mem ha', normOneSplitting_apply_snd, md_eq]
    · have ha' : (normOneSplitting w a).1 ∉ normOneFundamentalDomain ℚ := ha
      simp [ha, ha']
  rw [← lintegral_indicator (measurableSet_fundD w), lintegral_congr hpt,
    (measurePreserving_normOneSplitting w).lintegral_comp
      (f := fun p : normOneSubgroup ℚ × {r : ℝ // 0 < r} => (normOneFundamentalDomain ℚ).indicator 1 p.1 *
        ENNReal.ofReal (min 1 (p.2 : ℝ)⁻¹ ^ M * (p.2 : ℝ) ^ τ))
      ((hIm.comp measurable_fst).mul (hφm.comp measurable_snd)),
    lintegral_prod_mul hIm.aemeasurable hφm.aemeasurable, lintegral_indicator_one (measurableSet_normOneFundamentalDomain ℚ)]
  exact ENNReal.mul_lt_top (normOneMeasure_normOneFundamentalDomain_lt_top ℚ)
    (lintegral_posReal_weight_lt_top τ M h0 h1)

theorem exists_idele_fundamentalDomain : Ad3.R.D0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace ℚ) := inferInstance
  unfold Ad3.R.D0
  exact ⟨fundD w, measurableSet_fundD w, existsUnique_pri_mul_mem w,
    fun τ M h0 h1 => lintegral_fundD_lt_top w τ M h0 h1⟩

end GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainDescriptionStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_description : Ad3.R.D0 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain.exists_idele_fundamentalDomain | exact GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain.exists_idele_fundamentalDomain | (intros; apply GlobalTheory.CompanionTheory.RankinSelberg.IdeleDomain.exists_idele_fundamentalDomain <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainInvarianceOfDescription
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainInvarianceOfDescription
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology Set
open GroundTheory.Global GroundTheory.Global.IdeleGroup GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open scoped NumberField.AdeleRing ENNReal Pointwise

noncomputable section

namespace GlobalTheory.CompanionTheory.RSGlobal

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem exists_isHaarMeasure_isMulRightInvariant (hn : 0 < n) :
    ∃ μ : Measure (AdelicGLn.AdelicGL K n), μ.IsHaarMeasure ∧ μ.IsMulRightInvariant := by
  set Φ := glNormOneSplitting (K := K) hn with hΦ
  let ν : Measure (normOneGL (K := K) (n := n)) := Measure.haar
  let ρ : Measure {r : ℝ // 0 < r} := Measure.haar
  haveI : ν.IsMulRightInvariant := isMulRightInvariant_normOneGL ν
  let m : Measure (normOneGL (K := K) (n := n) × {r : ℝ // 0 < r}) := ν.prod ρ
  haveI : m.IsHaarMeasure := inferInstanceAs (ν.prod ρ).IsHaarMeasure
  haveI : m.IsMulRightInvariant := inferInstanceAs (ν.prod ρ).IsMulRightInvariant
  have hc : Measurable (Φ.symm : normOneGL (K := K) (n := n) × {r : ℝ // 0 < r} → AdelicGLn.AdelicGL K n) :=
    Φ.symm.continuous.measurable
  refine ⟨m.map Φ.symm, ContinuousMulEquiv.isHaarMeasure_map m Φ.symm, ⟨fun g => ?_⟩⟩
  rw [Measure.map_map (measurable_mul_const g) hc]
  have h : (· * g) ∘ (Φ.symm : normOneGL (K := K) (n := n) × {r : ℝ // 0 < r} → AdelicGLn.AdelicGL K n) =
      Φ.symm ∘ (· * Φ g) := by
    funext p
    simp only [Function.comp_apply, map_mul, ContinuousMulEquiv.symm_apply_apply]
  rw [h, ← Measure.map_map hc (measurable_mul_const (Φ g)), map_mul_right_eq_self]

theorem exists_measure_lt_top_slab (μ : Measure (AdelicGLn.AdelicGL K n)) [μ.IsHaarMeasure] :
    ∃ E : Set (AdelicGLn.AdelicGL K n), μ E < ⊤ ∧ ∀ g : AdelicGLn.AdelicGL K n,
      1 ≤ (ideleModule K (AdelicGLn.det K n g) : ℝ) → (ideleModule K (AdelicGLn.det K n g) : ℝ) ≤ Real.exp 1 →
        ∃ γ : GL (Fin n) K, AdelicGLn.diagonal K n γ * g ∈ E := by
  classical
  obtain ⟨ω, hω, hωB, t, ht, hsieg⟩ := exists_siegelSet (K := K) n
  choose c₁ c₂ hc₁ hbd using fun w => exists_norm_det_infAt_bounds (K := K) hω t w
  set S : ∀ w : InfinitePlace K, Set (GL (Fin n) w.Completion) :=
    fun w => localSiegel w (infAt w '' ω) t (c₁ w) (c₂ w) with hSdef
  have hS : ∀ w, (Measure.haar : Measure (GL (Fin n) w.Completion)) (S w) < ⊤ := fun w =>
    measure_localSiegel_lt_top w _ (hω.image (continuous_infAt w))
      (by rintro _ ⟨b, hb, rfl⟩; exact infAt_isUpperTriangular (hωB hb)) ht (hc₁ w)
  set p2 : AdelicGLn.AdelicGL K n → AdelicGLn.FiniteAdelicGL K n :=
    fun g => (AdelicGLn.prodEquiv K n g).2 with hp2
  have hp2c : Continuous p2 := continuous_snd.comp (AdelicGLn.prodEquiv K n).continuous
  set F : Set (AdelicGLn.FiniteAdelicGL K n) :=
    (p2 '' ω) * (p2 '' (maxCompact (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n))) with hFdef
  have hF : IsCompact F := (hω.image hp2c).mul (isCompact_maxCompact.image hp2c)
  set E : Set (AdelicGLn.AdelicGL K n) := {g | g ∈ siegelSet n ω t ∧
    1 ≤ (ideleModule K (AdelicGLn.det K n g) : ℝ) ∧
      (ideleModule K (AdelicGLn.det K n g) : ℝ) ≤ Real.exp 1} with hEdef
  have hE : μ E < ⊤ := by
    refine measure_lt_top_of_forall_mem μ S hS hF fun g hg => ⟨fun w => ?_, ?_⟩
    · obtain ⟨hgs, h1, h2⟩ := hg
      have hb := hbd w g hgs h1 h2
      obtain ⟨b, hbω, _, ⟨r, hr, hratio, rfl⟩, k, hk, rfl⟩ := hgs
      refine ⟨hb.1, hb.2, infAt w b, ⟨b, hbω, rfl⟩, r, hr, hratio, infAt w k, hk.1 w, ?_⟩
      rw [infAt_mul, infAt_mul, infAt_diagUnits_posIdele w r hr]
    · obtain ⟨⟨b, hbω, _, ⟨r, hr, -, rfl⟩, k, hk, rfl⟩, -, -⟩ := hg
      refine ⟨p2 b, ⟨b, hbω, rfl⟩, p2 k, ⟨k, hk, rfl⟩, ?_⟩
      simp only [hp2, map_mul, Prod.snd_mul, prodEquiv_diagUnits_posIdele_snd r hr, mul_one]
  refine ⟨E, hE, fun g h1 h2 => ?_⟩
  obtain ⟨γ, hγ⟩ := hsieg g
  have hmod : (ideleModule K (AdelicGLn.det K n (AdelicGLn.diagonal K n γ * g)) : ℝ) =
      (ideleModule K (AdelicGLn.det K n g) : ℝ) := by
    have h0 : (ideleModule K (AdelicGLn.det K n (AdelicGLn.diagonal K n γ)) : ℝ) = 1 :=
      mem_normOneGL.1 (rationalGL_le_normOneGL ⟨γ, rfl⟩)
    rw [map_mul, map_mul, Positive.val_mul, h0, one_mul]
  exact ⟨γ, hγ, hmod ▸ h1, hmod ▸ h2⟩

instance countable_GL_rat : Countable (GL (Fin 2) ℚ) :=
  Function.Injective.countable
    (f := fun g : GL (Fin 2) ℚ => (fun i j => (g : Matrix (Fin 2) (Fin 2) ℚ) i j : Fin 2 → Fin 2 → ℚ))
    fun _ _ h => Units.ext (by ext i j; exact congrFun (congrFun h i) j)

theorem measure_inter_band_lt_top (μ : Measure Ad3.R.G2) [μ.IsHaarMeasure] {𝓕 : Set Ad3.R.G2}
    (hF : IsFundamentalDomain (AdelicGLn.diagonal ℚ 2).range 𝓕 μ) : μ (𝓕 ∩ Ad3.R.band) < ⊤ := by
  obtain ⟨E, hE, hcov⟩ := exists_measure_lt_top_slab (K := ℚ) (n := 2) μ
  haveI : Countable (AdelicGLn.diagonal ℚ 2).range :=
    Function.Surjective.countable (AdelicGLn.diagonal ℚ 2).rangeRestrict_surjective
  refine lt_of_le_of_lt ?_ hE
  calc μ (𝓕 ∩ Ad3.R.band) ≤ μ (⋃ γ : (AdelicGLn.diagonal ℚ 2).range, γ • E ∩ 𝓕) := by
        refine measure_mono fun x hx => ?_
        have h2 : (2 : ℝ) ≤ Real.exp 1 := by
          have := Real.exp_one_gt_d9
          linarith
        obtain ⟨γ, hγ⟩ := hcov x hx.2.1 (hx.2.2.le.trans h2)
        refine mem_iUnion.2 ⟨⟨AdelicGLn.diagonal ℚ 2 γ, ⟨γ, rfl⟩⟩⁻¹, ?_, hx.1⟩
        rw [Set.mem_inv_smul_set_iff]
        exact hγ
    _ ≤ ∑' γ : (AdelicGLn.diagonal ℚ 2).range, μ (γ • E ∩ 𝓕) := measure_iUnion_le _
    _ = μ E := by
      set_option synthInstance.maxHeartbeats 200000 in
        exact (hF.measure_eq_tsum E).symm

theorem exists_probability_haar :
    ∃ m : Measure Ad3.R.KA, m.IsHaarMeasure ∧ IsProbabilityMeasure m := by
  haveI : CompactSpace Ad3.R.KA := isCompact_iff_compactSpace.1 isCompact_maxCompact
  haveI : WeaklyLocallyCompactSpace Ad3.R.KA := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact inferInstance
  let K₀ : TopologicalSpace.PositiveCompacts Ad3.R.KA := ⊤
  set_option synthInstance.maxHeartbeats 200000 in
    refine ⟨Measure.haarMeasure K₀, inferInstance, ⟨?_⟩⟩
  have h := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact Measure.haarMeasure_self (K₀ := K₀)
  simpa [K₀] using h

theorem setup_of_ideleDomain : Ad3.R.D0 → Ad3.R.G0 := by
  rintro ⟨𝓓, h1, h2, h3⟩
  obtain ⟨μ, hμ, hr⟩ := exists_isHaarMeasure_isMulRightInvariant (K := ℚ) (n := 2) (by norm_num)
  obtain ⟨mK, hK, hP⟩ := exists_probability_haar
  haveI : DiscreteTopology (AdelicGLn.rationalGL ℚ 2) := AdelicGLn.discreteTopology_rationalGL ℚ 2
  set_option synthInstance.maxHeartbeats 200000 in
  have hF : IsFundamentalDomain (AdelicGLn.diagonal ℚ 2).range
      (RightCosetSpace.fundamentalDomain (AdelicGLn.rationalGL ℚ 2)) μ :=
    RightCosetSpace.isFundamentalDomain_fundamentalDomain (AdelicGLn.rationalGL ℚ 2) μ
  exact ⟨μ, _, mK, 𝓓, ⟨hμ, hr, hF, RightCosetSpace.measurableSet_fundamentalDomain _,
    measure_inter_band_lt_top μ hF, hK, hP, h1, h2, h3⟩⟩

end GlobalTheory.CompanionTheory.RSGlobal

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainInvarianceOfDescriptionStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fundamental_domain_invariance_of_description : Ad3.R.D0 → Ad3.R.G0 := by
  first | exact @GlobalTheory.CompanionTheory.RSGlobal.setup_of_ideleDomain | exact GlobalTheory.CompanionTheory.RSGlobal.setup_of_ideleDomain | (intros; apply GlobalTheory.CompanionTheory.RSGlobal.setup_of_ideleDomain <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeIntegralFiniteSum
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeIntegralFiniteSum
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

namespace GlobalTheory.CompanionTheory.HintLevelPt

theorem hint_eq_level_of_forall : ∀ (H : Type) [Group H] (K L : Subgroup H) (u : H → ℂ), L ≤ K →
    L.relIndex K ≠ 0 → (∀ l ∈ L, ∀ x, u (x * l) = u x) →
    hint K u = ((L.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ p : H ⧸ L, u p.out := by
  intro H _ K L u hLK hfin hu
  exact GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K L u hLK (fun l hl x => hu l hl x) hfin

end GlobalTheory.CompanionTheory.HintLevelPt
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeIntegralFiniteSumStatement
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_integral_finite_sum : ∀ (H : Type) [Group H] (K L : Subgroup H) (u : H → ℂ), L ≤ K → L.relIndex K ≠ 0 → (∀ l ∈ L, ∀ x, u (x * l) = u x) → hint K u = ((L.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ p : H ⧸ L, u p.out := by
  first | exact @GlobalTheory.CompanionTheory.HintLevelPt.hint_eq_level_of_forall | exact GlobalTheory.CompanionTheory.HintLevelPt.hint_eq_level_of_forall | (intros; apply GlobalTheory.CompanionTheory.HintLevelPt.hint_eq_level_of_forall <;> assumption)
end
end
