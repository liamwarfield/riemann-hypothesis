module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormAdelicThetaSumSchroedingerRationalPairInvari
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairReadingOfJoin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAdelicThetaSumSqParsevalSecondVariable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoundedDenominatorStandardCharTrivial

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestExtra
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

namespace GlobalTheory.GramDet

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hn, A, hA⟩ := h
  subst hn
  set A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm with hA'
  have key : A'ᵀ * M * A'.map star =
      (Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℂ) 0 0 (-1)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]
    ext i j
    simp [hA', Matrix.mul_apply, Matrix.submatrix_apply, Matrix.transpose_apply]
  intro h0
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, h0, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁] at hd
  simp [Matrix.det_neg] at hd
  exact pow_ne_zero s (neg_ne_zero.mpr one_ne_zero) hd.symm

theorem det_ne_zero_of_map {n : ℕ} {K : Type} [Field K] (φ : K →+* ℂ) {J : Matrix (Fin n) (Fin n) K}
    (h : (J.map φ).det ≠ 0) : J.det ≠ 0 := by
  intro h0
  apply h
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

theorem gram_det_ne_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    G.V'.J.det ≠ 0 ∧ G.W.J.det ≠ 0 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  refine ⟨det_ne_zero_of_map (B.emb w).1 (det_ne_zero_of_hasSig (hT.geo.hV'.sig w)), ?_⟩
  refine det_ne_zero_of_map (B.emb w).1 ?_
  have h := det_ne_zero_of_hasSig (hT.geo.hW.sig w)
  rw [Matrix.det_smul] at h
  intro h0
  exact h (by rw [h0, mul_zero])

end GlobalTheory.GramDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GbigTwo
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SqStepBig

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Geo Chars)

theorem gbig_two {Q1 Q2 Q : GP} (h1 : GBig Q1) (h2 : GBig Q2)
    (H : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) (μ₀ : T) (C x b : ℝ),
      Q1 G μ₀ C x b → Q2 G μ₀ C x b → Q G μ₀ C x b) : GBig Q := by
  obtain ⟨a1, h1⟩ := h1
  obtain ⟨a2, h2⟩ := h2
  refine ⟨max a1 a2, fun ε CF hCF => ?_⟩
  obtain ⟨c1, x1, g1⟩ := h1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨c2, x2, g2⟩ := h2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max c1 c2, max x1 x2, fun C hC D large₂ hε hx hR T Lc μ₀ hμ G => H G μ₀ C _ _ ?_ ?_⟩
  · exact g1 C (le_trans (le_max_left _ _) hC) D large₂ hε (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hμ G
  · exact g2 C (le_trans (le_max_right _ _) hC) D large₂ hε (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hμ G

variable {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

def Carried (G : GridData Lc sc) (W : G.Weil) (i j : Fin D.R.m) {A A' WW : HSp D} (X : Tri T A A' WW)
    (Bs : Base D.host.F D.host.E) (FA : GlobalTheory.ChainFr.Fr A) (FA' : GlobalTheory.ChainFr.Fr A') (FW : GlobalTheory.ChainFr.Fr WW)
    (Γ : Geo D.sp.cm.sig A.rank A'.rank) (s : T) : Prop :=
  GlobalTheory.SquareComm.IsFinF W.ψ W.θ true FA FW (X.f s) ∧ GlobalTheory.SquareComm.IsFinF W.ψ W.θ false FA' FW (X.f' s) ∧
    (∀ P g h, thetaKO (X.ω s) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ true FA FW (X.f s) P) = X.ker W.ψ W.θ s P h g) ∧
    (∀ P g h, thetaKO (X.ω' s) g h (GlobalTheory.SquareComm.fockF W.ψ W.θ false FA' FW (X.f' s) P) = X.ker' W.ψ W.θ s P h g) ∧
    ∀ om om', GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' →
      ∃ e cA cB, GlobalTheory.SquareAgree.IsOver W.ψ W.θ FA FA' FW (GlobalTheory.SqStep.chs G i j s).α (GlobalTheory.SqStep.chs G i j s).β X.m X.fd
        X.m' X.fd' (X.ω s) (X.ω' s) e Bs Γ (GlobalTheory.SqStep.chs G i j s) om om' cA cB

end GlobalTheory.SqStepBig

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsPrimitive
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsPrimitive
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.AbCoh

theorem primF_of_abelian (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hs : SmoothOfRelativeDimension g A.hom) : PrimF A := by
  obtain ⟨-, -, hAA, hsAA⟩ := GlobalTheory.T.abelianScheme_oneFormFrame_and_square R A g hA hs
  have hax := (GlobalTheory.T.grpObj_pullback_axes_cohomology_projections R A).2.1
  have hM : FP R (GlobForm A.hom × GlobForm A.hom) (g + g) :=
    (GlobalTheory.T.fgProjectiveConstantRank_extension_and_prod).2 R _ _ g g (GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R A g hA hs) (GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R A g hA hs)
  have hN : FP R (GlobForm (A ⊗ A).hom) (g + g) := GlobalTheory.T.abelianScheme_global_oneForms_projective_rank R (A ⊗ A) (g + g) hAA hsAA
  let i₁ : A ⟶ A ⊗ A := lift (𝟙 A) (toUnit A ≫ η[A])
  let i₂ : A ⟶ A ⊗ A := lift (toUnit A ≫ η[A]) (𝟙 A)
  let f : (GlobForm A.hom × GlobForm A.hom) →ₗ[R] GlobForm (A ⊗ A).hom :=
    (pF (fst A A)).coprod (pF (snd A A))
  let r : GlobForm (A ⊗ A).hom →ₗ[R] (GlobForm A.hom × GlobForm A.hom) :=
    (pF i₁).prod (pF i₂)
  have hr : ∀ y, r y = (pF i₁ y, pF i₂ y) := fun y ↦ by simp [r, LinearMap.prod_apply, Function.prod]
  have hrf : ∀ x, r (f x) = x := by
    rintro ⟨a, b⟩
    obtain ⟨h1, h2, -, h4, h5, -⟩ := hax a
    obtain ⟨k1, k2, -, k4, k5, -⟩ := hax b
    have hf : f (a, b) = pF (fst A A) a + pF (snd A A) b := by simp [f]
    rw [hr, hf, map_add (f := _), map_add (f := _), h1, k2, h4, k5, add_zero, zero_add]
  have hbij := GlobalTheory.T.bijective_of_split_injective_fgProjectiveConstantRank R _ _ (g + g) hM hN f r hrf
  have hrinj : Function.Injective r := by
    intro y y' h
    obtain ⟨x, rfl⟩ := hbij.2 y
    obtain ⟨x', rfl⟩ := hbij.2 y'
    rw [hrf, hrf] at h; rw [h]
  intro x
  obtain ⟨-, -, h3, -, -, h6⟩ := hax x
  have e1 : r (pF μ[A] x) = (x, x) := (hr _).trans (Prod.ext h3 h6)
  exact (hrinj (e1.trans (hrf (x, x)).symm)).trans (LinearMap.coprod_apply _ _ _)

end GlobalTheory.AbCoh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeGlobalOneFormsPrimitiveStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_globalOneForms_primitive : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → PrimF A := by
  first | exact @GlobalTheory.AbCoh.primF_of_abelian | exact GlobalTheory.AbCoh.primF_of_abelian | (intros; apply GlobalTheory.AbCoh.primF_of_abelian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeNeTopOfContinuousMulEquivSubgroup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeNeTopOfContinuousMulEquivSubgroup
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

theorem covolume_ne_top_of_continuousMulEquiv : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (e : G ≃ₜ* H) (Γ : Subgroup G) (Λ : Subgroup H) [Countable Γ], (∀ g, g ∈ Γ ↔ e g ∈ Λ) → (∀ μ : Measure G, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤) → ∀ (π : Measure H) (𝓜 : Set H), π.IsHaarMeasure → IsFundamentalDomain Λ 𝓜 π → π 𝓜 ≠ ⊤ := by
  intro G _ _ _ _ _ _ _ _ H _ _ _ _ _ _ _ _ e Γ Λ _ hmem hfin π 𝓜 hπ h𝓜
  let E : G ≃ᵐ H := e.toHomeomorph.toMeasurableEquiv
  have hE : ∀ x, E x = e x := fun _ => rfl
  set μ : Measure G := π.map E.symm with hμdef
  have hμ : μ.IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map π e.symm
  have hqmp : MeasureTheory.Measure.QuasiMeasurePreserving E μ π := by
    refine ⟨E.measurable.aemeasurable, ?_⟩
    rw [hμdef, Measure.map_map E.measurable E.symm.measurable]
    simp only [MeasurableEquiv.self_comp_symm, Measure.map_id]
    exact Measure.AbsolutelyContinuous.rfl
  let φ : Λ → Γ := fun l => ⟨e.symm l, (hmem _).2 (by simpa using l.2)⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro a b hab
      apply Subtype.ext
      have := congrArg (fun x : Γ => e (x : G)) hab
      simpa [φ] using this
    · intro g
      refine ⟨⟨e g, (hmem g).1 g.2⟩, ?_⟩
      apply Subtype.ext; simp [φ]
  have hsemi : ∀ l : Λ, Function.Semiconj E (φ l • ·) (l • ·) := by
    intro l x
    show e ((e.symm l : G) * x) = (l : H) * e x
    simp [map_mul]
  have hF := h𝓜.preimage_of_equiv hqmp hφ hsemi
  have hlt := hfin μ hμ _ hF
  have : μ (E ⁻¹' 𝓜) = π 𝓜 := by
    rw [hμdef, MeasurableEquiv.map_apply]
    congr 1
    ext x; simp
  rw [this] at hlt
  exact hlt.ne

end GlobalTheory.SphEis
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeNeTopOfContinuousMulEquivSubgroupStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_ne_top_of_continuousMulEquiv_subgroup : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (e : G ≃ₜ* H) (Γ : Subgroup G) (Λ : Subgroup H) [Countable Γ], (∀ g, g ∈ Γ ↔ e g ∈ Λ) → (∀ μ : Measure G, μ.IsHaarMeasure → ∀ 𝓕, IsFundamentalDomain Γ 𝓕 μ → μ 𝓕 < ⊤) → ∀ (π : Measure H) (𝓜 : Set H), π.IsHaarMeasure → IsFundamentalDomain Λ 𝓜 π → π 𝓜 ≠ ⊤ := by
  first | exact @GlobalTheory.SphEis.covolume_ne_top_of_continuousMulEquiv | exact GlobalTheory.SphEis.covolume_ne_top_of_continuousMulEquiv | (intros; apply GlobalTheory.SphEis.covolume_ne_top_of_continuousMulEquiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingsCurveFieldAboveFiniteNonempty
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingsCurveFieldAboveFiniteNonempty
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.KerConjMean

theorem fld_finiteDimensional (D : D7) (hI : GlobalTheory.NormSum.Inp D) (δ t0 : ℂ) (hc : Crv D D.host.ccK δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lat D δ) t0) : FiniteDimensional ℚ (fld D δ t0) := by
  obtain ⟨hdata, htor⟩ := (GlobalTheory.T.admJ_and_torsion_data_algebraic D hI.g1).2 D.host.ccK δ hc
  have hwp : wpF (lat D δ) t0 ∈ Qbar := by
    refine (htor t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ fun h0 => ?_).1
    obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have h1 := GlobalTheory.ArchNorm.mul_mem_lamOf D D.host.ccK δ a h0
    rw [ha, mul_comm] at h1
    exact ht.2.1 h1
  let b := Module.finBasis ℚ D.what₂.LL
  obtain ⟨M, hM1, -, hM⟩ := GlobalTheory.ArchNorm.exists_galois
    (Set.range (fun i => D.what₂.embLL (b i)) ∪ {g2 (lat D δ), g3 (lat D δ), wpF (lat D δ) t0})
    ((Set.finite_range _).union (Set.toFinite _)) (by
      rintro y (⟨i, rfl⟩ | rfl | rfl | rfl)
      · exact mem_algebraicClosure_iff.2
          ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom D.what₂.embLL.toRatAlgHom)
      · exact hdata.2.1
      · exact hdata.2.2
      · exact hwp)
  have hσ : ∀ y, D.what₂.embLL y ∈ M := fun y => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr y, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul]
    exact M.smul_mem (hM _ (Or.inl ⟨i, rfl⟩))
  have hle : fld D δ t0 ≤ M := by
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro y (⟨x, rfl⟩ | rfl | rfl | rfl)
    · exact hσ x
    · exact hM _ (Or.inr (by simp))
    · exact hM _ (Or.inr (by simp))
    · exact hM _ (Or.inr (by simp))
  exact Module.Finite.of_injective (IntermediateField.inclusion hle).toLinearMap
    (IntermediateField.inclusion hle).injective

theorem ext_finite_nonempty : ∀ D : D7, GlobalTheory.NormSum.Inp D → ∀ δ t0 : ℂ, Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lat D δ) t0 →
    ∀ σ : D.what₂.LL →+* ℂ, (ext D δ t0 σ).Finite ∧ (ext D δ t0 σ).Nonempty := by
  intro D hI δ t0 hc ht σ
  have := fld_finiteDimensional D hI δ t0 hc ht
  refine ⟨Set.toFinite _, ?_⟩
  let τ : D.what₂.LL →+* fld D δ t0 :=
    { toFun := fun x => ⟨D.what₂.embLL x, embLL_mem D δ t0 x⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y)
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun x y => Subtype.ext (map_add _ x y) }
  letI : Algebra D.what₂.LL (fld D δ t0) := τ.toAlgebra
  letI : Algebra D.what₂.LL ℂ := σ.toAlgebra
  have : IsScalarTower ℚ D.what₂.LL (fld D δ t0) := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : IsScalarTower ℚ D.what₂.LL ℂ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have : Algebra.IsAlgebraic ℚ (fld D δ t0) := Algebra.IsAlgebraic.of_finite ℚ _
  have : Algebra.IsAlgebraic D.what₂.LL (fld D δ t0) := Algebra.IsAlgebraic.tower_top (K := ℚ) D.what₂.LL
  let φ : fld D δ t0 →ₐ[D.what₂.LL] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨φ.restrictScalars ℚ, fun x => ?_⟩
  show φ (algebraMap D.what₂.LL (fld D δ t0) x) = σ x
  rw [φ.commutes]
  rfl

end GlobalTheory.KerConjMean
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingsCurveFieldAboveFiniteNonemptyStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.embeddingsCurveFieldAbove_finite_nonempty : ∀ D : D7, GlobalTheory.NormSum.Inp D → ∀ δ t0 : ℂ, Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lat D δ) t0 → ∀ σ : D.what₂.LL →+* ℂ, (ext D δ t0 σ).Finite ∧ (ext D δ t0 σ).Nonempty := by
  first | exact @GlobalTheory.KerConjMean.ext_finite_nonempty | exact GlobalTheory.KerConjMean.ext_finite_nonempty | (intros; apply GlobalTheory.KerConjMean.ext_finite_nonempty <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactLevelHeightScalesIsotropicFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactLevelHeightScalesIsotropicFrame
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ResidueEisenstein.HtCont

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n k : ℕ} {J : Matrix (Fin n) (Fin n) E} {X : Matrix (Fin n) (Fin k) E}


omit [NumberField E] in
theorem scalesBy_mul {p q : GAd σ J} {β γ : GL (Fin k) (AF F ⊗[F] E)} (e : ScalesBy σ J X p β)
    (e' : ScalesBy σ J X q γ) : ScalesBy σ J X (p * q) (β * γ) := by
  unfold ScalesBy at *
  rw [map_mul, Units.val_mul, Matrix.mul_assoc, e', ← Matrix.mul_assoc, e, Units.val_mul, Matrix.mul_assoc]


omit [NumberField E] in
theorem scalesBy_inv {p : GAd σ J} {β : GL (Fin k) (AF F ⊗[F] E)} (e : ScalesBy σ J X p β) :
    ScalesBy σ J X p⁻¹ β⁻¹ := by
  unfold ScalesBy at *
  calc (matHom _ σ J p⁻¹).1 * adMat F X = (matHom _ σ J p⁻¹).1 * (adMat F X * β.1 * (β⁻¹).1) := by
        rw [Matrix.mul_assoc (adMat F X), ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
    _ = (matHom _ σ J p⁻¹).1 * (matHom _ σ J p).1 * adMat F X * (β⁻¹).1 := by
        rw [← e]; simp only [Matrix.mul_assoc]
    _ = adMat F X * (β⁻¹).1 := by
        rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul]

theorem absE_pos (u : (AF F ⊗[F] E)ˣ) : (0 : ℝ) < absE F E u := by
  have h : absE F E u * absE F E u⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have : absE F E u ≠ 0 := fun h0 => by rw [h0, zero_mul] at h; exact zero_ne_one h
  exact_mod_cast pos_iff_ne_zero.2 this

theorem isCompact_isHt_scales : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → IsCompact (levelAll σ J L a : Set (GAd σ J)) ∧ IsHt (levelAll σ J L a) h ∧ ∀ p β, ScalesBy σ J X p β → ∀ g, h (p * g) = absE F E (Matrix.GeneralLinearGroup.det β) * h g := by
  intro F E _ _ _ _ _ σ n J r X Y L a h H
  haveI := H.lat
  obtain ⟨_, _⟩ := GlobalTheory.StdPar.ring_facts (F := F) (E := E)
  have hK : IsCompact (levelAll σ J L a : Set (GAd σ J)) := GlobalTheory.Doubling.isCompact_levelAll H.cm J L a
  have hyx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := GlobalTheory.StdPar.yx H.cm H.herm H.witt
  have hsc : ∀ p β, ScalesBy σ J X p β → ∀ g, h (p * g) = absE F E (Matrix.GeneralLinearGroup.det β) * h g := by
    intro p β e g
    obtain ⟨q, γ, e', k, hk, rfl⟩ := H.iwa g
    rw [← mul_assoc, H.ht _ _ (scalesBy_mul e e') _ hk, H.ht _ _ e' _ hk, map_mul, map_mul, NNReal.coe_mul]
  let φ : GAd σ J → Matrix (Fin (r + 1)) (Fin (r + 1)) (AF F ⊗[F] E) := fun p =>
    adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) * ((matHom _ σ J p).1 * adMat F X)
  have h1 : adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) * adMat F X = 1 := by
    simp only [adMat, ← Matrix.map_mul, hyx]; simp
  have hφ : ∀ p β, ScalesBy σ J X p β → φ p = β.1 := fun p β e => by
    unfold ScalesBy at e
    show adMat F (Formalism.UG.cT (σ : E →+* E) Y * J) * ((matHom _ σ J p).1 * adMat F X) = β.1
    rw [e, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  have cφ : Continuous φ := continuous_const.matrix_mul (GlobalTheory.StdPar.continuous_mat.matrix_mul continuous_const)
  let P := GlobalTheory.StdPar.frameStab σ J X (⊤ : Subgroup (GL (Fin (r + 1)) (AF F ⊗[F] E)))
  have cP : IsClosed (P : Set (GAd σ J)) := GlobalTheory.StdPar.isClosed_frameStab hyx isClosed_univ
  have hP : ∀ p : P, ScalesBy σ J X p.1 p.2.choose := fun p => p.2.choose_spec.2
  let u : P → (AF F ⊗[F] E)ˣ := fun p => Matrix.GeneralLinearGroup.det p.2.choose
  have cu : Continuous u := Units.continuous_iff.2
    ⟨((cφ.comp continuous_subtype_val).matrix_det).congr fun p => by
        simp only [Function.comp, u, hφ _ _ (hP p)]; rfl,
      ((cφ.comp (continuous_subtype_val.inv)).matrix_det).congr fun p => by
        show (φ (p.1⁻¹)).det = _
        rw [hφ _ _ (scalesBy_inv (hP p)), ← map_inv, Matrix.GeneralLinearGroup.val_det_apply]⟩
  refine ⟨hK, ⟨fun g => ?_, ?_, fun k hk => by simpa using H.ht 1 1 (by simp [ScalesBy]) k hk, fun g => ?_⟩, hsc⟩
  · obtain ⟨p, β, e, k, hk, rfl⟩ := H.iwa g
    rw [H.ht _ _ e _ hk]; exact absE_pos _
  · refine GlobalTheory.Doubling.continuous_of_prod cP hK
      (fun g => let ⟨p, β, e, k, hk, e'⟩ := H.iwa g; ⟨⟨p, β, trivial, e⟩, k, hk, e'⟩) ?_
    exact (NNReal.continuous_coe.comp (GlobalTheory.Doubling.continuous_absE.comp (cu.comp continuous_fst))).congr
      fun x => (H.ht _ _ (hP x.1) _ x.2.2).symm
  · obtain ⟨p, β, e, k, hk, rfl⟩ := H.iwa g
    refine ⟨k, hk, fun x => ?_⟩
    rw [mul_assoc, hsc _ _ e, H.ht _ _ e _ hk]

end GlobalTheory.ResidueEisenstein.HtCont

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactLevelHeightScalesIsotropicFrameStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_level_height_scales_isotropicFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → IsCompact (levelAll σ J L a : Set (GAd σ J)) ∧ IsHt (levelAll σ J L a) h ∧ ∀ p β, ScalesBy σ J X p β → ∀ g, h (p * g) = absE F E (Matrix.GeneralLinearGroup.det β) * h g := by
  first | exact @GlobalTheory.ResidueEisenstein.HtCont.isCompact_isHt_scales | exact GlobalTheory.ResidueEisenstein.HtCont.isCompact_isHt_scales | (intros; apply GlobalTheory.ResidueEisenstein.HtCont.isCompact_isHt_scales <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentLevelFixedVectorsNeBot
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentLevelFixedVectorsNeBot
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.LocFix

theorem fixed_ne_bot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π →
    (∀ v, HasWeightAt π v.embedding (lam v)) → π ⊓ fixed (RF E n) (globLev S K') ≠ ⊥ →
    ∀ w ∈ S, ∀ σ : SmIrr (UL n w), IsCompU π w σ → fixed σ.ρ (K' w) ≠ ⊥ := by
  intro E _ _ _ hU n _ S hS lam K' hK' π hπ _ hne w hw σ hσ
  classical
  obtain ⟨p, hp, -, f, hf0, hfm, hf⟩ := hσ
  obtain ⟨e, he⟩ := GlobalTheory.BCT.LocCompU.exists_equiv hU n w
  have hpe : ∀ x, p x = e x := fun x => Subtype.ext ((hp x).trans (he x).symm)
  have hps : Function.Surjective p := fun g => ⟨e.symm g, by rw [hpe, e.apply_symm_apply]⟩
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
  let π' : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  let F : Representation.IntertwiningMap (σ.ρ.comp p) (π'.rep.comp (locU n w).subtype) :=
    ⟨f.codRestrict π hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
  have hF0 : F ≠ 0 := fun h =>
    hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
  have hσirr := GlobalTheory.BCT.LocCompU.isIrreducible_comp_of_surjective σ.ρ p hps σ.irred
  have htop := (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) π σ.V σ.V π'.rep (locU n w).subtype
    (σ.ρ.comp p) (σ.ρ.comp p) π'.isIrreducible_rep hσirr hσirr (fun g => ⟨r g, fun y => hr g y⟩) F hF0).1

  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hφπ : φ ∈ π := (Submodule.mem_inf.1 hφ).1
  have hφfix : φ ∈ fixed (RF E n) (globLev S K') := (Submodule.mem_inf.1 hφ).2

  have hfixx : ∀ x : locU n w, p x ∈ K' w → RU E n (x : UA E n) φ = φ := by
    intro x hx
    have hxfin : (x : UA E n) ∈ finU (E := E) (n := n) := (Subgroup.mem_inf.1 x.2).1
    have hy : (⟨x, hxfin⟩ : finU (E := E) (n := n)) ∈ globLev S K' := by
      simp only [globLev, Subgroup.mem_iInf]
      intro w' hw'
      rw [Subgroup.mem_comap, Subgroup.mem_map]
      by_cases hww : w' = w
      · subst hww
        exact ⟨p x, hx, hp x⟩
      · have hund : w'.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E)) :=
          fun h => hww ((hS w).unique ⟨hw', h⟩ ⟨hw, rfl⟩)
        have h1 : cLoc w' (x : UA E n) = 1 := by
          have h2 := (Subgroup.mem_inf.1 x.2).2
          rw [Subgroup.mem_iInf] at h2
          exact Subgroup.mem_iInf.1 (h2 w') hund
        exact ⟨1, (K' w').one_mem, by simp [h1]⟩
    have h3 : RF E n ⟨x, hxfin⟩ φ = φ := by simpa using hφfix ⟨_, hy⟩
    exact h3
  have hmem : (⟨φ, hφπ⟩ : π) ∈ ⨆ F : Representation.IntertwiningMap (σ.ρ.comp p) (π'.rep.comp (locU n w).subtype),
      LinearMap.range F.toLinearMap := by
    rw [htop]; trivial
  obtain ⟨c, hc, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hmem
  choose u hu using fun i => LinearMap.mem_range.1 (hc i)
  let ρK : Representation ℂ (K' w) σ.V := σ.ρ.comp (K' w).subtype
  have hsumF : ∀ g : K' w, ∑ i ∈ c.support, (i.toLinearMap : σ.V →ₗ[ℂ] π) (ρK g (u i)) =
      (((1 : K' w →* ℂˣ) g : ℂˣ) : ℂ) • (⟨φ, hφπ⟩ : π) := by
    intro g
    have hpx : p (e.symm g) = g := by rw [hpe, e.apply_symm_apply]
    have hterm : ∀ i ∈ c.support, (i.toLinearMap : σ.V →ₗ[ℂ] π) (ρK g (u i)) = π'.rep (e.symm g : UA E n) (c i) := by
      intro i _
      have h1 := LinearMap.congr_fun (i.isIntertwining' (e.symm g)) (u i)
      simp only [LinearMap.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype] at h1
      rw [hpx] at h1
      rw [← hu i]
      exact h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl hterm, ← map_sum]
    have hs : ∑ i ∈ c.support, c i = (⟨φ, hφπ⟩ : π) := hsum
    rw [hs]
    apply Subtype.ext
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    exact hfixx (e.symm g) (by rw [hpx]; exact g.2)
  let H : Subgroup (K' w) := ⨅ i ∈ c.support, GlobalTheory.LocVec.stabSub ρK (u i)
  have hHo : IsOpen (H : Set (K' w)) := by
    simp only [H, Subgroup.coe_iInf]
    refine isOpen_biInter_finset fun i _ => ?_
    have : (GlobalTheory.LocVec.stabSub ρK (u i) : Set (K' w)) =
        (fun g : K' w => (g : UL n w)) ⁻¹' {x | σ.ρ x (u i) = u i} := rfl
    rw [this]
    exact (σ.smooth (u i)).preimage continuous_subtype_val
  have hKc := (GlobalTheory.BCT.LocCompU.isOpen_isCompact_KL hU n w).2
  haveI : H.FiniteIndex := GlobalTheory.LocVec.finiteIndex_of_isOpen (K' w) hKc (fun g hg => (hK'.1 w).2.1 hg) H hHo
  obtain ⟨v, hv0, hv⟩ := GlobalTheory.LocVec.exists_eigen_of_sum ρK (1 : K' w →* ℂˣ) H (fun h _ => MonoidHom.mem_ker.2 rfl)
    c.support u (fun i hi h hh => (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hh i) hi))
    (fun i => (i.toLinearMap : σ.V →ₗ[ℂ] π)) ⟨φ, hφπ⟩ (fun h => hφ0 (congrArg Subtype.val h)) hsumF
  have hvmem : v ∈ fixed σ.ρ (K' w) := fun h => hv h
  intro hb
  rw [hb] at hvmem
  exact hv0 ((Submodule.mem_bot ℂ).1 hvmem)

end GlobalTheory.BCT.LocFix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalComponentLevelFixedVectorsNeBotStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localComponent_levelFixedVectors_ne_bot : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → (∀ v, HasWeightAt π v.embedding (lam v)) → π ⊓ fixed (RF E n) (globLev S K') ≠ ⊥ → ∀ w ∈ S, ∀ σ : SmIrr (UL n w), IsCompU π w σ → fixed σ.ρ (K' w) ≠ ⊥ := by
  first | exact @GlobalTheory.BCT.LocFix.fixed_ne_bot | exact GlobalTheory.BCT.LocFix.fixed_ne_bot | (intros; apply GlobalTheory.BCT.LocFix.fixed_ne_bot <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRationalSupportCommonDenominator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRationalSupportCommonDenominator
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical

noncomputable section

namespace GlobalTheory.FinSupp

theorem finDiv_finPart_mul {F : Type} [Field F] [NumberField F] {N m : ℕ} {T : AF F} (hT : GlobalTheory.FinSupp.FinDiv F N ((m : AF F) * T))
    (a : 𝓞 F) : GlobalTheory.FinSupp.FinDiv F N (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((m : F) * (a : F))) * T) := by
  intro v
  obtain ⟨b, hb, e⟩ := hT v
  have ha : algebraMap F (Fv F v) (a : F) ∈ v.adicCompletionIntegers F := HeightOneSpectrum.coe_mem_adicCompletionIntegers v a
  refine ⟨algebraMap F (Fv F v) (a : F) * b, mul_mem ha hb, ?_⟩
  have e1 : evFin F v (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((m : F) * (a : F)))) =
      evFin F v (algebraMap F (AF F) ((m : F) * (a : F))) := rfl
  rw [map_mul, e1, AlgHom.commutes, map_mul, map_natCast]
  simp only [map_mul, map_natCast] at e
  rw [mul_comm ((m : Fv F v)) _, mul_assoc, e]
  ring

theorem finPart_mul {F : Type} [Field F] [NumberField F] (x y : AF F) :
    GlobalTheory.FinSupp.finPart F x * y = GlobalTheory.FinSupp.finPart F (x * y) :=
  Prod.ext (zero_mul _) rfl

theorem exists_common_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧
    ∀ ξ : Fin n × Fin d → F, om (g, h) Φ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP Φ hΦ
  have S := hP.weil.isUSplitting
  have hstd : IsStd B.ψ := hP.base.std
  obtain ⟨N, hN1, hinv⟩ := GlobalTheory.T.adelicSchwartz_fixed_by_small_heisenberg_lattice F (Fin n × Fin d) B.ψ hstd.1 Φ hΦ
  obtain ⟨C, k, hC⟩ := GlobalTheory.T.exists_scale_movedHeisenbergLattice_polynomial_heights F E n d (Fin n × Fin d) M.co.e N hN1
  obtain ⟨D, hD1, hD⟩ := GlobalTheory.T.exists_bounded_denominator_standardChar_trivial F
  refine ⟨D * C, k, fun g h => ?_⟩
  obtain ⟨m, hm1, hmC, hmT⟩ := hC g.1 h.1
  refine ⟨D * m, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_, ?_⟩
  · push_cast
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hmC (by positivity)
  · intro ξ hξ i
    have key : ∀ a : 𝓞 F, B.ψ (GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((a : F) * ((m : F) * ξ i)))) = 1 := by
      intro a
      set c : AF F := GlobalTheory.FinSupp.finPart F (algebraMap F (AF F) ((m : F) * (a : F))) with hc
      set y : Fin n × Fin d → AF F := c • Pi.single i 1 with hy
      set w' := M.co.e.symm (0, y) with hw'
      set p : UA σ X.J × UA σ W.J := (g, h) with hp
      set w := actAB (cA σ) p⁻¹ w' with hw
      have hwe : M.co.e w = c • M.co.e ((((g.1)⁻¹ : GL (Fin n) (AF F ⊗[F] E)) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) *
          M.co.e.symm (0, Pi.single i 1) * (((h.1⁻¹ : GL (Fin d) (AF F ⊗[F] E)) : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)))ᵀ) := by
        rw [hw, hw', hy, hp]
        rw [show ((0 : Fin n × Fin d → AF F), c • Pi.single i (1 : AF F)) = c • ((0 : Fin n × Fin d → AF F), Pi.single i (1 : AF F)) by simp]
        rw [LinearEquiv.map_smul, ← LinearEquiv.map_smul M.co.e]
        congr 1
        simp only [actAB, Prod.inv_mk, Subgroup.coe_inv]
        rw [Matrix.mul_smul, Matrix.smul_mul]
      have hrho : M.co.rho B.ψ w Φ = Φ := by
        unfold Darboux.rho
        apply hinv
        intro l
        rw [hwe]
        obtain ⟨h1, h2⟩ := hmT i l
        refine ⟨?_, ?_, ?_, ?_⟩
        · show (c * _).1 = 0
          exact zero_mul _
        · rw [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
          exact finDiv_finPart_mul h1 a
        · show (c * _).1 = 0
          exact zero_mul _
        · rw [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
          exact finDiv_finPart_mul h2 a
      have himpl := S.impl p w Φ hΦ
      rw [hrho] at himpl
      have hact : actAB (cA σ) p w = w' := by
        rw [hw]
        simp only [actAB, Prod.fst_inv, Prod.snd_inv, Subgroup.coe_inv, hp]
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul,
          Matrix.mul_assoc, ← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one,
          Matrix.mul_one]
      rw [hact] at himpl
      have hx := congrFun himpl (fun j => algebraMap F (AF F) (ξ j))
      simp only [Darboux.rho, hw', LinearEquiv.apply_symm_apply, schr, zero_dotProduct, mul_zero, add_zero] at hx
      have h1 : B.ψ ((fun j => algebraMap F (AF F) (ξ j)) ⬝ᵥ y) = 1 := by
        have hne : om p Φ (fun j => algebraMap F (AF F) (ξ j)) ≠ 0 := hξ
        exact (mul_eq_right₀ hne).1 hx.symm
      rw [hy, dotProduct_smul, dotProduct_single, smul_eq_mul, mul_one, hc, finPart_mul, ← map_mul] at h1
      convert h1 using 3
      ring
    have := hD B.ψ hstd _ key
    convert this using 1
    push_cast
    ring

end GlobalTheory.FinSupp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepRationalSupportCommonDenominatorStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_rational_support_common_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 1 ≤ m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧
    ∀ ξ : Fin n × Fin d → F, om (g, h) Φ (fun i => algebraMap F (AF F) (ξ i)) ≠ 0 → ∀ i, IsIntegral ℤ ((m : F) * ξ i) := by
  first | exact @GlobalTheory.FinSupp.exists_common_denominator | exact GlobalTheory.FinSupp.exists_common_denominator | (intros; apply GlobalTheory.FinSupp.exists_common_denominator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIsotropicUnipotentRadicalIffFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIsotropicUnipotentRadicalIffFrame
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis

theorem mem_unipRad_iff_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ u : GAd σ J, u ∈ unipRad σ J C ↔ ((matHom _ σ J u).1 * adMat F C = adMat F C ∧ ∃ b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), (matHom _ σ J u).1 * adMat F Z = adMat F Z + adMat F C * b) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ fr u
  have hmap : ∀ {a b c : ℕ} (X : Matrix (Fin a) (Fin b) E) (Y : Matrix (Fin b) (Fin c) E),
      adMat F (X * Y) = adMat F X * adMat F Y := fun X Y => by
    simp only [adMat]; exact Matrix.map_mul
  have hsub : adMat F ((1 : Matrix (Fin n) (Fin n) E) - D * (cT (σ : E →+* E) C * J)) =
      adMat F C * adMat F (cT (σ : E →+* E) D * J) + adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) := by
    have e : (1 : Matrix (Fin n) (Fin n) E) - D * (cT (σ : E →+* E) C * J) =
        C * (cT (σ : E →+* E) D * J) + Z * (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) := by
      rw [← fr.sum]; abel
    rw [e, ← hmap, ← hmap]
    simp only [adMat]; exact Matrix.map_add _ (map_add _) _ _
  have hZ : ((1 : Matrix (Fin n) (Fin n) E) - D * (cT (σ : E →+* E) C * J)) * Z = Z := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, fr.cz, Matrix.mul_zero, sub_zero]
  have hdual : u ∈ unipRad σ J C ↔ ((matHom _ σ J u).1 - 1) * adMat F C = 0 ∧
      ∃ B : Matrix (Fin j) (Fin n) (AF F ⊗[F] E),
        ((matHom _ σ J u).1 - 1) * adMat F (1 - D * (cT (σ : E →+* E) C * J)) = adMat F C * B := by
    constructor
    · intro hg
      simp only [Matrix.sub_mul _ (1 : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)), Matrix.one_mul,
        sub_eq_iff_eq_add, zero_add]
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        obtain ⟨h1, -, h3⟩ := hg
        rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
        have hT : cT (σ : E →+* E) C * J * (1 - D * (cT (σ : E →+* E) C * J)) = 0 := by
          rw [Matrix.mul_sub, ← Matrix.mul_assoc _ D, fr.cd, Matrix.mul_one, Matrix.one_mul, sub_self]
        choose a ha using fun k => h3 (fun j => (1 - D * (cT (σ : E →+* E) C * J) : Matrix (Fin n) (Fin n) E) j k)
          (funext fun j => congrFun (congrFun hT j) k)
        refine ⟨h1, Matrix.of fun i k => a k i, ?_⟩
        rw [← sub_eq_iff_eq_add, ← Matrix.one_mul (adMat F (1 - _)), ← Matrix.mul_assoc, Matrix.mul_one, ← Matrix.sub_mul]
        ext i k
        exact congrFun (ha k) i
      | one => exact ⟨by simp, 0, by simp⟩
      | mul a b _ _ ha hb =>
        obtain ⟨a1, A, a2⟩ := ha
        obtain ⟨b1, B, b2⟩ := hb
        refine ⟨by rw [map_mul, Units.val_mul, Matrix.mul_assoc, b1, a1], B + A, ?_⟩
        rw [map_mul, Units.val_mul, Matrix.mul_assoc, b2, Matrix.mul_add, ← Matrix.mul_assoc, a1, a2, Matrix.mul_add,
          add_assoc]
      | inv a _ ha =>
        obtain ⟨a1, A, a2⟩ := ha
        have i1 : (matHom _ σ J a⁻¹).1 * adMat F C = adMat F C := by
          conv_lhs => rw [← a1]
          rw [map_inv, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
        refine ⟨i1, -A, ?_⟩
        have := congrArg ((matHom _ σ J a⁻¹).1 * ·) a2
        rw [Matrix.mul_add, ← Matrix.mul_assoc _ (adMat F C), i1, ← Matrix.mul_assoc, ← Units.val_mul, ← map_mul,
          inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul] at this
        rw [Matrix.mul_neg]
        conv_rhs => rw [this]
        abel
    · rintro ⟨h1, B, h2⟩
      refine Subgroup.subset_closure ⟨h1, ?_, fun x hx => ⟨B *ᵥ fun i => inclR (F := F) (AF F) (x i), ?_⟩⟩
      · have hg : cT (sigR (AF F) σ) (matHom _ σ J u).1 * adMat F J * (matHom _ σ J u).1 = adMat F J := u.2
        have c1 : cT (sigR (AF F) σ) (adMat F C) = adMat F (cT (σ : E →+* E) C) := rfl
        rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
        rw [adMat, Matrix.map_mul, ← adMat, ← c1, Matrix.mul_sub, Matrix.mul_one, sub_eq_zero]
        conv_lhs => rw [← h1, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT _ (matHom _ σ J u).1)]
        exact congrArg _ hg
      · have e : adMat F (1 - D * (cT (σ : E →+* E) C * J)) *ᵥ (fun i => inclR (F := F) (AF F) (x i)) =
            fun i => inclR (F := F) (AF F) (x i) := by
          funext i
          have := RingHom.map_mulVec (inclR (F := F) (AF F)) (1 - D * (cT (σ : E →+* E) C * J)) x i
          rw [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, sub_zero, Matrix.one_mulVec] at this
          exact this.symm
        rw [Matrix.mulVec_mulVec, ← h2, ← Matrix.mulVec_mulVec, e]
  rw [hdual]
  set M := (matHom _ σ J u).1
  constructor
  · rintro ⟨h1, B, h2⟩
    refine ⟨by rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1; exact h1, B * adMat F Z, ?_⟩
    have := congrArg (· * adMat F Z) h2
    rw [Matrix.mul_assoc, ← hmap, hZ, Matrix.mul_assoc] at this
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_iff_eq_add] at this
    rw [this, add_comm]
  · rintro ⟨h1, b, h2⟩
    refine ⟨by rw [Matrix.sub_mul, Matrix.one_mul, h1, sub_self], b * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)), ?_⟩
    have h1' : (M - 1) * adMat F C = 0 := by rw [Matrix.sub_mul, Matrix.one_mul, h1, sub_self]
    have h2' : (M - 1) * adMat F Z = adMat F C * b := by rw [Matrix.sub_mul, Matrix.one_mul, h2]; abel
    rw [hsub, Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1', h2', Matrix.zero_mul, zero_add, Matrix.mul_assoc]

end GlobalTheory.SphEis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIsotropicUnipotentRadicalIffFrameStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_isotropicUnipotentRadical_iff_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ u : GAd σ J, u ∈ unipRad σ J C ↔ ((matHom _ σ J u).1 * adMat F C = adMat F C ∧ ∃ b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), (matHom _ σ J u).1 * adMat F Z = adMat F Z + adMat F C * b) := by
  first | exact @GlobalTheory.SphEis.mem_unipRad_iff_frame | exact GlobalTheory.SphEis.mem_unipRad_iff_frame | (intros; apply GlobalTheory.SphEis.mem_unipRad_iff_frame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFrameCoordsOfMemTorusLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFrameCoordsOfMemTorusLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaLawLat

variable {D : D7}

theorem entry_mem_AA {N N' : ℕ} {z : Matrix (Fin N') (Fin N) D.host.E}
    (hz : z ∈ GlobalTheory.InertSign.RL D D.host.ccK (Formalism.MainNotions.StandardLatticesGL3.stdL D N) (Formalism.MainNotions.StandardLatticesGL3.stdL D N'))
    (p : Fin N') (q : Fin N) : z p q ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) := by
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨t, ht, A, hA, rfl⟩ := hz
    have hAint : GlobalTheory.InertSign.IntE D (A p q) := by
      have h1 : (Pi.single q 1 : Fin N → D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D N := by
        refine GlobalTheory.ThetaLatImage.mem_stdL.2 fun i => ?_
        by_cases h : i = q
        · subst h; rw [Pi.single_eq_same]; exact one_mem _
        · rw [Pi.single_eq_of_ne h]; exact zero_mem _
      have h2 := GlobalTheory.ThetaLatImage.mem_homL.1 hA _ h1
      rw [Matrix.mulVec_single_one] at h2
      exact GlobalTheory.ThetaLatImage.mem_stdL.1 h2 p
    obtain ⟨o, ho⟩ := hAint
    have ht' : t ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) := by
      induction ht using Submodule.span_induction with
      | mem t ht =>
        obtain ⟨c, hc, a, ha, rfl⟩ := ht
        have hc' : ((c : D.host.K) : D.host.E) ∈ (D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
          FractionalIdeal.mem_coeIdeal_of_mem _ (Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) hc)
        exact FractionalIdeal.mul_mem_mul hc' ha
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | smul o x _ hx => exact Submodule.smul_mem _ o hx
    rw [Matrix.smul_apply, smul_eq_mul, ← ho, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ o ht'
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul o x _ hx => exact Submodule.smul_mem _ o hx

end GlobalTheory.ThetaLawLat

namespace GlobalTheory.ThetaLawLat

variable {D : D7}

theorem one_mem_intAf' : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

theorem inv_frame {S : HSp D} (frS : GL (Fin S.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1) :
    (frS⁻¹).1 = frS.1ᴴ * S.gram := by
  have h1 : (frS.1ᴴ * S.gram) * frS.1 = 1 := hS
  calc (frS⁻¹).1 = ((frS.1ᴴ * S.gram) * frS.1) * (frS⁻¹).1 := by rw [h1, Matrix.one_mul]
    _ = frS.1ᴴ * S.gram := by rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem finRat_frame_mem_latO {S T : HSp D} (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E)
    (hS : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1)
    (z : Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (hz : ∀ p q, z p q ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E)) :
    GlobalTheory.VacUnique.finRat S T (frT.1 * z * (frS⁻¹).1) ∈
      latO S T (colLat frS : Set (Fin S.rank → D.host.E)) (colLat frT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
  have key : GlobalTheory.VacUnique.finRat S T (frT.1 * z * (frS⁻¹).1) =
      ∑ p, ∑ q, Matrix.of fun i j => (pairA D.host.F 0 1) ⊗ₜ[D.host.F]
        (z p q * (fun a => frT.1 a p) i * ∑ k, star ((fun a => frS.1 a q) k) * S.gram k j) := by
    ext i j
    simp only [Matrix.sum_apply, Matrix.of_apply]
    simp only [← TensorProduct.tmul_sum]
    show (pairA D.host.F 0 1) ⊗ₜ[D.host.F] (frT.1 * z * (frS⁻¹).1) i j = _
    congr 1
    rw [inv_frame frS hS]
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  rw [key]
  refine AddSubgroup.sum_mem _ fun p _ => AddSubgroup.sum_mem _ fun q _ => AddSubgroup.subset_closure ?_
  exact ⟨1, one_mem_intAf', fun v h => (h trivial).elim, z p q, hz p q, _,
    Submodule.subset_span ⟨q, rfl⟩, _, Submodule.subset_span ⟨p, rfl⟩, rfl⟩

theorem mem_La_frame : ∀ {D : D7} (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ δ : ℂ, ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank), ∃ v : Matrix (Fin T.rank) (Fin S.rank) D.host.E, GlobalTheory.VacUnique.finRat S T v ∈ latO S T (colLat frS : Set (Fin S.rank → D.host.E)) (colLat frT : Set (Fin T.rank → D.host.E)) (fun _ => True) ∧ x = δ • (fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b) := by
  intro D S T frS frT hS hT δ x hx
  obtain ⟨z, hz, rfl⟩ := GlobalTheory.ThetaLatImage.La_sub hx
  refine ⟨frT.1 * z * (frS⁻¹).1, finRat_frame_mem_latO frS frT hS z (GlobalTheory.ThetaLawLat.entry_mem_AA hz), ?_⟩
  have hmap : ∀ τ, Matrix.of (GlobalTheory.VacUnique.infRat S T (frT.1 * z * (frS⁻¹).1) τ) =
      GlobalTheory.FockPos.frAt frT τ * Matrix.of (fun i j => tauE D τ (z i j)) * (GlobalTheory.FockPos.frAt frS τ)⁻¹ := by
    intro τ
    have hi : (GlobalTheory.FockPos.frAt frS τ)⁻¹ = (frS⁻¹).1.map (tauE D τ) := by
      refine Matrix.inv_eq_right_inv ?_
      rw [GlobalTheory.FockPos.frAt, ← Matrix.map_mul, Units.mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [hi]
    show (frT.1 * z * (frS⁻¹).1).map (tauE D τ) = _
    rw [Matrix.map_mul, Matrix.map_mul]
    rfl
  funext τ a b
  rw [GlobalTheory.ThetaLatImage.pt_apply]
  show _ = δ * ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T (frT.1 * z * (frS⁻¹).1) τ) *
    GlobalTheory.FockPos.frAt frS τ) a b
  rw [hmap τ, GlobalTheory.ThetaLawOF.coord_back frS frT (fun τ i j => tauE D τ (z i j)) τ]
  rfl

end GlobalTheory.ThetaLawLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFrameCoordsOfMemTorusLatticeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_frameCoords_of_mem_torusLattice : ∀ {D : D7} (S T : HSp D) (frS : GL (Fin S.rank) D.host.E) (frT : GL (Fin T.rank) D.host.E), Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frS.1 * S.gram * frS.1 = 1 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) frT.1 * T.gram * frT.1 = 1 → ∀ δ : ℂ, ∀ x ∈ Formalism.MainNotions.TaylorLogMetric.La D (Formalism.MainNotions.TaylorLogMetric.tor0 D D.host.ccK δ) (Formalism.MainNotions.StandardLatticesGL3.stdL D S.rank) (Formalism.MainNotions.StandardLatticesGL3.stdL D T.rank), ∃ v : Matrix (Fin T.rank) (Fin S.rank) D.host.E, GlobalTheory.VacUnique.finRat S T v ∈ latO S T (colLat frS : Set (Fin S.rank → D.host.E)) (colLat frT : Set (Fin T.rank → D.host.E)) (fun _ => True) ∧ x = δ • (fun τ a b => ((GlobalTheory.FockPos.frAt frT τ)⁻¹ * Matrix.of (GlobalTheory.VacUnique.infRat S T v τ) * GlobalTheory.FockPos.frAt frS τ) a b) := by
  first | exact @GlobalTheory.ThetaLawLat.mem_La_frame | exact GlobalTheory.ThetaLawLat.mem_La_frame | (intros; apply GlobalTheory.ThetaLawLat.mem_La_frame <;> assumption)
end
end
