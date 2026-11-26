module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.AdmissibleParabolicInduction.IrrAdm
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.AdmissibleParabolicInduction.AdmProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.AlmostGoodOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalVolumeRankOneProduct
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermRepTwistedBundleExists
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.DictInf
public import Development.WeilBound.ThetaLifts.SmallCones.SoDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothWeightPullbackChartFormula
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JmThetaHolds

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleParabolicInduction
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleParabolicInduction
namespace GlobalTheory.CompanionTheory.ProdAdm

theorem isAdmissible_multiProd_smIrr (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {c n : ℕ} (N : Fin c → ℕ) (h : ∑ i, N i = n)
    (σ : ∀ i, GlobalTheory.CuspRep.SmIrr (GL (Fin (N i)) k)) :
    GlobalTheory.PRep.IsAdmissible (GlobalTheory.SmGL.multiProd (GlobalTheory.SmGL.stdBlocks N h) fun i => (σ i).ρ) :=
  PositivityTheory.PfBern.Props1.isAdmissible_parInd_of _ _
    (GlobalTheory.ContraProd.isAdmissible_piTensor _ _ fun i =>
      PositivityTheory.PfBern.Props1.irrSmoothAdmissible_holds k (N i) (σ i).V (σ i).ρ (σ i).smooth (σ i).irred)

end GlobalTheory.CompanionTheory.ProdAdm
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdmissibleParabolicInductionStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_parabolic_induction : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {c n : ℕ} (N : Fin c → ℕ) (h : ∑ i, N i = n) (σ : ∀ i, GlobalTheory.CuspRep.SmIrr (GL (Fin (N i)) k)), GlobalTheory.PRep.IsAdmissible (GlobalTheory.SmGL.multiProd (GlobalTheory.SmGL.stdBlocks N h) fun i => (σ i).ρ) := by
  first | exact @GlobalTheory.CompanionTheory.ProdAdm.isAdmissible_multiProd_smIrr | exact GlobalTheory.CompanionTheory.ProdAdm.isAdmissible_multiProd_smIrr | (intros; apply GlobalTheory.CompanionTheory.ProdAdm.isAdmissible_multiProd_smIrr <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveIntertwinerSubrepEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveIntertwinerSubrepEquiv
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZRes

theorem subQuot_bot_equiv_of_bijective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (τ : Representation ℂ G W) (S : Subrepresentation ρ) (O : S.toSubmodule →ₗ[ℂ] W)
    (hO : Function.Bijective O)
    (hi : ∀ (g : G) (v : S.toSubmodule), O ⟨ρ g v, S.apply_mem_toSubmodule g v.2⟩ = τ g (O v)) :
    Nonempty ((subQuot S ⊥).Equiv τ) := by
  have hbot : (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := by
    first
      | rfl
      | simp
      | (ext v; simp)
  have hp : Submodule.comap S.toSubmodule.subtype (⊥ : Subrepresentation ρ).toSubmodule = ⊥ := by
    rw [hbot, Submodule.comap_bot, Submodule.ker_subtype]
  let e := (Submodule.quotEquivOfEqBot _ hp).trans (LinearEquiv.ofBijective O hO)
  refine ⟨Representation.Equiv.mk' ⟨e.toLinearMap, fun g => ?_⟩ e.symm e.left_inv e.right_inv⟩
  refine LinearMap.ext fun x => ?_
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  exact hi g v

end GlobalTheory.CompanionTheory.BZRes
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BijectiveIntertwinerSubrepEquivStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZRes Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_intertwiner_subrep_equiv : ∀ {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G V) (τ : Representation ℂ G W) (S : Subrepresentation ρ) (O : S.toSubmodule →ₗ[ℂ] W), Function.Bijective O → (∀ (g : G) (v : S.toSubmodule), O ⟨ρ g v, S.apply_mem_toSubmodule g v.2⟩ = τ g (O v)) → Nonempty ((subQuot S ⊥).Equiv τ) := by
  first | exact @GlobalTheory.CompanionTheory.BZRes.subQuot_bot_equiv_of_bijective | exact GlobalTheory.CompanionTheory.BZRes.subQuot_bot_equiv_of_bijective | (intros; apply GlobalTheory.CompanionTheory.BZRes.subQuot_bot_equiv_of_bijective <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerExistence
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerExistence
noncomputable section

namespace GlobalTheory.CompanionTheory.LocalUnif

open NumberField IsDedekindDomain HeckeCharacterZeroLocus.SiegelWeilU

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem isUnit_iff_valued_eq_one (x : v.adicCompletionIntegers F) :
    IsUnit x ↔ Valued.v (x : v.adicCompletion F) = 1 := by
  have hv : (Valued.v : Valuation (v.adicCompletion F) _).Integers (v.adicCompletionIntegers F) :=
    ⟨Subtype.coe_injective, fun y => y.2, fun r hr => ⟨⟨r, hr⟩, rfl⟩⟩
  exact hv.isUnit_iff_valuation_eq_one

theorem norm_lt_one_iff_not_isUnit (x : v.adicCompletionIntegers F) :
    ‖(x : v.adicCompletion F)‖ < 1 ↔ ¬ IsUnit x := by
  rw [isUnit_iff_valued_eq_one, Valued.toNormedField.norm_lt_one_iff]
  have h := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 x.2
  exact ⟨ne_of_lt, fun h' => lt_of_le_of_ne h h'⟩

theorem natCard_quotient_span_irreducible {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {ϖ}) = Ideal.absNorm v.asIdeal := by
  rw [← hϖ.maximalIdeal_eq]
  exact GroundTheory.Global.natCard_residueField_adicCompletionIntegers v

theorem unifEx : PositivityTheory.SiegelWeilFormula.Gunr.UnifEx := by
  unfold PositivityTheory.SiegelWeilFormula.Gunr.UnifEx
  intro F _ _ v
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers F)
  refine ⟨ϖ, ?_, ?_, ?_, natCard_quotient_span_irreducible v hϖ⟩
  · intro h
    exact hϖ.ne_zero (Subtype.ext h)
  · exact (norm_lt_one_iff_not_isUnit v ϖ).2 hϖ.not_isUnit
  · intro x hx
    have hm : x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) :=
      (IsLocalRing.mem_maximalIdeal x).2 (mem_nonunits_iff.2 ((norm_lt_one_iff_not_isUnit v x).1 hx))
    rw [hϖ.maximalIdeal_eq] at hm
    exact Ideal.mem_span_singleton.1 hm

end GlobalTheory.CompanionTheory.LocalUnif

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformizerExistenceStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformizer_existence : PositivityTheory.SiegelWeilFormula.Gunr.UnifEx := by
  first | exact @GlobalTheory.CompanionTheory.LocalUnif.unifEx | exact GlobalTheory.CompanionTheory.LocalUnif.unifEx | (intros; apply GlobalTheory.CompanionTheory.LocalUnif.unifEx <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharacterBlockValue
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharacterBlockValue
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS.NuVal

theorem ord_eq_ordL_unit {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))
    (x : (w.adicCompletion E)ˣ) : GlobalTheory.SmGL.ord (w.adicCompletion E) x = ordL (x : w.adicCompletion E) := by
  have h : Valued.v (x : w.adicCompletion E) ≠ 0 := (Valuation.ne_zero_iff _).2 x.ne_zero
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion]
  unfold ordL
  rw [dite_eq_right h]
  congr 1
  conv_lhs => rw [← WithZero.coe_unzero h]
  first | rfl | simp [WithZero.log]

theorem unrChar_twist : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (c : ℂˣ) (i j : ℕ) (m : GLw a w × GLw b w), ordL m.1.val.det = (i : ℤ) → ordL m.2.val.det = (j : ℤ) → (GlobalTheory.SmGL.unrChar (w.adicCompletion E) c ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) = (c : ℂ) ^ (i * b + j * a) := by
  intro E _ _ _ a b w c i j m h1 h2
  have hneg : GlobalTheory.SmGL.unrChar (w.adicCompletion E) c (-1) = 1 := by
    rw [GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.ord_eq_zero (by simp), zpow_zero]
  have hd1 : GlobalTheory.SmGL.unrChar (w.adicCompletion E) c (GeneralLinearGroup.det m.1) = c ^ i := by
    rw [GlobalTheory.SmGL.unrChar_apply, ord_eq_ordL_unit]
    erw [h1]
    simp
  have hd2 : GlobalTheory.SmGL.unrChar (w.adicCompletion E) c (GeneralLinearGroup.det m.2) = c ^ j := by
    rw [GlobalTheory.SmGL.unrChar_apply, ord_eq_ordL_unit]
    erw [h2]
    simp
  rw [map_mul, map_mul, map_pow, map_pow, map_pow, hneg, hd1, hd2, one_pow, one_mul, ← pow_mul, ← pow_mul,
    ← pow_add]
  simp

end GlobalTheory.CompanionTheory.CtS.NuVal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnramifiedCharacterBlockValueStatement
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_character_block_value : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (c : ℂˣ) (i j : ℕ) (m : GLw a w × GLw b w), ordL m.1.val.det = (i : ℤ) → ordL m.2.val.det = (j : ℤ) → (GlobalTheory.SmGL.unrChar (w.adicCompletion E) c ((-1) ^ (a * b) * GeneralLinearGroup.det m.1 ^ b * GeneralLinearGroup.det m.2 ^ a) : ℂ) = (c : ℂ) ^ (i * b + j * a) := by
  first | exact @GlobalTheory.CompanionTheory.CtS.NuVal.unrChar_twist | exact GlobalTheory.CompanionTheory.CtS.NuVal.unrChar_twist | (intros; apply GlobalTheory.CompanionTheory.CtS.NuVal.unrChar_twist <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleReadExists
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleReadExists
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm)
open GlobalTheory.CompanionTheory.MPDict

namespace GlobalTheory.CompanionTheory.MixZ

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem exists_block_ne_zero_of_isUnder {y : CxPts (mpStr ℤ m n) σ₀} {z : (Σ k, Bk n k) → ℂ} (h : IsUnder y z) (k : Fin (m + 1)) :
    ∃ i, z ⟨k, i⟩ ≠ 0 :=
  ⟨ptChart _ k, (h k _).1.1 (CxPts.mem_ptsIn.2 (mem_ptChart _ k))⟩

theorem combLine_unit_a (A : HermLine (Bk n)) : (combLine (fun _ : Unit => A) 1).a = A.a := by
  simp [combLine]

theorem combLine_unit_h (A : HermLine (Bk n)) {z : (Σ k, Bk n k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (combLine (fun _ : Unit => A) 1).h z = A.h z := by
  simp [combLine, if_pos hz]

theorem combLine_unit_h_off (A : HermLine (Bk n)) {z : (Σ k, Bk n k) → ℂ} (hz : ¬ ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    (combLine (fun _ : Unit => A) 1).h z = 0 :=
  if_neg hz

theorem isHermRep_combLine_unit {M : HermLB (mpStr ℤ m n)} {A : HermLine (Bk n)} (hA : IsHermRep M A) :
    IsHermRep M (combLine (fun _ : Unit => A) 1) := by
  obtain ⟨u, h₁, h₂, h₃⟩ := hA
  refine ⟨u, h₁, fun i c c' => ?_, fun i c y z hu hy => ?_⟩
  · rw [combLine_unit_a]
    exact h₂ i c c'
  · rw [combLine_unit_h A (exists_block_ne_zero_of_isUnder hu), combLine_unit_a]
    exact h₃ i c y z hu hy

theorem existsRead : ExistsRead := by
  rintro m n M ⟨c, t, e⟩
  obtain ⟨A, hA, -⟩ := GlobalTheory.T.hermRep_twisted_bundle_exists m n M c t e
  have hs : IsSmoothHerm A := GlobalTheory.CompanionTheory.MPDict.SmoothRep.isSmoothHerm_of_isHermRep m n M A hA
  exact ⟨combLine (fun _ : Unit => A) 1, isSmoothHerm_combLine (fun _ => hs) 1, isHermRep_combLine_unit hA,
    fun z hz => combLine_unit_h_off A hz⟩

end GlobalTheory.CompanionTheory.MixZ
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleReadExistsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_cycle_read_exists : GlobalTheory.CompanionTheory.MixZ.ExistsRead := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.existsRead | exact GlobalTheory.CompanionTheory.MixZ.existsRead | (intros; apply GlobalTheory.CompanionTheory.MixZ.existsRead <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockIntegralIff
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockIntegralIff
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS

theorem blk_val_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ} (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w m X).val = Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val) := by
  have hU : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 m.1.isUnit).mul
      ((Matrix.isUnit_iff_isUnit_det _).1 m.2.isUnit)
  unfold blk
  simp only
  rw [dite_eq_left hU]
  rfl

theorem isInt_blk_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsInt w (blk h w m X).val ↔ IsInt w m.1.val ∧ IsInt w m.2.val ∧ IsInt w (m.1.val * X) := by
  intro E _ _ _ n a b h w m X
  rw [blk_val_eq]
  set e : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr h) with he
  constructor
  · intro H
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using H (e (Sum.inl i)) (e (Sum.inl j))
    · simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using H (e (Sum.inr i)) (e (Sum.inr j))
    · simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using H (e (Sum.inl i)) (e (Sum.inr j))
  · rintro ⟨h1, h2, h3⟩ i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    rcases i with i | i <;> rcases j with j | j
    · simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using h1 i j
    · simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using h3 i j
    · simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using (Ov E w).zero_mem
    · simpa [Matrix.reindex_apply, Matrix.submatrix_apply] using h2 i j

end GlobalTheory.CompanionTheory.CtS
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockIntegralIffStatement
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_integral_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsInt w (blk h w m X).val ↔ IsInt w m.1.val ∧ IsInt w m.2.val ∧ IsInt w (m.1.val * X) := by
  first | exact @GlobalTheory.CompanionTheory.CtS.isInt_blk_iff | exact GlobalTheory.CompanionTheory.CtS.isInt_blk_iff | (intros; apply GlobalTheory.CompanionTheory.CtS.isInt_blk_iff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StdQuotGenericOfStdSubGeneric
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.StdQuot

section Theta

variable {k : Type} [Field k] {N : ℕ}

theorem thetaW_apply (g : GL (Fin N) k) (i j : Fin N) :
    (thetaW k N g).val i j = (g⁻¹).val (Fin.rev j) (Fin.rev i) := by
  simp [thetaW, invT, Matrix.reindexAlgEquiv_apply]

theorem thetaW_mem_unipB {u : GL (Fin N) k} (hu : u ∈ unipB k (Fin N)) : thetaW k N u ∈ unipB k (Fin N) := by
  have hi := (mem_unipB k).1 (inv_mem hu)
  refine (mem_unipB k).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [thetaW_apply]
    exact hi.1 _ _ (Fin.rev_lt_rev.2 hij)
  · rw [thetaW_apply]
    exact hi.2 _

theorem whitChar_thetaW (ψ : AddChar k Circle) (u : unipB k (Fin N)) :
    whitChar ψ N ⟨thetaW k N u, thetaW_mem_unipB u.2⟩ = whitChar ψ N u⁻¹ := by
  show Circle.toUnits (ψ _) = Circle.toUnits (ψ _)
  refine congrArg (fun s => Circle.toUnits (ψ s)) ?_
  refine Finset.sum_nbij' (fun p => (Fin.rev p.2, Fin.rev p.1)) (fun p => (Fin.rev p.2, Fin.rev p.1)) ?_ ?_ ?_ ?_ ?_
  · intro p hp
    have h := (Finset.mem_filter.1 hp).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    simp only [Fin.val_rev]
    have := p.1.2
    have := p.2.2
    omega
  · intro p hp
    have h := (Finset.mem_filter.1 hp).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    simp only [Fin.val_rev]
    have := p.1.2
    have := p.2.2
    omega
  · intro p _
    simp
  · intro p _
    simp
  · intro p _
    simp only [thetaW_apply]
    rfl

theorem whitChar_inv (ψ : AddChar k Circle) (u : unipB k (Fin N)) :
    whitChar ψ⁻¹ N u = whitChar ψ N u⁻¹ := by
  rw [map_inv]
  show Circle.toUnits (ψ⁻¹ _) = (Circle.toUnits (ψ _))⁻¹
  rw [AddChar.inv_apply', map_inv]

end Theta

section Main

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable {k}

variable (k)

end Main

end GlobalTheory.CompanionTheory.StdQuot

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockInverseIntegralIff
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockInverseIntegralIff
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompanionTheory.CtS

theorem blk_inv_val {E : Type} [Field E] [NumberField E] {n a b : ℕ} (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    ((blk h w m X)⁻¹).val =
      reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val) := by
  have a1 : m.1.val * (m.1⁻¹).val = 1 := Units.mul_inv m.1
  have a2 : (m.1⁻¹).val * m.1.val = 1 := Units.inv_mul m.1
  have b1 : m.2.val * (m.2⁻¹).val = 1 := Units.mul_inv m.2
  have b2 : (m.2⁻¹).val * m.2.val = 1 := Units.inv_mul m.2
  have h1 : fromBlocks m.1.val (m.1.val * X) 0 m.2.val *
      fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1
    · simp [a1]
    · simp [Matrix.mul_assoc]
    · simp
    · simp [b1]
  have h2 : fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val *
      fromBlocks m.1.val (m.1.val * X) 0 m.2.val = 1 := by
    rw [fromBlocks_multiply, ← fromBlocks_one]
    congr 1
    · simp [a2]
    · simp [← Matrix.mul_assoc, a2, Matrix.mul_assoc, b2]
    · simp
    · simp [b2]
  have r1 : reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (fromBlocks m.1.val (m.1.val * X) 0 m.2.val) *
      reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val) = 1 := by
    simp only [reindex_apply, submatrix_mul_equiv, h1, submatrix_one_equiv]
  have r2 : reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val) *
      reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (fromBlocks m.1.val (m.1.val * X) 0 m.2.val) = 1 := by
    simp only [reindex_apply, submatrix_mul_equiv, h2, submatrix_one_equiv]
  have hU : IsUnit (reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) := ⟨⟨_, _, r1, r2⟩, rfl⟩
  have hb : (blk h w m X).val = reindex (finSumFinEquiv.trans (finCongr h))
      (finSumFinEquiv.trans (finCongr h)) (fromBlocks m.1.val (m.1.val * X) 0 m.2.val) := by
    unfold blk
    simp only []
    rw [dite_eq_left hU]
    rfl
  exact Units.inv_eq_of_mul_eq_one_right (by rw [hb]; exact r1)

theorem isInt_smul_blk_inv_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (ϖ : w.adicCompletion E) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsInt w (ϖ • ((blk h w m X)⁻¹).val) ↔ IsInt w (ϖ • (m.1⁻¹).val) ∧ IsInt w (ϖ • (m.2⁻¹).val) ∧ IsInt w (ϖ • (X * (m.2⁻¹).val)) := by
  intro E _ _ _ n a b h w ϖ m X
  rw [blk_inv_val h w m X]
  constructor
  · intro H
    have key : ∀ (i j : Fin a ⊕ Fin b), ϖ * fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val i j ∈ Ov E w := by
      intro i j
      have := H (finSumFinEquiv.trans (finCongr h) i) (finSumFinEquiv.trans (finCongr h) j)
      simpa [reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul] using this
    refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_⟩
    · simpa [Matrix.smul_apply, smul_eq_mul] using key (Sum.inl i) (Sum.inl j)
    · simpa [Matrix.smul_apply, smul_eq_mul] using key (Sum.inr i) (Sum.inr j)
    · have := (Ov E w).neg_mem (key (Sum.inl i) (Sum.inr j))
      simpa [Matrix.smul_apply, smul_eq_mul] using this
  · rintro ⟨H1, H2, H3⟩ i j
    have key : ∀ (i j : Fin a ⊕ Fin b), ϖ * fromBlocks (m.1⁻¹).val (-(X * (m.2⁻¹).val)) 0 (m.2⁻¹).val i j ∈ Ov E w := by
      rintro (i | i) (j | j)
      · simpa [Matrix.smul_apply, smul_eq_mul] using H1 i j
      · have := (Ov E w).neg_mem (H3 i j)
        simpa [Matrix.smul_apply, smul_eq_mul] using this
      · simpa using (Ov E w).zero_mem
      · simpa [Matrix.smul_apply, smul_eq_mul] using H2 i j
    simpa [reindex_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul] using
      key ((finSumFinEquiv.trans (finCongr h)).symm i) ((finSumFinEquiv.trans (finCongr h)).symm j)

end GlobalTheory.CompanionTheory.CtS
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockInverseIntegralIffStatement
open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.F.RS GlobalTheory.CompanionTheory.CtS
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_inverse_integral_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (ϖ : w.adicCompletion E) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), IsInt w (ϖ • ((blk h w m X)⁻¹).val) ↔ IsInt w (ϖ • (m.1⁻¹).val) ∧ IsInt w (ϖ • (m.2⁻¹).val) ∧ IsInt w (ϖ • (X * (m.2⁻¹).val)) := by
  first | exact @GlobalTheory.CompanionTheory.CtS.isInt_smul_blk_inv_iff | exact GlobalTheory.CompanionTheory.CtS.isInt_smul_blk_inv_iff | (intros; apply GlobalTheory.CompanionTheory.CtS.isInt_smul_blk_inv_iff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalDictionary
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalDictionary
noncomputable section

namespace GlobalTheory.CompanionTheory.EisDict

open scoped TensorProduct NNReal Matrix NumberField.AdeleRing
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open PositivityTheory.RgEis

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]


variable (F E) in
def sec : (Af F ⊗[F] E) →+ AE F E :=
  (TensorProduct.map (LinearMap.inr F (Ainf F) (Af F)) (LinearMap.id : E →ₗ[F] E)).toAddMonoidHom

theorem sec_tmul (a : Af F) (x : E) : sec F E (a ⊗ₜ[F] x) = ((0, a) : AF F) ⊗ₜ[F] x := rfl

theorem sec_finPart (z : AE F E) : sec F E (HeckeCharacterZeroLocus.ThmBIn.finPart F E z) = finOne F • z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, smul_add]
  | tmul a x =>
    change sec F E (HeckeCharacterZeroLocus.ThmBIn.sndA F a ⊗ₜ[F] x) = _
    rw [sec_tmul, TensorProduct.smul_tmul']
    congr 1
    refine Prod.ext ?_ ?_
    · change (0 : Ainf F) = 0 * a.1
      simp
    · change a.2 = 1 * a.2
      simp

theorem finPart_finOne_smul (z : AE F E) :
    HeckeCharacterZeroLocus.ThmBIn.finPart F E (finOne F • z) = HeckeCharacterZeroLocus.ThmBIn.finPart F E z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy]
  | tmul a x =>
    rw [TensorProduct.smul_tmul']
    change HeckeCharacterZeroLocus.ThmBIn.sndA F (finOne F • a) ⊗ₜ[F] x = HeckeCharacterZeroLocus.ThmBIn.sndA F a ⊗ₜ[F] x
    congr 1
    change 1 * a.2 = a.2
    simp

theorem sec_mem {y : Af F ⊗[F] E} (hy : y ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E) : sec F E y ∈ intHat F E := by
  induction hy using AddSubgroup.closure_induction with
  | mem y h =>
    obtain ⟨a, ha, x, rfl⟩ := h
    refine AddSubgroup.subset_closure ⟨(0, a), ?_, fun v => ha v, x, ?_⟩
    · exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)
    · rw [sec_tmul]
      change _ = pairA F 0 a • ((1 : AF F) ⊗ₜ[F] (x : E))
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rfl
  | zero => simpa using (intHat F E).zero_mem
  | add x y _ _ hx hy => simpa using (intHat F E).add_mem hx hy
  | neg x _ hx => simpa using (intHat F E).neg_mem hx

theorem finPart_mem {z : AE F E} (hz : z ∈ intHat F E) : HeckeCharacterZeroLocus.ThmBIn.finPart F E z ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  induction hz using AddSubgroup.closure_induction with
  | mem z h =>
    obtain ⟨a, -, ha, o, rfl⟩ := h
    refine AddSubgroup.subset_closure ⟨HeckeCharacterZeroLocus.ThmBIn.sndA F a, fun v => ha v, o, ?_⟩
    change HeckeCharacterZeroLocus.ThmBIn.finPart F E (a • ((1 : AF F) ⊗ₜ[F] (o : E))) = _
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rfl
  | zero => simpa using (HeckeCharacterZeroLocus.ThmBIn.intAE F E).zero_mem
  | add x y _ _ hx hy => simpa using (HeckeCharacterZeroLocus.ThmBIn.intAE F E).add_mem hx hy
  | neg x _ hx => simpa using (HeckeCharacterZeroLocus.ThmBIn.intAE F E).neg_mem hx

theorem mem_intAd_iff (z : AE F E) :
    eqv F E z ∈ intAd E ↔ HeckeCharacterZeroLocus.ThmBIn.finPart F E z ∈ HeckeCharacterZeroLocus.ThmBIn.intAE F E := by
  rw [GroundTheory.BlockD.ThmBHecke.mem_intAE_iff, ← GroundTheory.BlockD.ThmBHecke.adeleEquiv_snd,
    GroundTheory.Global.mem_integralFiniteAdeles]
  simp only [intAd, Subring.mem_iInf, Subring.mem_comap]
  rfl

theorem dict : Dict := by
  intro F E _ _ _ _ _
  refine ⟨GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv, GroundTheory.BlockD.ThmBHecke.continuous_adeleEquiv_symm,
    GroundTheory.BlockD.ThmBHecke.adeleEquiv_incA, fun z => ?_, fun x => ?_⟩
  · rw [mem_intAd_iff]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [← sec_finPart]
      exact sec_mem h
    · rw [← finPart_finOne_smul]
      exact finPart_mem h
  · exact (PositivityTheory.ThKCT.Tate.absE_eq x).symm

end GlobalTheory.CompanionTheory.EisDict
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGlobalDictionaryStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_global_dictionary : PositivityTheory.RgEis.Dict := by
  first | exact @GlobalTheory.CompanionTheory.EisDict.dict | exact GlobalTheory.CompanionTheory.EisDict.dict | (intros; apply GlobalTheory.CompanionTheory.EisDict.dict <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicFreeVectorsSameGram
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicFreeVectorsSameGram
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeTrans

section Form

variable {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J : Matrix (Fin n) (Fin n) A)

theorem hform_add_right (x y z : Fin n → A) :
    hform s J x (y + z) = hform s J x y + hform s J x z := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_add_left (x y z : Fin n → A) :
    hform s J (x + y) z = hform s J x z + hform s J y z := by
  simp only [hform, Pi.add_apply, map_add (f := _), add_mul, Finset.sum_add_distrib]

theorem hform_smul_right (t : A) (x y : Fin n → A) :
    hform s J x (t • y) = t * hform s J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_smul_left (t : A) (x y : Fin n → A) :
    hform s J (t • x) y = s t * hform s J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Form

theorem exists_hyperbolic_partner {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) (R : Type) [CommRing R] [Algebra F R] (x y : Fin M → R ⊗[F] E)
    (hxx : hR R σ J x x = 0) (hxy : hR R σ J x y = 1) :
    ∃ y₁ : Fin M → R ⊗[F] E, hR R σ J x y₁ = 1 ∧ hR R σ J y₁ x = 1 ∧ hR R σ J y₁ y₁ = 0 := by
  have herm : ∀ u v : Fin M → R ⊗[F] E, sigR R σ (hR R σ J u v) = hR R σ J v u := by
    intro u v
    have h : ∀ a b, sigR R σ (gramR R σ J ![u, v] b a) = gramR R σ J ![u, v] a b :=
      GlobalTheory.CompanionTheory.SW.HermTop.gramR_mem R (GlobalTheory.CompanionTheory.SW.HermTop.sigma_sigma hσ) hJ.1 ![u, v]
    simpa [gramR] using h 1 0
  have hyx : hR R σ J y x = 1 := by rw [← herm, hxy, map_one]
  set c : R ⊗[F] E := algebraMap F (R ⊗[F] E) (1 / 2) with hc
  have hcc : c + c = 1 := by
    rw [hc, ← map_add (f := _), ← map_one (algebraMap F (R ⊗[F] E))]
    norm_num
  have hsc : sigR R σ c = c := AlgHom.commutes (Algebra.TensorProduct.map (AlgHom.id F R) σ) _
  set q := hR R σ J y y with hq
  have hsq : sigR R σ q = q := herm y y
  refine ⟨y + (-(c * q)) • x, ?_, ?_, ?_⟩
  · have : hR R σ J x (y + (-(c * q)) • x) = hR R σ J x y + -(c * q) * hR R σ J x x := by
      simp only [hR, hform_add_right, hform_smul_right]
    rw [this, hxx, hxy]
    ring
  · have : hR R σ J (y + (-(c * q)) • x) x =
        hR R σ J y x + sigR R σ (-(c * q)) * hR R σ J x x := by
      simp only [hR, hform_add_left, hform_smul_left]
    rw [this, hxx, hyx]
    ring
  · have : hR R σ J (y + (-(c * q)) • x) (y + (-(c * q)) • x) =
        hR R σ J y y + -(c * q) * hR R σ J y x + (sigR R σ (-(c * q)) * hR R σ J x y +
          sigR R σ (-(c * q)) * (-(c * q) * hR R σ J x x)) := by
      simp only [hR, hform_add_left, hform_add_right, hform_smul_left, hform_smul_right]
      ring
    rw [this, hxx, hxy, hyx, ← hq, map_neg, map_mul, hsc, hsq]
    linear_combination (-q) * hcc

theorem transitive_free_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ X Y : Fin 1 → Fin M → R ⊗[F] E, LinearIndependent (R ⊗[F] E) X → LinearIndependent (R ⊗[F] E) Y → gramR R σ J X = 0 → gramR R σ J Y = 0 → ∃ h : HA R σ J, actW R σ J h X = Y := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hL X Y hX hY gX gY
  haveI : IsArtinianRing R := hL.2.2.2.2.1
  haveI : IsReduced R := hL.2.2.2.2.2.1
  have hconst : ∀ Z : Fin 1 → Fin M → R ⊗[F] E, (fun _ : Fin 1 => Z 0) = Z := by
    intro Z
    funext a
    rw [Subsingleton.elim a 0]
  have hlx : LinearIndependent (R ⊗[F] E) (fun _ : Fin 1 => X 0) := by rwa [hconst]
  have hly : LinearIndependent (R ⊗[F] E) (fun _ : Fin 1 => Y 0) := by rwa [hconst]
  have hxx : hR R σ J (X 0) (X 0) = 0 := congrFun (congrFun gX 0) 0
  have hyy : hR R σ J (Y 0) (Y 0) = 0 := congrFun (congrFun gY 0) 0
  obtain ⟨y, hy⟩ := GlobalTheory.T.hermitian_form_primitive_vector_pairing F E σ hσ M J hJ R hL (X 0) hlx
  obtain ⟨y', hy'⟩ := GlobalTheory.T.hermitian_form_primitive_vector_pairing F E σ hσ M J hJ R hL (Y 0) hly
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_hyperbolic_partner hσ hJ R (X 0) y hxx hy
  obtain ⟨u', hu1', hu2', hu3'⟩ := exists_hyperbolic_partner hσ hJ R (Y 0) y' hyy hy'
  have hG : gramR R σ J ![X 0, u] = !![0, 1; 1, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [gramR, hxx, hu1, hu2, hu3]
  have hG' : gramR R σ J ![Y 0, u'] = !![0, 1; 1, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [gramR, hyy, hu1', hu2', hu3']
  have hdet : IsUnit (gramR R σ J ![X 0, u]).det := by
    rw [hG, Matrix.det_fin_two_of]
    simp
  obtain ⟨h, hh⟩ := GlobalTheory.T.witt_extension_artinian_ring F E σ hσ M J hJ R 2 ![X 0, u] ![Y 0, u'] (hG.trans hG'.symm) hdet
  refine ⟨h, ?_⟩
  funext a
  rw [Subsingleton.elim a 0]
  simpa [actW, actTup] using congrFun hh 0

end GlobalTheory.CompanionTheory.WeilSiegel.FreeTrans
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicFreeVectorsSameGramStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_free_vectors_same_gram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ X Y : Fin 1 → Fin M → R ⊗[F] E, LinearIndependent (R ⊗[F] E) X → LinearIndependent (R ⊗[F] E) Y → gramR R σ J X = 0 → gramR R σ J Y = 0 → ∃ h : HA R σ J, actW R σ J h X = Y := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.FreeTrans.transitive_free_isotropic | exact GlobalTheory.CompanionTheory.WeilSiegel.FreeTrans.transitive_free_isotropic | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.FreeTrans.transitive_free_isotropic <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanLocalGlobalDictionary
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanLocalGlobalDictionary
set_option maxSynthPendingDepth 1

noncomputable section

namespace GlobalTheory.CompanionTheory.RgEis

open scoped TensorProduct NumberField.AdeleRing NumberField.LiesOver
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels PositivityTheory.RgEis GroundTheory.Automorphic.Reduction

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem embedding_comp [IsTotallyReal F] (w : InfinitePlace E) :
    w.embedding.comp (algebraMap F E) = (w.comap (algebraMap F E)).embedding := by
  conv_rhs => rw [← w.mk_embedding, InfinitePlace.comap_mk]
  exact (InfinitePlace.embedding_mk_eq_of_isReal
    (InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal _))).symm

def embOf [IsTotallyReal F] (w : InfinitePlace E) : EmbOver E (w.comap (algebraMap F E)) :=
  ⟨w.embedding, embedding_comp w⟩

theorem conj_ext [IsTotallyReal F] (w : InfinitePlace F) (a : w.Completion) :
    starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w a) =
      InfinitePlace.Completion.extensionEmbedding w a := by
  have hr : w.IsReal := IsTotallyReal.isReal w
  rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hr, Complex.conj_ofReal]

theorem ext_algebraMap [IsTotallyReal F] (w : InfinitePlace E) (a : (w.comap (algebraMap F E)).Completion) :
    InfinitePlace.Completion.extensionEmbedding w (algebraMap _ w.Completion a) =
      InfinitePlace.Completion.extensionEmbedding (w.comap (algebraMap F E)) a := by
  have c1 : Continuous fun a : (w.comap (algebraMap F E)).Completion =>
      InfinitePlace.Completion.extensionEmbedding w (algebraMap _ w.Completion a) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp
      (continuous_algebraMap _ _)
  have c2 := (InfinitePlace.Completion.isometry_extensionEmbedding (w.comap (algebraMap F E))).continuous
  refine congrFun ((InfinitePlace.Completion.denseRange_coe (w.comap (algebraMap F E))).equalizer c1 c2
    (funext fun x => ?_)) a
  obtain ⟨k, rfl⟩ := (WithAbs.equiv (w.comap (algebraMap F E)).1).symm.surjective x
  simp only [Function.comp_apply]
  have hk : ((WithAbs.equiv (w.comap (algebraMap F E)).1).symm k : (w.comap (algebraMap F E)).Completion) = algebraMap F (w.comap (algebraMap F E)).Completion k := by
    rw [InfinitePlace.Completion.algebraMap_apply]
    rfl
  rw [hk]
  change InfinitePlace.Completion.extensionEmbedding w (algebraMap _ w.Completion
      (algebraMap F (w.comap (algebraMap F E)).Completion k)) =
    InfinitePlace.Completion.extensionEmbedding (w.comap (algebraMap F E))
      (algebraMap F (w.comap (algebraMap F E)).Completion k)
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply F E]
  have e1 : InfinitePlace.Completion.extensionEmbedding w (algebraMap E w.Completion (algebraMap F E k)) =
      w.embedding (algebraMap F E k) :=
    by simpa [InfinitePlace.Completion.algebraMap_apply] using
      InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm (algebraMap F E k))
  have e2 : InfinitePlace.Completion.extensionEmbedding (w.comap (algebraMap F E))
      (algebraMap F (w.comap (algebraMap F E)).Completion k) = (w.comap (algebraMap F E)).embedding k :=
    by simpa [InfinitePlace.Completion.algebraMap_apply] using
      InfinitePlace.Completion.extensionEmbedding_coe _ ((WithAbs.equiv (w.comap (algebraMap F E)).1).symm k)
  rw [e1, e2]
  exact RingHom.congr_fun (embedding_comp w) k

theorem phi_eqv [IsTotallyReal F] (w : InfinitePlace E) (z : AE F E) :
    (adStd E).φ w (eqv F E z) = piInf (embOf w) z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x =>
    have e : eqv F E (a ⊗ₜ x) = algebraMap E 𝔸[E] x * GroundTheory.Global.AdeleBaseChange.adeleMap F E a :=
      GroundTheory.BlockD.ThmBHecke.adeleEquiv_tmul a x
    rw [e, map_mul]
    change _ * InfinitePlace.Completion.extensionEmbedding w (algebraMap _ w.Completion (a.1 (w.comap (algebraMap F E)))) =
      InfinitePlace.Completion.extensionEmbedding (w.comap (algebraMap F E)) (a.1 (w.comap (algebraMap F E))) * w.embedding x
    rw [ext_algebraMap, mul_comm]
    congr 1
    change InfinitePlace.Completion.extensionEmbedding w ((algebraMap E 𝔸[E] x).1 w) = w.embedding x
    rw [AdeleRing.algebraMap_fst_apply]
    exact InfinitePlace.Completion.extensionEmbedding_coe w ((WithAbs.equiv w.1).symm x)

theorem piInf_cA [IsTotallyReal F] {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w)
    (z : AE F E) : piInf τ (cA σ z) = starRingEnd ℂ (piInf τ z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]
  | tmul a x =>
    change InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 (σ x) =
      starRingEnd ℂ (InfinitePlace.Completion.extensionEmbedding w (a.1 w) * τ.1 x)
    rw [map_mul, conj_ext, h.2.2.2]
    rfl

theorem place_cases [IsTotallyReal F] {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (w' : InfinitePlace E)
    {w : InfinitePlace F} (hv : w'.comap (algebraMap F E) = w) (τ : EmbOver E w) :
    (∀ z, piInf τ z = (adStd E).φ w' (eqv F E z)) ∨
      ∀ z, piInf τ z = starRingEnd ℂ ((adStd E).φ w' (eqv F E z)) := by
  subst hv
  rcases infEmb_eq_or_conj h (embOf w') τ with e | e
  · refine Or.inl fun z => ?_
    rw [phi_eqv]
    exact RingHom.congr_fun e (compInf F E _ z)
  · refine Or.inr fun z => ?_
    rw [phi_eqv]
    exact RingHom.congr_fun e (compInf F E _ z)

theorem dictInf : DictInf := by
  intro F E _ _ _ _ _ σ h
  have := h.1
  refine ⟨fun w z => ?_, fun τ => ⟨fun w => ?_, fun w' => ⟨w'.comap (algebraMap F E), place_cases h w' rfl _⟩⟩⟩
  · rw [phi_eqv, phi_eqv]
    exact piInf_cA h _ z
  · refine ⟨InfinitePlace.mk (τ w).1, place_cases h _ ?_ (τ w)⟩
    rw [InfinitePlace.comap_mk, (τ w).2, InfinitePlace.mk_embedding]

end GlobalTheory.CompanionTheory.RgEis
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanLocalGlobalDictionaryStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_local_global_dictionary : PositivityTheory.RgEis.DictInf := by
  first | exact @GlobalTheory.CompanionTheory.RgEis.dictInf | exact GlobalTheory.CompanionTheory.RgEis.dictInf | (intros; apply GlobalTheory.CompanionTheory.RgEis.dictInf <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetThetaReverseBlocks
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetThetaReverseBlocks
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL Zc.Cos GlobalTheory.CompanionTheory.ThetaProd

namespace GlobalTheory.CompanionTheory.JacTheta

theorem nonempty_jac_comp_thetaW : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    Nonempty ((GlobalTheory.SmGL.jac (stdBlocks d hd) (π.comp (thetaW k N))).Equiv
      ((GlobalTheory.SmGL.jac (stdBlocks (fun a => d (Fin.rev a)) hd') π).comp (thetaL d))) := by
  intro k _ _ _ _ h N d hd hd' V _ _ π
  exact ⟨GlobalTheory.CompanionTheory.JmThetaInv.jacCompThetaW d hd hd' π⟩

end GlobalTheory.CompanionTheory.JacTheta
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetThetaReverseBlocksStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL Zc.Cos GlobalTheory.CompanionTheory.ThetaProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_theta_reverse_blocks : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (h N : ℕ) (d : Fin h → ℕ) (hd : ∑ a, d a = N) (hd' : ∑ a, d (Fin.rev a) = N)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    Nonempty ((GlobalTheory.SmGL.jac (stdBlocks d hd) (π.comp (thetaW k N))).Equiv
      ((GlobalTheory.SmGL.jac (stdBlocks (fun a => d (Fin.rev a)) hd') π).comp (thetaL d))) := by
  first | exact @GlobalTheory.CompanionTheory.JacTheta.nonempty_jac_comp_thetaW | exact GlobalTheory.CompanionTheory.JacTheta.nonempty_jac_comp_thetaW | (intros; apply GlobalTheory.CompanionTheory.JacTheta.nonempty_jac_comp_thetaW <;> assumption)
end
end
