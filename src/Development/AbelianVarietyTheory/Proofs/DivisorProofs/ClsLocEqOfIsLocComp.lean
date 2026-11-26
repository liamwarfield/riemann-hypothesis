module

public import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LandherrHasse
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingSumGLConvergentLValue
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselToJacobiFlatMapVacuumAtGoodPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductOfLocalLevelsUnitaryIsOpenIsCompactIsLeve
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelExistsAfterBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMaxCompactGLOfCommuteEtaleCharpolyBounded
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftWeightSizesEventuallyAlongFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulHomInjective
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticPowOfRestrictsToQuadraticSig
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CapelliOfGelfand

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsLocEqOfIsLocComp
open NumberField IsDedekindDomain ValuativeRel Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SatakeFlip GlobalTheory.CuspRep GlobalTheory.CuspRep.ParLawsT
open GlobalTheory.Mem.Chr hiding HChar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CuspRep.ParLawsT

variable {E Ω : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {a : ℕ}

theorem locParT_eq_of_isLocComp (hT : UpperTheory.Zero.LLC.RecTExists) {π : CuspSub E a} {σ : SmIrr (GL (Fin a) (w.adicCompletion E))}
    (hσ : π.IsLocComp w σ) (h : IsPlaceOver A w) :
    locParT hT (CG.mk π) h = locRecT hT h (cls (ParLaws.toRep σ)) := by
  have h1 : (CG.mk π).IsLoc w (Quotient.mk _ σ) := hσ
  rw [locParT, CG.IsLoc.unique E a _ w _ _ h1.loc h1]
  rfl

theorem cls_loc_eq_of_isLocComp {π : CuspSub E a} {σ : SmIrr (GL (Fin a) (w.adicCompletion E))} (hσ : π.IsLocComp w σ) :
    (⟨a, ParLaws.toCl ((CG.mk π).loc w)⟩ : IrrGL (k := w.adicCompletion E)) = cls (ParLaws.toRep σ) := by
  have h1 : (CG.mk π).IsLoc w (Quotient.mk _ σ) := hσ
  rw [CG.IsLoc.unique E a _ w _ _ h1.loc h1]
  rfl

theorem locParT_ofChar_eq (hT : UpperTheory.Zero.LLC.RecTExists) (χ : HChar E) (h : IsPlaceOver A w) :
    locParT hT (CG.ofChar χ) h = locRecT hT h (.ofChar (χ.loc w) (ParLaws.isSmoothChar_loc χ w)) :=
  locParT_eq_of_isLocComp hT (CG.isLoc_ofChar χ w) h

end GlobalTheory.CuspRep.ParLawsT

theorem GlobalTheory.CuspRep.ParLawsT.locParT_twist : ∀ (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hT : UpperTheory.Zero.LLC.RecTExists) (E Ω : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (π : CG E a) (χ : HChar E) (h : IsPlaceOver A w), UpperTheory.Zero.LLC.Good (⟨a, ParLaws.toCl (π.loc w)⟩ : IrrGL (k := w.adicCompletion E)) → locParT hT (π.twist χ) h = (locParT hT π h).lpChar (locParT hT (CG.ofChar χ) h) := by
  intro hF hT E Ω _ _ _ _ _ _ A w a π χ h hg
  induction π using Quotient.inductionOn with | _ π =>
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  obtain ⟨_, _, H⟩ := isRecT_locRecT hT h
  have hg' : UpperTheory.Zero.LLC.Good (cls (ParLaws.toRep σ)) := cls_loc_eq_of_isLocComp hσ ▸ hg
  refine (locParT_eq_of_isLocComp hT (hσ.twist χ) h).trans ?_
  rw [locParT_ofChar_eq, show locParT hT (Quotient.mk _ π) h = _ from locParT_eq_of_isLocComp hT hσ h, ← H.twist _ _ _ hg']
  exact congrArg _ (IrrGL.tw_of σ.ρ σ.smooth σ.irred _ _).symm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeToLevelOfDvdTrueDGam
noncomputable section

namespace GlobalTheory.DGamOnRecord

open Formalism.BasicNotions Formalism.MainNotions NumberField
open Formalism.L2.Col (Sp hStd autLat PosStar)
open Formalism.HermitianLatticesTheory (isom IsUnimodular)
open GlobalTheory.Mem.Col2 (DGam autOrd autO gamOrd gamRanks)

section Transport

variable {E : Type} [Field E] [NumberField E] [StarRing E]
  {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
  {V' : Type} [AddCommGroup V'] [Module E V'] [Module (𝓞 E) V'] [IsScalarTower (𝓞 E) E V']


omit [StarRing E] in
theorem card_dvd_of_minkMult {n N M : ℕ} (hM : MinkMult N M) (hN : Module.finrank ℚ E * n ≤ N)
    (G : Subgroup (Sp E n ≃ₗ[E] Sp E n)) [Finite G] : Nat.card G ∣ M := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  have hr : Module.finrank ℚ (Sp E n × (Fin k → ℚ)) = Module.finrank ℚ E * n + k := by
    rw [Module.finrank_prod, ← Module.finrank_mul_finrank ℚ E (Sp E n)]
    simp
  let b := Module.finBasisOfFinrankEq ℚ _ hr
  let r : G →* Module.End ℚ (Sp E n × (Fin k → ℚ)) :=
    { toFun := fun g => ((g.1 : Sp E n →ₗ[E] Sp E n).restrictScalars ℚ).prodMap LinearMap.id
      map_one' := LinearMap.ext fun _ => rfl
      map_mul' := fun _ _ => LinearMap.ext fun _ => rfl }
  have hr : Function.Injective r := fun g h hgh =>
    Subtype.ext (LinearEquiv.ext fun x => congrArg Prod.fst (LinearMap.congr_fun hgh (x, 0)))
  let φ : G →* Matrix.GeneralLinearGroup (Fin (Module.finrank ℚ E * n + k)) ℚ :=
    ((LinearMap.toMatrixAlgEquiv b).toMulEquiv.toMonoidHom.comp r).toHomUnits
  have hφ : Function.Injective φ := fun g h hgh =>
    hr ((LinearMap.toMatrixAlgEquiv b).injective (congrArg Units.val hgh))
  have e := MonoidHom.ofInjective hφ
  rw [Nat.card_congr e.toEquiv]
  exact hM φ.range (Finite.of_equiv _ e.toEquiv)

end Transport

end GlobalTheory.DGamOnRecord

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureCballZpow
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell

namespace GlobalTheory.OrdShellInt

end GlobalTheory.OrdShellInt

namespace GlobalTheory.OrdShellInt

end GlobalTheory.OrdShellInt

namespace GlobalTheory.OrdShellInt

open ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_le_iff_ord (x s : kˣ) : valuation k (x : k) ≤ valuation k (s : k) ↔ ord k s ≤ ord k x := by
  unfold ord
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  rw [neg_le_neg_iff, WithZero.log_le_log (by simp) (by simp), map_le_map_iff]

theorem ord_zpow (x : kˣ) (n : ℤ) : ord k (x ^ n) = n * ord k x := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  have h := map_zpow o x n
  have h2 : Multiplicative.toAdd (o (x ^ n)) = Multiplicative.toAdd ((o x) ^ n) := by rw [h]
  simpa [o, toAdd_zpow] using h2

end GlobalTheory.OrdShellInt

namespace GlobalTheory.OrdShellInt

open ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable [MeasurableSpace k] [BorelSpace k]

end GlobalTheory.OrdShellInt

namespace GlobalTheory.OrdShellInt

open ValuativeRel

end GlobalTheory.OrdShellInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDomainTensorComplex
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct

namespace GlobalTheory.TensorFields

theorem exists_finset_lift {k κ K : Type} [Field k] [Field κ] [Field K] [Algebra k κ] [Algebra k K]
    (x : κ ⊗[k] K) : ∃ S : Finset K, ∀ T : Finset K, S ⊆ T →
      ∃ x' : κ ⊗[k] (Algebra.adjoin k (T : Set K)),
        Algebra.TensorProduct.map (AlgHom.id k κ) (Algebra.adjoin k (T : Set K)).val x' = x := by
  classical
  obtain ⟨P, rfl⟩ := TensorProduct.exists_finset x
  refine ⟨P.image Prod.snd, fun T hT => ?_⟩
  refine ⟨∑ i ∈ P.attach, i.1.1 ⊗ₜ[k] (⟨i.1.2, Algebra.subset_adjoin
    (hT (Finset.mem_image_of_mem Prod.snd i.2))⟩ : Algebra.adjoin k (T : Set K)), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, Subalgebra.coe_val]
  exact Finset.sum_attach P (fun i => i.1 ⊗ₜ[k] i.2)

theorem isDomain_tensor_complex : ∀ (K κ : Type) [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ],
    IsDomain (K ⊗[ℂ] κ) := by
  classical
  intro K κ _ _ _ _
  suffices h : IsDomain (κ ⊗[ℂ] K) from (Algebra.TensorProduct.comm ℂ K κ).toMulEquiv.isDomain
  haveI : Nontrivial (κ ⊗[ℂ] K) := inferInstance
  refine @NoZeroDivisors.to_isDomain _ _ _ ⟨fun {x y} hxy => ?_⟩
  obtain ⟨S₁, h₁⟩ := exists_finset_lift (k := ℂ) x
  obtain ⟨S₂, h₂⟩ := exists_finset_lift (k := ℂ) y
  let A := Algebra.adjoin ℂ ((S₁ ∪ S₂ : Finset K) : Set K)
  obtain ⟨x', hx'⟩ := h₁ (S₁ ∪ S₂) Finset.subset_union_left
  obtain ⟨y', hy'⟩ := h₂ (S₁ ∪ S₂) Finset.subset_union_right
  haveI : Algebra.FiniteType ℂ A := ⟨(Subalgebra.fg_top _).mpr (Subalgebra.fg_adjoin_finset _)⟩
  haveI : IsDomain A := inferInstance
  haveI : IsDomain (κ ⊗[ℂ] A) := GlobalTheory.GeomComp.isDomain_tensor_of_isAlgClosed ℂ A κ
  let φ := Algebra.TensorProduct.map (AlgHom.id ℂ κ) A.val
  have hφ : Function.Injective φ :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := κ) A.val.toLinearMap Subtype.val_injective
  have h0 : x' * y' = 0 := hφ (by rw [map_mul, hx', hy', hxy, map_zero])
  rcases mul_eq_zero.mp h0 with h | h
  · left; rw [← hx', h, map_zero]
  · right; rw [← hy', h, map_zero]

end GlobalTheory.TensorFields
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSystemHilbertFunctionEqFinrankConePiece
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSystemHilbertFunctionEqFinrankConePiece
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt GlobalTheory.DegCmp Filter
open scoped ENNReal

namespace GlobalTheory.DegCmp

theorem rank_map_eq_of_ker_iff {K M A B : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup A] [Module K A]
    [AddCommGroup B] [Module K B] (S : Submodule K M) (f : M →ₗ[K] A) (g : M →ₗ[K] B)
    (h : ∀ x ∈ S, f x = 0 ↔ g x = 0) :
    Module.rank K (S.map f) = Module.rank K (S.map g) := by
  have hk : LinearMap.ker (f.domRestrict S) = LinearMap.ker (g.domRestrict S) := by
    ext x
    simpa using h x x.2
  rw [← LinearMap.range_domRestrict, ← LinearMap.range_domRestrict,
    ← (LinearMap.quotKerEquivRange _).rank_eq, ← (LinearMap.quotKerEquivRange _).rank_eq, hk]

theorem range_pow_eq_map_homogeneous {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) {N : ℕ} (b : Module.Basis (Fin N) K V) (τ : ℕ) :
    ((LinearMap.range ev) ^ τ : Submodule K Ω) =
      (homogeneousSubmodule (Fin N) K τ).map (aeval (fun j => ev (b j)) : MvPolynomial (Fin N) K →ₐ[K] Ω).toLinearMap := by
  rw [← homogeneousSubmodule_one_pow, Submodule.map_pow, homogeneousSubmodule_one_eq_span_X, Submodule.map_span,
    LinearMap.range_eq_map, ← b.span_eq, Submodule.map_span, ← Set.range_comp, ← Set.range_comp]
  congr 3
  ext j
  simp

theorem hilb_eq_finrank_quotPiece : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (N : ℕ) (b : Module.Basis (Fin N) K V) (τ : ℕ), hilb ev τ = ((Module.finrank K (GlobalTheory.quotPiece (imageIdeal ev b) (τ : ℤ)) : ℕ) : ℕ∞) := by
  intro K V Ω _ _ _ _ _ ev N b τ
  rw [hilb, range_pow_eq_map_homogeneous ev b τ, GlobalTheory.quotPiece_natCast,
    rank_map_eq_of_ker_iff _ _ (Ideal.Quotient.mkₐ K (imageIdeal ev b)).toLinearMap, ← Module.finrank_eq_rank]
  · simp
  · intro x hx
    simp only [AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact (mem_coneIdeal_of_isHomogeneous _ hx).symm

end GlobalTheory.DegCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearSystemHilbertFunctionEqFinrankConePieceStatement
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt GlobalTheory.DegCmp Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearSystemHilbertFunction_eq_finrank_conePiece : ∀ (K V Ω : Type) [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω] (ev : V →ₗ[K] Ω) (N : ℕ) (b : Module.Basis (Fin N) K V) (τ : ℕ), hilb ev τ = ((Module.finrank K (GlobalTheory.quotPiece (imageIdeal ev b) (τ : ℤ)) : ℕ) : ℕ∞) := by
  first | exact @GlobalTheory.DegCmp.hilb_eq_finrank_quotPiece | exact GlobalTheory.DegCmp.hilb_eq_finrank_quotPiece | (intros; apply GlobalTheory.DegCmp.hilb_eq_finrank_quotPiece <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentConjLeviEqBlockUpperTwistedSylvester
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentConjLeviEqBlockUpperTwistedSylvester
noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LeviDesc.LeviBlockConjugation

theorem blk_val {E : Type} [Field E] [NumberField E] {n a b : ℕ} (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w m X).val = Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val) := by
  have hU : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
    exact (m.1.isUnit.map Matrix.detMonoidHom).mul (m.2.isUnit.map Matrix.detMonoidHom)
  unfold blk
  simp only [dif_pos hU, IsUnit.unit_spec]

theorem conj_blk (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    (blk h w 1 X)⁻¹ * blk h w m 0 * blk h w 1 X = blk h w m (GlobalTheory.LeviDesc.adL m.1 m.2.val X) := by
  rw [mul_assoc, inv_mul_eq_iff_eq_mul]
  ext : 1
  simp only [Units.val_mul, blk_val, Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  congr 1
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Prod.fst_one, Prod.snd_one, Units.val_one, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, Matrix.fromBlocks_inj, true_and, and_true]
  simp only [adL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_sub, ← Matrix.mul_assoc]
  rw [show m.1.val * (m.1⁻¹ : GL (Fin a) _).val = 1 from by simp]
  simp [Matrix.one_mul, add_sub_cancel]

end GlobalTheory.LeviDesc.LeviBlockConjugation
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentConjLeviEqBlockUpperTwistedSylvesterStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_conj_levi_eq_blockUpperTwistedSylvester : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)), (blk h w 1 X)⁻¹ * blk h w m 0 * blk h w 1 X = blk h w m (GlobalTheory.LeviDesc.adL m.1 m.2.val X) := by
  first | exact @GlobalTheory.LeviDesc.LeviBlockConjugation.conj_blk | exact GlobalTheory.LeviDesc.LeviBlockConjugation.conj_blk | (intros; apply GlobalTheory.LeviDesc.LeviBlockConjugation.conj_blk <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPolarisedTopChernCoeffLeOfWeightedBound
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPolarisedTopChernCoeffLeOfWeightedBound
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem norm_mixTop_le_of_weighted : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (w : Fin n → ℝ) (c : ℝ), (∀ a, 0 < w a) → (∀ i a b p q, ‖K i a b p q‖ * (w a * w b) ≤ c) → ‖mixTop K‖ ≤ (Fintype.card r : ℝ) ^ n * (n.factorial : ℝ) ^ 2 * |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 := by
  intro n r _ _ K w c hw hK
  set D : ℝ := (n.factorial : ℝ) * |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 with hD
  have hs : ∀ σ : Equiv.Perm (Fin n), ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
    intro σ
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  have hterm : ∀ (p : Fin n → r) (π u : Equiv.Perm (Fin n)),
      ‖((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => K i (u i) b (p i) (p (π i))).det‖ ≤ D := by
    intro p π u
    rw [norm_mul, norm_mul, hs, hs, one_mul, one_mul]
    exact GlobalTheory.T.norm_det_le_of_weighted_entry_bound _ u w c hw (fun i b => by simpa using hK i (u i) b (p i) (p (π i)))
  have hsum : ‖∑ p : Fin n → r, ∑ π : Equiv.Perm (Fin n), ∑ u : Equiv.Perm (Fin n),
      ((Equiv.Perm.sign π : ℤ) : ℂ) * ((Equiv.Perm.sign u : ℤ) : ℂ) *
        (Matrix.of fun i b => K i (u i) b (p i) (p (π i))).det‖ ≤
      (Fintype.card r : ℝ) ^ n * ((n.factorial : ℝ) * ((n.factorial : ℝ) * D)) := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun p _ => (norm_sum_le _ _).trans
      (Finset.sum_le_sum fun π _ => (norm_sum_le _ _).trans
        (Finset.sum_le_sum fun u _ => hterm p π u))).trans ?_
    simp [Finset.sum_const, Fintype.card_perm, Fintype.card_fun]
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  unfold mixTop
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (n.factorial : ℝ)⁻¹ * ‖_‖ ≤ (n.factorial : ℝ)⁻¹ *
        ((Fintype.card r : ℝ) ^ n * ((n.factorial : ℝ) * ((n.factorial : ℝ) * D))) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hf.le)
    _ = _ := by rw [hD]; field_simp

end GlobalTheory.GoodTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormPolarisedTopChernCoeffLeOfWeightedBoundStatement
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_polarisedTopChernCoeff_le_of_weighted_bound : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (K : Fin n → EndValuedForm11Coeffs n r) (w : Fin n → ℝ) (c : ℝ), (∀ a, 0 < w a) → (∀ i a b p q, ‖K i a b p q‖ * (w a * w b) ≤ c) → ‖mixTop K‖ ≤ (Fintype.card r : ℝ) ^ n * (n.factorial : ℝ) ^ 2 * |c| ^ n * ∏ a, (w a)⁻¹ ^ 2 := by
  first | exact @GlobalTheory.GoodTop.norm_mixTop_le_of_weighted | exact GlobalTheory.GoodTop.norm_mixTop_le_of_weighted | (intros; apply GlobalTheory.GoodTop.norm_mixTop_le_of_weighted <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpaceOfSignature
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ChiGrid
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChiGrid

theorem hasSignature_diag_signs (p q : ℕ) : Formalism.UG.HasSignature
    (Matrix.diagonal fun i : Fin (p + q) => (Examples₂.sgn (decide (p ≤ (i : ℕ))) : ℂ)) p q := by
  have hne : ∀ (i : Fin p) (j : Fin q), Fin.castAdd q i ≠ Fin.natAdd p j := fun i j h => by
    have := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at this
    omega
  refine ⟨(finSumFinEquiv (m := p) (n := q)).symm, 1, ?_⟩
  simp only [Units.val_one, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, Matrix.fromBlocks_apply₁₁, Matrix.diagonal_apply,
      Matrix.one_apply, (Fin.castAdd_injective p q).eq_iff]
    simp [Examples₂.sgn, Nat.not_le.2 i.isLt]
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₁₂,
      Matrix.diagonal_apply, Matrix.zero_apply]
    rw [if_neg (hne i j)]
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₂₁,
      Matrix.diagonal_apply, Matrix.zero_apply]
    rw [if_neg (hne j i).symm]
  · simp only [Formalism.UG.Jpq, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_right, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply,
      Matrix.neg_apply, Matrix.one_apply, (Fin.natAdd_injective q p).eq_iff]
    split_ifs <;> simp [Examples₂.sgn]

theorem exists_isV : ∀ (D : D7) (ν q : ℕ), q ≤ ν → ∃ X : LSp D, X.IsV ν q := by
  intro D ν q h
  obtain ⟨p, rfl⟩ : ∃ p, ν = p + q := ⟨ν - q, by omega⟩
  refine ⟨⟨diagSp D (p + q) (fun i => decide (p ≤ (i : ℕ))) p q, GlobalTheory.PlaceModel.latFrame _⟩, rfl, fun τ => ?_,
    fun τ => ?_, GlobalTheory.PlaceModel.isSelfDualC_latFrame _⟩
  · have hg : (diagSp D (p + q) (fun i => decide (p ≤ (i : ℕ))) p q).gram.map τ =
        Matrix.diagonal fun i : Fin (p + q) => (Examples₂.sgn (decide (p ≤ (i : ℕ))) : ℂ) := by
      rw [diagSp_gram]
      ext i j
      change τ (if i = j then _ else 0) = if i = j then _ else 0
      by_cases hij : i = j <;> simp [hij, Examples₂.map_sgn]
    change Formalism.UG.HasSignature ((diagSp D (p + q) (fun i => decide (p ≤ (i : ℕ))) p q).gram.map τ) p q
    rw [hg]
    exact hasSignature_diag_signs p q
  · rw [Nat.add_sub_cancel]
    rfl

end GlobalTheory.ChiGrid
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralIndicatorEqFinsumRelIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralIndicatorEqFinsumRelIndex
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb

namespace GlobalTheory.OrbIndUnit

theorem avg_const_fun {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have hs : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [rStab]
  unfold avg
  rw [hs, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) := uniqueOfSubsingleton (1 : H ⧸ (⊤ : Subgroup H))
  rw [finsum_unique]
  simp

theorem twOrb_id_indicator (G : Type) [Group G] [TopologicalSpace G] (K : Subgroup G) (γ : G) :
    twOrb (MonoidHom.id G) K γ ((K : Set G).indicator 1) = ∑ᶠ q : DoubleCoset.Quotient (twCent (MonoidHom.id G) γ : Set G) (K : Set G), if (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K then (((twCent (MonoidHom.id G) γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) γ)) : ℕ) : ℂ) else 0 := by
  unfold twOrb
  apply finsum_congr
  intro q
  set Q : G := Quotient.out q with hQ
  have hfun : (fun k : K => (K : Set G).indicator 1 ((Q * k)⁻¹ * γ * (MonoidHom.id G) (Q * k)))
      = fun _ => (K : Set G).indicator (1 : G → ℂ) (Q⁻¹ * γ * Q) := by
    funext k
    have he : (Q * k)⁻¹ * γ * (MonoidHom.id G) (Q * k) = (k : G)⁻¹ * (Q⁻¹ * γ * Q) * k := by
      simp only [MonoidHom.id_apply]; group
    rw [he]
    by_cases h : Q⁻¹ * γ * Q ∈ K
    · have h' : (k : G)⁻¹ * (Q⁻¹ * γ * Q) * k ∈ K := K.mul_mem (K.mul_mem (K.inv_mem k.2) h) k.2
      simp [Set.indicator_apply, h, h']
    · have h' : (k : G)⁻¹ * (Q⁻¹ * γ * Q) * k ∉ K := by
        intro h'
        apply h
        have := K.mul_mem (K.mul_mem k.2 h') (K.inv_mem k.2)
        simpa [mul_assoc] using this
      simp [Set.indicator_apply, h, h']
  rw [hfun, avg_const_fun]
  by_cases h : Q⁻¹ * γ * Q ∈ K
  · simp [Set.indicator_apply, h]
  · simp [Set.indicator_apply, h]

end GlobalTheory.OrbIndUnit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrbitalIntegralIndicatorEqFinsumRelIndexStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.UnitLemma GlobalTheory.InertUnitOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitalIntegral_indicator_eq_finsum_relIndex : ∀ (G : Type) [Group G] [TopologicalSpace G] (K : Subgroup G) (γ : G), twOrb (MonoidHom.id G) K γ ((K : Set G).indicator 1) = ∑ᶠ q : DoubleCoset.Quotient (twCent (MonoidHom.id G) γ : Set G) (K : Set G), if (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K then (((twCent (MonoidHom.id G) γ ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id G) γ)) : ℕ) : ℂ) else 0 := by
  first | exact @GlobalTheory.OrbIndUnit.twOrb_id_indicator | exact GlobalTheory.OrbIndUnit.twOrb_id_indicator | (intros; apply GlobalTheory.OrbIndUnit.twOrb_id_indicator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrBasisInImageOfFractionField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrBasisInImageOfFractionField
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct

namespace GlobalTheory.GraphLocal


open scoped IntermediateField.algebraAdjoinAdjoin in
theorem exists_trBasis_lift : ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ κ] (k : ℕ) (R : Subring K) (π : R →+* κ),
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  ∃ zR : Fin k → R, TrBasis (algebraMap ℂ κ) (fun i => π (zR i)) := by
  intro K κ _ _ inst k R π hfrac ⟨z, hz⟩
  have hiff : ∀ u : Fin k → κ, TrBasis (algebraMap ℂ κ) u ↔ IsTranscendenceBasis ℂ u := by
    intro u
    have : (algebraMap ℂ κ).toAlgebra = inst := Algebra.algebra_ext _ _ fun _ => rfl
    unfold TrBasis
    rw [this]
  have hz' := (hiff z).1 hz
  have htop : IntermediateField.adjoin ℂ (Set.range π) = ⊤ := by
    refine eq_top_iff.2 fun f _ => ?_
    obtain ⟨a, b, hb, e⟩ := hfrac f
    have : f = π a / π b := by rw [← e, mul_div_cancel_right₀ _ hb]
    rw [this]
    exact div_mem (IntermediateField.subset_adjoin _ _ ⟨a, rfl⟩)
      (IntermediateField.subset_adjoin _ _ ⟨b, rfl⟩)
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin ℂ (Set.range π)) κ :=
    ⟨fun f => isAlgebraic_algebraMap
      (⟨f, htop ▸ IntermediateField.mem_top⟩ : IntermediateField.adjoin ℂ (Set.range π))⟩
  have halg' : Algebra.IsAlgebraic (Algebra.adjoin ℂ (Set.range π)) κ :=
    IntermediateField.isAlgebraic_adjoin_iff_top.mp halg
  obtain ⟨t, ht, hb⟩ := exists_isTranscendenceBasis_subset (R := ℂ) (Set.range π)
  have hc : Cardinal.mk (Fin k) = Cardinal.mk t := by
    rw [hb.cardinalMk_eq_trdeg, hz'.cardinalMk_eq_trdeg]
  obtain ⟨e⟩ := Cardinal.eq.mp hc
  choose J hJ using fun i : Fin k => ht (e i).2
  refine ⟨J, (hiff _).2 ?_⟩
  have := (isTranscendenceBasis_equiv e).2 hb
  convert this using 1
  funext i
  exact hJ i

end GlobalTheory.GraphLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTrBasisInImageOfFractionFieldStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair GlobalTheory.GraphLocal
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_trBasis_in_image_of_fractionField : ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ κ] (k : ℕ) (R : Subring K) (π : R →+* κ),
  (∀ f : κ, ∃ a b : R, π b ≠ 0 ∧ f * π b = π a) → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) →
  ∃ zR : Fin k → R, TrBasis (algebraMap ℂ κ) (fun i => π (zR i)) := by
  first | exact @GlobalTheory.GraphLocal.exists_trBasis_lift | exact GlobalTheory.GraphLocal.exists_trBasis_lift | (intros; apply GlobalTheory.GraphLocal.exists_trBasis_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConstantTermSplitPlaceRegular
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConstantTermSplitPlaceRegular
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtReg

theorem exists_ne_of_avg_ne {H : Type} [Group H] {u : H → ℂ} (h : avg u ≠ 0) : ∃ x, u x ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  rw [avg, finsum_eq_zero_of_forall_eq_zero (fun q => hc _), mul_zero]

theorem exists_ne_of_hint_ne {H : Type} [Group H] {K : Subgroup H} {u : H → ℂ} (h : hint K u ≠ 0) :
    ∃ x, u x ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  rw [hint, finsum_eq_zero_of_forall_eq_zero (fun q => hc _), mul_zero]

theorem charpoly_conj_GL {ι R : Type} [Fintype ι] [DecidableEq ι] [CommRing R] (k g : GL ι R) :
    ((k⁻¹ * g * k : GL ι R) : Matrix ι ι R).charpoly = (g : Matrix ι ι R).charpoly := by
  rw [Units.val_mul, Units.val_mul, Matrix.charpoly_mul_comm, ← mul_assoc, Units.mul_inv, one_mul]

theorem ctMu_regAt2 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ), IsSplitAt w →
    (∀ y, f y ≠ 0 → y.1.val.charpoly.Separable) → RegAt2 a b w (ctMu h w μ f) := by
  intro E _ _ _ a b n h w μ f hw hf m hm
  have hct : ct h w (fun y => f (toSub _ y)) m ≠ 0 := by
    intro h0; apply hm; rw [ctMu, h0, mul_zero]
  rw [ct] at hct
  obtain ⟨X, hX⟩ := exists_ne_of_hint_ne (right_ne_zero_of_mul hct)
  obtain ⟨k, hk⟩ := exists_ne_of_avg_ne hX
  have hsep := hf _ hk
  have hmem : ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k) ∈ UL n w := by
    rw [UL, if_pos hw]; exact Subgroup.mem_top _
  have e0 : (toSub (UL n w) ((k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k)).1 =
      (k : GLw n w)⁻¹ * blk h w m (Multiplicative.toAdd X) * k := by
    rw [toSub, dite_eq_left hmem]
  rw [e0, charpoly_conj_GL, blk_val, Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₂₁] at hsep
  have e1 : nrmL a w m.1 = m.1 := by rw [nrmL, if_pos hw]
  have e2 : nrmL b w m.2 = m.2 := by rw [nrmL, if_pos hw]
  rw [e1, e2]
  exact hsep

end GlobalTheory.BCT.CtReg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConstantTermSplitPlaceRegularStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedConstantTermSplitPlace_regular : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (μ : (w.adicCompletion E)ˣ →* ℂˣ) (f : UL n w → ℂ), IsSplitAt w →
    (∀ y, f y ≠ 0 → y.1.val.charpoly.Separable) → RegAt2 a b w (ctMu h w μ f) := by
  first | exact @GlobalTheory.BCT.CtReg.ctMu_regAt2 | exact GlobalTheory.BCT.CtReg.ctMu_regAt2 | (intros; apply GlobalTheory.BCT.CtReg.ctMu_regAt2 <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyKottwitzLatticeSeparableMinpoly
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyKottwitzLatticeSeparableMinpoly
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.FinClsLoc.SepLat

theorem kottwitz_lattice_sep : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Y : G.Cˣ), (minpoly G.F (Y : G.C)).Separable →
    (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∀ᶠ w : AwayP p in Filter.cofinite, ∀ k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IntC G w ((k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) (Y : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) →
      IntC G w ((k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) ((Y⁻¹ : G.Cˣ) : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) →
      ∃ z m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (z : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) ∧
        IntC G w (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧ IntC G w ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧ k⁻¹ = z * m := by
  intro p _ G Y hsep hdeg
  filter_upwards [GlobalTheory.T.eventually_completedTensor_matrix_split_semilocal p G (Y : G.C) hdeg hsep, GlobalTheory.OrbFinAf.isIntV_mul_eventually G,
    GlobalTheory.OrbFinAf.KottLat.eventually_isIntV_map G ((1 : AfP p) ⊗ₜ[ℚ] (Y : G.C))] with w hA _ hY1
  intro k h1 _
  obtain ⟨K, _, R, Φ, hfin, hInt, Q, hQs, hQm⟩ := hA
  let γ₀ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ := Units.map (inC G (w.1.adicCompletion ℚ)).toMonoidHom Y
  have hγv : (γ₀ : w.1.adicCompletion ℚ ⊗[ℚ] G.C) = (1 : w.1.adicCompletion ℚ) ⊗ₜ[ℚ] (Y : G.C) := rfl
  have hγi : (γ₀ : w.1.adicCompletion ℚ ⊗[ℚ] G.C) = inC G (w.1.adicCompletion ℚ) (Y : G.C) := rfl
  have hγ0 : GlobalTheory.OrbFinAf.IsIntV G w (γ₀ : w.1.adicCompletion ℚ ⊗[ℚ] G.C) := by
    rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply] at hY1
    rw [hγv]; exact hY1
  have hconj : GlobalTheory.OrbFinAf.IsIntV G w (((k⁻¹)⁻¹ * γ₀ * k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) :
      w.1.adicCompletion ℚ ⊗[ℚ] G.C) := by
    rw [inv_inv, Units.val_mul, Units.val_mul, hγi]
    exact h1
  obtain ⟨U, hU, hU1, hU2⟩ := GlobalTheory.OrbFinAf.KottLat.conj_integral R Φ hfin Q hQs γ₀ (by rw [hγv]; exact hQm)
    ((hInt _).1 hγ0) k⁻¹ ((hInt _).1 hconj)
  have hcomm : k⁻¹ * U⁻¹ * γ₀ = γ₀ * (k⁻¹ * U⁻¹) := by
    have e : U * (k * γ₀ * k⁻¹) = γ₀ * U := by simpa using hU
    calc k⁻¹ * U⁻¹ * γ₀ = k⁻¹ * U⁻¹ * (γ₀ * U) * U⁻¹ := by group
      _ = k⁻¹ * U⁻¹ * (U * (k * γ₀ * k⁻¹)) * U⁻¹ := by rw [e]
      _ = γ₀ * (k⁻¹ * U⁻¹) := by group
  refine ⟨k⁻¹ * U⁻¹, U, ?_, (hInt _).2 hU1, (hInt _).2 hU2, by group⟩
  show _ * _ = _ * _
  rw [← hγi, ← Units.val_mul, ← Units.val_mul, hcomm]

end GlobalTheory.FinClsLoc.SepLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyKottwitzLatticeSeparableMinpolyStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.AwayOrb GlobalTheory.FinClsLoc
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_kottwitz_lattice_separable_minpoly : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (Y : G.Cˣ), (minpoly G.F (Y : G.C)).Separable →
    (minpoly G.F (Y : G.C)).natDegree = G.n →
    ∀ᶠ w : AwayP p in Filter.cofinite, ∀ k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ,
      IntC G w ((k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) (Y : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) →
      IntC G w ((k : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) * inC G (w.1.adicCompletion ℚ) ((Y⁻¹ : G.Cˣ) : G.C) * ((k⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C))) →
      ∃ z m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ, Commute (z : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) (inC G (w.1.adicCompletion ℚ) (Y : G.C)) ∧
        IntC G w (m : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧ IntC G w ((m⁻¹ : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)ˣ) : (w.1.adicCompletion ℚ ⊗[ℚ] G.C)) ∧ k⁻¹ = z * m := by
  first | (exact @GlobalTheory.FinClsLoc.SepLat.kottwitz_lattice_sep) | (exact GlobalTheory.FinClsLoc.SepLat.kottwitz_lattice_sep) | (intros; apply GlobalTheory.FinClsLoc.SepLat.kottwitz_lattice_sep  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenConjStableSubgroupOfSplitLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenConjStableSubgroupOfSplitLevel
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.CtLevel

theorem exists_open_conjStable_sub_level (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E)
    (K' : Subgroup (UL n w)) (hw : IsSplitAt w) (hK : IsLevel (MonoidHom.id _) (KL n w) K') :
    ∃ N : Subgroup (GLw n w), IsOpen (N : Set (GLw n w)) ∧
      N ≤ K'.map (UL n w).subtype ∧ (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ x ∈ N, k⁻¹ * x * k ∈ N) ∧
      (K' = KL n w → N = GlobalTheory.LFun.KGL w (n := n)) := by
  obtain ⟨hKo, hKc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL (E := E) w n
  have hUtop : UL n w = ⊤ := by unfold UL; rw [if_pos hw]
  have hUo : IsOpen (UL n w : Set (GLw n w)) := by rw [hUtop]; exact isOpen_univ
  have hmemU : ∀ x : GLw n w, x ∈ UL n w := fun x => by rw [hUtop]; trivial
  by_cases hKL : K' = KL n w
  · refine ⟨GlobalTheory.LFun.KGL w (n := n), hKo, ?_, ?_, fun _ => rfl⟩
    · intro x hx
      refine Subgroup.mem_map.2 ⟨⟨x, hmemU x⟩, ?_, rfl⟩
      rw [hKL, KL, Subgroup.mem_subgroupOf]
      exact hx
    · intro k hk x hx
      exact (GlobalTheory.LFun.KGL w (n := n)).mul_mem ((GlobalTheory.LFun.KGL w (n := n)).mul_mem ((GlobalTheory.LFun.KGL w (n := n)).inv_mem hk) hx) hk
  · set S : Subgroup (GLw n w) := K'.map (UL n w).subtype with hSdef
    have hSo : IsOpen (S : Set (GLw n w)) := by
      rw [hSdef, Subgroup.coe_map]
      exact hUo.isOpenMap_subtype_val _ hK.1
    haveI : CompactSpace (GlobalTheory.LFun.KGL w (n := n)) := isCompact_iff_compactSpace.1 hKc
    have hWo : IsOpen ((S.subgroupOf (GlobalTheory.LFun.KGL w (n := n)) : Subgroup _) : Set (GlobalTheory.LFun.KGL w (n := n))) := by
      rw [Subgroup.coe_subgroupOf]
      exact hSo.preimage continuous_subtype_val
    obtain ⟨V, hV⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
      ⟨Subgroup.isClosed_of_isOpen _ hWo, hWo⟩ (Subgroup.one_mem _)
    refine ⟨V.toSubgroup.map (GlobalTheory.LFun.KGL w (n := n)).subtype, ?_, ?_, ?_, fun h => absurd h hKL⟩
    · rw [Subgroup.coe_map]
      exact hKo.isOpenMap_subtype_val _ V.isOpen'
    · rintro _ ⟨v, hv, rfl⟩
      have := hV hv
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at this
      exact this
    · rintro k hk _ ⟨v, hv, rfl⟩
      refine ⟨(⟨k, hk⟩ : GlobalTheory.LFun.KGL w (n := n))⁻¹ * v * (⟨k, hk⟩ : GlobalTheory.LFun.KGL w (n := n)), ?_, ?_⟩
      · have := V.isNormal'.conj_mem v hv (⟨k, hk⟩ : GlobalTheory.LFun.KGL w (n := n))⁻¹
        simpa using this
      · simp

end GlobalTheory.BCT.CtLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenConjStableSubgroupOfSplitLevelStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_conjStable_subgroup_of_splitLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (K' : Subgroup (UL n w)), IsSplitAt w →
    IsLevel (MonoidHom.id _) (KL n w) K' → ∃ N : Subgroup (GLw n w), IsOpen (N : Set (GLw n w)) ∧
      N ≤ K'.map (UL n w).subtype ∧ (∀ k ∈ GlobalTheory.LFun.KGL w (n := n), ∀ x ∈ N, k⁻¹ * x * k ∈ N) ∧
      (K' = KL n w → N = GlobalTheory.LFun.KGL w (n := n)) := by
  first | exact @GlobalTheory.BCT.CtLevel.exists_open_conjStable_sub_level | exact GlobalTheory.BCT.CtLevel.exists_open_conjStable_sub_level | (intros; apply GlobalTheory.BCT.CtLevel.exists_open_conjStable_sub_level <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocModelLocRingAndExistsTrBasis
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

theorem preimage_fromSpecStalk_eq_constFn {k : Type} [Field k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) :
    (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)).hom = Cartier.constFn p := by
  ext a
  have n := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (.of k)).inv a))
    (Scheme.ΓSpecIso_naturality (Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p)))
  simp only [Spec.map_preimage, Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop,
    CommRingCat.hom_comp, RingHom.comp_apply, Iso.inv_hom_id_apply] at n
  rw [← n]
  have hid : (Spec (X.presheaf.stalk (genericPoint X))).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (X.presheaf.stalk (genericPoint X))).Opens) ≤ ⊤)).op = 𝟙 _ := by
    rw [show (homOfLE (le_top : (⊤ : (Spec (X.presheaf.stalk (genericPoint X))).Opens) ≤ ⊤))
      = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
  rw [hid, CommRingCat.id_apply, Iso.inv_hom_id_apply]
  have e2 : Scheme.Hom.appLE p ⊤ ⊤ (by simp) = Scheme.Hom.appTop p := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    congr 1
  simp only [Cartier.constFn, Cartier.fnOf, algX, e2, RingHom.comp_apply]

theorem isLocModel_locRing_and_exists_trBasis {k : Type} [Field k] (X : Scheme.{0}) [IsIntegral X]
    (p : X ⟶ Sp k) [LocallyOfFiniteType p] (n : ℕ) (x : X) (hn : topologicalKrullDim X = n) :
    IsLocModel (Cartier.constFn p) (locRing x) ∧
      ∃ z : Fin n → X.functionField, TrBasis (Cartier.constFn p) z := by
  refine ⟨isLocModel_locRing x, ?_⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU : IsAffineOpen U := hU
  have hne : (U : Set X).Nonempty := ⟨x, hxU⟩
  obtain ⟨d, h₁, h₂⟩ := GlobalTheory.OpenDim.ringKrullDim_affineOpen k p hU hne
  have e₁ := GlobalTheory.OpenDim.topologicalKrullDim_open k p U hne
  have e₂ : topologicalKrullDim (U : Set X) = ringKrullDim Γ(X, U) := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
      hU.range_fromSpec
  have hdn : d = n := by
    have : ((d : ℕ) : WithBot ℕ∞) = (n : WithBot ℕ∞) := by rw [← h₁, ← e₂, e₁, hn]
    exact_mod_cast this
  subst hdn
  rw [preimage_fromSpecStalk_eq_constFn] at h₂
  letI := (Cartier.constFn p).toAlgebra
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k X.functionField
  have hc : Cardinal.mk s = (d : Cardinal) := hs.cardinalMk_eq_trdeg.trans h₂
  have hfin : Fintype s := (Cardinal.lt_aleph0_iff_fintype.mp (hc ▸ Cardinal.natCast_lt_aleph0 (n := d))).some
  have hcard : Fintype.card s = d := by
    have := hc; rw [Cardinal.mk_fintype] at this; exact_mod_cast this
  let e : Fin d ≃ s := (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨fun i => (e i : X.functionField), ?_⟩
  unfold TrBasis
  exact hs.comp_equiv e

end GlobalTheory.FieldPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandInvariantsDetermineMultiset
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.WignerGL GlobalTheory.WigAlg Formalism.REAL
open scoped TensorProduct

namespace GlobalTheory.GelfandInj

open Finset Polynomial

theorem capQ_eq_prod (m : ℕ) (χ : Fin (m+1) → ℂ) :
    GlobalTheory.CapelliNewton.capQ m χ
      = (((Multiset.map χ Finset.univ.val).map (fun a => ((m : ℂ) / 2 - a))).map (fun a => X - C a)).prod := by
  unfold GlobalTheory.CapelliNewton.capQ
  rw [Multiset.map_map, Multiset.map_map, Finset.prod_eq_multiset_prod]
  congr 1
  refine Multiset.map_congr rfl fun s _ => ?_
  simp only [Function.comp_apply, map_sub]
  ring

theorem capQ_roots (m : ℕ) (χ : Fin (m+1) → ℂ) :
    (GlobalTheory.CapelliNewton.capQ m χ).roots = (Multiset.map χ Finset.univ.val).map (fun a => ((m : ℂ) / 2 - a)) := by
  rw [capQ_eq_prod, Polynomial.roots_multiset_prod_X_sub_C]

theorem gelfVal_multiset_eq : ∀ (n : ℕ) (χ χ' : Fin n → ℂ), (∀ k : ℕ, GlobalTheory.Dec.gelfVal χ (k + 1) = GlobalTheory.Dec.gelfVal χ' (k + 1)) → Multiset.map χ Finset.univ.val = Multiset.map χ' Finset.univ.val := by
  intro n χ χ' h
  cases n with
  | zero => simp
  | succ m =>
    have hall : ∀ k, GlobalTheory.Dec.gelfVal χ k = GlobalTheory.Dec.gelfVal χ' k := by
      intro k
      cases k with
      | zero => rw [GlobalTheory.CapelliNewton.gelfVal_zero, GlobalTheory.CapelliNewton.gelfVal_zero]
      | succ k => exact h k
    have hgv : GlobalTheory.Dec.gelfVal χ = GlobalTheory.Dec.gelfVal χ' := funext hall
    obtain ⟨r, hr, hrE⟩ := GlobalTheory.T.scalar_capelli_truncated_perelomov_popov m (m + 1) χ
    obtain ⟨r', hr', hrE'⟩ := GlobalTheory.T.scalar_capelli_truncated_perelomov_popov m (m + 1) χ'
    have hf := GlobalTheory.T.poly_eq_zero_of_newton_recursion m (m + 1) (GlobalTheory.Dec.gelfVal χ)
      (GlobalTheory.CapelliNewton.capQ m χ - GlobalTheory.CapelliNewton.capQ m χ') (r - r')
      (Nat.lt_succ_self m) (GlobalTheory.CapelliNewton.gelfVal_zero m χ) ?_ ?_ ?_
    · have hQ : GlobalTheory.CapelliNewton.capQ m χ = GlobalTheory.CapelliNewton.capQ m χ' := sub_eq_zero.mp hf
      have hroots := congrArg Polynomial.roots hQ
      rw [capQ_roots, capQ_roots] at hroots
      exact Multiset.map_injective (fun a b hab => by simpa using hab) hroots
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro k hk
      rw [coeff_sub]
      rcases Nat.lt_or_ge (m + 1) k with hlt | hge
      · rw [coeff_eq_zero_of_natDegree_lt (by rw [GlobalTheory.CapelliNewton.capQ_natDegree]; exact hlt),
          coeff_eq_zero_of_natDegree_lt (by rw [GlobalTheory.CapelliNewton.capQ_natDegree]; exact hlt), sub_zero]
      · have hk' : k = m + 1 := le_antisymm hge hk
        subst hk'
        have h1 := (GlobalTheory.CapelliNewton.capQ_monic m χ).coeff_natDegree
        have h2 := (GlobalTheory.CapelliNewton.capQ_monic m χ').coeff_natDegree
        rw [GlobalTheory.CapelliNewton.capQ_natDegree] at h1 h2
        rw [h1, h2, sub_self]
    · exact (natDegree_sub_le _ _).trans (max_le hr hr')
    · intro u
      have h1 := hrE u
      have h2 := hrE' u
      rw [← hgv] at h2
      rw [← GlobalTheory.CapelliNewton.capQ_eval m χ (u + 1), ← GlobalTheory.CapelliNewton.capQ_eval m χ u] at h1
      rw [← GlobalTheory.CapelliNewton.capQ_eval m χ' (u + 1), ← GlobalTheory.CapelliNewton.capQ_eval m χ' u] at h2
      simp only [eval_sub]
      linear_combination h1 - h2

end GlobalTheory.GelfandInj
end
