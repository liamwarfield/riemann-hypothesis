module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPermOfCardFalse
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MultiplicityMapEqZeroOfTranslatedEvaluationAeZer
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodParParBLast
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantHermitianFormCuspidalRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfFderivEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiIdemMulLvlIdemBaseNeZero
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAddEquivSymplecticCoordsOrientedModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeOperatorMoveAcrossInvariantBilinear
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeImageAdelicUnitary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelModelsOfFunctoriality
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SepRows

open Matrix

theorem exists_model_of_enum {D : D7} (hDS : GlobalTheory.Published.DiscreteSeriesUpqExists) {V : HSp D} (hV : V.SigOK)
    {S : D.what₂.Tau → SPar} (O C : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hS : ∀ τ, ∃ (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool), IsEnum (S τ) lam ε ∧ Formalism.QuantumDeterminants.IsHCParam lam ∧
      (Finset.univ.filter fun a => ε a = false).card = (V.sig (tauE D τ)).2)
    (hO : ∀ τ, ∃ ε : Fin V.rank → Bool, (O τ)ᴴ * gramAt D V τ * O τ = Formalism.REAL.Jm ε ∧ C τ * O τ = O τ * Formalism.REAL.Jm ε) :
    ∃ M : DSModel V S, cart M = C := by
  classical
  have key : ∀ τ, ∃ σ : Equiv.Perm (Fin V.rank), ∃ (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool), IsEnum (S τ) lam ε ∧
      Formalism.QuantumDeterminants.IsHCParam lam ∧ ((O τ).submatrix id σ)ᴴ * gramAt D V τ * (O τ).submatrix id σ = Formalism.REAL.Jm ε ∧
      C τ * (O τ).submatrix id σ = (O τ).submatrix id σ * Formalism.REAL.Jm ε := by
    intro τ
    obtain ⟨lam, ε', hE, hH, hc⟩ := hS τ
    obtain ⟨ε, h1, h2⟩ := hO τ
    obtain ⟨σ, hσ⟩ := GlobalTheory.GridJoin.exists_perm_of_card_false ε ε' (by rw [GlobalTheory.GridJoin.card_false_of_gram hV τ h1, hc])
    have e : ε ∘ σ = ε' := funext hσ
    refine ⟨σ, lam, ε', hE, hH, ?_, ?_⟩
    · rw [GlobalTheory.GridJoin.gram_submatrix, h1, GlobalTheory.GridJoin.jm_submatrix, e]
    · rw [GlobalTheory.GridJoin.mul_submatrix_cols, h2, GlobalTheory.GridJoin.submatrix_mul_jm, e]
  choose σ lam ε hE hH h1 h2 using key
  obtain ⟨M, hM, -⟩ := GlobalTheory.T.exists_discreteSeriesModel_of_orthonormalBasis_cartan D hDS V S (fun τ => (O τ).submatrix id (σ τ)) C
    (fun τ => ⟨lam τ, ε τ, hE τ, hH τ, h1 τ⟩) (fun τ => ⟨ε τ, h1 τ, h2 τ⟩)
  exact ⟨M, hM⟩

theorem isHCParam_dual_parV (D : D7) (i j : ℕ) (τ : D.what₂.Tau) {n : ℕ} (lam : Fin n → ℝ) (ε : Fin n → Bool)
    (hn : n = rankV D i j) (hE : IsEnum (dualPar (parV D 1 i j τ)) lam ε) : Formalism.QuantumDeterminants.IsHCParam lam := by
  refine ⟨hE.1, fun a' => ?_⟩
  obtain ⟨-, q, hq, hS⟩ := hE
  have hmem : (q a', ε a') ∈ dualPar (parV D 1 i j τ) := by
    rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
  simp only [parV, dualPar, GlobalTheory.SignedHC.shift, Finset.mem_image, Prod.mk.injEq] at hmem
  obtain ⟨y, ⟨x, hx, rfl⟩, hy1, -⟩ := hmem
  rw [← GlobalTheory.GridParDCount.grid_eq_num] at hx
  obtain ⟨z, hz⟩ := GlobalTheory.Grid.parD_entry_int D τ i j hx
  have hpar : Even (rankV D i j) ↔ Odd (i + j) := GlobalTheory.Grid.even_rkV_iff D i j
  rw [hq a', ← hy1]
  by_cases ho : Odd (i + j)
  · obtain ⟨N, hN⟩ := hpar.2 ho
    rw [if_pos ho]
    refine ⟨-z + 1 - N, ?_⟩
    have : (n : ℝ) = N + N := by rw [hn, hN]; push_cast; ring
    simp only [hz, this]; push_cast; ring
  · have hne : ¬ Even (rankV D i j) := fun h => ho (hpar.1 h)
    obtain ⟨N, hN⟩ := Nat.not_even_iff_odd.1 hne
    rw [if_neg ho]
    refine ⟨-z - N, ?_⟩
    have : (n : ℝ) = 2 * N + 1 := by rw [hn, hN]; push_cast; ring
    simp only [hz, this]; push_cast; ring

end GlobalTheory.SepRows
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodCharactersDualStableOfThetaLiftScalars
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodStableOfIrr
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

noncomputable section

namespace GlobalTheory.GoodStableDual

open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.DimPartsCompare GlobalTheory.BI

theorem isChar_dual {G : Type} [Group G] [Fintype G] {χ : G → ℂ} (h : IsChar ℂ ℂ χ) :
    IsChar ℂ ℂ fun g => χ g⁻¹ := by
  obtain ⟨n, ρ, hρ⟩ := h
  let e : Module.Dual ℂ (Fin n → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) := (Pi.basisFun ℂ (Fin n)).dualBasis.equivFun
  let σ : Representation ℂ G (Fin n → ℂ) :=
    { toFun := fun g => e.conj (ρ.dual g)
      map_one' := by rw [map_one]; exact LinearEquiv.conj_id e
      map_mul' := fun a b => by rw [map_mul]; exact LinearEquiv.conj_comp e _ _ }
  refine ⟨n, σ, fun g => ?_⟩
  have : σ.character g = ρ.dual.character g := LinearMap.trace_conj' _ e
  show χ g⁻¹ = _
  rw [Algebra.algebraMap_self, RingHom.id_apply, this, Representation.char_dual, hρ, Algebra.algebraMap_self,
    RingHom.id_apply]

theorem coeff_idemOf_inv {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (hrec : R.grp_record) {om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ} (hI : IdemTie D om) (g : G) :
    (idemOf A.X).coeff g⁻¹ = (idemOf A.X).coeff g := by
  obtain ⟨eR, plg, iso, h1, -, -⟩ := hrec
  let π : LevelCuspCharacters.LevelGroup D.host ≃* G0g D.nd :=
    MulEquiv.ofBijective (⟨⟨pull, rfl⟩, fun _ _ => rfl⟩ : LevelCuspCharacters.LevelGroup D.host →* G0g D.nd) pull_bijective
  let φ : G ≃* LevelCuspCharacters.LevelGroup D.host := eR.trans π.symm
  have hφ : ∀ g, pull (φ g) = eR g := fun g => π.apply_symm_apply (eR g)
  apply D.what₂.embLL.injective
  rw [h1, h1, ← hφ, ← hφ, hI, hI]
  exact GlobalTheory.GoodIdemFlip.coeff_goodIdem_flip _ D.host om Set.univ (φ g) (φ g⁻¹)
    (fun v _ => by rw [map_inv, Pi.inv_apply]) (fun v hv => absurd (Set.mem_univ v) hv)

theorem goodStable_of_irr {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A) (hirr : ∀ χ ∈ A.X, IsAbsIrrChar χ) (hG : R.IsGrp F) (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ)
    (hI : IdemTie D om) : GoodStable A.X := by
  classical
  have hsym := coeff_idemOf_inv R hG.record hI
  intro χ hχ
  obtain ⟨ψ, hψ, hψe⟩ := GlobalTheory.GoodTypeGeneric.exists_eq_of_idemOf D.what₂.embLL A.X hirr A.X
    (fun ψ g => D.what₂.embLL (ψ g⁻¹)) (fun ψ hψ => by
      obtain ⟨n, ρ, -, hρ⟩ := GlobalTheory.GoodTypeGeneric.isIrrChar_of_isAbsIrrChar D.what₂.embLL (hirr ψ hψ)
      exact isChar_dual ⟨n, ρ, hρ⟩) (fun g => by
      rw [← hsym g]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [idemOf, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, coeff_chiIdem, map_sum, map_mul, map_div₀,
        map_natCast, inv_one, inv_inv, Nat.card_eq_fintype_card]) hχ
  convert hψ using 1
  funext g
  apply D.what₂.embLL.injective
  simpa using hψe g⁻¹

end GlobalTheory.GoodStableDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodCharactersDualStableOfThetaLiftScalars
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.GoodStableGiven

theorem goodStable_of_given : GlobalTheory.Published.GreenCuspidal → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (F : Face D A), Given R F → Formalism.L2.DIV.GoodStable A.X := by
  intro hGC D G _ _ Pl0 T A Ks _ _ _ R F h
  obtain ⟨om, hT⟩ := GlobalTheory.T.exists_tameCharacters_seriesIdempotentsTameLabelled R F h
  exact GlobalTheory.GoodStableDual.goodStable_of_irr R F h.irr h.core.grp om
    (GlobalTheory.GoodIdemTie.idemTie_of_tameTie hGC D om hT)

end GlobalTheory.GoodStableGiven

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodCharactersDualStableOfThetaLiftScalarsStatement
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodCharacters_dual_stable_of_thetaLift_scalars : GlobalTheory.Published.GreenCuspidal → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → Formalism.L2.DIV.GoodStable A.X := by
  first | exact @GlobalTheory.GoodStableGiven.goodStable_of_given | exact GlobalTheory.GoodStableGiven.goodStable_of_given | (intros; apply GlobalTheory.GoodStableGiven.goodStable_of_given <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTransposeGramCoordinateHomeomorphSymplecti
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTransposeGramCoordinateHomeomorphSymplecti
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic

variable {D : D7}

theorem gram_map_mul_inv {R : Type*} [CommRing R] (S : HSp D) (φ : D.host.E →+* R) :
    S.gram.map φ * (S.gram⁻¹).map φ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.gram_det_ne_zero S)),
    Matrix.map_one _ φ.map_zero φ.map_one]

theorem gram_inv_map_mul {R : Type*} [CommRing R] (S : HSp D) (φ : D.host.E →+* R) :
    (S.gram⁻¹).map φ * S.gram.map φ = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (GlobalTheory.Twist.exists_addEquiv_symplecticCoords_orientedModel.gram_det_ne_zero S)),
    Matrix.map_one _ φ.map_zero φ.map_one]

def coordsLin (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank) :
    WO S' T' ≃ₗ[AE D] WO S T where
  toFun u := (HMul.hMul (uᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))
  invFun x := ((HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂
  map_add' u v := by
    show (u + v)ᵀ.submatrix e₂.symm e₁.symm * _ = uᵀ.submatrix e₂.symm e₁.symm * _ + vᵀ.submatrix e₂.symm e₁.symm * _
    rw [Matrix.transpose_add, ← Matrix.add_mul]
    rfl
  map_smul' c u := by
    show (c • u)ᵀ.submatrix e₂.symm e₁.symm * _ = c • (uᵀ.submatrix e₂.symm e₁.symm * _)
    rw [Matrix.transpose_smul, ← Matrix.smul_mul]
    rfl
  left_inv u := by
    show ((uᵀ.submatrix e₂.symm e₁.symm * S.gram.map (incA D) * (S.gram⁻¹).map (incA D))ᵀ).submatrix e₁ e₂ = u
    rw [Matrix.mul_assoc, gram_map_mul_inv, Matrix.mul_one]
    ext i j; simp
  right_inv x := by
    dsimp only
    have : (((HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂)ᵀ.submatrix e₂.symm e₁.symm =
        (HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
      ext i j; simp
    rw [this, Matrix.mul_assoc, gram_inv_map_mul, Matrix.mul_one]

theorem map_transpose_submatrix {A B : Type*} [Semiring A] [Semiring B] (φ : A →+* B) {m n p q : Type*}
    (u : Matrix m n A) (f : p → n) (g : q → m) : (uᵀ.submatrix f g).map φ = ((u.map φ)ᵀ).submatrix f g := rfl

theorem coordsLin_map_zero {R : Type*} [Semiring R] (φ : AE D →+* R) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank)
    (e₂ : Fin S'.rank ≃ Fin T.rank) (x : WO S' T') (h : x.map φ = 0) : (coordsLin S T S' T' e₁ e₂ x).map φ = 0 := by
  change (HMul.hMul (xᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D)).map φ = 0
  rw [Matrix.map_mul, map_transpose_submatrix, h]
  simp

theorem coordsLin_symm_map_zero {R : Type*} [Semiring R] (φ : AE D →+* R) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank)
    (e₂ : Fin S'.rank ≃ Fin T.rank) (y : WO S T) (h : y.map φ = 0) : ((coordsLin S T S' T' e₁ e₂).symm y).map φ = 0 := by
  change (((HMul.hMul y ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂).map φ = 0
  rw [map_transpose_submatrix, Matrix.map_mul, h]
  simp

theorem coordsLin_map_zero_iff {R : Type*} [Semiring R] (φ : AE D →+* R) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank)
    (e₂ : Fin S'.rank ≃ Fin T.rank) (x : WO S' T') : (coordsLin S T S' T' e₁ e₂ x).map φ = 0 ↔ x.map φ = 0 := by
  refine ⟨fun h => ?_, coordsLin_map_zero φ S T S' T' e₁ e₂ x⟩
  have := coordsLin_symm_map_zero φ S T S' T' e₁ e₂ _ h
  rwa [LinearEquiv.symm_apply_apply] at this

theorem coordsLin_rat_iff (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank)
    (e₂ : Fin S'.rank ≃ Fin T.rank) (x : WO S' T') : coordsLin S T S' T' e₁ e₂ x ∈ ratL T S ↔ x ∈ ratL T' S' := by
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨((γ * S.gram⁻¹)ᵀ).submatrix e₁ e₂, ?_⟩
    rw [← (coordsLin S T S' T' e₁ e₂).symm_apply_apply x, ← hγ]
    change (((γ * S.gram⁻¹)ᵀ).submatrix e₁ e₂).map (incA D) =
      ((HMul.hMul (γ.map (incA D)) ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂
    rw [map_transpose_submatrix, Matrix.map_mul]
  · rintro ⟨γ, rfl⟩
    refine ⟨γᵀ.submatrix e₂.symm e₁.symm * S.gram, ?_⟩
    change (γᵀ.submatrix e₂.symm e₁.symm * S.gram).map (incA D) =
      (HMul.hMul ((γ.map (incA D))ᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))
    rw [Matrix.map_mul, map_transpose_submatrix]

theorem coordsLin_spec (D : D7) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank) :
    ∃ L : WO S' T' ≃ₗ[AE D] WO S T,
      (∀ u, L u = (HMul.hMul (uᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))) ∧
      (∀ x : Matrix (Fin T.rank) (Fin S.rank) (AE D),
        L.symm x = ((HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂) ∧
      Continuous L ∧ Continuous L.symm ∧ (∀ x, L x ∈ ratL T S ↔ x ∈ ratL T' S') ∧
      (∀ x, (L x).map (infPart D) = 0 ↔ x.map (infPart D) = 0) ∧ ∀ x, (L x).map (finPart D) = 0 ↔ x.map (finPart D) = 0 := by
  refine ⟨coordsLin S T S' T' e₁ e₂, fun _ => rfl, fun _ => rfl, ?_, ?_, coordsLin_rat_iff S T S' T' e₁ e₂,
    coordsLin_map_zero_iff _ S T S' T' e₁ e₂, coordsLin_map_zero_iff _ S T S' T' e₁ e₂⟩
  · change Continuous fun u : WO S' T' =>
      (HMul.hMul (uᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))
    exact (continuous_id.matrix_transpose.matrix_submatrix _ _).matrix_mul continuous_const
  · change Continuous fun x : WO S T =>
      ((HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂
    exact ((continuous_id.matrix_mul continuous_const).matrix_transpose).matrix_submatrix _ _

end GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTransposeGramCoordinateHomeomorphSymplectiStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_transposeGram_coordinate_homeomorph_symplectic : ∀ (D : D7) (S T S' T' : HSp D) (e₁ : Fin T'.rank ≃ Fin S.rank) (e₂ : Fin S'.rank ≃ Fin T.rank),
    ∃ L : WO S' T' ≃ₗ[AE D] WO S T,
      (∀ u, L u = (HMul.hMul (uᵀ.submatrix e₂.symm e₁.symm) (S.gram.map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))) ∧
      (∀ x : Matrix (Fin T.rank) (Fin S.rank) (AE D),
        L.symm x = ((HMul.hMul x ((S.gram⁻¹).map (incA D)) : Matrix (Fin T.rank) (Fin S.rank) (AE D))ᵀ).submatrix e₁ e₂) ∧
      Continuous L ∧ Continuous L.symm ∧ (∀ x, L x ∈ ratL T S ↔ x ∈ ratL T' S') ∧
      (∀ x, (L x).map (infPart D) = 0 ↔ x.map (infPart D) = 0) ∧ ∀ x, (L x).map (finPart D) = 0 ↔ x.map (finPart D) = 0 := by
  first | exact @GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic.coordsLin_spec | exact GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic.coordsLin_spec | (intros; apply GlobalTheory.Twist.exists_transposeGram_coordinate_homeomorph_symplectic.coordsLin_spec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftsCuspidalOfLowerTowerLiftsVanish
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftsCuspidalOfLowerTowerLiftsVanish
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairLift.LowCusp

variable {D : D7}

theorem multT_ind {W : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel W S)
    (J : Set (GA D W)) (χ : GA D W → ℂ) (P : (GA D W → ℂ) → Prop) (h0 : P 0)
    (hadd : ∀ φ φ', P φ → P φ' → P (φ + φ')) (hsmul : ∀ (c : ℂ) φ, P φ → P (c • φ))
    (hcusp : ∀ φ, IsAutFunSm θ W φ → IsCuspFun W φ → P φ)
    (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M) : P (F v) := by
  obtain ⟨T, hT, rfl⟩ := hF
  have key : ∀ w : M.Vec, P (T w) := by
    induction hT using Submodule.span_induction with
    | mem T hT => exact fun w => hcusp _ (hT.aut w) (hT.cusp w)
    | zero => intro w; simpa using h0
    | add T T' _ _ h h' => intro w; simpa using hadd _ _ (h w) (h' w)
    | smul c T _ h => intro w; simpa using hsmul c _ (h w)
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c w =>
    simpa using hsmul c _ (key w)
  | add x y hx hy =>
    simpa using hadd _ _ hx hy

theorem liftInt_add' {G H S : Type*} [MeasurableSpace H] {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ} {s : S}
    {φ φ' : H → ℂ} {g : G} (h : IntegrableOn (fun x => th g x s * φ x) 𝓕 ν)
    (h' : IntegrableOn (fun x => th g x s * φ' x) 𝓕 ν) :
    Lift.liftInt ν 𝓕 th s (φ + φ') g = Lift.liftInt ν 𝓕 th s φ g + Lift.liftInt ν 𝓕 th s φ' g := by
  unfold Lift.liftInt
  rw [← integral_add h h']
  simp only [Pi.add_apply, mul_add]

theorem liftInt_smul' {G H S : Type*} [MeasurableSpace H] {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ} {s : S}
    (c : ℂ) (φ : H → ℂ) (g : G) :
    Lift.liftInt ν 𝓕 th s (c • φ) g = c * Lift.liftInt ν 𝓕 th s φ g := by
  unfold Lift.liftInt
  rw [← integral_const_mul]
  congr 1
  funext h
  simp only [Pi.smul_apply, smul_eq_mul]
  exact mul_left_comm (th g h s) c (φ h)

theorem liftInt_zero' {G H S : Type*} [MeasurableSpace H] {ν : Measure H} {𝓕 : Set H} {th : G → H → S → ℂ} {s : S}
    (g : G) : Lift.liftInt ν 𝓕 th s (0 : H → ℂ) g = 0 := by
  simp [Lift.liftInt]

structure CtGood {V V' W : HSp D} {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E)
    (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ))
    (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (κ : Measure (NI V C)) (𝓝 : Set (NI V C))
    (f : WO V W → ℂ) (f' : WO V' W → ℂ) (g : GA D V) (c : ℂ) (φ : GA D W → ℂ) : Prop where
  integ : ∀ g₁, IntegrableOn (fun h => thetaKO ω g₁ h f * φ h) 𝓕 ν
  integ' : IntegrableOn (fun h => thetaKO ω' 1 h f' * φ h) 𝓕 ν
  mean : IntegrableOn (fun n : NI V C => Lift.liftInt ν 𝓕 (thetaKO ω) f φ ((n : GA D V) * g)) 𝓝 κ
  eq : ∫ n in 𝓝, Lift.liftInt ν 𝓕 (thetaKO ω) f φ ((n : GA D V) * g) ∂κ =
    c * Lift.liftInt ν 𝓕 (thetaKO ω') f' φ 1

section CtGood

variable {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
  {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)}
  {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} {κ : Measure (NI V C)} {𝓝 : Set (NI V C)}
  {f : WO V W → ℂ} {f' : WO V' W → ℂ} {g : GA D V} {c : ℂ}

theorem CtGood.zero : CtGood C ω ω' ν 𝓕 κ 𝓝 f f' g c 0 := by
  refine ⟨fun g₁ => ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp [liftInt_zero']
  · simp [liftInt_zero']

theorem CtGood.add {φ φ' : GA D W → ℂ} (h : CtGood C ω ω' ν 𝓕 κ 𝓝 f f' g c φ)
    (h' : CtGood C ω ω' ν 𝓕 κ 𝓝 f f' g c φ') : CtGood C ω ω' ν 𝓕 κ 𝓝 f f' g c (φ + φ') := by
  have e : (fun n : NI V C => Lift.liftInt ν 𝓕 (thetaKO ω) f (φ + φ') ((n : GA D V) * g)) =
      fun n : NI V C => Lift.liftInt ν 𝓕 (thetaKO ω) f φ ((n : GA D V) * g) +
        Lift.liftInt ν 𝓕 (thetaKO ω) f φ' ((n : GA D V) * g) :=
    funext fun n => liftInt_add' (h.integ _) (h'.integ _)
  refine ⟨fun g₁ => ?_, ?_, ?_, ?_⟩
  · refine ((h.integ g₁).add (h'.integ g₁)).congr (Filter.Eventually.of_forall fun x => ?_)
    simp [mul_add]
  · refine (h.integ'.add h'.integ').congr (Filter.Eventually.of_forall fun x => ?_)
    simp [mul_add]
  · rw [e]; exact h.mean.add h'.mean
  · rw [e, integral_add h.mean h'.mean, h.eq, h'.eq, liftInt_add' h.integ' h'.integ', mul_add]

theorem CtGood.smul {φ : GA D W → ℂ} (a : ℂ) (h : CtGood C ω ω' ν 𝓕 κ 𝓝 f f' g c φ) :
    CtGood C ω ω' ν 𝓕 κ 𝓝 f f' g c (a • φ) := by
  have e : (fun n : NI V C => Lift.liftInt ν 𝓕 (thetaKO ω) f (a • φ) ((n : GA D V) * g)) =
      fun n : NI V C => a * Lift.liftInt ν 𝓕 (thetaKO ω) f φ ((n : GA D V) * g) :=
    funext fun n => liftInt_smul' a φ _
  refine ⟨fun g₁ => ?_, ?_, ?_, ?_⟩
  · refine ((h.integ g₁).const_mul a).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  · refine (h.integ'.const_mul a).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.smul_apply, smul_eq_mul]; ring
  · rw [e]; exact h.mean.const_mul a
  · rw [e, integral_const_mul, h.eq, liftInt_smul']; ring

end CtGood

theorem constTerm_eq_zero (hct : TowerConstTerm D) (hP : GlobalTheory.Published.CuspRapidDecay)
    {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} (hs : IsIsoSplit V V' C B)
    {θ : InfFam D} (hθ : IsInfFam θ) {ψ : AddChar (AF D.host.F) ℂ} {χS χT χT' : (AE D)ˣ →* Circle}
    {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)}
    (hω : IsWeilDatumO ψ V W χS χT ω) (hω' : IsWeilDatumO ψ V' W χS χT' ω')
    {ν : Measure (GA D W)} {𝓕 : Set (GA D W)} (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ W) 𝓕 ν)
    {S : D.what₂.Tau → SPar} (M : DSModel W S) (J : Set (GA D W)) (χ : GA D W → ℂ)
    (F : SmT M →ₗ[ℂ] (GA D W → ℂ)) (hF : F ∈ MultT θ M J χ) (v : SmT M)
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (hlow : ∀ f', IsThetaFunO ψ V' W f' → Lift.liftInt ν 𝓕 (thetaKO ω') f' (F v) 1 = 0)
    (κ : Measure (NI V C)) (𝓝 : Set (NI V C)) (hκ : κ.IsHaarMeasure) (h𝓝 : IsFundamentalDomain (NIQ V C) 𝓝 κ)
    (g : GA D V) : ∫ n in 𝓝, Lift.liftInt ν 𝓕 (thetaKO ω) f (F v) ((n : GA D V) * g) ∂κ = 0 := by
  obtain ⟨μ, 𝓨, hc⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank r
  have form := hct V V' W r C B hs ψ χS χT χT' ω ω' hω hω' μ 𝓨 hc ν 𝓕 hν h𝓕 κ 𝓝 hκ h𝓝
  have h0 : GlobalTheory.Grow.RapidDec W (0 : GA D W → ℂ) :=
    ⟨fun _ _ _ => rfl, continuous_const, fun N => ⟨0, fun g => by simp⟩⟩
  have hc0 : IsCuspFun W (0 : GA D W → ℂ) := fun _ _ _ _ _ _ _ _ => by simp
  have ht := (form 0 h0 hc0 f hf g).2.2.1
  have good : CtGood C ω ω' ν 𝓕 κ 𝓝 f (res V V' W C B μ 𝓨 (ω (g, 1) f)) g (((κ 𝓝).toReal : ℝ) : ℂ) (F v) := by
    refine multT_ind θ M J χ _ CtGood.zero (fun _ _ h h' => h.add h') (fun a _ h => h.smul a) (fun φ ha hcu => ?_) F hF v
    obtain ⟨-, -, -, h1, h2, h3, h4⟩ := form φ (GlobalTheory.Size.rapidDecSm_of_cuspForm hP hθ ha hcu).rapidDec hcu f hf g
    exact ⟨h1, h2, h3, h4⟩
  rw [good.eq, hlow _ ht, mul_zero]

end GlobalTheory.PairLift.LowCusp

namespace GlobalTheory.PairLift

theorem cuspAll_of_lowAll : ∀ (D : D7) (X : ProvA), Inputs D X → LowAll D X → CuspAll D X := by
  intro D X hI hL S S' aS aT hR V W _M M' θ ψ hθ ω hω ν 𝓕 hν h𝓕 F hF v f hf r C hC κ 𝓝 hκ h𝓝 g
  obtain ⟨V', B, hs, hsig⟩ := GlobalTheory.T.exists_lowerWittTower_isotropicSplitEmbedding D V S _M r C hC
  obtain ⟨χS, χT, hW, hexp⟩ := hω
  obtain ⟨η, hη⟩ := GlobalTheory.Mem.EtaTilde.exists_etaTilde D
  have hpar : V.rank % 2 = V'.rank % 2 := by rw [hs.rank]; omega
  obtain ⟨ω', hω'⟩ := GlobalTheory.T.exists_weilDatum_of_splittingCharacters D ψ hW.std V' W χS χT ⟨η, hη.1, hη.2.2.2, hη.2.2.1, hη.2.1⟩ hW.hecS hW.hecT
    (resEta_parity hW.resS hpar) hW.resT
  refine LowCusp.constTerm_eq_zero hI.const hI.decay hs hθ hW hω' hν h𝓕 M' ∅ 1 F hF v hf
    (fun f' hf' => ?_) κ 𝓝 hκ h𝓝 g
  exact congrFun (hL S S' aS aT hR r V' W M' θ ψ hθ hC.1 hsig ω' ⟨χS, χT, hω', hexp⟩ ν 𝓕 hν h𝓕 F hF v f' hf') 1

end GlobalTheory.PairLift

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftsCuspidalOfLowerTowerLiftsVanishStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLifts_cuspidal_of_lower_tower_lifts_vanish : ∀ (D : D7) (X : ProvA), Inputs D X → LowAll D X → CuspAll D X := by
  first | exact @GlobalTheory.PairLift.cuspAll_of_lowAll | exact GlobalTheory.PairLift.cuspAll_of_lowAll | (intros; apply GlobalTheory.PairLift.cuspAll_of_lowAll <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelInf
noncomputable section

namespace GlobalTheory.HoweGlobal

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def opInf (Bs : Base F E) (G : Geo σ a a') (om : Rep σ G.V G.W) : Set (Module.End ℂ ↥(G.M.Pol Bs.ψ Bs.emb)) :=
  {g | (∃ k ∈ KInf σ G.W Bs.emb, ∀ f : ↥(G.M.Pol Bs.ψ Bs.emb),
      Acts (evI F) (om (1, k)) ⇑(f : SInf F (Fin a × Fin (a + a'))) ⇑((g f : ↥(G.M.Pol Bs.ψ Bs.emb)) : SInf F _)) ∨
    ∃ γ ∈ Lines σ G.W, ∀ f : ↥(G.M.Pol Bs.ψ Bs.emb),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) ⇑(f : SInf F (Fin a × Fin (a + a')))
        ⇑((g f : ↥(G.M.Pol Bs.ψ Bs.emb)) : SInf F _)}

def relInf (Bs : Base F E) (G : Geo σ a a') (om : Rep σ G.V G.W) : Submodule ℂ ↥(G.M.Pol Bs.ψ Bs.emb) :=
  Submodule.span ℂ {x | (∃ γ ∈ Lines σ G.V, ∃ f ∈ G.M.Pol Bs.ψ Bs.emb,
      ActsD (evI F) (fun t => om (γ (Multiplicative.ofAdd t), 1)) ⇑f ⇑(x : SInf F (Fin a × Fin (a + a')))) ∨
    ∃ k ∈ KInf σ G.V Bs.emb, ∃ f f₁ : ↥(G.M.Pol Bs.ψ Bs.emb),
      Acts (evI F) (om (k, 1)) ⇑(f : SInf F (Fin a × Fin (a + a'))) ⇑(f₁ : SInf F (Fin a × Fin (a + a'))) ∧ x = f₁ - f}

def opFin (G : Geo σ a a') (om : Rep σ G.V G.W) (v : Pl F) :
    Set (Module.End ℂ ↥(SB (Fin a × Fin (a + a') → Fv F v))) :=
  {g | ∃ h ∈ UAt σ G.W (evFin F v), ∀ φ : ↥(SB (Fin a × Fin (a + a') → Fv F v)),
    Acts (evFin F v) (om (1, h)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ)
      ((g φ : ↥(SB (Fin a × Fin (a + a') → Fv F v))) : (Fin a × Fin (a + a') → Fv F v) → ℂ)}

def relFin (G : Geo σ a a') (om : Rep σ G.V G.W) (v : Pl F) : Submodule ℂ ↥(SB (Fin a × Fin (a + a') → Fv F v)) :=
  (augAt om v).comap (SB (Fin a × Fin (a + a') → Fv F v)).subtype

end GlobalTheory.HoweGlobal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankChainParamsTrivialBoundRapidDecay
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankChainParamsTrivialBoundRapidDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.EvenOnto.parBound_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ParBound D := by
  intro hCRD D c hc j hj s hs u B hB
  obtain ⟨hu0, hpar⟩ := hB
  have hex : ∃ v, PiLocalization₂.val u v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hu0
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact h v
  obtain ⟨v, hv⟩ := hex
  set f : GA D s.V → ℂ := fun g => conj (PiLocalization₂.val u v g) with hfdef
  have h3 : GlobalTheory.LFun.IsParamFunV s.V c.S f B := hpar v hv
  obtain ⟨h4a, _⟩ := GlobalTheory.T.multiplicity_values_continuous_bounded_hecke_conj hCRD D c hc j hj s hs
  obtain ⟨hcont, ⟨C, hC⟩, hinv, hlev, _⟩ := h4a u v
  have hsph : SphOff (s.J : Set (GA D s.V)) 1 c.S := hs.sph
  have hfmem : f ∈ GlobalTheory.FinZeta.bddAut s.V := by
    refine ⟨(Complex.continuous_conj).comp hcont, fun γ hγ g => ?_, C, fun g => ?_⟩
    · simp only [hfdef, hinv γ hγ g]
    · simpa [hfdef] using hC g
  have hf0 : f ≠ 0 := by
    intro h0
    apply hv
    funext g
    have := congrFun h0 g
    simpa [hfdef] using this
  have hlev' : ∀ k ∈ (s.J : Set (GA D s.V)), ∀ g, f (g * k) = (1 : GA D s.V → ℂ) k * f g := by
    intro k hk g
    simp only [hfdef, hlev k hk g, Pi.one_apply, one_mul]
  obtain ⟨a, ha⟩ := GlobalTheory.T.sphericalOperator_eigenvalues_determined_by_params D s.V (s.J : Set (GA D s.V)) 1 c.S hsph B
  obtain ⟨B', hB', hbd⟩ := GlobalTheory.T.exists_satake_parameters_bounded_eigenfunction D s.V _ _ c.S hsph f hfmem hf0 hlev' a (fun P d R hR => ha f h3 P d R hR)
  intro w hw
  rw [GlobalTheory.LFun.IsParamVecOff.unique h3 hB' hw]
  exact hbd w hw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenRankChainParamsTrivialBoundRapidDecayStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenRankChain_params_trivialBound_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, ParBound D := by
  first | exact @GlobalTheory.EvenOnto.parBound_of_rapidDecay | exact GlobalTheory.EvenOnto.parBound_of_rapidDecay | (intros; apply GlobalTheory.EvenOnto.parBound_of_rapidDecay <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BasicModelsOfFunctoriality
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SignedHC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepRows

theorem exists_dsModel_cart {D : D7} (hDS : GlobalTheory.Published.DiscreteSeriesUpqExists) {V : HSp D} (hV : V.SigOK)
    (S : D.what₂.Tau → SPar) (O C : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (hS : ∀ τ, SignedHC.IsRegular (S τ)) (hc : ∀ τ, (S τ).card = V.rank)
    (hm : ∀ τ, SignedHC.nMinus (S τ) = (V.sig (tauE D τ)).2)
    (hP : ∀ τ (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool), IsEnum (S τ) lam ε → Formalism.QuantumDeterminants.IsHCParam lam)
    (h : ∀ τ, ∃ ε : Fin V.rank → Bool, (O τ)ᴴ * gramAt D V τ * O τ = Formalism.REAL.Jm ε ∧ C τ * O τ = O τ * Formalism.REAL.Jm ε) :
    ∃ M : DSModel V S, cart M = C := by

  have hperm : ∀ τ, ∃ σ : Equiv.Perm (Fin V.rank), ∃ (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool), IsEnum (S τ) lam ε ∧
      ((O τ).submatrix id σ)ᴴ * gramAt D V τ * (O τ).submatrix id σ = Formalism.REAL.Jm ε ∧
      C τ * (O τ).submatrix id σ = (O τ).submatrix id σ * Formalism.REAL.Jm ε :=
    fun τ => GlobalTheory.GridJoin.exists_perm_onb hV τ (hS τ) (hc τ) (hm τ) (h τ)
  choose σ lam ε hEn hGr hCa using hperm
  obtain ⟨M, hMc, -⟩ := GlobalTheory.dsModel_of_onb_cart D hDS V S (fun τ => (O τ).submatrix id (σ τ)) C
    (fun τ => ⟨lam τ, ε τ, hEn τ, hP τ (lam τ) (ε τ) (hEn τ), hGr τ⟩) (fun τ => ⟨ε τ, hGr τ, hCa τ⟩)
  exact ⟨M, hMc⟩

private theorem exists_int_eq_half_add_of_mem_parPi (G : GlobalTheory.SignedHC.GridData) (hs : Odd G.s) (i : ℕ) (x : ℚ) (b : Bool)
    (hx : (x, b) ∈ G.parPi i) : ∃ z : ℤ, x = 1 / 2 + z := by
  rcases GlobalTheory.SignedHC.GridData.mem_parPi.1 hx with ⟨l, -, hl⟩ | ⟨hc, -⟩ | ⟨l, -, -, hl, -⟩
  · simp only [Prod.mk.injEq] at hl
    refine ⟨G.v 2 + ((G.m : ℤ) + 1 - l) * G.ga, ?_⟩
    rw [hl.1, GlobalTheory.SignedHC.GridData.a]
    push_cast
    ring
  · dsimp only at hc
    obtain ⟨j, -, -, hj⟩ := GlobalTheory.SignedHC.GridData.mem_cloudHalf.1 hc
    refine ⟨G.v j - 1, ?_⟩
    rw [hj, GlobalTheory.SignedHC.GridData.vHalf]
    push_cast
    ring
  · dsimp only at hl
    obtain ⟨w, hw⟩ := hs
    obtain ⟨z, hz⟩ := GlobalTheory.SignedHC.inCoset_block _ _ x hl
    refine ⟨G.cen l + w + z, ?_⟩
    have hlen : ((G.s - 1 : ℕ) : ℚ) = 2 * w := by
      rw [hw, Nat.add_sub_cancel]; push_cast; ring
    rw [hz, hlen]
    push_cast
    ring

theorem isHCParam_parPi (D : D7) (C : ℝ) (i : ℕ) (τ : D.what₂.Tau) {n : ℕ} (lam : Fin n → ℝ) (ε : Fin n → Bool)
    (hn : n = rankP D i) (hE : IsEnum ((num D C τ).parPi i) lam ε) : Formalism.QuantumDeterminants.IsHCParam lam := by
  obtain ⟨hanti, q, hq, hS⟩ := hE
  refine ⟨hanti, fun a => ?_⟩
  have hmem : (q a, ε a) ∈ (num D C τ).parPi i := by
    rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
  obtain ⟨z, hz⟩ := exists_int_eq_half_add_of_mem_parPi (num D C τ) (odd_sLen D) i (q a) (ε a) hmem
  obtain ⟨k, hk⟩ := even_rankP D i
  refine ⟨z - k + 1, ?_⟩
  rw [hq a, hz, hn, hk]
  push_cast
  ring

theorem coreModels_of_upq (hDS : GlobalTheory.Published.DiscreteSeriesUpqExists) : CoreModels := by
  intro D _ T L μ0 _ sc G W M _ i hi
  have hin : (Node.core i).InRange D.R.m := hi
  obtain ⟨hrank, hsig, hsg, -⟩ := G.isV hin (fun j h => by cases h)
  have hg : 0 < (gap D sc.cGap) := lt_of_le_of_lt (Nat.zero_le _) (sLen_lt_gap D sc.cGap)
  have hs1 : 1 ≤ sLen D := by unfold sLen; omega
  refine exists_dsModel_cart hDS hsig (Node.par D sc.cGap (.core i)) (W.onb (.core i)) (W.cart (.core i))
    (fun τ => ?_) (fun τ => ?_) (fun τ => ?_) (fun τ lam ε hE => ?_) (W.onb_is (.core i) hin)
  · exact GlobalTheory.PiCounts.isRegular_parPi (num_nearMid D sc.cGap τ) hs1 (sLen_lt_gap D sc.cGap) hi
  · exact (GlobalTheory.PiCounts.card_parPi (num_nearMid D sc.cGap τ) hs1 (sLen_lt_gap D sc.cGap) hi).trans
      ((num_ranks D sc.cGap τ i 0).2.1.trans hrank.symm)
  · show nMinus ((num D sc.cGap τ).parPi i) = _
    rw [GlobalTheory.PiCounts.nMinus_parPi hg i, hsg (tauE D τ)]
    rfl
  · exact isHCParam_parPi D sc.cGap i τ lam ε hrank hE

end GlobalTheory.SepRows

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainFiniteDimensionalAndPeterssonProdu
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainFiniteDimensionalAndPeterssonProdu
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenMetric

variable {D : D7}

theorem finDim : GlobalTheory.Published.HarishChandraFinite → ∀ D : D7, FinDim D := by
  intro hP D c hc j _ s hs
  obtain ⟨U, hU, hUJ⟩ := hs.isOpen
  have : FiniteDimensional ℂ (Mult c.θ s.M (s.J : Set (GA D s.V)) 1) :=
    GlobalTheory.MultFinite.hcFinite hP hc.inf ⟨U, hU, fun k hk hf => ⟨hUJ k hk hf, rfl⟩⟩
  exact Module.Finite.map _ _

theorem metEx : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D := by
  intro hP D c hc j _ s hs
  obtain ⟨ipD, hpure, hhermD, hposD⟩ := GlobalTheory.ChainOnto.exists_ipD_smT D s.V s.par s.M
  set J : Set (GA D s.V) := (s.J : Set (GA D s.V))
  set χ : GA D s.V → ℂ := 1
  have hS : SchurMult c.θ s.M J χ s.ν s.fd := GlobalTheory.MultFinite.schurMult hP s.ν s.fd
  obtain ⟨hI1, hI2⟩ := GlobalTheory.SchurConst.ipM_posDef D c.θ s.V s.par s.M J χ s.ν s.fd hc.inf hs.haar hs.fund hS
    (GlobalTheory.GardingVec.sm_ne_bot D s.V s.par s.M)
  let T : s.CC c → MMap s.M := fun x => PiTensorProduct.lift.symm (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))
  have hT : ∀ x : s.CC c, T x ∈ Mult c.θ s.M J χ := fun x => (mem_multT c.θ s.M J χ _).1 x.2
  have hTadd : ∀ x y : s.CC c, T (x + y) = T x + T y := fun x y => by
    simp only [T, Submodule.coe_add, map_add (f := _)]
  have hTsmul : ∀ (a : ℂ) (x : s.CC c), T (a • x) = a • T x := fun a x => by
    simp only [T, Submodule.coe_smul, map_smul]
  have hlin : ∀ x y y' : s.CC c, ∀ a : ℂ,
      ipM s.M s.ν s.fd (T x) (T y + a • T y') = ipM s.M s.ν s.fd (T x) (T y) + a * ipM s.M s.ν s.fd (T x) (T y') :=
    fun x y y' a => (hI1 _ (hT x) _ (hT y) _ (hT y') a).1
  have hsym : ∀ x y : s.CC c, ipM s.M s.ν s.fd (T y) (T x) = star (ipM s.M s.ν s.fd (T x) (T y)) :=
    fun x y => (hI1 _ (hT x) _ (hT y) _ (hT y) 0).2
  have hzero : ∀ x : s.CC c, ipM s.M s.ν s.fd (T x) (T 0) = 0 := fun x => by
    have h := hlin x 0 0 1
    rw [one_smul, one_mul, show T 0 + T 0 = T 0 by simp [T]] at h
    linear_combination -h
  have hlin' : ∀ x y y' : s.CC c, ∀ a : ℂ,
      ipM s.M s.ν s.fd (T x) (T (y + a • y')) = ipM s.M s.ν s.fd (T x) (T y) + a * ipM s.M s.ν s.fd (T x) (T y') :=
    fun x y y' a => by rw [hTadd, hTsmul]; exact hlin x y y' a
  let ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => ipM s.M s.ν s.fd (T y) (T x))
      (fun x x' y => by simpa using hlin' y x x' 1)
      (fun a x y => by
        have h := hlin' y 0 x a
        rw [zero_add, hzero, zero_add] at h
        simpa using h)
      (fun x y y' => by
        rw [hsym x (y + y'), hsym x y, hsym x y']
        have h := hlin' x y y' 1
        rw [one_mul, one_smul] at h
        rw [h, star_add])
      (fun a x y => by
        rw [hsym x (a • y), hsym x y]
        have h := hlin' x 0 y a
        rw [zero_add, hzero, zero_add] at h
        rw [h, star_mul', smul_eq_mul, starRingEnd_apply])
  have hip : ∀ x y, ip x y = ipM s.M s.ν s.fd (T y) (T x) := fun _ _ => rfl
  have hpair : ∀ x y : s.CC c, ∀ w w', IntegrableOn (fun g => PiLocalization₂.val x w g * conj (PiLocalization₂.val y w' g)) s.fd s.ν ∧
      ∫ g in s.fd, PiLocalization₂.val x w g * conj (PiLocalization₂.val y w' g) ∂s.ν = ip x y * ipD w w' := by
    intro x y
    refine GlobalTheory.ChainMetric.integ_pair (μ := s.ν) (A := s.fd) (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))
      (y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ipD (ip x y) ?_
    intro v v'
    obtain ⟨hi, he⟩ := ipM_spec s.M s.ν s.fd (T y) (T x) (hS hc.inf hs.haar hs.fund _ (hT y) _ (hT x)) v' v
    have e : (fun g => (x : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) (PiTensorProduct.tprod ℂ v) g *
        conj ((y : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) (PiTensorProduct.tprod ℂ v') g)) = fun g => star (T y v' g) * T x v g := by
      funext g
      rw [GlobalTheory.ChainMetric.val_tprod, GlobalTheory.ChainMetric.val_tprod, starRingEnd_apply, mul_comm]
    rw [e, hip, hpure]
    exact ⟨hi, he⟩
  refine ⟨ipD, ip, hpure, hhermD, hposD, fun x y => ?_, fun x hx => ?_, fun x y w w' => (hpair x y w w').1,
    fun x y w w' => (hpair x y w w').2⟩
  · rw [hip, hip, hsym, starRingEnd_apply]
  · rw [hip]
    refine hI2 _ (hT x) fun h0 => hx ?_
    exact Submodule.coe_eq_zero.1 ((LinearEquiv.map_eq_zero_iff _).1 h0)

theorem finDim_and_metEx : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D ∧ MetEx D :=
  fun h h' D => ⟨finDim h D, metEx h' D⟩

end GlobalTheory.EvenMetric

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainFiniteDimensionalAndPeterssonProduStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenThetaChain_finiteDimensional_and_peterssonProducts : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D ∧ MetEx D := by
  first | exact @GlobalTheory.EvenMetric.finDim_and_metEx | exact GlobalTheory.EvenMetric.finDim_and_metEx | (intros; apply GlobalTheory.EvenMetric.finDim_and_metEx <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactorisationFromTopLine
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepRows

theorem factor_multT_le_empty {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) (J : Set (GA D V))
    (χ : GA D V → ℂ) : MultT θ M J χ ≤ MultT θ M ∅ 1 := by

  refine Submodule.map_mono (Submodule.span_mono ?_)
  intro T hT
  exact ⟨hT.aut, hT.cusp, fun v k hk g => by simp at hk, hT.equiv, hT.cont⟩

end GlobalTheory.SepRows
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurMultMultiplicitySpacesOfRapidDecay
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurMultMultiplicitySpacesOfRapidDecay
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SchurConst

theorem schurMult_all : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → SchurMult θ M J χ μ 𝓕 :=
  fun hP _ _ _ _ _ _ _ _ μ 𝓕 _ _ => GlobalTheory.MultFinite.schurMult hP μ 𝓕

end GlobalTheory.SchurConst

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchurMultMultiplicitySpacesOfRapidDecayStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schurMult_multiplicitySpaces_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), μ.IsHaarMeasure → IsFundamentalDomain (GQ V) 𝓕 μ → SchurMult θ M J χ μ 𝓕 := by
  first | exact @GlobalTheory.SchurConst.schurMult_all | exact GlobalTheory.SchurConst.schurMult_all | (intros; apply GlobalTheory.SchurConst.schurMult_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeImageAdelicUnitaryStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Matrix
open Formalism.L2.DIV (Pl)
open Formalism.IndefR.Lev (EAf)
open Formalism.IndefR.Datum (IsSelfDualC)
open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents GlobalTheory.AdIsom
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLattice_image_adelicUnitary : ∀ D : D7, ImageSt D := by
  first | exact @GlobalTheory.AdIsomImage.imageSt | exact GlobalTheory.AdIsomImage.imageSt | (intros; apply GlobalTheory.AdIsomImage.imageSt <;> assumption)
end
