module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjointIffBiextensionPullbacksIsomorphic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionUniformisingSpaceIsType
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedComplexFibreMarkedLatticeClass

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomMatrixLiftOfOrderActionExponential
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomMatrixLiftOfOrderActionExponential
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.ExpLin

theorem exists_ringHom_matrix_lift : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ) (O : Type) [Ring O] (act : O → (G ⟶ G)), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act b ≫ act a) → (∀ a b, act (a + b) = act a * act b) → ∀ (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsExp y e → ∃ ρ' : O →+* Matrix (Fin g) (Fin g) ℂ, ∀ a z, e (ρ' a *ᵥ z) = e z ≫ act a := by
  intro X G _ _ g O _ act hab hsm hhom h1 hmul hadd y e he
  have H := fun a => GlobalTheory.T.existsUnique_linear_lift_of_abelianEndomorphism X G g hab hsm y e e (act a) he he (hhom a)
  let M : O → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := fun a => (H a).exists.choose
  have hM : ∀ a z, e (M a z) = e z ≫ act a := fun a => (H a).exists.choose_spec
  have key : ∀ a (N : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), (∀ z, e (N z) = e z ≫ act a) → N = M a :=
    fun a N hN => (H a).unique hN (hM a)
  have M1 : M 1 = LinearMap.id := (key 1 LinearMap.id (fun z => by simp [h1])).symm
  have Mmul : ∀ a b, M (a * b) = M a ∘ₗ M b := fun a b =>
    (key (a * b) (M a ∘ₗ M b) (fun z => by
      simp only [LinearMap.comp_apply, hM, hmul, Category.assoc])).symm
  have Madd : ∀ a b, M (a + b) = M a + M b := fun a b =>
    (key (a + b) (M a + M b) (fun z => by
      rw [LinearMap.add_apply, he.1, hM, hM, hadd, MonObj.comp_mul])).symm
  let f : O →* Matrix (Fin g) (Fin g) ℂ :=
    { toFun := fun a => LinearMap.toMatrix' (M a)
      map_one' := by simp only [M1, LinearMap.toMatrix'_id]
      map_mul' := fun a b => by simp only [Mmul, LinearMap.toMatrix'_comp] }
  refine ⟨RingHom.mk' f (fun a b => by simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, Madd, map_add (f := _)]), ?_⟩
  intro a z
  show e (LinearMap.toMatrix' (M a) *ᵥ z) = _
  rw [LinearMap.toMatrix'_mulVec, hM]

end GlobalTheory.ExpLin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomMatrixLiftOfOrderActionExponentialStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_matrix_lift_of_orderAction_exponential : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ) (O : Type) [Ring O] (act : O → (G ⟶ G)), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → (∀ a, IsMonHom (act a)) → act 1 = 𝟙 G → (∀ a b, act (a * b) = act b ≫ act a) → (∀ a b, act (a + b) = act a * act b) → ∀ (y : Sp ℂ ⟶ X) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsExp y e → ∃ ρ' : O →+* Matrix (Fin g) (Fin g) ℂ, ∀ a z, e (ρ' a *ᵥ z) = e z ≫ act a := by
  first | exact @GlobalTheory.ExpLin.exists_ringHom_matrix_lift | exact GlobalTheory.ExpLin.exists_ringHom_matrix_lift | (intros; apply GlobalTheory.ExpLin.exists_ringHom_matrix_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImHermFormAlternatingNondegenerateOnLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImHermFormAlternatingNondegenerateOnLattice
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

namespace GlobalTheory.HermImNondeg

theorem hermForm_add_right' {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  simp only [hermForm, star_add, Matrix.mulVec_add, dotProduct_add]

theorem hermForm_smul_right' {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (a : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z (a • w) = star a * hermForm Hm z w := by
  simp only [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hermForm_self_star {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (z : Fin g → ℂ) :
    star (hermForm Hm z z) = hermForm Hm z z := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', Pi.star_apply, star_star, h.apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem im_hermForm_alternating_nondegenerate (La : Type) [AddCommGroup La] (g : ℕ) (P : La →+ (Fin g → ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ) (EF : LinearMap.BilinForm ℤ La) (hP : Function.Injective P)
    (hspan : Submodule.span ℝ (Set.range P) = ⊤) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re)
    (hEF : ∀ x y, (hermForm Hm (P x) (P y)).im = EF x y) :
    (∀ x, EF x x = 0) ∧ ∀ x, (∀ y, EF x y = 0) → x = 0 := by
  refine ⟨fun x => ?_, fun x hx => ?_⟩
  · have hc : ((EF x x : ℤ) : ℝ) = 0 := by
      rw [← hEF]
      have h1 := congrArg Complex.im (hermForm_self_star hH (P x))
      have h2 : (star (hermForm Hm (P x) (P x))).im = -(hermForm Hm (P x) (P x)).im := Complex.conj_im _
      linarith
    exact_mod_cast hc
  · set z := P x with hz
    have key : ∀ w : Fin g → ℂ, (hermForm Hm z w).im = 0 := by
      intro w
      have hw : w ∈ Submodule.span ℝ (Set.range P) := hspan ▸ Submodule.mem_top
      induction hw using Submodule.span_induction with
      | mem a ha =>
        obtain ⟨y, rfl⟩ := ha
        rw [hEF, hx y]; simp
      | zero => simp [hermForm]
      | add a b _ _ h1 h2 => rw [hermForm_add_right', Complex.add_im, h1, h2, add_zero]
      | smul r a _ h1 =>
        rw [← Complex.coe_smul, hermForm_smul_right']
        simp [h1]
    have hI := key (Complex.I • z)
    rw [hermForm_smul_right'] at hI
    have hre : (hermForm Hm z z).re = 0 := by
      have : (star Complex.I * hermForm Hm z z).im = -(hermForm Hm z z).re := by
        simp [Complex.mul_im]
      linarith
    by_contra hne
    have hz0 : z ≠ 0 := by
      intro h0; apply hne; apply hP; rw [← hz, h0, map_zero]
    have := hpos z hz0
    linarith

end GlobalTheory.HermImNondeg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImHermFormAlternatingNondegenerateOnLatticeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.im_hermForm_alternating_nondegenerate_on_lattice : ∀ (La : Type) [AddCommGroup La] (g : ℕ) (P : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (EF : LinearMap.BilinForm ℤ La), Function.Injective P → Submodule.span ℝ (Set.range P) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ x y, (hermForm Hm (P x) (P y)).im = EF x y) → (∀ x, EF x x = 0) ∧ ∀ x, (∀ y, EF x y = 0) → x = 0 := by
  first | exact @GlobalTheory.HermImNondeg.im_hermForm_alternating_nondegenerate | exact GlobalTheory.HermImNondeg.im_hermForm_alternating_nondegenerate | (intros; apply GlobalTheory.HermImNondeg.im_hermForm_alternating_nondegenerate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexFibreExponentialFullLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexFibreExponentialFullLattice
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix

noncomputable section

namespace GlobalTheory.FibreExp

theorem exists_exp_lattice : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G →
    SmoothOfRelativeDimension g G.hom → ∀ y : Sp ℂ ⟶ X, ∃ (e : (Fin g → ℂ) → (Over.mk y ⟶ G))
      (Λ : Submodule ℤ (Fin g → ℂ)), IsExp y e ∧ DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ ∧
        ∀ z, e z = 1 ↔ z ∈ Λ := by
  intro X G _ _ g hG hgG y
  letI : GrpObj ((Over.pullback y).obj G) := Functor.grpObjObj
  have hj := isGrpPullback_pullback G y
  have hA : IsAbelianScheme ((Over.pullback y).obj G) := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG hj
  have hgA : SmoothOfRelativeDimension g ((Over.pullback y).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback hj.1 hgG
  obtain ⟨L, ⟨u⟩⟩ := GlobalTheory.HomDescentQb.exists_holUnif _ g hA hgA
  obtain ⟨h1, h2⟩ := GlobalTheory.UnifTangent.tangent_bijection u hgA
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.LiePull.exists_pushEquiv hj (𝟙_ _) y (Category.id_comp _).symm
  have he := GlobalTheory.PointUnif.isExp_push hj u h1 h2 Φ hΦ
  exact ⟨fun z => Φ (u.ex z), u.Λ, he, u.discrete, u.full,
    fun z => (map_eq_one_iff Φ Φ.injective).trans (u.ker z)⟩

end GlobalTheory.FibreExp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexFibreExponentialFullLatticeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexFibreExponential_full_lattice : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (g : ℕ), IsAbelianScheme G → SmoothOfRelativeDimension g G.hom → ∀ y : Sp ℂ ⟶ X, ∃ (e : (Fin g → ℂ) → (Over.mk y ⟶ G)) (Λ : Submodule ℤ (Fin g → ℂ)), IsExp y e ∧ DiscreteTopology Λ ∧ Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ ∧ ∀ z, e z = 1 ↔ z ∈ Λ := by
  first | exact @GlobalTheory.FibreExp.exists_exp_lattice | exact GlobalTheory.FibreExp.exists_exp_lattice | (intros; apply GlobalTheory.FibreExp.exists_exp_lattice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomConjOfTraceEqHarrisTaylorOrder
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomOrderPiMatrixEmbeddings
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomOrderPiMatrixEmbeddings
noncomputable section

namespace GlobalTheory.UPel.HT.SplitC

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix TensorProduct
open GlobalTheory.UPel.HT

theorem span_embeddings_eq_top (K : Type) [Field K] [NumberField K] :
    Submodule.span ℂ (Set.range fun (c : 𝓞 K) (τ : K →+* ℂ) => τ (c : K)) = ⊤ := by
  rw [eq_top_iff, ← (canonicalEmbedding.latticeBasis K).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  refine ⟨RingOfIntegers.basis K i, ?_⟩
  rw [canonicalEmbedding.latticeBasis_apply, integralBasis_apply]
  rfl

theorem mem_of_embeddings {K : Type} [Field K] [NumberField K] {W : Type} [AddCommGroup W] [Module ℂ W]
    (V : Submodule ℂ W) (L : ((K →+* ℂ) → ℂ) → W) (hadd : ∀ f g, L (f + g) = L f + L g)
    (hsmul : ∀ (a : ℂ) f, L (a • f) = a • L f) (h : ∀ c : 𝓞 K, L (fun τ => τ (c : K)) ∈ V)
    (f : (K →+* ℂ) → ℂ) : L f ∈ V := by
  let Ll : ((K →+* ℂ) → ℂ) →ₗ[ℂ] W := { toFun := L, map_add' := hadd, map_smul' := hsmul }
  have hf : f ∈ Submodule.span ℂ (Set.range fun (c : 𝓞 K) (τ : K →+* ℂ) => τ (c : K)) := by
    rw [span_embeddings_eq_top]; trivial
  have : Ll f ∈ (Submodule.span ℂ (Set.range fun (c : 𝓞 K) (τ : K →+* ℂ) => τ (c : K))).map Ll :=
    Submodule.mem_map_of_mem hf
  have hle : (Submodule.span ℂ (Set.range fun (c : 𝓞 K) (τ : K →+* ℂ) => τ (c : K))).map Ll ≤ V := by
    rw [Submodule.map_span_le]
    rintro _ ⟨c, rfl⟩
    exact h c
  exact hle this

variable {p : ℕ} [Fact p.Prime]

def padicToComplex (j : PadicAlgCl p ≃+* ℂ) : ℤ_[p] →+* ℂ :=
  j.toRingHom.comp ((algebraMap ℚ_[p] (PadicAlgCl p)).comp PadicInt.Coe.ringHom)

def evalTensor (F : Type) [Field F] (κ : ℤ_[p] →+* ℂ) (τ : F →+* ℂ) : 𝓞 F ⊗[ℤ] ℤ_[p] →+* ℂ :=
  (Algebra.TensorProduct.lift (τ.comp (algebraMap (𝓞 F) F)).toIntAlgHom κ.toIntAlgHom
    (fun _ _ => Commute.all _ _)).toRingHom

theorem evalTensor_tmul (F : Type) [Field F] (κ : ℤ_[p] →+* ℂ) (τ : F →+* ℂ) (c : 𝓞 F) (z : ℤ_[p]) :
    evalTensor F κ τ (c ⊗ₜ z) = τ (c : F) * κ z := by
  simp [evalTensor]

def bigPhi (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) :
    (D.O ⊗[ℤ] ℤ_[p]) →+* ((D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ) :=
  Pi.ringHom fun τ => (evalTensor D.F κ τ).mapMatrix.comp e.toRingHom

theorem bigPhi_algebraMap (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) (c : 𝓞 D.F) (τ : D.F →+* ℂ) :
    bigPhi D κ e (algebraMap (𝓞 D.F) D.O c ⊗ₜ 1) τ = Matrix.scalar (Fin D.m) (τ (c : D.F)) := by
  have h1 : (algebraMap (𝓞 D.F) D.O c ⊗ₜ[ℤ] (1 : ℤ_[p])) = algebraMap (𝓞 D.F) (D.O ⊗[ℤ] ℤ_[p]) c := rfl
  rw [h1]
  show (evalTensor D.F κ τ).mapMatrix (e (algebraMap (𝓞 D.F) (D.O ⊗[ℤ] ℤ_[p]) c)) = _
  rw [e.commutes c, Matrix.algebraMap_eq_diagonal]
  ext i j
  simp [Matrix.diagonal_apply, Matrix.scalar_apply, Algebra.TensorProduct.algebraMap_apply, evalTensor_tmul]
  split_ifs <;> simp [evalTensor_tmul]

theorem tmul_one_comm {A : Type} [Ring A] (z : ℤ_[p]) (a : A ⊗[ℤ] ℤ_[p]) :
    a * ((1 : A) ⊗ₜ z) = ((1 : A) ⊗ₜ z) * a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
  | add a b ha hb => rw [add_mul, mul_add, ha, hb]

theorem bigPhi_one_tmul (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) (z : ℤ_[p]) :
    ∃ w : 𝓞 D.F ⊗[ℤ] ℤ_[p], bigPhi D κ e ((1 : D.O) ⊗ₜ z) = fun τ => Matrix.scalar (Fin D.m) (evalTensor D.F κ τ w) := by
  have hc : e ((1 : D.O) ⊗ₜ z) ∈ Set.center (Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) := by
    rw [Semigroup.mem_center_iff]
    intro g
    obtain ⟨a, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, tmul_one_comm]
  rw [Matrix.center_eq_range] at hc
  obtain ⟨w, hw⟩ := hc
  refine ⟨w, funext fun τ => ?_⟩
  show (evalTensor D.F κ τ).mapMatrix (e ((1 : D.O) ⊗ₜ z)) = _
  rw [← hw]
  ext i j
  simp only [Matrix.scalar_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem mem_span_bigPhi (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) (y : D.O ⊗[ℤ] ℤ_[p]) :
    bigPhi D κ e y ∈ Submodule.span ℂ (Set.range ((bigPhi D κ e).comp Algebra.TensorProduct.includeLeftRingHom)) := by
  set V := Submodule.span ℂ (Set.range ((bigPhi D κ e).comp Algebra.TensorProduct.includeLeftRingHom))
  have hφ : ∀ x : D.O, bigPhi D κ e (x ⊗ₜ 1) ∈ V := fun x => Submodule.subset_span ⟨x, rfl⟩
  have hL : ∀ (x : D.O) (f : (D.F →+* ℂ) → ℂ),
      (fun τ => Matrix.scalar (Fin D.m) (f τ)) * bigPhi D κ e (x ⊗ₜ 1) ∈ V := by
    intro x
    apply mem_of_embeddings V (fun f => (fun τ => Matrix.scalar (Fin D.m) (f τ)) * bigPhi D κ e (x ⊗ₜ 1))
    · intro f g
      funext τ
      simp only [Pi.mul_apply, Pi.add_apply, map_add (f := _), _root_.add_mul]
    · intro a f
      funext τ
      ext i j
      simp [Matrix.scalar_apply, Matrix.diagonal_mul, _root_.mul_assoc]
    · intro c
      have : (fun τ : D.F →+* ℂ => Matrix.scalar (Fin D.m) (τ (c : D.F))) =
          bigPhi D κ e (algebraMap (𝓞 D.F) D.O c ⊗ₜ 1) := funext fun τ => (bigPhi_algebraMap D κ e c τ).symm
      rw [this, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul]
      exact hφ _
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul x z =>
    obtain ⟨w, hw⟩ := bigPhi_one_tmul D κ e z
    have : x ⊗ₜ[ℤ] z = ((1 : D.O) ⊗ₜ z) * (x ⊗ₜ 1) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.one_mul, _root_.mul_one]
    rw [this, map_mul, hw]
    exact hL x _
  | add a b ha hb => rw [map_add (f := _)]; exact V.add_mem ha hb

theorem bigPhi_symm_single (D : Datum p) (κ : ℤ_[p] →+* ℂ)
    (e : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) (i j : Fin D.m) (c : 𝓞 D.F) :
    bigPhi D κ e (e.symm (Matrix.single i j (c ⊗ₜ 1))) = fun τ => Matrix.single i j (τ (c : D.F)) := by
  funext τ
  show (evalTensor D.F κ τ).mapMatrix (e (e.symm _)) = _
  rw [e.apply_symm_apply]
  ext k l
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp [evalTensor_tmul]

theorem exists_ringHom_pi_matrix : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p),
    ∃ φ : D.O →+* ((D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ),
      (∀ (c : 𝓞 D.F) τ, φ (algebraMap (𝓞 D.F) D.O c) τ = Matrix.scalar (Fin D.m) (τ (c : D.F))) ∧
        Submodule.span ℂ (Set.range φ) = ⊤ := by
  intro p _ D
  obtain ⟨e⟩ := D.splitP
  obtain ⟨j⟩ := GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex p
  set κ := padicToComplex j
  refine ⟨(bigPhi D κ e).comp Algebra.TensorProduct.includeLeftRingHom, fun c τ => bigPhi_algebraMap D κ e c τ, ?_⟩
  rw [eq_top_iff]
  intro X _
  have hX : X = ∑ i, ∑ k, (fun τ => Matrix.single i k (X τ i k)) := by
    funext τ
    simp only [Finset.sum_apply]
    exact Matrix.matrix_eq_sum_single (X τ)
  rw [hX]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun k _ => ?_
  apply mem_of_embeddings _ (fun f => fun τ => Matrix.single i k (f τ)) (f := fun τ => X τ i k)
  · intro f g; funext τ; simp [Matrix.single_add]
  · intro a f; funext τ; simp [Matrix.smul_single]
  · intro c
    rw [← bigPhi_symm_single D κ e i k c]
    exact mem_span_bigPhi D κ e _

end GlobalTheory.UPel.HT.SplitC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomOrderPiMatrixEmbeddingsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_order_pi_matrix_embeddings : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), ∃ φ : D.O →+* ((D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ), (∀ (c : 𝓞 D.F) τ, φ (algebraMap (𝓞 D.F) D.O c) τ = Matrix.scalar (Fin D.m) (τ (c : D.F))) ∧ Submodule.span ℂ (Set.range φ) = ⊤ := by
  first | exact @GlobalTheory.UPel.HT.SplitC.exists_ringHom_pi_matrix | exact GlobalTheory.UPel.HT.SplitC.exists_ringHom_pi_matrix | (intros; apply GlobalTheory.UPel.HT.SplitC.exists_ringHom_pi_matrix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentationsEqualTracesConjugate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulMulEqOfTraceEq
namespace GlobalTheory.TraceEqualFinrank

open Module

theorem trace_eq_finrank_range {g : ℕ} (P : Matrix (Fin g) (Fin g) ℂ) (hP : IsIdempotentElem P) :
    Matrix.trace P = (finrank ℂ (LinearMap.range (Matrix.toLin' P)) : ℂ) := by
  have he : IsIdempotentElem (Matrix.toLin' P) := by
    change Matrix.toLin' P * Matrix.toLin' P = Matrix.toLin' P
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP.eq]
  have hproj := (LinearMap.isProj_range_iff_isIdempotentElem (Matrix.toLin' P)).mpr he
  rw [← Matrix.trace_toLin'_eq, hproj.trace]

theorem exists_mul_mul_eq_of_trace_eq {g : ℕ} (P P' : Matrix (Fin g) (Fin g) ℂ)
    (hP : IsIdempotentElem P) (hP' : IsIdempotentElem P')
    (h : Matrix.trace P = Matrix.trace P') :
    ∃ (X : Matrix (Fin g) (Fin g) ℂ) (Y : Matrix (Fin g) (Fin g) ℂ), Y * P' * X = P := by
  have hrk : finrank ℂ (LinearMap.range (Matrix.toLin' P')) =
      finrank ℂ (LinearMap.range (Matrix.toLin' P)) := by
    have h2 := (trace_eq_finrank_range P' hP').symm.trans (h.symm.trans (trace_eq_finrank_range P hP))
    exact_mod_cast h2
  let e := LinearEquiv.ofFinrankEq _ _ hrk
  have hid' : ∀ w ∈ LinearMap.range (Matrix.toLin' P'), Matrix.toLin' P' w = w := by
    rintro w ⟨u, rfl⟩
    rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, hP'.eq]
  let Xl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := (LinearMap.range (Matrix.toLin' P')).subtype ∘ₗ
    e.symm.toLinearMap ∘ₗ (Matrix.toLin' P).rangeRestrict
  let Yl : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := (LinearMap.range (Matrix.toLin' P)).subtype ∘ₗ
    e.toLinearMap ∘ₗ (Matrix.toLin' P').rangeRestrict
  refine ⟨LinearMap.toMatrix' Xl, LinearMap.toMatrix' Yl, ?_⟩
  apply Matrix.toLin'.injective
  rw [Matrix.toLin'_mul, Matrix.toLin'_mul, Matrix.toLin'_toMatrix', Matrix.toLin'_toMatrix']
  refine LinearMap.ext fun v => ?_
  have hw := (e.symm ((Matrix.toLin' P).rangeRestrict v)).2
  have h1 : (Matrix.toLin' P').rangeRestrict
      (Matrix.toLin' P' ((e.symm ((Matrix.toLin' P).rangeRestrict v) : Fin g → ℂ))) =
      e.symm ((Matrix.toLin' P).rangeRestrict v) := by
    apply Subtype.ext
    change Matrix.toLin' P' (Matrix.toLin' P' _) = _
    rw [hid' _ hw, hid' _ hw]
  change ((e ((Matrix.toLin' P').rangeRestrict
      (Matrix.toLin' P' ((e.symm ((Matrix.toLin' P).rangeRestrict v) : Fin g → ℂ)))) :
      LinearMap.range (Matrix.toLin' P)) : Fin g → ℂ) = Matrix.toLin' P v
  rw [h1, LinearEquiv.apply_symm_apply]
  rfl

end GlobalTheory.TraceEqualFinrank
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentationsEqualTracesConjugate
open Matrix

namespace GlobalTheory

def piMatUnit {I : Type} [DecidableEq I] (m : ℕ) (τ : I) (i j : Fin m) :
    I → Matrix (Fin m) (Fin m) ℂ :=
  Pi.single τ (Matrix.single i j 1)

lemma piMatUnit_mul {I : Type} [DecidableEq I] (m : ℕ) (τ τ' : I) (i j k l : Fin m) :
    piMatUnit m τ i j * piMatUnit m τ' k l =
      if τ = τ' ∧ j = k then piMatUnit m τ i l else 0 := by
  funext ρ
  simp only [piMatUnit, Pi.mul_apply]
  by_cases h1 : τ = τ'
  · subst h1
    by_cases h2 : j = k
    · subst h2
      by_cases h3 : ρ = τ
      · subst h3; simp [Matrix.single_mul_single_same]
      · simp [Pi.single_apply, h3]
    · by_cases h3 : ρ = τ
      · subst h3; simp [Matrix.single_mul_single_of_ne, h2]
      · simp [Pi.single_apply, h3, h2]
  · by_cases h3 : ρ = τ
    · subst h3
      have : ρ ≠ τ' := h1
      simp [Pi.single_apply, this, h1]
    · simp [Pi.single_apply, h3, h1]

lemma piMatUnit_decomp {I : Type} [Fintype I] [DecidableEq I] (m : ℕ)
    (x : I → Matrix (Fin m) (Fin m) ℂ) :
    x = ∑ τ, ∑ i, ∑ j, x τ i j • piMatUnit m τ i j := by
  funext ρ
  ext a b
  simp only [Finset.sum_apply, Matrix.sum_apply, Pi.smul_apply, Matrix.smul_apply, piMatUnit,
    Pi.single_apply]
  simp only [show ∀ (c : Prop) [Decidable c] (M : Matrix (Fin m) (Fin m) ℂ),
      (if c then M else 0) a b = if c then M a b else 0 from fun c _ M => by split_ifs <;> rfl]
  simp [Matrix.zero_apply, Matrix.single_apply, mul_ite, ite_and, Finset.sum_ite_eq,
    Finset.sum_ite_eq']

lemma sum_piMatUnit_diag {I : Type} [Fintype I] [DecidableEq I] (m : ℕ) (τ : I) :
    ∑ i, piMatUnit m τ i i = Pi.single τ 1 := by
  funext ρ
  ext a b
  by_cases h : ρ = τ
  · subst h
    simp only [piMatUnit, Finset.sum_apply, Matrix.sum_apply, Pi.single_eq_same, Matrix.single_apply,
      Matrix.one_apply]
    rcases eq_or_ne a b with rfl | hab
    · simp
    · simp [hab]
  · simp [piMatUnit, Finset.sum_apply, Matrix.sum_apply, Pi.single_apply, h]

lemma exists_mul_idem_mul_eq_of_trace_eq {g : ℕ} (P P' : Matrix (Fin g) (Fin g) ℂ)
    (hP : IsIdempotentElem P) (hP' : IsIdempotentElem P') (ht : P.trace = P'.trace) :
    ∃ X Y : Matrix (Fin g) (Fin g) ℂ, Y * P' * X = P := by
  first
  | exact @_root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq
  | exact _root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq
  | (apply _root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.TraceEqualFinrank.exists_mul_mul_eq_of_trace_eq ..)

theorem conj_of_trace_central_idem_eq :
    ∀ (I : Type) [Fintype I] [DecidableEq I] (m g : ℕ), 0 < m →
      ∀ (σ σ' : (I → Matrix (Fin m) (Fin m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ),
        (∀ τ, (σ (Pi.single τ 1)).trace = (σ' (Pi.single τ 1)).trace) →
          ∃ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h ∧ ∀ x, σ' x * h = h * σ x := by
  intro I _ _ m g hm σ σ' htr
  set z : Fin m := ⟨0, hm⟩

  have hdiag : ∀ (ρ : (I → Matrix (Fin m) (Fin m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ) (τ : I),
      (ρ (Pi.single τ 1)).trace = (m : ℂ) * (ρ (piMatUnit m τ z z)).trace := by
    intro ρ τ
    have hi : ∀ i, (ρ (piMatUnit m τ i i)).trace = (ρ (piMatUnit m τ z z)).trace := by
      intro i
      have e1 : piMatUnit m τ i i = piMatUnit m τ i z * piMatUnit m τ z i := by
        rw [piMatUnit_mul]; simp
      have e2 : piMatUnit m τ z z = piMatUnit m τ z i * piMatUnit m τ i z := by
        rw [piMatUnit_mul]; simp
      rw [e1, e2, map_mul, map_mul, Matrix.trace_mul_comm]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← sum_piMatUnit_diag, map_sum, Matrix.trace_sum, Finset.sum_congr rfl (fun i _ => hi i),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hidem : ∀ (ρ : (I → Matrix (Fin m) (Fin m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ) (τ : I),
      IsIdempotentElem (ρ (piMatUnit m τ z z)) := by
    intro ρ τ
    unfold IsIdempotentElem
    rw [← map_mul, piMatUnit_mul]; simp
  have hm' : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have htr' : ∀ τ, (σ (piMatUnit m τ z z)).trace = (σ' (piMatUnit m τ z z)).trace := by
    intro τ
    have := htr τ
    rw [hdiag σ, hdiag σ'] at this
    exact mul_left_cancel₀ hm' this
  choose X Y hYX using fun τ => exists_mul_idem_mul_eq_of_trace_eq _ _ (hidem σ τ) (hidem σ' τ) (htr' τ)
  set h : Matrix (Fin g) (Fin g) ℂ :=
    ∑ τ, ∑ i, σ' (piMatUnit m τ i z) * X τ * σ (piMatUnit m τ z i) with hh
  set h' : Matrix (Fin g) (Fin g) ℂ :=
    ∑ τ, ∑ i, σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i) with hh'

  have hE : ∀ τ k l, σ' (piMatUnit m τ k l) * h = h * σ (piMatUnit m τ k l) := by
    intro τ k l
    have hL : ∀ τ' i, σ' (piMatUnit m τ k l) * (σ' (piMatUnit m τ' i z) * X τ' * σ (piMatUnit m τ' z i))
        = if τ = τ' ∧ l = i then σ' (piMatUnit m τ k z) * X τ * σ (piMatUnit m τ z l) else 0 := by
      intro τ' i
      rw [← mul_assoc, ← mul_assoc, ← map_mul, piMatUnit_mul]
      split_ifs with hc
      · obtain ⟨rfl, rfl⟩ := hc; rfl
      · simp
    have hR : ∀ τ' i, σ' (piMatUnit m τ' i z) * X τ' * σ (piMatUnit m τ' z i) * σ (piMatUnit m τ k l)
        = if τ = τ' ∧ k = i then σ' (piMatUnit m τ k z) * X τ * σ (piMatUnit m τ z l) else 0 := by
      intro τ' i
      rw [mul_assoc _ (σ _), ← map_mul, piMatUnit_mul]
      by_cases hc : τ' = τ ∧ i = k
      · obtain ⟨rfl, rfl⟩ := hc; simp
      · have hc' : ¬ (τ = τ' ∧ k = i) := fun h => hc ⟨h.1.symm, h.2.symm⟩
        simp [hc, hc']
    rw [hh, Finset.mul_sum, Finset.sum_mul]
    simp only [Finset.mul_sum, Finset.sum_mul, hL, hR]
    simp [ite_and, Finset.sum_ite_eq]
  have hint : ∀ x, σ' x * h = h * σ x := by
    intro x
    rw [piMatUnit_decomp m x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm, hE]

  have hprod : ∀ τ i τ' j, σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i) *
      (σ' (piMatUnit m τ' j z) * X τ' * σ (piMatUnit m τ' z j))
        = if τ = τ' ∧ i = j then σ (piMatUnit m τ i i) else 0 := by
    intro τ i τ' j
    have e : σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i) *
        (σ' (piMatUnit m τ' j z) * X τ' * σ (piMatUnit m τ' z j)) =
        σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i * piMatUnit m τ' j z) * X τ' *
          σ (piMatUnit m τ' z j) := by
      rw [map_mul]; simp only [mul_assoc]
    rw [e, piMatUnit_mul]
    split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc
      rw [show σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z z) * X τ * σ (piMatUnit m τ z i) =
          σ (piMatUnit m τ i z) * (Y τ * σ' (piMatUnit m τ z z) * X τ) * σ (piMatUnit m τ z i) by
            simp only [mul_assoc], hYX τ, ← map_mul, ← map_mul]
      simp [piMatUnit_mul]
    · simp
  have hrow : ∀ τ i, σ (piMatUnit m τ i z) * Y τ * σ' (piMatUnit m τ z i) * h =
      σ (piMatUnit m τ i i) := by
    intro τ i
    rw [hh]
    simp only [Finset.mul_sum, hprod]
    simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq']
  have hinv : h' * h = 1 := by
    rw [hh', Finset.sum_mul]
    simp only [Finset.sum_mul, hrow]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_one σ, ← Finset.univ_sum_single (1 : I → Matrix (Fin m) (Fin m) ℂ), map_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Pi.one_apply, ← sum_piMatUnit_diag, map_sum]
  exact ⟨h, (Matrix.isUnit_iff_isUnit_det h).mpr (Matrix.isUnit_det_of_left_inverse hinv), hint⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentationsEqualTracesConjugateStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representations_equal_traces_conjugate : ∀ (I : Type) [Fintype I] [DecidableEq I] (m g : ℕ), 0 < m → ∀ (σ σ' : (I → Matrix (Fin m) (Fin m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ), (∀ τ, (σ (Pi.single τ 1)).trace = (σ' (Pi.single τ 1)).trace) → ∃ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h ∧ ∀ x, σ' x * h = h * σ x := by
  first | exact @GlobalTheory.conj_of_trace_central_idem_eq | exact GlobalTheory.conj_of_trace_central_idem_eq | (intros; apply GlobalTheory.conj_of_trace_central_idem_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomExtendsAlgHomOfSpanOfFinrankEq
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomExtendsAlgHomOfSpanOfFinrankEq
namespace GlobalTheory

theorem ringHom_extends_algHom_of_span_of_finrank_eq :
    ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (A : Type) [Ring A] [Algebra ℂ A]
      [FiniteDimensional ℂ A] (B : Type) [Ring B] [Algebra ℂ B] (φ : O →+* A) (ρ : O →+* B),
      Submodule.span ℂ (Set.range φ) = ⊤ → Module.finrank ℂ A = Module.finrank ℤ O →
      ∃ σ : A →ₐ[ℂ] B, ∀ x, σ (φ x) = ρ x := by
  intro O _ _ _ A _ _ _ B _ _ φ ρ hspan hdim
  classical
  let b := Module.Free.chooseBasis ℤ O
  let v : Module.Free.ChooseBasisIndex ℤ O → A := fun i => φ (b i)
  have hle : ⊤ ≤ Submodule.span ℂ (Set.range v) := by
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    have hx : x = ∑ i, b.repr x i • b i := (b.sum_repr x).symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ O) = Module.finrank ℂ A := by
    rw [hdim, Module.finrank_eq_card_chooseBasisIndex]
  let bA := basisOfTopLeSpanOfCardEqFinrank v hle hcard
  have hbA : ∀ i, bA i = φ (b i) := fun i => by
    simp only [bA, coe_basisOfTopLeSpanOfCardEqFinrank, v]
  let L : A →ₗ[ℂ] B := bA.constr ℂ (fun i => ρ (b i))
  have hLb : ∀ i, L (φ (b i)) = ρ (b i) := by
    intro i
    rw [← hbA]
    exact bA.constr_basis ℂ _ i
  have hLφ : ∀ x, L (φ x) = ρ x := by
    have h : (L.restrictScalars ℤ).comp φ.toAddMonoidHom.toIntLinearMap
        = ρ.toAddMonoidHom.toIntLinearMap := b.ext (fun i => hLb i)
    intro x
    exact LinearMap.congr_fun h x
  have hmul : ∀ u w : A, L (u * w) = L u * L w := by
    have h : (LinearMap.mul ℂ A).compr₂ L = (LinearMap.mul ℂ B).compl₁₂ L L := by
      refine bA.ext (fun i => bA.ext (fun j => ?_))
      simp only [LinearMap.compr₂_apply, LinearMap.compl₁₂_apply, LinearMap.mul_apply', hbA]
      rw [← map_mul, hLφ, hLφ, hLφ, map_mul]
    intro u w
    exact LinearMap.congr_fun₂ h u w
  have hone : L 1 = 1 := by
    rw [← map_one φ, hLφ, map_one]
  exact ⟨AlgHom.ofLinearMap L hone hmul, fun x => by
    simp only [AlgHom.ofLinearMap_apply]; exact hLφ x⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomExtendsAlgHomOfSpanOfFinrankEqStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algHom_extend_ringHom_of_span_eq_top_of_finrank_eq : ∀ (O : Type) [Ring O] [Module.Free ℤ O] [Module.Finite ℤ O] (A : Type) [Ring A] [Algebra ℂ A] [FiniteDimensional ℂ A] (B : Type) [Ring B] [Algebra ℂ B] (φ : O →+* A) (ρ : O →+* B), Submodule.span ℂ (Set.range φ) = ⊤ → Module.finrank ℂ A = Module.finrank ℤ O → ∃ σ : A →ₐ[ℂ] B, ∀ x, σ (φ x) = ρ x := by
  first | exact @GlobalTheory.ringHom_extends_algHom_of_span_of_finrank_eq | exact GlobalTheory.ringHom_extends_algHom_of_span_of_finrank_eq | (intros; apply GlobalTheory.ringHom_extends_algHom_of_span_of_finrank_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomConjOfTraceEqHarrisTaylorOrder
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem rep_conj_of_trace_eq : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : ℕ) (ρ ρ' : D.O →+* Matrix (Fin g) (Fin g) ℂ), (∀ c : 𝓞 D.F, (ρ (algebraMap (𝓞 D.F) D.O c)).trace = (ρ' (algebraMap (𝓞 D.F) D.O c)).trace) → ∃ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h ∧ ∀ a, ρ' a * h = h * ρ a := by
  classical
  intro p _ D g ρ ρ' htr
  obtain ⟨φ, hφ, hspan⟩ := GlobalTheory.T.exists_ringHom_order_pi_matrix_embeddings p D
  haveI := D.freeO
  haveI := D.finO
  have hdim : Module.finrank ℂ ((D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ) = Module.finrank ℤ D.O := by
    rw [Module.finrank_pi_fintype, D.rankO]
    simp [Module.finrank_matrix, NumberField.Embeddings.card]
    ring
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_algHom_extend_ringHom_of_span_eq_top_of_finrank_eq D.O _ _ φ ρ hspan hdim
  obtain ⟨σ', hσ'⟩ := GlobalTheory.T.exists_algHom_extend_ringHom_of_span_eq_top_of_finrank_eq D.O _ _ φ ρ' hspan hdim
  have key : ∀ (s : ((D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ) →ₐ[ℂ] Matrix (Fin g) (Fin g) ℂ) (f : (D.F →+* ℂ) → ℂ),
      (s (fun τ => Matrix.scalar (Fin D.m) (f τ))).trace = ∑ τ, f τ * (s (Pi.single τ 1)).trace := by
    intro s f
    have : (fun τ => Matrix.scalar (Fin D.m) (f τ)) = ∑ τ, f τ • (Pi.single τ 1 : (D.F →+* ℂ) → Matrix (Fin D.m) (Fin D.m) ℂ) := by
      ext τ i j
      simp only [Finset.sum_apply]
      rw [Finset.sum_eq_single τ]
      · simp [Pi.single_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]
      · intro b _ hb
        simp [Pi.single_apply, Ne.symm hb]
      · simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [this, map_sum, Matrix.trace_sum]
    simp [map_smul, Matrix.trace_smul]
  let χ : (D.F →+* ℂ) → (𝓞 D.F →* ℂ) := fun τ => (τ.comp (algebraMap (𝓞 D.F) D.F)).toMonoidHom
  have hχ : Function.Injective χ := by
    intro τ τ' h
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 D.F))
    ext x
    exact DFunLike.congr_fun h x
  have hlin := (linearIndependent_monoidHom (𝓞 D.F) ℂ).comp χ hχ
  rw [Fintype.linearIndependent_iff] at hlin
  have heq : ∀ τ, (σ (Pi.single τ 1)).trace = (σ' (Pi.single τ 1)).trace := by
    have := hlin (fun τ => (σ (Pi.single τ 1)).trace - (σ' (Pi.single τ 1)).trace) (by
      funext c
      have h1 := htr c
      have hφ' : φ (algebraMap (𝓞 D.F) D.O c) = fun τ => Matrix.scalar (Fin D.m) (τ (c : D.F)) := funext (hφ c)
      rw [← hσ, ← hσ', hφ', key, key] at h1
      simp only [Finset.sum_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul, Pi.zero_apply]
      simp only [χ, MonoidHom.coe_coe, RingHom.coe_comp, Function.comp_apply, sub_mul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      simpa [mul_comm] using h1)
    intro τ
    exact sub_eq_zero.mp (this τ)
  exact GlobalTheory.T.representations_equal_traces_conjugate (D.F →+* ℂ) D.m g D.m_pos σ σ' heq |>.imp fun h hh => ⟨hh.1, fun a => by rw [← hσ, ← hσ']; exact hh.2 _⟩

end GlobalTheory.UPel.HT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomConjOfTraceEqHarrisTaylorOrderStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_conj_of_trace_eq_harrisTaylorOrder : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (g : ℕ) (ρ ρ' : D.O →+* Matrix (Fin g) (Fin g) ℂ), (∀ c : 𝓞 D.F, (ρ (algebraMap (𝓞 D.F) D.O c)).trace = (ρ' (algebraMap (𝓞 D.F) D.O c)).trace) → ∃ h : Matrix (Fin g) (Fin g) ℂ, IsUnit h ∧ ∀ a, ρ' a * h = h * ρ a := by
  first | exact @GlobalTheory.UPel.HT.rep_conj_of_trace_eq | exact GlobalTheory.UPel.HT.rep_conj_of_trace_eq | (intros; apply GlobalTheory.UPel.HT.rep_conj_of_trace_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexUniformisationHarrisTaylor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Unif

theorem eta_points {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {g : ℕ} {y : Sp ℂ ⟶ S}
    {e : (Fin g → ℂ) → (Over.mk y ⟶ G)} {Λ' : Type} [AddCommGroup Λ'] {lv : Λ' → (𝟙_ (Over S) ⟶ G)} {N : ℕ}
    (hN : 0 < N) (hadd : ∀ z w, e (z + w) = e z * e w) (hsurj : Function.Surjective e)
    (hlv : ∀ x y, lv (x + y) = lv x * lv y) (hker : ∀ x, lv (N • x) = 1) (a : Λ') :
    ∃ z, e z = 1 ∧ toUnit _ ≫ lv a = e ((N : ℂ)⁻¹ • z) := by
  obtain ⟨w, hw⟩ := hsurj (toUnit _ ≫ lv a)
  have hepow : ∀ n : ℕ, e (n • w) = e w ^ n := by
    intro n
    induction n with
    | zero =>
      have h0 := hadd 0 0
      rw [add_zero] at h0
      simpa using (mul_eq_left.mp h0.symm)
    | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hlvpow : ∀ n : ℕ, lv (n • a) = lv a ^ n := by
    intro n
    induction n with
    | zero =>
      have h0 := hlv 0 0
      rw [add_zero] at h0
      simpa using (mul_eq_left.mp h0.symm)
    | succ n ih => rw [succ_nsmul, hlv, ih, pow_succ]
  refine ⟨N • w, ?_, ?_⟩
  · rw [hepow, hw, ← comp_pow, ← hlvpow, hker, comp_one]
  · have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [← hw, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hN', one_smul]

end GlobalTheory.UPel.HT.Unif

namespace GlobalTheory.UPel.HT.Unif

theorem unifAt_change {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ ρ₂ : O →+* Matrix (Fin g) (Fin g) ℂ} {R : Type}
    [CommRing R] {σ : R →+* ℂ} {Λ : Type} {F : Fam R O Λ g} {N : ℕ} {D' : PLat O bar} {t : Λ → D'.La}
    {P : D'.La →+ (Fin g → ℂ)} {y : Sp ℂ ⟶ F.X} {e : (Fin g → ℂ) → (Over.mk y ⟶ F.A)}
    (hU : UnifAt F σ ρ N D' t P y e) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ))
    (hc : ∀ a z, h (ρ a *ᵥ z) = ρ₂ a *ᵥ h z) :
    UnifAt F σ ρ₂ N D' t (h.toLinearMap.toAddMonoidHom.comp P) y (fun z => e (h.symm z)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hU
  have hc' : ∀ a z, h.symm (ρ₂ a *ᵥ z) = ρ a *ᵥ h.symm z := fun a z => by
    rw [LinearEquiv.symm_apply_eq, hc, LinearEquiv.apply_symm_apply]
  have hs : ∀ (k : ℂ) x, h.symm (k • h (P x)) = k • P x := fun k x => by simp
  refine ⟨h1, GlobalTheory.T.comp_linearEquiv_intertwining O bar D' g ρ ρ₂ P h h2 hc, ?_, ?_, ?_, ?_, ?_⟩
  · exact GlobalTheory.LocLift.IsExp.comp h3 (LinearEquiv.toContinuousLinearEquiv h.symm)
  · intro z
    rw [h4]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, by simp [hx]⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, by simp⟩
  · intro a z
    simp only [hc']
    exact h5 a _
  · intro k a b c hk hcc
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, hs]
    exact h6 k a b c hk hcc
  · intro a
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, LinearMap.toAddMonoidHom_coe, LinearEquiv.coe_coe, hs]
    exact h7 a

end GlobalTheory.UPel.HT.Unif

namespace GlobalTheory.UPel.HT.Unif

variable {p : ℕ} [Fact p.Prime]

theorem exists_unifAt_of_exp (D : Datum p) {R : Type} [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ)
    (o : Obj b N (spMap σ)) (h : SmoothOfRelativeDimension D.g o.A.hom)
    (hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB) (hN : 0 < N)
    (ρ' : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ o.A))
    (Λ : Submodule ℤ (Fin D.g → ℂ)) (he : IsExp (𝟙 _) e) (hd : DiscreteTopology Λ)
    (hs : Submodule.span ℝ (Λ : Set (Fin D.g → ℂ)) = ⊤) (hk : ∀ z, e z = 1 ↔ z ∈ Λ)
    (hρ : ∀ a z, e (ρ' a *ᵥ z) = e z ≫ o.act.act a) :
    ∃ (D' : PLat D.O D.inv) (t : D.La → D'.La) (Q : D'.La →+ (Fin D.g → ℂ)), UnifAt (o.fam h hL) σ ρ' N D' t Q (𝟙 _) e := by
  have hst : ∀ a z, z ∈ Λ → ρ' a *ᵥ z ∈ Λ := fun a z hz => by
    haveI := o.act.hom a
    rw [← hk, hρ, (hk z).2 hz]
    exact one_comp _
  let φ : D.O →+* Module.End ℤ Λ :=
    { toFun := fun a =>
        { toFun := fun x => ⟨ρ' a *ᵥ (x : Fin D.g → ℂ), hst a x x.2⟩
          map_add' := fun x y => Subtype.ext (by simp [Matrix.mulVec_add])
          map_smul' := fun n x => Subtype.ext (by
            show ρ' a *ᵥ (n • (x : Fin D.g → ℂ)) = n • (ρ' a *ᵥ (x : Fin D.g → ℂ))
            exact map_zsmul (Matrix.mulVecLin (ρ' a)) n (x : Fin D.g → ℂ)) }
      map_one' := by ext x i; simp
      map_mul' := fun a b => by ext x i; simp [Matrix.mulVec_mulVec]
      map_zero' := by ext x i; simp
      map_add' := fun a b => by ext x i; simp [Matrix.add_mulVec] }
  letI : Module D.O Λ := Module.compHom Λ φ
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  let Q : Λ →+ (Fin D.g → ℂ) := Λ.subtype.toAddMonoidHom
  have hQi : Function.Injective Q := Subtype.val_injective
  have hQk : ∀ z, e z = 1 ↔ z ∈ Q.range := fun z => by
    rw [hk]; simp [Q]
  have hQs : Submodule.span ℝ (Set.range Q) = ⊤ := by
    simpa [Q] using hs
  obtain ⟨Hm, EF, hH, hpos, him, hweil⟩ := GlobalTheory.T.exists_positiveRiemannForm_of_relAmple_exponential (Sp ℂ) o.A D.g o.ab h
    (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) hL o.ample (𝟙 _) e Λ Q he hQi hQk
  obtain ⟨halt, hnd⟩ := GlobalTheory.T.im_hermForm_alternating_nondegenerate_on_lattice Λ D.g Q Hm EF hQi hQs hH hpos him
  have hmv : ∀ (a : D.O) (k : ℂ) (z : Fin D.g → ℂ), k • (ρ' a *ᵥ z) = ρ' a *ᵥ (k • z) := fun a k z => by
    rw [Matrix.mulVec_smul]
  have hadj : ∀ (a : D.O) x y, EF (φ a x) y = EF x (φ (D.inv a) y) := by
    intro a
    have hu : ∀ (c : D.O) (k : ℕ) (x : Λ), 0 < k →
        e ((k : ℂ)⁻¹ • Q ((φ c).toAddMonoidHom x)) = e ((k : ℂ)⁻¹ • Q x) ≫ o.act.act c := fun c k x _ => by
      show e ((k : ℂ)⁻¹ • (ρ' c *ᵥ (x : Fin D.g → ℂ))) = _
      rw [hmv, hρ]
      rfl
    have key := GlobalTheory.T.rosati_adjoint_iff_biextension_pullbacks_isomorphic o.A D.g o.ab h o.P o.isLB o.rig₁ o.rig₂ o.symm o.ample e Λ Q EF he hQi hQk hweil
      (o.act.act a) (o.act.act (D.star a).unop) (φ a).toAddMonoidHom (φ (D.inv a)).toAddMonoidHom (o.act.hom a)
      (o.act.hom _) (hu a) (hu (D.inv a))
    exact key.1 (o.rosati a)
  have het : ∀ a : D.La, ∃ z, e z = 1 ∧ toUnit _ ≫ o.eta a = e ((N : ℂ)⁻¹ • z) :=
    eta_points hN he.1 he.2.1 o.eta_add o.eta_ker
  choose tz htz using het
  let D' : PLat D.O D.inv :=
    { La := Λ
      fin := ZLattice.module_finite ℝ Λ
      free := ZLattice.module_free ℝ Λ
      EF := EF
      alt := halt
      nondeg := hnd
      adj := fun a x y => hadj a x y }
  refine ⟨D', fun a => (⟨tz a, (hk _).1 (htz a).1⟩ : Λ), Q, Category.id_comp _,
    ⟨fun a x => rfl, hQi, ?_, hQs, Hm, hH, hpos, him⟩, he, hQk, hρ, hweil, fun a => (htz a).2⟩
  have : Q.range = Λ.toAddSubgroup := by ext; simp [Q]
  rw [this]
  exact hd

end GlobalTheory.UPel.HT.Unif

namespace GlobalTheory.UPel.HT.Unif

theorem exists_unifAt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL, 0 < N → N.Coprime p → b.IsType σ ρ → ∃ D' t Q e, D.Cls N D' t ∧ UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e := by
  intro p _ D R _ b N σ ρ o h hL hN hNp hty
  obtain ⟨e₀, Λ, hexp, hdisc, hspan, hker⟩ := GlobalTheory.T.exists_complexFibreExponential_full_lattice (Sp ℂ) o.A D.g o.ab h (𝟙 _)
  obtain ⟨ρ', hρ'⟩ := GlobalTheory.T.exists_ringHom_matrix_lift_of_orderAction_exponential (Sp ℂ) o.A D.g D.O o.act.act o.ab h o.act.hom o.act.one o.act.mul o.act.add (𝟙 _) e₀ hexp
  obtain ⟨D', t, Q, hU⟩ := exists_unifAt_of_exp D b N σ o h hL hN ρ' e₀ Λ hexp hdisc hspan hker hρ'
  have hty' := GlobalTheory.T.lieCondition_uniformisingSpace_isType p D R b N σ ρ' o h hL D' t Q e₀ hU
  obtain ⟨M, hMu, hM⟩ := GlobalTheory.T.ringHom_conj_of_trace_eq_harrisTaylorOrder p D D.g ρ ρ' (fun c => by rw [hty c, hty' c])
  set u := hMu.unit with hu
  have hM' : ∀ a, ρ' a * (u : Matrix (Fin D.g) (Fin D.g) ℂ) = u * ρ a := fun a => by
    rw [hu, IsUnit.unit_spec]; exact hM a
  let Mi : Matrix (Fin D.g) (Fin D.g) ℂ := ((u⁻¹ : (Matrix (Fin D.g) (Fin D.g) ℂ)ˣ) : Matrix (Fin D.g) (Fin D.g) ℂ)
  have hinv : ∀ a, Mi * ρ' a = ρ a * Mi := fun a => by
    calc Mi * ρ' a = Mi * ρ' a * ((u : Matrix (Fin D.g) (Fin D.g) ℂ) * Mi) := by
          rw [Units.mul_inv, _root_.mul_one]
      _ = Mi * (ρ' a * u) * Mi := by simp only [_root_.mul_assoc]
      _ = Mi * (u * ρ a) * Mi := by rw [hM']
      _ = ρ a * Mi := by rw [← _root_.mul_assoc Mi, Units.inv_mul, _root_.one_mul]
  let hl : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ) := Matrix.toLinearEquiv' Mi (Units.invertible u⁻¹)
  have hc : ∀ a z, hl (ρ' a *ᵥ z) = ρ a *ᵥ hl z := fun a z => by
    show Mi *ᵥ (ρ' a *ᵥ z) = ρ a *ᵥ (Mi *ᵥ z)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hinv]
  have hU2 := unifAt_change hU hl hc
  obtain ⟨t', hcls, ht'⟩ := GlobalTheory.T.uniformised_complex_fibre_marked_lattice_class p D R b N σ ρ o h hL D' t _ _ hN hNp hU2
  have hmk : IsMarkedIsom N D' D' t t' (LinearEquiv.refl D.O D'.La) := by
    refine ⟨fun x y => rfl, fun a => ?_⟩
    obtain ⟨x, hx⟩ := ht' a
    exact ⟨-x, by rw [hx]; simp⟩
  exact ⟨D', t', _, _, hcls, GlobalTheory.T.uniformisationAt_transport_isometry D.O D.inv D.g ρ R σ D.La (o.fam h hL) N D' D' t t' _ _ (𝟙 _) _
    (LinearEquiv.refl D.O D'.La) (LinearEquiv.refl ℂ (Fin D.g → ℂ)) hN hU2 hmk (fun x => rfl) hU2.2.1⟩

end GlobalTheory.UPel.HT.Unif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplexUniformisationHarrisTaylorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complexUniformisation_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o : Obj b N (spMap σ)) h hL, 0 < N → N.Coprime p → b.IsType σ ρ → ∃ D' t Q e, D.Cls N D' t ∧ UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e := by
  first | (exact @GlobalTheory.UPel.HT.Unif.exists_unifAt) | (exact GlobalTheory.UPel.HT.Unif.exists_unifAt) | (intros; apply GlobalTheory.UPel.HT.Unif.exists_unifAt <;> assumption)
end
