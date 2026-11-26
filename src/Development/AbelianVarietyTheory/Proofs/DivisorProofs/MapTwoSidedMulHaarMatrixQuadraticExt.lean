module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveRootPowUnitSubProdProperties
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMeasUnivNeTopOfCompact
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
public import GroundTheory.AutomorphicForms.DixmierMalliavin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechLevelRepresentable
public import Formalism.UnipotentAdelicQuotients.EllRegCheck
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsExtAndGlue
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallySurjectiveEtaleSectionBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeAleph0SmoothIrreducibleUnitaryAdelic

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapTwoSidedMulHaarMatrixQuadraticExt
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetRestrictScalarsTwoSidedMatrixMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetRestrictScalarsTwoSidedMatrixMul
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

noncomputable section

namespace GlobalTheory.KSp

def twoSidedMulLin {E : Type} [Field E] {α ν : Type} [Fintype α] [Fintype ν]
    (u : Matrix α α E) (a : Matrix ν ν E) : Matrix α ν E →ₗ[E] Matrix α ν E where
  toFun x := u * x * a
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c x := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl

theorem det_twoSidedMulLin {E : Type} [Field E] {α ν : Type} [Fintype α] [DecidableEq α]
    [Fintype ν] [DecidableEq ν] (u : Matrix α α E) (a : Matrix ν ν E) :
    LinearMap.det (twoSidedMulLin u a) = u.det ^ Fintype.card ν * a.det ^ Fintype.card α := by
  let e : (α × ν → E) ≃ₗ[E] Matrix α ν E := LinearEquiv.curry E E α ν
  have h : twoSidedMulLin u a =
      (e : _ →ₗ[E] _) ∘ₗ (Matrix.toLin' (Matrix.kroneckerMap (· * ·) u a.transpose)) ∘ₗ
        (e.symm : _ →ₗ[E] _) := by
    refine LinearMap.ext fun z => ?_
    funext i j
    change (u * z * a) i j = (Matrix.kroneckerMap (· * ·) u a.transpose).mulVec (Function.uncurry z) (i, j)
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
      Matrix.transpose_apply, Function.uncurry_apply_pair, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [show Function.uncurry z (b, c) = z b c from rfl]
    ring
  rw [h, LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_kronecker, Matrix.det_transpose]

theorem det_restrictScalars_twoSidedMul : ∀ (F : Type) [Field F] (E : Type) [Field E] [Algebra F E]
    [FiniteDimensional F E] (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν]
    [DecidableEq ν] (u : Matrix α α E) (a : Matrix ν ν E) (T : Matrix α ν E →ₗ[F] Matrix α ν E),
    (∀ x, T x = u * x * a) →
      LinearMap.det T = Algebra.norm F u.det ^ Fintype.card ν * Algebra.norm F a.det ^ Fintype.card α := by
  intro F _ E _ _ _ α _ _ ν _ _ u a T hT
  have hT' : T = (twoSidedMulLin u a).restrictScalars F := by
    refine LinearMap.ext fun x => ?_
    rw [hT]; rfl
  rw [hT', LinearMap.det_restrictScalars, det_twoSidedMulLin, map_mul, map_pow, map_pow]

end GlobalTheory.KSp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetRestrictScalarsTwoSidedMatrixMulStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_restrictScalars_twoSidedMatrixMul : ∀ (F : Type) [Field F] (E : Type) [Field E] [Algebra F E] [FiniteDimensional F E] (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (u : Matrix α α E) (a : Matrix ν ν E) (T : Matrix α ν E →ₗ[F] Matrix α ν E), (∀ x, T x = u * x * a) → LinearMap.det T = Algebra.norm F u.det ^ Fintype.card ν * Algebra.norm F a.det ^ Fintype.card α := by
  first | exact @GlobalTheory.KSp.det_restrictScalars_twoSidedMul | exact GlobalTheory.KSp.det_restrictScalars_twoSidedMul | (intros; apply GlobalTheory.KSp.det_restrictScalars_twoSidedMul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapTwoSidedMulHaarMatrixQuadraticExt
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

noncomputable def twoSidedEquiv (F : Type) [Field F] (E : Type) [Field E] [Algebra F E]
    {α : Type} [Fintype α] [DecidableEq α] {ν : Type} [Fintype ν] [DecidableEq ν]
    (u : GL α E) (a : GL ν E) : Matrix α ν E ≃ₗ[F] Matrix α ν E where
  toFun x := (u : Matrix α α E) * x * (a : Matrix ν ν E)
  invFun x := ((u⁻¹ : GL α E) : Matrix α α E) * x * ((a⁻¹ : GL ν E) : Matrix ν ν E)
  map_add' x y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' r x := by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl
  left_inv x := by
    show ((u⁻¹ : GL α E) : Matrix α α E) * ((u : Matrix α α E) * x * (a : Matrix ν ν E)) * ((a⁻¹ : GL ν E) : Matrix ν ν E) = x
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  right_inv x := by
    show (u : Matrix α α E) * (((u⁻¹ : GL α E) : Matrix α α E) * x * ((a⁻¹ : GL ν E) : Matrix ν ν E)) * (a : Matrix ν ν E) = x
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Units.inv_mul, Matrix.mul_one, ← Matrix.mul_assoc,
      Units.mul_inv, Matrix.one_mul]

theorem map_twoSided_haar : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (u : GL α E) (a : GL ν E), μ.map (fun x => (u : Matrix α α E) * x * (a : Matrix ν ν E)) = (distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det u)) ^ Fintype.card ν * distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det a)) ^ Fintype.card α)⁻¹ • μ := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ _ _ μ _ u a
  obtain ⟨hfd, -, -, -, -, -, -, hmat⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  have := hfd
  have := (hmat α ν).1
  let T := twoSidedEquiv F E u a

  have hdet : LinearEquiv.det T =
      (Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det u) ^ Fintype.card ν *
        (Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det a) ^
          Fintype.card α := by
    ext
    rw [LinearEquiv.coe_det, GlobalTheory.T.det_restrictScalars_twoSidedMatrixMul F E α ν (u : Matrix α α E) (a : Matrix ν ν E)
      (T : Matrix α ν E →ₗ[F] Matrix α ν E) (fun x ↦ rfl)]
    simp
  have hT : (fun x ↦ (u : Matrix α α E) * x * (a : Matrix ν ν E)) = ⇑T := rfl
  rw [hT, GlobalTheory.T.map_linearEquiv_addHaar_localField F (Matrix α ν E) μ T, hdet, map_mul, map_pow, map_pow]

end GlobalTheory.KSp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapTwoSidedMulHaarMatrixQuadraticExtStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_twoSided_mul_haar_matrix_quadraticExt : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] [MeasurableSpace (Matrix α ν E)] [BorelSpace (Matrix α ν E)] (μ : Measure (Matrix α ν E)) [μ.IsAddHaarMeasure] (u : GL α E) (a : GL ν E), μ.map (fun x => (u : Matrix α α E) * x * (a : Matrix ν ν E)) = (distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det u)) ^ Fintype.card ν * distribHaarChar F ((Units.map (Algebra.norm F : E →* F)) (Matrix.GeneralLinearGroup.det a)) ^ Fintype.card α)⁻¹ • μ := by
  first | exact @GlobalTheory.KSp.map_twoSided_haar | exact GlobalTheory.KSp.map_twoSided_haar | (intros; apply GlobalTheory.KSp.map_twoSided_haar <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrPreservesHomology
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex

namespace GlobalTheory.EtC

section
variable {R S : Type} [CommRing R] [CommRing S]

instance restr_additive (φ : R →+* S) : (restr φ).Additive where
  map_add {F G} {f g} := by
    apply Sheaf.hom_ext
    ext U x
    rfl

abbrev rcx (φ : R →+* S) : Cx S ⥤ Cx R := (restr φ).mapHomologicalComplex _

def rAug (φ : R →+* S) {F : Shv S} {C : Cx S} (ε : sgl F ⟶ C) : sgl ((restr φ).obj F) ⟶ (rcx φ).obj C :=
  (HomologicalComplex.singleMapHomologicalComplex (restr φ) (ComplexShape.up ℤ) 0).inv.app F ≫ (rcx φ).map ε

def idSemi (φ : R →+* S) (K : Cx S) : SemiMap K ((rcx φ).obj K) where
  app _ _ := { toFun := fun a => a, map_zero' := rfl, map_add' := fun _ _ => rfl }
  nat _ _ _ := rfl
  comm _ _ _ _ := rfl

end

section
variable {S R : Type} [CommRing S] [CommRing R]

def SemiMap.sub {I : Cx S} {J : Cx R} (ρ ρ' : SemiMap I J) : SemiMap I J where
  app U s := ρ.app U s - ρ'.app U s
  nat g s a := by simp [map_sub, ρ.nat, ρ'.nat]
  comm U s t a := by simp [map_sub, ρ.comm, ρ'.comm]

end

section
variable {S R : Type} [CommRing S] [CommRing R]

theorem ulift_intCast_smul {T : Type} [CommRing T] (M : ModuleCat.{1} (ULift.{1} T)) (x : M) (k : ℤ) :
    (ULift.up (k : T) : ULift.{1} T) • x = k • x := by
  rw [show (ULift.up (k : T) : ULift.{1} T) = ((k : ULift.{1} T)) from rfl]
  exact Int.cast_smul_eq_zsmul _ k x

def SemiMap.toZl {I : Cx S} {J : Cx R} (ρ : SemiMap I J) (s : ℤ) (U : Scheme.{0}ᵒᵖ) :
    ((restr (Int.castRingHom S)).obj (I.X s)).obj.obj U ⟶ ((restr (Int.castRingHom R)).obj (J.X s)).obj.obj U :=
  ModuleCat.ofHom (X := ((restr (Int.castRingHom S)).obj (I.X s)).obj.obj U)
      (Y := ((restr (Int.castRingHom R)).obj (J.X s)).obj.obj U)
    { toFun := ρ.app U.unop s
      map_add' := map_add _
      map_smul' := fun r a => by
        have h1 : ∀ b : Sec (I.X s) U.unop, (ULift.up ((r.down : ℤ) : S) : ULift.{1} S) • b = r.down • b :=
          fun b => ulift_intCast_smul _ b _
        have h2 : ∀ b : Sec (J.X s) U.unop, (ULift.up ((r.down : ℤ) : R) : ULift.{1} R) • b = r.down • b :=
          fun b => ulift_intCast_smul _ b _
        exact (congrArg (ρ.app U.unop s) (h1 a)).trans ((map_zsmul _ _ _).trans (h2 _).symm) }

def SemiMap.toZs {I : Cx S} {J : Cx R} (ρ : SemiMap I J) (s : ℤ) :
    (restr (Int.castRingHom S)).obj (I.X s) ⟶ (restr (Int.castRingHom R)).obj (J.X s) :=
  ⟨{ app := ρ.toZl s
     naturality := fun U V g => by
       ext a
       change ρ.app V.unop s (Sec.res g.unop a) = Sec.res g.unop (ρ.app U.unop s a)
       exact (ρ.nat g.unop s a).symm }⟩

def SemiMap.toZ {I : Cx S} {J : Cx R} (ρ : SemiMap I J) :
    (rcx (Int.castRingHom S)).obj I ⟶ (rcx (Int.castRingHom R)).obj J where
  f s := ρ.toZs s
  comm' s t _ := by
    apply Sheaf.hom_ext
    ext U a
    change Sec.map (J.d s t) (ρ.app U.unop s a) = ρ.app U.unop t (Sec.map (I.d s t) a)
    exact ρ.comm U.unop s t a

end

section
variable {R S : Type} [CommRing R] [CommRing S]

theorem restr_eq (φ : R →+* S) : restr φ = sheafCompose _ (ModuleCat.restrictScalars.{1} (liftHom φ)) := rfl

theorem restr_exact (φ : R →+* S) : PreservesFiniteLimits (restr φ) ∧ PreservesFiniteColimits (restr φ) := by
  rw [restr_eq]
  have adj₁ := Sheaf.adjunction Scheme.etaleTopology.{0} (ModuleCat.extendRestrictScalarsAdj.{1, 1, 1} (liftHom φ))
  have adj₂ := Sheaf.adjunction Scheme.etaleTopology.{0} (ModuleCat.restrictCoextendScalarsAdj.{1, 1, 1} (liftHom φ))
  have := adj₁.isRightAdjoint
  have := adj₂.isLeftAdjoint
  let j : sheafCompose Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} (liftHom φ)) ≅
      Sheaf.composeAndSheafify Scheme.etaleTopology.{0} (ModuleCat.restrictScalars.{1} (liftHom φ)) :=
    (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ (sheafificationNatIso _ _)
  exact ⟨inferInstance, preservesFiniteColimits_of_natIso j.symm⟩

instance restr_preservesHomology (φ : R →+* S) : (restr φ).PreservesHomology := by
  obtain ⟨_, _⟩ := restr_exact φ
  infer_instance

theorem rAug_quasiIso (φ : R →+* S) {F : Shv S} {C : Cx S} (ε : sgl F ⟶ C) [QuasiIso ε] : QuasiIso (rAug φ ε) := by
  unfold rAug
  have h1 : QuasiIso ((rcx φ).map ε) := HomologicalComplex.quasiIso_map_of_preservesHomology ε (restr φ)
  have h2 : QuasiIso ((HomologicalComplex.singleMapHomologicalComplex (restr φ) (ComplexShape.up ℤ) 0).inv.app F) :=
    quasiIso_of_isIso _
  exact quasiIso_comp (hφ := h2) (hφ' := h1) _ _

end

section
variable {R S : Type} [CommRing R] [CommRing S]

theorem rAug_f_zero (φ : R →+* S) {F : Shv S} {C : Cx S} (ε : sgl F ⟶ C) (U : Scheme.{0}) (a : Sec F U) :
    Sec.map ((rAug φ ε).f 0) (Sec.map (sglι ((restr φ).obj F)) (show Sec ((restr φ).obj F) U from a)) =
      (show Sec ((restr φ).obj (C.X 0)) U from Sec.map (ε.f 0) (Sec.map (sglι F) a)) := by
  have h : sglι ((restr φ).obj F) ≫ (rAug φ ε).f 0 = (restr φ).map (sglι F ≫ ε.f 0) := by
    set_option backward.isDefEq.respectTransparency false in
    simp [rAug, sglι]
  have := congrArg (fun m => Sec.map m (show Sec ((restr φ).obj F) U from a)) h
  exact this

end

end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralModularFamilyValueDivPeriodPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmPowTwelveDivDiscriminantMemSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmPowTwelveDivDiscriminantMemSubring
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)

namespace GlobalTheory.QFam

theorem esymm_pow_twelve_div_mem : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ)
    (f : ι → ℍ → ℂ) (R : Subring ℂ) (τ₀ : ℍ), 0 < N → ActBij act → IsFam act w f →
    (∀ i, QAll (· ∈ R) N (f i)) → jT τ₀ ∈ R → ∀ k : ℕ,
    (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ₀ ^ 12 / DD τ₀ ^ w) ∈ R := by
  intro ι _ act w N f R τ₀ hN hact hf hq hj k
  have hF : IsFam act ((12 : ℕ) * (w : ℤ)) fun i τ => f i τ ^ 12 :=
    (GlobalTheory.T.isSLTwoPermutedModularFamily_algebra_closure ι act).2.2.2.2.1 w f 12 hf
  obtain ⟨-, -, -, -, hpow, hsp⟩ := GlobalTheory.T.qExpansionCoeffsInSubring_ring_closed R N hN
  have hqS : QAll (· ∈ R) N fun τ =>
      ∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ ^ 12 :=
    (hsp (Finset ι) (Finset.powersetCard k Finset.univ) (fun t τ => ∏ i ∈ t, f i τ ^ 12)
      fun t _ => (hsp ι t (fun i τ => f i τ ^ 12) fun i _ => hpow (f i) 12 (hq i)).2).1
  have hw : ((k : ℤ) * (((12 : ℕ) : ℤ) * (w : ℤ))) = 12 * ((k * w : ℕ) : ℤ) := by
    push_cast; ring
  obtain ⟨P, hP, hPe⟩ := GlobalTheory.T.exists_eq_discriminant_pow_mul_eval_jInvariant R N (k * w) _ hN (fun γ => by
    have h := (GlobalTheory.T.permutedModularFamily_sum_esymm_slash_invariant ι act _ _ hact hF γ).2 k
    rw [hw] at h
    exact h) hqS
  have hD : DD τ₀ ^ (k * w) ≠ 0 := pow_ne_zero _ (ReciprocityTheory.ChartRestriction.L1.DD_ne_zero τ₀)
  have hsum : (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ₀ ^ 12 / DD τ₀ ^ w) =
      (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ₀ ^ 12) / DD τ₀ ^ (k * w) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.prod_div_distrib, Finset.prod_const, (Finset.mem_powersetCard.mp ht).2, ← pow_mul,
      mul_comm w k]
  have h0 := hPe τ₀
  rw [hsum, h0, mul_div_cancel_left₀ _ hD, Polynomial.eval_eq_sum_range]
  exact R.sum_mem fun i _ => R.mul_mem (hP i) (R.pow_mem hj i)

end GlobalTheory.QFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmPowTwelveDivDiscriminantMemSubringStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.esymm_pow_twelve_div_discriminant_mem_subring : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ) (f : ι → ℍ → ℂ) (R : Subring ℂ) (τ₀ : ℍ), 0 < N → ActBij act → IsFam act w f → (∀ i, QAll (· ∈ R) N (f i)) → jT τ₀ ∈ R → ∀ k : ℕ, (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, f i τ₀ ^ 12 / DD τ₀ ^ w) ∈ R := by
  first | exact @GlobalTheory.QFam.esymm_pow_twelve_div_mem | exact GlobalTheory.QFam.esymm_pow_twelve_div_mem | (intros; apply GlobalTheory.QFam.esymm_pow_twelve_div_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfEsymmMemSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfEsymmMemSubring
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open Polynomial

namespace GlobalTheory.QFam

theorem isIntegral_of_esymm_mem (ι : Type) [Fintype ι] (R : Subring ℂ) (x : ι → ℂ)
    (h : ∀ k : ℕ, (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, x i) ∈ R) (i : ι) :
    IsIntegral R (x i) := by
  classical
  set Q : ℂ[X] := ∏ j, (X + C (x j)) with hQ
  have hmon : Q.Monic := monic_prod_of_monic _ _ (fun j _ => monic_X_add_C (x j))
  have hdeg : Q.natDegree = (Finset.univ : Finset ι).card := by
    rw [hQ, natDegree_prod_of_monic _ _ (fun j _ => monic_X_add_C (x j))]
    simp
  have hl : Q ∈ Polynomial.lifts (algebraMap R ℂ) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases hn : n ≤ (Finset.univ : Finset ι).card
    · rw [hQ, Finset.prod_X_add_C_coeff _ _ hn]
      exact ⟨⟨_, h _⟩, rfl⟩
    · rw [coeff_eq_zero_of_natDegree_lt (by omega)]
      exact ⟨0, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hmon
  have hneg : IsIntegral R (-x i) := by
    refine ⟨q, hqm, ?_⟩
    rw [← Polynomial.eval_map, hq, hQ, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  simpa using hneg.neg

end GlobalTheory.QFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfEsymmMemSubringStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_of_esymm_mem_subring : ∀ (ι : Type) [Fintype ι] (R : Subring ℂ) (x : ι → ℂ), (∀ k : ℕ, (∑ t ∈ Finset.powersetCard k Finset.univ, ∏ i ∈ t, x i) ∈ R) → ∀ i, IsIntegral R (x i) := by
  first | exact @GlobalTheory.QFam.isIntegral_of_esymm_mem | exact GlobalTheory.QFam.isIntegral_of_esymm_mem | (intros; apply GlobalTheory.QFam.isIntegral_of_esymm_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralModularFamilyValueDivPeriodPow
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)

namespace GlobalTheory.QFam

theorem isIntegral_value_div (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ)
    (f : ι → ℍ → ℂ) (R : Subring ℂ) (τ₀ : ℍ) (Ω : ℂ) (hN : 0 < N) (hact : ActBij act)
    (hf : IsFam act w f) (hq : ∀ i, QAll (· ∈ R) N (f i)) (hj : IsIntegral R (jT τ₀))
    (hΩ : Ω ^ 12 = DD τ₀) (i : ι) : IsIntegral R (f i τ₀ / Ω ^ w) := by
  have hq' : ∀ i, QAll (· ∈ (integralClosure R ℂ).toSubring) N (f i) := fun i => by
    obtain ⟨a, ha, haR⟩ := hq i
    exact ⟨a, ha, fun n => (integralClosure R ℂ).algebraMap_mem ⟨a n, haR n⟩⟩
  have hs := GlobalTheory.T.esymm_pow_twelve_div_discriminant_mem_subring ι act w N f (integralClosure R ℂ).toSubring τ₀ hN hact hf hq' hj
  have h1 : IsIntegral (integralClosure R ℂ) (f i τ₀ ^ 12 / DD τ₀ ^ w) :=
    GlobalTheory.T.isIntegral_of_esymm_mem_subring ι (integralClosure R ℂ).toSubring (fun i => f i τ₀ ^ 12 / DD τ₀ ^ w) hs i
  have h2 : IsIntegral R (f i τ₀ ^ 12 / DD τ₀ ^ w) := isIntegral_trans _ h1
  have h3 : (f i τ₀ / Ω ^ w) ^ 12 = f i τ₀ ^ 12 / DD τ₀ ^ w := by
    rw [div_pow, ← hΩ, ← pow_mul, ← pow_mul, mul_comm]
  exact IsIntegral.of_pow (n := 12) (by norm_num) (h3 ▸ h2)

end GlobalTheory.QFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralModularFamilyValueDivPeriodPowStatement
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIntegral_modularFamily_value_div_period_pow : ∀ (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ) (f : ι → ℍ → ℂ) (R : Subring ℂ) (τ₀ : ℍ) (Ω : ℂ), 0 < N → ActBij act → IsFam act w f → (∀ i, QAll (· ∈ R) N (f i)) → IsIntegral R (jT τ₀) → Ω ^ 12 = DD τ₀ → ∀ i, IsIntegral R (f i τ₀ / Ω ^ w) := by
  first | exact @GlobalTheory.QFam.isIntegral_value_div | exact GlobalTheory.QFam.isIntegral_value_div | (intros; apply GlobalTheory.QFam.isIntegral_value_div <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftTranslateBoundedDerivFunctional
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftTranslateBoundedDerivFunctional
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem SmFn.continuous_leftTranslate : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ l, ∀ f ∈ S, Continuous fun x : G => Λ l fun y => f (x * y) := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ hμ S hS hL K hK Λ hΛ l f hf
  letI := h.chartedSpace
  haveI : LocallyCompactSpace G := ChartedSpace.locallyCompactSpace 𝔤 G
  haveI : SecondCountableTopology 𝔸ˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology G := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨C, hC⟩ := hΛ.bdd l
  rw [continuous_iff_continuousAt]
  intro x₀
  have hfc := hS f hf
  have hcont : Continuous fun x : G => ∫ y in K, ‖f (x * y) - f (x₀ * y)‖ ∂μ :=
    continuous_parametric_integral_of_continuous
      (f := fun x y : G => ‖f (x * y) - f (x₀ * y)‖)
      (((hfc.comp (continuous_fst.mul continuous_snd)).sub
        (hfc.comp (continuous_const.mul continuous_snd))).norm) hK
  have h0 : Filter.Tendsto (fun x : G => C * ∫ y in K, ‖f (x * y) - f (x₀ * y)‖ ∂μ) (nhds x₀) (nhds 0) := by
    have := (hcont.const_mul C).tendsto x₀
    simpa using this
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ => norm_nonneg _) (fun x => ?_) h0
  have h1 := hΛ.lin l _ (hL f hf x₀) _ (hL f hf x) (-1)
  have h2 := hC _ (S.add_mem (S.smul_mem (-1 : ℂ) (hL f hf x₀)) (hL f hf x))
  rw [h1] at h2
  simpa [neg_add_eq_sub] using h2

end GlobalTheory.HCA
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousLeftTranslateBoundedDerivFunctionalStatement
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_leftTranslate_boundedDerivFunctional : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ l, ∀ f ∈ S, Continuous fun x : G => Λ l fun y => f (x * y) := by
  first | exact @GlobalTheory.HCA.SmFn.continuous_leftTranslate | exact GlobalTheory.HCA.SmFn.continuous_leftTranslate | (intros; apply GlobalTheory.HCA.SmFn.continuous_leftTranslate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleModuleSheafSectionsCoprodBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleModuleSheafSectionsCoprodBijective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem sec_res_comp' {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (f : W ⟶ V) (g : V ⟶ U) (x : Sec F U) :
    Sec.res (f ≫ g) x = Sec.res f (Sec.res g x) := by
  simp [Sec.res, op_comp, Functor.map_comp]

theorem sec_res_id' {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (x : Sec F U) :
    Sec.res (𝟙 U) x = x := by
  simp [Sec.res]

theorem sec_coprod : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U j) → Function.Bijective (fun (x : Sec F U) (i : ι) => Sec.res (j i) x) := by
  intro R _ F U ι V j hU
  let e : ∐ V ≅ U := (coproductIsCoproduct V).coconePointUniqueUpToIso hU
  have he : ∀ i, Sigma.ι V i ≫ e.hom = j i := fun i =>
    (coproductIsCoproduct V).comp_coconePointUniqueUpToIso_hom hU ⟨i⟩
  have hb := GlobalTheory.T.sec_sigma_res_bijective R F V
  have hiso : Function.Bijective (fun x : Sec F U => Sec.res e.hom x) := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun y => Sec.res e.inv y, fun x => ?_, fun y => ?_⟩
    · simp only
      rw [← sec_res_comp', e.inv_hom_id, sec_res_id']
    · simp only
      rw [← sec_res_comp', e.hom_inv_id, sec_res_id']
  have hfun : (fun (x : Sec F U) (i : ι) => Sec.res (j i) x) =
      (fun (a : Sec F (∐ V)) (i : ι) => Sec.res (Sigma.ι V i) a) ∘ (fun x : Sec F U => Sec.res e.hom x) := by
    funext x i
    simp only [Function.comp_apply]
    rw [← sec_res_comp', he i]
  rw [hfun]
  exact hb.comp hiso

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleModuleSheafSectionsCoprodBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleModuleSheaf_sections_coprod_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U j) → Function.Bijective (fun (x : Sec F U) (i : ι) => Sec.res (j i) x) := by
  first | (exact @GlobalTheory.EtC.sec_coprod) | (exact GlobalTheory.EtC.sec_coprod) | (intros; apply GlobalTheory.EtC.sec_coprod  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainCoboundaryOfClassZeroStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simplicialCochain_coboundary_of_class_zero :
    ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc)
      (s : (free R).obj (E.obj (op ⦋1⦌)) ⟶ F),
      IsCls (R := R) s (0 : H R E F ((1 : ℕ) : ℤ)) →
        ∃ t : (free R).obj (E.obj (op ⦋0⦌)) ⟶ F, s = cobd (R := R) (E := E) (n := 0) t := by
  intro R _ F E s hs
  obtain ⟨-, hneg, hmono, ⟨w, hex⟩, -, hpos⟩ := GlobalTheory.T.chosenInjectiveResolutionEtaleSheaf_basic_properties R F
  obtain ⟨z, hz0, hz⟩ := hs
  rw [CohomologyClass.mk_eq_zero_iff] at hz0
  obtain ⟨m, hm, β, hβ⟩ := hz0
  obtain rfl : m = 0 := by push_cast at hm; omega
  have hzv : ∀ (p q : ℤ) (hpq : p + ((1 : ℕ) : ℤ) = q),
      (↑z : Cochain ((chains R).obj E) (res R F) ((1 : ℕ) : ℤ)).v p q hpq =
        (Cochain.single (p := -((1 : ℕ) : ℤ)) (q := 0)
          ((chainsXIso R E 1).hom ≫ s ≫ resι R F) ((1 : ℕ) : ℤ)).v p q hpq := by
    intro p q hpq
    rw [show (↑z : Cochain ((chains R).obj E) (res R F) ((1 : ℕ) : ℤ)) = z.1 from rfl, hz]
  let b := β.v 0 0 (by omega)
  have hb : b ≫ (res R F).d 0 1 = 0 := by
    have e := Cochain.congr_v hβ 0 1 (by norm_num)
    rw [δ_v 0 _ (by norm_num) β 0 1 _ 0 1 (by omega) rfl,
      (hpos E 1 (by norm_num)).eq_of_tgt (((chains R).obj E).d 0 1) 0, zero_comp, smul_zero, add_zero, hzv,
      Cochain.single_v_eq_zero _ _ _ _ _ (by omega)] at e
    exact e
  have : Mono (ShortComplex.mk _ _ w).f := hmono
  let t' : ((chains R).obj E).X 0 ⟶ F := hex.lift b hb
  have ht' : t' ≫ resι R F = b := hex.lift_f b hb
  have e := Cochain.congr_v hβ (-((1 : ℕ) : ℤ)) 0 (by omega)
  have h1 : β.v (-((1 : ℕ) : ℤ)) (-1) (by omega) = 0 := (hneg (-1) (by norm_num)).eq_of_tgt _ _
  rw [δ_v 0 _ (by norm_num) β _ 0 _ (-1) 0 (by omega) (by norm_num), h1,
    zero_comp, zero_add, hzv, Cochain.single_v] at e
  rw [show β.v 0 0 (by omega) = b from rfl, ← ht'] at e
  let D : (free R).obj (E.obj (op ⦋1⦌)) ⟶ (free R).obj (E.obj (op ⦋0⦌)) :=
    ∑ i : Fin 2, (-1 : ℤ) ^ (i : ℕ) • (free R).map (SimplicialObject.δ E i)
  have hd : ((chains R).obj E).d (-((1 : ℕ) : ℤ)) 0 = (chainsXIso R E 1).hom ≫ D ≫ (chainsXIso R E 0).inv :=
    GlobalTheory.EtC.ClsBasic.chains_d (R := R) E 0
  rw [hd] at e
  have hs_eq : s = (((1 : ℕ) : ℤ).negOnePow : ℤ) • (D ≫ (chainsXIso R E 0).inv ≫ t') := by
    apply (cancel_epi (chainsXIso R E 1).hom).1
    apply (cancel_mono (resι R F)).1
    rw [Category.assoc, ← e]
    simp only [Units.smul_def, Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
  refine ⟨(((1 : ℕ) : ℤ).negOnePow : ℤ) • ((chainsXIso R E 0).inv ≫ t'), ?_⟩
  rw [hs_eq]
  simp only [D, cobd, Preadditive.sum_comp, Preadditive.comp_zsmul, Preadditive.zsmul_comp, Finset.smul_sum,
    smul_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftTranslateSmoothCommuteLeftInvariantOps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftTranslateSmoothCommuteLeftInvariantOps
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

theorem isSmoothFun_leftTranslate (h : IsExpLieAlgebra G 𝔤) {f : G → ℂ}
    (hf : h.IsSmoothFun f) (g : G) : h.IsSmoothFun (fun y => f (g * y)) := by
  rw [IsExpLieAlgebra.isSmoothFun_iff] at hf ⊢
  intro g'
  simpa only [mul_assoc] using hf (g * g')

def leftTranslateSmoothEnd (h : IsExpLieAlgebra G 𝔤) (g : G) :
    Module.End ℂ (h.smoothFuns (F := ℂ)) where
  toFun f := ⟨fun y => (f : G → ℂ) (g * y), isSmoothFun_leftTranslate h f.2 g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coe_leftTranslateSmoothEnd (h : IsExpLieAlgebra G 𝔤) (g : G)
    (f : h.smoothFuns (F := ℂ)) (y : G) :
    ((leftTranslateSmoothEnd h g f : h.smoothFuns (F := ℂ)) : G → ℂ) y = (f : G → ℂ) (g * y) :=
  rfl

theorem commute_rightDerivEnd_leftTranslate (h : IsExpLieAlgebra G 𝔤) (g : G) (X : 𝔤) :
    Commute (h.rightDerivEnd (F := ℂ) X) (leftTranslateSmoothEnd h g) := by
  ext f y
  simp only [Module.End.mul_apply, IsExpLieAlgebra.coe_rightDerivEnd,
    coe_leftTranslateSmoothEnd, IsExpLieAlgebra.rightDeriv]
  simp only [mul_assoc]

theorem leftTranslate_smooth_commute (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸]
    [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸)
    (h : IsExpLieAlgebra G 𝔤) (f : h.smoothFuns (F := ℂ)) (g : G) :
    ∃ f' : h.smoothFuns (F := ℂ), (∀ y, (f' : G → ℂ) y = (f : G → ℂ) (g * y)) ∧
      ∀ T ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))), ∀ y,
        (T f' : G → ℂ) y = (T f : G → ℂ) (g * y) := by
  refine ⟨leftTranslateSmoothEnd h g f, fun y => rfl, fun T hT y => ?_⟩
  have hc : Commute T (leftTranslateSmoothEnd h g) := by
    refine (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hT ?_).symm
    rintro _ ⟨X, rfl⟩
    exact (commute_rightDerivEnd_leftTranslate h g X).symm
  have := congrArg (fun S : Module.End ℂ (h.smoothFuns (F := ℂ)) => ((S f : h.smoothFuns (F := ℂ)) : G → ℂ) y) hc.eq
  simpa only [Module.End.mul_apply, coe_leftTranslateSmoothEnd] using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeftTranslateSmoothCommuteLeftInvariantOpsStatement
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leftTranslate_smooth_commute_leftInvariantOps : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (f : h.smoothFuns (F := ℂ)) (g : G), ∃ f' : h.smoothFuns (F := ℂ), (∀ y, (f' : G → ℂ) y = (f : G → ℂ) (g * y)) ∧ ∀ T ∈ Algebra.adjoin ℂ (Set.range (h.rightDerivEnd (F := ℂ))), ∀ y, (T f' : G → ℂ) y = (T f : G → ℂ) (g * y) := by
  first | exact @GlobalTheory.leftTranslate_smooth_commute | exact GlobalTheory.leftTranslate_smooth_commute | (intros; apply GlobalTheory.leftTranslate_smooth_commute <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalPairDichotomy
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.PairDich

theorem isUnit_ι_appTop {T : Scheme.{0}} (W : T.Opens) (E : Γ(T, ⊤)) (h : W ≤ T.basicOpen E) :
    IsUnit (W.ι.appTop E) := by
  refine W.toScheme.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun w _ => ?_
  have hw : w ∈ W.ι ⁻¹ᵁ T.basicOpen E := h w.2
  rw [Scheme.preimage_basicOpen_top] at hw
  exact (Scheme.mem_basicOpen_top _ _ _).1 hw

theorem mem_basicOpen_or {T : Scheme.{0}} (E : Γ(T, ⊤)) (t : T) :
    t ∈ T.basicOpen E ∨ t ∈ T.basicOpen (1 - E) := by
  rw [Scheme.mem_basicOpen_top, Scheme.mem_basicOpen_top, map_sub, map_one]
  exact IsLocalRing.isUnit_or_isUnit_one_sub_self _

theorem comp_rule {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) {T : Scheme.{0}}
    (y : T ⟶ Spec (CommRingCat.of B)) (a : A) :
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (y ≫ Spec.map (CommRingCat.ofHom g)).appTop).hom a =
      ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ y.appTop).hom (g a) := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

end GlobalTheory.EtC.PairDich

namespace GlobalTheory.EtC.PairDich

theorem pair_dich : ∀ (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) (e u : A' ⊗[A] A'), (∀ a : A', (a ⊗ₜ[A] (1 : A') - (1 : A') ⊗ₜ[A] a) * e = 0) → algebraMap A (A' ⊗[A] A') f * u = 1 - e → ∀ (T : Scheme.{0}) (y y' : T ⟶ Spec (CommRingCat.of A')), y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A')) = y' ≫ Spec.map (CommRingCat.ofHom (algebraMap A A')) → Loc T fun V k => k ≫ y = k ≫ y' ∨ IsUnit (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (k ≫ y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A'))).appTop).hom f) := by
  intro A A' _ _ _ f e u he hu T y y' hyy
  let φ : A' →+* Γ(T, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of A')).inv ≫ y.appTop).hom
  let φ' : A' →+* Γ(T, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of A')).inv ≫ y'.appTop).hom
  have hA : ∀ r : A, φ (algebraMap A A' r) = φ' (algebraMap A A' r) := by
    intro r
    have := congrArg (fun m : T ⟶ Spec (CommRingCat.of A) =>
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ m.appTop).hom r) hyy
    simp only at this
    rw [comp_rule, comp_rule] at this
    exact this
  letI : Algebra A Γ(T, ⊤) := (φ.comp (algebraMap A A')).toAlgebra
  let φa : A' →ₐ[A] Γ(T, ⊤) := ⟨φ, fun _ => rfl⟩
  let φa' : A' →ₐ[A] Γ(T, ⊤) := ⟨φ', fun r => (hA r).symm⟩
  let ψ := Algebra.TensorProduct.productMap φa φa'
  have hE : ∀ a : A', (φ a - φ' a) * ψ e = 0 := by
    intro a
    have := congrArg ψ (he a)
    rw [map_mul, map_sub, Algebra.TensorProduct.productMap_apply_tmul,
      Algebra.TensorProduct.productMap_apply_tmul, map_one, map_one, mul_one, one_mul, map_zero] at this
    exact this
  have hF : ψ (algebraMap A _ f) * ψ u = 1 - ψ e := by rw [← map_mul, hu, map_sub, map_one]
  have hψf : ψ (algebraMap A _ f) = φ (algebraMap A A' f) := by rw [AlgHom.commutes]; rfl
  rw [GlobalTheory.T.etaleLocally_iff_affine_etale_point_cover]
  · intro t
    have key : ∀ G : Γ(T, ⊤), t ∈ T.basicOpen G → ∃ W : T.Opens, IsAffine W ∧ t ∈ W ∧ IsUnit (W.ι.appTop G) := by
      intro G hG
      obtain ⟨W0, hW, htW, hWle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens) hG
      exact ⟨W0, hW, htW, isUnit_ι_appTop W0 G hWle⟩
    rcases mem_basicOpen_or (ψ e) t with h1 | h2
    · obtain ⟨W, hW, htW, hunit⟩ := key _ h1
      refine ⟨W, W.ι, hW, inferInstance, by rw [Scheme.Opens.range_ι]; exact htW, Or.inl ?_⟩
      apply ext_to_Spec
      simp only [Scheme.Γ_map_op, Scheme.Hom.comp_appTop]
      ext a
      have h0 := congrArg W.ι.appTop.hom (hE a)
      rw [map_mul, map_sub, map_zero, hunit.mul_left_eq_zero, sub_eq_zero] at h0
      exact h0
    · obtain ⟨W, hW, htW, hunit⟩ := key _ h2
      refine ⟨W, W.ι, hW, inferInstance, by rw [Scheme.Opens.range_ι]; exact htW, Or.inr ?_⟩
      rw [← Category.assoc, comp_rule, Scheme.Hom.comp_appTop]
      have h0 := congrArg W.ι.appTop.hom hF
      rw [map_mul, hψf] at h0
      rw [← h0] at hunit
      exact isUnit_of_mul_isUnit_left hunit
  · rintro V W g k (h | h)
    · exact Or.inl (by rw [Category.assoc, h, Category.assoc])
    · right
      have hc : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ ((k ≫ g) ≫ y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A'))).appTop
          = ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ (g ≫ y ≫ Spec.map (CommRingCat.ofHom (algebraMap A A'))).appTop) ≫ k.appTop := by
        simp only [Scheme.Hom.comp_appTop, Category.assoc]
      rw [hc, CommRingCat.hom_comp, RingHom.comp_apply]
      exact h.map _

end GlobalTheory.EtC.PairDich
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyLevelwiseCoproductBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyLevelwiseCoproductBijective
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.HCofan

theorem comm_el {C D : AbCx} (φ : C ⟶ D) (i j : ℤ) (x : C.X i) : φ.f j (C.d i j x) = D.d i j (φ.f i x) := by
  have := ConcreteCategory.congr_hom (φ.comm i j) x
  simp only [ConcreteCategory.comp_apply] at this
  exact this.symm

theorem cochains_bij (R : Type) [CommRing R] (F : Shv R) (E : Spc) (ι : Type) (Q : ι → Spc) (a : ∀ i, Q i ⟶ E)
    (hc : ∀ k : SimplexCategoryᵒᵖ, Nonempty (IsColimit (Cofan.mk ((free R).obj (E.obj k)) (fun i => (free R).map ((a i).app k)))))
    (n : ℤ) : Function.Bijective (fun (x : ((HC R F).obj (op E)).X n) (i : ι) => ((HC R F).map (a i).op).f n x) := by
  obtain ⟨π, hπ⟩ := GlobalTheory.T.bijective_HC_component_eval_of_maps R F n
  have nat : ∀ (k : ℕ) (i : ι) (x : ((HC R F).obj (op E)).X n),
      (π k).app (op (Q i)) (((HC R F).map (a i).op).f n x) =
        (free R).map ((a i).app (op (SimplexCategory.mk k))) ≫ (π k).app (op E) x := by
    intro k i x
    have := ConcreteCategory.congr_hom ((π k).naturality (a i).op) x
    exact this
  let hk := fun k : ℕ => (hc (op (SimplexCategory.mk k))).some
  constructor
  · intro x y hxy
    apply (hπ (op E)).1
    funext k
    apply Cofan.IsColimit.hom_ext (hk k)
    intro i
    have h : ((HC R F).map (a i).op).f n x = ((HC R F).map (a i).op).f n y := congrFun hxy i
    change (free R).map ((a i).app (op (SimplexCategory.mk k))) ≫ (π k).app (op E) x =
      (free R).map ((a i).app (op (SimplexCategory.mk k))) ≫ (π k).app (op E) y
    rw [← nat, ← nat, h]
  · intro y
    obtain ⟨x, hx⟩ := (hπ (op E)).2 (fun k => Cofan.IsColimit.desc (hk k) (fun i => (π k).app (op (Q i)) (y i)))
    refine ⟨x, funext fun i => ?_⟩
    apply (hπ (op (Q i))).1
    funext k
    have e : (π k).app (op E) x = Cofan.IsColimit.desc (hk k) (fun i => (π k).app (op (Q i)) (y i)) := congrFun hx k
    show (π k).app (op (Q i)) (((HC R F).map (a i).op).f n x) = (π k).app (op (Q i)) (y i)
    rw [nat, e]
    exact Cofan.IsColimit.fac (hk k) _ i

end GlobalTheory.EtC.HCofan

theorem GlobalTheory.EtC.HCofan.main : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (ι : Type) (Q : ι → Spc) (a : ∀ i, Q i ⟶ E), (∀ k : SimplexCategoryᵒᵖ, Nonempty (IsColimit (Cofan.mk ((free R).obj (E.obj k)) (fun i => (free R).map ((a i).app k))))) → ∀ n : ℤ, Function.Bijective (fun (x : H R E F n) (i : ι) => pull R (a i) F n x) := by
  intro R _ F E ι Q a hc n
  obtain ⟨-, cl, hsurj, heq, -, hpull⟩ := GlobalTheory.EtC.HCElements.main R F
  have hb := fun m => GlobalTheory.EtC.HCofan.cochains_bij R F E ι Q a hc m
  constructor
  · intro x x' hxx
    obtain ⟨z, hz, rfl⟩ := hsurj E n x
    obtain ⟨z', hz', rfl⟩ := hsurj E n x'
    rw [heq]
    have hi : ∀ i, ∃ y, ((HC R F).map (a i).op).f n z =
        ((HC R F).map (a i).op).f n z' + ((HC R F).obj (op (Q i))).d (n - 1) n y := by
      intro i
      have h : pull R (a i) F n (cl E n z hz) = pull R (a i) F n (cl E n z' hz') := congrFun hxx i
      obtain ⟨h1, e1⟩ := hpull (Q i) E (a i) n z hz
      obtain ⟨h2, e2⟩ := hpull (Q i) E (a i) n z' hz'
      rw [e1, e2] at h
      exact (heq _ _ _ h1 _ h2).1 h
    choose y hy using hi
    obtain ⟨w, hw⟩ := (hb (n - 1)).2 y
    have hw' : ∀ i, ((HC R F).map (a i).op).f (n - 1) w = y i := fun i => congrFun hw i
    refine ⟨w, (hb n).1 (funext fun i => ?_)⟩
    show ((HC R F).map (a i).op).f n z = ((HC R F).map (a i).op).f n (z' + ((HC R F).obj (op E)).d (n - 1) n w)
    rw [map_add (f := _), GlobalTheory.EtC.HCofan.comm_el, hw' i]
    exact hy i
  · intro x
    choose z hz hzx using fun i => hsurj (Q i) n (x i)
    obtain ⟨w, hw⟩ := (hb n).2 z
    have hw' : ∀ i, ((HC R F).map (a i).op).f n w = z i := fun i => congrFun hw i
    have hdw : ((HC R F).obj (op E)).d n (n + 1) w = 0 := by
      apply (hb (n + 1)).1
      funext i
      show ((HC R F).map (a i).op).f (n + 1) (((HC R F).obj (op E)).d n (n + 1) w) = ((HC R F).map (a i).op).f (n + 1) 0
      rw [GlobalTheory.EtC.HCofan.comm_el, hw' i, hz i, map_zero]
    refine ⟨cl E n w hdw, funext fun i => ?_⟩
    obtain ⟨h1, e1⟩ := hpull (Q i) E (a i) n w hdw
    show pull R (a i) F n (cl E n w hdw) = x i
    rw [e1, ← hzx i]
    exact (heq _ _ _ h1 _ (hz i)).2 ⟨0, by rw [hw' i, map_zero, add_zero]⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyLevelwiseCoproductBijectiveStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpaceCohomology_levelwise_coproduct_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc) (ι : Type) (Q : ι → Spc) (a : ∀ i, Q i ⟶ E), (∀ k : SimplexCategoryᵒᵖ, Nonempty (IsColimit (Cofan.mk ((free R).obj (E.obj k)) (fun i => (free R).map ((a i).app k))))) → ∀ n : ℤ, Function.Bijective (fun (x : H R E F n) (i : ι) => pull R (a i) F n x) := by
  first | (exact @GlobalTheory.EtC.HCofan.main) | (exact GlobalTheory.EtC.HCofan.main) | (intros; apply GlobalTheory.EtC.HCofan.main  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfSubsingleton
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfSubsingleton
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem eqv_of_isIso {R : Type} [CommRing R] {E E' : Spc} (f : E ⟶ E') [IsIso f] (F : Shv R) :
    Eqv R f F := by
  intro n
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R (inv f) F n, ?_, ?_⟩
  · intro x
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  · intro x
    rw [← pull_comp, IsIso.hom_inv_id, pull_id]

theorem hInv_of_subsingleton : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], Subsingleton A → HInv q A := by
  intro q _ A _ hA i
  have hb : Function.Bijective (Polynomial.C : A →+* Polynomial A) :=
    ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  let e : A ≃+* Polynomial A := RingEquiv.ofBijective _ hb
  haveI : IsIso (CommRingCat.ofHom (Polynomial.C : A →+* Polynomial A)) :=
    (RingEquiv.toCommRingCatIso e).isIso_hom
  haveI : IsIso (spMap (Polynomial.C : A →+* Polynomial A)) := by
    unfold spMap; infer_instance
  exact eqv_of_isIso _ _

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleHomotopyInvariantTwistsOfSubsingletonStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleHomotopyInvariantTwists_of_subsingleton : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], Subsingleton A → HInv q A := by
  first | exact @GlobalTheory.EtC.hInv_of_subsingleton | exact GlobalTheory.EtC.hInv_of_subsingleton | (intros; apply GlobalTheory.EtC.hInv_of_subsingleton; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicPreservesSchwartzBruhat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicPreservesSchwartzBruhat
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)

namespace GlobalTheory.KSp

theorem parFun_mem : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) (p : UG c (stdJ ν E)), p ∈ sieg c ν → ∀ φ ∈ SB (Matrix α ν E), parFun c ψ χ Q (mat c p) φ ∈ SB (Matrix α ν E) := by
  intro F _ _ _ _ _ E _ _ _ _ c δ hE α _ _ ν _ _ Q hQ ψ hψ _ _ χ _ _ p hp φ hφ
  obtain ⟨-, hring, -, -, hc, -, htr, -⟩ := GlobalTheory.T.quadExt_topological_properties F E c δ hE
  obtain ⟨β, hβ, -, -, -, hform⟩ := GlobalTheory.T.hermitianMatrixColumnPairing_algebraic_properties F E c δ hE α ν Q hQ
  obtain ⟨hinv, -, -⟩ := GlobalTheory.T.splitUnitarySiegelParabolic_block_relations F E c δ hE ν p hp
  haveI := GlobalTheory.WeilM.nonarch_field F
  set a := (mat c p).toBlocks₁₁ with ha
  set b := (mat c p).toBlocks₁₂ with hb
  set d := (((mat c p).toBlocks₂₂).map c)ᵀ with hd
  have hinv' : d * a = 1 := mul_eq_one_comm.mp hinv
  have hca : Continuous fun x : Matrix α ν E => x * a := continuous_id.matrix_mul continuous_const
  have hcb : Continuous fun x : Matrix α ν E => x * b := continuous_id.matrix_mul continuous_const
  have hcd : Continuous fun x : Matrix α ν E => x * d := continuous_id.matrix_mul continuous_const
  let e : Matrix α ν E ≃ₜ Matrix α ν E :=
    { toFun := fun x => x * a
      invFun := fun x => x * d
      left_inv := fun x => by simp only [Matrix.mul_assoc, hinv, Matrix.mul_one]
      right_inv := fun x => by simp only [Matrix.mul_assoc, hinv', Matrix.mul_one]
      continuous_toFun := hca
      continuous_invFun := hcd }
  have hpr : Continuous fun x : Matrix α ν E => (2⁻¹ : F) * pr c Q (x * a) (x * b) := by
    refine continuous_const.mul ?_
    have : (fun x : Matrix α ν E => pr c Q (x * a) (x * b)) = fun x =>
        2⁻¹ * Algebra.trace F E (Matrix.trace (Qᵀ * ((x * a) * ((x * b).map c)ᵀ))) := by
      funext x; rw [← hβ, hform]
    rw [this]
    exact continuous_const.mul (htr.comp (continuous_const.matrix_mul
      (hca.matrix_mul (hcb.matrix_map hc).matrix_transpose)).matrix_trace)
  have h1 := (GlobalTheory.WeilM.isLocallyConstant_addChar ψ hψ).comp_continuous hpr
  have h2 : IsLocallyConstant (φ ∘ fun x : Matrix α ν E => x * a) := hφ.1.comp_continuous hca
  have h3 : HasCompactSupport (φ ∘ e) := hφ.2.comp_homeomorph e
  refine ⟨(IsLocallyConstant.const _).mul (h1.mul h2), ?_⟩
  exact HasCompactSupport.mul_left (HasCompactSupport.mul_left h3)

end GlobalTheory.KSp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelParabolicPreservesSchwartzBruhatStatement
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelParabolic_preserves_schwartzBruhat : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (α : Type) [Fintype α] [DecidableEq α] (ν : Type) [Fintype ν] [DecidableEq ν] (Q : Matrix α α E) (_ : IsHerm c Q) (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1) (χ : Eˣ →* Circle) (_ : Continuous χ) (_ : ResEtaPow (R := F) ⊥ χ (Fintype.card α)) (p : UG c (stdJ ν E)), p ∈ sieg c ν → ∀ φ ∈ SB (Matrix α ν E), parFun c ψ χ Q (mat c p) φ ∈ SB (Matrix α ν E) := by
  first | exact @GlobalTheory.KSp.parFun_mem | exact GlobalTheory.KSp.parFun_mem | (intros; apply GlobalTheory.KSp.parFun_mem <;> assumption)
end
end
