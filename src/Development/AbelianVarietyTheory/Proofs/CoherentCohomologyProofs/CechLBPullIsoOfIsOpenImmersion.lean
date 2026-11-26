module

public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsSaturatedSubmoduleIffExistsIsComplOfValuationR
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FlatOfIsFiniteOfFlatGeometricFibres

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBPullIsoOfIsOpenImmersion
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem bijective_appLE_of_le_opensRange {Y Y' : Scheme.{0}} (e : Y' ⟶ Y) [IsOpenImmersion e]
    {V : Y.Opens} (hV : V ≤ e.opensRange) {V' : Y'.Opens} (h : V' ≤ e ⁻¹ᵁ V) (h' : e ⁻¹ᵁ V ≤ V') :
    Function.Bijective (e.appLE V V' h).hom := by
  obtain rfl : V' = e ⁻¹ᵁ V := le_antisymm h h'
  have := e.isIso_app V hV
  rw [Scheme.Hom.appLE_eq_app]
  exact ConcreteCategory.bijective_of_isIso (e.app V)

theorem SecOn.pullLE_bijective_of_le_opensRange {Y Y' : Scheme.{0}} (M : LB Y) (e : Y' ⟶ Y)
    [IsOpenImmersion e] {V : Y.Opens} (hV : V ≤ e.opensRange) {V' : Y'.Opens}
    (h : V' ≤ e ⁻¹ᵁ V) (h' : e ⁻¹ᵁ V ≤ V') :
    Function.Bijective (SecOn.pullLE M e V V' h) := by
  have hb (i : M.ι) : Function.Bijective (e.appLE (V ⊓ M.U i) (V' ⊓ (M.pull e).U fun _ => i)
      ((inf_le_inf_right _ h).trans (GlobalTheory.LB.pull_inf_le e V fun _ => i))).hom :=
    bijective_appLE_of_le_opensRange e (inf_le_left.trans hV) _
      (inf_le_inf h' (GlobalTheory.LB.pull_U (L := M) e fun _ => i).ge)
  refine ⟨fun s t hst => GlobalTheory.LB.sec_ext fun i => (hb i).1 ?_, fun t => ?_⟩
  · exact (SecOn.coord_pullLE e h s fun _ => i).symm.trans
      ((congrArg (GlobalTheory.LB.coord · fun _ => i) hst).trans (SecOn.coord_pullLE e h t fun _ => i))
  · choose a ha using fun i => (hb i).2 (GlobalTheory.LB.coord t fun _ => i)
    refine ⟨GlobalTheory.LB.mkSec a fun i j => ?_, GlobalTheory.LB.sec_ext fun j =>
      (SecOn.coord_pullLE e h _ j).trans (ha (j PUnit.unit))⟩
    have e₁ : V' ⊓ (M.pull e).U (fun _ => i) ⊓ (M.pull e).U (fun _ => j) ≤
        e ⁻¹ᵁ (V ⊓ M.U i ⊓ M.U j) :=
      inf_le_inf ((inf_le_inf_right _ h).trans (GlobalTheory.LB.pull_inf_le e V fun _ => i))
        (GlobalTheory.LB.pull_U_le (L := M) e fun _ => j)
    refine (bijective_appLE_of_le_opensRange e (inf_le_left.trans (inf_le_left.trans hV)) e₁
      (inf_le_inf (inf_le_inf h' (GlobalTheory.LB.pull_U (L := M) e fun _ => i).ge)
        (GlobalTheory.LB.pull_U (L := M) e fun _ => j).ge)).1 ?_
    have := GlobalTheory.LB.coord_mem t (fun _ => i) (fun _ => j)
    rw [← ha i, ← ha j, GlobalTheory.LB.resG_appLE, GlobalTheory.LB.resG_appLE] at this
    rw [map_mul, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG, GlobalTheory.LB.appLE_resG]
    exact this.trans (congrArg (· * _) (GlobalTheory.LB.resG_pull_g (L := M) e (fun _ => i) (fun _ => j) _))

theorem cechLB_pull_iso_of_isOpenImmersion : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (Y' : Scheme.{0}) (e : Y' ⟶ Y) [IsOpenImmersion e] (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens), M.IsLB → (∀ i, D i ≤ e.opensRange) → Nonempty (cechLB (e ≫ f) (M.pull e) (fun i => e ⁻¹ᵁ D i) ≅ cechLB f M D) := by
  intro R _ Y f M Y' e _ κ _ _ D _ hD
  have w : e ≫ f = (e ≫ f) ≫ Spec.map (CommRingCat.ofHom (RingHom.id R)) := by
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]
  let φ : secCube f M D ⟶ secCube (e ≫ f) (M.pull e) fun i => e ⁻¹ᵁ D i :=
    GlobalTheory.Cube.homMk κ R (fun s => secCubePull M D w s) fun h x => secCubePull_res D w h x
  have : IsIso (cechComplexMap φ) := isIso_cechComplexMap φ fun s ⟨i, hi⟩ =>
    SecOn.pullLE_bijective_of_le_opensRange M e ((biInf_le D hi).trans (hD i))
      (preimage_biInf D e s).ge (preimage_biInf D e s).le
  exact ⟨(asIso (cechComplexMap φ)).symm⟩

end GlobalTheory.AbLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulHomologyEqZeroOfAcyclicFibre
open CategoryTheory CategoryTheory.Limits TensorProduct Function

namespace GlobalTheory

theorem exists_smul_mem_range_of_exact_fibre {R : Type*} [CommRing R] {A B C : Type*}
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    [Module.Finite R B] [Module.Projective R B] [Module.Finite R C] [Module.Projective R C]
    (K : Type*) [Field K] [Algebra R K] {f : A →ₗ[R] B} {g : B →ₗ[R] C} (hfg : g ∘ₗ f = 0)
    (h : Exact (f.lTensor K) (g.lTensor K)) (b : B) (hb : g b = 0) :
    ∃ r : R, algebraMap R K r ≠ 0 ∧ r • b ∈ LinearMap.range f := by
  let P : Ideal R := RingHom.ker (algebraMap R K)
  haveI : P.IsPrime := RingHom.ker_isPrime _
  let O := Localization.AtPrime P
  have h1 := (exact_lTensor_iff_residueField P K rfl f g).1 h
  have h2 : Exact (AlgebraTensorModule.lTensor O P.ResidueField f)
      (AlgebraTensorModule.lTensor O P.ResidueField g) ↔
      Exact ((f.baseChange O).lTensor P.ResidueField) ((g.baseChange O).lTensor P.ResidueField) :=
    Function.Exact.iff_of_ladder_linearEquiv
      (e₁ := AlgebraTensorModule.cancelBaseChange R O O P.ResidueField A)
      (e₂ := AlgebraTensorModule.cancelBaseChange R O O P.ResidueField B)
      (e₃ := AlgebraTensorModule.cancelBaseChange R O O P.ResidueField C)
      (by ext; simp) (by ext; simp)
  have h3 := h2.1 h1
  have hfg' : g.baseChange O ∘ₗ f.baseChange O = 0 := by
    rw [← LinearMap.baseChange_comp, hfg, LinearMap.baseChange_zero]
  obtain ⟨s, t, hst⟩ := exists_homotopy_of_forall_exact_residueField hfg'
    (fun m _ => forall_exact_residueField_of_isLocalRing h3 m)
  have h4 := exact_of_homotopy hfg' hst
  obtain ⟨x, hx⟩ := (h4 ((1 : O) ⊗ₜ[R] b)).1 (by simp [hb])
  obtain ⟨⟨a, u⟩, ha⟩ := IsLocalizedModule.surj P.primeCompl (TensorProduct.mk R O A 1) x
  have h5 : TensorProduct.mk R O B 1 ((u : R) • b) = TensorProduct.mk R O B 1 (f a) := by
    have := congrArg (f.lTensor O) ha
    rw [Submonoid.smul_def, map_smul] at this
    have hx' : f.lTensor O x = (1 : O) ⊗ₜ[R] b := hx
    rw [hx'] at this
    simpa using this
  obtain ⟨v, hv⟩ := IsLocalizedModule.exists_of_eq (S := P.primeCompl) h5
  refine ⟨(v * u : P.primeCompl), (v * u).2, (v : R) • a, ?_⟩
  rw [map_smul, Submonoid.coe_mul, mul_smul]
  exact hv.symm

set_option backward.isDefEq.respectTransparency false in
theorem exists_smul_homology_eq_zero_of_acyclic_fibre (R : Type) [CommRing R] [IsNoetherianRing R]
    (K : Type) [Field K] (χ : R →+* K) (C : CochainComplex (ModuleCat.{0} R) ℕ) (n : ℕ)
    (hn : ∀ p, n < p → IsZero (C.X p)) (hflat : ∀ p, Module.Flat R (C.X p))
    (hfin : ∀ p, Module.Finite R (C.homology p))
    (hac : (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).obj C).Acyclic)
    (p : ℕ) : ∃ r : R, χ r ≠ 0 ∧ ∀ z : C.homology p, r • z = 0 := by
  letI : Algebra R K := χ.toAlgebra
  obtain ⟨L, φ, -, h2, -, h4, h5, -, h7⟩ :=
    exists_finite_projective_complex_quasiIso.{0, 0} C n hn hflat hfin
  have h8 : QuasiIso
      (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).map φ) := h7 K
  have h9 : (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).obj L).ExactAt p :=
    (exactAt_iff_of_quasiIsoAt
      (((ModuleCat.extendScalars.{0, 0, 0} χ).mapHomologicalComplex _).map φ) p).2 (hac p)
  have h10 : Exact ((L.sc p).f.hom.lTensor K) ((L.sc p).g.hom.lTensor K) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 h9
  have hpt : ∀ z : L.homology p, ∃ r : R, χ r ≠ 0 ∧ r • z = 0 := by
    intro z
    let e := (L.sc p).moduleCatHomologyIso.toLinearEquiv
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (e z)
    haveI : Module.Finite R (L.sc p).X₂ := h2 _
    haveI : Module.Finite R (L.sc p).X₃ := h2 _
    haveI : Module.Projective R (L.sc p).X₂ := h4 _
    haveI : Module.Projective R (L.sc p).X₃ := h4 _
    obtain ⟨r, hr, a, ha⟩ := exists_smul_mem_range_of_exact_fibre K
      (congrArg ModuleCat.Hom.hom (L.sc p).zero) h10 b.1 b.2
    refine ⟨r, hr, e.injective ?_⟩
    rw [map_smul, map_zero, ← hb]
    exact (Submodule.Quotient.mk_eq_zero _).2 (show r • b ∈ _ from ⟨a, Subtype.ext ha⟩)
  let e := (isoOfQuasiIsoAt φ p).toLinearEquiv
  let P : PrimeSpectrum R := ⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩
  have hP : P ∉ Module.support R (C.homology p) := by
    rw [Module.notMem_support_iff']
    intro z
    obtain ⟨r, hr, hz⟩ := hpt (e.symm z)
    refine ⟨r, hr, ?_⟩
    rw [← e.apply_symm_apply z, ← map_smul, hz, map_zero]
  haveI := hfin p
  rw [Module.mem_support_iff_of_finite, SetLike.not_le_iff_exists] at hP
  obtain ⟨r, hr, hr'⟩ := hP
  exact ⟨r, hr', Module.mem_annihilator.1 hr⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomLocBijectiveGrSum
open CategoryTheory DirectSum MvPolynomial

noncomputable section

namespace GlobalTheory

open GradedHilbert

section

variable {ι : Type} {R : Type} [CommRing R]

theorem GrSum.X_smul_bijective {A : ℤ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x) {i : ι}
    (h : ∀ t, Function.Bijective (x i t)) :
    Function.Bijective fun m : GrSum hx => (X i : MvPolynomial ι R) • m := by
  have hg := isGradedMap_lsmul (GrSum.grading hx) (X_mem_polyGrading (R := R) i)
  refine ⟨hg.injective_iff.2 fun n => ?_, hg.surjective_iff.2 fun n => ?_⟩
  · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩ e
    have e' : (X i : MvPolynomial ι R) • GrSum.of hx n a = (X i : MvPolynomial ι R) • GrSum.of hx n b :=
      congrArg Subtype.val e
    rw [GrSum.X_smul_of, GrSum.X_smul_of] at e'
    obtain rfl := (h n).1 (GrSum.of_injective hx _ e')
    rfl
  · rintro ⟨_, b, rfl⟩
    obtain ⟨a, rfl⟩ := (h n).2 b
    exact ⟨⟨_, a, rfl⟩, Subtype.ext (GrSum.X_smul_of hx i n a)⟩

theorem xProd_smul_bijective_of {N : Type} [AddCommGroup N] [Module (MvPolynomial ι R) N]
    (s : Finset ι) (h : ∀ i ∈ s, Function.Bijective fun m : N => (X i : MvPolynomial ι R) • m) :
    Function.Bijective fun m : N => xProd R s • m := by
  refine Finset.prod_induction _ (fun p : MvPolynomial ι R => Function.Bijective fun m : N => p • m)
    (fun p q hp hq => ?_) ?_ h
  · simp only [mul_smul]
    exact hp.comp hq
  · simp only [one_smul]
    exact Function.bijective_id

theorem exists_homLoc_bijective_of
    {M : Type} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M]
    {N : Type} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
    [IsScalarTower R (MvPolynomial ι R) N]
    {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ] [Decomposition ℳ]
    {𝒩 : ℤ → Submodule R N} [PolyGradedSMul ι 𝒩] [Decomposition 𝒩]
    {f : M →ₗ[MvPolynomial ι R] N} (hf : IsGradedMap ℳ 𝒩 f) (s : Finset ι)
    (hb : Function.Bijective fun m : N => xProd R s • m)
    (h₁ : ∀ n, ∀ y ∈ ℳ n, f y = 0 → ∃ k : ℕ, xProd R s ^ k • y = 0)
    (h₂ : ∀ n, ∀ a ∈ 𝒩 n, ∃ (k : ℕ) (y : M), f y = xProd R s ^ k • a) (n : ℤ) :
    ∃ φ : homLoc ℳ s n →ₗ[R] 𝒩 n, Function.Bijective φ ∧
      ∀ (z : homLoc ℳ s n) (k : ℕ) (m : M), awayFrac M (xProd R s) k m = z →
        xProd R s ^ k • (φ z : N) = f m := by
  let e := LinearEquiv.ofBijective _ (toHomLoc_bijective 𝒩 hb n)
  refine ⟨e.symm.toLinearMap ∘ₗ homLocMap hf s n, e.symm.bijective.comp ⟨?_, ?_⟩, ?_⟩
  · rw [injective_iff_map_eq_zero]
    rintro ⟨_, k, m, hm, rfl⟩ hz
    have hz' : awayMap _ f (awayFrac M (xProd R s) k m) = 0 := congrArg Subtype.val hz
    rw [awayMap_awayFrac, map_eq_zero_iff _ (awayFrac_injective hb.1 k)] at hz'
    exact Subtype.ext (awayFrac_eq_zero_iff.2 (h₁ _ m hm hz'))
  · refine homLocMap_surjective_of hf (fun y => ?_) n
    induction y using Decomposition.inductionOn 𝒩 with
    | zero => exact ⟨0, by simp⟩
    | @homogeneous d a =>
      obtain ⟨k, y, hy⟩ := h₂ d a a.2
      exact ⟨k, y, hy⟩
    | add a b ha hb =>
      obtain ⟨k, ha⟩ := ha
      obtain ⟨j, hb⟩ := hb
      refine ⟨k + j, ?_⟩
      rw [smul_add]
      refine add_mem ?_ ?_
      · rw [add_comm, pow_add, mul_smul]
        exact Submodule.smul_mem _ _ ha
      · rw [pow_add, mul_smul]
        exact Submodule.smul_mem _ _ hb
  · intro z k m hm
    have h : awayFrac N (xProd R s) 0 (e.symm (homLocMap hf s n z) : N) = awayMap _ f z :=
      congrArg Subtype.val (e.apply_symm_apply (homLocMap hf s n z))
    apply awayFrac_injective hb.1 0
    rw [map_smul]
    erw [h]
    rw [← hm, awayMap_awayFrac, pow_smul_awayFrac]

theorem exists_homLoc_bijective_grSum
    {M : Type} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M]
    {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ] [Decomposition ℳ]
    {A : ℤ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x)
    {f : M →ₗ[MvPolynomial ι R] GrSum hx} (hf : IsGradedMap ℳ (GrSum.grading hx) f) (s : Finset ι)
    (hb : ∀ i ∈ s, ∀ t, Function.Bijective (x i t))
    (h₁ : ∀ n, ∀ y ∈ ℳ n, f y = 0 → ∃ k : ℕ, xProd R s ^ k • y = 0)
    (h₂ : ∀ n (a : A n), ∃ (k : ℕ) (y : M), f y = xProd R s ^ k • GrSum.of hx n a) (n : ℤ) :
    ∃ φ : homLoc ℳ s n →ₗ[R] A n, Function.Bijective φ ∧
      ∀ (z : homLoc ℳ s n) (k : ℕ) (m : M), awayFrac M (xProd R s) k m = z →
        xProd R s ^ k • GrSum.of hx n (φ z) = f m := by
  obtain ⟨ψ, hψ, hψ'⟩ := exists_homLoc_bijective_of hf s
    (xProd_smul_bijective_of s fun i hi => GrSum.X_smul_bijective hx (hb i hi)) h₁
    (by rintro n _ ⟨a, rfl⟩; exact h₂ n a) n
  refine ⟨(GrSum.pieceEquiv hx n).symm.toLinearMap ∘ₗ ψ,
    (GrSum.pieceEquiv hx n).symm.bijective.comp hψ, fun z k m e => ?_⟩
  rw [← hψ' z k m e]
  exact congrArg (fun w : GrSum.grading hx n => xProd R s ^ k • (w : GrSum hx))
    ((GrSum.pieceEquiv hx n).apply_symm_apply (ψ z))

theorem homLoc_grSum_res
    {M : Type} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M]
    {ℳ : ℤ → Submodule R M} [PolyGradedSMul ι ℳ]
    {A : ℤ → Type} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x)
    {B : ℤ → Type} [∀ n, AddCommGroup (B n)] [∀ n, Module R (B n)]
    {y : ι → ∀ n, B n →ₗ[R] B (n + 1)} (hy : OperatorsCommute y)
    (r : ∀ n, A n →ₗ[R] B n) (hr : ∀ i n a, r (n + 1) (x i n a) = y i n (r n a))
    {f : M →ₗ[MvPolynomial ι R] GrSum hx} (hf : IsGradedMap ℳ (GrSum.grading hx) f)
    {g : M →ₗ[MvPolynomial ι R] GrSum hy}
    (hfg : ∀ n m a, f m = GrSum.of hx n a → g m = GrSum.of hy n (r n a))
    {s t : Finset ι} (h : s ⊆ t) (hb : ∀ i ∈ t, ∀ n, Function.Bijective (y i n)) {n : ℤ}
    (z : homLoc ℳ s n) (a : A n) (b : B n)
    (ha : ∀ (k : ℕ) (m : M), awayFrac M (xProd R s) k m = z →
      xProd R s ^ k • GrSum.of hx n a = f m)
    (hb' : ∀ (k : ℕ) (m : M), awayFrac M (xProd R t) k m = homLocRes ℳ h n z →
      xProd R t ^ k • GrSum.of hy n b = g m) : b = r n a := by
  obtain ⟨k, m, hm, e⟩ := z.2
  obtain ⟨a', ha'⟩ := hf hm
  have h1 : g m = GrSum.map hx hy r hr (f m) := by
    rw [hfg _ m a' ha'.symm, ← ha', GrSum.map_of]
  obtain ⟨c, hc⟩ : ∃ c, xProd R t = c * xProd R s :=
    exists_eq_mul_left_of_dvd (Finset.prod_dvd_prod_of_subset s t X h)
  have h2 := hb' k (c ^ k • m) (by rw [coe_homLocRes, ← e, locRes_awayFrac X h hc])
  rw [map_smul, h1, ← ha k m e, map_smul, GrSum.map_of, ← mul_smul, ← mul_pow, ← hc] at h2
  have h3 := xProd_smul_bijective_of t fun i hi => GrSum.X_smul_bijective hy (hb i hi)
  exact GrSum.of_injective hy n (IsSMulRegular.pow k h3.1 h2)

end

theorem exists_grCube_hom_bijective (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type) [CommRing R]
    (G : Type) [AddCommGroup G] [Module R G] [Module (MvPolynomial ι R) G]
    [IsScalarTower R (MvPolynomial ι R) G] (𝒢 : ℤ → Submodule R G) [PolyGradedSMul ι 𝒢]
    [Decomposition 𝒢] (A : ℤ → Cube.{0} ι R) (x : ι → ∀ t, A t ⟶ A (t + 1))
    (hx : ∀ I : Finset ι,
      OperatorsCommute (A := fun t => (A t).obj I) fun i t => ((x i t).app I).hom)
    (ρ : ∀ I : Finset ι, G →ₗ[MvPolynomial ι R] GrSum (hx I))
    (hρ : ∀ I, IsGradedMap 𝒢 (GrSum.grading (hx I)) (ρ I))
    (hres : ∀ (I J : Finset ι) (h : I ⊆ J) (n : ℤ) (y : G) (a : (A n).obj I),
      ρ I y = GrSum.of (hx I) n a → ρ J y = GrSum.of (hx J) n (Cube.res (A n) h a))
    (hbij : ∀ (I : Finset ι), ∀ i ∈ I, ∀ t, Function.Bijective ((x i t).app I).hom)
    (hker : ∀ (I : Finset ι) (n : ℤ), ∀ y ∈ 𝒢 n, ρ I y = 0 → ∃ k : ℕ, xProd R I ^ k • y = 0)
    (hcoker : ∀ (I : Finset ι) (t : ℤ) (a : (A t).obj I), ∃ (k : ℕ) (y : G),
      ρ I y = xProd R I ^ k • GrSum.of (hx I) t a) (t : ℤ) :
    ∃ φ : grCube ι 𝒢 t ⟶ A t, ∀ I, Function.Bijective (φ.app I).hom := by
  choose φ hφ hφ' using fun I =>
    exists_homLoc_bijective_grSum (hx I) (hρ I) I (hbij I) (hker I) (hcoker I) t
  refine ⟨Cube.homMk (ι := ι) (R := R) (A := grCube ι 𝒢 t) φ fun {I J} h z => ?_, hφ⟩
  exact homLoc_grSum_res (hx I) (hx J) (fun n => Cube.res (A n) h)
    (fun i n a => (Cube.app_res (x i n) h a).symm) (hρ I) (hres I J h) h (hbij J) z _ _
    (hφ' I z) (hφ' J _)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.SecOnBasicOpenLocalization
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem secOn_basicOpen_localization :
    ∀ (Y : Scheme.{0}) (M : LB Y) (V W : Y.Opens) (a : Γ(Y, V)) (h : W ≤ V), M.IsLB → IsCompact (V : Set Y) → IsQuasiSeparated (V : Set Y) → W = Y.basicOpen a → (∀ x : SecOn M V, SecOn.restrict M h x = 0 → ∃ k : ℕ, a ^ k • x = 0) ∧ ∀ y : SecOn M W, ∃ (k : ℕ) (x : SecOn M V), SecOn.restrict M h x = rs Y h a ^ k • y := by
  intro Y M V W a h hM hV hV' hW
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hM
  refine ⟨fun x hx => GlobalTheory.QCoh.Qcqs.exists_pow_smul_eq_zero_of_isCompact (GlobalTheory.LB.toMod M) hV a h hW x hx,
    fun y => ?_⟩
  obtain ⟨k, x, e⟩ := GlobalTheory.QCoh.Qcqs.exists_pow_smul_eq_res_of_qcqs (GlobalTheory.LB.toMod M) hV hV' a h hW y
  exact ⟨k, x, e.symm⟩

end GlobalTheory.AbLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthBallQuotientEqSumMulFdeg
open TensorProduct

namespace GlobalTheory.PointSupport

theorem _root_.GlobalTheory.PointSupport.exists_algHom_ker_eq (K : Type) [Field K] [IsAlgClosed K] (R : Type)
    [CommRing R] [Algebra K R] [Algebra.FiniteType K R] (M : Ideal R) [M.IsMaximal] :
    ∃ χ : R →ₐ[K] K, RingHom.ker χ = M := by
  letI : Field (R ⧸ M) := Ideal.Quotient.field M
  haveI : Module.Finite K (R ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ M)
  let e : K ≃ₐ[K] R ⧸ M :=
    AlgEquiv.ofBijective (Algebra.ofId K (R ⧸ M)) IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K M), ?_⟩
  ext x
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

theorem _root_.GlobalTheory.PointSupport.finiteLength_and_finrank_eq_length :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (R : Type) [CommRing R] [Algebra K R]
      [Algebra.FiniteType K R] (χ₀ : R →ₐ[K] K) (O : Type) [CommRing O] [Algebra R O]
      [(RingHom.ker χ₀).IsPrime] [IsLocalization.AtPrime O (RingHom.ker χ₀)]
      (H : Type) [AddCommGroup H] [Module R H] [Module K H] [IsScalarTower K R H]
      [Module.Finite R H],
      (∀ χ : R →ₐ[K] K, χ ≠ χ₀ → ∃ r : R, χ r ≠ 0 ∧ ∀ z : H, r • z = 0) →
      IsFiniteLength O (O ⊗[R] H) ∧ Module.Finite K H ∧
        (Module.finrank K H : ℕ∞) = Module.length O (O ⊗[R] H) := by
  intro K _ _ R _ _ _ χ₀ O _ _ _ _ H _ _ _ _ _ hsupp
  classical
  haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  have hχ₀ : Function.Surjective χ₀ := fun k => ⟨algebraMap K R k, χ₀.commutes k⟩
  haveI hP : (RingHom.ker χ₀).IsMaximal := RingHom.ker_isMaximal_of_surjective _ hχ₀

  have hmax : ∀ M : Ideal R, M.IsMaximal → Module.annihilator R H ≤ M → M = RingHom.ker χ₀ := by
    intro M hM hle
    obtain ⟨χ, hχ⟩ := _root_.GlobalTheory.PointSupport.exists_algHom_ker_eq K R M
    by_cases h : χ = χ₀
    · rw [← hχ, h]
    · obtain ⟨r, hr, hrz⟩ := hsupp χ h
      have hrM : r ∈ M := hle (Module.mem_annihilator.mpr hrz)
      rw [← hχ] at hrM
      exact absurd (RingHom.mem_ker.mp hrM) hr

  have hprime : ∀ Q : Ideal R, Q.IsPrime → Module.annihilator R H ≤ Q → Q = RingHom.ker χ₀ := by
    intro Q hQ hle
    rw [← IsJacobsonRing.out' Q hQ.isRadical]
    apply le_antisymm
    · obtain ⟨J, hJ, hQJ⟩ := Ideal.exists_le_maximal Q hQ.ne_top
      rw [← hmax J hJ (hle.trans hQJ)]
      exact sInf_le ⟨hQJ, hJ⟩
    · exact le_sInf fun J hJ => (hmax J hJ.2 (hle.trans hJ.1)).ge

  letI : Module (R ⧸ Module.annihilator R H) H := Module.quotientAnnihilator
  have hmk : ∀ (r : R) (z : H), (Ideal.Quotient.mk (Module.annihilator R H) r) • z = r • z :=
    fun _ _ => rfl
  haveI : IsScalarTower R (R ⧸ Module.annihilator R H) H :=
    ⟨fun r a z => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, hmk, hmk, mul_smul]⟩
  haveI : IsScalarTower K (R ⧸ Module.annihilator R H) H :=
    ⟨fun k a z => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
      rw [Algebra.smul_def, ← Ideal.Quotient.mk_algebraMap, ← map_mul, hmk, hmk, ← Algebra.smul_def,
        smul_assoc]⟩
  haveI : Module.Finite (R ⧸ Module.annihilator R H) H :=
    Module.Finite.of_restrictScalars_finite R _ H
  have hprimeq : ∀ Q : Ideal (R ⧸ Module.annihilator R H), Q.IsPrime →
      Q.comap (Ideal.Quotient.mk _) = RingHom.ker χ₀ := fun Q hQ =>
    hprime _ (Ideal.comap_isPrime _ Q) fun r hr => by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hr]
      exact Q.zero_mem
  haveI : Ring.KrullDimLE 0 (R ⧸ Module.annihilator R H) := Ring.KrullDimLE.mk₀ fun Q hQ => by
    rw [← Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective Q, hprimeq Q hQ]
    refine Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective ?_
    rw [Ideal.mk_ker, ← hprimeq Q hQ]
    intro r hr
    rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr hr]
    exact Q.zero_mem
  haveI : Module.Finite K (R ⧸ Module.annihilator R H) :=
    (Module.finite_iff_krullDimLE_zero K _).mpr inferInstance
  haveI hfin : Module.Finite K H := Module.Finite.trans (R ⧸ Module.annihilator R H) H

  have hunit : ∀ s : (RingHom.ker χ₀).primeCompl, IsUnit (algebraMap R (Module.End R H) s) := by
    intro s
    have ha : IsUnit (Ideal.Quotient.mk (Module.annihilator R H) (s : R)) := by
      by_contra h
      obtain ⟨I, hI, hsI⟩ := exists_max_ideal_of_mem_nonunits h
      have hsI' : (s : R) ∈ Ideal.comap (Ideal.Quotient.mk (Module.annihilator R H)) I := hsI
      rw [hprimeq I hI.isPrime] at hsI'
      exact s.2 hsI'
    rw [Module.End.isUnit_iff]
    obtain ⟨b, hb⟩ := ha.exists_right_inv
    refine ⟨fun x y hxy => ?_, fun z => ⟨b • z, ?_⟩⟩
    · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply, ← hmk, ← hmk] at hxy
      exact ha.smul_left_cancel.mp hxy
    · rw [Module.algebraMap_end_apply, ← hmk, smul_smul, hb, one_smul]
  haveI : IsLocalizedModule (RingHom.ker χ₀).primeCompl (LinearMap.id : H →ₗ[R] H) :=
    IsLocalizedModule.mk hunit (fun y => ⟨⟨y, 1⟩, one_smul _ _⟩)
      (fun {x₁ x₂} h => ⟨1, by simpa using h⟩)
  let e : H ≃ₗ[R] O ⊗[R] H := IsLocalizedModule.linearEquiv (RingHom.ker χ₀).primeCompl
    LinearMap.id (TensorProduct.mk R O H 1)

  letI : Algebra K O := ((algebraMap R O).comp (algebraMap K R)).toAlgebra
  haveI : IsScalarTower K R O := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let eK : H ≃ₗ[K] O ⊗[R] H := e.restrictScalars K
  haveI : IsLocalRing O := IsLocalization.AtPrime.isLocalRing O (RingHom.ker χ₀)
  haveI : IsLocalHom (algebraMap K O) := ⟨fun k hk => by
    by_cases h0 : k = 0
    · rw [h0, map_zero] at hk
      exact absurd hk not_isUnit_zero
    · exact isUnit_iff_ne_zero.mpr h0⟩
  haveI : Module.Finite K (O ⊗[R] H) := Module.Finite.equiv eK

  have hsurj : Function.Surjective
      (algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O)) := by
    have hR : ∀ r : R, IsLocalRing.residue O (algebraMap R O r) ∈
        (algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O)).fieldRange := by
      intro r
      refine ⟨IsLocalRing.residue K (χ₀ r), ?_⟩
      have hmem : algebraMap R O (r - algebraMap K R (χ₀ r)) ∈ IsLocalRing.maximalIdeal O := by
        rw [IsLocalization.AtPrime.to_map_mem_maximal_iff O (RingHom.ker χ₀), RingHom.mem_ker,
          map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, map_sub, sub_eq_zero] at hmem
      rw [hmem]
      exact IsLocalRing.ResidueField.map_residue (algebraMap K O) (χ₀ r)
    intro x
    obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq (RingHom.ker χ₀).primeCompl o
    rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul]
    have hs : IsLocalRing.residue O (IsLocalization.mk' O (1 : R) s) =
        (IsLocalRing.residue O (algebraMap R O s))⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← map_mul, IsLocalization.mk'_spec, map_one, map_one]
    rw [hs]
    exact Subfield.mul_mem _ (hR r) (Subfield.inv_mem _ (hR s))
  have hres : Module.length (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O) = 1 := by
    let f := LinearEquiv.ofBijective
      (Algebra.linearMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O))
      ⟨(algebraMap (IsLocalRing.ResidueField K) (IsLocalRing.ResidueField O)).injective, hsurj⟩
    rw [← f.length_eq, Module.length_eq_one_iff]
    infer_instance
  have hlen := IsLocalRing.length_restrictScalars K O (O ⊗[R] H)
  rw [hres, mul_one, Module.length_eq_finrank K] at hlen
  have hfr : Module.finrank K H = Module.finrank K (O ⊗[R] H) := eK.finrank_eq
  refine ⟨?_, hfin, ?_⟩
  · rw [← Module.length_ne_top_iff, ← hlen]
    exact ENat.coe_ne_top _
  · rw [hfr]
    exact hlen

end GlobalTheory.PointSupport
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsTwExtendPowMul
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw.TwExtend

variable {Y : Scheme.{0}}

theorem basicOpen_rs_eq {L : LB Y} (s : LB.Sec L) (k : L.ι) {W : Y.Opens} (h : W ≤ L.U k) :
    Y.basicOpen (rs Y h (s.f k)) = nonzeroLocus s ⊓ W := by
  apply le_antisymm
  · have hb : Y.basicOpen (rs Y h (s.f k)) = W ⊓ Y.basicOpen (s.f k) := Y.basicOpen_res _ _
    rw [hb]
    exact le_inf (inf_le_right.trans (le_iSup (fun k => Y.basicOpen (s.f k)) k)) inf_le_left
  · have hu := SecOn.isUnit_rs_of_le_nonzeroLocus s k
      (inf_le_right.trans h : nonzeroLocus s ⊓ W ≤ L.U k) inf_le_left
    rw [← rs_rs h inf_le_right] at hu
    have hb : Y.basicOpen (rs Y (inf_le_right : nonzeroLocus s ⊓ W ≤ W) (rs Y h (s.f k))) =
      (nonzeroLocus s ⊓ W) ⊓ Y.basicOpen (rs Y h (s.f k)) := Y.basicOpen_res _ _
    rw [Y.basicOpen_of_isUnit hu] at hb
    exact hb.le.trans inf_le_right

theorem fun_extend {W O : Y.Opens} (hW : IsAffineOpen W) (f : Γ(Y, W)) (hO : Y.basicOpen f = O)
    (h : O ≤ W) (z : Γ(Y, O)) : ∃ (n : ℕ) (x : Γ(Y, W)), rs Y h x = rs Y h f ^ n * z := by
  subst hO
  exact exists_eq_pow_mul_of_isAffineOpen Y W hW f z

theorem fun_kill {W O : Y.Opens} (hW : IsCompact (W : Set Y)) (f x : Γ(Y, W))
    (hO : Y.basicOpen f = O) (h : O ≤ W) (hx : rs Y h x = 0) : ∃ n : ℕ, f ^ n * x = 0 := by
  subst hO
  exact exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact Y hW x f hx

theorem exists_fin_cover [CompactSpace Y] {M H : LB Y} (hM : M.IsLB) (hH : H.IsLB) :
    ∃ (κ : Type) (_ : Fintype κ) (W : κ → Y.Opens) (p : κ → M.ι) (l : κ → H.ι),
      (∀ a, IsAffineOpen (W a)) ∧ (∀ a, W a ≤ M.U (p a) ⊓ H.U (l a)) ∧ ⊤ ≤ ⨆ a, W a := by
  have h : ∀ x : Y, ∃ (W : Y.Opens) (p : M.ι) (l : H.ι),
      IsAffineOpen W ∧ x ∈ W ∧ W ≤ M.U p ⊓ H.U l := by
    intro x
    obtain ⟨p, hp⟩ := LB.mem_of_cover hM x
    obtain ⟨l, hl⟩ := LB.mem_of_cover hH x
    obtain ⟨_, ⟨W, hW, rfl⟩, hx, hle⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ M.U p ⊓ H.U l from ⟨hp, hl⟩)
        (M.U p ⊓ H.U l).isOpen
    exact ⟨W, p, l, hW, hx, hle⟩
  choose W p l hW hx hle using h
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun x => (W x : Set Y))
    (fun x => (W x).isOpen) (fun x _ => Set.mem_iUnion.2 ⟨x, hx x⟩)
  refine ⟨s, inferInstance, fun a => W a, fun a => p a, fun a => l a, fun a => hW a,
    fun a => hle a, ?_⟩
  intro x _
  obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, ha⟩, hxa⟩

theorem unit_shift {R : Type} [CommRing R] (A B : Rˣ) (t d : ℤ) (k : ℕ) {u v : R}
    (h : u = (B ^ d).val * v) :
    (A * B ^ (t + k * d)).val * v ^ k = u ^ k * (A * B ^ t).val := by
  rw [h, zpow_add, mul_comm (k : ℤ) d, zpow_mul, zpow_natCast]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, mul_pow]
  ring

theorem pw_rel {H : LB Y} {d : ℤ} (σ : LB.Sec (pw H d)) (u : ∀ l, Γ(Y, H.U l))
    (hu : ∀ l, u l = σ.f l) (l m : H.ι) {O : Y.Opens}
    (hl : O ≤ H.U l) (hm : O ≤ H.U m) (h : O ≤ H.U l ⊓ H.U m) :
    rs Y hl (u l) = (res h (H.g l m) ^ d).val * rs Y hm (u m) := by
  rw [← map_zpow, hu, hu]
  exact GlobalTheory.LB.sec_rel σ l m hl hm h

end GlobalTheory.AbLaw.TwExtend

namespace GlobalTheory.AbLaw

open TwExtend

theorem exists_tw_extend_pow_mul : ∀ (Y : Scheme.{0}) (H M : LB Y) (d : ℤ) (σ : LB.Sec (pw H d)) (V : Y.Opens) (t : ℤ), H.IsLB → M.IsLB → V = nonzeroLocus σ → CompactSpace Y → QuasiSeparatedSpace Y → ∀ y : SecOn (tw M H t) V, ∃ (k : ℕ) (a : SecOn (tw M H (t + k * d)) ⊤), ∀ (p : M.ι) (l : H.ι), rs Y (inf_le_inf_right _ le_top : V ⊓ (M.U p ⊓ H.U l) ≤ ⊤ ⊓ (M.U p ⊓ H.U l)) (SecOn.twCoord a p l) = rs Y (inf_le_right.trans inf_le_right : V ⊓ (M.U p ⊓ H.U l) ≤ H.U l) (σ.f l) ^ k * SecOn.twCoord y p l := by
  intro Y H M d σ V t hH hM hV _ _ y
  obtain ⟨u, hu⟩ : ∃ u : ∀ l, Γ(Y, H.U l), ∀ l, u l = σ.f l := ⟨σ.f, fun _ => rfl⟩
  have hb : ∀ l {W : Y.Opens} (h : W ≤ H.U l), Y.basicOpen (rs Y h (u l)) = V ⊓ W := by
    intro l W h
    rw [hu, hV]
    exact basicOpen_rs_eq σ l h
  have hrel := pw_rel σ u hu
  suffices key : ∃ (k : ℕ) (a : SecOn (tw M H (t + k * d)) ⊤), ∀ (p : M.ι) (l : H.ι),
      rs Y (inf_le_inf_right _ le_top : V ⊓ (M.U p ⊓ H.U l) ≤ ⊤ ⊓ (M.U p ⊓ H.U l))
        (SecOn.twCoord a p l) =
      rs Y (inf_le_right.trans inf_le_right : V ⊓ (M.U p ⊓ H.U l) ≤ H.U l) (u l) ^ k *
        SecOn.twCoord y p l by
    simp only [hu] at key
    exact key
  clear hu hV σ
  obtain ⟨κ, _, W, p, l, hW, hWc, hc⟩ := exists_fin_cover hM hH
  have hWl : ∀ a, W a ≤ H.U (l a) := fun a => (hWc a).trans inf_le_right
  have hWp : ∀ a, W a ≤ M.U (p a) := fun a => (hWc a).trans inf_le_left
  choose n x hx using fun a => fun_extend (hW a) (rs Y (hWl a) (u (l a))) (hb _ _) inf_le_right
    (rs Y (inf_le_inf_left V (hWc a)) (SecOn.twCoord y (p a) (l a)))
  obtain ⟨N, hN⟩ : ∃ N, ∀ a, n a ≤ N :=
    ⟨Finset.univ.sup n, fun a => Finset.le_sup (Finset.mem_univ a)⟩
  obtain ⟨x', hx'⟩ : ∃ x' : ∀ a, Γ(Y, W a), ∀ a {O : Y.Opens} (hO : O ≤ W a) (hO' : O ≤ V),
      rs Y hO (x' a) = rs Y (hO.trans (hWl a)) (u (l a)) ^ N *
        rs Y (le_inf hO' (hO.trans (hWc a))) (SecOn.twCoord y (p a) (l a)) := by
    refine ⟨fun a => rs Y (hWl a) (u (l a)) ^ (N - n a) * x a, fun a O hO hO' => ?_⟩
    have := congrArg (rs Y (le_inf hO' hO)) (hx a)
    simp only [map_mul, map_pow, rs_rs] at this ⊢
    rw [this, ← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel (hN a)]
  have hk : ∀ q : κ × κ, ∃ K : ℕ, rs Y (inf_le_left.trans (hWl q.1)) (u (l q.1)) ^ K *
      (rs Y (inf_le_left : W q.1 ⊓ W q.2 ≤ _) (x' q.1) -
        (res (inf_le_inf (hWp q.1) (hWp q.2)) (M.g (p q.1) (p q.2)) *
          res (inf_le_inf (hWl q.1) (hWl q.2)) (H.g (l q.1) (l q.2)) ^ (t + N * d)).val *
        rs Y inf_le_right (x' q.2)) = 0 := by
    rintro ⟨a, b⟩
    refine fun_kill (QuasiSeparatedSpace.inter_isCompact _ _ (W a).isOpen (hW a).isCompact
      (W b).isOpen (hW b).isCompact) _ _ (hb _ _) inf_le_right ?_
    have hM' : V ⊓ (W a ⊓ W b) ≤ M.U (p a) ⊓ M.U (p b) :=
      inf_le_right.trans (inf_le_inf (hWp a) (hWp b))
    have hH' : V ⊓ (W a ⊓ W b) ≤ H.U (l a) ⊓ H.U (l b) :=
      inf_le_right.trans (inf_le_inf (hWl a) (hWl b))
    have e : rs Y (inf_le_right : V ⊓ (W a ⊓ W b) ≤ W a ⊓ W b)
        (res (inf_le_inf (hWp a) (hWp b)) (M.g (p a) (p b)) *
          res (inf_le_inf (hWl a) (hWl b)) (H.g (l a) (l b)) ^ (t + N * d)).val =
        (res hM' (M.g (p a) (p b)) * res hH' (H.g (l a) (l b)) ^ (t + N * d)).val := by
      refine (GlobalTheory.LB.val_res _ _).symm.trans (congrArg Units.val ?_)
      rw [map_mul, map_zpow, LB.res_res, LB.res_res]
    rw [map_sub, map_mul, e, rs_rs, rs_rs, hx' a _ inf_le_left, hx' b _ inf_le_left,
      SecOn.twCoord_compat y (p a) (p b) (l a) (l b) _
        (inf_le_inf_left V (inf_le_right.trans (hWc b))) hM' hH', ← _root_.mul_assoc,
      ← _root_.mul_assoc, unit_shift _ _ t d N (hrel (l a) (l b) (hH'.trans inf_le_left) _ hH'),
      sub_self]
  choose k hk using hk
  obtain ⟨K, hK⟩ : ∃ K, ∀ q, k q ≤ K :=
    ⟨Finset.univ.sup k, fun a => Finset.le_sup (Finset.mem_univ a)⟩
  have hNK : t + ((N + K : ℕ) : ℤ) * d = t + N * d + K * d := by push_cast; ring
  obtain ⟨s, hs, -⟩ := SecOn.existsUnique_of_local (isLB_tw hM hH (t + ((N + K : ℕ) : ℤ) * d))
    (V := ⊤) W (fun _ => le_top) hc (fun a => (p a, l a)) hWc
    (fun a => rs Y (hWl a) (u (l a)) ^ K * x' a) (fun a b => by
      have e := congrArg Units.val (SecOn.res_tw_g (M := M) (H := H)
        (t + ((N + K : ℕ) : ℤ) * d) (p a) (p b) (l a) (l b) (inf_le_inf (hWc a) (hWc b))
        (inf_le_inf (hWp a) (hWp b)) (inf_le_inf (hWl a) (hWl b)))
      refine Eq.trans ?_ (congrArg (· * rs Y (inf_le_right : W a ⊓ W b ≤ W b)
        (rs Y (hWl b) (u (l b)) ^ K * x' b)) e.symm)
      have h0 := hk (a, b)
      have h1 := unit_shift (res (inf_le_inf (hWp a) (hWp b)) (M.g (p a) (p b))) _ (t + N * d) d K
        (hrel (l a) (l b) (inf_le_left.trans (hWl a)) (inf_le_right.trans (hWl b))
          (inf_le_inf (hWl a) (hWl b)))
      simp only [map_mul, map_pow, rs_rs]
      rw [hNK, ← _root_.mul_assoc, h1, ← Nat.sub_add_cancel (hK (a, b)), pow_add]
      linear_combination
        rs Y (inf_le_left.trans (hWl a) : W a ⊓ W b ≤ _) (u (l a)) ^ (K - k (a, b)) * h0)
  refine ⟨N + K, s, fun q m => ?_⟩
  refine GlobalTheory.LB.fun_ext_of_cover (fun a => V ⊓ (M.U q ⊓ H.U m) ⊓ W a) (fun _ => inf_le_left)
    (GlobalTheory.LB.le_iSup_inf (top_unique hc) _) fun a => ?_
  change rs Y _ _ = rs Y _ _
  have hM' : V ⊓ (M.U q ⊓ H.U m) ⊓ W a ≤ M.U q ⊓ M.U (p a) :=
    inf_le_inf (inf_le_right.trans inf_le_left) (hWp a)
  have hH' : V ⊓ (M.U q ⊓ H.U m) ⊓ W a ≤ H.U m ⊓ H.U (l a) :=
    inf_le_inf (inf_le_right.trans inf_le_right) (hWl a)
  have hs' : rs Y (le_inf le_top (hWc a)) (SecOn.twCoord s (p a) (l a)) =
    rs Y (hWl a) (u (l a)) ^ K * x' a := hs a
  have e := congrArg (rs Y (inf_le_right : V ⊓ (M.U q ⊓ H.U m) ⊓ W a ≤ W a)) hs'
  rw [map_mul, map_pow, rs_rs, rs_rs, hx' a _ (inf_le_left.trans inf_le_left),
    ← _root_.mul_assoc, ← pow_add, add_comm K N] at e
  rw [map_mul, map_pow, rs_rs, rs_rs,
    SecOn.twCoord_compat s q (p a) m (l a) _ (le_inf le_top (inf_le_right.trans (hWc a))) hM' hH',
    SecOn.twCoord_compat y q (p a) m (l a) _
      (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans (hWc a))) hM' hH',
    e, ← _root_.mul_assoc, ← _root_.mul_assoc,
    unit_shift _ _ t d (N + K) (hrel m (l a) (hH'.trans inf_le_left) _ hH')]

end GlobalTheory.AbLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularLocalRingAndRingKrullDimEqOfPolAV
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory

theorem isRegularLocalRing_and_ringKrullDim_eq_of_polAV :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (R : Type) [CommRing R] (t₀ : Spec (CommRingCat.of R) ⟶ P.A.left) (m : Ideal R) [m.IsMaximal] (O : Type) [CommRing O] [Algebra R O] [IsLocalization.AtPrime O m], IsOpenImmersion t₀ → IsRegularLocalRing O ∧ ringKrullDim O = P.g := by
  intro K _ _ P R _ t₀ m hm O _ _ _ ht
  have hab := P.isAb
  have hd := P.smoothDim
  have hsm : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g _
  have hgi : GeometricallyIntegral P.A.hom :=
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hsm hab.geomConnected
  have hint : IsIntegral P.A.left := GeometricallyIntegral.isIntegral_of_subsingleton P.A.hom
  have hnt : Nontrivial R := ⟨⟨0, 1, fun h => hm.ne_top ((Ideal.eq_top_iff_one m).2 (h ▸ m.zero_mem))⟩⟩
  let φ : CommRingCat.of K ⟶ CommRingCat.of R := Spec.preimage (t₀ ≫ P.A.hom)
  have hφ : t₀ ≫ P.A.hom = Spec.map φ := (Spec.map_preimage _).symm
  let _ : Algebra K R := φ.hom.toAlgebra
  have hφ' : t₀ ≫ P.A.hom = Spec.map (CommRingCat.ofHom (algebraMap K R)) := hφ
  have htr : Algebra.trdeg K R = P.g :=
    trdeg_eq_of_smoothOfRelativeDimension K P.A.left P.A.hom P.g hd R t₀ ht hφ'
  have : IsIntegral (Spec (CommRingCat.of R)) := isIntegral_of_isOpenImmersion t₀
  have : IsDomain R := (affine_isIntegral_iff (CommRingCat.of R)).1 inferInstance
  have hs : Smooth (Spec.map φ) := hφ ▸ inferInstance
  have hs' : Algebra.Smooth K R := (HasRingHomProperty.Spec_iff (P := @Smooth)).1 hs
  have hreg : IsRegularRing R := isRegularRing_of_smooth K R
  have hh := ReciprocityTheory.CA.height_eq_of_isMaximal_of_trdeg_eq_field P.g htr m
  refine ⟨?_, ?_⟩
  · have := isRegularRing_iff.mp hreg m
    exact IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv m.primeCompl
      (Localization.AtPrime m) O).toRingEquiv
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height m O, hh]
    rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSmulOfTwCoord
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory

theorem GrSum.apply_eq_eval₂Hom_mul {ι R B : Type*} [CommRing R] [CommRing B]
    {A : ℤ → Type*} [∀ n, AddCommGroup (A n)] [∀ n, Module R (A n)]
    {x : ι → ∀ n, A n →ₗ[R] A (n + 1)} (hx : OperatorsCommute x) (c : R →+* B) (b : ι → B)
    (φ : ∀ n, A n → B) (hadd : ∀ n a a', φ n (a + a') = φ n a + φ n a')
    (hsmul : ∀ n (r : R) a, φ n (r • a) = c r * φ n a)
    (hop : ∀ i n a, φ (n + 1) (x i n a) = b i * φ n a)
    (F : MvPolynomial ι R) {t t' : ℤ} {a : A t} {a' : A t'}
    (h : F • GrSum.of hx t a = GrSum.of hx t' a') :
    φ t' a' = MvPolynomial.eval₂Hom c b F * φ t a := by
  letI : Algebra R B := c.toAlgebra
  letI : Algebra (MvPolynomial ι R) B := (MvPolynomial.eval₂Hom c b).toAlgebra
  haveI : IsScalarTower R (MvPolynomial ι R) B :=
    IsScalarTower.of_algebraMap_eq fun r => (MvPolynomial.eval₂Hom_C c b r).symm
  let ψ : ∀ n, A n →ₗ[R] B := fun n => ⟨⟨φ n, hadd n⟩, hsmul n⟩
  have hψ : ∀ i n a, ψ (n + 1) (x i n a) = (MvPolynomial.X i : MvPolynomial ι R) • ψ n a :=
    fun i n a => (hop i n a).trans
      (congrArg (· * φ n a) (MvPolynomial.eval₂Hom_X' c b i).symm)
  have e := congrArg (GrSum.lift hx ψ hψ) h
  rw [map_smul, GrSum.lift_of, GrSum.lift_of] at e
  exact e.symm

theorem AbLaw.exists_smul_of_twCoord :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H) (M : LB Y) (hx : ∀ V : Y.Opens, OperatorsCommute (ι := Fin (m + 1)) (A := fun t => SecOnR f (tw M H t) V) fun i t => SecOnR.mulSec f M t (s i) V) (V : Y.Opens) (F : MvPolynomial (Fin (m + 1)) R) (d t t' : ℤ) (y : SecOn (tw M H t) V), F ∈ polyGrading (Fin (m + 1)) R d → t' = t + d → ∃ y' : SecOn (tw M H t') V, F • GrSum.of (hx V) t (SecOnR.of f _ V y) = GrSum.of (hx V) t' (SecOnR.of f _ V y') ∧ ∀ (p : M.ι) (l : H.ι), SecOn.twCoord y' p l = rs Y (inf_le_right.trans inf_le_right : V ⊓ (M.U p ⊓ H.U l) ≤ H.U l) (MvPolynomial.eval₂Hom (cst f (H.U l)) (fun j => (s j).f l) F) * SecOn.twCoord y p l := by
  intro R _ Y f H m s M hx V F d t t' y hF ht
  subst ht
  obtain ⟨a, ha⟩ := (GrSum.mem_grading (hx V)).1
    (grSMul_mem (GrSum.grading (hx V)) hF (GrSum.of_mem_grading (hx V) t (SecOnR.of f _ V y)))
  refine ⟨(SecOnR.of f _ V).symm a, ha.symm, fun p l => ?_⟩
  have h₀ : V ⊓ (M.U p ⊓ H.U l) ≤ H.U l := inf_le_right.trans inf_le_right
  have e := GrSum.apply_eq_eval₂Hom_mul (hx V) (cst f (V ⊓ (M.U p ⊓ H.U l)))
    (fun j => rs Y h₀ ((s j).f l))
    (fun n z => SecOn.twCoord ((SecOnR.of f _ V).symm z) p l) (fun _ _ _ => rfl)
    (fun n r z => SecOnR.coord_base_smul r z (p, l)) (fun _ _ _ => rfl) F ha.symm
  refine e.trans (congrArg (· * SecOn.twCoord y p l) ?_)
  rw [MvPolynomial.map_eval₂Hom]
  congr 2
  exact RingHom.ext fun r => (rs_cst f h₀ r).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemNonzeroLocusIffMemBasicOpenChart
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory

theorem mem_nonzeroLocus_iff_mem_basicOpen_chart {Y : Scheme.{0}} {H : LB Y} (s : LB.Sec H) (k : H.ι)
    {x : Y} (hk : x ∈ H.U k) : x ∈ nonzeroLocus s ↔ x ∈ Y.basicOpen (s.f k) := by
  refine ⟨fun hx => ?_, fun hx => TopologicalSpace.Opens.mem_iSup.2 ⟨k, hx⟩⟩
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  have e := congrArg Y.basicOpen (s.compat k l)
  rw [Scheme.basicOpen_mul, Y.basicOpen_of_isUnit (H.g k l).isUnit] at e
  erw [Scheme.basicOpen_res, Scheme.basicOpen_res] at e
  have hx' : x ∈ H.U k ⊓ H.U l := ⟨hk, Y.basicOpen_le _ hl⟩
  exact (e.ge ⟨hx', hx', hl⟩).2

theorem mem_basicOpen_finset_prod_iff {Y : Scheme.{0}} {U : Y.Opens} {ι : Type} (f : ι → Γ(Y, U))
    (I : Finset ι) {x : Y} (hx : x ∈ U) :
    x ∈ Y.basicOpen (∏ i ∈ I, f i) ↔ ∀ i ∈ I, x ∈ Y.basicOpen (f i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using hx
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Scheme.basicOpen_mul, Finset.forall_mem_insert, ← ih]
    rfl

theorem mem_finset_biInf_opens_iff {Y : Scheme.{0}} {ι : Type} (D : ι → Y.Opens) (I : Finset ι)
    {x : Y} : x ∈ (⨅ i ∈ I, D i) ↔ ∀ i ∈ I, x ∈ D i := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.iInf_insert, Finset.forall_mem_insert, ← ih]
    rfl

theorem exists_prod_sec_nonzeroLocus : ∀ (Y : Scheme.{0}) (H : LB Y) (ι : Type) (s : ι → LB.Sec H) (I : Finset ι), H.IsLB → ∃ σ : LB.Sec (pw H (I.card : ℤ)), (∀ l : H.ι, σ.f l = ∏ i ∈ I, (s i).f l) ∧ nonzeroLocus σ = ⨅ i ∈ I, nonzeroLocus (s i) := by
  intro Y H ι s I hH
  let σ : LB.Sec (pw H (I.card : ℤ)) :=
    { f := fun l : H.ι => ∏ i ∈ I, (s i).f l
      compat := fun k l : H.ι => by
        change (Y.presheaf.map (homOfLE (inf_le_left : H.U k ⊓ H.U l ≤ H.U k)).op).hom
            (∏ i ∈ I, (s i).f k) = ((H.g k l ^ (I.card : ℤ) : Γ(Y, H.U k ⊓ H.U l)ˣ) :
              Γ(Y, H.U k ⊓ H.U l)) *
          (Y.presheaf.map (homOfLE (inf_le_right : H.U k ⊓ H.U l ≤ H.U l)).op).hom
            (∏ i ∈ I, (s i).f l)
        rw [map_prod, map_prod, zpow_natCast, Units.val_pow_eq_pow_val, ← Finset.prod_const,
          ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ => (s i).compat k l }
  refine ⟨σ, fun _ => rfl, TopologicalSpace.Opens.ext (Set.ext fun x => ?_)⟩
  obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 (hH.cover.ge (show x ∈ (⊤ : Y.Opens) from trivial))
  refine (mem_nonzeroLocus_iff_mem_basicOpen_chart σ l hl).trans
    (((mem_basicOpen_finset_prod_iff (fun i => (s i).f l) I hl).trans ?_).trans
      (mem_finset_biInf_opens_iff (fun i => nonzeroLocus (s i)) I).symm)
  exact forall₂_congr fun i _ => (mem_nonzeroLocus_iff_mem_basicOpen_chart (s i) l hl).symm

end GlobalTheory
end
