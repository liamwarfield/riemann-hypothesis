module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmTensorSmoothOfRelativeDimension
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyPolAVGenericFibreWithLieBasis
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmCurveBaseChangeComp
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KTrivOfLamEq
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
public import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq
public import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.FrMapComp
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqSmulOfFinrankOne
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.FinrankInt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RelAmpleOfGenericIso
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.TripleModel

open GlobalTheory.PrimNorm GlobalTheory.MulPull

section Charts

variable {Y Y' : Scheme.{0}}

end Charts

section Cubical

theorem isPullCubical_of_lbIso (hG : Out.GlobalFnsSt) {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G']
    [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (hA : IsAbelianScheme G') {f : S' ⟶ S} {α : G'.left ⟶ G.left}
    (gp : IsGrpPullback G' G f α) {L' : RigLB G'} {L : RigLB G}
    (c' : CubicalStr G' L') (c : CubicalStr G L) (h : LBIso L'.L (L.L.pull α)) :
    (cubeMapOf gp).IsPullCubical c' c := by
  obtain ⟨w, hw⟩ := h
  have hw' := (isGen_iff w).1 hw
  obtain ⟨a, ha, hm⟩ := DegPull.exists_pmaps (K := PUnit) hw' L.isLB L'.isLB (φ' := fun _ => eSec G')
    (φ := fun _ => eSec G) (ε := fun _ => 1) (cubeMapOf gp).e (fun _ => (cubeMapOf gp).e_comm) L.rig L.rigGen
  obtain ⟨u, hu⟩ := HeckePoint.exists_unit_ratio L'.isLB a L'.rig ha L'.rigGen
  let w₁ : LB.Iso L'.L (L.L.pull α) :=
    ⟨fun p => w.s p * res (U := G'.hom ⁻¹ᵁ ⊤) (fun _ _ => trivial) (pullU G'.hom ⊤ u)⟩
  have g₁ : ∀ (Y : Scheme.{0}) (f : Y ⟶ G'.left) (y : Y) j k, α (f y) ∈ L.L.U j → f y ∈ L'.L.U k →
      gw w₁ f y j k = gw w f y j k * gm (f ≫ G'.hom) y ⊤ u := fun Y f y j k hj hk =>
    (map_mul _ _ _).trans (congrArg _ ((gm_res f y _ (show f y ∈ (L.L.pull α).U (fun _ => j) ⊓ L'.L.U k from
      ⟨mem_pull.2 hj, hk⟩) _).trans (gm_pull f G'.hom y ⊤ trivial u)))
  have hw₁ : PGen w₁ := fun Y f y j j' k k' hj hj' hk hk' => by
    rw [g₁ Y f y j k hj hk, g₁ Y f y j' k' hj' hk', hw' Y f y j j' k k' hj hj' hk hk', _root_.mul_assoc]
  refine (isPullCubical_iff _ c c').2 ⟨w₁, hw₁, fun Z r z p q hp hq => ?_, ?_⟩
  · refine (hm Z r z p q hp hq).trans ?_
    have e : (r ≫ eSec G') ≫ G'.hom = r := by
      rw [Category.assoc, show eSec G' ≫ G'.hom = 𝟙 _ from Over.w η[G'], Category.comp_id]
    have e₂ := g₁ Z (r ≫ eSec G') z _ _ (hp default) (hq default)
    rw [e] at e₂
    rw [hu Z r z q (Set.mem_iInter.2 hq), Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one]
    exact (_root_.mul_assoc _ _ _).symm.trans (congrArg (· * _) e₂.symm)
  · let e : 𝟙_ (Over S') ⟶ G3 G' := lift 1 (lift 1 1)
    have s₁ := (hG _ _ hA).2
    have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ α = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
      fun I => (cubeMapOf gp).psum_comm I.down
    refine EvenPull.pmaps_of_section (φ' := thφ G' (x3 G')) (φ := thφ G (x3 G)) (ε := thε) hw₁ L.isLB L'.isLB
      (cubeMapOf gp).F3 hψ c'.t c'.isGen
      c.t c.isGen (G3 G').hom e.left (Over.w e) (AbLaw.Cube.surj_tensor hG hA (AbLaw.Cube.surj_tensor hG hA s₁))
      (fun y J J' hJ hJ' => ?_)
    have a₁ : e.left ≫ (cubeMapOf gp).F3 =
        (lift (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G) (lift 1 1)).left := hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      have o := congrArg (fun q => q.left) (map_one (pushHom gp (𝟙_ (Over S'))))
      have e₁ : e ≫ x3 G' i = 1 := by fin_cases i <;> simp [e, x3]
      have e₂ : lift (1 : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ G) (lift 1 1) ≫ x3 G i = 1 := by
        fin_cases i <;> simp [x3]
      rw [e₁, e₂]
      exact o
    have b₁ := (isCub_cubV c (T := Over.mk ((𝟙_ (Over S')).hom ≫ f)) hJ).face 1 1
    have b₂ := (isCub_cubV c' (T := 𝟙_ (Over S')) hJ').face 1 1
    have b₃ := prod_cub (1 : 𝟙_ (Over S') ⟶ G') 1 1 (fun ψ => gw w₁ ψ y (J (ψ ≫ α)) (J' ψ))
    refine Eq.trans ((congrArg (fun q => val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t q y J) a₁).trans b₁)
      (Eq.symm ?_)
    refine (congrArg₂ (· * ·) b₃ b₂).trans ?_
    simp

end Cubical

section Ample

variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

end Ample

section Extend

variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {A : Over (Sp R)} [GrpObj A] {B : Over (Sp K)} [GrpObj B] {φ : B.left ⟶ A.left} {L : LB A.left} {L' : LB B.left}

end Extend

section Points

variable {S S' : Scheme.{0}} {A : Over S} [GrpObj A] {B : Over S'} [GrpObj B] {j : S' ⟶ S} {φ : B.left ⟶ A.left}

end Points

section Triple

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (hLaws : Out.Laws) (t₀ : SAB H (Sp K)) {A : Over (Sp R)} [GrpObj A] {φ : t₀.G.left ⟶ A.left}
  (hA : IsAbelianScheme A) (gp : IsGrpPullback t₀.G A (spMap (algebraMap R K)) φ)
  {L : LB A.left} (hL : L.IsLB) (hr : Out.Rigidified A L) (i : LBIso t₀.PP.L (L.pull φ))

include hLaws hA gp hL hr i

end Triple

end GlobalTheory.TripleModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SmoothOfRelativeDimensionTensor
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder TensorProduct
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.SerreDim

theorem finrank_tensor_of_algebra (O M k B L : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [CommRing B] [Algebra O B] [Algebra k B]
    [Module.Finite k B] [AddCommGroup L] [Module k L] [Module O L] [Module B L] [IsScalarTower k B L]
    [IsScalarTower O B L] [SMulCommClass O k L] [Module.Finite k L] :
    Module.finrank k (L ⊗[O] M) = Module.finrank O M * Module.finrank k L := by
  have : IsArtinianRing B := IsArtinianRing.of_finite k B
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq B (B ⊗[O] M) (Module.finrank O M) fun P => by
    letI : Field (B ⧸ P.asIdeal) := Ideal.Quotient.field _
    rw [(TensorProduct.AlgebraTensorModule.cancelBaseChange O B (B ⧸ P.asIdeal) (B ⧸ P.asIdeal) M).finrank_eq]
    exact TenDim.finrank_fibre O M _
  let e : L ⊗[O] M ≃ₗ[B] (Fin (Module.finrank O M) → L) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange O B B L M).symm ≪≫ₗ
      (b.equivFun.lTensor L) ≪≫ₗ TensorProduct.piScalarRight B B L _
  rw [(e.restrictScalars k).finrank_eq, Module.finrank_pi_fintype]
  simp

theorem finrank_tensor (O M k L : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [AddCommGroup L] [Module k L] [Module O L]
    [SMulCommClass O k L] [Module.Finite k L] :
    Module.finrank k (L ⊗[O] M) = Module.finrank O M * Module.finrank k L := by
  have : SMulCommClass k O L := SMulCommClass.symm _ _ _
  letI : Module (k ⊗[ℤ] O) L := TensorProduct.Algebra.module
  letI : Algebra O (k ⊗[ℤ] O) := Algebra.TensorProduct.rightAlgebra
  have : IsScalarTower k (k ⊗[ℤ] O) L := IsScalarTower.of_algebraMap_smul fun r x => by
    change (r ⊗ₜ[ℤ] (1 : O)) • x = _
    rw [TensorProduct.Algebra.smul_def, one_smul]
  have : IsScalarTower O (k ⊗[ℤ] O) L := IsScalarTower.of_algebraMap_smul fun r x => by
    change ((1 : k) ⊗ₜ[ℤ] r) • x = _
    rw [TensorProduct.Algebra.smul_def, one_smul]
  exact finrank_tensor_of_algebra O M k (k ⊗[ℤ] O) L

theorem dim_eq_of_isPullback {X Y S T X' S' : Scheme.{0}} {f : X ⟶ S} {g : Y ⟶ T} {f' : X' ⟶ S'} {a : X' ⟶ X}
    {b : S' ⟶ S} {c : X' ⟶ Y} {d : S' ⟶ T} (h : IsPullback a f' f b) (h' : IsPullback c f' g d)
    {n m : ℕ} {W : X.Opens} {V : Y.Opens} (hW : SmoothOfRelativeDimension n (W.ι ≫ f))
    (hV : SmoothOfRelativeDimension m (V.ι ≫ g)) (x : X') (hx : a x ∈ W) (hx' : c x ∈ V) : n = m := by
  have h₁ : SmoothOfRelativeDimension n ((a ⁻¹ᵁ W).ι ≫ f') :=
    (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback
      ((isPullback_morphismRestrict a W).paste_vert h) hW
  have h₂ : SmoothOfRelativeDimension m ((c ⁻¹ᵁ V).ι ≫ f') :=
    (smoothOfRelativeDimension_isStableUnderBaseChange m).of_isPullback
      ((isPullback_morphismRestrict c V).paste_vert h') hV
  have e₁ : SmoothOfRelativeDimension (0 + n) ((a ⁻¹ᵁ W ⊓ c ⁻¹ᵁ V).ι ≫ f') := by
    rw [← Scheme.homOfLE_ι _ (inf_le_left : a ⁻¹ᵁ W ⊓ c ⁻¹ᵁ V ≤ a ⁻¹ᵁ W), Category.assoc]; infer_instance
  have e₂ : SmoothOfRelativeDimension (0 + m) ((a ⁻¹ᵁ W ⊓ c ⁻¹ᵁ V).ι ≫ f') := by
    rw [← Scheme.homOfLE_ι _ (inf_le_right : a ⁻¹ᵁ W ⊓ c ⁻¹ᵁ V ≤ c ⁻¹ᵁ V), Category.assoc]; infer_instance
  simpa using H1.dim_unique _ e₁ e₂ ⟨x, hx, hx'⟩

theorem isPullback_mul {S : Scheme.{0}} (G : Over S) [GrpObj G] :
    IsPullback (fst G G * snd G G).left (snd G G).left G.hom G.hom := by
  let e : G ⊗ G ≅ G ⊗ G :=
    { hom := lift (fst G G * snd G G) (snd G G)
      inv := lift (fst G G * (snd G G)⁻¹) (snd G G)
      hom_inv_id := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.comp_mul, GrpObj.comp_inv]
      inv_hom_id := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.comp_mul, GrpObj.comp_inv] }
  have h : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  refine h.of_iso ((Over.forget S).mapIso e.symm) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · change (fst G G ≫ 𝟙 _).left = (e.inv ≫ (fst G G * snd G G)).left
    congr 1
    simp [e, MonObj.comp_mul]
  · change (snd G G ≫ 𝟙 _).left = (e.inv ≫ snd G G).left
    congr 1
    simp [e]

theorem exists_dim_of_grpObj {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G] [Smooth G.hom] :
    ∃ n, SmoothOfRelativeDimension n G.hom := by
  choose n W hW hd using H1.exists_dim G.hom
  let x₀ : G.left := η[G].left (default : PrimeSpectrum k)
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (n x₀)) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine ⟨n x₀, IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (n x₀)) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_⟩
  let p : G ⟶ G ⊗ G := lift 1 (𝟙 G)
  have p₁ : p ≫ fst G G = toUnit G ≫ η[G] := lift_fst _ _
  have p₂ : p ≫ (fst G G * snd G G) = 𝟙 G := by simp [p, MonObj.comp_mul]
  have q₁ : (fst G G).left (p.left y) = x₀ :=
    (congrArg (fun q : G ⟶ G => q.left y) p₁).trans
      (congrArg η[G].left (Subsingleton.elim (α := PrimeSpectrum k) _ _))
  have q₂ : (fst G G * snd G G).left (p.left y) = y := congrArg (fun q : G ⟶ G => q.left y) p₂
  have h : IsPullback (fst G G).left (snd G G).left G.hom G.hom := IsPullback.of_hasPullback _ _
  rw [dim_eq_of_isPullback h (isPullback_mul G) (hd x₀) (hd y) (p.left y) (q₁ ▸ hW x₀) (by rw [q₂]; exact hW y)]
  exact hd y

theorem dim_eq_field {k O M : Type} [Field k] [CommRing O] [IsDomain O] [Module.Finite ℤ O] [AddCommGroup M]
    [Module O M] [Module.Finite O M] [Module.Projective O M] {G A : Over (Sp k)} [GrpObj G] [IsCommMonObj G]
    [GrpObj A] [IsCommMonObj A] {a : OAct O G} {b : OAct O A} (t : Serre.IsTensor A b G a M) {g : ℕ}
    (hG : SmoothOfRelativeDimension g G.hom) {n : ℕ} (hA : SmoothOfRelativeDimension n A.hom) :
    n = Module.finrank O M * g := by
  obtain ⟨v, hv⟩ := TenDim.exists_isLieBasis G hG
  obtain ⟨w, hw⟩ := TenDim.exists_isLieBasis A hA
  have := Module.Finite.of_basis (Serre.Lie.basis a hv)
  have h := finrank_tensor O M k (Serre.Lie a)
  rwa [(t.lieEquivBase b).finrank_eq, Module.finrank_eq_card_basis (Serre.Lie.basis b hw),
    Module.finrank_eq_card_basis (Serre.Lie.basis a hv), Fintype.card_fin, Fintype.card_fin] at h

theorem smoothOfRelativeDimension_tensor :
    ∀ (S : Scheme.{0}) (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] (M : Type) [AddCommGroup M] [Module O M] [Module.Finite O M] [Module.Projective O M] (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (a : OAct O G) (b : OAct O A) (g : ℕ), Nonempty (Serre.IsTensor A b G a M) → SmoothOfRelativeDimension g G.hom → SmoothOfRelativeDimension (Module.finrank O M * g) A.hom := by
  rintro S O _ _ _ M _ _ _ _ G A _ _ _ _ a b g ⟨t⟩ hG
  have : Smooth G.hom := hG.smooth
  have : Smooth A.hom := t.smooth
  choose n W hW hd using H1.exists_dim A.hom
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (Module.finrank O M * g)) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension (Module.finrank O M * g)) W
    (top_le_iff.1 fun y _ => TopologicalSpace.Opens.mem_iSup.2 ⟨y, hW y⟩) fun y => ?_
  let k := A.left.residueField y
  let z : Sp k ⟶ A.left := A.left.fromSpecResidueField y
  have hz : ∀ u, z u = y := fun u => Scheme.fromSpecResidueField_apply y _
  let x : Sp k ⟶ S := z ≫ A.hom
  let z' : Sp k ⟶ pullback A.hom x := pullback.lift z (𝟙 _) (Category.id_comp _).symm
  have : Smooth ((Over.pullback x).obj A).hom := inferInstanceAs (Smooth (pullback.snd A.hom x))
  obtain ⟨m, hm⟩ := exists_dim_of_grpObj ((Over.pullback x).obj A)
  have e₁ : n y = m := H1.dim_base (IsPullback.of_hasPullback A.hom x) (hd y) hm (z' (default : PrimeSpectrum k)) (by
    have e : z' ≫ pullback.fst A.hom x = z := pullback.lift_fst _ _ _
    have e' := (congrArg (fun q : Sp k ⟶ A.left => q (default : PrimeSpectrum k)) e).trans (hz _)
    exact (congrArg (fun u => u ∈ W y) e').mpr (hW y))
  have hG' : SmoothOfRelativeDimension g (pullback.snd G.hom x) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hG
  rw [← dim_eq_field (t.pullback x) hG' hm, ← e₁]
  exact hd y

end GlobalTheory.SerreDim
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueHomOfIsGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem existsUnique_hom_of_isGrpPullback :
    ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G G₁ : Over S) (G' G₁' : Over S') [GrpObj G] [GrpObj G'] [GrpObj G₁] [GrpObj G₁'] (φ : G'.left ⟶ G.left) (φ₁ : G₁'.left ⟶ G₁.left), IsGrpPullback G' G f φ → IsGrpPullback G₁' G₁ f φ₁ → ∀ F : G ⟶ G₁, (∃! F' : G' ⟶ G₁', F'.left ≫ φ₁ = φ ≫ F.left) ∧ ∀ F' : G' ⟶ G₁', F'.left ≫ φ₁ = φ ≫ F.left → IsMonHom F → IsMonHom F' := by
  intro S S' f G G₁ G' G₁' _ _ _ _ φ φ₁ h h₁ F
  refine ⟨⟨Over.homMk (h₁.1.lift (φ ≫ F.left) G'.hom ?_) (h₁.1.lift_snd _ _ _),
    h₁.1.lift_fst _ _ _, fun F' hF' => ?_⟩, fun F' hF' hF => ?_⟩
  · rw [Category.assoc, Over.w F]
    exact h.1.w
  · apply Over.OverMorphism.ext
    apply h₁.1.hom_ext
    · exact hF'.trans (h₁.1.lift_fst _ _ _).symm
    · exact (Over.w F').trans (h₁.1.lift_snd _ _ _).symm
  · have hmul : ∀ (T : Over S') (x y : T ⟶ G'), (x * y) ≫ F' = (x ≫ F') * (y ≫ F') := by
      intro T x y
      obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_points_of_isGrpPullback S S' f G G' φ h T
      obtain ⟨Φ₁, hΦ₁⟩ := exists_mulEquiv_points_of_isGrpPullback S S' f G₁ G₁' φ₁ h₁ T
      have key : ∀ z : T ⟶ G', Φ₁ (z ≫ F') = Φ z ≫ F := fun z => by
        apply Over.OverMorphism.ext
        rw [hΦ₁, Over.comp_left, Over.comp_left, hΦ, Category.assoc, Category.assoc, hF']
      apply Φ₁.injective
      rw [map_mul, key, key, key, map_mul, MonObj.mul_comp]
    have hone : (1 : 𝟙_ (Over S') ⟶ G') ≫ F' = 1 := by
      have h1 := hmul (𝟙_ (Over S')) 1 1
      rw [_root_.mul_one] at h1
      exact _root_.left_eq_mul.mp h1
    refine ⟨?_, ?_⟩
    · simpa [Hom.one_def] using hone
    · have h2 := hmul (G' ⊗ G') (fst G' G') (snd G' G')
      simpa [Hom.mul_def] using h2

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOrthonormalFrameBorelChangeComplexFramedPo
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOrthonormalFrameBorelChangeComplexFramedPo
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT

theorem lact_one_frame {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Ψ : Finset (E →+* ℂ)}
    (y : FD.Frame Ψ r) : FD.lact (1 : GL (Fin r) E) y = y := by
  funext τ
  simp [FD.lact, FD.mat]
  rfl

theorem exists_ortho_frBor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U → ∀ y : FrPt Xo c (CAt σ), ∃ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), (U.X k).IsOrtho x.1 ∧ FrBor t (U.un k x) y := by
  intro E _ _ _ H Dw l Xo c σ r U hU y
  obtain ⟨-, -, h3, h4, -⟩ := hU
  obtain ⟨k, x, t, ht⟩ := h3 y
  obtain ⟨b, hb, ho⟩ := (FD.orthonormalFlagTranslate_holds r (U.X k)).1 x.1 x.2
  have hd := FD.OrthogonalFrameDomain.rmul_mem_dom (U.X k) x.2 hb
  obtain ⟨t', ht'⟩ := (h4 k k x ⟨_, hd⟩).2 ⟨1, (U.X k).Γ.one_mem, b, hb, by rw [lact_one_frame]⟩
  have hi := (frBor_calculus E H Dw l Xo c (CAt σ) (U.un k x) (U.un k ⟨_, hd⟩) y).2.2.2 t' ht'
  exact ⟨k, ⟨_, hd⟩, t * t'⁻¹, ho,
    (frBor_calculus E H Dw l Xo c (CAt σ) (U.un k ⟨_, hd⟩) (U.un k x) y).2.2.1 _ _ hi ht⟩

end GlobalTheory.LamT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsOrthonormalFrameBorelChangeComplexFramedPoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormalFrame_borelChange_complexFramedPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U → ∀ y : FrPt Xo c (CAt σ), ∃ (k : U.Comp) (x : (U.X k).dom) (t : Ix Dw → (CAt σ)ˣ), (U.X k).IsOrtho x.1 ∧ FrBor t (U.un k x) y := by
  first | exact @GlobalTheory.LamT.exists_ortho_frBor | exact GlobalTheory.LamT.exists_ortho_frBor | (intros; apply GlobalTheory.LamT.exists_ortho_frBor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsDvrModelLieBasisAtPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsDvrModelLieBasisAtPrime
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

namespace GlobalTheory.LamF

theorem exists_isModelAt : Out.SecTwistSt → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left), IsFibreOf A x (gmap K) φ → ∀ p : HeightOneSpectrum (𝓞 K), ∃ M, IsModelAt A x φ p M := by
  intro hT K _ _ A x φ hx p
  have hg : x.P.g = A.g := ((isFibreOf_iff_isPolFibre _ _ (algebraMap (𝓞 K) K) A x φ).1 hx).1
  have hφ : IsGrpPullback x.P.A A.A (spMap (algebraMap (𝓞 K) K)) φ := hx.1
  let R := (p.valuation K).integer
  let f : 𝓞 K →+* R := (algebraMap (𝓞 K) K).codRestrict R fun r => p.valuation_le_one r
  have hf : spMap (algebraMap R K) ≫ spMap f = spMap (algebraMap (𝓞 K) K) := (Spec.map_comp _ _).symm
  obtain ⟨y, ψ, w₀, hg₀, hψ, hw₀⟩ := KeyPow.exists_keyIn_pullback hT f A (hg ▸ x.g_pos)
  have sq : φ ≫ A.A.hom = (x.P.A.hom ≫ spMap (algebraMap R K)) ≫ spMap f := by rw [Category.assoc, hf, hφ.1.w]
  obtain ⟨φ', rfl, h₂⟩ : ∃ φ' : x.P.A.left ⟶ y.P.A.left, φ' ≫ ψ = φ ∧
      φ' ≫ y.P.A.hom = x.P.A.hom ≫ spMap (algebraMap R K) := ⟨hψ.1.lift _ _ sq, hψ.1.lift_fst _ _ _, hψ.1.lift_snd _ _ _⟩
  have h : IsGrpPullback x.P.A y.P.A (spMap (algebraMap R K)) φ' := hψ.cancel (hφ.congr hf.symm rfl) h₂
  have := x.P.isAb.comm
  have := y.P.isAb.comm
  have := y.P.isAb.smooth
  have sq' : ∀ i, (spMap (Chart.dualMapR (algebraMap R K)) ≫ (y.v i).left) ≫ y.P.A.hom =
      (epsR K).hom ≫ spMap (algebraMap R K) := fun i => by
    rw [Category.assoc, Over.w]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  let v' : Fin y.P.g → (epsR K ⟶ x.P.A) := fun i => Over.homMk (h.1.lift _ _ (sq' i)) (h.1.lift_snd _ _ _)
  have hv' : ∀ i, (v' i).left ≫ φ' = spMap (Chart.dualMapR (algebraMap R K)) ≫ (y.v i).left :=
    fun i => h.1.lift_fst _ _ _
  have hb : ∀ {n : ℕ} (e : n = y.P.g), IsLieBasis fun i : Fin n => v' (i.cast e) := fun e => by
    subst e
    exact Chart.isLieBasis_baseChange (algebraMap R K) h y.basis hv'
  have e : y.P.g = x.P.g := hg₀.trans hg.symm
  obtain ⟨a, M, -, hM⟩ := KeyPow.exists_scalar_matrix hT x.P x.th x.th x.th_ne x.basis (hb e.symm)
  have hd : Formalism.L2.Pj.dualMap (algebraMap R K) = Chart.dualMapR (algebraMap R K) := by
    ext a <;> simp [Chart.dualMapR, Formalism.L2.Pj.dualMap]
  refine ⟨M, R, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstanceAs (IsFractionRing (p.valuation K).valuationSubring K), f, y, ψ, e, rfl,
    fun z => ⟨fun ⟨r, hr⟩ => hr ▸ r.2, fun hz => ⟨⟨z, hz⟩, rfl⟩⟩, ⟨hψ, w₀, (isGen_iff _).2 hw₀⟩,
    (((LieComb.lieComb_algebra K x.P.A _ x.v x.basis.1).2.2.2.2 M _ x.basis hM).1 (hb e.symm)).ne_zero,
    fun k => ⟨_, hM k, ?_⟩⟩
  rw [hd, ← Category.assoc, hv', Category.assoc]

end GlobalTheory.LamF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsDvrModelLieBasisAtPrimeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.LamCM
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.LamF

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dvrModel_lieBasis_at_prime : Out.SecTwistSt → ∀ (K : Type) [Field K] [NumberField K] (A : Out.PolAV (Sp (𝓞 K))) (x : KeyIn K) (φ : x.P.A.left ⟶ A.A.left), IsFibreOf A x (gmap K) φ → ∀ p : HeightOneSpectrum (𝓞 K), ∃ M, IsModelAt A x φ p M := by
  first | exact @GlobalTheory.LamF.exists_isModelAt | exact GlobalTheory.LamF.exists_isModelAt | (intros; apply GlobalTheory.LamF.exists_isModelAt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNormalisedPolarisation
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNormalisedPolarisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM

open GlobalTheory.PrimNorm GlobalTheory.MulPull

theorem exists_normalised_polarisation : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R]
    (P : Out.PolAV (Sp R)) (w w' : P.A ⟶ P.A), IsMonHom w → IsMonHom w' → w * w' = 𝟙 P.A →
    LamEq P.L w (𝟙 P.A) P.L (𝟙 P.A) w' →
    ∃ L' : LB P.A.left, L'.IsLB ∧ Out.Rigidified P.A L' ∧ Out.Sym P.A L' ∧ Out.RelAmple P.A L' ∧ Out.KTriv P.A L' ∧
      LamEq L' (𝟙 P.A) (𝟙 P.A) P.L (𝟙 P.A) (𝟙 P.A) ∧ LBIso L' (cubeLB P.A ![𝟙 P.A, w] L') := by
  intro laws R _ _ P w w' hw hw' hs ha
  have : IsCommMonObj P.A := P.isAb.comm
  have hM := P.isLB
  obtain ⟨rig, hrig⟩ := P.rigid
  obtain ⟨⟨c⟩, -⟩ := laws.cube _ P ⟨P.L, rig, hM, hrig⟩ rfl
  have hT : ∃ t : LB.Gen (Theta P.A P.L), t.IsGen := ⟨c.t, c.isGen⟩
  have ha' : LBIso (cubeLB P.A ![fst P.A P.A ≫ w, snd P.A P.A] P.L)
      (cubeLB P.A ![fst P.A P.A, snd P.A P.A ≫ w'] P.L) := by
    simpa only [LamEq, Category.comp_id] using ha
  obtain ⟨Q, -, e, -, iso⟩ := exists_normalised_bundle laws.globalFns P.isAb hM hT w w' hs ha'
  have hc := fun T : Over (Sp R) => diff₃_ptCls (T := T) hM hT
  have hQ := Q.isLB
  have lam : LamEq Q.L (𝟙 P.A) (𝟙 P.A) P.L (𝟙 P.A) (𝟙 P.A) := iso _ _ _
  refine ⟨Q.L, hQ, ⟨Q.rig, Q.rigGen⟩, fun s => ⟨⊤, trivial, ?_⟩, ?_, kTriv_of_lamEq _ _ _ _ hM hQ lam P.ktriv, lam, ?_⟩
  · have h : HasGen Q.L (K := Fin 2) ![(GrpObj.inv (X := P.A)).left, 𝟙 _] ![1, -1] := by
      rw [e]
      refine hasGen_nested hM _ _ _ _ ?_
      rw [Fin.prod_univ_two]
      show normCls P.L w (GrpObj.inv (X := P.A)).left ^ (1 : ℤ) *
        normCls P.L w (𝟙 P.A : P.A ⟶ P.A).left ^ (-1 : ℤ) = 1
      have e : GrpObj.inv (X := P.A) = (𝟙 P.A)⁻¹ := by simp [Hom.inv_def]
      have e' : (𝟙 P.A)⁻¹ ≫ w = (𝟙 P.A ≫ w)⁻¹ := map_inv (postHom w P.A) _
      rw [normCls_left, normCls_left, e, e', diff₂_inv_inv (hc P.A), zpow_neg, zpow_one, mul_inv_cancel]
    have h' := h.pull (P.A.hom ⁻¹ᵁ ⊤).ι
    have e₁ : (fun k => (P.A.hom ⁻¹ᵁ ⊤).ι ≫ (![(GrpObj.inv (X := P.A)).left, 𝟙 _] : Fin 2 → _) k) =
        ![(P.A.hom ⁻¹ᵁ ⊤).ι ≫ (GrpObj.inv : P.A ⟶ P.A).left, (P.A.hom ⁻¹ᵁ ⊤).ι] := by
      funext k
      fin_cases k
      exacts [rfl, Category.comp_id _]
    rw [e₁] at h'
    exact h'
  · have one : ptCls P.L P.A 1 = 1 := by
      have h := (hasGen_iff hM _ _).1 (HasGen.pull (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1)
        ⟨rig, hrig⟩ (toUnit P.A).left)
      rw [Fintype.prod_unique, zpow_one] at h
      exact h
    have two : ptCls P.L P.A (𝟙 P.A * 𝟙 P.A) = ptCls P.L P.A (𝟙 P.A) ^ (4 : ℤ) := by
      have h := (hasGen_iff hM _ _).1 (laws.mulPull _ P 2)
      rw [Fin.prod_univ_two] at h
      have h' : ptCls P.L P.A (𝟙 P.A) ^ (((2 : ℕ) : ℤ) ^ 2) * ptCls P.L P.A (𝟙 P.A ^ 2) ^ (-1 : ℤ) = 1 := h
      rw [zpow_neg, zpow_one, mul_inv_eq_one, pow_two (𝟙 P.A)] at h'
      exact h'.symm
    have sq : LBIso (lbPow Q.L 2) (lbPow P.L 2) := by
      rw [e]
      refine lbIso_nested hM _ _ _ _ _ _ ?_
      refine (Fintype.prod_unique _).trans (Eq.trans ?_ (Fintype.prod_unique _).symm)
      show normCls P.L w (𝟙 P.A : P.A ⟶ P.A).left ^ ((2 : ℕ) : ℤ) = ptCls P.L P.A (𝟙 P.A) ^ ((2 : ℕ) : ℤ)
      rw [normCls_left, zpow_natCast, zpow_natCast, pow_two, Category.id_comp]
      have adj := diff₂_ptCls_adj hM ha' (𝟙 P.A) (𝟙 P.A)
      rw [Category.id_comp, Category.id_comp, diff₂_comm w] at adj
      nth_rewrite 2 [adj]
      rw [← diff₂_mul_right (hc P.A), hs, diff₂, one, two]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one, ofMul_zpow, ofMul_pow]
      abel
    have A₁ := relAmple_finite_pow_iso _ P.A P.A (𝟙 _) P.L 2 two_pos P.isAb P.isAb hM
      (show IsFinite (𝟙 P.A.left) from inferInstance)
    have A₂ := relAmple_finite_pow_iso _ P.A P.A (𝟙 _) Q.L 2 two_pos P.isAb P.isAb hQ
      (show IsFinite (𝟙 P.A.left) from inferInstance)
    have A₃ := relAmple_finite_pow_iso _ P.A P.A (𝟙 _) (lbPow P.L 2) 2 two_pos P.isAb P.isAb
      (DVR.linComb_isLB _ hM _ _) (show IsFinite (𝟙 P.A.left) from inferInstance)
    exact A₂.2.1.1 (A₃.2.2.2 _ (DVR.linComb_isLB _ hQ _ _) sq.symm (A₁.2.1.2 P.ample))
  · have := (iso P.A (𝟙 P.A) w).symm
    rwa [← e] at this

end GlobalTheory.CM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsNormalisedPolarisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

theorem _root_.GlobalTheory.T.exists_normalized_symmetric_ample_lb : Out.Laws → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Out.PolAV (Sp R)) (w w' : P.A ⟶ P.A), IsMonHom w → IsMonHom w' → w * w' = 𝟙 P.A → LamEq P.L w (𝟙 P.A) P.L (𝟙 P.A) w' →
  ∃ L' : LB P.A.left, L'.IsLB ∧ Out.Rigidified P.A L' ∧ Out.Sym P.A L' ∧ Out.RelAmple P.A L' ∧ Out.KTriv P.A L' ∧ LamEq L' (𝟙 P.A) (𝟙 P.A) P.L (𝟙 P.A) (𝟙 P.A) ∧ LBIso L' (cubeLB P.A ![𝟙 P.A, w] L') := by
  first | exact @GlobalTheory.CM.exists_normalised_polarisation | exact GlobalTheory.CM.exists_normalised_polarisation | (intros; apply GlobalTheory.CM.exists_normalised_polarisation <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConstantCmEvaluationFitsRoom
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConstantCmEvaluationFitsRoom
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

namespace GlobalTheory

theorem room_neg_log_epStar (f d L M k0 S : ℝ) (hf : 1 ≤ f) (hd : 1 ≤ d) (hL : 0 ≤ L)
    (hM : 0 < M) (hk : 0 < k0) (hS : 1 ≤ S)
    (h : Real.log (M * k0) ≤ 19 * L + 3 + Real.log d) :
    0 < epStar M f S k0 ∧ epStar M f S k0 ≤ 1 ∧
      -Real.log (epStar M f S k0) ≤ 19 * L + 6 + Real.log d + f + Real.log S := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num); linarith
  have hfS : 1 ≤ f * S := one_le_mul_of_one_le_of_one_le hf hS
  have hld : 0 ≤ Real.log d := Real.log_nonneg hd
  have hlS : 0 ≤ Real.log S := Real.log_nonneg hS
  have hpi := Real.pi_gt_three
  have hD : 0 < M * (f * S + 2) * k0 * Real.log 2 := by positivity
  unfold epStar
  refine ⟨lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
  rcases min_choice 1 (Real.pi / (M * (f * S + 2) * k0 * Real.log 2)) with h1 | h1 <;> rw [h1]
  · rw [Real.log_one]; linarith
  · have hMk : 0 < M * k0 := by positivity
    have e : M * (f * S + 2) * k0 * Real.log 2 = (M * k0) * ((f * S + 2) * Real.log 2) := by ring
    rw [Real.log_div (by positivity) hD.ne', e, Real.log_mul hMk.ne' (by positivity)]
    have h2 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith)
    have h3 : Real.log ((f * S + 2) * Real.log 2) ≤ Real.log (3 * f * S) :=
      Real.log_le_log (by positivity) (by nlinarith)
    have h6 : Real.log (3 * f * S) = Real.log 3 + Real.log f + Real.log S := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    have h4 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)
    have h5 := Real.log_le_sub_one_of_pos (show (0:ℝ) < f by positivity)
    linarith

theorem room_log_radius (f r : ℕ) (d e S : ℝ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hd : 1 ≤ d)
    (he : 0 < e) (hS : 1 ≤ S) :
    0 < 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (Real.sqrt e / Real.sqrt f)) (3 * frameRadius S r / 5) ∧
    Real.log (2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (Real.sqrt e / Real.sqrt f)) (3 * frameRadius S r / 5)) =
      Real.log (1600 / 3) + Real.log r + (1 / 2) * Real.log f + (1 / 2) * Real.log S
        + 3 * Real.log ((f : ℝ) * r) + Real.log d - (1 / 2) * Real.log e := by
  have hf' : (0 : ℝ) < f := by exact_mod_cast hf
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hS' : (0 : ℝ) < S := by linarith
  have hd' : (0 : ℝ) < d := by linarith
  have h1 : 0 < Real.sqrt e := Real.sqrt_pos.2 he
  have h2 : 0 < Real.sqrt f := Real.sqrt_pos.2 hf'
  have h3 : 0 < Real.sqrt r := Real.sqrt_pos.2 hr'
  have h4 : 0 < Real.sqrt (S * r) := Real.sqrt_pos.2 (by positivity)
  have E : 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (Real.sqrt e / Real.sqrt f)) (3 * frameRadius S r / 5) =
      1600 / 3 * Real.sqrt r * Real.sqrt f * Real.sqrt (S * r) * ((f : ℝ) * r) ^ 3 * d / Real.sqrt e := by
    unfold ReciprocityTheory.MultiplicativeHeights.approxR d5mu frameRadius
    field_simp
    norm_num
  rw [E]
  refine ⟨by positivity, ?_⟩
  rw [Real.log_div (by positivity) h1.ne', Real.log_mul (by positivity) hd'.ne',
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) h4.ne',
    Real.log_mul (by positivity) h2.ne', Real.log_mul (by positivity) h3.ne',
    Real.log_pow, Real.log_sqrt he.le, Real.log_sqrt hf'.le, Real.log_sqrt hr'.le,
    Real.log_sqrt (by positivity), Real.log_mul hS'.ne' hr'.ne']
  push_cast
  ring

theorem room_of_constants : ∃ C0 : ℝ, 0 < C0 ∧ ∀ (f r p0 : ℕ) (d L Om M k0 S : ℝ), 1 ≤ f → 1 ≤ r → p0 ≤ r → 1 ≤ d → 0 ≤ L → 0 < M → 0 < k0 → 1 ≤ S → Real.log (M * k0) ≤ 19 * L + 3 + Real.log d → 1 ≤ frameBasisRadius r p0 f d (Real.sqrt (epStar M f S k0)) (3 * frameRadius S r / 5) ∧ ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t ≤ S → ∀ C A : ℝ, C0 ≤ C → 2 ≤ A → (Formalism.L2.LamCM.pDeg Om + (1 / 2) * Real.log (frameBasisRadius r p0 f d (Real.sqrt (epStar M f S k0)) (3 * frameRadius S r / 5))) * (s + t) + s * Real.log ((r : ℝ) * frameBasisRadius r p0 f d (Real.sqrt (epStar M f S k0)) (3 * frameRadius S r / 5)) ≤ C * ((f : ℝ) * r + L + Real.log d + |Om|) ^ A * (1 + Real.log S) * S := by
  refine ⟨3000, by norm_num, ?_⟩
  intro f r p0 d L Om M k0 S hf hr hp hd hL hM hk hS h
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hp' : (p0 : ℝ) ≤ r := by exact_mod_cast hp
  obtain ⟨he0, he1, he2⟩ := room_neg_log_epStar f d L M k0 S hf' hd hL hM hk hS h
  obtain ⟨hX0, hX⟩ := room_log_radius f r d _ S hf hr hd he0 hS
  unfold frameBasisRadius
  set X := 2 * ReciprocityTheory.MultiplicativeHeights.approxR r (d5mu f r d (Real.sqrt (epStar M f S k0) / Real.sqrt f))
    (3 * frameRadius S r / 5) with hXdef
  clear_value X
  have hle : Real.log (epStar M f S k0) ≤ 0 := Real.log_nonpos he0.le he1
  have hn : (1 : ℝ) ≤ (f : ℝ) * r := one_le_mul_of_one_le_of_one_le hf' hr'
  have hfn : (f : ℝ) ≤ (f : ℝ) * r := le_mul_of_one_le_right (by linarith) hr'
  have hrn : (r : ℝ) ≤ (f : ℝ) * r := le_mul_of_one_le_left (by linarith) hf'
  have a1 : 0 ≤ Real.log d := Real.log_nonneg hd
  have a2 : 0 ≤ Real.log S := Real.log_nonneg hS
  have a3 : 0 ≤ Real.log (f : ℝ) := Real.log_nonneg hf'
  have a4 : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg hr'
  have a5 : 0 ≤ Real.log ((f : ℝ) * r) := Real.log_nonneg hn
  have a6 : 0 ≤ Real.log (1600 / 3 : ℝ) := Real.log_nonneg (by norm_num)
  have b3 := Real.log_le_sub_one_of_pos (show (0:ℝ) < f by linarith)
  have b4 := Real.log_le_sub_one_of_pos (show (0:ℝ) < r by linarith)
  have b5 := Real.log_le_sub_one_of_pos (show (0:ℝ) < (f : ℝ) * r by linarith)
  have b6 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1600 / 3 by norm_num)
  have hX1 : 0 ≤ Real.log X := by rw [hX]; linarith
  have hX1' : 1 ≤ X := by
    by_contra hc
    have := Real.log_neg hX0 (not_le.1 hc)
    linarith
  refine ⟨one_le_pow₀ hX1', ?_⟩
  intro s t hs ht hst C A hC hA
  have hOm := abs_nonneg Om
  set Z : ℝ := (f : ℝ) * r + L + Real.log d + |Om| with hZ
  have hZn : (f : ℝ) * r ≤ Z := by linarith
  have hZ1 : 1 ≤ Z := by linarith
  have hXZ : Real.log X ≤ 600 * Z + Real.log S := by rw [hX]; linarith
  have hXZ' : Real.log X ≤ 600 * (Z * (1 + Real.log S)) := by
    have : Real.log S ≤ Z * Real.log S := le_mul_of_one_le_left a2 hZ1
    linarith
  have hpd : Formalism.L2.LamCM.pDeg Om ≤ Z := by unfold Formalism.L2.LamCM.pDeg; linarith
  have hlog : Real.log (X ^ (2 * p0 + 1)) ≤ 1800 * (Z ^ 2 * (1 + Real.log S)) := by
    rw [Real.log_pow]
    push_cast
    calc (2 * (p0 : ℝ) + 1) * Real.log X ≤ (3 * Z) * (600 * (Z * (1 + Real.log S))) :=
          mul_le_mul (by linarith) hXZ' hX1 (by linarith)
      _ = _ := by ring
  have hlog0 : 0 ≤ Real.log (X ^ (2 * p0 + 1)) := Real.log_nonneg (one_le_pow₀ hX1')
  rw [Real.log_mul (by positivity) (by positivity)]
  have hZW : Z ≤ Z ^ 2 * (1 + Real.log S) :=
    (le_self_pow₀ hZ1 (by norm_num)).trans (le_mul_of_one_le_right (by positivity) (by linarith))
  have hZA : Z ^ 2 ≤ Z ^ A := by
    have := Real.rpow_le_rpow_of_exponent_le hZ1 hA
    rwa [Real.rpow_two] at this
  set W := Z ^ 2 * (1 + Real.log S) with hW
  set Y := Real.log (X ^ (2 * p0 + 1)) with hY
  have hW0 : 0 ≤ W := by linarith
  have c1 : (Formalism.L2.LamCM.pDeg Om + 1 / 2 * Y) * (s + t) ≤ (901 * W) * S :=
    mul_le_mul (by linarith) hst (by linarith) (by linarith)
  have c2 : s * (Real.log r + Y) ≤ S * (1801 * W) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)
  have c3 : 3000 * W ≤ C * Z ^ A * (1 + Real.log S) := by
    have : 3000 * Z ^ 2 ≤ C * Z ^ A := mul_le_mul hC hZA (by positivity) (by linarith)
    calc 3000 * W = (3000 * Z ^ 2) * (1 + Real.log S) := by rw [hW]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right this (by linarith)
  have c4 : 3000 * W * S ≤ C * Z ^ A * (1 + Real.log S) * S :=
    mul_le_mul_of_nonneg_right c3 (by linarith)
  have c5 : 0 ≤ W * S := mul_nonneg hW0 (by linarith)
  linarith

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsConstantCmEvaluationFitsRoomStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constant_cmEvaluation_fits_room : ∃ C0 : ℝ, 0 < C0 ∧ ∀ (f r p0 : ℕ) (d L Om M k0 S : ℝ), 1 ≤ f → 1 ≤ r → p0 ≤ r → 1 ≤ d → 0 ≤ L → 0 < M → 0 < k0 → 1 ≤ S → Real.log (M * k0) ≤ 19 * L + 3 + Real.log d → 1 ≤ frameBasisRadius r p0 f d (Real.sqrt (epStar M f S k0)) (3 * frameRadius S r / 5) ∧ ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → s + t ≤ S → ∀ C A : ℝ, C0 ≤ C → 2 ≤ A → (Formalism.L2.LamCM.pDeg Om + (1 / 2) * Real.log (frameBasisRadius r p0 f d (Real.sqrt (epStar M f S k0)) (3 * frameRadius S r / 5))) * (s + t) + s * Real.log ((r : ℝ) * frameBasisRadius r p0 f d (Real.sqrt (epStar M f S k0)) (3 * frameRadius S r / 5)) ≤ C * ((f : ℝ) * r + L + Real.log d + |Om|) ^ A * (1 + Real.log S) * S := by
  first | exact @GlobalTheory.room_of_constants | exact GlobalTheory.room_of_constants | (intros; apply GlobalTheory.room_of_constants <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NormMulDetGram
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.TopDifferential

theorem eq_dualMapR {R R' : Type} [CommRing R] [CommRing R'] {f : R →+* R'} {F : DualNumber R →+* DualNumber R'}
    (h₁ : ∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) (h₂ : F DualNumber.eps = DualNumber.eps) :
    F = Chart.dualMapR f := by
  refine RingHom.ext fun x => ?_
  have e : x = algebraMap R _ x.fst + algebraMap R _ x.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [e, map_add (f := _), map_mul, h₁, h₁, h₂, ← e]
  ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem det_gram {g : ℕ} (Hm W : Matrix (Fin g) (Fin g) ℂ) :
    (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W j) (W i)).det.re = Real.pi ^ g * ‖W.det‖ ^ 2 * Hm.det.re := by
  have e : (Matrix.of fun i j => (Real.pi : ℂ) * hermForm Hm (W j) (W i)) =
      (Real.pi : ℂ) • (W * (Hm * W.conjTranspose)).transpose := rfl
  rw [e, Matrix.det_smul, Matrix.det_transpose, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose,
    Fintype.card_fin, mul_left_comm W.det, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    mul_comm Hm.det, ← _root_.mul_assoc, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.re_ofReal_mul]

end GlobalTheory.CM.TopDifferential
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqNsmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM.RationalTorsion

theorem section_ext {K k : Type} [Field K] [Field k] (t : Sp k ⟶ Sp K) {G : Over (Sp K)}
    {s s' : 𝟙_ (Over (Sp K)) ⟶ G} (h : toUnit (Over.mk t) ≫ s = toUnit (Over.mk t) ≫ s') : s = s' := by
  have h1 : Surjective t := ⟨fun x => ⟨IsLocalRing.closedPoint k, Subsingleton.elim _ _⟩⟩
  have h2 : Flat t := inferInstance
  have h3 : Epi t := Flat.epi_of_flat_of_surjective t
  have h4 : (toUnit (Over.mk t)).left = t := by simp
  have h5 : Epi (toUnit (Over.mk t)).left := by rw [h4]; exact h3
  have h6 : Epi (toUnit (Over.mk t)) := Over.epi_of_epi_left _
  exact (cancel_epi _).1 h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem ev_add_smul {D : Datum H} {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (I : TateIso D k Q act e) {n : ℕ} (hn : 0 < n) (a c : D.La) :
    I.ev n (a + n • c) = I.ev n a := by
  rw [I.add, (I.ker n hn _).2 ⟨c, rfl⟩, _root_.mul_one]

theorem exists_eq_nsmul (D : Datum H) (l : Level H) {J J' : Ideal (𝓞 E)}
    (hJ : J * J' = Ideal.span {(l.M : 𝓞 E)}) {e : 𝓞 E} (he : e ∈ J) {a : D.La}
    (ha : a ∈ J' • (⊤ : Submodule (𝓞 E) D.La)) : ∃ c, e • a = l.M • c := by
  have h1 : e • a ∈ (J * J') • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul he ha
  rw [hJ, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨c, -, hc⟩ := h1
  exact ⟨c, by rw [← hc, Nat.cast_smul_eq_nsmul]⟩

end GlobalTheory.CM.RationalTorsion
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTensorProductHomOfCmCurveHomFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTensorProductHomOfCmCurveHomFamily
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.CM

theorem IsKForm.map_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D₁ D : Datum H} {ε : ℤˣ}
    {h₁ : D₁.La → D₁.La → OK H} {h : D.La → D.La → OK H} (k₁ : IsKForm D₁ ε h₁) (k : IsKForm D ε h)
    {L : Submodule (𝓞 E) D.La} (f : D₁.La →ₗ[𝓞 E] L) (c : 𝓞 E) (hf : ∀ a b, D.EF (f a) (f b) = D₁.EF (c • a) b)
    (a b : D₁.La) : h (f a) (f b) = h₁ (c • a) b := by
  apply Subtype.ext
  have e : H.w0 • ((f a : L) : D.La) = ((f (H.w0 • a) : L) : D.La) := by rw [map_smul]; rfl
  rw [k, k₁, e, hf, hf, smul_comm c H.w0 a]

theorem exists_famLift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (D₁ D : Datum H) (ε : ℤˣ) (h₁ : D₁.La → D₁.La → OK H) (h : D.La → D.La → OK H) (T₁ T : PAT H (Sp R)) (t : IsTen C D₁ h₁ T₁) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)) (f : D₁.La →ₗ[𝓞 E] L) (c : 𝓞 E), IsKForm D₁ ε h₁ → IsKForm D ε h → (∀ a b, D.EF (f a) (f b) = D₁.EF (c • a) b) → IsFam C T h L ψ →
  ∃ Φ : T₁.t.G ⟶ T.t.G, Serre.IsLinearHom T₁.t.act T.t.act Φ ∧ (∀ a, t.ten.tmul a ≫ Φ = ψ (f a)) ∧ LamEq T.t.PP.L Φ Φ T₁.t.PP.L (T₁.t.act.act c) (𝟙 T₁.t.G) := by
  intro E _ _ _ H R _ ω C D₁ D ε h₁ h T₁ T t L ψ f c k₁ k hf ⟨l, hadd, hsmul, hlam⟩
  let F : D₁.La →ₗ[OK H] Serre.Pts (Serre.comapAct T.t.act (algebraMap (OK H) (𝓞 E))) C.P.A :=
    { toFun := fun a => Serre.Pts.mk _ (ψ (f a))
      map_add' := fun a b => Serre.Pts.ext (by rw [map_add (f := _)]; exact hadd _ _)
      map_smul' := fun s a => Serre.Pts.ext (by
        have e : f (s • a) = (s : 𝓞 E) • f a := f.map_smul (s : 𝓞 E) a
        rw [e]; exact hsmul _ _) }
  have hF : ∀ a, Serre.IsLinearHom C.act (Serre.comapAct T.t.act (algebraMap (OK H) (𝓞 E))) (F a).hom :=
    fun a => l (f a)
  have hm : IsMonHom (t.ten.lift F hF) := (t.ten.isLinearHom_lift F hF).isMonHom
  have ht : ∀ a, t.ten.tmul a ≫ t.ten.lift F hF = ψ (f a) := fun a => t.ten.tmul_lift F hF a
  refine ⟨t.ten.lift F hF, ⟨hm, fun s => ?_⟩, ht, ?_⟩
  · have := T₁.t.act.hom s
    have := T.t.act.hom s
    refine t.ten.hom_ext fun a => ?_
    rw [← Category.assoc, ← t.lin, ht, ← Category.assoc, ht, map_smul, hsmul]
  · refine GlobalTheory.T.tensor_pairing_identity_of_pure_tensors _ _ _ _ _ _ _ t.ten _ _ _ t.ten _ _ _ _ _ _ _ _ T.t.PP.isLB T₁.t.PP.isLB
      ⟨T.t.cub.t, T.t.cub.isGen⟩ ⟨T₁.t.cub.t, T₁.t.cub.isGen⟩ hm hm (T₁.t.act.hom c) inferInstance fun a b => ?_
    rw [ht, ht, ← t.lin, Category.comp_id]
    have e := hlam (f a) (f b)
    rw [k₁.map_eq k f c hf] at e
    exact LBIso.trans (LamCalc.cubeLB_isLB T.t.PP.isLB _) (LamCalc.cubeLB_isLB C.P.isLB _)
      (LamCalc.cubeLB_isLB T₁.t.PP.isLB _) e (LBIso.symm (t.lam (c • a) b))

end GlobalTheory.CM
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsTensorProductHomOfCmCurveHomFamilyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensorProduct_hom_of_cmCurveHomFamily : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] (ω : R) (C : Ell H R ω) (D₁ D : Datum H) (ε : ℤˣ) (h₁ : D₁.La → D₁.La → OK H) (h : D.La → D.La → OK H) (T₁ T : PAT H (Sp R)) (t : IsTen C D₁ h₁ T₁) (L : Submodule (𝓞 E) D.La) (ψ : L → (C.P.A ⟶ T.t.G)) (f : D₁.La →ₗ[𝓞 E] L) (c : 𝓞 E), IsKForm D₁ ε h₁ → IsKForm D ε h → (∀ a b, D.EF (f a) (f b) = D₁.EF (c • a) b) → IsFam C T h L ψ →
  ∃ Φ : T₁.t.G ⟶ T.t.G, Serre.IsLinearHom T₁.t.act T.t.act Φ ∧ (∀ a, t.ten.tmul a ≫ Φ = ψ (f a)) ∧ LamEq T.t.PP.L Φ Φ T₁.t.PP.L (T₁.t.act.act c) (𝟙 T₁.t.G) := by
  first | exact @GlobalTheory.CM.exists_famLift | exact GlobalTheory.CM.exists_famLift | (intros; apply GlobalTheory.CM.exists_famLift <;> assumption)
end
end
