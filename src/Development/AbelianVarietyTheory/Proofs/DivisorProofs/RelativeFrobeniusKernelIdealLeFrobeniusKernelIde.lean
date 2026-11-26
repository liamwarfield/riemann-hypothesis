module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleRigidFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionTowerPresentationCotangentPullbackResRigi
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsNefPullLLStepEx
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonHomOverAlgebraicClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMultiplierIntegralImaginary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReferenceCoreOfSumPoint
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTraitNonlocalTorusExtensionStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFrobeniusKernelIdealLeFrobeniusKernelIde
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFrobeniusKernelIdealLeFrobeniusKernelIde
set_option autoImplicit false

noncomputable section

open Coalgebra Bialgebra

namespace GlobalTheory.PDiv

open GlobalTheory.PDivGroup

theorem pow_sub_counit_mem_frobKerIdeal {p : ℕ} [Fact p.Prime] {R H : Type} [CommRing R]
    [CommRing H] [Bialgebra R H] (h : (p : R) = 0) (a : H) :
    a ^ p - algebraMap R H (counit (R := R) (a ^ p)) ∈ frobKerIdeal p R H := by
  have h0 := natCast_eq_zero_of_algebra h H
  have e : a ^ p - algebraMap R H (counit (R := R) (a ^ p)) =
      (a - algebraMap R H (counit (R := R) a)) ^ p := by
    rw [← frobRing_apply h0 (a - _), map_sub, frobRing_apply, frobRing_apply, counit_pow, map_pow]
  rw [e]
  exact pow_mem_frobKerIdeal (by simp [RingHom.mem_ker])

theorem kerIdeal_relFrob_le_frobKerIdeal (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (h : (p : R) = 0) (G : PDivGroup p R) (n : ℕ) :
    kerIdeal ((relFrob h G).app n) ≤ frobKerIdeal p R (G.A n) := by
  have key : ∀ x : (frobTwist h G).A n, (relFrob h G).app n x -
      algebraMap R (G.A n) (counit (R := R) ((relFrob h G).app n x)) ∈
        frobKerIdeal p R (G.A n) := by
    intro x
    induction x using frobTwist_induction h n with
    | h0 => simp
    | h1 r a =>
      rw [map_smul, relFrob_app_frobProj, map_smul, smul_eq_mul, map_mul, Algebra.smul_def,
        ← mul_sub]
      exact Ideal.mul_mem_left _ _ (pow_sub_counit_mem_frobKerIdeal h a)
    | h2 x y hx hy =>
      rw [map_add (f := _), map_add (f := _), map_add (f := _), add_sub_add_comm]
      exact add_mem hx hy
  refine Ideal.map_le_iff_le_comap.2 fun x hx => ?_
  have hx' : counit (R := R) x = 0 := hx
  have := key x
  rw [CoalgHomClass.counit_comp_apply, hx', map_zero, sub_zero] at this
  exact this

end GlobalTheory.PDiv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativeFrobeniusKernelIdealLeFrobeniusKernelIdeStatement
open GlobalTheory GlobalTheory.PDiv

theorem _root_.GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (h : (p : R) = 0)
    (G : PDivGroup p R) (n : ℕ) :
    kerIdeal ((PDivGroup.relFrob h G).app n) ≤ frobKerIdeal p R (G.A n) :=
  kerIdeal_relFrob_le_frobKerIdeal p R h G n
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusEmbeddingClosedAllFibres
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.CovTop GlobalTheory.CovHt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusFibreImm

set_option backward.isDefEq.respectTransparency.types false

theorem isPullback_pullback_map {S S' : Scheme.{0}} (a : S' ⟶ S) {X Y : Over S} (v : X ⟶ Y) :
    IsPullback ((Over.pullback a).map v).left (pullback.fst X.hom a) (pullback.fst Y.hom a) v.left := by
  have h1 : ((Over.pullback a).map v).left ≫ pullback.fst Y.hom a = pullback.fst X.hom a ≫ v.left :=
    pullback.lift_fst _ _ _
  have h2 : ((Over.pullback a).map v).left ≫ pullback.snd Y.hom a = pullback.snd X.hom a :=
    Over.w ((Over.pullback a).map v)
  refine IsPullback.of_right ?_ h1 (IsPullback.of_hasPullback Y.hom a).flip
  have h := (IsPullback.of_hasPullback X.hom a).flip
  rw [h2, Over.w v]
  exact h

theorem closedImm_comp_iff {S S' S'' : Scheme.{0}} (b : S'' ⟶ S') (a : S' ⟶ S) {X Y : Over S} (v : X ⟶ Y) :
    IsClosedImmersion ((Over.pullback (b ≫ a)).map v).left ↔
      IsClosedImmersion ((Over.pullback b).map ((Over.pullback a).map v)).left := by
  let e := Over.pullbackComp b a
  exact MorphismProperty.arrow_mk_iso_iff @IsClosedImmersion
    (Arrow.isoMk ((Over.forget _).mapIso (e.app X)) ((Over.forget _).mapIso (e.app Y))
      (congrArg (·.left) (e.hom.naturality v).symm))

theorem closedImm_pullback {S S' : Scheme.{0}} (a : S' ⟶ S) {X Y : Over S} (v : X ⟶ Y)
    (h : IsClosedImmersion v.left) : IsClosedImmersion ((Over.pullback a).map v).left :=
  MorphismProperty.of_isPullback (P := @IsClosedImmersion) (isPullback_pullback_map a v).flip h

theorem closedImm_of_pullback {k Ω : CommRingCat.{0}} (hk : IsField k) (hΩ : IsField Ω) (φ : k ⟶ Ω)
    {X Y : Over (Spec k)} (v : X ⟶ Y)
    (h : IsClosedImmersion ((Over.pullback (Spec.map φ)).map v).left) : IsClosedImmersion v.left := by
  letI := hk.toField
  letI := hΩ.toField
  letI := φ.hom.toAlgebra
  have hd := GlobalTheory.ClosedImmFieldDescent.isClosedImmersion_descendsAlong_fpqc
  have hq : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) (Spec.map φ) :=
    GlobalTheory.ClosedImmFieldDescent.fpqc_specMap_field k Ω
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := @IsClosedImmersion)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (isPullback_pullback_map _ v)
    (MorphismProperty.of_isPullback (P := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      (IsPullback.of_hasPullback Y.hom (Spec.map φ)).flip hq) h

theorem closedImm_iff_residue {W : Scheme.{0}} {X Y : Over W} (v : X ⟶ Y) (k : Type) [Field k] (w : Sp k ⟶ W) :
    IsClosedImmersion ((Over.pullback w).map v).left ↔
      IsClosedImmersion ((Over.pullback (W.fromSpecResidueField (w (IsLocalRing.closedPoint k)))).map v).left := by
  conv_lhs => rw [← Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k W w]
  rw [closedImm_comp_iff]
  exact ⟨closedImm_of_pullback (Field.toIsField _) (Field.toIsField _) _ _, closedImm_pullback _ _⟩

end GlobalTheory.TorusFibreImm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondencePeriod
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondencePeriod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem gtRelV_io : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ y' : N'.X, GtRelV W φ e wv (N'.io y') (fun j => N.io (e y' j)) := by
  intro F _ N N' r W φ e wv hT y'
  obtain ⟨-, -, he_add, -, hc, hw0, -, hψ⟩ := hT
  refine ⟨fun j => hc y' j, fun χ' => ?_⟩
  simp only [NumD.io_s, NumD.io_b]
  let U : N'.A → Fˣ := fun x => Units.mk0 (wv x) (hw0 x)
  have hU : ∀ x, wv x = (U x : F) := fun x => rfl
  let P : N'.X → Fˣ := fun a => ∏ i, ∏ j, N.τ (e a i) (e a j) ^ W i j
  have hψ' : ∀ a, N'.ψ a * U 1 = U (N'.c a) * P a := fun a => Units.ext (by
    simp only [Units.val_mul, U, Units.val_mk0, P]; exact hψ a)
  have key : ∀ i j, N.τ (e y' j) (e χ' i) * N.τ (e y' i) (e χ' j) /
      (N.θ (N.c (e χ' j)) (N.c (e y' j)) (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (N.c (e y' j)) (N.c (e y' i)) *
        N.θ (N.c (e χ' i)) (N.c (e y' i)) (N.c (e χ' j) * N.c (e y' j))) =
      N.τ (e (y' + χ') i) (e (y' + χ') j) / N.τ (e y' i) (e y' j) / N.τ (e χ' i) (e χ' j) := by
    intro i j
    rw [he_add y' χ' i, he_add y' χ' j, add_comm (e y' i), add_comm (e y' j)]
    have h1 := N.τ_add_left (e χ' i) (e y' i) (e χ' j + e y' j)
    rw [N.c_add] at h1
    have h2 := N.τ_add_right (e χ' i) (e χ' j) (e y' j)
    have h3 := N.τ_add_right (e y' i) (e χ' j) (e y' j)
    have h4 := N.τ_symm (e y' j) (e χ' i)
    replace h1 := congrArg Additive.ofMul h1
    replace h2 := congrArg Additive.ofMul h2
    replace h3 := congrArg Additive.ofMul h3
    replace h4 := congrArg Additive.ofMul h4
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at h1 h2 h3 h4 ⊢
    linear_combination (norm := abel) h4 - h1 - h2 - h3
  have hQ : (∏ i, ∏ j, (N.τ (e y' j) (e χ' i) * N.τ (e y' i) (e χ' j) /
      (N.θ (N.c (e χ' j)) (N.c (e y' j)) (N.c (e χ' i)) * N.θ (N.c (e χ' j)) (N.c (e y' j)) (N.c (e y' i)) *
        N.θ (N.c (e χ' i)) (N.c (e y' i)) (N.c (e χ' j) * N.c (e y' j)))) ^ W i j : Fˣ) =
      P (y' + χ') / P y' / P χ' := by
    simp only [key, div_zpow, Finset.prod_div_distrib, P]
  rw [hQ, hU, hU, hU, hU]
  have hS := hψ' (y' + χ')
  rw [N'.c_add y' χ', mul_comm (N'.c y')] at hS
  have hy := hψ' y'
  have hx := hψ' χ'
  have E : N'.τ y' χ' * U (N'.c χ') * U (N'.c y') = P (y' + χ') / P y' / P χ' * U (N'.c χ' * N'.c y') * U 1 := by
    simp only [NumD.τ]
    replace hS := congrArg Additive.ofMul hS
    replace hy := congrArg Additive.ofMul hy
    replace hx := congrArg Additive.ofMul hx
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at hS hy hx ⊢
    linear_combination (norm := abel) hS - hy - hx
  have := congrArg Units.val E
  simpa only [Units.val_mul] using this

end GlobalTheory.Mum.TensTor
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondencePeriodStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorTorusValueCorrespondence_period : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → ∀ y' : N'.X, GtRelV W φ e wv (N'.io y') (fun j => N.io (e y' j)) := by
  first | exact @GlobalTheory.Mum.TensTor.gtRelV_io | exact GlobalTheory.Mum.TensTor.gtRelV_io | (intros; apply GlobalTheory.Mum.TensTor.gtRelV_io <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricTwoCocycleOfAdditiveStructureTorsor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricTwoCocycleOfAdditiveStructureTorsor
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem isSymCoc_of_isAdd : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (f : Fn1 A) (g : Fn2 A), IsAdd f g → IsSymCoc g := by
  intro R _ A _ hA f g hfg
  have hc : IsCommMonObj A := hA.comm
  unfold IsSymCoc
  unfold IsAdd at hfg
  intro D _ _
  constructor
  · let k : Fn0 (A ⊗ A) := fun E _ _ w ↦
      g E (w ≫ fst A A) (w ≫ snd A A) - g E (w ≫ snd A A) (w ≫ fst A A)
    have hk : IsCob (whole (A ⊗ A)) (Fn1.zero (A ⊗ A)) k := by
      unfold IsCob
      intro E _ _ E' _ _ φ w _
      have h1 := hfg E E' φ (w ≫ fst A A) (w ≫ snd A A)
      have h2 := hfg E E' φ (w ≫ snd A A) (w ≫ fst A A)
      rw [mul_comm (w ≫ snd A A) (w ≫ fst A A)] at h2
      simp only [k, Fn1.zero, Category.assoc, map_sub]
      linear_combination h2 - h1
    obtain ⟨r, hr⟩ := GlobalTheory.T.natural_pointwiseCochain_const_of_globalSections_base R (A ⊗ A) Unit (whole (A ⊗ A)) (by simp [whole])
      (GlobalTheory.globalFns_holds (Sp R) (A ⊗ A)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA)).2 k hk
    intro x y
    have e1 := hr D (lift x y) (sm_whole _)
    have e0 := hr D (lift 1 1) (sm_whole _)
    simp only [k, lift_fst, lift_snd, sub_self] at e0 e1
    exact sub_eq_zero.mp (e1.trans e0.symm)
  · let k : Fn0 (A ⊗ (A ⊗ A)) := fun E _ _ w ↦
      g E (w ≫ snd _ _ ≫ fst A A) (w ≫ snd _ _ ≫ snd A A)
        - g E ((w ≫ fst _ _) * (w ≫ snd _ _ ≫ fst A A)) (w ≫ snd _ _ ≫ snd A A)
        + g E (w ≫ fst _ _) ((w ≫ snd _ _ ≫ fst A A) * (w ≫ snd _ _ ≫ snd A A))
        - g E (w ≫ fst _ _) (w ≫ snd _ _ ≫ fst A A)
    have hk : IsCob (whole (A ⊗ (A ⊗ A))) (Fn1.zero _) k := by
      unfold IsCob
      intro E _ _ E' _ _ φ w _
      have h1 := hfg E E' φ (w ≫ snd _ _ ≫ fst A A) (w ≫ snd _ _ ≫ snd A A)
      have h2 := hfg E E' φ ((w ≫ fst _ _) * (w ≫ snd _ _ ≫ fst A A)) (w ≫ snd _ _ ≫ snd A A)
      have h3 := hfg E E' φ (w ≫ fst _ _) ((w ≫ snd _ _ ≫ fst A A) * (w ≫ snd _ _ ≫ snd A A))
      have h4 := hfg E E' φ (w ≫ fst _ _) (w ≫ snd _ _ ≫ fst A A)
      rw [_root_.mul_assoc] at h2
      simp only [MonObj.comp_mul] at h2 h3
      simp only [k, Fn1.zero, Category.assoc, map_sub, map_add (f := _), MonObj.comp_mul]
      linear_combination h2 - h1 - h3 + h4
    obtain ⟨r, hr⟩ := GlobalTheory.T.natural_pointwiseCochain_const_of_globalSections_base R (A ⊗ (A ⊗ A)) Unit (whole _) (by simp [whole])
      (GlobalTheory.globalFns_holds (Sp R) (A ⊗ (A ⊗ A))
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A (A ⊗ A) hA
          (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA))).2 k hk
    intro x y z
    have e1 := hr D (lift x (lift y z)) (sm_whole _)
    have e0 := hr D (lift 1 (lift 1 1)) (sm_whole _)
    simp only [k, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, _root_.mul_one, sub_self, add_sub_cancel_right,
      sub_add_cancel] at e0 e1
    rw [← e0] at e1
    exact e1

end GlobalTheory.PtExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricTwoCocycleOfAdditiveStructureTorsorStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSymmetricTwoCocycle_of_additiveStructure_torsor : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → ∀ (f : Fn1 A) (g : Fn2 A), IsAdd f g → IsSymCoc g := by
  first | exact @GlobalTheory.PtExt.isSymCoc_of_isAdd | exact GlobalTheory.PtExt.isSymCoc_of_isAdd | (intros; apply GlobalTheory.PtExt.isSymCoc_of_isAdd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyHomDescendsAlgClosedCharZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyHomDescendsAlgClosedCharZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.AlgClosedHomDescent

theorem hom_descends : ∀ (K Ω : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field Ω] (j : K →+* Ω) (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'] (B B' : Over (Sp Ω)) [GrpObj B] [GrpObj B'] (b : B.left ⟶ A.left) (b' : B'.left ⟶ A'.left), IsAbelianScheme A → IsAbelianScheme A' → IsGrpPullback B A (spMap j) b → IsGrpPullback B' A' (spMap j) b' → ∀ f : B ⟶ B', IsMonHom f → ∃ f₀ : A ⟶ A', IsMonHom f₀ ∧ b ≫ f₀.left = f.left ≫ b' := by
  intro K Ω _ _ _ _ j A A' _ _ B B' _ _ b b' hA hA' hB hB' f hf
  let Ωb := AlgebraicClosure Ω
  let io : Ω →+* Ωb := algebraMap Ω Ωb
  letI : Algebra K Ωb := (io.comp j).toAlgebra
  have hJ : spMap io ≫ spMap j = spMap (algebraMap K Ωb) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

  let P := (Over.pullback (spMap (algebraMap K Ωb))).obj A
  let P' := (Over.pullback (spMap (algebraMap K Ωb))).obj A'
  have hP : IsGrpPullback P A (spMap (algebraMap K Ωb)) (pullback.fst _ _) := isGrpPullback_pullback A _
  have hP' : IsGrpPullback P' A' (spMap (algebraMap K Ωb)) (pullback.fst _ _) := isGrpPullback_pullback A' _

  let u : P.left ⟶ B.left := hB.1.lift (pullback.fst A.hom _) (pullback.snd A.hom _ ≫ spMap io)
    (by rw [pullback.condition, Category.assoc, hJ])
  let u' : P'.left ⟶ B'.left := hB'.1.lift (pullback.fst A'.hom _) (pullback.snd A'.hom _ ≫ spMap io)
    (by rw [pullback.condition, Category.assoc, hJ])
  have hu₁ : u ≫ b = pullback.fst A.hom _ := hB.1.lift_fst _ _ _
  have hu₂ : u ≫ B.hom = P.hom ≫ spMap io := hB.1.lift_snd _ _ _
  have hu₁' : u' ≫ b' = pullback.fst A'.hom _ := hB'.1.lift_fst _ _ _
  have hu₂' : u' ≫ B'.hom = P'.hom ≫ spMap io := hB'.1.lift_snd _ _ _
  have hPB : IsGrpPullback P B (spMap io) u :=
    hB.cancel (hP.congr hJ.symm hu₁.symm) hu₂
  have hPB' : IsGrpPullback P' B' (spMap io) u' :=
    hB'.cancel (hP'.congr hJ.symm hu₁'.symm) hu₂'

  let fb : P ⟶ P' := Over.homMk (pullback.lift (u ≫ f.left ≫ b') (pullback.snd A.hom _) (by
      rw [Category.assoc, Category.assoc, hB'.1.w, ← Category.assoc f.left, Over.w f, ← Category.assoc, hu₂,
        Category.assoc, hJ]; rfl))
    (pullback.lift_snd _ _ _)
  have hfb₁ : fb.left ≫ pullback.fst A'.hom _ = u ≫ f.left ≫ b' := pullback.lift_fst _ _ _
  have hfb₂ : fb.left ≫ P'.hom = P.hom := Over.w fb
  have hfbu : u ≫ f.left = fb.left ≫ u' := by
    apply hB'.1.hom_ext
    · rw [Category.assoc, Category.assoc, hu₁', hfb₁]
    · rw [Category.assoc, Over.w f, hu₂, Category.assoc, hu₂', ← Category.assoc, hfb₂]
  have hfbm : IsMonHom fb :=
    ((GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff Ω Ωb io).2 B B' P P' u u' f fb hPB hPB' hfbu).2 hf

  obtain ⟨g, hg, hge⟩ := GlobalTheory.T.exists_mon_hom_over_algebraic_closure K Ωb A A' hA hA' fb hfbm
  let L := algebraicClosure K Ωb
  have hbij : Function.Bijective (algebraMap K L) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  haveI : IsIso (CommRingCat.ofHom (algebraMap K L)) := (ConcreteCategory.isIso_iff_bijective _).2 hbij
  haveI : IsIso (spMap (algebraMap K L)) := by unfold spMap; infer_instance
  let q := pullback.fst A.hom (spMap (algebraMap K L))
  let q' := pullback.fst A'.hom (spMap (algebraMap K L))

  let f₀ : A ⟶ A' := Over.homMk (inv q ≫ g.left ≫ q') (by
    have hg' : g.left ≫ pullback.snd A'.hom (spMap (algebraMap K L)) = pullback.snd A.hom _ := Over.w g
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc g.left, hg', ← pullback.condition,
      IsIso.inv_hom_id_assoc])
  have hq : q ≫ f₀.left = g.left ≫ q' := by
    show q ≫ inv q ≫ g.left ≫ q' = _
    rw [IsIso.hom_inv_id_assoc]
  have hf₀ : IsMonHom f₀ :=
    ((GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K L (algebraMap K L)).2 A A' _ _ q q' f₀ g
      (isGrpPullback_pullback A _) (isGrpPullback_pullback A' _) hq).1 hg
  refine ⟨f₀, hf₀, ?_⟩
  have hepi : Epi u := ((GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff Ω Ωb io).1 B.left P.left B.hom P.hom u hPB.1).1
  rw [← cancel_epi u, ← Category.assoc, hu₁, ← GlobalTheory.Spread.bcMap_fst A.hom L.val, Category.assoc, hq, hge, hfb₁]

end GlobalTheory.AlgClosedHomDescent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyHomDescendsAlgClosedCharZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_hom_descends_algClosed_charZero : ∀ (K Ω : Type) [Field K] [IsAlgClosed K] [CharZero K] [Field Ω] (j : K →+* Ω) (A A' : Over (Sp K)) [GrpObj A] [GrpObj A'] (B B' : Over (Sp Ω)) [GrpObj B] [GrpObj B'] (b : B.left ⟶ A.left) (b' : B'.left ⟶ A'.left), IsAbelianScheme A → IsAbelianScheme A' → IsGrpPullback B A (spMap j) b → IsGrpPullback B' A' (spMap j) b' → ∀ f : B ⟶ B', IsMonHom f → ∃ f₀ : A ⟶ A', IsMonHom f₀ ∧ b ≫ f₀.left = f.left ≫ b' := by
  first | exact @GlobalTheory.AlgClosedHomDescent.hom_descends | exact GlobalTheory.AlgClosedHomDescent.hom_descends | (intros; apply GlobalTheory.AlgClosedHomDescent.hom_descends <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLabelsSurjectiveKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLabelsSurjectiveKernel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

theorem uIsLab_onto_and_ker : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X), UIsLab X ct yy → Function.Surjective yy ∧ yy.ker = X.S.HH X.M z := by
  intro E _ _ _ H Dw _ l Xo cf C X p _ z ct yy hl
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', -, -, -, hR', G, _, α, β, -, -, -, y₀, hy₀, u, lb, j, -, hyy, -⟩ := hl
  refine ⟨?_, ?_⟩
  · intro m
    obtain ⟨χ', rfl⟩ := QuotientAddGroup.mk_surjective m
    obtain ⟨a, ha⟩ := lb.yy_onto (QuotientAddGroup.mk (j.symm χ'))
    exact ⟨a, by rw [hyy a _ ha, j.apply_symm_apply]⟩
  have hker : yy.ker = lb.yy.ker := by
    ext a
    simp only [AddMonoidHom.mem_ker]
    obtain ⟨χ, hχ⟩ := QuotientAddGroup.mk_surjective (lb.yy a)
    rw [hyy a χ hχ.symm, ← hχ, QuotientAddGroup.eq_zero_iff, QuotientAddGroup.eq_zero_iff]
    constructor
    · rintro ⟨v, hv⟩
      refine ⟨j.symm v, ?_⟩
      simp only [nsmulAddMonoidHom_apply] at hv ⊢
      rw [← map_nsmul, hv, j.symm_apply_apply]
    · rintro ⟨v, hv⟩
      refine ⟨j v, ?_⟩
      simp only [nsmulAddMonoidHom_apply] at hv ⊢
      rw [← map_nsmul, hv]
  have hint : ∀ a : X.o₁, ‖y₀ (algebraMap X.o₁ R' a)‖ ≤ 1 := fun a => by
    rw [hy₀]
    exact RatModel.norm_val_le_one ct.cen ((X.M.O z).algebraMap_mem a)
  have hcl := GlobalTheory.UnitTheta.closure_unit_theta GlobalTheory.abelianSchemeLaws_all.1 GlobalTheory.abelianSchemeLaws_all.2
    GlobalTheory.ZH.uTors_closed _ _ _ ρ' p y₀ u lb hint
  rw [hker, ← hcl.2]
  obtain ⟨x₀, hx₀⟩ := X.hasDiv z
  set val := X.M.val (gPt p ≫ ct.y) with hval
  have hsp : ∀ w, (gPt p ≫ ct.y) w ⤳ (gPt p ≫ ct.y) (IsLocalRing.closedPoint (PadicAlgCl p)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)
  have hgz : (gPt p ≫ ct.y) (IsLocalRing.closedPoint (PadicAlgCl p)) ⤳ z :=
    RatModel.gPt_specializes ct.cen _
  have hy : ∀ x, y₀ ⟨c₀ * X.S.th x, hth x⟩ = val (c₀ * X.S.th x) := fun x => hy₀ _
  have hmul : ∀ x, ‖val (c₀ * X.S.th x)‖ = ‖val (X.S.th x / X.S.th x₀)‖ * ‖val (c₀ * X.S.th x₀)‖ := by
    intro x
    rw [← norm_mul, hval, ← RatModel.val_mul hsp (RatModel.O_le_of_specializes hgz (hx₀.2 x)) (hR' (hth x₀))]
    congr 2
    have := hx₀.1
    field_simp
  have hδ : ‖val (c₀ * X.S.th x₀)‖ = (X.S.rechart c₀ hc R' fg frac hth hev).delta y₀ := by
    apply le_antisymm
    · rw [← hy]
      exact le_ciSup (f := fun x => ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖) (Set.finite_range _).bddAbove x₀
    · obtain ⟨x₁, hx₁⟩ := exists_eq_ciSup_of_finite (f := fun x => ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖)
      change ⨆ x, ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖ ≤ _
      rw [← hx₁, hy, hmul x₁]
      exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.norm_val_le_one ct.cen (hx₀.2 x₁))
  have key : ∀ x, x ∈ X.S.supI X.M z ↔
      ‖y₀ ⟨c₀ * X.S.th x, hth x⟩‖ = (X.S.rechart c₀ hc R' fg frac hth hev).delta y₀ := by
    intro x
    change X.M.Div X.S.th x z ↔ _
    rw [hx₀.div_iff_isUnit x, ← RatModel.norm_val_eq_one_iff ct.cen (hx₀.2 x), hy, hmul x, hδ]
    exact (mul_eq_right₀ hcl.1.ne').symm
  rw [ThetaSys.HH]
  congr 1
  ext x
  exact (key x).symm

end GlobalTheory.UPoinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLabelsSurjectiveKernelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryTraitLabels_surjective_kernel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X : USetup C) (p : ℕ) [Fact p.Prime] (z : X.M.Z) (ct : UCTrait X p z) (yy : X.S.Gam →+ ModN (X.S.r * X.S.N) ct.T.P.D.toPre.X), UIsLab X ct yy → Function.Surjective yy ∧ yy.ker = X.S.HH X.M z := by
  first | exact @GlobalTheory.UPoinc.uIsLab_onto_and_ker | exact GlobalTheory.UPoinc.uIsLab_onto_and_ker | (intros; apply GlobalTheory.UPoinc.uIsLab_onto_and_ker <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverLiftThroughNormal
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
open CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Mean4O.NormCoverFin

theorem isDominant_j {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) : IsDominant V.j := by
  have : Flat (spMap (algebraMap (𝓞 F) F)) := flat_specMap_localization (nonZeroDivisors (𝓞 F)) F
  have : Flat V.j := MorphismProperty.of_isPullback V.pb.flip ‹_›
  refine ⟨?_⟩
  obtain ⟨x⟩ : Nonempty V.G := inferInstance
  have h0 : genericPoint V.X ∈ Set.range V.j :=
    (Flat.generalizingMap V.j).stableUnderGeneralization_range (genericPoint_specializes (V.j x)) ⟨x, rfl⟩
  have h2 : closure ({genericPoint V.X} : Set V.X) ⊆ closure (Set.range V.j) :=
    closure_mono (Set.singleton_subset_iff.2 h0)
  rw [show closure ({genericPoint V.X} : Set V.X) = Set.univ from genericPoint_spec V.X] at h2
  exact dense_iff_closure_eq.2 (Set.eq_univ_of_univ_subset h2)

theorem exists_cover : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V V₂ : Mean4O.Cover Y) (G : Scheme.{0})
    [IsIntegral G] [GlobalTheory.IsNormalScheme G] (g : G ⟶ V.G) [IsFinite g] [IsDominant g] (k : G ⟶ V₂.G),
    k ≫ V₂.π = g ≫ V.π →
    ∃ (W : Mean4O.Cover Y) (a : W.X ⟶ V.X) (k' : W.G ⟶ V₂.G), a ≫ V.p = W.p ∧ Lies W V a ∧ k' ≫ V₂.π = W.π := by
  intro F _ _ Y V V₂ G _ _ g _ _ k hk
  have := V.ar.isLocallyNoetherian
  have : IsProper V.p := CommonModel.isProper_of_isProjOver V.ar.isProjOver
  have : Flat (spMap (algebraMap (𝓞 F) F)) := flat_specMap_localization (nonZeroDivisors (𝓞 F)) F
  have : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := 𝓞 F) (S := F) (nonZeroDivisors (𝓞 F))
  have : IsAffineHom V.j := MorphismProperty.of_isPullback V.pb.flip (isAffineHom_of_isAffine _)
  have : IsDominant V.j := isDominant_j V
  let h : G ⟶ V.X := g ≫ V.j
  have hh : h = g ≫ 𝟙 _ ≫ V.j := by simp [h]
  have hpb := GlobalTheory.isPullback_toNormalization_of_isLocalization (nonZeroDivisors (𝓞 F)) V.pb g (𝟙 _) h hh
  rw [Category.id_comp] at hpb
  have w : h ≫ V.p = (g ≫ V.π ≫ Y.str) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [h, Category.assoc, V.pb.w]
  have hfin : IsFinite h.fromNormalization :=
    GlobalTheory.isFinite_fromNormalization_of_over_fractionRing (o := .of (𝓞 F)) h V.p F (g ≫ V.π ≫ Y.str) w
  have : GlobalTheory.IsNormalScheme h.normalization := GlobalTheory.IsNormalScheme.normalization_of_isIntegral h
  have hint : IsIntegral h.normalization := inferInstance
  have : IsDominant h.fromNormalization := by
    have : IsDominant (h.toNormalization ≫ h.fromNormalization) := by
      rw [Scheme.Hom.toNormalization_fromNormalization]; infer_instance
    exact IsDominant.of_comp h.toNormalization h.fromNormalization
  have hs : Surjective h.fromNormalization :=
    surjective_of_isDominant_of_isClosed_range _ h.fromNormalization.isClosedMap.isClosed_range
  have hdim : topologicalKrullDim h.normalization = (Y.dim + 1 : ℕ) := by
    rw [← V.ar.dim_eq]
    refine le_antisymm (ProperCover.dim_le_of_residueDegree_pos h.fromNormalization
      (apply_genericPoint_of_isDominant h.fromNormalization) ?_)
      (PosBaseChange.dim_le_of_isClosedMap h.fromNormalization.isClosedMap hs.surj)
    let := (h.fromNormalization.residueFieldMap (genericPoint h.normalization)).hom.toAlgebra
    have : Module.Finite (V.X.residueField (h.fromNormalization (genericPoint h.normalization)))
        (h.normalization.residueField (genericPoint h.normalization)) :=
      residueFieldMap_finite_of_locallyQuasiFinite h.fromNormalization _
    exact Module.finrank_pos
  have hfl : Flat (h.fromNormalization ≫ V.p) :=
    GlobalTheory.flat_fromNormalization_comp h F V.p (g ≫ V.π ≫ Y.str) w
  have hfZ : Flat (spMap (Int.castRingHom (𝓞 F))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat ℤ (𝓞 F))
  have : Surjective g := surjective_of_isDominant_of_isClosed_range _ g.isClosedMap.isClosed_range
  have hη : (g ≫ V.π) (genericPoint G) ⤳ genericPoint Y.X :=
    specializes_of_eq (apply_genericPoint_of_isDominant (g ≫ V.π))
  let W : Cover Y :=
    { X := h.normalization
      p := h.fromNormalization ≫ V.p
      ar := ⟨V.ar.isDomain, V.ar.finite, hint, GlobalTheory.isProjOver_comp_of_finite _ _ _ _ _ hfin V.ar.isProjOver,
        inferInstance, hdim⟩
      normal := GlobalTheory.IsNormalScheme.pred _
      G := G
      j := h.toNormalization
      π := g ≫ V.π
      pb := by simpa [Category.assoc] using hpb.paste_vert V.pb
      φ := SmallSec.fnMap (g ≫ V.π) hη
      φ_spec := by
        change _ = Spec.map (Y.X.presheaf.stalkSpecializes hη ≫ (g ≫ V.π).stalkMap _) ≫ _
        rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
          Scheme.SpecMap_stalkMap_fromSpecStalk] }
  exact ⟨W, h.fromNormalization, k, rfl, ⟨g, by simp [W, h], rfl⟩, hk⟩

end GlobalTheory.Mean4O.NormCoverFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomSpecPointsLevels
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomSpecPointsLevels
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

theorem exists_spMap_affPt {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens)
    {C : Type} [CommRing C] (x : Sp C ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U.1) :
    ∃ g : Sec s U.1 →+* C, spMap g ≫ affPt s U = x := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec x U.2 (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
  refine ⟨(x.appLE U.1 ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom).hom, ?_⟩
  change Spec.map (x.appLE U.1 ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom) ≫ U.2.fromSpec = x
  rw [Spec.map_comp, Category.assoc, this, ← Category.assoc, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.id_comp]

theorem eq_of_spMap_eq {A C : Type} [CommRing A] [CommRing C] {g g' : A →+* C} (h : spMap g = spMap g') : g = g' :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

theorem eq_of_spMap_affPt {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (U : X.affineOpens)
    {C : Type} [CommRing C] {g g' : Sec s U.1 →+* C} (h : spMap g ≫ affPt s U = spMap g' ≫ affPt s U) : g = g' := by
  have : Mono (affPt s U) := @IsOpenImmersion.mono _ _ _ (IsAffineOpen.isOpenImmersion_fromSpec U.2)
  exact eq_of_spMap_eq ((cancel_mono _).1 h)

theorem red_over (D : Data) : D.i ≫ D.s = D.t := by
  obtain ⟨s₀, hpb, ht⟩ := D.red
  rw [ht, hpb.w]

variable {D : Data} (Λ : Lift D)

theorem Lift.isDPMorphism (U : AffOp D.X) (T : Thick D.κ D.t) (φ : (Λ.L.obj U).B →ₐ[D.R] T.B) :
    IsDPMorphism (Λ.L.obj U).δ T.δ (φ : (Λ.L.obj U).B →+* T.B) := by
  have hI : ∀ r ∈ D.I, algebraMap D.R T.B r ∈ T.J := fun r hr ↦ T.dp.1 (Ideal.mem_map_of_mem _ hr)
  refine IsDPMorphism.on_span (S := algebraMap D.R (Λ.L.obj U).B '' D.I) _ _ (Λ.gen U) ?_ ?_
  · rintro _ ⟨r, hr, rfl⟩
    simpa using hI r hr
  · rintro n _ ⟨r, hr, rfl⟩
    rw [(Λ.L.obj U).dp.2 r hr]
    simpa using (T.dp.2 (n := n) r hr).symm

theorem Lift.hom_iff (U : AffOp D.X) (T : Thick D.κ D.t) (y : Sec D.s U.unop.1 →ₐ[D.R] T.B) :
    spMap (T.π.comp (y : Sec D.s U.unop.1 →+* T.B)) ≫ affPt D.s U.unop = T.x ≫ D.i ↔
      ∃ b : Λ.L.obj U ⟶ T, ∀ a, b.φ (Λ.e U a) = y a := by
  constructor
  · intro h
    let φ : (Λ.L.obj U).B →ₐ[D.R] T.B := y.comp (Λ.e U).symm.toAlgHom
    have hφ : ∀ a, φ (Λ.e U a) = y a := fun a ↦ by simp [φ]
    have hd := Λ.isDPMorphism U T φ
    let φ₀ : (Λ.L.obj U).B₀ →+* T.B₀ := RingHom.liftOfSurjective (Λ.L.obj U).π (Λ.L.obj U).surj
      ⟨T.π.comp (φ : (Λ.L.obj U).B →+* T.B), fun b hb ↦
        (T.ker _).2 (hd.1 (Ideal.mem_map_of_mem _ (((Λ.L.obj U).ker b).1 hb)))⟩
    have hc : ∀ b, φ₀ ((Λ.L.obj U).π b) = T.π (φ b) := fun b ↦
      RingHom.liftOfRightInverse_comp_apply _ _ _ _ b
    refine ⟨⟨φ, φ₀, hc, hd, ?_⟩, hφ⟩
    have := D.mono_i
    rw [← cancel_mono D.i, Category.assoc, ← Λ.pt U, ← h, ← Category.assoc, ← Cris.spMap_comp]
    congr 2
    exact RingHom.ext fun a ↦ (hc _).trans (congrArg T.π (hφ a))
  · rintro ⟨b, hb⟩
    rw [← b.pt, Category.assoc, ← Λ.pt U, ← Category.assoc, ← Cris.spMap_comp]
    congr 2
    exact RingHom.ext fun a ↦ ((b.comm _).trans (congrArg T.π (hb a))).symm

theorem Lift.hom_spec : ∀ (D : Data) (Λ : Lift D), (∀ (U : AffOp D.X) (T : Thick D.κ D.t) (y : Sec D.s U.unop.1 →ₐ[D.R] T.B), spMap (T.π.comp (y : Sec D.s U.unop.1 →+* T.B)) ≫ affPt D.s U.unop = T.x ≫ D.i ↔ ∃ b : Λ.L.obj U ⟶ T, ∀ a, b.φ (Λ.e U a) = y a) ∧ (∀ (U : AffOp D.X) (T : Thick D.κ D.t), ⊤ ≤ (T.x ≫ D.i) ⁻¹ᵁ U.unop.1 → ∃ g : Sec D.s U.unop.1 →+* T.B₀, spMap g ≫ affPt D.s U.unop = T.x ≫ D.i ∧ ∀ r, g (algebraMap D.R _ r) = T.π (algebraMap D.R T.B r)) ∧ (∀ (U : AffOp D.X) (C : Type) [CommRing C] (g g' : Sec D.s U.unop.1 →+* C), spMap g ≫ affPt D.s U.unop = spMap g' ≫ affPt D.s U.unop → g = g') ∧ ∃ N₀, ∀ N, N₀ ≤ N → ∀ U, IsLev (Λ.L.obj U).δ N := by
  intro D Λ
  refine ⟨Λ.hom_iff, fun U T h ↦ ?_, fun U C _ g g' h ↦ eq_of_spMap_affPt _ _ h, ?_⟩
  · obtain ⟨g, hg⟩ := exists_spMap_affPt D.s U.unop _ h
    refine ⟨g, hg, fun r ↦ ?_⟩
    have : spMap (g.comp (algebraMap D.R (Sec D.s U.unop.1))) = spMap (T.π.comp (algebraMap D.R T.B)) := by
      rw [Cris.spMap_comp, ← affPt_w, ← Category.assoc, hg, Category.assoc, red_over, T.w]
    exact RingHom.congr_fun (eq_of_spMap_eq this) r
  · obtain ⟨N₀, h⟩ := (isDPNilpotent_iff_exists_isLevel D.κ).1 D.nil
    refine ⟨N₀, fun N hN U ↦ ?_⟩
    have h' : fil D.κ N = ⊥ := eq_bot_iff.2 (le_of_le_of_eq (ExpBij.dpFil_anti D.κ hN) h)
    have := fil_le_map_fil _ _ D.κ _ _ (Λ.L.obj U).δ _ (Λ.L.obj U).dp (Λ.gen U) N
    rw [h', Ideal.map_bot] at this
    exact eq_bot_iff.2 this

end GlobalTheory.PDForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomSpecPointsLevelsStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hom_spec_points_levels : ∀ (D : Data) (Λ : Lift D), (∀ (U : AffOp D.X) (T : Thick D.κ D.t) (y : Sec D.s U.unop.1 →ₐ[D.R] T.B), spMap (T.π.comp (y : Sec D.s U.unop.1 →+* T.B)) ≫ affPt D.s U.unop = T.x ≫ D.i ↔ ∃ b : Λ.L.obj U ⟶ T, ∀ a, b.φ (Λ.e U a) = y a) ∧ (∀ (U : AffOp D.X) (T : Thick D.κ D.t), ⊤ ≤ (T.x ≫ D.i) ⁻¹ᵁ U.unop.1 → ∃ g : Sec D.s U.unop.1 →+* T.B₀, spMap g ≫ affPt D.s U.unop = T.x ≫ D.i ∧ ∀ r, g (algebraMap D.R _ r) = T.π (algebraMap D.R T.B r)) ∧ (∀ (U : AffOp D.X) (C : Type) [CommRing C] (g g' : Sec D.s U.unop.1 →+* C), spMap g ≫ affPt D.s U.unop = spMap g' ≫ affPt D.s U.unop → g = g') ∧ ∃ N₀, ∀ N, N₀ ≤ N → ∀ U, IsLev (Λ.L.obj U).δ N := by
  first | exact @GlobalTheory.PDForm.Lift.hom_spec | exact GlobalTheory.PDForm.Lift.hom_spec | (intros; apply GlobalTheory.PDForm.Lift.hom_spec <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteTraitOverClosedPointModification
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteTraitOverClosedPointModification
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_cDvr_injective_isLocalHom (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [CharZero A] :
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (ψ : A →+* W),
      GlobalTheory.LN.CDvr W ∧ Function.Injective ψ ∧ IsLocalHom ψ := by
  by_cases h : IsField A
  · letI := h.toField
    refine ⟨PowerSeries A, inferInstance, inferInstance, inferInstance, PowerSeries.C, ⟨inferInstance, ?_, ?_⟩,
      RingHom.injective _, inferInstance⟩
    · rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
    · exact charZero_of_injective_ringHom (f := PowerSeries.C (R := A)) (RingHom.injective _)
  · obtain ⟨O, _, _, _, _, φ, h1, h2⟩ := exists_complete_discreteValuationRing_dominating A h
    exact ⟨O, inferInstance, inferInstance, inferInstance, φ,
      ⟨inferInstance, inferInstance, charZero_of_injective_ringHom h1⟩, h1, h2⟩

theorem exists_trait_over_closedPoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R →
    ∀ (M : Modif R) (x₀ : M.S), M.π x₀ = closedPoint R →
      ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (ξ : Sp W ⟶ M.S),
        GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ ≫ M.π = spMap φ ∧ ξ (closedPoint W) = x₀ := by
  intro R _ _ _ hB M x₀ hx
  have : IsNoetherianRing R := hB.1.1
  have : CharZero R := hB.2
  have := M.integral
  have := M.proper
  have := LocallyOfFiniteType.isLocallyNoetherian M.π
  obtain ⟨θ, hθ⟩ := Spec.map_surjective (M.S.fromSpecStalk x₀ ≫ M.π)
  have hpt : ∀ q, (Spec.map θ) q = M.π (M.S.fromSpecStalk x₀ q) := fun q => by
    rw [hθ, Scheme.Hom.comp_apply]
  have hloc : IsLocalHom θ.hom := by
    apply ((local_hom_tfae θ.hom).out 1 5).2
    have e := hpt (closedPoint (M.S.presheaf.stalk x₀) : Spec (M.S.presheaf.stalk x₀))
    rw [Scheme.fromSpecStalk_closedPoint, hx] at e
    exact congrArg PrimeSpectrum.asIdeal e
  have hinj : Function.Injective θ.hom := by
    let pt : Sp (FractionRing R) := closedPoint (FractionRing R)
    obtain ⟨q, hq⟩ : M.gp pt ∈ Set.range (M.S.fromSpecStalk x₀) := by
      rw [Scheme.range_fromSpecStalk]
      show _ ⤳ x₀
      rw [specializes_iff_mem_closure]
      have hd := M.dominant.denseRange
      have hs : Set.range M.gp.base ⊆ {M.gp pt} := by
        rintro _ ⟨y, rfl⟩
        rw [Subsingleton.elim y (closedPoint _)]
        rfl
      exact closure_mono hs (hd.closure_range ▸ Set.mem_univ x₀)
    have h1 : (Spec.map θ) q = jK R pt := by
      rw [hpt, hq]
      exact (Scheme.Hom.comp_apply M.gp M.π pt).symm.trans (by rw [M.gp_π])
    have h2 := congrArg PrimeSpectrum.asIdeal h1
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    have h3 : a ∈ Ideal.comap θ.hom q.asIdeal := by
      rw [Ideal.mem_comap, ha]; exact Ideal.zero_mem _
    have h4 : algebraMap R (FractionRing R) a ∈ maximalIdeal (FractionRing R) := by
      have h5 : a ∈ ((jK R) pt).asIdeal := by
        rw [← h2]; exact h3
      exact h5
    have h6 : algebraMap R (FractionRing R) a = 0 := by
      by_contra hne
      exact (maximalIdeal.isMaximal _).ne_top (Ideal.eq_top_of_isUnit_mem _ h4 (isUnit_iff_ne_zero.2 hne))
    exact IsFractionRing.injective R (FractionRing R) (h6.trans (map_zero _).symm)
  have : CharZero (M.S.presheaf.stalk x₀) := charZero_of_injective_ringHom hinj
  obtain ⟨W, _, _, _, ψ, hW, hψi, hψl⟩ := exists_cDvr_injective_isLocalHom (M.S.presheaf.stalk x₀)
  refine ⟨W, inferInstance, inferInstance, inferInstance, ψ.comp θ.hom, spMap ψ ≫ M.S.fromSpecStalk x₀, hW,
    hψi.comp hinj, RingHom.isLocalHom_comp _ _, ?_, ?_⟩
  · rw [Category.assoc, ← hθ, ← Spec.map_comp]
    rfl
  · exact (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (M.S.fromSpecStalk x₀) (IsLocalRing.comap_closedPoint ψ))
        (Scheme.fromSpecStalk_closedPoint (x := x₀)))

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteTraitOverClosedPointModificationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_completeTrait_over_closedPoint_modification : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (M : Modif R) (x₀ : M.S), M.π x₀ = closedPoint R → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (ξ : Sp W ⟶ M.S), GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧ ξ ≫ M.π = spMap φ ∧ ξ (closedPoint W) = x₀ := by
  first | exact @GlobalTheory.Mum.exists_trait_over_closedPoint | exact GlobalTheory.Mum.exists_trait_over_closedPoint | (intros; apply GlobalTheory.Mum.exists_trait_over_closedPoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpreadOfTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.SpreadTrait

theorem pull_cancel {S S' S'' : Scheme.{0}} {G : Over S} [GrpObj G] {G₁ : Over S'} [GrpObj G₁] {f : S' ⟶ S}
    {m₁ : G₁.left ⟶ G.left} (h₁ : IsGrpPullback G₁ G f m₁) (u : S'' ⟶ S') {Gl : Over S''} [GrpObj Gl]
    {φl : Gl.left ⟶ G.left} (hGl : IsGrpPullback Gl G (u ≫ f) φl) :
    ∃ φ : Gl.left ⟶ G₁.left, IsGrpPullback Gl G₁ u φ ∧ φ ≫ m₁ = φl :=
  ⟨h₁.1.lift φl (Gl.hom ≫ u) (by rw [hGl.1.w, Category.assoc]),
    h₁.cancel (hGl.congr rfl (h₁.1.lift_fst _ _ _).symm) (h₁.1.lift_snd _ _ _), h₁.1.lift_fst _ _ _⟩

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (u : A →+* B) (v : B →+* C) :
    spMap v ≫ spMap u = spMap (v.comp u) := (Spec.map_comp _ _).symm

theorem spread_of_trait {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {D' : DegData V (maximalIdeal V)}
    {A' : PolAV (Sp (FractionRing V))} {G' : Over (Sp V)} [GrpObj G'] [IsCommMonObj G']
    (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left)
    (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsDiscreteValuationRing V₁] (ψ : R →+* V₁) (hψ : IsLocalHom ψ)
    (Ω : Type) [Field Ω] (α : V₁ →+* Ω) (hα : Function.Injective α) (b : V →+* Ω)
    (hb : ∀ x ∈ maximalIdeal V ^ (0 + 1), b x = 0) (eα : α.comp ψ = b.comp g)
    (GΩ : Over (Sp Ω)) [GrpObj GΩ] (n : GΩ.left ⟶ ((Over.pullback (spMap ψ)).obj G).left)
    (hn : IsGrpPullback GΩ ((Over.pullback (spMap ψ)).obj G) (spMap α) n)
    (n' : GΩ.left ⟶ G'.left) (hn' : IsGrpPullback GΩ G' (spMap b) n')
    (hnn : n ≫ pullback.fst G.hom (spMap ψ) = n' ≫ β)
    (j : splitTorus (Sp V₁) D'.toPre.X ⟶ (Over.pullback (spMap ψ)).obj G) (hj : IsMonHom j)
    (ej : GlobalTheory.TorusPart.pullTorus hn j = GlobalTheory.TorusPart.gtTorus (U'.gt 0) hb hn') :
    ∃ ρ, Spread U U' g β ρ := by
  haveI := hψ
  haveI := hj
  have hm₁ := isGrpPullback_pullback G (spMap ψ)
  have hm₀ := isGrpPullback_pullback ((Over.pullback (spMap ψ)).obj G) (spMap (residue V₁))
  have hm₀' := (hm₀.comp hm₁).congr (spMap_comp' ψ (residue V₁)) rfl
  have h₀ : ∀ x ∈ maximalIdeal R, (residue V₁).comp ψ x = 0 := GlobalTheory.TorusPart.map_eq_zero_of_isLocalHom _
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt 0) (GlobalTheory.TorusPart.map_pow_one_eq_zero h₀)
    hm₀').2 _ (GlobalTheory.TorusPart.pullTorus hm₀ j) inferInstance
  exact ⟨ρ, V₁, inferInstance, inferInstance, inferInstance, ψ, (Over.pullback (spMap ψ)).obj G, inferInstance,
    inferInstance, pullback.fst G.hom (spMap ψ), Ω, inferInstance, α, b, hb, GΩ, inferInstance, n, hn, n', hn', j, _,
    inferInstance, _, hm₀, GlobalTheory.TorusPart.map_pow_one_eq_zero h₀, hm₀', hψ, hm₁, hj, hα, eα, hnn, ej, hρ⟩

theorem exists_spread : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) β → ∃ ρ, Spread U U' g β ρ := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hV G' _ _ hG' D' A' U' g β hβ
  haveI : IsNoetherianRing R := hR.1.1
  by_cases hl : IsLocalHom g
  · haveI := hl
    let κ := ResidueField V
    have hC : IsLocalHom (PowerSeries.C (R := κ)) :=
      ⟨fun a ha => by simpa using ha.map (PowerSeries.constantCoeff (R := κ))⟩
    let c : V →+* PowerSeries κ := (PowerSeries.C (R := κ)).comp (residue V)
    have hcl : IsLocalHom c := RingHom.isLocalHom_comp _ _
    let ψ : R →+* PowerSeries κ := c.comp g
    have hψ : IsLocalHom ψ := RingHom.isLocalHom_comp _ _
    let α := algebraMap (PowerSeries κ) (FractionRing (PowerSeries κ))
    have hα : Function.Injective α := IsFractionRing.injective _ _
    let b : V →+* FractionRing (PowerSeries κ) := α.comp c
    have hc0 : ∀ x ∈ maximalIdeal V, c x = 0 := fun x hx => by
      simp [c, (IsLocalRing.residue_eq_zero_iff x).2 hx]
    have hc : ∀ x ∈ maximalIdeal V ^ (0 + 1), c x = 0 := GlobalTheory.TorusPart.map_pow_one_eq_zero hc0
    have hb : ∀ x ∈ maximalIdeal V ^ (0 + 1), b x = 0 := fun x hx => by
      simp [b, hc x hx]
    have hm₁ := isGrpPullback_pullback G (spMap ψ)
    obtain ⟨mc, hmc, hmcβ⟩ := pull_cancel hβ (spMap c) (hm₁.congr (spMap_comp' g c).symm rfl)
    have hn := isGrpPullback_pullback ((Over.pullback (spMap ψ)).obj G) (spMap α)
    have hn' : IsGrpPullback _ G' (spMap b) _ := (hn.comp hmc).congr (spMap_comp' c α) rfl
    have hnn : pullback.fst ((Over.pullback (spMap ψ)).obj G).hom (spMap α) ≫ pullback.fst G.hom (spMap ψ) =
        (pullback.fst ((Over.pullback (spMap ψ)).obj G).hom (spMap α) ≫ mc) ≫ β := by
      rw [Category.assoc, hmcβ]
    exact spread_of_trait U U' g β (PowerSeries κ) ψ hψ _ α hα b hb rfl _ _ hn _ hn' hnn
      (GlobalTheory.TorusPart.gtTorus (U'.gt 0) hc hmc) inferInstance
      (GlobalTheory.TorusPart.pullTorus_gtTorus (U'.gt 0) hc hb hmc hn' hn rfl rfl)
  · obtain ⟨V₁, _, _, _, ψ, Ω, _, αK, b, hψ, hb, eα, hT⟩ := GlobalTheory.T.exists_trait_nonlocal_torusExtension' R G hG V g hl
    haveI := hψ
    let alg := algebraMap V₁ (FractionRing V₁)
    have hα : Function.Injective (αK.comp alg) :=
      αK.injective.comp (IsFractionRing.injective V₁ (FractionRing V₁))
    have hm₁ := isGrpPullback_pullback G (spMap ψ)
    have hG₁ : IsSemiAbelian ((Over.pullback (spMap ψ)).obj G) := IsSemiAbelian.pullback _ G hG
    obtain ⟨φ₁, hφ₁, -⟩ := pull_cancel hm₁ (spMap alg)
      ((isGrpPullback_pullback G (spMap (alg.comp ψ))).congr (spMap_comp' ψ alg).symm rfl)
    have hn' := isGrpPullback_pullback G' (spMap b)
    obtain ⟨n, hn, hnm⟩ := pull_cancel hm₁ (spMap (αK.comp alg))
      ((hn'.comp hβ).congr ((spMap_comp' g b).trans ((congrArg spMap eα.symm).trans
        (spMap_comp' ψ (αK.comp alg)).symm)) rfl)
    have hb' : ∀ x ∈ maximalIdeal V ^ (0 + 1), b x = 0 := GlobalTheory.TorusPart.map_pow_one_eq_zero hb
    obtain ⟨j, hj, ej⟩ := GlobalTheory.T.extend_splitTorus_hom_over_dvr V₁ ((Over.pullback (spMap ψ)).obj G) hG₁ _ φ₁ hφ₁ hT Ω αK _ n hn _
      (GlobalTheory.TorusPart.gtTorus (U'.gt 0) hb' hn') inferInstance
    exact spread_of_trait U U' g β V₁ ψ hψ Ω (αK.comp alg) hα b hb' eα _ n hn _ hn' hnm j hj ej

end GlobalTheory.SpreadTrait
end
