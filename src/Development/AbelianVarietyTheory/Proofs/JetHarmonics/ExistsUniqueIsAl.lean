module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowEqScaleAndExistsUniqueTorsion
public import Development.AbelianVarietyTheory.Definitions.Jets.WigMap
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CasimirSplitting
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeAdelicMatrixIntegralTranslate

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueIsAl
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HodgeTateImage

open GlobalTheory.TangentPow GlobalTheory.GmPoints

variable {O : Type} [CommRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G] {p : ℕ}

noncomputable def bc (R : Type) [CommRing R] [Algebra O R] (x : LieG G) :
    specO O (DualNumber R) ⟶ G :=
  ptMap (dualBC (Algebra.ofId O R)) ≫ x.1

theorem fst_bc (R : Type) [CommRing R] [Algebra O R] (x : LieG G) :
    ptMap (TrivSqZeroExt.fstHom O R R) ≫ bc R x = 1 := by
  have h : ptMap (TrivSqZeroExt.fstHom O R R) ≫ ptMap (dualBC (Algebra.ofId O R)) =
      ptMap (Algebra.ofId O R) ≫ ptMap (TrivSqZeroExt.fstHom O O O) := by
    rw [ptMap_comp_ptMap, ptMap_comp_ptMap]
    congr 1
    refine AlgHom.ext fun y => ?_
    simp [dualBC, TrivSqZeroExt.lift_def, TrivSqZeroExt.algebraMap_eq_inl']
  rw [bc, ← Category.assoc, h, Category.assoc, x.2]
  exact comp_one _

theorem dualBC_fst {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (φ : R →ₐ[O] R') (y : DualNumber R) : (dualBC φ y).fst = φ y.fst := by
  simp [dualBC, TrivSqZeroExt.lift_def]

theorem dualBC_snd {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (φ : R →ₐ[O] R') (y : DualNumber R) : (dualBC φ y).snd = φ y.snd := by
  simp [dualBC, TrivSqZeroExt.lift_def]

theorem ptMap_bc {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (φ : R →ₐ[O] R') (x : LieG G) : ptMap (dualBC φ) ≫ bc R x = bc R' x := by
  rw [bc, bc, ← Category.assoc, ptMap_comp_ptMap]
  congr 2
  refine AlgHom.ext fun y => ?_
  ext
  · simp only [AlgHom.comp_apply, dualBC_fst, Algebra.ofId_apply, AlgHom.commutes]
  · simp only [AlgHom.comp_apply, dualBC_snd, Algebra.ofId_apply, AlgHom.commutes]

theorem existsUnique_lift {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : ∃! w : specO O (DualNumber R) ⟶ torsion G (p ^ n),
      w ≫ torsion.ι G (p ^ n) = bc R x :=
  (pow_eq_scale_and_existsUnique_torsion O G R (p ^ n) _ (fst_bc R x)).2 (by exact_mod_cast hR)

noncomputable def lift {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : specO O (DualNumber R) ⟶ torsion G (p ^ n) :=
  (existsUnique_lift hR x).choose

theorem lift_ι {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : lift hR x ≫ torsion.ι G (p ^ n) = bc R x :=
  (existsUnique_lift hR x).choose_spec.1

theorem eq_lift {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) {w : specO O (DualNumber R) ⟶ torsion G (p ^ n)}
    (hw : w ≫ torsion.ι G (p ^ n) = bc R x) : w = lift hR x :=
  (existsUnique_lift hR x).unique hw (lift_ι hR x)

variable (χ : Tv G p)

noncomputable def unitAt {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : DualNumber R :=
  (unitOf (lift hR x ≫ χ.χ n) : DualNumber R)

theorem unitAt_fst {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x : LieG G) : (unitAt χ hR x).fst = 1 := by
  set z := ptMap (TrivSqZeroExt.fstHom O R R) ≫ lift hR x with hz
  have h1 : z ≫ torsion.ι G (p ^ n) = 1 := by
    rw [hz, Category.assoc, lift_ι, fst_bc]
  have h2 := χ.isChar n _ z z z (by rw [h1, _root_.mul_one])
  have h3 : unitOf (z ≫ χ.χ n) = 1 := by
    have := congrArg unitOf h2
    rw [unitOf_mul] at this
    exact left_eq_mul.mp this
  have h4 := unitOf_ptMap (TrivSqZeroExt.fstHom O R R) (lift hR x ≫ χ.χ n)
  rw [← Category.assoc, ← hz, h3] at h4
  exact h4.symm

theorem unitAt_map {n : ℕ} {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (φ : R →ₐ[O] R') (hR : (p : R) ^ n = 0) (hR' : (p : R') ^ n = 0) (x : LieG G) :
    (unitAt χ hR' x).snd = φ (unitAt χ hR x).snd := by
  have h : ptMap (dualBC φ) ≫ lift hR x = lift hR' x :=
    eq_lift hR' x (by rw [Category.assoc, lift_ι, ptMap_bc])
  rw [unitAt, ← h, Category.assoc, unitOf_ptMap, dualBC_snd, unitAt]

theorem unitAt_le {m n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hm : (p : R) ^ m = 0)
    (hmn : m ≤ n) (hn : (p : R) ^ n = 0) (x : LieG G) : unitAt χ hn x = unitAt χ hm x := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    have hn' : (p : R) ^ n = 0 := pow_eq_zero_of_le hmn hm
    rw [← ih hn', unitAt, unitAt,
      χ.compat n _ (lift hn' x) (lift hn x) (by rw [lift_ι, lift_ι])]

theorem unitAt_mul {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (x y z : LieG G) (h : z.1 = x.1 * y.1) :
    (unitAt χ hR z).snd = (unitAt χ hR x).snd + (unitAt χ hR y).snd := by
  have h1 := χ.isChar n _ (lift hR x) (lift hR y) (lift hR z)
    (by rw [lift_ι, lift_ι, lift_ι, bc, bc, bc, h, comp_mul])
  have h2 : unitAt χ hR z = unitAt χ hR x * unitAt χ hR y := by
    rw [unitAt, h1, unitOf_mul, Units.val_mul, unitAt, unitAt]
  rw [h2, DualNumber.snd_mul, unitAt_fst, unitAt_fst]
  ring

theorem unitAt_scale {n : ℕ} {R : Type} [CommRing R] [Algebra O R] (hR : (p : R) ^ n = 0)
    (a : O) (x z : LieG G) (h : z.1 = ptMap (dualScale a) ≫ x.1) :
    (unitAt χ hR z).snd = algebraMap O R a * (unitAt χ hR x).snd := by
  have h1 : scale (O := O) (algebraMap O R a) ≫ lift hR x = lift hR z := by
    refine eq_lift hR z ?_
    rw [Category.assoc, lift_ι, bc, bc, h, ← Category.assoc, ← Category.assoc, scale,
      ptMap_comp_ptMap, ptMap_comp_ptMap]
    congr 2
    refine AlgHom.ext fun y => ?_
    ext
    · simp [dualBC_fst, dualScale]
    · simp [dualBC_snd, dualScale, Algebra.smul_def]
  rw [unitAt, ← h1, Category.assoc, scale, unitOf_ptMap]
  simp [unitAt, Algebra.smul_def]

theorem pow_quot (n : ℕ) : (p : O ⧸ Ideal.span {(p : O) ^ n}) ^ n = 0 := by
  have : Ideal.Quotient.mk (Ideal.span {(p : O) ^ n}) ((p : O) ^ n) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rwa [map_pow, map_natCast] at this

theorem smod_iff (n : ℕ) (a b : O) :
    a ≡ b [SMOD (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O O)] ↔
      algebraMap O (O ⧸ Ideal.span {(p : O) ^ n}) a =
        algebraMap O (O ⧸ Ideal.span {(p : O) ^ n}) b := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top,
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq]

theorem eq_of_forall [IsHausdorff (Ideal.span {(p : O)}) O] {a b : O}
    (h : ∀ n, algebraMap O (O ⧸ Ideal.span {(p : O) ^ n}) a =
        algebraMap O (O ⧸ Ideal.span {(p : O) ^ n}) b) : a = b := by
  refine sub_eq_zero.mp (IsHausdorff.haus' (I := Ideal.span {(p : O)}) (a - b) fun n => ?_)
  rw [SModEq.zero, ← SModEq.sub_mem, smod_iff]
  exact h n

theorem exists_level (n : ℕ) (x : LieG G) : ∃ a : O, ∀ (R : Type) [CommRing R] [Algebra O R]
    (hR : (p : R) ^ n = 0), algebraMap O R a = (unitAt χ hR x).snd := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (unitAt χ (pow_quot (O := O) n) x).snd
  refine ⟨a, fun R _ _ hR => ?_⟩
  let φ : (O ⧸ Ideal.span {(p : O) ^ n}) →ₐ[O] R :=
    Ideal.Quotient.liftₐ _ (Algebra.ofId O R) fun c hc => by
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
      simp [hR]
  rw [unitAt_map χ φ (pow_quot n) hR, ← ha]
  exact (φ.commutes a).symm

theorem exists_limit [IsPrecomplete (Ideal.span {(p : O)}) O] (x : LieG G) :
    ∃ a : O, ∀ (n : ℕ) (R : Type) [CommRing R] [Algebra O R]
      (hR : (p : R) ^ n = 0), algebraMap O R a = (unitAt χ hR x).snd := by
  choose a ha using fun n => exists_level χ n x
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : O)}) a fun {m n} hmn => by
    rw [smod_iff, ha m _ (pow_quot m), ha n _ (pow_eq_zero_of_le hmn (pow_quot m)),
      unitAt_le χ (pow_quot m) hmn]
  refine ⟨L, fun n R _ _ hR => ?_⟩
  have h := hL n
  rw [smod_iff, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq] at h
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp h
  rw [← ha n R hR, eq_comm, ← sub_eq_zero, ← map_sub, ← hd]
  simp [hR]

theorem isAl_iff (f : LieG G → O) : IsAl χ f ↔ ∀ (x : LieG G) (n : ℕ) (R : Type) [CommRing R]
    [Algebra O R] (hR : (p : R) ^ n = 0), algebraMap O R (f x) = (unitAt χ hR x).snd := by
  constructor
  · intro h x n R _ _ hR
    rw [unitAt, h n R hR x _ (lift_ι hR x), TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl,
      TrivSqZeroExt.snd_inr, zero_add]
  · intro h n R _ _ hR x w hw
    rw [eq_lift hR x hw]
    ext
    · rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
      exact unitAt_fst χ hR x
    · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
      exact (h x n R hR).symm

theorem existsUnique_isAl [IsAdicComplete (Ideal.span {(p : O)}) O] :
    ∃! f : LieG G → O, f ∈ omega G ∧ IsAl χ f := by
  choose f hf using exists_limit χ
  refine ⟨f, ⟨⟨fun x y h => eq_of_forall (p := p) fun n => ?_,
    fun a x h => eq_of_forall (p := p) fun n => ?_⟩, (isAl_iff χ f).2 hf⟩, fun g hg => ?_⟩
  · rw [map_add (f := _), hf x n _ (pow_quot n), hf y n _ (pow_quot n)]
    exact (hf _ n _ (pow_quot n)).trans (unitAt_mul χ _ x y _ rfl)
  · rw [map_mul, hf x n _ (pow_quot n)]
    exact (hf _ n _ (pow_quot n)).trans (unitAt_scale χ _ a x _ rfl)
  · funext x
    refine eq_of_forall (p := p) fun n => ?_
    rw [hf _ n _ (pow_quot n), (isAl_iff χ g).1 hg.2 x n _ (pow_quot n)]

end GlobalTheory.HodgeTateImage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsReducedTorsionGeometricFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.TorsionReduced

theorem isReduced_of_forall_dualNumber (F B : Type) [Field F] [IsAlgClosed F] [CommRing B]
    [Algebra F B] [Module.Finite F B]
    (h : ∀ (φ : B →ₐ[F] DualNumber F) (b : B), (φ b).snd = 0) : _root_.IsReduced B := by
  have hs : Subsingleton (KaehlerDifferential F B) := by
    by_contra hne
    have : Nontrivial (KaehlerDifferential F B) := not_subsingleton_iff_nontrivial.mp hne
    obtain ⟨P, hP, -⟩ := (eq_top_or_exists_le_coatom
      (⊥ : Submodule B (KaehlerDifferential F B))).resolve_left bot_ne_top
    have hsimple : IsSimpleModule B (KaehlerDifferential F B ⧸ P) :=
      isSimpleModule_iff_isCoatom.mpr hP
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
    letI : Field (B ⧸ m) := Ideal.Quotient.field m
    have hb : Function.Bijective (algebraMap F (B ⧸ m)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let u : (B ⧸ m) ≃ₐ[F] F := (AlgEquiv.ofBijective (Algebra.ofId F (B ⧸ m)) hb).symm
    let l : KaehlerDifferential F B →ₗ[B] (B ⧸ m) := e.toLinearMap ∘ₗ P.mkQ
    let D : Derivation F B (B ⧸ m) := l.compDer (KaehlerDifferential.D F B)
    let φ : B →ₐ[F] DualNumber F :=
      { toFun := fun b => TrivSqZeroExt.inl (u (Ideal.Quotient.mk m b)) + TrivSqZeroExt.inr (u (D b))
        map_one' := by ext <;> simp
        map_mul' := fun a b => by
          ext
          · simp
          · simp [Algebra.smul_def, mul_comm, TrivSqZeroExt.algebraMap_eq_inl]
        map_zero' := by ext <;> simp
        map_add' := fun a b => by ext <;> simp
        commutes' := fun r => by
          ext
          · simpa [TrivSqZeroExt.algebraMap_eq_inl] using u.commutes r
          · simp [TrivSqZeroExt.algebraMap_eq_inl] }
    have hD : ∀ b, l (KaehlerDifferential.D F B b) = 0 := fun b => by
      have := h φ b
      simpa [φ, D] using this
    have hl : l = 0 := by
      refine LinearMap.ext_on (KaehlerDifferential.span_range_derivation F B) ?_
      rintro _ ⟨b, rfl⟩
      exact hD b
    apply hP.1
    rw [eq_top_iff]
    intro x _
    have := LinearMap.congr_fun hl x
    simpa [l] using this
  have : Algebra.FormallyUnramified F B := ⟨hs⟩
  exact Algebra.FormallyUnramified.isReduced_of_field F B

variable {O : Type} [CommRing O] {R : Type} [CommRing R] [Algebra O R]

theorem scale_comp_scale (a b : R) :
    TangentPow.scale O a ≫ TangentPow.scale O b = TangentPow.scale O (a * b) := by
  rw [TangentPow.scale, TangentPow.scale, TangentPow.ptMap_comp_ptMap, TangentPow.scale]
  congr 1
  refine AlgHom.ext fun x => ?_
  ext <;> simp [_root_.mul_assoc]

theorem eq_const_of_pow_eq_one {G : Over (Spec (CommRingCat.of O))} [GrpObj G] [IsCommMonObj G]
    {N : ℕ} (hN : IsUnit (N : R)) (y : specO O (DualNumber R) ⟶ G) (hy : y ^ N = 1) :
    y = ptMap (TrivSqZeroExt.inlAlgHom O R R) ≫ ptMap (TrivSqZeroExt.fstHom O R R) ≫ y := by
  set c := ptMap (TrivSqZeroExt.inlAlgHom O R R) ≫ ptMap (TrivSqZeroExt.fstHom O R R) ≫ y with hc
  have h0 : ptMap (TrivSqZeroExt.fstHom O R R) ≫ ptMap (TrivSqZeroExt.inlAlgHom O R R) = 𝟙 _ := by
    rw [TangentPow.ptMap_comp_ptMap, ← TangentPow.ptMap_id']
    congr 1
  have h1 : ptMap (TrivSqZeroExt.fstHom O R R) ≫ (y * c⁻¹) = 1 := by
    rw [comp_mul, GrpObj.comp_inv, hc, ← Category.assoc, h0, Category.id_comp, mul_inv_cancel]
  have h2 : c ^ N = 1 := by
    rw [hc, ← MonObj.comp_pow, ← MonObj.comp_pow, hy, comp_one, comp_one]
  have h3 : (y * c⁻¹) ^ N = 1 := by
    rw [mul_pow, inv_pow, hy, h2, inv_one, _root_.mul_one]
  rw [TangentPow.pow_eq_scale_comp h1] at h3
  obtain ⟨a, ha⟩ := hN.exists_left_inv
  have h4 := congrArg (TangentPow.scale O a ≫ ·) h3
  simp only [← Category.assoc, scale_comp_scale, ha, TangentPow.scale_one, Category.id_comp,
    comp_one] at h4
  exact mul_inv_eq_one.mp h4

end GlobalTheory.TorsionReduced

namespace GlobalTheory

theorem isReduced_torsion_geometric_fibre :
    ∀ (O F : Type) [CommRing O] [Field F] [IsAlgClosed F] [Algebra O F] (G : Over (Spec (CommRingCat.of O))) [GrpObj G] [IsCommMonObj G] (N : ℕ), (N : F) ≠ 0 → IsFinite (torsion G N).hom → IsReduced (specO O F ⊗ torsion G N).left := by
  intro O F _ _ _ _ G _ _ N hN hfin
  have : IsAffine (torsion G N).left := isAffine_of_isAffineHom (torsion G N).hom
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective ((torsion G N).left.isoSpec.inv ≫ (torsion G N).hom)
  letI : Algebra O Γ((torsion G N).left, ⊤) := ψ.hom.toAlgebra
  let e : specO O Γ((torsion G N).left, ⊤) ≅ torsion G N :=
    Over.isoMk (torsion G N).left.isoSpec.symm hψ.symm
  have h1 : IsFinite (Spec.map ψ) := by rw [hψ]; infer_instance
  have : Module.Finite O Γ((torsion G N).left, ⊤) := (IsFinite.SpecMap_iff ψ).mp h1
  have hred : _root_.IsReduced (TensorProduct O F Γ((torsion G N).left, ⊤)) := by
    refine TorsionReduced.isReduced_of_forall_dualNumber F _ fun φ b => ?_
    let χ : Γ((torsion G N).left, ⊤) →ₐ[O] DualNumber F :=
      (φ.restrictScalars O).comp Algebra.TensorProduct.includeRight
    have hy : ((ptMap χ ≫ e.hom) ≫ torsion.ι G N) ^ N = 1 := by
      rw [← MonObj.comp_pow, KernelNoTorsion.torsionι_pow, comp_one]
    have h2 := TorsionReduced.eq_const_of_pow_eq_one hN.isUnit _ hy
    simp only [← Category.assoc] at h2
    have h3 := (cancel_mono e.hom).mp (KernelNoTorsion.torsion_hom_ext h2)
    rw [TangentPow.ptMap_comp_ptMap, TangentPow.ptMap_comp_ptMap] at h3
    have h4 := Spec.map_injective (congrArg Over.Hom.left h3)
    have h5 : ∀ a, (χ a).snd = 0 := fun a => by
      have := congrArg TrivSqZeroExt.snd (congrArg (fun f => f.hom a) h4)
      simpa using this
    induction b with
    | add x y hx hy => simp [hx, hy]
    | tmul f a =>
      have : f ⊗ₜ[O] a = f • ((1 : F) ⊗ₜ[O] a) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [this, map_smul, TrivSqZeroExt.snd_smul]
      exact smul_eq_zero_of_right f (h5 a)
  have h4 : IsReduced (Spec (CommRingCat.of (TensorProduct O F Γ((torsion G N).left, ⊤)))) :=
    (affine_isReduced_iff _).mpr hred
  have h3 : IsReduced (specO O F ⊗ specO O Γ((torsion G N).left, ⊤)).left :=
    @isReduced_of_isOpenImmersion _ _ (pullbackSpecIso O F Γ((torsion G N).left, ⊤)).hom _ h4
  have h0 : IsIso (specO O F ◁ e.inv).left :=
    inferInstanceAs (IsIso ((Over.forget _).map (specO O F ◁ e.inv)))
  exact isReduced_of_isOpenImmersion (specO O F ◁ e.inv).left

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.OmgMulLeft
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace GlobalTheory.WigSh.OmLeftN

section
variable {k r : ℕ}

private lemma flagMat_mulVec_eq_sum_fvec (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (r + 1) → ℂ) :
    _root_.GlobalTheory.LeadingMinorInv.flagMat k r z *ᵥ c = ∑ a, c a • _root_.Formalism.QuantumDeterminants.fvec k r z a := by
  ext i
  simp [mulVec, dotProduct, _root_.GlobalTheory.LeadingMinorInv.flagMat, Finset.sum_apply, mul_comm]

private lemma rW_mulVec_adjugate_zhat_single_last (z z' : Fin (2 * r + k + 1) → ℂ) (g : _root_.Formalism.FourierDecayAlt.Q.Mx k r) :
    _root_.GlobalTheory.WigSh.omg k r z z' g = _root_.Formalism.FourierDecayAlt.D.prW k r z'
      ((_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z) *ᵥ
        ((_root_.Formalism.QuantumDeterminants.Zhat k r z z' g).adjugateᴴ *ᵥ Pi.single (Fin.last r) 1)) := by
  unfold _root_.GlobalTheory.WigSh.omg
  rw [← mulVec_mulVec _ (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.GlobalTheory.LeadingMinorInv.flagMat k r z), flagMat_mulVec_eq_sum_fvec]
  simp [mulVec_single_one, conjTranspose_apply]

private lemma conjTranspose_hpk : (_root_.Formalism.QuantumDeterminants.Hpk k r)ᴴ = _root_.Formalism.QuantumDeterminants.Hpk k r :=
  _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_conjTranspose

private lemma gram_eq_upper_bounds (z z' : Fin (2 * r + k + 1) → ℂ) (g : _root_.Formalism.FourierDecayAlt.Q.Mx k r) :
    _root_.Formalism.QuantumDeterminants.Zhat k r z z' g = (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z)ᴴ *
      (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z') := by
  rw [_root_.GlobalTheory.LeadingMinorInv.zhat_eq]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, conjTranspose_hpk,
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (_root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.Formalism.QuantumDeterminants.Hpk k r), _root_.GlobalTheory.CompanionTheory.ZuckCasSplit.hpk_sq, Matrix.one_mul]

private lemma mul_adjugate_conjTranspose_eq_of_det_eq_one {m n : ℕ} (X : Matrix (Fin n) (Fin m) ℂ)
    (U : Matrix (Fin m) (Fin m) ℂ) (Y : Matrix (Fin n) (Fin m) ℂ) (hU : U.det = 1) :
    (X * U) * ((X * U)ᴴ * Y).adjugateᴴ = X * (Xᴴ * Y).adjugateᴴ := by
  rw [conjTranspose_mul, Matrix.mul_assoc Uᴴ, adjugate_mul_distrib, conjTranspose_mul,
    adjugate_conjTranspose, conjTranspose_conjTranspose, Matrix.mul_assoc X U,
    ← Matrix.mul_assoc U, mul_adjugate, hU, one_smul, Matrix.one_mul]

private lemma det_eq_one_of_upUni {n : ℕ} {U : Matrix (Fin n) (Fin n) ℂ}
    (hU : _root_.GlobalTheory.LeadingMinorInv.UpUni U) : U.det = 1 := by
  rw [det_of_upperTriangular (fun i j h => hU.1 i j h)]
  simp [hU.2]
end

theorem _root_.GlobalTheory.WigSh.OmLeftN.omg_mul_left (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (g n : _root_.Formalism.FourierDecayAlt.Q.Mx k r) (hz : _root_.Formalism.QuantumDeterminants.inWb k r z)
    (hn : n ∈ _root_.Formalism.QuantumDeterminants.Nset k r) :
    _root_.GlobalTheory.WigSh.omg k r z z' (n * g) = _root_.GlobalTheory.WigSh.omg k r z z' g := by
  obtain ⟨U, hU, hnF⟩ := _root_.GlobalTheory.LeadingMinorInv.exists_N k r z hz n hn
  have hnU : nᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * n = _root_.Formalism.QuantumDeterminants.Hpk k r := ((_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.mem_Nset_iff n).1 hn).1
  have hQ : _root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z =
      _root_.Formalism.QuantumDeterminants.Hpk k r * (n * g)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z * U := by
    have key : nᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * (n * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z)) =
        _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z := by
      simp only [← Matrix.mul_assoc, hnU]
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rw [← hnF, key]
  rw [rW_mulVec_adjugate_zhat_single_last, rW_mulVec_adjugate_zhat_single_last, gram_eq_upper_bounds, gram_eq_upper_bounds, mulVec_mulVec, mulVec_mulVec, hQ,
    mul_adjugate_conjTranspose_eq_of_det_eq_one _ _ _ (det_eq_one_of_upUni hU)]

theorem omg_left_N : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g m : Mx k r), inWb k r z → inWb k r z' → g ∈ UH (Hpk k r) → m ∈ Formalism.QuantumDeterminants.Nset k r → GlobalTheory.WigSh.omg k r z z' (m⁻¹ * g) = GlobalTheory.WigSh.omg k r z z' g :=
  fun k r z z' g m hz _ _ hm => omg_mul_left k r z z' g m⁻¹ hz ((unipotent_subgroup_holds k r).2.2 m hm)

end GlobalTheory.WigSh.OmLeftN
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HpkConjTranspose
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q

noncomputable section

namespace GlobalTheory.WigSh

open GlobalTheory.LeadingMinorInv

namespace OmgRight

end OmgRight

open OmgRight

section
variable {k r : ℕ}

private lemma inv_eq_hpk_mul_conjTranspose_mul_hpk_of_mem_UH {x : _root_.Formalism.FourierDecayAlt.Q.Mx k r} (hx : x ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r)) :
    x⁻¹ = _root_.Formalism.QuantumDeterminants.Hpk k r * xᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r :=
  _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.inv_eq_UH hx

private lemma hpk_mul_hpk_mul_eq_self (X : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ) :
    _root_.Formalism.QuantumDeterminants.Hpk k r * (_root_.Formalism.QuantumDeterminants.Hpk k r * X) = X := by
  rw [← Matrix.mul_assoc, _root_.GlobalTheory.CompanionTheory.ZuckCasSplit.hpk_sq, Matrix.one_mul]

private lemma hpk_conjTranspose_eq_self' : (_root_.Formalism.QuantumDeterminants.Hpk k r)ᴴ = _root_.Formalism.QuantumDeterminants.Hpk k r :=
  _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_conjTranspose

private lemma adjugate_upUni_last_apply {m : ℕ} {U : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ}
    (hU : _root_.GlobalTheory.LeadingMinorInv.UpUni U) (a : Fin (m + 1)) :
    U.adjugate (Fin.last m) a = if a = Fin.last m then 1 else 0 := by
  rw [adjugate_apply, det_of_upperTriangular]
  · simp [updateRow_apply, Pi.single_apply, hU.2]
  · intro i j hij
    simp only [updateRow_apply]
    split_ifs with h
    · subst h
      rw [Pi.single_apply, if_neg]
      exact (hij.trans_le (Fin.le_last _)).ne
    · exact hU.1 i j hij

private lemma flagMat_mulVec_eq_sum_smul_fvec (z : Fin (2 * r + k + 1) → ℂ) (c : Fin (r + 1) → ℂ) :
    _root_.GlobalTheory.LeadingMinorInv.flagMat k r z *ᵥ c = ∑ a, c a • _root_.Formalism.QuantumDeterminants.fvec k r z a := by
  ext i
  simp [mulVec, dotProduct, _root_.GlobalTheory.LeadingMinorInv.flagMat, Finset.sum_apply, mul_comm]

private lemma rW_mulVec_adjugate_zhat_single_last_eq (z z' : Fin (2 * r + k + 1) → ℂ) (g : _root_.Formalism.FourierDecayAlt.Q.Mx k r) :
    _root_.GlobalTheory.WigSh.omg k r z z' g = _root_.Formalism.FourierDecayAlt.D.prW k r z'
      ((_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z) *ᵥ
        ((_root_.Formalism.QuantumDeterminants.Zhat k r z z' g).adjugateᴴ *ᵥ Pi.single (Fin.last r) 1)) := by
  unfold _root_.GlobalTheory.WigSh.omg
  rw [← mulVec_mulVec _ (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.GlobalTheory.LeadingMinorInv.flagMat k r z), flagMat_mulVec_eq_sum_smul_fvec]
  simp [mulVec_single_one, conjTranspose_apply]

private lemma gram_eq_conjTranspose_hpk_mul_flagMat_mul (z z' : Fin (2 * r + k + 1) → ℂ) (g : _root_.Formalism.FourierDecayAlt.Q.Mx k r) :
    _root_.Formalism.QuantumDeterminants.Zhat k r z z' g = (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z)ᴴ *
      (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z') := by
  rw [_root_.GlobalTheory.LeadingMinorInv.zhat_eq]
  simp only [conjTranspose_mul, conjTranspose_conjTranspose, hpk_conjTranspose_eq_self',
    Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (_root_.Formalism.QuantumDeterminants.Hpk k r) (_root_.Formalism.QuantumDeterminants.Hpk k r), _root_.GlobalTheory.CompanionTheory.ZuckCasSplit.hpk_sq, Matrix.one_mul]

private lemma prW_mulVec_eq_of_mem_nset_of_tail_eq_zero {z' : Fin (2 * r + k + 1) → ℂ} {m : _root_.Formalism.FourierDecayAlt.Q.Mx k r}
    (hm : m ∈ _root_.Formalism.QuantumDeterminants.Nset k r) {p : Fin (2 * r + k + 1) → ℂ}
    (hp : ∀ j : Fin (2 * r + k + 1), r + k < ↑j → p j = 0) :
    _root_.Formalism.FourierDecayAlt.D.prW k r z' (m *ᵥ p) = _root_.Formalism.FourierDecayAlt.D.prW k r z' p := by
  have hNC := ((_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.mem_Nset_iff m).1 hm).2
  have hb : (fun i : Fin (2 * r + k + 1) => if r ≤ ↑i ∧ ↑i ≤ r + k then (m *ᵥ p) i else 0) =
      (fun i : Fin (2 * r + k + 1) => if r ≤ ↑i ∧ ↑i ≤ r + k then p i else 0) := by
    ext i
    split_ifs with hi
    · simp only [mulVec, dotProduct]
      rw [Finset.sum_eq_single i]
      · rw [hNC i i hi.2 (min_le_left _ _)]
        simp
      · intro j _ hji
        by_cases hj : (j : ℕ) ≤ r + k
        · rw [hNC i j hj (le_trans (min_le_right _ _) hi.1), if_neg (Ne.symm hji)]
          simp
        · rw [hp j (by omega)]
          simp
      · simp
    · rfl
  simp only [_root_.Formalism.FourierDecayAlt.D.prW]
  rw [hb]

private lemma mulVec_adjugate_single_last_apply_eq_zero_of_lt (z' : Fin (2 * r + k + 1) → ℂ)
    (Q : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ) (j : Fin (2 * r + k + 1))
    (hj : r + k < ↑j) :
    (Q *ᵥ ((Qᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')).adjugateᴴ *ᵥ
      Pi.single (Fin.last r) 1)) j = 0 := by
  have hJP : ∀ (X : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) ℂ) i c,
      (_root_.Formalism.QuantumDeterminants.Hpk k r * X) i c = _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI k r i * X (_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI k r i) c := by
    intro X i c
    have hJa : ∀ i l, _root_.Formalism.QuantumDeterminants.Hpk k r i l =
        if l = _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI k r i then _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI k r i else 0 :=
      fun i l => _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.Hpk_apply i l
    rw [Matrix.mul_apply]
    simp only [hJa, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
  have hj2 := j.isLt
  obtain ⟨b, hb⟩ : ∃ b : Fin r, (b : ℕ) = 2 * r + k - j := ⟨⟨2 * r + k - j, by omega⟩, rfl⟩
  have hpi : _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI k r (_root_.Formalism.QuantumDeterminants.eI k r b) = j := by
    have hb2 := b.isLt
    apply Fin.ext
    rw [_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.piI_val, if_neg] <;> simp only [_root_.Formalism.QuantumDeterminants.eI] <;> omega
  have key : (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')ᴴ *
      (Q * (Qᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')).adjugateᴴ) =
      ((Qᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')).adjugate *
        (Qᴴ * (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')))ᴴ := by
    rw [conjTranspose_mul (adjugate _), conjTranspose_mul Qᴴ, conjTranspose_conjTranspose,
      Matrix.mul_assoc]
  have h1 := congrFun (congrFun key (Fin.castSucc b)) (Fin.last r)
  rw [adjugate_mul] at h1
  simp only [conjTranspose_apply, Matrix.smul_apply, one_apply,
    if_neg (Fin.castSucc_lt_last b).ne', smul_zero, star_zero] at h1
  rw [conjTranspose_mul, hpk_conjTranspose_eq_self', Matrix.mul_assoc, Matrix.mul_apply,
    Finset.sum_eq_single (_root_.Formalism.QuantumDeterminants.eI k r b)] at h1
  · rw [hJP, hpi] at h1
    have heps := _root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.epsI_mul_self (k := k) (r := r) (_root_.Formalism.QuantumDeterminants.eI k r b)
    have hF : (_root_.GlobalTheory.LeadingMinorInv.flagMat k r z')ᴴ (Fin.castSucc b) (_root_.Formalism.QuantumDeterminants.eI k r b) = 1 := by
      simp [conjTranspose_apply, _root_.GlobalTheory.LeadingMinorInv.flagMat, _root_.Formalism.QuantumDeterminants.fvec, _root_.Formalism.QuantumDeterminants.bvec]
    rw [hF, one_mul] at h1
    simp only [Matrix.one_apply, if_neg (Fin.castSucc_lt_last b).ne', smul_zero, star_zero] at h1
    rw [mulVec_mulVec]
    simp only [mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rcases mul_eq_zero.1 h1 with h | h
    · rw [h, zero_mul] at heps
      exact absurd heps zero_ne_one
    · exact h
  · intro l _ hl
    simp [conjTranspose_apply, _root_.GlobalTheory.LeadingMinorInv.flagMat, _root_.Formalism.QuantumDeterminants.fvec, _root_.Formalism.QuantumDeterminants.bvec, Pi.single_apply, hl]
  · simp
end

theorem _root_.GlobalTheory.WigSh.omg_mul_N : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ))
    (g m : _root_.Formalism.FourierDecayAlt.Q.Mx k r), _root_.Formalism.QuantumDeterminants.inWb k r z → _root_.Formalism.QuantumDeterminants.inWb k r z' →
    g ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r) → m ∈ _root_.Formalism.QuantumDeterminants.Nset k r →
    _root_.GlobalTheory.WigSh.omg k r z z' (g * m) = _root_.GlobalTheory.WigSh.omg k r z z' g := by
  intro k r z z' g m _ hz' _ hm
  obtain ⟨U, hU, hmF⟩ := _root_.GlobalTheory.LeadingMinorInv.exists_N k r z' hz' m hm
  have hmUH : m ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r) := ((_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.mem_Nset_iff m).1 hm).1
  have hQm : _root_.Formalism.QuantumDeterminants.Hpk k r * (g * m)ᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z =
      m⁻¹ * (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z) := by
    rw [inv_eq_hpk_mul_conjTranspose_mul_hpk_of_mem_UH hmUH]
    simp only [conjTranspose_mul, Matrix.mul_assoc, hpk_mul_hpk_mul_eq_self]
  have hC : (m⁻¹ * (_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z))ᴴ *
      (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z') =
      ((_root_.Formalism.QuantumDeterminants.Hpk k r * gᴴ * _root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z)ᴴ *
        (_root_.Formalism.QuantumDeterminants.Hpk k r * _root_.GlobalTheory.LeadingMinorInv.flagMat k r z')) * U := by
    rw [conjTranspose_mul m⁻¹, inv_eq_hpk_mul_conjTranspose_mul_hpk_of_mem_UH hmUH]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, hpk_conjTranspose_eq_self',
      Matrix.mul_assoc, hpk_mul_hpk_mul_eq_self, hmF]
  have he : U.adjugateᴴ *ᵥ Pi.single (Fin.last r) 1 = Pi.single (Fin.last r) 1 := by
    ext a
    simp [mulVec_single_one, conjTranspose_apply, adjugate_upUni_last_apply hU, Pi.single_apply]
  rw [rW_mulVec_adjugate_zhat_single_last_eq, rW_mulVec_adjugate_zhat_single_last_eq, gram_eq_conjTranspose_hpk_mul_flagMat_mul, gram_eq_conjTranspose_hpk_mul_flagMat_mul, hQm, hC, adjugate_mul_distrib, conjTranspose_mul,
    ← mulVec_mulVec _ (adjugate _)ᴴ, he, ← mulVec_mulVec _ m⁻¹]
  exact prW_mulVec_eq_of_mem_nset_of_tail_eq_zero ((_root_.PI.QuotSetU.UnitaryGroupMassFormula.SW.nilpotent_subgroup k r).2.2 m hm)
    (mulVec_adjugate_single_last_apply_eq_zero_of_lt _ _)

end GlobalTheory.WigSh
end
end
