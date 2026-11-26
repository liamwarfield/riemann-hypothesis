module

public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedRingOfIntegers
set_option autoImplicit false

noncomputable section

open TensorProduct

namespace GlobalTheory.Serre

section Eigen

variable {R O O' : Type*} [CommRing R] [CommRing O] [CommRing O'] [Algebra O O'] [Algebra O R]
  [Algebra O' R] [IsScalarTower O O' R]


variable (R O O') in
def mulChar : R ⊗[O] O' →ₐ[R] R :=
  Algebra.TensorProduct.lift (AlgHom.id R R) (IsScalarTower.toAlgHom O O' R) fun _ _ ↦ .all _ _

@[simp] theorem mulChar_tmul (r : R) (x : O') :
    mulChar (R := R) (O := O) (O' := O') (r ⊗ₜ x) = r * algebraMap O' R x := rfl

theorem exists_elem_of_unramified {A : Type*} [CommRing A] [Algebra R A]
    [Algebra.FormallyUnramified R A] [Algebra.EssFiniteType R A] (χ : A →ₐ[R] R) :
    ∃ e : A, χ e = 1 ∧ ∀ x, x * e = χ x • e := by
  let f : A ⊗[R] A →ₐ[R] A :=
    Algebra.TensorProduct.lift ((Algebra.ofId R A).comp χ) (AlgHom.id R A) fun _ _ ↦ .all _ _
  refine ⟨f (Algebra.FormallyUnramified.elem R A), ?_, fun x ↦ ?_⟩
  · have : ∀ z, χ (f z) = χ (Algebra.TensorProduct.lmul' R z) := fun z ↦ by
      induction z with
      | tmul x y => simp [f]
      | add z w hz hw => simp only [map_add (f := _), hz, hw]
    rw [this, Algebra.FormallyUnramified.lmul_elem, map_one]
  · simpa [f, Algebra.smul_def] using
      congrArg f (Algebra.FormallyUnramified.one_tmul_mul_elem (R := R) x)

variable {M : Type*} [AddCommGroup M] [Module O M] [Module O' M] [IsScalarTower O O' M]

theorem exists_eigen_of_unramified (N : Type*) [AddCommGroup N] [Module R N] [Module O N]
    [Module O' N] [IsScalarTower O R N] [IsScalarTower O' R N] [IsScalarTower O O' N]
    [Algebra.FormallyUnramified R (R ⊗[O] O')] [Algebra.EssFiniteType R (R ⊗[O] O')] :
    ∃ s : N ⊗[O'] M →ₗ[R] N ⊗[O] M, Function.Injective s ∧ ∀ z, z ∈ LinearMap.range s ↔
      ∀ x : O', (Algebra.lsmul O O M x).lTensor N z = algebraMap O' R x • z := by
  obtain ⟨e, he₁, he₂⟩ := exists_elem_of_unramified (mulChar (R := R) (O := O) (O' := O'))
  let g : O' →ₐ[O] Module.End R (N ⊗[O] M) :=
    { toFun x := AlgebraTensorModule.lTensor R N (Algebra.lsmul O O M x)
      map_one' := by ext; simp
      map_mul' x y := by ext; simp
      map_zero' := by ext; simp
      map_add' x y := by ext; simp
      commutes' x := by ext; simp }
  let ρ : R ⊗[O] O' →ₐ[R] Module.End R (N ⊗[O] M) :=
    Algebra.TensorProduct.lift (Algebra.ofId R _) g fun r x ↦ Algebra.commute_algebraMap_left _ _
  have hρ : ∀ (r : R) (x : O') z, ρ (r ⊗ₜ x) z = r • (Algebra.lsmul O O M x).lTensor N z :=
    fun r x z ↦ rfl
  have hρe : ∀ (x : O') z, (Algebra.lsmul O O M x).lTensor N (ρ e z) = algebraMap O' R x • ρ e z :=
    fun x z ↦ by
      have := congrArg (fun y ↦ ρ y z) (he₂ (1 ⊗ₜ x))
      simpa only [map_mul, map_smul, Module.End.mul_apply, hρ, one_smul, mulChar_tmul, one_mul,
        LinearMap.smul_apply] using this
  have hρe' : ∀ (x : O') z, ρ e ((Algebra.lsmul O O M x).lTensor N z) = algebraMap O' R x • ρ e z :=
    fun x z ↦ by
      have := congrArg (fun y ↦ ρ y z) ((mul_comm _ _).trans (he₂ (1 ⊗ₜ x)))
      simpa only [map_mul, map_smul, Module.End.mul_apply, hρ, one_smul, mulChar_tmul, one_mul,
        LinearMap.smul_apply] using this
  let s : N ⊗[O'] M →ₗ[R] N ⊗[O] M := AlgebraTensorModule.lift
    { toFun n :=
        { toFun m := ρ e (n ⊗ₜ m)
          map_add' m m' := by rw [tmul_add, map_add (f := _)]
          map_smul' x m := (hρe' x (n ⊗ₜ m)).trans (algebraMap_smul R x _) }
      map_add' n n' := LinearMap.ext fun m ↦ (congrArg (ρ e) (add_tmul n n' m)).trans (map_add _ _ _)
      map_smul' r n := LinearMap.ext fun m ↦ map_smul (ρ e) r (n ⊗ₜ m) }
  let q : N ⊗[O] M →ₗ[R] N ⊗[O'] M := mapOfCompatibleSMul O' O R N M
  have hq : ∀ y z, q (ρ y z) = mulChar (R := R) (O := O) (O' := O') y • q z := fun y z ↦ by
    induction y with
    | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, hy, hy', add_smul]
    | tmul r x =>
      induction z with
      | add z z' hz hz' => simp only [map_add (f := _), hz, hz', smul_add]
      | tmul n m => simp [hρ, q, mul_smul]
  have hqs : ∀ z, q (s z) = z := fun z ↦ by
    induction z with
    | add z z' hz hz' => simp only [map_add (f := _), hz, hz']
    | tmul n m => exact (hq e (n ⊗ₜ m)).trans (by rw [he₁, one_smul]; rfl)
  have hsq : ∀ z, s (q z) = ρ e z := fun z ↦ by
    induction z with
    | add z z' hz hz' => simp only [map_add (f := _), hz, hz']
    | tmul n m => rfl
  refine ⟨s, Function.LeftInverse.injective hqs, fun z ↦ ⟨?_, fun hz ↦ ⟨q z, ?_⟩⟩⟩
  · rintro ⟨z, rfl⟩ x
    rw [← hqs z, hsq, hρe]
  · have : ∀ y, ρ y z = mulChar (R := R) (O := O) (O' := O') y • z := fun y ↦ by
      induction y with
      | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, hy, hy', add_smul]
      | tmul r x => rw [hρ, hz, mulChar_tmul, mul_smul]
    rw [hsq, this, he₁, one_smul]


omit [Algebra O R] in
theorem exists_eigen_of_projective (M : Type*) [AddCommGroup M] [Module O M] [Module.Finite O M]
    [Module.Projective O M] {N L : Type*} [AddCommGroup N] [Module R N] [Module O N]
    [SMulCommClass O R N] [AddCommGroup L] [Module R L] [Module O L] [SMulCommClass O R L]
    (τ : O → R) (i : N →ₗ[R] L) (hi : Function.Injective i)
    (hlin : ∀ (x : O) n, i (x • n) = x • i n)
    (hr : ∀ l, l ∈ LinearMap.range i ↔ ∀ x : O, x • l = τ x • l) :
    ∃ j : N ⊗[O] M →ₗ[R] L ⊗[O] M, (∀ n m, j (n ⊗ₜ m) = i n ⊗ₜ m) ∧ Function.Injective j ∧
      ∀ z, z ∈ LinearMap.range j ↔ ∀ x : O, x • z = τ x • z := by
  let i' : N →ₗ[O] L := { i.toAddHom with map_smul' := hlin }
  let j : N ⊗[O] M →ₗ[R] L ⊗[O] M :=
    { (i'.rTensor M).toAddHom with
      map_smul' := fun r z ↦ by
        change i'.rTensor M (r • z) = r • i'.rTensor M z
        induction z with
        | add z z' hz hz' => simp only [smul_add, map_add (f := _), hz, hz']
        | tmul n m => simp [smul_tmul', i'] }
  refine ⟨j, fun _ _ ↦ rfl, Module.Flat.rTensor_preserves_injective_linearMap i' hi,
    fun z ↦ ⟨?_, fun hz ↦ ?_⟩⟩
  · rintro ⟨z, rfl⟩ x
    induction z with
    | add z z' hz hz' => simp only [smul_add, map_add (f := _), hz, hz']
    | tmul n m =>
      change (x • i n) ⊗ₜ[O] m = (τ x • i n) ⊗ₜ[O] m
      rw [(hr _).mp ⟨n, rfl⟩]
  · obtain ⟨n, t, s, -, -, hst⟩ := Module.Finite.exists_comp_eq_id_of_projective O M
    let c (k : Fin n) : L ⊗[O] M →ₗ[O] L :=
      (TensorProduct.rid O L).toLinearMap ∘ₗ (LinearMap.proj k ∘ₗ s).lTensor L
    have hc : ∀ k (r : R) z, c k (r • z) = r • c k z := fun k r z ↦ by
      induction z with
      | add z z' hz hz' => simp only [smul_add, map_add (f := _), hz, hz']
      | tmul l m => simpa [smul_tmul', c] using smul_comm _ r l
    have hsum : ∀ z, ∑ k, c k z ⊗ₜ[O] t (Pi.single k 1) = z := fun z ↦ by
      induction z with
      | add z z' hz hz' => simp only [map_add (f := _), add_tmul, Finset.sum_add_distrib, hz, hz']
      | tmul l m =>
        have hm : t (s m) = m := congr($hst m)
        conv_rhs => rw [← hm, pi_eq_sum_univ' (s m)]
        simp [c, smul_tmul, tmul_sum]
    choose u hu using fun k ↦ (hr (c k z)).mpr fun x ↦ by rw [← map_smul, hz, hc]
    refine ⟨∑ k, u k ⊗ₜ t (Pi.single k 1), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← hsum z]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [← hu]; rfl

theorem exists_eigen_tensor [Module.Finite O M] [Module.Projective O M]
    {N L : Type*} [AddCommGroup N] [Module R N] [Module O N]
    [Module O' N] [IsScalarTower O R N] [IsScalarTower O' R N] [IsScalarTower O O' N]
    [Algebra.FormallyUnramified R (R ⊗[O] O')] [Algebra.EssFiniteType R (R ⊗[O] O')]
    [AddCommGroup L] [Module R L] [Module O L] [SMulCommClass O R L]
    (i : N →ₗ[R] L) (hi : Function.Injective i)
    (hr : ∀ l, l ∈ LinearMap.range i ↔ ∀ x : O, x • l = algebraMap O R x • l) :
    ∃ s : N ⊗[O'] M →ₗ[R] L ⊗[O] M, Function.Injective s ∧ ∀ z, z ∈ LinearMap.range s ↔
      ∀ x : O', (Algebra.lsmul O O M x).lTensor L z = algebraMap O' R x • z := by
  obtain ⟨s, hs₁, hs₂⟩ := exists_eigen_of_unramified (R := R) (O := O) (O' := O') (M := M) N
  obtain ⟨j, hj₀, hj₁, hj₂⟩ := exists_eigen_of_projective M (algebraMap O R) i hi
    (fun x n ↦ by rw [(hr _).mp ⟨n, rfl⟩, ← map_smul, algebraMap_smul]) hr
  have hj : ∀ (x : O') z, j ((Algebra.lsmul O O M x).lTensor N z) =
      (Algebra.lsmul O O M x).lTensor L (j z) := fun x z ↦ by
    induction z with
    | add z z' hz hz' => simp only [map_add (f := _), hz, hz']
    | tmul n m => simp [hj₀]
  refine ⟨j ∘ₗ s, hj₁.comp hs₁, fun z ↦ ⟨?_, fun hz ↦ ?_⟩⟩
  · rintro ⟨w, rfl⟩ x
    rw [LinearMap.comp_apply, ← hj, (hs₂ _).mp ⟨w, rfl⟩, map_smul]
  · obtain ⟨w, rfl⟩ := (hj₂ z).mpr fun x ↦ by
      rw [IsScalarTower.algebraMap_apply O O' R, ← hz, AlgHom.commutes]
      simp [Module.algebraMap_end_eq_smul_id]
    obtain ⟨v, rfl⟩ := (hs₂ w).mpr fun x ↦ hj₁ (by rw [hj, hz, map_smul])
    exact ⟨v, rfl⟩

end Eigen

section Integers

open NumberField

variable (k K E : Type*) [Field k] [CharZero k] [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E]


omit [NumberField K] in
theorem ringOfIntegers_injective (τ : 𝓞 K →+* k) : Function.Injective τ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
  rw [Ideal.under_def, RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  exact RingHom.injective_int _

theorem formallyUnramified_ringOfIntegers [Algebra (𝓞 K) k] :
    Algebra.FormallyUnramified k (k ⊗[𝓞 K] 𝓞 E) := by
  have hinj := ringOfIntegers_injective k K (algebraMap (𝓞 K) k)
  let : Algebra K k := (IsFractionRing.lift hinj).toAlgebra
  have : IsScalarTower (𝓞 K) K k :=
    .of_algebraMap_eq fun x ↦ (IsFractionRing.lift_algebraMap hinj x).symm
  have : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors (𝓞 K))) E :=
    IsIntegralClosure.isLocalization (𝓞 K) K E (𝓞 E)
  have : Algebra.IsPushout (𝓞 K) K (𝓞 E) E :=
    (Algebra.isPushout_of_isLocalization (nonZeroDivisors (𝓞 K)) K (𝓞 E) E).symm
  have : Algebra.FormallyUnramified K E := Algebra.FormallyUnramified.of_isSeparable K E
  have : Algebra.FormallyUnramified K (K ⊗[𝓞 K] 𝓞 E) :=
    .of_equiv (Algebra.IsPushout.equiv (𝓞 K) K (𝓞 E) E).symm
  exact .of_equiv (Algebra.TensorProduct.cancelBaseChange (𝓞 K) K k k (𝓞 E))



end Integers

theorem iSupIndep_eigen {k V I : Type*} [Field k] [AddCommGroup V] [Module k V]
    (f : I → Module.End k V) (hf : ∀ i j, Commute (f i) (f j)) :
    iSupIndep fun χ : I → k ↦ ⨅ i, (f i).eigenspace (χ i) :=
  (Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f fun i j φ ↦
    Module.End.mapsTo_maxGenEigenspace_of_comm (hf j i) φ).mono fun _ ↦
      iInf_mono fun i ↦ ((f i).genEigenspace _).monotone le_top

end GlobalTheory.Serre
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding epsScale
open GlobalTheory.GrpTangent

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Serre

section Lie

variable {R : Type} [CommRing R] {O O' O'' : Type} [CommRing O] [CommRing O'] [CommRing O'']
  {G H K : Over (Sp R)} [GrpObj G] [GrpObj H] [GrpObj K]
  [IsCommMonObj G] [IsCommMonObj H] [IsCommMonObj K]

def tangentSub (a : OAct O G) : Submodule O (Pts a (epsR R)) :=
  (LinearMap.ker (Pts.pre a (epsZero R))).copy {x | IsTangent x.hom}
    (Set.ext fun x ↦ (isTangent_iff x.hom).trans ⟨fun h ↦ Pts.ext h, fun h ↦ congrArg Pts.hom h⟩)

def Lie (a : OAct O G) : Type := tangentSub a

namespace Lie

variable {a : OAct O G} {b : OAct O' H} {c : OAct O'' K}

instance : AddCommGroup (Lie a) := inferInstanceAs (AddCommGroup (tangentSub a))

instance actModule : Module O (Lie a) := inferInstanceAs (Module O (tangentSub a))

def toPts (a : OAct O G) : Lie a →ₗ[O] Pts a (epsR R) := (tangentSub a).subtype

def hom (v : Lie a) : epsR R ⟶ G := (toPts a v).hom

@[simp] theorem hom_toPts (v : Lie a) : (toPts a v).hom = v.hom := rfl

theorem isTangent (v : Lie a) : IsTangent v.hom := v.2

def mk (a : OAct O G) (w : epsR R ⟶ G) (hw : IsTangent w) : Lie a := ⟨Pts.mk a w, hw⟩

@[simp] theorem hom_mk (w : epsR R ⟶ G) (hw : IsTangent w) : (mk a w hw).hom = w := rfl

@[ext] theorem ext {v w : Lie a} (h : v.hom = w.hom) : v = w := Subtype.ext h

@[simp] theorem hom_zero : (0 : Lie a).hom = 1 := rfl

@[simp] theorem hom_add (v w : Lie a) : (v + w).hom = v.hom * w.hom := rfl

@[simp] theorem hom_act_smul (x : O) (v : Lie a) : (x • v).hom = v.hom ≫ a.act x := rfl

theorem hom_sum {I : Type*} (s : Finset I) (v : I → Lie a) :
    (∑ i ∈ s, v i).hom = ∏ i ∈ s, (v i).hom := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hom_toPts, map_sum, Pts.hom_sum]; rfl

instance baseModule : Module R (Lie a) where
  smul r v := mk a (epsScale r ≫ v.hom) (isTangent_epsScale r v.isTangent)
  one_smul v := ext (by
    change epsScale 1 ≫ v.hom = _
    rw [epsScale_one, Category.id_comp])
  mul_smul r s v := ext (epsScale_mul_assoc r s v.hom).symm
  smul_zero r := ext (MonObj.comp_one (epsScale r))
  smul_add r v w := ext (MonObj.comp_mul (epsScale r) v.hom w.hom)
  add_smul r s v := ext (epsScale_add_comp r s v.isTangent)
  zero_smul v := ext (epsScale_zero_comp v.isTangent)

@[simp] theorem hom_smul (r : R) (v : Lie a) : (r • v).hom = epsScale r ≫ v.hom := rfl

theorem hom_smul_left (r : R) (v : Lie a) :
    (r • v).hom.left = spMap (epsScaleR r) ≫ v.hom.left := rfl

instance smulCommClass : SMulCommClass R O (Lie a) :=
  ⟨fun r x v ↦ ext (Category.assoc (epsScale r) v.hom (a.act x)).symm⟩

instance smulCommClass' : SMulCommClass O R (Lie a) := SMulCommClass.symm _ _ _

def map (a : OAct O G) (b : OAct O' H) (f : G ⟶ H) [IsMonHom f] : Lie a →ₗ[R] Lie b where
  toFun v := mk b (v.hom ≫ f) (isTangent_comp v.isTangent f)
  map_add' v w := ext (MonObj.mul_comp v.hom w.hom f)
  map_smul' r v := ext (Category.assoc (epsScale r) v.hom f)

@[simp] theorem hom_map (f : G ⟶ H) [IsMonHom f] (v : Lie a) : (map a b f v).hom = v.hom ≫ f := rfl

theorem map_act (x : O) [IsMonHom (a.act x)] (v : Lie a) : map a a (a.act x) v = x • v := rfl

theorem map_act_smul {b : OAct O H} {f : G ⟶ H} [IsMonHom f] (hf : IsLinearHom a b f) (x : O)
    (v : Lie a) : map a b f (x • v) = x • map a b f v := by ext; simp [hf.comm]

def mapLinear {b : OAct O H} {f : G ⟶ H} (hf : IsLinearHom a b f) : Lie a →ₗ[O] Lie b :=
  haveI := hf.isMonHom
  { (map a b f).toAddHom with map_smul' := map_act_smul hf }

def changeAct (a : OAct O G) (a' : OAct O' G) : Lie a ≃ₗ[R] Lie a' :=
  LinearEquiv.ofLinearMap (map a a' (𝟙 G)) (map a' a (𝟙 G)) (by ext; simp) (by ext; simp)

def proj (a : OAct O G) : Pts a (epsR R) →ₗ[O] Lie a :=
  LinearMap.codRestrict (tangentSub a) (LinearMap.id - Pts.pre a (toUnit _ ≫ epsZero R)) fun x ↦ by
    refine (isTangent_iff _).mpr ?_
    change epsZero R ≫ (x.hom / ((toUnit _ ≫ epsZero R) ≫ x.hom)) = 1
    rw [div_eq_mul_inv, MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc,
      toUnit_unique (epsZero R ≫ toUnit _) (𝟙 _), Category.id_comp, mul_inv_cancel]

theorem toPts_comp_proj :
    toPts a ∘ₗ proj a = LinearMap.id - Pts.pre a (toUnit _ ≫ epsZero R) := rfl

theorem pre_toPts (v : Lie a) : Pts.pre a (toUnit (epsR R) ≫ epsZero R) (toPts a v) = 0 :=
  Pts.ext (by
    rw [Pts.hom_pre, Category.assoc, hom_toPts, (isTangent_iff _).mp v.isTangent, MonObj.comp_one,
      Pts.hom_zero])

theorem proj_comp_toPts : proj a ∘ₗ toPts a = LinearMap.id :=
  LinearMap.ext fun v ↦ Subtype.ext (by
    change toPts a v - Pts.pre a _ (toPts a v) = toPts a v
    rw [pre_toPts, sub_zero])

theorem isLieComb_iff {n : ℕ} (r : Fin n → R) (v : Fin n → Lie a) (w : epsR R ⟶ G) :
    IsLieComb r (fun i ↦ (v i).hom) w ↔ w = (∑ i, r i • v i).hom := by
  rw [hom_sum, ← List.prod_ofFn]
  refine ⟨?_, fun h ↦ ⟨_, fun _ ↦ rfl, h⟩⟩
  rintro ⟨u, hu, rfl⟩
  obtain rfl : u = fun i ↦ (r i • v i).hom := funext fun i ↦ Over.OverMorphism.ext (hu i)
  rfl

theorem isLieBasis_iff {n : ℕ} (v : Fin n → Lie a) :
    IsLieBasis (fun i ↦ (v i).hom) ↔ Function.Bijective (Fintype.linearCombination R v) := by
  rw [Function.bijective_iff_existsUnique]
  simp only [IsLieBasis, isLieComb_iff, Fintype.linearCombination_apply]
  refine ⟨fun h w ↦ (existsUnique_congr fun r ↦ ⟨fun e ↦ ext e.symm, fun e ↦ by rw [e]⟩).mp
      (h.2 w.hom w.isTangent), fun h ↦ ⟨fun i ↦ (v i).isTangent, fun w hw ↦ ?_⟩⟩
  exact (existsUnique_congr fun r ↦ ⟨fun e ↦ by rw [e, hom_mk], fun e ↦ ext e.symm⟩).mp
    (h (mk a w hw))

def basis (a : OAct O G) {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) :
    Module.Basis (Fin n) R (Lie a) :=
  Module.Basis.ofEquivFun
    (LinearEquiv.ofBijective _ ((isLieBasis_iff fun i ↦ mk a (v i) (hv.1 i)).mp hv)).symm

@[simp] theorem hom_basis {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v) (i : Fin n) :
    (basis a hv i).hom = v i := by
  simp [basis, Module.Basis.coe_ofEquivFun]

theorem isLieBasis_basis {n : ℕ} (v : Module.Basis (Fin n) R (Lie a)) :
    IsLieBasis fun i ↦ (v i).hom := by
  rw [isLieBasis_iff]
  convert v.equivFun.symm.bijective using 1
  ext r
  simp [Fintype.linearCombination_apply]

theorem map_kernel {i : K ⟶ G} {f : G ⟶ H} [IsMonHom i] [IsMonHom f]
    (h : IsPullback i (toUnit K) f η[H]) :
    Function.Injective (map c a i) ∧ Function.Exact (map c a i) (map a b f) := by
  have hinj : ∀ {T : Over (Sp R)} {x y : T ⟶ K}, x ≫ i = y ≫ i → x = y :=
    fun e ↦ h.hom_ext e (toUnit_unique _ _)
  refine ⟨fun v w e ↦ ext (hinj (congrArg hom e)), fun w ↦ ⟨fun e ↦ ?_, ?_⟩⟩
  · have e' : w.hom ≫ f = toUnit _ ≫ η[H] := congrArg hom e
    refine ⟨mk c (h.lift w.hom (toUnit _) e') ((isTangent_iff _).mpr (hinj ?_)),
      ext (h.lift_fst _ _ _)⟩
    rw [Category.assoc, h.lift_fst, MonObj.one_comp]
    exact (isTangent_iff _).mp w.isTangent
  · rintro ⟨v, rfl⟩
    ext
    simp only [hom_map, Category.assoc, h.w, hom_zero]
    rw [← Category.assoc, toUnit_unique (v.hom ≫ toUnit K) (toUnit _)]
    rfl

end Lie

namespace IsTensor

variable {G' H' : Over (Sp R)} [GrpObj G'] [GrpObj H'] [IsCommMonObj G'] [IsCommMonObj H']
  {a : OAct O G} {b : OAct O H} {a' : OAct O G'} {b' : OAct O H'}
  {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
  (h : IsTensor H b G a M)

def lieMap : M ⊗[O] Lie a →ₗ[O] Lie b :=
  TensorProduct.lift (LinearMap.mk₂ O (fun m v ↦ Lie.mapLinear (h.isLinearHom_tmul m) v)
    (fun m n v ↦ Lie.ext (by
      change v.hom ≫ h.tmul (m + n) = (v.hom ≫ h.tmul m) * (v.hom ≫ h.tmul n)
      rw [h.tmul_add, MonObj.comp_mul]))
    (fun x m v ↦ Lie.ext (by
      change v.hom ≫ h.tmul (x • m) = (v.hom ≫ h.tmul m) ≫ b.act x
      rw [h.tmul_smul, Category.assoc]))
    (fun m v w ↦ map_add _ _ _) (fun x m v ↦ map_smul _ _ _))

theorem toPts_lieMap (z : M ⊗[O] Lie a) :
    Lie.toPts b (h.lieMap z) = h.equiv (epsR R) ((Lie.toPts a).lTensor M z) := by
  induction z with
  | tmul m v =>
    apply Pts.ext
    exact (h.hom_equiv_tmul m (Lie.toPts a v)).symm
  | add z w hz hw => simp only [map_add (f := _), hz, hw]

def lieEquiv : M ⊗[O] Lie a ≃ₗ[O] Lie b :=
  LinearEquiv.ofLinearMap h.lieMap
    ((Lie.proj a).lTensor M ∘ₗ (h.equiv (epsR R)).symm.toLinearMap ∘ₗ Lie.toPts b)
    (LinearMap.ext fun w ↦ Subtype.ext (by
      change Lie.toPts b (h.lieMap _) = Lie.toPts b w
      simp only [toPts_lieMap, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [← LinearMap.lTensor_comp_apply, Lie.toPts_comp_proj, LinearMap.lTensor_sub,
        LinearMap.sub_apply, ← h.natural_symm, Lie.pre_toPts]
      simp))
    (LinearMap.ext fun z ↦ by
      simp only [toPts_lieMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
      rw [← LinearMap.lTensor_comp_apply, Lie.proj_comp_toPts, LinearMap.lTensor_id])

def lieEquivBase (b₁ : OAct O' H) : Lie a ⊗[O] M ≃ₗ[R] Lie b₁ :=
  ({ (TensorProduct.comm O (Lie a) M ≪≫ₗ h.lieEquiv).toAddEquiv with
    map_smul' := fun r z ↦ by
      change h.lieEquiv (TensorProduct.comm O _ _ (r • z)) =
        r • h.lieEquiv (TensorProduct.comm O _ _ z)
      induction z with
      | tmul v m =>
        rw [smul_tmul']
        apply Lie.ext
        change (epsScale r ≫ v.hom) ≫ h.tmul m = epsScale r ≫ (v.hom ≫ h.tmul m)
        exact Category.assoc _ _ _
      | add z w hz hw => simp only [map_add (f := _), smul_add, hz, hw] } :
    Lie a ⊗[O] M ≃ₗ[R] Lie b) ≪≫ₗ Lie.changeAct b b₁

@[simp] theorem hom_lieEquivBase_tmul (b₁ : OAct O' H) (v : Lie a) (m : M) :
    (h.lieEquivBase b₁ (v ⊗ₜ m)).hom = v.hom ≫ h.tmul m :=
  Category.comp_id (X := epsR R) _

section Algebra

variable [Algebra O O'] [Module O' M] [IsScalarTower O O' M]


theorem lieEquivBase_smul (x : O') (z : Lie a ⊗[O] M) :
    h.lieEquivBase (h.algAct O') ((Algebra.lsmul O O M x).lTensor _ z) =
      x • h.lieEquivBase (h.algAct O') z := by
  induction z with
  | tmul v m =>
    apply Lie.ext
    simp only [LinearMap.lTensor_tmul, Algebra.lsmul_apply, hom_lieEquivBase_tmul,
      Lie.hom_act_smul, Category.assoc, h.tmul_algAct]
  | add z w hz hw => simp only [map_add (f := _), smul_add, hz, hw]

end Algebra

end IsTensor

end Lie

section Eigen

variable {R : Type} [CommRing R] {O O' : Type} [CommRing O] [CommRing O']
  {G H : Over (Sp R)} [GrpObj G] [GrpObj H] [IsCommMonObj G] [IsCommMonObj H]

namespace Lie

variable {a : OAct O G}

def eig (a : OAct O G) (τ : O →+* R) : Submodule R (Lie a) where
  carrier := {v | ∀ x : O, x • v = τ x • v}
  add_mem' {v w} hv hw x := by rw [smul_add, smul_add, hv, hw]
  zero_mem' x := by rw [smul_zero, smul_zero]
  smul_mem' r v hv x := by rw [smul_comm, hv, smul_comm]

theorem mem_eig_iff {τ : O →+* R} {v : Lie a} : v ∈ eig a τ ↔ ∀ x : O, x • v = τ x • v := Iff.rfl

theorem mem_eig_iff_left {τ : O →+* R} {v : Lie a} : v ∈ eig a τ ↔
    ∀ x : O, (v.hom ≫ a.act x).left = spMap (epsScaleR (τ x)) ≫ v.hom.left :=
  forall_congr' fun _ ↦ ⟨fun h ↦ congrArg (fun w : Lie a ↦ w.hom.left) h,
    fun h ↦ ext (Over.OverMorphism.ext h)⟩

theorem eig_eq_top {τ : O →+* R} {n : ℕ} {v : Fin n → (epsR R ⟶ G)} (hv : IsLieBasis v)
    (hτ : ∀ i x, (v i ≫ a.act x).left = spMap (epsScaleR (τ x)) ≫ (v i).left) : eig a τ = ⊤ := by
  rw [eq_top_iff, ← (basis a hv).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact mem_eig_iff_left.mpr (by simpa only [hom_basis] using hτ i)

end Lie

namespace IsTensor

variable {a : OAct O G} {b : OAct O H} {M : Type} [AddCommGroup M] [Module O M]
  (h : IsTensor H b G a M) [Algebra O R]

def lieEquivScalar (b₁ : OAct O' H) {N : Type} [AddCommGroup N] [Module R N] [Module O N]
    [IsScalarTower O R N] (e : N ≃ₗ[R] Lie a) (hτ : Lie.eig a (algebraMap O R) = ⊤) :
    N ⊗[O] M ≃ₗ[R] Lie b₁ :=
  haveI : IsScalarTower O R (Lie a) := ⟨fun x r v ↦ by
    rw [Algebra.smul_def, mul_smul, Lie.mem_eig_iff.mp (hτ.ge Submodule.mem_top) x]⟩
  AlgebraTensorModule.congr e (LinearEquiv.refl O M) ≪≫ₗ h.lieEquivBase b₁

@[simp] theorem hom_lieEquivScalar_tmul (b₁ : OAct O' H) {N : Type} [AddCommGroup N] [Module R N]
    [Module O N] [IsScalarTower O R N] (e : N ≃ₗ[R] Lie a) (hτ : Lie.eig a (algebraMap O R) = ⊤)
    (n : N) (m : M) : (h.lieEquivScalar b₁ e hτ (n ⊗ₜ m)).hom = (e n).hom ≫ h.tmul m :=
  h.hom_lieEquivBase_tmul b₁ (e n) m

def lieEquivLine (b₁ : OAct O' H) {v : epsR R ⟶ G} (hv : IsLieBasis ![v])
    (hτ : ∀ x, (v ≫ a.act x).left = spMap (epsScaleR (algebraMap O R x)) ≫ v.left) :
    R ⊗[O] M ≃ₗ[R] Lie b₁ :=
  h.lieEquivScalar b₁ ((Lie.basis a hv).equivFun ≪≫ₗ LinearEquiv.funUnique (Fin 1) R R).symm
    (Lie.eig_eq_top hv fun i ↦ by rw [Subsingleton.elim i 0]; exact hτ)

@[simp] theorem hom_lieEquivLine_tmul (b₁ : OAct O' H) {v : epsR R ⟶ G} (hv : IsLieBasis ![v])
    (hτ : ∀ x, (v ≫ a.act x).left = spMap (epsScaleR (algebraMap O R x)) ≫ v.left) (r : R) (m : M) :
    (h.lieEquivLine b₁ hv hτ (r ⊗ₜ m)).hom = epsScale r ≫ v ≫ h.tmul m := by
  simp [lieEquivLine]

variable [Algebra O O'] [Module O' M] [IsScalarTower O O' M]

theorem nonempty_eig_equiv [Algebra O' R] [IsScalarTower O O' R] [Module.Finite O M]
    [Module.Projective O M] [Algebra.FormallyUnramified R (R ⊗[O] O')]
    [Algebra.EssFiniteType R (R ⊗[O] O')] {N : Type} [AddCommGroup N] [Module R N] [Module O N]
    [Module O' N] [IsScalarTower O R N] [IsScalarTower O' R N] [IsScalarTower O O' N]
    (e : N ≃ₗ[R] Lie.eig a (algebraMap O R)) :
    Nonempty (N ⊗[O'] M ≃ₗ[R] Lie.eig (h.algAct O') (algebraMap O' R)) := by
  obtain ⟨s, hs₁, hs₂⟩ := exists_eigen_tensor (O := O) (O' := O') (M := M)
    ((Lie.eig a (algebraMap O R)).subtype ∘ₗ e.toLinearMap) (Subtype.val_injective.comp e.injective)
    fun l ↦ by
      rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_subtype_top]; rfl
  let F := (h.lieEquivBase (h.algAct O')).toLinearMap ∘ₗ s
  refine ⟨LinearEquiv.ofInjective F ((h.lieEquivBase _).injective.comp hs₁) ≪≫ₗ
    LinearEquiv.ofEq _ _ (Submodule.ext fun w ↦ ?_)⟩
  obtain ⟨z, rfl⟩ := (h.lieEquivBase (h.algAct O')).surjective w
  simp only [Lie.mem_eig_iff, ← h.lieEquivBase_smul, ← map_smul, EmbeddingLike.apply_eq_iff_eq,
    ← hs₂]
  exact exists_congr fun y ↦ (h.lieEquivBase (h.algAct O')).injective.eq_iff

end IsTensor

end Eigen

section Mult

variable {k : Type} [Field k] {O O' : Type} [CommRing O] [CommRing O']

theorem IsLinearPullback.id {S : Scheme.{0}} {G : Over S} [GrpObj G] (a : OAct O G) :
    IsLinearPullback a a (𝟙 S) (𝟙 G.left) :=
  haveI : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  ⟨isGrpPullback_of_iso (Iso.refl G), fun _ ↦ by simp⟩

namespace Lie

variable {G₁ : Over (Sp k)} [GrpObj G₁] [IsCommMonObj G₁] (a₁ : OAct O G₁)

theorem iSupIndep_eig : iSupIndep (eig a₁) := by
  have h := (iSupIndep_eigen (fun x : O ↦ DistribSMul.toLinearMap k (Lie a₁) x)
    fun x y ↦ LinearMap.ext fun v ↦ smul_comm x y v).comp
      (DFunLike.coe_injective (F := O →+* k))
  refine h.mono fun τ v hv ↦ ?_
  simp only [Function.comp, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  exact hv

theorem lieMult_id_iff (τ : O →+* k) (n : ℕ) :
    LieMult a₁ (𝟙 (Sp k)) τ n ↔ Nonempty (Module.Basis (Fin n) k (eig a₁ τ)) := by
  obtain ⟨e, he⟩ := LiePull.exists_pushEquiv (IsLinearPullback.id a₁).1 (epsR k)
    (spMap (algebraMap k (DualNumber k)) ≫ 𝟙 _) rfl
  replace he : ∀ x, (e x).left = x.left := fun x ↦ (he x).trans (Category.comp_id _)
  let P (v : epsR k ⟶ G₁) : Prop := IsTangent v ∧
    ∀ x : O, (v ≫ a₁.act x).left = spMap (epsScaleR (τ x)) ≫ v.left
  have hP : ∀ v, P v ↔ IsLieEigen a₁ (𝟙 _) τ (e v) := fun v ↦ by
    have : (1 : Over.mk (𝟙 (Sp k)) ⟶ G₁).left = η[G₁].left :=
      congrArg Over.Hom.left (one_eq_one (M := G₁)).symm
    simp only [IsLieEigen, Over.comp_left, he, this]
    rfl
  have hR : ∀ (c : k) (u v : epsR k ⟶ G₁), u.left = spMap (epsScaleR c) ≫ v.left ↔
      (e u).left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScale c) ≫ (e v).left := fun c u v ↦ by
    rw [he, he]; rfl
  have key : LieMult a₁ (𝟙 (Sp k)) τ n ↔ ∃ v : Fin n → (epsR k ⟶ G₁), (∀ i, P (v i)) ∧
      ∀ w, P w → ∃! c : Fin n → k, IsLieComb c v w :=
    ⟨LiePull.basis_transport e.symm (P := IsLieEigen a₁ (𝟙 _) τ) (Q := P)
      (R := fun c u v ↦ u.left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScale c) ≫ v.left)
      (R' := fun c u v ↦ u.left = spMap (epsScaleR c) ≫ v.left)
      (fun v ↦ by rw [hP, e.apply_symm_apply])
      (fun c u v ↦ by rw [hR, e.apply_symm_apply, e.apply_symm_apply]) n,
    LiePull.basis_transport e (P := P) (Q := IsLieEigen a₁ (𝟙 _) τ)
      (R := fun c u v ↦ u.left = spMap (epsScaleR c) ≫ v.left)
      (R' := fun c u v ↦ u.left = spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScale c) ≫ v.left) hP hR n⟩
  have comb : ∀ (v : Fin n → eig a₁ τ) (w : eig a₁ τ) (c : Fin n → k),
      IsLieComb c (fun i ↦ (v i).1.hom) w.1.hom ↔ Fintype.linearCombination k v c = w :=
    fun v w c ↦ by
      rw [isLieComb_iff, Fintype.linearCombination_apply, Subtype.ext_iff, Submodule.coe_sum]
      exact ⟨fun h ↦ ext h.symm, fun h ↦ (congrArg hom h).symm⟩
  rw [key]
  constructor
  · rintro ⟨v, hv, H⟩
    let v' (i : Fin n) : eig a₁ τ := ⟨mk a₁ (v i) (hv i).1, mem_eig_iff_left.mpr (hv i).2⟩
    exact ⟨Module.Basis.ofEquivFun (LinearEquiv.ofBijective (Fintype.linearCombination k v')
      ((Function.bijective_iff_existsUnique _).mpr fun w ↦ (existsUnique_congr (comb v' w)).mp
        (H w.1.hom ⟨w.1.isTangent, mem_eig_iff_left.mp w.2⟩))).symm⟩
  · rintro ⟨v⟩
    refine ⟨fun i ↦ (v i).1.hom, fun i ↦ ⟨(v i).1.isTangent, mem_eig_iff_left.mp (v i).2⟩,
      fun w hw ↦ (existsUnique_congr (comb v ⟨mk a₁ w hw.1, mem_eig_iff_left.mpr hw.2⟩)).mpr ?_⟩
    refine (Function.bijective_iff_existsUnique _).mp ?_ _
    convert v.equivFun.symm.bijective using 1
    ext r
    simp [Fintype.linearCombination_apply]

variable {a₁} {S : Scheme.{0}} {G : Over S} [GrpObj G] {a : OAct O G} {t : Sp k ⟶ S}
  {φ : G₁.left ⟶ G.left}

theorem lieMult_iff_basis (hφ : IsLinearPullback a₁ a t φ) (τ : O →+* k) (n : ℕ) :
    LieMult a t τ n ↔ Nonempty (Module.Basis (Fin n) k (eig a₁ τ)) := by
  rw [← lieMult_id_iff, LiePull.lieMult_pull O _ _ G G₁ t φ a a₁ hφ.1 hφ.2, Category.id_comp]

theorem lieMult_iff_finrank (hφ : IsLinearPullback a₁ a t φ) (τ : O →+* k) (n : ℕ) :
    LieMult a t τ n ↔ Module.Finite k (eig a₁ τ) ∧ Module.finrank k (eig a₁ τ) = n := by
  rw [lieMult_iff_basis hφ]
  exact ⟨fun ⟨v⟩ ↦ ⟨.of_basis v, (Module.finrank_eq_card_basis v).trans (Fintype.card_fin n)⟩,
    fun ⟨_, h⟩ ↦ ⟨Module.finBasisOfFinrankEq _ _ h⟩⟩


end Lie

namespace IsTensor

variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H] [IsCommMonObj G] [IsCommMonObj H]

theorem isLinearPullback_algAct {a : OAct O G} {b : OAct O H} {M : Type} [AddCommGroup M]
    [Module O M] (h : IsTensor H b G a M) [Algebra O O'] [Module O' M] [IsScalarTower O O' M]
    {S' : Scheme.{0}} (f : S' ⟶ S) :
    IsLinearPullback ((h.pullback f).algAct O') (h.algAct O') f (pullback.fst H.hom f) :=
  ⟨isGrpPullback_pullback H f, fun _ ↦
    (congrArg (fun g ↦ g.left ≫ pullback.fst H.hom f) (h.pullback_mapLeft h f _)).trans
      (Limits.pullback.lift_fst _ _ _)⟩

theorem lieMult_of_unramified {a : OAct O G} {b : OAct O H} {M : Type} [AddCommGroup M]
    [Module O M] (h : IsTensor H b G a M) [Algebra O O'] [Module O' M] [IsScalarTower O O' M]
    [Module.Finite O M] [Module.Projective O M] [Algebra O k] [Algebra O' k] [IsScalarTower O O' k]
    [Algebra.FormallyUnramified k (k ⊗[O] O')] [Algebra.EssFiniteType k (k ⊗[O] O')]
    (t : Sp k ⟶ S) {n : ℕ} (hn : LieMult a t (algebraMap O k) n) :
    LieMult (h.algAct O') t (algebraMap O' k) (n * Module.finrank k (k ⊗[O'] M)) := by
  obtain ⟨v⟩ := (Lie.lieMult_iff_basis (isLinearPullback_pullback a t) _ _).mp hn
  obtain ⟨e⟩ := (h.pullback t).nonempty_eig_equiv (O' := O') v.equivFun.symm
  have : Module.Finite O' M := .of_restrictScalars_finite O O' M
  let e' := AlgebraTensorModule.cancelBaseChange O' k k (Fin n → k) M ≪≫ₗ e
  rw [Lie.lieMult_iff_finrank (h.isLinearPullback_algAct t)]
  refine ⟨.equiv e', ?_⟩
  rw [← e'.finrank_eq, Module.finrank_tensorProduct, Module.finrank_fin_fun]

open NumberField

variable [CharZero k] {K E : Type} [Field K] [Field E] [NumberField K] [NumberField E] [Algebra K E]
  {a : OAct (𝓞 K) G} {b : OAct (𝓞 K) H}

section Module

variable {M : Type} [AddCommGroup M] [Module (𝓞 K) M] [Module (𝓞 E) M]
  [IsScalarTower (𝓞 K) (𝓞 E) M] [Module.Finite (𝓞 E) M] [Module.Projective (𝓞 E) M]
  (h : IsTensor H b G a M)

theorem lieMult (t : Sp k ⟶ S) (τ : 𝓞 E →+* k) {n : ℕ}
    (hn : LieMult a t (τ.comp (algebraMap (𝓞 K) (𝓞 E))) n) :
    LieMult (h.algAct (𝓞 E)) t τ (n * Module.finrank (𝓞 E) M) := by
  let : Algebra (𝓞 E) k := τ.toAlgebra
  let : Algebra (𝓞 K) k := (τ.comp (algebraMap (𝓞 K) (𝓞 E))).toAlgebra
  have : IsScalarTower (𝓞 K) (𝓞 E) k := .of_algebraMap_eq' rfl
  have := formallyUnramified_ringOfIntegers k K E
  have : Module.Finite (𝓞 K) M := .trans (𝓞 E) M
  have : Module.Flat (𝓞 K) M := .trans (𝓞 K) (𝓞 E) M
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  have : FaithfulSMul (𝓞 E) k :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (ringOfIntegers_injective k E τ)
  rw [← (TensorProduct.isBaseChange (𝓞 E) M k).finrank_eq]
  exact h.lieMult_of_unramified t hn

end Module

section Ideal

variable {I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E}

variable {G₁ H₁ : Over (Sp k)} [GrpObj G₁] [GrpObj H₁] [IsCommMonObj G₁] [IsCommMonObj H₁]
  {a₁ : OAct (𝓞 K) G₁} {b₁ : OAct (𝓞 K) H₁}

end Ideal

end IsTensor

end Mult

def Lie.splitTorusEquiv {R O X : Type} [CommRing R] [CommRing O] [AddCommGroup X]
    (a : OAct O (ReciprocityTheory.ChartRestriction.G.Semi.splitTorus (Sp R) X)) : (X →+ R) ≃ₗ[R] Lie a :=
  LinearEquiv.ofBijective
    ({ toFun c := Lie.mk a (Diag.lieVec c) (Diag.isTangent_lieVec c)
       map_add' c d := Lie.ext (Diag.lieVec_add c d)
       map_smul' r c := Lie.ext (Diag.lieVec_smul r c) } : (X →+ R) →ₗ[R] Lie a)
    ⟨fun _ _ e ↦ Diag.lieVec_injective (congrArg Lie.hom e), fun v ↦
      ((Diag.isTangent_iff_exists _).mp v.isTangent).imp fun _ e ↦ Lie.ext e⟩


end GlobalTheory.Serre
