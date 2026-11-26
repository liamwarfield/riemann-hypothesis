module

public import Development.EtaleCohomology.EtaleSheaves.EtaleFirstChernClassRepresentedByChernCocycle
public import Development.EtaleCohomology.EtaleSheaves.LeafActSheafPf
public import Development.EtaleCohomology.EtaleSheaves.AffinePf
public import Development.EtaleCohomology.EtaleSheaves.UnimodularBlockEqToHomValEqOne
public import Development.EtaleCohomology.EtaleSheaves.DescentPf
public import Development.EtaleCohomology.EtaleSheaves.IterCompPf
public import Development.EtaleCohomology.EtaleSheaves.LeafObjAffPf
public import Development.EtaleCohomology.EtaleSheaves.LocSHPf
public import Development.EtaleCohomology.EtaleSheaves.EtaleEvenCohomologyGradedCommRingOfCupRingAxioms
public import Development.EtaleCohomology.EtaleSheaves.LeafRelDimOnePf
public import Development.EtaleCohomology.EtaleSheaves.LeafTw0LocGenOf
public import Development.EtaleCohomology.EtaleSheaves.LeafInclPiecePf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTateTwistResolutionTensorFlat

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleSheaves.RingCommutativity
namespace LateralTheory.E.RingCommutativity

theorem goal_of : LateralTheory.E.CupProductRingLaws.LeafRingComm := LateralTheory.Fix.CupProductTensor.ringComm'

end LateralTheory.E.RingCommutativity
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.PrimitiveRootLocalization
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial GlobalTheory.EtC

namespace LateralTheory.E.PrimitiveRootLocalization

theorem cyc_cond {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) :
    ∃ (p₁ p₂ : A[X]) (n : ℕ), derivative (cyclotomic q A) * p₁ + cyclotomic q A * p₂ = (1 : A[X]) ^ n := by
  obtain ⟨h, e1⟩ := cyclotomic.dvd_X_pow_sub_one q A
  obtain ⟨v, hv⟩ := hq.exists_left_inv
  have e2 := congrArg derivative e1
  rw [derivative_sub, derivative_X_pow, derivative_one, sub_zero, derivative_mul] at e2
  have e3 : C v * C (q : A) = 1 := by rw [← C_mul, hv, C_1]
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have e4 : X * X ^ (q - 1) = (X : A[X]) ^ q := by rw [← pow_succ']; congr 1; omega
  refine ⟨C v * X * h, C v * X * derivative h - h, 0, ?_⟩
  linear_combination (-(C v * X)) * e2 + (C v * C (q : A)) * e4 + X ^ q * e3 + e1

def cycPair {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A)) : StandardEtalePair A where
  f := cyclotomic q A
  monic_f := cyclotomic.monic q A
  g := 1
  cond := cyc_cond q hq

section
variable {A : Type} [CommRing A] (q : ℕ) [NeZero q] (hq : IsUnit (q : A))

theorem cycPair_hasMap_root : (cycPair q hq).HasMap (AdjoinRoot.root (cyclotomic q A)) := by
  refine ⟨?_, ?_⟩
  · simp [cycPair]
  · simp [cycPair]

theorem adjoinRoot_nontrivial [Nontrivial A] : Nontrivial (AdjoinRoot (cyclotomic q A)) := by
  refine Ideal.Quotient.nontrivial_iff.mpr ?_
  rw [Ne, Ideal.span_singleton_eq_top]
  intro hu
  have h1 := (cyclotomic.monic q A).isUnit_iff.mp hu
  have h2 := natDegree_cyclotomic q A
  rw [h1, natDegree_one] at h2
  exact (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))).ne' h2.symm

theorem comap_surj : Function.Surjective (PrimeSpectrum.comap (algebraMap A (cycPair q hq).Ring)) := by
  by_cases hA : Nontrivial A
  · let ψ : (cycPair q hq).Ring →ₐ[A] AdjoinRoot (cyclotomic q A) := (cycPair q hq).lift _ (cycPair_hasMap_root q hq)
    have := (cyclotomic.monic q A).free_adjoinRoot
    have := adjoinRoot_nontrivial (A := A) q
    have hs := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := A) (B := AdjoinRoot (cyclotomic q A))
    have e : algebraMap A (AdjoinRoot (cyclotomic q A)) = (ψ : (cycPair q hq).Ring →+* _).comp (algebraMap A (cycPair q hq).Ring) := by
      ext a; simp
    intro x
    obtain ⟨y, hy⟩ := hs x
    refine ⟨PrimeSpectrum.comap (ψ : (cycPair q hq).Ring →+* _) y, ?_⟩
    rw [← hy, e]
    rfl
  · intro x
    rw [not_nontrivial_iff_subsingleton] at hA
    exact absurd (Subsingleton.elim _ _) x.isPrime.ne_top

def primRing : Prim q (cycPair q hq).Ring :=
  ⟨(cycPair q hq).X, by simpa using hq.map (algebraMap A (cycPair q hq).Ring), by
    have h := (cycPair q hq).hasMap_X.1
    change aeval (cycPair q hq).X (cyclotomic q A) = 0 at h
    rw [← map_cyclotomic q (algebraMap ℤ A), aeval_map_algebraMap] at h
    exact h⟩

end

theorem LeafPrimLoc_of : LateralTheory.E.LeafOneLocPf.LeafPrimLoc := by
  intro q _ U hq
  let P := cycPair (A := Γ(U, ⊤)) q hq
  let f : Spec (CommRingCat.of P.Ring) ⟶ Spec Γ(U, ⊤) := Spec.map (CommRingCat.ofHom (algebraMap Γ(U, ⊤) P.Ring))
  have hfe : Etale f := by
    rw [HasRingHomProperty.Spec_iff (P := @Etale)]
    exact RingHom.etale_algebraMap.mpr inferInstance
  have hfs : Surjective f := ⟨comap_surj q hq⟩
  have hge : Etale (pullback.fst U.toSpecΓ f) := inferInstance
  have hgs : Surjective (pullback.fst U.toSpecΓ f) := inferInstance
  let S : Sieve U :=
    { arrows := fun V _ => Nonempty (Prim q Γ(V, ⊤))
      downward_closed := fun {V W} g hg h => hg.elim fun ζ => ⟨Prim.map h.appTop.hom ζ⟩ }
  refine ⟨S, ?_, fun V g hg => hg⟩
  refine GrothendieckTopology.superset_covering _ ?_ (Precoverage.generate_mem_toGrothendieck
    ((Scheme.singleton_mem_precoverage_iff _ _).mpr ⟨hgs.surj, hge⟩))
  rintro V _ ⟨W, h, k, ⟨⟩, rfl⟩
  exact ⟨Prim.map ((Scheme.ΓSpecIso (CommRingCat.of P.Ring)).inv ≫ (h ≫ pullback.snd _ _).appTop).hom (primRing q hq)⟩

end LateralTheory.E.PrimitiveRootLocalization
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafTensFactorPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.E.LeafTensFactorPf

theorem lift_lof {R : Type} [CommRing R] {I J T : Cx R} (τ : Pair I J T) (U : Scheme.{0}) (s t w : ℤ) (hw : s + t = w)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    τ.lift U w (DirectSum.of (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U)
      ⟨(s, t), hw⟩ (a ⊗ₜ b)) = τ.mul U s t w hw a b := by
  classical
  rw [← DirectSum.lof_eq_of (ULift.{1} R)]
  simp only [Pair.lift, DirectSum.toModule_lof, TensorProduct.lift.tmul]

theorem uniq_mul {R : Type} [CommRing R] {I J T : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (w : ℤ) {M : Shv R}
    (ψ ψ' : ∀ U : Scheme.{0}, Sec (T.X w) U →+ Sec M U)
    (hψ : ∀ {V U : Scheme.{0}} (g : V ⟶ U) y, Sec.res g (ψ U y) = ψ V (Sec.res g y))
    (hψ' : ∀ {V U : Scheme.{0}} (g : V ⟶ U) y, Sec.res g (ψ' U y) = ψ' V (Sec.res g y))
    (h : ∀ U s t (hw : s + t = w) a b, ψ U (τ.mul U s t w hw a b) = ψ' U (τ.mul U s t w hw a b))
    (U : Scheme.{0}) (y : Sec (T.X w) U) : ψ U y = ψ' U y := by
  have hl : ∀ V (x : Tens I J V w), ψ V (τ.lift V w x) = ψ' V (τ.lift V w x) := by
    intro V x
    classical
    induction x using DirectSum.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _)]; rw [ha, hb]
    | of p z =>
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add a b ha hb => simp only [map_add (f := _)]; rw [ha, hb]
      | tmul a c =>
        obtain ⟨⟨s, t⟩, hw⟩ := p
        rw [lift_lof]
        exact h V s t hw a c
  apply LateralTheory.EtaleFoundations.TensFam.sep M
  obtain ⟨S, hS, h1⟩ := hτ.1 U w y
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨x, hx⟩ := h1 V g hg
  rw [hψ, hψ', ← hx, hl]

theorem secMap_nat {R : Type} [CommRing R] {F G : Shv R} (f : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (y : Sec F U) :
    Sec.res g (Sec.map f y) = Sec.map f (Sec.res g y) := by
  have := f.hom.naturality g.op
  exact (congrArg (fun φ => (ModuleCat.Hom.hom φ) y) this).symm

theorem addHom_usmul {A B : Type*} [AddCommGroup A] [AddCommGroup B] (φ : A →+ B) (n : ℤˣ) (x : A) :
    φ (n • x) = n • φ x := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _

end LateralTheory.E.LeafTensFactorPf

namespace LateralTheory.E.LeafTensFactorPf

theorem phi_exists {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (ν : Pair I J K) (w : ℤ) :
    ∃ φ : ∀ U : Scheme.{0}, Sec (T.X w) U →+ Sec (K.X w) U,
      (∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y)) ∧
      ∀ U s t (hw : s + t = w) a b, φ U (τ.mul U s t w hw a b) = ν.mul U s t w hw a b := by
  obtain ⟨φ, h1, h2⟩ := LateralTheory.EtaleFoundations.etale_tensor_hom_descends_along_tensor_pairing R R τ hτ w (K.X w)
    (fun U => (ν.lift U w).toAddMonoidHom) (fun V U g x => LateralTheory.EtaleFoundations.TensFam.lift_res ν g w x)
  refine ⟨φ, h1, fun U s t hw a b => ?_⟩
  have := h2 U (DirectSum.of _ ⟨(s, t), hw⟩ (a ⊗ₜ b))
  rw [lift_lof] at this
  rw [this]
  exact lift_lof ν U s t w hw a b

theorem phi_smul {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (ν : Pair I J K) (w : ℤ)
    (φ : ∀ U : Scheme.{0}, Sec (T.X w) U →+ Sec (K.X w) U)
    (h1 : ∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y))
    (h2 : ∀ U s t (hw : s + t = w) a b, φ U (τ.mul U s t w hw a b) = ν.mul U s t w hw a b)
    (U : Scheme.{0}) (r : ULift.{1} R) (y : Sec (T.X w) U) : φ U (r • y) = r • φ U y := by
  refine uniq_mul τ hτ w (fun U => (φ U).comp (DistribSMul.toAddMonoidHom _ r))
    (fun U => (DistribSMul.toAddMonoidHom _ r).comp (φ U)) ?_ ?_ ?_ U y
  · intro V U g y
    simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply]
    rw [h1]; congr 1; exact map_smul _ r y
  · intro V U g y
    simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply]
    rw [← h1]; exact map_smul _ r _
  · intro U s t hw a b
    simp only [AddMonoidHom.comp_apply, DistribSMul.toAddMonoidHom_apply]
    rw [← LinearMap.map_smul₂, h2, h2, LinearMap.map_smul₂]

def toHom {R : Type} [CommRing R] {F G : Shv R} (φ : ∀ U : Scheme.{0}, Sec F U →+ Sec G U)
    (hnat : ∀ (V U : Scheme.{0}) (g : V ⟶ U) y, Sec.res g (φ U y) = φ V (Sec.res g y))
    (hsm : ∀ U (r : ULift.{1} R) y, φ U (r • y) = r • φ U y) : F ⟶ G :=
  ObjectProperty.homMk
    { app := fun U => ModuleCat.ofHom { toFun := φ (unop U), map_add' := map_add _, map_smul' := hsm (unop U) }
      naturality := fun U V g => by
        ext y
        exact (hnat _ _ g.unop y).symm }

theorem sheafHom_ext {R : Type} [CommRing R] {F G : Shv R} (f g : F ⟶ G)
    (h : ∀ (U : Scheme.{0}) (y : Sec F U), Sec.map f y = Sec.map g y) : f = g := by
  apply Sheaf.hom_ext
  ext U y
  exact h (unop U) y

theorem factor {R : Type} [CommRing R] {I J T K : Cx R} (τ : Pair I J T) (hτ : τ.IsTensor) (ν : Pair I J K) :
    ∃ u : T ⟶ K, τ.Compat ν (𝟙 I) (𝟙 J) u := by
  choose φ h1 h2 using fun w => phi_exists τ hτ ν w
  have hsm : ∀ w U (r : ULift.{1} R) y, φ w U (r • y) = r • φ w U y :=
    fun w => phi_smul τ hτ ν w (φ w) (h1 w) (h2 w)
  refine ⟨{ f := fun w => toHom (φ w) (h1 w) (hsm w), comm' := ?_ }, ?_⟩
  · intro i j hij
    simp only [ComplexShape.up_Rel] at hij
    subst hij
    apply sheafHom_ext
    intro U y
    show Sec.map (K.d i (i + 1)) (φ i U y) = φ (i + 1) U (Sec.map (T.d i (i + 1)) y)
    refine uniq_mul τ hτ i (M := K.X (i + 1))
      (fun U => ((K.d i (i + 1)).hom.app (op U)).hom.toAddMonoidHom.comp (φ i U))
      (fun U => (φ (i + 1) U).comp ((T.d i (i + 1)).hom.app (op U)).hom.toAddMonoidHom) ?_ ?_ ?_ U y
    · intro V U g y
      show Sec.res g (Sec.map (K.d i (i + 1)) (φ i U y)) = Sec.map (K.d i (i + 1)) (φ i V (Sec.res g y))
      rw [secMap_nat, h1]
    · intro V U g y
      show Sec.res g (φ (i + 1) U (Sec.map (T.d i (i + 1)) y)) = φ (i + 1) V (Sec.map (T.d i (i + 1)) (Sec.res g y))
      rw [h1, secMap_nat]
    · intro U s t hw a b
      show Sec.map (K.d i (i + 1)) (φ i U (τ.mul U s t i hw a b)) = φ (i + 1) U (Sec.map (T.d i (i + 1)) (τ.mul U s t i hw a b))
      rw [h2, ν.leibniz, τ.leibniz, map_add (f := _), addHom_usmul, h2, h2]
  · intro U s t w hw a b
    rw [LateralTheory.E.LeafTwPairHtpyPf.secMap_id_f, LateralTheory.E.LeafTwPairHtpyPf.secMap_id_f]
    exact h2 w U s t hw a b

end LateralTheory.E.LeafTensFactorPf

theorem LateralTheory.E.LeafTwPairHtpyPf.LeafTensFactor_of : LateralTheory.E.LeafTwPairHtpyPf.LeafTensFactor := by
  intro R _ I J T K τ hτ ν
  exact LateralTheory.E.LeafTensFactorPf.factor τ hτ ν
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafTwResHtpyPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafTwResHtpyPf

theorem res_isKInj (R : Type) [CommRing R] (F : Shv R) : (res R F).IsKInjective := by
  unfold res InjectiveResolution.cochainComplex
  infer_instance

theorem htpy_of_qiso {C : Type*} [Category C] [Abelian C] {K L I : CochainComplex C ℤ}
    (f : K ⟶ L) [QuasiIso f] [I.IsKInjective] (u u' : L ⟶ I) (h : f ≫ u = f ≫ u') :
    Nonempty (Homotopy u u') := by
  have hY := IsKInjective.rightOrthogonal I
  rw [← ObjectProperty.isLocal_trW] at hY
  have hf : (HomotopyCategory.subcategoryAcyclic C).trW
      ((HomotopyCategory.quotient C _).map f) := by
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
      HomotopyCategory.quotient_map_mem_quasiIso_iff]
    assumption
  have hb := (hY _ hf).1
  have : (HomotopyCategory.quotient C _).map u = (HomotopyCategory.quotient C _).map u' := by
    apply hb
    simp only [← Functor.map_comp, h]
  exact ⟨HomotopyCategory.homotopyOfEq _ _ this⟩

theorem sh_ext {R : Type} [CommRing R] {P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} {X : Shv R}
    (φ ψ : (presheafToSheaf Scheme.etaleTopology.{0} _).obj P ⟶ X)
    (h : toSheafify Scheme.etaleTopology.{0} P ≫ φ.hom = toSheafify Scheme.etaleTopology.{0} P ≫ ψ.hom) : φ = ψ := by
  apply ((sheafificationAdjunction Scheme.etaleTopology.{0} _).homEquiv P X).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  exact h

theorem tw_hom_ext (q : ℕ) (i : ℤ) {X : Shv (ZMod q)} (φ ψ : tw q i ⟶ X)
    (h : ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)), Sec.map φ (twGen i ζ) = Sec.map ψ (twGen i ζ)) : φ = ψ := by
  apply sh_ext
  ext U : 2
  apply ModuleCat.hom_ext
  refine Submodule.linearMap_qext _ (Finsupp.lhom_ext' fun ζ => LinearMap.ext_ring ?_)
  exact h U.unop ζ

end LateralTheory.E.LeafTwResHtpyPf

open LateralTheory.E.LeafTwResHtpyPf in
theorem LateralTheory.E.LeafTwPairHtpyPf.LeafTwResHtpy_of : LateralTheory.E.LeafTwPairHtpyPf.LeafTwResHtpy := by
  intro q _ k T e hT u u' hu
  obtain ⟨_, ε, hε, he⟩ := hT
  have := res_isKInj (ZMod q) (tw q k)
  refine htpy_of_qiso ε u u' ?_
  apply HomologicalComplex.from_single_hom_ext
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f]
  have key : sglι (tw q k) ≫ ε.f 0 ≫ u.f 0 = sglι (tw q k) ≫ ε.f 0 ≫ u'.f 0 := by
    apply tw_hom_ext
    intro U ζ
    have := hu U ζ
    rw [← he U ζ] at this
    exact this
  have h1 : ε.f 0 ≫ u.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q k)).hom ≫
      (sglι (tw q k) ≫ ε.f 0 ≫ u.f 0) := by
    unfold sglι; exact (Iso.hom_inv_id_assoc _ _).symm
  have h2 : ε.f 0 ≫ u'.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (tw q k)).hom ≫
      (sglι (tw q k) ≫ ε.f 0 ≫ u'.f 0) := by
    unfold sglι; exact (Iso.hom_inv_id_assoc _ _).symm
  exact h1.trans ((congrArg _ key).trans h2.symm)
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafTwTensExistsPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC MonoidalCategory

open scoped TensorProduct DirectSum

namespace LateralTheory.E.LeafTwTensExistsPf

variable {R : Type} [CommRing R]

abbrev PSh1 (R : Type) [CommRing R] := Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)

def tF (R : Type) [CommRing R] : Shv R ⥤ Shv R ⥤ PSh1 R :=
  sheafToPresheaf _ _ ⋙ curriedTensor (PSh1 R) ⋙ (Functor.whiskeringLeft _ _ _).obj (sheafToPresheaf _ _)

instance : MonoidalPreadditive (PSh1 R) where
  whiskerLeft_zero := by intros; exact NatTrans.ext (funext fun U => by simp; rfl)
  zero_whiskerRight := by intros; exact NatTrans.ext (funext fun U => by simp; rfl)
  whiskerLeft_add := by intros; exact NatTrans.ext (funext fun U => by simp; rfl)
  add_whiskerRight := by intros; exact NatTrans.ext (funext fun U => by simp; rfl)

instance : (tF R).PreservesZeroMorphisms where
  map_zero A B := by
    apply NatTrans.ext; funext C
    change (sheafToPresheaf _ _).map (0 : A ⟶ B) ▷ C.obj = 0
    rw [Functor.map_zero]; exact MonoidalPreadditive.zero_whiskerRight

instance (A : Shv R) : ((tF R).obj A).PreservesZeroMorphisms where
  map_zero B C := by
    change A.obj ◁ (sheafToPresheaf _ _).map (0 : B ⟶ C) = 0
    rw [Functor.map_zero]; exact MonoidalPreadditive.whiskerLeft_zero

abbrev P (I J : Cx R) : CochainComplex (PSh1 R) ℤ := HomologicalComplex.mapBifunctor I J (tF R) (ComplexShape.up ℤ)

abbrev T (I J : Cx R) : Cx R := ((presheafToSheaf Scheme.etaleTopology _).mapHomologicalComplex _).obj (P I J)

abbrev jm (I J : Cx R) (s t w : ℤ) (h : s + t = w) : ((tF R).obj (I.X s)).obj (J.X t) ⟶ sheafify Scheme.etaleTopology ((P I J).X w) :=
  HomologicalComplex.ιMapBifunctor I J (tF R) (ComplexShape.up ℤ) s t w h ≫ toSheafify Scheme.etaleTopology _

theorem jm_d (I J : Cx R) (s t w : ℤ) (h : s + t = w) :
    jm I J s t w h ≫ sheafifyMap Scheme.etaleTopology ((P I J).d w (w + 1)) =
      ((tF R).map (I.d s (s + 1))).app (J.X t) ≫ jm I J (s + 1) t (w + 1) (by omega) +
      s.negOnePow • (((tF R).obj (I.X s)).map (J.d t (t + 1)) ≫ jm I J s (t + 1) (w + 1) (by omega)) := by
  rw [jm, Category.assoc, ← toSheafify_naturality, ← Category.assoc, HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
    HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.up ℤ).Rel s (s + 1) by simp) _ _ (by simp; omega),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ (show (ComplexShape.up ℤ).Rel t (t + 1) by simp) _ (by simp; omega)]
  simp [Preadditive.add_comp, Category.assoc]

def tau (I J : Cx R) : Pair I J (T I J) where
  mul U s t w h := (TensorProduct.mk _ _ _).compr₂ ((jm I J s t w h).app (op U)).hom
  nat := by
    intro V U g s t w h a b
    have := congrArg (fun f => f.hom (a ⊗ₜ b)) ((jm I J s t w h).naturality g.op)
    exact this.symm
  leibniz := by
    intro U s t w h a b
    change ((jm I J s t w h ≫ sheafifyMap Scheme.etaleTopology ((P I J).d w (w + 1))).app (op U)).hom (a ⊗ₜ b) = _
    rw [jm_d]
    simp only [NatTrans.app_add, NatTrans.app_zsmul, NatTrans.comp_app, ModuleCat.hom_add, ModuleCat.hom_comp,
      LinearMap.add_apply, LinearMap.comp_apply, Units.smul_def]
    simp only [ModuleCat.hom_zsmul, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply]
    rfl

def Phi (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] ToType ((P I J).X w |>.obj (op U)) := by
  classical
  exact DirectSum.toModule _ _ _ fun p =>
    ((HomologicalComplex.ιMapBifunctor I J (tF R) (ComplexShape.up ℤ) p.1.1 p.1.2 w p.2).app (op U)).hom

theorem Phi_lof (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (t : Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) :
    Phi I J U w (DirectSum.of (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p t) =
      ((HomologicalComplex.ιMapBifunctor I J (tF R) (ComplexShape.up ℤ) p.1.1 p.1.2 w p.2).app (op U)).hom t := by
  classical
  unfold Phi
  exact DirectSum.toModule_lof (ULift.{1} R) (M := fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p t

theorem lift_eq (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    (tau I J).lift U w x = ((toSheafify Scheme.etaleTopology ((P I J).X w)).app (op U)).hom (Phi I J U w x) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => first | (erw [map_zero, map_zero] <;> rfl) | (erw [map_zero, map_zero, map_zero] <;> rfl) | (erw [map_zero, map_zero, map_zero, map_zero] <;> rfl) | (simp only [map_zero]) | rfl
  | add x y hx hy => erw [map_add, map_add, map_add, hx, hy] <;> rfl
  | of p t =>
    rw [Phi_lof]
    unfold Pair.lift
    erw [DirectSum.toModule_lof]
    induction t using TensorProduct.induction_on with
    | zero => erw [map_zero, map_zero, map_zero]
    | add x y hx hy => erw [map_add, map_add, map_add, hx, hy]
    | tmul a b => rw [TensorProduct.lift.tmul]; rfl

theorem Phi_nat (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    ((P I J).X w |>.map g.op).hom (Phi I J U w x) = Phi I J V w (Tens.res g w x) := by
  classical
  induction x using DirectSum.induction_on with
  | zero => first | (erw [map_zero, map_zero] <;> rfl) | (erw [map_zero, map_zero, map_zero] <;> rfl) | (erw [map_zero, map_zero, map_zero, map_zero] <;> rfl) | (simp only [map_zero]) | rfl
  | add x y hx hy => erw [map_add, map_add, map_add, map_add, hx, hy] <;> rfl
  | of p t =>
    rw [Phi_lof]
    unfold Tens.res
    erw [DirectSum.lmap_lof]
    erw [Phi_lof]
    have := congrArg (fun f => f.hom t)
      ((HomologicalComplex.ιMapBifunctor I J (tF R) (ComplexShape.up ℤ) p.1.1 p.1.2 w p.2).naturality g.op)
    exact this.symm

abbrev GX (I J : Cx R) : GradedObject (ℤ × ℤ) (PSh1 R) :=
  ((((tF R).mapBifunctorHomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj I).obj J).toGradedObject

def hcol (I J : Cx R) (U : Scheme.{0}) (w : ℤ) :
    IsColimit (((evaluation Scheme.{0}ᵒᵖ (ModuleCat.{1} (ULift.{1} R))).obj (op U)).mapCocone
      ((GX I J).cofanMapObj (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) w)) :=
  isColimitOfPreserves _ ((GX I J).isColimitCofanMapObj _ w)

def dsCocone (I J : Cx R) (U : Scheme.{0}) (w : ℤ) :
    Cocone (Discrete.functor ((GX I J).mapObjFun (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) w) ⋙
      (evaluation Scheme.{0}ᵒᵖ (ModuleCat.{1} (ULift.{1} R))).obj (op U)) where
  pt := ModuleCat.of (ULift.{1} R) (Tens I J U w)
  ι := Discrete.natTrans fun k => ModuleCat.ofHom (DirectSum.lof (ULift.{1} R) _
    (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨k.as.1, k.as.2⟩)

theorem Phi_bij (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Function.Bijective (Phi I J U w) := by
  classical
  let hc := hcol I J U w
  let Ψ := hc.desc (dsCocone I J U w)
  have h1 : ∀ x, Ψ.hom (Phi I J U w x) = x := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => erw [map_zero]; first | rfl | exact map_zero Ψ.hom
    | add x y hx hy => erw [map_add, map_add, hx, hy]; rfl
    | of p t =>
      rw [Phi_lof]
      have := congrArg (fun f => f.hom t) (hc.fac (dsCocone I J U w) ⟨⟨p.1, p.2⟩⟩)
      exact this
  have h2 : ∀ y, Phi I J U w (Ψ.hom y) = y := by
    let PhiH : (dsCocone I J U w).pt ⟶ (((evaluation Scheme.{0}ᵒᵖ (ModuleCat.{1} (ULift.{1} R))).obj (op U)).mapCocone
      ((GX I J).cofanMapObj (ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)) w)).pt :=
      ModuleCat.ofHom (Phi I J U w)
    have : Ψ ≫ PhiH = 𝟙 _ := by
      apply hc.hom_ext
      rintro ⟨k⟩
      rw [← Category.assoc, hc.fac, Category.comp_id]
      ext t
      exact Phi_lof I J U w ⟨k.1, k.2⟩ t
    intro y
    exact congrArg (fun f => f.hom y) this
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem tau_isTensor (I J : Cx R) : (tau I J).IsTensor := by
  constructor
  · intro U w y
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology ((P I J).X w)) y, ?_⟩
    rintro V g ⟨t, ht⟩
    obtain ⟨x, rfl⟩ := (Phi_bij I J V w).2 t
    exact ⟨x, by rw [lift_eq]; exact ht⟩
  · intro U w x hx
    rw [lift_eq] at hx
    have hm := Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology ((P I J).X w))
      (X := op U) (Phi I J U w x) 0 (by rw [map_zero]; exact hx)
    refine ⟨_, hm, ?_⟩
    intro V g hg
    apply (Phi_bij I J V w).1
    rw [map_zero, ← Phi_nat]
    have hg' : ((P I J).X w |>.map g.op).hom (Phi I J U w x) = ((P I J).X w |>.map g.op).hom 0 := hg
    rw [hg', map_zero]

theorem tens_exists (I J : Cx R) : ∃ (K : Cx R) (τ : Pair I J K), τ.IsTensor := ⟨_, tau I J, tau_isTensor I J⟩

end LateralTheory.E.LeafTwTensExistsPf

theorem LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensExists_of : LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensExists := by
  intro q _ i j
  exact LateralTheory.E.LeafTwTensExistsPf.tens_exists _ _
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.WeightBoundsExistence
section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafHAWBounds
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafHtpyAWPf

abbrev HFam (R : Type) [CommRing R] (I J K : Cx R) : Type 1 :=
  ∀ (U : Scheme.{0}) (s t w : ℤ), s + t = w + 1 →
    Sec (I.X s) U →ₗ[ULift.{1} R] Sec (J.X t) U →ₗ[ULift.{1} R] Sec (K.X w) U

def IsHAW {R : Type} [CommRing R] {I J K : Cx R} (h : HFam R I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (η : Cochain ((chains R).obj E) K (k - 1)) :
    Prop :=
  ∀ (N : ℕ) (w : ℤ) (hw : -(N : ℤ) + (k - 1) = w) (U : Scheme.{0}) (x : Sx E N U), ev η N w hw U x =
    ∑ p : Fin (N + 1), (m * (p : ℕ)).negOnePow • h U (-((p : ℕ) : ℤ) + n) (-((N - p : ℕ) : ℤ) + m) w (by omega)
      (ev α p _ rfl U (x.sub 0 p (by omega))) (ev β (N - p) _ rfl U (x.sub p (N - p) (by omega)))

def LeafHAWExists : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (h : HFam R I J K),
  (∀ {V U : Scheme.{0}} (g : V ⟶ U) (s t w : ℤ) (hw : s + t = w + 1) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    Sec.res g (h U s t w hw a b) = h V s t w hw (Sec.res g a) (Sec.res g b)) →
  ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m),
    ∃ η : Cochain ((chains R).obj E) K (k - 1), IsHAW h hk α β η

def LeafHAWBounds : Prop := ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ μ' : Pair I J K) (h : HFam R I J K),
  (∀ (U : Scheme.{0}) (s t w : ℤ) (hw : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    μ.mul U s t w hw a b - μ'.mul U s t w hw a b =
      Sec.map (K.d (w - 1) w) (h U s t (w - 1) (by omega) a b) +
        h U (s + 1) t w (by omega) (Sec.map (I.d s (s + 1)) a) b +
        s.negOnePow • h U s (t + 1) w (by omega) a (Sec.map (J.d t (t + 1)) b)) →
  ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ γ' : Cocycle ((chains R).obj E) K k), μ.IsAW hk α.1 β.1 γ.1 → μ'.IsAW hk α.1 β.1 γ'.1 →
    ∀ η : Cochain ((chains R).obj E) K (k - 1), IsHAW h hk α.1 β.1 η → δ (k - 1) k η = γ.1 - γ'.1

end LateralTheory.E.LeafHtpyAWPf
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open LateralTheory.KummerTheory.AW LateralTheory.EtaleFoundations.AWLeib LateralTheory.E.LeafHtpyAWPf

namespace LateralTheory.E.FreeSheafGeneratorLifts
section Lift
variable {R : Type} [CommRing R]

def freeLiftP (P : PSh) (G : Shv R) (f : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hf : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (f U x) = f V (P.map g.op x)) :
    (freeP R).obj P ⟶ G.obj where
  app U := ModuleCat.freeDesc (↾fun x : ULift (P.obj U) => f U.unop x.down)
  naturality {U V} g := by
    refine ModuleCat.free_hom_ext fun x => ?_
    obtain ⟨x⟩ := x
    have h1 : (((freeP R).obj P).map g).hom (ModuleCat.freeMk (ULift.up x)) = ModuleCat.freeMk (ULift.up (P.map g x)) := by
      simp [freeP, ModuleCat.freeMk, ModuleCat.free]
      exact Finsupp.mapDomain_single
    change (ModuleCat.freeDesc _).hom ((((freeP R).obj P).map g).hom (ModuleCat.freeMk _)) =
      (G.obj.map g).hom ((ModuleCat.freeDesc _).hom (ModuleCat.freeMk _))
    rw [h1]
    erw [ ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
    exact (hf g.unop x).symm

def freeLift (P : PSh) (G : Shv R) (f : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hf : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (f U x) = f V (P.map g.op x)) :
    (free R).obj P ⟶ G :=
  ⟨sheafifyLift Scheme.etaleTopology (freeLiftP P G f hf) G.property⟩

theorem freeLift_gen (P : PSh) (G : Shv R) (f : ∀ U : Scheme.{0}, P.obj (op U) → Sec G U)
    (hf : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)), Sec.res g (f U x) = f V (P.map g.op x))
    (U : Scheme.{0}) (x : P.obj (op U)) : ((freeLift P G f hf).hom.app (op U)).hom (freeGen R P U x) = f U x := by
  have := congrArg (fun φ => (φ.app (op U)).hom (ModuleCat.freeMk (ULift.up x)))
    (toSheafify_sheafifyLift Scheme.etaleTopology (freeLiftP P G f hf) G.property)
  exact this.trans (ModuleCat.freeDesc_apply (R := ULift.{1} R) _ _)

theorem freeGen_nat (P : PSh) {V U : Scheme.{0}} (g : V ⟶ U) (x : P.obj (op U)) :
    freeGen R P V (P.map g.op x) = Sec.res (F := (free R).obj P) g (freeGen R P U x) := by
  have h1 : (((freeP R).obj P).map g.op).hom (ModuleCat.freeMk (ULift.up x)) =
      ModuleCat.freeMk (ULift.up (P.map g.op x)) := by
    simp [freeP, ModuleCat.freeMk, ModuleCat.free]
    exact Finsupp.mapDomain_single
  have h2 := congrArg (fun φ => φ.hom (ModuleCat.freeMk (R := ULift.{1} R) (ULift.up x)))
    ((toSheafify Scheme.etaleTopology ((freeP R).obj P)).naturality g.op)
  unfold freeGen
  erw [← h1]
  exact h2

theorem ev_nat {E : Spc} {I : Cx R} {n : ℤ} (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    ev α p s h V ((E.obj (op (SimplexCategory.mk p))).map g.op x) = Sec.res g (ev α p s h U x) := by
  unfold ev
  rw [freeGen_nat]
  exact congrArg (fun φ => φ.hom (freeGen R _ U x)) (((chainsXIso R E p).inv ≫ α.v _ _ h).hom.naturality g.op)

theorem sub_nat {E : Spc} {N : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U) (j l : ℕ) (h : j + l ≤ N) :
    Sx.sub ((E.obj (op (SimplexCategory.mk N))).map g.op x) j l h =
      (E.obj (op (SimplexCategory.mk l))).map g.op (Sx.sub x j l h) :=
  NatTrans.naturality_apply (E.map (SimplexCategory.subinterval j l h).op) g.op x

variable {K : Cx R} {E : Spc} {k : ℤ}
  (F : ∀ (N : ℕ) (w : ℤ), -(N : ℤ) + k = w → ∀ U : Scheme.{0}, Sx E N U → Sec (K.X w) U)
  (hF : ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E N U),
    Sec.res g (F N w h U x) = F N w h V ((E.obj (op (SimplexCategory.mk N))).map g.op x))

def comp (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) : ((chains R).obj E).X (-(N : ℤ)) ⟶ K.X w :=
  (chainsXIso R E N).hom ≫ freeLift _ (K.X w) (F N w h) (fun g x => hF N w h g x)

theorem comp_cast (N N' : ℕ) (e : N' = N) (hp : -(N : ℤ) = -(N' : ℤ)) (w : ℤ) (h : -(N : ℤ) + k = w)
    (h' : -(N' : ℤ) + k = w) :
    (((chains R).obj E).XIsoOfEq hp).hom ≫ comp F hF N' w h' = comp F hF N w h := by
  subst e
  simp


include hF in
theorem exists_cochain : ∃ η : Cochain ((chains R).obj E) K k,
    ∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (U : Scheme.{0}) (x : Sx E N U), ev η N w h U x = F N w h U x := by
  refine ⟨Cochain.mk fun p q hpq => if hp : p ≤ 0 then
    (((chains R).obj E).XIsoOfEq (by omega : p = -(((-p).toNat : ℕ) : ℤ))).hom ≫ comp F hF (-p).toNat q (by omega)
    else 0, fun N w h U x => ?_⟩
  unfold ev
  rw [Cochain.mk_v, dite_eq_left (by omega), comp_cast F hF N _ (by omega) _ w h, comp, Iso.inv_hom_id_assoc]
  exact freeLift_gen _ _ _ _ U x

end Lift

end LateralTheory.E.FreeSheafGeneratorLifts

open LateralTheory.E.FreeSheafGeneratorLifts in
theorem LateralTheory.E.LeafHtpyAWPf.LeafHAWExists_of : LateralTheory.E.LeafHtpyAWPf.LeafHAWExists := by
  intro R _ I J K h hnat E n m k hk α β
  refine exists_cochain (fun N w hw U x => ∑ p : Fin (N + 1), (m * (p : ℕ)).negOnePow •
    h U (-((p : ℕ) : ℤ) + n) (-((N - p : ℕ) : ℤ) + m) w (by omega)
      (ev α p _ rfl U (x.sub 0 p (by omega))) (ev β (N - p) _ rfl U (x.sub p (N - p) (by omega)))) ?_
  intro N w hw V U g x
  show ((K.X w).obj.map g.op).hom _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Units.smul_def, map_zsmul, Units.smul_def, sub_nat, sub_nat, FreeSheafGeneratorLifts.ev_nat, FreeSheafGeneratorLifts.ev_nat, ← hnat]

namespace LateralTheory.E.FreeSheafGeneratorLifts
section
variable {R : Type} [CommRing R] {I J K : Cx R}

theorem htpy' (μ μ' : Pair I J K) (H : HFam R I J K)
    (hH : ∀ (U : Scheme.{0}) (s t w : ℤ) (hw : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
    μ.mul U s t w hw a b - μ'.mul U s t w hw a b =
      Sec.map (K.d (w - 1) w) (H U s t (w - 1) (by omega) a b) +
        H U (s + 1) t w (by omega) (Sec.map (I.d s (s + 1)) a) b +
        s.negOnePow • H U s (t + 1) w (by omega) a (Sec.map (J.d t (t + 1)) b))
    (U : Scheme.{0}) (s t w0 w s' t' : ℤ) (h : s + t = w) (h0 : s + t = w0 + 1)
    (hs : s + 1 = s') (ht : t + 1 = t') (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Sec.map (K.d w0 w) (H U s t w0 h0 a b) = μ.mul U s t w h a b - μ'.mul U s t w h a b
      - H U s' t w (by omega) (Sec.map (I.d s s') a) b - s.negOnePow • H U s t' w (by omega) a (Sec.map (J.d t t') b) := by
  obtain rfl : w0 = w - 1 := by omega
  subst hs ht
  rw [hH U s t w h a b]
  abel

theorem hmul_bd_left (H : HFam R I J K) {E : Spc} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w + 1)
    (f : ∀ q : ℕ, Sx E q U → Sec (I.X s) U) (p : ℕ) (y : Sx E p U) (b : Sec (J.X t) U) :
    H U s t w h (bd f p y) b = bd (fun q z => H U s t w h (f q z) b) p y :=
  bd_map (((H U s t w h).flip b).toAddMonoidHom) f p y

theorem hmul_bd_right (H : HFam R I J K) {E : Spc} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w + 1)
    (f : ∀ q : ℕ, Sx E q U → Sec (J.X t) U) (p : ℕ) (y : Sx E p U) (a : Sec (I.X s) U) :
    H U s t w h a (bd f p y) = bd (fun q z => H U s t w h a (f q z)) p y :=
  bd_map ((H U s t w h a).toAddMonoidHom) f p y

theorem hmul_congr (H : HFam R I J K) (U : Scheme.{0}) {E : Spc} {n m : ℤ}
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (p q : ℕ) (y : Sx E p U) (z : Sx E q U)
    (s t w s' t' : ℤ) (h : s + t = w + 1) (h' : s' + t' = w + 1) (hs : -(p : ℤ) + n = s) (ht : -(q : ℤ) + m = t)
    (hs' : -(p : ℤ) + n = s') (ht' : -(q : ℤ) + m = t') :
    H U s t w h (ev α p s hs U y) (ev β q t ht U z) = H U s' t' w h' (ev α p s' hs' U y) (ev β q t' ht' U z) := by
  subst hs ht hs' ht'; rfl

def Fh (H : HFam R I J K) {E : Spc} {n m : ℤ} (α : Cochain ((chains R).obj E) I n)
    (β : Cochain ((chains R).obj E) J m) (U : Scheme.{0}) (w : ℤ) (p q : ℕ) (y : Sx E p U) (z : Sx E q U) :
    Sec (K.X w) U :=
  if hh : (-(p : ℤ) + n) + (-(q : ℤ) + m) = w + 1 then H U _ _ w hh (ev α p _ rfl U y) (ev β q _ rfl U z) else 0

end

theorem ev_sub' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (a b : Cochain ((chains R).obj E) I n) (p : ℕ) (s : ℤ)
    (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) : ev (a - b) p s h U x = ev a p s h U x - ev b p s h U x := by
  have := ev_add (a - b) b p s h U x
  rw [sub_add_cancel] at this
  rw [this]; abel

theorem d_cocycle {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α : Cocycle ((chains R).obj E) I n) (p : ℕ)
    (s s' : ℤ) (hs : -(p : ℤ) + n = s) (hs' : -(p : ℤ) + (n + 1) = s') (U : Scheme.{0}) (y : Sx E p U) :
    Sec.map (I.d s s') (ev α.1 p s hs U y) =
      -((n + 1).negOnePow • bd (fun q z => if hh : -(q : ℤ) + n = s' then ev α.1 q s' hh U z else 0) p y) := by
  have h0 := ev_delta_bd rfl α.1 p s s' hs hs' U y
  rw [(Cocycle.mem_iff n (n + 1) rfl α.1).1 α.2] at h0
  have hz : ev (0 : Cochain ((chains R).obj E) I (n + 1)) p s' hs' U y = 0 := by
    rw [ev_eq, Cochain.zero_v, Limits.comp_zero]; rfl
  rw [hz] at h0
  exact eq_neg_of_add_eq_zero_left h0.symm

theorem recH {G : Type*} [AddCommGroup G] (X Y P P' Q Q' : G) (ε A s B K c' c e : ℤ) (hP : P' = P) (hQ : Q' = Q)
    (h1 : K * c' = -(ε * A)) (h2 : K * (c * e) = -(ε * (s * B))) :
    ε • (X - Y - -(A • P) - s • -(B • Q)) + K • (c' • P' + c • e • Q') = ε • X - ε • Y := by
  rw [hP, hQ]
  have : K • (c' • P + c • e • Q) = (K * c') • P + (K * (c * e)) • Q := by
    simp only [smul_add, smul_smul]
  rw [this, h1, h2]
  simp only [smul_sub, smul_neg, smul_smul, neg_smul]
  abel

theorem LeafHAWBounds_proved : LeafHAWBounds := by
  intro R _ I J K μ μ' H hH E n m k hk α β γ₁ γ₂ h1 h2 c hc
  apply ev_ext
  intro N w hw U x
  rw [ev_sub', ev_delta_bd (by omega : k - 1 + 1 = k) c N (-(N : ℤ) + (k - 1)) w rfl hw U x, hc N _ rfl U x, h1 N w hw U x, h2 N w hw U x]
  rw [bd_congr (g := fun N' y => ∑ p : Fin (N' + 1), ((m * (p : ℕ)).negOnePow : ℤ) •
      Fh H α.1 β.1 U w p (N' - p) (y.sub 0 p (by omega)) (y.sub p (N' - p) (by omega))) ?_ x]
  swap
  · intro N' y hN
    rw [dite_eq_left (by omega), hc N' w _ U y]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Units.smul_def]
    unfold Fh
    rw [dite_eq_left (by omega)]
  rw [bd_aw (Fh H α.1 β.1 U w) (fun p : ℕ => ((m * (p : ℤ)).negOnePow : ℤ)) (fun p : ℕ => ((m * ((p : ℤ) - 1)).negOnePow : ℤ))
    (fun p => by congr 2; push_cast; ring) N x]
  rw [secmap_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp := p.2
  rw [Units.smul_def, secmap_zsmul, htpy' μ μ' H hH U _ _ _ w (-((p : ℕ) : ℤ) + (n + 1)) (-((N - p : ℕ) : ℤ) + (m + 1)) (by omega) (by omega) (by omega) (by omega)]
  rw [d_cocycle α p (-((p : ℕ) : ℤ) + n) _ rfl (by omega) U, d_cocycle β (N - p) (-((N - p : ℕ) : ℤ) + m) _ rfl (by omega) U]
  simp only [map_neg, map_zsmul, LinearMap.neg_apply, LinearMap.smul_apply, Units.smul_def, hmul_bd_left, hmul_bd_right]
  refine recH _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_ ?_
  · refine bd_congr (fun q z hq => ?_) _
    unfold Fh
    rw [dite_eq_left (by omega), dite_eq_left (by omega)]
    exact hmul_congr H U α.1 β.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · refine bd_congr (fun q z hq => ?_) _
    unfold Fh
    rw [dite_eq_left (by omega), dite_eq_left (by omega)]
    exact hmul_congr H U α.1 β.1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  · subst hk
    simp only [← Units.val_mul, ← Int.negOnePow_add, ← Units.val_neg, ← Int.negOnePow_succ]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨-1, by ring⟩
  · subst hk
    rw [sign_nat]
    simp only [← Units.val_mul, ← Int.negOnePow_add, ← Units.val_neg, ← Int.negOnePow_succ]
    congr 1
    rw [Int.negOnePow_eq_iff]
    exact ⟨(p : ℤ) - 1, by ring⟩

theorem LeafHtpyAW_proved : LateralTheory.E.LeafTwPairUniquePf.LeafHtpyAW := by
  intro R _ I J K μ μ' ⟨h, hnat, hht⟩ E n m k hk α β γ γ' h₁ h₂
  obtain ⟨η, hη⟩ := LeafHAWExists_of R h hnat E hk α.1 β.1
  have hc := LeafHAWBounds_proved R μ μ' h hht E hk α β γ γ' h₁ h₂ η hη
  rw [← sub_eq_zero, ← CohomologyClass.mk_sub, CohomologyClass.mk_eq_zero_iff]
  exact ⟨k - 1, by omega, η, by rw [hc]; rfl⟩

end LateralTheory.E.FreeSheafGeneratorLifts
end
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.GoalOf
namespace LateralTheory.E.LeafA6ringCut

theorem goal_of (h5 : LateralTheory.E.CupProductRingLaws.LeafRingUnit) (h6 : LateralTheory.E.CupProductRingLaws.LeafRingAssoc)
    (h7 : LateralTheory.E.CupProductRingLaws.LeafRingComm) : LateralTheory.E.D2.LeafA6ring :=
  fun q _ E => ⟨h5 q E, h6 q E, h7 q E⟩

end LateralTheory.E.LeafA6ringCut
end

section -- merged from Development.EtaleCohomology.EtaleSheaves.LeafUnitAWPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitAWPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafRingUnitPf

theorem sec_sub {R : Type} [CommRing R] (F : Shv R) (s : ℤ) (hs : s < 0) (U : Scheme.{0}) :
    Subsingleton (Sec ((res R F).X s) U) := by
  have hz : IsZero ((res R F).X s) := by
    unfold res
    exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)
  have h2 : IsZero (((res R F).X s).obj.obj (op U)) :=
    Functor.map_isZero ((sheafToPresheaf _ _) ⋙ (evaluation _ _).obj (op U)) hz
  exact ModuleCat.isZero_iff_subsingleton.mp h2

theorem sub_zero_self {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (h : 0 + N ≤ N) : x.sub 0 N h = x := by
  have : SimplexCategory.subinterval (n := N) 0 N h = 𝟙 _ := by
    ext i : 3
    simp [SimplexCategory.subinterval]
  simp [Sx.sub, this]

theorem main_gen (q : ℕ) [NeZero q] (E : Spc) (i j : ℤ) (hij : i = j)
    (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q j)))
    (hU : ∀ (U : Scheme.{0}) (t w : ℤ) (h : 0 + t = w) (a : Sec ((res _ (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      Loc U (fun V g => ∃ ζ : Prim q Γ(V, ⊤), Sec.res g a = resGen 0 ζ) → HEq (μ.mul U 0 t w h a b) b)
    (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0) (hα : OneLoc α)
    (n k : ℤ) (hnk : n = k) (β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q i)) n) :
    ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q j)) k, μ.IsAW (show 0 + n = k by omega) α.1 β.1 γ.1 ∧
      CohomologyClass.mk γ = Ht.cast hnk hij (CohomologyClass.mk β : Ht q E n i) := by
  subst hij hnk
  refine ⟨β, ?_, rfl⟩
  intro N w h U x
  have hmz : ∀ (s t w : ℤ) (h : s + t = w) (a : Sec ((res _ (tw q 0)).X s) U) (b : Sec ((res _ (tw q i)).X t) U),
      s < 0 → μ.mul U s t w h a b = 0 := by
    intro s t w h a b hs
    have := sec_sub (tw q 0) s hs U
    rw [Subsingleton.elim a 0]
    simp
  rw [Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]
  · subst h
    show _ = (n * ((0 : ℕ) : ℤ)).negOnePow • μ.mul U (-((0 : ℕ) : ℤ) + 0) (-((N - 0 : ℕ) : ℤ) + n) (-(N : ℤ) + n) (by omega)
      (ev α.1 0 _ rfl U (x.sub 0 0 (by omega))) (ev β.1 (N - 0) _ rfl U (x.sub 0 (N - 0) (by omega)))
    have h1 : (n * ((0 : ℕ) : ℤ)).negOnePow = 1 := by simp
    rw [h1, one_smul]
    show _ = μ.mul U 0 (-(N : ℤ) + n) (-(N : ℤ) + n) (by omega)
      (ev α.1 0 0 (by simp) U (x.sub 0 0 (by omega))) (ev β.1 N _ rfl U (x.sub 0 N (by omega)))
    rw [sub_zero_self]
    exact (eq_of_heq (hU U _ _ (by omega) _ (ev β.1 N _ rfl U x) (hα U (x.sub 0 0 (by omega))))).symm
  · intro p _
    rw [hmz, smul_zero]
    simp
    omega

theorem LeafUnitAW_of : LeafUnitAW := by
  intro q _ E i μ hU α hα n β
  exact main_gen q E i (0 + i) (by ring) μ hU α hα n (0 + n) (by ring) β

end LateralTheory.E.LeafUnitAWPf
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.Fix.EtaleChapterDTwo

theorem awSpec : LateralTheory.E.LeafA6suppPf.LeafAWSpec := by
  intro q _ E n m i j α β
  have hS := LateralTheory.Fix.CupProductTensor.cupSpec (ZMod q) (twPair q i j) E (rfl : n + m = n + m)
  obtain ⟨γ, hγ⟩ := hS.1 α β
  exact ⟨γ, hγ, hS.2 α β γ hγ⟩

theorem s0 : LateralTheory.E.D2.LeafA6nat := @_root_.LateralTheory.E.LeafA6nat_xy7V2Cut.goal_of
theorem s1 : LateralTheory.E.CupProductRingLaws.LeafCupSpec := @_root_.LateralTheory.Fix.CupProductTensor.cupSpec
theorem s2 : LateralTheory.E.CupProductRingLaws.LeafTwPairExists := @_root_.LateralTheory.Fix.CupProductTensor.twPairExists
theorem s3 : LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensExists := @_root_.LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensExists_of
theorem s4 : LateralTheory.E.LeafTwPairHtpyPf.LeafTensFactor := @_root_.LateralTheory.E.LeafTwPairHtpyPf.LeafTensFactor_of
theorem s5 : LateralTheory.E.ZModFlatnessFromBaerCriterion.TensTwRes := @_root_.GlobalTheory.EtC.isTwRes_tensor
theorem s6 : LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjSecInj := @_root_.LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjSecInj_of
theorem s7 : LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjFlatZMod := @_root_.LateralTheory.E.ZModFlatnessFromBaerCriterion.LeafInjFlatZMod_of
theorem s8 : LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensRes := @_root_.LateralTheory.E.LeafTwPairHtpyPf.LeafTwTensRes_of s5 s6 s7
theorem s9 : LateralTheory.E.LeafTwPairHtpyPf.LeafTwResHtpy := @_root_.LateralTheory.E.LeafTwPairHtpyPf.LeafTwResHtpy_of
theorem s10 : LateralTheory.E.LeafTwPairUniquePf.LeafTwPairHtpy := @_root_.LateralTheory.E.LeafTwPairUniquePf.LeafTwPairHtpy_of s3 s4 s8 s9
theorem s11 : LateralTheory.E.LeafTwPairUniquePf.LeafHtpyAW := @_root_.LateralTheory.E.FreeSheafGeneratorLifts.LeafHtpyAW_proved
theorem s12 : LateralTheory.E.CupProductRingLaws.LeafTwPairUnique := @_root_.LateralTheory.E.CupProductRingLaws.LeafTwPairUnique_of s1 s10 s11
theorem s13 : LateralTheory.E.LeafOneExistsPf.LeafUnitSec := @_root_.LateralTheory.E.UnitSections.LeafUnitSec_of
theorem s14 : LateralTheory.E.LeafOneSpecPf.LeafOneExists := @_root_.LateralTheory.E.LeafOneExistsPf.CocycleOfSec.LeafOneExists_of_unit s13
theorem s15 : LateralTheory.E.LeafOneSpecPf.LeafPrimCover := @_root_.LateralTheory.E.LeafPrimCoverPf.leafPrimCover_pf
theorem s16 : LateralTheory.E.CupProductRingLaws.LeafOneSpec := @_root_.LateralTheory.E.LeafOneSpecPf.LeafOneSpec_of s14 s15
theorem s17 : LateralTheory.E.LeafUnitActPf.LeafActSheaf := @_root_.LateralTheory.E.LeafActSheafPf.LeafActSheaf_of
theorem s18 : LateralTheory.E.LeafUnitPairGPf.LeafUnitAct := @_root_.LateralTheory.E.LeafUnitActPf.LeafUnitAct_of s17
theorem s19 : LateralTheory.E.LeafPairExtPf2.LeafTensUP := @_root_.LateralTheory.E.LeafTensUPPf.etale_tensor_pairing_universal_property_holds
theorem s20 : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0LocGen := @_root_.LateralTheory.E.LeafTw0LocGenPf.LeafTw0LocGen_of
theorem s21 : LateralTheory.E.LeafTw0LocSplitPfM.LeafTw0TwFree := @_root_.LateralTheory.E.LeafTw0TwFreePf.LeafTw0TwFree_of
theorem s22 : LateralTheory.E.LeafTw0LocSplitPf.LeafTw0GenFree := @_root_.LateralTheory.E.LeafTw0LocSplitPfM.LeafTw0GenFree_of s21
theorem s23 : LateralTheory.E.LeafTensMonoPf.LeafTw0LocSplit := @_root_.LateralTheory.E.LeafTw0LocSplitPf.LeafTw0LocSplit_of s20 s22
theorem s24 : LateralTheory.E.LeafTensMonoPf.LeafPreTensLocInj := @_root_.LateralTheory.E.LeafPreTensLocInjPf.LeafPreTensLocInj_of s23
theorem s25 : LateralTheory.E.LeafExtTensPf.LeafTensMono := @_root_.LateralTheory.E.LeafTensMonoPf.LeafTensMono_of s24
theorem s26 : LateralTheory.E.LeafTensQIsoPf.LeafTensQIsoGen := @_root_.LateralTheory.E.LeafTensQIsoGenPf.LeafTensQIsoGen_of
theorem s27 : LateralTheory.E.LeafTensQIsoPf.LeafSecInj := @_root_.LateralTheory.E.LeafSecInjPf.LeafSecInj_of
theorem s28 : LateralTheory.E.LeafTensQIsoPf.LeafZModInjFlat := @_root_.LateralTheory.E.LeafZModInjFlatPf.LeafZModInjFlat_of
theorem s29 : LateralTheory.E.LeafExtTensPf.LeafTensQIso := @_root_.LateralTheory.E.LeafTensQIsoPf.LeafTensQIso_of s26 s27 s28
theorem s30 : LateralTheory.E.LeafPairExtPf2.LeafExtTens := @_root_.LateralTheory.E.LeafExtTensPf.LeafExtTens_of s25 s29
theorem s31 : LateralTheory.E.LeafPairExtPf.LeafExtAlongAug := @_root_.LateralTheory.E.LeafPairExtPf2.LeafExtAlongAug_of s19 s30
theorem s32 : LateralTheory.E.LeafUnitPairGPf.LeafPairExt := @_root_.LateralTheory.E.LeafPairExtPf.LeafPairExt_of' s31
theorem s33 : LateralTheory.E.LeafUnitPairPf.LeafUnitPairG := @_root_.LateralTheory.E.LeafUnitPairGPf.LeafUnitPairG_of s18 s32
theorem s34 : LateralTheory.E.LeafRingUnitPf.LeafUnitPair := @_root_.LateralTheory.E.LeafUnitPairPf.LeafUnitPair_of s33
theorem s35 : LateralTheory.E.LeafOneLocPf.LeafPrimLoc := @_root_.LateralTheory.E.PrimitiveRootLocalization.LeafPrimLoc_of
theorem s36 : LateralTheory.E.LeafRingUnitPf.LeafOneLoc := @_root_.LateralTheory.E.LeafOneLocPf.LeafOneLoc_of s35
theorem s37 : LateralTheory.E.LeafRingUnitPf.LeafUnitAW := @_root_.LateralTheory.E.LeafUnitAWPf.LeafUnitAW_of
theorem s38 : LateralTheory.E.CupProductRingLaws.LeafRingUnit := @_root_.LateralTheory.E.LeafRingUnitPf.LeafRingUnit_of s1 s2 s12 s16 s34 s36 s37
theorem s39 : LateralTheory.E.CupProductRingLaws.LeafRingAssoc := @_root_.LateralTheory.Fix.CupProductTensor.ringAssoc
theorem s40 : LateralTheory.E.CupProductRingLaws.LeafRingComm := @_root_.LateralTheory.E.RingCommutativity.goal_of
theorem s41 : LateralTheory.E.D2.LeafA6ring := @_root_.LateralTheory.E.LeafA6ringCut.goal_of s38 s39 s40
theorem s42 : LateralTheory.E.D2.LeafRing := @_root_.LateralTheory.E.D2.LeafRing_of s0 s41
theorem s43 : LateralTheory.E.D2.LeafChern := @_root_.LateralTheory.E.D2.LeafChern_of
theorem s44 : LateralTheory.E.D2.LeafNat := @_root_.LateralTheory.E.D2.LeafNat_of s0
theorem s45 : LateralTheory.E.LeafGeomPf.LeafHalf1 := @_root_.LateralTheory.E.LeafHalf1Pf.LeafHalf1_of
theorem s46 : LateralTheory.E.HalfDegreeVanishing.LeafMapW := @_root_.LateralTheory.E.LeafMapWPf.LeafMapW_of
theorem s47 : LateralTheory.E.LeafGeomPf.LeafHalf2 := @_root_.LateralTheory.E.HalfDegreeVanishing.LeafHalf2_of s46
theorem s48 : LateralTheory.E.D2.LeafGeom := @_root_.LateralTheory.E.LeafGeomPfLoc.LeafGeom_of s45 s47
theorem s49 : LateralTheory.E.D2.LeafCover2 := @_root_.LateralTheory.E.LeafCover2Pf.LeafCover2_of
theorem s50 : LateralTheory.E.LeafA6suppPf.LeafAWSpec := awSpec
theorem s51 : LateralTheory.E.LeafA6suppPf.LeafRepVanish := @_root_.LateralTheory.E.LeafRepVanishPf.LeafRepVanish_of
theorem s52 : LateralTheory.E.LeafA6suppPf.LeafCochainVanish := @_root_.LateralTheory.E.LeafA6suppPf.LeafCochainVanish_of
theorem s53 : LateralTheory.E.D2.LeafA6supp := @_root_.LateralTheory.E.LeafA6suppPf.LeafA6supp_of s50 s51 s52
theorem s54 : LateralTheory.E.D2.LeafWhitney := @_root_.LateralTheory.E.D2.LeafWhitney_of s48 s49 s53 s0
theorem s55 : LateralTheory.E.D2.LeafLine := @_root_.LateralTheory.E.D2.LeafLine_of s0
theorem s56 : LateralTheory.E.D2.LeafNewton := @_root_.LateralTheory.E.LeafNewtonPf.LeafNewton_of
theorem s57 : LateralTheory.E.EtaleChapterDTwo := @_root_.LateralTheory.E.D2.goal_of s42 s43 s44 s54 s55 s56

end LateralTheory.Fix.EtaleChapterDTwo
