module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMayerVietorisConnectingExact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistMulIsTensorPairing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFlatComplexPreservesQuasiIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcyclicTensorAcyclicFlatEtaleComplex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFlatEtaleSheafPreservesLocalExactness
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFlatEtaleSheafPreservesLocalExactness
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC
namespace TensFlat

variable {R : Type} [CommRing R]

theorem rl_comm {M N P Q : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
    [Module (ULift.{1} R) M] [Module (ULift.{1} R) N] [Module (ULift.{1} R) P] [Module (ULift.{1} R) Q]
    (f : M →ₗ[ULift.{1} R] P) (g : N →ₗ[ULift.{1} R] Q) (x : TensorProduct (ULift.{1} R) M N) :
    LinearMap.rTensor Q f (LinearMap.lTensor M g x) = LinearMap.lTensor P g (LinearMap.rTensor N f x) := by
  rw [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor, ← LinearMap.lTensor_comp_rTensor,
    LinearMap.comp_apply]

theorem tres_comp (X Y : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) {W V U : Scheme.{0}} (m : W ⟶ V) (k : V ⟶ U)
    (x : TensorProduct (ULift.{1} R) (X.obj (op U)) (Y.obj (op U))) :
    TensorProduct.map (X.map (m ≫ k).op).hom (Y.map (m ≫ k).op).hom x =
      TensorProduct.map (X.map m.op).hom (Y.map m.op).hom (TensorProduct.map (X.map k.op).hom (Y.map k.op).hom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem nat_apply {X Z : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (ψ : X ⟶ Z) {V U : Scheme.{0}} (k : V ⟶ U)
    (a : X.obj (op U)) : (Z.map k.op).hom ((ψ.app (op U)).hom a) = (ψ.app (op V)).hom ((X.map k.op).hom a) := by
  have h := congrArg (fun h => ModuleCat.Hom.hom h a) (ψ.naturality k.op)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

theorem tres_rTensor {X Z : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)} (Y : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R))
    (ψ : X ⟶ Z) {V U : Scheme.{0}} (k : V ⟶ U) (x : TensorProduct (ULift.{1} R) (X.obj (op U)) (Y.obj (op U))) :
    TensorProduct.map (Z.map k.op).hom (Y.map k.op).hom (LinearMap.rTensor _ (ψ.app (op U)).hom x) =
      LinearMap.rTensor _ (ψ.app (op V)).hom (TensorProduct.map (X.map k.op).hom (Y.map k.op).hom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul, nat_apply]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem tres_lTensor (X : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) {Y Z : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)}
    (ψ : Y ⟶ Z) {V U : Scheme.{0}} (k : V ⟶ U) (x : TensorProduct (ULift.{1} R) (X.obj (op U)) (Y.obj (op U))) :
    TensorProduct.map (X.map k.op).hom (Z.map k.op).hom (LinearMap.lTensor _ (ψ.app (op U)).hom x) =
      LinearMap.lTensor _ (ψ.app (op V)).hom (TensorProduct.map (X.map k.op).hom (Y.map k.op).hom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp only [LinearMap.lTensor_tmul, TensorProduct.map_tmul, nat_apply]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem ker_tensor_loc {A B C : Shv R} (f : A ⟶ B) (g : B ⟶ C)
    (hex : ∀ U (b : Sec B U), Sec.map g b = 0 → Loc U fun V k => ∃ a : Sec A V, Sec.map f a = Sec.res k b)
    (P : Scheme.{0}ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)) (W : Scheme.{0})
    (z : TensorProduct (ULift.{1} R) (LinearMap.ker (g.hom.app (op W)).hom) (P.obj (op W))) :
    Loc W fun W' n => ∃ y : TensorProduct (ULift.{1} R) (Sec A W') (P.obj (op W')),
      LinearMap.rTensor _ (f.hom.app (op W')).hom y = TensorProduct.map (B.obj.map n.op).hom (P.map n.op).hom
        (LinearMap.rTensor _ (LinearMap.ker (g.hom.app (op W)).hom).subtype z) := by
  induction z using TensorProduct.induction_on with
  | zero => exact loc_of_forall W _ fun W' n => ⟨0, by simp⟩
  | tmul b p =>
    refine loc_mono W _ _ (hex W b.1 (LinearMap.mem_ker.mp b.2)) ?_
    rintro W' n ⟨a, ha⟩
    refine ⟨a ⊗ₜ (P.map n.op).hom p, ?_⟩
    simp only [LinearMap.rTensor_tmul, TensorProduct.map_tmul, Submodule.coe_subtype]
    exact congrArg (· ⊗ₜ[ULift.{1} R] (P.map n.op).hom p) ha
  | add z₁ z₂ h₁ h₂ =>
    refine loc_mono W _ _ (loc_and W _ _ h₁ h₂) ?_
    rintro W' n ⟨⟨y₁, e₁⟩, ⟨y₂, e₂⟩⟩
    exact ⟨y₁ + y₂, by simp only [map_add (f := _), e₁, e₂]⟩

end TensFlat


open TensFlat in
theorem tensor_flat_loc_exact : ∀ (R : Type) [CommRing R] (M : Shv R), FlatS M → ∀ {A B C : Shv R} (f : A ⟶ B) (g : B ⟶ C), f ≫ g = 0 → (∀ U (b : Sec B U), Sec.map g b = 0 → Loc U fun V k => ∃ a : Sec A V, Sec.map f a = Sec.res k b) → ∀ U (x : TensorProduct (ULift.{1} R) (Sec B U) (Sec M U)), (Loc U fun V k => LinearMap.rTensor _ (g.hom.app (op V)).hom (TensorProduct.map (B.obj.map k.op).hom (M.obj.map k.op).hom x) = 0) → Loc U fun V k => ∃ y : TensorProduct (ULift.{1} R) (Sec A V) (Sec M V), LinearMap.rTensor _ (f.hom.app (op V)).hom y = TensorProduct.map (B.obj.map k.op).hom (M.obj.map k.op).hom x := by
  intro R _ M hM A B C f g _ hex U x hx
  obtain ⟨P, φ, hsurj, hinj, hflat⟩ := hM
  have h1 := (GlobalTheory.T.sectionwiseTensor_presheaf_locallyBijective R B.obj P M.obj φ hsurj hinj U).1 x
  apply loc_trans
  refine loc_mono U _ _ (loc_and U _ _ h1 hx) ?_
  rintro V k ⟨⟨x', hx'⟩, hz⟩
  have hz0 : LinearMap.lTensor _ (φ.app (op V)).hom (LinearMap.rTensor _ (g.hom.app (op V)).hom x') = 0 := by
    rw [← rl_comm, hx']
    exact hz
  have h2 := (GlobalTheory.T.sectionwiseTensor_presheaf_locallyBijective R C.obj P M.obj φ hsurj hinj V).2 _ hz0
  apply loc_trans
  refine loc_mono V _ _ h2 ?_
  intro W m hm
  have hg0 : LinearMap.rTensor _ (g.hom.app (op W)).hom
      (TensorProduct.map (B.obj.map m.op).hom (P.map m.op).hom x') = 0 := by
    rw [← tres_rTensor]; exact hm
  by_cases hW : Nonempty W
  · haveI := hflat W hW
    have hexact := Module.Flat.rTensor_exact (P.obj (op W))
      (LinearMap.exact_subtype_ker_map (g.hom.app (op W)).hom)
    obtain ⟨z, hzx⟩ := (hexact _).mp hg0
    refine loc_mono W _ _ (ker_tensor_loc f g hex P W z) ?_
    rintro W' n ⟨y, hy⟩
    refine ⟨LinearMap.lTensor _ (φ.app (op W')).hom y, ?_⟩
    rw [rl_comm, hy, hzx, tres_comp, tres_comp, ← hx', tres_lTensor, tres_lTensor]
  · haveI : IsEmpty W := not_nonempty_iff.mp hW
    exact loc_of_isEmpty W _

end GlobalTheory.EtC
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFlatEtaleSheafPreservesLocalExactnessStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_flat_etaleSheaf_preserves_local_exactness : ∀ (R : Type) [CommRing R] (M : Shv R), FlatS M → ∀ {A B C : Shv R} (f : A ⟶ B) (g : B ⟶ C), f ≫ g = 0 → (∀ U (b : Sec B U), Sec.map g b = 0 → Loc U fun V k => ∃ a : Sec A V, Sec.map f a = Sec.res k b) → ∀ U (x : TensorProduct (ULift.{1} R) (Sec B U) (Sec M U)), (Loc U fun V k => LinearMap.rTensor _ (g.hom.app (op V)).hom (TensorProduct.map (B.obj.map k.op).hom (M.obj.map k.op).hom x) = 0) → Loc U fun V k => ∃ y : TensorProduct (ULift.{1} R) (Sec A V) (Sec M V), LinearMap.rTensor _ (f.hom.app (op V)).hom y = TensorProduct.map (B.obj.map k.op).hom (M.obj.map k.op).hom x := by
  first | (exact @GlobalTheory.EtC.tensor_flat_loc_exact) | (exact GlobalTheory.EtC.tensor_flat_loc_exact) | (intros; apply GlobalTheory.EtC.tensor_flat_loc_exact  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcyclicTensorAcyclicFlatEtaleComplex
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex
open scoped DirectSum TensorProduct

namespace GlobalTheory.EtC

variable {R : Type} [CommRing R]

abbrev Sec.lin {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) : Sec F U →ₗ[ULift.{1} R] Sec G U := (φ.hom.app (op U)).hom

abbrev Tens.of (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w}) :
    (Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) →ₗ[ULift.{1} R] Tens I J U w :=
  DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w} (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) p

def Tens.d (I J : Cx R) (U : Scheme.{0}) (w : ℤ) : Tens I J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) := by
  classical
  exact DirectSum.toModule _ _ _ fun p =>
    Tens.of I J U (w + 1) ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
      TensorProduct.map (Sec.lin (I.d p.1.1 (p.1.1 + 1)) U) LinearMap.id +
    ((p.1.1.negOnePow : ℤˣ) : ℤ) •
      (Tens.of I J U (w + 1) ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩ ∘ₗ
        TensorProduct.map LinearMap.id (Sec.lin (J.d p.1.2 (p.1.2 + 1)) U))

theorem Tens.d_of_tmul (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.d I J U w (Tens.of I J U w p (a ⊗ₜ b)) =
      Tens.of I J U (w + 1) ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩
          (Sec.map (I.d p.1.1 (p.1.1 + 1)) a ⊗ₜ b) +
        ((p.1.1.negOnePow : ℤˣ) : ℤ) • Tens.of I J U (w + 1) ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩
          (a ⊗ₜ Sec.map (J.d p.1.2 (p.1.2 + 1)) b) := by
  simp [Tens.d, Tens.of, DirectSum.toModule_lof]

end GlobalTheory.EtC

namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]
open scoped DirectSum TensorProduct

theorem Pair.lift_of_tmul {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    μ.lift U w (Tens.of I J U w p (a ⊗ₜ b)) = μ.mul U p.1.1 p.1.2 w p.2 a b := by
  simp [Pair.lift, Tens.of, DirectSum.toModule_lof]

theorem Pair.lift_tensD {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    μ.lift U (w + 1) (Tens.d I J U w x) = Sec.map (K.d w (w + 1)) (μ.lift U w x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have e := Tens.d_of_tmul I J U w p a b
      simp only [Tens.of, DirectSum.lof_eq_of] at e
      rw [e, map_add (f := _), map_zsmul]
      have e1 := μ.lift_of_tmul U (w + 1) ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩
        (Sec.map (I.d p.1.1 (p.1.1 + 1)) a) b
      have e2 := μ.lift_of_tmul U (w + 1) ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩
        a (Sec.map (J.d p.1.2 (p.1.2 + 1)) b)
      have e3 := μ.lift_of_tmul U w p a b
      simp only [Tens.of, DirectSum.lof_eq_of] at e1 e2 e3
      rw [e1, e2, e3, μ.leibniz U p.1.1 p.1.2 w p.2 a b, Units.smul_def]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem Pair.lift_tensRes {I J K : Cx R} (μ : Pair I J K) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    μ.lift V w (Tens.res g w x) = Sec.res g (μ.lift U w x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have e3 := μ.lift_of_tmul U w p a b
      have e4 := μ.lift_of_tmul V w p (Sec.res g a) (Sec.res g b)
      simp only [Tens.of, DirectSum.lof_eq_of] at e3 e4
      rw [e3, μ.nat g, ← e4, ← DirectSum.lof_eq_of (ULift.{1} R), ← DirectSum.lof_eq_of (ULift.{1} R), Tens.res, DirectSum.lmap_lof]
      rfl
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem Tens.res_of_tmul (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (a : Sec (I.X p.1.1) U) (b : Sec (J.X p.1.2) U) :
    Tens.res g w (Tens.of I J U w p (a ⊗ₜ b)) = Tens.of I J V w p (Sec.res g a ⊗ₜ Sec.res g b) := by
  rw [Tens.res, Tens.of, DirectSum.lmap_lof]
  rfl

theorem Sec.res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  simp only [Sec.res, Sec.map]
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← NatTrans.naturality]

theorem Tens.res_d (I J : Cx R) {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    Tens.res g (w + 1) (Tens.d I J U w x) = Tens.d I J V w (Tens.res g w x) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have e := Tens.res_of_tmul I J g w p a b
      have e1 := Tens.d_of_tmul I J U w p a b
      have e2 := Tens.d_of_tmul I J V w p (Sec.res g a) (Sec.res g b)
      simp only [Tens.of, DirectSum.lof_eq_of] at e e1 e2
      rw [e, e1, e2, map_add (f := _), map_zsmul, ← DirectSum.lof_eq_of (ULift.{1} R), ← DirectSum.lof_eq_of (ULift.{1} R),
        Tens.res, DirectSum.lmap_lof, DirectSum.lmap_lof]
      simp only [TensorProduct.map_tmul, DirectSum.lof_eq_of]
      have h1 := Sec.res_map (I.d p.1.1 (p.1.1 + 1)) g a
      have h2 := Sec.res_map (J.d p.1.2 (p.1.2 + 1)) g b
      simp only [Sec.res] at h1 h2
      rw [h1, h2]
    | add y z hy hz => simp only [map_add (f := _), hy, hz]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.EtC

namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]
open scoped DirectSum TensorProduct

theorem Sec.map_d_d (I : Cx R) (i j k : ℤ) {U : Scheme.{0}} (a : Sec (I.X i) U) :
    Sec.map (I.d j k) (Sec.map (I.d i j) a) = 0 := by
  have h : Sec.map (I.d j k) (Sec.map (I.d i j) a) = Sec.map (I.d i j ≫ I.d j k) a := rfl
  rw [h, I.d_comp_d]
  rfl

theorem Tens.d_d (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w) :
    Tens.d I J U (w + 1) (Tens.d I J U w x) = 0 := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      have e := Tens.d_of_tmul I J U w p a b
      have e1 := Tens.d_of_tmul I J U (w + 1) ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩
        (Sec.map (I.d p.1.1 (p.1.1 + 1)) a) b
      have e2 := Tens.d_of_tmul I J U (w + 1) ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩
        a (Sec.map (J.d p.1.2 (p.1.2 + 1)) b)
      simp only [Tens.of, DirectSum.lof_eq_of] at e e1 e2
      rw [e, map_add (f := _), map_zsmul, e1, e2]
      simp only [Sec.map_d_d, TensorProduct.zero_tmul, TensorProduct.tmul_zero, map_zero, zero_add, smul_zero, add_zero,
        smul_add, Int.negOnePow_succ, Units.val_neg, neg_smul, smul_smul]
      simp
    | add y z hy hz => simp only [map_add (f := _), hy, hz, add_zero]
  | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]

end GlobalTheory.EtC

namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]
open scoped DirectSum TensorProduct

theorem Tens.d_of (I J : Cx R) (U : Scheme.{0}) (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (y : Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) :
    Tens.d I J U w (DirectSum.of _ p y) =
      DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
          ⟨(p.1.1 + 1, p.1.2), by have := p.2; simp only at this ⊢; omega⟩
          (TensorProduct.map (Sec.lin (I.d p.1.1 (p.1.1 + 1)) U) LinearMap.id y) +
        ((p.1.1.negOnePow : ℤˣ) : ℤ) • DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w + 1} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U)
          ⟨(p.1.1, p.1.2 + 1), by have := p.2; simp only at this ⊢; omega⟩
          (TensorProduct.map LinearMap.id (Sec.lin (J.d p.1.2 (p.1.2 + 1)) U) y) := by
  rw [← DirectSum.lof_eq_of (ULift.{1} R)]
  simp only [Tens.d, DirectSum.toModule_lof]
  simp [Tens.of, DirectSum.lof_eq_of]

def Tens.upper {I J : Cx R} {U : Scheme.{0}} {w : ℤ} (n : ℤ) (x : Tens I J U w) : Tens I J U w :=
  DFinsupp.filter (fun p : {p : ℤ × ℤ // p.1 + p.2 = w} => n ≤ p.1.2) x

theorem Tens.upper_apply {I J : Cx R} {U : Scheme.{0}} {w : ℤ} (n : ℤ) (x : Tens I J U w) (p) :
    Tens.upper n x p = if n ≤ p.1.2 then x p else 0 := DFinsupp.filter_apply _ _ _

theorem Tens.upper_of {I J : Cx R} {U : Scheme.{0}} {w : ℤ} (n : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w})
    (y : Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) :
    Tens.upper n (DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} => Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) p y) =
      if n ≤ p.1.2 then DirectSum.of _ p y else 0 := by
  unfold Tens.upper
  rw [DirectSum.of, DFinsupp.singleAddHom_apply, DFinsupp.filter_single]

theorem Tens.upper_add {I J : Cx R} {U : Scheme.{0}} {w : ℤ} (n : ℤ) (x y : Tens I J U w) :
    Tens.upper n (x + y) = Tens.upper n x + Tens.upper n y := DFinsupp.filter_add _ _ _

theorem Tens.d_upper_low (I J : Cx R) (U : Scheme.{0}) (w n : ℤ) (x : Tens I J U w)
    (q : {q : ℤ × ℤ // q.1 + q.2 = w + 1}) (hq : q.1.2 < n) : Tens.d I J U w (Tens.upper n x) q = 0 := by
  induction x using DirectSum.induction_on with
  | zero => simp [Tens.upper]
  | of p y =>
    rw [Tens.upper_of]
    split_ifs with hp
    · rw [Tens.d_of, DFinsupp.add_apply, DFinsupp.smul_apply, DirectSum.of_eq_of_ne, DirectSum.of_eq_of_ne, smul_zero, add_zero]
      · intro h; subst h; simp at hq; omega
      · intro h; subst h; simp at hq; omega
    · simp
  | add x y hx hy => rw [Tens.upper_add, map_add (f := _), DFinsupp.add_apply, hx, hy, add_zero]

theorem Tens.d_upper_edge (I J : Cx R) (U : Scheme.{0}) (w n s : ℤ) (h : s + n = w) (x : Tens I J U w) :
    Tens.d I J U w (Tens.upper n x) ⟨(s + 1, n), by simp only; omega⟩ =
      TensorProduct.map (Sec.lin (I.d s (s + 1)) U) LinearMap.id (x ⟨(s, n), h⟩) := by
  induction x using DirectSum.induction_on with
  | zero => simp [Tens.upper]
  | of p y =>
    obtain ⟨⟨a, b⟩, hp⟩ := p
    rw [Tens.upper_of]
    by_cases hab : a = s ∧ b = n
    · obtain ⟨rfl, rfl⟩ := hab
      rw [if_pos le_rfl, Tens.d_of, DFinsupp.add_apply, DFinsupp.smul_apply, DirectSum.of_eq_same, DirectSum.of_eq_of_ne,
        smul_zero, add_zero, DirectSum.of_eq_same]
      intro e; simp at e
    · rw [DirectSum.of_eq_of_ne]
      · split_ifs with hb
        · rw [Tens.d_of, DFinsupp.add_apply, DFinsupp.smul_apply, DirectSum.of_eq_of_ne, DirectSum.of_eq_of_ne,
            smul_zero, add_zero, map_zero]
          · intro e; simp at e; simp at hb; omega
          · intro e; simp at e; simp at hb hp; omega
        · simp
      · intro e; simp at e; omega
  | add x y hx hy => rw [Tens.upper_add, map_add (f := _), DFinsupp.add_apply, hx, hy, DFinsupp.add_apply, map_add (f := _)]

end GlobalTheory.EtC

namespace GlobalTheory.EtC
variable {R : Type} [CommRing R]
open scoped DirectSum TensorProduct

theorem Sec.eq_zero_of_isZero {F : Shv R} (hF : IsZero F) {U : Scheme.{0}} (x : Sec F U) : x = 0 := by
  have h : Sec.map (𝟙 F) x = Sec.map (0 : F ⟶ F) x := by rw [hF.eq_of_src (𝟙 F) 0]
  exact h

theorem tensor_eq_zero_left {S M N : Type*} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    (h : ∀ m : M, m = 0) (y : M ⊗[S] N) : y = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rfl
  | tmul m n => rw [h m, TensorProduct.zero_tmul]
  | add y z hy hz => rw [hy, hz, add_zero]

theorem tensor_eq_zero_right {S M N : Type*} [CommRing S] [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]
    (h : ∀ n : N, n = 0) (y : M ⊗[S] N) : y = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => rfl
  | tmul m n => rw [h n, TensorProduct.tmul_zero]
  | add y z hy hz => rw [hy, hz, add_zero]

theorem Tens.res_apply {I J : Cx R} {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w) (p) :
    Tens.res g w x p = TensorProduct.map ((I.X p.1.1).obj.map g.op).hom ((J.X p.1.2).obj.map g.op).hom (x p) := rfl

theorem Tens.res_comp {I J : Cx R} {W V U : Scheme.{0}} (m : W ⟶ V) (k : V ⟶ U) (w : ℤ) (x : Tens I J U w) :
    Tens.res (m ≫ k) w x = Tens.res m w (Tens.res k w x) := by
  refine DFinsupp.ext fun p => ?_
  rw [Tens.res_apply, Tens.res_apply, Tens.res_apply, ← LinearMap.comp_apply, ← TensorProduct.map_comp]
  simp [op_comp, Functor.map_comp]

theorem rTensor_res_comm {B C M : Shv R} (g : B ⟶ C) {V U : Scheme.{0}} (k : V ⟶ U)
    (x : Sec B U ⊗[ULift.{1} R] Sec M U) :
    LinearMap.rTensor _ (g.hom.app (op V)).hom (TensorProduct.map (B.obj.map k.op).hom (M.obj.map k.op).hom x) =
      TensorProduct.map (C.obj.map k.op).hom (M.obj.map k.op).hom (LinearMap.rTensor _ (g.hom.app (op U)).hom x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    have h := Sec.res_map g k a
    simp only [Sec.res, Sec.map] at h
    simp only [TensorProduct.map_tmul, LinearMap.rTensor_tmul, h]
  | add y z hy hz => simp only [map_add (f := _), hy, hz]

theorem Tens.cycle_loc_boundary {C J : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b]
    (hJ : ∀ t, FlatS (J.X t)) (hC : C.Acyclic) (w : ℤ) (U : Scheme.{0}) (x : Tens C J U (w + 1))
    (hx : Tens.d C J U (w + 1) x = 0) :
    Loc U fun V g => ∃ y : Tens C J V w, Tens.d C J V w y = Tens.res g (w + 1) x := by
  obtain ⟨L_all, L_mono, -, -, L_trans, -, -⟩ := loc_calculus
  let P : ℤ → Prop := fun n => ∀ (U : Scheme.{0}) (x : Tens C J U (w + 1)), Tens.upper n x = x →
    Tens.d C J U (w + 1) x = 0 → Loc U fun V g => ∃ y : Tens C J V w, Tens.d C J V w y = Tens.res g (w + 1) x
  have base : P (w + 2 - a) := by
    intro U x hu _
    have hx0 : x = 0 := by
      refine DFinsupp.ext fun p => ?_
      rw [← hu, Tens.upper_apply]
      split_ifs with hp
      · have hs : p.1.1 < a := by have := p.2; omega
        exact tensor_eq_zero_left (fun m => Sec.eq_zero_of_isZero (C.isZero_of_isStrictlyGE a p.1.1 hs) m) _
      · rfl
    refine L_all _ _ fun V g => ⟨0, ?_⟩
    rw [hx0, map_zero, map_zero]
  have step : ∀ n, P (n + 1) → P n := by
    intro n ih U x hu hdx
    have hedge : LinearMap.rTensor _ ((C.d (w - n + 1) (w - n + 1 + 1)).hom.app (op U)).hom
        (x ⟨(w - n + 1, n), by simp only; omega⟩) = 0 := by
      have := Tens.d_upper_edge C J U (w + 1) n (w - n + 1) (by omega) x
      rw [hu, hdx] at this
      exact this.symm
    have hexact : ∀ (U : Scheme.{0}) (b : Sec (C.X (w - n + 1)) U), Sec.map (C.d (w - n + 1) (w - n + 1 + 1)) b = 0 →
        Loc U fun V k => ∃ a : Sec (C.X (w - n)) V, Sec.map (C.d (w - n) (w - n + 1)) a = Sec.res k b :=
      (GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally R (C.sc' (w - n) (w - n + 1) (w - n + 1 + 1))).mp
        ((C.exactAt_iff' (w - n) (w - n + 1) (w - n + 1 + 1) (by simp) (by simp)).mp (hC (w - n + 1)))
    have hloc : Loc U fun V k => LinearMap.rTensor _ ((C.d (w - n + 1) (w - n + 1 + 1)).hom.app (op V)).hom
        (TensorProduct.map ((C.X (w - n + 1)).obj.map k.op).hom ((J.X n).obj.map k.op).hom
          (x ⟨(w - n + 1, n), by simp only; omega⟩)) = 0 :=
      L_all _ _ fun V k => by rw [rTensor_res_comm, hedge, map_zero]
    have hrow := GlobalTheory.T.tensor_flat_etaleSheaf_preserves_local_exactness R (J.X n) (hJ n) (C.d (w - n) (w - n + 1)) (C.d (w - n + 1) (w - n + 1 + 1))
      (C.d_comp_d _ _ _) hexact U _ hloc
    apply L_trans
    refine L_mono _ _ _ hrow ?_
    rintro V k ⟨y0, hy0⟩
    let y : Tens C J V w := DirectSum.of (fun q : {q : ℤ × ℤ // q.1 + q.2 = w} =>
      Sec (C.X q.1.1) V ⊗[ULift.{1} R] Sec (J.X q.1.2) V) ⟨(w - n, n), by simp only; omega⟩ y0
    have hyu : Tens.upper n y = y := by
      simp only [y]
      rw [Tens.upper_of, if_pos le_rfl]
    let x' : Tens C J V (w + 1) := Tens.res k (w + 1) x - Tens.d C J V w y
    have hx'd : Tens.d C J V (w + 1) x' = 0 := by
      simp only [x', map_sub, ← Tens.res_d, hdx, map_zero, Tens.d_d, sub_zero]
    have hx'u : Tens.upper (n + 1) x' = x' := by
      refine DFinsupp.ext fun q => ?_
      rw [Tens.upper_apply]
      split_ifs with hq
      · rfl
      symm
      show (Tens.res k (w + 1) x - Tens.d C J V w y) q = 0
      rw [DFinsupp.sub_apply]
      rcases lt_or_eq_of_le (Int.lt_add_one_iff.mp (not_le.mp hq)) with hlt | heq
      · rw [Tens.res_apply, ← hu, Tens.upper_apply, if_neg (by omega), map_zero, ← hyu,
          Tens.d_upper_low C J V w n _ q hlt, sub_zero]
      · obtain ⟨⟨s', t'⟩, hq'⟩ := q
        simp only at heq hq'
        subst heq
        obtain rfl : s' = w - t' + 1 := by omega
        rw [Tens.res_apply, ← hyu, Tens.d_upper_edge C J V w t' (w - t') (by omega) y]
        simp only [y]
        rw [DirectSum.of_eq_same, sub_eq_zero]
        exact hy0.symm
    refine L_mono _ _ _ (ih V x' hx'u hx'd) ?_
    rintro W m ⟨z, hz⟩
    refine ⟨z + Tens.res m w y, ?_⟩
    rw [map_add (f := _), hz, Tens.res_comp, ← Tens.res_d]
    simp only [x', map_sub, sub_add_cancel]
  have hall : ∀ k : ℕ, P (w + 2 - a - k) := by
    intro k
    induction k with
    | zero => simpa using base
    | succ k ih =>
      have e : w + 2 - a - ((k + 1 : ℕ) : ℤ) + 1 = w + 2 - a - (k : ℤ) := by push_cast; ring
      exact step _ (e ▸ ih)
  refine hall (w + 2 - a - b).toNat U x ?_ hx
  refine DFinsupp.ext fun p => ?_
  rw [Tens.upper_apply]
  split_ifs with hp
  · rfl
  · have ht : p.1.2 < b := by omega
    exact (tensor_eq_zero_right (fun m => Sec.eq_zero_of_isZero (J.isZero_of_isStrictlyGE b p.1.2 ht) m) _).symm

theorem acyclic_of_isTensor : ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b]
    (τ : Pair C J T), τ.IsTensor → (∀ t, FlatS (J.X t)) → C.Acyclic → T.Acyclic := by
  intro R _ C J T a b _ _ τ hT hJ hC j
  obtain ⟨L_all, L_mono, -, -, L_trans, -, -⟩ := loc_calculus
  obtain ⟨w, rfl⟩ : ∃ w, j = w + 1 := ⟨j - 1, by ring⟩
  rw [T.exactAt_iff' w (w + 1) (w + 1 + 1) (by simp) (by simp), GlobalTheory.T.etaleSheaf_shortComplex_exact_iff_locally]
  rintro U (z : Sec (T.X (w + 1)) U) (hz' : Sec.map (T.d (w + 1) (w + 1 + 1)) z = 0)
  apply L_trans
  refine L_mono _ _ _ (hT.1 U (w + 1) z) ?_
  rintro V g ⟨x, hx⟩
  have h1 : τ.lift V (w + 1 + 1) (Tens.d C J V (w + 1) x) = 0 := by
    rw [Pair.lift_tensD, hx, ← Sec.res_map, hz']
    exact map_zero _
  apply L_trans
  refine L_mono _ _ _ (hT.2 V (w + 1 + 1) _ h1) ?_
  intro W k hk
  rw [Tens.res_d] at hk
  refine L_mono _ _ _ (Tens.cycle_loc_boundary a b hJ hC w W _ hk) ?_
  rintro W' m ⟨y, hy⟩
  refine ⟨τ.lift W' w y, ?_⟩
  change Sec.map (T.d w (w + 1)) (τ.lift W' w y) = _
  rw [← Pair.lift_tensD, hy, Pair.lift_tensRes, Pair.lift_tensRes, hx]
  simp [Sec.res, op_comp, Functor.map_comp]

end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcyclicTensorAcyclicFlatEtaleComplexStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acyclic_tensor_acyclic_flatEtaleComplex : ∀ (R : Type) [CommRing R] {C J T : Cx R} (a b : ℤ) [C.IsStrictlyGE a] [J.IsStrictlyGE b] (τ : Pair C J T), τ.IsTensor → (∀ t, FlatS (J.X t)) → C.Acyclic → T.Acyclic := by
  first | (exact @GlobalTheory.EtC.acyclic_of_isTensor) | (exact GlobalTheory.EtC.acyclic_of_isTensor) | (intros; apply GlobalTheory.EtC.acyclic_of_isTensor  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFlatComplexPreservesQuasiIso
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.TensQis
variable {R : Type} [CommRing R]
theorem sm_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) : Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl
theorem sm_add {F G : Shv R} (φ ψ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) : Sec.map (φ + ψ) x = Sec.map φ x + Sec.map ψ x := rfl
theorem sm_neg {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) : Sec.map (-φ) x = -Sec.map φ x := rfl
theorem sm_zero {F G : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (0 : F ⟶ G) x = 0 := rfl
theorem sm_id {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := rfl
theorem sm_res {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) : Sec.map φ (Sec.res g x) = Sec.res g (Sec.map φ x) :=
  congrArg (fun k => k.hom x) (φ.hom.naturality g.op)
theorem sm_madd {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x y : Sec F U) : Sec.map φ (x + y) = Sec.map φ x + Sec.map φ y := map_add _ _ _
theorem sm_mzero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} : Sec.map φ (0 : Sec F U) = 0 := map_zero _
theorem sm_munits {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (e : ℤˣ) (x : Sec F U) : Sec.map φ (e • x) = e • Sec.map φ x := by
  rw [Units.smul_def, Units.smul_def]; exact map_zsmul _ _ _
theorem rs_madd {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (x y : Sec F U) : Sec.res g (x + y) = Sec.res g x + Sec.res g y := map_add _ _ _

section Cone
variable {K L : Cx R} (φ : K ⟶ L) {U : Scheme.{0}}

theorem fst_inl (p : ℤ) (a : Sec (K.X (p + 1)) U) :
    Sec.map ((mappingCone.fst φ).1.v p (p + 1) rfl) (Sec.map ((mappingCone.inl φ).v (p + 1) p (by omega)) a) = a := by
  rw [← sm_comp, mappingCone.inl_v_fst_v φ (p + 1) p rfl, sm_id]
theorem fst_inr (p : ℤ) (a : Sec (L.X p) U) :
    Sec.map ((mappingCone.fst φ).1.v p (p + 1) rfl) (Sec.map ((mappingCone.inr φ).f p) a) = 0 := by
  rw [← sm_comp, mappingCone.inr_f_fst_v φ p (p + 1) rfl, sm_zero]
theorem snd_inl (p : ℤ) (a : Sec (K.X (p + 1)) U) :
    Sec.map ((mappingCone.snd φ).v p p (add_zero p)) (Sec.map ((mappingCone.inl φ).v (p + 1) p (by omega)) a) = 0 := by
  rw [← sm_comp, mappingCone.inl_v_snd_v φ (p + 1) p (by omega), sm_zero]
theorem snd_inr (p : ℤ) (a : Sec (L.X p) U) :
    Sec.map ((mappingCone.snd φ).v p p (add_zero p)) (Sec.map ((mappingCone.inr φ).f p) a) = a := by
  rw [← sm_comp, mappingCone.inr_f_snd_v φ p, sm_id]
theorem cone_eta (p : ℤ) (z : Sec ((mappingCone φ).X p) U) :
    z = Sec.map ((mappingCone.inl φ).v (p + 1) p (by omega)) (Sec.map ((mappingCone.fst φ).1.v p (p + 1) rfl) z) +
      Sec.map ((mappingCone.inr φ).f p) (Sec.map ((mappingCone.snd φ).v p p (add_zero p)) z) := by
  have := congrArg (fun k => Sec.map k z) (mappingCone.id_X φ p (p + 1) rfl)
  beta_reduce at this
  rw [sm_add, sm_comp, sm_comp, sm_id] at this
  exact this.symm
theorem cone_ext {p : ℤ} {z z' : Sec ((mappingCone φ).X p) U}
    (h1 : Sec.map ((mappingCone.fst φ).1.v p (p + 1) rfl) z = Sec.map ((mappingCone.fst φ).1.v p (p + 1) rfl) z')
    (h2 : Sec.map ((mappingCone.snd φ).v p p (add_zero p)) z = Sec.map ((mappingCone.snd φ).v p p (add_zero p)) z') : z = z' := by
  rw [cone_eta φ p z, cone_eta φ p z', h1, h2]
theorem fst_d (p : ℤ) (z : Sec ((mappingCone φ).X p) U) :
    Sec.map ((mappingCone.fst φ).1.v (p + 1) (p + 1 + 1) rfl) (Sec.map ((mappingCone φ).d p (p + 1)) z) =
      -Sec.map (K.d (p + 1) (p + 1 + 1)) (Sec.map ((mappingCone.fst φ).1.v p (p + 1) rfl) z) := by
  rw [← sm_comp, mappingCone.d_fst_v φ p (p + 1) (p + 1 + 1) rfl rfl, sm_neg, sm_comp]
theorem snd_d (p : ℤ) (z : Sec ((mappingCone φ).X p) U) :
    Sec.map ((mappingCone.snd φ).v (p + 1) (p + 1) (add_zero _)) (Sec.map ((mappingCone φ).d p (p + 1)) z) =
      Sec.map (φ.f (p + 1)) (Sec.map ((mappingCone.fst φ).1.v p (p + 1) rfl) z) +
        Sec.map (L.d p (p + 1)) (Sec.map ((mappingCone.snd φ).v p p (add_zero p)) z) := by
  rw [← sm_comp, mappingCone.d_snd_v φ p (p + 1) rfl, sm_add, sm_comp, sm_comp]
end Cone

variable {I I' J T T' : Cx R}

def coneMul (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T') (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) :
    Sec ((mappingCone f).X s) U →ₗ[ULift.{1} R] Sec (J.X t) U →ₗ[ULift.{1} R] Sec ((mappingCone u).X w) U :=
  ((τ.mul U (s + 1) t (w + 1) (by omega)) ∘ₗ (((mappingCone.fst f).1.v s (s + 1) rfl).hom.app (op U)).hom).compr₂
      (((mappingCone.inl u).v (w + 1) w (by omega)).hom.app (op U)).hom +
    ((τ'.mul U s t w h) ∘ₗ (((mappingCone.snd f).v s s (add_zero s)).hom.app (op U)).hom).compr₂
      (((mappingCone.inr u).f w).hom.app (op U)).hom

theorem coneMul_apply (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T') (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w)
    (c : Sec ((mappingCone f).X s) U) (b : Sec (J.X t) U) :
    coneMul τ τ' f u U s t w h c b =
      Sec.map ((mappingCone.inl u).v (w + 1) w (by omega))
          (τ.mul U (s + 1) t (w + 1) (by omega) (Sec.map ((mappingCone.fst f).1.v s (s + 1) rfl) c) b) +
        Sec.map ((mappingCone.inr u).f w) (τ'.mul U s t w h (Sec.map ((mappingCone.snd f).v s s (add_zero s)) c) b) := rfl

def conePair (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T') (hc : τ.Compat τ' f (𝟙 J) u) :
    Pair (mappingCone f) J (mappingCone u) where
  mul := coneMul τ τ' f u
  nat := by
    intro V U g s t w h c b
    rw [coneMul_apply, coneMul_apply, rs_madd, ← sm_res, ← sm_res, τ.nat, τ'.nat, ← sm_res, ← sm_res]
  leibniz := by
    intro U s t w h c b
    apply cone_ext u
    · rw [← sm_comp, mappingCone.d_fst_v u w (w + 1) (w + 1 + 1) rfl rfl, sm_neg, sm_comp]
      simp only [coneMul_apply, sm_madd, sm_munits, fst_inl, fst_inr, add_zero, fst_d, map_neg, LinearMap.neg_apply, τ.leibniz]
      rw [Int.negOnePow_succ, Units.neg_smul, neg_add, neg_neg]
    · rw [← sm_comp, mappingCone.d_snd_v u w (w + 1) rfl, sm_add, sm_comp, sm_comp]
      simp only [coneMul_apply, sm_madd, sm_munits, snd_inl, snd_inr, fst_inl, fst_inr, zero_add, add_zero, snd_d,
        LinearMap.map_add₂, τ'.leibniz, hc, HomologicalComplex.id_f, sm_id]
      rw [hc U (s + 1) t (w + 1) (by omega), HomologicalComplex.id_f, sm_id]
      abel

end GlobalTheory.EtC.TensQis
end

noncomputable section
namespace GlobalTheory.EtC.TensQis
open scoped DirectSum TensorProduct
variable {R : Type} [CommRing R] {I I' J T T' : Cx R}

def upI (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w}) : {p : ℤ × ℤ // p.1 + p.2 = w + 1} :=
  ⟨(p.1.1 + 1, p.1.2), by have := p.2; omega⟩

def dnI (w : ℤ) (p : {p : ℤ × ℤ // p.1 + p.2 = w + 1}) : {p : ℤ × ℤ // p.1 + p.2 = w} :=
  ⟨(p.1.1 - 1, p.1.2), by have := p.2; omega⟩

def tInl (f : I ⟶ I') (U : Scheme.{0}) (w : ℤ) : Tens I J U (w + 1) →ₗ[ULift.{1} R] Tens (mappingCone f) J U w :=
  by classical exact DirectSum.toModule _ _ _ fun p =>
    DirectSum.lof _ _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        Sec ((mappingCone f).X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) (dnI w p) ∘ₗ
      TensorProduct.map (((mappingCone.inl f).v p.1.1 (p.1.1 - 1) (by omega)).hom.app (op U)).hom LinearMap.id

def tInr (f : I ⟶ I') (U : Scheme.{0}) (w : ℤ) : Tens I' J U w →ₗ[ULift.{1} R] Tens (mappingCone f) J U w :=
  by classical exact DirectSum.toModule _ _ _ fun p =>
    DirectSum.lof _ _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        Sec ((mappingCone f).X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) p ∘ₗ
      TensorProduct.map (((mappingCone.inr f).f p.1.1).hom.app (op U)).hom LinearMap.id

def tFst (f : I ⟶ I') (U : Scheme.{0}) (w : ℤ) : Tens (mappingCone f) J U w →ₗ[ULift.{1} R] Tens I J U (w + 1) :=
  by classical exact DirectSum.toModule _ _ _ fun p =>
    DirectSum.lof _ _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w + 1} =>
        Sec (I.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) (upI w p) ∘ₗ
      TensorProduct.map (((mappingCone.fst f).1.v p.1.1 (p.1.1 + 1) rfl).hom.app (op U)).hom LinearMap.id

def tSnd (f : I ⟶ I') (U : Scheme.{0}) (w : ℤ) : Tens (mappingCone f) J U w →ₗ[ULift.{1} R] Tens I' J U w :=
  by classical exact DirectSum.toModule _ _ _ fun p =>
    DirectSum.lof _ _ (fun q : {p : ℤ × ℤ // p.1 + p.2 = w} =>
        Sec (I'.X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) p ∘ₗ
      TensorProduct.map (((mappingCone.snd f).v p.1.1 p.1.1 (add_zero _)).hom.app (op U)).hom LinearMap.id

theorem mul_fst_inl (f : I ⟶ I') (τ : Pair I J T) (U : Scheme.{0}) (s t w' : ℤ) (hst : s + t = w') (s' : ℤ) (e : s' = s)
    (h1 : s' + t = w') (h2 : s - 1 + 1 = s') (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    τ.mul U s' t w' h1 (Sec.map ((mappingCone.fst f).1.v (s - 1) s' h2) (Sec.map ((mappingCone.inl f).v s (s - 1) (by omega)) a)) b =
      τ.mul U s t w' hst a b := by
  subst e
  rw [← sm_comp, mappingCone.inl_v_fst_v, sm_id]

theorem lift_tInl (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T') (hc : τ.Compat τ' f (𝟙 J) u)
    (U : Scheme.{0}) (w : ℤ) (x : Tens I J U (w + 1)) :
    (conePair τ τ' f u hc).lift U w (tInl f U w x) = Sec.map ((mappingCone.inl u).v (w + 1) w (by omega)) (τ.lift U (w + 1) x) := by
  have : (conePair τ τ' f u hc).lift U w ∘ₗ tInl f U w =
      (((mappingCone.inl u).v (w + 1) w (by omega)).hom.app (op U)).hom ∘ₗ τ.lift U (w + 1) := by
    refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
    obtain ⟨⟨s, t⟩, hp⟩ := p
    simp only [LinearMap.comp_apply, tInl, Pair.lift, DirectSum.toModule_lof, TensorProduct.map_tmul, LinearMap.id_apply,
      TensorProduct.lift.tmul]
    change coneMul τ τ' f u U (s - 1) t w (by omega) (Sec.map ((mappingCone.inl f).v s (s - 1) (by omega)) a) b =
      Sec.map ((mappingCone.inl u).v (w + 1) w (by omega)) (τ.mul U s t (w + 1) hp a b)
    rw [coneMul_apply, ← sm_comp _ ((mappingCone.snd f).v _ _ _), mappingCone.inl_v_snd_v, sm_zero, map_zero,
      LinearMap.zero_apply, sm_mzero, add_zero, mul_fst_inl f τ U s t (w + 1) hp _ (by omega)]
  exact congrArg (fun k => k x) this

theorem lift_tInr (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T') (hc : τ.Compat τ' f (𝟙 J) u)
    (U : Scheme.{0}) (w : ℤ) (x : Tens I' J U w) :
    (conePair τ τ' f u hc).lift U w (tInr f U w x) = Sec.map ((mappingCone.inr u).f w) (τ'.lift U w x) := by
  have : (conePair τ τ' f u hc).lift U w ∘ₗ tInr f U w = (((mappingCone.inr u).f w).hom.app (op U)).hom ∘ₗ τ'.lift U w := by
    refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
    obtain ⟨⟨s, t⟩, hp⟩ := p
    simp only [LinearMap.comp_apply, tInr, Pair.lift, DirectSum.toModule_lof, TensorProduct.map_tmul, LinearMap.id_apply,
      TensorProduct.lift.tmul]
    change coneMul τ τ' f u U s t w hp (Sec.map ((mappingCone.inr f).f s) a) b =
      Sec.map ((mappingCone.inr u).f w) (τ'.mul U s t w hp a b)
    rw [coneMul_apply, fst_inr, map_zero, LinearMap.zero_apply, sm_mzero, zero_add, snd_inr]
  exact congrArg (fun k => k x) this

theorem lof_shift (f : I ⟶ I') (U : Scheme.{0}) (w : ℤ) [DecidableEq {p : ℤ × ℤ // p.1 + p.2 = w}] (s t : ℤ) (hp : s + t = w)
    (s'' : ℤ) (e : s'' = s) (h : s'' + t = w) (h' : s + 1 + -1 = s'') (y : Sec (I.X (s + 1)) U) (b : Sec (J.X t) U) :
    DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w}
        (fun q => Sec ((mappingCone f).X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) ⟨(s'', t), h⟩
        (Sec.map ((mappingCone.inl f).v (s + 1) s'' h') y ⊗ₜ b) =
      DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w}
        (fun q => Sec ((mappingCone f).X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) ⟨(s, t), hp⟩
        (Sec.map ((mappingCone.inl f).v (s + 1) s (by omega)) y ⊗ₜ b) := by
  subst e; rfl

theorem tDecomp (f : I ⟶ I') (U : Scheme.{0}) (w : ℤ) (x : Tens (mappingCone f) J U w) :
    tInl f U w (tFst f U w x) + tInr f U w (tSnd f U w x) = x := by
  have : (tInl f U w ∘ₗ tFst f U w + tInr f U w ∘ₗ tSnd f U w :
      Tens (mappingCone f) J U w →ₗ[ULift.{1} R] Tens (mappingCone f) J U w) = LinearMap.id := by
    refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
    obtain ⟨⟨s, t⟩, hp⟩ := p
    simp only [LinearMap.add_apply, LinearMap.comp_apply, tInl, tInr, tFst, tSnd, DirectSum.toModule_lof,
      TensorProduct.map_tmul, LinearMap.id_apply]
    change DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w}
        (fun q => Sec ((mappingCone f).X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) ⟨(s + 1 - 1, t), by omega⟩
        (Sec.map ((mappingCone.inl f).v (s + 1) (s + 1 - 1) (by omega)) (Sec.map ((mappingCone.fst f).1.v s (s + 1) rfl) a) ⊗ₜ b) +
      DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w}
        (fun q => Sec ((mappingCone f).X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) ⟨(s, t), hp⟩
        (Sec.map ((mappingCone.inr f).f s) (Sec.map ((mappingCone.snd f).v s s (add_zero s)) a) ⊗ₜ b) =
      DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w}
        (fun q => Sec ((mappingCone f).X q.1.1) U ⊗[ULift.{1} R] Sec (J.X q.1.2) U) ⟨(s, t), hp⟩ (a ⊗ₜ b)
    rw [lof_shift f U w s t hp _ (by omega), ← map_add (f := _), ← TensorProduct.add_tmul, ← cone_eta]
  exact congrArg (fun k => k x) this

theorem res_tInl (f : I ⟶ I') {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U (w + 1)) :
    Tens.res g w (tInl f U w x) = tInl f V w (Tens.res g (w + 1) x) := by
  have : (Tens.res g w ∘ₗ tInl f U w : Tens I J U (w + 1) →ₗ[ULift.{1} R] Tens (mappingCone f) J V w) =
      tInl f V w ∘ₗ Tens.res g (w + 1) := by
    refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
    obtain ⟨⟨s, t⟩, hp⟩ := p
    simp only [LinearMap.comp_apply, tInl, Tens.res, DirectSum.toModule_lof, DirectSum.lmap_lof, TensorProduct.map_tmul,
      LinearMap.id_apply]
    congr 1
    change Sec.res g (Sec.map ((mappingCone.inl f).v s (s - 1) (by omega)) a) ⊗ₜ[ULift.{1} R] Sec.res g b =
      Sec.map ((mappingCone.inl f).v s (s - 1) (by omega)) (Sec.res g a) ⊗ₜ[ULift.{1} R] Sec.res g b
    rw [sm_res]
  exact congrArg (fun k => k x) this

theorem res_tInr (f : I ⟶ I') {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I' J U w) :
    Tens.res g w (tInr f U w x) = tInr f V w (Tens.res g w x) := by
  have : (Tens.res g w ∘ₗ tInr f U w : Tens I' J U w →ₗ[ULift.{1} R] Tens (mappingCone f) J V w) =
      tInr f V w ∘ₗ Tens.res g w := by
    refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
    obtain ⟨⟨s, t⟩, hp⟩ := p
    simp only [LinearMap.comp_apply, tInr, Tens.res, DirectSum.toModule_lof, DirectSum.lmap_lof, TensorProduct.map_tmul,
      LinearMap.id_apply]
    congr 1
    change Sec.res g (Sec.map ((mappingCone.inr f).f s) a) ⊗ₜ[ULift.{1} R] Sec.res g b =
      Sec.map ((mappingCone.inr f).f s) (Sec.res g a) ⊗ₜ[ULift.{1} R] Sec.res g b
    rw [sm_res]
  exact congrArg (fun k => k x) this

theorem conePair_isTensor (τ : Pair I J T) (τ' : Pair I' J T') (f : I ⟶ I') (u : T ⟶ T') (hc : τ.Compat τ' f (𝟙 J) u)
    (hτ : τ.IsTensor) (hτ' : τ'.IsTensor) : (conePair τ τ' f u hc).IsTensor := by
  obtain ⟨-, loc_mono, loc_and, -, -, -, -⟩ := GlobalTheory.EtC.loc_calculus
  constructor
  · intro U w y
    have h1 := hτ.1 U (w + 1) (Sec.map ((mappingCone.fst u).1.v w (w + 1) rfl) y)
    have h2 := hτ'.1 U w (Sec.map ((mappingCone.snd u).v w w (add_zero w)) y)
    refine loc_mono _ _ _ (loc_and _ _ _ h1 h2) ?_
    rintro V g ⟨⟨x1, hx1⟩, ⟨x2, hx2⟩⟩
    refine ⟨tInl f V w x1 + tInr f V w x2, ?_⟩
    rw [map_add (f := _), lift_tInl, lift_tInr, hx1, hx2, sm_res, sm_res, ← rs_madd, ← cone_eta]
  · intro U w x hx
    rw [← tDecomp f U w x, map_add (f := _), lift_tInl, lift_tInr] at hx
    have e1 : τ.lift U (w + 1) (tFst f U w x) = 0 := by
      have := congrArg (fun z => Sec.map ((mappingCone.fst u).1.v w (w + 1) rfl) z) hx
      simpa only [sm_madd, fst_inl, fst_inr, add_zero, sm_mzero] using this
    have e2 : τ'.lift U w (tSnd f U w x) = 0 := by
      have := congrArg (fun z => Sec.map ((mappingCone.snd u).v w w (add_zero w)) z) hx
      simpa only [sm_madd, snd_inl, snd_inr, zero_add, sm_mzero] using this
    refine loc_mono _ _ _ (loc_and _ _ _ (hτ.2 U (w + 1) _ e1) (hτ'.2 U w _ e2)) ?_
    rintro V g ⟨h1, h2⟩
    rw [← tDecomp f U w x, map_add (f := _), res_tInl, res_tInr, h1, h2, map_zero, map_zero, add_zero]

theorem quasiIso_of_cone_acyclic {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    {K L : CochainComplex 𝒜 ℤ} (u : K ⟶ L) (h : (CochainComplex.mappingCone u).Acyclic) : QuasiIso u := by
  rw [← HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at h
  have hu : HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)
      ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map u) := by
    rw [HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    exact ((HomotopyCategory.subcategoryAcyclic 𝒜).trW_iff_of_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished u)).2 h
  rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff] at hu

end GlobalTheory.EtC.TensQis

namespace GlobalTheory.EtC

theorem tensor_quasiIso : ∀ (R : Type) [CommRing R] {I I' J T T' : Cx R} [I.IsStrictlyGE 0] [I'.IsStrictlyGE 0]
    [J.IsStrictlyGE 0] (τ : Pair I J T) (τ' : Pair I' J T'), τ.IsTensor → τ'.IsTensor → (∀ t, FlatS (J.X t)) →
    ∀ (f : I ⟶ I') [QuasiIso f] (u : T ⟶ T'), τ.Compat τ' f (𝟙 J) u → QuasiIso u := by
  intro R _ I I' J T T' _ _ _ τ τ' hτ hτ' hJ f _ u hc
  haveI : (mappingCone f).IsStrictlyGE (-1) := CochainComplex.isStrictlyGE_mappingCone f 0 0 (-1)
  have hC := GlobalTheory.mappingCone_acyclic_of_quasiIso f
  exact TensQis.quasiIso_of_cone_acyclic u (GlobalTheory.T.acyclic_tensor_acyclic_flatEtaleComplex R (-1) 0 (TensQis.conePair τ τ' f u hc)
    (TensQis.conePair_isTensor τ τ' f u hc hτ hτ') hJ hC)

end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorFlatComplexPreservesQuasiIsoStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_flat_complex_preserves_quasiIso : ∀ (R : Type) [CommRing R] {I I' J T T' : Cx R} [I.IsStrictlyGE 0] [I'.IsStrictlyGE 0] [J.IsStrictlyGE 0] (τ : Pair I J T) (τ' : Pair I' J T'), τ.IsTensor → τ'.IsTensor → (∀ t, FlatS (J.X t)) → ∀ (f : I ⟶ I') [QuasiIso f] (u : T ⟶ T'), τ.Compat τ' f (𝟙 J) u → QuasiIso u := by
  first | (exact @GlobalTheory.EtC.tensor_quasiIso) | (exact GlobalTheory.EtC.tensor_quasiIso) | (intros; apply GlobalTheory.EtC.tensor_quasiIso  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTateTwistResolutionTensorFlat
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

section
variable {R : Type} [CommRing R]

theorem sec_map_res' {F G : Shv R} (ψ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (z : Sec F U) :
    Sec.map ψ (Sec.res g z) = Sec.res g (Sec.map ψ z) :=
  congrArg (fun f => f.hom z) (ψ.hom.naturality g.op)

theorem sec_map_comp' {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (φ ≫ ψ) x = Sec.map ψ (Sec.map φ x) := rfl

theorem sec_map_id' {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := rfl

theorem flatS_of_iso {M N : Shv R} (i : M ≅ N) (h : FlatS M) : FlatS N := by
  obtain ⟨P, φ, hs, hi, hf⟩ := h
  refine ⟨P, φ ≫ i.hom.hom, ?_, ?_, hf⟩
  · intro U y
    obtain ⟨S, hS, hP⟩ := hs U (Sec.map i.inv y)
    refine ⟨S, hS, fun V g hg => ?_⟩
    obtain ⟨x, hx⟩ := hP V g hg
    refine ⟨x, ?_⟩
    change Sec.map i.hom ((φ.app (op V)).hom x) = Sec.res g y
    rw [hx, sec_map_res', ← sec_map_comp', i.inv_hom_id, sec_map_id']
  · intro U x hx
    refine hi U x ?_
    have h1 : Sec.map i.inv (Sec.map i.hom ((φ.app (op U)).hom x)) = Sec.map i.inv (0 : Sec N U) :=
      congrArg (Sec.map i.inv) hx
    rw [← sec_map_comp', i.hom_inv_id, sec_map_id'] at h1
    exact h1.trans (map_zero _)

theorem flatS_of_isZero {M : Shv R} (h : IsZero M) : FlatS M := by
  have hsub : ∀ U : Scheme.{0}, Subsingleton (Sec M U) := fun U => by
    have h1 : IsZero M.obj := (sheafToPresheaf _ _).map_isZero h
    exact ModuleCat.subsingleton_of_isZero (((evaluation _ _).obj (op U)).map_isZero h1)
  refine ⟨M.obj, 𝟙 _, fun U y => ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => ⟨Sec.res g y, rfl⟩⟩,
    fun U x _ => ⟨⊤, Scheme.etaleTopology.top_mem U, fun V g _ => (hsub V).elim _ _⟩, fun U _ => ?_⟩
  haveI := hsub U
  change Module.Flat _ (Sec M U)
  infer_instance

theorem flatS_sgl {F : Shv R} (h : FlatS F) (t : ℤ) : FlatS ((sgl F).X t) := by
  by_cases ht : t = 0
  · subst ht
    exact flatS_of_iso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).symm h
  · exact flatS_of_isZero (HomologicalComplex.isZero_single_obj_X _ _ _ _ ht)

end

theorem isTwRes_tensor : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {I J T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (I.X 0) U) (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U), IsTwRes q i I e → IsTwRes q j J e' → (∀ t, FlatS (J.X t)) → ∀ τ : Pair I J T, τ.IsTensor → IsTwRes q k T fun U ζ => τ.mul U 0 0 0 (add_zero 0) (e U ζ) (e' U ζ) := by
  intro q _ i j k hk I J T e e' hI hJ hflat τ hτ
  obtain ⟨hIge, εI, hεI, heI⟩ := hI
  obtain ⟨hJge, εJ, hεJ, heJ⟩ := hJ
  obtain ⟨μ, hμ, hμgen⟩ := GlobalTheory.T.tateTwist_mul_isTensorPairing q i j k hk
  obtain ⟨T₁, τ₁, hτ₁⟩ := GlobalTheory.T.exists_isTensor_etaleSheafComplexPairing (ZMod q) (sgl (tw q i)) J
  have hTge : T.IsStrictlyGE 0 := (GlobalTheory.T.isTensor_universal_property (ZMod q) τ hτ).2.1 hIge hJge
  obtain ⟨u₁, hu₁, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod q) μ hμ).1 τ₁ (𝟙 _) εJ
  obtain ⟨u₂, hu₂, -⟩ := (GlobalTheory.T.isTensor_universal_property (ZMod q) τ₁ hτ₁).1 τ εI (𝟙 J)
  obtain ⟨ν, hμν, -, hνt⟩ := GlobalTheory.T.exists_isFlip_sheafComplexPairing (ZMod q) μ
  obtain ⟨ν₁, hν₁, -, hν₁t⟩ := GlobalTheory.T.exists_isFlip_sheafComplexPairing (ZMod q) τ₁
  have hflati : ∀ t, FlatS ((sgl (tw q i)).X t) := flatS_sgl (flatS_tw q i)
  have hid : ∀ {K : Cx (ZMod q)} (t : ℤ) {U : Scheme.{0}} (x : Sec (K.X t) U), Sec.map (HomologicalComplex.Hom.f (𝟙 K) t) x = x :=
    fun _ _ _ => rfl
  haveI := hIge
  haveI := hJge
  haveI := hεI
  haveI := hεJ
  have hc : ν.Compat ν₁ εJ (𝟙 _) u₁ := by
    intro U s t w h a b
    rw [hμν U t s w (by omega) b a, hid, hν₁ U t s w (by omega) b (Sec.map (εJ.f s) a), Units.smul_def,
      Units.smul_def]
    have h1 := hu₁ U t s w (by omega) b a
    rw [hid] at h1
    rw [← h1]
    exact map_zsmul ((u₁.f w).hom.app (op U)).hom _ _
  have hq1 : QuasiIso u₁ := GlobalTheory.T.tensor_flat_complex_preserves_quasiIso (ZMod q) ν ν₁ (hνt hμ) (hν₁t hτ₁) hflati εJ u₁ hc
  have hq2 : QuasiIso u₂ := GlobalTheory.T.tensor_flat_complex_preserves_quasiIso (ZMod q) τ₁ τ hτ₁ hτ hflat εI u₂ hu₂
  refine ⟨hTge, u₁ ≫ u₂, quasiIso_comp (hφ := hq1) (hφ' := hq2) _ _, fun U ζ => ?_⟩
  rw [← hμgen U ζ]
  change Sec.map (u₂.f 0) (Sec.map (u₁.f 0) _) = _
  rw [hu₁ U 0 0 0 (add_zero 0), hu₂ U 0 0 0 (add_zero 0), hid, hid, heI, heJ]

end GlobalTheory.EtC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTateTwistResolutionTensorFlatStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTateTwistResolution_tensor_flat : ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {I J T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (I.X 0) U) (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U), IsTwRes q i I e → IsTwRes q j J e' → (∀ t, FlatS (J.X t)) → ∀ τ : Pair I J T, τ.IsTensor → IsTwRes q k T fun U ζ => τ.mul U 0 0 0 (add_zero 0) (e U ζ) (e' U ζ) := by
  first
  | exact @GlobalTheory.EtC.isTwRes_tensor
  | exact GlobalTheory.EtC.isTwRes_tensor
  | (intros; apply GlobalTheory.EtC.isTwRes_tensor <;> assumption)
end
