module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.RedMk

@[expose] public section

local instance (priority := high) : IsEmpty Empty := ⟨Empty.elim⟩

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatThickeningQuotient
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatThickeningQuotient
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsQ

namespace GlobalTheory.CompanionTheory.FlatThick


open TensorProduct in
set_option backward.isDefEq.respectTransparency true in
theorem flat_quotientMap {P B : Type} [CommRing P] [CommRing B] [Algebra P B] [Module.Flat P B] (I₀ : Ideal P) :
    (Ideal.quotientMap (I₀.map (algebraMap P B)) (algebraMap P B) Ideal.le_comap_map :
      P ⧸ I₀ →+* B ⧸ I₀.map (algebraMap P B)).Flat := by
  have f3 : (algebraMap (P ⧸ I₀) ((P ⧸ I₀) ⊗[P] B)).Flat := RingHom.flat_algebraMap_iff.2 inferInstance
  let e₂ : (B ⧸ I₀.map (algebraMap P B)) ≃+* (P ⧸ I₀) ⊗[P] B :=
      (((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I₀).toRingEquiv).trans
        (Algebra.TensorProduct.comm P B (P ⧸ I₀)).toRingEquiv)
  have f5 : (e₂.symm.toRingHom).Flat := RingHom.Flat.of_bijective e₂.symm.bijective
  have f4 := RingHom.Flat.comp f3 f5
  convert f4 using 1
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
  refine e₂.injective ?_
  have : e₂ (Ideal.Quotient.mk _ (algebraMap P B r)) = algebraMap (P ⧸ I₀) ((P ⧸ I₀) ⊗[P] B) (Ideal.Quotient.mk _ r) := by
    change Algebra.TensorProduct.comm P B (P ⧸ I₀) (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I₀ (Ideal.Quotient.mk _ (algebraMap P B r))) = _
    rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
    simp [Algebra.TensorProduct.algebraMap_apply]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    rfl
  simpa using this

theorem flat_of_surjective_ker {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (f : A →+* B) (hf : f.Flat)
    (π : A →+* A') (hπ : Function.Surjective π) (a : A) (hker : RingHom.ker π = Ideal.span {a})
    (g : A' →+* B ⧸ Ideal.span {f a}) (hg : ∀ r, g (π r) = Ideal.Quotient.mk _ (f r)) : g.Flat := by
  letI : Algebra A B := f.toAlgebra
  haveI : Module.Flat A B := hf
  have hJ : (Ideal.span {a}).map (algebraMap A B) = Ideal.span {f a} := by
    rw [Ideal.map_span, Set.image_singleton]; rfl
  let e₁ : (A ⧸ Ideal.span {a}) ≃+* A' :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hπ)
  let e₂ : (B ⧸ (Ideal.span {a}).map (algebraMap A B)) ≃+* (B ⧸ Ideal.span {f a}) := Ideal.quotEquivOfEq hJ
  have h0 := flat_quotientMap (P := A) (B := B) (Ideal.span {a})
  have h1 : (e₁.symm.toRingHom).Flat := RingHom.Flat.of_bijective e₁.symm.bijective
  have h2 : (e₂.toRingHom).Flat := RingHom.Flat.of_bijective e₂.bijective
  have h3 := RingHom.Flat.comp (RingHom.Flat.comp h1 h0) h2
  convert h3 using 1
  refine RingHom.ext fun x => ?_
  obtain ⟨r, rfl⟩ := hπ x
  have hr : e₁.symm (π r) = Ideal.Quotient.mk _ r := by
    rw [RingEquiv.symm_apply_eq]; rfl
  change g (π r) = e₂ (Ideal.quotientMap _ (algebraMap A B) Ideal.le_comap_map (e₁.symm (π r)))
  rw [hr, hg]
  rfl

theorem flatT_qT (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] (O : Type) [CommRing O]
    (F : B.Fn O) (ρ : O →+* k) (n : ℕ) (hn : n ≠ 0) (T : Thick (Wc.L l F ρ (n + 1))) (hT : FlatT T) :
    FlatT (qT hn T) := by
  refine flat_of_surjective_ker T.i hT (Wc.red l k n) ?_ (Ideal.Quotient.mk _ ((l : WittVector l k) ^ n)) ?_ (qi T)
    (qi_red T)
  · intro x
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨Ideal.Quotient.mk _ w, red_mk' w⟩
  · ext x
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [RingHom.mem_ker, red_mk', Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
      Ideal.mem_span_singleton]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨Ideal.Quotient.mk _ c, (map_mul _ _ _)⟩
    · rintro ⟨c, hc⟩
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective c
      rw [← map_mul, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hc
      obtain ⟨d, hd⟩ := hc
      refine ⟨c + (l : WittVector l k) * d, ?_⟩
      rw [mul_add, ← mul_assoc, ← pow_succ, ← hd]
      ring

end GlobalTheory.CompanionTheory.FlatThick

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatThickeningQuotientStatement
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.LsQ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_thickening_quotient : ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [CharP k l] [PerfectRing k l] (O : Type) [CommRing O] (F : B.Fn O) (ρ : O →+* k) (n : ℕ) (hn : n ≠ 0) (T : Thick (Wc.L l F ρ (n + 1))), FlatT T → FlatT (qT hn T) := by
  first | exact @GlobalTheory.CompanionTheory.FlatThick.flatT_qT | exact GlobalTheory.CompanionTheory.FlatThick.flatT_qT | (intros; apply GlobalTheory.CompanionTheory.FlatThick.flatT_qT <;> assumption)
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.LsQ

open CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb.LsG

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
  {F : B.Fn O} {ρ : O →+* k} {n : ℕ} (hn : n ≠ 0)

def qG : (fl l F ρ (n + 1)).FullSubcategory ⥤ (fl l F ρ n).FullSubcategory :=
  (fl l F ρ n).lift ((fl l F ρ (n + 1)).ι ⋙ qF hn) fun T => GlobalTheory.T.flat_thickening_quotient l k O F ρ n hn T.obj T.property

def mq : QMor (sW l F ρ n) (sW l F ρ (n + 1)) (IdF.span _ ((l : WittVector l k) ^ n)) where
  G := qG hn
  ρ T := { toFun := fun x => (show T.obj.B ⧸ lI n T.obj from x)
           map_one' := rfl
           map_mul' := fun _ _ => rfl
           map_zero' := rfl
           map_add' := fun _ _ => rfl
           commutes' := fun _ => rfl }
  inj _ _ _ h := h
  nat {T T'} φ x y h := by
    have h' : x = Ideal.Quotient.mk (lI n T.obj) y := h
    subst h'
    rfl
  dp T e x y hx hy h := by
    have h' : x = Ideal.Quotient.mk (lI n T.obj) y := h
    subst h'
    exact DividedPowers.Quotient.dpow_apply T.obj.δ (subPd hn T.obj) hy

def qα (T : Thick (Wc.L l F ρ (n + 1))) : T ⟶ (Wc.redM l F ρ n).functor.obj (qT hn T) where
  φ := Ideal.Quotient.mk (lI n T)
  u j := j.elim
  comm r := (qi_red T r).symm
  dp := DividedPowers.Quotient.isDPMorphism T.δ (subPd hn T)
  hle := Ideal.le_comap_map
  pt := by
    refine Subtype.ext (Prod.ext ?_ rfl)
    refine Ideal.Quotient.ringHom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun w => ?_))
    have h := T.w (Ideal.Quotient.mk _ w)
    change Ideal.quotientMap (T.J.map (Ideal.Quotient.mk (lI n T))) (Ideal.Quotient.mk (lI n T)) Ideal.le_comap_map
        ((Wc.L l F ρ (n + 1)).str T.y _) =
      qy T (Ideal.quotientMap (Wc.Im l k n) (Wc.red l k n) (Ideal.map_le_iff_le_comap.1 (Wc.dp_red l k n).1)
        (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ w)))
    rw [h, Ideal.quotientMap_mk, Ideal.quotientMap_mk, red_mk']
    rfl
  hx j := j.elim
  hs := by
    have h := T.hs
    change ∏ j : Empty, T.x j = (T.s : T.B) * T.i 1 at h
    rw [Finset.univ_eq_empty, Finset.prod_empty, map_one, mul_one] at h
    have : IsEmpty (Wc.L l F ρ (n + 1)).ι := inferInstanceAs (IsEmpty Empty)
    have : IsEmpty (Wc.L l F ρ n).ι := inferInstanceAs (IsEmpty Empty)
    ext
    simp [Wc.redM, B.crMor, Mor.functor, Mor.obj, qT, ← h]
  hv j := j.elim

theorem qα_nat {T T' : Thick (Wc.L l F ρ (n + 1))} (f : T ⟶ T') :
    qα hn T ≫ (Wc.redM l F ρ n).functor.map ((qF hn).map f) = f ≫ qα hn T' :=
  Thick.Hom.ext (RingHom.ext fun _ => rfl) (funext fun j => j.elim)

end CrystallineSemistableComparison.Pb.LsQ

end
