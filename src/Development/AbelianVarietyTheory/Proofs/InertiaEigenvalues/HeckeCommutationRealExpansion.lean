module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLanglandsClassificationAddOfIrreducibleProduct

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOperatorsRationalFormsCommute
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOperatorsRationalFormsCommute
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HkKs

theorem comm_of_conj {K F V : Type} [Field K] [AddCommGroup F] [Module K F] [AddCommGroup V] [Module K V]
    (e : F ≃ₗ[K] V) (A B : Module.End K F) (A' B' : Module.End K V) (a c : K) (ha : a ≠ 0) (hc : c ≠ 0)
    (hA : ∀ x, e (A x) = a • A' (e x)) (hB : ∀ x, e (B x) = c • B' (e x)) (h : A * B = B * A) :
    A' * B' = B' * A' := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  have h1 : e (A (B x)) = (a * c) • A' (B' (e x)) := by
    rw [hA, hB, map_smul, smul_smul]
  have h2 : e (B (A x)) = (a * c) • B' (A' (e x)) := by
    rw [hB, hA, map_smul, smul_smul, mul_comm c a]
  have h3 : e (A (B x)) = e (B (A x)) := by
    rw [← Module.End.mul_apply, h, Module.End.mul_apply]
  rw [h1, h2] at h3
  have h4 := congrArg (fun z => (a * c)⁻¹ • z) h3
  simp only [inv_smul_smul₀ (mul_ne_zero ha hc)] at h4
  simpa using h4

theorem baseChange_inj {Ks K M : Type} [Field Ks] [Field K] [Algebra Ks K] [AddCommGroup M] [Module Ks M]
    {f g : Module.End Ks M}
    (h : Module.End.baseChangeHom Ks K M f = Module.End.baseChangeHom Ks K M g) : f = g := by
  have hinj : Function.Injective fun y : M => ((1 : K) ⊗ₜ[Ks] y : K ⊗[Ks] M) := by
    have h0 := Module.Flat.rTensor_preserves_injective_linearMap (M := M) (Algebra.linearMap Ks K)
      (algebraMap Ks K).injective
    intro y y' hy
    apply (TensorProduct.lid Ks M).symm.injective
    apply h0
    simpa using hy
  ext x
  apply hinj
  exact LinearMap.congr_fun h ((1 : K) ⊗ₜ[Ks] x)

end GlobalTheory.HkKs

namespace GlobalTheory.HkKs


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem opK_comm : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks)
    (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS Rl cG S) (H : NExpRealH Rl cG S Y), CommG D → HkComm D →
    ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (b : Bool) k P k' P', HkIdx i k P → HkIdx i k' P' →
      GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) *
                   GlobalTheory.GoodSS.opK S j (H.hL j k' P') (fun x hx => H.hs j h1 h2 k' P' x hx) =
        GlobalTheory.GoodSS.opK S j (H.hL j k' P') (fun x hx => H.hs j h1 h2 k' P' x hx) *
          GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) ∧
      ∀ g : S.G, GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) * rhoKG S j (Y.rho j h1 h2) g =
        rhoKG S j (Y.rho j h1 h2) g * GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG S Y H hCG hHk i hi j h1 h2 b k P k' P' hP hP'
  have hj : j ∈ Finset.Icc 1 D.R.m := Finset.mem_Icc.2 ⟨h1, h2⟩
  have hc : ∀ k P, H.cHk i b k P ≠ 0 := fun k P => by
    rw [H.cHk_pow]; exact pow_ne_zero _ (H.cHk_unit i b P).ne_zero
  have hkE : ∀ k P, HkIdx i k P → ∀ x, Y.eF i j b h1 h2 (D.nexp.hkF i j b k P x) =
      H.cHk i b k P • hkFR S i j b (H.hL j) (H.hs j h1 h2) k P (Y.eF i j b h1 h2 x) := by
    intro k P hP x
    exact H.hkEq i j b h1 h2 k P x hP.2.2.2 hP.2.2.1 hP.2.1
  constructor
  · have hcm := comm_of_conj (Y.eF i j b h1 h2) (D.nexp.hkF i j b k P) (D.nexp.hkF i j b k' P') _ _ _ _
      (hc k P) (hc k' P') (hkE k P hP) (hkE k' P' hP') (hHk i hi j hj b k P k' P' hP hP').eq
    apply baseChange_inj (K := KB S i b)
    rw [map_mul, map_mul]
    exact hcm
  · intro g
    have hne : (show FractionRing (D.ntw.O i) from (readLL0 S i b (chiL S j (Y.chi j h1 h2) (S.eG.symm (S.eG g))))⁻¹) ≠ 0 := by
      refine inv_ne_zero ((_root_.map_ne_zero _).2 fun h0 => ?_)
      exact Units.ne_zero _ (congrArg Subtype.val h0)
    have hA : ∀ x, Y.eF i j b h1 h2 (D.nexp.actG i j b (S.eG g) x) =
        (show FractionRing (D.ntw.O i) from (readLL0 S i b (chiL S j (Y.chi j h1 h2) (S.eG.symm (S.eG g))))⁻¹) •
          (show Module.End (FractionRing (D.ntw.O i)) (Fm S i j b) from
            Module.End.baseChangeHom S.Ks (KB S i b) (FmK S j) (rhoKG S j (Y.rho j h1 h2) (S.eG.symm (S.eG g))))
            (Y.eF i j b h1 h2 x) := by
      intro x
      rw [Y.act]
      rfl
    have hCG' : (D.nexp.actG i j b (S.eG g)).toLinearMap * D.nexp.hkF i j b k P =
        D.nexp.hkF i j b k P * (D.nexp.actG i j b (S.eG g)).toLinearMap := hCG i hi b j hj (S.eG g) k P hP
    have hcm := comm_of_conj (Y.eF i j b h1 h2) _ _ _ _ _ _ hne (hc k P) hA (hkE k P hP) hCG'
    rw [MulEquiv.symm_apply_apply] at hcm
    symm
    apply baseChange_inj (K := KB S i b)
    rw [map_mul, map_mul]
    exact hcm

end GlobalTheory.HkKs
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeOperatorsRationalFormsCommuteStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeOperatorsRationalForms_commute : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks)
    (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS Rl cG S) (H : NExpRealH Rl cG S Y), CommG D → HkComm D →
    ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (b : Bool) k P k' P', HkIdx i k P → HkIdx i k' P' →
      GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) *
                   GlobalTheory.GoodSS.opK S j (H.hL j k' P') (fun x hx => H.hs j h1 h2 k' P' x hx) =
        GlobalTheory.GoodSS.opK S j (H.hL j k' P') (fun x hx => H.hs j h1 h2 k' P' x hx) *
          GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) ∧
      ∀ g : S.G, GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) * rhoKG S j (Y.rho j h1 h2) g =
        rhoKG S j (Y.rho j h1 h2) g * GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx) := by
  first | exact @GlobalTheory.HkKs.opK_comm | exact GlobalTheory.HkKs.opK_comm | (intros; apply GlobalTheory.HkKs.opK_comm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorFormsIdempotent
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorFormsIdempotent
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms NumberField Polynomial Formalism.IndefR.NX
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GoodSS.Idem

def rhoTw {D : D7} (S : RatDat D.ntw) (j : ℕ) : G0g D.nd →* Module.End D.what₂.LL (S.WL j) where
  toFun g := ((((S.A j).chi (S.eG.symm g))⁻¹ : D.what₂.LLˣ) : D.what₂.LL) • (S.A j).ρ (S.eG.symm g)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, mul_inv, Units.val_mul]
    rw [smul_mul_smul_comm]

theorem goodProjW_idem : ∀ (D : D7) (S : RatDat D.ntw) (j : ℕ), D.ntw.Tw →
    goodProjW S j D.nexp.eLL0 * goodProjW S j D.nexp.eLL0 = goodProjW S j D.nexp.eLL0 := by
  intro D S j i
  set s := (D.nexp.eAlg i true).coeff.support with hs
  have hsupp : ∀ g, g ∉ s → D.nexp.eLL0 g = 0 := fun g hg => by
    have h0 : (D.nexp.eAlg i true).coeff g = 0 := Finsupp.notMem_support_iff.1 hg
    have hcoef : (D.nexp.eAlg i true).coeff g = readLL0 S i true (D.nexp.eLL0 g) := by
      rw [D.nexp.eAlg_def]; rfl
    rw [hcoef] at h0
    exact (map_eq_zero_iff _ (readLL0 S i true).injective).1 h0
  let rd : ↥D.LL0 →+* FractionRing (D.ntw.O i) := readLL0 S i true
  have hrd : Function.Injective rd := (readLL0 S i true).injective
  let eL : MonoidAlgebra ↥D.LL0 (G0g D.nd) :=
    MonoidAlgebra.ofCoeff (Finsupp.onFinset s D.nexp.eLL0 fun g hg => by
      by_contra h
      exact hg (hsupp g h))
  have heL : ∀ g, eL.coeff g = D.nexp.eLL0 g := fun g => by
    simp only [eL, MonoidAlgebra.coeff_ofCoeff, Finsupp.onFinset_apply]
  have hmap : MonoidAlgebra.mapRingHom (G0g D.nd) rd eL = D.nexp.eAlg i true := by
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro g
    rw [MonoidAlgebra.coeff_mapRingHom, heL, D.nexp.eAlg_def]
    rfl
  have hinj : Function.Injective (MonoidAlgebra.mapRingHom (G0g D.nd) rd) := by
    intro x y hxy
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro g
    apply hrd
    rw [← MonoidAlgebra.coeff_mapRingHom, ← MonoidAlgebra.coeff_mapRingHom, hxy]
  have hidem : eL * eL = eL := hinj (by rw [map_mul, hmap, D.nexp.eAlg_idem])
  let eLL := MonoidAlgebra.mapRingHom (G0g D.nd) (algebraMap ↥D.LL0 D.what₂.LL) eL
  have hP : goodProjW S j D.nexp.eLL0 =
      MonoidAlgebra.lift D.what₂.LL (Module.End D.what₂.LL (S.WL j)) (G0g D.nd) (rhoTw S j) eLL := by
    rw [MonoidAlgebra.lift_apply]
    unfold goodProjW
    rw [finsum_eq_sum_of_support_subset _ (s := s) fun g hg => by
      by_contra hgs
      exact hg (by simp only [hsupp g hgs, IntermediateField.coe_zero, zero_mul, zero_smul])]
    rw [Finsupp.sum_of_support_subset _ (s := s) (fun g hg => by
      by_contra hgs
      apply Finsupp.mem_support_iff.1 hg
      simp only [eLL, MonoidAlgebra.coeff_mapRingHom, heL, hsupp g hgs, map_zero]) (fun a b => b • rhoTw S j a) (fun _ _ => zero_smul _ _)]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [eLL, MonoidAlgebra.coeff_mapRingHom, heL, rhoTw, MonoidHom.coe_mk, OneHom.coe_mk, mul_smul,
      Units.val_inv_eq_inv_val]
    rfl
  rw [hP, ← map_mul, ← map_mul, hidem]

end GlobalTheory.GoodSS.Idem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodProjectorFormsIdempotentStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms NumberField Polynomial Formalism.IndefR.NX
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_projector_forms_idempotent : ∀ (D : D7) (S : RatDat D.ntw) (j : ℕ), D.ntw.Tw →
    goodProjW S j D.nexp.eLL0 * goodProjW S j D.nexp.eLL0 = goodProjW S j D.nexp.eLL0 := by
  first | exact @GlobalTheory.GoodSS.Idem.goodProjW_idem | exact GlobalTheory.GoodSS.Idem.goodProjW_idem | (intros; apply GlobalTheory.GoodSS.Idem.goodProjW_idem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MinpolySeparableOfComplexNormalReading
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MinpolySeparableOfComplexNormalReading
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct

namespace GlobalTheory.NormalSeparable

section SlopeTestRemainingChoices
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem aeval_mem (U : Submodule ℂ H) (S : Module.End ℂ H) (hS : ∀ u ∈ U, S u ∈ U)
    (q : Polynomial ℂ) : ∀ u ∈ U, Polynomial.aeval S q u ∈ U := by
  refine Polynomial.induction_on q ?_ ?_ ?_
  · intro a u hu
    simpa [Module.algebraMap_end_apply] using U.smul_mem a hu
  · intro p r hp hr u hu
    simpa using U.add_mem (hp u hu) (hr u hu)
  · intro n a ih u hu
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    exact ih _ (hS u hu)

theorem aeval_adj (U : Submodule ℂ H) (S S' : Module.End ℂ H) (hS : ∀ u ∈ U, S u ∈ U)
    (hadj : ∀ u ∈ U, ∀ v ∈ U, inner ℂ (S u) v = inner ℂ u (S' v)) (hS' : ∀ u ∈ U, S' u ∈ U)
    (q : Polynomial ℂ) : ∀ u ∈ U, ∀ v ∈ U, inner ℂ (Polynomial.aeval S q u) v
      = inner ℂ u (Polynomial.aeval S' (q.map (starRingEnd ℂ)) v) := by
  refine Polynomial.induction_on q ?_ ?_ ?_
  · intro a u hu v hv
    simp [Module.algebraMap_end_apply, inner_smul_left, inner_smul_right, mul_comm]
  · intro p r hp hr u hu v hv
    simp only [map_add (f := _), Polynomial.map_add (f := _), LinearMap.add_apply, inner_add_left, inner_add_right,
      hp u hu v hv, hr u hu v hv]
  · intro n a ih u hu v hv
    have e : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial ℂ)
        = Polynomial.C a * Polynomial.X ^ n * Polynomial.X := by ring
    rw [e]
    generalize Polynomial.C a * Polynomial.X ^ n = p at ih ⊢
    have e2 : (p * Polynomial.X).map (starRingEnd ℂ) = Polynomial.X * p.map (starRingEnd ℂ) := by
      rw [Polynomial.map_mul, Polynomial.map_X, mul_comm]
    rw [e2, map_mul, Polynomial.aeval_X, Module.End.mul_apply, map_mul, Polynomial.aeval_X,
      Module.End.mul_apply, ih _ (hS u hu) v hv]
    exact hadj u hu _ (GlobalTheory.NormalSeparable.aeval_mem U S' hS' _ v hv)

theorem aeval_comm (U : Submodule ℂ H) (S B : Module.End ℂ H) (hS : ∀ u ∈ U, S u ∈ U)
    (hc : ∀ u ∈ U, S (B u) = B (S u)) (q : Polynomial ℂ) :
    ∀ u ∈ U, Polynomial.aeval S q (B u) = B (Polynomial.aeval S q u) := by
  refine Polynomial.induction_on q ?_ ?_ ?_
  · intro a u hu
    simp [Module.algebraMap_end_apply]
  · intro p r hp hr u hu
    simp only [map_add (f := _), LinearMap.add_apply, hp u hu, hr u hu]
  · intro n a ih u hu
    rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X]
    simp only [Module.End.mul_apply]
    rw [hc u hu, ih _ (hS u hu)]

theorem normal_sq_zero (U : Submodule ℂ H) (A A' : Module.End ℂ H) (hA : ∀ u ∈ U, A u ∈ U)
    (hA' : ∀ u ∈ U, A' u ∈ U)
    (hadj : ∀ u ∈ U, ∀ v ∈ U, inner ℂ (A u) v = inner ℂ u (A' v))
    (hc : ∀ u ∈ U, A (A' u) = A' (A u)) (u : H) (hu : u ∈ U) (h : A (A u) = 0) : A u = 0 := by
  have hw : A u ∈ U := hA u hu
  have h1 : A' (A u) = 0 := by
    have h2 : inner ℂ (A' (A u)) (A' (A u)) = 0 := by
      rw [← hadj _ (hA' _ hw) _ hw, hc _ hw, h, map_zero, inner_zero_left]
    exact inner_self_eq_zero.mp h2
  have h3 : inner ℂ (A u) (A u) = 0 := by
    rw [hadj _ hu _ hw, h1, inner_zero_right]
  exact inner_self_eq_zero.mp h3

end SlopeTestRemainingChoices

theorem minpoly_separable_of_normal : ∀ (K V H : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (φ : K →+* ℂ) (j : V →ₛₗ[φ] H) (T : Module.End K V) (S S' : Module.End ℂ H), (∀ (n : ℕ) (x : Fin n → V), LinearIndependent K x → LinearIndependent ℂ (fun a => j (x a))) → (∀ x, j (T x) = S (j x)) → (∀ u ∈ Submodule.span ℂ (Set.range j), S' u ∈ Submodule.span ℂ (Set.range j)) → (∀ u ∈ Submodule.span ℂ (Set.range j), ∀ v ∈ Submodule.span ℂ (Set.range j), inner ℂ (S u) v = inner ℂ u (S' v)) → (∀ u ∈ Submodule.span ℂ (Set.range j), S (S' u) = S' (S u)) → (minpoly K T).Separable := by
  intro K V H _ _ _ _ _ _ φ j T S S' hlin hT hS' hadj hc
  haveI : CharZero K := φ.charZero
  set U : Submodule ℂ H := Submodule.span ℂ (Set.range j) with hU
  have hjU : ∀ x, j x ∈ U := fun x => Submodule.subset_span ⟨x, rfl⟩
  have hSU : ∀ u ∈ U, S u ∈ U := by
    have hle : U ≤ U.comap S := by
      rw [hU, Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_comap, ← hT x]
      exact Submodule.subset_span ⟨T x, rfl⟩
    intro u hu
    exact hle hu
  have hinj : ∀ v : V, j v = 0 → v = 0 := by
    intro v hv
    by_contra hne
    have hli : LinearIndependent K (fun _ : Fin 1 => v) := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      obtain rfl : i = 0 := Subsingleton.elim _ _
      simp only [Fin.sum_univ_one] at hg
      exact (smul_eq_zero.mp hg).resolve_right hne
    have h1 := hlin 1 (fun _ => v) hli
    exact h1.ne_zero 0 (by simpa using hv)
  have htr : ∀ (p : Polynomial K) (x : V),
      j (Polynomial.aeval T p x) = Polynomial.aeval S (p.map φ) (j x) := by
    intro p
    refine Polynomial.induction_on p ?_ ?_ ?_
    · intro a x
      simp [Module.algebraMap_end_apply]
    · intro p r hp hr x
      simp only [map_add (f := _), Polynomial.map_add (f := _), LinearMap.add_apply, hp, hr]
    · intro n a ih x
      have e : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial K)
          = Polynomial.C a * Polynomial.X ^ n * Polynomial.X := by ring
      rw [e]
      generalize Polynomial.C a * Polynomial.X ^ n = p at ih ⊢
      rw [map_mul, Polynomial.aeval_X, Module.End.mul_apply, ih, Polynomial.map_mul,
        Polynomial.map_X, map_mul, Polynomial.aeval_X, Module.End.mul_apply, hT]
  have hsq : Squarefree (minpoly K T) := by
    intro q hq
    obtain ⟨r, hr⟩ := hq
    have hp0 : minpoly K T ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral T)
    have hann : Polynomial.aeval T (q * r) = 0 := by
      apply LinearMap.ext
      intro x
      rw [LinearMap.zero_apply]
      apply hinj
      have e1 : Polynomial.aeval T (q * r) x = Polynomial.aeval T q (Polynomial.aeval T r x) := by
        rw [map_mul, Module.End.mul_apply]
      rw [e1, htr]
      have h0 : Polynomial.aeval T q (Polynomial.aeval T q (Polynomial.aeval T r x)) = 0 := by
        have h4 : Polynomial.aeval T (q * q * r) x = 0 := by
          rw [← hr, minpoly.aeval, LinearMap.zero_apply]
        simpa only [map_mul, Module.End.mul_apply] using h4
      have h0' : Polynomial.aeval S (q.map φ)
          (Polynomial.aeval S (q.map φ) (j (Polynomial.aeval T r x))) = 0 := by
        rw [← htr, ← htr, h0, map_zero]
      have hcomm1 : ∀ u ∈ U, Polynomial.aeval S (q.map φ) (S' u)
          = S' (Polynomial.aeval S (q.map φ) u) :=
        GlobalTheory.NormalSeparable.aeval_comm U S S' hSU hc (q.map φ)
      have hcomm2 := GlobalTheory.NormalSeparable.aeval_comm U S' (Polynomial.aeval S (q.map φ)) hS'
        (fun u hu => (hcomm1 u hu).symm) ((q.map φ).map (starRingEnd ℂ))
      exact GlobalTheory.NormalSeparable.normal_sq_zero U (Polynomial.aeval S (q.map φ))
        (Polynomial.aeval S' ((q.map φ).map (starRingEnd ℂ)))
        (GlobalTheory.NormalSeparable.aeval_mem U S hSU _) (GlobalTheory.NormalSeparable.aeval_mem U S' hS' _)
        (GlobalTheory.NormalSeparable.aeval_adj U S S' hSU hadj hS' _) (fun u hu => (hcomm2 u hu).symm)
        (j (Polynomial.aeval T r x)) (hjU _) h0'
    have hdvd : minpoly K T ∣ q * r := minpoly.dvd K T hann
    rw [hr] at hdvd
    have hqr : q * r ≠ 0 := by
      intro h
      apply hp0
      rw [hr, mul_assoc, h, mul_zero]
    have h5 : q * (q * r) ∣ 1 * (q * r) := by rwa [one_mul, ← mul_assoc]
    exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hqr).mp h5)
  exact PerfectField.separable_iff_squarefree.mpr hsq

end GlobalTheory.NormalSeparable
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MinpolySeparableOfComplexNormalReadingStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minpoly_separable_of_complex_normal_reading : ∀ (K V H : Type) [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [NormedAddCommGroup H] [InnerProductSpace ℂ H] (φ : K →+* ℂ) (j : V →ₛₗ[φ] H) (T : Module.End K V) (S S' : Module.End ℂ H), (∀ (n : ℕ) (x : Fin n → V), LinearIndependent K x → LinearIndependent ℂ (fun a => j (x a))) → (∀ x, j (T x) = S (j x)) → (∀ u ∈ Submodule.span ℂ (Set.range j), S' u ∈ Submodule.span ℂ (Set.range j)) → (∀ u ∈ Submodule.span ℂ (Set.range j), ∀ v ∈ Submodule.span ℂ (Set.range j), inner ℂ (S u) v = inner ℂ u (S' v)) → (∀ u ∈ Submodule.span ℂ (Set.range j), S (S' u) = S' (S u)) → (minpoly K T).Separable := by
  first | exact @GlobalTheory.NormalSeparable.minpoly_separable_of_normal | exact GlobalTheory.NormalSeparable.minpoly_separable_of_normal | (intros; apply GlobalTheory.NormalSeparable.minpoly_separable_of_normal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalIntertwine
namespace GlobalTheory.AevalIntertwine

theorem aeval_intertwine : ∀ {K M N : Type} [inst : Field K] [inst_1 : AddCommGroup M] [inst_2 : Module K M] [inst_3 : AddCommGroup N] [inst_4 : Module K N] (f : M →ₗ[K] N) (A : Module.End K M) (B : Module.End K N), (∀ (x : M), (f : M → N) ((A : M → M) x) = (B : N → N) ((f : M → N) x)) → ∀ (p : Polynomial K) (x : M), (f : M → N) (((Polynomial.aeval A : Polynomial K → Module.End K M) p : M → M) x) = ((Polynomial.aeval B : Polynomial K → Module.End K N) p : N → N) ((f : M → N) x) := by
  intro K M N _ _ _ _ _ f A B h p
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro a x
    simp [Polynomial.aeval_C, Module.algebraMap_end_apply]
  · intro p q hp hq x
    simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  · intro n a ih x
    have e : ∀ {V : Type} [AddCommGroup V] [Module K V] (E : Module.End K V) (y : V),
        Polynomial.aeval E (Polynomial.C a * Polynomial.X ^ (n + 1)) y
          = Polynomial.aeval E (Polynomial.C a * Polynomial.X ^ n) (E y) := by
      intro V _ _ E y
      rw [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply]
    rw [e, e, ih, h]

end GlobalTheory.AevalIntertwine
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentFormsIntermediateField
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentFormsIntermediateField
open Polynomial
open scoped TensorProduct

namespace GlobalTheory

theorem rows_algebraMap_linearIndependent {L0 L : Type} [Field L0] [Field L] [Algebra L0 L]
    {m n : ℕ} (v : Fin m → Fin n → L0) (hv : LinearIndependent L0 v) :
    LinearIndependent L (fun a b => algebraMap L0 L (v a b)) := by
  have h1 : LinearIndependent L (fun a => (1 : L) ⊗ₜ[L0] v a) :=
    Module.Flat.linearIndependent_one_tmul hv
  have h2 := h1.map' (TensorProduct.piScalarRight L0 L L (Fin n)).toLinearMap (LinearEquiv.ker _)
  have he : (fun a b => algebraMap L0 L (v a b)) =
      (TensorProduct.piScalarRight L0 L L (Fin n)).toLinearMap ∘ fun a => (1 : L) ⊗ₜ[L0] v a := by
    funext a b
    simp [TensorProduct.piScalarRight_apply, Algebra.smul_def]
  rw [he]
  exact h2

theorem ksForm_tensor_linearIndependent : ∀ (Ks L0 L WL : Type) [Field Ks] [Field L0] [Field L] [Algebra Ks L0] [Algebra L0 L] [Algebra Ks L]
    [IsScalarTower Ks L0 L] [AddCommGroup WL] [Module L WL] [Module Ks WL] [IsScalarTower Ks L WL]
    (WK : Submodule Ks WL) (n : ℕ) (bs : Fin n → WL), (∀ a, bs a ∈ WK) → Submodule.span Ks (Set.range bs) = WK →
    LinearIndependent L bs → ∀ (ι : L0 ⊗[Ks] WK →ₗ[Ks] WL), (∀ (c : L0) (f : WK), ι (c ⊗ₜ[Ks] f) = algebraMap L0 L c • (f : WL)) →
    ∀ (m : ℕ) (x : Fin m → L0 ⊗[Ks] WK), LinearIndependent L0 x → LinearIndependent L (fun a => ι (x a)) := by
  intro Ks L0 L WL _ _ _ _ _ _ _ _ _ _ _ WK n bs hmem hspan hL ι hι m x hx
  subst hspan
  have hK : LinearIndependent Ks bs := hL.restrict_scalars' Ks
  let bK := Module.Basis.span hK
  let B0 := Algebra.TensorProduct.basis L0 bK
  let M : Fin m → Fin n → L0 := fun a => B0.equivFun (x a)
  have hMli : LinearIndependent L0 M := hx.map' B0.equivFun.toLinearMap B0.equivFun.ker
  have hML := rows_algebraMap_linearIndependent (L := L) M hMli
  have hιs : ∀ (c : L0) (y : L0 ⊗[Ks] (Submodule.span Ks (Set.range bs))),
      ι (c • y) = algebraMap L0 L c • ι y := by
    intro c y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul d f => rw [TensorProduct.smul_tmul', hι, hι, smul_eq_mul, map_mul, mul_smul]
    | add y z hy hz => rw [smul_add, map_add (f := _), map_add (f := _), hy, hz, smul_add]
  have hx_eq : ∀ a, ι (x a) = ∑ b, algebraMap L0 L (M a b) • bs b := by
    intro a
    conv_lhs => rw [← B0.sum_equivFun (x a)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hιs, Algebra.TensorProduct.basis_apply, hι]
    simp [bK, Module.Basis.span_apply, M]
  rw [Fintype.linearIndependent_iff] at hL hML ⊢
  intro g hg
  apply hML g
  funext b
  simp_rw [hx_eq, Finset.smul_sum, smul_smul] at hg
  rw [Finset.sum_comm] at hg
  simp_rw [← Finset.sum_smul] at hg
  have := hL _ hg b
  simpa [Finset.sum_apply] using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentFormsIntermediateFieldStatement
open Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_forms_intermediate_field : ∀ (Ks L0 L WL : Type) [Field Ks] [Field L0] [Field L] [Algebra Ks L0] [Algebra L0 L] [Algebra Ks L]
    [IsScalarTower Ks L0 L] [AddCommGroup WL] [Module L WL] [Module Ks WL] [IsScalarTower Ks L WL]
    (WK : Submodule Ks WL) (n : ℕ) (bs : Fin n → WL), (∀ a, bs a ∈ WK) → Submodule.span Ks (Set.range bs) = WK →
    LinearIndependent L bs → ∀ (ι : L0 ⊗[Ks] WK →ₗ[Ks] WL), (∀ (c : L0) (f : WK), ι (c ⊗ₜ[Ks] f) = algebraMap L0 L c • (f : WL)) →
    ∀ (m : ℕ) (x : Fin m → L0 ⊗[Ks] WK), LinearIndependent L0 x → LinearIndependent L (fun a => ι (x a)) := by
  first | exact @GlobalTheory.ksForm_tensor_linearIndependent | exact GlobalTheory.ksForm_tensor_linearIndependent | (intros; apply GlobalTheory.ksForm_tensor_linearIndependent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCommutationRealExpansion
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GoodSS.Heart

theorem aeval_map_of_comm {K M N : Type} [Field K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    (f : M →ₗ[K] N) (A : Module.End K M) (B : Module.End K N) (h : ∀ x, f (A x) = B (f x)) (p : K[X]) (x : M) :
    f (Polynomial.aeval A p x) = Polynomial.aeval B p (f x) := by
  first
  | exact @_root_.GlobalTheory.AevalIntertwine.aeval_intertwine
  | exact _root_.GlobalTheory.AevalIntertwine.aeval_intertwine
  | (apply _root_.GlobalTheory.AevalIntertwine.aeval_intertwine <;> assumption)
  | (intros; apply _root_.GlobalTheory.AevalIntertwine.aeval_intertwine <;> assumption)
  | (intros; apply @_root_.GlobalTheory.AevalIntertwine.aeval_intertwine <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.AevalIntertwine.aeval_intertwine ..)

theorem exists_lift_end {H X : Type} [AddCommGroup H] [Module ℂ H] [AddCommGroup X] [Module ℂ X]
    (e : H →ₗ[ℂ] X) (he : Function.Injective e) (A : X →ₗ[ℂ] X) (h : ∀ x, ∃ x', e x' = A (e x)) :
    ∃ S : Module.End ℂ H, ∀ x, e (S x) = A (e x) := by
  have hr : ∀ x, (A ∘ₗ e) x ∈ LinearMap.range e := fun x => by
    obtain ⟨x', hx'⟩ := h x
    exact ⟨x', hx'⟩
  refine ⟨(LinearEquiv.ofInjective e he).symm.toLinearMap ∘ₗ (A ∘ₗ e).codRestrict (LinearMap.range e) hr,
    fun x => ?_⟩
  have h1 := LinearEquiv.ofInjective_apply e (h := he)
    ((LinearEquiv.ofInjective e he).symm ⟨(A ∘ₗ e) x, hr x⟩)
  rw [LinearEquiv.apply_symm_apply] at h1
  exact h1.symm

variable {D : D7} (S : RatDat D.ntw)

theorem inWL_tmul (j : ℕ) (c : ↥D.LL0) (f : FmK S j) :
    inWL S j (c ⊗ₜ[S.Ks] f) = (c : D.what₂.LL) • (show ↥(S.A j).WK from f).1 := rfl

theorem inWL_smul (j : ℕ) (c : ↥D.LL0) (z : ↥D.LL0 ⊗[S.Ks] FmK S j) :
    inWL S j (c • z) = (c : D.what₂.LL) • inWL S j z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a f =>
    rw [TensorProduct.smul_tmul']
    show ((c • a : ↥D.LL0) : D.what₂.LL) • (_ : S.WL j) = (c : D.what₂.LL) • (((a : ↥D.LL0) : D.what₂.LL) • (_ : S.WL j))
    rw [smul_eq_mul, IntermediateField.coe_mul, mul_smul]
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem inWL_opK (j : ℕ) (f : Module.End D.what₂.LL (S.WL j)) (hf : ∀ x ∈ (S.A j).WK, f x ∈ (S.A j).WK)
    (z : ↥D.LL0 ⊗[S.Ks] FmK S j) :
    inWL S j (LinearMap.baseChange ↥D.LL0 (opK S j f hf) z) = f (inWL S j z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, inWL_tmul, inWL_tmul, LinearMap.map_smul]
    rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem goodProjector_eq_sum (j : ℕ) (hst : RhoStab S j) (hχ : ChiInLL0 S j) (eC : G0g D.nd → ↥D.LL0)
    (s : Finset (G0g D.nd)) (hs : ∀ g, g ∉ s → eC g = 0) :
    goodProjectorBaseChangeForms S j hst hχ eC = ∑ g ∈ s, (eC g * (chiL S j hχ (S.eG.symm g))⁻¹) •
      LinearMap.baseChange ↥D.LL0 (rhoKG S j hst (S.eG.symm g)) := by
  unfold goodProjectorBaseChangeForms
  refine finsum_eq_sum_of_support_subset _ fun g hg => ?_
  by_contra hgs
  exact hg (by simp only [hs g hgs, zero_mul, zero_smul])

theorem goodProjW_eq_sum (j : ℕ) (eC : G0g D.nd → ↥D.LL0)
    (s : Finset (G0g D.nd)) (hs : ∀ g, g ∉ s → eC g = 0) :
    goodProjW S j eC = ∑ g ∈ s, (((eC g : ↥D.LL0) : D.what₂.LL) *
      ((((S.A j).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL))⁻¹) • (S.A j).ρ (S.eG.symm g) := by
  unfold goodProjW
  refine finsum_eq_sum_of_support_subset _ fun g hg => ?_
  by_contra hgs
  exact hg (by simp only [hs g hgs, IntermediateField.coe_zero, zero_mul, zero_smul])

theorem inForms_goodProjector (j : ℕ) (hst : RhoStab S j) (hχ : ChiInLL0 S j) (eC : G0g D.nd → ↥D.LL0)
    (s : Finset (G0g D.nd)) (hs : ∀ g, g ∉ s → eC g = 0) (z : ↥D.LL0 ⊗[S.Ks] FmK S j) :
    inWL S j (goodProjectorBaseChangeForms S j hst hχ eC z) = goodProjW S j eC (inWL S j z) := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [goodProjector_eq_sum S j hst hχ eC s hs, goodProjW_eq_sum S j eC s hs, LinearMap.sum_apply, map_sum,
    LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [LinearMap.smul_apply, inWL_smul, LinearMap.smul_apply]
  have h := inWL_opK S j ((S.A j).ρ (S.eG.symm g)) (fun x hx => hst (S.eG.symm g) x hx) z
  change inWL S j (LinearMap.baseChange ↥D.LL0 (opK S j ((S.A j).ρ (S.eG.symm g)) _) z) = _ at h
  erw [h]
  congr 1

theorem goodProjector_comm (j : ℕ) (hst : RhoStab S j) (hχ : ChiInLL0 S j) (eC : G0g D.nd → ↥D.LL0)
    (s : Finset (G0g D.nd)) (hs : ∀ g, g ∉ s → eC g = 0) (A : Module.End S.Ks (FmK S j))
    (hA : ∀ g, A * rhoKG S j hst g = rhoKG S j hst g * A) :
    LinearMap.baseChange ↥D.LL0 A * goodProjectorBaseChangeForms S j hst hχ eC = goodProjectorBaseChangeForms S j hst hχ eC * LinearMap.baseChange ↥D.LL0 A := by
  have hbm : ∀ f g : Module.End S.Ks (FmK S j),
      LinearMap.baseChange ↥D.LL0 (f * g) = LinearMap.baseChange ↥D.LL0 f * LinearMap.baseChange ↥D.LL0 g :=
    fun f g => LinearMap.baseChange_comp g f
  rw [goodProjector_eq_sum S j hst hχ eC s hs, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [mul_smul_comm, smul_mul_assoc, ← hbm, ← hbm, hA]

end GlobalTheory.GoodSS.Heart

namespace GlobalTheory.GoodSS.Heart


set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem hL_separable_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3)
    (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS Rl cG S) (H : NExpRealH Rl cG S Y), CommG D → HkComm D → NExpHeckeRowX Rl cG S Y H (fun j => goodProjW S j D.nexp.eLL0) →
    Rl.Char3 F → Rl.toRealDat.LUnif → Rl.toRealDat.LIntegral →
    (∀ i P P', P ∈ D.ntw.S0 i → IsConjPl D.host P P' → P' ∈ D.ntw.S0 i) →
    (∀ i, placesOver D.host.E 2 ⊆ (D.ntw.S0 i : Set (PlE D.host))) →
    (∀ i, ∀ Q ∈ Rl.Sb, Q ∈ D.ntw.S0 i) →
    ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (b : Bool) k P, HkIdx i k P →
      ∃ q : (↥D.LL0)[X], q.Separable ∧
        ∀ z ∈ LinearMap.range (GlobalTheory.GoodSS.goodProjectorBaseChangeForms S j (Y.rho j h1 h2) (Y.chi j h1 h2) D.nexp.eLL0),
          Polynomial.aeval (LinearMap.baseChange ↥D.LL0
            (GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx))) q z = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ Rl F cG S Y H hG hC hX hR hU hI hS0c hS02 hS0b i hi j h1 h2 b k P hk
  obtain ⟨i0, rfl⟩ : ∃ i0 : Fin D.R.m, j = (i0 : ℕ) + 1 := ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  obtain ⟨hk1, hk2, hPs, hP0⟩ := hk
  obtain ⟨P', hPP', hP's, hP'0, hoffP, hoffP', h2P, h2P'⟩ :=
    GlobalTheory.T.exists_conjugate_splitPlace_off_stableSet D (D.ntw.S0 i) Rl.Sb P (fun P1 P2 h h' => hS0c i P1 P2 h h') (hS02 i) (hS0b i) hPs hP0
  obtain ⟨α, α', R, R', hα, hRd, hα', hRd', hxR, hyR, hadj⟩ :=
    GlobalTheory.T.complexHecke_conjugatePlace_petersson_adjoint Rl F hR i0 k P P' hPs hPP' hoffP hoffP' h2P h2P' hk1 hk2
  have hkP : HkIdx i k P := ⟨hk1, hk2, hPs, hP0⟩
  have hkP' : HkIdx i k P' := ⟨hk1, hk2, hP's, hP'0⟩
  obtain ⟨hPQ, hPg⟩ := GlobalTheory.T.heckeOperatorsRationalForms_commute Rl cG S Y H hG hC i hi ((i0 : ℕ) + 1) h1 h2 b k P k P' hkP hkP'
  obtain ⟨-, hQg⟩ := GlobalTheory.T.heckeOperatorsRationalForms_commute Rl cG S Y H hG hC i hi ((i0 : ℕ) + 1) h1 h2 b k P' k P hkP' hkP

  set s := (D.nexp.eAlg i b).coeff.support with hs
  have hsupp : ∀ g, g ∉ s → D.nexp.eLL0 g = 0 := fun g hg => by
    have h0 : (D.nexp.eAlg i b).coeff g = 0 := Finsupp.notMem_support_iff.1 hg
    have hcoef : (D.nexp.eAlg i b).coeff g = readLL0 S i b (D.nexp.eLL0 g) := by
      rw [D.nexp.eAlg_def]; rfl
    rw [hcoef] at h0
    exact (map_eq_zero_iff _ (readLL0 S i b).injective).1 h0
  set σ0 := Formalism.IndefR.Links.sg0 D A3.A with hσ0
  set hst := Y.rho ((i0 : ℕ) + 1) h1 h2 with hhst
  set hχ := Y.chi ((i0 : ℕ) + 1) h1 h2 with hhχ
  set E := goodProjectorBaseChangeForms S ((i0 : ℕ) + 1) hst hχ D.nexp.eLL0 with hE
  set V := LinearMap.range E with hV
  set Tp := opK S ((i0 : ℕ) + 1) (H.hL ((i0 : ℕ) + 1) k P) (fun x hx => H.hs ((i0 : ℕ) + 1) h1 h2 k P x hx) with hTp
  set Tq := opK S ((i0 : ℕ) + 1) (H.hL ((i0 : ℕ) + 1) k P') (fun x hx => H.hs ((i0 : ℕ) + 1) h1 h2 k P' x hx) with hTq
  set T0 := LinearMap.baseChange ↥D.LL0 Tp with hT0
  set T0' := LinearMap.baseChange ↥D.LL0 Tq with hT0'
  have hTE : T0 * E = E * T0 := goodProjector_comm S _ hst hχ _ s hsupp Tp hPg
  have hTE' : T0' * E = E * T0' := goodProjector_comm S _ hst hχ _ s hsupp Tq hQg
  have hVT : ∀ z ∈ V, T0 z ∈ V := by
    rintro _ ⟨y, rfl⟩
    exact ⟨T0 y, (LinearMap.congr_fun hTE y).symm⟩
  have hVT' : ∀ z ∈ V, T0' z ∈ V := by
    rintro _ ⟨y, rfl⟩
    exact ⟨T0' y, (LinearMap.congr_fun hTE' y).symm⟩
  have hbm : ∀ f g : Module.End S.Ks (FmK S ((i0 : ℕ) + 1)),
      LinearMap.baseChange ↥D.LL0 (f * g) = LinearMap.baseChange ↥D.LL0 f * LinearMap.baseChange ↥D.LL0 g :=
    fun f g => LinearMap.baseChange_comp g f
  have hPQc : T0 * T0' = T0' * T0 := by rw [hT0, hT0', ← hbm, hPQ, hbm]

  have hfix : ∀ z ∈ V, goodProjW S ((i0 : ℕ) + 1) D.nexp.eLL0 (inWL S ((i0 : ℕ) + 1) z) = inWL S ((i0 : ℕ) + 1) z := by
    rintro _ ⟨y, rfl⟩
    rw [inForms_goodProjector S _ hst hχ _ s hsupp y, ← Module.End.mul_apply, GlobalTheory.T.good_projector_forms_idempotent D S ((i0 : ℕ) + 1) i]
  have hT0w : ∀ z, inWL S ((i0 : ℕ) + 1) (T0 z) = H.hL ((i0 : ℕ) + 1) k P (inWL S ((i0 : ℕ) + 1) z) := fun z =>
    inWL_opK S _ _ _ z
  have hT0w' : ∀ z, inWL S ((i0 : ℕ) + 1) (T0' z) = H.hL ((i0 : ℕ) + 1) k P' (inWL S ((i0 : ℕ) + 1) z) := fun z =>
    inWL_opK S _ _ _ z

  set φ : ↥D.LL0 →+* ℂ := σ0.comp (algebraMap ↥D.LL0 D.what₂.LL) with hφ
  let jm : ↥V →ₛₗ[φ] (Rl.HW i0 σ0).H :=
    { toFun := fun z => (Rl.FW i0).j σ0 ((Y.fi i0).e (inWL S ((i0 : ℕ) + 1) z.1))
      map_add' := fun z w => by
        show (Rl.FW i0).j σ0 ((Y.fi i0).e (inWL S ((i0 : ℕ) + 1) (z.1 + w.1))) = _
        rw [map_add (f := _), map_add (f := _), map_add (f := _)]
      map_smul' := fun c z => by
        show (Rl.FW i0).j σ0 ((Y.fi i0).e (inWL S ((i0 : ℕ) + 1) (c • z.1))) = _
        rw [inWL_smul, LinearEquiv.map_smul, LinearMap.map_smulₛₗ]
        rfl }
  have hjm : ∀ z : ↥V, jm z = (Rl.FW i0).j σ0 ((Y.fi i0).e (inWL S ((i0 : ℕ) + 1) z.1)) := fun _ => rfl

  have he : Function.Injective (Rl.HW i0 σ0).e := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨y', hy'⟩ := hyR x
    have h0 := hadj 0 x x y' (by rw [hx, map_zero, map_zero]) hy'
    rw [inner_zero_left] at h0
    exact inner_self_eq_zero.1 h0
  obtain ⟨S0, hS0⟩ := exists_lift_end _ he _ hxR
  obtain ⟨S1, hS1⟩ := exists_lift_end _ he _ hyR

  set c : ℂ := (((Rl.C.mu0 i0).val P : ℂˣ) : ℂ)⁻¹ ^ k *
    (((Nat.card (Formalism.L2.DIV.kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹ with hc
  set c' : ℂ := (((Rl.C.mu0 i0).val P' : ℂˣ) : ℂ)⁻¹ ^ k *
    (((Nat.card (Formalism.L2.DIV.kP P') : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹ with hc'
  have hc'0 : c' ≠ 0 := by
    have hq : ((Nat.card (Formalism.L2.DIV.kP P') : ℕ) : ℂ) ≠ 0 := by
      haveI := Ideal.finiteQuotientOfFreeOfNeBot P'.asIdeal P'.ne_bot
      exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero (Units.ne_zero _))) (inv_ne_zero (pow_ne_zero _ hq))
  set T : Module.End ↥D.LL0 ↥V := T0.restrict hVT with hT
  set T' : Module.End ↥D.LL0 ↥V := T0'.restrict hVT' with hT'
  have htie : ∀ z : ↥V, (Rl.HW i0 σ0).e (jm (T z)) = c • Formalism.IndefR.Mult.heckeOn (Rl.MW i0 σ0) R ((Rl.HW i0 σ0).e (jm z)) := by
    intro z
    have h := hX.tie i0 k P hPs hoffP ⟨i, hP0⟩ h2P hk2 α R hα hRd (inWL S ((i0 : ℕ) + 1) z.1) (hfix z.1 z.2)
    rw [hjm, hjm]
    show (Rl.HW i0 σ0).e ((Rl.FW i0).j σ0 ((Y.fi i0).e (inWL S ((i0 : ℕ) + 1) (T0 z.1)))) = _
    rw [hT0w]
    exact h
  have htie' : ∀ z : ↥V, (Rl.HW i0 σ0).e (jm (T' z)) = c' • Formalism.IndefR.Mult.heckeOn (Rl.MW i0 σ0) R' ((Rl.HW i0 σ0).e (jm z)) := by
    intro z
    have h := hX.tie i0 k P' hP's hoffP' ⟨i, hP'0⟩ h2P' hk2 α' R' hα' hRd' (inWL S ((i0 : ℕ) + 1) z.1) (hfix z.1 z.2)
    rw [hjm, hjm]
    show (Rl.HW i0 σ0).e ((Rl.FW i0).j σ0 ((Y.fi i0).e (inWL S ((i0 : ℕ) + 1) (T0' z.1)))) = _
    rw [hT0w']
    exact h
  set SS : Module.End ℂ (Rl.HW i0 σ0).H := c • S0 with hSS
  set SS' : Module.End ℂ (Rl.HW i0 σ0).H := (starRingEnd ℂ c) • S1 with hSS'
  have hSj : ∀ z : ↥V, SS (jm z) = jm (T z) := by
    intro z
    apply he
    rw [htie z, hSS, LinearMap.smul_apply, map_smul, hS0]
  have hS'j : ∀ z : ↥V, SS' (jm z) = (starRingEnd ℂ c * c'⁻¹) • jm (T' z) := by
    intro z
    have h2 : jm (T' z) = c' • S1 (jm z) := he (by rw [htie' z, map_smul, hS1])
    rw [hSS', LinearMap.smul_apply, h2, smul_smul, mul_assoc, inv_mul_cancel₀ hc'0, mul_one]
  have hTT : ∀ z : ↥V, T (T' z) = T' (T z) := fun z => Subtype.ext (LinearMap.congr_fun hPQc z.1)

  obtain ⟨nb, bs, hbs, -, hspan, hbLL, -⟩ := GlobalTheory.T.isKsForm_of_algebraicFormsIso _ _ (Y.fi i0) (hI i0).1
  haveI : IsScalarTower S.Ks ↥D.LL0 D.what₂.LL := IsScalarTower.of_algebraMap_eq fun x => (S.kKs_spec x).symm
  haveI : Module.Finite S.Ks (FmK S ((i0 : ℕ) + 1)) := by
    have h := FiniteDimensional.span_of_finite S.Ks (Set.finite_range bs)
    rw [hspan] at h
    exact h
  haveI : FiniteDimensional ↥D.LL0 ↥V := inferInstance
  have hind : ∀ (n : ℕ) (x : Fin n → ↥V), LinearIndependent ↥D.LL0 x → LinearIndependent ℂ (fun a => jm (x a)) := by
    intro n x hx
    have hx1 : LinearIndependent ↥D.LL0 (fun a => (x a : ↥D.LL0 ⊗[S.Ks] FmK S ((i0 : ℕ) + 1))) :=
      hx.map' V.subtype (Submodule.ker_subtype V)
    have hx2 : LinearIndependent D.what₂.LL (fun a => inWL S ((i0 : ℕ) + 1) (x a).1) :=
      GlobalTheory.T.linearIndependent_forms_intermediate_field S.Ks ↥D.LL0 D.what₂.LL (S.WL ((i0 : ℕ) + 1)) (S.A ((i0 : ℕ) + 1)).WK nb bs hbs hspan hbLL
        (inWL S ((i0 : ℕ) + 1)) (fun _ _ => rfl) n (fun a => (x a).1) hx1
    have hx3 : LinearIndependent D.what₂.LL (fun a => (Y.fi i0).e (inWL S ((i0 : ℕ) + 1) (x a).1)) :=
      hx2.map' (Y.fi i0).e.toLinearMap (LinearEquiv.ker _)
    exact (hU i0 σ0).1 n _ hx3
  have hkeep : ∀ u ∈ Submodule.span ℂ (Set.range jm), SS' u ∈ Submodule.span ℂ (Set.range jm) := by
    intro u hu
    have hle : Submodule.span ℂ (Set.range jm) ≤ (Submodule.span ℂ (Set.range jm)).comap SS' := by
      rw [Submodule.span_le]
      rintro _ ⟨z, rfl⟩
      show SS' (jm z) ∈ Submodule.span ℂ (Set.range jm)
      rw [hS'j]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨T' z, rfl⟩)
    exact hle hu
  have hcomm : ∀ u ∈ Submodule.span ℂ (Set.range jm), SS (SS' u) = SS' (SS u) := by
    intro u hu
    have hle : Submodule.span ℂ (Set.range jm) ≤ LinearMap.eqLocus (SS * SS') (SS' * SS) := by
      rw [Submodule.span_le]
      rintro _ ⟨z, rfl⟩
      show SS (SS' (jm z)) = SS' (SS (jm z))
      rw [hS'j, map_smul, hSj, hSj, hS'j, hTT]
    exact hle hu
  have hadj' : ∀ u ∈ Submodule.span ℂ (Set.range jm), ∀ v ∈ Submodule.span ℂ (Set.range jm),
      inner ℂ (SS u) v = inner ℂ u (SS' v) := by
    intro u _ v _
    rw [hSS, hSS', LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left, inner_smul_right,
      hadj u v (S0 u) (S1 v) (hS0 u) (hS1 v)]
  have hsep := GlobalTheory.T.minpoly_separable_of_complex_normal_reading ↥D.LL0 ↥V (Rl.HW i0 σ0).H φ jm T SS SS' hind (fun z => (hSj z).symm) hkeep hadj' hcomm
  refine ⟨minpoly ↥D.LL0 T, hsep, fun z hz => ?_⟩
  have h := aeval_map_of_comm V.subtype T T0 (fun _ => rfl) (minpoly ↥D.LL0 T) ⟨z, hz⟩
  rw [minpoly.aeval, LinearMap.zero_apply, map_zero] at h
  exact h.symm

end GlobalTheory.GoodSS.Heart
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCommutationRealExpansionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.LiftLeaf GlobalTheory.SupLaw Formalism.IndefR.NX
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_commutation_real_expansion : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (Rl : Formalism.IndefR.Links.RealDat3 D A3 Ks) (F : Formalism.IndefR.Links.Face3 D A3)
    (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : RatDat D.ntw) (Y : NExpRealS Rl cG S) (H : NExpRealH Rl cG S Y), CommG D → HkComm D → NExpHeckeRowX Rl cG S Y H (fun j => goodProjW S j D.nexp.eLL0) →
    Rl.Char3 F → Rl.toRealDat.LUnif → Rl.toRealDat.LIntegral →
    (∀ i P P', P ∈ D.ntw.S0 i → IsConjPl D.host P P' → P' ∈ D.ntw.S0 i) →
    (∀ i, placesOver D.host.E 2 ⊆ (D.ntw.S0 i : Set (PlE D.host))) →
    (∀ i, ∀ Q ∈ Rl.Sb, Q ∈ D.ntw.S0 i) →
    ∀ i, D.ntw.NonzeroIndexPlace i → ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (b : Bool) k P, HkIdx i k P →
      ∃ q : (↥D.LL0)[X], q.Separable ∧
        ∀ z ∈ LinearMap.range (GlobalTheory.GoodSS.goodProjectorBaseChangeForms S j (Y.rho j h1 h2) (Y.chi j h1 h2) D.nexp.eLL0),
          Polynomial.aeval (LinearMap.baseChange ↥D.LL0
            (GlobalTheory.GoodSS.opK S j (H.hL j k P) (fun x hx => H.hs j h1 h2 k P x hx))) q z = 0 := by
  first | exact @GlobalTheory.GoodSS.Heart.hL_separable_good | exact GlobalTheory.GoodSS.Heart.hL_separable_good | (intros; apply GlobalTheory.GoodSS.Heart.hL_separable_good <;> assumption)
end
