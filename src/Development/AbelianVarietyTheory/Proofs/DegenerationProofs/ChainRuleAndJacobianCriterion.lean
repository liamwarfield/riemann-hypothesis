module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ChainRuleAndJacobianCriterion
open KaehlerDifferential TensorProduct

namespace GlobalTheory.EtaleCoordJacobian

section tower
variable (R B : Type) [CommRing R] [CommRing B] (I : Type) [Algebra R B]
  [Algebra (MvPolynomial I R) B] [IsScalarTower R (MvPolynomial I R) B]

theorem _root_.GlobalTheory.EtaleCoordJacobian.mapBaseChange_basis (i : I) :
    mapBaseChange R (MvPolynomial I R) B (((mvPolynomialBasis R I).baseChange B) i) =
      D R B (algebraMap (MvPolynomial I R) B (MvPolynomial.X i)) := by
  rw [Module.Basis.baseChange_apply, mvPolynomialBasis_apply, mapBaseChange_tmul, one_smul,
    map_D]

theorem _root_.GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale [Finite I] [Algebra.Etale (MvPolynomial I R) B] :
    (∃ b : Module.Basis I B Ω[B⁄R],
      ∀ i, b i = D R B (algebraMap (MvPolynomial I R) B (MvPolynomial.X i))) ∧
      Algebra.Smooth R B := by
  haveI : Algebra.Smooth R (MvPolynomial I R) := Algebra.Smooth.mk
  refine ⟨⟨((mvPolynomialBasis R I).baseChange B).map
    (tensorKaehlerEquivOfFormallyEtale R (MvPolynomial I R) B), fun i => ?_⟩,
    Algebra.Smooth.comp R (MvPolynomial I R) B⟩
  rw [Module.Basis.map_apply, ← _root_.GlobalTheory.EtaleCoordJacobian.mapBaseChange_basis]
  rfl

theorem _root_.GlobalTheory.EtaleCoordJacobian.etale_of_basis [Finite I] [Algebra.Smooth R B]
    (b : Module.Basis I B Ω[B⁄R])
    (hb : ∀ i, b i = D R B (algebraMap (MvPolynomial I R) B (MvPolynomial.X i))) :
    Algebra.Etale (MvPolynomial I R) B := by
  set bc := (mvPolynomialBasis R I).baseChange B
  have hmap : mapBaseChange R (MvPolynomial I R) B = (bc.equiv b (Equiv.refl I)).toLinearMap :=
    bc.ext fun i => by
      rw [_root_.GlobalTheory.EtaleCoordJacobian.mapBaseChange_basis, LinearEquiv.coe_coe, Module.Basis.equiv_apply,
        Equiv.refl_apply, hb]
  have hinj : Function.Injective (mapBaseChange R (MvPolynomial I R) B) := by
    rw [hmap]; exact (bc.equiv b (Equiv.refl I)).injective
  have hsurj : Function.Surjective (mapBaseChange R (MvPolynomial I R) B) := by
    rw [hmap]; exact (bc.equiv b (Equiv.refl I)).surjective
  have hΩ : Subsingleton Ω[B⁄MvPolynomial I R] := by
    refine ⟨fun x y => ?_⟩
    have hx : ∀ z : Ω[B⁄MvPolynomial I R], z = 0 := fun z => by
      obtain ⟨w, rfl⟩ := map_surjective R (MvPolynomial I R) B z
      obtain ⟨v, rfl⟩ := hsurj w
      exact (exact_mapBaseChange_map R (MvPolynomial I R) B).apply_apply_eq_zero v
    rw [hx x, hx y]
  have hH : Subsingleton (Algebra.H1Cotangent (MvPolynomial I R) B) := by
    haveI : Subsingleton (Algebra.H1Cotangent R B) :=
      Algebra.FormallySmooth.subsingleton_h1Cotangent
    refine ⟨fun x y => ?_⟩
    have hx : ∀ z : Algebra.H1Cotangent (MvPolynomial I R) B, z = 0 := fun z => by
      have h1 : Algebra.H1Cotangent.δ R (MvPolynomial I R) B z = 0 :=
        hinj (((Algebra.H1Cotangent.exact_δ_mapBaseChange R _ B).apply_apply_eq_zero z).trans
          (map_zero _).symm)
      obtain ⟨w, rfl⟩ := (Algebra.H1Cotangent.exact_map_δ R (MvPolynomial I R) B z).mp h1
      rw [Subsingleton.elim w 0, map_zero]
    rw [hx x, hx y]
  haveI : Algebra.FormallyEtale (MvPolynomial I R) B := Algebra.FormallyEtale.mk hΩ hH
  haveI : Algebra.FinitePresentation (MvPolynomial I R) B :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ B
  exact Algebra.Etale.mk

end tower

private theorem exists_basis_D_and_smooth_of_etale_eval2Hom (R B I : Type) [CommRing R] [CommRing B]
    [Finite I] [Algebra R B] (t : I → B)
    (h : (MvPolynomial.eval₂Hom (algebraMap R B) t).Etale) :
    (∃ b : Module.Basis I B Ω[B⁄R], ∀ i, b i = D R B (t i)) ∧ Algebra.Smooth R B := by
  letI : Algebra (MvPolynomial I R) B := (MvPolynomial.eval₂Hom (algebraMap R B) t).toAlgebra
  haveI : IsScalarTower R (MvPolynomial I R) B := IsScalarTower.of_algebraMap_eq fun r => by
    simp [RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq]
  haveI : Algebra.Etale (MvPolynomial I R) B := h
  obtain ⟨⟨b, hb⟩, hs⟩ := _root_.GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale R B I
  exact ⟨⟨b, fun i => by rw [hb]; simp [RingHom.algebraMap_toAlgebra]⟩, hs⟩

private theorem det_derivation_eq_mul_det_repr {R B I : Type} [CommRing R] [CommRing B] [Fintype I]
    [DecidableEq I] [Algebra R B] (t t' : I → B) (b : Module.Basis I B Ω[B⁄R])
    (hb : ∀ i, b i = D R B (t i)) (C : Type) [CommRing C] (φ : B →+* C) (d : I → B →+ C)
    (hd : ∀ i x y, d i (x * y) = φ x * d i y + φ y * d i x)
    (hc : ∀ i r, d i (algebraMap R B r) = 0) :
    (Matrix.of fun i j => d i (t' j)).det =
      φ (Matrix.of fun k j => b.repr (D R B (t' j)) k).det *
        (Matrix.of fun i j => d i (t j)).det := by
  letI : Algebra B C := φ.toAlgebra
  letI : Algebra R C := (φ.comp (algebraMap R B)).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have key : ∀ i j, d i (t' j) = ∑ k, d i (t k) * φ (b.repr (D R B (t' j)) k) := by
    intro i j
    let δ : Derivation R B C := Derivation.mk'
      { toFun := d i
        map_add' := map_add (d i)
        map_smul' := fun r x => by
          rw [RingHom.id_apply, Algebra.smul_def r (d i x), Algebra.smul_def, hd, hc, mul_zero,
            add_zero]
          rfl }
      (fun x y => by
        simp only [LinearMap.coe_mk, AddHom.coe_mk, Algebra.smul_def]
        exact hd i x y)
    have h1 : ∀ x, d i x = δ.liftKaehlerDifferential (D R B x) := fun x => by
      rw [Derivation.liftKaehlerDifferential_comp_D]; rfl
    rw [h1]
    conv_lhs => rw [← b.sum_repr (D R B (t' j))]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, hb, ← h1, Algebra.smul_def, mul_comm]
    rfl
  have hmat : (Matrix.of fun i j => d i (t' j)) = (Matrix.of fun i j => d i (t j)) *
      (Matrix.of fun k j => b.repr (D R B (t' j)) k).map φ := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.map_apply, key]
  rw [hmat, Matrix.det_mul, mul_comm]
  congr 1
  exact (RingHom.map_det φ _).symm

private theorem exists_basis_D_of_isUnit_det_repr {R B I : Type} [CommRing R] [CommRing B]
    [Fintype I] [DecidableEq I] [Algebra R B] (t' : I → B) (b : Module.Basis I B Ω[B⁄R])
    (ha : IsUnit (Matrix.of fun k j => b.repr (D R B (t' j)) k).det) :
    ∃ b' : Module.Basis I B Ω[B⁄R], ∀ j, b' j = D R B (t' j) := by
  refine ⟨b.map (Matrix.toLinearEquiv b _ ha), fun j => ?_⟩
  rw [Module.Basis.map_apply, Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  conv_rhs => rw [← b.sum_repr (D R B (t' j))]
  simp only [Matrix.of_apply]

private theorem etale_eval2Hom_of_basis_D (R B I : Type) [CommRing R] [CommRing B]
    [Finite I] [Algebra R B] [Algebra.Smooth R B] (t : I → B) (b : Module.Basis I B Ω[B⁄R])
    (hb : ∀ i, b i = D R B (t i)) : (MvPolynomial.eval₂Hom (algebraMap R B) t).Etale := by
  letI : Algebra (MvPolynomial I R) B := (MvPolynomial.eval₂Hom (algebraMap R B) t).toAlgebra
  haveI : IsScalarTower R (MvPolynomial I R) B := IsScalarTower.of_algebraMap_eq fun r => by
    simp [RingHom.algebraMap_toAlgebra, MvPolynomial.algebraMap_eq]
  exact _root_.GlobalTheory.EtaleCoordJacobian.etale_of_basis R B I b fun i => by
    rw [hb]; simp [RingHom.algebraMap_toAlgebra]

theorem _root_.GlobalTheory.EtaleCoordJacobian.chain_rule_and_jacobian_criterion : ∀ (R B : Type) [CommRing R] [CommRing B] (c : R →+* B) (I : Type) [Fintype I] [DecidableEq I] (t t' : I → B), (MvPolynomial.eval₂Hom c t).Etale → ∃ a : B, (∀ (C : Type) [CommRing C] (φ : B →+* C) (d : I → B →+ C), (∀ i x y, d i (x * y) = φ x * d i y + φ y * d i x) → (∀ i r, d i (c r) = 0) → (Matrix.of fun i j => d i (t' j)).det = φ a * (Matrix.of fun i j => d i (t j)).det) ∧ (IsUnit a → (MvPolynomial.eval₂Hom c t').Etale) := by
  intro R B _ _ c I _ _ t t' het
  letI : Algebra R B := c.toAlgebra
  obtain ⟨⟨b, hb⟩, hs⟩ := exists_basis_D_and_smooth_of_etale_eval2Hom R B I t het
  refine ⟨(Matrix.of fun k j => b.repr (D R B (t' j)) k).det,
    fun C _ φ d hd hc => det_derivation_eq_mul_det_repr t t' b hb C φ d hd hc, fun ha => ?_⟩
  obtain ⟨b', hb'⟩ := exists_basis_D_of_isUnit_det_repr t' b ha
  exact etale_eval2Hom_of_basis_D R B I t' b' hb'

end GlobalTheory.EtaleCoordJacobian
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.OrthogonalFreeOfPerfectAltZmod
open Module TensorProduct

namespace GlobalTheory.ZModPerp

theorem exists_eq_nsmul_zmod {n r N : ℕ} [NeZero n] (h : r * N = n) (y : ZMod n)
    (hy : N • y = 0) : ∃ z : ZMod n, y = r • z := by
  have hN : N ≠ 0 := by
    rintro rfl
    exact NeZero.ne n (by simpa using h.symm)
  have h1 : ((N * y.val : ℕ) : ZMod n) = 0 := by
    simpa [nsmul_eq_mul] using hy
  rw [ZMod.natCast_eq_zero_iff] at h1
  replace h1 : N * r ∣ N * y.val := by rwa [mul_comm N r, h]
  obtain ⟨k, hk⟩ := Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hN) h1
  refine ⟨(k : ZMod n), ?_⟩
  rw [← ZMod.natCast_zmod_val y, hk]
  simp [nsmul_eq_mul]

theorem dvd_of_forall_mul_eq_zero {n : ℕ} [NeZero n] (x y : ZMod n)
    (h : ∀ a : ZMod n, a * x = 0 → a * y = 0) : x ∣ y := by
  obtain ⟨m, hm⟩ := Nat.gcd_dvd_right x.val n
  obtain ⟨k, hk⟩ := Nat.gcd_dvd_left x.val n
  have h1 : (m : ZMod n) * x = 0 := by
    have : ((m * x.val : ℕ) : ZMod n) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      refine ⟨k, ?_⟩
      calc m * x.val = m * (Nat.gcd x.val n * k) := by rw [← hk]
        _ = (Nat.gcd x.val n * m) * k := by ring
        _ = n * k := by rw [← hm]
    simpa using this
  obtain ⟨z, hz⟩ := exists_eq_nsmul_zmod hm.symm y (by simpa [nsmul_eq_mul] using h _ h1)
  have h2 := congrArg (Int.cast : ℤ → ZMod n) (Nat.gcd_eq_gcd_ab x.val n)
  simp only [Int.cast_natCast, Int.cast_add, Int.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
    ZMod.natCast_zmod_val] at h2
  rw [hz, nsmul_eq_mul, h2, mul_assoc]
  exact dvd_mul_right _ _

theorem isPrincipalIdealRing_zmod (n : ℕ) : IsPrincipalIdealRing (ZMod n) :=
  IsPrincipalIdealRing.of_surjective (Int.castRingHom (ZMod n)) (ZMod.ringHom_surjective _)

theorem baer_zmod (n : ℕ) [NeZero n] : Module.Baer (ZMod n) (ZMod n) := by
  intro I g
  obtain ⟨x, rfl⟩ := ((isPrincipalIdealRing_zmod n).principal I).principal
  have hx : x ∈ Submodule.span (ZMod n) {x} := Submodule.mem_span_singleton_self x
  obtain ⟨c, hc⟩ := dvd_of_forall_mul_eq_zero x (g ⟨x, hx⟩) fun a ha => by
    rw [← smul_eq_mul, ← map_smul]
    have : a • (⟨x, hx⟩ : Submodule.span (ZMod n) {x}) = 0 := Subtype.ext ha
    rw [this, map_zero]
  refine ⟨LinearMap.toSpanSingleton _ _ c, fun y hy => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have : (⟨a • x, hy⟩ : Submodule.span (ZMod n) {x}) = a • ⟨x, hx⟩ := rfl
  rw [this, map_smul g, hc]
  simp [mul_assoc]

theorem exists_dual_ne_zero {n : ℕ} [NeZero n] {M : Type*} [AddCommGroup M] [Module (ZMod n) M]
    {q : M} (hq : q ≠ 0) : ∃ f : Dual (ZMod n) M, f q ≠ 0 := by
  obtain ⟨x, hx⟩ := ((isPrincipalIdealRing_zmod n).principal
    (LinearMap.ker (LinearMap.toSpanSingleton (ZMod n) M q))).principal
  have hx' : ∀ a : ZMod n, a • q = 0 ↔ x ∣ a := fun a => by
    rw [← Ideal.mem_span_singleton, ← Ideal.submodule_span_eq, ← hx]
    simp
  obtain ⟨c, hc, hc0⟩ : ∃ c : ZMod n, c * x = 0 ∧ c ≠ 0 := by
    by_contra! H
    have := dvd_of_forall_mul_eq_zero x 1 fun a ha => by simp [H a ha]
    exact hq (by simpa using (hx' 1).mpr this)
  have H : ∀ a : ZMod n, a • q = 0 → (RingHom.id (ZMod n)) a • c = 0 := fun a ha => by
    obtain ⟨b, rfl⟩ := (hx' a).mp ha
    simp only [RingHom.id_apply, smul_eq_mul]
    linear_combination b * hc
  let φ := LinearPMap.mkSpanSingleton' q c H
  obtain ⟨f, hf⟩ := (baer_zmod n).extension_property φ.domain.subtype
    φ.domain.subtype_injective φ.toFun
  refine ⟨f, ?_⟩
  have := LinearMap.congr_fun hf ⟨q, Submodule.mem_span_singleton_self q⟩
  have h2 := LinearPMap.mkSpanSingleton'_apply_self q c H (Submodule.mem_span_singleton_self q)
  have h3 : f q = c := this.trans h2
  rwa [h3]

theorem baer_of_free {n : ℕ} [NeZero n] (M : Type*) [AddCommGroup M] [Module (ZMod n) M]
    [Module.Free (ZMod n) M] [Module.Finite (ZMod n) M] : Module.Baer (ZMod n) M := by
  let b := Module.Free.chooseBasis (ZMod n) M
  refine Module.Baer.of_equiv b.equivFun.symm fun I g => ?_
  choose l hl using fun i => baer_zmod n I ((LinearMap.proj i).comp g)
  exact ⟨LinearMap.pi l, fun x hx => funext fun i => hl i x hx⟩

theorem exists_eq_nsmul_of_free {n r N : ℕ} [NeZero n] (h : r * N = n) {M : Type*}
    [AddCommGroup M] [Module (ZMod n) M] [Module.Free (ZMod n) M] [Module.Finite (ZMod n) M]
    (y : M) (hy : N • y = 0) : ∃ z : M, y = r • z := by
  let b := Module.Free.chooseBasis (ZMod n) M
  choose z hz using fun i => exists_eq_nsmul_zmod h (b.equivFun y i) (by
    rw [← Pi.smul_apply, ← map_nsmul, hy, map_zero, Pi.zero_apply])
  refine ⟨b.equivFun.symm z, b.equivFun.injective ?_⟩
  rw [map_nsmul, LinearEquiv.apply_symm_apply]
  exact funext hz

theorem free_of_isCompl {R M : Type*} [CommRing R] [Finite (MaximalSpectrum R)] [AddCommGroup M]
    [Module R M] [Module.Free R M] [Module.Finite R M] {T T' : Submodule R M} [Module.Free R T]
    (h : IsCompl T T') : Module.Free R T' := by
  let e := Submodule.prodEquivOfIsCompl T T' h
  have : Module.Finite R T := Module.Finite.of_surjective (T.projectionOnto T' h)
    (Submodule.projectionOnto_surjective h)
  have : Module.Finite R T' := Module.Finite.of_surjective (T'.projectionOnto T h.symm)
    (Submodule.projectionOnto_surjective h.symm)
  have : Module.Projective R T' :=
    Module.Projective.of_split T'.subtype (T'.projectionOnto T h.symm) (by ext; simp)
  refine Module.free_of_flat_of_finrank_eq R T' (finrank R M - finrank R T) fun P => ?_
  let := P.isMaximal
  let := Ideal.Quotient.field P.asIdeal
  have : Nontrivial R := (Ideal.Quotient.mk P.asIdeal).domain_nontrivial
  have e' : ((R ⧸ P.1) ⊗[R] M) ≃ₗ[R ⧸ P.1] ((R ⧸ P.1) ⊗[R] T) × ((R ⧸ P.1) ⊗[R] T') :=
    (e.symm.baseChange R (R ⧸ P.1) _ _).trans (TensorProduct.prodRight R (R ⧸ P.1) _ _ _)
  have := e'.finrank_eq
  rw [finrank_prod, finrank_baseChange, finrank_baseChange] at this
  omega

end GlobalTheory.ZModPerp

namespace GlobalTheory

open ZModPerp

theorem orthogonal_free_of_perfect_alt_zmod :
    ∀ (N r : ℕ) [NeZero (r * N)] (Γ : Type) [AddCommGroup Γ] [Module (ZMod (r * N)) Γ]
      [Module.Free (ZMod (r * N)) Γ] [Module.Finite (ZMod (r * N)) Γ]
      (e : LinearMap.BilinForm (ZMod (r * N)) Γ), e.IsAlt → Function.Bijective e →
      (∀ H : Submodule (ZMod (r * N)) Γ, e.orthogonal (e.orthogonal H) = H) ∧
      ∀ T : Submodule (ZMod (r * N)) Γ, Module.Free (ZMod (r * N)) T →
        (∃ T', IsCompl T T') ∧ Module.Free (ZMod (r * N)) (e.orthogonal T) ∧
        (∀ t ∈ T, N • t = 0 ↔ ∃ t' ∈ T, t = r • t') ∧
        ∀ a : Γ, (∀ t ∈ T, r • e a t = 0) ↔ ∃ h ∈ e.orthogonal T, r • a = r • h := by
  intro N r _ Γ _ _ _ _ e halt hbij
  have hmem : ∀ (H : Submodule (ZMod (r * N)) Γ) (x : Γ),
      x ∈ e.orthogonal H ↔ ∀ y ∈ H, e x y = 0 := fun H x => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    exact forall₂_congr fun y _ => ⟨halt.isRefl _ _, halt.isRefl _ _⟩
  have hkill : ∀ x : Γ, (r * N) • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul (ZMod (r * N)), ZMod.natCast_self, zero_smul]
  refine ⟨fun H => le_antisymm (fun x hx => ?_) (fun x hx => ?_), fun T hT => ?_⟩
  · by_contra hxH
    obtain ⟨f, hf⟩ := exists_dual_ne_zero (n := r * N) (q := H.mkQ x)
      (by simpa using hxH)
    obtain ⟨b, hb⟩ := hbij.2 (f ∘ₗ H.mkQ)
    have hb' : b ∈ e.orthogonal H := (hmem _ _).mpr fun y hy => by
      rw [hb, LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero H).mpr hy,
        map_zero]
    have := halt.isRefl _ _ ((hmem _ _).mp hx b hb')
    rw [hb] at this
    exact hf this
  · exact (hmem _ _).mpr fun y hy => halt.isRefl _ _ ((hmem _ _).mp hy x hx)
  · obtain ⟨p, hp⟩ := (baer_of_free (n := r * N) T).extension_property T.subtype
      T.subtype_injective LinearMap.id
    have hp' : ∀ t : T, p t = t := fun t => LinearMap.congr_fun hp t
    have hc : IsCompl T (LinearMap.ker p) := LinearMap.isCompl_of_proj hp'
    refine ⟨⟨_, hc⟩, ?_, fun t ht => ⟨fun h => ?_, ?_⟩, fun a => ⟨fun h => ?_, ?_⟩⟩
    · have := free_of_isCompl hc
      have : Module.Free (ZMod (r * N)) (Γ ⧸ T) :=
        Module.Free.of_equiv (Submodule.quotientEquivOfIsCompl T _ hc).symm
      have E : e.orthogonal T ≃ₗ[ZMod (r * N)] T.dualAnnihilator :=
        (LinearEquiv.ofBijective e hbij).ofSubmodules _ _ (by
          ext f
          obtain ⟨b, rfl⟩ := hbij.2 f
          simp only [Submodule.mem_map, Submodule.mem_dualAnnihilator, hmem]
          constructor
          · rintro ⟨x, hx, hxb⟩
            rw [← hxb]
            exact hx
          · exact fun h => ⟨b, h, rfl⟩)
      exact Module.Free.of_equiv (E.trans T.dualQuotEquivDualAnnihilator.symm).symm
    · obtain ⟨z, hz⟩ := exists_eq_nsmul_of_free (n := r * N) rfl (⟨t, ht⟩ : T) (Subtype.ext h)
      exact ⟨z, z.2, congrArg Subtype.val hz⟩
    · rintro ⟨t', -, rfl⟩
      rw [← mul_smul, mul_comm, hkill]
    · obtain ⟨l, hl⟩ := exists_eq_nsmul_of_free (n := r * N) (mul_comm N r)
        (M := Dual (ZMod (r * N)) T) (e a ∘ₗ T.subtype) (LinearMap.ext fun t => h t t.2)
      obtain ⟨b, hb⟩ := hbij.2 (l ∘ₗ p)
      refine ⟨a - N • b, (hmem _ _).mpr fun y hy => ?_, ?_⟩
      · have h1 : e a y = N • l ⟨y, hy⟩ := LinearMap.congr_fun hl ⟨y, hy⟩
        have h2 : e b y = l ⟨y, hy⟩ := by
          rw [hb, LinearMap.comp_apply, hp' ⟨y, hy⟩]
        rw [map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply, h1, h2, sub_self]
      · rw [smul_sub, ← mul_smul, hkill, sub_zero]
    · rintro ⟨h, hh, hah⟩ t ht
      rw [← LinearMap.smul_apply, ← map_nsmul, hah, map_nsmul, LinearMap.smul_apply,
        (hmem _ _).mp hh t ht, smul_zero]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAlgHomOfFiniteTypeOfIsAlgClosed
open scoped BigOperators
open Matrix

namespace GlobalTheory

theorem exists_algHom_of_finiteType_of_isAlgClosed (K C F : Type) [Field K] [CommRing C]
    [Nontrivial C] [Algebra K C] [Algebra.FiniteType K C] [Field F] [IsAlgClosed F]
    [Algebra K F] : Nonempty (C →ₐ[K] F) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal C
  let := Ideal.Quotient.field m
  have := finite_of_finite_type_of_isJacobsonRing K (C ⧸ m)
  exact ⟨(IsAlgClosed.lift : (C ⧸ m) →ₐ[K] F).comp (Ideal.Quotient.mkₐ K m)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsBasisAdaptedToIdempotents
open Module

namespace GlobalTheory.ZH

private lemma mulVec_column_of_orthogonal_idempotents {R J C : Type} [CommRing R] [Fintype J]
    [DecidableEq C] (e : C → Matrix J J R)
    (he : ∀ c c', e c * e c' = if c = c' then e c else 0) (d c : C) (s : J) :
    (e d).mulVec (fun j => e c j s) = if d = c then (fun j => e c j s) else 0 := by
  ext i
  have h := congrFun (congrFun (he d c) i) s
  rw [Matrix.mul_apply] at h
  simp only [Matrix.mulVec, dotProduct]
  rw [h]
  split_ifs with hdc
  · subst hdc; rfl
  · rfl

theorem _root_.GlobalTheory.ZH.exists_basis_adapted_to_idempotents :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (J C : Type) [Fintype J] [DecidableEq J] [Fintype C]
      [DecidableEq C] (e : C → Matrix J J O),
      (∀ c c', e c * e c' = if c = c' then e c else 0) → ∑ c, e c = 1 →
      ∃ (κ : J → C) (col : J → J),
        IsUnit (Matrix.det (Matrix.of fun i j => e (κ i) j (col i))) ∧
        ∀ c, Submodule.span O (Set.range fun i => fun j => e c j i) =
          Submodule.span O {v | ∃ i, κ i = c ∧ v = fun j => e c j (col i)} := by
  intro O _ _ J C _ _ _ _ e he hsum
  classical
  let f : Matrix J J O →+* Matrix J J (IsLocalRing.ResidueField O) :=
    (IsLocalRing.residue O).mapMatrix
  let E : C → Matrix J J (IsLocalRing.ResidueField O) := fun c => f (e c)
  have hE : ∀ c c', E c * E c' = if c = c' then E c else 0 := by
    intro c c'
    simp only [E, ← map_mul, he]
    split_ifs <;> simp
  have hEsum : ∑ c, E c = 1 := by simp only [E, ← map_sum, hsum, map_one]
  let w : C → J → (J → IsLocalRing.ResidueField O) := fun c s j => E c j s
  choose T a ha hsp hli using fun c => exists_linearIndependent' (IsLocalRing.ResidueField O) (w c)
  haveI : ∀ c, Fintype (T c) := fun c => Fintype.ofInjective (a c) (ha c)
  let W : (Σ c, T c) → (J → IsLocalRing.ResidueField O) := fun p => w p.1 (a p.1 p.2)
  have hWli : LinearIndependent (IsLocalRing.ResidueField O) W := by
    rw [Fintype.linearIndependent_iff]
    intro g hg p
    obtain ⟨d, t⟩ := p
    have h1 := congrArg (Matrix.mulVecLin (E d)) hg
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_zero, Matrix.mulVecLin_apply, W, w,
      mulVec_column_of_orthogonal_idempotents E hE, Fintype.sum_sigma, smul_ite, smul_zero] at h1
    rw [Finset.sum_eq_single d (fun c _ hc => by simp [Ne.symm hc]) (by simp)] at h1
    simp only [if_pos rfl] at h1
    exact Fintype.linearIndependent_iff.mp (hli d) (fun t => g ⟨d, t⟩) h1 t
  have hWsp : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField O) (Set.range W) := by
    rw [← (Pi.basisFun (IsLocalRing.ResidueField O) J).span_eq, Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    have hs : Pi.basisFun (IsLocalRing.ResidueField O) J s = ∑ c, w c s := by
      ext j
      have := congrFun (congrFun hEsum j) s
      simp only [Matrix.sum_apply, Matrix.one_apply] at this
      simp [w, Finset.sum_apply, this, Pi.single_apply]
    rw [hs]
    refine Submodule.sum_mem _ fun c _ => ?_
    have h2 : w c s ∈ Submodule.span (IsLocalRing.ResidueField O) (Set.range (w c ∘ a c)) := by
      rw [hsp c]; exact Submodule.subset_span ⟨s, rfl⟩
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨t, rfl⟩
    exact ⟨⟨c, t⟩, rfl⟩
  let b := Basis.mk hWli hWsp
  have hcard : Fintype.card J = Fintype.card (Σ c, T c) := by
    rw [← Module.finrank_fintype_fun_eq_card (IsLocalRing.ResidueField O),
      Module.finrank_eq_card_basis b]
  let σ : J ≃ (Σ c, T c) := Fintype.equivOfCardEq hcard
  let M : Matrix J J O := Matrix.of fun i j => e (σ i).1 j (a (σ i).1 (σ i).2)
  have hdet : IsUnit M.det := by
    rw [← isUnit_map_iff (IsLocalRing.residue O), RingHom.map_det,
      ← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_rows_iff_isUnit]
    exact hWli.comp σ σ.injective
  refine ⟨fun i => (σ i).1, fun i => a (σ i).1 (σ i).2, hdet, fun c => le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    show (fun j => e c j s) ∈ Submodule.span O _
    have hfix : (e c).mulVec (fun j => e c j s) = fun j => e c j s := by
      simpa using mulVec_column_of_orthogonal_idempotents e he c c s
    have h3 : (fun j => e c j s) = Matrix.vecMul (Matrix.vecMul (fun j => e c j s) M⁻¹) M := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
    have h4 : (fun j => e c j s) =
        ∑ i, (Matrix.vecMul (fun j => e c j s) M⁻¹) i • (e c).mulVec (M i) := by
      calc (fun j => e c j s) = (e c).mulVec (fun j => e c j s) := hfix.symm
        _ = (e c).mulVec (Matrix.vecMul (Matrix.vecMul (fun j => e c j s) M⁻¹) M) := by rw [← h3]
        _ = _ := by
          rw [Matrix.vecMul_eq_sum]
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [← Matrix.mulVecLin_apply, map_sum, map_smul]
    rw [h4]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have h5 : (e c).mulVec (M i) = if c = (σ i).1 then M i else 0 :=
      mulVec_column_of_orthogonal_idempotents e he c (σ i).1 _
    rw [h5]
    split_ifs with h
    · exact Submodule.subset_span ⟨i, h.symm, by subst h; rfl⟩
    · exact zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨i, -, rfl⟩
    exact Submodule.subset_span ⟨a (σ i).1 (σ i).2, rfl⟩

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasSumMapPowerSeriesMkFinsum
open Module

namespace GlobalTheory

theorem hasSum_map_powerSeries_mk_finsum : ∀ (O K Z : Type) [CommRing O] [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (φ : PowerSeries O →+* K), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (deg : Z → ℕ), (∀ n, {z | deg z = n}.Finite) → ∀ a : Z → O, HasSum (fun z => φ (PowerSeries.C (a z)) * φ PowerSeries.X ^ deg z) (φ (PowerSeries.mk fun n => ∑ᶠ (z : Z) (_ : deg z = n), a z)) := by
  intro O K Z _ _ _ _ φ h1 hX deg hfin a
  classical
  set F : PowerSeries O := PowerSeries.mk fun n => ∑ᶠ (z : Z) (_ : deg z = n), a z with hF
  have key : ∀ (n : ℕ) (s : Finset Z), (∀ z, deg z < n → z ∈ s) →
      ‖(∑ z ∈ s, φ (PowerSeries.C (a z)) * φ PowerSeries.X ^ deg z) - φ F‖
        ≤ ‖φ PowerSeries.X‖ ^ n := by
    intro n s hs
    have hdvd : (PowerSeries.X : PowerSeries O) ^ n ∣
        (∑ z ∈ s, PowerSeries.C (a z) * PowerSeries.X ^ deg z) - F := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, hF, PowerSeries.coeff_mk, sub_eq_zero]
      have : (∑ᶠ (z : Z) (_ : deg z = m), a z) = ∑ z ∈ s.filter (fun z => deg z = m), a z := by
        rw [← finsum_mem_coe_finset]
        refine finsum_congr fun z => ?_
        refine finsum_congr_Prop ?_ (fun _ => rfl)
        apply propext
        simp only [Finset.coe_filter, Set.mem_setOf_eq]
        exact ⟨fun h => ⟨hs z (h ▸ hm), h⟩, fun h => h.2⟩
      rw [this, Finset.sum_filter]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      by_cases h : deg z = m
      · simp [h]
      · simp [h, Ne.symm h]
    obtain ⟨g, hg⟩ := hdvd
    have h2 := congrArg φ hg
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_mul, map_pow] at h2
    rw [h2, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (h1 g)
  rw [HasSum, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hX
  have hfn : {z | deg z < n}.Finite := by
    refine ((Set.finite_Iio n).biUnion (fun m _ => hfin m)).subset ?_
    intro z hz
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_Iio]
    exact ⟨deg z, hz, rfl⟩
  simp only [SummationFilter.unconditional_filter]
  filter_upwards [Filter.eventually_ge_atTop hfn.toFinset] with s hs
  rw [dist_eq_norm]
  exact (key n s fun z hz => hs (hfn.mem_toFinset.2 hz)).trans_lt hn

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.CoeffEqZeroOfHasSumMFourierOrthonormalImage
open scoped BigOperators
open Matrix

namespace GlobalTheory

theorem coeff_eq_zero_of_hasSum_mFourier_orthonormal_image {J : Type} [Fintype J] {E : Type}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (L : C(UnitAddTorus J, ℂ) →L[ℂ] E)
    (hL : Orthonormal ℂ (fun n : J → ℤ => L (UnitAddTorus.mFourier n))) (b : (J → ℤ) → ℂ)
    (h : HasSum (fun s => b s • UnitAddTorus.mFourier s) (0 : C(UnitAddTorus J, ℂ)))
    (t : J → ℤ) : b t = 0 := by
  classical
  have h1 := ((innerSL ℂ (L (UnitAddTorus.mFourier t))).comp L).hasSum h
  have h2 : HasSum (fun s => if s = t then b t else 0) (0 : ℂ) := by
    rw [map_zero] at h1
    refine HasSum.congr_fun h1 fun s => ?_
    have := orthonormal_iff_ite.mp hL t s
    simp only [ContinuousLinearMap.comp_apply, map_smul, innerSL_apply_apply, this, smul_eq_mul]
    by_cases hs : s = t
    · simp [hs]
    · simp [hs, Ne.symm hs]
  exact (hasSum_ite_eq t (b t)).unique h2

theorem mFourier_coe_eq_exp {J : Type} [Fintype J] (s : J → ℤ) (x : J → ℝ) :
    UnitAddTorus.mFourier s (fun j => (x j : UnitAddCircle)) =
      Complex.exp (2 * Real.pi * Complex.I * ∑ j, (s j : ℂ) * (x j : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_coe_apply]
  rw [Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun j _ => ?_
  congr 1
  push_cast
  ring

theorem coeff_eq_zero_of_fourier_series_eq_zero :
    ∀ (J : Type) [Fintype J] (b : (J → ℤ) → ℂ), (Summable fun s => ‖b s‖) →
      (∀ x : J → ℝ, ∑' s, b s *
        Complex.exp (2 * Real.pi * Complex.I * ∑ j, (s j : ℂ) * (x j : ℂ)) = 0) →
      ∀ s, b s = 0 := by
  intro J _ b hb h0 t
  have hs : Summable (fun s => b s • UnitAddTorus.mFourier s : (J → ℤ) → C(UnitAddTorus J, ℂ)) := by
    refine Summable.of_norm ?_
    simpa only [norm_smul, UnitAddTorus.mFourier_norm, mul_one] using hb
  have hz : (∑' s, b s • UnitAddTorus.mFourier s : C(UnitAddTorus J, ℂ)) = 0 := by
    ext y
    choose x hx using fun j => QuotientAddGroup.mk_surjective (y j)
    have hy : y = fun j => (x j : UnitAddCircle) := funext fun j => (hx j).symm
    have h1 := ((ContinuousMap.evalCLM ℂ y).hasSum hs.hasSum).tsum_eq
    simp only [map_smul, ContinuousMap.evalCLM_apply, smul_eq_mul] at h1
    rw [← h1, hy]
    simp only [mFourier_coe_eq_exp]
    simpa using h0 x
  have hsum := hs.hasSum
  rw [hz] at hsum
  exact coeff_eq_zero_of_hasSum_mFourier_orthonormal_image _ UnitAddTorus.orthonormal_mFourier b hsum t

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsArithFrobeniusAbsGalois
namespace GlobalTheory

open IsLocalRing

theorem _root_.GlobalTheory.exists_arithFrobenius_absGalois (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (hfin : Finite (IsLocalRing.ResidueField V)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [Algebra V Ω] [IsScalarTower V K Ω] [IsLocalRing (integralClosure V Ω)] : ∃ φ : Ω ≃ₐ[K] Ω, ∀ x : integralClosure V Ω, ∃ y : integralClosure V Ω, (y : Ω) = φ x ∧ y - x ^ Nat.card (IsLocalRing.ResidueField V) ∈ IsLocalRing.maximalIdeal (integralClosure V Ω) := by
  classical
  haveI : Algebra.IsIntegral K Ω := inferInstance
  letI : TopologicalSpace (integralClosure V Ω) := ⊥
  haveI : DiscreteTopology (integralClosure V Ω) := ⟨rfl⟩
  haveI : ContinuousSMul (Ω ≃ₐ[K] Ω) (integralClosure V Ω) := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    convert stabilizer_isOpen_of_isIntegral (K := K) (L := Ω) (x : Ω) using 2
    ext g
    simp [MulAction.mem_stabilizer_iff, Subtype.ext_iff]
  haveI : Algebra.IsInvariant V (integralClosure V Ω) (Ω ≃ₐ[K] Ω) := by
    refine ⟨fun x hx => ?_⟩
    have hmem : (x : Ω) ∈ IntermediateField.fixedField (⊤ : Subgroup (Ω ≃ₐ[K] Ω)) := by
      rintro ⟨g, -⟩
      exact congrArg Subtype.val (hx g)
    rw [InfiniteGalois.fixedField_bot, IntermediateField.mem_bot] at hmem
    obtain ⟨k, hk⟩ := hmem
    have hx2 : IsIntegral V (x : Ω) := x.2
    rw [← hk] at hx2
    have hint : IsIntegral V k :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom V K Ω) (algebraMap K Ω).injective).mp hx2
    obtain ⟨v, hv⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
    refine ⟨v, Subtype.ext ?_⟩
    simp [IsScalarTower.algebraMap_apply V K Ω, hv, hk]
  haveI : (maximalIdeal (integralClosure V Ω)).LiesOver (maximalIdeal V) := by
    refine ⟨(IsLocalRing.eq_maximalIdeal ?_).symm⟩
    exact Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := V)
      (maximalIdeal (integralClosure V Ω))
  letI : Fintype (V ⧸ maximalIdeal V) := @Fintype.ofFinite _ hfin
  letI : Field (V ⧸ maximalIdeal V) := Ideal.Quotient.field _
  letI : Field (integralClosure V Ω ⧸ maximalIdeal (integralClosure V Ω)) :=
    Ideal.Quotient.field _
  haveI : Algebra.IsIntegral (V ⧸ maximalIdeal V)
      (integralClosure V Ω ⧸ maximalIdeal (integralClosure V Ω)) := inferInstance
  haveI : Algebra.IsAlgebraic (V ⧸ maximalIdeal V)
      (integralClosure V Ω ⧸ maximalIdeal (integralClosure V Ω)) := Algebra.IsIntegral.isAlgebraic
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := Ω ≃ₐ[K] Ω)
    (maximalIdeal V) (maximalIdeal (integralClosure V Ω))
    (FiniteField.frobeniusAlgEquivOfAlgebraic (V ⧸ maximalIdeal V) _)
  refine ⟨g.1, fun x => ⟨g.1 • x, rfl, ?_⟩⟩
  rw [← Ideal.Quotient.eq]
  have h := congrArg (fun e => e (Ideal.Quotient.mk (maximalIdeal (integralClosure V Ω)) x)) hg
  simp only [Ideal.Quotient.stabilizerHom_apply, FiniteField.frobeniusAlgEquivOfAlgebraic_apply] at h
  rw [Fintype.card_eq_nat_card] at h
  rw [map_pow]
  exact h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ClosureZmodPowEqTopOfMeetsTorsionCosets
namespace GlobalTheory.ThetaReal

theorem zmod_pow_exists_nsmul_of_nsmul_eq_zero (n J : ℕ) (hn : 1 ≤ n) (hJ : 2 ≤ J)
    (y : ZMod (n ^ J)) (hy : n • y = 0) : ∃ w : ZMod (n ^ J), y = n • w := by
  haveI : NeZero (n ^ J) := ⟨pow_ne_zero _ (by omega)⟩
  obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective y
  rw [nsmul_eq_mul, ← Nat.cast_mul, ZMod.natCast_eq_zero_iff] at hy
  obtain ⟨j, rfl⟩ : ∃ j, J = j + 2 := ⟨J - 2, by omega⟩
  have h1 : n * (n * n ^ j) ∣ n * k := by
    have : n * (n * n ^ j) = n ^ (j + 2) := by ring
    rw [this]; exact hy
  have h2 : n * n ^ j ∣ k := Nat.dvd_of_mul_dvd_mul_left (by omega) h1
  obtain ⟨c, rfl⟩ := (Dvd.intro _ rfl : n ∣ n * n ^ j).trans h2
  exact ⟨(c : ZMod (n ^ (j + 2))), by rw [nsmul_eq_mul, Nat.cast_mul]⟩

theorem closure_eq_top_of_meets_torsion_cosets :
    ∀ (κ : Type) (n J M : ℕ), 1 ≤ n → 2 ≤ J → M = n ^ J → ∀ X : Set (κ → ZMod M),
      (∀ a : κ → ZMod M, ∃ y : κ → ZMod M, n • y = 0 ∧ a + y ∈ X) →
      AddSubgroup.closure X = ⊤ := by
  intro κ n J M hn hJ hM X hX
  subst hM
  have step : ∀ a : κ → ZMod (n ^ J), ∃ w : κ → ZMod (n ^ J),
      a + n • w ∈ AddSubgroup.closure X := by
    intro a
    obtain ⟨y, hy, hay⟩ := hX a
    have : ∀ i, ∃ w : ZMod (n ^ J), y i = n • w := fun i =>
      zmod_pow_exists_nsmul_of_nsmul_eq_zero n J hn hJ (y i) (congrFun hy i)
    choose w hw using this
    refine ⟨w, ?_⟩
    have : n • w = y := funext fun i => (hw i).symm
    rw [this]
    exact AddSubgroup.subset_closure hay
  have ind : ∀ (i : ℕ) (a : κ → ZMod (n ^ J)), ∃ w : κ → ZMod (n ^ J),
      a + n ^ i • w ∈ AddSubgroup.closure X := by
    intro i
    induction i with
    | zero => intro a; exact ⟨-a, by simp⟩
    | succ i ih =>
      intro a
      obtain ⟨w, hw⟩ := ih a
      obtain ⟨v, hv⟩ := step (-w)
      refine ⟨v, ?_⟩
      have h := (AddSubgroup.closure X).add_mem hw ((AddSubgroup.closure X).nsmul_mem hv (n ^ i))
      have e : a + n ^ i • w + n ^ i • (-w + n • v) = a + n ^ (i + 1) • v := by
        rw [smul_add, smul_neg, smul_smul, pow_succ]; abel
      rwa [e] at h
  rw [eq_top_iff]
  intro a _
  obtain ⟨w, hw⟩ := ind J a
  have : n ^ J • w = 0 := by
    funext i
    show n ^ J • w i = 0
    rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rwa [this, add_zero] at hw

end GlobalTheory.ThetaReal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FinsuppEqZeroOfSumTorsionCharactersEqZero
open Module

namespace GlobalTheory

theorem exists_eq_add_nsmul_of_torsion_characters_eq (k X : Type) [Field k] [AddCommGroup X]
    [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (ζ : k) (hN : 0 < N)
    (hζ : IsPrimitiveRoot ζ N) (α β : X)
    (h : ∀ t : Multiplicative X →* kˣ, t ^ N = 1 →
      t (Multiplicative.ofAdd α) = t (Multiplicative.ofAdd β)) :
    ∃ w, α = β + N • w := by
  classical
  have hu : IsUnit ζ := hζ.isUnit hN.ne'
  obtain ⟨u, rfl⟩ := hu
  have hu' : IsPrimitiveRoot u N := IsPrimitiveRoot.coe_units_iff.mp hζ
  let b := Module.Free.chooseBasis ℤ X
  have key : ∀ i, (N : ℤ) ∣ b.repr (α - β) i := by
    intro i
    let t : Multiplicative X →* kˣ :=
      { toFun := fun x => u ^ (b.repr (Multiplicative.toAdd x) i)
        map_one' := by simp
        map_mul' := by
          intro x y
          simp [zpow_add] }
    have ht : t ^ N = 1 := by
      refine MonoidHom.ext fun x => ?_
      have : (u ^ (b.repr (Multiplicative.toAdd x) i)) ^ N = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu'.pow_eq_one,
          one_zpow]
      rw [MonoidHom.pow_apply, MonoidHom.one_apply]
      exact this
    have h1 : u ^ (b.repr α i) = u ^ (b.repr β i) := h t ht
    rw [← hu'.zpow_eq_one_iff_dvd, map_sub, Finsupp.sub_apply, zpow_sub, h1, mul_inv_cancel]
  choose d hd using key
  refine ⟨∑ i, d i • b i, ?_⟩
  rw [← sub_eq_iff_eq_add', ← b.sum_repr (α - β), Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hd i, mul_smul, natCast_zsmul]

theorem finsupp_eq_zero_of_sum_torsion_characters_eq_zero :
    ∀ (k X : Type) [Field k] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (N : ℕ) (ζ : k), 0 < N → IsPrimitiveRoot ζ N → ∀ (M : Type) [AddCommGroup M] [Module k M] (c : X →₀ M), (∀ α ∈ c.support, ∀ β ∈ c.support, (∃ w, α = β + N • w) → α = β) → (∀ t : Multiplicative X →* kˣ, t ^ N = 1 → c.sum (fun α m => (t (Multiplicative.ofAdd α) : k) • m) = 0) → c = 0 := by
  intro k X _ _ _ _ N ζ hN hζ M _ _ c hc hsum
  classical
  let G : Subgroup (Multiplicative X →* kˣ) := (powMonoidHom N).ker
  let ev : c.support → (G →* k) := fun α =>
    { toFun := fun t => ((t : Multiplicative X →* kˣ) (Multiplicative.ofAdd (α : X)) : k)
      map_one' := by simp
      map_mul' := by
        intro s t
        simp }
  have hinj : Function.Injective ev := by
    intro α β hαβ
    apply Subtype.ext
    refine hc _ α.2 _ β.2
      (exists_eq_add_nsmul_of_torsion_characters_eq k X N ζ hN hζ _ _ fun t ht => ?_)
    exact Units.ext (DFunLike.congr_fun hαβ (⟨t, ht⟩ : G))
  have hli : LinearIndependent k (fun α : c.support => (ev α : G → k)) :=
    (linearIndependent_monoidHom G k).comp ev hinj
  ext α
  by_contra hα
  have hmem : α ∈ c.support := Finsupp.mem_support_iff.mpr hα
  apply hα
  rw [Finsupp.zero_apply, ← Module.forall_dual_apply_eq_zero_iff k]
  intro φ
  refine Fintype.linearIndependent_iff.mp hli (fun β => φ (c β)) ?_ ⟨α, hmem⟩
  funext t
  have h0 := congrArg φ (hsum t t.2)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finsupp.sum, map_sum, map_zero, ← Finset.sum_coe_sort] at h0
  rw [Finset.sum_apply, Pi.zero_apply, ← h0]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [map_smul, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_comm]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsEqDivOfIsPullback
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.SS

theorem exists_eq_div_of_isPullback : ∀ (P X Y S : Scheme.{0}) [IsAffine S] (p : P ⟶ X) (q : P ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S), IsPullback p q f g → ∀ (z : P) (U : X.Opens) (U' : Y.Opens) (W : P.Opens), p z ∈ U → q z ∈ U' → z ∈ W → ∃ (V : X.Opens) (V' : Y.Opens) (W' : P.Opens) (h₁ : W' ≤ p ⁻¹ᵁ V) (h₂ : W' ≤ q ⁻¹ᵁ V'), V ≤ U ∧ V' ≤ U' ∧ W' ≤ W ∧ z ∈ W' ∧ ∀ τ : Γ(P, W'), ∃ a ∈ Subring.closure (Set.range (p.appLE V W' h₁).hom ∪ Set.range (q.appLE V' W' h₂).hom), ∃ b ∈ Subring.closure (Set.range (p.appLE V W' h₁).hom ∪ Set.range (q.appLE V' W' h₂).hom), IsUnit a ∧ τ * a = b := by
  intro P X Y S _ p q f g H z U U' W hU hU' hW
  obtain ⟨V, hV, hpV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := U) hU
  obtain ⟨V', hV', hpV', hVU'⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (U := U') hU'
  have hP : IsAffineOpen (p ⁻¹ᵁ V ⊓ q ⁻¹ᵁ V') := by
    have : IsAffine _ := hV
    have : IsAffine _ := hV'
    have : IsAffine _ := isAffineOpen_top S
    exact .of_isIso (Scheme.Hom.isPullback_resLE H (US := ⊤) (UT := V') (UX := V) le_top le_top
      rfl).isoPullback.hom
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := V') (UX := V) le_top le_top rfl).1
    (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _) hV' hV)
  have hgen := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  obtain ⟨r, hrW, hzr⟩ := hP.exists_basicOpen_le (V := W) ⟨z, hW⟩ ⟨hpV, hpV'⟩
  have hle : P.basicOpen r ≤ p ⁻¹ᵁ V ⊓ q ⁻¹ᵁ V' := P.basicOpen_le r
  refine ⟨V, V', P.basicOpen r, hle.trans inf_le_left, hle.trans inf_le_right, hVU, hVU', hrW,
    hzr, fun τ => ?_⟩
  have key : ∀ x : Γ(P, p ⁻¹ᵁ V ⊓ q ⁻¹ᵁ V'), (P.presheaf.map (homOfLE hle).op).hom x ∈
      Subring.closure (Set.range (p.appLE V _ (hle.trans inf_le_left)).hom ∪
        Set.range (q.appLE V' _ (hle.trans inf_le_right)).hom) := by
    intro x
    have hx := hgen.ge (Subring.mem_top x)
    refine Subring.mem_comap.1 (Subring.closure_le.2 ?_ hx)
    rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
    · refine Subring.subset_closure (Or.inl ⟨a, ?_⟩)
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
    · refine Subring.subset_closure (Or.inr ⟨a, ?_⟩)
      rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have hloc := hP.isLocalization_basicOpen r
  obtain ⟨⟨b, a⟩, hab⟩ := IsLocalization.surj (Submonoid.powers r) τ
  exact ⟨_, key a, _, key b, IsLocalization.map_units Γ(P, P.basicOpen r) a, hab⟩

end GlobalTheory.SS
end
