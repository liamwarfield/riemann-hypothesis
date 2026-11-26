module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyDieudonneIntegralityFactorisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitsOfModuliPointHaveIsomorphicProportionalLat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthQuotRangeEqAddValDet
section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthEqTopOfFinrankNeZero
universe u_1 u_2

namespace GlobalTheory.LengthCokernelFinrank

open Module _root_.Submodule IsDiscreteValuationRing

variable {R : Type u_1} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem length_self_eq_top : Module.length R R = ⊤ := by
  have h0 : Module.length R (R ⧸ Ideal.span {(0 : R)}) = ⊤ := by
    have h := Ring.ord_eq_addVal (0 : R)
    rw [addVal_zero] at h
    exact h
  have hle := Module.length_le_of_surjective (Submodule.mkQ (Ideal.span {(0 : R)}))
    (Submodule.mkQ_surjective _)
  rw [h0] at hle
  exact top_le_iff.mp hle

theorem addVal_prod {ι : Type*} (s : Finset ι) (a : ι → R) :
    addVal R (∏ i ∈ s, a i) = ∑ i ∈ s, addVal R (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, addVal_mul, ih]

variable {M : Type u_2} [AddCommGroup M] [Module R M]

theorem length_eq_top_of_finrank_ne_zero [Module.Finite R M] (h : finrank R M ≠ 0) :
    Module.length R M = ⊤ := by
  have hnt : ¬ Module.IsTorsion R M := fun ht => h (Module.finrank_eq_zero_iff_isTorsion.mpr ht)
  have hx : ∃ x : M, ∀ a : R, a • x = 0 → a = 0 := by
    by_contra hc
    push Not at hc
    apply hnt
    intro x
    obtain ⟨a, ha, ha0⟩ := hc x
    exact ⟨⟨a, mem_nonZeroDivisors_of_ne_zero ha0⟩, ha⟩
  obtain ⟨x, hx⟩ := hx
  have hinj : Function.Injective (LinearMap.toSpanSingleton R M x) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    exact hx a (by simpa using ha)
  have hle := Module.length_le_of_injective _ hinj
  rw [length_self_eq_top] at hle
  exact top_le_iff.mp hle

theorem length_coker_eq_addVal_det [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.det f) := by
  classical
  by_cases hk : LinearMap.ker f = ⊥
  · have hinj : Function.Injective f := LinearMap.ker_eq_bot.mp hk
    set N := LinearMap.range f with hN
    let e : M ≃ₗ[R] N := LinearEquiv.ofInjective f hinj
    let b := Module.Free.chooseBasis R M
    have h : finrank R N = finrank R M := e.symm.finrank_eq
    let a := smithNormalFormCoeffs b h
    let b' := smithNormalFormTopBasis b h
    let ab := smithNormalFormBotBasis b h
    let e' : M ≃ₗ[R] N := b'.equiv ab (Equiv.refl _)
    let g : M →ₗ[R] M := N.subtype ∘ₗ (e' : M →ₗ[R] N)
    have hf : f = N.subtype ∘ₗ (e : M →ₗ[R] N) := by
      ext x
      rfl
    have hassoc : Associated (LinearMap.det f) (LinearMap.det g) := by
      have := LinearMap.associated_det_comp_equiv N.subtype e e'
      rwa [← hf] at this
    have hg : ∀ i, g (b' i) = a i • b' i := by
      intro i
      have : e' (b' i) = ab i := by simp [e']
      change ((e' (b' i) : N) : M) = _
      rw [this]
      exact smithNormalFormBotBasis_def b h i
    have hmat : LinearMap.toMatrix b' b' g = Matrix.diagonal a := by
      ext i j
      rw [LinearMap.toMatrix_apply, hg, map_smul, Basis.repr_self, Finsupp.smul_single,
        smul_eq_mul, mul_one, Matrix.diagonal_apply, Finsupp.single_apply]
      by_cases hij : i = j
      · simp [hij]
      · simp [hij, Ne.symm hij]
    have hdet : LinearMap.det g = ∏ i, a i := by
      rw [← LinearMap.det_toMatrix b', hmat, Matrix.det_diagonal]
    rw [(addVal_eq_iff_associated _ _).mpr hassoc, hdet, addVal_prod,
      (quotientEquivPiSpan N b h).length_eq, Module.length_pi_of_fintype]
    exact Finset.sum_congr rfl fun i _ => Ring.ord_eq_addVal (a i)
  · rw [LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk, addVal_zero]
    apply length_eq_top_of_finrank_ne_zero
    intro h0
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
    have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
    rw [(LinearMap.quotKerEquivRange f).finrank_eq] at h2
    have h3 : finrank R (LinearMap.ker f) = 0 := by omega
    exact hk (Submodule.finrank_eq_zero.mp h3)

end GlobalTheory.LengthCokernelFinrank
end

namespace GlobalTheory

open IsDiscreteValuationRing

section CokernelLength

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

theorem length_quot_range_eq_addVal_det {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (f : M →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) = addVal R (LinearMap.det f) := by
  first
  | exact @_root_.GlobalTheory.LengthCokernelFinrank.length_coker_eq_addVal_det
  | exact _root_.GlobalTheory.LengthCokernelFinrank.length_coker_eq_addVal_det
  | (apply _root_.GlobalTheory.LengthCokernelFinrank.length_coker_eq_addVal_det <;> assumption)
  | (intros; apply _root_.GlobalTheory.LengthCokernelFinrank.length_coker_eq_addVal_det <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LengthCokernelFinrank.length_coker_eq_addVal_det <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LengthCokernelFinrank.length_coker_eq_addVal_det ..)

end CokernelLength

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompEqZeroOfNotIsIsogeny
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittVectorColengthRangeEqDetValuation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittVectorColengthRangeEqDetValuation
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu.ColenDet

theorem map_eq_unit_mul_pow {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p]
    (ψ : ℤ_[p] →+* WittVector p k) {x : ℤ_[p]} (hx : x ≠ 0) :
    ψ x = ψ (PadicInt.unitCoeff hx : ℤ_[p]) * (p : WittVector p k) ^ x.valuation := by
  conv_lhs => rw [PadicInt.unitCoeff_spec hx]
  rw [map_mul, map_pow, map_natCast]

theorem addVal_map {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p] [PerfectRing k p]
    (ψ : ℤ_[p] →+* WittVector p k) {x : ℤ_[p]} (hx : x ≠ 0) :
    IsDiscreteValuationRing.addVal (WittVector p k) (ψ x) = (x.valuation : ℕ∞) := by
  rw [map_eq_unit_mul_pow ψ hx, AddValuation.map_mul, AddValuation.map_pow,
    IsDiscreteValuationRing.addVal_uniformizer (WittVector.irreducible p),
    (IsDiscreteValuationRing.addVal_eq_zero_iff).mpr ((PadicInt.unitCoeff hx).isUnit.map ψ)]
  simp

theorem colength_det : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N : Type) [AddCommGroup N] [Module (WittVector p k) N] [Module.Free (WittVector p k) N] [Module.Finite (WittVector p k) N] (ψ : ℤ_[p] →+* (WittVector p k)) (u : N →ₗ[(WittVector p k)] N) (d : ℤ_[p]), LinearMap.det u = ψ d → (∀ e : ℕ, Module.length (WittVector p k) (N ⧸ LinearMap.range u) = e → ‖d‖ = (p : ℝ) ^ (-(e : ℤ))) ∧ (¬ Function.Injective u → d = 0) ∧ Function.Injective ψ := by
  intro p _ k _ _ _ N _ _ _ _ ψ u d hdet
  have hψ : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h0
    have h1 := addVal_map ψ h0
    rw [hx, AddValuation.map_zero] at h1
    exact ENat.top_ne_coe _ h1
  have hlen := GlobalTheory.length_quot_range_eq_addVal_det u
  refine ⟨fun e he => ?_, fun hu => ?_, hψ⟩
  · rw [hlen, hdet] at he
    have hd : d ≠ 0 := by
      rintro rfl
      rw [map_zero, AddValuation.map_zero] at he
      exact ENat.top_ne_coe _ he
    rw [addVal_map ψ hd] at he
    have he' : d.valuation = e := by exact_mod_cast he
    rw [PadicInt.norm_eq_zpow_neg_valuation hd, he']
  · have h0 : LinearMap.det u = 0 := by
      by_contra h
      apply hu
      rwa [LinearMap.det_eq_zero_iff_ker_ne_bot, not_not, LinearMap.ker_eq_bot] at h
    exact hψ (by rw [← hdet, h0, map_zero])

end GlobalTheory.Dieu.ColenDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittVectorColengthRangeEqDetValuationStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittVector_colength_range_eq_det_valuation : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N : Type) [AddCommGroup N] [Module (WittVector p k) N] [Module.Free (WittVector p k) N] [Module.Finite (WittVector p k) N] (ψ : ℤ_[p] →+* (WittVector p k)) (u : N →ₗ[(WittVector p k)] N) (d : ℤ_[p]), LinearMap.det u = ψ d → (∀ e : ℕ, Module.length (WittVector p k) (N ⧸ LinearMap.range u) = e → ‖d‖ = (p : ℝ) ^ (-(e : ℤ))) ∧ (¬ Function.Injective u → d = 0) ∧ Function.Injective ψ := by
  first | exact @GlobalTheory.Dieu.ColenDet.colength_det | exact GlobalTheory.Dieu.ColenDet.colength_det | (intros; apply GlobalTheory.Dieu.ColenDet.colength_det <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

open Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.Dieu.AbsDet

theorem exists_mul_eq_zero_of_not_isUnit {R : Type} [Ring R] [Algebra ℚ R] [Module.Finite ℚ R] (x : R)
    (hx : ¬ IsUnit x) : ∃ y : R, y ≠ 0 ∧ y * x = 0 := by
  by_contra h
  push Not at h
  have hr : Function.Injective (LinearMap.mulRight ℚ x) := by
    intro a b hab
    by_contra hne
    refine h (a - b) (sub_ne_zero.mpr hne) ?_
    rw [sub_mul]
    exact sub_eq_zero.mpr hab
  obtain ⟨y, hy⟩ := (LinearMap.injective_iff_surjective.mp hr) 1
  have hyx : y * x = 1 := hy
  have hl : Function.Injective (LinearMap.mulLeft ℚ x) := by
    intro a b hab
    have hab' : x * a = x * b := hab
    have e : y * (x * a) = y * (x * b) := by rw [hab']
    rwa [← mul_assoc, ← mul_assoc, hyx, one_mul, one_mul] at e
  obtain ⟨z, hz⟩ := (LinearMap.injective_iff_surjective.mp hl) 1
  have hxz : x * z = 1 := hz
  have hyz : y = z := by
    calc y = y * (x * z) := by rw [hxz, mul_one]
      _ = z := by rw [← mul_assoc, hyx, one_mul]
  exact hx ⟨⟨x, y, hyz ▸ hxz, hyx⟩, rfl⟩

theorem norm_natCast_padicInt (p : ℕ) [Fact p.Prime] (n : ℕ) (hn : 0 < n) :
    ‖((n : ℕ) : ℤ_[p])‖ = (p : ℝ) ^ (-(padicValNat p n : ℤ)) := by
  have h1 : ‖((n : ℕ) : ℤ_[p])‖ = ‖((n : ℚ) : ℚ_[p])‖ := by
    rw [PadicInt.norm_def]; push_cast; rfl
  rw [h1, Padic.eq_padicNorm, padicNorm.eq_zpow_of_ne_zero (by exact_mod_cast hn.ne'),
    padicValRat.of_nat, Rat.cast_zpow, Rat.cast_natCast, Nat.padicValNat_def]

theorem exists_comp_eq_zero_of_not_isIsogeny {k : Type} [Field k] (A : AbVar k) (f : End A)
    (hf : ¬ IsIsogeny f.asHom) : ∃ g : End A, g ≠ 0 ∧ f.asHom ≫ g.asHom = 0 := by
  have hfin := (GlobalTheory.T.end_isogeny_algebra_finite_finrank_le k A).1
  have hx : ¬ IsUnit (toEnd0 A f) := by
    rintro ⟨u, hu⟩
    obtain ⟨n, g, hn, hg⟩ := (toEnd0_injective_and_fraction k A).2 (↑u⁻¹ : End0 A)
    have h1 : toEnd0 A (f * g) = toEnd0 A ((n : ℤ) • (1 : End A)) := by
      rw [map_mul, ← hg, ← hu, mul_smul_comm, Units.mul_inv, map_zsmul, map_one, natCast_zsmul]
    have h2 : g.asHom ≫ f.asHom = (n : ℤ) • 𝟙 A := by
      rw [← End.mul_asHom, (toEnd0_injective_and_fraction k A).1 h1]
      exact map_zsmul End.addEquiv (n : ℤ) (1 : End A)
    have hiso : IsIsogeny (g.asHom ≫ f.asHom) := by
      rw [h2]; exact (GlobalTheory.MulIsogeny.mul_isogeny k A n (by exact_mod_cast hn.ne')).1
    exact hf ((isIsogeny_comp_iff_and_deg_comp k A A A g.asHom f.asHom rfl rfl).1.1 hiso).2
  obtain ⟨y, hy0, hyx⟩ := exists_mul_eq_zero_of_not_isUnit _ hx
  obtain ⟨n, g, hn, hg⟩ := (toEnd0_injective_and_fraction k A).2 y
  refine ⟨g, ?_, ?_⟩
  · rintro rfl
    rw [map_zero] at hg
    have h0 : (n : ℚ) • y = 0 := by rw [Nat.cast_smul_eq_nsmul]; exact hg
    have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    apply hy0
    rw [← inv_smul_smul₀ hnq y, h0, smul_zero]
  · have hz : g * f = 0 := by
      apply (toEnd0_injective_and_fraction k A).1
      rw [map_mul, ← hg, smul_mul_assoc, hyx, smul_zero, map_zero]
    simpa only [End.addEquiv_apply, End.mul_asHom, map_zero] using congrArg End.addEquiv hz

theorem norm_det_eq_norm_deg : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (A : AbVar k) (G : PDivGroup p k) (t : G.TorsionTower A.X)
    [Module.Free (WittVector p k) (T.M G)] [Module.Finite (WittVector p k) (T.M G)]
    (ψ : ℤ_[p] →+* (WittVector p k)) (f : End A) (d : ℤ_[p]),
    LinearMap.det (T.map (t.map t f.asHom.hom)) = ψ d → ‖d‖ = ‖((deg f.asHom : ℕ) : ℤ_[p])‖ := by
  intro p _ T k _ _ _ A G t _ _ ψ f d hd
  have hlen := GlobalTheory.T.wittVector_colength_range_eq_det_valuation p k (T.M G) ψ (T.map (t.map t f.asHom.hom)) d hd
  by_cases hf : IsIsogeny f.asHom
  · have hb := (GlobalTheory.T.abelianVariety_dieudonne_integrality_factorisation p T k A A G G t t f.asHom).2.1 hf
    have hpos := (isogeny_flat_finrank k A A f.asHom hf).2.2.1
    rw [hlen.1 _ hb.2, norm_natCast_padicInt p _ hpos]
  · have hdeg : deg f.asHom = 0 := by rw [deg, ite_eq_right hf]
    rw [hdeg, Nat.cast_zero, norm_zero, norm_eq_zero]
    apply hlen.2.1
    intro hinj
    obtain ⟨g, hg0, hfg⟩ := exists_comp_eq_zero_of_not_isIsogeny A f hf
    have hfun := GlobalTheory.T.dieudonneFunctorBase_functor_properties p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
    have hcomp : t.map t f.asHom.hom ≫ t.map t g.asHom.hom = 0 := by
      have e1 : f.asHom.hom ≫ g.asHom.hom = (1 : A.X ⟶ A.X) := by rw [← comp_hom, hfg, zero_hom]
      exact (TorsionTower.map_comp t t t _ _).symm.trans ((t.map_congr t e1).trans (TorsionTower.map_one t t))
    have hne : T.map (t.map t g.asHom.hom) ≠ 0 := by
      intro h0
      apply hg0
      apply End.addEquiv.injective
      rw [map_zero]
      exact (GlobalTheory.T.eq_pow_smul_of_pDivGroup_torsionTower_map p k A A G G t t g.asHom).2
        ((GlobalTheory.T.dieudonne_integrality_and_faithful p T k G G _).2 h0)
    obtain ⟨m, hm⟩ : ∃ m, T.map (t.map t g.asHom.hom) m ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (LinearMap.ext h)
    apply hm
    apply hinj
    have e := hfun.2.1 (t.map t f.asHom.hom) (t.map t g.asHom.hom)
    rw [hcomp, hfun.2.2.2.1] at e
    have e2 := LinearMap.congr_fun e m
    rw [map_zero]
    exact e2.symm.trans rfl

end GlobalTheory.Dieu.AbsDet
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPadicIntCharpolyCommuteFrobeniusSemilinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPadicIntCharpolyCommuteFrobeniusSemilinear
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.DieuCharpoly

open Polynomial

theorem mem_range_zmod_of_pow_eq_self (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]
    (c : k) (hc : c ^ p = c) : c ∈ Set.range ((ZMod.castHom (dvd_refl p) k)) := by
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have hroots := FiniteField.roots_X_pow_card_sub_X (ZMod p)
  rw [ZMod.card p] at hroots
  have hdeg : (X ^ p - X : (ZMod p)[X]).natDegree = p := Polynomial.natDegree_X_pow_sub_X hp
  have hcard : Multiset.card (X ^ p - X : (ZMod p)[X]).roots = (X ^ p - X : (ZMod p)[X]).natDegree := by
    rw [hroots, hdeg, Finset.card_val, Finset.card_univ, ZMod.card]
  have hmap := Polynomial.roots_map_of_injective_of_card_eq_natDegree
    ((ZMod.castHom (dvd_refl p) k)).injective hcard
  have hmem : c ∈ ((X ^ p - X : (ZMod p)[X]).map ((ZMod.castHom (dvd_refl p) k))).roots := by
    rw [Polynomial.mem_roots]
    · simp [hc]
    · simpa using (Polynomial.X_pow_sub_X_ne_zero hp : (X ^ p - X : k[X]) ≠ 0)
  rw [← hmap, hroots, Multiset.mem_map] at hmem
  obtain ⟨a, -, ha⟩ := hmem
  exact ⟨a, ha⟩

theorem exists_map_eq_of_frobenius_eq (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]
    (x : WittVector p k) (hx : WittVector.frobenius x = x) :
    ∃ y : WittVector p (ZMod p), WittVector.map ((ZMod.castHom (dvd_refl p) k)) y = x := by
  have hc : ∀ n, ∃ a : ZMod p, (ZMod.castHom (dvd_refl p) k) a = x.coeff n := by
    intro n
    have h := congrArg (fun z => z.coeff n) hx
    simp only [WittVector.frobenius_eq_map_frobenius, WittVector.map_coeff, frobenius_def] at h
    exact mem_range_zmod_of_pow_eq_self p _ h
  choose a ha using hc
  refine ⟨WittVector.mk p a, ?_⟩
  ext n
  simp [WittVector.map_coeff, ha]

theorem padicInt_ringHom_ext (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]
    [PerfectRing k p] (f g : ℤ_[p] →+* WittVector p k) : f = g := by
  refine RingHom.ext fun x => ?_
  rw [← sub_eq_zero]
  have hI : Ideal.span {(p : WittVector p k)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]; exact (WittVector.irreducible p).not_isUnit
  have h := Ideal.iInf_pow_eq_bot_of_isDomain _ hI
  rw [← Ideal.mem_bot, ← h, Ideal.mem_iInf]
  intro m
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec m x)
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨f y - g y, ?_⟩
  have h1 : x = ((x.appr m : ℕ) : ℤ_[p]) + y * (p : ℤ_[p]) ^ m := by rw [hy]; ring
  rw [h1]
  simp only [map_add (f := _), map_mul, map_pow, map_natCast]
  ring

end GlobalTheory.DieuCharpoly

namespace GlobalTheory.DieuCharpoly

open Polynomial

theorem charpoly_map_eq_of_commute_semilinear {R : Type} [CommRing R] [IsDomain R]
    (σ : R →+* R) (hσ : Function.Surjective σ) (N : Type) [AddCommGroup N] [Module R N]
    [Module.Free R N] [Module.Finite R N] (F : N →ₛₗ[σ] N) (u : N →ₗ[R] N)
    (hF : Function.Injective F) (hu : ∀ x, u (F x) = F (u x)) :
    u.charpoly.map σ = u.charpoly := by
  classical
  let b := Module.Free.chooseBasis R N
  let U := LinearMap.toMatrix b b u
  let Φ : Matrix _ _ R := fun i j => b.repr (F (b j)) i
  have hFrepr : ∀ x i, b.repr (F x) i = ∑ j, Φ i j * σ (b.repr x j) := by
    intro x i
    conv_lhs => rw [← b.sum_repr x]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, LinearMap.map_smulₛₗ, Finset.sum_apply',
      map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hurepr : ∀ y i, b.repr (u y) i = ∑ l, U i l * b.repr y l := by
    intro y i
    rw [← LinearMap.toMatrix_mulVec_repr b b u y]
    rfl
  have hcomm : U * Φ = Φ * U.map σ := by
    refine Matrix.ext fun i j => ?_
    have h := congrArg (fun z => b.repr z i) (hu (b j))
    rw [hurepr, hFrepr] at h
    rw [Matrix.mul_apply, Matrix.mul_apply]
    refine h.trans (Finset.sum_congr rfl fun l _ => ?_)
    rw [Matrix.map_apply, show U l j = b.repr (u (b j)) l from LinearMap.toMatrix_apply b b u l j]
  have hdet : Φ.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    choose w hw using fun j => hσ (v j)
    let x := b.repr.symm (Finsupp.equivFunOnFinite.symm w)
    have hx : ∀ j, b.repr x j = w j := by simp [x]
    have hFx : F x = 0 := by
      apply b.repr.injective
      refine Finsupp.ext fun i => ?_
      rw [hFrepr, map_zero, Finsupp.coe_zero, Pi.zero_apply]
      have := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
      rw [← this]
      exact Finset.sum_congr rfl fun j _ => by rw [hx, hw]
    have hx0 : x = 0 := hF (by rw [hFx, map_zero])
    apply hv0
    funext j
    rw [← hw j, Pi.zero_apply, ← hx j, hx0, map_zero, Finsupp.coe_zero, Pi.zero_apply, map_zero]
  rw [← LinearMap.charpoly_toMatrix u b, ← Matrix.charpoly_map]
  have hm : U.charmatrix * (Polynomial.C : R →+* _).mapMatrix Φ =
      (Polynomial.C : R →+* _).mapMatrix Φ * (U.map σ).charmatrix := by
    rw [Matrix.charmatrix, Matrix.charmatrix, sub_mul, mul_sub, ← map_mul, hcomm, map_mul,
      (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).eq]
  have hd := congrArg Matrix.det hm
  rw [Matrix.det_mul, Matrix.det_mul, ← RingHom.map_det] at hd
  have hC : Polynomial.C Φ.det ≠ 0 := Polynomial.C_ne_zero.2 hdet
  rw [mul_comm] at hd
  exact (mul_left_cancel₀ hC hd).symm

end GlobalTheory.DieuCharpoly

namespace GlobalTheory.DieuCharpoly

open Polynomial

theorem exists_monic_map_eq_charpoly : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (N : Type) [AddCommGroup N] [Module (WittVector p k) N]
    [Module.Free (WittVector p k) N] [Module.Finite (WittVector p k) N]
    (F : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] N)
    (ψ : ℤ_[p] →+* (WittVector p k)) (u : N →ₗ[(WittVector p k)] N),
    Function.Injective F → (∀ x, u (F x) = F (u x)) →
      ∃ P : Polynomial ℤ_[p], P.Monic ∧ P.map ψ = u.charpoly := by
  intro p _ k _ _ _ N _ _ _ _ F ψ u hF hu
  have hfix := charpoly_map_eq_of_commute_semilinear _
    (WittVector.frobenius_bijective p k).surjective N F u hF hu
  have hψ : ψ = (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp
      (WittVector.equiv p).symm.toRingHom := padicInt_ringHom_ext p _ _
  have hl : u.charpoly ∈ Polynomial.lifts ψ := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    have h : WittVector.frobenius (u.charpoly.coeff n) = u.charpoly.coeff n := by
      conv_rhs => rw [← hfix]
      rw [Polynomial.coeff_map]
    obtain ⟨y, hy⟩ := exists_map_eq_of_frobenius_eq p _ h
    refine ⟨WittVector.equiv p y, ?_⟩
    rw [hψ, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
      RingEquiv.symm_apply_apply, hy]
  obtain ⟨P, hP, -, hPm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (LinearMap.charpoly_monic u)
  exact ⟨P, hPm, hP⟩

end GlobalTheory.DieuCharpoly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPadicIntCharpolyCommuteFrobeniusSemilinearStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicInt_charpoly_commute_frobeniusSemilinear : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (N : Type) [AddCommGroup N] [Module (WittVector p k) N] [Module.Free (WittVector p k) N] [Module.Finite (WittVector p k) N] (F : N →ₛₗ[(WittVector.frobenius : WittVector p k →+* WittVector p k)] N) (ψ : ℤ_[p] →+* (WittVector p k)) (u : N →ₗ[(WittVector p k)] N), Function.Injective F → (∀ x, u (F x) = F (u x)) → ∃ P : Polynomial ℤ_[p], P.Monic ∧ P.map ψ = u.charpoly := by
  first | exact @GlobalTheory.DieuCharpoly.exists_monic_map_eq_charpoly | exact GlobalTheory.DieuCharpoly.exists_monic_map_eq_charpoly | (intros; apply GlobalTheory.DieuCharpoly.exists_monic_map_eq_charpoly; all_goals assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdAevalPadicRootsCharpolyEqDet
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdAevalPadicRootsCharpolyEqDet
namespace GlobalTheory
open Polynomial

theorem aeval_int_eq_eval₂ {A : Type} [Ring A] [inst : Algebra ℤ A] (x : A) (R : ℤ[X]) :
    @aeval ℤ A _ _ inst x R = eval₂ (Int.castRingHom A) x R := by
  rw [aeval_def]
  congr 1
  exact RingHom.ext_int _ _

theorem prod_aeval_aroots_padic_eq_det : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [IsDomain S] (N : Type) [AddCommGroup N] [Module S N] [Module.Free S N] [Module.Finite S N] (ψ : ℤ_[p] →+* S) (u : N →ₗ[S] N) (P : Polynomial ℤ_[p]) (R : Polynomial ℤ) (d : ℤ_[p]), Function.Injective ψ → P.map ψ = u.charpoly → LinearMap.det (Polynomial.aeval u R) = ψ d → (((P.map (algebraMap ℤ_[p] ℚ_[p])).aroots (PadicAlgCl p)).map (fun a => Polynomial.aeval a R)).prod = algebraMap ℚ_[p] (PadicAlgCl p) (d : ℚ_[p]) := by
  intro p _ S _ _ N _ _ _ _ ψ u P R d hψ hP hd
  let K := FractionRing S
  have hg : Function.Injective ((algebraMap S K).comp ψ) :=
    (IsFractionRing.injective S K).comp hψ
  let ψ' : ℚ_[p] →+* K := IsFractionRing.lift hg
  have hψ' : ψ'.comp (algebraMap ℤ_[p] ℚ_[p]) = (algebraMap S K).comp ψ :=
    IsLocalization.lift_comp _
  let Ω := AlgebraicClosure K
  letI : Algebra ℚ_[p] Ω := ((algebraMap K Ω).comp ψ').toAlgebra
  have hΩ : algebraMap ℚ_[p] Ω = (algebraMap K Ω).comp ψ' := rfl
  let j : PadicAlgCl p →ₐ[ℚ_[p]] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hj : Function.Injective j := j.toRingHom.injective
  let uK : Module.End K (TensorProduct S K N) := u.baseChange K
  have key := GlobalTheory.T.det_aeval_eq_prod_aroots_charpoly' K Ω (TensorProduct S K N) uK (R.map (Int.castRingHom K))
  have hF : ∀ {A : Type} [Ring A] [Algebra K A] (x : A), aeval x (R.map (Int.castRingHom K)) = aeval x R := by
    intro A _ _ x
    rw [← algebraMap_int_eq, aeval_map_algebraMap]
  simp only [hF] at key
  have hbc : aeval uK R = (aeval u R).baseChange K := by
    have := aeval_algHom_apply (Module.End.baseChangeHom S K N).toRingHom.toIntAlgHom u R
    exact this
  rw [hbc, LinearMap.det_baseChange, hd] at key
  have hch : uK.charpoly.aroots Ω = (P.map (algebraMap ℤ_[p] ℚ_[p])).aroots Ω := by
    rw [LinearMap.charpoly_baseChange, ← hP, aroots_def, aroots_def, map_map, map_map, map_map, hΩ]
    simp only [RingHom.comp_assoc, hψ']
  rw [hch] at key
  apply hj
  set Q := P.map (algebraMap ℤ_[p] ℚ_[p])
  have hroots : Q.aroots Ω = (Q.aroots (PadicAlgCl p)).map j := by
    have h := (IsAlgClosed.splits (Q.map (algebraMap ℚ_[p] (PadicAlgCl p)))).roots_map (j : PadicAlgCl p →+* Ω)
    rw [map_map, AlgHom.comp_algebraMap] at h
    rw [aroots_def, aroots_def, h]
    rfl
  rw [hroots, Multiset.map_map] at key
  rw [map_multiset_prod, Multiset.map_map, AlgHom.commutes]
  simp only [aeval_int_eq_eval₂] at key ⊢
  have e1 : ∀ a : PadicAlgCl p, j (eval₂ (Int.castRingHom _) a R) = eval₂ (Int.castRingHom Ω) (j a) R := by
    intro a
    change (j : PadicAlgCl p →+* Ω) (eval₂ (Int.castRingHom _) a R) = _
    rw [Polynomial.hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _
  simp only [Function.comp_def, e1] at key ⊢
  refine key.symm.trans ?_
  rw [hΩ, RingHom.comp_apply]
  congr 1
  exact (RingHom.congr_fun hψ' d).symm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdAevalPadicRootsCharpolyEqDetStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_aeval_padicRoots_charpoly_eq_det : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [IsDomain S] (N : Type) [AddCommGroup N] [Module S N] [Module.Free S N] [Module.Finite S N] (ψ : ℤ_[p] →+* S) (u : N →ₗ[S] N) (P : Polynomial ℤ_[p]) (R : Polynomial ℤ) (d : ℤ_[p]), Function.Injective ψ → P.map ψ = u.charpoly → LinearMap.det (Polynomial.aeval u R) = ψ d → (((P.map (algebraMap ℤ_[p] ℚ_[p])).aroots (PadicAlgCl p)).map (fun a => Polynomial.aeval a R)).prod = algebraMap ℚ_[p] (PadicAlgCl p) (d : ℚ_[p]) := by
  first | exact @GlobalTheory.prod_aeval_aroots_padic_eq_det | exact GlobalTheory.prod_aeval_aroots_padic_eq_det | (intros; apply GlobalTheory.prod_aeval_aroots_padic_eq_det <;> assumption)
end
end

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory

open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Dieu.CharpolyAV

section Rho

variable {p : ℕ} [Fact p.Prime] (T : Theory p) {k : Type} [Field k] [CharP k p] [PerfectRing k p]
  {A : AbVar k} {G : PDivGroup p k} (t : G.TorsionTower A.X)

def rho : End A →+ Module.End (WittVector p k) (T.M G) :=
  AddMonoidHom.mk' (fun g => T.map (t.map t g.asHom.hom)) fun g h => by
    have hfun := base_functor_props p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
    haveI : IsMonHom (g.asHom.hom * h.asHom.hom) := inferInstanceAs (IsMonHom (g + h).asHom.hom)
    show T.map (t.map t (g.asHom.hom * h.asHom.hom)) = _
    rw [TorsionTower.map_mul]
    exact hfun.2.2.1 _ _

theorem rho_apply (g : End A) : rho T t g = T.map (t.map t g.asHom.hom) := rfl

theorem rho_pow (f : End A) (n : ℕ) : rho T t (f ^ n) = rho T t f ^ n := by
  have hfun := base_functor_props p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, rho_apply]
    show T.map (t.map t (𝟙 A.X)) = _
    rw [TorsionTower.map_id]
    exact hfun.1
  | succ n ih =>
    rw [pow_succ, pow_succ', ← ih, rho_apply, rho_apply, rho_apply]
    show T.map (t.map t (f.asHom.hom ≫ (f ^ n).asHom.hom)) = _
    rw [TorsionTower.map_comp t t t]
    exact hfun.2.1 _ _

theorem rho_aeval (f : End A) (R : Polynomial ℤ) :
    rho T t (Polynomial.aeval f R) = Polynomial.aeval (rho T t f) R := by
  induction R using Polynomial.induction_on' with
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
  | monomial n a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, eq_intCast (algebraMap ℤ (End A)),
      eq_intCast (algebraMap ℤ (Module.End (WittVector p k) (T.M G))), ← zsmul_eq_mul, ← zsmul_eq_mul, map_zsmul, rho_pow]

end Rho

theorem charpoly_map_eq : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (A : AbVar k) (G : PDivGroup p k) (t : G.TorsionTower A.X)
    [Module.Free (WittVector p k) (T.M G)] [Module.Finite (WittVector p k) (T.M G)] (f : End A),
    (T.map (t.map t f.asHom.hom)).charpoly = (GlobalTheory.AV.AbVar.charpoly f).map (Int.castRingHom (WittVector p k)) := by
  intro p _ T k _ _ _ A G t _ _ f
  have hfun := base_functor_props p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
  have hFc : ∀ (g : End A) (x : T.M G), T.map (t.map t g.asHom.hom) (T.F G x) = T.F G (T.map (t.map t g.asHom.hom) x) :=
    fun g x => hfun.2.2.2.2.2.2.1 _ x
  have hFinj : Function.Injective (T.F G) := (GlobalTheory.T.dieudonneTheory_V_eq_verschiebung_injective p T k G).1
  let ψ : ℤ_[p] →+* WittVector p k :=
    (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp (WittVector.equiv p).symm.toRingHom
  have hψ : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0
    rw [PadicInt.unitCoeff_spec hx0, map_mul, map_pow, map_natCast] at hx
    have hu : IsUnit (ψ (PadicInt.unitCoeff hx0 : ℤ_[p])) := (Units.isUnit _).map ψ
    have hpn : ((p : WittVector p k)) ^ x.valuation ≠ 0 := pow_ne_zero _ (WittVector.p_nonzero p k)
    exact hpn ((hu.mul_right_eq_zero).1 hx)
  have hrank : Module.finrank (WittVector p k) (T.M G) = 2 * A.dim :=
    hfun.2.2.2.2.2.2.2.1.trans ((GlobalTheory.T.exists_torsionTower_and_height_eq_two_dim p k A).2 G t)
  obtain ⟨P, hPm, hP⟩ := GlobalTheory.T.exists_padicInt_charpoly_commute_frobeniusSemilinear p k (T.M G) (T.F G) ψ (T.map (t.map t f.asHom.hom)) hFinj (hFc f)
  obtain ⟨⟨hQm, hQdeg, -⟩, -⟩ := GlobalTheory.T.abelianVarietyEndCharpoly_spec k A f
  have hPdeg : P.natDegree = 2 * A.dim := by
    rw [← hPm.natDegree_map ψ, hP, LinearMap.charpoly_natDegree, hrank]
  have key : P.map (algebraMap ℤ_[p] ℚ_[p]) = (charpoly f).map (Int.castRingHom ℚ_[p]) := by
    refine GlobalTheory.T.eq_of_norm_prod_aeval_eq' p _ _ (hPm.map _) (hQm.map _) ?_ ?_
    · rw [hPm.natDegree_map, hQm.natDegree_map, hPdeg, hQdeg]
    · intro R
      obtain ⟨PR, -, hPR⟩ := GlobalTheory.T.exists_padicInt_charpoly_commute_frobeniusSemilinear p k (T.M G) (T.F G) ψ
        (T.map (t.map t (Polynomial.aeval f R).asHom.hom)) hFinj (hFc _)
      set d : ℤ_[p] := (-1) ^ Module.finrank (WittVector p k) (T.M G) * PR.coeff 0 with hd_def
      have hd : LinearMap.det (T.map (t.map t (Polynomial.aeval f R).asHom.hom)) = ψ d := by
        rw [LinearMap.det_eq_sign_charpoly_coeff, ← hPR, Polynomial.coeff_map, hd_def, map_mul, map_pow,
          map_neg, map_one]
      have habs := GlobalTheory.Dieu.AbsDet.norm_det_eq_norm_deg p T k A G t ψ (Polynomial.aeval f R) d hd
      have hd' : LinearMap.det (Polynomial.aeval (T.map (t.map t f.asHom.hom)) R) = ψ d := by
        rw [← hd]; exact congrArg LinearMap.det (rho_aeval T t f R).symm
      rw [GlobalTheory.T.prod_aeval_padicRoots_charpoly_eq_det p (WittVector p k) (T.M G) ψ _ P R d hψ hP hd']
      have hQ : (charpoly f).map (Int.castRingHom ℚ_[p]) =
          ((charpoly f).map (Int.castRingHom ℚ)).map (algebraMap ℚ ℚ_[p]) := by
        rw [Polynomial.map_map]; congr 1 <;> exact RingHom.ext_int _ _
      have h2 := GlobalTheory.T.deg_aeval_end_eq_prod_aroots k A f (PadicAlgCl p) R
      rw [hQ, Polynomial.aroots_map]
      erw [← h2]
      rw [PadicAlgCl.norm_extends, map_natCast, ← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)), PadicAlgCl.norm_extends]
      rw [PadicInt.padic_norm_e_of_padicInt, habs]
      rw [← PadicInt.padic_norm_e_of_padicInt]; push_cast; rfl
  have hP' : P = (charpoly f).map (Int.castRingHom ℤ_[p]) := by
    apply Polynomial.map_injective (algebraMap ℤ_[p] ℚ_[p]) (IsFractionRing.injective ℤ_[p] ℚ_[p])
    rw [key, Polynomial.map_map]; congr 1 <;> exact RingHom.ext_int _ _
  rw [← hP, hP', Polynomial.map_map]; congr 1 <;> exact RingHom.ext_int _ _

end GlobalTheory.Dieu.CharpolyAV
