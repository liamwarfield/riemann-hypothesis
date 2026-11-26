module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnTorusComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodPartMemTautologicalPointTorsion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBaseEqOfMatchingPullbacks

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerObjectCompleteDVRBothMaps
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyLatticeIdentificationEqId
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSelfOfConeCongMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.eq_self_of_cone_congMod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (φ : InvFun (𝓞 E)) (q : ℕ), IsPolFan H.bar q φ → NoSelfInt H.bar q φ → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] [Module.Finite (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsCone H.bar φ δ → (∀ y, y ≠ 0 → 0 < ∑ i, δ i y y) → ∀ (u : X ≃ₗ[𝓞 E] X) (a a' : Fin m → ℕ), (∀ i, 0 < a i) → (∀ i, 0 < a' i) → (∀ y z, ∑ i, (a i : ℤ) * δ i (u y) (u z) = ∑ i, (a' i : ℤ) * δ i y z) → ∀ N : ℕ, 3 ≤ N → (∀ y, ∃ z, u y = y + N • z) → ∀ y, u y = y := by
  intro E _ _ _ H φ q hfan hno X _ _ _ _ _ hX m δ hδ hdef u a a' ha ha' hsum N hN hcong
  haveI : Module.Projective (𝓞 E) X := GlobalTheory.Forms.projective_of_int (𝓞 E) X
  have hon : IsPolFanOn H.bar φ X := hfan X hX
  have hu : IsCone H.bar φ fun i => pull u.toLinearMap (δ i) := hδ.pull_equiv u
  have heq : ∑ j, a j • pull u.toLinearMap (δ j) = ∑ j, a' j • δ j := LinearMap.ext₂ fun y z => by
    simpa [LinearMap.sum_apply, nsmul_eq_mul] using hsum y z
  have hfix : ∀ j, pull u.toLinearMap (δ j) = δ j := by
    intro j
    obtain ⟨j', hj'⟩ := GlobalTheory.Poinc.intCone_face (𝓞 E) H.bar φ X hon _ _ _ δ hu hδ a a' ha heq j
    obtain rfl := hno X hX m δ hδ u j j' hj'
    exact hj'
  have hβ : ∀ y z, (∑ i, δ i) (u y) (u z) = (∑ i, δ i) y z := fun y z => by
    simp only [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => LinearMap.congr_fun₂ (hfix i) y z
  have he := GlobalTheory.Poinc.eq_refl_of_isometry_congMod X (∑ i, δ i)
    (fun y hy => by simpa [LinearMap.sum_apply] using hdef y hy) (u.restrictScalars ℤ) (fun y z => hβ y z) N hN
    (fun y => hcong y)
  intro y
  exact LinearEquiv.congr_fun he y
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyLatticeIdentificationEqId
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.LatId

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem second_diff_bal {X Y K I : Type} [AddCommGroup X] [Module (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y] [Field K]
    [Fintype I] (e : X ≃ₗ[𝓞 E] Y) (s : I → K) (hs : ∀ k, s k ≠ 0) (ε : I → LinearMap.BilinForm ℤ Y)
    (hε : ∀ k, ε k ∈ balForms H.bar Y) (n : ℤ) (g : X → Kˣ)
    (hg : ∀ y, (((g y)⁻¹ : Kˣ) : K) = ∏ k, s k ^ (n * ε k (e y) (H.w0 • e y))) (a a' : X) :
    (((g (a + a'))⁻¹ * g a * g a' : Kˣ) : K) = ∏ k, s k ^ (n * ε k (e a) (e a')) := by
  have hw : H.w0 + H.bar H.w0 = 1 := GlobalTheory.PelPrim.cmHostUnit_add_conj_eq_one H
  have hg' : ∀ y, (g y : K) = (∏ k, s k ^ (n * ε k (e y) (H.w0 • e y)))⁻¹ := fun y => by
    rw [← hg, Units.val_inv_eq_inv_val, inv_inv]
  rw [Units.val_mul, Units.val_mul, hg, hg', hg', ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_neg, ← zpow_neg, ← zpow_add₀ (hs k), ← zpow_add₀ (hs k)]
  congr 1
  have h1 : ε k (e a') (H.w0 • e a) = ε k (e a) (H.bar H.w0 • e a') := by rw [(hε k).1, (hε k).2]
  have h2 : ε k (e a) (H.w0 • e a') + ε k (e a) (H.bar H.w0 • e a') = ε k (e a) (e a') := by
    rw [← map_add (f := _), ← add_smul, hw, one_smul]
  simp only [map_add (f := _), smul_add, LinearMap.add_apply, h1]
  rw [← h2]
  ring


set_option maxHeartbeats 1000000 in
theorem lattice_eq_id : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f₁ f₂ : R →+* V, Function.Injective f₁ → Function.Injective f₂ → IsLocalHom f₁ → IsLocalHom f₂ → ∀ (D₁ D₂ : DegData V (maximalIdeal V)) (hD₁ : IsPullDeg f₁ C.P.D.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ C.P.D.toPre D₂.toPre) (j₁ j₂ : (AlgebraicClosure (FractionRing R)) →+* (AlgebraicClosure (FractionRing V))) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ' : D₁.toPre.X ≃+ D₂.toPre.X), GlobalTheory.TInj.Ext f₁ j₁ → GlobalTheory.TInj.Ext f₂ j₂ → GlobalTheory.TInj.Match D₁.toPre D₂.toPre b φ' (AlgebraicClosure (FractionRing V)) → (∀ (x : 𝓞 E) (y : C.P.D.toPre.X), hD₂.xe (φ' (hD₁.xe.symm (x • y))) = x • hD₂.xe (φ' (hD₁.xe.symm y))) → (∀ p₀ : QkPt C.P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) l.M') (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) l.M'), p₁.y = hD₁.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ GlobalTheory.TInj.QImg b φ' p₁ p₂) → ∀ y : C.P.D.toPre.X, hD₂.xe (φ' (hD₁.xe.symm y)) = y := by
  intro E _ _ _ H Dw l Xo c φ hpq hφ hns R _ _ _ hR C Cn V _ _ _ _ hVc f₁ f₂ hf₁ hf₂ lf₁ lf₂ D₁ D₂ hD₁ hD₂ j₁ j₂ b ph hE₁ hE₂
    hM hlin hpairs
  letI := H.starRing
  have hn : 3 ≤ l.M' := l.three_le.trans (Nat.le_of_dvd (Nat.lcm_pos (by have := l.three_le; omega) l.A_pos)
    (Nat.dvd_lcm_left _ _))
  have hn1 : 1 ≤ l.M' := by omega
  set iw := Cn.ψ.comp MvPolynomial.C with hiwd
  have hiw : Function.Injective iw := by
    have hfl : iw.Flat := RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 inferInstance) Cn.compl.2.2.1
    letI := iw.toAlgebra
    have : Module.Flat Cn.L.W R := hfl
    have : IsLocalHom (algebraMap Cn.L.W R) := Cn.ψ_loc
    have : Module.FaithfullyFlat Cn.L.W R := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective Cn.L.W R
  let s : Fin C.m ⊕ Fin Cn.N → R := fun k => Cn.ψ (MvPolynomial.X k)
  have hs0 : ∀ k, s k ≠ 0 := by
    rintro (k | k)
    · exact (Cn.bd k).trans_ne (C.s_ne_zero k)
    · exact (Cn.tor k).ne_zero
  obtain ⟨hev, hbi, hgen, -⟩ := GlobalTheory.T.degenerationDataNsmulRescale_keeps_laws Cn.L.W Cn.L.D (𝓞 E) Cn.L.oa H.w0 l.M' Cn.L.even Cn.L.bimult Cn.L.w0 Cn.L.gen
  obtain ⟨T, ib, β₀, ββ₀, w₀, hF₀⟩ := GlobalTheory.T.exists_tautologicalBase_nsmul_degenerationData Cn.L.b Cn.L.D Cn.L.bimult Cn.L.gen l.M'
  obtain ⟨g, hD, hg, hxe, -⟩ := Cn.data
  let ε : Fin C.m ⊕ Fin Cn.N → LinearMap.BilinForm ℤ (Fin T.r → ℤ) := fun k =>
    (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X).compl₁₂ ib.symm.toIntLinearEquiv.toLinearMap ib.symm.toIntLinearEquiv.toLinearMap
  have hε : ∀ k a b, ε k (ib a) (ib b) = (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) a b := fun k a b =>
    congrArg₂ (fun x y => (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) x y) (ib.symm_apply_apply a) (ib.symm_apply_apply b)
  let e : C.P.D.toPre.X ≃+ (Fin T.r → ℤ) := Cn.e.toAddEquiv.trans ib
  have he : ∀ y, e y = ib (Cn.e y) := fun _ => rfl
  obtain ⟨β, ββ, w, hF⟩ := GlobalTheory.T.comesFromTautBase_of_rescaled_pullback_monomial T l.M' (mulDeg Cn.L.D l.M') hev hbi hgen ib β₀ ββ₀ w₀ hF₀ R iw hiw C.P.D.toPre g hD
    s ε e (fun y => congrArg ib (hxe y).symm) (fun a a' => by
      simp only [he, hε]
      exact second_diff_bal Cn.e _ (fun k => (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (hs0 k)) _
        (fun k => (Cn.ε k).2) _ g hg a a')
  obtain ⟨ββ₁, w₁, hF₁⟩ := GlobalTheory.TInj.from_pull T ε l.M' R V _ C.P.D iw s e β ββ w f₁ D₁.toPre hD₁ hf₁ hF
  obtain ⟨ββ₂, w₂, hF₂⟩ := GlobalTheory.TInj.from_pull T ε l.M' R V _ C.P.D iw s e β ββ w f₂ D₂.toPre hD₂ hf₂ hF

  let ga : C.P.D.toPre.X ≃ₗ[𝓞 E] C.P.D.toPre.X :=
    { (hD₁.xe.symm.trans ph).trans hD₂.xe with map_smul' := hlin }
  have hga : ∀ y, ga y = hD₂.xe (ph (hD₁.xe.symm y)) := fun _ => rfl

  have hcong : ∀ y, ∃ z, ga y = y + l.M' • z := by
    intro y
    obtain ⟨p₀, hp₀y, -⟩ := GlobalTheory.TInj.exists_qkPt_tautPt T ε l.M' R C.P.D.toPre iw s e β ββ w C.P.D.tau_bimult hF hs0
      (AlgebraicClosure (FractionRing R)) (e y)
    obtain ⟨p₁, p₂, hy₁, -, hy₂, -, p', hp', -, z, hz, -⟩ := hpairs p₀
    rw [hp₀y, AddEquiv.symm_apply_apply] at hy₁ hy₂
    have h : hD₂.xe p₂.y = hD₂.xe (ph p₁.y) + l.M' • hD₂.xe z := by rw [hz, map_add (f := _), hp', map_nsmul]
    rw [hy₂, hy₁, AddEquiv.apply_symm_apply] at h
    refine ⟨-(hD₂.xe z), ?_⟩
    rw [smul_neg, hga, ← sub_eq_add_neg, eq_sub_iff_add_eq]
    exact h.symm

  have hbd : ∀ f : R →+* V, Function.Injective f → IsLocalHom f → ∀ k, f (s (.inl k)) ∈ maximalIdeal V ∧ f (s (.inl k)) ≠ 0 :=
    fun f hf hl k => ⟨map_nonunit f _ (show Cn.ψ _ ∈ maximalIdeal R from (Cn.bd k).symm ▸ C.s_mem k),
      (map_ne_zero_iff f hf).2 (hs0 _)⟩
  have hpu := GlobalTheory.T.tautologicalBase_matching_monomials_ratio_unit T ε l.M' V D₁.toPre D₂.toPre _ _ _ _ ββ₁ w₁ _ _ _ _ ββ₂ w₂ b ph _ D₁.tau_bimult D₂.tau_bimult
    hF₁ hF₂ hM
  let gz : (Fin T.r → ℤ) ≃ₗ[ℤ] (Fin T.r → ℤ) := ((e.symm.trans ga.toAddEquiv).trans e).toIntLinearEquiv
  have hgz : ∀ y, gz (e y) = e (ga y) := fun y => by
    show e (ga (e.symm (e y))) = e (ga y)
    rw [AddEquiv.symm_apply_apply]
  obtain ⟨d₁, d₂, hd₁, hd₂, hsum⟩ := GlobalTheory.T.monomials_differ_by_units_positive_boundaryCombination V T.r C.m Cn.N l.M' hn1 ε (fun k => f₁ (s k)) (fun k => f₂ (s k))
    gz (hbd f₁ hf₁ lf₁) (fun k => (Cn.tor k).map f₁) (hbd f₂ hf₂ lf₂)
    (fun k => (Cn.tor k).map f₂) (fun a a' => by
      obtain ⟨u, hu⟩ := hpu (hD₁.xe.symm (e.symm a)) (hD₁.xe.symm (e.symm a'))
      simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply] at hu
      exact ⟨u, hu⟩)
  have hδ : ∀ k a a', C.δ k a a' = ε (.inl k) (e a) (e a') := fun k a a' => by rw [he, he, hε, Cn.cone]; rfl
  have hform : ∀ y z, ∑ i, (d₂ i : ℤ) * C.δ i (ga y) (ga z) = ∑ i, (d₁ i : ℤ) * C.δ i y z := by
    intro y z
    have h := LinearMap.congr_fun₂ hsum (e y) (e z)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, pull_apply, LinearEquiv.coe_coe, hgz, nsmul_eq_mul] at h
    simp only [hδ]
    exact h.symm
  have hpos : ∀ y, y ≠ 0 → 0 < ∑ i, C.δ i y y := by
    intro y hy
    obtain ⟨i, hi⟩ := C.mono.exists_pos (maximalIdeal.isMaximal _).ne_top hy
    have hi' : 0 < C.δ i y y :=
      (mul_pos_iff_of_pos_left (show (0 : ℤ) < l.M' by exact_mod_cast (by omega : 0 < l.M'))).1 hi
    exact Finset.sum_pos' (fun j _ => C.cone.nonneg j y) ⟨i, Finset.mem_univ _, hi'⟩
  have hid := GlobalTheory.UCanon.eq_self_of_cone_congMod H φ (min Dw.p Dw.q) hφ hns C.P.D.toPre.X C.rank C.m C.δ C.cone hpos ga
    d₂ d₁ hd₂ hd₁ hform l.M' hn hcong
  intro y
  exact hid y

end GlobalTheory.UCanon.LatId
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyLatticeIdentificationEqIdStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalFamily_latticeIdentification_eq_id : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f₁ f₂ : R →+* V, Function.Injective f₁ → Function.Injective f₂ → IsLocalHom f₁ → IsLocalHom f₂ → ∀ (D₁ D₂ : DegData V (maximalIdeal V)) (hD₁ : IsPullDeg f₁ C.P.D.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ C.P.D.toPre D₂.toPre) (j₁ j₂ : (AlgebraicClosure (FractionRing R)) →+* (AlgebraicClosure (FractionRing V))) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ' : D₁.toPre.X ≃+ D₂.toPre.X), GlobalTheory.TInj.Ext f₁ j₁ → GlobalTheory.TInj.Ext f₂ j₂ → GlobalTheory.TInj.Match D₁.toPre D₂.toPre b φ' (AlgebraicClosure (FractionRing V)) → (∀ (x : 𝓞 E) (y : C.P.D.toPre.X), hD₂.xe (φ' (hD₁.xe.symm (x • y))) = x • hD₂.xe (φ' (hD₁.xe.symm y))) → (∀ p₀ : QkPt C.P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) l.M') (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) l.M'), p₁.y = hD₁.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ GlobalTheory.TInj.QImg b φ' p₁ p₂) → ∀ y : C.P.D.toPre.X, hD₂.xe (φ' (hD₁.xe.symm y)) = y := by
  first | exact @GlobalTheory.UCanon.LatId.lattice_eq_id | exact GlobalTheory.UCanon.LatId.lattice_eq_id | (intros; apply GlobalTheory.UCanon.LatId.lattice_eq_id <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompBEq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UCanon.LowPull

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_pull {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (A : Type) [CommRing A]
    (f : L.W →+* A) :
    ∃ (o' : LowObj D' c (f.comp L.b)) (m : ObjMap o' L.o (spMap f)) (x : L.D.X → (Sp A ⟶ o'.t.G.left)),
      (∀ y, x y ≫ m.toSABMap.φ ≫ L.φB = spMap f ≫ (L.D.c y).left) ∧ ∀ y, x y ≫ o'.t.G.hom = 𝟙 _ := by
  have hs : lowMap c (f.comp L.b) = spMap f ≫ lowMap c L.b := by
    simp only [lowMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨o', ⟨m⟩⟩ := (GlobalTheory.UCanon.obj_pull_comp_cancel (D := D') (l := LowDat.lowLevel l)).1
    (lowMap c L.b) L.o (spMap f) (lowMap c (f.comp L.b)) hs
  have hB := L.ab.1.1
  have u : ∀ y, ∃ u : Sp L.W ⟶ L.o.t.G.left, u ≫ L.φB = (L.D.c y).left ∧ u ≫ L.o.t.G.hom = 𝟙 _ := by
    intro y
    refine ⟨hB.lift (L.D.c y).left (𝟙 _) ?_, hB.lift_fst _ _ _, hB.lift_snd _ _ _⟩
    simpa using Over.w (L.D.c y)
  choose u hu₁ hu₂ using u
  have hm := m.toSABMap.cart.1
  refine ⟨o', m, fun y => hm.lift (spMap f ≫ u y) (𝟙 _) ?_, fun y => ?_, fun y => hm.lift_snd _ _ _⟩
  · rw [Category.assoc, hu₂, Category.comp_id, Category.id_comp]
  · rw [← Category.assoc, hm.lift_fst, Category.assoc, hu₁]

theorem exists_pull₂ {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (A : Type) [CommRing A]
    (f₁ f₂ : L.W →+* A) (h : f₁ = f₂) :
    ∃ (o' : LowObj D' c (f₁.comp L.b)) (m₁ : ObjMap o' L.o (spMap f₁)) (m₂ : ObjMap o' L.o (spMap f₂))
      (x : L.D.X → (Sp A ⟶ o'.t.G.left)),
      (∀ y, x y ≫ m₁.toSABMap.φ ≫ L.φB = spMap f₁ ≫ (L.D.c y).left) ∧
      (∀ y, x y ≫ m₂.toSABMap.φ ≫ L.φB = spMap f₂ ≫ (L.D.c y).left) ∧ ∀ y, x y ≫ o'.t.G.hom = 𝟙 _ := by
  subst h
  obtain ⟨o', m, x, hx, hxs⟩ := exists_pull L A f₁
  exact ⟨o', m, m, x, hx, hx, hxs⟩

end GlobalTheory.UCanon.LowPull

namespace GlobalTheory.UCanon.LowPull
theorem comp_b_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (F : Fam Xo c R)
    {V : Type} [CommRing V] [IsDomain V] (θ₁ θ₂ : R →+* V) (κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R))
    (h₁ : κ₁ ≫ jK R = jK V ≫ spMap θ₁) (h₂ : κ₂ ≫ jK R = jK V ≫ spMap θ₂) (hy : κ₁ ≫ F.y = κ₂ ≫ F.y) :
    θ₁.comp F.b = θ₂.comp F.b := by
  have key : ∀ (θ : R →+* V) (κ : Sp (FractionRing V) ⟶ Sp (FractionRing R)), κ ≫ jK R = jK V ≫ spMap θ →
      jK V ≫ spMap (θ.comp F.b) = κ ≫ F.y ≫ pullback.snd _ _ := by
    intro θ κ h
    rw [F.y_over, ← Category.assoc, h, Category.assoc, spMap_comp]
  have e : jK V ≫ spMap (θ₁.comp F.b) = jK V ≫ spMap (θ₂.comp F.b) := by
    rw [key θ₁ κ₁ h₁, key θ₂ κ₂ h₂, ← Category.assoc, hy, Category.assoc]
  simp only [jK, spMap, ← Spec.map_comp] at e
  have e2 := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  ext r
  have := congrArg (fun f => f r) e2
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
  exact IsFractionRing.injective V (FractionRing V) this
end GlobalTheory.UCanon.LowPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerObjectCompleteDVRBothMaps
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.UCanon.LowPull.exists_lowObj_cdvr : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ θ₁ θ₂ : R →+* V, Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK V ≫ spMap θ₁ → κ₂ ≫ jK R = jK V ≫ spMap θ₂ → κ₁ ≫ C.y = κ₂ ≫ C.y → ∃ (o' : LowObj Cn.D' c ((θ₁.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b)) (m₁ : ObjMap o' Cn.L.o (spMap (θ₁.comp (Cn.ψ.comp MvPolynomial.C)))) (m₂ : ObjMap o' Cn.L.o (spMap (θ₂.comp (Cn.ψ.comp MvPolynomial.C)))) (x : Cn.L.D.X → (Sp V ⟶ o'.t.G.left)), (∀ y, x y ≫ m₁.toSABMap.φ ≫ Cn.L.φB = spMap (θ₁.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.D.c y).left) ∧ (∀ y, x y ≫ m₂.toSABMap.φ ≫ Cn.L.φB = spMap (θ₂.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.D.c y).left) ∧ ∀ y, x y ≫ o'.t.G.hom = 𝟙 _ := by
  intro E _ _ _ H Dw l Xo c φ hpq hφ hns R _ _ _ hR C Cn V _ _ _ hV θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂ κ₁ κ₂ hκ₁ hκ₂ hy
  obtain ⟨hdvr, hc, hch⟩ := hV
  haveI := hdvr
  haveI := hch
  have hb : θ₁.comp C.b = θ₂.comp C.b := LowPull.comp_b_eq C.toFam θ₁ θ₂ κ₁ κ₂ hκ₁ hκ₂ hy
  obtain ⟨D₁, D₂, hD₁, hD₂, j₁, j₂, b, φ', he₁, he₂, hM, hlin, hQ, hbl⟩ :=
    GlobalTheory.UInj.pair_match Xo c φ R hR C.toFam V hc θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂ κ₁ κ₂ hκ₁ hκ₂ hy
  have hlat := GlobalTheory.T.canonicalFamily_latticeIdentification_eq_id Xo c φ hpq hφ hns R hR C Cn V hc θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂ D₁ D₂ hD₁ hD₂ j₁ j₂ b φ' he₁ he₂ hM
    hlin hQ
  exact LowPull.exists_pull₂ Cn.L V _ _ (GlobalTheory.T.canonicalFamily_base_eq_of_matching_pullbacks Xo c φ R hR C Cn V hc θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂ D₁ D₂ hD₁ hD₂ j₁ j₂ b φ'
    he₁ he₂ hM hQ hbl hlat hb)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLowerObjectCompleteDVRBothMapsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lowerObject_completeDVR_both_maps : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ θ₁ θ₂ : R →+* V, Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK V ≫ spMap θ₁ → κ₂ ≫ jK R = jK V ≫ spMap θ₂ → κ₁ ≫ C.y = κ₂ ≫ C.y → ∃ (o' : LowObj Cn.D' c ((θ₁.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b)) (m₁ : ObjMap o' Cn.L.o (spMap (θ₁.comp (Cn.ψ.comp MvPolynomial.C)))) (m₂ : ObjMap o' Cn.L.o (spMap (θ₂.comp (Cn.ψ.comp MvPolynomial.C)))) (x : Cn.L.D.X → (Sp V ⟶ o'.t.G.left)), (∀ y, x y ≫ m₁.toSABMap.φ ≫ Cn.L.φB = spMap (θ₁.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.D.c y).left) ∧ (∀ y, x y ≫ m₂.toSABMap.φ ≫ Cn.L.φB = spMap (θ₂.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.D.c y).left) ∧ ∀ y, x y ≫ o'.t.G.hom = 𝟙 _ := by
  first | exact @GlobalTheory.UCanon.LowPull.exists_lowObj_cdvr | exact GlobalTheory.UCanon.LowPull.exists_lowObj_cdvr | (intros; apply GlobalTheory.UCanon.LowPull.exists_lowObj_cdvr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBaseInjectionsAgree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon

theorem comp_b_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (F : Fam Xo c R)
    {V : Type} [CommRing V] [IsDomain V] (θ₁ θ₂ : R →+* V) (κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R))
    (h₁ : κ₁ ≫ jK R = jK V ≫ spMap θ₁) (h₂ : κ₂ ≫ jK R = jK V ≫ spMap θ₂) (hy : κ₁ ≫ F.y = κ₂ ≫ F.y) :
    θ₁.comp F.b = θ₂.comp F.b := by
  have key : ∀ (θ : R →+* V) (κ : Sp (FractionRing V) ⟶ Sp (FractionRing R)), κ ≫ jK R = jK V ≫ spMap θ →
      jK V ≫ spMap (θ.comp F.b) = κ ≫ F.y ≫ pullback.snd _ _ := by
    intro θ κ h
    rw [F.y_over, ← Category.assoc, h, Category.assoc, spMap_comp]
  have e : jK V ≫ spMap (θ₁.comp F.b) = jK V ≫ spMap (θ₂.comp F.b) := by
    rw [key θ₁ κ₁ h₁, key θ₂ κ₂ h₂, ← Category.assoc, hy, Category.assoc]
  simp only [jK, spMap, ← Spec.map_comp] at e
  have e2 := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  ext r
  have := congrArg (fun f => f r) e2
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
  exact IsFractionRing.injective V (FractionRing V) this

theorem injBase_cdvr : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.LN.CDvr V → ∀ θ₁ θ₂ : R →+* V, Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK V ≫ spMap θ₁ → κ₂ ≫ jK R = jK V ≫ spMap θ₂ → κ₁ ≫ C.y = κ₂ ≫ C.y → θ₁.comp (Cn.ψ.comp MvPolynomial.C) = θ₂.comp (Cn.ψ.comp MvPolynomial.C) := by
  intro E _ _ _ H Dw l Xo c φ hpq hφ hns R _ _ _ hR C Cn V _ _ _ hV θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂ κ₁ κ₂ hκ₁ hκ₂ hy
  obtain ⟨o', m₁, m₂, x, h₁, h₂, h₃⟩ :=
    GlobalTheory.T.exists_lowerObject_completeDVR_both_maps Xo c φ hpq hφ hns R hR C Cn V hV θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂ κ₁ κ₂ hκ₁ hκ₂ hy
  have hb : (θ₁.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b = (θ₂.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b := by
    have k : ∀ θ : R →+* V, (θ.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b = θ.comp C.b := fun θ => by
      rw [← Cn.base]; rfl
    rw [k, k]
    exact comp_b_eq C.toFam θ₁ θ₂ κ₁ κ₂ hκ₁ hκ₂ hy
  exact Cn.L.fineRed V _ _ hb o' m₁ m₂ x h₁ h₂ h₃

theorem injBase : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], GlobalTheory.Mum.Base R' → ∀ θ₁ θ₂ : R →+* R', Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ κ₁ κ₂ : Sp (FractionRing R') ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK R' ≫ spMap θ₁ → κ₂ ≫ jK R = jK R' ≫ spMap θ₂ → κ₁ ≫ C.y = κ₂ ≫ C.y → θ₁.comp (Cn.ψ.comp MvPolynomial.C) = θ₂.comp (Cn.ψ.comp MvPolynomial.C) := by
  intro E _ _ _ H Dw l Xo c φ hpq hφ hns R _ _ _ hR C Cn R' _ _ _ hR' θ₁ θ₂ hθ₁ hθ₂ hl₁ hl₂ κ₁ κ₂ hκ₁ hκ₂ hy
  haveI : IsNoetherianRing R' := hR'.1.1
  haveI : CharZero R' := hR'.2
  obtain ⟨V, _, _, _, jv, hV, hjv, hjvl⟩ := GlobalTheory.Mum.exists_cDvr_injective_isLocalHom R'
  obtain ⟨κv, hκv⟩ := GlobalTheory.PolDeg.exists_genericMap hjv
  have h := injBase_cdvr Xo c φ hpq hφ hns R hR C Cn V hV (jv.comp θ₁) (jv.comp θ₂) (hjv.comp hθ₁) (hjv.comp hθ₂)
    (RingHom.isLocalHom_comp _ _) (RingHom.isLocalHom_comp _ _) (κv ≫ κ₁) (κv ≫ κ₂)
    (by rw [Category.assoc, hκ₁, ← Category.assoc, hκv, Category.assoc, ← spMap_comp])
    (by rw [Category.assoc, hκ₂, ← Category.assoc, hκv, Category.assoc, ← spMap_comp])
    (by rw [Category.assoc, Category.assoc, hy])
  ext r
  exact hjv (by simpa using DFunLike.congr_fun h r)

end GlobalTheory.UCanon
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBaseInjectionsAgreeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalFamily_base_injections_agree : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], GlobalTheory.Mum.Base R' → ∀ θ₁ θ₂ : R →+* R', Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ → ∀ κ₁ κ₂ : Sp (FractionRing R') ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK R' ≫ spMap θ₁ → κ₂ ≫ jK R = jK R' ≫ spMap θ₂ → κ₁ ≫ C.y = κ₂ ≫ C.y → θ₁.comp (Cn.ψ.comp MvPolynomial.C) = θ₂.comp (Cn.ψ.comp MvPolynomial.C) := by
  first | exact @GlobalTheory.UCanon.injBase | exact GlobalTheory.UCanon.injBase | (intros; apply GlobalTheory.UCanon.injBase <;> assumption)
end
