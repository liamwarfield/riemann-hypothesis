module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingExistsOfCubeTheorem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechKodairaSpencerPullbackSemiAbelianMap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerCompat
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KSAgree

theorem dual_alg {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') :
    (dualMap r).comp (algebraMap S (DualNumber S)) = (algebraMap S' (DualNumber S')).comp r := by
  ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl] <;> rfl

theorem fst_dual {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') :
    (TrivSqZeroExt.fstHom S' S' S').toRingHom.comp (dualMap r) = r.comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext a <;> (try simp [dualMap]) <;> rfl

section Gen
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)

theorem eps_over {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') {x : Sp S ⟶ X} {x' : Sp S' ⟶ X}
    (hx : spMap r ≫ x = x') :
    spMap (dualMap r) ≫ spMap (algebraMap S (DualNumber S)) ≫ x = spMap (algebraMap S' (DualNumber S')) ≫ x' := by
  have h : spMap (dualMap r) ≫ spMap (algebraMap S (DualNumber S)) =
      spMap (algebraMap S' (DualNumber S')) ≫ spMap r := by
    rw [GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.spMap_comp', dual_alg]
  rw [← hx, ← Category.assoc, ← Category.assoc, h]

theorem tan_map {S S' : Type} [CommRing S] [CommRing S'] (r : S →+* S') {x : Sp S ⟶ X} {x' : Sp S' ⟶ X}
    (hx : spMap r ≫ x = x') {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x v) :
    IsTanAtG t x' (spMap (dualMap r) ≫ v) := by
  refine ⟨?_, ?_⟩
  · rw [Category.assoc, hv.1, eps_over r hx]
  · have h : spMap (TrivSqZeroExt.fstHom S' S' S').toRingHom ≫ spMap (dualMap r) =
        spMap r ≫ spMap (TrivSqZeroExt.fstHom S S S).toRingHom := by
      rw [GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.spMap_comp', fst_dual]
    rw [← Category.assoc, h, Category.assoc, hv.2]
    let k : Over.mk x' ⟶ Over.mk x := Over.homMk (spMap r) hx
    exact congrArg CommaMorphism.left (comp_one k (M := t.G))

end Gen

theorem tan_res : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (U W : X.affineOpens) (hW : W.1 ≤ U.1) (v : Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left), IsTanAtG t (chart U) v → IsTanAtG t (chart W) (spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v) :=
  fun _ _ _ _ _ _ t U W hW _ hv => tan_map t _ (GlobalTheory.LogKSLoc.spMap_res_chart U W hW) hv

end GlobalTheory.KSAgree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationAway
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LocReg

theorem exists_derivation_away {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (f : A)
    (hloc : letI := φ.toAlgebra; IsLocalization.Away f B) (d : A → A)
    (hadd : ∀ x y, d (x + y) = d x + d y) (hmul : ∀ x y, d (x * y) = x * d y + y * d x) :
    ∃ D : Derivation ℤ B B, ∀ a, D (φ a) = φ (d a) := by
  letI := φ.toAlgebra
  have h0 : d 0 = 0 := by
    have e := hadd 0 0
    rw [add_zero] at e
    linear_combination -e
  have h1 : d 1 = 0 := by
    have e := hmul 1 1
    rw [_root_.mul_one, _root_.one_mul] at e
    linear_combination -e
  let ψ : A →+* TrivSqZeroExt B B :=
    { toFun := fun a => TrivSqZeroExt.inl (φ a) + TrivSqZeroExt.inr (φ (d a))
      map_one' := by ext <;> simp [h1]
      map_mul' := fun x y => by
        ext
        · simp
        · simp [hmul]
          ring
      map_zero' := by ext <;> simp [h0]
      map_add' := fun x y => by ext <;> simp [hadd] }
  have hu : IsUnit (ψ f) := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (by
    simpa [ψ, RingHom.algebraMap_toAlgebra] using IsLocalization.Away.algebraMap_isUnit (S := B) f)
  let Λ : B →+* TrivSqZeroExt B B := IsLocalization.Away.lift f hu
  have hΛ : ∀ a, Λ (φ a) = ψ a := fun a => IsLocalization.lift_eq (M := Submonoid.powers f) (S := B) _ a
  have hfst : ∀ x, (Λ x).fst = x := by
    have : (TrivSqZeroExt.fstHom ℤ B B).toRingHom.comp Λ = RingHom.id B := by
      refine IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun r => ?_)
      simp [RingHom.algebraMap_toAlgebra, hΛ, ψ]
    intro x
    exact congr($this x)
  let L : B →+ B :=
    { toFun := fun x => (Λ x).snd
      map_zero' := by simp
      map_add' := fun x y => by simp }
  refine ⟨Derivation.mk' L.toIntLinearMap (fun x y => ?_), fun a => ?_⟩
  · show (Λ (x * y)).snd = x • (Λ y).snd + y • (Λ x).snd
    rw [map_mul, TrivSqZeroExt.snd_mul, hfst, hfst]
    simp [mul_comm]
  · show (Λ (φ a)).snd = φ (d a)
    rw [hΛ]
    simp [ψ]

theorem deriv_ext_basicOpen : ∀ (X : Scheme.{0}) (U W : X.affineOpens) (hWU : W.1 ≤ U.1) (D : Derivation ℤ Γ(X, U.1) Γ(X, U.1)) (DW : Derivation ℤ Γ(X, W.1) Γ(X, W.1)), (∀ r, DW ((X.presheaf.map (homOfLE hWU).op).hom r) = (X.presheaf.map (homOfLE hWU).op).hom (D r)) → ∀ (h : Γ(X, U.1)), X.basicOpen h ≤ W.1 → ∀ (R : Type) [CommRing R] [Algebra ℤ R] (g : Sp R ⟶ X) (hg : ⊤ ≤ g ⁻¹ᵁ U.1) (D' : Derivation ℤ R R), (∀ r, D' ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((g.appLE U.1 ⊤ hg).hom r)) = (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom ((g.appLE U.1 ⊤ hg).hom (D r))) → ∃ (hUW : ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1 ≤ g ⁻¹ᵁ W.1) (D'' : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1)), (∀ r, D'' (((Sp R).presheaf.map (homOfLE (le_top : ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1 ≤ ⊤)).op).hom r) = ((Sp R).presheaf.map (homOfLE (le_top : ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)).1 ≤ ⊤)).op).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (D' ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom r)))) ∧ (∀ θ, D'' ((g.appLE W.1 _ hUW).hom θ) = (g.appLE W.1 _ hUW).hom (DW θ)) := by

  intro X U W hWU D DW hDW h hhW R _ _ g hg D' hD'
  set e := Scheme.ΓSpecIso (CommRingCat.of R) with he
  set f := (g.appLE U.1 ⊤ hg).hom h with hf
  have hUW : ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) f).1 ≤ g ⁻¹ᵁ W.1 := by
    show (Sp R).basicOpen f ≤ _
    rw [hf, Scheme.Hom.appLE, CommRingCat.comp_apply, Scheme.basicOpen_res, ← Scheme.preimage_basicOpen]
    exact fun x hx => hhW hx.2
  refine ⟨hUW, ?_⟩
  set U' := ((Sp R).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) f) with hU'
  let φ := ((Sp R).presheaf.map (homOfLE (le_top : U'.1 ≤ ⊤)).op).hom
  have hloc : letI := φ.toAlgebra; IsLocalization.Away f Γ(Sp R, U'.1) :=
    (isAffineOpen_top (Sp R)).isLocalization_basicOpen f
  obtain ⟨D'', hD''⟩ := exists_derivation_away φ f hloc (fun r => e.inv.hom (D' (e.hom.hom r)))
    (fun x y => by simp only [map_add (f := _)]) (fun x y => by
      simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add (f := _)]
      simp)
  refine ⟨D'', hD'', ?_⟩

  set resUW := (X.presheaf.map (homOfLE hWU).op).hom with hresUW
  set ψW := (g.appLE W.1 U'.1 hUW).hom with hψW
  have hUU : U'.1 ≤ g ⁻¹ᵁ U.1 := hUW.trans (fun x hx => hWU hx)
  set ψU := (g.appLE U.1 U'.1 hUU).hom with hψU
  have hψ : ∀ y, ψW (resUW y) = ψU y := fun y => by
    rw [hψW, hresUW, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  have hψU' : ∀ y, ψU y = φ ((g.appLE U.1 ⊤ hg).hom y) := fun y => by
    rw [hψU, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  have hDU : ∀ y, D'' (ψU y) = ψU (D y) := fun y => by
    rw [hψU', hD'', hψU', hD']
    simp
  have hres : ∀ y, D'' (ψW (resUW y)) = ψW (DW (resUW y)) := fun y => by
    rw [hψ, hDU, hDW, hψ]
  have hunit : IsUnit (ψU h) := by
    rw [hψU']
    letI := φ.toAlgebra
    exact IsLocalization.Away.algebraMap_isUnit (S := Γ(Sp R, U'.1)) f
  have key : ∀ θ : Γ(X, W.1), ∃ (a : Γ(X, U.1)) (M : ℕ), resUW (h ^ M) * θ = resUW a := by
    intro θ
    set V := X.basicOpen (resUW h) with hVdef
    have hV : V = X.basicOpen h := by
      rw [hVdef, hresUW, Scheme.basicOpen_res]
      exact inf_eq_right.2 hhW
    have hVW : V ≤ W.1 := X.basicOpen_le _
    have hVU : V ≤ U.1 := hVW.trans hWU
    let resUV := (X.presheaf.map (homOfLE hVU).op).hom
    let resWV := (X.presheaf.map (homOfLE hVW).op).hom
    have hcomp : ∀ y, resWV (resUW y) = resUV y := fun y => by
      rw [hresUW, ← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    have hlocU : letI := resUV.toAlgebra; IsLocalization.Away h Γ(X, V) :=
      U.2.isLocalization_of_eq_basicOpen h (homOfLE hVU) hV
    have hlocW : letI := resWV.toAlgebra; IsLocalization.Away (resUW h) Γ(X, V) :=
      W.2.isLocalization_basicOpen (resUW h)
    obtain ⟨⟨a, _, N, rfl⟩, hN⟩ := (letI := resUV.toAlgebra; IsLocalization.surj (Submonoid.powers h) (resWV θ))
    simp only [RingHom.algebraMap_toAlgebra] at hN
    rw [← hcomp, ← hcomp, ← map_mul] at hN
    letI := resWV.toAlgebra
    obtain ⟨⟨c, k, rfl⟩, hc⟩ := IsLocalization.exists_of_eq (M := Submonoid.powers (resUW h)) (S := Γ(X, V))
      (x := θ * resUW (h ^ N)) (y := resUW a) (by simpa only [RingHom.algebraMap_toAlgebra] using hN)
    refine ⟨h ^ k * a, k + N, ?_⟩
    simp only [map_mul, map_pow] at hc ⊢
    linear_combination hc
  intro θ
  obtain ⟨a, M, hM⟩ := key θ
  have e2 := congrArg (fun x => D'' (ψW x)) hM
  have e3 := congrArg (fun x => ψW (DW x)) hM
  simp only [map_mul, Derivation.leibniz, smul_eq_mul, map_add (f := _)] at e2 e3
  rw [hres, hres] at e2
  have hu : IsUnit (ψW (resUW (h ^ M))) := by rw [hψ, map_pow]; exact hunit.pow M
  exact hu.mul_left_cancel (by linear_combination e2 - e3)

end GlobalTheory.LocReg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TanBasisPull
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BasisPull

theorem tanBasis_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (T : SAB H X) (t : SAB H X') (g : X' ⟶ X) (φ : SABMap t T g) (U : X.affineOpens) (U' : X'.affineOpens) (hU : U'.1 ≤ g ⁻¹ᵁ U.1) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ T.G.left)) (v' : Fin n → (Sp (DualNumber Γ(X', U'.1)) ⟶ t.G.left)), (∀ i, IsTanAtG T (chart U) (v i)) → (∀ w, IsTanAtG T (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG T (chart U) v cf w) → (∀ i, IsTanAtG t (chart U') (v' i)) → (∀ i, v' i ≫ φ.φ = spMap (dualMap (g.appLE U.1 U'.1 hU).hom) ≫ v i) → ∀ w, IsTanAtG t (chart U') w → ∃! cf : Fin n → Γ(X', U'.1), IsCombAtG t (chart U') v' cf w := by
  intro E _ _ _ H X X' T t g φ U U' hU n v v' hv hvb hv' hvv' w hw
  have hx : chart U' ≫ g = spMap (g.appLE U.1 U'.1 hU).hom ≫ chart U :=
    (IsAffineOpen.SpecMap_appLE_fromSpec g U.2 U'.2 hU).symm
  obtain ⟨v'', hv''φ, hv''t, hv''b⟩ :=
    GlobalTheory.SabTan.tanBasis_sabMap E H X X' T t g φ _ _ (g.appLE U.1 U'.1 hU).hom (chart U) (chart U')
      hx n v hv hvb
  have heq : v'' = v' := by
    funext i
    apply φ.cart.1.hom_ext
    · rw [hv''φ, hvv']
    · rw [(hv''t i).1, (hv' i).1]
  rw [← heq]
  exact hv''b w hw

end GlobalTheory.BasisPull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartAppLEEq
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocReg

theorem chart_appLE_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), ∃ hg : ⊤ ≤ (ξ ≫ genι Y) ⁻¹ᵁ U.1, ((ξ ≫ genι Y).appLE U.1 ⊤ hg).hom = (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom.comp (GlobalTheory.LocReg.chartHom Y U ξ hx) := by
  intro E _ _ _ H Dw l Xo c Y U k _ m d ξ hx
  have hx' : (ξ ≫ genι Y) (closedPoint (CommRingCat.of (ChartRing k m d))) ∈ U.1 := hx
  refine ⟨(Scheme.preimage_eq_top_of_closedPoint_mem (ξ ≫ genι Y) hx').ge, ?_⟩
  have key : (gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) _ hx ≫ Scheme.stalkClosedPointTo ξ =
      ξ.appLE (genι Y ⁻¹ᵁ U.1) ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem ξ hx).ge ≫
        (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom := by
    rw [Scheme.germ_stalkClosedPointTo]
    simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]
  have e : (ξ ≫ genι Y).appLE U.1 ⊤ (Scheme.preimage_eq_top_of_closedPoint_mem (ξ ≫ genι Y) hx').ge =
      (genι Y).app U.1 ≫ (gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) _ hx ≫ Scheme.stalkClosedPointTo ξ ≫
        (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv := by
    rw [reassoc_of% key, Iso.hom_inv_id, Category.comp_id, Scheme.Hom.comp_appLE]
  rw [e]
  rfl

end GlobalTheory.LocReg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpMulTransport
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolAVPull

theorem grp_mul_transport {Y X : Scheme.{0}} (G : Over X) [GrpObj G] {a b : Y ⟶ X} (h : a = b)
    (u v : Over.mk a ⟶ G) (u' v' : Over.mk b ⟶ G) (hu : u'.left = u.left) (hv : v'.left = v.left) :
    (u' * v').left = (u * v).left := by
  subst h
  have e1 : u' = u := Over.OverMorphism.ext hu
  have e2 : v' = v := Over.OverMorphism.ext hv
  rw [e1, e2]

theorem polAV_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (T : SAB H X) (t : SAB H X') (g : X' ⟶ X) (φ : SABMap t T g) (K : Type) [Field K] (z : Sp K ⟶ X') (P₀ : PolAV (Sp K)) (θ : P₀.A.left ⟶ T.G.left), IsGrpPullback P₀.A T.G (z ≫ g) θ → LBIso P₀.L (T.PP.L.pull θ) → ∃ m : P₀.A.left ⟶ t.G.left, IsGrpPullback P₀.A t.G z m ∧ LBIso P₀.L (t.PP.L.pull m) := by
  intro E _ _ _ H X X' T t g φ K _ z P₀ θ hθ hL
  have hw : θ ≫ T.G.hom = (P₀.A.hom ≫ z) ≫ g := by rw [Category.assoc]; exact hθ.1.w
  let m : P₀.A.left ⟶ t.G.left := φ.cart.1.lift θ (P₀.A.hom ≫ z) hw
  have hm1 : m ≫ φ.φ = θ := φ.cart.1.lift_fst _ _ _
  have hm2 : m ≫ t.G.hom = P₀.A.hom ≫ z := φ.cart.1.lift_snd _ _ _
  refine ⟨m, ⟨?_, ?_⟩, ?_⟩
  · have s : IsPullback (m ≫ φ.φ) P₀.A.hom T.G.hom (z ≫ g) := by rw [hm1]; exact hθ.1
    exact IsPullback.of_right s hm2 φ.cart.1
  · intro T' x y x₀ y₀ hx hy
    apply φ.cart.1.hom_ext
    · let x₁ : Over.mk ((Over.mk (T'.hom ≫ z)).hom ≫ g) ⟶ T.G :=
        Over.homMk (x₀.left ≫ φ.φ) (by
          show x₀.left ≫ φ.φ ≫ T.G.hom = _; rw [φ.cart.1.w, ← Category.assoc, Over.w x₀]; rfl)
      let y₁ : Over.mk ((Over.mk (T'.hom ≫ z)).hom ≫ g) ⟶ T.G :=
        Over.homMk (y₀.left ≫ φ.φ) (by
          show y₀.left ≫ φ.φ ≫ T.G.hom = _; rw [φ.cart.1.w, ← Category.assoc, Over.w y₀]; rfl)
      have e1 := φ.cart.2 (Over.mk (T'.hom ≫ z)) x₀ y₀ x₁ y₁ rfl rfl
      let x₂ : Over.mk (T'.hom ≫ z ≫ g) ⟶ T.G := Over.homMk (x.left ≫ θ) (by
        show x.left ≫ θ ≫ T.G.hom = _; rw [hθ.1.w, ← Category.assoc, Over.w x]; rfl)
      let y₂ : Over.mk (T'.hom ≫ z ≫ g) ⟶ T.G := Over.homMk (y.left ≫ θ) (by
        show y.left ≫ θ ≫ T.G.hom = _; rw [hθ.1.w, ← Category.assoc, Over.w y]; rfl)
      have e2 := hθ.2 T' x y x₂ y₂ rfl rfl
      have e3 : (x₁ * y₁).left = (x₂ * y₂).left :=
        grp_mul_transport T.G (by simp [Category.assoc]) x₂ y₂ x₁ y₁
          (by simp [x₁, x₂, hx, Category.assoc, hm1]) (by simp [y₁, y₂, hy, Category.assoc, hm1])
      rw [← e1, e3, e2, Category.assoc, hm1]
    · rw [Category.assoc, hm2, Over.w]
      simp only [Over.mk_hom, ← Category.assoc, Over.w]
  · have h1 : LBIso (t.PP.L.pull m) (T.PP.L.pull θ) :=
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t.PP.L m m rfl)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullSame T.PP.L (fun _ : PUnit => θ) (fun _ => φ.φ) (fun _ => 1) m (fun _ => hm1.symm))
        (by obtain ⟨w, hw, -⟩ := φ.lin; exact ⟨w, hw⟩)
    exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.trans P₀.isLB (pull_isLB T.PP.isLB θ) (pull_isLB t.PP.isLB m) hL (ReciprocityTheory.ChartRestriction.G.Geo.Tor.LBIso.symm h1)

end GlobalTheory.PolAVPull
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerChartEqAtGenericPoint
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section

namespace GlobalTheory.LocRegCmp
open GlobalTheory.FlagMod (ev)

theorem leibniz_ext_of_res {X : Scheme.{0}} (U W : X.affineOpens) (hW : W.1 ≤ U.1) {C : Type} [CommRing C]
    (ψ : Γ(X, W.1) →+* C) (d : C → C) (hadd : ∀ x y, d (x + y) = d x + d y)
    (hd : ∀ x y, d (x * y) = x * d y + y * d x) (D : Derivation ℤ Γ(X, W.1) Γ(X, W.1))
    (h : ∀ r, d (ψ ((X.presheaf.map (homOfLE hW).op).hom r)) = ψ (D ((X.presheaf.map (homOfLE hW).op).hom r)))
    (b : Γ(X, W.1)) : d (ψ b) = ψ (D b) := by
  have d0 : d 0 = 0 := by simpa using hadd 0 0
  have d1 : d 1 = 0 := by simpa using hd 1 1
  let g₁ : Γ(X, W.1) →+* DualNumber C :=
    { toFun := fun r => TrivSqZeroExt.inl (ψ r) + TrivSqZeroExt.inr (d (ψ r))
      map_one' := by ext <;> simp [d1]
      map_zero' := by ext <;> simp [d0]
      map_add' := fun a b => by ext <;> simp [hadd]
      map_mul' := fun a b => by ext <;> simp [hd, mul_comm] }
  let g₂ : Γ(X, W.1) →+* DualNumber C :=
    { toFun := fun r => TrivSqZeroExt.inl (ψ r) + TrivSqZeroExt.inr (ψ (D r))
      map_one' := by ext <;> simp
      map_zero' := by ext <;> simp
      map_add' := fun a b => by ext <;> simp
      map_mul' := fun a b => by ext <;> simp [Derivation.leibniz, mul_comm] }
  have e : g₁.comp (X.presheaf.map (homOfLE hW).op).hom = g₂.comp (X.presheaf.map (homOfLE hW).op).hom := by
    refine RingHom.ext fun r => ?_
    ext
    · simp [g₁, g₂]
    · simpa [g₁, g₂] using h r
  have : IsOpenImmersion (chart W) := W.2.isOpenImmersion_fromSpec
  have e2 : spMap g₁ ≫ chart W = spMap g₂ ≫ chart W := by
    rw [← GlobalTheory.LogKSLoc.spMap_res_chart U W hW, ← Category.assoc, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp',
      GlobalTheory.LogKSLoc.spMap_comp', e]
  have e3 := congrArg CommRingCat.Hom.hom (Spec.map_inj.1 ((cancel_mono (chart W)).1 e2))
  have e4 : g₁ b = g₂ b := congrArg (fun k => k b) e3
  simpa [g₁, g₂] using congrArg TrivSqZeroExt.snd e4

theorem isKS_restrict {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X)
    (V : X.Opens) (U W : X.affineOpens) (hW : W.1 ≤ U.1) {n : ℕ}
    (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (D : Γ(X, U.1) → Γ(X, U.1))
    (DW : Derivation ℤ Γ(X, W.1) Γ(X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1))
    (hD : ∀ r, DW ((X.presheaf.map (homOfLE hW).op).hom r) = (X.presheaf.map (homOfLE hW).op).hom (D r))
    (hKS : IsKS t V U v D Θ) :
    IsKS t V W (fun i => spMap (dualMap (X.presheaf.map (homOfLE hW).op).hom) ≫ v i) DW
      ((X.presheaf.map (homOfLE hW).op).hom.mapMatrix Θ) := by
  obtain ⟨J, Wc, j, d, hsup, hj, hfld, hcomp, htest⟩ := hKS
  have hWU : ∀ i, Wc i ≤ t.G.hom ⁻¹ᵁ U.1 := fun i =>
    (le_iSup Wc i).trans (hsup.le.trans (t.G.hom.preimage_mono inf_le_left))
  refine ⟨J, fun i => Wc i ⊓ t.G.hom ⁻¹ᵁ W.1, j, d, ?_, fun i => inf_le_left.trans (hj i), fun i => ?_,
    fun i h b => ?_, fun i i' O hO g S _ φ g₀ w hg₀ hO' hw => ?_⟩
  · rw [← iSup_inf_eq, hsup, ← Scheme.Hom.preimage_inf, inf_right_comm, inf_eq_right.mpr hW]
  · exact ⟨fun O hO => (hfld i).1 O (hO.trans inf_le_left), fun O hO => (hfld i).2.1 O (hO.trans inf_le_left),
      fun O O' h hO => (hfld i).2.2 O O' h (hO.trans inf_le_left)⟩
  · have e : ∀ r : Γ(X, U.1), (t.G.hom.appLE W.1 (Wc i ⊓ t.G.hom ⁻¹ᵁ W.1) h).hom
        ((X.presheaf.map (homOfLE hW).op).hom r) =
        resG t.G.left (inf_le_left : Wc i ⊓ t.G.hom ⁻¹ᵁ W.1 ≤ Wc i) ((t.G.hom.appLE U.1 (Wc i) (hWU i)).hom r) := by
      intro r
      have e1 := congrArg (fun k => k.hom r) (t.G.hom.map_appLE h (homOfLE hW).op)
      have e2 := congrArg (fun k => k.hom r) (t.G.hom.appLE_map (hWU i)
        (homOfLE (inf_le_left : Wc i ⊓ t.G.hom ⁻¹ᵁ W.1 ≤ Wc i)).op)
      exact e1.trans e2.symm
    refine leibniz_ext_of_res U W hW _ _ ((hfld i).1 _ inf_le_left) ((hfld i).2.1 _ inf_le_left) DW (fun r => ?_) b
    rw [hD, e, e, (hfld i).2.2 _ _ _ le_rfl, hcomp]
  · refine htest i i' O (hO.trans (inf_le_inf inf_le_left inf_le_left)) g S
      (φ.comp (X.presheaf.map (homOfLE hW).op).hom) g₀ w ?_ hO' fun a => ?_
    · rw [hg₀, ← GlobalTheory.LogKSLoc.spMap_res_chart U W hW, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp']
    · obtain ⟨g', v', h₁, h₂, h₃⟩ := hw a
      refine ⟨g', v', h₁, ?_, h₃⟩
      rw [h₂, ← Category.assoc, GlobalTheory.LogKSLoc.spMap_comp', GlobalTheory.LogKSLoc.dualMap_comp']

theorem ks_chart_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ∀ (U W : Y.X.affineOpens) (hW : W.1 = U.1 ⊓ interior Y) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (DW : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, W.1)), (∀ r, DW ((Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom r) = (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom (D.1 r)) → IsKS Y.t (interior Y) W (fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) DW Θ → ∀ (k : Type) [Field k] [CharZero k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1) (t : SAB H (Sp (ChartRing k m d))) (φ : SABMap t Y.t (ξ ≫ genι Y)), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) → ∀ vR : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (vR i)) → (∀ i, vR i ≫ φ.φ = spMap (dualMap ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom.comp (GlobalTheory.LocReg.chartHom Y U ξ hx))) ≫ v i) → ∀ D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ r, D' (GlobalTheory.LocReg.chartHom Y U ξ hx r) = GlobalTheory.LocReg.chartHom Y U ξ hx (D.1 r)) → ∀ ΘR : Matrix (Fin n) (Fin n) Γ(Sp (ChartRing k m d), ⊤), IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) vR (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D' ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) ΘR → ∀ (h : Γ(Y.X, U.1)) (hh : Y.X.basicOpen h ≤ W.1), GlobalTheory.LocReg.chartHom Y U ξ hx h ≠ 0 → ∀ (a b : Fin n) (s : Γ(Y.X, U.1)) (N : ℕ), (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le h)).op).hom s = (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le h)).op).hom (h ^ N) * (Y.X.presheaf.map (homOfLE hh).op).hom (Θ a b) → GlobalTheory.LocReg.chartHom Y U ξ hx s = GlobalTheory.LocReg.chartHom Y U ξ hx h ^ N * (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (ΘR a b) := by
  intro E _ _ _ H Dw l Xo c Y hpq hsm U W hW n v hv hb D DW Θ hDW hKS k _ _ m d ξ hx t φ hEt hbd vR hvR hvRφ D' hD' ΘR hKSR h hh hρh a b s N hs
  let ι0 : ChartRing k m d →+* FractionRing (ChartRing k m d) := algebraMap _ _
  let g : Sp (ChartRing k m d) ⟶ Y.X := ξ ≫ genι Y
  have hι0 : Function.Injective ι0 := IsFractionRing.injective _ _
  haveI : CharZero (FractionRing (ChartRing k m d)) :=
    charZero_of_injective_ringHom (f := ι0.comp (algebraMap k (ChartRing k m d))) (hι0.comp (algebraMap k _).injective)
  obtain ⟨hg, hgρ⟩ := GlobalTheory.LocReg.chart_appLE_eq E H Dw l Xo c Y U k m d ξ hx
  have eR : ∀ x : ChartRing k m d, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom x) = x :=
    fun x => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv_hom_id_apply x
  have hgx : ∀ r, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom ((g.appLE U.1 ⊤ hg).hom r) =
      GlobalTheory.LocReg.chartHom Y U ξ hx r := by
    intro r; rw [hgρ]; exact eR _
  obtain ⟨hUW, D'', hDtop, hDW'⟩ := GlobalTheory.LocReg.deriv_ext_basicOpen Y.X U W (hW.le.trans inf_le_left) D.1 DW hDW h hh _ g hg D'
    (fun r => by rw [hgx, hgx]; exact hD' r)
  let U' : (Sp (ChartRing k m d)).affineOpens :=
    (Sp (ChartRing k m d)).affineBasicOpen (U := ⟨⊤, isAffineOpen_top _⟩) ((g.appLE U.1 ⊤ hg).hom h)
  have hU'U : U'.1 ≤ g ⁻¹ᵁ U.1 := hUW.trans (g.preimage_mono (hW.le.trans inf_le_left))
  let v' : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), U'.1)) ⟶ t.G.left) := fun i =>
    spMap (dualMap ((Sp (ChartRing k m d)).presheaf.map (homOfLE (le_top : U'.1 ≤ ⊤)).op).hom) ≫ vR i
  have hv' : ∀ i, IsTanAtG t (chart U') (v' i) := fun i =>
    GlobalTheory.KSAgree.tan_res E H _ t ⟨⊤, isAffineOpen_top _⟩ U' le_top (vR i) (hvR i)
  have hcompU : ∀ i, v' i ≫ φ.φ = spMap (dualMap (g.appLE U.1 U'.1 hU'U).hom) ≫ v i := by
    intro i
    show (spMap _ ≫ vR i) ≫ φ.φ = _
    rw [Category.assoc, hvRφ i, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, GlobalTheory.CechKS.dualMap_comp_dualMap, ← hgρ,
      ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
  have hcompW : ∀ i, v' i ≫ φ.φ = spMap (dualMap (g.appLE W.1 U'.1 hUW).hom) ≫
      (spMap (dualMap (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) := by
    intro i
    rw [hcompU i, ← Category.assoc, ← GlobalTheory.Cris.spMap_comp, GlobalTheory.CechKS.dualMap_comp_dualMap,
      ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]
  let V' : (Sp (ChartRing k m d)).Opens := (Sp (ChartRing k m d)).basicOpen
    ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))
  have hUV' : U'.1 ⊓ V' ≤ g ⁻¹ᵁ interior Y := by
    intro p hp
    have hp2 : p ∈ V' := hp.2
    have hnp : ∏ i, bdParam k m d i ∉ p.asIdeal := by
      have := hp2
      simp only [V'] at this
      rw [basicOpen_eq_of_affine] at this
      exact this
    have hnb : ξ p ∉ genBd Y := fun h' => hnp ((hbd p).1 h')
    obtain ⟨y, hy⟩ : ξ p ∈ Set.range Y.jQ := by
      by_contra h'
      exact hnb (mem_genBd.2 h')
    show g p ∈ (interior Y : Set Y.X)
    rw [GlobalTheory.LogKS.interior, Scheme.Hom.coe_opensRange]
    refine ⟨y, ?_⟩
    show (Y.jQ ≫ pullback.fst _ _) y = (ξ ≫ genι Y) p
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy]
  have hprod : ∏ i, bdParam k m d i ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun i _ h0 => ?_
    have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i : Fin m ⊕ Fin d) 1)) h0
    simp [bdParam, MvPowerSeries.coeff_X] at this
  let x0 : Sp (FractionRing (ChartRing k m d)) ⟶ Y.X := spMap ι0 ≫ g
  have hevtop : ∀ (hK : ⊤ ≤ (spMap ι0) ⁻¹ᵁ (⊤ : (Sp (ChartRing k m d)).Opens)) r,
      ev (spMap ι0) ⊤ hK r = ι0 ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r) := by
    intro hK r
    unfold ev
    have : (spMap ι0).appLE ⊤ ⊤ hK = (spMap ι0).appTop := Scheme.Hom.appLE_eq_app _
    rw [this, Scheme.ΓSpecIso_naturality]
    rfl
  have hx0U : ⊤ ≤ x0 ⁻¹ᵁ U.1 := GlobalTheory.FlagMod.le_preimage_comp (spMap ι0) hg
  have hevU : ∀ r, ev x0 U.1 hx0U r = ι0 (GlobalTheory.LocReg.chartHom Y U ξ hx r) := by
    intro r
    rw [GlobalTheory.FlagMod.ev_spMap ι0 g U.1 hg hx0U]
    show ι0 ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom ((g.appLE U.1 ⊤ hg).hom r)) = _
    rw [hgx]
  have htop : ⊤ ≤ (spMap ι0) ⁻¹ᵁ (⊤ : (Sp (ChartRing k m d)).Opens) := fun _ _ => trivial
  have hx0h : ⊤ ≤ x0 ⁻¹ᵁ Y.X.basicOpen h := fun p _ =>
    GlobalTheory.DRFlag.LineOfMap.mem_basicOpen_of_isUnit_ev x0 U.1 hx0U h
      (by rw [hevU]; exact ((map_ne_zero_iff ι0 hι0).2 hρh).isUnit) p
  have hx0W : ⊤ ≤ x0 ⁻¹ᵁ W.1 := fun p hp => hh (hx0h hp)
  have hKU' : ⊤ ≤ (spMap ι0) ⁻¹ᵁ U'.1 := fun p _ =>
    GlobalTheory.DRFlag.LineOfMap.mem_basicOpen_of_isUnit_ev (spMap ι0) ⊤ htop ((g.appLE U.1 ⊤ hg).hom h)
      (by rw [hevtop, hgx]; exact ((map_ne_zero_iff ι0 hι0).2 hρh).isUnit) p
  have hKV' : ⊤ ≤ (spMap ι0) ⁻¹ᵁ V' := fun p _ =>
    GlobalTheory.DRFlag.LineOfMap.mem_basicOpen_of_isUnit_ev (spMap ι0) ⊤ htop _
      (by rw [hevtop, eR]; exact ((map_ne_zero_iff ι0 hι0).2 hprod).isUnit) p
  have hint : ⊤ ≤ x0 ⁻¹ᵁ interior Y := fun p hp => hUV' ⟨hKU' hp, hKV' hp⟩
  obtain ⟨P₀, θ0, hpb, hiso⟩ := GlobalTheory.KSUniq.exists_polAV_interior Y x0 hint
  obtain ⟨mm, hmm, hiso'⟩ := GlobalTheory.PolAVPull.polAV_pull E H Y.X _ Y.t t g φ _ (spMap ι0) P₀ θ0 hpb hiso
  let φK := ev (spMap ι0) U'.1 hKU'
  have hpt : spMap φK ≫ chart U' = spMap ι0 := GlobalTheory.FlagMod.spMap_ev (spMap ι0) U'.2 hKU'
  have hvW : ∀ i, IsTanAtG Y.t (chart W) (spMap (dualMap (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) :=
    fun i => GlobalTheory.KSAgree.tan_res E H Y.X Y.t U W _ (v i) (hv i)
  have hks1 := GlobalTheory.KSBaseChange.isKS_pull E H Y.X _ Y.t t g φ (interior Y) V' W U' hUW hUV' n _ v' hvW hv' hcompW DW D'' hDW' Θ hKS
  have hks2 := isKS_restrict t V' ⟨⊤, isAffineOpen_top _⟩ U' le_top vR _ D'' ΘR hDtop hKSR
  have hb' := GlobalTheory.BasisPull.tanBasis_pull E H Y.X _ Y.t t g φ U U' hU'U n v v' hv hb hv' hcompU
  have huniq := GlobalTheory.KSPtUniq.isKS_unique_at_point E H _ t V' U' n v' hv' hb' _ φK P₀ mm
    (by rw [hpt]; exact hKV') (by rw [hpt]; exact hmm) hiso' _ _ _ hks1 hks2
  have hab := congrFun (congrFun huniq a) b
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply] at hab
  have e1 : φK ((g.appLE W.1 U'.1 hUW).hom (Θ a b)) = ev x0 W.1 hx0W (Θ a b) :=
    GlobalTheory.FlagMod.ev_appLE (spMap ι0) g hUW hKU' hx0W (Θ a b)
  have e2 : φK (((Sp (ChartRing k m d)).presheaf.map (homOfLE (le_top : U'.1 ≤ ⊤)).op).hom (ΘR a b)) =
      ι0 ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (ΘR a b)) :=
    (GlobalTheory.FlagMod.ev_res (spMap ι0) le_top hKU' htop (ΘR a b)).trans (hevtop _ _)
  have r1 : ev x0 (Y.X.basicOpen h) hx0h ((Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le h)).op).hom s) =
      ι0 (GlobalTheory.LocReg.chartHom Y U ξ hx s) :=
    (GlobalTheory.FlagMod.ev_res x0 (Y.X.basicOpen_le h) hx0h hx0U s).trans (hevU s)
  have r2 : ev x0 (Y.X.basicOpen h) hx0h ((Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le h)).op).hom (h ^ N)) =
      ι0 (GlobalTheory.LocReg.chartHom Y U ξ hx h) ^ N := by
    rw [← map_pow, ← map_pow]
    exact (GlobalTheory.FlagMod.ev_res x0 (Y.X.basicOpen_le h) hx0h hx0U (h ^ N)).trans (hevU _)
  have r3 : ev x0 (Y.X.basicOpen h) hx0h ((Y.X.presheaf.map (homOfLE hh).op).hom (Θ a b)) = ev x0 W.1 hx0W (Θ a b) :=
    GlobalTheory.FlagMod.ev_res x0 hh hx0h hx0W _
  have hsx := congrArg (ev x0 (Y.X.basicOpen h) hx0h) hs
  rw [map_mul, r1, r2, r3, ← e1, hab, e2] at hsx
  apply hι0
  rw [map_mul, map_pow]
  exact hsx

end GlobalTheory.LocRegCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerChartEqAtGenericPointStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencer_chart_eq_at_generic_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ∀ (U W : Y.X.affineOpens) (hW : W.1 = U.1 ⊓ interior Y) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (DW : Derivation ℤ Γ(Y.X, W.1) Γ(Y.X, W.1)) (Θ : Matrix (Fin n) (Fin n) Γ(Y.X, W.1)), (∀ r, DW ((Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom r) = (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom (D.1 r)) → IsKS Y.t (interior Y) W (fun i => spMap (dualMap (Y.X.presheaf.map (homOfLE (hW.le.trans inf_le_left)).op).hom) ≫ v i) DW Θ → ∀ (k : Type) [Field k] [CharZero k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1) (t : SAB H (Sp (ChartRing k m d))) (φ : SABMap t Y.t (ξ ≫ genι Y)), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) → ∀ vR : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (vR i)) → (∀ i, vR i ≫ φ.φ = spMap (dualMap ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom.comp (GlobalTheory.LocReg.chartHom Y U ξ hx))) ≫ v i) → ∀ D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ r, D' (GlobalTheory.LocReg.chartHom Y U ξ hx r) = GlobalTheory.LocReg.chartHom Y U ξ hx (D.1 r)) → ∀ ΘR : Matrix (Fin n) (Fin n) Γ(Sp (ChartRing k m d), ⊤), IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) vR (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D' ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) ΘR → ∀ (h : Γ(Y.X, U.1)) (hh : Y.X.basicOpen h ≤ W.1), GlobalTheory.LocReg.chartHom Y U ξ hx h ≠ 0 → ∀ (a b : Fin n) (s : Γ(Y.X, U.1)) (N : ℕ), (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le h)).op).hom s = (Y.X.presheaf.map (homOfLE (Y.X.basicOpen_le h)).op).hom (h ^ N) * (Y.X.presheaf.map (homOfLE hh).op).hom (Θ a b) → GlobalTheory.LocReg.chartHom Y U ξ hx s = GlobalTheory.LocReg.chartHom Y U ξ hx h ^ N * (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (ΘR a b) := by
  first | exact @GlobalTheory.LocRegCmp.ks_chart_eq | exact GlobalTheory.LocRegCmp.ks_chart_eq | (intros; apply GlobalTheory.LocRegCmp.ks_chart_eq <;> assumption)
end
