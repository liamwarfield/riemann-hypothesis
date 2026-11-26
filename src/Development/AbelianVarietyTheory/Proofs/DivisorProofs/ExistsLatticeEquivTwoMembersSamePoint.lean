module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricTorsionSectionOfSpreadThroughLatticeMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalBaseNsmulDegenerationData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedMemberOfRefinedUniformisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelPreservingLatticeIsoOfMembers

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedMemberThroughPointOfModelAbove
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedMemberThroughPointOfModelAbove
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.Cmp.Thru

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_stalkHom {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (z : M.Z) :
    spMap (M.stalkHom z) ≫ M.Z.fromSpecStalk z = M.pt := by
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := CommRingCat.of Ω) M.pt
  have h2 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk (M.pt_specializes (IsLocalRing.closedPoint Ω) z)
  refine Eq.trans ?_ h1
  rw [← h2, ← Category.assoc, ← Spec.map_comp]
  rfl

theorem isFractionRing_stalk {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (z : M.Z) :
    letI : Algebra (M.Z.presheaf.stalk z) Ω := (M.stalkHom z).toAlgebra
    IsFractionRing (M.Z.presheaf.stalk z) Ω := by
  letI : Algebra (M.Z.presheaf.stalk z) Ω := (M.stalkHom z).toAlgebra
  have : FaithfulSMul (M.Z.presheaf.stalk z) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (M.stalkHom_injective z)
  refine IsFractionRing.of_field _ _ fun x => ?_
  obtain ⟨a, b, -, hx⟩ := IsFractionRing.div_surjective (A := M.O z) x
  refine ⟨(M.stalkEquiv z).symm a, (M.stalkEquiv z).symm b, ?_⟩
  have h : ∀ c : M.O z, algebraMap (M.Z.presheaf.stalk z) Ω ((M.stalkEquiv z).symm c) = c := fun c => by
    change M.stalkHom z _ = _
    rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
  rw [h, h, ← hx]
  rfl

theorem exists_cdvr_thru {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] [CharZero Ω]
    (M : RatModel o Ω) (z : M.Z) :
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (φ : M.Z.presheaf.stalk z →+* V)
      (e : Ω →+* FractionRing V), IsAdicComplete (maximalIdeal V) V ∧ CharZero V ∧ IsLocalHom φ ∧
      jK V ≫ spMap φ ≫ M.Z.fromSpecStalk z = spMap e ≫ M.pt := by
  letI : Algebra (M.Z.presheaf.stalk z) Ω := (M.stalkHom z).toAlgebra
  haveI := isFractionRing_stalk M z
  haveI : CharZero (M.Z.presheaf.stalk z) := (M.stalkHom z).charZero
  haveI := M.lft
  haveI : IsLocallyNoetherian (Sp o) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of o)))
  haveI : IsLocallyNoetherian M.Z := LocallyOfFiniteType.isLocallyNoetherian M.s
  obtain ⟨V₀, _, _, _, φ₀, ⟨hdvr, hcpl, hchar⟩, hinj₀, hmax⟩ :=
    GlobalTheory.ClosedPol.exists_cdvr (M.Z.presheaf.stalk z) (maximalIdeal _)
  have hl : IsLocalHom φ₀ := ((IsLocalRing.local_hom_tfae φ₀).out 1 5).2 hmax
  have hg₀ : Function.Injective ((algebraMap V₀ (FractionRing V₀)).comp φ₀) :=
    (IsFractionRing.injective V₀ (FractionRing V₀)).comp hinj₀
  let emb : Ω →+* FractionRing V₀ := IsFractionRing.lift (A := M.Z.presheaf.stalk z) hg₀
  have hemb : ∀ r, emb (M.stalkHom z r) = algebraMap V₀ (FractionRing V₀) (φ₀ r) := fun r =>
    IsFractionRing.lift_algebraMap (A := M.Z.presheaf.stalk z) hg₀ r
  refine ⟨V₀, inferInstance, inferInstance, hdvr, φ₀, emb, hcpl, hchar, hl, ?_⟩
  rw [← spMap_stalkHom, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [show jK V₀ = spMap (algebraMap V₀ (FractionRing V₀)) from rfl, spMap_spMap, spMap_spMap]
  congr 1
  ext r
  exact (hemb r).symm

theorem exists_uMem_thru : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ y : Y.Z, πY y = z₁ → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (_ : IsDiscreteValuationRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) (_ : AddCommGroup X) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔫 : UMem X₁ z₁ act V ev X t δ) (ξ : Sp V ⟶ Y.Z), ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ∧ ξ (closedPoint V) = y := by
  intro g n F W Z i X₁ z₁ act hact Y πY hY y hy
  subst hy
  obtain ⟨U₀, EE, -, -, -, hhom, -⟩ := hY
  haveI := X₁.imm
  haveI : CharZero X₁.Ω₁ := X₁.ar.char
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  obtain ⟨V₀, _, _, hdvr, φ₀, emb, hcpl, hchar, hl₀, hptY⟩ := exists_cdvr_thru Y y
  have hB : GlobalTheory.Mum.Base V₀ := ⟨⟨inferInstance, inferInstance, inferInstance, hcpl⟩, hchar⟩
  have hπ : Y.pt ≫ πY = X₁.M.pt := by
    refine Eq.trans hhom ?_
    exact (congrArg (· ≫ X₁.M.pt) (Spec.map_id _)).trans (Category.id_comp _)
  let s : X₁.M.Z.presheaf.stalk (πY y) →+* Y.Z.presheaf.stalk y := (πY.stalkMap y).hom
  have hs : spMap s ≫ X₁.M.Z.fromSpecStalk (πY y) = Y.Z.fromSpecStalk y ≫ πY :=
    Scheme.SpecMap_stalkMap_fromSpecStalk πY
  haveI hsl : IsLocalHom s := inferInstanceAs (IsLocalHom (πY.stalkMap y).hom)
  let y₀ : Sp (FractionRing V₀) ⟶ F.X := spMap emb ≫ spMap X₁.S.R.val.toRingHom ≫ X₁.u
  obtain ⟨T, f, fK, hf, hfl, hff, hfK, hTy⟩ := GlobalTheory.T.traitExistsAfterFiniteExtension_of_completeDVR g n _ (zetaAway n) F V₀ hB hdvr y₀
  haveI := hfl
  let ψ : Y.Z.presheaf.stalk y →+* T.V := f.comp φ₀
  let ev : X₁.M.Z.presheaf.stalk (πY y) →+* T.V := ψ.comp s
  have hξ : (spMap ψ ≫ Y.Z.fromSpecStalk y) ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk (πY y) := by
    rw [Category.assoc, ← hs, ← Category.assoc, spMap_spMap]
  have hkey : jK T.V ≫ spMap ψ = spMap fK ≫ jK V₀ ≫ spMap φ₀ := by
    rw [show jK T.V = spMap (algebraMap T.V (FractionRing T.V)) from rfl,
      show jK V₀ = spMap (algebraMap V₀ (FractionRing V₀)) from rfl, spMap_spMap, spMap_spMap, spMap_spMap]
    congr 1
    ext a
    simp only [RingHom.comp_apply]
    exact (hfK _).symm
  have hpt' : jK T.V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (πY y) = spMap fK ≫ spMap emb ≫ X₁.M.pt := by
    rw [← hξ, ← hπ, ← Category.assoc (spMap emb), ← hptY, Category.assoc (spMap ψ), ← Category.assoc (jK T.V), hkey]
    simp only [Category.assoc]
  have hreg : RegAt X₁ (πY y) ev := by
    intro a _
    rw [hpt']
    change a ∈ X₁.M.O (X₁.M.pt ((spMap fK ≫ spMap emb) (closedPoint (FractionRing T.V))))
    rw [X₁.M.pt_apply, RatModel.O_genericPoint]
    trivial
  have hcomm : jK T.V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk (πY y) ≫ X₁.π = T.y ≫ i := by
    have := congrArg (· ≫ X₁.π) hpt'
    simp only [Category.assoc] at this
    rw [this, hTy, X₁.comp]
    simp only [y₀, Category.assoc]
  obtain ⟨hmono, hnn, -, -⟩ := GlobalTheory.T.siegelModuliTrait_periods_monomial_posDef g n _ (zetaAway n) F T
  have hCN : IsCN T.V := ⟨inferInstance, inferInstance, T.complete, inferInstance⟩
  haveI hψ : IsLocalHom ψ := RingHom.isLocalHom_comp _ _
  obtain ⟨𝔪, -⟩ := GlobalTheory.T.exists_uniformised_member_of_refined_uniformisation g X₁.one_le n X₁.three_le X₁.odd F Z X₁.z i X₁.proj
    (fun x => ⟨X₁.normalZ.isDomain_stalk x, X₁.normalZ.isIntegrallyClosed_stalk x⟩) X₁.thetaSetup_structureMap_comp X₁.dense W X₁.e8
    X₁.thetaInt X₁ (πY y) act hact T.V
    (Wit.ofDeg T.D.toPre T.D.tau_bimult) 1 ![T.ϖ] ![T.β] (fun k => by fin_cases k; exact T.irr.ne_zero)
    (fun k a b => by fin_cases k; exact T.symm a b) (fun k a => by fin_cases k; exact hnn a) hmono T.V (RingHom.id _)
    hCN Function.injective_id (RingHom.Finite.id T.V) T.D (AddEquiv.refl _) (Wit.refines_ofDeg _ _) T.G T.A T.U T.y T.α T.α₂
    T.semi T.cart T.sq T.lb ev (RingHom.isLocalHom_comp _ _) hreg hcomm
  refine ⟨T.V, inferInstance, inferInstance, inferInstance, inferInstance, ev, _, inferInstance, 1, _, _, 𝔪,
    spMap ψ ≫ Y.Z.fromSpecStalk y, hξ, ?_⟩
  change Y.Z.fromSpecStalk y (spMap ψ (closedPoint T.V)) = y
  have : spMap ψ (closedPoint T.V) = closedPoint (Y.Z.presheaf.stalk y) := IsLocalRing.comap_closedPoint ψ
  rw [this]
  exact Scheme.fromSpecStalk_closedPoint

end GlobalTheory.Poinc.Sep.Cmp.Thru
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisedMemberThroughPointOfModelAboveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformised_member_through_point_of_model_above : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ y : Y.Z, πY y = z₁ → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (_ : IsDiscreteValuationRing V) (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) (_ : AddCommGroup X) (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔫 : UMem X₁ z₁ act V ev X t δ) (ξ : Sp V ⟶ Y.Z), ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ ∧ ξ (closedPoint V) = y := by
  first | exact @GlobalTheory.Poinc.Sep.Cmp.Thru.exists_uMem_thru | exact GlobalTheory.Poinc.Sep.Cmp.Thru.exists_uMem_thru | (intros; apply GlobalTheory.Poinc.Sep.Cmp.Thru.exists_uMem_thru <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberLatticesIsoOfSpecialisingClosedPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricTorsionPointCharacterEqWeilPairingLabel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricTorsionPointCharacterEqWeilPairingLabel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section
namespace GlobalTheory.Poinc.Sep.Spz
open GlobalTheory.TorusExt GlobalTheory.ZH.TorusPerp GlobalTheory.QkNumberField GlobalTheory.TorsionExt

theorem isPrimitiveRoot_map_of_isUnit_order {o K : Type} [CommRing o] [IsDomain o] [CommRing K] [IsDomain K] (φ : o →+* K)
    {m : ℕ} (hm : 0 < m) {q : o} (hq : IsPrimitiveRoot q m) (hu : IsUnit (m : o)) : IsPrimitiveRoot (φ q) m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine IsPrimitiveRoot.mk_of_lt _ hm (by rw [← map_pow, hq.pow_eq_one, map_one]) fun l hl hlt h1 => ?_
  have hp := congrArg φ hq.prod_one_sub_pow_eq_order
  rw [map_prod] at hp
  have hz : ∏ k ∈ Finset.range n, φ (1 - q ^ (k + 1)) = 0 := by
    refine Finset.prod_eq_zero (i := l - 1) (Finset.mem_range.2 (by omega)) ?_
    rw [map_sub, map_one, map_pow, Nat.sub_add_cancel hl, h1, sub_self]
  rw [hz] at hp
  have hu' : IsUnit (φ ((n : o) + 1)) := by
    have := hu.map φ; simpa using this
  exact hu'.ne_zero hp.symm

theorem intCast_eq_of_zpow_eq {K : Type} [Field K] {m : ℕ} [NeZero m] {z : K} (hz : IsPrimitiveRoot z m) {a : ℤ}
    {b : ZMod m} (h : z ^ a = z ^ (b.val : ℤ)) : (a : ZMod m) = b := by
  have hz0 : z ≠ 0 := hz.ne_zero (NeZero.ne m)
  have h1 : z ^ (a - (b.val : ℤ)) = 1 := by rw [zpow_sub₀ hz0, h, div_self (zpow_ne_zero _ hz0)]
  have h2 := (hz.zpow_eq_one_iff_dvd _).1 h1
  have h3 : ((a - (b.val : ℤ) : ℤ) : ZMod m) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 h2
  rw [Int.cast_sub, sub_eq_zero, Int.cast_natCast, ZMod.natCast_zmod_val] at h3
  exact h3

theorem torAt_char_eq_weil : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∃ sg : ℤˣ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (c : 𝔪.D.toPre.X →+ ℤ) (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), TorAt 𝔪.U (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))))) c x → x.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt τ).left → ∀ a mu, 𝔪.YY a mu → ((c (𝔪.e₈ mu) : ℤ) : ZMod (X₁.S.r * X₁.S.N)) = ((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a := by
  intro g n F W Z i X₁ z₁ act
  refine ⟨1, ?_⟩
  intro V _ _ _ ev X _ m t δ 𝔪 τ c x hT hxo a mu hY
  haveI : CharZero V := 𝔪.cn.2.2.2
  have hA : AdmBase V (maximalIdeal V) := ⟨𝔪.cn.1, inferInstance, 𝔪.cn.2.1, 𝔪.cn.2.2.1⟩
  have hL : LL := GlobalTheory.firstFiveLaws
  have hG : GlobalFnsSt := hL.1.globalFns
  have hk : 1 ≤ X₁.S.r * X₁.S.N := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega))
  obtain ⟨τ', q, hτv, hqy, hqt, hqx⟩ := hT
  obtain ⟨p', x', hp'y, hp'x, hx'o⟩ := hY
  have W₁ := weilQkIs_tor hG q p' hqy hqt
  have W₂ := (GlobalTheory.UT.weilQkIs_iff_weilIs hL V (maximalIdeal V) hA 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U
    (AlgebraicClosure (FractionRing V)) _ hk q p' x x' hqx hp'x (τ' (Multiplicative.ofAdd p'.y))).1 W₁
  have := X₁.ρ.P.isAb.comm
  have hy : (TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK =
      spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) := (spMap_comp _ _).symm
  let h : Over.mk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) ⟶ baseOver (Sp X₁.S.R) :=
    Over.homMk ((TFK (R := V) (AlgebraicClosure (FractionRing V))).hom ≫ spMap 𝔪.yK) (by simp)
  have hh : h.left = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) := hy
  have hζ : IsPrimitiveRoot (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) (X₁.S.r * X₁.S.N) :=
    X₁.S.prim.pow (pow_pos hk 2) (pow_two _)
  let c₀ : (X₁.S.R)ˣ := Units.map (algebraMap X₁.o₁ X₁.S.R).toMonoidHom (hζ.isUnit (by omega)).unit
  have w := GlobalTheory.CommPairing.weilIs_pull hG X₁.ρ.P.isAb X₁.ρ.P.isLB h
    (X₁.ρ.weil τ a (c₀ ^ (eStd X₁.S.g _ τ a).val) (by rw [pow_mul, map_pow]; rfl))
  have W₃ := (GlobalTheory.weilIs_iff_of_isGrpPullback_comm _ _ _ _ _ _ _ _ X₁.ρ.P.isLB 𝔪.A.isLB 𝔪.cart ⟨𝔪.wl, 𝔪.wl_gen⟩
    (TFK (R := V) (AlgebraicClosure (FractionRing V))) _
    x x' (h ≫ X₁.ρ.pt τ) (h ≫ X₁.ρ.pt a) _ ?_ ?_).2 w
  · rw [hh, map_unitOn] at W₃
    have e := unitOn_injective (GlobalTheory.CommutatorPairing.weilIs_unique hG 𝔪.A.isAb 𝔪.A.isLB W₂ W₃)
    rw [hp'y] at e
    have e' := congrArg Units.val e
    simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      RingHom.coe_comp, Function.comp_apply, Units.val_pow_eq_pow_val, c₀, IsUnit.unit_spec] at e'
    rw [hτv] at e'
    rw [Units.val_one, one_smul]
    haveI : IsDomain X₁.o₁ := X₁.ar.ded.toIsDomain
    haveI : NeZero (X₁.S.r * X₁.S.N) := ⟨by omega⟩
    have hzp := isPrimitiveRoot_map_of_isUnit_order ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp
      (𝔪.yK.comp (algebraMap X₁.o₁ X₁.S.R))) (by omega) hζ X₁.S.unit
    refine intCast_eq_of_zpow_eq hzp ?_
    rw [zpow_natCast]
    simp only [RingHom.coe_comp, Function.comp_apply, map_pow] at e' ⊢
    exact e'
  · show h.left ≫ (X₁.ρ.pt τ).left = _
    rw [hh, hxo]
  · show h.left ≫ (X₁.ρ.pt a).left = _
    rw [hx'o, hh]

end GlobalTheory.Poinc.Sep.Spz
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricTorsionPointCharacterEqWeilPairingLabelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricTorsionPoint_character_eq_weilPairing_label : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∃ sg : ℤˣ, ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (c : 𝔪.D.toPre.X →+ ℤ) (x : TFK (R := V) (AlgebraicClosure (FractionRing V)) ⟶ 𝔪.A.A), TorAt 𝔪.U (AlgebraicClosure (FractionRing V)) (X₁.S.r * X₁.S.N) (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))))) c x → x.left ≫ 𝔪.φ = spMap ((algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).comp 𝔪.yK) ≫ (X₁.ρ.pt τ).left → ∀ a mu, 𝔪.YY a mu → ((c (𝔪.e₈ mu) : ℤ) : ZMod (X₁.S.r * X₁.S.N)) = ((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.torAt_char_eq_weil | exact GlobalTheory.Poinc.Sep.Spz.torAt_char_eq_weil | (intros; apply GlobalTheory.Poinc.Sep.Spz.torAt_char_eq_weil <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberLatticesIsoOfSpecialisingClosedPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem exists_eq_nsmul_of_forall_dvd {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (L : ℕ) (x : X)
    (h : ∀ c : X →+ ℤ, (L : ℤ) ∣ c x) : ∃ w, x = L • w := by
  let b := Module.Free.chooseBasis ℤ X
  choose w hw using fun k => h (b.coord k).toAddMonoidHom
  refine ⟨∑ k, w k • b k, ?_⟩
  rw [Finset.smul_sum, ← b.sum_repr x]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : b.repr x k = L * w k := hw k
  rw [this, mul_smul, natCast_zsmul]

theorem injective_of_ker_le {X Y : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup Y]
    [Module.Free ℤ Y] (ρ : X →+ Y) (L : ℕ) (hL : 2 ≤ L) (h : ∀ x, ρ x = 0 → ∃ w, x = L • w) : Function.Injective ρ := _root_.GlobalTheory.GSep.Spz.injective_of_ker_le (X := X) (Y := Y) ρ L hL h

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {Y : RatModel X₁.o₁ X₁.Ω₁} {πY : Y.Z ⟶ X₁.M.Z} {U₀ : Y.Z.Opens} {EE : Y.Lat X₁.S.J} (FinalForm : ZHOut X₁.ρ Y U₀ EE)
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
  (𝔫 : UMem X₁ z₁ act V ev X t δ) {ξ : Sp V ⟶ Y.Z}


include 𝔫 in
theorem base_of_uMem : GlobalTheory.Mum.Base V :=
  ⟨⟨𝔫.cn.1, inferInstance, 𝔫.cn.2.1, 𝔫.cn.2.2.1⟩, 𝔫.cn.2.2.2⟩

theorem exists_link (hO : X₁.S.Over₀ Y U₀) (hπ : X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY)
    (hξ : ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) :
    ∃ β : 𝔫.G.left ⟶ FinalForm.G.left, IsGrpPullback 𝔫.G FinalForm.G ξ β ∧
      Link FinalForm (jK V ≫ ξ) (spMap 𝔫.yK) 𝔫.A.A 𝔫.φ (genMap 𝔫.U ≫ β) ∧
      ∀ (f : X₁.ρ.P.A ⟶ X₁.ρ.P.A) (Fm : FinalForm.G ⟶ FinalForm.G), EndOn FinalForm f Fm → ∀ E : EndU 𝔫.U.toUnifPre,
        E.aA.left ≫ 𝔫.φ = 𝔫.φ ≫ f.left → E.aG.left ≫ β = β ≫ Fm.left := by
  have e : (jK V ≫ ξ) ≫ πY = jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ := by rw [Category.assoc, hξ]
  have hreg : ∀ a ∈ X₁.S.R, a ∈ X₁.M.O (πY ((jK V ≫ ξ) (closedPoint (FractionRing V)))) := fun a ha => by
    have := 𝔫.reg a ha
    rw [← e] at this
    exact this
  obtain ⟨O, _, _, _, _, _, _, xO, u, v, h₁, h₂, h₃, h₄⟩ := GlobalTheory.T.exists_normalNoetherianStalk_factor_of_fieldPoint X₁.o₁ X₁.Ω₁ Y hO.normal X₁.S.R (FractionRing V)
    (jK V ≫ ξ) 𝔫.yK (fun a ha => hπ.map_mem_O (hreg a ha)) (fun a => by
      rw [𝔫.yK_eq, ← e]
      exact hπ.val_comp _ _ (hreg a a.2))
  obtain ⟨gm, hgm⟩ := GlobalTheory.T.abelianScheme_pullback_semiAbelian_over_normalDomain X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ Y U₀ EE FinalForm hO.ne O xO u h₁ h₂
  have e₂ : spMap v ≫ spMap u = spMap 𝔫.yK := (GlobalTheory.SpreadTrait.spMap_comp' u v).trans (congrArg spMap h₄)
  obtain ⟨w, hw, hwφ⟩ := GlobalTheory.SpreadTrait.pull_cancel (isGrpPullback_pullback X₁.ρ.P.A (spMap u)) (spMap v)
    (𝔫.cart.congr e₂.symm rfl)
  have hl := hgm.pull FinalForm hw
  rw [h₃, e₂, hwφ] at hl
  obtain ⟨β, hβ, hβg, hE⟩ := GlobalTheory.T.exists_grpPullback_uniformisingGroup_sameGenericFibre Y.Z FinalForm.G FinalForm.semi V (base_of_uMem 𝔫) 𝔫.G 𝔫.semi 𝔫.D 𝔫.A 𝔫.U ξ _ hl.1
  refine ⟨β, hβ, hβg ▸ hl, fun f Fm hf E h => hE E Fm ?_⟩
  have := hl.2.1 f Fm hf _ (𝟙 _) E.aA.left ((Over.w E.aA).trans (Category.id_comp _).symm)
    (h.trans (Category.id_comp _).symm)
  exact this.trans (Category.id_comp _)

theorem yK_algebraMap (hπ : X₁.M.IsHom Y (AlgHom.id X₁.o₁ X₁.Ω₁) πY)
    (hξ : ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) :
    ∃ oV : X₁.o₁ →+* V, ξ ≫ Y.s = spMap oV ∧
      ∀ a, 𝔫.yK (algebraMap X₁.o₁ X₁.S.R a) = algebraMap V (FractionRing V) (oV a) := by
  have h : ξ ≫ Y.s = spMap (Spec.preimage (ξ ≫ Y.s)).hom := (Spec.map_preimage _).symm
  refine ⟨_, h, fun a => ?_⟩
  rw [𝔫.yK_eq, ← hξ]
  refine RatModel.val_algebraMap (σ := (algebraMap V (FractionRing V)).comp (Spec.preimage (ξ ≫ Y.s)).hom) ?_ a
  rw [Category.assoc, Category.assoc, hπ.inducedModelMorphism_comp_structureMap]
  exact (congrArg (jK V ≫ ·) h).trans (GlobalTheory.SpreadTrait.spMap_comp' _ _)

theorem pow_eq_one_of_qkToAkU {K : Type} [Field K] [Algebra (FractionRing V) K] {k : ℕ} {q : QkPt 𝔫.D.toPre K k}
    {x : TFK (R := V) K ⟶ 𝔫.A.A} (h : QkToAkU 𝔫.U.toUnifPre K k q x) : x ^ k = 1 := by
  obtain ⟨w, hw⟩ := 𝔫.U.ext
  exact (h w hw).1

theorem pt_eq_sec {β : 𝔫.G.left ⟶ FinalForm.G.left}
    (hl : Link FinalForm (jK V ≫ ξ) (spMap 𝔫.yK) 𝔫.A.A 𝔫.φ (genMap 𝔫.U ≫ β)) {a : X₁.S.Gam} {Wo : Y.Z.Opens}
    {h : Wo.toScheme ⟶ FinalForm.G.left} (hs : SecOn FinalForm a Wo h) {ξ' : Sp V ⟶ Wo.toScheme} (hξ' : ξ' ≫ Wo.ι = ξ)
    (K : Type) [Field K] [Algebra (FractionRing V) K] (x : TFK (R := V) K ⟶ 𝔫.A.A)
    (hx : x.left ≫ 𝔫.φ = spMap ((algebraMap (FractionRing V) K).comp 𝔫.yK) ≫ (X₁.ρ.pt a).left) :
    x.left ≫ genMap 𝔫.U ≫ β = spMap (algebraMap (FractionRing V) K) ≫ jK V ≫ ξ' ≫ h := by
  have e : x.left ≫ 𝔫.A.A.hom = spMap (algebraMap (FractionRing V) K) := Over.w x
  have := hl.2.2 a Wo h hs _ x.left (spMap (algebraMap (FractionRing V) K) ≫ jK V ≫ ξ') (by
    rw [reassoc_of% e]
    simp only [Category.assoc, hξ']) (by
    rw [reassoc_of% e, hx, ← GlobalTheory.SpreadTrait.spMap_comp', Category.assoc])
  simpa only [Category.assoc] using this

end GlobalTheory.Poinc.Sep.Spz

theorem GlobalTheory.Poinc.Sep.Spz.latTo_of_specializes : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] [IsDiscreteValuationRing V₁] (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (X₀ : Type) [AddCommGroup X₀] (m₁ : ℕ) (t₁ : Fin m₁ → V₁) (δ₁ : Fin m₁ → LinearMap.BilinForm ℤ X₀) (𝔫₁ : UMem X₁ z₁ act V₁ ev₁ X₀ t₁ δ₁) (ξ₁ : Sp V₁ ⟶ Y.Z) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] [IsDiscreteValuationRing V₂] (ev₂ : X₁.M.Z.presheaf.stalk z₁ →+* V₂) (X : Type) [AddCommGroup X] (m₂ : ℕ) (t₂ : Fin m₂ → V₂) (δ₂ : Fin m₂ → LinearMap.BilinForm ℤ X) (𝔫₂ : UMem X₁ z₁ act V₂ ev₂ X t₂ δ₂) (ξ₂ : Sp V₂ ⟶ Y.Z), ξ₁ ≫ πY = spMap ev₁ ≫ X₁.M.Z.fromSpecStalk z₁ → ξ₂ ≫ πY = spMap ev₂ ≫ X₁.M.Z.fromSpecStalk z₁ → ξ₁ (closedPoint V₁) ⤳ ξ₂ (closedPoint V₂) → Cmp.LatTo 𝔫₁ 𝔫₂ := by
  intro g n F W Z i X₁ z₁ act hact Y πY hZ V₁ _ _ _ _ ev₁ X₀ _ m₁ t₁ δ₁ 𝔫₁ ξ₁ V₂ _ _ _ _ ev₂ X _ m₂ t₂ δ₂ 𝔫₂ ξ₂ hξ₁ hξ₂ hsp
  obtain ⟨U₀, EE, ⟨FinalForm⟩, hO, -, hπ, -⟩ := hZ
  obtain ⟨β₁, hβ₁, hl₁, hE₁⟩ := exists_link FinalForm 𝔫₁ hO hπ hξ₁
  obtain ⟨β₂, hβ₂, hl₂, hE₂⟩ := exists_link FinalForm 𝔫₂ hO hπ hξ₂
  obtain ⟨o₁, ho₁, hy₁⟩ := yK_algebraMap 𝔫₁ hπ hξ₁
  obtain ⟨o₂, ho₂, hy₂⟩ := yK_algebraMap 𝔫₂ hπ hξ₂
  have b₁ := base_of_uMem 𝔫₁
  have b₂ := base_of_uMem 𝔫₂
  obtain ⟨ρ, hρ⟩ := GlobalTheory.T.exists_torus_spread_over_trait_specialisation Y.Z FinalForm.G FinalForm.semi V₁ b₁ 𝔫₁.G 𝔫₁.semi 𝔫₁.D 𝔫₁.A 𝔫₁.U ξ₁ β₁ hβ₁ V₂ b₂ 𝔫₂.G 𝔫₂.semi 𝔫₂.D 𝔫₂.A
    𝔫₂.U ξ₂ β₂ hβ₂ inferInstance (by
      haveI := ArithBase.ded (o := X₁.o₁) (Ω := X₁.Ω₁)
      haveI := Y.lft
      exact LocallyOfFiniteType.isLocallyNoetherian Y.s) hsp
  have onto := GlobalTheory.T.torus_spread_lattice_map_surjective Y.Z FinalForm.G FinalForm.semi V₁ b₁ 𝔫₁.G 𝔫₁.semi 𝔫₁.D 𝔫₁.A 𝔫₁.U ξ₁ β₁ hβ₁ V₂ b₂ 𝔫₂.G 𝔫₂.semi 𝔫₂.D 𝔫₂.A
    𝔫₂.U ξ₂ β₂ hβ₂ ρ hρ
  have eqv := GlobalTheory.T.torus_spread_lattice_map_commutes_endomorphisms Y.Z FinalForm.G FinalForm.semi V₁ b₁ 𝔫₁.G 𝔫₁.semi 𝔫₁.D 𝔫₁.A 𝔫₁.U ξ₁ β₁ hβ₁ V₂ b₂ 𝔫₂.G 𝔫₂.semi 𝔫₂.D 𝔫₂.A
    𝔫₂.U ξ₂ β₂ hβ₂ ρ hρ
  have tor := GlobalTheory.T.toricTorsionSection_of_spread_through_latticeMap Y.Z FinalForm.G FinalForm.semi V₁ b₁ 𝔫₁.G 𝔫₁.semi 𝔫₁.D 𝔫₁.A 𝔫₁.U ξ₁ β₁ hβ₁ V₂ b₂ 𝔫₂.G 𝔫₂.semi 𝔫₂.D 𝔫₂.A
    𝔫₂.U ξ₂ β₂ hβ₂ ρ hρ X₁.o₁ Y.s o₁ o₂ ho₁ ho₂
  obtain ⟨tot₁, sur₁, cong₁, -⟩ := GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act V₁ ev₁ X₀ m₁ t₁ δ₁ 𝔫₁
  obtain ⟨tot₂, sur₂, cong₂, -⟩ := GlobalTheory.Poinc.Sep.Labels.yy_hom g n F W Z i X₁ z₁ act V₂ ev₂ X m₂ t₂ δ₂ 𝔫₂
  obtain ⟨x₀, hx₀⟩ := X₁.div z₁
  have int₁ := GlobalTheory.T.dividingThetaConstants_generate_integral_torsion_labels g n F W Z i X₁ z₁ act x₀ hx₀ V₁ ev₁ X₀ m₁ t₁ δ₁ 𝔫₁
  have int₂ := GlobalTheory.T.dividingThetaConstants_generate_integral_torsion_labels g n F W Z i X₁ z₁ act x₀ hx₀ V₂ ev₂ X m₂ t₂ δ₂ 𝔫₂
  obtain ⟨sg, weil⟩ := GlobalTheory.T.toricTorsionPoint_character_eq_weilPairing_label g n F W Z i X₁ z₁ act
  have hL : 2 ≤ X₁.S.r * X₁.S.N := le_trans X₁.S.N_ge (Nat.le_mul_of_pos_left _ X₁.S.r_pos)
  have hζ : (X₁.S.ζ ^ (X₁.S.r * X₁.S.N)) ^ (X₁.S.r * X₁.S.N) = 1 := by
    rw [← pow_mul, ← sq]; exact X₁.S.prim.pow_eq_one

  have hy : πY (ξ₂ (closedPoint V₂)) = z₁ := by
    haveI := 𝔫₂.loc
    have : (ξ₂ ≫ πY) (closedPoint V₂) = z₁ := by
      rw [hξ₂]
      exact (congrArg (X₁.M.Z.fromSpecStalk z₁) (IsLocalRing.comap_closedPoint ev₂)).trans
        Scheme.fromSpecStalk_closedPoint
    exact this
  have hHH : X₁.S.HH X₁.M z₁ ≤ X₁.S.HH Y (ξ₂ (closedPoint V₂)) :=
    AddSubgroup.closure_mono fun a ha => hπ.div (t := X₁.S.th) (hy.symm ▸ ha)

  have lab : ∀ a mu₁ mu₂, 𝔫₁.YY a mu₁ → 𝔫₂.YY a mu₂ →
      ∃ w, 𝔫₁.e₈ mu₁ - ρ (𝔫₂.e₈ mu₂) = (X₁.S.r * X₁.S.N) • w := by
    intro a mu₁ mu₂ h₁ h₂
    refine exists_eq_nsmul_of_forall_dvd _ _ fun c => ?_
    obtain ⟨x₁, hx₁⟩ := GlobalTheory.T.exists_toric_torsion_point_of_lattice_character V₁ b₁ 𝔫₁.G 𝔫₁.semi 𝔫₁.D 𝔫₁.A 𝔫₁.U (AlgebraicClosure (FractionRing V₁))
      (X₁.S.r * X₁.S.N) (algebraMap (FractionRing V₁) _ (algebraMap V₁ _ (o₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))))) (by omega)
      (by rw [← map_pow, ← map_pow, ← map_pow, hζ, map_one, map_one, map_one]) c
    obtain ⟨τ', q, hτ', hq, hq', hQ⟩ := id hx₁
    obtain ⟨τ, hτ⟩ := GlobalTheory.Poinc.IntTerm.torsion_has_label g n F W Z i X₁ z₁ act V₁ ev₁ X₀ m₁ t₁ δ₁ 𝔫₁ x₁ (pow_eq_one_of_qkToAkU 𝔫₁ hQ)
    have hH : τ ∈ X₁.S.HH X₁.M z₁ := (int₁ τ).2 ⟨q, x₁, hq.trans (map_zero _).symm, hQ, hτ⟩
    obtain ⟨Wo, h, hW, hs⟩ := FinalForm.sec _ τ (hHH hH)
    have lift : ∀ {V : Type} [CommRing V] [IsLocalRing V] (ξ : Sp V ⟶ Y.Z), ξ (closedPoint V) ∈ Wo →
        ∃ ξ' : Sp V ⟶ Wo.toScheme, ξ' ≫ Wo.ι = ξ := fun ξ hξ =>
      ⟨IsOpenImmersion.lift Wo.ι ξ (by
        rintro _ ⟨w, rfl⟩
        rw [Scheme.Opens.range_ι]
        exact ((IsLocalRing.specializes_closedPoint w).map ξ.continuous).mem_open Wo.isOpen hξ),
        IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨ξ₁', hξ₁'⟩ := lift ξ₁ (hsp.mem_open Wo.isOpen hW)
    obtain ⟨ξ₂', hξ₂'⟩ := lift ξ₂ hW
    obtain ⟨-, q₂, x₂, -, hQ₂, hx₂'⟩ := tot₂ τ
    have hx₂ := pow_eq_one_of_qkToAkU 𝔫₂ hQ₂
    have ht := tor _ _ (by omega) X₁.S.unit hζ Wo h ξ₁' ξ₂' hs.1 hξ₁' hξ₂' _ _ c x₁ x₂ hx₁
      (pt_eq_sec FinalForm 𝔫₁ hl₁ hs hξ₁' _ x₁ hτ) hx₂ (pt_eq_sec FinalForm 𝔫₂ hl₂ hs hξ₂' _ x₂ hx₂')
    rw [← hy₁] at hx₁
    rw [← hy₂] at ht
    have w₁ := weil V₁ ev₁ X₀ m₁ t₁ δ₁ 𝔫₁ τ c x₁ hx₁ hτ a mu₁ h₁
    have w₂ := weil V₂ ev₂ X m₂ t₂ δ₂ 𝔫₂ τ _ x₂ ht hx₂' a mu₂ h₂
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, map_sub, Int.cast_sub, w₁, sub_eq_zero]
    exact w₂.symm
  have vec : ∀ {X' : Type} [AddCommGroup X'] (mu mu' w : Fin 8 → X'), mu' = mu + (X₁.S.r * X₁.S.N) • w →
      ∀ v, CongMod (X₁.S.r * X₁.S.N) (mu' v) (mu v) := fun mu mu' w h v => ⟨w v, congrFun h v⟩
  have inj : Function.Injective ρ := by
    refine injective_of_ker_le ρ _ hL fun y hy0 => ?_
    obtain ⟨mu, rfl⟩ := 𝔫₂.e₈.surjective y
    obtain ⟨a, ha⟩ := sur₂ mu
    obtain ⟨mu₁, h₁⟩ := tot₁ a
    obtain ⟨w, hw⟩ := lab a mu₁ mu h₁ ha
    have h0 : 𝔫₁.YY a 0 := (cong₁ a mu₁ 0 h₁).2 (vec _ _ (-𝔫₁.e₈.symm w) (𝔫₁.e₈.injective (by
      rw [hy0, sub_zero] at hw
      simp [hw])))
    have h0' := (cong₂ a 0 mu ((int₂ a).1 ((int₁ a).2 h0))).1 ha
    choose w' hw' using h0'
    exact ⟨𝔫₂.e₈ w', by rw [← map_nsmul]; exact congrArg _ (funext fun v => by simpa using hw' v)⟩
  let e := AddEquiv.ofBijective ρ ⟨inj, onto⟩
  let K : (Fin 8 → X₀) ≃+ (Fin 8 → X) := (𝔫₁.e₈.trans e.symm).trans 𝔫₂.e₈.symm
  have hK : ∀ mu, ρ (𝔫₂.e₈ (K mu)) = 𝔫₁.e₈ mu := fun mu => by
    simp only [K, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
    exact e.apply_symm_apply _
  refine ⟨K, fun a' mu => ?_, fun a mu h₁ => ?_⟩
  · have hdet : (W + W.transpose).det = 1 := X₁.e8.2
    have ha : (W + W.transpose) * a' = ((W + W.transpose) * a' * (W + W.transpose).adjugate).transpose.transpose *
        (W + W.transpose) := by
      rw [Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.adjugate_mul, hdet, one_smul, Matrix.mul_one]
    obtain ⟨E₁, h₁, h₁'⟩ := 𝔫₁.equiv _ a' ha
    obtain ⟨E₂, h₂, h₂'⟩ := 𝔫₂.equiv _ a' ha
    obtain ⟨Fm, hF⟩ := GlobalTheory.T.exists_semiAbelianEnd_extending_abelianSchemeEnd X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ Y U₀ EE FinalForm hO.ne _ (hact.isMonHom _)
    apply 𝔫₂.e₈.injective
    apply inj
    rw [hK, ← h₂', eqv Fm E₁ E₂ (hE₁ _ Fm hF E₁ h₁) (hE₂ _ Fm hF E₂ h₂), hK, h₁']
  · obtain ⟨mu₂, h₂⟩ := tot₂ a
    obtain ⟨w, hw⟩ := lab a mu mu₂ h₁ h₂
    obtain ⟨w', rfl⟩ := onto w
    refine (cong₂ a mu₂ _ h₂).2 (vec _ _ (𝔫₂.e₈.symm w') (𝔫₂.e₈.injective (inj ?_)))
    rw [hK, map_add (f := _), map_add (f := _), map_nsmul, map_nsmul, AddEquiv.apply_symm_apply, ← hw, add_sub_cancel]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberLatticesIsoOfSpecialisingClosedPointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberLattices_iso_of_specialising_closedPoints : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] [IsDiscreteValuationRing V₁] (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (X₀ : Type) [AddCommGroup X₀] (m₁ : ℕ) (t₁ : Fin m₁ → V₁) (δ₁ : Fin m₁ → LinearMap.BilinForm ℤ X₀) (𝔫₁ : UMem X₁ z₁ act V₁ ev₁ X₀ t₁ δ₁) (ξ₁ : Sp V₁ ⟶ Y.Z) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] [IsDiscreteValuationRing V₂] (ev₂ : X₁.M.Z.presheaf.stalk z₁ →+* V₂) (X : Type) [AddCommGroup X] (m₂ : ℕ) (t₂ : Fin m₂ → V₂) (δ₂ : Fin m₂ → LinearMap.BilinForm ℤ X) (𝔫₂ : UMem X₁ z₁ act V₂ ev₂ X t₂ δ₂) (ξ₂ : Sp V₂ ⟶ Y.Z), ξ₁ ≫ πY = spMap ev₁ ≫ X₁.M.Z.fromSpecStalk z₁ → ξ₂ ≫ πY = spMap ev₂ ≫ X₁.M.Z.fromSpecStalk z₁ → ξ₁ (closedPoint V₁) ⤳ ξ₂ (closedPoint V₂) → Cmp.LatTo 𝔫₁ 𝔫₂ := by
  first | exact @GlobalTheory.Poinc.Sep.Spz.latTo_of_specializes | exact GlobalTheory.Poinc.Sep.Spz.latTo_of_specializes | (intros; apply GlobalTheory.Poinc.Sep.Spz.latTo_of_specializes <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiabelianExtensionModelAboveThetaSetup
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiabelianExtensionModelAboveThetaSetup
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open Classical

theorem GlobalTheory.Poinc.Sep.Cmp.exists_zhAbove : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ)
    (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i),
    ∃ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY := by
  intro g n F W Z i X₁
  obtain ⟨m, c, hc⟩ := RatModel.exists_isCl_of_isProjOver X₁.projM
  have hc0 : ∃ j, c j ≠ 0 := by
    obtain ⟨j, hj⟩ := hc.1 (genericPoint X₁.M.Z)
    exact ⟨j, hj.1⟩
  obtain ⟨Y, U₀, EE, hO, hdiv, hE, ⟨G⟩⟩ := GlobalTheory.zhSt_holds X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ X₁.big (Fin (m + 1)) c hc0
    (GlobalTheory.ZH.finite_closure_theta_ratios_of_isCl X₁.o₁ X₁.Ω₁ X₁.S X₁.M (Fin (m + 1)) c hc)
  obtain ⟨q, hq⟩ := hc.exists_isHom (M' := Y) (φ := AlgHom.id X₁.o₁ X₁.Ω₁) hdiv
  have hYp : IsProper Y.s := ((GlobalTheory.isProjOver_iff_isProper_and_exists_isAmpleLB _).1 hO.proj).1
  have hsep : IsSeparated X₁.M.s := X₁.M.sep
  have hqp : IsProper q := by
    haveI : IsProper (q ≫ X₁.M.s) := by rw [hq.inducedModelMorphism_comp_structureMap]; exact hYp
    exact IsProper.of_comp q X₁.M.s
  exact ⟨Y, q, U₀, EE, ⟨G⟩, hO, hE, hq, hqp⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiabelianExtensionModelAboveThetaSetupStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiabelianExtensionModel_above_thetaSetup : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), ∃ (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY := by
  first | exact @GlobalTheory.Poinc.Sep.Cmp.exists_zhAbove | exact GlobalTheory.Poinc.Sep.Cmp.exists_zhAbove | (intros; apply GlobalTheory.Poinc.Sep.Cmp.exists_zhAbove <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeEquivTwoMembersSamePoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.Cmp

section Glue

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

theorem LatTo.symm' {V₀ : Type} [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] {ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀}
    {X₀ : Type} [AddCommGroup X₀] {m₀ : ℕ} {t₀ : Fin m₀ → V₀} {δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    {𝔪₀ : UMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀} {𝔪 : UMem X₁ z₁ act V ev X t δ} (h : LatTo 𝔪₀ 𝔪) : LatTo 𝔪 𝔪₀ := by
  obtain ⟨K, hK, hl⟩ := h
  have y₀ := GlobalTheory.T.surjective_labelHom_lattice_mod_level_thetaMember g n F W Z i X₁ z₁ act V₀ ev₀ X₀ m₀ t₀ δ₀ 𝔪₀
  have y₁ := GlobalTheory.T.surjective_labelHom_lattice_mod_level_thetaMember g n F W Z i X₁ z₁ act V ev X m t δ 𝔪
  refine ⟨K.symm, fun a mu => K.injective ?_, fun a mu' h => ?_⟩
  · rw [K.apply_symm_apply, hK]
    simp only [K.apply_symm_apply]
  · obtain ⟨mu, hmu⟩ := y₀.1 a
    have hc := (y₁.2.2.1 a (K mu) mu' (hl a mu hmu)).1 h
    refine (y₀.2.2.1 a mu (K.symm mu') hmu).2 fun v => ?_
    choose w hw using hc
    have e : mu' = K mu + (X₁.S.r * X₁.S.N) • w := funext fun u => by simpa using hw u
    refine ⟨K.symm w v, ?_⟩
    have e' : K.symm mu' = mu + (X₁.S.r * X₁.S.N) • K.symm w := by
      rw [e, map_add (f := _), K.symm_apply_apply, map_nsmul]
    exact congrFun e' v

theorem closed_over {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    [IsLocalHom ev] {Y : Scheme.{0}} {πY : Y ⟶ X₁.M.Z} {ξ : Sp V ⟶ Y}
    (h : ξ ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) : πY (ξ (closedPoint V)) = z₁ := by
  change (ξ ≫ πY) (closedPoint V) = z₁
  rw [h]
  change X₁.M.Z.fromSpecStalk z₁ (spMap ev (closedPoint V)) = z₁
  rw [show spMap ev (closedPoint V) = closedPoint _ from IsLocalRing.comap_closedPoint ev]
  exact Scheme.fromSpecStalk_closedPoint

end Glue

section Main

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}

theorem latTo_all (hact : IsAct X₁ act)
    {V₀ : Type} [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] {ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀}
    {X₀ : Type} [AddCommGroup X₀] {m₀ : ℕ} {t₀ : Fin m₀ → V₀} {δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀}
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (𝔪₀ : UMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀) (𝔪 : UMem X₁ z₁ act V ev X t δ) : LatTo 𝔪₀ 𝔪 := by
  obtain ⟨Y, πY, hY⟩ := GlobalTheory.T.exists_semiabelianExtensionModel_above_thetaSetup g n F W Z i X₁
  have lift : ∀ {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
      {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
      (𝔪 : UMem X₁ z₁ act V ev X t δ), ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsLocalRing V')
        (_ : IsDiscreteValuationRing V') (ev' : X₁.M.Z.presheaf.stalk z₁ →+* V') (m' : ℕ) (t' : Fin m' → V')
        (δ' : Fin m' → LinearMap.BilinForm ℤ X) (𝔫 : UMem X₁ z₁ act V' ev' X t' δ') (ξ : Sp V' ⟶ Y.Z),
        ξ ≫ πY = spMap ev' ≫ X₁.M.Z.fromSpecStalk z₁ ∧ LatTo 𝔪 𝔫 := by
    intro V _ _ _ ev X _ m t δ 𝔪
    obtain ⟨V₁, _, _, _, _, j₁, hcn₁, hj₁, hl₁⟩ := GlobalTheory.T.exists_completeDVR_local_embedding_normal V 𝔪.cn
    haveI := 𝔪.loc
    haveI := hl₁
    obtain ⟨V₂, _, _, _, _, j₂, ξ, hcn₂, hj₂, hl₂, hξ⟩ :=
      GlobalTheory.T.exists_trait_lift_semiabelianExtensionModel g n F W Z i X₁ z₁ Y πY hY V₁ (j₁.comp ev) inferInstance hcn₁
    haveI := hl₂
    obtain ⟨m', t', δ', 𝔫, hyy⟩ :=
      GlobalTheory.T.member_baseChange_injective_local_complete_normal g n F W Z i X₁ z₁ act hact V ev X m t δ 𝔪 V₂ (j₂.comp j₁) hcn₂ (hj₂.comp hj₁) inferInstance
    exact ⟨V₂, inferInstance, inferInstance, inferInstance, inferInstance, (j₂.comp j₁).comp ev, m', t', δ', 𝔫, ξ, hξ,
      AddEquiv.refl _, fun _ _ => rfl, hyy⟩
  obtain ⟨W₀, _, _, _, _, e₀, n₀, s₀, d₀, 𝔫₀, ξ₀, hξ₀, a₀⟩ := lift 𝔪₀
  obtain ⟨W₁, _, _, _, _, e₁, n₁, s₁, d₁, 𝔫₁, ξ₁, hξ₁, a₁⟩ := lift 𝔪
  let P : Y.Z → Prop := fun y => ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V]
    (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V)
    (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔠 : UMem X₁ z₁ act V ev X t δ) (ξc : Sp V ⟶ Y.Z),
    ξc ≫ πY = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ → ξc (closedPoint V) = y → LatTo 𝔫₀ 𝔠
  have step : ∀ a b : Y.Z, πY a = z₁ → πY b = z₁ → a ⤳ b → (P a ↔ P b) := by
    intro a b ha hb hab
    obtain ⟨Va, _, _, _, _, eva, Xa, _, ma, ta, δa, 𝔠a, ξa, hξa, hca⟩ :=
      GlobalTheory.T.exists_uniformised_member_through_point_of_model_above g n F W Z i X₁ z₁ act hact Y πY hY a ha
    obtain ⟨Vb, _, _, _, _, evb, Xb, _, mb, tb, δb, 𝔠b, ξb, hξb, hcb⟩ :=
      GlobalTheory.T.exists_uniformised_member_through_point_of_model_above g n F W Z i X₁ z₁ act hact Y πY hY b hb
    constructor
    · intro hP V _ _ _ _ ev X _ m t δ 𝔠 ξc hξc hc
      have h1 := hP Va eva Xa ma ta δa 𝔠a ξa hξa hca
      have h2 := GlobalTheory.T.memberLattices_iso_of_specialising_closedPoints g n F W Z i X₁ z₁ act hact Y πY hY Va eva Xa ma ta δa 𝔠a ξa V ev X m t δ 𝔠 ξc hξa hξc
        (by rw [hca, hc]; exact hab)
      exact h1.trans h2
    · intro hP V _ _ _ _ ev X _ m t δ 𝔠 ξc hξc hc
      have h1 := hP Vb evb Xb mb tb δb 𝔠b ξb hξb hcb
      have h2 := GlobalTheory.T.memberLattices_iso_of_specialising_closedPoints g n F W Z i X₁ z₁ act hact Y πY hY V ev X m t δ 𝔠 ξc Vb evb Xb mb tb δb 𝔠b ξb hξc hξb
        (by rw [hc, hcb]; exact hab)
      exact h1.trans h2.symm'
  have key : ∀ y y' : Y.Z, Relation.EqvGen (fun a b : Y.Z => πY a = z₁ ∧ πY b = z₁ ∧ a ⤳ b) y y' → (P y ↔ P y') := by
    intro y y' h
    induction h with
    | rel a b hr => exact step a b hr.1 hr.2.1 hr.2.2
    | refl => exact Iff.rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2
  haveI := 𝔫₀.loc
  haveI := 𝔫₁.loc
  have c₀ : πY (ξ₀ (closedPoint W₀)) = z₁ := closed_over hξ₀
  have c₁ : πY (ξ₁ (closedPoint W₁)) = z₁ := closed_over hξ₁
  have P0 : P (ξ₀ (closedPoint W₀)) := by
    intro V _ _ _ _ ev X _ m t δ 𝔠 ξc hξc hc
    exact GlobalTheory.T.memberLattices_iso_of_specialising_closedPoints g n F W Z i X₁ z₁ act hact Y πY hY W₀ e₀ X₀ n₀ s₀ d₀ 𝔫₀ ξ₀ V ev X m t δ 𝔠 ξc hξ₀ hξc
      (by rw [hc])
  have P1 := (key _ _ (GlobalTheory.T.semiabelianModel_fibre_specialization_chain g n F W Z i X₁ z₁ Y πY hY _ _ c₀ c₁)).1 P0
  exact a₀.trans ((P1 W₁ e₁ X n₁ s₁ d₁ 𝔫₁ ξ₁ hξ₁ rfl).trans a₁.symm')

end Main

theorem exists_latEquiv_of_members : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (V₀ : Type) [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] (ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀) (X₀ : Type) [AddCommGroup X₀] (m₀ : ℕ) (t₀ : Fin m₀ → V₀) (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (𝔪₀ : UMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∃ K : (Fin 8 → X₀) ≃+ (Fin 8 → X), (∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (mu : Fin 8 → X₀), K (fun u => ∑ v, a u v • mu v) = fun u => ∑ v, a u v • K mu v) ∧ ∀ a mu, 𝔪₀.YY a mu → 𝔪.YY a (K mu) := by
  intro g _ n _ _ F Z z i _ _ _ _ _ W _ _ X₁ z₁ act hact V₀ _ _ _ ev₀ X₀ _ m₀ t₀ δ₀ 𝔪₀ V _ _ _ ev X _ m t δ 𝔪
  exact latTo_all hact 𝔪₀ 𝔪

end GlobalTheory.Poinc.Sep.Cmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLatticeEquivTwoMembersSamePointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_equiv_two_members_same_point : ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) [IsOpenImmersion i], IsProjOver z → IsNormalScheme Z → i ≫ z = F.s → Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i → ∀ (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsAct X₁ act → ∀ (V₀ : Type) [CommRing V₀] [IsDomain V₀] [IsLocalRing V₀] (ev₀ : X₁.M.Z.presheaf.stalk z₁ →+* V₀) (X₀ : Type) [AddCommGroup X₀] (m₀ : ℕ) (t₀ : Fin m₀ → V₀) (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (𝔪₀ : UMem X₁ z₁ act V₀ ev₀ X₀ t₀ δ₀) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∃ K : (Fin 8 → X₀) ≃+ (Fin 8 → X), (∀ (a : Matrix (Fin 8) (Fin 8) ℤ) (mu : Fin 8 → X₀), K (fun u => ∑ v, a u v • mu v) = fun u => ∑ v, a u v • K mu v) ∧ ∀ a mu, 𝔪₀.YY a mu → 𝔪.YY a (K mu) := by
  first | exact @GlobalTheory.Poinc.Sep.Cmp.exists_latEquiv_of_members | exact GlobalTheory.Poinc.Sep.Cmp.exists_latEquiv_of_members | (intros; apply GlobalTheory.Poinc.Sep.Cmp.exists_latEquiv_of_members <;> assumption)
end
