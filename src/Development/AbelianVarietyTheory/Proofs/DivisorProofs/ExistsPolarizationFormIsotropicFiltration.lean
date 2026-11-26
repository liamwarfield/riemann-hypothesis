module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationCrystalFormPerfectSelfAnnihila
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsDetEquivOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationCrystalFormAdjointConjAction
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteSideRealisationsCoefMapDifferRootOfUnity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeepsCuspLatticeNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationFormIsotropicFiltration
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationFormIsotropicFiltration
set_option autoImplicit false
noncomputable section
open Module

namespace GlobalTheory.PolExistsRing

theorem mem_of_annihilates {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    (ψ : LinearMap.BilinForm R V) [hψ : ψ.IsPerfPair] (W W' : Submodule R V) (hc : IsCompl W W')
    [Module.Finite R W'] [Module.Projective R W'] [Module.Finite R (Dual R W)]
    [Module.Projective R (Dual R W)]
    (hrk : ∀ p : PrimeSpectrum R, rankAtStalk W' p = rankAtStalk (Dual R W) p)
    (hiso : ∀ f ∈ W, ∀ g ∈ W, ψ f g = 0) (f : V) (hf : ∀ g ∈ W, ψ f g = 0) : f ∈ W := by
  let Φ : W' →ₗ[R] Dual R W := W.subtype.dualMap ∘ₗ ψ ∘ₗ W'.subtype
  let e := Submodule.prodEquivOfIsCompl W W' hc
  have hdec : ∀ v : V, (((e.symm v).1 : W) : V) + ((e.symm v).2 : V) = v := fun v ↦ by
    rw [← Submodule.coe_prodEquivOfIsCompl' W W' hc, LinearEquiv.apply_symm_apply]
  have hΦ' : ∀ v : V, ∀ g : W, Φ (e.symm v).2 g = ψ v g := by
    intro v g
    have h := congrArg (fun u ↦ ψ u g) (hdec v)
    simp only [map_add (f := _), LinearMap.add_apply] at h
    rw [hiso _ (Submodule.coe_mem _) g g.2, zero_add] at h
    simpa [Φ] using h
  have hΦ : Function.Surjective Φ := by
    intro l
    obtain ⟨v, hv⟩ := hψ.bijective_left.2 (l ∘ₗ W.projectionOnto W' hc)
    refine ⟨(e.symm v).2, LinearMap.ext fun g ↦ ?_⟩
    rw [hΦ' v g, hv]
    simp
  obtain ⟨s, hs⟩ := Module.projective_lifting_property Φ LinearMap.id hΦ
  have hsinj : Function.Injective s := fun x y h ↦ by
    have := congrArg Φ h
    rwa [← LinearMap.comp_apply, hs, ← LinearMap.comp_apply, hs] at this
  have hc2 : IsCompl (LinearMap.range s) (LinearMap.ker Φ) := by
    have h := LinearMap.isCompl_of_proj (f := s.rangeRestrict ∘ₗ Φ) (fun x ↦ by
      obtain ⟨_, y, rfl⟩ := x
      apply Subtype.ext
      simp only [LinearMap.comp_apply, LinearMap.codRestrict_apply]
      rw [← LinearMap.comp_apply Φ s, hs, LinearMap.id_apply])
    have hk : LinearMap.ker s.rangeRestrict = ⊥ := by
      rw [LinearMap.ker_rangeRestrict]; exact LinearMap.ker_eq_bot.2 hsinj
    rwa [LinearMap.ker_comp_of_ker_eq_bot _ hk] at h
  let ep := Submodule.prodEquivOfIsCompl _ _ hc2
  let es : Dual R W ≃ₗ[R] LinearMap.range s := LinearEquiv.ofInjective s hsinj
  haveI : Module.Finite R (LinearMap.range s) := Module.Finite.equiv es
  haveI : Module.Projective R (LinearMap.range s) := Module.Projective.of_equiv es
  let pr : W' →ₗ[R] LinearMap.ker Φ := LinearMap.snd R _ _ ∘ₗ ep.symm.toLinearMap
  have hpr : pr ∘ₗ (LinearMap.ker Φ).subtype = LinearMap.id := LinearMap.ext fun x ↦ by
    simp [pr, ep, Submodule.prodEquivOfIsCompl_symm_apply_right]
  haveI : Module.Finite R (LinearMap.ker Φ) :=
    Module.Finite.of_surjective pr (fun x ↦ ⟨x, by simpa using congrArg (fun m ↦ m x) hpr⟩)
  haveI : Module.Projective R (LinearMap.ker Φ) := Module.Projective.of_split _ _ hpr
  have hr0 : rankAtStalk (R := R) (LinearMap.ker Φ) = 0 := by
    have h1 := rankAtStalk_eq_of_equiv ep
    rw [rankAtStalk_prod, rankAtStalk_eq_of_equiv es.symm] at h1
    funext p
    have := congrFun h1 p
    simp only [Pi.add_apply] at this
    rw [hrk p] at this
    simp only [Pi.zero_apply]
    omega
  haveI := (rankAtStalk_eq_zero_iff_subsingleton).1 hr0
  have hb : (e.symm f).2 ∈ LinearMap.ker Φ := LinearMap.mem_ker.2 (LinearMap.ext fun g ↦ by
    rw [hΦ' f g]; exact hf g g.2)
  have h0 : (e.symm f).2 = 0 := by
    have := Subsingleton.elim (⟨_, hb⟩ : LinearMap.ker Φ) 0
    simpa using congrArg Subtype.val this
  rw [← hdec f, h0]
  simp

theorem mem_of_annihilates_dual {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (ψ : LinearMap.BilinForm R (Dual R M)) [ψ.IsPerfPair] (F N : Submodule R M) (hc : IsCompl F N)
    [Module.Finite R M] [Module.Projective R M] [Module.Finite R F] [Module.Projective R F] (g : ℕ)
    (hM : ∀ p : PrimeSpectrum R, rankAtStalk M p = 2 * g)
    (hF : ∀ p : PrimeSpectrum R, rankAtStalk F p = g)
    (hiso : ∀ f ∈ F.dualAnnihilator, ∀ h ∈ F.dualAnnihilator, ψ f h = 0) (f : Dual R M)
    (hf : ∀ h ∈ F.dualAnnihilator, ψ f h = 0) : f ∈ F.dualAnnihilator := by
  let e := Submodule.prodEquivOfIsCompl F N hc
  have hdec : ∀ x : M, (((e.symm x).1 : F) : M) + ((e.symm x).2 : M) = x := fun x ↦ by
    rw [← Submodule.coe_prodEquivOfIsCompl' F N hc, LinearEquiv.apply_symm_apply]
  have hc' : IsCompl F.dualAnnihilator N.dualAnnihilator := by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro φ ⟨h1, h2⟩
      rw [Submodule.mem_bot]
      refine LinearMap.ext fun x ↦ ?_
      rw [← hdec x, map_add (f := _), (Submodule.mem_dualAnnihilator _).1 h1 _ (Submodule.coe_mem _),
        (Submodule.mem_dualAnnihilator _).1 h2 _ (Submodule.coe_mem _)]
      simp
    · rw [codisjoint_iff_le_sup]
      intro φ _
      rw [Submodule.mem_sup]
      refine ⟨φ ∘ₗ N.subtype ∘ₗ LinearMap.snd R F N ∘ₗ e.symm.toLinearMap, ?_,
        φ ∘ₗ F.subtype ∘ₗ LinearMap.fst R F N ∘ₗ e.symm.toLinearMap, ?_, ?_⟩
      · refine (Submodule.mem_dualAnnihilator _).2 fun x hx ↦ ?_
        simp [e]
        rw [Submodule.projection_apply_of_mem_right _ hx, map_zero]
      · refine (Submodule.mem_dualAnnihilator _).2 fun x hx ↦ ?_
        simp [e]
        rw [Submodule.projection_apply_of_mem_right _ hx, map_zero]
      · refine LinearMap.ext fun x ↦ ?_
        conv_rhs => rw [← hdec x]
        simp [add_comm]
  let eW' : Dual R F ≃ₗ[R] N.dualAnnihilator :=
    (Submodule.quotientEquivOfIsCompl N F hc.symm).dualMap.trans (Submodule.dualQuotEquivDualAnnihilator N)
  let eW : Dual R N ≃ₗ[R] F.dualAnnihilator :=
    (Submodule.quotientEquivOfIsCompl F N hc).dualMap.trans (Submodule.dualQuotEquivDualAnnihilator F)
  have hpN : (N.projectionOnto F hc.symm) ∘ₗ N.subtype = LinearMap.id :=
    LinearMap.ext fun x ↦ Submodule.projectionOnto_apply_left hc.symm x
  haveI : Module.Projective R N := Module.Projective.of_split _ _ hpN
  haveI : Module.Finite R N := Module.Finite.of_surjective _ (Submodule.projectionOnto_surjective hc.symm)
  let eN : Dual R F.dualAnnihilator ≃ₗ[R] N := eW.dualMap.trans (Module.evalEquiv R N).symm
  haveI : Module.Finite R N.dualAnnihilator := Module.Finite.equiv eW'
  haveI : Module.Projective R N.dualAnnihilator := Module.Projective.of_equiv eW'
  haveI : Module.Finite R (Dual R F.dualAnnihilator) := Module.Finite.equiv eN.symm
  haveI : Module.Projective R (Dual R F.dualAnnihilator) := Module.Projective.of_equiv eN.symm
  refine mem_of_annihilates ψ _ _ hc' (fun p ↦ ?_) hiso f hf
  rw [← rankAtStalk_eq_of_equiv eW', rankAtStalk_eq_of_equiv eN, GlobalTheory.TopExt.rankAtStalk_dual F p, hF p]
  have h1 := congrFun (rankAtStalk_eq_of_equiv e) p
  rw [rankAtStalk_prod, Pi.add_apply, hM p, hF p] at h1
  omega

end GlobalTheory.PolExistsRing

namespace GlobalTheory.PolExistsRing

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
open GlobalTheory.Published GlobalTheory.CatCoh
attribute [local instance] Over.cartesianMonoidalCategory

theorem polForm_exists : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X}
    {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π →
    ∃ ψ : LinearMap.BilinForm S (HdR A), IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧
      (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) ∧ LinearMap.IsPerfPair ψ ∧
      ∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A := by
  intro P E _ _ _ H Dw l Xo S _ x A _ π hπ
  open ReciprocityTheory.ChartRestriction.G.Semi CategoryTheory.Limits
    CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj in
  have hA : IsAbelianScheme A := by
    have hG := ObjDim.isAbelianScheme Xo.univ
    have := hG.comm
    have hcomm : IsCommMonObj A := by
      rw [isCommMonObj_iff_isMulCommutative]
      intro T
      refine ⟨⟨fun x y => Over.OverMorphism.ext (hπ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
      rw [← hπ.2 T x y (pushPt hπ.1.w x) (pushPt hπ.1.w y) rfl rfl,
        ← hπ.2 T y x (pushPt hπ.1.w y) (pushPt hπ.1.w x) rfl rfl, _root_.mul_comm]
    exact ⟨hcomm, MorphismProperty.of_isPullback (P := @Smooth) hπ.1 hG.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hπ.1 hG.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hπ.1 hG.geomConnected⟩
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1
    (ObjDim.smoothOfRelativeDimension Xo.univ)
  obtain ⟨h0, -, -, -, e, he⟩ := P.1 S A _ hA gA
  have hLB : (Xo.univ.t.PP.L.pull π).IsLB := pull_isLB Xo.univ.t.PP.isLB π
  obtain ⟨z, hz, -⟩ := (isChern_existsUnique_and_iso S ⊥ (dp0 S) _ (A.hom ≫ 𝟙 _)).1 _ hLB
  obtain ⟨n, a, b, hab⟩ := GlobalTheory.PolExists.exists_sum_wedge (e.symm z)
  have hm : ∀ c : FirstDeRham (A.hom ≫ 𝟙 _), c ∈ primDR A := fun c ↦ by
    change c ∈ prim (dp0 S) (𝟙 _) A
    rw [show prim (dp0 S) (𝟙 _) A = ⊤ from h0]; trivial
  let a' : Fin n → primDR A := fun k ↦ ⟨a k, hm _⟩
  let b' : Fin n → primDR A := fun k ↦ ⟨b k, hm _⟩
  have hz' : IsChern (dp0 S) (A.hom ≫ 𝟙 _) (Xo.univ.t.PP.L.pull π) (∑ k, cup _ (a' k).1 (b' k).1) := by
    have : z = ∑ k, cup _ (a k) (b k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← e.apply_symm_apply z, ← hab, map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ he _ _
    exact this ▸ hz
  have hpol : IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) (wedgeForm (dp0 S) (𝟙 _) A a' b') :=
    ⟨n, a', b', hz', rfl⟩
  have hK : Out.KTriv A (Xo.univ.t.PP.L.pull π) :=
    kTriv_pull hπ Xo.univ.t.PP.isLB hLB ((isGen_iff _).1 (GlobalTheory.PolExists.isGen_self hLB)) Xo.univ.ktriv
  obtain ⟨hiso, hperf⟩ := P.2.2.2.2 S A _ hA gA _ hLB _ hpol
  have hperf' := hperf hK
  refine ⟨_, hpol, hiso, hperf', fun f hf ↦ ?_⟩

  obtain ⟨hfin, hproj, hrk⟩ := AbelianDeRham.Free.prim P.1 hA gA
  obtain ⟨-, ⟨N, hN⟩, hFfin, hFproj, hFrk⟩ := P.2.1 S A _ hA gA
  exact mem_of_annihilates_dual (wedgeForm (dp0 S) (𝟙 _) A a' b') (PrimitiveSubmodule A) N hN _ hrk hFrk hiso f hf

end GlobalTheory.PolExistsRing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationFormIsotropicFiltrationStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polarization_form_isotropic_filtration : GlobalTheory.Published.AbelianDeRham → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) {S : Type} [CommRing S] {x : Sp S ⟶ Xo.X} {A : Over (Sp S)} [GrpObj A] {π : A.left ⟶ Xo.univ.t.G.left}, IsGrpPullback A Xo.univ.t.G x π → ∃ ψ : LinearMap.BilinForm S (HdR A), IsPolForm (dp0 S) (𝟙 _) A (Xo.univ.t.PP.L.pull π) ψ ∧ (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) ∧ LinearMap.IsPerfPair ψ ∧ ∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A := by
  first | exact @GlobalTheory.PolExistsRing.polForm_exists | exact GlobalTheory.PolExistsRing.polForm_exists | (intros; apply GlobalTheory.PolExistsRing.polForm_exists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmEllipticCurveIsPureHodgeEndomorphismBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmEllipticCurveIsPureHodgeEndomorphismBaseChange
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.PureLift GlobalTheory.DeRham GlobalTheory.Cris GlobalTheory.CatCoh GlobalTheory.GrpTangent
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding epsScale
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PureLift

theorem eq_epsScale_of_isLieComb {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {c : Fin 1 → R}
    {v : Fin 1 → (epsR R ⟶ A)} {w : epsR R ⟶ A} (h : IsLieComb c v w) : w = epsScale (c 0) ≫ v 0 := by
  obtain ⟨u, hu, rfl⟩ := h
  have h1 : (List.ofFn u).prod = u 0 := by simp
  rw [h1]
  apply Over.OverMorphism.ext
  rw [Over.comp_left]
  exact hu 0

theorem push_sub_smul_mem_Fil {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] (hA : LieExact A)
    {v : Fin 1 → (epsR R ⟶ A)} (hv : IsLieBasis v) (W : A ⟶ A) [IsMonHom W] {s : Fin 1 → R}
    (e : IsLieComb s v (v 0 ≫ W)) (y : HdR A) : push (dp0 R) (𝟙 _) W y - s 0 • y ∈ Fil A := by
  obtain ⟨u, hu⟩ := (hA.1 y).exists
  obtain ⟨c, hc, -⟩ := hv.2 u hu.1
  have hu' : u = epsScale (c 0) ≫ v 0 := eq_epsScale_of_isLieComb hc
  have hW : v 0 ≫ W = epsScale (s 0) ≫ v 0 := eq_epsScale_of_isLieComb e
  have key : u ≫ W = epsScale (s 0) ≫ u := by
    rw [hu', Category.assoc, hW, epsScale_mul_assoc, epsScale_mul_assoc, mul_comm]
  have h1 := hu.push W
  rw [key] at h1
  exact h1.sub_mem (hu.smul (s 0))

theorem exists_isPolForm (P : GlobalTheory.Published.AbelianDeRham.Free) {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A]
    {g : ℕ} (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) {L : LB A.left} (hL : L.IsLB) :
    ∃ ψ, IsPolForm (dp0 R) (𝟙 _) A L ψ := by
  obtain ⟨hall, -, -, -, e, he⟩ := P R A g hA hg
  obtain ⟨z, hz⟩ : ∃ z, IsChern (dp0 R) (A.hom ≫ 𝟙 (Sp R)) L z :=
    GlobalTheory.Cris.ChernExists.exists_isChern L hL
  obtain ⟨n, a, b, hab⟩ := GlobalTheory.PolExists.exists_sum_wedge (e.symm z)
  have hmem : ∀ x, x ∈ prim (dp0 R) (𝟙 (Sp R)) A := fun x => by
    rw [show prim (dp0 R) (𝟙 (Sp R)) A = ⊤ from hall]
    exact Submodule.mem_top
  refine ⟨_, n, fun k => ⟨a k, hmem _⟩, fun k => ⟨b k, hmem _⟩, ?_, rfl⟩
  have hz' : z = ∑ k, cup _ (a k) (b k) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e.apply_symm_apply z, ← hab, map_sum]
    exact Finset.sum_congr rfl fun k _ => he _ _
  rw [hz'] at hz
  exact hz

private theorem pGen_pull_refl {X Y : Scheme.{0}} (L : LB X) (hL : L.IsLB) (F : Y ⟶ X) :
    PGen (⟨fun p => (L.pull F).g p.1 p.2⟩ : LB.Iso (L.pull F) (L.pull F)) := by
  intro Z f y j j' k k' h1 h2 h3 h4
  unfold gw
  dsimp only
  have e1 : (f ≫ F) y ∈ L.U j := h1
  have e2 : (f ≫ F) y ∈ L.U j' := h2
  have e3' : F (f y) ∈ L.U (k PUnit.unit) := mem_pull.1 h3
  have e3 : (f ≫ F) y ∈ L.U (k PUnit.unit) := e3'
  have e4' : F (f y) ∈ L.U (k' PUnit.unit) := mem_pull.1 h4
  have e4 : (f ≫ F) y ∈ L.U (k' PUnit.unit) := e4'
  rw [gm_pull_g L F f y (fun _ => j) k (mem_pull.2 h1) h3, gm_pull_g L F f y k k' h3 h4,
    gm_pull_g L F f y (fun _ => j') k' (mem_pull.2 h2) h4]
  have c1 := gm_cocycle hL (f ≫ F) y e1 e2 e4
  have c2 := gm_cocycle hL (f ≫ F) y e1 e4 e3
  have c3 := gm_cocycle hL (f ≫ F) y e3 e4 e3
  have c4 := gm_cocycle hL (f ≫ F) y e3 e3 e3
  have hkk : (gm (f ≫ F) y (L.U (k PUnit.unit) ⊓ L.U (k PUnit.unit))) (L.g (k PUnit.unit) (k PUnit.unit)) = 1 := by
    have h := congrArg (· * ((gm (f ≫ F) y (L.U (k PUnit.unit) ⊓ L.U (k PUnit.unit)))
      (L.g (k PUnit.unit) (k PUnit.unit)))⁻¹) c4
    simpa using h
  have hinv := eq_inv_of_mul_eq_one_right (c3.trans hkk)
  rw [← c2, ← c1, hinv, mul_right_comm]

theorem isPureBC_ell : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (S : Type) [CommRing S] (ω : S) (C : GlobalTheory.CM.Ell H S ω),
    IsPureBC C.P.A (C.act.act (GlobalTheory.CM.wK H)) (1 - ω) ω := by
  intro hP E _ _ _ H S _ ω C
  unfold IsPureBC
  intro R _ f A _ φ hpb W' _ hW'

  haveI : IsCommMonObj A := GlobalTheory.PolPull.isCommMonObj_of_isGrpPullback hpb
  have hA : IsAbelianScheme A := by
    exact ⟨inferInstance, MorphismProperty.of_isPullback (P := @Smooth) hpb.1 C.P.isAb.smooth,
      MorphismProperty.of_isPullback (P := @IsProper) hpb.1 C.P.isAb.proper,
      MorphismProperty.of_isPullback (P := @GeometricallyConnected) hpb.1 C.P.isAb.geomConnected⟩
  have hgG : SmoothOfRelativeDimension 1 C.P.A.hom := by
    have h := C.P.smoothDim
    rw [C.dim] at h
    exact h
  have hgA : SmoothOfRelativeDimension 1 A.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback hpb.1 hgG
  have hLie : LieExact A := (hP.2.1 R A 1 hA hgA).1

  haveI := hgG
  obtain ⟨v', hv', hv'φ⟩ := GlobalTheory.exists_isLieBasis_baseChange S R f C.P.A A φ hpb
    (SmoothOfRelativeDimension.smooth 1 C.P.A.hom) 1 ![C.v] C.basis
  have hu : ∀ i, (v' i).left ≫ φ = spMap (Chart.dualMapR f) ≫ (![C.v] i).left := hv'φ
  have hw : (v' 0 ≫ W').left ≫ φ = spMap (Chart.dualMapR f) ≫ (C.v ≫ C.act.act (GlobalTheory.CM.wK H)).left := by
    rw [Over.comp_left, Category.assoc, hW', ← Category.assoc, hu 0, Over.comp_left, Category.assoc]
    rfl
  have e : IsLieComb (fun i => f (![ω] i)) v' (v' 0 ≫ W') := by
    have he := eq_epsScale_of_isLieComb C.eig
    have hs : spMap (epsScaleR (f ω)) ≫ spMap (Chart.dualMapR f) =
        spMap (Chart.dualMapR f) ≫ spMap (epsScaleR ω) := by
      rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp]
      congr 1
      ext r <;> simp [Chart.dualMapR, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
    have heq : v' 0 ≫ W' = epsScale (f ω) ≫ v' 0 := by
      apply Over.OverMorphism.ext
      apply hpb.1.hom_ext
      · rw [hw, he, Over.comp_left, Over.comp_left, Category.assoc, hu 0]
        change (spMap (Chart.dualMapR f) ≫ spMap (epsScaleR ω)) ≫ C.v.left =
          spMap (epsScaleR (f ω)) ≫ (spMap (Chart.dualMapR f) ≫ C.v.left)
        rw [← hs, Category.assoc]
      · rw [Over.w, Over.w]
    refine ⟨fun _ => epsScale (f ω) ≫ v' 0, ?_, ?_⟩
    · intro i
      fin_cases i
      rfl
    · simpa using heq
  have hquot : ∀ y : HdR A, push (dp0 R) (𝟙 _) W' y - f ω • y ∈ Fil A :=
    fun y => push_sub_smul_mem_Fil hLie hv' W' e y

  have hL' : (C.P.L.pull φ).IsLB := pull_isLB C.P.isLB φ
  obtain ⟨ψ, hψ⟩ := exists_isPolForm hP.1 hA hgA hL'
  obtain ⟨hiso, hperf⟩ := hP.2.2.2.2 R A 1 hA hgA (C.P.L.pull φ) hL' ψ hψ
  have hK : ReciprocityTheory.ChartRestriction.G.Out.KTriv A (C.P.L.pull φ) :=
    kTriv_pull hpb C.P.isLB hL' (pGen_pull_refl C.P.L C.P.isLB φ) C.P.ktriv
  haveI := hperf hK

  obtain ⟨o', ho'⟩ := GlobalTheory.CM.ellPull_exists_oAct hpb C.act
  haveI := o'.hom (GlobalTheory.CM.wK H)
  haveI := o'.hom (1 - GlobalTheory.CM.wK H)
  have hWo : o'.act (GlobalTheory.CM.wK H) = W' := by
    apply Over.OverMorphism.ext
    apply hpb.1.hom_ext
    · rw [ho', hW']
    · rw [Over.w, Over.w]

  have hb : ((1 - GlobalTheory.CM.wK H : GlobalTheory.CM.OK H) : 𝓞 E) = H.bar ((GlobalTheory.CM.wK H : GlobalTheory.CM.OK H) : 𝓞 E) := by
    rw [show ((GlobalTheory.CM.wK H : GlobalTheory.CM.OK H) : 𝓞 E) = H.w0 from rfl, GlobalTheory.CM.kform_bar_w0]
    push_cast
    rfl
  have HG : LBIso (cubeLB C.P.A ![fst C.P.A C.P.A ≫ C.act.act (GlobalTheory.CM.wK H), snd C.P.A C.P.A] C.P.L)
      (cubeLB C.P.A ![fst C.P.A C.P.A, snd C.P.A C.P.A ≫ C.act.act (1 - GlobalTheory.CM.wK H)] C.P.L) := by
    have h := C.adj (GlobalTheory.CM.wK H) (1 - GlobalTheory.CM.wK H) hb
    unfold GlobalTheory.CM.LamEq at h
    simpa only [Category.comp_id] using h
  have HA := GlobalTheory.PolAdjoint.lbIso_cube hpb C.P.L hW' (ho' (1 - GlobalTheory.CM.wK H)) HG
  have hadj : ∀ x y : HdR A, ψ (push (dp0 R) (𝟙 _) W' x) y =
      ψ x (push (dp0 R) (𝟙 _) (o'.act (1 - GlobalTheory.CM.wK H)) y) :=
    GlobalTheory.PolAdjoint.adjoint_of_lbIso hP.1 hA hgA hL' hψ W' (o'.act (1 - GlobalTheory.CM.wK H)) HA
  have hpushb : ∀ y : HdR A, push (dp0 R) (𝟙 _) (o'.act (1 - GlobalTheory.CM.wK H)) y = y - push (dp0 R) (𝟙 _) W' y := by
    intro y
    have h1 : GlobalTheory.DeRham.act (dp0 R) (𝟙 _) o' (1 - GlobalTheory.CM.wK H) = 1 - push (dp0 R) (𝟙 _) W' := by
      set_option synthInstance.maxHeartbeats 200000 in
       rw [map_sub, map_one, GlobalTheory.DeRham.act_apply (dp0 R) (𝟙 _) o' (GlobalTheory.CM.wK H),
        push_congr (dp0 R) (𝟙 _) hWo]
    rw [← GlobalTheory.DeRham.act_apply (dp0 R) (𝟙 _) o' (1 - GlobalTheory.CM.wK H), h1]
    rfl

  have hfil : ∀ x ∈ Fil A, push (dp0 R) (𝟙 _) W' x = f (1 - ω) • x := by
    intro x hx
    have hlie : ∀ y : HdR A, ψ x (push (dp0 R) (𝟙 _) W' y) = f ω * ψ x y := by
      intro y
      have h0 := hiso x hx _ (hquot y)
      rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h0
      exact h0
    have key : ψ (push (dp0 R) (𝟙 _) W' x - f (1 - ω) • x) = 0 := by
      ext y
      rw [LinearMap.map_sub₂, LinearMap.map_smul₂, hadj, hpushb, map_sub, hlie, map_sub, map_one,
        smul_eq_mul, LinearMap.zero_apply]
      ring
    have hinj := (LinearMap.IsPerfPair.bijective_left ψ).1
    have h0 : push (dp0 R) (𝟙 _) W' x - f (1 - ω) • x = 0 := hinj (by rw [key, map_zero])
    exact sub_eq_zero.mp h0
  exact ⟨hfil, hquot⟩

end GlobalTheory.PureLift
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmEllipticCurveIsPureHodgeEndomorphismBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmEllipticCurve_isPureHodgeEndomorphismBaseChange : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Type) [CommRing S] (ω : S) (C : GlobalTheory.CM.Ell H S ω), IsPureBC C.P.A (C.act.act (GlobalTheory.CM.wK H)) (1 - ω) ω := by
  first | exact @GlobalTheory.PureLift.isPureBC_ell | exact GlobalTheory.PureLift.isPureBC_ell | (intros; apply GlobalTheory.PureLift.isPureBC_ell <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulInvPow
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.CombTw

open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

theorem wt_diff_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : Datum H) (u : GlobalTheory.AllWt.Weight Dw) (w₀ : Psi H → ℤ) (m : ℕ) :
    wtOf Dw u 0 - wtOf Dw (u + parWt Dw w₀) m = wtOf Dw (parWt Dw (-w₀)) 0 + m • (-wtOf Dw 0 1) := by
  ext x
  · simp only [Prod.fst_sub, Prod.fst_add, Prod.smul_fst, Prod.fst_neg, Pi.sub_apply, Pi.add_apply, Pi.smul_apply,
      Pi.neg_apply]
    simp only [wtOf, parWt, Pi.zero_apply, Pi.neg_apply, Pi.add_apply, nsmul_eq_mul]
    split_ifs <;> ring
  · simp only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd, Prod.snd_neg]
    simp only [wtOf, nsmul_eq_mul]
    ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}

theorem exists_mul_inv_pow {Z : Comp Xo c} {G₀ G₁ : WTZ E} (s : TwSec U x Z G₀) (t : TwSec U x Z G₁) (m : ℕ) :
    ∃ z : TwSec U x Z (G₀ + m • (-G₁)), z.lo = s.lo - (m : ℝ) • t.hi ∧ z.hi = s.hi - (m : ℝ) • t.lo := by
  induction m with
  | zero => exact ⟨s.copy (by simp), by simp [TwSec.copy], by simp [TwSec.copy]⟩
  | succ n ih =>
    obtain ⟨z, hlo, hhi⟩ := ih
    refine ⟨(z.mul t.symm).copy (by rw [succ_nsmul, add_assoc]), ?_, ?_⟩
    · show z.lo + -t.hi = _
      rw [hlo]; push_cast; rw [add_smul, one_smul]; abel
    · show z.hi + -t.lo = _
      rw [hhi]; push_cast; rw [add_smul, one_smul]; abel

theorem exists_twSec_comb : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (x : ℝ) (B : Finset ℕ) (Z : Comp Xo c) (u : GlobalTheory.AllWt.Weight Dw) (w₀ : Psi H → ℤ) (m : ℕ) (k : HeightOneSpectrum (𝓞 c.F) → ℝ) (s : TwSec U x Z (wtOf Dw (parWt Dw (-w₀)) 0)) (t : TwSec U x Z (wtOf Dw 0 1)), s.hi = s.lo → IntOff B s.lo → IntOff B t.hi → (∀ w, t.hi w - t.lo w ≤ k w) → ∃ z : TwSec U x Z (wtOf Dw u 0 - wtOf Dw (u + parWt Dw w₀) m), IntOff B z.lo ∧ ∀ w, z.hi w - z.lo w ≤ m * k w := by
  intro E _ _ _ H Dw l Xo c r U _ x B Z u w₀ m k s t hs hslo hthi hk
  obtain ⟨z, hlo, hhi⟩ := exists_mul_inv_pow s t m
  refine ⟨z.copy (wt_diff_eq Dw u w₀ m).symm, ?_, ?_⟩
  · show IntOff B z.lo
    rw [hlo]
    intro w hw
    obtain ⟨a, ha⟩ := hslo w hw
    obtain ⟨b, hb⟩ := hthi w hw
    exact ⟨a - m * b, by simp [ha, hb]⟩
  · intro w
    show z.hi w - z.lo w ≤ _
    rw [hhi, hlo]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hs]
    have := hk w
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith

end GlobalTheory.CombTw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstLengthArchSectionEqSmulOfSameWeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstLengthArchSectionEqSmulOfSameWeight
noncomputable section

namespace GlobalTheory.FlatCore

open NumberField IsDedekindDomain Module Formalism.BasicNotions _root_.Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem archSec_exists_eq_smul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ)
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → FnAlgClosed (Xo := Xo) (c := c) →
    ∀ (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) (s t : ArchSec U x Z la), ∃ a : c.F, a ≠ 0 ∧ t.sig = a • s.sig := by
  intro E _ _ _ H Dw l Xo c r U x hU hF Z la s t
  obtain σ : c.F →+* ℂ := c.F.val.toRingHom
  have hσ₀ : GoodEmb c (goodOf c σ) := goodEmb_goodOf c σ
  set V := U (goodOf c σ) with hV

  have hinv : s.inv ∈ suppOn Z := by
    have h := mul_mem_suppOn s.inv (idem_mem_suppOn Z)
    rwa [mul_comm, s.idem_inv] at h
  have hg0 : t.sig * s.inv ∈ secZ Xo c 0 := by
    have h := mul_mem_secZ t.sig_mem s.inv_mem
    rwa [add_neg_cancel] at h
  have hgs : t.sig * s.inv ∈ suppOn Z := mul_mem_suppOn t.sig hinv

  have hb : ∀ z ∈ framesOn V Z, ‖rdU V (t.sig * s.inv) z.1 z.2‖ = t.cInf σ / s.cInf σ := by
    intro z hz
    obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ f : Rul Xo c, homN V x (wtOf Dw la 0) f z = ‖rdU V f z.1 z.2‖ * K := by
      refine ⟨lieFacZ Dw x (wtOf Dw la 0) *
        (V.X z.1).pnorm (modelWt V (wtOf Dw la 0) z.1) (fun _ => 1) z.2, fun f => ?_⟩
      simp only [homN, ptN, ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm, norm_one, one_mul]
      ring
    have ht : ‖rdU V t.sig z.1 z.2‖ * K = t.cInf σ := by
      rw [← hK]
      have h := t.norm_inf σ ▸ Set.mem_image_of_mem (homN V x (wtOf Dw la 0) t.sig) hz
      exact h
    have hs : ‖rdU V s.sig z.1 z.2‖ * K = s.cInf σ := by
      rw [← hK]
      have h := s.norm_inf σ ▸ Set.mem_image_of_mem (homN V x (wtOf Dw la 0) s.sig) hz
      exact h
    have hspos := s.cInf_pos σ
    have hs0 : rdU V s.sig z.1 z.2 ≠ 0 := by
      intro h0
      rw [h0, norm_zero, zero_mul] at hs
      linarith
    have hread : ∀ f g : Rul Xo c, rdU V (f * g) z.1 z.2 = rdU V f z.1 z.2 * rdU V g z.1 z.2 := by
      intro f g
      rw [AllWt.rdU_mul]
      rfl
    have hidem : rdU V (idem Z) z.1 z.2 = 1 := by
      have h := congrArg (fun f => rdU V f z.1 z.2) s.idem_sig
      simp only [hread] at h
      exact (mul_eq_right₀ hs0).mp h
    have hone : rdU V s.sig z.1 z.2 * rdU V s.inv z.1 z.2 = 1 := by
      rw [← hread, s.mul_inv, hidem]
    rw [eq_div_iff hspos.ne', ← hs, hread, norm_mul]
    calc ‖rdU V t.sig z.1 z.2‖ * ‖rdU V s.inv z.1 z.2‖ * (‖rdU V s.sig z.1 z.2‖ * K)
        = ‖rdU V t.sig z.1 z.2‖ * K * ‖rdU V s.sig z.1 z.2 * rdU V s.inv z.1 z.2‖ := by
          rw [norm_mul]; ring
      _ = t.cInf σ := by rw [ht, hone, norm_one, mul_one]
  obtain ⟨a, ha⟩ := exists_eq_smul_idem V hσ₀ (hU _ hσ₀) hF hg0 hgs hb
  have hts : t.sig = s.sig * (t.sig * s.inv) := by
    calc t.sig = idem Z * t.sig := t.idem_sig.symm
      _ = s.sig * s.inv * t.sig := by rw [s.mul_inv]
      _ = s.sig * (t.sig * s.inv) := by ring
  have hsi : s.sig * idem Z = s.sig := by rw [mul_comm]; exact s.idem_sig
  have hta : t.sig = a • s.sig := by
    rw [hts, ha, mul_smul_comm, hsi]
  by_cases ha0 : a = 0
  · refine ⟨1, one_ne_zero, ?_⟩
    have ht0 : t.sig = 0 := by
      set_option synthInstance.maxHeartbeats 200000 in
        rw [hta, ha0, zero_smul]
    have hi0 : idem Z = 0 := by rw [← t.mul_inv, ht0, zero_mul]
    have hs0 : s.sig = 0 := by rw [← s.idem_sig, hi0, zero_mul]
    rw [ht0, hs0, smul_zero]
  · exact ⟨a, ha0, hta⟩

end GlobalTheory.FlatCore
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstLengthArchSectionEqSmulOfSameWeightStatement
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constLengthArchSection_eq_smul_of_same_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), (∀ σ, GoodEmb c σ → IsUnf (U σ)) → FnAlgClosed (Xo := Xo) (c := c) → ∀ (Z : Comp Xo c) (la : GlobalTheory.AllWt.Weight Dw) (s t : ArchSec U x Z la), ∃ a : c.F, a ≠ 0 ∧ t.sig = a • s.sig := by
  first | exact @GlobalTheory.FlatCore.archSec_exists_eq_smul | exact GlobalTheory.FlatCore.archSec_exists_eq_smul | (intros; apply GlobalTheory.FlatCore.archSec_exists_eq_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryRepresentativesThetaCompatible
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameStabiliserMapsToCompletedLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameStabiliserMapsToCompletedLattice
open NumberField
open scoped TensorProduct Matrix

namespace GlobalTheory

theorem stab_hatL_mapsTo {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    Formalism.L2.DIV.IsFrame β Λ → ∀ x ∈ Formalism.L2.DIV.St β, ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      x.1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  intro hF x hx v hv
  obtain ⟨y, rfl⟩ := hx
  have hw := (hF v).1 hv
  refine (hF _).2 fun i => ?_
  set Y : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F) :=
    (y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)).map (Formalism.L2.Herm.intAf F E).subtype with hY
  have hval : ((Formalism.L2.DIV.frGL β y : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) _) =
      (β : Matrix (Fin n) (Fin n) _) * Y * ((β⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) := by
    simp only [Formalism.L2.DIV.frGL, Formalism.L2.DIV.intGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, Units.val_mul]
    rfl
  have hmv : ((β⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ
      (((Formalism.L2.DIV.frGL β y : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ v) =
      Y *ᵥ (((β⁻¹ : GL (Fin n) _) : Matrix (Fin n) (Fin n) _) *ᵥ v) := by
    rw [hval, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Units.inv_mul, Matrix.one_mul]
  rw [hmv]
  simp only [Matrix.mulVec, dotProduct]
  refine Subring.sum_mem _ fun j _ => Subring.mul_mem _ ?_ (hw j)
  simp only [hY, Matrix.map_apply]
  exact (y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) i j |>.2

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameStabiliserMapsToCompletedLatticeStatement
open NumberField
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameStabiliser_mapsTo_completedLattice : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)), Formalism.L2.DIV.IsFrame β Λ → ∀ x ∈ Formalism.L2.DIV.St β, ∀ v ∈ Formalism.L2.Herm.hatL (F := F) Λ, x.1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  first | exact @GlobalTheory.stab_hatL_mapsTo | exact GlobalTheory.stab_hatL_mapsTo | (intros; apply GlobalTheory.stab_hatL_mapsTo <;> assumption)
end
end

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.MassLinkConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain
open scoped Matrix

theorem mulVec_mem_hatL {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (hβ : Formalism.L2.DIV.IsFrame β Λ)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hx : x ∈ Formalism.L2.DIV.St β)
    (v : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) (hv : v ∈ Formalism.L2.Herm.hatL (F := F) Λ) :
    x.1 *ᵥ v ∈ Formalism.L2.Herm.hatL (F := F) Λ :=
  GlobalTheory.T.frameStabiliser_mapsTo_completedLattice β Λ hβ x hx v hv

theorem mulVec_mem_hat (D : D7) {n : ℕ} (β : GL (Fin n) (Formalism.IndefR.Lev.EAf D))
    (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (hβ : Formalism.L2.DIV.IsFrame β Λ)
    (k : GL (Fin n) (Af D.host.F ⊗[D.host.F] D.host.E))
    (hk : Formalism.UG.bc (Formalism.IndefR.Lev.swapAE D) k ∈ Formalism.L2.DIV.St β)
    (x : Fin n → Af D.host.F ⊗[D.host.F] D.host.E) (hx : x ∈ GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E))) :
    k.1 *ᵥ x ∈
      GlobalTheory.AdLat.hat D.host.F (Λ : Set (Fin n → D.host.E)) := by
  have h1 := GlobalTheory.PrincInLevel.swap_mem_hatL Λ x hx
  have h2 := mulVec_mem_hatL β Λ hβ _ hk _ h1
  have h3 := GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ h2
  convert h3 using 1
  ext i
  simp [Formalism.UG.bc, Formalism.IndefR.Lev.swapAE, Matrix.mulVec, dotProduct,
    RingHom.mapMatrix_apply, Matrix.map_apply, map_sum, map_mul]

end GlobalTheory.MassLinkConj

namespace GlobalTheory.MassLinkConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain
open scoped Matrix

end GlobalTheory.MassLinkConj

namespace GlobalTheory.MassLinkConj
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain
open scoped Matrix


end GlobalTheory.MassLinkConj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoDefiniteBoundGeAnchoredMainTermSubCrudeErrors
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoDefiniteBoundGeAnchoredMainTermSubCrudeErrors
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefArith

theorem sum_laOf_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hq : Dw.q = 0) (hn : Even n) (τ : Psi H) :
    (∑ k, (laOf Dw a n τ k : ℝ)) = (GlobalTheory.DualWeyl.size (part Dw a τ.1) : ℝ) + (Dw.p : ℝ) * n / 2 := by
  have hm : Dw.mult τ.1 = Dw.p := by unfold Datum.mult; rw [if_pos τ.2]
  have hk : ∀ k : Fin (Dw.p + Dw.q), (laOf Dw a n τ k : ℝ) = (a (τ.1, k) : ℝ) + ((n / 2 : ℕ) : ℝ) := by
    intro k
    have h := k.2
    have hlt : (k : ℕ) < Dw.p := by omega
    simp [laOf, weightOf, hlt]
    norm_cast
  simp_rw [hk]
  rw [Finset.sum_add_distrib, Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)) (Dw.p + Dw.q)]
  have hs : (GlobalTheory.DualWeyl.size (part Dw a τ.1) : ℝ) = ∑ i ∈ Finset.range Dw.p, (a (τ.1, i) : ℝ) := by
    unfold GlobalTheory.DualWeyl.size part
    push_cast
    rw [Fin.sum_univ_eq_sum_range (fun i => (a (τ.1, i) : ℝ)) (Dw.mult τ.1), hm]
  rw [hs, hq, add_zero]
  obtain ⟨r, rfl⟩ := hn
  have : (r + r) / 2 = r := by omega
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, this, hq, add_zero]
  push_cast
  ring

end GlobalTheory.DefArith

namespace GlobalTheory.DefArith

theorem two_defBound_ge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n kc : ℕ) (lo : ℝ), Dw.q = 0 → 1 ≤ Dw.p → Even n → -(∑ τ : Psi H, (Dw.p : ℝ) * (anchor Dw a n kc τ : ℝ) * lo) - |lo| * (∑ τ : Psi H, ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)|) - (∑ τ : Psi H, Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ)) - (n : ℝ) * (Fintype.card (Psi H) : ℝ) * (Dw.p : ℝ) * |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E| ≤ 2 * defBound Dw a n (-flatDegVal Dw lo) := by
  intro E _ _ _ H Dw a n kc lo hq hp hn
  have hp0 : (Dw.p : ℝ) ≠ 0 := by
    have : (0 : ℝ) < Dw.p := by exact_mod_cast hp
    exact this.ne'

  have hτ : ∀ τ : Psi H, -((Dw.p : ℝ) * (anchor Dw a n kc τ : ℝ) * lo) -
      |lo| * ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)| - Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ) ≤
      2 * ((((GlobalTheory.DualWeyl.size (part Dw a τ.1) : ℝ)) / Dw.p + (n : ℝ) / 2) * (-flatDegVal Dw lo) -
        Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ) / 2) := by
    intro τ
    have hS := sum_laOf_eq Dw a n hq hn τ
    have hsplit : (∑ k, (laOf Dw a n τ k : ℝ)) =
        (Dw.p : ℝ) * (anchor Dw a n kc τ : ℝ) + ∑ k, ((laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)) := by
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hq, add_zero]
      ring
    have hb : -(|lo| * ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)|) ≤
        -((∑ k, ((laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ))) * lo) := by
      rw [neg_le_neg_iff]
      calc (∑ k, ((laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ))) * lo
          ≤ |(∑ k, ((laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ))) * lo| := le_abs_self _
        _ = |∑ k, ((laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ))| * |lo| := abs_mul _ _
        _ ≤ (∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)|) * |lo| :=
            mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
        _ = |lo| * ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)| := mul_comm _ _
    have he : 2 * ((((GlobalTheory.DualWeyl.size (part Dw a τ.1) : ℝ)) / Dw.p + (n : ℝ) / 2) * (-flatDegVal Dw lo) -
        Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ) / 2) =
        -((∑ k, (laOf Dw a n τ k : ℝ)) * lo) - Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ) := by
      rw [hS]
      unfold flatDegVal
      rw [hq]
      field_simp
      ring
    rw [he, hsplit]
    linarith
  have hlog : 0 < Real.log (2 * Real.pi) := Real.log_pos (by linarith [Real.pi_gt_three])
  have hN : 0 ≤ (n : ℝ) * (Fintype.card (Psi H) : ℝ) * (Dw.p : ℝ) := by positivity
  have hl : -((n : ℝ) * (Fintype.card (Psi H) : ℝ) * (Dw.p : ℝ) * |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E|) ≤
      2 * ((n : ℝ) * ((Fintype.card (Psi H) : ℝ) * Dw.p) * (Real.log (2 * Real.pi) / 4 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E / 2)) := by
    have h1 := le_abs_self (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E)
    have h2 : -|GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E| ≤ Real.log (2 * Real.pi) / 2 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E := by linarith
    have h3 := mul_le_mul_of_nonneg_left h2 hN
    nlinarith
  have hsum := Finset.sum_le_sum fun τ (_ : τ ∈ Finset.univ) => hτ τ
  have eL : -(∑ τ : Psi H, (Dw.p : ℝ) * (anchor Dw a n kc τ : ℝ) * lo) -
      |lo| * (∑ τ : Psi H, ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)|) -
      (∑ τ : Psi H, Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ)) =
      ∑ τ : Psi H, (-((Dw.p : ℝ) * (anchor Dw a n kc τ : ℝ) * lo) -
        |lo| * ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)| - Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.mul_sum]
  have eR : 2 * defBound Dw a n (-flatDegVal Dw lo) =
      ∑ τ : Psi H, 2 * ((((GlobalTheory.DualWeyl.size (part Dw a τ.1) : ℝ)) / Dw.p + (n : ℝ) / 2) * (-flatDegVal Dw lo) -
        Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ) / 2) +
      2 * ((n : ℝ) * ((Fintype.card (Psi H) : ℝ) * Dw.p) * (Real.log (2 * Real.pi) / 4 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E / 2)) := by
    unfold defBound
    rw [mul_add, Finset.mul_sum]
  rw [eL, eR]
  linarith

end GlobalTheory.DefArith
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoDefiniteBoundGeAnchoredMainTermSubCrudeErrorsStatement
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_definiteBound_ge_anchoredMainTerm_sub_crude_errors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n kc : ℕ) (lo : ℝ), Dw.q = 0 → 1 ≤ Dw.p → Even n → -(∑ τ : Psi H, (Dw.p : ℝ) * (anchor Dw a n kc τ : ℝ) * lo) - |lo| * (∑ τ : Psi H, ∑ k, |(laOf Dw a n τ k : ℝ) - (anchor Dw a n kc τ : ℝ)|) - (∑ τ : Psi H, Real.log (GlobalTheory.DualWeyl.dim (part Dw a τ.1) : ℝ)) - (n : ℝ) * (Fintype.card (Psi H) : ℝ) * (Dw.p : ℝ) * |GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E| ≤ 2 * defBound Dw a n (-flatDegVal Dw lo) := by
  first | exact @GlobalTheory.DefArith.two_defBound_ge | exact GlobalTheory.DefArith.two_defBound_ge | (intros; apply GlobalTheory.DefArith.two_defBound_ge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaleRootOfPrint
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp

theorem isScale_pow_eq {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) {c c' : ℂ}
    (h : IsScale Rl v₀ B c) (h' : IsScale Rl v₀ B c') : ∃ k : ℕ, k ≠ 0 ∧ c' ^ k = c ^ k := by
  obtain ⟨gR, cR0, cL0, hT, u, hu, hF⟩ := h
  obtain ⟨gR', cR0', cL0', hT', u', hu', hF'⟩ := h'
  have huu : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  subst huu
  obtain ⟨a, ⟨k, hk, hak⟩, ha⟩ := GlobalTheory.T.definiteSideRealisations_coefMap_differ_rootOfUnity _ _ _ _ _ _ _ _ _ _ _ _ _ hT hT' j
  obtain ⟨F, x, hx⟩ := GlobalTheory.T.exists_coefficientPolynomial_GLFunction_ne_zero (FWT.lamV D j)
  have e1 := hF' F
  rw [ha] at e1
  erw [LinearMap.map_smul, LinearMap.map_smul, hF F] at e1
  have e2 := congrFun e1 x
  simp only [Pi.smul_apply, smul_eq_mul] at e2
  have hc : c' = D.what₂.embLL a * c := by
    have h3 : D.what₂.embLL a * c * coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) x =
        c' * coefFn D.what₂.embLL (FWT.lamV D j) (F : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) x := by
      rw [mul_assoc]; exact e2
    exact (mul_right_cancel₀ hx h3).symm
  refine ⟨k, hk, ?_⟩
  rw [hc, mul_pow, ← map_pow, hak, map_one, one_mul]

end GlobalTheory.BigOn.Exp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairConverse
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.EvZeroUniq

open scoped Classical

theorem proj_zero_mem_adm (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    (LinearMap.proj (R := ℂ) (φ := fun _ : (κ → AF F) => ℂ) 0) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g 0 • (BoundedContinuousFunction.evalCLM ℂ 0).comp
    (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (κ → mixedEmbedding.mixedSpace F) ℂ), fun f => ?_⟩
  have h1 : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((0 : κ → AF F) i).1) = 0 := by
    funext i
    exact map_zero _
  have h2 : (fun i => ((0 : κ → AF F) i).2) = 0 := rfl
  show pureA F f g 0 = _
  rw [pureA, h1, h2]
  simp [mul_comm]

theorem schr_mem_schA {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) {κ : Type} [Fintype κ]
    (w : (κ → AF F) × (κ → AF F)) {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : schr ψ w Φ ∈ schA F κ := by
  have h2 := GlobalTheory.T.addCharDotMul_mem_adelicSchwartzSpace ψ hψ w.2 _ (GlobalTheory.SchwartzTranslate.main F κ w.1 Φ hΦ)
  have : schr ψ w Φ = ψ (⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) • (fun x => ψ (x ⬝ᵥ w.2) * Φ (x + w.1)) := by
    funext x
    simp only [schr, Pi.smul_apply, smul_eq_mul, AddChar.map_add_eq_mul]
    ring
  rw [this]
  exact Submodule.smul_mem _ _ h2

theorem apply_eq_rho {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {Bf : W → W → AF F} {κ : Type} [Fintype κ] (dc : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (f : (κ → AF F) → ℂ)
    (x : κ → AF F) : f x = dc.rho ψ (dc.e.symm (x, 0)) f 0 := by
  simp [Darboux.rho, schr]

theorem rho_apply_zero {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {Bf : W → W → AF F} {κ : Type} [Fintype κ] (dc : Darboux Bf κ) (ψ : AddChar (AF F) ℂ) (f : (κ → AF F) → ℂ)
    (z : W) (hz : (dc.e z).1 = 0) : dc.rho ψ z f 0 = f 0 := by
  simp [Darboux.rho, schr, hz]

end GlobalTheory.EvZeroUniq
end
end
