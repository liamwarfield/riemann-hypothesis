module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TestFieldFiniteOverPadic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfPowerSeriesArcsOverAlgClosed
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTestDimensionsAndSplitFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTestPowerIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTestPowerIntegral
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.MultInt

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem pow_left_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (G : Over S) [GrpObj G] {T : Over S'} {T₀ : Over S}
    (h : T.left ⟶ T₀.left) (hh : h ≫ T₀.hom = T.hom ≫ f) (x : T ⟶ (Over.pullback f).obj G) (x₀ : T₀ ⟶ G)
    (hx : h ≫ x₀.left = x.left ≫ pullback.fst G.hom f) (k : ℕ) :
    h ≫ (x₀ ^ k).left = (x ^ k).left ≫ pullback.fst G.hom f := by
  let h' : Over.mk (T.hom ≫ f) ⟶ T₀ := Over.homMk h hh
  have e : TorsionLift.ptsEquiv f G T _ rfl x = h' ≫ x₀ :=
    Over.OverMorphism.ext ((TorsionLift.ptsEquiv_left f G T _ rfl x).trans hx.symm)
  rw [← TorsionLift.ptsEquiv_left f G T _ rfl, map_pow, e, ← comp_pow]
  rfl

theorem exists_finite_factor {p : ℕ} [Fact p.Prime] {V : Type} [CommRing V] {X : Scheme.{0}} (s : X ⟶ Sp V)
    [LocallyOfFiniteType s] (φ : V →+* PadicAlgCl p) (K₀ : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K₀] (hφ : ∀ v, φ v ∈ K₀) (x : Sp (PadicAlgCl p) ⟶ X) (hx : x ≫ s = spMap φ) :
    ∃ K : IntermediateField ℚ_[p] (PadicAlgCl p), K₀ ≤ K ∧ FiniteDimensional ℚ_[p] K ∧
      ∃ x' : Sp K ⟶ X, spMap K.val.toRingHom ≫ x' = x := by
  obtain ⟨U, hU, ψ', hψ'⟩ := exists_affineOpen_factor_of_isLocalRing x
  let A : Type := Γ(X, U)
  let i : Sp A ⟶ X := hU.fromSpec
  haveI : IsOpenImmersion i := hU.isOpenImmersion_fromSpec
  let ψ : A →+* PadicAlgCl p := ψ'.hom
  have hψ : spMap ψ ≫ i = x := hψ'
  obtain ⟨α, hα⟩ : ∃ α : V →+* A, spMap α = i ≫ s := by
    obtain ⟨α, hα⟩ := Spec.map_surjective (i ≫ s)
    exact ⟨α.hom, hα⟩
  have hft : α.FiniteType := by
    have : LocallyOfFiniteType (spMap α) := by rw [hα]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).1 this
  have hψα : ψ.comp α = φ := by
    refine congrArg CommRingCat.Hom.hom (Spec.map_injective (?_ : spMap _ = spMap _))
    rw [← spMap_comp_spMap, hα, ← Category.assoc, hψ, hx]
  letI := α.toAlgebra
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (self := hft)
  haveI : Finite (ψ '' (t : Set A)) := (t.finite_toSet.image _).to_subtype
  haveI : FiniteDimensional ℚ_[p] (IntermediateField.adjoin ℚ_[p] (ψ '' (t : Set A))) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let K : IntermediateField ℚ_[p] (PadicAlgCl p) := K₀ ⊔ IntermediateField.adjoin ℚ_[p] (ψ '' (t : Set A))
  have hk : K₀ ≤ K := le_sup_left
  have hmem : ∀ x, ψ x ∈ K := by
    intro x
    have hx : x ∈ Algebra.adjoin V (t : Set A) := ht ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      exact (le_sup_right : _ ≤ K) (IntermediateField.subset_adjoin _ _ ⟨x, hx, rfl⟩)
    | algebraMap r =>
      change (ψ.comp α) r ∈ K
      rw [hψα]; exact hk (hφ r)
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨K, hk, IntermediateField.finiteDimensional_sup _ _, spMap (ψ.codRestrict K hmem) ≫ i, ?_⟩
  rw [← Category.assoc, spMap_comp_spMap]
  exact hψ

theorem isProjOver_snd_snd {V F O K : Type} [CommRing V] [CommRing F] [CommRing O] [CommRing K] {X : Scheme.{0}}
    (s : X ⟶ Sp V) (α : V →+* F) (β : F →+* K) (ψ : V →+* O) (χ : O →+* K) (h : β.comp α = χ.comp ψ)
    (hp : IsProjOver (pullback.snd s (spMap α))) :
    IsProjOver (pullback.snd (pullback.snd s (spMap ψ)) (spMap χ)) := by
  have e : spMap χ ≫ spMap ψ = spMap β ≫ spMap α := by rw [spMap_comp_spMap, spMap_comp_spMap, h]
  have H := (IsPullback.of_hasPullback (pullback.snd s (spMap ψ)) (spMap χ)).paste_horiz
    (IsPullback.of_hasPullback s (spMap ψ))
  rw [e] at H
  exact ProjSpace.isProjOver_of_isPullback_spMap β
    (IsPullback.of_right' H (IsPullback.of_hasPullback s (spMap α))) hp

end GlobalTheory.ZH.MultInt

namespace GlobalTheory.ZH
open MultInt

theorem exists_int_pow : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a : u.PtC), ∃ k : ℕ, 1 ≤ k ∧ u.Int (a ^ k) := by
  intro _ o Ω _ _ _ _ S ρ p _ y₀ u a
  obtain ⟨-, -, -, K₀, hK₀, hr⟩ := GlobalTheory.T.testField_finite_over_padic o Ω S ρ p y₀ u
  haveI := u.semi.smooth
  haveI := u.semi.separated
  let θ : FractionRing u.V →+* PadicAlgCl p := algebraMap _ _
  let α : u.V →+* FractionRing u.V := algebraMap _ _
  have hθ : ∀ v, θ v ∈ K₀ := fun v => show θ v ∈ (K₀ : Set _) from hr ▸ ⟨v, rfl⟩
  have ha : u.toG a ≫ u.G.hom = spMap (θ.comp α) := by
    have := Over.w a
    rw [← spMap_comp_spMap, ThetaSys.Real.UTest.toG, Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ spMap α) this
  obtain ⟨K, hK, hfd, x, hx⟩ := exists_finite_factor u.G.hom (θ.comp α) K₀ (fun v => hθ _) (u.toG a) ha
  let β : FractionRing u.V →+* K := θ.codRestrict K fun v => hK (hθ v)
  let ψ : u.V →+* integralClosure ℤ_[p] K := (β.comp α).codRestrict (integralClosure ℤ_[p] K) fun v =>
    (mem_integralClosure_padicInt_iff K _).mpr ((u.norm_le _).2 ⟨v, rfl⟩)
  let χ : integralClosure ℤ_[p] K →+* K := algebraMap _ _
  have hc : β.comp α = χ.comp ψ := rfl
  have hxG : x ≫ u.G.hom = spMap χ ≫ spMap ψ := by
    obtain ⟨δ, hδ⟩ := Spec.map_surjective (x ≫ u.G.hom)
    have h1 : spMap K.val.toRingHom ≫ spMap δ.hom = spMap (θ.comp α) := by
      rw [← ha, ← hx, Category.assoc, ← hδ]; rfl
    rw [spMap_comp_spMap] at h1
    have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
    have h3 : δ.hom = χ.comp ψ := RingHom.ext fun v => Subtype.ext (RingHom.congr_fun h2 v)
    rw [spMap_comp_spMap, ← h3, ← hδ]; rfl
  have hp : IsProjOver (pullback.snd u.G.hom (spMap α)) := by
    have : IsIso u.U.gen.inv.left := ((Over.forget _).mapIso u.U.gen).isIso_inv
    refine ProjSpace.isProjOver_of_isIso_comp (Y := pullback u.G.hom (spMap α)) u.U.gen.inv.left ?_
    have := ProjSpace.isProjOver_polAV u.A
    rw [← Over.w u.U.gen.inv] at this
    exact this
  let G' := (Over.pullback (spMap ψ)).obj u.G
  haveI : LocallyOfFiniteType G'.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd u.G.hom (spMap ψ)))
  haveI : IsSeparated G'.hom := inferInstanceAs (IsSeparated (pullback.snd u.G.hom (spMap ψ)))
  let a' : Over.mk (spMap χ) ⟶ G' := Over.homMk (pullback.lift x (spMap χ) hxG) (pullback.lift_snd _ _ _)
  obtain ⟨k, hk, g, hg⟩ := GlobalTheory.T.exists_pow_point_integral_padic_groupScheme p K G' (isProjOver_snd_snd u.G.hom α β ψ χ hc hp) a'
  let a₀ : Over.mk (spMap χ ≫ spMap ψ) ⟶ u.G := Over.homMk x hxG
  have e₁ := pow_left_pullback (spMap ψ) u.G (T := Over.mk (spMap χ)) (𝟙 _) (Category.id_comp _) a' a₀
    ((Category.id_comp _).trans (pullback.lift_fst _ _ _).symm) k
  have e₂ := pow_left_pullback (jK u.V) u.G (spMap K.val.toRingHom)
    (show spMap K.val.toRingHom ≫ spMap χ ≫ spMap ψ = spMap θ ≫ spMap α by
      simp only [spMap_comp_spMap]; rfl) a a₀ hx k
  have hgw : g.left ≫ pullback.snd u.G.hom (spMap ψ) = 𝟙 _ := Over.w g
  have hg' : spMap χ ≫ g.left = (a' ^ k).left := by
    rw [← hg]; rfl
  refine ⟨k, hk, spMap (integralClosureToPadicAlgClIntegers K) ≫ g.left ≫ pullback.fst u.G.hom (spMap ψ), ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hgw, spMap_comp_spMap]
    rfl
  · have e₃ : gPt p ≫ spMap (integralClosureToPadicAlgClIntegers K) = spMap K.val.toRingHom ≫ spMap χ := by
      rw [spMap_comp_spMap, spMap_comp_spMap]; rfl
    rw [reassoc_of% e₃, reassoc_of% hg']
    refine Eq.trans ?_ e₂
    exact congrArg _ (e₁.symm.trans (Category.id_comp _))

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaTestPowerIntegralStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_test_power_integral : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (a : u.PtC), ∃ k : ℕ, 1 ≤ k ∧ u.Int (a ^ k) := by
  first | exact @GlobalTheory.ZH.exists_int_pow | exact GlobalTheory.ZH.exists_int_pow | (intros; apply GlobalTheory.ZH.exists_int_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationValuesIsoFieldPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationValuesIsoFieldPullback
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ValuesPullIso
open GlobalTheory.TorusExt GlobalTheory.ArcPull GlobalTheory.ArcTransport
open GlobalTheory.PsiEvenPull (proj)
open ReciprocityTheory.ChartRestriction.G.DVR (cP)

section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem const_vF (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (vF t r J) = (val t r z J).val :=
  ((gs_unit r z _ (hJ.mem φ r) _).symm.trans (gs_eq_stalkConst r z
    (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _)).symm

theorem const_sF (s : LB.Sec (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    stalkConst z (sF s r J) = sval s r z J :=
  (gs_eq_stalkConst r z (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _).symm

theorem units_of_vF {t : LB.Gen (LB.LinComb L φ ε)} {r : Sp F ⟶ Y} {z : Sp F} {J : (Sp F ⟶ X) → L.ι}
    (hJ : Good L z J) {u : Fˣ} (h : (u : F) = vF t r J) : stalkUnits z u = val t r z J :=
  Units.ext ((congrArg (stalkConst z) h).trans (const_vF t r hJ))
end Val

section Num
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]
  {N : NumD F} (ν : NumOf D F N) (z : Sp F)

theorem good : Good D.P.L z ν.J := fun ψ => ν.good ψ trivial

theorem stalk_θ (x y u : N.A) : stalkUnits z (N.θ x y u) = thS D z ν.J (ν.eA x) (ν.eA y) (ν.eA u) :=
  units_of_vF (good ν z) (ν.θ_eq x y u)

theorem stalk_σ (x : N.A) : stalkUnits z (N.σ x) = val (Z := Sp F) D.sym (ν.eA x).left z ν.J :=
  units_of_vF (good ν z) (ν.σ_eq x)

theorem const_rig : stalkConst z (vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
    (TF (R := R) F).hom ν.J) = (val (Z := Sp F) D.rigK (jFK (R := R) F) z ν.J).val :=
  (const_vF _ _ (good ν z)).trans (congrArg Units.val (val_pull (good ν z) _ _ _).symm)

theorem stalk_ψ (χ : N.X) : stalkUnits z (N.ψ χ) =
    val (Z := Sp F) (D.psi (ν.eX χ)) (jFK (R := R) F) z ν.J * val (Z := Sp F) D.rigK (jFK (R := R) F) z ν.J :=
  Units.ext ((congrArg (stalkConst z) (ν.ψ_eq χ)).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (const_vF _ _ (good ν z)) (const_rig ν z))))

theorem stalk_th (x : N.A) : stalkConst z (N.th x) * (val (Z := Sp F) D.rigK (jFK (R := R) F) z ν.J).val =
    sval (Z := Sp F) ν.th (ν.eA x).left z ν.J :=
  (congrArg _ (const_rig ν z).symm).trans ((map_mul _ _ _).symm.trans
    ((congrArg (stalkConst z) (ν.th_eq x)).trans (const_sF _ _ (good ν z))))

theorem stalk_pt {g : GtPtF D F} {c : N.Gt} (h : ν.Pt g c) (χ : N.X) :
    stalkUnits z (c.s χ) = val (Z := Sp F) (g.s (ν.eX χ)) (𝟙 (Sp F)) z ν.J :=
  units_of_vF (good ν z) (h.2 χ)
end Num

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'} (hD : IsPullDeg φ D D') {F : Type} [Field F] [Algebra (FractionRing R) F]
  [Algebra (FractionRing R') F]

theorem injective_of_compat (hF : ArcPull.Compat φ F) : Function.Injective φ := fun a b h =>
  IsFractionRing.injective R (FractionRing R) ((algebraMap (FractionRing R) F).injective
    ((hF a).trans ((congrArg _ (congrArg _ h)).trans (hF b).symm)))

def pushEquiv (hF : ArcPull.Compat φ F) : (TF (R := R') F ⟶ D'.P.A) ≃* (TF (R := R) F ⟶ D.P.A) :=
  MulEquiv.ofBijective (MonoidHom.mk' (pushF (pull_grp hD) hF.base) (pushF_mul _ _))
    ⟨pushF_injective (pull_grp hD) hF.base, pushF_surjective (pull_grp hD) hF.base⟩

theorem exists_iso_of_th (hG : GlobalFnsSt) (hF : ArcPull.Compat φ F) {N N' : NumD F} (ν : NumOf D F N)
    (ν' : NumOf D' F N') (z : Sp F) (lam : ((Sp F).presheaf.stalk z)ˣ)
    (hth : ∀ x : TF (R := R') F ⟶ D'.P.A, sval (Z := Sp F) ν.th (x.left ≫ proj hD) z ν.J =
      (lam * om hD.w z ν.J ν'.J x.left).val * sval (Z := Sp F) ν'.th x.left z ν'.J) :
    ∃ I : NumD.Iso N' N, (∀ y, ν.eX (I.e y) = hD.xe (ν'.eX y)) ∧
      ∀ (g : GtPtF D F) (g' : GtPtF D' F) (c : N.Gt) (c' : N'.Gt), ν.Pt g c → ν'.Pt g' c' →
        IsPullGtF φ hD F g g' → I.Rel c' c := by
  have hJ := good ν z
  have hJ' := good ν' z
  let Ω : (TF (R := R') F ⟶ D'.P.A) → ((Sp F).presheaf.stalk z)ˣ := fun x => om hD.w z ν.J ν'.J x.left
  obtain ⟨h, hh⟩ : ∃ h : N'.A → Fˣ, ∀ x, stalkUnits z (h x) = Ω (ν'.eA x) * (Ω 1)⁻¹ :=
    ⟨fun x => (stalkUnits z).symm _, fun x => (stalkUnits z).apply_symm_apply _⟩
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : N'.A ≃* N.A, ∀ x, ν.eA (Φ x) = pushF (pull_grp hD) hF.base (ν'.eA x) :=
    ⟨(ν'.eA.trans (pushEquiv hD hF)).trans ν.eA.symm, fun x => ν.eA.apply_symm_apply _⟩
  obtain ⟨e, he⟩ : ∃ e : N'.X ≃+ N.X, ∀ y, ν.eX (e y) = hD.xe (ν'.eX y) :=
    ⟨(ν'.eX.trans hD.xe).trans ν.eX.symm, fun x => ν.eX.apply_symm_apply _⟩
  have hc : ∀ χ, ν'.eA (N'.c χ) = cP D' _ (ν'.eX χ) := ν'.c_eq
  have a₁ : ∀ χ, jFK (R := R') F ≫ D'.xK χ = (cP D' (TF (R := R') F) χ).left := fun χ => (Category.assoc _ _ _).symm
  have a₂ : jFK (R := R') F ≫ (1 : TK R' ⟶ D'.P.A).left = (1 : TF (R := R') F ⟶ D'.P.A).left :=
    (Category.assoc _ _ _).symm
  have rig : val (Z := Sp F) D.rigK (jFK (R := R) F) z ν.J = Ω 1 * val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J :=
    (rig_val hD (Z := Sp F) _ _ hF.sq hJ hJ').trans
      (congrArg (fun q => om hD.w z ν.J ν'.J q * val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J) a₂)
  refine ⟨{
    φ := Φ, h := h, lam := (stalkUnits z).symm lam, e := e
    h_one := ?_, θ_eq := fun x y u => ?_, σ_eq := fun x => ?_, th_eq := fun x => ?_
    c_eq := fun χ => ?_, ψ_eq := fun χ => ?_ }, he, fun g g' c c' hg hg' H => ⟨?_, fun χ => ?_⟩⟩
  · apply (stalkUnits z).injective
    rw [hh, map_one, map_one, mul_inv_cancel]
  · apply (stalkUnits z).injective
    have k : thS D z ν.J (pushF (pull_grp hD) hF.base (ν'.eA x)) (pushF (pull_grp hD) hF.base (ν'.eA y))
        (pushF (pull_grp hD) hF.base (ν'.eA u)) =
        Ω (ν'.eA x * ν'.eA y * ν'.eA u) * (Ω (ν'.eA x * ν'.eA y))⁻¹ * (Ω (ν'.eA x * ν'.eA u))⁻¹ *
          (Ω (ν'.eA y * ν'.eA u))⁻¹ * Ω (ν'.eA x) * Ω (ν'.eA y) * Ω (ν'.eA u) * (Ω 1)⁻¹ *
          thS D' z ν'.J (ν'.eA x) (ν'.eA y) (ν'.eA u) :=
      thS_push (pull_grp hD) hF.base ((isGen_iff _).1 hD.w_gen) hG hJ hJ' _ _ _
    simp only [map_mul, hh, stalk_θ ν, stalk_θ ν', hΦ, k]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · apply (stalkUnits z).injective
    have k : val (Z := Sp F) D.sym (pushF (pull_grp hD) hF.base (ν'.eA x)).left z ν.J =
        Ω (ν'.eA x)⁻¹ * (Ω (ν'.eA x))⁻¹ * val (Z := Sp F) D'.sym (ν'.eA x).left z ν'.J :=
      PsiEvenPull.sym_pull hG hD (Z := Sp F) (ν'.eA x).left z hJ hJ'
    simp only [map_mul, map_inv, hh, stalk_σ ν, stalk_σ ν', hΦ, k]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · apply (stalkConst z).injective
    have k := stalk_th ν z (Φ x)
    have k' := stalk_th ν' z x
    rw [hΦ, rig] at k
    have k₁ := k.trans ((hth (ν'.eA x)).trans (congrArg _ k'.symm))
    rw [map_mul, ← stalkUnits_val, map_mul, hh, MulEquiv.apply_symm_apply]
    refine (Units.mul_left_inj (Ω 1 * val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J)).1 (k₁.trans ?_)
    have := (Ω 1).inv_mul
    simp only [Units.val_mul]
    linear_combination (-(lam.val * (Ω (ν'.eA x)).val * stalkConst z (N'.th x) *
      (val (Z := Sp F) D'.rigK (jFK (R := R') F) z ν'.J).val)) * this
  · apply ν.eA.injective
    rw [hΦ, ν.c_eq, he, hc]
    exact Over.OverMorphism.ext ((cPoint_proj hD (T := TF (R := R) F) (T' := TF (R := R') F) (𝟙 _)
      (hF.base.trans (Category.id_comp _).symm) _).trans (Category.id_comp _)).symm
  · apply (stalkUnits z).injective
    have k : val (Z := Sp F) (D.psi (hD.xe (ν'.eX χ))) (jFK (R := R) F) z ν.J =
        (Ω (cP D' _ (ν'.eX χ)))⁻¹ * val (Z := Sp F) (D'.psi (ν'.eX χ)) (jFK (R := R') F) z ν'.J :=
      (psi_val hD (Z := Sp F) _ _ hF.sq hJ hJ' _).trans (congrArg (fun q => (om hD.w z ν.J ν'.J q)⁻¹ *
        val (Z := Sp F) (D'.psi (ν'.eX χ)) (jFK (R := R') F) z ν'.J) (a₁ _))
    rw [map_mul, hh, stalk_ψ ν, stalk_ψ ν', he, k, rig, hc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · apply ν.eA.injective
    refine hg.1.trans (Eq.trans ?_ (hΦ _).symm)
    rw [hg'.1]
    exact Over.OverMorphism.ext H.1.symm
  · apply (stalkUnits z).injective
    have k₀ := pullGt_val hD H (ν'.eX χ) (𝟙 _) hJ hJ'
    simp only [Category.id_comp] at k₀
    have k : val (Z := Sp F) (g.s (hD.xe (ν'.eX χ))) (𝟙 (Sp F)) z ν.J =
        (Ω (cP D' _ (ν'.eX χ) * g'.b))⁻¹ * Ω (cP D' _ (ν'.eX χ)) * Ω g'.b * (Ω 1)⁻¹ *
          val (Z := Sp F) (g'.s (ν'.eX χ)) (𝟙 (Sp F)) z ν'.J := k₀
    show stalkUnits z (c.s (e χ) * h (N'.c χ * c'.b)) = stalkUnits z (c'.s χ * h (N'.c χ) * h c'.b)
    rw [map_mul, map_mul, map_mul, hh, hh, hh, stalk_pt ν z hg, stalk_pt ν' z hg', he, k, map_mul, hc, hg'.1]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

theorem exists_values_iso : GlobalFnsSt → ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (φ : R →+* K) (D : DegPre R) (D' : DegPre K) (hD : IsPullDeg φ D D') (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing K) F], ArcPull.Compat φ F → ∀ (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N'), ∃ I : NumD.Iso N' N, (∀ y, ν.eX (I.e y) = hD.xe (ν'.eX y)) ∧ ∀ (g : GtPtF D F) (g' : GtPtF D' F) (c : N.Gt) (c' : N'.Gt), ν.Pt g c → ν'.Pt g' c' → IsPullGtF φ hD F g g' → I.Rel c' c := by
  intro hG R K _ _ _ φ D D' hD F _ _ _ hF N N' ν ν'
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_unit_generatingSection_pullback_field R K φ (injective_of_compat hF) D D' hD ν.th ν'.th ν.th_gen ν'.th_gen
  let z : Sp F := IsLocalRing.closedPoint F
  refine exists_iso_of_th hD hG hF ν ν' z (TauTwist.unitAt (Z := Sp F) (TF (R := K) F).hom z c) fun x => ?_
  have := hc (Sp F) x.left z ν.J ν'.J (good ν z) (good ν' z)
  exact this.trans (congrArg (fun q => (TauTwist.unitAt (Z := Sp F) q z c * om hD.w z ν.J ν'.J x.left).val *
    sval (Z := Sp F) ν'.th x.left z ν'.J) (Over.w x))

end GlobalTheory.ValuesPullIso
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegenerationValuesIsoFieldPullbackStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degenerationValuesIso_fieldPullback : GlobalFnsSt → ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] (φ : R →+* K) (D : DegPre R) (D' : DegPre K) (hD : IsPullDeg φ D D') (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing K) F], ArcPull.Compat φ F → ∀ (N N' : NumD F) (ν : NumOf D F N) (ν' : NumOf D' F N'), ∃ I : NumD.Iso N' N, (∀ y, ν.eX (I.e y) = hD.xe (ν'.eX y)) ∧ ∀ (g : GtPtF D F) (g' : GtPtF D' F) (c : N.Gt) (c' : N'.Gt), ν.Pt g c → ν'.Pt g' c' → IsPullGtF φ hD F g g' → I.Rel c' c := by
  first | exact @GlobalTheory.ValuesPullIso.exists_values_iso | exact GlobalTheory.ValuesPullIso.exists_values_iso | (intros; apply GlobalTheory.ValuesPullIso.exists_values_iso <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSpreadsOutFromGenericFibreProper
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSpreadsOutFromGenericFibreProper
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GenSpread

set_option backward.isDefEq.respectTransparency false

theorem isLB_of_gm {Y : Scheme.{0}} (L : LB Y) (hc : ∀ y : Y, ∃ i, y ∈ L.U i)
    (h : ∀ (y : Y) i j k, y ∈ L.U i → y ∈ L.U j → y ∈ L.U k →
      gm (𝟙 Y) y _ (L.g i j) * gm (𝟙 Y) y _ (L.g j k) = gm (𝟙 Y) y _ (L.g i k)) : L.IsLB := {
  cover := top_le_iff.1 fun y _ => Opens.mem_iSup.2 (hc y)
  g_self i := unit_ext fun y hy => by
    refine (gm_res (𝟙 Y) y _ hy _).trans ?_
    rw [map_one]
    exact mul_eq_left.1 (h y i i i hy hy hy)
  cocycle i j k := unit_ext fun y hy =>
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res (𝟙 Y) y _ hy _) (gm_res (𝟙 Y) y _ hy _))).trans
      ((h y i j k hy.1.1 hy.1.2 hy.2).trans (gm_res (𝟙 Y) y _ hy _).symm) }

section Limit

variable {I : Type} [SmallCategory I] [IsCofiltered I]
  (D : I ⥤ Scheme.{0}) {X : Scheme.{0}} (π : ∀ i, X ⟶ D.obj i)
  (w : ∀ {i j} (f : i ⟶ j), π i ≫ D.map f = π j) (hc : IsLimit (schemeConeOfFamily D π w))
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]


include hc in
theorem exists_isLB_of_isLimit {i : I} [CompactSpace (D.obj i)] (M : LB (D.obj i)) [Finite M.ι]
    (hM : ∀ a b c, IsCompact ((M.U a ⊓ M.U b ⊓ M.U c : (D.obj i).Opens) : Set (D.obj i)))
    (hcov : ∀ y : X, ∃ a, π i y ∈ M.U a)
    (h : ∀ (y : X) a b c, π i y ∈ M.U a → π i y ∈ M.U b → π i y ∈ M.U c →
      gm (π i) y _ (M.g a b) * gm (π i) y _ (M.g b c) = gm (π i) y _ (M.g a c)) :
    ∃ (j : I) (f : j ⟶ i), (M.pull (D.map f)).IsLB := by
  have l₁ : ∀ a b c, M.U a ⊓ M.U b ⊓ M.U c ≤ M.U a ⊓ M.U b := fun a b c => inf_le_left
  have l₂ : ∀ a b c, M.U a ⊓ M.U b ⊓ M.U c ≤ M.U b ⊓ M.U c := fun a b c _ hy => ⟨hy.1.2, hy.2⟩
  have l₃ : ∀ a b c, M.U a ⊓ M.U b ⊓ M.U c ≤ M.U a ⊓ M.U c := fun a b c _ hy => ⟨hy.1.1, hy.2⟩
  have val : ∀ {Z : Scheme.{0}} (r : Z ⟶ D.obj i) (z : Z) a b c, r z ∈ M.U a ⊓ M.U b ⊓ M.U c →
      gm r z _ (res (l₁ a b c) (M.g a b) * res (l₂ a b c) (M.g b c)) =
        gm r z _ (M.g a b) * gm r z _ (M.g b c) := fun r z a b c hz =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _) (gm_res r z _ hz _))
  obtain ⟨j, f, hj⟩ := exists_common_refinement (i := i)
    (fun (p : M.ι × M.ι × M.ι) k g =>
      pullU (D.map g) _ (res (l₁ p.1 p.2.1 p.2.2) (M.g _ _) * res (l₂ p.1 p.2.1 p.2.2) (M.g _ _)) =
        pullU (D.map g) _ (res (l₃ p.1 p.2.1 p.2.2) (M.g _ _)))
    (by
      intro p k g k' g' h
      rw [D.map_comp]
      exact congrArg (pullU (D.map g') _) h)
    (by
      rintro ⟨a, b, c⟩
      exact exists_pullU_eq D π w hc (hM a b c) _ _ fun y hy =>
        (val (π i) y a b c hy).trans ((h y a b c hy.1.1 hy.1.2 hy.2).trans (gm_res _ y _ hy _).symm))
  obtain ⟨j', f', hj'⟩ := exists_map_preimage_le_map_preimage D _ hc (U := ⊤) (V := ⨆ a, M.U a)
    isCompact_univ (fun y _ => Opens.mem_iSup.2 (hcov y))
  obtain ⟨k, g, g', hg⟩ := IsCofiltered.cospan f f'
  refine ⟨k, g ≫ f, isLB_of_gm _ (fun y => ?_) fun y a b c ha hb hc' => ?_⟩
  · obtain ⟨a, ha⟩ := Opens.mem_iSup.1 (hj' (show D.map g' y ∈ D.map f' ⁻¹ᵁ ⊤ from trivial))
    refine ⟨fun _ => a, mem_pull.2 ?_⟩
    rw [hg, D.map_comp]
    exact ha
  · rw [gm_pull_g M _ (𝟙 _) y a b ha hb, gm_pull_g M _ (𝟙 _) y b c hb hc', gm_pull_g M _ (𝟙 _) y a c ha hc',
      Category.id_comp]
    have hy : D.map (g ≫ f) y ∈ M.U (a PUnit.unit) ⊓ M.U (b PUnit.unit) ⊓ M.U (c PUnit.unit) :=
      ⟨⟨mem_pull.1 ha, mem_pull.1 hb⟩, mem_pull.1 hc'⟩
    rw [D.map_comp] at hy ⊢
    have e := congrArg (gm (D.map g) y _) (hj (a PUnit.unit, b PUnit.unit, c PUnit.unit))
    exact (val _ y _ _ _ hy).symm.trans ((gm_pull (D.map g) (D.map f) y _ hy _).symm.trans (e.trans
      ((gm_pull (D.map g) (D.map f) y _ hy _).trans (gm_res _ y _ hy _))))


include hc in
theorem exists_lb_of_isLimit {i : I} [CompactSpace (D.obj i)] [CompactSpace X]
    (hsep : ∀ U V : (D.obj i).Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V))
    (hπ : Topology.IsInducing (π i)) (L₀ : LB X) (hL : L₀.IsLB) :
    ∃ (j : I) (L : LB (D.obj j)), L.IsLB ∧ LBIso L₀ (L.pull (π j)) := by
  have loc : ∀ x : X, ∃ (V : (D.obj i).Opens) (c : L₀.ι),
      IsAffineOpen V ∧ π i x ∈ V ∧ π i ⁻¹ᵁ V ≤ L₀.U c := by
    intro x
    obtain ⟨c, hc⟩ := exists_chart hL x
    obtain ⟨W, hW, hW'⟩ := hπ.isOpen_iff.1 (L₀.U c).isOpen
    have hx : π i x ∈ W := hW'.ge hc
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, hle⟩ := (D.obj i).isBasis_affineOpens.exists_subset_of_mem_open hx hW
    exact ⟨V, c, hV, hx, fun y hy => hW'.le (hle hy)⟩
  choose V c hV hx hle using loc
  obtain ⟨σ, hσ⟩ := CompactSpace.elim_nhds_subcover (fun x => ((π i ⁻¹ᵁ V x : X.Opens) : Set X))
    (fun x => (π i ⁻¹ᵁ V x).isOpen.mem_nhds (hx x))
  have cov : ∀ x : X, ∃ a : σ, π i x ∈ V a := fun x => by
    obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.1 (hσ.ge (Set.mem_univ x))
    exact ⟨⟨a, ha⟩, hx⟩
  have le : ∀ {j k : I} (f : j ⟶ i) (g : k ⟶ j) (U : (D.obj i).Opens),
      D.map (g ≫ f) ⁻¹ᵁ U ≤ D.map g ⁻¹ᵁ (D.map f ⁻¹ᵁ U) := fun f g U => by
    rw [D.map_comp, Scheme.Hom.comp_preimage]
  have l : ∀ a b, π i ⁻¹ᵁ (V a ⊓ V b) ≤ L₀.U (c a) ⊓ L₀.U (c b) := fun a b _ hy => ⟨hle a hy.1, hle b hy.2⟩
  obtain ⟨j, f, hj⟩ := exists_common_refinement (i := i)
    (fun (p : σ × σ) j f => ∃ t : Γ(D.obj j, D.map f ⁻¹ᵁ (V p.1 ⊓ V p.2))ˣ, ∀ y : X,
      y ∈ π i ⁻¹ᵁ (V p.1 ⊓ V p.2) →
      gm (π j) y (D.map f ⁻¹ᵁ (V p.1 ⊓ V p.2)) t = gm (𝟙 X) y _ (res (l p.1 p.2) (L₀.g _ _)))
    (by
      rintro p j f k g ⟨t, ht⟩
      refine ⟨res (le f g _) (pullU (D.map g) _ t), fun y hy => ?_⟩
      have hy' := cone_preimage_le D π w (g ≫ f) _ hy
      refine (gm_res_pullU (π k) (D.map g) y (le f g (V p.1 ⊓ V p.2)) hy' t).trans ?_
      rw [w g]
      exact ht y hy)
    (fun p => exists_unit_π_eq D π w hc (hsep _ _ (hV _) (hV _)) _)
  choose t ht using hj
  let M : LB (D.obj j) := ⟨σ, fun a => D.map f ⁻¹ᵁ V a, fun a b => t (a, b)⟩
  have mem : ∀ (y : X) (a : σ), π j y ∈ M.U a ↔ π i y ∈ V a := fun y a => by
    rw [← w f]; rfl
  have val : ∀ (y : X) (a b : σ), π j y ∈ M.U a → π j y ∈ M.U b →
      gm (π j) y _ (M.g a b) = gm (𝟙 X) y _ (L₀.g (c a) (c b)) := fun y a b ha hb =>
    have hy : y ∈ π i ⁻¹ᵁ (V a ⊓ V b) := ⟨(mem y a).1 ha, (mem y b).1 hb⟩
    (ht (a, b) y hy).trans (gm_res _ y _ hy _)
  have : CompactSpace (D.obj j) := QuasiCompact.compactSpace_of_compactSpace (D.map f)
  have : Finite M.ι := inferInstanceAs (Finite σ)
  obtain ⟨k, g, hk⟩ := exists_isLB_of_isLimit D π w hc M
    (fun a b e => ((hsep _ _ (hsep _ _ (hV a) (hV b)) (hV e)).preimage (D.map f)).isCompact)
    (fun y => (cov y).imp fun a ha => (mem y a).2 ha)
    (fun y a b e ha hb he => by
      rw [val y a b ha hb, val y b e hb he, val y a e ha he]
      exact gm_cocycle hL (𝟙 X) y (hle a ((mem y a).1 ha)) (hle b ((mem y b).1 hb)) (hle e ((mem y e).1 he)))
  have mem' : ∀ (y : X) J, y ∈ ((M.pull (D.map g)).pull (π k)).U J → π j y ∈ M.U (J PUnit.unit PUnit.unit) :=
    fun y J hy => by
      rw [← w g]
      have hy' : π k y ∈ (M.pull (D.map g)).U (J PUnit.unit) := mem_pull.1 hy
      exact (mem_pull (F := D.map g)).1 hy'
  refine ⟨k, _, hk, (lbIso_of_chartPull (B' := (M.pull (D.map g)).pull (π k))
    ⟨fun J => c (J PUnit.unit PUnit.unit).1, fun J y hy => hle _ ((mem y _).1 (mem' y J hy)),
      fun y J J' hJ hJ' => ?_⟩ hL).symm⟩
  rw [gm_pull_g _ _ (𝟙 _) y J J' hJ hJ', Category.id_comp,
    gm_pull_g M _ (π k) y _ _ (mem_pull.1 hJ) (mem_pull.1 hJ'), w g]
  exact val y _ _ (mem' y J hJ) (mem' y J' hJ')

end Limit

theorem exists_lb {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {X X₀ : Scheme.{0}} (f : X ⟶ Sp R) [QuasiCompact f] [IsSeparated f] {φ : X₀ ⟶ X} {f₀ : X₀ ⟶ Sp K}
    (h : IsPullback φ f₀ f (spMap (algebraMap R K))) {L₀ : LB X₀} (hL : L₀.IsLB) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), π ≫ f = f' ≫ spMap g →
        ∃ L' : LB X', L'.IsLB ∧ ∀ φ' : X₀ ⟶ X', φ' ≫ π = φ → LBIso L₀ (L'.pull φ') := by
  obtain ⟨p₁, h₁⟩ := exists_isPullback_stalk h
  obtain ⟨hc⟩ := StalkLimit.nonempty_isLimit h₁
  obtain ⟨V₀⟩ : Nonempty (StalkLimit.AffNhd (genericPoint (Sp R))) := IsCofiltered.nonempty
  have : IsAffine V₀.1.toScheme := V₀.2.2
  have : CompactSpace ((StalkLimit.diagram _ f).obj V₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f V₀.1.ι)
  have : QuasiCompact f₀ := MorphismProperty.of_isPullback (P := @QuasiCompact) h inferInstance
  have : CompactSpace X₀ := QuasiCompact.compactSpace_of_compactSpace f₀
  have : IsPreimmersion φ := MorphismProperty.of_isPullback (P := @IsPreimmersion) h₁.flip inferInstance
  have hs : (pullback f V₀.1.ι).IsSeparated :=
    ⟨by rw [← terminal.comp_from (pullback.snd f V₀.1.ι)]; infer_instance⟩
  have : ((StalkLimit.diagram _ f).obj V₀).IsSeparated := hs
  have hi : Topology.IsInducing ((StalkLimit.cone h₁).π.app V₀) := by
    refine Topology.IsInducing.of_comp (g := pullback.fst f V₀.1.ι) (Scheme.Hom.continuous _)
      (Scheme.Hom.continuous _) ?_
    have := φ.isEmbedding.isInducing
    rw [← StalkLimit.cone_π_fst h₁ V₀] at this
    exact this
  obtain ⟨V, L, hL', H⟩ := exists_lb_of_isLimit (StalkLimit.diagram _ f) (fun V => (StalkLimit.cone h₁).π.app V)
    (fun i => (StalkLimit.cone h₁).w i) hc (i := V₀) (fun U W hU hW => hU.inf hW) hi L₀ hL
  obtain ⟨a, ha, Ha⟩ := exists_forall_mem V.2.1
  refine ⟨a, ha, fun R' _ g hg X' π f' e => ?_⟩
  obtain ⟨l, hl⟩ := exists_lift_open f V.1 e (Ha R' g hg)
  refine ⟨L.pull l, pull_isLB hL' _, fun φ' hφ' => ?_⟩
  have : (StalkLimit.cone h₁).π.app V = φ' ≫ l := by
    rw [← cancel_mono (pullback.fst f V.1.ι), Category.assoc, hl, hφ', StalkLimit.cone_π_fst]
  exact LBIso.trans hL (pull_isLB hL' _) (pull_isLB (pull_isLB hL' _) _) H (lbIso_pull_pull hL' φ' this)

theorem lineBundle_spreads_out (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (X X₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp K) (φ : X₀ ⟶ X)
    (h : IsPullback φ f₀ f (spMap (algebraMap R K))) (_ : Flat f) (_ : IsProper f) (L₀ : LB X₀) (hL : L₀.IsLB) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), π ≫ f = f' ≫ spMap g →
        ∃ L' : LB X', L'.IsLB ∧ ∀ φ' : X₀ ⟶ X', φ' ≫ π = φ → LBIso L₀ (L'.pull φ') :=
  exists_lb f h hL

end GlobalTheory.GenSpread
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSpreadsOutFromGenericFibreProperStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_spreads_out_from_genericFibre_proper : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (X X₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp K) (φ : X₀ ⟶ X), IsPullback φ f₀ f (spMap (algebraMap R K)) → Flat f → IsProper f → ∀ L₀ : LB X₀, L₀.IsLB → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), π ≫ f = f' ≫ spMap g → ∃ L' : LB X', L'.IsLB ∧ ∀ φ' : X₀ ⟶ X', φ' ≫ π = φ → LBIso L₀ (L'.pull φ') := by
  first | exact @GlobalTheory.GenSpread.lineBundle_spreads_out | exact GlobalTheory.GenSpread.lineBundle_spreads_out | (intros; apply GlobalTheory.GenSpread.lineBundle_spreads_out <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralGaugeValuesAreValuationUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralGaugeValuesAreValuationUnits
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
noncomputable section
namespace GlobalTheory.Ex.UnitVal

section Values
variable {C : Type} [Field C] {X Y : Scheme.{0}}

theorem valF_appLE' {F : Type} [Field F] {x : Sp F ⟶ X} {U : X.Opens} (f : X ⟶ Y) (W : Y.Opens) (e : U ≤ f ⁻¹ᵁ W)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(Y, W)) : valF x U ((f.appLE W U e).hom a) = valF (x ≫ f) W a := by
  have h' : ⊤ ≤ (x ≫ f) ⁻¹ᵁ W := fun q hq => e (h hq)
  rw [valF, valF, dite_eq_left h, dite_eq_left h', ← Scheme.Hom.appLE_comp_appLE x f W U ⊤ e h]
  rfl

theorem valF_res' {F : Type} [Field F] {x : Sp F ⟶ X} {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)) : valF x V ((X.presheaf.map (homOfLE e).op).hom a) = valF x U a := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := fun q hq => e (h hq)
  rw [valF, valF, dite_eq_left h, dite_eq_left h', ← Scheme.Hom.map_appLE x h (homOfLE e).op]
  rfl

theorem exists_valHom (S : ValuationSubring C) (t : Sp S ⟶ X) (U : X.Opens) (ht : ⊤ ≤ t ⁻¹ᵁ U) :
    ∃ g : Γ(X, U) →+* S, ∀ a, valF (spMap S.subtype ≫ t) U a = g a := by
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom.comp (t.appLE U ⊤ ht).hom, fun a => ?_⟩
  have h' : ⊤ ≤ (spMap S.subtype ≫ t) ⁻¹ᵁ U := fun q _ => ht (Set.mem_univ (spMap S.subtype q))
  rw [valF, dite_eq_left h']
  have e : (spMap S.subtype ≫ t).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom =
      t.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom ≫ CommRingCat.ofHom S.subtype := by
    rw [← Scheme.ΓSpecIso_naturality, ← Scheme.Hom.appLE_comp_appLE (spMap S.subtype) t U ⊤ ⊤ ht le_rfl,
      Category.assoc]
    rfl
  exact congrArg (fun g => g.hom a) e

theorem val_valF_le {S : ValuationSubring C} (t : Sp S ⟶ X) (U : X.Opens)
    (ht : ⊤ ≤ t ⁻¹ᵁ U) (a : Γ(X, U)) : valF (spMap S.subtype ≫ t) U a ∈ S := by
  obtain ⟨g, hg⟩ := exists_valHom S t U ht
  rw [hg]
  exact (g a).2

theorem val_valF_unit {S : ValuationSubring C} (t : Sp S ⟶ X) (U : X.Opens)
    (ht : ⊤ ≤ t ⁻¹ᵁ U) (a : Γ(X, U)) (ha : IsUnit a) : S.valuation (valF (spMap S.subtype ≫ t) U a) = 1 := by
  obtain ⟨g, hg⟩ := exists_valHom S t U ht
  rw [hg]
  exact (S.valuation_eq_one_iff (g a)).1 (ha.map g)
end Values

section Geo
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {C : Type} [Field C] [Algebra (FractionRing R) C]
  {N : NumD C} {ν : NumOf D C N} {S : ValuationSubring C} {s : Sp S ⟶ Sp R}

theorem exists_base (h : ∀ r : R, algebraMap (FractionRing R) C (algebraMap R _ r) ∈ S) :
    ∃ s : Sp S ⟶ Sp R, spMap S.subtype ≫ s = (TF (R := R) C).hom := by
  refine ⟨spMap (((algebraMap (FractionRing R) C).comp (algebraMap R _)).codRestrict S.toSubring h), ?_⟩
  change _ = jFK (R := R) C ≫ jK R
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem base_ext {a b : Sp S ⟶ Sp R} (h : spMap S.subtype ≫ a = spMap S.subtype ≫ b) : a = b := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective a
  obtain ⟨b, rfl⟩ := Spec.map_surjective b
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  have := Spec.map_injective h
  congr 1
  ext r
  exact congrArg (fun g => g.hom r) this

theorem isDominant_sub : IsDominant (spMap S.subtype) :=
  ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical S.subtype).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 S.subtype_injective]; exact bot_le)⟩

theorem chart_int (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) (y : Sp S ⟶ D.P.A.left)
    (hy : y ≫ D.P.A.hom = s) : ⊤ ≤ y ⁻¹ᵁ D.P.L.U (ν.J (spMap S.subtype ≫ y)) := by
  obtain ⟨x₀, e, h⟩ := hν (Over.homMk (spMap S.subtype ≫ y) (by rw [Category.assoc, hy, hs]))
  have := D.P.isAb.proper
  have := isDominant_sub (S := S)
  have e' : spMap S.subtype ≫ x₀ = spMap S.subtype ≫ y := e
  obtain rfl : x₀ = y := ext_of_isDominant_of_isSeparated D.P.A.hom
    (base_ext (by rw [← Category.assoc, e', Category.assoc])) _ e'
  exact h

theorem wchart_int (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) {Y : Scheme.{0}} {K : Type}
    [Fintype K] (φ : K → (Y ⟶ D.P.A.left)) (r : Sp S ⟶ Y) (h : ∀ k, r ≫ φ k ≫ D.P.A.hom = s) :
    ⊤ ≤ r ⁻¹ᵁ LB.wchart D.P.L φ fun k => ν.J ((spMap S.subtype ≫ r) ≫ φ k) := fun q hq =>
  Set.mem_iInter.2 fun k => by
    beta_reduce
    rw [Category.assoc]
    exact chart_int hν hs (r ≫ φ k) (by rw [Category.assoc, h]) hq

theorem val_vF (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb D.P.L φ ε))
    (r : Sp S ⟶ Y) (h : ∀ k, r ≫ φ k ≫ D.P.A.hom = s) {r' : Sp C ⟶ Y} (e : spMap S.subtype ≫ r = r') :
    S.valuation (vF t r' ν.J) = 1 := by
  subst e
  exact val_valF_unit r _ (wchart_int hν hs φ r h) _ (Units.isUnit _)

theorem val_sF (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ D.P.A.left)} {ε : K → ℤ} (t : LB.Sec (LB.LinComb D.P.L φ ε))
    (r : Sp S ⟶ Y) (h : ∀ k, r ≫ φ k ≫ D.P.A.hom = s) {r' : Sp C ⟶ Y} (e : spMap S.subtype ≫ r = r') :
    sF t r' ν.J ∈ S := by
  subst e
  exact val_valF_le r _ (wchart_int hν hs φ r h) _

theorem exists_ext (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) (x : TF (R := R) C ⟶ D.P.A) :
    ∃ x₀ : Over.mk s ⟶ D.P.A, (Over.homMk (spMap S.subtype) hs : TF (R := R) C ⟶ Over.mk s) ≫ x₀ = x := by
  obtain ⟨x₀, e, -⟩ := hν x
  refine ⟨Over.homMk x₀ (base_ext ?_), Over.OverMorphism.ext e⟩
  rw [← Category.assoc, e, Over.w x]
  exact hs.symm

theorem val_rig (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom) :
    S.valuation (vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) C).hom ν.J) = 1 :=
  val_vF hν hs _ s (fun _ => by
    have : eSec D.P.A ≫ D.P.A.hom = 𝟙 _ := Over.w η[D.P.A]
    exact (congrArg (s ≫ ·) this).trans (Category.comp_id _)) hs

theorem val_θ (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (x y u : N.A) : S.valuation ((N.θ x y u : C)) = 1 := by
  obtain ⟨x₀, hx⟩ := exists_ext hν hs (ν.eA x)
  obtain ⟨y₀, hy⟩ := exists_ext hν hs (ν.eA y)
  obtain ⟨u₀, hu⟩ := exists_ext hν hs (ν.eA u)
  rw [ν.θ_eq]
  refine val_vF hν hs _ (lift x₀ (lift y₀ u₀)).left (fun k => ?_) ?_
  · exact (congrArg (_ ≫ ·) (Over.w (psum D.P.A (x3 D.P.A) k.down))).trans (Over.w (lift x₀ (lift y₀ u₀)))
  · rw [← hx, ← hy, ← hu, ← comp_lift, ← comp_lift]
    rfl

theorem val_σ (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (x : N.A) : S.valuation ((N.σ x : C)) = 1 := by
  obtain ⟨x₀, hx⟩ := exists_ext hν hs (ν.eA x)
  rw [ν.σ_eq]
  refine val_vF hν hs _ x₀.left (fun k => ?_) (congrArg (·.left) hx)
  fin_cases k
  · exact (congrArg (_ ≫ ·) (Over.w ι[D.P.A])).trans (Over.w x₀)
  · exact (congrArg (_ ≫ ·) (Category.id_comp _)).trans (Over.w x₀)

theorem val_th (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (x : N.A) : N.th x ∈ S := by
  obtain ⟨x₀, hx⟩ := exists_ext hν hs (ν.eA x)
  have h := congrArg S.valuation (ν.th_eq x)
  rw [map_mul, val_rig hν hs, _root_.mul_one] at h
  rw [← S.valuation_le_one_iff, h, S.valuation_le_one_iff]
  exact val_sF hν hs _ x₀.left (fun _ => (congrArg (_ ≫ ·) (Category.id_comp _)).trans (Over.w x₀))
    (congrArg (·.left) hx)

theorem val_psi (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (χ : D.X) (hχ : PsiUnitOn D χ Set.univ) : S.valuation (vF (D.psi χ) (jFK (R := R) C) ν.J) = 1 := by
  have e : jFK (R := R) C ≫ D.xK χ = spMap S.subtype ≫ s ≫ (D.c χ).left := by
    rw [← Category.assoc, hs]
    exact (Category.assoc _ _ _).symm
  have h1 := chart_int hν hs (s ≫ (D.c χ).left)
    ((Category.assoc _ _ _).trans ((congrArg (s ≫ ·) (Over.w (D.c χ))).trans (Category.comp_id _)))
  rw [← e] at h1
  have h2 : s (IsLocalRing.closedPoint S) ∈ ((D.c χ).left ⁻¹ᵁ D.P.L.U (ν.J (jFK (R := R) C ≫ D.xK χ)) : (Sp R).Opens) :=
    h1 (Set.mem_univ _)
  obtain ⟨_, ⟨V, hV, rfl⟩, hy, hle⟩ := (Sp R).isBasis_affineOpens.exists_subset_of_mem_open h2 (TopologicalSpace.Opens.isOpen _)
  have h3 : ⊤ ≤ s ⁻¹ᵁ V := ((IsLocalRing.closedPoint_mem_iff (s ⁻¹ᵁ V)).1 hy).ge
  have h : jK R ⁻¹ᵁ V ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U
      (fun _ => ν.J (jFK (R := R) C ≫ D.xK χ)) := fun y hy => Set.mem_iInter.2 fun _ => hle hy
  obtain ⟨r, hr, er⟩ := hχ (fun _ => ν.J (jFK (R := R) C ≫ D.xK χ)) V hV (Set.subset_univ _) hle h
  have hs' : jFK (R := R) C ≫ jK R = spMap S.subtype ≫ s := hs.symm
  have h4 : ⊤ ≤ jFK (R := R) C ⁻¹ᵁ (jK R ⁻¹ᵁ V) := by
    change ⊤ ≤ (jFK (R := R) C ≫ jK R) ⁻¹ᵁ V
    rw [hs']
    exact fun q _ => h3 (Set.mem_univ (spMap S.subtype q))
  have a := valF_res' h h4 ((D.psi χ).s _).val
  rw [Scheme.Hom.app_eq_appLE] at er
  refine (congrArg S.valuation (a.symm.trans ((congrArg (valF _ _) er.symm).trans
    (valF_appLE' (jK R) V le_rfl h4 r)))).trans ?_
  exact (congrArg (fun q => S.valuation (valF q V r)) hs').trans (val_valF_unit s V h3 r hr)

theorem val_ψ (hν : ν.Integral S) (hs : spMap S.subtype ≫ s = (TF (R := R) C).hom)
    (χ : N.X) (hχ : PsiUnitOn D (ν.eX χ) Set.univ) : S.valuation ((N.ψ χ : C)) = 1 := by
  rw [ν.ψ_eq, map_mul, val_rig hν hs, val_psi hν hs _ hχ, _root_.mul_one]
end Geo

theorem integral_values : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (S : ValuationSubring F), (∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S) → ∀ (N : NumD F) (ν : NumOf D F N), ν.Integral S → (∀ x y u, S.valuation (N.θ x y u : F) = 1) ∧ (∀ x, S.valuation (N.σ x : F) = 1) ∧ (∀ x, N.th x ∈ S) ∧ ((∀ y, PsiUnitOn D y Set.univ) → ∀ χ, S.valuation (N.ψ χ : F) = 1) := by
  intro R _ _ D F _ _ S hR N ν hν
  obtain ⟨s, hs⟩ := exists_base (R := R) (S := S) hR
  exact ⟨val_θ hν hs, val_σ hν hs, val_th hν hs, fun h χ => val_ψ hν hs χ (h _)⟩

end GlobalTheory.Ex.UnitVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralGaugeValuesAreValuationUnitsStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralGauge_values_are_valuationUnits : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (S : ValuationSubring F), (∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S) → ∀ (N : NumD F) (ν : NumOf D F N), ν.Integral S → (∀ x y u, S.valuation (N.θ x y u : F) = 1) ∧ (∀ x, S.valuation (N.σ x : F) = 1) ∧ (∀ x, N.th x ∈ S) ∧ ((∀ y, PsiUnitOn D y Set.univ) → ∀ χ, S.valuation (N.ψ χ : F) = 1) := by
  first | exact @GlobalTheory.Ex.UnitVal.integral_values | exact GlobalTheory.Ex.UnitVal.integral_values | (intros; apply GlobalTheory.Ex.UnitVal.integral_values <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsThetaPtDown
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsThetaPtDown
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory.ThetaNest
open ThetaCoord CommPairing GlobalLift

variable {S : Scheme.{0}} {T : Over S}

theorem isThetaPt_of_over (P : PolAV S) [Subsingleton T.left] {k : ℕ} {I : Type} {x : I → (T ⟶ P.A)}
    {v : I → Γ(T.left, ⊤)} (ho : Odd k) (hu : IsUnit (k : Γ(T.left, ⊤))) (H : IsThetaPtOver P k x v) :
    IsThetaPt P k x v := by
  refine ⟨ho, hu, fun p => ⟨⊤, trivial, ?_⟩⟩
  obtain ⟨h, hh⟩ := exists_section (T := T) (V := ⊤) (p := p) trivial
  have hi : overResι (T := T) ⊤ ≫ h = 𝟙 _ := by
    haveI : Mono (overResι (T := T) ⊤) := Over.mono_of_mono_left _ (hk := inferInstanceAs (Mono (⊤ : T.left.Opens).ι))
    rw [← cancel_mono (overResι (T := T) ⊤), Category.assoc, hh, Category.comp_id, Category.id_comp]
  exact isThetaPtOver_pull P H _ h hi

theorem weilIs_one_left (hG : GlobalFnsSt) (P : PolAV S) {k : ℤ} {ν : LB.Gen (negLB P.A P.L k T)} (hν : ν.IsGen)
    (θ : ThetaGrp P.A P.L k T) : WeilIs P.A P.L k 1 θ.pt 1 := by
  obtain ⟨o, ho, hv⟩ := exists_symLift_one P.isLB hν 1
  rw [← ho.pt_eq]
  refine weilIs_of_commIsOf hG P.isAb P.isLB ((commIsOf_iff P.isLB _ _ _).2 fun Z r z J hJ => ?_)
  have e : translT P.A (1 : T ⟶ P.A) = 𝟙 _ := by
    rw [translT, ThetaAct.translPt_one, lift_fst_snd]
  rw [hv _ _ z J hJ, hv _ _ z J hJ, ho.pt_eq, e, map_one]
  simp

theorem isThetaPtOver_down (hG : GlobalFnsSt) (P : PolAV S) [Subsingleton T.left] {n m : ℕ} (ho : Odd (n * m))
    {I : Type} {x : I → (T ⟶ P.A)} {v v' : I → Γ(T.left, ⊤)} (hx : ∀ i, (x i ^ n) ^ m ^ 2 = 1)
    (H : IsThetaPtOver P (n * m) x v) (H' : IsThetaPtOver P m (fun i => x i ^ n) v') :
    IsThetaPtOver P m (fun i => x i ^ n) v := by
  rcases isEmpty_or_nonempty I with hI | ⟨⟨i₀⟩⟩
  · rwa [Subsingleton.elim v v']
  obtain ⟨th', s', α', τ', W, t', w', u', hth', hα', hτ', hs', hW, ht', hw', hv⟩ := H
  obtain ⟨th, s, α, τ, U, t, -, -, hth, hα, hτ, hs, hU, ht, -, -⟩ := H'
  obtain ⟨ρ, hρ⟩ := exists_unit_of_isGenSec hth hth'
  obtain ⟨ν, hν, -⟩ := (hW i₀).sym
  obtain ⟨o, hoo, -⟩ := exists_symLift_one P.isLB hν ((n * m) ^ 2)
  obtain ⟨u, hu⟩ := exists_unit_isValueAt hG P.isAb P.isLB (r := n) (q := m ^ 2) rfl
    (pow_dvd_pow_of_dvd (Dvd.intro_left n rfl) 2) ho.pow hρ hα hα' hs hs' hτ' (one_pow n) hoo hτ
  refine ⟨th, s, α, τ, U, t, fun i => ρ * u * w' i, u' * (ρ * u)⁻¹, hth, hα, hτ, hs, hU, ht, fun i => ?_, fun i => ?_⟩
  · have := hu (x i) (U i) (t i) (W i) (t' i) (w' i) 1
      (by rw [show (n * m) ^ 2 = n * m ^ 2 * n by ring, pow_mul, pow_mul, hx, one_pow]) (hU i) (ht i)
      (by rw [_root_.mul_one]; exact hW i) (ht' i) (hw' i)
      (by rw [← (hW i).pt_eq]; exact weilIs_one_left hG P hν _)
    rwa [one_pow, Units.val_one, _root_.mul_one] at this
  · rw [hv, ← Units.val_mul, ← _root_.mul_assoc, ← Units.val_mul, inv_mul_cancel_right]

theorem isThetaPt_down : Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (n m : ℕ) (Ix : Type)
    (x : Ix → (baseOver (Sp K) ⟶ P.A)) (v : Ix → Γ((baseOver (Sp K)).left, ⊤)),
    (∀ i, (x i ^ n) ^ m ^ 2 = 1) → IsThetaPt P (n * m) x v → IsThetaPt P m (fun i => x i ^ n) v := by
  intro hL K _ _ P n m Ix x v hx H
  haveI : Subsingleton (baseOver (Sp K)).left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  haveI : Nonempty (baseOver (Sp K)).left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  have ho : Odd m := (Nat.odd_mul.1 H.1).2
  have hu : IsUnit (m : Γ((baseOver (Sp K)).left, ⊤)) :=
    isUnit_of_mul_isUnit_right (by rw [← Nat.cast_mul]; exact H.2.1)
  have hK : (m : K) ≠ 0 := by
    have := IsUnit.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom hu
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨v', H'⟩ := ThetaPtExist.exists_isThetaPt hL K P m ho hK (fun i => x i ^ n) hx
  exact isThetaPt_of_over P ho hu (isThetaPtOver_down hL.globalFns P H.1 hx (isThetaPtOver_of_subsingleton P H)
    (isThetaPtOver_of_subsingleton P H'))

end GlobalTheory.ThetaNest
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsThetaPtDownStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaPt_pow_of_isThetaPt_mul : Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Sp K)) (n m : ℕ) (Ix : Type) (x : Ix → (baseOver (Sp K) ⟶ P.A)) (v : Ix → Γ((baseOver (Sp K)).left, ⊤)), (∀ i, (x i ^ n) ^ m ^ 2 = 1) → IsThetaPt P (n * m) x v → IsThetaPt P m (fun i => x i ^ n) v := by
  first | exact @GlobalTheory.ThetaNest.isThetaPt_down | exact GlobalTheory.ThetaNest.isThetaPt_down | (intros; apply GlobalTheory.ThetaNest.isThetaPt_down <;> assumption)
end
end
