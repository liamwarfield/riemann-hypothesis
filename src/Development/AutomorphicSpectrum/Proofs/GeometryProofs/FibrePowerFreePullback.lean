module

public import Development.WeilBound.CoreStatements.HodgeTatePoints.LbIsoPullPull
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TateIsoPullbackEquiv
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibrePowerFreePullback
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibrePowerFreePullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.FibPull

theorem fibPF_pull_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (X₂ : Scheme.{0}) (t₂ : SAB H X₂) (f : X₂ ⟶ X0) (_ : SABMap t₂ t f) (z : X₂), FibPF t₂ z ↔ FibPF t (f z) :=
  PositivityTheory.HtPt.Cf.fibpf_pull

end GlobalTheory.CompanionTheory.Ar.FibPull
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FibrePowerFreePullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_power_free_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (X₂ : Scheme.{0}) (t₂ : SAB H X₂) (f : X₂ ⟶ X0) (_ : SABMap t₂ t f) (z : X₂), FibPF t₂ z ↔ FibPF t (f z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FibPull.fibPF_pull_iff | exact GlobalTheory.CompanionTheory.Ar.FibPull.fibPF_pull_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.FibPull.fibPF_pull_iff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentMatchesModelComponent
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentMatchesModelComponent
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CptIn

theorem exists_isTie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j) → ∃ (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li), CptIn.IsTie Z 𝔐 i j := by
  intro E _ _ _ H D l Xo c _ Y U Z S Ω _ K _ J _ y 𝔐 hgen
  obtain ⟨ψ, hψ⟩ := GlobalTheory.CompanionTheory.Ar.GenIso.exists_iso_of_genPt_eq Y.X _ _ 𝔐.ξ₀ (Z.ξ₀ ≫ Y.j) 𝔐.gen₀ Z.gen hgen
  have hdom' : 𝔐.ξ ≫ 𝔐.f = Spec.map (CommRingCat.ofHom (𝔐.fn.comp ψ.toRingHom)) ≫ (Z.ξ₀ ≫ Y.j) := by
    have h1 : 𝔐.ξ ≫ 𝔐.f = Spec.map (CommRingCat.ofHom 𝔐.fn) ≫ 𝔐.ξ₀ := 𝔐.fn_over
    have h2 : Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ (Z.ξ₀ ≫ Y.j) = 𝔐.ξ₀ := hψ
    rw [h1, ← h2, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have hdom : GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ (Z.ξ₀ ≫ Y.j) 𝔐.f (𝔐.fn.comp ψ.toRingHom) := hdom'
  have key : ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (((𝔐.fn.comp ψ.toRingHom).comp Z.inc).comp (algebraMap (𝓞 c.F) c.F)) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
    have e1 := 𝔐.cst_over
    have e2 := Z.over_inc
    have e3 := Y.jQ_over
    rw [← e1, ← Category.assoc, hdom', ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model.j]
    simp only [Category.assoc]
    rw [pullback.condition, ← Category.assoc Y.jQ, e3, ← Category.assoc Z.ξ₀, e2]
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have hcst : (𝔐.fn.comp ψ.toRingHom).comp Z.inc = 𝔐.cst := by
    have k0 : Spec.map (CommRingCat.ofHom (((𝔐.fn.comp ψ.toRingHom).comp Z.inc).comp (algebraMap (𝓞 c.F) c.F))) = Spec.map (CommRingCat.ofHom (𝔐.cst.comp (algebraMap (𝓞 c.F) c.F))) := key
    have k1 := congrArg CommRingCat.Hom.hom (Spec.map_injective k0)
    simp only [CommRingCat.hom_ofHom] at k1
    exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) k1
  letI := CategoryTheory.Over.cartesianMonoidalCategory 𝔐.X
  letI := CategoryTheory.Over.cartesianMonoidalCategory Y.X
  letI : CategoryTheory.GrpObj 𝔐.t.G := 𝔐.t.grp
  letI : CategoryTheory.GrpObj Y.t.G := Y.t.grp
  letI : Group (Over.mk 𝔐.ξ ⟶ 𝔐.t.G) := CategoryTheory.Hom.group
  letI : Group (Over.mk (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G) := CategoryTheory.Hom.group
  letI : Group (GlobalTheory.CompanionTheory.Ar.epsAt (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G) := CategoryTheory.Hom.group
  letI : Group (Over.mk ((GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f) ⟶ Y.t.G) := CategoryTheory.Hom.group
  have hpb : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback 𝔐.t.G Y.t.G 𝔐.f 𝔐.m.φ := 𝔐.m.cart
  have hone : (1 : Over.mk 𝔐.ξ ⟶ 𝔐.t.G).left ≫ 𝔐.m.φ = (1 : Over.mk (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G).left := by
    obtain ⟨o, ho⟩ : ∃ o : Over.mk (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G, o.left = (1 : Over.mk 𝔐.ξ ⟶ 𝔐.t.G).left ≫ 𝔐.m.φ :=
      ⟨Over.homMk ((1 : Over.mk 𝔐.ξ ⟶ 𝔐.t.G).left ≫ 𝔐.m.φ) (by
        rw [Category.assoc, hpb.1.w, ← Category.assoc, Over.w]; rfl), rfl⟩
    have hoo : o * o = o := by
      apply Over.OverMorphism.ext
      rw [hpb.2 (Over.mk 𝔐.ξ) 1 1 o o ho ho, mul_one, ho]
    have ho1 : o = 1 := by simpa using hoo
    rw [← ho, ho1]
  have hT : GlobalTheory.CompanionTheory.Ar.epsAt (𝔐.ξ ≫ 𝔐.f) = Over.mk ((GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f) := by
    simp [GlobalTheory.CompanionTheory.Ar.epsAt]
  have hx0 : ∀ e : 𝔐.Li, ((𝔐.M.pt e).left ≫ 𝔐.m.φ) ≫ Y.t.G.hom = (Over.mk ((GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f)).hom := by
    intro e
    rw [Category.assoc, hpb.1.w, ← Category.assoc, Over.w]; rfl
  let x₀ : 𝔐.Li → (Over.mk ((GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f) ⟶ Y.t.G) := fun e => Over.homMk ((𝔐.M.pt e).left ≫ 𝔐.m.φ) (hx0 e)
  let pt' : 𝔐.Li → (GlobalTheory.CompanionTheory.Ar.epsAt (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G) := fun e => eqToHom hT ≫ x₀ e
  have hleft : ∀ e, (pt' e).left = (𝔐.M.pt e).left ≫ 𝔐.m.φ := by
    intro e
    simp [pt', x₀]
  have hx0mul : ∀ e e', x₀ (e + e') = x₀ e * x₀ e' := by
    intro e e'
    apply Over.OverMorphism.ext
    rw [hpb.2 (GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ) (𝔐.M.pt e) (𝔐.M.pt e') (x₀ e) (x₀ e') rfl rfl, ← 𝔐.M.add]
    rfl
  have hadd : ∀ e e', pt' (e + e') = pt' e * pt' e' := by
    intro e e'
    simp only [pt']
    rw [hx0mul, MonObj.comp_mul]
  have htan : ∀ e, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G (𝔐.ξ ≫ 𝔐.f) (pt' e) := by
    intro e
    have h := 𝔐.M.tan e
    unfold GlobalTheory.CompanionTheory.Ar.IsTanAt at h ⊢
    rw [hleft, ← Category.assoc, h, hone]
  have hinj : Function.Injective pt' := by
    intro e e' hee
    apply 𝔐.M.inj
    apply Over.OverMorphism.ext
    apply hpb.1.hom_ext
    · rw [← hleft, ← hleft, hee]
    · rw [Over.w, Over.w]
  have hfa : (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom.comp (algebraMap Ω (DualNumber Ω)) = RingHom.id Ω := by
    ext r
    simp
  have honto : ∀ v : GlobalTheory.CompanionTheory.Ar.epsAt (𝔐.ξ ≫ 𝔐.f) ⟶ Y.t.G, GlobalTheory.CompanionTheory.Ar.IsTanAt Y.t.G (𝔐.ξ ≫ 𝔐.f) v → ∃ e, pt' e = v := by
    intro v hv
    have hw : v.left ≫ Y.t.G.hom = (GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom ≫ 𝔐.f := by
      rw [Over.w]
      simp [GlobalTheory.CompanionTheory.Ar.epsAt]
    obtain ⟨L, hL1, hL2⟩ : ∃ L, L ≫ 𝔐.m.φ = v.left ∧ L ≫ 𝔐.t.G.hom = (GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ).hom :=
      ⟨_, hpb.1.lift_fst _ _ hw, hpb.1.lift_snd _ _ hw⟩
    have htw : GlobalTheory.CompanionTheory.Ar.IsTanAt 𝔐.t.G 𝔐.ξ (Over.homMk (U := GlobalTheory.CompanionTheory.Ar.epsAt 𝔐.ξ) L hL2) := by
      unfold GlobalTheory.CompanionTheory.Ar.IsTanAt at hv ⊢
      apply hpb.1.hom_ext
      · rw [Category.assoc]
        change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom) ≫ L ≫ 𝔐.m.φ = _
        rw [hL1, hv, hone]
      · rw [Category.assoc]
        change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom) ≫ L ≫ 𝔐.t.G.hom = _
        rw [hL2, Over.w]
        show Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom Ω Ω Ω).toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω (DualNumber Ω))) ≫ 𝔐.ξ = 𝔐.ξ
        rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hfa, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    obtain ⟨e, he⟩ := 𝔐.M.onto _ htw
    refine ⟨e, Over.OverMorphism.ext ?_⟩
    rw [hleft, he]
    exact hL1
  have hsmul : ∀ (a : Ω) (e : 𝔐.Li), (pt' (a • e)).left = Spec.map (CommRingCat.ofHom (GlobalTheory.CompanionTheory.Ar.epsMul a)) ≫ (pt' e).left := by
    intro a e
    rw [hleft, hleft, 𝔐.M.smul, Category.assoc]
  let M' : GlobalTheory.CompanionTheory.Ar.LieModel Y.t.G (𝔐.ξ ≫ 𝔐.f) 𝔐.Li := ⟨pt', htan, hinj, honto, hadd, hsmul⟩
  have hsm : AlgebraicGeometry.Smooth Y.t.G.hom := @ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian.smooth _ _ _ Y.t.semi
  obtain ⟨j, hj1, hj2, -⟩ := GlobalTheory.CompanionTheory.Ar.OrVert.LieCmp.exists_ext hsm (𝔐.fn.comp ψ.toRingHom) (Z.ξ₀ ≫ Y.j) (𝔐.ξ ≫ 𝔐.f) hdom'.symm Z.M M'
  refine ⟨𝔐.fn.comp ψ.toRingHom, j, ?_⟩
  unfold GlobalTheory.CompanionTheory.Ar.Flat.CptIn.IsTie
  exact ⟨hdom, hcst, hj2, fun e => (hleft (j e)).symm.trans (hj1 e)⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CptIn
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentMatchesModelComponentStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_component_matches_model_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) [NumberField c.F] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (U : Set (Xo.XF c)) (Z : CptOver Y U) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), genPt 𝔐.ξ₀ = genPt (Z.ξ₀ ≫ Y.j) → ∃ (i : Z.Ω →+* Ω) (j : Z.V →+ 𝔐.Li), CptIn.IsTie Z 𝔐 i j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.CptIn.exists_isTie | exact GlobalTheory.CompanionTheory.Ar.Flat.CptIn.exists_isTie | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.CptIn.exists_isTie <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingBaseChangeUnit
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingBaseChangeUnit
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

private theorem gm_unitRes' {S : Scheme} {T : Over S} (V : T.left.Opens) {Z : Scheme}
    (r : Z ⟶ (Out.overRes V).left) (z : Z) (a : (↑(T.left.presheaf.obj (Opposite.op ⊤)))ˣ) :
    gm r z ⊤ (Out.unitRes V a) = gm (r ≫ V.ι) z ⊤ a :=
  gm_pull r V.ι z ⊤ trivial a

private theorem unitOn_units_map {k M : Type} [Field k] [Field M] (j : k →+* M) (c : kˣ) :
    unitOn (Units.map j.toMonoidHom c) = Units.map (spMap j).appTop.hom (unitOn c) := by
  ext
  show (Scheme.ΓSpecIso (CommRingCat.of M)).inv.hom (j c) =
    (Spec.map (CommRingCat.ofHom j)).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)
  exact congrArg (fun g => g.hom (c : k)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))

theorem weilIs_fieldExt : ∀ {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB → ∀ (k M : Type) [Field k] [Field M] (j : k →+* M) (q : Sp k ⟶ X) (q' : Sp M ⟶ X), q' = spMap j ≫ q → ∀ (n : ℤ) (x y : Over.mk q ⟶ G) (x' y' : Over.mk q' ⟶ G), x'.left = spMap j ≫ x.left → y'.left = spMap j ≫ y.left → ∀ (c : kˣ) (c' : Mˣ), Out.WeilIs G L n x y (unitOn c) → Out.WeilIs G L n x' y' (unitOn c') → c' = Units.map j.toMonoidHom c := by
  intro X G _ _ L hL k M _ _ j q q' hq n x y x' y' hx hy c c' h1 h2
  let p' : (Over.mk q').left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum M)
  obtain ⟨V', hpV', -, H2⟩ := h2 p'
  obtain ⟨V, hpV, ⟨θx₀, θy₀, hθx₀, hθy₀⟩, H1'⟩ := h1 ((spMap j).base p')
  have H1 := H1' θx₀ θy₀ hθx₀ hθy₀
  have key : ∀ I : Ideal k, I.IsPrime → I = ⊥ := fun I _ => Ideal.eq_bot_of_prime I
  have hall : ∀ z : (Over.mk q).left, z ∈ V := by
    intro z
    have hz : z = (spMap j).base p' := by
      apply PrimeSpectrum.ext
      exact (key z.asIdeal z.isPrime).trans (key _ ((spMap j).base p').isPrime).symm
    rw [hz]; exact hpV
  let τ : (Out.overRes V').left ⟶ (Out.overRes V).left :=
    IsOpenImmersion.lift V.ι (V'.ι ≫ spMap j) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      exact hall _)
  have hτι : τ ≫ V.ι = V'.ι ≫ spMap j := IsOpenImmersion.lift_fac _ _ _
  have hτ : τ ≫ (Out.overRes V).hom = (Out.overRes V').hom ≫ 𝟙 X := by
    change τ ≫ (V.ι ≫ q) = (V'.ι ≫ q') ≫ 𝟙 X
    rw [← Category.assoc, hτι, hq]
    simp
  haveI : IsMonHom (Iso.refl G).hom := by
    show IsMonHom (𝟙 G)
    infer_instance
  have hp : IsGrpPullback G G (𝟙 X) (𝟙 G.left) :=
    (isGrpPullback_of_iso (Iso.refl G)).congr rfl (by simp)
  obtain ⟨w, hw⟩ : LBIso L (L.pull (𝟙 G.left)) :=
    LBIso.chartPull (chartPullId L) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull L (𝟙 _) (𝟙 _) rfl) (GlobalTheory.PolBaseChange.lbIso_refl hL)
  have hxpt : τ ≫ θx₀.pt.left = (Out.overResι V' ≫ x').left ≫ 𝟙 G.left := by
    rw [hθx₀]
    change τ ≫ (V.ι ≫ x.left) = (V'.ι ≫ x'.left) ≫ 𝟙 G.left
    rw [hx, Category.comp_id, ← Category.assoc τ, hτι, Category.assoc]
  have hypt : τ ≫ θy₀.pt.left = (Out.overResι V' ≫ y').left ≫ 𝟙 G.left := by
    rw [hθy₀]
    change τ ≫ (V.ι ≫ y.left) = (V'.ι ≫ y'.left) ≫ 𝟙 G.left
    rw [hy, Category.comp_id, ← Category.assoc τ, hτι, Category.assoc]
  obtain ⟨θx, hθx, hPx⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_theta_move hp τ hτ hL hL w hw n (Out.overResι V' ≫ x') θx₀ hxpt
  obtain ⟨θy, hθy, hPy⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_theta_move hp τ hτ hL hL w hw n (Out.overResι V' ≫ y') θy₀ hypt
  have hgm : ∀ (Z : Scheme) (r : Z ⟶ (Out.overRes V').left) (z : Z),
      gm (r ≫ τ) z ⊤ (Out.unitRes V (unitOn c)) =
        gm r z ⊤ (Out.unitRes V' (unitOn (Units.map j.toMonoidHom c))) := by
    intro Z r z
    rw [gm_unitRes', gm_unitRes', unitOn_units_map]
    erw [gm_pull (r ≫ V'.ι) (spMap j) z ⊤ trivial (unitOn c)]
    rw [Category.assoc, hτι, Category.assoc]
  have HC := ReciprocityTheory.ChartRestriction.G.H1.commIsOf_move hp τ hτ hL hL w n θx₀ θy₀ θx θy
    (by rw [hθx]; exact hxpt) (by rw [hθy]; exact hypt) hPx hPy _ _ hgm H1
  have HC2 := H2 θx θy hθx hθy
  have heq := ReciprocityTheory.ChartRestriction.G.H1.commIsOf_unique hL θx θy _ _ HC2 HC
  let pt : (Out.overRes V').left := ⟨p', hpV'⟩
  have e := (gm_unitRes' V' (𝟙 (Out.overRes V').left) pt (unitOn c')).symm.trans
    ((congrArg (gm (𝟙 (Out.overRes V').left) pt ⊤) heq).trans
      (gm_unitRes' V' (𝟙 (Out.overRes V').left) pt _))
  have e' := (gm_val (𝟙 (Out.overRes V').left ≫ V'.ι) pt ⊤ trivial (unitOn c')).symm.trans
    ((congrArg Units.val e).trans
      (gm_val (𝟙 (Out.overRes V').left ≫ V'.ι) pt ⊤ trivial _))
  apply Units.ext
  refine (RingHom.injective
    (((Out.overRes V').left.presheaf.germ ((TopologicalSpace.Opens.map (𝟙 (Out.overRes V').left ≫ V'.ι).base).obj ⊤)
      pt trivial).hom.comp
      (((𝟙 (Out.overRes V').left ≫ V'.ι).app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of M)).inv.hom))) ?_
  have e'' := by simpa [unitOn] using e'
  exact e''

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilPairingBaseChangeUnitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_pairing_base_change_unit : ∀ {X : Scheme.{0}} (G : Over X) [GrpObj G] [IsCommMonObj G] (L : LB G.left), L.IsLB → ∀ (k M : Type) [Field k] [Field M] (j : k →+* M) (q : Sp k ⟶ X) (q' : Sp M ⟶ X), q' = spMap j ≫ q → ∀ (n : ℤ) (x y : Over.mk q ⟶ G) (x' y' : Over.mk q' ⟶ G), x'.left = spMap j ≫ x.left → y'.left = spMap j ≫ y.left → ∀ (c : kˣ) (c' : Mˣ), Out.WeilIs G L n x y (unitOn c) → Out.WeilIs G L n x' y' (unitOn c') → c' = Units.map j.toMonoidHom c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.weilIs_fieldExt | exact GlobalTheory.CompanionTheory.Ar.weilIs_fieldExt | (intros; apply GlobalTheory.CompanionTheory.Ar.weilIs_fieldExt <;> assumption)
end
end
