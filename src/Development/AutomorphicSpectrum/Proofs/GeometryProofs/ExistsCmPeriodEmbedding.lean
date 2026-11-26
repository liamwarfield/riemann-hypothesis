module

public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.VerticalDivisorsCommute
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PurePeriodLocalBasisExists
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPureFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemeModelBaseChangeSubalgebra

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.SesquilinearFractions.GRational
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
open scoped CategoryTheory.Obj

namespace PositivityTheory.Xgf

def pureTypeSign (b : Bool) : ℤˣ := if b then 1 else -1

theorem sgnRt_eq_sign_mul {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (b : Bool) :
    sgnRt H b = ((pureTypeSign b : ℤ) : ℂ) * H.rt0 := by
  cases b <;> simp [sgnRt, pureTypeSign]

open GlobalTheory.CM GlobalTheory.PointAlg ReciprocityTheory.GeometryOfNumbersTheory IsDedekindDomain in
set_option maxHeartbeats 1000000 in
theorem family_pure_periods_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (n : ℕ), 0 < n → (∀ y : (FU.Di i).La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) → ∃ (K₁ : IntermediateField ℚ ℂ) (hk : KA l ≤ K₁) (y : Sp K₁ ⟶ Xo.X), FiniteDimensional ℚ K₁ ∧ y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i P := by
  intro E _ _ _ H D l Xo cc g ty FU i Pe hP nn hnn hfi
  have hC := GlobalTheory.cmCurve_closed
  have hPt := GlobalTheory.cmPoint_closed
  have hT := GlobalTheory.thetaUnifAV_all
  have hL := GlobalTheory.allSixLaws.1
  have hd := H.d_mod
  obtain ⟨K, _, h2, hr⟩ := exists_quadraticField_sq_eq_neg H.d_prime.pos
  obtain ⟨M, _, w, P, v, hw, hg, hv, -, hcm, -⟩ := hC H.d (by omega) H.d_prime.squarefree (by omega) K h2 hr
  have := PureType.finiteDimensional_base l
  let k : IntermediateField ℚ ℂ := M ⊔ KA l
  have hk : KA l ≤ k := le_sup_right
  have hfin : FiniteDimensional ℚ k := inferInstance
  let f : 𝓞 M →+* k := (IntermediateField.inclusion (le_sup_left : M ≤ k)).toRingHom.comp (algebraMap (𝓞 M) M)
  obtain ⟨P₀, π, hg₀, hπ, hL₀⟩ := PureType.exists_baseChange hL.polBaseChange (spMap f) P
  obtain ⟨PC, ψ, hgC, hψ, hLC⟩ := PureType.exists_baseChange hL.polBaseChange (spMap (algebraMap k ℂ)) P₀
  obtain ⟨v₀, hv₀, -⟩ := PureType.exists_tangent_over f hπ (hv.1 0)
  obtain ⟨u₀, hu⟩ := PureType.exists_isThetaUnif hT PC
  have hLL : LBIso PC.L (P.L.pull (ψ ≫ π)) :=
    LBIso.trans PC.isLB (LB.isLB_pull P₀.isLB ψ) (LB.isLB_pull P.isLB _) hLC
      (LBIso.chartPull (chartPullPull P₀.L ψ ψ rfl) (chartPullSame P.L _ _ _ ψ fun _ => rfl) hL₀)
  obtain ⟨c, hc0, hc⟩ := hcm PC (ψ ≫ π) ⟨hgC.trans hg₀, (hψ.comp hπ).congr (spMap_comp_spMap _ _) rfl, hLL.symm⟩ u₀
  rw [hw] at hc
  obtain ⟨R, hR, -, y, t, m, vR, φ, hy, hj, -, -, hφ⟩ := hPt E H D l Xo g ty FU i Pe hP k hk hfin P₀ v₀ (hg₀.trans hg) hv₀
    PC ψ u₀ c (hgC.trans (hg₀.trans hg)) hψ hLC hu hc0 hc (fun _ => ∅) (fun _ => Set.finite_empty) ⊥ Subalgebra.fg_bot
  obtain ⟨-, bo, a₀, ha₀⟩ := periods_span_pure_decomposition E H (FU.Di i) g ty Pe hP nn hnn hfi
  let ε : Fin g → ℤˣ := fun j => pureTypeSign (bo j)
  let a : ∀ j, PureType.lat hP (((ε j : ℤ) : ℂ) * H.rt0) := fun j =>
    ⟨(a₀ j).1, (congrArg (fun ρ => (a₀ j).1 ∈ PureType.lat hP ρ) (sgnRt_eq_sign_mul H (bo j))).mp (a₀ j).2⟩
  have ha : ∀ z : Fin g → ℂ, ∃ s : Fin g → ℂ, z = ∑ j, s j • Pe (a j) := ha₀
  have hρ : ∀ ρ : R →ₐ[k] ℂ, spMap ρ.toRingHom ≫ spMap (algebraMap k R) = spMap (algebraMap k ℂ) := fun ρ =>
    (spMap_comp_spMap _ _).trans (congrArg _ ρ.comp_algebraMap)
  have hB := isGrpPullback_pullback P₀.A (spMap (algebraMap k R))
  have hA : IsAbelianScheme t.G := by
    have := Xo.univ.proper
    have : IsProper t.G.hom := MorphismProperty.of_isPullback m.cart.1 this
    exact AbelianSchemeGerms.isAbelianScheme_of_proper _ t.semi
  have onto := onto_of_onto R.val.toRingHom Subtype.val_injective hA
    (Out.TLinPf.isAb_pullback (spMap (algebraMap k R)) P₀.A P₀.isAb) (fun n => φ (ε n) (a n)) fun y' => by
      obtain ⟨z, hz⟩ := FU.ex_onto i Pe hP (Over.homMk (y'.left ≫ m.φ) (by
        rw [Category.assoc, m.cart.1.w, ← Category.assoc, Over.w y']
        exact hj))
      obtain ⟨b, rfl⟩ := ha z
      choose x hx using fun n => exists_lift_pt (G := P₀.A) (G' := (Over.pullback (spMap (algebraMap k R))).obj P₀.A) hB.1 (t' := spMap R.val.toRingHom)
        ((u₀.ex fun _ => c * b n).left ≫ ψ) (by
          rw [Category.assoc, hψ.1.w, ← Category.assoc, Over.w, hρ]
          exact Category.id_comp _)
      refine ⟨x, pt_ext m.cart.1 ?_⟩
      rw [prod_left m.cart hj _ (fun n => FU.ex i Pe (b n • Pe (a n))) fun n =>
        (Category.assoc _ _ _).trans ((hφ (ε n)).2 (a n) (b n) (x n).left (hx n) (Over.w (x n))),
        ← map_sum_eq_prod _ (FU.ex_add i Pe hP), hz]
      rfl
  have hs : Smooth Xo.s := by
    have := Xo.smooth
    exact SmoothOfRelativeDimension.smooth D.dim Xo.s
  obtain ⟨K₁, hk₁, y₁, h₁, h₂, h₃⟩ := exists_numberField_point_of_countable k R hR (KA l)
    (IntermediateField.inclusion hk).toRingHom Xo.X Xo.s y hy (by
      refine (countable_points_of_onto hT hL E H D l Xo g ty FU PC).mono ?_
      rintro _ ⟨ρ, rfl⟩
      refine ⟨?_, ?_⟩
      · rw [Category.assoc, hy, spMap_comp_spMap]
        exact congrArg spMap (RingHom.ext fun x => ρ.commutes _)
      obtain ⟨t', ⟨m'⟩⟩ : ∃ t' : SAB H (Sp ℂ), Nonempty (SABMap t' Xo.univ.t (spMap ρ.toRingHom ≫ y)) := by
        let f := spMap ρ.toRingHom ≫ y
        let t := Xo.univ.t
        have h := isGrpPullback_pullback t.G f
        obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := Out.CubePf.cubePull _ _ t.G _ (cubeMapOf h) t.PP t.cub
        have hact : ∀ a, ((OAct.pullback f t.G t.act).act a).left ≫ pullback.fst t.G.hom f =
            pullback.fst t.G.hom f ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
        have pa : ∀ {T : Over (Sp ℂ)} (x : T ⟶ (Over.pullback f).obj t.G) a,
            pushPt h.1.w (x ≫ (OAct.pullback f t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
          Over.OverMorphism.ext (by
            show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
            rw [Category.assoc, hact, Category.assoc])
        have hsemi : IsSemiAbelian ((Over.pullback f).obj t.G) := by
          refine { comm := ?_, smooth := ?_, separated := ?_, quasiCompact := ?_, geomConnected := ?_, fibres := ?_ }
          · have := t.semi.comm; infer_instance
          · have := t.semi.smooth; change Smooth (pullback.snd t.G.hom f); infer_instance
          · have := t.semi.separated; change IsSeparated (pullback.snd t.G.hom f); infer_instance
          · have := t.semi.quasiCompact; change QuasiCompact (pullback.snd t.G.hom f); infer_instance
          · have := t.semi.geomConnected; change GeometricallyConnected (pullback.snd t.G.hom f); infer_instance
          · intro Ω _ _ q
            obtain ⟨E⟩ := t.semi.fibres Ω (q ≫ f)
            exact ⟨torusExtOfIso (pullCompIso q f t.G) E⟩
        refine ⟨⟨(Over.pullback f).obj t.G, hsemi,
          OAct.pullback f t.G t.act, (cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, ?_, ?_⟩,
          ⟨⟨cubeMapOf h, h, rfl, hact, hc'⟩⟩⟩
        · intro a
          let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
            (pushPt h.1.w (snd ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
          refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
            (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
          · fin_cases i
            · exact (pa _ a).trans (by simp [U])
            · simp [U]
          · fin_cases i
            · simp [U]
            · exact (pa _ _).trans (by simp [U])
        · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj t.G))
          refine LBIso.chartPull (chartPullPull t.PP.L _ U.left (Category.id_comp _))
            (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
          fin_cases i
          · simp [U]
          · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
      let κ := m.cart.1.lift m'.φ (t'.G.hom ≫ spMap ρ.toRingHom) (by rw [m'.cart.1.w, Category.assoc])
      have hγ : IsGrpPullback t'.G t.G (spMap ρ.toRingHom) κ :=
        m.cart.cancel (m'.cart.congr rfl (m.cart.1.lift_fst _ _ _).symm) (m.cart.1.lift_snd _ _ _)
      let β := hB.1.lift ψ (PC.A.hom ≫ spMap ρ.toRingHom) (by rw [hψ.1.w, Category.assoc, hρ])
      have hβ : IsGrpPullback PC.A _ (spMap ρ.toRingHom) β :=
        hB.cancel (hψ.congr (hρ ρ).symm (hB.1.lift_fst _ _ _).symm) (hB.1.lift_snd _ _ _)
      choose w' hw₁ hw₂ using fun n => @exists_lift_hom _ _ _ _ _ _ _ _ _ _ _ _ _ hβ hγ (φ (ε n) (a n))
        ((hφ (ε n)).1.1 (a n))
      refine ⟨t', m', _, w', hw₁, fun y' => ?_⟩
      obtain ⟨x, hx⟩ := onto_lift hβ.1 hγ _ w' hw₂ (Category.id_comp _) (onto _) y'
      exact ⟨_, id, x, hx⟩)
  exact ⟨K₁, hk.trans hk₁, y₁, h₁, h₂, h₃.trans hj⟩

end PositivityTheory.Xgf
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPeriodAlgebraic
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyPurePeriodsSpan
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyPurePeriodsSpan
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ggeo

theorem point_numberField_of_finiteIndex : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (n : ℕ), 0 < n → (∀ y : (FU.Di i).La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) → ∃ (K₁ : IntermediateField ℚ ℂ) (hk : KA l ≤ K₁) (y : Sp K₁ ⟶ Xo.X), FiniteDimensional ℚ K₁ ∧ y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i P :=
  @PositivityTheory.Xgf.family_pure_periods_span

end GlobalTheory.CompanionTheory.Ggeo
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FamilyPurePeriodsSpanStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_pure_periods_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (n : ℕ), 0 < n → (∀ y : (FU.Di i).La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) → ∃ (K₁ : IntermediateField ℚ ℂ) (hk : KA l ≤ K₁) (y : Sp K₁ ⟶ Xo.X), FiniteDimensional ℚ K₁ ∧ y ≫ Xo.s = spMap (IntermediateField.inclusion hk).toRingHom ∧ spMap (algebraMap K₁ ℂ) ≫ y = FU.u i P := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.point_numberField_of_finiteIndex | exact GlobalTheory.CompanionTheory.Ggeo.point_numberField_of_finiteIndex | (intros; apply GlobalTheory.CompanionTheory.Ggeo.point_numberField_of_finiteIndex <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPeriodAlgebraic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CM.PeriodModel GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Fl.CMGiven

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_desc (hU : ThetaUnifAV) (hL : Out.Laws) {D : Datum H} {l : Level H} {Xo : Moduli D l} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n)
    {P : (FU.Di i).La →+ (Fin g → ℂ)} (hP : IsPeriod (FU.Di i) ty P)
    (k₀ : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k₀] {ω₀ : k₀} (C₀ : Ell H k₀ ω₀)
    {ω' : ℂ} (C' : Ell H ℂ ω') {φ : C'.P.A.left ⟶ C₀.P.A.left} (c' : EllMap C' C₀ (algebraMap k₀ ℂ) φ)
    (u : HolUnif C'.P.A C'.P.L C'.P.g) (hu : PureType.IsThetaUnif u) {c : ℂ} (hc : c ≠ 0)
    (hΛ : PureType.IsQuadLattice u.Λ H.d c) {ρ : ℂ} (hρ : 2 * ω' - 1 = ρ) {ε : ℤˣ}
    (hε : 0 < ((ε : ℤ) : ℝ) * ω'.im) {h : (FU.Di i).La → (FU.Di i).La → OK H} (hh : IsKForm (FU.Di i) ε h)
    (T : PAT H (Sp k₀)) (T' : PAT H (Sp ℂ)) (n : SABMap T'.t Xo.univ.t (FU.u i P))
    (mT : SABMap T'.t T.t (spMap (algebraMap k₀ ℂ))) :
    ∃ k₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₁ ∧ k₀ ≤ k₁ ∧
      ∀ (K : IntermediateField ℚ ℂ) (e : k₀ ≤ K), k₁ ≤ K → ∀ (ω₂ : K) (C₂ : Ell H K ω₂)
        (φ₂ : C₂.P.A.left ⟶ C₀.P.A.left) (φ₃ : C'.P.A.left ⟶ C₂.P.A.left) (T₂ : PAT H (Sp K))
        (m₂ : SABMap T₂.t T.t (spMap (IntermediateField.inclusion e).toRingHom))
        (m₃ : SABMap T'.t T₂.t (spMap (algebraMap K ℂ))) (f : Sp K ⟶ Xo.X) (m : SABMap T₂.t Xo.univ.t f),
        EllMap C₂ C₀ (IntermediateField.inclusion e).toRingHom φ₂ → EllMap C' C₂ (algebraMap K ℂ) φ₃ →
        φ₃ ≫ φ₂ = φ → m₃.φ ≫ m₂.φ = mT.φ → m₃.φ ≫ m.φ = n.φ →
        ∃ ψ : PureType.lat hP ρ → (C₂.P.A ⟶ T₂.t.G), IsFam C₂ T₂ h _ ψ ∧
          ∀ a (z : ℂ), ((u.ex fun _ => c * z).left ≫ φ₃ ≫ (ψ a).left) ≫ m.φ = (FU.ex i P (z • P a)).left := by
  subst hρ
  obtain ⟨ψ', hψ', hex⟩ := GlobalTheory.T.exists_cmCurve_homFamily_to_fibre_at_period hU hL E H D l Xo g ty FU i P hP _ C' u c T' n ε _ hu hc hΛ hε hh
  obtain ⟨k₁, hk₁, hle, hdesc⟩ := GlobalTheory.T.cmFamily_descends_to_numberField hU hL E H k₀ _ C₀ (FU.Di i) _ T _ _ C' φ T' mT ψ' c' hψ'
  refine ⟨k₁, hk₁, hle, fun K e eK ω₂ C₂ φ₂ φ₃ T₂ m₂ m₃ f m c₂ c₃ hφ hm hn => ?_⟩
  obtain ⟨ψ₂, hψ₂, hsq⟩ := hdesc K e eK _ C₂ φ₂ φ₃ T₂ m₂ m₃ c₂ c₃ hφ hm
  refine ⟨ψ₂, hψ₂, fun a z => ?_⟩
  rw [← hex, ← hn, ← Category.assoc _ m₃.φ, Over.comp_left, Category.assoc _ _ m₃.φ]
  exact congrArg (fun q => (_ ≫ q) ≫ m.φ) (hsq a).symm

theorem exists_tower (hB : Out.PolBaseChangeSt) {M k₀ K : IntermediateField ℚ ℂ} [NumberField M] [NumberField K]
    (e₂ : M ≤ k₀) (e₅ : k₀ ≤ K) {ω : 𝓞 M} (C : Ell H (𝓞 M) ω) {ω₀ : k₀} (C₀ : Ell H k₀ ω₀)
    {φ₀ : C₀.P.A.left ⟶ C.P.A.left}
    (c₀ : EllMap C₀ C ((IntermediateField.inclusion e₂).toRingHom.comp (algebraMap (𝓞 M) M)) φ₀)
    {ω' : ℂ} (C' : Ell H ℂ ω') {φ : C'.P.A.left ⟶ C₀.P.A.left} (c' : EllMap C' C₀ (algebraMap k₀ ℂ) φ) :
    ∃ (ω₁ : 𝓞 K) (C₁ : Ell H (𝓞 K) ω₁) (φ₁ : C₁.P.A.left ⟶ C.P.A.left) (ω₂ : K) (C₂ : Ell H K ω₂)
      (φ₁₂ : C₂.P.A.left ⟶ C₁.P.A.left) (φ₂ : C₂.P.A.left ⟶ C₀.P.A.left) (φ₃ : C'.P.A.left ⟶ C₂.P.A.left),
      EllMap C₁ C (RingOfIntegers.mapRingHom (IntermediateField.inclusion (e₂.trans e₅)).toRingHom) φ₁ ∧
      EllMap C₂ C₁ (algebraMap (𝓞 K) K) φ₁₂ ∧ EllMap C₂ C₀ (IntermediateField.inclusion e₅).toRingHom φ₂ ∧
      EllMap C' C₂ (algebraMap K ℂ) φ₃ ∧ φ₃ ≫ φ₂ = φ ∧ φ₁₂ ≫ φ₁ = φ₂ ≫ φ₀ := by
  obtain ⟨C₁, φ₁, c₁⟩ := exists_ellMap hB E H _ ω C (𝓞 K)
    (RingOfIntegers.mapRingHom (IntermediateField.inclusion (e₂.trans e₅)).toRingHom)
  obtain ⟨C₂, φ₁₂, c₁₂⟩ := exists_ellMap hB E H _ _ C₁ K (algebraMap (𝓞 K) K)
  obtain ⟨φ₂, c₂, hφ₂⟩ := (Factor.ellMap_cancel_and_sabMap_cancel E H (𝓞 M) k₀ K _
    (IntermediateField.inclusion e₅).toRingHom).1 _ _ _ C C₀ C₂ φ₀ _ c₀
    ((EllComp.ellMap_comp E H _ _ C _ _ C₁ _ _ c₁).1 _ _ C₂ _ _ c₁₂)
  obtain ⟨φ₃, c₃, hφ₃⟩ := (Factor.ellMap_cancel_and_sabMap_cancel E H k₀ K ℂ _ (algebraMap K ℂ)).1
    _ _ _ C₀ C₂ C' φ₂ φ c₂ c'
  exact ⟨_, C₁, φ₁, _, C₂, φ₁₂, φ₂, φ₃, c₁, c₁₂, c₂, c₃, hφ₃, hφ₂.symm⟩

theorem sgnRt_sq (b : Bool) : sgnRt H b ^ 2 = -(H.d : ℂ) := by
  unfold sgnRt
  split_ifs <;> simp [H.sqrt_neg_disc_sq]

theorem exists_pack_given : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (n : ℕ) (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k → 0 < n → (∀ y : (FU.Di i).La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) → ∃ X : CMPack Z c FU i hP, k ≤ X.K := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP n k hkf hn hy
  have := c.fin
  have hU : ThetaUnifAV := GlobalTheory.thetaUnifAV_closed
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  have hX : HomExtDvr := GlobalTheory.CM.homExtDvr_of_card_torsion GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional
  have hK : Published.KernelFiniteFlatSt := GlobalTheory.kernelFiniteFlat_holds
  have hB := hL.polBaseChange
  obtain ⟨K₀, hK₀, y₀, _, hy₀, hy₀'⟩ := GlobalTheory.T.family_pure_periods_span E H D l Xo c g ty FU i P hP n hn hy
  obtain ⟨hg0, bb0, a0, hspan0⟩ := GlobalTheory.T.periods_span_pure_decomposition E H (FU.Di i) g ty P hP n hn hy

  obtain ⟨k₀, _, e₁, e₂, e₃, e₆⟩ : ∃ k₀ : IntermediateField ℚ ℂ, FiniteDimensional ℚ k₀ ∧ K₀ ≤ k₀ ∧
      (∀ b, (Z b).M ≤ k₀) ∧ k ≤ k₀ ∧ c.F ≤ k₀ :=
    ⟨K₀ ⊔ (Z true).M ⊔ (Z false).M ⊔ k ⊔ c.F, inferInstance,
      le_sup_left.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)),
      fun b => by
        cases b
        · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
        · exact le_sup_right.trans (le_sup_left.trans (le_sup_left.trans le_sup_left)),
      le_sup_right.trans le_sup_left, le_sup_right⟩
  choose C₀ φ₀ c₀ using fun b => exists_ellMap hB E H _ (Z b).ω (Z b).C k₀
    ((IntermediateField.inclusion (e₂ b)).toRingHom.comp (algebraMap (𝓞 (Z b).M) (Z b).M))
  choose φ c' hφ using fun b => (Factor.ellMap_cancel_and_sabMap_cancel E H (𝓞 (Z b).M) k₀ ℂ _
    (algebraMap k₀ ℂ)).1 _ _ _ (Z b).C (C₀ b) (Z b).C' (φ₀ b) (Z b).π (c₀ b) (Z b).map
  obtain ⟨T, mT, -⟩ := exists_pat_univ Xo (spMap (IntermediateField.inclusion e₁).toRingHom ≫ y₀)
  obtain ⟨T', nT, -⟩ := exists_pat_univ Xo (FU.u i P)
  obtain ⟨mT', hmT'⟩ := (Factor.ellMap_cancel_and_sabMap_cancel E H k₀ k₀ ℂ (RingHom.id _) (algebraMap k₀ ℂ)).2
    _ _ _ _ _ _ mT nT (by rw [← Category.assoc, spMap_comp_spMap]; exact hy₀')

  choose ε hε using fun b => exists_sign (H := H) (Z b).hω (sgnRt_sq b)
  choose h hh _ using fun b => GlobalTheory.T.exists_unique_cmHermitianLatticeForm E H (FU.Di i) (ε b)
  have htw : 2 * (1 - (((Z true).ω : (Z true).M) : ℂ)) - 1 = sgnRt H false := by
    have := (Z true).hω
    simp only [sgnRt, Bool.false_eq_true, if_false, if_true] at this ⊢
    linear_combination -this
  obtain ⟨ε₁, hε₁⟩ := exists_sign (H := H) htw (sgnRt_sq false)
  obtain ⟨h₁, hh₁, -⟩ := GlobalTheory.T.exists_unique_cmHermitianLatticeForm E H (FU.Di i) ε₁
  choose k₁ hk₁ hle hdesc using fun b => exists_desc hU hL FU i hP k₀ (C₀ b) (Z b).C' (c' b) (Z b).u (Z b).theta
    (Z b).c_ne (Z b).lat (Z b).hω (hε b) (hh b) T T' nT mT'
  obtain ⟨k₂, hk₂, hle₂, hdesc₂⟩ := exists_desc hU hL FU i hP k₀ (GlobalTheory.CM.PeriodModel.twist (C₀ true) false)
    (GlobalTheory.CM.PeriodModel.twist (Z true).C' false) (ellMap_twist (c' true) false) (Z true).u (Z true).theta
    (Z true).c_ne (Z true).lat htw hε₁ hh₁ T T' nT mT'

  obtain ⟨K₁, _, e₄, e₄'⟩ : ∃ K₁ : IntermediateField ℚ ℂ, FiniteDimensional ℚ K₁ ∧ (∀ b, k₁ b ≤ K₁) ∧ k₂ ≤ K₁ := by
    have := hk₁ true
    have := hk₁ false
    exact ⟨k₁ true ⊔ k₁ false ⊔ k₂, inferInstance, fun b => by
      cases b
      exacts [le_sup_right.trans le_sup_left, le_sup_left.trans le_sup_left], le_sup_right⟩
  have : NumberField K₁ := ⟨⟩
  have e₅ : k₀ ≤ K₁ := (hle true).trans (e₄ true)
  choose ω₁ C₁ φ₁ ω₂ C₂ φ₁₂ φ₂ φ₃ c₁ c₁₂ c₂ c₃ hφ₃ hφ₂ using fun b =>
    exists_tower hB (e₂ b) e₅ (Z b).C (C₀ b) (c₀ b) (Z b).C' (c' b)
  have hyy : spMap (algebraMap K₁ ℂ) ≫ spMap (IntermediateField.inclusion (e₁.trans e₅)).toRingHom ≫ y₀ = FU.u i P := by
    rw [← Category.assoc, spMap_comp_spMap]; exact hy₀'
  obtain ⟨T₂, m, hg⟩ := exists_pat_univ Xo (spMap (IntermediateField.inclusion (e₁.trans e₅)).toRingHom ≫ y₀)
  obtain ⟨m₂, hm₂⟩ := (Factor.ellMap_cancel_and_sabMap_cancel E H k₀ k₀ K₁ (RingHom.id _)
    (IntermediateField.inclusion e₅).toRingHom).2 _ _ _ _ _ _ mT m (by rw [← Category.assoc, spMap_comp_spMap]; rfl)
  obtain ⟨m₃, hm₃⟩ := (Factor.ellMap_cancel_and_sabMap_cancel E H K₁ K₁ ℂ (RingHom.id _)
    (algebraMap K₁ ℂ)).2 _ _ _ _ _ _ m₂ mT' (by rw [spMap_comp_spMap]; rfl)
  have hnT : m₃.φ ≫ m.φ = nT.φ := by rw [← hm₂, ← Category.assoc, hm₃, hmT']
  choose ψ₂ hψ₂ hex₂ using fun b => hdesc b K₁ e₅ (e₄ b) _ (C₂ b) (φ₂ b) (φ₃ b) T₂ m₂ m₃ _ m (c₂ b) (c₃ b)
    (hφ₃ b) hm₃ hnT
  obtain ⟨ψt, hψt, hext⟩ := hdesc₂ K₁ e₅ e₄' _ (GlobalTheory.CM.PeriodModel.twist (C₂ true) false) (φ₂ true) (φ₃ true) T₂ m₂ m₃ _ m
    (ellMap_twist (c₂ true) false) (ellMap_twist (c₃ true) false) (hφ₃ true) hm₃ hnT
  have hpt : ∀ b (z : Fin (Z b).C'.P.g → ℂ),
      (((Z b).u.ex z).left ≫ φ₃ b) ≫ (C₂ b).P.A.hom = spMap (algebraMap K₁ ℂ) := fun b z => by
    rw [Category.assoc, (c₃ b).2.1.2.1.1.w, ← Category.assoc, Over.w]
    exact Category.id_comp _

  have hΨ : ∀ b, ∃ Ψ : PureType.lat hP (sgnRt H b) → ((C₂ true).P.A ⟶ T₂.t.G), (∀ a, IsMonHom (Ψ a)) ∧
      ∀ a (z : ℂ), (((Z true).u.ex fun _ => (Z true).c * z).left ≫ φ₃ true ≫ (Ψ a).left) ≫ m.φ =
        (FU.ex i P (z • P a)).left := by
    intro b
    cases b
    · exact ⟨ψt, fun a => (hψt.1 a).1, hext⟩
    · exact ⟨ψ₂ true, fun a => ((hψ₂ true).1 a).1, hex₂ true⟩
  choose Ψ hΨm hΨe using hΨ
  have hgT : T₂.g = g := by rw [hg, hg0, (FU.sig i).1, (FU.sig i).2]
  have key : ∀ N : ℕ, N = g → ∃ (bb : Fin N → Bool) (a : ∀ j, PureType.lat hP (sgnRt H (bb j))),
      ∀ z : Fin g → ℂ, ∃ s : Fin N → ℂ, z = ∑ j, s j • P (a j) := by
    rintro N rfl
    exact ⟨bb0, a0, hspan0⟩
  obtain ⟨bb, a, hspan⟩ := key _ hgT
  obtain ⟨B, m', hBg⟩ := GlobalTheory.T.principal_triple_extends_of_curve_homomorphisms hU hL hL₂ hX hK E H (𝓞 K₁) K₁ (algebraMap K₁ ℂ) (C₁ true).P (C₂ true).P
    (φ₁₂ true) T₂ (fun j => Ψ (bb j) (a j)) (c₁₂ true).2.1 (C₁ true).dim (fun j => hΨm (bb j) (a j))
    (ontoAt_of_exp m.cart _ hyy (FU.ex i P) (FU.ex_add i P hP) (FU.ex_onto i P hP) _ hspan _ fun j z =>
      ⟨Over.homMk _ (hpt true fun _ => (Z true).c * z), by
        rw [← hΨe (bb j) (a j) z]
        simp only [Category.assoc]
        exact Category.assoc _ _ _⟩)
  choose ψ hψ hsq' using fun b => GlobalTheory.T.cmFamily_extends_over_dedekindDomain hL hX E H (𝓞 K₁) K₁ _ (C₁ b) (FU.Di i) _ B _ _ (C₂ b) (φ₁₂ b)
    T₂ m' (ψ₂ b) (c₁₂ b) (hψ₂ b)
  have hcF : c.F ≤ K₁ := e₆.trans e₅
  let yK : Sp K₁ ⟶ Xo.XF c := pullback.lift (spMap (IntermediateField.inclusion (e₁.trans e₅)).toRingHom ≫ y₀)
    (spMap (IntermediateField.inclusion hcF).toRingHom) (by
      rw [Category.assoc, hy₀, spMap_comp_spMap, spMap_comp_spMap]; rfl)
  have hyK : under yK = spMap (IntermediateField.inclusion (e₁.trans e₅)).toRingHom ≫ y₀ := pullback.lift_fst _ _ _
  obtain ⟨mK, hmK⟩ : ∃ mK : SABMap T₂.t Xo.univ.t (under yK), mK.φ = m.φ := by
    rw [hyK]; exact ⟨m, rfl⟩
  refine ⟨
    { K := K₁, hc := hcF, hM := fun b => (e₂ b).trans e₅, ω := ω₁, C := C₁, φ := φ₁
      map := c₁
      π := fun b => φ₃ b ≫ φ₁₂ b
      map' := fun b => (EllComp.ellMap_comp E H _ _ (C₁ b) _ _ (C₂ b) _ _ (c₁₂ b)).1 _ _ (Z b).C' _ _ (c₃ b)
      tri := fun b => by
        rw [Category.assoc, hφ₂, ← Category.assoc, hφ₃, hφ]
      ε := ε
      sgn := fun b => by
        have e := congrArg Complex.im (Z b).hω
        have e' : (sgnRt H b).im = 2 * (((Z b).ω : (Z b).M) : ℂ).im := by
          rw [← e]; simp
        rw [e']; nlinarith [hε b]
      h := fun b x y => h b x y
      kform := hh
      B := B
      dim := by rw [hBg, hgT]
      y := yK
      hy := pullback.lift_snd _ _ _
      pt := by rw [hyK]; exact hyy
      t := T₂.t, m := mK, m' := m', ψ := ψ, fam := hψ
      tie := fun b a z x hx hx' => ?_ }, e₃.trans e₅⟩
  rw [hmK, ← hex₂ b a z]
  congr 1
  refine m'.cart.1.hom_ext ?_ ?_
  · refine hx'.trans ?_
    simp only [Category.assoc]
    exact congrArg (fun q => _ ≫ φ₃ b ≫ q) (hsq' b a).symm
  · rw [hx, ← hpt b fun _ => (Z b).c * z]
    simp only [Category.assoc]
    exact congrArg (fun q => _ ≫ φ₃ b ≫ q) (Over.w (ψ₂ b a)).symm

end GlobalTheory.CompanionTheory.Ar.Fl.CMGiven
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPeriodAlgebraicStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmPack_field_ge_of_isPeriod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (n : ℕ) (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k → 0 < n → (∀ y : (FU.Di i).La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) → ∃ X : CMPack Z c FU i hP, k ≤ X.K := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.CMGiven.exists_pack_given | exact GlobalTheory.CompanionTheory.Ar.Fl.CMGiven.exists_pack_given | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.CMGiven.exists_pack_given <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCmPeriodEmbedding
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem exists_cmPoint_locBasis_frames :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (τ : E →+* ℂ) (ℓ : Nat.Primes) (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k → IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → ∃ (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (x : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (hx : IsPure hP x) (X : CMPack Z c FU i hP) (v : Vecs X.y D.p) (w : Vecs X.y D.q), k ≤ X.K ∧ IsLocBasis (𝓞 E) ℓ x ∧ X.IsCMFrame τ hx v w := by
  intro E _ _ _ H D l Xo c g ty FU i Z τ ℓ k hk hty hτ
  obtain ⟨P₀, hP₀⟩ := PeriodNonempty.exists_isPeriod E H (FU.Di i) g ty
    (by rw [(FU.sig i).1, (FU.sig i).2]; exact hty)
  have hsum : D.p + D.q = (FU.Di i).p + (FU.Di i).q := by rw [(FU.sig i).1, (FU.sig i).2]
  obtain ⟨P, hP, x, hloc, hx⟩ := GlobalTheory.T.pure_period_local_basis_exists E H (FU.Di i) g ty P₀ D.p D.q ℓ hP₀ hty hsum
  obtain ⟨hli, n, hn, hspan⟩ := id hloc
  have hn0 : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hn (dvd_zero _))
  obtain ⟨hsplit, -, -⟩ := GlobalTheory.T.pure_family_decomposition E H (FU.Di i) g ty P hP D.p D.q x n hx hspan
  obtain ⟨X, hkX⟩ := GlobalTheory.T.exists_cmPack_field_ge_of_isPeriod E H D l Xo c g ty FU i Z P hP n k hk hn0 hsplit
  obtain ⟨⟨v, w, hvw⟩, -⟩ := GlobalTheory.T.cm_pack_pure_frame E H D l Xo c g ty FU i Z P hP X x hx τ hty hτ hli
  exact ⟨P, hP, x, hx, X, v, w, hkX, hloc, hvw⟩

end GlobalTheory.CompanionTheory.Ar.Fl
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCmPeriodEmbeddingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cm_period_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (τ : E →+* ℂ) (ℓ : Nat.Primes) (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k → IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → ∃ (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (x : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (hx : IsPure hP x) (X : CMPack Z c FU i hP) (v : Vecs X.y D.p) (w : Vecs X.y D.q), k ≤ X.K ∧ IsLocBasis (𝓞 E) ℓ x ∧ X.IsCMFrame τ hx v w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.exists_cmPoint_locBasis_frames | exact GlobalTheory.CompanionTheory.Ar.Fl.exists_cmPoint_locBasis_frames | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.exists_cmPoint_locBasis_frames <;> assumption)
end
