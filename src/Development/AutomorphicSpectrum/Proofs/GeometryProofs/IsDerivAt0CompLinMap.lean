module

public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LamIsoOfDoublingPullbackEqDiagonalSq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModuliConsequenceOfAbelianSchemeLaws
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelFieldPoint
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IdempotentEmbeddingsCard

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsDerivAt0CompLinMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.PerGram

variable {g m : ℕ} {Y : Scheme.{0}}

theorem isDerivAt0_comp_linMap {e : (Fin m → ℂ) → (Sp ℂ ⟶ Y)} (hol : IsHolTo Set.univ e)
    (D : (Fin g → ℂ) →ₗ[ℂ] (Fin m → ℂ)) {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Y}
    (hv : IsDerivAt0 e (D w) v) : IsDerivAt0 (fun z => e (D z)) w v := by
  obtain ⟨h1, h2⟩ := hv
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0
  refine ⟨by show _ = e (D 0); rw [map_zero]; exact h1, fun U h f => ?_⟩
  rw [h2 U h f]
  obtain ⟨hopen, hdiff⟩ := hol U f
  have h0mem : (0 : Fin m → ℂ) ∈ {b | b ∈ Set.univ ∧ ⊤ ≤ (TopologicalSpace.Opens.map (e b).base).obj U} := by
    refine ⟨Set.mem_univ _, ?_⟩
    have hv' : (TopologicalSpace.Opens.map v.base).obj U = ⊤ := top_le_iff.1 h
    rw [← h1]
    simp [hv']
  have hφ : DifferentiableAt ℂ (fun z => valAt' (e z) U f) (D 0) := by
    rw [map_zero]
    exact (hdiff 0 h0mem).differentiableAt (hopen.mem_nhds h0mem)
  have hDd : DifferentiableAt ℂ (⇑(LinearMap.toContinuousLinearMap D)) 0 :=
    (LinearMap.toContinuousLinearMap D).differentiableAt
  have hc := fderiv_comp (0 : Fin g → ℂ) hφ hDd
  have hDf : fderiv ℂ (⇑D) 0 = LinearMap.toContinuousLinearMap D :=
    (LinearMap.toContinuousLinearMap D).fderiv
  rw [show (fun z => valAt' (e (D z)) U f) = (fun z => valAt' (e z) U f) ∘ ⇑D from rfl, hc, hDf]
  simp

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left}

theorem ex_zero_left (u : HolUnif A L g) : (u.ex 0).left = η[A].left := by
  have h := u.ex_add 0 0
  rw [add_zero] at h
  have h1 : u.ex 0 = 1 := by simpa using h
  rw [h1, Hom.one_def]
  simp

theorem isHolTo_ex (u : HolUnif A L g) : IsHolTo Set.univ (fun z => (u.ex z).left) := by
  intro U f
  simpa using u.hol U f

theorem isDerivAt0_of_isDiff (u : HolUnif A L g) {w : Fin g → ℂ} {v : epsR ℂ ⟶ A} (ht : IsTangent v)
    (hd : u.IsDiff w v) : IsDerivAt0 (fun z => (u.ex z).left) w v.left := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.HolUnif.IsDiff at hd
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsTangent at ht
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0
  exact ⟨ht.trans (ex_zero_left u).symm, hd⟩

theorem isDerivAt0_of_fibre {Q : Out.PolAV (Sp ℂ)} {X : Scheme.{0}} (ψ : Q.A.left ⟶ X) {e : (Fin g → ℂ) → (Sp ℂ ⟶ X)}
    (u : HolUnif Q.A Q.L Q.g) (F : (Fin g → ℂ) →ₗ[ℂ] (Fin Q.g → ℂ)) (hF : ∀ z, (u.ex (F z)).left ≫ ψ = e z)
    {w : Fin g → ℂ} {t : epsR ℂ ⟶ Q.A} (ht : IsTangent t) (hd : u.IsDiff (F w) t) :
    IsDerivAt0 e w (t.left ≫ ψ) := by
  have h4 := isDerivAt0_comp_linMap (isHolTo_ex u) F (isDerivAt0_of_isDiff u ht hd)
  have he : e = fun z => (u.ex (F z)).left ≫ ψ := funext fun z => (hF z).symm
  subst he
  obtain ⟨h41, h42⟩ := h4
  have hval : ∀ (y : Sp ℂ ⟶ Q.A.left) (U : X.Opens) (f : ↑(X.presheaf.obj (Opposite.op U))),
      valAt' (y ≫ ψ) U f = valAt' y (ψ ⁻¹ᵁ U) ((ψ.app U).hom f) := by
    intro y U f
    unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt' ReciprocityTheory.ChartRestriction.G.Geo.Tor.valAt
    by_cases hy : ⊤ ≤ (TopologicalSpace.Opens.map y.base).obj (ψ ⁻¹ᵁ U)
    · rw [dite_eq_left hy, dite_eq_left (show ⊤ ≤ (y ≫ ψ) ⁻¹ᵁ U from hy)]
      simp only [Scheme.Hom.comp_appLE, CommRingCat.hom_comp, RingHom.comp_apply]
    · rw [dite_eq_right hy, dite_eq_right (show ¬ ⊤ ≤ (y ≫ ψ) ⁻¹ᵁ U from hy)]
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0
  refine ⟨by rw [← Category.assoc, h41], fun U h f => ?_⟩
  have h' : ⊤ ≤ (TopologicalSpace.Opens.map t.left.base).obj (ψ ⁻¹ᵁ U) := h
  simp only [hval]
  rw [← h42 (ψ ⁻¹ᵁ U) h' ((ψ.app U).hom f)]
  simp only [Scheme.Hom.comp_appLE, CommRingCat.hom_comp, RingHom.comp_apply]

theorem isDiff_map {Q : Out.PolAV (Sp ℂ)} (u u' : HolUnif Q.A Q.L Q.g) (d₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v)
    (G : (Fin Q.g → ℂ) →ₗ[ℂ] (Fin Q.g → ℂ)) (hG : ∀ z, u.ex (G z) = u'.ex z) {w : Fin Q.g → ℂ}
    {t : epsR ℂ ⟶ Q.A} (ht : IsTangent t) (hd : u'.IsDiff w t) : u.IsDiff (G w) t := by
  have h4 := isDerivAt0_of_isDiff u' ht hd
  simp_rw [← hG] at h4
  obtain ⟨v₀, hv₀⟩ := GlobalTheory.VerticalDeriv.exists_isDerivAt0 (isHolTo_ex u) (G w)
  have h1 := isDerivAt0_comp_linMap (isHolTo_ex u) G hv₀
  have heq := GlobalTheory.VerticalDeriv.isDerivAt0_unique h1 h4
  rw [heq] at hv₀
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.HolUnif.IsDiff
  exact hv₀.2

end GlobalTheory.CompanionTheory.Ar.Flat.PerGram

namespace GlobalTheory.CompanionTheory.Ar.Flat


open PerGram in
theorem hodgeGram_iff_period : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) (P : (FU.Di i).La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), IsPeriod (FU.Di i) ty P → Hm.IsHermitian → (∀ x y, (hermForm Hm (P x) (P y)).im = (FU.Di i).EF x y) → ∀ (y : Sp ℂ ⟶ Xo.X), y = FU.u i P → ∀ (m : ℕ) (v : Fin m → (epsAt y ⟶ Xo.univ.t.G)) (W : Fin m → Fin g → ℂ) (Γ : Matrix (Fin m) (Fin m) ℂ), (∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left) (W a) (v a).left) → (IsHodgeGram Xo.univ.t.G Xo.univ.t.PP.L y v Γ ↔ ∀ a b, Γ a b = Real.pi * hermForm Hm (W a) (W b)) := by
  intro E _ _ _ H D l Xo σ g ty FU i P Hm hP _ hIm y hy m v W Γ hd
  subst hy
  have key : ∀ (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ Xo.univ.t.G.left),
      IsGrpPullback Q.A Xo.univ.t.G (FU.u i P) ψ → LBIso Q.L (Xo.univ.t.PP.L.pull ψ) →
      ∃ (u : HolUnif Q.A Q.L Q.g) (H₂ : Matrix (Fin Q.g) (Fin Q.g) ℂ) (χ : u.Λ → ℂ)
        (F : (Fin g → ℂ) ≃ₗ[ℂ] (Fin Q.g → ℂ)), u.IsAH H₂ χ ∧ (∀ t, IsTangent t → ∃! w, u.IsDiff w t) ∧
        (∀ w, ∃! t, IsTangent t ∧ u.IsDiff w t) ∧ (∀ z w, hermForm H₂ (F z) (F w) = hermForm Hm z w) ∧
        ∀ a, ∃ t : epsR ℂ ⟶ Q.A, IsTangent t ∧ u.IsDiff (F (W a)) t ∧ t.left ≫ ψ = (v a).left := by
    intro Q ψ hQ hQL
    obtain ⟨u, H₂, χ, F, hAH, d₁, d₂, -, hF, -, hE⟩ :=
      GlobalTheory.familyUnif_fibre_theta GlobalTheory.thetaUnifAV_all GlobalTheory.abelianSchemeLaws_all.1.weil E H D l Xo σ g ty FU i P hP
        Q ψ hQ hQL
    refine ⟨u, H₂, χ, F, hAH, d₁, d₂, fun z w => ?_, fun a => ?_⟩
    · refine GlobalTheory.KeyFam.SamePeriod.hermForm_eq_of_im H₂ F.toLinearMap Hm LinearMap.id hP.2.2.2.1 ?_ z w
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      exact (hE a b).trans (hIm a b).symm
    · obtain ⟨t, ⟨h₁, h₂⟩, -⟩ := d₂ (F (W a))
      exact ⟨t, h₁, h₂, GlobalTheory.VerticalDeriv.isDerivAt0_unique
        (isDerivAt0_of_fibre ψ u F.toLinearMap hF h₁ h₂) (hd a)⟩
  unfold IsHodgeGram
  constructor
  · rintro ⟨Q, ψ, v', u', Hm', χ', W', hQ, hQL, hAH, hv, hΓ⟩ a b
    obtain ⟨u, H₂, χ, F, hAH₂, d₁, d₂, hH, ht⟩ := key Q ψ hQ hQL.symm
    obtain ⟨G, hG, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo Q.A Q.isAb Q.L Q.g Q.g u d₁ d₂ u'.ex u'.ex_add
      (isHolTo_ex u')
    have hW : ∀ c, G (W' c) = F (W c) := fun c => by
      obtain ⟨t, h₁, h₂, h₃⟩ := ht c
      have e : v' c = t := Over.OverMorphism.ext
        (hQ.1.hom_ext ((hv c).1.trans h₃.symm) (by rw [Over.w, Over.w]))
      have h₄ : u'.IsDiff (W' c) t := e ▸ (hv c).2
      exact (d₁ t h₁).unique (isDiff_map u u' d₂ G hG h₁ h₄) h₂
    rw [hΓ, ← GlobalTheory.UnifCompare.hermForm_eq Q.isLB u' u hAH hAH₂ G hG, hW, hW, hH]
  · intro hΓ
    obtain ⟨Q, ψ, -, hQ, hQL, -⟩ := GlobalTheory.exists_polAV_pullback_of_isLocalRing E H _ Xo.univ.t Xo.univ.proper
      Xo.univ.ample Xo.univ.ktriv ℂ (FU.u i P)
    obtain ⟨u, H₂, χ, F, hAH₂, -, -, hH, ht⟩ := key Q ψ hQ hQL
    choose t h₁ h₂ h₃ using ht
    exact ⟨Q, ψ, t, u, H₂, χ, fun a => F (W a), hQ, hQL.symm, hAH₂, fun a => ⟨h₃ a, h₂ a⟩,
      fun a b => by rw [hΓ, hH]⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.WeilSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.Link

theorem weilSt : Out.WeilSt := GlobalTheory.allSixLaws.1.weil

end GlobalTheory.CompanionTheory.Ar.Link
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexUniformisationHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem complex_uniformisation_holds : N1c := GlobalTheory.closing_of_abelianSchemeLaws

end GlobalTheory.CompanionTheory.Ar.Top
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelLattice
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelLattice
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

theorem triIn_of_frBor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (g : Spec (CommRingCat.of F) ⟶ X) (EC : Type) [AddCommGroup EC] [Module F EC] (MC : LieModel tX.G g EC) (y : FrPt Xo c F), Small.ptY Y y = g ≫ f → ∀ (y' : FrPt Xo c F) (t : Ix Dw → Fˣ), FrBor t y y' → ∀ (τ : E →+* ℂ) (r : ℕ) (hr : r = Dw.mult τ) (u yb : Fin r → EC), (∀ i, (MC.pt (u i)).left ≫ m.φ = Small.tanY Y y τ (Fin.cast hr i)) → (∀ i, (MC.pt (yb i)).left ≫ m.φ = Small.tanY Y y' τ (Fin.cast hr i)) → FinRd.Roots.TriIn u (fun i => (t (some ⟨τ, Fin.cast hr i⟩) : F)) yb := by
  intro E _ _ _ H Dw l Xo c O _ β Y X tX f m F _ _ g EC _ _ MC y hy y' t hb τ r hr u yb hu hyb
  subst hr
  intro i
  obtain ⟨hx, hcomb, -⟩ := hb
  obtain ⟨cf, h1, h2, h3⟩ := hcomb τ i
  refine ⟨cf, h1, h2, ?_⟩
  obtain ⟨hw, hval⟩ := GlobalTheory.T.abelian_map_lie_model_field_point E H Dw l Xo c O β Y X tX f m F g EC MC y hy (Dw.mult τ) (y.u τ)
    (fun j => y.tan τ j) u hu cf (y'.u τ i) h3
  have hF : Small.ptF y' = Small.ptF y := by
    apply Limits.pullback.hom_ext
    · rw [Small.ptF_fst, Small.ptF_fst, hx]
    · rw [Small.ptF_snd, Small.ptF_snd]
  have htan : FinRd.Roots.LieBasis.tanW Y y (y'.u τ i) hw = Small.tanY Y y' τ i := by
    unfold FinRd.Roots.LieBasis.tanW Small.tanY
    congr 1
    apply Small.eq_tanF
    · exact IsPullback.lift_fst _ _ _ _
    · rw [hF]
      exact IsPullback.lift_snd _ _ _ _
  have hleft : (MC.pt (yb i)).left = (MC.pt (∑ j, cf j • u j)).left := by
    apply m.cart.1.hom_ext
    · rw [hval, htan]
      exact hyb i
    · rw [Over.w (MC.pt (yb i)), Over.w (MC.pt (∑ j, cf j • u j))]
  exact MC.inj (Over.OverMorphism.ext hleft)

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelLatticeStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_map_lie_model_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (g : Spec (CommRingCat.of F) ⟶ X) (EC : Type) [AddCommGroup EC] [Module F EC] (MC : LieModel tX.G g EC) (y : FrPt Xo c F), Small.ptY Y y = g ≫ f → ∀ (y' : FrPt Xo c F) (t : Ix Dw → Fˣ), FrBor t y y' → ∀ (τ : E →+* ℂ) (r : ℕ) (hr : r = Dw.mult τ) (u yb : Fin r → EC), (∀ i, (MC.pt (u i)).left ≫ m.φ = Small.tanY Y y τ (Fin.cast hr i)) → (∀ i, (MC.pt (yb i)).left ≫ m.φ = Small.tanY Y y' τ (Fin.cast hr i)) → FinRd.Roots.TriIn u (fun i => (t (some ⟨τ, Fin.cast hr i⟩) : F)) yb := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.triIn_of_frBor | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.triIn_of_frBor | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.triIn_of_frBor <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelEigenFrame
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelEigenFrame
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

open Limits MonoidalCategory CartesianMonoidalCategory MonObj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem tanW_injective (Y : Model Xo c β) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    {w w' : Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left}
    (hw : w ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y.x)
    (hw' : w' ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y.x)
    (h : tanW Y y w hw = tanW Y y w' hw') : w = w' := by
  have a₁ : w ≫ Xo.univ.t.G.hom = (spMap (algebraMap S (DualNumber S)) ≫ Small.ptF y) ≫ pullback.fst _ _ := by
    rw [hw, Category.assoc, Small.ptF_fst]
  have a₂ : w' ≫ Xo.univ.t.G.hom = (spMap (algebraMap S (DualNumber S)) ≫ Small.ptF y) ≫ pullback.fst _ _ := by
    rw [hw', Category.assoc, Small.ptF_fst]
  have e : Y.m0.cart.1.lift w (spMap (algebraMap S (DualNumber S)) ≫ Small.ptF y) a₁ =
      Y.m0.cart.1.lift w' (spMap (algebraMap S (DualNumber S)) ≫ Small.ptF y) a₂ :=
    Y.m.cart.1.hom_ext h (by rw [IsPullback.lift_snd, IsPullback.lift_snd])
  rw [← Y.m0.cart.1.lift_fst w _ a₁, e, IsPullback.lift_fst]

theorem comp_unit {T : Scheme.{0}} {A B M : CategoryTheory.Over T} [GrpObj M] (u : B ⟶ A) : u ≫ (1 : A ⟶ M) = 1 := by
  rw [Hom.one_def, Hom.one_def, ← Category.assoc, toUnit_unique (u ≫ toUnit A) (toUnit B)]

theorem eps_alg {S : Type} [CommRing S] (a : S) :
    spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ spMap (algebraMap S (DualNumber S)) =
      spMap (algebraMap S (DualNumber S)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext b <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem eps_zero {S : Type} [CommRing S] :
    spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (0 : S)) =
      spMap (algebraMap S (DualNumber S)) ≫ spMap (TrivSqZeroExt.fstHom S S S).toRingHom := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext b <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem fst_alg {S : Type} [CommRing S] :
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
  congr 1

theorem isTanAt_one {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) :
    Formalism.L2.Pj.IsTanAt x (1 : tEps x ⟶ Xo.univ.t.G).left := by
  refine ⟨Over.w _, ?_⟩
  let k : Over.mk x ⟶ tEps x := Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
    change _ ≫ _ ≫ x = x
    rw [← Category.assoc, fst_alg, Category.id_comp])
  exact congrArg (fun z => z.left) (comp_unit (M := Xo.univ.t.G) k)

theorem eps_one {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) (a : S) :
    spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a) ≫ (1 : tEps x ⟶ Xo.univ.t.G).left =
      (1 : tEps x ⟶ Xo.univ.t.G).left := by
  let k : tEps x ⟶ tEps x := Over.homMk (spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul a)) (by
    change _ ≫ _ ≫ x = _ ≫ x
    rw [← Category.assoc, eps_alg])
  exact congrArg (fun z => z.left) (comp_unit (M := Xo.univ.t.G) k)

theorem isEigAt_one {S : Type} [CommRing S] [Algebra c.F S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) (τ : E →+* ℂ) :
    Formalism.L2.Pj.IsEigAt c τ (Xo := Xo) (1 : tEps x ⟶ Xo.univ.t.G).left := by
  intro a
  rw [eps_one]
  haveI := Xo.univ.t.act.hom a
  have h : (1 : tEps x ⟶ Xo.univ.t.G) ≫ Xo.univ.t.act.act a = 1 := by
    rw [Hom.one_def, Category.assoc, IsMonHom.one_hom, ← Hom.one_def]
  exact congrArg (fun z => z.left) h

theorem eps_zero_comp {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X)
    (v : Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left) (hv : Formalism.L2.Pj.IsTanAt x v) :
    spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (0 : S)) ≫ v = (1 : tEps x ⟶ Xo.univ.t.G).left := by
  rw [eps_zero, Category.assoc, hv.2]
  let k : tEps x ⟶ Over.mk x := Over.homMk (spMap (algebraMap S (DualNumber S))) rfl
  exact congrArg (fun z => z.left) (comp_unit (M := Xo.univ.t.G) k)

def combPt {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) {n : ℕ}
    (v : Fin n → (Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left))
    (hv : ∀ j, Formalism.L2.Pj.IsTanAt x (v j)) (a : Fin n → S) (i : Fin n) : tEps x ⟶ Xo.univ.t.G :=
  Over.homMk (spMap (ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsMul (a i)) ≫ v i) (by
    change (_ ≫ v i) ≫ _ = _ ≫ x
    rw [Category.assoc, (hv i).1, ← Category.assoc, eps_alg])

theorem exists_comb {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) {n : ℕ}
    (v : Fin n → (Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left))
    (hv : ∀ j, Formalism.L2.Pj.IsTanAt x (v j)) (a : Fin n → S) : ∃ w, IsCombAt x v a w :=
  ⟨_, combPt x v hv a, fun _ => rfl, rfl⟩

theorem comb_zero {S : Type} [CommRing S] (x : Spec (CommRingCat.of S) ⟶ Xo.X) {n : ℕ}
    (v : Fin n → (Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left))
    (hv : ∀ j, Formalism.L2.Pj.IsTanAt x (v j)) :
    IsCombAt x v (0 : Fin n → S) (1 : tEps x ⟶ Xo.univ.t.G).left :=
  ⟨fun _ => 1, fun i => (eps_zero_comp x (v i) (hv i)).symm, by
    simp [List.ofFn_const, List.prod_replicate]⟩

theorem coeff_zero_of_unit {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (τ : E →+* ℂ)
    (a : Fin (Dw.mult τ) → S) (h : IsCombAt y.x (y.u τ) a (1 : tEps y.x ⟶ Xo.univ.t.G).left) : a = 0 :=
  (y.basis τ _ (isTanAt_one y.x) (isEigAt_one y.x τ)).unique h (comb_zero y.x (y.u τ) (y.tan τ))

theorem coeff_zero_of_tanW {S : Type} [CommRing S] [Algebra c.F S] (Y : Model Xo c β) (y : FrPt Xo c S) (τ : E →+* ℂ)
    (a : Fin (Dw.mult τ) → S) {w w₁ : Spec (CommRingCat.of (DualNumber S)) ⟶ Xo.univ.t.G.left}
    (h : IsCombAt y.x (y.u τ) a w) (h₁ : IsCombAt y.x (y.u τ) (0 : Fin (Dw.mult τ) → S) w₁)
    (hw : w ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y.x)
    (hw₁ : w₁ ≫ Xo.univ.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ y.x)
    (e : tanW Y y w hw = tanW Y y w₁ hw₁) : a = 0 := by
  have e₁ : w₁ = (1 : tEps y.x ⟶ Xo.univ.t.G).left := by
    obtain ⟨U, hU, rfl⟩ := h₁
    have : U = fun _ => 1 := by
      funext i
      apply CategoryTheory.Over.OverMorphism.ext
      rw [hU i]
      exact eps_zero_comp y.x (y.u τ i) (y.tan τ i)
    subst this
    simp [List.ofFn_const, List.prod_replicate]
  have := tanW_injective Y y hw hw₁ e
  rw [this, e₁] at h
  exact coeff_zero_of_unit y τ a h

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis

theorem GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.indep_of_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (g : Spec (CommRingCat.of F) ⟶ X) (EC : Type) [AddCommGroup EC] [Module F EC] (MC : LieModel tX.G g EC) (y : FrPt Xo c F), Small.ptY Y y = g ≫ f → ∀ (τ : E →+* ℂ) (r : ℕ) (hr : r = Dw.mult τ) (u : Fin r → EC), (∀ i, (MC.pt (u i)).left ≫ m.φ = Small.tanY Y y τ (Fin.cast hr i)) → LinearIndependent F u := by
  intro E _ _ _ H Dw l Xo c O _ β Y X tX f m F _ _ g EC _ _ MC y hy τ r hr u hu
  subst hr
  rw [Fintype.linearIndependent_iff]
  intro a ha
  have comb := GlobalTheory.T.abelian_map_lie_model_field_point E H Dw l Xo c O β Y X tX f m F g EC MC y hy (Dw.mult τ) (y.u τ) (y.tan τ) u hu
  obtain ⟨w, hc⟩ := FinRd.Roots.LieBasis.exists_comb y.x (y.u τ) (y.tan τ) a
  obtain ⟨w₁, h1⟩ := FinRd.Roots.LieBasis.exists_comb y.x (y.u τ) (y.tan τ) (0 : Fin (Dw.mult τ) → F)
  obtain ⟨hw, ew⟩ := comb a w hc
  obtain ⟨hw1, e1⟩ := comb 0 w₁ h1
  have hz := FinRd.Roots.LieBasis.coeff_zero_of_tanW Y y τ a hc h1 hw hw1 (by
    rw [← ew, ← e1, ha]
    simp)
  intro i
  exact congrFun hz i
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianMapLieModelEigenFrameStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_map_lie_model_eigen_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (X : Scheme.{0}) (tX : SAB H X) (f : X ⟶ Y.X) (m : SABMap tX Y.t f) (F : Type) [Field F] [Algebra c.F F] (g : Spec (CommRingCat.of F) ⟶ X) (EC : Type) [AddCommGroup EC] [Module F EC] (MC : LieModel tX.G g EC) (y : FrPt Xo c F), Small.ptY Y y = g ≫ f → ∀ (τ : E →+* ℂ) (r : ℕ) (hr : r = Dw.mult τ) (u : Fin r → EC), (∀ i, (MC.pt (u i)).left ≫ m.φ = Small.tanY Y y τ (Fin.cast hr i)) → LinearIndependent F u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.indep_of_frame | exact GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.indep_of_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots.LieBasis.indep_of_frame <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqSingleOfIsUnitCoeff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.UU

open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.CompanionTheory.TorusMono

open AddMonoidAlgebra (single)
open GlobalTheory.TorusUnit GlobalTheory.BiextTriv

theorem eq_single_of_isUnit_coeff {A X : Type} [CommRing A] [IsReduced A] [AddCommGroup X]
    [TwoUniqueSums X] {u : AddMonoidAlgebra A X} (hu : IsUnit u) {χ : X}
    (hχ : IsUnit (u.coeff χ)) : u = single χ (u.coeff χ) := by
  classical
  have key : ∀ z, z ≠ χ → u.coeff z = 0 := by
    intro z hz
    have hn : u.coeff z ∈ nilradical A := by
      rw [nilradical_eq_sInf]
      refine Ideal.mem_sInf.2 fun {p} hp => ?_
      have : p.IsPrime := hp
      obtain ⟨a, c, -, e⟩ := Semi.Rosenlicht.isUnit_eq_single
        (hu.map (AddMonoidAlgebra.mapRingHom X (Ideal.Quotient.mk p)))
      have ec : ∀ w, Ideal.Quotient.mk p (u.coeff w) = (single a c : AddMonoidAlgebra (A ⧸ p) X).coeff w := by
        intro w
        rw [← e, AddMonoidAlgebra.coeff_mapRingHom]
      have ha : a = χ := by
        by_contra hne
        have h1 := ec χ
        simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg hne] at h1
        exact (hχ.map (Ideal.Quotient.mk p)).ne_zero h1
      have h2 := ec z
      simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg (ha.trans_ne hz.symm)] at h2
      exact Ideal.Quotient.eq_zero_iff_mem.1 h2
    rw [nilradical_eq_zero] at hn
    exact hn
  ext z
  by_cases h : z = χ
  · subst h; simp
  · simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, key z h, Ne.symm h]

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Y : Over S}

def IsMonoNear (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)) (χ : X) (p : Y.left) : Prop :=
  ∃ (R : CommRingCat.{0}) (y : Spec R ⟶ Y.left), IsOpenImmersion y ∧
    p ∈ Set.range y ∧ ∃ c : R, IsUnit c ∧ (expand y).hom ρ = single χ c

theorem IsMonoNear.residueField {ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)} {χ : X} {p : Y.left}
    (h : IsMonoNear ρ χ p) : ∃ c : Y.left.residueField p, c ≠ 0 ∧
      (expand (Y.left.fromSpecResidueField p)).hom ρ = single χ c := by
  obtain ⟨R, y, hy, hp, c, hc, he⟩ := h
  have H : Set.range (Y.left.fromSpecResidueField p) ⊆ Set.range y := by
    rw [Scheme.range_fromSpecResidueField]; simpa using hp
  obtain ⟨f, hf⟩ : ∃ f, Spec.map f ≫ y = Y.left.fromSpecResidueField p :=
    ⟨Spec.preimage (IsOpenImmersion.lift y _ H), by
      rw [Spec.map_preimage, IsOpenImmersion.lift_fac]⟩
  refine ⟨f.hom c, (hc.map _).ne_zero, ?_⟩
  rw [← hf, expand_map, he]
  simp

theorem IsMonoNear.unique {ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)} {χ χ' : X} {p : Y.left}
    (h : IsMonoNear ρ χ p) (h' : IsMonoNear ρ χ' p) : χ = χ' := by
  classical
  obtain ⟨c, hc, e⟩ := h.residueField
  obtain ⟨c', -, e'⟩ := h'.residueField
  by_contra hne
  have := congrArg (fun f => AddMonoidAlgebra.coeff f χ) (e.symm.trans e')
  simp [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Ne.symm hne] at this
  exact hc this

theorem exists_isMonoNear [Module.Free ℤ X] [IsReduced Y.left]
    (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ) (p : Y.left) : ∃ χ, IsMonoNear ρ.val χ p := by
  have : TwoUniqueSums X := twoUniqueSums_of_free X
  obtain ⟨R, y, hy, q, hq⟩ : ∃ (R : CommRingCat.{0}) (y : Spec R ⟶ Y.left), IsOpenImmersion y ∧
      p ∈ Set.range y :=
    ⟨_, Y.left.affineOpenCover.f (Y.left.affineOpenCover.idx p), inferInstance,
      Y.left.affineOpenCover.covers p⟩
  obtain ⟨χ, hχ⟩ := exists_coeff_notMem (ρ.isUnit.map (expand y).hom) q.asIdeal q.2.ne_top
  set a := ((expand y).hom ρ.val).coeff χ with ha
  let g : R ⟶ CommRingCat.of (Localization.Away a) :=
    CommRingCat.ofHom (algebraMap R (Localization.Away a))
  have hopen : IsOpenImmersion (Spec.map g ≫ y) := inferInstance
  have hred : IsReduced (Spec (CommRingCat.of (Localization.Away a))) :=
    isReduced_of_isOpenImmersion (Spec.map g ≫ y)
  have hred' : _root_.IsReduced (Localization.Away a) :=
    (affine_isReduced_iff (CommRingCat.of (Localization.Away a))).1 hred
  have hcoeff : ((expand (Spec.map g ≫ y)).hom ρ.val).coeff χ = algebraMap R (Localization.Away a) a := by
    rw [expand_map, AddMonoidAlgebra.coeff_mapRingHom]
    rfl
  have hunit : IsUnit (((expand (Spec.map g ≫ y)).hom ρ.val).coeff χ) := by
    rw [hcoeff]
    exact IsLocalization.Away.algebraMap_isUnit a
  refine ⟨χ, _, Spec.map g ≫ y, hopen, ?_, _, hunit,
    eq_single_of_isUnit_coeff (ρ.isUnit.map (expand _).hom) hunit⟩
  have := PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
  obtain ⟨r, hr⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap R (Localization.Away a))) := by
    rw [this]; exact hχ
  refine ⟨r, ?_⟩
  rw [← hq, ← hr]
  exact Scheme.Hom.comp_apply _ _ _

theorem snd_expand {R : CommRingCat.{0}} (y : Spec R ⟶ Y.left) :
    (snd (splitTorus S X) Y).left.appTop ≫ expand y =
      y.appTop ≫ (Scheme.ΓSpecIso R).hom ≫ const X R := by
  rw [expand, value, ← Scheme.Hom.comp_appTop_assoc, prodPoint_snd, Scheme.Hom.comp_appTop,
    Category.assoc, Scheme.ΓSpecIso_naturality]

theorem eq_char_mul [Module.Free ℤ X] [ConnectedSpace Y.left] [IsReduced Y.left]
    (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ) :
    ∃ χ : X, ρ.val = (fst (splitTorus S X) Y).left.appTop.hom (charUnit S X χ).val *
      (snd (splitTorus S X) Y).left.appTop.hom ((unitSec X Y).appTop.hom ρ.val) := by
  choose c hc using exists_isMonoNear (X := X) (Y := Y) ρ
  have hlc : IsLocallyConstant c := by
    rw [IsLocallyConstant.iff_exists_open]
    intro p
    obtain ⟨R, y, hy, hp, he⟩ := hc p
    exact ⟨Set.range y, y.isOpenEmbedding.isOpen_range, hp,
      fun p' hp' => (hc p').unique ⟨R, y, hy, hp', he⟩⟩
  obtain ⟨p₀⟩ : Nonempty Y.left := inferInstance
  refine ⟨c p₀, ext_of_expand fun p => ?_⟩
  obtain ⟨R, y, hy, hp, d, -, he⟩ := hc p
  refine ⟨R, y, hy, hp, ?_⟩
  have e1 := congrArg (fun f => f.hom ρ.val) (expand_aug (X := X) y)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e1
  rw [he, aug_single] at e1
  have e2 := congrArg (fun f => f.hom ((unitSec X Y).appTop.hom ρ.val)) (snd_expand (X := X) y)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e2
  rw [map_mul, e2, ← e1, expand_char, he, hlc.apply_eq_of_preconnectedSpace p p₀]
  simp [const, AddMonoidAlgebra.single_mul_single]

end GlobalTheory.CompanionTheory.TorusMono


open GlobalTheory.CompanionTheory.TorusMono GlobalTheory.BiextTriv in
theorem GlobalTheory.CompanionTheory.TorusMono.torus_unit_eq_char_mul : ∀ (S : Scheme.{0}) (X : Type) [AddCommGroup X] [Module.Free ℤ X] (Y : Over S) [ConnectedSpace Y.left] [IsReduced Y.left] (ρ : Γ((splitTorus S X ⊗ Y).left, ⊤)ˣ), ∃ χ : X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ Y), (lift t y).left.appTop.hom ρ.val = (chV t χ).val * (lift (1 : Z ⟶ splitTorus S X) y).left.appTop.hom ρ.val := by
  intro S X _ _ Y _ _ ρ
  obtain ⟨χ, hχ⟩ := eq_char_mul ρ
  refine ⟨χ, fun Z t y => ?_⟩
  have c1 : ∀ v, (lift t y).left.appTop.hom ((fst (splitTorus S X) Y).left.appTop.hom v) =
      t.left.appTop.hom v := fun v => by
    have e : (lift t y).left ≫ (fst (splitTorus S X) Y).left = t.left := by
      rw [← Over.comp_left, lift_fst]
    rw [← e, Scheme.Hom.comp_appTop]
    rfl
  have c2 : ∀ v, (lift t y).left.appTop.hom ((snd (splitTorus S X) Y).left.appTop.hom v) =
      y.left.appTop.hom v := fun v => by
    have e : (lift t y).left ≫ (snd (splitTorus S X) Y).left = y.left := by
      rw [← Over.comp_left, lift_snd]
    rw [← e, Scheme.Hom.comp_appTop]
    rfl
  have c3 : y.left.appTop.hom ((unitSec X Y).appTop.hom ρ.val) =
      (lift (1 : Z ⟶ splitTorus S X) y).left.appTop.hom ρ.val := by
    rw [← comp_unitSec, Scheme.Hom.comp_appTop]
    rfl
  conv_lhs => rw [hχ]
  rw [map_mul, c1, c2, c3, chV_val]
end
end
