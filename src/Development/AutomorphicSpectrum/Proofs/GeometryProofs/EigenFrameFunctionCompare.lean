module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrameAtComponentPoint
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsHolomorphicChartAtPoint
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartFrameGrowth
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsBdryChartOfHol
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordDegreeBoundOfFlag

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AffineChartBundleSections
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicAffinePolydiscChart
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicAffinePolydiscChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem hol_polydisc_chart : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (d : ℕ) (T : Set X), SmoothOfRelativeDimension d s → Geo.ResK.HasSncCoords s d T → ∀ (x : Sp ℂ ⟶ X) (W : X.Opens), x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → ∃ (V : X.Opens) (hV : IsAffineOpen V) (a : ℕ) (ψ : (Fin d → ℂ) → (Γ(X, V) →+* ℂ)), V ≤ W ∧ a ≤ d ∧ IsHolPts (ball 0 1) ψ ∧ spMap (ψ 0) ≫ hV.fromSpec = x ∧ Set.InjOn ψ (ball 0 1) ∧ (∀ z ∈ ball (0 : Fin d → ℂ) 1, spMap (ψ z) ≫ hV.fromSpec ≫ s = spMap σ ∧ (centre (spMap (ψ z) ≫ hV.fromSpec) ∉ T ↔ z ∈ punct d a 1)) ∧ ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsHolTo B y → (∀ b ∈ B, y b ≫ s = spMap σ) → ∀ b₀ ∈ B, y b₀ = x → ∃ (ε : ℝ) (κ : (Fin m → ℂ) → (Fin d → ℂ)), 0 < ε ∧ ball b₀ ε ⊆ B ∧ DifferentiableOn ℂ κ (ball b₀ ε) ∧ κ b₀ = 0 ∧ ∀ b ∈ ball b₀ ε, κ b ∈ ball (0 : Fin d → ℂ) 1 ∧ y b = spMap (ψ (κ b)) ≫ hV.fromSpec :=
  @PositivityTheory.Xgn.exists_holomorphic_chart_at_point

end GlobalTheory.CompanionTheory.Ar.Flat
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicAffinePolydiscChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_affine_polydisc_chart : ∀ (K : Type) [Field K] (σ : K →+* ℂ) (X : Scheme.{0}) (s : X ⟶ Sp K) (d : ℕ) (T : Set X), SmoothOfRelativeDimension d s → Geo.ResK.HasSncCoords s d T → ∀ (x : Sp ℂ ⟶ X) (W : X.Opens), x ≫ s = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → ∃ (V : X.Opens) (hV : IsAffineOpen V) (a : ℕ) (ψ : (Fin d → ℂ) → (Γ(X, V) →+* ℂ)), V ≤ W ∧ a ≤ d ∧ IsHolPts (ball 0 1) ψ ∧ spMap (ψ 0) ≫ hV.fromSpec = x ∧ Set.InjOn ψ (ball 0 1) ∧ (∀ z ∈ ball (0 : Fin d → ℂ) 1, spMap (ψ z) ≫ hV.fromSpec ≫ s = spMap σ ∧ (centre (spMap (ψ z) ≫ hV.fromSpec) ∉ T ↔ z ∈ punct d a 1)) ∧ ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsHolTo B y → (∀ b ∈ B, y b ≫ s = spMap σ) → ∀ b₀ ∈ B, y b₀ = x → ∃ (ε : ℝ) (κ : (Fin m → ℂ) → (Fin d → ℂ)), 0 < ε ∧ ball b₀ ε ⊆ B ∧ DifferentiableOn ℂ κ (ball b₀ ε) ∧ κ b₀ = 0 ∧ ∀ b ∈ ball b₀ ε, κ b ∈ ball (0 : Fin d → ℂ) 1 ∧ y b = spMap (ψ (κ b)) ≫ hV.fromSpec := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.hol_polydisc_chart | exact GlobalTheory.CompanionTheory.Ar.Flat.hol_polydisc_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.hol_polydisc_chart <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AffineChartBundleSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open GlobalTheory.CompanionTheory.Ar.Flat.BdryModel

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.ChartFamily

theorem exists_tied_chart {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
    (Xo : Moduli D l) (σ : KA l →+* ℂ) (Z : Scheme.{0}) (T : SAB H Z) (U₀ : Scheme.{0}) (j₀ : U₀ ⟶ Z) (k₀ : U₀ ⟶ Xo.X)
    (To : SAB H U₀) (n a : ℕ) (y : (Fin n → ℂ) → (Sp ℂ ⟶ Z)) (han : a ≤ n) (hj : IsOpenImmersion j₀)
    (n₁ : SABMap To T j₀) (n₂ : SABMap To Xo.univ.t k₀) (hy : IsHolTo (Metric.ball 0 1) y)
    (hp : ∀ z ∈ punct n a 1, ∃ p : Sp ℂ ⟶ U₀, p ≫ j₀ = y z ∧ p ≫ k₀ ≫ Xo.s = spMap σ) :
    ∃ (ρ : ℝ) (C : BdryChart Xo σ n a) (i : Sp C.R ⟶ Z) (e : C.V ⟶ U₀) (mi : SABMap C.t T i) (me : SABMap C.tV To e),
      0 < ρ ∧ ρ ≤ 1 ∧ e ≫ j₀ = C.j ≫ i ∧ e ≫ k₀ = C.k ∧
      (∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (C.ψ z) ≫ i = y ((ρ : ℂ) • z)) ∧
      C.m₂.φ = me.φ ≫ n₂.φ ∧ C.m₁.φ ≫ mi.φ = me.φ ≫ n₁.φ := by
  classical
  have := T.semi.smooth
  obtain ⟨U, hU, hx, -, n', v₀, hv₀⟩ := GlobalTheory.exists_affine_lieBasis_baseChange Z T.G
    (y 0 (default : PrimeSpectrum ℂ)) ⊤ trivial
  have h0 : ⊤ ≤ y 0 ⁻¹ᵁ U := fun p _ => by
    have : p = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [this]; exact hx
  obtain ⟨ρ₀, hρ₀, hB₀⟩ := Metric.isOpen_iff.1 (hy U 0).1 0 ⟨Metric.mem_ball_self one_pos, h0⟩
  obtain ⟨ρ, hρ, hρ1, hB⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      Metric.ball (0 : Fin n → ℂ) ρ ⊆ {b ∈ Metric.ball 0 1 | ⊤ ≤ y b ⁻¹ᵁ U} :=
    ⟨min ρ₀ 1, lt_min hρ₀ one_pos, min_le_right _ _, (Metric.ball_subset_ball (min_le_left _ _)).trans hB₀⟩
  have hin : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, (ρ : ℂ) • z ∈ Metric.ball (0 : Fin n → ℂ) ρ := fun z hz => by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    exact mul_lt_of_lt_one_right hρ hz
  obtain ⟨t, ⟨m⟩⟩ := exists_sab hU.fromSpec T
  have hdim : SmoothOfRelativeDimension n' t.G.hom := HolChart.smoothDim_of_fibres t n' fun κ _ f t₀ m₀ => by
    obtain ⟨q, -⟩ := GlobalTheory.ObjMaps.exists_sab_comp m m₀
    obtain ⟨v', -, hv'⟩ := hv₀ κ f t₀.G _ q.cart
    exact ⟨v', hv'⟩
  obtain ⟨v', -, hv'⟩ := hv₀ Γ(Z, U) (RingHom.id _) t.G m.cm.F (by
    have : spMap (RingHom.id Γ(Z, U)) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp]; exact m.cart)
  obtain ⟨M⟩ := lieModel_of_isLieBasis v' hv'
  let ψ : (Fin n → ℂ) → (Γ(Z, U) →+* ℂ) := fun z =>
    if h : ⊤ ≤ y ((ρ : ℂ) • z) ⁻¹ᵁ U then evalHom _ U h else evalHom _ U h0
  have hψ : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) 1, spMap (ψ z) ≫ hU.fromSpec = y ((ρ : ℂ) • z) := fun z hz => by
    simp only [ψ, dif_pos (hB (hin z hz)).2]
    exact spMap_evalHom _ _ _ _
  obtain ⟨tV, ⟨q⟩⟩ := exists_sab (pullback.snd hU.fromSpec j₀) To
  obtain ⟨m₂, e₂⟩ := GlobalTheory.ObjMaps.exists_sab_comp n₂ q
  obtain ⟨q₁, e₁⟩ : ∃ q₁ : SABMap tV T (pullback.fst hU.fromSpec j₀ ≫ hU.fromSpec), q₁.φ = q.φ ≫ n₁.φ := by
    rw [pullback.condition]
    exact GlobalTheory.ObjMaps.exists_sab_comp n₁ q
  obtain ⟨m₁, e₃⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m q₁
  have hpt : ∀ z ∈ punct n a 1, ∃ p : Sp ℂ ⟶ pullback hU.fromSpec j₀,
      p ≫ pullback.fst _ _ = spMap (ψ z) ∧ p ≫ (pullback.snd _ _ ≫ k₀) ≫ Xo.s = spMap σ := fun z hz => by
    obtain ⟨p, hp₁, hp₂⟩ := hp ((ρ : ℂ) • z) ⟨(hB (hin z hz.1)).1, fun i hi => by
      simpa using ⟨hρ.ne', hz.2 i hi⟩⟩
    refine ⟨pullback.lift (spMap (ψ z)) p ((hψ z hz.1).trans hp₁.symm), pullback.lift_fst _ _ _, ?_⟩
    rw [Category.assoc, pullback.lift_snd_assoc, hp₂]
  obtain ⟨p₀, -⟩ := hpt _ (half_mem_punct n a)
  have : Nonempty (Sp ℂ ⟶ pullback hU.fromSpec j₀) := ⟨p₀⟩
  choose! pt hpt using hpt
  refine ⟨ρ, { a_le := han, R := Γ(Z, U), t := t, g := n', dim := hdim
               M := M, ψ := ψ, hol := ⟨Metric.isOpen_ball, fun r => ?_⟩
               V := pullback hU.fromSpec j₀, j := pullback.fst _ _, j_open := inferInstance
               k := pullback.snd _ _ ≫ k₀, tV := tV, m₁ := m₁, m₂ := m₂, pt := pt, pt_eq := hpt },
    hU.fromSpec, pullback.snd _ _, m, q, hρ, hρ1, pullback.condition.symm, rfl, hψ, e₂, e₃.symm.trans e₁⟩
  refine (((hy U r).2.comp (f := fun z => (ρ : ℂ) • z) (by fun_prop) (fun z hz => hB (hin z hz)))).congr
    fun z hz => ?_
  simp only [ψ, Function.comp, valAt', dif_pos (hB (hin z hz)).2]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f :=
  Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)

theorem exists_lift_of_centre_mem {X : Scheme.{0}} (W : X.Opens) (w : Sp ℂ ⟶ X) (h : centre w ∈ W) :
    ∃ w' : Sp ℂ ⟶ W.toScheme, w' ≫ W.ι = w := by
  have hr : Set.range w ⊆ Set.range W.ι := by
    rintro _ ⟨p, rfl⟩
    have e : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [Scheme.Opens.range_ι, e]
    exact h
  exact ⟨IsOpenImmersion.lift W.ι w hr, IsOpenImmersion.lift_fac _ _ _⟩

theorem exists_model_chart (Y : Model Xo c β) (σ : c.F →+* ℂ) {X' : Scheme.{0}} (π : X' ⟶ Y.X) (s' : X' ⟶ Sp c.F)
    (d : ℕ) (W' : X'.Opens) (jW : W'.toScheme ⟶ Xo.XF c) (h1 : jW ≫ Y.j = W'.ι ≫ π)
    (h2 : jW ≫ pullback.snd _ _ = W'.ι ≫ s') (V : X'.Opens) (hV : IsAffineOpen V) (a : ℕ)
    (ψ : (Fin d → ℂ) → (Γ(X', V) →+* ℂ)) (ha : a ≤ d) (hol : IsHolPts (ball 0 1) ψ)
    (hpt : ∀ z ∈ punct d a 1, spMap (ψ z) ≫ hV.fromSpec ≫ s' = spMap σ ∧ centre (spMap (ψ z) ≫ hV.fromSpec) ∈ W') :
    ∃ (ρ : ℝ) (C : BdryChart Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) d a)
      (i₀ : Sp C.R ⟶ Sp Γ(X', V)) (mR : SABMap C.t Y.t (i₀ ≫ hV.fromSpec ≫ π)) (k' : C.V ⟶ Xo.XF c)
      (φ₀ : C.tV.G.left ⟶ Y.oF.t.G.left), 0 < ρ ∧ ρ ≤ 1 ∧
      (∀ z ∈ ball (0 : Fin d → ℂ) 1, spMap (C.ψ z) ≫ i₀ = spMap (ψ ((ρ : ℂ) • z))) ∧
      k' ≫ pullback.fst _ _ = C.k ∧ k' ≫ Y.j = C.j ≫ i₀ ≫ hV.fromSpec ≫ π ∧
      k' ≫ pullback.snd _ _ = C.j ≫ i₀ ≫ hV.fromSpec ≫ s' ∧ φ₀ ≫ Y.oF.t.G.hom = C.tV.G.hom ≫ k' ∧
      φ₀ ≫ Y.m0.toSABMap.φ = C.m₂.φ ∧ φ₀ ≫ Y.m.φ = C.m₁.φ ≫ mR.φ := by
  obtain ⟨T, ⟨m⟩⟩ := exists_sab (hV.fromSpec ≫ π) Y.t
  let U₀ := pullback hV.fromSpec W'.ι
  let j₀ : U₀ ⟶ Sp Γ(X', V) := pullback.fst _ _
  let g₀ : U₀ ⟶ Xo.XF c := pullback.snd hV.fromSpec W'.ι ≫ jW
  have hcond : j₀ ≫ hV.fromSpec = pullback.snd hV.fromSpec W'.ι ≫ W'.ι := pullback.condition
  obtain ⟨tU, ⟨n₃⟩⟩ := exists_sab g₀ Y.oF.t
  obtain ⟨n₂, e₂⟩ := GlobalTheory.ObjMaps.exists_sab_comp Y.m0.toSABMap n₃
  have hj : g₀ ≫ Y.jQ ≫ pullback.fst _ _ = j₀ ≫ hV.fromSpec ≫ π := by
    have : g₀ ≫ Y.j = j₀ ≫ hV.fromSpec ≫ π := by
      simp only [g₀, Category.assoc, h1]
      rw [← Category.assoc j₀, hcond, Category.assoc]
    exact this
  obtain ⟨q₁, eq₁⟩ : ∃ q₁ : SABMap tU Y.t (j₀ ≫ hV.fromSpec ≫ π), q₁.φ = n₃.φ ≫ Y.m.φ := by
    rw [← hj]
    exact GlobalTheory.ObjMaps.exists_sab_comp Y.m n₃
  obtain ⟨n₁, e₁⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m q₁
  have hp : ∀ z ∈ punct d a 1, ∃ p : Sp ℂ ⟶ U₀, p ≫ j₀ = spMap (ψ z) ∧
      p ≫ (g₀ ≫ pullback.fst _ _) ≫ Xo.s = spMap (σ.comp (IntermediateField.inclusion c.le).toRingHom) := by
    intro z hz
    obtain ⟨w', hw'⟩ := exists_lift_of_centre_mem W' _ (hpt z hz).2
    refine ⟨pullback.lift (spMap (ψ z)) w' hw'.symm, pullback.lift_fst _ _ _, ?_⟩
    have e : (pullback.lift (spMap (ψ z)) w' hw'.symm : Sp ℂ ⟶ U₀) ≫ g₀ = w' ≫ jW := by
      simp only [g₀]
      rw [← Category.assoc, pullback.lift_snd]
    have ec : pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) ≫ Xo.s =
        pullback.snd _ _ ≫ spMap (IntermediateField.inclusion c.le).toRingHom := pullback.condition
    calc _ = ((pullback.lift (spMap (ψ z)) w' hw'.symm : Sp ℂ ⟶ U₀) ≫ g₀) ≫ pullback.fst _ _ ≫ Xo.s := by
            simp only [Category.assoc]
      _ = (w' ≫ jW) ≫ pullback.snd _ _ ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by rw [e, ec]
      _ = w' ≫ (jW ≫ pullback.snd _ _) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
            simp only [Category.assoc]
      _ = (w' ≫ W'.ι) ≫ s' ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
            rw [h2]; simp only [Category.assoc]
      _ = _ := by
            rw [hw', spMap_comp', ← (hpt z hz).1]; simp only [Category.assoc]
  obtain ⟨ρ, C, i₀, e, mi, me, hρ, hρ1, hej, hek, hψ, hm₂, hm₁⟩ := exists_tied_chart Xo _ _ T U₀ j₀
    (g₀ ≫ pullback.fst _ _) tU d a (fun z => spMap (ψ z)) ha inferInstance n₁ n₂
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_spMap hol.1 hol.2) hp
  obtain ⟨mR, eR⟩ := GlobalTheory.ObjMaps.exists_sab_comp m mi
  refine ⟨ρ, C, i₀, mR, e ≫ g₀, me.φ ≫ n₃.φ, hρ, hρ1, hψ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Category.assoc]; exact hek
  · have w2 : g₀ ≫ Y.j = j₀ ≫ hV.fromSpec ≫ π := hj
    rw [Category.assoc, w2, ← Category.assoc, hej]
    simp only [Category.assoc]
  · have w2 : g₀ ≫ pullback.snd _ _ = j₀ ≫ hV.fromSpec ≫ s' := by
      simp only [g₀, Category.assoc, h2]
      rw [← Category.assoc j₀, hcond, Category.assoc]
    rw [Category.assoc, w2, ← Category.assoc, hej]
    simp only [Category.assoc]
  · have w3 : n₃.φ ≫ Y.oF.t.G.hom = tU.G.hom ≫ g₀ := n₃.cart.1.w
    have w4 : me.φ ≫ tU.G.hom = C.tV.G.hom ≫ e := me.cart.1.w
    rw [Category.assoc, w3, ← Category.assoc, w4, Category.assoc]
  · rw [hm₂, e₂, Category.assoc]
  · have e5 : C.m₁.φ ≫ mR.φ = me.φ ≫ n₁.φ ≫ m.φ := by rw [eR, ← Category.assoc, hm₁, Category.assoc]
    rw [e5, ← e₁, eq₁, Category.assoc]

theorem exists_coord {S : Scheme.{0}} {A R L : Type} [CommRing A] [CommRing R] [AddCommGroup L] [Module R L]
    {G : Over S} [GrpObj G] {G' : Over (Sp R)} [GrpObj G'] (xA : Sp A ⟶ S) (fR : A →+* R) (f : Sp R ⟶ S)
    (hf : spMap fR ≫ xA = f) (φ : G'.left ⟶ G.left) (h : IsGrpPullback G' G f φ) (M : LieModel G' (𝟙 (Sp R)) L)
    (v : epsAt xA ⟶ G) (hv : IsTanAt G xA v) :
    ∃ u : L, (M.pt u).left ≫ φ = spMap (dualMap fR) ≫ v.left := by
  have hx : Spec.map (CommRingCat.ofHom fR) ≫ xA = 𝟙 _ ≫ f := by rw [Category.id_comp]; exact hf
  have t := LiePull.tan_pull fR xA _ hx v hv
  obtain ⟨u, hu⟩ := M.onto (LieMove.liftEps h (LieCarrier.epsHom fR xA _ hx ≫ v))
    ((LieMove.tan_iff h _).2 (by rw [LieMove.push_lift]; exact t))
  exact ⟨u, by rw [hu, LieMove.liftEps_left]; rfl⟩

theorem indep_of_frame {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (hs : Smooth G.hom) {R : Type}
    [CommRing R] (ψ : R →+* ℂ) (xR : Sp R ⟶ S) (y : Sp ℂ ⟶ S) (hy : spMap ψ ≫ xR = y) {g n : ℕ}
    (M : LieModel G xR (Fin g → R)) (u : Fin n → Fin g → R) {O : Type} [CommRing O] (act : OAct O G) (τ : O →+* ℂ)
    (v : Fin n → (epsAt y ⟶ G)) (hv : IsEigFrame act y τ v)
    (hu : ∀ i, (v i).left = spMap (dualMap ψ) ≫ (M.pt (u i)).left) :
    LinearIndependent ℂ (fun i b => ψ (u i b)) := by
  classical
  subst hy
  letI := ψ.toAlgebra
  obtain ⟨E', i1, i2, ⟨M'⟩⟩ := GlobalTheory.T.exists_lie_model S G ℂ (spMap ψ ≫ xR)
  obtain ⟨j, hj, hlin, hb⟩ := GlobalTheory.T.lie_model_base_change_map S G R ℂ xR (Fin g → R) E' M M'
  have hv' : v = fun i => M'.pt (j (u i)) :=
    funext fun i => Over.OverMorphism.ext ((hu i).trans (hj _).symm)
  have hcomb := (GlobalTheory.T.lie_model_eigenvectors_action S ℂ G _ E' M').1
  have hind : LinearIndependent ℂ (fun i => j (u i)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have c1 : IsComb (Pi.single i 1) v (v i) := by
      rw [hv']
      exact (hcomb _ _ _ _).2 (by simp [Pi.single_apply])
    have c2 : IsComb (Pi.single i 1 + c) v (v i) := by
      rw [hv']
      exact (hcomb _ _ _ _).2 (by simp [Pi.single_apply, add_smul, Finset.sum_add_distrib, hc])
    obtain ⟨c0, -, hun⟩ := (hv.2 (v i) (hv.1 i))
    have e := congrFun ((hun _ c1).trans (hun _ c2).symm) i
    simpa using e
  have hbas := (hb hs g (Pi.basisFun R (Fin g))).1
  let L : (Fin g → ℂ) →ₗ[ℂ] E' := Fintype.linearCombination ℂ (fun k => j (Pi.basisFun R (Fin g) k))
  have hL : ∀ x : Fin g → R, L (fun k => ψ (x k)) = j x := by
    intro x
    have ex : x = ∑ k, x k • Pi.basisFun R (Fin g) k := ((Pi.basisFun R (Fin g)).sum_repr x).symm
    set_option synthInstance.maxHeartbeats 100000 in
      conv_rhs => rw [ex, map_sum]
    simp only [L, Fintype.linearCombination_apply, hlin]
    rfl
  refine LinearIndependent.of_comp L ?_
  have : L ∘ (fun i b => ψ (u i b)) = fun i => j (u i) := funext fun i => hL (u i)
  rw [this]
  exact hind

theorem exists_vec (Y : Model Xo c β) {σ' : KA l →+* ℂ} {n a : ℕ} (C : BdryChart Xo σ' n a) (k' : C.V ⟶ Xo.XF c)
    (φ₀ : C.tV.G.left ⟶ Y.oF.t.G.left) {f : Sp C.R ⟶ Y.X} (mR : SABMap C.t Y.t f)
    (hk : k' ≫ pullback.fst _ _ = C.k) (h₁ : φ₀ ≫ Y.oF.t.G.hom = C.tV.G.hom ≫ k')
    (h₂ : φ₀ ≫ Y.m0.toSABMap.φ = C.m₂.φ) (h₃ : φ₀ ≫ Y.m.φ = C.m₁.φ ≫ mR.φ)
    (p : Sp ℂ ⟶ C.V) (ψz : C.R →+* ℂ) (hp : p ≫ C.j = spMap ψz) (u : Fin C.g → C.R) :
    ∃ (v : epsAt (under (p ≫ k')) ⟶ Xo.univ.t.G) (v₀ : epsAt ((p ≫ k') ≫ Y.j) ⟶ Y.t.G)
      (uu : Sp (DualNumber ℂ) ⟶ C.tV.G.left), SameVec Y (p ≫ k') v v₀ ∧ uu ≫ C.m₂.φ = v.left ∧
      uu ≫ C.m₁.φ = spMap (dualMap ψz) ≫ (C.M.pt u).left ∧
      v₀.left = spMap (dualMap ψz) ≫ (C.M.pt u).left ≫ mR.φ := by
  have hq : IsPullback C.m₁.φ C.tV.G.hom C.t.G.hom C.j := C.m₁.cart.1
  have hsq : spMap (dualMap ψz) ≫ spMap (algebraMap C.R (DualNumber C.R)) =
      spMap (algebraMap ℂ (DualNumber ℂ)) ≫ spMap ψz := by
    rw [← spMap_comp', ← spMap_comp']
    congr 1
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  have w : (spMap (dualMap ψz) ≫ (C.M.pt u).left) ≫ C.t.G.hom =
      (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p) ≫ C.j := by
    have w₀ : (C.M.pt u).left ≫ C.t.G.hom = spMap (algebraMap C.R (DualNumber C.R)) ≫ 𝟙 _ := Over.w (C.M.pt u)
    rw [Category.assoc, w₀, Category.comp_id, hsq, Category.assoc, hp]
  have l₁ : hq.lift _ _ w ≫ C.m₁.φ = _ := hq.lift_fst _ _ w
  have l₂ : hq.lift _ _ w ≫ C.tV.G.hom = _ := hq.lift_snd _ _ w
  have w₂ : C.m₂.φ ≫ Xo.univ.t.G.hom = C.tV.G.hom ≫ C.k := C.m₂.cart.1.w
  have hu₁ : (hq.lift _ _ w ≫ φ₀) ≫ Y.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ p ≫ k' := by
    rw [Category.assoc, h₁, ← Category.assoc, l₂]
    simp only [Category.assoc]
  refine ⟨Over.homMk (hq.lift _ _ w ≫ C.m₂.φ) ?_, Over.homMk (hq.lift _ _ w ≫ φ₀ ≫ Y.m.φ) ?_, hq.lift _ _ w,
    ⟨hq.lift _ _ w ≫ φ₀, hu₁, ?_, ?_⟩, rfl, l₁, ?_⟩
  · show (hq.lift _ _ w ≫ C.m₂.φ) ≫ Xo.univ.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (p ≫ k') ≫ pullback.fst _ _
    rw [Category.assoc, w₂, ← Category.assoc, l₂, ← hk]
    simp only [Category.assoc]
  · have w₃ : Y.m.φ ≫ Y.t.G.hom = Y.oF.t.G.hom ≫ Y.j := Y.m.cart.1.w
    show (hq.lift _ _ w ≫ φ₀ ≫ Y.m.φ) ≫ Y.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ (p ≫ k') ≫ Y.j
    simp only [Category.assoc]
    rw [w₃, ← Category.assoc φ₀, h₁, ← Category.assoc, ← Category.assoc, l₂]
    simp only [Category.assoc]
  · rw [Category.assoc, h₂]; rfl
  · rw [Category.assoc]; rfl
  · show hq.lift _ _ w ≫ φ₀ ≫ Y.m.φ = _
    rw [h₃, ← Category.assoc, l₁, Category.assoc]

theorem spMap_dual {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (dualMap (g.comp f)) = spMap (dualMap g) ≫ spMap (dualMap f) := by
  rw [← LiePull.dualMap_comp, spMap_comp']

theorem chart_unit (Y : Model Xo c β) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (A : Y.X.Opens) (hA : IsAffineOpen A)
    {EB : Type} [AddCommGroup EB] [Module Γ(Y.X, A) EB] (MB : LieModel Y.t.G hA.fromSpec EB) (e₁ : Fin D.p → EB)
    (e₂ : Fin D.q → EB) (h1 : 1 ≤ D.p + D.q) (hr1 : τ (H.rt : E) = H.rt0) (hr2 : σ (tauIn c τ H.rt) = H.rt0)
    (hU : IsUnitAn τ σ Φ) {d a : ℕ} (C : BdryChart Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) d a)
    (fR : Γ(Y.X, A) →+* C.R) (f : Sp C.R ⟶ Y.X) (hf : spMap fR ≫ hA.fromSpec = f) (mR : SABMap C.t Y.t f)
    (k' : C.V ⟶ Xo.XF c) (φ₀ : C.tV.G.left ⟶ Y.oF.t.G.left) (hk : k' ≫ pullback.fst _ _ = C.k)
    (hkj : k' ≫ Y.j = C.j ≫ f) (h₁ : φ₀ ≫ Y.oF.t.G.hom = C.tV.G.hom ≫ k') (h₂ : φ₀ ≫ Y.m0.toSABMap.φ = C.m₂.φ)
    (h₃ : φ₀ ≫ Y.m.φ = C.m₁.φ ≫ mR.φ)
    (hover : ∀ z ∈ ball (0 : Fin d → ℂ) 1, (spMap ((C.ψ z).comp fR) ≫ hA.fromSpec) ≫ Y.s = spMap (σ.comp β))
    (hsnd : ∀ z ∈ punct d a 1, (C.pt z ≫ k') ≫ pullback.snd _ _ = spMap σ)
    (hframe : ∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X) (v : Fin D.p → (epsAt y ⟶ Y.t.G))
      (w : Fin D.q → (epsAt y ⟶ Y.t.G)), y = spMap f ≫ hA.fromSpec → y ≫ Y.s = spMap (σ.comp β) →
      (∀ i, (v i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) →
      (∀ j, (w j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) →
      IsEigFrame Y.t.act y (σ.comp (tauIn c τ)) v ∧
        IsEigFrame Y.t.act y (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) w) :
    ∃ (ρ' : ℝ) (h₀ : (Fin d → ℂ) → ℂ), 0 < ρ' ∧ ρ' ≤ 1 ∧ DifferentiableOn ℂ h₀ (ball 0 ρ') ∧
      (∀ z ∈ ball (0 : Fin d → ℂ) ρ', h₀ z ≠ 0) ∧ ∀ z ∈ punct d a ρ', ∀ (v : Vecs (C.pt z ≫ k') D.p)
        (w : Vecs (C.pt z ≫ k') D.q) (v₀ : Fin D.p → (epsAt ((C.pt z ≫ k') ≫ Y.j) ⟶ Y.t.G))
        (w₀ : Fin D.q → (epsAt ((C.pt z ≫ k') ≫ Y.j) ⟶ Y.t.G)),
        (∀ i, SameVec Y (C.pt z ≫ k') (v i) (v₀ i)) → (∀ j, SameVec Y (C.pt z ≫ k') (w j) (w₀ j)) →
        (∀ i, (v₀ i).left = spMap (dualMap ((C.ψ z).comp fR)) ≫ (MB.pt (e₁ i)).left) →
        (∀ j, (w₀ j).left = spMap (dualMap ((C.ψ z).comp fR)) ≫ (MB.pt (e₂ j)).left) →
        h₀ z = Φ (C.pt z ≫ k') v w := by
  classical
  have hs : Smooth Y.t.G.hom := Y.t.semi.smooth
  choose u₁ hu₁ using fun i => exists_coord hA.fromSpec fR f hf mR.φ mR.cart C.M (MB.pt (e₁ i)) (MB.tan _)
  choose u₂ hu₂ using fun j => exists_coord hA.fromSpec fR f hf mR.φ mR.cart C.M (MB.pt (e₂ j)) (MB.tan _)
  have hy0 : spMap (C.ψ 0) ≫ 𝟙 _ ≫ f = spMap ((C.ψ 0).comp fR) ≫ hA.fromSpec := by
    rw [Category.id_comp, ← hf, spMap_comp', Category.assoc]
  have hfr0 := hframe ((C.ψ 0).comp fR) _
    (fun i => LieCarrier.epsHom ((C.ψ 0).comp fR) hA.fromSpec _ rfl ≫ MB.pt (e₁ i))
    (fun j => LieCarrier.epsHom ((C.ψ 0).comp fR) hA.fromSpec _ rfl ≫ MB.pt (e₂ j)) rfl
    (hover 0 (mem_ball_self one_pos)) (fun _ => rfl) (fun _ => rfl)
  have ind₁ := indep_of_frame hs (C.ψ 0) (𝟙 _ ≫ f) _ hy0 (LieMove.pushModel mR.cart C.M) u₁ Y.t.act _ _ hfr0.1
    (fun i => by
      show spMap (dualMap ((C.ψ 0).comp fR)) ≫ (MB.pt (e₁ i)).left =
        spMap (dualMap (C.ψ 0)) ≫ (C.M.pt (u₁ i)).left ≫ mR.φ
      rw [hu₁, spMap_dual, Category.assoc])
  have ind₂ := indep_of_frame hs (C.ψ 0) (𝟙 _ ≫ f) _ hy0 (LieMove.pushModel mR.cart C.M) u₂ Y.t.act _ _ hfr0.2
    (fun j => by
      show spMap (dualMap ((C.ψ 0).comp fR)) ≫ (MB.pt (e₂ j)).left =
        spMap (dualMap (C.ψ 0)) ≫ (C.M.pt (u₂ j)).left ≫ mR.φ
      rw [hu₂, spMap_dual, Category.assoc])
  have key : ∀ z ∈ punct d a 1, ∃ (v : Vecs (C.pt z ≫ k') D.p) (w : Vecs (C.pt z ≫ k') D.q)
      (v₀ : Fin D.p → (epsAt ((C.pt z ≫ k') ≫ Y.j) ⟶ Y.t.G))
      (w₀ : Fin D.q → (epsAt ((C.pt z ≫ k') ≫ Y.j) ⟶ Y.t.G)),
      IsFramed Set.univ τ σ (C.pt z ≫ k') v w ∧ (∀ i, SameVec Y (C.pt z ≫ k') (v i) (v₀ i)) ∧
      (∀ j, SameVec Y (C.pt z ≫ k') (w j) (w₀ j)) ∧
      (∀ i, (v₀ i).left = spMap (dualMap ((C.ψ z).comp fR)) ≫ (MB.pt (e₁ i)).left) ∧
      (∀ j, (w₀ j).left = spMap (dualMap ((C.ψ z).comp fR)) ≫ (MB.pt (e₂ j)).left) ∧
      (∀ i, ∃ uu : Sp (DualNumber ℂ) ⟶ C.tV.G.left, uu ≫ C.m₂.φ = (v i).left ∧
        uu ≫ C.m₁.φ = spMap (dualMap (C.ψ z)) ≫ (C.M.pt (u₁ i)).left) ∧
      (∀ j, ∃ uu : Sp (DualNumber ℂ) ⟶ C.tV.G.left, uu ≫ C.m₂.φ = (w j).left ∧
        uu ≫ C.m₁.φ = spMap (dualMap (C.ψ z)) ≫ (C.M.pt (u₂ j)).left) := by
    intro z hz
    have hp := (C.pt_eq z hz).1
    choose v v₀ uu a1 a2 a3 a4 using fun i =>
      exists_vec Y C k' φ₀ mR hk h₁ h₂ h₃ (C.pt z) (C.ψ z) hp (u₁ i)
    choose w w₀ uw b1 b2 b3 b4 using fun j =>
      exists_vec Y C k' φ₀ mR hk h₁ h₂ h₃ (C.pt z) (C.ψ z) hp (u₂ j)
    have c1 : ∀ i, (v₀ i).left = spMap (dualMap ((C.ψ z).comp fR)) ≫ (MB.pt (e₁ i)).left := fun i => by
      have e₁' := a4 i
      rw [hu₁ i] at e₁'
      have q : spMap (dualMap ((C.ψ z).comp fR)) ≫ (MB.pt (e₁ i)).left =
          spMap (dualMap (C.ψ z)) ≫ spMap (dualMap fR) ≫ (MB.pt (e₁ i)).left := by
        rw [spMap_dual, Category.assoc]
      exact e₁'.trans q.symm
    have c2 : ∀ j, (w₀ j).left = spMap (dualMap ((C.ψ z).comp fR)) ≫ (MB.pt (e₂ j)).left := fun j => by
      have e₂' := b4 j
      rw [hu₂ j] at e₂'
      have q : spMap (dualMap ((C.ψ z).comp fR)) ≫ (MB.pt (e₂ j)).left =
          spMap (dualMap (C.ψ z)) ≫ spMap (dualMap fR) ≫ (MB.pt (e₂ j)).left := by
        rw [spMap_dual, Category.assoc]
      exact e₂'.trans q.symm
    have hy : (C.pt z ≫ k') ≫ Y.j = spMap ((C.ψ z).comp fR) ≫ hA.fromSpec := by
      rw [Category.assoc, hkj, ← Category.assoc, hp, spMap_comp', Category.assoc, hf]
    have hf2 := hframe ((C.ψ z).comp fR) ((C.pt z ≫ k') ≫ Y.j) v₀ w₀ hy (by rw [hy]; exact hover z hz.1) c1 c2
    exact ⟨v, w, v₀, w₀, GlobalTheory.T.vectors_at_complex_point E H D l Xo c O β Y τ σ _ v w v₀ w₀ (hsnd z hz) a1 b1 hf2.1 hf2.2, a1, b1,
      c1, c2, fun i => ⟨uu i, a2 i, a3 i⟩, fun j => ⟨uw j, b2 j, b3 j⟩⟩
  choose v w v₀ w₀ hF hS₁ hS₂ hc₁ hc₂ hl₁ hl₂ using key
  let φ : (Fin d → ℂ) → ℂ := fun z => if hz : z ∈ punct d a 1 then Φ (C.pt z ≫ k') (v z hz) (w z hz) else 0
  obtain ⟨ρ', h₀, hρ', hρ1, hd, hne, hφ⟩ := GlobalTheory.T.boundary_chart_frame_growth E H D l Xo c τ σ Φ d a C k' u₁ u₂ φ h1 hr2 hr1 hU hk ind₁ ind₂
    (fun z hz => ⟨v z hz, w z hz, hF z hz, hl₁ z hz, hl₂ z hz, by simp only [φ, dif_pos hz]⟩)
  refine ⟨ρ', h₀, hρ', hρ1, hd, hne, ?_⟩
  intro z hz vv ww vv₀ ww₀ s1 s2 t1 t2
  have hz1 : z ∈ punct d a 1 := ⟨ball_subset_ball hρ1 hz.1, hz.2⟩
  have e₀ : vv₀ = v₀ z hz1 := funext fun i => Over.OverMorphism.ext ((t1 i).trans (hc₁ z hz1 i).symm)
  have f₀ : ww₀ = w₀ z hz1 := funext fun j => Over.OverMorphism.ext ((t2 j).trans (hc₂ z hz1 j).symm)
  have e₁' : vv = v z hz1 := funext fun i => SameVec.unique_left (s1 i) (by rw [e₀]; exact hS₁ z hz1 i)
  have f₁ : ww = w z hz1 := funext fun j => SameVec.unique_left (s2 j) (by rw [f₀]; exact hS₂ z hz1 j)
  rw [hφ z hz]
  simp only [φ, dif_pos hz1, e₁', f₁]

end GlobalTheory.CompanionTheory.Ar.Flat.ChartFamily

theorem GlobalTheory.CompanionTheory.Ar.Flat.flat_unit_along_families : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (X' : Scheme.{0}) (π : X' ⟶ Y.X) (s' : X' ⟶ Sp c.F) (d : ℕ) (W' : X'.Opens) (jW : W'.toScheme ⟶ Xo.XF c) (A : Y.X.Opens) (hA : IsAffineOpen A) (EB : Type) [AddCommGroup EB] [Module Γ(Y.X, A) EB] (MB : LieModel Y.t.G hA.fromSpec EB) (e₁ : Fin D.p → EB) (e₂ : Fin D.q → EB) (x : Sp ℂ ⟶ X'), 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → IsUnitAn τ σ Φ → π ≫ Y.s = s' ≫ spMap β → SmoothOfRelativeDimension d s' → Geo.ResK.HasSncCoords s' d (W' : Set X')ᶜ → jW ≫ Y.j = W'.ι ≫ π → jW ≫ pullback.snd _ _ = W'.ι ≫ s' → x ≫ s' = spMap σ → ⊤ ≤ x ⁻¹ᵁ (π ⁻¹ᵁ A) → (∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X) (v : Fin D.p → (epsAt y ⟶ Y.t.G)) (w : Fin D.q → (epsAt y ⟶ Y.t.G)), y = spMap f ≫ hA.fromSpec → y ≫ Y.s = spMap (σ.comp β) → (∀ i, (v i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → IsEigFrame Y.t.act y (σ.comp (tauIn c τ)) v ∧ IsEigFrame Y.t.act y (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) w) → ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X')), IsOpen B → IsHolTo B y → (∀ b ∈ B, y b ≫ s' = spMap σ) → ∀ b₀ ∈ B, y b₀ = x → ∃ (ε : ℝ) (h : (Fin m → ℂ) → ℂ), 0 < ε ∧ DifferentiableOn ℂ h (Metric.ball b₀ ε) ∧ h b₀ ≠ 0 ∧ ∀ b ∈ B ∩ Metric.ball b₀ ε, ∃ f : Γ(Y.X, A) →+* ℂ, spMap f ≫ hA.fromSpec = y b ≫ π ∧ (⊤ ≤ y b ⁻¹ᵁ W' → ∀ (yy : Sp ℂ ⟶ Xo.XF c) (v : Vecs yy D.p) (w : Vecs yy D.q) (v₀ : Fin D.p → (epsAt (yy ≫ Y.j) ⟶ Y.t.G)) (w₀ : Fin D.q → (epsAt (yy ≫ Y.j) ⟶ Y.t.G)), yy ≫ Y.j = y b ≫ π → yy ≫ pullback.snd _ _ = spMap σ → (∀ i, SameVec Y yy (v i) (v₀ i)) → (∀ j, SameVec Y yy (w j) (w₀ j)) → (∀ i, (v₀ i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w₀ j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → h b = Φ yy v w) := by
  intro E _ _ _ H D l Xo c O _ β Y τ σ Φ X' π s' d W' jW A hA EB _ _ MB e₁ e₂ x h1 hr1 hr2 hU hπ hsm hsnc hj1 hj2 hxs hxA
    hframe m B y hB hy hyσ b₀ hb₀ hyb
  obtain ⟨V, hV, a, ψ, hVA, ha, hol, h0, -, hpts, hfam⟩ :=
    GlobalTheory.T.holomorphic_affine_polydisc_chart c.F σ X' s' d ((W' : Set X')ᶜ) hsm hsnc x (π ⁻¹ᵁ A) hxs hxA
  have hpt : ∀ z ∈ punct d a 1, spMap (ψ z) ≫ hV.fromSpec ≫ s' = spMap σ ∧
      centre (spMap (ψ z) ≫ hV.fromSpec) ∈ W' := fun z hz =>
    ⟨(hpts z hz.1).1, not_not.1 ((hpts z hz.1).2.2 hz)⟩
  obtain ⟨ρ, C, i₀, mR, k', φ₀, hρ, hρ1, hψ, hk, hkj, hks, h₁, h₂, h₃⟩ :=
    GlobalTheory.CompanionTheory.Ar.Flat.ChartFamily.exists_model_chart Y σ π s' d W' jW hj1 hj2 V hV a ψ ha hol hpt
  let aV : Γ(Y.X, A) →+* Γ(X', V) := (π.appLE A V hVA).hom
  have haV : spMap aV ≫ hA.fromSpec = hV.fromSpec ≫ π := IsAffineOpen.SpecMap_appLE_fromSpec π hA hV hVA
  let g : Γ(X', V) →+* C.R := (Spec.preimage i₀).hom
  have hg : spMap g = i₀ := Spec.map_preimage i₀
  have hfR : spMap (g.comp aV) ≫ hA.fromSpec = i₀ ≫ hV.fromSpec ≫ π := by
    rw [GlobalTheory.CompanionTheory.Ar.Flat.ChartFamily.spMap_comp', Category.assoc, haV, hg]
  have hin : ∀ z ∈ ball (0 : Fin d → ℂ) 1, (ρ : ℂ) • z ∈ ball (0 : Fin d → ℂ) 1 := fun z hz => by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hρ.le]
    nlinarith [norm_nonneg z]
  have hover : ∀ z ∈ ball (0 : Fin d → ℂ) 1,
      (spMap ((C.ψ z).comp (g.comp aV)) ≫ hA.fromSpec) ≫ Y.s = spMap (σ.comp β) := fun z hz => by
    have e : spMap ((C.ψ z).comp (g.comp aV)) ≫ hA.fromSpec = spMap (C.ψ z) ≫ i₀ ≫ hV.fromSpec ≫ π := by
      rw [GlobalTheory.CompanionTheory.Ar.Flat.ChartFamily.spMap_comp', Category.assoc, hfR]
    rw [e]
    calc (spMap (C.ψ z) ≫ i₀ ≫ hV.fromSpec ≫ π) ≫ Y.s = (spMap (C.ψ z) ≫ i₀) ≫ hV.fromSpec ≫ s' ≫ spMap β := by
          simp only [Category.assoc, hπ]
      _ = (spMap (ψ ((ρ : ℂ) • z)) ≫ hV.fromSpec ≫ s') ≫ spMap β := by
          rw [hψ z hz]; simp only [Category.assoc]
      _ = _ := by rw [(hpts _ (hin z hz)).1, GlobalTheory.CompanionTheory.Ar.Flat.ChartFamily.spMap_comp']
  have hsnd : ∀ z ∈ punct d a 1, (C.pt z ≫ k') ≫ pullback.snd _ _ = spMap σ := fun z hz => by
    rw [Category.assoc, hks, ← Category.assoc, (C.pt_eq z hz).1, ← Category.assoc, hψ z hz.1]
    exact (hpts _ (hin z hz.1)).1
  obtain ⟨ρ', h₀, hρ', hρ'1, hd, hne, hφ⟩ := GlobalTheory.CompanionTheory.Ar.Flat.ChartFamily.chart_unit Y τ σ Φ A hA MB e₁ e₂ h1 hr1 hr2 hU C
    (g.comp aV) _ hfR mR k' φ₀ hk (by rw [hkj]) h₁ h₂ h₃ hover hsnd hframe
  obtain ⟨ε₁, κ, hε₁, hsub, hκd, hκ0, hκ⟩ := hfam m B y hB hy hyσ b₀ hb₀ hyb
  have hκc : ContinuousAt κ b₀ := hκd.continuousOn.continuousAt (ball_mem_nhds _ hε₁)
  obtain ⟨ε₂, hε₂, hb⟩ := Metric.continuousAt_iff.1 hκc (ρ * ρ') (mul_pos hρ hρ')
  have hρc : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hn : ∀ b ∈ ball b₀ (min ε₁ ε₂), (ρ : ℂ)⁻¹ • κ b ∈ ball (0 : Fin d → ℂ) ρ' := fun b hbε => by
    have h3 := hb (ball_subset_ball (min_le_right _ _) hbε)
    rw [hκ0, dist_zero_right] at h3
    rw [mem_ball_zero_iff, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hρ.le, inv_mul_lt_iff₀ hρ]
    exact h3
  refine ⟨min ε₁ ε₂, fun b => h₀ ((ρ : ℂ)⁻¹ • κ b), lt_min hε₁ hε₂, ?_, ?_, ?_⟩
  · have hdk : DifferentiableOn ℂ (fun b => (ρ : ℂ)⁻¹ • κ b) (ball b₀ (min ε₁ ε₂)) :=
      ((hκd.mono (ball_subset_ball (min_le_left ε₁ ε₂))).const_smul ((ρ : ℂ)⁻¹)).congr fun _ _ => rfl
    exact hd.comp hdk hn
  · exact hne _ (hn b₀ (mem_ball_self (lt_min hε₁ hε₂)))
  rintro b ⟨hbB, hbε⟩
  have hbε₁ : b ∈ ball b₀ ε₁ := ball_subset_ball (min_le_left _ _) hbε
  obtain ⟨hκb, hyb'⟩ := hκ b hbε₁
  refine ⟨(ψ (κ b)).comp aV, ?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.Ar.Flat.ChartFamily.spMap_comp', Category.assoc, haV, hyb', Category.assoc]
  intro hW yy v w v₀ w₀ hyj hys hv hw hv₀ hw₀
  have hρz : (ρ : ℂ) • ((ρ : ℂ)⁻¹ • κ b) = κ b := smul_inv_smul₀ hρc _
  have hcen : centre (spMap (ψ (κ b)) ≫ hV.fromSpec) ∉ ((W' : Set X')ᶜ) := by
    rw [← hyb']
    exact not_not.2 (hW (show IsLocalRing.closedPoint ℂ ∈ (⊤ : (Sp ℂ).Opens) from trivial))
  have hκp : κ b ∈ punct d a 1 := (hpts _ hκb).2.1 hcen
  have hz : (ρ : ℂ)⁻¹ • κ b ∈ punct d a ρ' := ⟨hn b hbε, fun i hi => by
    simpa [hρ.ne'] using hκp.2 i hi⟩
  have hz1 : (ρ : ℂ)⁻¹ • κ b ∈ punct d a 1 := ⟨ball_subset_ball hρ'1 hz.1, hz.2⟩
  have hpz := (C.pt_eq _ hz1).1
  have hpψ : spMap (C.ψ ((ρ : ℂ)⁻¹ • κ b)) ≫ i₀ = spMap (ψ (κ b)) := by
    rw [hψ _ hz1.1, hρz]
  have hyy : yy = C.pt ((ρ : ℂ)⁻¹ • κ b) ≫ k' := by
    have : IsOpenImmersion Y.jQ := Y.jQ_open
    rw [← cancel_mono Y.jQ]
    apply pullback.hom_ext
    · have e1 : yy ≫ Y.j = (C.pt ((ρ : ℂ)⁻¹ • κ b) ≫ k') ≫ Y.j := by
        rw [hyj, hyb', Category.assoc _ k', hkj, ← Category.assoc, hpz, ← Category.assoc (spMap _), hpψ]
        simp only [Category.assoc]
      simpa only [Model.j, Category.assoc] using e1
    · rw [Category.assoc, Category.assoc, Y.jQ_over, hys]
      exact (hsnd _ hz1).symm
  subst hyy
  have hf : (ψ (κ b)).comp aV = (C.ψ ((ρ : ℂ)⁻¹ • κ b)).comp (g.comp aV) := by
    have e : spMap ((ψ (κ b)).comp aV) = spMap ((C.ψ ((ρ : ℂ)⁻¹ • κ b)).comp (g.comp aV)) := by
      rw [← cancel_mono hA.fromSpec, GlobalTheory.CompanionTheory.Ar.Flat.ChartFamily.spMap_comp', GlobalTheory.CompanionTheory.Ar.Flat.ChartFamily.spMap_comp',
        Category.assoc, Category.assoc, hfR, haV, ← Category.assoc (spMap _) i₀, hpψ]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  rw [hf] at hv₀ hw₀
  exact hφ _ hz v w v₀ w₀ hv hw hv₀ hw₀
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AffineChartBundleSectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_chart_bundle_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (X' : Scheme.{0}) (π : X' ⟶ Y.X) (s' : X' ⟶ Sp c.F) (d : ℕ) (W' : X'.Opens) (jW : W'.toScheme ⟶ Xo.XF c) (A : Y.X.Opens) (hA : IsAffineOpen A) (EB : Type) [AddCommGroup EB] [Module Γ(Y.X, A) EB] (MB : LieModel Y.t.G hA.fromSpec EB) (e₁ : Fin D.p → EB) (e₂ : Fin D.q → EB) (x : Sp ℂ ⟶ X'), 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → IsUnitAn τ σ Φ → π ≫ Y.s = s' ≫ spMap β → SmoothOfRelativeDimension d s' → Geo.ResK.HasSncCoords s' d (W' : Set X')ᶜ → jW ≫ Y.j = W'.ι ≫ π → jW ≫ pullback.snd _ _ = W'.ι ≫ s' → x ≫ s' = spMap σ → ⊤ ≤ x ⁻¹ᵁ (π ⁻¹ᵁ A) → (∀ (f : Γ(Y.X, A) →+* ℂ) (y : Sp ℂ ⟶ Y.X) (v : Fin D.p → (epsAt y ⟶ Y.t.G)) (w : Fin D.q → (epsAt y ⟶ Y.t.G)), y = spMap f ≫ hA.fromSpec → y ≫ Y.s = spMap (σ.comp β) → (∀ i, (v i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → IsEigFrame Y.t.act y (σ.comp (tauIn c τ)) v ∧ IsEigFrame Y.t.act y (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) w) → ∀ (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X')), IsOpen B → IsHolTo B y → (∀ b ∈ B, y b ≫ s' = spMap σ) → ∀ b₀ ∈ B, y b₀ = x → ∃ (ε : ℝ) (h : (Fin m → ℂ) → ℂ), 0 < ε ∧ DifferentiableOn ℂ h (Metric.ball b₀ ε) ∧ h b₀ ≠ 0 ∧ ∀ b ∈ B ∩ Metric.ball b₀ ε, ∃ f : Γ(Y.X, A) →+* ℂ, spMap f ≫ hA.fromSpec = y b ≫ π ∧ (⊤ ≤ y b ⁻¹ᵁ W' → ∀ (yy : Sp ℂ ⟶ Xo.XF c) (v : Vecs yy D.p) (w : Vecs yy D.q) (v₀ : Fin D.p → (epsAt (yy ≫ Y.j) ⟶ Y.t.G)) (w₀ : Fin D.q → (epsAt (yy ≫ Y.j) ⟶ Y.t.G)), yy ≫ Y.j = y b ≫ π → yy ≫ pullback.snd _ _ = spMap σ → (∀ i, SameVec Y yy (v i) (v₀ i)) → (∀ j, SameVec Y yy (w j) (w₀ j)) → (∀ i, (v₀ i).left = spMap (dualMap f) ≫ (MB.pt (e₁ i)).left) → (∀ j, (w₀ j).left = spMap (dualMap f) ≫ (MB.pt (e₂ j)).left) → h b = Φ yy v w) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.flat_unit_along_families | exact GlobalTheory.CompanionTheory.Ar.Flat.flat_unit_along_families | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.flat_unit_along_families <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PullbackFramesComplexPoint
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PullbackFramesComplexPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.PointCompare

section Val
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {F : Type} [Field F] {z : Sp F ⟶ X}

theorem val_mul {a a' : Ω} {r r' : F} (h : ValAt ξ z a r) (h' : ValAt ξ z a' r') : ValAt ξ z (a * a') (r * r') := by
  obtain ⟨hs, s, e1, e2⟩ := h
  obtain ⟨_, s', e1', e2'⟩ := h'
  have f2 : RootHt.Pick.valMap z s = r := e2
  have f2' : RootHt.Pick.valMap z s' = r' := e2'
  refine ⟨hs, s * s', by rw [map_mul, e1, e1'], ?_⟩
  show RootHt.Pick.valMap z (s * s') = r * r'
  rw [map_mul, f2, f2']

theorem val_det (h : genPt ξ ⤳ centre z) {n : ℕ} {P : Matrix (Fin n) (Fin n) Ω} {A : Matrix (Fin n) (Fin n) F}
    (hP : ∀ i j, ValAt ξ z (P i j) (A i j)) : ValAt ξ z P.det A.det := by
  have : ∀ i j, ∃ s : X.presheaf.stalk (centre z), genMap ξ ⟨centre z, h⟩ s = P i j ∧
      (Scheme.stalkClosedPointTo z).hom s = A i j := fun i j => by
    obtain ⟨_, s, e1, e2⟩ := hP i j
    exact ⟨s, e1, e2⟩
  choose s e1 e2 using this
  refine ⟨h, (Matrix.of s).det, ?_, ?_⟩
  · rw [RingHom.map_det]
    congr 1
    ext i j
    exact e1 i j
  · show RootHt.Pick.valMap z _ = A.det
    rw [RingHom.map_det]
    congr 1
    ext i j
    exact e2 i j

end Val

section Gen
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {F : Type} [Field F] {x : Sp F ⟶ S}

theorem exists_comb {n : ℕ} (cf : Fin n → F) (v : Fin n → (epsAt x ⟶ G)) : ∃ w, IsComb cf v w :=
  ⟨_, fun i => LieTangent.epsScale x (cf i) ≫ v i, fun _ => rfl, rfl⟩

theorem frame_det {P : Type} [CommRing P] {act : OAct P G} {σ : P →+* F} {n : ℕ} {v v' : Fin n → (epsAt x ⟶ G)}
    {A : Matrix (Fin n) (Fin n) F} (hv : IsEigFrame act x σ v) (hv' : IsEigFrame act x σ v')
    (hA : ∀ i, IsComb (A i) v (v' i)) : A.det ≠ 0 := by
  have : ∀ i, ∃ cf, IsComb cf v' (v i) := fun i => (hv'.2 _ (hv.1 i)).exists
  choose C hC using this
  have ht : ∀ i, IsTanAt G x (v i) := fun i => (hv.1 i).1
  have h1 := GlobalTheory.T.is_comb_matrix_mul S G F x n n n v v' v (Matrix.of C) A ht hA hC
  have h2 := GlobalTheory.T.is_comb_identity_matrix S G F x n v ht
  have h3 : Matrix.of C * A = 1 := by
    ext i j
    have := (hv.2 _ (hv.1 i)).unique (h1 i) (h2 i)
    exact congrFun this j
  intro h0
  have := congrArg Matrix.det h3
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_one] at this
  exact zero_ne_one this

end Gen

section Main
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {U : Set (Xo.XF c)}

theorem expand (Z : CptOver Y U) {F : Type} [Field F] {y : Sp F ⟶ Xo.XF c}
    (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (σ : E →+* ℂ) (σ' : 𝓞 E →+* F) {n : ℕ} {c₀ b₁ : Fin n → Z.V}
    {v₀ v : Vecs y n} {t : Z.Ω} (hc : (Z.eig σ).IsFrameAt c₀ ⟨_, h⟩) (h₀ : Rep.IsValFam Z y c₀ v₀)
    (h₁ : Rep.IsValFam Z y b₁ v) (he : ∀ i, b₁ i ∈ eigSp Z.ρ (Z.inc.comp (tauIn c σ)))
    (hf₀ : IsEigFrame Xo.univ.t.act (under y) σ' v₀) (hf : IsEigFrame Xo.univ.t.act (under y) σ' v)
    (hw : exteriorPower.ιMulti Z.Ω n b₁ = t • exteriorPower.ιMulti Z.Ω n c₀) :
    ∃ A : Matrix (Fin n) (Fin n) F, (∀ i, IsComb (A i) v₀ (v i)) ∧ A.det ≠ 0 ∧
      ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) t A.det := by
  have hb : ∀ i, b₁ i ∈ Z.eig σ ⟨_, h⟩ := fun i => by
    obtain ⟨v', hv', -⟩ := h₁ i
    exact ⟨RootHt.Pick.mem_lat_of_val Z.M hv' h, he i⟩
  have hco : ∀ i, ∃ P : Fin n → regAt (Z.ξ₀ ≫ Y.j) ⟨_, h⟩, ∑ j, P j • c₀ j = b₁ i := fun i => by
    have := hb i
    rw [hc.2] at this
    exact (Submodule.mem_span_range_iff_exists_fun _).1 this
  choose P hP using hco
  have hval : ∀ i j, ∃ r : F, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (P i j : Z.Ω) r := fun i j =>
    RootHt.Pick.exists_valAt (P i j).2
  choose A hA using hval
  let Pm : Matrix (Fin n) (Fin n) Z.Ω := fun i j => (P i j : Z.Ω)
  have hb' : b₁ = fun i => ∑ j, Pm i j • c₀ j := by
    funext i
    rw [← hP i]
    rfl
  have hdet : t = Pm.det := by
    have h1 := GlobalTheory.T.iota_multi_change_of_basis_det Z.Ω Z.V n c₀ Pm
    rw [← hb', hw] at h1
    have h2 : (t - Pm.det) • exteriorPower.ιMulti Z.Ω n c₀ = 0 := by
      rw [sub_smul, h1, sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right (GlobalTheory.T.iota_multi_ne_zero_of_lin_indep Z.Ω Z.V n c₀ hc.1))
  have hcomb : ∀ i, IsComb (Matrix.of A i) v₀ (v i) := fun i => by
    obtain ⟨w, hw'⟩ := exists_comb (Matrix.of A i) v₀
    obtain ⟨w', hw₁, hw₂⟩ := GlobalTheory.T.component_specialization_tangent_comb E H D l Xo c O β Y U Z F y n c₀ v₀ (Pm i) (Matrix.of A i) w h h₀ (hA i) hw'
    obtain ⟨v', hv₁, hv₂⟩ := h₁ i
    have e : ∑ j, Pm i j • c₀ j = b₁ i := by rw [hb']
    rw [e] at hw₁
    have e' := LieModel.ValAt.unique Z.gen hw₁ hv₁
    subst e'
    rw [← SameVec.unique_left hw₂ hv₂]
    exact hw'
  refine ⟨Matrix.of A, hcomb, frame_det hf₀ hf hcomb, ?_⟩
  rw [hdet]
  exact val_det h hA

end Main

theorem valAt_pull {X X' : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω ⟶ X'} {π : X' ⟶ X}
    (hd : ξ' ≫ π = ξ) {y' : Sp ℂ ⟶ X'} (hq : genPt ξ' ⤳ centre y') {a : Ω} {r : ℂ}
    (h : ValAt ξ (y' ≫ π) a r) : ValAt ξ' y' a r := by
  obtain ⟨hp, s, hs, hr⟩ := h
  have hdom : Dominates ξ' ξ π (RingHom.id Ω) := by
    change ξ' ≫ π = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, hd]
  refine ⟨hq, (π.stalkMap (centre y')).hom s, ?_, ?_⟩
  · exact (RegAtDom.genMap_stalkMap hdom (centre y') hq hp s).trans hs
  · rw [← hr, Scheme.stalkClosedPointTo_comp]
    rfl

theorem genPt_specializes {X X' : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {ξ' : Sp Ω ⟶ X'} {π : X' ⟶ X}
    (hd : ξ' ≫ π = ξ) {y' : Sp ℂ ⟶ X'} (hq : genPt ξ' ⤳ centre y') : genPt ξ ⤳ centre (y' ≫ π) := by
  have hdom : Dominates ξ' ξ π (RingHom.id Ω) := by
    change ξ' ≫ π = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ
    rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, hd]
  have := hq.map π.continuous
  rw [RegAtDom.map_genPt hdom] at this
  exact this

theorem point_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (b₁ v₁ : Fin D.p → Z.V) (b₂ v₂ : Fin D.q → Z.V) (X' : Scheme.{0}) (π : X' ⟶ Y.X) (ξ' : Sp Z.Ω ⟶ X') (y' : Sp ℂ ⟶ X') (yy : Sp ℂ ⟶ Xo.XF c) (v vz : Vecs yy D.p) (w wz : Vecs yy D.q) (α κ : Z.Ω) (r : ℂ), ξ' ≫ π = Z.ξ₀ ≫ Y.j → IsCptGen ξ' → yy ≫ Y.j = y' ≫ π → IsUnitAn τ σ Φ → IsFramed Set.univ τ σ yy v w → IsFramed Set.univ τ σ yy vz wz → (∀ i, ∃ v', Z.M.ValAt (yy ≫ Y.j) (b₁ i) v' ∧ SameVec Y yy (v i) v') → (∀ j, ∃ w', Z.M.ValAt (yy ≫ Y.j) (b₂ j) w' ∧ SameVec Y yy (w j) w') → (∀ i, ∃ v', Z.M.ValAt (yy ≫ Y.j) (v₁ i) v' ∧ SameVec Y yy (vz i) v') → (∀ j, ∃ w', Z.M.ValAt (yy ≫ Y.j) (v₂ j) w' ∧ SameVec Y yy (wz j) w') → (∀ q : Cpt (Z.ξ₀ ≫ Y.j), q.1 = centre (yy ≫ Y.j) → (Z.eig τ).IsFrameAt v₁ q ∧ (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt v₂ q) → (∀ i, b₁ i ∈ eigSp Z.ρ (Z.inc.comp (tauIn c τ))) → (∀ j, b₂ j ∈ eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ)))) → α ≠ 0 → κ ≠ 0 → exteriorPower.ιMulti Z.Ω D.p v₁ = α • exteriorPower.ιMulti Z.Ω D.p b₁ → exteriorPower.ιMulti Z.Ω D.q v₂ = κ • exteriorPower.ιMulti Z.Ω D.q b₂ → ValAt ξ' y' (α / κ) r → Φ yy v w = Φ yy vz wz * r := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ σ Φ b₁ v₁ b₂ v₂ X' π ξ' y' yy v vz w wz α κ r hξ hgen hyy hΦ hf hfz hb₁ hb₂
    hz₁ hz₂ hfr he₁ he₂ hα hκ hw₁ hw₂ hr
  obtain ⟨hq, -⟩ := id hr
  have h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (yy ≫ Y.j) := by
    rw [hyy]
    exact genPt_specializes hξ hq
  obtain ⟨hfr₁, hfr₂⟩ := hfr ⟨_, h⟩ rfl
  have hw₁' : exteriorPower.ιMulti Z.Ω D.p b₁ = α⁻¹ • exteriorPower.ιMulti Z.Ω D.p v₁ := by
    rw [hw₁, smul_smul, inv_mul_cancel₀ hα, one_smul]
  have hw₂' : exteriorPower.ιMulti Z.Ω D.q b₂ = κ⁻¹ • exteriorPower.ιMulti Z.Ω D.q v₂ := by
    rw [hw₂, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  obtain ⟨A, hA, hA0, hAv⟩ := expand Z h τ (σ.comp (tauIn c τ)) hfr₁ hz₁ hb₁ he₁ hfz.2.2.1 hf.2.2.1 hw₁'
  obtain ⟨B, hB, -, hBv⟩ := expand Z h (ComplexEmbedding.conjugate τ)
    (σ.comp (tauIn c (ComplexEmbedding.conjugate τ))) hfr₂ hz₂ hb₂ he₂ hfz.2.2.2 hf.2.2.2 hw₂'
  rw [hyy] at hAv hBv
  have hA' := valAt_pull hξ hq hAv
  have hB' := valAt_pull hξ hq hBv
  have hm := val_mul hr hA'
  have e : α / κ * α⁻¹ = κ⁻¹ := by field_simp
  rw [e] at hm
  have hdet : r * A.det = B.det := LieTangent.valAt_unique hgen hm hB'
  have hc := hΦ.chg yy vz wz v w A B hfz hf hA hB
  rw [← hdet] at hc
  rw [← _root_.mul_assoc] at hc
  exact mul_right_cancel₀ hA0 hc

end GlobalTheory.CompanionTheory.Ar.Flat.PointCompare
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PullbackFramesComplexPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_frames_complex_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (b₁ v₁ : Fin D.p → Z.V) (b₂ v₂ : Fin D.q → Z.V) (X' : Scheme.{0}) (π : X' ⟶ Y.X) (ξ' : Sp Z.Ω ⟶ X') (y' : Sp ℂ ⟶ X') (yy : Sp ℂ ⟶ Xo.XF c) (v vz : Vecs yy D.p) (w wz : Vecs yy D.q) (α κ : Z.Ω) (r : ℂ), ξ' ≫ π = Z.ξ₀ ≫ Y.j → IsCptGen ξ' → yy ≫ Y.j = y' ≫ π → IsUnitAn τ σ Φ → IsFramed Set.univ τ σ yy v w → IsFramed Set.univ τ σ yy vz wz → (∀ i, ∃ v', Z.M.ValAt (yy ≫ Y.j) (b₁ i) v' ∧ SameVec Y yy (v i) v') → (∀ j, ∃ w', Z.M.ValAt (yy ≫ Y.j) (b₂ j) w' ∧ SameVec Y yy (w j) w') → (∀ i, ∃ v', Z.M.ValAt (yy ≫ Y.j) (v₁ i) v' ∧ SameVec Y yy (vz i) v') → (∀ j, ∃ w', Z.M.ValAt (yy ≫ Y.j) (v₂ j) w' ∧ SameVec Y yy (wz j) w') → (∀ q : Cpt (Z.ξ₀ ≫ Y.j), q.1 = centre (yy ≫ Y.j) → (Z.eig τ).IsFrameAt v₁ q ∧ (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt v₂ q) → (∀ i, b₁ i ∈ eigSp Z.ρ (Z.inc.comp (tauIn c τ))) → (∀ j, b₂ j ∈ eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ)))) → α ≠ 0 → κ ≠ 0 → exteriorPower.ιMulti Z.Ω D.p v₁ = α • exteriorPower.ιMulti Z.Ω D.p b₁ → exteriorPower.ιMulti Z.Ω D.q v₂ = κ • exteriorPower.ιMulti Z.Ω D.q b₂ → ValAt ξ' y' (α / κ) r → Φ yy v w = Φ yy vz wz * r := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.PointCompare.point_compare | exact GlobalTheory.CompanionTheory.Ar.Flat.PointCompare.point_compare | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.PointCompare.point_compare <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairFramesOnSet
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairFramesOnSet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat.LineGenerator

theorem exists_ιMulti_eq_smul {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}
    {v b : Fin r → E} (h : ∀ i, v i ∈ Submodule.span Ω (Set.range b)) :
    ∃ α : Ω, exteriorPower.ιMulti Ω r v = α • exteriorPower.ιMulti Ω r b := by
  classical
  have hc : ∀ i, ∃ c : Fin r → Ω, ∑ j, c j • b j = v i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (h i)
  choose c hc using hc
  have hv : v = fun i => ∑ j, c i j • b j := funext fun i => (hc i).symm
  have hsum : exteriorPower.ιMulti Ω r v =
      ∑ f : Fin r → Fin r, (∏ i, c i (f i)) • exteriorPower.ιMulti Ω r (fun i => b (f i)) := by
    rw [hv]
    refine ((exteriorPower.ιMulti Ω r (M := E)).toMultilinearMap.map_sum
      (fun i j => c i j • b j)).trans (Finset.sum_congr rfl fun f _ => ?_)
    exact (exteriorPower.ιMulti Ω r (M := E)).toMultilinearMap.map_smul_univ
      (fun i => c i (f i)) (fun i => b (f i))
  have hmem : exteriorPower.ιMulti Ω r v ∈ Submodule.span Ω {exteriorPower.ιMulti Ω r b} := by
    rw [hsum]
    refine Submodule.sum_mem _ fun f _ => Submodule.smul_mem _ _ ?_
    by_cases hf : Function.Injective f
    · let σ : Equiv.Perm (Fin r) := Equiv.ofBijective f (Finite.injective_iff_bijective.1 hf)
      have h5 : (fun i => b (f i)) = b ∘ σ := rfl
      rw [h5, (exteriorPower.ιMulti Ω r (M := E)).map_perm b σ]
      have hm := Submodule.mem_span_singleton_self (R := Ω) (exteriorPower.ιMulti Ω r b)
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
      · rw [hs, one_smul]
        exact hm
      · rw [hs, Units.neg_smul, one_smul]
        exact neg_mem hm
    · have h6 : ¬ Function.Injective (fun i => b (f i)) := fun hh =>
        hf (Function.Injective.of_comp (f := b) hh)
      rw [(exteriorPower.ιMulti Ω r (M := E)).map_eq_zero_of_not_injective _ h6]
      exact zero_mem _
  obtain ⟨α, hα⟩ := Submodule.mem_span_singleton.1 hmem
  exact ⟨α, hα.symm⟩

theorem frame_mem_of_isVBOn {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {E : Type} [AddCommGroup E] [Module Ω E] {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ}
    {V : Submodule Ω E} {v : Fin r → E} {x : Cpt ξ} (hx : x ∈ T) (hL : L.IsVBOn T r V)
    (hv : L.IsFrameAt v x) (i : Fin r) : v i ∈ V := by
  obtain ⟨U, hU, e, he, hfr⟩ := hL x hx
  have h1 : v i ∈ L x := hv.2 ▸ Submodule.subset_span ⟨i, rfl⟩
  rw [(hfr x hx hU).2] at h1
  have h2 : Submodule.span (regAt ξ x) (Set.range e) ≤
      (Submodule.span Ω (Set.range e)).restrictScalars (regAt ξ x) :=
    Submodule.span_le.2 fun _ hy => Submodule.subset_span hy
  exact he ▸ h2 h1

theorem exists_wedge_coeff {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    {E : Type} [AddCommGroup E] [Module Ω E] {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ}
    {V : Submodule Ω E} {v b : Fin r → E} {x : Cpt ξ} (hx : x ∈ T) (hL : L.IsVBOn T r V)
    (hb : Submodule.span Ω (Set.range b) = V) (hv : L.IsFrameAt v x) :
    ∃ α : Ω, α ≠ 0 ∧ exteriorPower.ιMulti Ω r v = α • exteriorPower.ιMulti Ω r b := by
  obtain ⟨α, hα⟩ := exists_ιMulti_eq_smul (v := v) (b := b)
    fun i => hb ▸ frame_mem_of_isVBOn hx hL hv i
  refine ⟨α, ?_, hα⟩
  rintro rfl
  exact GenModel.ιMulti_ne_zero hv.1 (by rw [hα, zero_smul])

theorem isGenAt_div : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (A B : Lat ξ V) (p q : ℕ) (Vp Vq : Submodule Ω V) (T : Set (Cpt ξ)) (b₁ v₁ : Fin p → V) (b₂ v₂ : Fin q → V) (x : Cpt ξ), x ∈ T → A.IsVBOn T p Vp → B.IsVBOn T q Vq → LinearIndependent Ω b₁ → Submodule.span Ω (Set.range b₁) = Vp → LinearIndependent Ω b₂ → Submodule.span Ω (Set.range b₂) = Vq → A.IsFrameAt v₁ x → B.IsFrameAt v₂ x → ∃ α κ : Ω, α ≠ 0 ∧ κ ≠ 0 ∧ exteriorPower.ιMulti Ω p v₁ = α • exteriorPower.ιMulti Ω p b₁ ∧ exteriorPower.ιMulti Ω q v₂ = κ • exteriorPower.ιMulti Ω q b₂ ∧ (lineLat A B p q (exteriorPower.ιMulti Ω p b₁) (exteriorPower.ιMulti Ω q b₂)).IsGenAt x (α / κ) := by
  intro X Ω _ ξ V _ _ A B p q Vp Vq T b₁ v₁ b₂ v₂ x hx hA hB hb₁ hs₁ hb₂ hs₂ hv₁ hv₂
  obtain ⟨α, hα, e₁⟩ := exists_wedge_coeff hx hA hs₁ hv₁
  obtain ⟨κ, hκ, e₂⟩ := exists_wedge_coeff hx hB hs₂ hv₂
  have hco : IsCoeffAt A B p q (exteriorPower.ιMulti Ω p b₁) (exteriorPower.ιMulti Ω q b₂) x (κ / α) :=
    ⟨α, κ, hα, hκ, by rw [GenModel.wedge_of_frame hv₁, e₁], by rw [GenModel.wedge_of_frame hv₂, e₂],
      div_mul_cancel₀ _ hα⟩
  have key := GlobalTheory.T.wedge_line_lattice_vector_bundle X Ω ξ V A B p q Vp Vq T _ _ hA hB (GenModel.ιMulti_ne_zero hb₁)
    (GenModel.ιMulti_ne_zero hb₂) ⟨x, hx, _, hco⟩
  exact ⟨α, κ, hα, hκ, e₁, e₂, key.2.2 x hx v₁ v₂ α κ hv₁ hv₂ e₁ e₂⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LineGenerator
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PairFramesOnSetStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_frames_on_set : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (A B : Lat ξ V) (p q : ℕ) (Vp Vq : Submodule Ω V) (T : Set (Cpt ξ)) (b₁ v₁ : Fin p → V) (b₂ v₂ : Fin q → V) (x : Cpt ξ), x ∈ T → A.IsVBOn T p Vp → B.IsVBOn T q Vq → LinearIndependent Ω b₁ → Submodule.span Ω (Set.range b₁) = Vp → LinearIndependent Ω b₂ → Submodule.span Ω (Set.range b₂) = Vq → A.IsFrameAt v₁ x → B.IsFrameAt v₂ x → ∃ α κ : Ω, α ≠ 0 ∧ κ ≠ 0 ∧ exteriorPower.ιMulti Ω p v₁ = α • exteriorPower.ιMulti Ω p b₁ ∧ exteriorPower.ιMulti Ω q v₂ = κ • exteriorPower.ιMulti Ω q b₂ ∧ (lineLat A B p q (exteriorPower.ιMulti Ω p b₁) (exteriorPower.ιMulti Ω q b₂)).IsGenAt x (α / κ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LineGenerator.isGenAt_div | exact GlobalTheory.CompanionTheory.Ar.Flat.LineGenerator.isGenAt_div | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LineGenerator.isGenAt_div <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameFunctionCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_vecs {S : Scheme.{0}} {G : Over S} {R R' : Type} [CommRing R] [CommRing R'] (x : Sp R ⟶ S) (f : R →+* R')
    (y : Sp R' ⟶ S) (hy : y = spMap f ≫ x) {n : ℕ} (u : Fin n → (epsAt x ⟶ G)) :
    ∃ u' : Fin n → (epsAt y ⟶ G), ∀ i, (u' i).left = spMap (dualMap f) ≫ (u i).left :=
  ⟨fun i => LieCarrier.epsHom f x y hy.symm ≫ u i, fun i => rfl⟩

theorem extendsUnitAt_resolution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (X' : Scheme.{0}) (π : X' ⟶ Y.X) (s' : X' ⟶ Sp c.F) (d : ℕ) (ξ' : Sp Z.Ω ⟶ X') (W' W : X'.Opens) (jW : W'.toScheme ⟶ Xo.XF c) (F : (Sp ℂ ⟶ X') → ℂ), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → IsUnitAn τ σ Φ → LinearIndependent Z.Ω b₁ → Submodule.span Z.Ω (Set.range b₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) → LinearIndependent Z.Ω b₂ → Submodule.span Z.Ω (Set.range b₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → π ≫ Y.s = s' ≫ spMap β → SmoothOfRelativeDimension d s' → Geo.ResK.HasSncCoords s' d (W' : Set X')ᶜ → ξ' ≫ π = Z.ξ₀ ≫ Y.j → IsCptGen ξ' → jW ≫ Y.j = W'.ι ≫ π → jW ≫ pullback.snd _ _ = W'.ι ≫ s' → W ≤ W' → (∀ (y' : Sp ℂ ⟶ X') (y : Sp ℂ ⟶ Xo.XF c), y' ≫ s' = spMap σ → ⊤ ≤ y' ⁻¹ᵁ W → genPt ξ' ⤳ centre y' → y ≫ Y.j = y' ≫ π → y ≫ pullback.snd _ _ = spMap σ → ∃ (v : Vecs y D.p) (w : Vecs y D.q), IsFramed Set.univ τ σ y v w ∧ ((∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w') ∧ F y' = Φ y v w) → (∀ p : Cpt ξ', p.1 ∈ W → ((lineLat (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q (exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂)).pull ξ' π (AddMonoidHom.id _)).IsGenAt p 1) → ∀ (x : Sp ℂ ⟶ X') (h : genPt ξ' ⤳ centre x), x ≫ s' = spMap σ → ∃ t : Z.Ω, ((lineLat (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q (exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂)).pull ξ' π (AddMonoidHom.id _)).IsGenAt ⟨centre x, h⟩ t ∧ ExtendsUnitAt s' σ ξ' W F t x := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ σ Φ b₁ b₂ X' π s' d ξ' W' W jW F hβ hpq hτ hσ hΦ hb₁ hs₁ hb₂ hs₂ hπ hsm hsnc hξ hgen hj hjs hWW' hF hgen1 x h hx
  have hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ' (Z.ξ₀ ≫ Y.j) π (RingHom.id Z.Ω) := by
    have e : Spec.map (CommRingCat.ofHom (RingHom.id Z.Ω)) = 𝟙 _ := Spec.map_id _
    show ξ' ≫ π = Spec.map (CommRingCat.ofHom (RingHom.id Z.Ω)) ≫ Z.ξ₀ ≫ Y.j
    rw [hξ, e, Category.id_comp]
  obtain ⟨hp, -, hpull⟩ := pull_reg_and_gen _ _ _ _ _ _ π _ hd ⟨centre x, h⟩
  let p₀ : Cpt (Z.ξ₀ ≫ Y.j) := ⟨π (centre x), hp⟩
  have hp₀ : p₀ ∈ Z.genFib := ⟨pullback.lift π s' hπ (centre x), by
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst]⟩
  obtain ⟨hVB₁, hVB₂, -, -⟩ := GlobalTheory.T.eigen_lattice_vector_bundle E H D l Xo c O β Y U Z τ hβ hτ
  obtain ⟨A, hA, EB, _, _, MB, e₁, e₂, v₁, v₂, hp₀A, hfr, heig, hval⟩ :=
    GlobalTheory.T.frame_at_component_point E H D l Xo c O β Y U Z τ σ b₁ b₂ p₀ hβ hτ hb₁ hs₁ hb₂ hs₂ hp₀
  obtain ⟨hv₁, hv₂⟩ := hfr p₀ hp₀A
  obtain ⟨α, κ, hα, hκ, hαe, hκe, hgen0⟩ := GlobalTheory.T.pair_frames_on_set _ _ _ _ (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q _ _ Z.genFib
    b₁ v₁ b₂ v₂ p₀ hp₀ hVB₁ hVB₂ hb₁ hs₁ hb₂ hs₂ hv₁ hv₂
  refine ⟨α / κ, hpull _ _ hgen0, ?_⟩
  intro m B y hB hy hyσ b₀ hb₀ hyx
  have hxA : ⊤ ≤ x ⁻¹ᵁ (π ⁻¹ᵁ A) := fun q _ => by
    have : q = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
    rw [this]
    exact hp₀A
  obtain ⟨ε, hh, hε, hdiff, hne, key⟩ := GlobalTheory.T.affine_chart_bundle_sections E H D l Xo c O β Y τ σ Φ X' π s' d W' jW A hA EB MB e₁ e₂ x hpq hτ hσ hΦ hπ hsm hsnc hj hjs hx hxA heig m B y hB hy hyσ b₀ hb₀ hyx
  refine ⟨ε, hh, hε, hdiff, hne, fun b hbB hbW r hr => ?_⟩
  obtain ⟨f, hf, hk⟩ := key b hbB
  have hc : genPt ξ' ⤳ centre (y b) := hr.choose
  have hW' : ⊤ ≤ y b ⁻¹ᵁ W' := fun q hq => hWW' (hbW hq)
  have hrange : Set.range (y b) ⊆ Set.range W'.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨q, rfl⟩
    exact hW' (show q ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  let y₀ : Sp ℂ ⟶ W'.toScheme := IsOpenImmersion.lift W'.ι (y b) hrange
  have e₀ : y₀ ≫ W'.ι = y b := IsOpenImmersion.lift_fac _ _ _
  let yy : Sp ℂ ⟶ Xo.XF c := y₀ ≫ jW
  have hyj : yy ≫ Y.j = y b ≫ π := by
    show (y₀ ≫ jW) ≫ Y.j = _
    rw [Category.assoc, hj, ← Category.assoc, e₀]
  have hys : yy ≫ pullback.snd _ _ = spMap σ := by
    show (y₀ ≫ jW) ≫ _ = _
    rw [Category.assoc, hjs, ← Category.assoc, e₀, hyσ b hbB.1]
  obtain ⟨v, w, hfrvw, ⟨hvv, hww⟩, hFe⟩ := hF (y b) yy (hyσ b hbB.1) hbW hc hyj hys
  have hyf : yy ≫ Y.j = spMap f ≫ hA.fromSpec := hyj.trans hf.symm
  obtain ⟨u₁, hu₁⟩ := exists_vecs hA.fromSpec f (yy ≫ Y.j) hyf (fun i => MB.pt (e₁ i))
  obtain ⟨u₂, hu₂⟩ := exists_vecs hA.fromSpec f (yy ≫ Y.j) hyf (fun i => MB.pt (e₂ i))
  have hover : (yy ≫ Y.j) ≫ Y.s = spMap (σ.comp β) := by
    rw [hyj, Category.assoc, hπ, ← Category.assoc, hyσ b hbB.1, ← Spec.map_comp]
    rfl
  obtain ⟨hE₁, hE₂⟩ := heig f (yy ≫ Y.j) u₁ u₂ hyf hover hu₁ hu₂
  have hspec : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (yy ≫ Y.j) := by
    have e : centre (yy ≫ Y.j) = π (centre (y b)) := by
      rw [hyj]; rfl
    rw [e, ← RegAtDom.map_genPt hd]
    exact hc.map π.continuous
  obtain ⟨hV₁, hV₂⟩ := hval f (yy ≫ Y.j) u₁ u₂ hyf hspec hu₁ hu₂
  choose a₁ ha₁ using fun i => exists_sameVec_left Y yy (u₁ i)
  choose a₂ ha₂ using fun i => exists_sameVec_left Y yy (u₂ i)
  have hfr₀ : IsFramed Set.univ τ σ yy a₁ a₂ := GlobalTheory.T.vectors_at_complex_point E H D l Xo c O β Y τ σ yy a₁ a₂ u₁ u₂ hys ha₁ ha₂ hE₁ hE₂
  have h₁ := (hk hW') yy a₁ a₂ u₁ u₂ hyj hys ha₁ ha₂ hu₁ hu₂
  have hqA : ∀ q : Cpt (Z.ξ₀ ≫ Y.j), q.1 = centre (yy ≫ Y.j) → q.1 ∈ A := fun q hq => by
    rw [hq, hyf, ← SetLike.mem_coe, ← hA.range_fromSpec]
    exact ⟨_, rfl⟩
  have h₂ := GlobalTheory.T.pullback_frames_complex_point E H D l Xo c O β Y U Z τ σ Φ b₁ v₁ b₂ v₂ X' π ξ' (y b) yy v a₁ w a₂ α κ r hξ hgen hyj hΦ hfrvw hfr₀ hvv hww
    (fun i => ⟨_, hV₁ i, ha₁ i⟩) (fun j => ⟨_, hV₂ j, ha₂ j⟩) (fun q hq => hfr q (hqA q hq))
    (fun i => hs₁ ▸ Submodule.subset_span ⟨i, rfl⟩) (fun j => hs₂ ▸ Submodule.subset_span ⟨j, rfl⟩)
    hα hκ hαe hκe hr
  rw [hFe, h₂, h₁]

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameFunctionCompareStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_frame_function_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (Φ : CFn Xo c) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (X' : Scheme.{0}) (π : X' ⟶ Y.X) (s' : X' ⟶ Sp c.F) (d : ℕ) (ξ' : Sp Z.Ω ⟶ X') (W' W : X'.Opens) (jW : W'.toScheme ⟶ Xo.XF c) (F : (Sp ℂ ⟶ X') → ℂ), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → 1 ≤ D.p + D.q → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → IsUnitAn τ σ Φ → LinearIndependent Z.Ω b₁ → Submodule.span Z.Ω (Set.range b₁) = eigSp Z.ρ (Z.inc.comp (tauIn c τ)) → LinearIndependent Z.Ω b₂ → Submodule.span Z.Ω (Set.range b₂) = eigSp Z.ρ (Z.inc.comp (tauIn c (ComplexEmbedding.conjugate τ))) → π ≫ Y.s = s' ≫ spMap β → SmoothOfRelativeDimension d s' → Geo.ResK.HasSncCoords s' d (W' : Set X')ᶜ → ξ' ≫ π = Z.ξ₀ ≫ Y.j → IsCptGen ξ' → jW ≫ Y.j = W'.ι ≫ π → jW ≫ pullback.snd _ _ = W'.ι ≫ s' → W ≤ W' → (∀ (y' : Sp ℂ ⟶ X') (y : Sp ℂ ⟶ Xo.XF c), y' ≫ s' = spMap σ → ⊤ ≤ y' ⁻¹ᵁ W → genPt ξ' ⤳ centre y' → y ≫ Y.j = y' ≫ π → y ≫ pullback.snd _ _ = spMap σ → ∃ (v : Vecs y D.p) (w : Vecs y D.q), IsFramed Set.univ τ σ y v w ∧ ((∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w') ∧ F y' = Φ y v w) → (∀ p : Cpt ξ', p.1 ∈ W → ((lineLat (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q (exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂)).pull ξ' π (AddMonoidHom.id _)).IsGenAt p 1) → ∀ (x : Sp ℂ ⟶ X') (h : genPt ξ' ⤳ centre x), x ≫ s' = spMap σ → ∃ t : Z.Ω, ((lineLat (Z.eig τ) (Z.eig (ComplexEmbedding.conjugate τ)) D.p D.q (exteriorPower.ιMulti Z.Ω D.p b₁) (exteriorPower.ιMulti Z.Ω D.q b₂)).pull ξ' π (AddMonoidHom.id _)).IsGenAt ⟨centre x, h⟩ t ∧ ExtendsUnitAt s' σ ξ' W F t x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.extendsUnitAt_resolution | exact GlobalTheory.CompanionTheory.Ar.Flat.extendsUnitAt_resolution | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.extendsUnitAt_resolution <;> assumption)
end
