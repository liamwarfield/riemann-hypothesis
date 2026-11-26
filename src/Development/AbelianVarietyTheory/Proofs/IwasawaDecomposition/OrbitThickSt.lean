module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentEqScaleAtResidueChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PtOfFrameEqOfPointEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCharacterRestrictionTraitSurjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OrbitThickSt
noncomputable section

namespace GlobalTheory.CuspFrom

section Analytic

open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD

def FlowMajSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
    (∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, ∀ s : X.Ψ → ℂ, X.flow ξ s x ∈ X.dom → ∀ (τ : X.Ψ) (v : Fin r → ℂ),
      hermC τ.1 X.Gm v (Data.emb τ.1 ξ) = 0 →
      X.maj (X.flow ξ s x) τ v = X.maj x τ v +
        ‖X.Hf x τ v (Data.emb τ.1 ξ) / X.Hf x τ (Data.emb τ.1 ξ) (Data.emb τ.1 ξ)‖ ^ 2 *
          (X.maj (X.flow ξ s x) τ (Data.emb τ.1 ξ) - X.maj x τ (Data.emb τ.1 ξ))) ∧
    ∀ x ∈ X.dom, ∀ (τ : X.Ψ) (v w : Fin r → ℂ),
      ‖hermC τ.1 X.Gm v w‖ ^ 2 ≤ X.maj x τ v * X.maj x τ w ∧ ‖X.Hf x τ v w‖ ^ 2 ≤ X.maj x τ v * X.maj x τ w

def OrbitThickSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (ξ : Fin r → E), X.IsIso ξ →
    ∀ x ∈ X.dom, ∃ ε : ℝ, 0 < ε ∧ ∀ s : X.Ψ → ℂ, X.flow ξ s x ∈ X.dom →
      ∏ τ, X.tt ξ (X.flow ξ s x) τ = ∏ τ, X.tt ξ x τ → ε ≤ X.la1 (X.flow ξ s x)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

def ThickBdd (φ : Frame X.Ψ r → ℝ) : Prop := ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ x ∈ X.dom, ε ≤ X.la1 x → φ x ≤ C

def FreqNonneg (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) : Prop :=
  ∀ ξ, X.IsIso ξ → ∀ (ν : X.Ψ → ℝ), ∀ x ∈ X.dom, X.fj la ξ ν P x ≠ 0 → ∀ τ, 0 ≤ ν τ

def StepBound (w : ℝ) (φ : Frame X.Ψ r → ℝ) : Prop :=
  ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom, ∀ q : X.Ψ → ℝ, (∀ τ, 0 < q τ ∧ q τ ≤ 1) → ∀ B : ℝ,
    (∀ s : X.Ψ → ℝ, φ (X.flow ξ (fun τ => (s τ : ℂ) + I * (((q τ - 1) * X.tt ξ x τ : ℝ) : ℂ)) x) ≤ B) →
    φ x ≤ B * ∏ τ, q τ ^ (-w)

end Analytic

section Geometric

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.ArcQ GlobalTheory.Toroidal GlobalTheory.ShFam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

def FlowTie {σ : c.F →+* ℂ} {r : ℕ} {U : Formalism.L2.PjFree.Unf Xo c σ r} [Algebra (FractionRing ℂ) ℂ] (Uw : UnfWit U)
    {O : Type} [CommRing O] {β : O →+* c.F} (a : ArcIn Dw l β ℂ (σ.comp β)) (k : U.Comp) (ξ' : Fin r → E)
    (x : Frame (U.X k).Ψ r) : Prop :=
  ∀ (Y : Model Xo c β) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : Wit Y a χ) (Ha : HolArc Y σ a χ W Uw.F),
    ∃ (T : ℝ) (s : (U.X k).Ψ → ℂ) (d : (U.X k).Ψ → ℝ) (z : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Fin Uw.g → ℂ)),
      (∀ τ, 0 < d τ) ∧ (∀ τ, LinearIndependent ℂ (z τ) ∧ ∀ i j, z τ i j ≠ 0 → (Uw.e j).1 = τ) ∧
      ∀ w : ℂ, T < w.im → ∃ hx : (U.X k).flow ξ' (fun τ => s τ + w * (d τ : ℂ)) x ∈ (U.X k).dom,
        AnLie Uw.F Ha.i (Ha.Pw w) (U.un k ⟨_, hx⟩) z

def BdExt {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {V K : Type} [CommRing V] [IsLocalRing V] [Field K]
    [Algebra V K] [Algebra c.F K] (φ : c.F →+* V) (y : FrPt Xo c K) : Prop :=
  ∃ (χ : Sp V ⟶ gen Z) (g : EigFrame Z φ (χ ≫ genι Z)), χ ≫ genStr Z = spMap φ ∧
    GlobalTheory.AllWt.ptF y ≫ Z.jQ = spMap (algebraMap V K) ≫ χ ∧
    (∀ τ i, ∃ w : Sp (DualNumber K) ⟶ Z.oF.t.G.left,
      w ≫ Z.oF.t.G.hom = spMap (algebraMap K (DualNumber K)) ≫ GlobalTheory.AllWt.ptF y ∧
      w ≫ Z.m0.toSABMap.φ = y.u τ i ∧ w ≫ Z.m.φ = spMap (dualMap (algebraMap V K)) ≫ g.v τ i) ∧
    χ (IsLocalRing.closedPoint V) ∈ genBd Z

end Geometric

end GlobalTheory.CuspFrom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegers
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.FlagTan

namespace GlobalTheory.ShFam

instance mono_spMap_ringOfIntegers (K : Type) [Field K] [NumberField K] : Mono (spMap (algebraMap (𝓞 K) K)) :=
  have := IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 K)) (S := K)
  inferInstance

namespace Descent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem sp_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

section Move

variable {A B T : Type} [CommRing A] [Algebra c.F A] [CommRing B] [Algebra c.F B] [CommRing T] [Algebra c.F T]

theorem ptF_fst (P : FrPt Xo c A) : GlobalTheory.AllWt.ptF P ≫ pullback.fst _ _ = P.x := pullback.lift_fst _ _ _

theorem ptF_snd (P : FrPt Xo c A) : GlobalTheory.AllWt.ptF P ≫ pullback.snd _ _ = spMap (algebraMap c.F A) :=
  pullback.lift_snd _ _ _

theorem ptF_map {φ : A →ₐ[c.F] B} {P : FrPt Xo c A} {Q : FrPt Xo c B} (h : Q.x = spMap φ.toRingHom ≫ P.x) :
    GlobalTheory.AllWt.ptF Q = spMap φ.toRingHom ≫ GlobalTheory.AllWt.ptF P := by
  apply pullback.hom_ext
  · rw [Category.assoc, ptF_fst, ptF_fst, h]
  · rw [Category.assoc, ptF_snd, ptF_snd, sp_comp]
    exact congrArg spMap φ.comp_algebraMap.symm

def umap (φ : A →ₐ[c.F] B) (t : Ix Dw → Aˣ) : Ix Dw → Bˣ := fun i => Units.map (φ : A →* B) (t i)

theorem frBor_one (P : FrPt Xo c A) : FrBor 1 P P :=
  ((frBor_calculus E H Dw l Xo c A P P P).1 1).2 ⟨fun _ => 1, fun _ _ _ h => Matrix.one_apply_ne h.ne,
    fun _ _ => Matrix.one_apply_eq _, (frChg_refl_and_comp E H Dw l Xo c A P P P).1⟩

def BM (φ : A →ₐ[c.F] B) (t : Ix Dw → Bˣ) (P : FrPt Xo c A) (Q : FrPt Xo c B) : Prop :=
  ∃ P', FrMap φ P P' ∧ FrBor t P' Q

theorem BM.of_frBor {t : Ix Dw → Aˣ} {P Q : FrPt Xo c A} (h : FrBor t P Q) : BM (AlgHom.id _ _) t P Q :=
  ⟨P, frMap_id P, h⟩

theorem BM.x_eq {φ : A →ₐ[c.F] B} {t : Ix Dw → Bˣ} {P : FrPt Xo c A} {Q : FrPt Xo c B} (h : BM φ t P Q) :
    Q.x = spMap φ.toRingHom ≫ P.x := by
  obtain ⟨P', h1, h2⟩ := h
  exact h2.1.trans h1.1

end Move

section Dict

variable {S T : Type} [CommRing S] [CommRing T]


attribute [local instance] Over.cartesianMonoidalCategory in
open GlobalTheory.Exist.FlagBaseChange MonObj in
theorem sab_dict {X X' : Scheme.{0}} {t' : SAB H X'} {t : SAB H X} {f : X' ⟶ X} (m : SABMap t' t f) {x' : Sp S ⟶ X'}
    {x : Sp S ⟶ X} (hx : x' ≫ f = x) :
    (∀ v : Sp (DualNumber S) ⟶ t.G.left, v ≫ t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x →
      ∃ w, w ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x' ∧ w ≫ m.φ = v) ∧
    (∀ w : Sp (DualNumber S) ⟶ t'.G.left, w ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x' →
      (IsTanAtG t x (w ≫ m.φ) ↔ IsTanAtG t' x' w) ∧ ∀ χ : 𝓞 E → S,
        (∀ a, (w ≫ m.φ) ≫ (t.act.act a).left = spMap (epsMul (χ a)) ≫ w ≫ m.φ) ↔
          ∀ a, w ≫ (t'.act.act a).left = spMap (epsMul (χ a)) ≫ w) ∧
    ∀ (n : ℕ) (w : Fin n → (Sp (DualNumber S) ⟶ t'.G.left)) (a : Fin n → S) (w' : Sp (DualNumber S) ⟶ t'.G.left),
      (∀ i, w i ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x') →
      w' ≫ t'.G.hom = spMap (algebraMap S (DualNumber S)) ≫ x' →
      (IsCombAtG t x (fun i => w i ≫ m.φ) a (w' ≫ m.φ) ↔ IsCombAtG t' x' w a w') := by
  obtain ⟨B, hB, h1, h2, h3⟩ := exists_tangentEquiv m.cart t'.act.act t.act.act m.act x' x hx
  refine ⟨fun v hv => ?_, fun w hw => ⟨?_, fun χ => ?_⟩, fun n w a w' hw hw' => ?_⟩
  · obtain ⟨w, e⟩ := B.surjective (Over.homMk v hv)
    exact ⟨w.left, Over.w w, (hB w).symm.trans (congrArg (fun u => u.left) e)⟩
  · have := h1 (Over.homMk w hw)
    unfold TanAt at this
    rw [hB] at this
    have e := Over.w (B (Over.homMk w hw))
    rw [hB] at e
    exact (and_iff_right e).trans (this.trans (and_iff_right hw).symm)
  · have := h2 χ (Over.homMk w hw)
    unfold EigAt at this
    simp only [Over.comp_left, hB] at this
    exact this
  · have := h3 n (fun i => Over.homMk (w i) (hw i)) a (Over.homMk w' hw')
    unfold CombAt at this
    simp only [hB, Over.OverMorphism.ext_iff] at this
    unfold IsCombAtG
    simp only [eq_comm (b := w'), eq_comm (b := w' ≫ m.φ)]
    exact this

variable {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)

def TanRel (xF : Sp S ⟶ Xo.XF c) (u : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (v : Sp (DualNumber S) ⟶ Z.t.G.left) : Prop :=
  ∃ w : Sp (DualNumber S) ⟶ Z.oF.t.G.left, w ≫ Z.oF.t.G.hom = spMap (algebraMap S (DualNumber S)) ≫ xF ∧
    w ≫ Z.m0.toSABMap.φ = u ∧ w ≫ Z.m.φ = v

variable {Z} {xF : Sp S ⟶ Xo.XF c} {x₀ : Sp S ⟶ Xo.X} {x : Sp S ⟶ Z.X}

theorem TanRel.map (ψ : S →+* T) {u v} (h : TanRel Z xF u v) :
    TanRel Z (spMap ψ ≫ xF) (spMap (dualMap ψ) ≫ u) (spMap (dualMap ψ) ≫ v) := by
  obtain ⟨w, h1, rfl, rfl⟩ := h
  refine ⟨spMap (dualMap ψ) ≫ w, ?_, Category.assoc _ _ _, Category.assoc _ _ _⟩
  rw [Category.assoc, h1, ← Category.assoc, ← Category.assoc, sp_comp, sp_comp]
  congr 2
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_tanRel_right (h₀ : xF ≫ pullback.fst _ _ = x₀) {u} (hu : IsTanAt x₀ u) : ∃ v, TanRel Z xF u v := by
  obtain ⟨w, h1, h2⟩ := (sab_dict Z.m0.toSABMap h₀).1 u hu.1
  exact ⟨_, w, h1, h2, rfl⟩

theorem exists_tanRel_left (hx : xF ≫ Z.j = x) {v} (hv : IsTanAtG Z.t x v) : ∃ u, TanRel Z xF u v := by
  obtain ⟨w, h1, h2⟩ := (sab_dict Z.m hx).1 v hv.1
  exact ⟨_, w, h1, rfl, h2⟩

theorem TanRel.tan_iff (h₀ : xF ≫ pullback.fst _ _ = x₀) (hx : xF ≫ Z.j = x) {u v} (h : TanRel Z xF u v) :
    IsTanAt x₀ u ↔ IsTanAtG Z.t x v := by
  obtain ⟨w, h1, rfl, rfl⟩ := h
  exact ((sab_dict Z.m0.toSABMap h₀).2.1 w h1).1.trans ((sab_dict Z.m hx).2.1 w h1).1.symm

theorem TanRel.eig_iff {u v} (h : TanRel Z xF u v) (χ : 𝓞 E → S) :
    (∀ a, u ≫ (Xo.univ.t.act.act a).left = spMap (epsMul (χ a)) ≫ u) ↔
      ∀ a, v ≫ (Z.t.act.act a).left = spMap (epsMul (χ a)) ≫ v := by
  obtain ⟨w, h1, rfl, rfl⟩ := h
  exact (((sab_dict Z.m0.toSABMap rfl).2.1 w h1).2 χ).trans (((sab_dict Z.m rfl).2.1 w h1).2 χ).symm

theorem TanRel.comb_iff (h₀ : xF ≫ pullback.fst _ _ = x₀) (hx : xF ≫ Z.j = x) {n : ℕ} {u v u' v'}
    (h : ∀ i : Fin n, TanRel Z xF (u i) (v i)) (h' : TanRel Z xF u' v') (a : Fin n → S) :
    IsCombAt x₀ u a u' ↔ IsCombAtG Z.t x v a v' := by
  choose w h1 h2 h3 using h
  obtain ⟨w', k1, rfl, rfl⟩ := h'
  obtain rfl : u = _ := (funext h2).symm
  obtain rfl : v = _ := (funext h3).symm
  exact ((sab_dict Z.m0.toSABMap h₀).2.2 n w a w' h1 k1).trans ((sab_dict Z.m hx).2.2 n w a w' h1 k1).symm

variable [Algebra c.F S] [Algebra c.F T]

def Comparison₂ (P : FrPt Xo c S) {φ : c.F →+* S} {x : Sp S ⟶ Z.X} (g : EigFrame Z φ x) : Prop :=
  φ = algebraMap c.F S ∧ GlobalTheory.AllWt.ptF P ≫ Z.j = x ∧ ∀ τ i, TanRel Z (GlobalTheory.AllWt.ptF P) (P.u τ i) (g.v τ i)

theorem exists_tie_frame (P : FrPt Xo c S) (hx : GlobalTheory.AllWt.ptF P ≫ Z.j = x) :
    ∃ g : EigFrame Z (algebraMap c.F S) x, Comparison₂ P g := by
  choose v hv using fun τ i => exists_tanRel_right (Z := Z) (ptF_fst P) (P.tan τ i)
  refine ⟨⟨v, fun τ i => ((hv τ i).tan_iff (ptF_fst P) hx).1 (P.tan τ i), fun τ i => ((hv τ i).eig_iff _).1 (P.eig τ i),
    fun τ w hw he => ?_⟩, rfl, hx, hv⟩
  obtain ⟨u, hu⟩ := exists_tanRel_left hx hw
  exact (existsUnique_congr fun a => TanRel.comb_iff (ptF_fst P) hx (hv τ) hu a).1
    (P.basis τ u ((hu.tan_iff (ptF_fst P) hx).2 hw) ((hu.eig_iff _).2 he))

theorem Comparison₂.tri_of_bm {P : FrPt Xo c S} {Q : FrPt Xo c T} {φ : c.F →+* S} {φ' : c.F →+* T} {x' : Sp T ⟶ Z.X}
    {f : EigFrame Z φ x} {g : EigFrame Z φ' x'} (hf : Comparison₂ P f) (hg : Comparison₂ Q g) {ψ : S →ₐ[c.F] T} {t : Ix Dw → Tˣ}
    (h : BM ψ t P Q) : f.Tri ψ.toRingHom g fun τ i => t (some ⟨τ, i⟩) := by
  have e := ptF_map h.x_eq
  obtain ⟨P', h1, h2⟩ := h
  refine ⟨by rw [← hg.2.1, e, Category.assoc, hf.2.1], by rw [hg.1, hf.1]; exact ψ.comp_algebraMap.symm, fun τ i => ?_⟩
  obtain ⟨cf, c1, c2, c3⟩ := h2.2.1 τ i
  refine ⟨cf, c1, c2, (TanRel.comb_iff ((ptF_fst Q).trans h2.1) hg.2.1 (fun k => ?_) (hg.2.2 τ i) cf).1 c3⟩
  rw [e, h1.2.1]
  exact (hf.2.2 τ k).map _

end Dict

end Descent

end GlobalTheory.ShFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmplePointsLocalizedModel
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Models GlobalTheory.TorRef

namespace GlobalTheory.TorRef.DomFine

theorem generalizing_of_stalk {Y : Scheme.{0}} {A : Type} [CommRing A] [IsLocalRing A] (ξ : Sp A ⟶ Y)
    (hf : (Scheme.stalkClosedPointTo ξ).hom.Flat) : GeneralizingMap ξ := by
  have h₁ : Flat (Spec.map (Scheme.stalkClosedPointTo ξ)) := by
    rw [Flat.SpecMap_iff]; exact hf
  have h₂ : GeneralizingMap (Y.fromSpecStalk (ξ (closedPoint _))) := by
    refine (Y.fromSpecStalk (ξ (closedPoint _))).isEmbedding.isInducing.generalizingMap ?_
    rw [Scheme.range_fromSpecStalk]
    exact fun a b hab hb => hab.trans hb
  have e : (ξ : Sp A → Y) = Y.fromSpecStalk (ξ (closedPoint _)) ∘ Spec.map (Scheme.stalkClosedPointTo ξ) := by
    funext p
    conv_lhs => rw [← Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ]
    exact Scheme.Hom.comp_apply _ _ _
  rw [e]
  exact (Flat.generalizingMap _).comp h₂

theorem eq_of_specializes {Y : Scheme.{0}} {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A] (ξ : Sp A ⟶ Y)
    (hf : (Scheme.stalkClosedPointTo ξ).hom.Flat) (w : Sp (FractionRing A)) (q : Y) (h : q ⤳ (jK A ≫ ξ) w) :
    q = (jK A ≫ ξ) w := by
  rw [Scheme.Hom.comp_apply] at h ⊢
  obtain ⟨r, hr, rfl⟩ := generalizing_of_stalk ξ hf h
  have hw : (jK A w).asIdeal = ⊥ := by
    haveI : (PrimeSpectrum.asIdeal w).IsPrime := PrimeSpectrum.isPrime w
    have hw₀ : PrimeSpectrum.asIdeal w = ⊥ := Ideal.eq_bot_of_prime _
    ext x
    change algebraMap A (FractionRing A) x ∈ PrimeSpectrum.asIdeal w ↔ _
    rw [hw₀, Ideal.mem_bot, Ideal.mem_bot]
    exact map_eq_zero_iff _ (IsFractionRing.injective A (FractionRing A))
  have hle := (PrimeSpectrum.le_iff_specializes (R := A) r (jK A w)).mpr hr
  have : r = jK A w := by
    apply le_antisymm hle
    change (jK A w).asIdeal ≤ PrimeSpectrum.asIdeal r
    rw [hw]; exact bot_le
  rw [this]

theorem mem_range_of_generic {U V : Scheme.{0}} (j : U ⟶ V) [IsOpenImmersion j] (hd : Dense (Set.range j))
    [TopologicalSpace.NoetherianSpace V] (g : V) (hg : ∀ q : V, q ⤳ g → q = g) : g ∈ Set.range j := by
  have hc : closure {g} ∈ irreducibleComponents V := by
    refine ⟨isIrreducible_singleton.closure, fun S hS hle => ?_⟩
    have hq := hS.isGenericPoint_genericPoint_closure
    have hgS : g ∈ S := hle (subset_closure rfl)
    have e := hg _ (hq.specializes (subset_closure hgS))
    rw [e] at hq
    exact subset_closure.trans hq.def.symm.subset
  obtain ⟨o, ho, hne, hle⟩ := TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent _ hc
  obtain ⟨u, hu, hu'⟩ := hd.inter_open_nonempty o ho hne
  have hs : g ⤳ u := specializes_iff_mem_closure.2 (hle hu)
  exact j.isOpenEmbedding.isOpen_range.stableUnderGeneralization hs hu'

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem injective_of_flat {O A : Type} [CommRing O] [IsDomain O] [CommRing A] [IsDomain A] [IsLocalRing A]
    {X : Scheme.{0}} (s : X ⟶ Sp O) (hs : Flat s) (ξ₀ : Sp A ⟶ X) (hfl : (Scheme.stalkClosedPointTo ξ₀).hom.Flat)
    (κ : O →+* A) (hκ : spMap κ = ξ₀ ≫ s) : Function.Injective ((algebraMap A (FractionRing A)).comp κ) := by
  have hsρ : spMap ((algebraMap A (FractionRing A)).comp κ) = (jK A ≫ ξ₀) ≫ s := by
    rw [← spMap_comp', hκ, Category.assoc]
  refine GlobalTheory.GenericFlat.injective_of_apply_eq_genericPoint _ (⊥ : PrimeSpectrum (FractionRing A)) ?_
  obtain ⟨y, hy, e⟩ := Flat.generalizingMap s
    (genericPoint_specializes (s ((jK A ≫ ξ₀) (⊥ : PrimeSpectrum (FractionRing A)))))
  have h := eq_of_specializes ξ₀ hfl (⊥ : PrimeSpectrum (FractionRing A)) y hy
  rw [hsρ]
  refine (Scheme.Hom.comp_apply (jK A ≫ ξ₀) s _).trans ?_
  rw [← h, e]

theorem exists_lift_frac {O F B : Type} [CommRing O] [IsDomain O] [Field F] [Algebra O F] [IsFractionRing O F] [CommRing B]
    (g : O →+* B) (hu : ∀ y : O, y ≠ 0 → IsUnit (g y)) : ∃ ρ : F →+* B, ρ.comp (algebraMap O F) = g := by
  have hu' : ∀ y : nonZeroDivisors O, IsUnit (g y) := fun y => hu _ (nonZeroDivisors.ne_zero y.2)
  exact ⟨IsLocalization.lift hu', IsLocalization.lift_comp hu'⟩

theorem exists_generic_fibre {O F A : Type} [CommRing O] [IsDomain O] [Field F] [Algebra O F] [IsFractionRing O F]
    [CommRing A] [IsDomain A] [IsLocalRing A] {X : Scheme.{0}} (s : X ⟶ Sp O) (hs : Flat s) (ξ₀ : Sp A ⟶ X)
    (hfl : (Scheme.stalkClosedPointTo ξ₀).hom.Flat) :
    ∃ v : Sp (FractionRing A) ⟶ pullback s (spMap (algebraMap O F)), v ≫ pullback.fst _ _ = jK A ≫ ξ₀ := by
  obtain ⟨κ', hκ'⟩ := Spec.map_surjective (ξ₀ ≫ s)
  obtain ⟨κ, rfl⟩ : ∃ κ : O →+* A, CommRingCat.ofHom κ = κ' := ⟨κ'.hom, rfl⟩
  have hκ : spMap κ = ξ₀ ≫ s := hκ'
  have hρ := injective_of_flat s hs ξ₀ hfl κ hκ
  obtain ⟨ρ', hρ'⟩ := exists_lift_frac (F := F) ((algebraMap A (FractionRing A)).comp κ) (fun y hy => by
    have h0 : κ y ≠ 0 := fun h => hy (hρ (by simp [h]))
    exact IsLocalization.map_units (FractionRing A) (⟨κ y, mem_nonZeroDivisors_of_ne_zero h0⟩ : nonZeroDivisors A))
  have hv : (jK A ≫ ξ₀) ≫ s = spMap ρ' ≫ spMap (algebraMap O F) := by
    rw [spMap_comp', hρ', ← spMap_comp', hκ, Category.assoc]
  exact ⟨pullback.lift (jK A ≫ ξ₀) _ hv, pullback.lift_fst _ _ _⟩

theorem exists_generic_point (O F : Type) [CommRing O] [IsDedekindDomain O] [Field F] [Algebra O F] [IsFractionRing O F]
    (X U : Scheme.{0}) (s : X ⟶ Sp O) (jQ : U ⟶ pullback s (spMap (algebraMap O F))) (hs : Flat s) (hp : IsProjOver s)
    (hj : IsOpenImmersion jQ) (hd : Dense (Set.range jQ)) {A : Type} [CommRing A] [IsDomain A] [IsLocalRing A]
    (ξ₀ : Sp A ⟶ X) (hfl : (Scheme.stalkClosedPointTo ξ₀).hom.Flat) :
    ∃ y : Sp (FractionRing A) ⟶ U, y ≫ jQ ≫ pullback.fst _ _ = jK A ≫ ξ₀ := by
  obtain ⟨v, v1⟩ := exists_generic_fibre (F := F) s hs ξ₀ hfl
  obtain ⟨hN, hC, -⟩ := GlobalTheory.genericPart_dense_proOpen O F X U s jQ hs hp hj hd
  haveI : IsNoetherian X := {}
  have hb0 : IsPreimmersion (spMap (algebraMap O F)) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of O) (S := F) (nonZeroDivisors O)
  haveI h1 : IsPreimmersion (pullback.fst s (spMap (algebraMap O F))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb0
  haveI hNs : TopologicalSpace.NoetherianSpace ↥(pullback s (spMap (algebraMap O F))) :=
    (pullback.fst s (spMap (algebraMap O F))).isEmbedding.isInducing.noetherianSpace
  have hr : Set.range v ⊆ Set.range jQ := by
    rintro _ ⟨w, rfl⟩
    refine mem_range_of_generic jQ hd _ fun q hq => ?_
    have h' := hq.map (pullback.fst s (spMap (algebraMap O F))).continuous
    have e : (pullback.fst s (spMap (algebraMap O F))) (v w) = (jK A ≫ ξ₀) w := by
      rw [← Scheme.Hom.comp_apply, v1]
    rw [e] at h'
    exact (pullback.fst s (spMap (algebraMap O F))).isEmbedding.injective ((eq_of_specializes ξ₀ hfl w _ h').trans e.symm)
  refine ⟨IsOpenImmersion.lift jQ v hr, ?_⟩
  rw [← Category.assoc, IsOpenImmersion.lift_fac, v1]

end GlobalTheory.TorRef.DomFine
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SvalUpSec
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorRef

def upSec {S : Scheme.{0}} (G : Over S) {L : LB G.left} {k : ℕ} (σ : H0 L k) :
    LB.Sec (LPow G L (k : ℤ) (Over.mk (𝟙 S))) :=
  GlobalTheory.VVRank.pullTo σ (snd (Over.mk (𝟙 S)) G).left (fun _ => Category.comp_id _)

end GlobalTheory.TorRef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatDRSubsetLatHT
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.Pad

theorem latDR_subset_latHT :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (p : ℕ) (x : Sp C ⟶ X), latDR t x ⊆ latHT t p x := by
  intro E _ _ _ H X t C _ _ p x v hv
  obtain ⟨xO, hx, vO, htan, hvO⟩ := hv
  have h1 : epsMul (1 : C) = RingHom.id (DualNumber C) := by
    ext a <;> simp [epsMul]
  have h2 : spMap (RingHom.id (DualNumber C)) = 𝟙 _ := by
    simp [spMap]
  refine ⟨xO, hx, 0, vO, htan, ?_, ?_⟩
  · rw [pow_zero, h1, h2, Category.id_comp, hvO]
  · intro n c g _
    rw [pow_zero, Ideal.span_singleton_one]
    exact Submodule.mem_top

end GlobalTheory.ShFam.Pad
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ForcedContentEqClosedContentNumericalDatum
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Top.Bl

theorem forcedContent_eq_closedContent_numericalDatum : ∀ (D : D7) (L : SizeData₂ D) (Del h0 : ℕ), DV.KapDef D →
    ∀ (y : HeightOneSpectrum (𝓞 D.what₂.LL)) (j : Fin D.R.m),
      GlobalTheory.Mem.Top.Bl.F0K L.sc D y j = (ofRecord D L Del h0).Fj (j.1 + 1) y :=
  fun D L Del h0 hK y j => (ofRecord_Fj_succ D L Del h0 hK y j).symm

end GlobalTheory.Mem.Top.Bl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DomainPointStabilizerTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDetNeZeroFirstCol
namespace GlobalTheory.FirstColumnConjugation

open Matrix

theorem exists_det_ne_zero_first_col {n : ℕ} (v : Fin (n + 1) → ℂ) (hv : v ≠ 0) :
    ∃ P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, P.det ≠ 0 ∧ ∀ k, P k 0 = v k := by
  obtain ⟨k₀, hk₀⟩ := Function.ne_iff.1 hv
  let u : Fin (n + 1) → ℂ := v - Pi.single k₀ (1 : ℂ)
  let Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
    1 + replicateCol Unit u * replicateRow Unit (Pi.single k₀ (1 : ℂ))
  have hQdet : Q.det = v k₀ := by
    simp only [Q]
    rw [det_one_add_replicateCol_mul_replicateRow]
    simp [u]
  have hQcol : ∀ k, Q k k₀ = v k := by
    intro k
    simp only [Q, u]
    by_cases h : k = k₀ <;> simp [Matrix.mul_apply, Matrix.one_apply, Pi.single_apply, h]
  refine ⟨Q.submatrix id (Equiv.swap 0 k₀), ?_, fun k => ?_⟩
  · rw [det_permute', hQdet]
    exact mul_ne_zero (by simp) hk₀
  · simp [hQcol]

theorem exists_conj_first_col_zero {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∃ (P : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ),
      Matrix.det P ≠ 0 ∧ (∀ a : Fin n, B (Fin.succ a) 0 = 0) ∧ A * P = P * B := by
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue (Matrix.toLin' A)
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hAv : A *ᵥ v = μ • v := by
    have h := Module.End.mem_eigenspace_iff.1 hv.1
    rwa [Matrix.toLin'_apply] at h
  obtain ⟨P, hP, hPv⟩ := exists_det_ne_zero_first_col v hv.2
  have hu : IsUnit P := (Matrix.isUnit_iff_isUnit_det P).2 (Ne.isUnit hP)
  refine ⟨P, P⁻¹ * A * P, hP, fun a => ?_, ?_⟩
  · have hPe : P *ᵥ Pi.single 0 1 = v := by
      ext k
      rw [mulVec_single_one]
      exact hPv k
    have hcol : (P⁻¹ * A * P) *ᵥ Pi.single 0 1 = μ • Pi.single 0 1 := by
      rw [← mulVec_mulVec, hPe, ← mulVec_mulVec, hAv, mulVec_smul, ← hPe, mulVec_mulVec,
        Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det P).1 hu), one_mulVec]
    have h := congrFun hcol (Fin.succ a)
    rw [mulVec_single_one] at h
    simpa [Pi.single_apply, Fin.succ_ne_zero] using h
  · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det P).1 hu),
      Matrix.one_mul]

end GlobalTheory.FirstColumnConjugation
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DomainPointStabilizerTrivial
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FreeOnDomain

theorem exists_conj_first_col {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ∃ P B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, P.det ≠ 0 ∧ (∀ a : Fin n, B a.succ 0 = 0) ∧ A * P = P * B := by
  first
  | exact @_root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero
  | exact _root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero
  | (apply _root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero <;> assumption)
  | (intros; apply _root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FirstColumnConjugation.exists_conj_first_col_zero ..)

theorem exists_conj_triangular (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ P T : Matrix (Fin n) (Fin n) ℂ, P.det ≠ 0 ∧ (∀ a c, c < a → T a c = 0) ∧ A * P = P * T := by
  induction n with
  | zero => exact ⟨1, 1, by simp, fun a => a.elim0, Subsingleton.elim _ _⟩
  | succ n ih =>
    obtain ⟨P, B, hP, hB, e⟩ := exists_conj_first_col A
    obtain ⟨Q, T, hQ, hT, e'⟩ := ih (B.submatrix Fin.succ Fin.succ)
    let D : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
      of (Fin.cons (Fin.cons 1 fun _ => 0) fun a => Fin.cons 0 (Q a))
    let T' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
      of (Fin.cons ((B * D) 0) fun a => Fin.cons 0 (T a))
    have hD : D.det = Q.det := by
      rw [det_succ_row_zero, Fin.sum_univ_succ]
      simp only [D, of_apply, Fin.cons_zero, Fin.cons_succ, mul_zero, zero_mul, Finset.sum_const_zero, add_zero,
        Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero]
      rfl
    have hBD : B * D = D * T' := by
      ext a c
      refine Fin.cases ?_ (fun a => ?_) a
      · rw [Matrix.mul_apply (M := D), Fin.sum_univ_succ]
        simp [D, T']
      · refine Fin.cases ?_ (fun c => ?_) c
        · simp [D, T', Matrix.mul_apply, Fin.sum_univ_succ, hB]
        · have := congrFun (congrFun e' a) c
          simpa [D, T', Matrix.mul_apply, Fin.sum_univ_succ] using this
    refine ⟨P * D, T', ?_, fun a c h => ?_, ?_⟩
    · rw [det_mul, hD]; exact mul_ne_zero hP hQ
    · revert h
      refine Fin.cases ?_ (fun a => ?_) a
      · intro h; exact absurd h (by simp)
      · refine Fin.cases ?_ (fun c => ?_) c
        · intro _; simp [T']
        · intro h; simpa [T'] using hT a c (Fin.succ_lt_succ_iff.1 h)
    · rw [← Matrix.mul_assoc, e, Matrix.mul_assoc, hBD, Matrix.mul_assoc]

theorem toBlocks₁₂_eq_zero {p q : ℕ} {F F' : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ} (hF : IsUnit F.det)
    (h2 : IsUnit F.toBlocks₂₂.det) (h2' : IsUnit F'.toBlocks₂₂.det) (h : moeb F' 0 = moeb F 0) :
    (F⁻¹ * F').toBlocks₁₂ = 0 := by
  rw [moeb_zero, moeb_zero] at h
  have h1 : F'.toBlocks₁₂ = F.toBlocks₁₂ * (F.toBlocks₂₂⁻¹ * F'.toBlocks₂₂) := by
    rw [← Matrix.mul_assoc, ← h, nonsing_inv_mul_cancel_right _ _ h2']
  have e : F' * fromBlocks 0 0 0 1 =
      F * fromBlocks (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (F.toBlocks₂₂⁻¹ * F'.toBlocks₂₂) := by
    conv_lhs => rw [← fromBlocks_toBlocks F']
    conv_rhs => enter [1]; rw [← fromBlocks_toBlocks F]
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one, ← h1, mul_nonsing_inv_cancel_left _ _ h2]
  have e2 : (F⁻¹ * F') * fromBlocks 0 0 0 1 =
      fromBlocks (0 : Matrix (Fin p) (Fin p) ℂ) 0 0 (F.toBlocks₂₂⁻¹ * F'.toBlocks₂₂) := by
    rw [Matrix.mul_assoc, e, nonsing_inv_mul_cancel_left _ _ hF]
  rw [← fromBlocks_toBlocks (F⁻¹ * F'), fromBlocks_multiply] at e2
  simpa using congrArg toBlocks₁₂ e2

theorem exists_conj_block {r j : ℕ} (hj : j ≤ r) (M : Matrix (Fin r) (Fin r) ℂ)
    (hM : (reindex (idx hj) (idx hj) M).toBlocks₁₂ = 0) :
    ∃ b t : Matrix (Fin r) (Fin r) ℂ, b.det ≠ 0 ∧ (∀ a c : Fin r, (c : ℕ) < r - j → ¬ (a : ℕ) < r - j → b a c = 0) ∧
      (∀ a c, c < a → t a c = 0) ∧ M * b = b * t := by
  set G := reindex (idx hj) (idx hj) M with hG
  obtain ⟨P, T, hP, hT, e⟩ := exists_conj_triangular _ G.toBlocks₁₁
  obtain ⟨Q, S, hQ, hS, e'⟩ := exists_conj_triangular _ G.toBlocks₂₂
  have hm : G * fromBlocks P 0 0 Q = fromBlocks P 0 0 Q * fromBlocks T 0 (Q⁻¹ * (G.toBlocks₂₁ * P)) S := by
    conv_lhs => rw [← fromBlocks_toBlocks G, hM]
    rw [fromBlocks_multiply, fromBlocks_multiply]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, e, e', mul_nonsing_inv_cancel_left _ _ hQ.isUnit]
  refine ⟨(fromBlocks P 0 0 Q).submatrix (idx hj) (idx hj),
    (fromBlocks T 0 (Q⁻¹ * (G.toBlocks₂₁ * P)) S).submatrix (idx hj) (idx hj), ?_, fun a c hc ha => ?_,
    fun a c h => ?_, ?_⟩
  · rw [det_submatrix_equiv_self, det_fromBlocks_zero₁₂]; exact mul_ne_zero hP hQ
  · obtain ⟨a, rfl⟩ := (idx hj).symm.surjective a
    obtain ⟨c, rfl⟩ := (idx hj).symm.surjective c
    rcases a with a | a <;> rcases c with c | c
    · rw [idx_symm_inl] at hc; omega
    · simp
    · simp
    · rw [idx_symm_inr] at ha; exact absurd a.2 ha
  · obtain ⟨a, rfl⟩ := (idx hj).symm.surjective a
    obtain ⟨c, rfl⟩ := (idx hj).symm.surjective c
    rw [Fin.lt_def] at h
    rcases a with a | a <;> rcases c with c | c
    · rw [idx_symm_inl, idx_symm_inl] at h
      simpa using hT a c (by rw [Fin.lt_def]; omega)
    · simp
    · rw [idx_symm_inl, idx_symm_inr] at h
      have := a.2; omega
    · rw [idx_symm_inr, idx_symm_inr] at h
      simpa using hS a c h
  · have : M = G.submatrix (idx hj) (idx hj) := by simp [hG]
    rw [submatrix_mul_equiv, ← hm, ← submatrix_mul_equiv _ _ _ (idx hj), ← this]

theorem eq_one_of_domPt_lact_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, domPt X hj κ (lact γ x) = domPt X hj κ x → γ = 1 := by
  intro E _ _ _ r j X hj Tau _ κ hp γ hγ x hx h
  obtain ⟨x, ho, b₀, hb₀, rfl⟩ := ortho_holds r X x hx
  rw [KU.lact_rmul', domPt_rmul X hj κ hb₀, domPt_rmul X hj κ hb₀] at h
  have hx := IC.orth_mem_dom X ho
  have hx' := IC.orth_mem_dom X (KU.isOrth_lact X hγ ho)
  have key : ∀ τ : X.Ψ, ∃ b t : Matrix (Fin r) (Fin r) ℂ, b.det ≠ 0 ∧
      (∀ a c : Fin r, (c : ℕ) < r - j → ¬ (a : ℕ) < r - j → b a c = 0) ∧
      (∀ a c, c < a → t a c = 0) ∧ (mat x τ)⁻¹ * mat (lact γ x) τ * b = b * t := by
    intro τ
    refine exists_conj_block hj _ ?_
    obtain ⟨s, rfl⟩ := κ.surjective τ
    have u0 : IsUnit (mat (x0F X) (κ s)).det := (det_x0F X _).isUnit
    have hF : IsUnit (frameCo X hj x (κ s)).det := by
      rw [frameCo, det_reindex_self, det_mul]
      exact (isUnit_nonsing_inv_det _ u0).mul (hx _).1.isUnit
    have := toBlocks₁₂_eq_zero hF (frameCo_isUnit₂₂ X hj hp hx _) (frameCo_isUnit₂₂ X hj hp hx' _) (congrFun h s)
    rw [frameCo, frameCo, inv_reindex, Matrix.mul_inv_rev, nonsing_inv_nonsing_inv _ u0] at this
    simp only [reindex_apply, submatrix_mul_equiv] at this ⊢
    rwa [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ u0] at this
  choose b t hb hb0 ht e using key
  have e' : ∀ τ, mat (lact γ x) τ * b τ = mat x τ * b τ * t τ := fun τ => by
    rw [Matrix.mul_assoc, ← e, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ (hx τ).1.isUnit]
  refine X.Γ_free γ hγ (rmul x fun τ => b τ)
    (GlobalTheory.PointOfFrames.rmul_mem_dom X hx _ hb (by rw [hp]; exact hb0)) (fun τ => t τ) (fun τ => ⟨?_, ht τ⟩) ?_
  · intro h0
    have h1 := congrArg det (e' τ)
    have h0' : (t τ).det = 0 := h0
    rw [det_mul, det_mul, h0', mul_zero] at h1
    exact mul_ne_zero (hx' τ).1 (hb τ) h1
  · exact (KU.lact_rmul' X γ x _).trans (funext e')

end GlobalTheory.FreeOnDomain
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DomainPointStabilizerTrivialStatement
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.domain_point_stabilizer_trivial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r) (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, domPt X hj κ (lact γ x) = domPt X hj κ x → γ = 1 := by
  first | exact @GlobalTheory.FreeOnDomain.eq_one_of_domPt_lact_eq | exact GlobalTheory.FreeOnDomain.eq_one_of_domPt_lact_eq | (intros; apply GlobalTheory.FreeOnDomain.eq_one_of_domPt_lact_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerMapTie
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

namespace GlobalTheory.Mem.Col2.LowerTie

theorem lowerMap_tie : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (Ch : ℕ → Type) (chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i) (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → Formalism.L2.Rows.LowerMapTieS F :=
  fun I hO hP l Z u Ch chOf F hS =>
    fun _ ψ c P _ h => lowerMap_std I hO hP l Z u Ch chOf F hS ψ c P h

end GlobalTheory.Mem.Col2.LowerTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorBlockDecomposition
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorBlockDecomposition
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

namespace GlobalTheory.FlagFibre

theorem lminor_block : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ H : Matrix (Fin r) (Fin r) ℂ, IsUnit (reindex e e H).toBlocks₂₂.det → (∀ (i : Fin (r + 1)) (k : Fin (q + 1)), (i : ℕ) = k → lminor H i = lminor (reindex e e H).toBlocks₂₂ k) ∧ ∀ (i : Fin (r + 1)) (k : Fin (p + 1)), (i : ℕ) = q + k → lminor H i = (reindex e e H).toBlocks₂₂.det * lminor (schur (reindex e e H)) k := by
  intro r p q e he H hH
  constructor
  · rintro ⟨i, hi⟩ ⟨k, hk⟩ h
    obtain rfl : i = k := h
    unfold lminor
    congr 1
    ext a b
    simp only [submatrix_apply, toBlocks₂₂, reindex_apply, of_apply]
    congr 1 <;> exact Fin.ext (by rw [he.2]; rfl)
  · rintro ⟨i, hi⟩ ⟨k, hk⟩ h
    obtain rfl : i = q + k := h
    obtain ⟨f0, hf0⟩ := exists_isBlockOrderedSumEquiv k q
    let f : Fin (q + k) ≃ Fin k ⊕ Fin q := (finCongr (add_comm q k)).trans f0
    have hf : IsBlockSL2Embedding f := ⟨fun a => hf0.1 a, fun a => hf0.2 a⟩
    let c : Fin k → Fin p := Fin.castLE (Nat.le_of_lt_succ hk)
    let G : Matrix (Fin k ⊕ Fin q) (Fin k ⊕ Fin q) ℂ := (reindex e e H).submatrix (Sum.map c id) (Sum.map c id)
    have key : ∀ a, Fin.castLE (Nat.le_of_lt_succ hi) (f.symm a) = e.symm (Sum.map c id a) := by
      rintro (a | a) <;> apply Fin.ext
      · simp only [Fin.val_castLE, Sum.map_inl, hf.1, he.1, c]
      · simp only [Fin.val_castLE, Sum.map_inr, hf.2, he.2, id]
    have h1 : lminor H ⟨q + k, hi⟩ = G.det := by
      unfold lminor
      rw [← det_submatrix_equiv_self f.symm]
      congr 1
      ext a b
      simp only [G, submatrix_apply, reindex_apply, ← key]
    have h2 : G.toBlocks₂₂ = (reindex e e H).toBlocks₂₂ := rfl
    rw [h1, det_eq_mul_schur (h2 ▸ hH), h2]
    rfl

end GlobalTheory.FlagFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorBlockDecompositionStatement
open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leadingMinor_blockDecomposition : ∀ (r p q : ℕ) (e : Fin r ≃ Fin p ⊕ Fin q), IsBlockSL2Embedding e → ∀ H : Matrix (Fin r) (Fin r) ℂ, IsUnit (reindex e e H).toBlocks₂₂.det → (∀ (i : Fin (r + 1)) (k : Fin (q + 1)), (i : ℕ) = k → lminor H i = lminor (reindex e e H).toBlocks₂₂ k) ∧ ∀ (i : Fin (r + 1)) (k : Fin (p + 1)), (i : ℕ) = q + k → lminor H i = (reindex e e H).toBlocks₂₂.det * lminor (schur (reindex e e H)) k := by
  first | exact @GlobalTheory.FlagFibre.lminor_block | exact GlobalTheory.FlagFibre.lminor_block | (intros; apply GlobalTheory.FlagFibre.lminor_block <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LowerMapTwGen
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000

namespace GlobalTheory.Mem.Col2.LowerTie

theorem lowerMap_tw_gen {B : Base} {X : PreX B.toPre} (I : TC B X) (hO : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (l0 : I.Law0 l) {cf : Formalism.L2.Host.CharFrame (I.rec7 l Z)} {nch : NChoice (I.rec7 l Z)}
    {tp : Formalism.L2.Host.TupTied (I.rec7 l Z) cf nch} {C : ColsTiedSym (I.rec7 l Z)} {Tw : TwForms (I.rec7 l Z)}
    (t : SymmetricTwistedColumnsAtPrimes tp C Tw) (he : Tw = I.tw l l0 Z) (hC : I.StdC l Z C) (hTw : I.StdTw l Z l0 (he ▸ t))
    (u : (I.rec7 l Z).what₂.Word) (a : (I.rec7 l Z).what₂.Tup) (ha : a ≠ (I.rec7 l Z).what₂.mu0) (h1 : 1 ≤ (I.rec7 l Z).R.m) :
    IsUnit (Formalism.L2.Forms.bZ u (t.pt.til u a ha h1).z0).det → ∀ (ψ : ((I.rec7 l Z).PTw u a).Wz) (c : (Tw.fm u a).clsP)
      (P : MvPolynomial ((I.rec7 l Z).what₂.Tau × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m) × Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m)) ℂ),
      P ∈ Formalism.L2.Forms.CSpan (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m) →
      (∀ s, t.ptE.eWz u a ψ c s =
        Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.lamT u (I.rec7 l Z).R.m)) (Formalism.L2.Forms.mZ u (t.pt.til u a ha h1).z0) P
          (Formalism.L2.Forms.twYS t.ch C.forms u a (I.rec7 l Z).R.m le_rfl s)) →
      (t.pt.val u a ha).eW (((I.rec7 l Z).PTw u a).lowerMap ψ) c =
        Formalism.L2.Forms.fnOf _ (Formalism.L2.Forms.shiftOf (Formalism.L2.Forms.sgT u)) 1 (Formalism.L2.Ker.brTen (I.rec7 l Z) u P) := by

  subst he
  obtain ⟨hW, hLv, hPd⟩ := hTw
  intro _ ψ c P _ hψ
  have hS := hC u
  have hPd' : I.StdP l Z l0 t.pt t.ptE := hPd
  have hW' : I.StdW l Z l0 t.forms := hW
  have hl : Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u = B.wts.lamTrue u B.R.m := funext (trueWeight_lastStep_trueColumns I l Z u)
  have hs : Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u = B.wts.sgTrue := funext (trueRowWeight_trueColumns I l Z u)
  have hl' : Formalism.L2.Forms.lamT (D := I.rec7 l Z) u (I.rec7 l Z).R.m = B.wts.lamTrue u B.R.m := hl
  have hs' : Formalism.L2.Forms.sgT (D := I.rec7 l Z) u = B.wts.sgTrue := hs
  have hI : ∀ τ i, 0 ≤ Br.bBr (N_m_succ B.R) (B.wts.lamTrue u B.R.m τ) (B.wts.sgTrue τ) i := by
    intro τ i
    have h := (Formalism.MainNotions.product_first_zeroth_parts.interlaceTr (I.rec7 l Z) u (sg_interlace (C.forms u).valP) τ i).1
    rw [hl, hs] at h
    exact sub_nonneg.2 h
  have h1' : ψ c = fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) 1
      (actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P) := by
    refine Eq.trans ?_ (fnOf_lastAll (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (B.wts.lamTrue u B.R.m) (aT I l u) P)
    funext s
    have h := hψ s
    rw [hPd'.eWz, hl', hPd'.z0 u a ha h1, mZ_std I l Z u hO hP (TC.z0 X u) (fun j => rfl)] at h
    refine h.trans ?_
    have h2 : (Formalism.L2.Forms.twYS t.ch C.forms u a (I.rec7 l Z).R.m le_rfl s).1 = s.1 := by
      simp only [Formalism.L2.Forms.twYS, Equiv.trans_apply, hW'.eY, Equiv.refl_symm, Equiv.refl_apply]
      rw [Formalism.L2.Forms.eYS_end _ _ _ (Or.inr rfl)]
      exact hS.eY B.R.m le_rfl (Or.inr rfl) s
    exact congrArg (fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) _ P) (Subtype.ext h2)
  have h3 : polOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) (Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m)) (ψ c) =
      actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P := by
    have e : (fun τ => ((Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m)).1 τ)⁻¹) = 1 := funext fun τ => inv_one
    have h := polOf_fnOf (Col2.Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (B.wts.lamTrue u B.R.m)) (Col2.fr0 B.fields.emb B.embLL (B.R.N B.R.m))
      (actP (B.wts.lamTrue u B.R.m) (lastAll (B.R.N B.R.m) (aT I l u)) P)
    rw [e] at h
    rw [h1']
    exact h
  have h4 : Formalism.L2.Ker.brTen (I.rec7 l Z) u P = (Br.brStdP (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue P : Pol ℂ (Tau B.R) (B.R.N B.R.m - 1)) := by
    have h := blk_brOne (ι := Tau B.R) (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue P
    refine Eq.trans ?_ h
    unfold Formalism.L2.Ker.brTen
    rw [hl, hs]
    rfl
  have h5 := branchingProjection_act_last (N_m_succ B.R) (B.wts.lamTrue u B.R.m) B.wts.sgTrue hI (aT I l u) P
  funext s
  rw [hPd'.eW u a ha _ c s ⟨s.1, s.2⟩ rfl, hs', h4, ← h5, ← h3]
  rfl

end GlobalTheory.Mem.Col2.LowerTie
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearIndependentRulBC
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam

namespace GlobalTheory.CuspFieldChange

open GlobalTheory.FieldBC GlobalTheory.SecFieldChange
open GlobalTheory.CoefChangeCompare (ValueWD HasBC hasBC_of evR_of_map)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l}

variable {c c₀ : Coeff l} (hle : c₀.F ≤ c.F)

theorem eq_sum_of_isBC {m : ℕ} {f' : Rul Xo c} {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hf' : f' ∈ sec Xo c a n)
    {as : Fin m → c.F} {fs : Fin m → Rul Xo c₀} (h : IsBC hle f' as fs) : f' = ∑ i, as i • rulBC hle (fs i) := by
  funext q y
  letI := resAlg hle q.R
  rw [val_of_isBC hle hf'.1 h q (fun _ => rfl) y, Finset.sum_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Algebra.smul_def]
  rfl

theorem cusp_unfBC_eq_span {r : ℕ} (U : ∀ σ : c₀.F →+* ℂ, Unf Xo c₀ σ r) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    cusp Xo c (unfBC hle U) a n = Submodule.span c.F (rulBC hle '' (cusp Xo c₀ U a n : Set (Rul Xo c₀))) := by
  refine le_antisymm (fun f' hf' => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨m, as, fs, hfs, h⟩ := cuspBC_holds hle U a n f' hf'
    rw [eq_sum_of_isBC hle (cusp_le_sec _ _ _ _ _ hf') h]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hfs i, rfl⟩)
  · rintro _ ⟨f, hf, rfl⟩
    exact (rulBC_cusp E H Dw l Xo c₀ c hle r U a n f (cusp_le_sec _ _ _ _ _ hf)).2.2 hf

theorem linearIndependent_rulBC {a : (E →+* ℂ) × ℕ → ℕ} {n m : ℕ} {v : Fin m → Rul Xo c₀}
    (hv : ∀ i, v i ∈ sec Xo c₀ a n) (hi : LinearIndependent c₀.F v) :
    LinearIndependent c.F (fun i => rulBC hle (v i)) := by
  have hS := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  have hWD : ValueWD Xo c₀ :=
    evalWD_fr (frChartF_of (GlobalTheory.Frames.chartCoverF_of_secBaseChange hS E H Dw l Xo c₀))
  have hBC : HasBC Xo c₀ := hasBC_of hS
  letI alg : Algebra c₀.F c.F := (incF c₀ c hle).toAlgebra
  rw [Fintype.linearIndependent_iff] at hi ⊢
  intro g hg i
  refine (Module.forall_dual_apply_eq_zero_iff c₀.F (g i)).1 fun lam => ?_
  refine hi (fun j => lam (g j)) ?_ i
  funext p y
  have hov : AlgOver c₀ c hle (Ext c₀.F c.F p.R) := fun x => ext_tower x
  obtain ⟨z, hz⟩ := hBC p.R (Ext c₀.F c.F p.R) (inR c.F p.R) y
  have h1 := evR_sum_smul (z.ext hle hov) g (fun i => rulBC hle (v i))
  have h0 : evR Xo c (0 : Rul Xo c) (z.ext hle hov) = 0 := evalAt_zero _ _ _
  rw [hg, h0] at h1
  have h2 : ∀ j, evR Xo c (rulBC hle (v j)) (z.ext hle hov) = inR c.F p.R (v j p y) := fun j => by
    rw [((rulBC_sec_val_linear E H Dw l Xo c₀ c hle).1 a n _ (hv j)).2 _ hov, FrPt.res_ext,
      evR_of_map hWD (hv j).1 hz]
  simp only [h2] at h1
  have h3 : ∀ j, algebraMap c.F (Ext c₀.F c.F p.R) (g j) * inR c.F p.R (v j p y) =
      (TensorProduct.tmul c₀.F (g j) (v j p y) : TensorProduct c₀.F c.F p.R) := fun j => by
    show (TensorProduct.tmul c₀.F (g j) (1 : p.R) * TensorProduct.tmul c₀.F (1 : c.F) (v j p y) :
      TensorProduct c₀.F c.F p.R) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have h4 : (0 : TensorProduct c₀.F c.F p.R) = ∑ j, TensorProduct.tmul c₀.F (g j) (v j p y) :=
    h1.trans (Finset.sum_congr rfl fun j _ => h3 j)
  have h5 := congrArg (coord lam p.R) h4
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_zero, map_sum] at h5
  simp only [coord_tmul] at h5
  rw [Finset.sum_apply, Finset.sum_apply]
  exact h5.symm

end GlobalTheory.CuspFieldChange
end
end
