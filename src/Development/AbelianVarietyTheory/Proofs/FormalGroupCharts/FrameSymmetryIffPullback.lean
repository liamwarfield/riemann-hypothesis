module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsAdjointnessSeriesOfFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JetSubstPCompJetBC

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameSymmetryIffPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameSymmetryIffPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory.FrameSym

section Val

variable {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K K₁ : Type} [Fintype K] [Fintype K₁]

theorem val_tie (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε))
    (c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (hm : LB.Gen.Maps (LB.linCombIso w φ' ε) a (flatGen L F φ' ε c))
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) {J' : (Z ⟶ X') → L'.ι}
    (hJ' : Good L' z J') :
    val c r z J = (∏ k, gw w (r ≫ φ' k) z (J ((r ≫ φ' k) ≫ F)) (J' (r ≫ φ' k)) ^ ε k) * val a r z J' := by
  have P := (maps_iff w φ' (fun k => φ' k ≫ F) ε a c (𝟙 Y) (flatGen L F φ' ε c)
    (fun j x hx => wchart_pull_le L F φ' j hx) (fun j => ?_)).1 hm
  · have := P Z r z (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => J' (r ≫ φ' k)) (fun k => hJ ((r ≫ φ' k) ≫ F))
      (fun k => hJ' (r ≫ φ' k))
    rw [Category.comp_id] at this
    rw [val_of c r z J (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc])]
    exact this
  · refine unit_ext fun y hy => ?_
    have hyV : (𝟙 Y : Y ⟶ Y) y ∈ ((L.pull F).LinComb φ' ε).U j := hy
    have hyU : (𝟙 Y : Y ⟶ Y) ((𝟙 Y : Y ⟶ Y) y) ∈ LB.wchart L (fun k => φ' k ≫ F) (fun k => j k ⟨⟩) :=
      wchart_pull_le L F φ' j hy
    refine (gm_res (𝟙 Y) y _ hyV _).trans ?_
    refine Eq.trans ?_ (gm_res (𝟙 Y) y _ hyV _).symm
    have e := gm_pull (𝟙 Y) (𝟙 Y) y _ hyU (c.s fun k => j k ⟨⟩)
    rw [Category.comp_id] at e
    exact e.symm

def scale (φ : K → (Y ⟶ X)) (ε : K → ℤ) (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb L φ ε)) : LB.Gen (LB.LinComb L φ ε) :=
  ⟨fun j => res le_top u * g.s j⟩

theorem val_scale {φ : K → (Y ⟶ X)} {ε : K → ℤ} (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb L φ ε)) {Z : Scheme.{0}}
    (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val (scale φ ε u g) r z J = gm r z ⊤ u * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) u) rfl)

theorem good_exists (hL : L.IsLB) {Z : Scheme.{0}} (z : Z) : ∃ J, Good L z J := by
  choose d hd using fun χ : Z ⟶ X => exists_chart hL (χ z)
  exact ⟨d, hd⟩

theorem corr_sym_iff (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ)
    (a : LB.Gen (LB.LinComb L' φ' ε)) (c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε))
    (hm : LB.Gen.Maps (LB.linCombIso w φ' ε) a (flatGen L F φ' ε c))
    (φ : K₁ → (Y ⟶ X)) (ε₁ : K₁ → ℤ) (e : LB.Gen (LB.LinComb L φ ε₁)) (hc : LB.Gen.Corr L _ _ _ _ c e)
    (s : Y ⟶ Y) (hs : FormEq φ' ε (fun k => s ≫ φ' k) ε) (u : Γ(Y, ⊤)ˣ) :
    LB.Gen.Corr L _ _ _ _ e (scale _ _ u (LB.pullGen L φ ε₁ e s)) ↔
      LB.Gen.Corr L' _ _ _ _ a (scale _ _ u (LB.pullGen L' φ' ε a s)) := by
  have key : ∀ (y : Y) J J', Good L y J → Good L' y J' →
      (val e (𝟙 Y) y J = val (scale _ _ u (LB.pullGen L φ ε₁ e s)) (𝟙 Y) y J ↔
        val a (𝟙 Y) y J' = val (scale _ _ u (LB.pullGen L' φ' ε a s)) (𝟙 Y) y J') := by
    intro y J J' hJ hJ'
    rw [val_scale _ _ _ _ hJ, val_scale _ _ _ _ hJ', val_pull hJ, val_pull hJ', ← val_corr hJ hc, ← val_corr hJ hc,
      val_tie w φ' ε a c hm _ y hJ hJ', val_tie w φ' ε a c hm _ y hJ hJ']
    have h := hs _ (fun ψ => gw w ψ y (J (ψ ≫ F)) (J' ψ))
    simp only [Category.id_comp]
    rw [← h, mul_left_comm, mul_right_inj]
  constructor
  · intro h
    refine corr_of_val hL' fun y J' hJ' => ?_
    obtain ⟨J, hJ⟩ := good_exists hL y
    exact (key y J J' hJ hJ').1 (val_corr hJ h _)
  · intro h
    refine corr_of_val hL fun y J hJ => ?_
    obtain ⟨J', hJ'⟩ := good_exists hL' y
    exact (key y J J' hJ hJ').2 (val_corr hJ' h _)

end Val

theorem formEq_swap {B : Scheme.{0}} (G : Over B) [GrpObj G] [IsCommMonObj G] {T : Over B} (a b : T ⟶ G) (s : T ⟶ T)
    (ha : s ≫ a = b) (hb : s ≫ b = a) :
    FormEq (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![a, b] I.down).left) (cε 2)
      (fun I => s.left ≫ (psum G ![a, b] I.down).left) (cε 2) := by
  intro U _ h
  have hp : ∀ I : Finset (Fin 2), s.left ≫ (psum G ![a, b] I).left = (psum G ![b, a] I).left := fun I => by
    have := psum_hom (preHom (G := G) s) ![a, b] I
    have e : (fun i => preHom (G := G) s (![a, b] i)) = ![b, a] := by
      funext i; fin_cases i
      exacts [ha, hb]
    rw [e] at this
    exact congrArg (fun z => z.left) this
  simp only [hp]
  have hu : (Finset.univ : Finset (ULift.{0} (Finset (Fin 2)))) = {⟨∅⟩, ⟨{0}⟩, ⟨{1}⟩, ⟨{0, 1}⟩} := by decide
  rw [hu]
  simp only [Finset.prod_insert (by decide : (⟨∅⟩ : ULift.{0} (Finset (Fin 2))) ∉ ({⟨{0}⟩, ⟨{1}⟩, ⟨{0, 1}⟩} : Finset _)),
    Finset.prod_insert (by decide : (⟨{0}⟩ : ULift.{0} (Finset (Fin 2))) ∉ ({⟨{1}⟩, ⟨{0, 1}⟩} : Finset _)),
    Finset.prod_insert (by decide : (⟨{1}⟩ : ULift.{0} (Finset (Fin 2))) ∉ ({⟨{0, 1}⟩} : Finset _)),
    Finset.prod_singleton]
  have p0 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs ∅ = 1 := fun _ => rfl
  have p1 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs {0} = xs 0 * 1 := fun _ => rfl
  have p2 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs {1} = xs 1 * 1 := fun _ => rfl
  have p3 : ∀ xs : Fin 2 → (T ⟶ G), psum G xs {0, 1} = xs 0 * (xs 1 * 1) := fun _ => rfl
  simp only [p0, p1, p2, p3, Matrix.cons_val_zero, Matrix.cons_val_one, _root_.mul_one]
  rw [_root_.mul_comm b a]
  exact congrArg _ (mul_left_comm _ _ _)

theorem jetMap_mk {R : Type} [CommRing R] {κ κ' : Type} {m : ℕ} (φ : κ → MvPolynomial κ' R) (hφ : ∀ i, φ i ∈ orig R κ')
    (p : MvPolynomial κ R) :
    jetMap (m := m) φ hφ (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (MvPolynomial.aeval φ p) := rfl

theorem swap_jpt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (m : ℕ)
    (φ : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S) (i k : Fin 2) (h : φ i = fun j => X (k, j)) :
    Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2) ≫ jptG t x0 d x m i = jptG t x0 d x m k := by
  have e : (jetSubstP m (fun p : Fin 2 × Fin d => φ p.1 p.2)).comp (jetCopy d m i) = jetCopy d m k := by
    refine Ideal.Quotient.algHom_ext S (MvPolynomial.algHom_ext fun p => ?_)
    show jetSubstP m _ (jetCopy d m i (Ideal.Quotient.mk _ (X p))) = jetCopy d m k (Ideal.Quotient.mk _ (X p))
    simp [jetSubstP, jetCopy, jetMap_mk, h]
  rw [jptG, jptG, ← Category.assoc, ← e]
  congr 1
  apply Over.OverMorphism.ext
  simp only [Formalism.L2.Pj.homAt, Over.comp_left, Over.homMk_left, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem frame_sym_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (sy : PS S 2 d), (∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧ LB.Gen.Corr t.PP.L _ _ _ _ (e m) (scaleGenG t _ _ (unitΓ u⁻¹) (peG t x0 d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]))) ↔ (∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (e' m) (scaleGenG t' _ _ (unitΓ u⁻¹) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]))) := by
  intro E _ _ _ H X0 t S _ x0 t' mp w _ d x x' _ e e' _ _ ht sy
  refine forall_congr' fun m => exists_congr fun u => and_congr Iff.rfl ?_
  obtain ⟨c₁, hc, hm⟩ := ht m
  exact corr_sym_iff t.PP.isLB t'.PP.isLB w _ (cε 2) (e' m) c₁ hm
    (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m) hc _
    (formEq_swap t'.G _ _ _ (swap_jpt t' _ d x' m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] 0 1 rfl)
      (swap_jpt t' _ d x' m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] 1 0 rfl)) (unitΓ u⁻¹)

end GlobalTheory.FrameSym
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameSymmetryIffPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_symmetry_iff_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (sy : PS S 2 d), (∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧ LB.Gen.Corr t.PP.L _ _ _ _ (e m) (scaleGenG t _ _ (unitΓ u⁻¹) (peG t x0 d x e m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]))) ↔ (∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m sy ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (e' m) (scaleGenG t' _ _ (unitΓ u⁻¹) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)]))) := by
  first | exact @GlobalTheory.FrameSym.frame_sym_iff | exact GlobalTheory.FrameSym.frame_sym_iff | (intros; apply GlobalTheory.FrameSym.frame_sym_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AdjointSeriesFramesPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AdjointSeriesFramesPullback
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.FrameAdjDown

section General

variable {X0 X' Y Z A A' : Scheme.{0}} {L : LB X0} {L' : LB X'} {F : X' ⟶ X0} {K K₂ : Type} [Fintype K] [Fintype K₂]

def scl {φ : K → (Y ⟶ X0)} {ε : K → ℤ} (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb L φ ε)) : LB.Gen (LB.LinComb L φ ε) :=
  ⟨fun j => res le_top u * g.s j⟩

theorem val_scl {φ : K → (Y ⟶ X0)} {ε : K → ℤ} (u : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) {z : Z}
    {J : (Z ⟶ X0) → L.ι} (hJ : Good L z J) : val (scl u g) r z J = gm r z ⊤ u * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) u) rfl)

theorem pmaps_of_flat (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε))
    (c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε))
    (h : LB.Gen.Maps (LB.linCombIso w φ' ε) a (flatGen L F φ' ε c)) :
    PMaps w φ' (fun k => φ' k ≫ F) ε a c (𝟙 Y) := by
  refine (maps_iff w φ' (fun k => φ' k ≫ F) ε a c (𝟙 Y) (flatGen L F φ' ε c)
    (fun j x hx => wchart_pull_le L F φ' j hx) (fun j => ?_)).1 h
  refine unit_ext fun y hy => ?_
  have hyV : (𝟙 Y : Y ⟶ Y) y ∈ ((L.pull F).LinComb φ' ε).U j := hy
  have hyU : (𝟙 Y : Y ⟶ Y) ((𝟙 Y : Y ⟶ Y) y) ∈ LB.wchart L (fun k => φ' k ≫ F) (fun k => j k ⟨⟩) :=
    wchart_pull_le L F φ' j hy
  refine (gm_res (𝟙 Y) y _ hyV _).trans ?_
  refine Eq.trans ?_ (gm_res (𝟙 Y) y _ hyV _).symm
  have e := gm_pull (𝟙 Y) (𝟙 Y) y _ hyU (c.s fun k => j k ⟨⟩)
  rw [Category.comp_id] at e
  exact e.symm

theorem corr_down (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F))
    {ψ : K → (A ⟶ X0)} {ψ' : K → (A' ⟶ X')} {ε : K → ℤ} {U : A' ⟶ A} (hψ : ∀ k, ψ' k ≫ F = U ≫ ψ k)
    {g : LB.Gen (LB.LinComb L ψ ε)} {g' : LB.Gen (LB.LinComb L' ψ' ε)} (hg : PMaps w ψ' ψ ε g' g U)
    {φ : K₂ → (Y ⟶ X0)} {φ' : K₂ → (Y ⟶ X')} {δ : K₂ → ℤ} {e : LB.Gen (LB.LinComb L φ δ)}
    {e' : LB.Gen (LB.LinComb L' φ' δ)} {c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) δ)}
    (hc : LB.Gen.Corr L _ _ _ _ c e) (hm : LB.Gen.Maps (LB.linCombIso w φ' δ) e' (flatGen L F φ' δ c))
    {l : Y ⟶ A} {l' : Y ⟶ A'} (hl : l' ≫ U = l) (σ₁ σ₂ : Y ⟶ Y) (u : Γ(Y, ⊤)ˣ)
    (hF : ∀ (V : Type) [CommGroup V] (h : (Y ⟶ X') → V),
      (∏ k, h (l' ≫ ψ' k) ^ ε k) * ∏ k, h (σ₁ ≫ φ' k) ^ δ k = ∏ k, h (σ₂ ≫ φ' k) ^ δ k)
    (H : LB.Gen.Corr L _ _ _ _ (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ g l) (LB.pullGen L _ _ e σ₁))
      (scl u (LB.pullGen L _ _ e σ₂))) :
    LB.Gen.Corr L' _ _ _ _ (LB.mulGen L' _ _ _ _ (LB.pullGen L' _ _ g' l') (LB.pullGen L' _ _ e' σ₁))
      (scl u (LB.pullGen L' _ _ e' σ₂)) := by
  refine corr_of_val hL' fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ := DegPull.exists_good' hL y
  have h0 := val_corr hJ H (𝟙 Y)
  rw [val_mul hJ, val_scl _ _ _ hJ, val_pull hJ, val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp,
    Category.id_comp] at h0
  rw [val_mul hJ', val_scl _ _ _ hJ', val_pull hJ', val_pull hJ', val_pull hJ', Category.id_comp, Category.id_comp,
    Category.id_comp]
  have he : ∀ σ : Y ⟶ Y, val e σ y J =
      (∏ k, gw w (σ ≫ φ' k) y (J ((σ ≫ φ' k) ≫ F)) (J' (σ ≫ φ' k)) ^ δ k) * val e' σ y J' := fun σ => by
    have := DegPull.pmaps_val (fun k => (Category.id_comp _).symm) (pmaps_of_flat w φ' δ e' c hm) σ y hJ hJ'
    rw [Category.comp_id] at this
    exact (val_corr hJ hc σ).symm.trans this
  have h1 := DegPull.pmaps_val hψ hg l' y hJ hJ'
  rw [hl] at h1
  have h2 := hF _ (fun q => gw w q y (J (q ≫ F)) (J' q))
  rw [h1, he, he, ← h2, _root_.mul_mul_mul_comm, mul_left_comm (gm (𝟙 Y) y ⊤ u)] at h0
  exact mul_left_cancel h0

end General

open Formalism.MainNotions.ModuliIntegralCharts.H1.GermB Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun GlobalTheory.FrameAdjSeries

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem pt_act' {X0 : Scheme.{0}} {t : SAB H X0} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ}
    {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {act : 𝓞 E → Fin d → PS S 1 d}
    (h : ∀ m (b : 𝓞 E), x m ≫ t.act.act b =
      homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x m)
    (m : ℕ) {n : ℕ} (r : Fin 1 → Fin n) (a : 𝓞 E) :
    homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => psIn d m r (act a p.2))) ≫ x m =
      jptG t x0 d x m (r 0) ≫ t.act.act a := by
  rw [subst_psIn, ← homAt_comp, Category.assoc, ← h m a, ← Category.assoc, ren_one]
  try rfl

theorem push_act {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (mp : SABMap t' t f) {T : Over S'}
    (p : T ⟶ t'.G) (a : 𝓞 E) : pushPt mp.cart.1.w (p ≫ t'.act.act a) = pushPt mp.cart.1.w p ≫ t.act.act a :=
  Over.OverMorphism.ext (by
    show (p.left ≫ _) ≫ _ = (p.left ≫ _) ≫ _
    rw [Category.assoc, mp.act, Category.assoc])

def sqMap {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (mp : SABMap t' t f) :
    Over.mk ((t'.G ⊗ t'.G).hom ≫ f) ⟶ t.G ⊗ t.G :=
  lift (pushPt mp.cart.1.w (fst t'.G t'.G)) (pushPt mp.cart.1.w (snd t'.G t'.G))

theorem adj_comm {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (mp : SABMap t' t f) (a b : 𝓞 E)
    (k : ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2))) :
    Sum.elim (cφG t' ![fst t'.G t'.G, snd t'.G t'.G ≫ t'.act.act b])
        (cφG t' ![fst t'.G t'.G ≫ t'.act.act a, snd t'.G t'.G]) k ≫ mp.φ =
      (sqMap mp).left ≫ Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act b])
        (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) k := by
  rcases k with I | I
  · refine psum_push mp.cart _ _ (sqMap mp) (fun i => ?_) I.down
    fin_cases i
    · simp [sqMap]
    · exact (push_act mp _ _).trans (by simp [sqMap])
  · refine psum_push mp.cart _ _ (sqMap mp) (fun i => ?_) I.down
    fin_cases i
    · exact (push_act mp _ _).trans (by simp [sqMap])
    · simp [sqMap]

theorem lift_sqMap {S S' : Scheme.{0}} {t' : SAB H S'} {t : SAB H S} {f : S' ⟶ S} (mp : SABMap t' t f)
    {T' : Over S'} {T : Over S} (p' q' : T' ⟶ t'.G) (p q : T ⟶ t.G) (h : T'.left ⟶ T.left)
    (hp : p'.left ≫ mp.φ = h ≫ p.left) (hq : q'.left ≫ mp.φ = h ≫ q.left) :
    (lift p' q').left ≫ (sqMap mp).left = h ≫ (lift p q).left := by
  apply pullback.hom_ext
  · show ((lift p' q').left ≫ (sqMap mp).left) ≫ (fst t.G t.G).left = (h ≫ (lift p q).left) ≫ (fst t.G t.G).left
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, sqMap, lift_fst, lift_fst, ← hp]
    show (lift p' q').left ≫ (fst t'.G t'.G).left ≫ mp.φ = _
    rw [← Category.assoc, ← Over.comp_left, lift_fst]
  · show ((lift p' q').left ≫ (sqMap mp).left) ≫ (snd t.G t.G).left = (h ≫ (lift p q).left) ≫ (snd t.G t.G).left
    rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left, sqMap, lift_snd, lift_snd, ← hq]
    show (lift p' q').left ≫ (snd t'.G t'.G).left ≫ mp.φ = _
    rw [← Category.assoc, ← Over.comp_left, lift_snd]


set_option maxHeartbeats 2000000 in
theorem adjoint_series_pull_back : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (act : 𝓞 E → Fin d → PS S 1 d) (ad : 𝓞 E → PS S 2 d) (a : 𝓞 E), (∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) → (∀ m (b : 𝓞 E), x' m ≫ t'.act.act b = homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x' m) → (∃ wL : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.mulGen t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left) (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)])) (scaleGenG t _ _ (unitΓ u) (peG t x0 d x e m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))) → (∃ wL : LB.Gen (LB.LinComb t'.PP.L (Sum.elim (cφG t' ![fst t'.G t'.G, snd t'.G t'.G ≫ t'.act.act (H.bar a)]) (cφG t' ![fst t'.G t'.G ≫ t'.act.act a, snd t'.G t'.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (LB.mulGen t'.PP.L _ _ _ _ (LB.pullGen t'.PP.L _ _ wL (lift (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))).left) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)])) (scaleGenG t' _ _ (unitΓ u) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))) := by
  intro E _ _ _ H X0 t S _ x0 t' mp w hw d x x' hx e e' _ _ htie act ad a _ hact ⟨wL, hwL, hu⟩
  obtain ⟨wL', hwL', hp⟩ := DegPull.exists_pmaps ((isGen_iff w).1 hw.1) t.PP.isLB t'.PP.isLB (sqMap mp).left
    (adj_comm mp a (H.bar a)) wL hwL
  refine ⟨wL', hwL', fun m => ?_⟩
  obtain ⟨u, hu1, hu2⟩ := hu m
  obtain ⟨c, hc, hm⟩ := htie m
  refine ⟨u, hu1, ?_⟩
  have hj : ∀ i : Fin 2, (jptG t' (𝟙 (Sp S)) d x' m i).left ≫ mp.φ = 𝟙 _ ≫ (jptG t x0 d x m i).left := fun i => by
    show ((homAt (𝟙 (Sp S)) (jetCopy d m i)).left ≫ (x' m).left) ≫ mp.φ =
      𝟙 _ ≫ (homAt x0 (jetCopy d m i)).left ≫ (x m).left
    rw [Category.assoc, hx, Category.id_comp]
    rfl
  have hl₀ := lift_sqMap mp (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))
    (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2)) (𝟙 (Sp (Jet S (Fin 2 × Fin d) m))) (hj 0) (hj 1)
  have hl : (lift (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))).left ≫
      (sqMap mp).left = (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left :=
    hl₀.trans (Category.id_comp _)
  refine corr_down (Y := (jOG (𝟙 (Sp S)) d m 2).left) t.PP.isLB t'.PP.isLB w (adj_comm mp a (H.bar a)) hp hc hm hl
    _ _ (unitΓ u) (fun V _ h => ?_) hu2
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, wl_pt, wl_pt', pe_pt, pt_sub, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, pt_X, pt_act' hact, zpow_neg, Finset.prod_inv_distrib]
  simp only [inv_mul_cancel_right]

end GlobalTheory.FrameAdjDown
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AdjointSeriesFramesPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjointSeries_frames_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (act : 𝓞 E → Fin d → PS S 1 d) (ad : 𝓞 E → PS S 2 d) (a : 𝓞 E), (∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) → (∀ m (b : 𝓞 E), x' m ≫ t'.act.act b = homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x' m) → (∃ wL : LB.Gen (LB.LinComb t.PP.L (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)]) (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.mulGen t.PP.L _ _ _ _ (LB.pullGen t.PP.L _ _ wL (lift (jptG t x0 d x m (0 : Fin 2)) (jptG t x0 d x m (1 : Fin 2))).left) (peG t x0 d x e m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)])) (scaleGenG t _ _ (unitΓ u) (peG t x0 d x e m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))) → (∃ wL : LB.Gen (LB.LinComb t'.PP.L (Sum.elim (cφG t' ![fst t'.G t'.G, snd t'.G t'.G ≫ t'.act.act (H.bar a)]) (cφG t' ![fst t'.G t'.G ≫ t'.act.act a, snd t'.G t'.G])) (Sum.elim (cε 2) fun I => -cε 2 I)), wL.IsGen ∧ ∀ m, ∃ u : (Jet S (Fin 2 × Fin d) m)ˣ, (u : Jet S (Fin 2 × Fin d) m) = psJet m (ad a) ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (LB.mulGen t'.PP.L _ _ _ _ (LB.pullGen t'.PP.L _ _ wL (lift (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))).left) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => psIn d m ![0] (act a j), fun j => X ((1 : Fin 2), j)])) (scaleGenG t' _ _ (unitΓ u) (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 2), j), fun j => psIn d m ![1] (act (H.bar a) j)]))) := by
  first | exact @GlobalTheory.FrameAdjDown.adjoint_series_pull_back | exact GlobalTheory.FrameAdjDown.adjoint_series_pull_back | (intros; apply GlobalTheory.FrameAdjDown.adjoint_series_pull_back <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RigidificationAtOriginIffPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RigidificationAtOriginIffPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.RigOriginPull

theorem val_tie {X₁ X₂ Y Z : Scheme.{0}} {K : Type} [Fintype K] {L : LB X₁} {L' : LB X₂} {F : X₂ ⟶ X₁}
    (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X₂)) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε))
    (c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε))
    (h : LB.Gen.Maps (LB.linCombIso w φ' ε) a (flatGen L F φ' ε c)) (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X₁) → L.ι} {J' : (Z ⟶ X₂) → L'.ι} (hJ : Good L z J) (hJ' : Good L' z J') :
    val c r z J = (∏ k, Geo.Tor.gw w (r ≫ φ' k) z (J ((r ≫ φ' k) ≫ F)) (J' (r ≫ φ' k)) ^ ε k) * val a r z J' := by
  have H := (maps_iff w φ' (fun k => φ' k ≫ F) ε a c (𝟙 Y) (flatGen L F φ' ε c)
    (fun j x hx => wchart_pull_le L F φ' j hx) (fun j => ?_)).1 h Z r z (fun k => J ((r ≫ φ' k) ≫ F))
    (fun k => J' (r ≫ φ' k)) (fun k => hJ ((r ≫ φ' k) ≫ F)) (fun k => hJ' (r ≫ φ' k))
  · rw [Category.comp_id] at H
    exact (val_of c r z J _ (fun k => by rw [Category.assoc])).trans H
  · refine unit_ext fun y hy => ?_
    have hyV : (𝟙 Y : Y ⟶ Y) y ∈ ((L.pull F).LinComb φ' ε).U j := hy
    have hyU : (𝟙 Y : Y ⟶ Y) ((𝟙 Y : Y ⟶ Y) y) ∈ LB.wchart L (fun k => φ' k ≫ F) (fun k => j k ⟨⟩) :=
      wchart_pull_le L F φ' j hy
    refine (gm_res (𝟙 Y) y _ hyV _).trans ?_
    refine Eq.trans ?_ (gm_res (𝟙 Y) y _ hyV _).symm
    have e := gm_pull (𝟙 Y) (𝟙 Y) y _ hyU (c.s fun k => j k ⟨⟩)
    rw [Category.comp_id] at e
    exact e.symm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

theorem prod_prim (t : SAB H X0) {T : Over X0} {M : Type} [CommGroup M] (h : (T.left ⟶ t.G.left) → M) :
    ∏ k, h ((1 : T ⟶ t.G).left ≫ primφ t k) ^ primε k = h (1 : T ⟶ t.G).left := by
  have hpt : ∀ I : ULift.{0} (Finset (Fin 2)), (1 : T ⟶ t.G).left ≫ cφG t ![𝟙 t.G, t.act.act H.w0] I =
      (psum t.G ![1, (1 : T ⟶ t.G) ≫ t.act.act H.w0] I.down).left := by
    intro I
    simp only [cφG, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · exact Category.comp_id (1 : T ⟶ t.G)
    · rfl
  have hc : ∏ I, h ((1 : T ⟶ t.G).left ≫ cφG t ![𝟙 t.G, t.act.act H.w0] I) ^ cε 2 I = 1 :=
    (Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ cε 2 I) (hpt I)).trans
      (GermB.cube_one_left t (fun p => h p.left) _)
  rw [Fintype.prod_sum_type]
  simp only [primφ, primε, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, Category.comp_id, zpow_neg,
    Finset.prod_inv_distrib, zpow_one]
  exact (congrArg (fun q => h (1 : T ⟶ t.G).left * q⁻¹) hc).trans (by rw [inv_one, _root_.mul_one])

theorem prod_cube_left (t : SAB H X0) {T T' : Over X0} {M : Type} [CommGroup M] (h : (T'.left ⟶ t.G.left) → M)
    (u : T' ⟶ T) (a b : T ⟶ t.G) (ha : u ≫ a = 1) :
    ∏ I, h (u.left ≫ cφG t ![a, b] I) ^ cε 2 I = 1 := by
  have hpt : ∀ I : ULift.{0} (Finset (Fin 2)), u.left ≫ cφG t ![a, b] I = (psum t.G ![1, u ≫ b] I.down).left := by
    intro I
    simp only [cφG, ← Over.comp_left]
    refine congrArg Over.Hom.left ((psum_hom (preHom _) _ I.down).trans ?_)
    refine congrArg (fun f => psum t.G f I.down) (funext fun i => ?_)
    fin_cases i
    · exact ha
    · rfl
  exact (Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ cε 2 I) (hpt I)).trans
    (GermB.cube_one_left t (fun p => h p.left) _)

end GlobalTheory.RigOriginPull


open GlobalTheory.RigOriginPull in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.rigOrigin_iff_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (wP : PrimTyG t) (wP' : PrimTyG t'), wP.IsGen → wP'.IsGen → (∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun k => primφ t' k ≫ mp.φ) primε), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (LB.pullGen t.PP.L _ _ wP mp.φ) ∧ LB.Gen.Maps (LB.linCombIso w (primφ t') primε) wP' (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (act : 𝓞 E → Fin d → PS S 1 d), (homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S) ≫ x' 0 = 1) → (∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) → (Rig0G t x0 d x act e wP ↔ Rig0G t' (𝟙 (Sp S)) d x' act e' wP') := by
  intro E _ _ _ H X0 t S _ x0 t' mp w hrig d x x' hx e e' _ _ htie wP wP' _ _ hP act h0 _
  obtain ⟨c, hc₁, hc₂⟩ := htie 0
  obtain ⟨cP, hP₁, hP₂⟩ := hP
  have hL := t.PP.isLB
  have hL' := t'.PP.isLB
  have pm := (maps_iff w _ (fun _ => eSec t.G) _ t'.PP.rig t.PP.rig mp.cm.e _
    (rigPull_le mp.cm.F mp.cm.e mp.cm.e_comm t.PP.L) (fun _ => rfl)).1 hrig.2
  let o : Sp S ⟶ t'.G.left := (1 : overAt (𝟙 (Sp S)) S ⟶ t'.G).left
  have key : ∀ (y : Sp S) (J : (Sp S ⟶ t.G.left) → t.PP.L.ι) (J' : (Sp S ⟶ t'.G.left) → t'.PP.L.ι),
      Good t.PP.L y J → Good t'.PP.L y J' →
      val (LB.pullGen t.PP.L _ _ (eLG t x0 d x act e wP 0)
          (Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left) (𝟙 (Sp S)) y J =
        Geo.Tor.gw w o y (J (o ≫ mp.φ)) (J' o) *
          val (LB.pullGen t'.PP.L _ _ (eLG t' (𝟙 (Sp S)) d x' act e' wP' 0)
            (Formalism.L2.Pj.homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)).left) (𝟙 (Sp S)) y J' ∧
      val (rigT t.G t.PP.L t.PP.rig (overAt x0 S) 1) (𝟙 (Sp S)) y J =
        Geo.Tor.gw w o y (J (o ≫ mp.φ)) (J' o) *
          val (rigT t'.G t'.PP.L t'.PP.rig (overAt (𝟙 (Sp S)) S) 1) (𝟙 (Sp S)) y J' := by
    intro y J J' hJ hJ'
    constructor
    · let A := Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)
      let A' := Formalism.L2.Pj.homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S)
      let σ : Jet S (Fin 2 × Fin d) 0 →ₐ[S] Jet S (Fin 1 × Fin d) 0 := jetSubstP 0 fun p : Fin 2 × Fin d =>
        (![fun j => X ((0 : Fin 1), j), fun j => psIn d 0 ![0] (act H.w0 j)] :
          Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2
      have ho : (𝟙 (Sp S) ≫ A'.left) ≫ (x' 0).left = o :=
        (congrArg (· ≫ (x' 0).left) (Category.id_comp _)).trans (congrArg (fun q => q.left) h0)
      have ho' : (𝟙 (Sp S) ≫ A.left) ≫ (x 0).left = o ≫ mp.φ := by
        rw [← ho, ← hx 0]
        exact (Category.assoc _ _ _).symm
      have p₁ : val wP ((𝟙 (Sp S) ≫ A.left) ≫ (x 0).left) y J =
          Geo.Tor.gw w o y (J (o ≫ mp.φ)) (J' o) * val wP' ((𝟙 (Sp S) ≫ A'.left) ≫ (x' 0).left) y J' := by
        rw [ho, ho']
        refine (val_pull hJ wP mp.φ o).symm.trans ((val_corr hJ hP₁ o).symm.trans
          ((val_tie w _ _ wP' cP hP₂ o y hJ hJ').trans (congrArg₂ (· * ·) ?_ rfl)))
        exact prod_prim t' (T := overAt (𝟙 (Sp S)) S) (fun q => Geo.Tor.gw w q y (J (q ≫ mp.φ)) (J' q))
      have hu : (A' ≫ Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ) ≫ jptG t' (𝟙 (Sp S)) d x' 0 (0 : Fin 2) = 1 := by
        have hid : σ.comp (jetCopy d 0 (0 : Fin 2)) = AlgHom.id S _ := by
          apply GermD.jet_hom_ext
          rintro ⟨i, j⟩
          obtain rfl : i = 0 := Subsingleton.elim _ _
          simp [σ, jetSubstP, jetCopy, GermD.jetMap_mk]
        rw [jptG, Category.assoc, ← Category.assoc (Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ), GermD.homAt_comp, hid,
          GermD.homAt_id, Category.id_comp]
        exact h0
      have p₂ : val (e 0) ((𝟙 (Sp S) ≫ A.left) ≫ (Formalism.L2.Pj.homAt x0 σ).left) y J =
          val (e' 0) ((𝟙 (Sp S) ≫ A'.left) ≫ (Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ).left) y J' := by
        have q : (𝟙 (Sp S) ≫ A'.left) ≫ (Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ).left =
            (A' ≫ Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ).left := congrArg (· ≫ _) (Category.id_comp _)
        have q' : (𝟙 (Sp S) ≫ A.left) ≫ (Formalism.L2.Pj.homAt x0 σ).left =
            (A' ≫ Formalism.L2.Pj.homAt (𝟙 (Sp S)) σ).left := q
        rw [q, q']
        refine (val_corr hJ hc₁ _).symm.trans ((val_tie w _ _ (e' 0) c hc₂ _ y hJ hJ').trans ?_)
        exact (congrArg₂ (· * ·) (prod_cube_left t' (fun q => Geo.Tor.gw w q y (J (q ≫ mp.φ)) (J' q)) _ _ _ hu)
          rfl).trans (_root_.one_mul _)
      refine (val_pull hJ _ _ _).trans ((val_mul hJ _ _ _).trans ((congrArg₂ (· * ·)
        ((val_pull hJ _ _ _).trans p₁) ((val_pull hJ _ _ _).trans p₂)).trans ((_root_.mul_assoc _ _ _).trans
          (congrArg₂ (· * ·) rfl (Eq.symm ?_)))))
      exact (val_pull hJ' _ _ _).trans ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ' _ _ _)
        (val_pull hJ' _ _ _)))
    · refine (GermB.val_rigT _ _ _ _ _ y J hJ).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl
        (GermB.val_rigT _ _ _ _ _ y J' hJ').symm))
      have b : (𝟙 (Sp S) ≫ (overAt (𝟙 (Sp S)) S).hom) ≫ mp.cm.e = 𝟙 (Sp S) ≫ (overAt x0 S).hom := by
        rw [mp.base]
        simp
      have a₁ : (𝟙 (Sp S) ≫ (overAt (𝟙 (Sp S)) S).hom) ≫ eSec t'.G = o :=
        congrArg (· ≫ eSec t'.G) (Category.id_comp _)
      have a₂ : (𝟙 (Sp S) ≫ (overAt x0 S).hom) ≫ eSec t.G = o ≫ mp.φ := by
        rw [← b, ← a₁, Category.assoc, ← mp.cm.e_comm]
        exact (Category.assoc _ _ _).symm
      have q := pm _ (𝟙 (Sp S) ≫ (overAt (𝟙 (Sp S)) S).hom) y (fun _ => J (o ≫ mp.φ)) (fun _ => J' o)
        (fun _ => (congrArg (fun r => (r ≫ mp.φ) y ∈ t.PP.L.U (J (o ≫ mp.φ))) a₁).mpr (hJ _))
        (fun _ => (congrArg (fun r => r y ∈ t'.PP.L.U (J' o)) a₁).mpr (hJ' _))
      rw [Fintype.prod_unique, zpow_one, b, a₁] at q
      exact (val_of _ _ y J _ (fun _ => congrArg J a₂)).trans (q.trans (congrArg₂ (· * ·) rfl
        (val_of _ _ y J' _ (fun _ => congrArg J' a₁)).symm))
  constructor
  · intro h
    refine corr_of_val hL' fun y J' hJ' => ?_
    choose J hJ using fun χ : Sp S ⟶ t.G.left => exists_chart hL (χ y)
    obtain ⟨k₁, k₂⟩ := key y J J' hJ hJ'
    exact mul_left_cancel (k₁.symm.trans ((val_corr hJ h _).trans k₂))
  · intro h
    refine corr_of_val hL fun y J hJ => ?_
    choose J' hJ' using fun χ : Sp S ⟶ t'.G.left => exists_chart hL' (χ y)
    obtain ⟨k₁, k₂⟩ := key y J J' hJ hJ'
    exact k₁.trans ((congrArg₂ (· * ·) rfl (val_corr hJ' h _)).trans k₂.symm)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RigidificationAtOriginIffPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidificationAtOrigin_iff_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (wP : PrimTyG t) (wP' : PrimTyG t'), wP.IsGen → wP'.IsGen → (∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun k => primφ t' k ≫ mp.φ) primε), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (LB.pullGen t.PP.L _ _ wP mp.φ) ∧ LB.Gen.Maps (LB.linCombIso w (primφ t') primε) wP' (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (act : 𝓞 E → Fin d → PS S 1 d), (homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) 0 →ₐ[S] S) ≫ x' 0 = 1) → (∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) → (Rig0G t x0 d x act e wP ↔ Rig0G t' (𝟙 (Sp S)) d x' act e' wP') := by
  first | exact @GlobalTheory.rigOrigin_iff_pullback | exact GlobalTheory.rigOrigin_iff_pullback | (intros; apply GlobalTheory.rigOrigin_iff_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsFrameGCoefficientRingBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsFrameGCoefficientRingBaseChange
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TripleFrameBaseChange

open MvPolynomial (X C)

theorem spec_comp {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem gm_unit_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (u : Aˣ) {Z : Scheme.{0}} (r : Z ⟶ Sp B)
    (z : Z) : gm r z ⊤ (unitΓ (Units.map f.toMonoidHom u)) = gm (r ≫ spMap f) z ⊤ (unitΓ u) := by
  refine Eq.trans ?_ (gm_pull r (spMap f) z ⊤ trivial (unitΓ u))
  refine congrArg (gm r z ⊤) (Units.ext ?_)
  exact congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}

theorem val_scale {Y Z : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ}
    {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) (c : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) :
    val (scaleGenG t φ ε c g) r z J = gm r z ⊤ c * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) c) rfl)

variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0)

def jetOver (d m n : ℕ) : jOG (spMap ψ ≫ x0) d m n ⟶ jOG x0 d m n :=
  Over.homMk (spMap (jetBC ψ (Fin n × Fin d) m)) (by
    dsimp
    simp only [spMap, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 3
    ext s
    exact jetBC_algebraMap ψ _ m s)

theorem psIn_map {d n n' : ℕ} (m : ℕ) (r : Fin n → Fin n') (f : MvPowerSeries (Fin n × Fin d) S) :
    psIn d m r (MvPowerSeries.map ψ f) = MvPolynomial.map ψ (psIn d m r f) := by
  unfold psIn
  rw [MvPolynomial.map_rename]
  congr 1
  unfold psTrunc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem subst_square {n n' d : ℕ} (m : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) :
    homAt (spMap ψ ≫ x0) (jetSubstP m (fun i => MvPolynomial.map ψ (φ i)) :
        Jet S' (Fin n × Fin d) m →ₐ[S'] Jet S' (Fin n' × Fin d) m) ≫ jetOver ψ x0 d m n =
      jetOver ψ x0 d m n' ≫ homAt x0 (jetSubstP m φ : Jet S (Fin n × Fin d) m →ₐ[S] Jet S (Fin n' × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ m) = spMap (jetBC ψ _ m) ≫ spMap _
  rw [spec_comp, spec_comp]
  exact congrArg spMap (PullbackSections.jetSubstP_comp_jetBC ψ m φ)

theorem jetMap_congr {R κ κ' : Type} [CommRing R] {m : ℕ} {f g : κ → MvPolynomial κ' R} (e : f = g)
    (hf : ∀ i, f i ∈ orig R κ') (hg : ∀ i, g i ∈ orig R κ') : jetMap (m := m) f hf = jetMap (m := m) g hg := by
  subst e
  rfl

theorem copy_square (d m n : ℕ) (i : Fin n) :
    homAt (spMap ψ ≫ x0) (jetCopy d m i : Jet S' (Fin 1 × Fin d) m →ₐ[S'] Jet S' (Fin n × Fin d) m) ≫
        jetOver ψ x0 d m 1 =
      jetOver ψ x0 d m n ≫ homAt x0 (jetCopy d m i : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetBC ψ _ m) = spMap (jetBC ψ _ m) ≫ spMap _
  rw [spec_comp, spec_comp]
  have e := PullbackSections.jetMap_comp_jetBC ψ m (fun p : Fin 1 × Fin d => (X (i, p.2) : MvPolynomial (Fin n × Fin d) S))
    (fun _ => X_mem_orig _) (fun p => by rw [MvPolynomial.map_X]; exact X_mem_orig _)
  rw [jetMap_congr (show (fun p : Fin 1 × Fin d => MvPolynomial.map ψ (X (i, p.2) : MvPolynomial (Fin n × Fin d) S)) =
    fun p => X (i, p.2) from funext fun p => MvPolynomial.map_X ψ _) _ (fun _ => X_mem_orig _)] at e
  exact congrArg spMap e

variable {ψ x0} {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {x' : ∀ m, jOG (spMap ψ ≫ x0) d m 1 ⟶ t.G}

theorem point_bc (hx : ∀ m, x' m = jetOver ψ x0 d m 1 ≫ x m) {n : ℕ} (m : ℕ) (i : Fin n) :
    jptG t (spMap ψ ≫ x0) d x' m i = jetOver ψ x0 d m n ≫ jptG t x0 d x m i := by
  unfold jptG
  rw [hx m, ← Category.assoc, copy_square, Category.assoc]

variable {e : ∀ m, FrTyG t x0 d x m} {e' : ∀ m, FrTyG t (spMap ψ ≫ x0) d x' m} {m : ℕ}
  (hc : LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L
    (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m) (jetOver ψ x0 d m 2).left))
  {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J)
include hc hJ

theorem val_subst {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S)
    (φ' : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S') (hφ : ∀ i j, φ' i j = MvPolynomial.map ψ (φ i j))
    (r : Z ⟶ (jOG (spMap ψ ≫ x0) d m n).left) :
    val (peG t (spMap ψ ≫ x0) d x' e' m φ') r z J = val (peG t x0 d x e m φ) (r ≫ (jetOver ψ x0 d m n).left) z J := by
  obtain rfl : φ' = fun i j => MvPolynomial.map ψ (φ i j) := funext fun i => funext fun j => hφ i j
  refine (val_pull hJ _ _ _).trans ((val_corr hJ hc _).trans ((val_pull hJ _ _ _).trans
    (Eq.trans ?_ (val_pull hJ _ _ _).symm)))
  rw [Category.assoc, Category.assoc, ← Over.comp_left, ← Over.comp_left,
    subst_square ψ x0 m (fun p : Fin 2 × Fin d => φ p.1 p.2)]

end GlobalTheory.TripleFrameBaseChange

namespace GlobalTheory

open TripleFrameBaseChange
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X C)

theorem isFrameG_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0), x1 = spMap ψ ≫ x0 → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G), (∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t x1 d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L _ _ (e m) (spMap (jetCoef ψ (Fin 2 × Fin d) m)))) → ∀ (F : Fin d → PS S 2 d) (act : 𝓞 E → Fin d → PS S 1 d) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d) (ad : 𝓞 E → PS S 2 d), IsFrameG t x0 d x F act ph1 ph2 sy ad e → IsFrameG t x1 d x' (fun i => (MvPowerSeries.map ψ (F i))) (fun a i => (MvPowerSeries.map ψ (act a i))) (MvPowerSeries.map ψ ph1) (MvPowerSeries.map ψ ph2) (MvPowerSeries.map ψ sy) (fun a => (MvPowerSeries.map ψ (ad a))) e' := by
  intro E _ _ _ H X0 t S S' _ _ ψ x0 x1 h01 d x x' hx0 e e' _ he' hc0 F act ph1 ph2 sy ad h
  subst h01
  have hx : ∀ m, x' m = jetOver ψ x0 d m 1 ≫ x m := fun m => Over.OverMorphism.ext (hx0 m)
  have hc : ∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L
      (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m) (jetOver ψ x0 d m 2).left) := hc0
  have hX : ∀ {n : ℕ} (p : Fin n × Fin d), (X p : MvPolynomial (Fin n × Fin d) S') = MvPolynomial.map ψ (X p) :=
    fun p => (MvPolynomial.map_X ψ p).symm
  refine ⟨he', fun m => ?_, fun m => ?_, fun m => ?_, fun a => ?_⟩
  · obtain ⟨u, hu, hcor⟩ := h.ph1 m
    refine ⟨Units.map (jetBC ψ _ m).toMonoidHom u, (congrArg (jetBC ψ _ m) hu).trans (PullbackSections.jetBC_psJet ψ m ph1),
      corr_of_val t.PP.isLB fun y J hJ => ?_⟩
    have k := val_corr hJ hcor (𝟙 _ ≫ (jetOver ψ x0 d m 3).left)
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_pull hJ _ _ _).symm.trans (k.trans ?_)))
    · rw [point_bc hx, point_bc hx, point_bc hx, ← comp_lift, ← comp_lift, Over.comp_left, Category.assoc]
    · refine (val_scale hJ _ _ _).trans (Eq.trans ?_ (val_scale hJ _ _ _).symm)
      refine congrArg₂ (· * ·) (gm_unit_map _ u _ y).symm ?_
      refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (val_mul hJ _ _ _).symm)
      · exact (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => psIn_map ψ m _ _, fun j => hX _⟩) _).symm
      refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (val_mul hJ _ _ _).symm)
      all_goals
        exact (val_inv _ _).trans ((congrArg (·⁻¹)
          (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => hX _, fun j => hX _⟩) _).symm).trans
          (val_inv _ _).symm)
  · obtain ⟨u, hu, hcor⟩ := h.ph2 m
    refine ⟨Units.map (jetBC ψ _ m).toMonoidHom u, (congrArg (jetBC ψ _ m) hu).trans (PullbackSections.jetBC_psJet ψ m ph2),
      corr_of_val t.PP.isLB fun y J hJ => ?_⟩
    have k := val_corr hJ hcor (𝟙 _ ≫ (jetOver ψ x0 d m 3).left)
    refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_pull hJ _ _ _).symm.trans (k.trans ?_)))
    · rw [point_bc hx, point_bc hx, point_bc hx, ← comp_lift, ← comp_lift, Over.comp_left, Category.assoc]
    · refine (val_scale hJ _ _ _).trans (Eq.trans ?_ (val_scale hJ _ _ _).symm)
      refine congrArg₂ (· * ·) (gm_unit_map _ u _ y).symm ?_
      refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (val_mul hJ _ _ _).symm)
      · exact (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => hX _, fun j => psIn_map ψ m _ _⟩) _).symm
      refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) (val_mul hJ _ _ _).symm)
      all_goals
        exact (val_inv _ _).trans ((congrArg (·⁻¹)
          (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => hX _, fun j => hX _⟩) _).symm).trans
          (val_inv _ _).symm)
  · obtain ⟨u, hu, hcor⟩ := h.sy m
    refine ⟨Units.map (jetBC ψ _ m).toMonoidHom u, (congrArg (jetBC ψ _ m) hu).trans (PullbackSections.jetBC_psJet ψ m sy),
      corr_of_val t.PP.isLB fun y J hJ => ?_⟩
    have k := val_corr hJ hcor (𝟙 _ ≫ (jetOver ψ x0 d m 2).left)
    refine (val_corr hJ (hc m) _).trans ((val_pull hJ _ _ _).trans (k.trans ?_))
    refine (val_scale hJ _ _ _).trans (Eq.trans ?_ (val_scale hJ _ _ _).symm)
    refine congrArg₂ (· * ·) (gm_unit_map _ u⁻¹ _ y).symm ?_
    exact (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => hX _, fun j => hX _⟩) _).symm
  · obtain ⟨wL, hw, hall⟩ := h.ad a
    refine ⟨wL, hw, fun m => ?_⟩
    obtain ⟨u, hu, hcor⟩ := hall m
    refine ⟨Units.map (jetBC ψ _ m).toMonoidHom u, (congrArg (jetBC ψ _ m) hu).trans (PullbackSections.jetBC_psJet ψ m (ad a)),
      corr_of_val t.PP.isLB fun y J hJ => ?_⟩
    have k := val_corr hJ hcor (𝟙 _ ≫ (jetOver ψ x0 d m 2).left)
    refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ ?_) ((val_mul hJ _ _ _).symm.trans (k.trans ?_)))
    · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
      rw [point_bc hx, point_bc hx, ← comp_lift, Over.comp_left, Category.assoc]
    · exact val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => psIn_map ψ m _ _, fun j => hX _⟩) _
    · refine (val_scale hJ _ _ _).trans (Eq.trans ?_ (val_scale hJ _ _ _).symm)
      refine congrArg₂ (· * ·) (gm_unit_map _ u _ y).symm ?_
      exact (val_subst (hc m) hJ _ _ (Fin.forall_fin_two.2 ⟨fun j => hX _, fun j => psIn_map ψ m _ _⟩) _).symm

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsFrameGCoefficientRingBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFrameG_coefficientRing_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0), x1 = spMap ψ ≫ x0 → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G), (∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t x1 d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L _ _ (e m) (spMap (jetCoef ψ (Fin 2 × Fin d) m)))) → ∀ (F : Fin d → PS S 2 d) (act : 𝓞 E → Fin d → PS S 1 d) (ph1 ph2 : PS S 3 d) (sy : PS S 2 d) (ad : 𝓞 E → PS S 2 d), IsFrameG t x0 d x F act ph1 ph2 sy ad e → IsFrameG t x1 d x' (fun i => (MvPowerSeries.map ψ (F i))) (fun a i => (MvPowerSeries.map ψ (act a i))) (MvPowerSeries.map ψ ph1) (MvPowerSeries.map ψ ph2) (MvPowerSeries.map ψ sy) (fun a => (MvPowerSeries.map ψ (ad a))) e' := by
  first | exact @GlobalTheory.isFrameG_baseChange | exact GlobalTheory.isFrameG_baseChange | (intros; apply GlobalTheory.isFrameG_baseChange <;> assumption)
end
end
