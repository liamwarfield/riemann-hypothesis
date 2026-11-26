module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsSecondPartialLaw
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.PushChart
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ChartsWithFramesRelatedAllOrders

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FamSyPush
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FamSyPush
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
namespace GlobalTheory.PushSym

theorem val_carries {X X' Y Z : Scheme.{0}} {L' : LB X'} (L : LB X) (F : X' ⟶ X) (w : LB.Iso L' (L.pull F))
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X')) (ε : K → ℤ) (g : LB.Gen (LB.LinComb L' φ ε))
    (g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)) (h : Carries L F w φ ε g g') (r : Z ⟶ Y) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) {J' : (Z ⟶ X') → L'.ι} (hJ' : Good L' z J') :
    val g' r z J = (∏ k, gm (r ≫ φ k) z ((L.pull F).U (fun _ => J ((r ≫ φ k) ≫ F)) ⊓ L'.U (J' (r ≫ φ k)))
      (w.s (fun _ => J ((r ≫ φ k) ≫ F), J' (r ≫ φ k))) ^ ε k) * val g r z J' := by
  have m1 : ∀ k, (r ≫ φ k) z ∈ (L.pull F).U (fun _ => J ((r ≫ φ k) ≫ F)) := fun k =>
    Set.mem_iInter.2 fun _ => hJ ((r ≫ φ k) ≫ F)
  have hm : r z ∈ LB.wchart (L.pull F) φ (fun k _ => J ((r ≫ φ k) ≫ F)) ⊓ LB.wchart L' φ (fun k => J' (r ≫ φ k)) :=
    ⟨Set.mem_iInter.2 m1, hJ'.mem φ r⟩
  have e := congrArg (gm r z (LB.wchart (L.pull F) φ (fun k _ => J ((r ≫ φ k) ≫ F)) ⊓
    LB.wchart L' φ (fun k => J' (r ≫ φ k)))) (h (fun k _ => J ((r ≫ φ k) ≫ F), fun k => J' (r ≫ φ k)))
  rw [val_of g' r z J (fun k => J ((r ≫ φ k) ≫ F)) (fun k => by rw [Category.assoc])]
  refine ((gm_res r z _ hm _).trans (gm_res r z _ hm.1 _)).symm.trans (e.trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  exact (gm_res r z _ hm _).trans (gm_pull r (φ k) z ((L.pull F).U (fun _ => J ((r ≫ φ k) ≫ F)) ⊓ L'.U (J' (r ≫ φ k)))
    ⟨m1 k, hJ' (r ≫ φ k)⟩ _)

theorem val_scaleGenG {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {Y Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ) (u : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) :
    val (scaleGenG t φ ε u g) r z J = gm r z ⊤ u * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ (hJ.mem φ r) _) rfl)

theorem prod_swap {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {T : Over X0} (a b : T ⟶ t.G) (s : T ⟶ T) (ha : s ≫ a = b) (hb : s ≫ b = a) {U : Type} [CommGroup U]
    (h : (T.left ⟶ t.G.left) → U) :
    ∏ k, h (s.left ≫ cφG t ![a, b] k) ^ cε 2 k = ∏ k, h (cφG t ![a, b] k) ^ cε 2 k := by
  have e : ∀ k, s.left ≫ cφG t ![a, b] k = cφG t ![b, a] k := fun k => by
    have := psum_hom (preHom (G := t.G) s) ![a, b] k.down
    have e2 : (fun i => preHom (G := t.G) s (![a, b] i)) = ![b, a] := by
      funext i; fin_cases i
      exacts [ha, hb]
    rw [e2] at this
    exact congrArg (fun q => q.left) this
  refine (Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ cε 2 k) (e k)).trans ?_
  refine (prod_cube₂ b a h).trans (Eq.trans ?_ (prod_cube₂ a b h).symm)
  rw [_root_.mul_comm b a, mul_right_comm (h (a * b).left)]

theorem famSy_push : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), CubIso n w → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → PushFr n w x x' e e' → ∀ sy : PS V 2 d, FamSy t (𝟙 (Sp V)) d x sy e → FamSy t' (𝟙 (Sp V)) d x' sy e' := by
  intro E _ _ _ H V _ t t' n w d x x' e e' _ _ _ hP sy hs m
  obtain ⟨u, hu, hc⟩ := hs m
  obtain ⟨-, c, -, hce, hcar⟩ := hP m
  refine ⟨u, hu, corr_of_val t'.PP.isLB fun y J hJ => ?_⟩
  choose J' hJ' using fun χ : (jOG (𝟙 (Sp V)) d m 2).left ⟶ t.G.left => exists_chart t.PP.isLB (χ y)
  have hJ'' : Good t.PP.L y J' := hJ'
  have hsub : (fun p : Fin 2 × Fin d => (![fun j => MvPolynomial.X ((1 : Fin 2), j), fun j => MvPolynomial.X ((0 : Fin 2), j)] :
      Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) V) p.1 p.2) = Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh.rel d ![1, 0] := by
    funext ⟨i, j⟩; fin_cases i <;> rfl
  have k := (val_corr hJ'' hc (𝟙 _)).trans ((val_scaleGenG t _ _ _ _ _ y hJ'').trans
    (congrArg₂ (· * ·) rfl (val_pull hJ'' _ _ _)))
  refine Eq.trans ?_ ((val_scaleGenG t' _ _ _ _ _ y hJ).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm
  have v := fun r : (jOG (𝟙 (Sp V)) d m 2).left ⟶ (jOG (𝟙 (Sp V)) d m 2).left =>
    (val_corr hJ hce r).symm.trans (val_carries _ _ w _ _ _ _ hcar r y hJ hJ'')
  refine (v _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (v _)).symm)
  refine (congrArg₂ (· * ·) ?_ k).trans (mul_left_comm _ _ _)
  have p := (prod_swap t _ _ _ (Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh.relabel_jpt t (𝟙 (Sp V)) d x m ![1, 0] 0)
    (Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh.relabel_jpt t (𝟙 (Sp V)) d x m ![1, 0] 1)
    (fun ψ => gm ψ y ((t'.PP.L.pull n.φ).U (fun _ => J (ψ ≫ n.φ)) ⊓ t.PP.L.U (J' ψ)) (w.s (fun _ => J (ψ ≫ n.φ), J' ψ)))).symm
  rw [← hsub] at p
  refine Eq.trans (Finset.prod_congr rfl fun k _ => ?_) (p.trans (Finset.prod_congr rfl fun k _ => ?_))
  · rw [Category.id_comp]; rfl
  · rw [Category.id_comp]; rfl

end GlobalTheory.PushSym
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FamSyPushStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.famSy_of_pushFr_cubIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), CubIso n w → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → PushFr n w x x' e e' → ∀ sy : PS V 2 d, FamSy t (𝟙 (Sp V)) d x sy e → FamSy t' (𝟙 (Sp V)) d x' sy e' := by
  first | exact @GlobalTheory.PushSym.famSy_push | exact GlobalTheory.PushSym.famSy_push | (intros; apply GlobalTheory.PushSym.famSy_push <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsPushFr
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsPushFr
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem exists_corr_of_family_eq {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)}
    (h : φ = φ') (ε : K → ℤ) (c : LB.Gen (LB.LinComb L φ ε)) (hc : c.IsGen) :
    ∃ c' : LB.Gen (LB.LinComb L φ' ε), c'.IsGen ∧ LB.Gen.Corr L _ _ _ _ c c' := by
  subst h
  refine ⟨c, hc, fun j j' _ _ hj => ?_⟩
  obtain rfl : j = j' := funext fun k => hj k k rfl
  rfl

theorem exists_pushFr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m), w.IsGen → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → ∃ e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m, PushFr n w x x' e e' := by
  intro E _ _ _ H V _ t t' n w d x x' e hw hx he
  obtain ⟨ψ, hψ, hmon, -⟩ := GlobalTheory.T.exists_groupIso_cubicalIso_of_tripleMap_id E H V t t' n
  haveI : IsIso n.φ := by
    rw [← hψ]
    exact inferInstanceAs (IsIso ((Over.forget _).map ψ.hom))
  have hcar := (GlobalTheory.T.carriesLinCombGenerator_calculus _ _ t.PP.L t'.PP.L n.φ w t.PP.isLB t'.PP.isLB hw).1
  have hx' : ∀ m, x' m = x m ≫ ψ.hom := fun m => by
    ext1
    rw [hx, Over.comp_left, hψ]
  have hfam : ∀ m, (fun J => cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] J ≫ n.φ) =
      cφG t' ![jptG t' (𝟙 (Sp V)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp V)) d x' m (1 : Fin 2)] := fun m => by
    funext J
    have hv : (![jptG t' (𝟙 (Sp V)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp V)) d x' m (1 : Fin 2)] : Fin 2 → _) =
        fun k => (![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] : Fin 2 → _) k ≫ ψ.hom := by
      funext k
      fin_cases k <;> simp [jptG, hx']
    rw [hv]
    simp only [cφG, psum]
    rw [← hψ, ← Over.comp_left, foldr_padd_comp]
  have key : ∀ m, ∃ e' : FrTyG t' (𝟙 (Sp V)) d x' m, e'.IsGen ∧ ∃ c : LB.Gen (LB.LinComb t'.PP.L
      (fun J => cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] J ≫ n.φ) (cε 2)),
      c.IsGen ∧ LB.Gen.Corr t'.PP.L _ _ _ _ c e' ∧
      Carries t'.PP.L n.φ w (cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)])
        (cε 2) (e m) c := fun m => by
    obtain ⟨c, hc, hcc⟩ := hcar _ _
      (cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)]) (cε 2) (e m) (he m)
    obtain ⟨e', he', hce⟩ := exists_corr_of_family_eq t'.PP.L (hfam m) (cε 2) c hc
    exact ⟨e', he', c, hc, hce, hcc⟩
  choose e' he' using key
  exact ⟨e', he'⟩

end GlobalTheory.ChartCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsPushFrStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pushFr_of_isGen : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m), w.IsGen → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → ∃ e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m, PushFr n w x x' e e' := by
  first | exact @GlobalTheory.ChartCmp.exists_pushFr | exact GlobalTheory.ChartCmp.exists_pushFr | (intros; apply GlobalTheory.ChartCmp.exists_pushFr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AdjointnessSeriesTransportFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AdjointnessSeriesTransportFrames
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp.PushAd

section Bundles
variable {X X' Y : Scheme.{0}} {L' : LB X'} {L : LB X} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
  {K : Type} [Fintype K] {φ : K → (Y ⟶ X')} {ε : K → ℤ}

def wv {Z : Scheme.{0}} (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) (χ : Z ⟶ X') : (Z.presheaf.stalk z)ˣ :=
  gw w χ z (J (χ ≫ F)) (J' χ)

theorem val_carries {g : LB.Gen (LB.LinComb L' φ ε)} {g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)}
    (h : Carries L F w φ ε g g') {Z : Scheme.{0}} (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι} {J' : (Z ⟶ X') → L'.ι}
    (hJ : Good L z J) (hJ' : Good L' z J') :
    val g' r z J = (∏ k, wv w z J J' (r ≫ φ k) ^ ε k) * val g r z J' := by
  have H := (maps_iff w φ (fun k => φ k ≫ F) ε g g' (𝟙 Y) (flatGen L F φ ε g') (wchart_pull_le L F φ)
    (fun j => congrArg (res (wchart_pull_le L F φ j)) (Units.ext rfl)) ).1 h Z r z
    (fun k => J ((r ≫ φ k) ≫ F)) (fun k => J' (r ≫ φ k)) (fun k => hJ ((r ≫ φ k) ≫ F)) (fun k => hJ' (r ≫ φ k))
  rw [Category.comp_id] at H
  rw [val_of g' r z J (fun k => J ((r ≫ φ k) ≫ F)) (fun k => by rw [Category.assoc])]
  exact H

theorem carried_trans (hw : w.IsGen) {g : LB.Gen (LB.LinComb L' φ ε)} (hg : g.IsGen) {Z : Scheme.{0}} (r : Z ⟶ Y)
    (z : Z) (p p' : K → L.ι) (q q' : K → L'.ι) (hp : r z ∈ LB.wchart L (fun k => φ k ≫ F) p)
    (hp' : r z ∈ LB.wchart L (fun k => φ k ≫ F) p') (hq : r z ∈ LB.wchart L' φ q) (hq' : r z ∈ LB.wchart L' φ q') :
    (∏ k, gw w (r ≫ φ k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart L' φ q) (g.s q) =
      trF (fun k => φ k ≫ F) ε r z p p' *
        ((∏ k, gw w (r ≫ φ k) z (p' k) (q' k) ^ ε k) * gm r z (LB.wchart L' φ q') (g.s q')) := by
  rw [gen_trans hg r z hq hq', ← _root_.mul_assoc, ← _root_.mul_assoc, trF, trF, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)
  rw [← mul_zpow, ← mul_zpow, (isGen_iff w).1 hw Z (r ≫ φ k) z (p k) (p' k) (q k) (q' k) (Set.mem_iInter.1 hp k)
    (Set.mem_iInter.1 hp' k) (Set.mem_iInter.1 hq k) (Set.mem_iInter.1 hq' k), Category.assoc, mul_right_comm _ (gw _ _ _ _ _),
    inv_mul_cancel_right]

theorem exists_carried (hL' : L'.IsLB) (hL : L.IsLB) (hw : w.IsGen) {g : LB.Gen (LB.LinComb L' φ ε)} (hg : g.IsGen) :
    ∃ g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε), g'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι), Good L z J → Good L' z J' →
        val g' r z J = (∏ k, wv w z J J' (r ≫ φ k) ^ ε k) * val g r z J' := by
  have glue : ∀ p : K → L.ι, ∃ a : Γ(Y, LB.wchart L (fun k => φ k ≫ F) p)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z)
      (q : K → L'.ι), r z ∈ LB.wchart L (fun k => φ k ≫ F) p → r z ∈ LB.wchart L' φ q →
      gm r z _ a = (∏ k, gw w (r ≫ φ k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart L' φ q) (g.s q) := by
    intro p
    let W : (K → L'.ι) → Y.Opens := fun q => LB.wchart L (fun k => φ k ≫ F) p ⊓ LB.wchart L' φ q
    have le : ∀ q k, W q ≤ φ k ⁻¹ᵁ ((L.pull F).U (fun _ => p k) ⊓ L'.U (q k)) := fun q k y hy =>
      ⟨mem_pull.2 (Set.mem_iInter.1 hy.1 k), Set.mem_iInter.1 hy.2 k⟩
    obtain ⟨u, hu⟩ : ∃ u : ∀ q, Γ(Y, W q)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q, r z ∈ W q →
        gm r z (W q) (u q) = (∏ k, gw w (r ≫ φ k) z (p k) (q k) ^ ε k) * gm r z (LB.wchart L' φ q) (g.s q) :=
      ⟨fun q => (∏ k, res (le q k) (pullU (φ k) _ (w.s (fun _ => p k, q k))) ^ ε k) *
          res (inf_le_right : W q ≤ LB.wchart L' φ q) (g.s q), fun Z r z q hz =>
        (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ =>
          (map_zpow _ _ _).trans (congrArg (· ^ ε k) ((gm_res r z _ hz _).trans
            (gm_pull r (φ k) z ((L.pull F).U (fun _ => p k) ⊓ L'.U (q k)) (le q k hz) _))))) (gm_res r z _ hz _))⟩
    obtain ⟨a, ha⟩ := glue_unit (LB.wchart L (fun k => φ k ≫ F) p) W (fun q => inf_le_left) (fun y hy => by
        choose q hq using fun k => exists_chart hL' (φ k y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨q, hy, Set.mem_iInter.2 hq⟩) u (fun q q' y hy => by
        rw [hu _ _ y q hy.1, hu _ _ y q' hy.2, carried_trans w hw hg (𝟙 Y) y p p q q' hy.1.1 hy.1.1 hy.1.2 hy.2.2,
          mul_eq_left.1 (trF_trans hL _ ε (𝟙 Y) y hy.1.1 hy.1.1 hy.1.1), _root_.one_mul])
    refine ⟨a, fun Z r z q h₁ h₂ => ?_⟩
    have hz : r z ∈ W q := ⟨h₁, h₂⟩
    exact (gm_res r z inf_le_left hz a).symm.trans ((congrArg (gm r z (W q)) (ha q)).trans (hu Z r z q hz))
  choose a ha using glue
  refine ⟨⟨a⟩, fun p p' => unit_ext fun y hy => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · choose q hq using fun k => exists_chart hL' (φ k y)
    have m : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L' φ q := Set.mem_iInter.2 hq
    refine (gm_res (𝟙 Y) y _ hy _).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (gm_linComb L _ ε (𝟙 Y) y p p' hy.1 hy.2) ((gm_res (𝟙 Y) y _ hy _).trans (ha p' _ (𝟙 Y) y q hy.2 m)))).symm)
    exact (ha p _ (𝟙 Y) y q hy.1 m).trans (carried_trans w hw hg (𝟙 Y) y p p' q q hy.1 hy.2 m m)
  · refine (ha _ Z r z _ (hJ.mem _ r) (hJ'.mem φ r)).trans ?_
    simp only [wv, Category.assoc]
    rfl

end Bundles

section Points
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}}

theorem cube_pre (t : SAB H X0) {T T' : Over X0} (h : T' ⟶ T) (a b : T ⟶ t.G) (I : ULift (Finset (Fin 2))) :
    h.left ≫ cφG t ![a, b] I = cφG t ![h ≫ a, h ≫ b] I := by
  rw [show (![h ≫ a, h ≫ b] : Fin 2 → (T' ⟶ t.G)) = fun i => h ≫ ![a, b] i from funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)]
  exact congrArg (fun z => z.left) (foldr_padd_pre h ![a, b] _).symm

theorem cube_push (t t' : SAB H X0) (f : t.G ⟶ t'.G) [IsMonHom f] {T : Over X0} (a b : T ⟶ t.G)
    (I : ULift (Finset (Fin 2))) : cφG t ![a, b] I ≫ f.left = cφG t' ![a ≫ f, b ≫ f] I := by
  rw [show (![a ≫ f, b ≫ f] : Fin 2 → (T ⟶ t'.G)) = fun i => ![a, b] i ≫ f from funext (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)]
  exact congrArg (fun z => z.left) (foldr_padd_comp f ![a, b] _)

theorem val_scale (t : SAB H X0) {Y Z : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ}
    {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) (c : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) :
    val (scaleGenG t φ ε c g) r z J = gm r z ⊤ c * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) c) rfl)

theorem subst_act (t : SAB H X0) {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)
    {n n' : ℕ} (m : ℕ) (f : Fin d → MvPowerSeries (Fin 1 × Fin d) S) (α : t.G ⟶ t.G)
    (hα : x m ≫ α = Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (f p.2)) ≫ x m)
    (ψ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) (i : Fin n) (k : Fin n')
    (h : ∀ j, ψ (i, j) = psIn d m ![k] (f j)) :
    Formalism.L2.Pj.homAt x0 (jetSubstP m ψ) ≫ jptG t x0 d x m i = jptG t x0 d x m k ≫ α := by
  rw [jptG, jptG, Category.assoc, hα, ← Category.assoc, ← Category.assoc, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_comp,
    Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.homAt_comp]
  congr 2
  apply Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jet_hom_ext
  rintro ⟨i0, j⟩
  have e : (fun p : Fin 1 × Fin d => (MvPolynomial.X (k, p.2) : MvPolynomial (Fin n' × Fin d) S)) =
      MvPolynomial.X ∘ fun p : Fin 1 × Fin d => ((![k] : Fin 1 → Fin n') p.1, p.2) := by
    funext p
    simp
  simp only [AlgHom.comp_apply, jetCopy, jetSubstP, Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.jetMap_mk, MvPolynomial.aeval_X, h, psIn,
    MvPolynomial.constantCoeff_rename, map_sub, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  rw [e, ← MvPolynomial.rename_eq_aeval]

end Points

theorem famAd_push : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), CubIso n w → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → PushFr n w x x' e e' → ∀ (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (ad : 𝓞 E → PS V 2 d), IsChartG t (𝟙 (Sp V)) d F act tg uv x → FamAd t (𝟙 (Sp V)) d x act ad e → FamAd t' (𝟙 (Sp V)) d x' act ad e' := by
  intro E _ _ _ H V _ t t' n w d x x' e e' hcub hx _ hpush F act κ _ tg uv ad hch had a
  obtain ⟨ψ, hψ, hmon, hact, -, -⟩ := exists_iso_of_sabMap_id E H V t t' n
  have hx' : ∀ m, x' m = x m ≫ ψ.hom := fun m => Over.OverMorphism.ext (by rw [hx m, Over.comp_left, hψ])
  have hj : ∀ m (i : Fin 2), jptG t' (𝟙 (Sp V)) d x' m i = jptG t (𝟙 (Sp V)) d x m i ≫ ψ.hom := fun m i => by
    rw [jptG, jptG, hx' m, Category.assoc]
  obtain ⟨wL, hwL, hall⟩ := had a
  obtain ⟨wc, hwc, vc⟩ := exists_carried w t.PP.isLB t'.PP.isLB hcub.1 hwL
  have hinv : ∀ b, ψ.inv ≫ t.act.act b ≫ ψ.hom = t'.act.act b := fun b => by
    rw [hact b, Iso.inv_hom_id_assoc]
  have hfam : (fun k => (ψ.inv ⊗ₘ ψ.inv).left ≫
      Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
        (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G]) k ≫ n.φ) =
      Sum.elim (cφG t' ![fst t'.G t'.G, snd t'.G t'.G ≫ t'.act.act (H.bar a)])
        (cφG t' ![fst t'.G t'.G ≫ t'.act.act a, snd t'.G t'.G]) := by
    funext k
    rcases k with I | I
    all_goals
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [← hψ, cube_push, cube_pre]
      simp [hinv]
  obtain ⟨wL', hwL', vL⟩ := exists_gen t'.PP.isLB (fun U _ h => Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ _) (congrFun hfam k))
    (LB.pullGen t'.PP.L _ _ wc (ψ.inv ⊗ₘ ψ.inv).left) (DVR.pullGen_isGen _ _ _ _ hwc _)
  refine ⟨wL', hwL', fun m => ?_⟩
  obtain ⟨u, hu, hcor⟩ := hall m
  obtain ⟨-, c, -, hc, hcar⟩ := hpush m
  refine ⟨u, hu, corr_of_val t'.PP.isLB fun y J hJ => ?_⟩
  choose J' hJ' using fun χ : _ ⟶ t.G.left => exists_chart t.PP.isLB (χ y)
  have hJ' : Good t.PP.L y J' := hJ'
  have k := val_corr hJ' hcor (𝟙 _)
  have hpe : ∀ φ : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) V,
      val (peG t' (𝟙 (Sp V)) d x' e' m φ) (𝟙 _) y J =
        (∏ I, wv w y J J' ((Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left ≫
          cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] I) ^ cε 2 I) *
        val (peG t (𝟙 (Sp V)) d x e m φ) (𝟙 _) y J' := fun φ => by
    refine (val_pull hJ _ _ _).trans ((val_corr hJ hc _).symm.trans ((val_carries w hcar _ hJ hJ').trans ?_))
    exact congrArg₂ (· * ·) (by rw [Category.id_comp]) (val_pull hJ' _ _ _).symm
  rw [val_mul hJ', val_scale t hJ', val_pull hJ'] at k
  rw [val_mul hJ, val_scale t' hJ, val_pull hJ, vL _ _ _ _ hJ, val_pull hJ, hpe, hpe, vc _ _ _ _ _ hJ hJ']
  have hl : (lift (jptG t' (𝟙 (Sp V)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp V)) d x' m (1 : Fin 2))).left ≫
      (ψ.inv ⊗ₘ ψ.inv).left = (lift (jptG t (𝟙 (Sp V)) d x m (0 : Fin 2)) (jptG t (𝟙 (Sp V)) d x m (1 : Fin 2))).left := by
    rw [← Over.comp_left, lift_map, hj, hj]
    simp
  simp only [Category.id_comp] at k ⊢
  rw [hl, _root_.mul_mul_mul_comm, k, mul_left_comm]
  refine congrArg (_ * ·) (congrArg (· * _) ?_)
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, cube_pre]
  rw [subst_act t _ d x m (act a) _ (hch.act m a) _ 0 0 (fun j => rfl),
    Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh.subst_jpt t _ d x m _ 1 1 ?h1,
    Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdPh.subst_jpt t _ d x m _ 0 0 ?h2,
    subst_act t _ d x m (act (H.bar a)) _ (hch.act m (H.bar a)) _ 1 1 (fun j => rfl)]
  case h1 => exact fun j => rfl
  case h2 => exact fun j => rfl
  simp only [lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, zpow_neg, Finset.prod_inv_distrib,
    inv_mul_cancel_right]

end GlobalTheory.ChartCmp.PushAd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.AdjointnessSeriesTransportFramesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjointness_series_transport_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), CubIso n w → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → PushFr n w x x' e e' → ∀ (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (ad : 𝓞 E → PS V 2 d), IsChartG t (𝟙 (Sp V)) d F act tg uv x → FamAd t (𝟙 (Sp V)) d x act ad e → FamAd t' (𝟙 (Sp V)) d x' act ad e' := by
  first | exact @GlobalTheory.ChartCmp.PushAd.famAd_push | exact GlobalTheory.ChartCmp.PushAd.famAd_push | (intros; apply GlobalTheory.ChartCmp.PushAd.famAd_push <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FirstPartialLawPushAlongTripleMap
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FirstPartialLawPushAlongTripleMap
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.PushFirstLaw

section Val
variable {X X' Y Z : Scheme.{0}} {L' : LB X'} {L : LB X} {F : X' ⟶ X} (w : LB.Iso L' (L.pull F))
  (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι)

def isoVal (ψ : Z ⟶ X') : (Z.presheaf.stalk z)ˣ :=
  gm ψ z ((LB.div (L.pull F) L').U (fun _ => J (ψ ≫ F), J' ψ)) (w.s (fun _ => J (ψ ≫ F), J' ψ))

variable {w z J J'}

theorem val_maps (hJ : Good L z J) (hJ' : Good L' z J') {K : Type} [Fintype K] {φ : K → (Y ⟶ X')} {ε : K → ℤ}
    {g : LB.Gen (LB.LinComb L' φ ε)} {b : LB.Gen (LB.LinComb (L.pull F) φ ε)}
    (h : LB.Gen.Maps (LB.linCombIso w φ ε) g b) (r : Z ⟶ Y) :
    gm r z (LB.wchart (L.pull F) φ fun k _ => J ((r ≫ φ k) ≫ F)) (b.s fun k _ => J ((r ≫ φ k) ≫ F)) =
      (∏ k, isoVal w z J J' (r ≫ φ k) ^ ε k) * val g r z J' := by
  have h1 : r z ∈ LB.wchart (L.pull F) φ fun k _ => J ((r ≫ φ k) ≫ F) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => hJ ((r ≫ φ k) ≫ F)
  have hm : r z ∈ LB.wchart (L.pull F) φ (fun k _ => J ((r ≫ φ k) ≫ F)) ⊓ LB.wchart L' φ (fun k => J' (r ≫ φ k)) :=
    ⟨h1, hJ'.mem φ r⟩
  refine (gm_res r z _ hm _).symm.trans ((congrArg (gm r z _)
    (h (fun k _ => J ((r ≫ φ k) ≫ F), fun k => J' (r ≫ φ k)))).trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) ?_ (gm_res r z _ hm _))))
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun a _ => (map_zpow _ _ _).trans (congrArg (· ^ ε a) ?_))
  have ha : (φ a) (r z) ∈ (L.pull F).U (fun _ => J ((r ≫ φ a) ≫ F)) ⊓ L'.U (J' (r ≫ φ a)) :=
    ⟨LB.wchart_le (L.pull F) φ _ a hm.1, LB.wchart_le L' φ _ a hm.2⟩
  exact (gm_res r z _ hm _).trans (gm_pull r (φ a) z _ ha _)

theorem val_carries (hJ : Good L z J) (hJ' : Good L' z J') {K : Type} [Fintype K] {φ : K → (Y ⟶ X')} {ε : K → ℤ}
    {g : LB.Gen (LB.LinComb L' φ ε)} {g' : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε)}
    (h : Carries L F w φ ε g g') (r : Z ⟶ Y) :
    val g' r z J = (∏ k, isoVal w z J J' (r ≫ φ k) ^ ε k) * val g r z J' := by
  refine Eq.trans ?_ (val_maps hJ hJ' h r)
  rw [val_of g' r z J (fun k => J ((r ≫ φ k) ≫ F)) (fun k => by rw [Category.assoc])]
  have h1 : r z ∈ LB.wchart (L.pull F) φ fun k _ => J ((r ≫ φ k) ≫ F) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => hJ ((r ≫ φ k) ≫ F)
  exact (gm_res r z _ h1 _).symm

end Val

section Cube
variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]

theorem val_theta (m : CubeMap G' G) {L : LB G.left} {L' : LB G'.left} {w : LB.Iso L' (L.pull m.F)}
    {c : LB.Gen (Theta G L)} {c' : LB.Gen (Theta G' L')}
    (h : LB.Gen.Maps (LB.linCombIso w (thφ G' (x3 G')) thε) c' (m.thetaPull L c))
    {Z : Scheme.{0}} {z : Z} {J : (Z ⟶ G.left) → L.ι} {J' : (Z ⟶ G'.left) → L'.ι} (hJ : Good L z J) (hJ' : Good L' z J')
    (r : Z ⟶ (G3 G').left) :
    val (φ := thφ G (x3 G)) (ε := thε) c (r ≫ m.F3) z J =
      (∏ k, isoVal w z J J' (r ≫ thφ G' (x3 G') k) ^ thε k) * val (φ := thφ G' (x3 G')) (ε := thε) c' r z J' := by
  refine Eq.trans ?_ (val_maps hJ hJ' h r)
  have e : ∀ k : thK, (r ≫ m.F3) ≫ thφ G (x3 G) k = (r ≫ thφ G' (x3 G') k) ≫ m.F := fun k => by
    rw [Category.assoc, Category.assoc]
    exact congrArg (r ≫ ·) (m.psum_comm k.down).symm
  refine (val_of (φ := thφ G (x3 G)) (ε := thε) c (r ≫ m.F3) z J (fun k => J ((r ≫ thφ G' (x3 G') k) ≫ m.F))
    (fun k => by rw [e])).trans ?_
  have h1 : r z ∈ LB.wchart (L.pull m.F) (thφ G' (x3 G')) fun k _ => J ((r ≫ thφ G' (x3 G') k) ≫ m.F) :=
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => hJ ((r ≫ thφ G' (x3 G') k) ≫ m.F)
  exact ((gm_res r z _ h1 _).trans (gm_pull r m.F3 z _ (m.theta_le L _ h1) _)).symm

end Cube

theorem lift_cubeMap {S : Scheme.{0}} {G' G T : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (m : CubeMap G' G) (a : Fin 3 → (T ⟶ G')) (b : Fin 3 → (T ⟶ G)) (h : ∀ i, (b i).left = (a i).left ≫ m.F) :
    (lift (b 0) (lift (b 1) (b 2))).left = (lift (a 0) (lift (a 1) (a 2))).left ≫ m.F3 := by
  have k : ∀ i : Fin 3, (x3 G' i).left ≫ m.F = m.F3 ≫ (x3 G i).left := fun i => by
    have e := m.psum_comm {i}
    have p : psum G (x3 G) {i} = x3 G i * 1 := by fin_cases i <;> rfl
    have p' : psum G' (x3 G') {i} = x3 G' i * 1 := by fin_cases i <;> rfl
    rwa [p, p', _root_.mul_one, _root_.mul_one] at e
  have la : ∀ i : Fin 3, lift (a 0) (lift (a 1) (a 2)) ≫ x3 G' i = a i := fun i => by
    fin_cases i <;> simp [x3]
  have k' : ∀ i : Fin 3, ((lift (a 0) (lift (a 1) (a 2))).left ≫ m.F3) ≫ (x3 G i).left = (b i).left := fun i => by
    rw [Category.assoc, ← k, ← Category.assoc, ← Over.comp_left, la, h]
  let q : T ⟶ G3 G := Over.homMk ((lift (a 0) (lift (a 1) (a 2))).left ≫ m.F3) (by
    rw [← Over.w (x3 G 0), ← Category.assoc, k', Over.w])
  have hq : ∀ i : Fin 3, q ≫ x3 G i = b i := fun i => Over.OverMorphism.ext (k' i)
  have : lift (b 0) (lift (b 1) (b 2)) = q := by
    refine CartesianMonoidalCategory.hom_ext _ _ ((lift_fst _ _).trans (hq 0).symm) ?_
    rw [lift_snd]
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [lift_fst, Category.assoc]; exact (hq 1).symm
    · rw [lift_snd, Category.assoc]; exact (hq 2).symm
  rw [this]
  rfl

theorem rearrange {U : Type} [CommGroup U] (a b c u p q r : U) :
    a * (b⁻¹ * c⁻¹) * (u * (p * (q⁻¹ * r⁻¹))) = u * (a * p * ((b * q)⁻¹ * (c * r)⁻¹)) := by
  simp only [mul_inv]
  ac_rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem val_scaleG {X0 : Scheme.{0}} (t : SAB H X0) {Y Z : Scheme.{0}} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ}
    {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J) (c : Γ(Y, ⊤)ˣ)
    (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) :
    val (scaleGenG t φ ε c g) r z J = gm r z ⊤ c * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) c) rfl)


open GlobalTheory.SecondPartialLaw in
theorem formal_sum {X0 : Scheme.{0}} {t : SAB H X0} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ}
    {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S}
    {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S} {κ : Type} [Fintype κ]
    {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uv : κ → Fin d → S} (hch : IsChartG t x0 d F act tg uv x) (m : ℕ)
    {U : Type} [CommGroup U] (h : ((jOG x0 d m 3).left ⟶ t.G.left) → U)
    (P : (Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) → U)
    (hP : ∀ φ, P φ = ∏ k, h ((Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left ≫
      cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] k) ^ cε 2 k) :
    ∏ k : thK.{0}, h ((lift (jptG t x0 d x m (0 : Fin 3)) (lift (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)))).left ≫
        thφ t.G (x3 t.G) k) ^ thε k =
      P ![fun j => psIn d m ![0, 1] (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] *
        ((P ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])⁻¹ *
          (P ![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)])⁻¹) := by
  have hP' : ∀ (φ : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) (a b : jOG x0 d m 3 ⟶ t.G),
      Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => φ 0 p.2)) ≫ x m = a →
      Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => φ 1 p.2)) ≫ x m = b →
      P φ = h (1 : jOG x0 d m 3 ⟶ t.G).left * (h a.left)⁻¹ * (h b.left)⁻¹ * h (b * a).left := by
    rintro φ _ _ rfl rfl
    rw [← pt_sub m φ 0, ← pt_sub m φ 1]
    have e1 := Finset.prod_congr (s₁ := Finset.univ) rfl fun (k : ULift.{0} (Finset (Fin 2))) _ =>
      congrArg (fun q => h q ^ cε 2 k) (pe_pt (t := t) (x := x) m (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2) k)
    have e2 := prod_cube2_swap (fun p : jOG x0 d m 3 ⟶ t.G => h p.left)
      ![Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2) ≫ jptG t x0 d x m (0 : Fin 2),
        Formalism.L2.Pj.homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2) ≫ jptG t x0 d x m (1 : Fin 2)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, _root_.mul_one] at e2
    exact (hP φ).trans (e1.trans e2)
  rw [hP' ![fun j => psIn d m ![0, 1] (F j), fun j => MvPolynomial.X ((2 : Fin 3), j)] _ _
      (pt_law hch m ![0, 1]) (pt_X m 2),
    hP' ![fun j => MvPolynomial.X ((0 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] _ _ (pt_X m 0) (pt_X m 2),
    hP' ![fun j => MvPolynomial.X ((1 : Fin 3), j), fun j => MvPolynomial.X ((2 : Fin 3), j)] _ _ (pt_X m 1) (pt_X m 2)]
  refine (Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ thε k) (th_pt _ _ _ k)).trans
    ((prod_cube3 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left) _).trans ?_)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, _root_.mul_one]
  generalize jptG t x0 d x m (0 : Fin 3) = a
  generalize jptG t x0 d x m (1 : Fin 3) = b
  generalize jptG t x0 d x m (2 : Fin 3) = c
  rw [_root_.mul_comm c (a * b), _root_.mul_comm c a, _root_.mul_comm c b, _root_.mul_assoc a b c]
  apply ofMul_eq
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.PushFirstLaw

namespace GlobalTheory

open PushFirstLaw

theorem famPh1_push : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), CubIso n w → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → PushFr n w x x' e e' → ∀ (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (ph : PS V 3 d), IsChartG t (𝟙 (Sp V)) d F act tg uv x → FamPh1 t (𝟙 (Sp V)) d x F ph e → FamPh1 t' (𝟙 (Sp V)) d x' F ph e' := by
  intro E _ _ _ H V _ t t' n w d x x' e e' hw hx _ hp F act κ _ tg uv ph hch h m
  obtain ⟨u, hu, hcor⟩ := h m
  obtain ⟨-, c, -, hc, hcar⟩ := hp m
  refine ⟨u, hu, corr_of_val t'.PP.isLB fun y J hJ => ?_⟩
  obtain ⟨J', hJ', -⟩ := exists_good t.PP.L t.PP.isLB y (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim)
    (fun a => a.elim)
  have k := val_corr hJ' hcor (𝟙 _)
  have hpe : ∀ φ : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) V,
      val (peG t' (𝟙 (Sp V)) d x' e' m φ) (𝟙 _) y J =
        (∏ k, isoVal w y J J' ((Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left ≫
          cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] k) ^ cε 2 k) *
          val (peG t (𝟙 (Sp V)) d x e m φ) (𝟙 _) y J' := fun φ => by
    refine (val_pull hJ _ _ _).trans ((val_corr hJ hc _).symm.trans ((val_carries hJ hJ' hcar _).trans
      (congrArg₂ (· * ·) ?_ (val_pull hJ' _ _ _).symm)))
    rw [Category.id_comp]
  have hl := lift_cubeMap n.cm (fun i => jptG t (𝟙 (Sp V)) d x m i) (fun i => jptG t' (𝟙 (Sp V)) d x' m i) (fun i => by
    simp only [jptG, Over.comp_left, hx m, Category.assoc])
  have hs := formal_sum hch m (isoVal w y J J') _ (fun _ => rfl)
  have k2 := (val_pull hJ' _ _ _).symm.trans (k.trans ((val_scaleG t hJ' _ _ _).trans (congrArg (_ * ·)
    ((val_mul hJ' _ _ _).trans (congrArg (_ * ·) ((val_mul hJ' _ _ _).trans
      (congrArg₂ (· * ·) (val_inv _ _) (val_inv _ _))))))))
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ ((val_scaleG t' hJ _ _ _).trans (congrArg (_ * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hpe _) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((val_inv _ _).trans (congrArg (·⁻¹) (hpe _)))
        ((val_inv _ _).trans (congrArg (·⁻¹) (hpe _))))))))).symm)
  refine (congrArg (fun r => val (φ := thφ t'.G (x3 t'.G)) (ε := thε) t'.cub.t r y J)
    ((Category.id_comp _).trans hl)).trans ((val_theta n.cm hw.2 hJ hJ' _).trans ((congrArg₂ (· * ·) hs
      ((congrArg (fun r => val (φ := thφ t.G (x3 t.G)) (ε := thε) t.cub.t r y J') (Category.id_comp _)).symm.trans k2)).trans
        (rearrange _ _ _ _ _ _ _)))

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FirstPartialLawPushAlongTripleMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstPartialLaw_push_along_tripleMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), CubIso n w → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → PushFr n w x x' e e' → ∀ (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (ph : PS V 3 d), IsChartG t (𝟙 (Sp V)) d F act tg uv x → FamPh1 t (𝟙 (Sp V)) d x F ph e → FamPh1 t' (𝟙 (Sp V)) d x' F ph e' := by
  first | exact @GlobalTheory.famPh1_push | exact GlobalTheory.famPh1_push | (intros; apply GlobalTheory.famPh1_push <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.SecondPartialLawPushAlongTripleMap
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.SecondPartialLawPushAlongTripleMap
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.PushSecondLaw

open MvPolynomial (X)
open GlobalTheory.SecondPartialLaw

section Values

variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
  {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X')} {ε : K → ℤ} {z : Z} {J : (Z ⟶ X) → L.ι} {J' : (Z ⟶ X') → L'.ι}

theorem val_pmaps {φ : K → (Y ⟶ X)} {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (H : PMaps w φ' φ ε a t h) (hc : ∀ k, φ' k ≫ F = h ≫ φ k) (hJ : Good L z J) (hJ' : Good L' z J') (r : Z ⟶ Y') :
    val t (r ≫ h) z J = (∏ k, (fun q => gw w q z (J (q ≫ F)) (J' q)) (r ≫ φ' k) ^ ε k) * val a r z J' := by
  have e := H _ r z (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => J' (r ≫ φ' k)) (fun k => hJ _) (fun k => hJ' _)
  refine Eq.trans ?_ e
  refine val_of _ _ _ _ _ fun k => congrArg J ?_
  rw [Category.assoc, Category.assoc, hc]

theorem val_carries {g : LB.Gen (LB.LinComb L' φ' ε)} {c : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)}
    (H : Carries L F w φ' ε g c) (hJ : Good L z J) (hJ' : Good L' z J') (r : Z ⟶ Y') :
    val c r z J = (∏ k, (fun q => gw w q z (J (q ≫ F)) (J' q)) (r ≫ φ' k) ^ ε k) * val g r z J' := by
  have P : PMaps w φ' (fun k => φ' k ≫ F) ε g c (𝟙 Y') :=
    (maps_iff w φ' _ ε g c (𝟙 Y') (flatGen L F φ' ε c) (fun j => wchart_pull_le L F φ' j) (fun j => rfl)).1 H
  have e := val_pmaps P (fun k => (Category.id_comp _).symm) hJ hJ' r
  rwa [Category.comp_id] at e

end Values

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem val_scaleGenG {X0 : Scheme.{0}} (t : SAB H X0) {Y Z : Scheme.{0}} {K : Type} [Fintype K]
    {φ : K → (Y ⟶ t.G.left)} {ε : K → ℤ} {z : Z} {J : (Z ⟶ t.G.left) → t.PP.L.ι} (hJ : Good t.PP.L z J)
    (c : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) (r : Z ⟶ Y) :
    val (scaleGenG t φ ε c g) r z J = gm r z ⊤ c * val g r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) c) rfl)


set_option maxHeartbeats 4000000 in
theorem prod_second_law {X0 : Scheme.{0}} {t : SAB H X0} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {d : ℕ}
    {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {F : Fin d → MvPowerSeries (Fin 2 × Fin d) S}
    {act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S} {κ : Type} [Fintype κ]
    {tg : κ → (Sp (DualNumber S) ⟶ t.G.left)} {uvec : κ → Fin d → S} (hch : IsChartG t x0 d F act tg uvec x) (m : ℕ)
    {U : Type} [CommGroup U] (h : ((jOG x0 d m 3).left ⟶ t.G.left) → U)
    (P : (Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) S) → U)
    (hP : ∀ φ, P φ = ∏ I : ULift.{0} (Finset (Fin 2)), h ((homAt x0 (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left ≫
      cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] I) ^ cε 2 I) :
    ∏ I, h ((lift (jptG t x0 d x m (1 : Fin 3)) (lift (jptG t x0 d x m (2 : Fin 3))
        (jptG t x0 d x m (0 : Fin 3)))).left ≫ thφ t.G (x3 t.G) I) ^ thε I =
      P ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)] *
        ((P ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)])⁻¹ *
          (P ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])⁻¹) := by
  have hQ : ∀ φ, P φ = ∏ I : ULift.{0} (Finset (Fin 2)), h (psum t.G
      ![Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => φ 0 p.2)) ≫ x m,
        Formalism.L2.Pj.homAt x0 (jetSubstP m (fun p : Fin 1 × Fin d => φ 1 p.2)) ≫ x m] I.down).left ^ cε 2 I := fun φ => by
    rw [← pt_sub m φ 0, ← pt_sub m φ 1]
    exact (hP φ).trans (Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ cε 2 I) (pe_pt m _ I))
  simp only [hQ, th_pt, Matrix.cons_val_zero, Matrix.cons_val_one, pt_X, pt_law hch]
  erw [prod_cube3 t.G (fun p : jOG x0 d m 3 ⟶ t.G => h p.left)]
  rw [prod_cube2_swap (fun p : jOG x0 d m 3 ⟶ t.G => h p.left),
    prod_cube2_swap (fun p : jOG x0 d m 3 ⟶ t.G => h p.left), prod_cube2_swap (fun p : jOG x0 d m 3 ⟶ t.G => h p.left)]
  have ha2 : jptG t x0 d x m (1 : Fin 3) * jptG t x0 d x m (2 : Fin 3) * jptG t x0 d x m (0 : Fin 3) =
      jptG t x0 d x m (1 : Fin 3) * (jptG t x0 d x m (2 : Fin 3) * jptG t x0 d x m (0 : Fin 3)) := _root_.mul_assoc _ _ _
  apply ofMul_eq
  simp only [ofMul_mul, ofMul_inv, _root_.mul_one]
  erw [ha2]
  abel!

theorem lift_comp_cube {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    (n : CubeMap G G') {T : Over S} {a b c : T ⟶ G} {a' b' c' : T ⟶ G'} (ha : a'.left = a.left ≫ n.F)
    (hb : b'.left = b.left ≫ n.F) (hc : c'.left = c.left ≫ n.F) :
    (lift a' (lift b' c')).left = (lift a (lift b c)).left ≫ n.F3 := hom_ext_triple _ fun i => by
  rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
  fin_cases i
  · simpa [x3] using ha
  · simpa [x3] using hb
  · simpa [x3] using hc

theorem alg_step {U : Type} [CommGroup U] {θ θ' u A B C A' B' C' p a b c : U} (k : θ = u * (A * (B⁻¹ * C⁻¹)))
    (hθ : θ' = p * θ) (hA : A' = a * A) (hB : B' = b * B) (hC : C' = c * C) (hp : p = a * (b⁻¹ * c⁻¹)) :
    θ' = u * (A' * (B'⁻¹ * C'⁻¹)) := by
  subst k hθ hA hB hC hp
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem famPh2_push : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), CubIso n w → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → PushFr n w x x' e e' → ∀ (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (ph : PS V 3 d), IsChartG t (𝟙 (Sp V)) d F act tg uv x → FamPh2 t (𝟙 (Sp V)) d x F ph e → FamPh2 t' (𝟙 (Sp V)) d x' F ph e' := by
  intro E _ _ _ H V _ t t' n w d x x' e e' hcub hx _ hfr F act κ _ tg uv ph hch h m
  obtain ⟨u, hu, hcor⟩ := h m
  refine ⟨u, hu, corr_of_val t'.PP.isLB fun y J' hJ' => ?_⟩
  choose J hJ using fun χ : (jOG (𝟙 (Sp V)) d m 3).left ⟶ t.G.left => exists_chart t.PP.isLB (χ y)
  replace hJ : Good t.PP.L y J := hJ
  obtain ⟨W, hW⟩ : ∃ W : ((jOG (𝟙 (Sp V)) d m 3).left ⟶ t.G.left) → ((jOG (𝟙 (Sp V)) d m 3).left.presheaf.stalk y)ˣ,
    W = fun q => gw w q y (J' (q ≫ n.φ)) (J q) := ⟨_, rfl⟩
  obtain ⟨-, c, -, hc, hcar⟩ := hfr m
  have hpt : ∀ i : Fin 3, (jptG t' (𝟙 (Sp V)) d x' m i).left = (jptG t (𝟙 (Sp V)) d x m i).left ≫ n.φ := fun i => by
    rw [jptG, jptG, Over.comp_left, Over.comp_left, hx m, Category.assoc]
  have hpe : ∀ φ : Fin 2 → Fin d → MvPolynomial (Fin 3 × Fin d) V,
      val (peG t' (𝟙 (Sp V)) d x' e' m φ) (𝟙 _) y J' =
        (∏ I : ULift.{0} (Finset (Fin 2)), W ((homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left ≫
          cφG t ![jptG t (𝟙 (Sp V)) d x m (0 : Fin 2), jptG t (𝟙 (Sp V)) d x m (1 : Fin 2)] I) ^ cε 2 I) *
          val (peG t (𝟙 (Sp V)) d x e m φ) (𝟙 _) y J := fun φ => by
    refine (val_pull hJ' _ _ _).trans ((val_corr hJ' hc _).symm.trans ((val_carries hcar hJ' hJ _).trans ?_))
    refine congrArg₂ (· * ·) ?_ (val_pull hJ _ _ _).symm
    rw [hW, Category.id_comp]
  have P : PMaps w (thφ t.G (x3 t.G)) (thφ t'.G (x3 t'.G)) thε t.cub.t t'.cub.t n.cm.F3 :=
    (maps_iff w _ _ thε t.cub.t t'.cub.t n.cm.F3 _ (fun j => n.cm.theta_le t'.PP.L j) (fun j => rfl)).1 hcub.2
  have hθ := val_pmaps P (fun I => n.cm.psum_comm I.down) hJ' hJ
    (lift (jptG t (𝟙 (Sp V)) d x m (1 : Fin 3)) (lift (jptG t (𝟙 (Sp V)) d x m (2 : Fin 3))
      (jptG t (𝟙 (Sp V)) d x m (0 : Fin 3)))).left
  rw [← hW, ← lift_comp_cube n.cm (hpt 1) (hpt 2) (hpt 0)] at hθ
  have k := (val_pull hJ _ _ _).symm.trans ((val_corr hJ hcor (𝟙 _)).trans ((val_scaleGenG t hJ _ _ _).trans
    (congrArg _ ((val_mul hJ _ _ _).trans (congrArg _ ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) (val_inv _ _) (val_inv _ _))))))))
  rw [Category.id_comp] at k
  refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ ((val_scaleGenG t' hJ' _ _ _).trans
    (congrArg _ ((val_mul hJ' _ _ _).trans (congrArg _ ((val_mul hJ' _ _ _).trans
      (congrArg₂ (· * ·) (val_inv _ _) (val_inv _ _))))))).symm)
  rw [Category.id_comp]
  exact alg_step k hθ (hpe _) (hpe _) (hpe _) (prod_second_law hch m W _ (fun _ => rfl))

end GlobalTheory.PushSecondLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.SecondPartialLawPushAlongTripleMapStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.secondPartialLaw_push_along_tripleMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))) (w : LB.Iso t.PP.L (t'.PP.L.pull n.φ)) (d : ℕ) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), CubIso n w → (∀ m, (x' m).left = (x m).left ≫ n.φ) → (∀ m, (e m).IsGen) → PushFr n w x x' e e' → ∀ (F : Fin d → PS V 2 d) (act : 𝓞 E → Fin d → PS V 1 d) (κ : Type) [Fintype κ] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (uv : κ → Fin d → V) (ph : PS V 3 d), IsChartG t (𝟙 (Sp V)) d F act tg uv x → FamPh2 t (𝟙 (Sp V)) d x F ph e → FamPh2 t' (𝟙 (Sp V)) d x' F ph e' := by
  first | exact @GlobalTheory.PushSecondLaw.famPh2_push | exact GlobalTheory.PushSecondLaw.famPh2_push | (intros; apply GlobalTheory.PushSecondLaw.famPh2_push <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalBiextensionsRelatedOfTripleMapOverId
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp

namespace GlobalTheory.ChartCmp

theorem jrel_of_sabMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (V : Type) [CommRing V] [IsLocalRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))), Function.Surjective (t'.G ⊗ t'.G).hom.appTop.hom → ∀ (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t'.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t' (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ t'.G (Fin 1 × Fin d) x' → IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e → IsFrameG t' (𝟙 (Sp V)) d x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e' → ∃ φ φi : Pt V 1 d, (∀ m, ∃ ε : PS V 2 d, JRel m B B' φ φi ε) ∧ ∀ (u u' : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t' (𝟙 (Sp V)) (dirs x') u' (v ≫ n.φ) → u = (dLin φ).mulVec u' := by
  intro E _ _ _ H _ hstar V _ _ t t' n hs d B B' κ κ' _ _ tg tg' uv uv' x x' e e' hc hc' hu hu' hf hf'
  obtain ⟨y, hy, hyu, hyc, hycomb⟩ := GlobalTheory.T.pushChartAlt E H V t t' n d x
  obtain ⟨_, _, _, _, _, w, hw⟩ := GlobalTheory.T.exists_groupIso_cubicalIso_of_tripleMap_id E H V t t' n
  obtain ⟨hg, h1, h2, h3, h4⟩ := (isFrameG_iff t _ d x _ _ _ _ _ _ e).1 hf
  obtain ⟨f, hp⟩ := GlobalTheory.T.exists_pushFr_of_isGen E H V t t' n w d x y e hw.1 hy hg
  have hfy : IsFrameG t' (𝟙 (Sp V)) d y B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad f :=
    (isFrameG_iff t' _ d y _ _ _ _ _ _ f).2
      ⟨fun m => (hp m).1,
        GlobalTheory.T.firstPartialLaw_push_along_tripleMap E H V t t' n w d x y e f hw hy hg hp _ _ κ tg uv _ hc h1,
        GlobalTheory.T.secondPartialLaw_push_along_tripleMap E H V t t' n w d x y e f hw hy hg hp _ _ κ tg uv _ hc h2,
        GlobalTheory.T.famSy_of_pushFr_cubIso E H V t t' n w d x y e f hw hy hg hp _ h3,
        GlobalTheory.T.adjointness_series_transport_frames E H V t t' n w d x y e f hw hy hg hp _ _ κ tg uv _ hc h4⟩
  obtain ⟨φ, φi, hj, hd⟩ := GlobalTheory.T.chartsWithFrames_related_allOrders E H hstar V t' hs d B B' κ κ' (fun l => tg l ≫ n.φ) tg' uv uv' y x' f e'
    (hyc _ _ κ tg uv hc) hc' (hyu hu) hu' hfy hf'
  exact ⟨φ, φi, hj, fun u u' v h h' => hd u u' _ (hycomb u v h) h'⟩

end GlobalTheory.ChartCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FormalBiextensionsRelatedOfTripleMapOverIdStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_biextensions_related_of_triple_map_over_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (V : Type) [CommRing V] [IsLocalRing V] (t t' : SAB H (Sp V)) (n : SABMap t t' (𝟙 (Sp V))), Function.Surjective (t'.G ⊗ t'.G).hom.appTop.hom → ∀ (d : ℕ) (B B' : FB V d (𝓞 E)) (κ κ' : Type) [Fintype κ] [Fintype κ'] (tg : κ → (Sp (DualNumber V) ⟶ t.G.left)) (tg' : κ' → (Sp (DualNumber V) ⟶ t'.G.left)) (uv : κ → Fin d → V) (uv' : κ' → Fin d → V) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t'.G) (e : ∀ m, FrTyG t (𝟙 (Sp V)) d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp V)) d x' m), IsChartG t (𝟙 (Sp V)) d B.G.F B.A.act tg uv x → IsChartG t' (𝟙 (Sp V)) d B'.G.F B'.A.act tg' uv' x' → GlobalTheory.PowGerm.IsUnivJ t.G (Fin 1 × Fin d) x → GlobalTheory.PowGerm.IsUnivJ t'.G (Fin 1 × Fin d) x' → IsFrameG t (𝟙 (Sp V)) d x B.G.F B.A.act B.ph1 B.ph2 B.sy B.ad e → IsFrameG t' (𝟙 (Sp V)) d x' B'.G.F B'.A.act B'.ph1 B'.ph2 B'.sy B'.ad e' → ∃ φ φi : Pt V 1 d, (∀ m, ∃ ε : PS V 2 d, JRel m B B' φ φi ε) ∧ ∀ (u u' : Fin d → V) (v : Sp (DualNumber V) ⟶ t.G.left), IsCombAtG t (𝟙 (Sp V)) (dirs x) u v → IsCombAtG t' (𝟙 (Sp V)) (dirs x') u' (v ≫ n.φ) → u = (dLin φ).mulVec u' := by
  first | exact @GlobalTheory.ChartCmp.jrel_of_sabMap | exact GlobalTheory.ChartCmp.jrel_of_sabMap | (intros; apply GlobalTheory.ChartCmp.jrel_of_sabMap <;> assumption)
end
