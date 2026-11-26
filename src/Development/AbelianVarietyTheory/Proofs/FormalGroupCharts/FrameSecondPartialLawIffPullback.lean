module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartPrimTrPfA
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ContinuousRmulPair
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.TripleProductTorusPeriodicBounded

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameSecondPartialLawIffPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameSecondPartialLawIffPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FramePartialLawTwo

section Val

variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

def om (w : LB.Iso L' (L.pull F)) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) (ψ : Z ⟶ X') :
    (Z.presheaf.stalk z)ˣ := gw w ψ z (J (ψ ≫ F)) (J' ψ)

theorem val_of_pmaps {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (H : PMaps w φ' φ ε a t h) (hφ : ∀ k, φ' k ≫ F = h ≫ φ k) (r : Z ⟶ Y') {z : Z} {J J'}
    (hJ : Good L z J) (hJ' : Good L' z J') :
    val t (r ≫ h) z J = (∏ k, om w z J J' (r ≫ φ' k) ^ ε k) * val a r z J' := by
  rw [val_of t (r ≫ h) z J (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc, Category.assoc, hφ])]
  exact H Z r z _ _ (fun k => hJ ((r ≫ φ' k) ≫ F)) (fun k => hJ' (r ≫ φ' k))

theorem pmaps_flat (w : LB.Iso L' (L.pull F)) (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (a : LB.Gen (LB.LinComb L' φ' ε))
    (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε))
    (H : LB.Gen.Maps (LB.linCombIso w φ' ε) a (flatGen L F φ' ε t)) :
    PMaps w φ' (fun k => φ' k ≫ F) ε a t (𝟙 Y) := by
  refine (maps_iff w φ' (fun k => φ' k ≫ F) ε a t (𝟙 Y) (flatGen L F φ' ε t)
    (fun j x hx => wchart_pull_le L F φ' j hx) (fun j => ?_)).1 H
  refine unit_ext fun y hy => ?_
  have hyV : (𝟙 Y : Y ⟶ Y) y ∈ ((L.pull F).LinComb φ' ε).U j := hy
  have hyU : (𝟙 Y : Y ⟶ Y) ((𝟙 Y : Y ⟶ Y) y) ∈ LB.wchart L (fun k => φ' k ≫ F) (fun k => j k ⟨⟩) :=
    wchart_pull_le L F φ' j hy
  refine (gm_res (𝟙 Y) y _ hyV _).trans ?_
  refine Eq.trans ?_ (gm_res (𝟙 Y) y _ hyV _).symm
  have e := gm_pull (𝟙 Y) (𝟙 Y) y _ hyU (t.s fun k => j k ⟨⟩)
  rw [Category.comp_id] at e
  exact e.symm

end Val

section Pts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)

theorem prod_sq {T T' : Over X0} (ρ : T' ⟶ T) (a b : T ⟶ t.G) {U : Type} [CommGroup U]
    (h : (T'.left ⟶ t.G.left) → U) :
    ∏ I, h (ρ.left ≫ cφG t ![a, b] I) ^ cε 2 I =
      h ((ρ ≫ a) * (ρ ≫ b)).left * (h (ρ ≫ a).left)⁻¹ * (h (ρ ≫ b).left)⁻¹ * h (1 : T' ⟶ t.G).left := by
  have e : ∀ I : ULift.{0} (Finset (Fin 2)), ρ.left ≫ cφG t ![a, b] I = (psum t.G ![ρ ≫ a, ρ ≫ b] I.down).left :=
    fun I => congrArg (fun q => q.left) ((psum_hom (preHom ρ) ![a, b] I.down).trans
      (congrArg (fun q => psum t.G q I.down) (funext fun i => by fin_cases i <;> rfl)))
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => h (psum t.G ![ρ ≫ a, ρ ≫ b] I).left ^ ((-1 : ℤ) ^ (2 - I.card)))
    (fun I => congrArg (fun q => h q ^ cε 2 I) (e I))).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have p₀ : psum t.G ![ρ ≫ a, ρ ≫ b] ∅ = 1 := rfl
  have p₁ : psum t.G ![ρ ≫ a, ρ ≫ b] {0} = ρ ≫ a := _root_.mul_one _
  have p₂ : psum t.G ![ρ ≫ a, ρ ≫ b] {1} = ρ ≫ b := _root_.mul_one _
  have p₄ : psum t.G ![ρ ≫ a, ρ ≫ b] {0, 1} = (ρ ≫ a) * (ρ ≫ b) := congrArg ((ρ ≫ a) * ·) (_root_.mul_one _)
  rw [p₀, p₁, p₂, p₄]
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₄ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [q₀, q₁, q₁, q₄]
  simp only [zpow_one, zpow_neg_one]
  ac_rfl

variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

theorem subst_jpt (m : ℕ) {n n' : ℕ} (φ : Fin n → Fin d → MvPolynomial (Fin n' × Fin d) S) (i : Fin n) :
    homAt x0 (jetSubstP m fun p : Fin n × Fin d => φ p.1 p.2) ≫ jptG t x0 d x m i =
      homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => φ i p.2) ≫ x m := by
  simp only [jptG, ← Category.assoc, GermD.homAt_comp]
  congr 2
  apply GermD.jet_hom_ext
  rintro ⟨i0, j⟩
  simp [jetCopy, jetSubstP, GermD.jetMap_mk]

theorem subst_X (m : ℕ) {n : ℕ} (i : Fin n) :
    homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => (MvPolynomial.X (i, p.2) : MvPolynomial (Fin n × Fin d) S)) ≫ x m =
      jptG t x0 d x m i := by
  simp only [jptG]
  congr 2
  apply GermD.jet_hom_ext
  rintro ⟨i0, j⟩
  simp [jetCopy, jetSubstP, GermD.jetMap_mk]

theorem subst_law (m : ℕ) (F : Fin d → PS S 2 d) (hF : ∀ j, MvPowerSeries.constantCoeff (F j) = 0)
    (law : homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x m =
      jptG t x0 d x m (0 : Fin 2) * jptG t x0 d x m (1 : Fin 2)) {n : ℕ} (σ : Fin 2 → Fin n) :
    homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psIn d m σ (F p.2)) ≫ x m =
      jptG t x0 d x m (σ 0) * jptG t x0 d x m (σ 1) := by
  rw [← FBIdPh.relabel_jpt t x0 d x m σ 0, ← FBIdPh.relabel_jpt t x0 d x m σ 1, ← MonObj.comp_mul, ← law,
    ← Category.assoc, GermD.homAt_comp, FBIdPh.jetSubstP_comp m _ _
      (fun p => (FBIdPh.cc_psTrunc m _).trans (hF _)) (fun p => by simp [FBIdPh.rel])]
  congr 3
  funext p
  rw [psIn, MvPolynomial.rename_eq_aeval]
  rfl

end Pts

section Comparison₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} {t : SAB H X0}
  {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {t' : SAB H (Sp S)} {mp : SABMap t' t x0}
  {w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)}

theorem val_cubic (hθ : LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t
      (mp.cm.thetaPull t.PP.L t.cub.t)) {Y : Scheme.{0}} {s : Y ⟶ X0} {s' : Y ⟶ Sp S}
    (a b c : Over.mk s ⟶ t.G) (a' b' c' : Over.mk s' ⟶ t'.G) (ha : a'.left ≫ mp.φ = a.left)
    (hb : b'.left ≫ mp.φ = b.left) (hc : c'.left ≫ mp.φ = c.left) {y : Y} {J J'}
    (hJ : Good t.PP.L y J) (hJ' : Good t'.PP.L y J') :
    val (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift a (lift b c)).left) (𝟙 Y) y J =
      (om w y J J' (a' * b' * c').left * (om w y J J' (a' * b').left)⁻¹ * (om w y J J' (a' * c').left)⁻¹ *
        (om w y J J' (b' * c').left)⁻¹ * om w y J J' a'.left * om w y J J' b'.left * om w y J J' c'.left *
        (om w y J J' (1 : Over.mk s' ⟶ t'.G).left)⁻¹) *
      val (LB.pullGen t'.PP.L (thφ t'.G (x3 t'.G)) thε t'.cub.t (lift a' (lift b' c')).left) (𝟙 Y) y J' := by
  have pm := (maps_iff w (thφ t'.G (x3 t'.G)) (thφ t.G (x3 t.G)) thε t'.cub.t t.cub.t mp.cm.F3 _
    (mp.cm.theta_le t.PP.L) (fun _ => rfl)).1 hθ
  have q : (lift a' (lift b' c')).left ≫ mp.cm.F3 = (lift a (lift b c)).left := hom_ext_triple _ fun i => by
    rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
    fin_cases i
    · simpa [x3] using ha
    · simpa [x3] using hb
    · simpa [x3] using hc
  have e := val_of_pmaps pm (fun I => mp.cm.psum_comm I.down) (lift a' (lift b' c')).left hJ hJ'
  rw [q] at e
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))
  refine Eq.trans (congrArg (fun r => val (L := t.PP.L) (φ := thφ t.G (x3 t.G)) (ε := thε) t.cub.t r y J)
    (Category.id_comp _)) (e.trans (congrArg₂ (· * ·) (prod_cub a' b' c' (om w y J J')) ?_))
  exact congrArg (fun r => val (L := t'.PP.L) (φ := thφ t'.G (x3 t'.G)) (ε := thε) t'.cub.t r y J')
    (Category.id_comp _).symm

variable {d : ℕ} {x : ∀ m, jOG x0 d m 1 ⟶ t.G} {x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G}

theorem val_frame {e : ∀ m, FrTyG t x0 d x m} {e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m} {m : ℕ}
    {c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2),
      jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2))}
    (h₁ : LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m))
    (h₂ : LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2),
      jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁))
    {n : ℕ} (φ : Fin 2 → Fin d → MvPolynomial (Fin n × Fin d) S) (a b : jOG (𝟙 (Sp S)) d m n ⟶ t'.G)
    (ha : homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => φ 0 p.2) ≫ x' m = a)
    (hb : homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => φ 1 p.2) ≫ x' m = b)
    {y : Sp (Jet S (Fin n × Fin d) m)} {J J'} (hJ : Good t.PP.L y J) (hJ' : Good t'.PP.L y J') :
    val (peG t x0 d x e m φ) (𝟙 (Sp (Jet S (Fin n × Fin d) m))) y J =
      (om w y J J' (a * b).left * (om w y J J' a.left)⁻¹ * (om w y J J' b.left)⁻¹ *
        om w y J J' (1 : jOG (𝟙 (Sp S)) d m n ⟶ t'.G).left) *
      val (peG t' (𝟙 (Sp S)) d x' e' m φ) (𝟙 (Sp (Jet S (Fin n × Fin d) m))) y J' := by
  have pm := pmaps_flat w _ _ _ _ h₂
  have e₀ := val_of_pmaps pm (fun _ => (Category.id_comp _).symm)
    (homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2)).left hJ hJ'
  have p := prod_sq t' (homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 2 × Fin d => φ p.1 p.2))
    (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2)) (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)) (om w y J J')
  rw [subst_jpt, subst_jpt, ha, hb] at p
  refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_pull hJ' _ _ _).symm))
  refine (val_corr hJ h₁ _).symm.trans (Eq.trans (congrArg (fun r => val c₁ r y J)
    ((Category.id_comp _).trans (Category.comp_id _).symm)) (e₀.trans (congrArg₂ (· * ·) p ?_)))
  exact congrArg (fun r => val (L := t'.PP.L) (φ := cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2),
      jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (ε := cε 2) (e' m) r y J') (Category.id_comp _).symm

theorem jpt_push (hx : ∀ m, (x' m).left ≫ mp.φ = (x m).left) (m : ℕ) {n : ℕ} (i : Fin n) :
    (jptG t' (𝟙 (Sp S)) d x' m i).left ≫ mp.φ = (jptG t x0 d x m i).left :=
  (Category.assoc _ _ _).trans (congrArg ((homAt x0 (jetCopy d m i)).left ≫ ·) (hx m))

end Comparison₂

theorem corr_iff_of_val {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB)
    {K₁ K₂ K₃ K₄ : Type} [Fintype K₁] [Fintype K₂] [Fintype K₃] [Fintype K₄]
    {φ₁ : K₁ → (Y ⟶ X)} {ε₁ : K₁ → ℤ} {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ}
    {φ₃ : K₃ → (Y ⟶ X')} {ε₃ : K₃ → ℤ} {φ₄ : K₄ → (Y ⟶ X')} {ε₄ : K₄ → ℤ}
    {a : LB.Gen (LB.LinComb L φ₁ ε₁)} {b : LB.Gen (LB.LinComb L φ₂ ε₂)}
    {a' : LB.Gen (LB.LinComb L' φ₃ ε₃)} {b' : LB.Gen (LB.LinComb L' φ₄ ε₄)}
    (h : ∀ (y : Y) J J', Good L y J → Good L' y J' →
      ∃ c, val a (𝟙 Y) y J = c * val a' (𝟙 Y) y J' ∧ val b (𝟙 Y) y J = c * val b' (𝟙 Y) y J') :
    LB.Gen.Corr L _ _ _ _ a b ↔ LB.Gen.Corr L' _ _ _ _ a' b' := by
  constructor
  · intro H
    refine corr_of_val hL' fun y J' hJ' => ?_
    choose J hJ using fun χ : Y ⟶ X => exists_chart hL (χ y)
    obtain ⟨c, e₁, e₂⟩ := h y J J' hJ hJ'
    exact mul_left_cancel (e₁.symm.trans ((val_corr hJ H _).trans e₂))
  · intro H
    refine corr_of_val hL fun y J hJ => ?_
    choose J' hJ' using fun χ : Y ⟶ X' => exists_chart hL' (χ y)
    obtain ⟨c, e₁, e₂⟩ := h y J J' hJ hJ'
    exact e₁.trans ((congrArg (c * ·) (val_corr hJ' H _)).trans e₂.symm)

theorem units_cancel {U : Type} [CommGroup U] (g p q r p₀₁₂ p₁₂ p₀₁ p₀₂ p₀ p₁ p₂ o : U) :
    g * ((p₀₁₂ * p₀⁻¹ * p₁₂⁻¹ * o * p) * ((p₀₁ * p₀⁻¹ * p₁⁻¹ * o * q)⁻¹ * (p₀₂ * p₀⁻¹ * p₂⁻¹ * o * r)⁻¹)) =
      (p₀₁₂ * p₁₂⁻¹ * p₀₁⁻¹ * p₀₂⁻¹ * p₁ * p₂ * p₀ * o⁻¹) * (g * (p * (q⁻¹ * r⁻¹))) := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.FramePartialLawTwo


open GlobalTheory.FramePartialLawTwo in
theorem GlobalTheory.frame_second_partial_law_iff_pullback :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t (mp.cm.thetaPull t.PP.L t.cub.t) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (F : Fin d → PS S 2 d) (ph2 : PS S 3 d), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ m, homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x' m = jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2) * jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)) → ((∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph2 ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift (jptG t x0 d x m (1 : Fin 3)) (lift (jptG t x0 d x m (2 : Fin 3)) (jptG t x0 d x m (0 : Fin 3)))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)]) (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)])) (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))) ↔ (∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph2 ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (LB.pullGen t'.PP.L (thφ t'.G (x3 t'.G)) thε t'.cub.t (lift (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 3)) (lift (jptG t' (𝟙 (Sp S)) d x' m (2 : Fin 3)) (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 3)))).left) (scaleGenG t' _ _ (unitΓ u) (LB.mulGen t'.PP.L _ _ _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)]) (LB.mulGen t'.PP.L _ _ _ _ (LB.invGen t'.PP.L _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)])) (LB.invGen t'.PP.L _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))))))) := by
  intro E _ _ _ H X0 t S _ x0 t' mp w _ d x x' hx hθ e e' _ _ he F ph2 hF law
  refine forall_congr' fun m => exists_congr fun u => and_congr_right fun _ => ?_
  obtain ⟨c₁, h₁, h₂⟩ := he m
  refine corr_iff_of_val t.PP.isLB t'.PP.isLB fun y J J' hJ hJ' => ?_
  have eθ := val_cubic hθ (jptG t x0 d x m (1 : Fin 3)) (jptG t x0 d x m (2 : Fin 3)) (jptG t x0 d x m (0 : Fin 3))
    (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 3)) (jptG t' (𝟙 (Sp S)) d x' m (2 : Fin 3))
    (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 3)) (jpt_push hx m 1) (jpt_push hx m 2) (jpt_push hx m 0) hJ hJ'
  have eA := val_frame h₁ h₂ ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)] _ _
    (subst_X t' _ d x' m 0) (subst_law t' _ d x' m F hF (law m) ![1, 2]) hJ hJ'
  have eB := val_frame h₁ h₂ ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)] _ _
    (subst_X t' _ d x' m 0) (subst_X t' _ d x' m 1) hJ hJ'
  have eC := val_frame h₁ h₂ ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)] _ _
    (subst_X t' _ d x' m 0) (subst_X t' _ d x' m 2) hJ hJ'
  rw [mul_comm (_ * _) (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 3)),
    mul_comm (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 3)) (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 3)),
    mul_comm (jptG t' (𝟙 (Sp S)) d x' m (2 : Fin 3)) (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 3))] at eθ
  refine ⟨_, eθ, ?_⟩
  refine ((GermB.val_scale t _ _ _ _ _ _ _ hJ).trans (congrArg₂ (· * ·) rfl ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) eA ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_inv _ _).trans (congrArg (·⁻¹) eB))
      ((val_inv _ _).trans (congrArg (·⁻¹) eC)))))))).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· * ·) rfl ((GermB.val_scale t' _ _ _ _ _ _ _ hJ').trans
    (congrArg₂ (· * ·) rfl ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) rfl ((val_mul hJ' _ _ _).trans
      (congrArg₂ (· * ·) (val_inv _ _) (val_inv _ _))))))).symm)
  exact units_cancel _ _ _ _ _ _ _ _ _ _ _ _
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.FrameSecondPartialLawIffPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_second_partial_law_iff_pullback_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → LB.Gen.Maps (LB.linCombIso w (thφ t'.G (x3 t'.G)) thε) t'.cub.t (mp.cm.thetaPull t.PP.L t.cub.t) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) → ∀ (F : Fin d → PS S 2 d) (ph2 : PS S 3 d), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ m, homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x' m = jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2) * jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)) → ((∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph2 ∧ LB.Gen.Corr t.PP.L _ _ _ _ (LB.pullGen t.PP.L (thφ t.G (x3 t.G)) thε t.cub.t (lift (jptG t x0 d x m (1 : Fin 3)) (lift (jptG t x0 d x m (2 : Fin 3)) (jptG t x0 d x m (0 : Fin 3)))).left) (scaleGenG t _ _ (unitΓ u) (LB.mulGen t.PP.L _ _ _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)]) (LB.mulGen t.PP.L _ _ _ _ (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)])) (LB.invGen t.PP.L _ _ (peG t x0 d x e m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)])))))) ↔ (∀ m, ∃ u : (Jet S (Fin 3 × Fin d) m)ˣ, (u : Jet S (Fin 3 × Fin d) m) = psJet m ph2 ∧ LB.Gen.Corr t'.PP.L _ _ _ _ (LB.pullGen t'.PP.L (thφ t'.G (x3 t'.G)) thε t'.cub.t (lift (jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 3)) (lift (jptG t' (𝟙 (Sp S)) d x' m (2 : Fin 3)) (jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 3)))).left) (scaleGenG t' _ _ (unitΓ u) (LB.mulGen t'.PP.L _ _ _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 3), j), fun j => psIn d m ![1, 2] (F j)]) (LB.mulGen t'.PP.L _ _ _ _ (LB.invGen t'.PP.L _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 3), j), fun j => X ((1 : Fin 3), j)])) (LB.invGen t'.PP.L _ _ (peG t' (𝟙 (Sp S)) d x' e' m ![fun j => X ((0 : Fin 3), j), fun j => X ((2 : Fin 3), j)]))))))) := by
  first | exact @GlobalTheory.frame_second_partial_law_iff_pullback | exact GlobalTheory.frame_second_partial_law_iff_pullback | (intros; apply GlobalTheory.frame_second_partial_law_iff_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsAbelianSchemePullbackUniversalTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsAbelianSchemePullbackUniversalTriple
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory

theorem isAbelianScheme_of_pullback_univ :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (X1 : Scheme.{0}) (t' : SAB H X1) (f : X1 ⟶ Xo.X) (mp : SABMap t' Xo.univ.t f), IsAbelianScheme t'.G := by
  intro E _ _ _ H Dw l Xo X1 t' f mp
  have hp : IsProper t'.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) mp.cart.1 Xo.univ.proper
  exact ⟨t'.semi.comm, t'.semi.smooth, hp, t'.semi.geomConnected⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsAbelianSchemePullbackUniversalTripleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianScheme_pullback_universalTriple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (X1 : Scheme.{0}) (t' : SAB H X1) (f : X1 ⟶ Xo.X) (mp : SABMap t' Xo.univ.t f), IsAbelianScheme t'.G := by
  first | exact @GlobalTheory.isAbelianScheme_of_pullback_univ | exact GlobalTheory.isAbelianScheme_of_pullback_univ | (intros; apply GlobalTheory.isAbelianScheme_of_pullback_univ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFramesCoefficientRingBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFramesCoefficientRingBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory.FrameBCGen

theorem cφG_comp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
    {T T' : Over X0} (ρ : T' ⟶ T) (a b : T ⟶ t.G) :
    cφG t ![ρ ≫ a, ρ ≫ b] = fun I => ρ.left ≫ cφG t ![a, b] I := by
  funext I
  refine Eq.symm (congrArg (fun q => q.left) ((psum_hom (preHom ρ) ![a, b] I.down).trans
      (congrArg (fun q => psum t.G q I.down) (funext fun i => ?_))))
  fin_cases i <;> rfl

theorem exists_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0), x1 = spMap ψ ≫ x0 → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G), (∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left) → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → ∃ e' : ∀ m, FrTyG t x1 d x' m, (∀ m, (e' m).IsGen) ∧ (∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L _ _ (e m) (spMap (jetCoef ψ (Fin 2 × Fin d) m)))) := by
  intro E _ _ _ H X0 t S S' _ _ ψ x0 x1 h01 d x x' hx e he
  subst h01
  let ρ : ∀ m, jOG (spMap ψ ≫ x0) d m 2 ⟶ jOG x0 d m 2 := fun m =>
    Over.homMk (spMap (jetCoef ψ (Fin 2 × Fin d) m)) (by
      show spMap (jetCoef ψ (Fin 2 × Fin d) m) ≫ spMap (algebraMap S (Jet S (Fin 2 × Fin d) m)) ≫ x0 =
        spMap (algebraMap S' (Jet S' (Fin 2 × Fin d) m)) ≫ spMap ψ ≫ x0
      rw [← Category.assoc, ← Category.assoc, RawFrameBC.spMap_comp_eq, RawFrameBC.spMap_comp_eq, JetTr.jetCoef_alg])
  have hp : ∀ m (i : Fin 2), jptG t (spMap ψ ≫ x0) d x' m i = ρ m ≫ jptG t x0 d x m i := by
    intro m i
    apply Over.OverMorphism.ext
    show spMap (jetCopy (S := S') d m i).toRingHom ≫ (x' m).left =
      spMap (jetCoef ψ (Fin 2 × Fin d) m) ≫ spMap (jetCopy (S := S) d m i).toRingHom ≫ (x m).left
    rw [hx, ← Category.assoc, ← Category.assoc, RawFrameBC.spMap_comp_eq, RawFrameBC.spMap_comp_eq]
    exact congrArg (fun f => spMap f ≫ (x m).left) (JetTr.jetCoef_copy ψ d m 2 i).symm
  have key := fun m => RawFrameBC.exists_reindexed_pull t.PP.isLB
    (cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)]) (cε 2) (e m) (he m) (ρ m).left
    (cφG t ![jptG t (spMap ψ ≫ x0) d x' m (0 : Fin 2), jptG t (spMap ψ ≫ x0) d x' m (1 : Fin 2)])
    (by rw [hp, hp, cφG_comp])
  choose e' h₁ h₂ _ using key
  exact ⟨e', h₁, h₂⟩

end GlobalTheory.FrameBCGen
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFramesCoefficientRingBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frames_coefficientRing_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0), x1 = spMap ψ ≫ x0 → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G), (∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left) → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → ∃ e' : ∀ m, FrTyG t x1 d x' m, (∀ m, (e' m).IsGen) ∧ (∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L _ _ (e m) (spMap (jetCoef ψ (Fin 2 × Fin d) m)))) := by
  first | exact @GlobalTheory.FrameBCGen.exists_frames | exact GlobalTheory.FrameBCGen.exists_frames | (intros; apply GlobalTheory.FrameBCGen.exists_frames <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointsUnitLawActionIffPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointsUnitLawActionIffPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory

section Push

variable {X0 : Scheme.{0}} {S : Type} [CommRing S] {x0 : Sp S ⟶ X0} {G : Over X0} {G' : Over (Sp S)}
  [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left}

def algPtPush (h : IsGrpPullback G' G x0 φ) (A : Type) [CommRing A] [Algebra S A] :
    (overAt (𝟙 (Sp S)) A ⟶ G') →* (overAt x0 A ⟶ G) :=
  (preHom (Over.homMk (𝟙 (Sp A)) (by simp) :
    overAt x0 A ⟶ Over.mk ((overAt (𝟙 (Sp S)) A).hom ≫ x0))).comp (pushHom h (overAt (𝟙 (Sp S)) A))

theorem algPtPush_left (h : IsGrpPullback G' G x0 φ) (A : Type) [CommRing A] [Algebra S A]
    (a : overAt (𝟙 (Sp S)) A ⟶ G') : (algPtPush h A a).left = a.left ≫ φ :=
  Category.id_comp (a.left ≫ φ)

theorem algPtPush_injective (h : IsGrpPullback G' G x0 φ) (A : Type) [CommRing A] [Algebra S A] :
    Function.Injective (algPtPush h A) := fun a b e => by
  refine Over.OverMorphism.ext (h.1.hom_ext ?_ ((Over.w a).trans (Over.w b).symm))
  exact (algPtPush_left h A a).symm.trans ((congrArg (fun q => q.left) e).trans (algPtPush_left h A b))

theorem algPtPush_homAt (h : IsGrpPullback G' G x0 φ) {A B : Type} [CommRing A] [Algebra S A] [CommRing B]
    [Algebra S B] (ψ : A →ₐ[S] B) (a : overAt (𝟙 (Sp S)) A ⟶ G') :
    algPtPush h B (Formalism.L2.Pj.homAt (𝟙 (Sp S)) ψ ≫ a) = Formalism.L2.Pj.homAt x0 ψ ≫ algPtPush h A a :=
  Over.OverMorphism.ext ((algPtPush_left h B _).trans ((Category.assoc (spMap (ψ : A →+* B)) a.left φ).trans
    (congrArg (fun q => spMap (ψ : A →+* B) ≫ q) (algPtPush_left h A a).symm)))

theorem algPtPush_comp (h : IsGrpPullback G' G x0 φ) {A : Type} [CommRing A] [Algebra S A]
    (u' : G' ⟶ G') (u : G ⟶ G) (e : u'.left ≫ φ = φ ≫ u.left) (a : overAt (𝟙 (Sp S)) A ⟶ G') :
    algPtPush h A (a ≫ u') = algPtPush h A a ≫ u :=
  Over.OverMorphism.ext ((algPtPush_left h A _).trans ((Category.assoc a.left u'.left φ).trans
    ((congrArg (fun q => a.left ≫ q) e).trans ((Category.assoc a.left φ u.left).symm.trans
      (congrArg (fun q => q ≫ u.left) (algPtPush_left h A a).symm)))))

end Push

theorem jetPoints_laws_iff_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ((∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1) ↔ (∀ m, homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x' m = 1)) ∧ (∀ F : Fin d → PS S 2 d, (∀ m, homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x m = jptG t x0 d x m (0 : Fin 2) * jptG t x0 d x m (1 : Fin 2)) ↔ (∀ m, homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x' m = jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2) * jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))) ∧ ∀ act : 𝓞 E → Fin d → PS S 1 d, (∀ m (b : 𝓞 E), x m ≫ t.act.act b = homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x m) ↔ (∀ m (b : 𝓞 E), x' m ≫ t'.act.act b = homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x' m) := by
  intro E _ _ _ H X0 t S _ x0 t' mp w _ d x x' hx
  obtain rfl : x = fun m => algPtPush mp.cart _ (x' m) :=
    funext fun m => Over.OverMorphism.ext ((hx m).symm.trans (algPtPush_left mp.cart _ (x' m)).symm)
  refine ⟨forall_congr' fun m => ?_, fun F => forall_congr' fun m => ?_,
    fun act => forall_congr' fun m => forall_congr' fun b => ?_⟩
  · rw [← (algPtPush_injective mp.cart _).eq_iff, map_one, algPtPush_homAt]
  · rw [← (algPtPush_injective mp.cart _).eq_iff, map_mul, algPtPush_homAt]
    simp only [jptG, algPtPush_homAt]
  · rw [← (algPtPush_injective mp.cart _).eq_iff, algPtPush_homAt,
      algPtPush_comp mp.cart _ _ (mp.act b)]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointsUnitLawActionIffPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetPoints_unit_law_action_iff_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ((∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1) ↔ (∀ m, homAt (𝟙 (Sp S)) (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x' m = 1)) ∧ (∀ F : Fin d → PS S 2 d, (∀ m, homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x m = jptG t x0 d x m (0 : Fin 2) * jptG t x0 d x m (1 : Fin 2)) ↔ (∀ m, homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x' m = jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2) * jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2))) ∧ ∀ act : 𝓞 E → Fin d → PS S 1 d, (∀ m (b : 𝓞 E), x m ≫ t.act.act b = homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x m) ↔ (∀ m (b : 𝓞 E), x' m ≫ t'.act.act b = homAt (𝟙 (Sp S)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x' m) := by
  first | exact @GlobalTheory.jetPoints_laws_iff_pullback | exact GlobalTheory.jetPoints_laws_iff_pullback | (intros; apply GlobalTheory.jetPoints_laws_iff_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointsUnitLawActionBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointsUnitLawActionBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

noncomputable section

namespace GlobalTheory.JetPointBC

theorem spMap_spMap {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'')
    (g : R →+* R') : spMap f ≫ spMap g = spMap (f.comp g) := by
  unfold spMap
  rw [← Spec.map_comp]
  rfl

section Maps

variable {X0 : Scheme.{0}} {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0)

def baseMap : overAt (spMap ψ ≫ x0) S' ⟶ overAt x0 S :=
  Over.homMk (spMap ψ) (by
    show spMap ψ ≫ spMap (algebraMap S S) ≫ x0 = spMap (algebraMap S' S') ≫ spMap ψ ≫ x0
    rw [← Category.assoc, ← Category.assoc, spMap_spMap, spMap_spMap]
    first | done | rfl)

def jetPtMap (d m n : ℕ) : jOG (spMap ψ ≫ x0) d m n ⟶ jOG x0 d m n :=
  Over.homMk (spMap (jetCoef ψ (Fin n × Fin d) m)) (by
    show spMap (jetCoef ψ (Fin n × Fin d) m) ≫ spMap (algebraMap S _) ≫ x0 =
      spMap (algebraMap S' _) ≫ spMap ψ ≫ x0
    rw [← Category.assoc, ← Category.assoc, spMap_spMap, spMap_spMap, JetTr.jetCoef_alg])

theorem sq_aug (d m : ℕ) :
    homAt (spMap ψ ≫ x0) (jetAug : Jet S' (Fin 1 × Fin d) m →ₐ[S'] S') ≫ jetPtMap ψ x0 d m 1 =
      baseMap ψ x0 ≫ homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetCoef ψ _ m) = spMap ψ ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  exact congrArg spMap (JetTr.jetCoef_aug ψ _ m)

theorem sq_subst {n n' d : ℕ} (m : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S) :
    homAt (spMap ψ ≫ x0) (jetSubstP m (fun i => MvPolynomial.map ψ (φ i)) :
        Jet S' (Fin n × Fin d) m →ₐ[S'] Jet S' (Fin n' × Fin d) m) ≫ jetPtMap ψ x0 d m n =
      jetPtMap ψ x0 d m n' ≫
        homAt x0 (jetSubstP m φ : Jet S (Fin n × Fin d) m →ₐ[S] Jet S (Fin n' × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetCoef ψ _ m) = spMap (jetCoef ψ _ m) ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  exact congrArg spMap (JetTr.jetCoef_substP ψ m φ).symm

theorem sq_copy (d m n : ℕ) (i : Fin n) :
    homAt (spMap ψ ≫ x0) (jetCopy d m i : Jet S' (Fin 1 × Fin d) m →ₐ[S'] Jet S' (Fin n × Fin d) m) ≫
        jetPtMap ψ x0 d m 1 =
      jetPtMap ψ x0 d m n ≫
        homAt x0 (jetCopy d m i : Jet S (Fin 1 × Fin d) m →ₐ[S] Jet S (Fin n × Fin d) m) := by
  apply Over.OverMorphism.ext
  show spMap _ ≫ spMap (jetCoef ψ _ m) = spMap (jetCoef ψ _ m) ≫ spMap _
  rw [spMap_spMap, spMap_spMap]
  exact congrArg spMap (JetTr.jetCoef_copy ψ d m n i).symm

end Maps

theorem unit_law_act_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0), x1 = spMap ψ ≫ x0 → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G), (∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left) → ((∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1) → (∀ m, homAt x1 (jetAug : Jet S' (Fin 1 × Fin d) m →ₐ[S'] S') ≫ x' m = 1)) ∧ (∀ F : Fin d → PS S 2 d, (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ m, homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x m = jptG t x0 d x m (0 : Fin 2) * jptG t x0 d x m (1 : Fin 2)) → (∀ m, homAt x1 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (MvPowerSeries.map ψ (F p.2))) ≫ x' m = jptG t x1 d x' m (0 : Fin 2) * jptG t x1 d x' m (1 : Fin 2))) ∧ ∀ act : 𝓞 E → Fin d → PS S 1 d, (∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) → (∀ m (b : 𝓞 E), x m ≫ t.act.act b = homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x m) → (∀ m (b : 𝓞 E), x' m ≫ t.act.act b = homAt x1 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (MvPowerSeries.map ψ (act b p.2))) ≫ x' m) := by
  intro E _ _ _ H X0 t S S' _ _ ψ x0 x1 hx1 d x x' hx'
  subst hx1
  obtain rfl : x' = fun m => jetPtMap ψ x0 d m 1 ≫ x m :=
    funext fun m => Over.OverMorphism.ext (hx' m)
  refine ⟨fun h m => ?_, fun F _ h m => ?_, fun act _ h m b => ?_⟩
  · rw [← Category.assoc, sq_aug, Category.assoc, h m]
    simp [Hom.one_def]
  · simp only [JetTr.psTrunc_map]
    rw [← Category.assoc, sq_subst, Category.assoc, h m]
    simp only [jptG, Hom.mul_def, comp_lift_assoc]
    rw [← Category.assoc (homAt _ _) (jetPtMap _ _ _ _ _), ← Category.assoc (homAt _ _) (jetPtMap _ _ _ _ _),
      sq_copy, sq_copy, Category.assoc, Category.assoc]
  · simp only [JetTr.psTrunc_map]
    rw [← Category.assoc (homAt _ _), sq_subst, Category.assoc, Category.assoc, h m b]

end GlobalTheory.JetPointBC
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.JetPointsUnitLawActionBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetPoints_unit_law_action_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0), x1 = spMap ψ ≫ x0 → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G), (∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left) → ((∀ m, homAt x0 (jetAug : Jet S (Fin 1 × Fin d) m →ₐ[S] S) ≫ x m = 1) → (∀ m, homAt x1 (jetAug : Jet S' (Fin 1 × Fin d) m →ₐ[S'] S') ≫ x' m = 1)) ∧ (∀ F : Fin d → PS S 2 d, (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → (∀ m, homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ x m = jptG t x0 d x m (0 : Fin 2) * jptG t x0 d x m (1 : Fin 2)) → (∀ m, homAt x1 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (MvPowerSeries.map ψ (F p.2))) ≫ x' m = jptG t x1 d x' m (0 : Fin 2) * jptG t x1 d x' m (1 : Fin 2))) ∧ ∀ act : 𝓞 E → Fin d → PS S 1 d, (∀ b j, MvPowerSeries.constantCoeff (act b j) = 0) → (∀ m (b : 𝓞 E), x m ≫ t.act.act b = homAt x0 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (act b p.2)) ≫ x m) → (∀ m (b : 𝓞 E), x' m ≫ t.act.act b = homAt x1 (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (MvPowerSeries.map ψ (act b p.2))) ≫ x' m) := by
  first | exact @GlobalTheory.JetPointBC.unit_law_act_baseChange | exact GlobalTheory.JetPointBC.unit_law_act_baseChange | (intros; apply GlobalTheory.JetPointBC.unit_law_act_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CubeFramesMoveToPullbackTriple
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CubeFramesMoveToPullbackTriple
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.FrameDown

open TopologicalSpace ReciprocityTheory.ChartRestriction.G.DVR

section

variable {X0 X' Y : Scheme.{0}} {L : LB X0} {L' : LB X'} {F : X' ⟶ X0} {K : Type} [Fintype K]

theorem exists_down_val {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y ⟶ X')} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
        gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) =
          pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ q : K → L'.ι, ∃ s : Γ(Y, LB.wchart L' φ' q)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gm r z _ s = (pw w φ' ε r z p q)⁻¹ * gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) := by
    intro q
    have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p,
        r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
        gm r z _ ((u p q)⁻¹ * res inf_le_left (t.s p)) =
          (pw w φ' ε r z p q)⁻¹ * gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) :=
      fun Z r z p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((map_inv _ _).trans (congrArg (·⁻¹) (hu p q _ _ z hz))) (gm_res _ z _ hz _))
    obtain ⟨s, hs⟩ := glue_unit _ (fun p => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q)
      (fun _ => inf_le_right)
      (fun y hy => by
        choose p hp using fun k => exists_chart hL (F (φ' k y))
        exact Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp, hy⟩) (fun p => (u p q)⁻¹ * res inf_le_left (t.s p))
      (fun p p' y hy => by
        rw [hv _ _ y p hy.1, hv _ _ y p' hy.2, pw_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.2.1 hy.1.2 hy.1.2,
          trF_self hL' _ ε (𝟙 Y) y hy.1.2, gen_trans ht (𝟙 Y) y hy.1.1 hy.2.1, inv_one, _root_.mul_one, mul_inv,
          _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun Z r z p h₁ h₂ => ?_⟩
    have hz : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
    exact (gm_res _ z inf_le_right hz s).symm.trans ((congrArg (gm _ z _) (hs p)).trans (hv Z r z p hz))
  choose s hs using glue
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun Z r z p q hp hq => ?_⟩
  · choose p hp using fun k => exists_chart hL (F (φ' k y))
    have m : y ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
    refine (hs j _ (𝟙 Y) y p m hj).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y p m hj')).symm)
    rw [pw_trans hw φ' ε (𝟙 Y) y m m hj hj', trF_self hL _ ε (𝟙 Y) y m, _root_.one_mul, mul_inv, inv_inv,
      _root_.mul_assoc]
  · exact ((congrArg _ (hs q Z r z p hp hq)).trans (mul_inv_cancel_left _ _)).symm

end

theorem frames_pull_back : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → ∃ e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m, (∀ m, (e' m).IsGen) ∧ (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) := by
  intro E _ _ _ H X0 t S _ x0 t' mp w hw d x x' hx e he
  have hφ : ∀ m, (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) =
      cφG t ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] := by
    intro m
    funext J
    let U : Over.mk ((jOG (𝟙 (Sp S)) d m 2).hom ≫ x0) ⟶ jOG x0 d m 2 :=
      Over.homMk (𝟙 _) (by simp [overAt])
    have hj : ∀ i : Fin 2, pushPt mp.cart.1.w (jptG t' (𝟙 (Sp S)) d x' m i) = U ≫ jptG t x0 d x m i := fun i =>
      Over.OverMorphism.ext (by
        show ((homAt (𝟙 (Sp S)) (jetCopy d m i)).left ≫ (x' m).left) ≫ mp.φ =
          𝟙 _ ≫ (homAt x0 (jetCopy d m i)).left ≫ (x m).left
        rw [Category.assoc, hx, Category.id_comp]
        rfl)
    refine (psum_push mp.cart _ ![jptG t x0 d x m (0 : Fin 2), jptG t x0 d x m (1 : Fin 2)] U
      (fun i => ?_) J.down).trans (Category.id_comp _)
    fin_cases i
    · exact hj 0
    · exact hj 1
  choose c₁ hc₁ hcorr using fun m => ChartPrimTrPf.exists_reindex t.PP.L (hφ m) (cε 2) (e m) (he m)
  choose a ha hv using fun m => exists_down_val ((isGen_iff w).1 hw.1) t.PP.isLB t'.PP.isLB (c₁ m) (hc₁ m)
  exact ⟨a, ha, fun m => ⟨c₁ m, hcorr m, ChartPrimTrPf.maps_flat w _ _ (a m) (c₁ m) (hv m)⟩⟩

end GlobalTheory.FrameDown
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.CubeFramesMoveToPullbackTripleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubeFrames_move_to_pullback_triple : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S : Type) [CommRing S] (x0 : Sp S ⟶ X0) (t' : SAB H (Sp S)) (mp : SABMap t' t x0) (w : LB.Iso t'.PP.L (t.PP.L.pull mp.φ)), RigIso mp w → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG (𝟙 (Sp S)) d m 1 ⟶ t'.G), (∀ m, (x' m).left ≫ mp.φ = (x m).left) → ∀ e : ∀ m, FrTyG t x0 d x m, (∀ m, (e m).IsGen) → ∃ e' : ∀ m, FrTyG t' (𝟙 (Sp S)) d x' m, (∀ m, (e' m).IsGen) ∧ (∀ m, ∃ c₁ : LB.Gen (LB.LinComb t.PP.L (fun J => cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)] J ≫ mp.φ) (cε 2)), LB.Gen.Corr t.PP.L _ _ _ _ c₁ (e m) ∧ LB.Gen.Maps (LB.linCombIso w (cφG t' ![jptG t' (𝟙 (Sp S)) d x' m (0 : Fin 2), jptG t' (𝟙 (Sp S)) d x' m (1 : Fin 2)]) (cε 2)) (e' m) (flatGen t.PP.L mp.φ _ _ c₁)) := by
  first | exact @GlobalTheory.FrameDown.frames_pull_back | exact GlobalTheory.FrameDown.frames_pull_back | (intros; apply GlobalTheory.FrameDown.frames_pull_back <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RigidificationAtOriginBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RigidificationAtOriginBaseChange
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)

namespace GlobalTheory.ChartRigBC

open GlobalTheory.RawChartGermBC

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0) (d : ℕ)

theorem jetCoef_eq (κ : Type) (m : ℕ) : jetCoef ψ κ m = jetBC ψ κ m :=
  RingHom.ext fun a => by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    rfl

theorem subst_jetCoef (m n n' : ℕ) (φ : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S)
    (φ' : Fin n × Fin d → MvPolynomial (Fin n' × Fin d) S') (h : ∀ p, φ' p = MvPolynomial.map ψ (φ p)) :
    (Formalism.L2.Pj.homAt x1 (jetSubstP m φ')).left ≫ spMap (jetCoef ψ (Fin n × Fin d) m) =
      spMap (jetCoef ψ (Fin n' × Fin d) m) ≫ (Formalism.L2.Pj.homAt x0 (jetSubstP m φ)).left := by
  obtain rfl : φ' = fun p => MvPolynomial.map ψ (φ p) := funext h
  rw [jetCoef_eq, jetCoef_eq]
  exact spMap_comp_eq _ _ _ _ (PullbackSections.jetSubstP_comp_jetBC ψ m φ)

theorem aug_jetCoef (m n : ℕ) :
    (Formalism.L2.Pj.homAt x1 (jetAug : Jet S' (Fin n × Fin d) m →ₐ[S'] S')).left ≫ spMap (jetCoef ψ (Fin n × Fin d) m) =
      spMap ψ ≫ (Formalism.L2.Pj.homAt x0 (jetAug : Jet S (Fin n × Fin d) m →ₐ[S] S)).left := by
  rw [jetCoef_eq]
  exact spMap_comp_eq _ _ _ _ (PullbackSections.jetAug_comp_jetBC ψ _ m)

theorem overAt_hom_comp :
    (overAt (spMap ψ ≫ x0) S').hom = spMap ψ ≫ (overAt x0 S).hom := by
  change spMap (algebraMap S' S') ≫ spMap ψ ≫ x0 = spMap ψ ≫ spMap (algebraMap S S) ≫ x0
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  exact spMap_comp_eq _ _ _ _ (RingHom.ext fun _ => rfl)

theorem val_eLG_bc (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) S)
    (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G)
    (hx : ∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left)
    (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t x1 d x' m)
    (he : ∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L _ _ (e m) (spMap (jetCoef ψ (Fin 2 × Fin d) m))))
    (wP : PrimTyG t) (m : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (jOG x1 d m 1).left) (z : Z) {J}
    (hJ : Good t.PP.L z J) :
    val (eLG t x1 d x' (fun a i => MvPowerSeries.map ψ (act a i)) e' wP m) r z J =
      val (eLG t x0 d x act e wP m) (r ≫ spMap (jetCoef ψ (Fin 1 × Fin d) m)) z J := by
  refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
  refine congrArg₂ (· * ·) ?_ ?_
  · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    refine congrArg (fun q => val wP q z J) ?_
    exact (congrArg (r ≫ ·) (hx m)).trans (Category.assoc _ _ _).symm
  · refine (val_pull hJ _ _ _).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm)
    refine (val_corr hJ (he m) _).trans ((val_pull hJ _ _ _).trans ?_)
    refine congrArg (fun q => val (e m) q z J) ?_
    refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    refine congrArg (r ≫ ·) (subst_jetCoef ψ x0 x1 d m 2 1 _ _ ?_)
    rintro ⟨i, j⟩
    fin_cases i
    · exact (MvPolynomial.map_X ψ _).symm
    · exact (map_psIn ψ d m _ _).symm

end GlobalTheory.ChartRigBC

namespace GlobalTheory


open ChartRigBC in
theorem rigidificationAtOrigin_baseChange :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0), x1 = spMap ψ ≫ x0 → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G), (∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t x1 d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L _ _ (e m) (spMap (jetCoef ψ (Fin 2 × Fin d) m)))) → ∀ (act : 𝓞 E → Fin d → PS S 1 d) (wP : PrimTyG t), wP.IsGen → Rig0G t x0 d x act e wP → Rig0G t x1 d x' (fun a i => (MvPowerSeries.map ψ (act a i))) e' wP := by
  intro E _ _ _ H X0 t S S' _ _ ψ x0 x1 hx1 d x x' hx e e' _ _ he act wP _ h0
  have hL := t.PP.isLB
  refine corr_of_val hL fun y J hJ => ?_
  refine (val_pull hJ _ _ _).trans ((val_eLG_bc t ψ x0 x1 d act x x' hx e e' he wP 0 _ y hJ).trans ?_)
  refine Eq.trans ?_ (GermB.val_rigT _ _ _ _ _ y J hJ).symm
  have h1 := (val_pull hJ _ _ _).symm.trans ((val_corr hJ h0 (spMap ψ)).trans (GermB.val_rigT _ _ _ _ _ y J hJ))
  refine (congrArg (fun q => val (eLG t x0 d x act e wP 0) q y J) ?_).trans
    (h1.trans (congrArg (fun q => val t.PP.rig q y J) ?_))
  · rw [Category.id_comp]; exact aug_jetCoef ψ x0 x1 d 0 1
  · subst hx1
    rw [Category.id_comp]; exact (overAt_hom_comp ψ x0).symm

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.RigidificationAtOriginBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt comp1 FGLaw)
open MvPolynomial (X)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rigidificationAtOrigin_baseChange_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X0 : Scheme.{0}) (t : SAB H X0) (S S' : Type) [CommRing S] [CommRing S'] (ψ : S →+* S') (x0 : Sp S ⟶ X0) (x1 : Sp S' ⟶ X0), x1 = spMap ψ ≫ x0 → ∀ (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G) (x' : ∀ m, jOG x1 d m 1 ⟶ t.G), (∀ m, (x' m).left = spMap (jetCoef ψ (Fin 1 × Fin d) m) ≫ (x m).left) → ∀ (e : ∀ m, FrTyG t x0 d x m) (e' : ∀ m, FrTyG t x1 d x' m), (∀ m, (e m).IsGen) → (∀ m, (e' m).IsGen) → (∀ m, LB.Gen.Corr t.PP.L _ _ _ _ (e' m) (LB.pullGen t.PP.L _ _ (e m) (spMap (jetCoef ψ (Fin 2 × Fin d) m)))) → ∀ (act : 𝓞 E → Fin d → PS S 1 d) (wP : PrimTyG t), wP.IsGen → Rig0G t x0 d x act e wP → Rig0G t x1 d x' (fun a i => (MvPowerSeries.map ψ (act a i))) e' wP := by
  first | exact @GlobalTheory.rigidificationAtOrigin_baseChange | exact GlobalTheory.rigidificationAtOrigin_baseChange | (intros; apply GlobalTheory.rigidificationAtOrigin_baseChange <;> assumption)
end
end
