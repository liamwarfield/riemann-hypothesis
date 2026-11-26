module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompatibleSections
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfThickenings
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Laws5
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsOfH0EqOneClosedFields
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProductOfSectionsExpandsToConvolution

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsUnconditional
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU.TorsionCount

theorem card_torsion_points_unconditional :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) :=
  GlobalTheory.T.card_torsion_points_abelianVariety GlobalTheory.laws_without_cohomology.1 GlobalTheory.laws_without_cohomology.2.1

end GlobalTheory.UU.TorsionCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLineBundleOfThickenings
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LBAlg

variable {X Y Z : Scheme.{0}}

theorem gm_tw (A H : LB X) (t : ℤ) (r : Z ⟶ X) (z : Z) (p q : A.ι × H.ι)
    (hm : r z ∈ A.U p.1 ⊓ H.U p.2 ⊓ (A.U q.1 ⊓ H.U q.2)) :
    gm r z ((tw A H t).U p ⊓ (tw A H t).U q) ((tw A H t).g p q) =
      gm r z _ (A.g p.1 q.1) * gm r z _ (H.g p.2 q.2) ^ t := by
  refine (gm_div (AbLaw.pw H (-t)) A r z p q hm).trans ?_
  refine congrArg _ ((congrArg (·⁻¹) (map_zpow _ _ _)).trans ?_)
  rw [zpow_neg, inv_inv]
  rfl

theorem lbIso_of_germs {A B : LB X} (s : ∀ p : B.ι × A.ι, Γ(X, B.U p.1 ⊓ A.U p.2)ˣ)
    (h : ∀ (x : X) (p q : B.ι × A.ι), x ∈ B.U p.1 → x ∈ A.U p.2 → x ∈ B.U q.1 → x ∈ A.U q.2 →
      gm (𝟙 X) x _ (s p) = gm (𝟙 X) x _ (B.g p.1 q.1) * (gm (𝟙 X) x _ (A.g p.2 q.2))⁻¹ * gm (𝟙 X) x _ (s q)) :
    LBIso A B := by
  refine ⟨⟨s⟩, fun p q => unit_ext fun x hx => ?_⟩
  exact (gm_res _ x _ hx _).trans ((h x p q hx.1.1 hx.1.2 hx.2.1 hx.2.2).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_div A B (𝟙 X) x p q hx) (gm_res _ x _ hx _))).symm)

theorem germs_of_isGen {A B : LB X} {w : LB.Iso A B} (hw : w.IsGen) (x : X) (p q : B.ι × A.ι)
    (h₁ : x ∈ B.U p.1) (h₂ : x ∈ A.U p.2) (h₃ : x ∈ B.U q.1) (h₄ : x ∈ A.U q.2) :
    gm (𝟙 X) x (B.U p.1 ⊓ A.U p.2) (w.s p) = gm (𝟙 X) x _ (B.g p.1 q.1) * (gm (𝟙 X) x _ (A.g p.2 q.2))⁻¹ *
      gm (𝟙 X) x (B.U q.1 ⊓ A.U q.2) (w.s q) := by
  have hx : (𝟙 X : X ⟶ X) x ∈ B.U p.1 ⊓ A.U p.2 ⊓ (B.U q.1 ⊓ A.U q.2) := ⟨⟨h₁, h₂⟩, h₃, h₄⟩
  exact (gm_res _ x _ hx _).symm.trans ((congrArg (gm (𝟙 X) x _) (hw p q)).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_div A B (𝟙 X) x p q hx) (gm_res _ x _ hx _))))

theorem lbIso_self {A : LB X} (hA : A.IsLB) : LBIso A A := by
  refine lbIso_of_germs (fun p => A.g p.1 p.2) fun x p q h₁ h₂ h₃ h₄ => ?_
  rw [← gm_cocycle hA (𝟙 X) x h₁ h₂ h₃, ← gm_cocycle hA (𝟙 X) x h₂ h₃ h₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

def chartPullTw {A' H' : LB Y} {A H : LB X} {h : Y ⟶ X} (a : ChartPull A' A h) (b : ChartPull H' H h) (t : ℤ) :
    ChartPull (tw A' H' t) (tw A H t) h where
  idx p := (a.idx p.1, b.idx p.2)
  le p y hy := ⟨a.le _ hy.1, b.le _ hy.2⟩
  g y p q hp hq := by
    refine (gm_tw A' H' t (𝟙 Y) y p q ⟨hp, hq⟩).trans (Eq.trans ?_ (gm_tw A H t h y (a.idx p.1, b.idx p.2)
      (a.idx q.1, b.idx q.2) ⟨⟨a.le _ hp.1, b.le _ hp.2⟩, a.le _ hq.1, b.le _ hq.2⟩).symm)
    rw [a.g y _ _ hp.1 hq.1, b.g y _ _ hp.2 hq.2]

theorem lbIso_tw_congr {A B H : LB X} (hH : H.IsLB) (t : ℤ) (h : LBIso A B) : LBIso (tw A H t) (tw B H t) := by
  obtain ⟨w, hw⟩ := h
  have l₁ : ∀ p : (B.ι × H.ι) × (A.ι × H.ι), (tw B H t).U p.1 ⊓ (tw A H t).U p.2 ≤ B.U p.1.1 ⊓ A.U p.2.1 :=
    fun p x hx => ⟨hx.1.1, hx.2.1⟩
  have l₂ : ∀ p : (B.ι × H.ι) × (A.ι × H.ι), (tw B H t).U p.1 ⊓ (tw A H t).U p.2 ≤ H.U p.1.2 ⊓ H.U p.2.2 :=
    fun p x hx => ⟨hx.1.2, hx.2.2⟩
  have v : ∀ (x : X) (p : (B.ι × H.ι) × (A.ι × H.ι)), x ∈ (tw B H t).U p.1 ⊓ (tw A H t).U p.2 →
      gm (𝟙 X) x _ (res (l₁ p) (w.s (p.1.1, p.2.1)) * res (l₂ p) (H.g p.1.2 p.2.2) ^ t) =
        gm (𝟙 X) x (B.U p.1.1 ⊓ A.U p.2.1) (w.s (p.1.1, p.2.1)) * gm (𝟙 X) x _ (H.g p.1.2 p.2.2) ^ t :=
    fun x p hx => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x _ hx _)
      ((map_zpow _ _ _).trans (congrArg (· ^ t) (gm_res _ x _ hx _))))
  refine lbIso_of_germs (fun p => res (l₁ p) (w.s (p.1.1, p.2.1)) * res (l₂ p) (H.g p.1.2 p.2.2) ^ t)
    fun x p q h₁ h₂ h₃ h₄ => ?_
  refine (v x p ⟨h₁, h₂⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg₂ (· * ·)
    (gm_tw B H t (𝟙 X) x p.1 q.1 ⟨h₁, h₃⟩) (congrArg (·⁻¹) (gm_tw A H t (𝟙 X) x p.2 q.2 ⟨h₂, h₄⟩)))
    (v x q ⟨h₃, h₄⟩)).symm)
  rw [germs_of_isGen hw x (p.1.1, p.2.1) (q.1.1, q.2.1) h₁.1 h₂.1 h₃.1 h₄.1,
    ← gm_cocycle hH (𝟙 X) x h₁.2 h₂.2 h₃.2, ← gm_cocycle hH (𝟙 X) x h₂.2 h₃.2 h₄.2]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem lbIso_tw_tw {A H : LB X} (hA : A.IsLB) (hH : H.IsLB) (t : ℤ) : LBIso A (tw (tw A H t) H (-t)) := by
  have l₁ : ∀ p : ((A.ι × H.ι) × H.ι) × A.ι, (tw (tw A H t) H (-t)).U p.1 ⊓ A.U p.2 ≤ A.U p.1.1.1 ⊓ A.U p.2 :=
    fun p x hx => ⟨hx.1.1.1, hx.2⟩
  have l₂ : ∀ p : ((A.ι × H.ι) × H.ι) × A.ι, (tw (tw A H t) H (-t)).U p.1 ⊓ A.U p.2 ≤ H.U p.1.1.2 ⊓ H.U p.1.2 :=
    fun p x hx => ⟨hx.1.1.2, hx.1.2⟩
  have v : ∀ (x : X) (p : ((A.ι × H.ι) × H.ι) × A.ι), x ∈ (tw (tw A H t) H (-t)).U p.1 ⊓ A.U p.2 →
      gm (𝟙 X) x _ (res (l₁ p) (A.g p.1.1.1 p.2) * res (l₂ p) (H.g p.1.1.2 p.1.2) ^ t) =
        gm (𝟙 X) x _ (A.g p.1.1.1 p.2) * gm (𝟙 X) x _ (H.g p.1.1.2 p.1.2) ^ t :=
    fun x p hx => (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ x _ hx _)
      ((map_zpow _ _ _).trans (congrArg (· ^ t) (gm_res _ x _ hx _))))
  refine lbIso_of_germs (fun p => res (l₁ p) (A.g p.1.1.1 p.2) * res (l₂ p) (H.g p.1.1.2 p.1.2) ^ t)
    fun x p q h₁ h₂ h₃ h₄ => ?_
  refine (v x p ⟨h₁, h₂⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·) (congrArg (· * _)
    ((gm_tw (tw A H t) H (-t) (𝟙 X) x p.1 q.1 ⟨h₁, h₃⟩).trans (congrArg (· * _)
      (gm_tw A H t (𝟙 X) x p.1.1 q.1.1 ⟨h₁.1, h₃.1⟩)))) (v x q ⟨h₃, h₄⟩)).symm)
  rw [← gm_cocycle hA (𝟙 X) x h₁.1.1 h₂ h₃.1.1, ← gm_cocycle hA (𝟙 X) x h₂ h₃.1.1 h₄,
    ← gm_cocycle hH (𝟙 X) x h₁.1.2 h₁.2 h₃.1.2, ← gm_cocycle hH (𝟙 X) x h₁.2 h₃.1.2 h₃.2]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem surjective_thickTrans (V : Type) [CommRing V] (I : Ideal V) (e : ℕ) : Surjective (thickTrans V I e) := by
  refine ⟨fun x => ?_⟩
  have h : x ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1)))) := by
    rw [range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective _)]
    intro a ha
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    have ha' : a ∈ I ^ (e + 1) := (GlobalTheory.SecLifts.mk_mem_ker_factor _ a).1 ha
    have h2 : Ideal.Quotient.mk (I ^ (e + 1 + 1)) a ^ 2 = 0 := by
      rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      have := Ideal.pow_mem_pow ha' 2
      rw [← pow_mul] at this
      exact Ideal.pow_le_pow_right (by omega) this
    exact x.isPrime.mem_of_pow_mem 2 (by rw [h2]; exact Ideal.zero_mem _)
  exact h


open GlobalTheory.MorAlg in
theorem exists_lineBundle_of_thickenings : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans V (IsLocalRing.maximalIdeal V) e)) → ∀ (B : Over (Spec (CommRingCat.of V))) (b : ∀ e, (Y e).left ⟶ B.left), IsProjBy B.hom → Flat B.hom → (∀ e, IsPullback (b e) (Y e).hom B.hom (thick V (IsLocalRing.maximalIdeal V) e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → ∃ M : LB B.left, M.IsLB ∧ ∀ e, LBIso (N e) (M.pull (b e)) := by
  intro V _ _ _ _ Y β hβ B b hB hfl hb hc N v hN
  obtain ⟨H, hH, m, σ, hσ⟩ := id hB
  have hL : ∀ e, (H.pull (b e)).IsLB := fun e => pull_isLB hH _
  obtain ⟨σ₀, w₀, hw₀, c₀⟩ := exists_isPull (b 0) hH σ
  have hva : VeryAmpleBy (Y 0).hom (H.pull (b 0)) σ₀ := by
    refine GlobalTheory.AbLaw.VeryAmplePull.veryAmpleBy_pull V B.left B.hom H m σ hH hσ _
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal V ^ (0 + 1))) _ _ (b 0) (hb 0).w ?_ _ w₀ _ (hL 0) hw₀ c₀
    have e : pullback.lift (b 0) (Y 0).hom (hb 0).w = (hb 0).isoPullback.hom := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, IsPullback.isoPullback_hom_fst]
      · rw [pullback.lift_snd, IsPullback.isoPullback_hom_snd]
    rw [e]
    infer_instance
  obtain ⟨t₁, ht₁⟩ := GlobalTheory.T.serre_vanishing_very_ample.1 _ _ _ _ _ _ (hL 0) hva (N 0) (hN 0).1
  obtain ⟨t₂, ht₂⟩ := GlobalTheory.TwistGen.twist_generated _ _ _ _ _ _ (hL 0) hva (N 0) (hN 0).1
  obtain ⟨t, h₁, h₂⟩ : ∃ t, t₁ ≤ t ∧ t₂ ≤ t := ⟨max t₁ t₂, le_max_left _ _, le_max_right _ _⟩
  obtain ⟨n, u, hu⟩ := ht₂ t h₂
  have hT : ∀ e, (tw (N e) (H.pull (b e)) t).IsLB := fun e => isLB_tw (hN e).1 (hL e) t
  have hv' : ∀ e, LBIso (tw (N e) (H.pull (b e)) t) ((tw (N (e + 1)) (H.pull (b (e + 1))) t).pull (β e)) :=
    fun e => LBIso.trans (hT e) (isLB_tw (pull_isLB (hN (e + 1)).1 _) (hL e) t) (pull_isLB (hT (e + 1)) _)
      (lbIso_tw_congr (hL e) t ⟨v e, (hN e).2⟩)
      (LBIso.chartPull (chartPullTw (Geo.Tor.chartPullPull _ _ _ rfl)
        (chartPullSame H _ _ _ (β e) fun _ => (hc e).symm) t) (Geo.Tor.chartPullPull _ _ _ rfl) (lbIso_self (hT (e + 1))))
  choose v' hv' using hv'
  have hflY : ∀ e, Flat (Y e).hom := fun e => MorphismProperty.of_isPullback (P := @Flat) (hb e) hfl
  choose s hs0 hs using fun j => GlobalTheory.SecLifts.exists_compatible_sections V Y β hβ hflY
    (fun e => tw (N e) (H.pull (b e)) t) v' (fun e => ⟨hT e, hv' e⟩) (ht₁ t h₁) (u j)
  have hcov : ∀ e, ⨆ j, nonzeroLocus (s j e) = ⊤ := by
    intro e
    induction e with
    | zero => simpa only [hs0] using hu
    | succ e ih =>
      have hsurj : Surjective (β e) :=
        MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip (surjective_thickTrans V _ e)
      refine top_le_iff.1 fun y _ => ?_
      obtain ⟨x, rfl⟩ := hsurj.surj y
      obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 (show x ∈ ⨆ j, nonzeroLocus (s j e) by rw [ih]; trivial)
      rw [(GlobalTheory.SecPullIso.section_pull _ _ (β e) _ _ (v' e) (hT (e + 1)) (hT e) (hv' e) (s j (e + 1))).2 _
        (hs j e)] at hj
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨j, hj⟩
  obtain ⟨P, p, O, x, hO, hx, heq⟩ := GlobalTheory.ProjQuot.exists_veryAmpleBy_of_ideal V n ⊥ (by
    intro F hF d
    rw [Ideal.mem_bot] at hF ⊢
    rw [hF, map_zero])
  choose φ w hφ hw cw using fun e => GlobalTheory.exists_hom_of_veryAmpleBy V P p O n x hO hx (Y e).left
    ((Y e).hom ≫ thick V (IsLocalRing.maximalIdeal V) e) _ (fun j => s j e) (hT e) (hcov e) (by
      intro d F hF h0 k
      obtain ⟨i, hi⟩ := (heq d F hF).1 h0 0
      rw [Ideal.mem_bot, mul_eq_zero] at hi
      rw [hi.resolve_left (pow_ne_zero _ (MvPolynomial.X_ne_zero _)), map_zero])
  have hφc : ∀ e, β e ≫ φ (e + 1) = φ e := fun e => by
    obtain ⟨w₁, hw₁, c₁⟩ := IsPull.comp (s := x) (s' := fun j => s j (e + 1)) (s'' := fun j => s j e)
      hO (hT (e + 1)) (hT e) ⟨w (e + 1), hw (e + 1), cw (e + 1)⟩ ⟨v' e, hv' e, fun j => hs j e⟩
    refine GlobalTheory.MapUniq.hom_eq_of_pull_sections V P p O n x hO hx _ _ (fun j => s j e) _ _ w₁ (w e) (hT e) ?_
      hw₁ (hw e) c₁ (cw e)
    rw [Category.assoc, hφ, hφ, ← Category.assoc, (hβ e).w, Category.assoc, thickTrans_comp]
  have hi : ∀ e, (hb e).isoPullback.inv ≫ β e =
      thickMap V (IsLocalRing.maximalIdeal V) e B ≫ (hb (e + 1)).isoPullback.inv := fun e => by
    apply (hb (e + 1)).hom_ext
    · rw [Category.assoc, Category.assoc, hc, IsPullback.isoPullback_inv_fst, IsPullback.isoPullback_inv_fst]
      exact ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm
    · rw [Category.assoc, Category.assoc, (hβ e).w, IsPullback.isoPullback_inv_snd_assoc,
        IsPullback.isoPullback_inv_snd]
      exact (pullback.lift_snd _ _ _).symm
  obtain ⟨g, hg⟩ := exists_hom_of_thickenings V B (Over.mk p) hB ⟨O, hO, n, x, hx⟩ hfl
    (fun e => (hb e).isoPullback.inv ≫ φ e) (fun e => by
      refine (Category.assoc _ _ _).trans ((congrArg _ (hφ e)).trans ?_)
      rw [IsPullback.isoPullback_inv_snd_assoc]
      exact pullback.condition.symm) (fun e => by
      rw [← hφc e]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ (e + 1)) (hi e).symm).trans
        (Category.assoc _ _ _)))
  let g' : B.left ⟶ P := g.left
  have hbg : ∀ e, φ e = b e ≫ g' := fun e => by
    have h : pullback.fst B.hom (thick V (IsLocalRing.maximalIdeal V) e) ≫ g' = (hb e).isoPullback.inv ≫ φ e := hg e
    rw [← (hb e).isoPullback_hom_fst, Category.assoc, h, Iso.hom_inv_id_assoc]
  have hM : (tw (O.pull g') H (-t)).IsLB := isLB_tw (pull_isLB hO _) hH _
  refine ⟨tw (O.pull g') H (-t), hM, fun e => ?_⟩
  have hO' : (tw (O.pull (φ e)) (H.pull (b e)) (-t)).IsLB := isLB_tw (pull_isLB hO _) (hL e) _
  exact LBIso.trans (hN e).1 hO' (pull_isLB hM _)
    (LBIso.trans (hN e).1 (isLB_tw (hT e) (hL e) _) hO' (lbIso_tw_tw (hN e).1 (hL e) t)
      (lbIso_tw_congr (hL e) (-t) ⟨w e, hw e⟩))
    (LBIso.chartPull (chartPullTw (chartPullSame O _ _ _ (b e) fun _ => hbg e) (Geo.Tor.chartPullPull _ _ _ rfl) (-t))
      (Geo.Tor.chartPullPull _ _ _ rfl) (lbIso_self hM))

end GlobalTheory.LBAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FurtherLawsOfLaws
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem furtherLaws_of_laws :
    Laws → DVR.TwistBaseChangeStatement → Laws3 ∧ Laws4 ∧ Laws5 ∧ Laws6 :=
  fun h ht =>
    ⟨laws3, uniformisationLaws_of_baseChange_laws h.polBaseChange h.globalFns h.secBaseChange ht,
      laws5 h.globalFns h.secBaseChange,
      lawsSixth_of_unifUniq h.globalFns h.secBaseChange h.ample⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HeckeOperatorMultiplicativeOnSectionProducts
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HeckeOperatorMultiplicativeOnSectionProducts
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.PhiMul

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem exists_frm_pow {D : DegPre R} {k : ℕ} {b : TF (R := R) F ⟶ D.P.A} (w : Frm D F k b) (hw : w.IsGen)
    (n N : ℕ) (hN : N = k * n) : ∃ w' : Frm D F N b, w'.IsGen ∧
      ∀ z J, Good D.P.L z J → val w' (𝟙 _) z J = val w (𝟙 _) z J ^ n := by
  obtain ⟨w', h₁, h₂⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b) (ε' := DegPre.lineε N)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      congr 1
      subst hN
      fin_cases i <;> simp [DegPre.lineε, mul_comm])
    (GeneratorPullback.powGen D.P.L _ _ w n) (powGen_isGen _ _ _ _ hw n)
  exact ⟨w', h₁, fun z J hJ => (h₂ _ _ z J hJ).trans (map_pow _ _ _)⟩


omit [IsDomain R] in
theorem exists_secA_mul {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {a b c : ℕ} (hc : c = a + b)
    (t : SecA A F a) (t' : SecA A F b) : ∃ u : SecA A F c,
      ∀ z J, Good A.L z J → sA u (𝟙 _) z J = sA t (𝟙 _) z J * sA t' (𝟙 _) z J := by
  obtain ⟨u, hu⟩ := exists_sec A.isLB (φ' := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left)
    (ε' := fun _ => (c : ℤ)) (fun U _ h => by
      subst hc
      simp [Fintype.prod_sum_type, zpow_add])
    (H1.SectionArithmetic.mulSec (L := A.L) (φ := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε := fun _ => (a : ℤ))
      (φ' := fun _ : Fin 1 => (snd (TFK (R := R) F) A.A).left) (ε' := fun _ => (b : ℤ)) t t')
  exact ⟨u, fun z J hJ => (hu _ _ z J hJ).trans (H1.SectionArithmetic.sval_mulSec _ _ _ z hJ)⟩

theorem phi_mul : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (w : Frm D.toPre F k p.g.b), w.IsGen → ∀ (n : Fin 3 → ℕ) (N : Fin 3 → ℕ), (∀ i, 1 ≤ n i ∧ N i = k * n i) → n 2 = n 0 + n 1 → ∀ (q : ∀ i, QkPt D.toPre F (N i)) (ω : ∀ i, Frm D.toPre F (N i) (q i).g.b), (∀ i, (q i).y = n i • p.y ∧ (q i).g = p.g ∧ ((ω i).IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val (ω i) (𝟙 _) z J = val w (𝟙 _) z J ^ n i)) → ∀ (t t' : ∀ i, SecA A F (N i)) (s s' : ∀ i, Fam D.toPre F (N i)), (∀ i, U.ExpandsF F (N i) w₀ (t i) (s i) ∧ U.ExpandsF F (N i) w₀ (t' i) (s' i) ∧ PhiRel D.toPre F (N i) (q i) (ω i) (s i) (s' i)) → (∀ z J, Good A.L z J → sA (t 2) (𝟙 _) z J = sA (t 0) (𝟙 _) z J * sA (t 1) (𝟙 _) z J) → ∀ z J, Good A.L z J → sA (t' 2) (𝟙 _) z J = sA (t' 0) (𝟙 _) z J * sA (t' 1) (𝟙 _) z J := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ _ w₀ hw₀ k hk p w hw n N hn hn2 q ω hq t t' s s' hs ht
  have hN1 : ∀ i, 1 ≤ N i := fun i => by rw [(hn i).2]; exact Nat.mul_pos hk (hn i).1
  have hN2 : N 2 = N 0 + N 1 := by rw [(hn 0).2, (hn 1).2, (hn 2).2, hn2, mul_add]
  have hB := (expBijF_and_expandsF_lin hL R I hI D A G hG U).1 F (N 2) (hN1 2) w₀ hw₀
  obtain ⟨u, hu⟩ := exists_secA_mul hN2 (t' 0) (t' 1)
  obtain ⟨r, hr, -⟩ := hB.1 u
  have hrs : r = s' 2 := by
    refine CoefDet.fam_eq_of_coef_eq hL R I hI D F (N 2) r (s' 2) fun g₀ => ?_
    letI := GlobalTheory.TorusExt.gtGroup D.toPre F
    have hadd : g₀.IsAdd p.g (g₀ + p.g) := (GlobalTheory.TorusExt.isAdd_iff_eq _ _ _).2 rfl
    obtain ⟨ω₀, hω₀⟩ : ∃ ω₀ : Frm D.toPre F k g₀.b, ω₀.IsGen :=
      exists_gen_of_local (V := F) D.toPre.P.L D.toPre.P.isLB _ _
    obtain ⟨ω₁, hω₁, -, hφ⟩ := CoefPhi.coef_phi hL R I hI D F k hk p w hw g₀ _ hadd ω₀ hω₀
    choose a ha using fun i => exists_frm_pow ω₀ hω₀ (n i) (N i) (hn i).2
    choose b hb using fun i => exists_frm_pow ω₁ hω₁ (n i) (N i) (hn i).2
    have hc : ∀ i α, coef (s' i) g₀ (a i) (α + (q i).y) = coef (s i) (g₀ + p.g) (b i) α := fun i =>
      hφ (n i) (N i) (hn i).1 (hn i).2 (q i) (hq i).1 (hq i).2.1 (ω i) (a i) (b i) (hq i).2.2 (ha i) (hb i)
        (s i) (s' i) (hs i).2.2
    refine ⟨a 2, (ha 2).1, fun χ => ?_⟩
    have S₀ := GlobalTheory.T.product_of_sections_expands_to_convolution hL R I hI D A G hG U F w₀ hw₀ (N 0) (N 1) (N 2) (hN1 0) (hN1 1) hN2 (t' 0) (t' 1) u
      (s' 0) (s' 1) r (hs 0).2.1 (hs 1).2.1 hr hu g₀ (a 0) (a 1) (a 2) (ha 0).1 (ha 1).1 (ha 2).1
      (fun z J hJ => by rw [(ha 0).2 z J hJ, (ha 1).2 z J hJ, (ha 2).2 z J hJ, hn2, pow_add]) χ
    have S₁ := GlobalTheory.T.product_of_sections_expands_to_convolution hL R I hI D A G hG U F w₀ hw₀ (N 0) (N 1) (N 2) (hN1 0) (hN1 1) hN2 (t 0) (t 1) (t 2)
      (s 0) (s 1) (s 2) (hs 0).1 (hs 1).1 (hs 2).1 ht (g₀ + p.g) (b 0) (b 1) (b 2) (hb 0).1 (hb 1).1 (hb 2).1
      (fun z J hJ => by rw [(hb 0).2 z J hJ, (hb 1).2 z J hJ, (hb 2).2 z J hJ, hn2, pow_add]) (χ - (q 2).y)
    have hy : (q 2).y = (q 0).y + (q 1).y := by rw [(hq 0).1, (hq 1).1, (hq 2).1, hn2, add_smul]
    have S₂ := ((GlobalTheory.AdicSum.sumF_calculus R I hI F _ _ (fun _ => 0) _ 0).2.2 _ (fun ψ => ψ + (q 0).y)
      (add_left_injective _) (fun i hi => absurd ⟨i - (q 0).y, sub_add_cancel _ _⟩ hi)).2 S₀
    have e : ((fun ψ => coef (s' 0) g₀ (a 0) ψ * coef (s' 1) g₀ (a 1) (χ - ψ)) ∘ fun ψ => ψ + (q 0).y) =
        fun ψ => coef (s 0) (g₀ + p.g) (b 0) ψ * coef (s 1) (g₀ + p.g) (b 1) (χ - (q 2).y - ψ) := by
      funext ψ
      rw [← hc 0, ← hc 1, hy]
      have e' : χ - ((q 0).y + (q 1).y) - ψ + (q 1).y = χ - (ψ + (q 0).y) := by abel
      rw [e']
      rfl
    rw [e] at S₂
    rw [(GlobalTheory.AdicSum.sumF_calculus R I hI F _ _ (fun _ => 0) _ _).1 S₂ S₁, ← hc 2, sub_add_cancel]
  obtain rfl : u = t' 2 := (hB.2 (s' 2)).unique (hrs ▸ hr) (hs 2).2.1
  exact hu

end GlobalTheory.UT.PhiMul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HeckeOperatorMultiplicativeOnSectionProductsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeOperator_multiplicative_on_section_products : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ (k : ℕ), 1 ≤ k → ∀ (p : QkPt D.toPre F k) (w : Frm D.toPre F k p.g.b), w.IsGen → ∀ (n : Fin 3 → ℕ) (N : Fin 3 → ℕ), (∀ i, 1 ≤ n i ∧ N i = k * n i) → n 2 = n 0 + n 1 → ∀ (q : ∀ i, QkPt D.toPre F (N i)) (ω : ∀ i, Frm D.toPre F (N i) (q i).g.b), (∀ i, (q i).y = n i • p.y ∧ (q i).g = p.g ∧ ((ω i).IsGen ∧ ∀ z J, Good D.toPre.P.L z J → val (ω i) (𝟙 _) z J = val w (𝟙 _) z J ^ n i)) → ∀ (t t' : ∀ i, SecA A F (N i)) (s s' : ∀ i, Fam D.toPre F (N i)), (∀ i, U.ExpandsF F (N i) w₀ (t i) (s i) ∧ U.ExpandsF F (N i) w₀ (t' i) (s' i) ∧ PhiRel D.toPre F (N i) (q i) (ω i) (s i) (s' i)) → (∀ z J, Good A.L z J → sA (t 2) (𝟙 _) z J = sA (t 0) (𝟙 _) z J * sA (t 1) (𝟙 _) z J) → ∀ z J, Good A.L z J → sA (t' 2) (𝟙 _) z J = sA (t' 0) (𝟙 _) z J * sA (t' 1) (𝟙 _) z J := by
  first | exact @GlobalTheory.UT.PhiMul.phi_mul | exact GlobalTheory.UT.PhiMul.phi_mul | (intros; apply GlobalTheory.UT.PhiMul.phi_mul <;> assumption)
end
end
