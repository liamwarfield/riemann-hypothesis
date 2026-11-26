module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionRatiosGenerateModMaximal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupMorphismsAgreeNearPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSectionRatioEqNearThickeningPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfAgreeOnAffineOpenGenerators
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfAgreeOnAffineOpenGenerators
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.AffineOpenAgree

theorem app_restrict_eq (X W : Scheme.{0}) (N : X.Opens) (c : W ⟶ N.toScheme) (hc : ⊤ ≤ (c ≫ N.ι) ⁻¹ᵁ N) :
    (c ≫ N.ι).app N ≫ W.presheaf.map (homOfLE hc).op = N.topIso.inv ≫ c.appTop := by
  have h0 : (⊤ : N.toScheme.Opens) ≤ N.ι ⁻¹ᵁ N := by simp
  have e1 : N.topIso.inv = N.ι.app N ≫ N.toScheme.presheaf.map (homOfLE h0).op := by
    rw [Scheme.Opens.topIso_inv, Scheme.Opens.ι_app]
    change _ = X.presheaf.map _ ≫ X.presheaf.map _
    exact (congrArg X.presheaf.map (Subsingleton.elim _ _)).trans (X.presheaf.map_comp _ _)
  have e2 := c.naturality (homOfLE h0).op
  rw [e1, Scheme.Hom.comp_app]
  refine (Category.assoc _ _ _).trans ((Category.assoc _ _ _).trans ?_).symm |>.symm
  refine congrArg (N.ι.app N ≫ ·) ?_
  refine Eq.trans ?_ e2.symm
  rfl

theorem cst_pull {R : Type} [CommRing R] {X W : Scheme.{0}} (sm : X ⟶ Spec (CommRingCat.of R)) (N : X.Opens)
    (c : W ⟶ X) (hc : ⊤ ≤ c ⁻¹ᵁ N) (x : R) :
    (W.presheaf.map (homOfLE hc).op).hom ((c.app N).hom (GlobalTheory.AbLaw.cst sm N x)) =
      (c ≫ sm).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) := by
  have e := c.naturality (homOfLE (le_top : N ≤ ⊤)).op
  have e' := congrArg (fun f => (f ≫ W.presheaf.map (homOfLE hc).op).hom (sm.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x))) e
  simp only [Category.assoc, ← Functor.map_comp] at e'
  simp only [GlobalTheory.AbLaw.cst, GlobalTheory.AbLaw.rs, RingHom.comp_apply]
  refine (e'.trans ?_)
  rw [Scheme.Hom.comp_appTop]
  have : ((TopologicalSpace.Opens.map c.base).map (homOfLE (le_top : N ≤ ⊤)).op.unop).op ≫ (homOfLE hc).op = 𝟙 _ := Subsingleton.elim _ _
  rw [this]
  erw [W.presheaf.map_id, Category.comp_id]
  rfl

end GlobalTheory.AffineOpenAgree

namespace GlobalTheory
open AffineOpenAgree

theorem eq_of_agree_on_generators (R : Type) [CommRing R] (X W : Scheme.{0}) (sm : X ⟶ Spec (CommRingCat.of R))
    (N : X.Opens) (hN : IsAffineOpen N) (m : ℕ) (r : Fin m → Γ(X, N))
    (hgen : ∀ g : Γ(X, N), ∃ P Q : MvPolynomial (Fin m) R,
      IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r Q) ∧
        g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r P)
    (a b : W ⟶ X) (hab : a ≫ sm = b ≫ sm) (ha : ⊤ ≤ a ⁻¹ᵁ N) (hb : ⊤ ≤ b ⁻¹ᵁ N)
    (hr : ∀ l, (W.presheaf.map (homOfLE ha).op).hom ((a.app N).hom (r l)) =
      (W.presheaf.map (homOfLE hb).op).hom ((b.app N).hom (r l))) : a = b := by

  have hφ : ∀ g : Γ(X, N), (W.presheaf.map (homOfLE ha).op).hom ((a.app N).hom g) =
      (W.presheaf.map (homOfLE hb).op).hom ((b.app N).hom g) := by
    let φa : Γ(X, N) →+* Γ(W, ⊤) := (W.presheaf.map (homOfLE ha).op).hom.comp (a.app N).hom
    let φb : Γ(X, N) →+* Γ(W, ⊤) := (W.presheaf.map (homOfLE hb).op).hom.comp (b.app N).hom
    have hc : φa.comp (GlobalTheory.AbLaw.cst sm N) = φb.comp (GlobalTheory.AbLaw.cst sm N) := by
      ext x
      simp only [RingHom.comp_apply, φa, φb]
      rw [cst_pull sm N a ha, cst_pull sm N b hb, hab]
    have hrr : (⇑φa ∘ r) = (⇑φb ∘ r) := funext hr
    have hev : ∀ P : MvPolynomial (Fin m) R, φa (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r P) =
        φb (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r P) := by
      intro P
      rw [MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left, hc, hrr]
    intro g
    obtain ⟨P, Q, hQ, hg⟩ := hgen g
    have h1 := congrArg φa hg
    have h2 := congrArg φb hg
    rw [map_mul] at h1 h2
    have hu : IsUnit (φa (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r Q)) := hQ.map φa
    change φa g = φb g
    refine hu.mul_left_injective ?_
    simp only
    rw [h1, hev P, ← h2, ← hev Q]
  haveI : IsAffine N := hN
  have hra : Set.range a ⊆ Set.range N.ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨w, rfl⟩; exact ha trivial
  have hrb : Set.range b ⊆ Set.range N.ι := by
    rw [Scheme.Opens.range_ι]; rintro _ ⟨w, rfl⟩; exact hb trivial
  obtain ⟨a', rfl⟩ : ∃ a', a' ≫ N.ι = a := ⟨_, IsOpenImmersion.lift_fac N.ι a hra⟩
  obtain ⟨b', rfl⟩ : ∃ b', b' ≫ N.ι = b := ⟨_, IsOpenImmersion.lift_fac N.ι b hrb⟩
  refine congrArg (· ≫ N.ι) (ext_of_isAffine ?_)
  ext x
  have ea := congrArg (fun f => f.hom (N.topIso.hom.hom x)) (app_restrict_eq X W N a' ha)
  have eb := congrArg (fun f => f.hom (N.topIso.hom.hom x)) (app_restrict_eq X W N b' hb)
  have key := ea.symm.trans ((hφ _).trans eb)
  simp only [CommRingCat.comp_apply, Iso.hom_inv_id_apply] at key
  exact key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfAgreeOnAffineOpenGeneratorsStatement
open AlgebraicGeometry CategoryTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_agree_on_affineOpen_generators : ∀ (R : Type) [CommRing R] (X W : Scheme.{0}) (sm : X ⟶ Spec (CommRingCat.of R)) (N : X.Opens), IsAffineOpen N → ∀ (m : ℕ) (r : Fin m → Γ(X, N)), (∀ g : Γ(X, N), ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r Q) ∧ g * MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r Q = MvPolynomial.eval₂ (GlobalTheory.AbLaw.cst sm N) r P) → ∀ (a b : W ⟶ X), a ≫ sm = b ≫ sm → ∀ (ha : ⊤ ≤ a ⁻¹ᵁ N) (hb : ⊤ ≤ b ⁻¹ᵁ N), (∀ l, (W.presheaf.map (homOfLE ha).op).hom ((a.app N).hom (r l)) = (W.presheaf.map (homOfLE hb).op).hom ((b.app N).hom (r l))) → a = b := by
  first | exact @GlobalTheory.eq_of_agree_on_generators | exact GlobalTheory.eq_of_agree_on_generators | (intros; apply GlobalTheory.eq_of_agree_on_generators <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizedPresentationEvalQuotientFraction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizedPresentationEvalQuotientFraction
namespace GlobalTheory

open MvPolynomial

theorem exists_eval₂_fraction_of_exists_mod_nilpotent : ∀ (R B : Type) [CommRing R] [CommRing B] (c : R →+* B) (J : Ideal R) (n : ℕ), (∀ x ∈ J ^ n, c x = 0) → ∀ (m : ℕ) (r : Fin m → B), (∀ g : B, ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ c r Q) ∧ g * MvPolynomial.eval₂ c r Q - MvPolynomial.eval₂ c r P ∈ Ideal.map c J) → ∀ g : B, ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ c r Q) ∧ g * MvPolynomial.eval₂ c r Q = MvPolynomial.eval₂ c r P := by
  intro R B _ _ c J n hn m r hgen
  let S : Subring B :=
    { carrier := {g | ∃ P Q : MvPolynomial (Fin m) R, IsUnit (eval₂ c r Q) ∧ g * eval₂ c r Q = eval₂ c r P}
      mul_mem' := by
        rintro a b ⟨P₁, Q₁, hQ₁, h₁⟩ ⟨P₂, Q₂, hQ₂, h₂⟩
        refine ⟨P₁ * P₂, Q₁ * Q₂, ?_, ?_⟩
        · rw [eval₂_mul]; exact hQ₁.mul hQ₂
        · rw [eval₂_mul, eval₂_mul, ← h₁, ← h₂]; ring
      one_mem' := ⟨1, 1, by simp, by simp⟩
      add_mem' := by
        rintro a b ⟨P₁, Q₁, hQ₁, h₁⟩ ⟨P₂, Q₂, hQ₂, h₂⟩
        refine ⟨P₁ * Q₂ + P₂ * Q₁, Q₁ * Q₂, ?_, ?_⟩
        · rw [eval₂_mul]; exact hQ₁.mul hQ₂
        · rw [eval₂_add, eval₂_mul, eval₂_mul, eval₂_mul, ← h₁, ← h₂]; ring
      zero_mem' := ⟨0, 1, by simp, by simp⟩
      neg_mem' := by
        rintro a ⟨P, Q, hQ, h⟩
        refine ⟨-P, Q, hQ, ?_⟩
        rw [eval₂_neg, ← h]; ring }
  have hS : ∀ g, g ∈ S ↔ ∃ P Q : MvPolynomial (Fin m) R,
      IsUnit (eval₂ c r Q) ∧ g * eval₂ c r Q = eval₂ c r P := fun g => Iff.rfl
  have hcS : ∀ a : R, c a ∈ S := fun a => (hS _).2 ⟨C a, 1, by simp, by simp⟩
  set I := Ideal.map c J with hI
  have hdec : ∀ b : B, ∃ s ∈ S, b - s ∈ I := by
    intro b
    obtain ⟨P, Q, hQ, hb⟩ := hgen b
    obtain ⟨u, hu⟩ := hQ
    refine ⟨eval₂ c r P * ↑u⁻¹, (hS _).2 ⟨P, Q, ⟨u, hu⟩, ?_⟩, ?_⟩
    · rw [← hu, mul_assoc, Units.inv_mul, mul_one]
    · have h1 : (↑u⁻¹ : B) * ↑u = 1 := Units.inv_mul u
      have : b - eval₂ c r P * ↑u⁻¹ = ↑u⁻¹ * (b * eval₂ c r Q - eval₂ c r P) := by
        rw [← hu]; linear_combination (-b) * h1
      rw [this]; exact I.mul_mem_left _ hb
  have hstep : ∀ k : ℕ, ∀ x ∈ I ^ k, ∃ s ∈ S, x - s ∈ I ^ (k + 1) := by
    intro k x hx
    have hIk : I ^ k = Ideal.span (c '' ↑(J ^ k)) := by rw [hI, ← Ideal.map_pow]; rfl
    rw [hIk] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, -, rfl⟩ := hy
      exact ⟨c j, hcS j, by simp⟩
    | zero => exact ⟨0, S.zero_mem, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨s, hs, hys⟩ := hy
      obtain ⟨t, ht, hzt⟩ := hz
      refine ⟨s + t, S.add_mem hs ht, ?_⟩
      have := Ideal.add_mem _ hys hzt
      convert this using 1; ring
    | smul b y hy ih =>
      obtain ⟨s, hs, hys⟩ := ih
      obtain ⟨t, ht, hbt⟩ := hdec b
      refine ⟨t * s, S.mul_mem ht hs, ?_⟩
      have hy' : y ∈ I ^ k := hIk ▸ hy
      have h1 : (b - t) * y ∈ I ^ (k + 1) := by
        rw [pow_succ']; exact Ideal.mul_mem_mul hbt hy'
      have h2 : t * (y - s) ∈ I ^ (k + 1) := Ideal.mul_mem_left _ _ hys
      have := Ideal.add_mem _ h1 h2
      rw [smul_eq_mul]
      convert this using 1; ring
  have hall : ∀ k : ℕ, ∀ g : B, ∃ s ∈ S, g - s ∈ I ^ k := by
    intro k
    induction k with
    | zero => intro g; exact ⟨0, S.zero_mem, by simp⟩
    | succ k ih =>
      intro g
      obtain ⟨s, hs, hgs⟩ := ih g
      obtain ⟨t, ht, hxt⟩ := hstep k _ hgs
      refine ⟨s + t, S.add_mem hs ht, ?_⟩
      convert hxt using 1; ring
  have hIn : I ^ n = ⊥ := by
    rw [hI, ← Ideal.map_pow, Ideal.map_eq_bot_iff_le_ker]
    intro x hx
    rw [RingHom.mem_ker]
    exact hn x hx
  intro g
  obtain ⟨s, hs, hgs⟩ := hall n g
  rw [hIn, Ideal.mem_bot, sub_eq_zero] at hgs
  exact (hS g).1 (hgs ▸ hs)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizedPresentationEvalQuotientFractionStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localized_presentation_eval_quotient_fraction : ∀ (R B : Type) [CommRing R] [CommRing B] (c : R →+* B) (J : Ideal R) (n : ℕ), (∀ x ∈ J ^ n, c x = 0) → ∀ (m : ℕ) (r : Fin m → B), (∀ g : B, ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ c r Q) ∧ g * MvPolynomial.eval₂ c r Q - MvPolynomial.eval₂ c r P ∈ Ideal.map c J) → ∀ g : B, ∃ P Q : MvPolynomial (Fin m) R, IsUnit (MvPolynomial.eval₂ c r Q) ∧ g * MvPolynomial.eval₂ c r Q = MvPolynomial.eval₂ c r P := by
  first | exact @GlobalTheory.exists_eval₂_fraction_of_exists_mod_nilpotent | exact GlobalTheory.exists_eval₂_fraction_of_exists_mod_nilpotent | (intros; apply GlobalTheory.exists_eval₂_fraction_of_exists_mod_nilpotent <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSectionRatioEqNearThickeningPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem eq_of_secRatioEq_near : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (s₀ : H0 U.LG.L k) (i : Fin 1 → U.LG.L.ι) (w : (thickObj R (maximalIdeal R) e G).left), (fstG (maximalIdeal R) e G).left w ∈ secChart U.LG.L i → IsUnit (secGerm (fstG (maximalIdeal R) e G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) e G).left.Opens) (m : ℕ) (σ : Fin m → H0 U.LG.L k), w ∈ N ∧ ∀ (W : Scheme.{0}) (a b : W ⟶ (thickObj R (maximalIdeal R) e G).left), a ≫ (thickObj R (maximalIdeal R) e G).hom = b ≫ (thickObj R (maximalIdeal R) e G).hom → (∀ x, a x ∈ N) → (∀ x, b x ∈ N) → (∀ l, SecRatioEq U.LG.L (a ≫ (fstG (maximalIdeal R) e G).left) (b ≫ (fstG (maximalIdeal R) e G).left) (σ l) s₀ (σ l) s₀) → a = b := by
  intro R _ _ _ hB D A G _ _ hG U
  obtain ⟨k₀, hk₀, H⟩ := GlobalTheory.T.exists_section_ratios_generate_mod_maximal R hB D A G hG U
  refine ⟨k₀, hk₀, fun e k hk s₀ i w hw hu => ?_⟩
  obtain ⟨N, m, σ, r, hwN, hNaff, hNi, hgerm, hgen⟩ := H e k hk s₀ i w hw hu
  have hw' : (fstG (maximalIdeal R) e G).left ≫ G.hom = (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e :=
    (fstG (maximalIdeal R) e G).w
  have hz : ∀ x ∈ maximalIdeal R ^ (e + 1), (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) x = 0 := by
    intro x hx
    have h0 : (thick R (maximalIdeal R) e).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom x) = 0 := by
      have := congrArg (fun φ => φ.hom x)
        (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))))
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
      rw [← this, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
    simp only [GlobalTheory.AbLaw.cst, RingHom.comp_apply, hw', Scheme.Hom.comp_appTop, CommRingCat.hom_comp, h0, map_zero]
  have hgen' := GlobalTheory.T.localized_presentation_eval_quotient_fraction R _ (GlobalTheory.AbLaw.cst (X := (thickObj R (maximalIdeal R) e G).left) ((fstG (maximalIdeal R) e G).left ≫ G.hom) N) (maximalIdeal R) (e + 1) hz m r hgen
  refine ⟨N, m, σ, hwN, fun W a b hab ha hb hrat => ?_⟩
  have ha' : ⊤ ≤ a ⁻¹ᵁ N := fun x _ => ha x
  have hb' : ⊤ ≤ b ⁻¹ᵁ N := fun x _ => hb x
  have hst : ∀ (c : W ⟶ (thickObj R (maximalIdeal R) e G).left) (x : W) (f : Γ((thickObj R (maximalIdeal R) e G).left, N)), c x ∈ N →
      (c.stalkMap x).hom (gs (𝟙 _) (c x) N f) = gs c x N f := by
    intro c x f h
    have e1 : gs (c ≫ 𝟙 _) x N f = (c.stalkMap x).hom (gs (𝟙 _) (c x) N f) := by
      rw [gs_eq (𝟙 _) (c x) _ h, ← gs_pull c (𝟙 _) x _ h, gs_eq c x _ (show c x ∈ (𝟙 (thickObj R (maximalIdeal R) e G).left : (thickObj R (maximalIdeal R) e G).left ⟶ (thickObj R (maximalIdeal R) e G).left) ⁻¹ᵁ N from h)]
      exact (Scheme.Hom.germ_stalkMap_apply c _ x h _).symm
    rw [← e1, Category.comp_id]
  have hsg : ∀ (c : W ⟶ (thickObj R (maximalIdeal R) e G).left) (x : W) (s : H0 U.LG.L k), c x ∈ N →
      secGerm (c ≫ (fstG (maximalIdeal R) e G).left) x s i = (c.stalkMap x).hom (secGerm (fstG (maximalIdeal R) e G).left (c x) s i) :=
    fun c x s h => secGerm_comp c _ x s (hNi h)
  refine GlobalTheory.T.eq_of_agree_on_affineOpen_generators R _ W ((fstG (maximalIdeal R) e G).left ≫ G.hom) N hNaff m r hgen' a b ?_ ha' hb' ?_
  · rw [hw', ← Category.assoc, hab, Category.assoc]
  · intro l
    apply fn_ext
    intro x _
    rw [gs_res _ _ _ (show (𝟙 W : W ⟶ W) x ∈ (⊤ : W.Opens) from trivial),
      gs_res _ _ _ (show (𝟙 W : W ⟶ W) x ∈ (⊤ : W.Opens) from trivial),
      gs_pull (𝟙 W) a x N (ha x), gs_pull (𝟙 W) b x N (hb x), Category.id_comp, Category.id_comp]
    have key := secRatioEq_iff_germ.1 (hrat l) x i i (hNi (ha x)) (hNi (hb x))
    rw [hsg a x _ (ha x), hsg a x _ (ha x), hsg b x _ (hb x), hsg b x _ (hb x),
      (hgerm _ (ha x)).2 l, (hgerm _ (hb x)).2 l, map_mul, map_mul, hst a x _ (ha x), hst b x _ (hb x)] at key
    have hA := ((hgerm _ (ha x)).1).map (a.stalkMap x).hom
    have hB := ((hgerm _ (hb x)).1).map (b.stalkMap x).hom
    refine (hA.mul hB).mul_left_inj.1 ?_
    linear_combination key

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfSectionRatioEqNearThickeningPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_sectionRatio_eq_near_thickening_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (s₀ : H0 U.LG.L k) (i : Fin 1 → U.LG.L.ι) (w : (thickObj R (maximalIdeal R) e G).left), (fstG (maximalIdeal R) e G).left w ∈ secChart U.LG.L i → IsUnit (secGerm (fstG (maximalIdeal R) e G).left w s₀ i) → ∃ (N : (thickObj R (maximalIdeal R) e G).left.Opens) (m : ℕ) (σ : Fin m → H0 U.LG.L k), w ∈ N ∧ ∀ (W : Scheme.{0}) (a b : W ⟶ (thickObj R (maximalIdeal R) e G).left), a ≫ (thickObj R (maximalIdeal R) e G).hom = b ≫ (thickObj R (maximalIdeal R) e G).hom → (∀ x, a x ∈ N) → (∀ x, b x ∈ N) → (∀ l, SecRatioEq U.LG.L (a ≫ (fstG (maximalIdeal R) e G).left) (b ≫ (fstG (maximalIdeal R) e G).left) (σ l) s₀ (σ l) s₀) → a = b := by
  exact @GlobalTheory.Mum.eq_of_secRatioEq_near
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupMorphismsAgreeNearPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.LocAgree

theorem gs_prod {X Y : Scheme.{0}} {L : LB X} {k : ℕ} (u v : Y ⟶ X) (i i' : Fin 1 → L.ι) (y : Y)
    (hi : u y ∈ secChart L i) (hi' : v y ∈ secChart L i') (s t : H0 L k) :
    gs (𝟙 Y) y (u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i')
        ((Y.presheaf.map (homOfLE (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i)).op).hom
          ((u.app (secChart L i)).hom (s.f i)) *
        (Y.presheaf.map (homOfLE (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i')).op).hom
          ((v.app (secChart L i')).hom (t.f i'))) = secGerm u y s i * secGerm v y t i' := by
  have hy : (𝟙 Y : Y ⟶ Y) y ∈ u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' := ⟨hi, hi'⟩
  rw [gs_mul _ _ _ hy, gs_res _ _ _ hy, gs_res _ _ _ hy]
  exact congrArg₂ (· * ·) (gs_pull (𝟙 Y) u y _ hi _) (gs_pull (𝟙 Y) v y _ hi' _)

theorem gs_nbhd {Z : Scheme.{0}} {O : Z.Opens} (a b : Γ(Z, O)) (z : Z) (hz : z ∈ O)
    (h : gs (𝟙 Z) z O a = gs (𝟙 Z) z O b) :
    ∃ V : Z.Opens, z ∈ V ∧ V ≤ O ∧ ∀ x ∈ V, gs (𝟙 Z) x O a = gs (𝟙 Z) x O b := by
  rw [gs_eq _ z O hz, gs_eq _ z O hz] at h
  obtain ⟨V, hzV, iU, iV, e⟩ := TopCat.Presheaf.germ_eq Z.presheaf z hz hz _ _ h
  refine ⟨V, hzV, leOfHom iU, fun x hx => ?_⟩
  have hxO : (𝟙 Z : Z ⟶ Z) x ∈ O := leOfHom iU hx
  rw [gs_eq _ x O hxO, gs_eq _ x O hxO]
  exact (TopCat.Presheaf.germ_res_apply Z.presheaf iU x hx _).symm.trans
    ((congrArg (Z.presheaf.germ V x hx).hom e).trans (TopCat.Presheaf.germ_res_apply Z.presheaf iV x hx _))

end GlobalTheory.Mum.LocAgree

namespace GlobalTheory.Mum.LocAgree

theorem locAgree : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (Z : Scheme.{0}) (u u' : Z ⟶ (thickObj R (maximalIdeal R) e G).left), u ≫ (thickObj R (maximalIdeal R) e G).hom = u' ≫ (thickObj R (maximalIdeal R) e G).hom → ∀ (s₀ : H0 U.LG.L k) (i i'' : Fin 1 → U.LG.L.ι) (z : Z), GermRatioAgree (u ≫ (fstG (maximalIdeal R) e G).left) (u' ≫ (fstG (maximalIdeal R) e G).left) s₀ i i'' z → u z = u' z → ∃ W : Z.Opens, z ∈ W ∧ W.ι ≫ u = W.ι ≫ u' := by
  intro R _ _ _ hB D A G _ _ hG U
  obtain ⟨k₀, hk₀, hK⟩ := GlobalTheory.T.eq_of_sectionRatio_eq_near_thickening_point R hB D A G hG U
  refine ⟨k₀, hk₀, fun e k hk Z u u' hu s₀ i i'' z hg hz => ?_⟩
  obtain ⟨hi, hi'', hunit, hunit', hall⟩ := hg
  set p := (fstG (maximalIdeal R) e G).left with hp
  have hiw : p (u z) ∈ secChart U.LG.L i := hi
  have hunitw : IsUnit (secGerm p (u z) s₀ i) := by
    rw [secGerm_comp u p z s₀ hiw] at hunit
    exact (isUnit_map_iff (u.stalkMap z).hom _).1 hunit
  obtain ⟨N, m, σ, hwN, hmono⟩ := hK e k hk s₀ i (u z) hiw hunitw

  have hz' : z ∈ (u ≫ p) ⁻¹ᵁ secChart U.LG.L i ⊓ (u' ≫ p) ⁻¹ᵁ secChart U.LG.L i'' := ⟨hi, hi''⟩
  have hV : ∀ l, ∃ V : Z.Opens, z ∈ V ∧ V ≤ (u ≫ p) ⁻¹ᵁ secChart U.LG.L i ⊓ (u' ≫ p) ⁻¹ᵁ secChart U.LG.L i'' ∧
      ∀ x ∈ V, secGerm (u ≫ p) x (σ l) i * secGerm (u' ≫ p) x s₀ i'' =
        secGerm (u ≫ p) x s₀ i * secGerm (u' ≫ p) x (σ l) i'' := by
    intro l
    obtain ⟨V, hzV, hVO, hx⟩ := gs_nbhd _ _ z hz'
      ((gs_prod (u ≫ p) (u' ≫ p) i i'' z hi hi'' (σ l) s₀).trans ((hall (σ l)).trans
        (gs_prod (u ≫ p) (u' ≫ p) i i'' z hi hi'' s₀ (σ l)).symm))
    refine ⟨V, hzV, hVO, fun x hxV => ?_⟩
    have hxO := hVO hxV
    rw [← gs_prod (u ≫ p) (u' ≫ p) i i'' x hxO.1 hxO.2, ← gs_prod (u ≫ p) (u' ≫ p) i i'' x hxO.1 hxO.2]
    exact hx x hxV
  choose V hzV hVO hVx using hV
  let W : Z.Opens := ⟨(⋂ l, (V l : Set Z)) ∩ ((u ≫ p) ⁻¹ᵁ secChart U.LG.L i ⊓ (u' ≫ p) ⁻¹ᵁ secChart U.LG.L i'' : Z.Opens)
      ∩ (u ⁻¹ᵁ N : Set Z) ∩ (u' ⁻¹ᵁ N : Set Z),
    (((isOpen_iInter_of_finite fun l => (V l).isOpen).inter (TopologicalSpace.Opens.isOpen _)).inter (TopologicalSpace.Opens.isOpen _)).inter
      (TopologicalSpace.Opens.isOpen _)⟩
  have hzW : z ∈ W := ⟨⟨⟨Set.mem_iInter.2 hzV, hz'⟩, hwN⟩, show u' z ∈ N from hz ▸ hwN⟩
  refine ⟨W, hzW, ?_⟩
  have hmem : ∀ x : W.toScheme, W.ι x ∈ W := fun x => by
    have h : W.ι x ∈ Set.range W.ι := ⟨x, rfl⟩
    rwa [Scheme.Opens.range_ι] at h
  apply hmono W.toScheme (W.ι ≫ u) (W.ι ≫ u')
  · simp only [Category.assoc, hu]
  · intro x; exact (hmem x).1.2
  · intro x; exact (hmem x).2
  · intro l
    refine secRatioEq_of_exists_germ fun x => ⟨i, i'', (hmem x).1.1.2.1, (hmem x).1.1.2.2, ?_⟩
    simp only [Category.assoc]
    rw [secGerm_comp W.ι (u ≫ p) x _ (hmem x).1.1.2.1, secGerm_comp W.ι (u ≫ p) x _ (hmem x).1.1.2.1,
      secGerm_comp W.ι (u' ≫ p) x _ (hmem x).1.1.2.2, secGerm_comp W.ι (u' ≫ p) x _ (hmem x).1.1.2.2,
      ← map_mul, ← map_mul, hVx l _ (Set.mem_iInter.1 (hmem x).1.1.1 l)]

end GlobalTheory.Mum.LocAgree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupMorphismsAgreeNearPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroup_morphisms_agree_near_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (Z : Scheme.{0}) (u u' : Z ⟶ (thickObj R (maximalIdeal R) e G).left), u ≫ (thickObj R (maximalIdeal R) e G).hom = u' ≫ (thickObj R (maximalIdeal R) e G).hom → ∀ (s₀ : H0 U.LG.L k) (i i'' : Fin 1 → U.LG.L.ι) (z : Z), GermRatioAgree (u ≫ (fstG (maximalIdeal R) e G).left) (u' ≫ (fstG (maximalIdeal R) e G).left) s₀ i i'' z → u z = u' z → ∃ W : Z.Opens, z ∈ W ∧ W.ι ≫ u = W.ι ≫ u' := by
  first | exact @GlobalTheory.Mum.LocAgree.locAgree | exact GlobalTheory.Mum.LocAgree.locAgree | (intros; apply GlobalTheory.Mum.LocAgree.locAgree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningMorphismsAgreeBeyondThreshold
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaImmersionPointsAgreeNearOfEqualRatios
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaImmersionPointsAgreeNearOfEqualRatios
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ThetaSep

open GlobalTheory.ProjSpace

variable {X H Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem sval_eq_secRatio_mul {φ : K → (H ⟶ X)} {ε : K → ℤ} (a b : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ H) (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (ha : r z ∈ nonzeroLocus a) :
    sval b r z J = gs r z (nonzeroLocus a) (secRatio a b) * sval a r z J := by
  have hc := hJ.mem φ r
  have hm : r z ∈ nonzeroLocus a ⊓ (LB.LinComb L φ ε).U (fun k => J (r ≫ φ k)) := ⟨ha, hc⟩
  have e := congrArg (gs r z _) (secRatio_spec a b (fun k => J (r ≫ φ k)))
  rw [gs_mul r z _ hm, gs_res r z _ hm, gs_res r z _ hm, gs_res r z _ hm] at e
  exact e

theorem pullRatio_ι_comp {R : Type} [CommRing R] {M : ℕ} (P : H ⟶ PSpace R M) {U : H.Opens} {i : Fin (M + 1)}
    (hi : U ≤ P ⁻¹ᵁ chart R M i) (r : Z ⟶ H) (W : Z.Opens) (hW : W ≤ r ⁻¹ᵁ U)
    (h : ⊤ ≤ (W.ι ≫ r ≫ P) ⁻¹ᵁ chart R M i) (j : Fin (M + 1)) :
    pullRatio (W.ι ≫ r ≫ P) ⊤ i h j =
      (W.ι.appLE (r ⁻¹ᵁ U) ⊤ (W.ι_preimage_self.ge.trans (W.ι.preimage_mono hW))).hom
        ((r.app U).hom (pullRatio P U i hi j)) := by
  have hW' : ⊤ ≤ W.ι ⁻¹ᵁ (r ⁻¹ᵁ U) := W.ι_preimage_self.ge.trans (W.ι.preimage_mono hW)
  rw [pullRatio_of_eq (Category.assoc W.ι r P).symm h ((hW'.trans ((W.ι ≫ r).preimage_mono hi))),
    ← appLE_pullRatio (W.ι ≫ r) hW', Scheme.Hom.app_eq_appLE, appLE_appLE]

end GlobalTheory.Mum.ThetaSep

namespace GlobalTheory.Mum.ThetaSep

open GlobalTheory.ProjSpace

theorem agree_near_of_minors : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) (k N : ℕ)
    (τ : Fin (N + 1) → SecK D.P.L Y.q.left k) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤),
    IsImmersion (GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) → ∀ (T : Over (Sp R)) (y y' : T ⟶ Y.H) (z : T.left)
    (J : (T.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
    (∀ j l : Fin (N + 1), sval (τ j) y.left z J * sval (τ l) y'.left z J =
      sval (τ l) y.left z J * sval (τ j) y'.left z J) →
    ∃ W : T.left.Opens, z ∈ W ∧ W.ι ≫ y.left = W.ι ≫ y'.left := by
  intro R _ _ D Y k N τ hτ hImm T y y' z J hJ hrel
  have hmono : Mono (GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) := inferInstance
  obtain ⟨j₀, hj₀⟩ := TopologicalSpace.Opens.mem_iSup.1 (hτ.ge (Set.mem_univ (y.left z)))
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hτ.ge (Set.mem_univ (y'.left z)))
  have ua : IsUnit (sval (τ j₀) y.left z J) := (GlobalTheory.MulPullSec.mem_nonzeroLocus_iff _ _ _ hJ).1 hj₀
  have ubi : IsUnit (sval (τ i) y'.left z J) := (GlobalTheory.MulPullSec.mem_nonzeroLocus_iff _ _ _ hJ).1 hi
  have ub : IsUnit (sval (τ j₀) y'.left z J) := by
    have h := hrel j₀ i
    have : IsUnit (sval (τ i) y.left z J * sval (τ j₀) y'.left z J) := h ▸ ua.mul ubi
    exact isUnit_of_mul_isUnit_right this
  have hj₀' : y'.left z ∈ nonzeroLocus (τ j₀) := (GlobalTheory.MulPullSec.mem_nonzeroLocus_iff _ _ _ hJ).2 ub
  have hg : ∀ j, gs y.left z (nonzeroLocus (τ j₀)) (secRatio (τ j₀) (τ j)) =
      gs y'.left z (nonzeroLocus (τ j₀)) (secRatio (τ j₀) (τ j)) := by
    intro j
    have h := hrel j₀ j
    rw [sval_eq_secRatio_mul (τ j₀) (τ j) y.left z hJ hj₀,
      sval_eq_secRatio_mul (τ j₀) (τ j) y'.left z hJ hj₀'] at h
    refine ((ua.mul ub).mul_right_cancel ?_).symm
    calc _ = sval (τ j₀) y.left z J * (gs y'.left z (nonzeroLocus (τ j₀)) (secRatio (τ j₀) (τ j)) *
          sval (τ j₀) y'.left z J) := by ring
      _ = _ := by rw [h]; ring
  have hW : ∀ j, ∃ W : T.left.Opens, z ∈ W ∧ ∃ (h₁ : W ≤ y.left ⁻¹ᵁ nonzeroLocus (τ j₀))
      (h₂ : W ≤ y'.left ⁻¹ᵁ nonzeroLocus (τ j₀)),
      resG T.left h₁ ((y.left.app _).hom (secRatio (τ j₀) (τ j))) =
        resG T.left h₂ ((y'.left.app _).hom (secRatio (τ j₀) (τ j))) := by
    intro j
    have e := hg j
    rw [gs_eq _ z _ hj₀, gs_eq _ z _ hj₀'] at e
    obtain ⟨W, hzW, iU, iV, e'⟩ := TopCat.Presheaf.germ_eq T.left.presheaf z hj₀ hj₀' _ _ e
    exact ⟨W, hzW, leOfHom iU, leOfHom iV, e'⟩
  choose Wj hzWj h₁ h₂ heq using hW
  let W : T.left.Opens := Finset.univ.inf Wj
  have hzW : z ∈ W := Finset.inf_induction (p := fun U : T.left.Opens => z ∈ U) trivial
    (fun _ h _ h' => ⟨h, h'⟩) (fun j _ => hzWj j)
  have hWle : ∀ j, W ≤ Wj j := fun j => Finset.inf_le (Finset.mem_univ j)
  refine ⟨W, hzW, (cancel_mono (GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ)).1 ?_⟩
  have hpre := toProj_preimage_chart Y.H.hom τ hτ j₀
  have hA : ∀ (r : T.left ⟶ Y.H.left), W ≤ r ⁻¹ᵁ nonzeroLocus (τ j₀) →
      ⊤ ≤ (W.ι ≫ r ≫ GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) ⁻¹ᵁ chart R N j₀ := fun r hr =>
    (W.ι_preimage_self.ge.trans (W.ι.preimage_mono hr)).trans
      ((W.ι ≫ r).preimage_mono hpre.ge)
  have hy₁ : W ≤ y.left ⁻¹ᵁ nonzeroLocus (τ j₀) := (hWle j₀).trans (h₁ j₀)
  have hy₂ : W ≤ y'.left ⁻¹ᵁ nonzeroLocus (τ j₀) := (hWle j₀).trans (h₂ j₀)
  simp only [Category.assoc]
  refine hom_ext ?_ fun _ => ⟨⊤, trivial, j₀, hA _ hy₁, hA _ hy₂, fun j => ?_⟩
  · simp only [Category.assoc, toProj_str]
    rw [Over.w y, Over.w y']
  · rw [pullRatio_ι_comp _ hpre.ge _ W hy₁, pullRatio_ι_comp _ hpre.ge _ W hy₂, pullRatio_toProj]
    have hW₁ : ⊤ ≤ W.ι ⁻¹ᵁ Wj j := W.ι_preimage_self.ge.trans (W.ι.preimage_mono (hWle j))
    rw [← appLE_resG W.ι (h₁ j) hW₁, ← appLE_resG W.ι (h₂ j) hW₁, heq j]

end GlobalTheory.Mum.ThetaSep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaImmersionPointsAgreeNearOfEqualRatiosStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaImmersion_points_agree_near_of_equal_ratios : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (Y : Ext D) (k N : ℕ) (τ : Fin (N + 1) → SecK D.P.L Y.q.left k) (hτ : ⨆ i, nonzeroLocus (τ i) = ⊤), IsImmersion (GlobalTheory.ProjSpace.toProj Y.H.hom τ hτ) → ∀ (T : Over (Sp R)) (y y' : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J → (∀ j l : Fin (N + 1), sval (τ j) y.left z J * sval (τ l) y'.left z J = sval (τ l) y.left z J * sval (τ j) y'.left z J) → ∃ W : T.left.Opens, z ∈ W ∧ W.ι ≫ y.left = W.ι ≫ y'.left := by
  first | exact @GlobalTheory.Mum.ThetaSep.agree_near_of_minors | exact GlobalTheory.Mum.ThetaSep.agree_near_of_minors | (intros; apply GlobalTheory.Mum.ThetaSep.agree_near_of_minors <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningMorphismsAgreeBeyondThreshold
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_closedFibre_factor : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) (e : ℕ) (K : Type) [Field K] (a : Spec (CommRingCat.of K) ⟶ (thickObj R (maximalIdeal R) e G).left), ∃ g : Spec (CommRingCat.of K) ⟶ (thickObj R (maximalIdeal R) 0 G).left, g ≫ (fstG (maximalIdeal R) 0 G).left = a ≫ (fstG (maximalIdeal R) e G).left ∧ g ≫ (thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0 = a ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e := by
  intro R _ _ _ G e K _ a
  let f := a ≫ (thickObj R (maximalIdeal R) e G).hom
  let φ := Spec.preimage f
  have hφ : Spec.map φ = f := Spec.map_preimage f
  have hker : ∀ r ∈ maximalIdeal R ^ (0 + 1),
      (φ.hom.comp (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))) r = 0 := by
    intro r hr
    rw [zero_add, pow_one] at hr
    have h1 : r ^ (e + 1) ∈ maximalIdeal R ^ (e + 1) := Ideal.pow_mem_pow hr _
    have h2 : (φ.hom.comp (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))) r ^ (e + 1) = 0 := by
      rw [← map_pow, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 h1, map_zero]
    exact pow_eq_zero_iff (Nat.succ_ne_zero e) |>.1 h2
  let ψ : R ⧸ maximalIdeal R ^ (0 + 1) →+* K := Ideal.Quotient.lift _ _ hker
  have hψ : (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (0 + 1)))) ≫ CommRingCat.ofHom ψ =
      CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1))) ≫ φ := by
    ext r
    exact Ideal.Quotient.lift_mk (maximalIdeal R ^ (0 + 1)) (φ.hom.comp (Ideal.Quotient.mk (maximalIdeal R ^ (e + 1)))) hker
  have hc : (a ≫ pullback.fst G.hom (thick R (maximalIdeal R) e)) ≫ G.hom =
      Spec.map (CommRingCat.ofHom ψ) ≫ thick R (maximalIdeal R) 0 := by
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change f ≫ _ = _
    rw [← hφ, thick, thick, ← Spec.map_comp, ← Spec.map_comp, hψ]
  refine ⟨pullback.lift _ _ hc, pullback.lift_fst _ _ _, ?_⟩
  change pullback.lift _ _ hc ≫ pullback.snd _ _ ≫ _ = a ≫ pullback.snd _ _ ≫ _
  rw [pullback.lift_snd_assoc, ← hc, Category.assoc, pullback.condition]

theorem eq_of_germRatioAgree : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (Z : Scheme.{0}) (u u' : Z ⟶ (thickObj R (maximalIdeal R) e G).left), u ≫ (thickObj R (maximalIdeal R) e G).hom = u' ≫ (thickObj R (maximalIdeal R) e G).hom → ∀ (s₀ : H0 U.LG.L k) (i i'' : Fin 1 → U.LG.L.ι) (z : Z), GermRatioAgree (u ≫ (fstG (maximalIdeal R) e G).left) (u' ≫ (fstG (maximalIdeal R) e G).left) s₀ i i'' z → u z = u' z := by
  intro R _ _ _ hB D A G _ _ hG U
  obtain ⟨Y⟩ : Nonempty (Ext D.toPre) := inferInstance
  obtain ⟨S, k₁, hk₁⟩ := GlobalTheory.T.exists_theta_immersion_torus_extension_projective R hB D Y
  choose k₀f hk₀f using (GlobalTheory.T.exists_integralThetaFamily_prescribed_leadingTerm R hB D).1
  refine ⟨max 3 (max k₁ (S.sup k₀f)), le_max_left _ _, ?_⟩
  intro e k hk Z u u' hu s₀ i i'' z h
  have hk3 : 3 ≤ k := le_trans (le_max_left _ _) hk
  have hkk₁ : k₁ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hkS : S.sup k₀f ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  obtain ⟨N, α, b, τ, hτ, hαb, himm⟩ := hk₁ k hkk₁
  have hF : ∀ j, ∃ F : IntFam (maximalIdeal R) D.toPre k, F.Lead (α j) (b j) := fun j =>
    hk₀f (α j) k (le_trans (Finset.le_sup (hαb j).1) hkS) (b j)
  choose F hF using hF
  have hs : ∀ j, ∃ σ : H0 U.LG.L k, ∀ e, U.ExpandsAt e k σ (F j).f := fun j =>
    IntFam.exists_expandsAt R hB D A G U hG k (by omega) (F j)
  choose s hs using hs
  obtain ⟨hzi, hzi'', hu0, hu0', hrat⟩ := h
  set p := (fstG (maximalIdeal R) e G).left with hp
  have minor : ∀ j l, secGerm (u ≫ p) z (s j) i * secGerm (u' ≫ p) z (s l) i'' =
      secGerm (u ≫ p) z (s l) i * secGerm (u' ≫ p) z (s j) i'' := by
    intro j l
    have h1 := hrat (s j)
    have h2 := hrat (s l)
    apply (hu0.mul hu0').mul_left_cancel
    linear_combination (secGerm (u ≫ p) z s₀ i * secGerm (u' ≫ p) z (s l) i'') * h1 -
      (secGerm (u ≫ p) z s₀ i * secGerm (u' ≫ p) z (s j) i'') * h2

  let K := Z.residueField z
  let x : Spec (CommRingCat.of K) ⟶ Z := Z.fromSpecResidueField z
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  have hx : x pt = z := Scheme.fromSpecResidueField_apply z pt
  have minorx : ∀ j l, secGerm (x ≫ u ≫ p) pt (s j) i * secGerm (x ≫ u' ≫ p) pt (s l) i'' =
      secGerm (x ≫ u ≫ p) pt (s l) i * secGerm (x ≫ u' ≫ p) pt (s j) i'' := by
    intro j l
    have hi : (u ≫ p) (x pt) ∈ secChart U.LG.L i := hx ▸ hzi
    have hi'' : (u' ≫ p) (x pt) ∈ secChart U.LG.L i'' := hx ▸ hzi''
    have m := hx ▸ minor j l
    rw [secGerm_comp x (u ≫ p) pt _ hi, secGerm_comp x (u ≫ p) pt _ hi, secGerm_comp x (u' ≫ p) pt _ hi'',
      secGerm_comp x (u' ≫ p) pt _ hi'', ← map_mul, ← map_mul, m]

  obtain ⟨g, hg1, hg2⟩ := exists_closedFibre_factor R G e K (x ≫ u)
  obtain ⟨g', hg1', hg2'⟩ := exists_closedFibre_factor R G e K (x ≫ u')
  let T : Over (Sp R) := Over.mk ((x ≫ u) ≫ (thickObj R (maximalIdeal R) e G).hom ≫ thick R (maximalIdeal R) e)
  have hgT : g ≫ (thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0 = T.hom := hg2
  have hgT' : g' ≫ (thickObj R (maximalIdeal R) 0 G).hom ≫ thick R (maximalIdeal R) 0 = T.hom := by
    rw [hg2']; show _ = (x ≫ u) ≫ _
    simp only [Category.assoc, ← reassoc_of% hu]
  obtain ⟨ξ, hξ⟩ := GlobalTheory.TorusCoord.exists_isPointOf (U.gt 0) (T := T) g hgT
  obtain ⟨ξ', hξ'⟩ := GlobalTheory.TorusCoord.exists_isPointOf (U.gt 0) (T := T) g' hgT'
  set y := (Y.Φ T).symm ξ with hy
  set y' := (Y.Φ T).symm ξ' with hy'
  have hyξ : Y.Φ T y = ξ := Equiv.apply_symm_apply _ _
  have hyξ' : Y.Φ T y' = ξ' := Equiv.apply_symm_apply _ _
  obtain ⟨J, hJ⟩ := GlobalTheory.TorusCoord.exists_good' U.LG.isLB pt
  obtain ⟨J', hJ'⟩ := GlobalTheory.TorusCoord.exists_good' D.toPre.P.isLB pt
  obtain ⟨c, hc⟩ := GlobalTheory.T.closedFibre_sectionValue_eq_unit_mul_fourierTerm R D A G U.toUnifPre Y T g y (hyξ ▸ hξ) k pt J J' hJ hJ'
  obtain ⟨c', hc'⟩ := GlobalTheory.T.closedFibre_sectionValue_eq_unit_mul_fourierTerm R D A G U.toUnifPre Y T g' y' (hyξ' ▸ hξ') k pt J J' hJ hJ'
  have hv : ∀ j, secGerm (x ≫ u ≫ p) pt (s j) (fun _ => J ((x ≫ u ≫ p) ≫ 𝟙 _)) = c.val * sval (τ j) y.left pt J' := by
    intro j
    have := hc (α j) (b j) (τ j) (F j) (s j) (hαb j).2 (hF j) (hs j 0)
    rw [hg1, Category.assoc] at this
    exact this
  have hv' : ∀ j, secGerm (x ≫ u' ≫ p) pt (s j) (fun _ => J ((x ≫ u' ≫ p) ≫ 𝟙 _)) = c'.val * sval (τ j) y'.left pt J' := by
    intro j
    have := hc' (α j) (b j) (τ j) (F j) (s j) (hαb j).2 (hF j) (hs j 0)
    rw [hg1', Category.assoc] at this
    exact this
  have hi : (x ≫ u ≫ p) pt ∈ secChart U.LG.L i := by
    rw [Scheme.Hom.comp_apply, hx]; exact hzi
  have hi'' : (x ≫ u' ≫ p) pt ∈ secChart U.LG.L i'' := by
    rw [Scheme.Hom.comp_apply, hx]; exact hzi''
  obtain ⟨a, ha⟩ := exists_unit_secGerm k (x ≫ u ≫ p) pt hi (hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (x ≫ u ≫ p))
  obtain ⟨a', ha'⟩ := exists_unit_secGerm k (x ≫ u' ≫ p) pt hi'' (hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (x ≫ u' ≫ p))
  have minorτ : ∀ j l, sval (τ j) y.left pt J' * sval (τ l) y'.left pt J' = sval (τ l) y.left pt J' * sval (τ j) y'.left pt J' := by
    intro j l
    have m := minorx j l
    rw [ha, ha, ha', ha', hv, hv, hv', hv'] at m
    apply (((a.isUnit.mul a'.isUnit).mul c.isUnit).mul c'.isUnit).mul_left_cancel
    linear_combination m
  obtain ⟨W, hW, hWy⟩ := GlobalTheory.T.thetaImmersion_points_agree_near_of_equal_ratios R D.toPre Y k N τ hτ himm T y y' pt J' hJ' minorτ
  have hWt : W = ⊤ := by
    exact eq_top_iff.2 fun q _ => (Subsingleton.elim (α := Spec (CommRingCat.of K)) q pt) ▸ hW
  subst hWt
  have : IsIso (⊤ : (T.left).Opens).ι := by rw [← Scheme.topIso_hom]; infer_instance
  have hyy : y = y' := Over.OverMorphism.ext ((cancel_epi _).1 hWy)
  have hξξ : ξ = ξ' := by rw [← hyξ, ← hyξ', hyy]
  have hgg : g = g' := GlobalTheory.TorusCoord.IsPointOf.unique_left (U.gt 0) hξ (hξξ ▸ hξ')
  have hpp : (x ≫ u ≫ p) pt = (x ≫ u' ≫ p) pt := by
    rw [← Category.assoc, ← hg1, ← Category.assoc, ← hg1', hgg]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hx] at hpp
  have : IsClosedImmersion p := by
    show IsClosedImmersion (pullback.fst G.hom (thick R (maximalIdeal R) e))
    have : IsClosedImmersion (thick R (maximalIdeal R) e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
    infer_instance
  exact p.isClosedEmbedding.injective hpp

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningMorphismsAgreeBeyondThresholdStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickening_morphisms_agree_beyond_threshold : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k : ℕ), k₀ ≤ k → ∀ (Z : Scheme.{0}) (u u' : Z ⟶ (thickObj R (maximalIdeal R) e G).left), u ≫ (thickObj R (maximalIdeal R) e G).hom = u' ≫ (thickObj R (maximalIdeal R) e G).hom → ∀ (s₀ : H0 U.LG.L k) (i i'' : Fin 1 → U.LG.L.ι) (z : Z), GermRatioAgree (u ≫ (fstG (maximalIdeal R) e G).left) (u' ≫ (fstG (maximalIdeal R) e G).left) s₀ i i'' z → u z = u' z := by
  first | exact @GlobalTheory.Mum.eq_of_germRatioAgree | exact GlobalTheory.Mum.eq_of_germRatioAgree | (intros; apply GlobalTheory.Mum.eq_of_germRatioAgree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupMorphismsAgreeOfSectionRatios
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem agree_near_of_ratios : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k k' : ℕ), k₀ ≤ k → ∀ (x x' : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (T : H0 U.LG.L k → H0 U.LG.L k'), (∀ s₁ s₂ : H0 U.LG.L k, SecRatioEq U.LG.L (x.left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (T s₁) (T s₂)) → (∀ s₁ s₂ : H0 U.LG.L k, SecRatioEq U.LG.L (x'.left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (T s₁) (T s₂)) → ∀ (y : (thickObj R (maximalIdeal R) e G).left) (s₀ : H0 U.LG.L k) (i i' i'' : Fin 1 → U.LG.L.ι), y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen ((((x).left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i)).hom (s₀.f i)) → y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen (((fstG (maximalIdeal R) e G).left.app (secChart U.LG.L i')).hom ((T s₀).f i')) → y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen ((((x').left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i'')).hom (s₀.f i'')) → ∃ W : (thickObj R (maximalIdeal R) e G).left.Opens, y ∈ W ∧ W.ι ≫ x.left = W.ι ≫ x'.left := by

  intro R _ _ _ hB D A G _ _ hG U
  obtain ⟨k₁, hk₁, H₁⟩ := GlobalTheory.T.thickening_morphisms_agree_beyond_threshold R hB D A G hG U
  obtain ⟨k₂, -, H₂⟩ := GlobalTheory.T.uniformisedGroup_morphisms_agree_near_point R hB D A G hG U
  refine ⟨max k₁ k₂, le_trans hk₁ (le_max_left _ _), ?_⟩
  intro e k k' hk x x' T hx hx' y s₀ i i' i'' hy₁ hy₂ hy₃
  have m₁ : (x.left ≫ (fstG (maximalIdeal R) e G).left) y ∈ secChart U.LG.L i :=
    (thickObj R (maximalIdeal R) e G).left.basicOpen_le _ hy₁
  have m₂ : (fstG (maximalIdeal R) e G).left y ∈ secChart U.LG.L i' :=
    (thickObj R (maximalIdeal R) e G).left.basicOpen_le _ hy₂
  have m₃ : (x'.left ≫ (fstG (maximalIdeal R) e G).left) y ∈ secChart U.LG.L i'' :=
    (thickObj R (maximalIdeal R) e G).left.basicOpen_le _ hy₃
  have u₁ : IsUnit (secGerm (x.left ≫ (fstG (maximalIdeal R) e G).left) y s₀ i) := by
    exact (congrArg IsUnit (gs_eq _ _ _ m₁ _)).mpr ((Scheme.mem_basicOpen (thickObj R (maximalIdeal R) e G).left _ y m₁).1 hy₁)
  have u₂ : IsUnit (secGerm (fstG (maximalIdeal R) e G).left y (T s₀) i') := by
    exact (congrArg IsUnit (gs_eq _ _ _ m₂ _)).mpr ((Scheme.mem_basicOpen (thickObj R (maximalIdeal R) e G).left _ y m₂).1 hy₂)
  have u₃ : IsUnit (secGerm (x'.left ≫ (fstG (maximalIdeal R) e G).left) y s₀ i'') := by
    exact (congrArg IsUnit (gs_eq _ _ _ m₃ _)).mpr ((Scheme.mem_basicOpen (thickObj R (maximalIdeal R) e G).left _ y m₃).1 hy₃)
  have hA : GermRatioAgree (x.left ≫ (fstG (maximalIdeal R) e G).left)
      (x'.left ≫ (fstG (maximalIdeal R) e G).left) s₀ i i'' y := by
    refine ⟨m₁, m₃, u₁, u₃, fun s₁ => ?_⟩
    have e₁ := secRatioEq_iff_germ.1 (hx s₁ s₀) y i i' m₁ m₂
    have e₂ := secRatioEq_iff_germ.1 (hx' s₁ s₀) y i'' i' m₃ m₂
    apply (u₂.mul_left_inj).1
    linear_combination secGerm (x'.left ≫ (fstG (maximalIdeal R) e G).left) y s₀ i'' * e₁ -
      secGerm (x.left ≫ (fstG (maximalIdeal R) e G).left) y s₀ i * e₂
  have hb : x.left ≫ (thickObj R (maximalIdeal R) e G).hom = x'.left ≫ (thickObj R (maximalIdeal R) e G).hom := by
    rw [Over.w x, Over.w x']
  have hk₁' : k₁ ≤ k := le_trans (le_max_left _ _) hk
  have hk₂' : k₂ ≤ k := le_trans (le_max_right _ _) hk
  exact H₂ e k hk₂' _ x.left x'.left hb s₀ i i'' y hA (H₁ e k hk₁' _ x.left x'.left hb s₀ i i'' y hA)

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedGroupMorphismsAgreeOfSectionRatiosStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisedGroup_morphisms_agree_of_sectionRatios : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ (e k k' : ℕ), k₀ ≤ k → ∀ (x x' : thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (T : H0 U.LG.L k → H0 U.LG.L k'), (∀ s₁ s₂ : H0 U.LG.L k, SecRatioEq U.LG.L (x.left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (T s₁) (T s₂)) → (∀ s₁ s₂ : H0 U.LG.L k, SecRatioEq U.LG.L (x'.left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (T s₁) (T s₂)) → ∀ (y : (thickObj R (maximalIdeal R) e G).left) (s₀ : H0 U.LG.L k) (i i' i'' : Fin 1 → U.LG.L.ι), y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen ((((x).left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i)).hom (s₀.f i)) → y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen (((fstG (maximalIdeal R) e G).left.app (secChart U.LG.L i')).hom ((T s₀).f i')) → y ∈ (thickObj R (maximalIdeal R) e G).left.basicOpen ((((x').left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i'')).hom (s₀.f i'')) → ∃ W : (thickObj R (maximalIdeal R) e G).left.Opens, y ∈ W ∧ W.ι ≫ x.left = W.ι ≫ x'.left := by
  first | exact @GlobalTheory.Mum.agree_near_of_ratios | exact GlobalTheory.Mum.agree_near_of_ratios | (intros; apply GlobalTheory.Mum.agree_near_of_ratios <;> assumption)
end
