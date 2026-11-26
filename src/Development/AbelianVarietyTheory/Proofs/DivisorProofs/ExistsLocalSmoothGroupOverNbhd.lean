module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealEqSpanMonomialOfOrdersAlongCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonKltCentreOfNotKltAfterAdding
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPushoutLocalizedPresentationBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadMorphismBasicOpenAgreeFlat

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartGrpLawAgreesWithAbelianSchemeLaw
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartGrpLawAgreesWithAbelianSchemeLaw
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.ChartLaw

theorem awayMap_notMem {R : Type} [CommRing R] (g : R) (w : Sp (Localization.Away g)) : g ∉ (awayMap g w).asIdeal := by
  intro h
  have : algebraMap R (Localization.Away g) g ∈ w.asIdeal := h
  exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ this (IsLocalization.Away.algebraMap_isUnit g))

theorem mul_left_comp {S T T' : Scheme.{0}} {H : Over S} [GrpObj H] {t : T ⟶ S} {t' : T' ⟶ S} (k : T' ⟶ T)
    (a b : Over.mk t ⟶ H) (a₁ b₁ : Over.mk t' ⟶ H) (ha : a₁.left = k ≫ a.left) (hb : b₁.left = k ≫ b.left) :
    (a₁ * b₁).left = k ≫ (a * b).left := by
  have ht : k ≫ t = t' := by
    have e1 : a.left ≫ H.hom = t := Over.w a
    have e2 : a₁.left ≫ H.hom = t' := Over.w a₁
    rw [← e1, ← e2, ha]; exact (Category.assoc _ _ _).symm
  let κ : Over.mk t' ⟶ Over.mk t := Over.homMk k ht
  have e1 : a₁ = κ ≫ a := Over.OverMorphism.ext ha
  have e2 : b₁ = κ ≫ b := Over.OverMorphism.ext hb
  rw [e1, e2, ← MonObj.comp_mul]
  rfl

theorem lift_open (σ : Setup) (x : Sp σ.R) {T : Scheme.{0}} (c : T ⟶ (σ.C x).G.left) (d : T ⟶ Sp (Localization.Away σ.f))
    (e : c ≫ (σ.C x).G.hom ≫ spMap (σ.ρ x) = d ≫ awayMap σ.f) : ∃ l : T ⟶ (σ.V x).toScheme, l ≫ (σ.V x).ι = c := by
  refine ⟨IsOpenImmersion.lift (σ.V x).ι c ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨τ, rfl⟩
  rw [Scheme.Opens.range_ι]
  refine (σ.hV x _).2 ?_
  have h1 := awayMap_notMem σ.f (d τ)
  rw [← Scheme.Hom.comp_apply, ← e] at h1
  exact h1

theorem chart_mul_generic (σ : Setup) (E : Emb σ) (x : Sp σ.R) {T : Scheme.{0}} (s : T ⟶ Sp (FractionRing (σ.C x).R))
    (t₂ : T ⟶ Sp (Localization.Away σ.f)) (a b : Over.mk (s ≫ jK (σ.C x).R) ⟶ (σ.C x).G) (a' b' : Over.mk t₂ ⟶ σ.A)
    (ha : a.left ≫ E.emb x = a'.left ≫ E.ιA) (hb : b.left ≫ E.emb x = b'.left ≫ E.ιA) :
    (a * b).left ≫ E.emb x = (a' * b').left ≫ E.ιA := by
  have : IsOpenImmersion E.ιA := MorphismProperty.of_isPullback E.cartA.flip inferInstance
  obtain ⟨l, hl⟩ := lift_open σ x (pullback.fst (σ.C x).G.hom (jK (σ.C x).R)) (pullback.snd _ _ ≫ (σ.C x).y) (by
    rw [pullback.condition_assoc, Category.assoc, (σ.C x).hy, σ.hρ])
  have hα : (σ.C x).α ≫ E.ιA = pullback.fst (σ.C x).G.hom (jK (σ.C x).R) ≫ E.emb x := by
    have := σ.compat x _ (𝟙 _) l (by rw [Category.id_comp, hl])
    rw [Category.id_comp] at this
    rw [this, Category.assoc, E.onV, ← Category.assoc, hl]
  let P : (Over.mk (s ≫ jK (σ.C x).R) ⟶ (σ.C x).G) → (Over.mk s ⟶ (Over.pullback (jK (σ.C x).R)).obj (σ.C x).G) :=
    fun c => Over.homMk (pullback.lift c.left s (Over.w c)) (pullback.lift_snd _ _ _)
  have hP : ∀ c, c.left = (P c).left ≫ pullback.fst (σ.C x).G.hom (jK (σ.C x).R) := fun c => (pullback.lift_fst _ _ _).symm
  have hA : ∀ c (c' : Over.mk t₂ ⟶ σ.A), c.left ≫ E.emb x = c'.left ≫ E.ιA → c'.left = (P c).left ≫ (σ.C x).α := by
    intro c c' h
    rw [← cancel_mono E.ιA, ← h, hP c]
    exact (Category.assoc _ _ _).trans ((congrArg ((P c).left ≫ ·) hα.symm).trans (Category.assoc _ _ _).symm)
  have ht : t₂ = s ≫ (σ.C x).y := by
    have e1 : a'.left ≫ σ.A.hom = t₂ := Over.w a'
    have e2 : (P a).left ≫ ((Over.pullback (jK (σ.C x).R)).obj (σ.C x).G).hom = s := Over.w (P a)
    have e3 := (σ.C x).gen.1.w
    rw [← e1, hA a a' ha]
    exact (Category.assoc _ _ _).trans ((congrArg ((P a).left ≫ ·) e3).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (σ.C x).y) e2)))
  subst ht
  have m1 := (σ.C x).gen.2 (Over.mk s) (P a) (P b) a' b' (hA a a' ha) (hA b b' hb)
  have m2 := (isGrpPullback_pullback (σ.C x).G (jK (σ.C x).R)).2 (Over.mk s) (P a) (P b) a b (hP a) (hP b)
  exact (congrArg (· ≫ E.emb x) m2).trans ((Category.assoc _ _ _).trans ((congrArg ((P a * P b).left ≫ ·) hα.symm).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ E.ιA) m1.symm))))

theorem chart_mul_flat (σ : Setup) (E : Emb σ) (x : Sp σ.R) {T : Scheme.{0}} (t₁ : T ⟶ Sp (σ.C x).R) [Flat t₁]
    (t₂ : T ⟶ Sp (Localization.Away σ.f)) (a b : Over.mk t₁ ⟶ (σ.C x).G) (a' b' : Over.mk t₂ ⟶ σ.A)
    (ha : a.left ≫ E.emb x = a'.left ≫ E.ιA) (hb : b.left ≫ E.emb x = b'.left ≫ E.ιA) :
    (a * b).left ≫ E.emb x = (a' * b').left ≫ E.ιA := by
  have := E.sep
  obtain ⟨w, -⟩ := E.openIn x
  have p1 : ∀ c : Over.mk t₁ ⟶ (σ.C x).G, (c.left ≫ E.emb x) ≫ E.p = t₁ ≫ spMap (σ.ρ x) := fun c => by
    have e : c.left ≫ (σ.C x).G.hom = t₁ := Over.w c
    rw [Category.assoc, w, ← Category.assoc, e]
  have p2 : ∀ c : Over.mk t₂ ⟶ σ.A, (c.left ≫ E.ιA) ≫ E.p = t₂ ≫ awayMap σ.f := fun c => by
    have e : c.left ≫ σ.A.hom = t₂ := Over.w c
    rw [Category.assoc, E.cartA.w, ← Category.assoc, e]
  have : IsSchemeTheoreticallyDominant (jK (σ.C x).R) :=
    schDom_spec_map _ (IsFractionRing.injective (σ.C x).R (FractionRing (σ.C x).R))
  have : IsSchemeTheoreticallyDominant (pullback.fst t₁ (jK (σ.C x).R)) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback t₁ (jK (σ.C x).R)).flip
  refine ext_of_schDom E.p (by rw [p1, p2, ← p1 a, ← p2 a', ha]) (pullback.fst t₁ (jK (σ.C x).R)) ?_
  let k := pullback.fst t₁ (jK (σ.C x).R)
  let Q : (Over.mk t₁ ⟶ (σ.C x).G) → (Over.mk (pullback.snd t₁ (jK (σ.C x).R) ≫ jK (σ.C x).R) ⟶ (σ.C x).G) := fun c =>
    Over.homMk (k ≫ c.left) ((Category.assoc _ _ _).trans ((congrArg (k ≫ ·) (Over.w c)).trans pullback.condition))
  let Q' : (Over.mk t₂ ⟶ σ.A) → (Over.mk (k ≫ t₂) ⟶ σ.A) := fun c =>
    Over.homMk (k ≫ c.left) ((Category.assoc _ _ _).trans (congrArg (k ≫ ·) (Over.w c)))
  have h := chart_mul_generic σ E x _ _ (Q a) (Q b) (Q' a') (Q' b')
    ((Category.assoc _ _ _).trans ((congrArg (k ≫ ·) ha).trans (Category.assoc _ _ _).symm))
    ((Category.assoc _ _ _).trans ((congrArg (k ≫ ·) hb).trans (Category.assoc _ _ _).symm))
  rw [mul_left_comp k a b (Q a) (Q b) rfl rfl, mul_left_comp k a' b' (Q' a') (Q' b') rfl rfl] at h
  exact (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))

theorem chart_mulAgree : ∀ (σ : Setup) (E : Emb σ) (x : Sp σ.R), MulAgree (σ.C x).G σ.A (E.emb x) E.ιA := by
  intro σ E x T t₁ t₂ a b a' b' ha hb
  have : IsOpenImmersion E.ιA := MorphismProperty.of_isPullback E.cartA.flip inferInstance
  have := (σ.C x).semi.smooth
  obtain ⟨w, -⟩ := E.openIn x
  have hl : ∀ (c : Over.mk t₁ ⟶ (σ.C x).G) (c' : Over.mk t₂ ⟶ σ.A), c.left ≫ E.emb x = c'.left ≫ E.ιA →
      ∃ l : T ⟶ (σ.V x).toScheme, l ≫ (σ.V x).ι = c.left ∧ l ≫ σ.φ x = c'.left := by
    intro c c' h
    obtain ⟨l, hl⟩ := lift_open σ x c.left (c'.left ≫ σ.A.hom) (by
      rw [← w, ← Category.assoc, h, Category.assoc, E.cartA.w, Category.assoc])
    refine ⟨l, hl, ?_⟩
    rw [← cancel_mono E.ιA, Category.assoc, E.onV, ← Category.assoc, hl]
    exact h
  obtain ⟨la, ha1, ha2⟩ := hl a a' ha
  obtain ⟨lb, hb1, hb2⟩ := hl b b' hb
  let q : (σ.V x).toScheme ⟶ Sp (σ.C x).R := (σ.V x).ι ≫ (σ.C x).G.hom
  have hq : la ≫ q = lb ≫ q := by
    have e1 : a.left ≫ (σ.C x).G.hom = t₁ := Over.w a
    have e2 : b.left ≫ (σ.C x).G.hom = t₁ := Over.w b
    simp only [q, ← Category.assoc, ha1, hb1]
    exact e1.trans e2.symm
  have hu : pullback.snd q q ≫ σ.φ x ≫ σ.A.hom = pullback.fst q q ≫ σ.φ x ≫ σ.A.hom := by
    rw [← cancel_mono (awayMap σ.f)]
    simp only [Category.assoc]
    rw [(σ.cart x).w]
    exact (pullback.condition_assoc (f := q) (g := q) _).symm
  let a₀ : Over.mk (pullback.fst q q ≫ q) ⟶ (σ.C x).G := Over.homMk (pullback.fst q q ≫ (σ.V x).ι) (Category.assoc _ _ _)
  let b₀ : Over.mk (pullback.fst q q ≫ q) ⟶ (σ.C x).G := Over.homMk (pullback.snd q q ≫ (σ.V x).ι)
    ((Category.assoc _ _ _).trans pullback.condition.symm)
  let a₁ : Over.mk (pullback.fst q q ≫ σ.φ x ≫ σ.A.hom) ⟶ σ.A := Over.homMk (pullback.fst q q ≫ σ.φ x) (Category.assoc _ _ _)
  let b₁ : Over.mk (pullback.fst q q ≫ σ.φ x ≫ σ.A.hom) ⟶ σ.A := Over.homMk (pullback.snd q q ≫ σ.φ x)
    ((Category.assoc _ _ _).trans hu)
  have h := chart_mul_flat σ E x (pullback.fst q q ≫ q) _ a₀ b₀ a₁ b₁
    ((Category.assoc _ _ _).trans ((congrArg (pullback.fst q q ≫ ·) (E.onV x).symm).trans (Category.assoc _ _ _).symm))
    ((Category.assoc _ _ _).trans ((congrArg (pullback.snd q q ≫ ·) (E.onV x).symm).trans (Category.assoc _ _ _).symm))
  let k := pullback.lift la lb hq
  have k1 : k ≫ pullback.fst q q = la := pullback.lift_fst _ _ _
  have k2 : k ≫ pullback.snd q q = lb := pullback.lift_snd _ _ _
  rw [mul_left_comp k a₀ b₀ a b (ha1.symm.trans (by rw [← k1]; exact Category.assoc _ _ _))
      (hb1.symm.trans (by rw [← k2]; exact Category.assoc _ _ _)),
    mul_left_comp k a₁ b₁ a' b' (ha2.symm.trans (by rw [← k1]; exact Category.assoc _ _ _))
      (hb2.symm.trans (by rw [← k2]; exact Category.assoc _ _ _))]
  exact (Category.assoc _ _ _).trans ((congrArg (k ≫ ·) h).trans (Category.assoc _ _ _).symm)

end GlobalTheory.Desc.ChartLaw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartGrpLawAgreesWithAbelianSchemeLawStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_grpLaw_agrees_with_abelian_scheme_law : ∀ (σ : Setup) (E : Emb σ) (x : Sp σ.R), MulAgree (σ.C x).G σ.A (E.emb x) E.ιA := by
  first | exact @GlobalTheory.Desc.ChartLaw.chart_mulAgree | exact GlobalTheory.Desc.ChartLaw.chart_mulAgree | (intros; apply GlobalTheory.Desc.ChartLaw.chart_mulAgree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjOfLawUnitInverseAgreeAway
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjOfLawUnitInverseAgreeAway
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.SpreadGrp

theorem grpObj_of_agree : ∀ (R : Type) [CommRing R] [IsDomain R] (f g : R), f ≠ 0 → ∀ (X : Scheme.{0}) (q : X ⟶ Sp R), Flat q → IsSeparated q → ∀ (A : Over (Sp (Localization.Away f))) [GrpObj A], IsCommMonObj A → ∀ i : A.left ⟶ X, IsPullback i A.hom q (awayMap f) → ∀ (H : Over (Sp (Localization.Away g))) (h : H.left ⟶ X), IsPullback h H.hom q (awayMap g) → ∀ (m : H ⊗ H ⟶ H) (n : H ⟶ H) (o : 𝟙_ (Over (Sp (Localization.Away g))) ⟶ H), (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)) (a b : Over.mk t₁ ⟶ H) (a' b' : Over.mk t₀ ⟶ A), a.left ≫ h = a'.left ≫ i → b.left ≫ h = b'.left ≫ i → (lift a b ≫ m).left ≫ h = (a' * b').left ≫ i) → (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)) (a : Over.mk t₁ ⟶ H) (a' : Over.mk t₀ ⟶ A), a.left ≫ h = a'.left ≫ i → (a ≫ n).left ≫ h = (a'⁻¹).left ≫ i) → (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)), t₁ ≫ awayMap g = t₀ ≫ awayMap f → t₁ ≫ o.left ≫ h = (1 : Over.mk t₀ ⟶ A).left ≫ i) → ∃ _ : GrpObj H, MulAgree H A h i := by
  intro R _ _ f g hf X q hq hs A _ _ i hA H h hH m n o hm hn ho
  have hinj : Function.Injective (algebraMap R (Localization.Away f)) :=
    IsLocalization.injective (Localization.Away f) (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsSchemeTheoreticallyDominant (awayMap f) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective
      (CommRingCat.ofHom (algebraMap R (Localization.Away f))) hinj
  have : Flat (awayMap g) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (Submonoid.powers g))
  have : Flat H.hom := MorphismProperty.of_isPullback hH hq
  have : IsSeparated H.hom := MorphismProperty.of_isPullback hH hs
  have := ExtUnique.flat_tensorUnit (S := Sp (Localization.Away g))
  have := ExtUnique.flat_tensorObj H H
  have := ExtUnique.flat_tensorObj (𝟙_ _) H
  have := ExtUnique.flat_tensorObj H (𝟙_ _)
  have := ExtUnique.flat_tensorObj (H ⊗ H) H
  let j := pullback.fst (awayMap g) (awayMap f)
  let k := pullback.snd (awayMap g) (awayMap f)
  have w : ∀ T : Over (pullback (awayMap g) (awayMap f)), (T.hom ≫ j) ≫ awayMap g = (T.hom ≫ k) ≫ awayMap f := by
    intro T; simp only [Category.assoc, j, k, pullback.condition]

  have key : ∀ {T : Scheme.{0}} {t₁ : T ⟶ Sp (Localization.Away g)} {t₀ : T ⟶ Sp (Localization.Away f)},
      t₁ ≫ awayMap g = t₀ ≫ awayMap f → ∀ a : Over.mk t₁ ⟶ H, ∃ a' : Over.mk t₀ ⟶ A, a.left ≫ h = a'.left ≫ i := by
    intro T t₁ t₀ e a
    have e' : (a.left ≫ h) ≫ q = t₀ ≫ awayMap f := by
      rw [Category.assoc, hH.w, ← Category.assoc, Over.w a]; exact e
    exact ⟨Over.homMk (hA.lift (a.left ≫ h) t₀ e') (hA.lift_snd _ _ _), (hA.lift_fst _ _ _).symm⟩

  have inj : ∀ {T : Scheme.{0}} {t₁ : T ⟶ Sp (Localization.Away g)} (a b : Over.mk t₁ ⟶ H),
      a.left ≫ h = b.left ≫ h → a = b := by
    intro T t₁ a b e
    exact Over.OverMorphism.ext (hH.hom_ext e (by rw [Over.w a, Over.w b]))
  have hone : ∀ {T : Scheme.{0}} {t₁ : T ⟶ Sp (Localization.Away g)} {t₀ : T ⟶ Sp (Localization.Away f)},
      t₁ ≫ awayMap g = t₀ ≫ awayMap f → (toUnit (Over.mk t₁) ≫ o).left ≫ h = (1 : Over.mk t₀ ⟶ A).left ≫ i := by
    intro T t₁ t₀ e
    simpa using ho T t₁ t₀ e
  letI : MonObj H :=
    { one := o
      mul := m
      one_mul := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ : ∃ x, t ≫ snd _ _ = x := ⟨_, rfl⟩
        have ht : t = lift (toUnit _) x :=
          CartesianMonoidalCategory.hom_ext _ _ (toUnit_unique _ _) (by rw [lift_snd, hx])
        subst ht
        obtain ⟨x', hx'⟩ := key (w T) x
        rw [lift_whiskerRight_assoc, lift_leftUnitor_hom]
        apply inj
        rw [hm _ _ _ _ _ _ _ (hone (w T)) hx', _root_.one_mul, hx']
      mul_one := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ : ∃ x, t ≫ fst _ _ = x := ⟨_, rfl⟩
        have ht : t = lift x (toUnit _) :=
          CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (toUnit_unique _ _)
        subst ht
        obtain ⟨x', hx'⟩ := key (w T) x
        rw [lift_whiskerLeft_assoc, lift_rightUnitor_hom]
        apply inj
        rw [hm _ _ _ _ _ _ _ hx' (hone (w T)), _root_.mul_one, hx']
      mul_assoc := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x, hx⟩ : ∃ x, t ≫ fst _ _ ≫ fst _ _ = x := ⟨_, rfl⟩
        obtain ⟨y, hy⟩ : ∃ y, t ≫ fst _ _ ≫ snd _ _ = y := ⟨_, rfl⟩
        obtain ⟨z, hz⟩ : ∃ z, t ≫ snd _ _ = z := ⟨_, rfl⟩
        have ht : t = lift (lift x y) z := by
          ext <;> simp [← hx, ← hy, ← hz]
        subst ht
        obtain ⟨x', hx'⟩ := key (w T) x
        obtain ⟨y', hy'⟩ := key (w T) y
        obtain ⟨z', hz'⟩ := key (w T) z
        rw [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc]
        apply inj
        rw [hm _ _ _ _ _ _ _ (hm _ _ _ _ _ _ _ hx' hy') hz', hm _ _ _ _ _ _ _ hx' (hm _ _ _ _ _ _ _ hy' hz'),
          _root_.mul_assoc] }
  letI : GrpObj H :=
    { inv := n
      left_inv := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x', hx'⟩ := key (w T) t
        change _ ≫ lift n (𝟙 H) ≫ m = _ ≫ toUnit H ≫ o
        rw [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
        apply inj
        rw [hm _ _ _ _ _ _ _ (hn _ _ _ _ _ hx') hx', inv_mul_cancel, hone (w T)]
      right_inv := SpreadAb.hom_ext_of_points j fun T t => by
        obtain ⟨x', hx'⟩ := key (w T) t
        change _ ≫ lift (𝟙 H) n ≫ m = _ ≫ toUnit H ≫ o
        rw [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
        apply inj
        rw [hm _ _ _ _ _ _ _ hx' (hn _ _ _ _ _ hx'), mul_inv_cancel, hone (w T)] }
  exact ⟨inferInstance, fun T t₁ t₂ a b a' b' ha hb => hm T t₁ t₂ a b a' b' ha hb⟩

end GlobalTheory.Desc.SpreadGrp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpObjOfLawUnitInverseAgreeAwayStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grpObj_of_law_unit_inverse_agree_away : ∀ (R : Type) [CommRing R] [IsDomain R] (f g : R), f ≠ 0 → ∀ (X : Scheme.{0}) (q : X ⟶ Sp R), Flat q → IsSeparated q → ∀ (A : Over (Sp (Localization.Away f))) [GrpObj A], IsCommMonObj A → ∀ i : A.left ⟶ X, IsPullback i A.hom q (awayMap f) → ∀ (H : Over (Sp (Localization.Away g))) (h : H.left ⟶ X), IsPullback h H.hom q (awayMap g) → ∀ (m : H ⊗ H ⟶ H) (n : H ⟶ H) (o : 𝟙_ (Over (Sp (Localization.Away g))) ⟶ H), (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)) (a b : Over.mk t₁ ⟶ H) (a' b' : Over.mk t₀ ⟶ A), a.left ≫ h = a'.left ≫ i → b.left ≫ h = b'.left ≫ i → (lift a b ≫ m).left ≫ h = (a' * b').left ≫ i) → (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)) (a : Over.mk t₁ ⟶ H) (a' : Over.mk t₀ ⟶ A), a.left ≫ h = a'.left ≫ i → (a ≫ n).left ≫ h = (a'⁻¹).left ≫ i) → (∀ (T : Scheme.{0}) (t₁ : T ⟶ Sp (Localization.Away g)) (t₀ : T ⟶ Sp (Localization.Away f)), t₁ ≫ awayMap g = t₀ ≫ awayMap f → t₁ ≫ o.left ≫ h = (1 : Over.mk t₀ ⟶ A).left ≫ i) → ∃ _ : GrpObj H, MulAgree H A h i := by
  first | exact @GlobalTheory.Desc.SpreadGrp.grpObj_of_agree | exact GlobalTheory.Desc.SpreadGrp.grpObj_of_agree | (intros; apply GlobalTheory.Desc.SpreadGrp.grpObj_of_agree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpUnitsAndInversesAgreeOfLawsAgree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpUnitsAndInversesAgreeOfLawsAgree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem hom_ext_of_cartesian {S S₀ X : Scheme.{0}} {q : X ⟶ S} {s₀ : S₀ ⟶ S} {A : Over S₀}
    {i : A.left ⟶ X} (h : IsPullback i A.hom q s₀) {T : Scheme.{0}} {t₀ : T ⟶ S₀}
    (c c' : Over.mk t₀ ⟶ A) (hc : c.left ≫ i = c'.left ≫ i) : c = c' := by
  apply Over.OverMorphism.ext
  apply h.hom_ext hc
  rw [Over.w c, Over.w c']

theorem oneAgree_invAgree_of_mulAgree : ∀ (S S₀ S₁ X : Scheme.{0}) (q : X ⟶ S) (s₀ : S₀ ⟶ S) (s₁ : S₁ ⟶ S) (A : Over S₀) [GrpObj A] (G : Over S₁) [GrpObj G] (i : A.left ⟶ X) (e : G.left ⟶ X), IsPullback i A.hom q s₀ → e ≫ q = G.hom ≫ s₁ → MulAgree G A e i → OneAgree s₁ s₀ G A e i ∧ ∀ (T : Scheme.{0}) (t₁ : T ⟶ S₁) (t₀ : T ⟶ S₀) (a : Over.mk t₁ ⟶ G) (a' : Over.mk t₀ ⟶ A), a.left ≫ e = a'.left ≫ i → (a⁻¹).left ≫ e = (a'⁻¹).left ≫ i := by
  intro S S₀ S₁ X q s₀ s₁ A _ G _ i e h he hm
  have one : OneAgree s₁ s₀ G A e i := by
    intro T t₁ t₀ ht
    have hw : ((1 : Over.mk t₁ ⟶ G).left ≫ e) ≫ q = t₀ ≫ s₀ := by
      rw [Category.assoc, he, ← Category.assoc, Over.w]; exact ht
    let a' : Over.mk t₀ ⟶ A := Over.homMk (h.lift _ t₀ hw) (by simp)
    have ha' : a'.left ≫ i = (1 : Over.mk t₁ ⟶ G).left ≫ e := h.lift_fst _ _ _
    have hmm := hm T t₁ t₀ 1 1 a' a' ha'.symm ha'.symm
    rw [_root_.mul_one] at hmm
    have h2 : a' * a' = a' := hom_ext_of_cartesian h _ _ (by rw [← hmm, ha'])
    have h3 : a' = 1 := by simpa using h2
    rw [← ha', h3]
  refine ⟨one, ?_⟩
  intro T t₁ t₀ a a' haa
  have ht : t₁ ≫ s₁ = t₀ ≫ s₀ := by
    have w1 : a.left ≫ G.hom = t₁ := Over.w a
    have w0 : a'.left ≫ A.hom = t₀ := Over.w a'
    calc t₁ ≫ s₁ = (a.left ≫ G.hom) ≫ s₁ := by rw [w1]
      _ = (a.left ≫ e) ≫ q := by rw [Category.assoc, Category.assoc, he]
      _ = (a'.left ≫ i) ≫ q := by rw [haa]
      _ = (a'.left ≫ A.hom) ≫ s₀ := by rw [Category.assoc, Category.assoc, h.w]
      _ = t₀ ≫ s₀ := by rw [w0]
  have hw : ((a⁻¹).left ≫ e) ≫ q = t₀ ≫ s₀ := by
    rw [Category.assoc, he, ← Category.assoc, Over.w]; exact ht
  let b' : Over.mk t₀ ⟶ A := Over.homMk (h.lift _ t₀ hw) (by simp)
  have hb' : b'.left ≫ i = (a⁻¹).left ≫ e := h.lift_fst _ _ _
  have hmm := hm T t₁ t₀ a a⁻¹ a' b' haa hb'.symm
  rw [_root_.mul_inv_cancel] at hmm
  have h2 : a' * b' = 1 := hom_ext_of_cartesian h _ _ (by rw [← hmm, one T t₁ t₀ ht])
  have h3 : b' = a'⁻¹ := eq_inv_of_mul_eq_one_right h2
  rw [← h3, hb']

end GlobalTheory.Desc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpUnitsAndInversesAgreeOfLawsAgreeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grpUnits_and_inverses_agree_of_laws_agree : ∀ (S S₀ S₁ X : Scheme.{0}) (q : X ⟶ S) (s₀ : S₀ ⟶ S) (s₁ : S₁ ⟶ S) (A : Over S₀) [GrpObj A] (G : Over S₁) [GrpObj G] (i : A.left ⟶ X) (e : G.left ⟶ X), IsPullback i A.hom q s₀ → e ≫ q = G.hom ≫ s₁ → MulAgree G A e i → OneAgree s₁ s₀ G A e i ∧ ∀ (T : Scheme.{0}) (t₁ : T ⟶ S₁) (t₀ : T ⟶ S₀) (a : Over.mk t₁ ⟶ G) (a' : Over.mk t₀ ⟶ A), a.left ≫ e = a'.left ≫ i → (a⁻¹).left ≫ e = (a'⁻¹).left ≫ i := by
  first | exact @GlobalTheory.Desc.oneAgree_invAgree_of_mulAgree | exact GlobalTheory.Desc.oneAgree_invAgree_of_mulAgree | (intros; apply GlobalTheory.Desc.oneAgree_invAgree_of_mulAgree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentMorphismToLocalScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentMorphismToLocalScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
noncomputable section

namespace GlobalTheory.Desc

theorem exists_desc_specStalk : ∀ (R : Type) [CommRing R] [IsDomain R] (f : R), f ≠ 0 → ∀ (x : Sp R)
    (S₁ B Z B₀ B₁ : Scheme.{0}) (ξ' : S₁ ⟶ Spec ((Sp R).presheaf.stalk x)), Flat ξ' → Surjective ξ' →
    QuasiCompact ξ' → ∀ (pB : B ⟶ Sp R) (pZ : Z ⟶ Sp R), Flat pB → IsSeparated pZ →
    ∀ (φ₀ : B₀ ⟶ B) (q₀ : B₀ ⟶ Sp (Localization.Away f)) (u₀ : B₀ ⟶ Z) (φ₁ : B₁ ⟶ B) (q₁ : B₁ ⟶ S₁)
      (u₁ : B₁ ⟶ Z), IsPullback φ₀ q₀ pB (awayMap f) → IsPullback φ₁ q₁ pB (ξ' ≫ (Sp R).fromSpecStalk x) →
    u₁ ≫ pZ = φ₁ ≫ pB →
    (∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t₁ : T ⟶ B₁), t₀ ≫ φ₀ = t₁ ≫ φ₁ → t₀ ≫ u₀ = t₁ ≫ u₁) →
    ∃ u : Limits.pullback pB ((Sp R).fromSpecStalk x) ⟶ Z, u ≫ pZ = Limits.pullback.fst _ _ ≫ pB ∧
      ∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t : T ⟶ Limits.pullback pB ((Sp R).fromSpecStalk x)),
        t₀ ≫ φ₀ = t ≫ Limits.pullback.fst _ _ → t₀ ≫ u₀ = t ≫ u := by
  intro R _ _ f hf x S₁ B Z B₀ B₁ ξ' hξf hξs hξq pB pZ hpB hpZ φ₀ q₀ u₀ φ₁ q₁ u₁ h₀ h₁ hu₁ H
  have hs : Flat ((Sp R).fromSpecStalk x) := GenericExt.flat_fromSpecStalk _ x
  let π : B₁ ⟶ pullback pB ((Sp R).fromSpecStalk x) :=
    pullback.lift φ₁ (q₁ ≫ ξ') (by rw [h₁.w, Category.assoc])
  have hπ₁ : π ≫ pullback.fst _ _ = φ₁ := pullback.lift_fst _ _ _
  have hπ₂ : π ≫ pullback.snd _ _ = q₁ ≫ ξ' := pullback.lift_snd _ _ _
  have hsq : IsPullback π q₁ (pullback.snd pB ((Sp R).fromSpecStalk x)) ξ' := by
    refine IsPullback.of_right ?_ hπ₂ (IsPullback.of_hasPullback pB ((Sp R).fromSpecStalk x))
    rw [hπ₁]; exact h₁
  have : Flat π := MorphismProperty.of_isPullback hsq.flip hξf
  have : Surjective π := MorphismProperty.of_isPullback hsq.flip hξs
  have : QuasiCompact π := MorphismProperty.of_isPullback hsq.flip hξq
  have : Flat φ₁ := by rw [← hπ₁]; infer_instance
  have key : pullback.fst π π ≫ u₁ = pullback.snd π π ≫ u₁ := by
    let g : pullback π π ⟶ Sp R := pullback.fst π π ≫ φ₁ ≫ pB
    have hg : Flat g := inferInstance
    have hφ : pullback.fst π π ≫ φ₁ = pullback.snd π π ≫ φ₁ := by
      rw [← hπ₁, pullback.condition_assoc]
    have hAf : IsSchemeTheoreticallyDominant (awayMap f) :=
      schDom_spec_map _ (IsLocalization.injective (Localization.Away f)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hf))
    have hdom : IsSchemeTheoreticallyDominant (pullback.fst g (awayMap f)) :=
      IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback g (awayMap f)).flip
    refine ext_of_schDom pZ ?_ (pullback.fst g (awayMap f)) ?_
    · simp only [Category.assoc, hu₁]; exact (reassoc_of% hφ) pB
    · let t₀ : pullback g (awayMap f) ⟶ B₀ :=
        h₀.lift (pullback.fst g (awayMap f) ≫ pullback.fst π π ≫ φ₁) (pullback.snd g (awayMap f))
          (by simpa [g] using pullback.condition (f := g) (g := awayMap f))
      have ht₀ : t₀ ≫ φ₀ = pullback.fst g (awayMap f) ≫ pullback.fst π π ≫ φ₁ := h₀.lift_fst _ _ _
      have e₁ := H _ t₀ (pullback.fst g (awayMap f) ≫ pullback.fst π π) (by rw [ht₀, Category.assoc])
      have e₂ := H _ t₀ (pullback.fst g (awayMap f) ≫ pullback.snd π π) (by rw [ht₀, Category.assoc, hφ])
      simp only [Category.assoc] at e₁ e₂
      rw [← e₁, ← e₂]
  have hE : EffectiveEpi π := by
    set_option synthInstance.maxHeartbeats 400000 in infer_instance
  let u := EffectiveEpi.desc π u₁ (fun a b hab => by
    have := congrArg (pullback.lift a b hab ≫ ·) key
    simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this)
  have hu : π ≫ u = u₁ := EffectiveEpi.fac _ _ _
  have : Epi π := Flat.epi_of_flat_of_surjective π
  refine ⟨u, ?_, ?_⟩
  · rw [← cancel_epi π, reassoc_of% hu, hu₁, reassoc_of% hπ₁]
  · intro T t₀ t ht
    have : Epi (pullback.fst t π) := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (pullback.fst t π), pullback.condition_assoc, hu]
    have := H _ (pullback.fst t π ≫ t₀) (pullback.snd t π) (by
      rw [Category.assoc, ht, pullback.condition_assoc, hπ₁])
    simpa only [Category.assoc] using this

end GlobalTheory.Desc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentMorphismToLocalSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_descent_morphism_to_local_scheme : ∀ (R : Type) [CommRing R] [IsDomain R] (f : R), f ≠ 0 → ∀ (x : Sp R) (S₁ B Z B₀ B₁ : Scheme.{0}) (ξ' : S₁ ⟶ Spec ((Sp R).presheaf.stalk x)), Flat ξ' → Surjective ξ' → QuasiCompact ξ' → ∀ (pB : B ⟶ Sp R) (pZ : Z ⟶ Sp R), Flat pB → IsSeparated pZ → ∀ (φ₀ : B₀ ⟶ B) (q₀ : B₀ ⟶ Sp (Localization.Away f)) (u₀ : B₀ ⟶ Z) (φ₁ : B₁ ⟶ B) (q₁ : B₁ ⟶ S₁) (u₁ : B₁ ⟶ Z), IsPullback φ₀ q₀ pB (awayMap f) → IsPullback φ₁ q₁ pB (ξ' ≫ (Sp R).fromSpecStalk x) → u₁ ≫ pZ = φ₁ ≫ pB → (∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t₁ : T ⟶ B₁), t₀ ≫ φ₀ = t₁ ≫ φ₁ → t₀ ≫ u₀ = t₁ ≫ u₁) → ∃ u : Limits.pullback pB ((Sp R).fromSpecStalk x) ⟶ Z, u ≫ pZ = Limits.pullback.fst _ _ ≫ pB ∧ ∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t : T ⟶ Limits.pullback pB ((Sp R).fromSpecStalk x)), t₀ ≫ φ₀ = t ≫ Limits.pullback.fst _ _ → t₀ ≫ u₀ = t ≫ u := by
  first | exact @GlobalTheory.Desc.exists_desc_specStalk | exact GlobalTheory.Desc.exists_desc_specStalk | (intros; apply GlobalTheory.Desc.exists_desc_specStalk <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothNhdsOfSmoothOverLocalScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothNhdsOfSmoothOverLocalScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.Desc

theorem exists_smooth_nhds_of_smooth_fromSpecStalk :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Scheme.{0}) (p : P ⟶ Sp R) (x : Sp R) (V W : P.Opens), W ≤ V → Smooth (Limits.pullback.snd (V.ι ≫ p) ((Sp R).fromSpecStalk x)) → LocallyOfFiniteType (W.ι ≫ p) → ∀ z : P, z ∈ W → (p z).asIdeal ≤ x.asIdeal → ∃ W' : P.Opens, z ∈ W' ∧ W' ≤ W ∧ Smooth (W'.ι ≫ p) := by
  intro R _ _ P p x V W hWV hV hW z hz hle
  have : LocallyOfFinitePresentation (W.ι ≫ p) := inferInstance
  have : Flat ((Sp R).fromSpecStalk x) := GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk _ x
  have : SurjectiveOnStalks ((Sp R).fromSpecStalk x) := inferInstance
  have e : W.ι ≫ p = P.homOfLE hWV ≫ V.ι ≫ p := by simp
  have h1 : Smooth (Limits.pullback.snd (P.homOfLE hWV ≫ V.ι ≫ p) ((Sp R).fromSpecStalk x)) := by
    rw [← pullbackRightPullbackFstIso_inv_snd_snd]
    infer_instance
  have h2 : Smooth (Limits.pullback.snd (W.ι ≫ p) ((Sp R).fromSpecStalk x)) := by
    rw [e]; exact h1
  have hs : p z ⤳ x := (PrimeSpectrum.le_iff_specializes (R := R) _ _).1 hle
  obtain ⟨y, hy⟩ : p z ∈ Set.range ((Sp R).fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]; exact hs
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := W.ι ≫ p)
    (g := (Sp R).fromSpecStalk x) (⟨z, hz⟩ : W) y hy.symm
  have h3 := GlobalTheory.GenSpread.mem_smoothLocus_of_isPullback
    (IsPullback.of_hasPullback (W.ι ≫ p) ((Sp R).fromSpecStalk x)) w
  rw [hw] at h3
  have h4 : Smooth ((W.ι ≫ p).smoothLocus.ι ≫ W.ι ≫ p) := GlobalTheory.smooth_smoothLocus_ι_comp _
  refine ⟨W.ι ''ᵁ (W.ι ≫ p).smoothLocus, ⟨⟨z, hz⟩, h3, rfl⟩, W.ι_image_le _, ?_⟩
  rw [← Scheme.Hom.isoImage_inv_ι, Category.assoc, Category.assoc]
  infer_instance

end GlobalTheory.Desc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothNhdsOfSmoothOverLocalSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_nhds_of_smooth_over_local_scheme : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Scheme.{0}) (p : P ⟶ Sp R) (x : Sp R) (V W : P.Opens), W ≤ V → Smooth (Limits.pullback.snd (V.ι ≫ p) ((Sp R).fromSpecStalk x)) → LocallyOfFiniteType (W.ι ≫ p) → ∀ z : P, z ∈ W → (p z).asIdeal ≤ x.asIdeal → ∃ W' : P.Opens, z ∈ W' ∧ W' ≤ W ∧ Smooth (W'.ι ≫ p) := by
  first | exact @GlobalTheory.Desc.exists_smooth_nhds_of_smooth_fromSpecStalk | exact GlobalTheory.Desc.exists_smooth_nhds_of_smooth_fromSpecStalk | (intros; apply GlobalTheory.Desc.exists_smooth_nhds_of_smooth_fromSpecStalk <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenOfSaturatedLocalSchemeBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenOfSaturatedLocalSchemeBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem exists_open_of_saturated_stalkBaseChange : ∀ (S S₁ P : Scheme.{0}) (p : P ⟶ S) (x : S) (ξ' : S₁ ⟶ Spec (S.presheaf.stalk x)) (ξ : S₁ ⟶ S), ξ' ≫ S.fromSpecStalk x = ξ → Flat ξ' → Surjective ξ' → QuasiCompact ξ' → ∀ O : Set ↥(Limits.pullback p ξ), IsOpen O → (∀ w w' : ↥(Limits.pullback p ξ), Limits.pullback.fst p ξ w = Limits.pullback.fst p ξ w' → w ∈ O → w' ∈ O) → ∃ V : P.Opens, ∀ w : ↥(Limits.pullback p ξ), Limits.pullback.fst p ξ w ∈ V ↔ w ∈ O := by
  intro S S₁ P p x ξ' ξ hξ hfl hsu hqc O hO hsat
  subst hξ
  obtain ⟨π, hπ, hπ2⟩ : ∃ π : pullback p (ξ' ≫ S.fromSpecStalk x) ⟶ pullback p (S.fromSpecStalk x),
      π ≫ pullback.fst p (S.fromSpecStalk x) = pullback.fst p (ξ' ≫ S.fromSpecStalk x) ∧
      π ≫ pullback.snd p (S.fromSpecStalk x) = pullback.snd p (ξ' ≫ S.fromSpecStalk x) ≫ ξ' :=
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ ξ') (by rw [Category.assoc]; exact pullback.condition),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hsq : IsPullback π (pullback.snd p (ξ' ≫ S.fromSpecStalk x)) (pullback.snd p (S.fromSpecStalk x)) ξ' := by
    refine IsPullback.of_right ?_ hπ2 (IsPullback.of_hasPullback p (S.fromSpecStalk x))
    rw [hπ]
    exact IsPullback.of_hasPullback p (ξ' ≫ S.fromSpecStalk x)
  have : Flat π := MorphismProperty.of_isPullback (P := @Flat) hsq.flip hfl
  have : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hsu
  have : QuasiCompact π := MorphismProperty.of_isPullback (P := @QuasiCompact) hsq.flip hqc
  have hq := Flat.isQuotientMap_of_surjective π
  have hc : ∀ w, pullback.fst p (S.fromSpecStalk x) (π w) = pullback.fst p (ξ' ≫ S.fromSpecStalk x) w := by
    intro w; rw [← Scheme.Hom.comp_apply, hπ]
  have hpre : π ⁻¹' (π '' O) = O := by
    ext w; constructor
    · rintro ⟨w', hw', he⟩
      exact hsat w' w (by rw [← hc, ← hc, he]) hw'
    · intro hw; exact ⟨w, hw, rfl⟩
  have hopen : IsOpen (π '' O) := by
    rw [← hq.isOpen_preimage, hpre]; exact hO
  have hemb := IsPreimmersion.isEmbedding (pullback.fst p (S.fromSpecStalk x))
  obtain ⟨t, ht, hte⟩ := hemb.isInducing.isOpen_iff.1 hopen
  refine ⟨⟨t, ht⟩, fun w => ?_⟩
  change _ ∈ t ↔ _
  rw [← hc, ← Set.mem_preimage, hte, ← Set.mem_preimage, hpre]

end GlobalTheory.Desc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenOfSaturatedLocalSchemeBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_of_saturated_local_scheme_baseChange : ∀ (S S₁ P : Scheme.{0}) (p : P ⟶ S) (x : S) (ξ' : S₁ ⟶ Spec (S.presheaf.stalk x)) (ξ : S₁ ⟶ S), ξ' ≫ S.fromSpecStalk x = ξ → Flat ξ' → Surjective ξ' → QuasiCompact ξ' → ∀ O : Set ↥(Limits.pullback p ξ), IsOpen O → (∀ w w' : ↥(Limits.pullback p ξ), Limits.pullback.fst p ξ w = Limits.pullback.fst p ξ w' → w ∈ O → w' ∈ O) → ∃ V : P.Opens, ∀ w : ↥(Limits.pullback p ξ), Limits.pullback.fst p ξ w ∈ V ↔ w ∈ O := by
  first | exact @GlobalTheory.Desc.exists_open_of_saturated_stalkBaseChange | exact GlobalTheory.Desc.exists_open_of_saturated_stalkBaseChange | (intros; apply GlobalTheory.Desc.exists_open_of_saturated_stalkBaseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOfOpenBaseChangeEqPreimage
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOfOpenBaseChangeEqPreimage
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem isPullback_of_open_part_eq_preimage :
    ∀ (S S₁ P G : Scheme.{0}) (p : P ⟶ S) (s : S₁ ⟶ S) (e : G ⟶ P) (c : G ⟶ S₁) (hw : e ≫ p = c ≫ s), IsOpenImmersion (Limits.pullback.lift e c hw) → ∀ V : P.Opens, (∀ w : ↥(Limits.pullback p s), Limits.pullback.fst p s w ∈ V ↔ w ∈ Set.range (Limits.pullback.lift e c hw)) → ∃ e' : G ⟶ V.toScheme, e' ≫ V.ι = e ∧ IsPullback e' c (V.ι ≫ p) s := by
  intro S S₁ P G p s e c hw hl V hV
  have hlf : Limits.pullback.lift e c hw ≫ Limits.pullback.fst p s = e :=
    Limits.pullback.lift_fst _ _ _
  have hls : Limits.pullback.lift e c hw ≫ Limits.pullback.snd p s = c :=
    Limits.pullback.lift_snd _ _ _
  generalize Limits.pullback.lift e c hw = l at hl hV hlf hls
  have hr : Set.range e ⊆ Set.range V.ι := by
    rintro _ ⟨g, rfl⟩
    rw [Scheme.Opens.range_ι]
    have h := (hV (l g)).mpr ⟨g, rfl⟩
    rw [← Scheme.Hom.comp_apply, hlf] at h
    exact h
  have he' : IsOpenImmersion.lift V.ι e hr ≫ V.ι = e := IsOpenImmersion.lift_fac _ _ _
  generalize IsOpenImmersion.lift V.ι e hr = e' at he'
  have hcomm : e' ≫ V.ι ≫ p = c ≫ s := by rw [← Category.assoc, he', hw]
  have hk : ∀ t : PullbackCone (V.ι ≫ p) s, ∃ q : t.pt ⟶ G,
      q ≫ l = Limits.pullback.lift (t.fst ≫ V.ι) t.snd
        ((Category.assoc _ _ _).trans t.condition) := by
    intro t
    refine ⟨IsOpenImmersion.lift l _ ?_, IsOpenImmersion.lift_fac _ _ _⟩
    rintro _ ⟨x, rfl⟩
    refine (hV _).mp ?_
    rw [← Scheme.Hom.comp_apply, Limits.pullback.lift_fst, Scheme.Hom.comp_apply]
    exact (t.fst x).2
  choose q hq using hk
  refine ⟨e', he', ⟨hcomm⟩, ⟨PullbackCone.IsLimit.mk hcomm q ?_ ?_ ?_⟩⟩
  · intro t
    rw [← cancel_mono V.ι, Category.assoc, he', ← hlf, ← Category.assoc, hq,
      Limits.pullback.lift_fst]
  · intro t
    conv_lhs => rw [← hls]
    rw [← Category.assoc, hq, Limits.pullback.lift_snd]
  · intro t m h₁ h₂
    rw [← cancel_mono l, hq]
    apply Limits.pullback.hom_ext
    · rw [Category.assoc, hlf, Limits.pullback.lift_fst, ← h₁, Category.assoc, he']
    · rw [Category.assoc, hls, Limits.pullback.lift_snd, h₂]

end GlobalTheory.Desc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackOfOpenBaseChangeEqPreimageStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullback_of_open_baseChange_eq_preimage : ∀ (S S₁ P G : Scheme.{0}) (p : P ⟶ S) (s : S₁ ⟶ S) (e : G ⟶ P) (c : G ⟶ S₁) (hw : e ≫ p = c ≫ s), IsOpenImmersion (Limits.pullback.lift e c hw) → ∀ V : P.Opens, (∀ w : ↥(Limits.pullback p s), Limits.pullback.fst p s w ∈ V ↔ w ∈ Set.range (Limits.pullback.lift e c hw)) → ∃ e' : G ⟶ V.toScheme, e' ≫ V.ι = e ∧ IsPullback e' c (V.ι ≫ p) s := by
  first | exact @GlobalTheory.Desc.isPullback_of_open_part_eq_preimage | exact GlobalTheory.Desc.isPullback_of_open_part_eq_preimage | (intros; apply GlobalTheory.Desc.isPullback_of_open_part_eq_preimage <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSmoothGroupOverNbhd
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.Spread

theorem isPullback_sq {S U Z X : Scheme.{0}} {s : Z ⟶ S} {j : U ⟶ S} {p : X ⟶ U} {φ : X ⟶ Z}
    (h : IsPullback φ p s j) :
    IsPullback (pullback.map p p s s φ φ j h.w.symm h.w.symm) (pullback.fst p p ≫ p) (pullback.fst s s ≫ s) j := by
  have h₁ : IsPullback (pullback.map p p s s φ φ j h.w.symm h.w.symm) (pullback.fst p p) (pullback.fst s s) φ := by
    refine IsPullback.of_right (h₁₂ := pullback.snd s s) (v₁₃ := s) (h₂₂ := s) ?_ (pullback.lift_fst _ _ _)
      (IsPullback.of_hasPullback s s).flip
    rw [pullback.lift_snd, h.w]
    exact (IsPullback.of_hasPullback p p).flip.paste_horiz h
  exact h₁.paste_vert h

theorem lift_left_eq {S : Scheme.{0}} {T G : Over S} (a b : T ⟶ G) (t : T.left ⟶ pullback G.hom G.hom)
    (h₁ : t ≫ pullback.fst _ _ = a.left) (h₂ : t ≫ pullback.snd _ _ = b.left) : (lift a b).left = t := by
  apply pullback.hom_ext
  · exact (congrArg (fun z => z.left) (lift_fst a b)).trans h₁.symm
  · exact (congrArg (fun z => z.left) (lift_snd a b)).trans h₂.symm

theorem mul_left_eq {S : Scheme.{0}} {T G : Over S} [GrpObj G] (a b : T ⟶ G) (t : T.left ⟶ pullback G.hom G.hom)
    (h₁ : t ≫ pullback.fst _ _ = a.left) (h₂ : t ≫ pullback.snd _ _ = b.left) : (a * b).left = t ≫ (μ[G]).left := by
  rw [← lift_left_eq a b t h₁ h₂]; rfl

theorem inv_left_eq {S : Scheme.{0}} {T G : Over S} [GrpObj G] (a : T ⟶ G) : (a⁻¹).left = a.left ≫ (ι[G]).left := rfl

theorem one_left_eq {S T : Scheme.{0}} {G : Over S} [GrpObj G] (t : T ⟶ S) :
    (1 : Over.mk t ⟶ G).left = t ≫ (η[G]).left := by
  have : (toUnit (Over.mk t)).left = t := by simpa using Over.w (toUnit (Over.mk t))
  exact (show (1 : Over.mk t ⟶ G).left = (toUnit (Over.mk t)).left ≫ (η[G]).left from rfl).trans
    (congrArg (· ≫ (η[G]).left) this)

theorem exists_ext {R : Type} [CommRing R] [IsDomain R] {f : R} (hf : f ≠ 0) (x : Sp R) {S₁ B Z B₀ B₁ : Scheme.{0}}
    (ξ' : S₁ ⟶ Spec ((Sp R).presheaf.stalk x)) [Flat ξ'] [Surjective ξ'] [QuasiCompact ξ'] (pB : B ⟶ Sp R) (pZ : Z ⟶ Sp R)
    [Flat pB] [QuasiCompact pB] [QuasiSeparated pB] [IsSeparated pZ] [LocallyOfFinitePresentation pZ]
    {φ₀ : B₀ ⟶ B} {q₀ : B₀ ⟶ Sp (Localization.Away f)} (u₀ : B₀ ⟶ Z) {φ₁ : B₁ ⟶ B} {q₁ : B₁ ⟶ S₁} (u₁ : B₁ ⟶ Z)
    (h₀ : IsPullback φ₀ q₀ pB (awayMap f)) (h₁ : IsPullback φ₁ q₁ pB (ξ' ≫ (Sp R).fromSpecStalk x))
    (w₀ : u₀ ≫ pZ = φ₀ ≫ pB) (w₁ : u₁ ≫ pZ = φ₁ ≫ pB)
    (ag : ∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t₁ : T ⟶ B₁), t₀ ≫ φ₀ = t₁ ≫ φ₁ → t₀ ≫ u₀ = t₁ ≫ u₁) :
    ∃ g : R, g ∉ x.asIdeal ∧ ∀ (Y : Scheme.{0}) (a : Y ⟶ B), (∀ y : Y, g ∉ (pB (a y)).asIdeal) →
      ∃ u' : Y ⟶ Z, u' ≫ pZ = a ≫ pB ∧
        ∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t : T ⟶ Y), t₀ ≫ φ₀ = t ≫ a → t₀ ≫ u₀ = t ≫ u' := by
  obtain ⟨u, hu, hu'⟩ := GlobalTheory.T.exists_descent_morphism_to_local_scheme R f hf x S₁ B Z B₀ B₁ ξ' ‹_› ‹_› ‹_› pB pZ ‹_› ‹_› φ₀ q₀ u₀ φ₁ q₁ u₁ h₀ h₁ w₁ ag
  exact GlobalTheory.T.exists_spread_morphism_basicOpen_agree_flat R x B Z B₀ pB pZ ‹_› ‹_› ‹_› ‹_› ‹_› φ₀ u₀
    (MorphismProperty.of_isPullback (P := @Flat) h₀.flip inferInstance) w₀ u hu hu'

theorem not_mem_of_dvd {R : Type} [CommRing R] {g g' : R} (hg : g' ∣ g) {Y B : Scheme.{0}} {a : Y ⟶ B} {pB : B ⟶ Sp R}
    {c : Y ⟶ Sp (Localization.Away g)} (w : a ≫ pB = c ≫ awayMap g) (y : Y) : g' ∉ (pB (a y)).asIdeal := by
  rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
  intro h
  have h' : algebraMap R (Localization.Away g) g ∈ (c y).asIdeal := Ideal.mem_of_dvd (awayMap g (c y)).asIdeal hg h
  exact (c y).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (IsLocalization.Away.algebraMap_isUnit g))

theorem exists_grp_near : ∀ (R : Type) [CommRing R] [IsDomain R] (f : R), f ≠ 0 → ∀ (x : Sp R) (S₁ X : Scheme.{0}) (ξ' : S₁ ⟶ Spec ((Sp R).presheaf.stalk x)), Flat ξ' → Surjective ξ' → QuasiCompact ξ' → ∀ q : X ⟶ Sp R, Smooth q → QuasiCompact q → IsSeparated q → ∀ (A : Over (Sp (Localization.Away f))) [GrpObj A], IsCommMonObj A → ∀ (G : Over S₁) [GrpObj G] (i : A.left ⟶ X) (e : G.left ⟶ X), IsPullback i A.hom q (awayMap f) → IsPullback e G.hom q (ξ' ≫ (Sp R).fromSpecStalk x) → MulAgree G A e i → ∃ g : R, g ∉ x.asIdeal ∧ ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ X), IsPullback h H.hom q (awayMap g) ∧ MulAgree H A h i := by
  intro R _ _ f hf x S₁ X ξ' _ _ _ q _ _ _ A _ hc G _ i e hi he hm
  obtain ⟨hone, hinv⟩ := GlobalTheory.T.grpUnits_and_inverses_agree_of_laws_agree _ _ _ X q _ _ A G i e hi he.w hm
  obtain ⟨g₁, hg₁, H₁⟩ := exists_ext hf x ξ' (pullback.fst q q ≫ q) q ((μ[A]).left ≫ i) ((μ[G]).left ≫ e)
    (isPullback_sq hi) (isPullback_sq he)
    (by rw [(isPullback_sq hi).w, Category.assoc, hi.w, Over.w_assoc]; rfl)
    (by rw [(isPullback_sq he).w, Category.assoc, he.w, Over.w_assoc]; rfl)
    (fun T t₀ t₁ h => by
      have k₁ := congrArg (· ≫ pullback.fst q q) h
      have k₂ := congrArg (· ≫ pullback.snd q q) h
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd] at k₁ k₂
      have := hm T (t₁ ≫ pullback.fst _ _ ≫ G.hom) (t₀ ≫ pullback.fst _ _ ≫ A.hom)
        (Over.homMk (t₁ ≫ pullback.fst _ _) (by simp)) (Over.homMk (t₁ ≫ pullback.snd _ _) (by simp [pullback.condition]))
        (Over.homMk (t₀ ≫ pullback.fst _ _) (by simp)) (Over.homMk (t₀ ≫ pullback.snd _ _) (by simp [pullback.condition]))
        (by simpa using k₁.symm) (by simpa using k₂.symm)
      rw [mul_left_eq _ _ t₁ rfl rfl, mul_left_eq _ _ t₀ rfl rfl] at this
      exact (Category.assoc _ _ _).symm.trans (this.symm.trans (Category.assoc _ _ _)))
  obtain ⟨g₂, hg₂, H₂⟩ := exists_ext hf x ξ' q q ((ι[A]).left ≫ i) ((ι[G]).left ≫ e) hi he
    (by rw [Category.assoc, hi.w, Over.w_assoc]) (by rw [Category.assoc, he.w, Over.w_assoc])
    (fun T t₀ t₁ h => by
      have := hinv T (t₁ ≫ G.hom) (t₀ ≫ A.hom) (Over.homMk t₁ rfl) (Over.homMk t₀ rfl) h.symm
      rw [inv_left_eq, inv_left_eq] at this
      exact (Category.assoc _ _ _).symm.trans (this.symm.trans (Category.assoc _ _ _)))
  obtain ⟨g₃, hg₃, H₃⟩ := exists_ext hf x ξ' (𝟙 _) q ((η[A]).left ≫ i) ((η[G]).left ≫ e)
    (IsPullback.id_vert (awayMap f)) (IsPullback.id_vert (ξ' ≫ (Sp R).fromSpecStalk x))
    (by rw [Category.assoc, hi.w, Over.w_assoc]; simp) (by rw [Category.assoc, he.w, Over.w_assoc]; simp)
    (fun T t₀ t₁ h => by
      have := hone T t₁ t₀ h.symm
      rw [one_left_eq, one_left_eq] at this
      exact (Category.assoc _ _ _).symm.trans (this.symm.trans (Category.assoc _ _ _)))
  let g := g₁ * g₂ * g₃
  have hg : g ∉ x.asIdeal := fun h => by
    rcases x.isPrime.mem_or_mem h with h | h
    · exact (x.isPrime.mem_or_mem h).elim hg₁ hg₂
    · exact hg₃ h
  let H : Over (Sp (Localization.Away g)) := Over.mk (pullback.snd q (awayMap g))
  let h : H.left ⟶ X := pullback.fst q (awayMap g)
  have hH : IsPullback h H.hom q (awayMap g) := IsPullback.of_hasPullback _ _
  obtain ⟨m, hm₁, hm₂⟩ := H₁ _ _ (not_mem_of_dvd ⟨g₂ * g₃, mul_assoc _ _ _⟩ (isPullback_sq hH).w)
  obtain ⟨n, hn₁, hn₂⟩ := H₂ _ _ (not_mem_of_dvd ⟨g₁ * g₃, by simp only [g]; ring⟩ hH.w)
  obtain ⟨o, ho₁, ho₂⟩ := H₃ _ (awayMap g) (not_mem_of_dvd (c := 𝟙 _) ⟨g₁ * g₂, mul_comm _ _⟩ (by simp))
  have L : ∀ (Y : Over (Sp (Localization.Away g))) (u : Y.left ⟶ X), u ≫ q = Y.hom ≫ awayMap g →
      ∃ v : Y ⟶ H, v.left ≫ h = u :=
    fun Y u w => ⟨Over.homMk (hH.lift u Y.hom w) (hH.lift_snd _ _ _), hH.lift_fst _ _ _⟩
  obtain ⟨m', hm'⟩ := L (H ⊗ H) m (hm₁.trans (isPullback_sq hH).w)
  obtain ⟨n', hn'⟩ := L H n (hn₁.trans hH.w)
  obtain ⟨o', ho'⟩ := L (𝟙_ _) o (ho₁.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  obtain ⟨_, hfin⟩ := GlobalTheory.T.grpObj_of_law_unit_inverse_agree_away R f g hf X q inferInstance ‹_› A hc i hi H h hH m' n' o'
    (fun T t₁ t₀ a b a' b' k₁ k₂ => by
      have := hm₂ T (lift a' b').left (lift a b).left (by
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.lift_fst]
          exact (Category.assoc _ _ _).symm.trans ((congrArg (fun z => z.left ≫ i) (lift_fst a' b')).trans
            (k₁.symm.trans ((congrArg (fun z => z.left ≫ h) (lift_fst a b)).symm.trans (Category.assoc _ _ _))))
        · simp only [Category.assoc, pullback.lift_snd]
          exact (Category.assoc _ _ _).symm.trans ((congrArg (fun z => z.left ≫ i) (lift_snd a' b')).trans
            (k₂.symm.trans ((congrArg (fun z => z.left ≫ h) (lift_snd a b)).symm.trans (Category.assoc _ _ _)))))
      rw [Over.comp_left, Category.assoc, hm']
      exact this.symm.trans (Category.assoc _ _ _).symm)
    (fun T t₁ t₀ a a' k => by
      rw [Over.comp_left, Category.assoc, hn', inv_left_eq, Category.assoc]
      exact (hn₂ T a'.left a.left k.symm).symm)
    (fun T t₁ t₀ k => by
      rw [one_left_eq]
      exact (congrArg (t₁ ≫ ·) ho').trans ((ho₂ T t₀ t₁ k.symm).symm.trans (Category.assoc _ _ _).symm))
  exact ⟨g, hg, H, inferInstance, h, hH, hfin⟩

theorem fst_mem_U_iff_range (σ : Setup) (E : Emb σ) (hC : σ.Common) (x : Sp σ.R)
    (hw : E.emb x ≫ E.p = (σ.C x).G.hom ≫ spMap (σ.ρ x)) (w : ↥(pullback E.p (spMap (σ.ρ x)))) :
    pullback.fst E.p (spMap (σ.ρ x)) w ∈ E.U ↔ w ∈ Set.range (pullback.lift (E.emb x) (σ.C x).G.hom hw) := by
  constructor
  · rintro ⟨x', y', hy', e⟩
    obtain ⟨Ω, _, s, t', o, hst, hs, ht⟩ :=
      Sat.exists_field_pt (pullback.fst E.p (spMap (σ.ρ x))) (E.emb x') w y' e.symm
    obtain ⟨w', -⟩ := E.openIn x'
    obtain ⟨t, h1, h2⟩ := (Sat.transfer σ E hC x x' Ω (s ≫ pullback.snd _ _) (t' ≫ (σ.C x').G.hom) o
      (by rw [Scheme.Hom.comp_apply, ht]; exact hy')
      (by rw [Category.assoc, Category.assoc, ← pullback.condition, ← w', reassoc_of% hst])).2 t' rfl
    have h3 : t ≫ pullback.lift (E.emb x) (σ.C x).G.hom hw = s := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, h2, hst]
      · rw [Category.assoc, pullback.lift_snd, h1]
    exact ⟨t o, by rw [← Scheme.Hom.comp_apply, h3, hs]⟩
  · rintro ⟨y, rfl⟩
    refine (Emb.fst_mem_U_iff σ E hC x _).2 ⟨y, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
    · rw [← Scheme.Hom.comp_apply, pullback.lift_snd]

theorem smooth_of_forall {P S : Scheme.{0}} (p : P ⟶ S) (V : P.Opens)
    (h : ∀ z ∈ V, ∃ W : P.Opens, z ∈ W ∧ Smooth (W.ι ≫ p)) : Smooth (V.ι ≫ p) := by
  choose W hW hs using h
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @Smooth) (Q := RingHom.Smooth)
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @Smooth) (fun z : V => V.ι ⁻¹ᵁ W z.1 z.2) ?_ fun z => ?_
  · rw [eq_top_iff]
    intro z _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨z, hW z.1 z.2⟩
  · have := hs z.1 z.2
    rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]
    infer_instance

theorem isPullback_of_mono {A V P S S₀ : Scheme.{0}} {i : A ⟶ V} {j : V ⟶ P} [Mono j] {a : A ⟶ S₀} {p : P ⟶ S}
    {s : S₀ ⟶ S} (h : IsPullback (i ≫ j) a p s) : IsPullback i a (j ≫ p) s := by
  have h₁ : IsPullback i (𝟙 A) j (i ≫ j) :=
    ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun c => c.snd)
      (fun c => by rw [← cancel_mono j, Category.assoc, c.condition]) (fun c => by simp)
      (fun c m _ h2 => by simpa using h2)⟩⟩
  simpa using h₁.paste_vert h

theorem exists_open (σ : Setup) (E : Emb σ) (hC : σ.Common) (x : Sp σ.R)
    (ξ' : Sp (σ.C x).R ⟶ Spec ((Sp σ.R).presheaf.stalk x)) (hξ : ξ' ≫ (Sp σ.R).fromSpecStalk x = spMap (σ.ρ x))
    [Flat ξ'] [Surjective ξ'] [QuasiCompact ξ'] :
    ∃ V : E.P.Opens, Smooth (V.ι ≫ E.p) ∧ QuasiCompact (V.ι ≫ E.p) ∧ Set.range E.ιA ⊆ (V : Set E.P) ∧
      (∀ w, pullback.fst E.p (spMap (σ.ρ x)) w ∈ E.U → pullback.fst E.p (spMap (σ.ρ x)) w ∈ V) ∧
      ∃ e : (σ.C x).G.left ⟶ V.toScheme, e ≫ V.ι = E.emb x ∧ IsPullback e (σ.C x).G.hom (V.ι ≫ E.p) (spMap (σ.ρ x)) := by
  obtain ⟨hw, hop⟩ := E.openIn x
  have sat := fst_mem_U_iff_range σ E hC x hw
  have hx : spMap (σ.ρ x) (closedPoint _) = x := by rw [← σ.hρ]; exact (σ.C x).centre
  obtain ⟨V', hV'⟩ := GlobalTheory.T.exists_open_of_saturated_local_scheme_baseChange _ _ _ E.p x ξ' _ hξ ‹_› ‹_› ‹_› _
    (pullback.lift (E.emb x) (σ.C x).G.hom hw).isOpenEmbedding.isOpen_range
    (fun w w' h hm => by rw [← sat] at hm ⊢; rwa [← h])
  obtain ⟨e', he', pb'⟩ := GlobalTheory.T.isPullback_of_open_baseChange_eq_preimage _ _ _ _ E.p _ _ _ hw hop V' hV'
  have hG : Smooth (σ.C x).G.hom := (σ.C x).semi.smooth
  have hGq : QuasiCompact (σ.C x).G.hom := (σ.C x).semi.quasiCompact
  have hA : Smooth σ.A.hom := σ.ab.smooth
  have hAp : IsProper σ.A.hom := σ.ab.proper
  have hιA : IsOpenImmersion E.ιA := MorphismProperty.of_isPullback (P := @IsOpenImmersion) E.cartA.flip inferInstance
  have hsm : Smooth (pullback.snd (V'.ι ≫ E.p) ((Sp σ.R).fromSpecStalk x)) := by
    rw [← hξ] at pb'
    have sq : IsPullback (pullback.lift e' ((σ.C x).G.hom ≫ ξ') (by rw [pb'.w, Category.assoc])) (σ.C x).G.hom
        (pullback.snd (V'.ι ≫ E.p) ((Sp σ.R).fromSpecStalk x)) ξ' :=
      IsPullback.of_right (by rwa [pullback.lift_fst]) (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    exact MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      sq.flip ⟨⟨‹_›, ‹_›⟩, ‹_›⟩ hG
  have hemb : ∀ y, pullback.fst E.p (spMap (σ.ρ x)) (pullback.lift (E.emb x) (σ.C x).G.hom hw y) = E.emb x y :=
    fun y => by rw [← Scheme.Hom.comp_apply, pullback.lift_fst]
  have loc : ∀ y : (σ.C x).G.left, ∃ W : E.P.Opens, IsAffineOpen W ∧ E.emb x y ∈ W ∧ W ≤ V' ∧ Smooth (W.ι ≫ E.p) := by
    intro y
    have h1 : E.emb x y ∈ V' := by rw [← hemb, hV']; exact ⟨y, rfl⟩
    have h2 : (E.p (E.emb x y)).asIdeal ≤ x.asIdeal := by
      rw [← Scheme.Hom.comp_apply, hw, Scheme.Hom.comp_apply]
      conv_rhs => rw [← hx]
      exact Ideal.comap_mono (f := σ.ρ x) (le_maximalIdeal ((σ.C x).G.hom y).isPrime.ne_top)
    obtain ⟨W₁, a₁, b₁, c₁⟩ := GlobalTheory.T.locallyOfFiniteType_near_generisation_of_point σ.R σ.f E.P σ.A.left E.p E.ιA σ.A.hom E.cartA inferInstance x V' inferInstance _ h1 h2
    obtain ⟨W₂, a₂, b₂, c₂⟩ := GlobalTheory.T.exists_smooth_nhds_of_smooth_over_local_scheme σ.R E.P E.p x V' W₁ b₁ hsm c₁ _ a₁ h2
    obtain ⟨W, a, b, c : W ≤ W₂⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp E.P.isBasis_affineOpens a₂
    refine ⟨W, a, b, c.trans (b₂.trans b₁), ?_⟩
    rw [← E.P.homOfLE_ι c, Category.assoc]
    infer_instance
  choose W hWa hWm hWle hWs using loc
  have : CompactSpace (Sp (σ.C x).R) := inferInstanceAs (CompactSpace (PrimeSpectrum _))
  have : CompactSpace (σ.C x).G.left := QuasiCompact.compactSpace_of_compactSpace (σ.C x).G.hom
  have : CompactSpace σ.A.left := QuasiCompact.compactSpace_of_compactSpace σ.A.hom
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun y : (σ.C x).G.left => ((E.emb x ⁻¹ᵁ W y : (σ.C x).G.left.Opens) : Set (σ.C x).G.left))
    (fun y => (E.emb x ⁻¹ᵁ W y).isOpen) (fun y _ => Set.mem_iUnion.2 ⟨y, hWm y⟩)
  let V : E.P.Opens := (⨆ y : s, W y) ⊔ E.ιA.opensRange
  have hmem : ∀ z, z ∈ V ↔ (∃ y : s, z ∈ W y) ∨ z ∈ Set.range E.ιA := fun z => by
    simp only [V, TopologicalSpace.Opens.mem_sup, TopologicalSpace.Opens.mem_iSup]; rfl
  have hV : ∀ w, pullback.fst E.p (spMap (σ.ρ x)) w ∈ V ↔ w ∈ Set.range (pullback.lift (E.emb x) (σ.C x).G.hom hw) := by
    intro w
    rw [hmem]
    constructor
    · rintro (⟨y, hy⟩ | ⟨a, ha⟩)
      · exact (hV' w).1 (hWle _ hy)
      · obtain ⟨v, hv₁, hv₂⟩ := Scheme.exists_preimage_of_isPullback (σ.cart x) a (pullback.snd E.p (spMap (σ.ρ x)) w) (by
          rw [← E.cartA.w, Scheme.Hom.comp_apply, ha, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
            pullback.condition])
        refine (sat w).1 ((Emb.fst_mem_U_iff σ E hC x w).2 ⟨(σ.V x).ι v, ?_, ?_⟩)
        · rw [← Scheme.Hom.comp_apply, ← E.onV, Scheme.Hom.comp_apply, hv₁, ha]
        · rw [← Scheme.Hom.comp_apply, hv₂]
    · rintro ⟨y, rfl⟩
      obtain ⟨y', hy', h⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
      exact Or.inl ⟨⟨y', hy'⟩, by rw [hemb]; exact h⟩
  refine ⟨V, smooth_of_forall _ _ fun z hz => ?_, ?_, fun z hz => (hmem z).2 (Or.inr hz),
    fun w h => (hV w).2 ((sat w).1 h), GlobalTheory.T.isPullback_of_open_baseChange_eq_preimage _ _ _ _ E.p _ _ _ hw hop V hV⟩
  · rcases (hmem z).1 hz with ⟨y, hy⟩ | h
    · exact ⟨_, hy, hWs _⟩
    · refine ⟨E.ιA.opensRange, h, ?_⟩
      rw [← E.ιA.isoOpensRange_inv_comp, Category.assoc, E.cartA.w]
      infer_instance
  · have hc : IsCompact (V : Set E.P) := by
      simp only [V, TopologicalSpace.Opens.coe_sup, TopologicalSpace.Opens.coe_iSup]
      exact (isCompact_iUnion fun y => (hWa _).isCompact).union (isCompact_range E.ιA.continuous)
    have : CompactSpace V.toScheme := isCompact_iff_compactSpace.1 hc
    exact (quasiCompact_iff_compactSpace _).2 this

end GlobalTheory.Desc.Spread

namespace GlobalTheory.Desc


open Spread in
theorem Emb.exists_locGrp : ∀ (σ : Setup) (E : Emb σ), σ.Common → ∀ x : Sp σ.R, ∃ g : σ.R, g ∉ x.asIdeal ∧ ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ E.P), E.LocGrp g H h ∧ ∀ z : E.P, z ∈ E.U → x.asIdeal ≤ (E.p z).asIdeal → (E.p z).asIdeal ≤ x.asIdeal → z ∈ Set.range h := by
  intro σ E hC x
  have hx : spMap (σ.ρ x) (closedPoint _) = x := by rw [← σ.hρ]; exact (σ.C x).centre
  obtain ⟨ξ', hξ, _, _, _⟩ := GlobalTheory.T.exists_faithfullyFlat_factor_through_local_scheme _ (σ.C x).R (spMap (σ.ρ x)) x hx
    ((HasRingHomProperty.Spec_iff (P := @Flat)).2 (σ.flat x))
  obtain ⟨V, hs, hq, hA, hU, e, he, pb⟩ := exists_open σ E hC x ξ' hξ
  have := E.sep
  have hιA : IsOpenImmersion E.ιA := MorphismProperty.of_isPullback (P := @IsOpenImmersion) E.cartA.flip inferInstance
  let i : σ.A.left ⟶ V.toScheme := IsOpenImmersion.lift V.ι E.ιA (by rwa [Scheme.Opens.range_ι])
  have hi : i ≫ V.ι = E.ιA := IsOpenImmersion.lift_fac _ _ _
  have pA : IsPullback i σ.A.hom (V.ι ≫ E.p) (awayMap σ.f) := isPullback_of_mono (hi ▸ E.cartA)
  obtain ⟨g, hg, H, _, h, ph, hm⟩ := exists_grp_near σ.R σ.f σ.hf x _ _ ξ' ‹_› ‹_› ‹_› (V.ι ≫ E.p) hs hq inferInstance σ.A σ.ab.comm
    (σ.C x).G i e pA (by rwa [hξ]) (fun T t₁ t₂ a b a' b' h₁ h₂ => by
      rw [← cancel_mono V.ι, Category.assoc, Category.assoc, he, hi]
      refine GlobalTheory.T.chart_grpLaw_agrees_with_abelian_scheme_law σ E x T t₁ t₂ a b a' b' ?_ ?_
      · rw [← he, ← hi, reassoc_of% h₁]
      · rw [← he, ← hi, reassoc_of% h₂])
  have : IsOpenImmersion h := MorphismProperty.of_isPullback (P := @IsOpenImmersion) ph.flip inferInstance
  refine ⟨g, hg, H, inferInstance, h ≫ V.ι, ⟨MorphismProperty.of_isPullback (P := @Smooth) ph hs,
    MorphismProperty.of_isPullback (P := @QuasiCompact) ph hq, inferInstance, by rw [Category.assoc, ph.w],
    fun T t₁ t₂ a b a' b' h₁ h₂ => ?_⟩, fun z hz h₁ h₂ => ?_⟩
  · rw [← hi, ← Category.assoc, ← Category.assoc, cancel_mono] at h₁ h₂ ⊢
    exact hm T t₁ t₂ a b a' b' h₁ h₂
  · have hz' : E.p z = x := PrimeSpectrum.ext (le_antisymm h₂ h₁)
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := E.p) (g := spMap (σ.ρ x)) z (closedPoint _)
      (hz'.trans hx.symm)
    have hV : z ∈ V := hw ▸ hU w (hw ▸ hz)
    obtain ⟨u, hu⟩ : x ∈ Set.range (awayMap g) := by
      change x ∈ Set.range (PrimeSpectrum.comap (algebraMap σ.R (Localization.Away g)))
      rw [PrimeSpectrum.localization_away_comap_range _ g]
      exact hg
    obtain ⟨v, hv, -⟩ := Scheme.exists_preimage_of_isPullback ph (⟨z, hV⟩ : V.toScheme) u (by
      rw [hu]; exact (Scheme.Hom.comp_apply _ _ _).trans hz')
    exact ⟨v, by rw [Scheme.Hom.comp_apply, hv]; rfl⟩

end GlobalTheory.Desc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSmoothGroupOverNbhdStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_smooth_group_over_nbhd : ∀ (σ : Setup) (E : Emb σ), σ.Common → ∀ x : Sp σ.R, ∃ g : σ.R, g ∉ x.asIdeal ∧ ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ E.P), E.LocGrp g H h ∧ ∀ z : E.P, z ∈ E.U → x.asIdeal ≤ (E.p z).asIdeal → (E.p z).asIdeal ≤ x.asIdeal → z ∈ Set.range h := by
  first | exact @GlobalTheory.Desc.Emb.exists_locGrp | exact GlobalTheory.Desc.Emb.exists_locGrp | (intros; apply GlobalTheory.Desc.Emb.exists_locGrp <;> assumption)
end
