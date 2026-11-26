module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationEqIffExpansionEq
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RelAmpleIffVeryAmpleBy
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsKernelVector

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijOfOnto
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ExpansionCriterion

private lemma sum_smul_sum_smul_eq_sum_mul_smul {K S J : Type} [Field K] {Λ : J → Type} [∀ j, CommRing (Λ j)]
    (ρ : ∀ j, K →+* Λ j) (f : S → ∀ j, Λ j) {n : ℕ} (b t : Fin n → S)
    (D : Matrix (Fin n) (Fin n) K) (hD : ∀ k j, f (t k) j = ∑ i, ρ j (D k i) * f (b i) j)
    (c : Fin n → K) (j : J) :
    ∑ k, ρ j (c k) * f (t k) j = ∑ i, ρ j (Matrix.vecMul c D i) * f (b i) j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hD, Matrix.vecMul, dotProduct, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

theorem total_of_onto {K S V J : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    {Λ : J → Type} [∀ j, CommRing (Λ j)] (ρ : ∀ j, K →+* Λ j) (f : S → ∀ j, Λ j)
    (E : S → V → Prop) {n : ℕ} (hn : Module.finrank K V = n) (b : Fin n → S)
    (hb₁ : ∀ c : Fin n → K, ∃ s : S, ∀ j, f s j = ∑ i, ρ j (c i) * f (b i) j)
    (hb₂ : ∀ s : S, ∃ c : Fin n → K, ∀ j, f s j = ∑ i, ρ j (c i) * f (b i) j)
    (hlin : ∀ (t : Fin n → S) (F : Fin n → V) (c : Fin n → K) (s : S), (∀ i, E (t i) (F i)) →
      (∀ j, f s j = ∑ i, ρ j (c i) * f (t i) j) → E s (∑ i, c i • F i))
    (hfun : ∀ s F F', E s F → E s F' → F = F')
    (hon : ∀ F, ∃ s, E s F) (s : S) : ∃ F, E s F := by
  classical

  let v := Module.finBasisOfFinrankEq K V hn
  choose t ht using fun k => hon (v k)
  choose D hD using fun k => hb₂ (t k)
  have key := sum_smul_sum_smul_eq_sum_mul_smul ρ f b t (D : Matrix (Fin n) (Fin n) K) hD

  have hinj : Function.Injective (Matrix.vecMulLinear (D : Matrix (Fin n) (Fin n) K)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hc' : Matrix.vecMul c (D : Matrix (Fin n) (Fin n) K) = 0 := hc
    obtain ⟨s₀, hs₀⟩ := hb₁ 0
    have h1 : E s₀ (∑ k, c k • v k) :=
      hlin t (fun k => v k) c s₀ ht (fun j => by rw [key c j, hc', hs₀ j])
    have h0 : E s₀ (∑ k, (0 : Fin n → K) k • v k) :=
      hlin t (fun k => v k) 0 s₀ ht (fun j => by rw [hs₀ j]; simp)
    have hsum : ∑ k, c k • v k = 0 := by simpa using hfun _ _ _ h1 h0
    funext k
    exact Fintype.linearIndependent_iff.mp v.linearIndependent c hsum k
  obtain ⟨a, ha⟩ := hb₂ s
  obtain ⟨c, hc⟩ := (LinearMap.injective_iff_surjective.mp hinj) a
  have hc' : Matrix.vecMul c (D : Matrix (Fin n) (Fin n) K) = a := hc
  exact ⟨_, hlin t (fun k => v k) c s ht (fun j => by rw [key c j, hc']; exact ha j)⟩

noncomputable def scalRes {R : Type} [CommRing R] {Y : Scheme.{0}}
    (p : Y ⟶ Spec (CommRingCat.of R)) (W : Y.Opens) : R →+* Γ(Y, W) :=
  ((Y.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom.comp p.appTop.hom).comp
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem expBij_of_onto : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ), 1 ≤ k → Module.Finite (FractionRing R) (Fam D.toPre (FractionRing R) k) → Module.finrank (FractionRing R) (Fam D.toPre (FractionRing R) k) = k ^ A.g → (∀ F : Fam D.toPre (FractionRing R) k, ∃ s : U.SecK k, U.Expands k s F) → U.ExpBij k := by
  intro hS R _ _ I hR D A G _ _ _ U k hk _ hrank honto
  obtain ⟨b, hb₁, hb₂⟩ := GlobalTheory.GenericSectionBasis.exists_secK_basis hS R I D A G U k hk
  have resTop_scal_lemma_2 : ∀ (W : (pullback G.hom (jK R)).Opens) (r : FractionRing R),
      resTop W (scal (pullback.snd G.hom (jK R)) r) = scalRes (pullback.snd G.hom (jK R)) W r :=
    fun W r => (GlobalTheory.ExpandsLinear.scalOn_apply _ W r).trans rfl

  have huniq := GlobalTheory.T.uniformisation_eq_iff_expansion_eq R I hR D A G U k
  have htot : ∀ s : U.SecK k, ∃ F, U.Expands k s F := by
    intro s
    refine total_of_onto (K := FractionRing R) (f := fun (s : U.SecK k) j => s.f j)
      (ρ := fun j => scalRes (pullback.snd G.hom (jK R)) _) (E := U.Expands k) hrank b
      (fun c => ?_) (fun s => ?_) (fun t F c s ht hs => ?_)
      (fun s F F' h h' => (huniq s s F F' h h').mp rfl) honto s
    · obtain ⟨s, hs⟩ := hb₁ c
      exact ⟨s, fun j => by simpa only [resTop_scal_lemma_2] using hs j⟩
    · obtain ⟨c, hc, _⟩ := hb₂ s
      exact ⟨c, fun j => by simpa only [resTop_scal_lemma_2] using hc j⟩
    · exact GlobalTheory.expands_linear R I hR D A G U k _ t F c s ht
        (fun j => by simpa only [resTop_scal_lemma_2] using hs j)

  refine ⟨fun s => ?_, fun F => ?_⟩
  · obtain ⟨F, hF⟩ := htot s
    exact ⟨F, hF, fun F' hF' => (huniq s s F' F hF' hF).mp rfl⟩
  · obtain ⟨s, hs⟩ := honto F
    exact ⟨s, hs, fun s' hs' => (huniq s' s F F hs' hs).mpr rfl⟩

end GlobalTheory.ExpansionCriterion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FormallyUnramifiedOfIsFinite
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace FiniteOnePoint

theorem isIso_of_formallyUnramified {K : Type} [Field K] [IsAlgClosed K] {X : Scheme.{0}}
    (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f] [FormallyUnramified f]
    (s : Spec (CommRingCat.of K) ⟶ X) (hs : s ≫ f = 𝟙 _)
    (h : ∀ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ → p = s) : IsIso f := by
  haveI : MorphismProperty.HasOfPostcompProperty @IsOpenImmersion
      (MorphismProperty.diagonal @IsOpenImmersion) :=
    MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.2 le_rfl
  have ho : IsOpenImmersion s :=
    MorphismProperty.of_postcomp (W := @IsOpenImmersion)
      (W' := MorphismProperty.diagonal @IsOpenImmersion) s f
      (inferInstanceAs (IsOpenImmersion (pullback.diagonal f))) (by rw [hs]; infer_instance)
  have := LocallyOfFiniteType.jacobsonSpace f
  have hsurj : Surjective s := ⟨fun x => by
    by_contra hx
    obtain ⟨c, hc, hc'⟩ := nonempty_inter_closedPoints (Z := (Set.range s)ᶜ) ⟨x, hx⟩
      s.isOpenEmbedding.isOpen_range.isClosed_compl.isLocallyClosed
    refine hc ⟨IsLocalRing.closedPoint K, ?_⟩
    rw [← h _ (pointOfClosedPoint_comp f c hc')]
    exact pointOfClosedPoint_apply f c hc' _⟩
  have : IsIso s := (isIso_iff_isOpenImmersion_and_surjective s).2 ⟨ho, hsurj⟩
  have : IsIso (s ≫ f) := by rw [hs]; infer_instance
  exact IsIso.of_isIso_comp_left s f

theorem formallyUnramified_of_isFinite {K : Type} [Field K] [CharZero K]
    (G : Over (Spec (CommRingCat.of K))) [GrpObj G] [IsCommMonObj G] (hf : IsFinite G.hom) :
    FormallyUnramified G.hom := by
  obtain ⟨N, hN, h⟩ := FiniteFlatKilled.main K G hf inferInstance
  have hu : IsUnit (N : Γ(Spec (CommRingCat.of K), ⊤)) := by
    have h1 : IsUnit (N : K) := (Nat.cast_ne_zero.2 (by omega)).isUnit
    simpa using h1.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have h2 := formallyUnramified_mulA _ G N hu
  have h3 : (mulA G N).left = G.hom ≫ η[G].left := by
    rw [show mulA G N = 1 from h, Hom.one_def]
    rfl
  rw [h3] at h2
  exact FormallyUnramified.of_comp G.hom η[G].left

theorem main : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (H : Over S) (j : H ⟶ B), Mono j → IsFinite H.hom → (∃ y : 𝟙_ _ ⟶ H, y ≫ j = 1) → (∀ (T : Over S) (x y : T ⟶ H), ∃ z : T ⟶ H, z ≫ j = (x ≫ j) * (y ≫ j)⁻¹) → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (t : Spec (CommRingCat.of K) ⟶ S), (∀ x : Over.mk t ⟶ H, x ≫ j = 1) → ∀ (T : Over S) (_ : T ⟶ Over.mk t) (y : T ⟶ H), y ≫ j = 1 := by
  intro S B _ _ H j hj hf ⟨e, he⟩ hsub K _ _ _ t hpt T a y
  have he' : ∀ T : Over S, (toUnit T ≫ e) ≫ j = 1 := fun T => by
    rw [Category.assoc, he, MonObj.comp_one]
  have hinv : ∀ (T : Over S) (x : T ⟶ H), ∃ z : T ⟶ H, z ≫ j = (x ≫ j)⁻¹ := fun T x => by
    obtain ⟨z, hz⟩ := hsub T (toUnit T ≫ e) x
    exact ⟨z, by rw [hz, he', _root_.one_mul]⟩
  obtain ⟨i, hi⟩ := hinv H (𝟙 H)
  obtain ⟨w, hw⟩ := hinv (H ⊗ H) (snd H H)
  obtain ⟨m, hm⟩ := hsub (H ⊗ H) (fst H H) w
  obtain ⟨_, _⟩ := ReducedSubgroup.exists_grpObj_of_mono j e m i
    (by rw [he, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp])
    (by
      rw [hm, hw, inv_inv, Hom.mul_def]
      congr 1)
    (by rw [hi, Category.id_comp, Hom.inv_def])
  haveI : IsCommMonObj H :=
    ⟨by rw [← cancel_mono j, Category.assoc, IsMonHom.mul_hom,
      ← BraidedCategory.braiding_naturality_assoc, IsCommMonObj.mul_comm]⟩
  have hfin : IsFinite (pullback.snd H.hom t) := inferInstance
  have hunr : FormallyUnramified (pullback.snd H.hom t) :=
    formallyUnramified_of_isFinite ((Over.pullback t).obj H) hfin
  have hiso : IsIso (pullback.snd H.hom t) := by
    refine isIso_of_formallyUnramified _
      (pullback.lift (toUnit (Over.mk t) ≫ e).left (𝟙 _)
        ((Over.w _).trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _) fun p hp => ?_
    let x : Over.mk t ⟶ H := Over.homMk (p ≫ pullback.fst H.hom t) (by
      change (p ≫ pullback.fst H.hom t) ≫ H.hom = t
      rw [Category.assoc, pullback.condition, reassoc_of% hp])
    have hx : x = toUnit _ ≫ e := by rw [← cancel_mono j, hpt, he']
    refine pullback.hom_ext ?_ ?_
    · rw [pullback.lift_fst, ← hx]
      rfl
    · rw [pullback.lift_snd, hp]
  have key : ∀ y₁ y₂ : T ⟶ H, y₁ = y₂ := fun y₁ y₂ => by
    have h : pullback.lift y₁.left a.left ((Over.w y₁).trans (Over.w a).symm) =
        pullback.lift (f := H.hom) (g := t) y₂.left a.left ((Over.w y₂).trans (Over.w a).symm) := by
      rw [← cancel_mono (pullback.snd H.hom t)]
      exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm
    ext1
    exact (pullback.lift_fst _ _ _).symm.trans
      ((h =≫ pullback.fst H.hom t).trans (pullback.lift_fst _ _ _))
  rw [key y (toUnit T ≫ e), he']

end FiniteOnePoint

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusCoordinatesCompatOfTorusCompat
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusCoordinatesCompatOfTorusCompat
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory
namespace CoordReduction

theorem exists_ratio {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)}
    {ε : K → ℤ} (hφ : ∀ k, φ k = φ' k) {u : LB.Gen (LB.LinComb L φ ε)} {u' : LB.Gen (LB.LinComb L φ' ε)}
    (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ ρ : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      val u r z J = gm r z ⊤ ρ * val u' r z J := by
  obtain ⟨t, -, hv⟩ := exists_gen hL (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_ (Fintype.prod_empty _).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, hφ, mul_inv_cancel])
    (LB.mulGen L _ _ _ _ u (LB.invGen L _ _ u')) (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ hu'))
  have le : (⊤ : Y.Opens) ≤ LB.wchart L (PEmpty.elim : PEmpty → (Y ⟶ X)) PEmpty.elim := fun _ _ =>
    Set.mem_iInter.2 fun k => k.elim
  refine ⟨res le (t.s PEmpty.elim), fun Z r z J hJ => ?_⟩
  have h := hv Z r z J hJ
  rw [val_mul hJ, val_inv, val_of t r z J PEmpty.elim (fun k => k.elim)] at h
  exact mul_inv_eq_iff_eq_mul.1 ((gm_res r z le trivial _).trans h).symm

theorem gm_char_comp {S S' Z : Scheme.{0}} {X : Type} [AddCommGroup X]
    (β : (splitTorus S' X).left ⟶ (splitTorus S X).left) (χ : X)
    (h : β.appTop.hom (charUnit S X χ).val = (charUnit S' X χ).val) (τ : Z ⟶ (splitTorus S' X).left) (z : Z) :
    gm (τ ≫ β) z ⊤ (charUnit S X χ) = gm τ z ⊤ (charUnit S' X χ) :=
  (gm_pull τ β z ⊤ trivial _).symm.trans (congrArg (gm τ z ⊤) (Units.ext h))

section Abstract

variable {X S S' : Scheme.{0}} {L : LB X} {H : Over S} {H' : Over S'} [GrpObj H] [GrpObj H'] {f : S' ⟶ S}
  {F : H'.left ⟶ H.left} (hp : IsGrpPullback H' H f F) {K : Type} [Fintype K] {φ : K → (H.left ⟶ X)} {ε : K → ℤ}
  (t : LB.Gen (LB.LinComb L φ ε))
include hp

theorem val_unit_pull
    (h : ∀ (Z : Over S) (z : Z.left) (J), Good L z J → val t (1 : Z ⟶ H).left z J = 1)
    {Z : Over S'} {z : Z.left} {J} (hJ : Good L z J) : val t ((1 : Z ⟶ H').left ≫ F) z J = 1 := by
  have e := hp.2 Z 1 1 (pushPt hp.1.w 1) (pushPt hp.1.w 1) rfl rfl
  rw [_root_.mul_one] at e
  have h1 : pushPt hp.1.w (1 : Z ⟶ H') = 1 :=
    left_eq_mul.1 (Over.OverMorphism.ext (f := pushPt hp.1.w 1) e.symm)
  have h2 := h (Over.mk (Z.hom ≫ f)) z J hJ
  rw [← h1] at h2
  exact h2

theorem val_torus_pull {M : Type} [AddCommGroup M] {i : splitTorus S M ⟶ H} {i' : splitTorus S' M ⟶ H'}
    (hi : TorusCompat f F i' i) (χ : M)
    (h : ∀ (Z : Over S) (z : Z.left) (J), Good L z J → ∀ (τ : Z ⟶ splitTorus S M) (a : Z ⟶ H),
      val t ((τ ≫ i) * a).left z J = gm τ.left z ⊤ (charUnit S M χ) * val t a.left z J)
    {Z : Over S'} {z : Z.left} {J} (hJ : Good L z J) (τ : Z ⟶ splitTorus S' M) (a : Z ⟶ H') :
    val t (((τ ≫ i') * a).left ≫ F) z J = gm τ.left z ⊤ (charUnit S' M χ) * val t (a.left ≫ F) z J := by
  obtain ⟨β, hβ, hχ, hβi⟩ := hi
  have e := hp.2 Z (τ ≫ i') a (pushPt hβ τ ≫ i) (pushPt hp.1.w a)
    ((Category.assoc _ _ _).trans ((congrArg (τ.left ≫ ·) hβi).trans (Category.assoc _ _ _).symm)) rfl
  have h2 := h (Over.mk (Z.hom ≫ f)) z J hJ (pushPt hβ τ) (pushPt hp.1.w a)
  exact (congrArg (fun r => val t r z J) e).symm.trans
    (h2.trans (congrArg₂ (· * ·) (gm_char_comp β χ (hχ χ) τ.left z) rfl))

end Abstract

theorem isGrpPullback_trans {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R)))
    [GrpObj G] :
    IsGrpPullback (thickObj R I e G) (thickObj R I (e + 1) G) (thickTrans R I e) (thickMap R I e G) :=
  (isGrpPullback_pullback G (thick R I (e + 1))).cancel
    ((isGrpPullback_pullback G (thick R I e)).congr (thickTrans_comp R I e).symm
      ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).symm) (pullback.lift_snd _ _ _)

end CoordReduction

open CoordReduction in
theorem gtCoord_compat_of_torusCompat : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g' : GtCoord I D (e + 1) G), thickMap R I e G ≫ g'.pG.left = g.pG.left → TorusCompat (thickTrans R I e) (thickMap R I e G) g.i g'.i → ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g'.t χ) (thickMap R I e G)) (g.t χ) := by
  intro hG R _ _ I D e G _ _ g g' hq hi χ
  obtain ⟨ρ, hρ⟩ := exists_ratio D.P.isLB (LevelCompat.thickMap_Oφ g g' hq χ)
    (DVR.pullGen_isGen _ _ _ _ (g'.t_gen χ) (thickMap R I e G)) (g.t_gen χ)
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.P.L z J →
      val (g'.t χ) (r ≫ thickMap R I e G) z J = gm r z ⊤ ρ * val (g.t χ) r z J := fun Z r z J hJ =>
    (val_pull hJ _ _ _).symm.trans (hρ Z r z J hJ)
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  have h1 : ρ.val = 1 := by
    refine eq_one_of_fibre_const_of_section hG _ _ _ (TLinPf.isAb_pullback _ _ D.P.isAb) g.q _
      (1 : 𝟙_ _ ⟶ thickObj R I e G) (fun Z a b hab => ?_) ?_
    · obtain ⟨τ, hτ⟩ := TorusCoord.exists_torus g a b hab
      refine TorusCoord.appTop_eq_of_gm _ _ ρ fun z => ?_
      obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z
      have k := key _ a.left z J hJ
      have t₁ := val_torus_pull (isGrpPullback_trans I e G) (g'.t χ) hi χ
        (fun _ _ _ hJ τ a => TorusCoord.val_torus g' χ hJ τ a) hJ τ b
      have t₂ := TorusCoord.val_torus g χ hJ τ b
      rw [← hτ] at t₁ t₂
      rw [t₁, t₂, key _ b.left z J hJ, mul_left_comm, ← _root_.mul_assoc, ← _root_.mul_assoc] at k
      exact (mul_right_cancel (mul_right_cancel k)).symm
    · have h : Units.map (1 : 𝟙_ _ ⟶ thickObj R I e G).left.appTop.hom.toMonoidHom ρ = 1 := by
        refine unit_ext fun z _ => ?_
        obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z
        have k := key _ (1 : 𝟙_ _ ⟶ thickObj R I e G).left z J hJ
        rw [val_unit_pull (isGrpPullback_trans I e G) (g'.t χ) (fun _ _ _ hJ => TorusCoord.val_unit g' χ hJ) hJ,
          TorusCoord.val_unit g χ hJ, _root_.mul_one] at k
        exact (gm_top _ z ρ).symm.trans (k.symm.trans (map_one _).symm)
      exact congrArg Units.val h
  have h2 : ρ = 1 := Units.ext h1
  refine corr_of_val D.P.isLB fun y J hJ => ?_
  rw [hρ _ _ y J hJ, h2, map_one, _root_.one_mul]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusCoordinatesCompatOfTorusCompatStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusCoordinates_compat_of_torus_compat : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (g' : GtCoord I D (e + 1) G), thickMap R I e G ≫ g'.pG.left = g.pG.left → TorusCompat (thickTrans R I e) (thickMap R I e G) g.i g'.i → ∀ χ, LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ (g'.t χ) (thickMap R I e G)) (g.t χ) := by
  first | exact @GlobalTheory.gtCoord_compat_of_torusCompat | exact GlobalTheory.gtCoord_compat_of_torusCompat | (intros; apply GlobalTheory.gtCoord_compat_of_torusCompat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HomEqOfThickeningPoints
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.isProper_tensorObj_over {S : Scheme.{0}} {Z B : Over S} (hZ : IsProper Z.hom)
    (hB : IsProper B.hom) : IsProper (Z ⊗ B).hom := by
  simp only [Over.tensorObj_hom]
  infer_instance

attribute [local instance] Over.cartesianMonoidalCategory in
private lemma hom_ext_of_thickenings (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] {X B : Over (Spec (CommRingCat.of V))} [IsProper X.hom]
    [IsProper B.hom] (f g : X ⟶ B)
    (h : ∀ (e : ℕ) (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
      (t : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ X), t ≫ f = t ≫ g) :
    f = g := by
  refine _root_.GlobalTheory.hom_eq_of_thickenings_of_isProper V (IsLocalRing.maximalIdeal V) ?_ X B f g ?_
  · rw [IsLocalRing.jacobson_eq_maximalIdeal]
    exact bot_ne_top
  · intro e
    exact congrArg Over.Hom.left (h e (_root_.ReciprocityTheory.ChartRestriction.G.Out.thickObj V _ e X) (_root_.ReciprocityTheory.ChartRestriction.G.Out.fstG _ e X))

attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.grpObj_of_thickenings : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback (Y e) (Y (e + 1)) (_root_.ReciprocityTheory.ChartRestriction.G.Out.thickTrans V _ e) (β e)) → ∀ (B : Over (Spec (CommRingCat.of V))) (b : ∀ e, (Y e).left ⟶ B.left) [IsProper B.hom], (∀ e, IsPullback (b e) (Y e).hom B.hom (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e)) → (∀ e, β e ≫ b (e + 1) = b e) → ∀ (mu : B ⊗ B ⟶ B) (io : B ⟶ B) (un : 𝟙_ _ ⟶ B), (∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))) (x y : T ⟶ Y e) (x₀ y₀ : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ B), x₀.left = x.left ≫ b e → y₀.left = y.left ≫ b e → (lift x₀ y₀ ≫ mu).left = (x * y).left ≫ b e ∧ (x₀ ≫ io).left = (x⁻¹).left ≫ b e ∧ (toUnit (Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e)) ≫ un).left = (1 : T ⟶ Y e).left ≫ b e) → ∃ _ : GrpObj B, (∀ e, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback (Y e) B (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick V _ e) (b e)) ∧ ((∀ e, IsCommMonObj (Y e)) → IsCommMonObj B) := by
  intro V _ _ _ Y _ β _ B b _ hpb _ mu io un hY
  have lft : ∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
      (u : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ B),
      ∃ x : T ⟶ Y e, u.left = x.left ≫ b e := by
    intro e T u
    refine ⟨Over.homMk ((hpb e).lift u.left T.hom (by simpa using Over.w u))
      ((hpb e).lift_snd _ _ _), ?_⟩
    simp
  have hmul : ∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
      (u v : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ B) (x y : T ⟶ Y e),
      u.left = x.left ≫ b e → v.left = y.left ≫ b e → (lift u v ≫ mu).left = (x * y).left ≫ b e :=
    fun e T u v x y hu hv => (hY e T x y u v hu hv).1
  have hinv : ∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1)))))
      (u : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ B) (x : T ⟶ Y e),
      u.left = x.left ≫ b e → (u ≫ io).left = x⁻¹.left ≫ b e :=
    fun e T u x hu => (hY e T x x u u hu hu).2.1
  have hone : ∀ e (T : Over (Spec (CommRingCat.of (V ⧸ (IsLocalRing.maximalIdeal V) ^ (e + 1))))),
      (toUnit (Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e)) ≫ un).left =
        (1 : T ⟶ Y e).left ≫ b e := by
    intro e T
    obtain ⟨u, hu⟩ : ∃ u : Over.mk (T.hom ≫ _root_.ReciprocityTheory.ChartRestriction.G.Out.thick V (IsLocalRing.maximalIdeal V) e) ⟶ B,
        u.left = (1 : T ⟶ Y e).left ≫ b e :=
      ⟨Over.homMk ((1 : T ⟶ Y e).left ≫ b e) (by
        simp only [Over.mk_hom, Category.assoc, (hpb e).w]
        rw [← Category.assoc, Over.w]), rfl⟩
    exact (hY e T 1 1 u u hu hu).2.2
  have hB2 : IsProper (B ⊗ B).hom := _root_.GlobalTheory.isProper_tensorObj_over inferInstance inferInstance
  have hB3 : IsProper ((B ⊗ B) ⊗ B).hom := _root_.GlobalTheory.isProper_tensorObj_over hB2 inferInstance
  have hB1 : IsProper (B ⊗ 𝟙_ _).hom :=
    _root_.GlobalTheory.isProper_tensorObj_over inferInstance (by simp; infer_instance)
  have hB1' : IsProper (𝟙_ _ ⊗ B).hom :=
    _root_.GlobalTheory.isProper_tensorObj_over (by simp; infer_instance) inferInstance
  letI : MonObj B :=
    { one := un
      mul := mu
      one_mul := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T (t ≫ snd _ _)
        have ht : t = lift (t ≫ fst _ _) (t ≫ snd _ _) := by
          apply CartesianMonoidalCategory.hom_ext <;> simp
        rw [ht, toUnit_unique (t ≫ fst _ _) (toUnit _)]
        simp only [lift_whiskerRight_assoc, lift_leftUnitor_hom]
        ext
        rw [hmul e T _ _ 1 x (hone e T) hx, _root_.one_mul, hx]
      mul_one := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T (t ≫ fst _ _)
        have ht : t = lift (t ≫ fst _ _) (t ≫ snd _ _) := by
          apply CartesianMonoidalCategory.hom_ext <;> simp
        rw [ht, toUnit_unique (t ≫ snd _ _) (toUnit _)]
        simp only [lift_whiskerLeft_assoc, lift_rightUnitor_hom]
        ext
        rw [hmul e T _ _ x 1 hx (hone e T), _root_.mul_one, hx]
      mul_assoc := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T (t ≫ fst _ _ ≫ fst _ _)
        obtain ⟨y, hy⟩ := lft e T (t ≫ fst _ _ ≫ snd _ _)
        obtain ⟨z, hz⟩ := lft e T (t ≫ snd _ _)
        have ht : t = lift (lift (t ≫ fst _ _ ≫ fst _ _) (t ≫ fst _ _ ≫ snd _ _)) (t ≫ snd _ _) := by
          apply CartesianMonoidalCategory.hom_ext <;>
            [apply CartesianMonoidalCategory.hom_ext; skip] <;> simp
        rw [ht]
        simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc]
        ext
        rw [hmul e T _ _ (x * y) z (hmul e T _ _ x y hx hy) hz,
          hmul e T _ _ x (y * z) hx (hmul e T _ _ y z hy hz), _root_.mul_assoc] }
  letI : GrpObj B :=
    { inv := io
      left_inv := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T t
        simp only [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
        ext
        refine (hmul e T _ _ x⁻¹ x (hinv e T t x hx) hx).trans ?_
        rw [inv_mul_cancel, ← hone e T]
        rfl
      right_inv := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T t
        simp only [comp_lift_assoc, Category.comp_id, comp_toUnit_assoc]
        ext
        refine (hmul e T _ _ x x⁻¹ hx (hinv e T t x hx)).trans ?_
        rw [mul_inv_cancel, ← hone e T]
        rfl }
  refine ⟨this, fun e => ⟨hpb e, fun T x y x₀ y₀ hx hy => hmul e T x₀ y₀ x y hx hy⟩, fun hc => ?_⟩
  exact
    { mul_comm := by
        refine hom_ext_of_thickenings V _ _ fun e T t => ?_
        obtain ⟨x, hx⟩ := lft e T (t ≫ fst _ _)
        obtain ⟨y, hy⟩ := lft e T (t ≫ snd _ _)
        have ht : t = lift (t ≫ fst _ _) (t ≫ snd _ _) := by
          apply CartesianMonoidalCategory.hom_ext <;> simp
        rw [ht]
        simp only [lift_braiding_hom_assoc]
        ext
        have := hc e
        refine (hmul e T _ _ y x hy hx).trans ?_
        rw [_root_.mul_comm]
        exact (hmul e T _ _ x y hx hy).symm }

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SquareOfCubical
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.Square

section General
variable {X Y : Scheme.{0}} {L : LB X} {K K' K'' : Type} [Fintype K] [Fintype K'] [Fintype K'']

private theorem map_zpow_zpow {M N : Type} [Group M] [Group N] (F : M →* N) (x : M) (n e : ℤ) :
    F (x ^ n) ^ e = F x ^ (n * e) := by
  rw [map_zpow, ← zpow_mul]

theorem linComb_pw (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (n : ℤ) :
    LB.LinComb (pw L n) φ ε = LB.LinComb L φ (fun k => n * ε k) := by
  unfold LB.LinComb GlobalTheory.AbLaw.pw
  congr 1
  funext j j'
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [map_zpow]
  exact map_zpow_zpow _ _ _ _

private theorem sameSum_of_prod_pow_eq' {K₁ K₂ : Type} [Fintype K₁] [Fintype K₂] {φ₁ : K₁ → (Y ⟶ X)} {ε₁ : K₁ → ℤ}
    {φ₂ : K₂ → (Y ⟶ X)} {ε₂ : K₂ → ℤ}
    (h : ∀ (U : Type) [CommGroup U] (f : (Y ⟶ X) → U), ∏ k, f (φ₁ k) ^ ε₁ k = ∏ k, f (φ₂ k) ^ ε₂ k) :
    LB.SameSum φ₁ ε₁ φ₂ ε₂ := by
  classical
  intro ψ
  have e := congrArg Multiplicative.toAdd
    (h (Multiplicative ℤ) (fun χ => Multiplicative.ofAdd (if χ = ψ then (1 : ℤ) else 0)))
  simp only [toAdd_prod, toAdd_zpow, toAdd_ofAdd, smul_eq_mul, mul_ite, mul_zero] at e
  convert e <;> simp

theorem triv_mul (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {φ'' : K'' → (Y ⟶ X)} {ε'' : K'' → ℤ} (h₁ : Triv (LB.LinComb L φ ε)) (h₂ : Triv (LB.LinComb L φ' ε'))
    (h : ∀ (U : Type) [CommGroup U] (f : (Y ⟶ X) → U),
      (∏ k, f (φ k) ^ ε k) * ∏ k, f (φ' k) ^ ε' k = ∏ k, f (φ'' k) ^ ε'' k) : Triv (LB.LinComb L φ'' ε'') := by
  obtain ⟨t₁, ht₁⟩ := h₁
  obtain ⟨t₂, ht₂⟩ := h₂
  have hs : LB.SameSum (Sum.elim φ φ') (Sum.elim ε ε') φ'' ε'' := sameSum_of_prod_pow_eq' fun U _ f => by
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr]
    exact h U f
  obtain ⟨t, ht, -⟩ := DVR.gen_transport hL hs (LB.mulGen L φ ε φ' ε' t₁ t₂)
    (DVR.mulGen_isGen L φ ε φ' ε' t₁ t₂ ht₁ ht₂)
  exact ⟨t, ht⟩

theorem triv_inv {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Triv (LB.LinComb L φ ε)) :
    Triv (LB.LinComb L φ fun k => -ε k) := by
  obtain ⟨t, ht⟩ := h
  exact ⟨LB.invGen L φ ε t, DVR.invGen_isGen L φ ε t ht⟩

end General

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B] {L : RigLB B}
  {A : Type} [CommRing A] [IsLocalRing A] {t : Spec (CommRingCat.of A) ⟶ S}

omit [IsCommMonObj B] in
theorem triv_const {K : Type} [Fintype K] (x : K → (Over.mk t ⟶ B)) (ε : K → ℤ) :
    Triv (LB.LinComb L.L (fun k => (fst (Over.mk t) B ≫ x k).left) ε) := by
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := A) L.L L.isLB (fun k => (x k).left) ε
  exact ⟨LB.pullGen L.L (fun k => (x k).left) ε e (fst (Over.mk t) B).left,
    DVR.pullGen_isGen L.L _ ε e he _⟩

private theorem translPt_eq_fst_comp_mul_snd {T : Over S} (w : T ⟶ B) : translPt B w = (fst T B ≫ w) * snd T B := by
  unfold translPt
  rw [Hom.mul_def]

private theorem over_comp_mul {T T' : Over S} (f : T' ⟶ T) (g h : T ⟶ B) : f ≫ (g * h) = (f ≫ g) * (f ≫ h) := by
  rw [Hom.mul_def, Hom.mul_def, ← Category.assoc, comp_lift]

private theorem over_comp_one {T T' : Over S} (f : T' ⟶ T) : f ≫ (1 : T ⟶ B) = 1 := by
  simp [Hom.one_def]

theorem triv_square (c : CubicalStr B L) (x y : Over.mk t ⟶ B) :
    Triv (LB.LinComb L.L (K := Fin 4) ![(translPt B (x * y)).left, (snd (Over.mk t) B).left, (translPt B x).left,
      (translPt B y).left] ![1, 1, -1, -1]) := by
  have h₁ : Triv (LB.LinComb L.L (fun k => (lift (fst (Over.mk t) B ≫ x)
      (lift (fst (Over.mk t) B ≫ y) (snd (Over.mk t) B))).left ≫ thφ B (x3 B) k) thε) :=
    ⟨LB.pullGen L.L (thφ B (x3 B)) thε c.t _, DVR.pullGen_isGen L.L _ _ c.t c.isGen _⟩
  have h₂ := triv_const (L := L) (t := t) (K := Fin 4) ![x * y, x, y, 1] ![1, -1, -1, 1]
  refine triv_mul L.isLB h₁ h₂ fun U _ f => ?_
  rw [Geo.Tor.prod_cub]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
    zpow_one, zpow_neg]
  simp only [translPt_eq_fst_comp_mul_snd, over_comp_mul, over_comp_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem triv_pow (c : CubicalStr B L) (r : ℕ) (x : Over.mk t ⟶ B) :
    Triv (LB.LinComb L.L (K := Fin 3) ![(translPt B (x ^ r)).left, (translPt B x).left, (snd (Over.mk t) B).left]
      ![1, -r, r - 1]) := by
  induction r with
  | zero =>
    have h₀ := triv_const (L := L) (t := t) (K := Fin 0) ![] ![]
    refine triv_mul L.isLB h₀ h₀ fun U _ f => ?_
    rw [pow_zero, translPt_eq_fst_comp_mul_snd, over_comp_one, _root_.one_mul]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, _root_.mul_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    push_cast
    module
  | succ r ih =>
    have hs := triv_square c (x ^ r) x
    refine triv_mul L.isLB hs ih fun U _ f => ?_
    rw [pow_succ]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, _root_.mul_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow]
    push_cast
    module

theorem square_of_cubical : ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B] (L : RigLB B) (_ : CubicalStr B L) (A : Type) [CommRing A] [IsLocalRing A] (t : Spec (CommRingCat.of A) ⟶ S), (∀ x y : Over.mk t ⟶ B, Triv (LB.LinComb L.L (K := Fin 4) ![(translPt B (x * y)).left, (snd (Over.mk t) B).left, (translPt B x).left, (translPt B y).left] ![1, 1, -1, -1])) ∧ ∀ (r : ℕ) (x : Over.mk t ⟶ B), Triv (translDiff B (pw L.L r) x) ↔ Triv (translDiff B L.L (x ^ r)) := by
  intro S B _ _ L c A _ _ t
  refine ⟨fun x y => triv_square c x y, fun r x => ?_⟩
  have hP := triv_pow c r x
  unfold translDiff
  rw [linComb_pw]
  simp only [← Hom.mul_def]
  simp only [translPt_eq_fst_comp_mul_snd] at hP
  constructor
  · intro h
    refine triv_mul L.isLB h hP fun U _ f => ?_
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    module
  · intro h
    refine triv_mul L.isLB h (triv_inv hP) fun U _ f => ?_
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow, ofMul_one]
    module

end GlobalTheory.Square
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CyclicIdeal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU.SecCyclic
open GlobalTheory.AbLaw.Seesaw

theorem coker_equiv {R : Type} [CommRing R] {a b : ℕ} (D : Matrix (Fin b) (Fin a) R) (v₀ : Fin a → R)
    (k : Fin a) (hk : IsUnit (v₀ k))
    (hker : ∀ (R' : Type) [CommRing R'] (g : R →+* R'),
      ∀ w, (D.map g).mulVec w = 0 → ∃ c : R', w = c • (g ∘ v₀)) :
    Nonempty (((Fin a → R) ⧸ LinearMap.range D.transpose.mulVecLin) ≃ₗ[R]
      (R ⧸ Ideal.span (Set.range (D.mulVec v₀)))) := by
  classical
  set N := LinearMap.range D.transpose.mulVecLin with hN
  set I := Ideal.span (Set.range (D.mulVec v₀)) with hI
  have hrow : ∀ i, ∑ j, D i j • N.mkQ (Pi.single j 1) = 0 := fun i => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_smul, ← map_sum]
    refine (Submodule.Quotient.mk_eq_zero N).2 ⟨Pi.single i 1, ?_⟩
    funext j
    simp [Pi.single_apply, Finset.sum_apply]
  obtain ⟨c, hc⟩ := hker (TrivSqZeroExt R ((Fin a → R) ⧸ N)) (TrivSqZeroExt.inlHom R ((Fin a → R) ⧸ N))
    (fun j => TrivSqZeroExt.inr (N.mkQ (Pi.single j 1))) (by
      funext i
      change ∑ j, TrivSqZeroExt.inl (D i j) * TrivSqZeroExt.inr (N.mkQ (Pi.single j 1)) = (0 : TrivSqZeroExt R ((Fin a → R) ⧸ N))
      have := congrArg (TrivSqZeroExt.inrHom R ((Fin a → R) ⧸ N)) (hrow i)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_zero] at this
      exact (Finset.sum_congr rfl fun j _ => TrivSqZeroExt.inl_mul_inr _ _).trans this)
  have he : ∀ j, N.mkQ (Pi.single j 1) = v₀ j • c.snd := fun j => by
    have := congrArg TrivSqZeroExt.snd (congrFun hc j)
    change _ = (c * TrivSqZeroExt.inl (v₀ j)).snd at this
    rw [_root_.mul_comm, TrivSqZeroExt.inl_mul_eq_smul, TrivSqZeroExt.snd_smul] at this
    exact this
  have hx : ∀ x : Fin a → R, N.mkQ x = (x ⬝ᵥ v₀) • c.snd := fun x => by
    have : x = ∑ j, x j • (Pi.single j 1 : Fin a → R) := by
      funext j
      simp [Pi.single_apply, Finset.sum_apply]
    conv_lhs => rw [this]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, he, smul_smul, dotProduct, Finset.sum_smul]
  have hIq : ∀ r ∈ I, r • c.snd = 0 := fun r hr => by
    refine Submodule.span_induction (p := fun r _ => r • c.snd = 0) ?_ (zero_smul _ _) ?_ ?_ hr
    · rintro _ ⟨i, rfl⟩
      rw [← hrow i]
      simp only [he, smul_smul, Matrix.mulVec, dotProduct, Finset.sum_smul]
    · intro x y _ _ h₁ h₂
      rw [add_smul, h₁, h₂, add_zero]
    · intro s x _ h
      rw [smul_eq_mul, mul_smul, h, smul_zero]
  let φ : (Fin a → R) →ₗ[R] R ⧸ I := I.mkQ ∘ₗ (dotProductBilin R R).flip v₀
  have hφ : ∀ x, φ x = I.mkQ (x ⬝ᵥ v₀) := fun _ => rfl
  have hs : Function.Surjective φ := fun y => by
    obtain ⟨r, rfl⟩ := I.mkQ_surjective y
    obtain ⟨u, hu⟩ := hk
    refine ⟨Pi.single k (r * u⁻¹.val), ?_⟩
    rw [hφ, single_dotProduct, ← hu, Units.inv_mul_cancel_right]
  have hk' : N = LinearMap.ker φ := by
    ext x
    rw [LinearMap.mem_ker, hφ, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨y, rfl⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
      exact Ideal.sum_mem _ fun i _ => I.mul_mem_left _ (Ideal.subset_span ⟨i, rfl⟩)
    · intro h
      exact (Submodule.Quotient.mk_eq_zero N).1 ((hx x).trans (hIq _ h))
  exact ⟨(Submodule.quotEquivOfEq _ _ hk').trans (φ.quotKerEquivOfSurjective hs)⟩

theorem cyclic_ideal : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → ∀ P : Perf f M, UniversallyClosed f → Surjective f → ∀ (K : Type) [Field K] (g₀ : R →+* K), IsLocalHom g₀ → ∀ (X₀ : Scheme.{0}) (π₀ : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π₀ f₀ f (Spec.map (CommRingCat.ofHom g₀)) → Function.Bijective f₀.appTop.hom → Triv (M.pull π₀) → ∃ I : Ideal R, Nonempty (((Fin P.a → R) ⧸ LinearMap.range P.D₀.transpose.mulVecLin) ≃ₗ[R] (R ⧸ I)) ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) → (Triv (M.pull π) ↔ I ≤ RingHom.ker g) := by
  intro R _ _ X f M hM P hcl hsurj K _ g₀ hloc X₀ π₀ f₀ h₀ hb ht
  obtain ⟨v, hv, hu, hline⟩ := loc_of_triv P h₀ hM ht
  have unit_of : ∀ r : R, g₀ r ≠ 0 → IsUnit r := fun r hr => hloc.map_nonunit r hr.isUnit
  let z : Spec (CommRingCat.of K) := (⊥ : PrimeSpectrum K)
  have unit_cst : ∀ (R' : Type) [CommRing R'] (g : R →+* R') (X' : Scheme.{0}) (π : X' ⟶ X)
      (f' : X' ⟶ Spec (CommRingCat.of R')), IsPullback π f' f (Spec.map (CommRingCat.ofHom g)) →
      ∀ (c : R') (w : Fin P.a → R'), (∀ i, IsUnit (loc P π f' (c • w) i)) → IsUnit c := by
    intro R' _ g X' π f' h c w H
    by_contra hc
    obtain ⟨m, hm, hcm⟩ := exists_max_ideal_of_mem_nonunits hc
    have : Surjective f' := MorphismProperty.of_isPullback h hsurj
    obtain ⟨y, hy⟩ := f'.surjective (⟨m, hm.isPrime⟩ : PrimeSpectrum R')
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    have h₁ := H i
    rw [loc_smul] at h₁
    have h₂ := (mem_basicOpen_cst f' _ c hi).1 (mem_of_isUnit (isUnit_of_mul_isUnit_left h₁) hi)
    rw [hy] at h₂
    exact h₂ hcm
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero (unit_cst K g₀ X₀ π₀ f₀ h₀ 0 0 (by rwa [smul_zero]))
  obtain ⟨δ, v₀, hδ, hker₀⟩ := exists_kernel_vector g₀ P.D₀ v hv0 (hline hb.2)
  have hker : ∀ (R' : Type) [CommRing R'] (g : R →+* R'),
      ∀ w, (P.D₀.map g).mulVec w = 0 → ∃ c : R', w = c • (g ∘ v₀) :=
    fun R' _ g => hker₀ R' g ((unit_of δ hδ).map g)
  obtain ⟨c₀, hc₀⟩ := hker K g₀ v hv
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hv0
  have hk' : IsUnit (v₀ k) := unit_of _ fun h0 => hk (by
    rw [hc₀]
    change c₀ * g₀ (v₀ k) = 0
    rw [h0, mul_zero])
  let G : X.Opens := ⨆ i, X.basicOpen (loc₀ P v₀ i)
  have hZ : IsClosed (f '' (G : Set X)ᶜ) := f.isClosedMap _ G.isOpen.isClosed_compl
  have hp : Spec.map (CommRingCat.ofHom g₀) z ∈ (f '' (G : Set X)ᶜ)ᶜ := by
    rintro ⟨x, hx, hfx⟩
    obtain ⟨y, rfl, -⟩ := Scheme.exists_preimage_of_isPullback h₀ x z hfx
    obtain ⟨i, hi⟩ := exists_mem P (π₀ y)
    have h₁ := hu i
    rw [hc₀, loc_smul, loc_comp P h₀] at h₁
    have h₂ := mem_of_isUnit (isUnit_of_mul_isUnit_right h₁) (y := y) hi
    rw [← Scheme.preimage_basicOpen] at h₂
    exact hx (TopologicalSpace.Opens.mem_iSup.2 ⟨i, h₂⟩)
  obtain ⟨_, ⟨r₁, rfl⟩, hr₁, hsub⟩ :=
    (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).exists_subset_of_mem_open hp hZ.isOpen_compl
  have hr₁' : IsUnit r₁ := unit_of r₁ hr₁
  refine ⟨Ideal.span (Set.range (P.D₀.mulVec v₀)), coker_equiv P.D₀ v₀ k hk' hker,
    fun R' _ g X' π f' h => ?_⟩
  have hI : Ideal.span (Set.range (P.D₀.mulVec v₀)) ≤ RingHom.ker g ↔ (P.D₀.map g).mulVec (g ∘ v₀) = 0 := by
    rw [Ideal.span_le, Set.range_subset_iff, funext_iff]
    refine forall_congr' fun j => ?_
    rw [← RingHom.map_mulVec]
    rfl
  rw [hI]
  constructor
  · intro H
    obtain ⟨w, hw, hwu, -⟩ := loc_of_triv P h hM H
    obtain ⟨c, rfl⟩ := hker R' g w hw
    rw [Matrix.mulVec_smul] at hw
    exact ((unit_cst R' g X' π f' h c _ hwu).smul_eq_zero).1 hw
  · intro H
    refine triv_of_loc P h _ H fun y => ?_
    have hy : π y ∈ G := by
      by_contra hy
      refine hsub (a := f (π y)) ?_ ⟨π y, hy, rfl⟩
      change r₁ ∉ (f (π y)).asIdeal
      exact fun hm => (f (π y)).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hr₁')
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    refine ⟨i, ?_⟩
    rw [loc_comp P h, ← Scheme.preimage_basicOpen]
    exact hi

end GlobalTheory.UU.SecCyclic
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueBiTriv
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.EvenCub

section Alg
variable {A A' B U : Type} [CommGroup A] [CommGroup A'] [CommGroup B] [CommGroup U]

def diff₃ (k : A → U) (x y u : A) : U :=
  k (x * y * u) * (k (x * y))⁻¹ * (k (x * u))⁻¹ * (k (y * u))⁻¹ * k x * k y * k u * (k 1)⁻¹

def diffS (k : A → U) (x : A) : U := k x⁻¹ * (k x)⁻¹

end Alg

section Rep
variable {S X : Scheme.{0}} {L : LB X} {Y : Over S}

def Rep (L : LB X) (Y : Over S) (F : ∀ (U : Type) [CommGroup U], ((Y.left ⟶ X) → U) → U)
    (v : ∀ (T : Over S), (T ⟶ Y) → ∀ z : T.left, ((T.left ⟶ X) → L.ι) → (T.left.presheaf.stalk z)ˣ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (Y.left ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)), t.IsGen ∧
    (∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), ∏ k, h (φ k) ^ ε k = F U h) ∧
    ∀ (T : Over S) (σ : T ⟶ Y) (z : T.left) (J), Good L z J → val t σ.left z J = v T σ z J

variable {F F' : ∀ (U : Type) [CommGroup U], ((Y.left ⟶ X) → U) → U}
  {v v' : ∀ (T : Over S), (T ⟶ Y) → ∀ z : T.left, ((T.left ⟶ X) → L.ι) → (T.left.presheaf.stalk z)ˣ}

theorem Rep.mul (h : Rep L Y F v) (h' : Rep L Y F' v') :
    Rep L Y (fun U _ k => F U k * F' U k) (fun T σ z J => v T σ z J * v' T σ z J) := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', hF', hv'⟩ := h'
  exact ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L φ ε φ' ε' t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ k => DVR.prod_sum₂ _ (hF U k) (hF' U k), fun T σ z J hJ =>
      (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv T σ z J hJ) (hv' T σ z J hJ))⟩

theorem Rep.inv (h : Rep L Y F v) : Rep L Y (fun U _ k => (F U k)⁻¹) (fun T σ z J => (v T σ z J)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, hF, hv⟩ := h
  refine ⟨K, inferInstance, _, _, LB.invGen L φ ε t, DVR.invGen_isGen _ _ _ _ ht, fun U _ k => ?_, fun T σ z J hJ =>
    (val_inv _ _).trans (congrArg (·⁻¹) (hv T σ z J hJ))⟩
  show _ = (F U k)⁻¹
  rw [← hF U k, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun a _ => zpow_neg _ _

theorem Rep.pull {K : Type} [Fintype K] {Y' : Over S} {φ : K → (Y'.left ⟶ X)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) (p : Y ⟶ Y')
    (hF : ∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), ∏ k, h (p.left ≫ φ k) ^ ε k = F U h) :
    Rep L Y F (fun _ σ z J => val t (σ ≫ p).left z J) :=
  ⟨K, inferInstance, _, _, LB.pullGen L φ ε t p.left, DVR.pullGen_isGen _ _ _ _ ht _, hF,
    fun _ _ _ _ hJ => val_pull hJ _ _ _⟩

theorem Rep.eq_one (hL : L.IsLB) (hY : Function.Surjective Y.hom.appTop.hom) (h : Rep L Y F v)
    (hF : ∀ (U : Type) [CommGroup U] (h : (Y.left ⟶ X) → U), F U h = 1) (e : 𝟙_ (Over S) ⟶ Y)
    (he : ∀ z J, Good L z J → v _ e z J = 1) (T : Over S) (σ : T ⟶ Y) (z : T.left) (J) (hJ : Good L z J) :
    v T σ z J = 1 := by
  obtain ⟨K, _, φ, ε, t, ht, hF', hv⟩ := h
  refine (hv T σ z J hJ).symm.trans ((gen_unique' hL (fun U _ k => ?_) Y.hom e.left (Over.w e) hY ht
    (LB.isGen_oneGen L) (fun y I hI => (hv _ e y I hI).trans ((he y I hI).trans (val_one _).symm)) _ σ.left z J hJ).trans
    (val_one _))
  rw [hF', hF]
  exact Fintype.prod_empty _

end Rep

section Quad
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

variable {H : Over S} [GrpObj H] [IsCommMonObj H] {P : CP G} {i : H ⟶ G} [IsMonHom i]

end Quad

section DVR
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K] {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
  [Smooth G.hom] [IsSeparated G.hom] [GeometricallyConnected G.hom]

end DVR

end GlobalTheory.EvenCub
end
end
