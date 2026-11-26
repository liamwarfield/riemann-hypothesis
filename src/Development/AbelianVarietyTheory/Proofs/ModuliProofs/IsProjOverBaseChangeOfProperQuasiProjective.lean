module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TautologicalModel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverBaseChangeOfProperQuasiProjective
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverBaseChangeOfProperQuasiProjective
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem _root_.GlobalTheory.isProjOver_of_isProper_of_isImmersion {A : Type} [CommRing A]
    {B X : Scheme.{0}} (e : B ⟶ X)
    [IsImmersion e] {x : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A} (hx : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver x) [IsProper (e ≫ x)] :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (e ≫ x) := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver at hx
  obtain ⟨N, i, hi, -, rfl⟩ := hx
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver
  haveI : IsProper (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str A N) := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str A N
  haveI : IsProper ((e ≫ i) ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str A N) := by rw [Category.assoc]; infer_instance
  haveI : IsProper (e ≫ i) := IsProper.of_comp (e ≫ i) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str A N)
  exact ⟨N, e ≫ i, .of_isPreimmersion _ (e ≫ i).isClosedMap.isClosed_range, by simp⟩

private theorem isPullback_fst_comp_map {X Y Z W : Scheme.{0}} (f : X ⟶ Y) (s : Y ⟶ Z)
    (t : W ⟶ Z) :
    IsPullback (pullback.fst (f ≫ s) t)
      (pullback.map (f ≫ s) t s t f (𝟙 _) (𝟙 _) (by simp) (by simp)) f (pullback.fst s t) := by
  have h₁ : pullback.map (f ≫ s) t s t f (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ pullback.fst s t =
      pullback.fst (f ≫ s) t ≫ f := pullback.lift_fst _ _ _
  have h₂ : pullback.map (f ≫ s) t s t f (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ pullback.snd s t =
      pullback.snd (f ≫ s) t := (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  refine IsPullback.of_bot ?_ h₁.symm (IsPullback.of_hasPullback s t)
  rw [h₂]
  exact IsPullback.of_hasPullback (f ≫ s) t

private theorem isImmersion_pullback_lift_of_isPullback {X Y Z W P : Scheme.{0}} (f : X ⟶ Y)
    (s : Y ⟶ Z) (t : W ⟶ Z) (y : W ⟶ Y) (hy : y ≫ s = t) (φ : P ⟶ X) (b : P ⟶ W)
    (h : IsPullback φ b f y) :
    IsImmersion (pullback.lift (f := f ≫ s) (g := t) φ b
      (by rw [← hy, ← Category.assoc, h.w, Category.assoc])) := by
  set Γ : W ⟶ pullback s t := pullback.lift y (𝟙 W) (by rw [hy, Category.id_comp]) with hΓdef
  have hΓs : Γ ≫ pullback.snd s t = 𝟙 W := pullback.lift_snd _ _ _
  have hΓf : Γ ≫ pullback.fst s t = y := pullback.lift_fst _ _ _
  haveI : IsImmersion (Γ ≫ pullback.snd s t) := by rw [hΓs]; infer_instance
  haveI : IsImmersion Γ := IsImmersion.of_comp Γ (pullback.snd s t)
  set e : P ⟶ pullback (f ≫ s) t := pullback.lift (f := f ≫ s) (g := t) φ b
    (by rw [← hy, ← Category.assoc, h.w, Category.assoc]) with hedef
  have hef : e ≫ pullback.fst (f ≫ s) t = φ := pullback.lift_fst _ _ _
  have hes : e ≫ pullback.snd (f ≫ s) t = b := pullback.lift_snd _ _ _
  set g := pullback.map (f ≫ s) t s t f (𝟙 _) (𝟙 _) (by simp) (by simp) with hgdef
  have hg₁ : g ≫ pullback.fst s t = pullback.fst (f ≫ s) t ≫ f := pullback.lift_fst _ _ _
  have hg₂ : g ≫ pullback.snd s t = pullback.snd (f ≫ s) t :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hsq : e ≫ g = b ≫ Γ := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hg₁, hΓf, ← Category.assoc, hef, h.w]
    · rw [Category.assoc, Category.assoc, hg₂, hΓs, hes, Category.comp_id]
  have hleft : IsPullback e b g Γ := by
    refine IsPullback.of_right ?_ hsq (isPullback_fst_comp_map f s t)
    rw [hef, hΓf]
    exact h
  exact MorphismProperty.of_isPullback (P := @IsImmersion) hleft.flip ‹IsImmersion Γ›

theorem _root_.GlobalTheory.isProjOver_of_isPullback_of_isProper_of_isQProjOver :
    ∀ (R A : Type) [CommRing R] [CommRing A] (S : Scheme.{0}) (s : S ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) (G : Over S)
      (y : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A ⟶ S) (B : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A)) (φ : B.left ⟶ G.left), IsProper G.hom →
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (G.hom ≫ s) → IsPullback φ B.hom G.hom y → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver B.hom := by
  intro R A _ _ S s G y B φ hG hq hpb
  let j : R →+* A :=
    (Spec.preimage (y ≫ s : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))).hom
  have hj : y ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j := by
    unfold _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap
    simp only [j, CommRingCat.ofHom_hom]
    exact (Spec.map_preimage _).symm
  haveI := isImmersion_pullback_lift_of_isPullback G.hom s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j) y hj φ B.hom hpb
  haveI : IsProper B.hom := MorphismProperty.of_isPullback (P := @IsProper) hpb hG
  have hqQ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver (pullback.snd (G.hom ≫ s) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j)) :=
    (_root_.GlobalTheory.isQProjOver_baseChange_and_finite_restrict R A j _ _).1 hq
  have he : pullback.lift (f := G.hom ≫ s) (g := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j) φ B.hom
      (by rw [← hj, ← Category.assoc, hpb.w, Category.assoc]) ≫
        pullback.snd (G.hom ≫ s) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j) = B.hom := pullback.lift_snd _ _ _
  haveI : IsProper (pullback.lift (f := G.hom ≫ s) (g := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j) φ B.hom
      (by rw [← hj, ← Category.assoc, hpb.w, Category.assoc]) ≫
        pullback.snd (G.hom ≫ s) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap j)) := by rw [he]; infer_instance
  rw [← he]
  exact _root_.GlobalTheory.isProjOver_of_isProper_of_isImmersion _ hqQ

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjOverBaseChangeOfProperQuasiProjectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProjOver_baseChange_of_proper_quasiProjective : ∀ (R A : Type) [CommRing R] [CommRing A] (S : Scheme.{0}) (s : S ⟶ Sp R) (G : Over S) (y : Sp A ⟶ S) (B : Over (Sp A)) (φ : B.left ⟶ G.left), IsProper G.hom → IsQProjOver (G.hom ≫ s) → IsPullback φ B.hom G.hom y → IsProjOver B.hom := by
  first | exact @GlobalTheory.isProjOver_of_isPullback_of_isProper_of_isQProjOver | exact GlobalTheory.isProjOver_of_isPullback_of_isProper_of_isQProjOver | (intros; apply GlobalTheory.isProjOver_of_isPullback_of_isProper_of_isQProjOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawTrivialityOnDenseFibresProductAbelian
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawTrivialityOnDenseFibresProductAbelian
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem isPullback_lift_toUnit_fst_left {S : Scheme.{0}} (A B : Over S) (x : 𝟙_ (Over S) ⟶ A) :
    IsPullback (lift (toUnit B ≫ x) (𝟙 B)).left B.hom (fst A B).left (x.left : S ⟶ A.left) := by
  have h1 : (lift (toUnit B ≫ x) (𝟙 B)).left ≫ (fst A B).left = B.hom ≫ (x.left : S ⟶ A.left) := by
    rw [← Over.comp_left, lift_fst, Over.comp_left]
    rfl
  have h2 : (lift (toUnit B ≫ x) (𝟙 B)).left ≫ (snd A B).left = 𝟙 B.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have h3 : (x.left : S ⟶ A.left) ≫ A.hom = 𝟙 S := Over.w x
  have hp : IsPullback (snd A B).left (fst A B).left B.hom A.hom :=
    (IsPullback.of_hasPullback A.hom B.hom).flip
  refine IsPullback.of_right ?_ h1 hp
  rw [h2, h3]
  exact IsPullback.of_horiz_isIso ⟨by simp⟩

theorem triv_of_triv_on_dense_fibres_prod_abelian : Out.GlobalFnsSt → ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (N : LB (A ⊗ B).left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → M.IsLB → Out.RelAmple B M → N.IsLB → (∃ t : (N.pull (lift (1 : B ⟶ A) (𝟙 B)).left).Gen, t.IsGen) → Dense (⋃ x ∈ {x : 𝟙_ (Over (Sp k)) ⟶ A | ∃ t : (N.pull (lift (toUnit B ≫ x) (𝟙 B)).left).Gen, t.IsGen}, Set.range x.left) → (∃ t : (N.pull (lift (𝟙 A) (1 : A ⟶ B)).left).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro hG k _ _ A B _ _ N M hA hB hM hamp hN _ hd h0
  have : IsReduced A.left :=
    (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k A.left A.hom hA.smooth).1
  have hp : IsPullback (snd A B).left (fst A B).left B.hom A.hom :=
    (IsPullback.of_hasPullback A.hom B.hom).flip
  refine GlobalTheory.T.seesaw_reduced_base_abelianScheme_of_dense_fibres hG (Sp k) B M hB hM hamp A.left (A ⊗ B).left A.hom (snd A B).left (fst A B).left N hp hN
    (hd.mono ?_) (lift (𝟙 A) (1 : A ⟶ B)).left ?_ h0
  · intro p hp
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hp
    obtain ⟨x, hx, hpx⟩ := hp
    exact ⟨k, inferInstance, x.left, B.left, _, B.hom, hpx, isPullback_lift_toUnit_fst_left A B x, hx⟩
  · rw [← Over.comp_left, lift_fst, Over.id_left]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawTrivialityOnDenseFibresProductAbelianStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_triviality_on_dense_fibres_product_abelian : Out.GlobalFnsSt → ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (N : LB (A ⊗ B).left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → M.IsLB → Out.RelAmple B M → N.IsLB → (∃ t : (N.pull (lift (1 : B ⟶ A) (𝟙 B)).left).Gen, t.IsGen) → Dense (⋃ x ∈ {x : 𝟙_ (Over (Sp k)) ⟶ A | ∃ t : (N.pull (lift (toUnit B ≫ x) (𝟙 B)).left).Gen, t.IsGen}, Set.range x.left) → (∃ t : (N.pull (lift (𝟙 A) (1 : A ⟶ B)).left).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  first | exact @GlobalTheory.triv_of_triv_on_dense_fibres_prod_abelian | exact GlobalTheory.triv_of_triv_on_dense_fibres_prod_abelian | (intros; apply GlobalTheory.triv_of_triv_on_dense_fibres_prod_abelian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelDominatedOfMapToBaseModel
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelDominatedOfMapToBaseModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models.Domination

noncomputable def toRing {T : Scheme.{0}} {R : Type} [CommRing R] (u : T ⟶ Sp R) : R →+* Γ(T, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ u.appTop).hom

theorem toRing_inj {T : Scheme.{0}} {R : Type} [CommRing R] {u v : T ⟶ Sp R} (h : toRing u = toRing v) : u = v := by
  apply ext_of_isAffine
  exact (cancel_epi _).1 (CommRingCat.hom_ext h)

theorem toRing_comp {T : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R'] (u : T ⟶ Sp R') (b : R →+* R') :
    toRing (u ≫ spMap b) = (toRing u).comp b := by
  unfold toRing
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]
  rfl

theorem eq_of_overring {T : Scheme.{0}} {O O' F : Type} [CommRing O] [CommRing O'] [Field F] {β : O →+* F}
    {β' : O' →+* F} {b : O →+* O'} (hβ : IsDedFrac β) (hβ' : IsDedFrac β') (hb : β'.comp b = β) (u : T ⟶ Sp O')
    (w : T ⟶ Sp F) (h : u ≫ spMap b = w ≫ spMap β) : u = w ≫ spMap β' := by
  obtain ⟨⟨_, -⟩, -, hf⟩ := hβ
  obtain ⟨-, -, hf'⟩ := hβ'
  apply toRing_inj
  have h' := congrArg toRing h
  rw [toRing_comp, toRing_comp] at h'
  rw [toRing_comp]
  ext x
  letI := β.toAlgebra
  have hinj : Function.Injective β' := by
    letI := β'.toAlgebra
    exact IsFractionRing.injective O' F
  obtain ⟨p, q, hq, e⟩ := IsFractionRing.div_surjective (A := O) (β' x)
  have hq0 : β q ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq
  have e' : β' x * β q = β p := by
    rw [← e]; exact div_mul_cancel₀ _ hq0
  have e₂ : x * b q = b p := by
    apply hinj
    rw [map_mul]
    have := RingHom.congr_fun hb
    simp only [RingHom.comp_apply] at this
    rw [this, this, e']
  have hu : IsUnit (toRing w (β q)) := (IsUnit.mk0 _ hq0).map _
  have k₁ : ∀ y, toRing u (b y) = toRing w (β y) := RingHom.congr_fun h'
  apply hu.mul_right_cancel
  rw [RingHom.comp_apply, ← map_mul, e', ← k₁, ← k₁, ← map_mul, e₂]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem eq_of_RZ {T : Scheme.{0}} {l : Level H} {S A : ℕ} (hA : l.A = A) {β : RZ H S A →+* KA l}
    (hβ : IsInc (RZ H S A).subtype (KA l).val.toRingHom β) (u v : T ⟶ Sp (KA l))
    (h : u ≫ spMap β = v ≫ spMap β) : u = v := by
  apply toRing_inj
  have h' := congrArg toRing h
  rw [toRing_comp, toRing_comp] at h'
  have k₁ : ∀ y, toRing u (β y) = toRing v (β y) := RingHom.congr_fun h'
  have k₂ : ∀ (x : ℂ) (hx : x ∈ KA l), x ∈ RZ H S A → toRing u ⟨x, hx⟩ = toRing v ⟨x, hx⟩ := fun x hx hx' => by
    have : β ⟨x, hx'⟩ = ⟨x, hx⟩ := Subtype.ext (hβ _)
    rw [← this, k₁]
  let K : Subfield ℂ := ((toRing u).eqLocusField (toRing v)).map (KA l).val.toRingHom
  have hK : (KA l).toSubfield ≤ K := by
    have : KA l ≤ K.toIntermediateField (fun x => by simp) := by
      unfold KA
      rw [IntermediateField.adjoin_le_iff]
      rintro x (rfl | rfl)
      · have m₁ : (1 + H.rt0) / 2 ∈ RZ H S A := Subring.subset_closure (by simp)
        have m₂ : H.rt0 ∈ RZ H S A := by
          have : H.rt0 = (1 + H.rt0) / 2 + (1 + H.rt0) / 2 - 1 := by ring
          rw [this]
          exact sub_mem (add_mem m₁ m₁) (one_mem _)
        exact ⟨(baseKA l).ρ, k₂ _ _ m₂, rfl⟩
      · exact ⟨(baseKA l).ζ, k₂ _ _ (Subring.subset_closure (by simp [hA])), rfl⟩
    exact this
  ext x
  obtain ⟨y, hy, e⟩ := hK x.2
  have : y = x := Subtype.ext e
  exact this ▸ hy

theorem dominates_of_map_to_base : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N) (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model (Xo l) c β) (Y' : Model (Xo l) c β') (b : O →+* O') (f : pullback Y.s (spMap b) ⟶ B.C.X) (t : SAB H (pullback Y.s (spMap b))) (m₁ : SABMap t Y.t (pullback.fst _ _)) (m₂ : SABMap t B.C.t f) (r : (Xo l).XF c ⟶ (Xo l₀).X) (ν : SABMap Y.oF.t (Xo l₀).univ.t r) (k : KA l₀ →+* c.F), IsDedFrac β → IsDedFrac β' → β'.comp b = β → Raises B Y' → LevComp Y.oF (Xo l₀).univ r ν → IsInc (KA l₀).val.toRingHom c.F.val.toRingHom k → r ≫ (Xo l₀).s = pullback.snd _ _ ≫ spMap k → (∀ g : (Xo l).XF c ⟶ pullback Y.s (spMap b), g ≫ pullback.fst _ _ = Y.j → g ≫ f = r ≫ B.C.j) → (∀ y : Y.oF.t.G.left ⟶ t.G.left, y ≫ m₁.φ = Y.m.φ → y ≫ m₂.φ = ν.φ ≫ B.C.m.φ) → Dominates Y Y' b := by
  intro L₁ L₂ L₃ E _ _ _ H D Xo n N T l₀ l B c O O' _ _ β β' Y Y' b f t m₁ m₂ r ν k hβ hβ' hb hR hν hk hr hf hφ
  obtain ⟨b₀, r₀, ν₀, hb₀, hν₀, ⟨a₀⟩⟩ := hR

  obtain ⟨ν', hν'⟩ := LevelCover.sab_cancel Y'.m0.toSABMap Y.m0.toSABMap (𝟙 _) (Category.id_comp _)
  have η₁ : ∀ x, (Y.oF.eta x).left ≫ ν'.φ = 𝟙 _ ≫ (Y'.oF.eta x).left := fun x =>
    LevelCover.sec_cancel ν' Y'.m0.toSABMap _ _ (by
      rw [hν', Category.id_comp]; exact (Y.m0.eta x).trans (Y'.m0.eta x).symm)
  have η₂ : ∀ x, (Y.oF.etaA x).left ≫ ν'.φ = 𝟙 _ ≫ (Y'.oF.etaA x).left := fun x =>
    LevelCover.sec_cancel ν' Y'.m0.toSABMap _ _ (by
      rw [hν', Category.id_comp]; exact (Y.m0.etaA x).trans (Y'.m0.etaA x).symm)
  obtain ⟨ν₁, hν₁⟩ := LevelCover.sab_comp ν' ν₀ (Category.id_comp r₀)
  have hl₁ : LevComp Y.oF (Xo l₀).univ r₀ ν₁ := by
    refine ⟨fun x => ?_, fun x => ?_⟩
    · rw [hν₁, ← Category.assoc, LevelCover.sec_pow ν' _ _ (η₁ x), Category.id_comp, hν₀.1]
    · rw [hν₁, ← Category.assoc, LevelCover.sec_pow ν' _ _ (η₂ x), Category.id_comp, hν₀.2]
  have hkb : k.comp B.β = β'.comp b₀ := RingHom.ext fun x => Subtype.ext
    ((hk (B.β x)).trans ((B.β_inc x).trans (hb₀ x).symm))
  have hrB : r ≫ B.C.j ≫ B.C.s = pullback.snd _ _ ≫ spMap (β'.comp b₀) := by
    rw [Cpt.openImmersion_comp_structure_eq_generic, ← Category.assoc, hr, Category.assoc, ← spMap_comp, hkb]
  have hrr : r ≫ (Xo l₀).s = r₀ ≫ (Xo l₀).s := by
    apply eq_of_RZ B.A_one B.β_inc
    rw [Category.assoc, Category.assoc, ← Cpt.openImmersion_comp_structure_eq_generic B.C, hrB, ← Category.assoc, ← a₀.j_comm, Category.assoc,
      a₀.π_over, ← Category.assoc, Cpt.openImmersion_comp_structure_eq_generic, Category.assoc, ← spMap_comp]
  have hred : IsReduced ((Xo l).XF c) := by
    have := (Xo l).smooth
    have : Smooth (Xo l).s := SmoothOfRelativeDimension.smooth D.dim _
    exact (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field c.F _ (pullback.snd _ _)
      inferInstance).1
  obtain ⟨rfl, hνν⟩ := GlobalTheory.LevUniq.map_to_univ_unique L₁ L₂ L₃ E H D l₀ l (Xo l₀) _ _ _ _ Y.oF r r₀ ν ν₁ hred hrr hν hl₁

  obtain ⟨ido, hid⟩ := ObjMaps.exists_sab_id Y.oF.t
  obtain ⟨C, a, hiso⟩ := GlobalTheory.T.exists_model_baseChange_overring E H _ c.F O _ Y.oF.t β O' β' b (ofModel Y) ido hid hβ hβ' hb
  obtain ⟨e, π, mu, _, e₁, e₂, hj, hm⟩ : ∃ (e : C.X ⟶ pullback Y.s (spMap b)) (π : C.X ⟶ Y.X) (mu : SABMap C.t Y.t π),
      IsIso e ∧ e ≫ pullback.fst _ _ = π ∧ e ≫ pullback.snd _ _ = C.s ∧ C.j ≫ π = Y.j ∧ C.m.φ ≫ mu.φ = Y.m.φ :=
    ⟨pullback.lift a.π C.s a.π_over, a.π, a.mu, hiso, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _,
      a.j_comm.trans (Category.id_comp _), a.φ_comm.trans (by rw [hid]; exact Category.id_comp _)⟩
  have hje : ∀ (S : Scheme.{0}) (u : S ⟶ pullback Y.s (spMap b)) (x : S ⟶ (Xo l).XF c),
      u ≫ pullback.fst _ _ = x ≫ Y.j → u = x ≫ C.j ≫ e := fun S u x h => by
    apply pullback.hom_ext
    · rw [h, Category.assoc, Category.assoc, e₁, hj]
    · rw [Category.assoc, Category.assoc, e₂, Cpt.openImmersion_comp_structure_eq_generic, ← Category.assoc]
      apply eq_of_overring hβ hβ' hb
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, h, Category.assoc, Category.assoc]
      exact congrArg (x ≫ ·) (Cpt.openImmersion_comp_structure_eq_generic (ofModel Y))
  have hjf : C.j ≫ e ≫ f = r ≫ B.C.j := by
    rw [← Category.assoc]
    exact hf _ (by rw [Category.assoc, e₁, hj])
  obtain ⟨κ, hκ⟩ := LevelCover.sab_cancel m₁ mu e e₁
  obtain ⟨κ₂, hκ₂⟩ := LevelCover.sab_comp κ m₂ rfl
  have hm₁ : (C.m.φ ≫ κ.φ) ≫ m₁.φ = Y.m.φ := by
    rw [Category.assoc, hκ, hm]
  have hover : (e ≫ f) ≫ B.C.s = C.s ≫ spMap ((RingHom.id O').comp b₀) := by
    obtain ⟨⟨_, _⟩, -, hfr⟩ := hβ'
    letI := β'.toAlgebra
    obtain ⟨-, -, -, -, -, h3, -⟩ :=
      GlobalTheory.genericPart_dense_proOpen O' c.F C.X _ C.s C.jQ C.flat C.proj C.jQ_open C.jQ_dense
    have : IsDominant C.j := h3
    have : IsReduced C.X := by
      have : ∀ x : C.X, _root_.IsReduced (C.X.presheaf.stalk x) := fun x => by
        have := (C.normal x).1
        infer_instance
      exact isReduced_of_isReduced_stalk _
    apply ext_of_isDominant C.j
    rw [← Category.assoc, hjf, Category.assoc, hrB, ← Category.assoc, Cpt.openImmersion_comp_structure_eq_generic, Category.assoc, ← spMap_comp]
  obtain ⟨h₀, κ₀, hh₀, -, -, hjh₀, hmh₀, -⟩ := Cpt.Above.exists_lift E H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ B.C
    (ofModel Y') C b₀ (RingHom.id O') (RingHom.id c.F) r ν₀ a₀ (𝟙 _) ν' (e ≫ f) κ₂ hover hβ' rfl
    (by rw [LevelCover.spMap_id', Category.id_comp, Category.comp_id]) (by rw [hjf, Category.id_comp])
    (by rw [hκ₂, ← Category.assoc, hφ _ hm₁, hνν, hν₁, Category.assoc])
  obtain ⟨h, κ', hh, hjh, hmh⟩ : ∃ (h : C.X ⟶ Y'.X) (κ' : SABMap C.t Y'.t h), h ≫ Y'.s = C.s ∧ C.j ≫ h = Y'.j ∧
      C.m.φ ≫ κ'.φ = ν'.φ ≫ Y'.m.φ :=
    ⟨h₀, κ₀, hh₀.trans (by rw [LevelCover.spMap_id', Category.comp_id]), hjh₀.trans (Category.id_comp _), hmh₀⟩
  obtain ⟨idt, hid'⟩ := ObjMaps.exists_sab_id t
  obtain ⟨κi, hκi⟩ := LevelCover.sab_cancel κ idt (inv e) (IsIso.inv_hom_id e)
  obtain ⟨m₃, hm₃⟩ := LevelCover.sab_comp κi κ' rfl
  have hκκ : κ.φ ≫ κi.φ = 𝟙 _ := by
    apply κ.cart.1.hom_ext
    · change (κ.φ ≫ κi.φ) ≫ κ.φ = 𝟙 _ ≫ κ.φ
      rw [Category.assoc, hκi, hid', Category.comp_id, Category.id_comp]
    · have w₁ : κ.φ ≫ t.G.hom = C.t.G.hom ≫ e := κ.cart.1.w
      have w₂ : κi.φ ≫ C.t.G.hom = t.G.hom ≫ inv e := κi.cart.1.w
      rw [Category.assoc, w₂, ← Category.assoc, w₁, Category.assoc, IsIso.hom_inv_id, Category.comp_id,
        Category.id_comp]
  refine ⟨inv e ≫ h, t, m₁, m₃, ?_, fun u hu => ?_, fun S g g₁ g₂ q₁ q₂ q₃ => ?_⟩
  · rw [Category.assoc, hh, ← e₂, IsIso.inv_hom_id_assoc]
  · rw [hje _ u (𝟙 _) (by rw [hu, Category.id_comp]), Category.id_comp, Category.assoc, IsIso.hom_inv_id_assoc, hjh]
  · have w₀ : ν'.φ ≫ Y'.oF.t.G.hom = Y.oF.t.G.hom := ν'.cart.1.w.trans (Category.comp_id _)
    have s₂ : g₂ = g₁ ≫ ν'.φ := by
      apply Y'.m0.toSABMap.cart.1.hom_ext
      · change g₂ ≫ Y'.m0.toSABMap.φ = (g₁ ≫ ν'.φ) ≫ Y'.m0.toSABMap.φ
        rw [Category.assoc, hν', q₂]
      · rw [Category.assoc, w₀, q₃]
    have s₁ : g = g₁ ≫ C.m.φ ≫ κ.φ := by
      apply m₁.cart.1.hom_ext
      · change g ≫ m₁.φ = (g₁ ≫ C.m.φ ≫ κ.φ) ≫ m₁.φ
        rw [Category.assoc, hm₁, q₁]
      · have w₁ : κ.φ ≫ t.G.hom = C.t.G.hom ≫ e := κ.cart.1.w
        have w₂ : C.m.φ ≫ C.t.G.hom = Y.oF.t.G.hom ≫ C.j := C.m.cart.1.w
        have w₃ : m₁.φ ≫ Y.t.G.hom = t.G.hom ≫ pullback.fst _ _ := m₁.cart.1.w
        have w₄ : Y.m.φ ≫ Y.t.G.hom = Y.oF.t.G.hom ≫ Y.j := Y.m.cart.1.w
        rw [hje S (g ≫ t.G.hom) (g₁ ≫ Y.oF.t.G.hom) (by
          rw [Category.assoc, ← w₃, ← Category.assoc, q₁, Category.assoc, w₄, Category.assoc])]
        simp only [Category.assoc]
        rw [w₁, reassoc_of% w₂]
    rw [s₁, s₂, hm₃]
    simp only [Category.assoc]
    rw [reassoc_of% hκκ, hmh]

end GlobalTheory.Models.Domination
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModelDominatedOfMapToBaseModelStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_dominated_of_map_to_baseModel : Out.Laws → Out.Laws2 → Out.Laws3 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (n N : ℕ) (T : Top Xo n N) (l₀ l : Level H) (B : BaseModel T l₀) (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model (Xo l) c β) (Y' : Model (Xo l) c β') (b : O →+* O') (f : pullback Y.s (spMap b) ⟶ B.C.X) (t : SAB H (pullback Y.s (spMap b))) (m₁ : SABMap t Y.t (pullback.fst _ _)) (m₂ : SABMap t B.C.t f) (r : (Xo l).XF c ⟶ (Xo l₀).X) (ν : SABMap Y.oF.t (Xo l₀).univ.t r) (k : KA l₀ →+* c.F), IsDedFrac β → IsDedFrac β' → β'.comp b = β → Raises B Y' → LevComp Y.oF (Xo l₀).univ r ν → IsInc (KA l₀).val.toRingHom c.F.val.toRingHom k → r ≫ (Xo l₀).s = pullback.snd _ _ ≫ spMap k → (∀ g : (Xo l).XF c ⟶ pullback Y.s (spMap b), g ≫ pullback.fst _ _ = Y.j → g ≫ f = r ≫ B.C.j) → (∀ y : Y.oF.t.G.left ⟶ t.G.left, y ≫ m₁.φ = Y.m.φ → y ≫ m₂.φ = ν.φ ≫ B.C.m.φ) → Dominates Y Y' b := by
  first | exact @GlobalTheory.Models.Domination.dominates_of_map_to_base | exact GlobalTheory.Models.Domination.dominates_of_map_to_base | (intros; apply GlobalTheory.Models.Domination.dominates_of_map_to_base <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFibrewiseThetaOfOpenImmersionCover
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFibrewiseThetaOfOpenImmersionCover
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum

namespace GlobalTheory.ThetaLocal

open GlobalTheory.AbLocusPull

variable {X X' : Scheme.{0}}

theorem fn_ext_of_isOpenImmersion (F : X' ⟶ X) [IsOpenImmersion F] {U : X.Opens} (hU : U ≤ F.opensRange)
    {a b : Γ(X, U)} (h : ∀ x, F x ∈ U → gs F x U a = gs F x U b) : a = b := by
  have := F.isIso_app U hU
  apply (ConcreteCategory.bijective_of_isIso (F.app U)).1
  refine fn_ext fun x hx => ?_
  have e₁ := gs_pull (𝟙 X') F x U hx a
  have e₂ := gs_pull (𝟙 X') F x U hx b
  rw [Category.id_comp] at e₁ e₂
  exact e₁.trans ((h x hx).trans e₂.symm)

theorem exists_fn_of_isOpenImmersion (F : X' ⟶ X) [IsOpenImmersion F] {U : X.Opens} (hU : U ≤ F.opensRange)
    (b : Γ(X', F ⁻¹ᵁ U)) : ∃ a : Γ(X, U), ∀ x, F x ∈ U → gs F x U a = gs (𝟙 X') x _ b := by
  have := F.isIso_app U hU
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (F.app U)).2 b
  refine ⟨a, fun x hx => ?_⟩
  have e₁ := gs_pull (𝟙 X') F x U hx a
  rw [Category.id_comp] at e₁
  exact e₁.symm

theorem exists_secOn_push {F : X' ⟶ X} [IsOpenImmersion F] {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull F)) {W : X.Opens} {W' : X'.Opens} (hr : W ≤ F.opensRange) (hW : F ⁻¹ᵁ W ≤ W')
    {θ' : ∀ k, Γ(X', W' ⊓ L'.U k)} (hθ' : θ' ∈ secOn L' W') :
    ∃ θ ∈ secOn L W, ∀ x, F x ∈ W → ∀ j k, F x ∈ L.U j → x ∈ X'.basicOpen (θ' k) → F x ∈ X.basicOpen (θ j) := by
  obtain ⟨w, hw⟩ := hw
  have hw := (isGen_iff w).1 hw
  have rel : ∀ (x : X') j j' k k', F x ∈ W → F x ∈ L.U j → F x ∈ L.U j' → x ∈ L'.U k → x ∈ L'.U k' →
      (gw w (𝟙 X') x j k).val * gs (𝟙 X') x _ (θ' k) =
        (gm F x (L.U j ⊓ L.U j') (L.g j j')).val * ((gw w (𝟙 X') x j' k').val * gs (𝟙 X') x _ (θ' k')) := by
    intro x j j' k k' hx hj hj' hk hk'
    have e := hw _ (𝟙 X') x j j' k k' hj hj' hk hk'
    rw [Category.id_comp] at e
    rw [gs_secOn hθ' (𝟙 X') x k k' (hW hx) hk hk', e, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul,
      ← Units.val_mul]
    congr 2
    rw [mul_right_comm, inv_mul_cancel_right]
  have ex : ∀ j, ∃ a : Γ(X, W ⊓ L.U j), ∀ x k, F x ∈ W → F x ∈ L.U j → x ∈ L'.U k →
      gs F x _ a = (gw w (𝟙 X') x j k).val * gs (𝟙 X') x _ (θ' k) := by
    intro j
    let O : L'.ι → X'.Opens := fun k => F ⁻¹ᵁ W ⊓ ((L.pull F).U (fun _ => j) ⊓ L'.U k)
    have le : ∀ k, O k ≤ W' ⊓ L'.U k := fun k x hx => ⟨hW hx.1, hx.2.2⟩
    let u : ∀ k, Γ(X', (L.pull F).U (fun _ => j) ⊓ L'.U k)ˣ := fun k => w.s (fun _ => j, k)
    let a : ∀ k, Γ(X', O k) := fun k => resG X' inf_le_right (u k).val * resG X' (le k) (θ' k)
    have va : ∀ x k, x ∈ O k → gs (𝟙 X') x _ (a k) = (gw w (𝟙 X') x j k).val * gs (𝟙 X') x _ (θ' k) := by
      intro x k hx
      refine (gs_mul _ x _ hx _ _).trans ?_
      rw [gs_res _ x _ hx, gs_res _ x _ hx, gs_unit _ x _ hx.2]
      rfl
    obtain ⟨b, hb⟩ := glue_fn (F ⁻¹ᵁ (W ⊓ L.U j)) O (fun k x hx => ⟨hx.1, mem_pull.1 hx.2.1⟩)
      (fun x hx => (exists_chart hL' x).imp fun k hk => ⟨hx.1, mem_pull.2 hx.2, hk⟩) a (fun k k' x hk hk' => by
        rw [va x k hk, va x k' hk', rel x j j k k' hk.1 (mem_pull.1 hk.2.1) (mem_pull.1 hk.2.1) hk.2.2 hk'.2.2,
          gm_self hL F x (mem_pull.1 hk.2.1), Units.val_one, _root_.one_mul])
    obtain ⟨c, hc⟩ := exists_fn_of_isOpenImmersion F (inf_le_left.trans hr) b
    refine ⟨c, fun x k hx hj hk => ?_⟩
    have hm : x ∈ O k := ⟨hx, mem_pull.2 hj, hk⟩
    exact (hc x ⟨hx, hj⟩).trans ((hb x k hm).trans (va x k hm))
  choose θ hθ using ex
  refine ⟨θ, fun j j' => fn_ext_of_isOpenImmersion F (inf_le_left.trans (inf_le_left.trans hr)) fun x hx => ?_,
    fun x hx j k hj hk => ?_⟩
  · obtain ⟨k, hk⟩ := exists_chart hL' x
    rw [gs_res _ x _ hx, gs_mul _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx,
      gs_unit F x (L.U j ⊓ L.U j') ⟨hx.1.2, hx.2⟩, hθ j x k hx.1.1 hx.1.2 hk, hθ j' x k hx.1.1 hx.2 hk]
    exact rel x j j' k k hx.1.1 hx.1.2 hx.2 hk hk
  · have hm : x ∈ W' ⊓ L'.U k := X'.basicOpen_le _ hk
    refine (isUnit_gs_iff F x (W ⊓ L.U j) ⟨hx, hj⟩ _).1 ?_
    rw [hθ j x k hx hj hm.2]
    exact (Units.isUnit _).mul ((isUnit_gs_iff (𝟙 X') x _ hm _).2 hk)

theorem hasTheta_of_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, HasTheta (u i).G (u i).PP.L) → HasTheta t.G t.PP.L := by
  intro E _ _ _ H Z t I Y f u m hf hc hu z
  obtain ⟨i, y, rfl⟩ := hc z
  have := hf i
  have h := (m i).cart.1
  have : IsOpenImmersion (m i).cm.F := MorphismProperty.of_isPullback (P := @IsOpenImmersion) h.flip ‹_›
  obtain ⟨w, g, -⟩ := (m i).lin
  have sq : ∀ x, t.G.hom ((m i).cm.F x) = f i ((u i).G.hom x) := fun x => by
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
  obtain ⟨V, hy, θ', hθ', hne⟩ := hu i y
  have hr : t.G.hom ⁻¹ᵁ (f i ''ᵁ V) ≤ (m i).cm.F.opensRange := by
    rintro x ⟨y', -, e⟩
    obtain ⟨x', h₁, -⟩ := Scheme.exists_preimage_of_isPullback h x y' e.symm
    exact ⟨x', h₁⟩
  have hW : (m i).cm.F ⁻¹ᵁ (t.G.hom ⁻¹ᵁ (f i ''ᵁ V)) ≤ (u i).G.hom ⁻¹ᵁ V := by
    rintro x ⟨y', hy', e⟩
    have e' : y' = (u i).G.hom x := (f i).isOpenEmbedding.injective (e.trans (sq x))
    show (u i).G.hom x ∈ V
    rw [← e']; exact hy'
  obtain ⟨θ, hθ, hb⟩ := exists_secOn_push t.PP.isLB (u i).PP.isLB ⟨w, g⟩ hr hW hθ'
  refine ⟨f i ''ᵁ V, ⟨y, hy, rfl⟩, θ, hθ, ?_⟩
  rintro _ ⟨y', hy', rfl⟩
  obtain ⟨x, k, hx, hk⟩ := hne y' hy'
  obtain ⟨j, hj⟩ := exists_chart t.PP.isLB ((m i).cm.F x)
  refine ⟨(m i).cm.F x, j, (sq x).trans (congrArg _ hx), hb x ⟨y', hy', ?_⟩ j k hj hk⟩
  exact ((sq x).trans (congrArg _ hx)).symm

end GlobalTheory.ThetaLocal

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasFibrewiseThetaOfOpenImmersionCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ModelSum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasFibrewiseTheta_of_openImmersion_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Z : Scheme.{0}) (t : SAB H Z) (I : Type) (Y : I → Scheme.{0}) (f : ∀ i, Y i ⟶ Z) (u : ∀ i, SAB H (Y i)) (_ : ∀ i, SABMap (u i) t (f i)), (∀ i, IsOpenImmersion (f i)) → (∀ z : Z, ∃ i, z ∈ Set.range (f i)) → (∀ i, HasTheta (u i).G (u i).PP.L) → HasTheta t.G t.PP.L := by
  first | exact @GlobalTheory.ThetaLocal.hasTheta_of_cover | exact GlobalTheory.ThetaLocal.hasTheta_of_cover | (intros; apply GlobalTheory.ThetaLocal.hasTheta_of_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LocallyQuasiFiniteOfTrivialOnFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.AmpleFibre

open TopologicalSpace GlobalTheory.MulFinite

theorem exists_fn {X Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) (N : ℕ)
    (s : LB.Sec (LB.LinComb L (K := Fin N) (fun _ => 𝟙 X) (fun _ => 1))) (r : Z ⟶ X)
    (t : (L.pull r).Gen) (ht : t.IsGen) :
    ∃ a : Γ(Z, ⊤), Z.basicOpen a = r ⁻¹ᵁ Out.nonzeroLocus s := by
  let V : L.ι → Z.Opens := fun j => r ⁻¹ᵁ L.U j
  have l₁ : ∀ j, V j ≤ r ⁻¹ᵁ LB.wchart L (K := Fin N) (fun _ => 𝟙 X) (fun _ => j) :=
    fun j z hz => Set.mem_iInter.2 fun _ => hz
  have l₂ : ∀ j, V j ≤ LB.wchart L (K := PUnit) (fun _ => r) (fun _ => j) :=
    fun j z hz => Set.mem_iInter.2 fun _ => hz
  obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(Z, V j), ∀ j z, z ∈ V j → gs (𝟙 Z) z (V j) (u j) =
      gs r z (LB.wchart L (K := Fin N) (fun _ => 𝟙 X) (fun _ => j)) (s.f (fun _ => j)) *
        ((gm (𝟙 Z) z (LB.wchart L (K := PUnit) (fun _ => r) (fun _ => j)) (t.s (fun _ => j)))⁻¹).val ^ N := by
    refine ⟨fun j => (r.appLE _ _ (l₁ j)).hom (s.f (fun _ => j)) *
      (Z.presheaf.map (homOfLE (l₂ j)).op).hom ((t.s (fun _ => j))⁻¹).val ^ N, fun j z hz => ?_⟩
    refine (gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·) (gs_appLE r z _ _ _ hz _)
      ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_))
    erw [gs_res (𝟙 Z) z (l₂ j) hz, gs_unit (𝟙 Z) z _ (l₂ j hz)]
    exact congrArg (fun x : (Z.presheaf.stalk z)ˣ => x.val ^ N)
      (map_inv (gm (𝟙 Z) z _ ) (t.s (fun _ => j)))
  have hcov : (⊤ : Z.Opens) ≤ iSup V := fun z _ => by
    obtain ⟨j, hj⟩ := exists_chart hL (r z)
    exact Opens.mem_iSup.2 ⟨j, hj⟩
  obtain ⟨a, ha, -⟩ := Z.sheaf.existsUnique_gluing' V ⊤ (fun j => homOfLE le_top) hcov u
    (fun j j' => fn_ext (V := V j ⊓ V j') fun z hz => by
      refine (gs_res (𝟙 Z) z inf_le_left hz _).trans (Eq.trans ?_ (gs_res (𝟙 Z) z inf_le_right hz _).symm)
      rw [hu j z hz.1, hu j' z hz.2, sec_trans s r z (l₁ j hz.1) (l₁ j' hz.2),
        gen_trans ht (𝟙 Z) z (l₂ j hz.1) (l₂ j' hz.2)]
      have t₁ : trF (L := L) (K := Fin N) (fun _ => 𝟙 X) (fun _ => 1) r z (fun _ => j) (fun _ => j') =
          gm r z (L.U j ⊓ L.U j') (L.g j j') ^ N := by simp [trF]
      have t₂ : trF (L := L) (K := PUnit) (fun _ => r) (fun _ => 1) (𝟙 Z) z (fun _ => j) (fun _ => j') =
          gm r z (L.U j ⊓ L.U j') (L.g j j') := by simp [trF]
      rw [t₁, t₂]
      simpa only [pow_one] using pow_aux _ _ _ 1 N)
  refine ⟨a, ?_⟩
  ext z
  obtain ⟨j, hj⟩ := exists_chart hL (r z)
  have k₁ : gs (𝟙 Z) z ⊤ a = gs (𝟙 Z) z (V j) (u j) :=
    (gs_res (𝟙 Z) z le_top hj a).symm.trans (congrArg (gs (𝟙 Z) z (V j)) (ha j))
  have k₂ : z ∈ Z.basicOpen (show Γ(Z, ⊤) from a) ↔
      IsUnit (gs r z (LB.wchart L (K := Fin N) (fun _ => 𝟙 X) (fun _ => j)) (s.f (fun _ => j))) := by
    refine (isUnit_gs (𝟙 Z) z ⊤ trivial a).symm.trans ?_
    rw [k₁, hu j z hj, ← Units.val_pow_eq_pow_val, Units.isUnit_mul_units]
  refine k₂.trans ⟨fun h => ?_, fun h => ?_⟩
  · exact Opens.mem_iSup.2 ⟨fun _ => j, (isUnit_gs r z _ (l₁ j hj) _).1 h⟩
  · obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show r z ∈ Out.nonzeroLocus s from h)
    have hk' : r z ∈ LB.wchart L (K := Fin N) (fun _ => 𝟙 X) k := X.basicOpen_le _ hk
    rw [sec_trans s r z (l₁ j hj) hk']
    exact (Units.isUnit _).mul ((isUnit_gs r z _ hk' _).2 hk)

theorem isAffineHom_of_field {k : Type} [Field k] {Y : Scheme.{0}} (y : Sp k ⟶ Y) : IsAffineHom y := by
  refine ⟨fun U _ => ?_⟩
  have : Subsingleton ↥(Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  by_cases h : ∃ p, p ∈ y ⁻¹ᵁ U
  · obtain ⟨p, hp⟩ := h
    have : y ⁻¹ᵁ U = ⊤ := top_unique fun x _ => by rwa [Subsingleton.elim x p]
    rw [this]; exact isAffineOpen_top _
  · have : y ⁻¹ᵁ U = ⊥ := bot_unique fun x hx => (h ⟨x, hx⟩).elim
    rw [this]; exact isAffineOpen_bot _

theorem exists_integral_closedImmersion {P : Scheme.{0}} (Z : Set P) (hc : IsClosed Z)
    (hi : IsIrreducible Z) :
    ∃ (C : Scheme.{0}) (_ : IsIntegral C) (i : C ⟶ P), IsClosedImmersion i ∧ Set.range i = Z := by
  let I := Scheme.IdealSheafData.vanishingIdeal (X := P) ⟨Z, hc⟩
  have hr : Set.range I.subschemeι = Z := by
    rw [Scheme.IdealSheafData.range_subschemeι]
    simp [I]
  have : IsReduced I.subscheme := ReducedSubgroup.isReduced_subscheme_vanishingIdeal _
  have : IrreducibleSpace I.subscheme := by
    have e := I.subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph
    have : IrreducibleSpace (Set.range I.subschemeι) := by
      rw [hr]; exact Subtype.irreducibleSpace hi
    exact e.irreducibleSpace_iff.2 this
  exact ⟨I.subscheme, isIntegral_of_irreducibleSpace_of_isReduced _, I.subschemeι, inferInstance, hr⟩

theorem locallyQuasiFinite_of_trivial_on_fibres :
    ∀ (X Y : Scheme.{0}) (f : X ⟶ Y) (A : LB X), IsProper f → A.IsLB → (∀ x : X, ∃ (d : ℕ) (s : LB.Sec (LB.LinComb A (K := Fin d) (fun _ => 𝟙 X) (fun _ => 1))), x ∈ Out.nonzeroLocus s ∧ IsAffineOpen (Out.nonzeroLocus s)) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Y) (C : Scheme.{0}) [IsIntegral C] (i : C ⟶ pullback f y), IsFinite i → ∃ t : (A.pull (i ≫ pullback.fst f y)).Gen, t.IsGen) → LocallyQuasiFinite f := by
  intro X Y f A hf hA hs ht
  refine LocallyQuasiFinite.of_finite_preimage_singleton f fun y ↦ ?_
  let Ω := AlgebraicClosure (Y.residueField y)
  let y' : Sp Ω ⟶ Y :=
    Spec.map (CommRingCat.ofHom (algebraMap (Y.residueField y) Ω)) ≫ Y.fromSpecResidueField y
  have hy : y ∈ Set.range y' := by
    obtain ⟨z⟩ : Nonempty ↥(Spec (.of Ω)) := inferInstance
    exact ⟨z, (Scheme.Hom.comp_apply _ _ z).trans (Scheme.fromSpecResidueField_apply y _)⟩
  clear_value y'
  have hy' := isAffineHom_of_field y'
  have h₁ : IsAffineHom (pullback.fst f y') :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0})
      (IsPullback.of_hasPullback f y').flip hy'
  have h₂ : IsLocallyNoetherian (pullback f y') :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd f y')
  have h₃ : CompactSpace ↥(pullback f y') := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f y')
  have h₄ : IsNoetherian (pullback f y') := {}
  have hP : (Set.univ : Set ↥(pullback f y')).Finite := by
    rw [← sUnion_irreducibleComponents]
    refine NoetherianSpace.finite_irreducibleComponents.sUnion fun Z hZ => ?_
    obtain ⟨C, _, i, hi, rfl⟩ := exists_integral_closedImmersion Z
      (isClosed_of_mem_irreducibleComponents Z hZ) hZ.1
    obtain ⟨t, ht⟩ := ht Ω y' C i inferInstance
    choose d s hx ha using hs
    choose a ha' using fun x => exists_fn A hA (d x) (s x) _ t ht
    have : LocallyQuasiFinite (i ≫ pullback.snd f y') := by
      refine locallyQuasiFinite_of_cover (K := Ω) _ a (top_unique fun c _ => ?_) fun x => ?_
      · refine Opens.mem_iSup.2 ⟨(i ≫ pullback.fst f y') c, ?_⟩
        rw [ha']
        exact hx _
      · rw [ha']
        exact (ha x).preimage _
    have : Subsingleton ↥(Sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
    obtain ⟨p⟩ : Nonempty ↥(Sp Ω) := inferInstance
    have hC : Finite C := Set.finite_univ_iff.1
      (((i ≫ pullback.snd f y').finite_preimage_singleton p).subset fun c _ => Subsingleton.elim _ _)
    exact Set.finite_range i
  have := Set.finite_univ_iff.1 hP
  refine (Set.finite_range (pullback.fst f y')).subset ?_
  rw [Scheme.Pullback.range_fst]
  exact Set.preimage_mono (Set.singleton_subset_iff.mpr hy)

end GlobalTheory.AmpleFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawRigidifiedLineBundleDenseFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawRigidifiedLineBundleDenseFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem seesaw_rigidified_of_dense :
    ∀ (R : Type) [CommRing R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (M N : LB A.left) (Sg : Set (Sp R)), IsAbelianScheme A → M.IsLB → Out.RelAmple A M → N.IsLB → Dense Sg → Out.Rigidified A N → (∀ p ∈ Sg, ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Sp R) (X : Scheme.{0}) (φ : X ⟶ A.left) (π : X ⟶ Sp K), p ∈ Set.range x ∧ IsPullback φ π A.hom x ∧ ∃ t : (N.pull φ).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro R _ _ A _ M N Sg hA hM hamp hN hd hr hf
  exact GlobalTheory.seesaw_reduced_of_dense GlobalTheory.globalFns_holds (Sp R) A M hA hM hamp (Sp R) A.left (𝟙 _) (𝟙 _)
    A.hom N (IsPullback.of_horiz_isIso ⟨by simp⟩) hN (hd.mono fun p hp => hf p hp) (eSec A)
    (Over.w η[A]) hr

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SeesawRigidifiedLineBundleDenseFibresStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_rigidified_lineBundle_dense_fibres : ∀ (R : Type) [CommRing R] [IsReduced R] (A : Over (Sp R)) [GrpObj A] (M N : LB A.left) (Sg : Set (Sp R)), IsAbelianScheme A → M.IsLB → Out.RelAmple A M → N.IsLB → Dense Sg → Out.Rigidified A N → (∀ p ∈ Sg, ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Sp R) (X : Scheme.{0}) (φ : X ⟶ A.left) (π : X ⟶ Sp K), p ∈ Set.range x ∧ IsPullback φ π A.hom x ∧ ∃ t : (N.pull φ).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  first | exact @GlobalTheory.seesaw_rigidified_of_dense | exact GlobalTheory.seesaw_rigidified_of_dense | (intros; apply GlobalTheory.seesaw_rigidified_of_dense <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullObjOfObj
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem RZ.rt_coe (S A : ℕ) : ((RZ.rt H S A : RZ H S A) : ℂ) = H.rt0 := by
  have h2 : ((2 : RZ H S A) : ℂ) = 2 := map_ofNat (RZ H S A).subtype 2
  unfold RZ.rt
  push_cast
  rw [h2]
  ring

theorem fullObj_of_obj {D : Datum H} {l : Level H} {n : ℕ} {S : Scheme.{0}} (s : S ⟶ Sp (KA l))
    (o : Obj D l (baseKA l) s) (β : RZ H n l.A →+* KA l) (hβ : IsInc (RZ H n l.A).subtype (KA l).val.toRingHom β) :
    FullObj D (s ≫ spMap β) o.t o.etaA := by
  unfold IsInc at hβ
  have hρ : β (RZ.rt H n l.A) = (baseKA l).ρ := by
    apply Subtype.ext
    show ((β (RZ.rt H n l.A) : ℂ)) = H.rt0
    rw [← RZ.rt_coe (H := H) n l.A]
    exact hβ (RZ.rt H n l.A)
  have hze : β (RZ.ze H n l.A) = (baseKA l).ζ := by
    apply Subtype.ext
    show ((β (RZ.ze H n l.A) : ℂ)) = zeta l.A
    exact hβ (RZ.ze H n l.A)
  refine ⟨o.proper, o.ample, o.ktriv, o.etaA_add, o.etaA_ker, ?_⟩
  intro k _ _ _ x β' hx
  obtain ⟨g0, hg0⟩ : ∃ g0 : KA l →+* k, x ≫ s = spMap g0 := by
    refine ⟨(Spec.preimage (x ≫ s)).hom, ?_⟩
    unfold spMap
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hb : β' = g0.comp β := by
    have h1 : Spec.map (CommRingCat.ofHom β') = Spec.map (CommRingCat.ofHom (g0.comp β)) := by
      unfold spMap at hx hg0
      rw [← hx, ← Category.assoc, hg0, ← Spec.map_comp, CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  subst hb
  obtain ⟨hdet, I, hI1, hI2, -⟩ := o.geom k x g0 hg0
  refine ⟨?_, I, ?_, hI2⟩
  · rw [RingHom.comp_apply, hρ]
    exact hdet
  · rw [RingHom.comp_apply, hze]
    exact hI1

end GlobalTheory.Models
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleKTrivOfFiniteEtaleCover
noncomputable section

namespace GlobalTheory.PolDescent

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem kTriv_of_pull {S S' : Scheme.{0}} {f : S' ⟶ S} [IsAffineHom f] [Flat f] [Surjective f]
    {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left}
    (h : IsGrpPullback A' A f φ) (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hK : KTriv A' L') :
    KTriv A L := by
  obtain ⟨w, hw⟩ := hw
  intro R _ t x hx
  obtain ⟨R', g, t', hg, sq⟩ : ∃ (R' : CommRingCat.{0}) (g : Spec R' ⟶ Spec (CommRingCat.of R)) (t' : Spec R' ⟶ S'),
      Epi g ∧ g ≫ t = t' ≫ f := by
    have : IsAffine (pullback t f) := isAffine_of_isAffineHom (pullback.fst t f)
    refine ⟨Γ(pullback t f, ⊤), (pullback t f).isoSpec.inv ≫ pullback.fst t f,
      (pullback t f).isoSpec.inv ≫ pullback.snd t f, Flat.epi_of_flat_of_surjective _, ?_⟩
    rw [Category.assoc, Category.assoc, pullback.condition]
  let T : Over S := Over.mk t
  let T' : Over S' := Over.mk t'
  have hxw : (g ≫ x.left) ≫ A.hom = t' ≫ f := by rw [Category.assoc, Over.w x]; exact sq
  let x' : T' ⟶ A' := Over.homMk (h.1.lift _ _ hxw) (h.1.lift_snd _ _ _)
  have hx' : x'.left ≫ φ = g ≫ x.left := h.1.lift_fst _ _ _
  have key : x' = toUnit _ ≫ η[A'] := hK R' t' x' fun p => by
    obtain ⟨V, hV, c, hc⟩ := hx (g p)
    refine ⟨g ⁻¹ᵁ V, hV, ?_⟩
    let a : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ T := Over.homMk ((fst T' A').left ≫ g)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) sq).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ f) (Over.w (fst T' A'))))))
    let b : Over.mk ((T' ⊗ A').hom ≫ f) ⟶ A := pushPt h.1.w (snd T' A')
    have k₁ : (lift a b).left ≫ (fst T A).left = (fst T' A').left ≫ g := congrArg (fun q => q.left) (lift_fst a b)
    have k₂ : (lift a b).left ≫ (snd T A).left = (snd T' A').left ≫ φ := congrArg (fun q => q.left) (lift_snd a b)
    have k₃ : (lift a b).left ≫ ((fst T A ≫ x) * snd T A).left = ((fst T' A' ≫ x') * snd T' A').left ≫ φ := by
      have e : lift a b ≫ ((fst T A ≫ x) * snd T A) = (a ≫ x) * b := by
        rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
      refine (congrArg (fun q => q.left) e).trans (h.2 (T' ⊗ A') _ _ _ _ ?_ rfl)
      exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hx'.symm).trans (Category.assoc _ _ _).symm)
    have le : (fst T' A').left ⁻¹ᵁ g ⁻¹ᵁ V ≤ (lift a b).left ⁻¹ᵁ (fst T A).left ⁻¹ᵁ V := fun y hy =>
      (congrArg (fun q => q y ∈ V) k₁).mpr hy
    have hn := Scheme.Hom.resLE_comp_ι (lift a b).left le
    obtain ⟨c₁, h₁⟩ := gen_chartPull (chartPullIn L _ _ _) c hc
    obtain ⟨c₂, h₂⟩ := gen_chartPull (chartPullSame L (fun k : Fin 2 => (((fst T' A').left ⁻¹ᵁ g ⁻¹ᵁ V).ι ≫
      ![(lift (fst T' A' ≫ x') (snd T' A') ≫ μ[A']).left, (snd T' A').left] k) ≫ φ) _ _
      ((lift a b).left.resLE _ _ le) fun k => by
        rw [← Category.assoc, hn, Category.assoc, Category.assoc]
        fin_cases k
        exacts [congrArg (_ ≫ ·) k₃.symm, congrArg (_ ≫ ·) k₂.symm]) c₁ h₁
    obtain ⟨c₃, h₃⟩ := exists_down ((isGen_iff w).1 hw) hL hL' c₂ h₂
    exact gen_chartPull (chartPullOut L' _ _ _ _ fun _ => rfl) c₃ h₃
  let U : Over.mk (T'.hom ≫ f) ⟶ T := Over.homMk g sq
  have e₁ : U ≫ x = pushHom h T' x' := Over.OverMorphism.ext hx'.symm
  have e₂ : U ≫ x = U ≫ (1 : T ⟶ A) := by
    rw [e₁, MonObj.comp_one]
    exact (congrArg (pushHom h T') key).trans (map_one (pushHom h T'))
  exact Over.OverMorphism.ext ((cancel_epi g).1 (congrArg (fun q => q.left) e₂))

theorem relAmple_of_pull {S S' : Scheme.{0}} [IsLocallyNoetherian S] {f : S' ⟶ S} [IsFinite f] [Flat f]
    [Surjective f] {A : Over S} {A' : Over S'} [IsProper A.hom] {φ : A'.left ⟶ A.left} {L : LB A.left}
    {L' : LB A'.left} (h : IsPullback φ A'.hom A.hom f) (hL : L.IsLB) (hL' : L'.IsLB)
    (hw : LBIso L' (L.pull φ)) (hA : RelAmple A' L') : RelAmple A L := by
  have : IsFinite φ := MorphismProperty.of_isPullback (P := @IsFinite) h.flip inferInstance
  have : Flat φ := MorphismProperty.of_isPullback (P := @Flat) h.flip inferInstance
  have : Surjective φ := MorphismProperty.of_isPullback (P := @Surjective) h.flip inferInstance
  have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  refine relAmple_of_isAmpleLB A hL fun U hU => ?_
  have h₁ := isAmpleLB_of_relAmple A' hL' hA (f ⁻¹ᵁ U) (hU.preimage f)
  have pre : A'.hom ⁻¹ᵁ (f ⁻¹ᵁ U) = φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, ← h.w, Scheme.Hom.comp_preimage]
  rw [pre] at h₁
  have h₂ : IsAmpleLB ((L.pull φ).pull (φ ⁻¹ᵁ (A.hom ⁻¹ᵁ U)).ι) :=
    h₁.of_lbIso (LB.isLB_pull (LB.isLB_pull hL _) _)
      (LBIso.chartPull (GlobalTheory.chartPullPull _ _) (GlobalTheory.chartPullPull _ _) hw.symm)
  have h₃ : IsAmpleLB ((L.pull (A.hom ⁻¹ᵁ U).ι).pull (φ ∣_ (A.hom ⁻¹ᵁ U))) :=
    (isAmpleLB_congr (LB.isLB_pull (LB.isLB_pull hL _) _) (LB.isLB_pull (LB.isLB_pull hL _) _)
      (FiniteAmple.lbIso_pull_pull _ hL (morphismRestrict_ι φ _).symm)).1 h₂
  have : Surjective (φ ∣_ A.hom ⁻¹ᵁ U) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› _
  exact FiniteAmple.isAmpleLB_of_pull _ (LB.isLB_pull hL _) h₃

end GlobalTheory.PolDescent

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

theorem relAmple_kTriv_of_finite_etale_cover : ∀ (S S' : Scheme.{0}) [IsLocallyNoetherian S] (π : S' ⟶ S) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), IsFinite π → Etale π → Surjective π → IsAbelianScheme G → L.IsLB → L'.IsLB → IsGrpPullback G' G π φ → LBIso L' (L.pull φ) → (Out.RelAmple G' L' → Out.RelAmple G L) ∧ (Out.KTriv G' L' → Out.KTriv G L) := by
  intro S S' _ π G G' _ _ φ L L' _ _ _ hG hL hL' h hw
  have := hG.proper
  exact ⟨PolDescent.relAmple_of_pull h.1 hL hL' hw, PolDescent.kTriv_of_pull h hL hL' hw⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfFaithfullyFlat
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ZM

namespace GlobalTheory.AmpleDescent

theorem relAmple_of_faithfullyFlat : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [CommRing R'] [IsLocalRing R'] [Algebra R R'] [Module.FaithfullyFlat R R'] (B : Over (Sp R)) (B' : Over (Sp R')) [GrpObj B] [GrpObj B'] (φ : B'.left ⟶ B.left) (L : LB B.left) (L' : LB B'.left), IsAbelianScheme B → IsGrpPullback B' B (spMap (algebraMap R R')) φ → L.IsLB → L'.IsLB → LBIso L' (L.pull φ) → RelAmple B' L' → RelAmple B L := by
  intro R R' _ _ _ _ _ _ _ B B' _ _ φ L L' hB h hL hL' hw hA
  have : Flat (Out.specOf (algebraMap R R')) :=
    (HasRingHomProperty.Spec_iff (P := @Flat)).2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective (Out.specOf (algebraMap R R')) :=
    ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := R')⟩
  have : IsProper B.hom := hB.proper
  have : IsProper B'.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) h.1 inferInstance
  have : CompactSpace B.left := QuasiCompact.compactSpace_of_compactSpace B.hom
  have : QuasiSeparatedSpace B.left := quasiSeparatedSpace_of_quasiSeparated B.hom
  refine (relAmple_iff_isAmpleLB_of_isAffine B hL).2 (isAmpleLB_of_pull (algebraMap R R') h.1 hL ?_)
  exact (isAmpleLB_of_relAmple_of_isAffine B' hL' hA).of_lbIso (LB.isLB_pull hL φ) hw.symm

end GlobalTheory.AmpleDescent
end
