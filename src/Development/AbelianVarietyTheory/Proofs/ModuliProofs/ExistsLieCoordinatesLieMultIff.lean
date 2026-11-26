module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisEigen
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SecCoordBcScaleUnique
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLieCoordinatesLieMultIff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

private theorem isGrpPullback_one_left {S : Scheme.{0}} {G : Over S} [GrpObj G] (X : Over S) :
    (1 : X ⟶ G).left = X.hom ≫ η[G].left := by
  have h1 : (toUnit X).left = X.hom := by simp
  show (toUnit X ≫ η[G]).left = _
  rw [Over.comp_left, h1]

private theorem left_comp_comp_hom_of_isGrpPullback {K : Type} [Field K] {S : Scheme.{0}} {x : Sp K ⟶ S} {G : Over S} {G' : Over (Sp K)}
    [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ) {T : Over (Sp K)} (y : T ⟶ G') :
    (y.left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ x)).hom := by
  simp only [Over.mk_hom, Category.assoc, h.1.w]
  rw [← Category.assoc, Over.w]

private theorem eq_one_of_left_eq_one_comp_of_isGrpPullback {K : Type} [Field K] {S : Scheme.{0}} {x : Sp K ⟶ S} {G : Over S} {G' : Over (Sp K)}
    [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ) {T : Over (Sp K)}
    (u₀ : Over.mk (T.hom ≫ x) ⟶ G) (hu : u₀.left = (1 : T ⟶ G').left ≫ φ) : u₀ = 1 := by
  have h2 := h.2 T 1 1 u₀ u₀ hu hu
  rw [_root_.mul_one, ← hu] at h2
  have h3 : u₀ * u₀ = u₀ := Over.OverMorphism.ext h2
  simpa using h3

private theorem list_prod_left_comp_of_isGrpPullback {K : Type} [Field K] {S : Scheme.{0}} {x : Sp K ⟶ S} {G : Over S} {G' : Over (Sp K)}
    [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ) {T : Over (Sp K)} :
    ∀ {m : ℕ} (u : Fin m → (T ⟶ G')) (u₀ : Fin m → (Over.mk (T.hom ≫ x) ⟶ G)),
      (∀ i, (u₀ i).left = (u i).left ≫ φ) → (List.ofFn u₀).prod.left = (List.ofFn u).prod.left ≫ φ := by
  intro m
  induction m with
  | zero =>
    intro u u₀ _
    simp only [List.ofFn_zero, List.prod_nil]
    have e0 : (Over.homMk ((1 : T ⟶ G').left ≫ φ) (left_comp_comp_hom_of_isGrpPullback h 1) : Over.mk (T.hom ≫ x) ⟶ G) = 1 :=
      eq_one_of_left_eq_one_comp_of_isGrpPullback h _ rfl
    rw [← e0]
    rfl
  | succ m ih =>
    intro u u₀ hu
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons]
    exact h.2 T _ _ _ _ (hu 0) (ih _ _ fun i => hu i.succ)

private theorem eq_of_left_comp_eq_of_isGrpPullback' {K : Type} [Field K] {S : Scheme.{0}} {x : Sp K ⟶ S} {G : Over S} {G' : Over (Sp K)}
    [GrpObj G] [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ) {T : Over (Sp K)} {u v : T ⟶ G'}
    (e : u.left ≫ φ = v.left ≫ φ) : u = v :=
  Over.OverMorphism.ext (h.1.hom_ext e (by rw [Over.w, Over.w]))

private theorem spMap_fstHom_comp_epsR_hom (K : Type) [Field K] :
    spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (epsR K).hom = 𝟙 (Sp K) := by
  have e1 : (TrivSqZeroExt.fstHom K K K).toRingHom.comp (algebraMap K (DualNumber K)) = RingHom.id K :=
    RingHom.ext fun _ => rfl
  show Spec.map (CommRingCat.ofHom _) ≫ Spec.map (CommRingCat.ofHom _) = 𝟙 _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, e1, CommRingCat.ofHom_id, Spec.map_id]

private theorem isLieComb_iff_eq_prodPts {K : Type} [Field K] {G' : Over (Sp K)} [GrpObj G'] {n : ℕ} (c : Fin n → K)
    (v : Fin n → (epsR K ⟶ G')) (y : epsR K ⟶ G') : IsLieComb c v y ↔ y = Chart.prodPts c v := by
  unfold IsLieComb
  constructor
  · rintro ⟨u, hu, rfl⟩
    have e1 : u = fun i => Chart.spMap (Chart.scaleD (c i)) ≫ v i := funext fun i => Over.OverMorphism.ext (hu i)
    rw [e1]
    rfl
  · rintro rfl
    exact ⟨fun i => Chart.spMap (Chart.scaleD (c i)) ≫ v i, fun i => rfl, rfl⟩

private theorem lieMult_of_finrank_eigenSub_eq {O K : Type} [CommRing O] [Field K] {S : Scheme.{0}} {x : Sp K ⟶ S} {G : Over S}
    {G' : Over (Sp K)} [GrpObj G] [GrpObj G'] [IsCommMonObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ)
    {n : ℕ} {v : Fin n → (epsR K ⟶ G')} (hv : IsLieBasis v) (act : OAct O G) (act' : OAct O G')
    (ha : ∀ a, (act'.act a).left ≫ φ = φ ≫ (act.act a).left) (ρ : O →+* Module.End K (Fin n → K))
    (hρ : ∀ a c, Chart.prodPts (ρ a c) v = Chart.prodPts c v ≫ act'.act a) (τ : O →+* K) (N : ℕ)
    (hN : Module.finrank K (GlobalTheory.EigenSplit.eigenSub ρ τ) = N) : LieMult act x τ N := by
  have hv0 := hv
  unfold IsLieBasis at hv0
  obtain ⟨hvt, hvu⟩ := hv0
  let P : (epsR K ⟶ G') → (epsPt x ⟶ G) := fun y => Over.homMk (y.left ≫ φ) (left_comp_comp_hom_of_isGrpPullback h y)
  have hP : ∀ y, (P y).left = y.left ≫ φ := fun y => rfl
  have hU : η[G'].left ≫ φ = x ≫ η[G].left := by
    have e1 := congrArg Over.Hom.left (eq_one_of_left_eq_one_comp_of_isGrpPullback h (T := epsR K) (P 1) rfl)
    rw [hP, isGrpPullback_one_left, isGrpPullback_one_left] at e1
    simp only [Over.mk_hom, Category.assoc] at e1
    have e2 := congrArg (fun t => spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ t) e1
    have hf1 : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 (Sp K) :=
      spMap_fstHom_comp_epsR_hom K
    simp only [← Category.assoc, hf1, Category.id_comp] at e2
    exact e2
  have hfstw : ∀ y : epsR K ⟶ G', (spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ y.left) ≫ G'.hom = 𝟙 _ := by
    intro y
    rw [Category.assoc, Over.w, spMap_fstHom_comp_epsR_hom]
  have hηw : η[G'].left ≫ G'.hom = 𝟙 _ := by
    exact Over.w η[G']
  have htan : ∀ y : epsR K ⟶ G', IsTangent y ↔
      spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (P y).left = (1 : Over.mk x ⟶ G).left := by
    intro y
    unfold IsTangent
    rw [hP, isGrpPullback_one_left]
    simp only [Over.mk_hom]
    constructor
    · intro hy
      rw [← Category.assoc, hy, hU]
    · intro hy
      apply h.1.hom_ext
      · rw [Category.assoc]
        exact hy.trans hU.symm
      · exact (hfstw y).trans hηw.symm
  have heig : ∀ (y : epsR K ⟶ G') (a : O) (s : K),
      (P y ≫ act.act a).left = spMap (epsScale s) ≫ (P y).left ↔ y ≫ act'.act a = Chart.spMap (Chart.scaleD s) ≫ y := by
    intro y a s
    have e1 : (P y ≫ act.act a).left = (y ≫ act'.act a).left ≫ φ := by
      simp only [Over.comp_left, Category.assoc, hP, ha]
    rw [e1, hP]
    constructor
    · intro e2
      apply eq_of_left_comp_eq_of_isGrpPullback' h
      rw [e2, Over.comp_left, Category.assoc]
      try rfl
    · intro e2
      rw [e2, Over.comp_left, Category.assoc]
      try rfl
  let B := Module.finBasisOfFinrankEq K (GlobalTheory.EigenSplit.eigenSub ρ τ) hN
  let e : Fin N → (epsR K ⟶ G') := fun i => Chart.prodPts ((B i : Fin n → K)) v
  have heS : ∀ c : Fin n → K, c ∈ GlobalTheory.EigenSplit.eigenSub ρ τ → ∀ a,
      Chart.prodPts c v ≫ act'.act a = Chart.spMap (Chart.scaleD (τ a)) ≫ Chart.prodPts c v := by
    intro c hc a
    rw [← hρ, GlobalTheory.EigenSplit.mem_eigenSub.1 hc a, GlobalTheory.LieEigen.prodPts_smul]
  have hlift : ∀ w : epsPt x ⟶ G, ∃ y, P y = w := by
    intro w
    refine ⟨Over.homMk (h.1.lift w.left (epsR K).hom (Over.w w)) (h.1.lift_snd _ _ _), ?_⟩
    apply Over.OverMorphism.ext
    exact h.1.lift_fst _ _ _
  have hsc : ∀ (d : K) (i : Fin N),
      (P (Chart.spMap (Chart.scaleD d) ≫ e i)).left = spMap (epsScale d) ≫ (P (e i)).left := by
    intro d i
    show (Chart.spMap (Chart.scaleD d) ≫ e i).left ≫ φ = spMap (epsScale d) ≫ (e i).left ≫ φ
    rw [Over.comp_left, Category.assoc]
    try rfl
  have hprod : ∀ (d : Fin N → K) (u : Fin N → (epsPt x ⟶ G)),
      (∀ i, (u i).left = spMap (epsScale (d i)) ≫ (P (e i)).left) →
        (List.ofFn u).prod = P (Chart.prodPts (∑ i, d i • (B i : Fin n → K)) v) := by
    intro d u hu
    apply Over.OverMorphism.ext
    rw [hP, ← GlobalTheory.LieEigen.prodPts_prodPts hvt d fun i => (B i : Fin n → K)]
    exact list_prod_left_comp_of_isGrpPullback h (fun i => Chart.spMap (Chart.scaleD (d i)) ≫ e i) u
      (fun i => by rw [hu i, ← hsc]; rfl)
  unfold LieMult
  refine ⟨fun i => P (e i), fun i => ?_, fun w hw => ?_⟩
  · unfold IsLieEigen
    exact ⟨(htan (e i)).1 (GlobalTheory.LieEigen.isTangent_prodPts hvt _),
      fun a => (heig (e i) a (τ a)).2 (heS _ (B i).2 a)⟩
  · unfold IsLieEigen at hw
    obtain ⟨hw0, hw1⟩ := hw
    obtain ⟨y, rfl⟩ := hlift w
    have hty : IsTangent y := (htan y).2 hw0
    have hye : ∀ a, y ≫ act'.act a = Chart.spMap (Chart.scaleD (τ a)) ≫ y := fun a => (heig y a (τ a)).1 (hw1 a)
    obtain ⟨c, hc, -⟩ := hvu y hty
    rw [isLieComb_iff_eq_prodPts] at hc
    subst hc
    have hcm : c ∈ GlobalTheory.EigenSplit.eigenSub ρ τ := by
      rw [GlobalTheory.EigenSplit.mem_eigenSub]
      intro a
      apply GlobalTheory.LieEigen.prodPts_injective hv
      show Chart.prodPts (ρ a c) v = Chart.prodPts (τ a • c) v
      rw [hρ, hye, GlobalTheory.LieEigen.prodPts_smul]
    let cc : GlobalTheory.EigenSplit.eigenSub ρ τ := ⟨c, hcm⟩
    have key : ∀ (d : Fin N → K) (u : Fin N → (epsPt x ⟶ G)),
        (∀ i, (u i).left = spMap (epsScale (d i)) ≫ (P (e i)).left) →
          (P (Chart.prodPts c v) = (List.ofFn u).prod ↔ d = B.repr cc) := by
      intro d u hu
      rw [hprod d u hu]
      constructor
      · intro hEq
        have h1 : Chart.prodPts c v = Chart.prodPts (∑ i, d i • (B i : Fin n → K)) v :=
          eq_of_left_comp_eq_of_isGrpPullback' h (congrArg Over.Hom.left hEq)
        have h2 := GlobalTheory.LieEigen.prodPts_injective hv h1
        have h3 : cc = ∑ i, d i • B i := by
          apply Subtype.ext
          rw [Submodule.coe_sum]
          simp only [Submodule.coe_smul]
          exact h2
        rw [h3, Module.Basis.repr_sum_self]
      · intro hd
        subst hd
        have h4 := congrArg Subtype.val (B.sum_repr cc)
        rw [Submodule.coe_sum] at h4
        simp only [Submodule.coe_smul] at h4
        exact congrArg (fun t => P (Chart.prodPts t v)) h4.symm
    refine ⟨fun i => B.repr cc i, ⟨fun i => P (Chart.spMap (Chart.scaleD (B.repr cc i)) ≫ e i), fun i => hsc _ i, ?_⟩, ?_⟩
    · exact (key _ _ fun i => hsc _ i).2 rfl
    · rintro d ⟨u, hu, hEq⟩
      exact (key d u hu).1 hEq

theorem GlobalTheory.exists_lie_coordinates_lieMult_iff : ∀ (O R : Type) [CommRing O] [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (act : OAct O G) (n : ℕ) (v : Fin n → (epsR R ⟶ G)), Smooth G.hom → IsLieBasis v → ∃ M : O →+* Module.End R (Fin n → R), ∀ (K : Type) [Field K] (f : R →+* K), ∃ M' : O →+* Module.End K (Fin n → K), (∀ a c, f ∘ M a c = M' a (f ∘ c)) ∧ ∀ (τ : O →+* K) (N : ℕ), LieMult act (spMap f) τ N ↔ Module.finrank K (GlobalTheory.EigenSplit.eigenSub M' τ) = N := by
  intro O R _ _ G _ _ act n v hs hv
  obtain ⟨M, hM⟩ := GlobalTheory.LieEigen.exists_action hv act
  refine ⟨M, fun K _ f => ?_⟩
  have hpb := isGrpPullback_pullback G (spMap f)
  obtain ⟨v', hv', hvv⟩ := GlobalTheory.exists_isLieBasis_baseChange R K f G ((Over.pullback (spMap f)).obj G)
    (pullback.fst G.hom (spMap f)) hpb hs n v hv
  obtain ⟨act', hact'⟩ := GlobalTheory.DetExtend.exists_oAct_pullback (spMap f) act
  have ha : ∀ a, (act'.act a).left ≫ pullback.fst G.hom (spMap f) =
      pullback.fst G.hom (spMap f) ≫ (act.act a).left := by
    intro a
    rw [hact']
    exact pullback.lift_fst _ _ _
  obtain ⟨M', hM'⟩ := GlobalTheory.LieEigen.exists_action hv' act'
  refine ⟨M', fun a c => GlobalTheory.LieEigen.action_baseChange hpb hv' hvv ha hM hM' a c, fun τ N => ⟨fun hN => ?_, fun hN => ?_⟩⟩
  · exact GlobalTheory.LieEigen.finrank_of_lieMult hpb hv' ha hM' hN
  · exact lieMult_of_finrank_eigenSub_eq hpb hv' act act' ha M' hM' τ N hN
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjectiveCoordinateRepresentationClosedSubsch
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjectiveCoordinateRepresentationClosedSubsch
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM.ClosedCoord
open MvPolynomial

theorem spMap_comp_eq {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem exists_ideal_factor {Y Z : Scheme.{0}} (i : Y ⟶ Z) [IsClosedImmersion i] {S : Type} [CommRing S]
    (x : Sp S ⟶ Z) : ∃ J : Ideal S, ∀ (R' : Type) [CommRing R'] (φ : S →+* R'),
      (∃ y : Sp R' ⟶ Y, y ≫ i = spMap φ ≫ x) ↔ ∀ f ∈ J, φ f = 0 := by
  obtain ⟨J, e, he⟩ := IsClosedImmersion.Spec_iff.1 (inferInstance : IsClosedImmersion (pullback.snd i x))
  refine ⟨J, fun R' _ φ => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy⟩ f hf
    obtain ⟨ψ, hψ⟩ := Spec.map_surjective (pullback.lift y (spMap φ) hy ≫ e.hom)
    have h1 : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ ψ) = spMap φ := by
      rw [Spec.map_comp, hψ, Category.assoc, ← he, pullback.lift_snd]
    have h2 := Spec.map_injective h1
    have h3 : ψ.hom (Ideal.Quotient.mk J f) = φ f := congrArg (fun t => t.hom f) h2
    rw [← h3, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
  · intro h
    refine ⟨spMap (Ideal.Quotient.lift J φ h) ≫ e.inv ≫ pullback.fst i x, ?_⟩
    rw [Category.assoc, Category.assoc, pullback.condition, he]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc]
    congr 1
    rw [← Spec.map_comp]; rfl

theorem exists_homogenisation {R σ : Type} [CommRing R] (a : σ) (F : MvPolynomial σ R) :
    ∃ (d : ℕ) (G : MvPolynomial σ R),
      (∀ (R' : Type) [CommRing R'] (β : R →+* R') (u : R') (w : σ → R'),
        eval₂ β (fun j => u * w j) G = u ^ d * eval₂ β w G) ∧
      ∀ (R' : Type) [CommRing R'] (β : R →+* R') (w : σ → R'), w a = 1 → eval₂ β w G = eval₂ β w F := by
  induction F using MvPolynomial.induction_on with
  | C c => exact ⟨0, C c, fun _ _ _ _ _ => by simp, fun _ _ _ _ _ => rfl⟩
  | add p q hp hq =>
    obtain ⟨d, G, h1, h2⟩ := hp
    obtain ⟨d', G', h1', h2'⟩ := hq
    refine ⟨d + d', X a ^ d' * G + X a ^ d * G', fun R' _ β u w => ?_, fun R' _ β w hw => ?_⟩
    · simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, h1, h1']; ring
    · simp only [eval₂_add, eval₂_mul, eval₂_pow, eval₂_X, h2 _ β w hw, h2' _ β w hw, hw]; ring
  | mul_X p n hp =>
    obtain ⟨d, G, h1, h2⟩ := hp
    refine ⟨d + 1, G * X n, fun R' _ β u w => ?_, fun R' _ β w hw => ?_⟩
    · simp only [eval₂_mul, eval₂_X, h1]; ring
    · simp only [eval₂_mul, eval₂_X, h2 _ β w hw]

theorem eq_zero_of_away {R' σ : Type} [CommRing R'] (v : σ → R') (hv : Ideal.span (Set.range v) = ⊤) (r : R')
    (h : ∀ a, algebraMap R' (Localization.Away (v a)) r = 0) : r = 0 := by
  have : r ∈ (⊥ : Ideal R') := by
    refine Submodule.mem_of_span_eq_top_of_smul_pow_mem _ (Set.range v) hv r ?_
    rintro ⟨_, a, rfl⟩
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (v a)) _ r).1 (h a)
    exact ⟨n, by simpa using hn⟩
  simpa using this

def awayUnit {R' : Type} [CommRing R'] (r : R') : (Localization.Away r)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away r) r).unit

theorem awayUnit_coe {R' : Type} [CommRing R'] (r : R') :
    (awayUnit r : Localization.Away r) = algebraMap R' _ r := rfl

theorem awayUnit_inv_mul {R' : Type} [CommRing R'] (r : R') :
    ((awayUnit r)⁻¹ : (Localization.Away r)ˣ) * algebraMap R' (Localization.Away r) r = 1 := by
  rw [← awayUnit_coe]; exact Units.inv_mul _

theorem away_of_vanishing {R σ : Type} [CommRing R] [Finite σ]
    (P : ∀ (R' : Type) [CommRing R'], (R →+* R') → (σ → R') → Prop)
    (bc : ∀ (R' R'' : Type) [CommRing R'] [CommRing R''] (φ : R' →+* R'') β v, P R' β v → P R'' (φ.comp β) (fun j => φ (v j)))
    (sc : ∀ (R' : Type) [CommRing R'] (u : R'ˣ) β v, P R' β v → P R' β (fun j => u * v j))
    (uni : ∀ (R' : Type) [CommRing R'] β v, P R' β v → Ideal.span (Set.range v) = ⊤)
    (ch : ∀ a, ∃ K : Ideal (MvPolynomial σ R), X a - 1 ∈ K ∧ ∀ (R' : Type) [CommRing R'] β w, w a = 1 →
      (P R' β w ↔ ∀ F ∈ K, eval₂ β w F = 0))
    (R' : Type) [CommRing R'] (β : R →+* R') (v : σ → R')
    (hv : ∀ F, (∀ (R'' : Type) [CommRing R''] β' w, P R'' β' w → eval₂ β' w F = 0) → eval₂ β v F = 0) (a : σ) :
    P (Localization.Away (v a)) ((algebraMap R' _).comp β) (fun j => algebraMap R' _ (v j)) := by
  classical
  choose K hK1 hK using ch
  have := Fintype.ofFinite σ

  have nrm : ∀ (A : Type) [CommRing A] β₀ (t : σ → A) (b : σ), P A β₀ t → ∀ F ∈ K b,
      eval₂ ((algebraMap A (Localization.Away (t b))).comp β₀)
        (fun j => ((awayUnit (t b))⁻¹ : (Localization.Away (t b))ˣ) * algebraMap A _ (t j)) F = 0 := by
    intro A _ β₀ t b ht
    exact (hK b _ _ _ (awayUnit_inv_mul _)).1 (sc _ _ _ _ (bc _ _ _ _ _ ht))
  suffices h : P (Localization.Away (v a)) ((algebraMap R' _).comp β)
      (fun j => ((awayUnit (v a))⁻¹ : (Localization.Away (v a))ˣ) * algebraMap R' _ (v j)) by
    have h2 := sc _ (awayUnit (v a)) _ _ h
    simpa only [Units.mul_inv_cancel_left] using h2
  refine (hK a _ _ _ (awayUnit_inv_mul _)).2 fun F hF => ?_
  obtain ⟨d, G, hG, hGF⟩ := exists_homogenisation a F
  have step : ∀ b, ∃ n : ℕ, X a ^ n * G ∈ K b := by
    intro b
    have hP : P (MvPolynomial σ R ⧸ K b) ((Ideal.Quotient.mk _).comp C) (fun j => Ideal.Quotient.mk _ (X j)) := by
      refine (hK b _ _ _ ?_).2 fun F' hF' => ?_
      · rw [← map_one (Ideal.Quotient.mk (K b)), Ideal.Quotient.eq]; exact hK1 b
      · have := (eval₂_comp_left (Ideal.Quotient.mk (K b)) C X F').symm
        rw [eval₂_eta, Ideal.Quotient.eq_zero_iff_mem.2 hF'] at this
        exact this
    have h1 := nrm _ _ _ a hP F hF
    rw [← hGF _ _ _ (awayUnit_inv_mul _), hG, (Units.isUnit _).pow d |>.mul_right_eq_zero] at h1
    have h2 := eval₂_comp_left (algebraMap _ (Localization.Away (Ideal.Quotient.mk (K b) (X a))))
      ((Ideal.Quotient.mk _).comp C) (fun j => Ideal.Quotient.mk (K b) (X j)) G
    have h3 := (eval₂_comp_left (Ideal.Quotient.mk (K b)) C X G)
    rw [eval₂_eta] at h3
    have h4 : algebraMap _ (Localization.Away (Ideal.Quotient.mk (K b) (X a))) (Ideal.Quotient.mk (K b) G) = 0 := by
      rw [h3]; exact h2.trans h1
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff
      (Submonoid.powers (Ideal.Quotient.mk (K b) (X a))) _ _).1 h4
    refine ⟨n, Ideal.Quotient.eq_zero_iff_mem.1 ?_⟩
    simpa using hn
  choose n hn using step
  have hH : eval₂ β v (X a ^ (∑ b, n b) * G) = 0 := by
    refine hv _ fun A _ β₀ t ht => eq_zero_of_away t (uni _ _ _ ht) _ fun b => ?_
    have hm : X a ^ (∑ b, n b) * G ∈ K b := by
      obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b))
      rw [hm, pow_add, _root_.mul_assoc]
      exact Ideal.mul_mem_left _ _ (hn b)
    have h1 := nrm _ _ _ b ht _ hm
    rw [eval₂_comp_left]
    rw [eval₂_mul, eval₂_pow, eval₂_X, hG, mul_pow, _root_.mul_mul_mul_comm, ← pow_add,
      (Units.isUnit _).pow _ |>.mul_right_eq_zero] at h1
    rw [eval₂_mul, eval₂_pow, eval₂_X]
    exact h1
  have h5 := congrArg (algebraMap R' (Localization.Away (v a))) hH
  rw [eval₂_mul, eval₂_pow, eval₂_X, map_mul, map_pow, map_zero, ← awayUnit_coe,
    (Units.isUnit _).pow _ |>.mul_right_eq_zero, eval₂_comp_left] at h5
  rw [← hGF _ _ _ (awayUnit_inv_mul _), hG]
  exact mul_eq_zero_of_right _ h5

theorem projRep_closed : ∀ (R σ : Type) [CommRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)) (Z Y : Scheme.{0}) (s : Z ⟶ Sp R) (M : LB Z) (th : σ → M.Sec) (i : Y ⟶ Z) (N : LB Y) (ty : σ → N.Sec), ProjRep I s M th → IsClosedImmersion i → N.IsLB → (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v ↔ SecCoord M th (y ≫ i) v) → ProjRep (idealOf (i ≫ s) N ty (𝟙 Y)) (i ≫ s) N ty := by
  intro R σ _ _ I Z Y s M th i N ty ⟨hM, hloc, hpts⟩ hi hN hc
  have mem : ∀ F, F ∈ idealOf (i ≫ s) N ty (𝟙 Y) ↔ ∀ (R' : Type) [CommRing R'] (β : R →+* R') (y : Sp R' ⟶ Y)
      (v : σ → R'), y ≫ i ≫ s = spMap β → SecCoord M th (y ≫ i) v → eval₂ β v F = 0 := by
    intro F
    simp only [idealOf, Ideal.mem_iInf, RingHom.mem_ker, coe_eval₂Hom, Category.comp_id, hc, and_imp]
  have hbc : ∀ (A B : Type) [CommRing A] [CommRing B] (φ : A →+* B) (x : Sp A ⟶ Z) (v : σ → A),
      SecCoord M th x v → SecCoord M th (spMap φ ≫ x) (fun j => φ (v j)) :=
    fun A B _ _ φ x v h => (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Z M σ th A x v hM h).1 B φ
  have huniq : ∀ (A : Type) [CommRing A] (β : R →+* A) (v : σ → A) (x x' : Sp A ⟶ Z), x ≫ s = spMap β →
      SecCoord M th x v → x' ≫ s = spMap β → SecCoord M th x' v → x = x' := by
    intro A _ β v x x' h1 h2 h3 h4
    obtain ⟨h5, h6⟩ := hloc A β x v h1 h2
    exact (hpts A β v h5 h6).unique ⟨h1, h2⟩ ⟨h3, h4⟩
  refine ⟨hN, fun R' _ β y v h1 h2 => ?_, fun R' _ β v hv hI => ?_⟩
  · rw [hc] at h2
    exact ⟨(hloc R' β (y ≫ i) v (by simpa using h1) h2).1, fun F hF => (mem F).1 hF R' β y v h1 h2⟩
  have hIv : ∀ F ∈ I, eval₂ β v F = 0 := fun F hF => hI F ((mem F).2 fun A _ β' y w h1 h2 =>
    (hloc A β' (y ≫ i) w (by simpa using h1) h2).2 F hF)
  obtain ⟨x, ⟨hx1, hx2⟩, -⟩ := hpts R' β v hv hIv
  have key := away_of_vanishing (R := R) (σ := σ)
    (fun A _ β' w => ∃ y : Sp A ⟶ Y, y ≫ i ≫ s = spMap β' ∧ SecCoord M th (y ≫ i) w)
    (by
      rintro A B _ _ φ β' w ⟨y, h1, h2⟩
      refine ⟨spMap φ ≫ y, by rw [Category.assoc, h1, spMap_comp_eq], ?_⟩
      rw [Category.assoc]; exact hbc _ _ φ _ _ h2)
    (by
      rintro A _ u β' w ⟨y, h1, h2⟩
      exact ⟨y, h1, (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique Z M σ th A _ w hM h2).2.1 u⟩)
    (by
      rintro A _ β' w ⟨y, h1, h2⟩
      exact (hloc A β' (y ≫ i) w (by simpa using h1) h2).1)
    (by
      intro a
      have hq : ∀ F, eval₂ ((Ideal.Quotient.mk (I ⊔ Ideal.span {X a - 1})).comp C)
          (fun j => Ideal.Quotient.mk _ (X j)) F = Ideal.Quotient.mk (I ⊔ Ideal.span {X a - 1}) F := by
        intro F
        have := (eval₂_comp_left (Ideal.Quotient.mk (I ⊔ Ideal.span {X a - 1})) C X F).symm
        rw [eval₂_eta] at this
        exact this
      have ha : X a - 1 ∈ I ⊔ Ideal.span {X a - 1} := Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
      obtain ⟨xa, ⟨hxa1, hxa2⟩, -⟩ := hpts (MvPolynomial σ R ⧸ (I ⊔ Ideal.span {X a - 1}))
        ((Ideal.Quotient.mk _).comp C) (fun j => Ideal.Quotient.mk _ (X j))
        (by
          rw [Ideal.eq_top_iff_one]
          refine Ideal.subset_span ⟨a, ?_⟩
          rw [← map_one (Ideal.Quotient.mk (I ⊔ Ideal.span {X a - 1}))]
          exact Ideal.Quotient.eq.2 ha)
        (fun F hF => by rw [hq]; exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_left hF))
      obtain ⟨J, hJ⟩ := exists_ideal_factor i xa
      have hle : ∀ F ∈ I ⊔ Ideal.span {X a - 1}, F ∈ J.comap (Ideal.Quotient.mk (I ⊔ Ideal.span {X a - 1})) := by
        intro F hF
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hF]; exact J.zero_mem
      refine ⟨J.comap (Ideal.Quotient.mk _), hle _ ha, fun A _ β' w hw => ?_⟩
      have main : ∀ h : ∀ F ∈ I ⊔ Ideal.span {X a - 1}, eval₂Hom β' w F = 0,
          (spMap (Ideal.Quotient.lift _ _ h) ≫ xa) ≫ s = spMap β' ∧
            SecCoord M th (spMap (Ideal.Quotient.lift _ _ h) ≫ xa) w := by
        intro h
        refine ⟨?_, ?_⟩
        · rw [Category.assoc, hxa1, spMap_comp_eq]
          congr 1
          ext r
          simp
        · have := hbc _ _ (Ideal.Quotient.lift _ _ h) _ _ hxa2
          simpa using this
      constructor
      · rintro ⟨y, h1, h2⟩ F hF
        have h : ∀ F ∈ I ⊔ Ideal.span {X a - 1}, eval₂Hom β' w F = 0 := by
          intro F hF
          have hle' : I ⊔ Ideal.span {X a - 1} ≤ RingHom.ker (eval₂Hom β' w) := by
            refine sup_le (fun F hF => (hloc A β' (y ≫ i) w (by simpa using h1) h2).2 F hF) ?_
            rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker]
            simp [hw]
          exact hle' hF
        have e := huniq A β' w _ _ (by simpa using h1) h2 (main h).1 (main h).2
        exact (hJ A _).1 ⟨y, e⟩ _ hF
      · intro hF
        have h : ∀ F ∈ I ⊔ Ideal.span {X a - 1}, eval₂Hom β' w F = 0 := fun F h => hF F (hle F h)
        obtain ⟨y, hy⟩ := (hJ A (Ideal.Quotient.lift _ _ h)).2 (by
          intro f hf
          obtain ⟨F, rfl⟩ := Ideal.Quotient.mk_surjective f
          exact hF F hf)
        exact ⟨y, by rw [← Category.assoc, hy]; exact (main h).1, by rw [hy]; exact (main h).2⟩)
    R' β v (fun F hF => hI F ((mem F).2 fun A _ β' y w h1 h2 => hF A β' w ⟨y, h1, h2⟩))
  obtain ⟨J, hJ⟩ := exists_ideal_factor i x
  obtain ⟨y, hy⟩ := (hJ R' (RingHom.id R')).2 (by
    intro f hf
    refine eq_zero_of_away v hv f fun a => ?_
    obtain ⟨y, h1, h2⟩ := key a
    refine (hJ _ (algebraMap R' _)).1 ⟨y, ?_⟩ f hf
    refine huniq _ _ _ _ _ (by simpa using h1) h2 ?_ (hbc _ _ _ _ _ hx2)
    rw [Category.assoc, hx1, spMap_comp_eq])
  have hid : spMap (RingHom.id R') = 𝟙 (Sp R') := Spec.map_id _
  rw [hid, Category.id_comp] at hy
  refine ⟨y, ⟨by rw [← Category.assoc, hy, hx1], by rw [hc, hy]; exact hx2⟩, ?_⟩
  rintro y' ⟨h1, h2⟩
  rw [hc] at h2
  rw [← cancel_mono i, hy]
  exact huniq _ _ _ _ _ (by simpa using h1) h2 hx1 hx2

end GlobalTheory.ZM.ClosedCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjectiveCoordinateRepresentationClosedSubschStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProjectiveCoordinateRepresentation_closedSubscheme : ∀ (R σ : Type) [CommRing R] [Finite σ] (I : Ideal (MvPolynomial σ R)) (Z Y : Scheme.{0}) (s : Z ⟶ Sp R) (M : LB Z) (th : σ → M.Sec) (i : Y ⟶ Z) (N : LB Y) (ty : σ → N.Sec), ProjRep I s M th → IsClosedImmersion i → N.IsLB → (∀ (R' : Type) [CommRing R'] (y : Sp R' ⟶ Y) (v : σ → R'), SecCoord N ty y v ↔ SecCoord M th (y ≫ i) v) → ProjRep (idealOf (i ≫ s) N ty (𝟙 Y)) (i ≫ s) N ty := by
  first | exact @GlobalTheory.ZM.ClosedCoord.projRep_closed | exact GlobalTheory.ZM.ClosedCoord.projRep_closed | (intros; apply GlobalTheory.ZM.ClosedCoord.projRep_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GrpObjOfDenseFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.FibreGrp

theorem hom_ext_of_fibres {S : Scheme.{0}} [IsReduced S] {Sg : Set S} (hSg : Dense Sg) {X Y : Over S}
    [Smooth X.hom] [IsSeparated Y.hom] {f g : X ⟶ Y}
    (h : ∀ p ∈ Sg, ∃ (U : Scheme.{0}) (j : U ⟶ S), p ∈ Set.range j ∧
      ∀ (T : Over U) (t : Over.mk (T.hom ≫ j) ⟶ X), t ≫ f = t ≫ g) : f = g := by
  have : IsReduced X.left := GlobalTheory.isReduced_of_smooth_of_isReduced X.hom
  choose U j hj hfg using h
  let incl : (∐ fun q : Sg => pullback X.hom (j q.1 q.2)) ⟶ X.left :=
    Sigma.desc fun q : Sg => pullback.fst X.hom (j q.1 q.2)
  have hincl : ∀ q : Sg, Sigma.ι (fun q : Sg => pullback X.hom (j q.1 q.2)) q ≫ incl =
      pullback.fst X.hom (j q.1 q.2) := fun q => Sigma.ι_desc _ q
  have hdense : Dense (X.hom ⁻¹' Sg) := hSg.preimage X.hom.isOpenMap
  have : IsDominant incl := by
    refine ⟨Dense.mono ?_ hdense⟩
    intro x hx
    have hx' : x ∈ Set.range (pullback.fst X.hom (j _ hx)) := by
      rw [Scheme.Pullback.range_fst]
      exact hj _ hx
    obtain ⟨y, hy⟩ := hx'
    refine ⟨Sigma.ι (fun q : Sg => pullback X.hom (j q.1 q.2)) ⟨_, hx⟩ y, ?_⟩
    rw [← Scheme.Hom.comp_apply, hincl]
    exact hy
  apply Over.OverMorphism.ext
  refine ext_of_isDominant_of_isSeparated Y.hom (by rw [Over.w f, Over.w g]) incl ?_
  refine Sigma.hom_ext _ _ fun q => ?_
  rw [← Category.assoc, hincl, ← Category.assoc, hincl]
  have key := hfg q.1 q.2 (Over.mk (pullback.snd X.hom (j q.1 q.2)))
    (Over.homMk (pullback.fst X.hom (j q.1 q.2)) (by simp only [Over.mk_hom]; exact pullback.condition))
  exact congrArg CommaMorphism.left key

private theorem smooth_tensor_hom {S : Scheme.{0}} (P Q : Over S) [Smooth P.hom] [Smooth Q.hom] :
    Smooth (P ⊗ Q).hom := by
  change Smooth (pullback.fst P.hom Q.hom ≫ P.hom)
  infer_instance

private theorem smooth_tensorUnit_hom (S : Scheme.{0}) : Smooth (𝟙_ (Over S)).hom := by
  change Smooth (𝟙 S)
  infer_instance

private theorem eq_of_points_lemma_3 {R : Type} [CommRing R] [IsReduced R] {Z : Over (Sp R)} [IsSeparated Z.hom]
    {m : Z ⊗ Z ⟶ Z} {i : Z ⟶ Z} {e : 𝟙_ (Over (Sp R)) ⟶ Z} {Sg : Set (Sp R)} (hSg : Dense Sg)
    (hfib : ∀ p ∈ Sg, ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Sp R) (A : Over (Sp K)) (_ : GrpObj A) (φ : A.left ⟶ Z.left), p ∈ Set.range x ∧ IsCommMonObj A ∧ IsPullback φ A.hom Z.hom x ∧ (∀ φ₂ : (A ⊗ A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ) ∧ φ ≫ i.left = (ι[A]).left ≫ φ ∧ x ≫ e.left = (η[A]).left ≫ φ)
    {P : Over (Sp R)} [Smooth P.hom] {u v : P ⟶ Z}
    (H : ∀ (K : Type) [Field K] (x : Sp K ⟶ Sp R) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A]
      (φ : A.left ⟶ Z.left), IsPullback φ A.hom Z.hom x →
      (∀ φ₂ : (A ⊗ A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ) →
      φ ≫ i.left = (ι[A]).left ≫ φ → x ≫ e.left = (η[A]).left ≫ φ →
      ∀ (T : Over (Sp K)) (t : Over.mk (T.hom ≫ x) ⟶ P), t ≫ u = t ≫ v) : u = v := by
  refine hom_ext_of_fibres hSg fun p hp => ?_
  obtain ⟨K, _, x, A, _, φ, hx, hc, pb, hm, hi, he⟩ := hfib p hp
  exact ⟨Sp K, x, hx, H K x A φ pb hm hi he⟩

end GlobalTheory.FibreGrp

namespace GlobalTheory

open GrpDense FibreGrp

theorem grpObj_of_dense_fibres :
    ∀ (R : Type) [CommRing R] [IsReduced R] (Z : Over (Sp R)) (m : Z ⊗ Z ⟶ Z) (i : Z ⟶ Z) (e : 𝟙_ (Over (Sp R)) ⟶ Z) (Sg : Set (Sp R)), Dense Sg → Smooth Z.hom → IsProper Z.hom → GeometricallyConnected Z.hom → (∀ p ∈ Sg, ∃ (K : Type) (_ : Field K) (x : Sp K ⟶ Sp R) (A : Over (Sp K)) (_ : GrpObj A) (φ : A.left ⟶ Z.left), p ∈ Set.range x ∧ IsCommMonObj A ∧ IsPullback φ A.hom Z.hom x ∧ (∀ φ₂ : (A ⊗ A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ) ∧ φ ≫ i.left = (ι[A]).left ≫ φ ∧ x ≫ e.left = (η[A]).left ≫ φ) → ∃ _ : GrpObj Z, μ[Z] = m ∧ η[Z] = e ∧ ι[Z] = i ∧ IsAbelianScheme Z ∧ ∀ (S' : Scheme.{0}) (x : S' ⟶ Sp R) (A : Over S') [GrpObj A] (φ : A.left ⟶ Z.left), IsPullback φ A.hom Z.hom x → (∀ φ₂ : (A ⊗ A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[A]).left ≫ φ) → IsGrpPullback A Z x φ := by
  intro R _ _ Z m i e Sg hSg hsm hpr hgc hfib
  have : Smooth Z.hom := hsm
  have : IsProper Z.hom := hpr
  have : Smooth (𝟙_ (Over (Sp R))).hom := smooth_tensorUnit_hom (Sp R)
  have : Smooth (Z ⊗ Z).hom := smooth_tensor_hom Z Z
  have : Smooth (𝟙_ (Over (Sp R)) ⊗ Z).hom := smooth_tensor_hom _ _
  have : Smooth (Z ⊗ 𝟙_ (Over (Sp R))).hom := smooth_tensor_hom _ _
  have : Smooth ((Z ⊗ Z) ⊗ Z).hom := smooth_tensor_hom _ _
  have one_mul' : e ▷ Z ≫ m = (λ_ Z).hom := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨c, hc⟩ := GrpDense.pushPt_surjective pb T (t ≫ snd (𝟙_ (Over (Sp R))) Z)
    rw [← lift_comp_fst_snd t, toUnit_unique (t ≫ fst (𝟙_ (Over (Sp R))) Z) (toUnit _),
      lift_whiskerRight_assoc, lift_leftUnitor_hom, ← hc, GrpDense.pushPt_one pb.w he T,
      GrpDense.pushPt_mul pb.w hm, _root_.one_mul]
  have mul_one' : Z ◁ e ≫ m = (ρ_ Z).hom := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨c, hc⟩ := GrpDense.pushPt_surjective pb T (t ≫ fst Z (𝟙_ (Over (Sp R))))
    rw [← lift_comp_fst_snd t, toUnit_unique (t ≫ snd Z (𝟙_ (Over (Sp R)))) (toUnit _),
      lift_whiskerLeft_assoc, lift_rightUnitor_hom, ← hc, GrpDense.pushPt_one pb.w he T,
      GrpDense.pushPt_mul pb.w hm, _root_.mul_one]
  have mul_assoc' : m ▷ Z ≫ m = (α_ Z Z Z).hom ≫ Z ◁ m ≫ m := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨a, ha⟩ := GrpDense.pushPt_surjective pb T (t ≫ fst (Z ⊗ Z) Z ≫ fst Z Z)
    obtain ⟨b, hb⟩ := GrpDense.pushPt_surjective pb T (t ≫ fst (Z ⊗ Z) Z ≫ snd Z Z)
    obtain ⟨c, hc⟩ := GrpDense.pushPt_surjective pb T (t ≫ snd (Z ⊗ Z) Z)
    have ht : t = lift (lift (pushPt pb.w a) (pushPt pb.w b)) (pushPt pb.w c) := by
      rw [ha, hb, hc]
      simp only [← Category.assoc, lift_comp_fst_snd]
    rw [ht]
    simp only [lift_whiskerRight_assoc, lift_lift_associator_hom_assoc, lift_whiskerLeft_assoc,
      GrpDense.pushPt_mul pb.w hm, _root_.mul_assoc]
  have left_inv' : lift i (𝟙 Z) ≫ m = toUnit Z ≫ e := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨c, rfl⟩ := GrpDense.pushPt_surjective pb T t
    rw [comp_lift_assoc, Category.comp_id, GrpDense.pushPt_inv pb.w hi, GrpDense.pushPt_mul pb.w hm,
      ← Category.assoc (pushPt pb.w c) (toUnit Z) e, toUnit_unique (pushPt pb.w c ≫ toUnit Z) (toUnit _),
      GrpDense.pushPt_one pb.w he T, _root_.inv_mul_cancel]
  have right_inv' : lift (𝟙 Z) i ≫ m = toUnit Z ≫ e := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨c, rfl⟩ := GrpDense.pushPt_surjective pb T t
    rw [comp_lift_assoc, Category.comp_id, GrpDense.pushPt_inv pb.w hi, GrpDense.pushPt_mul pb.w hm,
      ← Category.assoc (pushPt pb.w c) (toUnit Z) e, toUnit_unique (pushPt pb.w c ≫ toUnit Z) (toUnit _),
      GrpDense.pushPt_one pb.w he T, _root_.mul_inv_cancel]
  have comm' : (β_ Z Z).hom ≫ m = m := by
    refine eq_of_points_lemma_3 hSg hfib ?_
    intro K _ x A _ _ φ pb hm hi he T t
    obtain ⟨a, ha⟩ := GrpDense.pushPt_surjective pb T (t ≫ fst Z Z)
    obtain ⟨b, hb⟩ := GrpDense.pushPt_surjective pb T (t ≫ snd Z Z)
    have ht : t = lift (pushPt pb.w a) (pushPt pb.w b) := by rw [ha, hb, lift_comp_fst_snd]
    rw [ht, lift_braiding_hom_assoc, GrpDense.pushPt_mul pb.w hm, GrpDense.pushPt_mul pb.w hm, _root_.mul_comm]
  let G : GrpObj Z :=
    { one := e, mul := m, one_mul := one_mul', mul_one := mul_one', mul_assoc := mul_assoc',
      inv := i, left_inv := left_inv', right_inv := right_inv' }
  refine ⟨G, rfl, rfl, rfl, ?_, ?_⟩
  · exact { comm := ⟨comm'⟩, smooth := hsm, proper := hpr, geomConnected := hgc }
  · intro S' x A _ φ pb hm'
    refine ⟨pb, fun T a b a₀ b₀ ha hb => ?_⟩
    have ea : a₀ = pushPt pb.w a := Over.OverMorphism.ext ha
    have eb : b₀ = pushPt pb.w b := Over.OverMorphism.ext hb
    subst ea eb
    exact congrArg CommaMorphism.left (GrpDense.pushPt_mul pb.w hm' a b)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ResidueGeneric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoordChart

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (h : B →+* C) :
    spMap h ≫ spMap f = spMap (h.comp f) := by
  unfold spMap
  rw [← Spec.map_comp]; rfl

theorem sp_inj {A B : Type} [CommRing A] [CommRing B] {f h : A →+* B} (e : spMap f = spMap h) : f = h := by
  have := Spec.map_injective e
  exact congrArg CommRingCat.Hom.hom this

theorem sp_surj {A B : Type} [CommRing A] [CommRing B] (z : Sp B ⟶ Sp A) : ∃ f : A →+* B, spMap f = z :=
  ⟨(Spec.preimage z).hom, Spec.map_preimage z⟩

theorem lift_chart {o : Type} [CommRing o] {g n N' : ℕ} {I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)}
    (Y : MMPre n N' I) {R : Type} [CommRing R] (β : o →+* R) (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R)
    {K : Type} [Field K] (y : R →+* K) [IsOpenImmersion x] (hx : x ≫ Y.s = spMap β)
    (hv : SecCoord Y.de Y.th x v) (c : Kˣ)
    {L : Type} [CommRing L] (ψ : L →+* K) (hψ : ∀ l, ψ l ≠ 0 → IsUnit l) (β' : o →+* L)
    (w : Ix g (N' ^ 2) → L) (hβ : ψ.comp β' = y.comp β) (hw : ∀ a, ψ (w a) = c * y (v a))
    (hI : ∀ F ∈ I, MvPolynomial.eval₂ β' w F = 0) :
    ∃ φ : R →+* L, ψ.comp φ = y ∧ φ.comp β = β' ∧ ∃ u : Lˣ, ∀ a, w a = u * φ (v a) := by
  have h1 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hv).1 K y
  have h2 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB h1).2.1 c
  have h3 : (spMap y ≫ x) ≫ Y.s = spMap (y.comp β) := by rw [Category.assoc, hx, sp_comp]
  have hK := Y.loc K _ _ _ h3 h2
  have hL : InMM n N' I β' w := by
    refine ⟨hI, fun q hq a => ?_⟩
    obtain ⟨d, hd⟩ := hK.2 ⊥ Ideal.isPrime_bot a
    refine ⟨d, fun hm => hq.ne_top (Ideal.eq_top_of_isUnit_mem _ hm (hψ _ ?_))⟩
    rw [hw]
    simpa using hd
  obtain ⟨z, ⟨hz1, hz2⟩, -⟩ := Y.pts L β' w hL
  have h4 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hz2).1 K ψ
  have h5 : (spMap ψ ≫ z) ≫ Y.s = spMap (y.comp β) := by rw [Category.assoc, hz1, sp_comp, hβ]
  have heq : spMap ψ ≫ z = spMap y ≫ x := by
    refine (Y.pts K _ _ hK).unique ⟨h5, ?_⟩ ⟨h3, h2⟩
    simpa only [hw] using h4
  have hr : Set.range z ⊆ Set.range x := by
    rintro _ ⟨p, rfl⟩
    let p₀ : Sp K := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K)
    have hs : p ⤳ spMap ψ p₀ := by
      refine (PrimeSpectrum.le_iff_specializes (R := L) p (spMap ψ p₀)).1 ?_
      intro l hl
      change ψ l ∈ (⊥ : Ideal K)
      by_contra hne
      exact p.2.ne_top (Ideal.eq_top_of_isUnit_mem _ hl (hψ _ (by simpa using hne)))
    refine (hs.map z.continuous).mem_open x.isOpenEmbedding.isOpen_range ⟨spMap y p₀, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, heq]
  obtain ⟨φ, hφ⟩ := sp_surj (IsOpenImmersion.lift x z hr)
  have hz : spMap φ ≫ x = z := by rw [hφ, IsOpenImmersion.lift_fac]
  refine ⟨φ, sp_inj ?_, sp_inj ?_, ?_⟩
  · rw [← cancel_mono x, ← sp_comp, Category.assoc, hz, heq]
  · rw [← sp_comp, ← hx, ← Category.assoc, hz, hz1]
  · have h6 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hv).1 L φ
    rw [hz] at h6
    exact (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB h6).2.2 w hz2

theorem clear_denom {o σ R L : Type} [CommRing o] [CommRing R] [CommRing L] (β : o →+* R) (φ : R →+* L)
    (v : σ → R) (w : σ → L) (t : R) (h : ∀ a, w a * φ t = φ (v a)) (F : MvPolynomial σ o) :
    ∃ (r : R) (m : ℕ), MvPolynomial.eval₂ (φ.comp β) w F * φ t ^ m = φ r := by
  induction F using MvPolynomial.induction_on with
  | C c => exact ⟨β c, 0, by simp⟩
  | add p q hp hq =>
    obtain ⟨r, m, h1⟩ := hp
    obtain ⟨r', m', h2⟩ := hq
    refine ⟨r * t ^ m' + r' * t ^ m, m + m', ?_⟩
    rw [MvPolynomial.eval₂_add, map_add (f := _), map_mul, map_mul, ← h1, ← h2, map_pow, map_pow]
    ring
  | mul_X p a hp =>
    obtain ⟨r, m, h1⟩ := hp
    refine ⟨r * v a, m + 1, ?_⟩
    rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X, map_mul, ← h1, ← h a]
    ring

theorem residue_generic : ∀ (o : Type) [CommRing o] (g n N' : ℕ) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) o)) (Y : MMPre n N' I) (R : Type) [CommRing R] (β : o →+* R) (x : Sp R ⟶ Y.MM) (v : Ix g (N' ^ 2) → R) (K : Type) [Field K] (y : R →+* K) (a₀ : Ix g (N' ^ 2)), 0 < N' → IsOpenImmersion x → x ≫ Y.s = spMap β → SecCoord Y.de Y.th x v → (∀ k : K, ∃ r r' : R, y r' ≠ 0 ∧ k * y r' = y r) → y (v a₀) ≠ 0 → Subfield.closure (Set.range (y.comp β) ∪ Set.range (fun a => y (v a) / y (v a₀))) = ⊤ ∧ (RingHom.ker y ∈ minimalPrimes R → RingHom.ker (MvPolynomial.eval₂Hom (y.comp β) (fun a => y (v a) / y (v a₀))) ∈ (I ⊔ Ideal.span {MvPolynomial.X a₀ - 1}).minimalPrimes) := by
  intro o _ g n N' I Y R _ β x v K _ y a₀ _ hox hx hv hfr h0
  let c : Kˣ := (Units.mk0 _ h0)⁻¹
  have hc : ∀ a, y (v a) / y (v a₀) = c * y (v a) := fun a => by
    simp [c, div_eq_inv_mul]
  have h1 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB hv).1 K y
  have h2 := (GlobalTheory.ZM.Coord.secCoord_bc_scale_unique _ _ _ _ _ _ _ Y.isLB h1).2.1 c
  have h3 : (spMap y ≫ x) ≫ Y.s = spMap (y.comp β) := by rw [Category.assoc, hx, sp_comp]
  have hK : ∀ F ∈ I, MvPolynomial.eval₂ (y.comp β) (fun a => y (v a) / y (v a₀)) F = 0 := by
    simpa only [hc] using (Y.loc K _ _ _ h3 h2).1
  constructor
  · set E := Subfield.closure (Set.range (y.comp β) ∪ Set.range (fun a => y (v a) / y (v a₀))) with hE
    let β' : o →+* E := (y.comp β).codRestrict E fun t => Subfield.subset_closure (Or.inl ⟨t, rfl⟩)
    let w : Ix g (N' ^ 2) → E := fun a => ⟨y (v a) / y (v a₀), Subfield.subset_closure (Or.inr ⟨a, rfl⟩)⟩
    obtain ⟨φ, hφ, -⟩ := lift_chart Y β x v y hx hv c E.subtype
      (fun l hl => IsUnit.mk0 l (fun h => hl (by rw [h, map_zero]))) β' w rfl (fun a => hc a) (by
        intro F hF
        apply E.subtype.injective
        rw [MvPolynomial.eval₂_comp_left, map_zero]
        exact hK F hF)
    have hy : ∀ r, y r ∈ E := fun r => by rw [← hφ]; exact (φ r).2
    rw [eq_top_iff]
    intro k _
    obtain ⟨r, r', hr, hk⟩ := hfr k
    rw [eq_div_of_mul_eq hr hk]
    exact E.div_mem (hy r) (hy r')
  · intro hmin
    set ev := MvPolynomial.eval₂Hom (y.comp β) (fun a => y (v a) / y (v a₀)) with hev
    refine ⟨⟨RingHom.ker_isPrime ev, sup_le (fun F hF => hK F hF) ?_⟩, ?_⟩
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      change ev _ = 0
      simp [hev, h0]
    rintro P ⟨hP, hJ⟩ hle
    let e : (MvPolynomial (Ix g (N' ^ 2)) o ⧸ P) →+* K := Ideal.Quotient.lift P ev fun a ha => hle ha
    haveI : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
    let L := Localization.AtPrime (RingHom.ker e)
    have hu : ∀ s : (RingHom.ker e).primeCompl, IsUnit (e s) := fun s => IsUnit.mk0 _ s.2
    let ψ : L →+* K := IsLocalization.lift (M := (RingHom.ker e).primeCompl) hu
    let π : MvPolynomial (Ix g (N' ^ 2)) o →+* L := (algebraMap _ L).comp (Ideal.Quotient.mk P)
    have hπ : ∀ F, ψ (π F) = ev F := fun F => by
      simp only [ψ, π, RingHom.comp_apply, IsLocalization.lift_eq]
      rfl
    have hπe : ∀ F, MvPolynomial.eval₂ (π.comp MvPolynomial.C) (fun a => π (MvPolynomial.X a)) F = π F := fun F => by
      conv_rhs => rw [← MvPolynomial.eval₂_eta F, MvPolynomial.eval₂_comp_left]
      rfl
    have hπ0 : ∀ F, π F = 0 ↔ F ∈ P := fun F => by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact map_eq_zero_iff _ (IsLocalization.injective L (RingHom.ker e).primeCompl_le_nonZeroDivisors)
    have hψ : ∀ l, ψ l ≠ 0 → IsUnit l := by
      intro l hl
      obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker e).primeCompl l
      rw [IsLocalization.AtPrime.isUnit_mk'_iff L (RingHom.ker e)]
      intro ha
      apply hl
      change ψ (IsLocalization.mk' L a s) = 0
      rw [IsLocalization.lift_mk'_spec, mul_zero]
      exact ha
    obtain ⟨φ, hφ, hβ, u, hw⟩ := lift_chart Y β x v y hx hv c ψ hψ (π.comp MvPolynomial.C)
      (fun a => π (MvPolynomial.X a)) (by ext t; simp [hπ, hev]) (fun a => by rw [hπ, ← hc]; simp [hev])
      (fun F hF => by rw [hπe, hπ0]; exact hJ (Ideal.mem_sup_left hF))
    have hone : (u : L) * φ (v a₀) = 1 := by
      rw [← hw, ← sub_eq_zero, ← map_one π, ← map_sub, hπ0]
      exact hJ (Ideal.mem_sup_right (Ideal.subset_span rfl))
    have hker : RingHom.ker y ≤ RingHom.ker φ :=
      hmin.2 ⟨RingHom.ker_isPrime φ, bot_le⟩ (fun r hr => by
        rw [RingHom.mem_ker] at hr ⊢
        rw [← hφ, RingHom.comp_apply, hr, map_zero])
    intro F hF
    obtain ⟨r, m, hr⟩ := clear_denom β φ v (fun a => π (MvPolynomial.X a)) (v a₀)
      (fun a => by
        change π (MvPolynomial.X a) * _ = _
        rw [hw a, mul_right_comm, hone, _root_.one_mul]) F
    rw [hβ, hπe] at hr
    have hyr : r ∈ RingHom.ker y := by
      rw [RingHom.mem_ker] at hF ⊢
      rw [← hφ, RingHom.comp_apply, ← hr, map_mul, hπ, hF, zero_mul]
    have hφr : φ r = 0 := hker hyr
    rw [hφr] at hr
    rw [← hπ0]
    exact ((IsUnit.of_mul_eq_one_right _ hone).pow m).mul_left_eq_zero.1 hr

end GlobalTheory.CoordChart
end
