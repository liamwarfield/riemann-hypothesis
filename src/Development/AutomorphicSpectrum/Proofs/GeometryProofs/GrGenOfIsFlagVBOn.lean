module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flag

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

private theorem div_mem_of_mem_span_singleton {R : Subring Ω} {x y : Ω} (hy : y ≠ 0)
    (h : x ∈ Submodule.span R {y}) : x / y ∈ R := by
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp h
  have e : r • y = (r : Ω) * y := rfl
  rw [← hr, e, mul_div_assoc, div_self hy, mul_one]
  exact r.2

private theorem zpow_mem_lemma_2 {R : Subring Ω} {x : Ω} (hx : x ∈ R) (hxi : x⁻¹ ∈ R) (n : ℤ) :
    x ^ n ∈ R := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_natCast, zpow_natCast]; exact pow_mem hx n
  | negSucc n => rw [zpow_negSucc, ← inv_pow]; exact pow_mem hxi _

theorem tens_gen {I : Type} [Fintype I] (Λ : I → Lat ξ Ω) (a : I → ℤ) (p : Cpt ξ) (s : I → Ω)
    (hs : ∀ i, (Λ i).IsGenAt p (s i)) : (Lat.tens Λ a).IsGenAt p (∏ i, s i ^ a i) := by
  have hs0 : ∀ i, s i ≠ 0 := fun i => (hs i).1
  refine ⟨Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (hs0 i), ?_⟩
  show Submodule.span (regAt ξ p) {t | ∃ s' : I → Ω, (∀ i, (Λ i).IsGenAt p (s' i)) ∧ t = ∏ i, s' i ^ a i} = _
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro t ⟨s', hs', rfl⟩
    have hs'0 : ∀ i, s' i ≠ 0 := fun i => (hs' i).1
    have hw : ∀ i, s' i / s i ∈ regAt ξ p := fun i => by
      refine div_mem_of_mem_span_singleton (hs0 i) ?_
      rw [← (hs i).2, (hs' i).2]
      exact Submodule.mem_span_singleton_self _
    have hwi : ∀ i, (s' i / s i)⁻¹ ∈ regAt ξ p := fun i => by
      rw [inv_div]
      refine div_mem_of_mem_span_singleton (hs'0 i) ?_
      rw [← (hs' i).2, (hs i).2]
      exact Submodule.mem_span_singleton_self _
    have hc : ∏ i, (s' i / s i) ^ a i ∈ regAt ξ p :=
      prod_mem fun i _ => zpow_mem_lemma_2 (hw i) (hwi i) (a i)
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨⟨_, hc⟩, ?_⟩
    show (∏ i, (s' i / s i) ^ a i) * ∏ i, s i ^ a i = ∏ i, s' i ^ a i
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← mul_zpow, div_mul_cancel₀ _ (hs0 i)]
  · apply Submodule.span_mono
    rw [Set.singleton_subset_iff]
    exact ⟨s, hs, rfl⟩

variable {E : Type} [AddCommGroup E] [Module Ω E]

theorem step_succ {r : ℕ} (b : Fin r → E) (i : Fin r) : flagStep Ω b (i+1) = flagStep Ω b i ⊔ Submodule.span Ω {b i} := by
  unfold flagStep
  have hset : {k : Fin r | (k : ℕ) < (i : ℕ) + 1} = {k : Fin r | (k : ℕ) < i} ∪ {i} := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_singleton_iff]
    constructor
    · intro h
      by_cases h' : (k : ℕ) = i
      · exact Or.inr (Fin.ext h')
      · exact Or.inl (by omega)
    · rintro (h | h)
      · omega
      · subst h
        omega
  rw [hset, Set.image_union, Set.image_singleton, Submodule.span_union]

private theorem eq_zero_of_sum_smul_mem_span_lt {r : ℕ} {b : Fin r → E} (hli : LinearIndependent Ω b) (g : Fin r → Ω)
    (n : ℕ) (hg : ∑ k, g k • b k ∈ Submodule.span Ω (b '' {k | (k : ℕ) < n})) (k : Fin r)
    (hk : n ≤ (k : ℕ)) : g k = 0 := by
  classical
  have hhi : ∑ j : Fin r, (if (j : ℕ) < n then 0 else g j) • b j ∈
      Submodule.span Ω (b '' {k | (k : ℕ) < n}ᶜ) := by
    apply Submodule.sum_mem
    intro j _
    by_cases hj : (j : ℕ) < n
    · simp [hj]
    · rw [if_neg hj]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
  have hlo : ∑ j : Fin r, (if (j : ℕ) < n then g j else 0) • b j ∈
      Submodule.span Ω (b '' {k | (k : ℕ) < n}) := by
    apply Submodule.sum_mem
    intro j _
    by_cases hj : (j : ℕ) < n
    · rw [if_pos hj]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · simp [hj]
  have hsplit : ∑ j : Fin r, (if (j : ℕ) < n then 0 else g j) • b j =
      ∑ j : Fin r, g j • b j - ∑ j : Fin r, (if (j : ℕ) < n then g j else 0) • b j := by
    rw [eq_sub_iff_add_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : (j : ℕ) < n <;> simp [hj]
  have hzero : ∑ j : Fin r, (if (j : ℕ) < n then 0 else g j) • b j = 0 := by
    have hmem : ∑ j : Fin r, (if (j : ℕ) < n then 0 else g j) • b j ∈
        Submodule.span Ω (b '' {k | (k : ℕ) < n}) := by
      rw [hsplit]
      exact Submodule.sub_mem _ hg hlo
    exact (Submodule.disjoint_def.mp (hli.disjoint_span_image disjoint_compl_right)) _ hmem hhi
  have := Fintype.linearIndependent_iff.mp hli _ hzero k
  simpa [show ¬ (k : ℕ) < n by omega] using this

theorem gr_gen (L : Lat ξ E) {r : ℕ} (b b₀ : Fin r → E) (p : Cpt ξ) (h : ∀ i, flagStep Ω b i = flagStep Ω b₀ i)
    (hb : L.IsFrameAt b p) (i : Fin r) : ∃ t, (L.gr b₀ i).IsGenAt p t := by
  obtain ⟨hli, hLp⟩ := hb
  have hbi : b i ∈ flagStep Ω b₀ i ⊔ Submodule.span Ω {b₀ i} := by
    rw [← step_succ, ← h]
    unfold flagStep
    exact Submodule.subset_span ⟨i, show (i : ℕ) < (i : ℕ) + 1 by omega, rfl⟩
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hbi
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero] at hyz
    rw [← h, hyz] at hy
    unfold flagStep at hy
    exact hli.notMem_span_image (by simp) hy
  refine ⟨c, hc, ?_⟩
  show Submodule.span (regAt ξ p) {t | ∃ e ∈ L p, e - t • b₀ i ∈ flagStep Ω b₀ i} =
    Submodule.span (regAt ξ p) {c}
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro t ⟨e, he, hte⟩
    rw [hLp] at he
    obtain ⟨g, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp he
    have hsm : ∀ k, g k • b k = (g k : Ω) • b k := fun k => rfl
    have hsum : ∑ k, (c * (g k : Ω) - (if k = i then t else 0)) • b k =
        c • ∑ k, g k • b k - t • b i := by
      simp only [hsm, sub_smul, Finset.sum_sub_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte, mul_smul, Finset.smul_sum]
    have hx : c • (∑ k, g k • b k - t • b₀ i) - t • y ∈ flagStep Ω b₀ i :=
      Submodule.sub_mem _ (Submodule.smul_mem _ c hte) (Submodule.smul_mem _ t hy)
    have heq : ∑ k, (c * (g k : Ω) - (if k = i then t else 0)) • b k =
        c • (∑ k, g k • b k - t • b₀ i) - t • y := by
      rw [hsum, ← hyz, smul_add, smul_sub, smul_smul, smul_smul, mul_comm t c]
      abel
    have key : ∑ k, (c * (g k : Ω) - (if k = i then t else 0)) • b k ∈ flagStep Ω b i := by
      rw [h, heq]
      exact hx
    unfold flagStep at key
    have hci := eq_zero_of_sum_smul_mem_span_lt hli _ i key i le_rfl
    rw [if_pos rfl, sub_eq_zero] at hci
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨g i, ?_⟩
    show (g i : Ω) * c = t
    rw [mul_comm]
    exact hci
  · apply Submodule.span_mono
    rw [Set.singleton_subset_iff]
    refine ⟨b i, ?_, ?_⟩
    · rw [hLp]
      exact Submodule.subset_span ⟨i, rfl⟩
    · rw [← hyz, add_sub_cancel_right]
      exact hy

theorem gr_gen_of_isFlagVBOn {L : Lat ξ E} {T : Set (Cpt ξ)} {r : ℕ} {b₀ : Fin r → E} (h : L.IsFlagVBOn T b₀)
    {p : Cpt ξ} (hp : p ∈ T) (i : Fin r) : ∃ t, (L.gr b₀ i).IsGenAt p t := by
  obtain ⟨U, hU, b, hflag, hframe⟩ := h p hp
  exact gr_gen L b b₀ p hflag (hframe p hp hU) i

end GlobalTheory.CompanionTheory.Ar.Flag
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalence
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LiePull

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
  {φ : G'.left ⟶ G.left}

def push (h : IsGrpPullback G' G f φ) {T : Over S'} {g : T.left ⟶ S} (hg : T.hom ≫ f = g) (v : T ⟶ G') :
    Over.mk g ⟶ G :=
  Over.homMk (v.left ≫ φ) (by
    have e : (v.left ≫ φ) ≫ G.hom = g := by
      rw [Category.assoc, h.1.w, ← Category.assoc, Over.w v, hg]
    exact e)

def pull (h : IsGrpPullback G' G f φ) {T : Over S'} {g : T.left ⟶ S} (hg : T.hom ≫ f = g)
    (a : Over.mk g ⟶ G) : T ⟶ G' :=
  Over.homMk (h.1.lift a.left T.hom (by rw [hg]; exact Over.w a)) (h.1.lift_snd _ _ _)

def pts (h : IsGrpPullback G' G f φ) {T : Over S'} {g : T.left ⟶ S} (hg : T.hom ≫ f = g) :
    (T ⟶ G') ≃* (Over.mk g ⟶ G) where
  toFun := push h hg
  invFun := pull h hg
  left_inv v := by
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · exact h.1.lift_fst _ _ _
    · exact (h.1.lift_snd _ _ _).trans (Over.w v).symm
  right_inv a := Over.OverMorphism.ext (h.1.lift_fst _ _ _)
  map_mul' v w := by
    subst hg
    exact Over.OverMorphism.ext (h.2 T v w _ _ rfl rfl).symm

theorem pts_left (h : IsGrpPullback G' G f φ) {T : Over S'} {g : T.left ⟶ S} (hg : T.hom ≫ f = g)
    (v : T ⟶ G') : (pts h hg v).left = v.left ≫ φ := rfl

variable {R : Type} [CommRing R]

theorem one_left (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') :
    (1 : Over.mk x' ⟶ G').left ≫ φ = (1 : Over.mk (x' ≫ f) ⟶ G).left := by
  have e := map_one (pts h (T := Over.mk x') (g := x' ≫ f) rfl)
  exact (pts_left h rfl _).symm.trans (congrArg (fun z => z.left) e)

theorem eps_assoc (x' : Sp R ⟶ S') : (epsAt x').hom ≫ f = (epsAt (x' ≫ f)).hom :=
  Category.assoc _ _ _

abbrev tanPts (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') :
    (epsAt x' ⟶ G') ≃* (epsAt (x' ≫ f) ⟶ G) :=
  pts h (T := epsAt x') (g := (epsAt (x' ≫ f)).hom) (eps_assoc x')

theorem fst_comp_base (x' : Sp R ⟶ S') :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom) ≫ (epsAt x').hom = x' := by
  have e : (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom = 𝟙 _ := by
    ext r
    simp
  have e' := congrArg Spec.map e
  simp only [Spec.map_comp, Spec.map_id] at e'
  show _ ≫ Spec.map _ ≫ x' = x'
  rw [← Category.assoc, e', Category.id_comp]

theorem epsMul_comp_base (x' : Sp R ⟶ S') (c : R) :
    Spec.map (CommRingCat.ofHom (epsMul c)) ≫ (epsAt x').hom = (epsAt x').hom := by
  have e : (CommRingCat.ofHom (algebraMap R (DualNumber R))) ≫ CommRingCat.ofHom (epsMul c) =
      CommRingCat.ofHom (algebraMap R (DualNumber R)) := by
    refine CommRingCat.hom_ext (RingHom.ext fun r => ?_)
    show epsMul c (algebraMap R (DualNumber R) r) = algebraMap R (DualNumber R) r
    rw [TrivSqZeroExt.algebraMap_eq_inl]
    ext <;> simp [epsMul]
  have e' := congrArg Spec.map e
  simp only [Spec.map_comp] at e'
  show _ ≫ Spec.map _ ≫ x' = Spec.map _ ≫ x'
  rw [← Category.assoc, e']

theorem isTan_iff (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') (v : epsAt x' ⟶ G') :
    IsTanAt G (x' ≫ f) (tanPts h x' v) ↔ IsTanAt G' x' v := by
  unfold IsTanAt
  constructor
  · intro t
    apply h.1.hom_ext
    · rw [Category.assoc, one_left h x', ← pts_left h (eps_assoc x') v]
      exact t
    · rw [Category.assoc, Over.w v, fst_comp_base]
      exact (Over.w (1 : Over.mk x' ⟶ G')).symm
  · intro t
    rw [← one_left h x', ← t, pts_left h (eps_assoc x') v, Category.assoc]

def modelPull (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G (x' ≫ f) E) : LieModel G' x' E where
  pt e := (tanPts h x').symm (M.pt e)
  tan e := (isTan_iff h x' _).1 (by rw [MulEquiv.apply_symm_apply]; exact M.tan e)
  inj e e' w := M.inj ((tanPts h x').symm.injective w)
  onto v t := by
    obtain ⟨e, he⟩ := M.onto _ ((isTan_iff h x' v).2 t)
    exact ⟨e, by rw [he, MulEquiv.symm_apply_apply]⟩
  add e e' := by rw [M.add, map_mul]
  smul c e := by
    apply h.1.hom_ext
    · have a : ∀ e, ((tanPts h x').symm (M.pt e)).left ≫ φ = (M.pt e).left := fun e => by
        rw [← pts_left h (eps_assoc x'), MulEquiv.apply_symm_apply]
      rw [Category.assoc, a, a]
      exact M.smul c e
    · have b : ((tanPts h x').symm (M.pt e)).left ≫ G'.hom = (epsAt x').hom := Over.w _
      rw [Category.assoc, Over.w, b]
      exact (epsMul_comp_base x' c).symm

def modelPush (h : IsGrpPullback G' G f φ) (x' : Sp R ⟶ S') {E : Type} [AddCommGroup E] [Module R E]
    (M : LieModel G' x' E) : LieModel G (x' ≫ f) E where
  pt e := tanPts h x' (M.pt e)
  tan e := (isTan_iff h x' _).2 (M.tan e)
  inj e e' w := M.inj ((tanPts h x').injective w)
  onto v t := by
    have t' : IsTanAt G (x' ≫ f) (tanPts h x' ((tanPts h x').symm v)) := by
      rw [MulEquiv.apply_symm_apply]; exact t
    obtain ⟨e, he⟩ := M.onto _ ((isTan_iff h x' _).1 t')
    exact ⟨e, by rw [he, MulEquiv.apply_symm_apply]⟩
  add e e' := by rw [M.add, map_mul]
  smul c e := by
    show (M.pt (c • e)).left ≫ φ = _ ≫ (M.pt e).left ≫ φ
    rw [M.smul, Category.assoc]

theorem lieModel_pullback : ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (R : Type) [CommRing R] (x' : Sp R ⟶ S') (E : Type) [AddCommGroup E] [Module R E], (∀ M : LieModel G (x' ≫ f) E, ∃ M' : LieModel G' x' E, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left) ∧ ∀ M' : LieModel G' x' E, ∃ M : LieModel G (x' ≫ f) E, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left := by
  intro S S' G G' _ _ f φ h R _ x' E _ _
  refine ⟨fun M => ⟨modelPull h x' M, fun e => ?_⟩, fun M' => ⟨modelPush h x' M', fun e => rfl⟩⟩
  show ((tanPts h x').symm (M.pt e)).left ≫ φ = _
  rw [← pts_left h (eps_assoc x'), MulEquiv.apply_symm_apply]

end GlobalTheory.CompanionTheory.Ar.LiePull
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelPullbackEquivalenceStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_pullback_equivalence : ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left), IsGrpPullback G' G f φ → ∀ (R : Type) [CommRing R] (x' : Sp R ⟶ S') (E : Type) [AddCommGroup E] [Module R E], (∀ M : LieModel G (x' ≫ f) E, ∃ M' : LieModel G' x' E, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left) ∧ ∀ M' : LieModel G' x' E, ∃ M : LieModel G (x' ≫ f) E, ∀ e, (M'.pt e).left ≫ φ = (M.pt e).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback | exact GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback | (intros; apply GlobalTheory.CompanionTheory.Ar.LiePull.lieModel_pullback <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtFractionNoetherianClosed
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtFractionNoetherianClosed
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.RegAtRing

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

def stalkEquiv (h : IsCptGen ξ) (p : Cpt ξ) : X.presheaf.stalk p.1 ≃+* regAt ξ p :=
  RingEquiv.ofBijective (genMap ξ p).rangeRestrict
    ⟨fun _ _ hab => h.inj p (congrArg Subtype.val hab), (genMap ξ p).rangeRestrict_surjective⟩

theorem genMap_germ (p : Cpt ξ) (U : X.Opens) (hp : p.1 ∈ U) (hg : genPt ξ ∈ U) (s : Γ(X, U)) :
    genMap ξ p (X.presheaf.germ U p.1 hp s) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hg s) := by
  obtain ⟨q, hq⟩ := p
  have e := congrArg (fun f => (f ≫ Scheme.stalkClosedPointTo ξ).hom s)
    (X.presheaf.germ_stalkSpecializes hp hq)
  simp only [Category.assoc, CommRingCat.hom_comp, RingHom.comp_apply] at e
  simp only [genMap, CommRingCat.hom_comp, RingHom.comp_apply]
  exact e

theorem exists_div (h : IsCptGen ξ) (p : Cpt ξ) (z : Ω) :
    ∃ a b : regAt ξ p, z = (a : Ω) / (b : Ω) := by
  obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset (show p.1 ∈ (⊤ : X.Opens) from trivial)
  have hgU : genPt ξ ∈ U := p.2.mem_open U.isOpen hpU
  obtain ⟨t, rfl⟩ := h.bij.2 z
  change X.presheaf.stalk (genPt ξ) at t
  let x : U := ⟨genPt ξ, hgU⟩
  let _ : Algebra Γ(X, U) (X.presheaf.stalk (x : X)) := TopCat.Presheaf.algebra_section_stalk X.presheaf x
  have : IsLocalization.AtPrime (X.presheaf.stalk (x : X)) (hU.primeIdealOf x).asIdeal :=
    hU.isLocalization_stalk x
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.mk'_surjective (hU.primeIdealOf x).asIdeal.primeCompl
    (S := X.presheaf.stalk (x : X)) t
  have hspec := IsLocalization.mk'_spec (X.presheaf.stalk (x : X)) a s
  simp only at hs
  rw [hs] at hspec
  have hu : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk (x : X)) (s : Γ(X, U))) :=
    IsLocalization.map_units _ s
  have hne : (Scheme.stalkClosedPointTo ξ).hom
      (algebraMap Γ(X, U) (X.presheaf.stalk (x : X)) (s : Γ(X, U))) ≠ 0 :=
    (hu.map (Scheme.stalkClosedPointTo ξ).hom).ne_zero
  refine ⟨⟨genMap ξ p (X.presheaf.germ U p.1 hpU a), ⟨_, rfl⟩⟩,
    ⟨genMap ξ p (X.presheaf.germ U p.1 hpU (s : Γ(X, U))), ⟨_, rfl⟩⟩, ?_⟩
  simp only [genMap_germ p U hpU hgU]
  have hspec' : t * X.presheaf.germ U (genPt ξ) hgU (s : Γ(X, U)) = X.presheaf.germ U (genPt ξ) hgU a := hspec
  have hne' : ((Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hgU (s : Γ(X, U))) : Ω) ≠ 0 := hne
  have key : (Scheme.stalkClosedPointTo ξ).hom t *
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hgU (s : Γ(X, U))) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ U (genPt ξ) hgU a) := by
    rw [← congrArg (Scheme.stalkClosedPointTo ξ).hom hspec']
    exact (map_mul _ _ _).symm
  exact (eq_div_iff hne').2 key

theorem regAt_ring : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ p : Cpt ξ, IsFractionRing (regAt ξ p) Ω ∧ (IsNoetherianRing (X.presheaf.stalk p.1) → IsNoetherianRing (regAt ξ p)) ∧ (IsIntegrallyClosed (X.presheaf.stalk p.1) → IsIntegrallyClosed (regAt ξ p)) := by
  intro X Ω _ ξ h p
  refine ⟨?_, fun _ => isNoetherianRing_of_ringEquiv _ (stalkEquiv h p),
    fun _ => IsIntegrallyClosed.of_equiv (stalkEquiv h p)⟩
  haveI : FaithfulSMul (regAt ξ p) Ω :=
    (faithfulSMul_iff_algebraMap_injective (regAt ξ p) Ω).2 Subtype.val_injective
  exact IsFractionRing.of_field (regAt ξ p) Ω fun z => exists_div h p z

end GlobalTheory.CompanionTheory.Ar.RegAtRing
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtFractionNoetherianClosedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regAt_fraction_noetherian_closed : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ p : Cpt ξ, IsFractionRing (regAt ξ p) Ω ∧ (IsNoetherianRing (X.presheaf.stalk p.1) → IsNoetherianRing (regAt ξ p)) ∧ (IsIntegrallyClosed (X.presheaf.stalk p.1) → IsIntegrallyClosed (regAt ξ p)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RegAtRing.regAt_ring | exact GlobalTheory.CompanionTheory.Ar.RegAtRing.regAt_ring | (intros; apply GlobalTheory.CompanionTheory.Ar.RegAtRing.regAt_ring <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordTieCompEquiv
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagBun

open AlgebraicGeometry CategoryTheory

def GenIx {S : Type} (r : S → ℕ) : Type := Σ s, {lk : Fin (r s) × Fin (r s) // lk.2 < lk.1}

abbrev GenField (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) : Type :=
  FractionRing (MvPolynomial (GenIx r) Ω)

def genU (Ω : Type) [Field Ω] {S : Type} (r : S → ℕ) (s : S) :
    Matrix (Fin (r s)) (Fin (r s)) (GenField Ω r) := fun l k =>
  if h : k < l then algebraMap (MvPolynomial (GenIx r) Ω) (GenField Ω r) (MvPolynomial.X ⟨s, ⟨(l, k), h⟩⟩)
  else if l = k then 1 else 0

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {S : Type} {r : S → ℕ}

def genB (c : ∀ s, Fin (r s) → E) (s : S) (k : Fin (r s)) : TensorProduct Ω (GenField Ω r) E :=
  ∑ l, genU Ω r s l k • TensorProduct.mk Ω (GenField Ω r) E 1 (c s l)

def flagMat {n : S → ℕ} (φ : ∀ s, Fin (n s) → Module.Dual Ω E) (c : ∀ s, Fin (r s) → E) (s : S) :
    Matrix (Fin (n s)) (Fin (r s)) (GenField Ω r) :=
  Matrix.of (fun j l => algebraMap Ω (GenField Ω r) (φ s j (c s l))) * genU Ω r s

def FlagIx (κ : Type) {S : Type} (n : S → ℕ) (r : S → ℕ) : Type :=
  κ × ((q : Σ s, Fin (r s)) → Fin ((q.2 : ℕ) + 1) → Fin (n q.1))

def flagCoord [Fintype S] (κ : Type) (x : κ → Ω) {n : S → ℕ} (φ : ∀ s, Fin (n s) → Module.Dual Ω E)
    (c : ∀ s, Fin (r s) → E) : FlagIx κ n r → GenField Ω r := fun cJ =>
  algebraMap Ω (GenField Ω r) (x cJ.1) *
    ∏ q : (Σ s, Fin (r s)), ((flagMat φ c q.1).submatrix (cJ.2 q) (Fin.castLE q.2.2)).det

def IsTwistGen {X : Scheme.{0}} (ξ : Spec (CommRingCat.of Ω) ⟶ X) {κ : Type} (x : κ → Ω) (L : Lat ξ E) (m : ℕ)
    {n : ℕ} (φ : Fin n → Module.Dual Ω E) : Prop :=
  (∀ j (p : Cpt ξ) c, InChart ξ x c p → ∀ e ∈ L p, φ j e / x c ^ m ∈ regAt ξ p) ∧
  ∀ (p : Cpt ξ) c, InChart ξ x c p → ∀ w : Module.Dual Ω E, (∀ e ∈ L p, w e ∈ regAt ξ p) →
    ∃ g : Fin n → Ω, (∀ j, g j ∈ regAt ξ p) ∧ ∀ e ∈ L p, w e = ∑ j, g j * (φ j e / x c ^ m)

theorem coordTie_comp_equiv {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {o : Type}
    [CommRing o] [Algebra o Ω] {κ κ' : Type} {x : κ → Ω} (h : CoordTie o ξ x) (e : κ' ≃ κ) :
    CoordTie o ξ (x ∘ e) := by
  have hch : ∀ c p, InChart ξ (x ∘ e) c p ↔ InChart ξ x (e c) p := by
    intro c p
    simp only [InChart, Function.comp]
    exact and_congr Iff.rfl ⟨fun h c' => by simpa using h (e.symm c'), fun h c' => h (e c')⟩
  have hr : ∀ c, Set.range (fun j => (x ∘ e) j / (x ∘ e) c) = Set.range (fun j => x j / x (e c)) := by
    intro c
    ext a
    exact ⟨fun ⟨j, hj⟩ => ⟨e j, hj⟩, fun ⟨j, hj⟩ => ⟨e.symm j, by simpa using hj⟩⟩
  refine ⟨h.gen, fun p => ?_, fun c hc => ?_, fun c hc a => ?_⟩
  · obtain ⟨c, hc⟩ := h.cover p
    exact ⟨e.symm c, (hch _ p).2 (by simpa using hc)⟩
  · obtain ⟨U, hU, hq⟩ := h.affine (e c) hc
    exact ⟨U, hU, fun q => by rw [hq q]; exact exists_congr fun h' => (hch c _).symm⟩
  · rw [hr c, h.ring (e c) hc a]
    exact forall_congr' fun p => imp_congr (hch c p).symm Iff.rfl
end GlobalTheory.CompanionTheory.Ar.FlagBun
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapFromSpecStalk
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieCarrier

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar (dualMap)

variable {S : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

def epsHom (φ : R →+* R') (x : Spec (CommRingCat.of R) ⟶ S) (x' : Spec (CommRingCat.of R') ⟶ S)
    (h : Spec.map (CommRingCat.ofHom φ) ≫ x = x') : epsAt x' ⟶ epsAt x :=
  Over.homMk (Spec.map (CommRingCat.ofHom (dualMap φ))) (by
    subst h
    show _ ≫ _ ≫ x = _ ≫ _ ≫ x
    rw [← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp]
    congr 3
    ext a <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl])

theorem dualMap_epsMul (φ : R →+* R') (c : R) :
    (dualMap φ).comp (epsMul c) = (epsMul (φ c)).comp (dualMap φ) := by
  refine RingHom.ext fun a => TrivSqZeroExt.ext ?_ ?_ <;>
    simp [dualMap, epsMul, mul_comm]

theorem surjective_fst :
    Function.Surjective (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom R R R).toRingHom)) := by
  intro p
  have hn : ∀ m : R, (TrivSqZeroExt.inr m : TrivSqZeroExt R R) ∈ p.asIdeal := fun m =>
    p.isPrime.mem_of_pow_mem 2 (by rw [pow_two, TrivSqZeroExt.inr_mul_inr]; exact p.asIdeal.zero_mem)
  have : p.asIdeal.IsPrime := p.isPrime
  refine ⟨⟨Ideal.comap (TrivSqZeroExt.inlHom R R) p.asIdeal, Ideal.IsPrime.comap _⟩, ?_⟩
  change PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom _ = p
  ext y
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, Ideal.mem_comap]
  change TrivSqZeroExt.inl y.fst ∈ p.asIdeal ↔ y ∈ p.asIdeal
  have hy : TrivSqZeroExt.inl y.fst = y - TrivSqZeroExt.inr y.snd :=
    eq_sub_of_add_eq (TrivSqZeroExt.inl_fst_add_inr_snd_eq y)
  rw [hy]
  constructor
  · intro h
    have := p.asIdeal.add_mem h (hn y.snd)
    rwa [sub_add_cancel] at this
  · intro h
    exact p.asIdeal.sub_mem h (hn y.snd)

theorem tan_ext {G : Over S} [GrpObj G] (φ : R →+* R') (hφ : Function.Injective φ)
    (x : Spec (CommRingCat.of R) ⟶ S) (v v' : epsAt x ⟶ G) (hv : IsTanAt G x v) (hv' : IsTanAt G x v')
    (h : Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v.left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v'.left) :
    v = v' := by
  apply Over.OverMorphism.ext
  have hinj : Function.Injective ((TrivSqZeroExt.fstHom R R R).toRingHom.prod (dualMap φ)) := by
    intro a b hab
    have h2 : dualMap φ a = dualMap φ b := congrArg Prod.snd hab
    have h3 := congrArg TrivSqZeroExt.fst h2
    have h4 := congrArg TrivSqZeroExt.snd h2
    simp [dualMap, hφ.eq_iff] at h3 h4
    exact TrivSqZeroExt.ext h3 h4
  unfold IsTanAt at hv hv'
  exact GlobalTheory.CompanionTheory.Ar.LieEx.joint_epi _ _ hinj surjective_fst v.left v'.left (hv.trans hv'.symm) h

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem genMap_fromSpecStalk (p : Cpt ξ) :
    Spec.map (CommRingCat.ofHom (genMap ξ p)) ≫ X.fromSpecStalk p.1 = ξ := by
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (x := p.1) (U := ⊤) trivial
  have hxW : genPt ξ ∈ W := p.2.mem_open W.isOpen hyW
  have key : Spec.map (X.presheaf.stalkSpecializes p.2) ≫ X.fromSpecStalk p.1 =
      X.fromSpecStalk (genPt ξ) := by
    rw [← hW.fromSpecStalk_eq_fromSpecStalk hyW, ← hW.fromSpecStalk_eq_fromSpecStalk hxW]
    simp only [IsAffineOpen.fromSpecStalk]
    rw [← Category.assoc, ← Spec.map_comp, TopCat.Presheaf.germ_stalkSpecializes]
  have e1 : Spec.map (CommRingCat.ofHom (genMap ξ p)) =
      Spec.map (Scheme.stalkClosedPointTo ξ) ≫ Spec.map (X.presheaf.stalkSpecializes p.2) :=
    Spec.map_comp _ _
  rw [e1, Category.assoc]
  exact (congrArg (fun f => Spec.map (Scheme.stalkClosedPointTo ξ) ≫ f) key).trans
    (Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ)

theorem span_ext {G : Over S} [GrpObj G] (φ : R →+* R') (x : Spec (CommRingCat.of R) ⟶ S)
    (x' : Spec (CommRingCat.of R') ⟶ S) (h : Spec.map (CommRingCat.ofHom φ) ≫ x = x')
    {E : Type} [AddCommGroup E] [Module R' E] (M : LieModel G x' E) (e : E)
    (he : e ∈ Submodule.span φ.range {e | ∃ v : epsAt x ⟶ G, IsTanAt G x v ∧
      (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v.left}) :
    ∃ v : epsAt x ⟶ G, IsTanAt G x v ∧ (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v.left := by
  suffices H : ∃ v : epsAt x ⟶ G, IsTanAt G x v ∧ M.pt e = epsHom φ x x' h ≫ v by
    obtain ⟨v, hv, hev⟩ := H
    exact ⟨v, hv, by rw [hev]; rfl⟩
  induction he using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨v, hv, hav⟩ := ha
    exact ⟨v, hv, Over.OverMorphism.ext hav⟩
  | zero =>
    refine ⟨1, (GlobalTheory.CompanionTheory.Ar.LieEx.isTanAt_iff x G 1).mpr (MonObj.comp_one _), ?_⟩
    rw [MonObj.comp_one]
    have h0 : M.pt 0 * 1 = M.pt 0 * M.pt 0 := by rw [_root_.mul_one, ← M.add, add_zero]
    exact (mul_left_cancel h0).symm
  | add a b _ _ ha hb =>
    obtain ⟨v, hv, hva⟩ := ha
    obtain ⟨w, hw, hwb⟩ := hb
    refine ⟨v * w, ?_, ?_⟩
    · rw [GlobalTheory.CompanionTheory.Ar.LieEx.isTanAt_iff] at hv hw ⊢
      rw [MonObj.comp_mul, hv, hw, _root_.mul_one]
    · rw [M.add, hva, hwb, MonObj.comp_mul]
  | smul a b _ hb =>
    obtain ⟨v, hv, hvb⟩ := hb
    obtain ⟨r, hr⟩ := a
    obtain ⟨c, rfl⟩ := RingHom.mem_range.mp hr
    refine ⟨GlobalTheory.CompanionTheory.Ar.LieEx.hom x (c • LinearMap.id) ≫ v, ?_, ?_⟩
    · rw [GlobalTheory.CompanionTheory.Ar.LieEx.isTanAt_iff] at hv ⊢
      rw [← Category.assoc, GlobalTheory.CompanionTheory.Ar.LieEx.zsec_hom]
      exact hv
    · apply Over.OverMorphism.ext
      change (M.pt ((φ c) • b)).left = _
      rw [M.smul, hvb]
      have e2 : Spec.map (CommRingCat.ofHom (epsMul (φ c))) ≫ Spec.map (CommRingCat.ofHom (dualMap φ)) =
          Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ Spec.map (CommRingCat.ofHom (epsMul c)) := by
        rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
          dualMap_epsMul]
      change Spec.map (CommRingCat.ofHom (epsMul (φ c))) ≫ Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ v.left =
        Spec.map (CommRingCat.ofHom (dualMap φ)) ≫ Spec.map (CommRingCat.ofHom (epsMul c)) ≫ v.left
      rw [← Category.assoc, e2, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.LieCarrier

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

theorem lieLat_carrier (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) :
    (∀ e, e ∈ M.lat p ↔ ∃ v, M.Extends p e v) ∧
      (IsCptGen ξ → Smooth G.hom → ∀ e v v', M.Extends p e v → M.Extends p e v' → v = v') := by
  refine ⟨fun e => ⟨fun he => ?_, fun hv => Submodule.subset_span hv⟩, ?_⟩
  · exact LieCarrier.span_ext (genMap ξ p) (X.fromSpecStalk p.1) ξ
      (LieCarrier.genMap_fromSpecStalk p) M e he
  · intro hgen _ e v v' hv hv'
    exact LieCarrier.tan_ext (genMap ξ p) (hgen.inj p) _ v v' hv.1 hv'.1 (hv.2.symm.trans hv'.2)

end GlobalTheory.CompanionTheory.Ar
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrIsGenAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.FlagGrGen

theorem exists_coord {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {r : ℕ} {b : Fin r → E}
    (hb : LinearIndependent Ω b) (i : Fin r) :
    ∃ φ : E →ₗ[Ω] Ω, φ (b i) = 1 ∧ ∀ k, k ≠ i → φ (b k) = 0 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend ((Module.Basis.span hb).coord i)
  have key : ∀ k, g (b k) = Finsupp.single k (1 : Ω) i := by
    intro k
    have hk : (Module.Basis.span hb k : E) = b k := by rw [Module.Basis.span_apply]
    have := LinearMap.congr_fun hg (Module.Basis.span hb k)
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, Module.Basis.coord_apply, Module.Basis.repr_self] at this
    rw [hk] at this
    exact this
  refine ⟨g, ?_, ?_⟩
  · rw [key]
    simp
  · intro k hk
    rw [key]
    simp [Ne.symm hk]

theorem gr_isGenAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (b₀ b : Fin r → E) (p : Cpt ξ) (i : Fin r) (t : Ω), LinearIndependent Ω b₀ → (∀ s, flagStep Ω b s = flagStep Ω b₀ s) → L.IsFrameAt b p → b i - t • b₀ i ∈ flagStep Ω b₀ i → (L.gr b₀ i).IsGenAt p t := by
  intro X Ω _ ξ E _ _ L r b₀ b p i t hb₀ hflag hframe hti
  obtain ⟨hb, hLp⟩ := hframe
  obtain ⟨f0, hf0⟩ := exists_coord hb₀ i
  obtain ⟨g, hg⟩ := exists_coord hb i
  have hflag_i : flagStep Ω b₀ (i : ℕ) = flagStep Ω b (i : ℕ) := (hflag (i : ℕ)).symm
  have hf0ker : ∀ v ∈ flagStep Ω b₀ (i : ℕ), f0 v = 0 := by
    intro v hv
    have hle : flagStep Ω b₀ (i : ℕ) ≤ LinearMap.ker f0 := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      have hki : k ≠ i := by
        rintro rfl
        simp at hk
      exact LinearMap.mem_ker.mpr (hf0.2 k hki)
    exact LinearMap.mem_ker.mp (hle hv)
  have hgker : ∀ v ∈ flagStep Ω b (i : ℕ), g v = 0 := by
    intro v hv
    have hle : flagStep Ω b (i : ℕ) ≤ LinearMap.ker g := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      have hki : k ≠ i := by
        rintro rfl
        simp at hk
      exact LinearMap.mem_ker.mpr (hg.2 k hki)
    exact LinearMap.mem_ker.mp (hle hv)
  have hf0bi : f0 (b i) = t := by
    have := hf0ker _ hti
    rw [map_sub, map_smul, hf0.1, smul_eq_mul, _root_.mul_one, sub_eq_zero] at this
    exact this
  have ht0 : t ≠ 0 := by
    rintro rfl
    have hbi : b i ∈ flagStep Ω b (i : ℕ) := by
      rw [← hflag_i]
      simpa using hti
    have := hgker _ hbi
    rw [hg.1] at this
    exact one_ne_zero this
  have hmono : flagStep Ω b (i : ℕ) ≤ flagStep Ω b ((i : ℕ) + 1) :=
    Submodule.span_mono (Set.image_mono (fun k hk => by
      simp only [Set.mem_setOf_eq] at hk ⊢
      omega))
  have hb0i : b₀ i ∈ flagStep Ω b ((i : ℕ) + 1) := by
    rw [hflag]
    exact Submodule.subset_span ⟨i, by simp, rfl⟩
  have hagree : ∀ v ∈ flagStep Ω b ((i : ℕ) + 1), f0 v = t * g v := by
    intro v hv
    have hle : flagStep Ω b ((i : ℕ) + 1) ≤ LinearMap.eqLocus f0 (t • g) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨k, hk, rfl⟩
      have hk' : (k : ℕ) < (i : ℕ) + 1 := hk
      rw [SetLike.mem_coe, LinearMap.mem_eqLocus, LinearMap.smul_apply, smul_eq_mul]
      rcases lt_or_eq_of_le (by omega : (k : ℕ) ≤ (i : ℕ)) with hlt | heq
      · have hki : k ≠ i := by
          rintro rfl
          exact lt_irrefl _ hlt
        rw [hg.2 k hki, mul_zero]
        apply hf0ker
        rw [hflag_i]
        exact Submodule.subset_span ⟨k, hlt, rfl⟩
      · have hki : k = i := Fin.ext heq
        rw [hki, hg.1, _root_.mul_one, hf0bi]
    have := hle hv
    rw [LinearMap.mem_eqLocus, LinearMap.smul_apply, smul_eq_mul] at this
    exact this
  have hgO : ∀ v ∈ Submodule.span (regAt ξ p) (Set.range b), g v ∈ regAt ξ p := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      by_cases hki : k = i
      · rw [hki, hg.1]
        exact one_mem _
      · rw [hg.2 k hki]
        exact zero_mem _
    | zero =>
      rw [map_zero]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [map_add (f := _)]
      exact add_mem hx hy
    | smul a x _ hx =>
      show g ((a : Ω) • x) ∈ regAt ξ p
      rw [map_smul, smul_eq_mul]
      exact mul_mem a.2 hx
  have hbiL : b i ∈ L p := by
    rw [hLp]
    exact Submodule.subset_span ⟨i, rfl⟩
  show t ≠ 0 ∧ Submodule.span (regAt ξ p) {s | ∃ e ∈ L p, e - s • b₀ i ∈ flagStep Ω b₀ i} = Submodule.span (regAt ξ p) {t}
  refine ⟨ht0, ?_⟩
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro s ⟨e, he, hes⟩
    rw [hLp] at he
    have he_flag : e ∈ flagStep Ω b ((i : ℕ) + 1) := by
      have h1 : e - s • b₀ i ∈ flagStep Ω b ((i : ℕ) + 1) := hmono (by rw [← hflag_i]; exact hes)
      have h2 : s • b₀ i ∈ flagStep Ω b ((i : ℕ) + 1) := Submodule.smul_mem _ s hb0i
      simpa using add_mem h1 h2
    have hs : s = f0 e := by
      have := hf0ker _ hes
      rw [map_sub, map_smul, hf0.1, smul_eq_mul, _root_.mul_one, sub_eq_zero] at this
      exact this.symm
    rw [SetLike.mem_coe, Submodule.mem_span_singleton]
    refine ⟨⟨g e, hgO e he⟩, ?_⟩
    show g e * t = s
    rw [hs, hagree e he_flag, _root_.mul_comm]
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.subset_span ⟨b i, hbiL, hti⟩

end GlobalTheory.CompanionTheory.Ar.FlagGrGen
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderValueEval
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderValueEval
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.BT.Tan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.BT.ValEmb

theorem valAt_pull {A B : Type} [CommRing A] [CommRing B] {X : Scheme.{0}}
    (j : X ⟶ Spec (CommRingCat.of A)) (x : Spec (CommRingCat.of B) ⟶ X) (ρ : A →+* B)
    (h : x ≫ j = Spec.map (CommRingCat.ofHom ρ)) (f : A) :
    valAt x ⊤ le_top (j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom f)) = ρ f := by
  have h1 : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ j.appTop ≫ x.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom
      = CommRingCat.ofHom ρ := by
    have : j.appTop ≫ x.appTop = (Spec.map (CommRingCat.ofHom ρ)).appTop := by
      rw [← h, Scheme.Hom.comp_appTop]
    rw [reassoc_of% this, ← Scheme.ΓSpecIso_inv_naturality_assoc]
    simp
  have h2 := congrArg (fun φ => φ.hom f) h1
  have hle : x.appLE ⊤ ⊤ le_top = x.appTop := by
    simp only [Scheme.Hom.appLE]
    exact Category.comp_id _
  simp only [valAt]
  rw [hle]
  simpa using h2

theorem valAt_sub {B : Type} [CommRing B] {X : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) : valAt x U h (a - b) = valAt x U h a - valAt x U h b := by
  simp [valAt]

theorem val_emb : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → ∀ (f : Γ.btOrder ⊤) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (f : T → R) → ∀ (B : Type) [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (ρ : (Γ.btOrder ⊤) →+* B), y ≫ j = Spec.map (CommRingCat.ofHom ρ) → valAt y ⊤ le_top s = ρ f := by
  intro R _ _ T _ _ Γ j hj f s hs B _ y ρ hy
  have hz : s - j.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of (Γ.btOrder ⊤))).inv.hom f) = 0 := by
    refine GlobalTheory.T.section_eq_zero_of_values R T Γ ⊤ _ fun t h => ?_
    rw [valAt_sub, hs t, valAt_pull j (Γ.pt t).left _ (hj.pt t) f]
    simp
  rw [sub_eq_zero.mp hz]
  exact valAt_pull j y ρ hy f

end GlobalTheory.CompanionTheory.Ar.BT.ValEmb
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderValueEvalStatement
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.LieEx GlobalTheory.CompanionTheory.Ar.BT.Tan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bt_order_value_eval : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → ∀ (f : Γ.btOrder ⊤) (s : Γ(Γ.G.left, ⊤)), Γ.HasValues s (f : T → R) → ∀ (B : Type) [CommRing B] (y : Spec (CommRingCat.of B) ⟶ Γ.G.left) (ρ : (Γ.btOrder ⊤) →+* B), y ≫ j = Spec.map (CommRingCat.ofHom ρ) → valAt y ⊤ le_top s = ρ f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.ValEmb.val_emb | exact GlobalTheory.CompanionTheory.Ar.BT.ValEmb.val_emb | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.ValEmb.val_emb <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecStalkSpecializesComp
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieStalk

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor MonoidalCategory CartesianMonoidalCategory MonObj Limits

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

def regIso (h : IsCptGen ξ) (p : Cpt ξ) : X.presheaf.stalk p.1 ≃+* regAt ξ p :=
  RingEquiv.ofBijective (genMap ξ p).rangeRestrict
    ⟨fun a b hab => h.inj p (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩

def regPt (h : IsCptGen ξ) (p : Cpt ξ) : Sp (regAt ξ p) ⟶ X :=
  spMap (regIso h p).toRingHom ≫ X.fromSpecStalk p.1

theorem genMap_regIso_symm (h : IsCptGen ξ) (p : Cpt ξ) (a : regAt ξ p) :
    genMap ξ p ((regIso h p).symm a) = a := by
  exact congrArg Subtype.val ((regIso h p).apply_symm_apply a)

set_option backward.isDefEq.respectTransparency false in
theorem genMap_specializes {p q : Cpt ξ} (hs : q.1 ⤳ p.1) (s : X.presheaf.stalk p.1) :
    genMap ξ q ((X.presheaf.stalkSpecializes hs).hom s) = genMap ξ p s := by
  simp only [genMap]
  rw [← CommRingCat.comp_apply, ← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]

theorem regAt_le {p q : Cpt ξ} (hs : q.1 ⤳ p.1) : regAt ξ p ≤ regAt ξ q := by
  rintro _ ⟨s, rfl⟩
  exact ⟨_, genMap_specializes hs s⟩

theorem spMap_genMap_fromSpecStalk (p : Cpt ξ) : spMap (genMap ξ p) ≫ X.fromSpecStalk p.1 = ξ := by
  have h2 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  rw [← Scheme.SpecMap_stalkSpecializes_fromSpecStalk (x := ξ (IsLocalRing.closedPoint Ω)) (y := p.1) p.2,
    ← Category.assoc, ← Spec.map_comp] at h2
  exact h2

theorem spMap_algebraMap_regPt (h : IsCptGen ξ) (p : Cpt ξ) : spMap (algebraMap (regAt ξ p) Ω) ≫ regPt h p = ξ := by
  have e : (algebraMap (regAt ξ p) Ω).comp (regIso h p).toRingHom = genMap ξ p :=
    RingHom.ext fun x => rfl
  dsimp only [regPt, spMap]
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
  exact spMap_genMap_fromSpecStalk p

abbrev regIncl {p q : Cpt ξ} (hs : q.1 ⤳ p.1) : regAt ξ p →+* regAt ξ q := Subring.inclusion (regAt_le hs)

theorem spMap_regIncl_regPt (h : IsCptGen ξ) {p q : Cpt ξ} (hs : q.1 ⤳ p.1) :
    spMap (regIncl hs) ≫ regPt h p = regPt h q := by
  have e : (regIncl hs).comp (regIso h p).toRingHom =
      (regIso h q).toRingHom.comp (X.presheaf.stalkSpecializes hs).hom :=
    RingHom.ext fun s => Subtype.ext (genMap_specializes hs s).symm
  dsimp only [regPt, spMap]
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e, CommRingCat.ofHom_comp,
    CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]

def castPt {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x y : Sp R ⟶ S} (e : x = y) {E : Type}
    [AddCommGroup E] [Module R E] (M : LieModel G x E) : LieModel G y E := e ▸ M

theorem castPt_pt_left {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R] {x y : Sp R ⟶ S} (e : x = y)
    {E : Type} [AddCommGroup E] [Module R E] (M : LieModel G x E) (a : E) :
    ((castPt e M).pt a).left = (M.pt a).left := by
  subst e
  rfl

end GlobalTheory.CompanionTheory.Ar.LieStalk
end
end
