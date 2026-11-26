module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EgaHolds
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FullObjectOfGenericFibreDvr
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NearCOfPolFamOfKTriv
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GeometricallyConnectedOpenConditionSmoothProject
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyFromVeryDensePoints
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaSchemeSectionsGoodFibres

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGeometricallyConnectedAwayOfFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ConnSpread

open GlobalTheory.AbLaw GlobalTheory.AbLaw.Seesaw ReciprocityTheory.ChartRestriction.G.Out

theorem preconnectedSpace_of_functions (Y : Scheme.{0})
    (H : ∀ s : Γ(Y, ⊤), Y.basicOpen s = ⊥ ∨ Y.basicOpen s = ⊤) : PreconnectedSpace Y := _root_.GlobalTheory.ConnOpen.preconnectedSpace_of_functions Y H

variable {X X' : Scheme.{0}}

def fnSec (π : X' ⟶ X) (s : Γ(X', ⊤)) : LB.Sec ((Inh.trivLB X).pull π) where
  f := fun _ => rs X' le_top s
  compat := fun i j => by
    rw [Inh.linComb_triv_g, Units.val_one, _root_.one_mul]
    exact (rs_rs _ _ s).trans (rs_rs _ _ s).symm

theorem triv_pull (π : X' ⟶ X) : Triv ((Inh.trivLB X).pull π) :=
  ⟨⟨fun _ => 1⟩, fun i j => by
    erw [Inh.linComb_triv_g, _root_.one_mul]
    exact (map_one _).trans (map_one _).symm⟩

theorem preconnectedSpace_of_line {R F : Type} [CommRing R] [Field F]
    {f : X ⟶ Spec (CommRingCat.of R)} (P : Perf f (Inh.trivLB X)) {g : R →+* F} {π : X' ⟶ X}
    {f' : X' ⟶ Spec (CommRingCat.of F)} (h : IsPullback π f' f (Spec.map (CommRingCat.ofHom g)))
    (v : Fin P.a → F) (hv : ∀ w, (P.D₀.map g).mulVec w = 0 → ∃ c : F, w = c • v) :
    PreconnectedSpace X' := by
  obtain ⟨E, hE⟩ := P.sec F g X' π f' h
  have key : ∀ s : Γ(X', ⊤), ∃ c : F, ∀ i,
      rs X' (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s = AbLaw.cst f' _ c * loc P π f' v i := fun s => by
    obtain ⟨w, hw⟩ := E.surjective (fnSec π s)
    obtain ⟨c, hc⟩ := hv w.1 w.2
    refine ⟨c, fun i => ?_⟩
    have e := hE w i
    rw [hw] at e
    refine ((rs_rs _ _ s).symm.trans e).trans ?_
    rw [← loc_smul, ← hc]
    rfl
  obtain ⟨c₁, h₁⟩ := key 1
  have hu : ∀ i, IsUnit (loc P π f' v i) := fun i =>
    isUnit_of_mul_isUnit_right (by rw [← h₁ i, map_one]; exact isUnit_one)
  refine preconnectedSpace_of_functions X' fun s => ?_
  obtain ⟨c, hc⟩ := key s
  by_cases h0 : c = 0
  · refine Or.inl (le_bot_iff.1 fun y hy => ?_)
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    have := (mem_basicOpen_rs (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s hi).2 hy
    rwa [hc, h0, map_zero, zero_mul, Scheme.basicOpen_zero] at this
  · refine Or.inr (top_unique fun y _ => ?_)
    obtain ⟨i, hi⟩ := exists_mem P (π y)
    refine (mem_basicOpen_rs (le_top : π ⁻¹ᵁ P.W i ≤ ⊤) s hi).1 ?_
    rw [hc]
    exact mem_of_isUnit (((IsUnit.mk0 c h0).map _).mul (hu i)) hi

theorem exists_geometricallyConnected_away_of_fibre : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Z : Scheme.{0}) (s : Z ⟶ Sp R) (K : Type) [Field K] (x : R →+* K), IsProjOver s → Smooth s → GeometricallyConnected (pullback.snd s (spMap x)) → ∃ f : R, x f ≠ 0 ∧ GeometricallyConnected (pullback.snd s (spMap (algebraMap R (Localization.Away f)))) := by
  intro R _ _ Z s K _ x hp hs hc
  have hp' : IsProjBy s := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver s).2 hp
  obtain ⟨P⟩ := nonempty_perf_of_smooth_isProjBy R Z s hs hp' _ (Inh.trivLB_isLB _)
  have hpr : IsProper s := isProper_of_isProjBy R Z s hp'
  have h₀ : IsPullback (pullback.fst s (spMap x)) (pullback.snd s (spMap x)) s
      (Spec.map (CommRingCat.ofHom x)) := IsPullback.of_hasPullback _ _
  have hbij := bijective_appTop_of_smooth_of_isProper_of_geometricallyConnected K _
    (pullback.snd s (spMap x)) inferInstance inferInstance hc
  obtain ⟨v, -, hu, hline⟩ := loc_of_triv P h₀ (Inh.trivLB_isLB _) (triv_pull _)
  obtain ⟨x₀, -⟩ := (pullback.snd s (spMap x)).surjective (⊥ : PrimeSpectrum K)
  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨i, hi⟩ := exists_mem P ((pullback.fst s (spMap x)) x₀)
    have h₁ := mem_of_isUnit (hu i) (y := x₀) hi
    rw [← zero_smul K (0 : Fin P.a → K), loc_smul, map_zero, zero_mul, Scheme.basicOpen_zero] at h₁
    exact h₁
  obtain ⟨δ, v₀, hδ, hker⟩ := exists_kernel_vector x P.D₀ v hv0 (hline hbij.2)
  let p : PrimeSpectrum R := s ((pullback.fst s (spMap x)) x₀)
  have hpx : ∀ a : R, a ∉ p.asIdeal → x a ≠ 0 := fun a ha h0 => by
    have e : p = Spec.map (CommRingCat.ofHom x) (pullback.snd s (spMap x) x₀) :=
      congrArg (fun t => t x₀) h₀.w
    apply ha
    rw [e]
    change x a ∈ (pullback.snd s (spMap x) x₀).asIdeal
    rw [h0]
    exact zero_mem _
  obtain ⟨_, ⟨ε, rfl⟩, hε, hεs⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show p ∈ (Set.range s : Set (PrimeSpectrum R)) from ⟨_, rfl⟩) s.isOpenMap.isOpen_range
  refine ⟨δ * ε, by rw [map_mul]; exact mul_ne_zero hδ (hpx ε hε), ?_⟩
  refine ⟨geometrically_iff_of_commRing.2 fun F _ _ Y fst snd h => ?_⟩
  let g : R →+* F := (algebraMap (Localization.Away (δ * ε)) F).comp (algebraMap R _)
  have hg : IsUnit (g δ * g ε) := by
    rw [← map_mul]
    exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (δ * ε)) (δ * ε)).map
      (algebraMap (Localization.Away (δ * ε)) F)
  have h' : IsPullback (fst ≫ pullback.fst s (spMap (algebraMap R (Localization.Away (δ * ε))))) snd s
      (Spec.map (CommRingCat.ofHom g)) := by
    have := h.paste_horiz (IsPullback.of_hasPullback s _)
    rwa [← Spec.map_comp] at this
  have hmem : Spec.map (CommRingCat.ofHom g) (⊥ : PrimeSpectrum F) ∈ Set.range s :=
    hεs fun h0 : g ε ∈ (⊥ : Ideal F) => (isUnit_of_mul_isUnit_right hg).ne_zero h0
  obtain ⟨z, hz⟩ := hmem
  obtain ⟨y, -⟩ := Scheme.exists_preimage_of_isPullback h' z _ hz
  have := preconnectedSpace_of_line P h' _ (hker F _ (isUnit_of_mul_isUnit_left hg))
  exact ⟨⟨y⟩⟩

end GlobalTheory.ConnSpread
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.GrpFamOfDenseFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

namespace GlobalTheory.ZM.NearBuild.Fibre

theorem mem_range_spMap {R K : Type} [CommRing R] [Field K] (x : R →+* K) (p : Sp R)
    (h : RingHom.ker x = PrimeSpectrum.asIdeal (R := R) p) : p ∈ Set.range (spMap x) := by
  refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), ?_⟩
  apply PrimeSpectrum.ext
  rw [← h]
  rfl

theorem basis_pow {G : Type} [CommGroup G] {r k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0) (y : Fin r → G)
    (hy : ∀ i, y i ^ (k * l) = 1)
    (h : ∀ z : G, z ^ (k * l) = 1 → ∃! c : Fin r → ZMod (k * l), ∏ i, y i ^ (c i).val = z)
    (z : G) (hz : z ^ k = 1) : ∃! c : Fin r → ZMod k, ∏ i, (y i ^ l) ^ (c i).val = z := _root_.GlobalTheory.DensePol.basis_pow (G := G) (r := r) (k := k) (l := l) hk hl y hy h z hz

variable {S S' : Scheme.{0}}

theorem basis_pow_linComb {A T : Over S} [GrpObj A] [IsCommMonObj A] {r k l N : ℕ} (hN : N = k * l) (hN0 : N ≠ 0)
    (u : T ⟶ Out.baseOver S) (y : Fin r → (Out.baseOver S ⟶ A)) (hy : ∀ i, y i ^ N = 1)
    (h : ∀ z : T ⟶ A, z ^ N = 1 → ∃! c : Fin r → ZMod N, Out.linComb (fun i => u ≫ y i) (fun i => (c i).val) = z)
    (z : T ⟶ A) (hz : z ^ k = 1) :
    ∃! c : Fin r → ZMod k, Out.linComb (fun i => u ≫ y i ^ l) (fun i => (c i).val) = z := by
  subst hN
  simp only [Out.linComb, List.prod_ofFn, MonObj.comp_pow] at h ⊢
  exact basis_pow (left_ne_zero_of_mul hN0) (right_ne_zero_of_mul hN0) _
    (fun i => by rw [← MonObj.comp_pow, hy, MonObj.comp_one]) h z hz

variable {A : Over S'} {Z : Over S} {x : S' ⟶ S} {φ : A.left ⟶ Z.left}

theorem comp_eq_pushPt (w : φ ≫ Z.hom = A.hom ≫ x) {a : Out.baseOver S' ⟶ A} {s : Out.baseOver S ⟶ Z}
    (h : a.left ≫ φ = x ≫ s.left) {T : Over S'} (u : T ⟶ Out.baseOver S')
    (t : Over.mk (T.hom ≫ x) ⟶ Out.baseOver S) : t ≫ s = pushPt w (u ≫ a) := by
  apply Over.OverMorphism.ext
  have h1 : t.left = T.hom ≫ x := by simpa using Over.w t
  have h2 : u.left = T.hom := by simpa using Over.w u
  change t.left ≫ s.left = (u.left ≫ a.left) ≫ φ
  rw [h1, h2, Category.assoc, Category.assoc, h]

theorem basis_push [GrpObj A] [GrpObj Z] (hφ : IsGrpPullback A Z x φ) {r k : ℕ}
    {a : Fin r → (Out.baseOver S' ⟶ A)} {s : Fin r → (Out.baseOver S ⟶ Z)}
    (h : ∀ i, (a i).left ≫ φ = x ≫ (s i).left) {T : Over S'} (u : T ⟶ Out.baseOver S')
    (t : Over.mk (T.hom ≫ x) ⟶ Out.baseOver S)
    (hb : ∀ z : T ⟶ A, z ^ k = 1 → ∃! c : Fin r → ZMod k, Out.linComb (fun i => u ≫ a i) (fun i => (c i).val) = z)
    (z : Over.mk (T.hom ≫ x) ⟶ Z) (hz : z ^ k = 1) :
    ∃! c : Fin r → ZMod k, Out.linComb (fun i => t ≫ s i) (fun i => (c i).val) = z := by
  have inj : Function.Injective (pushHom hφ T) := fun y y' e =>
    Over.OverMorphism.ext (hφ.1.hom_ext (congrArg (fun z => z.left) e) ((Over.w y).trans (Over.w y').symm))
  obtain ⟨z, rfl⟩ := GrpDense.pushPt_surjective hφ.1 T z
  change pushHom hφ T z ^ k = 1 at hz
  rw [← map_pow, map_eq_one_iff _ inj] at hz
  have key : ∀ e : Fin r → ℕ, Out.linComb (fun i => t ≫ s i) e =
      pushHom hφ T (Out.linComb (fun i => u ≫ a i) e) := fun e => by
    simp only [Out.linComb, map_list_prod, List.map_ofFn]
    congr 2
    funext i
    rw [comp_eq_pushPt hφ.1.w (h i) u t]
    exact (map_pow (pushHom hφ T) _ _).symm
  simp only [key]
  change ∃! c : Fin r → ZMod k, _ = pushHom hφ T z
  simp only [inj.eq_iff]
  exact hb z hz

theorem lab_single {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) (i : Fin (2 * g)) : t.lab (Pi.single i 1) = t.pt i := by
  have := t.ab.comm
  rw [TObj.lab, Out.linComb, List.prod_ofFn, Finset.prod_eq_single i]
  · rw [Pi.single_eq_same, ← Nat.cast_one, ZMod.val_natCast, ← pow_eq_pow_mod _ (t.torsion i), pow_one]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, ZMod.val_zero, pow_zero]
  · simp

theorem lab_zero {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
    (t : TObj g k J b s) : t.lab 0 = 1 := by
  have := t.ab.comm
  rw [TObj.lab, Out.linComb, List.prod_ofFn]
  simp

theorem one_left {A : Over S} [GrpObj A] : (1 : Out.baseOver S ⟶ A).left = (η[A]).left :=
  Category.id_comp _

end GlobalTheory.ZM.NearBuild.Fibre

namespace GlobalTheory.ZM.NearBuild

open Fibre

theorem grpFam_of_dense_fibres :
    Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (m : ℕ) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g (N' ^ 2) → M.Sec) (sc : Ix g (N' ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (mu : Z ⊗ Z ⟶ Z) (F : Option J → (Z ⟶ Z)), N' ≠ 0 → DenseP (objPrimes b Mat κ β v) → Fam b Mat κ β v m M th sc → SmoothOfRelativeDimension g Z.hom → GeometricallyConnected Z.hom → AddAt b Mat κ β v m M th sc mu → (∀ i, EndAt b Mat κ β v m M th sc i (F i)) → ∃ _ : GrpObj Z, GrpFam b Mat κ β v m Z M (fun i => F (some i)) (fun i => sc (Pi.single i 1)) := by
  intro hL _ o _ g N' J b Mat κ R _ _ _ β v m Z M th sc mu F hN0 hden ⟨⟨I, p, hrep, _⟩, _, hfib⟩ hsm hgc hm hF
  haveI : NeZero (N' ^ 2) := ⟨pow_ne_zero _ hN0⟩
  have hun : IsUnit (N' : R) := by
    have := b.unit.map β
    rw [map_natCast, Nat.cast_pow, isUnit_pow_iff two_ne_zero] at this
    exact this
  obtain ⟨-, hpr, hamp⟩ := GlobalTheory.ZM.projRep_projective_ample R _ I Z M th hrep
  have hD := dense_of_denseP hden
  have hs : Smooth Z.hom := SmoothOfRelativeDimension.smooth g _
  have s1 : Smooth (Out.baseOver (Sp R)).hom := inferInstanceAs (Smooth (𝟙 _))
  have h0 : ∀ {K : Type} [Field K] {x : R →+* K} {s : Sp K ⟶ Sp o} (t' : TObj g (N' ^ 2) J b s)
      {φ : t'.A.left ⟶ Z.left}, (∀ h, (t'.lab h ^ N').left ≫ φ = spMap x ≫ (sc h).left) →
      (1 : Out.baseOver _ ⟶ t'.A).left ≫ φ = spMap x ≫ (sc 0).left := fun t' φ h => by
    have := h 0
    rwa [lab_zero, one_pow] at this
  have h1 : ∀ {K : Type} [Field K] {x : R →+* K} {s : Sp K ⟶ Sp o} (t' : TObj g (N' ^ 2) J b s)
      {φ : t'.A.left ⟶ Z.left}, (∀ h, (t'.lab h ^ N').left ≫ φ = spMap x ≫ (sc h).left) →
      ∀ i, (t'.pt i ^ N').left ≫ φ = spMap x ≫ (sc (Pi.single i 1)).left := fun t' φ h i => by
    have := h (Pi.single i 1)
    rwa [lab_single] at this
  obtain ⟨_, -, hη, -, hab, hgp⟩ := grpObj_of_dense_fibres R Z mu (F none) (sc 0) _ hD hs hpr hgc (by
    intro q hq
    obtain ⟨K, _, _, x, s, t', hx, ht⟩ := mem_objPrimes.1 hq
    obtain ⟨φ, hφ⟩ := hfib K x s t' ht
    refine ⟨K, inferInstance, spMap x, t'.A, inferInstance, φ, mem_range_spMap x q hx, t'.ab.comm, hφ.1,
      hm K x s t' φ ht hφ, ?_, ?_⟩
    · have := hF none K x s t' φ ht hφ
      rwa [Option.elim, Hom.inv_def, Category.id_comp] at this
    · rw [← one_left, h0 t' hφ.2.2.2])
  have := hab.comm
  have hhom : ∀ i, IsMonHom (F (some i)) := fun i => hL.rigidity _ Z Z hab hab _ (by
    rw [hη]
    refine FibreGrp.hom_ext_of_fibres (X := Out.baseOver (Sp R)) hD ?_
    intro q hq
    obtain ⟨K, _, _, x, s, t', hx, ht⟩ := mem_objPrimes.1 hq
    obtain ⟨φ, hφ⟩ := hfib K x s t' ht
    refine ⟨_, spMap x, mem_range_spMap x q hx, fun T t => ?_⟩
    rw [← Category.assoc, comp_eq_pushPt hφ.1.w (h0 t' hφ.2.2.2) (toUnit T) t]
    have := t'.hom i
    have e : (toUnit T ≫ (1 : Out.baseOver _ ⟶ t'.A)) ≫ t'.act i = toUnit T ≫ (1 : Out.baseOver _ ⟶ t'.A) := by
      rw [Category.assoc, MonObj.one_comp]
    apply Over.OverMorphism.ext
    change (_ ≫ φ) ≫ (F (some i)).left = _ ≫ φ
    rw [Category.assoc, hF (some i) K x s t' φ ht hφ, ← Category.assoc, ← Over.comp_left]
    exact congrArg (fun z => z.left ≫ φ) e)
  have htor : ∀ {K : Type} [Field K] {s : Sp K ⟶ Sp o} (t' : TObj g (N' ^ 2) J b s) (i),
      (t'.pt i ^ N') ^ N' = 1 := fun t' i => by
    have e : N' * N' = N' ^ 2 := (pow_two _).symm
    rw [← pow_mul (t'.pt i), e, t'.torsion]
  have hQ : ∀ i, sc (Pi.single i 1) ^ N' = 1 := fun i => by
    refine FibreGrp.hom_ext_of_fibres (X := Out.baseOver (Sp R)) hD ?_
    intro q hq
    obtain ⟨K, _, _, x, s, t', hx, ht⟩ := mem_objPrimes.1 hq
    obtain ⟨φ, hφ⟩ := hfib K x s t' ht
    refine ⟨_, spMap x, mem_range_spMap x q hx, fun T t => ?_⟩
    rw [MonObj.comp_pow, MonObj.comp_one, comp_eq_pushPt hφ.1.w (h1 t' hφ.2.2.2 i) (toUnit T) t]
    change pushHom (hgp _ _ _ φ hφ.1 (hm K x s t' φ ht hφ)) T _ ^ _ = 1
    rw [← map_pow]
    erw [← MonObj.comp_pow]
    rw [htor]
    erw [MonObj.comp_one]
    rw [map_one]
  have hB := torsion_basis_of_dense (Sp R) Z N' (2 * g) (fun i => sc (Pi.single i 1)) _ hab
    (Nat.pos_of_ne_zero hN0) (by
      have := hun.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      simpa using this) hQ hD (by
      intro q hq
      obtain ⟨K, _, _, x, s, t', hx, ht⟩ := mem_objPrimes.1 hq
      obtain ⟨φ, hφ⟩ := hfib K x s t' ht
      have := t'.ab.comm
      refine ⟨K, inferInstance, inferInstance, 𝟙 _ ≫ spMap x, by simpa using mem_range_spMap x q hx, ?_⟩
      exact basis_push (hgp _ _ _ φ hφ.1 (hm K x s t' φ ht hφ)) (h1 t' hφ.2.2.2) (T := Over.mk (𝟙 _)) _ _
        (basis_pow_linComb (pow_two _) (NeZero.ne _) _ t'.pt t'.torsion (t'.bij K (𝟙 _))))
  refine ⟨inferInstance, hab, hsm, hrep.1, hamp, ⟨hhom, hQ, hB⟩, fun K _ _ x s t' ht => ?_⟩
  obtain ⟨φ, hφ⟩ := hfib K x s t' ht
  exact ⟨φ, ⟨hgp _ _ _ φ hφ.1 (hm K x s t' φ ht hφ), fun i => (hF (some i) K x s t' φ ht hφ).symm,
    h1 t' hφ.2.2.2⟩, hφ.2.2.1⟩

end GlobalTheory.ZM.NearBuild
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolFamBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

open GlobalTheory.ThetaObjPull GlobalTheory.PolBaseChange

theorem polFam_baseChange : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (A : Over (Sp R)) [GrpObj A] (L : LB A.left) (act : J → (A ⟶ A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)) (R' : Type) [CommRing R'] (ρ : R →+* R'), PolFam b Mat κ β v A L act Q → ∃ act' Q', PolFam b Mat κ (ρ.comp β) (fun a => ρ (v a)) ((Over.pullback (spMap ρ)).obj A) (L.pull (pullback.fst A.hom (spMap ρ))) act' Q' := by
  intro o _ g N' J b Mat κ R _ β v A _ L act Q R' _ ρ ⟨hab, hdim, hL, hrig, hsym, hamp, ⟨hhom, htor, hbij⟩, hfib⟩
  have h := isGrpPullback_pullback A (spMap ρ)
  have hL' := LB.isLB_pull hL (pullback.fst A.hom (spMap ρ))
  have hiso := lbIso_refl hL'
  obtain ⟨hab', hamp', -⟩ := pol_pull _ _ _ _ _ _ _ _ hL hL' hab h hiso
  choose pt hpt using fun i => exists_sec h (Q i)
  have hpt' : ∀ i, (pt i).left ≫ pullback.fst A.hom (spMap ρ) = spMap ρ ≫ (Q i).left := fun i =>
    congrArg (fun z => z.left) (hpt i)
  have := hab.comm
  refine ⟨fun j => (Over.pullback (spMap ρ)).map (act j), pt, hab',
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 hdim, hL', rigidified_pull h hrig,
    sym_pull h hsym, hamp' hamp, ⟨fun j => inferInstance, fun i => pushHom_injective h _ ?_,
      fun K _ _ x y hy => ?_⟩, fun K _ _ x s t ht => ?_⟩
  · rw [map_pow, map_one, hpt]
    exact (map_pow (preHom (toBase (spMap ρ))) _ _).symm.trans (by rw [htor, map_one])
  · have key : ∀ c : Ix g N', pushHom h (Over.mk x) (Out.linComb (fun i =>
        (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R')) ≫ pt i) (fun i => (c i).val)) =
        Out.linComb (fun i => (Over.homMk (x ≫ spMap ρ) (by simp) :
          Over.mk (x ≫ spMap ρ) ⟶ Out.baseOver (Sp R)) ≫ Q i) (fun i => (c i).val) := fun c => by
      rw [map_linComb]
      congr 1
      funext i
      apply Over.OverMorphism.ext
      show (x ≫ (pt i).left) ≫ _ = (x ≫ spMap ρ) ≫ (Q i).left
      rw [Category.assoc, hpt', Category.assoc]
    have hy' : pushHom h (Over.mk x) y ^ N' = 1 := by rw [← map_pow, hy, map_one]
    obtain ⟨c, hc, hu⟩ := hbij K (x ≫ spMap ρ) (pushHom h (Over.mk x) y) hy'
    exact ⟨c, pushHom_injective h _ ((key c).trans hc), fun c' hc' => hu c' ((key c').symm.trans (congrArg _ hc'))⟩
  · obtain ⟨ψ, ⟨k₁, k₄, k₃⟩, k₂⟩ := hfib K (x.comp ρ) s t ((good_comp _ _ _).1 ht)
    rw [spMap_comp] at k₁ k₃
    have hp := h.1
    obtain ⟨F, hF, hw⟩ : ∃ F : t.A.left ⟶ ((Over.pullback (spMap ρ)).obj A).left,
        F ≫ pullback.fst A.hom (spMap ρ) = ψ ∧
        F ≫ ((Over.pullback (spMap ρ)).obj A).hom = t.A.hom ≫ spMap x :=
      ⟨hp.lift ψ (t.A.hom ≫ spMap x) (by rw [k₁.1.w, Category.assoc]), hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
    subst hF
    have h₄ : ∀ j, ((Over.pullback (spMap ρ)).map (act j)).left ≫ pullback.fst A.hom (spMap ρ) =
        pullback.fst A.hom (spMap ρ) ≫ (act j).left := fun j => pullback.lift_fst _ _ _
    refine ⟨F, ⟨h.cancel k₁ hw, fun j => ?_, fun i => ?_⟩, ?_⟩
    · apply hp.hom_ext
      · rw [Category.assoc, k₄, Category.assoc, Category.assoc, h₄]
      · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w, hw]
    · apply hp.hom_ext
      · rw [Category.assoc, k₃, Category.assoc, Category.assoc, hpt']
      · have a₁ : (t.pt i ^ N').left ≫ t.A.hom = 𝟙 _ := Over.w (t.pt i ^ N')
        have a₂ : (pt i).left ≫ ((Over.pullback (spMap ρ)).obj A).hom = 𝟙 _ := Over.w (pt i)
        rw [Category.assoc, hw, ← Category.assoc, a₁, Category.assoc, a₂]
        exact (Category.id_comp _).trans (Category.comp_id _).symm
    · exact LBIso.trans t.isLB (LB.isLB_pull hL _) (LB.isLB_pull hL' _) k₂ (lbIso_pull_comp hiso F).symm

end GlobalTheory.ZM.NearBuild
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLocLoc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

theorem concl_map (hL : Out.Laws2) {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
    {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ} {R R' : Type} [CommRing R] [CommRing R']
    {β : o →+* R} {v : Ix g (N' ^ 2) → R} (h : Concl b Mat κ β v) (ρ : R →+* R') :
    Concl b Mat κ (ρ.comp β) (fun a => ρ (v a)) := by
  obtain ⟨t, hth, hall⟩ := h
  have hs : spMap ρ ≫ spMap β = spMap (ρ.comp β) := (spMap_comp ρ β).symm
  obtain ⟨t₂, h₂⟩ := GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback o g (N' ^ 2) J b (Sp R) (Sp R') (spMap β) (spMap (ρ.comp β)) (spMap ρ) t hs
  refine ⟨t₂, ?_, ?_⟩
  · rw [GlobalTheory.T.hasThetaConstants_iff_of_thetaLevelPullback o g N' J b (Sp R) (spMap β) t (Sp R') (spMap (ρ.comp β)) t₂ (spMap ρ) R' (𝟙 _) _ h₂,
      Category.id_comp]
    have hpush := GlobalTheory.T.hasThetaConstants_ring_baseChange hL o g N' J b (Sp R) (spMap β) t R R' ρ (𝟙 _) v hth
    rwa [Category.comp_id] at hpush
  · intro K _ _ x s t' hg
    rw [good_comp] at hg
    have h3 := hall K (x.comp ρ) s t' hg
    rw [spMap_comp] at h3
    exact ((GlobalTheory.T.thetaLevelPullback_id_comp_cancel o g (N' ^ 2) J b (Sp R) (Sp R') (Sp K) (spMap β) (spMap (ρ.comp β)) s t t₂ t').2
      (spMap ρ) (spMap x) h₂).2 h3

theorem exists_loc_loc {R : Type} [CommRing R] (f : R) (q₁ : Ideal (Localization.Away f)) (hq : q₁.IsPrime)
    (f' : Localization.Away f) (hf' : f' ∉ q₁) :
    ∃ F : R, F ∉ q₁.comap (loc f) ∧ ∃ ρ : Localization.Away f' →+* Localization.Away F,
      (ρ.comp (loc f')).comp (loc f) = loc F := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj f f'
  have hunit : IsUnit (loc f f) := IsLocalization.Away.algebraMap_isUnit f
  have hfq : loc f f ∉ q₁ := fun hm => hq.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hunit)
  refine ⟨f * a, ?_, ?_⟩
  · intro hm
    rw [Ideal.mem_comap, map_mul] at hm
    rcases hq.mem_or_mem hm with h1 | h1
    · exact hfq h1
    · have h2 : f' * algebraMap R (Localization.Away f) f ^ n ∈ q₁ := by rw [ha]; exact h1
      rcases hq.mem_or_mem h2 with h3 | h3
      · exact hf' h3
      · exact hfq (hq.mem_of_pow_mem n h3)
  · have hF : IsUnit (loc (f * a) (f * a)) := IsLocalization.Away.algebraMap_isUnit (f * a)
    rw [map_mul] at hF
    have hf1 : IsUnit (loc (f * a) f) := isUnit_of_mul_isUnit_left hF
    have ha1 : IsUnit (loc (f * a) a) := isUnit_of_mul_isUnit_right hF
    have hσ : (IsLocalization.Away.lift f hf1).comp (loc f) = loc (f * a) := IsLocalization.Away.lift_comp f hf1
    have e : IsLocalization.Away.lift f hf1 f' * IsLocalization.Away.lift f hf1 (loc f f) ^ n = loc (f * a) a := by
      rw [← map_pow, ← map_mul, ha]
      exact RingHom.congr_fun hσ a
    rw [← e] at ha1
    have hu : IsUnit (IsLocalization.Away.lift f hf1 f') := isUnit_of_mul_isUnit_left ha1
    refine ⟨IsLocalization.Away.lift f' hu, ?_⟩
    rw [IsLocalization.Away.lift_comp f' hu]
    exact hσ

theorem nearC_of_loc : Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (f : R) (q₁ : Ideal (Localization.Away f)), q₁.IsPrime → NearC b Mat κ ((loc f).comp β) (fun a => loc f (v a)) q₁ → NearC b Mat κ β v (q₁.comap (loc f)) := by
  intro hL o _ g N' J b Mat κ R _ β v f q₁ hq h
  obtain ⟨f', hf', hc⟩ := h
  obtain ⟨F, hF, ρ, hρ⟩ := exists_loc_loc f q₁ hq f' hf'
  refine ⟨F, hF, ?_⟩
  have key : ∀ r : R, ρ (loc f' (loc f r)) = loc F r := fun r => RingHom.congr_fun hρ r
  have hc2 : Concl b Mat κ (ρ.comp ((loc f').comp ((loc f).comp β))) (fun a => ρ (loc f' (loc f (v a)))) :=
    concl_map hL hc ρ
  have e1 : ρ.comp ((loc f').comp ((loc f).comp β)) = (loc F).comp β := RingHom.ext fun r => key (β r)
  have e2 : (fun a => ρ (loc f' (loc f (v a)))) = fun a => loc F (v a) := funext fun a => key (v a)
  rw [e1, e2] at hc2
  exact hc2

end GlobalTheory.ZM.NearBuild
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSectionsFam
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.FamOf

theorem spMap_id (R : Type) [CommRing R] : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id _

section Unit
variable {S : Scheme.{0}} (A : Over S)

def unitInv : A ⟶ Over.mk (𝟙 S) ⊗ A := lift (Over.homMk A.hom (by simp)) (𝟙 A)

theorem unitInv_snd : (unitInv A).left ≫ (snd (Over.mk (𝟙 S)) A).left = 𝟙 _ := by
  rw [← Over.comp_left, unitInv, lift_snd]; rfl

theorem to_base_ext {T : Over S} (f f' : T ⟶ Over.mk (𝟙 S)) : f = f' :=
  Over.mkIdTerminal.hom_ext f f'

theorem snd_unitInv : (snd (Over.mk (𝟙 S)) A).left ≫ (unitInv A).left = 𝟙 _ := by
  rw [← Over.comp_left]
  have : snd (Over.mk (𝟙 S)) A ≫ unitInv A = 𝟙 _ :=
    CartesianMonoidalCategory.hom_ext _ _ (to_base_ext _ _) (by simp [unitInv])
  rw [this]; rfl

theorem unitInv_fst : (unitInv A).left ≫ (fst (Over.mk (𝟙 S)) A).left = A.hom := by
  rw [← Over.comp_left, unitInv, lift_fst]; rfl

theorem pt_unitInv (z : Over.mk (𝟙 S) ⟶ A) : z.left ≫ (unitInv A).left = (lift (𝟙 (Over.mk (𝟙 S))) z).left := by
  rw [← Over.comp_left]
  congr 1
  exact CartesianMonoidalCategory.hom_ext _ _ (to_base_ext _ _) (by simp [unitInv])

theorem isPullback_unitInv : IsPullback (unitInv A).left A.hom (fst (Over.mk (𝟙 S)) A).left (𝟙 S) := by
  haveI : IsIso (unitInv A).left := ⟨_, unitInv_snd A, snd_unitInv A⟩
  exact IsPullback.of_horiz_isIso ⟨by rw [unitInv_fst, Category.comp_id]⟩

def chartPullUnit (L : LB A.left) (k : ℕ) (a : ℤ) (ha : a = k) :
    ChartPull (lbPow L k) (Out.LPow A L a (Over.mk (𝟙 S))) (unitInv A).left :=
  have le : ∀ j : PUnit → L.ι, LB.wchart L (fun _ : PUnit => 𝟙 A.left) j ≤ (unitInv A).left ⁻¹ᵁ
      LB.wchart L (fun _ : Fin 1 => (snd (Over.mk (𝟙 S)) A).left) (fun _ => j PUnit.unit) :=
    fun j y hy => Set.mem_iInter.2 fun _ => by
      have h1 : y ∈ L.U (j PUnit.unit) := Set.mem_iInter.1 hy PUnit.unit
      show ((unitInv A).left ≫ (snd (Over.mk (𝟙 S)) A).left) y ∈ L.U (j PUnit.unit)
      rw [unitInv_snd]; exact h1
  { idx := fun j _ => j PUnit.unit
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L (fun _ : PUnit => 𝟙 A.left) (fun _ => (k : ℤ)) (𝟙 _) y j j' hj hj').trans
        (Eq.trans ?_ (gm_linComb L (fun _ : Fin 1 => (snd (Over.mk (𝟙 S)) A).left) (fun _ => a) (unitInv A).left y _ _
          (le j hj) (le j' hj')).symm)
      rw [Fintype.prod_unique, Fintype.prod_unique, unitInv_snd, Category.comp_id, ha] }

end Unit

theorem pt_unique {R σ : Type} [CommRing R] {I : Ideal (MvPolynomial σ R)} {Z : Scheme.{0}} {s : Z ⟶ Sp R}
    {M : LB Z} {th : σ → M.Sec} (hP : ProjRep I s M th) {T : Type} [CommRing T] {β : R →+* T} {y y' : Sp T ⟶ Z}
    {w : σ → T} (hy : y ≫ s = spMap β) (hy' : y' ≫ s = spMap β) (hc : SecCoord M th y w) (hc' : SecCoord M th y' w) :
    y = y' := by
  obtain ⟨h1, h2⟩ := hP.2.1 T β y w hy hc
  exact (hP.2.2 T β w h1 h2).unique ⟨hy, hc⟩ ⟨hy', hc'⟩

theorem fibre_of_unit {R K σ : Type} [CommRing R] [CommRing K] {x : R →+* K} {Z : Scheme.{0}} {s : Z ⟶ Sp R} {M : LB Z}
    {th : σ → M.Sec} (A : Over (Sp K)) (L : LB A.left) (k : ℕ) (a : ℤ) (ha : a = k)
    (th' : σ → (Out.LPow A L a (Over.mk (𝟙 (Sp K)))).Sec) (φ₀ : (Over.mk (𝟙 (Sp K)) ⊗ A).left ⟶ Z)
    (h1 : IsPullback φ₀ (fst (Over.mk (𝟙 (Sp K))) A).left s (spMap x))
    (h2 : LBIso (Out.LPow A L a (Over.mk (𝟙 (Sp K)))) (M.pull φ₀))
    (h3 : ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ A).left) (w : σ → T),
      SecCoord _ th' y w ↔ SecCoord M th (y ≫ φ₀) w) :
    ∃ φ : A.left ⟶ Z, IsPullback φ A.hom s (spMap x) ∧
      (∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ A).left) (w : σ → T),
        SecCoord _ th' y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) A).left ≫ φ) w) ∧
      LBIso (lbPow L k) (M.pull φ) ∧
      ∀ (z : Over.mk (𝟙 (Sp K)) ⟶ A) (w : σ → K), SecCoord _ th' (lift (𝟙 (Over.mk (𝟙 (Sp K)))) z).left w →
        SecCoord M th (z.left ≫ φ) w := _root_.GlobalTheory.ZM.FamilyScheme.fibre_of_unit (R := R) (K := K) (σ := σ) (x := x) (Z := Z) (s := s) (M := M) (th := th) A L k a ha th' φ₀ h1 h2 h3

theorem exists_section {R σ : Type} [CommRing R] {I : Ideal (MvPolynomial σ R)} {Z : Over (Sp R)}
    {M : LB Z.left} {th : σ → M.Sec} (hP : ProjRep I Z.hom M th) (p : σ → R) {P : Set (Ideal R)} (hd : DenseP P)
    (hu : Ideal.span (Set.range p) = ⊤)
    (h : ∀ q ∈ P, ∃ (K : Type) (_ : Field K) (x : R →+* K) (y : Sp K ⟶ Z.left), RingHom.ker x = q ∧
      y ≫ Z.hom = spMap x ∧ SecCoord M th y (fun a => x (p a))) :
    ∃ sc : Out.baseOver (Sp R) ⟶ Z, SecCoord M th sc.left p := by
  have hF : ∀ F ∈ I, MvPolynomial.eval₂ (RingHom.id R) p F = 0 := by
    intro F hF
    refine hd _ fun q hq _ => ?_
    obtain ⟨K, _, x, y, hx, hy, hc⟩ := h q hq
    have h1 := (hP.2.1 K x y _ hy hc).2 F hF
    rw [← hx, RingHom.mem_ker, MvPolynomial.eval₂_comp_left, RingHom.comp_id]
    exact h1
  obtain ⟨y, ⟨hy, hc⟩, -⟩ := hP.2.2 R (RingHom.id R) p hu hF
  exact ⟨Over.homMk y (hy.trans (spMap_id R)), hc⟩

theorem exists_sections_fam : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] [IsReduced R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (m : ℕ) (p : Ix g (N' ^ 2) → Ix g (N' ^ 2) → R) (Hh : Type) (hh : Hh → Ix g (N' ^ 2)) (Q : Polynomial ℚ) (d : ℕ) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g (N' ^ 2) → M.Sec), DenseP (objPrimes b Mat κ β v) → FibData b Mat κ β v m p hh Q d → (∀ h, Ideal.span (Set.range (p h)) = ⊤) → ProjRep (vanIdeal d (fun h i => p (hh h) i)) Z.hom M th → Flat Z.hom → (∀ (K : Type) [Field K] (x : R →+* K) (I : Ideal (MvPolynomial (Ix g (N' ^ 2)) K)) (X : Scheme.{0}) (s : X ⟶ Sp K) (M' : LB X) (th' : Ix g (N' ^ 2) → M'.Sec), (∀ F ∈ I, ∀ e, MvPolynomial.homogeneousComponent e F ∈ I) → CutBy I Q d (fun h i => x (p (hh h) i)) → ProjRep I s M' th' → ∃ φ : X ⟶ Z.left, IsPullback φ s Z.hom (spMap x) ∧ LBIso M' (M.pull φ) ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ X) (w : Ix g (N' ^ 2) → T), SecCoord M' th' y w ↔ SecCoord M th (y ≫ φ) w) → ∃ sc, Fam b Mat κ β v m M th sc := by
  intro o _ g N' J b Mat κ R _ _ β v m p Hh hh Q d Z M th hd hfib hu hZ hflat hφ
  have key : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (s : Sp K ⟶ Sp o) (t' : TObj g (N' ^ 2) J b s),
      Good b Mat κ β v x t' → ∃ φ : t'.A.left ⟶ Z.left, IsPullback φ t'.A.hom Z.hom (spMap x) ∧
      (∃ σ, t'.Emb m (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T]
        (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g (N' ^ 2) → T),
        SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧
      LBIso (lbPow t'.L (m ^ 2)) (M.pull φ) ∧
      ∀ h, ((t'.lab h ^ N').left ≫ φ) ≫ Z.hom = spMap x ∧
        SecCoord M th ((t'.lab h ^ N').left ≫ φ) (fun a => x (p h a)) := by
    intro K _ _ x s t' ht
    obtain ⟨σ, I, hE, hP, hI, hc, hs⟩ := hfib K x s t' ht
    obtain ⟨φ₀, a1, a2, a3⟩ := hφ K x I _ _ _ σ hI hc hP
    obtain ⟨φ, b1, b2, b3, b4⟩ := fibre_of_unit t'.A t'.L (m ^ 2) _ (Nat.cast_pow m 2).symm σ φ₀ a1 a2 a3
    refine ⟨φ, b1, ⟨σ, hE, b2⟩, b3, fun h => ⟨?_, b4 _ _ (hs h)⟩⟩
    rw [Category.assoc, b1.w, ← Category.assoc, Over.w]
    exact Category.id_comp _
  have hsc : ∀ h, ∃ sc : Out.baseOver (Sp R) ⟶ Z, SecCoord M th sc.left (p h) := fun h =>
    exists_section hZ (p h) hd (hu h) (by
      intro q hq
      obtain ⟨K, _, _, x, s, t', hx, ht⟩ := mem_objPrimes.1 hq
      obtain ⟨φ, -, -, -, h4⟩ := key K x s t' ht
      exact ⟨K, inferInstance, x, _, hx, h4 h⟩)
  choose sc hsc using hsc
  refine ⟨sc, ⟨_, p, hZ, hsc⟩, hflat, fun K _ _ x s t' ht => ?_⟩
  obtain ⟨φ, h1, h2, h3, h4⟩ := key K x s t' ht
  refine ⟨φ, h1, h2, h3, fun h => pt_unique hZ (h4 h).1 ?_ (h4 h).2
    ((Coord.secCoord_bc_scale_unique _ M _ th R _ _ hZ.1 (hsc h)).1 K x)⟩
  rw [Category.assoc, Over.w]
  exact Category.comp_id _

end GlobalTheory.ZM.FamOf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ChartPullCompOfPullPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

def chartPullCompOfPullPull {X Y Z : Scheme.{0}} (M : LB X) (π : Y ⟶ X) (φ : Z ⟶ Y) :
    ChartPull (M.pull (φ ≫ π)) ((M.pull π).pull φ) (𝟙 Z) where
  idx j := fun _ => j
  le j := RepBC.le₂ M π φ j
  g y j j' hj hj' := by
    have h := RepBC.le₂ M π φ j hj
    have h' := RepBC.le₂ M π φ j' hj'
    refine (gm_pull_g M (φ ≫ π) (𝟙 Z) y j j' hj hj').trans (Eq.symm ?_)
    refine (gm_pull_g (M.pull π) φ (𝟙 Z) y (fun _ => j) (fun _ => j') h h').trans ?_
    exact gm_pull_g M π (𝟙 Z ≫ φ) y j j' (mem_pull.1 h) (mem_pull.1 h')

theorem lbIso_pullPull_iff {X Y Z : Scheme.{0}} (A : LB Z) (M : LB X) (π : Y ⟶ X) (φ : Z ⟶ Y) :
    LBIso A ((M.pull π).pull φ) ↔ LBIso A (M.pull (φ ≫ π)) :=
  ⟨LBIso.chartPull (chartPullId A) (chartPullCompOfPullPull M π φ),
    LBIso.chartPull (chartPullId A) (chartPullLinComb M π (fun _ : PUnit => φ) (fun _ => φ ≫ π) (fun _ => 1) (𝟙 Z)
      fun _ => (Category.id_comp _).symm)⟩

theorem fam_baseChange : ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ) (R : Type) [CommRing R] (β : o →+* R) (v : Ix g (N' ^ 2) → R) (m : ℕ) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g (N' ^ 2) → M.Sec) (sc : Ix g (N' ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (R' : Type) [CommRing R'] (ρ : R →+* R') (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → Fam b Mat κ β v m M th sc → ∃ (th' : Ix g (N' ^ 2) → (M.pull π).Sec) (sc' : Ix g (N' ^ 2) → (Out.baseOver (Sp R') ⟶ Z')), Fam b Mat κ (ρ.comp β) (fun a => ρ (v a)) m (M.pull π) th' sc' ∧ ∀ (K : Type) [Field K] (x : R' →+* K) (s : Sp K ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (φ : t.A.left ⟶ Z'.left), Fib m (M.pull π) th' sc' x t φ → Fib m M th sc (x.comp ρ) t (φ ≫ π) := by
  intro o _ g N' J b Mat κ R _ β v m Z M th sc R' _ ρ Z' π hp ⟨⟨I, p, hrep, hco⟩, hflat, hfib⟩
  obtain ⟨th', hrep', hc⟩ := RepBC.projRep_baseChange R R' _ ρ I _ _ _ _ π M th hrep hp
  have hw : ∀ h, (spMap ρ ≫ (sc h).left) ≫ Z.hom = 𝟙 _ ≫ spMap ρ := fun h => by
    rw [Category.assoc, Over.w (sc h), Category.id_comp]
    exact Category.comp_id _
  let sc' : Ix g (N' ^ 2) → (Out.baseOver (Sp R') ⟶ Z') := fun h =>
    Over.homMk (hp.lift (spMap ρ ≫ (sc h).left) (𝟙 _) (hw h)) (hp.lift_snd _ _ _)
  have hsc : ∀ h, (sc' h).left ≫ π = spMap ρ ≫ (sc h).left := fun h => hp.lift_fst _ _ _
  have hsc' : ∀ h, (sc' h).left ≫ Z'.hom = 𝟙 _ := fun h => hp.lift_snd _ _ _
  refine ⟨th', sc', ⟨⟨_, fun h a => ρ (p h a), hrep', fun h => (hc _ _ _).2 ?_⟩,
    MorphismProperty.of_isPullback (P := @Flat) hp hflat, ?_⟩, ?_⟩
  · rw [hsc]
    exact Coord.baseChange (hco h) ρ
  · intro K _ _ x s t ht
    obtain ⟨φ, h1, ⟨σ, hσ, h2⟩, h3, h4⟩ := hfib K (x.comp ρ) s t ((good_comp _ _ _).1 ht)
    have hw' : φ ≫ Z.hom = (t.A.hom ≫ spMap x) ≫ spMap ρ := by
      rw [h1.w, NearBuild.spMap_comp, Category.assoc]
    have e1 : hp.lift φ _ hw' ≫ π = φ := hp.lift_fst _ _ _
    have e2 : hp.lift φ _ hw' ≫ Z'.hom = t.A.hom ≫ spMap x := hp.lift_snd _ _ _
    generalize hp.lift φ _ hw' = φ' at e1 e2
    subst e1
    refine ⟨φ', IsPullback.of_right (by rw [← NearBuild.spMap_comp]; exact h1) e2 hp, ⟨σ, hσ, fun T _ y w => ?_⟩,
      (lbIso_pullPull_iff _ _ _ _).2 h3, fun h => ?_⟩
    · rw [h2 T y w, hc, Category.assoc, Category.assoc]
    · apply hp.hom_ext
      · rw [Category.assoc, h4, NearBuild.spMap_comp]
        erw [Category.assoc, Category.assoc, hsc]
      · rw [Category.assoc, e2, ← Category.assoc, Over.w (t.lab h ^ N')]
        erw [Category.assoc, hsc', Category.id_comp]
  · rintro K _ x s t φ ⟨h1, ⟨σ, hσ, h2⟩, h3, h4⟩
    refine ⟨by rw [NearBuild.spMap_comp]; exact h1.paste_horiz hp, ⟨σ, hσ, fun T _ y w => ?_⟩,
      (lbIso_pullPull_iff _ _ _ _).1 h3, fun h => ?_⟩
    · rw [h2 T y w, hc, Category.assoc, Category.assoc]
    · rw [← Category.assoc, h4, NearBuild.spMap_comp]
      erw [Category.assoc, Category.assoc, hsc]

end GlobalTheory.ZM.NearBuild
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectNearGoodPrime
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild

noncomputable section
namespace GlobalTheory.ZM.NearBuild

section
variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)}
  {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ} {κ : ℕ} {R : Type} [CommRing R] {β : o →+* R} {v : Ix g (N' ^ 2) → R}

theorem nearC_of_den_loc (h2 : Out.Laws2) {q₀ : Ideal R} (h : Den b Mat κ β v q₀) {f : R} (hf : f ∉ q₀)
    (H : ∀ q₁, Den b Mat κ ((loc f).comp β) (fun a => loc f (v a)) q₁ →
      NearC b Mat κ ((loc f).comp β) (fun a => loc f (v a)) q₁) : NearC b Mat κ β v q₀ := by
  obtain ⟨q₁, hq₁, rfl⟩ := h.loc hf
  exact GlobalTheory.ZM.NearBuild.nearC_of_loc h2 o g N' J b Mat κ R β v f q₁ (isPrime_of_mem hq₁.2) (H q₁ hq₁)

theorem span_map {R' I : Type} [CommRing R'] (ρ : R →+* R') {w : I → R} (h : Ideal.span (Set.range w) = ⊤) :
    Ideal.span (Set.range fun a => ρ (w a)) = ⊤ := by
  have := congrArg (Ideal.map ρ) h
  rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this

theorem span_of_unit {R' I : Type} [CommRing R'] {w : I → R'} (a : I) (h : IsUnit (w a)) :
    Ideal.span (Set.range w) = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨a, rfl⟩) h

theorem isUnit_loc {f a : R} (h : a ∣ f) : IsUnit (loc f a) :=
  isUnit_of_dvd_unit (map_dvd _ h) (IsLocalization.Away.algebraMap_isUnit f)
end

section
variable (h1 : Out.Laws) (h2 : Out.Laws2) {g : ℕ} {J : Type} {Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ}
  {κ n j : ℕ} (hn : n.Prime) (hodd : Odd n) (hj : 2 ≤ j) {o : Type} [CommRing o] {b : TBase o ((n ^ j) ^ 2)}
include h1 h2 hn hodd hj

theorem nearC_of_grpFam {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
    {v : Ix g ((n ^ j) ^ 2) → R} {A : Over (Sp R)} [GrpObj A] {M : LB A.left} {act : J → (A ⟶ A)}
    {Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ A)} {q₀ : Ideal R} (h : Den b Mat κ β v q₀)
    (hv : Ideal.span (Set.range v) = ⊤) (hA : GrpFam b Mat κ β v (n ^ 2) A M act Q) : NearC b Mat κ β v q₀ := by
  obtain ⟨L, hL⟩ := GlobalTheory.ZM.NearBuild.exists_polFam_of_grpFam h1 h2 o g _ J b Mat κ R β v (n ^ 2) A M act Q (pow_ne_zero _ hn.ne_zero) hodd.pow
    (pow_dvd_pow n hj) h.1 hA
  obtain ⟨f, hf, hK⟩ := GlobalTheory.ZM.NearBuild.kTriv_near_good_prime o g _ J b Mat κ R β v A L act Q q₀ h.2 hL
  obtain ⟨act', Q', hL'⟩ := GlobalTheory.ZM.NearBuild.polFam_baseChange o g _ J b Mat κ R β v A L act Q _ (loc f) hL
  exact nearC_of_den_loc h2 h hf fun q₁ hq₁ =>
    GlobalTheory.ZM.NearBuild.nearC_of_polFam_of_kTriv h1 h2 g n j J hn hodd hj o b Mat κ _ _ _ _ _ act' Q' q₁ hq₁ (span_map _ hv) hL' hK

theorem nearC_of_smooth [Finite J]
    (hadd : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (q₀ : Ideal R), Den b Mat κ β v q₀ → Fam b Mat κ β v (n ^ 2) M th sc → Smooth Z.hom → ∃ f : R, f ∉ q₀ ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → ∃ mu : Z' ⊗ Z' ⟶ Z', AddOk b Mat κ β v (n ^ 2) M th sc ρ π mu)
    (hend : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (q₀ : Ideal R) (i : Option J), Den b Mat κ β v q₀ → Fam b Mat κ β v (n ^ 2) M th sc → Smooth Z.hom → ∃ f : R, f ∉ q₀ ∧ ∀ (R' : Type) [CommRing R'] (ρ : R →+* R'), IsUnit (ρ f) → ∀ (Z' : Over (Sp R')) (π : Z'.left ⟶ Z.left), IsPullback π Z'.hom Z.hom (spMap ρ) → ∃ F : Z' ⟶ Z', EndOk b Mat κ β v (n ^ 2) M th sc ρ π i F)
    {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
    {v : Ix g ((n ^ j) ^ 2) → R} {Z : Over (Sp R)} {M : LB Z.left} {th : Ix g ((n ^ j) ^ 2) → M.Sec}
    {sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)} {q₀ : Ideal R} (h : Den b Mat κ β v q₀)
    (hv : Ideal.span (Set.range v) = ⊤) (hZ : Fam b Mat κ β v (n ^ 2) M th sc)
    (hs : SmoothOfRelativeDimension g Z.hom) : NearC b Mat κ β v q₀ := by
  classical
  have := Fintype.ofFinite J
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  have hs' : Smooth Z.hom := SmoothOfRelativeDimension.smooth g _
  have hq := isPrime_of_mem h.2
  obtain ⟨f₁, hf₁, hmu⟩ := hadd R β v Z M th sc q₀ h hZ hs'
  choose f₂ hf₂ hF using fun i => hend R β v Z M th sc q₀ i h hZ hs'
  obtain ⟨f₃, hf₃, hc⟩ : ∃ f, f ∉ q₀ ∧ GeometricallyConnected (pullback.snd Z.hom (spMap (loc f))) := by
    obtain ⟨K, _, _, x, s, t, rfl, ht⟩ := mem_objPrimes.1 h.2
    obtain ⟨φ, hφ⟩ := hZ.2.2 K x s t ht
    obtain ⟨I, p, hI, -⟩ := hZ.1
    refine GlobalTheory.ConnSpread.exists_geometricallyConnected_away_of_fibre R _ Z.hom K x (GlobalTheory.ZM.projRep_projective_ample R _ I Z M th hI).1 hs' ?_
    have := t.ab.geomConnected
    refine MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso (fst := hφ.1.isoPullback.inv) (g := 𝟙 _) ⟨?_⟩) this
    rw [hφ.1.isoPullback_inv_snd, Category.comp_id]
  let f := f₁ * f₃ * ∏ i, f₂ i
  have hf : f ∉ q₀ := fun hh => by
    rcases hq.mem_or_mem hh with hh | hh
    · exact (hq.mem_or_mem hh).elim hf₁ hf₃
    · obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.1 hh
      exact hf₂ i hi
  let Z' : Over (Sp (Localization.Away f)) := Over.mk (pullback.snd Z.hom (spMap (loc f)))
  have hpb : IsPullback (pullback.fst Z.hom (spMap (loc f))) Z'.hom Z.hom (spMap (loc f)) :=
    IsPullback.of_hasPullback _ _
  obtain ⟨mu, hmu⟩ := hmu _ (loc f) (isUnit_loc ((dvd_mul_right f₁ f₃).mul_right _)) Z' _ hpb
  choose F hF using fun i => hF i _ (loc f)
    (isUnit_loc ((Finset.dvd_prod_of_mem f₂ (Finset.mem_univ i)).mul_left _)) Z' _ hpb
  obtain ⟨th', sc', hZ', hfib⟩ := GlobalTheory.ZM.NearBuild.fam_baseChange o g _ J b Mat κ R β v _ Z M th sc _ (loc f) Z' _ hpb hZ
  have hs₁ : SmoothOfRelativeDimension g Z'.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hpb hs
  have hc₁ : GeometricallyConnected Z'.hom := by
    have hu : IsUnit (loc f f₃) := isUnit_loc ((dvd_mul_left f₃ f₁).mul_right _)
    have e : spMap (loc f) = spMap (IsLocalization.Away.lift f₃ hu : Localization.Away f₃ →+* _) ≫ spMap (loc f₃) := by
      rw [← spMap_comp, IsLocalization.Away.lift_comp]
    have hpb' : IsPullback (pullback.fst Z.hom (spMap (loc f))) Z'.hom Z.hom
        (spMap (IsLocalization.Away.lift f₃ hu : Localization.Away f₃ →+* _) ≫ spMap (loc f₃)) := by
      rw [← e]; exact hpb
    have hp₃ := IsPullback.of_hasPullback Z.hom (spMap (loc f₃))
    have := IsPullback.of_right (h₁₁ := hp₃.lift _ _ (hpb'.w.trans (Category.assoc _ _ _).symm))
      (by rw [IsPullback.lift_fst]; exact hpb') (hp₃.lift_snd _ _ _) hp₃
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) this hc
  refine nearC_of_den_loc h2 h hf fun q₁ hq₁ => ?_
  obtain ⟨_, hG⟩ := GlobalTheory.ZM.NearBuild.grpFam_of_dense_fibres h1 h2 o g _ J b Mat κ _ _ _ _ Z' _ th' sc' mu F (pow_ne_zero _ hn.ne_zero) hq₁.1 hZ' hs₁ hc₁
    (fun K _ _ x s t φ ht hφ => hmu K x s t φ ((good_comp _ _ _).1 ht) (hfib K x s t φ hφ) hφ.1.w)
    (fun i K _ _ x s t φ ht hφ => hF i K x s t φ ((good_comp _ _ _).1 ht) (hfib K x s t φ hφ) hφ.1.w)
  exact nearC_of_grpFam h1 h2 hn hodd hj hq₁ (span_map _ hv) hG


omit h1 hodd hj in
theorem nearC_of_fam
    (H : ∀ {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
      {v : Ix g ((n ^ j) ^ 2) → R} {Z : Over (Sp R)} {M : LB Z.left} {th : Ix g ((n ^ j) ^ 2) → M.Sec}
      {sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)} {q₀ : Ideal R}, Den b Mat κ β v q₀ →
      Ideal.span (Set.range v) = ⊤ → Fam b Mat κ β v (n ^ 2) M th sc → SmoothOfRelativeDimension g Z.hom →
      NearC b Mat κ β v q₀)
    {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
    {v : Ix g ((n ^ j) ^ 2) → R} {Z : Over (Sp R)} {M : LB Z.left} {th : Ix g ((n ^ j) ^ 2) → M.Sec}
    {sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)} {q₀ : Ideal R} (h : Den b Mat κ β v q₀)
    (hv : Ideal.span (Set.range v) = ⊤) (hZ : Fam b Mat κ β v (n ^ 2) M th sc) : NearC b Mat κ β v q₀ := by
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  obtain ⟨f, hf, hs⟩ : ∃ f, f ∉ q₀ ∧ SmoothOfRelativeDimension g (pullback.snd Z.hom (spMap (loc f))) := by
    obtain ⟨K, _, _, x, s, t, rfl, ht⟩ := mem_objPrimes.1 h.2
    obtain ⟨φ, hφ⟩ := hZ.2.2 K x s t ht
    obtain ⟨I, p, hI, -⟩ := hZ.1
    refine GlobalTheory.ProperFlatNearFibre.exists_away_smoothOfRelativeDimension R _ Z.hom g K x (GlobalTheory.ZM.projRep_projective_ample R _ I Z M th hI).2.1 hZ.2.1 ?_
    refine (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_horiz_isIso (fst := hφ.1.isoPullback.inv) (g := 𝟙 _) ⟨?_⟩) t.dim
    rw [hφ.1.isoPullback_inv_snd, Category.comp_id]
  obtain ⟨th', sc', hZ', -⟩ := GlobalTheory.ZM.NearBuild.fam_baseChange o g _ J b Mat κ R β v _ Z M th sc _ (loc f)
    (Over.mk (pullback.snd Z.hom (spMap (loc f)))) _ (IsPullback.of_hasPullback _ _) hZ
  exact nearC_of_den_loc h2 h hf fun q₁ hq₁ => H hq₁ (span_map _ hv) hZ' hs


omit h1 hodd hj in
theorem nearC_of_unimodular
    (H : ∀ {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
      {v : Ix g ((n ^ j) ^ 2) → R} {Z : Over (Sp R)} {M : LB Z.left} {th : Ix g ((n ^ j) ^ 2) → M.Sec}
      {sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)} {q₀ : Ideal R}, Den b Mat κ β v q₀ →
      Ideal.span (Set.range v) = ⊤ → Fam b Mat κ β v (n ^ 2) M th sc → NearC b Mat κ β v q₀)
    {R : Type} [CommRing R] [IsNoetherianRing R] [IsReduced R] {β : o →+* R}
    {v : Ix g ((n ^ j) ^ 2) → R} {p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R} {Hh : Type} [Finite Hh]
    {hh : Hh → Ix g ((n ^ j) ^ 2)} {Q : Polynomial ℚ} {d : ℕ} {q₀ : Ideal R} (h : Den b Mat κ β v q₀)
    (hv : Ideal.span (Set.range v) = ⊤) (hp : ∀ c, Ideal.span (Set.range (p c)) = ⊤)
    (hD : FibData b Mat κ β v (n ^ 2) p hh Q d) : NearC b Mat κ β v q₀ := by
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  obtain ⟨f, hf, Z, M, th, hrep, hfl, hfib⟩ := GlobalTheory.ZM.NearCut.exists_away_flat_projRep R _ Hh (fun c => p (hh c)) Q d _ h.1 (fun q hq => by
    obtain ⟨K, _, _, x, s, t, rfl, ht⟩ := mem_objPrimes.1 hq
    obtain ⟨σ, I, -, -, -, hc, -⟩ := hD K x s t ht
    exact ⟨K, inferInstance, x, I, rfl, hc⟩) q₀ h.2
  refine nearC_of_den_loc h2 h hf fun q₁ hq₁ => ?_
  obtain ⟨sc, hZ⟩ := GlobalTheory.ZM.FamOf.exists_sections_fam o g _ J b Mat κ _ _ _ _ _ Hh hh Q d Z M th hq₁.1 (hD.comp (loc f))
    (fun c => span_map _ (hp c)) hrep hfl hfib
  exact H hq₁ (span_map _ hv) hZ
end

theorem exists_tObj_near : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), DenseP (objPrimes b Mat κ β v) → ∀ q₀ ∈ objPrimes b Mat κ β v, ∃ (f : R) (t : TObj g ((n ^ j) ^ 2) J b (spMap ((algebraMap R (Localization.Away f)).comp β))), f ∉ q₀ ∧ t.HasTh (𝟙 _) (fun a => (algebraMap R (Localization.Away f)) (v a)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : (Localization.Away f) →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap ((algebraMap R (Localization.Away f)).comp β))), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x ((algebraMap R (Localization.Away f)) (v a))) → TMap t' t (spMap x) := by
  classical
  intro h1 h2 g J _ Mat κ n hn hodd
  obtain ⟨j₁, H₁⟩ := GlobalTheory.T.exists_goodThetaObjectEmbeddingData h1 h2 g J Mat κ n hn hodd
  obtain ⟨j₂, H₂⟩ := GlobalTheory.T.exists_addition_morphism_thetaFamily_near_goodPrime h1 h2 g J Mat κ n hn hodd
  obtain ⟨j₃, H₃⟩ := GlobalTheory.T.exists_endomorphisms_extend_near_good_prime h1 h2 g J Mat κ n hn hodd
  refine ⟨j₁ + j₂ + j₃ + 2, fun j hj o _ b R _ _ _ β v hd q₀ hq₀ => ?_⟩
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ (pow_ne_zero _ hn.ne_zero)⟩
  suffices H : NearC b Mat κ β v q₀ by
    obtain ⟨f, hf, t, ht, H⟩ := H
    exact ⟨f, t, hf, ht, fun K _ _ x t' k₁ k₂ => H K x _ t' ⟨rfl, k₁, k₂⟩⟩
  obtain ⟨p, Hh, _, hh, Q, d, hD⟩ := H₁ j (by omega) o b R β v
  have hq := isPrime_of_mem hq₀
  obtain ⟨⟨a₀, ha₀⟩, hp⟩ : (∃ a, v a ∉ q₀) ∧ ∀ c, ∃ a, p c a ∉ q₀ := by
    obtain ⟨K, _, _, x, s, t, rfl, ht⟩ := mem_objPrimes.1 hq₀
    constructor
    · obtain ⟨c, hc⟩ := GlobalTheory.coset_of_hasTh h1 h2 o g _ J b _ s t n K _ _ ⊥ hn.two_le (dvd_pow_self n (by omega)) ht.2.2
        Ideal.isPrime_bot 0
      exact ⟨_, hc⟩
    · intro c
      obtain ⟨σ, I, -, hrep, -, -, hc⟩ := hD K x s t ht
      have := (hrep.2.1 K (RingHom.id K) _ _ (by
        rw [← Over.comp_left, lift_fst]
        exact (Spec.map_id _).symm) (hc c)).1
      by_contra hne
      push Not at hne
      refine (Ideal.isPrime_bot (α := K)).ne_top (eq_top_iff.2 (this ▸ Ideal.span_le.2 ?_))
      rintro _ ⟨a, rfl⟩
      exact hne a
  choose a ha using hp
  have hf : v a₀ * ∏ c, p c (a c) ∉ q₀ := fun hh => by
    rcases hq.mem_or_mem hh with hh | hh
    · exact ha₀ hh
    · obtain ⟨c, -, hc⟩ := Ideal.IsPrime.prod_mem_iff.1 hh
      exact ha c hc
  refine nearC_of_den_loc h2 ⟨hd, hq₀⟩ hf fun q₁ hq₁ => ?_
  refine nearC_of_unimodular h2 hn (nearC_of_fam h2 hn (nearC_of_smooth h1 h2 hn hodd (by omega)
    (H₂ j (by omega) o b) (H₃ j (by omega) o b))) hq₁
    (span_of_unit a₀ (isUnit_loc (dvd_mul_right _ _))) (fun c => span_of_unit (a c) (isUnit_loc
      ((Finset.dvd_prod_of_mem (fun c => p c (a c)) (Finset.mem_univ c)).mul_left _))) (hD.comp _)

end GlobalTheory.ZM.NearBuild
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaObjectNearGoodPrimeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaObject_near_good_prime : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), DenseP (objPrimes b Mat κ β v) → ∀ q₀ ∈ objPrimes b Mat κ β v, ∃ (f : R) (t : TObj g ((n ^ j) ^ 2) J b (spMap ((algebraMap R (Localization.Away f)).comp β))), f ∉ q₀ ∧ t.HasTh (𝟙 _) (fun a => (algebraMap R (Localization.Away f)) (v a)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : (Localization.Away f) →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap ((algebraMap R (Localization.Away f)).comp β))), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x ((algebraMap R (Localization.Away f)) (v a))) → TMap t' t (spMap x) := by
  first | exact @GlobalTheory.ZM.NearBuild.exists_tObj_near | exact GlobalTheory.ZM.NearBuild.exists_tObj_near | (intros; apply GlobalTheory.ZM.NearBuild.exists_tObj_near <;> assumption)
end
