module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaSchemeSectionsGoodFibres
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFamilyAdditionMorphismThetaLevel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsModelDominatingModelsOnOpenCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLevelCoverOfPowEqOne
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelEqOfPowEqOfHasTh

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarisedOfVeryDenseFibres
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarisedOfVeryDenseFibres
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.DensePol

theorem dense_of_veryDense {R : Type} [CommRing R] {P : Set (Ideal R)} (h : VeryDense P) :
    Dense {p : Sp R | PrimeSpectrum.asIdeal (R := R) p ∈ P} := by
  refine (PrimeSpectrum.isTopologicalBasis_basic_opens (R := R)).dense_iff.2 ?_
  rintro _ ⟨f, rfl⟩ ⟨q, hq⟩
  obtain ⟨p, hp, hp', -, hf⟩ := h q.asIdeal f q.isPrime hq
  exact ⟨⟨p, hp'⟩, hf, hp⟩

theorem mem_range_spMap {R K : Type} [CommRing R] [Field K] (x : R →+* K) (p : Sp R)
    (h : RingHom.ker x = PrimeSpectrum.asIdeal (R := R) p) : p ∈ Set.range (spMap x) := by
  refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum K), ?_⟩
  apply PrimeSpectrum.ext
  rw [← h]
  rfl

theorem basis_pow {G : Type} [CommGroup G] {r k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0) (y : Fin r → G)
    (hy : ∀ i, y i ^ (k * l) = 1)
    (h : ∀ z : G, z ^ (k * l) = 1 → ∃! c : Fin r → ZMod (k * l), ∏ i, y i ^ (c i).val = z)
    (z : G) (hz : z ^ k = 1) : ∃! c : Fin r → ZMod k, ∏ i, (y i ^ l) ^ (c i).val = z := by
  haveI : NeZero k := ⟨hk⟩
  have red : ∀ e : Fin r → ℕ, ∏ i, y i ^ ((e i : ZMod (k * l))).val = ∏ i, y i ^ e i := fun e =>
    Finset.prod_congr rfl fun i _ => by rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (hy i)]
  have tor : ∀ e : Fin r → ℕ, (∏ i, y i ^ e i) ^ (k * l) = 1 := fun e => by
    rw [← Finset.prod_pow]
    exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hy, one_pow]
  have inj : ∀ e e' : Fin r → ℕ, ∏ i, y i ^ e i = ∏ i, y i ^ e' i → ∀ i, e i ≡ e' i [MOD k * l] := by
    intro e e' he i
    have := (h _ (tor e)).unique (y₁ := fun i => (e i : ZMod (k * l))) (y₂ := fun i => (e' i : ZMod (k * l)))
      (red e) ((red e').trans he.symm)
    exact (ZMod.natCast_eq_natCast_iff _ _ _).1 (congrFun this i)
  obtain ⟨c, hc, -⟩ := h z (by rw [pow_mul, hz, one_pow])
  have hd : ∀ i, l ∣ (c i).val := fun i => by
    have := inj (fun i => k * (c i).val) (fun _ => 0) (by
      simp only [pow_zero, Finset.prod_const_one]
      rw [← hz, ← hc, ← Finset.prod_pow]
      exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, mul_comm]) i
    exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hk) ((Nat.modEq_zero_iff_dvd).1 this)
  choose d hd using hd
  refine ⟨fun i => (d i : ZMod k), ?_, fun c' hc' => funext fun i => ?_⟩
  · rw [← hc]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [ZMod.val_natCast, ← pow_eq_pow_mod _ (by rw [← pow_mul, mul_comm, hy]), hd, pow_mul]
  · have := inj (fun i => l * (c' i).val) (fun i => l * d i) (by
      simp only [pow_mul, ← hd]
      rw [hc, ← hc']) i
    rw [mul_comm k l] at this
    have h2 := Nat.ModEq.mul_left_cancel' hl this
    rw [← (ZMod.natCast_eq_natCast_iff _ _ _).2 h2, ZMod.natCast_zmod_val]

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
    change (pushHom hφ T (u ≫ a i)) ^ e i = pushHom hφ T ((u ≫ a i) ^ e i)
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

end GlobalTheory.DensePol

namespace GlobalTheory

open DensePol

theorem exists_polAV_of_veryDense_fibres :
    Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (I : Ideal (MvPolynomial (Ix g ((n ^ j) ^ 2)) R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R) (m : Z ⊗ Z ⟶ Z) (F : Option J → (Z ⟶ Z)), VeryDense (objPrimes b Mat κ β v) → (ProjRep I Z.hom M th ∧ SmoothOfRelativeDimension g Z.hom ∧ GeometricallyConnected Z.hom ∧ (∀ h, SecCoord M th (sc h).left (p h))) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ φ₂ : (t'.A ⊗ t'.A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[t'.A]).left ≫ φ) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), t'.Shape Mat κ → (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ i : Option J, φ ≫ (F i).left = (i.elim (𝟙 t'.A)⁻¹ t'.act : t'.A ⟶ t'.A).left ≫ φ) → ∃ (P : Out.PolAV (Sp R)) (act : J → (P.A ⟶ P.A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ P.A)), (P.g = g ∧ (∀ i, IsMonHom (act i)) ∧ (∀ i, Q i ^ (n ^ j) = 1) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ P.A), y ^ (n ^ j) = 1 → ∃! c : Ix g (n ^ j), Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R)) ≫ Q i) (fun i => (c i).val) = y)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ ψ : t'.A.left ⟶ P.A.left, (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left) := by
  intro hL hL2 g J _ Mat κ n hn hodd
  refine ⟨2, fun j hj o _ b R _ _ _ β v Z I M th sc p m F hVD ⟨hrep, hsm, hgc, _⟩ hfib hm hF => ?_⟩
  have hn0 : n ≠ 0 := hn.ne_zero
  have hN0 : n ^ j ≠ 0 := pow_ne_zero _ hn0
  haveI : NeZero ((n ^ j) ^ 2) := ⟨pow_ne_zero _ hN0⟩
  have hun : IsUnit (n : R) := by
    have := b.unit.map β
    rw [map_natCast, Nat.cast_pow, Nat.cast_pow, isUnit_pow_iff two_ne_zero, isUnit_pow_iff (by omega)] at this
    exact this
  obtain ⟨-, hpr, hamp⟩ := GlobalTheory.ZM.projRep_projective_ample R _ I Z M th hrep
  have hD := dense_of_veryDense hVD
  have hs : Smooth Z.hom := SmoothOfRelativeDimension.smooth g _
  have s1 : Smooth (Out.baseOver (Sp R)).hom := inferInstanceAs (Smooth (𝟙 _))
  have h0 : ∀ {K : Type} [Field K] {x : R →+* K} (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β))
      {φ : t'.A.left ⟶ Z.left}, (∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) →
      (1 : Out.baseOver _ ⟶ t'.A).left ≫ φ = spMap x ≫ (sc 0).left := fun t' φ h => by
    have := h 0
    rwa [lab_zero, one_pow] at this
  have h1 : ∀ {K : Type} [Field K] {x : R →+* K} (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β))
      {φ : t'.A.left ⟶ Z.left}, (∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) →
      ∀ i, (t'.pt i ^ n ^ j).left ≫ φ = spMap x ≫ (sc (Pi.single i 1)).left := fun t' φ h i => by
    have := h (Pi.single i 1)
    rwa [lab_single] at this
  obtain ⟨_, -, hη, -, hab, hgp⟩ := grpObj_of_dense_fibres R Z m (F none) (sc 0) _ hD hs hpr hgc (by
    rintro q ⟨K, _, _, x, t', hx, hsh, hth⟩
    obtain ⟨φ, hφ⟩ := hfib K x t' hsh hth
    refine ⟨K, inferInstance, spMap x, t'.A, inferInstance, φ, mem_range_spMap x q hx, t'.ab.comm, hφ.1,
      hm K x t' φ hφ, ?_, ?_⟩
    · have := hF K x t' φ hsh hφ none
      rwa [Option.elim, Hom.inv_def, Category.id_comp] at this
    · rw [← one_left, h0 t' hφ.2.2.2])
  have := hab.comm
  have hhom : ∀ i, IsMonHom (F (some i)) := fun i => hL.rigidity _ Z Z hab hab _ (by
    rw [hη]
    refine FibreGrp.hom_ext_of_fibres (X := Out.baseOver (Sp R)) hD ?_
    rintro q ⟨K, _, _, x, t', hx, hsh, hth⟩
    obtain ⟨φ, hφ⟩ := hfib K x t' hsh hth
    refine ⟨_, spMap x, mem_range_spMap x q hx, fun T t => ?_⟩
    rw [← Category.assoc, comp_eq_pushPt hφ.1.w (h0 t' hφ.2.2.2) (toUnit T) t]
    have := t'.hom i
    have e : (toUnit T ≫ (1 : Out.baseOver _ ⟶ t'.A)) ≫ t'.act i = toUnit T ≫ (1 : Out.baseOver _ ⟶ t'.A) := by
      rw [Category.assoc, MonObj.one_comp]
    apply Over.OverMorphism.ext
    change (_ ≫ φ) ≫ (F (some i)).left = _ ≫ φ
    rw [Category.assoc, hF K x t' φ hsh hφ (some i), ← Category.assoc, ← Over.comp_left]
    exact congrArg (fun z => z.left ≫ φ) e)
  have htor : ∀ {K : Type} [Field K] {x : R →+* K} (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (i),
      (t'.pt i ^ n ^ j) ^ n ^ j = 1 := fun t' i => by
    have e : n ^ j * n ^ j = (n ^ j) ^ 2 := (pow_two _).symm
    rw [← pow_mul (t'.pt i), e, t'.torsion]
  have hQ : ∀ i, sc (Pi.single i 1) ^ n ^ j = 1 := fun i => by
    refine FibreGrp.hom_ext_of_fibres (X := Out.baseOver (Sp R)) hD ?_
    rintro q ⟨K, _, _, x, t', hx, hsh, hth⟩
    obtain ⟨φ, hφ⟩ := hfib K x t' hsh hth
    refine ⟨_, spMap x, mem_range_spMap x q hx, fun T t => ?_⟩
    rw [MonObj.comp_pow, MonObj.comp_one, comp_eq_pushPt hφ.1.w (h1 t' hφ.2.2.2 i) (toUnit T) t]
    change pushHom (hgp _ _ _ φ hφ.1 (hm K x t' φ hφ)) T _ ^ _ = 1
    rw [← map_pow]
    erw [← MonObj.comp_pow]
    rw [htor]
    erw [MonObj.comp_one]
    rw [map_one]
  have hB := torsion_basis_of_dense (Sp R) Z (n ^ j) (2 * g) (fun i => sc (Pi.single i 1)) _ hab
    (Nat.pos_of_ne_zero hN0) (by
      have := (hun.pow j).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      simpa using this) hQ hD (by
      rintro q ⟨K, _, _, x, t', hx, hsh, hth⟩
      obtain ⟨φ, hφ⟩ := hfib K x t' hsh hth
      have := t'.ab.comm
      refine ⟨K, inferInstance, inferInstance, 𝟙 _ ≫ spMap x, by simpa using mem_range_spMap x q hx, ?_⟩
      exact basis_push (hgp _ _ _ φ hφ.1 (hm K x t' φ hφ)) (h1 t' hφ.2.2.2) (T := Over.mk (𝟙 _)) _ _
        (basis_pow_linComb (pow_two _) (NeZero.ne _) _ t'.pt t'.torsion (t'.bij K (𝟙 _))))
  have hj2 : n ^ j = n ^ 2 * n ^ (j - 2) := by rw [← pow_add]; congr 1; omega
  obtain ⟨L, l1, l2, l3, l4, l5, l6⟩ := GlobalTheory.T.exists_polarisation_descent_mul_odd_veryDense hL hL2 R Z g (n ^ 2) M _
    (fun i => (sc (Pi.single i 1) ^ n ^ (j - 2) : Out.baseOver (Sp R) ⟶ Z)) hab hsm hodd.pow
    (by simpa using hun.pow 2) hrep.1 hamp hVD
    (fun i => by
      have e : n ^ (j - 2) * n ^ 2 = n ^ j := by rw [mul_comm, ← hj2]
      have : (sc (Pi.single i 1) ^ n ^ (j - 2)) ^ n ^ 2 = 1 := by rw [← pow_mul, e, hQ]
      exact this)
    (fun K _ _ x => basis_pow_linComb hj2 hN0 _ _ hQ (hB K x))
    (by
      rintro q ⟨K, _, _, x, t', hx, hsh, hth⟩
      obtain ⟨φ, hφ⟩ := hfib K x t' hsh hth
      exact ⟨K, inferInstance, inferInstance, x, t'.pol, φ, hx, hgp _ _ _ φ hφ.1 (hm K x t' φ hφ), hφ.2.2.1⟩)
  refine ⟨{ A := Z, isAb := hab, g := g, smoothDim := hsm, L := L, isLB := l1, rigid := l2, sym := l3,
            ample := l4, ktriv := l5 }, fun i => F (some i), fun i => sc (Pi.single i 1),
    ⟨rfl, hhom, hQ, hB⟩, fun K _ _ x t' hsh hth => ?_⟩
  obtain ⟨φ, hφ⟩ := hfib K x t' hsh hth
  have hg := hgp _ _ _ φ hφ.1 (hm K x t' φ hφ)
  exact ⟨φ, hg, l6 K x t'.pol φ hg hφ.2.2.1, fun i => (hF K x t' φ hsh hφ (some i)).symm, h1 t' hφ.2.2.2⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarisedOfVeryDenseFibresStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principallyPolarised_of_veryDense_fibres : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (Z : Over (Sp R)) (I : Ideal (MvPolynomial (Ix g ((n ^ j) ^ 2)) R)) (M : LB Z.left) (th : Ix g ((n ^ j) ^ 2) → M.Sec) (sc : Ix g ((n ^ j) ^ 2) → (Out.baseOver (Sp R) ⟶ Z)) (p : Ix g ((n ^ j) ^ 2) → Ix g ((n ^ j) ^ 2) → R) (m : Z ⊗ Z ⟶ Z) (F : Option J → (Z ⟶ Z)), VeryDense (objPrimes b Mat κ β v) → (ProjRep I Z.hom M th ∧ SmoothOfRelativeDimension g Z.hom ∧ GeometricallyConnected Z.hom ∧ (∀ h, SecCoord M th (sc h).left (p h))) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ φ : t'.A.left ⟶ Z.left, (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ φ₂ : (t'.A ⊗ t'.A).left ⟶ (Z ⊗ Z).left, IsSquare φ φ₂ → φ₂ ≫ m.left = (μ[t'.A]).left ≫ φ) → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (φ : t'.A.left ⟶ Z.left), t'.Shape Mat κ → (IsPullback φ t'.A.hom Z.hom (spMap x) ∧ (∃ σ, t'.Emb (n ^ 2) (Over.mk (𝟙 _)) σ ∧ ∀ (T : Type) [CommRing T] (y : Sp T ⟶ (Over.mk (𝟙 (Sp K)) ⊗ t'.A).left) (w : Ix g ((n ^ j) ^ 2) → T), SecCoord _ σ y w ↔ SecCoord M th (y ≫ (snd (Over.mk (𝟙 (Sp K))) t'.A).left ≫ φ) w) ∧ LBIso (lbPow t'.L ((n ^ 2) ^ 2)) (M.pull φ) ∧ ∀ h, (t'.lab h ^ n ^ j).left ≫ φ = spMap x ≫ (sc h).left) → ∀ i : Option J, φ ≫ (F i).left = (i.elim (𝟙 t'.A)⁻¹ t'.act : t'.A ⟶ t'.A).left ≫ φ) → ∃ (P : Out.PolAV (Sp R)) (act : J → (P.A ⟶ P.A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ P.A)), (P.g = g ∧ (∀ i, IsMonHom (act i)) ∧ (∀ i, Q i ^ (n ^ j) = 1) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ P.A), y ^ (n ^ j) = 1 → ∃! c : Ix g (n ^ j), Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R)) ≫ Q i) (fun i => (c i).val) = y)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → ∃ ψ : t'.A.left ⟶ P.A.left, (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left) := by
  first | exact @GlobalTheory.exists_polAV_of_veryDense_fibres | exact GlobalTheory.exists_polAV_of_veryDense_fibres | (intros; apply GlobalTheory.exists_polAV_of_veryDense_fibres <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSquareLevelWithGivenThetaPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSquareLevelWithGivenThetaPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.LevelTheta

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem spMap_id {A : Type} [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := Spec.map_id _

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {ψ : Y ⟶ X} (φ : Z ⟶ Y) {χ : Z ⟶ X}
    (H : LBIso M (L.pull ψ)) (e : χ = φ ≫ ψ) : LBIso (M.pull φ) (L.pull χ) :=
  H.chartPull (Geo.Tor.chartPullPull M φ φ rfl)
    (chartPullSame L (fun _ : PUnit => χ) (fun _ : PUnit => ψ) (fun _ => 1) φ (fun _ => e))

theorem pow_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (x' : Out.baseOver S' ⟶ G') (x : Out.baseOver S ⟶ G)
    (e : x'.left ≫ φ = f ≫ x.left) (m : ℕ) : (x' ^ m).left ≫ φ = f ≫ (x ^ m).left := by
  let U : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S := Over.homMk f (by simp)
  have e₁ : pushHom h _ x' = preHom U x := Over.OverMorphism.ext e
  have e₂ : pushHom h _ (x' ^ m) = preHom U (x ^ m) := by rw [map_pow, map_pow, e₁]
  exact congrArg (fun z => z.left) e₂

variable {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k}

def Above {S S' : Scheme.{0}} (P : Out.PolAV S) (act : J → (P.A ⟶ P.A)) (Q : Fin (2 * g) → (Out.baseOver S ⟶ P.A))
    (m : ℕ) {s' : S' ⟶ Sp o} (t : TObj g k J b s') (f : S' ⟶ S) (ψ : t.A.left ⟶ P.A.left) : Prop :=
  IsGrpPullback t.A P.A f ψ ∧ LBIso t.L (P.L.pull ψ) ∧ (∀ i, (t.act i).left ≫ ψ = ψ ≫ (act i).left) ∧
    ∀ i, (t.pt i ^ m).left ≫ ψ = f ≫ (Q i).left

theorem Above.comp {S S' S'' : Scheme.{0}} {P : Out.PolAV S} {act : J → (P.A ⟶ P.A)}
    {Q : Fin (2 * g) → (Out.baseOver S ⟶ P.A)} {m : ℕ} {s' : S' ⟶ Sp o} {s'' : S'' ⟶ Sp o} {t : TObj g k J b s'}
    {u : TObj g k J b s''} {f : S' ⟶ S} {ψ : t.A.left ⟶ P.A.left} (h : Above P act Q m t f ψ) {f' : S'' ⟶ S'}
    {φ : u.A.left ⟶ t.A.left} (h₁ : IsGrpPullback u.A t.A f' φ) (h₂ : LBIso u.L (t.L.pull φ))
    (h₃ : ∀ i, (u.pt i).left ≫ φ = f' ≫ (t.pt i).left) (h₄ : ∀ j, (u.act j).left ≫ φ = φ ≫ (t.act j).left) :
    Above P act Q m u (f' ≫ f) (φ ≫ ψ) := by
  refine ⟨h₁.comp h.1, LBIso.trans u.isLB (pull_isLB t.isLB _) (pull_isLB P.isLB _) h₂
    (lbIso_pull_comp φ h.2.1 rfl), fun i => ?_, fun i => ?_⟩
  · rw [← Category.assoc, h₄, Category.assoc, h.2.2.1, Category.assoc]
  · rw [← Category.assoc, pow_push h₁ _ _ (h₃ i), Category.assoc, h.2.2.2, Category.assoc]

theorem Above.compare {S S' : Scheme.{0}} {P : Out.PolAV S} {act : J → (P.A ⟶ P.A)}
    {Q : Fin (2 * g) → (Out.baseOver S ⟶ P.A)} {m : ℕ} {s' : S' ⟶ Sp o} {u u' : TObj g k J b s'}
    {f : S' ⟶ S} {ψ : u.A.left ⟶ P.A.left} {ψ' : u'.A.left ⟶ P.A.left} (h : Above P act Q m u f ψ)
    (h' : Above P act Q m u' f ψ') :
    ∃ χ : u'.A.left ⟶ u.A.left, χ ≫ ψ = ψ' ∧ IsGrpPullback u'.A u.A (𝟙 _) χ ∧ LBIso u'.L (u.L.pull χ) ∧
      (∀ i, (u'.pt i ^ m).left ≫ χ = (u.pt i ^ m).left) ∧ ∀ j, (u'.act j).left ≫ χ = χ ≫ (u.act j).left := by
  have hp := h.1.1
  let χ : u'.A.left ⟶ u.A.left := hp.lift ψ' u'.A.hom h'.1.1.w
  have e₁ : χ ≫ ψ = ψ' := hp.lift_fst _ _ _
  have e₂ : χ ≫ u.A.hom = u'.A.hom := hp.lift_snd _ _ _
  refine ⟨χ, e₁, h.1.cancel (h'.1.congr (Category.id_comp _).symm e₁.symm) (by rw [e₂, Category.comp_id]),
    LBIso.trans u'.isLB (pull_isLB P.isLB _) (pull_isLB u.isLB _) h'.2.1
      (lbIso_pull_comp χ h.2.1 e₁.symm).symm, fun i => ?_, fun j => ?_⟩
  · apply hp.hom_ext
    · rw [Category.assoc, e₁, h'.2.2.2, h.2.2.2]
    · rw [Category.assoc, e₂, Over.w, Over.w]
  · apply hp.hom_ext
    · rw [Category.assoc, e₁, h'.2.2.1, Category.assoc, h.2.2.1, ← Category.assoc, e₁]
    · rw [Category.assoc, e₂, Over.w, Category.assoc, Over.w, e₂]

theorem exists_level_with_theta_point : Out.Laws → Out.Laws2 → ∀ (g n j : ℕ) (J : Type), n.Prime → Odd n → 2 ≤ j → ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (P : Out.PolAV (Sp R)) (act : J → (P.A ⟶ P.A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ P.A)), (P.g = g ∧ (∀ i, IsMonHom (act i)) ∧ (∀ i, Q i ^ (n ^ j) = 1) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ P.A), y ^ (n ^ j) = 1 → ∃! c : Ix g (n ^ j), Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R)) ≫ Q i) (fun i => (c i).val) = y)) → VeryDense {q | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (ψ : t'.A.left ⟶ P.A.left), RingHom.ker x = q ∧ t'.HasTh (𝟙 _) (fun a => x (v a)) ∧ (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left)} → ∃ t : TObj g ((n ^ j) ^ 2) J b (spMap β), t.HasTh (𝟙 _) v ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (ψ : t'.A.left ⟶ P.A.left), t'.HasTh (𝟙 _) (fun a => x (v a)) → (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left) → TMap t' t (spMap x) := by
  intro hL hL2 g n j J hn hodd hj o _ b R _ _ _ β v P act Q hP hdense
  have hn2 : 2 ≤ n := hn.two_le
  have hpos : 0 < n ^ j := pow_pos hn.pos j
  have hdvd : n ∣ n ^ j := dvd_pow_self n (by omega)
  have h3 : 3 ≤ n ^ j := by
    have h4 : 2 ^ 2 ≤ n ^ j := (Nat.pow_le_pow_left hn2 2).trans (Nat.pow_le_pow_right hn.pos hj)
    omega
  obtain ⟨R₁, _, _, t₁, ψ₁, hfin, het, hab, huniv⟩ := GlobalTheory.exists_finiteEtale_level_cover hL hL2 o g (n ^ j) J b R β P act Q hpos hP
  have hab' : Above P act Q (n ^ j) t₁ (spMap (algebraMap R R₁)) ψ₁ := hab
  have hspan : Ideal.span (Set.range v) = ⊤ := by
    by_contra hne
    obtain ⟨q, hq, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨p, ⟨K, _, _, x, t', ψ, hker, hth, -⟩, -, hqp, -⟩ :=
      hdense q 1 hq.isPrime (fun h => hq.ne_top ((Ideal.eq_top_iff_one _).2 h))
    obtain ⟨c, hc⟩ := GlobalTheory.coset_of_hasTh hL hL2 o g (n ^ j) J b _ _ t' n K (𝟙 _) _ ⊥ hn2 hdvd hth Ideal.isPrime_bot 0
    apply hc
    have : v (0 + (n ^ j / n) • c) ∈ RingHom.ker x := hker ▸ hqp (hle (Ideal.subset_span ⟨_, rfl⟩))
    exact this
  have hspan₁ : Ideal.span (Set.range fun a => algebraMap R R₁ (v a)) = ⊤ := by
    have := congrArg (Ideal.map (algebraMap R R₁)) hspan
    rwa [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at this
  obtain ⟨𝔞, h𝔞⟩ := GlobalTheory.ThetaClosed.exists_ideal_hasTh_iff hL hL2 o g (n ^ j) J b R₁ _ t₁ _ hodd.pow h3 hspan₁

  have hth : ∀ (R' : Type) [CommRing R'] (x : R →+* R') (y : R₁ →+* R') (s' : Sp R' ⟶ Sp o)
      (t' : TObj g ((n ^ j) ^ 2) J b s'), y.comp (algebraMap R R₁) = x → TMap t' t₁ (spMap y) →
      (t'.HasTh (𝟙 _) (fun a => x (v a)) ↔ ∀ r ∈ 𝔞, y r = 0) := by
    intro R' _ x y s' t' e hm
    subst e
    rw [GlobalTheory.hasTh_iff_of_tmap o g (n ^ j) J b _ _ t₁ _ _ t' _ R' _ _ hm, Category.id_comp]
    exact h𝔞 R' y

  have huniq : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (y y' : R₁ →+* K),
      y.comp (algebraMap R R₁) = x → y'.comp (algebraMap R R₁) = x → (∀ r ∈ 𝔞, y r = 0) → (∀ r ∈ 𝔞, y' r = 0) →
      y = y' := by
    intro K _ _ x y y' e e' k k'
    have d : spMap y ≫ spMap (algebraMap R R₁) = spMap x := by rw [spMap_comp, e]
    have d' : spMap y' ≫ spMap (algebraMap R R₁) = spMap x := by rw [spMap_comp, e']
    obtain ⟨u, hu⟩ := GlobalTheory.tObj_pull o g _ J b _ _ _ (spMap x ≫ spMap β) (spMap y) t₁ (by rw [← Category.assoc, d])
    obtain ⟨u', hu'⟩ := GlobalTheory.tObj_pull o g _ J b _ _ _ (spMap x ≫ spMap β) (spMap y') t₁ (by rw [← Category.assoc, d'])
    have T := (hth K x y _ u e hu).2 k
    have T' := (hth K x y' _ u' e' hu').2 k'
    obtain ⟨φ, a₁, a₂, a₃, a₄⟩ := id hu
    obtain ⟨φ', a₁', a₂', a₃', a₄'⟩ := id hu'
    have A := hab'.comp a₁ a₂ a₃ a₄
    have A' := hab'.comp a₁' a₂' a₃' a₄'
    rw [d] at A
    rw [d'] at A'
    obtain ⟨χ, c₀, c₁, c₂, c₃, c₄⟩ := A.compare A'
    have c₅ := GlobalTheory.level_eq_of_pow_eq_of_hasTh hL hL2 g n j J hn hodd hj o b K _ u u' χ _ c₁ c₂ c₃ T T'
    have hχ : TMap u' u (𝟙 _) := ⟨χ, c₁, c₂, fun i => by rw [c₅, Category.id_comp], c₄⟩
    have hm : TMap u' t₁ (spMap y) := by
      have := ((GlobalTheory.ZM.tmap_id_comp_cancel o g _ J b _ _ _ _ _ _ t₁ u u').2 _ _ hu).1 hχ
      rwa [Category.id_comp] at this
    refine (huniv K x u' (φ' ≫ ψ₁) A').unique ⟨e, fun i => ?_, hm⟩ ⟨e', fun i => ?_, hu'⟩
    · rw [← c₀, ← Category.assoc, c₅, ← Category.assoc, a₃, Category.assoc]
    · rw [← Category.assoc, a₃', Category.assoc]
  have hcomp : (Ideal.Quotient.mk 𝔞).comp (algebraMap R R₁) = algebraMap R (R₁ ⧸ 𝔞) := rfl
  have : Algebra.FormallyUnramified R (R₁ ⧸ 𝔞) :=
    Algebra.FormallyUnramified.of_surjective (Ideal.Quotient.mkₐ R 𝔞) Ideal.Quotient.mk_surjective
  have hbij : Function.Bijective (algebraMap R (R₁ ⧸ 𝔞)) := by
    refine GlobalTheory.algebraMap_bijective_of_unramified_of_unique_geometric_point R (R₁ ⧸ 𝔞) _ hdense ?_
    rintro q ⟨K, _, _, x, t', ψ, hker, T, A⟩
    obtain ⟨y, ⟨e, -, hm⟩, -⟩ := huniv K x t' ψ A
    have k := (hth K x y _ t' e hm).1 T
    refine ⟨K, inferInstance, inferInstance, x, hker, Ideal.Quotient.lift 𝔞 y k, ?_, fun z hz => ?_⟩
    · exact e
    · have := huniq K x (z.comp (Ideal.Quotient.mk 𝔞)) y hz e
        (fun r hr => by rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]) k
      exact Ideal.Quotient.ringHom_ext (this.trans (by ext r; rfl))
  let ε : R ≃+* R₁ ⧸ 𝔞 := RingEquiv.ofBijective _ hbij
  let ρ : R₁ →+* R := (ε.symm : R₁ ⧸ 𝔞 →+* R).comp (Ideal.Quotient.mk 𝔞)
  have hρ : ρ.comp (algebraMap R R₁) = RingHom.id R := RingHom.ext fun r => ε.symm_apply_apply r
  have hρ' : ∀ r, r - algebraMap R R₁ (ρ r) ∈ 𝔞 := fun r =>
    Ideal.Quotient.eq.1 (ε.apply_symm_apply (Ideal.Quotient.mk 𝔞 r)).symm
  obtain ⟨t, ht⟩ := GlobalTheory.tObj_pull o g _ J b _ _ _ (spMap β) (spMap ρ) t₁
    (by rw [← Category.assoc, spMap_comp, hρ, spMap_id, Category.id_comp])
  refine ⟨t, (hth R (RingHom.id R) ρ _ t hρ ht).2 fun r hr => ?_, fun K _ _ x t' ψ T A => ?_⟩
  · show ε.symm (Ideal.Quotient.mk 𝔞 r) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hr, map_zero]
  · obtain ⟨y, ⟨e, -, hm⟩, -⟩ := huniv K x t' ψ A
    have k := (hth K x y _ t' e hm).1 T
    have hy : x.comp ρ = y := RingHom.ext fun r => by
      have := k _ (hρ' r)
      rw [map_sub, sub_eq_zero] at this
      rw [this, ← e]; rfl
    refine ((GlobalTheory.ZM.tmap_id_comp_cancel o g _ J b _ _ _ _ _ _ t₁ t t').2 _ _ ht).2 ?_
    rwa [spMap_comp ρ x, hy]

end GlobalTheory.LevelTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSquareLevelWithGivenThetaPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_square_level_with_given_thetaPoint : Out.Laws → Out.Laws2 → ∀ (g n j : ℕ) (J : Type), n.Prime → Odd n → 2 ≤ j → ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R) (P : Out.PolAV (Sp R)) (act : J → (P.A ⟶ P.A)) (Q : Fin (2 * g) → (Out.baseOver (Sp R) ⟶ P.A)), (P.g = g ∧ (∀ i, IsMonHom (act i)) ∧ (∀ i, Q i ^ (n ^ j) = 1) ∧ (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp R) (y : Over.mk x ⟶ P.A), y ^ (n ^ j) = 1 → ∃! c : Ix g (n ^ j), Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver (Sp R)) ≫ Q i) (fun i => (c i).val) = y)) → VeryDense {q | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (ψ : t'.A.left ⟶ P.A.left), RingHom.ker x = q ∧ t'.HasTh (𝟙 _) (fun a => x (v a)) ∧ (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left)} → ∃ t : TObj g ((n ^ j) ^ 2) J b (spMap β), t.HasTh (𝟙 _) v ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)) (ψ : t'.A.left ⟶ P.A.left), t'.HasTh (𝟙 _) (fun a => x (v a)) → (IsGrpPullback t'.A P.A (spMap x) ψ ∧ LBIso t'.L (P.L.pull ψ) ∧ (∀ i, (t'.act i).left ≫ ψ = ψ ≫ (act i).left) ∧ ∀ i, (t'.pt i ^ (n ^ j)).left ≫ ψ = (spMap x) ≫ (Q i).left) → TMap t' t (spMap x) := by
  first | exact @GlobalTheory.LevelTheta.exists_level_with_theta_point | exact GlobalTheory.LevelTheta.exists_level_with_theta_point | (intros; apply GlobalTheory.LevelTheta.exists_level_with_theta_point <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyFromVeryDensePoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM

theorem exists_tObj_of_veryDense : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), VeryDense (objPrimes b Mat κ β v) → ∃ t : TObj g ((n ^ j) ^ 2) J b (spMap β), t.HasTh (𝟙 _) v ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → TMap t' t (spMap x) := by
  intro h1 h2 g J _ Mat κ n hn hodd
  obtain ⟨j1, H1⟩ := GlobalTheory.T.exists_theta_scheme_sections_good_fibres h1 h2 g J Mat κ n hn hodd
  obtain ⟨j2, H2⟩ := GlobalTheory.T.exists_family_addition_morphism_thetaLevel h1 h2 g J Mat κ n hn hodd
  obtain ⟨j3, H3⟩ := GlobalTheory.T.exists_inversion_endomorphisms_thetaLevelFamily h1 h2 g J Mat κ n hn hodd
  obtain ⟨j4, H4⟩ := GlobalTheory.T.exists_principallyPolarised_of_veryDense_fibres h1 h2 g J Mat κ n hn hodd
  refine ⟨j1 + j2 + j3 + j4 + 4, ?_⟩
  intro j hj o _ b R _ _ _ β v hv
  obtain ⟨Z, I, M, th, sc, p, hZ, hfib⟩ := H1 j (by omega) o b R β v hv
  obtain ⟨m, hm⟩ := H2 j (by omega) o b R β v Z I M th sc p hv hZ hfib
  obtain ⟨F, hF⟩ := H3 j (by omega) o b R β v Z I M th sc p hv hZ hfib
  obtain ⟨P, act, Q, hP, hgood⟩ := H4 j (by omega) o b R β v Z I M th sc p m F hv hZ hfib hm hF
  obtain ⟨t, ht, hlast⟩ := GlobalTheory.T.exists_square_level_with_given_thetaPoint h1 h2 g n j J hn hodd (by omega) o b R β v P act Q hP (by
    intro q f hq hf
    obtain ⟨p', ⟨K, iK, iK', x, t', hker, hsh, hth⟩, hp'⟩ := hv q f hq hf
    obtain ⟨ψ, hψ⟩ := hgood K x t' hsh hth
    exact ⟨p', ⟨K, iK, iK', x, t', ψ, hker, hth, hψ⟩, hp'⟩)
  refine ⟨t, ht, ?_⟩
  intro K _ _ x t' hsh hth
  obtain ⟨ψ, hψ⟩ := hgood K x t' hsh hth
  exact hlast K x t' ψ hth hψ

end GlobalTheory.ZM
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaFamilyFromVeryDensePointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_family_from_very_dense_points : Out.Laws → Out.Laws2 → ∀ (g : ℕ) (J : Type) [Finite J] (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ n : ℕ), n.Prime → Odd n → ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ (o : Type) [CommRing o] (b : TBase o ((n ^ j) ^ 2)) (R : Type) [CommRing R] [IsNoetherianRing R] [IsReduced R] (β : o →+* R) (v : Ix g ((n ^ j) ^ 2) → R), VeryDense (objPrimes b Mat κ β v) → ∃ t : TObj g ((n ^ j) ^ 2) J b (spMap β), t.HasTh (𝟙 _) v ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (x : R →+* K) (t' : TObj g ((n ^ j) ^ 2) J b (spMap x ≫ spMap β)), t'.Shape Mat κ → t'.HasTh (𝟙 _) (fun a => x (v a)) → TMap t' t (spMap x) := by
  first | exact @GlobalTheory.ZM.exists_tObj_of_veryDense | exact GlobalTheory.ZM.exists_tObj_of_veryDense | (intros; apply GlobalTheory.ZM.exists_tObj_of_veryDense <;> assumption)
end
