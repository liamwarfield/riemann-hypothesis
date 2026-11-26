module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.IntOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PHypEmb
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PFinCov
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PRingL
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PLowTL
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PPtVanT
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PTowerL
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PSlice
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.AllHolds
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PurTop
public import Development.EtaleCohomology.KummerTheory.GoalHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaVectorBundleAnySpace
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.N81
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomologyExcisionAxiomHolds
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.EtaleCohomologyIndEtaleBaseChange

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtMain
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PAffVan
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

private theorem sub_of_equiv {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B) (q : ℕ) (n i : ℤ)
    (h : Subsingleton (Ht q (sp A) n i)) : Subsingleton (Ht q (sp B) n i) := by
  have hid : spMap (e : A →+* B) ≫ spMap (e.symm : B →+* A) = 𝟙 (sp B) := by
    simp only [spMap, ← Functor.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (e : A →+* B).comp (e.symm : B →+* A) = RingHom.id B := by
      ext x
      simp
    rw [this]
    simp
  refine ⟨fun x y => ?_⟩
  have hx : x = pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n
      (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n x) := by
    rw [← pull_comp, hid, pull_id]
  have hy : y = pull (ZMod q) (spMap (e : A →+* B)) (tw q i) n
      (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n y) := by
    rw [← pull_comp, hid, pull_id]
  rw [hx, hy, Subsingleton.elim (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n x)
    (pull (ZMod q) (spMap (e.symm : B →+* A)) (tw q i) n y)]

theorem UpperTheory.Gal.KunnethLefschetz.affVan_holds :
    UpperTheory.Gal.KunnethLefschetz.AffVan := by
  intro hIn hPt k _ _ q _ hq d n i hn
  show Subsingleton (Ht q (sp (MvPolynomial (Fin d) k)) n i)
  induction d with
  | zero =>
    have h0 : Subsingleton (Ht q (sp k) n i) := hPt hIn k q n i hn
    exact sub_of_equiv (MvPolynomial.isEmptyRingEquiv k (Fin 0)).symm q n i h0
  | succ d ih =>
    have hq' : IsUnit ((q : ℕ) : MvPolynomial (Fin d) k) := by
      have := hq.map (MvPolynomial.C : k →+* MvPolynomial (Fin d) k)
      rwa [map_natCast] at this
    have hpoly : Subsingleton (Ht q (sp (Polynomial (MvPolynomial (Fin d) k))) n i) := by
      have hb := hIn.c4 q (MvPolynomial (Fin d) k) hq' i n
      refine ⟨fun x y => ?_⟩
      obtain ⟨a, rfl⟩ := hb.2 x
      obtain ⟨b, rfl⟩ := hb.2 y
      rw [Subsingleton.elim a b]
    exact sub_of_equiv (MvPolynomial.finSuccEquiv k d).toRingEquiv.symm q n i hpoly
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PQEasy
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

theorem qEasy_holds : QEasy := by
  unfold QEasy
  intro l _ k _ G
  haveI : Module.Flat ℤ_[l] ℚ_[l] := IsLocalization.flat ℚ_[l] (nonZeroDivisors ℤ_[l])
  refine ⟨?_, ?_, ?_⟩
  · intro d e Z X p ι h n m hn U hU a
    have h0 : (pullHl l (sch.map U.ι) m 0).comp (G.hl h hn) = 0 :=
      LinearMap.ext fun x => Subtype.ext (funext fun j =>
        (G.exact j h hn U hU _).mpr ⟨x.1 j, rfl⟩)
    have h1 : (pb l U.ι m).comp (G.q h hn) = 0 := by
      unfold Gys0.q pb pullHQ
      rw [← LinearMap.baseChange_comp, h0, LinearMap.baseChange_zero]
    exact LinearMap.congr_fun h1 a
  · intro d e Z X p ι h n m hn U hU hs
    have hinj : Function.Injective (G.hl h hn) := fun x y hxy =>
      Subtype.ext (funext fun j => G.inj j h hn U hU (hs j) (congrArg (fun z => z.1 j) hxy))
    unfold Gys0.q
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ hinj
  · intro d e' e Z' X' Z X p' ι' p ι h' h f u hf hp n m hn a
    have h0 : (pullHl l (sch.map f) m 0).comp (G.hl h hn) =
        (G.hl h' hn).comp (pullHl l (sch.map u) n 0) :=
      LinearMap.ext fun x => Subtype.ext (funext fun j => G.nat j h' h f u hf hp hn (x.1 j))
    have h1 : (pb l f m).comp (G.q h hn) = (G.q h' hn).comp (pb l u n) := by
      unfold Gys0.q pb pullHQ
      rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, h0]
    exact LinearMap.congr_fun h1 a

end UpperTheory.Gal.KunnethLefschetz
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.GysinTwistZeroExists
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace LateralTheory.EtaleTrace.LRingPf
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

section Tw
variable {k : Type} [Field k]

private theorem twMul_add (q : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) {i j w : ℤ} (hw : i + j = w)
    (v : Ht q (sch.obj (S k)) 0 i) (n : ℤ) (a b : Ht q (sch.obj X) n j) :
    twMul q p hw v n (a + b) = twMul q p hw v n a + twMul q p hw v n b := by
  simp only [twMul, map_add (f := _), cast_add]

private def twHom (q : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) {i j w : ℤ} (hw : i + j = w)
    (v : Ht q (sch.obj (S k)) 0 i) (n : ℤ) : Ht q (sch.obj X) n j →+ Ht q (sch.obj X) n w :=
  AddMonoidHom.mk' (twMul q p hw v n) (twMul_add q p hw v n)

private theorem twMul_pull (h6 : DivisorNaturality) (q : ℕ) [NeZero q] {Y X : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S k)
    {i j w : ℤ} (hw : i + j = w) (v : Ht q (sch.obj (S k)) 0 i) (n : ℤ) (a : Ht q (sch.obj X) n j) :
    pull _ (sch.map f) _ n (twMul q p hw v n a) = twMul q (f ≫ p) hw v n (pull _ (sch.map f) _ n a) := by
  simp only [twMul, pull_cast, (h6 q).1, Functor.map_comp, pull_comp]

private theorem twMul_red (h11 : A11) (Q q : ℕ) [NeZero Q] (hd : q ∣ Q) {X : Scheme.{0}} (p : X ⟶ S k)
    {i j w : ℤ} (hw : i + j = w) (v : Ht Q (sch.obj (S k)) 0 i) (n : ℤ) (a : Ht Q (sch.obj X) n j) :
    red Q q (sch.obj X) n w (twMul Q p hw v n a) =
      twMul q p hw (red Q q _ 0 i v) n (red Q q _ n j a) := by
  simp only [twMul, red_cast, ((h11 Q q hd (sch.obj X)).1), ← pull_red]

private theorem twMul_cup (h6 : DivisorRingCompatibility) (q : ℕ) [NeZero q] {Z : Scheme.{0}} (p : Z ⟶ S k) {n m r i : ℤ}
    (h1 : n + m = r) (hi : 0 + i = i) (v : Ht q (sch.obj (S k)) 0 i) (c : Ht q (sch.obj Z) n 0)
    (b : Ht q (sch.obj Z) m 0) :
    twMul q p (add_zero i) v r (Ht.cast h1 (add_zero 0) (cup q c b)) =
      Ht.cast h1 hi (cup q c (twMul q p (add_zero i) v m b)) := by
  have hc : ∀ {a b a' b' : ℤ} (h : a = a') (h' : b = b') (x : Ht q (sch.obj Z) a b),
      HEq (Ht.cast h h' x) x := by
    intro a b a' b' h h' x
    subst h
    subst h'
    rfl
  simp only [twMul, cup_cast_right]
  generalize (pull (ZMod q) (sch.map p) (tw q i) 0) v = v'
  apply eq_of_heq
  refine (hc _ _ _).trans ?_
  refine HEq.trans ?_ (hc _ _ _).symm
  refine (hc _ _ _).trans ?_
  refine HEq.trans ?_ (hc _ _ _).symm
  have hA := (h6 q (sch.obj Z)).2.1 v' c b
  have hC := (h6 q (sch.obj Z)).2.2 v' c
  have hA2 := (h6 q (sch.obj Z)).2.1 c v' b
  simp only [zero_mul, Int.negOnePow_zero, one_smul] at hC
  have e1 : HEq (cup q v' (cup q c b)) (cup q (cup q v' c) b) := by
    rw [hA]
    exact (hc _ _ _).symm
  have e2 : HEq (cup q (cup q v' c) b) (cup q (cup q c v') b) := by
    rw [hC, cup_cast_left]
    exact hc _ _ _
  have e3 : HEq (cup q (cup q c v') b) (cup q c (cup q v' b)) := by
    rw [hA2]
    exact hc _ _ _
  exact e1.trans (e2.trans e3)

private def gZ {l : ℕ} (GT : GysT k) (w : ∀ (i : ℤ) (j : ℕ), Ht (l ^ j) (sch.obj (S k)) 0 (-i)) (j : ℕ) {d e : ℕ}
    {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m : ℤ} (hn : n + 2 * d = m) :
    Ht (l ^ j) (sch.obj Z) n 0 →+ Ht (l ^ j) (sch.obj X) m 0 :=
  (GT.g (l ^ j) h hn (neg_add_cancel (d : ℤ))).comp (twHom (l ^ j) (ι ≫ p) (add_zero (-(d : ℤ))) (w d j) n)

private theorem gZ_apply {l : ℕ} (GT : GysT k) (w : ∀ (i : ℤ) (j : ℕ), Ht (l ^ j) (sch.obj (S k)) 0 (-i)) (j : ℕ)
    {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X} (h : IsPair d e p ι) {n m : ℤ} (hn : n + 2 * d = m)
    (a : Ht (l ^ j) (sch.obj Z) n 0) :
    gZ GT w j h hn a = GT.g (l ^ j) h hn (neg_add_cancel (d : ℤ))
      (twMul (l ^ j) (ι ≫ p) (add_zero (-(d : ℤ))) (w d j) n a) := rfl

private def mkGys0 (hIn : In) {l : ℕ} [Fact l.Prime] (GT : GysT k) (hu : ∀ j : ℕ, IsUnit (((l ^ j : ℕ)) : k))
    (w : ∀ (i : ℤ) (j : ℕ), Ht (l ^ j) (sch.obj (S k)) 0 (-i))
    (hw : ∀ (i : ℤ) (j : ℕ), red (l ^ (j + 1)) (l ^ j) _ 0 (-i) (w i (j + 1)) = w i j)
    (hb : ∀ (i : ℤ) (j : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (n : ℤ),
      Function.Bijective (twMul (l ^ j) p (add_zero (-i)) (w i j) n)) : Gys0 k l where
  g j _ _ _ _ _ _ h _ _ hn := gZ GT w j h hn
  exact := by
    intro j d e Z X p ι h n m hn U hU y
    have E := GT.exact (l ^ j) (hu j) h hn (neg_add_cancel (d : ℤ)) U hU
    rw [E y]
    constructor
    · rintro ⟨a, rfl⟩
      obtain ⟨b, rfl⟩ := (hb d j (ι ≫ p) n).2 a
      exact ⟨b, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨_, rfl⟩
  inj := by
    intro j d e Z X p ι h n m hn U hU hs
    exact (GT.inj (l ^ j) (hu j) h hn (neg_add_cancel (d : ℤ)) U hU hs).comp (hb d j (ι ≫ p) n).1
  nat := by
    intro j d e' e Z' X' Z X p' ι' p ι h' h f t hfp hpb n m hn a
    have hc : t ≫ ι ≫ p = ι' ≫ p' := by
      rw [← Category.assoc, ← hpb.w, Category.assoc, hfp]
    rw [gZ_apply, gZ_apply, GT.nat (l ^ j) (hu j) h' h f t hpb hn _ _, twMul_pull hIn.a6nat _ t (ι ≫ p), hc]
  proj := by
    intro j d e Z X p ι h n m r s t h1 h2 h3 h4 a b
    rw [gZ_apply, gZ_apply]
    unfold cup0
    rw [twMul_cup hIn.a6ring _ _ h1 (zero_add _)]
    exact GT.proj (l ^ j) (hu j) h h1 h2 h3 h4 (zero_add _) (neg_add_cancel _) (neg_add_cancel _) (add_zero 0) a _
  red := by
    intro j d e Z X p ι h n m hn a
    rw [gZ_apply, gZ_apply, GT.red (l ^ (j + 1)) (l ^ j) (hu _) (dvd_succ l j) h hn _ _,
      twMul_red hIn.a11 _ _ (dvd_succ l j), hw]

end Tw

theorem gysinTwistZero_exists : GysinCondition := by
  intro hI hB l _ k _ _ hl hT hG
  obtain ⟨GT⟩ := hG
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  choose u v huv using hT
  have hu : ∀ j : ℕ, IsUnit (((l ^ j : ℕ)) : k) := by
    intro j
    rw [Nat.cast_pow]
    exact (isUnit_iff_ne_zero.mpr hl).pow j
  refine ⟨mkGys0 hI GT hu (fun i j => (v i).1 j) (fun i j => (v i).2 j) ?_⟩
  intro i j X p n
  exact (hB hI k (l ^ j) (hu j) i ((u i).1 j) ((v i).1 j) (huv i j) p n 0 (-i)).1 (add_zero (-i))

end UpperTheory.Gal.KunnethLefschetz
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.KunLHolds
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

private lemma kun_lof {k : Type} [Field k] (l : ℕ) [Fact l.Prime] {X : Scheme.{0}} (p : X ⟶ S k)
    (n a : ℤ) (h : a + (n - a) = n) (u : V l X a) (v : V l X (n - a)) :
    kun l p p n (DirectSum.lof ℚ_[l] ℤ (fun i => V l X i ⊗[ℚ_[l]] V l X (n - i)) a (u ⊗ₜ v)) =
      ext2 l p h u v := by
  simp [kun, DirectSum.toModule_lof, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]

theorem UpperTheory.Gal.KunnethLefschetz.kunL_holds :
    UpperTheory.Gal.KunnethLefschetz.KunL := by
  intro l _ k _ d X p hb
  refine ⟨fun n => ?_, fun lam m n h => ?_⟩
  · rw [eq_top_iff]
    rintro w -
    obtain ⟨x, rfl⟩ := (hb n).2 w
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i t =>
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul u v =>
        rw [← DirectSum.lof_eq_of ℚ_[l], kun_lof l p n i (by omega) u v]
        exact Submodule.subset_span ⟨i, n - i, by omega, u, v, rfl⟩
      | add s t hs ht =>
        rw [map_add (f := _), map_add (f := _)]
        exact Submodule.add_mem _ hs ht
    | add x y hx hy =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
  · let e := LinearEquiv.ofBijective (kun l p p n) (hb n)
    have he : ∀ a (ha : a + (n - a) = n) (u : V l X a) (v : V l X (n - a)),
        e.symm (ext2 l p ha u v) = DirectSum.lof ℚ_[l] ℤ (fun i => V l X i ⊗[ℚ_[l]] V l X (n - i)) a (u ⊗ₜ v) := by
      intro a ha u v
      rw [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply, kun_lof]
    refine ⟨(DirectSum.toModule ℚ_[l] ℤ (V l X m) (fun i =>
        if hi : i = 2 * (d : ℤ) then
          TensorProduct.lift ((LinearMap.lsmul ℚ_[l] (V l X m)).compl₁₂
            (Eq.rec (motive := fun j _ => V l X j →ₗ[ℚ_[l]] ℚ_[l]) lam hi.symm)
            (Eq.rec (motive := fun j _ => V l X j →ₗ[ℚ_[l]] V l X m) LinearMap.id
              (show m = n - i by omega)))
        else 0)) ∘ₗ e.symm.toLinearMap, ?_, ?_⟩
    · intro u v
      obtain rfl : m = n - 2 * (d : ℤ) := by omega
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, he,
        DirectSum.toModule_lof, dif_pos rfl]
      simp [TensorProduct.lift.tmul, LinearMap.compl₁₂_apply, LinearMap.lsmul_apply]
    · intro a b h' hbm u v
      obtain rfl : b = n - a := by omega
      have ha : a ≠ 2 * (d : ℤ) := by omega
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, he,
        DirectSum.toModule_lof, dif_neg ha, LinearMap.zero_apply]
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PQOnto
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

private theorem tors_of {l : ℕ} [Fact l.Prime] {M : Type*} [AddCommGroup M] [Module ℤ_[l] M] (b : ℤ_[l]) (hb : b ≠ 0)
    (w : M) (h : ((b : ℚ_[l]))⁻¹ ⊗ₜ[ℤ_[l]] w = 0) : ∃ c : ℤ_[l], c ≠ 0 ∧ c • w = 0 := by
  have hb' : (b : ℚ_[l]) ≠ 0 := by rwa [Ne, PadicInt.coe_eq_zero]
  have h1 : (1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] w = 0 := by
    have h2 := congrArg (fun t => (b : ℚ_[l]) • t) h
    simpa [TensorProduct.smul_tmul', hb'] using h2
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] M 1) := inferInstance
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ_[l]) (TensorProduct.mk ℤ_[l] ℚ_[l] M 1)).1 h1
  exact ⟨c, nonZeroDivisors.ne_zero c.2, hc⟩

theorem UpperTheory.Gal.KunnethLefschetz.qOnto_holds :
    UpperTheory.Gal.KunnethLefschetz.QOnto := by
  unfold QOnto
  intro hI hLim l _ k _ _ hl G d e Z X p ι h n m hn U hU hprop z hz
  obtain ⟨b, x, hb, rfl⟩ := H0LimitCoherence.tensor_form l z
  have hz' : ((b : ℚ_[l]))⁻¹ ⊗ₜ[ℤ_[l]] (pullHl l (sch.map U.ι) m 0 x) = 0 := by
    simpa [pb, pullHQ, LinearMap.baseChange_tmul] using hz
  obtain ⟨c, hc, hcx⟩ := tors_of b hb _ hz'
  have hunit : ∀ j : ℕ, IsUnit (((l ^ j : ℕ)) : k) := fun j => by
    push_cast
    exact (IsUnit.mk0 _ hl).pow j
  have hne : ∀ j : ℕ, NeZero (l ^ j) := fun j => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hfin : ∀ j : ℕ, Finite (Ht (l ^ j) (sch.obj Z) n 0) := fun j => by
    haveI := hne j
    haveI := hprop
    exact hI.e4 (l ^ j) k (hunit j) (ι ≫ p) n 0
  set x' : Hl l (sch.obj X) m 0 := c • x with hx'
  have hpull : pullHl l (sch.map U.ι) m 0 x' = 0 := by
    rw [hx', map_smul]; exact hcx
  have hlev : ∀ j, ∃ a, G.g j h hn a = x'.1 j := fun j => by
    have h0 : pull _ (sch.map U.ι) (tw (l ^ j) 0) m (x'.1 j) = 0 := by
      have := congrArg (fun t : Hl l (sch.obj U) m 0 => t.1 j) hpull
      exact this
    exact (G.exact j h hn U hU _).1 h0
  obtain ⟨a, ha, hfa⟩ := hLim (fun j => Ht (l ^ j) (sch.obj Z) n 0) (fun j => Ht (l ^ j) (sch.obj X) m 0)
    (fun j => red (l ^ (j + 1)) (l ^ j) _ n 0) (fun j => red (l ^ (j + 1)) (l ^ j) _ m 0)
    (fun j => G.g j h hn) (fun j a => G.red j h hn a) (fun j => x'.1 j) (fun j => x'.2 j) hlev
  let a' : Hl l (sch.obj Z) n 0 := ⟨a, ha⟩
  have hga : G.hl h hn a' = x' := Subtype.ext (funext hfa)
  refine ⟨(((b * c : ℤ_[l]) : ℚ_[l]))⁻¹ ⊗ₜ a', ?_⟩
  have hc' : (c : ℚ_[l]) ≠ 0 := by rwa [Ne, PadicInt.coe_eq_zero]
  have hb' : (b : ℚ_[l]) ≠ 0 := by rwa [Ne, PadicInt.coe_eq_zero]
  change (G.hl h hn).baseChange ℚ_[l] _ = _
  rw [LinearMap.baseChange_tmul, hga, hx', ← TensorProduct.smul_tmul, Algebra.smul_def]
  congr 1
  have hal : algebraMap ℤ_[l] ℚ_[l] c = (c : ℚ_[l]) := rfl
  rw [hal, PadicInt.coe_mul]
  field_simp
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PQProj
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz

theorem qProj_holds : QProj := by
  unfold QProj
  intro hI l _ k _ G d e Z X p ι h n m r s t h1 h2 h3 h4 a b
  have key : ∀ (x : Hl l (sch.obj X) n 0) (y : Hl l (sch.obj Z) m 0),
      G.q h h2 (cupV l Z h1 (pb l ι n ((1 : ℚ_[l]) ⊗ₜ x)) ((1 : ℚ_[l]) ⊗ₜ y)) =
        cupV l X h4 ((1 : ℚ_[l]) ⊗ₜ x) (G.q h h3 ((1 : ℚ_[l]) ⊗ₜ y)) := by
    intro x y
    rw [LRingPf.pb_tmul, LRingPf.cupV_eq l hI.a11 Z, LRingPf.cupV_eq l hI.a11 X, LRingPf.cupQ_tmul]
    simp only [Gys0.q, LinearMap.baseChange_tmul]
    rw [LRingPf.cupQ_tmul]
    congr 1
    refine Subtype.ext (funext fun j => ?_)
    exact G.proj j h h1 h2 h3 h4 (x.1 j) (y.1 j)
  have hfg : ((cupV l Z h1 ∘ₗ pb l ι n).compr₂ (G.q h h2)) = (cupV l X h4).compl₂ (G.q h h3) :=
    LRingPf.ext2 fun x y => key x y
  exact DFunLike.congr_fun (DFunLike.congr_fun hfg a) b

end UpperTheory.Gal.KunnethLefschetz
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.InjLHolds
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace

namespace UpperTheory.Gal.KunnethLefschetz

private theorem rank_pos {K : Type} [Field K] {Z' : Scheme.{0}} (p' : Z' ⟶ TranscendenceTraces.gp K) [IsFinite p'] [Surjective p'] :
    1 ≤ p'.finrank (IsLocalRing.closedPoint K) := by
  have hF : Flat p' := inferInstance
  obtain ⟨x, hx⟩ := p'.surjective (IsLocalRing.closedPoint K)
  have h := p'.one_le_finrank_map x
  rwa [hx] at h

theorem injL_holds : InjL := by
  intro hT l _ X Y π hfin hsurj hint hloc hl n
  obtain ⟨hW, -, hD, hTr⟩ := hT
  haveI := hfin
  haveI := hsurj
  haveI := hint
  have hw : TranscendenceTraces.IsNwt π (TranscendenceTraces.nwt π) := hW π hloc
  let g : TranscendenceTraces.gp (Y.residueField (genericPoint Y)) ⟶ Y :=
    Y.fromSpecResidueField (genericPoint Y)
  have hpt : TranscendenceTraces.pt g = genericPoint Y :=
    Scheme.fromSpecResidueField_apply _ _
  have hpush := hD (Y.residueField (genericPoint Y)) (pullback.fst π g) (pullback.snd π g) π g
    (IsPullback.of_hasPullback π g) hloc hpt
  have hd := rank_pos (pullback.snd π g)
  have htr := hTr l n 0 π (TranscendenceTraces.nwt π) _ hw.1 hl hpush
  intro a b hab
  have key : ∀ c, ((Scheme.Hom.finrank (pullback.snd π g)
      (IsLocalRing.closedPoint (Y.residueField (genericPoint Y))) : ℤ) : ℚ_[l]) • c =
      TranscendenceTraces.trHQ l π (TranscendenceTraces.nwt π) n 0 (pb l π n c) := by
    intro c
    have := LinearMap.congr_fun htr c
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at this
    rw [this, Int.cast_smul_eq_zsmul]
  have hne : ((Scheme.Hom.finrank (pullback.snd π g)
      (IsLocalRing.closedPoint (Y.residueField (genericPoint Y))) : ℤ) : ℚ_[l]) ≠ 0 := by
    norm_cast
    omega
  set_option synthInstance.maxHeartbeats 200000 in
    apply smul_right_injective _ hne
  simp only [key, hab]

end UpperTheory.Gal.KunnethLefschetz
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PComps
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace

namespace UpperTheory.Gal.KunnethLefschetz

theorem comps_holds : Comps := by
  classical
  unfold Comps
  intro k _ _ d X p hp hX
  obtain ⟨hfin, hopen⟩ := comp_fin d p hp
  let m := Nat.card (_root_.ConnectedComponents X)
  let e : Fin m ≃ _root_.ConnectedComponents X := (Finite.equivFin _).symm
  let rep : Fin m → X := fun j => (ConnectedComponents.surjective_coe (e j)).choose
  have hrep : ∀ j, (rep j : _root_.ConnectedComponents X) = e j := fun j =>
    (ConnectedComponents.surjective_coe (e j)).choose_spec
  let U : Fin m → X.Opens := fun j => ⟨connectedComponent (rep j), hopen _⟩
  have hUc : ∀ j, IsClosed (U j : Set X) := fun j => isClosed_connectedComponent
  have hmem : ∀ j (x : X), x ∈ (U j : Set X) ↔ e j = (x : _root_.ConnectedComponents X) := by
    intro j x
    rw [← hrep]
    exact ⟨fun h => ConnectedComponents.coe_eq_coe.mpr (connectedComponent_eq h),
      fun h => by
        have := ConnectedComponents.coe_eq_coe.mp h
        show x ∈ connectedComponent (rep j)
        rw [this]; exact mem_connectedComponent⟩
  refine ⟨m, U, fun j => ?_, fun x => ?_, fun j j' hj => ?_⟩
  · have h2 := clopen_smoothProper_projective d p hp hX (U j) (hUc j)
    have hc : ConnectedSpace (U j) := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
    exact ⟨h2.1, h2.2, LCompInt_of k d ((U j).ι ≫ p) h2.1 hc⟩
  · refine ⟨e.symm (x : _root_.ConnectedComponents X), ?_⟩
    show x ∈ (U _ : Set X)
    rw [hmem]
    exact e.apply_symm_apply _
  · rw [disjoint_iff_inf_le]
    intro x hx
    exact (hj (e.injective (((hmem j x).mp hx.1).trans ((hmem j' x).mp hx.2).symm))).elim

end UpperTheory.Gal.KunnethLefschetz
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PFinFib
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.finFib_holds :
    UpperTheory.Gal.KunnethLefschetz.FinFib := by
  intro k _ _ X Y p r π hπ hfin t U hU
  classical
  obtain ⟨t0, ht0⟩ := t
  change ↑U = (Set.range t0)ᶜ at hU
  have hA : IsLocallyArtinian (pullback π t0) :=
    IsLocallyArtinian.of_locallyQuasiFinite (pullback.snd π t0)
  have hD : DiscreteTopology ↥(pullback π t0) := inferInstance
  have hF : Finite ↥(pullback π t0) := by
    have h := (pullback.snd π t0).finite_preimage_singleton (IsLocalRing.closedPoint k)
    rw [← Set.finite_univ_iff]
    refine h.subset fun z _ => ?_
    exact Subsingleton.elim _ _
  haveI : Fintype ↥(pullback π t0) := Fintype.ofFinite _
  let c : ↥(S k) := IsLocalRing.closedPoint k
  let e : ↥(pullback π t0) → (S k ⟶ pullback π t0) := fun z =>
    pointOfClosedPoint (pullback.snd π t0) z (isClosed_discrete _)
  have he : ∀ z, e z ≫ pullback.snd π t0 = 𝟙 _ := fun z => pointOfClosedPoint_comp _ _ _
  have he' : ∀ z, e z c = z := fun z => pointOfClosedPoint_apply _ _ _ _
  let g : ↥(pullback π t0) → Pt p := fun z =>
    ⟨e z ≫ pullback.fst π t0, by
      rw [Category.assoc, ← hπ, ← Category.assoc (pullback.fst π t0), pullback.condition,
        Category.assoc, ht0, Category.comp_id, he]⟩
  refine ⟨Finset.univ.image g, ?_⟩
  unfold OffPts
  rw [Scheme.Hom.coe_preimage, hU, Set.preimage_compl]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_range, Finset.mem_image, Finset.mem_univ, true_and,
    Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback x a ha.symm
    refine ⟨g z, ⟨z, rfl⟩, c, ?_⟩
    change (e z ≫ pullback.fst π t0) c = x
    rw [Scheme.Hom.comp_apply, he', hz1]
  · rintro ⟨y, ⟨z, rfl⟩, b, rfl⟩
    refine ⟨(e z ≫ pullback.snd π t0) b, ?_⟩
    change (e z ≫ pullback.snd π t0 ≫ t0) b = (e z ≫ pullback.fst π t0 ≫ π) b
    rw [pullback.condition]
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PBasisOne
noncomputable section

namespace UpperTheory.Gal.KunnethLefschetz

theorem basisOne_holds : BasisOne := by
  intro F M _ _ _ _ lam hlam
  by_cases h0 : lam = 0
  · haveI := hlam h0
    exact ⟨0, Module.Basis.empty M, fun t => t.elim0⟩
  obtain ⟨x, hx⟩ : ∃ x, lam x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (LinearMap.ext hc)
  set v : M := (lam x)⁻¹ • x with hvdef
  have hv : lam v = 1 := by
    rw [hvdef, map_smul, smul_eq_mul, inv_mul_cancel₀ hx]
  set N := LinearMap.ker lam
  let e := Module.finBasis F N
  let f : Fin (Module.finrank F N + 1) → M := Fin.cons v (fun i => v + (e i : M))
  have hrange : LinearMap.range lam = ⊤ := by
    rw [eq_top_iff]
    intro c _
    exact ⟨c • v, by rw [map_smul, hv, smul_eq_mul, mul_one]⟩
  have hcard : Fintype.card (Fin (Module.finrank F N + 1)) = Module.finrank F M := by
    rw [Fintype.card_fin, ← LinearMap.finrank_range_add_finrank_ker lam, hrange, finrank_top,
      Module.finrank_self, add_comm]
  have hvmem : v ∈ Submodule.span F (Set.range f) :=
    Submodule.subset_span ⟨0, by simp [f]⟩
  have hemem : ∀ i, (e i : M) ∈ Submodule.span F (Set.range f) := by
    intro i
    have h1 : v + (e i : M) ∈ Submodule.span F (Set.range f) :=
      Submodule.subset_span ⟨i.succ, by simp [f]⟩
    have := Submodule.sub_mem _ h1 hvmem
    simpa using this
  have hNmem : ∀ y : N, (y : M) ∈ Submodule.span F (Set.range f) := by
    intro y
    rw [← e.sum_repr y]
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hemem i))
  have hspan : ⊤ ≤ Submodule.span F (Set.range f) := by
    intro z _
    have hz : z - lam z • v ∈ N := by
      rw [LinearMap.mem_ker, map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]
    have h2 := hNmem ⟨_, hz⟩
    have h3 := Submodule.add_mem _ h2 (Submodule.smul_mem _ (lam z) hvmem)
    simpa using h3
  refine ⟨_, basisOfTopLeSpanOfCardEqFinrank f hspan hcard, fun t => ?_⟩
  rw [coe_basisOfTopLeSpanOfCardEqFinrank]
  refine Fin.cases ?_ (fun i => ?_) t
  · simpa [f] using hv
  · have hk : lam (e i : M) = 0 := (e i).2
    simp [f, hv, hk]

end UpperTheory.Gal.KunnethLefschetz
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PPairs
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.pairs_holds :
    UpperTheory.Gal.KunnethLefschetz.Pairs := by
  unfold Pairs
  intro k _ d X p hsep hsm
  have hfst : SmoothOfRelativeDimension d (pullback.fst p p) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := d)).of_isPullback
      (IsPullback.of_hasPullback p p).flip hsm
  have hcomp : SmoothOfRelativeDimension (d + d) (pullback.fst p p ≫ p) :=
    smoothOfRelativeDimension_comp (n := d) (m := d) (pullback.fst p p) p
  have hid : SmoothOfRelativeDimension 0 (𝟙 (S k)) := inferInstance
  refine ⟨⟨inferInstance, hcomp, ?_⟩, fun y => ⟨⟨?_, ?_, ?_⟩, ?_⟩⟩
  · rw [pullback.diagonal_fst_assoc]
    exact hsm
  · have h1 : IsClosedImmersion (y.1 ≫ p) := by rw [y.2]; infer_instance
    exact IsClosedImmersion.of_comp y.1 p
  · rw [Nat.zero_add]; exact hsm
  · rw [y.2]; exact hid
  · have key : ∀ s : PullbackCone (slice y) (pullback.diagonal p),
        s.fst = s.snd ∧ s.fst ≫ p ≫ y.1 = s.snd := by
      intro s
      have c := s.condition
      have c1 := congrArg (· ≫ pullback.fst p p) c
      have c2 := congrArg (· ≫ pullback.snd p p) c
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
        pullback.diagonal_snd, Category.comp_id] at c1 c2
      exact ⟨c1, c2⟩
    refine IsPullback.of_isLimit' ⟨?_⟩ (PullbackCone.IsLimit.mk _ (fun s => s.fst ≫ p) ?_ ?_ ?_)
    · have e1 : slice y ≫ pullback.fst p p = 𝟙 X := pullback.lift_fst _ _ _
      have e2 : slice y ≫ pullback.snd p p = p ≫ y.1 := pullback.lift_snd _ _ _
      have hy : y.1 ≫ p ≫ y.1 = y.1 := by rw [← Category.assoc, y.2, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, e1, Category.assoc, pullback.diagonal_fst, Category.comp_id]
      · rw [Category.assoc, e2, hy, Category.assoc, pullback.diagonal_snd, Category.comp_id]
    · intro s
      rw [Category.assoc, (key s).2, (key s).1]
    · intro s
      rw [Category.assoc, (key s).2]
    · intro s m h1 _
      rw [← h1, Category.assoc, y.2, Category.comp_id]
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PLimOnto
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.limOnto_holds :
    UpperTheory.Gal.KunnethLefschetz.LimOnto := by
  intro A B _ ra rb f hf z hz hsurj
  let F : ℕ → Type 1 := fun j => {a : A j // f j a = z j}
  let g : ∀ n, F (n + 1) → F n := fun n a =>
    ⟨ra n a.1, by rw [← hf, a.2, hz]⟩
  let G : ℕᵒᵖ ⥤ Type 1 := Functor.ofOpSequence (X := F) (fun n => TypeCat.ofHom (g n))
  haveI : ∀ j : ℕᵒᵖ, Finite (G.obj j) := fun j => (inferInstance : Finite (F j.unop))
  haveI : ∀ j : ℕᵒᵖ, Nonempty (G.obj j) := fun j => by
    obtain ⟨a, ha⟩ := hsurj j.unop
    exact ⟨(⟨a, ha⟩ : F j.unop)⟩
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_inverse_system G
  refine ⟨fun j => (s (Opposite.op j) : F j).1, fun j => ?_, fun j => (s (Opposite.op j) : F j).2⟩
  have h1 := hs (homOfLE (Nat.le_succ j)).op
  rw [Functor.ofOpSequence_map_homOfLE_succ] at h1
  have h2 := congrArg Subtype.val h1
  exact h2
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.LowLHolds
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace LateralTheory.EtaleTrace.H0LimitCoherence
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz

private theorem sub_of (l : ℕ) [Fact l.Prime] {E : Spc} {n : ℤ} (h : ∀ j, Subsingleton (Ht (l ^ j) E n 0)) :
    Subsingleton (HQ l E n 0) := by
  have hx : ∀ x : Hl l E n 0, x = 0 := by
    intro x
    apply Subtype.ext
    funext j
    exact @Subsingleton.elim _ (h j) _ _
  refine ⟨fun z w => ?_⟩
  obtain ⟨b, x, -, rfl⟩ := tensor_form l z
  obtain ⟨c, y, -, rfl⟩ := tensor_form l w
  rw [hx x, hx y, TensorProduct.tmul_zero, TensorProduct.tmul_zero]

theorem lowL_holds : LowL := by
  intro hI hP l _ k _ _ hl hR hT
  have hu : IsUnit ((l : ℕ) : Γ(S k, ⊤)) := by
    simpa using (isUnit_iff_ne_zero.mpr hl).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
  obtain ⟨ω, hω, hone⟩ := hR.one_def (S k) hu
  obtain ⟨hsurj, hinj⟩ := rep_of ω
    (fun j z => by
      obtain ⟨a, ha⟩ := (hT j).1.1 z
      exact ⟨a, by rw [ha]; simp [lv, hω]⟩)
    (fun j a ha => (hT j).1.2 a (by simpa [lv, hω] using ha))
  let e : ℤ_[l] ≃ₗ[ℤ_[l]] Hl l (sch.obj (S k)) 0 0 :=
    LinearEquiv.ofBijective (LinearMap.toSpanSingleton ℤ_[l] _ ω)
      ⟨fun c d hcd => by
        have h0 : (c - d) • ω = 0 := by
          simpa [sub_smul, sub_eq_zero] using hcd
        exact sub_eq_zero.mp (hinj _ h0),
       fun x => by
        obtain ⟨c, hc⟩ := hsurj x
        exact ⟨c, by simp [hc]⟩⟩
  let Φ : V l (S k) 0 ≃ₗ[ℤ_[l]] ℚ_[l] :=
    (TensorProduct.congr (LinearEquiv.refl ℤ_[l] ℚ_[l]) e.symm).trans (TensorProduct.rid ℤ_[l] ℚ_[l])
  have hΦ : ∀ (q : ℚ_[l]) (u : Hl l (sch.obj (S k)) 0 0),
      Φ (q ⊗ₜ u) = ((e.symm u : ℤ_[l]) : ℚ_[l]) * q := by
    intro q u
    simp [Φ, Algebra.smul_def]
  have he : ∀ c : ℤ_[l], e.symm (c • ω) = c := by
    intro c
    rw [LinearEquiv.symm_apply_eq]
    rfl
  have hsm : ∀ r : ℚ_[l], r • oneV l (S k) = r ⊗ₜ ω := by
    intro r
    rw [hone, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hΦr : ∀ r : ℚ_[l], Φ (r • oneV l (S k)) = r := by
    intro r
    rw [hsm, hΦ]
    have := he 1
    rw [one_smul] at this
    rw [this]
    simp
  have key : ∀ (b : ℤ_[l]) (u : Hl l (sch.obj (S k)) 0 0), b ≠ 0 →
      ((b : ℚ_[l])⁻¹ ⊗ₜ[ℤ_[l]] u : V l (S k) 0) = 0 → u = 0 := by
    intro b u hb h
    have h1 := congrArg Φ h
    rw [hΦ, map_zero] at h1
    have hb' : (b : ℚ_[l]) ≠ 0 := fun h' => hb (Subtype.ext h')
    have h2 : ((e.symm u : ℤ_[l]) : ℚ_[l]) = 0 := by
      rcases mul_eq_zero.mp h1 with h3 | h3
      · exact h3
      · exact absurd h3 (inv_ne_zero hb')
    have h4 : e.symm u = 0 := Subtype.ext h2
    simpa using congrArg e h4
  have hpb : ∀ {X : Scheme} (y : S k ⟶ X) (q : ℚ_[l]) (x : Hl l (sch.obj X) 0 0),
      pb l y 0 (q ⊗ₜ x) = q ⊗ₜ pullHl l (sch.map y) 0 0 x := by
    intro X y q x
    simp only [pb, pullHQ, LinearMap.baseChange_tmul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro X n hn
    exact sub_of l (fun j => ((In.a9 hI) (ZMod (l ^ j)) (tw (l ^ j) 0)).1 (sch.obj X) n hn)
  · intro n hn
    exact sub_of l (fun j => hP hI k (l ^ j) n 0 hn)
  · intro z
    obtain ⟨b, x, hb, rfl⟩ := tensor_form l z
    obtain ⟨c, rfl⟩ := hsurj x
    refine ⟨(c : ℚ_[l]) * (b : ℚ_[l])⁻¹, ?_, ?_⟩
    · apply Φ.injective
      rw [hΦr, hΦ, he]
    · intro r hr
      have h1 := congrArg Φ hr
      rw [hΦr, hΦ, he] at h1
      exact h1.symm
  · intro X p hp z hz
    obtain ⟨b, x, hb, rfl⟩ := tensor_form l z
    have hx : x = 0 := by
      apply Subtype.ext
      funext j
      apply ((hT j).2 p hp (x.1 j)).1
      intro y
      have h1 := hz y
      rw [hpb] at h1
      have h2 := key b _ hb h1
      exact congrArg (fun w : Hl l (sch.obj (S k)) 0 0 => w.1 j) h2
    rw [hx, TensorProduct.tmul_zero]
  · intro X p hp hc z y y'
    obtain ⟨b, x, hb, rfl⟩ := tensor_form l z
    rw [hpb, hpb]
    congr 1
    apply Subtype.ext
    funext j
    exact ((hT j).2 p hp (x.1 j)).2 hc y y'

end UpperTheory.Gal.KunnethLefschetz
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PKunBij
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace

namespace UpperTheory.Gal.KunnethLefschetz

theorem kunBij_holds : KunBij := by
  intro hIn l _ k _ _ hl hR d X p hp n
  obtain ⟨hprop, hsm⟩ := hp
  haveI := hprop
  haveI := hsm
  haveI : Smooth p := SmoothOfRelativeDimension.smooth d p
  apply kun_bijective_of_kunIso l p p n (fun a m r h => hR.isCup _ a m r h)
  exact hIn.kun hIn.a2 hIn.a6nat hIn.a6ring hIn.a7 hIn.a8 hIn.a9 hIn.a10 hIn.a11 hIn.b1 hIn.b2
    hIn.b3 hIn.e2 hIn.e3 hIn.e4 l k (Ne.isUnit hl) p p n 0

end UpperTheory.Gal.KunnethLefschetz

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PFinSupp
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

private theorem pbc (l : ℕ) [Fact l.Prime] {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (n : ℤ) (z : V l C n) :
    pb l (f ≫ g) n z = pb l f n (pb l g n z) := by
  rw [LateralTheory.EtaleTrace.pb_comp]; rfl

private theorem pbi (l : ℕ) [Fact l.Prime] (X : Scheme.{0}) (n : ℤ) (z : V l X n) : pb l (𝟙 X) n z = z := by
  show pullHQ l (sch.map (𝟙 X)) n 0 z = z
  rw [CategoryTheory.Functor.map_id]
  unfold pullHQ
  rw [pullHl_id, LinearMap.baseChange_id]; rfl

private theorem step {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (hP : Pairs) (hL : Low l k) (G : GysQ k l) (d : ℕ)
    {X : Scheme.{0}} (p : X ⟶ S k) (hs : IsSeparated p) (hsm : SmoothOfRelativeDimension d p) (y : Pt p)
    (U' U : X.Opens) (hU : (U : Set X) = (U' : Set X) \ Set.range y.1) (hy : Set.range y.1 ⊆ (U' : Set X))
    (z : V l X (2 * d)) (hz : pb l U.ι _ z = 0) :
    ∃ r : ℚ_[l], pb l U'.ι _ (z - r • G.pt d y) = 0 := by
  have hsep : IsSeparated (U'.ι ≫ p) := inferInstance
  have hsm' : SmoothOfRelativeDimension d (U'.ι ≫ p) := by
    have h := smoothOfRelativeDimension_comp (n := 0) (m := d) U'.ι p
    rwa [Nat.zero_add] at h
  have hr : Set.range y.1 ⊆ Set.range U'.ι := by simpa using hy
  let y' : S k ⟶ U'.toScheme := IsOpenImmersion.lift U'.ι y.1 hr
  have hy' : y' ≫ U'.ι = y.1 := IsOpenImmersion.lift_fac _ _ _
  let t : Pt (U'.ι ≫ p) := ⟨y', by rw [← Category.assoc, hy', y.2]⟩
  have hpt : IsPair d 0 (U'.ι ≫ p) y' := ((hP k d _ hsep hsm').2 t).1
  have hpy : IsPair d 0 p y.1 := ((hP k d p hs hsm).2 y).1
  have hoff : Off y' (U'.ι ⁻¹ᵁ U) := by
    unfold Off
    ext x
    have hx : U'.ι x ∈ (U' : Set X) := by
      have : U'.ι x ∈ Set.range U'.ι := ⟨x, rfl⟩
      simpa using this
    show U'.ι x ∈ (U : Set X) ↔ x ∉ Set.range y'
    rw [hU]
    constructor
    · rintro ⟨-, h2⟩ ⟨w, rfl⟩
      exact h2 ⟨w, by rw [← hy']; rfl⟩
    · intro h
      refine ⟨hx, ?_⟩
      rintro ⟨w, hw⟩
      apply h
      refine ⟨w, ?_⟩
      apply U'.ι.isOpenEmbedding.injective
      rw [← hw, ← hy']; rfl
  have hdead : pb l (U'.ι ⁻¹ᵁ U).ι _ (pb l U'.ι _ z) = 0 := by
    rw [← pbc, ← morphismRestrict_ι, pbc, hz, map_zero]
  have hprop : IsProper (y' ≫ U'.ι ≫ p) := by
    have : y' ≫ U'.ι ≫ p = 𝟙 _ := t.2
    rw [this]; infer_instance
  obtain ⟨a, ha⟩ := G.onto hpt (zero_add _) _ hoff hprop _ hdead
  obtain ⟨r, hra, -⟩ := hL.line a
  refine ⟨r, ?_⟩
  have hpb : IsPullback y' (𝟙 _) U'.ι y.1 := IsPullback.of_vert_isIso_mono ⟨by simp [hy']⟩
  have hnat := G.nat hpt hpy U'.ι (𝟙 _) rfl hpb (zero_add _) (oneV l (S k))
  rw [pbi] at hnat
  have hpt' : G.pt d y = G.g hpy (zero_add _) (oneV l (S k)) := by
    simp only [GysQ.cls, dif_pos hpy]
  rw [map_sub, map_smul, hpt', hnat, ← map_smul, ← hra, ha, sub_self]

end UpperTheory.Gal.KunnethLefschetz

theorem UpperTheory.Gal.KunnethLefschetz.finSupp_holds :
    UpperTheory.Gal.KunnethLefschetz.FinSupp := by
  unfold FinSupp
  intro _ hP l _ k _ _ _ _ hL G d X p hsep hsm s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro U hU z hz
    have hT : U = ⊤ := by
      apply SetLike.coe_injective
      simpa [OffPts] using hU
    subst hT
    have h0 : z = 0 := by
      have e : X.topIso.inv ≫ (⊤ : X.Opens).ι = 𝟙 X := by simp
      have h1 : pb l X.topIso.inv _ (pb l (⊤ : X.Opens).ι _ z) = z := by
        rw [← pbc, e, pbi]
      rw [← h1, hz, map_zero]
    rw [h0]; exact zero_mem _
  | insert y s hy ih =>
    intro U hU z hz
    have hcl : ∀ t : Pt p, IsClosed (Set.range t.1) := fun t => by
      haveI := ((hP k d p hsep hsm).2 t).1.cl
      exact t.1.isClosedEmbedding.isClosed_range
    have hopen : IsOpen ((⋃ t ∈ s, Set.range t.1)ᶜ) :=
      (s.finite_toSet.isClosed_biUnion fun t _ => hcl t).isOpen_compl
    let U' : X.Opens := ⟨_, hopen⟩
    have hU' : OffPts s U' := rfl
    have hU2 : (U : Set X) = (U' : Set X) \ Set.range y.1 := by
      rw [hU, Finset.set_biUnion_insert, Set.compl_union, Set.diff_eq, Set.inter_comm]; rfl
    by_cases hin : Set.range y.1 ⊆ (U' : Set X)
    · obtain ⟨r, hr⟩ := step hP hL G d p hsep hsm y U' U hU2 hin z hz
      have h1 := ih U' hU' _ hr
      have hz' : z = (z - r • G.pt d y) + r • G.pt d y := (sub_add_cancel _ _).symm
      rw [hz']
      exact add_mem h1 (Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩))
    · have hsub : Subsingleton (S k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
      have hUU : U = U' := by
        apply SetLike.coe_injective
        rw [hU2]
        ext x
        constructor
        · exact fun h => h.1
        · intro hx
          refine ⟨hx, ?_⟩
          rintro ⟨w, rfl⟩
          apply hin
          rintro _ ⟨w', rfl⟩
          rwa [Subsingleton.elim w' w]
      subst hUU
      exact ih _ hU' z hz
end
end

namespace UpperTheory.Gal.KunnethLefschetz

section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct DirectSum

theorem offEx_holds :
    UpperTheory.Gal.KunnethLefschetz.OffEx := by
  refine ⟨fun {Z X} ι hι => ⟨⟨(Set.range ι)ᶜ, ι.isClosedEmbedding.isClosed_range.isOpen_compl⟩, rfl⟩, ?_⟩
  intro Z' X' Z X ι' ι f u h U hU
  change f ⁻¹' (U : Set X) = _
  rw [hU, Set.preimage_compl, ← Scheme.Pullback.range_fst]
  congr 1
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨h.isoPullback.inv y, by rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨h.isoPullback.hom y, by rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]⟩

theorem topPart_holds : TopPart := by
  intro l _ k _ _ hl d X p hp hR hLow hKun lam s a hlam Λ hΛ δ
  classical
  have hmem : δ ∈ Submodule.span ℚ_[l]
      {w | ∃ a b, ∃ (h : a + b = 2 * (d : ℤ)), ∃ u v, w = ext2 l p h u v} := by
    rw [hKun.span]
    trivial
  induction hmem using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a', b', h', u, v, rfl⟩ := hx
    rcases lt_trichotomy b' 0 with hb | hb | hb
    · haveI := hLow.neg X b' hb
      obtain rfl : v = 0 := Subsingleton.elim _ _
      refine ⟨0, ?_, ?_⟩
      · simp [ext2]
      · simp [ext2]
    · subst hb
      obtain rfl : a' = 2 * (d : ℤ) := by omega
      let F : V l X (2 * (d : ℤ)) →ₗ[ℚ_[l]] V l (pullback p p) (2 * (d : ℤ)) :=
        (cupV l (pullback p p) h').flip (pb l (pullback.snd p p) 0 v) ∘ₗ
          pb l (pullback.fst p p) (2 * (d : ℤ))
      have hsum : ∑ t, ext2 l p (add_zero _ : 2 * (d : ℤ) + 0 = 2 * d) (a t) (a.repr u t • v) =
          ext2 l p h' u v := by
        calc ∑ t, ext2 l p (add_zero _ : 2 * (d : ℤ) + 0 = 2 * d) (a t) (a.repr u t • v)
            = ∑ t, a.repr u t • F (a t) := by
              refine Finset.sum_congr rfl fun t _ => ?_
              simp only [ext2, F, map_smul, LinearMap.comp_apply, LinearMap.flip_apply]
          _ = F (∑ t, a.repr u t • a t) := by
              set_option synthInstance.maxHeartbeats 100000 in
                rw [map_sum]
              simp only [map_smul]
          _ = ext2 l p h' u v := by
              rw [a.sum_repr]
              rfl
      refine ⟨fun t => a.repr u t • v, ?_, ?_⟩
      · rw [hΛ.1 u v, ← Finset.sum_smul]
        congr 1
        conv_rhs => rw [← a.sum_repr u]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        simp only [map_smul, hlam, smul_eq_mul, mul_one]
      · rw [hsum, sub_self]
        exact Submodule.zero_mem _
    · refine ⟨0, ?_, ?_⟩
      · simp only [Pi.zero_apply, Finset.sum_const_zero]
        exact (hΛ.2 a' b' h' (ne_of_gt hb) u v).symm
      · have h0 : ∑ t, ext2 l p (add_zero _ : 2 * (d : ℤ) + 0 = 2 * d) (a t) ((0 : Fin s → V l X 0) t) = 0 := by
          simp [ext2]
        rw [h0, sub_zero]
        rcases le_or_gt 0 a' with ha | ha
        · exact Submodule.subset_span ⟨a', b', h', u, v, ha, hb, rfl⟩
        · haveI := hLow.neg X a' ha
          obtain rfl : u = 0 := Subsingleton.elim _ _
          simp [ext2]
  | zero =>
    refine ⟨0, ?_, ?_⟩
    · simp
    · simp [ext2]
  | add x y _ _ hx hy =>
    obtain ⟨b1, hb1, hm1⟩ := hx
    obtain ⟨b2, hb2, hm2⟩ := hy
    refine ⟨b1 + b2, ?_, ?_⟩
    · simp [Finset.sum_add_distrib, hb1, hb2]
    · convert Submodule.add_mem _ hm1 hm2 using 1
      simp only [ext2, Pi.add_apply, map_add (f := _), Finset.sum_add_distrib]
      abel
  | smul c x _ hx =>
    obtain ⟨b, hb, hm⟩ := hx
    refine ⟨c • b, ?_, ?_⟩
    · simp [← Finset.smul_sum, hb]
    · convert Submodule.smul_mem _ c hm using 1
      simp only [ext2, Pi.smul_apply, map_smul, smul_sub, Finset.smul_sum]

end
end

theorem steps_holds : Steps :=
  ⟨offEx_holds, pairs_holds, pnFacts_holds, hypEmb_holds, finCov_holds, finFib_holds, comps_holds, ringL_holds, lowTL_holds, ptVanT_holds, lowL_holds, towerL_holds, affVan_holds, twBij_holds, gysTL_holds, gysinTwistZero_exists, qEasy_holds, limOnto_holds, qOnto_holds, qProj_holds, kunBij_holds, kunL_holds, swap_holds, slice_holds, ptInt_holds, detectL_holds, dualL_holds, finSupp_holds, pnCls_holds, injL_holds, trComp_holds, divL_holds, basisOne_holds, topPart_holds⟩

theorem qDual_holds (hI : In) (hT : TrIn) : QDual := steps_holds.qDual hI hT

theorem qDiag_holds (hI : In) (hT : TrIn) : QDiag := steps_holds.qDiag hI hT

end UpperTheory.Gal.KunnethLefschetz
end

namespace UpperTheory.Gal.KunnethLefschetz
open GlobalTheory.EtC

theorem trIn_holds : TrIn :=
  ⟨TranscendenceTraces.wtNormal_holds, TranscendenceTraces.nmlLoc_holds, TranscendenceTraces.nwtDeg_holds, TranscendenceTraces.trDegQ_holds GlobalTheory.T.etaleCohomology_coefficientRing_invariance⟩

end UpperTheory.Gal.KunnethLefschetz
