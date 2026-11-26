module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.BasisOne
public import Development.EtaleCohomology.EtaleTrace.LPdCut

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PSlice
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace

namespace UpperTheory.Gal.KunnethLefschetz

theorem slice_holds : Slice := by
  intro hP l _ k _ _ hl d X p hSP hR G y
  obtain ⟨hprop, hsm⟩ := hSP
  haveI := hprop
  obtain ⟨hdiag, hpt⟩ := hP k d p inferInstance hsm
  obtain ⟨hy, hpb⟩ := hpt y
  have hunitX : IsUnit ((l : Γ(X, ⊤))) := by
    have h1 : IsUnit ((l : k)) := isUnit_iff_ne_zero.mpr hl
    have h2 := (h1.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom
    simpa [map_natCast] using h2
  have hunit : IsUnit ((l : Γ(S k, ⊤))) := by
    simpa [map_natCast] using hunitX.map (y.1.appTop).hom
  simp only [GysQ.diag, GysQ.pt, GysQ.cls, dif_pos hdiag, dif_pos hy]
  rw [G.nat hy hdiag (slice y) y.1
    (by rw [slice, ← Category.assoc, pullback.lift_fst, Category.id_comp]) hpb]
  congr 1
  first
  | exact hR.one_nat y.1 hunitX
  | exact hR.one_nat y.1 hunit

end UpperTheory.Gal.KunnethLefschetz
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.SwapSymmetry
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

private theorem pb_self (l : ℕ) [Fact l.Prime] {X : Scheme.{0}} (n : ℤ) (x : V l X n) : pb l (𝟙 X) n x = x := by
  simp [pb, pullHQ, pullHl_id, LinearMap.baseChange_id]

private theorem pb_comp_apply (l : ℕ) [Fact l.Prime] {Z Y X : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (n : ℤ) (x : V l X n) :
    pb l (f ≫ g) n x = pb l f n (pb l g n x) := by
  rw [LateralTheory.EtaleTrace.pb_comp]
  rfl

theorem UpperTheory.Gal.KunnethLefschetz.swap_holds :
    UpperTheory.Gal.KunnethLefschetz.Swap := by
  intro hP l _ k _ _ hl d X p hSP hR G n w h h' x
  obtain ⟨hprop, hsm⟩ := hSP
  haveI := hprop
  have hpair := (hP k d p inferInstance hsm).1
  have hunit : IsUnit ((l : Γ(X, ⊤))) := by
    have h1 : IsUnit ((l : k)) := isUnit_iff_ne_zero.mpr hl
    have h2 := (h1.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom
    simpa [map_natCast] using h2
  have hu := hR.mul_one X hunit
  have key : ∀ f : pullback p p ⟶ X, pullback.diagonal p ≫ f = 𝟙 X →
      cupV l (pullback p p) h (pb l f n x) (G.diag d p) = G.g hpair h x := by
    intro f hf
    have hd : G.diag d p = G.g hpair (show (0 : ℤ) + 2 * d = 2 * d by simp) (oneV l X) := by
      simp only [GysQ.diag, GysQ.cls, dif_pos hpair]
    rw [hd, ← G.proj hpair (show n + 0 = n by simp) h (show (0 : ℤ) + 2 * d = 2 * d by simp) h,
      ← pb_comp_apply, hf, pb_self, hu]
  rw [key _ (by simp), hR.comm (pullback p p) (2 * d) n w h' h,
    key _ (by simp), Int.negOnePow_even _ ⟨d * n, by ring⟩, one_smul]
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PGysTL
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

private def castHom {q : ℕ} {E : Spc} {n i n' i' : ℤ} (hn : n = n') (hi : i = i') :
    Ht q E n i →+ Ht q E n' i' where
  toFun := Ht.cast hn hi
  map_zero' := by subst hn hi; rfl
  map_add' := LRingPf.cast_add hn hi

private def pairSP {k : Type} [Field k] {d e : ℕ} {Z X : Scheme.{0}} {p : X ⟶ S k} {ι : Z ⟶ X}
    (h : IsPair d e p ι) : LateralTheory.CohomologicalPurity.SP d :=
  { X := X, Z := Z, S := S k, p := p, ι := ι, e := e
    U := ⟨(Set.range ι)ᶜ, h.cl.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    cl := h.cl, smX := h.big, smZ := h.small, hU := rfl }

theorem UpperTheory.Gal.KunnethLefschetz.gysTL_holds :
    UpperTheory.Gal.KunnethLefschetz.GysTL := by
  unfold GysTL
  intro hI hO k _
  have hg : ∀ d, LateralTheory.CohomologicalPurity.Gysin d := hI.gys
  unfold LateralTheory.CohomologicalPurity.Gysin at hg
  choose gys rs H using hg
  refine ⟨⟨fun q d e Z X p ι h n m i j hn hi =>
    (castHom hn hi).comp (gys d q (pairSP h) n i), ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro q _ hq d e Z X p ι h n m i j hn hi U hU
    subst hn hi
    obtain rfl : U = (pairSP h).U := TopologicalSpace.Opens.ext hU
    exact ((H d q (pairSP h) (LPdCut.unit_of p hq)).1 n i).2.2
  · intro q _ hq d e Z X p ι h n m i j hn hi U hU hs
    subst hn hi
    obtain rfl : U = (pairSP h).U := TopologicalSpace.Opens.ext hU
    have hx := ((H d q (pairSP h) (LPdCut.unit_of p hq)).1 n i).2.1
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    obtain ⟨u, rfl⟩ := (hx a).1 ha
    rw [hs.elim u 0]
    exact map_zero (rs d q (pairSP h) n i)
  · intro q _ hq d e' e Z' X' Z X p' ι' p ι h' h f u hpb n m i j hn hi a
    subst hn hi
    have hoff : Off ι' (f ⁻¹ᵁ (pairSP h).U) := hO.2 ι' ι f u hpb (pairSP h).U rfl
    have hle : (pairSP h').U ≤ f ⁻¹ᵁ (pairSP h).U :=
      (TopologicalSpace.Opens.ext hoff.symm : (pairSP h').U = f ⁻¹ᵁ (pairSP h).U).le
    exact (((H d q (pairSP h) (LPdCut.unit_of p hq)).2.1 (pairSP h') ⟨f, u, hpb, hle⟩ n i).1 a)
  · intro q _ hq d e Z X p ι h n m r s t i j i' j' w h1 h2 h3 h4 k1 k2 k3 k4 a b
    subst h1 h2 h3 k1 k2 k3
    exact (H d q (pairSP h) (LPdCut.unit_of p hq)).2.2.1 n m i j a b
  · intro q r _ hq hr d e Z X p ι h n m i j hn hi a
    subst hn hi
    exact (((H d q (pairSP h) (LPdCut.unit_of p hq)).2.2.2 r hr n i).1 a).symm
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PPtInt
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

private theorem pb_id' (l : ℕ) [Fact l.Prime] (X : Scheme.{0}) (n : ℤ) (z : V l X n) : pb l (𝟙 X) n z = z := by
  simp [pb, pullHQ, pullHl_id, LinearMap.baseChange_id]

private theorem slice_gen {l : ℕ} [Fact l.Prime] {k : Type} [Field k] (R : Ring l) {X : Scheme.{0}} {p : X ⟶ S k}
    (y : Pt p) {a b n : ℤ} (h : a + b = n) (u : V l X a) (v : V l X b) :
    pb l (slice y) n (ext2 l p h u v) = cupV l X h u (pb l p b (pb l y.1 b v)) := by
  simp only [ext2]
  rw [R.nat (slice y) a b n h]
  have e1 : pb l (slice y) a (pb l (pullback.fst p p) a u) = u := by
    rw [← LinearMap.comp_apply, ← pb_comp]
    simp only [slice, pullback.lift_fst]
    exact pb_id' l X a u
  have e2 : pb l (slice y) b (pb l (pullback.snd p p) b v) = pb l p b (pb l y.1 b v) := by
    rw [← LinearMap.comp_apply, ← pb_comp, ← LinearMap.comp_apply, ← pb_comp]
    simp only [slice, pullback.lift_snd]
  rw [e1, e2]

theorem ptInt_holds : PtInt := by
  intro l _ k _ _ hl d X p hSP R L K lam Λ hΛ y w
  have hunitX : IsUnit ((l : Γ(X, ⊤))) := by
    have h1 : IsUnit ((l : k)) := isUnit_iff_ne_zero.mpr hl
    have h2 := (h1.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom
    simpa [map_natCast] using h2
  have hunitS : IsUnit ((l : Γ(S k, ⊤))) := by
    simpa [map_natCast] using hunitX.map (y.1.appTop).hom
  have key : (pb l y.1 0) ∘ₗ Λ =
      (lam ∘ₗ pb l (slice y) (2 * d)).smulRight (oneV l (S k)) := by
    apply LinearMap.ext_on (K.span (2 * d))
    rintro _ ⟨a, b, hab, u, v, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.smulRight_apply]
    rw [slice_gen R y hab u v]
    by_cases hb : b = 0
    · subst hb
      have ha : a = 2 * d := by omega
      subst ha
      obtain ⟨r, hr, -⟩ := L.line (pb l y.1 0 v)
      rw [hΛ.1, map_smul, hr]
      simp only [map_smul, R.one_nat p hunitS, R.mul_one X hunitX, smul_smul, smul_eq_mul]
      rw [mul_comm]
    · have hz : pb l y.1 b v = 0 := by
        rcases lt_or_gt_of_ne hb with hneg | hpos
        · haveI := L.neg (S k) b hneg
          exact Subsingleton.elim _ _
        · haveI := L.pos b hpos
          exact Subsingleton.elim _ _
      rw [hΛ.2 a b hab hb u v, map_zero, hz, map_zero, map_zero, map_zero, zero_smul]
  exact LinearMap.congr_fun key w

end UpperTheory.Gal.KunnethLefschetz
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PTwBij
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace LateralTheory.EtaleTrace.LRingPf
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz

private theorem inv_of_unit {q : ℕ} {X : Scheme.{0}} (hl : IsUnit (q : Γ(X, ⊤))) : Inv q (sch.obj X) := by
  intro U hU
  obtain ⟨y⟩ := hU
  let y' : U ⟶ X := y
  simpa using hl.map y'.appTop.hom

private theorem cancel_lemma {q : ℕ} {E : Spc} {n i : ℤ} (h1 : n = n) (h2 : i = i) (x : Ht q E n i) :
    Ht.cast h1 h2 x = x := rfl

private theorem eq_of_mul_mul_eq_of_det_ne_zero {q : ℕ} {E : Spc} {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E n i)
    (y : Ht q E n' i') (h : Ht.cast h1 h2 x = y) : x = Ht.cast h1.symm h2.symm y := by
  subst h
  rw [LRingPf.cast_cast, cancel_lemma]

private theorem cancel {q : ℕ} [NeZero q] (h6 : DivisorRingCompatibility) {E : Spc} (hi : Inv q E) {i i' : ℤ} (hs : i + i' = 0)
    (a : Ht q E 0 i) (b : Ht q E 0 i') (hab : (cup q a b).cast (add_zero 0) hs = one q E) {n j w : ℤ}
    (h1 : i' + j = w) (h2 : i + w = j) (c : Ht q E n j) :
    (cup q a ((cup q b c).cast (zero_add n) h1)).cast (zero_add n) h2 = c := by
  obtain ⟨hone, hassoc, -⟩ := h6 q E
  have e1 := hassoc a b c
  rw [eq_of_mul_mul_eq_of_det_ne_zero _ _ _ _ hab, cup_cast_left, hone hi, LRingPf.cast_cast] at e1
  have e3 := eq_of_mul_mul_eq_of_det_ne_zero _ _ _ _ e1.symm
  rw [cup_cast_right, LRingPf.cast_cast, e3, LRingPf.cast_cast, LRingPf.cast_cast, cancel_lemma]

private theorem swap {q : ℕ} [NeZero q] (h6 : DivisorRingCompatibility) {E : Spc} {i i' : ℤ} (hs : i + i' = 0) (hs' : i' + i = 0)
    (a : Ht q E 0 i) (b : Ht q E 0 i') (hab : (cup q a b).cast (add_zero 0) hs = one q E) :
    (cup q b a).cast (add_zero 0) hs' = one q E := by
  rw [(h6 q E).2.2 b a, cast_usmul, LRingPf.cast_cast, hab]
  simp

private theorem bij_of (hI : In) {k : Type} [Field k] {q : ℕ} [NeZero q] (hq : IsUnit (q : k)) {i i' : ℤ}
    (hs : i + i' = 0) (u : Ht q (sch.obj (S k)) 0 i) (v : Ht q (sch.obj (S k)) 0 i')
    (huv : (cup q u v).cast (add_zero 0) hs = one q (sch.obj (S k))) {X : Scheme.{0}} (p : X ⟶ S k) (n j w : ℤ)
    (hw : i + j = w) : Function.Bijective (twMul q p hw u n) := by
  have hX : Inv q (sch.obj X) := inv_of_unit (LPdCut.unit_of p hq)
  have hS : Inv q (sch.obj (S k)) := inv_of_unit (LPdCut.unit_of (𝟙 (S k)) hq)
  have hUV : (cup q (pull _ (sch.map p) _ 0 u) (pull _ (sch.map p) _ 0 v)).cast (add_zero 0) hs = one q (sch.obj X) := by
    rw [← (hI.a6nat q).2.1 (sch.map p) hS, ← huv, pull_cast, (hI.a6nat q).1]
  have hs' : i' + i = 0 := by omega
  have hVU := swap hI.a6ring hs hs' _ _ hUV
  have h : i' + w = j := by omega
  refine Function.bijective_iff_has_inverse.2 ⟨twMul q p h v n, fun c => ?_, fun c => ?_⟩
  · exact cancel hI.a6ring hX hs' _ _ hVU hw h c
  · exact cancel hI.a6ring hX hs _ _ hUV h hw c

theorem twBij_holds : TwBij := by
  unfold TwBij
  intro hI k _ q _ hq i u v huv X p n j w
  have hvu := swap hI.a6ring (add_neg_cancel i) (neg_add_cancel i) u v huv
  exact ⟨fun hw => bij_of hI hq (neg_add_cancel i) v u hvu p n j w hw,
    fun hw => bij_of hI hq (add_neg_cancel i) u v huv p n j w hw⟩

end UpperTheory.Gal.KunnethLefschetz
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PTrComp
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

private theorem pb_id (l : ℕ) [Fact l.Prime] (X : Scheme.{0}) (n : ℤ) : pb l (𝟙 X) n = LinearMap.id := by
  show pullHQ l (sch.map (𝟙 X)) n 0 = _
  rw [sch.map_id]
  unfold pullHQ
  rw [pullHl_id, LinearMap.baseChange_id]

private theorem lift_square {A B C : Scheme.{0}} (i : A ⟶ C) [IsOpenImmersion i] (y : B ⟶ C) (y' : B ⟶ A)
    (h : y' ≫ i = y) : IsPullback y' (𝟙 B) i y := (IsPullback.of_horiz_isIso_mono ⟨by simp [h]⟩ : IsPullback (𝟙 B) y' y i).flip

private theorem pt_restrict {k : Type} [Field k] {l : ℕ} [Fact l.Prime] (G : GysQ k l) (d : ℕ) {X : Scheme.{0}} {p : X ⟶ S k}
    (U : X.Opens) (y : Pt p) (y' : Pt (U.ι ≫ p)) (hy : y'.1 ≫ U.ι = y.1)
    (h : IsPair d 0 p y.1) (h' : IsPair d 0 (U.ι ≫ p) y'.1) :
    pb l U.ι _ (G.pt d y) = G.pt d y' := by
  show pb l U.ι _ (G.cls d 0 p y.1) = G.cls d 0 (U.ι ≫ p) y'.1
  unfold GysQ.cls
  rw [dite_eq_left h, dite_eq_left h', G.nat h' h U.ι (𝟙 _) rfl (lift_square U.ι y.1 y'.1 hy), pb_id]
  rfl

theorem trComp_holds : TrComp := by
  intro hC hO hP l _ k _ _ hl R G d hint X p hsp hpj
  obtain ⟨m, U, hU, hcov, hdisj⟩ := hC k d p hsp hpj
  have hex : ∀ j, ∃ lam : V l (U j : Scheme) (2 * d) →ₗ[ℚ_[l]] ℚ_[l],
      ∀ y : Pt ((U j).ι ≫ p), lam (G.pt d y) = 1 :=
    fun j => hint _ (hU j).1 (hU j).2.1 (hU j).2.2
  choose lamj hlamj using hex
  refine ⟨∑ j, (lamj j).comp (pb l (U j).ι (2 * d)), fun y => ?_⟩
  have hsep : IsSeparated p := by
    haveI := hsp.1
    infer_instance
  obtain ⟨hy, -⟩ := (hP k d p hsep hsp.2).2 y
  obtain ⟨s⟩ : Nonempty (S k) := inferInstance
  have hrange : Set.range y.1 = {y.1 s} := by
    ext t
    constructor
    · rintro ⟨t', rfl⟩
      rw [Subsingleton.elim t' s]
      rfl
    · intro ht
      exact ⟨s, ht.symm⟩
  obtain ⟨j, hj⟩ := hcov (y.1 s)
  have hsub : Set.range y.1 ⊆ Set.range (U j).ι := by
    rw [Scheme.Opens.range_ι, hrange]
    simpa using hj
  let y' : Pt ((U j).ι ≫ p) :=
    ⟨IsOpenImmersion.lift (U j).ι y.1 hsub, by
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact y.2⟩
  have hfac : y'.1 ≫ (U j).ι = y.1 := IsOpenImmersion.lift_fac _ _ _
  have hsep' : IsSeparated ((U j).ι ≫ p) := by
    haveI := (hU j).1.1
    infer_instance
  have hy' : IsPair d 0 ((U j).ι ≫ p) y'.1 := ((hP k d ((U j).ι ≫ p) hsep' (hU j).1.2).2 y').1
  rw [LinearMap.sum_apply, Finset.sum_eq_single j]
  · rw [LinearMap.comp_apply, pt_restrict G d (U j) y y' hfac hy hy', hlamj]
  · intro j' _ hj'
    obtain ⟨W, hW⟩ := hO.1 y.1 hy.cl
    have hle : U j' ≤ W := by
      intro t ht
      show t ∈ (W : Set X)
      rw [hW, hrange]
      rintro (rfl : t = y.1 s)
      exact (hdisj j' j hj').le_bot (show y.1 s ∈ U j' ⊓ U j from ⟨ht, hj⟩)
    rw [LinearMap.comp_apply, ← Scheme.homOfLE_ι X hle, pb_comp, LinearMap.comp_apply]
    unfold GysQ.pt GysQ.cls
    rw [dite_eq_left hy, G.off hy _ W hW, map_zero, map_zero]
  · intro h
    exact absurd (Finset.mem_univ j) h

end UpperTheory.Gal.KunnethLefschetz
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.DivLHolds
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct

namespace UpperTheory.Gal.KunnethLefschetz

private theorem pbc {l : ℕ} [Fact l.Prime] {Z Y X : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (n : ℤ) (x : V l X n) :
    pb l (f ≫ g) n x = pb l f n (pb l g n x) := by
  rw [LateralTheory.EtaleTrace.pb_comp]; rfl

private theorem powV_pull {l : ℕ} [Fact l.Prime] (R : Ring l) {Y X : Scheme.{0}} (f : Y ⟶ X) (hu : IsUnit (l : Γ(X, ⊤)))
    (x : V l X 2) (j : ℕ) : pb l f _ (powV l x j) = powV l (pb l f 2 x) j := by
  induction j with
  | zero => exact R.one_nat f hu
  | succ j ih =>
    change pb l f _ (cupV l X _ (powV l x j) x) = cupV l Y _ (powV l (pb l f 2 x) j) (pb l f 2 x)
    rw [R.nat, ih]

private theorem pull_onto {l : ℕ} [Fact l.Prime] (R : Ring l) {E W X : Scheme.{0}} (i : E ⟶ W) (s : W ⟶ X)
    (hu : IsUnit (l : Γ(W, ⊤))) (e : V l W 2) (hP : PBQ l (i ≫ s) (pb l i 2 e)) (n : ℤ) (b : V l E n) :
    ∃ m, pb l i n m = b := by
  have hle : (⊤ : Submodule ℚ_[l] (V l E n)) ≤ LinearMap.range (pb l i n) := by
    rw [← hP.span n, Submodule.span_le]
    rintro z ⟨j, a, h, u, rfl⟩
    refine ⟨cupV l W h (pb l s a u) (powV l e j), ?_⟩
    rw [R.nat, pbc, powV_pull R i hu]
  exact hle (Submodule.mem_top (x := b))

private theorem unit_eq {l : ℕ} [Fact l.Prime] (R : Ring l) {E W X : Scheme.{0}} (i : E ⟶ W) (s : W ⟶ X)
    (uX : IsUnit (l : Γ(X, ⊤))) (uE : IsUnit (l : Γ(E, ⊤))) (e ε : V l W 2) (u0 a v : _)
    (he : e = cupV l W (zero_add 2) (pb l s 0 u0) ε)
    (hP : PBQ l (i ≫ s) (pb l i 2 e))
    (hav : pb l i 2 ε = pb l (i ≫ s) 2 a + cupV l E (zero_add 2) (pb l (i ≫ s) 0 v) (pb l i 2 e)) :
    cupV l X (add_zero 0) v u0 = oneV l X := by
  set ξ := pb l i 2 e with hξdef
  have h0 : ξ = cupV l E (zero_add 2) (pb l (i ≫ s) 0 u0) (pb l i 2 ε) := by
    rw [hξdef, he, R.nat, pbc]
  have h1 : ξ = pb l (i ≫ s) 2 (cupV l X (zero_add 2) u0 a)
      + cupV l E (zero_add 2) (pb l (i ≫ s) 0 (cupV l X (add_zero 0) u0 v)) ξ := by
    conv_lhs => rw [h0, hav]
    rw [map_add (f := _), ← R.nat,
      ← R.assoc E 0 0 2 0 2 2 (add_zero 0) (zero_add 2) (zero_add 2) (zero_add 2), ← R.nat]
  have h2 : cupV l E (zero_add 2) (pb l (i ≫ s) 0 (oneV l X)) ξ = ξ := by
    rw [R.one_nat _ uX, R.one_mul E uE]
  have h3 : pb l (i ≫ s) 2 (cupV l X (zero_add 2) u0 a)
      + cupV l E (zero_add 2) (pb l (i ≫ s) 0 (cupV l X (add_zero 0) u0 v - oneV l X)) ξ = 0 := by
    rw [map_sub, map_sub, LinearMap.sub_apply, h2, ← add_sub_assoc, ← h1, sub_self]
  have h4 := hP.indep _ _ h3
  rw [sub_eq_zero] at h4
  rw [R.comm X 0 0 0 (add_zero 0) (add_zero 0) v u0, h4]
  simp

theorem divL_holds : DivL := by
  intro l _ k _ _ hl R G W E X px i s c hpair hprop U hoff e he0 hP n w h z hz
  have hk : IsUnit (l : k) := isUnit_iff_ne_zero.2 hl
  have uX := LPdCut.unit_of px hk
  have uW := LPdCut.unit_of (s ≫ px) hk
  have uE := LPdCut.unit_of (i ≫ s ≫ px) hk
  have h02 : (0 : ℤ) + 2 * ((1 : ℕ) : ℤ) = 2 := by norm_num
  have hnw : n + 2 * ((1 : ℕ) : ℤ) = w := by push_cast; omega
  have hn2 : n + 2 = w := by omega
  obtain ⟨ε, hε⟩ : ∃ ε, G.g hpair h02 (oneV l E) = ε := ⟨_, rfl⟩
  obtain ⟨ε0, hε0⟩ := G.onto hpair h02 U hoff hprop e he0
  obtain ⟨u0, rfl⟩ := hP.zero ε0
  have he : e = cupV l W (zero_add 2) (pb l s 0 u0) ε := by
    rw [← hε, ← G.proj hpair (add_zero 0) h02 h02 (zero_add 2), R.mul_one E uE, ← pbc, hε0]
  obtain ⟨a, v, hav⟩ := hP.two (pb l i 2 ε)
  have hunit := unit_eq R i s uX uE e ε u0 a v he hP hav
  have hε' : cupV l W (add_zero 2) e (pb l s 0 v) = ε := by
    rw [R.comm W 2 0 2 (add_zero 2) (zero_add 2), he,
      ← R.assoc W 0 0 2 0 2 2 (add_zero 0) (zero_add 2) (zero_add 2) (zero_add 2), ← R.nat, hunit,
      R.one_nat _ uX, R.one_mul W uW]
    simp
  obtain ⟨b, hb⟩ := G.onto hpair hnw U hoff hprop z hz
  obtain ⟨m', rfl⟩ := pull_onto R i s uW e hP n b
  have hz' : z = cupV l W hn2 m' ε := by
    rw [← hb, ← hε, ← G.proj hpair (add_zero n) hnw h02 hn2, R.mul_one E uE]
  refine ⟨cupV l W (zero_add n) (pb l s 0 v) m', ?_⟩
  rw [hz', ← R.assoc W 2 0 n 2 n w (add_zero 2) h (zero_add n) h, hε',
    R.comm W n 2 w hn2 h, Int.negOnePow_even _ ⟨n, by ring⟩, one_smul]

end UpperTheory.Gal.KunnethLefschetz
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PDetectL
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k]

private theorem exterior_product_cup_snd (R : Ring l) {X : Scheme.{0}} (p : X ⟶ S k) {a b n m t w : ℤ}
    (h1 : a + b = m) (h2 : m + n = w) (h3 : b + n = t) (h4 : a + t = w)
    (u : V l X a) (v : V l X b) (x : V l X n) :
    cupV l _ h2 (ext2 l p h1 u v) (pb l (pullback.snd p p) n x) =
      ext2 l p h4 u (cupV l X h3 v x) := by
  simp only [ext2]
  rw [R.assoc _ a b n m t w h1 h2 h3 h4, ← R.nat (pullback.snd p p) b n t h3 v x]

private theorem cup_fst_exterior_product (R : Ring l) {X : Scheme.{0}} (p : X ⟶ S k) {a b n m t w : ℤ}
    (h1 : a + b = m) (h2 : n + m = w) (h3 : n + a = t) (h4 : t + b = w)
    (x : V l X n) (u : V l X a) (v : V l X b) :
    cupV l _ h2 (pb l (pullback.fst p p) n x) (ext2 l p h1 u v) =
      ext2 l p h4 (cupV l X h3 x u) v := by
  simp only [ext2]
  rw [← R.assoc _ n a b t m w h3 h4 h1 h2, ← R.nat (pullback.fst p p) n a t h3 x u]

private theorem int_cup_snd (R : Ring l) {d : ℕ} {X : Scheme.{0}} {p : X ⟶ S k} (K : Kun l k d p)
    {lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l]} {n w : ℤ} (h : 2 * d + n = w)
    {Λ : V l (pullback p p) w →ₗ[ℚ_[l]] V l X n} (hΛ : IsInt l p lam h Λ)
    {Λ0 : V l (pullback p p) (2 * d) →ₗ[ℚ_[l]] V l X 0} (h0 : IsInt l p lam (add_zero _) Λ0)
    (x : V l X n) (y : V l (pullback p p) (2 * d)) :
    Λ (cupV l _ h y (pb l (pullback.snd p p) n x)) = cupV l X (zero_add n) (Λ0 y) x := by
  have key : Λ ∘ₗ (cupV l (pullback p p) h).flip (pb l (pullback.snd p p) n x) =
      ((cupV l X (zero_add n)).flip x) ∘ₗ Λ0 := by
    apply LinearMap.ext_on (K.span (2 * d))
    rintro _ ⟨a, b, hab, u, v, rfl⟩
    simp only [LinearMap.comp_apply, LinearMap.flip_apply]
    by_cases hb : b = 0
    · subst hb
      have ha : a = 2 * d := by omega
      subst ha
      rw [exterior_product_cup_snd R p hab h (zero_add n) h u v x, hΛ.1, h0.1, map_smul, LinearMap.smul_apply]
    · rw [exterior_product_cup_snd R p hab h rfl (by omega : a + (b + n) = w) u v x,
        hΛ.2 a (b + n) _ (by omega) u _, h0.2 a b hab hb u v, map_zero, LinearMap.zero_apply]
  exact LinearMap.congr_fun key y

private theorem int_fst_cup {d : ℕ} (R : Ring l) {X : Scheme.{0}} {p : X ⟶ S k}
    {lam : V l X (2 * d) →ₗ[ℚ_[l]] ℚ_[l]} {n w a b : ℤ} (h : 2 * d + n = w) (h2 : n + 2 * d = w)
    (h1 : a + b = 2 * d) {Λ : V l (pullback p p) w →ₗ[ℚ_[l]] V l X n} (hΛ : IsInt l p lam h Λ)
    (x : V l X n) (u : V l X a) (v : V l X b)
    (hx : ∀ hh : n + a = 2 * d, lam (cupV l X hh x u) = 0) :
    Λ (cupV l _ h2 (pb l (pullback.fst p p) n x) (ext2 l p h1 u v)) = 0 := by
  by_cases hb : b = n
  · subst b
    have ht : n + a = 2 * d := by omega
    rw [cup_fst_exterior_product R p h1 h2 ht h, hΛ.1, hx ht, zero_smul]
  · rw [cup_fst_exterior_product R p h1 h2 rfl (by omega : n + a + b = w)]
    exact hΛ.2 _ b _ hb _ _

theorem detectL_holds : DetectL := by
  intro l _ k _ _ hl d X p hSP R K lam δ hswap hΛ0
  obtain ⟨Λ0, h0⟩ := K.int lam 0 (2 * d) (add_zero _)
  have hone := hΛ0 Λ0 h0
  have hunit : IsUnit ((l : Γ(X, ⊤))) := by
    have h1 : IsUnit ((l : k)) := isUnit_iff_ne_zero.mpr hl
    have h2 := (h1.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).map p.appTop.hom
    simpa [map_natCast] using h2
  have hδ : δ ∈ Submodule.span ℚ_[l]
      {w | ∃ a b, ∃ (h : a + b = 2 * (d : ℤ)), ∃ u v, w = ext2 l p h u v} := by
    rw [K.span]
    trivial
  obtain ⟨N, f, g, hsum⟩ := Submodule.mem_span_set'.mp hδ
  have hg : ∀ t, ∃ a b, ∃ h : a + b = 2 * (d : ℤ), ∃ u v, (g t : V l (pullback p p) (2 * d)) = ext2 l p h u v :=
    fun t => (g t).2
  choose A B hAB U W hUW using hg
  refine ⟨N, A, U, fun n x hx => ?_⟩
  obtain ⟨Λ, hΛ⟩ := K.int lam n (2 * d + n) rfl
  calc x = cupV l X (zero_add n) (oneV l X) x := (R.one_mul X hunit n x).symm
    _ = cupV l X (zero_add n) (Λ0 δ) x := by rw [hone]
    _ = Λ (cupV l _ (rfl : 2 * (d : ℤ) + n = 2 * d + n) δ (pb l (pullback.snd p p) n x)) :=
        (int_cup_snd R K rfl hΛ h0 x δ).symm
    _ = Λ (cupV l _ (by ring : n + 2 * (d : ℤ) = 2 * d + n) (pb l (pullback.fst p p) n x) δ) := by
        rw [hswap n _ (by ring) rfl x]
    _ = 0 := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← hsum, map_sum, map_sum]
        apply Finset.sum_eq_zero
        intro t _
        rw [map_smul, map_smul, hUW t,
          int_fst_cup R rfl (by ring) (hAB t) hΛ x (U t) (W t) (hx t), smul_zero]

end UpperTheory.Gal.KunnethLefschetz
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PDualL
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

theorem UpperTheory.Gal.KunnethLefschetz.dualL_holds :
    UpperTheory.Gal.KunnethLefschetz.DualL := by
  intro l _ k _ _ hl d X p hSP hint R L lam hdet hlam
  obtain ⟨s, c, a, hA⟩ := hdet
  have hprop := hSP.1
  have nd : ∀ (n m : ℤ) (h : n + m = 2 * (d : ℤ)) (y : V l X m),
      (∀ x : V l X n, lam (cupV l X h x y) = 0) → y = 0 := by
    intro n m h y hy
    apply hA m y
    intro t ht
    obtain rfl : c t = n := by omega
    rw [R.comm X m (c t) _ ht h, Units.smul_def, map_zsmul, hy, smul_zero]
  have fd : ∀ n, FiniteDimensional ℚ_[l] (V l X n) := by
    intro n
    classical
    let f : V l X n →ₗ[ℚ_[l]] (Fin s → ℚ_[l]) := LinearMap.pi fun t =>
      if h : n + c t = 2 * (d : ℤ) then lam ∘ₗ (cupV l X h).flip (a t) else 0
    refine FiniteDimensional.of_injective f ?_
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    apply hA n x
    intro t h
    have := congrFun hx t
    simpa [f, h] using this
  have van : ∀ n, 2 * (d : ℤ) < n → Subsingleton (V l X n) := by
    intro n hn
    have key : ∀ z : V l X n, z = 0 := fun z => hA n z (fun t h => by
      haveI := L.neg X (c t) (by omega)
      rw [Subsingleton.elim (a t) 0]
      simp)
    exact ⟨fun x y => by rw [key x, key y]⟩
  have le : ∀ n m (h : n + m = 2 * (d : ℤ)),
      Module.finrank ℚ_[l] (V l X m) ≤ Module.finrank ℚ_[l] (V l X n) := by
    intro n m h
    haveI := fd n
    haveI := fd m
    have inj : Function.Injective ((cupV l X h).compr₂ lam).flip := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro y hy
      exact nd n m h y (fun x => by simpa using LinearMap.congr_fun hy x)
    have := LinearMap.finrank_le_finrank_of_injective inj
    rwa [Subspace.dual_finrank_eq] at this
  have d0 : Module.finrank ℚ_[l] (V l X 0) ≤ 1 := by
    by_cases hpt : Nonempty (Pt p)
    · obtain ⟨y0⟩ := hpt
      have hcon : ConnectedSpace X :=
        connectedSpace_iff_univ.2 (IrreducibleSpace.isIrreducible_univ _).isConnected
      have inj : Function.Injective (pb l y0.1 0) := by
        rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
        intro z hz
        apply L.pts p hprop z
        intro y
        rw [L.conn p hprop hcon z y y0, hz]
      have hsurj : Function.Surjective (LinearMap.toSpanSingleton ℚ_[l] _ (oneV l (S k))) := by
        intro w
        obtain ⟨r, hr, -⟩ := L.line w
        exact ⟨r, hr.symm⟩
      haveI : Module.Finite ℚ_[l] (V l (S k) 0) := Module.Finite.of_surjective _ hsurj
      calc Module.finrank ℚ_[l] (V l X 0) ≤ Module.finrank ℚ_[l] (V l (S k) 0) :=
            LinearMap.finrank_le_finrank_of_injective inj
        _ ≤ 1 := finrank_le_one (oneV l (S k)) (fun w => (L.line w).exists.imp fun r hr => hr.symm)
    · have hz : ∀ z : V l X 0, z = 0 := fun z => L.pts p hprop z (fun y => (hpt ⟨y⟩).elim)
      haveI : Subsingleton (V l X 0) := ⟨fun x y => by rw [hz x, hz y]⟩
      simp [Module.finrank_zero_of_subsingleton]
  obtain ⟨x0, hx0⟩ : ∃ x, lam x ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hlam (LinearMap.ext hc)
  have surj : Function.Surjective lam := fun r => ⟨(r / lam x0) • x0, by
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx0]⟩
  haveI := fd (2 * (d : ℤ))
  have hnt : Nontrivial (V l X (2 * (d : ℤ))) := ⟨⟨x0, 0, fun h => hx0 (by rw [h, map_zero])⟩⟩
  have d2 : Module.finrank ℚ_[l] (V l X (2 * (d : ℤ))) = Module.finrank ℚ_[l] ℚ_[l] := by
    rw [Module.finrank_self]
    have h1 := (le 0 (2 * (d : ℤ)) (zero_add _)).trans d0
    have h2 := Module.finrank_pos (R := ℚ_[l]) (M := V l X (2 * (d : ℤ)))
    omega
  have inj : Function.Injective lam := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank d2).2 surj
  refine ⟨fd, van, LinearEquiv.ofBijective lam ⟨inj, surj⟩, fun n m h => ?_⟩
  have htr : ((LinearEquiv.ofBijective lam ⟨inj, surj⟩ : V l X (2 * (d : ℤ)) ≃ₗ[ℚ_[l]] ℚ_[l]) :
      V l X (2 * (d : ℤ)) →ₗ[ℚ_[l]] ℚ_[l]) = lam := LinearMap.ext fun x => rfl
  rw [htr]
  haveI := fd n
  haveI := fd m
  have injf : Function.Injective ((cupV l X h).compr₂ lam).flip := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    exact nd n m h y (fun x => by simpa using LinearMap.congr_fun hy x)
  have heq : Module.finrank ℚ_[l] (V l X m) = Module.finrank ℚ_[l] (V l X n →ₗ[ℚ_[l]] ℚ_[l]) := by
    rw [Subspace.dual_finrank_eq]
    exact le_antisymm (le n m h) (le m n (by omega))
  exact ⟨injf, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).1 injf⟩
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.PPnCls
section -- merged from Development.EtaleCohomology.EtaleTrace.LEmptyPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace.LEmptyPf

theorem sec_subsingleton {R : Type} [CommRing R] (X : Scheme.{0}) [IsEmpty X] (F : Shv R) :
    Subsingleton (Sec F X) := by
  have ht : IsTerminal (F.obj.obj (Opposite.op X)) :=
    Sheaf.isTerminalOfBotCover F X (by exact Scheme.bot_mem_grothendieckTopology X)
  have hz : IsZero (F.obj.obj (Opposite.op X)) := ht.isZero
  exact ModuleCat.subsingleton_of_isZero hz

theorem pos_zero (a5 : A5) {R : Type} [CommRing R] (X : Scheme.{0}) [IsEmpty X] (F : Shv R) (n : ℤ)
    (hn : 0 < n) (x : H R (sch.obj X) F n) : x = 0 := by
  obtain ⟨Y, f, -, -, hx⟩ := a5 R X F n hn x
  have : IsEmpty Y := Function.isEmpty f.base
  have : IsIso f := isIso_of_isEmpty f
  have h1 : x = pull R (sch.map (inv f)) F n (pull R (sch.map f) F n x) := by
    rw [← pull_comp, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  rw [h1, hx, map_zero]

theorem LEmpty_of : LateralTheory.EtaleTrace.LPdCut.LEmpty := by
  intro a5 a9 R _ X hX F n
  refine ⟨fun a b => ?_⟩
  rcases lt_trichotomy n 0 with h | rfl | h
  · exact ((a9 R F).1 _ n h).elim a b
  · obtain ⟨e, -⟩ := (a9 R F).2
    have := sec_subsingleton X F
    exact (e X).symm.injective (Subsingleton.elim _ _)
  · rw [pos_zero a5 X F n h a, pos_zero a5 X F n h b]

end LateralTheory.EtaleTrace.LEmptyPf
end
end

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.EtaleTrace UpperTheory.Gal.KunnethLefschetz
open scoped TensorProduct DirectSum

namespace UpperTheory.Gal.KunnethLefschetz.PnClsPf

private theorem sm_open {A B C : Scheme.{0}} (i : A ⟶ B) [IsOpenImmersion i] (f : B ⟶ C) (n : ℕ)
    (h : SmoothOfRelativeDimension n f) : SmoothOfRelativeDimension n (i ≫ f) := by
  have := smoothOfRelativeDimension_comp (n := 0) (m := n) i f
  simpa using this

private theorem empty_v (l : ℕ) [Fact l.Prime] (hI : In) (X : Scheme.{0}) (hX : IsEmpty X) (n : ℤ) :
    Subsingleton (V l X n) := by
  have hE := LEmptyPf.LEmpty_of hI.a5 hI.a9
  haveI h1 : ∀ k, Subsingleton (HtL l k (sch.obj X) n 0) := fun k => hE _ X hX _ n
  haveI h2 : Subsingleton (Hl l (sch.obj X) n 0) := by
    show Subsingleton (HlSub l (sch.obj X) n 0)
    infer_instance
  show Subsingleton (ℚ_[l] ⊗[ℤ_[l]] Hl l (sch.obj X) n 0)
  infer_instance

private theorem iso_sub {A B : Scheme.{0}} (e : A ≅ B) (q : ℕ) (n : ℤ)
    (h : Subsingleton (Ht q (sch.obj B) n 0)) : Subsingleton (Ht q (sch.obj A) n 0) := by
  have key : ∀ z : Ht q (sch.obj A) n 0,
      pull (ZMod q) (sch.map e.hom) (tw q 0) n (pull (ZMod q) (sch.map e.inv) (tw q 0) n z) = z := by
    intro z
    rw [← pull_comp, ← CategoryTheory.Functor.map_comp, e.hom_inv_id,
      CategoryTheory.Functor.map_id, pull_id]
  constructor
  intro x y
  rw [← key x, ← key y,
    Subsingleton.elim (pull (ZMod q) (sch.map e.inv) (tw q 0) n x)
      (pull (ZMod q) (sch.map e.inv) (tw q 0) n y)]

end UpperTheory.Gal.KunnethLefschetz.PnClsPf

open UpperTheory.Gal.KunnethLefschetz.PnClsPf in
theorem UpperTheory.Gal.KunnethLefschetz.pnCls_holds :
    UpperTheory.Gal.KunnethLefschetz.PnCls := by
  intro hI hF hH hO l _ k _ _ hl hR hL hA hG
  obtain ⟨gq⟩ := hG
  have one_ne : oneV l (S k) ≠ 0 := by
    intro h0
    obtain ⟨r, -, hr⟩ := Low.line hL 0
    have h1 := hr 0 (by simp)
    have h2 := hr 1 (by simp [h0])
    exact one_ne_zero (h2.trans h1.symm)
  have key : ∀ d : ℕ, ∃ t : Pt (PNto k d), IsClosedImmersion t.1 ∧
      ∃ U : (PN k d).Opens, Off t.1 U ∧
        ∃ z : V l (PN k d) (2 * (d : ℤ)), z ≠ 0 ∧ pb l U.ι (2 * (d : ℤ)) z = 0 := by
    intro d
    induction d with
    | zero =>
      haveI := (hF k 0).2.2.2
      refine ⟨⟨inv (PNto k 0), IsIso.inv_hom_id _⟩, inferInstance, ⊥, ?_, ?_⟩
      · show ((⊥ : (PN k 0).Opens) : Set (PN k 0)) = (Set.range (inv (PNto k 0)).base)ᶜ
        rw [Set.range_eq_univ.mpr (ConcreteCategory.bijective_of_isIso (inv (PNto k 0)).base).2]
        simp
      · refine ⟨oneV l (PN k 0), ?_, ?_⟩
        · intro h0
          apply one_ne
          have hu := Ring.one_nat hR (inv (PNto k 0))
            (LPdCut.unit_of (PNto k 0) (isUnit_iff_ne_zero.mpr hl))
          rw [← hu]
          change pb l (inv (PNto k 0)) 0 (oneV l (PN k 0)) = 0
          rw [h0, map_zero]
        · have he : IsEmpty ((⊥ : (PN k 0).Opens) : Scheme) := ⟨fun x => by simpa using x.2⟩
          haveI := empty_v l hI ((⊥ : (PN k 0).Opens) : Scheme) he (2 * ((0 : ℕ) : ℤ))
          exact Subsingleton.elim _ _
    | succ d ih =>
      obtain ⟨t, htc, U, hU, z, hz, hzU⟩ := ih
      obtain ⟨ι, U0, hιc, hιp, hoff0, ⟨eU0⟩⟩ := hH k d
      haveI := htc
      haveI := hιc
      let t' : Pt (PNto k (d + 1)) := Pt.map ι hιp t
      have htc' : IsClosedImmersion t'.1 := by
        show IsClosedImmersion (t.1 ≫ ι)
        infer_instance
      obtain ⟨U', hU'⟩ := hO.1 t'.1 htc'
      have hP : IsPair 1 d (PNto k (d + 1)) ι :=
        ⟨hιc, (hF k (d + 1)).1.2, by rw [hιp]; exact (hF k d).1.2⟩
      have hn : 2 * (d : ℤ) + 2 * ((1 : ℕ) : ℤ) = 2 * ((d + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      refine ⟨t', htc', U', hU', gq.g hP hn z, ?_, ?_⟩
      · intro h0
        apply hz
        have hinj := gq.inj hP hn U0 hoff0 (fun j =>
          iso_sub eU0 (l ^ j) _ (hA j (d + 1) _ (by push_cast; omega)))
        apply hinj
        rw [h0, map_zero]
      · have hinj : Function.Injective ι.base := ι.isClosedEmbedding.injective
        have hVU : ι ⁻¹ᵁ U' = U := by
          apply TopologicalSpace.Opens.ext
          rw [hU]
          show ι.base ⁻¹' (U' : Set (PN k (d + 1))) = _
          rw [hU']
          ext x
          simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_range, t', Pt.map]
          constructor
          · rintro h ⟨y, rfl⟩
            exact h ⟨y, rfl⟩
          · rintro h ⟨y, hy⟩
            apply h
            refine ⟨y, hinj ?_⟩
            rw [← hy]
            rfl
        subst hVU
        have hP' : IsPair 1 d (U'.ι ≫ PNto k (d + 1)) (ι ∣_ U') := by
          refine ⟨inferInstance, sm_open U'.ι _ _ (hF k (d + 1)).1.2, ?_⟩
          rw [← Category.assoc, morphismRestrict_ι, Category.assoc, hιp]
          exact sm_open _ _ _ (hF k d).1.2
        rw [gq.nat hP' hP U'.ι (ι ⁻¹ᵁ U').ι rfl (isPullback_morphismRestrict ι U') hn z, hzU,
          map_zero]
  intro d
  obtain ⟨t, -, U, hU, z, hz, hzU⟩ := key d
  exact ⟨t, U, z, hU, hz, hzU⟩
end
end
