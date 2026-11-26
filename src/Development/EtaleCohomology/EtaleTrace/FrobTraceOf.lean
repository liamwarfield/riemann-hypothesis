module

public import Development.EtaleCohomology.EtaleTrace.LadicH0LocallyConstant
public import Development.EtaleCohomology.KummerTheory.InjSlice

@[expose] public section

section -- merged from Development.EtaleCohomology.EtaleTrace.FrobTraceOf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

theorem lefschetz_of (hB : Base) (hT : LTransfer) (hC : LCycle) (hF : LFix) (hTr : LTr) (hP : LPushPt) (hA : LAlg) :
    Lefschetz := by
  intro l _ k _ _ hl d Y X q p hq hp hpr c a hc ha hfin het hE
  classical
  obtain ⟨δ, hδ⟩ := hC hB l k hl
  obtain ⟨tr, htr⟩ := hTr hB l k hl δ hδ d p hp hpr
  have hproj := (hT hB l k hl p hp.1 a hfin het).2.1
  have h1 := hA hB l k hl δ hδ d q p hp tr htr c a hc ha (tr ∘ₗ push l a _) (fun n => push l a n ∘ₗ pb l c n)
    (fun n m h u v => by simp only [LinearMap.comp_apply]; rw [hproj])
  have hfx := hF k q p hq.1 hp.1 c a hc ha hE
  have hs : Set.Finite {y : Pt q | y.1 ≫ c = y.1 ≫ a} := hfx
  have h2 := hδ.trans d q p hq hp c a hc ha hE hs.toFinset (fun y => by simp)
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← h1, h2, map_sum]
  have h3 : ∀ y : Pt q, (tr ∘ₗ push l a _) (δ.cl d y) = 1 := fun y => by
    rw [LinearMap.comp_apply, hP hB l k hl δ hδ d q p hq hp a ha hfin het y, htr]
  simp only [h3, Finset.sum_const, nsmul_eq_mul, mul_one]
  congr 1
  exact (Nat.card_eq_card_finite_toFinset hs).symm

theorem pb_comp (l : ℕ) [Fact l.Prime] {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (n : ℤ) :
    pb l (f ≫ g) n = pb l f n ∘ₗ pb l g n := by
  unfold pb pullHQ
  rw [Functor.map_comp, pullHl_comp, LinearMap.baseChange_comp]

theorem gal_eq (l : ℕ) [Fact l.Prime] {κ : Type} [Field κ] (Ω : Type) [Field Ω] [Algebra κ Ω] {X : Scheme.{0}} (p : X ⟶ S κ)
    (n : ℤ) (σ : Ω ≃ₐ[κ] Ω) : galHQ l Ω p n 0 σ = pb l (GlobalTheory.Et.galMap Ω p σ) n := rfl

theorem pb_frob (l : ℕ) [Fact l.Prime] {κ : Type} [Field κ] (Ω : Type) [Field Ω] [Algebra κ Ω] {X W : Scheme.{0}} (p : X ⟶ S κ)
    (n : ℤ) (σ : Ω ≃ₐ[κ] Ω) (c b : W ⟶ GlobalTheory.Et.geom Ω p) (F : GlobalTheory.Et.geom Ω p ⟶ GlobalTheory.Et.geom Ω p)
    (h : c ≫ GlobalTheory.Et.galMap Ω p σ = b ≫ F) (hid : pb l F n = LinearMap.id) :
    pb l b n ∘ₗ galHQ l Ω p n 0 σ⁻¹ = pb l c n := by
  have h1 : pb l b n = pb l c n ∘ₗ pb l (GlobalTheory.Et.galMap Ω p σ) n :=
    calc pb l b n = pb l b n ∘ₗ pb l F n := by rw [hid, LinearMap.comp_id]
      _ = pb l (c ≫ GlobalTheory.Et.galMap Ω p σ) n := by rw [h]; exact (pb_comp l b F n).symm
      _ = _ := pb_comp l c _ n
  have h2 : pb l (GlobalTheory.Et.galMap Ω p σ) n ∘ₗ pb l (GlobalTheory.Et.galMap Ω p σ⁻¹) n = LinearMap.id := by
    refine (pb_comp l _ _ n).symm.trans ?_
    rw [← galMap_mul, mul_inv_cancel, galMap_one]
    unfold pb pullHQ
    rw [CategoryTheory.Functor.map_id, pullHl_id, LinearMap.baseChange_id]
  rw [gal_eq, h1, LinearMap.comp_assoc, h2, LinearMap.comp_id]

theorem frobTrace_of (hB : Base) (hL : Lefschetz) (hI : LFrobId) (hG : LFrobGeom) : FrobTrace := by
  intro l _ κ Ω _ _ _ _ _ hl d Y X q p hq hp hpr a b ha hb hfin het r hr σ hσ
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed κ
  have hlΩ : (l : Ω) ≠ 0 := fun h => hl ((algebraMap κ Ω).injective (by rw [map_natCast, h, map_zero]))
  obtain ⟨hq', hp', hpr', ha', hfin', het', c, F, hc, hF, hcF, hE, hcard⟩ :=
    hG κ Ω d q p hq hp hpr a b ha hb hfin het r hr σ hσ _ _ rfl rfl
  have key := hL l Ω hlΩ d _ _ hq' hp' hpr' c _ hc ha' hfin' het' hE
  refine Eq.trans ?_ (key.trans (congrArg _ hcard))
  have := Fintype.ofFinite κ
  obtain ⟨p₀, hp₀⟩ := CharP.exists κ
  obtain ⟨s, hs, hcd⟩ := FiniteField.card κ p₀
  have : Fact p₀.Prime := ⟨hs⟩
  have : CharP Ω p₀ := charP_of_injective_algebraMap (algebraMap κ Ω).injective p₀
  rw [Nat.card_eq_fintype_card, hcd, ← pow_mul] at hF
  have hid := hI hB l Ω p₀ hlΩ (pullback.snd _ _) _ F hF
  exact congrArg (altTr l _ d) (funext fun n => congrArg (push l _ n ∘ₗ ·) (pb_frob l Ω p n σ c _ F hcF (hid n)))

theorem goal_of (hFin : LFin) (_ : LRing) (hT : LTransfer) (_ : LadicH0LocallyConstant) (_ : LKunneth) (hC : LCycle) (_ : LPd) (_ : LCover)
    (_ : LInj) (_ : LConst) (hF : LFix) (hTr : LTr) (hP : LPushPt) (hA : LAlg) (hI : LFrobId) (hG : LFrobGeom) : Goal :=
  fun hB => ⟨hFin hB, hT hB, lefschetz_of hB hT hC hF hTr hP hA,
    frobTrace_of hB (lefschetz_of hB hT hC hF hTr hP hA) hI hG⟩

end LateralTheory.EtaleTrace

end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.LRingPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleTrace.LRingPf

section Cast
variable {q : ℕ} {E : Spc}

theorem cast_cast {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'') (h4 : i' = i'') (x : Ht q E n i) :
    Ht.cast h3 h4 (Ht.cast h1 h2 x) = Ht.cast (h1.trans h3) (h2.trans h4) x := by
  subst h1 h2 h3 h4; rfl

theorem cast_add {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x y : Ht q E n i) :
    Ht.cast h1 h2 (x + y) = Ht.cast h1 h2 x + Ht.cast h1 h2 y := by
  subst h1 h2; rfl

theorem cast_nsmul {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (k : ℕ) (x : Ht q E n i) :
    Ht.cast h1 h2 (k • x) = k • Ht.cast h1 h2 x := by
  subst h1 h2; rfl

theorem cast_usmul {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (k : ℤˣ) (x : Ht q E n i) :
    Ht.cast h1 h2 (k • x) = k • Ht.cast h1 h2 x := by
  subst h1 h2; rfl

theorem red_cast (Q q' : ℕ) {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht Q E n i) :
    red Q q' E n' i' (Ht.cast h1 h2 x) = Ht.cast h1 h2 (red Q q' E n i x) := by
  subst h1 h2; rfl

theorem pull_cast {E' : Spc} (f : E ⟶ E') {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') (x : Ht q E' n i) :
    pull _ f _ _ (Ht.cast h1 h2 x) = Ht.cast h1 h2 (pull _ f _ _ x : Ht q E n i) := by
  subst h1 h2; rfl

theorem cup_cast_left {n m i j n' i' : ℤ} (h1 : n = n') (h2 : i = i') (a : Ht q E n i) (b : Ht q E m j) :
    cup q (Ht.cast h1 h2 a) b = Ht.cast (by rw [h1]) (by rw [h2]) (cup q a b) := by
  subst h1 h2; rfl

theorem cup_cast_right {n m i j m' j' : ℤ} (h1 : m = m') (h2 : j = j') (a : Ht q E n i) (b : Ht q E m j) :
    cup q a (Ht.cast h1 h2 b) = Ht.cast (by rw [h1]) (by rw [h2]) (cup q a b) := by
  subst h1 h2; rfl

end Cast

section BC
variable {R A M N P : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

def bc (B : M →ₗ[R] N →ₗ[R] P) : A ⊗[R] M →ₗ[A] A ⊗[R] N →ₗ[A] A ⊗[R] P :=
  TensorProduct.curry ((TensorProduct.lift B).baseChange A ∘ₗ
    (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap)

theorem bc_tmul (B : M →ₗ[R] N →ₗ[R] P) (a a' : A) (x : M) (y : N) :
    bc B (a ⊗ₜ x) (a' ⊗ₜ y) = (a * a') ⊗ₜ B x y := by
  simp [bc, TensorProduct.AlgebraTensorModule.distribBaseChange_symm_tmul]

theorem tmul_eq (a : A) (x : M) : (a ⊗ₜ[R] x : A ⊗[R] M) = a • ((1 : A) ⊗ₜ x) := by
  rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end BC

end LateralTheory.EtaleTrace.LRingPf

namespace LateralTheory.EtaleTrace.LRingPf

section SlopeTestRemainingChoices
variable {q : ℕ} {E : Spc} {n m r : ℤ} (h : n + m = r)

theorem cc_add_left (a a' : Ht q E n 0) (b : Ht q E m 0) :
    Ht.cast h (add_zero 0) (cup q (a + a') b) = Ht.cast h (add_zero 0) (cup q a b) + Ht.cast h (add_zero 0) (cup q a' b) := by
  rw [map_add (f := _), AddMonoidHom.add_apply, cast_add]

theorem cc_add_right (a : Ht q E n 0) (b b' : Ht q E m 0) :
    Ht.cast h (add_zero 0) (cup q a (b + b')) = Ht.cast h (add_zero 0) (cup q a b) + Ht.cast h (add_zero 0) (cup q a b') := by
  rw [map_add (f := _), cast_add]

theorem zsmul_nat [NeZero q] (z : ZMod q) {n i : ℤ} (a : Ht q E n i) : z • a = z.val • a := by
  conv_lhs => rw [← ZMod.natCast_zmod_val z]
  exact Nat.cast_smul_eq_nsmul (ZMod q) z.val a

theorem cc_smul_left [NeZero q] (z : ZMod q) (a : Ht q E n 0) (b : Ht q E m 0) :
    Ht.cast h (add_zero 0) (cup q (z • a) b) = z • Ht.cast h (add_zero 0) (cup q a b) := by
  rw [zsmul_nat, zsmul_nat, map_nsmul, AddMonoidHom.nsmul_apply, cast_nsmul]

theorem cc_smul_right [NeZero q] (z : ZMod q) (a : Ht q E n 0) (b : Ht q E m 0) :
    Ht.cast h (add_zero 0) (cup q a (z • b)) = z • Ht.cast h (add_zero 0) (cup q a b) := by
  rw [zsmul_nat, zsmul_nat, map_nsmul, cast_nsmul]

theorem red_cc (hB : A11) (Q : ℕ) [NeZero Q] (hd : q ∣ Q) (a : Ht Q E n 0) (b : Ht Q E m 0) :
    red Q q E r 0 (Ht.cast h (add_zero 0) (cup Q a b)) =
      Ht.cast h (add_zero 0) (cup q (red Q q E n 0 a) (red Q q E m 0 b)) := by
  rw [red_cast, (hB Q q hd E).1 a b]

end SlopeTestRemainingChoices

section Adic
variable (l : ℕ) [Fact l.Prime]

instance nz (j : ℕ) : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩

omit [Fact l.Prime] in
theorem dvd_succ (j : ℕ) : l ^ j ∣ l ^ (j + 1) := pow_dvd_pow l (Nat.le_succ j)

variable (E : Spc) {n m r : ℤ} (h : n + m = r)

def cupF (x : Hl l E n 0) (y : Hl l E m 0) : ∀ j, HtL l j E r 0 := fun j =>
  Ht.cast h (add_zero 0) (cup (l ^ j) (show Ht (l ^ j) E n 0 from x.1 j) (show Ht (l ^ j) E m 0 from y.1 j))

theorem cupF_mem (hB : A11) (x : Hl l E n 0) (y : Hl l E m 0) : cupF l E h x y ∈ HlSub l E r 0 := by
  intro j
  have hx := x.2 j
  have hy := y.2 j
  exact (red_cc h hB _ (dvd_succ l j) (x.1 (j + 1)) (y.1 (j + 1))).trans <| congrArg₂ (fun a b => Ht.cast h (add_zero 0) (cup (l ^ j) a b)) hx hy

def cupL (hB : A11) : Hl l E n 0 →ₗ[ℤ_[l]] Hl l E m 0 →ₗ[ℤ_[l]] Hl l E r 0 :=
  LinearMap.mk₂ ℤ_[l] (fun x y => ⟨cupF l E h x y, cupF_mem l E h hB x y⟩)
    (fun x x' y => Subtype.ext (funext fun j => cc_add_left h (x.1 j) (x'.1 j) (y.1 j)))
    (fun c x y => Subtype.ext (funext fun j => cc_smul_left h (PadicInt.toZModPow j c) (x.1 j) (y.1 j)))
    (fun x y y' => Subtype.ext (funext fun j => cc_add_right h (x.1 j) (y.1 j) (y'.1 j)))
    (fun c x y => Subtype.ext (funext fun j => cc_smul_right h (PadicInt.toZModPow j c) (x.1 j) (y.1 j)))

theorem cupL_apply (hB : A11) (x : Hl l E n 0) (y : Hl l E m 0) (j : ℕ) :
    (cupL l E h hB x y).1 j = Ht.cast h (add_zero 0) (cup (l ^ j) (show Ht (l ^ j) E n 0 from x.1 j)
      (show Ht (l ^ j) E m 0 from y.1 j)) := rfl

end Adic

end LateralTheory.EtaleTrace.LRingPf

namespace LateralTheory.EtaleTrace.LRingPf

section Ext
variable {R A M N P : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module A P]

theorem ext1 {f g : A ⊗[R] M →ₗ[A] P} (H : ∀ x, f ((1 : A) ⊗ₜ x) = g ((1 : A) ⊗ₜ x)) : f = g := by
  apply LinearMap.ext; intro u
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [tmul_eq, map_smul, map_smul, H]
  | add u u' hu hu' => rw [map_add (f := _), map_add (f := _), hu, hu']

theorem ext2 {f g : A ⊗[R] M →ₗ[A] A ⊗[R] N →ₗ[A] P}
    (H : ∀ x y, f ((1 : A) ⊗ₜ x) ((1 : A) ⊗ₜ y) = g ((1 : A) ⊗ₜ x) ((1 : A) ⊗ₜ y)) : f = g := by
  apply LinearMap.ext; intro u
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rw [tmul_eq, map_smul, map_smul]; congr 1; exact ext1 (H x)
  | add u u' hu hu' => rw [map_add (f := _), map_add (f := _), hu, hu']

end Ext

section Aux2
variable {q : ℕ} {E E' : Spc} {n m r : ℤ} (h : n + m = r)

theorem pull_cc (h6 : DivisorNaturality) [NeZero q] (f : E ⟶ E') (a : Ht q E' n 0) (b : Ht q E' m 0) :
    pull _ f _ _ (Ht.cast h (add_zero 0) (cup q a b)) = Ht.cast h (add_zero 0) (cup q (pull _ f _ _ a) (pull _ f _ _ b)) := by
  rw [pull_cast, (h6 q).1 f a b]

theorem one_cc (h6 : DivisorRingCompatibility) [NeZero q] (hi : GlobalTheory.EtC.Inv q E) (a : Ht q E n 0) :
    Ht.cast (zero_add n) (add_zero 0) (cup q (one q E) a) = a := by
  rw [(h6 q E).1 hi a, cast_cast]; rfl

theorem assoc_cc (h6 : DivisorRingCompatibility) [NeZero q] {k s t w : ℤ} (h1 : n + m = s) (h2 : s + k = w) (h3 : m + k = t) (h4 : n + t = w)
    (a : Ht q E n 0) (b : Ht q E m 0) (c : Ht q E k 0) :
    Ht.cast h2 (add_zero 0) (cup q (Ht.cast h1 (add_zero 0) (cup q a b)) c) =
      Ht.cast h4 (add_zero 0) (cup q a (Ht.cast h3 (add_zero 0) (cup q b c))) := by
  rw [cup_cast_left, cup_cast_right, cast_cast, cast_cast, (h6 q E).2.1 a b c, cast_cast]

theorem comm_cc (h6 : DivisorRingCompatibility) [NeZero q] (h' : m + n = r) (a : Ht q E n 0) (b : Ht q E m 0) :
    Ht.cast h (add_zero 0) (cup q a b) = ((n * m).negOnePow : ℤ) • Ht.cast h' (add_zero 0) (cup q b a) := by
  rw [(h6 q E).2.2 a b, cast_usmul, cast_cast, Units.smul_def]

end Aux2

section V
variable (l : ℕ) [Fact l.Prime]

def cupQ (h11 : A11) (X : Scheme.{0}) {n m r : ℤ} (h : n + m = r) : V l X n →ₗ[ℚ_[l]] V l X m →ₗ[ℚ_[l]] V l X r :=
  bc (cupL l (sch.obj X) h h11)

theorem cupQ_tmul (h11 : A11) (X : Scheme.{0}) {n m r : ℤ} (h : n + m = r) (x : Hl l (sch.obj X) n 0) (y : Hl l (sch.obj X) m 0) :
    cupQ l h11 X h ((1 : ℚ_[l]) ⊗ₜ x) ((1 : ℚ_[l]) ⊗ₜ y) = (1 : ℚ_[l]) ⊗ₜ cupL l (sch.obj X) h h11 x y := by
  rw [cupQ, bc_tmul, mul_one]

theorem isCup_cupQ (h11 : A11) (X : Scheme.{0}) {n m r : ℤ} (h : n + m = r) : IsCup l X h (cupQ l h11 X h) := by
  intro x y z hz
  rw [cupQ_tmul]
  congr 1
  exact Subtype.ext (funext fun j => (hz j).symm)

theorem cupV_eq (h11 : A11) (X : Scheme.{0}) {n m r : ℤ} (h : n + m = r) : cupV l X h = cupQ l h11 X h := by
  have hs : IsCup l X h (cupV l X h) := pick_spec ⟨_, isCup_cupQ l h11 X h⟩
  apply ext2
  intro x y
  rw [hs x y (cupL l (sch.obj X) h h11 x y) (fun j => rfl), cupQ_tmul]

theorem pb_tmul {Y X : Scheme.{0}} (f : Y ⟶ X) (n : ℤ) (x : Hl l (sch.obj X) n 0) :
    pb l f n ((1 : ℚ_[l]) ⊗ₜ x) = (1 : ℚ_[l]) ⊗ₜ pullHl l (sch.map f) n 0 x := by
  simp [pb, pullHQ, LinearMap.baseChange_tmul]

theorem inv_of (X : Scheme.{0}) (hl : IsUnit (l : Γ(X, ⊤))) (j : ℕ) : GlobalTheory.EtC.Inv (l ^ j) (sch.obj X) := by
  intro U hU
  obtain ⟨y⟩ := hU
  let y' : U ⟶ X := y
  rw [Nat.cast_pow]
  apply IsUnit.pow
  simpa using hl.map y'.appTop.hom

theorem unit_pull {Y X : Scheme.{0}} (f : Y ⟶ X) (hl : IsUnit (l : Γ(X, ⊤))) : IsUnit (l : Γ(Y, ⊤)) := by
  simpa using hl.map f.appTop.hom

def z0 (h11 : A11) (X : Scheme.{0}) (hl : IsUnit (l : Γ(X, ⊤))) : Hl l (sch.obj X) 0 0 :=
  ⟨fun j => one (l ^ j) (sch.obj X), fun j => ((h11 _ _ (dvd_succ l j) _).2.1 (inv_of l X hl (j + 1))).1⟩

theorem oneV_eq (h11 : A11) (X : Scheme.{0}) (hl : IsUnit (l : Γ(X, ⊤))) : oneV l X = (1 : ℚ_[l]) ⊗ₜ z0 l h11 X hl := by
  have hs := pick_spec (P := fun c : V l X 0 => ∀ z : Hl l (sch.obj X) 0 0, (∀ j, z.1 j = one (l ^ j) (sch.obj X)) →
    c = 1 ⊗ₜ z) ⟨(1 : ℚ_[l]) ⊗ₜ z0 l h11 X hl, fun z hz => by
      congr 1; exact Subtype.ext (funext fun j => (hz j).symm)⟩
  exact hs _ (fun j => rfl)

end V

end LateralTheory.EtaleTrace.LRingPf

namespace LateralTheory.EtaleTrace

end LateralTheory.EtaleTrace
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.LCoverCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MvPolynomial
attribute [local instance] MvPolynomial.gradedAlgebra

namespace LateralTheory.EtaleTrace.Cov

def kHom {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) : k →+* X.functionField :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial).hom

def loc (X : Scheme.{0}) [IsIntegral X] (x : X) : Subring X.functionField :=
  (algebraMap (X.presheaf.stalk x) X.functionField).range

def jet (k : Type) [Field k] {K : Type} [Field K] [Algebra k K] {n : ℕ} (v : Fin n → K) (j : Fin n) : K × Ω[K⁄k] :=
  (v j, KaehlerDifferential.D k K (v j))

def Gen {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) {N : ℕ} (ι : X ⟶ PN k N)
    (v : Fin (N + 1) → X.functionField) : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (f : MvPolynomial (Fin (N + 1)) k) (hf : f ∈ homogeneousSubmodule (Fin (N + 1)) k n),
    (genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen _ f ↔ eval₂ (kHom p) v f ≠ 0) ∧
    ∀ (m : ℕ) (g : MvPolynomial (Fin (N + 1)) k) (hg : g ∈ homogeneousSubmodule (Fin (N + 1)) k (m • n))
      (h : genericPoint X ∈ ι ⁻¹ᵁ Proj.basicOpen _ f),
      (show X.functionField from X.presheaf.germ _ (genericPoint X) h (ι.app _
        (Proj.awayToSection _ f (HomogeneousLocalization.Away.mk _ hf m g hg)))) * eval₂ (kHom p) v f ^ m =
        eval₂ (kHom p) v g

structure Coord {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) {N : ℕ} (ι : X ⟶ PN k N)
    (v : Fin (N + 1) → X.functionField) : Prop where
  opens : ∀ (n : ℕ), 0 < n → ∀ f : MvPolynomial (Fin (N + 1)) k, f.IsHomogeneous n → ∀ x : X,
    (x ∈ ι ⁻¹ᵁ Proj.basicOpen _ f ↔ eval₂ (kHom p) v f ≠ 0 ∧
      ∀ g : MvPolynomial (Fin (N + 1)) k, g.IsHomogeneous n → eval₂ (kHom p) v g / eval₂ (kHom p) v f ∈ loc X x)
  range : ∀ z : X.functionField, z ∈ (ι.stalkMap (genericPoint X)).hom.range ↔
    ∃ (n : ℕ) (f g : MvPolynomial (Fin (N + 1)) k), f.IsHomogeneous n ∧ g.IsHomogeneous n ∧
      eval₂ (kHom p) v f ≠ 0 ∧ z = eval₂ (kHom p) v g / eval₂ (kHom p) v f

def PNBasic : Prop := ∀ (k : Type) [Field k] (d : ℕ),
  IsIntegral (PN k d) ∧ IsSeparated (PNto k d) ∧ LocallyOfFiniteType (PNto k d)

def GenIn : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N),
  ι ≫ PNto k N = p → ∃ (v : Fin (N + 1) → X.functionField) (i : Fin (N + 1)), v i = 1 ∧ Gen p ι v

def GenOut : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ)
  (w : Fin (N + 1) → X.functionField), (∀ x : X, ∃ i, w i ≠ 0 ∧ ∀ j, w j / w i ∈ loc X x) →
  ∃ π : X ⟶ PN k N, π ≫ PNto k N = p ∧ Gen p π w

def GenUse : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (N : ℕ) (ι : X ⟶ PN k N)
  (v : Fin (N + 1) → X.functionField), Gen p ι v → Coord p ι v

def JetSpan : Prop := ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (n : ℕ) (v : Fin n → K) (i : Fin n), v i = 1 →
  (∀ z : K, ∃ f g : MvPolynomial (Fin n) k, z = aeval v g / aeval v f) →
  Submodule.span K (Set.range (jet k v)) = ⊤ ∧ Algebra.EssFiniteType k K

def TrdegLe : Prop := ∀ (k K : Type) [Field k] [Field K] [Algebra k K] [Algebra.EssFiniteType k K],
  Algebra.trdeg k K ≤ (Module.finrank K Ω[K⁄k] : ℕ)

def HomRel : Prop := ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (d : ℕ), Algebra.trdeg k K ≤ (d : ℕ) →
  ∀ (n : ℕ), d + 1 < n → ∀ v : Fin n → K, ∃ (m : ℕ) (F : MvPolynomial (Fin n) k), F ≠ 0 ∧ F.IsHomogeneous m ∧ aeval v F = 0

def Step : Prop := ∀ (k K : Type) [Field k] [Infinite k] [Field K] [Algebra k K] (n : ℕ) (v : Fin (n + 1) → K)
  (m : ℕ) (F : MvPolynomial (Fin (n + 1)) k), F ≠ 0 → F.IsHomogeneous m → aeval v F = 0 → ¬ LinearIndependent K (jet k v) →
  ∃ w : Fin n → K, (∀ i, w i ∈ Submodule.span k (Set.range v)) ∧
    Submodule.span K (Set.range (jet k w)) = Submodule.span K (Set.range (jet k v)) ∧
    ∀ O : Subring K, IsLocalRing O → (∀ c : k, algebraMap k K c ∈ O) → (∃ i, v i ≠ 0 ∧ ∀ j, v j / v i ∈ O) →
      ∃ i, w i ≠ 0 ∧ ∀ j, v j / w i ∈ O

def Project : Prop := ∀ (k K : Type) [Field k] [Infinite k] [Field K] [Algebra k K] (d : ℕ), Module.finrank K Ω[K⁄k] = d →
  Algebra.trdeg k K ≤ (d : ℕ) → ∀ (n : ℕ) (v : Fin n → K), Submodule.span K (Set.range (jet k v)) = ⊤ →
  ∃ w : Fin (d + 1) → K, (∀ i, w i ∈ Submodule.span k (Set.range v)) ∧
    Submodule.span K (Set.range (jet k w)) = ⊤ ∧ LinearIndependent K (jet k w) ∧
    ∀ O : Subring K, IsLocalRing O → (∀ c : k, algebraMap k K c ∈ O) → (∃ i, v i ≠ 0 ∧ ∀ j, v j / v i ∈ O) →
      ∃ i, w i ≠ 0 ∧ ∀ j, v j / w i ∈ O

def JetIndep : Prop := ∀ (k K : Type) [Field k] [PerfectField k] [Field K] [Algebra k K] (n : ℕ) (w : Fin n → K),
  LinearIndependent K (jet k w) → ∀ (m : ℕ) (F : MvPolynomial (Fin n) k), F.IsHomogeneous m → aeval w F = 0 → F = 0

def JetUnram : Prop := ∀ (k K O : Type) [Field k] [Field K] [Algebra k K] [CommRing O] (φ : O →+* K) (n : ℕ) (w : Fin n → K)
  (i : Fin n), w i ≠ 0 → Submodule.span K (Set.range (jet k w)) = ⊤ → (∀ c : k, algebraMap k K c ∈ φ.range) →
  (∀ j, w j / w i ∈ φ.range) → φ.FormallyUnramified

def FieldDim : Prop := ∀ (k : Type) [Field k] (d : ℕ) {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k),
  SmoothOfRelativeDimension d p → letI := (kHom p).toAlgebra; Module.finrank X.functionField Ω[X.functionField⁄k] = d

def FinSurj : Prop := ∀ (k : Type) [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k), IsProper p →
  ∀ (N d : ℕ) (ι : X ⟶ PN k N) (π : X ⟶ PN k d) (v : Fin (N + 1) → X.functionField) (w : Fin (d + 1) → X.functionField),
  IsClosedImmersion ι → π ≫ PNto k d = p → Coord p ι v → Coord p π w →
  (∀ i, ∃ c : Fin (N + 1) → k, w i = ∑ j, kHom p (c j) * v j) →
  (∀ x : X, ∃ i, w i ≠ 0 ∧ ∀ j, v j / w i ∈ loc X x) →
  (∀ (m : ℕ) (F : MvPolynomial (Fin (d + 1)) k), F.IsHomogeneous m → eval₂ (kHom p) w F = 0 → F = 0) →
  IsFinite π ∧ Surjective π

def Fibre : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X P : Scheme.{0}} [IsIntegral X] [IsIntegral P] (p : X ⟶ S k)
  (r : P ⟶ S k) (π : X ⟶ P), π ≫ r = p → LocallyOfFiniteType r → IsFinite π → Surjective π →
  (π.stalkMap (genericPoint X)).hom.FormallyUnramified → ∃ t : Pt r, Etale (equalizer.ι π (p ≫ t.1) ≫ p)

theorem kHom_mem_loc {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ S k) (x : X) (c : k) :
    kHom p c ∈ loc X x := by
  refine ⟨X.presheaf.germ ⊤ x trivial (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of k)).inv c)), ?_⟩
  exact X.presheaf.germ_stalkSpecializes_apply _ _ _

theorem loc_local (X : Scheme.{0}) [IsIntegral X] (x : X) : IsLocalRing (loc X x) :=
  IsLocalRing.of_surjective' (algebraMap (X.presheaf.stalk x) X.functionField).rangeRestrict
    (RingHom.rangeRestrict_surjective _)

theorem goal_of (h1 : PNBasic) (h2 : GenIn) (h3 : GenOut) (h4 : GenUse) (h5 : JetSpan) (h6 : TrdegLe) (h7 : Project)
    (h8 : JetIndep) (h9 : JetUnram) (h10 : FieldDim) (h11 : FinSurj) (h12 : Fibre) : LCover := by
  intro k _ _ d X p hsp ⟨N, ι, hι, hιp⟩ hX
  let _ : Algebra k X.functionField := (kHom p).toAlgebra
  obtain ⟨v, i₀, hv1, hv⟩ := h2 k p N ι hιp
  have cv := h4 k p N ι v hv
  have hgen : ∀ z : X.functionField, ∃ f g : MvPolynomial (Fin (N + 1)) k, z = aeval v g / aeval v f := by
    intro z
    obtain ⟨n, f, g, -, -, -, h⟩ := (cv.range z).1 (ι.stalkMap_surjective (genericPoint X) z)
    exact ⟨f, g, h⟩
  obtain ⟨hspan, hess⟩ := h5 k X.functionField _ v i₀ hv1 hgen
  have hd := h10 k d p hsp.2
  have htr := h6 k X.functionField
  rw [hd] at htr
  obtain ⟨w, hw1, hw2, hw3, hw4⟩ := h7 k X.functionField d hd htr _ v hspan
  have hfree : ∀ x : X, ∃ i, v i ≠ 0 ∧ ∀ j, v j / v i ∈ loc X x := by
    intro x
    have htop : ⨆ i, Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) = ⊤ := by
      apply Proj.iSup_basicOpen_eq_top' _ _ (fun i => ⟨1, isHomogeneous_X k i⟩)
      rw [eq_top_iff]
      rintro f -
      induction f using MvPolynomial.induction_on with
      | C a => exact Subalgebra.algebraMap_mem _ (⟨C a, isHomogeneous_C _ a⟩ : homogeneousSubmodule (Fin (N + 1)) k 0)
      | add f g hf hg => exact add_mem hf hg
      | mul_X f i hf => exact mul_mem hf (Algebra.subset_adjoin ⟨i, rfl⟩)
    have hx : ι x ∈ ⨆ i, Proj.basicOpen (homogeneousSubmodule (Fin (N + 1)) k) (MvPolynomial.X i) := by
      rw [htop]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
    obtain ⟨a, b⟩ := (cv.opens 1 one_pos _ (isHomogeneous_X k i) x).1 hi
    exact ⟨i, by simpa using a, fun j => by simpa using b _ (isHomogeneous_X k j)⟩
  have hwx : ∀ x : X, ∃ i, w i ≠ 0 ∧ ∀ j, v j / w i ∈ loc X x := fun x =>
    hw4 _ (loc_local X x) (kHom_mem_loc p x) (hfree x)
  have hc : ∀ i, ∃ c : Fin (N + 1) → k, w i = ∑ j, kHom p (c j) * v j := by
    intro i
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).1 (hw1 i)
    exact ⟨c, by rw [← hc]; exact Finset.sum_congr rfl fun j _ => Algebra.smul_def _ _⟩
  have hww : ∀ x : X, ∃ i, w i ≠ 0 ∧ ∀ j, w j / w i ∈ loc X x := by
    intro x
    obtain ⟨i, hi, h⟩ := hwx x
    refine ⟨i, hi, fun j => ?_⟩
    obtain ⟨c, hc⟩ := hc j
    rw [hc, Finset.sum_div]
    exact sum_mem fun l _ => by rw [mul_div_assoc]; exact mul_mem (kHom_mem_loc p x _) (h l)
  obtain ⟨π, hπ, hg⟩ := h3 k p d w hww
  have cw := h4 k p d π w hg
  obtain ⟨hfin, hsurj⟩ := h11 k p hsp.1 N d ι π v w hι hπ cv cw hc hwx (h8 k X.functionField _ w hw3)
  obtain ⟨hint, -, hft⟩ := h1 k d
  obtain ⟨i, hi, -⟩ := hwx (genericPoint X)
  have hun := h9 k X.functionField _ (π.stalkMap (genericPoint X)).hom _ w i hi hw2
    (fun c => (cw.range _).2 ⟨0, 1, C c, isHomogeneous_one _ _, isHomogeneous_C _ c, by simp, by simp; rfl⟩)
    (fun j => (cw.range _).2 ⟨1, MvPolynomial.X i, MvPolynomial.X j, isHomogeneous_X k i, isHomogeneous_X k j,
      by simpa using hi, by simp⟩)
  obtain ⟨t, ht⟩ := h12 k p (PNto k d) π hπ hft hfin hsurj hun
  exact ⟨π, t, hπ, hfin, hsurj, ht⟩

end LateralTheory.EtaleTrace.Cov

end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.H0LimitCoherence
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleTrace.H0LimitCoherence
open LateralTheory.EtaleTrace

variable (l : ℕ) [Fact l.Prime]

def Coh : Subring (∀ m : ℕ, ZMod (l ^ m)) where
  carrier := {x | ∀ a b (h : a ≤ b), ZMod.castHom (pow_dvd_pow l h) (ZMod (l ^ a)) (x b) = x a}
  one_mem' a b h := map_one _
  mul_mem' {u v} hu hv a b h := by simp only [Pi.mul_apply, map_mul]; rw [hu a b h, hv a b h]
  zero_mem' a b h := map_zero _
  add_mem' {u v} hu hv a b h := by simp only [Pi.add_apply, map_add (f := _)]; rw [hu a b h, hv a b h]
  neg_mem' {u} hu a b h := by simp only [Pi.neg_apply, map_neg]; rw [hu a b h]

def toZl : Coh l →+* ℤ_[l] :=
  PadicInt.lift (f := fun a => (Pi.evalRingHom (fun m : ℕ => ZMod (l ^ m)) a).comp (Coh l).subtype)
    (fun a b h => RingHom.ext fun x => x.2 a b h)

theorem toZModPow_toZl (x : Coh l) (m : ℕ) : PadicInt.toZModPow m (toZl l x) = x.1 m :=
  RingHom.congr_fun (PadicInt.lift_spec _ m) x

theorem coh_of_succ (x : ∀ m : ℕ, ZMod (l ^ m))
    (h : ∀ m, ZMod.castHom (pow_dvd_pow l (Nat.le_succ m)) (ZMod (l ^ m)) (x (m + 1)) = x m) : x ∈ Coh l := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => simp [ZMod.castHom_apply, ZMod.cast_id']
  | succ n hn ih => rw [← ih, ← h n, ← RingHom.comp_apply, ZMod.castHom_comp]

theorem tensor_form {M : Type*} [AddCommGroup M] [Module ℤ_[l] M] (z : ℚ_[l] ⊗[ℤ_[l]] M) :
    ∃ (b : ℤ_[l]) (x : M), b ≠ 0 ∧ z = ((b : ℚ_[l]))⁻¹ ⊗ₜ x := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | tmul q m =>
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[l]) q
    refine ⟨b, a • m, nonZeroDivisors.ne_zero hb, ?_⟩
    rw [← TensorProduct.smul_tmul, Algebra.smul_def]
    congr 1
    try simp [div_eq_mul_inv, mul_comm]
  | add z z' ih ih' =>
    obtain ⟨b, x, hb, rfl⟩ := ih
    obtain ⟨b', x', hb', rfl⟩ := ih'
    have h1 : (b : ℚ_[l]) ≠ 0 := by rwa [Ne, PadicInt.coe_eq_zero]
    have h2 : (b' : ℚ_[l]) ≠ 0 := by rwa [Ne, PadicInt.coe_eq_zero]
    refine ⟨b * b', b' • x + b • x', mul_ne_zero hb hb', ?_⟩
    rw [TensorProduct.tmul_add, ← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul, Algebra.smul_def,
      Algebra.smul_def]
    congr 2 <;> simp <;> field_simp

variable {l}

abbrev lv {E : Spc} {n i : ℤ} (x : Hl l E n i) (j : ℕ) : Ht (l ^ j) E n i := x.1 j

theorem rep_of {E : Spc} (ω : Hl l E 0 0)
    (hgen : ∀ j (z : Ht (l ^ j) E 0 0), ∃ a : ℕ, z = a • lv ω j)
    (hord : ∀ j (a : ℕ), a • lv ω j = 0 → l ^ j ∣ a) :
    (∀ x : Hl l E 0 0, ∃ c : ℤ_[l], x = c • ω) ∧ ∀ c : ℤ_[l], c • ω = 0 → c = 0 := by
  have key : ∀ j (s s' : ZMod (l ^ j)), s • lv ω j = s' • lv ω j → s = s' := by
    intro j s s' h
    haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have h0 : (s - s').val • lv ω j = 0 := by
      rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ j)), ZMod.natCast_zmod_val, sub_smul, h, sub_self]
    obtain ⟨t, ht⟩ := hord j _ h0
    have : (((s - s').val : ℕ) : ZMod (l ^ j)) = 0 := by rw [ht, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    rw [ZMod.natCast_zmod_val] at this
    exact sub_eq_zero.1 this
  have gen : ∀ j (z : Ht (l ^ j) E 0 0), ∃ s : ZMod (l ^ j), z = s • lv ω j := by
    intro j z
    obtain ⟨a, ha⟩ := hgen j z
    exact ⟨a, by rw [Nat.cast_smul_eq_nsmul]; exact ha⟩
  have redω : ∀ j (s : ZMod (l ^ (j + 1))), red (l ^ (j + 1)) (l ^ j) E 0 0 (s • lv ω (j + 1)) =
      (ZMod.castHom (pow_dvd_pow l (Nat.le_succ j)) (ZMod (l ^ j)) s) • lv ω j := by
    intro j s
    haveI : NeZero (l ^ (j + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    conv_lhs => rw [← ZMod.natCast_zmod_val s, Nat.cast_smul_eq_nsmul]
    rw [map_nsmul, ZMod.castHom_apply, ZMod.cast_eq_val, Nat.cast_smul_eq_nsmul]
    exact congrArg (s.val • ·) (ω.2 j)
  refine ⟨fun x => ?_, fun c hc => ?_⟩
  · choose s hs using fun j => gen j (lv x j)
    have hc : s ∈ Coh l := coh_of_succ l s fun j => key j _ _ (by
      rw [← redω, ← hs (j + 1), ← hs j]; exact x.2 j)
    refine ⟨toZl l ⟨s, hc⟩, Subtype.ext (funext fun j => ?_)⟩
    haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    change lv x j = (toZl l ⟨s, hc⟩) • (ω.1 j : HtL l j E 0 0)
    rw [HtL.smul_eq l j j le_rfl, toZModPow_toZl]
    change lv x j = (s j).val • lv ω j
    rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ j)), ZMod.natCast_zmod_val]
    exact hs j
  · refine PadicInt.ext_of_toZModPow.mp fun j => ?_
    haveI : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    rw [map_zero]
    refine key j _ _ ?_
    have h1 : (c • ω).1 j = (0 : Hl l E 0 0).1 j := by rw [hc]
    change c • (ω.1 j : HtL l j E 0 0) = 0 at h1
    rw [HtL.smul_eq l j j le_rfl] at h1
    change (PadicInt.toZModPow j c).val • lv ω j = 0 at h1
    rw [← Nat.cast_smul_eq_nsmul (ZMod (l ^ j)), ZMod.natCast_zmod_val] at h1
    rw [h1, zero_smul]

end LateralTheory.EtaleTrace.H0LimitCoherence

namespace LateralTheory.EtaleTrace

end LateralTheory.EtaleTrace
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.EtaleTateTwistSectionsDeterminedByPointsOfProper
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

def EtaleTateTwistSectionsDeterminedByPointsOfProper : Prop := ∀ (l : ℕ) [Fact l.Prime] (k : Type) [Field k] [IsAlgClosed k], (l : k) ≠ 0 → ∀ j : ℕ,
  ∀ {X : Scheme.{0}} (p : X ⟶ S k), IsProper p → ∀ s : Sec (tw (l ^ j) 0) X,
    ((∀ y : Pt p, Sec.res y.1 s = 0) → s = 0) ∧
    (ConnectedSpace X → ∀ y y' : Pt p, Sec.res y.1 s = Sec.res y'.1 s)

end LateralTheory.EtaleTrace
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.LCoprodInjPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

theorem chains_zero (R : Type) [CommRing R] (E : Scheme.{0}) (hZ : IsZero ((free R).obj (yoneda.obj E))) (p : ℤ) :
    IsZero (((chains R).obj (sch.obj E)).X p) := by
  rcases le_or_gt p 0 with h | h
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, p = -(m : ℤ) := ⟨p.natAbs, by omega⟩
    exact hZ.of_iso (chainsXIso R (sch.obj E) m)
  · apply HomologicalComplex.isZero_extend_X
    intro i hi
    have : (ComplexShape.embeddingDownNat).f i = -(i : ℤ) := rfl
    omega

theorem H_sub (R : Type) [CommRing R] (E : Scheme.{0}) (hZ : IsZero ((free R).obj (yoneda.obj E))) (F : Shv R) (n : ℤ) :
    Subsingleton (H R (sch.obj E) F n) := by
  have : Subsingleton (CochainComplex.HomComplex.Cochain ((chains R).obj (sch.obj E)) (res R F) n) :=
    ⟨fun a b => CochainComplex.HomComplex.Cochain.ext _ _ (fun p q _ => (chains_zero R E hZ p).eq_of_src _ _)⟩
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := CochainComplex.HomComplex.CohomologyClass.mk_surjective x
  obtain ⟨b, rfl⟩ := CochainComplex.HomComplex.CohomologyClass.mk_surjective y
  have hab : a = b := Subtype.ext (@Subsingleton.elim _ this _ _)
  rw [hab]

end LateralTheory.EtaleTrace

end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.LTransferCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace LateralTheory.EtaleTrace.Tr

def Splits {Y X W : Scheme.{0}} (a : Y ⟶ X) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)) : Prop :=
  ∃ hs : ∀ j, s j ≫ a = x, IsIso (Sigma.desc (fun j => pullback.lift (s j) (𝟙 W) (by rw [hs j, Category.id_comp])) :
      ∐ (fun _ : Fin m => W) ⟶ pullback a x)

section
variable (R : Type) [CommRing R]

abbrev fr (X : Scheme.{0}) : Shv R := (free R).obj (yoneda.obj X)

abbrev gen {U X : Scheme.{0}} (x : U ⟶ X) : Sec (fr R X) U := freeGen R (yoneda.obj X) U x

def IsTr {Y X : Scheme.{0}} (a : Y ⟶ X) (τ : fr R X ⟶ fr R Y) : Prop :=
  ∀ (W : Scheme.{0}) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)), Splits a x m s →
    Sec.map τ (gen R x) = ∑ j, gen R (s j)

variable {R}

end

def LSpl : Prop := ∀ {Y X W : Scheme.{0}} (a : Y ⟶ X) (x : W ⟶ X) (m : ℕ) (s : Fin m → (W ⟶ Y)), Splits a x m s →
  (∀ (U : Scheme.{0}) (w : U ⟶ W), Splits a (w ≫ x) m (fun j => w ≫ s j)) ∧
  (∀ y : W ⟶ Y, y ≫ a = x → ∀ t : W, ∃ (O : W.Opens) (j : Fin m), t ∈ O ∧ O.ι ≫ y = O.ι ≫ s j) ∧
  (Nonempty W → Function.Injective s)

def LLoc : Prop := ∀ {Y X : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a → ∀ (W : Scheme.{0}) (x : W ⟶ X) (t : W),
  ∃ (U : Scheme.{0}) (g : U ⟶ W) (m : ℕ) (s : Fin m → (U ⟶ Y)), Etale g ∧ t ∈ Set.range g ∧ Splits a (g ≫ x) m s

def LTau : Prop := ∀ (R : Type) [CommRing R] {Y X : Scheme.{0}} (a : Y ⟶ X), IsFinite a → Etale a →
  ∃ τ : fr R X ⟶ fr R Y, IsTr R a τ

section Glue
variable (l : ℕ) [Fact l.Prime]

end Glue

end LateralTheory.EtaleTrace.Tr

end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.LCompDecPf
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.EtaleTrace

def LCompInt : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k), SP d p →
  ConnectedSpace X → IsIntegral X

theorem noeth_components {α : Type*} [TopologicalSpace α] [TopologicalSpace.NoetherianSpace α] :
    Finite (_root_.ConnectedComponents α) ∧ ∀ x : α, IsOpen (connectedComponent x) := by
  classical
  obtain ⟨S, hSf, hSc, hSi, hSu⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible (isClosed_univ (X := α))
  have hin : ∀ x : α, ∃ t ∈ S, x ∈ t := fun x => by
    have : x ∈ ⋃₀ S := hSu ▸ Set.mem_univ x
    simpa using this
  have hsub : ∀ t ∈ S, ∀ z ∈ t, t ⊆ connectedComponent z := fun t ht z hz =>
    (IsIrreducible.isConnected (hSi t ht)).isPreconnected.subset_connectedComponent hz
  refine ⟨?_, fun x => ?_⟩
  · have : Finite S := hSf.to_subtype
    refine Finite.of_surjective (fun t : S => (((IsIrreducible.nonempty (hSi t.1 t.2)).some : α) : _root_.ConnectedComponents α)) ?_
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨t, ht, hxt⟩ := hin x
    refine ⟨⟨t, ht⟩, ConnectedComponents.coe_eq_coe.mpr ?_⟩
    exact connectedComponent_eq (hsub t ht _ (IsIrreducible.nonempty (hSi t ht)).some_mem hxt)
  · have hc : (connectedComponent x)ᶜ = ⋃₀ {t ∈ S | Disjoint t (connectedComponent x)} := by
      ext z
      simp only [Set.mem_compl_iff, Set.mem_sUnion, Set.mem_setOf_eq]
      constructor
      · intro hz
        obtain ⟨t, ht, hzt⟩ := hin z
        refine ⟨t, ⟨ht, Set.disjoint_left.mpr fun w hwt hwx => hz ?_⟩, hzt⟩
        rw [connectedComponent_eq hwx]; exact hsub t ht w hwt hzt
      · rintro ⟨t, ⟨_, hd⟩, hzt⟩ hzx
        exact Set.disjoint_left.mp hd hzt hzx
    rw [← isClosed_compl_iff, hc]
    have hfin : ({t ∈ S | Disjoint t (connectedComponent x)}).Finite := hSf.subset (Set.sep_subset _ _)
    rw [Set.sUnion_eq_biUnion]
    exact hfin.isClosed_biUnion fun t ht => hSc t ht.1

theorem comp_fin {k : Type} [Field k] (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) :
    Finite (_root_.ConnectedComponents X) ∧ ∀ x : X, IsOpen (connectedComponent x) := by
  have := hp.1; have := hp.2
  have : Smooth p := SmoothOfRelativeDimension.smooth d p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsNoetherian X := {}
  exact noeth_components

theorem clopen_smoothProper_projective {k : Type} [Field k] (d : ℕ) {X : Scheme.{0}} (p : X ⟶ S k) (hp : SP d p) (hX : IsProj p)
    (U : X.Opens) (hU : IsClosed (U : Set X)) : SP d (U.ι ≫ p) ∧ IsProj (U.ι ≫ p) := by
  have : IsClosedImmersion U.ι := .of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hU)
  have := hp.1
  have := hp.2
  have hs := smoothOfRelativeDimension_comp (n := 0) (m := d) U.ι p
  rw [Nat.zero_add] at hs
  refine ⟨⟨inferInstance, hs⟩, ?_⟩
  obtain ⟨N, ι, hι, hιp⟩ := hX
  exact ⟨N, U.ι ≫ ι, inferInstance, by rw [Category.assoc, hιp]⟩

end LateralTheory.EtaleTrace
end
end

section -- merged from Development.EtaleCohomology.EtaleTrace.LKunnethCut
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC
open scoped TensorProduct DirectSum

namespace LateralTheory.EtaleTrace

theorem bilin_ext_one_tmul (l : ℕ) [Fact l.Prime] {M N W : Type 1} [AddCommGroup M] [Module ℤ_[l] M] [AddCommGroup N]
    [Module ℤ_[l] N] [AddCommGroup W] [Module ℚ_[l] W]
    (f g : (ℚ_[l] ⊗[ℤ_[l]] M) ⊗[ℚ_[l]] (ℚ_[l] ⊗[ℤ_[l]] N) →ₗ[ℚ_[l]] W)
    (h : ∀ x y, f ((1 ⊗ₜ x) ⊗ₜ (1 ⊗ₜ y)) = g ((1 ⊗ₜ x) ⊗ₜ (1 ⊗ₜ y))) : f = g := by
  refine TensorProduct.ext' fun u v => ?_
  induction u using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => rw [TensorProduct.add_tmul, map_add (f := _), map_add (f := _), ha, hb]
  | tmul a x =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | add c d hc hd => rw [TensorProduct.tmul_add, map_add (f := _), map_add (f := _), hc, hd]
    | tmul b y =>
      have e1 : (a ⊗ₜ[ℤ_[l]] x : ℚ_[l] ⊗[ℤ_[l]] M) = a • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      have e2 : (b ⊗ₜ[ℤ_[l]] y : ℚ_[l] ⊗[ℤ_[l]] N) = b • ((1 : ℚ_[l]) ⊗ₜ[ℤ_[l]] y) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [e1, e2, TensorProduct.tmul_smul, ← TensorProduct.smul_tmul', map_smul, map_smul, map_smul, map_smul, h]

theorem kun_bijective_of_kunIso (l : ℕ) [Fact l.Prime] {k : Type} [Field k] {X Y : Scheme.{0}} (p : X ⟶ S k) (q : Y ⟶ S k)
    (n : ℤ) (hc : ∀ (a m r : ℤ) (h : a + m = r), IsCup l (pullback p q) h (cupV l (pullback p q) h))
    (hk : LateralTheory.KummerTheory.KunIso l p q n 0) : Function.Bijective (kun l p q n) := by
  obtain ⟨κ, hκ⟩ := hk
  have e : kun l p q n = κ.toLinearMap := by
    refine DirectSum.linearMap_ext _ fun a => ?_
    refine bilin_ext_one_tmul l _ _ fun x y => ?_
    obtain ⟨z, hz, hz'⟩ := hκ a x y
    refine Eq.trans ?_ hz'.symm
    have h1 := hc a (n - a) n (by omega) (pullHl l (sch.map (pullback.fst p q)) a 0 x)
      (pullHl l (sch.map (pullback.snd p q)) (n - a) 0 y) z (fun j => hz j)
    refine Eq.trans ?_ h1
    simp only [kun, LinearMap.comp_apply, DirectSum.toModule_lof, TensorProduct.lift.tmul, LinearMap.compl₁₂_apply]
    rfl
  rw [e]
  exact κ.bijective

end LateralTheory.EtaleTrace

end
end
