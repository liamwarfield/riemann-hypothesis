module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EndoEqOfSections
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGradedVanishing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCrystallineLift
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAvoidOne

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.FormalAlg

variable {X Y : Scheme.{0}}

def chartFn {L : LB X} {d : ℤ} (s : LB.Sec (pw L d)) (i : L.ι) : Γ(X, L.U i) := s.f i

theorem map_prod_eq_pow_mul {A A' B : Type} [CommRing A] [CommRing A'] [CommRing B] (φ : A →+* B)
    (φ' : A' →+* B) {k : ℕ} (x : Fin k → A) (y : Fin k → A') (g : B)
    (h : ∀ l, φ (x l) = g * φ' (y l)) : φ (∏ l, x l) = g ^ k * φ' (∏ l, y l) := by
  rw [map_prod, map_prod, Finset.prod_congr rfl (fun l _ => h l), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

def secMono {L : LB X} {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D) (a : τ → LB.Sec (pw L d))
    (w : Fin k → τ) : LB.Sec (pw L D) where
  f i := ∏ l, chartFn (a (w l)) i
  compat i j := by
    subst h
    have := map_prod_eq_pow_mul (X.presheaf.map (homOfLE (inf_le_left : L.U i ⊓ L.U j ≤ L.U i)).op).hom
      (X.presheaf.map (homOfLE (inf_le_right : L.U i ⊓ L.U j ≤ L.U j)).op).hom
      (fun l => chartFn (a (w l)) i) (fun l => chartFn (a (w l)) j)
      ((L.g i j ^ d : Γ(X, L.U i ⊓ L.U j)ˣ) : Γ(X, L.U i ⊓ L.U j)) (fun l => (a (w l)).compat i j)
    refine this.trans ?_
    congr 1
    rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul]
    rfl

def pullPow {N : LB X} {N' : LB Y} {β : X ⟶ Y} (v : LB.Iso N (N'.pull β)) (t : ℤ) :
    LB.Iso (pw N t) ((pw N' t).pull β) :=
  ⟨fun p => v.s p ^ t⟩

theorem prod_mul_prod_eq {B τ : Type} [CommMonoid B] (φ : τ → B) {k : ℕ} (w₁ w₂ w₃ w₄ : Fin k → τ)
    (hw : Finset.univ.val.map w₁ + Finset.univ.val.map w₂ = Finset.univ.val.map w₃ + Finset.univ.val.map w₄) :
    (∏ l, φ (w₁ l)) * ∏ l, φ (w₂ l) = (∏ l, φ (w₃ l)) * ∏ l, φ (w₄ l) := by
  have key : ∀ w : Fin k → τ, ∏ l, φ (w l) = ((Finset.univ.val.map w).map φ).prod := by
    intro w
    rw [Multiset.map_map]
    rfl
  rw [key, key, key, key, ← Multiset.prod_add, ← Multiset.prod_add, ← Multiset.map_add (f := _), ← Multiset.map_add (f := _), hw]

theorem secMono_mul : ∀ {X : Scheme.{0}} {L : LB X} {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D) (a : τ → LB.Sec (pw L d)) (w₁ w₂ w₃ w₄ : Fin k → τ), (Finset.univ.val.map w₁ + Finset.univ.val.map w₂ = Finset.univ.val.map w₃ + Finset.univ.val.map w₄) → ∀ c, (secMono h a w₁).f c * (secMono h a w₂).f c = (secMono h a w₃).f c * (secMono h a w₄).f c := by
  intro X L τ d D k h a w₁ w₂ w₃ w₄ hw c
  exact prod_mul_prod_eq (fun i => chartFn (a i) (show L.ι from c)) w₁ w₂ w₃ w₄ hw

theorem zpow_mul_inv_eq {G : Type} [CommGroup G] (a a' b b' : G) (t : ℤ) (h : a' = a ^ t) (h' : b' = b ^ t) :
    (a * b⁻¹) ^ t = a' * b'⁻¹ := by
  rw [h, h', mul_zpow, inv_zpow]

theorem mapmap_zpow {G H K : Type} [CommGroup G] [CommGroup H] [CommGroup K] (f : G →* H) (g : H →* K)
    (x : G) (t : ℤ) : g (f (x ^ t)) = (g (f x)) ^ t := by
  rw [map_zpow, map_zpow]

theorem pull_pw_g {Z W : Scheme.{0}} (L : LB W) (φ : Z ⟶ W) (t : ℤ) (i j : PUnit → L.ι) :
    ((pw L t).pull φ).g i j = ((L.pull φ).g i j) ^ t := by
  refine (pull_g (pw L t) φ i j).trans ((mapmap_zpow (pullU φ _) (res _) (L.g _ _) t).trans ?_)
  exact congrArg (· ^ t) (pull_g L φ i j).symm

theorem pullPow_isGen : ∀ {X Y : Scheme.{0}} {N : LB X} {N' : LB Y} {β : X ⟶ Y} (v : LB.Iso N (N'.pull β)) (t : ℤ), v.IsGen → (pullPow v t).IsGen := by
  intro X Y N N' β v t hv p q
  have := congrArg (· ^ t) (hv p q)
  simp only [mul_zpow, ← map_zpow] at this
  refine this.trans ?_
  congr 1
  refine zpow_mul_inv_eq (G := Γ(X, (N'.pull β).U p.1 ⊓ N.U p.2 ⊓ ((N'.pull β).U q.1 ⊓ N.U q.2))ˣ)
    (res _ ((N'.pull β).g p.1 q.1)) (res _ (((pw N' t).pull β).g p.1 q.1)) (res _ (N.g p.2 q.2))
    (res _ ((pw N t).g p.2 q.2)) t ?_ ?_
  · exact (congrArg _ (pull_pw_g N' β t p.1 q.1)).trans (map_zpow _ _ _)
  · exact map_zpow _ _ _

theorem secMaps_secMono : ∀ {X Y : Scheme.{0}} {N : LB X} {N' : LB Y} {β : X ⟶ Y} (v : LB.Iso N (N'.pull β)) {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D) (a : τ → LB.Sec (pw N d)) (a' : τ → LB.Sec (pw N' d)), (∀ i, SecMaps (pullPow v d) (a i) (secPull (a' i) β)) → ∀ w : Fin k → τ, SecMaps (pullPow v D) (secMono h a w) (secPull (secMono h a' w) β) := by
  intro X Y N N' β v τ d D k h a a' hmaps w p
  subst h
  let u : Γ(X, (N'.pull β).U p.1 ⊓ N.U p.2)ˣ := v.s p
  refine (map_prod_eq_pow_mul
    ((resG X (inf_le_left)).comp ((resG X (GlobalTheory.Cartier.pull_U N' β p.1).le).comp (β.app _).hom))
    (resG X inf_le_right) (fun l => chartFn (a' (w l)) (p.1 ⟨⟩)) (fun l => chartFn (a (w l)) p.2)
    (u ^ d).val (fun l => hmaps (w l) p)).trans ?_
  congr 1
  rw [← Units.val_pow_eq_pow_val, ← zpow_natCast, ← zpow_mul]
  rfl

theorem nonzeroLocus_secMono_const : ∀ {X : Scheme.{0}} {L : LB X} {τ : Type} {d D : ℤ} {k : ℕ} (h : d * k = D) (a : τ → LB.Sec (pw L d)) (i : τ), 1 ≤ k → nonzeroLocus (secMono h a (fun _ => i)) = nonzeroLocus (a i) := by
  intro X L τ d D k h a i hk
  refine iSup_congr fun c => ?_
  change X.basicOpen (∏ l : Fin k, chartFn (a i) c) = X.basicOpen (chartFn (a i) c)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact Scheme.basicOpen_pow _ _ (by omega)

end GlobalTheory.CompanionTheory.FormalAlg
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGradedClassRepresentative
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGradedClassRepresentative
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeLocal

theorem loc_coef : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (t : Fin d → Γ(X, W)) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s t E ε → ∀ (σ : ∀ T, E.D ⟶ T) (m : ℕ) (r : ℤ), r = m → m + 1 ≤ s →
    (∀ c : HQ (KS q s {W}) r (r + 1) m, ∃ y : Idx m d → Γ(X, W),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (ε (y I)) u) c) ∧
    ∀ y : Idx m d → Γ(X, W),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (ε (y I)) u) 0 → y = 0 := by
  intro K _ _ X q W d t s E ε hL σ m r hr hs
  obtain ⟨hc, h1, -⟩ := hL
  obtain ⟨PQ, hPQ⟩ := GlobalTheory.T.polynomial_transfer (dividedPowersBot K) q (Ideal.Quotient.mk ⊥) 1 s {W}
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {W})
  have key := GlobalTheory.T.local_graded_vanishing PQ hF E σ hc r (fun r' hr' => (hPQ r' (by omega)).1) m
  obtain ⟨ha, hb⟩ := key.2 0 (by simpa using hr)
  refine ⟨fun c => ?_, fun y hy => ?_⟩
  · obtain ⟨x, -, hx⟩ := ha c
    refine ⟨fun I => ε.symm (x I), ?_⟩
    simpa only [RingEquiv.apply_symm_apply] using hx
  · have h0 : ∀ I, ε (y I) ∈ (sFil (KS q s {W}) ((0 : ℕ) : ℤ)).S E.D := fun I => by
      have e : (sFil (KS q s {W}) ((0 : ℕ) : ℤ)).S E.D = ⊤ := E.D.obj.pdPow_zero
      rw [e]
      trivial
    have := hb (fun I => ε (y I)) h0 hy
    funext I
    have h2 := h1 _ (this I)
    simpa using h2

end GlobalTheory.CompanionTheory.ConeLocal
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGradedClassRepresentativeStatement
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_graded_class_representative : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (t : Fin d → Γ(X, W)) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s t E ε → ∀ (σ : ∀ T, E.D ⟶ T) (m : ℕ) (r : ℤ), r = m → m + 1 ≤ s →
    (∀ c : HQ (KS q s {W}) r (r + 1) m, ∃ y : Idx m d → Γ(X, W),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (ε (y I)) u) c) ∧
    ∀ y : Idx m d → Γ(X, W),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (ε (y I)) u) 0 → y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.loc_coef | exact GlobalTheory.CompanionTheory.ConeLocal.loc_coef | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.loc_coef <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeXD
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT

namespace GlobalTheory.CompanionTheory.KunGlue

universe w

variable {K : Type} [Field K]

structure Idx (c n : ℕ) where
  a : ℕ
  i : ℕ
  a' : ℕ
  j : ℕ
  ha : a + a' = c
  h : i + j = n
  deriving DecidableEq

def KunE {P Q T : ℕ → Cx.{w} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) : Prop :=
  ∀ c n : ℕ, ∃ e : (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) ≃ₗ[K] (T c).H n,
    ∀ (t : Idx c n) (x : (P t.a).X t.i) (y : (Q t.a').X t.j) (hx : (P t.a).d t.i x = 0) (hy : (Q t.a').d t.j y = 0)
      (hz : (T c).d n ((pr t.ha).μ t.h x y) = 0),
      e (DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) t ((P t.a).cls x hx ⊗ₜ (Q t.a').cls y hy)) =
        (T c).cls ((pr t.ha).μ t.h x y) hz

def shD (ς : ℤˣ) (k : ℕ) (C : Cx.{w} K) (n : ℕ) (x : ∀ m : {m : ℕ // m + k = n}, C.X m.1) :
    ∀ m : {m : ℕ // m + k = n + 1}, C.X m.1
  | ⟨0, _⟩ => 0
  | ⟨m + 1, h⟩ => (ς : ℤ) • C.d m (x ⟨m, by omega⟩)

def Sh (ς : ℤˣ) (k : ℕ) (C : Cx.{w} K) : Cx.{w} K where
  X n := ∀ m : {m : ℕ // m + k = n}, C.X m.1
  d n :=
    { toFun := shD ς k C n
      map_add' := fun x y => by
        funext ⟨m, h⟩
        cases m with
        | zero => simp [shD]
        | succ m => simp [shD, smul_add]
      map_smul' := fun r x => by
        funext ⟨m, h⟩
        cases m with
        | zero => simp [shD]
        | succ m => simp [shD, smul_comm r] }
  dd n x := by
    funext ⟨m, h⟩
    cases m with
    | zero => rfl
    | succ m =>
      cases m with
      | zero => simp [shD]
      | succ m => simp [shD, C.dd]

def Dsum {I : Type w} [DecidableEq I] (E : I → Cx.{w} K) : Cx.{w} K where
  X n := ⨁ i, (E i).X n
  d n := DirectSum.lmap fun i => (E i).d n
  dd n x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x => simp [← DirectSum.lof_eq_of K, DirectSum.lmap_lof, (E i).dd]
    | add x y hx hy => simp only [map_add (f := _), hx, hy, add_zero]

variable {ι : Type} [DecidableEq ι]

def Sh.map (ς : ℤˣ) (k : ℕ) {C C' : Cx.{w} K} (f : Cx.Hom C C' (RingHom.id K)) :
    Cx.Hom (Sh ς k C) (Sh ς k C') (RingHom.id K) where
  f n := LinearMap.pi fun m => (f.f m.1).comp (LinearMap.proj m)
  comm n x := by
    funext ⟨m, h⟩
    cases m with
    | zero => exact (map_zero (f.f 0)).symm
    | succ m =>
      change (ς : ℤ) • C'.d m (f.f m (x ⟨m, _⟩)) = f.f (m + 1) ((ς : ℤ) • C.d m (x ⟨m, _⟩))
      rw [f.comm, map_zsmul]

def shSy (ς : ℤˣ) (k : ℕ) (A : Sy.{w} K ι) : Sy.{w} K ι where
  K S := Sh ς k (A.K S)
  res h := Sh.map ς k (A.res h)
  res_id S h n x := funext fun m => A.res_id S h _ _
  res_comp h h' n x := funext fun m => A.res_comp h h' _ _

def Dsum.map {I : Type w} [DecidableEq I] {E E' : I → Cx.{w} K} (f : ∀ i, Cx.Hom (E i) (E' i) (RingHom.id K)) :
    Cx.Hom (Dsum E) (Dsum E') (RingHom.id K) where
  f n := DirectSum.lmap fun i => (f i).f n
  comm n x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      change DirectSum.lmap _ (DirectSum.lmap _ _) = DirectSum.lmap _ (DirectSum.lmap _ _)
      simp [← DirectSum.lof_eq_of K, DirectSum.lmap_lof, (f i).comm]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

def sumSy {I : Type w} [DecidableEq I] (A : I → Sy.{w} K ι) : Sy.{w} K ι where
  K S := Dsum fun i => (A i).K S
  res h := Dsum.map fun i => (A i).res h
  res_id S h n x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      change DirectSum.lmap _ _ = _
      simp [← DirectSum.lof_eq_of K, DirectSum.lmap_lof, (A i).res_id]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  res_comp h h' n x := by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i x =>
      change DirectSum.lmap _ (DirectSum.lmap _ _) = DirectSum.lmap _ _
      simp [← DirectSum.lof_eq_of K, DirectSum.lmap_lof, (A i).res_comp]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

structure XD (K : Type) [Field K] where
  C₁ : Type 1
  [c₁ : Category.{0} C₁]
  C₂ : Type 1
  [c₂ : Category.{0} C₂]
  D : Type 1
  [cD : Category.{0} D]
  F₁ : ℕ → C₁ ⥤ ModuleCat.{0} K
  F₂ : ℕ → C₂ ⥤ ModuleCat.{0} K
  F₃ : ℕ → D ⥤ ModuleCat.{0} K
  L₁ : D ⥤ C₁
  L₂ : D ⥤ C₂
  τ₁ : ∀ (a : ℕ) (T : D), (F₁ a).obj (L₁.obj T) →ₗ[K] (F₃ a).obj T
  τ₂ : ∀ (a : ℕ) (T : D), (F₂ a).obj (L₂.obj T) →ₗ[K] (F₃ a).obj T
  n₁ : ∀ (a : ℕ) {T T' : D} (φ : T ⟶ T') (x : (F₁ a).obj (L₁.obj T)),
    τ₁ a T' (((F₁ a).map (L₁.map φ)).hom x) = ((F₃ a).map φ).hom (τ₁ a T x)
  n₂ : ∀ (a : ℕ) {T T' : D} (φ : T ⟶ T') (x : (F₂ a).obj (L₂.obj T)),
    τ₂ a T' (((F₂ a).map (L₂.map φ)).hom x) = ((F₃ a).map φ).hom (τ₂ a T x)
  μ : ∀ {a a' c : ℕ}, a + a' = c → CH.Pairing (F₃ a) (F₃ a') (F₃ c)

attribute [instance] XD.c₁ XD.c₂ XD.cD

namespace XD

variable (E : XD K)

def m₁ (a : ℕ) : CH.Mor (E.F₁ a) (E.F₃ a) (RingHom.id K) := ⟨E.L₁, E.τ₁ a, E.n₁ a⟩

def m₂ (a : ℕ) : CH.Mor (E.F₂ a) (E.F₃ a) (RingHom.id K) := ⟨E.L₂, E.τ₂ a, E.n₂ a⟩

def μU (U : ObjectProperty E.D) {a a' c : ℕ} (ha : a + a' = c) :
    CH.Pairing (U.ι ⋙ E.F₃ a) (U.ι ⋙ E.F₃ a') (U.ι ⋙ E.F₃ c) :=
  ⟨fun T => (E.μ ha).μ T.obj, fun φ => (E.μ ha).nat φ.hom⟩

def pr (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂) (U₃ : ObjectProperty E.D)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) {a a' c : ℕ} (ha : a + a' = c) :
    CxPairing (CH.cx (U₁.ι ⋙ E.F₁ a)) (CH.cx (U₂.ι ⋙ E.F₂ a')) (CH.cx (U₃.ι ⋙ E.F₃ c)) where
  μ {p q n} h := ((E.μU U₃ ha).cupC h).compl₁₂ ((morU (E.m₁ a) h₁).pullC p) ((morU (E.m₂ a') h₂).pullC q)
  leib {p q n} h x y := by
    simp only [LinearMap.compl₁₂_apply]
    rw [CrystallineSemistableComparison.P.leibniz, (morU (E.m₁ a) h₁).d_pullC, (morU (E.m₂ a') h₂).d_pullC]

end XD

variable {X X' P : Scheme.{0}}

def hodgeXD (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) (p₁ : P ⟶ X) (p₂ : P ⟶ X')
    (hw : p₂ ≫ q' = p₁ ≫ q) : XD K where
  C₁ := Thick (smFun X q)
  C₂ := Thick (smFun X' q')
  D := Thick (smFun P (p₁ ≫ q))
  F₁ a := G q a
  F₂ a := G q' a
  F₃ a := G (p₁ ≫ q) a
  L₁ := (smS p₁ rfl).G
  L₂ := (smS p₂ hw).G
  τ₁ a := (morG p₁ rfl a).τ
  τ₂ a := (morG p₂ hw a).τ
  n₁ a := (morG p₁ rfl a).nat
  n₂ a := (morG p₂ hw a).nat
  μ ha := (grOk (smFun P (p₁ ≫ q)) ha).pair

def swapPr {P Q T : ℕ → Cx.{w} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) {a a' c : ℕ}
    (ha : a + a' = c) : CxPairing (Q a) (P a') (T c) where
  μ {p q n} h := ((-1 : ℤ) ^ (p * q)) • ((pr (show a' + a = c by omega)).μ (show q + p = n by omega)).flip
  leib {p q n} h x y := by
    simp only [LinearMap.smul_apply, LinearMap.flip_apply, map_zsmul]
    rw [(pr (show a' + a = c by omega)).leib (show q + p = n by omega) y x]
    have s1 : ((-1 : ℤ) ^ (p * q) * (-1) ^ q) = (-1) ^ ((p + 1) * q) := by
      rw [← pow_add]
      congr 1
      ring
    have s2 : ((-1 : ℤ) ^ p * (-1) ^ (p * (q + 1))) = (-1) ^ (p * q) := by
      have : p + p * (q + 1) = p * q + 2 * p := by ring
      rw [← pow_add, this, pow_add, pow_mul]
      simp
    simp only [smul_add, smul_smul, s1, s2]
    exact add_comm _ _

def XD.Kun (E : XD K) (U₁ : ObjectProperty E.C₁) (U₂ : ObjectProperty E.C₂) (U₃ : ObjectProperty E.D)
    (h₁ : ∀ T, U₃ T → U₁ (E.L₁.obj T)) (h₂ : ∀ T, U₃ T → U₂ (E.L₂.obj T)) : Prop :=
  KunE (P := fun a => CH.cx (U₁.ι ⋙ E.F₁ a)) (Q := fun a => CH.cx (U₂.ι ⋙ E.F₂ a)) (T := fun a => CH.cx (U₃.ι ⋙ E.F₃ a))
    (fun {a a' c} ha => E.pr U₁ U₂ U₃ h₁ h₂ ha)

def MvE {ι : Type} {I : Type 1} [DecidableEq I] (k : I → ℕ) (A : I → Sy.{1} K ι) (T : Sy.{1} K ι)
    (g : ∀ (u : I) (S : Finset ι) {m n : ℕ}, m + k u = n → ((A u).K S).X m →ₗ[K] (T.K S).X n) (S : Finset ι) (n : ℕ) : Prop :=
  ∃ e : (⨁ v : {v : I × ℕ // v.2 + k v.1 = n}, ((A v.1.1).K S).H v.1.2) ≃ₗ[K] (T.K S).H n,
    ∀ (v : {v : I × ℕ // v.2 + k v.1 = n}) (x : ((A v.1.1).K S).X v.1.2) (hx : ((A v.1.1).K S).d v.1.2 x = 0)
      (hz : (T.K S).d n (g v.1.1 S v.2 x) = 0),
      e (DirectSum.lof K _ (fun v : {v : I × ℕ // v.2 + k v.1 = n} => ((A v.1.1).K S).H v.1.2) v (((A v.1.1).K S).cls x hx)) =
        (T.K S).cls (g v.1.1 S v.2 x) hz

end GlobalTheory.CompanionTheory.KunGlue
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeSeriesSpecialValueRational
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeSeriesSpecialValueRational
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem DL_int_valued {r : ℕ} (g : (Fin r → ℕ) → ℂ) (hg : ∀ m, ∃ z : ℤ, g m = (z : ℂ))
    (cs : List (Fin r)) : ∀ m, ∃ z : ℤ, DL cs g m = (z : ℂ) := by
  induction cs with
  | nil => exact hg
  | cons c cs ih =>
    intro m
    obtain ⟨z1, h1⟩ := ih (m + Pi.single c 1)
    obtain ⟨z2, h2⟩ := ih m
    refine ⟨z1 - z2, ?_⟩
    show DL cs g (m + Pi.single c 1) - DL cs g m = ((z1 - z2 : ℤ) : ℂ)
    rw [h1, h2]
    push_cast
    ring

theorem coneTerm_neg_nat {ι : Type} [Fintype ι] {r : ℕ} (a : ι → Fin r → ℝ) (b : ι → ℝ) (p : ℕ)
    (m : Fin r → ℕ) :
    coneTerm a b (-(p : ℂ)) m = ((∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p : ℝ) : ℂ) := by
  unfold coneTerm
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [neg_neg, Complex.cpow_natCast, Complex.ofReal_pow]

theorem tsum_mem_of_denominator {α : Type} (f : α → ℂ) (K l : ℕ) (hl : 0 < l)
    (hf : ∀ m, ∃ x : ℤ, ((l : ℂ) ^ K) * f m = (x : ℂ)) :
    ∃ (q : ℚ) (z : ℤ), ∑' m, f m = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  have hmem : ((l : ℂ) ^ K) * ∑' m, f m ∈ Set.range (Int.cast : ℤ → ℂ) := by
    by_cases hs : Summable f
    · rw [← tsum_mul_left]
      have hs' : Summable (fun m => (l : ℂ) ^ K * f m) := hs.mul_left _
      apply Complex.isClosed_range_intCast.mem_of_tendsto hs'.hasSum
      refine Filter.Eventually.of_forall (fun S => ?_)
      choose x hx using hf
      exact ⟨∑ b ∈ S, x b, by push_cast; exact Finset.sum_congr rfl (fun b _ => (hx b).symm)⟩
    · rw [tsum_eq_zero_of_not_summable hs, mul_zero]
      exact ⟨0, by simp⟩
  obtain ⟨z, hz⟩ := hmem
  have hlC : ((l : ℂ) ^ K) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.ne')
  have hlQ : ((l : ℚ) ^ K) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hl.ne')
  refine ⟨(z : ℚ) / (l : ℚ) ^ K, z, ?_, ?_⟩
  · push_cast
    rw [hz]
    exact (mul_div_cancel_left₀ (∑' m, f m) hlC).symm
  · rw [mul_div_assoc']
    exact mul_div_cancel_left₀ _ hlQ

theorem value_neg_nat_mem : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (u : (Fin r → ℕ) → ℚ) (cs : List (Fin r)) (p K l : ℕ), 0 < l → (∀ m, ∃ z : ℤ, (l : ℚ) ^ K * u m = z) → (∀ m : Fin r → ℕ, ∃ z : ℤ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (z : ℝ)) → ∃ (q : ℚ) (z : ℤ), ∑' m, (u m : ℂ) * DL cs (coneTerm a b (-(p : ℂ))) m = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  intro ι _ r a b u cs p K l hl hu hprod
  apply tsum_mem_of_denominator _ K l hl
  intro m
  obtain ⟨z2, h2⟩ := DL_int_valued (coneTerm a b (-(p : ℂ))) (fun m' => by
      obtain ⟨z, hz⟩ := hprod m'
      exact ⟨z, by rw [coneTerm_neg_nat, hz, Complex.ofReal_intCast]⟩) cs m
  obtain ⟨z1, h1⟩ := hu m
  refine ⟨z1 * z2, ?_⟩
  rw [h2, ← mul_assoc]
  have h1' : ((l : ℂ) ^ K) * (u m : ℂ) = (z1 : ℂ) := by exact_mod_cast h1
  rw [h1']
  push_cast
  ring

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeSeriesSpecialValueRationalStatement
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_series_special_value_rational : ∀ (ι : Type) [Fintype ι] (r : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (u : (Fin r → ℕ) → ℚ) (cs : List (Fin r)) (p K l : ℕ), 0 < l → (∀ m, ∃ z : ℤ, (l : ℚ) ^ K * u m = z) → (∀ m : Fin r → ℕ, ∃ z : ℤ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (z : ℝ)) → ∃ (q : ℚ) (z : ℤ), ∑' m, (u m : ℂ) * DL cs (coneTerm a b (-(p : ℂ))) m = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.value_neg_nat_mem | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.value_neg_nat_mem | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.value_neg_nat_mem <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FirstChernPullback
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FirstChernPullback

theorem mem_VD_pb {X X' : Scheme.{0}} (D : E.LineData X) (u : X' ⟶ X) {V : X.Opens} (hV : V ∈ 𝒱D D) :
    u ⁻¹ᵁ V ∈ 𝒱D (D.pb u) := by
  obtain ⟨σ, hσ⟩ := hV
  refine ⟨Limits.pullback.lift ((u ∣_ V) ≫ σ) (u ⁻¹ᵁ V).ι ?_, ?_⟩
  · rw [Category.assoc, hσ, morphismRestrict_ι]
  · exact Limits.pullback.lift_snd _ _ _

theorem sSup_preimage {X X' : Scheme.{0}} (𝒲 : Set X.Opens) (u : X' ⟶ X) (h : sSup 𝒲 = ⊤) :
    sSup ((fun V : X.Opens => u ⁻¹ᵁ V) '' 𝒲) = ⊤ := by
  refine top_le_iff.1 fun x _ => ?_
  have hx : u x ∈ sSup 𝒲 := by rw [h]; trivial
  obtain ⟨V, hV, hxV⟩ := TopologicalSpace.Opens.mem_sSup.1 hx
  exact TopologicalSpace.Opens.mem_sSup.2 ⟨_, ⟨V, hV, rfl⟩, hxV⟩

theorem u_congr {X : Scheme.{0}} (D : E.LineData X) {A : CommRingCat.{0}} {a a' b b' : Spec A ⟶ D.Y} (ea : a = a') (eb : b = b')
    (h : a ≫ D.f = b ≫ D.f) (h' : a' ≫ D.f = b' ≫ D.f) :
    (Scheme.ΓSpecIso A).hom.hom (D.u a b h) = (Scheme.ΓSpecIso A).hom.hom (D.u a' b' h') := by
  subst ea eb
  rfl

end GlobalTheory.CompanionTheory.FirstChernPullback


open GlobalTheory.CompanionTheory.FirstChernPullback in
theorem GlobalTheory.CompanionTheory.FirstChernPullback.firstChern_pullback : ∀ {O O' R R' : Type} [CommRing O] [CommRing O'] [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {X X' : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {q' : X' ⟶ Spec (CommRingCat.of O')}
    {κ : O →+* R ⧸ I} {κ' : O' →+* R' ⧸ I'} {σ : R →+* R'} (m : NMor γ q κ γ' q' κ' σ) {p : ℕ}
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (Q₀ : ObjectProperty (Thick (nlFun γ' p X' q' κ'))) (hQ : Used Q₀)
    (h : ∀ T, St Q₀ {⊤} T → Q ((m.mor p).obj T)) (D : E.LineData X) (N : ℕ) (z : HO Q 2) (z' : HO (St Q₀ {⊤}) 2),
    sSup (𝒱D D) = ⊤ → IsFirstChernThickening Q D N z → IsFirstChernThickening (St Q₀ {⊤}) (D.pb m.u) N z' → (m.smor Q (St Q₀ {⊤}) h).o.pull 2 z = z' := by
  intro O O' R R' _ _ _ _ I I' γ γ' X X' q q' κ κ' σ m p Q Q₀ hQ h D N z z' hD hz hz'
  let 𝒱 : Set X'.Opens := (fun V : X.Opens => m.u ⁻¹ᵁ V) '' 𝒱D D
  have h1 : St Q₀ 𝒱 ≤ St Q₀ {⊤} := fun T hT => ⟨hT.1, ⊤, rfl, fun _ _ => trivial⟩
  have hc : ∀ W ∈ ({⊤} : Set X'.Opens), W ≤ sSup 𝒱 := by
    rintro W rfl
    exact (sSup_preimage _ m.u hD).ge
  apply (GlobalTheory.T.cech_refinement_cohomology_bijective Q₀ hQ 𝒱 {⊤} h1 hc 2).2.2.1
  let G' : (St Q₀ 𝒱).FullSubcategory ⥤ (St Q₀ {⊤}).FullSubcategory := ObjectProperty.ιOfLE h1
  let sm := m.smor Q (St Q₀ {⊤}) h
  let G'' : (St Q₀ 𝒱).FullSubcategory ⥤ Q.FullSubcategory := G' ⋙ sm.G
  have hV' : ∀ T, ∃ V ∈ 𝒱D (D.pb m.u), InU V (G'.obj T).obj := by
    rintro ⟨T, -, -, ⟨V, hV, rfl⟩, hT⟩
    exact ⟨_, mem_VD_pb D m.u hV, hT⟩
  have hV : ∀ T, ∃ V ∈ 𝒱D D, InU V (G''.obj T).obj := by
    rintro ⟨T, -, -, ⟨V, hV, rfl⟩, hT⟩
    exact ⟨V, hV, hT⟩
  obtain ⟨Λ'⟩ := GlobalTheory.T.exists_crystalline_lift (q := q') (b := nlBase R' I' γ' p) (ht := rfl) (κ := κ') (G' ⋙ (St Q₀ {⊤}).ι) (D.pb m.u) (fun T => by
    obtain ⟨V, ⟨s, hs⟩, hT⟩ := hV' T
    have hr : Set.range (pt (G'.obj T).obj) ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact hT (show x ∈ (⊤ : Scheme.Opens _) from trivial)
    refine ⟨IsOpenImmersion.lift V.ι (pt (G'.obj T).obj) hr ≫ s, ?_⟩
    rw [Category.assoc, hs, IsOpenImmersion.lift_fac]
    rfl)
  let Λ : B.CLift (q := q) (b := nlBase R I γ p) (ht := rfl) (κ := κ) (G'' ⋙ Q.ι) D :=
    { p := fun T => Λ'.p T ≫ Limits.pullback.fst D.f m.u
      hp := fun T => by
        have e := Λ'.hp T
        rw [Category.assoc, Limits.pullback.condition, ← Category.assoc]
        exact congrArg (· ≫ m.u) e
      w := fun φ => Λ'.w φ
      hw := fun {T T'} φ hh => by
        have hh' : (B.thSp ((G' ⋙ (St Q₀ {⊤}).ι).map φ) ≫ Λ'.p T) ≫ (D.pb m.u).f = Λ'.p T' ≫ (D.pb m.u).f := by
          rw [Category.assoc, Λ'.hp T, Λ'.hp T']
          exact congrArg (fun y => y.1.2) ((G' ⋙ (St Q₀ {⊤}).ι).map φ).pt
        refine (Λ'.hw φ hh').trans ?_
        exact u_congr D (Category.assoc _ _ _) rfl _ hh }
  obtain ⟨hz1, hcl1⟩ := hz' _ G' hV' Λ'
  obtain ⟨hz2, hcl2⟩ := hz _ G'' hV Λ
  let ψ : CH.Mor (G' ⋙ CH.modF (sP (St Q₀ {⊤})).A) (CH.modF (sP (St Q₀ 𝒱)).A) (RingHom.id R') :=
    { G := 𝟭 _, τ := fun T => (incl h1).o.τ T, nat := fun φ x => (incl h1).o.nat φ x }
  let μ : CH.Mor (G'' ⋙ CH.modF (sP Q).A) (CH.modF (sP (St Q₀ 𝒱)).A) σ :=
    { G := 𝟭 _, τ := fun T => sm.o.τ (G'.obj T), nat := fun φ x => sm.o.nat (G'.map φ) x }
  have e1 : (incl h1).o.pull 2 z' = ψ.pull 2 ((CH.Mor.restrict (CH.modF (sP (St Q₀ {⊤})).A) G').pull 2 z') := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z'
    rfl
  have e2 : (incl h1).o.pull 2 (sm.o.pull 2 z) = μ.pull 2 ((CH.Mor.restrict (CH.modF (sP Q).A) G'').pull 2 z) := by
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    rfl
  have hE : μ.pullC 2 (Λ.coc (RingHom.id R) N) = ψ.pullC 2 (Λ'.coc (RingHom.id R') N) := by
    funext s
    rfl
  have b1 : CH.d _ 2 (ψ.pullC 2 (Λ'.coc (RingHom.id R') N)) = 0 := by
    rw [ψ.d_pullC, hz1, map_zero]
  have b2 : CH.d _ 2 (μ.pullC 2 (Λ.coc (RingHom.id R) N)) = 0 := by
    rw [μ.d_pullC, hz2, map_zero]
  have k1 : ψ.pull 2 ((CH.cx _).cls _ hz1) = (CH.cx _).cls _ b1 := CrystallineSemistableComparison.P.mapH_cls ψ.hom 2 _ hz1 b1
  have k2 : μ.pull 2 ((CH.cx _).cls _ hz2) = (CH.cx _).cls _ b2 := CrystallineSemistableComparison.P.mapH_cls μ.hom 2 _ hz2 b2
  have key : ∀ (a b : CH.Cn (CH.modF (sP (St Q₀ 𝒱)).A) 2) (ha : CH.d _ 2 a = 0) (hb : CH.d _ 2 b = 0), a = b →
      (CH.cx _).cls a ha = (CH.cx _).cls b hb := by
    rintro a _ ha hb rfl
    rfl
  rw [e1, e2, ← hcl1, ← hcl2, k1, k2]
  exact key _ _ b2 b1 hE
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightedSumDecompositionDenominators
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightedSumDecompositionDenominators
set_option autoImplicit false

noncomputable section

open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Integral

def IntW (l K : ℕ) {r : ℕ} (v : (Fin r → ℕ) → ℚ) : Prop :=
  ∀ m, ∃ z : ℤ, (l : ℚ) ^ K * v m = z

theorem IntW.succ {l K r : ℕ} {v : (Fin r → ℕ) → ℚ} (h : IntW l K v) : IntW l (K + 1) v := by
  intro m
  obtain ⟨z, hz⟩ := h m
  refine ⟨l * z, ?_⟩
  push_cast
  rw [← hz, pow_succ]
  ring

theorem IntW.mono {l K K' r : ℕ} {v : (Fin r → ℕ) → ℚ} (h : IntW l K v) (hK : K ≤ K') :
    IntW l K' v := by
  induction K', hK using Nat.le_induction with
  | base => exact h
  | succ n _ ih => exact ih.succ

theorem IntW.neg_one_pow_mul {l K r : ℕ} {v : (Fin r → ℕ) → ℚ} (h : IntW l K v) (c : ℕ) :
    IntW l K (fun m => (-1 : ℚ) ^ c * v m) := by
  intro m
  obtain ⟨z, hz⟩ := h m
  refine ⟨(-1) ^ c * z, ?_⟩
  push_cast
  rw [← hz]
  ring

theorem int_sum {α : Type} (s : Finset α) (q : ℚ) (f : α → ℚ)
    (h : ∀ a ∈ s, ∃ z : ℤ, q * f a = z) : ∃ z : ℤ, q * ∑ a ∈ s, f a = z := by
  classical
  choose! g hg using h
  refine ⟨∑ a ∈ s, g a, ?_⟩
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl hg

theorem partialSum_int {l K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (h : IntW l K v) :
    IntW l K (partialSum i v) :=
  fun m => int_sum _ _ _ fun k _ => h _

theorem intW_partialSumMean {l K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l) (h : IntW l K v) :
    IntW l (K + 1) (meanP l i v) := by
  intro m
  have hl' : (l : ℚ) ≠ 0 := by exact_mod_cast hl.ne'
  obtain ⟨z, hz⟩ := int_sum (Finset.range l) ((l : ℚ) ^ K)
    (fun k => partialSum i v (Function.update m i k)) (fun k _ => partialSum_int h _)
  refine ⟨z, ?_⟩
  rw [← hz, meanP, pow_succ]
  field_simp

theorem aop_int {l K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l) (h : IntW l K v) :
    IntW l (K + 1) (Aop l i v) := by
  intro m
  obtain ⟨a, ha⟩ := (partialSum_int (i := i) h).succ (m + Pi.single i 1)
  obtain ⟨b, hb⟩ := intW_partialSumMean (i := i) hl h m
  refine ⟨a - b, ?_⟩
  push_cast
  rw [← ha, ← hb, Aop]
  ring

theorem bop_int {l K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l) (h : IntW l K v) :
    IntW l (K + 1) (Bop l i v) := by
  intro m
  by_cases h0 : m i = 0
  · simpa [Bop, h0] using intW_partialSumMean (i := i) hl h m
  · exact ⟨0, by simp [Bop, h0]⟩

theorem iterate_int {l K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l) (h : IntW l K v)
    (c : ℕ) : IntW l (K + c) ((Aop l i)^[c] v) := by
  induction c with
  | zero => simpa using h
  | succ c ih =>
    rw [Function.iterate_succ_apply']
    exact aop_int hl ih

theorem uW_int {l N K r : ℕ} {i : Fin r} {v : (Fin r → ℕ) → ℚ} (hl : 0 < l) (h : IntW l K v)
    (c : Fin (N + 1)) : IntW l (K + (N + 1)) (OneVar.uW l N i v c) := by
  unfold OneVar.uW
  split_ifs with hc
  · have h1 : IntW l (K + c + 1) (Bop l i ((Aop l i)^[c] v)) := bop_int hl (iterate_int hl h c)
    exact (h1.mono (by omega)).neg_one_pow_mul _
  · exact ((iterate_int hl h N).mono (by omega)).neg_one_pow_mul _

theorem abel_oneVar_uW (r l N : ℕ) (i : Fin r) (v : (Fin r → ℕ) → ℚ) (hl : 0 < l) (hg : GoodAt l i v)
    (hb : BddW v) :
    (∀ c : Fin (N + 1), BddW (OneVar.uW l N i v c)) ∧
    (∀ c : Fin (N + 1), (c : ℕ) = N ∨ ∀ m, m i ≠ 0 → OneVar.uW l N i v c m = 0) ∧
    (∀ (c : Fin (N + 1)) k, k ≠ i → GoodAt l k v → GoodAt l k (OneVar.uW l N i v c)) ∧
    (∀ (c : Fin (N + 1)) k, k ≠ i → (∀ m, m k ≠ 0 → v m = 0) → ∀ m, m k ≠ 0 → OneVar.uW l N i v c m = 0) ∧
    ∀ g : (Fin r → ℕ) → ℂ, Summable g →
      ∑' m, (v m : ℂ) * g m =
        ∑ c : Fin (N + 1), ∑' m, (OneVar.uW l N i v c m : ℂ) * DL (List.replicate (c : ℕ) i) g m := by
  refine ⟨fun c => ?_, fun c => ?_, fun c k hk hgk => ?_, fun c k hk hsk => ?_, fun g hs => ?_⟩
  · unfold OneVar.uW
    beta_reduce
    split_ifs with h
    · have hc := OneVar.iterate_good_bdd hl hg hb c
      exact OneVar.bddW_sign _ (@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.aop_props r l i _ hl hc.1 hc.2).2.1
    · exact OneVar.bddW_sign _ (OneVar.iterate_good_bdd hl hg hb N).2
  · by_cases h : (c : ℕ) < N
    · refine Or.inr fun m hm => ?_
      simp [OneVar.uW, h, Bop, hm]
    · exact Or.inl (by have := c.isLt; omega)
  · unfold OneVar.uW
    beta_reduce
    split_ifs with h
    · exact OneVar.goodAt_smul _ ((@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar.otherVar_main r l i k _ hk).1 (OneVar.iterate_good_other hk hgk c)).2
    · exact OneVar.goodAt_smul _ (OneVar.iterate_good_other hk hgk N)
  · intro m hm
    unfold OneVar.uW
    beta_reduce
    split_ifs with h
    · simp [((@GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.OtherVar.otherVar_main r l i k _ hk).2 (OneVar.iterate_supp_other hk hsk c)).2 m hm]
    · simp [OneVar.iterate_supp_other hk hsk N m hm]
  · rw [OneVar.tsum_iterate hl hg hb hs N, Fin.sum_univ_castSucc, Finset.sum_range]
    congr 1
    · refine Finset.sum_congr rfl fun c _ => ?_
      have hc : (c : ℕ) < N := c.isLt
      rw [← tsum_mul_left]
      refine tsum_congr fun m => ?_
      simp [OneVar.uW, hc, mul_assoc]
    · rw [← tsum_mul_left]
      refine tsum_congr fun m => ?_
      simp [OneVar.uW, mul_assoc]

theorem expansion_on_finset_int (r l N : ℕ) (w : (Fin r → ℕ) → ℚ) (hl : 0 < l) (hw : GoodWeight l w)
    (hz : ∀ m, ∃ z : ℤ, w m = z) (I : Finset (Fin r)) :
    ∃ (Q : Type) (_ : Fintype Q) (cs : Q → List (Fin r)) (u : Q → (Fin r → ℕ) → ℚ) (K : ℕ),
      (∀ q, BddW (u q)) ∧ (∀ q i, i ∉ I → GoodAt l i (u q) ∧ (cs q).count i = 0) ∧
      (∀ q i, i ∈ I → (cs q).count i = N ∨ ∀ m, m i ≠ 0 → u q m = 0) ∧
      (∀ q, IntW l K (u q)) ∧
      ∀ g : (Fin r → ℕ) → ℂ, Summable g →
        ∑' m, (w m : ℂ) * g m = ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) g m := by
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨Unit, inferInstance, fun _ => [], fun _ => w, 0,
      fun _ => GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.GoodBdd.bddW_of_periodic r l w hl (fun i m => hw.1 m i),
      fun _ i _ => ⟨⟨fun m => hw.1 m i, fun m => hw.2 m i⟩, by simp⟩,
      fun _ i hi => absurd hi (by simp), fun _ m => ?_, fun g _ => by simp [DL]⟩
    obtain ⟨z, hz⟩ := hz m
    exact ⟨z, by simp [hz]⟩
  | insert a I ha ih =>
    obtain ⟨Q, _, cs, u, K, hb, hg, hs, hi, hid⟩ := ih
    have hP := fun q => abel_oneVar_uW r l N a (u q) hl (hg q a ha).1 (hb q)
    have h1 := fun q => (hP q).1
    have h2 := fun q => (hP q).2.1
    have h3 := fun q => (hP q).2.2.1
    have h4 := fun q => (hP q).2.2.2.1
    have h5 := fun q => (hP q).2.2.2.2
    refine ⟨Q × Fin (N + 1), inferInstance, fun p => List.replicate (p.2 : ℕ) a ++ cs p.1,
      fun p => OneVar.uW l N a (u p.1) p.2, K + (N + 1), fun p => h1 p.1 p.2, ?_, ?_,
      fun p => uW_int hl (hi p.1) p.2, ?_⟩
    · rintro ⟨q, c⟩ k hk
      have hka : k ≠ a := fun h => hk (h ▸ Finset.mem_insert_self _ _)
      have hkI : k ∉ I := fun h => hk (Finset.mem_insert_of_mem h)
      refine ⟨h3 q c k hka (hg q k hkI).1, ?_⟩
      simp [List.count_append, List.count_replicate, (hg q k hkI).2, hka.symm]
    · rintro ⟨q, c⟩ k hk
      by_cases hka : k = a
      · subst hka
        have h0 : (cs q).count k = 0 := (hg q k ha).2
        rcases h2 q c with h | h
        · left
          simp [List.count_append, h0, h]
        · exact Or.inr h
      · have hkI : k ∈ I := (Finset.mem_insert.1 hk).resolve_left hka
        have hak : a ≠ k := fun h => hka h.symm
        rcases hs q k hkI with h | h
        · left
          simp [List.count_append, List.count_replicate, hak, h]
        · exact Or.inr (h4 q c k hka h)
    · intro g hgs
      rw [hid g hgs, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [h5 q _ (GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.summable_DL r (cs q) g hgs)]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [DL, List.foldr_append]

theorem expansion_all_variables_int : ∀ (r l N : ℕ) (w : (Fin r → ℕ) → ℚ), 0 < l → GoodWeight l w →
    (∀ m, ∃ z : ℤ, w m = z) →
    ∃ (Q : Type) (_ : Fintype Q) (cs : Q → List (Fin r)) (u : Q → (Fin r → ℕ) → ℚ) (K : ℕ),
      (∀ q, BddW (u q)) ∧ (∀ q i, (cs q).count i = N ∨ ∀ m, m i ≠ 0 → u q m = 0) ∧
      (∀ q m, ∃ z : ℤ, (l : ℚ) ^ K * u q m = z) ∧
      ∀ g : (Fin r → ℕ) → ℂ, Summable g →
        ∑' m, (w m : ℂ) * g m = ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) g m := by
  intro r l N w hl hw hz
  obtain ⟨Q, iQ, cs, u, K, hb, -, hs, hi, hid⟩ := expansion_on_finset_int r l N w hl hw hz Finset.univ
  exact ⟨Q, iQ, cs, u, K, hb, fun q i => hs q i (Finset.mem_univ i), hi, hid⟩

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Integral
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeightedSumDecompositionDenominatorsStatement
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_sum_decomposition_denominators : ∀ (r l N : ℕ) (w : (Fin r → ℕ) → ℚ), 0 < l → GoodWeight l w → (∀ m, ∃ z : ℤ, w m = z) → ∃ (Q : Type) (_ : Fintype Q) (cs : Q → List (Fin r)) (u : Q → (Fin r → ℕ) → ℚ) (K : ℕ), (∀ q, BddW (u q)) ∧ (∀ q i, (cs q).count i = N ∨ ∀ m, m i ≠ 0 → u q m = 0) ∧ (∀ q m, ∃ z : ℤ, (l : ℚ) ^ K * u q m = z) ∧ ∀ g : (Fin r → ℕ) → ℂ, Summable g → ∑' m, (w m : ℂ) * g m = ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) g m := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Integral.expansion_all_variables_int | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Integral.expansion_all_variables_int | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.Integral.expansion_all_variables_int <;> assumption)
end
end
