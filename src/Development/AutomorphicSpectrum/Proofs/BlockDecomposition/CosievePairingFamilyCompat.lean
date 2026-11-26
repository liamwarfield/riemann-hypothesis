module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftSumDifferentialCompat
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingIsoOfComponentIsos

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingRestrictionNatural
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorDirectSumBasisEquiv
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorDirectSumBasisEquiv
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue

theorem tensBasis : ∀ {K : Type} [Field K] {J : Type} [DecidableEq J] (V W : J → Type 1) [∀ t, AddCommGroup (V t)] [∀ t, Module K (V t)] [∀ t, AddCommGroup (W t)] [∀ t, Module K (W t)] (B : J → Type 1) [DecidableEq (Σ t, B t)] (b : ∀ t, Module.Basis (B t) K (V t)), ∃ e : (⨁ t, V t ⊗[K] W t) ≃ₗ[K] ⨁ u : (Σ t, B t), W u.1, ∀ (t : J) (β : B t) (x : W t), e (DirectSum.lof K J (fun t => V t ⊗[K] W t) t (b t β ⊗ₜ x)) = DirectSum.lof K (Σ t, B t) (fun u => W u.1) ⟨t, β⟩ x := by
  classical
  intro K _ J _ V W _ _ _ _ B _ b
  let et : ∀ t, (V t ⊗[K] W t) ≃ₗ[K] (Π₀ _ : B t, W t) := fun t =>
    (TensorProduct.congr (b t).repr (LinearEquiv.refl K (W t))) ≪≫ₗ
      (TensorProduct.finsuppScalarLeft K (W t) (B t)) ≪≫ₗ (finsuppLequivDFinsupp K)
  have het : ∀ t (β : B t) (x : W t), et t (b t β ⊗ₜ x) = DFinsupp.single β x := by
    intro t β x
    simp [et, TensorProduct.finsuppScalarLeft_apply_tmul, Module.Basis.repr_self]
  let C : (⨁ u : (Σ t, B t), W u.1) ≃ₗ[K] (Π₀ t, Π₀ _ : B t, W t) :=
    DFinsupp.sigmaCurryLEquiv (R := K) (M := fun t (_ : B t) => W t)
  refine ⟨(DFinsupp.mapRange.linearEquiv et) ≪≫ₗ C.symm, ?_⟩
  intro t β x
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
  have h1 : C (DirectSum.lof K (Σ t, B t) (fun u => W u.1) ⟨t, β⟩ x)
      = DFinsupp.single t (DFinsupp.single β x) := by
    have : DirectSum.lof K (Σ t, B t) (fun u => W u.1) ⟨t, β⟩ x
        = DFinsupp.single (⟨t, β⟩ : Σ t, B t) x := rfl
    rw [this]
    change DFinsupp.sigmaCurry (δ := fun t (_ : B t) => W t) (DFinsupp.single (⟨t, β⟩ : Σ t, B t) x) = _
    convert DFinsupp.sigmaCurry_single (δ := fun t (_ : B t) => W t) (⟨t, β⟩ : Σ t, B t) x
  rw [h1, ← het]
  exact DFinsupp.mapRange_single (hf := fun i => map_zero (et i))

end GlobalTheory.CompanionTheory.KunGlue
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorDirectSumBasisEquivStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_direct_sum_basis_equiv : ∀ {K : Type} [Field K] {J : Type} [DecidableEq J] (V W : J → Type 1) [∀ t, AddCommGroup (V t)] [∀ t, Module K (V t)] [∀ t, AddCommGroup (W t)] [∀ t, Module K (W t)] (B : J → Type 1) [DecidableEq (Σ t, B t)] (b : ∀ t, Module.Basis (B t) K (V t)), ∃ e : (⨁ t, V t ⊗[K] W t) ≃ₗ[K] ⨁ u : (Σ t, B t), W u.1, ∀ (t : J) (β : B t) (x : W t), e (DirectSum.lof K J (fun t => V t ⊗[K] W t) t (b t β ⊗ₜ x)) = DirectSum.lof K (Σ t, B t) (fun u => W u.1) ⟨t, β⟩ x := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.tensBasis | exact GlobalTheory.CompanionTheory.KunGlue.tensBasis | (intros; apply GlobalTheory.CompanionTheory.KunGlue.tensBasis <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingRestrictionNatural
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue.Glue

variable {K : Type} [Field K]

abbrev Bi (C : Cx.{1} K) (i : ℕ) : Type 1 := Module.Basis.ofVectorSpaceIndex K (C.H i)

abbrev bas (C : Cx.{1} K) (i : ℕ) : Module.Basis (Bi C i) K (C.H i) := Module.Basis.ofVectorSpace K (C.H i)

def rep (C : Cx.{1} K) (i : ℕ) (β : Bi C i) : C.Z i :=
  (Submodule.Quotient.mk_surjective _ (bas C i β)).choose

theorem rep_cls (C : Cx.{1} K) (i : ℕ) (β : Bi C i) :
    C.cls (rep C i β).1 (rep C i β).2 = bas C i β :=
  (Submodule.Quotient.mk_surjective _ (bas C i β)).choose_spec

structure Tup (P : ℕ → Cx.{1} K) (c : ℕ) : Type 1 where
  a : ℕ
  a' : ℕ
  ha : a + a' = c
  i : ℕ
  β : Bi (P a) i

instance (P : ℕ → Cx.{1} K) (c : ℕ) : DecidableEq (Tup P c) := Classical.decEq _

def tupEquiv (P : ℕ → Cx.{1} K) (c n : ℕ) :
    {v : Tup P c × ℕ // v.2 + v.1.i = n} ≃ Σ t : Idx c n, Bi (P t.a) t.i where
  toFun v := ⟨⟨v.1.1.a, v.1.1.i, v.1.1.a', v.1.2, v.1.1.ha, by have := v.2; omega⟩, v.1.1.β⟩
  invFun u := ⟨(⟨u.1.a, u.1.a', u.1.ha, u.1.i, u.2⟩, u.1.j), by have := u.1.h; simp only; omega⟩
  left_inv := by rintro ⟨⟨⟨a, a', ha, i, β⟩, m⟩, h⟩; rfl
  right_inv := by rintro ⟨⟨a, i, a', j, ha, h⟩, β⟩; rfl

theorem reidx {V U : Type 1} [DecidableEq V] [DecidableEq U] (σ : V ≃ U) (W : U → Type 1)
    [∀ u, AddCommGroup (W u)] [∀ u, Module K (W u)] :
    ∃ r : (⨁ v, W (σ v)) ≃ₗ[K] ⨁ u, W u,
      ∀ v x, r (DirectSum.lof K V (fun v => W (σ v)) v x) = DirectSum.lof K U W (σ v) x := by
  let f : (⨁ v, W (σ v)) →ₗ[K] ⨁ u, W u :=
    DirectSum.toModule K V _ fun v => DirectSum.lof K U W (σ v)
  let g : (⨁ u, W u) →ₗ[K] ⨁ v, W (σ v) :=
    DirectSum.toModule K U _ fun u =>
      (DirectSum.lof K V (fun v => W (σ v)) (σ.symm u)).comp
        ((LinearEquiv.cast (R := K) (M := W) (σ.apply_symm_apply u).symm).toLinearMap)
  refine ⟨LinearEquiv.ofLinear f g ?_ ?_, fun v x => ?_⟩
  · refine DirectSum.linearMap_ext K fun u => LinearMap.ext fun x => ?_
    have key : ∀ (u' : U) (hu : u' = u) (hh : u = u'),
        DirectSum.lof K U W u' (LinearEquiv.cast (R := K) (M := W) hh x) = DirectSum.lof K U W u x := by
      rintro _ rfl hh
      rfl
    simp only [LinearMap.comp_apply, LinearMap.id_apply, f, g, DirectSum.toModule_lof, LinearEquiv.coe_coe]
    exact key _ (σ.apply_symm_apply u) _
  · refine DirectSum.linearMap_ext K fun v => LinearMap.ext fun x => ?_
    have key : ∀ (v' : V) (hv : v' = v) (hh : σ v = σ v'),
        DirectSum.lof K V (fun v => W (σ v)) v' (LinearEquiv.cast (R := K) (M := W) hh x) =
          DirectSum.lof K V (fun v => W (σ v)) v x := by
      rintro _ rfl hh
      rfl
    simp only [LinearMap.comp_apply, LinearMap.id_apply, f, g, DirectSum.toModule_lof, LinearEquiv.coe_coe]
    exact key _ (σ.symm_apply_apply v) _
  · simp only [LinearEquiv.ofLinear_apply, f, DirectSum.toModule_lof]

def KunC {P Q T : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (c n : ℕ) : Prop :=
  ∃ e : (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) ≃ₗ[K] (T c).H n,
    ∀ (t : Idx c n) (x : (P t.a).X t.i) (y : (Q t.a').X t.j) (hx : (P t.a).d t.i x = 0) (hy : (Q t.a').d t.j y = 0)
      (hz : (T c).d n ((pr t.ha).μ t.h x y) = 0),
      e (DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) t ((P t.a).cls x hx ⊗ₜ (Q t.a').cls y hy)) =
        (T c).cls ((pr t.ha).μ t.h x y) hz

def MvC {I : Type 1} [DecidableEq I] (k : I → ℕ) (A : I → Cx.{1} K) (T : Cx.{1} K)
    (g : ∀ (u : I) {m n : ℕ}, m + k u = n → (A u).X m →ₗ[K] T.X n) (n : ℕ) : Prop :=
  ∃ e : (⨁ v : {v : I × ℕ // v.2 + k v.1 = n}, (A v.1.1).H v.1.2) ≃ₗ[K] T.H n,
    ∀ (v : {v : I × ℕ // v.2 + k v.1 = n}) (x : (A v.1.1).X v.1.2) (hx : (A v.1.1).d v.1.2 x = 0)
      (hz : T.d n (g v.1.1 v.2 x) = 0),
      e (DirectSum.lof K _ (fun v : {v : I × ℕ // v.2 + k v.1 = n} => (A v.1.1).H v.1.2) v ((A v.1.1).cls x hx)) =
        T.cls (g v.1.1 v.2 x) hz

def gmap {P Q T : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (c : ℕ)
    (u : Tup P c) {m n : ℕ} (h : m + u.i = n) : (Q u.a').X m →ₗ[K] (T c).X n :=
  (pr u.ha).μ (show u.i + m = n by omega) (rep (P u.a) u.i u.β).1

theorem mu_closed {C D E : Cx.{1} K} (p : CxPairing C D E) {i j n : ℕ} (h : i + j = n) (x : C.X i) (y : D.X j)
    (hx : C.d i x = 0) (hy : D.d j y = 0) : E.d n (p.μ h x y) = 0 := by
  rw [p.leib, hx, hy]; simp

def sec (C : Cx.{1} K) (i : ℕ) : C.H i →ₗ[K] C.Z i := (bas C i).constr K (rep C i)

theorem sec_bas (C : Cx.{1} K) (i : ℕ) (β : Bi C i) : sec C i (bas C i β) = rep C i β :=
  (bas C i).constr_basis K _ _

theorem cls_sec (C : Cx.{1} K) (i : ℕ) (ξ : C.H i) : C.cls (sec C i ξ).1 (sec C i ξ).2 = ξ := by
  have : (Submodule.mkQ _ : C.Z i →ₗ[K] C.H i).comp (sec C i) = LinearMap.id := by
    refine (bas C i).ext fun β => ?_
    simp only [LinearMap.comp_apply, sec_bas, LinearMap.id_apply]
    exact rep_cls C i β
  exact LinearMap.congr_fun this ξ

def prodR {C D E : Cx.{1} K} (p : CxPairing C D E) {i j n : ℕ} (h : i + j = n) (y : D.X j) (hy : D.d j y = 0) :
    C.H i →ₗ[K] E.H n :=
  (Submodule.mkQ _ : E.Z n →ₗ[K] E.H n).comp
    (LinearMap.codRestrict (E.Z n)
      (((p.μ h).flip y).comp ((C.Z i).subtype.comp (sec C i)))
      (fun ξ => mu_closed p h _ y (sec C i ξ).2 hy))

theorem prodR_apply {C D E : Cx.{1} K} (p : CxPairing C D E) {i j n : ℕ} (h : i + j = n) (y : D.X j) (hy : D.d j y = 0)
    (ξ : C.H i) :
    prodR p h y hy ξ = E.cls (p.μ h (sec C i ξ).1 y) (mu_closed p h _ y (sec C i ξ).2 hy) := rfl

theorem prodR_cls {C D E : Cx.{1} K} (p : CxPairing C D E) {i j n : ℕ} (h : i + j = n) (x : C.X i) (hx : C.d i x = 0)
    (y : D.X j) (hy : D.d j y = 0) (hz : E.d n (p.μ h x y) = 0) :
    prodR p h y hy (C.cls x hx) = E.cls (p.μ h x y) hz := by
  rw [prodR_apply, ← CrystallineSemistableComparison.P.cxcup_cls p h _ y (sec C i _).2 hy, ← CrystallineSemistableComparison.P.cxcup_cls p h x y hx hy, cls_sec]

theorem kun_iff_mv {P Q T : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (c n : ℕ) :
    KunC pr c n ↔ MvC (I := Tup P c) (fun u => u.i) (fun u => Q u.a') (T c) (fun u {m n} h => gmap pr c u h) n := by
  classical
  obtain ⟨e₁, he₁⟩ := GlobalTheory.T.tensor_direct_sum_basis_equiv (K := K) (J := Idx c n) (fun t => (P t.a).H t.i) (fun t => (Q t.a').H t.j)
    (fun t => Bi (P t.a) t.i) (fun t => bas (P t.a) t.i)
  obtain ⟨r, hr⟩ := reidx (K := K) (tupEquiv P c n) (fun u : (Σ t : Idx c n, Bi (P t.a) t.i) => (Q u.1.a').H u.1.j)
  constructor
  · rintro ⟨e, he⟩
    refine ⟨(r.trans e₁.symm).trans e, ?_⟩
    rintro ⟨⟨⟨a, a', ha, i, β⟩, m⟩, h⟩ x hx hz
    have h' : i + m = n := by simpa [add_comm] using h
    have step := he ⟨a, i, a', m, ha, h'⟩ (rep (P a) i β).1 x (rep (P a) i β).2 hx hz
    have e1 := he₁ ⟨a, i, a', m, ha, h'⟩ β ((Q a').cls x hx)
    have r1 := hr ⟨(⟨a, a', ha, i, β⟩, m), h⟩ ((Q a').cls x hx)
    simp only [LinearEquiv.trans_apply]
    refine Eq.trans ?_ step
    refine congrArg e ?_
    rw [rep_cls]
    refine Eq.trans (congrArg e₁.symm r1) ?_
    exact (LinearEquiv.symm_apply_eq _).2 e1.symm
  · rintro ⟨E, hE⟩
    refine ⟨(e₁.trans r.symm).trans E, ?_⟩
    rintro ⟨a, i, a', j, ha, h⟩ x y hx hy hz
    have h' : j + i = n := by omega
    let L : (P a).H i →ₗ[K] (T c).H n :=
      ((E.toLinearMap.comp r.symm.toLinearMap).comp e₁.toLinearMap).comp
        ((DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) ⟨a, i, a', j, ha, h⟩).comp
          ((TensorProduct.mk K _ _).flip ((Q a').cls y hy)))
    have hL : L = prodR (pr ha) h y hy := by
      refine (bas (P a) i).ext fun β => ?_
      have e1 := he₁ ⟨a, i, a', j, ha, h⟩ β ((Q a').cls y hy)
      have r1 := hr ⟨(⟨a, a', ha, i, β⟩, j), h'⟩ ((Q a').cls y hy)
      have hz' := mu_closed (pr ha) h _ y (rep (P a) i β).2 hy
      have E1 := hE ⟨(⟨a, a', ha, i, β⟩, j), h'⟩ y hy hz'
      have r2 := (LinearEquiv.symm_apply_eq r).2 r1.symm
      have hLb : L (bas (P a) i β) = E (r.symm (e₁ (DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j)
          ⟨a, i, a', j, ha, h⟩ (bas (P a) i β ⊗ₜ (Q a').cls y hy)))) := rfl
      rw [hLb, e1]
      refine Eq.trans (congrArg E r2) (Eq.trans E1 ?_)
      rw [prodR_apply]
      simp only [sec_bas]
      rfl
    have := LinearMap.congr_fun hL ((P a).cls x hx)
    rw [prodR_cls (pr ha) h x hx y hy hz] at this
    exact this

end GlobalTheory.CompanionTheory.KunGlue.Glue

open GlobalTheory.CompanionTheory.KunGlue.Glue in
theorem GlobalTheory.CompanionTheory.KunGlue.kun_glue : MVBij → ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] [Fintype ι] (P : ℕ → Cx.{1} K) (Q T : ℕ → Sy.{1} K ι) (pr : ∀ (S : Finset ι) {a a' c : ℕ}, a + a' = c → CxPairing (P a) ((Q a').K S) ((T c).K S)), (∀ {S S' : Finset ι} (h : S ⊆ S') {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n) (x : (P a).X i) (y : ((Q a').K S).X j), ((T c).res h).f n ((pr S ha).μ hn x y) = (pr S' ha).μ hn x (((Q a').res h).f j y)) → (∀ a, (Q a).Desc) → (∀ c, (T c).Desc) → (∀ S : Finset ι, S.Nonempty → KunE (P := P) (Q := fun a => (Q a).K S) (T := fun c => (T c).K S) (fun {a a' c} ha => pr S ha)) → KunE (P := P) (Q := fun a => (Q a).K ∅) (T := fun c => (T c).K ∅) (fun {a a' c} ha => pr ∅ ha) := by
  intro hmv K _ ι _ _ P Q T pr hnat hQ hT hK c n
  have main := GlobalTheory.T.mvE_empty_of_mvE_nonempty hmv (K := K) (ι := ι) (I := Tup P c) (fun u => u.i) (fun u => (-1 : ℤˣ) ^ u.i)
    (fun u => Q u.a') (T c) (fun u S {m n} h => gmap (Q := fun a => (Q a).K S) (T := fun c => (T c).K S) (fun {a a' c} ha => pr S ha) c u h)
    ?_ ?_ (fun u => hQ _) (hT c)
    (fun S hS n => (kun_iff_mv (Q := fun a => (Q a).K S) (T := fun c => (T c).K S) (fun {a a' c} ha => pr S ha) c n).1 (hK S hS c n)) n
  · exact (kun_iff_mv (Q := fun a => (Q a).K ∅) (T := fun c => (T c).K ∅) (fun {a a' c} ha => pr ∅ ha) c n).2 main
  · intro u S m n h h' x
    simp only [gmap]
    rw [(pr S u.ha).leib, (rep (P u.a) u.i u.β).2]
    simp
  · intro u S S' hS m n h x
    exact hnat hS u.ha _ _ x
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingRestrictionNaturalStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_restriction_natural : MVBij → ∀ {K : Type} [Field K] {ι : Type} [DecidableEq ι] [Fintype ι] (P : ℕ → Cx.{1} K) (Q T : ℕ → Sy.{1} K ι) (pr : ∀ (S : Finset ι) {a a' c : ℕ}, a + a' = c → CxPairing (P a) ((Q a').K S) ((T c).K S)), (∀ {S S' : Finset ι} (h : S ⊆ S') {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n) (x : (P a).X i) (y : ((Q a').K S).X j), ((T c).res h).f n ((pr S ha).μ hn x y) = (pr S' ha).μ hn x (((Q a').res h).f j y)) → (∀ a, (Q a).Desc) → (∀ c, (T c).Desc) → (∀ S : Finset ι, S.Nonempty → KunE (P := P) (Q := fun a => (Q a).K S) (T := fun c => (T c).K S) (fun {a a' c} ha => pr S ha)) → KunE (P := P) (Q := fun a => (Q a).K ∅) (T := fun c => (T c).K ∅) (fun {a a' c} ha => pr ∅ ha) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.kun_glue | exact GlobalTheory.CompanionTheory.KunGlue.kun_glue | (intros; apply GlobalTheory.CompanionTheory.KunGlue.kun_glue <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosievePairingFamilyCompat
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

namespace GlobalTheory.CompanionTheory.KunGlue.GlueGen

variable {K : Type} [Field K] {C D : Type 1} [Category.{0} C] [Category.{0} D]

theorem mem_bot (F : C ⥤ ModuleCat.{0} K) (U : ObjectProperty C) (n : ℕ) (z : CH.Cn (U.ι ⋙ F) n) :
    z ∈ relS (U.ι ⋙ F) (fun T => (⊥ : ObjectProperty C) T.obj) n :=
  fun _ hs => False.elim hs

noncomputable def up (F : C ⥤ ModuleCat.{0} K) (U : ObjectProperty C) (n : ℕ) :
    CH.Cn (U.ι ⋙ F) n →ₗ[K] (RC F U (cosieve_bot (C := C))).X n :=
  LinearMap.codRestrict _ LinearMap.id (mem_bot F U n)

def inc (F : C ⥤ ModuleCat.{0} K) (U : ObjectProperty C) :
    Cx.Hom (RC F U (cosieve_bot (C := C))) (CH.cx (U.ι ⋙ F)) (RingHom.id K) :=
  ⟨fun _ => Submodule.subtype _, fun _ _ => rfl⟩

theorem inc_bij (F : C ⥤ ModuleCat.{0} K) (U : ObjectProperty C) (n : ℕ) :
    Function.Bijective ((inc F U).f n) :=
  ⟨Subtype.val_injective, fun z => ⟨⟨z, mem_bot F U n z⟩, rfl⟩⟩

noncomputable def relPr {M : Cx.{1} K} (F : C ⥤ ModuleCat.{0} K) (G : D ⥤ ModuleCat.{0} K) (U : ObjectProperty C)
    (U' : ObjectProperty D) (p : CxPairing M (CH.cx (U.ι ⋙ F)) (CH.cx (U'.ι ⋙ G))) :
    CxPairing M (RC F U (cosieve_bot (C := C))) (RC G U' (cosieve_bot (C := D))) where
  μ {i j n} h := ((p.μ h).compl₂ ((inc F U).f j)).compr₂ (up G U' n)
  leib h x y := Subtype.ext (p.leib h x y.1)

theorem kun_iff (F : ℕ → C ⥤ ModuleCat.{0} K) (E : ℕ → D ⥤ ModuleCat.{0} K) (P : ℕ → Cx.{1} K)
    (U : ObjectProperty C) (U' : ObjectProperty D)
    (p : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (CH.cx (U.ι ⋙ F a')) (CH.cx (U'.ι ⋙ E c))) :
    KunE (P := P) (Q := fun a => RC (F a) U (cosieve_bot (C := C))) (T := fun c => RC (E c) U' (cosieve_bot (C := D)))
        (fun {a a' c} ha => relPr (F a') (E c) U U' (p ha)) ↔
      KunE (P := P) (Q := fun a => CH.cx (U.ι ⋙ F a)) (T := fun c => CH.cx (U'.ι ⋙ E c)) (fun {a a' c} ha => p ha) :=
  GlobalTheory.T.pairing_iso_of_component_isos _ _ (fun a => Cx.Hom.id (C := P a)) (fun a => inc (F a) U) (fun c => inc (E c) U')
    (fun a n => CrystallineSemistableComparison.P.mapH_bij _ (fun _ => Function.bijective_id) n)
    (fun a n => CrystallineSemistableComparison.P.mapH_bij _ (inc_bij (F a) U) n)
    (fun c n => CrystallineSemistableComparison.P.mapH_bij _ (inc_bij (E c) U') n)
    (fun _ _ _ _ _ _ _ => rfl)

end GlobalTheory.CompanionTheory.KunGlue.GlueGen

open GlobalTheory.CompanionTheory.KunGlue.GlueGen in
theorem GlobalTheory.CompanionTheory.KunGlue.glue_gen : MVBij → CovDesc → ∀ {K : Type} [Field K] {C D : Type 1} [Category.{0} C] [Category.{0} D] (F : ℕ → C ⥤ ModuleCat.{0} K) (E : ℕ → D ⥤ ModuleCat.{0} K) (P : ℕ → Cx.{1} K) (Rel : ObjectProperty C → ObjectProperty D → Prop) (pr : ∀ (U : ObjectProperty C) (U' : ObjectProperty D), Rel U U' → ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (CH.cx (U.ι ⋙ F a')) (CH.cx (U'.ι ⋙ E c))), (∀ {U₁ U₂ : ObjectProperty C} {U₁' U₂' : ObjectProperty D} (r₁ : Rel U₁ U₁') (r₂ : Rel U₂ U₂') (k : U₂ ≤ U₁) (k' : U₂' ≤ U₁') {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n) (x : (P a).X i) (y : CH.Cn (U₁.ι ⋙ F a') j), (resU (E c) k').pullC n ((pr U₁ U₁' r₁ ha).μ hn x y) = (pr U₂ U₂' r₂ ha).μ hn x ((resU (F a') k).pullC j y)) → ∀ {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty C) (W : ι → ObjectProperty D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (hR : ∀ S : Finset ι, Rel (capU V S) (capU W S)), (∀ S : Finset ι, S.Nonempty → KunE (P := P) (Q := fun a => CH.cx ((capU V S).ι ⋙ F a)) (T := fun c => CH.cx ((capU W S).ι ⋙ E c)) (fun {a a' c} ha => pr (capU V S) (capU W S) (hR S) ha)) → KunE (P := P) (Q := fun a => CH.cx ((capU V ∅).ι ⋙ F a)) (T := fun c => CH.cx ((capU W ∅).ι ⋙ E c)) (fun {a a' c} ha => pr (capU V ∅) (capU W ∅) (hR ∅) ha) := by
  intro hmv hcd K _ C D _ _ F E P Rel pr hnat ι _ _ V W cV cW hR hS
  have key := GlobalTheory.T.pairing_restriction_natural hmv (K := K) (ι := ι) P (fun a => covSy (F a) V (cosieve_bot (C := C)))
    (fun c => covSy (E c) W (cosieve_bot (C := D)))
    (fun S {a a' c} ha => relPr (F a') (E c) (capU V S) (capU W S) (pr (capU V S) (capU W S) (hR S) ha))
    (fun {S S'} h {a a' c} ha {i j n} hn x y => Subtype.ext
      (hnat (hR S) (hR S') (fun _ hT => ⟨hT.1, fun α hα => hT.2 α (h hα)⟩)
        (fun _ hT => ⟨hT.1, fun α hα => hT.2 α (h hα)⟩) ha hn x y.1))
    (fun a => hcd K ι C (F a) V ⊥ cosieve_bot cV)
    (fun c => hcd K ι D (E c) W ⊥ cosieve_bot cW)
    (fun S hne => (kun_iff F E P (capU V S) (capU W S) (fun {a a' c} ha => pr (capU V S) (capU W S) (hR S) ha)).2 (hS S hne))
  exact (kun_iff F E P (capU V ∅) (capU W ∅) (fun {a a' c} ha => pr (capU V ∅) (capU W ∅) (hR ∅) ha)).1 key
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosievePairingFamilyCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosieve_pairing_family_compat : MVBij → CovDesc → ∀ {K : Type} [Field K] {C D : Type 1} [Category.{0} C] [Category.{0} D] (F : ℕ → C ⥤ ModuleCat.{0} K) (E : ℕ → D ⥤ ModuleCat.{0} K) (P : ℕ → Cx.{1} K) (Rel : ObjectProperty C → ObjectProperty D → Prop) (pr : ∀ (U : ObjectProperty C) (U' : ObjectProperty D), Rel U U' → ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (CH.cx (U.ι ⋙ F a')) (CH.cx (U'.ι ⋙ E c))), (∀ {U₁ U₂ : ObjectProperty C} {U₁' U₂' : ObjectProperty D} (r₁ : Rel U₁ U₁') (r₂ : Rel U₂ U₂') (k : U₂ ≤ U₁) (k' : U₂' ≤ U₁') {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (hn : i + j = n) (x : (P a).X i) (y : CH.Cn (U₁.ι ⋙ F a') j), (resU (E c) k').pullC n ((pr U₁ U₁' r₁ ha).μ hn x y) = (pr U₂ U₂' r₂ ha).μ hn x ((resU (F a') k).pullC j y)) → ∀ {ι : Type} [DecidableEq ι] [Fintype ι] (V : ι → ObjectProperty C) (W : ι → ObjectProperty D), (∀ α, Cosieve (V α)) → (∀ α, Cosieve (W α)) → ∀ (hR : ∀ S : Finset ι, Rel (capU V S) (capU W S)), (∀ S : Finset ι, S.Nonempty → KunE (P := P) (Q := fun a => CH.cx ((capU V S).ι ⋙ F a)) (T := fun c => CH.cx ((capU W S).ι ⋙ E c)) (fun {a a' c} ha => pr (capU V S) (capU W S) (hR S) ha)) → KunE (P := P) (Q := fun a => CH.cx ((capU V ∅).ι ⋙ F a)) (T := fun c => CH.cx ((capU W ∅).ι ⋙ E c)) (fun {a a' c} ha => pr (capU V ∅) (capU W ∅) (hR ∅) ha) := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.glue_gen | exact GlobalTheory.CompanionTheory.KunGlue.glue_gen | (intros; apply GlobalTheory.CompanionTheory.KunGlue.glue_gen <;> assumption)
end
