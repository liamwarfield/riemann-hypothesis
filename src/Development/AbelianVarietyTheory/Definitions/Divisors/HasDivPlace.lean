module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
section -- merged from Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.IsPrimeToPLat
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsogParam

def zpW (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] : ℤ_[p] →+* WittVector p k :=
  (WittVector.map (ZMod.castHom (dvd_refl p) k)).comp (WittVector.equiv p).symm.toRingHom

end GlobalTheory.IsogParam
end
end

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix
open IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct Classical ComplexOrder
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LKGeo

variable {p : ℕ} [Fact p.Prime]

abbrev VQ (D : Datum p) : Type := ℚ ⊗[ℤ] D.La

def actQ (D : Datum p) (b : D.O) : Module.End ℚ (VQ D) :=
  (DistribSMul.toLinearMap ℤ D.La b).baseChange ℚ

def actOn {C V : Type} [Ring C] [Algebra ℚ C] [AddCommGroup V] [Module ℚ V] (rep : C →ₐ[ℚ] Module.End ℚ V)
    (R : Type) [CommRing R] [Algebra ℚ R] : R ⊗[ℚ] C →ₐ[R] Module.End R (R ⊗[ℚ] V) :=
  Algebra.TensorProduct.lift (Algebra.ofId R _) ((Module.End.baseChangeHom ℚ R V).comp rep)
    (fun x _ => Algebra.commute_algebraMap_left x _)

structure Link (D : Datum p) (G : HTGroup p) where

  e : D.F ≃+* G.F
  n_eq : G.n = D.n

  rep : G.C →ₐ[ℚ] Module.End ℚ (VQ D)
  rep_inj : Function.Injective rep
  rep_range : ∀ A : Module.End ℚ (VQ D), (∃ x, rep x = A) ↔ ∀ b, A * actQ D b = actQ D b * A
  rep_F : ∀ c : 𝓞 D.F, rep (algebraMap G.F G.C (e c)) = actQ D (algebraMap (𝓞 D.F) D.O c)
  adj : ∀ x v w, D.EF.baseChange ℚ (rep x v) w = D.EF.baseChange ℚ v (rep (sh G x) w)

  ρp : ℤ_[p]
  ρp_eq : ∃ h : e D.ω ∈ G.Kq, G.u ⟨e D.ω, h⟩ = (ρp : ℚ_[p])

  s : Fin D.a → (G.F →+* AlgebraicClosure ℚ)
  s_C : ∀ i x, G.iotaC (s i (e x)) = D.tau i x

  w : Fin D.a → Fin G.m
  s_P : ∀ i x, G.iotaP (s i x) = G.emb (w i) x
  sig : ∀ v, sigPosH (G.gram_herm v) = 1 ↔ ∃ i, v = InfinitePlace.mk (G.iotaC.comp (s i))
  orient : ∃ J : ℝ ⊗[ℚ] G.C, J * J = -1 ∧ (starT G.star ℝ J).unop = -J ∧
    (∀ x, x ≠ 0 → 0 < (D.EF.baseChange ℚ).baseChange ℝ (actOn rep ℝ J x) x) ∧
    ∀ v : InfinitePlace G.F,
      ((if v.embedding (e D.ω) = D.ρc then -Complex.I else Complex.I) • (G.gram v * G.psiR v J)).PosDef

def HasDivPlace (G : HTGroup p) : Prop :=
  ∃ w : HeightOneSpectrum (𝓞 G.F), (p : 𝓞 G.F) ∉ w.asIdeal ∧
    ∀ x : w.adicCompletion G.F ⊗[G.F] G.C, x ≠ 0 → IsUnit x

def RegAf (G : HTGroup p) (ga : G.GAf) : Prop :=
  ∃ v : AwayP p, ∀ x y : v.1.adicCompletion ℚ ⊗[ℚ] G.C,
    Commute x ((ubcMap (AfP.eval v) ga).1.1 : v.1.adicCompletion ℚ ⊗[ℚ] G.C) →
    Commute y ((ubcMap (AfP.eval v) ga).1.1 : v.1.adicCompletion ℚ ⊗[ℚ] G.C) → Commute x y

def IsIntAf (a : AfP p) : Prop := ∀ v : AwayP p, AfP.eval v a ∈ v.1.adicCompletionIntegers ℚ

def LaHat (D : Datum p) : AddSubgroup (AfP p ⊗[ℚ] VQ D) :=
  AddSubgroup.closure {z | ∃ (a : AfP p) (x : D.La), IsIntAf a ∧ z = a ⊗ₜ ((1 : ℚ) ⊗ₜ x)}

def inAf (D : Datum p) (x : D.La) : AfP p ⊗[ℚ] VQ D := (1 : AfP p) ⊗ₜ ((1 : ℚ) ⊗ₜ x)

def mulKQ (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ) : KQ p K r →ₐ[ℚ_[p]] PadicAlgCl p :=
  Algebra.TensorProduct.lift K.val (Qr p r).val (fun _ _ => Commute.all _ _)

namespace Link

variable {D : Datum p} {G : HTGroup p} (L : Link D G)

def actG : G.GAf →* Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) :=
  ((actOn L.rep (AfP p)).toRingHom.toMonoidHom.comp (Units.coeHom _)).comp
    ((MonoidHom.fst _ _).comp (UPts G.star (AfP p)).subtype)

def CongOne (N : ℕ) (g : G.GAf) : Prop := ∀ v ∈ LaHat D, ∃ w ∈ LaHat D, L.actG g v = v + N • w

theorem CongOne.mul {N : ℕ} {g h : G.GAf} (hg : L.CongOne N g) (hh : L.CongOne N h) : L.CongOne N (g * h) := by
  intro v hv
  obtain ⟨w, hw, e1⟩ := hh v hv
  obtain ⟨w', hw', e2⟩ := hg (v + N • w) (add_mem hv (nsmul_mem hw N))
  refine ⟨w + w', add_mem hw hw', ?_⟩
  rw [map_mul, Module.End.mul_apply, e1, e2, smul_add, add_assoc]

def KN (N : ℕ) : Subgroup G.GAf where
  carrier := {g | L.CongOne N g ∧ L.CongOne N g⁻¹}
  one_mem' := by
    have h : L.CongOne N 1 := fun v _ => ⟨0, zero_mem _, by simp⟩
    exact ⟨h, by simpa using h⟩
  mul_mem' := fun hg hh => ⟨CongOne.mul L hg.1 hh.1, by rw [_root_.mul_inv_rev]; exact CongOne.mul L hh.2 hg.2⟩
  inv_mem' := fun hg => ⟨hg.2, by simpa using hg.1⟩

end Link

section Points

variable {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {k : Type} [Field k] {β : R →+* k} {N N' : ℕ}

abbrev TIso (o : Obj b N (spMap β)) : Type :=
  TateIsoO D k (Over.mk (𝟙 (Sp k)) ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))

variable {G : HTGroup p} (L : Link D G)

variable [CharP k p] [PerfectRing k p]

def Compat (b : Base D R) (β : R →+* k) (red : (Obar p).toSubring →+* k) : Prop :=
  WittVector.constantCoeff (GlobalTheory.IsogParam.zpW p k L.ρp) = β b.ρ ∧
    ∀ (i : Fin D.a) (c : 𝓞 D.F) (z : (Obar p).toSubring), (z : PadicAlgCl p) = G.emb (L.w i) (L.e c) →
      red z = β (b.t i c)

structure Frame (T : Theory p) (red : (Obar p).toSubring →+* k) (r : ℕ) (H : PDivGroup p k) (act : D.O → (H ⟶ H))
    (rat : ℤ → (H ⟶ H) → Prop) (d : (w : Fin G.m) → GL (Fin G.n) (KQ p (G.Fw w) r)) where

  io : GlobalTheory.LKLoc.intR p (LKRes.Q0 p) r →+* WittVector p k
  io_red : ∀ (a : GlobalTheory.LKLoc.intR p (LKRes.Q0 p) r) (z : (Obar p).toSubring),
    (z : PadicAlgCl p) = ((a : Qr p r) : PadicAlgCl p) → WittVector.constantCoeff (io a) = red z

  sp : ∀ w, D.O →+* Matrix (Fin D.m) (Fin D.m) (intKQ p (G.Fw w) r)
  sp_F : ∀ w (c : 𝓞 D.F), (sp w (algebraMap (𝓞 D.F) D.O c)).map (intKQ p (G.Fw w) r).subtype =
    Matrix.scalar (Fin D.m) (inclK p (G.Fw w) r (G.embW w (L.e c)))

  B : ∀ w, Matrix (Fin D.m) (Fin G.n) (intKQ p (G.Fw w) r) →+ T.M H
  B_smul : ∀ w (a : GlobalTheory.LKLoc.intR p (LKRes.Q0 p) r) (a' : intKQ p (G.Fw w) r), (a' : KQ p (G.Fw w) r) = inclQ p (G.Fw w) r a →
    ∀ X, B w (a' • X) = io a • B w X
  B_act : ∀ w c X, T.map (act c) (B w X) = B w ((sp w c)ᵀ * X)
  B_span : Submodule.span (WittVector p k) (⋃ w, Set.range (B w)) =
    LinearMap.ker (T.map (act (algebraMap (𝓞 D.F) D.O D.ω)) - GlobalTheory.IsogParam.zpW p k L.ρp • LinearMap.id)
  B_rat : ∀ w m ψ X, rat m ψ → T.map ψ (B w X) = m • (fun x => T.F H x)^[r] (B w X)
  B_F : ∀ w X, ∃ Y : Matrix (Fin D.m) (Fin G.n) (intKQ p (G.Fw w) r), Y.map (intKQ p (G.Fw w) r).subtype =
    HMul.hMul (α := Matrix (Fin D.m) (Fin G.n) (KQ p (G.Fw w) r)) (β := Matrix (Fin G.n) (Fin G.n) (KQ p (G.Fw w) r))
      ((X.map (intKQ p (G.Fw w) r).subtype).map (sigKQ p (G.Fw w) r)) ((d w)⁻¹).val ∧ T.F H (B w X) = B w Y

end Points

structure Setup {D : Datum p} {G : HTGroup p} (L : Link D G) {R : Type} [CommRing R] (b : Base D R)
    (β : R →+* AlgebraicClosure (ZMod p)) (red : (Obar p).toSubring →+* AlgebraicClosure (ZMod p)) (N r : ℕ) : Prop where
  simple : D.IsSimple
  div : HasDivPlace G
  three : 3 ≤ N
  cop : N.Coprime p
  pos : 0 < r
  rat : ∀ x, β x ^ p ^ r = β x
  compat : Compat L b β red

end GlobalTheory.LKGeo
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.ChernCalc
open GlobalTheory.FlagFibre (Low)
open scoped Matrix

namespace GlobalTheory.FlagCell2

variable {ι : Type} {m : ι → ℕ} {n d : ℕ}

abbrev Cell (m : ι → ℕ) : Type := Σ τ, Low (m τ)

def upU {K : Type} [Zero K] [One K] {s : ℕ} (y : Low s → K) : Matrix (Fin s) (Fin s) K :=
  Matrix.of fun a b => if h : a < b then y ⟨(b, a), h⟩ else if a = b then 1 else 0

def upM {K : Type} [Zero K] [One K] (y : Cell m → K) : Mat m K := fun τ => upU fun s => y ⟨τ, s⟩

def Cell.root (j : Cell m) : Root m := ⟨j.1, j.2.1.2⟩

def bsL {J : Type} (ε : Fin n ≃ Fin d ⊕ J) : V n →L[ℂ] V d :=
  (EuclideanSpace.equiv (Fin d) ℂ).symm.toContinuousLinearMap ∘L
    ContinuousLinearMap.pi fun a => EuclideanSpace.proj (ε.symm (.inl a))

def fb {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (w : V n) (j : J) : ℂ := w (ε.symm (.inr j))

def pt {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (v : V d) (y : J → ℂ) : V n := WithLp.toLp 2 fun a => Sum.elim (fun b => v b) y (ε a)

def cellPot (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (x : Root m) (w : V n) : ℝ :=
  -Real.log (grD (upM (fb ε w) x.1 * G (bsL ε w) x.1 * (upM (fb ε w) x.1)ᴴ) x.2)

variable [Fintype ι]

def cellFib (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (w : V n) : Ev n :=
  MvPolynomial.aeval (fun x => ofValues (ddc (cellPot ε G x) w)) ((fibrePoint m).map (algebraMap ℝ ℂ))

def cellForm (ε : Fin n ≃ Fin d ⊕ Cell m) (G : V d → Mat m ℂ) (a : V d → Alt d) (w : V n) : Alt n :=
  pull (bsL ε) (a (bsL ε w)) * (cellFib ε G w : Alt n)

def fibDens (G : Mat m ℂ) (y : Cell m → ℂ) : ℝ :=
  ∏ τ, GlobalTheory.TrueCx.flagConst (m τ) * (G τ).det.re ^ ((m τ : ℤ) - 1) * GlobalTheory.FlagFibre.dens (G τ)ᵀ fun s => y ⟨τ, s⟩


omit [Fintype ι] in
theorem upU_eq {s : ℕ} (y : Low s → ℂ) : upU y = (GlobalTheory.FlagFibre.uni y)ᵀ := by
  ext a b
  simp only [upU, GlobalTheory.FlagFibre.uni, Matrix.of_apply, Matrix.transpose_apply, eq_comm]


omit [Fintype ι] in
theorem bsL_apply {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (w : V n) (a : Fin d) : bsL ε w a = w (ε.symm (.inl a)) := rfl


omit [Fintype ι] in
theorem bsL_pt {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (v : V d) (y : J → ℂ) : bsL ε (pt ε v y) = v := by
  ext a
  simp [bsL_apply, pt]


omit [Fintype ι] in
theorem fb_pt {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (v : V d) (y : J → ℂ) : fb ε (pt ε v y) = y := by
  funext j
  simp [fb, pt]

section Variety

variable {F : Type} [Field F] {X Y : Var F} {σ : F →+* ℂ}

def InCell (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (A : Mat m X.Fn)
    (u : Cell m → Y.Fn) (y : Y.X) : Prop :=
  A ∈ E.S (f y) ∧ upM u * A.map φ ∈ E'.S y

def cellMap (ε : Fin n ≃ Fin X.dim ⊕ Cell m) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str) (c : AlgChart X.str σ X.dim)
    (u : Cell m → Y.Fn) (y : CxPts Y.str σ) : V n :=
  pt ε (c.e (ptMap σ f hf y)) fun j => ratVal (u j) y

def cellSet (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X)
    (hf : f ≫ X.str = Y.str) (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn) : Set (CxPts Y.str σ) :=
  {y | InCell E E' φ f A u (under y) ∧ ptMap σ f hf y ∈ c.e.source}

end Variety

end GlobalTheory.FlagCell2
end
end
