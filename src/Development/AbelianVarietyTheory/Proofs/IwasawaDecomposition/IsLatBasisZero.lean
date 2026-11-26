module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
public import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIvDOfDefinite
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EpsZeroCompOfIsTanAtG
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricHalfCoreFormsUniformisationIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
set_option autoImplicit false

noncomputable section

open Topology

namespace GlobalTheory.ShFam.Hor.LogCh

def IsLatBasis {g r : ℕ} (K : Set (Fin g → ℂ)) (b : Fin r → Fin g → ℂ) : Prop :=
  LinearIndependent ℝ b ∧ ∀ w, w ∈ K ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • b j

def IsLatFam {n g : ℕ} (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) : Prop :=
  IsOpen B ∧ (∀ b ∈ B, ∃ H : AddSubgroup (Fin g → ℂ), (H : Set (Fin g → ℂ)) = K b) ∧
    IsOpen {q : (Fin n → ℂ) × (Fin g → ℂ) | q.1 ∈ B ∧ q.2 ∉ K q.1} ∧
    ∀ b₀ ∈ B, ∀ w₀ ∈ K b₀, ∃ ζ : (Fin n → ℂ) → Fin g → ℂ, ζ b₀ = w₀ ∧ AnalyticAt ℂ ζ b₀ ∧
      ∀ᶠ q in 𝓝 (b₀, w₀), q.2 ∈ K q.1 ↔ q.2 = ζ q.1

section Exp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}

def IsExpAt (t : SAB H X) (y : Sp ℂ ⟶ X) {g : ℕ} (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) : Prop :=
  (∀ v w, e (v + w) = e v * e w) ∧
    (∀ w, ∃! v, IsTanAtG t y v ∧ IsDerivAt0 (fun u => (e u).left) w v) ∧
    ∀ v, IsTanAtG t y v → ∃! w, IsDerivAt0 (fun u => (e u).left) w v

end Exp

end GlobalTheory.ShFam.Hor.LogCh
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open MonObj

namespace GlobalTheory.LineNorm

attribute [local instance] Over.cartesianMonoidalCategory

section Models

variable {F : Type} [Field F] [NumberField F]

abbrev PtFn (Y : Var F) : Type := ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ

end Models

section Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

def IsTanBasis {R : Type} [CommRing R] (x : Sp R ⟶ X) {g : ℕ} (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) : Prop :=
  (∀ i, IsTanAtG t x (e i)) ∧ ∀ (S : Type) [CommRing S] (φ : R →+* S) (w : Sp (DualNumber S) ⟶ t.G.left),
    IsTanAtG t (spMap φ ≫ x) w →
      ∃! a : Fin g → S, IsCombAtG t (spMap φ ≫ x) (fun i => spMap (dualMap φ) ≫ e i) a w

def IsIndep {R : Type} [CommRing R] (x : Sp R ⟶ X) {m : ℕ} (u : Fin m → (Sp (DualNumber R) ⟶ t.G.left)) : Prop :=
  ∀ cf cf' w, IsCombAtG t x u cf w → IsCombAtG t x u cf' w → cf = cf'

def minor {R : Type} [CommRing R] {m g k : ℕ} (a : Fin m → Fin g → R) (hk : k ≤ m) (s : Fin k → Fin g) : R :=
  (Matrix.of fun l i => a (Fin.castLE hk l) (s i)).det

def DlogIs {O : Type} [CommRing O] {x : Sp O ⟶ X} (p n : ℕ) (c : TorsChar t x (p ^ n)) {g : ℕ}
    (e : Fin g → (Sp (DualNumber O) ⟶ t.G.left)) (h : Fin g → O) : Prop :=
  ∀ (a : Fin g → O) (v : Sp (DualNumber O) ⟶ t.G.left), IsCombAtG t x e a v →
    ∀ w : Over.mk (spMap (algebraMap O (DualNumber (O ⧸ Ideal.span {(p : O) ^ n}))) ≫ x) ⟶ t.G,
      w.left = spMap (dualMap (Ideal.Quotient.mk (Ideal.span {(p : O) ^ n}))) ≫ v →
        (c.χ _ w : DualNumber (O ⧸ Ideal.span {(p : O) ^ n})).snd =
          Ideal.Quotient.mk (Ideal.span {(p : O) ^ n}) (∑ i, h i * a i)

def Thru {R B : Type} [CommRing R] [CommRing B] [Algebra R B] (u : Sp B ⟶ t.G.left) {S : Type} [CommRing S]
    (φ : R →+* S) (w : Sp S ⟶ t.G.left) : Prop :=
  ∃ β : B →+* S, β.comp (algebraMap R B) = φ ∧ spMap β ≫ u = w

structure IsFinPart {R : Type} [CommRing R] (x : Sp R ⟶ X) (q : ℕ) {B : Type} [CommRing B] [Algebra R B]
    (u : Over.mk (spMap (algebraMap R B) ≫ x) ⟶ t.G) : Prop where
  finite : Module.Finite R B
  free : Module.Free R B
  tors : u ^ q = 1
  mono : ∀ (S : Type) [CommRing S] (β β' : B →+* S), β.comp (algebraMap R B) = β'.comp (algebraMap R B) →
    spMap β ≫ u.left = spMap β' ≫ u.left → β = β'
  isOpen : ∀ (S : Type) [CommRing S] (φ : R →+* S) (w : Over.mk (spMap φ ≫ x) ⟶ t.G), w ^ q = 1 →
    (∀ 𝔪 : Ideal S, 𝔪.IsMaximal →
      Thru t u.left ((Ideal.Quotient.mk 𝔪).comp φ) (spMap (Ideal.Quotient.mk 𝔪) ≫ w.left)) → Thru t u.left φ w.left
  one : ∀ (S : Type) [CommRing S] (φ : R →+* S), Thru t u.left φ (1 : Over.mk (spMap φ ≫ x) ⟶ t.G).left
  mul : ∀ (S : Type) [CommRing S] (φ : R →+* S) (w w' : Over.mk (spMap φ ≫ x) ⟶ t.G),
    Thru t u.left φ w.left → Thru t u.left φ w'.left → Thru t u.left φ (w * w').left
  sect : ∀ (k : Type) [Field k] (β : B →+* k), ∃ σ : B →ₐ[R] R, β = (β.comp (algebraMap R B)).comp σ.toRingHom
  inj : ∀ b : B, (∀ σ : B →ₐ[R] R, σ b = 0) → b = 0

variable {F : Type} [Field F] [NumberField F] {Y : Var F}


end Tangent

end GlobalTheory.LineNorm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM

namespace GlobalTheory.TorRef

section Defs

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

def IsTwInv (φ : InvFun (𝓞 E)) : Prop :=
  ∀ σ : 𝓞 E ≃+* 𝓞 E, σ H.w0 = H.w0 → ∀ (n : ℕ) (B : (Fin n → 𝓞 E) → (Fin n → 𝓞 E) → ℝ),
    φ.toFun n (fun a b => B (fun i => σ (a i)) (fun i => σ (b i))) = φ.toFun n B

def IsPosFn (φ : InvFun (𝓞 E)) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Nontrivial X], ∀ be ∈ levelForms H 1 X,
    (∀ y, y ≠ 0 → 0 < be y y) → 0 < φ.evalZ be

variable {H} {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def polOf (Z : Model Xo c β) (m : ℕ) (BD : EffCartierData Z.X) : LB Z.X :=
  GlobalTheory.CechPic.tens (lbPow (GlobalTheory.FlagMod.detOm Z) m) (GlobalTheory.CechPic.dual BD.lb)

def selfTor (Z : Model Xo c β) (h₁ : SmoothOfRelativeDimension D.dim (genStr Z)) (h₂ : FinalTheorems.Snc (genBdIdeal Z))
    (h₃ : ∀ x ∈ genBd Z, HasToricChart Z x) (BD : EffCartierData Z.X)
    (h₄ : ∀ x ∈ BD.idealSheaf.support, x ∉ abLocus Z.t.G) (h₅ : ∀ x ∈ genBd Z, genι Z x ∈ BD.idealSheaf.support)
    (m : ℕ) (hm : 0 < m) : TorModel Z where
  Z := Z
  b := 𝟙 _
  b_s := Category.id_comp _
  j_b := Category.comp_id _
  pull := ObjComp.sabMapId Z.t
  pull_univ T g₁ g₂ h₁ h₂ := by
    obtain rfl : g₁ = g₂ := Z.m0.cart.1.hom_ext h₁ h₂
    exact congrArg (g₁ ≫ ·) (Category.comp_id _)
  smooth := h₁
  snc := h₂
  toric := h₃
  lifts _ _ _ _ _ _ _ χ _ _ := ⟨χ, Category.comp_id _⟩
  BD := BD
  BD_supp := h₄
  BD_pos := h₅
  m0 := m
  torModel_multiplicity_pos := hm

end Defs

end GlobalTheory.TorRef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace

namespace GlobalTheory.FlagEmb

section Lin

variable {T : Type} (m : T → ℕ)

abbrev Let : Type := Σ τ : T, Fin (m τ)

abbrev CellVar : Type := Σ τ : T, {ij : Fin (m τ) × Fin (m τ) // ij.2 < ij.1}

abbrev Pm : Type := ∀ τ : T, Equiv.Perm (Fin (m τ))

variable {m} {S : Type} [CommRing S] {M : ℕ}

def cell (x : CellVar m → S) (τ : T) (i j : Fin (m τ)) : S :=
  if h : j < i then x ⟨τ, ⟨(i, j), h⟩⟩ else if i = j then 1 else 0

def cellVec {ι : Type} (c : Let m → ι → S) (w : Pm m) (x : CellVar m → S) : Let m → ι → S :=
  fun z => ∑ i, cell x z.1 i z.2 • c ⟨z.1, w z.1 i⟩

def wLet (w : Pm m) (z : Let m) : Let m := ⟨z.1, w z.1 z.2⟩

def Down {k : ℕ} (e : Fin k → Let m) : Prop :=
  Function.Injective e ∧ ∀ (l : Fin k) (j : Fin (m (e l).1)), j < (e l).2 → ∃ l', e l' = ⟨(e l).1, j⟩

def std (τ : T) (k : ℕ) (h : k ≤ m τ) : Fin k → Let m := fun l => ⟨τ, Fin.castLE h l⟩

theorem down_std (τ : T) (k : ℕ) (h : k ≤ m τ) : Down (std τ k h) := by
  refine ⟨fun a b hab => ?_, fun l j hj => ⟨⟨j, lt_trans hj l.2⟩, rfl⟩⟩
  have := congrArg (fun z : Let m => (z.2 : ℕ)) hab
  exact Fin.ext this


variable (m) in
abbrev En : Type := Σ k : ℕ, {e : Fin k → Let m // Down e}

abbrev stdEn (τ : T) (k : ℕ) (h : k ≤ m τ) : En m := ⟨k, std τ k h, down_std τ k h⟩

instance finite_en [Finite T] : Finite (En m) := by
  have := Fintype.ofFinite (Let m)
  refine Finite.of_surjective (fun a : Σ k : Fin (Fintype.card (Let m) + 1), {e : Fin k → Let m // Down e} =>
    (⟨a.1, a.2⟩ : En m)) ?_
  rintro ⟨k, e⟩
  have hk : k ≤ Fintype.card (Let m) := by simpa using Fintype.card_le_of_injective _ e.2.1
  exact ⟨⟨⟨k, Nat.lt_succ_of_le hk⟩, e⟩, rfl⟩

def plN (M k : ℕ) : ℕ := (M + 1) ^ k - 1

def plE (M k : ℕ) : Fin (plN M k + 1) ≃ (Fin k → Fin (M + 1)) :=
  (finCongr (Nat.sub_add_cancel (Nat.one_le_pow _ _ (Nat.succ_pos M)))).trans finFunctionFinEquiv.symm

def plk {ι : Type} {k : ℕ} (c : ι → Fin (M + 1) → S) (e : Fin k → ι) : Fin (plN M k + 1) → S :=
  fun q => (Matrix.of fun l l' => c (e l) (plE M k q l')).det

def lform {ι : Type} {k : ℕ} (D : ι → Fin (M + 1) → S) (ρ : Fin k → ι) : Fin (plN M k + 1) → S :=
  fun q => ∏ l, D (ρ l) (plE M k q l)


open Classical in
def LeftInv {ι : Type} (D c : ι → Fin M → S) : Prop := ∀ z z', ∑ r, D z r * c z' r = if z = z' then 1 else 0

def Tri {ι : Type} (c c' : Let m → ι → S) (d : Let m → S) : Prop :=
  ∀ z : Let m, c' z - d z • c z ∈ Submodule.span S ((fun j : Fin (m z.1) => c ⟨z.1, j⟩) '' {j | j < z.2})

def InBlock {ι : Type} (c c' : Let m → ι → S) : Prop :=
  ∀ z : Let m, c' z ∈ Submodule.span S (Set.range fun j : Fin (m z.1) => c ⟨z.1, j⟩)

theorem map_plk {ι : Type} {k : ℕ} {S' : Type} [CommRing S'] (φ : S →+* S') (c : ι → Fin (M + 1) → S) (e : Fin k → ι) :
    φ ∘ plk c e = plk (fun z => φ ∘ c z) e := by
  funext q
  simp only [plk, Function.comp_apply, RingHom.map_det]
  rfl

theorem map_cellVec {ι : Type} {S' : Type} [CommRing S'] (φ : S →+* S') (c : Let m → ι → S) (w : Pm m)
    (x : CellVar m → S) (z : Let m) : φ ∘ cellVec c w x z = cellVec (fun z => φ ∘ c z) w (φ ∘ x) z := by
  funext r
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cellVec, Function.comp_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  unfold cell
  split_ifs <;> simp

theorem LeftInv.map {ι : Type} {S' : Type} [CommRing S'] (φ : S →+* S') {D c : ι → Fin M → S} (h : LeftInv D c) :
    LeftInv (fun z => φ ∘ D z) (fun z => φ ∘ c z) := fun z z' => by
  have := congrArg φ (h z z')
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul] at this
  refine this.trans ?_
  split_ifs <;> simp

end Lin

section Geo

variable {O K : Type} [CommRing O] [Field K] (β : O →+* K) {X : Scheme.{0}} (s : X ⟶ Sp O) {T : Type} {m : T → ℕ}
  {M : ℕ} {B : Type} (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1))

structure IsCover (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) : Prop where
  ovr : ∀ b, (V b).2.fromSpec ≫ s = spMap ((α b).comp β)
  inv : ∀ b, LeftInv (D b) (c b)
  compat : ∀ (k : Type) [Field k] b b' (φ : Γ(X, (V b).1) →+* k) (φ' : Γ(X, (V b').1) →+* k),
    spMap φ ≫ (V b).2.fromSpec = spMap φ' ≫ (V b').2.fromSpec →
      InBlock (fun z => φ ∘ c b z) (fun z => φ' ∘ c b' z)


variable (m) in
abbrev CR (U : X.affineOpens) : Type := MvPolynomial (CellVar m) Γ(X, U.1)


variable (m) in
def cbase (U : X.affineOpens) : Sp (CR m U) ⟶ X := spMap (MvPolynomial.C : Γ(X, U.1) →+* CR m U) ≫ U.2.fromSpec

def uvec {U : X.affineOpens} (c : Let m → Fin (M + 1) → Γ(X, U.1)) (w : Pm m) : Let m → Fin (M + 1) → CR m U :=
  cellVec (fun z => MvPolynomial.C ∘ c z) w MvPolynomial.X

variable (c : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1))

structure HasPlk {P : Scheme.{0}} (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1))
    (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)) : Prop where
  base : ∀ b w, h b w ≫ p0 = cbase m (V b)
  plk : ∀ b w en, ∃ hu, h b w ≫ p en =
    pt ((MvPolynomial.C : _ →+* CR m (V b)).comp ((α b).comp β)) (plk (uvec (c b) w) en.2.1) hu

structure IsPlk {P : Scheme.{0}} (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1))
    (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)) : Prop extends HasPlk β V α c p0 p h where
  proj : IsProjOver (p0 ≫ s)
  ovr : ∀ en, p en ≫ PSpace.str _ _ = p0 ≫ s
  ext : ∀ (Z : Scheme.{0}) (a a' : Z ⟶ P), a ≫ p0 = a' ≫ p0 → (∀ en, a ≫ p en = a' ≫ p en) → a = a'

def IsCellOpen {P : Scheme.{0}} (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (U : X.affineOpens)
    (D : Let m → Fin (M + 1) → Γ(X, U.1)) (w : Pm m) (W : P.Opens) : Prop :=
  ∀ (k : Type) [Field k] (z : Sp k ⟶ P), Set.range z ⊆ W ↔ ∃ φ : Γ(X, U.1) →+* k, z ≫ p0 = spMap φ ≫ U.2.fromSpec ∧
    ∀ τ j hj (b : O →+* k) v hv, z ≫ p (stdEn τ j hj) = pt b v hv →
      ∑ q, φ (lform D (wLet w ∘ std τ j hj) q) * v q ≠ 0

end Geo

section Lie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

abbrev Tn (R : Type) [CommRing R] : Type := Sp (DualNumber R) ⟶ t.G.left


open GlobalTheory.FactorDepth in
theorem exists_comb {R : Type} [CommRing R] {x : Sp R ⟶ X} {n : ℕ} {u : Fin n → Tn t R} (hu : ∀ j, IsTanAtG t x (u j))
    (a : Fin n → R) : ∃ w, IsTanAtG t x w ∧ IsCombAtG t x u a w :=
  ⟨_, isTanAtG_of _ (combT_tan _ (fun j => ovT (hu j)) (fun j => smT_zero_ovT _) a),
    (isCombAtG_iff t x (fun j => ovT (hu j)) a _).2 rfl⟩


open GlobalTheory.FactorDepth in
theorem comb_unique {R : Type} [CommRing R] {x : Sp R ⟶ X} {n : ℕ} {u : Fin n → Tn t R} (hu : ∀ j, IsTanAtG t x (u j))
    {a : Fin n → R} {w w' : Tn t R} (h : IsCombAtG t x u a w) (h' : IsCombAtG t x u a w') : w = w' :=
  ((isCombAtG_iff t x (fun j => ovT (hu j)) a _).1 h).symm.trans ((isCombAtG_iff t x (fun j => ovT (hu j)) a _).1 h')

theorem comb_tan {R : Type} [CommRing R] {x : Sp R ⟶ X} {n : ℕ} {u : Fin n → Tn t R} (hu : ∀ j, IsTanAtG t x (u j))
    {a : Fin n → R} {w : Tn t R} (h : IsCombAtG t x u a w) : IsTanAtG t x w := by
  obtain ⟨w', h1, h2⟩ := exists_comb t hu a
  exact comb_unique t hu h2 h ▸ h1


variable {Dw : Datum H}

variable {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

end Lie

end GlobalTheory.FlagEmb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CombMatAddMul
set_option autoImplicit false

noncomputable section

open scoped Matrix

namespace GlobalTheory.PeriodFrame

open GlobalTheory.ShFam.Hor

def combMat {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε : Matrix (Fin g) (Fin r) ℚ) : Matrix (Fin g) (Fin g) ℂ :=
  Matrix.of fun k i => ∑ m, (ε i m : ℂ) * l m k

def perTau {n g r₀ r : ℕ} (a : ℕ) (ζ : (Fin n → ℂ) → Fin r₀ → Fin g → ℂ) (lam : (Fin n → ℂ) → Fin r → Fin g → ℂ)
    (α : Matrix (Fin g) (Fin r₀) ℚ) (φ : Matrix (Fin g) (Fin r) ℚ) (D : ℕ) (s : Fin n → ℂ) :
    Matrix (Fin g) (Fin g) ℂ :=
  (D : ℂ) • ((combMat (ζ (logExp a s)) α)⁻¹ * combMat (lam s) φ)

theorem combMat_comb {g r r' : ℕ} (w : Fin r' → Fin g → ℂ) (l : Fin r → Fin g → ℂ) (c : Matrix (Fin r') (Fin r) ℤ)
    (α : Matrix (Fin g) (Fin r') ℚ) (hw : ∀ i, w i = ∑ j, c i j • l j) :
    combMat w α = combMat l (α * c.map (Int.cast : ℤ → ℚ)) := by
  ext k i
  simp only [combMat, Matrix.of_apply, Matrix.mul_apply, Matrix.map_apply, hw, Finset.sum_apply, Pi.smul_apply,
    zsmul_eq_mul]
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => by
    simp only [Pi.mul_apply, Pi.intCast_apply]; ring

theorem combMat_add_mul {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ)
    (b : Matrix (Fin g) (Fin g) ℚ) :
    combMat l (φ + bᵀ * ε) = combMat l φ + combMat l ε * b.map (Rat.cast : ℚ → ℂ) := by
  ext k j
  simp only [combMat, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
  push_cast
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring

theorem combMat_shift {g r : ℕ} (l : Fin r → Fin g → ℂ) (ε φ : Matrix (Fin g) (Fin r) ℚ)
    (b : Matrix (Fin g) (Fin g) ℚ) (D : ℕ) (Bk : Matrix (Fin g) (Fin g) ℤ) (hP : IsUnit (combMat l ε).det)
    (hB : ∀ i j, (Bk i j : ℚ) = D * b i j) :
    (D : ℂ) • ((combMat l ε)⁻¹ * combMat l (φ + bᵀ * ε)) =
      (D : ℂ) • ((combMat l ε)⁻¹ * combMat l φ) + Bk.map (Int.cast : ℤ → ℂ) := by
  rw [combMat_add_mul, Matrix.mul_add, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.one_mul, smul_add]
  congr 1
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  have h := congrArg (Rat.cast : ℚ → ℂ) (hB i j)
  push_cast at h
  rw [h]

theorem shift_mem {n a : ℕ} (ha : a ≤ n) (k : Fin a) {s : Fin n → ℂ} (hs : s ∈ logDom n a) :
    s + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I) ∈ logDom n a ∧
      logExp a (s + Pi.single (Fin.castLE ha k) (2 * (Real.pi : ℂ) * Complex.I)) = logExp a s := by
  simp only [logDom, Set.mem_setOf_eq] at hs ⊢
  constructor
  · intro j
    have h := hs j
    by_cases hj : j = Fin.castLE ha k
    · subst hj
      have hk : ((Fin.castLE ha k : Fin n) : ℕ) < a := by simp [Fin.coe_castLE, k.isLt]
      simp only [hk, if_true] at h ⊢
      simpa [Pi.add_apply] using h
    · simpa [Pi.add_apply, Pi.single_eq_of_ne hj] using h
  · funext j
    by_cases hj : j = Fin.castLE ha k
    · subst hj
      have hk : ((Fin.castLE ha k : Fin n) : ℕ) < a := by simp [Fin.coe_castLE, k.isLt]
      simp only [logExp, hk, if_true, Pi.add_apply, Pi.single_eq_same]
      rw [Complex.exp_add, Complex.exp_two_pi_mul_I, _root_.mul_one]
    · simp [logExp, Pi.single_eq_of_ne hj]

end GlobalTheory.PeriodFrame
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueTangentOfValues
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO)
open GlobalTheory.LieVB GlobalTheory.Conormal GlobalTheory.VB GlobalTheory.LieVB.TangentSurj
open GlobalTheory.LB (resG_self)
open GlobalTheory.Twist (resM app_resM)
open GlobalTheory.QCoh (pullbackSections)

namespace GlobalTheory.TanFibre

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {π : Y ⟶ X} {e : X ⟶ Y} (he : e ≫ π = 𝟙 X)
  {x : Sp k ⟶ X} {v v' : (specO k (DualNumber k)).left ⟶ Y}

def form (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x) (we : sec (epsZero k) ≫ v = x ≫ e) :
    (Scheme.Modules.pullback x).obj (conormal e) ⟶ structureModule (Sp k) :=
  baseMap (sec_hom (epsZero k)) w we ≫ (epsIso k).hom

theorem form_d (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x) (we : sec (epsZero k) ≫ v = x ≫ e)
    {V : X.Opens} {W : Y.Opens} (h : V ≤ e ⁻¹ᵁ W) (f : Γ(Y, W)) {U : (Sp k).Opens} (hU : U ≤ x ⁻¹ᵁ V)
    (q : (specO k (DualNumber k)).hom ⁻¹ᵁ U ≤ v ⁻¹ᵁ W) (a b : Γ(Sp k, U))
    (H : v.appLE W _ q f = (specO k (DualNumber k)).hom.appLE U _ le_rfl a +
      (specO k (DualNumber k)).hom.appLE U _ le_rfl b * resG _ le_top (epsFn k)) :
    (form w we).app U (pullbackSections x _ hU (d he h f)) = b := by
  have hV : U ≤ sec (epsZero k) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ U :=
    (le_preimage_of_comp (sec_hom (epsZero k))).2 le_rfl
  refine (congrArg ((epsIso k).hom.app U) (baseMap_d he (sec_hom (epsZero k)) w we h hU hV q f)).trans ?_
  rw [H, map_add (f := _), d_base, zero_add, d_mul, d_base,
    smul_zero, add_zero, appLE_base (sec_hom _) _ _ le_rfl, resG_self, d_resG,
    ← resM_d _ (le_preimage_top _ ⊤) le_top, Scheme.Modules.Hom.app_smul, app_resM, epsIso_d]
  exact (congrArg (b * ·) (map_one (resG (Sp k) (le_top : U ≤ ⊤)))).trans (_root_.mul_one b)

theorem preimage_le (we : sec (epsZero k) ≫ v = x ≫ e) {U : (Sp k).Opens} {W : Y.Opens}
    (h : U ≤ x ⁻¹ᵁ e ⁻¹ᵁ W) : (specO k (DualNumber k)).hom ⁻¹ᵁ U ≤ v ⁻¹ᵁ W := by
  intro t ht
  obtain ⟨s, rfl⟩ := surjective_sec_epsZero t
  have h₁ : s ∈ (sec (epsZero k) ≫ (specO k (DualNumber k)).hom) ⁻¹ᵁ U := ht
  rw [sec_hom] at h₁
  have h₂ : s ∈ (x ≫ e) ⁻¹ᵁ W := h h₁
  rw [← we] at h₂
  exact h₂

theorem appLE_eq (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x) (we : sec (epsZero k) ≫ v = x ≫ e)
    {U : (Sp k).Opens} (hU : IsAffineOpen U) {W : Y.Opens} (h : U ≤ x ⁻¹ᵁ e ⁻¹ᵁ W) (f : Γ(Y, W)) :
    v.appLE W _ (preimage_le we h) f =
      (specO k (DualNumber k)).hom.appLE U _ le_rfl ((x ≫ e).appLE W U h f) +
        (specO k (DualNumber k)).hom.appLE U _ le_rfl
          ((form w we).app U (pullbackSections x _ h (d he le_rfl f))) * resG _ le_top (epsFn k) := by
  obtain ⟨⟨a, b⟩, E⟩ := (bijective_add_mul_epsFn k U hU).2 (v.appLE W _ (preimage_le we h) f)
  have hV : U ≤ sec (epsZero k) ⁻¹ᵁ (specO k (DualNumber k)).hom ⁻¹ᵁ U :=
    (le_preimage_of_comp (sec_hom (epsZero k))).2 le_rfl
  have hb := form_d he w we le_rfl f h (preimage_le we h) a b E.symm
  have ha : (x ≫ e).appLE W U h f = a := by
    have e' := congrArg ((sec (epsZero k)).appLE _ U hV) E
    simp only [map_add (f := _), map_mul] at e'
    rw [appLE_sec_epsZero_epsFn, mul_zero, add_zero, appLE_base (sec_hom _) _ _ le_rfl,
      resG_self, appLE_appLE we _ _ h] at e'
    exact e'.symm
  rw [ha, hb]
  exact E.symm


include he in
theorem eq_of_form_eq (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x) (we : sec (epsZero k) ≫ v = x ≫ e)
    (w' : v' ≫ π = (specO k (DualNumber k)).hom ≫ x) (we' : sec (epsZero k) ≫ v' = x ≫ e)
    (H : form w we = form w' we') : v = v' := by
  refine Scheme.hom_ext_of_forall _ _ fun t => ?_
  obtain ⟨W, hW, hW', -⟩ := QCoh.exists_affine_mem_le (U := ⊤)
    (e (x ((specO k (DualNumber k)).hom t))) trivial
  obtain ⟨U, hU, hU', h⟩ := QCoh.exists_affine_mem_le (U := x ⁻¹ᵁ e ⁻¹ᵁ W)
    ((specO k (DualNumber k)).hom t) hW'
  have hT : IsAffineOpen ((specO k (DualNumber k)).hom ⁻¹ᵁ U) := hU.preimage _
  have E : v.appLE W _ (preimage_le we h) = v'.appLE W _ (preimage_le we' h) := by
    ext f
    exact (appLE_eq he w we hU h f).trans (H ▸ (appLE_eq he w' we' hU h f).symm)
  refine ⟨(specO k (DualNumber k)).hom ⁻¹ᵁ U, hU', ?_⟩
  rw [← cancel_epi hT.isoSpec.inv, ← Category.assoc, ← Category.assoc, hT.isoSpec_inv_ι,
    ← hW.SpecMap_appLE_fromSpec _ hT (preimage_le we h),
    ← hW.SpecMap_appLE_fromSpec _ hT (preimage_le we' h), E]


include he in
theorem exists_form_eq [QuasiSeparated π]
    (L : (Scheme.Modules.pullback x).obj (conormal e) ⟶ structureModule (Sp k)) :
    ∃ (v : (specO k (DualNumber k)).left ⟶ Y) (w : v ≫ π = (specO k (DualNumber k)).hom ≫ x)
      (we : sec (epsZero k) ≫ v = x ≫ e), form w we = L := by
  let e' : Sp k ⟶ pullback π x := pullback.lift (x ≫ e) (𝟙 _) (by simp [he])
  have he' : e' ≫ pullback.snd π x = 𝟙 _ := pullback.lift_snd _ _ _
  have we' : e' ≫ pullback.fst π x = x ≫ e := pullback.lift_fst _ _ _
  have : QuasiCompact e :=
    have : QuasiCompact (e ≫ π) := he ▸ inferInstance
    .of_comp _ π
  have : QuasiCompact e' :=
    have : QuasiCompact (e' ≫ pullback.snd π x) := he' ▸ inferInstance
    .of_comp _ (pullback.snd π x)
  have := isIso_baseMap he he' (IsPullback.of_hasPullback π x) we'
  let β := baseMap he' (IsPullback.of_hasPullback π x).w we'
  let D := homEquivDer _ he' (inv β ≫ L)
  let u := deform (specO k (DualNumber k)).hom (epsFn k) (epsFn_sq k) D
  have w : (u ≫ pullback.fst π x) ≫ π = (specO k (DualNumber k)).hom ≫ x := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, deform_comp _ _ _ D he']
  have we : sec (epsZero k) ≫ u ≫ pullback.fst π x = x ≫ e := by
    rw [← Category.assoc, comp_deform _ _ (epsFn_sq k) D (sec_hom (epsZero k)) (epsZero_epsFn k), we']
  refine ⟨_, w, we, pullback_hom_ext he fun W f => ?_⟩
  have k₁ : x ⁻¹ᵁ e ⁻¹ᵁ W ≤ e' ⁻¹ᵁ pullback.fst π x ⁻¹ᵁ W := le_of_sq we' le_rfl le_rfl
  have k₂ := (specO k (DualNumber k)).hom.preimage_mono k₁
  let g := (pullback.fst π x).appLE W _ le_rfl f
  refine (form_d he w we le_rfl f le_rfl (preimage_le we le_rfl) (e'.appLE _ _ k₁ g) (val D k₁ g) ?_).trans ?_
  · have k₃ : (specO k (DualNumber k)).hom ⁻¹ᵁ x ⁻¹ᵁ e ⁻¹ᵁ W ≤ u ⁻¹ᵁ pullback.fst π x ⁻¹ᵁ W := k₂
    have e₁ : u.appLE _ _ k₃ g = resG _ k₂ (psi _ _ (epsFn_sq k) D _ g) :=
      deform_appLE _ _ (epsFn_sq k) D _ k₂ g
    rw [← appLE_appLE (f := u) (g := pullback.fst π x) rfl le_rfl k₃, e₁, psi_apply, map_add (f := _), map_mul, LB.resG_resG, DualPull.resG_appLE, DualPull.resG_appLE,
      ← DualPull.resG_appLE e' k₁ le_rfl, DualPull.appLE_resG,
      show val D k₁ g = resG _ k₁ (val D le_rfl g) from (D.res_app le_rfl k₁ g).symm, DualPull.appLE_resG]
  · have b := baseMap_d he he' (IsPullback.of_hasPullback π x).w we' le_rfl le_rfl k₁ le_rfl f
    have c : val D k₁ g = (inv β ≫ L).app _ (d he' k₁ g) := homEquivDer_app he' (inv β ≫ L) k₁ g
    rw [c, ← b]
    generalize pullbackSections x (conormal e) _ (d he _ f) = s
    have i : β ≫ inv β ≫ L = L := IsIso.hom_inv_id_assoc β L
    conv_rhs => rw [← i]
    rw [Scheme.Modules.Hom.comp_app β, AddCommGrpCat.comp_apply]

theorem exists_hom_of_isFrame {F : X.Modules} {n : ℕ} {s : Fin n → Γ(F, ⊤)} (hs : IsFrame s) (c : Fin n → Γ(X, ⊤)) :
    ∃ L : F ⟶ structureModule X, ∀ l, L.app ⊤ (s l) = c l := by
  refine ⟨homGlobalEquiv _ _ (∑ i, c i • hs.coord i), fun l => ?_⟩
  change dualApp (∑ i, c i • hs.coord i) le_rfl (s l) = c l
  have hsum (T : Finset (Fin n)) : dualApp (∑ i ∈ T, c i • hs.coord i) le_rfl (s l) = if l ∈ T then c l else 0 := by
    induction T using Finset.induction_on with
    | empty =>
      have := dualApp_smul (0 : Γ(X, ⊤)) (hs.coord l) le_rfl
      rw [zero_smul, map_zero, zero_smul] at this
      rw [Finset.sum_empty, this]
      simp
    | insert i T hi ih =>
      have := hs.dualApp_coord_frame i l le_rfl
      rw [Twist.resM_self] at this
      rw [Finset.sum_insert hi, dualApp_add, LinearMap.add_apply, ih, dualApp_smul, LinearMap.smul_apply, this,
        resG_self]
      by_cases hl : l = i
      · subst hl
        simp [hi]
      · simp [hl]
  simpa using hsum Finset.univ

theorem existsUnique_tanEv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (k : Type) [CommRing k] (x : Sp k ⟶ X) (V : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ V), ∀ (n : ℕ) (m : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)), GlobalTheory.VB.IsFrame m → ∀ c : Fin n → k, ∃! v : Sp (DualNumber k) ⟶ t.G.left, ∃ hv : IsTanAtG t x v, ∀ l, tanEv t hv h (m l) = c l := by
  intro E _ _ _ H X t k _ x V h n m hm c
  have := t.semi
  have hf : IsFrame fun l => pullbackSections x (omega t.G) h (m l) := by
    have := (hm.pullback x).res h
    exact (funext fun l => QCoh.res_pullbackSections x (omega t.G) le_rfl h (m l)) ▸ this
  obtain ⟨L, hL⟩ := exists_hom_of_isFrame hf fun l => cst k (c l)
  obtain ⟨v, w, we, hv⟩ := exists_form_eq (sec_hom η[t.G]) L
  have hv' : IsTanAtG t x v := ⟨w, we.trans (by
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left]
    rfl)⟩
  have hval (l) : tanEv t hv' h (m l) = c l :=
    (congrArg (fun (a : Γ(Sp k, ⊤)) => (Scheme.ΓSpecIso (.of k)).hom a)
      ((congr(($hv).app ⊤ _)).trans (hL l))).trans (Iso.inv_hom_id_apply _ _)
  refine ⟨v, ⟨hv', hval⟩, ?_⟩
  rintro u ⟨hu, hu'⟩
  refine eq_of_form_eq (sec_hom η[t.G]) hu.1 (epsZero_comp_of_isTanAtG t hu) w we (hom_ext_of_isFrame hf fun l => ?_)
  exact (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.injective ((hu' l).trans (hval l).symm)

end GlobalTheory.TanFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsProperToroidalModelStructureMap
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open TopologicalSpace
open Formalism.MainNotions.DIV.Cons (SCF intO)

namespace GlobalTheory.LocM.SharedLaws

section Top

variable {X : Type} [TopologicalSpace X] [NoetherianSpace X] [QuasiSober X]

theorem exists_finite_generic {F : Set X} (hF : IsClosed F) :
    ∃ G : Set X, G.Finite ∧ G ⊆ F ∧ ∀ x ∈ F, ∃ g ∈ G, g ⤳ x := by
  obtain ⟨S, hS, hc, hi, rfl⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  choose η hη using fun t (ht : t ∈ S) => QuasiSober.sober (hi t ht) (hc t ht)
  haveI := hS.to_subtype
  refine ⟨Set.range fun t : S => η t.1 t.2, Set.finite_range _, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨t.1, t.2, (hη t.1 t.2).mem⟩
  · rintro x ⟨t, ht, hx⟩
    exact ⟨_, ⟨⟨t, ht⟩, rfl⟩, (hη t ht).specializes hx⟩

theorem mem_of_maximal {x : X} (hx : ∀ x' : X, x' ⤳ x → x' = x) {U : Set X} (hU : IsOpen U) (hd : Dense U) :
    x ∈ U := by
  obtain ⟨G, hG, -, h⟩ := exists_finite_generic (isClosed_univ (X := X))
  have hC : IsClosed (⋃ g ∈ G \ {x}, closure ({g} : Set X)) :=
    (hG.subset Set.diff_subset).isClosed_biUnion fun _ _ => isClosed_closure
  obtain ⟨y, hy, hyU⟩ := hd.inter_open_nonempty _ hC.isOpen_compl ⟨x, fun hm => by
    obtain ⟨g, hg, hgx⟩ := Set.mem_iUnion₂.1 hm
    exact hg.2 (hx g (specializes_iff_mem_closure.2 hgx))⟩
  obtain ⟨g, hg, hgy⟩ := h y trivial
  by_cases e : g = x
  · exact (e ▸ hgy).mem_open hU hyU
  · exact absurd (Set.mem_iUnion₂.2 ⟨g, ⟨hg, e⟩, specializes_iff_mem_closure.1 hgy⟩) hy

end Top

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem mem_nonunits_V {l : Level H} (c : Coeff l) (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) :
    (p : c.F) ∈ (c.V W).nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or] at hW ⊢
  rcases hW with h | h
  · exact absurd (by exact_mod_cast h) hp
  · exact Or.inr fun h' => h (by simpa [Coeff.V] using h')

theorem isProper_toroidalModel_structureMap (Z : Mdl Y i₀) : IsProper Z.s := by
  have := isProper_str (Z.i.c.V W) Z.n
  unfold Pre.s
  infer_instance

theorem noetherianSpace (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) : NoetherianSpace Z.X := by
  haveI := Z.i.c.fin
  haveI : NumberField Z.i.c.F := {}
  haveI := (isDiscreteValuationRing_and_finite_residueField_of_numberField (Z.i.c.V W) hp
    (mem_nonunits_V Z.i.c hp hW)).1
  haveI := isProper_toroidalModel_structureMap Z
  haveI : IsLocallyNoetherian Z.X := LocallyOfFiniteType.isLocallyNoetherian Z.s
  haveI : CompactSpace Z.X := QuasiCompact.compactSpace_of_compactSpace Z.s
  haveI : IsNoetherian Z.X := {}
  infer_instance

theorem abP_of_isGenP (hp : p ≠ 0) (hW : (p : ℂ) ∈ W.nonunits) (Z : Mdl Y i₀) (x : Z.X) (hx : Z.isGenP x) :
    Z.abP x := by
  haveI := noetherianSpace hp hW Z
  have ho : IsOpen Z.opn := by
    rw [← Z.cover]
    exact isOpen_iUnion fun a => (Z.U a).1.2
  obtain ⟨z, hz⟩ := mem_of_maximal hx ho Z.dense
  have : (Y Z.i).jQ z ∈ pullback.fst (Y Z.i).s (spMap (Z.i.c.V W).subtype) ⁻¹' abLocus (Y Z.i).t.G := by
    rw [(Y Z.i).ab_gen]
    exact ⟨z, rfl⟩
  unfold Mdl.abP
  rw [← hz]
  exact this

end Free

end GlobalTheory.LocM.SharedLaws
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrNormPush
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LieMet MonObj

namespace GlobalTheory.ShFam.Pad.Pull

attribute [local instance] Over.cartesianMonoidalCategory

section Lin

variable {k V : Type} [Field k] [AddCommGroup V] [Module k V] {m : ℕ}

theorem lin_comp {u u' : Fin m → V} (A : Fin m → Fin m → k) (hA : ∀ j i, j < i → A j i = 0)
    (hu : ∀ j, u' j = ∑ i, A j i • u i) (d : Fin m → k) (j : Fin m) (hd : ∀ i, j < i → d i = 0) :
    ∃ e : Fin m → k, (∀ i, j < i → e i = 0) ∧ e j = d j * A j j ∧ ∑ i, d i • u' i = ∑ i, e i • u i := by
  refine ⟨fun i => ∑ l, d l * A l i, fun i hi => Finset.sum_eq_zero fun l _ => ?_, ?_, ?_⟩
  · rcases lt_or_ge j l with h | h
    · rw [hd l h, zero_mul]
    · rw [hA l i (h.trans_lt hi), mul_zero]
  · refine Finset.sum_eq_single j (fun l _ hl => ?_) (by simp)
    rcases lt_or_gt_of_ne hl with h | h
    · rw [hA l j h, mul_zero]
    · rw [hd l h, zero_mul]
  · simp only [hu, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm

theorem lin_symm {u u' : Fin m → V} (hi : ∀ c c' : Fin m → k, ∑ i, c i • u' i = ∑ i, c' i • u' i → c = c')
    (A : Fin m → Fin m → k) (hA : ∀ j i, j < i → A j i = 0) (hu : ∀ j, u' j = ∑ i, A j i • u i) :
    ∃ B : Fin m → Fin m → k, (∀ j i, j < i → B j i = 0) ∧ (∀ j, u j = ∑ i, B j i • u' i) ∧ ∀ j, A j j * B j j = 1 := by
  classical
  let M : Matrix (Fin m) (Fin m) k := Matrix.of A
  have key : ∀ d : Fin m → k, ∑ i, d i • u' i = ∑ i, Matrix.vecMul d M i • u i := fun d => by
    simp only [hu, Finset.smul_sum, smul_smul, Finset.sum_smul, Matrix.vecMul, dotProduct, M, Matrix.of_apply]
    exact Finset.sum_comm
  have hM : IsUnit M := Matrix.vecMul_injective_iff_isUnit.1 fun d d' h => hi _ _ (by
    rw [key, key]; exact congrArg (fun c : Fin m → k => ∑ i, c i • u i) h)
  obtain ⟨I⟩ := hM.nonempty_invertible
  have ht : M.BlockTriangular OrderDual.toDual := fun j i h => hA j i h
  have hB : ∀ j i, j < i → M⁻¹ j i = 0 := fun j i h => Matrix.blockTriangular_inv_of_blockTriangular ht h
  have h2 : ∀ j, u j = ∑ i, M⁻¹ j i • u' i := fun j => by
    rw [key, show Matrix.vecMul (M⁻¹ j) M = (M⁻¹ * M) j from rfl, Matrix.inv_mul_of_invertible]
    simp [Matrix.one_apply]
  refine ⟨fun j i => M⁻¹ j i, hB, h2, fun j => ?_⟩
  obtain ⟨e, -, he, h⟩ := lin_comp (fun j i => M⁻¹ j i) hB h2 (A j) j (hA j)
  have := hi e (Pi.single j 1) (by rw [← h, ← hu]; simp [Pi.single_apply])
  rw [← he, this, Pi.single_eq_same]

end Lin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X)

section Tan

variable {k : Type} [Field k] (x : Sp k ⟶ X) {m : ℕ}

def Ind (u : Fin m → (Sp (DualNumber k) ⟶ t.G.left)) : Prop :=
  (∀ i, IsTanAtG t x (u i)) ∧ ∀ cf cf' w, IsCombAtG t x u cf w → IsCombAtG t x u cf' w → cf = cf'

def Tri (u u' : Fin m → (Sp (DualNumber k) ⟶ t.G.left)) : Prop :=
  ∀ j, ∃ cf : Fin m → k, (∀ i, j < i → cf i = 0) ∧ IsCombAtG t x u cf (u' j)

variable {t x} {u u' u'' : Fin m → (Sp (DualNumber k) ⟶ t.G.left)}

theorem comb_iff (U : Fin m → TanM x t.G) (a : Fin m → k) (w : Sp (DualNumber k) ⟶ t.G.left) :
    IsCombAtG t x (fun i => (tv (U i)).left) a w ↔ w = (tv (∑ i, a i • U i)).left := by
  have h := (GlobalTheory.LieMet.isComb_iff U a _).2 rfl
  refine ⟨fun h' => ?_, fun e => e ▸ h⟩
  exact ((isCombAtG_iff t x (fun i => tv (U i)) a _).1 h').symm.trans
    ((isCombAtG_iff t x (fun i => tv (U i)) a _).1 h)

theorem exists_tan (h : ∀ i, IsTanAtG t x (u i)) : ∃ U : Fin m → TanM x t.G, u = fun i => (tv (U i)).left :=
  ⟨fun i => tanOf (h i), rfl⟩

theorem Tri.comp (hu : ∀ i, IsTanAtG t x (u i)) (hu' : ∀ i, IsTanAtG t x (u' i)) (h : Tri t x u u') {d : Fin m → k}
    {j : Fin m} (hd : ∀ i, j < i → d i = 0) {w : Sp (DualNumber k) ⟶ t.G.left} (hw : IsCombAtG t x u' d w) :
    ∃ c e : Fin m → k, IsCombAtG t x u c (u' j) ∧ (∀ i, j < i → e i = 0) ∧ e j = d j * c j ∧ IsCombAtG t x u e w := by
  obtain ⟨U, rfl⟩ := exists_tan hu
  obtain ⟨U', rfl⟩ := exists_tan hu'
  choose A hA hc using h
  obtain ⟨e, h1, h2, h3⟩ := lin_comp A hA (fun j => (GlobalTheory.LieMet.isComb_iff U _ _).1 (hc j)) d j hd
  exact ⟨A j, e, hc j, h1, h2, (comb_iff _ _ _).2 (h3 ▸ (comb_iff _ _ _).1 hw)⟩

theorem Tri.trans (hu : ∀ i, IsTanAtG t x (u i)) (hu' : ∀ i, IsTanAtG t x (u' i)) (h : Tri t x u u')
    (h' : Tri t x u' u'') : Tri t x u u'' := fun j => by
  obtain ⟨d, hd, hw⟩ := h' j
  obtain ⟨-, e, -, h1, -, h2⟩ := h.comp hu hu' hd hw
  exact ⟨e, h1, h2⟩

theorem Tri.symm (hu : Ind t x u) (hu' : Ind t x u') (h : Tri t x u u') : Tri t x u' u ∧
    ∀ j c d, IsCombAtG t x u c (u' j) → IsCombAtG t x u' d (u j) → c j * d j = 1 := by
  obtain ⟨U, rfl⟩ := exists_tan hu.1
  obtain ⟨U', rfl⟩ := exists_tan hu'.1
  choose A hA hc using h
  obtain ⟨B, h1, h2, h3⟩ := lin_symm (u := U) (u' := U') (fun c c' e => hu'.2 c c' _ ((GlobalTheory.LieMet.isComb_iff _ _ _).2 rfl)
    ((GlobalTheory.LieMet.isComb_iff _ _ _).2 e)) A hA fun j => (GlobalTheory.LieMet.isComb_iff U _ _).1 (hc j)
  refine ⟨fun j => ⟨B j, h1 j, (GlobalTheory.LieMet.isComb_iff _ _ _).2 (h2 j)⟩, fun j c d hc' hd => ?_⟩
  rw [hu.2 _ _ _ hc' (hc j), hu'.2 _ _ _ hd ((GlobalTheory.LieMet.isComb_iff _ _ _).2 (h2 j)), h3]

theorem Tri.diag (hu : Ind t x u) (hu' : Ind t x u') (h : Tri t x u u') {j : Fin m} {c : Fin m → k}
    (hc : IsCombAtG t x u c (u' j)) : c j ≠ 0 ∧ ∀ i, j < i → c i = 0 := by
  obtain ⟨h1, h2⟩ := h.symm hu hu'
  obtain ⟨d, -, hd⟩ := h1 j
  obtain ⟨c', h3, h4⟩ := h j
  exact ⟨left_ne_zero_of_mul_eq_one (h2 j c d hc hd), hu.2 _ _ _ hc h4 ▸ h3⟩

end Tan

section Norm

variable {t} {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] {x : Sp C ⟶ X} {m : ℕ}
  {u u' : Fin m → (Sp (DualNumber C) ⟶ t.G.left)}


end Norm

end GlobalTheory.ShFam.Pad.Pull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramTransformOfCoordinateChangeImports
set_option autoImplicit false

noncomputable section

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FramePairGram

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def ent (M : Matrix (Fin r) (Fin r) ℂ) (a b : ℕ) : ℂ := if h : a < r ∧ b < r then M ⟨a, h.1⟩ ⟨b, h.2⟩ else 0


open Classical in
def coef (X : Data E r) (x x' : Frame X.Ψ r) (ρ : E →+* ℂ) (b i : ℕ) : ℂ :=
  if h : ρ ∈ X.Ψ then ent ((mat x' ⟨ρ, h⟩)⁻¹ * mat x ⟨ρ, h⟩) (X.p0 + b) (X.p0 + i)
  else if h' : conjEmb ρ ∈ X.Ψ then ent ((mat x ⟨_, h'⟩)⁻¹ * mat x' ⟨_, h'⟩) (X.p0 - 1 - i) (X.p0 - 1 - b)
  else 0

end GlobalTheory.FramePairGram
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtDatLIntegral
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

theorem atDat_lIntegral : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram →
    GlobalTheory.Mem.Top.Bl.AtDat fun _ B f T w Z hX Wt z => z.R.toRealDat.LIntegral := fun _ _ _ =>
  StepW.of_all fun _ _ _ _ _ _ _ _ _ _ _ z _ _ _ hG i =>
    ⟨z.geo.fw.ks i, GlobalTheory.GoodLat.mkFull_of_tie z.geo.fw hG.latFull i,
      GlobalTheory.RealGeoIn.mkStable_of_rhoGeo z.geo.fw z.geo.pins z.geo.rhoGeo i⟩

end GlobalTheory.Mem.Top.Bl
end
