module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsFinSetSplitPlacesCoprimeConductor
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteAdeleBaseChangeEquiv
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeGal

namespace GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols

variable {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I]

def lamF (χ : HChar E) (s : ℕ) (y : (Af E)ˣ) : ℂ := (finPart χ y : ℂ) * ((modF y ^ s : ℝ) : ℂ)

def IsTwistedSum (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (χ : HChar E) (ψ : PicO c →* ℂˣ) (T : ℂ) : Prop :=
  Finite (PicO c) ∧ ∃ S : PicO c → ℂ → ℂ, (∀ q, IsLatSum φ (2 * s) κ (lattice c q.out) (S q)) ∧
    T = ∑ᶠ q : PicO c, ((ψ q : ℂˣ) : ℂ)⁻¹ * (lamF χ s q.out)⁻¹ * S q 0

def conjChar {c : Ideal (OF E)} (g : ℂ ≃+* ℂ) (ψ : PicO c →* ℂˣ) : PicO c →* ℂˣ :=
  (Units.map g.toRingHom.toMonoidHom).comp ψ

def classOf (K : Type) [Field K] [NumberField K] [Algebra K E] (c : Ideal (OF E)) (t : (Af K)ˣ) : PicO c :=
  QuotientGroup.mk (Units.map (GlobalTheory.AdeleBaseChange.adMap K E).toMonoidHom t)

def IsSymbol {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] (art : Ideles K →* Gab K Ω) (t : (Af K)ˣ)
    (σ : Formalism.ConjugateSelfDual.G K Ω) : Prop :=
  (art (finIdele K t))⁻¹ = toAb K Ω σ

def ToricRatioConjugates : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (K : Type) [Field K] [NumberField K] [Algebra K E] (d : ℕ) (δ : K) (ι : K →+* ℂ)
    (I : Type) [Fintype I] (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ)
    (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E),
    UnramFin E → Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = ι) →
    1 ≤ s → (∀ i, 1 ≤ κ i) → IsBaseCond 𝔣 → IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → IsValChar φ s κ 𝔣 ∅ χ →
    ∃ (T₀ : ℂ) (T : (PicO (condQ 𝔣 Q) →* ℂˣ) → ℂ),
      IsToricSum φ s κ 𝔣 χ T₀ ∧ T₀ ≠ 0 ∧ (∀ ψ, IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ (T ψ)) ∧
      (∀ ψ, IsAlgebraic ℚ (T ψ / T₀)) ∧
      ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (j : Ω →+* ℂ) (art : Ideles K →* Gab K Ω),
        j.comp (algebraMap K Ω) = ι → IsGlobalArtin art →
        ∀ (g : ℂ ≃+* ℂ) (σ : Formalism.ConjugateSelfDual.G K Ω) (t : (Af K)ˣ),
          (∀ i x, g (φ i x) = φ i x) → (∀ y, g (lamF χ s y) = lamF χ s y) →
          (∀ x, j (σ x) = g (j x)) → IsSymbol art t σ →
          ∀ ψ : PicO (condQ 𝔣 Q) →* ℂˣ,
            g (T ψ / T₀) =
              ((conjChar g ψ (classOf K (condQ 𝔣 Q) t) : ℂˣ) : ℂ)⁻¹ * (T (conjChar g ψ) / T₀) ∧
            IsOfFinOrder (conjChar g ψ (classOf K (condQ 𝔣 Q) t))

@[simp] theorem coe_conjChar {c : Ideal (OF E)} (g : ℂ ≃+* ℂ) (ψ : PicO c →* ℂˣ) (q : PicO c) :
    ((conjChar g ψ q : ℂˣ) : ℂ) = g (ψ q) := rfl

theorem IsTwistedSum.unique {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {c : Ideal (OF E)} {χ : HChar E} {ψ : PicO c →* ℂˣ}
    {T T' : ℂ} (h : IsTwistedSum φ s κ c χ ψ T) (h' : IsTwistedSum φ s κ c χ ψ T') : T = T' := by
  obtain ⟨_, S, hS, rfl⟩ := h
  obtain ⟨_, S', hS', rfl⟩ := h'
  have : S = S' := funext fun q => (hS q).unique (hS' q)
  rw [this]

theorem isTwistedSum_iff_isToricSum {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {c : Ideal (OF E)} {χ ξ : HChar E}
    {ψ : PicO c →* ℂˣ} (h : ∀ y, finPart ξ y = ψ (QuotientGroup.mk y)) (T : ℂ) :
    IsTwistedSum φ s κ c χ ψ T ↔ IsToricSum φ s κ c (χ * ξ) T := by
  have key : ∀ q : PicO c, ((ψ q : ℂˣ) : ℂ)⁻¹ * (lamF χ s q.out)⁻¹ =
      ((finPart (χ * ξ) q.out : ℂ) * ((modF q.out ^ s : ℝ) : ℂ))⁻¹ := fun q => by
    rw [finPart_mul, h, QuotientGroup.out_eq', lamF, Units.val_mul]
    simp only [mul_inv]
    ring
  simp only [IsTwistedSum, IsToricSum, key]

end GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedFlatCoordinates
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates

section Tangent

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {R : Type} [CommRing R]

abbrev epsAt (x : Sp R ⟶ S) : Over S := Over.mk (spMap (algebraMap R (DualNumber R)) ≫ x)

def IsEigenTangent {O : Type} [CommRing O] (act : OAct O G) (x : Sp R ⟶ S) (χ : O →+* R)
    (v : epsAt x ⟶ G) : Prop :=
  spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ v.left = (1 : Over.mk x ⟶ G).left ∧
    ∀ a, (v ≫ act.act a).left = spMap (epsScaleR (χ a)) ≫ v.left

def IsCombination (x : Sp R ⟶ S) {n : ℕ} (c : Fin n → R) (v : Fin n → (Sp (DualNumber R) ⟶ G.left))
    (w : epsAt x ⟶ G) : Prop :=
  ∃ u : Fin n → (epsAt x ⟶ G), (∀ i, (u i).left = spMap (epsScaleR (c i)) ≫ v i) ∧ w = (List.ofFn u).prod

def IsEigenBasis {O : Type} [CommRing O] (act : OAct O G) (x : Sp R ⟶ S) (χ : O →+* R) {n : ℕ}
    (v : Fin n → (epsAt x ⟶ G)) : Prop :=
  (∀ i, IsEigenTangent act x χ (v i)) ∧
    ∀ w, IsEigenTangent act x χ w → ∃! c : Fin n → R, IsCombination x c (fun i => (v i).left) w

end Tangent

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def embCoeff (c : Coeff l) (τ : E →+* ℂ) : E →+* c.F := τ.codRestrict c.F.toSubfield (c.conj τ)

def chr (c : Coeff l) (τ : E →+* ℂ) {R : Type} [CommRing R] (j : c.F →+* R) : 𝓞 E →+* R :=
  (j.comp (embCoeff c τ)).comp (algebraMap (𝓞 E) E)

abbrev genFibre (Y : Model Xo c β) : Scheme.{0} := pullback Y.s (spMap β)

def compactification (Y : Model Xo c β) (Xc : (Xo.XF c).Opens) : Set (genFibre Y) :=
  closure (Y.jQ '' (Xc : Set (Xo.XF c)))

structure Framed (Y : Model Xo c β) (Xc : (Xo.XF c).Opens) (τ : E →+* ℂ) (R : Type) [CommRing R]
    (j : c.F →+* R) where

  x : Sp R ⟶ genFibre Y
  x_over : x ≫ pullback.snd _ _ = spMap j
  x_mem : Set.range x ⊆ compactification Y Xc

  v : Fin D.p → (epsAt (x ≫ pullback.fst _ _) ⟶ Y.t.G)

  w : Fin D.q → (epsAt (x ≫ pullback.fst _ _) ⟶ Y.t.G)
  v_basis : IsEigenBasis Y.t.act (x ≫ pullback.fst _ _) (chr c τ j) v
  w_basis : IsEigenBasis Y.t.act (x ≫ pullback.fst _ _) (chr c (conjEmb τ) j) w

def Rule (Y : Model Xo c β) (Xc : (Xo.XF c).Opens) (τ : E →+* ℂ) : Type 1 :=
  ∀ (R : Type) [CommRing R] (j : c.F →+* R), Framed Y Xc τ R j → R

variable {Y : Model Xo c β} {Xc : (Xo.XF c).Opens} {τ : E →+* ℂ}

instance : AddCommGroup (Rule Y Xc τ) :=
  @Pi.addCommGroup _ _ fun _ => @Pi.addCommGroup _ _ fun _ => @Pi.addCommGroup _ _ fun _ =>
    @Pi.addCommGroup _ _ fun _ => inferInstance

instance : SMul c.F (Rule Y Xc τ) := ⟨fun t s R _ j a => j t * s R j a⟩

theorem Rule.add_apply (s s' : Rule Y Xc τ) (R : Type) [CommRing R] (j : c.F →+* R)
    (a : Framed Y Xc τ R j) : (s + s') R j a = s R j a + s' R j a := rfl

theorem Rule.zero_apply (R : Type) [CommRing R] (j : c.F →+* R)
    (a : Framed Y Xc τ R j) : (0 : Rule Y Xc τ) R j a = 0 := rfl

theorem Rule.smul_apply (t : c.F) (s : Rule Y Xc τ) (R : Type) [CommRing R] (j : c.F →+* R)
    (a : Framed Y Xc τ R j) : (t • s) R j a = j t * s R j a := rfl

instance : Module c.F (Rule Y Xc τ) where
  one_smul s := by funext R _ j a; simp [Rule.smul_apply]
  mul_smul t t' s := by funext R _ j a; simp [Rule.smul_apply, _root_.mul_assoc]
  smul_zero t := by funext R _ j a; simp [Rule.smul_apply, Rule.zero_apply]
  smul_add t s s' := by funext R _ j a; simp [Rule.smul_apply, Rule.add_apply, mul_add]
  add_smul t t' s := by funext R _ j a; simp [Rule.smul_apply, Rule.add_apply, add_mul]
  zero_smul s := by funext R _ j a; simp [Rule.smul_apply, Rule.zero_apply]

def IsChange {R R' : Type} [CommRing R] [CommRing R'] {j : c.F →+* R} {j' : c.F →+* R'}
    (a : Framed Y Xc τ R j) (a' : Framed Y Xc τ R' j') (f : R →+* R')
    (M : Matrix (Fin D.p) (Fin D.p) R') (N : Matrix (Fin D.q) (Fin D.q) R') : Prop :=
  f.comp j = j' ∧ a'.x = spMap f ≫ a.x ∧
    (∀ i, IsCombination _ (M i) (fun k => spMap (Chart.dualMapR f) ≫ (a.v k).left) (a'.v i)) ∧
    ∀ i, IsCombination _ (N i) (fun k => spMap (Chart.dualMapR f) ≫ (a.w k).left) (a'.w i)

def sections (Y : Model Xo c β) (Xc : (Xo.XF c).Opens) (τ : E →+* ℂ) : Submodule c.F (Rule Y Xc τ) where
  carrier := {s | ∀ (R R' : Type) [CommRing R] [CommRing R'] (j : c.F →+* R) (j' : c.F →+* R')
    (a : Framed Y Xc τ R j) (a' : Framed Y Xc τ R' j') (f : R →+* R')
    (M : Matrix (Fin D.p) (Fin D.p) R') (N : Matrix (Fin D.q) (Fin D.q) R'),
    IsChange a a' f M N → s R' j' a' * M.det = f (s R j a) * N.det}
  add_mem' := by
    intro s s' hs hs' R R' _ _ j j' a a' f M N h
    rw [Rule.add_apply, Rule.add_apply, add_mul, map_add (f := _), add_mul, hs R R' j j' a a' f M N h,
      hs' R R' j j' a a' f M N h]
  zero_mem' := by
    intro R R' _ _ j j' a a' f M N h
    simp [Rule.zero_apply]
  smul_mem' := by
    intro t s hs R R' _ _ j j' a a' f M N h
    rw [Rule.smul_apply, Rule.smul_apply, map_mul, _root_.mul_assoc, _root_.mul_assoc, hs R R' j j' a a' f M N h,
      ← h.1, RingHom.comp_apply]

def VanishesNowhere (s : Rule Y Xc τ) : Prop :=
  ∀ (R : Type) [CommRing R] (j : c.F →+* R) (a : Framed Y Xc τ R j), IsUnit (s R j a)

def IsDirection (Y : Model Xo c β) (y : Sp ℂ ⟶ Xo.XF c) {g : ℕ}
    (e : (Fin g → ℂ) → (Sp ℂ ⟶ Xo.univ.t.G.left)) (V : Fin g → ℂ)
    (v : Sp (DualNumber ℂ) ⟶ Y.t.G.left) : Prop :=
  ∃ v₀ : epsAt y ⟶ Y.oF.t.G, v₀.left ≫ Y.m.φ = v ∧ IsDerivAt0 e V (v₀.left ≫ Y.m0.toSABMap.φ)

def flatCoord {g p q : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z : Fin q ⊕ Fin p → Fin g → ℂ)
    (W : Fin q → Fin g → ℂ) (C : Fin q ⊕ Fin p → Fin p → ℂ) : ℂ :=
  Matrix.det (Matrix.of fun k => Sum.elim (fun b => -(Real.pi : ℂ) * hermForm Hm (W b) (z k)) (C k) :
    Matrix (Fin q ⊕ Fin p) (Fin q ⊕ Fin p) ℂ)


open Classical in
def IsHorizontal (sig : Rule Y Xc τ) : Prop :=
  ∀ (s : c.F →+* ℂ), s (IntermediateField.inclusion c.le (baseKA l).ρ) = H.rt0 →
  ∀ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H D.p D.q ty →
  ∀ (U : FamilyUnif Xo (s.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i : Fin U.n)
    (x : Fin D.q ⊕ Fin D.p → (U.Di i).La), LinearIndependent (𝓞 E) x →
  ∃ κ : ℂ, κ ≠ 0 ∧
    ∀ (P : (U.Di i).La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), IsPeriod (U.Di i) ty P →
      Hm.IsHermitian → (∀ a b, (hermForm Hm (P a) (P b)).im = (U.Di i).EF a b) →
    ∀ (y : Sp ℂ ⟶ Xo.XF c) (a : Framed Y Xc τ ℂ s), y ≫ pullback.fst _ _ = U.u i P → a.x = y ≫ Y.jQ →
    ∀ (V : Fin D.p → Fin g → ℂ) (W : Fin D.q → Fin g → ℂ) (C : Fin D.q ⊕ Fin D.p → Fin D.p → ℂ),
      (∀ b, IsDirection Y y (fun z => (U.ex i P z).left) (V b) (a.v b).left) →
      (∀ b, IsDirection Y y (fun z => (U.ex i P z).left) (W b) (a.w b).left) →
      (∀ k n, (if ty n = s.comp (embCoeff c τ) then P (x k) n else 0) = ∑ b, C k b * V b n) →
      sig ℂ s a = κ * flatCoord Hm (fun k => P (x k)) W C

end GlobalTheory.IndefiniteRowSideFullHecke.FramedFlatCoordinates
end
end
