module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevelLiftIsLiftPrincipalLevelDatumRealisation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulMemOfMemSpan
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassesAt

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

def IsTest (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} (Xw : X.Opens) (yb : Sp 𝓞_ℂ_[p] ⟶ X) : Prop :=
  (∃ (T : CDVR) (kO : T.V →+* 𝓞_ℂ_[p]) (yT : Sp T.V ⟶ X), T.FinRes ∧ Function.Injective kO ∧ spMap kO ≫ yT = yb) ∧
    Set.range (spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb) ⊆ Xw

def GeomIrr {V : Type} [CommRing V] {X : Scheme.{0}} (s : X ⟶ Sp V) (Xw : X.Opens) : Prop :=
  ∀ (k : Type) [Field k] (f : V →+* k), Function.Injective f → IrreducibleSpace ↑(pullback (Xw.ι ≫ s) (spMap f))


section Minors

variable {R V J : Type} [CommRing R] [CommRing V] {N g m : ℕ}

def pairDet (h U : Fin m → Fin g → R) : R := (Matrix.of fun k k' : Fin m => ∑ b, h k' b * U k b).det

def covec (β : V →+* R) (T : J → Fin N → V) (h : Fin N → Fin g → R) (I : Fin m → J) : Fin m → Fin g → R :=
  fun k b => ∑ a, β (T (I k) a) * h a b

end Minors

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

def embV {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (σ : E →+* ℂ) : 𝓞 E →+* c.V W :=
  (embK c σ).codRestrict (c.V W).toSubring fun a => by
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff (R := c.V W) (K := c.F).1
      ((map_isIntegral_int (embK c σ) (RingOfIntegers.isIntegral a)).tower_top)
    exact hy ▸ y.2

section Lie

variable {X : Scheme.{0}} (t : SAB H X) {g m : ℕ}

def IsEigG {S : Type} [CommRing S] (σ : 𝓞 E →+* S) (u : Sp (DualNumber S) ⟶ t.G.left) : Prop :=
  ∀ a, u ≫ (t.act.act a).left = spMap (epsMul (σ a)) ≫ u

def EigRowsAt {S : Type} [CommRing S] (x : Sp S ⟶ X) (σ : 𝓞 E →+* S) (e : Fin g → (Sp (DualNumber S) ⟶ t.G.left))
    (U : Fin m → Fin g → S) : Prop :=
  ∀ k u, IsCombAtG t x e (U k) u → IsEigG t σ u

def EigAt {S : Type} [CommRing S] (x : Sp S ⟶ X) (σ : 𝓞 E →+* S) (e : Fin g → (Sp (DualNumber S) ⟶ t.G.left))
    (U : Fin g → Fin g → S) : Prop :=
  EigRowsAt t x σ e U ∧
    ∀ w v, IsCombAtG t x e w v → IsEigG t σ v → ((discr E : ℤ) : S) • w ∈ Submodule.span S (Set.range U)

def bcV {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) :
    Fin g → (Sp (DualNumber S) ⟶ t.G.left) := fun i => spMap (dualMap φ) ≫ e i

def EigFam {R : Type} [CommRing R] (x : Sp R ⟶ X) (σ : 𝓞 E →+* R) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left))
    (U : Fin g → Fin g → R) : Prop :=
  ∀ (S : Type) [CommRing S] (φ : R →+* S), EigAt t (spMap φ ≫ x) (φ.comp σ) (bcV t φ e) fun k b => φ (U k b)

end Lie

abbrev Ind (Dw : Datum H) (τ : E →+* ℂ) : Type := Fin (Dw.mult τ) ⊕ Fin (Dw.mult (conjEmb τ))


section Model

variable {l l' : Level H} {Xo : Moduli Dw l} {Xo' : Moduli Dw l'} {c : Coeff l} {c' : Coeff l'} {W : ValuationSubring ℂ}
  (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c) (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _))

def OverIncl (hle : c.F ≤ c'.F) : Prop :=
  r ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hle).toRingHom

def IsCover (hle : c.F ≤ c'.F) (Z : Comp Xo c) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ) (Xw : Y.X.Opens) : Prop :=
  OverIncl r hle ∧ (∀ x : c.F, (x : ℂ) ∈ W ↔ la.valuation c.F x ≤ 1) ∧ (p : ℂ) ∈ W.nonunits ∧
  (p : c'.F) ∈ (c'.V W).nonunits ∧ (Xw : Set Y.X) ⊆ Set.range Y.j ∧ Xw ≤ Y.X.basicOpen (p : Γ(Y.X, ⊤)) ∧
  (∀ z, Y.j z ∈ Xw → r z ∈ (Z : Set (Xo.XF c))) ∧ GeomIrr Y.s Xw ∧
  ∀ (k : Type) [Field k] [IsAlgClosed k] (fK : c'.F →+* k) (x : Sp k ⟶ Xo.XF c),
    x ≫ pullback.snd _ _ = spMap (fK.comp (IntermediateField.inclusion hle).toRingHom) →
    Set.range x ⊆ (Z : Set (Xo.XF c)) →
    ∃ yy : Sp k ⟶ Xo'.XF c', yy ≫ pullback.snd _ _ = spMap fK ∧ yy ≫ r = x ∧ Set.range (yy ≫ Y.j) ⊆ Xw

def GVal (τ : E →+* ℂ) (f : Rul Xo c) {k : Type} [Field k] [Algebra c.F k] (yy : Sp k ⟶ Xo'.XF c') {g : ℕ}
    (e : Fin g → (Sp (DualNumber k) ⟶ Y.t.G.left)) (U₁ : Fin (Dw.mult τ) → Fin g → k)
    (U₂ : Fin (Dw.mult (conjEmb τ)) → Fin g → k) (fv : k) : Prop :=
  ∀ y : FrPt Xo c k, Tested y → GlobalTheory.AllWt.ptF y = yy ≫ r →
    ∀ (w₁ : Fin (Dw.mult τ) → (Sp (DualNumber k) ⟶ Y.oF.t.G.left))
      (w₂ : Fin (Dw.mult (conjEmb τ)) → (Sp (DualNumber k) ⟶ Y.oF.t.G.left))
      (g₁ : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) k)
      (g₂ : Matrix (Fin (Dw.mult (conjEmb τ))) (Fin (Dw.mult (conjEmb τ))) k),
      (∀ i, IsCombAtG Y.t (yy ≫ Y.j) e (U₁ i) (w₁ i ≫ Y.m.φ)) → (∀ i, IsCombAtG Y.t (yy ≫ Y.j) e (U₂ i) (w₂ i ≫ Y.m.φ)) →
      (∀ i, IsCombAt y.x (y.u τ) (g₁ i) (w₁ i ≫ ν.φ)) → (∀ i, IsCombAt y.x (y.u (conjEmb τ)) (g₂ i) (w₂ i ≫ ν.φ)) →
      fv * g₁.det = g₂.det * evR Xo c f y

variable {p : ℕ} [Fact p.Prime] [StarRing (𝓞 E)]


variable (p E) in
abbrev PtP : Type 1 := Point p (Valued.v : Valuation ℂ_[p] ℝ≥0) 𝓞_ℂ_[p] (𝓞 E)

def PtOn (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left)
    (ψ : P.A.A.left ⟶ Y.oF.t.G.left) : Prop :=
  spMap (algebraMap 𝓞_ℂ_[p] ℂ_[p]) ≫ yb = yy ≫ Y.j ∧ IsGrpPullback P.G Y.t.G yb π ∧
    (∀ a, (P.oG.act a).left ≫ π = π ≫ (Y.t.act.act a).left) ∧ IsGrpPullback P.A.A Y.oF.t.G yy ψ ∧
    ψ ≫ Y.m.φ = P.gen ≫ π ∧ LBIso P.A.L (Y.oF.t.PP.L.pull ψ)

def ITie (P : PtP E p) {G : Scheme.{0}} (π : P.G.left ⟶ G) (x : LieG P.Gt) (u : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ G) : Prop :=
  ∃ xG : LieG P.G, Corr P x.1 xG.1 ∧ xG.1.left ≫ π = u

def HTApprox (n : ℕ) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left)
    (ψ : P.A.A.left ⟶ Y.oF.t.G.left) {N g : ℕ} (a : Fin N → Dw.La)
    (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)) (h : Fin N → Fin g → 𝓞_ℂ_[p]) : Prop :=
  ∀ (m : Fin N) (t : P.T), (t.lev n).left ≫ ψ = yy ≫ (Y.oF.etaA (a m)).left → ∀ (k : Fin g) (x : LieG P.Gt),
    ITie P π x (e k) → h m k - (P.al₀ t).1 x ∈ Ideal.span {(p : 𝓞_ℂ_[p]) ^ n}

variable [Algebra c.F ℂ_[p]]

def KapSpec (τ : E →+* ℂ) (f : Rul Xo c) (n : ℕ) {N : ℕ} (a : Fin N → Dw.La) (T S : Ind Dw τ → Fin N → c'.V W)
    (yb : Sp 𝓞_ℂ_[p] ⟶ Y.X) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left)
    (ψ : P.A.A.left ⟶ Y.oF.t.G.left) (κ : ℂ_[p]) : Prop :=
  ∀ (β : c'.V W →+* 𝓞_ℂ_[p]), yb ≫ Y.s = spMap β →
  ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ Y.t.G.left)) (U₁ U₂ : Fin g → Fin g → 𝓞_ℂ_[p])
    (h : Fin N → Fin g → 𝓞_ℂ_[p]), IsTanBasis Y.t yb e → EigAt Y.t yb (β.comp (embV c' W τ)) e U₁ →
    EigAt Y.t yb (β.comp (embV c' W (conjEmb τ))) e U₂ → HTApprox Y n yy P π ψ a e h →
    (∃ (σ : Equiv.Perm (Ind Dw τ)) (K₁ : Fin (Dw.mult τ) → Fin g) (K₂ : Fin (Dw.mult (conjEmb τ)) → Fin g),
      (p : ℝ)⁻¹ ^ n < ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) *
        pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p])‖) ∧
    ∀ (σ : Equiv.Perm (Ind Dw τ)) (K₁ : Fin (Dw.mult τ) → Fin g) (K₂ : Fin (Dw.mult (conjEmb τ)) → Fin g),
      (p : ℝ)⁻¹ ^ n < ‖((pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) *
        pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) : ℂ_[p])‖ →
      ∀ fv : ℂ_[p], GVal Y r ν τ f yy (bcV Y.t (algebraMap 𝓞_ℂ_[p] ℂ_[p]) e) (fun k b => (U₁ (K₁ k) b : ℂ_[p]))
        (fun k b => (U₂ (K₂ k) b : ℂ_[p])) fv →
        ‖fv * ((Equiv.Perm.sign σ : ℤ) : ℂ_[p]) * (pairDet (covec β T h (σ ∘ Sum.inl)) (U₁ ∘ K₁) : 𝓞_ℂ_[p]) /
          (pairDet (covec β S h (σ ∘ Sum.inr)) (U₂ ∘ K₂) : 𝓞_ℂ_[p]) - κ‖ < ‖κ‖

end Model

def HTLocSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l' : Level H) (Xo' : Moduli Dw l') (c' : Coeff l') (W : ValuationSubring ℂ) (Y : Model Xo' c' (c'.V W).subtype) (p : ℕ) [Fact p.Prime] (n : ℕ)
    [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → (p : ℂ) ∈ W.nonunits → l'.A = p ^ n →
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (ξ : Sp R ⟶ Y.X),
    ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) ∈ Set.range Y.j → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ Y.t.G.left)),
    IsTanBasis Y.t ξ e → ∀ (N : ℕ) (a : Fin N → Dw.La) (𝔭 : Ideal R), 𝔭.IsPrime →
    ∃ (f : R) (h : Fin N → Fin g → Localization.Away f), f ∉ 𝔭 ∧
      ∀ (φ : Localization.Away f →+* 𝓞_ℂ_[p]) (yy : Sp ℂ_[p] ⟶ Xo'.XF c') (P : PtP E p) (π : P.G.left ⟶ Y.t.G.left)
        (ψ : P.A.A.left ⟶ Y.oF.t.G.left), PtOn Y (spMap (φ.comp (algebraMap R _)) ≫ ξ) yy P π ψ →
        HTApprox Y n yy P π ψ a (bcV Y.t (φ.comp (algebraMap R _)) e) fun m k => φ (h m k)

def GenSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (W : ValuationSubring ℂ)
    (Y : Model Xo' c' (c'.V W).subtype) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : SABMap Y.oF.t Xo.univ.t (r ≫ pullback.fst _ _)) (hle : c.F ≤ c'.F)
    (r₀ : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r₀) (x : ℝ), Laws U x →
    ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ)
      (Xw : Y.X.Opens), p.Prime → IsCover Y r hle Z la p Xw →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] (ξ : Sp A ⟶ Y.X) (β : c'.V W →+* A),
      IsOpenImmersion ξ → ξ ≫ Y.s = spMap β → IsUnit (p : A) → ξ (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum A) ∈ Xw →
    ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber A) ⟶ Y.t.G.left)) (U₁ h₁ : Fin (Dw.mult τ.1) → Fin g → A)
      (U₂ h₂ : Fin (Dw.mult (conjEmb τ.1)) → Fin g → A), IsTanBasis Y.t ξ e →
      (∀ (S : Type) [CommRing S] (φ : A →+* S),
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W τ.1))) (bcV Y.t φ e) (fun k b => φ (U₁ k b)) ∧
        EigRowsAt Y.t (spMap φ ≫ ξ) (φ.comp (β.comp (embV c' W (conjEmb τ.1)))) (bcV Y.t φ e) fun k b => φ (U₂ k b)) →
      IsUnit (pairDet h₁ U₁) → IsUnit (pairDet h₂ U₂) →
      ∃ f : Aˣ, ∀ (k : Type) [Field k] [Algebra c.F k] (φ : A →+* k) (yy : Sp k ⟶ Xo'.XF c'),
        yy ≫ Y.j = spMap φ ≫ ξ →
        GVal Y r ν τ.1 s.sig yy (bcV Y.t φ e) (fun k b => φ (U₁ k b)) (fun k b => φ (U₂ k b)) (φ f)

section BaseChange

variable {X : Scheme.{0}} {t : SAB H X} {g : ℕ} {R S S' : Type} [CommRing R] [CommRing S] [CommRing S']

theorem bcV_bcV (φ : R →+* S) (ψ : S →+* S') (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) :
    bcV t ψ (bcV t φ e) = bcV t (ψ.comp φ) e := by
  funext i
  rw [bcV, bcV, bcV, ← Category.assoc, spMap_spMap]
  congr 2
  ext s <;> simp [dualMap]

theorem sp_sp (φ : R →+* S) (ψ : S →+* S') (x : Sp R ⟶ X) : spMap ψ ≫ spMap φ ≫ x = spMap (ψ.comp φ) ≫ x := by
  rw [← Category.assoc, spMap_spMap]

theorem isTanBasis_bc {x : Sp R ⟶ X} {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)} (h : IsTanBasis t x e)
    (φ : R →+* S) : IsTanBasis t (spMap φ ≫ x) (bcV t φ e) := by
  refine ⟨fun i => ⟨?_, ?_⟩, fun S' _ ψ w hw => ?_⟩
  · rw [bcV, Category.assoc, (h.1 i).1, sp_sp, sp_sp]
    congr 2
    ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · have e1 : (1 : Over.mk (spMap φ ≫ x) ⟶ t.G) = (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ x) ⟶ Over.mk x) ≫ 1 :=
      (MonObj.comp_one _).symm
    rw [e1, Over.comp_left, ← (h.1 i).2, bcV, ← Category.assoc, spMap_spMap]
    change _ = spMap φ ≫ _ ≫ _
    rw [← Category.assoc, spMap_spMap]
    congr 2
    ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]
  · rw [sp_sp] at hw ⊢
    have := h.2 S' (ψ.comp φ) w hw
    change ∃! a, IsCombAtG t _ (bcV t ψ (bcV t φ e)) a w
    rw [bcV_bcV]
    exact this

theorem bot_map [IsDomain R] [IsDomain S] {φ : R →+* S} (hφ : Function.Injective φ) (x : Sp R ⟶ X) :
    (spMap φ ≫ x) (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum S) = x (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) := by
  refine (Scheme.Hom.comp_apply _ _ _).trans (congrArg x ?_)
  exact PrimeSpectrum.ext ((RingHom.injective_iff_ker_eq_bot φ).1 hφ)

end BaseChange

theorem coe_valued (p : ℕ) [Fact p.Prime] (x : ℂ_[p]) : ((Valued.v x : ℝ≥0) : ℝ) = ‖x‖ := by
  rw [PadicComplex.norm_eq_norm, Valued.v.norm_def, (show Valuation.RankLeOne.hom' Valued.v = MonoidWithZeroHom.ValueGroup₀.embedding from rfl), Valuation.embedding_restrict]

end GlobalTheory.FlatModel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCoverComponentExtendsToRankOneCuspData
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCoverComponentExtendsToRankOneCuspData
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)

namespace GlobalTheory.CovData

theorem hasPrinc_good (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ) (hG : Y.Good e o)
    (σ : Y.d.c₂.F →+* ℂ) (hσ : GoodEmb Y.d.c₂ σ) :
    GlobalTheory.FrameNorm.HasPrinc (Formalism.L2.PjFree.Unf.ofPj (Y.U σ))
      (Y.d.l₂.M * (D.host.g 0 * D.host.g 1 * Y.d.pd)) := by
  have hr : 0 < D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  have hN : 3 ≤ D.host.g 0 * D.host.g 1 * Y.d.pd := by
    have h0 := (D.host.g_prime 0).two_le
    have h1 := (D.host.g_prime 1).two_le
    have hp : 1 ≤ Y.d.pd := by rw [hG.pd]; exact Nat.one_le_pow _ _ (by norm_num)
    have : 4 ≤ D.host.g 0 * D.host.g 1 := Nat.mul_le_mul h0 h1
    nlinarith
  intro k γ hγ hc
  obtain ⟨γ', hγ', u, n, hn, hu, he⟩ := GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ σ _
    (Formalism.L2.PjFree.Unf.ofPj (Y.U σ)) ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hG.unf σ hσ)) hG.lev.2 hr k γ hγ
    (fun x hx => by
      obtain ⟨y, hy, h⟩ := hc x hx
      refine ⟨((D.host.g 0 * D.host.g 1 * Y.d.pd : ℕ) : D.host.E) • y, ?_, ?_⟩
      · rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hy _
      · rw [h, smul_smul, ← Nat.cast_mul])
  obtain ⟨th, hrk, hth, hD⟩ := hG.dictU σ hσ
  have hmu : MuUnit (D.sp.W j) (Y.dict σ) (fun _ => (1 : ℂ)) :=
    ⟨fun _ _ => (mul_one 1).symm, fun _ => norm_one, fun _ _ => rfl, hG.unit σ hσ⟩
  have h1 := GlobalTheory.PrincCore.root_eq_one (D.sp.W j) hrk hr (Y.U σ).X (Y.dict σ) (fun _ => (1 : ℂ)) Y.Kf th hth hD
    hmu _ hN hG.levelK k γ γ' hγ'
    (fun x hx => by
      obtain ⟨y, hy, h⟩ := hc x hx
      refine ⟨((Y.d.l₂.M : ℕ) : D.host.E) • y, ?_, ?_⟩
      · rw [Nat.cast_smul_eq_nsmul]; exact nsmul_mem hy _
      · rw [h, smul_smul, ← Nat.cast_mul, mul_comm])
    u n hn hu he
  rw [h1, one_smul] at he
  exact Units.ext he ▸ hγ'

end GlobalTheory.CovData

namespace GlobalTheory.CovData

theorem exists_dataX_good : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    ∀ σ, GoodEmb Y.d.c₂ σ → ∀ k : (Y.U σ).Comp, ∃ (Xx : FD.DataX D.host.E D.R.r)
      (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), Xx.toData = (Y.U σ).X k ∧ 𝔄 ≠ 0 ∧
      Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} := by
  intro D T j Y e o hG σ hσ k
  obtain ⟨hr, hm⟩ := hG.modelW σ hσ
  have hx1 : xiR D ≤ 1 := (ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelDataX.xiR_le_half D).trans (by norm_num)
  have habs := hG.xiAbs σ hσ k
  have hperf := GlobalTheory.traceForm_integral_perfect_of_isUnf _ _ _ _ _ _ σ _ (Formalism.L2.PjFree.Unf.ofPj (Y.U σ))
    ((Formalism.L2.PjFree.isUnf_ofPj _).2 (hG.unf σ hσ)) k
  have hone : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) ((Y.U σ).X k).ξ0 * D.host.AA *
      D.host.AAbar * (differentIdeal ℤ (𝓞 D.host.E) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) = 1 := by
    have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
    rw [(hm k).2, show -D.host.xi0 = (-1 : (𝓞 D.host.E)ˣ) • D.host.xi0 by simp,
      ← (FractionalIdeal.spanSingleton_eq_spanSingleton.2 ⟨-1, rfl⟩)]
    exact h1
  have hA : D.host.AA ≠ 0 := by
    intro e0
    rw [e0] at hone
    simp at hone
  have hM : 0 < Y.d.l₂.M * (D.host.g 0 * D.host.g 1 * Y.d.pd) := by
    have h0 := (D.host.g_prime 0).pos
    have h1 := (D.host.g_prime 1).pos
    have hp : 0 < Y.d.pd := by rw [hG.pd]; positivity
    have hl : 0 < Y.d.l₂.M := by have := Y.d.l₂.three_le; omega
    positivity
  obtain ⟨Xx, h1, -, h3⟩ := GlobalTheory.exists_dataX_of_perfect_traceForm _ _ ((Y.U σ).X k) D.host.AA D.host.AAbar
    (xiR D) _
    (fun a => by
      rw [GlobalTheory.LatticeData.cc_eq_conj]
      exact ⟨conj_mem_AA D, fun ha => by simpa only [conj_conj] using conj_mem_AAbar D ha⟩)
    hone habs hx1 hperf.1 hperf.2 hM (hasPrinc_good D T j Y e o hG σ hσ k)
  exact ⟨Xx, D.host.AA, h1, hA, h3⟩

end GlobalTheory.CovData
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCoverComponentExtendsToRankOneCuspDataStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodCover_component_extends_to_rankOne_cusp_data : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    ∀ σ, GoodEmb Y.d.c₂ σ → ∀ k : (Y.U σ).Comp, ∃ (Xx : FD.DataX D.host.E D.R.r)
      (𝔄 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), Xx.toData = (Y.U σ).X k ∧ 𝔄 ≠ 0 ∧
      Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ 𝔄, ∃ u ∈ Xx.L', v = a • u} := by
  first | exact @GlobalTheory.CovData.exists_dataX_good | exact GlobalTheory.CovData.exists_dataX_good | (intros; apply GlobalTheory.CovData.exists_dataX_good <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NabBaseChange
set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BaseCmp

section Data

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

abbrev lattice₂ : AddSubgroup (WO (Vc D i) (Wc D i)) := latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True


open Classical in
def IsTypeVec (eg : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D eg) (lattice₂ R i) 1 (R.vacP i)
    (fun x => if IsHalf (cA D eg) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
      omegaK R.Pg (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) fg


open Classical in
def flatDat (Q : Finset (Pl D.host.E)) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (eQ : AE D) (x : WO (Vc D i) (Wc D i)) : ℂ :=
  if IsHalf eQ x ∧ IsIntM (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
    omegaFlat Q (Wc D i).rank ξR (fun PP => redM PP (frMapO (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0

abbrev IsModel (eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ)
    (Tm : (WO (Vc D i) (Wc D i) → ℂ) →ₗ[ℂ] (WO (Vc D i) (Wc D i) → ℂ)) : Prop :=
  IsPlaceModel R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) eQ (lattice₂ R i) 1 fg Tm

abbrev dil (a : D.host.E) (x : WO (Vc D i) (Wc D i)) : WO (Vc D i) (Wc D i) := Matrix.map x fun w => incA D a * w

abbrev IsCoefMap (c0L : ∀ j : Fin D.R.m, VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV j).W) : Prop :=
  ∃ gramR c0R, Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
    (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L

end Data

def FlatTwoStep : Prop := ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F →
    ∀ (i : Fin D.R.m) (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle)
    (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ) (B : Base (Vc D i) (Wc D i)),
    B.Good → BaseOf R i B → KerDat R i ξ χ ξR B.de.Q ω φ → ChrEq B.de.chi ξ →
    ∃ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg ∧ IsIdemSum eQ B.de.Q ∧ IsTypeVec R i eg fg ∧
      IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) eQ (lattice₂ R i) 1 fg (flatDat R i B.de.Q ξR eQ)
        (GlobalTheory.FlatVecSum.princ B).vecBase

def TraceLevel : Prop := ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F →
    ∀ (i : Fin D.R.m) (B : Base (Vc D i) (Wc D i)), B.Good → BaseOf R i B → ∀ (U : Subgroup G) (ψ : U →* D.what₂.LLˣ)
    (e : G ≃* G0 B.G.Pg (Wc D i).rank),
    (∀ (g : G) (P : Pl D.host.E) (h : P ∈ B.G.Pg) (h' : P ∈ R.Pg) (a c : Fin (Wc D i).rank),
      (e g ⟨P, h⟩).val a c = (R.eG g ⟨P, h'⟩).val (Fin.cast (rank_Wc i) a) (Fin.cast (rank_Wc i) c)) →
    (∀ g, e g ∈ B.G.P.H ↔ g ∈ U) →
    (∀ (u : U) (hu : e u ∈ B.G.P.H), ((B.G.P.chi ⟨e u, hu⟩ : ℂˣ) : ℂ) = D.what₂.embLL ((ψ u : D.what₂.LLˣ) : D.what₂.LL)) →
    ∀ ω : WeilRep D i, B.IsWeil 1 ω → ∀ (h : GA D (Vc D i)) (P : PolF D (Wc D i).rank (Vc D i).rank),
      levelTrace R i U ψ ((GlobalTheory.FlatVecSum.princ B).theta ω h P) = B.theta ω h P

def CoefIndep : Prop := ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F →
    ∀ (i : Fin D.R.m) c0L, IsCoefMap R c0L → ∀ (h : GA D (Vc D i)) w, InCoefLat R i h w →
      ∃ P ∈ nabAtr (labLL D) (lamV D i) (Bridge.hLat (Vc D i) (fin (Vc D i) h)), w = c0L i P

def NabBaseChange : Prop := ∀ (E K₀ K ι : Type) [Field E] [NumberField E] [Field K₀] [NumberField K₀] [Field K] [NumberField K]
    [Fintype ι] (n : ℕ) (f : K₀ →+* K) (emb : ι → E →+* K₀) (lam : ι → DomWeight n) (M : Submodule (𝓞 E) (Fin n → E)),
    Submodule.IsFullLattice E M →
    nabAtr (fun τ => f.comp (emb τ)) lam M ≤
      Submodule.span (𝓞 K) {y : VV K lam | ∃ x ∈ nabAtr emb lam M, (y : Pol K ι n) = MvPolynomial.map f (x : Pol K₀ ι n)}

def LevLamRoot : Prop := ∀ (D : D7) (S T : HSp D) (B : Base S T) (t : Twist D Circle) (k : B.levJ t),
    ∃ n : ℕ, n ≠ 0 ∧ ((B.levLam t k : ℂˣ) : ℂ) ^ n = 1

end GlobalTheory.BaseCmp

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CnormMapConjMulVec
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSApp.GramFrame

open Matrix Module
open scoped ComplexOrder InnerProductSpace

variable {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]

def gramOf {n : ℕ} (w : Fin n → Hs) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j => ⟪w i, w j⟫_ℂ

theorem norm_sum_sq {n : ℕ} (w : Fin n → Hs) (c : Fin n → ℂ) :
    ((‖∑ i, c i • w i‖ ^ 2 : ℝ) : ℂ) = star c ⬝ᵥ (gramOf w *ᵥ c) := by
  have h1 : ((‖∑ i, c i • w i‖ ^ 2 : ℝ) : ℂ) = ⟪∑ i, c i • w i, ∑ i, c i • w i⟫_ℂ := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [h1]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, dotProduct, mulVec, gramOf, of_apply,
    Pi.star_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def]
  ring

theorem gramOf_posDef {n : ℕ} {w : Fin n → Hs} (hw : LinearIndependent ℂ w) : (gramOf w).PosDef := by
  refine posDef_iff_dotProduct_mulVec.2 ⟨?_, fun c hc => ?_⟩
  · ext i j
    simp [gramOf, conjTranspose_apply]
  · rw [← norm_sum_sq]
    have h0 : ∑ i, c i • w i ≠ 0 := fun h => hc (funext fun i => Fintype.linearIndependent_iff.1 hw c h i)
    exact Complex.zero_lt_real.2 (by positivity)

theorem exists_frame {n : ℕ} {w : Fin n → Hs} (hw : LinearIndependent ℂ w) :
    ∃ B : Matrix (Fin n) (Fin n) ℂ, IsUnit B.det ∧ ∀ c, Formalism.HermitianLatticesTheory.cnorm (B *ᵥ c) = ‖∑ i, c i • w i‖ := by
  obtain ⟨B, hB, hG⟩ := exists_unit_factor (gramOf_posDef hw)
  refine ⟨B, hB, fun c => ?_⟩
  have key : star (B *ᵥ c) ⬝ᵥ (B *ᵥ c) = star c ⬝ᵥ ((Bᴴ * B) *ᵥ c) := by
    have e0 : star c ⬝ᵥ (Bᴴ *ᵥ (B *ᵥ c)) = (star c ᵥ* Bᴴ) ⬝ᵥ (B *ᵥ c) := dotProduct_mulVec _ _ _
    rw [← mulVec_mulVec, e0, star_mulVec]
  have e : ((∑ i, ‖(B *ᵥ c) i‖ ^ 2 : ℝ) : ℂ) = ((‖∑ i, c i • w i‖ ^ 2 : ℝ) : ℂ) := by
    rw [sum_norm_sq_eq, norm_sum_sq, hG, key]
  simp only [Formalism.HermitianLatticesTheory.cnorm, Complex.ofReal_injective e, Real.sqrt_sq (norm_nonneg _)]

theorem cnorm_map_conj_mulVec {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (B.map (starRingEnd ℂ) *ᵥ u) = Formalism.HermitianLatticesTheory.cnorm (B *ᵥ star u) := by
  have e : B.map (starRingEnd ℂ) *ᵥ u = star (B *ᵥ star u) := by
    funext i
    simp [mulVec, dotProduct, star_sum, mul_comm]
  rw [e]
  simp [Formalism.HermitianLatticesTheory.cnorm]

end GlobalTheory.HSApp.GramFrame


open GlobalTheory.HSApp.GramFrame Matrix Module in
theorem GlobalTheory.HSApp.hasGram_of_inner : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] (N : (K →+* ℂ) → V → ℝ), (∀ v : InfinitePlace K, ∃ (Hs : Type) (_ : NormedAddCommGroup Hs) (_ : InnerProductSpace ℂ Hs) (Φ : V →+ Hs), ((∀ (a : K) (x : V), Φ (a • x) = v.embedding a • Φ x) ∨ (∀ (a : K) (x : V), Φ (a • x) = starRingEnd ℂ (v.embedding a) • Φ x)) ∧ (∀ x, N v.embedding x = ‖Φ x‖) ∧ ∀ (n : ℕ) (e : Fin n → V), LinearIndependent K e → LinearIndependent ℂ (fun i => Φ (e i))) → GlobalTheory.AllWt.HasGram N := by
  intro K V _ _ _ _ _ N h
  classical
  let b := Module.finBasis K V
  have key : ∀ v : InfinitePlace K, ∃ Y : Matrix (Fin (finrank K V)) (Fin (finrank K V)) ℂ, IsUnit Y.det ∧
      ∀ x, Formalism.HermitianLatticesTheory.cnorm (Y *ᵥ Formalism.HermitianLatticesTheory.vecAt b v x) = N v.embedding x := by
    intro v
    obtain ⟨Hs, i1, i2, Φ, hlin, hN, hli⟩ := h v
    obtain ⟨B, hB, hBn⟩ := exists_frame (hli _ b b.linearIndependent)
    have hsum : ∀ x, Φ x = ∑ i, Φ (b.repr x i • b i) := fun x => by
      conv_lhs => rw [← b.sum_repr x]
      exact map_sum Φ _ _
    rcases hlin with hl | hl
    · refine ⟨B, hB, fun x => ?_⟩
      rw [hN, hBn, hsum]
      simp only [hl]
      rfl
    · refine ⟨B.map (starRingEnd ℂ), ?_, fun x => ?_⟩
      · have e := RingHom.map_det (starRingEnd ℂ) B
        change IsUnit ((starRingEnd ℂ).mapMatrix B).det
        rw [← e]
        exact hB.map _
      · rw [cnorm_map_conj_mulVec, hN, hBn, hsum]
        simp only [hl]
        rfl
  choose Y hY hYn using key
  refine GlobalTheory.AllWt.IsGram.hasGram (b := b) (X := fun v => (Y v)⁻¹) fun v => ⟨isUnit_nonsing_inv_det _ (hY v), fun x => ?_⟩
  simp only [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.fcoord]
  rw [nonsing_inv_nonsing_inv _ (hY v)]
  exact hYn v x
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CovTop.MeasRd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

def ratAt : ℝ := GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.ratio D i (p.R.toRealDat.νW i) (p.R.toRealDat.fdW i)

def ExactAt : Prop :=
  ∀ (σ : D.what₂.LL →+* ℂ) (f : p.T.cuspA ((i : ℕ) + 1) (wtA (p.κ i)) (p.κ i).n),
    nrmR p.R.toRealDat i σ ((p.fw.e i f : (p.R.toRealDat.FW i).WK) : Fin (p.R.toRealDat.nW i) → D.what₂.LL) =
      Real.sqrt (ratAt p i) * petW (p.T.U ((i : ℕ) + 1)) (xiR D) (p.T.V ((i : ℕ) + 1)) (p.T.dict ((i : ℕ) + 1)) (Gk p i)
        (σ.comp (algebraMap p.T.Q.c.F D.what₂.LL)) f

theorem measAt_of (h : ExactAt p i) (hr : 0 < ratAt p i) {K₁ K₂ : ℝ} (h1 : 0 ≤ K₁) (h2 : 0 ≤ K₂)
    (hu : Real.log (ratAt p i) ≤ K₁ * unitE p) (hl : -(K₂ * unitE p) ≤ Real.log (ratAt p i)) :
    MeasAt p i ((K₁ + K₂) / 2) := by
  intro σ
  refine ⟨Real.sqrt (ratAt p i), Real.sqrt_pos.2 hr, ?_, fun f => h σ f⟩
  rw [Real.log_sqrt hr.le]
  have key : |Real.log (ratAt p i)| ≤ (K₁ + K₂) * unitE p := by
    rcases le_or_gt 0 (unitE p) with hu0 | hu0
    · rw [abs_le]; constructor <;> nlinarith
    · have hs : K₁ + K₂ = 0 := by nlinarith
      have e1 : K₁ = 0 := by linarith
      have e2 : K₂ = 0 := by linarith
      subst e1 e2
      have : Real.log (ratAt p i) = 0 := by
        apply le_antisymm <;> simp_all
      rw [this, hs]; simp
  rw [abs_div, abs_two]
  have : |Real.log (ratAt p i)| / 2 ≤ (K₁ + K₂) * unitE p / 2 := by linarith
  linarith [this, show (K₁ + K₂) * unitE p / 2 = (K₁ + K₂) / 2 * unitE p by ring]

end GlobalTheory.CovTop.MeasRd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsDominantLastEntryOneDegree
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsDominantLastEntryOneDegree
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RefSum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : Datum H}

theorem conjEmb_rt_of_not {τ : E →+* ℂ} (h : ¬ τ (H.rt : E) = H.rt0) :
    conjEmb τ (H.rt : E) = H.rt0 := by
  have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
    simpa using this
  have hsq : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow, hE]; simp
  have hneg : τ (H.rt : E) = -H.rt0 := (sq_eq_sq_iff_eq_or_eq_neg.1 hsq).resolve_left h
  have hre : H.rt0.re = 0 := by
    have h2 := H.sqrt_neg_disc_sq
    have hr := congrArg Complex.re h2
    have hi := congrArg Complex.im h2
    simp only [sq, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
      Complex.natCast_im] at hr hi
    have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
    by_contra hne
    have him : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left hne
    rw [him] at hr
    nlinarith [mul_self_nonneg H.rt0.re]
  show (starRingEnd ℂ) (τ (H.rt : E)) = H.rt0
  rw [hneg]
  apply Complex.ext <;> simp [hre]

theorem psi_or_conj (σ : E →+* ℂ) : (∃ τ : Psi H, σ = τ.1) ∨ ∃ τ : Psi H, σ = conjEmb τ.1 := by
  by_cases h : σ (H.rt : E) = H.rt0
  · exact Or.inl ⟨⟨σ, h⟩, rfl⟩
  · exact Or.inr ⟨⟨conjEmb σ, conjEmb_rt_of_not h⟩, (GlobalTheory.AllWt.conjEmb_conjEmb σ).symm⟩

theorem psi_nonempty : Nonempty (Psi H) := by
  have : 0 < Fintype.card (E →+* ℂ) := by
    rw [NumberField.Embeddings.card]; exact Module.finrank_pos
  obtain ⟨σ⟩ := Fintype.card_pos_iff.1 this
  rcases psi_or_conj (H := H) σ with ⟨τ, -⟩ | ⟨τ, -⟩ <;> exact ⟨τ⟩

theorem sum_mult : ∑ τ : E →+* ℂ, Dw.mult τ = (Module.finrank ℚ E / 2) * (Dw.p + Dw.q) := by
  classical
  set P := (Finset.univ : Finset (E →+* ℂ)).filter (fun τ => τ (H.rt : E) = H.rt0) with hP
  set Q := (Finset.univ : Finset (E →+* ℂ)).filter (fun τ => ¬ τ (H.rt : E) = H.rt0) with hQ
  have hcard : Q.card = P.card := by
    refine Finset.card_nbij' conjEmb conjEmb ?_ ?_ ?_ ?_
    · intro a ha
      simp only [hQ, hP, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
      exact conjEmb_rt_of_not ha
    · intro a ha
      simp only [hQ, hP, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ⊢
      exact GlobalTheory.AllWt.conj_not_mem ⟨a, ha⟩
    · intro a _; exact GlobalTheory.AllWt.conjEmb_conjEmb a
    · intro a _; exact GlobalTheory.AllWt.conjEmb_conjEmb a
  have htot : P.card + Q.card = Module.finrank ℚ E := by
    rw [← NumberField.Embeddings.card E ℂ, ← Finset.card_univ]
    exact Finset.card_filter_add_card_filter_not _
  have hsum : ∑ τ : E →+* ℂ, Dw.mult τ = P.card * Dw.p + Q.card * Dw.q := by
    simp only [Datum.mult]
    rw [Finset.sum_ite]
    simp [Finset.sum_const, hP, hQ]
  rw [hsum, hcard, ← htot, hcard, ← two_mul, Nat.mul_div_cancel_left _ (by norm_num)]
  ring


variable (Dw) in
abbrev thExpZ (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) : (E →+* ℂ) × ℕ → ℤ :=
  (GlobalTheory.AllWt.wtOf Dw (u + GlobalTheory.FlatLine.parWt Dw (shift Dw u n)) ((n / 2 : ℕ) : ℤ)).1

theorem thExpZ_big (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (τ : Psi H) (i : ℕ) (hi : i < Dw.p) :
    thExpZ Dw u n (τ.1, i) = u τ ⟨i, by omega⟩ + 1 - u τ ⟨Dw.p - 1, by omega⟩ := by
  rw [thExpZ, GlobalTheory.AllWt.wtOf_big _ _ τ i hi]
  simp only [Pi.add_apply, GlobalTheory.FlatLine.parWt, shift, dif_pos (show 0 < Dw.p by omega)]
  ring

theorem thExpZ_big_ge (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (τ : Psi H) (i : ℕ) (hi : Dw.p ≤ i) :
    thExpZ Dw u n (τ.1, i) = 0 := by
  simp only [thExpZ, GlobalTheory.AllWt.wtOf, dif_pos τ.2, dif_neg (not_lt.2 hi)]

theorem thExpZ_small (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (hp : 0 < Dw.p) (τ : Psi H) (i : ℕ) (hi : i < Dw.q) :
    thExpZ Dw u n (conjEmb τ.1, i) =
      u τ ⟨Dw.p - 1, by omega⟩ - u τ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ - 2 * ((n / 2 : ℕ) : ℤ) - 1 := by
  rw [thExpZ, GlobalTheory.AllWt.wtOf_small _ _ τ i hi]
  simp only [Pi.add_apply, GlobalTheory.FlatLine.parWt, shift, dif_pos hp]
  ring

theorem thExpZ_small_ge (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (τ : Psi H) (i : ℕ) (hi : Dw.q ≤ i) :
    thExpZ Dw u n (conjEmb τ.1, i) = 0 := by
  have h' : conjEmb (conjEmb τ.1) (H.rt : E) = H.rt0 := by
    rw [GlobalTheory.AllWt.conjEmb_conjEmb]; exact τ.2
  simp only [thExpZ, GlobalTheory.AllWt.wtOf, dif_neg (GlobalTheory.AllWt.conj_not_mem τ), dif_pos h', dif_neg (not_lt.2 hi)]

theorem thA_dominant_lastPos_degree (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (u : GlobalTheory.AllWt.Weight Dw) (n : ℕ) (b : ℝ) (hp : 1 ≤ Dw.p)
    (hn : Even n) (hu : ∀ τ, Antitone (u τ))
    (hgap : ∀ τ (i j : Fin (Dw.p + Dw.q)), (i : ℕ) + 1 = Dw.p → (j : ℕ) = Dw.p → (n : ℤ) + 1 ≤ u τ i - u τ j)
    (hb : ∀ τ i, |(u τ i : ℝ)| ≤ b) :
    Formalism.L2.Pj.Dom (thA Dw u n) n ∧
      Formalism.L2.Pj.wtZ (thA Dw u n) n =
        GlobalTheory.AllWt.wtOf Dw (u + GlobalTheory.FlatLine.parWt Dw (shift Dw u n)) ((n / 2 : ℕ) : ℤ) ∧
      Formalism.L2.Pj.LastPos Dw (thA Dw u n) ∧ (∀ x, (thA Dw u n x : ℝ) ≤ 2 * b + 1) ∧
      (Formalism.L2.Pj.DF Dw (thA Dw u n) : ℝ) ≤ (Module.finrank ℚ E / 2 : ℕ) * (Dw.p + Dw.q : ℕ) * (2 * b + 1) := by
  have hp0 : 0 < Dw.p := hp
  obtain ⟨τ0⟩ := psi_nonempty (H := H)
  have hb0 : 0 ≤ b := (abs_nonneg _).trans (hb τ0 ⟨0, by omega⟩)
  have hup : ∀ τ i, (u τ i : ℝ) ≤ b := fun τ i => (le_abs_self _).trans (hb τ i)
  have hlo : ∀ τ i, -b ≤ (u τ i : ℝ) := fun τ i => by
    have := neg_abs_le (u τ i : ℝ); linarith [hb τ i]
  have hm : 2 * ((n / 2 : ℕ) : ℤ) = n := by obtain ⟨k, rfl⟩ := hn; omega

  have F1 : ∀ x, 0 ≤ thExpZ Dw u n x := by
    rintro ⟨σ, i⟩
    rcases psi_or_conj (H := H) σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · by_cases hi : i < Dw.p
      · rw [thExpZ_big u n τ i hi]
        have := hu τ (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨Dw.p - 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))
        omega
      · rw [thExpZ_big_ge u n τ i (by omega)]
    · by_cases hi : i < Dw.q
      · rw [thExpZ_small u n hp0 τ i hi]
        have h1 := hu τ (show (⟨Dw.p, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ from
          Fin.mk_le_mk.2 (by omega))
        have h2 := hgap τ ⟨Dw.p - 1, by omega⟩ ⟨Dw.p, by omega⟩ (by simp; omega) rfl
        omega
      · rw [thExpZ_small_ge u n τ i (by omega)]

  have F2 : ∀ x, (thExpZ Dw u n x : ℝ) ≤ 2 * b + 1 := by
    rintro ⟨σ, i⟩
    rcases psi_or_conj (H := H) σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · by_cases hi : i < Dw.p
      · rw [thExpZ_big u n τ i hi]; push_cast
        linarith [hup τ ⟨i, by omega⟩, hlo τ ⟨Dw.p - 1, by omega⟩]
      · rw [thExpZ_big_ge u n τ i (by omega)]; push_cast; linarith
    · by_cases hi : i < Dw.q
      · rw [thExpZ_small u n hp0 τ i hi, hm]; push_cast
        have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
        linarith [hup τ ⟨Dw.p - 1, by omega⟩, hlo τ ⟨Dw.p + (Dw.q - 1 - i), by omega⟩]
      · rw [thExpZ_small_ge u n τ i (by omega)]; push_cast; linarith

  have F3 : ∀ σ i, thExpZ Dw u n (σ, i + 1) ≤ thExpZ Dw u n (σ, i) := by
    intro σ i
    rcases psi_or_conj (H := H) σ with ⟨τ, rfl⟩ | ⟨τ, rfl⟩
    · by_cases hi : i + 1 < Dw.p
      · rw [thExpZ_big u n τ _ hi, thExpZ_big u n τ i (by omega)]
        have := hu τ (show (⟨i, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨i + 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))
        omega
      · rw [thExpZ_big_ge u n τ (i + 1) (by omega)]; exact F1 _
    · by_cases hi : i + 1 < Dw.q
      · rw [thExpZ_small u n hp0 τ _ hi, thExpZ_small u n hp0 τ i (by omega)]
        have := hu τ (show (⟨Dw.p + (Dw.q - 1 - (i + 1)), by omega⟩ : Fin (Dw.p + Dw.q)) ≤
          ⟨Dw.p + (Dw.q - 1 - i), by omega⟩ from Fin.mk_le_mk.2 (by omega))
        omega
      · rw [thExpZ_small_ge u n τ (i + 1) (by omega)]; exact F1 _
  have hcast : ∀ x, (thA Dw u n x : ℝ) = (thExpZ Dw u n x : ℝ) := fun x => by
    have h := Int.toNat_of_nonneg (F1 x)
    show (((thExpZ Dw u n x).toNat : ℕ) : ℝ) = _
    rw [← h]; norm_cast
  have hbound : ∀ x, (thA Dw u n x : ℝ) ≤ 2 * b + 1 := fun x => (hcast x).trans_le (F2 x)
  refine ⟨⟨fun σ => antitone_nat_of_succ_le fun i => Int.toNat_le_toNat (F3 σ i), hn⟩, ?_, ?_, hbound, ?_⟩
  · refine Prod.ext (funext fun x => ?_) ?_
    · exact Int.toNat_of_nonneg (F1 x)
    · show (n : ℤ) = 2 * ((n / 2 : ℕ) : ℤ)
      omega
  · intro σ hσ _
    have hmul : Dw.mult σ = Dw.p := if_pos hσ
    rw [hmul]
    have h1 : thExpZ Dw u n (σ, Dw.p - 1) = 1 :=
      (thExpZ_big u n ⟨σ, hσ⟩ (Dw.p - 1) (by omega)).trans (by ring)
    show 0 < (thExpZ Dw u n (σ, Dw.p - 1)).toNat
    rw [h1]; decide
  · have hDF : (Formalism.L2.Pj.DF Dw (thA Dw u n) : ℝ) ≤ ∑ τ : E →+* ℂ, (Dw.mult τ : ℝ) * (2 * b + 1) := by
      unfold Formalism.L2.Pj.DF; push_cast
      refine Finset.sum_le_sum fun τ _ => ?_
      calc ∑ i : Fin (Dw.mult τ), (thA Dw u n (τ, i) : ℝ) ≤ ∑ _i : Fin (Dw.mult τ), (2 * b + 1) :=
            Finset.sum_le_sum fun i _ => hbound (τ, i)
        _ = _ := by simp [mul_add]
    rw [← Finset.sum_mul] at hDF
    have hs : (∑ τ : E →+* ℂ, (Dw.mult τ : ℝ)) =
        ((Module.finrank ℚ E / 2 : ℕ) : ℝ) * ((Dw.p + Dw.q : ℕ) : ℝ) := by
      rw [← Nat.cast_sum, sum_mult, Nat.cast_mul]
    rw [hs] at hDF
    exact hDF

end GlobalTheory.RefSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsDominantLastEntryOneDegreeStatement
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaExponents_dominant_lastEntry_one_degree : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (u : Weight Dw) (n : ℕ) (b : ℝ), 1 ≤ Dw.p → Even n → (∀ τ, Antitone (u τ)) → (∀ τ (i j : Fin (Dw.p + Dw.q)), (i : ℕ) + 1 = Dw.p → (j : ℕ) = Dw.p → (n : ℤ) + 1 ≤ u τ i - u τ j) → (∀ τ i, |(u τ i : ℝ)| ≤ b) → Dom (thA Dw u n) n ∧ wtZ (thA Dw u n) n = wtOf Dw (u + parWt Dw (shift Dw u n)) ((n / 2 : ℕ) : ℤ) ∧ LastPos Dw (thA Dw u n) ∧ (∀ x, (thA Dw u n x : ℝ) ≤ 2 * b + 1) ∧ (DF Dw (thA Dw u n) : ℝ) ≤ (Module.finrank ℚ E / 2 : ℕ) * (Dw.p + Dw.q : ℕ) * (2 * b + 1) := by
  first | exact @GlobalTheory.RefSum.thA_dominant_lastPos_degree | exact GlobalTheory.RefSum.thA_dominant_lastPos_degree | (intros; apply GlobalTheory.RefSum.thA_dominant_lastPos_degree <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaRulesExistAndCusp
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem thetaRules_exist_and_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), 1 ≤ r → (∀ σ, GoodEmb c σ → IsUnf (U σ)) → ∀ (nab : NabV Xo c), IsNab Xo c nab → ThValTot Xo c nab ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → LastPos Dw a → ∀ f ∈ thGen Xo c nab a n, f ∈ cuspW Xo c U (wtZ a n) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro r U hr hU nab hn
  refine ⟨GlobalTheory.thValTot_of_chartIndep GlobalTheory.firstFiveLaws.1 GlobalTheory.chartIndependence_unconditional E H Dw l Xo c nab hn, ?_⟩
  intro a n hd hl f hf
  rw [GlobalTheory.AllWt.cuspW_wtZ, ← Formalism.L2.PjFree.cusp_ofPj]
  exact GlobalTheory.Dict.thInCusp_cusp GlobalTheory.chartIndependence_unconditional E H Dw l Xo c r
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (U σ)) hr
    (fun σ hσ => (Formalism.L2.PjFree.isUnf_ofPj _).2 (hU σ ((Formalism.L2.PjFree.goodEmb_iff σ).1 hσ))) nab hn a n hd hl f hf

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamGApply
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial

namespace GlobalTheory.FrameRead

def detPol (R : Type) [CommRing R] (n : ℕ) : MvPolynomial (Fin n × Fin n) R :=
  Matrix.det (Matrix.of fun a s => X (a, s))

def liftPol {K C : Type} [CommRing K] [CommRing C] {n : ℕ} (e0 : K →+* C) (k : ℕ) (f : MvPolynomial (Fin n × Fin n) K) :
    MvPolynomial (Fin n × Fin n) C :=
  detPol C n ^ k * MvPolynomial.map e0 f

def Shift {ι : Type} {n : ℕ} (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) : Prop :=
  ∀ τ (a : Fin n), (lamW τ a : ℤ) = (lam τ).w a + c τ

def IsPhi {K C : Type} [Field K] [Field C] {ι : Type} [Fintype ι] {n : ℕ} (e0 : K →+* C) (lam : ι → DomWeight n) (lamW : ι → ℕ → ℕ)
    (Φ : VV K lam →ₛₗ[e0] NablaT C n lamW) : Prop :=
  ∀ (x : ι → MvPolynomial (Fin n × Fin n) K) (v : VV K lam), (∀ τ, x τ ∈ nablaSq K n (lam τ)) → (v : Pol K ι n) = ten x →
    ∃ y : ∀ τ, dualWeyl C n n (res n (lamW τ)),
      (∀ τ, (y τ : MvPolynomial (Fin n × Fin n) C) = liftPol e0 (lamW τ (n - 1)) (x τ)) ∧ Φ v = PiTensorProduct.tprod C y

def lamG (C : Type) [CommRing C] {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ) (c : ι → ℤ) :
    (ι → GL (Fin n) C) →* Module.End C (NablaT C n lamW) where
  toFun g := ((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ c τ : Cˣ) : C) • grp C n lamW g
  map_one' := by simp [grp]
  map_mul' g h := by
    simp only [grp, map_mul, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul, smul_mul_smul_comm]

theorem lamG_apply (C : Type) [CommRing C] {ι : Type} [Fintype ι] [DecidableEq ι] (n : ℕ) (lamW : ι → ℕ → ℕ) (c : ι → ℤ)
    (g : ι → GL (Fin n) C) (z : NablaT C n lamW) :
    lamG C n lamW c g z = ((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ c τ : Cˣ) : C) • grp C n lamW g z := rfl

def AtPlace {K : Type} [Field K] [NumberField K] {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 K)) (e0 : K →+* PadicAlgCl l) : Prop :=
  ∀ x : 𝓞 K, x ∈ w.asIdeal ↔ ‖e0 x‖ < 1

end GlobalTheory.FrameRead
end
end
