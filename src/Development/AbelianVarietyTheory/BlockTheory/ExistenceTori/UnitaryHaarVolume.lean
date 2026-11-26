module

public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AdmissibleHarmonicLattice

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume

open Formalism.L2.Pj Formalism.L2.PjFree NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD MeasureTheory
open scoped ENNReal

def sgnMat (r p0 : ℕ) : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)

def Upq (r p0 : ℕ) : Subgroup (GL (Fin r) ℂ) where
  carrier := {g | (g : Matrix (Fin r) (Fin r) ℂ).transpose * sgnMat r p0 *
    (g : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = sgnMat r p0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.transpose_mul, Matrix.map_mul] at *
    calc _ = (b : Matrix (Fin r) (Fin r) ℂ).transpose * ((a : Matrix (Fin r) (Fin r) ℂ).transpose * sgnMat r p0 *
        (a : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ)) * (b : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at *
    have h1 : ((a⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).transpose * (a : Matrix (Fin r) (Fin r) ℂ).transpose = 1 := by
      rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.transpose_one]
    have h2 : (a : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) *
        ((a⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]
      simp
    calc _ = ((a⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).transpose *
        ((a : Matrix (Fin r) (Fin r) ℂ).transpose * sgnMat r p0 * (a : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ)) *
        ((a⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) := by rw [ha]
      _ = (((a⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).transpose * (a : Matrix (Fin r) (Fin r) ℂ).transpose) *
        sgnMat r p0 * ((a : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) *
        ((a⁻¹ : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ)) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

set_option autoImplicit false in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.isClosed_Upq (r p0 : ℕ) :
    IsClosed (_root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.Upq r p0 : Set (GL (Fin r) ℂ)) := by
  show IsClosed {g : GL (Fin r) ℂ | (g : Matrix (Fin r) (Fin r) ℂ).transpose *
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.sgnMat r p0 * (g : Matrix (Fin r) (Fin r) ℂ).map (starRingEnd ℂ) =
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.sgnMat r p0}
  have hv : Continuous fun g : GL (Fin r) ℂ => (g : Matrix (Fin r) (Fin r) ℂ) :=
    Units.continuous_val
  exact isClosed_eq ((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul
    (hv.matrix_map Complex.continuous_conj)) continuous_const

instance locallyCompact_Upq (r p0 : ℕ) : LocallyCompactSpace (Upq r p0) := by
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) ℂ) := inferInstanceAs (LocallyCompactSpace (Fin r → Fin r → ℂ))
  haveI : LocallyCompactSpace (Matrix (Fin r) (Fin r) ℂ)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin r) ℂ) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  exact (isClosed_Upq r p0).locallyCompactSpace

instance measurable_Upq (r p0 : ℕ) : MeasurableSpace (Upq r p0) := borel _

instance borel_Upq (r p0 : ℕ) : BorelSpace (Upq r p0) := ⟨rfl⟩

def haarU (r p0 : ℕ) : Measure (Upq r p0) := Measure.haar

section Comp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

abbrev RealGrp : Type := X.Ψ → Upq r X.p0

def haarR : Measure (RealGrp X) := Measure.pi fun _ => haarU r X.p0

def OrthFr : Set (Frame X.Ψ r) := {x | ∀ τ : X.Ψ, gram τ.1 X.Gm (mat x τ) = sgnMat r X.p0}

def baseFr : Frame X.Ψ r := fun τ => ((X.signature τ).choose : Matrix (Fin r) (Fin r) ℂ)

set_option autoImplicit false in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
theorem _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.baseFr_mem :
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.baseFr X ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.OrthFr X := by
  intro τ
  exact (X.signature τ).choose_spec.2

def frameOf (g : RealGrp X) : Frame X.Ψ r :=
  rmul (baseFr X) fun τ => (((g τ : Upq r X.p0) : GL (Fin r) ℂ) : Matrix (Fin r) (Fin r) ℂ)

def InjMod (D : Set (RealGrp X)) : Prop :=
  ∀ γ ∈ X.Γ, ∀ g ∈ D, ∀ g' ∈ D, lact γ (frameOf X g) = frameOf X g' → γ = 1

def quotInt (F : Frame X.Ψ r → ℝ≥0∞) : ℝ≥0∞ :=
  ⨆ (D : Set (RealGrp X)) (_ : MeasurableSet D) (_ : InjMod X D), ∫⁻ g in D, F (frameOf X g) ∂(haarR X)

end Comp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

section OneEmb

variable {σ : c.F →+* ℂ} (V : Unf Xo c σ r)

def totVol : ℝ≥0∞ := ∑ k, quotInt (V.X k) fun _ => 1

def totInt (F : ∀ k, Frame (V.X k).Ψ r → ℝ≥0∞) : ℝ≥0∞ := ∑ k, quotInt (V.X k) (F k)

def piFac (a : (E →+* ℂ) × ℕ → ℕ) (k : V.Comp) : ℝ :=
  ∏ τ : E →+* ℂ, ∏ i : Fin (Dw.mult τ), (2 * Real.pi * ‖relab c σ τ (V.X k).ξ0‖) ^ (-(a (τ, i) : ℝ) / 2)

def ptNorm (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) (k : V.Comp) (x : Frame (V.X k).Ψ r) : ℝ :=
  piFac V a k * (V.X k).pnorm (laU V a n k) (rdU V f k) x

def sqInt (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) : ℝ≥0∞ :=
  totInt V fun k x => ENNReal.ofReal (ptNorm V a n f k x ^ 2)

def petNorm (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) : ℝ :=
  Real.sqrt ((sqInt V a n f).toReal / (totVol V).toReal)

end OneEmb

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def petAt (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) : ℝ :=
  petNorm (U (goodOf c σ)) a n f

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.BlockPolyLevelMove
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField MvPolynomial

section Lattice

variable {E : Type} [Field E] [NumberField E]

def unitLat (E : Type) [Field E] [NumberField E] (n : ℕ) : GenLat E n := ⟨stdLat E n⟩

def blockLat {n₁ n₂ : ℕ} (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂) : GenLat E (n₁ + n₂) :=
  ⟨Λ₁.La.comap (LinearMap.funLeft (𝓞 E) E (Fin.castAdd n₂)) ⊓
    Λ₂.La.comap (LinearMap.funLeft (𝓞 E) E (Fin.natAdd n₁))⟩

end Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

def LatAdm (l : Level H) (bad : ℕ) {n : ℕ} (Λ : GenLat E n) : Prop :=
  Λ.Unimod ∧ Λ.TrivAt bad ∧ Λ.TrivAt l.M

def letL (Dw : Datum H) (n₁ n₂ : ℕ) (ℓ : LtN Dw n₁) : LtN Dw (n₁ + n₂) := ⟨ℓ.1, ℓ.2.1, Fin.castAdd n₂ ℓ.2.2⟩

def letR (Dw : Datum H) (n₁ n₂ : ℕ) (ℓ : LtN Dw n₂) : LtN Dw (n₁ + n₂) := ⟨ℓ.1, ℓ.2.1, Fin.natAdd n₁ ℓ.2.2⟩

def blockPoly {K : Type} [Field K] {n₁ n₂ : ℕ} (P₁ : MvPolynomial (LtN Dw n₁) K)
    (P₂ : MvPolynomial (LtN Dw n₂) K) : MvPolynomial (LtN Dw (n₁ + n₂)) K :=
  rename (letL Dw n₁ n₂) P₁ * rename (letR Dw n₁ n₂) P₂

def blockDat {K : Type} [Field K] {n₁ n₂ : ℕ} (w₁ : (Fin n₁ → LevQ Dw l) → K) (w₂ : (Fin n₂ → LevQ Dw l) → K) :
    (Fin (n₁ + n₂) → LevQ Dw l) → K :=
  fun q => w₁ (fun i => q (Fin.castAdd n₂ i)) * w₂ (fun j => q (Fin.natAdd n₁ j))

variable (Xo : Moduli Dw l) (c : Coeff l)

def IsBeta (Dw : Datum H) {l : Level H} (c : Coeff l) {n : ℕ} (Λ : GenLat E n) (β : c.F) : Prop :=
  β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β

def FreeOfLevel (nab : NabV Xo c) (bad : ℕ) : Prop :=
  ∀ (n : ℕ) (Λ : GenLat E n), LatAdm l bad Λ →
    ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmL c Λ a →
    ∀ (w : (Fin n → LevQ Dw l) → c.F) (β : c.F), β ≠ 0 →
    ∀ (N N' : ℕ), Λ.LevOK N l.M → Λ.LevOK N' l.M →
    ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v v' : S),
      ShortValAt Xo c nab w Λ β N P y v → (ShortValAt Xo c nab w Λ β N' P y v' ↔ v' = v)

def BlockProduct (nab : NabV Xo c) (bad : ℕ) : Prop :=
  ∀ (n₁ n₂ : ℕ) (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂), LatAdm l bad Λ₁ → LatAdm l bad Λ₂ →
    ∀ N : ℕ, Λ₁.LevOK N l.M → Λ₂.LevOK N l.M →
    (LatAdm l bad (blockLat Λ₁ Λ₂) ∧ (blockLat Λ₁ Λ₂).LevOK N l.M) ∧
    ∀ (a₁ a₂ : (E →+* ℂ) × ℕ → ℕ) (P₁ : MvPolynomial (LtN Dw n₁) c.F) (P₂ : MvPolynomial (LtN Dw n₂) c.F),
      P₁ ∈ harmL c Λ₁ a₁ → P₂ ∈ harmL c Λ₂ a₂ →
      blockPoly P₁ P₂ ∈ harmL c (blockLat Λ₁ Λ₂) (a₁ + a₂) ∧
      ∀ (w₁ : (Fin n₁ → LevQ Dw l) → c.F) (w₂ : (Fin n₂ → LevQ Dw l) → c.F)
        (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) (v₁ v₂ v : S),
        ShortValAt Xo c nab w₁ Λ₁ 1 N P₁ y v₁ → ShortValAt Xo c nab w₂ Λ₂ 1 N P₂ y v₂ →
        (ShortValAt Xo c nab (blockDat w₁ w₂) (blockLat Λ₁ Λ₂) 1 N (blockPoly P₁ P₂) y v ↔ v = v₁ * v₂)

def BlockBeta (Dw : Datum H) {l : Level H} (c : Coeff l) (bad : ℕ) : Prop :=
  (∀ (n₁ n₂ : ℕ) (Λ₁ : GenLat E n₁) (Λ₂ : GenLat E n₂), LatAdm l bad Λ₁ → LatAdm l bad Λ₂ →
    ∀ β₁ β₂ β : c.F, IsBeta Dw c Λ₁ β₁ → IsBeta Dw c Λ₂ β₂ →
      (IsBeta Dw c (blockLat Λ₁ Λ₂) β ↔ ∃ ζ : c.F, IsOfFinOrder ζ ∧ β = ζ * (β₁ * β₂))) ∧
  ∀ (n₁ n₂ : ℕ) (Λ₂ : GenLat E n₂), LatAdm l bad Λ₂ →
    IsBeta Dw c (unitLat E n₁) 1 ∧
      ∀ β : c.F, IsBeta Dw c (blockLat (unitLat E n₁) Λ₂) β ↔ IsBeta Dw c Λ₂ β

end GlobalTheory.IndefiniteRowSideFullHecke.BlockLatticeAdmissibility
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AdelicNormWeight
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain
open scoped TensorProduct

section Adelic

variable (E : Type) [Field E] [NumberField E] [IsCMField E]

abbrev Plc : Type := HeightOneSpectrum (𝓞 (maximalRealSubfield E))

abbrev AdF : Type := FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)

def AdE : Type := AdF E ⊗[maximalRealSubfield E] E

instance : CommRing (AdE E) := inferInstanceAs (CommRing (AdF E ⊗[maximalRealSubfield E] E))

def adConj : (AdF E ⊗[maximalRealSubfield E] E) →ₐ[maximalRealSubfield E] (AdF E ⊗[maximalRealSubfield E] E) :=
  Algebra.TensorProduct.map (AlgHom.id _ _) (IsCMField.complexConj E).toAlgHom

theorem adConj_adConj (x : AdF E ⊗[maximalRealSubfield E] E) : adConj E (adConj E x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [adConj]
  | add x y hx hy => simp [hx, hy]

instance : StarRing (AdE E) where
  star x := adConj E x
  star_involutive x := adConj_adConj E x
  star_mul x y := by
    show adConj E (x * y) = adConj E y * adConj E x
    rw [mul_comm (adConj E y)]
    exact map_mul (adConj E) x y
  star_add x y := map_add (adConj E) x y

def diagE : E →+* AdE E :=
  (Algebra.TensorProduct.includeRight (R := maximalRealSubfield E) (A := AdF E) (B := E)).toRingHom

def inclF : AdF E →+* AdE E :=
  Algebra.TensorProduct.includeLeftRingHom (R := maximalRealSubfield E) (A := AdF E) (B := E)


variable {E} in
def compF (v : Plc E) : AdF E →ₐ[maximalRealSubfield E] v.adicCompletion (maximalRealSubfield E) where
  toFun a := a v
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl


variable {E} in
def compE (v : Plc E) : AdE E →+* (v.adicCompletion (maximalRealSubfield E) ⊗[maximalRealSubfield E] E) :=
  (Algebra.TensorProduct.map (compF v) (AlgHom.id (maximalRealSubfield E) E)).toRingHom

def intAd : Subring (AdE E) :=
  Subring.closure ((inclF E '' {a | ∀ v : Plc E, a v ∈ v.adicCompletionIntegers (maximalRealSubfield E)}) ∪
    Set.range fun o : 𝓞 E => diagE E (o : E))

abbrev UA (n : ℕ) : Type := Matrix.unitaryGroup (Fin n) (AdE E)

variable {E} {n : ℕ}

def ptsIn (n : ℕ) (R : Subring (AdE E)) : Subgroup (UA E n) where
  carrier := {k | (∀ a b, k.1 a b ∈ R) ∧ ∀ a b, (k⁻¹).1 a b ∈ R}
  one_mem' := by
    have : ∀ a b : Fin n, (1 : UA E n).1 a b ∈ R := fun a b => by
      show (1 : Matrix (Fin n) (Fin n) (AdE E)) a b ∈ R
      rw [Matrix.one_apply]
      split_ifs
      exacts [R.one_mem, R.zero_mem]
    exact ⟨this, by rw [inv_one]; exact this⟩
  mul_mem' := by
    have key : ∀ x y : UA E n, (∀ a b, x.1 a b ∈ R) → (∀ a b, y.1 a b ∈ R) → ∀ a b, (x * y).1 a b ∈ R :=
      fun x y hx hy a b => by
        show (x.1 * y.1) a b ∈ R
        rw [Matrix.mul_apply]
        exact R.sum_mem fun j _ => R.mul_mem (hx a j) (hy j b)
    intro x y hx hy
    exact ⟨key x y hx.1 hy.1, by rw [mul_inv_rev]; exact key _ _ hy.2 hx.2⟩
  inv_mem' := fun {x} hx => ⟨hx.2, by rw [inv_inv]; exact hx.1⟩


variable (E) in
def ratPts (n : ℕ) : Subgroup (UA E n) := ptsIn n (diagE E).range


variable (E) in
def maxCpt (n : ℕ) : Subgroup (UA E n) := ptsIn n (intAd E)

def IsLevelGrp (J : Subgroup (UA E n)) : Prop :=
  J ≤ maxCpt E n ∧
  (∃ m : ℕ, m ≠ 0 ∧ ∀ k ∈ maxCpt E n,
    (∀ a b, ∃ u ∈ intAd E, (k.1 - 1) a b = (m : AdE E) * u) → k ∈ J) ∧
  ∀ k : UA E n, (∀ v : Plc E, ∃ j ∈ J, ∀ a b, compE v (k.1 a b) = compE v (j.1 a b)) → k ∈ J

def TrivOn (S : Finset (Plc E)) (h : UA E n) : Prop :=
  ∀ v ∈ S, ∀ a b, compE v (h.1 a b) = compE v ((1 : Matrix (Fin n) (Fin n) (AdE E)) a b)

def stab (J : Subgroup (UA E n)) (h : UA E n) : Subgroup (UA E n) :=
  ratPts E n ⊓ J.comap (MulAut.conj h⁻¹).toMonoidHom


end Adelic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

abbrev ConjQ (Dw : Datum H) (l : Level H) : Type := Dw.La ⧸ (Mfr l • ⊤ : Submodule (𝓞 E) Dw.La)

def fourierSum {n : ℕ} (ph : (Fin n → ConjQ Dw l) → c.F) : (Fin n → LevQ Dw l) → c.F :=
  fun q => ∑ᶠ x : Fin n → ConjQ Dw l, ph x * zetaM c ^ (-pairL (l := l) (fun b => qRep (x b)) (fun b => levRep (q b)))

def FixesDatum {n : ℕ} (J : Subgroup (UA E n)) (ph : (Fin n → ConjQ Dw l) → c.F) : Prop :=
  ∀ k ∈ J, ∀ κ : Fin n → Fin n → 𝓞 E,
    (∀ a b, ∃ u ∈ intAd E, star (k.1 a b) - diagE E (κ a b : E) = (l.M : AdE E) * u) →
      ∀ x, ph (fun a => ∑ b, κ a b • x b) = ph x




end GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.ReflexNormIndexIdeal
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def indexIdeal (L' L : Submodule (𝓞 E) (Fin n → E)) : Ideal (𝓞 E) :=
  Ideal.span {a | ∃ g : (Fin n → E) →ₗ[E] (Fin n → E), (∀ x ∈ L', g x ∈ L) ∧ (a : E) = LinearMap.det g}

def latIdeal (Λ : Lat E n) : Ideal (𝓞 E) := indexIdeal Λ.L Λ.inter

omit [IsCMField E] in
theorem latIdeal_ne_bot (Λ : Lat E n) : latIdeal Λ ≠ ⊥ := by
  classical
  obtain ⟨S, hS⟩ := Λ.fg
  obtain ⟨k, hk⟩ := IsLocalization.exist_integer_multiples (𝓞 E)⁰ (S ×ˢ (Finset.univ : Finset (Fin n)))
    (fun t => (t.1 t.2 : E))
  have hL : ∀ x ∈ Λ.L, (k : 𝓞 E) • x ∈ stdMod E n := by
    have : Λ.L ≤ (stdMod E n).comap (LinearMap.lsmul (𝓞 E) (Fin n → E) (k : 𝓞 E)) := by
      rw [← hS, Submodule.span_le]
      intro x hx
      refine mem_stdMod.2 fun j => ?_
      obtain ⟨a, ha⟩ := hk (x, j) (by simpa using hx)
      exact ⟨a, ha⟩
    exact fun x hx => this hx
  intro h
  have hm : (k : 𝓞 E) ^ n ∈ latIdeal Λ := by
    refine Ideal.subset_span ⟨((k : 𝓞 E) : E) • LinearMap.id, fun x hx => ⟨hL x hx, Λ.L.smul_mem _ hx⟩, ?_⟩
    rw [LinearMap.det_smul]
    simp
  rw [h, Ideal.mem_bot] at hm
  exact pow_ne_zero n (nonZeroDivisors.coe_ne_zero k) hm


variable {H : Host E} (Dw : Datum H) {l : Level H} (c : Coeff l)

def reflexNorm (γ : E) : c.F := ∏ σ : E →+* ℂ, embF c σ γ ^ Dw.mult σ

def reflexIdeal (𝔞 : Ideal (𝓞 E)) : Ideal (𝓞 c.F) :=
  ∏ σ : E →+* ℂ, 𝔞.map (RingOfIntegers.mapRingHom (embF c σ)) ^ Dw.mult σ

def IsBe (𝔞 : Ideal (𝓞 E)) (β : c.F) : Prop :=
  (∃ b : 𝓞 c.F, (b : c.F) = β ∧ Ideal.span {b} = reflexIdeal Dw c 𝔞) ∧
    ∀ s : c.F →+* ℂ, ‖s β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ (Dw.p + Dw.q)

def IsBeLat (Λ : Lat E n) (β : c.F) : Prop := IsBe Dw c (latIdeal Λ) β

def ReflexLe : Prop := ∀ 𝔞 : Ideal (𝓞 E), 𝔞 ≠ ⊥ → ∃ β : c.F, IsBe Dw c 𝔞 β

theorem isBe_top : IsBe Dw c ⊤ 1 :=
  ⟨⟨1, rfl, by
    simp only [reflexIdeal, Ideal.map_top, Ideal.span_singleton_one]
    simp [← Ideal.one_eq_top]⟩, fun s => by simp⟩

variable {Dw c}


open scoped Classical in
def beIdeal (hK : ReflexLe Dw c) (𝔞 : Ideal (𝓞 E)) (h𝔞 : 𝔞 ≠ ⊥) : c.F :=
  if 𝔞 = ⊤ then 1 else (hK 𝔞 h𝔞).choose

def be (hK : ReflexLe Dw c) (Λ : Lat E n) : c.F := beIdeal hK (latIdeal Λ) (latIdeal_ne_bot Λ)

variable (Dw c)

end GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.NormFactorThetaValue
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation

attribute [local instance] Over.cartesianMonoidalCategory

section TwoLifts

variable {X : Scheme.{0}} (A : Over X) [GrpObj A] [IsCommMonObj A] (L : RigLB A)

def IsTwoLifts (N : ℕ) {T : Over X} (s : LB.Sec (LPow A L.L 1 T)) (x₁ x₂ : T ⟶ A)
    (F : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) : Prop :=
  Odd N ∧ x₁ ^ (N ^ 2) = 1 ∧ x₂ ^ (N ^ 2) = 1 ∧
  ∃ (α₀ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 A.left, (mulA A N).left] ![(N : ℤ) ^ 2, -1]))
    (α : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T A).left, (snd T A ^ N).left] ![(N : ℤ) ^ 2, -1]))
    (s₁ s₂ : LB.Sec (LPow A L.L ((N : ℤ) ^ 2) T)) (U₁ U₂ : ThetaGrp A L.L ((N : ℤ) ^ 2) T),
    α₀.IsGen ∧ IsNormMul A L.L L.rig N α₀ ∧ α.IsGen ∧
    LB.Gen.Corr L.L _ _ _ _ α (LB.pullGen L.L _ _ α₀ (snd T A).left) ∧
    IsTwistPull A L.L (mulT A T N) (snd T A ^ N) (lift_snd _ _) ((N : ℤ) ^ 2) 1 α s s₁ ∧
    SymLift A L.L ((N : ℤ) ^ 2) (N ^ 2) x₁ U₁ ∧ IsActOf A L.L ((N : ℤ) ^ 2) U₁ s₁ s₂ ∧
    SymLift A L.L ((N : ℤ) ^ 2) (N ^ 2) x₂ U₂ ∧ IsActOf A L.L ((N : ℤ) ^ 2) U₂ s₂ F

end TwoLifts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def InKer {n : ℕ} (N : ℕ) (Lm : Submodule (𝓞 E) (Fin n → E))
    (hN : ∀ j, N • (Pi.single j 1 : Fin n → E) ∈ Lm) {T : Over Xo.X} (a : Fin n → (T ⟶ Xo.univ.t.G)) : Prop :=
  (∀ j, a j ^ (N ^ 2) = 1) ∧
    ∀ (f : Lm →ₗ[𝓞 E] (Fin n → 𝓞 E)) (i : Fin n), ∏ j, a j ≫ Xo.univ.t.act.act (f ⟨_, hN j⟩ i) = 1

omit [NumberField E] [IsCMField E] in
theorem nsmul_single_mem_inter {n M N : ℕ} {Λ : Lat E n} (h : Λ.Admissible M N) (j : Fin n) :
    N • (Pi.single j 1 : Fin n → E) ∈ Λ.inter := by
  refine h.2.2 ?_
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_pointwise_smul _ _ _ (single_mem_stdMod j)

omit [NumberField E] [IsCMField E] in
theorem nsmul_single_mem {n M N : ℕ} {Λ : Lat E n} (h : Λ.Admissible M N) (j : Fin n) :
    N • (Pi.single j 1 : Fin n → E) ∈ Λ.L := (nsmul_single_mem_inter h j).2

def InZ {n N : ℕ} {Λ : Lat E n} (h : Λ.Admissible l.M N) {T : Over Xo.X} (a : Fin n → (T ⟶ Xo.univ.t.G)) : Prop :=
  InKer Xo N Λ.L (nsmul_single_mem h) a

def ptRes {S k : Type} [CommRing S] [CommRing k] (x0 : Sp S ⟶ Xo.X) (ψ : S →+* k) :
    ptO Xo (spMap ψ ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap ψ) rfl

def SplitsZ {n N : ℕ} {Λ : Lat E n} (h : Λ.Admissible l.M N) {S : Type} [CommRing S] (x0 : Sp S ⟶ Xo.X)
    {J : Type} (z : J → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)) : Prop :=
  (∀ i, InZ Xo h (z i)) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (ψ : S →+* k) (a : Fin n → (ptO Xo (spMap ψ ≫ x0) ⟶ Xo.univ.t.G)),
      InZ Xo h a → ∃! i, ∀ j, a j = ptRes Xo x0 ψ ≫ z i j

def IsDivPt (N : ℕ) {T : Over Xo.X} (t t' : T ⟶ Xo.univ.t.G) : Prop :=
  t' ^ N = t ∧ KilledBy Xo (halfPart l N ^ 2) t'

def pairBox (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ} (k : ℤ)
    (P : MvPolynomial (LtN Dw n) c.F) (F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L k (ptO Xo y.x))) : S :=
  ∑ m ∈ P.support, algebraMap c.F S (P.coeff m) * ∏ b, nab y k (F b) (colOf m b)

def normFactor {n : ℕ} (Λ : Lat E n) (N : ℕ) (β : c.F) (P : MvPolynomial (LtN Dw n) c.F) : c.F :=
  β⁻¹ * ((Λ.cardCenterZero (Dw.p + Dw.q) N : ℕ) : c.F)⁻¹ * ((N : c.F) ^ P.totalDegree)⁻¹

def SplitVal (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n N : ℕ} {Λ : Lat E n}
    (h : Λ.Admissible l.M N) (β : c.F) (cf : (Fin n → NamedCl Dw l) → c.F) (P : MvPolynomial (LtN Dw n) c.F)
    (v : S) : Prop :=
  ∃ (r : ℕ) (z : Fin r → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (t' : (Fin n → NamedCl Dw l) → Fin n → (ptO Xo y.x ⟶ Xo.univ.t.G))
    (F : (Fin n → NamedCl Dw l) → Fin r → Fin n →
      LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((N : ℤ) ^ 2) (ptO Xo y.x))),
    SplitsZ Xo h y.x z ∧
    (∀ t b, IsDivPt Xo N (levPtCl Xo y.x (t b)) (t' t b)) ∧
    (∀ t i b, IsTwoLifts Xo.univ.t.G Xo.univ.t.PP N y.s (z i b) (t' t b) (F t i b)) ∧
    v = algebraMap c.F S (normFactor c Λ N β P) *
      ∑ t ∈ levelIndex Dw l n, algebraMap c.F S (cf t) * ∑ i, pairBox Xo c nab y ((N : ℤ) ^ 2) P (F t i)

def LocVal (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n N : ℕ} {Λ : Lat E n}
    (h : Λ.Admissible l.M N) (β : c.F) (cf : (Fin n → NamedCl Dw l) → c.F) (P : MvPolynomial (LtN Dw n) c.F)
    (v : S) : Prop :=
  ∃ (S' : Type) (_ : CommRing S') (_ : Algebra c.F S') (φ : S →ₐ[c.F] S') (y' : FrPt Xo c S'),
    φ.toRingHom.FaithfullyFlat ∧ FrMap φ y y' ∧ SplitVal Xo c nab y' h β cf P (φ v)

def InRange {n : ℕ} (Λ : Lat E n) (β : c.F) (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F) : Prop :=
  Λ.InGenus ∧ Λ.StdAt l.M ∧ β ≠ 0 ∧ P ∈ harmLat Dw c a Λ

def ThVal (nab : NabV Xo c) {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) {n : ℕ} (Λ : Lat E n)
    (N : ℕ) (β : c.F) (cf : (Fin n → NamedCl Dw l) → c.F) (a : (E →+* ℂ) × ℕ → ℕ)
    (P : MvPolynomial (LtN Dw n) c.F) (v : S) : Prop :=
  InRange c Λ β a P ∧ ∃ h : Λ.Admissible l.M N, LocVal Xo c nab y h β cf P v

end GlobalTheory.IndefiniteRowSideFullHecke.NormFactorThetaValue
end
end
