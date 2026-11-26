module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
public import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VacuumCharacterDeterminant
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open GlobalTheory.SW hiding Level
open GlobalTheory.Ker
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate ComplexOrder Classical ENNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev Fam (D : D7) (m n : ℕ) : Type := D.what₂.Tau → Matrix (Fin m) (Fin n) ℂ

def realOf (θ : InfFam D) {m n : ℕ} (z : Fam D m n) : Mx D m n := ∑ τ, lineAt θ τ (z τ) 1

section Forms

variable (S T : HSp D)

def hAt (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) : ℂ :=
  Matrix.trace ((gramAt D S τ)⁻¹ * yᴴ * gramAt D T τ * x)

def efR (x y : Fam D T.rank S.rank) : ℝ :=
  -∑ τ, 2 * (tauE D τ D.host.xi0 * hAt S T τ (x τ) (y τ)).re

def cxJ (s : Fam D T.rank T.rank) (x : Fam D T.rank S.rank) : Fam D T.rank S.rank :=
  fun τ => cplxO 1 (s τ) (x τ)

def hermH (s : Fam D T.rank T.rank) (x y : Fam D T.rank S.rank) : ℂ :=
  (efR S T (cxJ S T s x) y : ℂ) + Complex.I * (efR S T x y : ℂ)

end Forms

section Moved

variable (θ : InfFam D) (S T : HSp D)

def movS (sT : Fam D T.rank T.rank) (g : GA D T) : Fam D T.rank T.rank :=
  fun τ => compAt θ τ (mt T g) * sT τ * compAt θ τ (mt T g⁻¹)

def frameFn (sT : Fam D T.rank T.rank) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (f : WO S T → ℂ)
    (g : GA D T) (z : Fam D T.rank S.rank) : ℂ :=
  Complex.exp (Real.pi * hermH S T (movS θ T sT g) z z / 2) * om (1, g) f (realOf θ z)

end Moved

section Canon

variable (S T : HSp D) (s : Fam D T.rank T.rank) (BS : Fam D S.rank S.rank) (BT : Fam D T.rank T.rank)
  (Γ : Set (Matrix (Fin T.rank) (Fin S.rank) D.host.E))

end Canon

section Chars

def detPos {r : ℕ} (s k : Matrix (Fin r) (Fin r) ℂ) : ℂ :=
  (k * ((1 / 2 : ℂ) • (1 + s)) + (1 / 2 : ℂ) • (1 - s)).det

def detNeg {r : ℕ} (s k : Matrix (Fin r) (Fin r) ℂ) : ℂ := detPos (-s) k

def vacChar (θ : InfFam D) (T : HSp D) (sT : Fam D T.rank T.rank) (n : ℕ) (a : D.what₂.Tau → ℤ) (k : GA D T) : ℂ :=
  ∏ τ, detPos (sT τ) (compAt θ τ (mt T k)) ^ (a τ + ((n / 2 : ℕ) : ℤ)) *
    detNeg (sT τ) (compAt θ τ (mt T k)) ^ (a τ - ((n / 2 : ℕ) : ℤ))

end Chars

end GlobalTheory.IndefiniteRowSideFullHecke.VacuumCharacterDeterminant

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EigenvectorLieDegree
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj nonZeroDivisors

namespace GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree

section Adelic

variable {L : Type} [Field L] [NumberField L]

def adDeg (r : HeightOneSpectrum (𝓞 L) → ℝ) (N : (L →+* ℂ) → ℝ) : ℝ :=
  (∑ᶠ 𝔭, r 𝔭 * Real.log (Ideal.absNorm 𝔭.asIdeal) - (1 / 2) * ∑ σ, Real.log (N σ)) / Module.finrank ℚ L

end Adelic

section Eigen

variable {R O : Type} [CommRing R] [CommRing O] {G : Over (Sp R)} [GrpObj G]

def IsEigVec (act : OAct O G) (χ : O →+* R) (v : epsR R ⟶ G) : Prop :=
  IsTangent v ∧ ∀ a, (v ≫ act.act a).left = spMap (epsScaleR (χ a)) ≫ v.left

def IsEigBasis (act : OAct O G) (χ : O →+* R) {m : ℕ} (v : Fin m → (epsR R ⟶ G)) : Prop :=
  (∀ i, IsEigVec act χ (v i)) ∧ ∀ w, IsEigVec act χ w → ∃! c : Fin m → R, IsLieComb c v w

end Eigen

section Local

variable {L : Type} [Field L] [NumberField L] (A : Over (Sp L)) [GrpObj A] {m : ℕ}

def IsArchSq (𝓛 : LB A.left) (v : Fin m → (epsR L ⟶ A)) (σ : L →+* ℂ) (N : ℝ) : Prop :=
  ∃ (A' : Over (Sp ℂ)) (_ : GrpObj A') (φ : A'.left ⟶ A.left) (g : ℕ) (u : HolUnif A' (𝓛.pull φ) g)
    (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ) (v' : Fin m → (epsR ℂ ⟶ A')) (W : Fin m → Fin g → ℂ),
    IsGrpPullback A' A (spMap σ) φ ∧ u.IsAH Hm χ ∧ (∀ i, IsVecOver σ φ (v i) (v' i) ∧ u.IsDiff (W i) (v' i)) ∧
    0 < N ∧ (N : ℂ) = (Matrix.of fun i k => (Real.pi : ℂ) * (W i ⬝ᵥ Hm.mulVec (star (W k)))).det

end Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Lines

variable {L : Type} [Field L] [NumberField L]

def ordIdeal (τ : E →+* L) (𝔞 : Ideal (𝓞 E)) (𝔭 : HeightOneSpectrum (𝓞 L)) : ℤ :=
  FractionalIdeal.count L 𝔭
    ((𝔞.map (RingOfIntegers.mapRingHom τ) : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L)

def ordTwist (H : Host E) (τ : E →+* L) (𝔭 : HeightOneSpectrum (𝓞 L)) : ℤ :=
  (ordIdeal τ (differentIdeal ℤ (𝓞 E)) 𝔭 - ordIdeal τ (Ideal.span {H.rt}) 𝔭) - ordIdeal τ (Ideal.span {H.rt}) 𝔭

end Lines

def cOne (H : Host E) (p q : ℕ) (logOm : ℝ) : ℝ :=
  -(((p : ℝ) - q) / 2 * logOm) - q * (2 * Real.log √(H.d : ℝ) - Real.log (rootDiscr E))

def IsHostField (H : Host E) : Prop :=
  IsAbelianGalois ℚ E ∧
  ∀ w : HeightOneSpectrum (𝓞 E), w.asIdeal ∣ differentIdeal ℤ (𝓞 E) →
    w.asIdeal.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ w.asIdeal ∧
    ∀ ℓ : ℕ, ℓ.Prime → (ℓ : 𝓞 E) ∈ w.asIdeal →
      (ℓ ≠ H.d ∧ IsSquare (-(H.d : ZMod ℓ))) ∨ (ℓ = H.d ∧ ¬ w.asIdeal ^ 3 ∣ Ideal.span {(ℓ : 𝓞 E)})

end GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UniformLevelMultiplicity
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Mult
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Side (D : D7) (σ : D.what₂.LL →+* ℂ) : Prop :=
  ∀ x : D.host.K, σ (D.embE (algebraMap D.host.K D.host.E x)) =
    D.what₂.embLL (D.embE (algebraMap D.host.K D.host.E x))

def SitsAt (D : D7) (σ : D.what₂.LL →+* ℂ) (τ τ' : D.what₂.Tau) : Prop :=
  ∃ t : D.host.E →+* D.what₂.LL, D.what₂.embLL.comp t = tauE D τ ∧ σ.comp t = tauE D τ'

def IsConjPar (D : D7) (j : ℕ) (σ : D.what₂.LL →+* ℂ) (S : D.what₂.Tau → SPar) : Prop :=
  ∀ τ', ∃ τ, SitsAt D σ τ τ' ∧ S τ' = parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j)) τ

variable {D : D7}

def levSet (V : HSp D) (N : ℕ) : Set (GA D V) :=
  {k | k ∈ GfC V ∧ ∀ z ∈ latHat V, ∃ y ∈ latHat V, (finHom V k).1.mulVec z - z = N • y}

def IsCover (V : HSp D) {G0 : Type} [Group G0] (Lift : G0 → GA D V → Prop) : Prop :=
  (∀ κ, κ ∈ levSet V 1 ↔ ∃ g, Lift g κ) ∧ (∀ g, ∃ κ, Lift g κ) ∧
    (∀ g g' κ, Lift g κ → Lift g' κ → g = g') ∧
    (∀ g g' κ κ', Lift g κ → Lift g' κ' → Lift (g * g') (κ * κ')) ∧
    ∀ κ, Lift 1 κ ↔ κ ∈ levSet V (D.host.g 0 * D.host.g 1)

variable (T : CoreJ D) (j : ℕ)

def rdK (w : WeightFamilies.Wt D j) (s : T.Q.c.F →+* ℂ) (c : (T.U j s).Comp → ℂ) : T.R j →ₛₗ[s] (GA D (T.V j s) → ℂ) :=
  ((lieFac (T.Q.Dw j) (xiR D) (wtA w) : ℂ) •
    adel (T.V j s) (T.dict j s) (muPin (T.V j s) (T.dict j s) (T.mu j s) c)).comp (rdU (T.U j s))

variable [Algebra T.Q.c.F D.what₂.LL]

end GlobalTheory.IndefiniteRowSideFullHecke.EmbeddingLevelSets
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LevelLiftConditions
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open GlobalTheory.FormTies (levFull)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Level

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

abbrev LevGrp (Dw : Datum H) (l : Level H) : Type := LaMod Dw l ≃ₗ[𝓞 E] LaMod Dw l

def levDet (Dw : Datum H) (l : Level H) : LevGrp Dw l →* (𝓞 E ⧸ l.Mb)ˣ where
  toFun γ := LinearEquiv.det
    (γ.extendScalarsOfSurjective (S := 𝓞 E ⧸ l.Mb) Ideal.Quotient.mk_surjective)
  map_one' := by
    rw [← map_one (LinearEquiv.det (R := 𝓞 E ⧸ l.Mb) (M := LaMod Dw l))]
    rfl
  map_mul' γ δ := by
    rw [← map_mul]
    rfl

end Level

variable {D : D7}

def idealHat (D : D7) (I : Ideal (𝓞 D.host.E)) : AddSubgroup (Af D.host.F ⊗[D.host.F] D.host.E) :=
  AddSubgroup.closure {z | ∃ b ∈ I, ∃ y ∈ intAE D, z = ((1 : Af D.host.F) ⊗ₜ (b : D.host.E)) * y}

def CongMod (I : Ideal (𝓞 D.host.E)) (x : (AE D)ˣ) (u : 𝓞 D.host.E) : Prop :=
  finPart D (x : AE D) - (1 : Af D.host.F) ⊗ₜ (u : D.host.E) ∈ idealHat D I

def IsInvTame {K : Type} [Field K] (σ : K →+* ℂ) (Mb Mc : Ideal (𝓞 D.host.E)) (μ : (AE D)ˣ →* Circle)
    (χ : (𝓞 D.host.E ⧸ Mb)ˣ →* Kˣ) : Prop :=
  ∀ x : (AE D)ˣ, FinUnit x → ∀ (u : 𝓞 D.host.E) (ub : (𝓞 D.host.E ⧸ Mb)ˣ),
    (ub : 𝓞 D.host.E ⧸ Mb) = Ideal.Quotient.mk Mb u → CongMod Mb x u → CongMod Mc x 1 →
      σ ((χ ub : Kˣ) : K) * ((μ x : Circle) : ℂ) = 1

def IsLevLift {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} (l : Level H) (V : HSp D)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (γ : LevGrp Dw l) (κ : GA D V) : Prop :=
  κ ∈ GfC V ∧ gLat V κ = (latHat V : Set _) ∧
    ∀ a ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
    ∀ a' ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La),
      (l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a' = γ ((l.Mb • (⊤ : Submodule (𝓞 D.host.E) Dw.La)).mkQ a) →
      ∃ w ∈ latGHat V 1, (finHom V κ).1.mulVec (finVec V (ι a)) - finVec V (ι a') = (l.M : ℕ) • w

end GlobalTheory.IndefiniteRowSideFullHecke.LevelLiftConditions
end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.BadPlacesGoodCoefficients
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Lev Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.BadPlacesGoodCoefficients

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def badPlaces (D : D7) : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
  Formalism.L2.DIV.primesOf (((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F))

def IsReadingPlaces (D : D7) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) : Prop :=
  ∃ pb : Fin 2 → 𝓞 D.host.E, (∀ i, (pb i : D.host.E) ∈ D.host.K) ∧ IsTypePlaces (D := D) D.host.g pb Pg

def IsBelow {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} (b : Pg ≃ LevelCuspCharacters.Sq D.host) : Prop :=
  ∀ PP : Pg, (b PP).2.1.asIdeal = PP.1.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))

def IsFrameAtG (V : HSp D) (β : GL (Fin V.rank) (EAf D)) : Prop :=
  ∃ (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (c : ℕ), IsBaseFrame V β Λ ((D.host.g 0 * D.host.g 1) ^ c)

def datR (V : HSp D) (hr : D.R.r ≤ V.rank) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (P : Formalism.L2.DIV.LevelP Pg D.R.r ℂ)
    (fr : Lev.Frm) : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank :=
  datY V.rank D.R.r D.R.t 0 hr Pg ∅ P (fun _ _ => 1) (fun _ => 1) fr

def eLin (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (e : Formalism.L2.DIV.G0 L.Pg L.r →₀ ℂ) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun := eAct V β L e
  map_add' F G := by
    funext h
    simp only [eAct, Finsupp.sum, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    unfold actG0
    split_ifs
    · simp only [Pi.add_apply]; ring
    · simp
  map_smul' a F := by
    funext h
    simp only [eAct, Finsupp.sum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    unfold actG0
    split_ifs
    · simp only [Pi.smul_apply, smul_eq_mul]; ring
    · simp

theorem rank_le_first_space_rank (D : D7) : D.R.r ≤ (D.sp.Y 0).rank := by
  rw [D.sp.Y_rank 0 (Nat.zero_le _)]
  simp [Ranks.rankY]

section Parts

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}

def rowPart (M : DSModel (D.sp.Y 0) (parB (tparRec D) 0)) (β : GL (Fin (D.sp.Y 0).rank) (EAf D))
    (P : Formalism.L2.DIV.LevelP Pg D.R.r ℂ) (e : Formalism.L2.DIV.G0 Pg D.R.r →₀ ℂ)
    (c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ) : Submodule ℂ (MMap M) :=
  EEpart θ M (levG (D.sp.Y 0) β (datR _ (rank_le_first_space_rank D) Pg P Lev.Frm.B) : Set (GA D (D.sp.Y 0)))
    (levChi (D.sp.Y 0) β (datR _ (rank_le_first_space_rank D) Pg P Lev.Frm.B))
    (eLin (D.sp.Y 0) β (datR _ (rank_le_first_space_rank D) Pg P Lev.Frm.B) e) (badPlaces D) c

end Parts

def gramIn (V : HSp D) (β : GL (Fin V.rank) (EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (EAf D) :=
  Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) β.val *
    V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * β.val

def Matched (V V' : HSp D) (h : V'.rank = V.rank) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (β : GL (Fin V.rank) (EAf D)) (β' : GL (Fin V'.rank) (EAf D)) : Prop :=
  ∃ y : GL (Fin V'.rank) (Formalism.L2.Herm.intAf D.host.F D.host.E),
    (∀ PP ∈ Pg, Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP) y = 1) ∧
    gramIn V' (β' * Formalism.L2.DIV.intGL D.host.F D.host.E V'.rank y) = (gramIn V β).submatrix (Fin.cast h) (Fin.cast h)

end GlobalTheory.IndefiniteRowSideFullHecke.BadPlacesGoodCoefficients

end
end

section -- merged from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LinearCoefficientData
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.L2.DIV
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.LinearCoefficientData

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsRecPlaces (D : D7) (Pg : Finset (Pl D.host.E)) : Prop :=
  ∀ PP, PP ∈ Pg ↔ ∃ kv : (Σ k : Fin 2, D.nd.PlG k), D.naut.plGw kv.1 kv.2 = PP

def resMap {E : Type} [Field E] [NumberField E] (p : ℕ) (PP : Pl E) (h : (p : 𝓞 E) ∈ PP.asIdeal) :
    ZMod p →+* kP PP :=
  ZMod.castHom (m := ringChar (kP PP))
    ((ringChar.spec (kP PP) p).1 (by
      rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 h)) (kP PP)

def idx {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) (PP : ↥Pg) : (Σ k : Fin 2, D.nd.PlG k) :=
  ((h PP.1).1 PP.2).choose

theorem idx_spec {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) (PP : ↥Pg) :
    D.naut.plGw (idx h PP).1 (idx h PP).2 = PP.1 :=
  ((h PP.1).1 PP.2).choose_spec

theorem idx_mem {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) (PP : ↥Pg) :
    ((D.host.g (idx h PP).1 : ℕ) : 𝓞 D.host.E) ∈ PP.1.asIdeal := by
  have h1 := D.naut.plGw_over (idx h PP).1 (idx h PP).2
  rw [idx_spec h PP] at h1
  exact h1

def toG0 {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) (γ : G0g D.nd) : G0 Pg D.R.r := fun PP =>
  Matrix.GeneralLinearGroup.map (resMap (D.host.g (idx h PP).1) PP.1 (idx_mem h PP)) (γ (idx h PP))

def eCoef {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) : G0 Pg D.R.r →₀ ℂ :=
  Finsupp.mapDomain (toG0 h) D.ntypes.e0.coeff

def datR (V : HSp D) (hr : V.rank = D.R.r) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg D.R.r ℂ) (fr : Lev.Frm) :
    LevDat D.host.E ℂ V.rank :=
  Lev.datY V.rank D.R.r D.R.t 0 hr.ge Pg ∅ P (fun _ _ => 1) (fun _ => 1) fr

def eLin (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (e : G0 L.Pg L.r →₀ ℂ) :
    (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun F := Lev.eAct V β L e F
  map_add' F G := by
    funext x
    simp only [Lev.eAct, Finsupp.sum, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    unfold Lev.actG0
    split_ifs
    · simp only [Pi.add_apply]; ring
    · simp
  map_smul' c F := by
    funext x
    simp only [Lev.eAct, Finsupp.sum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    unfold Lev.actG0
    split_ifs
    · simp only [Pi.smul_apply, smul_eq_mul]; ring
    · simp

theorem rank_zeroth_component_eq (D : D7) : (D.sp.Y 0).rank = D.R.r := by
  rw [D.sp.Y_rank 0 (Nat.zero_le _)]; simp [Ranks.rankY]

abbrev InfFam (D : D7) : Type := D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)

abbrev Eig (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

abbrev datE (D : D7) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg D.R.r ℂ) : LevDat D.host.E ℂ (D.sp.Y 0).rank :=
  datR (D.sp.Y 0) (rank_zeroth_component_eq D) Pg P Lev.Frm.B

abbrev datWj (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg D.R.r ℂ) :
    LevDat D.host.E ℂ (D.sp.W j).rank :=
  datR (D.sp.W j) (D.sp.W_rank j h1 h2) Pg P Lev.Frm.A

def EEc (θ : InfFam D) (M : Mult.DSModel (D.sp.Y 0) (Mult.parB (Mult.tparRec D) 0)) {Pg : Finset (Pl D.host.E)}
    (h : IsRecPlaces D Pg) (β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (P : LevelP Pg D.R.r ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : Eig D) : Submodule ℂ (Mult.MMap M) :=
  Mult.EEpart θ M (Lev.levG (D.sp.Y 0) β (datE D Pg P)) (Lev.levChi (D.sp.Y 0) β (datE D Pg P))
    (eLin (D.sp.Y 0) β (datE D Pg P) (eCoef h)) S c

def Wc (θ : InfFam D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (M : Mult.DSModel (D.sp.W j) (Mult.parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j)))) {Pg : Finset (Pl D.host.E)}
    (h : IsRecPlaces D Pg) (β : GL (Fin (D.sp.W j).rank) (Lev.EAf D)) (P : LevelP Pg D.R.r ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : Eig D) : Submodule ℂ (Mult.MMap M) :=
  Mult.Wpart θ j M (Lev.levG (D.sp.W j) β (datWj D j h1 h2 Pg P)) (Lev.levChi (D.sp.W j) β (datWj D j h1 h2 Pg P))
    (eLin (D.sp.W j) β (datWj D j h1 h2 Pg P) (eCoef h)) S c

end GlobalTheory.IndefiniteRowSideFullHecke.LinearCoefficientData

end
end
