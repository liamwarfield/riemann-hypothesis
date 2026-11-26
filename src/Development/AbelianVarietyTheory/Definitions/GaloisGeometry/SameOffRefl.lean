module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LocSpBot
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.DetOfColSpanEq
public import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.PtStep0
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.TrueWtAddSSNonneg
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMulOfApprox

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
noncomputable section

namespace GlobalTheory.TwV.Xc

open NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n p : ℕ} {G : GAtP p}

def phiA (A : LocAt F E n G) (v : Fin G.P.nV) : AfE F E →+* G.P.Qq v :=
  ((A.eQ v).symm : (A.pl v).1.adicCompletion F →+* G.P.Qq v).comp ((A.ph v).comp (prV (E := E) (A.pl v).1))

def ordA (A : LocAt F E n G) (v : Fin G.P.nV) (x : (AfE F E)ˣ) : ℤ := ordP (G.P.W v) p (phiA A v (x : AfE F E))

def OneOff (w : HeightOneSpectrum (𝓞 F)) (x : (AfE F E)ˣ) : Prop :=
  ∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → prV (E := E) w' (x : AfE F E) = 1

def SameOff (w : HeightOneSpectrum (𝓞 F)) {N : ℕ} (x y : GL (Fin N) (AfE F E)) : Prop :=
  ∀ w' : HeightOneSpectrum (𝓞 F), w' ≠ w → bc (prV (E := E) w') x = bc (prV (E := E) w') y

def PrimeOf (p : ℕ) (W : Type) {Q : Type} [CommRing W] [Field Q] [Algebra W Q] (ρ : E →+* Q) (P : HeightOneSpectrum (𝓞 E)) : Prop :=
  ∀ x : 𝓞 E, ∃ y : W, ρ x = algebraMap W Q y ∧ (x ∈ P.asIdeal ↔ (p : W) ∣ y)

def eMat {a N : ℕ} (hr : a = N) (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (γ : GL (Fin N) E) : Matrix (Fin a) (Fin a) E :=
  (LinearMap.toMatrix' (stdG σ J γ).toLinearMap).submatrix (finCongr hr) (finCongr hr)

theorem phiA_incl (A : LocAt F E n G) (v : Fin G.P.nV) (x : E) : phiA A v (x ⊗ₜ[F] 1) = A.iw v x := by
  have hp : prV (E := E) (A.pl v).1 (x ⊗ₜ[F] (1 : FiniteAdeleRing (𝓞 F) F)) = x ⊗ₜ[F] 1 := by
    simp [prV]
  simp only [phiA, LocAt.iw, LocAt.phE, RingHom.comp_apply, hp]
  rfl

end GlobalTheory.TwV.Xc

end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
noncomputable section

namespace GlobalTheory.SplitRead

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh GlobalTheory.RowTie GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL

section Local

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

structure Irr (n : ℕ) : Type 1 where

  V : Type
  [acg : AddCommGroup V]
  [mod : Module ℂ V]

  π : Representation ℂ (GL (Fin n) k) V
  smooth : IsSmooth π
  irr : π.IsIrreducible

attribute [instance] Irr.acg Irr.mod


variable {k} in
def Irr.ofDet (n : ℕ) (χ : kˣ →* ℂˣ) (h : IsSmoothChar χ) : Irr k n where
  V := ℂ
  π := detRep (Fin n) χ
  smooth := (isSmooth_ofChar_iff _).2 h.detChar
  irr := isIrreducible_ofChar _


instance (n : ℕ) : Inhabited (Irr k n) := ⟨Irr.ofDet n 1 (isSmoothChar_of_isUnram fun _ _ => rfl)⟩


variable {k} in
@[reducible] def Irr.toIrrRep {n : ℕ} (π : Irr k n) : IrrRep (GL (Fin n) k) := ⟨π.V, π.π, π.smooth, π.irr⟩


variable {k} in
@[reducible] def Irr.ofIrrRep {n : ℕ} (σ : IrrRep (GL (Fin n) k)) : Irr k n := ⟨σ.V, σ.ρ, σ.smooth, σ.irr⟩




def TameSplit : Prop := ∀ (r t : ℕ) (χ : kˣ →* ℂˣ) (π : Irr k (r + t)) (v : π.V), IsSmoothChar χ → IsTame χ →
  ¬ IsUnram χ → v ≠ 0 → IsParahoricVec χ π.π v →
  ∃ (π₁ : Irr k r) (π₂ : Irr k t), IsSpherical π₁.π ∧ IsSpherical π₂.π ∧
    Nonempty (π.π.Equiv (prod₂ π₁.π (twist π₂.π (detChar (Fin t) χ))))

variable {k} {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def speh (a : WD h) (d : ℕ) : WD h :=
  (List.range d).foldr (fun j acc => (a.lpTw (((d : ℝ) - 1) / 2 - j)).lpSum acc) (WD.lpZero (h := h))

structure RecLaws (rc : ∀ n, Irr k n → WD h) : Prop where
  dim : ∀ n π, (rc n π).lpDim = n
  iso : ∀ n (π π' : Irr k n), rc n π = rc n π' ↔ Nonempty (π.π.Equiv π'.π)
  prod : ∀ r t (σ : Irr k r) (τ : Irr k t) (π : Irr k (r + t)), Nonempty (π.π.Equiv (prod₂ σ.π τ.π)) →
    rc (r + t) π = (rc r σ).lpSum (rc t τ)
  det : ∀ t (χ : kˣ →* ℂˣ) (c : Irr k 1) (τ : Irr k t), Nonempty (c.π.Equiv (detRep (Fin 1) χ)) →
    Nonempty (τ.π.Equiv (detRep (Fin t) χ)) → rc t τ = speh (rc 1 c) t
  twist : ∀ n (χ : kˣ →* ℂˣ) (c : Irr k 1) (π π' : Irr k n), Nonempty (c.π.Equiv (detRep (Fin 1) χ)) →
    Nonempty (π'.π.Equiv (twist π.π (detChar (Fin n) χ))) → rc n π' = (rc n π).lpChar (rc 1 c)
  sph : ∀ n (π : Irr k n), (rc n π).unr ↔ IsSpherical π.π
  sat : ∀ n (π : Irr k n) (α : Fin n → ℂˣ), HasSatake π.π α →
    (rc n π).frobEig = Finset.univ.val.map fun i => ((α i)⁻¹ : ℂˣ).1

end Local

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

structure ReadAt (T : WDTie N A) (i : N.Loc) (w : PlE H) : Type 1 where

  rc : ∀ n, Irr (w.adicCompletion H.E) n → WD (E := H.E) (A := N.plOm.1 w) (w := w) (N.plOm.2 w)

  row : what₂.FT → Irr (w.adicCompletion H.E) R.r

  rep : A.AV i → Irr (w.adicCompletion H.E) (R.r + R.t)

  mu : (w.adicCompletion H.E)ˣ →* ℂˣ
  eta : (w.adicCompletion H.E)ˣ →* ℂˣ
  mu_ok : IsSmoothChar mu ∧ IsUnitaryChar mu
  eta_ok : IsSmoothChar eta ∧ IsUnram eta
  locW : ∀ σ, what₂.isot (N.j i) σ ≠ ⊥ → T.e w (A.locW i σ w) = rc _ (row σ)
  locV : ∀ P, T.e w (A.locV i P w) = rc _ (rep P)
  locMu : ∀ c : Irr (w.adicCompletion H.E) 1, Nonempty (c.π.Equiv (detRep (Fin 1) mu)) →
    T.e w (A.locG (A.muC i) w) = rc 1 c
  locEta : ∀ c : Irr (w.adicCompletion H.E) 1, Nonempty (c.π.Equiv (detRep (Fin 1) eta⁻¹)) →
    T.e w (A.locG A.etaTinv w) = rc 1 c

abbrev Reading (T : WDTie N A) : Type 1 := ∀ (i : N.Loc) (w : PlE H), IsSplitPl H w → ReadAt T i w

variable {T : WDTie N A} (S : Reading T)

def Laws : Prop := ∀ i w hw, RecLaws (S i w hw).rc

def RowUnit : Prop := ∀ i w hw σ, what₂.isot (N.j i) σ ≠ ⊥ → IsUnitarisable ((S i w hw).row σ).π

def PairRead : Prop := ∀ i w hw σ P, Pairs N A i σ P →
  ThetaPair (S i w hw).mu ((S i w hw).row σ).π
    (twist ((S i w hw).rep P).π (detChar (Fin (R.r + R.t)) (S i w hw).eta))

def TypeTame (i : N.Loc) (w : PlE H) (hw : IsSplitPl H w) : Prop :=
  IsTame (S i w hw).mu ∧ ¬ IsUnram (S i w hw).mu ∧
    ∀ P, ∃ v, v ≠ 0 ∧ IsParahoricVec (S i w hw).mu ((S i w hw).rep P).π v

def TameSplitAll (E : Type) [Field E] [NumberField E] : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 E), TameSplit (w.adicCompletion E)

end GlobalTheory.SplitRead
end
end

section -- merged from Development.AbelianVarietyTheory.Definitions.GaloisGeometry.JetStepEqZeroExample
noncomputable section

namespace GlobalTheory.GO

open NumberField Formalism.L2.Col Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms

section Exp

open MvPolynomial Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint

variable {ι : Type} [Fintype ι] {a b : ℕ}

end Exp

namespace ChSrc

open Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint

variable {X : Fields} {R : Ranks} (σ : X.K →+* ℂ)

theorem jetInVV_trueWt (hc : X.Tau → HCParam R) {i : ℕ} (hi : i < R.m) : JetInVV X.K (trueWt hc i) (trueWt hc (i + 1)) (nuEnd hc i) := by
  have hab : R.N i < R.N (i + 1) := by
    simp only [Ranks.N]
    nlinarith
  have hW : WtCompat hab (trueWt hc i) (trueWt hc (i + 1)) (sD hc i) (sS hc i) (nuEnd hc i) := by
    refine ⟨fun τ a => ?_, fun τ j hj => trueWt_new hc hi τ j (by omega), fun τ => nuEnd_cast hc hi τ⟩
    have h1 := trueWt_old hc hi τ (Fin.castLE hab.le a) (by simp)
    simp only [Fin.coe_castLE] at h1
    rw [h1]
    ring
  haveI : Infinite X.K := Infinite.of_injective (Nat.cast : ℕ → X.K) Nat.cast_injective
  intro J P hP
  exact GlobalTheory.JetPoint.jetMap_mem hab.le (nuEnd hc i) P _
    (fun ap => GlobalTheory.SubstMem.substAdj_sharp_mem X.K X.Tau _ _ hab _ _ _ _ _ hW ap P hP) J

end ChSrc

end GlobalTheory.GO
end
end
