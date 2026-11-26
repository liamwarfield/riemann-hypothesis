module

public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant
public import Formalism.LocalToGlobal.HermitianForms.Interlace
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkMin
public import Formalism.LocalToGlobal.HermitianForms.ExtraSym

@[expose] public section

section -- merged from Formalism.LocalToGlobal.HermitianForms.TiedBr
noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts NumberField

variable {D : D7}

def bZ (u : D.what₂.Word) (z0 : Fin (D.R.N D.R.m) → D.host.E) :
    Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E :=
  fun a b => if hb : (b : ℕ) < D.R.N D.R.m - 1 then iXm D a ⟨b, hb⟩ else z0 a / ((D.mem u).A.T : D.host.E)

def mZ (u : D.what₂.Word) (z0 : Fin (D.R.N D.R.m) → D.host.E) :
    D.what₂.Tau → Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ :=
  atInf (embT D) (bZ u z0)⁻¹

theorem mZ_isUnit {u : D.what₂.Word} {z0 : Fin (D.R.N D.R.m) → D.host.E} (hB : IsUnit (bZ u z0).det) (τ : D.what₂.Tau) :
    IsUnit (mZ u z0 τ).det := by
  have h1 : IsUnit ((bZ u z0)⁻¹).det := Matrix.isUnit_nonsing_inv_det _ hB
  have h2 : IsUnit ((embT D τ).mapMatrix (bZ u z0)⁻¹).det := by
    rw [← RingHom.map_det]
    exact h1.map _
  exact h2

end Formalism.L2.Forms
end
end

section -- merged from Formalism.LocalToGlobal.HermitianForms.TiedTwSymAll
section -- merged from Formalism.LocalToGlobal.HermitianForms.TiedTwSymP
section -- merged from Formalism.LocalToGlobal.HermitianForms.TiedTwP
section -- merged from Formalism.LocalToGlobal.HermitianForms.TiedTwPGen
noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {D : D7}

section Gen

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P)

def sgTG : D.what₂.Tau → DomWeight (D.R.N D.R.m - 1) :=
  fun τ => shW (M.sg τ) ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℤ)


set_option maxHeartbeats 1000000 in
structure ClassesAtPrimes (bad : Set (HeightOneSpectrum (𝓞 D.host.F))) where
  lev : StepLevel D.host.F D.host.E (sigD D) (gramP D) 1 D.R.f bad

  y : M.clsP → UPts (sigD D) (gramP D) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls lev))

  lat : M.clsP → Submodule (𝓞 D.host.E) (Fin (D.R.N D.R.m - 1) → D.host.E)
  y_lat : ∀ c (x : Fin (D.R.N D.R.m - 1) → D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F))
      (lat c) ↔
    ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) lev.Lb
  lat_fin : ∀ c, Module.Finite (𝓞 D.host.E) (lat c)

  stabI : ∀ c, M.stabilizer₂ c →* UJ (sigD D : D.host.E →+* D.host.E) (gramP D)
  stabI_inj : ∀ c, Function.Injective (stabI c)
  stabI_range : ∀ c (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramP D)),
    γ ∈ (stabI c).range ↔
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
        lev.U.map (MulAut.conj (y c).1).toMonoidHom

variable {M}


set_option maxHeartbeats 1000000 in
structure ValuationAtPrimes {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} (K : ClassesAtPrimes M bad) (okW : D.what₂.places.Pl → Prop) where

  sg : ∀ τ (i : Fin (D.R.N D.R.m - 1)),
    ((M.sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i

  eW : P.Wrow ≃ₗ[ℂ] (M.clsP → FrP D → ℂ)

  ptC : ∀ z, z ∈ M.ptC ↔ eW z ∈ FiC K.lev (embT D) (sgTG M) K.y

  ipP : ∀ (o : FrP D), o.IsON → ∀ (z z' : P.Wrow)
    (Pc Qc : M.clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) ℂ),
    (∀ c, Pc c ∈ CSpan M.sg) → (∀ c, Qc c ∈ CSpan M.sg) →
    (∀ c, eW z c = fnOf _ (shiftOf (sgTG M)) (fun τ => (o.1 τ)⁻¹) (Pc c)) →
    (∀ c, eW z' c = fnOf _ (shiftOf (sgTG M)) (fun τ => (o.1 τ)⁻¹) (Qc c)) →
    M.ipP z z' = ∑ c, ((Nat.card (M.stabilizer₂ c) : ℕ) : ℂ)⁻¹ * nfAll M.sg (Qc c) (Pc c)

  rat : ∀ z, (∃ x, M.ptEmb x = z) ↔
    z ∈ M.ptC ∧ ∀ c, ∃ Pc ∈ RatSpan D M.sg, eW z c = fnOf _ (shiftOf (sgTG M)) 1 Pc

  lat : ∀ w, okW w → ∀ x : M.ptLat.V, x ∈ M.SP w ↔
    ∀ (c : M.clsP) (B : GL (Fin (D.R.N D.R.m - 1)) D.host.E),
      IsLocBasis (D.what₂.places.resChar w) (K.lat c : Set _) B →
      ∃ Pc ∈ IntSpan D w M.sg, eW (M.ptEmb x) c =
        fnOf _ (shiftOf (sgTG M)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N D.R.m - 1)) D.host.E).1) Pc

def NormPTieG {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {K : ClassesAtPrimes M bad} {okW : D.what₂.places.Pl → Prop}
    (W : ValuationAtPrimes K okW) : Prop :=
  ∀ (s : D.what₂.LL →+* ℂ) (x : M.ptLat.V)
    (Pc : M.clsP → MvPolynomial (D.what₂.Tau × Fin (D.R.N D.R.m - 1) × Fin (D.R.N D.R.m - 1)) D.what₂.LL),
    (∀ c, W.eW (M.ptEmb x) c =
      fnOf _ (shiftOf (sgTG M)) 1 (MvPolynomial.map D.what₂.embLL (Pc c))) →
    ∀ o : Frames (gramC (gramP D) (embS D s)), o.IsON →
      (Formalism.HermitianLatticesTheory.majAt M.ptLat.b M.ptLat.X (InfinitePlace.mk s) x x).re =
        ∑ c, ((Nat.card (M.stabilizer₂ c) : ℕ) : ℝ)⁻¹ * (∏ τ, ‖(o.1 τ).det‖ ^ (2 * shiftOf (sgTG M) τ)) *
          (nfAll M.sg (subP o.1 (MvPolynomial.map s (Pc c))) (subP o.1 (MvPolynomial.map s (Pc c)))).re

end Gen

def ClsPTied.toG {u : D.what₂.Word} (K : ClsPTied u) : ClassesAtPrimes (D.fm u) (badG D) where
  lev := K.lev
  y := K.y
  y_bij := K.y_bij
  lat := K.lat
  y_lat := K.y_lat
  lat_fin := K.lat_fin
  stabI := K.stabI
  stabI_inj := K.stabI_inj
  stabI_range := K.stabI_range

end Formalism.L2.Forms

end
end

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

variable {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}

def okPT (D : D7) (Q : Finset (HeightOneSpectrum (𝓞 D.host.F))) (T : ℕ) (w : D.what₂.places.Pl) : Prop :=
  okQ D Q w ∨ D.what₂.places.resChar w = T



end Formalism.L2.Forms

end
end

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Forms

variable {D : D7} {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}


set_option maxHeartbeats 4000000 in
structure SymmetricTwistedTiltedData {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
    {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)} {W : TwFormsTiedS D Tw T J F}
    (Lv : SymmetricTwistedLevelData W) (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0) (h1 : 1 ≤ D.R.m)
    (K : ClassesAtPrimes (Tw.fm u μ) (badQ D (T.Q μ))) where
  z0 : Fin (D.R.N D.R.m) → D.host.E
  lastCoordinateUniformizerVector_spans_orthogonal_line : ∃ a : D.host.E, z0 = a • zc D
  hermitianForm_lastCoordinateUniformizerVector_self : hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) z0 z0 = ((D.mem u).A.T : D.host.E)
  ga : (Tw.fm u μ).clsP → UJ (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl)
  til_lat : ∀ c, mulLat (ga c).1.1 (latCrd D D.R.m le_rfl (T.lat u μ D.R.m ((Tw.fm u μ).til c))) =
    (K.lat c).map ((iXc D).restrictScalars (𝓞 D.host.E)) ⊔ Submodule.span (𝓞 D.host.E) {z0}
  til_fv : ∀ v c (x : ↥(LdG D D.R.m le_rfl (latCrd D D.R.m le_rfl (T.lat u μ D.R.m ((Tw.fm u μ).til c))))) (r : 𝓞 D.host.E),
    (r : D.host.E) = hform (sigD D : D.host.E →+* D.host.E) (gramN D D.R.m le_rfl) z0 ((ga c).1.1 *ᵥ x.1) →
    (Tw.fm u μ).fv D.R.m v ((Tw.fm u μ).til c) ((Lv.lv u μ hμ D.R.m h1 le_rfl).pr v _ x) = (W.atT u μ).res (F u).atT v r

  stabMap : ∀ c s, IsExt D z0 (RingHom.id D.host.E) (K.stabI c s).1.1
    ((ga c).1.1 * ((W.ch u μ hμ D.R.m h1 le_rfl (T.chOf u μ D.R.m ((Tw.fm u μ).til c))).stabI ⟨(Tw.fm u μ).til c, rfl⟩
      ((Tw.fm u μ).stabMap c s)).1.1 * ((ga c)⁻¹).1.1)

  ka : ∀ c, (W.ch u μ hμ D.R.m h1 le_rfl (T.chOf u μ D.R.m ((Tw.fm u μ).til c))).lev.U
  til_ad : ∀ c (g : GL (Fin (D.R.N D.R.m)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)),
    IsExt D z0 (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (K.y c).1.1 g.1 →
    bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (ga c).1 *
      ((W.ch u μ hμ D.R.m h1 le_rfl (T.chOf u μ D.R.m ((Tw.fm u μ).til c))).y ⟨(Tw.fm u μ).til c, rfl⟩).1 = g * (ka c).1


set_option maxHeartbeats 4000000 in
structure TwPTiedS {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
    {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)} {W : TwFormsTiedS D Tw T J F} (Lv : SymmetricTwistedLevelData W) where

  cls : ∀ u μ, μ ≠ D.what₂.mu0 → ClassesAtPrimes (Tw.fm u μ) (badQ D (T.Q μ))

  Lb : ∀ u μ hμ, (cls u μ hμ).lev.Lb = (F u).clsP.lev.Lb

  chi_fin : ∀ u μ hμ, ∃ n : ℕ, 0 < n ∧ ∀ κ, (cls u μ hμ).lev.chi κ ^ n = 1

  val : ∀ u μ hμ, ValuationAtPrimes (cls u μ hμ) (okPT D (T.Q μ) (D.mem u).A.T)

  norm : ∀ u μ hμ, NormPTieG (val u μ hμ)

  til : ∀ u μ hμ (h1 : 1 ≤ D.R.m), SymmetricTwistedTiltedData Lv u μ hμ h1 (cls u μ hμ)

structure TwPAtGS {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
    {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)} {W : TwFormsTiedS D Tw T J F} {Lv : SymmetricTwistedLevelData W} (P : TwPTiedS Lv) : Prop where
  Uloc_g : ∀ u μ hμ v, v ∈ badG D → (P.cls u μ hμ).lev.Uloc v = (F u).clsP.lev.Uloc v
  chi_g : ∀ u μ hμ (κ : (P.cls u μ hμ).lev.U) (κ' : (F u).clsP.lev.U), κ.1 = κ'.1 →
    (∀ v ∈ T.Q μ, bc (prV (E := D.host.E) v) κ.1 = 1) → (P.cls u μ hμ).lev.chi κ = (F u).clsP.lev.chi κ'


set_option maxHeartbeats 4000000 in
structure TwPEvzS {Tw : TwForms D} {T : Formalism.L2.Herm.TwChTied D inQ} {H : Formalism.L2.Herm.HermColsCh D} {J : Formalism.L2.Herm.TwChJointS T H}
    {F : ∀ u, FormsTiedSym D u (H.Ch u) (H.chOf u)} {W : TwFormsTiedS D Tw T J F} {Lv : SymmetricTwistedLevelData W} (P : TwPTiedS Lv) where
  eWz : ∀ u μ, (D.PTw u μ).Wz ≃ₗ[ℂ] ((Tw.fm u μ).clsP → (D.chTw u μ).Y D.R.m → ℂ)
  evz : ∀ u μ (hμ : μ ≠ D.what₂.mu0) (h1 : 1 ≤ D.R.m) (φ : (D.chTw u μ).cls D.R.m → (D.chTw u μ).Y D.R.m → ℂ) c s s',
    IsTr (atInf (embT D) ((P.til u μ hμ h1).ga c).1.1) (twYS T F u μ D.R.m le_rfl s') (twYS T F u μ D.R.m le_rfl s) →
    eWz u μ ((D.PTw u μ).evz φ) c s =
      ((((W.ch u μ hμ D.R.m h1 le_rfl (T.chOf u μ D.R.m ((Tw.fm u μ).til c))).lev.chi ((P.til u μ hμ h1).ka c))⁻¹ : ℂˣ) : ℂ) *
        φ ((Tw.fm u μ).til c) s'
  jM : ∀ u μ, (D.PTw u μ).Mt →ₛₗ[starRingEnd ℂ] (D.PTw u μ).Wrow
  per : ∀ u μ, μ ≠ D.what₂.mu0 →
    (∀ z ∈ (Tw.fm u μ).ptC, ∃ G, jM u μ G = z) ∧ (∀ G, jM u μ G ∈ (Tw.fm u μ).ptC) ∧
      ∀ w G, (D.PTw u μ).period w G = (Tw.fm u μ).ipP (jM u μ G) w

end Formalism.L2.Forms

end
end

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG

namespace Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure SymmetricTwistedColumnsCompatible {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} (tp : Formalism.L2.Host.TupTied D cf nch)
    (cols : ColsTiedSym D) (Tw : TwForms D) where
  ch : Formalism.L2.Herm.TwistedCharacterData tp
  chJ : Formalism.L2.Herm.TwChJointS ch cols.herm.base
  chM : Formalism.L2.Herm.TwChMu0 ch
  forms : TwFormsTiedS D Tw ch chJ cols.forms
  lv : SymmetricTwistedLevelData forms

  same : TwLvSameS forms

  lvJ : SymmetricTwistedJointForms ch cols.forms

structure SymmetricTwistedColumnsAtPrimes {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} (tp : Formalism.L2.Host.TupTied D cf nch)
    (cols : ColsTiedSym D) (Tw : TwForms D) extends SymmetricTwistedColumnsCompatible tp cols Tw where

  pt : TwPTiedS lv

  ptG : TwPAtGS pt

  ptE : TwPEvzS pt

end Formalism.L2.Forms

end
end
