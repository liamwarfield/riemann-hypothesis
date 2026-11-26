module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
public import Formalism.LocalToGlobal.LatticeGeometry.LevPrPrime
public import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs

@[expose] public section

section -- merged from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Geo NumberField IsDedekindDomain

namespace Formalism.MainNotions.Gaps.FamilyHypotheses

def SupBoundPageRows (D : D7) (large₂ : SizeData₂ D) {j : ℕ} (ka : WeightFamilies.Wt D j) : Prop :=
  (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) ∧
  lrd D ≤ 2 * large₂.sc.L ∧
  Real.log D.host.d ≤ 2 * large₂.sc.L ∧
  Real.log (Ideal.absNorm D.host.ccK) ≤ 2 * large₂.sc.L ∧
  Real.log D.R.f ≤ 2 * large₂.sc.L ∧
  Real.log D.host.pde ≤ large₂.sc.L ∧
  Real.log D.host.pde' ≤ large₂.sc.L ∧
  Real.log (1 + DF ka) ≤ 2 * large₂.sc.L ∧
  Real.log ka.n ≤ large₂.sc.L

def OwnPr (D : D7) (p : ℕ) : Prop := p = Formalism.MainNotions.DIV.Cons.po D ∨ p = Formalism.MainNotions.DIV.Cons.po2 D

theorem ownPr_iff (D : D7) (p : ℕ) : OwnPr D p ↔ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ) := Iff.rfl

section Split

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def FourthHypothesisSizes (large₂ : SizeData₂ D) (C2 A2 CR : ℝ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) : Prop :=
  large₂.sc.b ≤ ka.size ∧ (T : ℝ) * wL.size ≤ 2 * ka.size ∧
  wF.size ≤ ((WeightFamilies.dimY D j : ℝ) + 2) * wL.size + 5 * D.R.f * (D.R.r : ℝ) ^ 2 * T ∧
  WeightFamilies.PPv D large₂ C2 A2 ^ 3 * (T : ℝ) ^ 2 ≤ large₂.sc.b ∧
  WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 ≤ large₂.sc.b ∧
  (∀ i, 2 * DF ka + 2 < D.host.g i)

def I4 (large₂ : SizeData₂ D) (X : PJ D B P j) (wL wF : WeightFamilies.Wt D j) (nW : ℕ) : Prop :=
  ∃ PLam lNc : ℝ, PLam ≤ 1009 * Zb D large₂ ∧ lNc ≤ 81 * Zb D large₂ ^ 2 ∧
  (j < D.R.m → ∃ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW ∧ ∃ th ∈ B.Mlat j w1, X.NonZeroComp w1 th ∧
    ∀ σ, Real.log (B.supN j w1 σ th) ≤ 2 * PI4 D j PLam lNc * WeightFamilies.dimY D j * wL.size) ∧
  ∃ w2 : WeightFamilies.Wt D j, IsG2 wL wF w2 ∧ ∃ th ∈ B.Mlat j w2, X.NonZeroComp w2 th ∧
    ∀ σ, Real.log (B.supN j w2 σ th) ≤ PI4 D j PLam lNc * WeightFamilies.dimY D j * wL.size

theorem fourthHypothesis_iff_sizes_and_index (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CR : ℝ) (ka wL wF : WeightFamilies.Wt D j) (T nW : ℕ) :
    H4 large₂ X H C2 A2 CR ka wL wF T nW ↔ FourthHypothesisSizes large₂ C2 A2 CR ka wL wF T ∧ I4 large₂ X wL wF nW :=
  ⟨fun ⟨a, b, c, d, e, f, g⟩ => ⟨⟨a, b, c, d, e, f⟩, g⟩, fun ⟨⟨a, b, c, d, e, f⟩, g⟩ => ⟨a, b, c, d, e, f, g⟩⟩

def HypPage (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ)
    (h0 : ℝ) : Prop :=
  ParA large₂ H.CA ∧ SetC large₂ X H.CK H.C1 H.A1 ka wL wF T nP nW h0 ∧ H3 large₂ H C2 A2 CR 0 wL T ∧
    FourthHypothesisSizes large₂ C2 A2 CR ka wL wF T ∧ (T : ℝ) ≤ large₂.sc.x ^ CT

theorem hypC_iff (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.HypC large₂ X H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus ↔
      HypPage large₂ X H C2 A2 CR CT ka wL wF T nP nW h0 ∧ ScalB large₂ X H.C1 H.A1 S ka wL wF T ∧
        Formalism.MainNotions.Gaps.EtaleWeightGaps.WeightedPrimeSumBoundAlt large₂ X wL nus ∧ H2 X S ka wL wF ∧ I4 large₂ X wL wF nW :=
  ⟨fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨⟨a, b, f, ((fourthHypothesis_iff_sizes_and_index ..).1 g).1, h⟩, c, d, e, ((fourthHypothesis_iff_sizes_and_index ..).1 g).2⟩,
    fun ⟨⟨a, b, f, g, h⟩, c, d, e, i⟩ => ⟨a, b, c, d, e, f, (fourthHypothesis_iff_sizes_and_index ..).2 ⟨g, i⟩, h⟩⟩

def refill {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G₀ : Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData X ka wL wF)
    (del : ℕ) (th' : Fin del → B.Cusp j wF) (rz : ℕ) (alz : Fin rz → Fin (WeightFamilies.dimY D j) → ℕ)
    (th0 : Fin rz → B.Cusp j (X.wF0 wL wF)) (zc : Fin rz → ((Fin (WeightFamilies.dimY D j + 1) × Fin G₀.N) →₀ ℕ) →₀ B.Cusp j ka)
    (rq : ℕ) (th : Fin rq → B.Mlat j ka) (iet : ℕ) (et : B.Cusp j (Formalism.MainNotions.Gaps.EtaleWeightGaps.etWt D j iet)) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData X ka wL wF :=
  ⟨G₀.N, G₀.w, del, th', rz, alz, th0, zc, rq, th, iet, et, G₀.mx⟩

end Split

section Views

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type}

variable (F : ShimFam D G Lev) (I : Type) (dat : I → Dat D Lev) (hI : ∀ i, (dat i).Indef) (iW : ℕ → I)
  (hiW : ∀ j, 1 ≤ j → j < D.R.m → dat (iW j) = datW D F.κg j)

end Views

end Formalism.MainNotions.Gaps.FamilyHypotheses
end
end

section -- merged from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.CombBound4Of
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def ShareRhoT (T rz rq d : ℕ) : Prop := (rz : ℝ) ≤ rq + 22 * (WeightFamilies.dimY D j : ℝ) ^ 2 * d / T

def flipOneThree (D : D7) (nW : ℕ) : ℝ :=
  max (16200 * Real.pi * (nW : ℝ) * (D.R.m : ℝ) ^ 4 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4)
    (max ((2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 * (nW : ℝ) + 2 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 3)
      ((D.R.r : ℝ) * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 3))

def PageSupp (D : D7) (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) {j : ℕ} (C2 A2 : ℝ) (nW : ℕ) (S : Scal B) (wL : WeightFamilies.Wt D j) :
    Prop :=
  flipOneThree D nW ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  (∀ σ : B.KO →+* ℂ, (DF wL : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤ Real.log ‖σ (S.sW : B.KO)‖) ∧
  (D.R.f : ℝ) ^ 2 ≤ D.host.rdE ∧ 8 ≤ D.R.r ∧ 3 ≤ DF wL

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

def CombBound4 (G : GlobalFamilyData X ka wL wF) (Qf : ∀ la, LocalPointData G la) (S : Scal B) (c : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) :
    Prop :=
  ∀ la (ζ : PtsG G la),
    0 ≤ X.vAt la ((Qf la).y ζ) (X.inc _ G.et) ∧ (X.vAt la ((Qf la).y ζ) (X.inc _ G.et) ≠ ⊤ →
      X.depth S.sW wL la ((Qf la).y ζ) ≤
        (((nus la : ℝ) + c / (2 * (G.iet : ℝ)) * (X.vAt la ((Qf la).y ζ) (X.inc _ G.et)).toReal : ℝ) : EReal))

theorem combBound4_of {G : GlobalFamilyData X ka wL wF} {S : Scal B} {c : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (hj : j < D.R.m) (h : CombBound G S c nus) (Qf : ∀ la, LocalPointData G la) : CombBound4 G Qf S c nus :=
  fun la ζ => (h la ((Qf la).y ζ)).1 hj

def DepthAtM (X : PJ D B P j) (S : Scal B) (wL : WeightFamilies.Wt D j) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  ∀ la (y : X.Pt la), X.depth S.sW wL la y ≤ ((nus la : ℝ) : EReal)

theorem depthAtM_of {G : GlobalFamilyData X ka wL wF} {S : Scal B} {c : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (hj : D.R.m ≤ j) (h : CombBound G S c nus) : DepthAtM X S wL nus :=
  fun la y => (h la y).2 hj

def ConclAtM (large₂ : SizeData₂ D) (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  D.R.m ≤ j → DepthAtM X S wL nus →
    Concl X S ka wL wF T nus (X.rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2)

def PageGd4 (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (large₂ : SizeData₂ D) (CG AG Pd : ℝ) : Prop :=
  WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size) ≤ Pd

theorem pageGd4_iff {X : PJ D B P j} {ka : WeightFamilies.Wt D j} {large₂ : SizeData₂ D} {CG AG Pd : ℝ} :
    PageGd4 X ka large₂ CG AG Pd ↔ PageGd X ka large₂ CG AG Pd := Iff.rfl

def PolyDom4 (D : D7) {j : ℕ} (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (C2 A2 CR Ch Ah Cq Aq : ℝ)
    (Gc PH Prw Pet Pd : ℝ) (ka : WeightFamilies.Wt D j) : Prop :=
  2 ≤ K.CRm ∧ 0 ≤ CR ∧ 0 ≤ Gc ∧ 0 ≤ Prw ∧ 0 ≤ WeightFamilies.PP0v D large₂ K.CL K.AL ∧ WeightFamilies.Obound B large₂ Ch Ah ∧
  WeightFamilies.RRv D H.CRc * WeightFamilies.PPv D large₂ H.Cc H.Ac ≤ WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 ∧
  WeightFamilies.RRv D K.CRm * D.host.rdE ^ 2 ≤ WeightFamilies.RRv D CR ^ 2 ∧
  2 ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 ∧ 4 * H.CK ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * D.R.f ∧
  (2 * Gc + 6 * PH + Prw) * 25 ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  Pet ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂) ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  60 * Gc + 180 * PH + 44 * (2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂)) +
      22 * (2 * WeightFamilies.PPv D large₂ Cq Aq) ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * (WeightFamilies.dimY D j : ℝ) ∧
  1 / 2 ≤ Prw ∧ Prw ≤ PH ∧ 0 ≤ Pet ∧
  Prw ≤ WeightFamilies.PPv D large₂ C2 A2

theorem polyDom4_iff {B : WeightFamilies.Prov D} {large₂ : SizeData₂ D} {K : KAdm} {H : KHyp} {C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd : ℝ}
    {ka : WeightFamilies.Wt D j} :
    PolyDom4 D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka ↔ PolyDom D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka :=
  Iff.rfl

def Conclusion1OfComb4 : Prop :=
  ∀ (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ),
    ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
      (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    HypC large₂ (X j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus →
    LatAt B j ka → SupBoundByL2AtWeight large₂ B j ka K.CG K.AG → LAMwAt large₂ B j ka K.CL K.AL →
    (j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL)) →
    TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → PageSupp D large₂ B C2 A2 nW S wL →
    ∀ (G : GlobalFamilyData (X j h1 h2) ka wL wF) (Gc PH Prw Pet Pd : ℝ),
    G.TiedW S Gc Prw → G.TiedTh S Gc → G.TiedZ S T Gc →
    G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah → G.TiedEt large₂ K.Cf K.Af →
    DeepHerm (X j h1 h2) ka → DeepSubMul (X j h1 h2) → DeepLogD (X j h1 h2) ka Pd →
    PageGd4 (X j h1 h2) ka large₂ K.CG K.AG Pd →
    ShareRd (D := D) (j := j) T G.del ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRhoT (D := D) (j := j) T G.rz G.rq ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRhoP (D := D) (j := j) T G.rq ((X j h1 h2).rk ka (B.Mlat j ka)) →
    PolyDom4 (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka →
    (∀ la, InContainZ G la S T) → (∀ la, InContainM G la K.CRm T (cc D large₂ C2 A2 CR wL)) →
    (j < D.R.m → ∃ Qf : ∀ la, LocalPointData G la,
      (∀ la, InBasis G la) ∧ (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧ (∀ la, (Qf la).InLiftC S Gc Prw T) ∧
      CombBound4 G Qf S (cc D large₂ C2 A2 CR wL) nus ∧ Heights Qf Gc PH Prw Pet) →
    (D.R.m ≤ j → DepthAtM (X j h1 h2) S wL nus) →
    ConclAtM large₂ (X j h1 h2) S ka wL wF T nus →
    Concl (X j h1 h2) S ka wL wF T nus
      ((X j h1 h2).rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2)

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

section -- merged from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.VEtNonnegOfTied
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}

def vEt (Q : LocalPointData G la) (ζ : PtsG G la) : ℝ :=
  if j < D.R.m then (X.vAt la (Q.y ζ) (X.inc _ G.et)).toReal / (2 * (G.iet : ℝ)) else 0

theorem ep_nu_int {S : Scal B} (Q : LocalPointData G la) (hTie : Q.InTie S) (ζ : PtsG G la) :
    ∃ n : ℤ, (ep (unifO X la G.N) ζ : ℝ) * Q.nu S ζ = n := (hTie ζ).2.2.2.1

theorem levels_eq [Fintype (PtsG G la)] (Q : LocalPointData G la) (T : ℕ) (c : ℝ) :
    (T : ℝ) * max 0 c * ∑ ζ, ((ep (unifO X la G.N) ζ : ℝ) * (fdeg ζ : ℝ)) * vEt Q ζ =
      if j < D.R.m then (T : ℝ) * (max 0 c / (2 * (G.iet : ℝ))) * Q.Net else 0 := by
  split_ifs with hj
  · unfold LocalPointData.Net vEt
    rw [finsum_eq_sum_of_fintype]
    simp only [if_pos hj]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    ring
  · unfold vEt
    simp only [if_neg hj, mul_zero, Finset.sum_const_zero]

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

section -- merged from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.IsLatticeOfAdmissible
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.T0

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem qlen_of_idx (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) (la : HeightOneSpectrum (𝓞 B.KO))
    (hLat : InLat X ka la S wL wF T) (hΘM : X.Theta S ka wL wF T ≤ X.Msup ka) (e r : ℝ)
    (h : ∀ U : Submodule (X.Kl la) ↥(WL X ka la),
      (Formalism.LatticeIndexTer.idx (X.Ol la) ↥(WL X ka la) (MW X ka la ⊓ U.restrictScalars (X.Ol la))
        (ThW X S ka wL wF T la ⊓ U.restrictScalars (X.Ol la)) : ℝ) ≤ e * (finrank (X.Kl la) U : ℝ) + r)
    (V' : Submodule (X.Kl la) (X.Vl la)) (hV' : V' ≤ X.locK la (X.Msup ka)) :
    X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V') (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V') ≠ ⊤ ∧
      ((X.qlen la (X.loc la (X.Msup ka) ⊓ X.ofK la V')
        (X.loc la (X.Theta S ka wL wF T) ⊓ X.ofK la V')).toNat : ℝ) ≤ e * (finrank (X.Kl la) V' : ℝ) + r := by
  have hb := h (V'.comap (WL X ka la).subtype)
  have hrk : finrank (X.Kl la) ↥(V'.comap (WL X ka la).subtype) = finrank (X.Kl la) V' :=
    (Submodule.comapSubtypeEquivOfLe hV').finrank_eq
  have hq := qlen_eq_inW X ka la (X.loc la (X.Msup ka)) (X.loc la (X.Theta S ka wL wF T)) V' hV'
  have hle : ThW X S ka wL wF T la ≤ MW X ka la :=
    Submodule.comap_mono (Submodule.span_mono (Set.image_mono hΘM))
  have h0 := qlen_eq_zero_of_le
    (MW X ka la ⊓ (V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la))
    (ThW X S ka wL wF T la ⊓ (V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la))
    (inf_le_inf_right _ hle)
  have hfin := qlen_inf_ne_top (X.Ol la) (X.Kl la) ↥(WL X ka la) (MW X ka la) (ThW X S ka wL wF T la)
    hLat.1 hLat.2 ((V'.comap (WL X ka la).subtype).restrictScalars (X.Ol la))
  rw [← hq]
  refine ⟨hfin, ?_⟩
  rw [hrk] at hb
  unfold Formalism.LatticeIndexTer.idx at hb
  rw [h0] at hb
  have hb' := hb
  simp only [ENat.toNat_zero, Nat.cast_zero, sub_zero, Int.cast_natCast] at hb'
  exact hb'

theorem span_eq_top_of_shortG {X : PJ D B P j} {w : WeightFamilies.Wt D j} {N : Submodule (𝓞 B.KO) (B.Cusp j w)} {β : ℝ}
    (h : ShortG X w N β) : Submodule.span B.KO (N : Set (B.Cusp j w)) = ⊤ := by
  obtain ⟨Sh, h1, h2, -⟩ := h
  exact top_le_iff.1 (h2 ▸ Submodule.span_mono h1)

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

section -- merged from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsGlobalFamilyQuotientBounded
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

section LinAlgQ

theorem exists_den {R K V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (M : Submodule R V)
    (hM : Submodule.span K (M : Set V) = ⊤) (v : V) : ∃ s ∈ nonZeroDivisors R, s • v ∈ M := by
  have hv : v ∈ Submodule.span K (M : Set V) := by rw [hM]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_mem _, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_mem _, by rw [smul_zero]; exact M.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, mul_mem hs ht, ?_⟩
    have h1 : (s * t) • x = t • (s • x) := by rw [mul_comm, mul_smul]
    rw [smul_add, h1, mul_smul]
    exact M.add_mem (M.smul_mem _ hsx) (M.smul_mem _ hty)
  | smul a x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective R a
    refine ⟨d * s, mul_mem hd hs, ?_⟩
    have hd0 : algebraMap R K d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero hd)
    have h1 : (d * s) • ((algebraMap R K n / algebraMap R K d) • x) = n • (s • x) := by
      rw [← algebraMap_smul K (d * s), ← algebraMap_smul K n, ← algebraMap_smul K s, smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [h1]
    exact M.smul_mem _ hsx

theorem finrank_quot_eq {R K V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (M : Submodule R V)
    (hM : Submodule.span K (M : Set V) = ⊤) (W : Submodule K V) :
    finrank R (M ⧸ (W.restrictScalars R).comap M.subtype) = finrank K (V ⧸ W) := by
  let g : M →ₗ[R] (V ⧸ W) := (W.mkQ.restrictScalars R).comp M.subtype
  have hker : LinearMap.ker g = (W.restrictScalars R).comap M.subtype := by
    ext x
    simp [g]
  let f : (M ⧸ (W.restrictScalars R).comap M.subtype) →ₗ[R] (V ⧸ W) :=
    Submodule.liftQ _ g (le_of_eq hker.symm)
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (le_of_eq hker)
  have hloc : IsLocalizedModule (nonZeroDivisors R) f := by
    refine ⟨fun s => ?_, fun y => ?_, fun {x₁ x₂} h => ⟨1, by rw [hinj h]⟩⟩
    · have hs0 : algebraMap R K s ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero s.2)
      rw [Module.End.isUnit_iff]
      constructor
      · intro a b hab
        simp only [Module.algebraMap_end_apply] at hab
        rw [← algebraMap_smul K (s : R) a, ← algebraMap_smul K (s : R) b] at hab
        exact smul_right_injective _ hs0 hab
      · intro a
        refine ⟨(algebraMap R K s)⁻¹ • a, ?_⟩
        simp only [Module.algebraMap_end_apply]
        rw [← algebraMap_smul K (s : R), smul_smul, mul_inv_cancel₀ hs0, one_smul]
    · obtain ⟨v, rfl⟩ := W.mkQ_surjective y
      obtain ⟨s, hs, hsv⟩ := exists_den (K := K) M hM v
      refine ⟨(Submodule.Quotient.mk ⟨s • v, hsv⟩, ⟨s, hs⟩), ?_⟩
      rfl
  rw [IsLocalization.finrank_eq K (nonZeroDivisors R) le_rfl, IsLocalizedModule.finrank_eq (nonZeroDivisors R) f le_rfl]

theorem exists_sub_basis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Sh : Finset V) (hS : Submodule.span K (Sh : Set V) = ⊤) (W : Submodule K V) :
    ∃ e : Fin (finrank K (V ⧸ W)) → V, (∀ i, e i ∈ Sh) ∧ Submodule.span K (Set.range e) ⊔ W = ⊤ := by
  classical
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent K (W.mkQ '' (Sh : Set V))
  have htop : Submodule.span K b = ⊤ := by
    rw [hspan, Submodule.span_image, hS, Submodule.map_top, Submodule.range_mkQ]
  have hfin : Finite b := ((Sh.finite_toSet.image _).subset hb).to_subtype
  have := Fintype.ofFinite b
  let bs : Basis b K (V ⧸ W) := Basis.mk hli (by rw [Subtype.range_coe, htop])
  have hcard : Fintype.card b = finrank K (V ⧸ W) := (finrank_eq_card_basis bs).symm
  let eq : Fin (finrank K (V ⧸ W)) ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hpre : ∀ k, ∃ v ∈ (Sh : Set V), W.mkQ v = (eq k : V ⧸ W) := fun k => hb (eq k).2
  choose e he1 he2 using hpre
  refine ⟨e, fun i => he1 i, ?_⟩
  rw [sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
  have : (⇑W.mkQ ∘ e) = (Subtype.val : b → V ⧸ W) ∘ eq := by funext k; exact he2 k
  rw [this, Set.range_comp, eq.surjective.range_eq, Set.image_univ, Subtype.range_coe, htop]

end LinAlgQ

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem rhoP_eq_finrank (B : WeightFamilies.Prov D) (CR T c : ℝ) (j : ℕ) (ka : WeightFamilies.Wt D j)
    (hM : Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka)) = ⊤) :
    WeightFamilies.rhoP B CR T c j ka = finrank B.KO (B.Cusp j ka ⧸ WeightFamilies.MggK B CR T c j ka) :=
  finrank_quot_eq (B.Mlat j ka) hM (WeightFamilies.MggK B CR T c j ka)

theorem exists_global_family_quotient_bounded {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G0 : GlobalFamilyData X ka wL wF) (large₂ : SizeData₂ D) (S : Scal B)
    (CRm : ℝ) (T : ℕ) (c be Ch Ah : ℝ)
    (hS4 : ShortG X ka (X.Thc S.sK ka) be)
    (hM : X.Thc S.sK ka ≤ B.Mlat j ka)
    (hbe : be ≤ WeightFamilies.PPv D large₂ Ch Ah * ka.size) :
    ∃ th : Fin (WeightFamilies.rhoP B CRm T c j ka) → B.Mlat j ka,
      ({ G0 with rq := WeightFamilies.rhoP B CRm T c j ka, th := th } : GlobalFamilyData X ka wL wF).TiedQ large₂ S CRm T c Ch Ah := by
  obtain ⟨Sh, hSh, hspan, hshort⟩ := hS4
  have hMtop : Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka)) = ⊤ :=
    top_le_iff.mp (hspan ▸ Submodule.span_mono fun x hx => hM (hSh hx))
  have hex := exists_sub_basis Sh hspan (WeightFamilies.MggK B CRm T c j ka)
  rw [← rhoP_eq_finrank B CRm T c j ka hMtop] at hex
  obtain ⟨e, he, hsup⟩ := hex
  exact ⟨fun i => ⟨e i, hM (hSh (he i))⟩, rfl, fun i => hSh (he i), hsup, fun i => (hshort _ (he i)).trans hbe⟩

section Unchanged

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G0 : GlobalFamilyData X ka wL wF) (rq : ℕ) (th : Fin rq → B.Mlat j ka)

variable {G0} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G0 la)

end Unchanged

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

section -- merged from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.NormEuclideanEmbeddingEqNetNorm
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module ComplexConjugate

namespace Formalism.MainNotions.Gaps.NetNorms

variable {D : D7} {B : WeightFamilies.Prov D} {j : ℕ} {ka : WeightFamilies.Wt D j}

structure NetData (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) where
  NN : (B.KO →+* ℂ) → Type
  [fin : ∀ σ, Fintype (NN σ)]
  ev : ∀ σ, NN σ → (B.Cusp j ka →ₛₗ[σ] ℂ)
  cj : ∀ σ, NN σ ≃ NN (ComplexEmbedding.conjugate σ)
  ev_conj : ∀ σ (y : NN σ) (F : B.Cusp j ka),
    ev (ComplexEmbedding.conjugate σ) (cj σ y) F = conj (ev σ y F)

attribute [instance] NetData.fin

namespace NetData

variable (Nt : NetData B j ka)

def netN (σ : B.KO →+* ℂ) (F : B.Cusp j ka) : ℝ :=
  Real.sqrt ((Fintype.card (Nt.NN σ) : ℝ)⁻¹ * ∑ y, ‖Nt.ev σ y F‖ ^ 2)

def cf (σ : B.KO →+* ℂ) : ℝ := (Real.sqrt (Fintype.card (Nt.NN σ) : ℝ))⁻¹


open Classical in
def e0 (σ : B.KO →+* ℂ) : B.Cusp j ka →ₛₗ[σ] EuclideanSpace ℂ (Σ τ : B.KO →+* ℂ, Nt.NN τ) where
  toFun F := WithLp.toLp 2 (fun p => if p.1 = σ then ((Nt.cf p.1 : ℝ) : ℂ) * Nt.ev p.1 p.2 F else 0)
  map_add' F G := by
    ext p
    simp only [map_add (f := _), PiLp.add_apply]
    split_ifs <;> ring
  map_smul' a F := by
    ext ⟨τ, y⟩
    by_cases h : τ = σ
    · subst h
      simp [map_smulₛₗ]
      ring
    · simp [h]

end NetData

def NetMax (Nt : NetData B j ka) : Prop :=
  ∀ (σ : B.KO →+* ℂ) (F : B.Cusp j ka), ∃ y : Nt.NN σ, B.supN j ka σ F / 4 ≤ ‖Nt.ev σ y F‖

def NetLeSup (Nt : NetData B j ka) : Prop :=
  ∀ (σ : B.KO →+* ℂ) (y : Nt.NN σ) (F : B.Cusp j ka), ‖Nt.ev σ y F‖ ≤ B.supN j ka σ F

def NetInj (Nt : NetData B j ka) (σ : B.KO →+* ℂ) : Prop :=
  ∀ (n : ℕ) (F : Fin n → B.Cusp j ka), LinearIndependent B.KO F →
    LinearIndependent ℂ (fun i => fun y : Nt.NN σ => Nt.ev σ y (F i))

def NetPageG (Nt : NetData B j ka) (large₂ : SizeData₂ D) (CG AG : ℝ) : Prop :=
  ∀ σ : B.KO →+* ℂ, Real.log (16 * (Fintype.card (Nt.NN σ) : ℝ)) ≤ WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size)

def NetSize (Nt : NetData B j ka) (CZ : ℝ) : Prop :=
  ∀ σ : B.KO →+* ℂ, Real.log (16 * (Fintype.card (Nt.NN σ) : ℝ)) ≤ CZ

namespace NetData

variable (Nt : NetData B j ka)

theorem goodRowsProjector_apply_eq_sum (σ : B.KO →+* ℂ) (F : B.Cusp j ka) (p : Σ τ : B.KO →+* ℂ, Nt.NN τ) [Decidable (p.1 = σ)] :
    Nt.e0 σ F p = if p.1 = σ then ((Nt.cf p.1 : ℝ) : ℂ) * Nt.ev p.1 p.2 F else 0 := by
  by_cases h : p.1 = σ <;> simp [e0, h]

theorem cf_sq (σ : B.KO →+* ℂ) : Nt.cf σ * Nt.cf σ = (Fintype.card (Nt.NN σ) : ℝ)⁻¹ := by
  unfold cf
  rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg _)]

theorem norm_euclideanEmbedding_eq_netNorm (σ : B.KO →+* ℂ) (F : B.Cusp j ka) : ‖Nt.e0 σ F‖ = Nt.netN σ F := by
  classical
  rw [EuclideanSpace.norm_eq, netN]
  congr 1
  rw [Fintype.sum_sigma, Finset.sum_eq_single σ]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Nt.goodRowsProjector_apply_eq_sum, if_pos rfl, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, ← Nt.cf_sq]
    ring
  · intro τ _ hτ
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [Nt.goodRowsProjector_apply_eq_sum, if_neg hτ, norm_zero]
    ring
  · intro h
    exact absurd (Finset.mem_univ σ) h

theorem netN_nonneg (σ : B.KO →+* ℂ) (F : B.Cusp j ka) : 0 ≤ Nt.netN σ F := Real.sqrt_nonneg _

theorem netN_smul (σ : B.KO →+* ℂ) (a : B.KO) (F : B.Cusp j ka) : Nt.netN σ (a • F) = ‖σ a‖ * Nt.netN σ F := by
  rw [← Nt.norm_euclideanEmbedding_eq_netNorm, ← Nt.norm_euclideanEmbedding_eq_netNorm, map_smulₛₗ, norm_smul]

theorem netN_add (σ : B.KO →+* ℂ) (F G : B.Cusp j ka) : Nt.netN σ (F + G) ≤ Nt.netN σ F + Nt.netN σ G := by
  rw [← Nt.norm_euclideanEmbedding_eq_netNorm, ← Nt.norm_euclideanEmbedding_eq_netNorm, ← Nt.norm_euclideanEmbedding_eq_netNorm, map_add (f := _)]
  exact norm_add_le _ _

theorem netN_eq_zero (hM : NetMax Nt) (σ : B.KO →+* ℂ) (F : B.Cusp j ka) : Nt.netN σ F = 0 ↔ F = 0 := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := hM σ F
    have hpos : (0 : ℝ) < Fintype.card (Nt.NN σ) := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨y⟩)
    have h2 : (Fintype.card (Nt.NN σ) : ℝ)⁻¹ * ∑ y, ‖Nt.ev σ y F‖ ^ 2 ≤ 0 := Real.sqrt_eq_zero'.mp h
    have h3 : ∑ y, ‖Nt.ev σ y F‖ ^ 2 ≤ 0 := by
      by_contra hc
      push_neg at hc
      have := mul_pos (inv_pos.mpr hpos) hc
      linarith
    have h4 : ‖Nt.ev σ y F‖ ^ 2 ≤ ∑ y, ‖Nt.ev σ y F‖ ^ 2 :=
      Finset.single_le_sum (f := fun y => ‖Nt.ev σ y F‖ ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ y)
    have ht : ‖Nt.ev σ y F‖ = 0 := by
      have h5 : ‖Nt.ev σ y F‖ ^ 2 ≤ 0 := h4.trans h3
      have := norm_nonneg (Nt.ev σ y F)
      nlinarith
    have hs : B.supN j ka σ F ≤ 0 := by
      rw [ht] at hy
      linarith
    have hl : B.l2NormAlt j ka σ F = 0 :=
      le_antisymm ((B.l2Norm_le_supNorm_alt j ka σ F).trans hs) (B.l2Norm_nonneg_bis j ka σ F)
    exact (B.l2Norm_eq_zero_iff j ka σ F).mp hl
  · rintro rfl
    rw [← Nt.norm_euclideanEmbedding_eq_netNorm, map_zero, norm_zero]

theorem netN_le (hL : NetLeSup Nt) (σ : B.KO →+* ℂ) (F : B.Cusp j ka) : Nt.netN σ F ≤ B.supN j ka σ F := by
  have hs : 0 ≤ B.supN j ka σ F := B.supN_nonneg j ka σ F
  unfold netN
  calc Real.sqrt ((Fintype.card (Nt.NN σ) : ℝ)⁻¹ * ∑ y, ‖Nt.ev σ y F‖ ^ 2)
      ≤ Real.sqrt (B.supN j ka σ F ^ 2) := by
        apply Real.sqrt_le_sqrt
        have h1 : ∑ y, ‖Nt.ev σ y F‖ ^ 2 ≤ ∑ _y : Nt.NN σ, B.supN j ka σ F ^ 2 :=
          Finset.sum_le_sum fun y _ => by
            gcongr
            exact hL σ y F
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
        rcases eq_or_ne (Fintype.card (Nt.NN σ) : ℝ) 0 with h0 | h0
        · rw [h0, inv_zero, zero_mul]
          positivity
        · calc (Fintype.card (Nt.NN σ) : ℝ)⁻¹ * ∑ y, ‖Nt.ev σ y F‖ ^ 2
              ≤ (Fintype.card (Nt.NN σ) : ℝ)⁻¹ * ((Fintype.card (Nt.NN σ) : ℝ) * B.supN j ka σ F ^ 2) :=
                mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr (Nat.cast_nonneg _))
            _ = B.supN j ka σ F ^ 2 := by rw [← mul_assoc, inv_mul_cancel₀ h0, one_mul]
    _ = B.supN j ka σ F := Real.sqrt_sq hs

end NetData

def covRun (j : ℕ) (ka : WeightFamilies.Wt D j) : ∀ j', WeightFamilies.Wt D j' → Prop :=
  fun j' ka' => (⟨j', ka'⟩ : Σ i, WeightFamilies.Wt D i) = ⟨j, ka⟩

namespace NetData

variable (Nt : NetData B j ka)


open Classical in
def runN : ∀ j' (ka' : WeightFamilies.Wt D j'), (B.KO →+* ℂ) → B.Cusp j' ka' → ℝ :=
  fun j' ka' => if h : (⟨j', ka'⟩ : Σ i, WeightFamilies.Wt D i) = ⟨j, ka⟩ then
      cast (congrArg (fun p : (Σ i, WeightFamilies.Wt D i) => (B.KO →+* ℂ) → B.Cusp p.1 p.2 → ℝ) h.symm) Nt.netN
    else B.supN j' ka'

theorem runN_run : Nt.runN j ka = Nt.netN := by
  simp [runN]

theorem netNorm_nonneg_alt : ∀ j' (ka' : WeightFamilies.Wt D j'), covRun j ka j' ka' → ∀ σ F, 0 ≤ Nt.runN j' ka' σ F := by
  rintro j' ka' ⟨⟩ σ F
  rw [runN_run]
  exact Nt.netN_nonneg σ F

theorem netNorm_eq_zero_iff (hM : NetMax Nt) :
    ∀ j' (ka' : WeightFamilies.Wt D j'), covRun j ka j' ka' → ∀ σ F, Nt.runN j' ka' σ F = 0 ↔ F = 0 := by
  rintro j' ka' ⟨⟩ σ F
  rw [runN_run]
  exact Nt.netN_eq_zero hM σ F

theorem netNorm_smul_alt : ∀ j' (ka' : WeightFamilies.Wt D j'), covRun j ka j' ka' →
    ∀ σ (a : B.KO) F, Nt.runN j' ka' σ (a • F) = ‖σ a‖ * Nt.runN j' ka' σ F := by
  rintro j' ka' ⟨⟩ σ a F
  rw [runN_run]
  exact Nt.netN_smul σ a F

theorem netNorm_add_le_alt : ∀ j' (ka' : WeightFamilies.Wt D j'), covRun j ka j' ka' →
    ∀ σ F G, Nt.runN j' ka' σ (F + G) ≤ Nt.runN j' ka' σ F + Nt.runN j' ka' σ G := by
  rintro j' ka' ⟨⟩ σ F G
  rw [runN_run]
  exact Nt.netN_add σ F G

theorem netNorm_le_supNorm (hL : NetLeSup Nt) :
    ∀ j' (ka' : WeightFamilies.Wt D j'), covRun j ka j' ka' → ∀ σ F, Nt.runN j' ka' σ F ≤ B.supN j' ka' σ F := by
  rintro j' ka' ⟨⟩ σ F
  rw [runN_run]
  exact Nt.netN_le hL σ F

abbrev Bp (hM : NetMax Nt) (hL : NetLeSup Nt) : WeightFamilies.Prov D :=
  Formalism.L2.Pj.withNormOnWeights (cov := covRun j ka) (Nn := Nt.runN) Nt.netNorm_nonneg_alt (Nt.netNorm_eq_zero_iff hM) Nt.netNorm_smul_alt Nt.netNorm_add_le_alt (Nt.netNorm_le_supNorm hL)

theorem Bp_L2N_run (hM : NetMax Nt) (hL : NetLeSup Nt) : (Nt.Bp hM hL).l2NormAlt j ka = Nt.netN := by
  funext σ F
  simp [Bp, Formalism.L2.Pj.withNormOnWeights, Formalism.L2.Pj.l2nOn, covRun, Nt.runN_run]

end NetData

def SupL2BoundFromNet : Prop :=
  ∀ (Nt : NetData B j ka) (hM : NetMax Nt) (hL : NetLeSup Nt) (large₂ : SizeData₂ D) (CG AG : ℝ),
    NetPageG Nt large₂ CG AG → EtaleWeightGaps.SupBoundByL2AtWeight large₂ (Nt.Bp hM hL) j ka CG AG

def DeepHermNetSt : Prop :=
  ∀ (P : ModuliIntegralCharts.Prov D) (Nt : NetData B j ka) (hM : NetMax Nt) (hL : NetLeSup Nt) (X : PJ D (Nt.Bp hM hL) P j),
    EtaleWeightGaps.DeepHerm X ka

def DeepLogDNetSt : Prop :=
  ∀ (P : ModuliIntegralCharts.Prov D) (Nt : NetData B j ka) (hM : NetMax Nt) (hL : NetLeSup Nt) (X : PJ D (Nt.Bp hM hL) P j)
    (σ : B.KO →+* ℂ) (Pd : ℝ), NetInj Nt σ → Real.log (Fintype.card (Nt.NN σ) : ℝ) ≤ Pd → EtaleWeightGaps.DeepLogD X ka Pd

end Formalism.MainNotions.Gaps.NetNorms
end
end
