module

public import Formalism.SharpRestriction.ParConsts
public import Formalism.LocalToGlobal.CharacterGerms.RowTieValK
public import Formalism.SharpRestriction.GrowthBounds.MixedCoefficientClosed

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.SelectionLemmas
noncomputable section

open scoped BigOperators

namespace Formalism.MainNotions.SelectionLemmas

open Formalism.MainNotions.G

variable {p : ℕ} {O : Type} [CommRing O]

def esymmOn {ι : Type} (VV : Finset ι) (κ : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ B ∈ VV.powersetCard k, ∏ v ∈ B, κ v

def monoN (G : GAtP p) (VV B : Finset (Fin G.P.nV)) (m : ℕ) (Sv : Fin G.P.nV → ℕ) (x : G.Fn) : G.Fn :=
  ((p : G.O) ^ (∑ v ∈ VV \ B, Sv v)) •
    ((B.sort (· ≤ ·)).foldr (fun v f => (G.yv v)^[m] ∘ f) id) x

def prodIdeal (G : GAtP p) (VV : Finset (Fin G.P.nV)) (m : ℕ) (Sv : Fin G.P.nV → ℕ)
    (M : Submodule G.O G.Fn) : Submodule G.O G.Fn :=
  Submodule.span G.O (⋃ B ∈ VV.powerset, monoN G VV B m Sv '' (M : Set G.Fn))

def tau {ι : Type} (VV : Finset ι) (m D : ℕ) (t : ι → ℕ) : ℕ := ∑ v ∈ VV, m * (t v + D + 1)

def IsSaturatedIn {X : Type} [AddCommGroup X] [Module O X] (M' M : Submodule O X) : Prop :=
  M' ≤ M ∧ ∀ (a : O) (x : X), x ∈ M → a ≠ 0 → a • x ∈ M' → x ∈ M'

def adm1 (_D : Formalism.BasicNotions.D7) (G : GAtP p) : Prop := G.TrivStab

def adm2 (_D : Formalism.BasicNotions.D7) (G : GAtP p) : Prop := G.FinClasses

def adm3 (_D : Formalism.BasicNotions.D7) (G : GAtP p) : Prop :=
  ∀ (u v : Fin G.P.nV) (F : G.Fn), G.yv u (G.yv v F) = G.yv v (G.yv u F)

def admitted (D : Formalism.BasicNotions.D7) (G : GAtP p) : Prop := adm1 D G ∧ adm2 D G ∧ adm3 D G

def Conclusion1 (_D : Formalism.BasicNotions.D7) (G : GAtP p) : Prop :=
  ∀ (VV : Finset (Fin G.P.nV)) (t Sv : Fin G.P.nV → ℕ) (Dd cStar S m : ℕ) (κ : Fin G.P.nV → ℝ),
    1 ≤ m → (∀ v ∈ VV, Sv v ≤ S) →
    (∀ v ∈ VV, LPprime (W := G.P.W v) (Qq := G.P.Qq v) (O := G.O) (Kf := G.Kf) p (G.P.n' v) (G.P.ι v) (G.P.σ v) G.P.w G.P.r
      (G.P.lam0 v) (t v) Dd (κ v) cStar) →
    let M := G.Mna
    let d : ℕ := G.dna
    let N := prodIdeal G VV m Sv M
    let τ : ℕ := tau VV m Dd t
    ((∀ β : ℕ, Formalism.G0.AllButLE (p : G.O) M N
        ⌊(d : ℝ) * (m : ℝ) ^ (β + 1) * esymmOn VV κ (β + 1)⌋₊ (τ + β * S)) ∧
      Formalism.G0.AllButLE (p : G.O) M N 0 (∑ v ∈ VV, Sv v)) ∧
    ((m : ℝ) * ∑ v ∈ VV, κ v ≤ 1 / 2 →
      let Sig : ℝ := (m : ℝ) * ∑ v ∈ VV, κ v
      let Nst := N ⊓ (Ideal.span {(p : G.O) ^ τ}) • M
      (∀ β : ℕ, (d : ℝ) * (m : ℝ) ^ (β + 1) * esymmOn VV κ (β + 1) ≤
          (d : ℝ) * Sig ^ (β + 1) / ((β + 1).factorial : ℝ)) ∧
      (∃ ℓ : ℕ, Module.length G.O (↥M ⧸ Submodule.comap M.subtype Nst) = ℓ ∧
        (ℓ : ℝ) ≤ ((Module.length G.O (G.O ⧸ Ideal.span {(p : G.O)})).toNat : ℝ) *
          ((d : ℝ) * τ + 2 * S * Sig * d)) ∧
      ∀ (M' : Submodule G.O G.Fn) (hM' : IsSaturatedIn M' M),
        Nst ⊓ M' ≤ (Ideal.span {(p : G.O) ^ τ}) • M' ∧
        Function.Injective (Submodule.mapQ (Submodule.comap M'.subtype Nst) (Submodule.comap M.subtype Nst)
          (Submodule.inclusion hM'.1) (fun _ hx => hx)) ∧
        ∀ (Y : Type) [AddCommGroup Y] [Module G.O Y] (K : G.Fn →ₗ[G.O] Y) (Z : Submodule G.O Y),
          N.map K ≤ Z → (Nst ⊓ M').map K ≤ Z)

end Formalism.MainNotions.SelectionLemmas
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.ProofRowTieValsDef
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

structure IsEndo (Y : FBChart C V O dd) (φ : Pt C 1 dd) : Prop where
  int : ∀ i, IntS V (φ i)
  cc : ∀ i, MvPowerSeries.constantCoeff (φ i) = 0
  add : comp1 φ (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)) =
    addOf Y.B.G.F (comp1 φ (pt C (n := 2) dd 0)) (comp1 φ (pt C (n := 2) dd 1))

structure GmPack (Y : FBChart C V O dd) {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0)
    (γ γ' : Fin 2 → Fin 2 → Pt C 1 dd) : Prop where
  endo : ∀ r s, IsEndo Y (γ r s)
  endo' : ∀ r s, IsEndo Y (γ' r s)
  comm : ∀ r s a, comp1 (γ r s) (Y.B.A.act a) = comp1 (Y.B.A.act a) (γ r s)
  comm' : ∀ r s a, comp1 (γ' r s) (Y.B.A.act a) = comp1 (Y.B.A.act a) (γ' r s)
  lin : ∀ r s c, linAct (γ r s) (p.e c) = p.gm (p.ty0 c) r s • p.e c
  lin' : ∀ r s c, linAct (γ' r s) (p.e c) = p.gm (p.ty0 c + p.hd) r s • p.e c
  img : ∀ r s (v : Fin dd → C), ∃ b : I0 → C, linAct (γ r s) v = ∑ c, b c • p.e c
  img' : ∀ r s (v : Fin dd → C), ∃ b : I0 → C, linAct (γ' r s) v = ∑ c, b c • p.e c
  adj : ∀ r s, IntS V (FB.expS C (ev (n := 2) ![comp1 (γ r s) (pt C dd 0), pt C dd 1] Y.h -
    ev (n := 2) ![pt C dd 0, comp1 (γ' r s) (pt C dd 1)] Y.h))

def GmPackSt (Y : FBChart C V O dd) {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0) : Prop :=
  ∃ γ γ' : Fin 2 → Fin 2 → Pt C 1 dd, GmPack Y p γ γ'

end Formalism.L2.FormalSeriesBounds
end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.PowerSeriesFrobeniusCongruence
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

variable {C : Type} [Field C] {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

def ee (i j : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 i + Finsupp.single 1 j

def inV (j : Fin 2) (f : PowerSeries C) : MvPowerSeries (Fin 2) C :=
  PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin 2) C) f

def HH (X : RawChart C d I κ) (x z : κ → PowerSeries C) : MvPowerSeries (Fin 2) C :=
  hAt X (fun i => inV 0 (x i)) (fun i => inV 1 (z i))

def rs (j : Fin 2) (c : C) : MvPowerSeries (Fin 2) C →+* MvPowerSeries (Fin 2) C :=
  MvPowerSeries.rescale (fun i => if i = j then c else 1)

def rc (c : C) (γ : κ → PowerSeries C) : κ → PowerSeries C := fun i => PowerSeries.rescale c (γ i)

def pw (n : ℕ) (δ : κ → PowerSeries C) : κ → PowerSeries C :=
  fun i => PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (δ i)

end SelfConjCharts

open SelfConjCharts

def PowerSeriesFrobeniusCongruence : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (σ : Type) (f : MvPowerSeries σ C), IntS V f → ∀ μ : σ →₀ ℕ,
    V.MM (MvPowerSeries.coeff (V.l • μ) (f ^ V.l) - MvPowerSeries.coeff μ f ^ V.l)

def RootsOfUnityProductCongruence : Prop :=
  ∀ (C : Type) [Field C] (V : VF C) (ζ : C), ζ ^ V.l = 1 → ∀ (j : Fin 2) (f : MvPowerSeries (Fin 2) C), IntS V f →
    ∀ μ, V.MM (MvPowerSeries.coeff μ (∏ k ∈ Finset.range V.l, rs j (ζ ^ k) f - f ^ V.l))

def ExpLowOrderTruncation : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (F : MvPowerSeries (Fin 2) C) (m : ℕ), 1 ≤ m →
    (∀ i j, j < m → MvPowerSeries.coeff (ee i j) F = 0) →
    ∀ i j, j < 2 * m → MvPowerSeries.coeff (ee i j) (mvExp F) =
      MvPowerSeries.coeff (ee i j) (1 : MvPowerSeries (Fin 2) C) + MvPowerSeries.coeff (ee i j) F

def GaugeLeadingTermLinear : Prop :=
  ∀ (C : Type) [Field C] (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ),
    (∀ e : Fin 2 × κ →₀ ℕ, (∀ s ∈ e.support, s.1 ≠ 1) → MvPowerSeries.coeff e X.h = 0) →
    ∀ x c : κ → PowerSeries C, (∀ i, PowerSeries.constantCoeff (x i) = 0) → ∀ m : ℕ, 1 ≤ m →
    (∀ i j, j < m → PowerSeries.coeff j (c i) = 0) →
    (∀ n j, j < m → MvPowerSeries.coeff (ee n j) (HH X x c) = 0) ∧
      ∀ n, MvPowerSeries.coeff (ee n m) (HH X x c) =
        -PowerSeries.coeff n (alongCv x (X.sg fun i => PowerSeries.coeff m (c i)))

def GaugeRescalingSymmetry : Prop :=
  ∀ (C : Type) [Field C] (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ) (x z : κ → PowerSeries C), (∀ i, PowerSeries.constantCoeff (x i) = 0) →
    (∀ i, PowerSeries.constantCoeff (z i) = 0) → ∀ c : C,
    HH X (rc c x) z = rs 0 c (HH X x z) ∧ HH X x (rc c z) = rs 1 c (HH X x z)

def IntegralUnitFamilies : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ), Basic X V → BiInt X V → ∀ ζ : C, ζ ^ V.l = 1 → ∀ (n : ℕ), 0 < n →
    ∀ γ δ c : κ → PowerSeries C, IsCv V γ → IsCv V δ → IsCv V c → NormRel X V.l n ζ γ δ →
    IntS V (mvExp (∑ k ∈ Finset.range V.l, HH X (rc (ζ ^ k) γ) c - HH X (pw n δ) c)) ∧
      IntS V (mvExp (∑ k ∈ Finset.range V.l, HH X c (rc (ζ ^ k) γ) - HH X c (pw n δ)))

def GenericPointUnitCongruence : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (d : ℕ) (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ]
    (X : RawChart C d I κ), Basic X V → BiInt X V → ∀ ζ : C, ζ ^ V.l = 1 → ∀ (n : ℕ), 0 < n →
    ∀ z ε δ : κ → PowerSeries C, IsCv V z → IsCv V ε → IsCv V δ → NormRel X V.l n ζ z ε →
    (∀ i, V.MM (PowerSeries.coeff 1 (δ i))) → ∀ N : ℕ, 0 < N → ∀ i j, i ≤ N →
    V.MM (MvPowerSeries.coeff (ee i j)
      (mvExp (∑ k ∈ Finset.range V.l, HH X (pw N δ) (rc (ζ ^ k) z) - HH X (pw N δ) (pw n ε)) - 1))

end Formalism.L2.FormalSeriesBounds
end
end
