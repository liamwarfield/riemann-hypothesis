module

public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FlagIndices

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct

section General

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

def TorsVal (P : RigLB G) {n : ℕ} (s : Out.H0 P.L n) {F : Type} [Field F] {b : Sp F ⟶ S} (y : Over.mk b ⟶ G)
    (N : ℕ) (T : F) : Prop :=
  1 ≤ N ∧ y ^ N = 1 ∧
  ∃ (w : LB.Gen (LB.LinComb P.L (K := Fin 2) ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![1, -((N : ℤ) ^ 2)]))
    (i₀ i : P.L.ι), w.IsGen ∧ ⊤ ≤ (1 : Over.mk b ⟶ G).left ⁻¹ᵁ P.L.U i₀ ∧ ⊤ ≤ y.left ⁻¹ᵁ P.L.U i ∧
    T * (valF (1 : Over.mk b ⟶ G).left _ (w.s ![i₀, i₀]).val *
        valF (X := (𝟙_ (Over S)).left) b _ (P.rig.s fun _ => i₀).val ^ (N ^ 2)) ^ n =
      valF y.left _ (s.f fun _ => i) ^ (N ^ 2) * valF y.left _ (w.s ![i₀, i]).val ^ n

structure ArchFrame (P : RigLB G) (z : Sp ℂ ⟶ S) (g : ℕ) where

  A : Over (Sp ℂ)
  [grp : GrpObj A]

  φ : A.left ⟶ G.left
  cart : IsGrpPullback A G z φ

  u : HolUnif A (P.L.pull φ) g

  Hm : Matrix (Fin g) (Fin g) ℂ

  χ : u.Λ → ℂ
  ah : u.IsAH Hm χ
  rig : ∀ i : P.L.ι, ⊤ ≤ ((u.ex 0).left ≫ φ) ⁻¹ᵁ P.L.U i →
    u.fr (fun _ => i) 0 = valF (X := (𝟙_ (Over S)).left) z _ (P.rig.s fun _ => i).val

attribute [instance] ArchFrame.grp

namespace ArchFrame

variable {P : RigLB G} {z : Sp ℂ ⟶ S} {g : ℕ} (a : ArchFrame P z g)

def pt (w : Fin g → ℂ) : Sp ℂ ⟶ G.left := (a.u.ex w).left ≫ a.φ

def IsFn {n : ℕ} (s : Out.H0 P.L n) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  ∀ (i : P.L.ι) (w : Fin g → ℂ), ⊤ ≤ a.pt w ⁻¹ᵁ P.L.U i →
    valF (a.pt w) _ (s.f fun _ => i) = θ w * a.u.fr (fun _ => i) w ^ n

def herm (w w' : Fin g → ℂ) : ℂ := w ⬝ᵥ a.Hm.mulVec (star w')

def nrm (n : ℕ) (θ : (Fin g → ℂ) → ℂ) (w : Fin g → ℂ) : ℝ :=
  ‖θ w‖ * Real.exp (-(Real.pi * n / 2) * (a.herm w w).re)

def IsTheta (n : ℕ) (θ : (Fin g → ℂ) → ℂ) : Prop :=
  Differentiable ℂ θ ∧ ∀ (l : a.u.Λ) (w : Fin g → ℂ),
    θ (w + l) = (a.χ l * Complex.exp (Real.pi * a.herm w l + Real.pi / 2 * a.herm l l)) ^ n * θ w

def IsThetaMeanSquareNorm (θ : (Fin g → ℂ) → ℂ) (b : ℝ) : Prop :=
  0 < b ∧ ∀ Fd : Set (Fin g → ℂ), IsAddFundamentalDomain a.u.Λ Fd volume →
    b ^ 2 = (∫ w in Fd, a.nrm 1 θ w ^ 2) / (volume Fd).toReal

def IsTan (c : Fin g → ℂ) (v : epsAt z ⟶ G) : Prop :=
  ∃ v' : epsR ℂ ⟶ a.A, v'.left ≫ a.φ = v.left ∧ a.u.IsDiff c v'

end ArchFrame

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

structure PPData (H : Host E) (L : Type) [Field L] [NumberField L] where

  t : SAB H (Sp (𝓞 L))

  tK : SAB H (Sp L)
  m : SABMap tK t (spMap (algebraMap (𝓞 L) L))
  princ : IsPrincipal tK

  B : HermitianBundle.{0} L
  MB : LieModel t.G (𝟙 _) B.carrier
  fib : IsFibre (HodgeIP t.G t.PP.L) (𝟙 _) B MB

abbrev emb {L : Type} [Field L] [NumberField L] (σ : L →+* ℂ) : Sp ℂ ⟶ Sp (𝓞 L) :=
  spMap (σ.comp (algebraMap (𝓞 L) L))

def mean (L : Type) [Field L] [NumberField L] (f : (L →+* ℂ) → ℝ) : ℝ := (∑ σ : L →+* ℂ, f σ) / Module.finrank ℚ L

namespace PPData

variable {H : Host E} {L : Type} [Field L] [NumberField L] (D : PPData H L)

def g : ℕ := Module.finrank (𝓞 L) D.B.carrier

def hp : ℝ := max (-D.B.normDegree ⊤) 0

abbrev Frame (σ : L →+* ℂ) := ArchFrame D.t.PP (emb σ) D.g

def len (σ : L →+* ℂ) (x : D.B.carrier) : ℝ :=
  Real.sqrt ((D.B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) : ℂ).re

def IsVec {σ : L →+* ℂ} (a : D.Frame σ) (x : D.B.carrier) (c : Fin D.g → ℂ) : Prop :=
  ∃ v : epsAt (emb σ) ⟶ D.t.G, (v.left ≫ (𝟙 D.t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt x).left) ∧ a.IsTan c v

abbrev Ext {L' : Type} [Field L'] [NumberField L'] [Algebra L L'] (D' : PPData H L') :=
  SABMap D'.t D.t (spMap (algebraMap (𝓞 L) (𝓞 L')))

def HasTheta (th : Out.H0 D.t.PP.L 1) (Φ : ℝ) : Prop :=
  ∃ b : (L →+* ℂ) → ℝ, (∀ (σ : L →+* ℂ) (a : D.Frame σ) θ, a.IsFn th θ → a.IsThetaMeanSquareNorm θ (b σ)) ∧
    mean L (fun σ => Real.log (b σ)) ≤ Φ

def SupLe {n : ℕ} (s : Out.H0 D.t.PP.L n) (M : (L →+* ℂ) → ℝ) : Prop :=
  ∀ (σ : L →+* ℂ) (a : D.Frame σ) θ, a.IsFn s θ → ∀ w, a.nrm n θ w ≤ M σ

end PPData

def KeyDegSt : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L]
    [NumberField L] (D : PPData H L), 1 ≤ D.g →
    ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra L L') (D' : PPData H L') (_ : D.Ext D')
      (th : Out.H0 D'.t.PP.L 1), D'.HasTheta th (D.hp / 2 + C * D.g)

def LineSt : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L]
    [NumberField L] (D : PPData H L) (x : D.B.carrier), x ≠ 0 →
    -mean L (fun σ => Real.log (D.len σ x)) ≤ C * Real.log (2 + D.g + D.hp)

end GlobalTheory.CompanionTheory.Ar.Sl
end
end

section -- merged from Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

open GroundTheory.Heights₂.Heights.LowerBoundFree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {II : IntersectionSystem} {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
  [Algebra ℚ Ω] {W : CMType H → Type} [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]

structure CptOrigin (Y : Model Xo c β) (S₀ : Finset ℕ) (Dc : ComponentData II (CMType H) K J Ω W)
    (Hd : HodgeData Dc) where

  𝔐 : HodgeCpt Y S₀ Dc.y

  deg : ℕ
  cover : 𝔐.IsCover deg

  bg : CMType H → CMType H ⊕ CMType H

  sm : CMType H → CMType H ⊕ CMType H
  side : (bg = Sum.inl ∧ sm = Sum.inr ∧ Dc.j = D.p) ∨ (bg = Sum.inr ∧ sm = Sum.inl ∧ Dc.j = D.q)
  N_eq : Dc.N = D.p + D.q

  i : ∀ τ, W τ →ₗ[Ω] 𝔐.Li
  i_inj : ∀ τ, Function.Injective (i τ)
  i_range : ∀ τ, LinearMap.range (i τ) = 𝔐.Vgen (bg τ) ⊔ 𝔐.Vgen (sm τ)
  F_eq : ∀ τ, Hd.F τ = (𝔐.Vgen (bg τ)).comap (i τ)
  lat : ∀ τ, (Lat.comap (fun p => 𝔐.V (bg τ) p ⊔ 𝔐.V (sm τ) p) (i τ)).IsChartOf (segreCoord Dc.y) (Dc.W τ).lat
  bd : ∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ Dc.y z w → (w ∈ Dc.Bd ↔ ¬ 𝔐.Interior z)
  metric : ∀ τ a (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ Dc.y z w → 𝔐.Interior z →
    InFrameDomain Dc.y ((Dc.h τ).chart a) ((Dc.h τ).fr a) w →
      𝔐.M.GramAt 𝔐.t.PP.L z (fun k => i τ ((Dc.h τ).b a k)) ((Dc.h τ).gram a w)
  S_disj : Disjoint Dc.S S₀
  R_ge : ∀ p ∈ Dc.S, 4 ≤ 𝔐.R p
  tors : ∀ p ∈ Dc.S, FullTorsion 𝔐.t.G 𝔐.ξ (p ^ 𝔐.R p)
  ht_vb : ∀ p ∈ Dc.S, ∀ s, (𝔐.HT p s).IsVBOn {q | ∀ r : ℕ, r.Prime → r ≠ p → ¬ InFibre 𝔐.ξ r q} (labelRk D s)
    (𝔐.Vgen s)
  vert : ∀ p ∈ Dc.S, ∀ q : Cpt 𝔐.ξ, InFibre 𝔐.ξ p q → ∀ ch, InChart 𝔐.ξ (segreCoord Dc.y) ch q →
    ∀ (b b' : ∀ τ, Fin (labelRk D (sm τ)) → 𝔐.Li)
      (T : ∀ τ, Matrix (Fin (labelRk D (sm τ))) (Fin (labelRk D (sm τ))) Ω),
      (∀ τ, (𝔐.V (sm τ)).IsFrameAt (b τ) q) → (∀ τ, (𝔐.HT p (sm τ)).IsFrameAt (b' τ) q) →
      (∀ τ k, b' τ k = ∑ k', T τ k' k • b τ k') →
        unitAt 𝔐.ξ q ((∏ τ, (T τ).det) / (MvPolynomial.aeval Dc.y (Dc.vnum p) / MvPolynomial.aeval Dc.y (Dc.vden p) *
          chartMono Dc.y ch (-Dc.vdeg p)))

section Ranks

variable {Y : Model Xo c β} {S₀ : Finset ℕ} {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc}
  (Or : CptOrigin Y S₀ Dc Hd)

theorem CptOrigin.rk_bg (τ : CMType H) : labelRk D (Or.bg τ) = Dc.j := by
  rcases Or.side with ⟨h, -, hj⟩ | ⟨h, -, hj⟩ <;> simp [h, hj]

theorem CptOrigin.rk_sm (τ : CMType H) : labelRk D (Or.sm τ) = Dc.N - Dc.j := by
  rcases Or.side with ⟨-, h, hj⟩ | ⟨-, h, hj⟩ <;> simp [h, hj, Or.N_eq]

theorem CptOrigin.bg_ne_sm (τ τ' : CMType H) : Or.bg τ ≠ Or.sm τ' := by
  rcases Or.side with ⟨h, h', -⟩ | ⟨h, h', -⟩ <;> simp [h, h']


include Or in
theorem CptOrigin.n_eq : Dc.n = Fintype.card (CMType H) * D.p * D.q := by
  rcases Or.side with ⟨-, -, hj⟩ | ⟨-, -, hj⟩ <;> simp [ComponentData.n, hj, Or.N_eq]
  ring

end Ranks

namespace Origin

section Period

variable {Ψ : Type} [Fintype Ψ] {V : Ψ → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module Ω (V τ)]
  {Dc : ComponentData II Ψ K J Ω V} {T T' : Set ((Σ k, J k) → ℂ)} {O' Lt : Type} [CommRing O'] [AddCommGroup Lt]
  [Module O' Lt]

end Period

section Plane

open Line GaussianInt

variable (II) (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2])

end Plane

end Origin

section Comparison₂

variable {Y : Model Xo c β} {S₀ : Finset ℕ} {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc}
  (Or : CptOrigin Y S₀ Dc Hd) {T T' : Set ((Σ k, J k) → ℂ)} {O' Lt : Type} [CommRing O'] [AddCommGroup Lt]
  [Module O' Lt]

variable {Or}

end Comparison₂

end GlobalTheory.CompanionTheory.Ar
end
end
