module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
public import GroundTheory.HeightsAndTheta.Heights.IterateExamples.Statements

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
noncomputable section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace GlobalTheory.CompanionTheory.Ar.Top

structure RootTower (Ψ : Type) [Fintype Ψ] (N : ℕ) where

  j : ℕ
  j_pos : 1 ≤ j
  j_lt : j < N

  Comp : Type
  [finC : Fintype Comp]
  [neC : Nonempty Comp]

  bad : Finset ℕ
  two_mem : 2 ∈ bad

  nu : Wt Ψ N
  nu_rat : IsRatWt nu

  M : ℕ → Comp → RootModel Ψ N

attribute [instance] RootTower.finC RootTower.neC

def scale (s : ℝ) : ℝ := Real.exp (-(s ^ 2)⁻¹)

namespace RootTower

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (T : RootTower Ψ N) (II : IntersectionSystem)

def InS (B p : ℕ) : Prop := p.Prime ∧ (p ≤ B ∨ p ∈ T.bad)

def lamS (lam : Wt Ψ N) (s : ℝ) : Wt Ψ N := lam - s • T.nu

def vol (c : T.Comp) : ℝ :=
  (T.M 2 c).geoFun (toA (linRoot (rhoWt : Wt Ψ N) ^ dimFl Ψ N)) / flagDeg (rhoWt : Wt Ψ N)

def volT : ℝ := ∑ c, T.vol c

def PPc (B : ℕ) (c : T.Comp) (F : RP Ψ N) : ℝ := (T.M B c).PP II (toA F)

def PPt (B : ℕ) (F : RP Ψ N) : ℝ := ∑ c, T.PPc II B c F

def PBs (B : ℕ) (c : T.Comp) (lam : Wt Ψ N) (s : ℝ) : ℝ := (T.M B c).PP II (linA lam s ^ (dimFl Ψ N + 1))

def PB (B : ℕ) (lam : Wt Ψ N) : ℝ := T.PPt II B (linRoot lam ^ (dimFl Ψ N + 1))

def mbarTop (B : ℕ) (c : T.Comp) (lam : Wt Ψ N) (s : ℝ) : ℝ :=
  (T.M B c).arFun II (scale s) (linA (T.lamS lam s) s ^ (dimFl Ψ N + 1))

def mDeg (B : ℕ) (c : T.Comp) (lam : Wt Ψ N) (s : ℝ) : ℝ :=
  (T.M B c).geoFun (linA (T.lamS lam s) s ^ dimFl Ψ N)

def mbarHt (B : ℕ) (c : T.Comp) (lam : Wt Ψ N) (s : ℝ) (W : Ideal (MRing (T.M B c).ι)) : ℝ :=
  (T.M B c).ht II (scale s) (T.lamS lam s) s W

def slope (B : ℕ) (c : T.Comp) (u : Wt Ψ N) : ℝ :=
  T.PPc II B c (linRoot u ^ (dimFl Ψ N + 1)) / (((dimFl Ψ N : ℝ) + 1) * (T.vol c * flagDeg u))

def Conv : Prop := ∀ B c, (T.M B c).Converges II

def Proportional : Prop :=
  (∀ c, 0 < T.vol c) ∧ (∀ B c (F : RP Ψ N), (T.M B c).geoFun (toA F) = T.vol c * degFl F) ∧
    ∀ B B' c, (T.M B c).geoFun = (T.M B' c).geoFun

def I1 : Prop :=
  ∃ C : ℝ, ∀ B : ℕ, 2 ≤ B → ∀ c m, |(T.M B c).PP II (monomial m 1)| ≤ C * Real.log B

def I2 : Prop :=
  ∀ abelian₂ : ℝ, ∃ s₀ > (0 : ℝ), ∃ C : ℝ, ∀ B : ℕ, 2 ≤ B → ∀ c (lam : Wt Ψ N) (s : ℝ), l1 lam ≤ abelian₂ → 0 < s → s ≤ s₀ →
    Dominant (T.lamS lam s) → |T.mbarTop II B c lam s - T.PBs II B c (T.lamS lam s) s| ≤ C * s

def A1 : Prop :=
  ∀ abelian₂ : ℝ, ∃ s₀ > (0 : ℝ), ∀ B : ℕ, 2 ≤ B → ∀ c (lam : Wt Ψ N) (s : ℝ), l1 lam ≤ abelian₂ → 0 < s → s ≤ s₀ →
    Dominant (T.lamS lam s) → (T.M B c).Semipos (scale s) (T.lamS lam s) s

def ModelNefStatement : Prop := ∀ B c p, T.InS B p → ∀ mu : Wt Ψ N, Dominant mu → (T.M B c).NefAt p mu 0

def M2 : Prop :=
  ∀ B c (p : ℕ), p.Prime → ¬ T.InS B p → ∀ mu : Wt Ψ N, Dominant mu → NefThreshold T.j p mu → (T.M B c).NefAt p mu 0

def ANef : Prop := ∀ B c, (T.M B c).NefFib 0 1

def I3 : Prop :=
  ∀ abelian₂ : ℝ, ∃ s₀ > (0 : ℝ), ∀ B : ℕ, 2 ≤ B → ∀ c (lam : Wt Ψ N) (s : ℝ), l1 lam ≤ abelian₂ → 0 < s → s ≤ s₀ →
    Dominant (T.lamS lam s) → NefThreshold T.j B (T.lamS lam s) →
      (T.M B c).NefFib (T.lamS lam s) s ∧ (T.M B c).Semipos (scale s) (T.lamS lam s) s

def I5 : Prop :=
  ∀ c₀ > (0 : ℝ), ∃ θ₀ > (0 : ℝ), ∃ C : ℝ, ∀ B : ℕ, 2 ≤ B → ∀ c (lam : Wt Ψ N) (θ : ℝ) (s : ℚ), IsRatWt lam →
    ‖lam‖ ≤ 1 → 0 < θ → θ ≤ θ₀ → (s : ℝ) = θ ^ 2 → (∀ τ, θ ≤ gap T.j lam τ) → CompactGapsGE T.j c₀ lam →
      ∀ W, (T.M B c).IsPt W → -(C * Real.log (B / (s : ℝ))) ≤ T.mbarHt II B c lam s W

def I6 : Prop :=
  ∀ c₀ > (0 : ℝ), ∃ θ₀ > (0 : ℝ), ∃ C : ℝ, ∀ B : ℕ, 2 ≤ B → ∀ c (lam : Wt Ψ N) (θ : ℝ) (s : ℚ), IsRatWt lam →
    ‖lam‖ ≤ 1 → 0 < θ → θ ≤ θ₀ → (s : ℝ) = θ ^ 2 → (∀ τ, θ ≤ gap T.j lam τ) → CompactGapsGE T.j c₀ lam →
      ∃ F : Set (Ideal (MRing (T.M B c).ι)), IsZariskiDense (T.M B c).P F ∧
        ∀ W ∈ F, (T.M B c).IsPt W ∧ T.mbarHt II B c lam s W ≤ C * Real.log B

def I7 : Prop :=
  ∀ B c, (∀ lam : Wt Ψ N, Dominant lam → (T.M B c).NefGen lam 0) ∧ (T.M B c).NefGen 0 1 ∧ (T.M B c).EffDiff T.nu

def I8 (hh : RP Ψ N → ℝ) : Prop :=
  ∀ B : ℕ, 2 ≤ B → ∀ c τ (a b : Fin N), (b : ℕ) = a + 1 → (b : ℕ) ≠ T.j → ∀ lam : Wt Ψ N,
    T.PPc II B c (linRoot (swapWt τ a b lam) ^ (dimFl Ψ N + 1)) -
        T.vol c * hh (linRoot (swapWt τ a b lam) ^ (dimFl Ψ N + 1)) =
      -(T.PPc II B c (linRoot lam ^ (dimFl Ψ N + 1)) - T.vol c * hh (linRoot lam ^ (dimFl Ψ N + 1)))

def Prop6 (frob : ℕ → Ψ → ℕ → Ψ ⊕ Ψ) : Prop :=
  ∀ B₀ B : ℕ, 2 ≤ B₀ → B₀ ≤ B → ∀ c τ (k : ℕ), 1 ≤ k → k ≤ N → ∀ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N + 1 - k) →
    T.PPc II B₀ c (pk τ k * Q) = T.PPc II B c (pk τ k * Q) +
      T.vol c * ∑ p ∈ (Finset.Ioc B₀ B).filter (fun p => p.Prime ∧ p ∉ T.bad), deltaTerm T.j p τ (frob p τ) k Q

def PropA : Prop :=
  ∃ Γ : Subgroup (Equiv.Perm Ψ), (∀ τ τ' : Ψ, ∃ σ ∈ Γ, σ τ = τ') ∧ ∀ σ ∈ Γ, ∀ B : ℕ, 2 ≤ B → ∀ F : RP Ψ N,
    T.PPt II B (rename (fun x : Ψ × Fin N => (σ x.1, x.2)) F) = T.PPt II B F

def PropF (C rd Lval : ℝ) : Prop :=
  ∃ h : ℕ → T.Comp → Ψ → ℝ,
    (∀ B : ℕ, 2 ≤ B → ∀ c τ (Q : RP Ψ N), Q.IsHomogeneous (dimFl Ψ N) →
      T.PPc II B c (pk τ 1 * Q) = h B c τ * (T.vol c * degFl Q)) ∧
    ∀ B : ℕ, 128 ≤ B → T.bad.card ≤ B → ∀ c τ, |h B c τ| ≤ C * N * bigLam B rd Lval

def VolEq : Prop := ∀ c c', T.vol c = T.vol c'

end RootTower

def I9 {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ} (hh : RP Ψ N → ℝ) : Prop :=
  (∀ lam : Wt Ψ N, Dominant lam → (∃ τ, ∃ a b : Fin N, (b : ℕ) = a + 1 ∧ lam τ a = lam τ b) →
      hh (linRoot lam ^ (dimFl Ψ N + 1)) = 0) ∧
    (∀ lam : Wt Ψ N, Dominant lam → 0 ≤ hh (linRoot lam ^ (dimFl Ψ N + 1))) ∧
    ∀ τ (Q : RP Ψ N), Q.IsHomogeneous (dimFl Ψ N) → hh (pk τ 1 * Q) = 0

end GlobalTheory.CompanionTheory.Ar.Top
end
end

section -- merged from Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
namespace GlobalTheory.CompanionTheory.Ar.Num

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

structure LocPair {K : Type} (ι : K → Type) (R : Type) [CommRing R] (σ : Type) where

  x : σ → K → ℤ

  x' : σ → K → ℤ

  f : σ → MRing ι R

  g : σ → MRing ι R

variable {K : Type} {ι : K → Type} {σ σ' : Type}

def LocPair.map {R R' : Type} [CommRing R] [CommRing R'] (T : LocPair ι R σ) (ψ : R →+* R') :
    LocPair ι R' σ :=
  ⟨T.x, T.x', fun i => MvPolynomial.map ψ (T.f i), fun i => MvPolynomial.map ψ (T.g i)⟩

def LocPair.comp {R : Type} [CommRing R] (T : LocPair ι R σ) (e : σ' → σ) : LocPair ι R σ' :=
  ⟨T.x ∘ e, T.x' ∘ e, T.f ∘ e, T.g ∘ e⟩

def IsMixExpansion [Fintype σ] (m : ℕ) (V : MvPolynomial (σ ⊕ σ) ℝ) (Gs : σ → MvPolynomial (σ ⊕ σ) ℝ) : Prop :=
  V = ∑ i, (X (Sum.inl i) - X (Sum.inr i)) * Gs i ∧ ∀ i, (Gs i).IsHomogeneous m

def mixDiff (F : MvPolynomial σ ℝ) : MvPolynomial (σ ⊕ σ) ℝ := rename Sum.inl F - rename Sum.inr F

variable [DecidableEq K]

def genNum (F : Type) [Field F] (V : Ideal (MRing ι F)) (cls : σ → K → ℤ) (H : MvPolynomial σ ℝ)
    (Q : List (K → ℤ)) : ℝ :=
  ∑ μ ∈ H.support, H.coeff μ * (intNumL F V (classList cls μ ++ Q) : ℝ)

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def cycList (Z : Ideal (MRing ι O) → ℤ) (l : List (K → ℤ)) : ℤ := cycEval (fun W => vNumL W l) Z

def cycNum (Z : Ideal (MRing ι O) → ℤ) (cls : σ → K → ℤ) (H : MvPolynomial σ ℝ) (Q : List (K → ℤ)) : ℝ :=
  ∑ μ ∈ H.support, H.coeff μ * (cycList Z (classList cls μ ++ Q) : ℝ)

def LocPair.IsVert (T : LocPair ι O σ) (P : Ideal (MRing ι O)) (ϖ : O) : Prop :=
  ∀ i, IsVerticalDivisor P ϖ (T.x i - T.x' i) (T.f i) (T.g i)

def LocPair.val [Fintype σ] (T : LocPair ι O σ) (P : Ideal (MRing ι O))
    (Gs : σ → MvPolynomial (σ ⊕ σ) ℝ) : ℝ :=
  ∑ i, cycNum (ratDiv P (T.f i) (T.g i)) (Sum.elim T.x T.x') (Gs i) []

def LocPair.ck {r : ℕ} (T : LocPair ι O (Fin r)) (P : Ideal (MRing ι O)) (k : ℕ) (Q : List (K → ℤ)) : ℤ :=
  pairNum P T.x T.x' T.f T.g (psumExpansion r k) Q

def laNum {r : ℕ} (P : Ideal (MRing ι O)) (a : O) (x : Fin r → K → ℤ) (k : ℕ) (Q : List (K → ℤ)) : ℤ :=
  (k : ℤ) * cycEval (fun W => classNum x (psum (Fin r) ℤ (k - 1)) Q W) (divCycle P (C a))

section Labels

variable {Sg : Type} (P : Ideal (MRing ι O)) (d p : ℕ) (φ : Equiv.Perm Sg) {r s : Sg → ℕ}
  (lie : ∀ τ, LocPair ι O (Fin (r τ))) (om : ∀ τ, LocPair ι O (Fin (s τ)))

def Relations : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ Q : List (K → ℤ), Q.length + k = d + 1 → ∃ h : Sg → ℝ,
    (∀ τ, (((lie τ).ck P k Q : ℤ) : ℝ) + (((om τ).ck P k Q : ℤ) : ℝ) =
      h τ - ((laNum P (p : O) (lie τ).x k Q : ℤ) : ℝ) / ((p : ℝ) - 1)) ∧
    ∀ τ, (p : ℝ) ^ k * h τ = h (φ τ) + ((laNum P (p : O) (lie (φ τ)).x k Q : ℤ) : ℝ)

def LabelChernComparison [Fintype Sg] [DecidableEq Sg] : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ Q : List (K → ℤ), Q.length + k = d + 1 → ∀ τ,
    (((lie τ).ck P k Q : ℤ) : ℝ) + (((om τ).ck P k Q : ℤ) : ℝ) =
      ∑ τ', GroundTheory.Heights₂.Heights.ModelLeaves.co φ p k τ τ' * ((laNum P (p : O) (lie τ').x k Q : ℤ) : ℝ)

end Labels

def BundleChernComparison (P : Ideal (MRing ι O)) (d p : ℕ) {r s : ℕ} (lie : LocPair ι O (Fin r))
    (om : LocPair ι O (Fin s)) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ Q : List (K → ℤ), Q.length + k = d + 1 →
    ((lie.ck P k Q : ℤ) : ℝ) + ((om.ck P k Q : ℤ) : ℝ) =
      (1 / ((p : ℝ) ^ k - 1) - 1 / ((p : ℝ) - 1)) * ((laNum P (p : O) lie.x k Q : ℤ) : ℝ)

def IsFibreComp (P : Ideal (MRing ι O)) (W : Ideal (MRing ι O)) : Prop :=
  W ∈ (P ⊔ (IsLocalRing.maximalIdeal O).map (C : O →+* MRing ι O)).minimalPrimes ∧ IsRelevant W

def PowerSumsVanish (P : Ideal (MRing ι O)) (d : ℕ) {N : ℕ} (x : Fin N → K → ℤ) : Prop :=
  ∀ W, IsFibreComp P W → ∀ k : ℕ, 1 ≤ k → ∀ Q : List (K → ℤ), Q.length + k = d →
    classNum x (psum (Fin N) ℤ k) Q W = 0

def TrivFlagAt [Fintype K] (W : Ideal (MRing ι O)) {N : ℕ} (x : Fin N → K → ℤ) : Prop :=
  ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra (IsLocalRing.ResidueField O) Ω) (y : (Σ k, ι k) → Ω)
    (w : Module.Basis (Fin N) Ω (Fin N → Ω)),
    pointIdeal (IsLocalRing.ResidueField O) y = specialIdeal W ∧
      IsFlagFrame y (scaledTrivBundle (IsLocalRing.ResidueField O) (segreVec y) N (one_ne_zero (α := Ω))) w x

section Roots

variable {Ψ : Type} {N : ℕ}

def rootPs (τ : Ψ) (k : ℕ) : MvPolynomial (Ψ × Fin N) ℝ := ∑ i : Fin N, X (τ, i) ^ k

def liePs (j m : ℕ) : Ψ ⊕ Ψ → MvPolynomial (Ψ × Fin N) ℝ
  | Sum.inl τ => ∑ i ∈ Finset.univ.filter (fun i : Fin N => (i : ℕ) < j), X (τ, i) ^ m
  | Sum.inr τ => ∑ i ∈ Finset.univ.filter (fun i : Fin N => j ≤ (i : ℕ)), (-X (τ, i)) ^ m

variable [Fintype Ψ] [DecidableEq Ψ]

def bracket (j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (p k : ℕ) (τ : Ψ) : MvPolynomial (Ψ × Fin N) ℝ :=
  C (k : ℝ) * ∑ τ', C (GroundTheory.Heights₂.Heights.ModelLeaves.co φ p k (Sum.inl τ) τ') * liePs j (k - 1) τ'

def FlagChernComparison (P : Ideal (MRing ι O)) (d p j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (T : LocPair ι O (Ψ × Fin N)) :
    Prop :=
  ∀ τ, ∀ k : ℕ, 1 ≤ k → ∀ Q : List (K → ℤ), Q.length + k = d + 1 →
    (((T.comp fun i : Fin N => (τ, i)).ck P k Q : ℤ) : ℝ) =
      cycNum (divCycle P (C (p : O))) T.x (bracket j φ p k τ) Q

end Roots

end

end GlobalTheory.CompanionTheory.Ar.Num
end
