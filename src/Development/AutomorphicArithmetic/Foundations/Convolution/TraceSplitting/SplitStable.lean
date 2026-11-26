module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.NormCharSplit
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.EigSplit
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CuspidalMultiplicityOneTotallyComplex
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.EvExSub
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.MatchOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TypedEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.OccursBasics

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical
open scoped ComplexConjugate

namespace UpperTheory.ConvolutionTheory.T

def AbsLast : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (v : Pl K) [MeasurableSpace (Gw n v)] [BorelSpace (Gw n v)]
    (m : Measure (Gw n v)) [m.IsHaarMeasure] (U : Subgroup (Gw n v)), CO U →
    ∀ (ι : Type) [Fintype ι] (τ : ι → SmIrr (Gw n v)) (a : ι → ℂ) (Z : ι → Multiset ℂ) (τ₀ : SmIrr (Gw n v)) (c : ℂ) (Z₀ : Multiset ℂ),
    c ≠ 0 → Z₀ ≠ 0 → 0 ∉ Z₀ → (∀ i, 0 ∉ Z i) → fixedVectors τ₀.ρ U ≠ ⊥ →
    (∀ (φ : Gw n v → ℂ) (s₀ : ℂ) (s : ι → ℂ), Test φ → (∀ u ∈ U, ∀ g, φ (u * g) = φ g ∧ φ (g * u) = φ g) →
      HasTrace m τ₀.ρ φ s₀ → (∀ i, HasTrace m (τ i).ρ φ (s i)) →
      ∀ᶠ j : ℕ in atTop, c * (Z₀.map (· ^ j)).sum * s₀ = ∑ i, a i * ((Z i).map (· ^ j)).sum * s i) →
    ∃ i, Nonempty ((τ i).ρ.Equiv τ₀.ρ)

def PullBack : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (v : Pl F) (w : PlacesOver E v),
    Function.Surjective (completionMap v w.1) →
    ∀ [MeasurableSpace (Gw n v)] [BorelSpace (Gw n v)] [MeasurableSpace (Gw n w.1)] [BorelSpace (Gw n w.1)]
      (mF : Measure (Gw n v)) (mE : Measure (Gw n w.1)), mF.IsHaarMeasure → mE.IsHaarMeasure → ∀ τ' : SmIrr (Gw n w.1),
    ∃ (τ : SmIrr (Gw n v)) (r : ℂ), r ≠ 0 ∧ (∀ τ₁ : SmIrr (Gw n v), Nonempty (τ₁.ρ.Equiv τ.ρ) → LocIso w τ₁ τ') ∧
      (∀ (ψ : Gw n w.1 → ℂ) (s : ℂ), HasTrace mF τ.ρ (fun g => ψ (mapGL n (completionMap v w.1) g)) s → HasTrace mE τ'.ρ ψ (r * s)) ∧
      ∀ (J : Subgroup (Gw n w.1)) (U : Subgroup (Gw n v)), CO J → (∀ g, g ∈ U ↔ mapGL n (completionMap v w.1) g ∈ J) →
        CO U ∧ (fixedVectors τ'.ρ J ≠ ⊥ → fixedVectors τ.ρ U ≠ ⊥) ∧
        ∀ φ : Gw n v → ℂ, Test φ → (∀ u ∈ U, ∀ g, φ (u * g) = φ g ∧ φ (g * u) = φ g) →
          ∃ ψ : Gw n w.1 → ℂ, Test ψ ∧ (∀ u ∈ J, ∀ g, ψ (u * g) = ψ g ∧ ψ (g * u) = ψ g) ∧
            φ = fun g => ψ (mapGL n (completionMap v w.1) g)

def UnitTrace : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)),
    IsSummand μ V → ∀ (w : Pl K) [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] (m : Measure (Gw n w)), m.IsHaarMeasure →
    ∀ (τ : SmIrr (Gw n w)) (J : Subgroup (Gw n w)), Occurs μ V w τ → CO J → V ⊓ fixL μ w J ≠ ⊥ →
      fixedVectors τ.ρ J ≠ ⊥ ∧ Test ((J : Set (Gw n w)).indicator (1 : Gw n w → ℂ)) ∧
      (∀ u ∈ J, ∀ g, (J : Set (Gw n w)).indicator (1 : Gw n w → ℂ) (u * g) = (J : Set (Gw n w)).indicator 1 g ∧
        (J : Set (Gw n w)).indicator (1 : Gw n w → ℂ) (g * u) = (J : Set (Gw n w)).indicator 1 g) ∧
      ∃ s : ℂ, s ≠ 0 ∧ HasTrace m τ.ρ ((J : Set (Gw n w)).indicator 1) s

def OneTerm : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] (n l : ℕ), 0 < n →
    ∀ (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (θ : Twist μ) (𝔰 : Side θ l) (V : Submodule ℂ (LL μ)) Λ t,
    IsSummand μ V → V.map (θ.U : LL μ →ₗ[ℂ] LL μ) = V → At μ 𝔰.S V Λ t → ∀ (x : ℝ) (j : ℕ),
      𝔰.tr (fun V' => At μ 𝔰.S V' Λ t) x j = trOn (eigIn V 𝔰.toAmp.A x) ((𝔰.Uq 0 ^ j) ∘L Rop μ 𝔰.g ∘L θ.U)

def SideSum : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [_root_.NumberField.IsTotallyComplex F] (σ : E ≃ₐ[F] E)
    (n l : ℕ), 0 < n → ∀ (μ : Measure (normOneGL (K := F) (n := n))) [μ.IsHaarMeasure] (ν : Measure (archGroup F n)) [ν.IsHaarMeasure]
    [∀ v : Pl F, MeasurableSpace (Gw n v)] [∀ v : Pl F, BorelSpace (Gw n v)] (m : ∀ v : Pl F, Measure (Gw n v)),
    (∀ v, (m v).IsHaarMeasure ∧ m v (GLnLocal.integralGL (v.adicCompletion F) n) = 1) →
    ∀ (a : TI F n) (q : Pl F) (w₀ : PlacesOver E q) (S : Finset (Pl F)) (UF : ∀ v : Pl F, Subgroup (Gw n v)) (e : Fin n → ℤ),
      Antitone e → ∀ (p : Submodule ℂ (LL μ) → Prop) (x : ℝ), 0 < x →
      ∃ (ι : Type) (_ : Fintype ι) (V : ι → Submodule ℂ (LL μ)) (τ : ι → ∀ v : Pl F, SmIrr (Gw n v)) (b : ι → ℂ) (Z : ι → Multiset ℂ),
        (∀ i, IsSummand μ (V i) ∧ p (V i) ∧ 0 ∉ Z i ∧ ∀ v, Occurs μ (V i) v (τ i v)) ∧
        ∀ (L : GM.Loc σ n q w₀) (𝔣 : Side (Twist.id μ) l), L.S = S → (∀ v ∈ S, L.UF v = UF v) → GM.IsSideF L ν a e 𝔣 →
          ∀ s : ι → Pl F → ℂ, (∀ i, ∀ v ∈ S, HasTrace (m v) (τ i v).ρ (L.f v) (s i v)) → ∀ j : ℕ,
            𝔣.tr p x j = ∑ i, b i * ((Z i).map (· ^ j)).sum * ∏ v ∈ S, s i v

def PickS : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [_root_.NumberField.IsTotallyComplex F]
    [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)) Λ t, IsSummand μ V → AtAE μ V Λ t → ∀ v : Pl F,
      ∃ (S : Finset (Pl F)) (q : Pl F) (_ : PlacesOver E q), v ∈ S ∧ q ∉ S ∧ GM.Split E q ∧ (∀ u ∉ S, GM.Unr E u) ∧
        (∀ w : Pl E, w.under (𝓞 F) ∉ S → V ⊓ fixL μ w (GLnLocal.integralGL (w.adicCompletion E) n) ≠ ⊥) ∧
        ∀ S' : Set (Pl E), (∀ w, w ∈ S' ↔ w.under (𝓞 F) ∈ S ∨ w.under (𝓞 F) = q) →
          At μ S' V Λ t ∧ (∀ τ, (Λ τ).card = n) ∧ ∀ w ∉ S', (t w).card = n ∧ 0 ∉ t w

def PickInf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [_root_.NumberField.IsTotallyComplex F]
    [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μE : Measure (normOneGL (K := E) (n := n))) [μE.IsHaarMeasure] (μF : Measure (normOneGL (K := F) (n := n))) [μF.IsHaarMeasure] (u : LL μE), u ≠ 0 →
      ∃ (m : ℕ) (_ : Module.finrank F E = m + 1) (D : InfD σ m) (s : Fin (m + 1) → archGroup F n →* archGroup E n)
        (hs : ∀ i, Continuous (s i)) (νE : Measure (archGroup E n)) (_ : νE.IsHaarMeasure) (νF : Measure (archGroup F n))
        (_ : νF.IsHaarMeasure) (b a : TI F n) (aE : TI E n) (aF : TI F n), IsBlockElement D n s ∧ ArchSlot D νE νF b a aE aF ∧
        GM.AmpFn μE νE aE ∧ GM.AmpFn μF νF aF ∧ GM.ArchPair σ νE νF aE aF 1 ∧ OComponent μE (s 0) (hs 0) νF a u ≠ 0

def SplitLev : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [_root_.NumberField.IsTotallyComplex F]
    [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)), IsSummand μ V → ∀ v : Pl F, GM.Split E v →
      ∃ (U : Subgroup (Gw n v)) (J : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)), CO U ∧
        U ≤ GLnLocal.integralGL (v.adicCompletion F) n ∧
        ∀ u, CO (J u) ∧ (∀ g, g ∈ U ↔ mapGL n (completionMap v u.1) g ∈ J u) ∧ V ⊓ fixL μ u.1 (J u) ≠ ⊥

def SplitStable : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [_root_.NumberField.IsTotallyComplex F]
    [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ v : Pl F, GM.Split E v → ∀ (U : Subgroup (Gw n v)) (J : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)),
      (∀ u g, g ∈ U ↔ mapGL n (completionMap v u.1) g ∈ J u) →
      (∀ x : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u x ∈ J u) → ∀ u, GM.cmp u (mapGL n (galFin σ v) x) ∈ J u) ∧
      (CO U → U ≤ GLnLocal.integralGL (v.adicCompletion F) n →
        ∃ UE : Subgroup (GL (Fin n) (CompletionsOver E v)), (∀ g, g ∈ UE ↔ ∀ u, GM.cmp u g ∈ J u) ∧
          IsOpen (UE : Set (GL (Fin n) (CompletionsOver E v))) ∧ (UE : Set (GL (Fin n) (CompletionsOver E v))) ⊆ unitSet E n v)

def SplitMatch : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [_root_.NumberField.IsTotallyComplex F]
    [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (v : Pl F) (w : PlacesOver E v), GM.Split E v → ∀ (U : Subgroup (Gw n v)) (J : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)),
      CO U → (∀ u, CO (J u) ∧ ∀ g, g ∈ U ↔ mapGL n (completionMap v u.1) g ∈ J u) →
      ∃ c : ℂ, ∀ ψ : Gw n w.1 → ℂ, Test ψ → (∀ u ∈ J w, ∀ g, ψ (u * g) = ψ g ∧ ψ (g * u) = ψ g) →
        GM.MatchAt σ v c
          (GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) w ψ))
          (fun g => ψ (mapGL n (completionMap v w.1) g)) ∧
        Test (GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) w ψ)) ∧
        Test (fun g => ψ (mapGL n (completionMap v w.1) g)) ∧
        (∀ y : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u y ∈ J u) → ∀ g,
          GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) w ψ) (y * g) =
          GM.prodFn (Function.update (fun u : PlacesOver E v => ((J u : Set (Gw n u.1)).indicator 1 : Gw n u.1 → ℂ)) w ψ) g) ∧
        ∀ y ∈ U, ∀ g, ψ (mapGL n (completionMap v w.1) (y * g)) = ψ (mapGL n (completionMap v w.1) g)

def InertData : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [_root_.NumberField.IsTotallyComplex F]
    [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ)), IsSummand μ V → ∀ v : Pl F, ¬ GM.Split E v →
      ∃ (J : ∀ u : PlacesOver E v, Subgroup (Gw n u.1)) (χ : ∀ u : PlacesOver E v, Gw n u.1 → ℂ) (f : Gw n v → ℂ)
        (UE : Subgroup (GL (Fin n) (CompletionsOver E v))) (UF : Subgroup (Gw n v)),
        (∀ u, CO (J u) ∧ IsChr (J u) (χ u) ∧ RankOne μ V u.1 (J u) (χ u) ∧ V ⊓ eigL μ u.1 (J u) (χ u) ≠ ⊥) ∧
        (∀ x : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u x ∈ J u) → (∀ u, GM.cmp u (mapGL n (galFin σ v) x) ∈ J u) ∧
          ∏ᶠ u : PlacesOver E v, χ u (GM.cmp u (mapGL n (galFin σ v) x)) = ∏ᶠ u : PlacesOver E v, χ u (GM.cmp u x)) ∧
        GM.MatchAt σ v 1 (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) f ∧
        Test (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) ∧ Test f ∧
        IsOpen (UE : Set (GL (Fin n) (CompletionsOver E v))) ∧ (UE : Set (GL (Fin n) (CompletionsOver E v))) ⊆ unitSet E n v ∧
        IsOpen (UF : Set (Gw n v)) ∧ UF ≤ GLnLocal.integralGL (v.adicCompletion F) n ∧
        (∀ y ∈ UE, ∀ g, (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) (y * g) =
          (GM.prodFn fun u : PlacesOver E v => (J u : Set (Gw n u.1)).indicator fun x => conj (χ u x)) g) ∧
        ∀ y ∈ UF, ∀ g, f (y * g) = f g

def OffStable : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [_root_.NumberField.IsTotallyComplex F]
    [_root_.NumberField.IsTotallyComplex E] (σ : E ≃ₐ[F] E), (∀ τ, τ ∈ Subgroup.zpowers σ) → (Module.finrank F E).Prime → ∀ n : ℕ, 0 < n →
    ∀ v : Pl F, (∀ x : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u x ∈ GLnLocal.integralGL (u.1.adicCompletion E) n) →
        ∀ u, GM.cmp u (mapGL n (galFin σ v) x) ∈ GLnLocal.integralGL (u.1.adicCompletion E) n) ∧
      (∀ x : GL (Fin n) (CompletionsOver E v), (∀ u, GM.cmp u x ∈ GLnLocal.iwahori (u.1.adicCompletion E) n) →
        ∀ u, GM.cmp u (mapGL n (galFin σ v) x) ∈ GLnLocal.iwahori (u.1.adicCompletion E) n) ∧
      (∃ U : Subgroup (GL (Fin n) (CompletionsOver E v)), (U : Set (GL (Fin n) (CompletionsOver E v))) = unitSet E n v) ∧
      (∃ U : Subgroup (GL (Fin n) (CompletionsOver E v)), ∀ g, g ∈ U ↔ ∀ u, GM.cmp u g ∈ GLnLocal.iwahori (u.1.adicCompletion E) n) ∧
      ∀ w : Pl E, CO (GLnLocal.integralGL (w.adicCompletion E) n) ∧ CO (GLnLocal.iwahori (w.adicCompletion E) n) ∧
        GLnLocal.iwahori (w.adicCompletion E) n ≤ GLnLocal.integralGL (w.adicCompletion E) n

end UpperTheory.ConvolutionTheory.T
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.GoodEx
theorem UpperTheory.ConvolutionTheory.T.goodEx :
    UpperTheory.ConvolutionTheory.T.GoodEx := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  set S : ℤ := ∑ k : Fin m, ((m : ℤ) + 1 - (k : ℕ)) with hS
  have hS0 : 0 ≤ S := by
    refine Finset.sum_nonneg fun k _ => ?_
    have := k.isLt
    omega
  let ν : Fin (m + 1) → ℤ := fun i => if i = Fin.last m then -S else (m : ℤ) + 1 - (i : ℕ)
  have hlast : ν (Fin.last m) = -S := by simp [ν]
  have hcast : ∀ k : Fin m, ν k.castSucc = (m : ℤ) + 1 - (k : ℕ) := by
    intro k
    have : k.castSucc ≠ Fin.last m := (Fin.castSucc_lt_last k).ne
    simp [ν, this]
  have hne : ∀ i : Fin (m + 1), i ≠ Fin.last m → ν i = (m : ℤ) + 1 - (i : ℕ) := by
    intro i hi
    simp [ν, hi]
  have hpos : ∀ i : Fin (m + 1), i ≠ Fin.last m → 0 < ν i := by
    intro i hi
    rw [hne i hi]
    have := i.isLt
    omega
  have hsum : ∑ i, ν i = 0 := by
    rw [Fin.sum_univ_castSucc, hlast]
    simp only [hcast]
    rw [← hS]
    ring
  have hJ : ∀ J : Finset (Fin (m + 1)), J.Nonempty → Fin.last m ∉ J → 0 < ∑ i ∈ J, ν i := by
    intro J hJ hl
    refine Finset.sum_pos (fun i hi => hpos i ?_) hJ
    rintro rfl
    exact hl hi
  refine ⟨ν, ?_, hsum, ?_⟩
  · intro i j hij
    by_cases hj : j = Fin.last m
    · have hi : i ≠ Fin.last m := by
        rintro rfl
        subst hj
        exact lt_irrefl _ hij
      have h1 := hpos i hi
      have h2 : ν j = -S := by rw [hj, hlast]
      show ν j < ν i
      omega
    · have hi : i ≠ Fin.last m := by
        rintro rfl
        exact absurd (Fin.le_last j) (not_le.mpr hij)
      show ν j < ν i
      rw [hne i hi, hne j hj]
      have : (i : ℕ) < (j : ℕ) := hij
      omega
  · intro J hJne hJu
    by_cases hl : Fin.last m ∈ J
    · have hc : Jᶜ.Nonempty := by
        rw [Finset.nonempty_iff_ne_empty]
        intro h
        exact hJu (by simpa using h)
      have h1 := hJ Jᶜ hc (by simpa using hl)
      have h2 : ∑ i ∈ J, ν i + ∑ i ∈ Jᶜ, ν i = 0 := by
        rw [Finset.sum_add_sum_compl, hsum]
      omega
    · exact (hJ J hJne hl).ne'
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.AmpFin
open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped InnerProductSpace

private theorem exists_pos_eig {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (W V : Submodule ℂ H) (hV : IsClosed (V : Set H)) (hVW : V ≤ W) (A : H →L[ℂ] H) (hA : 0 ≤ A)
    (hAV : ∀ v ∈ V, A v ∈ V) (hc : IsCompactOperator (A ∘L prj W)) (h : ∃ v ∈ V, A v ≠ 0) :
    ∃ x : ℝ, 0 < x ∧ eigIn V A x ≠ ⊥ := by
  have hs : IsSelfAdjoint A := GroundTheory.Automorphic.isSelfAdjoint_of_nonneg hA
  have hcl : V.topologicalClosure = V := hV.submodule_topologicalClosure_eq
  have hPV : ∀ v, prj V v ∈ V := fun v => by
    have h1 : prj V v ∈ V.topologicalClosure := V.topologicalClosure.starProjection_apply_mem v
    rwa [hcl] at h1
  have hPfix : ∀ v ∈ V, prj V v = v := fun v hv =>
    Submodule.starProjection_eq_self_iff.2 (by rw [hcl]; exact hv)
  have hWfix : ∀ v, prj W (prj V v) = prj V v := fun v =>
    Submodule.starProjection_eq_self_iff.2 (W.le_topologicalClosure (hVW (hPV v)))
  have hPs : ContinuousLinearMap.adjoint (prj V) = prj V :=
    (ContinuousLinearMap.isSelfAdjoint_iff'.1 (isSelfAdjoint_starProjection _))
  set B : H →L[ℂ] H := prj V ∘L A ∘L prj V with hB
  have hBc : IsCompactOperator B := by
    have e : B = prj V ∘L ((A ∘L prj W) ∘L prj V) := by
      refine ContinuousLinearMap.ext fun v => ?_
      simp only [hB, ContinuousLinearMap.comp_apply, hWfix]
    rw [e]
    exact (hc.comp_clm (prj V)).clm_comp (prj V)
  have hBs : IsSelfAdjoint B := by
    have h1 := hs.conj_adjoint (prj V)
    rwa [hPs] at h1
  have hBv : ∀ v ∈ V, B v = A v := fun v hv => by
    simp only [hB, ContinuousLinearMap.comp_apply, hPfix v hv, hPfix _ (hAV v hv)]
  obtain ⟨s, b, l, -, hTb₀, hsum, -⟩ := GroundTheory.Automorphic.CompactSelfAdjoint.exists_hilbertBasis_eigenvectors_hasSum hBc hBs
  have hTb : ∀ i, B (b i) = ((l i : ℝ) : ℂ) • b i := fun i => by
    rw [hTb₀ i]
    rfl
  obtain ⟨v, hv, hv0⟩ := h
  obtain ⟨i, hi⟩ : ∃ i, l i ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have h0 : HasSum (fun i => (((l i : ℝ) : ℂ) * ⟪b i, v⟫_ℂ) • b i) (0 : H) := by
      simp only [hcon, Complex.ofReal_zero, zero_mul, zero_smul]
      exact hasSum_zero
    exact hv0 (by rw [← hBv v hv]; exact (hsum v).unique h0)
  have hw0 : b i ≠ 0 := b.orthonormal.ne_zero i
  have hli : ((l i : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hi
  have hwV : b i ∈ V := by
    have h1 : b i = ((l i : ℝ) : ℂ)⁻¹ • B (b i) := by
      rw [hTb i, smul_smul, inv_mul_cancel₀ hli, one_smul]
    rw [h1]
    exact V.smul_mem _ (hPV _)
  have hAw : A (b i) = ((l i : ℝ) : ℂ) • b i := by rw [← hBv _ hwV, hTb i]
  have hpos : 0 < l i := by
    have h1 := ((ContinuousLinearMap.nonneg_iff_isPositive).1 hA).re_inner_nonneg_right (b i)
    have hn : ⟪b i, b i⟫_ℂ = 1 := by
      rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
      simp
    rw [hAw, inner_smul_right, hn] at h1
    simp only [mul_one, RCLike.re_to_complex, Complex.ofReal_re] at h1
    exact lt_of_le_of_ne h1 hi.symm
  refine ⟨l i, hpos, (Submodule.ne_bot_iff _).2 ⟨b i, Submodule.mem_inf.2 ⟨hwV, ?_⟩, hw0⟩⟩
  exact Module.End.mem_eigenspace_iff.2 hAw

theorem UpperTheory.ConvolutionTheory.T.ampFin :
    UpperTheory.ConvolutionTheory.T.AmpFin := by
  intro K _ _ _ n hn μ _ 𝔞
  obtain ⟨hA0, -, -, -⟩ := UpperTheory.ConvolutionTheory.evEx K n hn μ 𝔞
  have hUc : IsCompact (𝔞.U : Set (AdelicGLn.FiniteAdelicGL K n)) :=
    (AdelicGLn.isCompact_integralFiniteGL K n).of_isClosed_subset (𝔞.U.isClosed_of_isOpen 𝔞.isOpen)
      fun _ h => 𝔞.le h
  obtain ⟨m, hm, hC⟩ := (UpperTheory.ConvolutionTheory.Tf.compatEx K n hn).2.1 μ 𝔞.ν
  haveI := hm
  obtain ⟨e, -, he⟩ := UpperTheory.ConvolutionTheory.Tf.prjFix K n μ m 𝔞.U 𝔞.isOpen hUc
  have hAR : RR μ (tens 𝔞.a₀ e) = 𝔞.A := by
    rw [UpperTheory.ConvolutionTheory.Tf.rrTens K n hn μ 𝔞.ν m hC, he]
    rfl
  obtain ⟨hsum, hcusp, hcpt⟩ := opBasics K n μ (tens 𝔞.a₀ e)
  rw [hAR] at hsum hcusp hcpt
  have hs : IsSelfAdjoint 𝔞.A := GroundTheory.Automorphic.isSelfAdjoint_of_nonneg hA0
  refine ⟨fun x hx => ?_, fun V hV hv =>
    exists_pos_eig (cuspidalL2 μ) V hV.closed hV.le 𝔞.A hA0 (hsum V hV) hcpt hv⟩
  have hfd : FiniteDimensional ℂ (eigIn (cuspidalL2 μ) 𝔞.A x) := by
    obtain ⟨S, hS, hf, -⟩ := eigSplit (LL μ) (cuspidalL2 μ) 𝔞.A (isClosed_cuspidalL2 μ) hA0 hcusp hcpt (x / 2) (by linarith)
    by_cases h : eigIn (cuspidalL2 μ) 𝔞.A x = ⊥
    · rw [h]
      infer_instance
    · exact hf x ((hS x).2 ⟨by linarith, h⟩)
  obtain ⟨s, hs', -⟩ := eigSummands (LL μ) {V : Submodule ℂ (LL μ) // IsSummand μ V} (fun i => i.1) (cuspidalL2 μ) 𝔞.A x
    (fun i => i.2.closed) (fun i j hij => Dp.multiplicity_one_cuspidal_spectrum_normOneGL K n μ i.1 j.1 i.2 j.2 fun h => hij (Subtype.ext h))
    (summandsSpan K n μ) hs (fun i => hsum i.1 i.2) hfd
  classical
  refine (s.image Subtype.val).finite_toSet.subset ?_
  rintro V ⟨hV, hne⟩
  exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨⟨V, hV⟩, (hs' _).2 hne, rfl⟩)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.MatchOne
theorem UpperTheory.ConvolutionTheory.T.matchOne :
    UpperTheory.ConvolutionTheory.T.MatchOne := by
  intro F E _ _ _ _ _ σ n v aE bE aF bF
  obtain ⟨⟨aE', bE', aF', bF', mE, mF, hE, hF, hE1, hF1⟩, h2⟩ := UpperTheory.ConvolutionTheory.GM.matchOne F E σ n v
  obtain rfl : aE = aE' := bE.measurable_eq.trans bE'.measurable_eq.symm
  obtain rfl : aF = aF' := bF.measurable_eq.trans bF'.measurable_eq.symm
  exact ⟨mE, mF, hE, hF, hE1, hF1, fun c φ f hM => @h2 _ bE' _ bF' mE mF hE hF hE1 hF1 c φ f hM⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.LevelEx
noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.L1 Formalism.BasicNotions GlobalTheory.PRep GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets
open Formalism.L2.Host UpperTheory.V.Published UpperTheory.CBC
open scoped Classical

namespace UpperTheory.ConvolutionTheory.T

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

private lemma mem_fixL_iff (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K) (J : Subgroup (Gw n w))
    (v : LL μ) : v ∈ fixL μ w J ↔ ∀ g ∈ J, rhoL μ w g v = v := by
  simp [fixL, fixF, rhoL, Submodule.mem_iInf, LinearMap.mem_eqLocus, Subgroup.mem_map]

private lemma co_integral (w : Pl K) : CO (GLnLocal.integralGL (w.adicCompletion K) n) :=
  ⟨GLnLocal.isCompact_integralGL _ n, GLnLocal.isOpen_integralGL _ n⟩

private lemma isChr_one {G : Type} [Group G] [TopologicalSpace G] (J : Subgroup G) : IsChr J (1 : G → ℂ) :=
  ⟨IsLocallyConstant.const (1 : ℂ), fun _ _ => by simp, fun _ _ _ _ => by simp⟩

private lemma exists_local_level (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (V : Submodule ℂ (LL μ))
    (hV : IsSummand μ V) (w : Pl K) :
    ∃ U : Subgroup (Gw n w), CO U ∧ U ≤ GLnLocal.integralGL (w.adicCompletion K) n ∧ V ⊓ fixL μ w U ≠ ⊥ := by
  letI : MeasurableSpace (Gw n w) := borel _
  haveI : BorelSpace (Gw n w) := ⟨rfl⟩
  let P : TopologicalSpace.PositiveCompacts (Gw n w) :=
    { carrier := GLnLocal.integralGL (w.adicCompletion K) n
      isCompact' := GLnLocal.isCompact_integralGL _ n
      interior_nonempty' := by
        rw [(GLnLocal.isOpen_integralGL _ n).interior_eq]
        exact ⟨1, Subgroup.one_mem _⟩ }
  obtain ⟨⟨σ, f, hf0, hfV, hfe⟩, -, -⟩ := occursBasics K n μ V w (Measure.haarMeasure P) hV
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf0 (LinearMap.ext h)
  let U : Subgroup (Gw n w) := stabilizerOf σ.ρ x ⊓ GLnLocal.integralGL (w.adicCompletion K) n
  have hUo : IsOpen (U : Set (Gw n w)) := by
    rw [Subgroup.coe_inf]
    exact (σ.smooth x).inter (GLnLocal.isOpen_integralGL _ n)
  have hUc : IsCompact (U : Set (Gw n w)) :=
    (GLnLocal.isCompact_integralGL _ n).of_isClosed_subset (Subgroup.isClosed_of_isOpen U hUo)
      (by rw [Subgroup.coe_inf]; exact Set.inter_subset_right)
  refine ⟨U, ⟨hUc, hUo⟩, inf_le_right, fun hb => hx ?_⟩
  have hm : f x ∈ V ⊓ fixL μ w U := by
    refine Submodule.mem_inf.2 ⟨hfV x, (mem_fixL_iff μ w U _).2 fun g hg => ?_⟩
    rw [← hfe g x]
    exact congrArg f hg.1
  rw [hb] at hm
  exact (Submodule.mem_bot ℂ).1 hm

end UpperTheory.ConvolutionTheory.T

theorem UpperTheory.ConvolutionTheory.T.levelEx :
    UpperTheory.ConvolutionTheory.T.LevelEx := by
  intro K _ _ n μ _ V hV S hS
  choose U₀ hU₀ hU₀le hU₀ne using fun w : Pl K => exists_local_level μ V hV w
  let J : ∀ w : Pl K, Subgroup (Gw n w) := fun w =>
    if w ∈ S then U₀ w else GLnLocal.integralGL (w.adicCompletion K) n
  have hJin : ∀ w ∈ S, J w = U₀ w := fun w hw => if_pos hw
  have hJout : ∀ w, w ∉ S → J w = GLnLocal.integralGL (w.adicCompletion K) n := fun w hw => if_neg hw
  have hco : ∀ w, CO (J w) := fun w => by
    by_cases hw : w ∈ S
    · rw [hJin w hw]; exact hU₀ w
    · rw [hJout w hw]; exact co_integral w
  have hle : ∀ w, J w ≤ GLnLocal.integralGL (w.adicCompletion K) n := fun w => by
    by_cases hw : w ∈ S
    · rw [hJin w hw]; exact hU₀le w
    · rw [hJout w hw]
  have heig : ∀ w, eigL μ w (J w) 1 = fixL μ w (J w) := fun w =>
    (eigBasic K n μ w (J w) 1 (hco w) (isChr_one _)).2.1
  have hloc : ∀ w, V ⊓ eigL μ w (J w) 1 ≠ ⊥ := fun w => by
    rw [heig w]
    by_cases hw : w ∈ S
    · rw [hJin w hw]; exact hU₀ne w
    · rw [hJout w hw]; exact hS w hw
  have hall := typedEx K n μ V hV J (fun _ => 1) (fun w => ⟨hco w, isChr_one _⟩)
    ((S.finite_toSet.eventually_cofinite_notMem).mono fun w hw => ⟨hJout w hw, rfl⟩) hloc
  refine ⟨J, fun w => ⟨hco w, hle w⟩, fun hb => hall (eq_bot_iff.2 ?_)⟩
  rw [← hb]
  refine le_inf (le_inf inf_le_left ?_) ?_
  · refine inf_le_right.trans (le_iInf₂ fun w hw => (iInf_le _ w).trans ?_)
    rw [heig w, hJout w hw]
  · refine inf_le_right.trans (le_iInf₂ fun w _ => (iInf_le _ w).trans ?_)
    rw [heig w]
end
end
