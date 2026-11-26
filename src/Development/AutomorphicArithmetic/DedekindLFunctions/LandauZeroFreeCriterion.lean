module

public import Mathlib

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.DedekindLFunctions.CharFamily
open scoped ArithmeticFunction.vonMangoldt
open Complex

noncomputable section

namespace Deduction

def ramp (f : ℕ → ℂ) (y : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊y⌋₊ + 1), (Λ n : ℂ) * f n * ((max (y / n - 1) 0 : ℝ) : ℂ)


open Classical in
def Gchi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (y : ℝ) : ℂ :=
  if χ = 1 then
    ramp (fun n => χ n) y - ((y * Real.log y : ℝ) : ℂ) + (((1 + Real.eulerMascheroniConstant) * y : ℝ) : ℂ)
  else
    ramp (fun n => χ n) y + (y : ℂ) * (deriv (DirichletCharacter.LFunction χ) 1 / DirichletCharacter.LFunction χ 1)

def G (y : ℝ) : ℝ :=
  (ramp (fun _ => 1) y).re - y * Real.log y + (1 + Real.eulerMascheroniConstant) * y

structure CharFamily where
  ι : Type
  [fin : Fintype ι]
  N : ι → ℕ
  [nz : ∀ i, NeZero (N i)]
  χ : ∀ i, DirichletCharacter ℂ (N i)
  a : ι → ℝ
  a_pos : ∀ i, 0 < a i
  adm : ∀ i, N i = 1 ∨ χ i ≠ 1

attribute [instance] CharFamily.fin CharFamily.nz

def Gm (F : CharFamily) (y : ℝ) : ℝ := ∑ i, F.a i * (Gchi (F.χ i) y).re

def ZeroFree (F : CharFamily) (θ : ℝ) : Prop :=
  ∀ i, ∀ s : ℂ, θ < s.re → DirichletCharacter.LFunction (F.χ i) s ≠ 0

def WindowHyp (F : CharFamily) (θ δ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ Y₀ : ℝ, ∃ Y : ℝ, Y₀ ≤ Y ∧ ∃ R : ℝ → ℝ,
    MeasureTheory.IntegrableOn (fun y => R y * y ^ (-θ - 1)) (Set.Icc Y (Y ^ (1 + δ))) ∧
    (∀ y ∈ Set.Icc Y (Y ^ (1 + δ)), 0 ≤ R y ∧ Gm F y ≤ R y) ∧
    ∫ y in Set.Icc Y (Y ^ (1 + δ)), R y * y ^ (-θ - 1) ≤ Y ^ η

end Deduction

end
end

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace Deduction

def gm (F : CharFamily) (u : ℝ) : ℝ := Gm F (Real.exp u)

def zeroSet (F : CharFamily) : Set ℂ :=
  {ρ | 0 < ρ.re ∧ ∃ i, DirichletCharacter.LFunction (F.χ i) ρ = 0 ∨
    DirichletCharacter.LFunction (F.χ i) ((starRingEnd ℂ) ρ) = 0}

structure PoleData (g : ℝ → ℝ) (Φ : ℂ → ℂ) (Z : Set ℂ) : Prop where
  meas : Measurable g
  growth : ∃ C : ℝ, ∀ u : ℝ, 0 ≤ u → |g u| ≤ C * Real.exp (2 * u)
  laplace : ∀ s : ℂ, 2 < s.re → Φ s = ∫ u in Ioi (0 : ℝ), (g u : ℂ) * cexp (-s * u)
  pos : ∀ ρ ∈ Z, 0 < ρ.re
  diff : DifferentiableOn ℂ Φ ({s : ℂ | 0 < s.re} \ Z)
  iso : ∀ z : ℂ, 0 < z.re → ∀ᶠ w in 𝓝[≠] z, w ∉ Z
  pole : ∀ ρ ∈ Z, ∃ c : ℂ, c ≠ 0 ∧ (ρ.im = 0 → 0 < c.re ∧ c.im = 0) ∧
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h ρ ∧ ∀ᶠ s in 𝓝[≠] ρ, Φ s = c / (s - ρ) + h s

def WindowHypU (g : ℝ → ℝ) (θ δ : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∀ U₀ : ℝ, ∃ U : ℝ, U₀ ≤ U ∧ ∃ R : ℝ → ℝ,
    IntegrableOn (fun u => R u * Real.exp (-θ * u)) (Icc U ((1 + δ) * U)) ∧
    (∀ u ∈ Icc U ((1 + δ) * U), 0 ≤ R u ∧ g u ≤ R u) ∧
    ∫ u in Icc U ((1 + δ) * U), R u * Real.exp (-θ * u) ≤ Real.exp (η * U)

open Classical

end Deduction

end
