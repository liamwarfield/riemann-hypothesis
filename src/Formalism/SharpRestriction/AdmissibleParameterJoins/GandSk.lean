module

public import Formalism.SharpRestriction.GrowthBounds.CornerGLContinuity
public import Formalism.SharpRestriction.GlobalTheoremInputs
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces

@[expose] public section

section -- merged from Formalism.SharpRestriction.AdmissibleParameterJoins.GandSk
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField

private theorem hH_hP (D : D7) (p : ℕ) (hp : p.Prime) (hc : IsResidueClassZero D p) :
    ∃ h : Nat.Coprime p 2, D.R.hH (D.R.iota (hP D p)) =
      hcl D.R.e (ZMod.unitOfCoprime p (Nat.Coprime.pow_right (D.R.e + 2) h)) := by
  have hp2 : p ≠ 2 := by
    rintro rfl
    have h2 : D.host.cls 2 = PrimeClass.ram2 := Formalism.BasicNotions.primeClass_two D.host.toHostRaw
    have hc' : D.host.cls 2 = PrimeClass.inertClass := hc
    rw [h2] at hc'
    cases hc'
  have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr hp2
  refine ⟨hcop, ?_⟩
  have hN : ¬ p ∣ D.host.condN := Formalism.BasicNotions.not_dvd_conductor_of_inert hp (show D.host.cls p = PrimeClass.inertClass from hc)
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  obtain ⟨P, hPm, hPl⟩ : ∃ P : Ideal (𝓞 D.host.E), P.IsMaximal ∧ P.LiesOver (Ideal.span {(p : ℤ)}) := by
    first
    | exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral _
    | exact Ideal.exists_maximal_ideal_liesOver_of_isIntegral _ _
    | exact Ideal.exists_ideal_liesOver_maximal_of_isIntegral _
    | (obtain ⟨Q, hQm, hQc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E)
          (Ideal.span {(p : ℤ)}) (by simp)
       exact ⟨Q, hQm, ⟨hQc.symm⟩⟩)
  haveI : P.IsPrime := hPm.isPrime
  obtain ⟨⟨σ, hσ⟩, -, -, -⟩ := D.host.der.frob p hN P
  have hmem : D.host.galE σ ∈ frobSet D p := ⟨P, inferInstance, hPl, σ, hσ, rfl⟩
  obtain ⟨P', hP'p, hP'l, σ', hσ', hgal⟩ := Classical.epsilon_spec ⟨_, hmem⟩
  obtain ⟨-, -, h3, -⟩ := D.host.der.frob p hN P'
  obtain ⟨-, -, v, hv, hvh⟩ := h3 σ' hσ'
  unfold hP
  simp only [Formalism.HC.Frame.iota_iotaInv]
  rw [← hgal, show ZMod.unitOfCoprime p (Nat.Coprime.pow_right (D.R.e + 2) hcop) = v from
    Units.ext (by rw [ZMod.coe_unitOfCoprime, hv])]
  exact hvh

theorem two_readings_of_Frobenius (D : D7) : Formalism.MainNotions.CornerGLContinuity.FrobeniusClassCompatibility D := by
  intro p hp hc
  obtain ⟨h2, hh⟩ := hH_hP D p hp hc
  refine ⟨fun h => ?_, ?_⟩
  · subst h
    exact absurd h2 (by decide)
  unfold Formalism.MainNotions.GlobalTheoryTheory.hOf
  split_ifs with hcond
  rw [Formalism.BasicNotions.iotaH_iotaHInv, ← hh]
  rfl

end Formalism.MainNotions.J

end
end

section -- merged from Formalism.SharpRestriction.AdmissibleParameterJoins.NandDIVb
section -- merged from Formalism.SharpRestriction.AdmissibleParameterJoins.NandDIVa
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

theorem injective_of_scalars {ι V W : Type*} [DecidableEq ι] [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (S : ι → Submodule ℂ V) (hS : DirectSum.IsInternal S)
    (A : V →ₗ[ℂ] W) (B : W →ₗ[ℂ] V)
    (h : ∀ σ, S σ ≠ ⊥ → ∃ lam : ℂ, lam ≠ 0 ∧ ∀ f ∈ S σ, B (A f) = lam • f) :
    Function.Injective A := by
  classical
  have h' : ∀ σ, ∃ lam : ℂ, lam ≠ 0 ∧ ∀ f ∈ S σ, B (A f) = lam • f := by
    intro σ
    by_cases hσ : S σ = ⊥
    · refine ⟨1, one_ne_zero, fun f hf => ?_⟩
      rw [hσ, Submodule.mem_bot] at hf
      simp [hf]
    · exact h σ hσ
  choose c hc0 hc using h'
  let _ := hS.chooseDecomposition
  have key : ∀ v : V, ∀ k, ((DirectSum.decompose S (B (A v)) k : S k) : V) =
      c k • ((DirectSum.decompose S v k : S k) : V) := by
    intro v
    induction v using DirectSum.Decomposition.inductionOn S with
    | zero => intro k; simp
    | @homogeneous i m =>
      intro k
      have hm : B (A (m : V)) ∈ S i := by
        rw [hc i _ m.2]; exact (S i).smul_mem _ m.2
      by_cases hik : i = k
      · subst hik
        rw [DirectSum.decompose_of_mem_same S hm, DirectSum.decompose_of_mem_same S m.2, hc i _ m.2]
      · rw [DirectSum.decompose_of_mem_ne S hm hik, DirectSum.decompose_of_mem_ne S m.2 hik, smul_zero]
    | add a b ha hb =>
      intro k
      simp only [map_add (f := _), DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, smul_add, ha k, hb k]
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro v hv
  have hz : DirectSum.decompose S v = 0 := by
    ext k
    have := key v k
    rw [hv, map_zero, DirectSum.decompose_zero] at this
    simp only [DirectSum.zero_apply, ZeroMemClass.coe_zero] at this ⊢
    exact (smul_eq_zero.mp this.symm).resolve_left (hc0 k)
  exact (DirectSum.decompose S).injective (by rw [hz, DirectSum.decompose_zero])

end Formalism.MainNotions.J

end
end

noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

theorem theta_injective_of_scalars (D : D7) (h42 : Formalism.MainNotions.SumRepresentations.Conclusion42 D) (hI : Rows.IsotInternal D.what₂)
    (i : D.nd.Loc) (hj : D.nd.j i ∈ SizeData₂.lifts D) :
    Function.Injective (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) := by
  have hj' := Finset.mem_Icc.mp hj
  exact injective_of_scalars (D.what₂.isot (D.nd.j i)) (hI _ hj'.1 hj'.2) _ (D.what₂.thetaP (D.nd.mu i) (D.nd.j i))
    (fun σ hσ => let ⟨lam, h0, hl⟩ := (h42 i σ hσ).1.1; ⟨(lam : ℂ), by exact_mod_cast h0.ne', hl⟩)

end Formalism.MainNotions.J

end
end
