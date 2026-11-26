module

public import Formalism.LocalToGlobal.InertKernelTheory.AdmissibleEleventhInert
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntAsm
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.JetsModel
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.JetsOrth
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.GlobalOrthonormalBasisFour
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.OneCopyTh1SOfIsom
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.AlgKleinPf
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMIsom
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.BlockFourfoldHOneEqHOne
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntWAPlaces
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.FrLocB

@[expose] public section

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ConjugationFixedClosure
noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension omegaK)

namespace FrFix

variable {p : ℕ} [Fact p.Prime]

theorem not_sq (d : ℕ) (hj : jacobiSym (-(d : ℤ)) p = -1) : ¬ ∃ a : ZMod p, a ^ 2 = -(d : ZMod p) := by
  have hleg : legendreSym p (-(d : ℤ)) = -1 := by rw [jacobiSym.legendreSym.to_jacobiSym]; exact hj
  have hns : ¬ IsSquare (((-(d : ℤ)) : ℤ) : ZMod p) := (legendreSym.eq_neg_one_iff (p := p)).1 hleg
  rintro ⟨a, ha⟩
  apply hns
  refine ⟨a, ?_⟩
  push_cast
  rw [← ha]
  ring

theorem fixed_mem_closure (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p) (hσ : Formalism.InvariantFactorPaths.G7.UnrOK (MaximalUnramifiedExtension p) p σ) (z : MaximalUnramifiedExtension p)
    (hz : σ z = z) : (z : ℂ_[p]) ∈ closure (Set.range fun q : ℚ => (q : ℂ_[p])) := by
  have hp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ‖z‖ hp1
  have hpk : ‖((p : MaximalUnramifiedExtension p) ^ k)‖ = ((p : ℝ) ^ k)⁻¹ := by rw [norm_pow, hσ.2.2.1, inv_pow]
  have hpkpos : (0 : ℝ) < (p : ℝ) ^ k := by positivity
  obtain ⟨w, hw⟩ : ∃ w : MaximalUnramifiedExtension p, w = (p : MaximalUnramifiedExtension p) ^ k * z := ⟨_, rfl⟩
  have hw1 : ‖w‖ ≤ 1 := by
    rw [hw, norm_mul, hpk, inv_mul_le_iff₀ hpkpos, mul_one]
    exact hk.le
  have hσw : σ w = w := by rw [hw, map_mul, map_pow, map_natCast, hz]
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hε' : 0 < ε * ((p : ℝ) ^ k)⁻¹ := by positivity
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one hε' (inv_lt_one_of_one_lt₀ hp1)
  obtain ⟨n, hn⟩ := Formalism.L2.Th1.D.fixedIsLimit (MaximalUnramifiedExtension p) p σ hσ w hw1 hσw j
  refine ⟨((n : ℚ) / (p : ℚ) ^ k : ℚ), ⟨_, rfl⟩, ?_⟩
  have hpk0 : ((p : MaximalUnramifiedExtension p) ^ k) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
  have hq : ((((n : ℚ) / (p : ℚ) ^ k : ℚ)) : ℂ_[p]) = ((((n : ℚ) / (p : ℚ) ^ k : ℚ) : MaximalUnramifiedExtension p) : ℂ_[p]) :=
    (map_ratCast (MaximalUnramifiedExtension p).subtype _).symm
  have e : z - ((((n : ℚ) / (p : ℚ) ^ k : ℚ)) : MaximalUnramifiedExtension p) = ((p : MaximalUnramifiedExtension p) ^ k)⁻¹ * (w - n) := by
    rw [hw]
    push_cast
    field_simp
  rw [hq, ← Subtype.dist_eq, dist_eq_norm, e, norm_mul, norm_inv, hpk, inv_inv]
  calc (p : ℝ) ^ k * ‖w - n‖ ≤ (p : ℝ) ^ k * ((p : ℝ) ^ j)⁻¹ := by gcongr
    _ = (p : ℝ) ^ k * ((p : ℝ)⁻¹) ^ j := by rw [inv_pow]
    _ < (p : ℝ) ^ k * (ε * ((p : ℝ) ^ k)⁻¹) := by gcongr
    _ = ε := by field_simp

end FrFix

theorem conjugation_fixed_closure : FixConj := by
  intro D p _ h5 hj lam ι hι σ hσ y hy
  have hsq : Squarefree D.host.d := (Nat.prime_iff.mp D.host.hyp.2.1).squarefree
  have h4 : D.host.d % 4 = 3 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.discriminant_mod_four D
  obtain ⟨hwm, hws⟩ := Formalism.L2.Th1.D.sqrt_in_unramified_completion D.host.d hsq h4 p h5 (FrFix.not_sq D.host.d hj) ι
  obtain ⟨w, hw⟩ : ∃ w : MaximalUnramifiedExtension p, (w : ℂ_[p]) = ι (omegaK D.host.d) := ⟨⟨_, hwm⟩, rfl⟩
  have hσw : σ w = 1 - w := hws σ hσ w hw
  have hLI := Formalism.L2.KerInert.lamCIota p lam ι hι
  have hlc : ∀ z : D.host.E, lamC lam (D.host.φ₀ z) = ι (D.host.φ₀ z) :=
    fun z => hLI.1 _ (Formalism.MainNotions.Ext.test_vector_mem_schwartz_bruhat D z)
  have hsK : D.host.sqrtMinusD ∈ D.host.K := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrt_mem D
  have hx2 : (D.host.φ₀ D.host.sqrtMinusD) ^ 2 = -(D.host.d : ℂ) := by
    rw [← map_pow, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_sqrtE_sq D, map_neg, map_natCast]
  have hom : (2 * omegaK D.host.d - 1) ^ 2 = -(D.host.d : ℂ) := by
    unfold omegaK
    have hsq : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = (D.host.d : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
    linear_combination (-1 : ℂ) * hsq + (((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2) * Complex.I_sq

  have c2 : ((2 : MaximalUnramifiedExtension p) : ℂ_[p]) = 2 := map_ofNat (MaximalUnramifiedExtension p).subtype 2
  obtain ⟨rK, hrK, hσr⟩ : ∃ rK : MaximalUnramifiedExtension p, (rK : ℂ_[p]) = ι (D.host.φ₀ D.host.sqrtMinusD) ∧ σ rK = -rK := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hx2.trans hom.symm) with h | h
    · refine ⟨2 * w - 1, ?_, ?_⟩
      · rw [h, map_sub, map_mul, map_ofNat, map_one, ← hw]; push_cast; rw [c2]
      · rw [map_sub, map_mul, map_ofNat, map_one, hσw]; ring
    · refine ⟨1 - 2 * w, ?_, ?_⟩
      · rw [h, map_neg, map_sub, map_mul, map_ofNat, map_one, ← hw]; push_cast; rw [c2]; ring
      · rw [map_sub, map_mul, map_ofNat, map_one, hσw]; ring
  have hd0 : (D.host.d : ℂ_[p]) ≠ 0 := by exact_mod_cast (D.host.hyp.2.1).ne_zero
  have hr0 : rK ≠ 0 := by
    intro h
    have h' : ((rK : ℂ_[p])) ^ 2 = 0 := by rw [h]; simp
    rw [hrK, ← map_pow, hx2, map_neg, map_natCast, neg_eq_zero] at h'
    exact hd0 h'

  have h2 : (2 : MaximalUnramifiedExtension p) ≠ 0 := two_ne_zero
  obtain ⟨u, hu⟩ : ∃ u : MaximalUnramifiedExtension p, u = (y + σ y) / 2 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : MaximalUnramifiedExtension p, v = (y - σ y) / (2 * rK) := ⟨_, rfl⟩
  have hσu : σ u = u := by rw [hu, map_div₀, map_add (f := _), hy, map_ofNat]; ring
  have hσv : σ v = v := by
    rw [hv, map_div₀, map_sub, map_mul, hy, hσr, map_ofNat]
    field_simp
    ring
  have hyuv : y = u + v * rK := by
    rw [hu, hv]
    field_simp
    ring
  have cu := FrFix.fixed_mem_closure σ hσ u hσu
  have cv := FrFix.fixed_mem_closure σ hσ v hσv
  have hyc : (y : ℂ_[p]) = (u : ℂ_[p]) + (v : ℂ_[p]) * (rK : ℂ_[p]) := by rw [hyuv]; push_cast; rfl
  refine ⟨?_, ?_⟩
  · have hcont : Continuous fun ab : ℂ_[p] × ℂ_[p] => ab.1 + ab.2 * (rK : ℂ_[p]) := by fun_prop
    have hmem : ((u : ℂ_[p]), (v : ℂ_[p])) ∈ closure ((Set.range fun q : ℚ => (q : ℂ_[p])) ×ˢ
        (Set.range fun q : ℚ => (q : ℂ_[p]))) := by
      rw [closure_prod_eq]; exact ⟨cu, cv⟩
    have hmaps : Set.MapsTo (fun ab : ℂ_[p] × ℂ_[p] => ab.1 + ab.2 * (rK : ℂ_[p]))
        ((Set.range fun q : ℚ => (q : ℂ_[p])) ×ˢ (Set.range fun q : ℚ => (q : ℂ_[p])))
        (Set.range fun x : D.host.K => lamC lam (D.host.φ₀ (x : D.host.E))) := by
      rintro ⟨_, _⟩ ⟨⟨a, rfl⟩, ⟨b, rfl⟩⟩
      refine ⟨(a : D.host.K) + (b : D.host.K) * ⟨D.host.sqrtMinusD, hsK⟩, ?_⟩
      have e : (((a : D.host.K) + (b : D.host.K) * ⟨D.host.sqrtMinusD, hsK⟩ : D.host.K) : D.host.E) =
          (a : D.host.E) + (b : D.host.E) * D.host.sqrtMinusD := by
        push_cast; rfl
      simp only
      rw [e, hlc, hrK, map_add (f := _), map_mul, map_ratCast, map_ratCast, map_add (f := _), map_mul, map_ratCast, map_ratCast]
    have hh := map_mem_closure hcont hmem hmaps
    rw [hyc]
    exact hh
  · intro σp hσp
    have hσc : Continuous σp :=
      AddMonoidHomClass.continuous_of_bound σp 1 (fun z => by rw [hσp.2 z, one_mul])
    have hfixS : closure (Set.range fun q : ℚ => (q : ℂ_[p])) ⊆ {z | σp z = z} :=
      closure_minimal (by rintro _ ⟨q, rfl⟩; exact map_ratCast σp q) (isClosed_eq hσc continuous_id)
    have hu' : σp u = u := hfixS cu
    have hv' : σp v = v := hfixS cv
    have hr' : σp (rK : ℂ_[p]) = -(rK : ℂ_[p]) := by
      have h := hσp.1 ⟨D.host.sqrtMinusD, hsK⟩
      have hc : D.host.conj D.host.sqrtMinusD = -D.host.sqrtMinusD := Formalism.BasicNotions.Examples₂.conj_bE D.host
      change σp (lamC lam (D.host.φ₀ D.host.sqrtMinusD)) =
        lamC lam (D.host.φ₀ (D.host.conj D.host.sqrtMinusD)) at h
      rw [hc, hlc, hlc, map_neg, map_neg, ← hrK] at h
      exact h
    rw [hyc, map_add (f := _), map_mul, hu', hv', hr', hyuv, map_add (f := _), map_mul, hσu, hσv, hσr]
    push_cast
    ring

end Formalism.L2.KerInert
end
end

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMConj
noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

namespace MMConj

theorem not_sq_padic (d p : ℕ) [Fact p.Prime] (hj : jacobiSym (-(d : ℤ)) p = -1) (y : ℚ_[p]) :
    y ^ 2 ≠ -(d : ℚ_[p]) := by
  intro hy
  have hleg : legendreSym p (-(d : ℤ)) = -1 := by rw [jacobiSym.legendreSym.to_jacobiSym]; exact hj
  have hns : ¬ IsSquare (((-(d : ℤ)) : ℤ) : ZMod p) := (legendreSym.eq_neg_one_iff (p := p)).1 hleg
  have hnd : ¬ p ∣ d := by
    intro hd
    apply hns
    have h0 : ((d : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff d p).2 hd
    refine ⟨0, ?_⟩
    push_cast
    rw [h0]
    simp
  have hdn : ‖(d : ℚ_[p])‖ = 1 := by
    have h1 : ‖(d : ℚ_[p])‖ ≤ 1 := by exact_mod_cast Padic.norm_int_le_one (p := p) (d : ℤ)
    have h2 : ¬ ‖(d : ℚ_[p])‖ < 1 := by rw [Padic.norm_natCast_lt_one_iff]; exact hnd
    linarith [not_lt.1 h2]
  have hy1 : ‖y‖ ≤ 1 := by
    have h3 : ‖y‖ ^ 2 = 1 := by rw [← norm_pow, hy, norm_neg, hdn]
    nlinarith [norm_nonneg y]
  set z : ℤ_[p] := ⟨y, hy1⟩ with hz
  have hz2 : z ^ 2 = -(d : ℤ_[p]) := by
    apply Subtype.ext
    simp only [hz, PadicInt.coe_neg, PadicInt.coe_natCast]
    exact hy
  apply hns
  refine ⟨PadicInt.toZMod z, ?_⟩
  have h4 := congrArg (PadicInt.toZMod (p := p)) hz2
  rw [map_pow, map_neg, map_natCast] at h4
  push_cast
  rw [← h4]
  ring

theorem exists_aut_neg (d p : ℕ) [Fact p.Prime] (hj : jacobiSym (-(d : ℤ)) p = -1) (β : PadicAlgCl p)
    (hβ : β ^ 2 = -(d : PadicAlgCl p)) : ∃ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, τ β = -β := by
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C (-(d : ℚ_[p]))) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => not_sq_padic d p hj b hb)
  have hmon : (Polynomial.X ^ 2 - Polynomial.C (-(d : ℚ_[p]))).Monic :=
    Polynomial.monic_X_pow_sub_C _ two_ne_zero
  have h1 := minpoly.eq_of_irreducible_of_monic (x := β) hirr (by simp [hβ]) hmon
  have h2 := minpoly.eq_of_irreducible_of_monic (x := -β) hirr (by simp [hβ]) hmon
  obtain ⟨τ, hτ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ_[p]) (E := PadicAlgCl p)).1 (h2.symm.trans h1)
  exact ⟨τ, hτ⟩

theorem aut_norm {p : ℕ} [Fact p.Prime] (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : PadicAlgCl p) :
    ‖τ x‖ = ‖x‖ := by
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
  exact (spectralNorm_eq_of_equiv τ x).symm

theorem aut_cont {p : ℕ} [Fact p.Prime] (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    Continuous ((τ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p) :=
  (AddMonoidHomClass.isometry_of_norm ((τ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p)
    (fun x => aut_norm τ x)).continuous

def extC {p : ℕ} [Fact p.Prime] (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : ℂ_[p] →+* ℂ_[p] :=
  UniformSpace.Completion.mapRingHom ((τ : PadicAlgCl p ≃+* PadicAlgCl p) : PadicAlgCl p →+* PadicAlgCl p) (aut_cont τ)

theorem extC_coe {p : ℕ} [Fact p.Prime] (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : PadicAlgCl p) :
    extC τ (x : ℂ_[p]) = ((τ x : PadicAlgCl p) : ℂ_[p]) :=
  UniformSpace.Completion.mapRingHom_coe _ _

theorem extC_norm {p : ℕ} [Fact p.Prime] (τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (y : ℂ_[p]) :
    ‖extC τ y‖ = ‖y‖ := by
  refine UniformSpace.Completion.induction_on y ?_ ?_
  · exact isClosed_eq (continuous_norm.comp UniformSpace.Completion.continuous_map) continuous_norm
  · intro a
    rw [extC_coe, PadicComplex.norm_extends, PadicComplex.norm_extends, aut_norm]

theorem phi0_algebraic (D : D7) (x : D.host.E) : D.host.φ₀ x ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.host.φ₀.toRatAlgHom

end MMConj


open MMConj in
theorem conjugation_extension_inert : ConjExt := by
  intro D p _ _ hj lam
  let L : D.host.E →+* ℂ_[p] := lam.comp (D.host.φ₀.codRestrict Qbar.toSubring (fun z => phi0_algebraic D z))
  have hL : ∀ x, L x = lamC lam (D.host.φ₀ x) := by
    intro x
    simp only [lamC, dif_pos (phi0_algebraic D x)]
    rfl
  set b : D.host.E := D.host.sqd with hbdef
  have hb2 : b ^ 2 = -(D.host.d : D.host.E) := Formalism.BasicNotions.Examples₂.bE_sq D.host
  have hcb : D.host.conj b = -b := Formalism.BasicNotions.Examples₂.conj_bE D.host
  obtain ⟨β, hβ⟩ : ∃ β : PadicAlgCl p, β ^ 2 = -(D.host.d : PadicAlgCl p) := IsAlgClosed.exists_pow_nat_eq _ two_pos
  obtain ⟨τ, hτ⟩ := exists_aut_neg D.host.d p hj β hβ
  refine ⟨extC τ, ?_, extC_norm τ⟩
  have e1 : L b ^ 2 = -(D.host.d : ℂ_[p]) := by rw [← map_pow, hb2, map_neg, map_natCast]
  have e2 : (β : ℂ_[p]) ^ 2 = -(D.host.d : ℂ_[p]) := by
    rw [PadicComplex.coe_eq, ← map_pow, hβ, map_neg, map_natCast]
  have hLb : L b = (β : ℂ_[p]) ∨ L b = -(β : ℂ_[p]) := sq_eq_sq_iff_eq_or_eq_neg.1 (e1.trans e2.symm)
  have hσβ : extC τ (β : ℂ_[p]) = -(β : ℂ_[p]) := by
    rw [extC_coe, hτ, PadicComplex.coe_eq, PadicComplex.coe_eq, map_neg]
  have hσLb : extC τ (L b) = L (D.host.conj b) := by
    rw [hcb, map_neg]
    rcases hLb with h | h
    · rw [h, hσβ]
    · rw [h, map_neg, hσβ, neg_neg]
  let f : D.host.E →ₐ[ℚ] ℂ_[p] := ((extC τ).comp L).toRatAlgHom
  let g : D.host.E →ₐ[ℚ] ℂ_[p] := (L.comp (D.host.conj : D.host.E →+* D.host.E)).toRatAlgHom
  have hfg : b ∈ AlgHom.equalizer f g := hσLb
  have hK : (D.host.K).toSubalgebra ≤ AlgHom.equalizer f g := by
    have hK' : D.host.K = IntermediateField.adjoin ℚ {b} := rfl
    rw [hK', IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic b)]
    exact Algebra.adjoin_le (Set.singleton_subset_iff.2 hfg)
  intro x
  rw [← hL, ← hL]
  exact hK x.2

end Formalism.L2.KerInert
end
end

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntUnit
noncomputable section

namespace Formalism.L2.KerInert.IntegralUnitSubstitution

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.MainNotions.Ext Formalism.MainNotions.Ext.CutA

variable {p : ℕ} [Fact p.Prime]

theorem expMv_pi {σ : Type} (F : MvPowerSeries σ ℂ_[p]) : Formalism.MainNotions.TaylorLogMetric.expMv F = PI.FglPhSplit.expMv F := rfl

theorem expMv_subst_eq {σ : Type} {F : MvPowerSeries σ ℂ_[p]} (hF : MvPowerSeries.constantCoeff F = 0) :
    Formalism.MainNotions.TaylorLogMetric.expMv F = PowerSeries.subst F (PowerSeries.exp ℂ_[p]) := by
  rw [expMv_pi]; exact PI.FglPhSplit.Wk.expMv_eq_subst hF

theorem cc_expMv {σ : Type} {F : MvPowerSeries σ ℂ_[p]} (hF : MvPowerSeries.constantCoeff F = 0) :
    MvPowerSeries.constantCoeff (Formalism.MainNotions.TaylorLogMetric.expMv F) = 1 := by
  rw [expMv_subst_eq hF, PI.FglShared.constantCoeff_subst_of_zero hF]
  simp

theorem expMv_zero' {σ : Type} : Formalism.MainNotions.TaylorLogMetric.expMv (0 : MvPowerSeries σ ℂ_[p]) = 1 := by
  rw [expMv_subst_eq (map_zero _)]
  simp [PowerSeries.subst_zero_eq_C_constantCoeff]

theorem expMv_add'' {σ : Type} {f g : MvPowerSeries σ ℂ_[p]} (hf : MvPowerSeries.constantCoeff f = 0)
    (hg : MvPowerSeries.constantCoeff g = 0) :
    Formalism.MainNotions.TaylorLogMetric.expMv (f + g) = Formalism.MainNotions.TaylorLogMetric.expMv f * Formalism.MainNotions.TaylorLogMetric.expMv g :=
  PI.FglShared.expMv_add' hf hg

theorem expMv_sum {σ ι : Type} (s : Finset ι) (f : ι → MvPowerSeries σ ℂ_[p])
    (hf : ∀ i, MvPowerSeries.constantCoeff (f i) = 0) :
    Formalism.MainNotions.TaylorLogMetric.expMv (∑ i ∈ s, f i) = ∏ i ∈ s, Formalism.MainNotions.TaylorLogMetric.expMv (f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using (expMv_zero' (σ := σ) (p := p))
  · intro a s ha ih
    have h0 : MvPowerSeries.constantCoeff (∑ i ∈ s, f i) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; exact Finset.sum_eq_zero fun i _ => hf i
    rw [Finset.sum_insert ha, Finset.prod_insert ha, expMv_add'' (hf a) h0, ih]

theorem msubst_psubst {τ υ : Type} {a : MvPowerSeries τ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    {b : τ → MvPowerSeries υ ℂ_[p]} (hb : MvPowerSeries.HasSubst b) (f : PowerSeries ℂ_[p]) :
    MvPowerSeries.subst b (PowerSeries.subst a f) = PowerSeries.subst (MvPowerSeries.subst b a) f := by
  have h1 : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => ha)
  exact MvPowerSeries.subst_comp_subst_apply h1 hb f

theorem subst_expMv {σ τ : Type} {b : σ → MvPowerSeries τ ℂ_[p]} (hb : MvPowerSeries.HasSubst b)
    {F : MvPowerSeries σ ℂ_[p]} (hF : MvPowerSeries.constantCoeff F = 0)
    (hb0 : MvPowerSeries.constantCoeff (MvPowerSeries.subst b F) = 0) :
    MvPowerSeries.subst b (Formalism.MainNotions.TaylorLogMetric.expMv F) = Formalism.MainNotions.TaylorLogMetric.expMv (MvPowerSeries.subst b F) := by
  rw [expMv_subst_eq hF, expMv_subst_eq hb0, msubst_psubst hF hb]

section G
variable (g : G1 p)

theorem cc_l : PowerSeries.constantCoeff g.l = 0 := by
  unfold G1.l flog
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
  simp

theorem cc_lg {σ : Type} {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.constantCoeff (g.lg a) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero ha _ (cc_l g)

theorem cc_pt (hOk : g.Ok) {σ : Type} {y : MvPowerSeries σ ℂ_[p]} (hy : MvPowerSeries.constantCoeff y = 0) :
    MvPowerSeries.constantCoeff (g.pt y) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero hy _ hOk.2.2.1

theorem lg_pt (hOk : g.Ok) {σ : Type} {y : MvPowerSeries σ ℂ_[p]} (hy : MvPowerSeries.constantCoeff y = 0) :
    g.lg (g.pt y) = y := by
  unfold G1.lg G1.pt
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hOk.2.2.1)
    (PowerSeries.HasSubst.of_constantCoeff_zero hy), hOk.2.2.2, PowerSeries.subst_X
    (PowerSeries.HasSubst.of_constantCoeff_zero hy)]

theorem subst_lg {σ τ : Type} {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0)
    {b : σ → MvPowerSeries τ ℂ_[p]} (hb : MvPowerSeries.HasSubst b) :
    MvPowerSeries.subst b (g.lg a) = g.lg (MvPowerSeries.subst b a) :=
  msubst_psubst ha hb _

theorem add_eq_subst (hOk : g.Ok) {σ : Type} {a b : MvPowerSeries σ ℂ_[p]}
    (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) :
    g.add a b = MvPowerSeries.subst ![a, b] (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) := by
  have hs : MvPowerSeries.HasSubst ![a, b] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simpa)
  have hX : ∀ i : Fin 2, MvPowerSeries.constantCoeff (Xv i : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := fun i => by simp
  have h0 : MvPowerSeries.constantCoeff (g.lg (Xv 0) + g.lg (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    rw [map_add (f := _), cc_lg g (hX 0), cc_lg g (hX 1), add_zero]
  unfold G1.add G1.pt
  rw [msubst_psubst h0 hs, ← MvPowerSeries.coe_substAlgHom hs, map_add (f := _), MvPowerSeries.coe_substAlgHom hs,
    subst_lg g (hX 0) hs, subst_lg g (hX 1) hs, MvPowerSeries.subst_X hs, MvPowerSeries.subst_X hs]
  rfl

theorem mulBy_eq_subst {σ : Type} (c : ℂ_[p]) {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    g.mulBy c a = MvPowerSeries.subst (fun _ : Unit => a) (g.mulBy c (Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
  have hs : MvPowerSeries.HasSubst (fun _ : Unit => a) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => ha)
  have hX : MvPowerSeries.constantCoeff (Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := by simp
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.C c * g.lg (Xv ()) : MvPowerSeries Unit ℂ_[p]) = 0 := by
    rw [map_mul, cc_lg g hX, mul_zero]
  unfold G1.mulBy G1.pt
  rw [msubst_psubst h0 hs, ← MvPowerSeries.coe_substAlgHom hs, map_mul, MvPowerSeries.coe_substAlgHom hs,
    MvPowerSeries.subst_C, subst_lg g hX hs, MvPowerSeries.subst_X hs]

theorem integral_zero {σ : Type} : IntegralMv (0 : MvPowerSeries σ ℂ_[p]) := fun n => by
  simp [IsIntP]

theorem lin_partial (hOk : g.Ok) {r : ℕ} (c : Fin r → ℂ_[p])
    (hc : ∀ j, IntegralMv (g.mulBy (c j) (Xv ()) : MvPowerSeries Unit ℂ_[p]))
    (ha : IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])) (s : Finset (Fin r)) :
    MvPowerSeries.constantCoeff (g.pt (∑ j ∈ s, MvPowerSeries.C (c j) * g.lg (Xv j)) : MvPowerSeries (Fin r) ℂ_[p]) = 0 ∧
      IntegralMv (g.pt (∑ j ∈ s, MvPowerSeries.C (c j) * g.lg (Xv j)) : MvPowerSeries (Fin r) ℂ_[p]) := by
  classical
  have hX : ∀ j : Fin r, MvPowerSeries.constantCoeff (Xv j : MvPowerSeries (Fin r) ℂ_[p]) = 0 := fun j => by simp
  have hT : ∀ t : Finset (Fin r),
      MvPowerSeries.constantCoeff (∑ j ∈ t, MvPowerSeries.C (c j) * g.lg (Xv j) : MvPowerSeries (Fin r) ℂ_[p]) = 0 := by
    intro t
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_eq_zero fun j _ => by rw [map_mul, cc_lg g (hX j), mul_zero]
  refine Finset.induction_on s ?_ ?_
  · rw [Finset.sum_empty]
    unfold G1.pt
    rw [PowerSeries.subst_zero_of_constantCoeff_zero hOk.2.2.1]
    exact ⟨map_zero _, integral_zero⟩
  · intro j t hj ih
    have hm0 : MvPowerSeries.constantCoeff (g.mulBy (c j) (Xv j) : MvPowerSeries (Fin r) ℂ_[p]) = 0 := by
      unfold G1.mulBy
      exact cc_pt g hOk (by rw [map_mul, cc_lg g (hX j), mul_zero])
    have hmI : IntegralMv (g.mulBy (c j) (Xv j) : MvPowerSeries (Fin r) ℂ_[p]) := by
      rw [mulBy_eq_subst g (c j) (hX j)]
      exact IntegralOrthonormalChange.integral_subst _ (fun _ => hX j) (fun _ => fun n => by
        rw [MvPowerSeries.coeff_X]; split_ifs <;> simp [IsIntP]) (hc j)
    have e : (∑ j' ∈ insert j t, MvPowerSeries.C (c j') * g.lg (Xv j') : MvPowerSeries (Fin r) ℂ_[p]) =
        g.lg (g.mulBy (c j) (Xv j)) + g.lg (g.pt (∑ j' ∈ t, MvPowerSeries.C (c j') * g.lg (Xv j'))) := by
      rw [Finset.sum_insert hj, lg_pt g hOk (hT t)]
      unfold G1.mulBy
      rw [lg_pt g hOk (by rw [map_mul, cc_lg g (hX j), mul_zero])]
    rw [e]
    refine ⟨cc_pt g hOk (by rw [map_add (f := _), cc_lg g hm0, cc_lg g ih.1, add_zero]), ?_⟩
    change IntegralMv (g.add _ _)
    rw [add_eq_subst g hOk hm0 ih.1]
    exact IntegralOrthonormalChange.integral_subst _ (fun i => by fin_cases i <;> simp [hm0, ih.1])
      (fun i => by fin_cases i <;> simp [hmI, ih.2]) ha

theorem lin_cc_int (hOk : g.Ok) {r : ℕ} (c : Fin r → ℂ_[p])
    (hc : ∀ j, IntegralMv (g.mulBy (c j) (Xv ()) : MvPowerSeries Unit ℂ_[p]))
    (ha : IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p])) :
    MvPowerSeries.constantCoeff (g.lin c (fun j => Xv j) : MvPowerSeries (Fin r) ℂ_[p]) = 0 ∧
      IntegralMv (g.lin c (fun j => Xv j) : MvPowerSeries (Fin r) ℂ_[p]) :=
  lin_partial g hOk c hc ha Finset.univ

theorem lg_lin (hOk : g.Ok) {r : ℕ} (c : Fin r → ℂ_[p]) :
    g.lg (g.lin c (fun j => Xv j) : MvPowerSeries (Fin r) ℂ_[p]) =
      ∑ j, MvPowerSeries.C (c j) * g.lg (Xv j : MvPowerSeries (Fin r) ℂ_[p]) := by
  unfold G1.lin
  refine lg_pt g hOk ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  exact Finset.sum_eq_zero fun j _ => by rw [map_mul, cc_lg g (by simp), mul_zero]

theorem inv_ePhi1 (he1 : PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1) {σ : Type}
    {y : MvPowerSeries σ ℂ_[p]} (hy : MvPowerSeries.constantCoeff y = 0) :
    (PowerSeries.subst y (ePhi1 g.lam g.abelian₂ g.C g.wq))⁻¹ = Formalism.MainNotions.TaylorLogMetric.expMv (g.phAt y) := by
  set e := ePhi1 g.lam g.abelian₂ g.C g.wq with he
  have hE : PI.FglPhSplit.expMv (PI.FglShared.logS e) = e := PI.FglShared.expMv_logS he1
  have hph : g.ph = -PI.FglShared.logS e := by
    show -logMv e = _
    rfl
  have hl0 : MvPowerSeries.constantCoeff (PI.FglShared.logS e) = 0 := PI.FglShared.constantCoeff_logS e
  have hsy : PowerSeries.HasSubst y := PowerSeries.HasSubst.of_constantCoeff_zero hy
  have hphy0 : MvPowerSeries.constantCoeff (g.phAt y) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hy _ (ph0 g)
  have h1 : PowerSeries.subst y e = Formalism.MainNotions.TaylorLogMetric.expMv (-(g.phAt y)) := by
    conv_lhs => rw [← hE]
    rw [← PI.FglShared.expMv_subst' hy hl0, expMv_pi]
    congr 1
    unfold G1.phAt
    rw [hph, ← PowerSeries.coe_substAlgHom hsy, map_neg, neg_neg]
  have hn0 : MvPowerSeries.constantCoeff (-(g.phAt y)) = 0 := by rw [map_neg, hphy0, neg_zero]
  have hne : MvPowerSeries.constantCoeff (Formalism.MainNotions.TaylorLogMetric.expMv (-(g.phAt y))) ≠ 0 := by
    rw [cc_expMv hn0]; exact one_ne_zero
  rw [h1]
  symm
  rw [MvPowerSeries.eq_inv_iff_mul_eq_one hne, ← expMv_add'' hphy0 hn0, add_neg_cancel, expMv_zero']

theorem ePh_eq (he1 : PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1) (hp : p ≠ 2) (r : ℕ) :
    ePh g.lam g.abelian₂ g.C g.wq r = Formalism.MainNotions.TaylorLogMetric.expMv (∑ i : Fin r, g.phAt (Xv i)) := by
  unfold ePh
  rw [if_neg hp, expMv_sum Finset.univ (fun i : Fin r => (g.phAt (Xv i) : MvPowerSeries (Fin r) ℂ_[p]))
    (fun i => PowerSeries.constantCoeff_subst_eq_zero (by simp) _ (ph0 g))]
  exact Finset.prod_congr rfl fun i _ => inv_ePhi1 g he1 (by simp)

end G

theorem core (D : D7) (g : G1 p) (hOk : g.Ok) (hp : p ≠ 2)
    (he : ∀ α ∈ OKp D g.lam, IntegralMv (g.mulBy α.1 (Xv ()) : MvPowerSeries Unit ℂ_[p]))
    (ha : IntegralMv (g.add (Xv 0) (Xv 1) : MvPowerSeries (Fin 2) ℂ_[p]))
    (hOK : ∀ a : 𝓞 D.host.K, Nat.Coprime (Algebra.norm ℤ a).natAbs p →
      Simeq (g.phAt (g.mulBy (tauK D g.lam (a : D.host.K)) (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (tauK D g.lam (a : D.host.K) * tauKc D g.lam (a : D.host.K)) * g.phAt (Xv ())))
    (hB : Simeq (g.be (g.add (Xv 0) (Xv 1)) (Xv 2) : MvPowerSeries (Fin 3) ℂ_[p])
      (g.be (Xv 0) (Xv 2) + g.be (Xv 1) (Xv 2)))
    (he1 : PowerSeries.constantCoeff (ePhi1 g.lam g.abelian₂ g.C g.wq) = 1)
    (r : ℕ) (M : Fin r → Fin r → ℂ_[p] × ℂ_[p]) (hM : ∀ i j, M i j ∈ OKp D g.lam)
    (hu : ∀ j j', ∑ i, M i j * (M i j').swap = if j = j' then 1 else 0) :
    ∃ S : Fin r → MvPowerSeries (Fin r) ℂ_[p],
      (∀ i, MvPowerSeries.constantCoeff (S i) = 0) ∧ (∀ i, IntegralMv (S i)) ∧
      (∀ i, PowerSeries.subst (S i) g.l =
        ∑ j, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) (M i j).1 *
          PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries (Fin r) ℂ_[p]) g.l) ∧
      ∃ V : MvPowerSeries (Fin r) ℂ_[p], IntegralMv V ∧
        ePh g.lam g.abelian₂ g.C g.wq r = MvPowerSeries.subst S (ePh g.lam g.abelian₂ g.C g.wq r) * V := by
  classical

  have hn : ∀ α ∈ OKp D g.lam, Simeq (g.phAt (g.mulBy α.1 (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C (α.1 * α.2) * g.phAt (Xv ())) := by
    refine phNormOfUnits_holds p g (OKp D g.lam) hOk hp (okpTwo_holds D p g.lam) (okpSwap_holds D p g.lam)
      (fun α hα β hβ => okp_add D g.lam α β hα hβ) (fun α hα β hβ => okp_mul D g.lam α β hα hβ)
      he ha ((okpTrace_holds D) p g.lam) ((okpNorm_holds D) p g.lam) ((okpTwoUnits2_holds D) p g.lam hp) hB ?_
    intro α hα h1 h2
    have hc := (okpUnitsDense_holds D) p g.lam hp α hα h1 h2
    refine phNormClosed_holds p g _ hOk ?_ ?_ α hc
    · rintro _ ⟨a, -, rfl⟩
      exact he _ (subset_closure ⟨a, rfl⟩)
    · rintro _ ⟨a, hcop, rfl⟩
      exact hOK a hcop
  have hb := beConjOfNorm_holds p g (OKp D g.lam) hOk (okpSwap_holds D p g.lam)
    (fun α hα β hβ => okp_add D g.lam α β hα hβ) he ha ((okpNorm_holds D) p g.lam)
    ((okpTwoUnits_holds D) p g.lam hp) hn hB
  let de : Fin r → Fin r → ℂ_[p] × ℂ_[p] := fun j i => M i j
  have hG := phGramG_holds p g (OKp D g.lam) hOk (okpSwap_holds D p g.lam) he ha hn hb hB (Fin r) r de
    (fun j i => hM i j)
  rw [gramUnitEq_holds p g hOk r de (fun j j' => hu j j')] at hG

  let S : Fin r → MvPowerSeries (Fin r) ℂ_[p] := fun i => g.lin (fun j => (M i j).1) (fun j => Xv j)
  have hSI : ∀ i, MvPowerSeries.constantCoeff (S i) = 0 ∧ IntegralMv (S i) := fun i =>
    lin_cc_int g hOk (fun j => (M i j).1) (fun j => he _ (hM i j)) ha
  have hS : MvPowerSeries.HasSubst S := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => (hSI i).1)
  refine ⟨S, fun i => (hSI i).1, fun i => (hSI i).2, fun i => ?_, ?_⟩
  · exact lg_lin g hOk (fun j => (M i j).1)
  ·
    have hPh : g.PhOn de = ∑ i : Fin r, g.phAt (S i) := rfl
    have hX0 : ∀ i : Fin r, MvPowerSeries.constantCoeff (Xv i : MvPowerSeries (Fin r) ℂ_[p]) = 0 := fun i => by simp
    have hsum0 : MvPowerSeries.constantCoeff (∑ i : Fin r, g.phAt (Xv i) : MvPowerSeries (Fin r) ℂ_[p]) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; exact Finset.sum_eq_zero fun i _ => PowerSeries.constantCoeff_subst_eq_zero (hX0 i) _ (ph0 g)
    have hsumS : MvPowerSeries.subst S (∑ i : Fin r, g.phAt (Xv i) : MvPowerSeries (Fin r) ℂ_[p]) =
        ∑ i : Fin r, g.phAt (S i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← MvPowerSeries.coe_substAlgHom hS, map_sum, MvPowerSeries.coe_substAlgHom hS]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold G1.phAt
      rw [msubst_psubst (hX0 i) hS, MvPowerSeries.subst_X hS]
    have hS0 : MvPowerSeries.constantCoeff (∑ i : Fin r, g.phAt (S i) : MvPowerSeries (Fin r) ℂ_[p]) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]; exact Finset.sum_eq_zero fun i _ => PowerSeries.constantCoeff_subst_eq_zero (hSI i).1 _ (ph0 g)
    obtain ⟨hG0, hGI⟩ := hG
    rw [hPh] at hG0 hGI
    have hd0 : MvPowerSeries.constantCoeff (∑ i : Fin r, g.phAt (Xv i) - ∑ i : Fin r, g.phAt (S i) :
        MvPowerSeries (Fin r) ℂ_[p]) = 0 := by rw [map_sub, hsum0, hS0, sub_zero]
    refine ⟨Formalism.MainNotions.TaylorLogMetric.expMv (∑ i : Fin r, g.phAt (Xv i) - ∑ i : Fin r, g.phAt (S i)), ?_, ?_⟩
    ·
      have hmul : Formalism.MainNotions.TaylorLogMetric.expMv (∑ i : Fin r, g.phAt (Xv i) - ∑ i : Fin r, g.phAt (S i)) *
          Formalism.MainNotions.TaylorLogMetric.expMv (∑ i : Fin r, g.phAt (S i) - ∑ i : Fin r, g.phAt (Xv i)) = 1 := by
        rw [← expMv_add'' hd0 hG0]
        rw [show (∑ i : Fin r, g.phAt (Xv i) - ∑ i : Fin r, g.phAt (S i)) +
            (∑ i : Fin r, g.phAt (S i) - ∑ i : Fin r, g.phAt (Xv i)) = (0 : MvPowerSeries (Fin r) ℂ_[p]) by ring]
        exact expMv_zero'
      exact PI.FglShared.int_of_mul_eq_one (fun α => hGI α) (cc_expMv hG0) hmul
    · rw [ePh_eq g he1 hp r, subst_expMv hS hsum0 (by rw [hsumS]; exact hS0), hsumS,
        ← expMv_add'' hS0 hd0]
      congr 1
      ring

theorem unitSubstLoc_of (hC : CcPrime) (hE : EndIntInertAll) (hN : PhNormOKInertAll) (hB : BiaddInertAll) :
    UnitSubstLoc := by
  intro D cc δ hcI hδ p _ hp5 hjac lam C wq hM hW r M hMO hMu
  obtain ⟨cc', δ', hcI', hδ', hcop, hL⟩ := hC D cc δ hcI hδ p hjac
  have hp : p ≠ 2 := by omega
  have hl0 : PowerSeries.constantCoeff (flog (C • wModel lam (lamOf D cc δ)) wq) = 0 := by
    unfold flog
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    simp
  have hl1 : PowerSeries.coeff 1 (flog (C • wModel lam (lamOf D cc δ)) wq) = 1 := by
    rw [Dict.formal_logarithm_agree p _ wq hW]
    exact (Formalism.L2.Th1.A.logSpec ℂ_[p] (C • wModel lam (lamOf D cc δ))).2.1
  have hu : IsUnit (PowerSeries.coeff 1 (flog (C • wModel lam (lamOf D cc δ)) wq)) := by
    rw [hl1]; exact isUnit_one
  let g : G1 p := ⟨lam, lamOf D cc δ, C, wq,
    (flog (C • wModel lam (lamOf D cc δ)) wq).substInvOfIsUnit hu⟩
  have hOk : g.Ok := ⟨Formalism.MainNotions.GL3Theta.IsModel.toU hM, hW, PowerSeries.constantCoeff_substInvOfIsUnit _ hu,
    PowerSeries.subst_substInvOfIsUnit_right _ hl0 hu⟩
  have hA : At D cc' δ' g := ⟨hcI', hcop, hδ', hL, hOk⟩
  exact core D g hOk hp (hE D p cc' δ' g hA hp5 hjac) (addInt_holds D p cc' δ' g hA).1
    (hN D p cc' δ' g hA hp5 hjac) (hB D p cc' δ' g hA hp5 hjac).1 (ePhiOne_holds D p cc' δ' g hA) r M hMO hMu

end Formalism.L2.KerInert.IntegralUnitSubstitution

namespace Formalism.L2.KerInert

theorem unitSubstLoc_of (hC : CcPrime) (hE : EndIntInertAll) (hN : PhNormOKInertAll) (hB : BiaddInertAll) :
    UnitSubstLoc :=
  IntegralUnitSubstitution.unitSubstLoc_of hC hE hN hB

theorem unitSubstLoc_of_model (hE : EndIntInertAll) (hN : PhNormOKInertAll) (hB : BiaddInertAll) : UnitSubstLoc :=
  unitSubstLoc_of curve_ideal_prime hE hN hB

end Formalism.L2.KerInert
end
end

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.MMFour
noncomputable section

namespace Formalism.L2.KerInert.MMFour

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.RestC Formalism.L2.KerInert.IntTens

section Mat

variable {n n' r : ℕ} {R : Type*} [CommRing R]

def AB (A : Matrix (Fin r) (Fin r) R) : Matrix (Fin (n' * n * r)) (Fin (n' * n * r)) R :=
  fun q q' => if ((eIdx n' n r).symm q).1 = ((eIdx n' n r).symm q').1 then
    A ((eIdx n' n r).symm q).2 ((eIdx n' n r).symm q').2 else 0

theorem AB_eIdx (A : Matrix (Fin r) (Fin r) R) (P P' : Fin n' × Fin n) (x y : Fin r) :
    AB (n' := n') (n := n) A (eIdx n' n r (P, x)) (eIdx n' n r (P', y)) = if P = P' then A x y else 0 := by
  simp [AB]

def eSw (n' n r : ℕ) : Fin r × (Fin n' × Fin n) ≃ Fin (n' * n * r) :=
  (Equiv.prodComm _ _).trans (eIdx n' n r)

theorem AB_eq_reindex (A : Matrix (Fin r) (Fin r) R) :
    AB (n' := n') (n := n) A =
      Matrix.reindex (eSw n' n r) (eSw n' n r) (Matrix.blockDiagonal fun _ : Fin n' × Fin n => A) := by
  ext q q'
  obtain ⟨⟨P, x⟩, rfl⟩ := (eIdx n' n r).surjective q
  obtain ⟨⟨P', y⟩, rfl⟩ := (eIdx n' n r).surjective q'
  rw [AB_eIdx]
  simp [eSw, Matrix.blockDiagonal_apply]

theorem det_AB (A : Matrix (Fin r) (Fin r) R) :
    (AB (n' := n') (n := n) A).det = A.det ^ (n' * n) := by
  rw [AB_eq_reindex, Matrix.det_reindex_self, Matrix.det_blockDiagonal, Finset.prod_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

theorem sum_eIdx {M : Type*} [AddCommMonoid M] (F : Fin (n' * n * r) → M) :
    ∑ q, F q = ∑ P : Fin n' × Fin n, ∑ x : Fin r, F (eIdx n' n r (P, x)) := by
  rw [← (eIdx n' n r).sum_comp, Fintype.sum_prod_type]

theorem gram_AB (A : Matrix (Fin r) (Fin r) R) (g : Fin (n' * n * r) → Fin (n' * n * r) → R) (g0 : Fin r → Fin r → R)
    (hg : ∀ P x P' y, g (eIdx n' n r (P, x)) (eIdx n' n r (P', y)) = if P = P' then g0 x y else 0)
    (σ : R →+* R) (hA : ∀ a c, ∑ x, ∑ y, A a x * g0 x y * σ (A c y) = if a = c then 1 else 0) :
    ∀ i j, ∑ m, ∑ k, AB (n' := n') (n := n) A i m * g m k * σ (AB (n' := n') (n := n) A j k) =
      if i = j then 1 else 0 := by
  classical
  intro i j
  obtain ⟨⟨P, a⟩, rfl⟩ := (eIdx n' n r).surjective i
  obtain ⟨⟨P', c⟩, rfl⟩ := (eIdx n' n r).surjective j
  have hσ : ∀ (c : Prop) [Decidable c] (x : R), σ (if c then x else 0) = if c then σ x else 0 := by
    intro c _ x; split_ifs <;> simp
  rw [sum_eIdx]
  simp_rw [sum_eIdx (fun k => _ * g _ k * σ (AB A _ k)), AB_eIdx, hg, hσ]
  simp only [ite_mul, mul_ite, zero_mul, mul_zero, (eIdx n' n r).injective.eq_iff, Prod.mk.injEq]
  by_cases h : P = P'
  · subst h; simp [hA]
  · simp [h]

end Mat

section GlobalTheory

variable {D : D7} {N N' n n' m m' : ℕ} (eR : Fin N' ≃ Fin n' × Fin m') (eC : Fin N ≃ Fin n × Fin m)
variable {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Λ : AddSubgroup ℂ)
  (C : WeierstrassCurve.VariableChange ℂ_[p]) (wq : PowerSeries ℂ_[p])

def atLogVA {r : ℕ} {NN NN' : ℕ} (v : Fin r → (D.what₂.Tau × Fin NN' × Fin NN → ℂ_[p])) :
    D.what₂.Tau × Fin NN' × Fin NN → MvPowerSeries (Fin r) ℂ_[p] :=
  fun k => ∑ i, algebraMap ℂ_[p] (MvPowerSeries (Fin r) ℂ_[p]) (((C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) * v i k) *
      PowerSeries.subst (MvPowerSeries.X i) (flog (C • wModel lam Λ) wq)

theorem atLogVA_hasSubst {r NN NN' : ℕ} (v : Fin r → (D.what₂.Tau × Fin NN' × Fin NN → ℂ_[p])) :
    MvPowerSeries.HasSubst (atLogVA lam Λ C wq v) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  intro k
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [atLogVA, map_sum, map_mul]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [cc_psubst' (MvPowerSeries.constantCoeff_X i) (cc_flog _ wq), mul_zero]

theorem atLogV_eq {r NN NN' : ℕ} (v : Fin r → (D.what₂.Tau × Fin NN' × Fin NN → ℂ_[p]))
    (F : MvPowerSeries (D.what₂.Tau × Fin NN' × Fin NN) ℂ_[p]) :
    atLogV D lam Λ C wq v F = MvPowerSeries.substAlgHom (atLogVA_hasSubst lam Λ C wq v) F := by
  rw [MvPowerSeries.coe_substAlgHom]; rfl

theorem atLogV_prod {r NN NN' : ℕ} (v : Fin r → (D.what₂.Tau × Fin NN' × Fin NN → ℂ_[p]))
    (F : Fin n' → Fin n → MvPowerSeries (D.what₂.Tau × Fin NN' × Fin NN) ℂ_[p]) :
    atLogV D lam Λ C wq v (∏ I, ∏ J, F I J) = ∏ I, ∏ J, atLogV D lam Λ C wq v (F I J) := by
  simp only [atLogV_eq, map_prod]

theorem atLogVA_blk {r : ℕ} (v : Fin r → (D.what₂.Tau × Fin m' × Fin m → ℂ_[p]))
    (v₄ : Fin (n' * n * r) → (D.what₂.Tau × Fin N' × Fin N → ℂ_[p]))
    (hv₄ : ∀ P i I J k, v₄ (eIdx n' n r (P, i)) (blkIdx D eR eC I J k) = if P = (I, J) then v i k else 0)
    (I : Fin n') (J : Fin n) (k : D.what₂.Tau × Fin m' × Fin m) :
    atLogVA lam Λ C wq v₄ (blkIdx D eR eC I J k) =
      MvPowerSeries.rename (idxK r I J) (atLogVA lam Λ C wq v k) := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [atLogVA, map_sum, map_mul, AlgHom.commutes]
  rw [sum_eIdx, Finset.sum_eq_single (I, J)]
  · refine Finset.sum_congr rfl fun k' _ => ?_
    rw [rename_psubst _ (MvPowerSeries.constantCoeff_X k'), MvPowerSeries.rename_X, hv₄, if_pos rfl]
    rfl
  · intro P _ hne
    refine Finset.sum_eq_zero fun k' _ => ?_
    rw [hv₄, if_neg hne]
    simp
  · simp

theorem atLogV_rename {r : ℕ} (v : Fin r → (D.what₂.Tau × Fin m' × Fin m → ℂ_[p]))
    (v₄ : Fin (n' * n * r) → (D.what₂.Tau × Fin N' × Fin N → ℂ_[p]))
    (hv₄ : ∀ P i I J k, v₄ (eIdx n' n r (P, i)) (blkIdx D eR eC I J k) = if P = (I, J) then v i k else 0)
    (I : Fin n') (J : Fin n) (F : MvPowerSeries (D.what₂.Tau × Fin m' × Fin m) ℂ_[p]) :
    atLogV D lam Λ C wq v₄ (MvPowerSeries.rename (blkIdx D eR eC I J) F) =
      MvPowerSeries.rename (idxK r I J) (atLogV D lam Λ C wq v F) := by
  show MvPowerSeries.subst (atLogVA lam Λ C wq v₄) _ =
    MvPowerSeries.rename (idxK r I J) (MvPowerSeries.subst (atLogVA lam Λ C wq v) F)
  rw [MvPowerSeries.rename_eq_subst, MvPowerSeries.rename_eq_subst,
    MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.HasSubst.X_comp _) (atLogVA_hasSubst lam Λ C wq _),
    MvPowerSeries.subst_comp_subst_apply (atLogVA_hasSubst lam Λ C wq v) (MvPowerSeries.HasSubst.X_comp _)]
  congr 1
  funext k
  rw [Function.comp_apply, MvPowerSeries.subst_X (atLogVA_hasSubst lam Λ C wq _), ← MvPowerSeries.rename_eq_subst]
  exact atLogVA_blk eR eC lam Λ C wq v v₄ hv₄ I J k

def v4 {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ_[p]) (b : Fin r → Matrix (Fin m') (Fin m) D.host.E)
    (q : Fin (n' * n * r)) (k : D.what₂.Tau × Fin N' × Fin N) : ℂ_[p] :=
  ∑ j, AB (n' := n') (n := n) A q j * lamC lam (embT D k.1 (bB (D := D) eR eC b j k.2.1 k.2.2))

theorem four_block_vector_entry {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ_[p]) (b : Fin r → Matrix (Fin m') (Fin m) D.host.E)
    (v : Fin r → (D.what₂.Tau × Fin m' × Fin m → ℂ_[p]))
    (hv : ∀ i k, v i k = ∑ j, A i j * lamC lam (embT D k.1 (b j k.2.1 k.2.2)))
    (P : Fin n' × Fin n) (i : Fin r) (I : Fin n') (J : Fin n) (k : D.what₂.Tau × Fin m' × Fin m) :
    v4 eR eC lam A b (eIdx n' n r (P, i)) (blkIdx D eR eC I J k) = if P = (I, J) then v i k else 0 := by
  classical
  have hb : ∀ P' x, bB (D := D) eR eC b (eIdx n' n r (P', x)) = sglB eR eC P'.1 P'.2 (b x) := fun P' x => by
    simp [bB]
  unfold v4
  rw [sum_eIdx]
  simp only [AB_eIdx, hb, blkIdx, sglB_apply, Equiv.apply_symm_apply]
  rw [Finset.sum_eq_single (I, J)]
  · by_cases h : P = (I, J)
    · simp [h, hv]
    · simp [h]
  · intro P' _ hne
    refine Finset.sum_eq_zero fun x _ => ?_
    have : ¬ (I = P'.1 ∧ J = P'.2) := fun h => hne (by rw [h.1, h.2])
    simp [this, lamC_zero]
  · simp

end GlobalTheory

def eOne (k : ℕ) : Fin k ≃ Fin k × Fin 1 := (finCongr (Nat.mul_one k).symm).trans finProdFinEquiv.symm

theorem lamC_phi_zero (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) :
    lamC lam (D.host.φ₀ (((0 : D.host.K)) : D.host.E)) = 0 := by
  simp [lamC_zero]

theorem isLocONB_blk (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : ℂ_[p] →+* ℂ_[p]) {r : ℕ}
    (v : Fin r → (D.what₂.Tau × Fin 1 × Fin 1 → ℂ_[p]))
    (hv : IsLocONB D p lam (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 1) (Formalism.MainNotions.StandardLatticesGL3.stdL D 1)) σ v) :
    ∃ (A : Matrix (Fin r) (Fin r) ℂ_[p]) (b : Fin r → Matrix (Fin 1) (Fin 1) D.host.E),
      (∀ i k, v i k = ∑ j, A i j * lamC lam (embT D k.1 (b j k.2.1 k.2.2))) ∧
      IsLocONB D p lam (YYl D (Formalism.MainNotions.StandardLatticesGL3.stdL D 2) (Formalism.MainNotions.StandardLatticesGL3.stdL D 2)) σ
        (v4 (eOne 2) (eOne 2) lam A b) := by
  classical
  obtain ⟨b, A, hloc, hAint, hdet, hgram, hvb⟩ := hv
  refine ⟨A, b, hvb, bB (eOne 2) (eOne 2) b, AB A, locBasis_bB (eOne 2) (eOne 2) p b hloc, ?_, ?_, ?_,
    fun i k => rfl⟩
  · intro i j
    unfold AB
    split_ifs
    · exact hAint _ _
    · exact ⟨by unfold IsIntP; simp, subset_closure ⟨0, lamC_phi_zero D lam⟩⟩
  · rw [det_AB, norm_pow, hdet, one_pow]
  · refine gram_AB A _ (fun x y => lamC lam (D.host.φ₀ ((hYY D (b x) (b y) : D.host.K) : D.host.E))) ?_ σ hgram
    intro P x P' y
    rw [bB_eIdx, bB_eIdx, hYY_sglB]
    by_cases h : P = P'
    · subst h; simp
    · have : ¬ (P.1 = P'.1 ∧ P.2 = P'.2) := fun h' => h (Prod.ext h'.1 h'.2)
      rw [if_neg this, if_neg h, lamC_phi_zero]

theorem fourProd_main : FourProd := by
  intro D cc δ B hcc hδ p _ hp5 hin lam σ r v hσ hv H
  have hp2 : p ≠ 2 := by omega
  obtain ⟨A, b, hvb, hv₄⟩ := isLocONB_blk D lam σ v hv
  refine ⟨2 * 2 * r, v4 (eOne 2) (eOne 2) lam A b, hv₄, ?_⟩
  intro s hs C wq hC hW
  have hfun : U D B.tor s (B.thZero 2 2) = fun z => ∏ I, ∏ J,
      U D B.tor (prjB (eOne 2) (eOne 2) I J s) (B.thZero 1 1) (blkPt D (eOne 2) (eOne 2) I J z) :=
    funext (U_tensPow (eOne 2) (eOne 2) B.tor B.thMM s)
  have hH := fun I J => H _ (torsB (eOne 2) (eOne 2) B.tor p I J s hs)
  rw [hfun, pSer_blk (eOne 2) (eOne 2) lam taylor_product_over_blocks _ (fun I J => (hH I J).1), atLogV_prod]
  simp_rw [atLogV_rename (eOne 2) (eOne 2) lam _ C wq v _ (four_block_vector_entry (eOne 2) (eOne 2) lam A b v hvb)]
  rw [ePh_blk lam _ C wq hp2 r]
  rw [← Finset.prod_mul_distrib]
  simp_rw [← Finset.prod_mul_distrib, ← map_mul]
  exact integralMv_prod _ _ fun I _ => integralMv_prod _ _ fun J _ =>
    integralMv_rename _ ((hH I J).2 C wq hC hW)

end Formalism.L2.KerInert.MMFour

namespace Formalism.L2.KerInert

theorem four_products_from_one : FourProd := MMFour.fourProd_main

end Formalism.L2.KerInert
end
end

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.ThFourIntOf
noncomputable section

namespace Formalism.L2.KerInert

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

theorem thFourInt_of (hA : OneCopyLoc) (hB : LocInv) (hC : FourProd) (hD : GlobONB) (hE : AlgZero) : ThFourInt := by
  intro D cc δ B hcc hδ p _ hp hin lam s hs
  obtain ⟨σ, r, v, hσ, hv, hint⟩ := hA D cc δ B hcc hδ p hp hin lam
  obtain ⟨r₄, v₄, hv₄, hint₄⟩ := hC D cc δ B hcc hδ p hp hin lam σ r v hσ hv
    (fun s1 hs1 => ⟨hE D cc δ B hcc hδ p hp hin 1 1 s1 hs1, hint s1 hs1⟩)
  obtain ⟨rb, b, hb, hon, hloc⟩ := hD D p hp hin lam
  refine ⟨rb, b, hb, hon, ?_⟩
  intro C wq hC hwq
  exact hB D cc δ hcc hδ p hp hin lam σ hσ 2 2 _ r₄ rb v₄ _ _ hv₄ (hloc σ hσ) (hint₄ s hs) C wq hC hwq

end Formalism.L2.KerInert
end
end

section -- merged from Formalism.LocalToGlobal.InertKernelTheory.IntegralInertOfApproxBasis
section -- merged from Formalism.LocalToGlobal.InertKernelTheory.IntegralInertOfWeakApprox
section -- merged from Formalism.LocalToGlobal.InertKernelTheory.IntegralInertOfWeakApproxTheta
namespace Formalism.L2.KerInert

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem genus_one_witt_exists : GenusOneWittExists := ModelP.genus_one_witt_exists_of (GenusOneDatumExistence.genus_one_datum_exists Sigma.invAlg')

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem unit_substitution_local : UnitSubstLoc :=
  unitSubstLoc_of_model (ModelP.endIntInertAll_of endomorphisms_integral_inert genus_one_witt_exists)
    (ModelP.phNormOKInertAll_of phi_norm_inert_prime endomorphisms_integral_inert genus_one_witt_exists)
    (ModelP.biaddInertAll_of (Dict.biaddInert_of (Sigma.sigmaCurveInert_of Sigma.invAlg' Sigma.secondEisensteinAlgebraic))
      genus_one_witt_exists)




end Formalism.L2.KerInert
end

namespace Formalism.L2.KerInert

def WeakApproxAndOrthonormalBases : Prop := WAPlaces ∧ OneCopyOrth ∧ IsomONB

variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem integral_inert_of_weakApprox (h : WeakApproxAndOrthonormalBases) : IntInert :=
  intInert_of combination_fact pairing_fact (weakApprox_of h.1) pullback_torsion pullback_fact AlgP.algebraic_fact_kernels
    power_series_linearity pairs_standard_at_p (basisInv_of_loc unit_substitution_local) tensor_matrix_units_fact
    (thFourInt_of (oneCopyLoc_of_isom h.2.2 AlgP.zero_value_algebraic) (locInv_of unit_substitution_local) four_products_from_one
      (MMOnb.globONB_of h.2.1) AlgP.zero_value_algebraic)


end Formalism.L2.KerInert
end

namespace Formalism.L2.KerInert

theorem isomONB_ofLB (hLB : LocBasisMM) : IsomONB :=
  isomONB_of_facts conjugation_extension_inert hLB rational_coordinates conjugation_fixed_closure


variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem integral_inert_of_approx_basis (hWA : WAPlaces) (hLB : LocBasisMM) : IntInert :=
  integral_inert_of_weakApprox ⟨hWA, one_theta_orthonormal, isomONB_ofLB hLB⟩

end Formalism.L2.KerInert
end

namespace Formalism.L2.KerInert


variable [Fact _root_.Formalism.L2.Th1.CM.CM2] in
theorem kernels_integral_inert : IntInert := integral_inert_of_approx_basis weak_approximation_places local_orthonormal_basis

end Formalism.L2.KerInert
