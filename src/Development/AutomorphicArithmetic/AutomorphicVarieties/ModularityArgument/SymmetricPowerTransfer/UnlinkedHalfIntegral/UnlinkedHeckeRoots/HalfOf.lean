module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.ROrdAway
public import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.CyclicCharacterEigen.CoefZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeProjectionEigenform
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftFourierCoefficients
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupCosetDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetRepresentatives
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FundamentalDomainIntegralCentralInvariance
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftConductor
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftLocalType
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftHeckeEigenvalues
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftWhittakerExpansion
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewformLiftRapidDecay
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.PrimCj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.SharedDedup_Mod_retr

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.GoodHalf
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.SelfAdj
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt)
open scoped NumberField.AdeleRing ValuativeRel ComplexConjugate
open Ad3 Ad3.R

namespace UpperTheory.V.Z.Sym.Unl

theorem selfAdj : SelfAdj := by
  intro k N _ hk χ hχ g p hp hpN
  have hB := GlobalTheory.T.global_rankin_selberg_basic_facts
  have hE := Ad3P.sEig k N hk χ g
  obtain ⟨hF, hEig⟩ := hE
  obtain ⟨ω, hω⟩ := GlobalTheory.T.newform_lift_existence hB N χ
  obtain ⟨hsign, φ, hL⟩ := GlobalTheory.T.newform_lift_level hB k N χ g.f g.a hF hEig.2.1 ω hω
  have hOmL := GlobalTheory.T.newform_lift_conductor hB k N χ hχ hsign ω hω
  have hHk := GlobalTheory.T.newform_lift_hecke_eigenvalues hB GlobalTheory.T.hecke_coset_representatives GlobalTheory.T.congruence_subgroup_coset_decomposition (GlobalTheory.T.newform_lift_conductor hB) (GlobalTheory.T.newform_lift_level hB)
    (GlobalTheory.T.newform_lift_level_character hB) (GlobalTheory.T.newform_lift_local_type hB) k N hk χ hχ g.f g.a hF hEig ω φ hω hL
  have hW := GlobalTheory.T.newform_lift_whittaker_expansion k N hk χ hχ g.f g.a hF hEig ω φ hω hL
  have hb := GlobalTheory.T.newform_lift_rapid_decay hB k N hk χ hχ g.f g.a hF hEig ω φ hω hL
  obtain ⟨μ, 𝓕, mK, 𝓓, hS⟩ := GlobalTheory.T.fundamental_domain_invariance_of_description GlobalTheory.T.fundamental_domain_description
  have hG1 := GlobalTheory.T.central_character_integral_properties GlobalTheory.T.fundamental_domain_integral_central_invariance
  obtain ⟨v, hv⟩ := hB.2.2.1 p hp
  have hnd : ¬pOf v ∣ N := by rwa [hv]
  obtain ⟨C, hC⟩ := hb.1
  have hφ0 : φ ≠ 0 := by
    intro h0
    have h1 := hW.2.2.2 (-1)
    rw [h0, GlobalTheory.CompanionTheory.RSEigen.wh_zero] at h1
    exact GlobalTheory.CompanionTheory.RSEigen.wr_ne k h1.symm
  have hpr := GlobalTheory.CompanionTheory.RSEigen.pr_self_ne hS hG1 (ω := ω) hL.cont hb.1 hL.left hL.cen hφ0
  have hone : ∀ x : G2, cdet 1 x = 1 := by
    intro x
    simp [Ad3.R.cdet, GroundTheory.Global.HeckeCharacter.toIdele_apply]
  have hPr : GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.Pr μ 𝓕 φ 1 1 1 ≠ 0 := by
    simpa [GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.Pr, GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.Fn, hone, GlobalTheory.CompanionTheory.RSEigen.pr] using hpr
  have hloc1 : ∀ u, localChar (1 : HeckeCharacter ℚ) v u = 1 := by
    intro u
    ext
    simp [GroundTheory.Automorphic.GodementSection.coe_localChar,
      GroundTheory.Global.HeckeCharacter.localComponent_apply, GroundTheory.Global.HeckeCharacter.toIdele_apply]
  have hunr1 : IsUnramifiedChar (localChar (1 : HeckeCharacter ℚ) v) :=
    isUnramifiedChar_iff.2 (fun u _ => hloc1 u)
  have hstd := (hB.1 v).1
  obtain ⟨ϖ, B, hR⟩ := (GlobalTheory.T.congruence_subgroup_coset_decomposition (Qv v) (localAdelicChar ℚ v) hstd).1
  have key := GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.eig_relation (φ := φ) (ω := ω) (c := 1) (μ := μ) (𝓕 := 𝓕) (C := C)
    hL.cont hC hL.left hL.cen (by simp)
    (fun F hF hFb hFL hFC h => (hG1 μ 𝓕 mK 𝓓 hS F hF hFb hFL).1 hFC h) hS.vol
    (v := v) (hB.1 v).2.2.2.2.2.1 hB.2.2.2.1 (hB.2.2.2.2.2.2.2 v) hunr1
    (lam := lamOf k g.a v) (fun g W hW' => hHk.good v hnd g W hW') hR (h := 1)
    (GroundTheory.Automorphic.Reduction.finAt_one v) hPr
  have hω1 : ((localChar ω v ϖ : ℂˣ) : ℂ) = χ p := by
    rw [quasiChar_apply_eq_of_isUnramified (hOmL.good v hnd).1 hR.1, (hOmL.good v hnd).2, hv]
  rw [hloc1, hω1] at key
  simp only [lamOf, hv, Units.val_one, one_mul, map_mul, Complex.conj_ofReal] at key
  have hr : (((p : ℝ) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _).ne'
  have h : g.a p * (((p : ℝ) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ)
      = (χ p * (starRingEnd ℂ) (g.a p)) * (((p : ℝ) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ) :=
    key.trans (by ring)
  have h2 := mul_right_cancel₀ hr h
  linear_combination -h2

end UpperTheory.V.Z.Sym.Unl
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.HalfAlg
open scoped ComplexConjugate

namespace UpperTheory.V.Z.Sym.Unl

private theorem sq_of_conj {a x : ℂ} (h : conj a * x = a) :
    a * a = ((‖a‖ ^ 2 : ℝ) : ℂ) * x := by
  have h1 : a * conj a = ((‖a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']; push_cast; rfl
  calc a * a = a * (conj a * x) := by rw [h]
    _ = (a * conj a) * x := by ring
    _ = _ := by rw [h1]

private theorem ratio_eq {p s t : ℝ} (hp : 2 ≤ p) (hs0 : 0 < s) (hs : s * s = p) {z : ℂ}
    (hz : z * conj z = (p : ℂ)) (ht : 0 ≤ t) (hzt : z + 2 + z⁻¹ = (t : ℂ)) : z = (s : ℂ) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hn : Complex.normSq z = p := by
    have e := Complex.mul_conj z
    rw [hz] at e
    exact_mod_cast e.symm
  have hre := congrArg Complex.re hzt
  have him := congrArg Complex.im hzt
  simp [Complex.inv_re, Complex.inv_im, hn] at hre him
  have hn2 : z.re * z.re + z.im * z.im = p := by rw [← hn, Complex.normSq_apply]
  have hv : z.im = 0 := by
    have e : z.im * (p - 1) = 0 := by
      have e2 : z.im * (p - 1) = p * (z.im + -z.im / p) := by
        field_simp
        ring
      rw [e2, him, mul_zero]
    rcases mul_eq_zero.mp e with h | h
    · exact h
    · exfalso
      linarith
  have hre' : (z.re + 2) * p + z.re = t * p := by
    rw [← hre]
    field_simp
  have hu : (z.re - s) * (z.re + s) = 0 := by
    rw [hv] at hn2
    linear_combination hn2 - hs
  have hr : z.re = s := by
    rcases mul_eq_zero.mp hu with h | h
    · linarith
    · exfalso
      have hm : z.re = -s := by linarith
      rw [hm, ← hs] at hre'
      have hs1 : 1 < s := by nlinarith
      nlinarith [mul_nonneg ht (mul_nonneg hs0.le hs0.le), mul_pos hs0 (mul_pos (sub_pos.mpr hs1) (sub_pos.mpr hs1))]
  apply Complex.ext
  · simp [hr]
  · simp [hv]

private theorem abs_ratio_ne_of_sqrt_flip (p m : ℕ) (a x α β : ℂ) (σ : ℂ ≃+* ℂ) (hp : 2 ≤ p) (hx : ‖x‖ = 1)
    (hσx : ‖σ x‖ = 1) (hσ : σ ((Real.sqrt p : ℝ) : ℂ) = -((Real.sqrt p : ℝ) : ℂ))
    (ha : conj a * x = a) (hσa : conj (σ a) * σ x = σ a) (hsum : α + β = a)
    (hprod : α * β = x * (p : ℂ) ^ m) : ‖α‖ ^ 2 ≠ (p : ℝ) * ‖β‖ ^ 2 := by
  intro hab
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hx
    exact zero_ne_one hx
  have hσx0 : σ x ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hσx
    exact zero_ne_one hσx
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have hprod0 : α * β ≠ 0 := by
    rw [hprod]
    exact mul_ne_zero hx0 (pow_ne_zero _ hpC)
  have hβ : β ≠ 0 := right_ne_zero_of_mul hprod0
  have hα : α ≠ 0 := left_ne_zero_of_mul hprod0
  set s := Real.sqrt p with hs_def
  have hs0 : 0 < s := Real.sqrt_pos.mpr hp0
  have hss : s * s = p := Real.mul_self_sqrt hp0.le
  have hn : Complex.normSq α = p * Complex.normSq β := by
    rw [← Complex.sq_norm, ← Complex.sq_norm]
    exact hab
  have hnβ : (Complex.normSq β : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_pos.mpr hβ).ne'
  have hz : (α / β) * conj (α / β) = ((p : ℝ) : ℂ) := by
    rw [map_div₀, div_mul_div_comm, Complex.mul_conj, Complex.mul_conj, hn]
    push_cast
    field_simp
  have key : α / β + 2 + (α / β)⁻¹ = (a * a) / (α * β) := by
    rw [← hsum, inv_div]
    field_simp
    ring
  have hzt : α / β + 2 + (α / β)⁻¹ = ((‖a‖ ^ 2 / (p : ℝ) ^ m : ℝ) : ℂ) := by
    rw [key, sq_of_conj ha, hprod]
    push_cast
    field_simp
  have ht : (0 : ℝ) ≤ ‖a‖ ^ 2 / (p : ℝ) ^ m := by positivity
  have hz' := ratio_eq hpR hs0 hss hz ht hzt
  have hαs : α = (s : ℂ) * β := (div_eq_iff hβ).mp hz'
  have k2 : (s : ℂ) * (a * a) = (1 + (s : ℂ)) ^ 2 * (x * (p : ℂ) ^ m) := by
    rw [← hprod, ← hsum, hαs]
    ring
  have k3 := congrArg σ k2
  simp only [map_mul, map_add (f := _), map_pow, map_natCast, map_one, hσ] at k3
  rw [sq_of_conj hσa] at k3
  push_cast at k3
  have k4 : (-(s * ‖σ a‖ ^ 2 : ℝ) : ℂ) * σ x = ((1 - s) ^ 2 * (p : ℝ) ^ m : ℝ) * σ x := by
    push_cast
    linear_combination k3
  have k5 := mul_right_cancel₀ hσx0 k4
  have k6 : -(s * ‖σ a‖ ^ 2) = (1 - s) ^ 2 * (p : ℝ) ^ m := by exact_mod_cast k5
  have hs1 : 1 < s := by nlinarith
  have hpm : 0 < (p : ℝ) ^ m := pow_pos hp0 m
  nlinarith [mul_nonneg hs0.le (sq_nonneg ‖σ a‖), mul_pos (pow_pos (sub_pos.mpr hs1) 2) hpm]

end UpperTheory.V.Z.Sym.Unl

theorem UpperTheory.V.Z.Sym.Unl.halfAlg :
    UpperTheory.V.Z.Sym.Unl.HalfAlg := by
  intro p m a x α β σ hp hx hσx hσ ha hσa hsum hprod
  exact UpperTheory.V.Z.Sym.Unl.abs_ratio_ne_of_sqrt_flip p m a x α β σ hp hx hσx hσ ha hσa hsum hprod
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.SqrtFlip
private theorem UpperTheory.V.Z.Sym.Unl.exists_ring_equiv_flip_sqrt (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsGalois ℚ Ω] [IsAlgClosed Ω]
    (ε : Ω →+* ℂ) (p : ℕ) (hp : p.Prime) :
    ∃ σ : ℂ ≃+* ℂ, σ ((Real.sqrt p : ℝ) : ℂ) = -((Real.sqrt p : ℝ) : ℂ) := by
  have hne : ∀ b : ℚ, b ^ 2 ≠ (p : ℚ) := by
    intro b hb
    apply hp.irrational_sqrt
    refine ⟨|b|, ?_⟩
    have h2 : ((b : ℝ)) ^ 2 = (p : ℝ) := by exact_mod_cast hb
    rw [← h2, Real.sqrt_sq_eq_abs]
    push_cast
    rfl
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (p : Ω) (by norm_num : 0 < 2)
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C (p : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two hne
  have hev : ∀ x : Ω, x ^ 2 = (p : Ω) → Polynomial.aeval x (Polynomial.X ^ 2 - Polynomial.C (p : ℚ)) = 0 := by
    intro x hx
    simp [hx]
  have hmon : (Polynomial.X ^ 2 - Polynomial.C (p : ℚ)).Monic := Polynomial.monic_X_pow_sub_C _ (by norm_num)
  have hmin : minpoly ℚ (-a) = minpoly ℚ a := by
    rw [← minpoly.eq_of_irreducible_of_monic hirr (hev a ha) hmon,
      ← minpoly.eq_of_irreducible_of_monic hirr (hev (-a) (by rw [neg_sq, ha])) hmon]
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ℚ) (E := Ω)).mp hmin
  let s : Ω ≃+* Ω := σ.toRingEquiv
  have hsa : s a = -a := hσ
  obtain ⟨g, hg⟩ := GlobalTheory.FN.exists_ringEquiv_extend_of_embedding Ω ε s
  refine ⟨g, ?_⟩
  have hea : (ε a) ^ 2 = ((Real.sqrt p : ℝ) : ℂ) ^ 2 := by
    rw [← map_pow, ha, map_natCast, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp
  have hga : g (ε a) = -(ε a) := by rw [hg, hsa, map_neg]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hea with h | h
  · rw [← h, hga]
  · have : ((Real.sqrt p : ℝ) : ℂ) = -(ε a) := by rw [h, neg_neg]
    rw [this, map_neg, hga, neg_neg]

theorem UpperTheory.V.Z.Sym.Unl.sqrtFlip :
    UpperTheory.V.Z.Sym.Unl.SqrtFlip := fun p hp =>
  UpperTheory.V.Z.Sym.Unl.exists_ring_equiv_flip_sqrt (AlgebraicClosure ℚ)
    (IsAlgClosed.lift (R := ℚ) (S := AlgebraicClosure ℚ) (M := ℂ)).toRingHom p hp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.ConjEig
open UpperTheory.V.Af UpperTheory.V.Sd

namespace UpperTheory.V.Z.Sym.Unl

theorem conjEig : ConjEig := by
  intro k N χ g hg σ
  obtain ⟨f', h1, h2⟩ := hg σ
  refine ⟨⟨f', h1, ?_, ?_⟩, fun n hn => h2 n hn⟩
  · rw [h2 1 le_rfl, g.one, map_one]
  · intro p hp n hn
    have e := congrArg σ (g.eig p hp n hn)
    have hc : (cj σ χ) (p : ZMod N) = σ (χ p) := rfl
    show coef f' (p * n) + (cj σ χ) p * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then coef f' (n / p) else 0) = coef f' p * coef f' n
    rw [h2 _ (Nat.mul_pos hp.pos hn), h2 _ hp.pos, h2 _ hn, hc]
    by_cases hd : p ∣ n
    · have hm : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd hn hd) hp.pos
      simp only [hd, if_true] at e ⊢
      rw [h2 _ hm]
      simpa [map_add (f := _), map_mul, map_pow, map_natCast] using e
    · simp only [hd, if_false] at e ⊢
      simpa [map_add (f := _), map_mul, map_pow, map_natCast] using e

end UpperTheory.V.Z.Sym.Unl
end

noncomputable section

namespace UpperTheory.V.Z.Sym.Unl

theorem goodHalf : GoodHalf := by
  intro k N _ hk χ hχ g hg p hp hpN α β hs hm
  obtain ⟨σ, hσ⟩ := sqrtFlip p hp
  obtain ⟨g', hg'⟩ := conjEig k N χ g hg σ
  have hu : IsUnit ((p : ℕ) : ZMod N) :=
    (ZMod.isUnit_iff_coprime p N).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN)
  have h1 : ‖χ (p : ZMod N)‖ = 1 := by
    have := DirichletCharacter.unit_norm_eq_one χ hu.unit
    simpa using this
  have e : cj σ χ (p : ZMod N) = σ (χ (p : ZMod N)) := rfl
  have h2 : ‖σ (χ (p : ZMod N))‖ = 1 := by
    have := DirichletCharacter.unit_norm_eq_one (cj σ χ) hu.unit
    rw [IsUnit.unit_spec, e] at this
    exact this
  have a1 := selfAdj k N hk χ hχ g p hp hpN
  have a2 := selfAdj k N hk (cj σ χ) (primCj N χ σ hχ) g' p hp hpN
  rw [hg' p hp.one_lt.le, e] at a2
  exact halfAlg p (k - 1) (g.a p) (χ (p : ZMod N)) α β σ hp.two_le h1 h2 hσ a1 a2 hs hm

end UpperTheory.V.Z.Sym.Unl
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.BadAbs
private theorem norm_sq_of_scaled (k p : ℕ) (hk : 3 ≤ k) (hp : 2 ≤ p) (x : ℂ)
    (h : ‖x * (((p : ℝ) ^ (1 - (k : ℝ) / 2) : ℝ) : ℂ)‖ ^ 2 = (p : ℝ)) : ‖x‖ ^ 2 = (p : ℝ) ^ (k - 1) := by
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (by omega)
  have hr : (0 : ℝ) < (p : ℝ) ^ (1 - (k : ℝ) / 2) := Real.rpow_pos_of_pos hp0 _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, mul_pow] at h
  have hr2 : ((p : ℝ) ^ (1 - (k : ℝ) / 2)) ^ 2 = (p : ℝ) ^ (2 - (k : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    congr 1
    push_cast
    ring
  have he : (((k - 1 : ℕ) : ℝ)) + (2 - (k : ℝ)) = 1 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have hkey : (p : ℝ) ^ (k - 1) * (p : ℝ) ^ (2 - (k : ℝ)) = p := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hp0, he, Real.rpow_one]
  have hne : (p : ℝ) ^ (2 - (k : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hp0 _).ne'
  rw [hr2] at h
  exact mul_right_cancel₀ hne (h.trans hkey.symm)

theorem UpperTheory.V.Z.Sym.Unl.badAbs :
    UpperTheory.V.Z.Sym.Unl.BadAbs := by
  intro k N _ hk χ hχ g p hp hpN
  have b0 : Ad3.R.B0 := @GlobalTheory.T.global_rankin_selberg_basic_facts
  have c0 : Ad3.R.C0 := @GlobalTheory.T.hecke_coset_representatives
  have c1 : Ad3.R.C1 := @GlobalTheory.T.congruence_subgroup_coset_decomposition
  have u2 : Ad3.R.U2 := @GlobalTheory.T.unramified_whittaker_newform
  have g0 : Ad3.R.G0 := @GlobalTheory.T.fundamental_domain_invariance_of_description (@GlobalTheory.T.fundamental_domain_description)
  have g1 : Ad3.R.G1 := @GlobalTheory.T.central_character_integral_properties (@GlobalTheory.T.fundamental_domain_integral_central_invariance)
  have f0 : Ad3.R.F0 := @GlobalTheory.T.newform_lift_existence b0
  have f0b : Ad3.R.F0b := @GlobalTheory.T.newform_lift_conductor b0
  have f1 : Ad3.R.F1 := @GlobalTheory.T.newform_lift_level b0
  have f1b : Ad3.R.AutomorphicLevelEquivariance := @GlobalTheory.T.newform_lift_level_character b0
  have f2 : Ad3.R.F2 := @GlobalTheory.T.newform_lift_whittaker_expansion
  have f3a : Ad3.R.HeckeSumLocalTranslates := @GlobalTheory.T.newform_lift_local_type b0
  have f3 : Ad3.R.F3 := @GlobalTheory.T.newform_lift_hecke_eigenvalues b0 c0 c1 f0b f1 f1b f3a
  have f5 : Ad3.R.F5 := @GlobalTheory.T.newform_lift_rapid_decay b0
  have f4 : Ad3.R.F4 := @GlobalTheory.T.newform_lift_fourier_coefficients b0 c1 u2 g0 g1 f0b f1 f2 f3 f5
  obtain ⟨hform, heig⟩ := Ad3P.sEig k N hk χ g
  obtain ⟨ω, hω⟩ := f0 N χ
  obtain ⟨-, φ, hφ⟩ := f1 k N χ _ _ hform g.one ω hω
  obtain ⟨v, rfl⟩ := b0.2.2.1 p hp
  have h := f4 k N hk χ hχ _ _ hform heig ω φ hω hφ v hpN
  exact norm_sq_of_scaled k _ hk hp.two_le _ h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.NeZeroRep
noncomputable section

namespace UpperTheory.V.Z.Sym.Unl.UnlinkedPrincipalSeriesHeckeRoots

section Rep

private theorem mod_retr {R S M : Type} [Ring R] [AddCommGroup S] [Module R S] [AddCommGroup M] [Module R M]
    [IsSimpleModule R S] (h : ⨆ f : S →ₗ[R] M, LinearMap.range f = ⊤) (x : M) (hx : x ≠ 0) :
    ∃ T : M →ₗ[R] S, T x ≠ 0 := _root_.DedupShared.dedup_mod_retr_5 (R := R) (S := S) (M := M) h x hx

variable {Γ X V : Type} [Group Γ] [AddCommGroup X] [Module ℂ X] [AddCommGroup V] [Module ℂ V]

private theorem rep_retr (σ : Representation ℂ Γ X) (hσ : σ.IsIrreducible) (τ : Representation ℂ Γ V)
    (h : ⨆ f : {f : X →ₗ[ℂ] V // ∀ g v, f (σ g v) = τ g (f v)}, LinearMap.range f.1 = ⊤) (x : V) (hx : x ≠ 0) :
    ∃ T : V →ₗ[ℂ] X, (∀ g v, T (τ g v) = σ g (T v)) ∧ T x ≠ 0 := by
  have key := mod_retr (R := MonoidAlgebra ℂ Γ) (S := σ.asModule) (M := τ.asModule) (by
      refine top_le_iff.1 fun y _ => ?_
      have hy : τ.asModuleEquiv y ∈ (⊤ : Submodule ℂ V) := trivial
      rw [← h] at hy
      rw [← τ.asModuleEquiv.symm_apply_apply y]
      refine Submodule.iSup_induction _ (motive := fun z => τ.asModuleEquiv.symm z ∈ _) hy ?_ ?_ ?_
      · rintro f _ ⟨v, rfl⟩
        exact Submodule.mem_iSup_of_mem (Representation.IntertwiningMap.equivLinearMapAsModule σ τ
          ⟨f.1, fun g => LinearMap.ext (f.2 g)⟩) ⟨v, rfl⟩
      · simp
      · intro a b ha hb
        rw [map_add (f := _)]
        exact add_mem ha hb)
  obtain ⟨T, h2⟩ := key x hx
  let T' := (Representation.IntertwiningMap.equivLinearMapAsModule τ σ).symm T
  exact ⟨T'.toLinearMap, fun g v => LinearMap.congr_fun (T'.2 g) v, h2⟩

private theorem ne_zero_rep (τ : Representation ℂ Γ V) {x : V} (hx : x ≠ 0) (g : Γ) : τ g ≠ 0 := fun h => hx (by
  have : τ g⁻¹ (τ g x) = x := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← this, h, LinearMap.zero_apply, map_zero])

private theorem map_dc (σ : Representation ℂ Γ X) (τ : Representation ℂ Γ V) (T : V →ₗ[ℂ] X)
    (hT : ∀ g v, T (τ g v) = σ g (T v)) {x : V} (hx : T x ≠ 0) (K : Subgroup Γ) (a : Γ) :
    T (Hi.dc τ K K a x) = Hi.dc σ K K a (T x) := by
  have hx0 : x ≠ 0 := fun e => hx (by rw [e, map_zero])
  rcases finite_or_infinite (MulAction.orbit K (a : Γ ⧸ K)) with hf | hf
  · haveI := Fintype.ofFinite (MulAction.orbit K (a : Γ ⧸ K))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply, map_sum, hT]
  · rw [Hi.dc, Hi.dc, finsum_of_infinite_support, finsum_of_infinite_support]
    · simp
    · rw [Function.support_eq_univ fun _ => ne_zero_rep σ hx _]
      exact Set.infinite_univ
    · rw [Function.support_eq_univ fun _ => ne_zero_rep τ hx0 _]
      exact Set.infinite_univ

end Rep

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL UpperTheory.V.Af UpperTheory.V.Sd

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem exists_ps {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin 2) k) V} (hπ : GlobalTheory.PRep.IsSmooth π)
    (hi : π.IsIrreducible) (μ₁ μ₂ : kˣ →* ℂˣ) (L : V →ₗ[ℂ] ℂ) (hL : L ≠ 0)
    (H : ∀ (a d : kˣ) (x : k) v, L (π (Matrix.GeneralLinearGroup.scalar (Fin 2) d * aff (a / d) x) v) =
      ((μ₁ a * μ₂ d : ℂˣ) : ℂ) * L v) :
    ∃ ψ : Fin 2 → kˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ IsSubquotient π (prinSeries ψ) ∧
      ∀ x : kˣ, ψ 0 x = μ₁ x * (absPow k (1 / 2) x)⁻¹ := by
  set δ : (Fin 2 → kˣ) →* ℂˣ := (deltaHalf k fun _ : Fin 2 => Unit).comp (leviTorus k (Fin 2)).toMonoidHom with hδ
  let χ : (Fin 2 → kˣ) →* ℂˣ := torusChar ![μ₁, μ₂] * δ⁻¹
  have hU : GlobalTheory.PRep.twKer π (unipB k (Fin 2)) 1 ≤ LinearMap.ker L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, v, rfl⟩
    obtain ⟨u1, u2⟩ := (mem_unipB k).1 u.2
    have e : (u : GL (Fin 2) k) = Matrix.GeneralLinearGroup.scalar (Fin 2) 1 * aff (1 / 1) (u.1.val 0 1) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [aff, u2, u1 1 0]
    have := H 1 1 (u.1.val 0 1) v
    rw [← e] at this
    simp [this]
  let l : GlobalTheory.PRep.Jacquet π (unipB k (Fin 2)) →ₗ[ℂ] ℂ := Submodule.liftQ _ L hU
  obtain ⟨v, hv⟩ : ∃ v, L v ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hL (LinearMap.ext hn)
  have hle : ∀ t x, l (jacB π t x) = (χ t : ℂ) * l x := fun t x => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have e : diagT k (Fin 2) t = Matrix.GeneralLinearGroup.scalar (Fin 2) (t 1) * aff (t 0 / t 1) 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [aff, val_diagT, Matrix.GeneralLinearGroup.scalar, mul_div_cancel₀]
    rw [UnramFixed.jacB_apply, jacBU_mk, map_smul, e]
    change _ * L _ = _ * L y
    rw [H, ← mul_assoc, ← Units.val_mul, mul_comm _ (μ₁ _ * _)]
    simp [χ, torusChar_apply, hδ]
  have hs : IsSmoothChar χ := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) (Filter.mem_of_superset
      ((isSmooth_jacB hπ (Submodule.Quotient.mk v)).mem_nhds (by simp)) ?_)
    intro g hg
    have hg' : jacB π g (Submodule.Quotient.mk v) = Submodule.Quotient.mk v := hg
    have h := hle g (Submodule.Quotient.mk v)
    rw [hg'] at h
    exact Units.ext (mul_right_cancel₀ (show l (Submodule.Quotient.mk v) ≠ 0 from hv) (h.symm.trans (one_mul _).symm))
  have htc : torusChar (fun i => χ.comp (MonoidHom.mulSingle (fun _ => kˣ) i)) = χ :=
    MonoidHom.ext fun t => by
      rw [torusChar_apply]
      conv_rhs => rw [← Finset.univ_prod_mulSingle t, map_prod]
      rfl
  refine ⟨fun i => χ.comp (MonoidHom.mulSingle (fun _ => kˣ) i),
    fun i => hs.comp _ (continuous_mulSingle (A := fun _ => kˣ) i), ?_, fun x => ?_⟩
  · have key := GlobalTheory.SatakeExists.isSubquotient_of_eigenform hπ hi χ l
      (fun e => hv (LinearMap.congr_fun e (Submodule.Quotient.mk v))) hle
    rw [← htc] at key
    exact key
  · have hd : ∀ (t : Fin 2 → kˣ) i, Matrix.GeneralLinearGroup.det (leviTorus k (Fin 2) t i) = t i := fun t =>
      congrFun ((leviTorus k (Fin 2)).left_inv t)
    have e0 : modExp (fun _ : Fin 2 => Unit) 0 = 1 := by decide
    have e1 : modExp (fun _ : Fin 2 => Unit) 1 = -1 := by decide
    have h1 : δ (Pi.mulSingle 0 x) = absPow k (1 / 2) x := by
      rw [hδ, MonoidHom.comp_apply]
      change deltaHalf k (fun _ : Fin 2 => Unit) (leviTorus k (Fin 2) (Pi.mulSingle 0 x)) = _
      rw [deltaHalf_apply, Fin.prod_univ_two, hd, hd, e0, e1]
      simp
    change torusChar ![μ₁, μ₂] (Pi.mulSingle 0 x) * (δ (Pi.mulSingle 0 x))⁻¹ = _
    rw [h1]
    simp [torusChar_apply]

section Gal

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} {h : IsPlaceOver A w}

private theorem root_lpTw (x : WD h) (s : ℝ) (g : Weil h) {z : ℂ} (hz : (x.charPol g).IsRoot z) :
    ((x.lpTw s).charPol g).IsRoot ((((normV w : ℕ) : ℂ) ^ (s : ℂ)) ^ deg g * z) := by
  obtain ⟨n, a, rfl⟩ := x.exists_rep
  rw [WD.lpTw_mk, WD.charPol_mk]
  rw [WD.charPol_mk] at hz
  have h1 := Module.End.hasEigenvalue_iff_isRoot_charpoly _ _ |>.2 hz
  obtain ⟨v, hv⟩ := h1.exists_hasEigenvector
  refine (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).1
    (Module.End.hasEigenvalue_of_hasEigenvector (x := v) ⟨?_, hv.2⟩)
  rw [Module.End.mem_eigenspace_iff, WDRep.tw_ρ, LinearMap.smul_apply, hv.apply_eq_smul, smul_smul]

end Gal

end UpperTheory.V.Z.Sym.Unl.UnlinkedPrincipalSeriesHeckeRoots

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial ValuativeRel
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL UpperTheory.V.Af
open UpperTheory.V.Sd UpperTheory.V.Z.Sym.Unl.UnlinkedPrincipalSeriesHeckeRoots

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Unl.tieU :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Z.Sym.Unl.TieU := by
  intro PH F Ω _ _ _ _ _ _ l _ ι ξ s c m a π r H w hl n lam hn hl0 hU A h t ht
  have P := PH.toClassicalTheorems
  obtain ⟨χ, hχ⟩ := H.pol
  obtain ⟨-, wt, HT, -, -, hall⟩ := UpperTheory.GalN.V.exRN (exR PH) F Ω l ι 2 one_le_two π χ H.reg hχ
  have hG := hall r H.cont H.att
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P F 2 π w
  obtain ⟨v, hv, hf, hUv⟩ := hU
  obtain ⟨T, hT, hTv⟩ := rep_retr σ.ρ σ.irred (π.locRep w) (hiso σ hσ).2 v hv
  obtain ⟨μ₁, μ₂, L, hL, hμ, hlam, hlaw⟩ := jacqOfU P F w σ n (Units.mk0 lam hl0) hn
    ⟨T v, hTv, fun u hu => by rw [← hT, hf u hu], by
      rw [Uop, ← map_dc σ.ρ (π.locRep w) T hT hTv, ← Uop, hUv, map_smul, Units.val_mk0]⟩
  obtain ⟨ψ, hψ, hs, hψ0⟩ := exists_ps σ.smooth σ.irred μ₁ μ₂ L hL hlaw
  obtain ⟨rc, hrc⟩ := P.exists_rec h
  let g : Weil h := (⟨t, mem_Weil_of_isFrob h ht⟩ : Weil h)⁻¹
  have hdeg : deg g = -1 := by
    rw [deg_inv, deg_eq_one_iff.2 ht]
  have hcont : Continuous fun g => ((r g : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) :=
    Units.continuous_val.comp H.cont
  have e1 := charPol_wdOf (h := h) hl ι hcont g
  rw [(hG.away w hl A h rc hrc σ hσ).pol, rec_algNorm hrc] at e1
  obtain ⟨b, hb, ε, -, hLw⟩ := id hrc
  have h1 := UpperTheory.V.AlgebraTools.jqRec F Ω A w h b hb ε rc hLw 2 ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩ ψ hψ hs g
  have hz : ((rc (IrrGL.of σ.ρ σ.smooth σ.irred)).charPol g).IsRoot ((ψ 0 (b g) : ℂˣ) : ℂ) := by
    refine (?_ : (rc (cls ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩)).charPol g |>.IsRoot _)
    rw [h1, Fin.prod_univ_two]
    simp
  have h2 := root_lpTw _ ((1 - ((2 : ℕ) : ℝ)) / 2) g hz
  rw [e1] at h2
  have key : (((normV w : ℕ) : ℂ) ^ ((((1 - ((2 : ℕ) : ℝ)) / 2 : ℝ)) : ℂ)) ^ deg g * ((ψ 0 (b g) : ℂˣ) : ℂ) = lam := by
    have hy : ord (w.adicCompletion F) (b g) = 1 := by rw [hb.ord_eq, hdeg, neg_neg]
    have hv0 : Valued.v ((b g : (w.adicCompletion F)ˣ) : w.adicCompletion F) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (Units.ne_zero _)
    have hv1 : Valued.v ((b g : (w.adicCompletion F)ˣ) : w.adicCompletion F) = WithZero.exp (-1 : ℤ) := by
      rw [SphCompletion.ord_completion] at hy
      rw [← WithZero.exp_log hv0]
      congr 1
      omega
    have hu : IsUnitAt w (b g * (atFin w (unif w))⁻¹) := by
      have h2 := unif_spec w
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀, hv1, h2]
      exact mul_inv_cancel₀ (by simp)
    have hμy : μ₁ (b g) = μ₁ (atFin w (unif w)) := by
      exact mul_inv_eq_one.1 (by rw [← map_inv, ← map_mul]; exact hμ _ hu)
    have hA := GlobalTheory.SatChar.absPow_art hb (1 / 2 : ℝ) g
    have hq : ((normV w : ℕ) : ℂ) ≠ 0 := by
      have := GlobalTheory.WeilDeligne.one_lt_normV w
      exact_mod_cast (zero_lt_one.trans this).ne'
    have hQ2 : ((normV w : ℕ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) * ((normV w : ℕ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) = ((normV w : ℕ) : ℂ) := by
      rw [← Complex.cpow_add _ _ hq]
      norm_num
    have hs' : ((((1 - ((2 : ℕ) : ℝ)) / 2 : ℝ)) : ℂ) = -(((1 / 2 : ℝ)) : ℂ) := by
      push_cast
      norm_num
    have hc : ((1 / 2 : ℂ)) = (((1 / 2 : ℝ)) : ℂ) := by
      push_cast
      rfl
    rw [hdeg] at hA
    rw [hψ0, Units.val_mul, Units.val_inv_eq_inv_val, hc, hA, hμy, hs', hdeg, Complex.cpow_neg]
    have hl' := hlam
    rw [Units.val_mk0] at hl'
    generalize ((normV w : ℕ) : ℂ) ^ (((1 / 2 : ℝ)) : ℂ) = Q at hQ2 ⊢
    rw [← hl', ← hQ2]
    simp only [zpow_neg, zpow_one, inv_inv]
    ring
  rw [key] at h2
  refine ⟨ι.symm lam, ?_, by simp⟩
  have h3 : ι.toRingHom (ι.symm lam) = lam := ι.apply_symm_apply lam
  rw [← h3] at h2
  exact (Polynomial.isRoot_map_iff ι.injective).1 h2
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.TieS
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.GalOfCusp GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.SmGL UpperTheory.V.Af UpperTheory.V.Sd

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.V.Z.Sym.Unl.tieS :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Z.Sym.Unl.TieS := by
  intro PH F Ω _ _ _ _ _ _ l _ ι ξ s c m a π r H w hl B hB
  have P := PH.toClassicalTheorems
  obtain ⟨χ, hχ⟩ := H.pol
  obtain ⟨-, wt, HT, -, -, hall⟩ := UpperTheory.GalN.V.exRN (exR PH) F Ω l ι 2 one_le_two π χ H.reg hχ
  have hG := hall r H.cont H.att
  obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P F 2 π w
  have hS := ((satLoc P F 2 w σ).2 _ π.finPart (hiso σ hσ) B).1 hB
  intro A h
  exact satFrob P F Ω l ι 2 r H.cont w hl σ B hS (fun A h rc hrc => UpperTheory.GalN.V.isWDOf_satR hG hl hrc hσ hS) A h
end

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.EG

namespace UpperTheory.V.Z.Sym.Unl

private theorem quad_pair {K : Type} [Field K] {a d u v : K} (hu : u ^ 2 - a * u + d = 0) (hv : v ^ 2 - a * v + d = 0)
    (hne : u ≠ v) : v + u = a ∧ v * u = d := by
  have h1 : u + v - a = 0 :=
    (mul_eq_zero.1 (by linear_combination hu - hv : (u - v) * (u + v - a) = 0)).resolve_left (sub_ne_zero.2 hne)
  exact ⟨by linear_combination h1, by linear_combination u * h1 - hu⟩

private theorem charpoly_quad {K : Type} [Field K] (B : Matrix (Fin 2) (Fin 2) K) {u : K} (h : B.charpoly.IsRoot u) :
    u ^ 2 - B.trace * u + B.det = 0 := by
  rw [Matrix.charpoly_fin_two] at h
  simpa [Polynomial.IsRoot] using h

private theorem inv_charpoly_root {K : Type} [Field K] {n : ℕ} (g : GL (Fin n) K) {x : K}
    (h : (g : Matrix (Fin n) (Fin n) K).charpoly.IsRoot x) :
    x ≠ 0 ∧ ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).charpoly.IsRoot x⁻¹ := by
  have hs : x ∈ spectrum K (g : Matrix (Fin n) (Fin n) K) := Matrix.mem_spectrum_iff_isRoot_charpoly.2 h
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact spectrum.zero_notMem K (Units.isUnit g) hs
  have hi : x⁻¹ ∈ spectrum K ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    simpa using (spectrum.inv_mem_iff (r := Units.mk0 x hx0) (a := g)).1 (by simpa using hs)
  exact ⟨hx0, Matrix.mem_spectrum_iff_isRoot_charpoly.1 hi⟩

private theorem norm_xi {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ)
    (ξ : G ℚ Ω →* (Qbar l)ˣ) (h : IsOpen (ξ.ker : Set (G ℚ Ω))) (s : G ℚ Ω) : ‖ι (ξ s : Qbar l)‖ = 1 := by
  haveI : Finite (G ℚ Ω ⧸ ξ.ker) := Subgroup.quotient_finite_of_isOpen _ h
  have h0 : ξ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : ξ s ^ ξ.ker.index = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (Subgroup.pow_index_mem _ s)
  have h2 : (ι (ξ s : Qbar l)) ^ ξ.ker.index = 1 := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]
  exact Complex.norm_eq_one_of_pow_eq_one h2 h0

private theorem det_inv {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {k : ℕ} (hk : 3 ≤ k)
    (r : G ℚ Ω →* GL (Fin 2) (Qbar l)) (ξ : G ℚ Ω →* (Qbar l)ˣ)
    (h : Matrix.GeneralLinearGroup.det.comp r = cycBar ℚ Ω l ^ (1 - (k : ℤ)) * ξ) (s : G ℚ Ω) :
    (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det = (cycBar ℚ Ω l s : Qbar l) ^ (k - 1) * ((ξ s)⁻¹ : (Qbar l)ˣ) := by
  have h1 : Matrix.GeneralLinearGroup.det (r s⁻¹) = (cycBar ℚ Ω l ^ (1 - (k : ℤ)) * ξ) s⁻¹ := DFunLike.congr_fun h s⁻¹
  have h2 : (cycBar ℚ Ω l ^ (1 - (k : ℤ)) * ξ) s⁻¹ = cycBar ℚ Ω l s ^ (k - 1) * (ξ s)⁻¹ := by
    rw [show 1 - (k : ℤ) = -((k - 1 : ℕ) : ℤ) by omega, zpow_neg, zpow_natCast, MonoidHom.mul_apply, map_inv, map_inv,
      MonoidHom.inv_apply, MonoidHom.pow_apply, inv_inv]
  have h3 := congrArg Units.val (h1.trans h2)
  simpa using h3

theorem halfOf : HypothesesH → HalfOf := by
  intro P Ω _ _ _ l _ ι k N _ hk χ hχ g hg ξ c m a π r hO hU hS w hwl A hA s hs x y hx hy heq
  have hp := normV_prime w
  obtain ⟨hx0, hxr⟩ := inv_charpoly_root (r s) hx
  obtain ⟨hy0, hyr⟩ := inv_charpoly_root (r s) hy
  rw [← map_inv] at hxr hyr
  have hp1 : (1 : ℝ) < (normV w : ℝ) := by exact_mod_cast hp.one_lt
  have hnx : 0 < ‖ι x‖ := norm_pos_iff.2 (by simpa using hx0)
  have hny : 0 < ‖ι y‖ := norm_pos_iff.2 (by simpa using hy0)
  by_cases hpN : normV w ∣ N
  · have hb := badAbs k N hk χ hχ g (normV w) hp hpN
    have hR : 0 < ‖g.a (normV w)‖ := by
      have : 0 < ‖g.a (normV w)‖ ^ 2 := by rw [hb]; positivity
      rcases (norm_nonneg (g.a (normV w))).lt_or_eq with h | h
      · exact h
      · rw [← h] at this
        simp at this
    have hn : N.factorization (normV w) ≠ 0 := (hp.factorization_pos_of_dvd (NeZero.ne N) hpN).ne'
    obtain ⟨u₀, hu₀, hun⟩ := tieU P ℚ Ω l ι ξ _ c m a π r hO w hwl _ _ hn (norm_pos_iff.1 hR) (hU w) A hA s hs
    have hAq := (over_iff hA _).2 (dvd_refl (normV w))
    have hpl : ¬ normV w ∣ l := fun h => hwl ((mem_iff w l).2 h)
    have hd : ‖ι (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).det‖ = (normV w : ℝ) ^ (k - 1) := by
      rw [det_inv hk r ξ hO.det s, cyc_frob hp hAq hpl hs, map_mul, norm_mul, map_pow, norm_pow, map_natCast, Complex.norm_natCast,
        Units.val_inv_eq_inv_val, map_inv₀, norm_inv, norm_xi ι ξ hO.ξ_open s, inv_one, mul_one]
    have hall : ∀ u : Qbar l, (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.IsRoot u → ‖ι u‖ = ‖g.a (normV w)‖ := fun u hu => by
      by_cases e : u = u₀
      · rw [e, hun]
      · have h1 := (quad_pair (charpoly_quad _ hu) (charpoly_quad _ hu₀) e).2
        have h2 : ‖ι u₀‖ * ‖ι u‖ = (normV w : ℝ) ^ (k - 1) := by rw [← norm_mul, ← map_mul, h1, hd]
        rw [hun, ← hb] at h2
        exact mul_left_cancel₀ hR.ne' (h2.trans (sq _))
    have e1 := hall _ hxr
    have e2 := hall _ hyr
    rw [map_inv₀, norm_inv] at e1 e2
    have e3 : ‖ι x‖ = ‖ι y‖ := inv_injective (e1.trans e2.symm)
    rw [e3] at heq
    have : (1 : ℝ) * ‖ι y‖ ^ 2 = (normV w : ℝ) * ‖ι y‖ ^ 2 := by rw [one_mul]; exact heq
    have := mul_right_cancel₀ (pow_pos hny 2).ne' this
    exact hp1.ne this
  · obtain ⟨B, hB, e⟩ := hS w hpN
    have hF := tieS P ℚ Ω l ι ξ _ c m a π r hO w hwl B hB
    have hP := ((hF A hA).2 s hs).trans e
    have hq : ∀ u : Qbar l, (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly.IsRoot u →
        (ι u) ^ 2 - g.a (normV w) * ι u + χ (normV w : ZMod N) * (normV w : ℂ) ^ (k - 1) = 0 := fun u hu => by
      have h1 := congrArg (Polynomial.eval (ι u)) hP
      have h2 : (Polynomial.eval (ι u) (((r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly).map ι.toRingHom)) = 0 := by
        have := Polynomial.eval₂_at_apply (p := (r s⁻¹ : Matrix (Fin 2) (Fin 2) (Qbar l)).charpoly) ι.toRingHom u
        rw [Polynomial.eval_map]
        refine this.trans ?_
        rw [hu.eq_zero, map_zero]
      rw [h2] at h1
      simpa using h1.symm
    have hU' := hq _ hxr
    have hV' := hq _ hyr
    have hfin : ‖ι y⁻¹‖ ^ 2 = (normV w : ℝ) * ‖ι x⁻¹‖ ^ 2 := by
      rw [map_inv₀, map_inv₀, norm_inv, norm_inv, inv_pow, inv_pow, heq]
      field_simp
    by_cases e : ι x⁻¹ = ι y⁻¹
    · rw [e] at hfin
      have h3 : ‖ι y⁻¹‖ ≠ 0 := by rw [map_inv₀, norm_inv]; exact (inv_pos.2 hny).ne'
      have : (1 : ℝ) * ‖ι y⁻¹‖ ^ 2 = (normV w : ℝ) * ‖ι y⁻¹‖ ^ 2 := by rw [one_mul]; exact hfin
      have := mul_right_cancel₀ (pow_ne_zero 2 h3) this
      exact hp1.ne this
    · obtain ⟨h1, h2⟩ := quad_pair hU' hV' e
      exact goodHalf k N hk χ hχ g hg (normV w) hp hpN _ _ h1 h2 hfin

end UpperTheory.V.Z.Sym.Unl
