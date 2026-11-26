module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalCochainsGlueGlobal
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisCocycleIntegralAfterScaling
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HomPadicIntTrivialOfIrreducibleCompactRep
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CohomologyUnramifiedLift

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherRest
theorem UpperTheory.Reformulated.B.Rb6.norm_le_one_of_mem :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (c : UpperTheory.V.HV.Coef l)
    {x : Formalism.ConjugateSelfDual.Qbar l},
    x ∈ c.O →
      ‖x‖ ≤
        (1 :
          ℝ) := by
  intro l _ c x hx
  have h1 : IsIntegral ℤ_[l] (⟨x, hx⟩ : c.O) := Algebra.IsIntegral.isIntegral _
  have h2 : IsIntegral ℤ_[l] x := h1.map c.O.val
  have h3 : IsIntegral ℚ_[l] x := h2.tower_top
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralValue_le_one_iff (minpoly.monic h3),
    minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h2]
  intro n
  rw [Polynomial.coeff_map]
  exact PadicInt.norm_le_one _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TateDualCocycleCoboundaryOfVanishOnFixing
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKerRepCyclotomicNeOneNormalForm
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKerRepCyclotomicNeOneNormalForm
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.ImZ

variable {l : ℕ} [Fact l.Prime]

theorem norm_coe_unit (u : ℤ_[l]ˣ) : ‖((u : ℤ_[l]) : ℚ_[l])‖ = 1 := by
  exact PadicInt.norm_def.symm.trans (PadicInt.isUnit_iff.mp u.isUnit)

def logU (u : ℤ_[l]ˣ) : ℤ_[l] :=
  ⟨Formalism.MainNotions.LocalSituation.logZl l ((u : ℤ_[l]) : ℚ_[l]), (GlobalTheory.PadicLogUnits.logZl_hom l).2.2.1 _ (norm_coe_unit u)⟩

theorem coe_logU (u : ℤ_[l]ˣ) : ((logU u : ℤ_[l]) : ℚ_[l]) = Formalism.MainNotions.LocalSituation.logZl l ((u : ℤ_[l]) : ℚ_[l]) := rfl

theorem logU_mul (u w : ℤ_[l]ˣ) : logU (u * w) = logU u + logU w := by
  apply Subtype.ext
  show Formalism.MainNotions.LocalSituation.logZl l (((u * w : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) = Formalism.MainNotions.LocalSituation.logZl l ((u : ℤ_[l]) : ℚ_[l]) + Formalism.MainNotions.LocalSituation.logZl l ((w : ℤ_[l]) : ℚ_[l])
  rw [Units.val_mul, PadicInt.coe_mul]
  exact (GlobalTheory.PadicLogUnits.logZl_hom l).1 _ _ (norm_coe_unit u) (norm_coe_unit w)

theorem logU_one : logU (1 : ℤ_[l]ˣ) = 0 := by
  have h := logU_mul (l := l) 1 1
  rw [mul_one] at h
  linear_combination -h

def logHom : ℤ_[l]ˣ →* Multiplicative ℤ_[l] where
  toFun u := Multiplicative.ofAdd (logU u)
  map_one' := by rw [logU_one]; rfl
  map_mul' u w := by rw [logU_mul]; rfl

theorem continuous_logHom : Continuous (logHom (l := l)) := by
  have h1 : Continuous fun u : ℤ_[l]ˣ => ((u : ℤ_[l]) : ℚ_[l]) :=
    (continuous_subtype_val : Continuous (fun x : ℤ_[l] => (x : ℚ_[l]))).comp (Units.continuous_val (M := ℤ_[l]))
  have h2 : Continuous fun u : ℤ_[l]ˣ => Formalism.MainNotions.LocalSituation.logZl l ((u : ℤ_[l]) : ℚ_[l]) :=
    (GlobalTheory.PadicLogUnits.logZl_hom l).2.1.comp_continuous h1 (fun u => norm_coe_unit u)
  exact continuous_ofAdd.comp (h2.subtype_mk _)

theorem cycZ_eq_one_of_eps {Ω : Type} [Field Ω] [Algebra ℚ Ω] {z : G ℚ Ω} (h : eps l z = 1) :
    cycZ ℚ Ω l z = 1 := by
  have h' : ((cycZ ℚ Ω l z : ℤ_[l]) : ℚ_[l]) = 1 := by
    have h2 := h
    simp [eps, cycBar] at h2
    exact h2
  apply Units.ext
  exact PadicInt.ext (h'.trans PadicInt.coe_one.symm)

theorem isIrr_of_comp {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (H : Subgroup Γ)
    (h : IsIrr (r.comp H.subtype)) : IsIrr r := by
  obtain ⟨h1, _, h3⟩ := h
  exact ⟨h1, fun _ _ _ => Submodule.mem_top, fun W' hW' hinv => h3 W' hW' fun g v hv => hinv g v hv⟩

theorem exists_cycZ_nat (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (hl : l ≠ 2) :
    ∃ (σ : G ℚ Ω) (n : ℕ), 2 ≤ n ∧ ((cycZ ℚ Ω l σ : ℤ_[l]) = n) := by
  haveI : (Ideal.span {((2 : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 2
  obtain ⟨M, hM, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 ℚ) (Ideal.span {((2 : ℕ) : ℤ)})
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 ℚ)).injective_int]; exact bot_le)
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    ⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField ℚ)⟩
  have hlv : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal := by
    intro h
    have h2 : ((l : ℕ) : ℤ) ∈ M.comap (algebraMap ℤ (𝓞 ℚ)) := by
      rw [Ideal.mem_comap, map_natCast]; exact h
    change ((l : ℕ) : ℤ) ∈ Ideal.under ℤ M at h2
    rw [hc, Ideal.mem_span_singleton] at h2
    have h3 : (2 : ℕ) ∣ l := by exact_mod_cast h2
    exact hl ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out)).mp h3).symm
  have hσ := cycZ_of_isFrob (l := l) hlv (isPlaceOver_placeOf Ω v) (isFrob_frobOf Ω v)
  refine ⟨frobOf Ω v, normV v, ?_, hσ⟩
  have h0 : normV v ≠ 0 := by
    intro h0
    rw [h0, Nat.cast_zero] at hσ
    exact (cycZ ℚ Ω l (frobOf Ω v)).ne_zero hσ
  have h1 : normV v ≠ 1 := by
    intro h1
    have : Nat.card (𝓞 ℚ ⧸ v.asIdeal) = 1 := h1
    obtain ⟨hs, _⟩ := Nat.card_eq_one_iff_unique.mp this
    haveI : v.asIdeal.IsMaximal := hM
    haveI : Nontrivial (𝓞 ℚ ⧸ v.asIdeal) := inferInstance
    exact not_subsingleton _ hs
  omega

theorem logHom_ne_one (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (hl : l ≠ 2) :
    ∃ σ : G ℚ Ω, logHom (cycZ ℚ Ω l σ) ≠ 1 := by
  obtain ⟨σ, n, hn, hσ⟩ := exists_cycZ_nat (l := l) Ω hl
  refine ⟨σ ^ (l - 1), fun h => ?_⟩
  have hl1 : 1 ≤ l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  have hval : ((cycZ ℚ Ω l (σ ^ (l - 1)) : ℤ_[l]) : ℚ_[l]) = ((n ^ (l - 1) : ℕ) : ℚ_[l]) := by
    rw [map_pow, Units.val_pow_eq_pow_val, hσ]; push_cast; rfl
  have h0 : logU (cycZ ℚ Ω l (σ ^ (l - 1))) = 0 := by
    have := congrArg Multiplicative.toAdd h
    simpa [logHom] using this
  have h0' : Formalism.MainNotions.LocalSituation.logZl l ((n ^ (l - 1) : ℕ) : ℚ_[l]) = 0 := by
    rw [← hval, ← coe_logU, h0]; rfl

  have hnd : ¬ l ∣ n := by
    rintro ⟨k, rfl⟩
    have hu : IsUnit ((l * k : ℕ) : ℤ_[l]) := by rw [← hσ]; exact Units.isUnit _
    rw [Nat.cast_mul] at hu
    have hlu := PadicInt.isUnit_iff.mp (isUnit_of_mul_isUnit_left hu)
    rw [PadicInt.norm_p] at hlu
    have : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    have : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ this
    linarith

  have hdvd : ((l : ℤ)) ^ 1 ∣ ((n : ℤ) ^ (l - 1) - 1) := by
    rw [pow_one, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hz : ((n : ℤ) : ZMod l) ≠ 0 := by
      rw [Int.cast_natCast, ne_eq, ZMod.natCast_eq_zero_iff]; exact hnd
    push_cast
    rw [ZMod.pow_card_sub_one_eq_one (by simpa using hz), sub_self]
  have hnorm := (Padic.norm_int_le_pow_iff_dvd (p := l) _ 1).mpr hdvd
  have hle : ‖((n ^ (l - 1) : ℕ) : ℚ_[l]) - 1‖ ≤ (l : ℝ) ^ (-((1 : ℕ) : ℤ)) := by
    have : ((((n : ℤ) ^ (l - 1) - 1 : ℤ)) : ℚ_[l]) = ((n ^ (l - 1) : ℕ) : ℚ_[l]) - 1 := by push_cast; ring
    rw [← this]; exact hnorm
  have heq := (GlobalTheory.PadicLogUnits.logZl_hom l).2.2.2 1 le_rfl (fun h2 => absurd h2 hl) _ hle
  rw [h0', norm_zero] at heq
  have hne : ((n ^ (l - 1) : ℕ) : ℚ_[l]) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    have : 2 ≤ n ^ (l - 1) := le_trans hn (Nat.le_self_pow (by omega) n)
    intro he
    have : n ^ (l - 1) = 1 := by exact_mod_cast he
    omega
  exact hne (norm_eq_zero.mp heq.symm)

end GlobalTheory.Ord2.ImZ

namespace GlobalTheory.Ord2


open GlobalTheory.Ord2.ImZ in
theorem exists_ker_eps_ne_one : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ)
    (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∃ z ∈ W.ker, eps l z ≠ 1 := by
  intro l _ Ω _ _ _ e S A W h
  by_contra hne
  push_neg at hne
  obtain ⟨c, hc⟩ := h.int
  let lam : G ℚ Ω →* Multiplicative ℤ_[l] := logHom.comp (cycZ ℚ Ω l)
  have hlamc : Continuous lam := continuous_logHom.comp (continuous_cycZ ℚ Ω l)
  have hdet : ∀ g, ((W g : Matrix (Fin 2) (Fin 2) (Qbar l))).det ^ 2 = 1 := by
    intro g
    have := congrArg (fun u : (Qbar l)ˣ => (u : Qbar l)) (DFunLike.congr_fun h.det2 g)
    simpa [dt] using this
  have hker : W.ker ≤ lam.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    show logHom (cycZ ℚ Ω l z) = 1
    rw [cycZ_eq_one_of_eps (hne z hz), map_one]
  have hlam := GlobalTheory.T.hom_padicInt_trivial_of_irreducible_compact_rep l c (G ℚ Ω) W lam h.cont hc hdet (isIrr_of_comp W _ h.irr) hlamc hker
  obtain ⟨σ, hσ⟩ := logHom_ne_one (l := l) Ω h.l_odd
  exact hσ (DFunLike.congr_fun hlam σ)

end GlobalTheory.Ord2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKerRepCyclotomicNeOneNormalFormStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ker_rep_cyclotomic_ne_one_normalForm : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∃ z ∈ W.ker, eps l z ≠ 1 := by
  first | exact @GlobalTheory.Ord2.exists_ker_eps_ne_one | exact GlobalTheory.Ord2.exists_ker_eps_ne_one | (intros; apply GlobalTheory.Ord2.exists_ker_eps_ne_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TateDualCocycleCoboundaryOfVanishOnFixing
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem h1dual_of_vanish_fix : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ)
    (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ z ∈ Z1 (Loc.colRep (dual1 W)),
    (∀ g ∈ N0g W, z g = 0) → z ∈ ReciprocityTheory.Gal.B1 (Loc.colRep (dual1 W)) := by
  intro l _ Ω _ _ _ e S A W hW z hz hN
  obtain ⟨a, haK, hae⟩ := GlobalTheory.T.exists_ker_rep_cyclotomic_ne_one_normalForm l Ω e S A W hW
  have hWa : W a = 1 := haK
  have hdual : ∀ v : Fin 2 → Qbar l, Loc.colRep (dual1 W) a v = eps l a • v := by
    intro v
    show Matrix.toLin' ((dual1 W a : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) v = _
    rw [dual1, UpperTheory.V.Af.tw_val, hWa]
    simp [dt, hWa, eps, Matrix.toLin'_apply]
  have hcomm : ∀ g, z (a * g) = z (g * a) := by
    intro g
    have hn : (g * a)⁻¹ * (a * g) ∈ N0g W := by
      refine ⟨?_, ?_⟩
      · show cycBar ℚ Ω l ((g * a)⁻¹ * (a * g)) = 1
        simp [map_mul, map_inv, mul_comm, mul_left_comm, mul_assoc]
      · show W ((g * a)⁻¹ * (a * g)) = 1
        simp [map_mul, map_inv, hWa]
    have h1 : a * g = (g * a) * ((g * a)⁻¹ * (a * g)) := by group
    rw [h1, hz.2, hN _ hn, map_zero, add_zero]
  have hne : eps l a - 1 ≠ 0 := sub_ne_zero.mpr hae
  rw [mem_coboundaries1]
  refine ⟨(eps l a - 1)⁻¹ • z a, fun g => ?_⟩
  have key := hcomm g
  rw [hz.2, hz.2, hdual] at key

  have : (eps l a - 1) • z g = Loc.colRep (dual1 W) g (z a) - z a := by
    rw [sub_smul, one_smul]; rw [← sub_eq_zero] at key ⊢; rw [← key]; abel
  rw [map_smul, ← smul_sub, ← this, smul_smul, inv_mul_cancel₀ hne, one_smul]

end GlobalTheory.Ord2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TateDualCocycleCoboundaryOfVanishOnFixingStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateDual_cocycle_coboundary_of_vanish_on_fixing : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ z ∈ Z1 (Loc.colRep (dual1 W)), (∀ g ∈ N0g W, z g = 0) → z ∈ ReciprocityTheory.Gal.B1 (Loc.colRep (dual1 W)) := by
  first | exact @GlobalTheory.Ord2.h1dual_of_vanish_fix | exact GlobalTheory.Ord2.h1dual_of_vanish_fix | (intros; apply GlobalTheory.Ord2.h1dual_of_vanish_fix <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CocyclePairAlternatingNeOnCycloKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CocyclePairAlternatingNeOnCycloKernel
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.PairSpan

section Abstract

variable {Γ k : Type} [Group Γ] [Field k]

theorem alt_left_nondeg {v : Fin 2 → k} (hv : v ≠ 0) : ∃ a : Fin 2 → k, v 0 * a 1 - v 1 * a 0 ≠ 0 := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1; apply hv; funext i; fin_cases i <;> simp [h0, h1]
    exact ⟨![1, 0], by simp [h1]⟩
  · exact ⟨![0, 1], by simp [h0]⟩

theorem stable_cases {W : Γ →* GL (Fin 2) k} {H : Subgroup Γ} (hirr : UpperTheory.V.Af.IsIrr (W.comp H.subtype))
    (U : Submodule k (Fin 2 → k)) (hU : ∀ s ∈ H, ∀ v ∈ U, (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ v ∈ U) :
    U = ⊥ ∨ U = ⊤ :=
  hirr.2.2 U le_top (by intro g v hv; exact hU g g.2 v hv)

theorem coc_conj {n : ℕ} (ρ : Γ →* GL (Fin n) k) (y : Γ → Fin n → k)
    (hy : ∀ g h, y (g * h) = y g + (ρ g : Matrix (Fin n) (Fin n) k) *ᵥ y h) (s g : Γ) (hg : ρ g = 1) :
    y (s * g * s⁻¹) = (ρ s : Matrix (Fin n) (Fin n) k) *ᵥ y g := by
  have h1 : y 1 = 0 := by simpa using hy 1 1
  have h2 : y s + (ρ s : Matrix (Fin n) (Fin n) k) *ᵥ y s⁻¹ = 0 := by rw [← hy, mul_inv_cancel, h1]
  rw [hy, hy, map_mul, hg, mul_one, add_right_comm, h2, zero_add]

end Abstract
end GlobalTheory.Ord2.PairSpan

namespace GlobalTheory.Ord2.PairSpan

variable {Γ k : Type} [Group Γ] [Field k]

theorem exists_pair_ne [IsAlgClosed k] [CharZero k] {W : Γ →* GL (Fin 2) k} {H : Subgroup Γ}
    (hirr : UpperTheory.V.Af.IsIrr (W.comp H.subtype)) {N : Set Γ}
    (hN : ∀ s ∈ H, ∀ g ∈ N, s * g * s⁻¹ ∈ N) {y z : Γ → Fin 2 → k}
    (hy : ∀ s ∈ H, ∀ g ∈ N, y (s * g * s⁻¹) = (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ y g)
    (hz : ∀ s ∈ H, ∀ g ∈ N, z (s * g * s⁻¹) = (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ z g)
    (hy0 : ∃ g ∈ N, y g ≠ 0) (hz0 : ∃ g ∈ N, z g ≠ 0) :
    ∃ g ∈ N, ∃ h ∈ N, y h 0 * z g 1 - y h 1 * z g 0 ≠ y g 0 * z h 1 - y g 1 * z h 0 := by
  by_contra hcon
  push_neg at hcon
  let Sig : Submodule k ((Fin 2 → k) × (Fin 2 → k)) := Submodule.span k ((fun g => (y g, z g)) '' N)
  have hgen : ∀ g ∈ N, (y g, z g) ∈ Sig := fun g hg => Submodule.subset_span ⟨g, hg, rfl⟩
  have hinv : ∀ s ∈ H, ∀ σ ∈ Sig,
      ((W s : Matrix (Fin 2) (Fin 2) k) *ᵥ σ.1, (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ σ.2) ∈ Sig := by
    intro s hs σ hσ
    induction hσ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      rw [← hy s hs g hg, ← hz s hs g hg]
      exact hgen _ (hN s hs g hg)
    | zero =>
      simp only [Prod.fst_zero, Prod.snd_zero, Matrix.mulVec_zero, Prod.mk_zero_zero]
      exact Sig.zero_mem
    | add x x' _ _ ihx ihx' => simpa [Matrix.mulVec_add] using Sig.add_mem ihx ihx'
    | smul a x _ ihx => simpa [Matrix.mulVec_smul] using Sig.smul_mem a ihx
  have hB : ∀ g ∈ N, ∀ σ ∈ Sig, y g 0 * σ.2 1 - y g 1 * σ.2 0 = σ.1 0 * z g 1 - σ.1 1 * z g 0 := by
    intro g hg σ hσ
    induction hσ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, rfl⟩ := hx
      exact (hcon g hg h hh).symm
    | zero => simp
    | add x x' _ _ ihx ihx' =>
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
      linear_combination ihx + ihx'
    | smul a x _ ihx =>
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      linear_combination a * ihx
  let K' : Submodule k (Fin 2 → k) := Sig.comap (LinearMap.inr k (Fin 2 → k) (Fin 2 → k))
  have hK' : K' = ⊥ := by
    rcases stable_cases hirr K' (by
      intro s hs v hv
      have := hinv s hs _ hv
      simpa [K', Matrix.mulVec_zero] using this) with h | h
    · exact h
    · exfalso
      obtain ⟨g, hg, hyg⟩ := hy0
      obtain ⟨a, ha⟩ := alt_left_nondeg hyg
      have hmem : ((0 : Fin 2 → k), a) ∈ Sig := by
        have : a ∈ K' := h ▸ Submodule.mem_top
        simpa [K'] using this
      exact ha ((hB g hg _ hmem).trans (by simp))
  let P : Submodule k (Fin 2 → k) := Sig.map (LinearMap.fst k (Fin 2 → k) (Fin 2 → k))
  have hP : P = ⊤ := by
    rcases stable_cases hirr P (by
      rintro s hs v ⟨σ, hσ, rfl⟩
      exact ⟨_, hinv s hs σ hσ, rfl⟩) with h | h
    · exfalso
      obtain ⟨g, hg, hyg⟩ := hy0
      have : y g ∈ P := ⟨_, hgen g hg, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hyg this
    · exact h
  let f : Sig →ₗ[k] (Fin 2 → k) := (LinearMap.fst k (Fin 2 → k) (Fin 2 → k)).comp Sig.subtype
  have hfi : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun σ hσ => ?_
    have h1 : (σ : (Fin 2 → k) × (Fin 2 → k)).1 = 0 := hσ
    have h2 : (σ : (Fin 2 → k) × (Fin 2 → k)).2 ∈ K' := by
      show LinearMap.inr k _ _ (σ : (Fin 2 → k) × (Fin 2 → k)).2 ∈ Sig
      have : LinearMap.inr k (Fin 2 → k) (Fin 2 → k) (σ : (Fin 2 → k) × (Fin 2 → k)).2 = σ := by
        ext1 <;> simp [h1]
      rw [this]; exact σ.2
    rw [hK', Submodule.mem_bot] at h2
    exact Subtype.ext (Prod.ext h1 h2)
  have hfs : Function.Surjective f := by
    intro a
    have : a ∈ P := hP ▸ Submodule.mem_top
    obtain ⟨σ, hσ, rfl⟩ := this
    exact ⟨⟨σ, hσ⟩, rfl⟩
  let e := LinearEquiv.ofBijective f ⟨hfi, hfs⟩
  let φ : Module.End k (Fin 2 → k) :=
    (LinearMap.snd k (Fin 2 → k) (Fin 2 → k)).comp (Sig.subtype.comp e.symm.toLinearMap)
  have hφmem : ∀ a, (a, φ a) ∈ Sig := by
    intro a
    have h1 : ((e.symm a : Sig) : (Fin 2 → k) × (Fin 2 → k)).1 = a := e.apply_symm_apply a
    have : (a, φ a) = ((e.symm a : Sig) : (Fin 2 → k) × (Fin 2 → k)) := Prod.ext h1.symm rfl
    rw [this]; exact (e.symm a).2
  have hφ : ∀ σ ∈ Sig, φ σ.1 = σ.2 := by
    intro σ hσ
    have : e.symm σ.1 = ⟨σ, hσ⟩ := e.symm_apply_eq.2 rfl
    show ((e.symm σ.1 : Sig) : (Fin 2 → k) × (Fin 2 → k)).2 = σ.2
    rw [this]
  have hφW : ∀ s ∈ H, ∀ a, φ ((W s : Matrix (Fin 2) (Fin 2) k) *ᵥ a) = (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ φ a :=
    fun s hs a => hφ _ (hinv s hs _ (hφmem a))
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue φ
  have hE : Module.End.eigenspace φ c = ⊤ := by
    rcases stable_cases hirr (Module.End.eigenspace φ c) (by
      intro s hs v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      rw [hφW s hs, hv, Matrix.mulVec_smul]) with h | h
    · exact absurd h (Module.End.hasEigenvalue_iff.1 hc)
    · exact h
  have hφc : ∀ a, φ a = c • a := fun a => Module.End.mem_eigenspace_iff.1 (hE ▸ Submodule.mem_top)
  have hzy : ∀ g ∈ N, z g = c • y g := fun g hg => by rw [← hφc]; exact (hφ _ (hgen g hg)).symm
  obtain ⟨g1, hg1, hzg1⟩ := hz0
  have hc0 : c ≠ 0 := by rintro rfl; apply hzg1; rw [hzy g1 hg1, zero_smul]
  obtain ⟨g0, hg0, hyg0⟩ := hy0
  have horth : ∀ h ∈ N, y g0 0 * y h 1 - y g0 1 * y h 0 = 0 := by
    intro h hh
    have := hcon h hh g0 hg0
    rw [hzy h hh, hzy g0 hg0] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have h2 : (2 * c) * (y g0 0 * y h 1 - y g0 1 * y h 0) = 0 := by linear_combination this
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exfalso; exact hc0 (by simpa using h3)
    · exact h3
  have hall : ∀ σ ∈ Sig, y g0 0 * σ.1 1 - y g0 1 * σ.1 0 = 0 := by
    intro σ hσ
    induction hσ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, rfl⟩ := hx
      exact horth h hh
    | zero => simp
    | add x x' _ _ ihx ihx' =>
      simp only [Prod.fst_add, Pi.add_apply]
      linear_combination ihx + ihx'
    | smul a x _ ihx =>
      simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
      linear_combination a * ihx
  obtain ⟨a, ha⟩ := alt_left_nondeg hyg0
  exact ha (hall _ (hφmem a))

end GlobalTheory.Ord2.PairSpan

namespace GlobalTheory.Ord2


open PairSpan in
theorem exists_om_ne_swap_on_N0g : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ)
    (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ y ∈ Z1 (Loc.colRep W),
    ∀ z ∈ Z1 (Loc.colRep (dual1 W)), (∃ g ∈ N0g W, y g ≠ 0) → (∃ g ∈ N0g W, z g ≠ 0) →
    ∃ g ∈ N0g W, ∃ h ∈ N0g W, om (y h) (z g) ≠ om (y g) (z h) := by
  intro l _ Ω _ _ _ e S A W hW y hyZ z hzZ hy0 hz0
  have hy' : ∀ g h, y (g * h) = y g + (W g : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ y h := fun g h => by
    rw [hyZ.2 g h]; rfl
  have hz' : ∀ g h, z (g * h) = z g + (dual1 W g : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ z h := fun g h => by
    rw [hzZ.2 g h]; rfl
  have hnorm : (N0g W).Normal := by unfold N0g; infer_instance
  have hdual : ∀ s, cycBar ℚ Ω l s = 1 → dt W s = 1 → dual1 W s = W s := by
    intro s h1 h2
    apply Units.ext
    rw [dual1, tw_val]
    simp [h1, h2]
  have hN1 : ∀ g ∈ N0g W, W g = 1 := fun g hg => (Subgroup.mem_inf.1 hg).2
  have hNd : ∀ g ∈ N0g W, dual1 W g = 1 := by
    intro g hg
    have h1 : cycBar ℚ Ω l g = 1 := (Subgroup.mem_inf.1 hg).1
    have h2 : dt W g = 1 := by
      show Matrix.GeneralLinearGroup.det (W g) = 1
      rw [hN1 g hg, map_one]
    rw [hdual g h1 h2, hN1 g hg]
  have hH : ∀ s ∈ H0g W, dual1 W s = W s := fun s hs =>
    hdual s (Subgroup.mem_inf.1 hs).1 (Subgroup.mem_inf.1 hs).2
  obtain ⟨g, hg, h, hh, hne⟩ := exists_pair_ne (k := Qbar l) (W := W) (H := H0g W) (N := (N0g W : Set (G ℚ Ω)))
    hW.irr (fun s _ g hg => hnorm.conj_mem g hg s)
    (y := y) (z := z)
    (fun s _ g hg => coc_conj W y hy' s g (hN1 g hg))
    (fun s hs g hg => by rw [coc_conj (dual1 W) z hz' s g (hNd g hg), hH s hs])
    hy0 hz0
  exact ⟨g, hg, h, hh, hne⟩

end GlobalTheory.Ord2

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CocyclePairAlternatingNeOnCycloKernelStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_pair_alternating_ne_on_cycloKernel : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ y ∈ Z1 (Loc.colRep W), ∀ z ∈ Z1 (Loc.colRep (dual1 W)), (∃ g ∈ N0g W, y g ≠ 0) → (∃ g ∈ N0g W, z g ≠ 0) → ∃ g ∈ N0g W, ∃ h ∈ N0g W, om (y h) (z g) ≠ om (y g) (z h) := by
  first | exact @GlobalTheory.Ord2.exists_om_ne_swap_on_N0g | exact GlobalTheory.Ord2.exists_om_ne_swap_on_N0g | (intros; apply GlobalTheory.Ord2.exists_om_ne_swap_on_N0g <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealEqComap
namespace GlobalTheory.IdealComapPreimage

open IsDedekindDomain

theorem ideal_eq_comap {p : ℕ} (hp : Nat.Prime p)
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (hv : (p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal) :
    v.asIdeal = Ideal.comap (Rat.ringOfIntegersEquiv : NumberField.RingOfIntegers ℚ →+* ℤ)
      (Ideal.span {(p : ℤ)}) := by
  set e := Rat.ringOfIntegersEquiv
  haveI hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hp).irreducible
  haveI : (Ideal.comap (e : NumberField.RingOfIntegers ℚ →+* ℤ) (Ideal.span {(p : ℤ)})).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ e.surjective
  symm
  refine Ideal.IsMaximal.eq_of_le this v.isPrime.ne_top ?_
  intro x hx
  rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hx
  obtain ⟨k, hk⟩ := hx
  have : x = (p : NumberField.RingOfIntegers ℚ) * e.symm k := by
    apply e.injective
    simpa using hk
  rw [this]
  exact v.asIdeal.mul_mem_right _ hv

theorem main : ∀ {p : ℕ}, Nat.Prime p → ∀ {v v' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)}, (↑p : NumberField.RingOfIntegers ℚ) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v → (↑p : NumberField.RingOfIntegers ℚ) ∈ IsDedekindDomain.HeightOneSpectrum.asIdeal v' → v = v' := by
  intro p hp v v' hv hv'
  apply HeightOneSpectrum.ext
  rw [ideal_eq_comap hp v hv, ideal_eq_comap hp v' hv']

end GlobalTheory.IdealComapPreimage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StrictVanishingDualOfLiterature
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2.StrictKill

section Basic

variable {l : ℕ} [Fact l.Prime]

theorem norm_le_one_of_mem (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.Rb6.norm_le_one_of_mem c hx

theorem place_eq {p : ℕ} (hp : p.Prime) {v v' : HeightOneSpectrum (𝓞 ℚ)} (hv : ((p : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (hv' : ((p : ℕ) : 𝓞 ℚ) ∈ v'.asIdeal) : v = v' :=
  _root_.GlobalTheory.IdealComapPreimage.main hp hv hv'

theorem cg_self (n : ℕ) (a : Qbar l) : Cg n a a := by
  unfold Cg; rw [sub_self, norm_zero]; exact norm_nonneg _

theorem cv_of_eq (n : ℕ) {a b : Fin 2 → Qbar l} (h : a = b) : Cv n a b := by
  subst h; intro i; exact cg_self n _

theorem norm_l_lt_one : ‖((l : ℕ) : Qbar l)‖ < 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
  exact Padic.norm_p_lt_one

theorem sub_one_mem (c : Coef l) {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : ∀ i j, M i j ∈ c.O) (i j : Fin 2) :
    (M - 1) i j ∈ c.O := by
  rw [Matrix.sub_apply, Matrix.one_apply]
  split_ifs
  · exact sub_mem (hM i j) (one_mem _)
  · exact sub_mem (hM i j) (zero_mem _)

theorem det_mem (c : Coef l) {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : ∀ i j, M i j ∈ c.O) : M.det ∈ c.O := by
  rw [Matrix.det_fin_two]
  exact sub_mem (mul_mem (hM 0 0) (hM 1 1)) (mul_mem (hM 0 1) (hM 1 0))

end Basic

section Twist

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem colRep_apply (W : R2 Ω l) (s : G ℚ Ω) (v : Fin 2 → Qbar l) : Loc.colRep W s v = mat W s *ᵥ v := by
  simp [Loc.colRep, mat, Matrix.toLin'_apply]

theorem mat_dual1 (W : R2 Ω l) (s : G ℚ Ω) :
    mat (dual1 W) s = (eps l s * (((dt W s)⁻¹ : (Qbar l)ˣ) : Qbar l)) • mat W s := by
  simp only [mat, dual1, tw_val, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul, eps]

theorem dt_inv (W : R2 Ω l) (h2 : dt W ^ 2 = 1) (s : G ℚ Ω) : (dt W s)⁻¹ = dt W s := by
  have h := DFunLike.congr_fun h2 s
  simp only [pow_two, MonoidHom.mul_apply, MonoidHom.one_apply] at h
  exact inv_eq_of_mul_eq_one_right h

theorem val_dt (W : R2 Ω l) (s : G ℚ Ω) : ((dt W s : (Qbar l)ˣ) : Qbar l) = (mat W s).det := by
  simp [dt, mat]

theorem eps_eq (s : G ℚ Ω) :
    eps l s = algebraMap ℤ_[l] (PadicAlgCl l) ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l]) := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
  rfl

theorem eps_mem (c : Coef l) (s : G ℚ Ω) : eps l s ∈ c.O := by
  rw [eps_eq]; exact c.O.algebraMap_mem _

theorem dual_representation_integral_entries (c : Coef l) (W : R2 Ω l) (hW : ∀ s i j, mat W s i j ∈ c.O) (h2 : dt W ^ 2 = 1) :
    ∀ s i j, mat (dual1 W) s i j ∈ c.O := by
  intro s i j
  rw [mat_dual1, dt_inv W h2, Matrix.smul_apply, smul_eq_mul, val_dt]
  exact mul_mem (mul_mem (eps_mem c s) (det_mem c (hW s))) (hW s i j)

theorem cont_dual1 (W : R2 Ω l) (hW : Continuous W) (h2 : dt W ^ 2 = 1) : Continuous (dual1 W) := by
  have he : Continuous (fun s : G ℚ Ω => eps l s) := by
    have hz : Continuous (fun s : G ℚ Ω => ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])) :=
      Units.continuous_val.comp (continuous_cycZ ℚ Ω l)
    exact (continuous_algebraMap ℚ_[l] (Qbar l)).comp (continuous_subtype_val.comp hz)
  have hdv : Continuous (fun s => ((dt W s : (Qbar l)ˣ) : Qbar l)) := by
    simp only [val_dt]
    exact (Units.continuous_val.comp hW).matrix_det
  have hm : Continuous (fun s => mat (dual1 W) s) := by
    have : (fun s => mat (dual1 W) s) = fun s => (eps l s * ((dt W s : (Qbar l)ˣ) : Qbar l)) • mat W s := by
      funext s; rw [mat_dual1, dt_inv W h2]
    rw [this]; exact (he.mul hdv).smul (Units.continuous_val.comp hW)
  refine Units.continuous_iff.2 ⟨hm, ?_⟩
  have : (fun s => (((dual1 W s)⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l))) =
      fun s => mat (dual1 W) s⁻¹ := by
    funext s; simp [mat, map_inv]
  rw [this]; exact hm.comp continuous_inv

variable [IsAlgClosure ℚ Ω]

theorem cycZ_one {A : ValuationSubring Ω} {v : Pl} (hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) (h : IsPlaceOver A v)
    {σ : G ℚ Ω} (hσ : σ ∈ Ine (F := ℚ) A) : cycZ ℚ Ω l σ = 1 :=
  Units.ext (PadicInt.ext_of_toZModPow.mp fun n => by
    rw [cycZ_toZModPow_eq hl h (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
    simp)

theorem unr_dual1 (S : Finset Pl) (W : R2 Ω l) (hS : ContainsAbove S l)
    (hunr : ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker) :
    ∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ (dual1 W).ker := by
  intro w hw B hB s hs
  have h1 : W s = 1 := hunr w hw B hB hs
  have hl : ((l : ℕ) : 𝓞 ℚ) ∉ w.asIdeal := fun h => hw (hS w h)
  have h2 : cycZ ℚ Ω l s = 1 := cycZ_one hl hB hs
  rw [MonoidHom.mem_ker]
  apply Units.ext
  rw [dual1, tw_val]
  simp [h1, h2, dt, cycBar]

end Twist

section Main

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem isIntegralCocycleOneModPow_of_integral_cocycle (c : Coef l) (n : ℕ) (W : R2 Ω l) (H : Subgroup (G ℚ Ω)) {a : G ℚ Ω → Fin 2 → Qbar l}
    (ha : a ∈ Z1 (Loc.colRep W)) (hint : ∀ s i, a s i ∈ c.O) : Coc1 c n W H a := by
  refine ⟨ha.1.continuousOn, hint, fun s _ t _ => cv_of_eq n ?_⟩
  rw [ha.2 s t, colRep_apply]

theorem unr_smul (W : R2 Ω l) (a : Qbar l) {y : G ℚ Ω → Fin 2 → Qbar l} (h : Unr W y) :
    Unr W (fun s => a • y s) := by
  intro w hw
  obtain ⟨B, hB, x, hx⟩ := h w hw
  exact ⟨B, hB, a • x, fun s hs => by show a • y s = _; rw [hx s hs, Matrix.mulVec_smul, smul_sub]⟩

theorem trivial_cyclotomic_le_det_one (W : R2 Ω l) : N0g W ≤ H0g W := by
  intro g hg
  rw [N0g, Subgroup.mem_inf] at hg
  rw [H0g, Subgroup.mem_inf]
  refine ⟨hg.1, ?_⟩
  have h1 : W g = 1 := hg.2
  rw [MonoidHom.mem_ker]
  simp [dt, h1]

theorem commutator_det_one_le (W : R2 Ω l) : ⁅H0g W, H0g W⁆ ≤ H0g W := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem main : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ES W A → StrZero (dual1 W) A := by
  intro hLit l _ Ω _ _ _ e S A W hN hES z hz hzU hzT
  by_contra hzB
  obtain ⟨c, y, S', hWc, hy, hyc, hyU, hyG, hT⟩ := hES

  obtain ⟨c1, k1, hcc1, hy1int, hy1loc, -, -⟩ := GlobalTheory.T.galois_cocycle_integral_after_scaling l Ω S W c y hN.cont hWc hN.unr hy hyU A
  have hWc1 : ∀ s i j, mat W s i j ∈ c1.O := fun s i j => hcc1 (hWc s i j)
  obtain ⟨c2, k2, hc12, hz2int, hz2loc, hz2triv, -⟩ := GlobalTheory.T.galois_cocycle_integral_after_scaling l Ω S (dual1 W) c1 z
    (cont_dual1 W hN.cont hN.det2) (dual_representation_integral_entries c1 W hWc1 hN.det2) (unr_dual1 S W hN.above hN.unr) hz hzU A
  have hWc2 : ∀ s i j, mat W s i j ∈ c2.O := fun s i j => hc12 (hWc1 s i j)
  set a1 : Qbar l := ((l : ℕ) : Qbar l) ^ k1 with ha1def
  set a2 : Qbar l := ((l : ℕ) : Qbar l) ^ k2 with ha2def
  have hl0 : ((l : ℕ) : Qbar l) ≠ 0 := by
    intro h0
    have := norm_l_lt_one (l := l)
    have h1 : ‖((l : ℕ) : Qbar l)‖ = 0 := by rw [h0, norm_zero]
    have h2 : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := (map_natCast _ _).symm
    rw [h2, norm_algebraMap', Padic.norm_p] at h1
    have : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast (Fact.out : l.Prime).pos)
    linarith
  have ha1 : a1 ≠ 0 := pow_ne_zero _ hl0
  have ha2 : a2 ≠ 0 := pow_ne_zero _ hl0
  set y' : G ℚ Ω → Fin 2 → Qbar l := fun s => a1 • y s with hy'def
  set z' : G ℚ Ω → Fin 2 → Qbar l := fun s => a2 • z s with hz'def
  have hy' : y' ∈ Z1 (Loc.colRep W) := (Z1 (Loc.colRep W)).smul_mem a1 hy
  have hz' : z' ∈ Z1 (Loc.colRep (dual1 W)) := (Z1 (Loc.colRep (dual1 W))).smul_mem a2 hz
  have hy'int : ∀ s i, y' s i ∈ c2.O := fun s i => hc12 (hy1int s i)
  have hz'int : ∀ s i, z' s i ∈ c2.O := fun s i => hz2int s i
  have hy'U : Unr W y' := unr_smul W a1 hyU
  have hz'U : Unr (dual1 W) z' := unr_smul (dual1 W) a2 hzU
  have ha1O : a1 ∈ c2.O := pow_mem (natCast_mem _ _) _
  have hT' : ∀ n : ℕ, 1 ≤ n → ∀ w : Pl, w ∉ S' → l ^ n ∣ normV w - 1 → ∀ ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)),
      KillsMu (normV w) ψ → Function.Surjective ψ → Tame c2 W y' n w ψ :=
    fun n hn w hw hd ψ hK hs => GlobalTheory.T.eulerSystemTameClass_scale_enlarge_coefficients l Ω W c c2 y n w ψ a1 (le_trans hcc1 hc12) ha1O (hT n hn w hw hd ψ hK hs)
  obtain ⟨xA, hxA, hxAe⟩ := hz2triv hzT

  have hloc : ∀ n : ℕ, ∀ v ∈ S, ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧
      Cob2 c2 n (Dec (F := ℚ) B) (cup W y' z') := by
    intro n v _
    by_cases hlv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal
    · obtain ⟨v0, hAv0, hlv0⟩ := hN.atL
      have hv : v = v0 := place_eq (Fact.out : l.Prime) hlv hlv0
      subst hv
      refine ⟨A, hAv0, ?_⟩
      exact GlobalTheory.T.cup_product_coboundary_mod l Ω c2 n W (Dec (F := ℚ) A) y' z' hN.cont hWc2 hN.det2
        (isIntegralCocycleOneModPow_of_integral_cocycle c2 n W _ hy' hy'int) (isIntegralCocycleOneModPow_of_integral_cocycle c2 n (dual1 W) _ hz' hz'int)
        (Or.inr ⟨xA, hxA, fun s hs => cv_of_eq n (hxAe s hs)⟩)
    · obtain ⟨B, hB, -⟩ := hyU v hlv
      obtain ⟨x1, hx1, hx1e⟩ := hy1loc v hlv B hB
      obtain ⟨x2, hx2, hx2e⟩ := hz2loc v hlv B hB
      exact ⟨B, hB, GlobalTheory.T.cupProduct_unramifiedClasses_vanishes hLit l Ω c2 n W v B y' z' hN.cont hWc2 hN.det2 hB hlv
        (isIntegralCocycleOneModPow_of_integral_cocycle c2 n W _ hy' hy'int) (isIntegralCocycleOneModPow_of_integral_cocycle c2 n (dual1 W) _ hz' hz'int)
        ⟨x1, fun i => hc12 (hx1 i), fun s hs => cv_of_eq n (hx1e s hs)⟩
        ⟨x2, hx2, fun s hs => cv_of_eq n (hx2e s hs)⟩⟩

  have hyN : ∃ g ∈ N0g W, y' g ≠ 0 := by
    by_contra h
    push_neg at h
    apply hyG
    refine GlobalTheory.T.greenbergOrdinary_of_vanishing_on_cycloKernel l Ω e S A W hN y hy fun g hg => ?_
    have := h g hg
    exact (smul_eq_zero.mp this).resolve_left ha1
  have hzN : ∃ g ∈ N0g W, z' g ≠ 0 := by
    by_contra h
    push_neg at h
    apply hzB
    refine GlobalTheory.T.tateDual_cocycle_coboundary_of_vanish_on_fixing l Ω e S A W hN z hz fun g hg => ?_
    have := h g hg
    exact (smul_eq_zero.mp this).resolve_left ha2
  obtain ⟨g, hg, h, hh, hne⟩ := GlobalTheory.T.cocycle_pair_alternating_ne_on_cycloKernel l Ω e S A W hN y' hy' z' hz' hyN hzN
  obtain ⟨φ, hφ, hde⟩ := GlobalTheory.T.exists_commutator_det_nonzero l Ω e S A W hN
  have hφH : φ ∈ H0g W := commutator_det_one_le W hφ
  have hgW : W g = 1 := (Subgroup.mem_inf.mp hg).2
  have hhW : W h = 1 := (Subgroup.mem_inf.mp hh).2
  have hcomm : g * h * g⁻¹ * h⁻¹ ∈ ⁅H0g W, H0g W⁆ := by
    have := Subgroup.commutator_mem_commutator (trivial_cyclotomic_le_det_one W hg) (trivial_cyclotomic_le_det_one W hh)
    rwa [commutatorElement_def] at this
  have hφ1 : φ * (g * h * g⁻¹ * h⁻¹) ∈ ⁅H0g W, H0g W⁆ := mul_mem hφ hcomm
  have hmat : mat W (φ * (g * h * g⁻¹ * h⁻¹)) = mat W φ := by
    simp [mat, map_mul, map_inv, hgW, hhW]
  set de : Qbar l := (mat W φ - 1).det with hdedef
  set de' : Qbar l := om (y' h) (z' g) - om (y' g) (z' h) with hde'def
  have hde' : de' ≠ 0 := sub_ne_zero.mpr hne
  have hdeO : ‖de‖ ≤ 1 := norm_le_one_of_mem c2 (det_mem c2 (sub_one_mem c2 (hWc2 φ)))

  have key : ∀ n : ℕ, 1 ≤ n → ‖de ^ 2 * de'‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
    intro n hn
    obtain ⟨u, hu, huint, huS, hucup⟩ := GlobalTheory.T.local_cochains_glue_global hLit l Ω c2 n S (cup W y' z') hN.l_odd hN.above
      (GlobalTheory.T.cupProductDualTwist_isTwoCocycle_unramified l Ω c2 n S W y' z' hN.cont hWc2 hN.det2 hN.above hN.unr hy' hz' hy'int hz'int hy'U hz'U)
      (hloc n)
    have hr := GlobalTheory.T.cohomology_unramified_lift hLit l Ω e S A W hN c2 y' z' u S' n hn hWc2 hy' hz' hy'int hz'int hy'U hz2loc
      ⟨xA, hxA, hxAe⟩ (hT' n hn) hu huint huS hucup
    have hc := GlobalTheory.T.height_commutator_invariance l Ω n c2 W y' z' u hWc2 hy' hz' hucup φ hφH g hg h hh
    have h0 := hr φ hφ
    have h1 := hr _ hφ1
    rw [hmat] at h1
    unfold Cg at h0 h1 hc
    rw [sub_zero] at h0 h1
    set L := ‖((l : ℕ) : Qbar l) ^ n‖
    set t1 := ht W y' z' u (φ * (g * h * g⁻¹ * h⁻¹))
    set t0 := ht W y' z' u φ
    have e1 : de ^ 2 * de' = de * (de * de' - (t1 - t0)) + de * t1 - de * t0 := by ring
    have b1 : ‖de * (de * de' - (t1 - t0))‖ ≤ L := by
      rw [norm_mul, norm_sub_rev]
      calc ‖de‖ * ‖t1 - t0 - de * de'‖ ≤ 1 * L := by
            gcongr
        _ = L := one_mul L
    rw [e1]
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (by rw [norm_neg]; exact h0))
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le b1 h1)
  have hx0 : de ^ 2 * de' ≠ 0 := mul_ne_zero (pow_ne_zero 2 hde) hde'
  have hpos : 0 < ‖de ^ 2 * de'‖ := norm_pos_iff.mpr hx0
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos (norm_l_lt_one (l := l))
  have hk := key (n + 1) (by omega)
  rw [norm_pow] at hk
  have hmono : ‖((l : ℕ) : Qbar l)‖ ^ (n + 1) ≤ ‖((l : ℕ) : Qbar l)‖ ^ n :=
    pow_le_pow_of_le_one (norm_nonneg _) (norm_l_lt_one (l := l)).le (by omega)
  linarith

end Main

end GlobalTheory.Ord2.StrictKill
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StrictVanishingDualOfLiteratureStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strict_vanishing_dual_of_literature : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ES W A → StrZero (dual1 W) A := by
  first | exact @GlobalTheory.Ord2.StrictKill.main | exact GlobalTheory.Ord2.StrictKill.main | (intros; apply GlobalTheory.Ord2.StrictKill.main <;> assumption)
end
