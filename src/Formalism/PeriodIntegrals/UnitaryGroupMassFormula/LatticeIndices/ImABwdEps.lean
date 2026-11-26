module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImASubKpp
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.SplitTransport

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImAInModPSplit
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImAGOthNotDvd
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.ImAGNonunit
noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge MassDataIdxStIm PI.MassDataKppVolLemmas
open scoped TensorProduct Matrix Pointwise

variable {D : D7} (X : HidaSetting D)

def eC : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F := 1 - X.ew - sigA X.B.I X.ew

theorem imA_eC_idem : eC X * eC X = eC X := by
  have h1 := X.ew_idem
  have h2 := X.ew_orth
  have h3 : sigA X.B.I X.ew * sigA X.B.I X.ew = sigA X.B.I X.ew := by rw [← map_mul, h1]
  simp only [eC]
  linear_combination h1 + h3 + 2 * h2

theorem imA_mL_mem (m : ℕ) {b : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F}
    (hb' : b ∈ mL X.B.I m) : ∃ x ∈ X.B.I.Lf, b = (m : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • x := by
  induction hb' using Submodule.span_induction with
  | mem y hy => exact hy
  | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
  | add y z _ _ hy hz =>
    obtain ⟨y', hy', rfl⟩ := hy
    obtain ⟨z', hz', rfl⟩ := hz
    exact ⟨y' + z', add_mem hy' hz', (smul_add _ _ _).symm⟩
  | smul c y _ hy =>
    obtain ⟨y', hy', rfl⟩ := hy
    refine ⟨c • y', Submodule.smul_mem _ c hy', ?_⟩
    show (c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • _ = _ • ((c : X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) • y')
    rw [smul_smul, smul_smul, mul_comm]

theorem imA_lat_fg (p : TypX X) : (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).FG := by
  classical
  obtain ⟨m, b, hb', -, he⟩ := MassDataIdxK.latImage p.1 X.B.I.L X.B.I.L_span X.B.I.L_fg
  refine ⟨(Finset.univ.image b), le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact hb' i
  · intro x hx
    have hx' : x ∈ (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) :
        Set (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E)) := hx
    rw [he] at hx'
    obtain ⟨c, hc, rfl⟩ := hx'
    refine Submodule.sum_mem _ fun i _ => ?_
    have : c i • b i = (⟨c i, hc i (Set.mem_univ _)⟩ : p.1.adicCompletionIntegers X.B.I.F) • b i := rfl
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))

theorem imA_g_nonunit (p : TypX X) : ¬ IsUnit ((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F) := by
  intro hu
  have hr : ResArith X p := by
    have hgp : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
    have hmem : ((gOf p : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
      have hty := (mem_typSet X.B.I.F (D.host.g 0) (D.host.g 1) (D.host.g_prime 0).ne_zero
        (D.host.g_prime 1).ne_zero p.1).1 p.2
      unfold gOf
      split_ifs with h
      · exact h
      · exact hty.resolve_left h
    have hsplit : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.E) |
        ((gOf p : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ X.B.I.E := by
      unfold gOf
      split_ifs
      · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 0)
      · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 1)
    obtain ⟨he, hf⟩ := MassDataIdxRes.locDeg_one_below (F := X.B.I.F) (E := X.B.I.E) (gOf p) hsplit p.1 hmem
    obtain ⟨hc, hn⟩ := MassDataIdxRes.arith_of_loc (gOf p) p.1 hmem he hf
    exact ⟨hc, hmem, hn⟩
  obtain ⟨π, -, -⟩ : StResZ X p := stResZ_of X p hr
  have hd : gOf p ∣ X.B.g := by
    rw [X.g_eq]; unfold gOf; split_ifs
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  have hu' : IsUnit ((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) :=
    isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) hu
  have h0 : π ((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) = 0 := by
    rw [map_natCast, ZMod.natCast_self]
  have : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  have h1 := hu'.map π
  rw [h0] at h1
  exact not_isUnit_zero h1

theorem imA_n_pos : 0 < X.B.I.n := by
  rw [X.n_eq]
  have := D.R.two_le_m
  unfold Formalism.BasicNotions.Ranks.r
  omega

theorem imA_ew_split (p : TypX X) :
    PI.FinKW.psiV X.B.I p.1 X.ew + PI.FinKW.psiV X.B.I p.1 (sigA X.B.I X.ew) = 1 := by
  set ε := PI.FinKW.psiV X.B.I p.1 (eC X) with hε
  have hεi : ε * ε = ε := by rw [hε, ← map_mul, imA_eC_idem]
  let φ : (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) →ₗ[p.1.adicCompletionIntegers X.B.I.F]
      (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) :=
    { toFun := fun u => ε • u
      map_add' := fun u w => smul_add _ _ _
      map_smul' := fun c u => smul_comm _ _ _ }
  have hφ : (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).map φ ≤
      Ideal.span {((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} •
        latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    rw [Submodule.map_le_iff_le_comap]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨l, hl, rfl⟩
    show ε • ratV (F := X.B.I.F) (Fv X.B.I.F p.1) l ∈
      Ideal.span {((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} •
        latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
    have hin : (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (l i)) ∈ X.B.I.Lf :=
      Submodule.subset_span ⟨⟨l, hl⟩, rfl⟩
    obtain ⟨y, hy, he⟩ := imA_mL_mem X X.B.g (X.ew_full _ hin)
    have hv : PI.FinKW.vecV X.B.I p.1 (fun i => Formalism.UG.inclE (F := X.B.I.F) (Formalism.MainNotions.S.Af X.B.I.F) (l i)) =
        ratV (F := X.B.I.F) (Fv X.B.I.F p.1) l := by
      funext i
      simp [PI.FinKW.vecV, PI.FinKW.psiV, Formalism.UG.inclE, ratV, inclR]
    have h2 := congrArg (PI.FinKW.vecV X.B.I p.1) he
    rw [imA_vecV_smul', imA_vecV_smul', hv, map_natCast] at h2
    have h3 : ε • ratV (F := X.B.I.F) (Fv X.B.I.F p.1) l =
        ((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F) • PI.FinKW.vecV X.B.I p.1 y := by
      rw [Nat.cast_smul_eq_nsmul] at h2
      rw [hε, Nat.cast_smul_eq_nsmul]
      exact h2
    rw [h3]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _)
      (PI.FinKW.LocTo.mem_local_lattice_iff X.B.I y hy p.1)
  have hφφ : φ.comp φ = φ := LinearMap.ext fun u => by
    show ε • ε • u = ε • u
    rw [smul_smul, hεi]
  have hN : (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).map φ ≤
      Ideal.span {((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} •
        (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).map φ := by
    calc _ = ((latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).map φ).map φ := by
            rw [← Submodule.map_comp, hφφ]
      _ ≤ _ := Submodule.map_mono hφ
      _ = _ := Submodule.map_smul'' _ _ _
  have hjac : Ideal.span {((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff]
    exact (IsLocalRing.mem_maximalIdeal _).mpr (imA_g_nonunit X p)
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ ((imA_lat_fg X p).map φ) hN hjac
  have hz : ∀ l ∈ X.B.I.L, ε • ratV (F := X.B.I.F) (Fv X.B.I.F p.1) l = 0 := by
    intro l hl
    have : φ (ratV (F := X.B.I.F) (Fv X.B.I.F p.1) l) ∈
        (latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).map φ :=
      Submodule.mem_map_of_mem (Submodule.subset_span ⟨l, hl, rfl⟩)
    rw [hbot] at this
    exact this
  have hex : ∃ l ∈ X.B.I.L, l ≠ 0 := by
    by_contra h
    simp only [not_exists, not_and, not_not] at h
    have hs := X.B.I.L_span
    rw [Submodule.span_eq_bot.mpr h] at hs
    have i0 : Fin X.B.I.n := ⟨0, imA_n_pos X⟩
    have hm : (Pi.single i0 (1 : X.B.I.E) : Fin X.B.I.n → X.B.I.E) ∈ (⊥ : Submodule X.B.I.E _) := by
      rw [hs]; exact Submodule.mem_top
    rw [Submodule.mem_bot] at hm
    have := congrFun hm i0
    simp at this
  obtain ⟨l, hl, hl0⟩ := hex
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hl0
  have h0 := congrFun (hz l hl) i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h0
  have hu : IsUnit (ratV (F := X.B.I.F) (Fv X.B.I.F p.1) l i) :=
    (isUnit_iff_ne_zero.mpr hi).map (inclR (F := X.B.I.F) (Fv X.B.I.F p.1))
  have hε0 : ε = 0 := (hu.mul_left_eq_zero).mp h0
  rw [hε, eC, map_sub, map_sub, map_one] at hε0
  linear_combination -hε0

end MassDataIdxSteps
end
end

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting

variable {D : D7} (X : HidaSetting D)


open Classical in
def gOth (p : TypX X) : ℕ := if ((D.host.g 0 : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal then D.host.g 1 else D.host.g 0

theorem imA_g_eq_mul (p : TypX X) : X.B.g = gOf p * gOth X p := by
  rw [X.g_eq]; unfold gOf gOth; split_ifs
  · rfl
  · exact mul_comm _ _

private theorem gOf_coprime_gOth (p : TypX X) : Nat.Coprime (gOf p) (gOth X p) := by
  have h0 := D.host.g_prime 0
  have h1 := D.host.g_prime 1
  have hne := D.host.g_ne
  unfold gOth gOf
  split_ifs
  · exact (Nat.coprime_primes h0 h1).2 hne
  · exact (Nat.coprime_primes h1 h0).2 hne.symm

private theorem le_exp_sub_one_of_lt_exp' (y : WithZero (Multiplicative ℤ)) (k : ℤ) (h : y < WithZero.exp k) :
    y ≤ WithZero.exp (k - 1) := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact zero_le'
  · rw [← WithZero.exp_log hy] at h ⊢
    rw [WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

private theorem exp_add_one_le_of_exp_lt (y : WithZero (Multiplicative ℤ)) (k : ℤ) (h : WithZero.exp k < y) :
    WithZero.exp (k + 1) ≤ y := by
  have hy : y ≠ 0 := (lt_of_le_of_lt zero_le' h).ne'
  rw [← WithZero.exp_log hy] at h ⊢
  rw [WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]
  omega

theorem imA_span_g_max (p : TypX X) :
    Ideal.span {((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} =
      IsLocalRing.maximalIdeal (p.1.adicCompletionIntegers X.B.I.F) := by
  have hmem : ((gOf p : ℕ) : 𝓞 X.B.I.F) ∈ p.1.asIdeal := by
    have hty := (mem_typSet X.B.I.F (D.host.g 0) (D.host.g 1) (D.host.g_prime 0).ne_zero
      (D.host.g_prime 1).ne_zero p.1).1 p.2
    unfold gOf
    split_ifs with h
    · exact h
    · exact hty.resolve_left h
  have hgp : Fact (gOf p).Prime := ⟨gOf_prime X p⟩
  have hsplit : {w : IsDedekindDomain.HeightOneSpectrum (𝓞 X.B.I.E) |
      ((gOf p : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ X.B.I.E := by
    unfold gOf
    split_ifs
    · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 0)
    · exact MassDataIdxRes.split_transport X.ιE _ (D.nd.g_split 1)
  obtain ⟨he, hf⟩ := MassDataIdxRes.locDeg_one_below (F := X.B.I.F) (E := X.B.I.E) (gOf p) hsplit p.1 hmem
  obtain ⟨_, hnot⟩ := MassDataIdxRes.arith_of_loc (gOf p) p.1 hmem he hf
  have hvg : Valued.v (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F) =
      p.1.intValuation ((gOf p : ℕ) : 𝓞 X.B.I.F) := by
    have e : (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F) =
        (((gOf p : ℕ) : X.B.I.F) : p.1.adicCompletion X.B.I.F) := by
      first
        | rfl
        | exact (map_natCast (algebraMap X.B.I.F (p.1.adicCompletion X.B.I.F)) (gOf p)).symm
        | norm_cast
        | simp
    rw [e, IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
      ← map_natCast (algebraMap (𝓞 X.B.I.F) X.B.I.F) (gOf p),
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  have hle1 : p.1.intValuation ((gOf p : ℕ) : 𝓞 X.B.I.F) ≤ WithZero.exp (-1 : ℤ) := by
    have := (IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem p.1
      ((gOf p : ℕ) : 𝓞 X.B.I.F) 1).2 (by simpa using hmem)
    simpa using this
  have hgt2 : WithZero.exp (-2 : ℤ) < p.1.intValuation ((gOf p : ℕ) : 𝓞 X.B.I.F) := by
    by_contra hc
    push_neg at hc
    exact hnot ((IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_mem p.1
      ((gOf p : ℕ) : 𝓞 X.B.I.F) 2).1 (by simpa using hc))
  have hge1 : WithZero.exp (-1 : ℤ) ≤ p.1.intValuation ((gOf p : ℕ) : 𝓞 X.B.I.F) := by
    have := exp_add_one_le_of_exp_lt _ (-2) hgt2
    norm_num at this
    exact this
  have hg0 : (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F) ≠ 0 := by
    intro h
    have h' := hvg
    rw [h, map_zero] at h'
    exact (lt_of_le_of_lt zero_le' hgt2).ne' h'.symm
  apply le_antisymm
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, ReciprocityTheory.Aut.mem_maxIdeal_iff, hvg]
    refine lt_of_le_of_lt hle1 ?_
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  · intro x hx
    rw [ReciprocityTheory.Aut.mem_maxIdeal_iff] at hx
    rw [Ideal.mem_span_singleton]
    have hx1 : Valued.v (x : p.1.adicCompletion X.B.I.F) ≤ WithZero.exp (-1 : ℤ) := by
      have := le_exp_sub_one_of_lt_exp' _ 0 (by rwa [WithZero.exp_zero])
      norm_num at this
      exact this
    have hq : Valued.v ((x : p.1.adicCompletion X.B.I.F) /
        (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F)) ≤ 1 := by
      rw [map_div₀, hvg, div_le_one₀ (lt_of_le_of_lt zero_le' hgt2)]
      exact hx1.trans hge1
    refine ⟨⟨(x : p.1.adicCompletion X.B.I.F) /
        (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F),
      (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 hq⟩, ?_⟩
    apply Subtype.ext
    show (x : p.1.adicCompletion X.B.I.F) =
      (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F) *
        ((x : p.1.adicCompletion X.B.I.F) /
          (((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) : p.1.adicCompletion X.B.I.F))
    field_simp

theorem imA_gOth_unit (p : TypX X) : IsUnit ((gOth X p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) := by
  by_contra hnu
  have hm : ((gOth X p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) ∈
      IsLocalRing.maximalIdeal (p.1.adicCompletionIntegers X.B.I.F) :=
    (IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 hnu)
  rw [← imA_span_g_max X p, Ideal.mem_span_singleton] at hm
  have hc : IsCoprime ((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F)
      ((gOth X p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) := by
    have hz : IsCoprime ((gOf p : ℕ) : ℤ) ((gOth X p : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.2 (gOf_coprime_gOth X p)
    simpa using hz.map (Int.castRingHom (p.1.adicCompletionIntegers X.B.I.F))
  have hu : IsUnit ((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F) := hc.isUnit_of_dvd' dvd_rfl hm
  have htop := (IsLocalRing.maximalIdeal.isMaximal (p.1.adicCompletionIntegers X.B.I.F)).ne_top
  rw [← imA_span_g_max X p, Ne, Ideal.span_singleton_eq_top] at htop
  exact htop hu

theorem imA_span_Bg (p : TypX X) :
    Ideal.span {((X.B.g : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} =
      Ideal.span {((gOf p : ℕ) : p.1.adicCompletionIntegers X.B.I.F)} := by
  rw [imA_g_eq_mul X p, Nat.cast_mul]
  exact Ideal.span_singleton_mul_right_unit (imA_gOth_unit X p) _

end MassDataIdxSteps
end
end

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting
open scoped TensorProduct Matrix

variable {D : D7} (X : HidaSetting D)

theorem imA_inModP_Bg (p : TypX X) (S : Set (Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E))
    (y : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) :
    InModP X p X.B.g S y ↔ InModP X p (gOf p) S y := by
  unfold InModP
  rw [imA_span_Bg X p]

theorem imA_OEp_one (p : TypX X) : (1 : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E) ∈ OEp X p :=
  ⟨1, Subring.one_mem _, map_one _⟩

theorem imA_OEp_sub (p : TypX X) {s t : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E} (hs : s ∈ OEp X p)
    (ht : t ∈ OEp X p) : s - t ∈ OEp X p := by
  obtain ⟨a, ha, rfl⟩ := hs
  obtain ⟨b, hb, rfl⟩ := ht
  exact ⟨a - b, Subring.sub_mem _ ha hb, map_sub _ _ _⟩

abbrev epsP (p : TypX X) : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E := PI.FinKW.psiV X.B.I p.1 X.ew

theorem imA_eps_mem (p : TypX X) : epsP X p ∈ OEp X p := ⟨X.ew, X.ew_int, rfl⟩

theorem imA_eps_idem (p : TypX X) : epsP X p * epsP X p = epsP X p := by
  unfold epsP
  rw [← map_mul, X.ew_idem]

private theorem latLoc_ringOfIntegers_incl (p : TypX X) (x : 𝓞 X.B.I.E) {u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hu : u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    ((1 : Fv X.B.I.F p.1) ⊗ₜ[X.B.I.F] (algebraMap (𝓞 X.B.I.E) X.B.I.E x)) • u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  unfold latLoc at hu ⊢
  induction hu using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨l, hl, rfl⟩ := hw
    refine Submodule.subset_span ⟨x • l, X.B.I.L.smul_mem x hl, ?_⟩
    funext i
    simp [ratV, inclR, Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul]
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul c a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ c ha

private theorem latLoc_adicIntegers_incl (p : TypX X) (c : p.1.adicCompletionIntegers X.B.I.F) {u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hu : u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    ((c : Fv X.B.I.F p.1) ⊗ₜ[X.B.I.F] (1 : X.B.I.E)) • u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  have h : ((c : Fv X.B.I.F p.1) ⊗ₜ[X.B.I.F] (1 : X.B.I.E)) • u = c • u := by
    funext i
    simp [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
  rw [h]
  exact Submodule.smul_mem _ c hu

theorem imA_lat_OEp (p : TypX X) {t : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E} (ht : t ∈ OEp X p)
    {u : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}
    (hu : u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))) :
    t • u ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
  have key : ∀ b ∈ Formalism.MainNotions.S.IntAf X.B.I.F X.B.I.E, ∀ w ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)),
      PI.FinKW.psiV X.B.I p.1 b • w ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) := by
    intro b hb
    unfold Formalism.MainNotions.S.IntAf Formalism.UG.tensInt at hb
    induction hb using Subring.closure_induction with
    | mem z hz =>
      intro w hw
      rcases hz with ⟨⟨e, he⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩
      · obtain ⟨x, rfl⟩ := RingHom.mem_range.mp he
        convert latLoc_ringOfIntegers_incl X p x hw using 2
        simp [PI.FinKW.psiV]
      · have hy' : ∀ v, y v ∈ v.adicCompletionIntegers X.B.I.F := hy
        convert latLoc_adicIntegers_incl X p ⟨y p.1, hy' p.1⟩ hw using 2
        simp [PI.FinKW.psiV] <;> rfl
    | zero => intro w _; simp
    | one => intro w hw; simpa using hw
    | add a b _ _ ha hb => intro w hw; rw [map_add (f := _), add_smul]; exact add_mem (ha w hw) (hb w hw)
    | neg a _ ha => intro w hw; rw [map_neg, neg_smul]; exact neg_mem (ha w hw)
    | mul a b _ _ ha hb => intro w hw; rw [map_mul, mul_smul]; exact ha _ (hb w hw)
  obtain ⟨a, ha, rfl⟩ := ht
  exact key a ha u hu

end MassDataIdxSteps
end
end

noncomputable section

namespace MassDataIdxSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting
open scoped TensorProduct Matrix

variable {D : D7} (X : HidaSetting D)

theorem imA_eps'_eq (p : TypX X) :
    1 - epsP X p = PI.FinKW.psiV X.B.I p.1 (sigA X.B.I X.ew) := by
  have h := imA_ew_split X p
  rw [epsP]
  linear_combination -h

theorem imA_bw_eps (p : TypX X) (i : Fin D.R.k) :
    epsP X p • PI.FinKW.vecV X.B.I p.1 (X.bw i) = PI.FinKW.vecV X.B.I p.1 (X.bw i) := by
  conv_rhs => rw [X.bw_w i]
  rw [imA_vecV_smul']

end MassDataIdxSteps
