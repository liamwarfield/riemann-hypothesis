module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHilbertEisensteinFourierCoeffFamily
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelHilbertEisensteinQuasiPeriod

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetGaloisConjCoefficients
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinSeriesRingEquivConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinFourierCoeffRingEquivConj
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem ecoef_ringEquiv : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (N : ℕ) (g : ℂ ≃+* ℂ) (m : ℤ) (π : Equiv.Perm (Emb F)) (μ : Emb F → ℕ) (n : ℕ), 0 < N → IsCoef k 𝔞 𝔟 a₀ a → g a₀ = a₀ → HasLevel N (split 𝔞 𝔟 x) → g (Complex.exp ((2 * Real.pi * Complex.I) / N)) = Complex.exp ((2 * Real.pi * Complex.I) * m / N) → (∀ (i : Emb F) (y : F), g ((i y : ℝ) : ℂ) = ((π i y : ℝ) : ℂ)) → g (ecoef N a x μ n) = ecoef N a (m * x) (fun j ↦ μ (π.symm j)) n := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x N g m π μ n hN hco hg0 hlev hζ hemb
  obtain ⟨h0, hint, hsupp, -⟩ := hco
  have hmap : ∀ {ι : Sort _} (f : ι → ℂ), g (∑ᶠ i, f i) = ∑ᶠ i, g (f i) :=
    fun f ↦ AddEquiv.map_finsum g.toAddEquiv f
  have hmapP : ∀ {p : Prop} (f : p → ℂ), g (∑ᶠ i, f i) = ∑ᶠ i, g (f i) :=
    fun f ↦ AddEquiv.map_finsum g.toAddEquiv f
  have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast hN.ne'

  have hprod : ∀ ξ : F, g (∏ i : Emb F, ((i ξ : ℝ) : ℂ) ^ μ i) = ∏ j : Emb F, ((j ξ : ℝ) : ℂ) ^ μ (π.symm j) := by
    intro ξ
    rw [map_prod]
    simp only [map_pow, hemb]
    exact Equiv.prod_comp π (fun j ↦ ((j ξ : ℝ) : ℂ) ^ μ (π.symm j)) |>.symm ▸ by
      simp only [Equiv.symm_apply_apply]

  have hchar : ∀ ξ : F, ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) → g (eTr (ξ * x)) = eTr (ξ * ((m : F) * x)) := by
    intro ξ hξ
    obtain ⟨r, hr⟩ := (GlobalTheory.T.splitLattice_level_trace_denominator F N 𝔞 𝔟 x ξ hlev hξ).2
    have ht : Algebra.trace ℚ F (ξ * x) = (r : ℚ) / N := by
      rw [eq_div_iff hNq, mul_comm]; exact hr
    have hsm : ξ * ((m : F) * x) = (m : ℚ) • (ξ * x) := by
      rw [Algebra.smul_def, map_intCast]; ring
    have ht' : Algebra.trace ℚ F (ξ * ((m : F) * x)) = (m : ℚ) * ((r : ℚ) / N) := by
      rw [hsm, LinearMap.map_smul, smul_eq_mul, ht]
    have e1 : eTr (ξ * x) = Complex.exp ((2 * Real.pi * Complex.I) / N) ^ r := by
      rw [eTr, ht, ← Complex.exp_int_mul]; congr 1; push_cast; ring
    rw [e1, map_zpow₀, hζ, ← Complex.exp_int_mul, eTr, ht']
    congr 1; push_cast; ring
  have key : ∀ ξ : F, g (a ξ * eTr (ξ * x) * ∏ i : Emb F, ((i ξ : ℝ) : ℂ) ^ μ i) =
      a ξ * eTr (ξ * ((m : F) * x)) * ∏ j : Emb F, ((j ξ : ℝ) : ℂ) ^ μ (π.symm j) := by
    intro ξ
    by_cases ha : a ξ = 0
    · simp [ha]
    have hga : g (a ξ) = a ξ := by
      by_cases hξ0 : ξ = 0
      · subst hξ0; rw [h0]; exact hg0
      · obtain ⟨z, hz⟩ := hint ξ hξ0; rw [hz, map_intCast]
    have hmem : ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) := by
      by_cases hξ0 : ξ = 0
      · subst hξ0; exact Submodule.zero_mem _
      · exact (hsupp ξ hξ0 ha).1
    rw [map_mul, map_mul, hga, hchar ξ hmem, hprod]
  unfold ecoef
  rw [hmap]
  refine finsum_congr fun ξ ↦ ?_
  rw [hmapP]
  refine finsum_congr fun _ ↦ ?_
  exact key ξ

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinSeriesRingEquivConj
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
private lemma powerSeries_map_mk' (g : ℂ ≃+* ℂ) (c : ℕ → ℂ) :
    PowerSeries.map (g : ℂ →+* ℂ) (PowerSeries.mk c) = PowerSeries.mk fun n ↦ g (c n) := by
  ext n
  simp

open NumberField UpperHalfPlane in
open scoped Classical MatrixGroups nonZeroDivisors in
theorem _root_.GlobalTheory.HilbFam.hser_conj : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (s N : ℕ) (g : ℂ ≃+* ℂ) (m : ℤ) (π : Equiv.Perm (_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F)) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ) (c : ℕ → ℂ) (n : ℕ), k = 2 * s → 0 < N → _root_.GlobalTheory.HilbFam.IsCoef k 𝔞 𝔟 a₀ a → g a₀ = a₀ → _root_.GlobalTheory.HilbFam.HasLevel N (_root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x) → g (Complex.exp ((2 * Real.pi * Complex.I) / N)) = Complex.exp ((2 * Real.pi * Complex.I) * m / N) → (∀ (i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) (y : F), g ((i y : ℝ) : ℂ) = ((π i y : ℝ) : ℂ)) → g (PowerSeries.coeff n (_root_.GlobalTheory.HilbFam.hser k N 𝔞 a x κ c)) = PowerSeries.coeff n (_root_.GlobalTheory.HilbFam.hser k N 𝔞 a (m * x) (fun j ↦ κ (π.symm j)) (fun n ↦ g (c n))) := by
  intro F _ _ _ k 𝔞 𝔟 a₀ a x s N g m π κ c n hk hN ha hga hlev hexp hemb
  have htr : ∀ μ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ,
      PowerSeries.map (g : ℂ →+* ℂ) (PowerSeries.mk (_root_.GlobalTheory.HilbFam.ecoef N a x μ)) =
        PowerSeries.mk (_root_.GlobalTheory.HilbFam.ecoef N a (m * x) fun j ↦ μ (π.symm j)) := by
    intro μ
    rw [powerSeries_map_mk']
    congr 1
    funext j
    exact _root_.GlobalTheory.HilbFam.ecoef_ringEquiv F k 𝔞 𝔟 a₀ a x N g m π μ j hN ha hga hlev
      hexp hemb
  unfold _root_.GlobalTheory.HilbFam.hser
  subst hk
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_smul, map_sum, smul_eq_mul, _root_.GlobalTheory.HilbFam.omegaFactor_pow_two_mul]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, map_ratCast, map_sum]
  congr 1
  refine Finset.sum_nbij' (fun μ j ↦ μ (π.symm j)) (fun μ i ↦ μ (π i)) ?_ ?_ ?_ ?_ ?_
  · intro μ hμ
    simp only [Finset.mem_coe, Finset.mem_Iic] at hμ ⊢
    exact fun j ↦ hμ (π.symm j)
  · intro μ hμ
    simp only [Finset.mem_coe, Finset.mem_Iic] at hμ ⊢
    intro i
    simpa using hμ (π i)
  · intro μ _
    funext i
    simp
  · intro μ _
    funext j
    simp
  · intro μ _
    have hcoeff : ∀ φ : PowerSeries ℂ,
        g (PowerSeries.coeff n φ) = PowerSeries.coeff n (PowerSeries.map (g : ℂ →+* ℂ) φ) :=
      fun φ ↦ by
        rw [PowerSeries.coeff_map]
        rfl
    rw [map_mul, map_intCast, hcoeff, map_mul, map_pow, powerSeries_map_mk', htr]
    rw [Equiv.prod_comp π.symm fun i ↦
        _root_.GlobalTheory.HilbFam.rco (2 * s) (κ i) (μ i) * (-1) ^ μ i,
      Equiv.sum_comp π.symm fun i ↦ κ i - μ i]

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinSeriesRingEquivConjStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertEisensteinSeries_ringEquiv_conj : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (k : ℕ) (𝔞 𝔟 : Frac F) (a₀ : ℂ) (a : F → ℂ) (x : F) (s N : ℕ) (g : ℂ ≃+* ℂ) (m : ℤ) (π : Equiv.Perm (Emb F)) (κ : Emb F → ℕ) (c : ℕ → ℂ) (n : ℕ), k = 2 * s → 0 < N → IsCoef k 𝔞 𝔟 a₀ a → g a₀ = a₀ → HasLevel N (split 𝔞 𝔟 x) → g (Complex.exp ((2 * Real.pi * Complex.I) / N)) = Complex.exp ((2 * Real.pi * Complex.I) * m / N) → (∀ (i : Emb F) (y : F), g ((i y : ℝ) : ℂ) = ((π i y : ℝ) : ℂ)) → g (PowerSeries.coeff n (hser k N 𝔞 a x κ c)) = PowerSeries.coeff n (hser k N 𝔞 a (m * x) (fun j ↦ κ (π.symm j)) (fun n ↦ g (c n))) := by
  first | exact @GlobalTheory.HilbFam.hser_conj | exact GlobalTheory.HilbFam.hser_conj | (intros; apply GlobalTheory.HilbFam.hser_conj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSplitLatticeTwistDiagonalCoprime
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSplitLatticeTwistDiagonalCoprime
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

theorem twist_split_diagonal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (𝔞 𝔟 : Frac F) (x : F) (a : ℤ), IsCoprime a (N : ℤ) → HasLevel N (split 𝔞 𝔟 x) → twist N (split 𝔞 𝔟 x) (Matrix.diagonal ![1, (a : ZMod N)]) = split 𝔞 𝔟 (a * x) := by
  intro F _ _ _ N 𝔞 𝔟 x a hcop hlev
  have hstd : ∀ w : Fin 2 → F, w ∈ stdLat F ↔ ∀ i, w i ∈ (1 : Submodule (𝓞 F) F) := by
    intro w; simp only [stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff]
  have hsp : ∀ (z : F) (w : Fin 2 → F), w ∈ split 𝔞 𝔟 z ↔
      w 0 ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) : Submodule (𝓞 F) F) ∧
      w 1 - w 0 * z ∈ (latM 𝔞 : Submodule (𝓞 F) F) := fun _ _ ↦ Iff.rfl
  have hA : (Matrix.diagonal ![1, (a : ZMod N)]) =
      (Matrix.diagonal ![(1 : ℤ), a]).map (Int.cast : ℤ → ZMod N) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hv0 : ∀ y : Fin 2 → F,
      Matrix.vecMul y ((Matrix.diagonal ![(1 : ℤ), a]).map (Int.cast : ℤ → F)) = ![y 0, a * y 1] := by
    intro y
    ext j; fin_cases j <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, mul_comm]
  have hN : ∀ w ∈ stdLat F, (N : F) • w ∈ split 𝔞 𝔟 x := by
    intro w hw
    have h := hlev.1 w hw
    rw [Nat.cast_smul_eq_nsmul] at h ⊢
    exact h
  have hz : ∀ (n : ℤ) (S : Submodule (𝓞 F) F) (m : F), m ∈ S → (n : F) * m ∈ S := by
    intro n S m hm
    rw [← zsmul_eq_mul]
    exact zsmul_mem hm n
  ext v
  rw [hA, GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N _ _ v hlev.2]
  constructor
  · rintro ⟨y, hy, w, hw, rfl⟩
    rw [hv0]
    have hw' := (hstd w).1 hw
    have h0 := (hsp _ _).1 (hN ![w 0, 0] ((hstd _).2 (by
      intro i; fin_cases i
      · exact hw' 0
      · exact Submodule.zero_mem _)))
    have h1 := (hsp _ _).1 (hN ![0, w 1] ((hstd _).2 (by
      intro i; fin_cases i
      · exact Submodule.zero_mem _
      · exact hw' 1)))
    have hy' := (hsp _ _).1 hy
    rw [hsp]
    refine ⟨?_, ?_⟩
    · have := Submodule.add_mem _ hy'.1 h0.1
      convert this using 1
      simp
    · have := Submodule.add_mem _ (Submodule.add_mem _ (hz a _ _ hy'.2) h1.2) (hz a _ _ h0.2)
      convert this using 1
      simp
      ring
  · intro hv
    have hv' := (hsp _ _).1 hv
    obtain ⟨u, t, hut⟩ := hcop
    have hut' : (u : F) * a + t * N = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → F) hut
    have hm : ![0, v 1 - v 0 * (a * x)] ∈ split 𝔞 𝔟 x := by
      rw [hsp]
      refine ⟨Submodule.zero_mem _, ?_⟩
      convert hv'.2 using 1
      simp
    have hm' := (hstd _).1 (hlev.2 hm) 1
    refine ⟨![v 0, v 0 * x + u * (v 1 - v 0 * (a * x))], ?_, ![0, t * (v 1 - v 0 * (a * x))], ?_, ?_⟩
    · rw [hsp]
      refine ⟨hv'.1, ?_⟩
      convert hz u _ _ hv'.2 using 1
      simp
    · rw [hstd]
      intro i; fin_cases i
      · exact Submodule.zero_mem _
      · exact hz t _ _ hm'
    · rw [hv0]
      ext j; fin_cases j
      · simp
      · simp
        linear_combination (-(v 1 - v 0 * (a * x))) * hut'

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertSplitLatticeTwistDiagonalCoprimeStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertSplitLattice_twist_diagonal_coprime : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (𝔞 𝔟 : Frac F) (x : F) (a : ℤ), IsCoprime a (N : ℤ) → HasLevel N (split 𝔞 𝔟 x) → twist N (split 𝔞 𝔟 x) (Matrix.diagonal ![1, (a : ZMod N)]) = split 𝔞 𝔟 (a * x) := by
  first | exact @GlobalTheory.HilbFam.twist_split_diagonal | exact GlobalTheory.HilbFam.twist_split_diagonal | (intros; apply GlobalTheory.HilbFam.twist_split_diagonal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutEmbInjective
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam

noncomputable def autEmb {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (g : ℂ ≃+* ℂ) (i : Emb F) : Emb F :=
  (IsTotallyReal.complexEmbedding_isReal (g.toRingHom.comp ((algebraMap ℝ ℂ).comp i))).embedding

theorem autEmb_apply {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (g : ℂ ≃+* ℂ) (i : Emb F) (y : F) :
    ((autEmb g i y : ℝ) : ℂ) = g ((i y : ℝ) : ℂ) :=
  (IsTotallyReal.complexEmbedding_isReal (g.toRingHom.comp ((algebraMap ℝ ℂ).comp i))).coe_embedding_apply y

theorem autEmb_injective {F : Type} [Field F] [NumberField F] [IsTotallyReal F] (g : ℂ ≃+* ℂ) :
    Function.Injective (autEmb (F := F) g) := by
  intro i j h
  ext y
  have h1 : g ((i y : ℝ) : ℂ) = g ((j y : ℝ) : ℂ) := by
    rw [← autEmb_apply, ← autEmb_apply, h]
  exact_mod_cast g.injective h1

theorem aut_perm_emb : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (g : ℂ ≃+* ℂ),
    ∃ π : Equiv.Perm (Emb F), ∀ (i : Emb F) (y : F), g ((i y : ℝ) : ℂ) = ((π i y : ℝ) : ℂ) := by
  intro F _ _ _ g
  refine ⟨Equiv.ofBijective (autEmb g) (Finite.injective_iff_bijective.mp (autEmb_injective g)), ?_⟩
  intro i y
  exact (autEmb_apply g i y).symm

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetGaloisConjCoefficients
set_option autoImplicit false

open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

namespace GlobalTheory.HilbFam

theorem qConj_hfun_twist : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (g : ℂ ≃+* ℂ) (m : ℤ) (κ κ' : Emb F → ℕ) (Ch Ch' : ℍ → ℂ), IsCoprime m (N : ℤ) → g (Complex.exp ((2 * Real.pi * Complex.I) / N)) = Complex.exp ((2 * Real.pi * Complex.I) * m / N) → (∀ i j : Emb F, (∀ y : F, g ((i y : ℝ) : ℂ) = ((j y : ℝ) : ℂ)) → κ' j = κ i) → QConj g N Ch Ch' → QConj g N (hfun (2 * s) L κ Ch) (hfun (2 * s) (twist N L (Matrix.diagonal ![1, (m : ZMod N)])) κ' Ch') := by
  intro hE F _ _ _ hf s N L hs hN hL z hz g m κ κ' Ch Ch' hm hg hκ hC
  obtain ⟨𝔞, 𝔟, x, rfl⟩ := exists_eq_split_of_hasLevel F N L hN hL
  have htw := GlobalTheory.T.hilbertSplitLattice_twist_diagonal_coprime F N 𝔞 𝔟 x m hm hL
  have hL' := hasLevel_twist_of_hasLevel F N _ (Matrix.diagonal ![1, (m : ZMod N)]) hL
  rw [htw] at hL' ⊢
  obtain ⟨Z, a, hZ, ha⟩ := GlobalTheory.T.exists_hilbertEisenstein_fourierCoeffFamily hE F hf 𝔞 𝔟 s hs
  have h0 := constTerm_eq_zetaVal F (2 * s) z _ Z (by omega) hz hZ
  obtain ⟨π, hπ⟩ := aut_perm_emb F g
  have hκ' : κ' = fun j ↦ κ (π.symm j) := by
    funext j
    refine hκ (π.symm j) j fun y ↦ ?_
    rw [hπ, Equiv.apply_symm_apply]
  obtain ⟨c, hc, hc'⟩ := hC
  have hev : Even (2 * s) := even_two_mul s
  refine ⟨_, GlobalTheory.T.hasQExpansionOfLevel_hilbertEisensteinQuasiPeriodJet F (2 * s) 𝔞 𝔟 _ a x N κ Ch c hN hev ha hL hc, ?_⟩
  have h2 := GlobalTheory.T.hasQExpansionOfLevel_hilbertEisensteinQuasiPeriodJet F (2 * s) 𝔞 𝔟 _ a (m * x) N κ' Ch' _ hN hev ha hL' hc'
  have h3 := fun n ↦ GlobalTheory.T.hilbertEisensteinSeries_ringEquiv_conj F (2 * s) 𝔞 𝔟 _ a x s N g m π κ c n rfl hN ha
    (by rw [h0, map_ratCast]) hL hg hπ
  simp only [h3]
  rw [hκ'] at h2 ⊢
  exact h2

end GlobalTheory.HilbFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinJetGaloisConjCoefficientsStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert_eisenstein_jet_galois_conj_coefficients : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) (L : Lat F), 1 ≤ s → 0 < N → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (g : ℂ ≃+* ℂ) (m : ℤ) (κ κ' : Emb F → ℕ) (Ch Ch' : ℍ → ℂ), IsCoprime m (N : ℤ) → g (Complex.exp ((2 * Real.pi * Complex.I) / N)) = Complex.exp ((2 * Real.pi * Complex.I) * m / N) → (∀ i j : Emb F, (∀ y : F, g ((i y : ℝ) : ℂ) = ((j y : ℝ) : ℂ)) → κ' j = κ i) → QConj g N Ch Ch' → QConj g N (hfun (2 * s) L κ Ch) (hfun (2 * s) (twist N L (Matrix.diagonal ![1, (m : ZMod N)])) κ' Ch') := by
  first | exact @GlobalTheory.HilbFam.qConj_hfun_twist | exact GlobalTheory.HilbFam.qConj_hfun_twist | (intros; apply GlobalTheory.HilbFam.qConj_hfun_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistByMatrixModNMul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistByMatrixModNMul
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors

namespace GlobalTheory.HilbFam.TwistMul

variable {F : Type} [Field F] [NumberField F]

theorem std_vecMul_int (A : Matrix (Fin 2) (Fin 2) ℤ) {y : Fin 2 → F} (hy : y ∈ stdLat F) :
    Matrix.vecMul y (A.map (Int.cast : ℤ → F)) ∈ stdLat F := by
  intro j _
  have h : ∀ i, y i * ((A i j : ℤ) : F) ∈ (1 : Submodule (𝓞 F) F) := fun i ↦ by
    have := Submodule.smul_of_tower_mem (1 : Submodule (𝓞 F) F) (A i j) (hy i (Set.mem_univ i))
    rwa [zsmul_eq_mul, mul_comm] at this
  have e : Matrix.vecMul y (A.map (Int.cast : ℤ → F)) j = y 0 * ((A 0 j : ℤ) : F) + y 1 * ((A 1 j : ℤ) : F) := by
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  change Matrix.vecMul y (A.map (Int.cast : ℤ → F)) j ∈ (1 : Submodule (𝓞 F) F)
  rw [e]
  exact Submodule.add_mem _ (h 0) (h 1)

theorem std_natCast_smul (N : ℕ) {y : Fin 2 → F} (hy : y ∈ stdLat F) : (N : F) • y ∈ stdLat F := by
  rw [Nat.cast_smul_eq_nsmul]
  exact Submodule.smul_of_tower_mem _ N hy

theorem twist_twist : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F)
    (α β : Matrix (Fin 2) (Fin 2) (ZMod N)), L ≤ stdLat F → twist N (twist N L α) β = twist N L (α * β) := by
  intro F _ _ _ N L α β hL
  have lift : ∀ γ : Matrix (Fin 2) (Fin 2) (ZMod N), ∃ C : Matrix (Fin 2) (Fin 2) ℤ, C.map (Int.cast : ℤ → ZMod N) = γ :=
    fun γ ↦ ⟨γ.map (ZMod.cast : ZMod N → ℤ), by ext i j; simp⟩
  obtain ⟨A, rfl⟩ := lift α
  obtain ⟨B, rfl⟩ := lift β
  have hm : A.map (Int.cast : ℤ → ZMod N) * B.map (Int.cast : ℤ → ZMod N) = (A * B).map (Int.cast : ℤ → ZMod N) :=
    (Matrix.map_mul (f := Int.castRingHom (ZMod N))).symm
  have hF : (A * B).map (Int.cast : ℤ → F) = A.map (Int.cast : ℤ → F) * B.map (Int.cast : ℤ → F) :=
    Matrix.map_mul (f := Int.castRingHom F)
  have hT : twist N L (A.map (Int.cast : ℤ → ZMod N)) ≤ stdLat F := by
    intro v hv
    obtain ⟨y, hy, w, hw, rfl⟩ := (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A v hL).1 hv
    exact Submodule.add_mem _ (std_vecMul_int A (hL hy)) (std_natCast_smul N hw)
  rw [hm]
  ext v
  rw [GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N _ B v hT, GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L (A * B) v hL, hF]
  constructor
  · rintro ⟨u, hu, w, hw, rfl⟩
    obtain ⟨y, hy, w', hw', rfl⟩ := (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A u hL).1 hu
    refine ⟨y, hy, Matrix.vecMul w' (B.map (Int.cast : ℤ → F)) + w,
      Submodule.add_mem _ (std_vecMul_int B hw') hw, ?_⟩
    rw [Matrix.add_vecMul, Matrix.vecMul_vecMul, Matrix.smul_vecMul, smul_add, add_assoc]
  · rintro ⟨y, hy, w, hw, rfl⟩
    refine ⟨Matrix.vecMul y (A.map (Int.cast : ℤ → F)),
      (GlobalTheory.T.mem_hilbertLatticeTwist_iff_lift F N L A _ hL).2 ⟨y, hy, 0, Submodule.zero_mem _, by simp⟩, w, hw, ?_⟩
    rw [Matrix.vecMul_vecMul]

end GlobalTheory.HilbFam.TwistMul
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertLatticeTwistByMatrixModNMulStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertLatticeTwistByMatrixModN_mul : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (L : Lat F) (α β : Matrix (Fin 2) (Fin 2) (ZMod N)), L ≤ stdLat F → twist N (twist N L α) β = twist N L (α * β) := by
  first | exact @GlobalTheory.HilbFam.TwistMul.twist_twist | exact GlobalTheory.HilbFam.TwistMul.twist_twist | (intros; apply GlobalTheory.HilbFam.TwistMul.twist_twist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisConjQExpansionFamilyDiagOneUnit
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam

namespace GlobalTheory.HilbFam.GalFamily

theorem ch_one (N : ℕ) [NeZero N] : ch N 1 = Complex.exp ((2 * Real.pi * Complex.I) / N) := by
  unfold ch
  rcases Nat.lt_or_ge 1 N with h | h
  · haveI : Fact (1 < N) := ⟨h⟩
    rw [ZMod.val_one]; simp
  · have hN : N = 1 := by have := NeZero.pos N; omega
    subst hN
    have : (1 : ZMod 1).val = 0 := rfl
    rw [this]; simp [Complex.exp_two_pi_mul_I]

theorem diag_eq {N : ℕ} [NeZero N] (a : (ZMod N)ˣ) :
    Matrix.diagonal ![1, ((((a : ZMod N).val : ℕ) : ℤ) : ZMod N)] = ((dg a : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [dg]

theorem qConj_family : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ) (κ κ' : Emb F → ℕ) (y : Fin 2 → ZMod N), ZetaAct g N a → (∀ i j : Emb F, (∀ x : F, g ((i x : ℝ) : ℂ) = ((j x : ℝ) : ℂ)) → κ' j = κ i) → y ≠ 0 → ∀ α : GL (Fin 2) (ZMod N), QConj g N (hfun (2 * s) (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ (wB N (vmul y (α)))) (hfun (2 * s) (twist N L ((α * dg a : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ' (wB N (vmul y (α * dg a)))) := by
  intro hE F _ _ _ hf s N _ L hs hL z hz g a κ κ' y hg hκ hy α
  have hact := GlobalTheory.WpFam.Act.rightActions N
  have hy' : vmul y α ≠ 0 := fun h ↦ hy ((hact.2.2.2.2.1 y α).1 h)
  have hq := (GlobalTheory.T.qConj_torsion_points N g a hg (vmul y α)).2.2 hy'
  rw [hact.2.2.1] at hq
  have hcop : IsCoprime (((a : ZMod N).val : ℕ) : ℤ) (N : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (ZMod.val_coe_unit_coprime a)
  have hz1 : g (Complex.exp ((2 * Real.pi * Complex.I) / N)) =
      Complex.exp ((2 * Real.pi * Complex.I) * ((((a : ZMod N).val : ℕ) : ℤ) : ℂ) / N) := by
    rw [← ch_one, hg 1, mul_one, ch, Int.cast_natCast]
  have h := GlobalTheory.T.hilbert_eisenstein_jet_galois_conj_coefficients hE F hf s N (twist N L (α : Matrix (Fin 2) (Fin 2) (ZMod N))) hs (NeZero.pos N)
    (GlobalTheory.HilbFam.hasLevel_twist_of_hasLevel F N L _ hL) z hz g _ κ κ' _ _ hcop hz1 hκ hq
  rw [diag_eq, GlobalTheory.T.hilbertLatticeTwistByMatrixModN_mul F N L _ _ hL.2, ← Units.val_mul] at h
  exact h

end GlobalTheory.HilbFam.GalFamily
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisConjQExpansionFamilyDiagOneUnitStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)
open GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_conj_qExpansion_family_diag_one_unit : EisExp → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F → ∀ (s N : ℕ) [NeZero N] (L : Lat F), 1 ≤ s → HasLevel N L → ∀ (z : ClassGroup (𝓞 F) → ℚ), ZetaVals (2 * s) z → ∀ (g : ℂ ≃+* ℂ) (a : (ZMod N)ˣ) (κ κ' : Emb F → ℕ) (y : Fin 2 → ZMod N), ZetaAct g N a → (∀ i j : Emb F, (∀ x : F, g ((i x : ℝ) : ℂ) = ((j x : ℝ) : ℂ)) → κ' j = κ i) → y ≠ 0 → ∀ α : GL (Fin 2) (ZMod N), QConj g N (hfun (2 * s) (twist N L ((α : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ (wB N (vmul y (α)))) (hfun (2 * s) (twist N L ((α * dg a : GL (Fin 2) (ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) κ' (wB N (vmul y (α * dg a)))) := by
  first | exact @GlobalTheory.HilbFam.GalFamily.qConj_family | exact GlobalTheory.HilbFam.GalFamily.qConj_family | (intros; apply GlobalTheory.HilbFam.GalFamily.qConj_family <;> assumption)
end
