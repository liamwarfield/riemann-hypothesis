module

public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.OffSmall
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIotaOQOfData
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
public import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
public import Formalism.SharpRestriction.GlobalSchurBounds.GL3Columns
public import Formalism.GaussJetBounds.StatementN
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DerivationCoordinateChange
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IotaOQContinuousInjective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaSupportInDivLattice
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker

namespace GlobalTheory

namespace ThetaCosetSum

open Formalism.L2.Th1.H

theorem xiL_eq_kernel {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (vol : ℝ) (SX SA SB : Finset V)
    (Φ e : V → ℂ) (z : V) :
    xiL H α vol SX SA SB Φ e z = (((Real.sqrt vol : ℝ) : ℂ)⁻¹ * ((vol : ℝ) : ℂ)) *
      ∑ x ∈ SX, ∑ y ∈ SB, ∑ t ∈ SA, Φ (t - x) *
        (α x * ((SA.card : ℂ)⁻¹ * (brk H y t)⁻¹ * α y * opU H y e (z + x)) *
          Complex.exp (-(Real.pi : ℂ) * H z x - (Real.pi : ℂ) * H x x / 2)) := by
  unfold xiL
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [opU]
  simp only [xiS, sumU, hatS, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun t _ => ?_
  ring

theorem sum_xiL {V ι : Type} [AddCommGroup V] [Module ℂ V] [Fintype ι] (H : Sesq V) (α : V → ℂ) (vol : ℝ) (hv : 0 < vol)
    (SX SA SB : Finset V) (c : ι → ℂ) (Φ : ι → V → ℂ) (Ψ e : V → ℂ) (hΨ : ∀ t, Ψ t = ∑ i, c i * Φ i t) (z : V) :
    ∑ i, c i * (((Real.sqrt vol : ℝ) : ℂ)⁻¹ * xiL H α vol SX SA SB (Φ i) e z) = xiL H α 1 SX SA SB Ψ e z := by
  have hs : ((Real.sqrt vol : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hv).ne'
  have h2 : ((vol : ℝ) : ℂ) = ((Real.sqrt vol : ℝ) : ℂ) * ((Real.sqrt vol : ℝ) : ℂ) := by
    exact_mod_cast (Real.mul_self_sqrt hv.le).symm
  have h3 : ∀ w : ℂ, ((Real.sqrt vol : ℝ) : ℂ)⁻¹ * ((((Real.sqrt vol : ℝ) : ℂ)⁻¹ * ((vol : ℝ) : ℂ)) * w) = w := by
    intro w
    generalize ((Real.sqrt vol : ℝ) : ℂ) = s at hs h2
    rw [h2]; field_simp
  simp only [xiL_eq_kernel, h3, Real.sqrt_one, Complex.ofReal_one, inv_one, one_mul, hΨ, Finset.sum_mul]
  simp only [Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]


open Classical in
theorem eq_sum_coset {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (A B : Submodule R M) (hBA : B ≤ A)
    [Fintype (↥A ⧸ B.comap A.subtype)] (Ξ : M → ℂ) (h1 : ∀ x, Ξ x ≠ 0 → x ∈ A) (h2 : ∀ x, ∀ y ∈ B, Ξ (x + y) = Ξ x)
    (r : (↥A ⧸ B.comap A.subtype) → ↥A) (hr : ∀ q, Submodule.Quotient.mk (r q) = q) (t : M) :
    Ξ t = ∑ q, Ξ (r q) * (if t - (r q : M) ∈ B then 1 else 0) := by
  by_cases ht : t ∈ A
  · have key : ∀ q, t - (r q : M) ∈ B ↔ q = Submodule.Quotient.mk (⟨t, ht⟩ : ↥A) := by
      intro q
      rw [eq_comm]
      conv_rhs => rw [← hr q]
      rw [Submodule.Quotient.eq]
      rfl
    rw [Finset.sum_eq_single (Submodule.Quotient.mk (⟨t, ht⟩ : ↥A))]
    · have hm := (key _).mpr rfl
      rw [if_pos hm, mul_one, ← h2 (r (Submodule.Quotient.mk (⟨t, ht⟩ : ↥A)) : M) _ hm, add_sub_cancel]
    · intro q _ hq
      rw [if_neg (fun h => hq ((key q).mp h)), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · have h0 : Ξ t = 0 := by
      by_contra h
      exact ht (h1 t h)
    rw [h0]
    symm
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg, mul_zero]
    intro h
    apply ht
    have := A.add_mem (hBA h) (r q).2
    simpa using this

end ThetaCosetSum


open ThetaCosetSum in
theorem latSum_thInd_eq_thC : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (cA cB : ℕ) (Ξ : HomE X.E a b → ℂ), A.IndTieD a b S (cA * cB) → IsSdLat N → IsSdLat N' → 0 < cA → 0 < cB → 0 < volC A.AA S N N' → Finite (↥(divLat cA (homAt S N N')) ⧸ (mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype) → (∀ x, Ξ x ≠ 0 → x ∈ divLat cA (homAt S N N')) → (∀ x, ∀ y ∈ mulLat cB (homAt S N N'), Ξ (x + y) = Ξ x) → ∀ z, latSum (divLat cA (homAt S N N')) (mulLat cB (homAt S N N')) (fun x => Ξ x * A.thInd S N N' cB x z) = thC (X.embC A.σ₀) A.δ A.d A.sc A.AA S N N' (cA * cB) Ξ (A.e a b N N') z := by
  intro X A a b S N N' cA cB Ξ hT hN hN' hA hB hv hfin h1 h2 z
  classical
  let _ := Fintype.ofFinite (↥(divLat cA (homAt S N N')) ⧸ (mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype)
  have hle : mulLat cB (homAt S N N') ≤ divLat cA (homAt S N N') := by
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hy)
  have hdiv : ∀ x ∈ divLat cA (homAt S N N'), x ∈ divLat (cA * cB) (homAt S N N') := by
    intro x hx
    have h : (cB : 𝓞 X.E) • (cA : 𝓞 X.E) • x ∈ homAt S N N' := Submodule.smul_mem _ _ hx
    rw [smul_smul, mul_comm, ← Nat.cast_mul] at h
    exact h
  unfold latSum
  rw [finsum_eq_sum_of_fintype]
  set r := Function.surjInv (Submodule.Quotient.mk_surjective
    ((mulLat cB (homAt S N N')).comap (divLat cA (homAt S N N')).subtype)) with hr
  have hrq : ∀ q, Submodule.Quotient.mk (r q) = q := fun q => Function.surjInv_eq _ q
  have hx : ∀ q, A.thInd S N N' cB (r q : HomE X.E a b) z = _ := fun q =>
    hT N N' cB (r q) ⟨hN, hN', hB, Dvd.intro_left _ rfl, hdiv _ (r q).2⟩ (Nat.mul_pos hA hB) z
  simp only [hx]
  unfold xiC thC xiV
  refine sum_xiL _ _ _ hv _ _ _ (fun q => Ξ (r q)) (fun q => onV (X.embC A.σ₀) A.δ (cosInd S N N' cB (r q))) _ _ ?_ z
  intro v
  unfold onV
  split_ifs with h
  · have := eq_sum_coset _ _ hle Ξ h1 h2 r hrq h.choose
    rw [this]
    refine Finset.sum_congr rfl fun q _ => ?_
    unfold cosInd
    congr
  · simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfWeightOfIntegerExpo
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfWeightOfIntegerExpo
noncomputable section

open NumberField Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.CuspRep GlobalTheory.CuspRep.InfType

namespace GlobalTheory.CuspRep.AlgExpo

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]

theorem dchi_atEmb (χ : HChar E) (τ : E →+* ℂ) (z : ℂ) :
    dchi χ (atEmb τ z) = expo χ τ * z + expo χ (ComplexEmbedding.conjugate τ) * starRingEnd ℂ z := by
  have e : atEmb τ (-Complex.I) = -atEmb τ Complex.I := by
    rw [atEmb_eq]; simp
  rw [atEmb_eq, map_add (f := _), map_smul, map_smul]
  simp only [expo, atEmb_conj, map_one, Complex.conj_I, e, map_neg, Complex.real_smul]
  conv_rhs => rw [← Complex.re_add_im z]
  simp only [map_add (f := _), map_mul, Complex.conj_ofReal, Complex.conj_I]
  linear_combination (z.im * dchi χ (atEmb τ Complex.I)) * Complex.I_mul_I

theorem dchi_eq_sum (χ : HChar E) (x : Cinf E) : dchi χ x = ∑ φ : E →+* ℂ, expo χ φ * coord φ x := by
  classical
  have hx : x = ∑ w : InfinitePlace E, atEmb w.embedding (x w) := by
    conv_lhs => rw [← Finset.univ_sum_single x]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold atEmb
    rw [InfinitePlace.mk_embedding, if_pos rfl]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hx, map_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [dchi_atEmb]
  simp only [coord_atEmb', mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

theorem chiInf_eq_prod (χ : HChar E) (n : (E →+* ℂ) → ℤ) (hn : ∀ τ, expo χ τ = n τ) (u : (Cinf E)ˣ) :
    ((chiInf χ u : ℂˣ) : ℂ) = ∏ φ : E →+* ℂ, coord φ (u : Cinf E) ^ n φ := by
  rw [← expU_log u, chiInf_expU, dchi_eq_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun φ _ => ?_
  rw [coord_expU, hn, ← Complex.exp_int_mul]

theorem isAlgPos_of_expo : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ : HChar E)
    (n : (E →+* ℂ) → ℤ), (∀ τ, expo χ τ = n τ) → IsAlgPos χ n := by
  intro E _ _ _ χ n hn k _
  have e := chiInf_eq_prod χ n hn (Units.map (diagInf E).toMonoidHom k)
  rw [HChar.inf, MonoidHom.comp_apply, InfType.infDiag_eq]
  refine e.trans (Finset.prod_congr rfl fun φ _ => ?_)
  exact congrArg (· ^ n φ) (coord_algebraMap φ (k : E))

end GlobalTheory.CuspRep.AlgExpo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsAlgebraicHeckeCharOfWeightOfIntegerExpoStatement
open NumberField Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAlgebraicHeckeCharOfWeight_of_integer_expo : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ : HChar E) (n : (E →+* ℂ) → ℤ), (∀ τ, expo χ τ = n τ) → IsAlgPos χ n := by
  first | exact @GlobalTheory.CuspRep.AlgExpo.isAlgPos_of_expo | exact GlobalTheory.CuspRep.AlgExpo.isAlgPos_of_expo | (intros; apply GlobalTheory.CuspRep.AlgExpo.isAlgPos_of_expo <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormPadicEmbeddingLeOneOfMemInverseHalfDifferent
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.InertCompare Classical
open scoped Pointwise

namespace GlobalTheory.EigenGenerator

theorem norm_le_one_of_int {C : Type} [NormedField C] [IsUltrametricDist C] {x : C} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_map_le_one {E : Type} [Field E] {l : ℕ} [Fact l.Prime] (ρ : E →+* ℂ_[l]) (a : 𝓞 E) :
    ‖ρ (a : E)‖ ≤ 1 := norm_le_one_of_int (map_isIntegral_int ρ a.isIntegral_coe)

def primeOf {E : Type} [Field E] {l : ℕ} [Fact l.Prime] (ρ : E →+* ℂ_[l]) : Ideal (𝓞 E) where
  carrier := {a | ‖ρ (a : E)‖ < 1}
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [RingOfIntegers.coe_eq_algebraMap, map_add (f := _), map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' := by
    intro c a ha
    simp only [Set.mem_setOf_eq, smul_eq_mul] at ha ⊢
    rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right (norm_map_le_one ρ c) (norm_nonneg _) ha

theorem mem_primeOf {E : Type} [Field E] {l : ℕ} [Fact l.Prime] (ρ : E →+* ℂ_[l]) (a : 𝓞 E) :
    a ∈ primeOf ρ ↔ ‖ρ (a : E)‖ < 1 := Iff.rfl

instance primeOf_isPrime {E : Type} [Field E] {l : ℕ} [Fact l.Prime] (ρ : E →+* ℂ_[l]) :
    (primeOf ρ).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one, mem_primeOf]; simp
  · intro a b hab
    rw [mem_primeOf, RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, norm_mul] at hab
    by_contra hcon
    push Not at hcon
    rw [mem_primeOf, mem_primeOf, not_lt, not_lt] at hcon
    exact absurd hab (not_lt.2 (one_le_mul_of_one_le_of_one_le hcon.1 hcon.2))

theorem norm_natCast_eq {l : ℕ} [Fact l.Prime] (n : ℕ) : ‖(n : ℂ_[l])‖ = ‖(n : ℚ_[l])‖ := by
  rw [← map_natCast (algebraMap ℚ_[l] ℂ_[l]), norm_algebraMap']

theorem natCast_mem_primeOf' {E : Type} [Field E] {l : ℕ} [hl : Fact l.Prime] (ρ : E →+* ℂ_[l]) : (l : 𝓞 E) ∈ primeOf ρ := by
  rw [mem_primeOf, RingOfIntegers.coe_eq_algebraMap, map_natCast, map_natCast, norm_natCast_eq]
  exact Padic.norm_p_lt_one

variable (D : D7) {l : ℕ} [hl : Fact l.Prime]

theorem norm_padicEmbedding_le_one_of_mem_inverseHalfDifferent (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q) (ρ : D.host.E →+* ℂ_[l]) {a : D.host.E}
    (ha : a ∈ D.host.AA0) : ‖ρ a‖ ≤ 1 := by
  have hnot : ¬ D.host.𝔟 ≤ primeOf ρ :=
    UpperTheory.Ram.half_not_le D.host _ (UpperTheory.Ram.QSq_notMem D.host (Ideal.IsPrime.ne_top inferInstance) hl.out h2 hq
      (natCast_mem_primeOf' ρ))
  obtain ⟨z, hz, hzP⟩ := Set.not_subset.1 hnot
  have hB : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (Formalism.L2.Pj.b_ne_bot D)
  unfold Host.AA0 at ha
  rw [FractionalIdeal.mem_inv_iff hB] at ha
  obtain ⟨w, hw⟩ := (FractionalIdeal.mem_one_iff _).1 (ha _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨z, hz, rfl⟩))
  have h1 : 1 ≤ ‖ρ (z : D.host.E)‖ := not_lt.1 hzP
  have h3 : ‖ρ a‖ * ‖ρ (z : D.host.E)‖ ≤ 1 := by
    rw [← norm_mul, ← map_mul]
    have := norm_map_le_one ρ w
    rwa [RingOfIntegers.coe_eq_algebraMap, hw] at this
  exact (le_mul_of_one_le_right (norm_nonneg _) h1).trans h3

theorem exists_sep (lam : Qbar →+* ℂ_[l]) (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q) {τ τ' : D.what₂.Tau} (hne : τ' ≠ τ) :
    ∃ x : 𝓞 D.host.E, 1 ≤ ‖rhoH D lam τ x - rhoH D lam τ' x‖ := by
  by_contra hcon
  push Not at hcon
  set σ : D.host.E ≃ₐ[D.host.K] D.host.E :=
    (GlobalTheory.InducedType.galK D.host (D.eTau τ))⁻¹ * GlobalTheory.InducedType.galK D.host (D.eTau τ') with hσ
  have hρ : ∀ x, rhoH D lam τ (σ x) = rhoH D lam τ' x := by
    intro x
    rw [rhoH_apply, rhoH_apply]
    congr 1
    change D.host.φ₀ (GlobalTheory.InducedType.galK D.host (D.eTau τ) (σ x)) =
      D.host.φ₀ (GlobalTheory.InducedType.galK D.host (D.eTau τ') x)
    rw [← AlgEquiv.mul_apply, hσ, mul_inv_cancel_left]
  have h1 : σ = 1 := by
    refine UpperTheory.Ram.inertiaK_trivial D.host hl.out h2 hq (primeOf (rhoH D lam τ))
      (natCast_mem_primeOf' _) σ fun x => ?_
    rw [mem_primeOf]
    have : ((σ • x - x : 𝓞 D.host.E) : D.host.E) = σ x - x := rfl
    rw [this, map_sub, hρ, norm_sub_rev]
    exact hcon x
  rw [hσ, inv_mul_eq_one] at h1
  exact hne (D.eTau.injective ((GlobalTheory.InducedType.galK_bijective D.host).1 h1)).symm

variable (M : IntermediateField ℚ ℂ) [NumberField M]

theorem mem_Qbar (s : M) : (s : ℂ) ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) s).algHom M.val

def lamM (lam : Qbar →+* ℂ_[l]) : M →+* ℂ_[l] :=
  lam.comp ((M.val : M →+* ℂ).codRestrict Qbar (mem_Qbar M))

theorem lamM_apply (lam : Qbar →+* ℂ_[l]) (s : M) : lamM M lam s = lamC lam (s : ℂ) := by
  unfold lamC
  rw [dite_eq_left (mem_Qbar M s)]
  rfl

variable (hM : ∀ τ x, embT D τ x ∈ M)

def embM (τ : D.what₂.Tau) : D.host.E →+* M := (embT D τ).codRestrict M (hM τ)

theorem liftM_eq (τ : D.what₂.Tau) (x : D.host.E) : TaylorLogMetric.liftM M (embT D τ x) = embM D M hM τ x := by
  unfold TaylorLogMetric.liftM
  rw [dite_eq_left (hM τ x)]
  rfl

theorem lamM_embM (lam : Qbar →+* ℂ_[l]) (τ : D.what₂.Tau) (x : D.host.E) :
    lamM M lam (embM D M hM τ x) = rhoH D lam τ x := by
  rw [lamM_apply, rhoH_apply]
  rfl

theorem mul_mem_mmM (x : 𝓞 D.host.E) {v : D.what₂.Tau → M} (hv : v ∈ mmM D M) :
    (fun τ => embM D M hM τ x * v τ) ∈ mmM D M := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, ha, rfl⟩ := hv
    refine Submodule.subset_span ⟨x • a, Submodule.smul_mem _ x ha, ?_⟩
    funext τ
    beta_reduce
    rw [liftM_eq D M hM, liftM_eq D M hM, Algebra.smul_def, map_mul]
  | zero =>
    convert (mmM D M).zero_mem using 1
    ext τ
    simp
  | add v w _ _ hv hw =>
    convert (mmM D M).add_mem hv hw using 1
    funext τ
    simp [mul_add]
  | smul c v _ hv =>
    convert (mmM D M).smul_mem c hv using 1
    funext τ
    simp [Algebra.smul_def, mul_left_comm]

include hM in
theorem norm_coord_le (lam : Qbar →+* ℂ_[l]) (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q) (τ : D.what₂.Tau)
    {v : D.what₂.Tau → M} (hv : v ∈ mmM D M) : ‖lamM M lam (v τ)‖ ≤ 1 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨a, ha, rfl⟩ := hv
    simp only
    rw [liftM_eq D M hM, lamM_embM]
    exact norm_padicEmbedding_le_one_of_mem_inverseHalfDifferent D h2 hq _ ha
  | zero => simp
  | add v w _ _ hv hw =>
    rw [Pi.add_apply, map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hv hw)
  | smul c v _ hv =>
    rw [Pi.smul_apply, Algebra.smul_def, map_mul, norm_mul]
    exact mul_le_one₀ (norm_map_le_one _ c) (norm_nonneg _) hv

include hM in
theorem exists_vanishing (lam : Qbar →+* ℂ_[l]) (h2 : l ∉ D.host.small) (hq : l ≠ D.host.q) (τ : D.what₂.Tau)
    (S : Finset D.what₂.Tau) (hS : τ ∉ S) :
    ∃ v ∈ mmM D M, (∀ τ' ∈ S, v τ' = 0) ∧ 1 ≤ ‖lamM M lam (v τ)‖ := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨_, Submodule.subset_span ⟨1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, rfl⟩, by simp, ?_⟩
    beta_reduce
    rw [liftM_eq D M hM]
    simp
  | insert τ' S _ ih =>
    rw [Finset.mem_insert, not_or] at hS
    obtain ⟨v, hv, hv0, hv1⟩ := ih hS.2
    obtain ⟨x, hx⟩ := exists_sep D lam h2 hq (Ne.symm hS.1)
    let c : 𝓞 M := ⟨embM D M hM τ' x, map_isIntegral_int _ x.isIntegral_coe⟩
    have hc : algebraMap (𝓞 M) M c = embM D M hM τ' x := rfl
    refine ⟨_, (mmM D M).sub_mem (mul_mem_mmM D M hM x hv) ((mmM D M).smul_mem c hv), ?_, ?_⟩
    · intro t ht
      rw [Pi.sub_apply, Pi.smul_apply, Algebra.smul_def, hc]
      rcases Finset.mem_insert.1 ht with rfl | ht
      · exact sub_self _
      · simp [hv0 t ht]
    · rw [Pi.sub_apply, Pi.smul_apply, Algebra.smul_def, hc, ← sub_mul, map_mul, map_sub, lamM_embM, lamM_embM,
        norm_mul]
      exact one_le_mul_of_one_le_of_one_le hx hv1

end GlobalTheory.EigenGenerator


open GlobalTheory.EigenGenerator in
theorem GlobalTheory.EigenGenerator.norm_generator_eq_one : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (lam : Qbar →+* ℂ_[l]), l ∉ D.host.small → l ≠ D.host.q → ∀ (M : IntermediateField ℚ ℂ) [NumberField M], (∀ τ x, embT D τ x ∈ M) → ∀ (τ : D.what₂.Tau) (s : M), ellT D M τ = Submodule.span (𝓞 M) {s} → ‖lamC lam (s : ℂ)‖ = 1 := by
  intro D l _ lam h2 hq M _ hM τ s hs
  rw [← lamM_apply]
  refine le_antisymm ?_ ?_
  · have h1 : s ∈ ellT D M τ := by rw [hs]; exact Submodule.mem_span_singleton_self s
    have := norm_coord_le D M hM lam h2 hq τ (Submodule.mem_comap.1 h1)
    simpa using this
  · obtain ⟨v, hv, hv0, hv1⟩ := exists_vanishing D M hM lam h2 hq τ (Finset.univ.erase τ) (Finset.notMem_erase _ _)
    have h1 : v τ ∈ ellT D M τ := by
      refine Submodule.mem_comap.2 ?_
      convert hv using 1
      funext t
      by_cases ht : t = τ
      · subst ht; simp
      · rw [hv0 t (Finset.mem_erase.2 ⟨ht, Finset.mem_univ _⟩)]
        simp [ht]
    rw [hs, Submodule.mem_span_singleton] at h1
    obtain ⟨c, hc⟩ := h1
    rw [← hc, Algebra.smul_def, map_mul, norm_mul] at hv1
    exact hv1.trans (mul_le_of_le_one_left (norm_nonneg _) (norm_map_le_one _ c))
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NatCastMemPrimeOf
open NumberField Filter Topology

noncomputable section

namespace GlobalTheory.Proof.IdempotentLatticeSequence

theorem norm_int_le {p : ℕ} [Fact p.Prime] {M : Type} [Field M] (φ : M →+* ℂ_[p]) (a : 𝓞 M) : ‖φ (a : M)‖ ≤ 1 := by
  obtain ⟨P, hmon, hev⟩ := RingOfIntegers.isIntegral_coe a
  have key : ∀ f : ℤ →+* ℂ_[p], Polynomial.eval₂ f (φ (a : M)) P = 0 := fun f => by
    rw [RingHom.ext_int f (φ.comp (algebraMap ℤ M)), ← Polynomial.hom_eval₂, hev, map_zero]
  exact GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral ⟨P, hmon, key _⟩

theorem flat_system {A B : Type} [CommRing A] [AddCommGroup B] [Module A B] [Module.Flat A B] {κ J : Type}
    [Fintype κ] [Fintype J] (b : κ → J → A) (r : κ → B) (h : ∀ j, ∑ k, b k j • r k = 0) :
    ∃ (n : ℕ) (a : κ → Fin n → A) (y : Fin n → B), (∀ k, r k = ∑ l, a k l • y l) ∧ ∀ l j, ∑ k, b k j * a k l = 0 := by
  classical
  let f : (J → A) →ₗ[A] (κ → A) := Matrix.mulVecLin (Matrix.of fun k j => b k j)
  let x : (κ → A) →ₗ[A] B := Fintype.linearCombination A r
  have hxf : x ∘ₗ f = 0 := by
    refine LinearMap.ext fun c => ?_
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, x, f, Fintype.linearCombination_apply,
      Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    simp_rw [mul_comm (b _ j) (c j), mul_smul]
    rw [← Finset.smul_sum, h j, smul_zero]
  obtain ⟨n, a', y', hxa, haf⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxf
  refine ⟨n, fun k l => a' (Pi.single k 1) l, fun l => y' (Finsupp.single l 1), fun k => ?_, fun l j => ?_⟩
  · have hr : r k = x (Pi.single k 1) := by
      simp [x, Fintype.linearCombination_apply, Pi.single_apply]
    rw [hr, hxa, LinearMap.comp_apply]
    conv_lhs => rw [← Finsupp.univ_sum_single (a' (Pi.single k 1))]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finsupp.smul_single_one, map_smul]
  · have h1 := congrArg (fun v => v l) (LinearMap.congr_fun haf (Pi.single j 1))
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, Finsupp.coe_zero, Pi.zero_apply] at h1
    have hf : f (Pi.single j 1) = ∑ k, b k j • Pi.single k 1 := by
      ext k'
      simp [f, Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hf, map_sum] at h1
    simpa [Finsupp.finsetSum_apply, map_smul] using h1

def primeOf {p : ℕ} [Fact p.Prime] {E : Type} [Field E] (φ : E →+* ℂ_[p]) : Ideal (𝓞 E) where
  carrier := {a | ‖φ (a : E)‖ < 1}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    change ‖φ (algebraMap (𝓞 E) E (a + b))‖ < 1
    rw [map_add (f := _), map_add (f := _)]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
  smul_mem' := fun c a ha => by
    change ‖φ (algebraMap (𝓞 E) E (c * a))‖ < 1
    rw [map_mul, map_mul, norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_int_le φ c)).trans_lt ha

theorem mem_primeOf {p : ℕ} [Fact p.Prime] {E : Type} [Field E] (φ : E →+* ℂ_[p]) (a : 𝓞 E) :
    a ∈ primeOf φ ↔ ‖φ (algebraMap (𝓞 E) E a)‖ < 1 := by
  exact Iff.rfl

theorem natCast_mem_primeOf {p : ℕ} [Fact p.Prime] {E : Type} [Field E] (φ : E →+* ℂ_[p]) :
    (p : 𝓞 E) ∈ primeOf φ := by
  rw [mem_primeOf]
  have h1 : ‖((p : ℚ_[p]) : ℂ_[p])‖ < 1 := by
    rw [PadicComplex.norm_extends', Padic.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  simpa using h1

theorem primeOf_isPrime {p : ℕ} [Fact p.Prime] {E : Type} [Field E] (φ : E →+* ℂ_[p]) : (primeOf φ).IsPrime := by
  refine ⟨?_, fun {a b} hab => ?_⟩
  · rw [Ne, Ideal.eq_top_iff_one, mem_primeOf]
    simp
  · rw [mem_primeOf, map_mul, map_mul, norm_mul] at hab
    rw [mem_primeOf, mem_primeOf]
    have ha : ‖φ (algebraMap (𝓞 E) E a)‖ ≤ 1 := norm_int_le φ a
    have hb : ‖φ (algebraMap (𝓞 E) E b)‖ ≤ 1 := norm_int_le φ b
    by_contra h
    rw [not_or, not_lt, not_lt] at h
    nlinarith [h.1, h.2, norm_nonneg (φ (algebraMap (𝓞 E) E a))]

theorem primeOf_isMaximal {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ_[p]) :
    (primeOf φ).IsMaximal := by
  refine (primeOf_isPrime φ).isMaximal ?_
  intro h
  have hp := natCast_mem_primeOf φ
  rw [h, Ideal.mem_bot] at hp
  exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) hp

end GlobalTheory.Proof.IdempotentLatticeSequence
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralEigenCombination
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

namespace GlobalTheory.Proof.IntegralEigenCombination

theorem eigGen_integral_comb : ∀ (D : D7) (cD : D.what₂.Tau → ℂ), Formalism.L2.Ker.IsDgen D cD → ∀ (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ τ : D.what₂.Tau, ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (a : Fin n → D.host.E), (∀ j, ‖r j‖ ≤ 1) ∧ (∀ j, a j ∈ D.host.AA0) ∧ ∀ τ', ∑ j, r j * tauEmb D lm τ' (a j) = if τ' = τ then lamC lm (cD τ) else 0 := by
  intro D cD hD p _ lm τ
  obtain ⟨M, hMnf, hM, hs⟩ := hD
  obtain ⟨s, hsc, hsp⟩ := hs τ
  have hmem : s ∈ TaylorLogMetric.ellT D M τ := by rw [hsp]; exact Submodule.mem_span_singleton_self s
  have hv : (LinearMap.single (𝓞 M) (fun _ : D.what₂.Tau => (M : Type)) τ) s ∈ TaylorLogMetric.mmM D M :=
    Submodule.mem_comap.1 hmem
  obtain ⟨n, f, v, hfv⟩ := Submodule.mem_span_set'.1 hv
  have hva : ∀ j, ∃ a ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E),
      (v j : D.what₂.Tau → M) = fun τ => TaylorLogMetric.liftM M (TaylorLogMetric.embT D τ a) := fun j => (v j).2
  choose a ha hav using hva
  obtain ⟨g, hg⟩ := GlobalTheory.Proof.DirectionalDerivative.exists_lamHom lm (algebraMap M ℂ)
  have hg' : ∀ x : M, lamC lm (x : ℂ) = g x := hg
  refine ⟨n, fun j => g ((f j : 𝓞 M) : M), a, fun j => ?_, ha, fun τ' => ?_⟩
  · exact GlobalTheory.SplitEmbSep.norm_le_one_of_isIntegral (map_isIntegral_int g (f j).isIntegral_coe)
  · have e : ∀ j, tauEmb D lm τ' (a j) = g (TaylorLogMetric.liftM M (TaylorLogMetric.embT D τ' (a j))) := by
      intro j
      rw [← hg', TaylorLogMetric.liftM, dite_eq_left (hM _ _)]
      rfl
    have hc := congrFun hfv τ'
    simp only [Finset.sum_apply, Pi.smul_apply, hav] at hc
    simp only [e, ← map_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum]
    have hc' : (∑ j, ((f j : 𝓞 M) : M) * TaylorLogMetric.liftM M (TaylorLogMetric.embT D τ' (a j))) =
        (LinearMap.single (𝓞 M) (fun _ : D.what₂.Tau => (M : Type)) τ) s τ' := by
      rw [← hc]; rfl
    rw [hc']
    by_cases h : τ' = τ
    · subst h; simp [hsc.symm, hg']
    · simp [h]
end GlobalTheory.Proof.IntegralEigenCombination
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRestrictEqTopOfAbsIrrSub
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRestrictEqTopOfAbsIrrSub
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.BurnsideSub

theorem matRep_apply {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (g : Γ)
    (v : Fin a → k) :
    matRep ((Units.coeHom _).comp ρ) g v = (ρ g : Matrix (Fin a) (Fin a) k).mulVec v := by
  simp [matRep]

theorem isIrrSub_top_of_intertwine {K Γ : Type} [Field K] [Group Γ] {a d : ℕ}
    (ρ : Γ →* GL (Fin a) K) (σ : Γ →* GL (Fin d) K) (B : Matrix (Fin a) (Fin d) K)
    (C : Matrix (Fin d) (Fin a) K) (hCB : C * B = 1)
    (hint : ∀ g, (ρ g : Matrix (Fin a) (Fin a) K) * B = B * (σ g : Matrix (Fin d) (Fin d) K))
    (h : IsIrrSub ρ (LinearMap.range B.mulVecLin)) : IsIrrSub σ ⊤ := by
  have hinj : Function.Injective B.mulVecLin := by
    intro x y hxy
    have := congrArg C.mulVec hxy
    simpa [Matrix.mulVec_mulVec, hCB] using this
  have hmap : ∀ U : Submodule K (Fin d → K), (∀ g, ∀ v ∈ U, (σ g : Matrix (Fin d) (Fin d) K).mulVec v ∈ U) →
      IsInv ρ (U.map B.mulVecLin) := by
    rintro U hU g _ ⟨v, hv, rfl⟩
    refine ⟨_, hU g v hv, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hint g]
  refine ⟨fun h0 => h.1 ?_, fun g v _ => trivial, fun U _ hU => ?_⟩
  · rw [LinearMap.range_eq_map, h0, Submodule.map_bot]
  · have hle : U.map B.mulVecLin ≤ LinearMap.range B.mulVecLin := LinearMap.map_le_range
    rcases h.2.2 _ hle (hmap U hU) with h1 | h1
    · left
      exact Submodule.map_injective_of_injective hinj (h1.trans (Submodule.map_bot _).symm)
    · right
      rw [LinearMap.range_eq_map] at h1
      exact Submodule.map_injective_of_injective hinj h1

theorem span_restrict_eq_top_of_absIrrSub : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k)
    (W : Submodule k (Fin a → k)) (hW : Stable (matRep ((Units.coeHom _).comp ρ)) W),
    AbsIrrSub ρ W →
    Submodule.span k (Set.range fun g =>
      (matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) = ⊤ := by
  intro k Γ _ _ a ρ W hW habs
  classical
  set τ := matRep ((Units.coeHom (Matrix (Fin a) (Fin a) k)).comp ρ) with hτ
  let r : Γ → Module.End k W := fun g => (τ g).restrict (hW g)
  have hr1 : r 1 = 1 := by
    ext v; simp [r]
  have hrm : ∀ g h, r (g * h) = r g * r h := by
    intro g h; ext v; simp [r]
  let d := Module.finrank k W
  let e : W ≃ₗ[k] (Fin d → k) := (Module.finBasis k W).equivFun

  let φ : Module.End k W ≃ₗ[k] Matrix (Fin d) (Fin d) k :=
    e.conj.trans LinearMap.toMatrix'
  have hφa : ∀ x, φ x = LinearMap.toMatrix' ((e : W →ₗ[k] (Fin d → k)) ∘ₗ x ∘ₗ
      (e.symm : (Fin d → k) →ₗ[k] W)) := fun _ => rfl
  have hφ1 : φ 1 = 1 := by
    rw [hφa]
    have : (e : W →ₗ[k] (Fin d → k)) ∘ₗ (1 : Module.End k W) ∘ₗ
        (e.symm : (Fin d → k) →ₗ[k] W) = LinearMap.id := LinearMap.ext fun v => by simp
    rw [this, LinearMap.toMatrix'_id]
  have hφm : ∀ x y, φ (x * y) = φ x * φ y := by
    intro x y
    rw [hφa, hφa, hφa, ← LinearMap.toMatrix'_comp]
    congr 1
    exact LinearMap.ext fun v => by simp
  let S : Γ →* Matrix (Fin d) (Fin d) k :=
    { toFun := fun g => φ (r g)
      map_one' := by rw [hr1, hφ1]
      map_mul' := fun g h => by rw [hrm, hφm] }
  let σ : Γ →* GL (Fin d) k := MonoidHom.toHomUnits S
  have hσ : ∀ g, (σ g : Matrix (Fin d) (Fin d) k) = φ (r g) := fun g => rfl

  let L : (Fin d → k) →ₗ[k] (Fin a → k) := W.subtype ∘ₗ e.symm.toLinearMap
  have hLinj : Function.Injective L := by
    intro x y hxy
    exact e.symm.injective (Subtype.val_injective hxy)
  obtain ⟨L', hL'⟩ := LinearMap.exists_leftInverse_of_injective L (LinearMap.ker_eq_bot.2 hLinj)
  let B : Matrix (Fin a) (Fin d) k := LinearMap.toMatrix' L
  let C : Matrix (Fin d) (Fin a) k := LinearMap.toMatrix' L'
  have hCB : C * B = 1 := by
    rw [← LinearMap.toMatrix'_comp, hL', LinearMap.toMatrix'_id]
  have hBv : ∀ c, B.mulVec c = L c := fun c => LinearMap.toMatrix'_mulVec L c
  have hint : ∀ g, (ρ g : Matrix (Fin a) (Fin a) k) * B = B * (σ g : Matrix (Fin d) (Fin d) k) := by
    intro g
    have hM : (ρ g : Matrix (Fin a) (Fin a) k) = LinearMap.toMatrix' (τ g) := by
      have : τ g = Matrix.toLin' (ρ g : Matrix (Fin a) (Fin a) k) :=
        LinearMap.ext fun v => by rw [hτ, matRep_apply, Matrix.toLin'_apply]
      rw [this, LinearMap.toMatrix'_toLin']
    rw [hσ, hφa, hM, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
    congr 1
    refine LinearMap.ext fun c => ?_
    change τ g ((e.symm c : W) : Fin a → k) = ((e.symm (e (r g (e.symm c))) : W) : Fin a → k)
    rw [e.symm_apply_apply]
    rfl
  set f := algebraMap k (AlgebraicClosure k) with hf
  have hspan : Submodule.span (AlgebraicClosure k) ((fun v => f ∘ v) '' W) =
      LinearMap.range (B.map f).mulVecLin := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨w, hw, rfl⟩
      refine ⟨f ∘ e ⟨w, hw⟩, ?_⟩
      funext i
      have h1 : B.mulVec (e ⟨w, hw⟩) = w := by
        rw [hBv]
        change ((e.symm (e ⟨w, hw⟩) : W) : Fin a → k) = w
        rw [e.symm_apply_apply]
      rw [Matrix.mulVecLin_apply, ← RingHom.map_mulVec, h1]
      rfl
    · rintro _ ⟨c, rfl⟩
      rw [Matrix.mulVecLin_apply, Matrix.mulVec_eq_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [op_smul_eq_smul]
      refine Submodule.smul_mem _ _ ?_
      apply Submodule.subset_span
      refine ⟨L (Pi.single j 1), (e.symm (Pi.single j 1)).2, ?_⟩
      funext i
      simp [← hBv, Matrix.mulVec_single_one]
  unfold AbsIrrSub at habs
  rw [hspan] at habs
  have hirr : IsIrrSub (mapRep f σ) ⊤ := by
    refine isIrrSub_top_of_intertwine (mapRep f ρ) (mapRep f σ) (B.map f) (C.map f) ?_ ?_ habs
    · rw [← Matrix.map_mul, hCB]
      exact Matrix.map_one _ f.map_zero f.map_one
    · intro g
      change (ρ g : Matrix (Fin a) (Fin a) k).map f * B.map f =
        B.map f * (σ g : Matrix (Fin d) (Fin d) k).map f
      rw [← Matrix.map_mul, ← Matrix.map_mul, hint g]
  have h2 := GlobalTheory.BurnsideField.span_mat_eq_top_of_isIrrSub _ hirr
  have h3 : GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat (mapRep f σ) = fun g => (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ g).map f := by
    funext g
    ext p q
    simp [GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat, mapRep]
  rw [h3] at h2
  have h4 := GlobalTheory.BurnsideField.span_eq_top_of_span_map (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ) h2
  have h5 : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices.mat σ) = φ '' Set.range r := by
    rw [← Set.range_comp]; rfl
  have h6 := Submodule.map_span φ.toLinearMap (Set.range r)
  change Submodule.span k (Set.range r) = ⊤
  refine Submodule.map_injective_of_injective φ.injective ?_
  rw [h6, Submodule.map_top, LinearEquiv.range]
  rw [h5] at h4
  exact h4

end GlobalTheory.BurnsideSub
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SpanRestrictEqTopOfAbsIrrSubStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_restrict_eq_top_of_absIrrSub_alt : ∀ {k Γ : Type} [Field k] [Group Γ] {a : ℕ} (ρ : Γ →* GL (Fin a) k) (W : Submodule k (Fin a → k)) (hW : Stable (matRep ((Units.coeHom _).comp ρ)) W), AbsIrrSub ρ W → Submodule.span k (Set.range fun g => (matRep ((Units.coeHom _).comp ρ) g).restrict (hW g)) = ⊤ := by
  first | exact @GlobalTheory.BurnsideSub.span_restrict_eq_top_of_absIrrSub | exact GlobalTheory.BurnsideSub.span_restrict_eq_top_of_absIrrSub | (intros; apply GlobalTheory.BurnsideSub.span_restrict_eq_top_of_absIrrSub <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeJetsIntegralIffIntegralFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeJetsIntegralIffIntegralFrames
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames

open MvPowerSeries GlobalTheory.Proof.DirectionalDerivative

section Formal

variable {p : ℕ} [Fact p.Prime] {σ κ : Type}

theorem jetsIntegral_iff (G : MvPowerSeries κ ℂ_[p]) :
    JetsIntegral G ↔ GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.JetsIntegral G := by
  unfold JetsIntegral GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.JetsIntegral GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.jetAt Formalism.DworkPowerSeriesWeights.mfact
  simp [Finsupp.prod, Nat.cast_prod]

theorem jetAt_linAt_list [Fintype σ] [Fintype κ] (c : σ → κ → ℂ_[p]) (l : List κ) (G : MvPowerSeries σ ℂ_[p]) :
    GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.jetAt (linAt c G) (l.map fun x => Finsupp.single x 1).sum =
      constantCoeff (l.foldl (fun H x => dirDer (fun k => c k x) H) G) := by
  induction l generalizing G with
  | nil => simp [jetAt_zero, constantCoeff_linAt]
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, add_comm, jetAt_add_single, pderiv_linAt, ih, List.foldl_cons]

end Formal

theorem jetsInt_frames : ∀ (D : D7) (N N' : ℕ) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (Yl : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)) (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (JetsInt D lm Yl F ↔ ∀ (n : ℕ) (y : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, y j ∈ Yl) → JetsIntegral (atLin (fun k j => tauEmb D lm k.1 (y j k.2.1 k.2.2)) (fun j => MvPowerSeries.X j) F)) ∧ (JetsInt D lm Yl F → ∀ (ν : Type) [Fintype ν] (M : D.what₂.Tau × Fin N' × Fin N → ν → ℂ_[p]), (∀ x, ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (y : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, ‖r j‖ ≤ 1) ∧ (∀ j, y j ∈ Yl) ∧ ∀ k, M k x = ∑ j, r j * tauEmb D lm k.1 (y j k.2.1 k.2.2)) → JetsIntegral (atLin M (fun j => MvPowerSeries.X j) F)) := by
  intro D N N' p _ lm Yl F
  refine ⟨⟨fun hF n y hy => ?_, fun h n y hy => ?_⟩, fun hF ν _ M hM => ?_⟩
  · change JetsIntegral (linAt (fun k j => vecY D lm (y j) k) F)
    rw [jetsIntegral_iff]
    exact jetsIntegral_linAt _ (JetsInt D lm Yl) (fun G hG => jetsInt_const D lm Yl hG)
      (fun x G hG => keeps_vecY D lm Yl (hy x) G hG) F hF
  · have hJ := (jetsIntegral_iff _).1 (h n y hy)
    change GlobalTheory.IndefiniteRowSideFullHecke.PolynomialIntegralityJets.JetsIntegral (linAt (fun k j => vecY D lm (y j) k) F) at hJ
    have := hJ (((List.finRange n).reverse.map fun x => Finsupp.single x 1).sum)
    rw [jetAt_linAt_list, List.foldl_reverse] at this
    show ‖constantCoeff ((List.ofFn y).foldr (fun y' G => der D lm y' G) F)‖ ≤ 1
    rw [List.ofFn_eq_map, List.foldr_map]
    have hfun : (fun x G => der D lm (y x) G) = fun x G => dirDer (fun k => vecY D lm (y x) k) G := by
      funext x G
      exact der_eq D lm (y x) G
    rw [hfun]
    exact this
  · change JetsIntegral (linAt M F)
    rw [jetsIntegral_iff]
    refine jetsIntegral_linAt _ (JetsInt D lm Yl) (fun G hG => jetsInt_const D lm Yl hG) (fun x => ?_) F hF
    obtain ⟨n, r, y, hr, hy, hMx⟩ := hM x
    have e : (fun k => M k x) = ∑ j, r j • vecY D lm (y j) := by
      funext k
      rw [hMx k, Finset.sum_apply]
      rfl
    rw [e]
    exact Finset.sum_induction _ (Keeps D lm Yl) (fun _ _ ha hb => keeps_add D lm Yl ha hb) (keeps_zero D lm Yl)
      fun j _ => keeps_smul D lm Yl (hr j) (keeps_vecY D lm Yl (hy j))

end GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LatticeJetsIntegralIffIntegralFramesStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric Classical
open Formalism.DworkPowerSeriesWeights (JetsIntegral)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeJetsIntegral_iff_integralFrames : ∀ (D : D7) (N N' : ℕ) (p : ℕ) [Fact p.Prime] (lm : TaylorLogMetric.Qbar →+* ℂ_[p]), ∀ (Yl : Submodule (𝓞 D.host.E) (Matrix (Fin N') (Fin N) D.host.E)) (F : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (JetsInt D lm Yl F ↔ ∀ (n : ℕ) (y : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, y j ∈ Yl) → JetsIntegral (atLin (fun k j => tauEmb D lm k.1 (y j k.2.1 k.2.2)) (fun j => MvPowerSeries.X j) F)) ∧ (JetsInt D lm Yl F → ∀ (ν : Type) [Fintype ν] (M : D.what₂.Tau × Fin N' × Fin N → ν → ℂ_[p]), (∀ x, ∃ (n : ℕ) (r : Fin n → ℂ_[p]) (y : Fin n → Matrix (Fin N') (Fin N) D.host.E), (∀ j, ‖r j‖ ≤ 1) ∧ (∀ j, y j ∈ Yl) ∧ ∀ k, M k x = ∑ j, r j * tauEmb D lm k.1 (y j k.2.1 k.2.2)) → JetsIntegral (atLin M (fun j => MvPowerSeries.X j) F)) := by
  first | exact @GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames.jetsInt_frames | exact GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames.jetsInt_frames | (intros; apply GlobalTheory.Proof.latticeJetsIntegral_iff_integralFrames.jetsInt_frames <;> assumption)
end
end
