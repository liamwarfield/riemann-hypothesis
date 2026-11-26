module

public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRegularLocalRingAdicCompletion
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdTsumEqTsumIndicatorEnnreal
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyMeasAndReps

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSatMOfSmul
namespace GlobalTheory.NL.Coker

open Formalism.BasicNotions

variable {O : Type} [CommRing O] {n : ℕ} {M : Type} [AddCommGroup M] [Module (LetA O n) M]

def satM (p : ℕ) (P N : Submodule (LetA O n) M) : Submodule (LetA O n) M where
  carrier := {x | x ∈ N ∧ ∃ k : ℕ, ((p : LetA O n)) ^ k • x ∈ P ∧ (letπ : LetA O n) ^ k • x ∈ P}
  add_mem' := by
    rintro x y ⟨hx, k, hk1, hk2⟩ ⟨hy, j, hj1, hj2⟩
    refine ⟨N.add_mem hx hy, k + j, ?_, ?_⟩
    · rw [smul_add, pow_add]
      refine P.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact P.smul_mem _ hk1
      · rw [mul_smul]; exact P.smul_mem _ hj1
    · rw [smul_add, pow_add]
      refine P.add_mem ?_ ?_
      · rw [mul_comm, mul_smul]; exact P.smul_mem _ hk2
      · rw [mul_smul]; exact P.smul_mem _ hj2
  zero_mem' := ⟨N.zero_mem, 0, by simp, by simp⟩
  smul_mem' := by
    rintro a x ⟨hx, k, hk1, hk2⟩
    refine ⟨N.smul_mem a hx, k, ?_, ?_⟩
    · rw [smul_comm]; exact P.smul_mem a hk1
    · rw [smul_comm]; exact P.smul_mem a hk2

theorem satM_le (p : ℕ) (P N : Submodule (LetA O n) M) : satM p P N ≤ N := fun _ hx => hx.1

theorem le_satM (p : ℕ) {P N : Submodule (LetA O n) M} (h : P ≤ N) : P ≤ satM p P N :=
  fun x hx => ⟨h hx, 0, by simpa using hx, by simpa using hx⟩

theorem mem_satM_of_smul {p : ℕ} {P N : Submodule (LetA O n) M} {x : M} (hx : x ∈ N)
    (h1 : ((p : LetA O n)) • x ∈ satM p P N) (h2 : (letπ : LetA O n) • x ∈ satM p P N) :
    x ∈ satM p P N := by
  obtain ⟨-, k, hk1, -⟩ := h1
  obtain ⟨-, j, -, hj2⟩ := h2
  refine ⟨hx, k + j + 1, ?_, ?_⟩
  · have : ((p : LetA O n)) ^ (k + j + 1) • x = ((p : LetA O n)) ^ j • (((p : LetA O n)) ^ k • ((p : LetA O n)) • x) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [this]; exact P.smul_mem _ hk1
  · have : (letπ : LetA O n) ^ (k + j + 1) • x = (letπ : LetA O n) ^ k • ((letπ : LetA O n) ^ j • (letπ : LetA O n) • x) := by
      rw [smul_smul, smul_smul]; congr 1; ring
    rw [this]; exact P.smul_mem _ hj2

theorem uniform {p : ℕ} {P N : Submodule (LetA O n) M} (hN : N.FG) (h : N ≤ satM p P N) :
    ∃ c : ℕ, ∀ z ∈ N, ((p : LetA O n)) ^ c • z ∈ P ∧ (letπ : LetA O n) ^ c • z ∈ P := by
  classical
  obtain ⟨G, rfl⟩ := hN
  have hk : ∀ x ∈ G, ∃ k : ℕ, ((p : LetA O n)) ^ k • x ∈ P ∧ (letπ : LetA O n) ^ k • x ∈ P :=
    fun x hx => (h (Submodule.subset_span hx)).2
  choose! k hk using hk
  refine ⟨G.sup k, fun z hz => ?_⟩
  induction hz using Submodule.span_induction with
  | mem x hx =>
    have hle : k x ≤ G.sup k := Finset.le_sup hx
    obtain ⟨h1, h2⟩ := hk x hx
    constructor
    · rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]; exact P.smul_mem _ h1
    · rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]; exact P.smul_mem _ h2
  | zero => simp
  | add x y _ _ hx hy =>
    exact ⟨by rw [smul_add]; exact P.add_mem hx.1 hy.1, by rw [smul_add]; exact P.add_mem hx.2 hy.2⟩
  | smul a x _ hx =>
    exact ⟨by rw [smul_comm]; exact P.smul_mem a hx.1, by rw [smul_comm]; exact P.smul_mem a hx.2⟩

end GlobalTheory.NL.Coker
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentOfInvariant
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.Per

theorem linearIndependent_of_invariant (G E M ι : Type) [Field E] [AddCommGroup M] [Module E M]
    [Fintype ι] (σ : G → (E →+* E)) (ρ : G → (M →+ M))
    (hρ : ∀ g (e : E) (m : M), ρ g (e • m) = σ g e • ρ g m) (v : ι → M)
    (hv : ∀ g i, ρ g (v i) = v i)
    (hind : ∀ c : ι → E, (∀ g i, σ g (c i) = c i) → ∑ i, c i • v i = 0 → ∀ i, c i = 0) :
    LinearIndependent E v := by
  classical
  rw [Fintype.linearIndependent_iff]

  suffices H : ∀ n : ℕ, ∀ c : ι → E,
      (Finset.univ.filter (fun i => c i ≠ 0)).card ≤ n → ∑ i, c i • v i = 0 → ∀ i, c i = 0 by
    exact fun c hc => H _ c le_rfl hc
  intro n
  induction n with
  | zero =>
    intro c hcard _ i
    by_contra h
    have hpos : 0 < (Finset.univ.filter (fun i => c i ≠ 0)).card :=
      Finset.card_pos.mpr ⟨i, by simp [h]⟩
    omega
  | succ n ih =>
    intro c hcard hsum
    by_contra hne
    obtain ⟨i0, hi0⟩ := not_forall.mp hne

    obtain ⟨c', hc'⟩ : ∃ c' : ι → E, c' = fun i => (c i0)⁻¹ * c i := ⟨_, rfl⟩
    have hc'sum : ∑ i, c' i • v i = 0 := by
      simp only [hc', mul_smul, ← Finset.smul_sum, hsum, smul_zero]
    have hc'i0 : c' i0 = 1 := by
      rw [hc']
      exact inv_mul_cancel₀ hi0
    have hsupp : Finset.univ.filter (fun i => c' i ≠ 0) = Finset.univ.filter (fun i => c i ≠ 0) := by
      ext i
      simp [hc', hi0]

    have hfix : ∀ g i, σ g (c' i) = c' i := by
      intro g
      obtain ⟨d, hd⟩ : ∃ d : ι → E, d = fun i => σ g (c' i) - c' i := ⟨_, rfl⟩
      have h1 : ∑ i, σ g (c' i) • v i = 0 := by
        have h2 := congrArg (ρ g) hc'sum
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, map_zero] at h2
        simpa [hρ, hv] using h2
      have hdsum : ∑ i, d i • v i = 0 := by
        simp only [hd, sub_smul, Finset.sum_sub_distrib, h1, hc'sum, sub_zero]
      have hsub : Finset.univ.filter (fun i => d i ≠ 0) ⊆
          (Finset.univ.filter (fun i => c' i ≠ 0)).erase i0 := by
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hi ⊢
        refine ⟨?_, ?_⟩
        · rintro rfl
          apply hi
          simp [hd, hc'i0]
        · intro h0
          apply hi
          simp [hd, h0]
      have hmem : i0 ∈ Finset.univ.filter (fun i => c' i ≠ 0) := by simp [hc'i0]
      have hdcard : (Finset.univ.filter (fun i => d i ≠ 0)).card ≤ n := by
        have h3 := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem hmem, hsupp] at h3
        omega
      intro i
      have h5 := ih d hdcard hdsum i
      rw [hd] at h5
      exact sub_eq_zero.mp h5
    have h4 := hind c' hfix hc'sum i0
    rw [hc'i0] at h4
    exact one_ne_zero h4

end GlobalTheory.Per
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharOnIdMulSqrtAbsNormInvMemSubring
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharOnIdMulSqrtAbsNormInvMemSubring
open NumberField IsDedekindDomain

noncomputable section
open scoped nonZeroDivisors

namespace GlobalTheory.HeckeIdealValue

open Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]

theorem finite_supp (χ : HChar L) (J : FractionalIdeal (𝓞 L)⁰ L) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 L) => χ.val v ^ FractionalIdeal.count L v J).Finite := by
  refine (Filter.eventually_cofinite.1 (FractionalIdeal.finite_factors J)).subset fun v hv h => hv ?_
  simp [h]

theorem onId_mul (χ : HChar L) {a b : FractionalIdeal (𝓞 L)⁰ L} (ha : a ≠ 0) (hb : b ≠ 0) :
    χ.onId (a * b) = χ.onId a * χ.onId b := by
  unfold HChar.onId
  rw [← finprod_mul_distrib (finite_supp χ _) (finite_supp χ _)]
  refine finprod_congr fun v => ?_
  rw [FractionalIdeal.count_mul L v ha hb, zpow_add]

theorem onId_one (χ : HChar L) : χ.onId (1 : FractionalIdeal (𝓞 L)⁰ L) = 1 := by
  unfold HChar.onId
  simp [FractionalIdeal.count_one]

theorem onId_prime (χ : HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    χ.onId ((v.asIdeal : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) = χ.val v := by
  unfold HChar.onId
  rw [finprod_eq_single _ v, FractionalIdeal.count_self, zpow_one]
  intro w hw
  rw [FractionalIdeal.count_maximal_coprime L w (Ne.symm hw), zpow_zero]

theorem inv_mem (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (O : Subring ℂ) (cc : Ideal (𝓞 L)) :
    cc ≠ ⊥ → (∀ P : HeightOneSpectrum (𝓞 L), cc ≤ P.asIdeal →
      (((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ))⁻¹ ∈ O) →
    (((χ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) : ℂˣ) : ℂ) *
      ((Real.sqrt (Ideal.absNorm cc) : ℝ) : ℂ))⁻¹ ∈ O := by
  induction cc using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h
  | h₂ I hI =>
    intro _ _
    have hI' : I = ⊤ := Ideal.isUnit_iff.1 hI
    subst hI'
    rw [FractionalIdeal.coeIdeal_top, onId_one, Ideal.absNorm_top]
    simp
  | h₃ I p hI hp ih =>
    intro _ hP
    let v : HeightOneSpectrum (𝓞 L) := ⟨p, Ideal.isPrime_of_prime hp, hp.ne_zero⟩
    have hv := hP v Ideal.mul_le_left
    have hrest := ih hI fun P hle => hP P (le_trans Ideal.mul_le_right hle)
    rw [FractionalIdeal.coeIdeal_mul, onId_mul χ (FractionalIdeal.coeIdeal_ne_zero.2 hp.ne_zero)
      (FractionalIdeal.coeIdeal_ne_zero.2 hI), map_mul, Nat.cast_mul,
      Real.sqrt_mul (Nat.cast_nonneg _), Units.val_mul, Complex.ofReal_mul]
    have e : χ.onId ((p : Ideal (𝓞 L)) : FractionalIdeal (𝓞 L)⁰ L) = χ.val v := onId_prime χ v
    rw [e]
    have : (((χ.val v : ℂˣ) : ℂ) * (χ.onId (I : FractionalIdeal (𝓞 L)⁰ L) : ℂ) *
        (((Real.sqrt (Ideal.absNorm p) : ℝ) : ℂ) * ((Real.sqrt (Ideal.absNorm I) : ℝ) : ℂ)))⁻¹ =
        (((χ.val v : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm v.asIdeal) : ℝ) : ℂ))⁻¹ *
        (((χ.onId (I : FractionalIdeal (𝓞 L)⁰ L) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm I) : ℝ) : ℂ))⁻¹ := by
      rw [← mul_inv]; congr 1; ring
    rw [this]
    exact O.mul_mem hv hrest

end GlobalTheory.HeckeIdealValue
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharOnIdMulSqrtAbsNormInvMemSubringStatement
open NumberField IsDedekindDomain

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeChar_onId_mul_sqrt_absNorm_inv_mem_subring : ∀ (L : Type) [Field L] [NumberField L] (χ : Formalism.L2.Host.HChar L) (O : Subring ℂ) (cc : Ideal (𝓞 L)), cc ≠ ⊥ → (∀ P : HeightOneSpectrum (𝓞 L), cc ≤ P.asIdeal → (((χ.val P : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm P.asIdeal) : ℝ) : ℂ))⁻¹ ∈ O) → (((χ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) : ℂˣ) : ℂ) * ((Real.sqrt (Ideal.absNorm cc) : ℝ) : ℂ))⁻¹ ∈ O := by
  first | exact @GlobalTheory.HeckeIdealValue.inv_mem | exact GlobalTheory.HeckeIdealValue.inv_mem | (intros; apply GlobalTheory.HeckeIdealValue.inv_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapPadicIntFinExtInjective
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

theorem exists_padicInt_of_mem_OL {l : ℕ} [Fact l.Prime] (LL : FinExt l) (x : ℚ_[l])
    (hx : algebraMap ℚ_[l] ↥LL.1 x ∈ OL LL) : ∃ y : ℤ_[l], algebraMap ℤ_[l] ℚ_[l] y = x := by
  have hint : IsIntegral ℤ_[l] (algebraMap ℚ_[l] ↥LL.1 x) := hx
  have hint' : IsIntegral ℤ_[l] x :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ_[l] ℚ_[l] ↥LL.1)
      (algebraMap ℚ_[l] ↥LL.1).injective).mp hint
  exact IsIntegrallyClosed.isIntegral_iff.mp hint'

theorem algebraMap_padicInt_finExt_injective {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    Function.Injective (algebraMap ℤ_[l] ↥LL.1) := by
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1]
  exact (algebraMap ℚ_[l] ↥LL.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])

theorem algebraMap_padicInt_OL_injective {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    Function.Injective (algebraMap ℤ_[l] ↥(OL LL)) := by
  intro a b h
  exact algebraMap_padicInt_finExt_injective LL (congrArg Subtype.val h)

private theorem associated_prime_of_valuation_eq_one {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l)
    (c : ℤ_[l]) (hc : P.v LL (algebraMap ℤ_[l] ↥LL.1 c) = 1) : Associated c (l : ℤ_[l]) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, AddValuation.map_zero] at hc
    exact WithTop.top_ne_one hc
  have hspec := PadicInt.unitCoeff_spec hc0
  set u := PadicInt.unitCoeff hc0
  have hnn : ∀ w : ℤ_[l], 0 ≤ P.v LL (algebraMap ℤ_[l] ↥LL.1 w) := fun w =>
    (P.v_O LL _).mpr (Subalgebra.algebraMap_mem _ w)
  have hu0 : P.v LL (algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l])) = 0 := by
    have h1 : P.v LL (algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l])) +
        P.v LL (algebraMap ℤ_[l] ↥LL.1 ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l])) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, Units.mul_inv, map_one, AddValuation.map_one]
    exact ((add_eq_zero_iff_of_nonneg (hnn _) (hnn _)).mp h1).1
  have hval : c.valuation = 1 := by
    rw [hspec, map_mul, AddValuation.map_mul, hu0, zero_add, map_pow, AddValuation.map_pow,
      map_natCast, P.v_l LL, nsmul_one] at hc
    exact_mod_cast hc
  refine ⟨u⁻¹, ?_⟩
  conv_lhs => rw [hspec]
  rw [hval, pow_one, mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

theorem associated_of_v_sub_one {l : ℕ} [Fact l.Prime] (P : LocPrime l) (LL : FinExt l)
    (y : ℤ_[l]) (x : ↥(OL LL)) (hy : algebraMap ℤ_[l] ↥(OL LL) y = x)
    (h : P.v LL (algebraMap ↥(OL LL) ↥LL.1 x - 1) = 1) : Associated (y - 1) (l : ℤ_[l]) := by
  apply associated_prime_of_valuation_eq_one P LL
  have hx : algebraMap ↥(OL LL) ↥LL.1 x = algebraMap ℤ_[l] ↥LL.1 y := by
    rw [← hy]
    rfl
  rw [map_sub, map_one, ← hx]
  exact h

theorem exists_units_hom_lift {Γ R S : Type} [Group Γ] [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) (c : Γ →* Sˣ) (hex : ∀ g, ∃ y : R, φ y = (c g : S)) :
    ∃ χ : Γ →* Rˣ, ∀ g, φ (χ g : R) = (c g : S) := by
  choose y hy using hex
  have hinv : ∀ g, y g * y g⁻¹ = 1 := fun g => hφ (by
    rw [map_mul, hy, hy, map_one, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one])
  have hinv' : ∀ g, y g⁻¹ * y g = 1 := fun g => by simpa using hinv g⁻¹
  let u : Γ → Rˣ := fun g => ⟨y g, y g⁻¹, hinv g, hinv' g⟩
  refine ⟨{ toFun := u, map_one' := ?_, map_mul' := ?_ }, fun g => hy g⟩
  · ext
    apply hφ
    simp [u, hy]
  · intro g h
    ext
    apply hφ
    simp [u, hy]

theorem exists_cyclotomicChar_padicInt_units : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ} (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n), ∃ χ : W.Gam →* ℤ_[l]ˣ, (∀ g, algebraMap ℤ_[l] ↥(OL LL) (χ g : ℤ_[l]) = (W.χΓ g : ↥(OL LL))) ∧ (W.s = 1 → Associated ((χ W.gam : ℤ_[l]) - 1) (l : ℤ_[l])) := by
  intro l _ P K LL n W
  have hex : ∀ g, ∃ y : ℤ_[l], algebraMap ℤ_[l] ↥(OL LL) y = (W.χΓ g : ↥(OL LL)) := by
    intro g
    obtain ⟨h, rfl⟩ := W.resΓ_onto g
    have hmem : algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ h : ℚ_[l]) ∈ OL LL := by
      rw [← W.χΓ_res h]
      exact (W.χΓ (W.resΓ h) : ↥(OL LL)).2
    obtain ⟨y, hy⟩ := exists_padicInt_of_mem_OL LL _ hmem
    refine ⟨y, Subtype.ext ?_⟩
    show algebraMap ℤ_[l] ↥LL.1 y = _
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1, hy, ← W.χΓ_res h]
    rfl
  obtain ⟨χ, hχ⟩ := exists_units_hom_lift (algebraMap ℤ_[l] ↥(OL LL))
    (algebraMap_padicInt_OL_injective LL) W.χΓ hex
  refine ⟨χ, hχ, fun hs => ?_⟩
  apply associated_of_v_sub_one P LL _ _ (hχ W.gam)
  have hg := W.gam_gen
  rw [hs, Nat.cast_one] at hg
  exact hg

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableInvAbsNormPrimesOfNotPrimeNorm
open NumberField IsDedekindDomain
open scoped Classical

namespace GlobalTheory

private lemma exists_prime_liesOver_absNorm_eq_pow (K : Type) [Field K] [NumberField K]
    (P : HeightOneSpectrum (𝓞 K)) :
    ∃ q : ℕ, q.Prime ∧ P.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) ∧
      ∃ f : ℕ, Ideal.absNorm P.asIdeal = q ^ f := by
  set I : Ideal ℤ := P.asIdeal.under ℤ with hI
  have hN : (Ideal.absNorm P.asIdeal : ℤ) ∈ I := by
    rw [hI, Ideal.mem_comap]
    simpa using Ideal.absNorm_mem P.asIdeal
  have hN0 : (Ideal.absNorm P.asIdeal : ℤ) ≠ 0 := by
    have := _root_.GlobalTheory.Mem.RayPrimes.two_le_absNorm P
    omega
  have hIbot : I ≠ ⊥ := fun h => hN0 (by simpa [h] using hN)
  have hprime := Submodule.IsPrincipal.prime_generator_of_isPrime I hIbot
  set g := Submodule.IsPrincipal.generator I
  refine ⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hprime, ?_, ?_⟩
  · refine ⟨?_⟩
    rw [Int.span_natAbs, Ideal.span_singleton_generator]
  · have hpr : Prime ((g.natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      exact hprime.abs
    haveI : P.asIdeal.LiesOver (Ideal.span {((g.natAbs : ℕ) : ℤ)}) :=
      ⟨by rw [Int.span_natAbs, Ideal.span_singleton_generator]⟩
    exact ⟨_, (Ideal.absNorm_eq_pow_inertiaDeg P.asIdeal hpr).trans (by rw [Int.natAbs_natCast])⟩

theorem _root_.GlobalTheory.summable_inv_absNorm_of_not_prime :
    ∀ (K : Type) [Field K] [NumberField K],
      Summable fun P : {P : HeightOneSpectrum (𝓞 K) // ¬ (Ideal.absNorm P.asIdeal).Prime} =>
        ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ)⁻¹ := by
  intro K _ _
  choose q hq hlies f hf using exists_prime_liesOver_absNorm_eq_pow K
  set d := Module.finrank ℚ K
  have hfib : ∀ (T : Finset {P : HeightOneSpectrum (𝓞 K) // ¬ (Ideal.absNorm P.asIdeal).Prime})
      (r : ℕ), (T.filter fun P => q P.1 = r).card ≤ d := by
    intro T r
    by_cases hr : ∃ P ∈ T, q P.1 = r
    · obtain ⟨P₀, -, rfl⟩ := hr
      have hspan : Ideal.span {((q P₀.1 : ℕ) : ℤ)} ≠ ⊥ := by
        simpa using (hq P₀.1).ne_zero
      haveI hsp : (Ideal.span {((q P₀.1 : ℕ) : ℤ)}).IsPrime :=
        (Ideal.span_singleton_prime (by simpa using (hq P₀.1).ne_zero)).mpr
          (Nat.prime_iff_prime_int.mp (hq P₀.1))
      haveI : (Ideal.span {((q P₀.1 : ℕ) : ℤ)}).IsMaximal := hsp.isMaximal hspan
      calc (T.filter fun P => q P.1 = q P₀.1).card
          ≤ (IsDedekindDomain.primesOverFinset (Ideal.span {((q P₀.1 : ℕ) : ℤ)}) (𝓞 K)).card := by
            refine Finset.card_le_card_of_injOn (fun P => P.1.asIdeal) ?_ ?_
            · intro P hP
              rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hspan]
              have hPq := (Finset.mem_filter.mp hP).2
              haveI := hlies P.1
              exact ⟨P.1.isPrime, by rw [← hPq]; infer_instance⟩
            · intro P _ P' _ h
              exact Subtype.ext (HeightOneSpectrum.ext h)
        _ ≤ d := Ideal.card_primesOverFinset_le_finrank (𝓞 K) ℚ K hspan
    · push_neg at hr
      rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr hr)]
      exact Nat.zero_le _
  have hsum : Summable fun n : ℕ => 1 / (n : ℝ) ^ 2 := Real.summable_one_div_nat_pow.mpr one_lt_two
  refine summable_of_sum_le (c := d * ∑' n : ℕ, 1 / (n : ℝ) ^ 2) (fun P => by positivity) ?_
  intro T
  have hle : ∀ P ∈ T, ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ)⁻¹ ≤ 1 / ((q P.1 : ℕ) : ℝ) ^ 2 := by
    intro P _
    have h2 := _root_.GlobalTheory.Mem.RayPrimes.two_le_absNorm P.1
    have hf2 : 2 ≤ f P.1 := by
      rcases Nat.lt_or_ge (f P.1) 2 with h | h
      · interval_cases hfP : f P.1
        · rw [hf P.1, hfP] at h2; simp at h2
        · exact absurd (by rw [hf P.1, hfP, pow_one]; exact hq P.1) P.2
      · exact h
    rw [one_div]
    apply inv_anti₀ (by have := (hq P.1).pos; positivity)
    rw [hf P.1]
    exact_mod_cast Nat.pow_le_pow_right (hq P.1).pos hf2
  calc ∑ P ∈ T, ((Ideal.absNorm P.1.asIdeal : ℕ) : ℝ)⁻¹
      ≤ ∑ P ∈ T, 1 / ((q P.1 : ℕ) : ℝ) ^ 2 := Finset.sum_le_sum hle
    _ = ∑ r ∈ T.image (fun P => q P.1), ∑ P ∈ T with q P.1 = r, 1 / ((q P.1 : ℕ) : ℝ) ^ 2 :=
        (Finset.sum_fiberwise_of_maps_to (fun P hP => Finset.mem_image_of_mem _ hP) _).symm
    _ = ∑ r ∈ T.image (fun P => q P.1),
          ((T.filter fun P => q P.1 = r).card : ℝ) * (1 / (r : ℝ) ^ 2) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_congr rfl (fun P hP => by rw [(Finset.mem_filter.mp hP).2]), Finset.sum_const,
          nsmul_eq_mul]
    _ ≤ ∑ r ∈ T.image (fun P => q P.1), (d : ℝ) * (1 / (r : ℝ) ^ 2) := by
        refine Finset.sum_le_sum fun r _ => ?_
        gcongr
        exact_mod_cast hfib T r
    _ = d * ∑ r ∈ T.image (fun P => q P.1), 1 / (r : ℝ) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ d * ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := by
        gcongr
        exact hsum.sum_le_tsum _ (fun n _ => by positivity)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLatticesIdempotentPositionBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLatticesIdempotentPositionBounded
noncomputable section

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial

namespace GlobalTheory.UnitLemma.Desc.PosCount

section Idem

variable {ι : Type} [Fintype ι] {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

theorem sum_smul_mul_idem {e : ι → A} (he : CompleteOrthogonalIdempotents e) (c : ι → R) (i : ι) (x : A) :
    (∑ j, c j • e j) * (e i * x) = c i • (e i * x) := by
  classical
  rw [Finset.sum_mul, Finset.sum_eq_single i]
  · rw [smul_mul_assoc, ← mul_assoc, (he.idem i).eq]
  · intro j _ hj
    rw [smul_mul_assoc, ← mul_assoc, he.ortho hj, zero_mul, smul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem sum_smul_mul {e : ι → A} (he : CompleteOrthogonalIdempotents e) (c : ι → R) (x : A) :
    (∑ j, c j • e j) * x = ∑ i, c i • (e i * x) := by
  calc (∑ j, c j • e j) * x = (∑ j, c j • e j) * (∑ i, e i * x) := by
        rw [← Finset.sum_mul, he.complete, one_mul]
    _ = ∑ i, (∑ j, c j • e j) * (e i * x) := Finset.mul_sum _ _ _
    _ = _ := Finset.sum_congr rfl fun i _ => sum_smul_mul_idem he c i x

theorem sum_smul_mul_cancel {e : ι → A} (he : CompleteOrthogonalIdempotents e) (c c' : ι → R)
    (h : ∀ i, c' i * c i = 1) (x : A) : (∑ j, c' j • e j) * ((∑ j, c j • e j) * x) = x := by
  rw [sum_smul_mul he c x, Finset.mul_sum]
  calc ∑ i, (∑ j, c' j • e j) * (c i • (e i * x)) = ∑ i, e i * x :=
        Finset.sum_congr rfl fun i _ => by
          rw [mul_smul_comm, sum_smul_mul_idem he, smul_smul, mul_comm, h, one_smul]
    _ = x := by rw [← Finset.sum_mul, he.complete, one_mul]

end Idem

variable (K : UQ) (B : InvAlg K)

def Sandwich (a : K.O) (N : ℕ) : Set (Submodule K.O B.A) :=
  {M | (∀ r : B.A, IsIntegral K.O r → a ^ N • r ∈ M) ∧ ∀ m ∈ M, IsIntegral K.O m}

theorem finite_quotient_span_pow {a : K.O} (ha : a ≠ 0) (N : ℕ) :
    Finite (K.O ⧸ Ideal.span {a ^ N}) := by
  rw [IsLocalRing.finite_quotient_iff]
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible K.O
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
  refine ⟨k * N, ?_⟩
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_le_span_singleton, mul_pow,
    ← Units.val_pow_eq_pow_val, Units.mul_left_dvd, ← pow_mul]

theorem sandwich_finite (hR : (Subalgebra.toSubmodule (integralClosure K.O B.A)).FG) {a : K.O} (ha : a ≠ 0)
    (N : ℕ) : (Sandwich K B a N).Finite := by
  set R := Subalgebra.toSubmodule (integralClosure K.O B.A) with hRdef
  haveI : Module.Finite K.O R := Module.Finite.iff_fg.mpr hR
  set I : Ideal K.O := Ideal.span {a ^ N}
  haveI := finite_quotient_span_pow K ha N
  set P : Submodule K.O R := I • (⊤ : Submodule K.O R)
  haveI : Module.Finite (K.O ⧸ I) (R ⧸ P) := Module.Finite.of_restrictScalars_finite K.O _ _
  haveI : Finite (R ⧸ P) := Module.finite_of_finite (K.O ⧸ I)
  haveI : Finite (Submodule K.O (R ⧸ P)) :=
    Finite.of_injective (fun Q : Submodule K.O (R ⧸ P) => (Q : Set (R ⧸ P))) SetLike.coe_injective
  let Φ : Submodule K.O B.A → Submodule K.O (R ⧸ P) := fun M => (M.comap R.subtype).map P.mkQ
  have key : ∀ M ∈ Sandwich K B a N, M = ((Φ M).comap P.mkQ).map R.subtype := by
    intro M hM
    have hP : P ≤ M.comap R.subtype := by
      refine Submodule.smul_le.2 fun r hr n _ => ?_
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul, mul_smul]
      exact M.smul_mem b (hM.1 _ n.2)
    rw [Submodule.comap_map_mkQ, sup_eq_right.2 hP, Submodule.map_comap_subtype,
      inf_eq_right.2 fun m hm => hM.2 m hm]
  have hinj : Set.InjOn Φ (Sandwich K B a N) := by
    intro M₁ h₁ M₂ h₂ h
    rw [key M₁ h₁, key M₂ h₂, h]
  exact Set.Finite.of_finite_image (Set.toFinite _) hinj

theorem card_pos_le : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι) (a : K.O),
    B.P.Separable → K.Small a → IsFrame B e π S → ∀ N : ℕ, ∃ C : ℕ, ∀ p : ι → ℤ,
    {M : Submodule K.O B.A | Pos B a e N M p}.Finite ∧ {M : Submodule K.O B.A | Pos B a e N M p}.ncard ≤ C := by
  intro K B ι _ e π S a hP ha hF N
  have he : CompleteOrthogonalIdempotents e := hF.1.1
  haveI : Algebra.Etale K.E B.A := GlobalTheory.etale_of_separable_charpoly_mulLeft K.E B.A B.g hP
  have hR := GlobalTheory.IntegralClosureFG.integralClosure_fg K.O K.E B.A
  have hfin := sandwich_finite K B hR ha.1 N
  refine ⟨(Sandwich K B a N).ncard, fun p => ?_⟩
  have hal : al K a ≠ 0 := by
    simpa using (IsFractionRing.injective K.O K.E).ne ha.1
  set t : B.A := ∑ j, (al K a ^ (-p j)) • e j with ht
  set t' : B.A := ∑ j, (al K a ^ (p j)) • e j with ht'
  have hcancel : ∀ x : B.A, t' * (t * x) = x := fun x =>
    sum_smul_mul_cancel he (fun j => al K a ^ (-p j)) (fun j => al K a ^ (p j))
      (fun i => by rw [← zpow_add₀ hal, add_neg_cancel, zpow_zero]) x
  have hmaps : ∀ M ∈ {M : Submodule K.O B.A | Pos B a e N M p}, mulLat K.O t M ∈ Sandwich K B a N := by
    intro M hM
    refine ⟨fun r hr => ?_, fun m hm => ?_⟩
    · refine Submodule.mem_map.2 ⟨∑ i, (al K a ^ (p i + N)) • (e i * r),
        Submodule.sum_mem _ fun i _ => (hM i).1 r hr, ?_⟩
      rw [LinearMap.mulLeft_apply, Finset.mul_sum]
      calc ∑ i, t * (al K a ^ (p i + N) • (e i * r)) = ∑ i, (al K a ^ N) • (e i * r) :=
            Finset.sum_congr rfl fun i _ => by
              rw [mul_smul_comm, ht, sum_smul_mul_idem he, smul_smul, ← zpow_add₀ hal,
                show p i + N + -p i = (N : ℤ) by ring, zpow_natCast]
        _ = a ^ N • r := by
            rw [← Finset.smul_sum, ← Finset.sum_mul, he.complete, one_mul, ← map_pow, algebraMap_smul]
    · obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hm
      rw [LinearMap.mulLeft_apply, ht, sum_smul_mul he]
      exact IsIntegral.sum _ fun i _ => (hM i).2 y hy
  have hinj : Set.InjOn (mulLat K.O t) {M : Submodule K.O B.A | Pos B a e N M p} := by
    intro M₁ _ M₂ _ h
    have hid : (LinearMap.mulLeft K.O t').comp (LinearMap.mulLeft K.O t) = LinearMap.id :=
      LinearMap.ext fun x => hcancel x
    have h' := congrArg (Submodule.map (LinearMap.mulLeft K.O t')) h
    simp only [mulLat, ← Submodule.map_comp, hid, Submodule.map_id] at h'
    exact h'
  exact ⟨Set.Finite.of_finite_image (hfin.subset (Set.image_subset_iff.2 hmaps)) hinj,
    Set.ncard_le_ncard_of_injOn _ hmaps hinj hfin⟩

end GlobalTheory.UnitLemma.Desc.PosCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLatticesIdempotentPositionBoundedStatement
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_lattices_idempotent_position_bounded : ∀ (K : UQ) (B : InvAlg K) (ι : Type) [Fintype ι] (e π : ι → B.A) (S : Finset ι) (a : K.O), B.P.Separable → K.Small a → IsFrame B e π S → ∀ N : ℕ, ∃ C : ℕ, ∀ p : ι → ℤ, {M : Submodule K.O B.A | Pos B a e N M p}.Finite ∧ {M : Submodule K.O B.A | Pos B a e N M p}.ncard ≤ C := by
  first | exact @GlobalTheory.UnitLemma.Desc.PosCount.card_pos_le | exact GlobalTheory.UnitLemma.Desc.PosCount.card_pos_le | (intros; apply GlobalTheory.UnitLemma.Desc.PosCount.card_pos_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEigenvectorOfTraceEqAddCharacter
namespace GlobalTheory

private lemma exists_char_augmentation_zero_acting_as_one {K Γ V : Type} [Field K] [Group Γ]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (ρ : Representation K Γ V)
    (χ : Γ →* Kˣ) (hs : ρ.IsSemisimpleRepresentation)
    (hno : ∀ v : V, (∀ g, ρ g v = ((χ g : Kˣ) : K) • v) → v = 0) :
    ∃ x : MonoidAlgebra K Γ, MonoidAlgebra.lift K K Γ ((Units.coeHom K).comp χ) x = 0 ∧
      ρ.asAlgebraHom x = 1 := by
  set ε := MonoidAlgebra.lift K K Γ ((Units.coeHom K).comp χ) with hε
  have hsm : IsSemisimpleModule (MonoidAlgebra K Γ) ρ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule ρ).mp hs
  let b := Module.finBasis K V
  let m : Fin (Module.finrank K V) → ρ.asModule := fun i => ρ.asModuleEquiv.symm (b i)
  let P : Submodule (MonoidAlgebra K Γ) (Fin (Module.finrank K V) → ρ.asModule) :=
    Submodule.map (LinearMap.toSpanSingleton (MonoidAlgebra K Γ) _ m)
      (RingHom.ker (ε : MonoidAlgebra K Γ →+* K))
  obtain ⟨C, hC⟩ := exists_isCompl P
  have hm : m ∈ P ⊔ C := by rw [hC.sup_eq_top]; trivial
  obtain ⟨p, hp, c, hc, hpc⟩ := Submodule.mem_sup.mp hm
  have hkill : ∀ x, ε x = 0 → x • c = 0 := by
    intro x hx
    have h1 : x • c ∈ P := by
      have : x • c = x • m - x • p := by rw [← hpc, smul_add, add_sub_cancel_left]
      rw [this]
      exact P.sub_mem (Submodule.mem_map.mpr ⟨x, RingHom.mem_ker.mpr hx,
        LinearMap.toSpanSingleton_apply _ _ _ _⟩) (P.smul_mem x hp)
    have h2 : x • c ∈ P ⊓ C := Submodule.mem_inf.mpr ⟨h1, C.smul_mem x hc⟩
    rwa [hC.inf_eq_bot, Submodule.mem_bot] at h2
  have hc0 : c = 0 := by
    funext i
    have hv := hno (ρ.asModuleEquiv (c i)) fun g => by
      have h := congrFun (hkill (MonoidAlgebra.single g 1 - MonoidAlgebra.single 1 ((χ g : Kˣ) : K))
        (by simp [hε, MonoidAlgebra.lift_single])) i
      change ρ.asModuleEquiv.symm (ρ.asAlgebraHom _ (ρ.asModuleEquiv (c i))) = 0 at h
      rw [LinearEquiv.map_eq_zero_iff, map_sub, Representation.asAlgebraHom_single,
        Representation.asAlgebraHom_single, one_smul, map_one, LinearMap.sub_apply,
        LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h
      exact h
    simpa using hv
  rw [hc0, add_zero] at hpc
  obtain ⟨y, hy, hym⟩ := Submodule.mem_map.mp (show m ∈ P from hpc ▸ hp)
  refine ⟨y, RingHom.mem_ker.mp hy, b.ext fun i => ?_⟩
  have h := congrFun hym i
  change ρ.asModuleEquiv.symm (ρ.asAlgebraHom y (ρ.asModuleEquiv (ρ.asModuleEquiv.symm (b i)))) =
    ρ.asModuleEquiv.symm (b i) at h
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.symm_apply_eq, LinearEquiv.apply_symm_apply] at h
  simpa using h

private lemma false_of_trace_pow_eq_card_add_one_sub {L ι : Type} [Field L] [CharZero L] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι L) (h : ∀ n : ℕ, (M ^ n).trace = ((Fintype.card ι : L) + 1) - 0 ^ n) :
    False := by
  set D : L := (Fintype.card ι : L) + 1 with hD
  have hD0 : D ≠ 0 := by rw [hD]; exact Nat.cast_add_one_ne_zero _
  have hpoly : ∀ f : Polynomial L, (Polynomial.aeval M f).trace = D * f.eval 1 - f.eval 0 := by
    intro f
    induction f using Polynomial.induction_on' with
    | add f g hf hg => simp only [map_add (f := _), Matrix.trace_add, hf, hg, Polynomial.eval_add]; ring
    | monomial n a =>
      rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
        Matrix.trace_smul, h n, Polynomial.eval_monomial, Polynomial.eval_monomial, one_pow,
        smul_eq_mul]
      ring
  set p := M.charpoly with hp
  have hvan : ∀ g : Polynomial L, D * (g * p).eval 1 - (g * p).eval 0 = 0 := by
    intro g
    rw [← hpoly, map_mul, hp, Matrix.aeval_self_charpoly, mul_zero, Matrix.trace_zero]
  have hp1 : p.eval 1 = 0 := by
    have := hvan Polynomial.X
    simp only [Polynomial.eval_mul, Polynomial.eval_X, one_mul, zero_mul, sub_zero] at this
    exact (mul_eq_zero.mp this).resolve_left hD0
  have hp0 : p.eval 0 = 0 := by
    have := hvan 1
    simpa [hp1] using this
  have hpne : p ≠ 0 := (Matrix.charpoly_monic M).ne_zero
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hpne 1
  set b := p.rootMultiplicity 1
  have hb : 0 < b := (Polynomial.rootMultiplicity_pos hpne).mpr hp1
  have hcop : IsCoprime ((Polynomial.X - Polynomial.C (1 : L)) ^ b) q :=
    ((Polynomial.irreducible_X_sub_C (1 : L)).coprime_iff_not_dvd.mpr hq).pow_left
  obtain ⟨u, v, huv⟩ := hcop
  have hq0 : q.eval 0 = 0 := by
    have := hp0
    rw [hpq, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C] at this
    exact (mul_eq_zero.mp this).resolve_left (pow_ne_zero _ (by norm_num))
  have he1 : (v * q).eval 1 = 1 := by
    have := congrArg (Polynomial.eval 1) huv
    simpa [Polynomial.eval_mul, zero_pow hb.ne'] using this
  have he0 : (v * q).eval 0 = 0 := by simp [Polynomial.eval_mul, hq0]
  have hidem : (v * q) * (v * q) = v * q - (u * v) * p := by
    rw [hpq]; linear_combination (v * q) * huv
  set E := Polynomial.aeval M (v * q) with hE
  have hEE : E * E = E := by
    rw [hE, ← map_mul, hidem, map_sub, map_mul (Polynomial.aeval M) (u * v) p, hp,
      Matrix.aeval_self_charpoly, mul_zero, sub_zero]
  have htrE : E.trace = D := by rw [hE, hpoly, he1, he0]; ring
  have hid : IsIdempotentElem (Matrix.toLin' E) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hEE]
  have htr := (LinearMap.IsIdempotentElem.isProj_range _ hid).trace
  rw [LinearMap.trace_eq_matrix_trace L (Pi.basisFun L ι), LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_toLin', htrE, hD] at htr
  have hle := Submodule.finrank_le (LinearMap.range (Matrix.toLin' E))
  rw [Module.finrank_fintype_fun_eq_card] at hle
  have : Fintype.card ι + 1 = Module.finrank L (LinearMap.range (Matrix.toLin' E)) := by
    exact_mod_cast htr
  omega

theorem _root_.GlobalTheory.exists_eigenvector_of_trace_eq_add_character :
    ∀ (K L Γ V ι : Type) [Field K] [Field L] [CharZero L] [Group Γ] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype ι] [DecidableEq ι] (φ : K →+* L) (ρ : Representation K Γ V) (σ : Γ →* Matrix ι ι L) (χ : Γ →* Kˣ), ρ.IsSemisimpleRepresentation → (∀ g, φ (LinearMap.trace K V (ρ g)) = (σ g).trace + φ ((χ g : Kˣ) : K)) → ∃ v : V, v ≠ 0 ∧ ∀ g, ρ g v = ((χ g : Kˣ) : K) • v := by
  intro K L Γ V ι _ _ _ _ _ _ _ _ _ φ ρ σ χ hs htr
  by_contra hcon
  push_neg at hcon
  have hno : ∀ v : V, (∀ g, ρ g v = ((χ g : Kˣ) : K) • v) → v = 0 := fun v hv => by
    by_contra h0
    obtain ⟨g, hg⟩ := hcon v h0
    exact hg (hv g)
  obtain ⟨x, hx, hρx⟩ := exists_char_augmentation_zero_acting_as_one ρ χ hs hno
  let S : MonoidAlgebra K Γ →+* Matrix ι ι L :=
    MonoidAlgebra.liftNCRingHom ((Matrix.scalar ι).comp φ) σ
      (fun _ _ => Matrix.scalar_commute _ (fun _ => Commute.all _ _) _)
  have hkey : ∀ z : MonoidAlgebra K Γ, φ (LinearMap.trace K V (ρ.asAlgebraHom z)) =
      (S z).trace + φ (MonoidAlgebra.lift K K Γ ((Units.coeHom K).comp χ) z) := by
    intro z
    refine MonoidAlgebra.induction_linear z ?_ ?_ ?_
    · simp
    · intro f g hf hg
      simp only [map_add (f := _), Matrix.trace_add, hf, hg]; ring
    · intro g r
      rw [Representation.asAlgebraHom_single, map_smul, smul_eq_mul, map_mul, htr g]
      have hS : S (MonoidAlgebra.single g r) = Matrix.scalar ι (φ r) * σ g := by
        simp [S, MonoidAlgebra.liftNCRingHom, MonoidAlgebra.liftNC_single]
      rw [hS]
      rw [MonoidAlgebra.lift_single, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul,
        Matrix.trace_smul, smul_eq_mul, smul_eq_mul, map_mul]
      simp only [MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply]
      ring
  have hdim := htr 1
  rw [map_one ρ, LinearMap.trace_one, map_natCast, map_one σ, Matrix.trace_one, map_one χ,
    Units.val_one, map_one φ] at hdim
  have hpow : ∀ n : ℕ, ((S x) ^ n).trace = ((Fintype.card ι : L) + 1) - 0 ^ n := by
    intro n
    have h1 := hkey (x ^ n)
    rw [map_pow, hρx, one_pow, LinearMap.trace_one, map_natCast, map_pow, map_pow, hx] at h1
    have h0 : φ ((0 : K) ^ n) = (0 : L) ^ n := by rw [map_pow, map_zero]
    linear_combination hdim - h1 - h0
  exact false_of_trace_pow_eq_card_add_one_sub (S x) hpow

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableQuadraticGaussIntegralMulNorm
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableQuadraticGaussIntegralMulNorm
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise ENNReal NNReal

namespace GlobalTheory.JR.WeilQuad.GaussTrans

theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (t s : A.Kˣ), (∃ ℓ : A.L, A.NL ℓ = s) → ∀ G : ℂ, IsStableGauss A ψ x μ t G → IsStableGauss A ψ x μ ((t * s : A.Kˣ) : A.K) (G * ((A.absK s : ℂ))⁻¹) := by
  intro F E _ _ _ _ U A ψ x μ ω hH t s ⟨ℓ, hℓ⟩ G ⟨Λ₀, ho₀, hc₀, hG⟩
  have := U.charZero; have := U.ultraF; have := U.lcF
  have : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  have := EtMeas.finite_L A
  obtain ⟨⟨b⟩, hinj, hN, -, -⟩ := GlobalTheory.JR.Et.quadratic_structure F E A
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.K
  obtain ⟨_, _, _, _, -⟩ := EtMeas.top_facts F A.L
  have : IsTopologicalRing A.L := IsModuleTopology.isTopologicalRing F A.L
  have : ContinuousStar A.L := ⟨IsModuleTopology.continuous_of_linearMap (EtMeas.starF A)⟩
  have hμ : μ.IsAddHaarMeasure := hH.2.2.2.1.1
  have hs' : algebraMap A.K A.L (s : A.K) = ℓ * star ℓ := by rw [← hℓ, hN]
  have hu : IsUnit ℓ := isUnit_of_mul_isUnit_left (hs' ▸ (s.isUnit.map (algebraMap A.K A.L)))
  set u : A.Lˣ := hu.unit with hu_def
  have hul : (u : A.L) = ℓ := hu.unit_spec
  have hmod : distribHaarChar A.L u = distribHaarChar A.K s :=
    GlobalTheory.JR.ModuleNorm.distribHaarChar_eq_norm A.K A.L b.equivFun.symm
      (IsModuleTopology.continuous_of_linearMap (b.equivFun.symm.toLinearMap.restrictScalars F))
      (IsModuleTopology.continuous_of_linearMap (b.equivFun.toLinearMap.restrictScalars F)) u s
      (by rw [hul]; exact hs')
  have hmap : μ.map (fun y => u • y) = (distribHaarChar A.L u⁻¹ : ℝ≥0∞) • μ := by
    ext S hS
    rw [Measure.map_apply (measurable_const_smul u) hS, Set.preimage_smul, Measure.smul_apply, smul_eq_mul,
      distribHaarChar_mul]
  have hemb : MeasurableEmbedding (fun y : A.L => u • y) :=
    (Homeomorph.smul u).measurableEmbedding
  have key : ∀ Λ : AddSubgroup A.L, gaussInt A ψ x μ ((t * s : A.Kˣ) : A.K) Λ =
      ((A.absK s : ℂ))⁻¹ * gaussInt A ψ x μ t (u • Λ : AddSubgroup A.L) := by
    intro Λ
    have h1 : gaussInt A ψ x μ ((t * s : A.Kˣ) : A.K) Λ =
        ∫ y in (Λ : Set A.L), A.psiK ψ ((t : A.K) * x * A.NL (u • y)) ∂μ := by
      unfold gaussInt
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      have hNm : A.NL (u • y) = s * A.NL y := by
        rw [Units.smul_def, hul, smul_eq_mul]
        unfold Et.NL
        rw [map_mul]
        exact congrArg (· * _) hℓ
      simp only
      rw [hNm]
      push_cast; ring_nf
    have h2 := hemb.setIntegral_map (μ := μ) (fun z => A.psiK ψ ((t : A.K) * x * A.NL z)) ((u • Λ : AddSubgroup A.L) : Set A.L)
    have hpre : (fun y => u • y) ⁻¹' ((u • Λ : AddSubgroup A.L) : Set A.L) = Λ := by
      ext y
      simp only [Set.mem_preimage, SetLike.mem_coe]
      exact ⟨fun h => by simpa using (AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem.1 h),
        fun h => AddSubgroup.smul_mem_pointwise_smul _ _ _ h⟩
    rw [hpre, hmap, Measure.restrict_smul, integral_smul_measure] at h2
    rw [h1, ← h2]
    unfold gaussInt
    rw [Complex.real_smul, EtMeas.absK_unit, ENNReal.coe_toReal, map_inv, hmod]
    congr 1
    push_cast
    rfl
  have hcoe : ∀ (v : A.Lˣ) (M : AddSubgroup A.L), ((v • M : AddSubgroup A.L) : Set A.L) = v • (M : Set A.L) :=
    fun v M => AddSubgroup.coe_pointwise_smul v M
  refine ⟨u⁻¹ • Λ₀, ?_, ?_, fun Λ hoΛ hcΛ hle => ?_⟩
  · rw [hcoe]; exact ho₀.smul _
  · rw [hcoe]; exact hc₀.smul _
  · rw [key, hG (u • Λ) (by rw [hcoe]; exact hoΛ.smul _) (by rw [hcoe]; exact hcΛ.smul _) ?_, mul_comm]
    intro z hz
    have : u⁻¹ • z ∈ Λ := hle (AddSubgroup.smul_mem_pointwise_smul _ _ _ hz)
    exact AddSubgroup.mem_pointwise_smul_iff_inv_smul_mem.2 this

end GlobalTheory.JR.WeilQuad.GaussTrans
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StableQuadraticGaussIntegralMulNormStatement
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stableQuadraticGaussIntegral_mul_norm : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.Kˣ) (μ : Measure A.L) (ω : A.K → ℂ), Hyp A ψ x μ ω → ∀ (t s : A.Kˣ), (∃ ℓ : A.L, A.NL ℓ = s) → ∀ G : ℂ, IsStableGauss A ψ x μ t G → IsStableGauss A ψ x μ ((t * s : A.Kˣ) : A.K) (G * ((A.absK s : ℂ))⁻¹) := by
  first | exact @GlobalTheory.JR.WeilQuad.GaussTrans.main | exact GlobalTheory.JR.WeilQuad.GaussTrans.main | (intros; apply GlobalTheory.JR.WeilQuad.GaussTrans.main <;> assumption)
end
end
