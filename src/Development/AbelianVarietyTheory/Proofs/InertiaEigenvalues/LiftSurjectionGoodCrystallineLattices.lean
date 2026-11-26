module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineClassFromMonodromyKernelElement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftingTheoremPhiModulesExactTriple
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisClassOfMonodromyEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.AdmissibleSignatures
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures

open GlobalTheory.BK PowerSeries

structure Admissible (l e N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ) : Prop where
  frob_mem : ∀ c ∈ Sig, (l : ZMod e) * c ∈ Sig
  zero_mem_Sig : (0 : ZMod e) ∈ Sig
  card_Sig : Sig.card ≤ N
  two_le : 2 ≤ N
  range_U : ∀ i ∈ U, -(η : ℤ) ≤ i ∧ i ≤ (H : ℤ)
  zero_mem_U : (0 : ℤ) ∈ U
  card_U : U.card ≤ N + 1
  one_le : 1 ≤ η
  lt : η < H
  large : 40 * (H * N ^ 2 + N ^ 3) < l

def cOne (l : ℕ) {e : ℕ} (η : ℕ) (Sig : Finset (ZMod e)) : ℕ := η * (maxPeriod l Sig + 1)

def ZetaBound : Prop :=
  ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K]
    [NeZero e] [NeZero a] [TameDescentExponentData K l e a]
    (N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), Admissible l e N η H Sig U →
    ∀ D : BKDat O K l e a ι η H, D.IsOfType (Sig : Set (ZMod e)) (U : Set ℤ) →
    ∀ y' ∈ D.Y', ∀ m ∈ D.Minv, D.Mon (y' + D.phi m) = 0 →
      (l : K) ^ cOne l η Sig • D.zeta (y' + D.phi m) ∈ D.MM

section Basic₂

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {l e a : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] [Fact l.Prime]
  [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] {η H : ℕ}
  {D : BKDat O K l e a ι η H}

omit [NeZero e]

theorem add_phi_mem_Y {y' m : Vec K a ι} (hy : y' ∈ D.Y') (hm : m ∈ D.Minv) :
    y' + D.phi m ∈ D.Y :=
  add_mem (D.desc.Y'_le_Y η hy)
    ⟨D.upper _ (D.phi_mem_L hm.1), fun g => by rw [D.desc.act_phi, hm.2 g]⟩

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGoodLatticeKernelOfSurjectionGoodLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGoodLatticeKernelOfSurjectionGoodLattice
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.KerGood

theorem map_aeval {R M N : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (F : M →ₗ[R] N) (A : Module.End R M) (A' : Module.End R N) (hA : ∀ y, F (A y) = A' (F y))
    (p : Polynomial R) (y : M) : F (Polynomial.aeval A p y) = Polynomial.aeval A' p (F y) := by
  induction p using Polynomial.induction_on generalizing y with
  | C c => simp [Module.algebraMap_end_apply]
  | add p q hp hq => simp only [map_add (f := _), LinearMap.add_apply, hp, hq]
  | monomial n c h =>
    simp only [pow_succ, ← mul_assoc, map_mul, Polynomial.aeval_X, Module.End.mul_apply] at h ⊢
    rw [h (A y), hA]

theorem isGood_of_injective (hF : GlobalTheory.Published.FontaineBcris) {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a]
    {ϖ : PiSys l e} {LL : FinExt l} {Pl : LocPrime l} {AI : LocAinf l Pl} (hs : IsStd Pl AI)
    {Sig : Finset (ZMod e)} {U : Finset ℤ} {T₀ T₁ : QLat LL} (f : T₀.V →ₗ[↥LL.1] T₁.V)
    (hf : Function.Injective f) (he : ∀ g x, f (T₀.ρ g x) = T₁.ρ g (f x))
    (hT : IsGood a ϖ Pl T₁ Sig U) : IsGood a ϖ Pl T₀ Sig U := by
  refine ⟨?_, ?_, ?_⟩
  · have hS := (GlobalTheory.RegularRing.fontaineFormalism hF l Pl AI hs).2.2.2.1 (ϖ.field a) LL
    exact hS _ (resF T₁ (ϖ.field a)).ρ _ (resF T₀ (ϖ.field a)).ρ f (fun g x => he _ x) hf hT.crys
  · intro γ hγ w hw x hx
    obtain ⟨r, hr⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hf)
    have hrf : ∀ v, r (f v) = v := fun v => LinearMap.congr_fun hr v
    have hRF : ∀ y, GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) r
        (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f y) = y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB, hrf]
      | add y z hy hz => simp only [map_add (f := _), hy, hz]
    have hFi : Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f) :=
      Function.LeftInverse.injective hRF
    have hFx := GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB_mem (Pl.PD (ϖ.field a)) (ρ := (resF T₀ (ϖ.field a)).ρ)
      (ρ' := (resF T₁ (ϖ.field a)).ρ) (f := f) (fun g x => he _ x) x hx
    have h1 := hT.type γ hγ w hw _ hFx
    have hc : ∀ y, GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f
        (actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T₀.ρ γ y) =
        actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T₁.ρ γ (GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB (Qp := ℚ_[l]) (B := Pl.R.B) f y) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul v b => simp [GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation.tensorB, actVB, he]
      | add y z hy hz => simp only [map_add (f := _), hy, hz]
    apply hFi
    exact (map_aeval _ _ _ hc _ x).trans (h1.trans (map_zero _).symm)
  · intro τ b hb
    exact hT.jumps τ b (GlobalTheory.HTW.isJumpV_of_injective _ _ T₁.ρ f hf he τ b hb)

theorem main : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ) (T₁ T₂ : QLat LL) (g : LatHom T₁.L T₂.L), g.Onto → IsGood a ϖ Pl T₁ Sig U → ∃ (T₀ : QLat LL) (f : LatHom T₀.L T₁.L), IsSESLat (Qp := ℚ_[l]) f g ∧ IsGood a ϖ Pl T₀ Sig U := by
  intro hF l _ a e _ _ ϖ LL _ _ Pl AI hs Sig U T₁ T₂ g hg hT
  obtain ⟨⟨_, hD, hFr⟩, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l LL
  have hden : Formalism.MainNotions.LiftingTheory.lker_Den ↥LL.1 ↥(OL LL) := by
    intro c
    obtain ⟨⟨x, s⟩, hxs⟩ := IsLocalization.surj (nonZeroDivisors ↥(OL LL)) c
    refine ⟨s, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2, x, ?_⟩
    rw [mul_comm]
    exact hxs
  have hinj : Function.Injective (Formalism.MainNotions.LiftingTheory.lker_ι g hg hden).f := fun x y h => Subtype.ext h
  refine ⟨Formalism.MainNotions.LiftingTheory.lker_T₀ g hg hden, Formalism.MainNotions.LiftingTheory.lker_ι g hg hden, ?_,
    isGood_of_injective hF hs _ hinj (Formalism.MainNotions.LiftingTheory.lker_ι g hg hden).equiv hT⟩
  exact ⟨hinj, Formalism.MainNotions.LiftingTheory.lker_surj g hg, hg,
    fun x => ⟨fun h => ⟨⟨x, h⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩, fun y hy => hy⟩

end GlobalTheory.KerGood
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGoodLatticeKernelOfSurjectionGoodLatticeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGoodLattice_kernel_of_surjection_goodLattice : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (Sig : Finset (ZMod e)) (U : Finset ℤ) (T₁ T₂ : QLat LL) (g : LatHom T₁.L T₂.L), g.Onto → IsGood a ϖ Pl T₁ Sig U → ∃ (T₀ : QLat LL) (f : LatHom T₀.L T₁.L), IsSESLat (Qp := ℚ_[l]) f g ∧ IsGood a ϖ Pl T₀ Sig U := by
  first | exact @GlobalTheory.KerGood.main | exact GlobalTheory.KerGood.main | (intros; apply GlobalTheory.KerGood.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZetaMemPowInvPhiModuleLattice
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLpowEisensteinPowTwistedDecomp
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLpowEisensteinPowTwistedDecomp
noncomputable section

namespace GlobalTheory.BK

open PowerSeries

section Helpers

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] {a : ℕ} {ι : Type}

theorem Epow_smul_mem_of_hasU (l e : ℕ) {B : Subalgebra O K⟦X⟧} [HasU B]
    (W : Submodule B (Vec K a ι)) (k : ℕ) {x : Vec K a ι} (hx : x ∈ W) : E K l e ^ k • x ∈ W := by
  have := W.smul_mem (EIn l e B ^ k) hx
  rwa [Subalgebra.smul_def, SubmonoidClass.coe_pow, coe_EIn] at this

theorem natPow_smul_mem {R M : Type} [Semiring R] [AddCommMonoid M] [Module R M] [Module K M]
    (W : Submodule R M) (l n : ℕ) {x : M} (hx : x ∈ W) : (l : K) ^ n • x ∈ W := by
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  exact W.nsmul_mem hx _

end Helpers

theorem lpow_Epow_twistedMon_decomp : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (c : ℕ), 1 ≤ η → η < H → 14 * H < l → 10 * H + 2 ≤ l → ∀ y' ∈ D.Y', ∀ m ∈ D.Minv, (l : K) ^ c • D.zeta (D.phi m) ∈ D.MM → ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), Ezpow K l e (-(2 * H : ℤ)) • f ∈ D.Man ∧ (l : K) ^ c • (E K l e ^ (2 * H) • (E K l e • D.zeta (y' + D.phi m) - D.EN (y' + D.phi m))) = p + ((l : K) ^ (3 * H))⁻¹ • f := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D c h1 h2 h3 h4 y' hy' m hm hc
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hr : ((l : K) ^ (3 * H)) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  have IC := GlobalTheory.T.breuilKisin_integrality_computation O K l e a ι η H D h2 h4
  obtain ⟨p₁, hp₁, f₁, hf₁, h₁⟩ := GlobalTheory.T.breuilKisin_zeta_fine_bound_second_basis O K l e a ι η H D h1 h2 h3 y' hy'
  obtain ⟨p', hp', f', hf', h'⟩ := IC.1 _ hc
  have hy : y' + D.phi m ∈ D.EM η := by
    refine add_mem ((D.desc.Y'_le_Y η hy').1 : y' ∈ D.EM η) ?_
    rw [mem_divE]
    exact D.upper _ (D.phi_mem_L hm.1)
  obtain ⟨p'', hp'', f'', hf'', h''⟩ := IC.2.2 _ hy
  set r : K := (l : K)
  set u : K⟦X⟧ := E K l e
  have hF : (u ^ (2 * H + 1) • (r ^ c • f₁) + r ^ (3 * H) • (u ^ (2 * H + 1) • f') -
      r ^ (3 * H) • (r ^ c • f'')) ∈ D.FilMM (10 * H) :=
    sub_mem (add_mem (Epow_smul_mem_of_hasU l e _ _ (natPow_smul_mem _ _ _ hf₁))
      (natPow_smul_mem _ _ _ (Epow_smul_mem_of_hasU l e _ _ hf')))
      (natPow_smul_mem _ _ _ (natPow_smul_mem _ _ _ hf''))
  refine ⟨u ^ (2 * H + 1) • (r ^ c • r ^ (l - 14 * H) • p₁) + u ^ (2 * H + 1) • p' - r ^ c • p'',
    sub_mem (add_mem (Epow_smul_mem_of_hasU l e _ _ (natPow_smul_mem _ _ _ (natPow_smul_mem _ _ _ hp₁)))
      (Epow_smul_mem_of_hasU l e _ _ hp')) (natPow_smul_mem _ _ _ hp''), _, hF, IC.2.1 _ hF, ?_⟩
  have hinv : (r ^ (3 * H))⁻¹ • (u ^ (2 * H + 1) • (r ^ c • f₁) + r ^ (3 * H) • (u ^ (2 * H + 1) • f') -
      r ^ (3 * H) • (r ^ c • f'')) =
      u ^ (2 * H + 1) • (r ^ c • ((r ^ (3 * H))⁻¹ • f₁)) + u ^ (2 * H + 1) • f' - r ^ c • f'' := by
    rw [smul_sub, smul_add, inv_smul_smul₀ hr, inv_smul_smul₀ hr, smul_comm (r ^ (3 * H))⁻¹ (u ^ (2 * H + 1)),
      smul_comm (r ^ (3 * H))⁻¹ (r ^ c)]
  rw [hinv, map_add D.zeta, h₁, smul_sub, smul_smul (u ^ (2 * H)) u, ← pow_succ, smul_sub,
    smul_comm (r ^ c) (u ^ (2 * H + 1)), smul_add (r ^ c) _ (D.zeta (D.phi m)), h', h'']
  simp only [smul_add]
  abel

end GlobalTheory.BK
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinLpowEisensteinPowTwistedDecompStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_lpow_eisensteinPow_twisted_decomp : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (c : ℕ), 1 ≤ η → η < H → 14 * H < l → 10 * H + 2 ≤ l → ∀ y' ∈ D.Y', ∀ m ∈ D.Minv, (l : K) ^ c • D.zeta (D.phi m) ∈ D.MM → ∃ p ∈ D.L, ∃ f ∈ D.FilMM (10 * H), Ezpow K l e (-(2 * H : ℤ)) • f ∈ D.Man ∧ (l : K) ^ c • (E K l e ^ (2 * H) • (E K l e • D.zeta (y' + D.phi m) - D.EN (y' + D.phi m))) = p + ((l : K) ^ (3 * H))⁻¹ • f := by
  first | exact @GlobalTheory.BK.lpow_Epow_twistedMon_decomp | exact GlobalTheory.BK.lpow_Epow_twistedMon_decomp | (intros; apply GlobalTheory.BK.lpow_Epow_twistedMon_decomp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowSmulPhiMemLatticeOfMemFiltration
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowSmulPhiMemLatticeOfMemFiltration
noncomputable section

namespace GlobalTheory.BK

open PowerSeries

theorem padicValNat_factorial_le_sub (l i j : ℕ) [hp : Fact l.Prime] (hji : j ≤ i) (hjl : j < l) :
    padicValNat l i.factorial ≤ i - j := by
  have hL : (l - 1) * padicValNat l i.factorial = i - (l.digits i).sum := by
    simpa only [Nat.padicValNat_def] using (Nat.Prime.sub_one_mul_multiplicity_factorial (n := i) hp.out)
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [_root_.Nat.padicValNat_def (n := 1)]
  have hpos : 0 < (l.digits i).sum := by
    rcases Nat.eq_zero_or_pos (l.digits i).sum with h0 | h0
    · exfalso
      have hne : l.digits i ≠ [] := Nat.digits_ne_nil_iff_ne_zero.mpr hi.ne'
      have h1 := Nat.getLast_digit_ne_zero l hi.ne'
      have h2 := List.sum_eq_zero_iff.1 h0 _ (List.getLast_mem hne)
      exact h1 h2
    · exact h0
  have hsum : (l.digits i).sum ≤ i := Nat.digit_sum_le l i
  have hl2 := hp.out.two_le
  set v := padicValNat l i.factorial
  rcases Nat.eq_zero_or_pos v with hv | hv
  · omega
  · have : (l - 1) * v ≤ i - 1 := by omega
    clear_value v
    have h3 : v + (l - 1) ≤ (l - 1) * v + 1 := by
      obtain ⟨L, hLe⟩ : ∃ L, l - 1 = L + 1 := ⟨l - 2, by omega⟩
      obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
      rw [hLe]
      nlinarith
    omega

section Padic

variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K]


omit [IsUltrametricDist K] in
theorem norm_pow_sub_le_norm_factorial {i j : ℕ} (hji : j ≤ i) (hjl : j < l) :
    ‖(l : K)‖ ^ (i - j) ≤ ‖(i.factorial : K)‖ := by
  rw [norm_l, norm_natCast_eq l, Padic.norm_eq_zpow_neg_valuation (by
    exact_mod_cast i.factorial_ne_zero), Padic.valuation_natCast, inv_pow, zpow_neg, zpow_natCast]
  have h1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_le
  exact inv_anti₀ (by positivity)
    (pow_le_pow_right₀ h1 (by
      simpa only [Nat.padicValNat_def] using padicValNat_factorial_le_sub l i j hji hjl))

theorem C_mem_S {e : ℕ} {c : K} (hc : ‖c‖ ≤ 1) : C c ∈ S O K e := by
  rw [← monomial_zero_eq_C_apply]
  exact monomial_mem_S (mul_le_one₀ hc (wS_nonneg _ _) (wS_le_one _ _))

theorem exists_frob_E_eq (e : ℕ) [NeZero e] : ∃ d ∈ S O K e, frob K l (E K l e) = C (l : K) * d := by
  refine ⟨1 + monomial (e * l) ((l : K)⁻¹), add_mem (one_mem _) (monomial_mem_S ?_), ?_⟩
  · rw [wS, Nat.mul_div_cancel_left _ (NeZero.pos e), norm_inv]
    have h0 : 0 < ‖(l : K)‖ := norm_pos_iff.2 (l_ne_zero l)
    rw [inv_mul_le_one₀ h0]
    exact norm_natCast_le_of_dvd (Nat.dvd_factorial (Fact.out : l.Prime).pos le_rfl)
  · rw [E, map_add (f := _), map_pow, frob_X, map_natCast, monomial_eq_C_mul_X_pow, mul_add, mul_one,
      ← mul_assoc, ← map_mul, mul_inv_cancel₀ (l_ne_zero l), map_one, one_mul, ← pow_mul,
      mul_comm l e, add_comm, map_natCast]

theorem exists_frob_Ediv_eq (e : ℕ) [NeZero e] {i j : ℕ} (hji : j ≤ i) (hjl : j < l) :
    ∃ s ∈ S O K e, frob K l (Ediv K l e i) = C ((l : K) ^ j) * s := by
  obtain ⟨d, hd, hE⟩ := exists_frob_E_eq (O := O) (K := K) l e
  have hf : (i.factorial : K) ≠ 0 := natCast_ne_zero' l i.factorial_ne_zero
  refine ⟨C ((l : K) ^ (i - j) / (i.factorial : K)) * d ^ i, mul_mem (C_mem_S ?_) (pow_mem hd i), ?_⟩
  · rw [norm_div, norm_pow]
    exact div_le_one_of_le₀ (norm_pow_sub_le_norm_factorial l hji hjl) (norm_nonneg _)
  · have key : (i.factorial : K)⁻¹ * (l : K) ^ i = (l : K) ^ j * ((l : K) ^ (i - j) / (i.factorial : K)) := by
      rw [mul_div_assoc', ← pow_add, Nat.add_sub_cancel' hji, div_eq_inv_mul]
    rw [Ediv, map_mul, frob_C, map_pow, hE, mul_pow, ← map_pow, ← mul_assoc, ← map_mul, key,
      map_mul, mul_assoc]

theorem exists_frob_eq_of_mem_Fil (e : ℕ) [NeZero e] {j : ℕ} (hjl : j < l) {r : S O K e}
    (hr : r ∈ Fil O K l e j) : ∃ s ∈ S O K e, frob K l (r : K⟦X⟧) = C ((l : K) ^ j) * s := by
  obtain ⟨g, hg, h, rfl⟩ := (mem_Fil l).1 hr j
  have key : ∀ x ∈ FilPre O K l e j, ∃ s ∈ S O K e, frob K l (x : K⟦X⟧) = C ((l : K) ^ j) * s := by
    intro x hx
    have hx' : x ∈ Submodule.span (S O K e) {x : S O K e | ∃ i, j ≤ i ∧ (x : K⟦X⟧) = Ediv K l e i} := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, hi, hxi⟩ := hx
      rw [hxi]
      exact exists_frob_Ediv_eq l e hi hjl
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨s, hs, h1⟩ := hx
      obtain ⟨t, ht, h2⟩ := hy
      exact ⟨s + t, add_mem hs ht, by rw [Subalgebra.coe_add, map_add (f := _), h1, h2, mul_add]⟩
    | smul c x _ hx =>
      obtain ⟨s, hs, h1⟩ := hx
      exact ⟨frob K l c * s, mul_mem (frob_mem_S l c.2) hs, by
        rw [smul_eq_mul, Subalgebra.coe_mul, map_mul, h1]; ring⟩
  obtain ⟨s, hs, h1⟩ := key g hg
  refine ⟨s + frob K l h, add_mem hs (frob_mem_S l h.2), ?_⟩
  rw [Subalgebra.coe_add, Subalgebra.coe_mul, map_add (f := _), map_mul, h1, mul_add]
  congr 2
  simp

end Padic

theorem phi_FilMM_mem : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (j : ℕ), j < l → ∀ v ∈ D.FilMM j, ∃ v' ∈ D.MM, (l : K) ^ η • D.phi v = (l : K) ^ j • v' := by
  intro O K _ _ _ _ _ _ l e a ι _ _ _ _ _ _ _ η H D j hjl v hv
  refine Submodule.smul_induction_on (p := fun v => ∃ v' ∈ D.MM, (l : K) ^ η • D.phi v = (l : K) ^ j • v')
    hv (fun r hr n hn => ?_) (fun x y hx hy => ?_)
  · obtain ⟨s, hs, hfs⟩ := exists_frob_eq_of_mem_Fil l e hjl hr
    have h3 := D.l_pow_smul_phi_mem_MM (k := η) (D.smul_mem_Mext (A_le_S l e) hn)
    refine ⟨s • ((l : K) ^ η • D.phi n), PhiMod.smul_mem_MM _ hs h3, ?_⟩
    rw [Subalgebra.smul_def, PhiMod.phi_smul, hfs, ← smul_eq_C_mul, smul_assoc,
      smul_comm ((l : K) ^ η) ((l : K) ^ j), smul_comm ((l : K) ^ η) s]
  · obtain ⟨v₁, h₁, e₁⟩ := hx
    obtain ⟨v₂, h₂, e₂⟩ := hy
    exact ⟨v₁ + v₂, add_mem h₁ h₂, by rw [map_add (f := _), smul_add, e₁, e₂, smul_add]⟩

end GlobalTheory.BK
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowSmulPhiMemLatticeOfMemFiltrationStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_pow_smul_phi_mem_lattice_of_mem_filtration : ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Algebra O K] [IsUnitBall O K] (l e a : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] [Fact l.Prime] [NormedAlgebra ℚ_[l] K] [NeZero e] [NeZero a] [TameDescentExponentData K l e a] (η H : ℕ) (D : BKDat O K l e a ι η H) (j : ℕ), j < l → ∀ v ∈ D.FilMM j, ∃ v' ∈ D.MM, (l : K) ^ η • D.phi v = (l : K) ^ j • v' := by
  first | exact @GlobalTheory.BK.phi_FilMM_mem | exact GlobalTheory.BK.phi_FilMM_mem | (intros; apply GlobalTheory.BK.phi_FilMM_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZetaMemPowInvPhiModuleLattice
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.ZetaDenominator

theorem zetaBound : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.ZetaBound := by
  intro O K _ _ _ _ _ l e a ι _ _ _ _ _ _ _ N η H Sig U hA D hT y' hy' m hm hMon
  haveI : CompleteSpace K := by
    haveI := TameDescentExponentData.finite (K := K) (l := l) (e := e) (a := a)
    exact FiniteDimensional.complete ℚ_[l] K
  have hl : l.Prime := Fact.out
  have ha : 1 ≤ a := NeZero.one_le
  obtain ⟨hr1, hrN, hrper⟩ := GlobalTheory.T.maxFrobeniusOrbitLengthDiff_bounds_zmod l e a hl ha (TameDescentExponentData.succ_eq (K := K)) Sig N
    hA.frob_mem hA.zero_mem_Sig hA.card_Sig hA.two_le
  obtain ⟨-, n2, n3, -, -, n6⟩ := GlobalTheory.T.numerical_conditions_theorem_T_large_prime l H N η (maxPeriod l Sig) hA.two_le hA.one_le hA.lt hrN hA.large
  have hl2 : l ≠ 2 := by have := hA.lt; have := hA.one_le; omega
  have hφm := GlobalTheory.T.prime_pow_smul_descent_phi_mem_lattice_of_orbit_bound O K l e a ι η H D (maxPeriod l Sig) hr1
    (fun τ c hc => hrper c (hT.chars_subset τ hc)) n6 hl2 m hm
  obtain ⟨P0, hP0, F0, hF0, hQF, hdec⟩ := GlobalTheory.T.breuilKisin_lpow_eisensteinPow_twisted_decomp O K l e a ι η H D (η * (maxPeriod l Sig + 1)) hA.one_le hA.lt
    (by have := hA.one_le; omega) (by omega) y' hy' m hm hφm
  show (l : K) ^ (η * (maxPeriod l Sig + 1)) • D.zeta (y' + D.phi m) ∈ D.MM
  set c₁ := η * (maxPeriod l Sig + 1)
  set y := y' + D.phi m
  set w := E K l e • D.zeta y - D.EN y with hw_def
  have hw : w ∈ D.Man := by
    have h : D.EN y - E K l e • D.zeta y ∈ D.Man := (D.cls_eq_zero_iff).1 (by rw [← PhiMod.Mon_apply]; exact hMon)
    have := D.Man.neg_mem h
    rwa [neg_sub] at this
  obtain ⟨c, hc, hcE⟩ := exists_mul_frob_E (O := O) (K := K) l e
  have hζ : D.zeta y = c • D.phi w := by
    have h1 : w = E K l e • (D.zeta y - D.conn y) := by simp only [hw_def, PhiMod.EN_apply, smul_sub]
    rw [h1, PhiMod.phi_smul, smul_smul, hcE]
    conv_lhs => rw [PhiMod.zeta_eq, PhiMod.lphi_apply]
    simp only [Nat.cast_smul_eq_nsmul]
  have hE1 : E K l e ^ (2 * H) * Ezpow K l e (-(2 * H : ℤ)) = 1 := by
    have := E_pow_mul_Ezpow_neg (K := K) l e (2 * H)
    push_cast at this
    exact this
  set Q := Ezpow K l e (-(2 * H : ℤ)) • (((l : K) ^ (3 * H))⁻¹ • F0) with hQ_def
  set X0 := Ezpow K l e (-(2 * H : ℤ)) • P0 with hX0_def
  have hsplit : (l : K) ^ c₁ • w = X0 + Q := by
    have h : (l : K) ^ c₁ • w = Ezpow K l e (-(2 * H : ℤ)) • (E K l e ^ (2 * H) • ((l : K) ^ c₁ • w)) := by
      rw [smul_smul, mul_comm, hE1, one_smul]
    rw [h, smul_comm (E K l e ^ (2 * H)) ((l : K) ^ c₁) w, hdec, smul_add]
  have hQ : Q ∈ D.Man := by
    rw [hQ_def, smul_comm]
    exact D.Man.smul_mem _ hQF
  have hX0 : X0 ∈ D.Man := by
    have : X0 = (l : K) ^ c₁ • w - Q := by rw [hsplit, add_sub_cancel_right]
    rw [this]
    exact D.Man.sub_mem (D.Man.smul_mem _ hw) hQ
  have hX0E : X0 ∈ D.EM (2 * H + η) := by
    rw [mem_divE, hX0_def, smul_smul, pow_add, mul_right_comm, hE1, one_mul]
    exact D.upper _ hP0
  have hX0M : X0 ∈ D.M := PhiMod.mem_M_of_mem_Man _ hX0E hX0
  have hφX0 : D.phi X0 ∈ D.MM := PhiMod.ext_mono _ (A_le_S l e) (D.phi_mem_L hX0M)
  obtain ⟨v', hv', hv'eq⟩ := GlobalTheory.T.prime_pow_smul_phi_mem_lattice_of_mem_filtration O K l e a ι η H D (10 * H) (by omega) F0 hF0
  have hl0 : (l : K) ≠ 0 := l_ne_zero (K := K) l
  have hF : D.phi F0 = (l : K) ^ (3 * H) • ((l : K) ^ (2 * H) • ((l : K) ^ (5 * H - η) • v')) := by
    apply smul_right_injective _ (pow_ne_zero η hl0)
    rw [show 10 * H = η + (3 * H + (2 * H + (5 * H - η))) by have := hA.lt; omega] at hv'eq
    simpa only [pow_add, mul_smul] using hv'eq
  have hfr : (l : K⟦X⟧) ^ (2 * H) * frob K l (Ezpow K l e (-(2 * H : ℤ))) = c ^ (2 * H) := by
    rw [← hcE, mul_pow, ← map_pow, mul_assoc, ← map_mul, hE1, map_one, mul_one]
  have hcast : ∀ (n : ℕ) (x : Vec K a ι), (l : K) ^ n • x = (l : K⟦X⟧) ^ n • x := by
    intro n x
    rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  have hφQ' : D.phi Q = c ^ (2 * H) • ((l : K) ^ (5 * H - η) • v') := by
    rw [hQ_def, PhiMod.phi_smul, map_smul, hF, inv_smul_smul₀ (pow_ne_zero _ hl0), hcast (2 * H), smul_smul, mul_comm (frob K l _), hfr]
  have hφQ : D.phi Q ∈ D.MM := by
    rw [hφQ']
    refine D.MM.smul_mem ⟨c ^ (2 * H), pow_mem hc _⟩ ?_
    rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hv' _
  have key : (l : K) ^ c₁ • D.zeta y = c • (D.phi X0 + D.phi Q) := by
    rw [← map_add (f := _), ← hsplit, map_smul, hζ, smul_comm]
  rw [key]
  exact D.MM.smul_mem ⟨c, hc⟩ (add_mem hφX0 hφQ)

end GlobalTheory.ZetaDenominator
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZetaMemPowInvPhiModuleLatticeStatement
open PowerSeries GlobalTheory.BK
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zeta_mem_pow_inv_phiModule_lattice : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.ZetaBound := by
  first | exact @GlobalTheory.ZetaDenominator.zetaBound | exact GlobalTheory.ZetaDenominator.zetaBound | (intros; apply GlobalTheory.ZetaDenominator.zetaBound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftSurjectionGoodCrystallineLattices
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.TheoremT


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem liftF_of_isGood : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Numerics l e N η H Sig U → ∀ (T₁ T₂ : QLat LL) (g : LatHom T₁.L T₂.L), g.Onto → IsGood a ϖ Pl T₁ Sig U → IsGood a ϖ Pl T₂ Sig U → g.LiftF (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (7 * (N * maxPeriod l Sig + η * (N + maxPeriod l Sig))) := by
  intro hBS hFon l _ a e _ _ ϖ LL _ _ Pl AI hStd N η H Sig U hNum T₁ T₂ g hg hG₁ hG₂
  have hN2 := hNum.two_le
  have hlarge := hNum.large
  have hHN : 4 * H ≤ H * N ^ 2 := by
    have h4 : 4 ≤ N ^ 2 := by nlinarith
    calc 4 * H = H * 4 := by ring
      _ ≤ H * N ^ 2 := Nat.mul_le_mul_left H h4
  have hl2 : l ≠ 2 := by intro h; subst h; nlinarith
  have h8 : 8 * H + 1 < l := by nlinarith
  obtain ⟨T₀, f, hSES, hG₀⟩ := GlobalTheory.T.isGoodLattice_kernel_of_surjection_goodLattice hFon l a e ϖ LL Pl AI hStd Sig U T₁ T₂ g hg hG₁
  obtain ⟨P₀, -⟩ := GlobalTheory.T.exists_breuilKisinModule_tameDescent_goodLattice hBS hFon l a e ϖ LL hl2 Pl AI hStd η H Sig U hNum.range_U T₀ hG₀
  obtain ⟨P₁, hP₁⟩ := GlobalTheory.T.exists_breuilKisinModule_tameDescent_goodLattice hBS hFon l a e ϖ LL hl2 Pl AI hStd η H Sig U hNum.range_U T₁ hG₁
  obtain ⟨P₂, hP₂⟩ := GlobalTheory.T.exists_breuilKisinModule_tameDescent_goodLattice hBS hFon l a e ϖ LL hl2 Pl AI hStd η H Sig U hNum.range_U T₂ hG₂
  obtain ⟨F, hF⟩ := GlobalTheory.T.latticeHom_lifts_breuilKisinDescentHom hBS l a e ϖ LL η H T₀ T₁ P₀ P₁ f
  obtain ⟨G, hG⟩ := GlobalTheory.T.latticeHom_lifts_breuilKisinDescentHom hBS l a e ϖ LL η H T₁ T₂ P₁ P₂ g
  have hEx := GlobalTheory.T.isExactTriple_breuilKisin_of_shortExactLattices l a e ϖ LL (Fin P₀.n) (Fin P₁.n) (Fin P₂.n) P₀.D.toPhiMod P₁.D.toPhiMod
    P₂.D.toPhiMod T₀ T₁ T₂ P₀.R.I P₁.R.I P₂.R.I f g F.toHom G.toHom hSES hF hG
  have hAdm : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.Admissible l e N η H Sig U :=
    ⟨hNum.frob_mem, hNum.zero_mem_Sig, hNum.card_Sig, hNum.two_le, hNum.range_U, hNum.zero_mem_U,
      hNum.card_U, hNum.one_le, hNum.lt, hNum.large⟩
  have hpot₂ := GlobalTheory.T.exists_frobeniusPotential_cocycle_class l a e _ _ (thetaW a LL) ϖ (Fin P₂.n) η H P₂.D T₂ P₂.R
  unfold LatHom.LiftF
  intro c hc

  obtain ⟨y₂, hy₂, hMon₂, hCl₂⟩ :=
    GlobalTheory.T.crystalline_class_from_monodromy_kernel_element hBS hFon l a e ϖ LL Pl AI hStd N η H Sig U hNum T₂ hG₂ P₂ c hc

  obtain ⟨y₂', hy₂', m₂, hm₂, hsum⟩ :=
    Submodule.mem_sup.1 ((GlobalTheory.T.prime_pow_divisibility_of_descentDatum _ _ l e a _ η H P₂.D).2 y₂ hy₂)
  have hrew : y₂' + P₂.D.phi m₂ = (l : ↥LL.1) ^ η • y₂ + (P₂.D.phi m₂ - m₂) := by
    rw [← hsum]; abel
  have hMon₂' : P₂.D.Mon (y₂' + P₂.D.phi m₂) = 0 := by
    rw [hrew, P₂.D.Mon_add_phi_sub _ (PhiMod.M_le_Man _ hm₂.1), LinearMap.map_smul, hMon₂, smul_zero]
  have hCl₂' : P₂.R.ClassOf (y₂' + P₂.D.phi m₂)
      ((l : ↥LL.1) ^ η • (l : ↥LL.1) ^ GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N (maxPeriod l Sig) • c) := by
    rw [hrew]
    exact hpot₂.2.2.2 _ _ m₂ hm₂ (hpot₂.2.2.1 _ _ η hCl₂)

  obtain ⟨y', hy', m, hm, hMon, hGy⟩ :=
    GlobalTheory.T.liftingTheorem_phiModules_exact_triple _ _ l e a _ _ _ η H P₀.D P₁.D P₂.D F G N Sig U
      ⟨hEx, hNum, hP₁, hP₂.chars_subset⟩ y₂' hy₂' m₂ hm₂ hMon₂'

  have hζ := GlobalTheory.T.zeta_mem_pow_inv_phiModule_lattice _ _ l e a _ N η H Sig U hAdm P₁.D hP₁ y' hy' m hm hMon
  obtain ⟨κ₁, hκ₁, hCl₁⟩ := GlobalTheory.T.galoisClass_of_monodromy_eq_zero hFon l a e ϖ LL (Fin P₁.n) η H P₁.D T₁ P₁.R Pl AI hStd hNum.lt h8
    _ (GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.add_phi_mem_Y hy' hm) hMon _ hζ

  have hnat := GlobalTheory.T.tame_breuil_kisin_datum_exists l a e _ _ (thetaW a LL) ϖ (Fin P₁.n) (Fin P₂.n) η H P₁.D P₂.D T₁ T₂ P₁.R P₂.R g G hG
    _ _ hCl₁
  have happ : G.app ((l : ↥LL.1) ^ GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig • (y' + P₁.D.phi m)) =
      (l : ↥LL.1) ^ (GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp N η (maxPeriod l Sig)) •
        (y₂' + P₂.D.phi m₂) := by
    have happ0 : ∀ (k : ↥LL.1) (v : Vec (↥LL.1) a (Fin P₁.n)), G.app (k • v) = k • G.app v := by
      intro k v
      ext1 τ
      simp only [Hom.app_apply, Pi.smul_apply, Matrix.mulVec_smul]
    rw [happ0, hGy, smul_smul, ← pow_add]
  rw [happ] at hnat
  have hCl := hpot₂.2.2.1 _ _ (GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp N η (maxPeriod l Sig)) hCl₂'
  rw [smul_smul, smul_smul, ← pow_add, ← pow_add] at hCl
  have hB := hpot₂.2.1 _ _ _ hnat hCl

  have hexp : GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp N η (maxPeriod l Sig) + η +
      GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N (maxPeriod l Sig) ≤ 7 * (N * maxPeriod l Sig + η * (N + maxPeriod l Sig)) := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.c₂, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.c₁,
      GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eL, GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW]
    obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by omega⟩
    generalize maxPeriod l Sig = r
    have h1 : n + 2 - 1 = n + 1 := by omega
    rw [h1]
    nlinarith [Nat.zero_le (n * r), Nat.zero_le (η * n), Nat.zero_le (η * r)]
  rw [← algebraMap_smul (↥LL.1), map_pow, map_natCast, Pl.PD_p,
    ← Nat.sub_add_cancel hexp, pow_add, mul_smul]
  obtain ⟨β, hβ, hβeq⟩ : ∃ β ∈ latticeCoboundaries T₂.L, (l : ↥LL.1) ^ (GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleSignatures.cOne l η Sig + GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.kExp N η (maxPeriod l Sig) + η +
      GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.eW N (maxPeriod l Sig)) • c = LatHom.post g κ₁ - β := ⟨_, hB, by abel⟩
  rw [hβeq, smul_sub]
  refine sub_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)
  · rw [← map_natCast (algebraMap ↥(OL LL) ↥LL.1) l, ← map_pow, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem hκ₁)
  · rw [← map_natCast (algebraMap ↥(OL LL) ↥LL.1) l, ← map_pow, algebraMap_smul]
    exact Submodule.smul_mem _ _ hβ

end GlobalTheory.TheoremT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftSurjectionGoodCrystallineLatticesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_surjection_good_crystalline_lattices : GlobalTheory.Published.BhattScholzeCrystallineLattices → GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (Pl : LocPrime l) (AI : LocAinf l Pl), IsStd Pl AI → ∀ (N η H : ℕ) (Sig : Finset (ZMod e)) (U : Finset ℤ), GlobalTheory.IndefiniteRowSideFullHecke.ConductorExponents.Numerics l e N η H Sig U → ∀ (T₁ T₂ : QLat LL) (g : LatHom T₁.L T₂.L), g.Onto → IsGood a ϖ Pl T₁ Sig U → IsGood a ϖ Pl T₂ Sig U → g.LiftF (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) (7 * (N * maxPeriod l Sig + η * (N + maxPeriod l Sig))) := by
  first | exact @GlobalTheory.TheoremT.liftF_of_isGood | exact GlobalTheory.TheoremT.liftF_of_isGood | (intros; apply GlobalTheory.TheoremT.liftF_of_isGood <;> assumption)
end
