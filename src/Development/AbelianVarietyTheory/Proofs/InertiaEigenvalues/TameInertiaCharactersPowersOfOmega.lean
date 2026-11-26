module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDecompositionBaseChange

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisFixingMaxUnramifiedMapConj
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisFixingMaxUnramifiedMapConj
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.LiftKur

theorem exists_gal_fix_Kur_map : ∀ (l : ℕ) [Fact l.Prime] (x y : Om l), Polynomial.aeval y (minpoly ↥(MaximalUnramifiedExtension l) x) = 0 → ∃ g : GQ l, (∀ z ∈ MaximalUnramifiedExtension l, g z = z) ∧ g x = y := by
  intro l _ x y hy
  haveI : Algebra.IsAlgebraic ↥(MaximalUnramifiedExtension l) (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) ↥(MaximalUnramifiedExtension l)
  haveI : IsAlgClosure ↥(MaximalUnramifiedExtension l) (Om l) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ↥(MaximalUnramifiedExtension l) (Om l) := IsAlgClosure.normal _ _
  have hx : IsIntegral ↥(MaximalUnramifiedExtension l) x := Algebra.IsIntegral.isIntegral x
  have hmin : minpoly ↥(MaximalUnramifiedExtension l) x = minpoly ↥(MaximalUnramifiedExtension l) y :=
    (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx) hy (minpoly.monic hx))
  obtain ⟨τ, hτ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ↥(MaximalUnramifiedExtension l)) (E := Om l) (x := y) (y := x)).1 hmin.symm
  refine ⟨τ.restrictScalars ℚ_[l], ?_, ?_⟩
  · intro z hz
    show τ z = z
    exact τ.commutes ⟨z, hz⟩
  · show τ x = y
    exact hτ

end GlobalTheory.LiftKur
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisFixingMaxUnramifiedMapConjStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galois_fixing_maxUnramified_map_conj : ∀ (l : ℕ) [Fact l.Prime] (x y : Om l), Polynomial.aeval y (minpoly ↥(MaximalUnramifiedExtension l) x) = 0 → ∃ g : GQ l, (∀ z ∈ MaximalUnramifiedExtension l, g z = z) ∧ g x = y := by
  first | exact @GlobalTheory.LiftKur.exists_gal_fix_Kur_map | exact GlobalTheory.LiftKur.exists_gal_fix_Kur_map | (intros; apply GlobalTheory.LiftKur.exists_gal_fix_Kur_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowFixingNormalOfNear
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowFixingNormalOfNear
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.PowFixNear
open GlobalTheory.MemLoc GlobalTheory.MemLoc.FrobLaws

theorem main : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), Normal ℚ_[l] ↥F.1 → ∀ g : GQ l, (∀ x ∈ F.1, x ≠ 0 → ‖g x - x‖ < ‖x‖) → ∃ s : ℕ, ∀ x ∈ F.1, (g ^ l ^ s) x = x := by
  intro l _ F hF g hg
  haveI := F.2
  haveI : Normal ℚ_[l] ↥F.1 := hF
  have hpow : ∀ (i : ℕ) (x : Om l), x ∈ F.1 → x ≠ 0 → ‖(g ^ i) x - x‖ < ‖x‖ := by
    intro i x hx hx0
    induction i with
    | zero => simpa using hx0
    | succ i ih =>
      have e : (g ^ (i + 1)) x - x = (g ^ i) (g x - x) + ((g ^ i) x - x) := by
        rw [pow_succ, AlgEquiv.mul_apply, map_sub (g ^ i)]; ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ih)
      rw [norm_gal]; exact hg x hx hx0
  have hst : ∀ (h : GQ l) (x : Om l), x ∈ F.1 → h x ∈ F.1 := by
    intro h x hx
    have e := AlgEquiv.restrictNormal_commutes h (↥F.1) ⟨x, hx⟩
    have e' : h x = (algebraMap (↥F.1) (Om l)) ((AlgEquiv.restrictNormal h (↥F.1)) ⟨x, hx⟩) := e.symm
    rw [e']
    exact ((AlgEquiv.restrictNormal h (↥F.1)) ⟨x, hx⟩).2
  set r := AlgEquiv.restrictNormalHom (F := ℚ_[l]) (K₁ := Om l) (↥F.1) with hr
  have hfin : IsOfFinOrder (r g) := isOfFinOrder_of_finite _
  set N := orderOf (r g) with hNdef
  have hN0 : N ≠ 0 := (hfin.orderOf_pos).ne'
  have hgN : ∀ x ∈ F.1, (g ^ N) x = x := by
    intro x hx
    have e := AlgEquiv.restrictNormal_commutes (g ^ N) (↥F.1) ⟨x, hx⟩
    have h1 : AlgEquiv.restrictNormal (g ^ N) (↥F.1) = 1 := by
      have := pow_orderOf_eq_one (r g)
      rw [← map_pow] at this
      exact this
    rw [h1] at e
    simpa using e.symm
  obtain ⟨s, N', hN', hNe⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN0 l (Fact.out : l.Prime).ne_one
  refine ⟨s, fun y hy => ?_⟩
  refine GlobalTheory.TameInertiaCyclic.fix_of_near F (g ^ l ^ s) (hst _) (fun x hx hx0 => hpow _ x hx hx0) hN' (fun x hx => ?_) y hy
  rw [← pow_mul, ← hNe]
  exact hgN x hx

end GlobalTheory.PowFixNear
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowFixingNormalOfNearStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_pow_fixing_normal_of_near : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), Normal ℚ_[l] ↥F.1 → ∀ g : GQ l, (∀ x ∈ F.1, x ≠ 0 → ‖g x - x‖ < ‖x‖) → ∃ s : ℕ, ∀ x ∈ F.1, (g ^ l ^ s) x = x := by
  first | exact @GlobalTheory.PowFixNear.main | exact GlobalTheory.PowFixNear.main | (intros; apply GlobalTheory.PowFixNear.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaFixingKummerRootMovesLess
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaFixingKummerRootMovesLess
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.TameInertiaCyclic GlobalTheory.MemLoc.FrobLaws

noncomputable section
namespace GlobalTheory.NearRoot

variable {l : ℕ} [hl : Fact l.Prime]

theorem ratio_one (g : GQ l) : GlobalTheory.TameInertiaCyclic.ratio g 1 = 1 :=
  Subtype.ext (by show g 1 / 1 = 1; simp)

theorem ratio_pow (g : GQ l) (x : Om l) (n : ℕ) :
    GlobalTheory.TameInertiaCyclic.ratio g (x ^ n) = GlobalTheory.TameInertiaCyclic.ratio g x ^ n := by
  induction n with
  | zero => simpa using ratio_one g
  | succ n ih => rw [pow_succ, GlobalTheory.TameInertiaCyclic.ratio_mul, ih, pow_succ]

theorem norm_natCast_lt_one : ‖(l : Om l)‖ < 1 := by
  have h : ‖((l : ℚ_[l]) : Om l)‖ < 1 := by
    rw [PadicAlgCl.norm_extends]; exact Padic.norm_p_lt_one
  simpa using h

theorem natCast_ne_zero : (l : Om l) ≠ 0 := by
  have h : ((l : ℚ_[l]) : Om l) ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap ℚ_[l] (Om l)).injective]
    exact_mod_cast hl.out.ne_zero
  simpa using h

theorem exists_unif (F : FinExt l) :
    ∃ ϖ ∈ F.1, ϖ ≠ 0 ∧ (∀ x ∈ F.1, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖ϖ ^ k‖) ∧
      ∃ E : ℕ, 0 < E ∧ ‖ϖ‖ ^ E = ‖(l : Om l)‖ := by
  obtain ⟨π, hπ, hπ0, hgen⟩ := GlobalTheory.TameInertiaCyclic.exists_gen F
  have hlF : (l : Om l) ∈ F.1 := natCast_mem _ l
  obtain ⟨k0, hk0⟩ := hgen _ hlF natCast_ne_zero
  have hk0' : k0 ≠ 0 := by
    rintro rfl
    have := norm_natCast_lt_one (l := l)
    rw [hk0] at this
    simp at this
  rcases lt_or_gt_of_ne hk0' with hneg | hpos
  · refine ⟨π⁻¹, inv_mem hπ, inv_ne_zero hπ0, fun x hx hx0 => ?_, (-k0).toNat, by omega, ?_⟩
    · obtain ⟨k, hk⟩ := hgen x hx hx0
      exact ⟨-k, by rw [hk, _root_.inv_zpow', neg_neg]⟩
    · rw [hk0, ← norm_pow, ← zpow_natCast, Int.toNat_of_nonneg (by omega), _root_.inv_zpow', neg_neg]
  · refine ⟨π, hπ, hπ0, hgen, k0.toNat, by omega, ?_⟩
    rw [hk0, ← norm_pow, ← zpow_natCast, Int.toNat_of_nonneg (by omega)]

theorem near_root : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), ∃ M : ℕ, 0 < M ∧ ¬ l ∣ M ∧ ∀ ρ : Om l, ρ ^ M = -(l : Om l) → ∀ g : GQ l, (∀ y : Om l, ‖y‖ ≤ 1 → ‖g y - y‖ < 1) → g ρ = ρ → ∀ x ∈ F.1, x ≠ 0 → ‖g x - x‖ < ‖x‖ := by
  intro l _ F
  obtain ⟨ϖ, hϖ, hϖ0, hgen, E, hE, hEn⟩ := exists_unif F
  obtain ⟨s, M, hlM, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hE.ne' l (Fact.out : l.Prime).ne_one
  have hM : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; simp at hlM)
  refine ⟨M, hM, hlM, fun ρ hρ g hg hgρ x hx hx0 => ?_⟩
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne', eq_comm, neg_eq_zero] at hρ
    exact natCast_ne_zero hρ
  have hq0 : ϖ ^ (l ^ s) ≠ 0 := pow_ne_zero _ hϖ0
  have hnq : ‖ϖ ^ (l ^ s)‖ = ‖ρ‖ := by
    refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hM.ne').1 ?_
    rw [← norm_pow, ← pow_mul, norm_pow, hEn, ← norm_pow, hρ, norm_neg]
  set u := ϖ ^ (l ^ s) / ρ with hu
  have hu0 : u ≠ 0 := div_ne_zero hq0 hρ0
  have hnu : ‖u‖ = 1 := by rw [hu, norm_div, hnq, div_self (norm_ne_zero_iff.2 hρ0)]
  have h1 : res (GlobalTheory.TameInertiaCyclic.ratio g u) = 1 := by
    rw [GlobalTheory.TameInertiaCyclic.res_ratio_iff g hu0, hnu]; exact hg u hnu.le
  have h2 : res (GlobalTheory.TameInertiaCyclic.ratio g ρ) = 1 := by
    rw [GlobalTheory.TameInertiaCyclic.res_ratio_iff g hρ0, hgρ, sub_self, norm_zero]
    exact norm_pos_iff.2 hρ0
  have h3 : res (GlobalTheory.TameInertiaCyclic.ratio g ϖ) ^ (l ^ s) = 1 := by
    rw [← map_pow, ← ratio_pow, ← div_mul_cancel₀ (ϖ ^ (l ^ s)) hρ0, ← hu,
      GlobalTheory.TameInertiaCyclic.ratio_mul, map_mul, h1, h2, one_mul]
  have h4 : res (GlobalTheory.TameInertiaCyclic.ratio g ϖ) = 1 := by
    have h5 : (res (GlobalTheory.TameInertiaCyclic.ratio g ϖ) - 1) ^ (l ^ s) = 0 := by
      rw [sub_pow_char_pow, h3, one_pow, sub_self]
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : l.Prime).ne_zero) |>.1 h5)
  obtain ⟨k, hk⟩ := hgen x hx hx0
  have hp : ϖ ^ k ≠ 0 := zpow_ne_zero k hϖ0
  have hv : ‖x / ϖ ^ k‖ = 1 := by rw [norm_div, hk, div_self (norm_ne_zero_iff.2 hp)]
  have h6 : res (GlobalTheory.TameInertiaCyclic.ratio g (x / ϖ ^ k)) = 1 := by
    rw [GlobalTheory.TameInertiaCyclic.res_ratio_iff _ (div_ne_zero hx0 hp), hv]
    exact hg _ hv.le
  rw [← GlobalTheory.TameInertiaCyclic.res_ratio_iff _ hx0, ← div_mul_cancel₀ x hp,
    GlobalTheory.TameInertiaCyclic.ratio_mul, map_mul, h6,
    GlobalTheory.TameInertiaCyclic.res_ratio_zpow _ hϖ0 h4, one_mul]

end GlobalTheory.NearRoot
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaFixingKummerRootMovesLessStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_fixing_kummer_root_moves_less : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), ∃ M : ℕ, 0 < M ∧ ¬ l ∣ M ∧ ∀ ρ : Om l, ρ ^ M = -(l : Om l) → ∀ g : GQ l, (∀ y : Om l, ‖y‖ ≤ 1 → ‖g y - y‖ < 1) → g ρ = ρ → ∀ x ∈ F.1, x ≠ 0 → ‖g x - x‖ < ‖x‖ := by
  first | exact @GlobalTheory.NearRoot.near_root | exact GlobalTheory.NearRoot.near_root | (intros; apply GlobalTheory.NearRoot.near_root <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCharOpenKerTrivialFixingNormal
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCharOpenKerTrivialFixingNormal
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.InertiaEigenvalues

theorem char_inertia_trivial_on_fixing_normal : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l)
    (χ : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) →* (↥LL.1)ˣ), IsOpen (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) →
    ∃ F : FinExt l, Normal ℚ_[l] ↥F.1 ∧ ∀ g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)),
      (∀ x ∈ F.1, ((g : Gl l) : GQ l) x = x) → χ g = 1 := by
  intro l _ LL χ hopen
  obtain ⟨t₁, ht₁, ht₁e⟩ := isOpen_induced_iff.mp hopen
  obtain ⟨t₂, ht₂, ht₂e⟩ := isOpen_induced_iff.mp ht₁
  have h1 : (1 : GQ l) ∈ t₂ := by
    have hk : (1 : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) ∈ (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) := χ.ker.one_mem
    rw [← ht₁e] at hk
    have hk' : ((1 : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) : Gl l) ∈ t₁ := hk
    rw [← ht₂e] at hk'
    exact hk'
  obtain ⟨E, hfd, hN, hE⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal ℚ_[l] (Om l) t₂).1 (ht₂.mem_nhds h1)
  refine ⟨⟨E, hfd⟩, hN, fun g hg => ?_⟩
  have hg₂ : ((g : Gl l) : GQ l) ∈ t₂ :=
    hE ((IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => hg x hx)
  have hg₁ : (g : Gl l) ∈ t₁ := by
    rw [← ht₂e]; exact hg₂
  have hg₀ : g ∈ (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) := by
    rw [← ht₁e]; exact hg₁
  exact hg₀

end GlobalTheory.InertiaEigenvalues
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCharOpenKerTrivialFixingNormalStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_char_openKer_trivial_fixing_normal : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (χ : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) →* (↥LL.1)ˣ), IsOpen (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) → ∃ F : FinExt l, Normal ℚ_[l] ↥F.1 ∧ ∀ g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)), (∀ x ∈ F.1, ((g : Gl l) : GQ l) x = x) → χ g = 1 := by
  first | exact @GlobalTheory.InertiaEigenvalues.char_inertia_trivial_on_fixing_normal | exact GlobalTheory.InertiaEigenvalues.char_inertia_trivial_on_fixing_normal | (intros; apply GlobalTheory.InertiaEigenvalues.char_inertia_trivial_on_fixing_normal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemInertiaQlIffResidueTrivial
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemInertiaQlIffResidueTrivial
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.IKRes

theorem norm_gal_ql {l : ℕ} [Fact l.Prime] (g : GQ l) (x : Om l) : ‖g x‖ = ‖x‖ :=
  (spectralNorm_eq_of_equiv g x).symm

theorem mem_IK_ql_iff : ∀ (l : ℕ) [Fact l.Prime] (g : Gl l), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) ↔ ∀ x : Om l, ‖x‖ ≤ 1 → ‖(g : GQ l) x - x‖ < 1 := by
  intro l _ g
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem σ hσ => exact hσ
    | one => intro x _; simp
    | mul σ τ _ _ hσ hτ =>
      intro x hx
      have h1 : ‖(σ : GQ l) ((τ : GQ l) x) - (τ : GQ l) x‖ < 1 :=
        hσ _ (by rwa [norm_gal_ql])
      have h2 := hτ x hx
      have he : ((σ * τ : Gl l) : GQ l) x - x =
          ((σ : GQ l) ((τ : GQ l) x) - (τ : GQ l) x) + ((τ : GQ l) x - x) := by
        rw [Subgroup.coe_mul, AlgEquiv.mul_apply]; abel
      rw [he]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 h2)
    | inv σ _ hσ =>
      intro x hx
      have hy : ‖((σ : GQ l)⁻¹) x‖ ≤ 1 := by rwa [norm_gal_ql]
      have h := hσ _ hy
      have hx' : (σ : GQ l) (((σ : GQ l)⁻¹) x) = x := by
        rw [← AlgEquiv.mul_apply, mul_inv_cancel, AlgEquiv.one_apply]
      rw [hx', norm_sub_rev] at h
      simpa [Subgroup.coe_inv] using h
  · intro h
    exact Subgroup.subset_closure h

end GlobalTheory.IKRes
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemInertiaQlIffResidueTrivialStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_inertia_Ql_iff_residue_trivial : ∀ (l : ℕ) [Fact l.Prime] (g : Gl l), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) ↔ ∀ x : Om l, ‖x‖ ≤ 1 → ‖(g : GQ l) x - x‖ < 1 := by
  first | exact @GlobalTheory.IKRes.mem_IK_ql_iff | exact GlobalTheory.IKRes.mem_IK_ql_iff | (intros; apply GlobalTheory.IKRes.mem_IK_ql_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalRootOfUnityMulKummerRootMinpoly
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalRootOfUnityMulKummerRootMinpoly
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.MinpolyKummerUr

open Polynomial

theorem minpoly_eq {l : ℕ} [Fact l.Prime] {M : ℕ} (hM : 0 < M) {ρ : Om l}
    (hρ : ρ ^ M = -(l : Om l)) :
    minpoly (↥(MaximalUnramifiedExtension l)) ρ = Polynomial.X ^ M + Polynomial.C ((l : ℕ) : ↥(MaximalUnramifiedExtension l)) := by
  set F := MaximalUnramifiedExtension l
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hQ : (Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)).Monic := by
    apply Polynomial.monic_X_pow_add_C _ hM.ne'
  have hQdeg : (Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)).natDegree = M := by
    rw [Polynomial.natDegree_X_pow_add_C]
  have haeval : Polynomial.aeval ρ (Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)) = 0 := by
    simp [hρ]
  have hint : IsIntegral F ρ := by
    refine ⟨_, hQ, ?_⟩
    rwa [← Polynomial.aeval_def]
  have hdvd : minpoly F ρ ∣ Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F) := minpoly.dvd _ _ haeval
  have hmon := minpoly.monic hint
  have hpos : 0 < (minpoly F ρ).natDegree := minpoly.natDegree_pos hint
  have hle : (minpoly F ρ).natDegree ≤ M := by
    rw [← hQdeg]
    exact Polynomial.natDegree_le_of_dvd hdvd hQ.ne_zero

  have hnρ : ‖ρ‖ ^ M = (l : ℝ)⁻¹ := by
    rw [← norm_pow, hρ, norm_neg, Formalism.MainNotions.N.PreambleDegrees.Loc.norm_l]
  set P := (minpoly F ρ).map (algebraMap F (Om l)) with hP
  have hsp : P.Splits := IsAlgClosed.splits P
  have hPm : P.Monic := hmon.map _
  have hroots : ∀ a ∈ P.roots, ‖0 - a‖ = ‖ρ‖ := by
    intro a ha
    have h1 : P ∣ (Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)).map (algebraMap F (Om l)) := Polynomial.map_dvd _ hdvd
    have h2 : ((Polynomial.X ^ M + Polynomial.C ((l : ℕ) : F)).map (algebraMap F (Om l))).IsRoot a :=
      (Polynomial.isRoot_of_mem_roots ha).dvd h1
    have h3 : a ^ M = -(l : Om l) := by
      simp [Polynomial.IsRoot] at h2
      linear_combination h2
    have h4 : ‖a‖ ^ M = ‖ρ‖ ^ M := by
      rw [← norm_pow, ← norm_pow, h3, hρ]
    rw [zero_sub, norm_neg]
    exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hM.ne').1 h4
  have heval : ‖P.eval 0‖ = ‖ρ‖ ^ (minpoly F ρ).natDegree := by
    rw [hsp.eval_eq_prod_roots_of_monic hPm, ← Polynomial.natDegree_map (algebraMap F (Om l)), ← hP,
      hsp.natDegree_eq_card_roots]
    have h3 := map_multiset_prod (normHom : Om l →*₀ ℝ) (P.roots.map (fun a => 0 - a))
    have h4 : ‖(P.roots.map (fun a => 0 - a)).prod‖
        = ((P.roots.map (fun a => 0 - a)).map (normHom : Om l →*₀ ℝ)).prod := h3
    have h5 : Multiset.map ((normHom : Om l →*₀ ℝ) ∘ fun a => 0 - a) P.roots
        = Multiset.map (fun _ => ‖ρ‖) P.roots :=
      Multiset.map_congr rfl (fun a ha => by simpa using hroots a ha)
    rw [h4, Multiset.map_map, h5, Multiset.map_const', Multiset.prod_replicate]
  have hy : P.eval 0 = (((minpoly F ρ).eval 0 : F) : Om l) := by
    rw [hP, Polynomial.eval_map, Polynomial.eval₂_at_zero, Polynomial.coeff_zero_eq_eval_zero]
    rfl
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hρ
    have : ((l : ℕ) : Om l) ≠ 0 := by
      intro h
      have := Formalism.MainNotions.N.PreambleDegrees.Loc.norm_l (l := l)
      rw [h, norm_zero] at this
      exact (inv_pos.2 hl0).ne this
    exact this (neg_eq_zero.1 hρ.symm)
  have hnρpos : 0 < ‖ρ‖ := norm_pos_iff.2 hρ0
  have hy0 : (((minpoly F ρ).eval 0 : F) : Om l) ≠ 0 := by
    rw [← hy, ← norm_pos_iff, heval]
    exact pow_pos hnρpos _
  obtain ⟨m, hm⟩ := Formalism.MainNotions.N.PreambleDegrees.Loc.norm_Kur_zpow ((minpoly F ρ).eval 0 : F).2 hy0
  rw [← hy, heval] at hm
  have h8 : (l : ℝ) ^ (m * (M : ℤ)) = (l : ℝ) ^ (-((minpoly F ρ).natDegree : ℤ)) := by
    rw [_root_.zpow_mul, ← hm, zpow_natCast, ← pow_mul, mul_comm, pow_mul, hnρ, _root_.zpow_neg, zpow_natCast, inv_pow]
  have h9 : m * (M : ℤ) = -((minpoly F ρ).natDegree : ℤ) :=
    zpow_right_injective₀ hl0 hl1.ne' h8
  have h10 : (M : ℤ) ∣ ((minpoly F ρ).natDegree : ℤ) := ⟨-m, by linarith⟩
  have hdeg : (minpoly F ρ).natDegree = M :=
    le_antisymm hle (Nat.le_of_dvd hpos (Int.natCast_dvd_natCast.1 h10))
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmon hQ hdvd (by rw [hdeg, hQdeg])).symm

theorem aeval_mul_root (l : ℕ) [Fact l.Prime] (M : ℕ) : 0 < M → ∀ (ρ ξ : Om l),
    ρ ^ M = -(l : Om l) → ξ ^ M = 1 → Polynomial.aeval (ξ * ρ) (minpoly ↥(MaximalUnramifiedExtension l) ρ) = 0 := by
  intro hM ρ ξ hρ hξ
  rw [minpoly_eq hM hρ]
  simp [mul_pow, hξ, hρ]

end GlobalTheory.MinpolyKummerUr
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AevalRootOfUnityMulKummerRootMinpolyStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aeval_rootOfUnity_mul_kummer_root_minpoly : ∀ (l : ℕ) [Fact l.Prime] (M : ℕ), 0 < M → ∀ (ρ ξ : Om l), ρ ^ M = -(l : Om l) → ξ ^ M = 1 → Polynomial.aeval (ξ * ρ) (minpoly ↥(MaximalUnramifiedExtension l) ρ) = 0 := by
  first | exact @GlobalTheory.MinpolyKummerUr.aeval_mul_root | exact GlobalTheory.MinpolyKummerUr.aeval_mul_root | (intros; apply GlobalTheory.MinpolyKummerUr.aeval_mul_root <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaCharactersPowersOfOmega
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.TameIner

theorem mem_IK_iff : ∀ (l : ℕ) [Fact l.Prime] (g : Gl l), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) ↔ ∀ x : Om l, ‖x‖ ≤ 1 → ‖(g : GQ l) x - x‖ < 1 :=
  GlobalTheory.T.mem_inertia_Ql_iff_residue_trivial

theorem minpoly_root : ∀ (l : ℕ) [Fact l.Prime] (M : ℕ), 0 < M → ∀ (ρ ξ : Om l), ρ ^ M = -(l : Om l) → ξ ^ M = 1 → Polynomial.aeval (ξ * ρ) (minpoly ↥(MaximalUnramifiedExtension l) ρ) = 0 :=
  GlobalTheory.T.aeval_rootOfUnity_mul_kummer_root_minpoly

theorem exists_lift : ∀ (l : ℕ) [Fact l.Prime] (x y : Om l), Polynomial.aeval y (minpoly ↥(MaximalUnramifiedExtension l) x) = 0 → ∃ g : GQ l, (∀ z ∈ MaximalUnramifiedExtension l, g z = z) ∧ g x = y :=
  GlobalTheory.T.exists_galois_fixing_maxUnramified_map_conj

theorem exists_open_normal : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l) (χ : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) →* (↥LL.1)ˣ), IsOpen (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) → ∃ F : FinExt l, Normal ℚ_[l] ↥F.1 ∧ ∀ g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)), (∀ x ∈ F.1, ((g : Gl l) : GQ l) x = x) → χ g = 1 :=
  GlobalTheory.T.inertia_char_openKer_trivial_fixing_normal

theorem exists_pow_fix : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), Normal ℚ_[l] ↥F.1 → ∀ g : GQ l, (∀ x ∈ F.1, x ≠ 0 → ‖g x - x‖ < ‖x‖) → ∃ s : ℕ, ∀ x ∈ F.1, (g ^ l ^ s) x = x :=
  GlobalTheory.T.exists_prime_pow_fixing_normal_of_near

theorem near_of_fix_root : ∀ (l : ℕ) [Fact l.Prime] (F : FinExt l), ∃ M : ℕ, 0 < M ∧ ¬ l ∣ M ∧ ∀ ρ : Om l, ρ ^ M = -(l : Om l) → ∀ g : GQ l, (∀ y : Om l, ‖y‖ ≤ 1 → ‖g y - y‖ < 1) → g ρ = ρ → ∀ x ∈ F.1, x ≠ 0 → ‖g x - x‖ < ‖x‖ :=
  GlobalTheory.T.inertia_fixing_kummer_root_moves_less

variable {l : ℕ} [hl : Fact l.Prime]


open GlobalTheory.MemLoc.FrobLaws in
theorem fix_root (g : Gl l) (hg : g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l)) {ζ : Om l} {m : ℕ} (hm : 0 < m)
    (hlm : ¬ l ∣ m) (hζ : ζ ^ m = 1) : (g : GQ l) ζ = ζ := by
  have h1 := (mem_IK_iff l g).1 hg ζ (norm_root hm hζ).le
  have hgζ : ((g : GQ l) ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
  let a : OO l := ⟨(g : GQ l) ζ, show ‖(g : GQ l) ζ‖ ≤ 1 from (norm_root hm hgζ).le⟩
  let b : OO l := ⟨ζ, show ‖ζ‖ ≤ 1 from (norm_root hm hζ).le⟩
  have := res_inj (a := a) (b := b) hm hlm (Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hgζ))
    (Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hζ)) ((res_eq_iff a b).2 h1)
  exact congrArg Subtype.val this


open GlobalTheory.MemLoc.FrobLaws in
theorem frob_root (Fr : Gl l) (hFr : ∀ x : Om l, x ∈ MaximalUnramifiedExtension l → ‖x‖ ≤ 1 → ‖(Fr : GQ l) x - x ^ l‖ < 1)
    {ζ : Om l} {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m) (hζ : ζ ^ m = 1) : (Fr : GQ l) ζ = ζ ^ l := by
  have hK : ζ ∈ MaximalUnramifiedExtension l := IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, hζ⟩
  have h1 := hFr ζ hK (norm_root hm hζ).le
  have hgζ : ((Fr : GQ l) ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
  have hζl : (ζ ^ l) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  let a : OO l := ⟨(Fr : GQ l) ζ, show ‖(Fr : GQ l) ζ‖ ≤ 1 from (norm_root hm hgζ).le⟩
  let b : OO l := ⟨ζ ^ l, show ‖ζ ^ l‖ ≤ 1 from (norm_root hm hζl).le⟩
  have := res_inj (a := a) (b := b) hm hlm (Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hgζ))
    (Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hζl)) ((res_eq_iff a b).2 h1)
  exact congrArg Subtype.val this


open GlobalTheory.MemLoc.FrobLaws in
theorem mem_IK_of_fix_Kur (g : Gl l) (hg : ∀ x ∈ MaximalUnramifiedExtension l, (g : GQ l) x = x) :
    g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
  have key : ∀ y : Om l, ‖y‖ < 1 → ‖(g : GQ l) y - y‖ < 1 := fun y hy => by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · rw [norm_gal]; exact hy
    · rw [norm_neg]; exact hy
  rw [mem_IK_iff]
  intro x hx
  rcases hx.lt_or_eq with h | h
  · exact key x h
  · obtain ⟨ζ, m, hm, hlm, hζ, hn⟩ := exists_root x h
    have e : (g : GQ l) x - x = (g : GQ l) (x - ζ) - (x - ζ) := by
      rw [map_sub, hg ζ (IntermediateField.subset_adjoin _ _ ⟨m, hm, hlm, hζ⟩)]; ring
    rw [e]
    exact key _ hn

theorem exists_inertia {M : ℕ} (hM : 0 < M) (ρ ζ : Om l) (hρ : ρ ^ M = -(l : Om l)) (hζ : ζ ^ M = 1) :
    ∃ g : Gl l, g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) ∧ (g : GQ l) ρ = ζ * ρ := by
  obtain ⟨g, hgK, hgρ⟩ := exists_lift l ρ (ζ * ρ) (minpoly_root l M hM ρ ζ hρ hζ)
  have hmem : g ∈ GK (Formalism.MainNotions.ElementDenominator.qlExt l) := by
    rw [GK, IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change x ∈ (⊥ : IntermediateField ℚ_[l] (Om l)) at hx
    obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.1 hx
    exact g.commutes c
  exact ⟨⟨g, hmem⟩, mem_IK_of_fix_Kur _ hgK, hgρ⟩

theorem chi_trivial (LL : FinExt l) (χ : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) →* (↥LL.1)ˣ)
    (ho : IsOpen (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)))) (hc : Nat.Coprime (orderOf χ) l) :
    ∃ M : ℕ, 0 < M ∧ ¬ l ∣ M ∧ ∀ ρ : Om l, ρ ^ M = -(l : Om l) →
      ∀ g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)), ((g : Gl l) : GQ l) ρ = ρ → χ g = 1 := by
  obtain ⟨F, hFn, hF⟩ := exists_open_normal l LL χ ho
  obtain ⟨M, hM, hlM, hnear⟩ := near_of_fix_root l F
  refine ⟨M, hM, hlM, fun ρ hρ g hg => ?_⟩
  have hres := (mem_IK_iff l (g : Gl l)).1 g.2
  have h1 := hnear ρ hρ _ hres hg
  obtain ⟨s, hs⟩ := exists_pow_fix l F hFn _ h1
  have h2 : χ (g ^ l ^ s) = 1 := hF _ (fun x hx => by simpa using hs x hx)
  have h3 : χ g ^ orderOf χ = 1 := by rw [← MonoidHom.pow_apply, pow_orderOf_eq_one]; rfl
  rw [map_pow] at h2
  have := pow_gcd_eq_one.2 ⟨h3, h2⟩
  rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right s hc), pow_one] at this

end GlobalTheory.TameIner

namespace GlobalTheory.TameIner

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], (∀ g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), ∃ w : ↥LL.1, (w : Om l) * ϖ.seq 0 = (g : GQ l) (ϖ.seq 0) ∧ w ^ e = 1) ∧ (∃ g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), ∃ w : ↥LL.1, (w : Om l) * ϖ.seq 0 = (g : GQ l) (ϖ.seq 0) ∧ IsPrimitiveRoot w e) ∧ ∀ (χ : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) →* (↥LL.1)ˣ), IsOpen (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) → Nat.Coprime (orderOf χ) l → (∀ (Fr : Gl l), (∀ x : Om l, x ∈ MaximalUnramifiedExtension l → ‖x‖ ≤ 1 → ‖(Fr : GQ l) x - x ^ l‖ < 1) → ∀ g h : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)), (g : Gl l) = Fr⁻¹ * h * Fr → χ h = χ g ^ l) ∧ (χ ^ e = 1 → ∃ c : ZMod e, ∀ (g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) (w : ↥LL.1), (w : Om l) * ϖ.seq 0 = ((g : Gl l) : GQ l) (ϖ.seq 0) → (χ g : ↥LL.1) = w ^ c.val) := by
  intro l _ a e _ _ ϖ LL _ _
  have hp : l.Prime := Fact.out
  obtain ⟨z, hz⟩ := TameDescentExponentData.prim (K := ↥LL.1) (l := l) (e := e) (a := a)
  have he0 : 0 < e := Nat.pos_of_ne_zero (NeZero.ne e)
  have hle : ¬ l ∣ e := by
    intro h
    have h1 : l ∣ l ^ a := dvd_pow_self l (NeZero.ne a)
    rw [← TameDescentExponentData.succ_eq (K := ↥LL.1) (l := l) (e := e) (a := a)] at h1
    exact hp.not_dvd_one ((Nat.dvd_add_right h).1 h1)
  have hzO : IsPrimitiveRoot ((z : ↥LL.1) : Om l) e := hz.map_of_injective (f := LL.1.val) LL.1.val.injective
  have hl0 : (l : Om l) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hπ0 : ϖ.seq 0 ≠ 0 := ϖ.seq_ne_zero 0
  have hroot : ∀ w : Om l, w ^ e = 1 → ∃ k < e, ((z ^ k : ↥LL.1) : Om l) = w := by
    intro w hw
    obtain ⟨k, hk, h⟩ := hzO.eq_pow_of_pow_eq_one hw
    exact ⟨k, hk, by rw [← h]; rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g _
    have hw : ((g : GQ l) (ϖ.seq 0) / ϖ.seq 0) ^ e = 1 := by
      rw [div_pow, ← map_pow, ϖ.seq_zero, map_neg, map_natCast, div_self (neg_ne_zero.2 hl0)]
    obtain ⟨k, -, hk⟩ := hroot _ hw
    refine ⟨z ^ k, ?_, ?_⟩
    · rw [hk]; field_simp
    · rw [← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow]
  · obtain ⟨g, hg, hgπ⟩ := exists_inertia he0 (ϖ.seq 0) _ ϖ.seq_zero hzO.pow_eq_one
    exact ⟨g, hg, z, hgπ.symm, hz⟩
  · intro χ hχo hχc
    obtain ⟨M0, hM0, hlM0, hM0χ⟩ := chi_trivial LL χ hχo hχc
    have hM : 0 < M0 * e := Nat.mul_pos hM0 he0
    have hlM : ¬ l ∣ M0 * e := fun h => ((Nat.Prime.dvd_mul hp).1 h).elim hlM0 hle
    haveI : NeZero (M0 * e) := ⟨hM.ne'⟩
    obtain ⟨ρ, hρ⟩ := IsAlgClosed.exists_pow_nat_eq (-(l : Om l)) hM
    obtain ⟨ζ, hζ⟩ : ∃ ζ : Om l, IsPrimitiveRoot ζ (M0 * e) :=
      HasEnoughRootsOfUnity.exists_primitiveRoot (Om l) (M0 * e)
    obtain ⟨σ, hσ, hσρ⟩ := exists_inertia hM ρ ζ hρ hζ.pow_eq_one
    have hρ0 : ρ ≠ 0 := by
      rintro rfl
      rw [zero_pow hM.ne', eq_comm, neg_eq_zero] at hρ
      exact hl0 hρ
    have hζσ : ∀ g : Gl l, g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) → (g : GQ l) ζ = ζ := fun g hg =>
      fix_root g hg hM hlM hζ.pow_eq_one
    have hrat : ∀ g : Gl l, ∃ j : ℕ, (g : GQ l) ρ = ζ ^ j * ρ := by
      intro g
      have h1 : ((g : GQ l) ρ / ρ) ^ (M0 * e) = 1 := by
        rw [div_pow, ← map_pow, hρ, map_neg, map_natCast, div_self (neg_ne_zero.2 hl0)]
      obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one h1
      exact ⟨j, by rw [hj]; field_simp⟩
    have hσpow : ∀ j : ℕ, ((σ ^ j : Gl l) : GQ l) ρ = ζ ^ j * ρ := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ, Subgroup.coe_mul, AlgEquiv.mul_apply, hσρ, map_mul, ih, hζσ _ (Subgroup.pow_mem _ hσ j), pow_succ]
        ring
    set σ' : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) := ⟨σ, hσ⟩ with hσ'
    have hχg : ∀ (g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) (j : ℕ), ((g : Gl l) : GQ l) ρ = ζ ^ j * ρ →
        χ g = χ σ' ^ j := by
      intro g j hj
      have hfix : ((((σ' ^ j)⁻¹ * g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) : Gl l) : GQ l) ρ = ρ := by
        have h2 := hσpow j
        have h3 : ((((σ' ^ j)⁻¹ * g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) : Gl l) : GQ l) =
            ((σ ^ j : Gl l) : GQ l)⁻¹ * ((g : Gl l) : GQ l) := by
          simp [σ']
        rw [h3, AlgEquiv.mul_apply, hj, ← h2]
        exact AlgEquiv.symm_apply_apply _ ρ
      have h1 : χ ((σ' ^ j)⁻¹ * g) = 1 := by
        refine hM0χ (ρ ^ e) (by rw [← pow_mul, mul_comm e M0]; exact hρ) _ ?_
        rw [map_pow, hfix]
      rw [map_mul, map_inv, map_pow, inv_mul_eq_one] at h1
      exact h1.symm
    refine ⟨?_, ?_⟩
    · intro Fr hFr g h hgh
      obtain ⟨j, hj⟩ := hrat g
      obtain ⟨i, hi⟩ := hrat Fr⁻¹
      have hFrζ : (Fr : GQ l) ζ = ζ ^ l := frob_root Fr hFr hM hlM hζ.pow_eq_one
      have hh : (h : Gl l) = Fr * g * Fr⁻¹ := by rw [hgh]; group
      have hFr1 : (Fr : GQ l) (ζ ^ i * ρ) = ρ := by
        rw [← hi]
        show (Fr : GQ l) (((Fr⁻¹ : Gl l) : GQ l) ρ) = ρ
        rw [← AlgEquiv.mul_apply, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, AlgEquiv.one_apply]
      have hhρ : ((h : Gl l) : GQ l) ρ = ζ ^ (j * l) * ρ := by
        rw [hh, Subgroup.coe_mul, Subgroup.coe_mul, AlgEquiv.mul_apply, AlgEquiv.mul_apply, hi, map_mul,
          map_pow, hζσ g g.2, hj]
        have e1 : ζ ^ i * (ζ ^ j * ρ) = ζ ^ j * (ζ ^ i * ρ) := by ring
        rw [e1, map_mul, hFr1, map_pow, hFrζ, ← pow_mul, mul_comm l j]
      rw [hχg h _ hhρ, hχg g j hj, pow_mul]
    · intro hχe
      have h1 : ((χ σ' : (↥LL.1)ˣ) : ↥LL.1) ^ e = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hχe]; rfl
      have hζe : IsPrimitiveRoot (ζ ^ M0) e := hζ.pow hM rfl
      obtain ⟨s, -, hs⟩ := hroot (ζ ^ M0) hζe.pow_eq_one
      have hzs : IsPrimitiveRoot (z ^ s) e := by
        rw [← hs] at hζe
        exact (IsPrimitiveRoot.map_iff_of_injective (f := LL.1.val) LL.1.val.injective).1 hζe
      obtain ⟨c, hc, hcz⟩ := hzs.eq_pow_of_pow_eq_one h1
      refine ⟨(c : ZMod e), fun g w hw => ?_⟩
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt hc]
      obtain ⟨j, hj⟩ := hrat g
      rw [hχg g j hj, Units.val_pow_eq_pow_val, ← hcz]

      have hη : (ϖ.seq 0 / ρ ^ M0) ^ e = 1 := by
        rw [div_pow, ϖ.seq_zero, ← pow_mul, hρ, div_self (neg_ne_zero.2 hl0)]
      have hgη := fix_root (g : Gl l) g.2 he0 hle hη
      have hgπ : ((g : Gl l) : GQ l) (ϖ.seq 0) = (ζ ^ M0) ^ j * ϖ.seq 0 := by
        have e1 : ϖ.seq 0 = (ϖ.seq 0 / ρ ^ M0) * ρ ^ M0 := by field_simp
        rw [e1, map_mul, hgη, map_pow, hj]
        ring
      have hw' : w = (z ^ s) ^ j := by
        apply Subtype.ext
        have e2 : (w : Om l) * ϖ.seq 0 = (ζ ^ M0) ^ j * ϖ.seq 0 := hw.trans hgπ
        rw [mul_left_inj' hπ0, ← hs] at e2
        rw [e2]; rfl
      rw [hw']
      ring

end GlobalTheory.TameIner
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameInertiaCharactersPowersOfOmegaStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tame_inertia_characters_powers_of_omega : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], (∀ g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), ∃ w : ↥LL.1, (w : Om l) * ϖ.seq 0 = (g : GQ l) (ϖ.seq 0) ∧ w ^ e = 1) ∧ (∃ g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l), ∃ w : ↥LL.1, (w : Om l) * ϖ.seq 0 = (g : GQ l) (ϖ.seq 0) ∧ IsPrimitiveRoot w e) ∧ ∀ (χ : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)) →* (↥LL.1)ˣ), IsOpen (χ.ker : Set ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) → Nat.Coprime (orderOf χ) l → (∀ (Fr : Gl l), (∀ x : Om l, x ∈ MaximalUnramifiedExtension l → ‖x‖ ≤ 1 → ‖(Fr : GQ l) x - x ^ l‖ < 1) → ∀ g h : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l)), (g : Gl l) = Fr⁻¹ * h * Fr → χ h = χ g ^ l) ∧ (χ ^ e = 1 → ∃ c : ZMod e, ∀ (g : ↥(IK (Formalism.MainNotions.ElementDenominator.qlExt l))) (w : ↥LL.1), (w : Om l) * ϖ.seq 0 = ((g : Gl l) : GQ l) (ϖ.seq 0) → (χ g : ↥LL.1) = w ^ c.val) := by
  first | exact @GlobalTheory.TameIner.main | exact GlobalTheory.TameIner.main | (intros; apply GlobalTheory.TameIner.main <;> assumption)
end
