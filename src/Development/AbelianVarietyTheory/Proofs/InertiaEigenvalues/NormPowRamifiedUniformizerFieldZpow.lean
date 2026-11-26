module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedKur
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLocB
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReadsAtOfCover
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseCoefJumpProof
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowRamifiedUniformizerFieldZpow
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowRamifiedUniformizerFieldZpow
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.ValGroupKprime

theorem norm_Kunr (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] {c : Om l} (hc : c ∈ Kunr l a) (h0 : c ≠ 0) :
    ∃ m : ℤ, ‖c‖ = (l : ℝ) ^ m := by
  have hK : MaximalUnramifiedExtension l ≤ ReciprocityTheory.ChartRestriction.L1.kurAlg l := by
    refine IntermediateField.adjoin_le_iff.2 fun x ⟨m, hm, hlm, hx⟩ => ?_
    refine ReciprocityTheory.ChartRestriction.L1.mem_kurAlg.2
      (Subfield.le_topologicalClosure _ (Subfield.subset_closure ⟨m, hm, hlm, ?_⟩))
    rw [← map_pow, hx, map_one]
  have h1 := ReciprocityTheory.ChartRestriction.L1.mem_kurAlg.1 (hK (Kunr_le_Kur l a hc))
  obtain ⟨m, hm⟩ := ReciprocityTheory.ChartRestriction.L1.kur_val l h1 ((map_ne_zero _).2 h0)
  exact ⟨m, by rw [← hm]; exact (PadicComplex.norm_extends l c).symm⟩

theorem norm_natCast_l (l : ℕ) [Fact l.Prime] : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
  have := PadicAlgCl.norm_extends l (l : ℚ_[l])
  rw [Padic.norm_p] at this
  simpa using this

theorem norm_pow_field (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e)
    (y : Om l) (hy : y ∈ (ϖ.field a).1) (h0 : y ≠ 0) : ∃ j : ℤ, ‖y‖ ^ e = (l : ℝ) ^ j := by
  set π := ϖ.seq 0 with hπdef
  set E := Kunr l a with hE
  have hπ0 : π ≠ 0 := ϖ.seq_ne_zero 0

  have hy' : y ∈ IntermediateField.adjoin E {π} := by
    have h1 : (ϖ.field a).1 = (IntermediateField.adjoin E {π}).restrictScalars ℚ_[l] := by
      rw [IntermediateField.restrictScalars_adjoin_eq_sup]; rfl
    rw [h1] at hy; exact hy
  have hint : IsAlgebraic E π :=
    (Algebra.IsIntegral.isIntegral (R := ℚ_[l]) π).tower_top.isAlgebraic
  rw [← IntermediateField.mem_toSubalgebra,
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint] at hy'

  let M : Submodule E (Om l) := Submodule.span E (Set.range fun i : Fin e => π ^ (i : ℕ))
  have hlE : (-(l : Om l)) ∈ E := E.neg_mem (IntermediateField.natCast_mem E l)
  have hpow : ∀ n, π ^ n ∈ M := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      by_cases hn : n < e
      · exact Submodule.subset_span ⟨⟨n, hn⟩, rfl⟩
      · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.1 hn)
        have hk : k < e + k := by have := NeZero.pos e; omega
        have h2 : π ^ (e + k) = (⟨-(l : Om l), hlE⟩ : E) • π ^ k := by
          rw [pow_add, ϖ.seq_zero]; rfl
        rw [h2]; exact M.smul_mem _ (ih k hk)
  have hyM : y ∈ M := by
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hy'
    obtain ⟨p, rfl⟩ := hy'
    show Polynomial.aeval π p ∈ M
    rw [Polynomial.aeval_eq_sum_range]
    exact Submodule.sum_mem _ fun i _ => M.smul_mem _ (hpow i)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hyM
  set t : Fin e → Om l := fun i => (c i : Om l) * π ^ (i : ℕ) with ht
  have hyt : y = ∑ i, t i := by rw [← hc]; rfl

  have hnπ : ‖π‖ ^ e = (l : ℝ)⁻¹ := by
    rw [← norm_pow, ϖ.seq_zero, norm_neg, norm_natCast_l]
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < l := by linarith

  have hnt : ∀ i, t i ≠ 0 → ∃ m : ℤ, ‖t i‖ ^ e = (l : ℝ) ^ ((e : ℤ) * m - (i : ℕ)) := by
    intro i hi
    have hci : (c i : Om l) ≠ 0 := fun h => hi (by simp [ht, h])
    obtain ⟨m, hm⟩ := norm_Kunr l a (c i).2 hci
    refine ⟨m, ?_⟩
    rw [ht]; dsimp only
    rw [norm_mul, norm_pow, mul_pow, hm, ← pow_mul, mul_comm (i : ℕ) e, pow_mul, hnπ,
      zpow_sub₀ hl0.ne', inv_pow, ← zpow_natCast, ← _root_.zpow_mul, mul_comm m, zpow_natCast, div_eq_mul_inv]

  have hdist : ∀ i j, t i ≠ 0 → t j ≠ 0 → ‖t i‖ = ‖t j‖ → i = j := by
    intro i j hi hj hij
    obtain ⟨m1, h1⟩ := hnt i hi
    obtain ⟨m2, h2⟩ := hnt j hj
    have h3 : (e : ℤ) * m1 - (i : ℕ) = (e : ℤ) * m2 - (j : ℕ) :=
      zpow_right_injective₀ hl0 hl1.ne' (show (l : ℝ) ^ _ = (l : ℝ) ^ _ by rw [← h1, ← h2, hij])
    have h4 : ((i : ℕ) : ℤ) - (j : ℕ) = 0 := by
      have hi' := i.2
      have hj' := j.2
      refine Int.eq_zero_of_abs_lt_dvd (m := (e : ℤ)) ⟨m1 - m2, by linear_combination -h3⟩ ?_
      rw [abs_lt]; constructor <;> omega
    exact Fin.ext (by omega)

  obtain ⟨i0, -, hi0⟩ := Finset.exists_max_image Finset.univ (fun i => ‖t i‖)
    (Finset.univ_nonempty_iff.2 ⟨⟨0, NeZero.pos e⟩⟩)
  have ht0 : t i0 ≠ 0 := by
    intro h
    apply h0
    rw [hyt]
    refine Finset.sum_eq_zero fun i _ => norm_eq_zero.1 (le_antisymm ?_ (norm_nonneg _))
    simpa [h] using hi0 i (Finset.mem_univ _)
  have hpos : 0 < ‖t i0‖ := norm_pos_iff.2 ht0
  have hrest : ‖∑ i ∈ Finset.univ.erase i0, t i‖ < ‖t i0‖ := by
    have hterm : ∀ i ∈ Finset.univ.erase i0, ‖t i‖ < ‖t i0‖ := by
      intro i hi
      by_cases hti : t i = 0
      · rw [hti, norm_zero]; exact hpos
      refine lt_of_le_of_ne (hi0 i (Finset.mem_univ _)) fun h => ?_
      exact (Finset.mem_erase.1 hi).1 (hdist i i0 hti ht0 h)
    generalize Finset.univ.erase i0 = s at hterm ⊢
    induction s using Finset.induction_on with
    | empty => simpa using hpos
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _)
        (max_lt (hterm i (Finset.mem_insert_self _ _))
          (ih (fun j hj => hterm j (Finset.mem_insert_of_mem hj))))
  have hy2 : ‖y‖ = ‖t i0‖ := by
    rw [hyt, ← Finset.add_sum_erase _ _ (Finset.mem_univ i0),
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hrest.ne', max_eq_left hrest.le]
  obtain ⟨m, hm⟩ := hnt i0 ht0
  exact ⟨_, by rw [hy2, hm]⟩

end GlobalTheory.ValGroupKprime
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormPowRamifiedUniformizerFieldZpowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_pow_ramifiedUniformizerField_zpow : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (y : Om l), y ∈ (ϖ.field a).1 → y ≠ 0 → ∃ j : ℤ, ‖y‖ ^ e = (l : ℝ) ^ j := by
  first | exact @GlobalTheory.ValGroupKprime.norm_pow_field | exact GlobalTheory.ValGroupKprime.norm_pow_field | (intros; apply GlobalTheory.ValGroupKprime.norm_pow_field <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaQlLeInertiaOfFiniteExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RootEqOfNormSubLtOne
namespace GlobalTheory.UltrametricUnitNorm

section
variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem norm_add_lt_one {x y : K} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x + y‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max x y).trans_lt (max_lt hx hy)

theorem norm_pow_sub_one_lt {u : K} (hu : ‖u‖ = 1) (h : ‖u - 1‖ < 1) (i : ℕ) : ‖u ^ i - 1‖ < 1 := by
  induction i with
  | zero => simp
  | succ i ih =>
    have e : u ^ (i + 1) - 1 = u * (u ^ i - 1) + (u - 1) := by ring
    rw [e]
    refine norm_add_lt_one ?_ h
    rwa [norm_mul, hu, one_mul]

theorem norm_geom_sub_lt {u : K} (hu : ‖u‖ = 1) (h : ‖u - 1‖ < 1) (n : ℕ) :
    ‖(∑ i ∈ Finset.range n, u ^ i) - (n : K)‖ < 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (∑ i ∈ Finset.range (n + 1), u ^ i) - ((n + 1 : ℕ) : K)
        = ((∑ i ∈ Finset.range n, u ^ i) - (n : K)) + (u ^ n - 1) := by
      rw [Finset.sum_range_succ]; push_cast; ring
    rw [e]
    exact norm_add_lt_one ih (norm_pow_sub_one_lt hu h n)

omit [IsUltrametricDist K] in
theorem norm_eq_one_of_pow {x : K} {m : ℕ} (hm : 0 < m) (hx : x ^ m = 1) : ‖x‖ = 1 := by
  have h : ‖x‖ ^ m = 1 := by rw [← norm_pow, hx, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg x) hm.ne').1 h

theorem eq_of_norm_sub_lt {m : ℕ} (hm : 0 < m) (hn : ‖(m : K)‖ = 1) {ζ η : K} (hζ : ζ ^ m = 1)
    (hη : η ^ m = 1) (h : ‖η - ζ‖ < 1) : η = ζ := by
  have nζ := norm_eq_one_of_pow hm hζ
  have nη := norm_eq_one_of_pow hm hη
  have z0 : ζ ≠ 0 := by
    rintro rfl
    simp at nζ
  by_contra hne
  have hu : ‖η / ζ‖ = 1 := by rw [norm_div, nζ, nη, div_one]
  have hu1 : η / ζ - 1 = (η - ζ) / ζ := by field_simp
  have hlt : ‖η / ζ - 1‖ < 1 := by rwa [hu1, norm_div, nζ, div_one]
  have hne' : η / ζ - 1 ≠ 0 := by
    rw [hu1]
    exact div_ne_zero (sub_ne_zero.2 hne) z0
  have hs : (∑ i ∈ Finset.range m, (η / ζ) ^ i) = 0 := by
    have := geom_sum_mul (η / ζ) m
    rw [div_pow η ζ m, hη, hζ, div_one, sub_self] at this
    exact (mul_eq_zero.1 this).resolve_right hne'
  have := norm_geom_sub_lt hu hlt m
  rw [hs, zero_sub, norm_neg, hn] at this
  exact lt_irrefl _ this

end

theorem norm_natCast_eq_one {l : ℕ} [hl : Fact (Nat.Prime l)] {m : ℕ} (hlm : ¬l ∣ m) :
    ‖(m : PadicAlgCl l)‖ = 1 := by
  have e : (m : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (m : ℚ_[l]) := (map_natCast _ m).symm
  rw [e, norm_algebraMap', Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hlm

theorem root_eq_of_norm_sub_lt_one {l : ℕ} [hl : Fact (Nat.Prime l)] {m : ℕ} (hm : 0 < m) (hlm : ¬l ∣ m)
    {ζ η : Formalism.BasicNotions.Loc.Om l} (hζ : ζ ^ m = 1) (hη : η ^ m = 1) (h : ‖η - ζ‖ < 1) : η = ζ :=
  eq_of_norm_sub_lt hm (norm_natCast_eq_one hlm) hζ hη h

end GlobalTheory.UltrametricUnitNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaQlLeInertiaOfFiniteExtension
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.BKGal GlobalTheory.Per

namespace GlobalTheory.InerQl

theorem root_eq_of_near {l : ℕ} [hl : Fact l.Prime] {m : ℕ} (hm : 0 < m) (hlm : ¬ l ∣ m)
    {ζ η : Om l} (hζ : ζ ^ m = 1) (hη : η ^ m = 1) (h : ‖η - ζ‖ < 1) : η = ζ := by
  first
  | exact @_root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one
  | exact _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one
  | (apply _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.UltrametricUnitNorm.root_eq_of_norm_sub_lt_one ..)

theorem IK_fixes_Kur {l : ℕ} [hl : Fact l.Prime] (K : FinExt l) {g : ↥(GK K)} (hg : g ∈ IK K)
    {c : Om l} (hc : c ∈ MaximalUnramifiedExtension l) : (g : GQ l) c = c := by
  let Fx : Subgroup ↥(GK K) :=
    { carrier := {g | ∀ c ∈ MaximalUnramifiedExtension l, (g : GQ l) c = c}
      one_mem' := fun c _ => rfl
      mul_mem' := fun {a b} ha hb c hc => by
        show (a : GQ l) ((b : GQ l) c) = c
        rw [hb c hc, ha c hc]
      inv_mem' := fun {a} ha c hc => by
        show ((a : GQ l)⁻¹) c = c
        rw [AlgEquiv.aut_inv]
        conv_lhs => rw [← ha c hc]
        exact AlgEquiv.symm_apply_apply _ _ }
  have hle : IK K ≤ Fx := by
    unfold IK
    rw [Subgroup.closure_le]
    intro σ hσ c hc
    unfold MaximalUnramifiedExtension at hc
    induction hc using IntermediateField.adjoin_induction with
    | mem x hx =>
      obtain ⟨m, hm, hlm, hxm⟩ := hx
      have hxn : ‖x‖ ≤ 1 := by
        have : ‖x‖ ^ m = 1 := by rw [← norm_pow, hxm, norm_one]
        exact ((pow_eq_one_iff_of_nonneg (norm_nonneg x) hm.ne').1 this).le
      exact root_eq_of_near hm hlm hxm (by rw [← map_pow, hxm, map_one]) (hσ x hxn)
    | algebraMap x => exact (σ : GQ l).commutes x
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]
  exact hle hg c hc

theorem IK_mem_Iner : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (g : Gl l), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) → g ∈ (pc Pl h hN hF hS).Iner := by
  intro l _ Pl K' h hN hF hS g hg c
  show (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c
  rw [Pl.PD_actB]
  have hc : (c : Om l) ∈ MaximalUnramifiedExtension l := (IntermediateField.mem_inf.1 c.2).2
  exact Pl.actQ_Kur (g : GQ l) ⟨c, hc⟩ ⟨c, hc⟩ (IK_fixes_Kur _ hg hc)

end GlobalTheory.InerQl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaQlLeInertiaOfFiniteExtensionStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.BKGal GlobalTheory.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_Ql_le_inertia_of_finite_extension : ∀ (l : ℕ) [Fact l.Prime] (Pl : LocPrime l) (K' : FinExt l) (h : (Formalism.MainNotions.ElementDenominator.qlExt l).1 ≤ K'.1) (hN : (GKin h).Normal) (hF : (GKin h).FiniteIndex) (hS : ∀ (g : Gl l) (c : ↥(K0 K')), ∃ c' : ↥(K0 K'), (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap ↥(K0 K') Pl.R.B c) = algebraMap ↥(K0 K') Pl.R.B c') (g : Gl l), g ∈ IK (Formalism.MainNotions.ElementDenominator.qlExt l) → g ∈ (pc Pl h hN hF hS).Iner := by
  first | exact @GlobalTheory.InerQl.IK_mem_Iner | exact GlobalTheory.InerQl.IK_mem_Iner | (intros; apply GlobalTheory.InerQl.IK_mem_Iner <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Adm8AtOfUnramifiedHecke
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Adm8AtOfUnramifiedHecke
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

noncomputable section

namespace GlobalTheory.AdmFrobTriple

theorem not_mem_placesOver_of_ne (E : Type) [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : p ≠ q) {v : HeightOneSpectrum (𝓞 E)} (h1 : v ∈ placesOver E p) : v ∉ placesOver E q := by
  intro h2
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 h)
  obtain ⟨a, b, hab⟩ := hc.map (Int.castRingHom (𝓞 E))
  have h1' : ((p : ℕ) : 𝓞 E) ∈ v.asIdeal := h1
  have h2' : ((q : ℕ) : 𝓞 E) ∈ v.asIdeal := h2
  apply v.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  simp only [eq_intCast, Int.cast_natCast]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1') (Ideal.mul_mem_left _ _ h2')

theorem continuous_algebraMap_padicInt {O : Type} [CommRing O] [TopologicalSpace O] [IsTopologicalRing O]
    {l : ℕ} [Fact l.Prime] [Algebra ℤ_[l] O] (I : Ideal O) (hI : IsAdic I) (hO : (l : O) ∈ I) :
    Continuous (algebraMap ℤ_[l] O) := by
  refine continuous_of_continuousAt_zero (algebraMap ℤ_[l] O) ?_
  rw [ContinuousAt, map_zero, hI.hasBasis_nhds_zero.tendsto_right_iff]
  intro n _
  have hl : (0 : ℝ) < (l : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℤ_[l]) hl] with x hx
  rw [mem_closedBall_zero_iff, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton] at hx
  obtain ⟨y, rfl⟩ := hx
  rw [map_mul, map_pow, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hO n)

theorem sum_coeff_charpolyRev {R : Type} [CommRing R] [Nontrivial R] {n : ℕ} (M : Matrix (Fin n) (Fin n) R) :
    ∑ k ∈ Finset.range (n + 1), M.charpolyRev.coeff k = (1 - M).det := by
  have hdeg : M.charpolyRev.natDegree < n + 1 := by
    rw [← Matrix.reverse_charpoly]
    have := Polynomial.reverse_natDegree_le M.charpoly
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at this
    omega
  have h1 := Polynomial.eval_eq_sum_range' hdeg (1 : R)
  simp only [one_pow, mul_one] at h1
  rw [← h1, Matrix.charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, RingHom.mapMatrix_apply]
  split_ifs <;> simp

variable {D : D7}

theorem l_mem (i : D.ntw.Tw) : ((D.ntw.l i : ℕ) : D.ntw.O0 i) ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i) := by
  intro h
  have h2 := h.map (algebraMap (D.ntw.O0 i) (D.ntw.O i))
  rw [map_natCast] at h2
  exact D.ntw.O_l i h2

theorem continuous_twistCyclotomicCharacter (i : D.ntw.Tw) :
    Continuous fun g : Gen.GE D.nd => ((eps0 D.ntw i g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) :=
  (continuous_algebraMap_padicInt _ (D.ntw.twistBaseCoefficientRing_isAdic i) (l_mem i)).comp
    (Units.continuous_val.comp (continuous_cycZ D.host.E D.nd.Om (D.ntw.l i)))

theorem pD_not (i : D.ntw.Tw) (v) (hv : v ∈ D.ntw.pD i) :
    v ∉ placesOver D.host.E (D.ntw.l i) ∧ ∀ k, v ∉ placesOver D.host.E (D.host.g k) := by
  have h2 : v ∈ (D.ntw.pD i : Set _) := hv
  rw [D.ntw.pD_eq] at h2
  have hl := (D.ntw.lPrime i).out
  split_ifs at h2 with h
  · refine ⟨not_mem_placesOver_of_ne _ D.host.pde'_prime hl ?_ h2, fun k =>
      not_mem_placesOver_of_ne _ D.host.pde'_prime (D.host.g_prime k) (D.host.pde_ne_g k).2 h2⟩
    rw [h]; exact D.host.pde_ne.symm
  · exact ⟨not_mem_placesOver_of_ne _ D.host.pde_prime hl (Ne.symm h) h2, fun k =>
      not_mem_placesOver_of_ne _ D.host.pde_prime (D.host.g_prime k) (D.host.pde_ne_g k).1 h2⟩

end GlobalTheory.AdmFrobTriple

namespace GlobalTheory.AdmFrobTriple

theorem eta_smul {D : D7} (i : D.ntw.Tw) (s : D.ntw.Sig i) (σ : Gen.GE D.nd) :
    ((((eps0 D.ntw i) ^ D.R.t * (chiS i s)⁻¹) σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) •
      ((D.ntw.rhoS i s σ : GL (Fin D.R.r) (D.ntw.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.ntw.O0 i)) =
    (((eps0 D.ntw i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ D.R.t) • Tmat i s σ := by
  simp only [Tmat, MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_mul,
    Units.val_pow_eq_pow_val, mul_smul]

theorem adm8At_of_hkFrob : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → HkFrob i s →
    characterTwistExists D.ntw D.nexp i s := by
  intro D i s hU hH _
  refine ⟨(eps0 D.ntw i) ^ D.R.t * (chiS i s)⁻¹, ?_, ?_, ?_, ?_⟩
  · have hc : Continuous fun g : Gen.GE D.nd => (((chiS i s g)⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) := by
      simp_rw [← map_inv]
      exact (D.ntw.twistCharacterFamily_continuous i _ _).comp continuous_inv
    have he : (fun g : Gen.GE D.nd => ((((eps0 D.ntw i) ^ D.R.t * (chiS i s)⁻¹) g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) =
        fun g => ((eps0 D.ntw i g : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ D.R.t *
          (((chiS i s g)⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) := by
      funext g
      simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_mul,
        Units.val_pow_eq_pow_val]
    rw [he]
    exact ((continuous_twistCyclotomicCharacter i).pow _).mul hc
  · intro P hP _ A hA σ hσ
    have hPl : P ∉ placesOver D.host.E (D.ntw.l i) := fun h => hP (D.ntw.twistExcludedPlaces_contains_residueChar i h)
    have hPg : ∀ k, P ∉ placesOver D.host.E (D.host.g k) := fun k h => hP (D.ntw.placesOver_subset_exceptional i k h)
    have hPd : P ∉ D.ntw.pD i := fun h => hP (D.ntw.primes_subset_exceptional i h)
    have h1 : D.ntw.rhoS i s σ = 1 := hU P hPl hPg A hA σ hσ
    have h2 : chiS i s σ = 1 := D.ntw.twistCharacterFamily_unramified i _ _ P hPl hPg hPd A hA σ hσ
    have h3 : eps0 D.ntw i σ = 1 := (GlobalTheory.TripleGal.eps0_unram_frob D i P hPl A hA).1 σ hσ
    simp [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, h1, h2, h3]
  · intro v hv A hA
    obtain ⟨hl, hg⟩ := pD_not i v hv
    have h1 : ∀ σ ∈ Ine (F := D.host.E) A, D.ntw.rhoS i s σ = 1 := fun σ hσ => hU v hl hg A hA σ hσ
    have h3 : ∀ σ ∈ Ine (F := D.host.E) A, eps0 D.ntw i σ = 1 := (GlobalTheory.TripleGal.eps0_unram_frob D i v hl A hA).1
    have h2 := D.ntw.twistCharacterFamily_at_auxiliaryPlaces i (D.ntw.jS i s) (D.ntw.side i s) v hv A hA
    cases hb : D.ntw.side i s
    · left
      intro σ hσ
      have h2' : chiS i s σ = (D.ntw.delta i σ)⁻¹ := by
        have := h2 σ hσ; rw [hb] at this; simpa [chiS, hb] using this
      simp [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, h1 σ hσ, h2', h3 σ hσ]
    · right
      intro σ hσ
      have h2' : chiS i s σ = D.ntw.delta i σ := by
        have := h2 σ hσ; rw [hb] at this; simpa [chiS, hb] using this
      simp [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.inv_apply, h1 σ hσ, h2', h3 σ hσ]
  · intro P hP hs σ hσ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eta_smul, ← sum_coeff_charpolyRev, map_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    exact hH P hP hs σ hσ k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))

end GlobalTheory.AdmFrobTriple
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Adm8AtOfUnramifiedHeckeStatement
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterTwistExists_of_unrRho_of_hkFrob : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), UnrRho i s → HkFrob i s → characterTwistExists D.ntw D.nexp i s := by
  first | exact @GlobalTheory.AdmFrobTriple.adm8At_of_hkFrob | exact GlobalTheory.AdmFrobTriple.adm8At_of_hkFrob | (intros; apply GlobalTheory.AdmFrobTriple.adm8At_of_hkFrob <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclIntegral
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.BaseCoef

variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G]

abbrev incl {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) : ↥LL.1 →ₐ[ℚ_[l]] ↥LL'.1 :=
  IntermediateField.inclusion h

def IsLatBasis {LL : FinExt l} (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) {k : ℕ}
    (b : Module.Basis (Fin k) ↥LL.1 T.V) : Prop :=
  (∀ i, b i ∈ T.L.T) ∧ ∀ x ∈ T.L.T, ∀ i, b.repr x i ∈ OL LL

def matRep {LL : FinExt l} (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) {k : ℕ}
    (b : Module.Basis (Fin k) ↥LL.1 T.V) : G →* Matrix (Fin k) (Fin k) ↥LL.1 :=
  (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp T.ρ

def matRepExt {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) {k : ℕ}
    (b : Module.Basis (Fin k) ↥LL.1 T.V) : G →* Matrix (Fin k) (Fin k) ↥LL'.1 :=
  ((incl h).mapMatrix : Matrix (Fin k) (Fin k) ↥LL.1 →ₐ[ℚ_[l]] Matrix (Fin k) (Fin k) ↥LL'.1).toRingHom.toMonoidHom.comp
    (matRep T b)

def intVec (LL' : FinExt l) (k : ℕ) : Submodule ↥(OL LL') (Fin k → ↥LL'.1) where
  carrier := {v | ∀ i, v i ∈ OL LL'}
  add_mem' := fun ha hb i => add_mem (ha i) (hb i)
  zero_mem' := fun _ => zero_mem _
  smul_mem' := fun c v hv i => by
    rw [Pi.smul_apply, Subalgebra.smul_def]
    exact mul_mem c.2 (hv i)

theorem incl_integral {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {x : ↥LL.1} (hx : x ∈ OL LL) :
    incl h x ∈ OL LL' := by
  have hx' : IsIntegral ℤ_[l] x := hx
  exact hx'.map ((incl h).restrictScalars ℤ_[l])

theorem rep_apply {F : Type} [Field F] {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) F) (g : G) (x : Fin k → F) :
    CJ.rep M g x = (M g).mulVec x := rfl

set_option synthInstance.maxHeartbeats 400000

def intVecEquiv (LL' : FinExt l) (k : ℕ) : ↥(intVec LL' k) ≃ₗ[↥(OL LL')] (Fin k → ↥(OL LL')) where
  toFun v := fun i => ⟨(v : Fin k → ↥LL'.1) i, v.2 i⟩
  invFun w := ⟨fun i => (w i : ↥LL'.1), fun i => (w i).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem repr_integral {LL : FinExt l} {T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k : ℕ}
    {b : Module.Basis (Fin k) ↥LL.1 T.V} (hb : IsLatBasis T b) (g : G) (i j : Fin k) :
    matRep T b g i j ∈ OL LL := by
  rw [matRep, MonoidHom.comp_apply]
  change LinearMap.toMatrix b b (T.ρ g) i j ∈ OL LL
  rw [LinearMap.toMatrix_apply]
  exact hb.2 _ (T.L.stable g _ (hb.1 j)) i

abbrev extLat {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) (T : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)) {k : ℕ}
    (b : Module.Basis (Fin k) ↥LL.1 T.V) (hb : IsLatBasis T b) : LocLat G ℚ_[l] ↥LL'.1 ↥(OL LL') where
  V := Fin k → ↥LL'.1
  ρ := CJ.rep (matRepExt h T b)
  cont x := by
    refine continuous_pi fun i => ?_
    simp only [rep_apply, Matrix.mulVec, dotProduct]
    refine continuous_finsetSum _ fun j _ => Continuous.mul ?_ continuous_const
    have h1 : Continuous fun g => b.coord i (T.ρ g (b j)) :=
      (IsModuleTopology.continuous_of_linearMap (b.coord i)).comp (T.cont (b j))
    have h2 : Continuous (incl h) := continuous_subtype_val.subtype_mk _
    refine (h2.comp h1).congr fun g => ?_
    simp [matRepExt, matRep, LinearMap.toMatrixAlgEquiv_apply, LinearMap.toMatrix_apply]
  L :=
    { T := intVec LL' k
      stable := fun g x hx i => by
        simp only [rep_apply, Matrix.mulVec, dotProduct]
        refine Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ ?_ (hx j)
        exact incl_integral h (repr_integral hb g i j)
      fg := by
        haveI : Module.Finite ↥(OL LL') ↥(intVec LL' k) := Module.Finite.equiv (intVecEquiv LL' k).symm
        exact Module.Finite.iff_fg.1 inferInstance
      free := Module.Free.of_equiv (intVecEquiv LL' k).symm
      span := by
        rw [eq_top_iff, ← (Pi.basisFun ↥LL'.1 (Fin k)).span_eq]
        refine Submodule.span_mono ?_
        rintro _ ⟨i, rfl⟩ j
        rw [Pi.basisFun_apply]
        by_cases hij : i = j
        · subst hij; simp [one_mem]
        · simp [Pi.single_apply, Ne.symm hij, zero_mem] }

theorem hom_integral {LL : FinExt l} {T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k₁ k₂ : ℕ}
    {b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V} {b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V}
    (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L) (i : Fin k₂) (j : Fin k₁) :
    LinearMap.toMatrix b₁ b₂ F.f i j ∈ OL LL := by
  rw [LinearMap.toMatrix_apply]
  exact hb₂.2 _ (F.T_le _ (hb₁.1 j)) i

def extMat {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k₁ k₂ : ℕ}
    (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (F : LatHom T₁.L T₂.L) :
    Matrix (Fin k₂) (Fin k₁) ↥LL'.1 :=
  (LinearMap.toMatrix b₁ b₂ F.f).map (incl h)

set_option maxHeartbeats 1000000 in
theorem extMat_comm {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k₁ k₂ : ℕ}
    (b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V) (b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V) (F : LatHom T₁.L T₂.L)
    (g : G) : extMat h b₁ b₂ F * matRepExt h T₁ b₁ g = matRepExt h T₂ b₂ g * extMat h b₁ b₂ F := by
  have e1 : matRepExt h T₁ b₁ g = (LinearMap.toMatrix b₁ b₁ (T₁.ρ g)).map (incl h) := rfl
  have e2 : matRepExt h T₂ b₂ g = (LinearMap.toMatrix b₂ b₂ (T₂.ρ g)).map (incl h) := rfl
  have key : LinearMap.toMatrix b₁ b₂ F.f * LinearMap.toMatrix b₁ b₁ (T₁.ρ g) =
      LinearMap.toMatrix b₂ b₂ (T₂.ρ g) * LinearMap.toMatrix b₁ b₂ F.f := by
    have c1 := LinearMap.toMatrix_comp b₁ b₁ b₂ F.f (T₁.ρ g)
    have c2 := LinearMap.toMatrix_comp b₁ b₂ b₂ (T₂.ρ g) F.f
    have hc : F.f ∘ₗ T₁.ρ g = T₂.ρ g ∘ₗ F.f := LinearMap.ext fun y => F.equiv g y
    rw [← c1, ← c2, hc]
  refine Matrix.ext fun i j => ?_
  have := congrArg (fun M => incl h (M i j)) key
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul] at this
  simpa only [e1, e2, Matrix.mul_apply, extMat, Matrix.map_apply] using this

def extHom {LL LL' : FinExt l} (h : LL.1 ≤ LL'.1) {T₁ T₂ : LocLat G ℚ_[l] ↥LL.1 ↥(OL LL)} {k₁ k₂ : ℕ}
    {b₁ : Module.Basis (Fin k₁) ↥LL.1 T₁.V} {b₂ : Module.Basis (Fin k₂) ↥LL.1 T₂.V}
    (hb₁ : IsLatBasis T₁ b₁) (hb₂ : IsLatBasis T₂ b₂) (F : LatHom T₁.L T₂.L) :
    LatHom (extLat h T₁ b₁ hb₁).L (extLat h T₂ b₂ hb₂).L where
  f := Matrix.toLin' (extMat h b₁ b₂ F)
  equiv g x := by
    change (extMat h b₁ b₂ F).mulVec ((matRepExt h T₁ b₁ g).mulVec x) =
      (matRepExt h T₂ b₂ g).mulVec ((extMat h b₁ b₂ F).mulVec x)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, extMat_comm]
  cont := LinearMap.continuous_on_pi _
  T_le x hx i := by
    change (extMat h b₁ b₂ F).mulVec x i ∈ OL LL'
    simp only [Matrix.mulVec, dotProduct, extMat, Matrix.map_apply]
    exact Subalgebra.sum_mem _ fun j _ => Subalgebra.mul_mem _ (incl_integral h (hom_integral hb₁ hb₂ F i j)) (hx j)

def mapSig {I LL LL' : Type} [Group I] [Field LL] [Field LL'] (f : LL →+* LL') (Sig : Finset (I →* LLˣ)) :
    Finset (I →* LL'ˣ) := by
  classical
  exact Sig.image fun a => (Units.map (f : LL →* LL')).comp a

end GlobalTheory.BaseCoef
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalFrobeniusBreuilKisinCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalFrobeniusBreuilKisinCoordinates
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysFrobCoord

theorem span_range_eq_top {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) :
    Submodule.span B (Set.range u) = ⊤ := by
  set S := Submodule.span B (Set.range u)
  obtain ⟨w, -, hu⟩ := h (N ⧸ S) 0
  have h1 := hu S.mkQ (fun x => by
    simpa using (Submodule.Quotient.mk_eq_zero S).2 (Submodule.subset_span ⟨x, rfl⟩))
  have h2 := hu 0 (fun x => by simp)
  rw [eq_top_iff]
  intro y _
  have : S.mkQ y = 0 := by rw [h1, ← h2]; rfl
  exact (Submodule.Quotient.mk_eq_zero S).1 this

theorem frac_indep {A M B : Type} [CommRing A] [AddCommGroup M] [Module A M] [CommRing B] [IsDomain B]
    (d : A) (J : A →+* B) (hd : J d ≠ 0) (lam : M →+ B) (hlam : ∀ r y, lam (r • y) = J r * lam y)
    {z : LocalizedModule (Submonoid.powers d) M} {n n' : M} {k k' : ℕ} (h : IsFrac d z n k)
    (h' : IsFrac d z n' k') {b : B} (hb : lam n' = J d ^ k' * b) : lam n = J d ^ k * b := by
  unfold IsFrac at h h'
  obtain ⟨⟨_, s, rfl⟩, hs⟩ := LocalizedModule.mk_eq.1 (h.symm.trans h')
  have h2 := congrArg lam hs
  simp only [Submonoid.smul_def, hlam, map_pow, hb] at h2
  have h3 := mul_left_cancel₀ (pow_ne_zero s hd) h2
  refine mul_left_cancel₀ (pow_ne_zero k' hd) ?_
  rw [h3]; ring

theorem frac_formula {A M B : Type} [CommRing A] [AddCommGroup M] [Module A M] [CommRing B] [IsDomain B]
    (d : A) (φ : A →+* A)
    (Φ : M →ₛₗ[(algebraMap A (Localization.Away d)).comp φ] LocalizedModule (Submonoid.powers d) M)
    (J : A →+* B) (hd : J d ≠ 0) (lam : M →+ B) (hlam : ∀ r y, lam (r • y) = J r * lam y)
    (F : M →+ B) (hF : ∀ r y, F (r • y) = J (φ r) * F y) (S : Set M) (hS : Submodule.span A S = ⊤)
    (h0 : ∀ y ∈ S, ∀ n k, IsFrac d (Φ y) n k → lam n = J d ^ k * F y) (y n : M) (k : ℕ)
    (h : IsFrac d (Φ y) n k) : lam n = J d ^ k * F y := by
  have key : ∀ y ∈ Submodule.span A S, ∃ n k, IsFrac d (Φ y) n k ∧ lam n = J d ^ k * F y := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨n, k, hn⟩ := exists_isFrac d (Φ y)
      exact ⟨n, k, hn, h0 y hy n k hn⟩
    | zero => exact ⟨0, 0, by simp [IsFrac], by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨n, k, hn, en⟩ := hx
      obtain ⟨m, j, hm, em⟩ := hy
      refine ⟨d ^ j • n + d ^ k • m, k + j, ?_, ?_⟩
      · unfold IsFrac at hn hm ⊢
        rw [map_add (f := _), hn, hm, LocalizedModule.mk_add_mk]
        congr 1
        exact Subtype.ext (pow_add d k j).symm
      · rw [map_add (f := _), hlam, hlam, en, em, map_add (f := _), map_pow, map_pow]; ring
    | smul r x _ hx =>
      obtain ⟨n, k, hn, en⟩ := hx
      refine ⟨φ r • n, k, ?_, ?_⟩
      · unfold IsFrac at hn ⊢
        rw [map_smulₛₗ, hn, RingHom.comp_apply, algebraMap_smul, LocalizedModule.smul'_mk]
      · rw [hlam, hF, en]; ring
  obtain ⟨n', k', h', e'⟩ := key y (hS ▸ Submodule.mem_top)
  exact frac_indep d J hd lam hlam h h' e'

section Maps

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] (t : Wq l a →ₐ[ℤ_[l]] O) (e : ℕ)

theorem frob_toAc (x : (Wq l a)⟦X⟧) (τ : ZMod a) :
    frob K l (toAc t K x (τ - 1) : K⟦X⟧) = (toAc t K (frobS l a x) τ : K⟦X⟧) := by
  ext n
  have : coeff n (frobS l a x) = if l ∣ n then sigma l a (coeff (n / l) x) else 0 := by
    simp only [frobS, RingHom.comp_apply, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, coeff_expand]
    split_ifs <;> simp
  rw [coeff_frob, coeff_toAc, coeff_toAc, this]
  split_ifs
  · rw [emb_sigma]
  · simp

theorem coe_toAc_eis (τ : ZMod a) : (toAc t K (eis l a e) τ : K⟦X⟧) = E K l e := by
  have hX : toAc t K X = fun _ => uIn (A O K) :=
    funext fun τ => Subtype.ext ((congrArg (PowerSeries.map _) (PowerSeries.map_X _)).trans
      (PowerSeries.map_X _))
  rw [eis, map_add (f := _), map_pow, hX, map_natCast]
  simp [E]

end Maps

theorem frob_in_coordinates : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → (∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e) (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k → c m = fun τ i => E K l e ^ k * P.phi (c x) τ i) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (hl : (l : PP.A) ∈ PP.I) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (g : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ (w : (Wq l a)⟦X⟧), J τ (p.f w) = g (toAc t K (frobS l a w) τ : K⟦X⟧)) → (∀ τ y, J τ (PP.D.φ y) = φ₂ (J (τ - 1) y)) → (∀ f, φ₂ (g f) = g (frob K l f)) → Function.Injective g → ∀ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) → (∀ x τ i, lam (EE.tr p x) τ i = g (frob K l (c x (τ - 1) i))) → ∀ (y n : EE.M PP) (k : ℕ), IsFrac (l : PP.A) (EE.Φ PP ⟨l, hl⟩ y) n k → ∀ τ i, lam n τ i = (l : K⟦X⟧⟦X⟧) ^ k * (((P.mx (τ - 1)).map (frob K l)).map g *ᵥ fun j => φ₂ (lam y (τ - 1) j)) i := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P EE c _ hc PP hl p J g φ₂ hJp hJφ hφg hg lam hlam hlamtr y n k h τ i
  have hK : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  have hl0 : (l : K) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hl1 : (l : K⟦X⟧) ≠ 0 := fun h => hl0 (by simpa using congrArg constantCoeff h)
  have hl2 : (l : K⟦X⟧⟦X⟧) ≠ 0 := fun h => hl1 (by simpa using congrArg constantCoeff h)
  have hE : E K l e ≠ 0 := fun h => hl0 (by
    simpa [E, NeZero.ne e] using congrArg constantCoeff h)
  have hJE : J τ (p.f (eis l a e)) = g (frob K l (E K l e)) := by
    rw [hJp, ← frob_toAc, coe_toAc_eis]
  have hJE0 : g (frob K l (E K l e)) ≠ 0 := by
    rw [map_ne_zero_iff _ hg, map_ne_zero_iff _ (frob_injective l)]; exact hE
  let lam' : EE.M PP →+ K⟦X⟧⟦X⟧ :=
    { toFun := fun y => lam y τ i, map_zero' := by simp, map_add' := by simp }
  let F : EE.M PP →+ K⟦X⟧⟦X⟧ :=
    { toFun := fun y => (((P.mx (τ - 1)).map (frob K l)).map g *ᵥ fun j => φ₂ (lam y (τ - 1) j)) i
      map_zero' := by simp [Matrix.mulVec, dotProduct]
      map_add' := by simp [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib] }
  have hJl : J τ (l : PP.A) = l := map_natCast _ _
  have := frac_formula (l : PP.A) PP.D.φ (EE.Φ PP ⟨l, hl⟩) (J τ) (hJl ▸ hl2) lam'
    (fun r y => hlam r y τ i) F ?_ _ (span_range_eq_top (EE.tr_bc p)) ?_ y n k h
  · rw [hJl] at this; exact this
  · intro r y
    simp only [F, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mulVec, dotProduct, hlam, map_mul, hJφ,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  · rintro _ ⟨x, rfl⟩ n k h
    obtain ⟨m', k', hm'⟩ := exists_isFrac (A := (ϖ.prism a).A) (eis l a e)
      (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x)
    obtain ⟨r, hr⟩ := EE.Φ_nat p ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ ⟨l, hl⟩ x m' k' n k hm' h
    have h1 := congrArg (fun y => lam y τ i) hr
    simp only [hlam, map_sub, Pi.sub_apply, map_zero, Pi.zero_apply, map_pow, map_mul, hJl, hJE] at h1
    have h2 := sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ (mul_ne_zero hJE0 hl2)))
    rw [hlamtr, hc x m' k' hm'] at h2
    rw [hJl]
    refine mul_left_cancel₀ (pow_ne_zero k' hJE0) ?_
    change _ * lam n τ i = _
    rw [← h2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [F, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Matrix.mulVec, dotProduct, hlamtr, hφg,
      PhiMod.phi_apply, frobV_apply, map_mul, map_pow, map_sum, Matrix.map_apply]
    ring

end GlobalTheory.CrysFrobCoord
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystalFrobeniusBreuilKisinCoordinatesStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystal_frobenius_breuilKisin_coordinates : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → (∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e) (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k → c m = fun τ i => E K l e ^ k * P.phi (c x) τ i) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (hl : (l : PP.A) ∈ PP.I) (p : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (J : ZMod a → PP.A →+* K⟦X⟧⟦X⟧) (g : K⟦X⟧ →+* K⟦X⟧⟦X⟧) (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ τ (w : (Wq l a)⟦X⟧), J τ (p.f w) = g (toAc t K (frobS l a w) τ : K⟦X⟧)) → (∀ τ y, J τ (PP.D.φ y) = φ₂ (J (τ - 1) y)) → (∀ f, φ₂ (g f) = g (frob K l f)) → Function.Injective g → ∀ lam : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧), (∀ (r : PP.A) (y : EE.M PP) τ i, lam (r • y) τ i = J τ r * lam y τ i) → (∀ x τ i, lam (EE.tr p x) τ i = g (frob K l (c x (τ - 1) i))) → ∀ (y n : EE.M PP) (k : ℕ), IsFrac (l : PP.A) (EE.Φ PP ⟨l, hl⟩ y) n k → ∀ τ i, lam n τ i = (l : K⟦X⟧⟦X⟧) ^ k * (((P.mx (τ - 1)).map (frob K l)).map g *ᵥ fun j => φ₂ (lam y (τ - 1) j)) i := by
  first | exact @GlobalTheory.CrysFrobCoord.frob_in_coordinates | exact GlobalTheory.CrysFrobCoord.frob_in_coordinates | (intros; apply GlobalTheory.CrysFrobCoord.frob_in_coordinates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdOtherRootFactorsActionFirstCoordinate
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdOtherRootFactorsActionFirstCoordinate
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.RootFactorProduct

private lemma map_sub_smul_E_mulVec_eq {O : Type} [CommRing O] [IsDomain O] {n r t : ℕ}
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O]
      ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (E X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O)
    (hE : ∀ u, e ((E.map (toFr O)).mulVec u) = (0, (e u).2))
    (hX : ∀ u, e ((X₀.map (toFr O)).mulVec u) =
      (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1)) * (e u).2 c))
    (a : ℕ) (v : Fin n → FractionRing O) :
    e (((X₀ - ρ a • E).map (toFr O)).mulVec v) =
      (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1) - ρ a) * (e v).2 c) := by
  have hm : (X₀ - ρ a • E).map (toFr O) = X₀.map (toFr O) - toFr O (ρ a) • E.map (toFr O) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, map_mul]
  have hs : ((toFr O (ρ a)) • E.map (toFr O)).mulVec v = toFr O (ρ a) • (E.map (toFr O)).mulVec v := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum,
      mul_assoc]
  rw [hm, Matrix.sub_mulVec, hs, map_sub, map_smul, hX, hE]
  refine Prod.ext (by simp) ?_
  funext c
  simp only [Prod.snd_sub, Prod.smul_snd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub]
  ring

theorem prod_cons_action {O : Type} [CommRing O] [IsDomain O] {n r t : ℕ}
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O]
      ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (E X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O)
    (hE : ∀ u, e ((E.map (toFr O)).mulVec u) = (0, (e u).2))
    (hX : ∀ u, e ((X₀.map (toFr O)).mulVec u) =
      (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1)) * (e u).2 c))
    (s : List ℕ) : ∀ (a : ℕ) (u : Fin n → FractionRing O),
      e (((((a :: s).map fun c => X₀ - ρ c • E).prod).map (toFr O)).mulVec u) =
        (0, fun c : Fin t =>
          toFr O (((a :: s).map fun c' => ρ ((c : ℕ) + 1) - ρ c').prod) * (e u).2 c) := by
  induction s with
  | nil =>
    intro a u
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact map_sub_smul_E_mulVec_eq e E X₀ ρ hE hX a u
  | cons b s ih =>
    intro a u
    rw [List.map_cons, List.prod_cons, Matrix.map_mul, ← Matrix.mulVec_mulVec,
      map_sub_smul_E_mulVec_eq e E X₀ ρ hE hX a, ih b u]
    refine Prod.ext rfl ?_
    funext c
    simp only [List.map_cons, List.prod_cons, map_mul, mul_assoc]

private lemma list_prod_range'_eq_prod_Ico {M : Type} [CommMonoid M] (g : ℕ → M) (n : ℕ) :
    ∀ m : ℕ, ((List.range' m n).map g).prod = ∏ k ∈ Finset.Ico m (m + n), g k := by
  induction n with
  | zero => intro m; simp
  | succ n ih =>
    intro m
    rw [List.range'_succ, List.map_cons, List.prod_cons, ih, show m + (n + 1) = m + 1 + n by omega,
      Finset.prod_eq_prod_Ico_succ_bot (show m < m + 1 + n by omega)]

theorem prod_other_factors_action {O : Type} [CommRing O] [IsDomain O] {n r t : ℕ}
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O]
      ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (E X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O) (ht : 2 ≤ t)
    (hE : ∀ u, e ((E.map (toFr O)).mulVec u) = (0, (e u).2))
    (hX : ∀ u, e ((X₀.map (toFr O)).mulVec u) =
      (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1)) * (e u).2 c)) (u : Fin n → FractionRing O) :
    e (((((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • E).prod).map (toFr O)).mulVec u) =
      (0, fun c : Fin t => if (c : ℕ) = 0 then
        toFr O (∏ c' ∈ Finset.Ioc 1 t, (ρ 1 - ρ c')) * (e u).2 c else 0) := by
  have hl : List.range' 2 (t - 1) = 2 :: List.range' 3 (t - 2) := by
    rw [show t - 1 = (t - 2) + 1 by omega, List.range'_succ]
  rw [hl, prod_cons_action e E X₀ ρ hE hX, ← hl]
  refine Prod.ext rfl ?_
  funext c
  dsimp only
  split_ifs with h0
  · simp only [h0, zero_add]
    congr 2
    all_goals
      rw [list_prod_range'_eq_prod_Ico]
      apply Finset.prod_congr _ (fun _ _ => rfl)
      ext x
      simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega
  · have hc := c.isLt
    rw [List.prod_eq_zero, map_zero, zero_mul]
    exact List.mem_map.2 ⟨(c : ℕ) + 1, List.mem_range'_1.2 ⟨by omega, by omega⟩, sub_self _⟩

end GlobalTheory.RootFactorProduct
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdOtherRootFactorsActionFirstCoordinateStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_other_root_factors_action_first_coordinate : ∀ {O : Type} [CommRing O] [IsDomain O] {n r t : ℕ} (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))) (E X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O), 2 ≤ t → (∀ u, e ((E.map (toFr O)).mulVec u) = (0, (e u).2)) → (∀ u, e ((X₀.map (toFr O)).mulVec u) = (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1)) * (e u).2 c)) → ∀ u, e (((((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • E).prod).map (toFr O)).mulVec u) = (0, fun c : Fin t => if (c : ℕ) = 0 then toFr O (∏ c' ∈ Finset.Ioc 1 t, (ρ 1 - ρ c')) * (e u).2 c else 0) := by
  first | exact @GlobalTheory.RootFactorProduct.prod_other_factors_action | exact GlobalTheory.RootFactorProduct.prod_other_factors_action | (intros; apply GlobalTheory.RootFactorProduct.prod_other_factors_action <;> assumption)
end
end
