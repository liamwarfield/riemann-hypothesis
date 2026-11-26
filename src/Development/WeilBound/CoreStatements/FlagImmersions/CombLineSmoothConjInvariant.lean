module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
public import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.CombLineSmoothConjInvariant
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

namespace Ii

theorem contDiffOn_zpow_h {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (A : HermLine ι)
    (hA : IsSmoothHerm A) (n : ℤ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => A.h z ^ n) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  unfold IsSmoothHerm at hA
  have hne : ∀ z ∈ {z : (k : K) × ι k → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0}, A.h z ≠ 0 :=
    fun z hz => (A.pos z hz).ne'
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · simpa using hA.pow m
  · simp only [zpow_neg, zpow_natCast]
    exact (hA.pow m).inv (fun z hz => pow_ne_zero _ (hne z hz))

end Ii

open Ii in
theorem combLine_smooth_conj_invariant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (J : Type) [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ), ((∀ j, IsSmoothHerm (ℓ j)) → IsSmoothHerm (combLine ℓ n)) ∧ ((∀ j, IsConjInvariantH (ℓ j)) → IsConjInvariantH (combLine ℓ n)) ∧ IsSmoothHerm (trivLine ι) := by
  intro K _ ι _ J _ ℓ n
  refine ⟨fun h => ?_, fun h z => ?_, ?_⟩
  · exact contDiffOn_prod fun j _ => contDiffOn_zpow_h (ℓ j) (h j) (n j)
  · exact Finset.prod_congr rfl fun j _ => by rw [h j z]
  · exact contDiffOn_const

end RootFieldNumerics
end

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.AltCMul
noncomputable section

open MvPolynomial GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics.M5

variable {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N : ℕ}

def expo (a : Ψ → Fin N → ℕ) (σ : Ψ → Equiv.Perm (Fin N)) : (Ψ × Fin N) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun x => a x.1 (σ x.1 x.2))

def alt (a : Ψ → Fin N → ℕ) (G : RP Ψ N) : ℝ :=
  ∑ σ : Ψ → Equiv.Perm (Fin N), (∏ τ, ((Equiv.Perm.sign (σ τ) : ℤ) : ℝ)) * G.coeff (expo a σ)

def rho : Ψ → Fin N → ℕ := fun _ c => N - 1 - (c : ℕ)

def bump (τ : Ψ) (c : Fin N) (k : ℕ) : Ψ → Fin N → ℕ :=
  fun τ' c' => N - 1 - (c' : ℕ) + if τ' = τ ∧ c' = c then k else 0

def lam (τ : Ψ) (k : ℕ) (G : RP Ψ N) : ℝ := ∑ c, alt (bump τ c k) G

def Maj (f : Polynomial ℝ) (c A : ℝ) : Prop := ∀ s : ℕ, |f.coeff s| ≤ c * A ^ s / (s.factorial : ℝ)

def gdet (e : Fin N → ℕ) (v : Fin N → Polynomial ℝ) : Polynomial ℝ :=
  Matrix.det (Matrix.of fun c b => Polynomial.C (((e c).factorial : ℝ)⁻¹) * v b ^ e c)

theorem degFl_eq (G : RP Ψ N) : degFl G = (-1) ^ dimFl Ψ N * alt rho G := rfl

theorem alt_add (a : Ψ → Fin N → ℕ) (F G : RP Ψ N) : alt a (F + G) = alt a F + alt a G := by
  simp [alt, mul_add, Finset.sum_add_distrib]

theorem alt_C_mul (a : Ψ → Fin N → ℕ) (r : ℝ) (G : RP Ψ N) : alt a (C r * G) = r * alt a G := by
  simp only [alt, coeff_C_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem alt_sum {ι : Type*} (a : Ψ → Fin N → ℕ) (s : Finset ι) (F : ι → RP Ψ N) :
    alt a (∑ i ∈ s, F i) = ∑ i ∈ s, alt a (F i) := by
  simp only [alt, coeff_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem lam_add (τ : Ψ) (k : ℕ) (F G : RP Ψ N) : lam τ k (F + G) = lam τ k F + lam τ k G := by
  simp [lam, alt_add, Finset.sum_add_distrib]

theorem lam_sum {ι : Type*} (τ : Ψ) (k : ℕ) (s : Finset ι) (F : ι → RP Ψ N) :
    lam τ k (∑ i ∈ s, F i) = ∑ i ∈ s, lam τ k (F i) := by
  simp only [lam, alt_sum]
  exact Finset.sum_comm

end RootFieldNumerics.M5
end
end

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.IntersectionConstantMetricLine
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

noncomputable section

namespace RootFieldNumerics

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem ptsIntegral_const_mul (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ)
    (g : ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ) :
    ptsIntegral P φ (fun z => c * g z) = c * ptsIntegral P φ g := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [← MeasureTheory.integral_const_mul]
    refine congrArg _ (funext fun y => ?_)
    rw [← smul_eq_mul, smul_finsum]
    refine finsum_congr (fun w => ?_)
    rw [smul_finsum]
    refine finsum_congr (fun hw => ?_)
    unfold sheetDensity
    split_ifs <;> simp [mul_assoc]
  · simp

theorem ptsIntegral_const (P : Ideal (MRing ι)) {e : ℕ} (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (c : ℝ) :
    ptsIntegral P φ (fun _ => c) = c * ptsIntegral P φ (fun _ => 1) := by
  simpa using ptsIntegral_const_mul P φ (fun _ => (1 : ℝ)) c

theorem smooth_constLine (c : ℝ) :
    IsSmoothHerm (HermLine.ofWeight (ι := ι) (fun _ => c) (fun _ _ _ => rfl)) := by
  unfold IsSmoothHerm HermLine.ofWeight
  exact contDiffOn_const

theorem intersection_constant_metric_line : ∀ II : IntersectionSystem, IsIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (L : Fin e → HermLine ι) (c : ℝ), IsArithVar P (e + 1) → (∀ j, IsSmoothHerm (L j)) → II K ι P (e + 1) (Fin.snoc L (HermLine.ofWeight (fun _ => c) (fun _ _ _ => rfl))) = -c * ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
  intro II hII K _ ι _ P e L c hP hL
  have hA : IsSmoothHerm (HermLine.ofWeight (ι := ι) (fun _ => c) (fun _ _ _ => rfl)) :=
    smooth_constLine c
  have hprime : P.IsPrime := hP.2.1.1
  have h1 : (1 : MRing ι) ∉ P := fun h => hprime.ne_top ((Ideal.eq_top_iff_one P).2 h)
  have hhom : IsMultiHomog (1 : MRing ι) (fun _ => 0) := by
    intro m hm k
    rw [MvPolynomial.support_one] at hm
    rw [Finset.mem_singleton.1 hm]
    simp
  rw [(hII K ι).2.2 P e L _ 1 (fun _ => 0) hP hL hA (fun k => by simp [HermLine.ofWeight]) hhom h1]
  have hempty : divSupp P (1 : MRing ι) = ∅ := by
    ext W
    simp only [divSupp, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hW
    rw [Ideal.span_singleton_one, sup_top_eq] at hW
    exact (hW.1.1.ne_top (top_le_iff.1 hW.1.2)).elim
  unfold recR arInt
  simp only [hempty, Set.mem_empty_iff_false, finsum_false, finsum_zero, zero_sub]
  have hln : logNorm (HermLine.ofWeight (ι := ι) (fun _ => c) (fun _ _ _ => rfl)) (1 : MRing ι) = fun _ => c := by
    funext z
    simp [logNorm, HermLine.ofWeight, Real.log_exp]
  rw [hln, ptsIntegral_const]
  ring

end RootFieldNumerics
end
end

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.IntersectionMonomialLines
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

namespace Ii

theorem exists_perm_of_map_eq {α J : Type} [Fintype α] (f g : α → J)
    (h : Finset.univ.val.map f = Finset.univ.val.map g) : ∃ σ : Equiv.Perm α, ∀ a, g (σ a) = f a := by
  classical
  have hc : ∀ j, Fintype.card {a // f a = j} = Fintype.card {a // g a = j} := by
    intro j
    have := congrArg (Multiset.count j) h
    simp only [Multiset.count_map] at this
    rw [Fintype.card_subtype, Fintype.card_subtype]
    convert this using 1 <;> simp [Finset.card_def, Finset.filter_val, eq_comm]
  let e : ∀ j, {a // f a = j} ≃ {a // g a = j} := fun j => Fintype.equivOfCardEq (hc j)
  let σ : Equiv.Perm α :=
    ((Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaCongrRight e)).trans (Equiv.sigmaFiberEquiv g)
  refine ⟨σ, fun a => ?_⟩
  exact (e (f a) ⟨a, rfl⟩).2

theorem toMultiset_sum_single {d : ℕ} {J : Type} (w : Fin d → J) :
    Finsupp.toMultiset (∑ k, Finsupp.single (w k) 1 : J →₀ ℕ) = Finset.univ.val.map w := by
  rw [Finsupp.toMultiset_sum]
  simp only [Finsupp.toMultiset_single, one_smul]
  rw [← Multiset.sum_map_singleton (Finset.univ.val.map w), Multiset.map_map]
  rfl

end Ii

open Ii in
theorem intersection_monomial_lines : ∀ II : IntersectionSystem, IsIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (d : ℕ) (J : Type) (ℓ : J → HermLine ι) (w : Fin d → J), IsArithVar P d → (∀ j, IsSmoothHerm (ℓ j)) → (∑ k, Finsupp.single (w k) 1 : J →₀ ℕ).degree = d ∧ ∃ σ : Equiv.Perm (Fin d), monoLines ℓ (∑ k, Finsupp.single (w k) 1) d = (fun k => ℓ (w k)) ∘ σ ∧ II K ι P d (monoLines ℓ (∑ k, Finsupp.single (w k) 1) d) = II K ι P d (fun k => ℓ (w k)) := by
  intro II hII K _ ι _ P d J ℓ w hP hℓ
  set m : J →₀ ℕ := ∑ k, Finsupp.single (w k) 1 with hm
  have hdeg : m.degree = d := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hm, map_sum, Finsupp.degree_single]
  set L : List J := (Finsupp.toMultiset m).toList with hL
  have hML : (L : Multiset J) = Finset.univ.val.map w := by
    rw [hL, Multiset.coe_toList, hm, toMultiset_sum_single]
  have hlen : L.length = d := by
    have := congrArg Multiset.card hML
    simpa using this
  let f : Fin d → J := fun k => L.get (Fin.cast hlen.symm k)
  have hf : List.ofFn f = L :=
    List.ext_get (by simp [hlen]) (fun i h1 h2 => by simp [f])
  have hmap : Finset.univ.val.map f = Finset.univ.val.map w := by
    rw [Fin.univ_val_map, hf, hML]
  obtain ⟨σ, hσ⟩ := exists_perm_of_map_eq f w hmap
  have hmono : monoLines ℓ m d = (fun k => ℓ (w k)) ∘ σ := by
    funext k
    have hk : (k : ℕ) < L.length := by
      rw [hlen]
      exact k.2
    simp only [monoLines, Function.comp_apply, hσ k]
    rw [dite_eq_left hk]
    rfl
  refine ⟨hdeg, σ, hmono, ?_⟩
  rw [hmono]
  exact (hII K ι).1 P d (fun k => ℓ (w k)) σ hP (fun j => hℓ _)

end RootFieldNumerics
end

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.RootModelLineSemipositive
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isOpen_nonvanishing_blocks : IsOpen {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  have : {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = ⋂ k, ⋃ i, {z : (Σ k, ι k) → ℂ | z ⟨k, i⟩ ≠ 0} := by
    ext z; simp
  rw [this]
  exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
    isOpen_ne_fun (continuous_apply _) continuous_const

theorem smooth_metric_zpow {A : HermLine ι} (hA : IsSmoothHerm A) (n : ℤ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => A.h z ^ n) {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
  cases n with
  | ofNat m =>
    simp only [Int.ofNat_eq_coe, zpow_natCast]
    exact hA.pow m
  | negSucc m =>
    simp only [zpow_negSucc]
    exact (hA.pow (m + 1)).inv fun z hz => pow_ne_zero _ (A.pos z hz).ne'

theorem combLine_smooth {J : Type} [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ)
    (h : ∀ j, IsSmoothHerm (ℓ j)) : IsSmoothHerm (combLine ℓ n) := by
  show ContDiffOn ℝ _ (fun z => ∏ j, (ℓ j).h z ^ n j) _
  exact contDiffOn_prod fun j _ => smooth_metric_zpow (h j) (n j)

theorem combLine_conj_invariant {J : Type} [Fintype J] (ℓ : J → HermLine ι) (n : J → ℤ)
    (h : ∀ j, IsConjInvariantH (ℓ j)) : IsConjInvariantH (combLine ℓ n) := by
  intro z
  show ∏ j, (ℓ j).h _ ^ n j = ∏ j, (ℓ j).h z ^ n j
  exact Finset.prod_congr rfl fun j _ => by rw [h j z]

end

theorem leviForm_congr_eventually {ι : Type} [Fintype ι] {φ ψ : (ι → ℂ) → ℝ} {z : ι → ℂ} (h : φ =ᶠ[𝓝 z] ψ)
    (w : ι → ℂ) : leviForm φ z w = leviForm ψ z w := by
  simp only [leviForm, h.fderiv.fderiv_eq]

theorem leviForm_smul {ι : Type} [Fintype ι] (c : ℝ) (φ : (ι → ℂ) → ℝ) (z w : ι → ℂ) :
    leviForm (c • φ) z w = c * leviForm φ z w := by
  by_cases hc : c = 0
  · subst hc
    simp [leviForm]
  · letI : Invertible c := invertibleOfNonzero hc
    have h1 : fderiv ℝ (c • φ) = c • fderiv ℝ φ :=
      funext fun x => fderiv_const_smul_of_invertible c
    have h2 : fderiv ℝ (c • fderiv ℝ φ) z = c • fderiv ℝ (fderiv ℝ φ) z :=
      fderiv_const_smul_of_invertible c
    simp only [leviForm, h1, h2, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring

theorem root_model_line_semipositive : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℝ) (q : ℕ) (n : Option (Ψ × Fin N) → ℤ), (∀ j, (n j : ℝ) = q * M.coef lam s j) → M.Semipos t lam s → IsSemipositiveH M.P (combLine (M.line t) n) ∧ IsConjInvariantH (combLine (M.line t) n) := by
  intro Ψ _ N M t lam s q n hn hS
  have hsm : IsSmoothHerm (combLine (M.line t) n) := by
    refine combLine_smooth _ _ fun j => ?_
    cases j with
    | none => exact M.A_smooth
    | some r => exact M.x_smooth t r
  have hcj : IsConjInvariantH (combLine (M.line t) n) := by
    refine combLine_conj_invariant _ _ fun j => ?_
    cases j with
    | none => exact M.A_conj
    | some r => exact M.x_conj t r
  refine ⟨⟨hsm, fun z hz w hw => ?_⟩, hcj⟩
  have hev : (fun y => Real.log ((combLine (M.line t) n).h y)) =ᶠ[𝓝 z]
      ((q : ℝ) • M.weight t lam s) := by
    filter_upwards [isOpen_nonvanishing_blocks.mem_nhds hz.1] with y hy
    rw [Pi.smul_apply, smul_eq_mul]
    show Real.log (∏ j, (M.line t j).h y ^ n j) =
      (q : ℝ) * ∑ j, M.coef lam s j * Real.log ((M.line t j).h y)
    rw [Real.log_prod (fun j _ => zpow_ne_zero _ ((M.line t j).pos y hy).ne'), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.log_zpow, hn j]
    ring
  rw [leviForm_congr_eventually hev w, leviForm_smul]
  exact mul_nonneg (Nat.cast_nonneg _) (hS z hz w hw)

end RootFieldNumerics
end

section -- merged from Development.WeilBound.CoreStatements.FlagImmersions.PerturbedWeightWallBounds
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace RootFieldNumerics

theorem dominant_of_gaps {Ψ : Type} {N : ℕ} (mu : Wt Ψ N)
    (h : ∀ τ (i : ℕ), i + 1 < N → 0 ≤ ent mu τ i - ent mu τ (i + 1)) : Dominant mu := by
  intro τ a b hab
  have hab' : (a : ℕ) ≤ b := hab
  have key : ∀ k : ℕ, (a : ℕ) + k < N → ent mu τ ((a : ℕ) + k) ≤ ent mu τ a := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have h1 := h τ ((a : ℕ) + k) (by omega)
      have h2 := ih (by omega)
      show ent mu τ ((a : ℕ) + k + 1) ≤ ent mu τ a
      linarith
  have h3 := key ((b : ℕ) - a) (by omega)
  rw [Nat.add_sub_cancel' hab'] at h3
  simpa [ent, a.isLt, b.isLt] using h3

theorem abs_ent_le {Ψ : Type} [Fintype Ψ] {N : ℕ} (mu : Wt Ψ N) (τ : Ψ) (i : ℕ) : |ent mu τ i| ≤ ‖mu‖ := by
  unfold ent
  split_ifs with h
  · exact (norm_le_pi_norm (mu τ) _).trans (norm_le_pi_norm mu τ)
  · simp

theorem perturbed_weight_wall_bounds : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (c₀ θ₀ : ℝ), 0 < c₀ → 0 < θ₀ → ∃ B₁ : ℕ, ∀ B : ℕ, B₁ ≤ B → ∀ (τ₀ : Ψ) (lam₀ : Wt Ψ N), InWall T.j τ₀ c₀ lam₀ → let θ : ℝ := 5 * Fintype.card Ψ / B; let lam : Wt Ψ N := fun τ i => lam₀ τ i + (if τ = τ₀ ∧ (i : ℕ) < T.j then 2 * θ else 0); 3 ≤ B ∧ 0 < θ ∧ θ ≤ θ₀ ∧ θ ≤ 1 ∧ ‖lam‖ ≤ 1 ∧ ‖T.lamS lam (θ ^ 2)‖ ≤ 1 ∧ (∀ τ, θ ≤ gap T.j lam τ) ∧ gap T.j lam τ₀ = 2 * θ ∧ CompactGapsGE T.j c₀ lam ∧ Dominant lam ∧ Dominant (T.lamS lam (θ ^ 2)) ∧ NefThreshold T.j B (T.lamS lam (θ ^ 2)) ∧ ‖T.lamS lam (θ ^ 2) - lam₀‖ ≤ 2 * θ + ‖T.nu‖ * θ ^ 2 := by
  intro Ψ _ _ N T c₀ θ₀ hc₀ hθ₀
  set R := ‖T.nu‖ with hR
  have hR0 : 0 ≤ R := norm_nonneg _
  set δ : ℝ := min (min θ₀ (1 / 8)) (min (c₀ / 2) (1 / (4 * (R + 1)))) with hδ
  have hδpos : 0 < δ :=
    lt_min (lt_min hθ₀ (by norm_num)) (lt_min (by linarith) (by positivity))
  refine ⟨max 10 ⌈5 * (Fintype.card Ψ : ℝ) / δ⌉₊, ?_⟩
  intro B hB τ₀ lam₀ hW
  intro θ lam
  obtain ⟨hn0, hg0, hgo, hcg⟩ := hW
  have hcard : (1 : ℝ) ≤ Fintype.card Ψ := by
    exact_mod_cast Fintype.card_pos_iff.mpr ⟨τ₀⟩
  have hB10 : (10 : ℝ) ≤ B := by exact_mod_cast (le_max_left _ _).trans hB
  have hBpos : (0 : ℝ) < B := by linarith
  have hBc : 5 * (Fintype.card Ψ : ℝ) / δ ≤ B :=
    (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hB)
  have hθdef : θ = 5 * (Fintype.card Ψ : ℝ) / B := rfl
  have hθpos : 0 < θ := by rw [hθdef]; exact div_pos (by linarith) hBpos
  have hθδ : θ ≤ δ := by
    rw [hθdef, div_le_iff₀ hBpos]
    have := (div_le_iff₀ hδpos).mp hBc
    linarith [mul_comm (B : ℝ) δ]
  have hθθ₀ : θ ≤ θ₀ := hθδ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hθ8 : θ ≤ 1 / 8 := hθδ.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hθc : θ ≤ c₀ / 2 := hθδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hθR' : θ ≤ 1 / (4 * (R + 1)) := hθδ.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hθR : θ * R ≤ 1 / 4 := by
    rw [le_div_iff₀ (by positivity)] at hθR'
    nlinarith
  have hθB : θ * B = 5 * (Fintype.card Ψ : ℝ) := by
    rw [hθdef]; field_simp
  let D : Wt Ψ N := fun τ i => if τ = τ₀ ∧ (i : ℕ) < T.j then 2 * θ else 0
  have hD : ‖D‖ ≤ 2 * θ := by
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun τ => ?_)
    refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr (fun i => ?_)
    simp only [D]
    split_ifs
    · rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    · simp; positivity
  have hlamD : lam = lam₀ + D := by funext τ i; rfl
  have hnlam : ‖lam‖ ≤ 1 / 2 + 2 * θ := by
    rw [hlamD]; exact (norm_add_le _ _).trans (by linarith)
  have hnmu : ‖T.lamS lam (θ ^ 2)‖ ≤ 1 / 2 + 2 * θ + θ ^ 2 * R := by
    show ‖lam - θ ^ 2 • T.nu‖ ≤ _
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  have hθ2R : θ ^ 2 * R ≤ θ / 4 := by
    have : θ ^ 2 * R = θ * (θ * R) := by ring
    rw [this]
    have := mul_le_mul_of_nonneg_left hθR hθpos.le
    linarith
  have hnmu1 : ‖T.lamS lam (θ ^ 2)‖ ≤ 1 := by linarith
  have hent : ∀ τ i, ent lam τ i = ent lam₀ τ i + (if τ = τ₀ ∧ i < T.j then 2 * θ else 0) := by
    intro τ i
    by_cases hi : i < N
    · simp [ent, hi, lam]
    · have : ¬ (i < T.j) := by have := T.j_lt; omega
      simp [ent, hi, this]
  have hentS : ∀ (mu : Wt Ψ N) (s : ℝ) τ i,
      ent (T.lamS mu s) τ i = ent mu τ i - s * ent T.nu τ i := by
    intro mu s τ i
    by_cases hi : i < N <;> simp [ent, hi, RootTower.lamS]
  have hnuD : ∀ τ i, ent T.nu τ i - ent T.nu τ (i + 1) ≤ 2 * R := by
    intro τ i
    have h1 := abs_ent_le T.nu τ i
    have h2 := abs_ent_le T.nu τ (i + 1)
    have h3 := le_abs_self (ent T.nu τ i)
    have h4 := neg_abs_le (ent T.nu τ (i + 1))
    linarith
  have hgapLam : ∀ τ i, i + 1 < N → 2 * θ ≤ ent lam τ i - ent lam τ (i + 1) := by
    intro τ i hi
    rw [hent, hent]
    rcases lt_trichotomy (i + 1) T.j with hlt | heq | hgt
    · have hc := hcg τ i hi hlt.ne
      have h1 : i < T.j := by omega
      by_cases hτ : τ = τ₀
      · subst hτ
        simp [h1, hlt]
        linarith
      · simp [hτ]
        linarith
    · have h1 : i < T.j := by omega
      have h2 : ¬ i + 1 < T.j := by omega
      have hg : gap T.j lam₀ τ = ent lam₀ τ i - ent lam₀ τ (i + 1) := by
        simp only [gap]; rw [← heq]; simp
      by_cases hτ : τ = τ₀
      · subst hτ
        simp [h1, h2]
        linarith [hg0, hg]
      · have := hgo τ hτ
        simp [hτ]
        linarith
    · have hc := hcg τ i hi hgt.ne'
      have h1 : ¬ i < T.j := by omega
      have h2 : ¬ i + 1 < T.j := by omega
      simp [h1, h2]
      linarith
  have hj1 : T.j - 1 + 1 = T.j := by have := T.j_pos; omega
  have hj2 : T.j - 1 + 1 < N := by have := T.j_pos; have := T.j_lt; omega
  have hgapj : ∀ τ, 2 * θ ≤ gap T.j lam τ := by
    intro τ
    have h := hgapLam τ (T.j - 1) hj2
    rw [hj1] at h
    exact h
  have hgapmu : ∀ τ, θ ≤ gap T.j (T.lamS lam (θ ^ 2)) τ := by
    intro τ
    have h := hgapj τ
    have hn := hnuD τ (T.j - 1)
    rw [hj1] at hn
    simp only [gap] at h ⊢
    rw [hentS, hentS]
    have : θ ^ 2 * (ent T.nu τ (T.j - 1) - ent T.nu τ T.j) ≤ θ ^ 2 * (2 * R) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    linarith
  refine ⟨?_, hθpos, hθθ₀, by linarith, by linarith, hnmu1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := (le_max_left 10 _).trans hB
    omega
  · intro τ; have := hgapj τ; linarith
  · have h1 : T.j - 1 < T.j := by have := T.j_pos; omega
    simp only [gap]
    rw [hent, hent]
    have := hg0
    simp only [gap] at this
    simp [h1]
    linarith
  · intro τ i hi hij
    rw [hent, hent]
    have hc := hcg τ i hi hij
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have h1 : i < T.j := by omega
      by_cases hτ : τ = τ₀
      · subst hτ
        simp [h1, hlt]
        linarith
      · simp [hτ]
        linarith
    · have h1 : ¬ i < T.j := by omega
      have h2 : ¬ i + 1 < T.j := by omega
      simp [h1, h2]
      linarith
  · exact dominant_of_gaps lam (fun τ i hi => by have := hgapLam τ i hi; linarith)
  · refine dominant_of_gaps _ (fun τ i hi => ?_)
    rw [hentS, hentS]
    have h := hgapLam τ i hi
    have hn := hnuD τ i
    have : θ ^ 2 * (ent T.nu τ i - ent T.nu τ (i + 1)) ≤ θ ^ 2 * (2 * R) :=
      mul_le_mul_of_nonneg_left hn (by positivity)
    linarith
  · intro τ
    have hg := hgapmu τ
    have hB2 : (0 : ℝ) ≤ (B : ℝ) - 2 := by linarith
    have h1 : ((B : ℝ) - 2) * θ ≤ ((B : ℝ) - 2) * gap T.j (T.lamS lam (θ ^ 2)) τ :=
      mul_le_mul_of_nonneg_left hg hB2
    have he : ((B : ℝ) - 2) * θ = θ * B - 2 * θ := by ring
    have h3 : 4 * (Fintype.card Ψ : ℝ) * ‖T.lamS lam (θ ^ 2)‖ ≤ 4 * (Fintype.card Ψ : ℝ) :=
      mul_le_of_le_one_right (by positivity) hnmu1
    linarith
  · have hsub : T.lamS lam (θ ^ 2) - lam₀ = D - θ ^ 2 • T.nu := by
      funext τ i
      simp [RootTower.lamS, lam, D]
      ring
    rw [hsub]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith

end RootFieldNumerics
end
