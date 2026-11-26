module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.PSmooth
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.IntegrableOnSimp

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.WhittakerSmoothForms.EtaTop
noncomputable section

open Set Filter Topology MeasureTheory

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]
variable {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ}

def Stk (U : Set V) : Prop := ∀ (q : ℕ) (ω : V → V [⋀^Fin q]→L[ℝ] ℝ), ContDiffOn ℝ 1 ω U →
  ∀ y : Fin (q + 2) → V, (∀ j, y j ∈ U) → dC' (intS' ω) y = intS' (extDeriv ω) y

def Wf (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (o : V) (j : ℕ)
    (g : ℕ → Γ) : ℝ :=
  intS' (eta A φ c j g) (fun l : Fin (j + 1) => A (g (k + 1 - j + l)) o)

def Bf (A : Γ →* (V →L[ℝ] V)) (φ : V → ℝ) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (o : V) (j : ℕ)
    (g : ℕ → Γ) : ℝ :=
  intS' (Kf A φ (eta A φ c j) g) (fun l : Fin (j + 1) => A (g (k - j + l)) o)

theorem kf_dep (hD : PDep A φ) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (j : ℕ) (σ σ' : ℕ → Γ)
    (h : ∀ n, n + j + 1 ≤ k + 1 → σ n = σ' n) :
    Kf A φ (eta A φ c j) σ = Kf A φ (eta A φ c j) σ' := by
  funext x
  simp only [Kf]
  congr 1
  funext γ
  rw [hD k c j (cons γ σ) (cons γ σ') (fun n hn => by
    cases n with
    | zero => rfl
    | succ m => exact h m (by omega))]

theorem eta_top (H : Hyp U A φ) (hD : PDep A φ) (hC : PCoc U A φ) {k : ℕ}
    (c : (Fin (k + 2) → Γ) → ℝ) (hc : Coc c) (τ τ' : ℕ → Γ) (x : V) (hx : x ∈ U) :
    eta A φ c (k + 1) τ x = eta A φ c (k + 1) τ' x := by
  have h0 := hC H k c hc (k + 1) le_rfl (cons (τ 0) τ') x hx
  rw [Nat.sub_self] at h0
  have e1 : eta A φ c (k + 1) (skip 0 (cons (τ 0) τ')) = eta A φ c (k + 1) τ' := by
    congr 1
  have e2 : eta A φ c (k + 1) (skip 1 (cons (τ 0) τ')) = eta A φ c (k + 1) τ :=
    hD k c (k + 1) _ _ (fun n hn => by
      have : n = 0 := by omega
      subst this
      simp [skip, cons])
  simp only [delG, Finset.sum_range_succ, Finset.sum_range_zero, e1, e2] at h0
  simp at h0
  rw [add_neg_eq_zero] at h0
  exact h0.symm

private theorem neg_one_pow_add_one_add_eq_mul (a : ℕ) (m : ℕ) : (-1 : ℝ) ^ (a + 1 + m) = (-1) ^ a * (-1) ^ (m + 1) := by
  ring

theorem chain (H : Hyp U A φ) (hH : PHom U A φ) (hSm : PSmooth U A φ) (hD : PDep A φ)
    (hC : PCoc U A φ) (hS : Stk U) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (hc : Coc c) {o : V}
    (ho : o ∈ U) (a j : ℕ) (hk : a + j = k) (g : ℕ → Γ) :
    ∑ i ∈ Finset.range (k + 2), (-1 : ℝ) ^ i * Bf A φ c o j (skip i g) =
      Wf A φ c o j g + (-1) ^ a * Wf A φ c o (j + 1) g := by
  subst hk
  obtain ⟨ω, hω⟩ : ∃ ω, ω = Kf A φ (eta A φ c j) g := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : Fin (j + 2) → V, Y = fun l : Fin (j + 2) => A (g (a + (l : ℕ))) o := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : Fin (j + 1) → V, Z = fun l : Fin (j + 1) => A (g (a + 1 + (l : ℕ))) o :=
    ⟨_, rfl⟩
  have hYU : ∀ l, Y l ∈ U := fun l => by rw [hY]; exact H.mapsTo _ _ ho
  have hZU : ∀ l, Z l ∈ U := fun l => by rw [hZ]; exact H.mapsTo _ _ ho
  have hcont : ∀ σ, ContinuousOn (Kf A φ (eta A φ c j) σ) U :=
    fun σ => ((hSm H (a + j) c j σ).2).continuousOn
  have hK : ∀ i, a + 1 ≤ i → Kf A φ (eta A φ c j) (skip i g) = ω := by
    intro i hi
    rw [hω]
    exact kf_dep hD c j _ _ (fun n hn => by simp only [skip]; rw [if_pos (by omega)])
  have hF2 : ∀ x ∈ U, (∑ i ∈ Finset.range (a + 2),
      ((-1 : ℝ) ^ i) • Kf A φ (eta A φ c j) (skip i g)) x = eta A φ c j g x := by
    intro x hx
    have h1 := hH H j a (eta A φ c j) g x hx
    have h0 : ∀ γ, psi A φ γ x • delG (a + 1) (eta A φ c j) (cons γ g) x = 0 := by
      intro γ
      have := hC H (a + j) c hc j (by omega) (cons γ g) x hx
      rw [show a + j + 1 - j = a + 1 by omega] at this
      rw [this, smul_zero]
    have h2 : Kf A φ (delG (a + 1) (eta A φ c j)) g x = 0 := by
      simp only [Kf, h0, finsum_zero]
    rw [h2, sub_zero] at h1
    rw [← h1]
    simp only [delG, Finset.sum_apply]
  have hWj : Wf A φ c o j g = ∑ i ∈ Finset.range (a + 2),
      (-1 : ℝ) ^ i * intS' (Kf A φ (eta A φ c j) (skip i g)) Z := by
    rw [← intS'_sum H.convex _ _ _ (fun i _ => hcont _) hZU]
    rw [intS'_congr H.convex hF2 hZU]
    simp only [Wf, hZ]
    congr 1
    funext l
    rw [show a + j + 1 - j + ↑l = a + 1 + ↑l by omega]
  have hBA : ∀ i, i < a + 1 → Bf A φ c o j (skip i g) = intS' (Kf A φ (eta A φ c j) (skip i g)) Z := by
    intro i hi
    simp only [Bf, hZ]
    congr 1
    funext l
    simp only [skip]
    rw [if_neg (by omega), show a + j - j + ↑l + 1 = a + 1 + ↑l by omega]
  have hBB : ∀ m : Fin (j + 1), Bf A φ c o j (skip (a + 1 + ↑m) g) =
      intS' ω (fun l => Y (m.succ.succAbove l)) := by
    intro m
    simp only [Bf, hY]
    rw [hK _ (by omega)]
    congr 1
    funext l
    simp only [skip, Fin.succAbove]
    split_ifs <;> simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at * <;>
      first | (exfalso; omega) | (congr 3; omega)
  have hExt : extDeriv ω = eta A φ c (j + 1) g := by rw [hω]; rfl
  have hSt := hS j ω (by
    rw [hω]
    exact ((hSm H (a + j) c j g).2).of_le (by exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤))) Y hYU
  rw [hExt] at hSt
  rw [dC', Fin.sum_univ_succ] at hSt
  have hW1 : Wf A φ c o (j + 1) g = intS' (eta A φ c (j + 1) g) Y := by
    simp only [Wf, hY]
    congr 1
    funext l
    rw [show a + j + 1 - (j + 1) + ↑l = a + ↑l by omega]
  have hY0 : (fun l => Y ((0 : Fin (j + 2)).succAbove l)) = Z := by
    funext l
    simp only [hY, hZ, Fin.succAbove_zero, Fin.val_succ]
    rw [show a + (↑l + 1) = a + 1 + ↑l by omega]
  rw [hY0] at hSt
  rw [show a + j + 2 = (a + 1) + (j + 1) by omega, Finset.sum_range_add]
  rw [Finset.sum_congr rfl (fun i hi => by rw [hBA i (Finset.mem_range.mp hi)])]
  rw [Finset.sum_range (fun m => (-1 : ℝ) ^ (a + 1 + m) * Bf A φ c o j (skip (a + 1 + m) g))]
  simp only [hBB]
  rw [Finset.sum_range_succ, hK _ le_rfl] at hWj
  rw [hWj, hW1, ← hSt]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, neg_one_pow_add_one_add_eq_mul, mul_assoc]
  rw [mul_add, ← Finset.mul_sum]
  ring

end PositivityTheory.KB.WhittakerCocycle

end
end

noncomputable section

open Set Filter Topology MeasureTheory

namespace PositivityTheory.KB.WhittakerCocycle

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {Γ : Type} [Group Γ]
variable {U : Set V} {A : Γ →* (V →L[ℝ] V)} {φ : V → ℝ}

def ext' {m : ℕ} (τ : Fin m → Γ) (n : ℕ) : Γ := if h : n < m then τ ⟨n, h⟩ else 1

private theorem isClosed_simplex_fin_sum_le_one (q : ℕ) : IsClosed {t : Fin q → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} := by
  show IsClosed ({t : Fin q → ℝ | ∀ j, 0 ≤ t j} ∩ {t | ∑ j, t j ≤ 1})
  apply IsClosed.inter
  · rw [Set.ofPred_forall]
    exact isClosed_iInter fun j => isClosed_le continuous_const (continuous_apply j)
  · exact isClosed_le (continuous_finsetSum _ fun j _ => continuous_apply j) continuous_const

private theorem simplex_point_mem_of_convex_of_vertices_mem {q : ℕ} (hU : Convex ℝ U) (y : Fin (q + 1) → V) (hy : ∀ i, y i ∈ U)
    (t : Fin q → ℝ) (ht : (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1) :
    y 0 + ∑ j, t j • (y j.succ - y 0) ∈ U := by
  have e : y 0 + ∑ j, t j • (y j.succ - y 0) =
      ∑ i, (Fin.cons (1 - ∑ j, t j) t : Fin (q + 1) → ℝ) i • y i := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smul_sub, Finset.sum_sub_distrib, sub_smul, one_smul,
      ← Finset.sum_smul]
    abel
  rw [e]
  apply hU.sum_mem
  · intro i _
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.cons_zero]
      linarith [ht.2]
    | succ i =>
      simp only [Fin.cons_succ]
      exact ht.1 i
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    ring
  · intro i _
    exact hy i

private theorem intS'_congr_of_eqOn_convex {q : ℕ} (hU : Convex ℝ U) (ω ω' : V → V [⋀^Fin q]→L[ℝ] ℝ)
    (hω : ∀ x ∈ U, ω x = ω' x) (y : Fin (q + 1) → V) (hy : ∀ i, y i ∈ U) :
    intS' ω y = intS' ω' y := by
  unfold intS'
  apply setIntegral_congr_fun (isClosed_simplex_fin_sum_le_one q).measurableSet
  intro t ht
  simp only [hω _ (simplex_point_mem_of_convex_of_vertices_mem hU y hy t ht)]

private theorem intS'_comp_continuousLinearMap {q : ℕ} (ω : V → V [⋀^Fin q]→L[ℝ] ℝ) (B : V →L[ℝ] V)
    (y : Fin (q + 1) → V) :
    intS' ω (fun l => B (y l)) = intS' (fun x => (ω (B x)).compContinuousLinearMap B) y := by
  unfold intS'
  apply setIntegral_congr_fun (isClosed_simplex_fin_sum_le_one q).measurableSet
  intro t _
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply, map_add (f := _), map_sum, map_smul,
    map_sub, Function.comp_def]

private theorem kf_eta_congr_of_eq_on_initial_of_pDep (hD : PDep A φ) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (j : ℕ)
    (σ σ' : ℕ → Γ) (h : ∀ m, m + j ≤ k → σ m = σ' m) :
    Kf A φ (eta A φ c j) σ = Kf A φ (eta A φ c j) σ' := by
  funext x
  simp only [Kf]
  congr 1
  funext γ
  rw [hD k c j (cons γ σ) (cons γ σ')]
  intro n hn
  cases n with
  | zero => rfl
  | succ m => exact h m (by omega)

theorem Bf_dep (hD : PDep A φ) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (o : V) (j : ℕ) (hj : j ≤ k)
    (g g' : ℕ → Γ) (h : ∀ n ≤ k, g n = g' n) : Bf A φ c o j g = Bf A φ c o j g' := by
  simp only [Bf]
  rw [kf_eta_congr_of_eq_on_initial_of_pDep hD c j g g' (fun m hm => h m (by omega))]
  congr 1
  funext l
  rw [h _ (by have := l.isLt; omega)]

theorem Bf_inv (H : Hyp U A φ) (hE : PEquiv U A φ) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (hc : Coc c)
    {o : V} (ho : o ∈ U) (j : ℕ) (x : Γ) (g : ℕ → Γ) :
    Bf A φ c o j (fun n => x * g n) = Bf A φ c o j g := by
  simp only [Bf]
  have hpts : (fun l : Fin (j + 1) => A (x * g (k - j + ↑l)) o) =
      fun l : Fin (j + 1) => A x (A (g (k - j + ↑l)) o) := by
    funext l
    rw [map_mul]
    rfl
  have hpsi : ∀ γ, ∀ h ∈ U, psi A φ γ (A x h) = psi A φ (x⁻¹ * γ) h := by
    intro γ h _
    simp only [psi]
    rw [mul_inv_rev, inv_inv, map_mul]
    rfl
  rw [hpts, intS'_comp_continuousLinearMap]
  refine intS'_congr_of_eqOn_convex H.convex _ _ ?_ _ (fun _ => H.mapsTo _ o ho)
  intro h hh
  rw [(hE H k c hc.inv (A x) x⁻¹ (H.mapsTo x) hpsi j (fun n => x * g n) h hh).2]
  simp only [inv_mul_cancel_left]

private theorem apply_add_succAbove_eq_skip (g : ℕ → Γ) (a : ℕ) {n : ℕ} (i : Fin (n + 1)) (l : Fin n) :
    g (a + ↑(i.succAbove l)) = skip (a + ↑i) g (a + ↑l) := by
  simp only [skip]
  rcases lt_or_ge l.val i.val with hl | hl
  · rw [Fin.succAbove_of_castSucc_lt _ _ (by rw [Fin.lt_def]; simpa using hl), if_pos (by omega)]
    rfl
  · rw [Fin.succAbove_of_le_castSucc _ _ (by rw [Fin.le_def]; simpa using hl), if_neg (by omega)]
    simp only [Fin.val_succ, Nat.add_assoc]

theorem tele (H : Hyp U A φ) (hH : PHom U A φ) (hSm : PSmooth U A φ) (hD : PDep A φ)
    (hC : PCoc U A φ) (hE : PEquiv U A φ) (hS : Stk U) {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ)
    (hc : Coc c) {o : V} (ho : o ∈ U) :
    ∀ j ≤ k + 1, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∃ b : (ℕ → Γ) → ℝ,
      (∀ x g, b (fun n => x * g n) = b g) ∧ (∀ g g', (∀ n ≤ k, g n = g' n) → b g = b g') ∧
      ∀ g, Wf A φ c o 0 g = ∑ i ∈ Finset.range (k + 2), (-1 : ℝ) ^ i * b (skip i g) + s * Wf A φ c o j g := by
  intro j
  induction j with
  | zero =>
    intro _
    exact ⟨1, Or.inl rfl, fun _ => 0, fun _ _ => rfl, fun _ _ _ => rfl, fun g => by simp⟩
  | succ j ih =>
    intro hj
    obtain ⟨s, hs, b, hbi, hbd, hb⟩ := ih (by omega)
    refine ⟨-s * (-1) ^ (k - j), ?_, fun g => b g + s * Bf A φ c o j g, ?_, ?_, fun g => ?_⟩
    · rcases hs with rfl | rfl <;> rcases neg_one_pow_eq_or ℝ (k - j) with h | h <;> rw [h] <;> norm_num
    · intro x g
      simp only [hbi, Bf_inv H hE c hc ho]
    · intro g g' hg
      simp only [hbd g g' hg, Bf_dep hD c o j (by omega) g g' hg]
    · rw [hb g]
      have hch := chain H hH hSm hD hC hS c hc ho (k - j) j (by omega) g
      have e : ∑ i ∈ Finset.range (k + 2), (-1 : ℝ) ^ i * (b (skip i g) + s * Bf A φ c o j (skip i g)) =
          ∑ i ∈ Finset.range (k + 2), (-1 : ℝ) ^ i * b (skip i g) +
            s * ∑ i ∈ Finset.range (k + 2), (-1 : ℝ) ^ i * Bf A φ c o j (skip i g) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [e, hch]
      ring

private theorem wf_zero_ext'_eq {k : ℕ} (c : (Fin (k + 2) → Γ) → ℝ) (o : V) (g : Fin (k + 2) → Γ) :
    Wf A φ c o 0 (ext' g) = c g := by
  have ez : eta A φ c 0 (ext' g) =
      fun _ => ContinuousAlternatingMap.constOfIsEmpty ℝ V (Fin 0) (c fun i => ext' g ↑i) := rfl
  simp only [Wf]
  rw [ez]
  unfold intS'
  simp only [ContinuousAlternatingMap.constOfIsEmpty_apply]
  have hS : {t : Fin 0 → ℝ | (∀ j, 0 ≤ t j) ∧ ∑ j, t j ≤ 1} = Set.univ := by
    ext t
    simp
  have e : (fun i : Fin (k + 2) => ext' g ↑i) = g := by
    funext i
    simp [ext', i.isLt]
  rw [hS, e, setIntegral_univ, integral_const]
  simp [Measure.real, volume_pi, Measure.pi_empty_univ]

private theorem eta_succ_congr_of_coc_of_mem (H : Hyp U A φ) (hD : PDep A φ) (hC : PCoc U A φ) {k : ℕ}
    (c : (Fin (k + 2) → Γ) → ℝ) (hc : Coc c) (σ σ' : ℕ → Γ) {h : V} (hh : h ∈ U) :
    eta A φ c (k + 1) σ h = eta A φ c (k + 1) σ' h := by
  have e := hC H k c hc (k + 1) le_rfl (cons (σ 0) σ') h hh
  have h1 : eta A φ c (k + 1) (skip 0 (cons (σ 0) σ')) = eta A φ c (k + 1) σ' :=
    hD k c (k + 1) _ _ (fun n hn => by
      obtain rfl : n = 0 := by omega
      rfl)
  have h2 : eta A φ c (k + 1) (skip 1 (cons (σ 0) σ')) = eta A φ c (k + 1) σ :=
    hD k c (k + 1) _ _ (fun n hn => by
      obtain rfl : n = 0 := by omega
      rfl)
  rw [Nat.sub_self] at e
  simp only [delG, Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Finset.sum_apply,
    Pi.add_apply, Pi.smul_apply, pow_zero, pow_one, one_smul, neg_smul, h1, h2] at e
  rw [add_neg_eq_zero] at e
  exact e.symm

theorem pComp (hH : PHom U A φ) (hSm : PSmooth U A φ) (hD : PDep A φ) (hC : PCoc U A φ)
    (hE : PEquiv U A φ) : PComp U A φ := by
  intro H hStk k c hc o ho
  obtain ⟨s, hs, b, hbi, hbd, hW⟩ := tele H hH hSm hD hC hE hStk c hc ho (k + 1) le_rfl
  refine ⟨s, hs, fun y => b (ext' y), ?_, ?_⟩
  · intro x y
    beta_reduce
    rw [← hbi x (ext' y)]
    apply hbd
    intro n hn
    simp [ext', show n < k + 1 by omega]
  · intro g
    have h0 := hW (ext' g)
    rw [wf_zero_ext'_eq c o g] at h0
    have hWk : Wf A φ c o (k + 1) (ext' g) =
        intS' (eta A φ c (k + 1) fun _ => 1) (fun l : Fin (k + 2) => A (g l) o) := by
      simp only [Wf]
      have ep : (fun l : Fin (k + 2) => A (ext' g (k + 1 - (k + 1) + ↑l)) o) =
          fun l : Fin (k + 2) => A (g l) o := by
        funext l
        simp [ext', l.isLt]
      rw [ep]
      exact intS'_congr_of_eqOn_convex H.convex _ _ (fun h hh => eta_succ_congr_of_coc_of_mem H hD hC c hc _ _ hh) _
        (fun _ => H.mapsTo _ o ho)
    have hsum : ∑ i ∈ Finset.range (k + 2), (-1 : ℝ) ^ i * b (skip i (ext' g)) =
        dC' (fun y => b (ext' y)) g := by
      simp only [dC']
      rw [Finset.sum_range]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      apply hbd
      intro n hn
      have := apply_add_succAbove_eq_skip (ext' g) 0 i (⟨n, by omega⟩ : Fin (k + 1))
      simp only [zero_add, Fin.val_mk] at this
      rw [← this]
      simp [ext', show n < k + 1 by omega]
    rw [hWk, hsum] at h0
    rw [h0]
    ring

end PositivityTheory.KB.WhittakerCocycle

end
