module

public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyConstantFinprodSchwartzBruhatFiniteAdel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.InitialPairs.SquareIntegrableOfLatticeTorus
section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.InitialPairs.SquareIntegrableIntegralHolds
noncomputable section

namespace PositivityTheory.ThKEst.Sq

open scoped ENNReal
open MeasureTheory Finset PositivityTheory.ThKEst

theorem cone_exponent_bound_holds : ConeExp := by
  intro r c hc
  have h1 := ReciprocityTheory.ThetaSummability.Est.integrableOn_exp_logCone (0 : ℝ) (s := c) fun k => by
    have := hc (k.val + 1) (by omega) k.isLt
    unfold psum at this
    unfold ReciprocityTheory.ThetaSummability.Est.partialSum
    rw [Finset.sum_filter]
    simpa only [Nat.lt_succ_iff, Fin.le_def] using this
  have h2 : Cone r ⊆ ReciprocityTheory.ThetaSummability.Est.logCone r 0 := fun t ht k => by
    unfold ReciprocityTheory.ThetaSummability.Est.gap
    split_ifs with h
    · exact sub_nonneg.2 (ht.1 (by simp [Fin.le_def]))
    · simpa using ht.2 k
  refine (lintegral_mono_set h2).trans_lt ?_
  have h3 := h1.2
  rwa [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)] at h3

def ext {y : ℕ} (t : Fin y → ℝ) (j : ℕ) : ℝ := if h : j < y then t ⟨j, h⟩ else 0

theorem sum_ext {y N : ℕ} (hN : y ≤ N) (t : Fin y → ℝ) (g : ℕ → ℝ → ℝ) (hg : ∀ j, g j 0 = 0) :
    ∑ j : Fin y, g j (t j) = ∑ j ∈ range N, g j (ext t j) := by
  rw [← Finset.sum_subset (Finset.range_mono hN) fun j _ hj => by
    rw [ext, dite_eq_right (by simpa using hj), hg], ← Fin.sum_univ_eq_sum_range (fun j => g j (ext t j))]
  exact Finset.sum_congr rfl fun j _ => by simp [ext]

theorem sum_cut {q N : ℕ} (hN : q ≤ N) (g : ℕ → ℝ) :
    ∑ j : Fin q, g j = ∑ j ∈ range N, if j < q then g j else 0 := by
  rw [Fin.sum_univ_eq_sum_range g, ← Finset.sum_filter]
  congr 1
  ext j
  simp only [mem_range, mem_filter]
  omega

theorem ext_nonneg {y : ℕ} {t : Fin y → ℝ} (ht : t ∈ Cone y) (j : ℕ) : 0 ≤ ext t j := by
  unfold ext
  split_ifs
  · exact ht.2 _
  · exact le_rfl

theorem ext_anti {y : ℕ} {t : Fin y → ℝ} (ht : t ∈ Cone y) : Antitone (ext t) := by
  intro i j hij
  by_cases hj : j < y
  · rw [ext, ext, dite_eq_left hj, dite_eq_left (by omega)]
    exact ht.1 (by simpa [Fin.le_def] using hij)
  · rw [ext, dite_eq_right hj]
    exact ext_nonneg ht i

theorem coneAff (r : ℕ) (a b : ℝ) (h : ∀ k : ℕ, 1 ≤ k → k ≤ r → a + b * ((k : ℝ) - 1) / 2 < 0) :
    ∫⁻ t in Cone r, ENNReal.ofReal (Real.exp (∑ i : Fin r, (a + b * (i.val : ℝ)) * t i)) < ⊤ := by
  refine cone_exponent_bound_holds r _ fun k hk hkr => ?_
  have e : psum (fun i : Fin r => a + b * (i.val : ℝ)) k = k * (a + b * ((k : ℝ) - 1) / 2) := by
    unfold psum
    rw [Fin.sum_univ_eq_sum_range (fun j => if j < k then a + b * (j : ℝ) else 0), ← sum_cut hkr (fun j => a + b * (j : ℝ)),
      Fin.sum_univ_eq_sum_range (fun j => a + b * (j : ℝ))]
    clear h hk hkr
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [e]
  exact mul_neg_of_pos_of_neg (by exact_mod_cast hk) (h k hk hkr)

theorem square_integrable_integral_holds : ConeIntegralsFinite := by
  intro n d q y D hD h1 h2
  constructor
  · refine lt_of_eq_of_lt (lintegral_congr fun s => ?_) (coneAff q (D * (d / 2 - n + 1)) (2 * D) fun k hk hkq => ?_)
    · rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      simp only [rho2, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    · rcases h1 with h1 | h1
      · omega
      · have a1 : (d : ℝ) + 2 * k < 2 * n := by exact_mod_cast (by omega : d + 2 * k < 2 * n)
        nlinarith
  · refine lt_of_eq_of_lt (lintegral_congr fun s => ?_) (coneAff y (D * (n - d + 1)) (2 * D) fun k hk hkq => ?_)
    · rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2
      simp only [rho2, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    · rcases h2 with h2 | h2
      · omega
      · have a1 : (n : ℝ) + k < d := by exact_mod_cast (by omega : n + k < d)
        nlinarith

theorem posWt_eq (n d : ℕ) {q y : ℕ} (s : Fin q → ℝ) (t : Fin y → ℝ) :
    posWt n d s t = d * ∑ i, s i + n * ∑ j, t j - 2 * ∑ i, ∑ j, min (s i) (t j) := by
  have e : ∑ i, ∑ j, 2 * max (s i) (t j) =
      2 * y * ∑ i, s i + 2 * q * ∑ j, t j - 2 * ∑ i, ∑ j, min (s i) (t j) := by
    have : ∀ i j, 2 * max (s i) (t j) = 2 * s i + 2 * t j - 2 * min (s i) (t j) := fun i j => by
      linarith [min_add_max (s i) (t j)]
    simp only [this, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [posWt, e]
  ring

theorem posWt' : PosWt := by
  intro n d q y s t hs ht
  have hb : BddAbove (Set.range fun i : Fin (q + 1) => psum s i.val - psum t i.val) := (Set.finite_range _).bddAbove
  refine ⟨?_, ?_, fun i hi => ?_⟩
  · rw [posWt_eq]
    have : 0 ≤ ∑ i, ∑ j, min (s i) (t j) :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => le_min (hs.2 i) (ht.2 j)
    linarith
  · have := le_ciSup hb 0
    refine le_trans (le_of_eq ?_) this
    simp [psum]
  · have := le_ciSup hb ⟨i, by omega⟩
    unfold viol
    linarith

theorem exists_initial {q : ℕ} (P : Fin q → Prop) (hP : ∀ i i', i ≤ i' → P i' → P i) :
    ∃ k ≤ q, ∀ i, P i ↔ i.val < k := by
  classical
  have hex : ∃ k, ∀ h : k < q, ¬ P ⟨k, h⟩ := ⟨q, fun h => absurd h (lt_irrefl q)⟩
  refine ⟨Nat.find hex, Nat.find_min' hex fun h => absurd h (lt_irrefl q), fun i => ⟨fun hi => ?_, fun hi => ?_⟩⟩
  · by_contra h
    have h' : Nat.find hex ≤ i.val := not_lt.1 h
    exact Nat.find_spec hex (h'.trans_lt i.isLt) (hP _ i h' hi)
  · have := Nat.find_min hex hi
    push Not at this
    exact this.2

theorem major_slack {q : ℕ} {s t : Fin q → ℝ} (hs : s ∈ Cone q) (ht : t ∈ Cone q) {δ : ℝ}
    (h : ∀ i ≤ q, psum s i ≤ psum t i + δ) :
    ∑ i, ∑ j, min (s i) (s j) - ∑ i, ∑ j, min (s i) (t j) ≤ ∑ j : Fin q, ((q : ℝ) - 1 - j.val) * t j + q * δ := by
  classical
  have h1 : ∑ i, ∑ j, min (s i) (s j) - ∑ i, ∑ j, min (s i) (t j) ≤
      ∑ j, ∑ i, ((if t j < s i then s i else 0) - if t j < s i then t j else 0) := by
    rw [Finset.sum_comm (f := fun j i => (if t j < s i then s i else 0) - if t j < s i then t j else 0),
      ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    have := min_le_left (s i) (s j)
    split_ifs with hij
    · rw [min_eq_right hij.le]; linarith
    · rw [min_eq_left (not_lt.1 hij)]; linarith
  have h2 : ∀ j, ∑ i, ((if t j < s i then s i else 0) - if t j < s i then t j else 0) ≤
      ∑ i, (if i < j then t i else 0) + δ := by
    intro j
    obtain ⟨k, hk, hP⟩ := exists_initial (fun i => t j < s i) fun i i' hi h' => h'.trans_le (hs.1 hi)
    have a1 := h k hk
    unfold psum at a1
    simp only [hP]
    rw [Finset.sum_sub_distrib]
    have a2 : ∑ i : Fin q, (if i.val < k then t i else 0) - ∑ i : Fin q, (if i.val < k then t j else 0) ≤
        ∑ i, (if i < j then t i else 0) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have := ht.2 i
      have := ht.2 j
      split_ifs with b1 b2 b2
      · linarith
      · linarith [ht.1 (not_lt.1 b2)]
      · linarith
      · linarith
    linarith
  refine h1.trans ((Finset.sum_le_sum fun j _ => h2 j).trans (le_of_eq ?_))
  rw [Finset.sum_add_distrib, Finset.sum_comm]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_filter, Finset.sum_const, Finset.filter_lt_eq_Ioi, Fin.card_Ioi, nsmul_eq_mul,
      Nat.cast_sub (by have := i.isLt; omega), Nat.cast_sub (by have := i.isLt; omega)]
    simp
  · simp

theorem sum_min_self {q : ℕ} {s : Fin q → ℝ} (hs : s ∈ Cone q) :
    ∑ i, ∑ j, min (s i) (s j) = ∑ i : Fin q, (2 * (i.val : ℝ) + 1) * s i := by
  have e : ∀ i j, min (s i) (s j) = (if j ≤ i then s i else 0) + if i < j then s j else 0 := fun i j => by
    rcases le_or_gt j i with h | h
    · rw [if_pos h, if_neg (not_lt.2 h), add_zero, min_eq_left (hs.1 h)]
    · rw [if_neg (not_le.2 h), if_pos h, zero_add, min_eq_right (hs.1 h.le)]
  simp only [e, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if i < j then s j else 0), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const, Finset.filter_ge_eq_Iic,
    Finset.filter_gt_eq_Iio, Fin.card_Iic, Fin.card_Iio, nsmul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

theorem exponent_bound_orthogonal_case : ExpSo := by
  intro n d q y Y hq hy hY hd
  refine ⟨d + q + 1, fun s hs t ht => ?_⟩
  obtain ⟨-, hδ, hps⟩ := posWt' n d q y s t hs ht
  set δ := viol s t
  let u : Fin q → ℝ := fun j => ext t j
  have hu : u ∈ Cone q := ⟨fun i j hij => ext_anti ht hij, fun j => ext_nonneg ht j⟩
  have hpu : ∀ k ≤ q, psum t k = psum u k := fun k hk => by
    unfold psum
    rw [sum_ext (Nat.le_add_left y q) t (fun j x => if j < k then x else 0) (by simp),
      sum_cut (Nat.le_add_right q y) (fun j => if j < k then ext t j else 0)]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> first | rfl | omega
  have h1 := major_slack hs hu (δ := δ) fun i hi => by rw [← hpu i hi]; exact hps i hi
  have h2 : ∑ i, ∑ j, min (s i) (u j) ≤ ∑ i, ∑ j, min (s i) (t j) := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [sum_ext (Nat.le_add_left y q) t (fun _ x => min (s i) x) (fun _ => min_eq_right (hs.2 i)),
      sum_cut (Nat.le_add_right q y) (fun j => min (s i) (ext t j))]
    refine Finset.sum_le_sum fun j _ => ?_
    split_ifs
    · exact le_rfl
    · exact le_min (hs.2 i) (ext_nonneg ht j)
  have h3 : ∑ i, s i ≤ ∑ j, u j + δ := by
    have := hps q le_rfl
    rw [hpu q le_rfl] at this
    simpa [psum] using this
  have hn : 2 * (Y : ℝ) + 2 ≤ n := by exact_mod_cast hY
  have hd' : 2 * (n : ℝ) ≤ d := by exact_mod_cast hd
  have hq' : (q : ℝ) ≤ Y := by exact_mod_cast hq
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  set c : ℝ := d / 2 - n + 1 / (4 * (q + 1)) with hc
  have hc1 : 1 / (4 * ((q : ℝ) + 1)) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hc2 : 0 ≤ 1 / (4 * ((q : ℝ) + 1)) := by positivity
  have h4 : ∑ j : Fin q, (c + ((q : ℝ) - 1 - j.val)) * u j ≤
      ∑ j : Fin y, (((d : ℝ) - 2 * j.val - 1) / 2 - n / 2 - 1 / 4) * t j := by
    rw [sum_ext (Nat.le_add_left y q) t (fun j x => (((d : ℝ) - 2 * j - 1) / 2 - n / 2 - 1 / 4) * x) (by simp),
      sum_cut (Nat.le_add_right q y) (fun j => (c + ((q : ℝ) - 1 - j)) * ext t j)]
    refine Finset.sum_le_sum fun j _ => ?_
    have a0 := ext_nonneg ht j
    split_ifs with hj
    · exact mul_le_mul_of_nonneg_right (by linarith) a0
    · by_cases hjy : j < y
      · have : (j : ℝ) + 1 ≤ Y := by exact_mod_cast (by omega : j + 1 ≤ Y)
        exact mul_nonneg (by linarith) a0
      · rw [ext, dite_eq_right hjy, mul_zero]
  have e1 : rho2 n s = n * ∑ i, s i - ∑ i, ∑ j, min (s i) (s j) := by
    rw [sum_min_self hs, rho2, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ j : Fin y, (((d : ℝ) - 2 * j.val - 1) / 2 - n / 2 - 1 / 4) * t j =
      rho2 d t / 2 - n / 2 * ∑ j, t j - (∑ j, t j) / 4 := by
    rw [rho2, Finset.sum_div, Finset.sum_div, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e3 : ∑ j : Fin q, (c + ((q : ℝ) - 1 - j.val)) * u j =
      c * ∑ j, u j + ∑ j : Fin q, ((q : ℝ) - 1 - j.val) * u j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e4 : (∑ i, s i) / (4 * ((q : ℝ) + 1)) = 1 / (4 * ((q : ℝ) + 1)) * ∑ i, s i := by ring
  have hc0 : 0 ≤ c := by linarith
  have h5 := mul_le_mul_of_nonneg_left h3 hc0
  have h6 : c * δ ≤ (d + 1) * δ := mul_le_mul_of_nonneg_right (by linarith [Nat.cast_nonneg (α := ℝ) n]) hδ
  have e5 : c * ∑ i, s i = (d / 2 - n) * ∑ i, s i + 1 / (4 * ((q : ℝ) + 1)) * ∑ i, s i := by rw [hc]; ring
  rw [posWt_eq, e1, e4]
  rw [e2, e3] at h4
  nlinarith

end PositivityTheory.ThKEst.Sq
end
end

noncomputable section

namespace PositivityTheory.ThKEst.Sq

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def TorBd (om : Rep σ X W) (fr : Frame σ X.J) (fr' : Frame σ W.J) (e : (Fin fr.r → ℝ) → (Fin fr'.r → ℝ) → ℝ)
    (Φ : (Fin n × Fin d → AF F) → ℂ) : Prop :=
  ∀ (Ω : Set (UA σ X.J)) (Ω' : Set (UA σ W.J)), IsCompact Ω → IsCompact Ω' → ∃ A : ℝ≥0, ∀ s ∈ Cone fr.r, ∀ t ∈ Cone fr'.r,
    ∀ κ ∈ Ω, ∀ κ' ∈ Ω', ‖theta om Φ (fr.a s * κ) (fr'.a t * κ')‖ₑ ≤ A * ENNReal.ofReal (Real.exp (e s t))

theorem pureA_mem' {κ : Type} [Fintype κ] (f : SInf F κ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB _) : pureA F f g ∈ schA F κ :=
  Submodule.subset_span ⟨f, g, hg, rfl⟩

theorem torBd_sum {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W} {r s r' s' : ℕ}
    (hP : IsPair B M χX χW om r s r' s') {fr : Frame σ X.J} {fr' : Frame σ W.J}
    {e : (Fin fr.r → ℝ) → (Fin fr'.r → ℝ) → ℝ} {ι : Type} (T : Finset ι) (Φ : ι → (Fin n × Fin d → AF F) → ℂ)
    (hΦ : ∀ i, Φ i ∈ schA F (Fin n × Fin d)) (h : ∀ i, TorBd om fr fr' e (Φ i)) : TorBd om fr fr' e (∑ i ∈ T, Φ i) := by
  classical
  have hpres : ∀ x, ∀ Ψ ∈ schA F (Fin n × Fin d), om x Ψ ∈ schA F (Fin n × Fin d) :=
    (IsUWeilPair.isUSplitting hP.weil).pres
  induction T using Finset.induction_on with
  | empty => intro Ω Ω' _ _; exact ⟨0, fun s _ t _ κ _ κ' _ => by simp [theta, thetaSum]⟩
  | insert a T ha ih =>
    intro Ω Ω' h1 h2
    obtain ⟨A, hA⟩ := h a Ω Ω' h1 h2
    obtain ⟨A', hA'⟩ := ih Ω Ω' h1 h2
    refine ⟨A + A', fun s hs t ht κ hκ κ' hκ' => ?_⟩
    rw [Finset.sum_insert ha, theta, map_add (f := _),
      thetaSum_add F (hpres _ _ (hΦ a)) (hpres _ _ (Submodule.sum_mem _ fun i _ => hΦ i)), ENNReal.coe_add, add_mul]
    exact (enorm_add_le _ _).trans (add_le_add (hA s hs t ht κ hκ κ' hκ') (hA' s hs t ht κ hκ κ' hκ'))

theorem torBd_pure (hC : LatCpt) {B : Base F E} {M : Model σ X W} {om : Rep σ X W} (hB : B.IsGood σ) (hX : EpsHerm σ X.J)
    (hW : EpsHerm σ W.J) {fr : Frame σ X.J} {fr' : Frame σ W.J} {𝓕 : Set ((Fin n × Fin d → Af F) → ℂ)}
    {S : Set (Matrix (Fin n) (Fin d) E)} (hS : SqBound B M om 𝓕 S) {e e₂ : (Fin fr.r → ℝ) → (Fin fr'.r → ℝ) → ℝ} {N : ℕ}
    (hT : ∀ C, IsCompact C → ∃ K : ℝ≥0, ∀ s ∈ Cone fr.r, ∀ t ∈ Cone fr'.r,
      latSum B.emb C N S (fr.a s) (fr'.a t) ≤ K * ENNReal.ofReal (Real.exp (e₂ s t)))
    (he : ∀ s ∈ Cone fr.r, ∀ t ∈ Cone fr'.r, e₂ s t ≤ 2 * e s t) (f : SInf F (Fin n × Fin d))
    {φ : (Fin n × Fin d → Af F) → ℂ} (hφ : φ ∈ 𝓕) : TorBd om fr fr' e (pureA F f φ) := by
  intro Ω Ω' h1 h2
  obtain ⟨p, C, -, hCc, hb⟩ := hS φ hφ N
  obtain ⟨C', K, hC', hK⟩ := hC F E σ hB.cm B.emb n d X.J W.J hX hW Ω Ω' h1 h2 C N hCc
  obtain ⟨K', hK'⟩ := hT C' hC'
  refine ⟨(p f).toNNReal * NNReal.sqrt (K * K'), fun s hs t ht κ hκ κ' hκ' => ?_⟩
  refine (ENNReal.pow_le_pow_left_iff two_ne_zero).1 ((hb f _ _).trans ?_)
  have e1 : ((NNReal.sqrt (K * K') : ℝ≥0) : ℝ≥0∞) ^ 2 = K * K' := by
    rw [← ENNReal.coe_pow, NNReal.sq_sqrt, ENNReal.coe_mul]
  have e2 : ENNReal.ofReal (Real.exp (e₂ s t)) ≤ ENNReal.ofReal (Real.exp (e s t)) ^ 2 := by
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by exact_mod_cast he s hs t ht))
  calc _ ≤ ENNReal.ofReal (p f) ^ 2 * (K * (K' * ENNReal.ofReal (Real.exp (e s t)) ^ 2)) := by
        refine mul_le_mul_right ((hK S _ _ κ hκ κ' hκ').trans (mul_le_mul_right ((hK' s hs t ht).trans ?_) _)) _
        exact mul_le_mul_right e2 _
    _ = _ := by
        rw [ENNReal.coe_mul, mul_pow, mul_pow, e1]
        simp only [ENNReal.ofReal, mul_assoc]

theorem square_integrable_of_torus_bound (hG : GrpTop) (hTh : ThetaBasic) {B : Base F E} {M : Model σ X W} {χX χW : Chr F E} {om : Rep σ X W}
    {r s r' s' : ℕ} (hP : IsPair B M χX χW om r s r' s') (hX : EpsHerm σ X.J) (hW : EpsHerm σ W.J) {fr : Frame σ X.J}
    {fr' : Frame σ W.J} (hI : SiegelInt fr) (hI' : SiegelInt fr') {U : (Fin fr.r → ℝ) → ℝ} {V : (Fin fr'.r → ℝ) → ℝ}
    (hUm : Measurable U) (hVm : Measurable V)
    (hU : ∫⁻ s in Cone fr.r, ENNReal.ofReal (Real.exp (U s)) *
      ENNReal.ofReal (Real.exp (-(Module.finrank ℚ E * rho2 n s))) < ⊤)
    (hV : ∫⁻ t in Cone fr'.r, ENNReal.ofReal (Real.exp (2 * V t)) *
      ENNReal.ofReal (Real.exp (-(Module.finrank ℚ E * rho2 d t))) < ⊤)
    {Φ : (Fin n × Fin d → AF F) → ℂ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) (hb : TorBd om fr fr' (fun s t => U s + V t) Φ)
    (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (ratU σ W.J) 𝓕 μ) :
    IntegrableOn (fun h => ‖M.I om Φ h‖ ^ 2) 𝓕 μ := by
  obtain ⟨lc, sc, -⟩ := hG F E σ hP.base.cm n X.J hX
  obtain ⟨lc', sc', -⟩ := hG F E σ hP.base.cm d W.J hW
  have : BorelSpace (UA σ X.J) := ⟨rfl⟩
  have : BorelSpace (UA σ W.J) := ⟨rfl⟩
  have := hP.good.haar
  have : SigmaCompactSpace (UA σ X.J) := sigmaCompactSpace_of_locallyCompact_secondCountable
  have : SigmaFinite M.μ := MeasureTheory.sigmaFinite_of_locallyFinite
  have : SFinite (M.μ.restrict M.dom) := @MeasureTheory.instSFiniteOfSigmaFinite _ _ _ (MeasureTheory.Restrict.sigmaFinite M.μ M.dom)
  obtain ⟨hcont, hinv, -⟩ := (hTh F E σ B n d X W M χX χW om r s r' s' hP).1 Φ hΦ
  obtain ⟨K, Ω, hK, hΩ, H⟩ := hI M.μ M.dom hP.good.haar hP.good.dom
  obtain ⟨K', Ω', hK', hΩ', H'⟩ := hI' μ 𝓕 hμ h𝓕
  obtain ⟨A, hA⟩ := hb Ω Ω' hΩ hΩ'
  have hsm : StronglyMeasurable (M.I om Φ) :=
    StronglyMeasurable.integral_prod_left (μ := M.μ.restrict M.dom) (f := fun g h => theta om Φ g h)
      hcont.stronglyMeasurable
  set IU := ∫⁻ s in Cone fr.r, ENNReal.ofReal (Real.exp (U s)) *
      ENNReal.ofReal (Real.exp (-(Module.finrank ℚ E * rho2 n s)))
  have h1 : ∀ t ∈ Cone fr'.r, ∀ κ' ∈ Ω', ‖M.I om Φ (fr'.a t * κ')‖ₑ ≤ (K * A * IU) * ENNReal.ofReal (Real.exp (V t)) := by
    intro t ht κ' hκ'
    have a1 := H (fun s => (A * ENNReal.ofReal (Real.exp (V t))) * ENNReal.ofReal (Real.exp (U s)))
      (measurable_const.mul (Real.measurable_exp.comp hUm).ennreal_ofReal)
      (fun g => ‖theta om Φ g (fr'.a t * κ')‖ₑ) (hcont.comp (continuous_id.prodMk continuous_const)).measurable.enorm
      (fun γ hγ g => by have := hinv γ hγ 1 (one_mem _) g (fr'.a t * κ'); rw [one_mul] at this; simp only [this])
      (fun s hs κ hκ => (hA s hs t ht κ hκ κ' hκ').trans (le_of_eq (by
        rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]; ring)))
    refine (enorm_integral_le_lintegral_enorm _).trans (a1.trans (le_of_eq ?_))
    simp only [mul_assoc]
    rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_comm IU]
  have hc : K * A * IU ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.mul_ne_top hK.ne ENNReal.coe_ne_top) hU.ne
  have h2 := H' (fun t => (K * A * IU) ^ 2 * ENNReal.ofReal (Real.exp (2 * V t)))
    (measurable_const.mul (Real.measurable_exp.comp (hVm.const_mul 2)).ennreal_ofReal)
    (fun h => ‖M.I om Φ h‖ₑ ^ 2) (hsm.measurable.enorm.pow_const 2)
    (fun γ hγ h => by
      have : M.I om Φ (γ * h) = M.I om Φ h := by
        unfold Model.I
        congr 1
        funext g
        have := hinv 1 (one_mem _) γ hγ g h
        rwa [one_mul] at this
      simp only [this])
    (fun t ht κ' hκ' => (pow_le_pow_left' (h1 t ht κ' hκ') 2).trans (le_of_eq (by
      rw [mul_pow _ (ENNReal.ofReal _), ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]; norm_num)))
  refine ⟨(hsm.norm.pow 2).aestronglyMeasurable, ?_⟩
  have e : ∀ h, ‖‖M.I om Φ h‖ ^ 2‖ₑ = ‖M.I om Φ h‖ₑ ^ 2 := fun h => by rw [enorm_pow, enorm_norm]
  unfold HasFiniteIntegral
  simp only [e]
  refine h2.trans_lt (ENNReal.mul_lt_top hK' ?_)
  simp only [mul_assoc ((K * A * IU) ^ 2)]
  rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top hc)]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top hc.lt_top) hV

theorem finrank_pos' (E : Type) [Field E] [NumberField E] : (0 : ℝ) < Module.finrank ℚ E := by
  exact_mod_cast Module.finrank_pos

theorem square_integrable_of_lattice_torus (hG : GrpTop) (hE : EpsOf) (hS : SiegelAll) (hTh : ThetaBasic) (hq : SqAll) (hF : SoFin) (hC : LatCpt)
    (hT : LatTor) : SquareIntegrableWeilRange := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP h1 h2 μ 𝓕 hμ h𝓕 Φ hΦ
  obtain ⟨hX, -, hr⟩ := hE F E σ B hP.base n X r s (Or.inl hP.herm)
  obtain ⟨hW, -, hr'⟩ := hE F E σ B hP.base d W r' s' (Or.inr hP.skew)
  obtain ⟨fr, hf, -, -, hI, -⟩ := hS F E σ hP.base.cm n X.J hX
  obtain ⟨fr', hf', -, -, hI', -⟩ := hS F E σ hP.base.cm d W.J hW
  have hD := finrank_pos' E
  obtain ⟨a1, a2⟩ := square_integrable_integral_holds n d fr.r fr'.r _ hD (by have := hr fr hf; omega) (by have := hr' fr' hf'; omega)
  obtain ⟨N, hN⟩ := hT F E σ hP.base.cm B.emb n d X.J W.J hX hW fr fr' hf hf'
  obtain ⟨m, f, φ, hφ, rfl⟩ := (hF F E σ B n d X W M χX χW om r s r' s' hP).2.1 Φ hΦ
  refine square_integrable_of_torus_bound hG hTh hP hX hW hI hI' (U := fun s => Module.finrank ℚ E * (d / 2 * ∑ i, s i))
    (V := fun t => Module.finrank ℚ E * (n * ∑ j, t j) / 2) (by fun_prop) (by fun_prop) a1 ?_ hΦ ?_ μ 𝓕 hμ h𝓕
  · simpa only [mul_div_cancel₀ _ (two_ne_zero (α := ℝ))] using a2
  · refine torBd_sum hP _ _ (fun i => pureA_mem' _ (hφ i)) fun i =>
      torBd_pure hC hP.base hX hW (hq F E σ B n d X W M χX χW om r s r' s' hP) hN (fun s hs t ht => ?_) _ (hφ i)
    have := mul_le_mul_of_nonneg_left (posWt' n d _ _ s t hs ht).1 hD.le
    linarith

theorem exp_cancel {r : ℕ} (c : ℝ) (hc : 0 < c) (ρ : (Fin r → ℝ) → ℝ) :
    ∫⁻ t in Cone r, ENNReal.ofReal (Real.exp (ρ t - c * ∑ i, t i)) * ENNReal.ofReal (Real.exp (-ρ t)) < ⊤ := by
  refine lt_of_eq_of_lt (lintegral_congr fun t => ?_) (coneAff r (-c) 0 fun k _ _ => by simpa using hc)
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  simp only [zero_mul, add_zero, ← Finset.mul_sum]
  ring

theorem square_integrable_orthogonal_case (hG : GrpTop) (hE : EpsOf) (hS : SiegelAll) (hTh : ThetaBasic) (hq : SqSo) (hF : SoFin) (hC : LatCpt)
    (hT : LatFull) : SquareIntegrableSiegelSet := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP h1 ⟨Y, y1, y2, y3⟩ μ 𝓕 hμ h𝓕 Φ hΦ
  obtain ⟨hX, -, hr⟩ := hE F E σ B hP.base n X r s (Or.inl hP.herm)
  obtain ⟨hW, -, hr'⟩ := hE F E σ B hP.base d W r' s' (Or.inr hP.skew)
  obtain ⟨fr, hf, -, -, hI, -⟩ := hS F E σ hP.base.cm n X.J hX
  obtain ⟨fr', hf', -, -, hI', -⟩ := hS F E σ hP.base.cm d W.J hW
  have hD := finrank_pos' E
  set D : ℝ := ((Module.finrank ℚ E : ℕ) : ℝ)
  obtain ⟨m₀, hm₀⟩ := exponent_bound_orthogonal_case n d fr.r fr'.r Y ((hr fr hf).trans y1) ((hr' fr' hf').trans y2) y3 h1
  obtain ⟨N, hN⟩ := hT F E σ hP.base.cm B.emb n d X.J W.J hX hW fr fr' hf hf' ⌈2 * D * m₀⌉₊
  obtain ⟨b1, -, b3, -⟩ := hF F E σ B n d X W M χX χW om r s r' s' hP
  have hΦ' := b3 Φ hΦ
  obtain ⟨m, f, φ, hφ, rfl⟩ := b1 Φ hΦ
  refine square_integrable_of_torus_bound hG hTh hP hX hW hI hI' (U := fun s => D * rho2 n s - D / (4 * (fr.r + 1)) * ∑ i, s i)
    (V := fun t => (D * rho2 d t - D / 2 * ∑ j, t j) / 2) (by unfold rho2; fun_prop) (by unfold rho2; fun_prop)
    (exp_cancel _ (by positivity) _) ?_ hΦ' ?_ μ 𝓕 hμ h𝓕
  · simpa only [mul_div_cancel₀ _ (two_ne_zero (α := ℝ))] using exp_cancel (D / 2) (by positivity) fun t => D * rho2 d t
  · refine torBd_sum hP _ _ (fun i => pureA_mem' _ (hφ i).1) fun i =>
      torBd_pure hC hP.base hX hW (hq F E σ B n d X W M χX χW om r s r' s' hP) hN (fun s hs t ht => ?_) _ (hφ i)
    have a1 := mul_le_mul_of_nonneg_left (hm₀ s hs t ht) hD.le
    have a2 := mul_le_mul_of_nonneg_right (Nat.le_ceil (2 * D * m₀)) (posWt' n d _ _ s t hs ht).2.1
    have e : D * ((∑ i, s i) / (4 * ((fr.r : ℝ) + 1))) = D / (4 * (fr.r + 1)) * ∑ i, s i := by ring
    nlinarith

omit [NumberField E] in
theorem polData_le {B : Base F E} {M : Model σ X W} (hM : M.IsGood B.ψ) : PolData B M ≤ schA F (Fin n × Fin d) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, -, φ, h1, h2, rfl⟩
  have h3 := (h2.and hM.std).mono fun _ h => h.1.trans h.2
  exact Submodule.subset_span ⟨f, _, ⟨isLocallyConstant_finprod_evalV φ h1 h3,
    GlobalTheory.AdelicCoordSupport.hasCompactSupport_finprod φ h1 h3⟩, rfl⟩

theorem sqInt_of (hT : TriplePair) (h1 : SquareIntegrableWeilRange) (h2 : SquareIntegrableSiegelSet) : SqInt := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr μ 𝓕 hμ h𝓕
  obtain ⟨p1, p2, p3⟩ := hT F E σ B a a' G X om om' hTr
  have g1 := hTr.geo.lt
  have g2 := hTr.geo.aBig
  exact ⟨fun Φ hΦ => h1 F E σ B _ _ _ _ _ _ _ om _ _ _ _ p1 (Or.inl p3) (Or.inr (by omega)) μ 𝓕 hμ h𝓕 Φ
      (polData_le hTr.geo.hM hΦ),
    fun Φ hΦ => h2 F E σ B _ _ _ _ _ _ _ om' _ _ _ _ p2 (by omega) ⟨G.p + G.q, by omega, by omega, g2⟩ μ 𝓕 hμ h𝓕 Φ hΦ.2⟩

end PositivityTheory.ThKEst.Sq
end
end

noncomputable section

namespace PositivityTheory.ThKEst.Sq

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hecke_div {χ₁ χ₂ : Chr F E} (h₁ : IsHecke F E χ₁) (h₂ : IsHecke F E χ₂) : IsHecke F E (χ₁ / χ₂) :=
  ⟨h₁.1.div' h₂.1, fun x => by rw [MonoidHom.div_apply, h₁.2 x, h₂.2 x, div_one]⟩

theorem res_div {K : Subgroup (AF F)ˣ} {χ₁ χ₂ : Chr F E} {a b n : ℕ} (h₁ : ResEtaPow K χ₁ a) (h₂ : ResEtaPow K χ₂ b)
    (he : Even (a + b)) (hn : Even n) : ResEtaPow K (χ₁ / χ₂) n := by
  intro x
  have e : (-1 : ℂ) ^ a = (-1) ^ b := neg_one_pow_congr (Nat.even_add.1 he)
  rw [MonoidHom.div_apply, Circle.coe_div, h₁ x, h₂ x, hn.neg_one_pow, e, ite_self, div_self]
  split_ifs <;> simp

theorem triplePair_holds : TriplePair := by
  intro F E _ _ _ _ _ σ B a a' G X om om' h
  have g := h.geo.eBig
  exact ⟨⟨h.base, h.geo.hV, h.geo.hW, h.geo.hM, h.chars.heckeβ, hecke_div h.chars.heckeβ h.chars.heckeα, h.chars.resβ,
      res_div h.chars.resβ h.chars.resα h.geo.even h.geo.even, h.weil⟩,
    ⟨h.base, h.geo.hV', h.geo.hW, h.geo.hM', h.chars.heckeα, hecke_div h.chars.heckeα h.chars.heckeβ, h.chars.resα,
      res_div h.chars.resα h.chars.resβ (add_comm a a' ▸ h.geo.even) h.geo.even, h.weil'⟩, by omega⟩

theorem sqInt_of_leaves (hTh : ThetaBasic) (hG : GrpTop) (hE : EpsOf) (hS : SiegelAll) (hA : SqAll) (hO : SqSo) (hF : SoFin)
    (hC : LatCpt) (hT : LatTor) (hL : LatFull) : SqInt :=
  sqInt_of triplePair_holds (square_integrable_of_lattice_torus hG hE hS hTh hA hF hC hT) (square_integrable_orthogonal_case hG hE hS hTh hO hF hC hL)

end PositivityTheory.ThKEst.Sq
