module

public import Formalism.PieriBlockIdeals.PieriColumnMinors.LpcDpartCommEps

@[expose] public section

section -- merged from Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightSuccessive
namespace Formalism.CohomologicalDescent.LP

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem casimir_central' : CasCentral := by
  intro K N q _ _ _ T hgl c d
  have e : ∀ b b', T b b' * T b' b * T c d - T c d * (T b b' * T b' b) =
      ((if b = c then T b b' * T b' d else 0) - (if d = b' then T b b' * T c b else 0)) +
      ((if b' = c then T b d * T b' b else 0) - (if d = b then T c b' * T b' b else 0)) := by
    intro b b'
    have h1 := hgl b' b c d
    have h2 := hgl b b' c d
    calc T b b' * T b' b * T c d - T c d * (T b b' * T b' b)
        = T b b' * (T b' b * T c d - T c d * T b' b) + (T b b' * T c d - T c d * T b b') * T b' b := by
          noncomm_ring
      _ = _ := by
          rw [h1, h2]
          simp only [mul_sub, sub_mul, mul_ite, ite_mul, mul_zero, zero_mul]
  show casOp T * T c d = T c d * casOp T
  rw [← sub_eq_zero]
  unfold casOp
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [Finset.sum_mul, Finset.mul_sum]
  simp only [← Finset.sum_sub_distrib, e]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have s1 : ∑ b, ∑ b', (if b = c then T b b' * T b' d else 0) = ∑ b', T c b' * T b' d := by
    rw [Finset.sum_eq_single c]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  have s2 : ∑ b, ∑ b', (if d = b' then T b b' * T c b else 0) = ∑ b, T b d * T c b := by
    simp [Finset.sum_ite_eq]
  have s3 : ∑ b, ∑ b', (if b' = c then T b d * T b' b else 0) = ∑ b, T b d * T c b := by
    simp [Finset.sum_ite_eq']
  have s4 : ∑ b, ∑ b', (if d = b then T c b' * T b' b else 0) = ∑ b', T c b' * T b' d := by
    rw [Finset.sum_eq_single d]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [s1, s2, s3, s4]
  abel

theorem highest_weight_successive : StepHW := by
  intro K N q _ _ _ T ε hmul hone hcomm z μ hz hw
  classical
  have hex : ∃ b, ε b b z ≠ 0 := by
    by_contra h
    push_neg at h
    apply hz
    calc z = (∑ a, ε a a) z := by rw [hone]; rfl
      _ = ∑ a, ε a a z := LinearMap.sum_apply _ _ _
      _ = 0 := Finset.sum_eq_zero fun a _ => h a
  obtain ⟨b0, hb0⟩ := hex
  obtain ⟨b, hbS, hmax⟩ := (Finset.univ.filter (fun a => ε a a z ≠ 0)).exists_max_image id
    ⟨b0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb0⟩⟩
  have hbz : ε b b z ≠ 0 := (Finset.mem_filter.mp hbS).2
  have hzero : ∀ c, b < c → ε c c z = 0 := fun c hc => by
    by_contra h
    have := hmax c (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    exact absurd hc (not_lt.mpr this)
  have hprod : ∀ a c d e (w : N), ε a c (ε d e w) = if c = d then ε a e w else 0 := by
    intro a c d e w
    rw [← Module.End.mul_apply, hmul]
    split_ifs <;> rfl
  refine ⟨b, hbz, ?_, ?_⟩
  · intro a c hac
    have h1 : T a c z = -(ε a c z) := by
      have := hw.1 a c hac
      rw [LinearMap.add_apply] at this
      exact eq_neg_of_add_eq_zero_left this
    have hcm : T a c (ε b b z) = ε b b (T a c z) := LinearMap.congr_fun (hcomm a c b b).eq z
    rw [hcm, h1, map_neg, hprod]
    split_ifs with hba
    · subst hba
      have h3 : ε b c z = ε b c (ε c c z) := by rw [hprod, if_pos rfl]
      rw [h3, hzero c hac, map_zero, neg_zero]
    · rw [neg_zero]
  · intro a
    have h1 : T a a z = μ a • z - ε a a z := by
      have := hw.2 a
      rw [LinearMap.add_apply] at this
      exact eq_sub_of_add_eq this
    have hcm : T a a (ε b b z) = ε b b (T a a z) := LinearMap.congr_fun (hcomm a a b b).eq z
    rw [hcm, h1, map_sub, map_smul, hprod]
    by_cases hab : a = b
    · subst hab
      simp [sub_smul]
    · rw [if_neg (Ne.symm hab)]
      simp [Pi.single_apply, hab]

section Tower

variable {K N : Type} {q : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup N] [Module K N]

theorem lp_stab_iSup {ι : Sort*} {T : Fin q → Fin q → Module.End K N} (S : ι → Submodule K N) (h : ∀ i, Stab T (S i)) :
    Stab T (⨆ i, S i) := by
  intro a b x hx
  exact Submodule.iSup_induction S (motive := fun x => T a b x ∈ ⨆ i, S i) hx
    (fun i y hy => Submodule.mem_iSup_of_mem i (h i a b y hy)) (by simp)
    (fun y z hy hz => by rw [map_add (f := _)]; exact Submodule.add_mem _ hy hz)

def PathTo (lam2 : Fin q → ℕ) (j : ℕ) (κ : ℕ → Fin q → ℕ) : Prop :=
  κ 0 = lam2 ∧ (∀ i < j, ∃ ρ, κ (i + 1) = κ i + Pi.single ρ 1) ∧ ∀ i ≤ j, Antitone (κ i)

def Eig (D : ℕ → Fin q → Fin q → Module.End K N) (j : ℕ) (κ : ℕ → Fin q → ℕ) : Submodule K N :=
  ⨅ i : ℕ, ⨅ _ : i ≤ j, Module.End.eigenspace (casOp (D i)) ((casVal (κ i) : ℤ) : K)

theorem lp_mem_Eig (D : ℕ → Fin q → Fin q → Module.End K N) (j : ℕ) (κ : ℕ → Fin q → ℕ) (z : N) :
    z ∈ Eig D j κ ↔ ∀ i ≤ j, casOp (D i) z = ((casVal (κ i) : ℤ) : K) • z := by
  unfold Eig
  simp only [Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

theorem lp_casVal_step (κ : Fin q → ℕ) (ρ : Fin q) :
    casVal (κ + Pi.single ρ 1) = casVal κ + (q : ℤ) + 2 * ((κ ρ : ℤ) - (ρ.val : ℤ)) := by
  unfold casVal
  have key : ∀ b : Fin q, ((((κ + Pi.single ρ 1 : Fin q → ℕ) b : ℕ)) : ℤ) *
      ((((κ + Pi.single ρ 1 : Fin q → ℕ) b : ℕ) : ℤ) + (q : ℤ) - 1 - 2 * (b.val : ℤ)) =
      (κ b : ℤ) * ((κ b : ℤ) + (q : ℤ) - 1 - 2 * (b.val : ℤ)) +
        (if b = ρ then (q : ℤ) + 2 * ((κ ρ : ℤ) - (ρ.val : ℤ)) else 0) := by
    intro b
    simp only [Pi.add_apply, Pi.single_apply]
    split_ifs with h
    · subst h
      push_cast
      ring
    · simp
  rw [Finset.sum_congr rfl (fun b _ => key b), Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  ring

theorem lp_content_inj (κ : Fin q → ℕ) (hκ : Antitone κ) (b ρ : Fin q)
    (h : casVal (κ + Pi.single b 1) = casVal (κ + Pi.single ρ 1)) : b = ρ := by
  rw [lp_casVal_step, lp_casVal_step] at h
  have h' : (κ b : ℤ) - (b.val : ℤ) = (κ ρ : ℤ) - (ρ.val : ℤ) := by linarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := hκ hlt.le
    have hv : b.val < ρ.val := hlt
    omega
  · have h1 := hκ hlt.le
    have hv : ρ.val < b.val := hlt
    omega

theorem lp_hw_cas (hDom : HWDominant) {T : Fin q → Fin q → Module.End K N} {B : LinearMap.BilinForm K N} (hF : FormMod T B)
    (κ : Fin q → ℕ) (z : N) (hz : z ≠ 0) (hw : IsHW T (fun b => (κ b : K)) z) :
    Antitone κ ∧ casOp T z = ((casVal κ : ℤ) : K) • z := by
  obtain ⟨hup, hdiag⟩ := hw
  have hdiag' : ∀ a, T a a z = (κ a : K) • z := hdiag
  refine ⟨?_, ?_⟩
  · intro a b hab
    rcases eq_or_lt_of_le hab with h | h
    · rw [h]
    · have := hDom K N q T B hF z (fun b => (κ b : K)) hz ⟨hup, hdiag⟩ a b h
      exact_mod_cast this
  · have hgl := hF.gl
    obtain ⟨c, hc⟩ : ∃ c : Fin q → Fin q → ℤ, ∀ b b', c b b' =
        (if b = b' then (κ b : ℤ) * κ b else 0) + (if b < b' then (κ b : ℤ) else 0) -
          (if b < b' then (κ b' : ℤ) else 0) := ⟨_, fun _ _ => rfl⟩
    have hterm : ∀ b b', (T b b' * T b' b) z = ((c b b' : ℤ) : K) • z := by
      intro b b'
      rw [hc]
      rcases lt_trichotomy b b' with h | h | h
      · have hgl' := hgl b b' b' b
        rw [if_pos rfl, if_pos rfl] at hgl'
        have hA : T b b' * T b' b = T b' b * T b b' + (T b b - T b' b') := by rw [← hgl']; abel
        rw [hA, LinearMap.add_apply, Module.End.mul_apply, hup b b' h, map_zero, zero_add,
          LinearMap.sub_apply, hdiag', hdiag', ← sub_smul, if_neg (ne_of_lt h), if_pos h, if_pos h]
        congr 1
        push_cast
        ring
      · subst h
        rw [Module.End.mul_apply, hdiag', map_smul, hdiag', smul_smul, if_pos rfl,
          if_neg (lt_irrefl _)]
        congr 1
        push_cast
        ring
      · rw [Module.End.mul_apply, hup b' b h, map_zero, if_neg (ne_of_gt h),
          if_neg (not_lt.mpr h.le), if_neg (not_lt.mpr h.le)]
        simp
    have hIoi : ∀ b : Fin q, (∑ b' : Fin q, if b < b' then (1 : ℤ) else 0) = (q : ℤ) - 1 - (b.val : ℤ) := by
      intro b
      rw [Finset.sum_boole, Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
      have := b.isLt
      omega
    have hIio : ∀ b' : Fin q, (∑ b : Fin q, if b < b' then (1 : ℤ) else 0) = (b'.val : ℤ) := by
      intro b'
      rw [Finset.sum_boole, Finset.filter_gt_eq_Iio, Fin.card_Iio]
    have t1 : ∑ b : Fin q, ∑ b' : Fin q, (if b = b' then (κ b : ℤ) * κ b else 0) =
        ∑ b, (κ b : ℤ) * κ b := by
      simp [Finset.sum_ite_eq]
    have t2 : ∑ b : Fin q, ∑ b' : Fin q, (if b < b' then (κ b : ℤ) else 0) =
        ∑ b, (κ b : ℤ) * ((q : ℤ) - 1 - (b.val : ℤ)) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← hIoi b, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b' _ => ?_
      split_ifs <;> simp
    have t3 : ∑ b : Fin q, ∑ b' : Fin q, (if b < b' then (κ b' : ℤ) else 0) =
        ∑ b', (κ b' : ℤ) * (b'.val : ℤ) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b' _ => ?_
      rw [← hIio b', Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> simp
    have hsum : ∑ b, ∑ b', c b b' = casVal κ := by
      simp only [hc, Finset.sum_add_distrib, Finset.sum_sub_distrib]
      rw [t1, t2, t3]
      unfold casVal
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    unfold casOp
    simp only [LinearMap.sum_apply, hterm, ← Finset.sum_smul]
    congr 1
    exact_mod_cast hsum

variable {n : ℕ} {D ε : ℕ → Fin q → Fin q → Module.End K N} {B : LinearMap.BilinForm K N}

theorem lp_cas_eps (H : Tower n D ε B) (i j : ℕ) (hij : i ≤ j) (hj : j < n) (c d : Fin q) :
    Commute (casOp (D i)) (ε j c d) := by
  unfold casOp
  refine Commute.sum_left _ _ _ fun b _ => Commute.sum_left _ _ _ fun b' _ => ?_
  exact (H.comm i j hij hj b b' c d).mul_left (H.comm i j hij hj b' b c d)

theorem lp_cas_D (H : Tower n D ε B) (i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) (c d : Fin q) :
    Commute (casOp (D i)) (D j c d) := by
  induction j, hij using Nat.le_induction generalizing c d with
  | base => exact casimir_central' K N q (D i) (H.form i hj).gl c d
  | succ j hij' ih =>
    rw [H.step j (by omega) c d]
    exact (ih (by omega) c d).add_right (lp_cas_eps H i j hij' (by omega) c d)

theorem lp_Eig_of_comm (j : ℕ) (κ : ℕ → Fin q → ℕ) (X : Module.End K N) (hX : ∀ i ≤ j, Commute (casOp (D i)) X)
    (z : N) (hz : z ∈ Eig D j κ) : X z ∈ Eig D j κ := by
  rw [lp_mem_Eig] at hz ⊢
  intro i hi
  rw [← Module.End.mul_apply, (hX i hi).eq, Module.End.mul_apply, hz i hi, map_smul]

theorem lp_Eig_stab (H : Tower n D ε B) (j j' : ℕ) (hjj : j ≤ j') (hj : j' ≤ n) (κ : ℕ → Fin q → ℕ) :
    Stab (D j') (Eig D j κ) := by
  intro a b x hx
  exact lp_Eig_of_comm j κ (D j' a b) (fun i hi => lp_cas_D H i j' (le_trans hi hjj) hj a b) x hx

theorem lp_key (hDom : HWDominant) (H : Tower n D ε B) (j : ℕ) (hj : j < n) (κ : ℕ → Fin q → ℕ)
    (hb : ∀ z ∈ Eig D j κ, ∀ μ : Fin q → K, z ≠ 0 → IsHW (D j) μ z → μ = fun b => (κ j b : K))
    (z : N) (hz : z ∈ Eig D j κ) (hz0 : z ≠ 0) (μ : Fin q → K) (hw : IsHW (D (j + 1)) μ z) :
    ∃ b, (μ = fun a => ((κ j + Pi.single b 1 : Fin q → ℕ) a : K)) ∧ Antitone (κ j + Pi.single b 1) ∧
      casOp (D (j + 1)) z = ((casVal (κ j + Pi.single b 1) : ℤ) : K) • z := by
  have hw' : IsHW (fun a b => D j a b + ε j a b) μ z := by
    have e : (fun a b => D j a b + ε j a b) = D (j + 1) := by
      funext a b
      exact (H.step j hj a b).symm
    rw [e]
    exact hw
  obtain ⟨b, hbz, hhw⟩ := highest_weight_successive K N q (D j) (ε j) (H.unit_mul j hj) (H.unit_one j hj)
    (fun a b c d => H.comm j j le_rfl hj a b c d) z μ hz0 hw'
  have hmem : ε j b b z ∈ Eig D j κ :=
    lp_Eig_of_comm j κ (ε j b b) (fun i hi => lp_cas_eps H i j hi hj b b) z hz
  have hμ := hb (ε j b b z) hmem (μ - Pi.single b 1) hbz hhw
  have hμ' : μ = fun a => ((κ j + Pi.single b 1 : Fin q → ℕ) a : K) := by
    funext a
    have h1 := congrFun hμ a
    simp only [Pi.sub_apply] at h1
    simp only [Pi.add_apply, Nat.cast_add]
    rw [Pi.single_apply] at h1 ⊢
    split_ifs at h1 ⊢ <;> push_cast <;> linarith
  have hw2 : IsHW (D (j + 1)) (fun a => ((κ j + Pi.single b 1 : Fin q → ℕ) a : K)) z := by
    rw [← hμ']
    exact hw
  obtain ⟨hanti, hcas⟩ := lp_hw_cas hDom (H.form (j + 1) (by omega)) (κ j + Pi.single b 1) z hz0 hw2
  exact ⟨b, hμ', hanti, hcas⟩

theorem lp_Eig_mono (j : ℕ) (κ : ℕ → Fin q → ℕ) : Eig D (j + 1) κ ≤ Eig D j κ := by
  intro z hz
  rw [lp_mem_Eig] at hz ⊢
  exact fun i hi => hz i (by omega)

theorem lp_claim [FiniteDimensional K N] (hCR : CompleteRed) (hDom : HWDominant) (H : Tower n D ε B) (lam2 : Fin q → ℕ)
    (h0 : ∀ (v : N) (μ : Fin q → K), v ≠ 0 → IsHW (D 0) μ v → μ = fun b => (lam2 b : K)) (j : ℕ) (hj : j ≤ n) :
    (⨆ κ, ⨆ _ : PathTo lam2 j κ, Eig D j κ) = ⊤ ∧
      ∀ κ, PathTo lam2 j κ → ∀ z ∈ Eig D j κ, ∀ μ : Fin q → K, z ≠ 0 → IsHW (D j) μ z → μ = fun b => (κ j b : K) := by
  induction j with
  | zero =>
    refine ⟨?_, ?_⟩
    · by_cases hanti : Antitone lam2
      · have hpath : PathTo lam2 0 (fun _ => lam2) :=
          ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _), fun i _ => hanti⟩
        apply eq_top_iff.mpr
        refine le_trans ?_ (le_iSup₂_of_le (fun _ => lam2) hpath le_rfl)
        refine hCR K N q (D 0) B (H.form 0 (Nat.zero_le _)) ⊤ (Eig D 0 (fun _ => lam2))
          (fun a b x _ => trivial) (lp_Eig_stab H 0 0 le_rfl (Nat.zero_le _) _) ?_
        intro v _ μ hv
        by_cases hv0 : v = 0
        · rw [hv0]
          exact Submodule.zero_mem _
        · have hμ := h0 v μ hv0 hv
          rw [hμ] at hv
          obtain ⟨-, hcas⟩ := lp_hw_cas hDom (H.form 0 (Nat.zero_le _)) lam2 v hv0 hv
          rw [lp_mem_Eig]
          intro i hi
          have hi0 : i = 0 := by omega
          subst hi0
          exact hcas
      · have hbot : (⊤ : Submodule K N) ≤ ⊥ := by
          refine hCR K N q (D 0) B (H.form 0 (Nat.zero_le _)) ⊤ ⊥ (fun a b x _ => trivial)
            (fun a b x hx => by rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero]) ?_
          intro v _ μ hv
          by_contra hne
          have hv0 : v ≠ 0 := fun h => hne (by rw [h]; exact Submodule.zero_mem _)
          apply hanti
          have hμ := h0 v μ hv0 hv
          rw [hμ] at hv
          exact (lp_hw_cas hDom (H.form 0 (Nat.zero_le _)) lam2 v hv0 hv).1
        exact eq_top_iff.mpr (le_trans hbot bot_le)
    · intro κ hκ z _ μ hz0 hzw
      rw [h0 z μ hz0 hzw, hκ.1]
  | succ j ih =>
    obtain ⟨ihtop, ihuniq⟩ := ih (by omega)
    refine ⟨?_, ?_⟩
    · apply eq_top_iff.mpr
      rw [← ihtop]
      refine iSup₂_le fun κ hκ => ?_
      refine hCR K N q (D (j + 1)) B (H.form (j + 1) hj) (Eig D j κ) _
        (lp_Eig_stab H j (j + 1) (by omega) hj κ)
        (lp_stab_iSup _ fun κ' => lp_stab_iSup _ fun _ => lp_Eig_stab H (j + 1) (j + 1) le_rfl hj κ') ?_
      intro v hv μ hvw
      by_cases hv0 : v = 0
      · rw [hv0]
        exact Submodule.zero_mem _
      obtain ⟨b, hμ, hanti, hcas⟩ := lp_key hDom H j (by omega) κ (ihuniq κ hκ) v hv hv0 μ hvw
      obtain ⟨κ', hκ'⟩ : ∃ κ' : ℕ → Fin q → ℕ,
          ∀ i, κ' i = if i = j + 1 then κ j + Pi.single b 1 else κ i := ⟨_, fun _ => rfl⟩
      have hκ'le : ∀ i ≤ j, κ' i = κ i := fun i hi => by rw [hκ', if_neg (by omega)]
      have hκ'top : κ' (j + 1) = κ j + Pi.single b 1 := by rw [hκ', if_pos rfl]
      have hpath : PathTo lam2 (j + 1) κ' := by
        refine ⟨by rw [hκ'le 0 (Nat.zero_le _)]; exact hκ.1, ?_, ?_⟩
        · intro i hi
          by_cases hij : i = j
          · subst hij
            exact ⟨b, by rw [hκ'top, hκ'le i le_rfl]⟩
          · obtain ⟨ρ, hρ⟩ := hκ.2.1 i (by omega)
            exact ⟨ρ, by rw [hκ'le (i + 1) (by omega), hκ'le i (by omega), hρ]⟩
        · intro i hi
          by_cases hij : i = j + 1
          · subst hij
            rw [hκ'top]
            exact hanti
          · rw [hκ'le i (by omega)]
            exact hκ.2.2 i (by omega)
      have hvE : v ∈ Eig D (j + 1) κ' := by
        rw [lp_mem_Eig]
        intro i hi
        by_cases hij : i = j + 1
        · subst hij
          rw [hκ'top]
          exact hcas
        · rw [hκ'le i (by omega)]
          exact (lp_mem_Eig D j κ v).mp hv i (by omega)
      exact Submodule.mem_iSup_of_mem κ' (Submodule.mem_iSup_of_mem hpath hvE)
    · intro κ hκ z hz μ hz0 hzw
      have hκj : PathTo lam2 j κ :=
        ⟨hκ.1, fun i hi => hκ.2.1 i (by omega), fun i hi => hκ.2.2 i (by omega)⟩
      have hzj : z ∈ Eig D j κ := lp_Eig_mono j κ hz
      obtain ⟨b, hμ, hanti, hcas⟩ := lp_key hDom H j (by omega) κ (ihuniq κ hκj) z hzj hz0 μ hzw
      obtain ⟨ρ, hρ⟩ := hκ.2.1 j (by omega)
      have hcas2 : casOp (D (j + 1)) z = ((casVal (κ (j + 1)) : ℤ) : K) • z :=
        (lp_mem_Eig D (j + 1) κ z).mp hz (j + 1) le_rfl
      have heq : casVal (κ j + Pi.single b 1) = casVal (κ j + Pi.single ρ 1) := by
        rw [← hρ]
        have h1 : ((casVal (κ j + Pi.single b 1) : ℤ) : K) • z = ((casVal (κ (j + 1)) : ℤ) : K) • z := by
          rw [← hcas, ← hcas2]
        have h2 := smul_left_injective K hz0 h1
        exact_mod_cast h2
      have hbρ := lp_content_inj (κ j) (hκ.2.2 j (by omega)) b ρ heq
      rw [hμ, hρ, hbρ]

end Tower

theorem TowerPieri_of (hCR : CompleteRed) (hDom : HWDominant) : TowerPieri := by
  intro K N q _ _ _ _ _ _ n D ε B lam2 H h0
  have hc := (lp_claim hCR hDom H lam2 h0 n le_rfl).1
  apply eq_top_iff.mpr
  rw [← hc]
  refine iSup₂_le fun κ hκ => ?_
  intro z hz
  apply Submodule.subset_span
  choose ρf hρf using hκ.2.1
  exact ⟨κ n, κ, fun i => ρf i.val i.isLt, ⟨hκ.1, fun i => hρf i.val i.isLt, rfl, hκ.2.2⟩,
    (lp_mem_Eig D n κ z).mp hz⟩

end Formalism.CohomologicalDescent.LP
end

section -- merged from Formalism.PieriBlockIdeals.PieriColumnMinors.GeneratedHighestWeightHolds
namespace Formalism.CohomologicalDescent.LP

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

section

variable {K N : Type*} [CommRing K] [AddCommGroup N] [Module K N] {q : ℕ}

inductive LowW (T : Fin q → Fin q → Module.End K N) (κ : Fin q → K) : N → Prop
  | base (v : N) : IsHW T κ v → LowW T κ v
  | step (a b : Fin q) (x : N) : b < a → LowW T κ x → LowW T κ (T a b x)

def lowSpan (T : Fin q → Fin q → Module.End K N) (κ : Fin q → K) : Submodule K N :=
  Submodule.span K {x | LowW T κ x}

theorem lowSpan_low (T : Fin q → Fin q → Module.End K N) (κ : Fin q → K) (c d : Fin q) (h : d < c) :
    ∀ y ∈ lowSpan T κ, T c d y ∈ lowSpan T κ := by
  intro y hy
  have : (lowSpan T κ).map (T c d) ≤ lowSpan T κ := by
    unfold lowSpan
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact Submodule.subset_span (LowW.step c d x h hx)
  exact this (Submodule.mem_map_of_mem hy)

theorem lowW_all (T : Fin q → Fin q → Module.End K N) (hT : GlRel T) (κ : Fin q → K) (x : N) (hx : LowW T κ x) :
    ∀ a b, T a b x ∈ lowSpan T κ := by
  induction hx with
  | base v hv =>
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · rw [hv.1 a b h]; exact Submodule.zero_mem _
    · subst h
      rw [hv.2 a]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (LowW.base v hv))
    · exact Submodule.subset_span (LowW.step a b v h (LowW.base v hv))
  | step c d x hdc _ ih =>
    intro a b
    have h := LinearMap.congr_fun (hT a b c d) x
    simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
    have e : T a b (T c d x) = T c d (T a b x) +
        (((if b = c then T a d else 0 : Module.End K N) x) - ((if d = a then T c b else 0 : Module.End K N) x)) := by
      rw [← h]; abel
    rw [e]
    refine Submodule.add_mem _ (lowSpan_low T κ c d hdc _ (ih a b)) (Submodule.sub_mem _ ?_ ?_)
    · split_ifs
      · exact ih a d
      · simp
    · split_ifs
      · exact ih c b
      · simp

theorem lowSpan_stab (T : Fin q → Fin q → Module.End K N) (hT : GlRel T) (κ : Fin q → K) : Stab T (lowSpan T κ) := by
  intro a b y hy
  have : (lowSpan T κ).map (T a b) ≤ lowSpan T κ := by
    rw [lowSpan, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    exact lowW_all T hT κ x hx a b
  exact this (Submodule.mem_map_of_mem hy)

end

theorem generatedHighestWeight_holds : GeneratedHW := by
  intro K N q _ _ _ _ _ T B hF κ hgen v μ hv hhw
  by_contra hne
  obtain ⟨a, ha⟩ : ∃ a, μ a ≠ κ a := by
    by_contra hcon
    exact hne (funext fun a => by_contra fun h => hcon ⟨a, h⟩)
  have htop : lowSpan T κ = ⊤ :=
    hgen _ (lowSpan_stab T hF.gl κ) (fun w hw => Submodule.subset_span (LowW.base w hw))
  have horth : ∀ x, LowW T κ x → B v x = 0 := by
    intro x hx
    cases hx with
    | base _ hw =>
      have h := hF.adj a a v x
      rw [hhw.2 a, hw.2 a, map_smul, map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h
      have h2 : (μ a - κ a) * B v x = 0 := by rw [sub_mul, h, sub_self]
      exact (mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 ha)
    | step c d y hdc _ =>
      rw [← hF.adj d c v y, hhw.1 d c hdc, map_zero, LinearMap.zero_apply]
  have hall : ∀ y ∈ lowSpan T κ, B v y = 0 := by
    intro y hy
    have : lowSpan T κ ≤ LinearMap.ker (B v) := by
      rw [lowSpan, Submodule.span_le]
      intro x hx
      exact LinearMap.mem_ker.2 (horth x hx)
    exact LinearMap.mem_ker.1 (this hy)
  have h0 : B v v = 0 := hall v (by rw [htop]; exact Submodule.mem_top)
  exact absurd (hF.pos v hv) (by rw [h0]; exact lt_irrefl _)

end Formalism.CohomologicalDescent.LP
end

section -- merged from Formalism.PieriBlockIdeals.PieriColumnMinors.HighestWeightDominantHolds
namespace Formalism.CohomologicalDescent.LP

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem lpa_nonneg {K N : Type*} [Field K] [LinearOrder K] [AddCommGroup N] [Module K N] {q : ℕ}
    {T : Fin q → Fin q → Module.End K N} {B : LinearMap.BilinForm K N} (h : FormMod T B) (x : N) : 0 ≤ B x x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (h.pos x hx).le

theorem highestWeightDominant_holds : HWDominant := by
  intro K N q _ _ _ _ _ T B hU v μ hv0 hv a b hab
  obtain ⟨hr, hd⟩ := hv
  have h2 := LinearMap.congr_fun (hU.gl a b b a) v
  rw [if_pos rfl, if_pos rfl] at h2
  simp only [LinearMap.sub_apply, Module.End.mul_apply, hr a b hab, map_zero, sub_zero, hd a, hd b] at h2
  have hnn := lpa_nonneg hU (T b a v)
  rw [hU.adj b a v (T b a v), h2, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← sub_mul] at hnn
  have hpos := hU.pos v hv0
  by_contra hlt
  push Not at hlt
  have hneg : (μ a - μ b) * B v v < 0 := mul_neg_of_neg_of_pos (sub_neg.mpr hlt) hpos
  exact (not_le.mpr hneg) hnn

theorem lpa_joint {K N ι : Type*} [Field K] [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    (f : ι → Module.End K N) (hcomm : ∀ i j, Commute (f i) (f j))
    (hdiag : ∀ i, ⨆ μ : K, Module.End.eigenspace (f i) μ = ⊤) (s : Finset ι) (C : Submodule K N)
    (hC : ∀ i, ∀ x ∈ C, f i x ∈ C) (hne : C ≠ ⊥) :
    ∃ C' : Submodule K N, C' ≤ C ∧ C' ≠ ⊥ ∧ (∀ i, ∀ x ∈ C', f i x ∈ C') ∧ ∃ μ : ι → K, ∀ i ∈ s, ∀ x ∈ C', f i x = μ i • x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨C, le_rfl, hne, hC, 0, by simp⟩
  | insert i s hi ih =>
    obtain ⟨C', hC'C, hC'ne, hC'st, μ, hμ⟩ := ih
    have key : C' ⊓ ⨆ c, (f i).genEigenspace c 1 = ⨆ c, C' ⊓ (f i).genEigenspace c 1 :=
      Submodule.inf_iSup_genEigenspace (p := C') (f := f i) (fun x hx => hC'st i x hx) 1
    have htop : (⨆ c, (f i).genEigenspace c 1) = ⊤ := hdiag i
    rw [htop, inf_top_eq] at key
    have hex : ∃ c, C' ⊓ (f i).genEigenspace c 1 ≠ ⊥ := by
      by_contra h
      push Not at h
      apply hC'ne
      rw [key]
      exact iSup_eq_bot.mpr h
    obtain ⟨c, hc⟩ := hex
    refine ⟨C' ⊓ (f i).genEigenspace c 1, inf_le_left.trans hC'C, hc, ?_, Function.update μ i c, ?_⟩
    · intro j x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      exact Submodule.mem_inf.mpr
        ⟨hC'st j x hx1, Module.End.mapsTo_genEigenspace_of_comm (hcomm i j) c 1 hx2⟩
    · intro j hj x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      rcases Finset.mem_insert.mp hj with hji | hjs
      · rw [hji, Function.update_self]
        exact Module.End.mem_genEigenspace_one.mp hx2
      · have hji : j ≠ i := fun h => hi (h ▸ hjs)
        rw [Function.update_of_ne hji]
        exact hμ j hjs x hx1

private theorem weighted_sum_add_single_sub_single {K : Type*} [Field K] {q : ℕ} (μ : Fin q → K) (a b : Fin q) :
    ∑ c : Fin q, -((c : ℕ) : K) * (μ + Pi.single a (1 : K) - Pi.single b (1 : K) : Fin q → K) c =
      ∑ c : Fin q, -((c : ℕ) : K) * μ c + ((b : ℕ) : K) - ((a : ℕ) : K) := by
  have hs : ∀ d : Fin q, ∑ c : Fin q, -((c : ℕ) : K) * (Pi.single d (1 : K) : Fin q → K) c = -((d : ℕ) : K) := by
    intro d
    rw [Finset.sum_eq_single d]
    · simp
    · intro c _ hcd
      rw [Pi.single_eq_of_ne hcd, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ d) h
  simp only [Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, hs]
  ring

theorem existsHighestWeight_holds : ExistsHW := by
  intro K N q _ _ _ _ _ _ T hT hdiag C hC hne
  classical
  have hcomm : ∀ a b, Commute (T a a) (T b b) := by
    intro a b
    by_cases hab : a = b
    · subst hab
      exact Commute.refl _
    · have h := hT a a b b
      rw [if_neg hab, if_neg (Ne.symm hab), sub_zero] at h
      exact sub_eq_zero.mp h
  obtain ⟨C', hC'C, hC'ne, _, μ0, hμ0⟩ :=
    lpa_joint (fun a => T a a) (fun a b => hcomm a b) hdiag Finset.univ C
      (fun a x hx => hC a a x hx) hne
  obtain ⟨x0, hx0C', hx00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hC'ne
  obtain ⟨W, hW⟩ : ∃ W : Set (Fin q → K), ∀ ν, ν ∈ W ↔ ∃ v ∈ C, v ≠ 0 ∧ ∀ c, T c c v = ν c • v :=
    ⟨{ν | ∃ v ∈ C, v ≠ 0 ∧ ∀ c, T c c v = ν c • v}, fun ν => Iff.rfl⟩
  have hW0 : μ0 ∈ W := (hW μ0).mpr ⟨x0, hC'C hx0C', hx00, fun c => hμ0 c (Finset.mem_univ c) x0 hx0C'⟩
  have hfin : (Set.univ.pi fun c : Fin q => {z : K | (T c c).HasEigenvalue z}).Finite :=
    Set.Finite.pi fun c => Module.End.finite_hasEigenvalue (T c c)
  have hWfin : W.Finite := by
    refine hfin.subset ?_
    intro ν hν
    obtain ⟨v, -, hv0, hv⟩ := (hW ν).mp hν
    rw [Set.mem_univ_pi]
    intro c
    exact Module.End.hasEigenvalue_of_hasEigenvector
      (Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr (hv c), hv0⟩)
  obtain ⟨μ, hμW, hmax⟩ :=
    Set.exists_max_image W (fun ν => ∑ c : Fin q, -((c : ℕ) : K) * ν c) hWfin ⟨μ0, hW0⟩
  obtain ⟨v, hvC, hv0, hvw⟩ := (hW μ).mp hμW
  refine ⟨v, hvC, hv0, μ, And.intro ?_ hvw⟩
  intro a b hab
  by_contra hw
  have hba : b ≠ a := hab.ne'
  have hwt : ∀ c, T c c (T a b v) = (μ + Pi.single a (1 : K) - Pi.single b (1 : K) : Fin q → K) c • T a b v := by
    intro c
    have h2 := LinearMap.congr_fun (hT c c a b) v
    simp only [LinearMap.sub_apply, Module.End.mul_apply, hvw c, map_smul] at h2
    have h3 := sub_eq_iff_eq_add.mp h2
    by_cases hca : c = a
    · rw [hca] at h3 ⊢
      rw [if_pos rfl, if_neg hba, LinearMap.zero_apply, sub_zero] at h3
      rw [h3]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab.ne, sub_zero]
      module
    · by_cases hcb : c = b
      · rw [hcb] at h3 ⊢
        rw [if_neg hba, if_pos rfl, LinearMap.zero_apply, zero_sub] at h3
        rw [h3]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hba, add_zero]
        module
      · rw [if_neg hca, if_neg (fun h => hcb h.symm), LinearMap.zero_apply, sub_zero, zero_add] at h3
        rw [h3]
        simp only [Pi.add_apply, Pi.sub_apply, Pi.single_eq_of_ne hca, Pi.single_eq_of_ne hcb,
          add_zero, sub_zero]
  have hνW : (μ + Pi.single a (1 : K) - Pi.single b (1 : K) : Fin q → K) ∈ W := (hW _).mpr ⟨T a b v, hC a b v hvC, hw, hwt⟩
  have hle : ∑ c : Fin q, -((c : ℕ) : K) * (μ + Pi.single a (1 : K) - Pi.single b (1 : K) : Fin q → K) c ≤
      ∑ c : Fin q, -((c : ℕ) : K) * μ c := hmax _ hνW
  rw [weighted_sum_add_single_sub_single] at hle
  have hlt : ((a : ℕ) : K) < ((b : ℕ) : K) := by
    exact Nat.cast_lt.mpr hab
  linarith

theorem completeReducibility_holds : CompleteRed := by
  intro K N q _ _ _ _ _ _ T B hU S S' hS hS' hhw
  classical
  have hrefl : B.IsRefl := by
    intro x y h
    exact (hU.symm y x).trans h
  have hRst : Stab T (S ⊓ S') := fun a b x hx =>
    Submodule.mem_inf.mpr ⟨hS a b x (Submodule.mem_inf.mp hx).1, hS' a b x (Submodule.mem_inf.mp hx).2⟩
  have hUst : Stab T (S ⊓ B.orthogonal (S ⊓ S')) := by
    intro a b x hx
    obtain ⟨hxS, hxO⟩ := Submodule.mem_inf.mp hx
    refine Submodule.mem_inf.mpr ⟨hS a b x hxS, ?_⟩
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    rw [hU.symm, hU.adj, hU.symm]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hxO) _ (hRst b a n hn)
  have hUbot : S ⊓ B.orthogonal (S ⊓ S') = ⊥ := by
    by_contra hne
    obtain ⟨v, hvU, hv0, μ, hμ⟩ := existsHighestWeight_holds K N q T hU.gl hU.diag _ hUst hne
    obtain ⟨hvS, hvO⟩ := Submodule.mem_inf.mp hvU
    have hvS' := hhw v hvS μ hμ
    have hvv := (LinearMap.BilinForm.mem_orthogonal_iff.mp hvO) v (Submodule.mem_inf.mpr ⟨hvS, hvS'⟩)
    exact (hU.pos v hv0).ne' hvv
  have hcompl : IsCompl (S ⊓ S') (B.orthogonal (S ⊓ S')) :=
    (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint hrefl).mpr
      (Submodule.disjoint_def.mpr fun x hxR hxO =>
        Classical.byContradiction fun h =>
          (hU.pos x h).ne' ((LinearMap.BilinForm.mem_orthogonal_iff.mp hxO) x hxR))
  intro x hxS
  have hx : x ∈ (S ⊓ S') ⊔ B.orthogonal (S ⊓ S') := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨y, hyR, z, hzO, hyz⟩ := Submodule.mem_sup.mp hx
  have hzS : z ∈ S := by
    have hz : z = x - y := by
      rw [← hyz]
      abel
    rw [hz]
    exact S.sub_mem hxS (Submodule.mem_inf.mp hyR).1
  have hz0 : z = 0 := by
    have hzU : z ∈ S ⊓ B.orthogonal (S ⊓ S') := Submodule.mem_inf.mpr ⟨hzS, hzO⟩
    rw [hUbot] at hzU
    exact (Submodule.mem_bot K).mp hzU
  rw [← hyz, hz0, add_zero]
  exact (Submodule.mem_inf.mp hyR).2

end Formalism.CohomologicalDescent.LP
end

namespace Formalism.CohomologicalDescent.LP

open Formalism.CohomologicalDescent.Symmetrization Formalism.CohomologicalDescent.BinaryFormsExample

theorem tower_pieri : TowerPieri := TowerPieri_of completeReducibility_holds highestWeightDominant_holds

theorem pieri_rule : Pieri := by
  intro K P M q _ _ _ _ _ _ _ _ EM B lam2 hF h0 n
  have hT := tensor_tower K P M q EM B n hF
  have hb := tensor_base_case K P M q EM n (fun b => (lam2 b : K)) h0
  have hTP := tower_pieri K (Tens (Fin q) P M n) q n (fun j => Dpart K EM j) (epsY K n)
    (tensForm n B) lam2 hT hb
  apply eq_top_iff.mpr
  rw [← hTP, Submodule.span_le]
  rintro z ⟨tau, κ, ρ, hp, hcas⟩
  exact Submodule.mem_iSup_of_mem tau (Submodule.subset_span ⟨κ, ρ, hp, fun j hj => hcas j hj⟩)

theorem pieri_generated : PieriGenerated := by
  intro K P M q _ _ _ _ _ _ _ _ EM B lam2 hF hgen n
  exact pieri_rule K P M q EM B lam2 hF (generatedHighestWeight_holds K M q EM B hF _ hgen) n

end Formalism.CohomologicalDescent.LP
