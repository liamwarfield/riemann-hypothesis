module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.DetDer
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.OnePos
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.FockLin
public import Formalism.SharpRestriction.GrowthBounds.DualFockLinear.FirstWeightLeConductor
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.OpWords

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.RowWtSpan
open MvPolynomial

noncomputable section

namespace PI.RW

def colW (r n : ℕ) : Fin r × Fin n → (Fin n → ℕ) := fun v => Pi.single v.2 1

def colAddGen (R : Type*) [CommRing R] {r n : ℕ} (l j : Fin n) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Option (Fin r × Fin n)) R :=
  aeval fun v => if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v)

def dualWeyl (R : Type*) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) :
    Submodule R (MvPolynomial (Fin r × Fin n) R) :=
  weightedHomogeneousSubmodule R (colW r n) ν ⊓
    ⨅ (l : Fin n) (j : Fin n) (_ : l < j),
      LinearMap.ker ((colAddGen R (r := r) l j).toLinearMap -
        (rename (R := R) (some : Fin r × Fin n → Option (Fin r × Fin n))).toLinearMap)

def initMinor (R : Type*) [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n) :
    MvPolynomial (Fin r × Fin n) R :=
  (Matrix.of fun p q : Fin s => (X (I p, Fin.castLE hs q) : MvPolynomial (Fin r × Fin n) R)).det

def bideterminant (R : Type*) [CommRing R] {r n K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r) : MvPolynomial (Fin r × Fin n) R :=
  ∏ k : Fin K, initMinor R (I k) (hsz k)

def shapeDeg {n K : ℕ} (sz : Fin K → ℕ) (t : Fin n) : ℕ :=
  (Finset.univ.filter fun k : Fin K => t.val < sz k).card

def RE (K : Type) [CommRing K] (k : ℕ) (a b : Fin k) (f : MvPolynomial (Fin k × Fin k) K) : MvPolynomial (Fin k × Fin k) K :=
  ∑ t : Fin k, X (a, t) * pderiv (b, t) f

def BideterminantMem : Prop :=
  ∀ (R : Type) [CommRing R] (r n K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
    (I : ∀ k, Fin (sz k) → Fin r),
    bideterminant R sz hsz I ∈ dualWeyl R r n (shapeDeg sz)

def BideterminantSpan : Prop :=
  ∀ (R : Type) [CommRing R] [IsDomain R] (k n : ℕ) (ν : Fin n → ℕ),
    dualWeyl R k n ν ≤ Submodule.span R {f | ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ i, sz i ≤ n) (I : ∀ i, Fin (sz i) → Fin k),
      shapeDeg sz = ν ∧ (∀ i, StrictMono (I i)) ∧ f = bideterminant R sz hsz I}

end PI.RW

namespace PI

open PI.RW

def RowWtSpan : Prop :=
  ∀ (K : Type) [Field K] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν →
    ∃ (J : Type) (b : J → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) (μ : J → Fin (m + 1) → ℕ),
      Submodule.span K (Set.range b) = dualWeyl K (m + 1) (m + 1) ν ∧
      (∀ i a, RE K (m + 1) a a (b i) = (μ i a : K) • b i) ∧ ∀ i a, μ i a ≤ ν 0

end PI
end
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.AdjointTensorOfSingleValid
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.FilterConcatWLength
open MvPolynomial

noncomputable section

namespace PI.TOW

open PI.TO

theorem mem_concatW {n' k : ℕ} (w : Fin n' → List (Fin k × Fin k)) (z : Fin n' × (Fin k × Fin k)) :
    z ∈ concatW w ↔ z.2 ∈ w z.1 := by
  simp only [concatW, liftW, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
  constructor
  · rintro ⟨t, y, hy, rfl⟩
    exact hy
  · intro h
    exact ⟨z.1, z.2, h, rfl⟩

theorem filter_concatW_length {n' k : ℕ} (w : Fin n' → List (Fin k × Fin k)) (t : Fin n') :
    ((concatW w).filter fun z => z.1 = t).length = (w t).length := by
  rw [← List.countP_eq_length_filter]
  simp only [concatW, liftW, List.countP_flatMap]
  rw [← List.ofFn_eq_map, List.sum_ofFn, Finset.sum_eq_single t]
  · simp [Function.comp_def]
  · intro b _ hb
    simp [Function.comp_def, hb]
  · simp

theorem prod_smul_eq {σ K : Type*} [CommRing K] {ι : Type*} [Fintype ι] (c : ι → K) (x : ι → MvPolynomial σ K) :
    ∏ i, (c i • x i) = (∏ i, c i) • ∏ i, x i := by
  simp only [MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, map_prod]

theorem partS_mem {K : Type} [CommRing K] {n' m : ℕ} {d : Fin n' → ℕ} (μ : Fin n' × Fin (m + 1) →₀ ℕ)
    (hμ : μ ∈ {μ : Fin n' × Fin (m + 1) →₀ ℕ | ∀ i, multideg μ i = d i}) (t : Fin n') :
    monomial (partS μ t) (1 : K) ∈ Hd K (m + 1) (d t) := by
  show monomial (partS μ t) (1 : K) ∈ restrictSupport K {ν : Fin (m + 1) →₀ ℕ | ∑ c, ν c = d t}
  rw [mem_restrictSupport_iff]
  intro x hx
  have hx' := support_monomial_subset hx
  rw [Finset.mem_singleton] at hx'
  subst hx'
  have h := hμ t
  simpa [partS, multideg] using h

theorem stepPure_of (hL : StepLift) (hM : StepMonoFactor) : StepPure := by
  unfold StepPure
  intro hFB hOP K _ _ n' m hm vec TT d c ν hν hνc hν0 B S hB hS
  classical
  have hex : ∀ t : Fin n', ∃ (L : Finset (List (Fin (m + 1) × Fin (m + 1))))
      (a : List (Fin (m + 1) × Fin (m + 1)) → K),
      (∀ l ∈ L, l.length ≤ (if t ∈ TT then c else 0)) ∧
      ∀ P ∈ Hd K (m + 1) (d t), ∀ Q ∈ Hd K (m + 1) (d t),
        fockR (theta K m (vec t) P * S t) (theta K m (vec t) Q * B t) =
          fockR (theta K m (vec t) (∑ l ∈ L, a l • word1 l P)) (theta K m (vec t) Q) := by
    intro t
    refine hOP K m hm (vec t) (d t) (if t ∈ TT then c else 0) (ν t) (hν t) ?_ (B t) (hB t)
      (S t) (hS t)
    split_ifs with ht
    · exact hνc t ht
    · simp [hν0 t ht]
  choose L a hLlen hLfock using hex
  let f : List (Fin n' × (Fin (m + 1) × Fin (m + 1))) →₀ K :=
    ∑ w ∈ Fintype.piFinset L, Finsupp.single (concatW w) (∏ t, a t (w t))
  unfold Ok
  refine ⟨f, ?_, ?_⟩
  · intro l hl
    have hl' := Finsupp.support_finsetSum hl
    rw [Finset.mem_biUnion] at hl'
    obtain ⟨w, hw, hlw⟩ := hl'
    have hlw' := Finsupp.support_single_subset hlw
    rw [Finset.mem_singleton] at hlw'
    subst hlw'
    rw [Fintype.mem_piFinset] at hw
    unfold WordOK
    constructor
    · intro z hz
      rw [mem_concatW] at hz
      by_contra hzT
      have hlen := hLlen z.1 (w z.1) (hw z.1)
      rw [if_neg hzT] at hlen
      cases hwz : w z.1 with
      | nil => simp [hwz] at hz
      | cons _ _ => simp [hwz] at hlen
    · intro t
      rw [filter_concatW_length]
      have hlen := hLlen t (w t) (hw t)
      split_ifs at hlen <;> omega
  · have hcombo : ∀ G, combo f G =
        ∑ w ∈ Fintype.piFinset L, (∏ t, a t (w t)) • opWord (concatW w) G := by
      intro G
      simp only [combo, f]
      rw [← Finsupp.sum_finsetSum_index (fun l => zero_smul K (opWord l G))
        (fun l b₁ b₂ => add_smul b₁ b₂ (opWord l G))]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [Finsupp.sum_single_index (zero_smul K (opWord (concatW w) G))]
    have hTh : ∀ F : Fin n' → MvPolynomial (Fin (m + 1)) K,
        Th0 K m vec (∏ t, embS K t (F t)) = ∏ t, blockEmb K t (theta K m (vec t) (F t)) := by
      intro F
      rw [map_prod]
      exact Finset.prod_congr rfl fun t _ => blockSubstitution_blockInclusion vec t (F t)
    have main : ∀ P Q : Fin n' → MvPolynomial (Fin (m + 1)) K,
        (∀ t, P t ∈ Hd K (m + 1) (d t)) → (∀ t, Q t ∈ Hd K (m + 1) (d t)) →
        fockR (Th0 K m vec (∏ t, embS K t (P t)) * ∏ t, blockEmb K t (S t))
            (Th0 K m vec (∏ t, embS K t (Q t)) * ∏ t, blockEmb K t (B t)) =
          fockR (Th0 K m vec (combo f (∏ t, embS K t (P t))))
            (Th0 K m vec (∏ t, embS K t (Q t))) := by
      intro P Q hP hQ
      have hc : combo f (∏ t, embS K t (P t)) =
          ∏ t, embS K t (∑ l ∈ L t, a t l • word1 l (P t)) := by
        rw [hcombo]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_sum, map_smul]
        rw [Finset.prod_univ_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [prod_smul_eq, hL K n' (m + 1) w P]
      rw [hc, hTh, hTh, hTh, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      simp only [← map_mul]
      rw [hFB K (Fin n') (m + 1) (m + 1), hFB K (Fin n') (m + 1) (m + 1)]
      exact Finset.prod_congr rfl fun t _ => hLfock t (P t) (hP t) (Q t) (hQ t)
    let Φ : MvPolynomial (Fin n' × Fin (m + 1)) K →ₗ[K] MvPolynomial (Fin n' × Fin (m + 1)) K →ₗ[K] K :=
      (fockB (Fin n' × (Fin (m + 1) × Fin (m + 1))) K).compl₁₂
        ((LinearMap.mulRight K (∏ t, blockEmb K t (S t))).comp (Th0 K m vec).toLinearMap)
        ((LinearMap.mulRight K (∏ t, blockEmb K t (B t))).comp (Th0 K m vec).toLinearMap)
    let Ψ : MvPolynomial (Fin n' × Fin (m + 1)) K →ₗ[K] MvPolynomial (Fin n' × Fin (m + 1)) K →ₗ[K] K :=
      (fockB (Fin n' × (Fin (m + 1) × Fin (m + 1))) K).compl₁₂
        ((Th0 K m vec).toLinearMap.comp (comboL f)) (Th0 K m vec).toLinearMap
    have key := bilin_ext_restrict {μ | ∀ i, multideg μ i = d i} Φ Ψ (by
      intro μ hμ μ' hμ'
      show fockB _ K (Th0 K m vec (monomial μ 1) * ∏ t, blockEmb K t (S t))
          (Th0 K m vec (monomial μ' 1) * ∏ t, blockEmb K t (B t)) =
        fockB _ K (Th0 K m vec (combo f (monomial μ 1))) (Th0 K m vec (monomial μ' 1))
      rw [fockB_apply, fockB_apply, hM K n' (m + 1) μ, hM K n' (m + 1) μ']
      exact main _ _ (fun t => partS_mem μ hμ t) (fun t => partS_mem μ' hμ' t))
    intro G hG H hH
    rw [← fockB_apply, ← fockB_apply]
    exact key G hG H hH

end PI.TOW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.OkSmulRight
open MvPolynomial

noncomputable section

namespace PI.TOW

open PI.TO

variable {K : Type} [Field K] {n' m : ℕ} {vec : Fin n' → Bool} {TT : Finset (Fin n')} {d : Fin n' → ℕ} {c : ℕ}

theorem ok_zero_left (s : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K) :
    Ok K n' m vec TT d c 0 s := by
  refine ⟨0, by simp, fun G _ H _ => ?_⟩
  rw [mul_zero, fockR_zero_right, combo_zero, map_zero, fockR_zero_left]

theorem ok_zero_right (β : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K) :
    Ok K n' m vec TT d c β 0 := by
  refine ⟨0, by simp, fun G _ H _ => ?_⟩
  rw [mul_zero, fockR_zero_left, combo_zero, map_zero, fockR_zero_left]

theorem ok_add_left {β₁ β₂ s : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K}
    (h₁ : Ok K n' m vec TT d c β₁ s) (h₂ : Ok K n' m vec TT d c β₂ s) : Ok K n' m vec TT d c (β₁ + β₂) s := by
  obtain ⟨f₁, hf₁, e₁⟩ := h₁
  obtain ⟨f₂, hf₂, e₂⟩ := h₂
  refine ⟨f₁ + f₂, fun l hl => ?_, fun G hG H hH => ?_⟩
  · rcases Finset.mem_union.1 (Finsupp.support_add hl) with h | h
    exacts [hf₁ l h, hf₂ l h]
  · rw [mul_add, fockR_add_right, e₁ G hG H hH, e₂ G hG H hH, combo_add, map_add (f := _),
      fockR_add_left]

theorem ok_add_right {β s₁ s₂ : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K}
    (h₁ : Ok K n' m vec TT d c β s₁) (h₂ : Ok K n' m vec TT d c β s₂) : Ok K n' m vec TT d c β (s₁ + s₂) := by
  obtain ⟨f₁, hf₁, e₁⟩ := h₁
  obtain ⟨f₂, hf₂, e₂⟩ := h₂
  refine ⟨f₁ + f₂, fun l hl => ?_, fun G hG H hH => ?_⟩
  · rcases Finset.mem_union.1 (Finsupp.support_add hl) with h | h
    exacts [hf₁ l h, hf₂ l h]
  · rw [mul_add, fockR_add_left, e₁ G hG H hH, e₂ G hG H hH, combo_add, map_add (f := _),
      fockR_add_left]

theorem ok_smul_left (a : K) {β s : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K}
    (h : Ok K n' m vec TT d c β s) : Ok K n' m vec TT d c (a • β) s := by
  obtain ⟨f, hf, e⟩ := h
  refine ⟨a • f, fun l hl => hf l (Finsupp.support_smul hl), fun G hG H hH => ?_⟩
  rw [mul_smul_comm, fockR_smul_right, e G hG H hH, combo_smul, map_smul,
    fockR_smul_left]

theorem ok_smul_right (a : K) {β s : MvPolynomial (Fin n' × (Fin (m + 1) × Fin (m + 1))) K}
    (h : Ok K n' m vec TT d c β s) : Ok K n' m vec TT d c β (a • s) := by
  obtain ⟨f, hf, e⟩ := h
  refine ⟨a • f, fun l hl => hf l (Finsupp.support_smul hl), fun G hG H hH => ?_⟩
  rw [mul_smul_comm, fockR_smul_left, e G hG H hH, combo_smul, map_smul,
    fockR_smul_left]

theorem stepSpan : StepSpan := by
  intro K _ n' m vec TT d c M hM β hβ s hs
  unfold PI.TO.tensorLat at hβ hs
  have key : ∀ F : Fin n' → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K, (∀ t, F t ∈ M t) →
      Ok K n' m vec TT d c (∏ t, PI.TO.blockEmb K t (F t)) s := by
    intro F hF
    induction hs using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨S, hS, rfl⟩ := hx
      exact hM F S hF hS
    | zero => exact ok_zero_right _
    | add x y _ _ hx hy => exact ok_add_right hx hy
    | smul a x _ hx => exact ok_smul_right a hx
  induction hβ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    exact key F hF
  | zero => exact ok_zero_left _
  | add x y _ _ hx hy => exact ok_add_left hx hy
  | smul a x _ hx => exact ok_smul_left a hx

end PI.TOW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.NotMemVarsEmbS
open MvPolynomial

noncomputable section

namespace PI.TOW.LiftW

open PI.TO PI.TOW

variable {K : Type} [CommRing K] {n' k : ℕ}

theorem inj (t : Fin n') : Function.Injective (fun c : Fin k => (t, c)) := by
  intro a c h
  exact (Prod.mk.inj h).2

theorem pderiv_embS (t : Fin n') (b : Fin k) (W : MvPolynomial (Fin k) K) :
    pderiv (t, b) (embS K t W) = embS K t (pderiv b W) := by
  simpa [embS] using pderiv_rename (inj (k := k) t) b W

theorem notMem_vars_embS {t a : Fin n'} (h : a ≠ t) (b : Fin k) (W : MvPolynomial (Fin k) K) :
    (t, b) ∉ (embS K a W).vars := by
  intro hm
  have h2 : (t, b) ∈ W.vars.image (fun c : Fin k => (a, c)) :=
    vars_rename (fun c : Fin k => (a, c)) W hm
  rw [Finset.mem_image] at h2
  obtain ⟨c, -, hc⟩ := h2
  exact h (congrArg Prod.fst hc)

theorem pderiv_prod_ne (t : Fin n') (b : Fin k) (T : Finset (Fin n')) (ht : t ∉ T)
    (H : Fin n' → MvPolynomial (Fin k) K) : pderiv (t, b) (∏ s ∈ T, embS K s (H s)) = 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert s T hs ih =>
    rw [Finset.prod_insert hs, Derivation.leibniz]
    have hst : s ≠ t := fun e => ht (e ▸ Finset.mem_insert_self s T)
    rw [ih (fun h => ht (Finset.mem_insert_of_mem h)),
      pderiv_eq_zero_of_notMem_vars (notMem_vars_embS hst b (H s))]
    simp

theorem opWord_liftW (t : Fin n') (l : List (Fin k × Fin k)) (F : MvPolynomial (Fin k) K)
    (R : MvPolynomial (Fin n' × Fin k) K) (hR : ∀ b, pderiv (t, b) R = 0) :
    opWord (liftW t l) (embS K t F * R) = embS K t (word1 l F) * R := by
  induction l with
  | nil => simp [opWord, liftW, word1]
  | cons y l ih =>
    have e1 : opWord (liftW t (y :: l)) (embS K t F * R)
        = X (t, y.1) * pderiv (t, y.2) (opWord (liftW t l) (embS K t F * R)) := by
      simp [opWord, liftW]
    have e2 : word1 (y :: l) F = X y.1 * pderiv y.2 (word1 l F) := by
      simp [word1]
    rw [e1, ih, e2, Derivation.leibniz, hR, pderiv_embS]
    simp [embS, map_mul, rename_X]
    ring

theorem opWord_append (l₁ l₂ : List (Fin n' × (Fin k × Fin k))) (f : MvPolynomial (Fin n' × Fin k) K) :
    opWord (l₁ ++ l₂) f = opWord l₁ (opWord l₂ f) := by
  simp [opWord, List.foldr_append]

theorem main_list (w : Fin n' → List (Fin k × Fin k)) (G : Fin n' → MvPolynomial (Fin k) K)
    (ts : List (Fin n')) (hts : ts.Nodup) :
    opWord (ts.flatMap fun t => liftW t (w t)) (∏ s, embS K s (G s)) =
      ∏ s, embS K s (if s ∈ ts then word1 (w s) (G s) else G s) := by
  classical
  induction ts with
  | nil => simp [opWord]
  | cons t ts ih =>
    rw [List.nodup_cons] at hts
    rw [List.flatMap_cons, opWord_append, ih hts.2]
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ t),
      ← Finset.mul_prod_erase Finset.univ
        (fun s => embS K s (if s ∈ t :: ts then word1 (w s) (G s) else G s)) (Finset.mem_univ t)]
    simp only [if_neg hts.1, List.mem_cons, true_or, if_true]
    rw [opWord_liftW t (w t) (G t) _ (fun b' => pderiv_prod_ne t b' _ (Finset.notMem_erase t _) _)]
    congr 1
    refine Finset.prod_congr rfl fun s hs => ?_
    have hne : s ≠ t := Finset.ne_of_mem_erase hs
    simp [hne]

theorem stepLift : StepLift := by
  intro K _ n' k w F
  have h := main_list w F (List.finRange n') (List.nodup_finRange n')
  simpa [concatW, List.mem_finRange] using h

end PI.TOW.LiftW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.StepMonoFactor
open MvPolynomial

noncomputable section

namespace PI.TOW.MonoW

open PI.TO PI.TOW

theorem stepMonoFactor : StepMonoFactor := by
  intro K _ n' k μ
  simp only [embS, rename_monomial]
  suffices hμ : μ = ∑ t, Finsupp.mapDomain (fun c => (t, c)) (partS μ t) by
    rw [← MvPolynomial.monomial_sum_one, ← hμ]
  ext ⟨t, c⟩
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single t]
  · rw [Finsupp.mapDomain_apply_of_injective (fun a b h => by simpa using h)]
    simp [partS]
  · intro t' _ ht'
    rw [Finsupp.mapDomain_notin_range]
    rintro ⟨c', hc'⟩
    exact ht' (congrArg Prod.fst hc')
  · simp

end PI.TOW.MonoW
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorOperator.MultidegSingle
open MvPolynomial

noncomputable section

namespace PI.TOW.DegW

open PI.TO PI.TOW

variable {K : Type} [Field K] {n' k : ℕ}

theorem multideg_add (a b : Fin n' × Fin k →₀ ℕ) (i : Fin n') :
    multideg (a + b) i = multideg a i + multideg b i := by
  simp only [multideg, Finsupp.add_apply, Finset.sum_add_distrib]

theorem multideg_single (j : Fin n' × Fin k) (i : Fin n') :
    multideg (Finsupp.single j 1) i = if j.1 = i then 1 else 0 := by
  obtain ⟨j₁, j₂⟩ := j
  by_cases h : j₁ = i <;> simp [multideg, Finsupp.single_apply, Prod.ext_iff, h]

theorem step_mem (t : Fin n') (a b : Fin k) (d : Fin n' → ℕ) (G : MvPolynomial (Fin n' × Fin k) K)
    (hG : G ∈ Pol K (ι := Fin n') k d) :
    X (t, a) * pderiv (t, b) G ∈ Pol K (ι := Fin n') k d := by
  rw [Pol, MvPolynomial.mem_restrictSupport_iff] at hG
  set_option synthInstance.maxHeartbeats 100000 in
    rw [G.as_sum, map_sum, Finset.mul_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  have hdm : ∀ i, multideg m i = d i := hG hm
  rw [MvPolynomial.pderiv_monomial, MvPolynomial.X, MvPolynomial.monomial_mul]
  by_cases hmb : m (t, b) = 0
  · simp [hmb]
  have hle : Finsupp.single (t, b) 1 ≤ m := by
    rw [Finsupp.single_le_iff]; omega
  have hsplit : m = (m - Finsupp.single (t, b) 1) + Finsupp.single (t, b) 1 :=
    (tsub_add_cancel_of_le hle).symm
  have hexp : ∀ i, multideg (Finsupp.single (t, a) 1 + (m - Finsupp.single (t, b) 1)) i = d i := by
    intro i
    have h1 := multideg_add (m - Finsupp.single (t, b) 1) (Finsupp.single (t, b) 1) i
    rw [← hsplit, hdm i, multideg_single] at h1
    rw [multideg_add, multideg_single]
    simp only at h1 ⊢
    split_ifs at h1 ⊢ <;> omega
  rw [Pol, MvPolynomial.mem_restrictSupport_iff]
  intro x hx
  have hx' := MvPolynomial.support_monomial_subset (Finset.mem_coe.mp hx)
  rw [Finset.mem_singleton] at hx'
  subst hx'
  exact hexp

theorem stepDeg : StepDeg := by
  intro K _ n' k d l G hG
  induction l with
  | nil => exact hG
  | cons y l ih =>
    simp only [opWord, List.foldr_cons] at ih ⊢
    exact step_mem y.1 y.2.1 y.2.2 d _ ih

end PI.TOW.DegW
end
end

theorem adjointTensorOfSingle_valid : PI.TenOp :=
  PI.TOW.tenOp_of_steps PI.TOW.DegW.stepDeg
    (PI.TOW.stepPure_of PI.TOW.LiftW.stepLift PI.TOW.MonoW.stepMonoFactor) PI.TOW.stepSpan
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.RowLetter
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.NvFalseEq
open MvPolynomial

noncomputable section

namespace PI.RL.W

open PI.RL

theorem Nv_false_eq (K : Type) [Field K] (m : ℕ) (c : Fin (m + 1)) :
    Nv K m false c = ((genM K m).updateRow c (Pi.single (Fin.last m) 1)).det := by
  simp [Nv, Matrix.adjugate_apply]

theorem keyCov : KeyCov := by
  intro K _ m a b c
  have hN : ∀ d, Nv K m false d =
      ((genM K m).updateRow d (Pi.single (Fin.last m) 1)).det := fun d => Nv_false_eq K m d
  have hG : ∀ i j, genM K m i j = X (i, j) := fun i j => rfl
  rw [RE_eq_REder, hN c, hN b, derivation_det]
  have hrow : ∀ i j, REder K (m + 1) a b
      (((genM K m).updateRow c (Pi.single (Fin.last m) 1)) i j) =
        if i = c then 0 else if i = b then X (a, j) else 0 := by
    intro i j
    by_cases hic : i = c
    · subst hic
      rw [Matrix.updateRow_self, if_pos rfl]
      by_cases hj : j = Fin.last m
      · subst hj; simp
      · simp [Pi.single_apply, hj]
    · rw [Matrix.updateRow_ne hic, hG, REder_X, if_neg hic]
  simp_rw [hrow]
  have hz : ∀ (M : Matrix (Fin (m + 1)) (Fin (m + 1)) (MvPolynomial (Fin (m + 1) × Fin (m + 1)) K))
      (i : Fin (m + 1)) (r : Fin (m + 1) → MvPolynomial (Fin (m + 1) × Fin (m + 1)) K),
      (∀ j, r j = 0) → (M.updateRow i r).det = 0 := by
    intro M i r hr
    exact Matrix.det_eq_zero_of_row_eq_zero i (fun j => by rw [Matrix.updateRow_self]; exact hr j)
  by_cases hbc : b = c
  · subst hbc
    rw [Finset.sum_eq_zero]
    · simp
    · intro i _
      apply hz
      intro j
      split_ifs <;> rfl
  rw [Finset.sum_eq_single b]
  rotate_left
  · intro i _ hib
    apply hz
    intro j
    split_ifs <;> rfl
  · intro h; exact absurd (Finset.mem_univ b) h
  simp only [hbc, if_false, if_true, eq_self_iff_true, ite_true, ite_false]
  by_cases hab : a = b
  · subst hab
    rw [if_pos rfl, if_neg hbc, sub_zero]
    congr 1
    refine Matrix.ext fun i j => ?_
    by_cases hi : i = a
    · rw [hi, Matrix.updateRow_self]
      simp only [Matrix.updateRow_apply, hG]
      try (split_ifs <;> simp_all)
    · rw [Matrix.updateRow_ne hi]
  rw [if_neg hab]
  by_cases hac : a = c
  · subst hac
    rw [if_pos rfl, zero_sub]
    have hperm : (((genM K m).updateRow a (Pi.single (Fin.last m) 1)).updateRow b
        (fun j => X (a, j))) =
        ((genM K m).updateRow b (Pi.single (Fin.last m) 1)).submatrix (Equiv.swap b a) id := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.submatrix_apply, id, Matrix.updateRow_apply, Equiv.swap_apply_def, hG]
      split_ifs <;> simp_all
    rw [hperm, Matrix.det_permute, Equiv.Perm.sign_swap hbc]
    simp
  · rw [if_neg hac, sub_zero]
    apply Matrix.det_zero_of_row_eq hab
    funext j
    rw [Matrix.updateRow_ne hab, Matrix.updateRow_self, Matrix.updateRow_ne hac, hG]

end PI.RL.W
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowDerivationChainRule.ChainRule
open MvPolynomial

noncomputable section

namespace PI.RL.W

open PI.RL

section

variable {K : Type} [Field K] {k : ℕ}

theorem RE_add (a b : Fin k) (f g : MvPolynomial (Fin k × Fin k) K) :
    RE K k a b (f + g) = RE K k a b f + RE K k a b g := by
  simp only [PI.RL.RE, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem RE_C (a b : Fin k) (r : K) : RE K k a b (C r) = 0 := by
  simp [PI.RL.RE]

private theorem pderiv_mul_eq {σ : Type*} {R : Type*} [CommRing R] (i : σ) (f g : MvPolynomial σ R) :
    pderiv i (f * g) = pderiv i f * g + f * pderiv i g := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring

theorem RE_mul (a b : Fin k) (f g : MvPolynomial (Fin k × Fin k) K) :
    RE K k a b (f * g) = RE K k a b f * g + f * RE K k a b g := by
  simp only [PI.RL.RE, pderiv_mul_eq, mul_add, Finset.sum_add_distrib, Finset.sum_mul,
    Finset.mul_sum]
  congr 1 <;> (refine Finset.sum_congr rfl (fun t _ => ?_); ring)

end

private theorem pderiv_X_eq_ite {σ : Type*} {R : Type*} [CommRing R] [DecidableEq σ] (c i : σ) :
    pderiv c (X i : MvPolynomial σ R) = if c = i then 1 else 0 := by
  rw [pderiv_X]
  by_cases h : c = i
  · subst h; simp
  · rw [if_neg h, Pi.single_apply, if_neg (Ne.symm h)]

private theorem derivation_aeval_eq_sum_pderiv {K : Type*} [CommRing K] {σ τ : Type*} [Fintype σ] [DecidableEq σ]
    (D : MvPolynomial τ K → MvPolynomial τ K)
    (hadd : ∀ f g, D (f + g) = D f + D g) (hC : ∀ r, D (C r) = 0)
    (hmul : ∀ f g, D (f * g) = D f * g + f * D g)
    (g : σ → MvPolynomial τ K) (P : MvPolynomial σ K) :
    D (aeval g P) = ∑ c, aeval g (pderiv c P) * D (g c) := by
  induction P using MvPolynomial.induction_on
  next r =>
    rw [aeval_C, MvPolynomial.algebraMap_eq, hC]
    simp
  next p q hp hq =>
    rw [map_add (f := _), hadd, hp, hq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [map_add (f := _), map_add (f := _), add_mul]
  next p i ih =>
    have e : ∀ c, aeval g (pderiv c (p * X i)) * D (g c) =
        g i * (aeval g (pderiv c p) * D (g c)) + (if c = i then aeval g p * D (g i) else 0) := by
      intro c
      rw [pderiv_mul_eq, pderiv_X_eq_ite, map_add (f := _), map_mul, map_mul, aeval_X]
      by_cases h : c = i
      · subst h; rw [if_pos rfl, if_pos rfl, map_one]; ring
      · rw [if_neg h, if_neg h, map_zero]; ring
    rw [Finset.sum_congr rfl (fun c _ => e c), Finset.sum_add_distrib, ← Finset.mul_sum, ← ih,
      map_mul, aeval_X, hmul]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring

theorem chainRule : ChainRule := by
  intro K _ m vec a b P
  simp only [PI.RL.theta]
  exact derivation_aeval_eq_sum_pderiv (PI.RL.RE K (m + 1) a b) (RE_add a b) (RE_C a b)
    (RE_mul a b) _ P

theorem vecX : VecX := by
  intro K _ m a b c
  have hp : ∀ t : Fin (m + 1),
      pderiv (b, t) (X (c, 0) : MvPolynomial (Fin (m + 1) × Fin (m + 1)) K) =
        if c = b ∧ t = 0 then 1 else 0 := by
    intro t
    rw [pderiv_X]
    by_cases h : c = b ∧ t = 0
    · obtain ⟨rfl, rfl⟩ := h; simp
    · rw [if_neg h, Pi.single_apply, if_neg]
      intro he
      simp only [Prod.mk.injEq] at he
      exact h ⟨he.1, he.2.symm⟩
  simp only [PI.RL.Nv, if_true, PI.RL.RE, hp, mul_ite, mul_one, mul_zero]
  by_cases h : c = b
  · subst h; simp [Finset.sum_ite_eq']
  · simp [h]

theorem hdHom : HdHom := by
  intro K _ k d P hP
  unfold PI.RL.Hd at hP
  rw [mem_restrictSupport_iff] at hP
  intro μ hμ
  have h2 := hP (mem_support_iff.mpr hμ)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
  simpa using h2

end PI.RL.W
end
end

theorem row_letter_rule : PI.RowLetter :=
  PI.RL.W.rowLetter_of PI.RL.W.chainRule PI.RL.W.vecX PI.RL.W.keyCov PI.RL.W.hdHom
end

section -- merged from Formalism.PeriodIntegrals.OrbitalBoundsConclusion.RowWtSpan
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RowWeightSpan.RowWtSpanOfBideterminant
open MvPolynomial

noncomputable section

namespace PI.RWS

open PI.RW

def rowW {k : ℕ} (a : Fin k) : Fin k × Fin k → ℕ := fun v => if v.1 = a then 1 else 0

theorem RE_eq_of_hom {K : Type} [CommRing K] {k : ℕ} (a : Fin k)
    (f : MvPolynomial (Fin k × Fin k) K) (d : ℕ)
    (h : IsWeightedHomogeneous (rowW a) f d) : RE K k a a f = (d : K) • f := by
  have h' := h.sum_weight_X_mul_pderiv
  unfold RE
  rw [Nat.cast_smul_eq_nsmul K d f, ← h']
  symm
  rw [Fintype.sum_prod_type, Finset.sum_eq_single a (fun x _ hx => by simp [rowW, hx])
    (fun h => absurd (Finset.mem_univ a) h)]
  simp [rowW]

theorem minor_hom {K : Type} [CommRing K] {k s : ℕ} (a : Fin k) (I : Fin s → Fin k) (hs : s ≤ k) :
    IsWeightedHomogeneous (rowW a) (initMinor K I hs)
      (Finset.univ.filter fun p => I p = a).card := by
  unfold initMinor
  rw [Matrix.det_apply]
  refine IsWeightedHomogeneous.sum _ _ _ fun σ _ => ?_
  have hp := IsWeightedHomogeneous.prod Finset.univ
    (fun i => (X (I (σ i), Fin.castLE hs i) : MvPolynomial (Fin k × Fin k) K))
    (fun i => rowW a (I (σ i), Fin.castLE hs i)) (w := rowW a)
    (fun i _ => isWeightedHomogeneous_X K (rowW a) _)
  have hdeg : ∑ i, rowW a (I (σ i), Fin.castLE hs i) =
      (Finset.univ.filter fun p => I p = a).card := by
    simp only [rowW]
    rw [Finset.card_filter]
    exact Equiv.sum_comp σ (fun p => if I p = a then 1 else 0)
  rw [hdeg] at hp
  rw [Units.smul_def, ← mem_weightedHomogeneousSubmodule] at *
  exact zsmul_mem hp _

theorem bidet_hom {K : Type} [CommRing K] {k N : ℕ} (a : Fin k) (sz : Fin N → ℕ)
    (hsz : ∀ j, sz j ≤ k) (I : ∀ j, Fin (sz j) → Fin k) :
    IsWeightedHomogeneous (rowW a) (bideterminant K sz hsz I)
      (∑ j, (Finset.univ.filter fun p => I j p = a).card) := by
  unfold bideterminant
  exact IsWeightedHomogeneous.prod _ _ _ fun j _ => minor_hom a (I j) (hsz j)

theorem wt_le {k N : ℕ} (sz : Fin N → ℕ) (I : ∀ j, Fin (sz j) → Fin k)
    (hI : ∀ j, StrictMono (I j)) (a t0 : Fin k) (ht0 : t0.val = 0) :
    ∑ j, (Finset.univ.filter fun p => I j p = a).card ≤ shapeDeg sz t0 := by
  unfold shapeDeg
  rw [ht0, Finset.card_filter]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : 0 < sz j
  · rw [if_pos hj]
    refine Finset.card_le_one.2 fun p hp q hq => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    exact (hI j).injective (hp.trans hq.symm)
  · rw [if_neg hj]
    have hem : (Finset.univ : Finset (Fin (sz j))) = ∅ :=
      Finset.univ_eq_empty_iff.2 ⟨fun p => hj (lt_of_le_of_lt (Nat.zero_le _) p.2)⟩
    rw [hem]
    simp

theorem rowWtSpan_of_bideterminant (h1 : BideterminantMem) (h2 : BideterminantSpan) : PI.RowWtSpan := by
  intro K _ m ν _
  refine ⟨{d : Σ N : ℕ, Σ sz : Fin N → ℕ, ∀ j, Fin (sz j) → Fin (m + 1) //
      (∀ j, d.2.1 j ≤ m + 1) ∧ shapeDeg d.2.1 = ν ∧ ∀ j, StrictMono (d.2.2 j)},
    fun d => bideterminant K d.1.2.1 d.2.1 d.1.2.2,
    fun d a => ∑ j, (Finset.univ.filter fun p => d.1.2.2 j p = a).card, ?_, ?_, ?_⟩
  · apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨⟨⟨N, sz, I⟩, hsz, hsh, hmono⟩, rfl⟩
      subst hsh
      exact h1 K (m + 1) (m + 1) N sz hsz I
    · refine le_trans (h2 K (m + 1) (m + 1) ν) (Submodule.span_mono ?_)
      rintro f ⟨N, sz, hsz, I, hsh, hmono, rfl⟩
      exact ⟨⟨⟨N, sz, I⟩, hsz, hsh, hmono⟩, rfl⟩
  · rintro ⟨⟨N, sz, I⟩, hsz, hsh, hmono⟩ a
    exact RE_eq_of_hom a _ _ (bidet_hom a sz hsz I)
  · rintro ⟨⟨N, sz, I⟩, hsz, hsh, hmono⟩ a
    have hw := wt_le sz I hmono a 0 rfl
    rw [hsh] at hw
    exact hw

end PI.RWS
end
end

theorem rowWtSpan_of (h1 : PI.RW.BideterminantMem) (h2 : PI.RW.BideterminantSpan) : PI.RowWtSpan :=
  PI.RWS.rowWtSpan_of_bideterminant h1 h2
end

noncomputable section

namespace Formalism.MainNotions.TestSideWords

open Formalism.GradedWeylDivisibility

private theorem initMinor_comp_perm_eq_sign_mul {R : Type} [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n)
    (σ : Equiv.Perm (Fin s)) :
    PI.RW.initMinor R (I ∘ σ) hs =
      ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (Fin r × Fin n) R)) * PI.RW.initMinor R I hs := by
  unfold PI.RW.initMinor
  rw [← Matrix.det_permute σ]
  rfl

private theorem initMinor_eq_zero_of_not_injective {R : Type} [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n)
    (hI : ¬ Function.Injective I) : PI.RW.initMinor R I hs = 0 := by
  unfold PI.RW.initMinor
  simp only [Function.Injective, not_forall] at hI
  obtain ⟨i, j, hij, hne⟩ := hI
  exact Matrix.det_zero_of_row_eq (Ne.symm (Ne.symm hne)) (by
    funext q
    simp [hij])

private theorem initMinor_eq_sign_sort_mul {R : Type} [CommRing R] {r n s : ℕ} (I : Fin s → Fin r) (hs : s ≤ n)
    (hI : Function.Injective I) :
    PI.RW.initMinor R I hs =
      ((((Equiv.Perm.sign (Tuple.sort I) : ℤˣ) : ℤ) : MvPolynomial (Fin r × Fin n) R)) *
        PI.RW.initMinor R (I ∘ Tuple.sort I) hs := by
  rw [initMinor_comp_perm_eq_sign_mul, ← mul_assoc, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

theorem bideterminant_span_holds : PI.RW.BideterminantSpan := by
  intro R _ _ k n ν
  rw [show PI.RW.dualWeyl R k n ν = Formalism.GradedWeylDivisibility.dualWeyl R k n ν from rfl,
    Formalism.GradedWeylDivisibility.standardMonomialSpanDomain R k n ν]
  refine Submodule.span_le.mpr ?_
  rintro f ⟨K, sz, hsz, I, hν, rfl⟩
  by_cases hinj : ∀ i, Function.Injective (I i)
  · have hb : Formalism.GradedWeylDivisibility.bideterminant R sz hsz I =
        (∏ i, ((((Equiv.Perm.sign (Tuple.sort (I i)) : ℤˣ) : ℤ) : MvPolynomial (Fin k × Fin n) R))) *
          PI.RW.bideterminant R sz hsz (fun i => I i ∘ Tuple.sort (I i)) := by
      show (∏ i, PI.RW.initMinor R (I i) (hsz i)) = _
      unfold PI.RW.bideterminant
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl (fun i _ => initMinor_eq_sign_sort_mul (I i) (hsz i) (hinj i))
    rw [hb, ← Int.cast_prod, ← zsmul_eq_mul]
    have hJ : ∀ i, StrictMono (I i ∘ Tuple.sort (I i)) := fun i =>
      (Tuple.monotone_sort (I i)).strictMono_of_injective ((hinj i).comp (Equiv.injective _))
    refine zsmul_mem (Submodule.subset_span ?_) _
    exact ⟨K, sz, hsz, fun i => I i ∘ Tuple.sort (I i), hν, hJ, rfl⟩
  · push_neg at hinj
    obtain ⟨i, hi⟩ := hinj
    have h0 : Formalism.GradedWeylDivisibility.bideterminant R sz hsz I = 0 := by
      show (∏ i, PI.RW.initMinor R (I i) (hsz i)) = 0
      exact Finset.prod_eq_zero (Finset.mem_univ i) (initMinor_eq_zero_of_not_injective (I i) (hsz i) hi)
    rw [h0]
    exact Submodule.zero_mem _

theorem dual_weyl_weights_bounded : Formalism.MainNotions.TestSideCounting.RestWt := rowWtSpan_of bidetMem bideterminant_span_holds

theorem letter_operators_holds : Formalism.MainNotions.TestSideCounting.RestTheta := row_letter_rule

theorem onePos_of_OB (hOB : Formalism.MainNotions.TestSideCounting.OpBound) : Formalism.MainNotions.TestSideCounting.OnePos :=
  Formalism.MainNotions.TestSideCounting.onePos_of_opBound hOB letter_operators_holds dual_weyl_weights_bounded

theorem tensor_operators_of_one_position (h : Formalism.MainNotions.TestSideCounting.OnePos) : Formalism.MainNotions.TestSideCounting.TenOp :=
  adjointTensorOfSingle_valid Formalism.L2.G.Model.TS.Top.fockRBlock h

theorem tenOp_of_OB (hOB : Formalism.MainNotions.TestSideCounting.OpBound) : Formalism.MainNotions.TestSideCounting.TenOp := tensor_operators_of_one_position (onePos_of_OB hOB)

theorem operator_weight_bound_holds : Formalism.MainNotions.TestSideCounting.OpBound := operator_words_bound

theorem tensor_operators_holds : Formalism.MainNotions.TestSideCounting.TenOp := tenOp_of_OB operator_weight_bound_holds

end Formalism.MainNotions.TestSideWords
