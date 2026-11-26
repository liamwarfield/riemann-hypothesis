module

public import Formalism.SharpRestriction.GrowthBounds.SegmentDegree.GoodPathWeight
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoboundaryCriterion

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.MemColRangeOfLeEntry
section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.KillKcolTau
section -- merged from Formalism.SharpRestriction.GrowthBounds.SegmentDegree.ScaleSCoeffZero
noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas

section Kill

variable {R σ : Type} [CommRing R] (S : Set σ)


open Classical in
def kill : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  aeval fun v => if v ∈ S then 0 else MvPolynomial.X v


open Classical in
def scaleS : MvPolynomial σ R →ₐ[R] Polynomial (MvPolynomial σ R) :=
  aeval fun v => if v ∈ S then Polynomial.X * Polynomial.C (MvPolynomial.X v) else Polynomial.C (MvPolynomial.X v)


open Classical in
def offDeg : (σ →₀ ℕ) →+ ℕ := Finsupp.liftAddHom fun v => if v ∈ S then AddMonoidHom.id ℕ else 0

theorem scaleS_monomial (m : σ →₀ ℕ) :
    scaleS (R := R) S (monomial m 1) = Polynomial.C (monomial m 1) * Polynomial.X ^ offDeg S m := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    have : (monomial (f + g) (1 : R)) = monomial f 1 * monomial g 1 := by
      rw [monomial_mul, one_mul]
    rw [this, map_mul, hf, hg, map_add (f := _), pow_add, map_mul]
    ring
  | single v k =>
    rw [← MvPolynomial.X_pow_eq_monomial, map_pow]
    by_cases hv : v ∈ S
    · have h1 : scaleS (R := R) S (MvPolynomial.X v) = Polynomial.X * Polynomial.C (MvPolynomial.X v) := by
        simp [scaleS, hv]
      have h2 : offDeg S (Finsupp.single v k) = k := by simp [offDeg, hv]
      rw [h1, h2, mul_pow, Polynomial.C_pow, mul_comm]
    · have h1 : scaleS (R := R) S (MvPolynomial.X v) = Polynomial.C (MvPolynomial.X v) := by
        simp [scaleS, hv]
      have h2 : offDeg S (Finsupp.single v k) = 0 := by simp [offDeg, hv]
      rw [h1, h2, pow_zero, mul_one, Polynomial.C_pow]

theorem scaleS_coeff_zero (f : MvPolynomial σ R) : (scaleS S f).coeff 0 = kill S f := by
  classical
  have h : (Polynomial.constantCoeff.comp (scaleS (R := R) S : MvPolynomial σ R →+* Polynomial (MvPolynomial σ R))) =
      (kill (R := R) S : MvPolynomial σ R →+* MvPolynomial σ R) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [scaleS, kill, MvPolynomial.algebraMap_eq]
    · intro v
      by_cases hv : v ∈ S <;> simp [scaleS, kill, hv]
  have := congrArg (fun g => g f) h
  simpa [Polynomial.constantCoeff_apply] using this

theorem li_of_kill {ι : Type} (m : ι → σ →₀ ℕ) (w : ι → MvPolynomial σ R)
    (h : LinearIndependent R fun q => monomial (m q) (1 : R) * kill S (w q)) :
    LinearIndependent R fun q => monomial (m q) (1 : R) * w q := by
  classical
  rw [linearIndependent_iff'] at h ⊢
  intro s a hsum
  by_contra hne
  push Not at hne
  obtain ⟨q0, hq0s, hq0⟩ := hne
  let s' := s.filter fun q => a q ≠ 0
  have hs' : s'.Nonempty := ⟨q0, Finset.mem_filter.mpr ⟨hq0s, hq0⟩⟩
  obtain ⟨q1, hq1, hmin⟩ := Finset.exists_min_image s' (fun q => offDeg S (m q)) hs'
  set δ := offDeg S (m q1) with hδ
  have hsum' : ∑ q ∈ s', a q • (monomial (m q) (1 : R) * w q) = 0 := by
    rw [← hsum]
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro q hq hq'
    have : a q = 0 := by
      by_contra hh
      exact hq' (Finset.mem_filter.mpr ⟨hq, hh⟩)
    rw [this, zero_smul]
  have hΘ := congrArg (fun P => (scaleS S P).coeff δ) hsum'
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, map_mul, scaleS_monomial, Polynomial.finsetSum_coeff, Polynomial.coeff_smul,
    map_zero, Polynomial.coeff_zero] at hΘ
  have hterm : ∀ q ∈ s', (Polynomial.C (monomial (m q) (1 : R)) * Polynomial.X ^ offDeg S (m q) *
      scaleS S (w q)).coeff δ = if offDeg S (m q) = δ then monomial (m q) (1 : R) * kill S (w q) else 0 := by
    intro q hq
    rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
    have hle := hmin q hq
    split_ifs with h1 h2 h2
    · rw [h2, Nat.sub_self, scaleS_coeff_zero]
    · exact absurd (le_antisymm h1 hle) h2
    · exact absurd (le_of_eq h2) h1
    · rw [mul_zero]
  rw [Finset.sum_congr rfl fun q hq => by rw [hterm q hq]] at hΘ
  have hΘ' : ∑ q ∈ s'.filter (fun q => offDeg S (m q) = δ), a q • (monomial (m q) (1 : R) * kill S (w q)) = 0 := by
    rw [Finset.sum_filter]
    refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) hΘ
    split_ifs <;> simp
  have := h _ a hΘ' q1 (Finset.mem_filter.mpr ⟨hq1, rfl⟩)
  exact (Finset.mem_filter.mp hq1).2 this

end Kill

namespace Dat

variable {n' r : ℕ} [NeZero n'] (X : Dat n' r) (K : ℕ)


omit [NeZero n'] in
def offSet (j : ℤ) : Set (ℤ × Fin (r + K)) :=
  {v | ∃ t c : Fin r, c ≠ Fin.rev t ∧ v = (X.F.fr j t.val, Fin.castAdd K c)}


omit [NeZero n'] in
def monTau (j : ℤ) (u : Fin r × Fin r → ℕ) : ℤ × Fin (r + K) →₀ ℕ :=
  ∑ v : Fin r × Fin r, Finsupp.single (X.F.fr j v.1.val, Fin.castAdd K v.2) (u v)

def wordEl (O : Type) [CommRing O] (j : ℤ)
    (q : (Fin (segN X.F j + 1) → Fin (r + K) → ℤ) × (ℤ → Finset (Fin K)) × (Fin r × Fin r → ℕ)) : SegRing O r K :=
  segRen X.F j O (r + K) (PsiPl O (plPart q.1) (Ican (plPart q.1)) * PsiTan O (tanPart q.1) q.2.1)

end Dat

def RestKey (C₀ : ℝ) : Prop :=
  ∀ (p n' r K : ℕ) [NeZero n'] [NeZero r] [NeZero K] (X : Dat n' r) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O], UniformizedDVR p O → X.Hyp p K → C₀ ≤ X.CLa → C₀ ≤ X.Ck →
    ∀ (j : ℤ) (b : ℤ → ℕ), X.BOK p K j b →
      LinearIndependent O fun q : X.Idx p K j (X.restr j b) =>
        monomial (X.monTau K j q.1.2.2) (1 : O) * kill (X.offSet K j) (X.wordEl K O j q.1)

theorem fr_injective {n' r : ℕ} [NeZero n'] (F : Frames n' r) {L₁ N₁ : ℕ} (hV : F.Valid L₁ N₁) (j : ℤ) :
    Function.Injective fun a : Fin r => F.fr j a.val := by
  obtain ⟨-, -, h3, -⟩ := hV
  have key : ∀ d a : ℕ, a + d + 1 < r → F.fr j a < F.fr j (a + d + 1) := by
    intro d
    induction d with
    | zero => intro a h; exact h3 j a h
    | succ d ih => intro a h; exact lt_trans (ih a (by omega)) (h3 j (a + d + 1) (by omega))
  intro a b hab
  have hab' : F.fr j a.val = F.fr j b.val := hab
  by_contra hne
  have hne' : a.val ≠ b.val := fun h => hne (Fin.ext h)
  have ha := a.isLt
  have hb := b.isLt
  rcases lt_or_gt_of_ne hne' with h | h
  · have := key (b.val - a.val - 1) a.val (by omega)
    rw [show a.val + (b.val - a.val - 1) + 1 = b.val by omega] at this
    exact absurd hab' (ne_of_lt this)
  · have := key (a.val - b.val - 1) b.val (by omega)
    rw [show b.val + (a.val - b.val - 1) + 1 = a.val by omega] at this
    exact absurd hab'.symm (ne_of_lt this)

theorem plEmb_injective (O : Type) [CommRing O] (r K : ℕ) : Function.Injective (plEmb O r K) := by
  apply rename_injective
  intro a b h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext h.1 (Fin.castAdd_injective _ _ h.2)

theorem restInd_of (C₀ : ℝ) (hK : RestKey C₀) : RestInd C₀ := by
  intro p n' r K _ _ _ X O _ _ _ S hX hLa hk j b hB
  have h1 := li_of_kill (X.offSet K j) (fun q : X.Idx p K j (X.restr j b) => X.monTau K j q.1.2.2)
    (fun q => X.wordEl K O j q.1) (hK p n' r K X O S hX hLa hk j b hB)
  set c0 : MvPolynomial (ℤ × Fin r) O := X.Dw O j ^ X.m0 K *
      (∏ i : Fin r, MvPolynomial.X (X.F.fr (j - 1) i.val, (0 : Fin r)) ^
        ((b (X.F.fr (j - 1) i.val) : ℤ) - X.Bw p K j (X.F.fr (j - 1) i.val)).toNat) with hc0
  have hD : X.Dw O j ≠ 0 := Formalism.MainNotions.G.Joints.StandardMonomialSpace.detX_ne_zero _ (fr_injective X.F hX.valid (j - 1))
  have hc0ne : c0 ≠ 0 := by
    refine mul_ne_zero (pow_ne_zero _ hD) (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (X_ne_zero _))
  have hc : plEmb O r K c0 ≠ 0 := (map_ne_zero_iff _ (plEmb_injective O r K)).mpr hc0ne
  have h2 := h1.map' (LinearMap.mulLeft O (plEmb O r K c0))
    (LinearMap.ker_eq_bot.mpr fun x y hxy => mul_left_cancel₀ hc hxy)
  have heq : (fun q : X.Idx p K j (X.restr j b) => X.famEl p K O j b q.1) =
      (⇑(LinearMap.mulLeft O ((plEmb O r K) c0)) ∘
        fun q : X.Idx p K j (X.restr j b) => (monomial (X.monTau K j q.1.2.2)) (1 : O) * X.wordEl K O j q.1) := by
    funext q
    simp only [Function.comp, LinearMap.mulLeft_apply]
    unfold Dat.famEl Dat.wordEl Dat.monTau
    rw [map_mul, ← hc0, mul_assoc]
    congr 2
    rw [MvPolynomial.monomial_sum_one, map_prod]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_pow, ← MvPolynomial.X_pow_eq_monomial]
    simp [plEmb]
  rw [heq]
  exact h2

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Abs

variable {R : Type} [CommRing R] {N r : ℕ}

def stg (ν : Fin (N + 1) → Fin r → ℤ) (i : ℕ) : Fin r → ℤ := if h : i < N + 1 then ν ⟨i, h⟩ else 0

theorem stg_eq (ν : Fin (N + 1) → Fin r → ℤ) (i : ℕ) (h : i < N + 1) : ν ⟨i, h⟩ = stg ν i := by
  simp [stg, h]

theorem Kcol_succ (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (j : ℕ) (h : j < N) :
    Kcol R ν c (j + 1) =
      colStep c (colH (stg ν j) c) (colH (stg ν (j + 1)) c) (letVec R ⟨j, h⟩) (Kcol R ν c j) := by
  rw [Kcol, dite_eq_left h, stg_eq ν j (by omega), stg_eq ν (j + 1) (by omega)]

def offN (n0 : ℕ) : Set (Fin N × Fin r) := {v | n0 ≤ v.1.val ∧ v.2.val + (v.1.val - n0) + 1 ≠ r}

theorem kill_colStep (S : Set (Fin N × Fin r)) (c : ℤ) (hP hN : ℕ) (x : Fin r → MvPolynomial (Fin N × Fin r) R)
    (Kf : Finset (Fin r) → MvPolynomial (Fin N × Fin r) R) (J : Finset (Fin r)) :
    kill S (colStep c hP hN x Kf J) = colStep c hP hN (fun m => kill S (x m)) (fun J => kill S (Kf J)) J :=
  lift_colStep_map (kill (R := R) S : MvPolynomial (Fin N × Fin r) R →+* MvPolynomial (Fin N × Fin r) R) c hP hN x Kf J

theorem kill_X_not (S : Set (Fin N × Fin r)) (v : Fin N × Fin r) (hv : v ∉ S) :
    kill (R := R) S (MvPolynomial.X v) = MvPolynomial.X v := by
  simp [kill, hv]

theorem kill_X_mem (S : Set (Fin N × Fin r)) (v : Fin N × Fin r) (hv : v ∈ S) :
    kill (R := R) S (MvPolynomial.X v) = 0 := by
  simp [kill, hv]

theorem kill_Kcol_low (n0 : ℕ) (hn : n0 ≤ N) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) :
    ∀ j ≤ n0, ∀ J, kill (offN n0) (Kcol R ν c j J) = Kcol R ν c j J := by
  intro j
  induction j with
  | zero =>
    intro _ J
    exact lift_extOne_map (kill (R := R) (offN (N := N) (r := r) n0) :
      MvPolynomial (Fin N × Fin r) R →+* MvPolynomial (Fin N × Fin r) R) J
  | succ j ih =>
    intro hj J
    have hjN : j < N := by omega
    rw [Kcol_succ ν c j hjN, kill_colStep]
    have e1 : (fun m => kill (offN n0) (letVec R (N := N) (n := r) ⟨j, hjN⟩ m)) = letVec R ⟨j, hjN⟩ := by
      funext m
      apply kill_X_not
      intro hv
      have : n0 ≤ j := hv.1
      omega
    have e2 : (fun J => kill (offN n0) (Kcol R ν c j J)) = Kcol R ν c j := funext (ih (by omega))
    rw [e1, e2]

variable (n0 : ℕ) (hN : n0 + r = N)

def tauI (m : Fin r) : Fin N := ⟨n0 + (r - 1 - m.val), by have := m.isLt; omega⟩

def rises (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (i : ℕ) : Prop := colH (stg ν i) c < colH (stg ν (i + 1)) c


open Classical in
def riseA (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (t : ℕ) : Finset (Fin r) :=
  Finset.univ.filter fun m => r - 1 - m.val < t ∧ rises ν c (n0 + (r - 1 - m.val))

theorem kill_Kcol_tau (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (hc : 1 ≤ c)
    (hmono : ∀ t < r, colH (stg ν (n0 + t)) c ≤ colH (stg ν (n0 + t + 1)) c) :
    ∀ t ≤ r, ∀ J, riseA n0 ν c t ⊆ J → ∃ e : ℕ, kill (offN n0) (Kcol R ν c (n0 + t) J) =
      (-1) ^ e * (∏ m ∈ riseA n0 ν c t, MvPolynomial.X (tauI n0 hN m, m)) * Kcol R ν c n0 (J \ riseA n0 ν c t) := by
  classical
  intro t
  induction t with
  | zero =>
    intro _ J _
    refine ⟨0, ?_⟩
    have : riseA n0 ν c 0 = ∅ := by
      simp [riseA]
    rw [this]
    simp only [add_zero, pow_zero, Finset.prod_empty, mul_one, one_mul, Finset.sdiff_empty]
    exact kill_Kcol_low n0 (by omega) ν c n0 le_rfl J
  | succ t ih =>
    intro ht J hJ
    have htr : t < r := by omega
    have hjN : n0 + t < N := by omega
    let mt : Fin r := ⟨r - 1 - t, by omega⟩
    have hmt : r - 1 - mt.val = t := by simp only [mt]; omega
    have hval : ∀ m : Fin r, r - 1 - m.val = t → m = mt := by
      intro m hm
      apply Fin.ext
      have := m.isLt
      simp only [mt]; omega
    rw [show n0 + (t + 1) = n0 + t + 1 by ring, Kcol_succ ν c (n0 + t) hjN, kill_colStep]
    by_cases hr : rises ν c (n0 + t)
    · have hA : riseA n0 ν c (t + 1) = insert mt (riseA n0 ν c t) := by
        ext m
        simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases h3 : r - 1 - m.val = t
          · exact Or.inl (hval m h3)
          · exact Or.inr ⟨by omega, h2⟩
        · rintro (h | ⟨h1, h2⟩)
          · subst h
            rw [hmt]; exact ⟨by omega, hr⟩
          · exact ⟨by omega, h2⟩
      have hnot : mt ∉ riseA n0 ν c t := by
        simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
        intro h; rw [hmt] at h; omega
      have hmJ : mt ∈ J := hJ (by rw [hA]; exact Finset.mem_insert_self _ _)
      have hsub : riseA n0 ν c t ⊆ J.erase mt := by
        intro m hm
        refine Finset.mem_erase.mpr ⟨fun h => hnot (h ▸ hm), hJ (by rw [hA]; exact Finset.mem_insert_of_mem hm)⟩
      obtain ⟨e, he⟩ := ih (by omega) (J.erase mt) hsub
      have hstep : colStep c (colH (stg ν (n0 + t)) c) (colH (stg ν (n0 + t + 1)) c)
          (fun m => kill (offN n0) (letVec R (N := N) (n := r) ⟨n0 + t, hjN⟩ m))
          (fun J => kill (offN n0) (Kcol R ν c (n0 + t) J)) J =
          (-1) ^ (J.filter fun j => mt < j).card * MvPolynomial.X (tauI n0 hN mt, mt) *
            kill (offN n0) (Kcol R ν c (n0 + t) (J.erase mt)) := by
        have hr' : colH (stg ν (n0 + t)) c < colH (stg ν (n0 + t + 1)) c := hr
        unfold colStep
        rw [if_pos hr', if_pos hc]
        unfold wedgeR
        rw [Finset.sum_eq_single mt]
        · congr 2
          have : (tauI n0 hN mt : Fin N) = ⟨n0 + t, hjN⟩ := by
            apply Fin.ext; simp only [tauI]; omega
          rw [this]
          apply kill_X_not
          intro hv
          apply hv.2
          simp only [mt]; omega
        · intro m _ hm
          have : kill (offN n0) (letVec R (N := N) (n := r) ⟨n0 + t, hjN⟩ m) = 0 := by
            apply kill_X_mem
            refine ⟨by simp, ?_⟩
            intro h
            apply hm
            apply hval
            simp only [add_tsub_cancel_left] at h
            omega
          beta_reduce
          rw [this]; ring
        · intro h; exact absurd hmJ h
      rw [hstep, he, hA, Finset.prod_insert hnot]
      refine ⟨(J.filter fun j => mt < j).card + e, ?_⟩
      have hset : J.erase mt \ riseA n0 ν c t = J \ insert mt (riseA n0 ν c t) := by
        ext m
        simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert, not_or]
        tauto
      rw [hset, pow_add]
      ring
    · have hA : riseA n0 ν c (t + 1) = riseA n0 ν c t := by
        ext m
        simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨h1, h2⟩
          by_cases h3 : r - 1 - m.val = t
          · rw [h3] at h2; exact absurd h2 hr
          · exact ⟨by omega, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨by omega, h2⟩
      have heq : colH (stg ν (n0 + t)) c = colH (stg ν (n0 + t + 1)) c :=
        le_antisymm (hmono t htr) (not_lt.mp hr)
      rw [hA] at hJ ⊢
      obtain ⟨e, he⟩ := ih (by omega) J hJ
      refine ⟨e, ?_⟩
      unfold colStep
      rw [heq, if_neg (lt_irrefl _), if_neg (lt_irrefl _)]
      exact he

end Abs

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Abs2

variable {R : Type} [CommRing R] {N r : ℕ}

theorem colStep_same (c : ℤ) (h : ℕ) (x : Fin r → MvPolynomial (Fin N × Fin r) R)
    (Kf : Finset (Fin r) → MvPolynomial (Fin N × Fin r) R) : colStep c h h x Kf = Kf := by
  unfold colStep
  rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]

theorem Kcol_const (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) :
    ∀ j ≤ N, (∀ i < j, colH (stg ν i) c = colH (stg ν (i + 1)) c) → Kcol R ν c j = extOne := by
  intro j
  induction j with
  | zero => intro _ _; rw [Kcol]
  | succ j ih =>
    intro hj h
    rw [Kcol_succ ν c j (by omega), h j (by omega), colStep_same]
    exact ih (by omega) fun i hi => h i (by omega)

def cutPath (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) : Fin (N + 1) → Fin r → ℤ := fun i => stg ν (min i.val n0)

theorem stg_cut (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (i : ℕ) (hi : i ≤ N) :
    stg (cutPath n0 ν) i = stg ν (min i n0) := by
  have : i < N + 1 := by omega
  simp [stg, cutPath, this]

theorem Kcol_cut (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) :
    ∀ j ≤ N, Kcol R (cutPath n0 ν) c j = Kcol R ν c (min j n0) := by
  intro j
  induction j with
  | zero => intro _; rw [Nat.zero_min, Kcol, Kcol]
  | succ j ih =>
    intro hj
    rw [Kcol_succ _ c j (by omega), stg_cut n0 ν j (by omega), stg_cut n0 ν (j + 1) hj, ih (by omega)]
    by_cases h : j + 1 ≤ n0
    · rw [min_eq_left h, min_eq_left (by omega : j ≤ n0), Kcol_succ ν c j (by omega)]
    · rw [min_eq_right (by omega : n0 ≤ j + 1), min_eq_right (by omega : n0 ≤ j), colStep_same]

theorem colH_all {μ : Fin r → ℤ} {c : ℤ} (h : ∀ m, c ≤ μ m) : colH μ c = r := by
  unfold colH
  rw [Finset.filter_true_of_mem fun m _ => h m, Finset.card_univ, Fintype.card_fin]

theorem colH_none {μ : Fin r → ℤ} {c : ℤ} (h : ∀ m, μ m < c) : colH μ c = 0 := by
  unfold colH
  rw [Finset.filter_false_of_mem fun m _ => not_le.mpr (h m), Finset.card_empty]

theorem colH_anti (μ : Fin r → ℤ) {c c' : ℤ} (h : c ≤ c') : colH μ c' ≤ colH μ c := by
  unfold colH
  exact Finset.card_le_card fun m hm => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
    omega

structure PlHyp (n0 : ℕ) (be : ℤ) (ν : Fin (N + 1) → Fin r → ℤ) : Prop where
  rng : ∀ i ≤ N, ∀ m, 0 ≤ stg ν i m ∧ stg ν i m ≤ be
  fin : ∀ m, stg ν N m = be
  up : ∀ t < r, ∀ c, colH (stg ν (n0 + t)) c ≤ colH (stg ν (n0 + t + 1)) c ∧
    colH (stg ν (n0 + t + 1)) c ≤ colH (stg ν (n0 + t)) c + 1

def mT (t : ℕ) (ht : t < r) : Fin r := ⟨r - 1 - t, by omega⟩

theorem riseA_succ_pos (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (t : ℕ) (ht : t < r)
    (hr : rises ν c (n0 + t)) :
    riseA n0 ν c (t + 1) = insert (mT t ht) (riseA n0 ν c t) ∧ mT t ht ∉ riseA n0 ν c t := by
  classical
  have hmt : r - 1 - (mT t ht).val = t := by simp only [mT]; omega
  constructor
  · ext m
    simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases h3 : r - 1 - m.val = t
      · left
        apply Fin.ext
        have := m.isLt
        simp only [mT]; omega
      · exact Or.inr ⟨by omega, h2⟩
    · rintro (h | ⟨h1, h2⟩)
      · subst h
        rw [hmt]; exact ⟨by omega, hr⟩
      · exact ⟨by omega, h2⟩
  · simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, not_and]
    intro h; rw [hmt] at h; omega

theorem riseA_succ_neg (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (t : ℕ)
    (hr : ¬ rises ν c (n0 + t)) : riseA n0 ν c (t + 1) = riseA n0 ν c t := by
  classical
  ext m
  simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases h3 : r - 1 - m.val = t
    · rw [h3] at h2; exact absurd h2 hr
    · exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩

theorem card_riseA {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) (c : ℤ) :
    ∀ t ≤ r, colH (stg ν n0) c + (riseA n0 ν c t).card = colH (stg ν (n0 + t)) c := by
  classical
  intro t
  induction t with
  | zero =>
    intro _
    have : riseA n0 ν c 0 = ∅ := by simp [riseA]
    rw [this]; simp
  | succ t ih =>
    intro ht
    have htr : t < r := by omega
    have h := ih (by omega)
    obtain ⟨u1, u2⟩ := H.up t htr c
    by_cases hr : rises ν c (n0 + t)
    · obtain ⟨hA, hnot⟩ := riseA_succ_pos n0 ν c t htr hr
      rw [hA, Finset.card_insert_of_notMem hnot]
      have hr' : colH (stg ν (n0 + t)) c < colH (stg ν (n0 + t + 1)) c := hr
      rw [show n0 + (t + 1) = n0 + t + 1 by ring]
      omega
    · rw [riseA_succ_neg n0 ν c t hr]
      have hr' : ¬ colH (stg ν (n0 + t)) c < colH (stg ν (n0 + t + 1)) c := hr
      rw [show n0 + (t + 1) = n0 + t + 1 by ring]
      omega

theorem pEnd_eq (ν : Fin (N + 1) → Fin r → ℤ) : pEnd ν = stg ν N := by
  unfold pEnd
  rw [← stg_eq ν N (by omega)]
  rfl

theorem Ican_eq [NeZero r] {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) (c : ℤ) :
    Ican ν c = if 1 ≤ c ∧ c ≤ be then Finset.univ else ∅ := by
  classical
  have hbe : 0 ≤ be := by
    have := (H.rng N le_rfl 0).1
    rwa [H.fin] at this
  unfold Ican
  rw [pEnd_eq]
  by_cases h1 : 1 ≤ c
  · rw [if_pos h1]
    by_cases h2 : c ≤ be
    · rw [if_pos ⟨h1, h2⟩, colH_all fun m => by rw [H.fin]; exact h2]
      exact Finset.filter_true_of_mem fun m _ => m.isLt
    · rw [if_neg (fun h => h2 h.2), colH_none fun m => by rw [H.fin]; omega]
      exact Finset.filter_false_of_mem fun m _ => by omega
  · rw [if_neg h1, if_neg (fun h => h1 h.1), colH_all fun m => by rw [H.fin]; omega]
    exact Finset.filter_false_of_mem fun m _ => by have := m.isLt; omega

def Icut (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) : ℤ → Finset (Fin r) := fun c => Ican ν c \ riseA n0 ν c r

theorem Kcol_inactive {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) (c : ℤ)
    (hc : ¬ (1 ≤ c ∧ c ≤ be)) (j : ℕ) (hj : j ≤ N) : Kcol R ν c j = extOne := by
  apply Kcol_const ν c j hj
  intro i hi
  by_cases h1 : 1 ≤ c
  · have h2 : be < c := by
      by_contra h; exact hc ⟨h1, by omega⟩
    rw [colH_none fun m => lt_of_le_of_lt (H.rng i (by omega) m).2 h2,
      colH_none fun m => lt_of_le_of_lt (H.rng (i + 1) (by omega) m).2 h2]
  · rw [colH_all fun m => le_trans (by omega) (H.rng i (by omega) m).1,
      colH_all fun m => le_trans (by omega) (H.rng (i + 1) (by omega) m).1]

theorem extOne_empty {P : Type} [CommRing P] : (extOne (n := r) (P := P) ∅) = 1 := by
  simp [extOne]

theorem mem_colRange_of_le_entry (μ : Fin (N + 1) → Fin r → ℤ) (i : Fin (N + 1)) (m : Fin r) {c : ℤ} (h1 : 0 ≤ c)
    (h2 : c ≤ μ i m) : c ∈ colRange μ := by
  unfold colRange
  have hT : |μ i m| ≤ ∑ i, ∑ m, |μ i m| := by
    refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ m, |μ i m|)
      (fun i _ => Finset.sum_nonneg fun m _ => abs_nonneg _) (Finset.mem_univ i))
    exact Finset.single_le_sum (f := fun m => |μ i m|) (fun m _ => abs_nonneg _) (Finset.mem_univ m)
  have := le_abs_self (μ i m)
  simp only [Finset.mem_Icc]
  constructor <;> omega

theorem Psi_full [NeZero r] {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) :
    Psi R ν (Ican ν) = ∏ c ∈ Finset.Icc 1 be, Kcol R ν c N Finset.univ := by
  classical
  unfold Psi
  symm
  have hsub : Finset.Icc 1 be ⊆ colRange ν := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    refine mem_colRange_of_le_entry ν (Fin.last N) 0 (by omega) ?_
    have := H.fin 0
    rw [← stg_eq ν N (by omega)] at this
    have h' : ν (Fin.last N) 0 = be := this
    rw [h']; exact hc.2
  rw [← Finset.prod_subset hsub]
  · refine Finset.prod_congr rfl fun c hc => ?_
    rw [Finset.mem_Icc] at hc
    rw [Ican_eq H, if_pos hc]
  · intro c _ hc
    rw [Finset.mem_Icc] at hc
    rw [Ican_eq H, if_neg hc, Kcol_inactive H c hc N le_rfl, extOne_empty]

theorem Psi_cut [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) :
    Psi R (cutPath n0 ν) (Icut n0 ν) = ∏ c ∈ Finset.Icc 1 be, Kcol R ν c n0 (Finset.univ \ riseA n0 ν c r) := by
  classical
  unfold Psi
  have hterm : ∀ c, Kcol R (cutPath n0 ν) c N (Icut n0 ν c) =
      if 1 ≤ c ∧ c ≤ be then Kcol R ν c n0 (Finset.univ \ riseA n0 ν c r) else 1 := by
    intro c
    rw [Kcol_cut n0 ν c N le_rfl, min_eq_right (by omega : n0 ≤ N)]
    unfold Icut
    rw [Ican_eq H]
    split_ifs with h
    · rfl
    · rw [Finset.empty_sdiff, Kcol_inactive H c h n0 (by omega), extOne_empty]
  rw [Finset.prod_congr rfl fun c _ => hterm c]
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one]

  have hsub : (colRange (cutPath n0 ν)).filter (fun c => 1 ≤ c ∧ c ≤ be) ⊆ Finset.Icc 1 be := by
    intro c hc
    rw [Finset.mem_filter] at hc
    exact Finset.mem_Icc.mpr hc.2
  refine Finset.prod_subset hsub ?_
  intro c hc hnot
  rw [Finset.mem_Icc] at hc
  have hout : c ∉ colRange (cutPath n0 ν) := fun h => hnot (Finset.mem_filter.mpr ⟨h, hc⟩)
  have hlow : ∀ i ≤ n0, ∀ m, stg ν i m < c := by
    intro i hi m
    by_contra hge
    apply hout
    refine mem_colRange_of_le_entry (cutPath n0 ν) ⟨i, by omega⟩ m (by omega) ?_
    have : cutPath n0 ν ⟨i, by omega⟩ m = stg ν i m := by
      simp [cutPath, min_eq_left hi]
    rw [this]; omega
  have h0 : colH (stg ν n0) c = 0 := colH_none (hlow n0 le_rfl)
  have hcard := card_riseA H c r le_rfl
  rw [h0, hN, colH_all fun m => by rw [H.fin]; exact hc.2, zero_add] at hcard
  have hall : riseA n0 ν c r = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcard, Fintype.card_fin]
  rw [hall, Finset.sdiff_self, Kcol_const ν c n0 (by omega) fun i hi => by
    rw [colH_none (hlow i (by omega)), colH_none (hlow (i + 1) (by omega))], extOne_empty]

theorem kill_Psi [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) :
    ∃ e : ℕ, kill (offN n0) (Psi R ν (Ican ν)) =
      (-1) ^ e * (∏ c ∈ Finset.Icc 1 be, ∏ m ∈ riseA n0 ν c r, MvPolynomial.X (tauI n0 hN m, m)) *
        Psi R (cutPath n0 ν) (Icut n0 ν) := by
  classical
  rw [Psi_full H, Psi_cut hN H, map_prod]
  have hcol : ∀ c ∈ Finset.Icc 1 be, ∃ e : ℕ, kill (offN n0) (Kcol R ν c N Finset.univ) =
      (-1) ^ e * (∏ m ∈ riseA n0 ν c r, MvPolynomial.X (tauI n0 hN m, m)) *
        Kcol R ν c n0 (Finset.univ \ riseA n0 ν c r) := by
    intro c hc
    rw [Finset.mem_Icc] at hc
    have := kill_Kcol_tau (R := R) n0 hN ν c hc.1 (fun t ht => (H.up t ht c).1) r le_rfl Finset.univ
      (Finset.subset_univ _)
    rwa [hN] at this
  choose! e he using hcol
  refine ⟨∑ c ∈ Finset.Icc 1 be, e c, ?_⟩
  rw [Finset.prod_congr rfl he, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]

end Abs2

end Formalism.MainNotions.SelectionLemmas.Pf
end
end

noncomputable section

open MvPolynomial

namespace Formalism.MainNotions.SelectionLemmas.Pf

open Formalism.MainNotions.G Formalism.MainNotions.SelectionLemmas Formalism.MainNotions.G.Joints.StandardMonomialSpace

section Abs3

variable {N r : ℕ}

theorem Icut_eq [NeZero r] {n0 : ℕ} {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) (c : ℤ) :
    Icut n0 ν c = if 1 ≤ c ∧ c ≤ be then Finset.univ \ riseA n0 ν c r else ∅ := by
  classical
  unfold Icut
  rw [Ican_eq H]
  split_ifs
  · rfl
  · exact Finset.empty_sdiff _

theorem pEnd_cut {n0 : ℕ} (hn : n0 ≤ N) (ν : Fin (N + 1) → Fin r → ℤ) : pEnd (cutPath n0 ν) = stg ν n0 := by
  rw [pEnd_eq, stg_cut n0 ν N le_rfl, min_eq_right hn]

theorem riseA_filter (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) (t : Fin r) :
    (riseA n0 ν c r).filter (· ≤ t) = riseA n0 ν c r \ riseA n0 ν c (r - 1 - t.val) := by
  classical
  ext m
  have hm := m.isLt
  have ht := t.isLt
  simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff, not_and]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, h2⟩, fun h4 => ?_⟩
    have : m.val ≤ t.val := h3
    omega
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, h2⟩, ?_⟩
    by_contra h4
    have h5 : t.val < m.val := not_le.mp h4
    exact h3 (by omega) h2

theorem riseA_mono (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) {s t : ℕ} (h : s ≤ t) :
    riseA n0 ν c s ⊆ riseA n0 ν c t := by
  classical
  intro m
  simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]
  rintro ⟨h1, h2⟩
  exact ⟨by omega, h2⟩

theorem card_Icut_filter [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ}
    (H : PlHyp n0 be ν) (c : ℤ) (hc : 1 ≤ c ∧ c ≤ be) (t : Fin r) :
    ((Finset.univ \ riseA n0 ν c r).filter (· ≤ t)).card + r =
      t.val + 1 + colH (stg ν (n0 + (r - 1 - t.val))) c := by
  classical
  have ht := t.isLt
  have h1 : ((Finset.univ \ riseA n0 ν c r).filter (· ≤ t)).card + ((riseA n0 ν c r).filter (· ≤ t)).card =
      t.val + 1 := by
    rw [← Finset.card_union_of_disjoint]
    · have : (Finset.univ \ riseA n0 ν c r).filter (· ≤ t) ∪ (riseA n0 ν c r).filter (· ≤ t) = Finset.Iic t := by
        ext m
        simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_Iic]
        tauto
      rw [this, Fin.card_Iic]
    · rw [Finset.disjoint_left]
      intro m hm hm'
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and] at hm hm'
      exact hm.1 hm'.1
  have h2 : ((riseA n0 ν c r).filter (· ≤ t)).card + (riseA n0 ν c (r - 1 - t.val)).card = (riseA n0 ν c r).card := by
    rw [riseA_filter, Finset.card_sdiff_add_card_eq_card (riseA_mono n0 ν c (by omega))]
  have h3 := card_riseA H c r le_rfl
  have h4 := card_riseA H c (r - 1 - t.val) (by omega)
  have hNr : colH (stg ν N) c = r := colH_all fun m => by rw [H.fin]; exact hc.2
  rw [hN, hNr] at h3
  omega

theorem isSt_cut [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν : Fin (N + 1) → Fin r → ℤ} (H : PlHyp n0 be ν) :
    IsSt (cutPath n0 ν) (Icut n0 ν) := by
  classical
  have hcard : ∀ c, (Icut n0 ν c).card =
      if 1 ≤ c then colH (pEnd (cutPath n0 ν)) c else r - colH (pEnd (cutPath n0 ν)) c := by
    intro c
    rw [pEnd_cut (by omega), Icut_eq H]
    by_cases h1 : 1 ≤ c
    · rw [if_pos h1]
      by_cases h2 : c ≤ be
      · rw [if_pos ⟨h1, h2⟩, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin]
        have h3 := card_riseA H c r le_rfl
        have hNr : colH (stg ν N) c = r := colH_all fun m => by rw [H.fin]; exact h2
        rw [hN, hNr] at h3
        omega
      · rw [if_neg fun h => h2 h.2, Finset.card_empty,
          colH_none fun m => lt_of_le_of_lt (H.rng n0 (by omega) m).2 (by omega)]
    · rw [if_neg h1, if_neg fun h => h1 h.1, Finset.card_empty,
        colH_all fun m => le_trans (by omega) (H.rng n0 (by omega) m).1]
      omega
  refine ⟨?_, hcard, ?_⟩
  · intro c hc
    by_cases h : 1 ≤ c ∧ c ≤ be
    · rw [← Finset.card_eq_zero, hcard c, if_pos h.1, pEnd_cut (by omega)]
      apply colH_none
      intro m
      by_contra hge
      apply hc
      refine mem_colRange_of_le_entry (cutPath n0 ν) ⟨n0, by omega⟩ m (by omega) ?_
      have : cutPath n0 ν ⟨n0, by omega⟩ m = stg ν n0 m := by simp [cutPath]
      rw [this]; omega
    · rw [Icut_eq H, if_neg h]
  · intro c t
    unfold tabCol
    by_cases h1 : 1 ≤ c
    · rw [if_pos h1, if_pos (by omega : (1 : ℤ) ≤ c + 1), Icut_eq H, Icut_eq H]
      by_cases h2 : c + 1 ≤ be
      · rw [if_pos ⟨by omega, h2⟩, if_pos ⟨h1, by omega⟩]
        have e1 := card_Icut_filter hN H (c + 1) ⟨by omega, h2⟩ t
        have e2 := card_Icut_filter hN H c ⟨h1, by omega⟩ t
        have e3 := colH_anti (stg ν (n0 + (r - 1 - t.val))) (by omega : c ≤ c + 1)
        omega
      · rw [if_neg fun h => h2 h.2]
        simp
    · rw [if_neg h1]
      have hc0 : Icut n0 ν c = ∅ := by rw [Icut_eq H, if_neg fun h => h1 h.1]
      rw [hc0, Finset.sdiff_empty]
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))

theorem le_iff_lt_colH {μ : Fin r → ℤ} (hμ : Antitone μ) (c : ℤ) (m : Fin r) : c ≤ μ m ↔ m.val < colH μ c := by
  first | exact UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH .. | (apply UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> assumption) | (intros; apply UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> assumption) | (apply @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r μ hμ c m | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r μ hμ c | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r μ hμ | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r μ | exact @UpperTheory.Reformulated.B.Qk46.le_iff_lt_colH r

theorem eq_of_colH {μ μ' : Fin r → ℤ} (hμ : Antitone μ) (hμ' : Antitone μ') (h : ∀ c, colH μ c = colH μ' c) :
    μ = μ' := by
  funext m
  apply le_antisymm
  · rw [le_iff_lt_colH hμ', ← h, ← le_iff_lt_colH hμ]
  · rw [le_iff_lt_colH hμ, h, ← le_iff_lt_colH hμ']

theorem riseA_eq_filter (n0 : ℕ) (ν : Fin (N + 1) → Fin r → ℤ) (c : ℤ) {t : ℕ} (ht : t ≤ r) :
    riseA n0 ν c t = (riseA n0 ν c r).filter fun m => r - 1 - m.val < t := by
  classical
  ext m
  have := m.isLt
  simp only [riseA, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨⟨by omega, h2⟩, h1⟩
  · rintro ⟨⟨_, h2⟩, h1⟩; exact ⟨h1, h2⟩

theorem path_eq_of_cut [NeZero r] {n0 : ℕ} (hN : n0 + r = N) {be : ℤ} {ν ν' : Fin (N + 1) → Fin r → ℤ}
    (H : PlHyp n0 be ν) (H' : PlHyp n0 be ν') (hd : ∀ i, Antitone (ν i)) (hd' : ∀ i, Antitone (ν' i))
    (hcut : cutPath n0 ν = cutPath n0 ν') (hI : Icut n0 ν = Icut n0 ν') : ν = ν' := by
  classical
  have hlow : ∀ i ≤ n0, stg ν i = stg ν' i := by
    intro i hi
    have h1 := stg_cut n0 ν i (by omega)
    have h2 := stg_cut n0 ν' i (by omega)
    rw [min_eq_left hi] at h1 h2
    rw [← h1, ← h2, hcut]
  have hrise : ∀ c, 1 ≤ c ∧ c ≤ be → riseA n0 ν c r = riseA n0 ν' c r := by
    intro c hc
    have h1 := congrFun hI c
    rw [Icut_eq H, Icut_eq H', if_pos hc, if_pos hc] at h1
    have := congrArg (fun s => Finset.univ \ s) h1
    simpa [Finset.sdiff_sdiff_eq_self (Finset.subset_univ _)] using this
  funext i
  rw [stg_eq ν i.val i.isLt, stg_eq ν' i.val i.isLt]
  by_cases hi : i.val ≤ n0
  · exact hlow i.val hi
  · obtain ⟨t, ht⟩ : ∃ t, i.val = n0 + t := ⟨i.val - n0, by omega⟩
    have hi' := i.isLt
    have htr : t ≤ r := by omega
    apply eq_of_colH
    · rw [← stg_eq ν i.val i.isLt]; exact hd i
    · rw [← stg_eq ν' i.val i.isLt]; exact hd' i
    intro c
    rw [ht]
    by_cases hc : 1 ≤ c ∧ c ≤ be
    · rw [← card_riseA H c t htr, ← card_riseA H' c t htr, hlow n0 le_rfl, riseA_eq_filter n0 ν c htr,
        riseA_eq_filter n0 ν' c htr, hrise c hc]
    · by_cases h1 : 1 ≤ c
      · have h2 : be < c := by
          by_contra h; exact hc ⟨h1, by omega⟩
        rw [colH_none fun m => lt_of_le_of_lt (H.rng _ (by omega) m).2 h2,
          colH_none fun m => lt_of_le_of_lt (H'.rng _ (by omega) m).2 h2]
      · rw [colH_all fun m => le_trans (by omega) (H.rng _ (by omega) m).1,
          colH_all fun m => le_trans (by omega) (H'.rng _ (by omega) m).1]

end Abs3

end Formalism.MainNotions.SelectionLemmas.Pf
