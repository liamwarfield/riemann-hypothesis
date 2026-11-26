module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Tensor
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.OneMemDualWeyl

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.ProdSmulPowT
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

def ExistsIO : Prop :=
  ∀ (K : Type) [Field K] (S α : Type) [Fintype S] [DecidableEq S] (TT : Finset S)
    (i : TT → MvPolynomial α K →ₗ[K] MvPolynomial (Bool × α) K),
    ∃ IO : MvPolynomial (S × α) K →ₗ[K] MvPolynomial ((TT × Bool) × α) K, ∀ P : S → MvPolynomial α K,
      (∀ s, s ∉ TT → P s = 1) → IO (∏ s, rename (fun v => (s, v)) (P s)) =
        ∏ s : TT, rename (fun v : Bool × α => ((s, v.1), v.2)) (i s (P s.val))

def ExistsPR : Prop :=
  ∀ (K : Type) [Field K] (S α : Type) [Fintype S] [DecidableEq S] (TT : Finset S)
    (pr : TT → MvPolynomial (Bool × α) K →ₗ[K] MvPolynomial α K),
    ∃ PR : MvPolynomial ((TT × Bool) × α) K →ₗ[K] MvPolynomial (S × α) K, ∀ Y : TT → MvPolynomial (Bool × α) K,
      PR (∏ s : TT, rename (fun v : Bool × α => ((s, v.1), v.2)) (Y s)) =
        ∏ s : TT, rename (fun v => (s.val, v)) (pr s (Y s))

def RegroupP : Prop :=
  ∀ (R K : Type) [CommRing R] [CommRing K] [Algebra R K] (T α : Type) [Fintype T] [DecidableEq T]
    (N : T × Bool → Submodule R (MvPolynomial α K)) (y : T → MvPolynomial (Bool × α) K),
    (∀ s, y s ∈ Submodule.span R {P | ∃ F : Bool → MvPolynomial α K, (∀ b, F b ∈ N (s, b)) ∧
      P = ∏ b, rename (fun v => (b, v)) (F b)}) →
    ∏ s, rename (fun v : Bool × α => ((s, v.1), v.2)) (y s) ∈
      Submodule.span R {P | ∃ F : T × Bool → MvPolynomial α K, (∀ x, F x ∈ N x) ∧
        P = ∏ x, rename (fun v => (x, v)) (F x)}

section Abs

variable {A K : Type} [CommRing A] [Field K] [Algebra A K] {n' k n : ℕ} (TT : Finset (Fin n'))

theorem prodSmulPowT {σ ι : Type} [Fintype ι] (c : K) (w : ι → MvPolynomial σ K) :
    ∏ s, (c • w s) = c ^ Fintype.card ι • ∏ s, w s := by
  simp only [MvPolynomial.smul_eq_C_mul, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
    map_pow]

theorem genRegroupT (F : TT × Bool → MvPolynomial (Fin k × Fin n) K) :
    ∏ x, blockEmb K x (F x) =
      ∏ s : TT, rename (fun v : Bool × (Fin k × Fin n) => ((s, v.1), v.2)) (∏ b, blockEmb K b (F (s, b))) := by
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_prod]
  exact Finset.prod_congr rfl fun b _ =>
    (MvPolynomial.rename_rename (R := K) (fun v : Fin k × Fin n => (b, v))
      (fun v : Bool × (Fin k × Fin n) => ((s, v.1), v.2)) (F (s, b))).symm

theorem prodTopsT (G : TT → MvPolynomial (Fin k × Fin n) K) :
    ∏ s : TT, rename (fun v => (s.val, v)) (G s) =
      ∏ s : Fin n', blockEmb K s (if h : s ∈ TT then G ⟨s, h⟩ else 1) := by
  symm
  rw [← Finset.prod_subset (Finset.subset_univ TT)]
  · rw [← Finset.prod_coe_sort TT]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [dite_eq_left s.2]
    rfl
  · intro s _ hs
    rw [dif_neg hs, map_one]

theorem ioMem (hK2 : RegroupP) (i : TT → MvPolynomial (Fin k × Fin n) K →ₗ[K] MvPolynomial (Bool × (Fin k × Fin n)) K)
    (IO : MvPolynomial (Fin n' × (Fin k × Fin n)) K →ₗ[K] MvPolynomial ((TT × Bool) × (Fin k × Fin n)) K)
    (hIO : ∀ P : Fin n' → MvPolynomial (Fin k × Fin n) K, (∀ s, s ∉ TT → P s = 1) →
      IO (∏ s, rename (fun v => (s, v)) (P s)) =
        ∏ s : TT, rename (fun v : Bool × (Fin k × Fin n) => ((s, v.1), v.2)) (i s (P s.val)))
    (Nv : Fin n' → Submodule A (MvPolynomial (Fin k × Fin n) K))
    (N2 : TT × Bool → Submodule A (MvPolynomial (Fin k × Fin n) K)) (c : K)
    (h1 : ∀ s : TT, ∀ y ∈ Nv s.val, c • i s y ∈ tensorLat A K (fun b => N2 (s, b)))
    (h0 : ∀ s, s ∉ TT → ∀ y ∈ Nv s, ∃ a : A, y = C (algebraMap A K a)) :
    ∀ y ∈ tensorLat A K Nv, c ^ TT.card • IO y ∈ tensorLat A K N2 := by
  have hcomm : ∀ (a : A) (z : MvPolynomial ((TT × Bool) × (Fin k × Fin n)) K),
      c ^ TT.card • a • z = a • c ^ TT.card • z := fun a z => by
    rw [← algebraMap_smul K a z, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
  intro y hy
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    classical
    let a' : Fin n' → A := fun s =>
      if h : s ∈ TT then 1 else Classical.choose (h0 s h (F s) (hF s))
    let P : Fin n' → MvPolynomial (Fin k × Fin n) K := fun s => if s ∈ TT then F s else 1
    have hP : ∀ s, s ∉ TT → P s = 1 := fun s hs => if_neg hs
    have hPF : ∀ s : TT, P s.val = F s.val := fun s => if_pos s.2
    have hterm : ∀ s, blockEmb K s (F s) =
        MvPolynomial.C (algebraMap A K (a' s)) * rename (fun v : Fin k × Fin n => (s, v)) (P s) := by
      intro s
      by_cases h : s ∈ TT
      · simp [a', P, h, blockEmb]
      · have e := Classical.choose_spec (h0 s h (F s) (hF s))
        simp only [a', P, dif_neg h, if_neg h, map_one, mul_one]
        conv_lhs => rw [e]
        exact MvPolynomial.rename_C _ _
    have hy : ∏ s, blockEmb K s (F s) =
        (∏ s, a' s) • ∏ s, rename (fun v : Fin k × Fin n => (s, v)) (P s) := by
      rw [Finset.prod_congr rfl fun s _ => hterm s, Finset.prod_mul_distrib, Algebra.smul_def,
        MvPolynomial.algebraMap_apply]
      simp only [map_prod]
    have hmem := hK2 A K TT (Fin k × Fin n) N2 (fun s => c • i s (P s.val))
      (fun s => by
        simp only [hPF s]
        exact h1 s (F s.val) (hF s.val))
    have hc : ∀ w : TT → MvPolynomial ((TT × Bool) × (Fin k × Fin n)) K,
        c ^ TT.card • ∏ s, w s = ∏ s, c • w s := fun w => by
      rw [prodSmulPowT, Fintype.card_coe]
    rw [hy, LinearMap.map_smul_of_tower, hcomm]
    refine Submodule.smul_mem _ _ ?_
    rw [hIO P hP, hc]
    simp only [map_smul] at hmem
    exact hmem
  | zero =>
    rw [map_zero, smul_zero]
    exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
    rw [map_add (f := _), smul_add]
    exact Submodule.add_mem _ ihx ihy
  | smul a x _ ih =>
    rw [LinearMap.map_smul_of_tower, hcomm]
    exact Submodule.smul_mem _ a ih

theorem prMem (pr : TT → MvPolynomial (Bool × (Fin k × Fin n)) K →ₗ[K] MvPolynomial (Fin k × Fin n) K)
    (PR : MvPolynomial ((TT × Bool) × (Fin k × Fin n)) K →ₗ[K] MvPolynomial (Fin n' × (Fin k × Fin n)) K)
    (hPR : ∀ Y : TT → MvPolynomial (Bool × (Fin k × Fin n)) K,
      PR (∏ s : TT, rename (fun v : Bool × (Fin k × Fin n) => ((s, v.1), v.2)) (Y s)) =
        ∏ s : TT, rename (fun v => (s.val, v)) (pr s (Y s)))
    (Nv : Fin n' → Submodule A (MvPolynomial (Fin k × Fin n) K))
    (N2 : TT × Bool → Submodule A (MvPolynomial (Fin k × Fin n) K)) (c : K)
    (h1 : ∀ s : TT, ∀ x ∈ tensorLat A K (fun b => N2 (s, b)), c • pr s x ∈ Nv s.val)
    (h0 : ∀ s, s ∉ TT → (1 : MvPolynomial (Fin k × Fin n) K) ∈ Nv s) :
    ∀ x ∈ tensorLat A K N2, c ^ TT.card • PR x ∈ tensorLat A K Nv := by
  have hcomm : ∀ (a : A) (z : MvPolynomial (Fin n' × (Fin k × Fin n)) K),
      c ^ TT.card • a • z = a • c ^ TT.card • z := fun a z => by
    rw [← algebraMap_smul K a z, smul_smul, mul_comm, ← smul_smul, algebraMap_smul]
  have hc : ∀ w : TT → MvPolynomial (Fin n' × (Fin k × Fin n)) K,
      c ^ TT.card • ∏ s, w s = ∏ s, c • w s := fun w => by
    rw [prodSmulPowT, Fintype.card_coe]
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    have ht := prodTopsT TT (fun s => c • pr s (∏ b, blockEmb K b (F (s, b))))
    simp only [map_smul] at ht
    rw [genRegroupT, hPR, hc, ht]
    refine Submodule.subset_span ⟨fun s => if h : s ∈ TT then
      c • pr ⟨s, h⟩ (∏ b, blockEmb K b (F (⟨s, h⟩, b))) else 1, fun s => ?_, rfl⟩
    dsimp only
    by_cases h : s ∈ TT
    · rw [dite_eq_left h]
      exact h1 ⟨s, h⟩ _ (Submodule.subset_span ⟨fun b => F (⟨s, h⟩, b), fun b => hF _, rfl⟩)
    · rw [dif_neg h]
      exact h0 s h
  | zero =>
    rw [map_zero, smul_zero]
    exact Submodule.zero_mem _
  | add x y _ _ ihx ihy =>
    rw [map_add (f := _), smul_add]
    exact Submodule.add_mem _ ihx ihy
  | smul a x _ ih =>
    rw [LinearMap.map_smul_of_tower, hcomm]
    exact Submodule.smul_mem _ a ih

end Abs

end Formalism.MainNotions.flipOneThree.Pf

end
end

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.GradedWeylDivisibility MvPolynomial

theorem ex_val {n' : ℕ} {TT : Finset (Fin n')} (f : TT → ℕ) (s : TT) : ex f s.val = f s := by
  unfold ex
  rw [dif_pos s.2]

theorem lamAt_flat_top {n' : ℕ} (m : ℕ) (hm : 1 ≤ m) {TT : Finset (Fin n')} (al be : TT → ℕ) (s : TT) :
    lamAt (flatW m al be) s.val =
      wtPQ m (if Even s.val.val then al s else be s) (if Even s.val.val then be s else al s) := by
  have hl : (Fin.last m) ≠ 0 := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  funext i
  have r0 : i.rev = 0 ↔ i = Fin.last m := by rw [← Fin.rev_last, Fin.rev_inj]
  have rl : i.rev = Fin.last m ↔ i = 0 := by rw [← Fin.rev_zero, Fin.rev_inj]
  unfold lamAt flatW wtPQ
  by_cases he : Even s.val.val
  · simp only [he, if_true, s.2, dite_true]
  · simp only [he, if_false, s.2, dite_true, r0, rl]
    by_cases h0 : i = 0
    · subst h0
      simp [hl.symm]
    · by_cases h1 : i = Fin.last m
      · subst h1
        simp [hl]
      · simp [h0, h1]

theorem lamAt_flat_off {n' : ℕ} (m : ℕ) {TT : Finset (Fin n')} (al be : TT → ℕ) (s : Fin n') (hs : s ∉ TT) :
    lamAt (flatW m al be) s = 0 := by
  apply tn_lamAt_zero
  funext i
  simp [flatW, hs]

theorem functor_comparison_of_single_weight (hIOe : ExistsIO) (hPRe : ExistsPR) (hK2 : RegroupP) (h : SingleWeightLatticeComparison) : LatticeFunctorComparison := by
  classical
  intro p n' R m hm TT a A B hdeg
  let Ps : TT → ℕ := fun s => if Even s.val.val then A s else B s
  let Qs : TT → ℕ := fun s => if Even s.val.val then B s else A s
  have hdeg' : ∀ s, Ps s + Qs s + 1 ≤ 8 * a := fun s => by
    have := hdeg s
    simp only [Ps, Qs]
    split_ifs <;> omega
  have hmin : ∀ s, min (Ps s) (Qs s) = min (A s) (B s) := fun s => by
    simp only [Ps, Qs]
    split_ifs
    · rfl
    · exact min_comm _ _
  choose i1 pr1 hsum1 hrange1 hlat1 using fun s : TT => h p n' R m hm a (Ps s) (Qs s) (hdeg' s)
  choose IO hIO using fun j : TT → ℕ =>
    hIOe R.Kf (Fin n') (Fin (m + 1) × Fin (m + 1)) TT (fun s => i1 s (j s))
  choose PR hPR using fun j : TT → ℕ =>
    hPRe R.Kf (Fin n') (Fin (m + 1) × Fin (m + 1)) TT (fun s => pr1 s (j s))
  set Jf := Fintype.piFinset (fun s : TT => Finset.range (min (A s) (B s) + 1)) with hJf
  let lamj : (TT → ℕ) → Fin n' → Fin (m + 1) → ℤ := fun j => flatW m (fun s => A s - j s) (fun s => B s - j s)
  have hjle : ∀ j ∈ Jf, ∀ s, j s ≤ min (Ps s) (Qs s) := fun j hj s => by
    rw [hmin]
    exact Nat.lt_succ_iff.1 (Finset.mem_range.1 ((Fintype.mem_piFinset.1 hj) s))
  have hwt : ∀ (j : TT → ℕ) (s : TT), lamAt (lamj j) s.val = wtPQ m (Ps s - j s) (Qs s - j s) := fun j s => by
    rw [lamAt_flat_top m (by omega)]
    simp only [Ps, Qs]
    split_ifs <;> rfl
  have hoff : ∀ (j : TT → ℕ) (s : Fin n'), s ∉ TT → lamAt (lamj j) s = 0 := fun j s hs => lamAt_flat_off m _ _ s hs
  have hhh : ∀ (s : TT) (b : Bool), hhWt m TT (ex A) (ex B) (s, b) = letterWt m (if b then Ps s else Qs s) b := by
    intro s b
    unfold hhWt hhDeg
    cases b <;> simp [ex_val, Ps, Qs]
  have hdom : ∀ j, IsDominant (lamj j) := fun j => flattened_weight_dominant m _ _

  have hVHH : VHH (m := m) R.Kf TT (ex A) (ex B) = tensorLat R.Kf R.Kf
      (fun x : TT × Bool => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (hhWt m TT (ex A) (ex B) x))) := rfl
  have htwoSp : ∀ s : TT, tensorLat R.Kf R.Kf
      (fun b : Bool => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (hhWt m TT (ex A) (ex B) (s, b)))) =
      twoSp R.Kf m (Ps s) (Qs s) := fun s => by
    unfold twoSp
    congr 1
    funext b
    rw [hhh]
  have hioV : ∀ j ∈ Jf, ∀ y ∈ Vsp R.Kf (lamj j), IO j y ∈ VHH (m := m) R.Kf TT (ex A) (ex B) := by
    intro j hj y hy
    rw [Vsp_eq R.Kf _ (hdom j)] at hy
    have := ioMem (A := R.Kf) TT hK2 (fun s => i1 s (j s)) (IO j) (hIO j) _
      (fun x : TT × Bool => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (hhWt m TT (ex A) (ex B) x))) 1
      (fun s y hy => by
        rw [one_smul, htwoSp]
        rw [hwt] at hy
        exact ((hrange1 s (j s) (hjle j hj s)).2 y hy))
      (fun s hs y hy => by
        rw [hoff j s hs, nuOf_zero] at hy
        exact ⟨_, tn_const _ _ y hy⟩) y hy
    rw [one_pow, one_smul] at this
    exact this
  have hprV : ∀ j ∈ Jf, ∀ x ∈ VHH (m := m) R.Kf TT (ex A) (ex B), PR j x ∈ Vsp R.Kf (lamj j) := by
    intro j hj x hx
    rw [Vsp_eq R.Kf _ (hdom j)]
    have := prMem (A := R.Kf) TT (fun s => pr1 s (j s)) (PR j) (hPR j)
      (fun s => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (lamAt (lamj j) s)))
      (fun x : TT × Bool => dualWeyl R.Kf (m + 1) (m + 1) (nuOf (hhWt m TT (ex A) (ex B) x))) 1
      (fun s x hx => by
        rw [one_smul, hwt]
        rw [htwoSp] at hx
        exact ((hrange1 s (j s) (hjle j hj s)).1 x hx))
      (fun s hs => by
        rw [hoff j s hs, nuOf_zero]
        exact one_mem_dualWeyl _ _ _) x hx
    rw [one_pow, one_smul] at this
    exact this

  have hsumA : ∀ x ∈ VHH (m := m) R.Kf TT (ex A) (ex B), ∑ j ∈ Jf, IO j (PR j x) = x := by
    intro x hx
    rw [hVHH] at hx
    refine Submodule.span_induction (p := fun x _ => ∑ j ∈ Jf, IO j (PR j x) = x) ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨F, hF, rfl⟩
      rw [genRegroupT]
      set Y : TT → MvPolynomial (Bool × (Fin (m + 1) × Fin (m + 1))) R.Kf :=
        fun s => ∏ b, blockEmb R.Kf b (F (s, b)) with hY
      have hYm : ∀ s, Y s ∈ twoSp R.Kf m (Ps s) (Qs s) := fun s => by
        rw [← htwoSp]
        exact Submodule.subset_span ⟨fun b => F (s, b), fun b => hF _, rfl⟩
      have e1 : ∀ j, IO j (PR j (∏ s : TT, rename (fun v : Bool × (Fin (m + 1) × Fin (m + 1)) => ((s, v.1), v.2)) (Y s))) =
          ∏ s : TT, rename (fun v : Bool × (Fin (m + 1) × Fin (m + 1)) => ((s, v.1), v.2))
            (i1 s (j s) (pr1 s (j s) (Y s))) := by
        intro j
        rw [hPR j, prodTopsT TT (fun s => pr1 s (j s) (Y s))]
        have := hIO j (fun s => if h : s ∈ TT then pr1 ⟨s, h⟩ (j ⟨s, h⟩) (Y ⟨s, h⟩) else 1)
          (fun s hs => by rw [dite_eq_right hs])
        rw [show (∏ s : Fin n', blockEmb R.Kf s (if h : s ∈ TT then pr1 ⟨s, h⟩ (j ⟨s, h⟩) (Y ⟨s, h⟩) else 1)) =
          ∏ s : Fin n', rename (fun v => (s, v)) (if h : s ∈ TT then pr1 ⟨s, h⟩ (j ⟨s, h⟩) (Y ⟨s, h⟩) else 1) from rfl,
          this]
        refine Finset.prod_congr rfl fun s _ => ?_
        rw [dif_pos s.2]
      show ∑ j ∈ Jf, IO j (PR j (∏ s : TT, rename (fun v : Bool × (Fin (m + 1) × Fin (m + 1)) => ((s, v.1), v.2)) (Y s))) =
        ∏ s : TT, rename (fun v : Bool × (Fin (m + 1) × Fin (m + 1)) => ((s, v.1), v.2)) (Y s)
      simp only [e1]
      rw [hJf, ← Finset.prod_univ_sum (fun s : TT => Finset.range (min (A s) (B s) + 1))
        (fun s j => rename (fun v : Bool × (Fin (m + 1) × Fin (m + 1)) => ((s, v.1), v.2)) (i1 s j (pr1 s j (Y s))))]
      refine Finset.prod_congr rfl fun s _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, ← hmin s, hsum1 s (Y s) (hYm s)]
    · simp
    · intro x y _ _ hx hy
      simp only [map_add (f := _), Finset.sum_add_distrib, hx, hy]
    · intro c x _ hx
      simp only [map_smul]
      rw [← Finset.smul_sum, hx]
  refine ⟨fun j => if hj : j ∈ Jf then
      LinearMap.codRestrict _ ((IO j).comp (Submodule.subtype _)) (fun y => hioV j hj y.1 y.2) else 0,
    fun j => if hj : j ∈ Jf then
      LinearMap.codRestrict _ ((PR j).comp (Submodule.subtype _)) (fun x => hprV j hj x.1 x.2) else 0, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    rw [← hsumA x.1 x.2]
    rw [Submodule.coe_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [dif_pos hj]
    rfl
  · intro M hM j hj
    simp only [dif_pos hj]
    have hpow : (p : R.Kf) ^ (TT.card * ⌈((m : ℝ) + 2) * lgA p a m⌉₊) =
        ((p : R.Kf) ^ ⌈((m : ℝ) + 2) * lgA p a m⌉₊) ^ TT.card := by rw [← pow_mul, mul_comm]
    have htwoLat : ∀ s : TT, tensorLat R.O R.Kf
        (fun b : Bool => H0 R.O m (hhWt m TT (ex A) (ex B) (s, b)) (M s.val)) =
        twoLat R.O m (Ps s) (Qs s) (M s.val) := fun s => by
      unfold twoLat
      congr 1
      funext b
      rw [hhh]
    constructor
    · intro x hx
      have := prMem (A := R.O) TT (fun s => pr1 s (j s)) (PR j) (hPR j)
        (fun s => H0 R.O m (lamAt (lamj j) s) (M s))
        (fun x : TT × Bool => H0 R.O m (hhWt m TT (ex A) (ex B) x) (M x.1.val))
        ((p : R.Kf) ^ ⌈((m : ℝ) + 2) * lgA p a m⌉₊)
        (fun s x hx => by
          rw [hwt]
          rw [htwoLat] at hx
          exact ((hlat1 s (M s.val) (hM _) (j s) (hjle j hj s)).1 x hx))
        (fun s hs => by
          rw [hoff j s hs]
          exact (invariant_sections_zero_weight_iff m (M s) (hM s) 1).2 ⟨1, by simp⟩) x.1 hx
      rw [← hpow] at this
      exact this
    · intro y hy
      have := ioMem (A := R.O) TT hK2 (fun s => i1 s (j s)) (IO j) (hIO j)
        (fun s => H0 R.O m (lamAt (lamj j) s) (M s))
        (fun x : TT × Bool => H0 R.O m (hhWt m TT (ex A) (ex B) x) (M x.1.val))
        ((p : R.Kf) ^ ⌈((m : ℝ) + 2) * lgA p a m⌉₊)
        (fun s y hy => by
          rw [htwoLat]
          rw [hwt] at hy
          exact ((hlat1 s (M s.val) (hM _) (j s) (hjle j hj s)).2 y hy))
        (fun s hs y hy => by
          rw [hoff j s hs] at hy
          exact (invariant_sections_zero_weight_iff m (M s) (hM s) y).1 hy) y.1 hy
      rw [← hpow] at this
      exact this

end Formalism.MainNotions.flipOneThree.Pf

end
