module

public import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.DivDerZero

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.OtherEFree
section -- merged from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.ChainEmbInj
section -- merged from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.LettersAtUpdate
section -- merged from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.BlockWithThresholds
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees

section GlobalTheory

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)] {N r : ℕ} [NeZero r]

abbrev blockWithThresholds (D : BlockData N) (thr : Fin D.T.q → WithTop ℤ) : BlockData N :=
  { D with T := { D.T with thr := thr } }

abbrev SSt (O : Type) [CommRing O] [IsDomain O] (r : ℕ) [NeZero r] (D : BlockData N) (thr : Fin D.T.q → WithTop ℤ) :
    Submodule O (MvPolynomial (BVar N r D.T.t) (KK O)) :=
  (blockWithThresholds D thr).SSZ O (r := r)

structure TieOK (D : BlockData N) : Prop where
  lt : ∀ i, D.T.pos i + 1 < N
  inj : ∀ i i', D.T.pos i = D.T.pos i' → i = i'
  sep : ∀ i i', D.T.pos i + 1 ≠ D.T.pos i'
  uW : ∀ i, D.T.pos i ≠ (D.uPos : ℕ) ∧ D.T.pos i + 1 ≠ (D.uPos : ℕ)
  vecE : ∀ i (h : D.T.pos i + 1 < N), D.LL.vec ⟨D.T.pos i + 1, h⟩ = false

def tailP (O : Type) [CommRing O] [IsDomain O] (r : ℕ) (D : BlockData N) (jp : ℕ)
    (y : MvPolynomial (Fin N × Fin r) (KK O)) (g : MvPolynomial (BVar N r D.T.t) (KK O)) :
    MvPolynomial (BVar N r D.T.t) (KK O) :=
  D.Eplus O (r := r) ^ jp * (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) *
    X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus * rename (chainEmb N r D.T.t) y * g

theorem gen_mem (D : BlockData N) (thr : Fin D.T.q → WithTop ℤ) {j : Fin D.T.t → ℕ} {jp : ℕ} (hL : D.LevelOK j jp)
    {y : MvPolynomial (Fin N × Fin r) (KK O)} (hy : y ∈ YjtZ O (r := r) (D.lettersAt j jp) D.T.J thr)
    {g : MvPolynomial (BVar N r D.T.t) (KK O)} (hg : g ∈ XiPolZ O N r D.T.t (D.B - jp)) :
    (∏ i, D.Ehat O (r := r) i ^ j i) * tailP O r D jp y g ∈ SSt O r D thr := by
  unfold SSt BlockData.SSZ
  apply Submodule.subset_span
  refine Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨jp, Set.mem_iUnion.2 ⟨hL, ⟨y, hy, g, hg, ?_⟩⟩⟩⟩
  unfold tailP
  simp only [mul_assoc]
  rfl

theorem SSt_mono (D : BlockData N) {thr thr' : Fin D.T.q → WithTop ℤ} (h : ∀ k, thr k ≤ thr' k) :
    SSt O r D thr ≤ SSt O r D thr' := by
  unfold SSt BlockData.SSZ
  apply Submodule.span_mono
  intro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨j, jp, hL, hx⟩ := hx
  obtain ⟨y, hy, g0, hg0, rfl⟩ := hx
  exact Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨jp, Set.mem_iUnion.2 ⟨hL,
    ⟨y, ⟨yjt_mono' _ _ h hy.1, hy.2⟩, g0, hg0, rfl⟩⟩⟩⟩

def IsMult (O : Type) [CommRing O] [IsDomain O] (r : ℕ) [NeZero r] (vec : Fin N → Bool) {q : ℕ} (J : Fin q → ℕ)
    (aW aE : Fin N) (q0 : MvPolynomial (Fin N × Fin r) (KK O)) : Prop :=
  ∀ (deg : Fin N → ℕ) (thr : Fin q → WithTop ℤ) (y : MvPolynomial (Fin N × Fin r) (KK O)),
    y ∈ YjtZ O (r := r) ⟨vec, deg⟩ J thr →
    q0 * y ∈ YjtZ O (r := r) ⟨vec, fun a => deg a + if a = aW ∨ a = aE then 1 else 0⟩ J
      (fun k => thr k + ((1 : ℤ) : WithTop ℤ))

theorem IsMult.pow {vec : Fin N → Bool} {q : ℕ} {J : Fin q → ℕ} {aW aE : Fin N}
    {q0 : MvPolynomial (Fin N × Fin r) (KK O)} (h : IsMult O r vec J aW aE q0) (l : ℕ) (deg : Fin N → ℕ)
    (thr : Fin q → WithTop ℤ) (y : MvPolynomial (Fin N × Fin r) (KK O)) (hy : y ∈ YjtZ O (r := r) ⟨vec, deg⟩ J thr) :
    q0 ^ l * y ∈ YjtZ O (r := r) ⟨vec, fun a => deg a + if a = aW ∨ a = aE then l else 0⟩ J
      (fun k => thr k + ((l : ℤ) : WithTop ℤ)) := by
  induction l with
  | zero =>
    simpa using hy
  | succ l ih =>
    have h1 := h _ _ _ ih
    rw [pow_succ', mul_assoc]
    have e1 : (fun a => (deg a + if a = aW ∨ a = aE then l else 0) + if a = aW ∨ a = aE then 1 else 0) =
        fun a => deg a + if a = aW ∨ a = aE then l + 1 else 0 := by
      funext a
      split_ifs <;> omega
    have e2 : (fun k => thr k + ((l : ℤ) : WithTop ℤ) + ((1 : ℤ) : WithTop ℤ)) =
        fun k => thr k + (((l + 1 : ℕ) : ℤ) : WithTop ℤ) := by
      funext k
      rw [add_assoc]
      norm_cast
    rw [e1, e2] at h1
    exact h1

theorem isMult_XX (D7 : Formalism.BasicNotions.D7) (vec : Fin N → Bool) {q : ℕ} (J : Fin q → ℕ) (aW aE : Fin N) (hne : aW ≠ aE)
    (hE : vec aE = false) (c c' : Fin r) : IsMult O r vec J aW aE (X (aW, c) * X (aE, c')) := by
  intro deg thr y hy
  have h1 := yjtZ_X (O := O) D7 ⟨vec, deg⟩ ⟨vec, fun a => deg a + if a = aE then 1 else 0⟩ rfl aE c' (fun _ => rfl) J
    (thr := thr) (thr' := thr) 0 (fun h => by simp [hE] at h) (fun k => by simp) hy
  have h2 := yjtZ_X (O := O) D7 ⟨vec, fun a => deg a + if a = aE then 1 else 0⟩
    ⟨vec, fun a => deg a + if a = aW ∨ a = aE then 1 else 0⟩ rfl aW c
    (fun i => by
      show deg i + _ = deg i + _ + _
      by_cases h1 : i = aW
      · subst h1; simp [hne]
      · simp [h1]) J (thr := thr) (thr' := fun k => thr k + ((1 : ℤ) : WithTop ℤ)) 1 (fun _ => le_rfl)
    (fun k => by norm_cast) h1
  rw [mul_assoc]
  exact h2

theorem IsMult.neg {vec : Fin N → Bool} {q : ℕ} {J : Fin q → ℕ} {aW aE : Fin N}
    {q0 : MvPolynomial (Fin N × Fin r) (KK O)} (h : IsMult O r vec J aW aE q0) : IsMult O r vec J aW aE (-q0) := by
  intro deg thr y hy
  rw [neg_mul]
  exact Submodule.neg_mem _ (h deg thr y hy)

theorem IsMult.sum {vec : Fin N → Bool} {q : ℕ} {J : Fin q → ℕ} {aW aE : Fin N} {ι : Type} (s : Finset ι)
    {q0 : ι → MvPolynomial (Fin N × Fin r) (KK O)} (h : ∀ i ∈ s, IsMult O r vec J aW aE (q0 i)) :
    IsMult O r vec J aW aE (∑ i ∈ s, q0 i) := by
  intro deg thr y hy
  rw [Finset.sum_mul]
  exact Submodule.sum_mem _ fun i hi => h i hi deg thr y hy

end GlobalTheory

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees

section GlobalTheory

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)] {N r : ℕ} [NeZero r]

def tieW {D : BlockData N} (hT : TieOK D) (i : Fin D.T.t) : Fin N := ⟨D.T.pos i, by have := hT.lt i; omega⟩

def tieE {D : BlockData N} (hT : TieOK D) (i : Fin D.T.t) : Fin N := ⟨D.T.pos i + 1, hT.lt i⟩

theorem lettersAt_update {D : BlockData N} (hT : TieOK D) {j : Fin D.T.t → ℕ} {jp : ℕ} (hL : D.LevelOK j jp)
    (i : Fin D.T.t) (l : ℕ) (hl : l ≤ j i) :
    D.lettersAt (Function.update j i (j i - l)) jp =
      ⟨D.LL.vec, fun a => (D.lettersAt j jp).deg a + if a = tieW hT i ∨ a = tieE hT i then l else 0⟩ := by
  classical
  unfold BlockData.lettersAt
  simp only [ChainLetters.mk.injEq, true_and]
  funext a
  have hW : a = tieW hT i ↔ (a : ℕ) = D.T.pos i := by unfold tieW; rw [Fin.ext_iff]
  have hE : a = tieE hT i ↔ (a : ℕ) = D.T.pos i + 1 := by unfold tieE; rw [Fin.ext_iff]
  simp only [hW, hE]
  by_cases ha : (a : ℕ) = D.T.pos i ∨ (a : ℕ) = D.T.pos i + 1
  · have hoth : ∀ i', i' ≠ i → ¬ ((a : ℕ) = D.T.pos i' ∨ (a : ℕ) = D.T.pos i' + 1) := by
      intro i' hi' h
      rcases ha with ha | ha <;> rcases h with h | h
      · exact hi' (hT.inj _ _ (h.symm.trans ha))
      · exact hT.sep i' i (h.symm.trans ha)
      · exact hT.sep i i' (ha.symm.trans h)
      · exact hi' (hT.inj _ _ (by omega))
    have s1 : (∑ i', if (a : ℕ) = D.T.pos i' ∨ (a : ℕ) = D.T.pos i' + 1 then
        Function.update j i (j i - l) i' else 0) = j i - l := by
      rw [Finset.sum_eq_single i (fun i' _ hi' => if_neg (hoth i' hi')) (fun h => absurd (Finset.mem_univ i) h),
        if_pos ha, Function.update_self]
    have s2 : (∑ i', if (a : ℕ) = D.T.pos i' ∨ (a : ℕ) = D.T.pos i' + 1 then j i' else 0) = j i := by
      rw [Finset.sum_eq_single i (fun i' _ hi' => if_neg (hoth i' hi')) (fun h => absurd (Finset.mem_univ i) h),
        if_pos ha]
    have hu : a ≠ D.uPos := by
      intro h
      rcases ha with ha | ha
      · exact (hT.uW i).1 (by rw [← ha, h])
      · exact (hT.uW i).2 (by rw [← ha, h])
    have hdeg : j i ≤ D.LL.deg a := by
      have hN := hT.lt i
      rcases ha with ha | ha
      · have : D.letterAt (D.T.pos i) = a := by
          unfold BlockData.letterAt
          apply Fin.ext
          simp only
          omega
        rw [← this]; exact (hL.1 i).1
      · have : D.letterAt (D.T.pos i + 1) = a := by
          unfold BlockData.letterAt
          apply Fin.ext
          simp only
          omega
        rw [← this]; exact (hL.1 i).2
    rw [s1, s2, if_neg hu, if_pos ha]
    omega
  · rw [if_neg ha, add_zero]
    congr 2
    refine Finset.sum_congr rfl fun i' _ => ?_
    by_cases hi' : i' = i
    · subst hi'
      rw [if_neg ha, if_neg ha]
    · rw [Function.update_of_ne hi']

theorem levelOK_update {D : BlockData N} {j : Fin D.T.t → ℕ} {jp : ℕ} (hL : D.LevelOK j jp) (i : Fin D.T.t) (l : ℕ) :
    D.LevelOK (Function.update j i (j i - l)) jp := by
  classical
  refine ⟨fun i' => ?_, hL.2⟩
  have : Function.update j i (j i - l) i' ≤ j i' := by
    by_cases h : i' = i
    · subst h; rw [Function.update_self]; omega
    · rw [Function.update_of_ne h]
  exact ⟨this.trans (hL.1 i').1, this.trans (hL.1 i').2⟩

theorem tailP_mul (D : BlockData N) (jp : ℕ) (q y : MvPolynomial (Fin N × Fin r) (KK O))
    (g : MvPolynomial (BVar N r D.T.t) (KK O)) :
    tailP O r D jp (q * y) g = rename (chainEmb N r D.T.t) q * tailP O r D jp y g := by
  unfold tailP
  rw [map_mul]
  ring


open Classical in
def otherE (O : Type) [CommRing O] [IsDomain O] (r : ℕ) (D : BlockData N) (j : Fin D.T.t → ℕ) (i : Fin D.T.t) :
    MvPolynomial (BVar N r D.T.t) (KK O) :=
  ∏ i' ∈ Finset.univ.erase i, D.Ehat O (r := r) i' ^ j i'

theorem prodE_split (D : BlockData N) (j : Fin D.T.t → ℕ) (i : Fin D.T.t) :
    (∏ i', D.Ehat O (r := r) i' ^ j i') = D.Ehat O (r := r) i ^ j i * otherE O r D j i := by
  classical
  unfold otherE
  exact (Finset.mul_prod_erase Finset.univ (fun i' => D.Ehat O (r := r) i' ^ j i') (Finset.mem_univ i)).symm

theorem prodE_update (D : BlockData N) (j : Fin D.T.t → ℕ) (i : Fin D.T.t) (e : ℕ) :
    (∏ i', D.Ehat O (r := r) i' ^ Function.update j i e i') = D.Ehat O (r := r) i ^ e * otherE O r D j i := by
  classical
  unfold otherE
  rw [← Finset.mul_prod_erase Finset.univ (fun i' => D.Ehat O (r := r) i' ^ Function.update j i e i')
    (Finset.mem_univ i), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i' hi' => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi')]

theorem shift_mem {D : BlockData N} (hT : TieOK D) {thr0 thr' : Fin D.T.q → WithTop ℤ} {j : Fin D.T.t → ℕ} {jp : ℕ}
    (hL : D.LevelOK j jp) (i : Fin D.T.t) (l : ℕ) (hl : l ≤ j i)
    (hthr : ∀ k, thr0 k + ((l : ℤ) : WithTop ℤ) ≤ thr' k)
    {q0 : MvPolynomial (Fin N × Fin r) (KK O)} (hq0 : IsMult O r D.LL.vec D.T.J (tieW hT i) (tieE hT i) q0)
    {y : MvPolynomial (Fin N × Fin r) (KK O)} (hy : y ∈ YjtZ O (r := r) (D.lettersAt j jp) D.T.J thr0)
    {g : MvPolynomial (BVar N r D.T.t) (KK O)} (hg : g ∈ XiPolZ O N r D.T.t (D.B - jp)) :
    D.Ehat O (r := r) i ^ (j i - l) * rename (chainEmb N r D.T.t) q0 ^ l * otherE O r D j i * tailP O r D jp y g ∈
      SSt O r D thr' := by
  have h1 := hq0.pow l (D.lettersAt j jp).deg thr0 y hy
  rw [← lettersAt_update hT hL i l hl] at h1
  have h2 := gen_mem D (fun k => thr0 k + ((l : ℤ) : WithTop ℤ)) (levelOK_update hL i l) h1 hg
  rw [prodE_update, tailP_mul, map_pow] at h2
  have h3 := SSt_mono (O := O) (r := r) D hthr h2
  convert h3 using 1
  ring

def FreeV {K σ : Type} [CommSemiring K] (v : σ) (F : MvPolynomial σ K) : Prop := ∀ μ ∈ F.support, μ v = 0

theorem freeV_of_vars {K σ : Type} [CommSemiring K] {v : σ} {F : MvPolynomial σ K} (h : v ∉ F.vars) : FreeV v F := by
  classical
  intro μ hμ
  by_contra h0
  exact h ((mem_vars_iff_mem_support v).2 ⟨μ, hμ, Finsupp.mem_support_iff.2 h0⟩)

theorem cth_lin {K σ : Type} [Field K] {v : σ} {E m' E' : MvPolynomial σ K} (hE : E = X v * m' + E')
    (hm' : FreeV v m') (hE' : FreeV v E') : cth v 1 E = X v * m' ∧ ∀ a, 2 ≤ a → cth v a E = 0 := by
  have hX : ∀ a, cth v a (X v * m') = m' * cth v a (X v : MvPolynomial σ K) := by
    intro a
    rw [mul_comm, cth_mul_free v a hm']
  have hXa : ∀ a, cth v a (X v : MvPolynomial σ K) = monomial (Finsupp.single v 1) (((Nat.choose 1 a : ℕ) : K)) := by
    intro a
    show cth v a (monomial (Finsupp.single v 1) (1 : K)) = _
    rw [cth_monomial, Finsupp.single_eq_same, one_mul]
  constructor
  · rw [hE, cth_add, cth_free v hE' one_ne_zero, add_zero, hX, hXa]
    simp only [Nat.choose_self, Nat.cast_one]
    rw [mul_comm]
    rfl
  · intro a ha
    rw [hE, cth_add, cth_free v hE' (by omega), add_zero, hX, hXa, Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem tie_mem {D : BlockData N} (hT : TieOK D) {thr thr' : Fin D.T.q → WithTop ℤ} (n : ℕ)
    (hthr : ∀ k, thr k + ((n : ℤ) : WithTop ℤ) ≤ thr' k) {j : Fin D.T.t → ℕ} {jp : ℕ} (hL : D.LevelOK j jp)
    (i : Fin D.T.t) (v : BVar N r D.T.t) {m' E' : MvPolynomial (BVar N r D.T.t) (KK O)}
    (hE : D.Ehat O (r := r) i = X v * m' + E') (hm' : FreeV v m') (hE' : FreeV v E')
    {q0 : MvPolynomial (Fin N × Fin r) (KK O)} (hq0 : IsMult O r D.LL.vec D.T.J (tieW hT i) (tieE hT i) q0)
    (δ : Bool) (hq : X v * m' = (if δ then D.Ehat O (r := r) i else 0) + rename (chainEmb N r D.T.t) q0)
    (hPE : FreeV v (otherE O r D j i))
    {y : MvPolynomial (Fin N × Fin r) (KK O)} {g : MvPolynomial (BVar N r D.T.t) (KK O)}
    (hg : g ∈ XiPolZ O N r D.T.t (D.B - jp))
    (H : ∀ b, b ≤ n → ∃ (cb : ℕ) (yb : MvPolynomial (Fin N × Fin r) (KK O)),
      yb ∈ YjtZ O (r := r) (D.lettersAt j jp) D.T.J (fun k => thr k + ((b : ℤ) : WithTop ℤ)) ∧
      cth v b (tailP O r D jp y g) = cb • tailP O r D jp yb g) :
    cth v n ((∏ i, D.Ehat O (r := r) i ^ j i) * tailP O r D jp y g) ∈ SSt O r D thr' := by
  classical
  obtain ⟨h1, h2⟩ := cth_lin hE hm' hE'
  rw [prodE_split D j i, mul_comm (D.Ehat O (r := r) i ^ j i), mul_assoc, cth_mul_free v n hPE, cth_mul, Finset.mul_sum]
  refine Submodule.sum_mem _ ?_
  rintro ⟨l, b⟩ hlb
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hlb
  simp only at hlb ⊢
  obtain ⟨cb, yb, hyb, hcb⟩ := H b (by omega)
  rw [cth_pow v h1 h2, hcb, Nat.cast_smul_eq_nsmul]
  by_cases hl : l ≤ j i
  · have key : D.Ehat O (r := r) i ^ (j i - l) * (X v * m') ^ l * otherE O r D j i * tailP O r D jp yb g ∈
        SSt O r D thr' := by
      cases δ with
      | false =>
        simp only [Bool.false_eq_true, if_false, zero_add] at hq
        rw [hq]
        refine shift_mem hT hL i l hl (fun k => ?_) hq0 hyb hg
        refine le_trans (le_of_eq ?_) (hthr k)
        rw [add_assoc, ← hlb]
        push_cast
        rw [add_comm (l : WithTop ℤ)]
      | true =>
        simp only [if_true] at hq
        rw [hq, add_pow, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
        refine Submodule.sum_mem _ fun a ha => ?_
        have ha' : a ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
        have h3 := shift_mem (thr' := thr') hT hL i (l - a) (by omega) (fun k => ?_) hq0 hyb hg
        · have h4 := (SSt O r D thr').smul_of_tower_mem (l.choose a) h3
          convert h4 using 1
          have e : j i - (l - a) = (j i - l) + a := by omega
          rw [e, pow_add, nsmul_eq_mul]
          ring
        · refine le_trans ?_ (hthr k)
          rw [add_assoc]
          gcongr
          have : ((b : ℤ) + ((l - a : ℕ) : ℤ)) ≤ (n : ℤ) := by omega
          exact_mod_cast this
    have h5 := (SSt O r D thr').smul_of_tower_mem ((j i).choose l) ((SSt O r D thr').smul_of_tower_mem cb key)
    convert h5 using 1
    simp only [nsmul_eq_mul]
    ring
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

end GlobalTheory

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees

section NV

variable {K σ : Type} [Field K]

theorem nv_mul {v : σ} {F G : MvPolynomial σ K} (h1 : v ∉ F.vars) (h2 : v ∉ G.vars) : v ∉ (F * G).vars := by
  classical
  intro h
  rcases Finset.mem_union.1 (MvPolynomial.vars_mul F G h) with h' | h'
  · exact h1 h'
  · exact h2 h'

theorem nv_add {v : σ} {F G : MvPolynomial σ K} (h1 : v ∉ F.vars) (h2 : v ∉ G.vars) : v ∉ (F + G).vars := by
  classical
  intro h
  rcases Finset.mem_union.1 (MvPolynomial.vars_add_subset F G h) with h' | h'
  · exact h1 h'
  · exact h2 h'

theorem nv_pow {v : σ} {F : MvPolynomial σ K} (h1 : v ∉ F.vars) (n : ℕ) : v ∉ (F ^ n).vars := by
  intro h
  exact h1 (MvPolynomial.vars_pow F n h)

theorem nv_prod {v : σ} {ι : Type} (s : Finset ι) {f : ι → MvPolynomial σ K} (h1 : ∀ i ∈ s, v ∉ (f i).vars) :
    v ∉ (∏ i ∈ s, f i).vars := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [MvPolynomial.vars_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact nv_mul (h1 a (Finset.mem_insert_self a s)) (ih fun i hi => h1 i (Finset.mem_insert_of_mem hi))

theorem nv_sum {v : σ} {ι : Type} (s : Finset ι) {f : ι → MvPolynomial σ K} (h1 : ∀ i ∈ s, v ∉ (f i).vars) :
    v ∉ (∑ i ∈ s, f i).vars := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact nv_add (h1 a (Finset.mem_insert_self a s)) (ih fun i hi => h1 i (Finset.mem_insert_of_mem hi))

theorem nv_X {v u : σ} (h : v ≠ u) : v ∉ (X u : MvPolynomial σ K).vars := by
  classical
  rw [MvPolynomial.vars_X, Finset.mem_singleton]
  exact h

theorem nv_rename {τ : Type} {v : σ} (f : τ → σ) (h : ∀ x, f x ≠ v) (y : MvPolynomial τ K) : v ∉ (rename f y).vars := by
  classical
  intro hv
  obtain ⟨x, _, hx⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename f y hv)
  exact h x hx

theorem cth_rename {τ : Type} (f : τ → σ) (hf : Function.Injective f) (x : τ) (n : ℕ) (y : MvPolynomial τ K) :
    cth (f x) n (rename f y) = rename f (cth x n y) := by
  induction y using MvPolynomial.induction_on' with
  | monomial e c =>
    rw [rename_monomial, cth_monomial, cth_monomial, rename_monomial, Finsupp.mapDomain_apply_of_injective hf]
  | add p q hp hq => rw [map_add (f := _), cth_add, cth_add, map_add (f := _), hp, hq]

theorem cth_X_pow (v : σ) (b z : ℕ) : cth v b ((X v : MvPolynomial σ K) ^ z) = (z.choose b) • (X v : MvPolynomial σ K) ^ z := by
  rw [X_pow_eq_monomial, cth_monomial, Finsupp.single_eq_same, one_mul, ← Nat.cast_smul_eq_nsmul K,
    smul_monomial, smul_eq_mul, mul_one]

end NV

section GlobalTheory

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)] {N r : ℕ} [NeZero r]

theorem chainEmb_inj (N r t : ℕ) : Function.Injective (chainEmb N r t) := by
  intro a b h
  simp only [chainEmb, Sum.inl.injEq, Prod.mk.injEq] at h
  exact Prod.ext (Fin.castSucc_injective _ h.1) h.2

theorem Ehat_eq {D : BlockData N} (hT : TieOK D) (i : Fin D.T.t) :
    D.Ehat O (r := r) i = X (scalZ N r D.T.t (Fin.castSucc i)) * X (scalS N r D.T.t (Fin.castSucc i)) +
      ∑ c, X (chainEmb N r D.T.t (tieW hT i, c)) * X (chainEmb N r D.T.t (tieE hT i, c)) := by
  have e1 : finPos N (D.T.pos i) = Fin.castSucc (tieW hT i) := by
    apply Fin.ext
    simp only [finPos, tieW, Fin.coe_castSucc]
    exact Nat.min_eq_left (by have := hT.lt i; omega)
  have e2 : finPos N (D.T.pos i + 1) = Fin.castSucc (tieE hT i) := by
    apply Fin.ext
    simp only [finPos, tieE, Fin.coe_castSucc]
    exact Nat.min_eq_left (by have := hT.lt i; omega)
  rw [BlockData.Ehat, e1, e2]
  rfl

def pairP (O : Type) [CommRing O] [IsDomain O] (r : ℕ) {D : BlockData N} (hT : TieOK D) (i : Fin D.T.t) :
    MvPolynomial (Fin N × Fin r) (KK O) :=
  ∑ c, X (tieW hT i, c) * X (tieE hT i, c)

theorem Ehat_eq' {D : BlockData N} (hT : TieOK D) (i : Fin D.T.t) :
    D.Ehat O (r := r) i = X (scalZ N r D.T.t (Fin.castSucc i)) * X (scalS N r D.T.t (Fin.castSucc i)) +
      rename (chainEmb N r D.T.t) (pairP O r hT i) := by
  rw [Ehat_eq hT i]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [pairP, map_sum, rename_X]

theorem tieW_ne_tieE {D : BlockData N} (hT : TieOK D) (i i' : Fin D.T.t) : tieW hT i ≠ tieE hT i' := by
  intro h
  have := congrArg Fin.val h
  simp only [tieW, tieE] at this
  exact hT.sep i' i this.symm

theorem nv_Ehat {D : BlockData N} (hT : TieOK D) (i : Fin D.T.t) {v : BVar N r D.T.t}
    (h1 : v ≠ scalZ N r D.T.t (Fin.castSucc i)) (h2 : v ≠ scalS N r D.T.t (Fin.castSucc i))
    (h3 : ∀ c, v ≠ chainEmb N r D.T.t (tieW hT i, c)) (h4 : ∀ c, v ≠ chainEmb N r D.T.t (tieE hT i, c)) :
    v ∉ (D.Ehat O (r := r) i).vars := by
  rw [Ehat_eq hT i]
  exact nv_add (nv_mul (nv_X h1) (nv_X h2)) (nv_sum _ fun c _ => nv_mul (nv_X (h3 c)) (nv_X (h4 c)))

theorem nv_Eplus (D : BlockData N) {v : BVar N r D.T.t}
    (h1 : v ≠ scalZ N r D.T.t (Fin.last D.T.t)) (h2 : v ≠ scalS N r D.T.t (Fin.last D.T.t))
    (h3 : ∀ c, v ≠ Sum.inl (Fin.castSucc D.uPos, c)) (h4 : ∀ c, v ≠ xiVar N r D.T.t c) :
    v ∉ (D.Eplus O (r := r)).vars := by
  unfold BlockData.Eplus
  exact nv_add (nv_mul (nv_X h1) (nv_X h2)) (nv_sum _ fun c _ => nv_mul (nv_X (h3 c)) (nv_X (h4 c)))

theorem nv_xi {t b : ℕ} {v : BVar N r t} (h : ∀ c, v ≠ xiVar N r t c) {g : MvPolynomial (BVar N r t) (KK O)}
    (hg : g ∈ XiPolZ O N r t b) : v ∉ g.vars := by
  intro hv
  obtain ⟨m, hm, hvm⟩ := (MvPolynomial.mem_vars_iff_mem_support v).1 hv
  have h1 := (MvPolynomial.mem_restrictSupport_iff (KK O)).1 (Submodule.mem_inf.1 hg).1 hm
  obtain ⟨c, hc⟩ := h1.1 v hvm
  exact h c hc

def OddV (D : BlockData N) : BVar N r D.T.t → Prop
  | Sum.inl (a, _) => a ≠ Fin.castSucc D.uPos ∧ a ≠ Fin.last N
  | Sum.inr (l, _) => l ≠ Fin.last D.T.t

theorem tail_chain (D : BlockData N) (jp : ℕ) (a0 : Fin N) (ha0 : a0 ≠ D.uPos) (c : Fin r) (b : ℕ)
    (y : MvPolynomial (Fin N × Fin r) (KK O)) {g : MvPolynomial (BVar N r D.T.t) (KK O)}
    (hg : g ∈ XiPolZ O N r D.T.t (D.B - jp)) :
    cth (chainEmb N r D.T.t (a0, c)) b (tailP O r D jp y g) = tailP O r D jp (cth (a0, c) b y) g := by
  have hfree : ∀ F : MvPolynomial (BVar N r D.T.t) (KK O), chainEmb N r D.T.t (a0, c) ∉ F.vars →
      ∀ μ ∈ F.support, μ (chainEmb N r D.T.t (a0, c)) = 0 := by
    intro F h μ hμ
    by_contra hne
    exact h ((MvPolynomial.mem_vars_iff_mem_support _).2 ⟨μ, hμ, Finsupp.mem_support_iff.2 hne⟩)
  have hE : chainEmb N r D.T.t (a0, c) ∉ (D.Eplus O (r := r)).vars := by
    refine nv_Eplus D ?_ ?_ ?_ ?_
    · simp [chainEmb, scalZ]
    · simp [chainEmb, scalS]
    · intro c' h
      simp only [chainEmb, Sum.inl.injEq, Prod.mk.injEq] at h
      exact ha0 (Fin.castSucc_injective _ h.1)
    · intro c' h
      simp only [chainEmb, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
      exact Fin.castSucc_ne_last _ h.1
  have hP : chainEmb N r D.T.t (a0, c) ∉ (D.Eplus O (r := r) ^ jp *
      (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) *
      X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus : MvPolynomial (BVar N r D.T.t) (KK O)).vars := by
    refine nv_mul (nv_mul (nv_pow hE jp) (nv_prod _ fun i _ => nv_pow (nv_X ?_) _)) (nv_pow (nv_X ?_) _)
    · simp [chainEmb, scalZ]
    · simp [chainEmb, scalZ]
  have hg' : chainEmb N r D.T.t (a0, c) ∉ g.vars := by
    refine nv_xi (fun c' h => ?_) hg
    simp only [chainEmb, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
    exact Fin.castSucc_ne_last _ h.1
  have key : ∀ Y : MvPolynomial (Fin N × Fin r) (KK O), tailP O r D jp Y g =
      (D.Eplus O (r := r) ^ jp * (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) *
        X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus) * (g * rename (chainEmb N r D.T.t) Y) := by
    intro Y
    unfold tailP
    ring
  rw [key, key, cth_mul_free _ _ (hfree _ hP), cth_mul_free _ _ (hfree _ hg'),
    cth_rename _ (chainEmb_inj N r D.T.t)]

end GlobalTheory

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees

section GlobalTheory

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)] {N r : ℕ} [NeZero r]

theorem yjtZ_mono (LL : ChainLetters N) {q : ℕ} (J : Fin q → ℕ) {thr thr' : Fin q → WithTop ℤ} (h : ∀ k, thr k ≤ thr' k)
    {y : MvPolynomial (Fin N × Fin r) (KK O)} (hy : y ∈ YjtZ O (r := r) LL J thr) : y ∈ YjtZ O (r := r) LL J thr' :=
  ⟨yjt_mono' _ _ h hy.1, hy.2⟩

theorem le_add_nat (x : WithTop ℤ) (b : ℕ) : x ≤ x + ((b : ℤ) : WithTop ℤ) :=
  le_add_of_nonneg_right (by exact_mod_cast Int.natCast_nonneg b)

theorem otherE_free {D : BlockData N} (hT : TieOK D) (j : Fin D.T.t → ℕ) (i : Fin D.T.t) {v : BVar N r D.T.t}
    (h : ∀ i', i' ≠ i → v ∉ (D.Ehat O (r := r) i').vars) : FreeV v (otherE O r D j i) := by
  classical
  unfold otherE
  exact freeV_of_vars (nv_prod _ fun i' hi' => nv_pow (h i' (Finset.ne_of_mem_erase hi')) _)

theorem cth_gen (D7 : Formalism.BasicNotions.D7) {D : BlockData N} (hT : TieOK D) {thr thr' : Fin D.T.q → WithTop ℤ} (n : ℕ)
    (hthr : ∀ k, thr k + ((n : ℤ) : WithTop ℤ) ≤ thr' k) (v : BVar N r D.T.t) (hv : OddV D v)
    {j : Fin D.T.t → ℕ} {jp : ℕ} (hL : D.LevelOK j jp)
    {y : MvPolynomial (Fin N × Fin r) (KK O)} (hy : y ∈ YjtZ O (r := r) (D.lettersAt j jp) D.T.J thr)
    {g : MvPolynomial (BVar N r D.T.t) (KK O)} (hg : g ∈ XiPolZ O N r D.T.t (D.B - jp)) :
    cth v n ((∏ i, D.Ehat O (r := r) i ^ j i) * tailP O r D jp y g) ∈ SSt O r D thr' := by
  classical
  have hXX : ∀ i c, IsMult O r D.LL.vec D.T.J (tieW hT i) (tieE hT i) (X (tieW hT i, c) * X (tieE hT i, c)) :=
    fun i c => isMult_XX D7 D.LL.vec D.T.J _ _ (tieW_ne_tieE hT i i) (hT.vecE i _) c c
  have hPP : ∀ i, IsMult O r D.LL.vec D.T.J (tieW hT i) (tieE hT i) (-(pairP O r hT i)) :=
    fun i => (IsMult.sum _ fun c _ => hXX i c).neg
  rcases v with ⟨a, c⟩ | ⟨l, s⟩
  ·
    obtain ⟨ha1, ha2⟩ := hv
    obtain ⟨a0, rfl⟩ : ∃ a0 : Fin N, a = Fin.castSucc a0 := ⟨a.castPred ha2, (Fin.castSucc_castPred a ha2).symm⟩
    have ha0 : a0 ≠ D.uPos := fun h => ha1 (by rw [h])
    have hv' : (Sum.inl (Fin.castSucc a0, c) : BVar N r D.T.t) = chainEmb N r D.T.t (a0, c) := rfl
    rw [hv']
    have Hc : ∀ b, b ≤ n → ∃ (cb : ℕ) (yb : MvPolynomial (Fin N × Fin r) (KK O)),
        yb ∈ YjtZ O (r := r) (D.lettersAt j jp) D.T.J (fun k => thr k + ((b : ℤ) : WithTop ℤ)) ∧
        cth (chainEmb N r D.T.t (a0, c)) b (tailP O r D jp y g) = cb • tailP O r D jp yb g := fun b _ =>
      ⟨1, cth (a0, c) b y, yjtZ_cth D7 _ _ b (fun _ => le_rfl) _ hy, by rw [tail_chain D jp a0 ha0 c b y hg, one_smul]⟩
    have hZS : ∀ i', chainEmb N r D.T.t (a0, c) ≠ scalZ N r D.T.t (Fin.castSucc i') ∧
        chainEmb N r D.T.t (a0, c) ≠ scalS N r D.T.t (Fin.castSucc i') := fun i' => by
      constructor <;> simp [chainEmb, scalZ, scalS]
    have hemb : ∀ {x x' : Fin N × Fin r}, x ≠ x' → chainEmb N r D.T.t x ≠ chainEmb N r D.T.t x' :=
      fun h h' => h (chainEmb_inj N r D.T.t h')
    by_cases hW : ∃ i, a0 = tieW hT i
    · obtain ⟨i, rfl⟩ := hW
      refine tie_mem hT n hthr hL i _ (m' := X (chainEmb N r D.T.t (tieE hT i, c)))
        (E' := X (scalZ N r D.T.t (Fin.castSucc i)) * X (scalS N r D.T.t (Fin.castSucc i)) +
          ∑ c' ∈ Finset.univ.erase c, X (chainEmb N r D.T.t (tieW hT i, c')) * X (chainEmb N r D.T.t (tieE hT i, c')))
        ?_ ?_ ?_ (hXX i c) false ?_ ?_ hg Hc
      · rw [Ehat_eq hT, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ c)]
        ring
      · exact freeV_of_vars (nv_X (hemb fun h => tieW_ne_tieE hT i i (congrArg Prod.fst h)))
      · refine freeV_of_vars (nv_add (nv_mul (nv_X (hZS i).1) (nv_X (hZS i).2)) (nv_sum _ fun c' hc' =>
          nv_mul (nv_X (hemb fun h => Finset.ne_of_mem_erase hc' (congrArg Prod.snd h).symm))
            (nv_X (hemb fun h => tieW_ne_tieE hT i i (congrArg Prod.fst h)))))
      · simp only [Bool.false_eq_true, if_false, zero_add, map_mul, rename_X]
      · refine otherE_free hT j i fun i' hi' => nv_Ehat hT i' (hZS i').1 (hZS i').2
          (fun c' => hemb fun h => hi' (hT.inj _ _ (congrArg Fin.val (congrArg Prod.fst h)).symm))
          (fun c' => hemb fun h => tieW_ne_tieE hT i i' (congrArg Prod.fst h))
    · by_cases hE : ∃ i, a0 = tieE hT i
      · obtain ⟨i, rfl⟩ := hE
        refine tie_mem hT n hthr hL i _ (m' := X (chainEmb N r D.T.t (tieW hT i, c)))
          (E' := X (scalZ N r D.T.t (Fin.castSucc i)) * X (scalS N r D.T.t (Fin.castSucc i)) +
            ∑ c' ∈ Finset.univ.erase c, X (chainEmb N r D.T.t (tieW hT i, c')) * X (chainEmb N r D.T.t (tieE hT i, c')))
          ?_ ?_ ?_ (hXX i c) false ?_ ?_ hg Hc
        · rw [Ehat_eq hT, ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ c)]
          ring
        · exact freeV_of_vars (nv_X (hemb fun h => tieW_ne_tieE hT i i (congrArg Prod.fst h).symm))
        · refine freeV_of_vars (nv_add (nv_mul (nv_X (hZS i).1) (nv_X (hZS i).2)) (nv_sum _ fun c' hc' =>
            nv_mul (nv_X (hemb fun h => tieW_ne_tieE hT i i (congrArg Prod.fst h).symm))
              (nv_X (hemb fun h => Finset.ne_of_mem_erase hc' (congrArg Prod.snd h).symm))))
        · simp only [Bool.false_eq_true, if_false, zero_add, map_mul, rename_X]
          ring
        · refine otherE_free hT j i fun i' hi' => nv_Ehat hT i' (hZS i').1 (hZS i').2
            (fun c' => hemb fun h => tieW_ne_tieE hT i' i (congrArg Prod.fst h).symm)
            (fun c' => hemb fun h => hi' (hT.inj _ _ (by
              have := congrArg Fin.val (congrArg Prod.fst h)
              simp only [tieE] at this
              omega)))
      ·
        push_neg at hW hE
        have hfree : FreeV (chainEmb N r D.T.t (a0, c)) (∏ i, D.Ehat O (r := r) i ^ j i) :=
          freeV_of_vars (nv_prod _ fun i' _ => nv_pow (nv_Ehat hT i' (hZS i').1 (hZS i').2
            (fun c' => hemb fun h => hW i' (congrArg Prod.fst h))
            (fun c' => hemb fun h => hE i' (congrArg Prod.fst h))) _)
        rw [cth_mul_free _ _ hfree, tail_chain D jp a0 ha0 c n y hg]
        exact gen_mem D thr' hL (yjtZ_cth D7 _ _ n hthr _ hy) hg
  ·
    have hl : l ≠ Fin.last D.T.t := hv
    obtain ⟨i, rfl⟩ : ∃ i : Fin D.T.t, l = Fin.castSucc i := ⟨l.castPred hl, (Fin.castSucc_castPred l hl).symm⟩
    have hch : ∀ x, chainEmb N r D.T.t x ≠ (Sum.inr (Fin.castSucc i, s) : BVar N r D.T.t) := fun x => by
      simp [chainEmb]
    have hoth : FreeV (Sum.inr (Fin.castSucc i, s) : BVar N r D.T.t) (otherE O r D j i) := by
      refine otherE_free hT j i fun i' hi' => nv_Ehat hT i' ?_ ?_ (fun c' => (hch _).symm) (fun c' => (hch _).symm)
      · simp only [scalZ, ne_eq, Sum.inr.injEq, Prod.mk.injEq, Fin.castSucc_inj, not_and]
        exact fun h => absurd h.symm hi'
      · simp only [scalS, ne_eq, Sum.inr.injEq, Prod.mk.injEq, Fin.castSucc_inj, not_and]
        exact fun h => absurd h.symm hi'
    have hrest : ∀ (F : MvPolynomial (BVar N r D.T.t) (KK O)),
        (Sum.inr (Fin.castSucc i, s) : BVar N r D.T.t) ∉ F.vars →
        (Sum.inr (Fin.castSucc i, s) : BVar N r D.T.t) ∉ (D.Eplus O (r := r) ^ jp * F *
          X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus * rename (chainEmb N r D.T.t) y * g).vars := by
      intro F hF
      refine nv_mul (nv_mul (nv_mul (nv_mul (nv_pow (nv_Eplus D ?_ ?_ ?_ ?_) _) hF) (nv_pow (nv_X ?_) _))
        (nv_rename _ hch y)) (nv_xi ?_ hg)
      · simp only [scalZ, ne_eq, Sum.inr.injEq, Prod.mk.injEq, not_and]
        exact fun h => absurd h (Fin.castSucc_lt_last i).ne
      · simp only [scalS, ne_eq, Sum.inr.injEq, Prod.mk.injEq, not_and]
        exact fun h => absurd h (Fin.castSucc_lt_last i).ne
      · intro c'; simp
      · intro c'; simp [xiVar]
      · simp only [scalZ, ne_eq, Sum.inr.injEq, Prod.mk.injEq, not_and]
        exact fun h => absurd h (Fin.castSucc_lt_last i).ne
      · intro c'; simp [xiVar]
    have hpair : (Sum.inr (Fin.castSucc i, s) : BVar N r D.T.t) ∉
        (rename (chainEmb N r D.T.t) (pairP O r hT i)).vars := nv_rename _ hch _
    cases s with
    | false =>
      refine tie_mem hT n hthr hL i _ (m' := X (scalS N r D.T.t (Fin.castSucc i)))
        (E' := rename (chainEmb N r D.T.t) (pairP O r hT i)) (Ehat_eq' hT i) ?_ (freeV_of_vars hpair) (hPP i) true ?_
        hoth hg ?_
      · exact freeV_of_vars (nv_X (by simp [scalS, scalZ]))
      · simp only [if_true]
        rw [Ehat_eq' hT i, map_neg]
        ring
      · intro b _
        refine ⟨(D.T.z i).choose b, y, yjtZ_mono _ _ (fun k => le_add_nat _ b) hy, ?_⟩
        have e : tailP O r D jp y g = (D.Eplus O (r := r) ^ jp *
            (∏ i' ∈ Finset.univ.erase i, X (scalZ N r D.T.t (Fin.castSucc i')) ^ D.T.z i') *
            X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus * rename (chainEmb N r D.T.t) y * g) *
            X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i := by
          unfold tailP
          rw [← Finset.mul_prod_erase Finset.univ (fun i' => (X (scalZ N r D.T.t (Fin.castSucc i')) :
            MvPolynomial (BVar N r D.T.t) (KK O)) ^ D.T.z i') (Finset.mem_univ i)]
          ring
        have hfr := freeV_of_vars (hrest (∏ i' ∈ Finset.univ.erase i, X (scalZ N r D.T.t (Fin.castSucc i')) ^ D.T.z i')
          (nv_prod _ fun i' hi' => nv_pow (nv_X (by
            simp only [scalZ, ne_eq, Sum.inr.injEq, Prod.mk.injEq, Fin.castSucc_inj, and_true]
            exact fun h => Finset.ne_of_mem_erase hi' h.symm)) _))
        have hfr' : FreeV (scalZ N r D.T.t (Fin.castSucc i)) _ := hfr
        rw [e, cth_mul_free _ _ hfr', cth_X_pow, mul_smul_comm]
    | true =>
      refine tie_mem hT n hthr hL i _ (m' := X (scalZ N r D.T.t (Fin.castSucc i)))
        (E' := rename (chainEmb N r D.T.t) (pairP O r hT i)) ?_ ?_ (freeV_of_vars hpair) (hPP i) true ?_
        hoth hg ?_
      · rw [Ehat_eq' hT i]
        unfold scalS
        ring
      · exact freeV_of_vars (nv_X (by simp [scalZ]))
      · simp only [if_true]
        rw [Ehat_eq' hT i, map_neg]
        unfold scalS
        ring
      · intro b _
        have hfr : FreeV (Sum.inr (Fin.castSucc i, true) : BVar N r D.T.t) (tailP O r D jp y g) := by
          unfold tailP
          exact freeV_of_vars (hrest _ (nv_prod _ fun i' _ => nv_pow (nv_X (by simp [scalZ])) _))
        by_cases hb : b = 0
        · subst hb
          exact ⟨1, y, yjtZ_mono _ _ (fun k => le_add_nat _ 0) hy, by rw [cth_zero, one_smul]⟩
        · exact ⟨0, y, yjtZ_mono _ _ (fun k => le_add_nat _ b) hy, by rw [cth_free _ hfr hb, zero_smul]⟩

theorem cth_SSt (D7 : Formalism.BasicNotions.D7) {D : BlockData N} (hT : TieOK D) {thr thr' : Fin D.T.q → WithTop ℤ} (n : ℕ)
    (hthr : ∀ k, thr k + ((n : ℤ) : WithTop ℤ) ≤ thr' k) (v : BVar N r D.T.t) (hv : OddV D v)
    {u : MvPolynomial (BVar N r D.T.t) (KK O)} (hu : u ∈ SSt O r D thr) : cth v n u ∈ SSt O r D thr' := by
  have hle : SSt O r D thr ≤ (SSt O r D thr').comap ((cthL v n).restrictScalars O) := by
    unfold SSt BlockData.SSZ
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨j, jp, hL, y, hy, g, hg, rfl⟩ := hx
    have h := cth_gen D7 hT n hthr v hv hL hy hg
    unfold tailP at h
    simp only [← mul_assoc] at h
    exact h
  exact hle hu

end GlobalTheory

end Formalism.MainNotions.ColumnSystems.Pf
end
end

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees

theorem op_single_add {K σ : Type} [Field K] (a : σ) (b : ℕ) (f : σ →₀ ℕ) (ha : a ∉ f.support) (u : MvPolynomial σ K) :
    monomial (Finsupp.single a b + f) (1 : K) * divDer (Finsupp.single a b + f) u =
      cth a b (monomial f (1 : K) * divDer f u) := by
  classical
  ext μ
  rw [eig_one, coeff_cth, eig_one]
  have hd : Disjoint (Finsupp.single a b).support f.support := by
    refine Finset.disjoint_of_subset_left Finsupp.support_single_subset ?_
    rw [Finset.disjoint_singleton_left]
    exact ha
  rw [Finsupp.prod_add_index_of_disjoint hd, Finsupp.prod_single_index (by simp)]
  push_cast
  ring

section GlobalTheory

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)] {N r : ℕ} [NeZero r]

theorem op_SSt (D7 : Formalism.BasicNotions.D7) {D : BlockData N} (hT : TieOK D) (ν : BVar N r D.T.t →₀ ℕ) :
    (∀ v ∈ ν.support, OddV D v) → ∀ (thr thr' : Fin D.T.q → WithTop ℤ),
    (∀ k, thr k + (((ν.sum fun _ n => n : ℕ) : ℤ) : WithTop ℤ) ≤ thr' k) →
    ∀ u ∈ SSt O r D thr, monomial ν (1 : KK O) * divDer ν u ∈ SSt O r D thr' := by
  classical
  induction ν using Finsupp.induction with
  | zero =>
    intro _ thr thr' hthr u hu
    rw [divDer_zero]
    have : (monomial (0 : BVar N r D.T.t →₀ ℕ) (1 : KK O)) = 1 := rfl
    rw [this, one_mul]
    exact SSt_mono D (fun k => by simpa using hthr k) hu
  | single_add a b f ha hb ih =>
    intro hv thr thr' hthr u hu
    rw [op_single_add a b f ha]
    have hsum : ((Finsupp.single a b + f).sum fun _ n => n) = b + f.sum fun _ n => n := by
      rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl), Finsupp.sum_single_index rfl]
    have hsupp : (Finsupp.single a b + f).support = insert a f.support := by
      rw [Finsupp.support_add_eq, Finsupp.support_single _ hb]
      · rfl
      · rw [Finsupp.support_single _ hb, Finset.disjoint_singleton_left]
        exact ha
    have h1 := ih (fun v hvf => hv v (by rw [hsupp]; exact Finset.mem_insert_of_mem hvf)) thr
      (fun k => thr k + (((f.sum fun _ n => n : ℕ) : ℤ) : WithTop ℤ)) (fun _ => le_rfl) u hu
    refine cth_SSt D7 hT b (fun k => ?_) a (hv a (by rw [hsupp]; exact Finset.mem_insert_self _ _)) h1
    refine le_trans (le_of_eq ?_) (hthr k)
    rw [hsum, add_assoc]
    push_cast
    rw [add_comm ((b : ℕ) : WithTop ℤ)]

end GlobalTheory

theorem tieOK_blockBase (p : ℕ) {r s : ℕ} (S : SegData s) (aTop : Fin s → ℕ) (aPlus : ℕ) (b : SegBlock s r) :
    TieOK (blockBase p S aTop aPlus b) := by
  refine { lt := ?_, inj := ?_, sep := ?_, uW := ?_, vecE := ?_ }
  · intro i
    have := (uTop S i).2
    show 2 * ((uTop S i : Fin s) : ℕ) + 1 < 2 * s + 1
    omega
  · intro i i' h
    have h' : 2 * ((uTop S i : Fin s) : ℕ) = 2 * ((uTop S i' : Fin s) : ℕ) := h
    simp only [uTop] at h'
    exact Fin.ext (by omega)
  · intro i i' h
    have h' : 2 * ((uTop S i : Fin s) : ℕ) + 1 = 2 * ((uTop S i' : Fin s) : ℕ) := h
    omega
  · intro i
    have := (uTop S i).2
    constructor
    · show 2 * ((uTop S i : Fin s) : ℕ) ≠ 2 * s
      omega
    · show 2 * ((uTop S i : Fin s) : ℕ) + 1 ≠ 2 * s
      omega
  · intro i h
    show decide ((2 * ((uTop S i : Fin s) : ℕ) + 1) % 2 = 0) = false
    simp

theorem thr_shift (x : WithTop ℤ) (mm : ℝ) (n c4 : ℕ) (h : n ≤ c4) :
    x.map (fun y : ℤ => ⌊(y : ℝ) - mm⌋) + ((n : ℤ) : WithTop ℤ) ≤ x.map (fun y : ℤ => ⌊(y : ℝ) - (mm - (c4 : ℝ))⌋) := by
  cases x with
  | top => simp
  | coe y =>
    simp only [WithTop.map_coe]
    have e : (y : ℝ) - (mm - (c4 : ℝ)) = ((y : ℝ) - mm) + (c4 : ℝ) := by ring
    rw [e, Int.floor_add_natCast]
    have : ⌊(y : ℝ) - mm⌋ + (n : ℤ) ≤ ⌊(y : ℝ) - mm⌋ + (c4 : ℤ) := by omega
    exact_mod_cast this

theorem gThetaAt (D7 : Formalism.BasicNotions.D7) : GThetaAt := by
  intro C0 CE1 CE2 X _ O _ _ _ _ j b _ c T q hT mm u hu
  unfold gOp
  refine Submodule.sum_mem _ fun ν hν => Submodule.smul_mem _ _ ?_
  have hTie := tieOK_blockBase X.p (r := X.m) (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b
  refine op_SSt (O := O) (r := X.m) D7 hTie ν ?_
    (fun k => (segmentCapacities X.p (X.seg C0 CE1 CE2 j) b k).map (fun y : ℤ => ⌊(y : ℝ) - mm⌋))
    (fun k => (segmentCapacities X.p (X.seg C0 CE1 CE2 j) b k).map (fun y : ℤ => ⌊(y : ℝ) - (mm - 4 * (c : ℝ))⌋)) ?_ u hu
  · intro v hv
    have h := (hT ν hν).2 v hv
    rcases v with ⟨a, c'⟩ | ⟨l, s⟩
    · have h' : (a : ℕ) < 2 * segS X.TT j := h
      constructor
      · intro e
        have := congrArg Fin.val e
        simp only [Fin.val_castSucc] at this
        have h2 : ((blockBase X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b).uPos : ℕ) =
          2 * segS X.TT j := rfl
        omega
      · intro e
        have := congrArg Fin.val e
        simp only [Fin.val_last] at this
        omega
    · have h' : (l : ℕ) < (X.seg C0 CE1 CE2 j).t := h
      intro e
      have := congrArg Fin.val e
      have h2 : ((Fin.last (blockBase X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) b).T.t :
        Fin _) : ℕ) = (X.seg C0 CE1 CE2 j).t := rfl
      omega
  · intro k
    have := thr_shift (segmentCapacities X.p (X.seg C0 CE1 CE2 j) b k) mm (ν.sum fun _ n => n) (4 * c) (hT ν hν).1
    have e : (((4 * c : ℕ) : ℕ) : ℝ) = 4 * (c : ℝ) := by push_cast; ring
    rw [e] at this
    exact this

end Formalism.MainNotions.ColumnSystems.Pf
