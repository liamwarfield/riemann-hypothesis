module

public import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.SmulMemOfNorm

@[expose] public section

section -- merged from Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.BiHomPlus
section -- merged from Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.ChainEmbInj
section -- merged from Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.LetterAtSuccVal
namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

section block
variable {N r : ℕ} (D : BlockData N)

def wv (i : Fin D.T.t) (c : Fin r) : BVar N r D.T.t := Sum.inl (finPos N (D.T.pos i), c)
def ev (i : Fin D.T.t) (c : Fin r) : BVar N r D.T.t := Sum.inl (finPos N (D.T.pos i + 1), c)
def zi (r : ℕ) (i : Fin D.T.t) : BVar N r D.T.t := scalZ N r D.T.t (Fin.castSucc i)
def si (r : ℕ) (i : Fin D.T.t) : BVar N r D.T.t := scalS N r D.T.t (Fin.castSucc i)
def wU (c : Fin r) : BVar N r D.T.t := Sum.inl (Fin.castSucc D.uPos, c)
def zP (r : ℕ) : BVar N r D.T.t := scalZ N r D.T.t (Fin.last D.T.t)
def sP (r : ℕ) : BVar N r D.T.t := scalS N r D.T.t (Fin.last D.T.t)

variable {D}

theorem pos_succ_lt (hB : D.BlockOK) (i : Fin D.T.t) : D.T.pos i + 1 + 1 < N := by
  obtain ⟨_, h2, _, h4⟩ := hB
  have := h2 i
  omega

theorem finPos_pos_val (hB : D.BlockOK) (i : Fin D.T.t) : (finPos N (D.T.pos i)).val = D.T.pos i := by
  have := pos_succ_lt hB i
  show min (D.T.pos i) N = D.T.pos i
  omega

theorem finPos_succ_val (hB : D.BlockOK) (i : Fin D.T.t) :
    (finPos N (D.T.pos i + 1)).val = D.T.pos i + 1 := by
  have := pos_succ_lt hB i
  show min (D.T.pos i + 1) N = D.T.pos i + 1
  omega

theorem letterAt_pos_val (hB : D.BlockOK) (i : Fin D.T.t) : (D.letterAt (D.T.pos i)).val = D.T.pos i := by
  have := pos_succ_lt hB i
  show min (D.T.pos i) (N - 1) = D.T.pos i
  omega

theorem letterAt_succ_val (hB : D.BlockOK) (i : Fin D.T.t) :
    (D.letterAt (D.T.pos i + 1)).val = D.T.pos i + 1 := by
  have := pos_succ_lt hB i
  show min (D.T.pos i + 1) (N - 1) = D.T.pos i + 1
  omega

theorem pos_inj (hB : D.BlockOK) {i i' : Fin D.T.t} (h : D.T.pos i = D.T.pos i') : i = i' := hB.1.1.injective h

theorem pos_ne_succ (hB : D.BlockOK) (i i' : Fin D.T.t) : D.T.pos i ≠ D.T.pos i' + 1 := by
  intro h
  obtain ⟨hi, hti, _⟩ := hB.1.2.1 i
  obtain ⟨hi', _, hfi'⟩ := hB.1.2.1 i'
  have e : D.LL.vec ⟨D.T.pos i, by omega⟩ = D.LL.vec ⟨D.T.pos i' + 1, hi'⟩ := congrArg D.LL.vec (Fin.ext h)
  rw [hti, hfi'] at e
  exact absurd e (by decide)

theorem pos_lt_u (hB : D.BlockOK) (i : Fin D.T.t) : D.T.pos i + 1 < (D.uPos : ℕ) := hB.2.1 i

theorem deg_lettersAt_pos (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) :
    (D.lettersAt j jp).deg (D.letterAt (D.T.pos i)) = D.LL.deg (D.letterAt (D.T.pos i)) - j i := by
  simp only [BlockData.lettersAt]
  simp only [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  have hs : (∑ i', if ((D.letterAt (D.T.pos i) : Fin N) : ℕ) = D.T.pos i' ∨
      ((D.letterAt (D.T.pos i) : Fin N) : ℕ) = D.T.pos i' + 1 then j i' else 0) = j i := by
    rw [Finset.sum_eq_single i]
    · simp [letterAt_pos_val hB]
    · intro b _ hb
      rw [if_neg]
      rw [letterAt_pos_val hB]
      rintro (h | h)
      · exact hb (pos_inj hB h).symm
      · exact pos_ne_succ hB i b h
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hu : D.letterAt (D.T.pos i) ≠ D.uPos := by
    intro h
    have h1 := congrArg Fin.val h
    rw [letterAt_pos_val hB] at h1
    have := pos_lt_u hB i
    omega
  rw [hs, if_neg hu, Nat.sub_zero]

theorem deg_lettersAt_pos_succ (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) :
    (D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)) = D.LL.deg (D.letterAt (D.T.pos i + 1)) - j i := by
  simp only [BlockData.lettersAt]
  simp only [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  have hs : (∑ i', if ((D.letterAt (D.T.pos i + 1) : Fin N) : ℕ) = D.T.pos i' ∨
      ((D.letterAt (D.T.pos i + 1) : Fin N) : ℕ) = D.T.pos i' + 1 then j i' else 0) = j i := by
    rw [Finset.sum_eq_single i]
    · simp [letterAt_succ_val hB]
    · intro b _ hb
      rw [if_neg]
      rw [letterAt_succ_val hB]
      rintro (h | h)
      · exact pos_ne_succ hB b i h.symm
      · exact hb (pos_inj hB (by omega)).symm
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hu : D.letterAt (D.T.pos i + 1) ≠ D.uPos := by
    intro h
    have h1 := congrArg Fin.val h
    rw [letterAt_succ_val hB] at h1
    have := pos_lt_u hB i
    omega
  rw [hs, if_neg hu, Nat.sub_zero]

theorem deg_U (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) :
    (D.lettersAt j jp).deg D.uPos = D.LL.deg D.uPos - jp := by
  simp only [BlockData.lettersAt]
  simp only [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  rw [Finset.sum_eq_zero (fun b _ => by
      rw [if_neg]
      have := pos_lt_u hB b
      omega)]
  simp

end block

end Formalism.InvariantFactorPaths.KP.LL
end

namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M
open scoped Pointwise

section lat
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)

noncomputable def Lat (j : Fin D.T.t → ℕ) (jp : ℕ) : Submodule ℤ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  Submodule.span ℤ_[p] {x | ∃ y ∈ YZ p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
    ∃ g ∈ XiPolZ p N r D.T.t (D.B - jp), x = rename (chainEmb N r D.T.t) y * g}

noncomputable def Pt (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  tieP (fun c => Sum.inl (finPos N (D.T.pos i), c)) (fun c => Sum.inl (finPos N (D.T.pos i + 1), c))
    (scalZ N r D.T.t (Fin.castSucc i)) (scalS N r D.T.t (Fin.castSucc i))
    ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i))) ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)))
    (D.T.z i) y

noncomputable def PL (L : List (Fin D.T.t)) (j : Fin D.T.t → ℕ) (jp : ℕ)
    (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) : MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  L.foldr (fun i acc => Pt p D j jp i acc) y

noncomputable def Pplus (jp : ℕ) (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) : MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  tieP (fun c => Sum.inl (Fin.castSucc D.uPos, c)) (fun c => xiVar N r D.T.t c)
    (scalZ N r D.T.t (Fin.last D.T.t)) (scalS N r D.T.t (Fin.last D.T.t))
    (D.LL.deg D.uPos - jp) (D.B - jp) D.zPlus y

theorem Pall_eq (j : Fin D.T.t → ℕ) (jp : ℕ) (y : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    D.Pall p j jp y = Pplus p D jp (PL p D (List.finRange D.T.t) j jp y) := rfl

variable {p D}

theorem wv_chain (hB : D.BlockOK) (i : Fin D.T.t) (c : Fin r) :
    wv D i c = chainEmb N r D.T.t (D.letterAt (D.T.pos i), c) := by
  simp only [wv, chainEmb, Sum.inl.injEq, Prod.mk.injEq, and_true]
  apply Fin.ext
  rw [finPos_pos_val hB, Fin.coe_castSucc, letterAt_pos_val hB]

theorem ev_chain (hB : D.BlockOK) (i : Fin D.T.t) (c : Fin r) :
    ev D i c = chainEmb N r D.T.t (D.letterAt (D.T.pos i + 1), c) := by
  simp only [ev, chainEmb, Sum.inl.injEq, Prod.mk.injEq, and_true]
  apply Fin.ext
  rw [finPos_succ_val hB, Fin.coe_castSucc, letterAt_succ_val hB]

theorem chainEmb_inj : Function.Injective (chainEmb N r D.T.t) := by
  intro x y h
  simp only [chainEmb, Sum.inl.injEq, Prod.mk.injEq, Fin.castSucc_inj] at h
  exact Prod.ext h.1 h.2

theorem xi_notin (c : Fin r) : xiVar N r D.T.t c ∉ Set.range (chainEmb N r D.T.t) := by
  rintro ⟨x, hx⟩
  simp only [chainEmb, xiVar, Sum.inl.injEq, Prod.mk.injEq] at hx
  exact (Fin.castSucc_lt_last x.1).ne hx.1

theorem supp_gen {y : MvPolynomial (Fin N × Fin r) ℚ_[p]} {g : MvPolynomial (BVar N r D.T.t) ℚ_[p]}
    {mon : BVar N r D.T.t →₀ ℕ} (hm : mon ∈ (rename (chainEmb N r D.T.t) y * g).support) :
    ∃ m1 ∈ y.support, ∃ m2 ∈ g.support, mon = Finsupp.mapDomain (chainEmb N r D.T.t) m1 + m2 := by
  classical
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul _ _ hm)
  rw [MvPolynomial.support_rename_of_injective chainEmb_inj] at ha
  obtain ⟨m1, hm1, rfl⟩ := Finset.mem_image.mp ha
  exact ⟨m1, hm1, b, hb, rfl⟩

theorem xi_supp {b : ℕ} {g : MvPolynomial (BVar N r D.T.t) ℚ_[p]} (hg : g ∈ XiPolZ p N r D.T.t b)
    {m2 : BVar N r D.T.t →₀ ℕ} (hm2 : m2 ∈ g.support) :
    (∀ v, (∀ c, v ≠ xiVar N r D.T.t c) → m2 v = 0) ∧ ∑ c, m2 (xiVar N r D.T.t c) = b := by
  have h1 := (Submodule.mem_inf.mp hg).1
  rw [Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff] at h1
  have h2 := h1 hm2
  refine ⟨fun v hv => ?_, h2.2⟩
  by_contra hne
  obtain ⟨c, hc⟩ := h2.1 v (Finsupp.mem_support_iff.mpr hne)
  exact hv c hc

end lat

end Formalism.InvariantFactorPaths.KP.LL
end

namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

section lat2
variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] {D : BlockData N}

theorem wv_ne_xi (hB : D.BlockOK) (i : Fin D.T.t) (c d : Fin r) : wv D i c ≠ xiVar N r D.T.t d := by
  intro h
  simp only [wv, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
  have h1 := congrArg Fin.val h.1
  rw [finPos_pos_val hB, Fin.val_last] at h1
  have := pos_succ_lt hB i
  omega

theorem ev_ne_xi (hB : D.BlockOK) (i : Fin D.T.t) (c d : Fin r) : ev D i c ≠ xiVar N r D.T.t d := by
  intro h
  simp only [ev, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
  have h1 := congrArg Fin.val h.1
  rw [finPos_succ_val hB, Fin.val_last] at h1
  have := pos_succ_lt hB i
  omega

theorem wU_ne_xi (c d : Fin r) : wU D c ≠ xiVar N r D.T.t d := by
  intro h
  simp only [wU, xiVar, Sum.inl.injEq, Prod.mk.injEq] at h
  exact (Fin.castSucc_lt_last _).ne h.1

theorem yz_pol {LL : Letters N} {q : ℕ} {J : Fin q → ℕ} {M : Fin q → WithTop ℤ}
    {y : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hy : y ∈ YZ p (r := r) LL J M) : y ∈ Pol p r LL :=
  (Submodule.mem_inf.1 (Submodule.mem_inf.1 hy).1).1

theorem yz_y {LL : Letters N} {q : ℕ} {J : Fin q → ℕ} {M : Fin q → WithTop ℤ}
    {y : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hy : y ∈ YZ p (r := r) LL J M) : y ∈ Y p (r := r) LL J M :=
  (Submodule.mem_inf.1 hy).1

theorem yz_int {LL : Letters N} {q : ℕ} {J : Fin q → ℕ} {M : Fin q → WithTop ℤ}
    {y : MvPolynomial (Fin N × Fin r) ℚ_[p]} (hy : y ∈ YZ p (r := r) LL J M) : y ∈ IntPol p (Fin N × Fin r) :=
  (Submodule.mem_inf.1 (Submodule.mem_inf.1 hy).2).2

theorem yz_mk {LL : Letters N} {q : ℕ} {J : Fin q → ℕ} {M : Fin q → WithTop ℤ}
    {y : MvPolynomial (Fin N × Fin r) ℚ_[p]} (h1 : y ∈ Y p (r := r) LL J M) (h2 : y ∈ IntPol p (Fin N × Fin r)) :
    y ∈ YZ p (r := r) LL J M :=
  Submodule.mem_inf.2 ⟨h1, Submodule.mem_inf.2 ⟨(Submodule.mem_inf.1 h1).1, h2⟩⟩

omit [NeZero r] in
theorem biHom_span {r' : ℕ} {w e : Fin r' → BVar N r D.T.t} {a b : ℕ} {S : Set (MvPolynomial (BVar N r D.T.t) ℚ_[p])}
    (h : ∀ x ∈ S, BiHom w e a b x) : ∀ x ∈ Submodule.span ℤ_[p] S, BiHom w e a b x := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hxS => exact h x hxS
  | zero => intro m hm; simp at hm
  | add x y _ _ hx hy =>
    intro m hm
    rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h' | h'
    · exact hx m h'
    · exact hy m h'
  | smul a x _ hx =>
    intro m hm
    exact hx m (MvPolynomial.support_smul hm)

theorem biHom_tie (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) :
    ∀ x ∈ Lat p D (r := r) j jp, BiHom (wv D i) (ev D i) ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i)))
      ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1))) x := by
  intro x hx
  refine biHom_span (S := {x | ∃ y ∈ YZ p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
    ∃ g ∈ XiPolZ p N r D.T.t (D.B - jp), x = rename (chainEmb N r D.T.t) y * g}) ?_ x hx
  rintro _ ⟨y, hy, g, hg, rfl⟩ m hm
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := supp_gen (p := p) (D := D) (hm := hm)
  have hdeg : MultiDeg (D.lettersAt j jp) m1 :=
    ((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).1 (yz_pol hy)) hm1
  have hxi := (xi_supp (p := p) (D := D) (hg := hg) (hm2 := hm2))
  constructor
  · simp only [Finsupp.add_apply]
    rw [Finset.sum_add_distrib]
    have e1 : ∀ c, Finsupp.mapDomain (chainEmb N r D.T.t) m1 (wv D i c) = m1 (D.letterAt (D.T.pos i), c) := fun c => by
      rw [wv_chain (hB := hB), Finsupp.mapDomain_apply_of_injective (chainEmb_inj (D := D))]
    have e2 : ∀ c, m2 (wv D i c) = 0 := fun c => hxi.1 _ (fun d => wv_ne_xi hB i c d)
    simp only [e1, e2, Finset.sum_const_zero, add_zero]
    exact hdeg _
  · simp only [Finsupp.add_apply]
    rw [Finset.sum_add_distrib]
    have e1 : ∀ c, Finsupp.mapDomain (chainEmb N r D.T.t) m1 (ev D i c) = m1 (D.letterAt (D.T.pos i + 1), c) := fun c => by
      rw [ev_chain (hB := hB), Finsupp.mapDomain_apply_of_injective (chainEmb_inj (D := D))]
    have e2 : ∀ c, m2 (ev D i c) = 0 := fun c => hxi.1 _ (fun d => ev_ne_xi hB i c d)
    simp only [e1, e2, Finset.sum_const_zero, add_zero]
    exact hdeg _

theorem biHom_plus (j : Fin D.T.t → ℕ) (jp : ℕ) :
    ∀ x ∈ Lat p D (r := r) j jp, BiHom (wU D) (xiVar N r D.T.t) ((D.lettersAt j jp).deg D.uPos) (D.B - jp) x := by
  intro x hx
  refine biHom_span (S := {x | ∃ y ∈ YZ p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
    ∃ g ∈ XiPolZ p N r D.T.t (D.B - jp), x = rename (chainEmb N r D.T.t) y * g}) ?_ x hx
  rintro _ ⟨y, hy, g, hg, rfl⟩ m hm
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := supp_gen (p := p) (D := D) (hm := hm)
  have hdeg : MultiDeg (D.lettersAt j jp) m1 :=
    ((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).1 (yz_pol hy)) hm1
  have hxi := (xi_supp (p := p) (D := D) (hg := hg) (hm2 := hm2))
  constructor
  · simp only [Finsupp.add_apply]
    rw [Finset.sum_add_distrib]
    have e1 : ∀ c, Finsupp.mapDomain (chainEmb N r D.T.t) m1 (wU D c) = m1 (D.uPos, c) := fun c => by
      show Finsupp.mapDomain (chainEmb N r D.T.t) m1 (chainEmb N r D.T.t (D.uPos, c)) = _
      rw [Finsupp.mapDomain_apply_of_injective (chainEmb_inj (D := D))]
    have e2 : ∀ c, m2 (wU D c) = 0 := fun c => hxi.1 _ (fun d => wU_ne_xi c d)
    simp only [e1, e2, Finset.sum_const_zero, add_zero]
    exact hdeg _
  · simp only [Finsupp.add_apply]
    rw [Finset.sum_add_distrib]
    have e1 : ∀ c, Finsupp.mapDomain (chainEmb N r D.T.t) m1 (xiVar N r D.T.t c) = 0 := fun c =>
      Finsupp.mapDomain_notin_range _ _ (xi_notin (D := D) c)
    simp only [e1, Finset.sum_const_zero, zero_add]
    exact hxi.2

end lat2

end Formalism.InvariantFactorPaths.KP.LL
end

namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

def PairStep : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (r : ℕ) (w e : Fin r → σ) (zv sv : σ), 1 ≤ r → (∀ c, w c ≠ zv ∧ e c ≠ zv) →
    ∀ (o n z L u : ℕ) (Λ : ℕ → Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])),
      (∀ l, ∀ x ∈ Λ l, ∀ m, min (o - l) (n - l) < m → (tieF w e ^ m) x = 0) →
      (∀ l m, m ≤ min o n → ∀ x ∈ Λ l,
        (((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • (tieF w e ^ m) x) ∈ Λ (l + m)) →
      r * L + Nat.log p (o + n + r + z) ≤ u →
      ∀ l ≤ min o n, ∀ x ∈ Λ l,
        ((p : ℚ_[p]) ^ u • (ehP w e zv sv ^ l * (X zv ^ z * x)) ∈ Submodule.span ℤ_[p]
          {v | ∃ l' ≤ min o n, ∃ x' ∈ Λ l', v = ehP w e zv sv ^ l' * tieP w e zv sv (o - l') (n - l') z x'}) ∧
        ((p : ℚ_[p]) ^ u • (ehP w e zv sv ^ l * tieP w e zv sv (o - l) (n - l) z x) ∈ Submodule.span ℤ_[p]
          {v | ∃ l' ≤ min o n, ∃ x' ∈ Λ l', v = ehP w e zv sv ^ l' * (X zv ^ z * x')})

section block
variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (D : BlockData N)

def HypJoin : Prop :=
  ∀ (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t), ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
    Formalism.GM.tieF (fun c => (D.letterAt (D.T.pos i), c)) (fun c => (D.letterAt (D.T.pos i + 1), c)) y ∈
      Y p (r := r) (D.lettersAt (Function.update j i (j i + 1)) jp) D.T.J D.T.thr

def HypU : Prop :=
  ∀ (j : Fin D.T.t → ℕ) (jp : ℕ) (c : Fin r), ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
    pderiv (D.uPos, c) y ∈ Y p (r := r) (D.lettersAt j (jp + 1)) D.T.J D.T.thr

noncomputable def midGen (k : ℕ) (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    MvPolynomial (BVar N r D.T.t) ℚ_[p] :=
  (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
    (∏ i : Fin D.T.t with i.val < k, X (zi D r i) ^ D.T.z i) * X (zP D r) ^ D.zPlus *
    PL p D ((List.finRange D.T.t).drop k) j jp x

noncomputable def Mid (k : ℕ) : Submodule ℤ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  Submodule.span ℤ_[p] {v | ∃ (j : Fin D.T.t → ℕ) (jp : ℕ), D.LevelOK j jp ∧ ∃ x ∈ Lat p D (r := r) j jp,
    v = midGen p D k j jp x}

noncomputable def MidP : Submodule ℤ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  Submodule.span ℤ_[p] {v | ∃ (j : Fin D.T.t → ℕ) (jp : ℕ), D.LevelOK j jp ∧ ∃ x ∈ Lat p D (r := r) j jp,
    v = (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
      Pplus p D jp (PL p D (List.finRange D.T.t) j jp x)}

end block

def LatPlus : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), D.BlockOK → HypU p (r := r) D →
    ∀ (j : Fin D.T.t → ℕ) (jp m L : ℕ), Nat.log p m ≤ L → ∀ x ∈ Lat p D (r := r) j jp,
      (((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • (tieF (wU D) (xiVar N r D.T.t) ^ m) x) ∈
        Lat p D (r := r) j (jp + m)

def LatTie : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), D.BlockOK → HypJoin p (r := r) D →
    ∀ (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t) (m L : ℕ), Nat.log p m ≤ L → ∀ x ∈ Lat p D (r := r) j jp,
      (((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • (tieF (wv D i) (ev D i) ^ m) x) ∈
        Lat p D (r := r) (j + Pi.single i m) jp

def PLLin : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N) (L : List (Fin D.T.t)) (j : Fin D.T.t → ℕ) (jp : ℕ),
    (∃ T : MvPolynomial (BVar N r D.T.t) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (BVar N r D.T.t) ℚ_[p],
      ∀ x, T x = PL p D L j jp x) ∧
    ∃ T : MvPolynomial (BVar N r D.T.t) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (BVar N r D.T.t) ℚ_[p],
      ∀ x, T x = Pplus p D jp x

def CommPL : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), D.BlockOK →
    ∀ (L : List (Fin D.T.t)) (j : Fin D.T.t → ℕ) (jp m : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]),
      (∀ k : Fin D.T.t, k ∉ L →
        (tieF (wv D k) (ev D k) ^ m) (PL p D L j jp x) = PL p D L j jp ((tieF (wv D k) (ev D k) ^ m) x)) ∧
      (tieF (wU D) (xiVar N r D.T.t) ^ m) (PL p D L j jp x) =
        PL p D L j jp ((tieF (wU D) (xiVar N r D.T.t) ^ m) x)

def ParamPL : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), D.BlockOK →
    ∀ (L : List (Fin D.T.t)) (j j' : Fin D.T.t → ℕ) (jp jp' : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]),
      (∀ i ∈ L, j i = j' i) → PL p D L j jp x = PL p D L j' jp' x

def MidTop : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), Mid p (r := r) D D.T.t = D.SSZ p (r := r)

def MidPEq : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N), MidP p (r := r) D = D.PSZ p (r := r)

def JoinCondition : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N) (a u : ℕ), D.BlockOK → 1 ≤ r →
    (∀ x, D.LL.deg x ≤ 2 * a) → (∀ i, D.T.z i ≤ 2 * a) → HypJoin p (r := r) D →
    r * Nat.log p (2 * a) + Nat.log p (6 * a + r) ≤ u → ∀ k < D.T.t,
      (∀ v ∈ Mid p (r := r) D (k + 1), (p : ℚ_[p]) ^ u • v ∈ Mid p (r := r) D k) ∧
      (∀ v ∈ Mid p (r := r) D k, (p : ℚ_[p]) ^ u • v ∈ Mid p (r := r) D (k + 1))

def PlusCondition : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N) (a u : ℕ), D.BlockOK → 1 ≤ r →
    (∀ x, D.LL.deg x ≤ 2 * a) → D.B ≤ 2 * a → D.zPlus ≤ 2 * a → HypU p (r := r) D →
    r * Nat.log p (2 * a) + Nat.log p (6 * a + r) ≤ u →
      (∀ v ∈ Mid p (r := r) D 0, (p : ℚ_[p]) ^ u • v ∈ MidP p (r := r) D) ∧
      (∀ v ∈ MidP p (r := r) D, (p : ℚ_[p]) ^ u • v ∈ Mid p (r := r) D 0)

end Formalism.InvariantFactorPaths.KP.LL
