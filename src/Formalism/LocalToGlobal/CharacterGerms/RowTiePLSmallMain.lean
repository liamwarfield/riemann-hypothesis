module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupMonomialHolderLogConvex

@[expose] public section

section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePLSmall
section -- merged from Formalism.LocalToGlobal.CharacterGerms.RowTiePLSmallCv
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePLSmall

open PartialDerivEval RowTiePE0 RowTiePProj

section Bd

variable {C : Type} [Field C] {V : VF C}

def Bdd (V : VF C) (s : ℕ → C) : Prop := ∃ K : ℝ, ∀ n, V.Ge K (s n)

theorem bdd_const (x : C) : Bdd V (fun _ => x) := by
  obtain ⟨K, hK⟩ := exists_ge (V := V) x
  exact ⟨K, fun _ => hK⟩

theorem Bdd.add {s t : ℕ → C} (hs : Bdd V s) (ht : Bdd V t) : Bdd V (fun n => s n + t n) := by
  obtain ⟨K, hK⟩ := hs
  obtain ⟨L, hL⟩ := ht
  exact ⟨min K L, fun n => ((hK n).mono (min_le_left _ _)).add ((hL n).mono (min_le_right _ _))⟩

theorem Bdd.mul {s t : ℕ → C} (hs : Bdd V s) (ht : Bdd V t) : Bdd V (fun n => s n * t n) := by
  obtain ⟨K, hK⟩ := hs
  obtain ⟨L, hL⟩ := ht
  exact ⟨K + L, fun n => (hK n).mul (hL n)⟩

theorem Bdd.sum {ι : Type} (S : Finset ι) {s : ι → ℕ → C} (h : ∀ i ∈ S, Bdd V (s i)) :
    Bdd V (fun n => ∑ i ∈ S, s i n) := by
  first | exact GlobalTheory.ScalarStatement.main .. | (apply GlobalTheory.ScalarStatement.main <;> assumption) | (intros; apply GlobalTheory.ScalarStatement.main <;> assumption) | (apply @GlobalTheory.ScalarStatement.main <;> assumption) | (intros; apply @GlobalTheory.ScalarStatement.main <;> assumption) | (apply @GlobalTheory.ScalarStatement.main <;> first | assumption | infer_instance) | exact @GlobalTheory.ScalarStatement.main C ‹_› V ι S s h | exact @GlobalTheory.ScalarStatement.main C ‹_› V ι S s | exact @GlobalTheory.ScalarStatement.main C ‹_› V ι S | exact @GlobalTheory.ScalarStatement.main C ‹_› V ι | exact @GlobalTheory.ScalarStatement.main C ‹_› V | exact @GlobalTheory.ScalarStatement.main C ‹_› | exact @GlobalTheory.ScalarStatement.main C

theorem tends_mul_bdd {s t : ℕ → C} (hs : Bdd V s) (ht : Tends V t 0) : Tends V (fun n => s n * t n) 0 := by
  intro w
  obtain ⟨K, hK⟩ := hs
  obtain ⟨n0, h0⟩ := ht (w - K)
  refine ⟨n0, fun n hn => ?_⟩
  have h := (hK n).mul (h0 n hn)
  have e : (0 : C) - s n * t n = s n * (0 - t n) := by ring
  rw [e]
  exact h.mono (by linarith)

variable {σ : Type}

def BddS (V : VF C) (f : ℕ → MvPowerSeries σ C) : Prop := ∀ μ, Bdd V (fun n => coeff μ (f n))

theorem BddS.const (g : MvPowerSeries σ C) : BddS V (fun _ => g) := fun _ => bdd_const _

theorem BddS.of_int {f : ℕ → MvPowerSeries σ C} (h : ∀ n, IntS V (f n)) : BddS V f :=
  fun μ => ⟨0, fun n => h n μ⟩

theorem BddS.mul {f g : ℕ → MvPowerSeries σ C} (hf : BddS V f) (hg : BddS V g) :
    BddS V (fun n => f n * g n) := fun μ => by
  classical
  simp only [coeff_mul]
  exact Bdd.sum _ fun p _ => (hf p.1).mul (hg p.2)

theorem BddS.pow {f : ℕ → MvPowerSeries σ C} (hf : BddS V f) (k : ℕ) : BddS V (fun n => f n ^ k) := by
  induction k with
  | zero => simpa using BddS.const (V := V) (1 : MvPowerSeries σ C)
  | succ k ih => simpa only [pow_succ] using ih.mul hf

theorem BddS.prod {ι : Type} (S : Finset ι) {f : ι → ℕ → MvPowerSeries σ C} (h : ∀ i ∈ S, BddS V (f i)) :
    BddS V (fun n => ∏ i ∈ S, f i n) := by
  first | exact UpperTheory.Reformulated.B.BoundedSums.prod .. | (apply UpperTheory.Reformulated.B.BoundedSums.prod <;> assumption) | (intros; apply UpperTheory.Reformulated.B.BoundedSums.prod <;> assumption) | (apply @UpperTheory.Reformulated.B.BoundedSums.prod <;> assumption) | (intros; apply @UpperTheory.Reformulated.B.BoundedSums.prod <;> assumption) | (apply @UpperTheory.Reformulated.B.BoundedSums.prod <;> first | assumption | infer_instance) | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V σ ι S f h | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V σ ι S f | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V σ ι S | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V σ ι | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V σ | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› V | exact @UpperTheory.Reformulated.B.BoundedSums.prod C ‹_› | exact @UpperTheory.Reformulated.B.BoundedSums.prod C

theorem BddS.fprod {ι : Type} (d : ι →₀ ℕ) {a : ℕ → ι → MvPowerSeries σ C} (ha : ∀ i, BddS V (fun n => a n i)) :
    BddS V (fun n => d.prod fun i e => a n i ^ e) := by
  unfold Finsupp.prod
  exact BddS.prod _ fun i _ => (ha i).pow _

theorem BddS.subst [Finite σ] {τ : Type} {a : ℕ → σ → MvPowerSeries τ C} {f : ℕ → MvPowerSeries σ C}
    (ha0 : ∀ n s, constantCoeff (a n s) = 0) (ha : ∀ s, BddS V (fun n => a n s)) (hf : BddS V f) :
    BddS V (fun n => MvPowerSeries.subst (a n) (f n)) := fun μ => by
  have e : (fun n => coeff μ (MvPowerSeries.subst (a n) (f n))) = fun n =>
      ∑ d ∈ (Finsupp.finite_of_degree_le (σ := σ) (Finsupp.degree μ)).toFinset,
        coeff d (f n) * coeff μ (d.prod fun s e => a n s ^ e) :=
    funext fun n => coeff_subst_eq_sum (ha0 n) _ _
  rw [e]
  exact Bdd.sum _ fun d _ => (hf d).mul (BddS.fprod d ha μ)

theorem TendsS.mul_bdd {f g : ℕ → MvPowerSeries σ C} (hf : BddS V f) (hg : TendsS V g 0) :
    TendsS V (fun n => f n * g n) 0 := fun μ => by
  classical
  show Tends V (fun n => coeff μ (f n * g n)) (coeff μ 0)
  simp only [coeff_mul, map_zero]
  have h := Tends.sum (V := V) (Finset.HasAntidiagonal.antidiagonal μ)
    (s := fun p n => coeff p.1 (f n) * coeff p.2 (g n)) (x := fun _ => 0)
    fun p _ => tends_mul_bdd (hf p.1) (by simpa using hg p.2)
  simpa using h

def Close (V : VF C) (f g : ℕ → MvPowerSeries σ C) : Prop := TendsS V (fun n => f n - g n) 0

theorem Close.refl (f : ℕ → MvPowerSeries σ C) : Close V f f := by
  unfold Close
  simpa using TendsS.const (V := V) (0 : MvPowerSeries σ C)

theorem Close.mul {a a' b b' : ℕ → MvPowerSeries σ C} (ha : BddS V a) (hb' : BddS V b') (h1 : Close V a b)
    (h2 : Close V a' b') : Close V (fun n => a n * a' n) (fun n => b n * b' n) := by
  have e : (fun n => a n * a' n - b n * b' n) = fun n => a n * (a' n - b' n) + b' n * (a n - b n) :=
    funext fun n => by ring
  unfold Close
  rw [e]
  simpa using (TendsS.mul_bdd ha h2).add (TendsS.mul_bdd hb' h1)

theorem Close.pow {a b : ℕ → MvPowerSeries σ C} (ha : BddS V a) (hb : BddS V b) (h : Close V a b) (k : ℕ) :
    Close V (fun n => a n ^ k) (fun n => b n ^ k) := by
  induction k with
  | zero => simpa using Close.refl (V := V) (fun _ => (1 : MvPowerSeries σ C))
  | succ k ih => simpa only [pow_succ] using Close.mul (ha.pow k) hb ih h

theorem Close.prod {ι : Type} (S : Finset ι) {a b : ι → ℕ → MvPowerSeries σ C} (ha : ∀ i ∈ S, BddS V (a i))
    (hb : ∀ i ∈ S, BddS V (b i)) (h : ∀ i ∈ S, Close V (a i) (b i)) :
    Close V (fun n => ∏ i ∈ S, a i n) (fun n => ∏ i ∈ S, b i n) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using Close.refl (V := V) (fun _ => (1 : MvPowerSeries σ C))
  | insert x S hx ih =>
    simp only [Finset.prod_insert hx]
    exact Close.mul (ha x (Finset.mem_insert_self x S)) (BddS.prod S fun i hi => hb i (Finset.mem_insert_of_mem hi))
      (h x (Finset.mem_insert_self x S))
      (ih (fun i hi => ha i (Finset.mem_insert_of_mem hi)) (fun i hi => hb i (Finset.mem_insert_of_mem hi))
        fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Close.fprod {ι : Type} (d : ι →₀ ℕ) {a b : ℕ → ι → MvPowerSeries σ C} (ha : ∀ i, BddS V (fun n => a n i))
    (hb : ∀ i, BddS V (fun n => b n i)) (h : ∀ i, Close V (fun n => a n i) (fun n => b n i)) :
    Close V (fun n => d.prod fun i e => a n i ^ e) (fun n => d.prod fun i e => b n i ^ e) := by
  unfold Finsupp.prod
  exact Close.prod _ (fun i _ => (ha i).pow _) (fun i _ => (hb i).pow _) fun i _ => Close.pow (ha i) (hb i) (h i) _

theorem Close.subst [Finite σ] {τ : Type} {a b : ℕ → σ → MvPowerSeries τ C}
    (ha0 : ∀ n s, constantCoeff (a n s) = 0) (hb0 : ∀ n s, constantCoeff (b n s) = 0)
    (ha : ∀ s, BddS V (fun n => a n s)) (hb : ∀ s, BddS V (fun n => b n s))
    (h : ∀ s, Close V (fun n => a n s) (fun n => b n s)) (f : MvPowerSeries σ C) :
    Close V (fun n => MvPowerSeries.subst (a n) f) (fun n => MvPowerSeries.subst (b n) f) := fun μ => by
  show Tends V (fun n => coeff μ (MvPowerSeries.subst (a n) f - MvPowerSeries.subst (b n) f)) (coeff μ 0)
  have e : (fun n => coeff μ (MvPowerSeries.subst (a n) f - MvPowerSeries.subst (b n) f)) = fun n =>
      ∑ d ∈ (Finsupp.finite_of_degree_le (σ := σ) (Finsupp.degree μ)).toFinset,
        coeff d f * coeff μ ((d.prod fun s e => a n s ^ e) - (d.prod fun s e => b n s ^ e)) := funext fun n => by
    rw [map_sub, coeff_subst_eq_sum (ha0 n), coeff_subst_eq_sum (hb0 n), ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun d _ => by rw [map_sub, mul_sub]
  rw [e, map_zero]
  have h2 := Tends.sum (V := V) (Finsupp.finite_of_degree_le (σ := σ) (Finsupp.degree μ)).toFinset
    (s := fun d n => coeff d f * coeff μ ((d.prod fun s e => a n s ^ e) - (d.prod fun s e => b n s ^ e)))
    (x := fun _ => 0) fun d _ => by
      have h3 := (tends_const (V := V) (coeff d f)).mul (Close.fprod d ha hb h μ)
      simpa using h3
  simpa using h2

end Bd

end RowTiePLSmall

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePLSmall

open PartialDerivEval RowTiePE0 RowTiePProj

section Main

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem lg_const (Y : FBChart C V O dd) (i : Fin dd) : constantCoeff (Y.lg i) = 0 := by
  have h := Y.lg_lin i 0 (by simp)
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h]
  simp [MvPowerSeries.coeff_X]
  exact (Finsupp.single_ne_zero.2 one_ne_zero).symm

theorem germEval_oneStandardPoint_self (f : PS C 1 dd) : ev (n := 1) ![pt C dd 0] f = f := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev
  have : (fun p : Fin 1 × Fin dd => (![pt C dd 0] : Fin 1 → Pt C 1 dd) p.1 p.2) = X := by
    funext p
    obtain ⟨k, j⟩ := p
    fin_cases k
    rfl
  rw [this, subst_self]
  rfl

theorem formalGroupLaw_ev_x_zero (Y : FBChart C V O dd) {n : ℕ} (A : Pt C n dd) (hA : ∀ j, constantCoeff (A j) = 0) (i : Fin dd) :
    ev (![A, 0] : Fin 2 → Pt C n dd) (Y.B.G.F i) = A i := by
  have hZ : Z0 (![A, 0] : Fin 2 → Pt C n dd) := z0_p0 A hA
  conv_lhs => rw [← Y.B.G.comm i]
  rw [ev_ev (z0_pp 1 0) hZ]
  have e1 : (fun k j => ev (![A, 0] : Fin 2 → Pt C n dd) ((![pt C dd 1, pt C dd 0] : Fin 2 → Pt C 2 dd) k j)) =
      ![0, A] := by
    funext k j; fin_cases k
    · exact ev_X hZ 1 j
    · exact ev_X hZ 0 j
  rw [e1]
  have hB : Z0 (![A] : Fin 1 → Pt C n dd) := z0_1 _ hA
  have hU : Z0 (![0, pt C dd 0] : Fin 2 → Pt C 1 dd) := by
    intro k j; fin_cases k
    · simp
    · exact z0_pt 0 j
  have e2 : (![0, A] : Fin 2 → Pt C n dd) =
      fun k j => ev (![A] : Fin 1 → Pt C n dd) ((![0, pt C dd 0] : Fin 2 → Pt C 1 dd) k j) := by
    funext k j; fin_cases k
    · exact (ev_zero hB).symm
    · exact (ev_X hB 0 j).symm
  rw [e2, ← ev_ev hU hB, Y.B.G.unit i, ev_X hB]
  rfl

theorem lg_addOf (Y : FBChart C V O dd) {n : ℕ} (P Q : Pt C n dd) (hP : ∀ j, constantCoeff (P j) = 0)
    (hQ : ∀ j, constantCoeff (Q j) = 0) (i : Fin dd) :
    ev ![addOf Y.B.G.F P Q] (Y.lg i) = ev ![P] (Y.lg i) + ev ![Q] (Y.lg i) := by
  have hPQ : Z0 (![P, Q] : Fin 2 → Pt C n dd) := constant_zero_two_points P Q hP hQ
  have h := congrArg (ev (![P, Q] : Fin 2 → Pt C n dd)) (Y.lg_add i)
  rw [ev_add hPQ] at h
  have hA : Z0 (![addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)] : Fin 1 → Pt C 2 dd) :=
    z0_1 _ (fun j => const_addOf Y 0 1 j)
  rw [ev_ev hA hPQ, ev_ev (z0_1 _ (z0_pt 0)) hPQ, ev_ev (z0_1 _ (z0_pt 1)) hPQ] at h
  have e1 : (fun k j => ev (![P, Q] : Fin 2 → Pt C n dd)
      ((![addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1)] : Fin 1 → Pt C 2 dd) k j)) =
      ![addOf Y.B.G.F P Q] := by
    funext k j
    rw [Fin.fin_one_eq_zero k]
    show ev (![P, Q] : Fin 2 → Pt C n dd) (ev ![pt C (n := 2) dd 0, pt C (n := 2) dd 1] (Y.B.G.F j)) =
      ev ![P, Q] (Y.B.G.F j)
    rw [ev_ev (z0_pp 0 1) hPQ]
    congr 1
    funext k' j'
    fin_cases k'
    · exact ev_X hPQ 0 j'
    · exact ev_X hPQ 1 j'
  have e2 : (fun k j => ev (![P, Q] : Fin 2 → Pt C n dd) ((![pt C (n := 2) dd 0] : Fin 1 → Pt C 2 dd) k j)) = ![P] := by
    funext k j
    rw [Fin.fin_one_eq_zero k]
    exact ev_X hPQ 0 j
  have e3 : (fun k j => ev (![P, Q] : Fin 2 → Pt C n dd) ((![pt C (n := 2) dd 1] : Fin 1 → Pt C 2 dd) k j)) = ![Q] := by
    funext k j
    rw [Fin.fin_one_eq_zero k]
    exact ev_X hPQ 1 j
  rw [e1, e2, e3] at h
  exact h

theorem lg_act_nat (Y : FBChart C V O dd) (k : ℕ) (i : Fin dd) :
    ev ![Y.B.A.act (k : O)] (Y.lg i) = MvPowerSeries.C (k : C) * Y.lg i := by
  have act0 := Y.B.A.const
  induction k with
  | zero =>
    have h0 : Y.B.A.act ((0 : ℕ) : O) = addOf Y.B.G.F (Y.B.A.act ((0 : ℕ) : O)) (Y.B.A.act ((0 : ℕ) : O)) := by
      have := Y.B.A.add_act 0 0
      rw [add_zero] at this
      rw [Nat.cast_zero]; exact this
    have h := lg_addOf Y (Y.B.A.act ((0 : ℕ) : O)) (Y.B.A.act ((0 : ℕ) : O)) (act0 _) (act0 _) i
    rw [← h0] at h
    simp only [Nat.cast_zero, map_zero, zero_mul] at h ⊢
    linear_combination -h
  | succ k ih =>
    have h1 : Y.B.A.act ((k + 1 : ℕ) : O) = addOf Y.B.G.F (Y.B.A.act (k : O)) (pt C dd 0) := by
      rw [Nat.cast_succ, Y.B.A.add_act, Y.B.A.one_act]
    rw [h1, lg_addOf Y _ _ (act0 _) (z0_pt 0) i, ih, germEval_oneStandardPoint_self, Nat.cast_succ, map_add (f := _), map_one]
    ring

theorem ex_lg_comp (Y : FBChart C V O dd) {n : ℕ} (φ : Pt C n dd) (hφ : ∀ j, constantCoeff (φ j) = 0) (i : Fin dd) :
    ev ![fun j => ev ![φ] (Y.lg j)] (Y.ex i) = φ i := by
  have hφ1 : Z0 (![φ] : Fin 1 → Pt C n dd) := z0_1 φ hφ
  have hlg : Z0 (![Y.lg] : Fin 1 → Pt C 1 dd) := z0_1 _ (lg_const Y)
  have e1 : (![fun j => ev ![φ] (Y.lg j)] : Fin 1 → Pt C n dd) =
      fun k j => ev (![φ] : Fin 1 → Pt C n dd) ((![Y.lg] : Fin 1 → Pt C 1 dd) k j) := by
    funext k j; rw [Fin.fin_one_eq_zero k]; rfl
  rw [e1, ← ev_ev hlg hφ1]
  have e2 : ev (![Y.lg] : Fin 1 → Pt C 1 dd) (Y.ex i) = pt C dd 0 i := congrFun Y.ex_lg i
  rw [e2]
  exact ev_X hφ1 0 i

end Main

end RowTiePLSmall

end Formalism.L2.FormalSeriesBounds
end
end

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePLSmall

open PartialDerivEval RowTiePE0 RowTiePProj

section Main

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem subst_zero_of {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, a s = 0)
    {f : MvPowerSeries σ C} (hf : constantCoeff f = 0) : MvPowerSeries.subst a f = 0 := by
  have h0 : a = 0 := funext ha
  subst h0
  have hs : MvPowerSeries.HasSubst (0 : σ → MvPowerSeries τ C) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  ext e
  rw [MvPowerSeries.coeff_subst hs, map_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : d = 0
  · subst hd
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
  · obtain ⟨s, hsd⟩ : ∃ s, d s ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hd (Finsupp.ext hcon)
    have hp : (d.prod fun s n => (0 : σ → MvPowerSeries τ C) s ^ n) = 0 := by
      apply Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.mpr hsd)
      simp [zero_pow hsd]
    rw [hp, map_zero, smul_zero]

private theorem ev_C_mul' {m n : ℕ} {a : Fin m → Pt C n dd} (ha : Z0 a) (c : C) (f : PS C m dd) :
    ev a (MvPowerSeries.C c * f) = MvPowerSeries.C c * ev a f := by
  rw [← MvPowerSeries.smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul, ev_eq_alg ha, ev_eq_alg ha, map_smul]

theorem act_nat_mul (Y : FBChart C V O dd) (k : ℕ) (w : O) (j : Fin dd) :
    Y.B.A.act ((k : O) * w) j =
      ev ![fun j' => MvPowerSeries.C (k : C) * ev ![Y.B.A.act w] (Y.lg j')] (Y.ex j) := by
  have hk : ∀ i, Y.B.A.act (k : O) i = ev ![fun j' => MvPowerSeries.C (k : C) * Y.lg j'] (Y.ex i) := by
    intro i
    have h := ex_lg_comp Y (Y.B.A.act (k : O)) (Y.B.A.const _) i
    simp only [lg_act_nat] at h
    exact h.symm
  have hw : Z0 ![Y.B.A.act w] := by
    intro k' i'
    fin_cases k'
    simp [Y.B.A.const]
  have hb : Z0 ![fun j' => MvPowerSeries.C (k : C) * Y.lg j'] := by
    intro k' i'
    fin_cases k'
    simp [lg_const]
  rw [Y.B.A.mul_act]
  show ev ![Y.B.A.act w] (Y.B.A.act (k : O) j) = _
  rw [hk, ev_ev hb hw]
  congr 1
  funext k' i'
  fin_cases k'
  show ev ![Y.B.A.act w] (MvPowerSeries.C (k : C) * Y.lg i') = MvPowerSeries.C (k : C) * ev ![Y.B.A.act w] (Y.lg i')
  exact ev_C_mul' hw _ _

theorem tends_lpow : Tends V (fun n => ((V.l ^ (n + 1) : ℕ) : C)) 0 := by
  apply tends_of_nat
  intro N
  refine ⟨N, fun n hn => ?_⟩
  show ((N : ℝ) : WithTop ℝ) ≤ V.v (0 - ((V.l ^ (n + 1) : ℕ) : C))
  rw [zero_sub, AddValuation.map_neg, Nat.cast_pow, AddValuation.map_pow, V.v_l, nsmul_one]
  have h2 : ((N : ℝ) : WithTop ℝ) ≤ (((n + 1 : ℕ) : ℝ) : WithTop ℝ) := by
    rw [WithTop.coe_le_coe]
    exact_mod_cast (by omega : N ≤ n + 1)
  simpa using h2

theorem lSmall_holds : LSmallSt := by
  intro C _ _ V O _ _ dd Y x x' hx N i μ
  have hx' : ∀ n, ∃ c, x n - x' n = (V.l : O) ^ (n + 1) * c := fun n => hx n
  choose y hy using hx'
  have hsmall : ∀ (z : ℕ → O) (j : Fin dd),
      TendsS V (fun n => Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * z n) j) 0 := by
    intro z j
    have hw : ∀ n, Z0 ![Y.B.A.act (z n)] := by
      intro n k' i'
      fin_cases k'
      simp [Y.B.A.const]
    have hg : ∀ s2 : Fin dd, BddS V (fun n => ev ![Y.B.A.act (z n)] (Y.lg s2)) := by
      intro s2
      exact BddS.subst (a := fun n (p : Fin 1 × Fin dd) => (![Y.B.A.act (z n)] p.1) p.2)
        (f := fun _ => Y.lg s2)
        (by
          rintro n ⟨t1, t2⟩
          fin_cases t1
          simp [Y.B.A.const])
        (by
          rintro ⟨t1, t2⟩
          fin_cases t1
          exact BddS.of_int (fun n => Y.intAct _ _))
        (BddS.const _)
    have hcl := Close.subst (V := V)
      (a := fun n (p : Fin 1 × Fin dd) =>
        (![fun j' => MvPowerSeries.C (((V.l ^ (n + 1) : ℕ) : C)) * ev ![Y.B.A.act (z n)] (Y.lg j')] p.1) p.2)
      (b := fun _ _ => 0)
      (by
        rintro n ⟨s1, s2⟩
        fin_cases s1
        simp [const_ev (hw n) (lg_const Y s2)])
      (by intros; simp)
      (by
        rintro ⟨s1, s2⟩
        fin_cases s1
        show BddS V (fun n => MvPowerSeries.C (((V.l ^ (n + 1) : ℕ) : C)) * ev ![Y.B.A.act (z n)] (Y.lg s2))
        apply BddS.mul _ (hg s2)
        intro ν
        refine ⟨0, fun n => ?_⟩
        show V.Ge 0 (MvPowerSeries.coeff ν (MvPowerSeries.C (((V.l ^ (n + 1) : ℕ) : C))))
        rw [MvPowerSeries.coeff_C]
        split_ifs
        · exact ge_natCast _
        · show ((0 : ℝ) : WithTop ℝ) ≤ V.v 0
          simp)
      (fun _ => BddS.const 0)
      (by
        rintro ⟨s1, s2⟩
        fin_cases s1
        show TendsS V (fun n => MvPowerSeries.C (((V.l ^ (n + 1) : ℕ) : C)) * ev ![Y.B.A.act (z n)] (Y.lg s2) - 0) 0
        simp only [sub_zero]
        simp only [mul_comm (MvPowerSeries.C _)]
        apply TendsS.mul_bdd (hg s2)
        intro ν
        simp only [MvPowerSeries.coeff_C, map_zero]
        split_ifs
        · exact tends_lpow
        · exact tends_const 0)
      (Y.ex j)
    have h0 : MvPowerSeries.subst (fun _ : Fin 1 × Fin dd => (0 : MvPowerSeries (Fin 1 × Fin dd) C)) (Y.ex j) = 0 :=
      subst_zero_of (fun _ => rfl) (Y.ex_const j)
    intro ν
    have h1 := hcl ν
    simp only [h0, sub_zero] at h1
    simp only [act_nat_mul]
    exact h1
  have heq : ∀ n, MvPowerSeries.subst (fun p : Fin 2 × Fin dd =>
      (![Y.B.A.act (x' n), Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * y n)] p.1) p.2) (Y.B.G.F i) =
        Y.B.A.act (x n) i := by
    intro n
    have hxn : x n = x' n + ((V.l ^ (n + 1) : ℕ) : O) * y n := by
      rw [Nat.cast_pow, ← hy n]
      ring
    rw [hxn, Y.B.A.add_act]
    rfl
  have heq' : ∀ n, MvPowerSeries.subst (fun p : Fin 2 × Fin dd =>
      (![Y.B.A.act (x' n), Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * (fun _ => (0 : O)) n)] p.1) p.2) (Y.B.G.F i) =
        Y.B.A.act (x' n) i := by
    intro n
    have hxn : Y.B.A.act (x' n) i =
        Y.B.A.act (x' n + ((V.l ^ (n + 1) : ℕ) : O) * (fun _ => (0 : O)) n) i := by
      simp
    rw [hxn, Y.B.A.add_act]
    rfl
  have hcl := Close.subst (V := V)
    (a := fun n (p : Fin 2 × Fin dd) =>
      (![Y.B.A.act (x' n), Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * y n)] p.1) p.2)
    (b := fun n (p : Fin 2 × Fin dd) =>
      (![Y.B.A.act (x' n), Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * (fun _ => (0 : O)) n)] p.1) p.2)
    (by
      rintro n ⟨s1, s2⟩
      fin_cases s1 <;> simp [Y.B.A.const])
    (by
      rintro n ⟨s1, s2⟩
      fin_cases s1 <;> simp [Y.B.A.const])
    (by
      rintro ⟨s1, s2⟩
      fin_cases s1 <;> exact BddS.of_int (fun n => Y.intAct _ _))
    (by
      rintro ⟨s1, s2⟩
      fin_cases s1 <;> exact BddS.of_int (fun n => Y.intAct _ _))
    (by
      rintro ⟨s1, s2⟩
      fin_cases s1
      · exact Close.refl (fun n => Y.B.A.act (x' n) s2)
      · intro ν
        have h1 := hsmall y s2 ν
        have h2 := hsmall (fun _ => 0) s2 ν
        have h3 := h1.sub h2
        simp only [map_zero, sub_zero] at h3
        rw [map_zero]
        simp only [map_sub]
        exact h3)
    (Y.B.G.F i)
  obtain ⟨n0, hn0⟩ := hcl μ (N : ℝ)
  refine ⟨n0, fun n hn => ?_⟩
  have h4 := hn0 n hn
  simp only [heq, heq', map_zero, zero_sub, map_sub] at h4
  show ((N : ℝ) : WithTop ℝ) ≤ V.v _
  have h5 : ((N : ℝ) : WithTop ℝ) ≤ V.v (-(MvPowerSeries.coeff μ (Y.B.A.act (x n) i) -
      MvPowerSeries.coeff μ (Y.B.A.act (x' n) i))) := h4
  rwa [AddValuation.map_neg] at h5

end Main

end RowTiePLSmall

end Formalism.L2.FormalSeriesBounds
