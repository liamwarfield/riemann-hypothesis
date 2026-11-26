module

public import ReciprocityTheory.DualLattices.ColengthSqMulLeProd
public import ReciprocityTheory.DualLattices.LengthDegreeOfFrobenius
public import ReciprocityTheory.DualLattices.FrobeniusOfGroupDivisorsRank

@[expose] public section

section -- merged from ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

theorem lat_conseq (C : Type) [Field C] [IsAlgClosed C] (v : Valuation C NNReal) (R : Type)
    [CommRing R] [Algebra R C] (hv : v.Integers R) (hnt : ∃ c : C, 0 < v c ∧ v c < 1)
    (n : ℕ) (a : Fin n → C) (hinj : Function.Injective a) (hint : ∀ τ, v (a τ) ≤ 1)
    (s h : ℕ) (A : Fin n → Matrix (Fin s) (Fin h) C) (F : Lat v (Fin n × Fin h))
    (M M' : Lat v (Fin n × Fin s)) (Mτ M'τ : Fin n → Lat v (Fin s)) (hF : F.B = freeMat a h)
    (hA : ∀ τ, Function.Surjective (A τ).mulVec)
    (hM' : M'.pts = (fun w : Fin n × Fin h → C => fun y : Fin n × Fin s =>
        ∑ l, A y.1 y.2 l * w (y.1, l)) '' F.pts)
    (hMst : IsLaStable a M) (hMτ : ∀ τ, (Mτ τ).pts = projPts M.pts τ)
    (hM'τ : ∀ τ, (M'τ τ).pts = projPts M'.pts τ) (c : NNReal) (hc : c ≤ colen M' M) :
    c ^ 2 * v (discr a) ^ h ≤ (∏ τ, colen (M'τ τ) (Mτ τ)) ^ 2 * v (discr a) ^ s :=
  le_trans (by gcongr)
    (colength_sq_mul_le_prod C v R hv hnt n a hinj hint s h A F M M' Mτ M'τ hF hA hM' hMst hMτ hM'τ)

theorem lengthDegree_abelianVariety : PermutedCokernelLowerBoundStatement := permutedCokernelLowerBound_of u6 lenEx killedGen idemGen

theorem up_full (hU7 : UnramifiedCokernelLengthStatement) (p : ℕ) [Fact p.Prime] (g : ℕ) (C : Type) [Field C]
    [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    [Algebra ℤ_[p] R] (O : Type) [CommRing O] [Algebra ℤ_[p] O] (σ : O ≃ₐ[ℤ_[p]] O) (cp : R)
    (hp2 : p ≠ 2) (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp)
    (U : UnramData p g v R O σ cp H) (i : Fin U.m) (N : Type) [AddCommGroup N] [Module R N]
    (E : cokE H.Ht U.εT U.εL i (U.cj i) ≃ₗ[R] N) (V1 : NNReal) (hN : HasLen v R N V1) :
    (v (algebraMap R C (p : R)) : ℝ) ^ (((U.r i : ℝ) + U.r (U.cj i)) / (p - 1) - frobSum U i) ≤ V1 := by
  obtain ⟨k, c0, ⟨F0⟩, hc0⟩ := hN
  have h10 := unramifiedCokernelLowerBound_of hU7 lenEx killedGen idemGen
  unfold UnramifiedCokernelLowerBoundStatement at h10
  exact h10 p g C v R O σ cp hp2 hS H U i V1 ⟨k, c0, ⟨E.trans F0⟩, hc0⟩

private lemma prime_rpow_neg_succ_eq_inv_mul_inv_pow {p : ℕ} [Fact p.Prime] (n : ℕ) :
    (p : ℝ) ^ (-((n : ℝ) + 1)) = (p : ℝ)⁻¹ * ((p : ℝ)⁻¹) ^ n := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hn : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [Real.rpow_neg hp0.le, hn, Real.rpow_natCast, ← inv_pow, pow_succ]
  ring

private lemma prime_inv_lt_one {p : ℕ} [Fact p.Prime] : (p : ℝ)⁻¹ < 1 := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have h1 := one_div_lt_one_div_of_lt one_pos hp
  simpa using h1

private lemma summable_prime_rpow_neg_succ {p : ℕ} [Fact p.Prime] :
    Summable fun n : ℕ => (p : ℝ) ^ (-((n : ℝ) + 1)) := by
  have e : (fun n : ℕ => (p : ℝ) ^ (-((n : ℝ) + 1))) =
      fun n : ℕ => (p : ℝ)⁻¹ * ((p : ℝ)⁻¹) ^ n := funext fun n => prime_rpow_neg_succ_eq_inv_mul_inv_pow n
  rw [e]
  exact (summable_geometric_of_lt_one (inv_nonneg.mpr (Nat.cast_nonneg p)) prime_inv_lt_one).mul_left _

lemma tsum_geom_p {p : ℕ} [Fact p.Prime] :
    ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) = 1 / ((p : ℝ) - 1) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hp.ne'
  rw [tsum_congr (fun n : ℕ => prime_rpow_neg_succ_eq_inv_mul_inv_pow (p := p) n), tsum_mul_left,
    tsum_geometric_of_lt_one (inv_nonneg.mpr (Nat.cast_nonneg p)) prime_inv_lt_one]
  field_simp

lemma summable_geom_p {p : ℕ} [Fact p.Prime] (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (B : ℝ)
    (hfB : ∀ n, f n ≤ B) : Summable fun n : ℕ => (p : ℝ) ^ (-((n : ℝ) + 1)) * f n := by
  exact Summable.of_nonneg_of_le
    (fun n => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _) (hf0 n))
    (fun n => mul_le_mul_of_nonneg_left (hfB n) (Real.rpow_nonneg (Nat.cast_nonneg p) _))
    ((summable_prime_rpow_neg_succ (p := p)).mul_right B)

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.UpBrChar
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

def omTr {R : Type} [CommRing R] {g N : ℕ} (M : Matrix (Fin g) (Fin N) R) (s : ℕ) (hs : s ≤ g) :
    Submodule R (Fin s → R) :=
  Submodule.span R (Set.range fun b : Fin N => fun a : Fin s => M (Fin.castLE hs a) b)

def CharStatement : Prop :=
  ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → ∀ (g N : ℕ) (M : Matrix (Fin g) (Fin N) R) (c : R), c ≠ 0 →
    (∀ s (hs : s ≤ g), ∀ w : Fin s → R, c • w ∈ omTr M s hs) →
    ∃ ι : Fin g → Fin N, Function.Injective ι ∧ ∀ s (hs : s ≤ g),
      Submodule.span R (Set.range fun b : Fin s => fun a : Fin s => M (Fin.castLE hs a) (ι (Fin.castLE hs b)))
        = omTr M s hs

section Char

variable {R : Type} [CommRing R] [IsDomain R]

lemma det_ne_of_span {s : ℕ} (A : Matrix (Fin s) (Fin s) R) (c : R) (hc : c ≠ 0)
    (h : ∀ w : Fin s → R, c • w ∈ Submodule.span R (Set.range fun i => fun a => A a i)) :
    A.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hvA⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hdet
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  have key : ∀ u ∈ Submodule.span R (Set.range fun i => fun a => A a i), v ⬝ᵥ u = 0 := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact congrFun hvA i
    | zero => simp
    | add x y _ _ hx hy => rw [dotProduct_add, hx, hy, add_zero]
    | smul a x _ hx => rw [dotProduct_smul, hx, smul_zero]
  have h1 := key _ (h (Pi.single j 1))
  simp [hc] at h1
  exact hj h1

lemma not_span_lt {s : ℕ} (B : Matrix (Fin (s + 1)) (Fin s) R) (c : R) (hc : c ≠ 0)
    (h : ∀ w : Fin (s + 1) → R, c • w ∈ Submodule.span R (Set.range fun i => fun a => B a i)) :
    False := by
  classical
  let A : Matrix (Fin (s + 1)) (Fin (s + 1)) R :=
    Matrix.of fun a i => Fin.snoc (α := fun _ => R) (B a) (0 : R) i
  have hA : A.det = 0 := by
    apply Matrix.det_eq_zero_of_column_eq_zero (Fin.last s)
    intro a
    simp [A]
  refine det_ne_of_span A c hc ?_ hA
  intro w
  refine Submodule.span_mono ?_ (h w)
  rintro _ ⟨i, rfl⟩
  refine ⟨Fin.castSucc i, ?_⟩
  funext a
  simp [A]

lemma mulVec_inj_of_det {s : ℕ} (A : Matrix (Fin s) (Fin s) R) (hA : A.det ≠ 0) {x y : Fin s → R}
    (h : A *ᵥ x = A *ᵥ y) : x = y := by
  by_contra hne
  apply hA
  refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨x - y, sub_ne_zero.mpr hne, ?_⟩
  rw [Matrix.mulVec_sub, h, sub_self]

variable {C : Type} [Field C] {v : Valuation C NNReal} [Algebra R C]

lemma char_step (hv : v.Integers R) {g N : ℕ} (M : Matrix (Fin g) (Fin N) R) (c : R) (hc : c ≠ 0)
    (hspan : ∀ s (hs : s ≤ g), ∀ w : Fin s → R, c • w ∈ omTr M s hs) (s : ℕ) (hs1 : s + 1 ≤ g)
    (ι : Fin s → Fin N)
    (hι : Submodule.span R (Set.range fun i : Fin s => fun a : Fin s =>
      M (Fin.castLE (Nat.le_of_succ_le hs1) a) (ι i)) = omTr M s (Nat.le_of_succ_le hs1)) :
    ∃ b, b ∉ Set.range ι ∧ Submodule.span R (Set.range fun i : Fin (s + 1) => fun a : Fin (s + 1) =>
      M (Fin.castLE hs1 a) (Fin.snoc (α := fun _ => Fin N) ι b i)) = omTr M (s + 1) hs1 := by
  classical
  have hcast : ∀ a : Fin s, (Fin.castLE hs1 (Fin.castSucc a) : Fin g) =
      Fin.castLE (Nat.le_of_succ_le hs1) a := fun a => Fin.ext rfl
  set T : Fin N → Fin (s + 1) → R := fun b a => M (Fin.castLE hs1 a) b with hT
  set A : Matrix (Fin s) (Fin s) R :=
    Matrix.of fun a i => M (Fin.castLE (Nat.le_of_succ_le hs1) a) (ι i) with hA
  have hAdet : A.det ≠ 0 := by
    refine det_ne_of_span A c hc fun w => ?_
    have h1 := hspan s (Nat.le_of_succ_le hs1) w
    rw [← hι] at h1
    exact h1
  have hlam : ∀ b, ∃ l : Fin s → R, ∀ a : Fin s, M (Fin.castLE (Nat.le_of_succ_le hs1) a) b =
      ∑ i, l i * M (Fin.castLE (Nat.le_of_succ_le hs1) a) (ι i) := by
    intro b
    have hmem : (fun a : Fin s => M (Fin.castLE (Nat.le_of_succ_le hs1) a) b) ∈
        omTr M s (Nat.le_of_succ_le hs1) := Submodule.subset_span ⟨b, rfl⟩
    rw [← hι, Submodule.mem_span_range_iff_exists_fun] at hmem
    obtain ⟨l, hl⟩ := hmem
    refine ⟨l, fun a => ?_⟩
    have h2 := congrFun hl a
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h2
    exact h2.symm
  choose l hl using hlam
  have hlι : ∀ j, l (ι j) = Pi.single j 1 := by
    intro j
    apply mulVec_inj_of_det A hAdet
    funext a
    have h1 := hl (ι j) a
    simp only [Matrix.mulVec, dotProduct, hA, Matrix.of_apply, Pi.single_apply, mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [h1]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  set μ : Fin N → R := fun b => T b (Fin.last s) - ∑ i, l b i * T (ι i) (Fin.last s) with hμ
  have hdecomp : ∀ b, T b = ∑ i, l b i • T (ι i) + μ b • (Pi.single (Fin.last s) 1 : Fin (s + 1) → R) := by
    intro b
    funext a
    induction a using Fin.lastCases with
    | last => simp [hμ, Finset.sum_apply]
    | cast a =>
      simpa [hT, Finset.sum_apply, Pi.single_apply, hcast, Fin.castSucc_ne_last] using hl b a
  have hex : ∃ b, μ b ≠ 0 := by
    by_contra hall
    push_neg at hall
    have hle : omTr M (s + 1) hs1 ≤ Submodule.span R (Set.range fun i => T (ι i)) := by
      rw [omTr, Submodule.span_le]
      rintro _ ⟨b, rfl⟩
      show T b ∈ _
      rw [hdecomp b, hall b, zero_smul, add_zero]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    exact not_span_lt (Matrix.of fun a i => T (ι i) a) c hc fun w => hle (hspan (s + 1) hs1 w)
  obtain ⟨b0, hb0⟩ := hex
  obtain ⟨bs, -, hbs⟩ := Finset.exists_max_image Finset.univ
    (fun b => v (algebraMap R C (μ b))) ⟨b0, Finset.mem_univ _⟩
  have hμs : μ bs ≠ 0 := by
    intro h
    have h1 := hbs b0 (Finset.mem_univ _)
    rw [h, map_zero, map_zero] at h1
    have h2 : v (algebraMap R C (μ b0)) = 0 := le_antisymm h1 zero_le
    rw [Valuation.zero_iff] at h2
    exact hb0 (hv.hom_inj (by rw [h2, map_zero]))
  have hbsι : bs ∉ Set.range ι := by
    rintro ⟨j, hj⟩
    apply hμs
    rw [← hj]
    simp [hμ, hlι j, Pi.single_apply]
  refine ⟨bs, hbsι, le_antisymm ?_ ?_⟩
  · rw [omTr, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨Fin.snoc (α := fun _ => Fin N) ι bs i, rfl⟩
  · set S := Submodule.span R (Set.range fun i : Fin (s + 1) => fun a : Fin (s + 1) =>
      M (Fin.castLE hs1 a) (Fin.snoc (α := fun _ => Fin N) ι bs i)) with hS
    have hTι : ∀ i, T (ι i) ∈ S := fun i => by
      have h1 : (fun a : Fin (s + 1) => M (Fin.castLE hs1 a)
          (Fin.snoc (α := fun _ => Fin N) ι bs (Fin.castSucc i))) ∈ S :=
        Submodule.subset_span ⟨Fin.castSucc i, rfl⟩
      simpa only [Fin.snoc_castSucc] using h1
    have hTbs : T bs ∈ S := by
      have h1 : (fun a : Fin (s + 1) => M (Fin.castLE hs1 a)
          (Fin.snoc (α := fun _ => Fin N) ι bs (Fin.last s))) ∈ S :=
        Submodule.subset_span ⟨Fin.last s, rfl⟩
      simpa only [Fin.snoc_last] using h1
    have hE : μ bs • (Pi.single (Fin.last s) 1 : Fin (s + 1) → R) ∈ S := by
      have h2 : μ bs • (Pi.single (Fin.last s) 1 : Fin (s + 1) → R) =
          T bs - ∑ i, l bs i • T (ι i) := by
        rw [hdecomp bs]
        abel
      rw [h2]
      exact S.sub_mem hTbs (S.sum_mem fun i _ => S.smul_mem _ (hTι i))
    rw [omTr, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    show T b ∈ S
    obtain ⟨d, hd⟩ := hv.dvd_of_le (hbs b (Finset.mem_univ _))
    rw [hdecomp b, hd, mul_comm, mul_smul]
    exact S.add_mem (S.sum_mem fun i _ => S.smul_mem _ (hTι i)) (S.smul_mem _ hE)

lemma char_ind (hv : v.Integers R) {g N : ℕ} (M : Matrix (Fin g) (Fin N) R) (c : R) (hc : c ≠ 0)
    (hspan : ∀ s (hs : s ≤ g), ∀ w : Fin s → R, c • w ∈ omTr M s hs) :
    ∀ s (hs : s ≤ g), ∃ ι : Fin s → Fin N, Function.Injective ι ∧ ∀ s' (hs' : s' ≤ s),
      Submodule.span R (Set.range fun b : Fin s' => fun a : Fin s' =>
        M (Fin.castLE (hs'.trans hs) a) (ι (Fin.castLE hs' b))) = omTr M s' (hs'.trans hs) := by
  intro s
  induction s with
  | zero =>
    intro _
    refine ⟨fun a => a.elim0, fun a _ _ => a.elim0, fun s' hs' => ?_⟩
    obtain rfl : s' = 0 := Nat.le_zero.mp hs'
    ext w
    have hw : w = 0 := Subsingleton.elim _ _
    subst hw
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
  | succ s ih =>
    intro hs
    obtain ⟨ι, hinj, hι⟩ := ih (Nat.le_of_succ_le hs)
    obtain ⟨b, hb, hb2⟩ := char_step hv M c hc hspan s hs ι (hι s le_rfl)
    refine ⟨Fin.snoc (α := fun _ => Fin N) ι b, ?_, fun s' hs' => ?_⟩
    · intro i j hij
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => rfl
        | cast j =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
          exact (hb ⟨j, hij.symm⟩).elim
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          simp only [Fin.snoc_last, Fin.snoc_castSucc] at hij
          exact (hb ⟨i, hij⟩).elim
        | cast j =>
          simp only [Fin.snoc_castSucc] at hij
          rw [hinj hij]
    · rcases Nat.lt_or_ge s' (s + 1) with hlt | hge
      · have hle : s' ≤ s := Nat.lt_succ_iff.mp hlt
        refine Eq.trans ?_ (hι s' hle)
        congr 2
        funext b' a
        have e : (Fin.castLE hs' b' : Fin (s + 1)) = Fin.castSucc (Fin.castLE hle b') := Fin.ext rfl
        rw [e, Fin.snoc_castSucc]
      · obtain rfl : s' = s + 1 := le_antisymm hs' hge
        exact hb2

theorem charThm : CharStatement := by
  intro C _ v R _ _ hv g N M c hc hspan
  haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  obtain ⟨ι, hinj, h⟩ := char_ind hv M c hc hspan g le_rfl
  exact ⟨ι, hinj, fun s hs => h s hs⟩

theorem char_len (hv : v.Integers R) {g N : ℕ} (M : Matrix (Fin g) (Fin N) R) (ι : Fin g → Fin N)
    (s : ℕ) (hs : s ≤ g)
    (hι : Submodule.span R (Set.range fun b : Fin s => fun a : Fin s =>
      M (Fin.castLE hs a) (ι (Fin.castLE hs b))) = omTr M s hs) :
    HasLen v R ((Fin s → R) ⧸ omTr M s hs)
      (v (algebraMap R C (Matrix.of fun a b : Fin s => M (Fin.castLE hs a) (ι (Fin.castLE hs b))).det)) := by
  have h := hasLen_coker_det' v R hv (Fin s) (Matrix.of fun a b : Fin s => M (Fin.castLE hs a) (ι (Fin.castLE hs b)))
  have hr : LinearMap.range (Matrix.of fun a b : Fin s => M (Fin.castLE hs a)
      (ι (Fin.castLE hs b))).mulVecLin = omTr M s hs := by
    rw [Matrix.range_mulVecLin, ← hι]
    rfl
  rw [hr] at h
  exact h

end Char

end ReciprocityTheory.PGsh.Up
end
end
