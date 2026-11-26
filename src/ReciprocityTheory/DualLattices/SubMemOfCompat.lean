module

public import ReciprocityTheory.DualLattices.TowerZeroSurjective
public import ReciprocityTheory.DualLattices.MatEquivApply

@[expose] public section

section -- merged from ReciprocityTheory.DualLattices.SubMemOfCompat
noncomputable section

open WittVector Ideal

namespace ReciprocityTheory.PGsh

namespace Ainf

variable (p : ℕ) [hp : Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
  {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
  [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O]
  (hv : v.Integers O) (ε : PreTilt O p)
  (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p)

def r'Alg (n : ℕ) : R'n p O ε (n + 1) →ₐ[R0 p O ε] R'n p O ε n :=
  Ideal.Quotient.liftₐ _ (Ideal.Quotient.mkₐ (R0 p O ε) _) (fun a ha => by
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_span_singleton'.2 ⟨b * p, by ring⟩)

def rRing (n : ℕ) : Rn p O (n + 1) →+* Rn p O n :=
  Ideal.Quotient.lift (span {(p : O) ^ (n + 1 + 1)})
    (Ideal.Quotient.mk (span {(p : O) ^ (n + 1)})) (fun a ha => by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton'.2 ⟨b * p, by ring⟩)

def rAlg (n : ℕ) : (LR p O hv ε hε (n + 1) : Type) →ₐ[R0 p O ε] (LR p O hv ε hε n : Type) :=
  { toRingHom := rRing p O n
    commutes' := fun _ => rfl }

lemma r'Alg_surj (n : ℕ) : Function.Surjective (r'Alg p O ε n) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

lemma rAlg_surj (n : ℕ) : Function.Surjective (rAlg p O hv ε hε n) := by
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

lemma sub_mem_of_compat (f : ℕ → O)
    (hf : ∀ n, f (n + 1) - f n ∈ span {(p : O) ^ (n + 1)}) :
    ∀ m k, f (m + k) - f m ∈ span {(p : O) ^ m} := by
  intro m k
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : f (m + k + 1) - f (m + k) ∈ span {(p : O) ^ m} := by
      have h := hf (m + k)
      rw [Ideal.mem_span_singleton'] at h ⊢
      obtain ⟨a, ha⟩ := h
      exact ⟨a * p ^ (k + 1), by rw [← ha, mul_assoc, ← pow_add]; ring_nf⟩
    have : f (m + (k + 1)) - f m = (f (m + k + 1) - f (m + k)) + (f (m + k) - f m) := by
      rw [← add_assoc]; ring
    rw [this]
    exact Ideal.add_mem _ h1 ih

lemma complete_O (x : ∀ n, (Rn p O n)) (hx : ∀ n, rRing p O n (x (n + 1)) = x n) :
    ∃ a : O, ∀ n, Ideal.Quotient.mk (span {(p : O) ^ (n + 1)}) a = x n := by
  choose f hf using fun n => Ideal.Quotient.mk_surjective (x n)
  have hc : ∀ n, f (n + 1) - f n ∈ span {(p : O) ^ (n + 1)} := by
    intro n
    have h := hx n
    rw [← hf (n + 1), ← hf n, rRing, Ideal.Quotient.lift_mk, Ideal.Quotient.eq] at h
    exact h
  have hsm : ∀ m, (span {(p : O)} ^ m • ⊤ : Submodule O O) = span {(p : O) ^ m} := by
    intro m
    rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := span {(p : O)}) (M := O) inferInstance
    (f := f) (fun {m n} hmn => by
      rw [SModEq.sub_mem, hsm]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      have := sub_mem_of_compat p O f hc m k
      rw [← neg_sub]
      exact (Ideal.neg_mem_iff _).2 this)
  refine ⟨L, fun n => ?_⟩
  rw [← hf n, Ideal.Quotient.eq]
  have h1 := hL (n + 1)
  rw [SModEq.sub_mem, hsm] at h1
  have h2 := hc n
  have : L - f n = (f (n + 1) - f n) - (f (n + 1) - L) := by ring
  rw [this]
  exact Ideal.sub_mem _ h2 h1

def ainfTowerL : ATowerL (R0 p O ε) p where
  toATower := ainfTower p O hv ε hε
  r' n := ⟨r'Alg p O ε n, TowerExample.isLocalHom_of_surj _ (r'Alg_surj p O ε n)⟩
  r n := ⟨rAlg p O hv ε hε n, TowerExample.isLocalHom_of_surj _ (rAlg_surj p O hv ε hε n)⟩
  r_π n x := by
    obtain ⟨x0, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x0
    rfl
  r_q n x := rfl
  r'_ξ n := rfl
  complete x hx := complete_O p O x hx

lemma root_succ_pow (k : ℕ) : root p O ε (k + 1) ^ p = root p O ε k := by
  show ((frobeniusEquiv (PreTilt O p) p).symm^[k + 1] ε) ^ p = _
  rw [Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
  rfl

lemma root_pow_one (n : ℕ) : root p O ε (n + 1) ^ p ^ n = root p O ε 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_mul, root_succ_pow, ih]

theorem zeta_succ_pow (n : ℕ) : zetaV p O ε (n + 1) ^ p = zetaV p O ε n := by
  rw [zetaV, zetaV, ← map_pow, ← map_pow, root_succ_pow]


include hv hε in
theorem zeta_primitive (n : ℕ) : IsPrimitiveRoot (zetaV p O ε n) (p ^ (n + 1)) := by
  have hz1 : zetaV p O ε n ^ p ^ (n + 1) = 1 := by
    rw [zetaV, ← map_pow, ← map_pow, root_pow, fontaineTheta_teichmuller,
      untilt_eps p O hv ε hε]
  have hzn : zetaV p O ε n ^ p ^ n ≠ 1 := by
    rw [zetaV, ← map_pow, ← map_pow, root_pow_one, fontaineTheta_teichmuller]
    exact hε.ne_one hp.out.one_lt
  have hord : orderOf (zetaV p O ε n) ∣ p ^ (n + 1) := orderOf_dvd_of_pow_eq_one hz1
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow hp.out).1 hord
  have hjn : j = n + 1 := by
    by_contra hne
    have hle : j ≤ n := by omega
    apply hzn
    have : orderOf (zetaV p O ε n) ∣ p ^ n := by rw [hj']; exact pow_dvd_pow p hle
    exact orderOf_dvd_iff_pow_eq_one.1 this
  rw [← hjn, ← hj']
  exact IsPrimitiveRoot.orderOf _


include hv hε in
theorem c_val : v (algebraMap O C (fontaineTheta O p (nu p O ε))) ^ (p - 1) = v (p : C) := by
  obtain ⟨-, -, -, hX, -, -⟩ := a0 p C v O hv
  exact (hX ε hv hε).2.2.1


end Ainf

end ReciprocityTheory.PGsh
end
end

section -- merged from ReciprocityTheory.DualLattices.PSerFrobStatement
noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def nsmulF {S : Type} [CommRing S] [Algebra R₀ S] (F : Fin g → MvPowerSeries (Fin g ⊕ Fin g) R₀)
    (a : Fin g → S) : ℕ → Fin g → S
  | 0 => 0
  | n + 1 => fAdd F (nsmulF F a n) a

def PSerFrobStatement (p : ℕ) [Fact p.Prime] (K : LAlg R₀) (ch : FormalChartAtZero B K g) : Prop :=
  ∀ N : ℕ, ∃ G : Fin g → MvPolynomial (Fin g) R₀,
    (∀ k m, (∃ i, ¬ p ∣ m i) → ∃ r : R₀, AddMonoidAlgebra.coeff (G k) m = p * r) ∧
    ∀ (S : Type) [CommRing S] [Algebra R₀ S] (a : Fin g → S), (∀ i, a i ^ N = 0) →
      nsmulF ch.F a p = fun k => MvPolynomial.aeval a (G k)

end ReciprocityTheory.PGsh.Be2
end
end

section -- merged from ReciprocityTheory.DualLattices.EvCotStatement
noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def EvCotStatement (D : Dat p g B Tw Dt Oe σ cp) : Prop :=
  ∀ (C : Type) [Field C] [Algebra (Tw.O : Type) C], Function.Injective (algebraMap (Tw.O : Type) C) →
    ∃ φ : augIdeal (D.evImg C) →ₗ[(Tw.O : Type)] LieDualModP p (Tw.O : Type) g,
      Function.Surjective φ ∧
      LinearMap.ker φ = (sqIdeal (augIdeal (D.evImg C))).comap (augIdeal (D.evImg C)).subtype ∧
      ∀ (a : Oe) (f f' : augIdeal (D.evImg C)) (l : Fin g → (Tw.O : Type)),
        (∀ t, (f' : Nb p g → C) (red p g t) = (f : Nb p g → C) (red p g (D.H.ρ a *ᵥ t))) →
        φ f = Submodule.Quotient.mk l → φ f' = Submodule.Quotient.mk ((D.H.ρL a)ᵀ *ᵥ l)

end ReciprocityTheory.PGsh.Be2
end
end

section -- merged from ReciprocityTheory.DualLattices.InvolutionPermApplyZero
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

lemma idem_free {R : Type} [CommRing R] [IsLocalRing R] {g : ℕ} (P : Matrix (Fin g) (Fin g) R)
    (hP : P * P = P) : ∃ d : ℕ, Nonempty (LinearMap.range (Matrix.mulVecLin P) ≃ₗ[R] (Fin d → R)) := by
  classical
  set f := Matrix.mulVecLin P with hf
  have hff : ∀ x, f (f x) = f x := by
    intro x
    simp only [hf, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hP]
  have hsplit : f.rangeRestrict.comp (LinearMap.range f).subtype = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨x, hx⟩
    obtain ⟨y, rfl⟩ := LinearMap.mem_range.1 hx
    apply Subtype.ext
    first
    | exact hff y
    | simp [hff]
  haveI : Module.Projective R (LinearMap.range f) :=
    Module.Projective.of_split (LinearMap.range f).subtype f.rangeRestrict hsplit
  haveI : Module.Free R (LinearMap.range f) := by
    first
    | exact Module.free_of_flat_of_isLocalRing
    | exact Module.free_of_flat_of_localRing
    | infer_instance
  exact ⟨Module.finrank R (LinearMap.range f), ⟨(Module.finBasis R (LinearMap.range f)).equivFun⟩⟩

lemma hasLen_subsingleton {C : Type} [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R]
    [Algebra R C] (M : Type) [AddCommGroup M] [Module R M] [Subsingleton M] : HasLen v R M 1 := by
  unfold HasLen
  refine ⟨0, fun i => i.elim0, ⟨LinearEquiv.ofSubsingleton _ _⟩, ?_⟩
  simp

section Inv

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Algebra ℤ_[p] O] {σ : O ≃ₐ[ℤ_[p]] O}

def pi2 {m : ℕ} (e : Fin m → O) (π : Equiv.Perm (Fin m)) (hσ : ∀ i, σ (e i) = e (π i)) :
    Equiv.Perm (Fin m) := by
  classical
  exact Equiv.ofBijective (fun k => if e k = 0 then k else π k) (by
    apply Finite.injective_iff_bijective.1
    intro a b hab
    simp only at hab
    by_cases ha : e a = 0 <;> by_cases hb : e b = 0
    · simpa [ha, hb] using hab
    · rw [if_pos ha, if_neg hb] at hab
      exfalso; apply hb
      have h := hσ b
      rw [← hab, ha] at h
      exact σ.injective (h.trans (map_zero σ).symm)
    · rw [if_neg ha, if_pos hb] at hab
      exfalso; apply ha
      have h := hσ a
      rw [hab, hb] at h
      exact σ.injective (h.trans (map_zero σ).symm)
    · rw [if_neg ha, if_neg hb] at hab
      exact π.injective hab)

lemma involutionPerm_apply {m : ℕ} (e : Fin m → O) (π : Equiv.Perm (Fin m)) (hσ : ∀ i, σ (e i) = e (π i))
    (k : Fin m) (hk : e k ≠ 0) : pi2 e π hσ k = π k := by
  unfold pi2
  simp [hk]

lemma involutionPerm_apply_zero {m : ℕ} (e : Fin m → O) (π : Equiv.Perm (Fin m)) (hσ : ∀ i, σ (e i) = e (π i))
    (k : Fin m) (hk : e k = 0) : pi2 e π hσ k = k := by
  unfold pi2
  simp [hk]

lemma involutionPerm_sigma {m : ℕ} (e : Fin m → O) (π : Equiv.Perm (Fin m)) (hσ : ∀ i, σ (e i) = e (π i))
    (k : Fin m) : σ (e k) = e (pi2 e π hσ k) := by
  by_cases hk : e k = 0
  · rw [involutionPerm_apply_zero e π hσ k hk, hk, map_zero]
  · rw [involutionPerm_apply e π hσ k hk]
    exact hσ k

lemma involutionPerm_involutive {m : ℕ} (e : Fin m → O) (π : Equiv.Perm (Fin m)) (hσ : ∀ i, σ (e i) = e (π i))
    (horth : ∀ i j, e i * e j = if i = j then e i else 0) (hinv : ∀ a, σ (σ a) = a) (k : Fin m) :
    pi2 e π hσ (pi2 e π hσ k) = k := by
  by_cases hk : e k = 0
  · rw [involutionPerm_apply_zero e π hσ k hk, involutionPerm_apply_zero e π hσ k hk]
  · have h1 : e (π k) ≠ 0 := by
      intro h0
      apply hk
      have h := hσ k
      rw [h0] at h
      exact σ.injective (h.trans (map_zero σ).symm)
    rw [involutionPerm_apply e π hσ k hk, involutionPerm_apply e π hσ (π k) h1]
    by_contra hne
    have h2 : e (π (π k)) = e k := by
      rw [← hσ, ← hσ, hinv]
    have h3 := horth (π (π k)) k
    rw [if_neg hne, h2, horth k k, if_pos rfl] at h3
    exact hk h3

end Inv

theorem wdetLen : WdetLenStatement := by
  intro p _ g C _ _ _ v R _ _ _ O _ _ σ cp hS H m e π horth hσ hsT hPT hsL hPL w hw cw cwb hcw hcwb
  haveI := htd_domain hS
  haveI := isLocal_of_integers hS.integers
  by_cases hw0 : e w = 0
  · have he' : e (π w) = 0 := by
      have h := hσ w; rw [hw0, map_zero] at h; exact h.symm
    have hsubL : ∀ a : O, a = 0 → Subsingleton (LinearMap.range (Matrix.mulVecLin (H.ρL a))) := by
      rintro a rfl
      refine ⟨fun x y => Subtype.ext ?_⟩
      obtain ⟨x', hx⟩ := x.2; obtain ⟨y', hy⟩ := y.2
      rw [← hx, ← hy]; simp
    have hsubD : ∀ a : O, a = 0 → Subsingleton (lieDPart H a) := by
      rintro a rfl
      refine ⟨fun x y => Subtype.ext ?_⟩
      obtain ⟨x', hx⟩ := x.2; obtain ⟨y', hy⟩ := y.2
      rw [← hx, ← hy]; simp
    have hquot : ∀ {M : Type} [AddCommGroup M] [Module R M] [Subsingleton M] (N : Submodule R M),
        Subsingleton (M ⧸ N) := fun N => ⟨fun a b => by
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ a
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ b
      rw [Subsingleton.elim x y]⟩
    haveI := hsubL _ hw0
    haveI := hsubD _ hw0
    haveI := hsubD _ he'
    haveI : Subsingleton (qW H (e w) (e (π w))) := by
      refine ⟨fun x y => Subtype.ext ?_⟩
      funext k
      rcases k with k | k
      · have hx : ((x : Fin g ⊕ Fin g → R) ∘ Sum.inl) = 0 := by
          have := Subsingleton.elim (⟨_, x.2.1⟩ : lieDPart H (e (π w))) ⟨0, Submodule.zero_mem _⟩
          exact congrArg Subtype.val this
        have hy : ((y : Fin g ⊕ Fin g → R) ∘ Sum.inl) = 0 := by
          have := Subsingleton.elim (⟨_, y.2.1⟩ : lieDPart H (e (π w))) ⟨0, Submodule.zero_mem _⟩
          exact congrArg Subtype.val this
        exact (congrFun hx k).trans (congrFun hy k).symm
      · have hx : ((x : Fin g ⊕ Fin g → R) ∘ Sum.inr) = 0 := by
          have := Subsingleton.elim (⟨_, x.2.2⟩ : LinearMap.range (Matrix.mulVecLin (H.ρL (e w))))
            ⟨0, Submodule.zero_mem _⟩
          exact congrArg Subtype.val this
        have hy : ((y : Fin g ⊕ Fin g → R) ∘ Sum.inr) = 0 := by
          have := Subsingleton.elim (⟨_, y.2.2⟩ : LinearMap.range (Matrix.mulVecLin (H.ρL (e w))))
            ⟨0, Submodule.zero_mem _⟩
          exact congrArg Subtype.val this
        exact (congrFun hx k).trans (congrFun hy k).symm
    haveI : Subsingleton (htCoker H (e w) (e (π w))) := hquot _
    haveI : Subsingleton (htCoker H (e (π w)) (e w)) := hquot _
    haveI : Subsingleton (xMod H e π w) := hquot _
    have h1 : cw = 1 := hasLen_unique hS.integers hcw (hasLen_subsingleton v R _)
    have h2 : cwb = 1 := hasLen_unique hS.integers hcwb (hasLen_subsingleton v R _)
    exact ⟨0, 1, ⟨LinearEquiv.ofSubsingleton _ _⟩, hasLen_subsingleton v R _, by simp [h1, h2]⟩

  set ι := (algebraMap ℤ_[p] R).mapMatrix (m := Ix g) with hι
  have hpw : pi2 e π hσ w = π w := involutionPerm_apply e π hσ w hw0
  set π₂ := pi2 e π hσ
  set π' : Equiv.Perm (Fin (m + 1)) := Equiv.Perm.decomposeFin.symm (0, π₂) with hπ'
  have hπ'0 : π' 0 = 0 := by simp [hπ']
  have hπ's : ∀ k : Fin m, π' k.succ = (π₂ k).succ := by
    intro k; simp [hπ', Equiv.Perm.decomposeFin_symm_apply_succ]
  set εT : Fin (m + 1) → Matrix (Ix g) (Ix g) R :=
    Fin.cons (ι H.P) (fun i => ι (H.ρ (e i))) with hεT
  set εL : Fin (m + 1) → Matrix (Fin g) (Fin g) R :=
    Fin.cons H.PL (fun i => H.ρL (e i)) with hεL
  have hPcomm : ∀ i, H.P * H.ρ (e i) = 0 := fun i => by rw [H.projectors.2.2.2.1, hPT]
  have hPLcomm : ∀ i, H.PL * H.ρL (e i) = 0 := fun i => by rw [H.projectors.2.2.2.2, hPL]
  have hπinv : ∀ k, π' (π' k) = k := by
    intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · rw [hπ'0, hπ'0]
    · rw [hπ's, hπ's, involutionPerm_involutive e π hσ horth hS.invol]
  have hTo : ∀ a b, εT a * εT b = if a = b then εT a else 0 := by
    intro a b
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
    · simp only [hεT, Fin.cons_zero, if_true, ← map_mul, H.projectors.1]
    · simp only [hεT, Fin.cons_zero, Fin.cons_succ, ← map_mul, hPcomm, map_zero,
        (Fin.succ_ne_zero j).symm, if_false]
    · simp only [hεT, Fin.cons_zero, Fin.cons_succ, ← map_mul, hPT, map_zero,
        Fin.succ_ne_zero i, if_false]
    · simp only [hεT, Fin.cons_succ, ← map_mul, ← map_mul H.ρ, horth, Fin.succ_inj]
      split_ifs <;> simp
  have hLo : ∀ a b, εL a * εL b = if a = b then εL a else 0 := by
    intro a b
    refine Fin.cases ?_ (fun i => ?_) a <;> refine Fin.cases ?_ (fun j => ?_) b
    · simp only [hεL, Fin.cons_zero, if_true, H.projectors.2.1]
    · simp only [hεL, Fin.cons_zero, Fin.cons_succ, hPLcomm, (Fin.succ_ne_zero j).symm, if_false]
    · simp only [hεL, Fin.cons_zero, Fin.cons_succ, hPL, Fin.succ_ne_zero i, if_false]
    · simp only [hεL, Fin.cons_succ, ← map_mul, horth, Fin.succ_inj]
      split_ifs <;> simp
  have hTs : ∑ a, εT a = 1 := by
    rw [Fin.sum_univ_succ]
    simp only [hεT, Fin.cons_zero, Fin.cons_succ]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum ι (fun i => H.ρ (e i)) Finset.univ, ← map_add (f := _), add_comm, hsT, map_one]
  have hLs : ∑ a, εL a = 1 := by
    rw [Fin.sum_univ_succ]
    simp only [hεL, Fin.cons_zero, Fin.cons_succ]
    rw [add_comm, hsL]
  have hHt : ∀ a, H.Ht * εT a = (εL (π' a))ᵀ * H.Ht := by
    intro a
    refine Fin.cases ?_ (fun i => ?_) a
    · rw [hπ'0]; simp only [hεT, hεL, Fin.cons_zero]; exact H.Ht_equivariant.2
    · rw [hπ's]; simp only [hεT, hεL, Fin.cons_succ]
      rw [← involutionPerm_sigma e π hσ i]; exact H.Ht_equivariant.1 (e i)
  have hadj : ∀ a, (εT a)ᵀ * H.E.map (algebraMap ℤ_[p] R) =
      H.E.map (algebraMap ℤ_[p] R) * εT (π' a) := by
    intro a
    refine Fin.cases ?_ (fun i => ?_) a
    · rw [hπ'0]; simp only [hεT, Fin.cons_zero, hι, RingHom.mapMatrix_apply]
      rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, H.projectors.2.2.1]
    · rw [hπ's]; simp only [hεT, Fin.cons_succ, hι, RingHom.mapMatrix_apply]
      rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, H.E_equivariant (e i),
        involutionPerm_sigma e π hσ i]
  obtain ⟨hua, hub, -⟩ := u1 R g (m + 1) H.Ht H.Bt (H.E.map (algebraMap ℤ_[p] R)) cp εT εL π'
    hπinv hTo hTs hLo hLs hHt hadj H.form_eq_alt
  have hbt : ∑ a, εL a * H.Bt * εT a = btP H e := by
    rw [Fin.sum_univ_succ]
    simp only [hεT, hεL, Fin.cons_zero, Fin.cons_succ, btP, hι, RingHom.mapMatrix_apply]
    rw [add_comm]
  rw [hbt] at hua hub
  have hidem : H.ρL (e w) * H.ρL (e w) = H.ρL (e w) := by rw [← map_mul, horth, if_pos rfl]
  obtain ⟨d, ⟨φ⟩⟩ := idem_free (H.ρL (e w)) hidem
  obtain ⟨hEt, -, hEdet⟩ := htd_E H
  have hcw' : HasLen v R (cokE H.Ht εT εL w.succ (π' w.succ)) cw := by
    rw [hπ's, hpw]; exact hcw
  have hcwb' : HasLen v R (cokE H.Ht εT εL (π' w.succ) w.succ) cwb := by
    rw [hπ's, hpw]; exact hcwb
  obtain ⟨X, hX, hXe⟩ := lenId C v R hS.integers g (m + 1) H.Ht (btP H e)
    (H.E.map (algebraMap ℤ_[p] R)) cp (htd_cp_ne hS) hEdet hua εT εL π' hπinv hTo hTs hLo hLs
    hHt hub hadj w.succ d ⟨φ⟩ cw cwb hcw' hcwb'
  refine ⟨d, X, ⟨φ⟩, ?_, hXe⟩
  have hX' : HasLen v R (qE εL w.succ (π' w.succ) ⧸
      ((LinearMap.range (Matrix.mulVecLin (εT w.succ))).map
        (Matrix.mulVecLin (fromRows H.Ht (btP H e)))).comap (qE εL w.succ (π' w.succ)).subtype) X := hX
  generalize hq : π' w.succ = q at hX'
  rw [hπ's, hpw] at hq
  subst hq
  exact hX'

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.EvBtStatement
noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def EvBtStatement (D : Dat p g B Tw Dt Oe σ cp) : Prop :=
  ∀ (C : Type) [Field C] [Algebra (Tw.O : Type) C], ∀ k : Fin g, ∃ f ∈ D.evImg C, ∀ t : TT p g,
    ∃ r : (Tw.O : Type), algebraMap (Tw.O : Type) C
      ((D.H.Bt *ᵥ (algebraMap ℤ_[p] (Tw.O : Type) ∘ t)) k) - f (red p g t) =
        algebraMap (Tw.O : Type) C (p * r)

end ReciprocityTheory.PGsh.Be2
end
end

section -- merged from ReciprocityTheory.DualLattices.WFrobStatement
noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def WFrobStatement {K : LAlg R₀} (wd : WData Tw K) (g : ℕ) : Prop :=
  ∀ G : MvPolynomial (Fin g) (wd.W : Type),
    (∀ m, (∃ i, ¬ p ∣ m i) → AddMonoidAlgebra.coeff G m ∈ Ideal.span {(p : (wd.W : Type))}) →
    ∃ Q : MvPolynomial (Fin g) (Tw.R 0 : Type), ∀ y : Fin g → (wd.W : Type),
      MvPolynomial.eval y G ∈ Ideal.span {(p : (wd.W : Type))} →
      ∀ a : (wd.W : Type), wd.πW.1 a = MvPolynomial.eval (fun i => wd.πW.1 (y i)) Q →
        MvPolynomial.eval y G = p * a

end ReciprocityTheory.PGsh.Be2
end
end

section -- merged from ReciprocityTheory.DualLattices.HasLenLeOfSurj
noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

theorem hasLen_le_of_surj {C : Type} [Field C] {v : Valuation C NNReal} {R : Type} [CommRing R]
    [Algebra R C] (hv : v.Integers R) {M : Type} [AddCommGroup M] [Module R M] {z : NNReal}
    (hz : HasLen v R M z) (q : R) (r : ℕ)
    (π : M →ₗ[R] ((t : Fin r) → R ⧸ Ideal.span {q})) (hπ : Function.Surjective π) :
    z ≤ v (algebraMap R C q) ^ r := by
  obtain ⟨m, c, ⟨e⟩, hzc⟩ := hz
  have hx : HasLen v R ((t : Fin r) → R ⧸ Ideal.span {q}) (v (algebraMap R C q) ^ r) :=
    ⟨r, fun _ => q, ⟨LinearEquiv.refl R _⟩, by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]⟩
  have hs : Submodule.span R (Set.range fun i : Fin m =>
      (Pi.single i 1 : (j : Fin m) → R ⧸ Ideal.span {c j})) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [show x = ∑ i, (Pi.single i (x i) : (j : Fin m) → R ⧸ Ideal.span {c j}) from
      (Finset.univ_sum_single x).symm]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x i)
    have hsi : (Pi.single i (x i) : (j : Fin m) → R ⧸ Ideal.span {c j}) = a • Pi.single i 1 := by
      rw [← ha]
      ext j
      by_cases hj : j = i
      · subst hj
        rw [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, Algebra.smul_def, mul_one,
          Ideal.Quotient.algebraMap_eq]
      · simp [Pi.single_eq_of_ne hj]
    rw [hsi]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hy : Submodule.span R (Set.range fun i : Fin m =>
      π (e.symm (Pi.single i 1 : (j : Fin m) → R ⧸ Ideal.span {c j}))) = ⊤ := by
    have hr : (Set.range fun i : Fin m => π (e.symm (Pi.single i 1 : (j : Fin m) → R ⧸ Ideal.span {c j}))) =
        (π ∘ₗ e.symm.toLinearMap) '' Set.range fun i : Fin m =>
          (Pi.single i 1 : (j : Fin m) → R ⧸ Ideal.span {c j}) := by
      rw [← Set.range_comp]
      rfl
    rw [hr, Submodule.span_image, hs, Submodule.map_top, LinearMap.range_eq_top]
    exact hπ.comp e.symm.surjective
  have key := prod_le_of_gen hv hx _ hy c (fun i => ⟨0, ?_⟩)
  · rw [← hzc]
    exact key
  · simp only [Pi.zero_apply, ite_self, zero_smul, Finset.sum_const_zero]
    have h0 : c i • (Pi.single i 1 : (j : Fin m) → R ⧸ Ideal.span {c j}) = 0 := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp only [Pi.smul_apply, Pi.single_eq_same, Pi.zero_apply]
        rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
        exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
      · simp [Pi.single_eq_of_ne hj]
    rw [← LinearMap.map_smul, ← LinearEquiv.map_smul, h0, map_zero, map_zero]

section Mono

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R} {H : HodgeTateDatum p g v R O σ cp} {U : UnramData p g v R O σ cp H}
  {X : Fin U.m → NNReal}

lemma monX_eq (D : Lifts H U X) (α : Nb p g) : monX D α = ∏ j, xL D j ^ (α j).val := by
  funext y
  simp only [monX, Finset.prod_apply, Pi.pow_apply]

lemma monX_mem (D : Lifts H U X) (α : Nb p g) : monX D α ∈ H.AA.carrier := by
  have hx : ∀ j, xL D j ∈ H.AA.carrier := fun j => (Submodule.mem_inf.mp (D.x_mem j)).1
  have hpow : ∀ (f : Nb p g → C) (n : ℕ), f ∈ H.AA.carrier → f ^ n ∈ H.AA.carrier := by
    intro f n hf
    induction n with
    | zero => simpa using H.AA.one_mem
    | succ n ih =>
      rw [pow_succ]
      exact H.AA.mul_mem _ _ ih hf
  rw [monX_eq]
  exact Finset.prod_induction _ (· ∈ H.AA.carrier) (fun a b ha hb => H.AA.mul_mem a b ha hb)
    H.AA.one_mem (fun j _ => hpow _ _ (hx j))

lemma monX_zero_at (D : Lifts H U X) {α : Nb p g} (hα : α ≠ 0) : monX D α 0 = 0 := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hα
  have hj' : α j ≠ 0 := hj
  have h0 : xL D j 0 = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp (D.x_mem j)).2
  have hv : (α j).val ≠ 0 := by rwa [Ne, ZMod.val_eq_zero]
  simp only [monX]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [h0, zero_pow hv])

lemma monX_mem_aug (D : Lifts H U X) {α : Nb p g} (hα : α ≠ 0) :
    monX D α ∈ augIdeal H.AA.carrier :=
  Submodule.mem_inf.mpr ⟨monX_mem D α, LinearMap.mem_ker.mpr (monX_zero_at D hα)⟩

lemma monX_single (D : Lifts H U X) (k : Ix g) : monX D (Pi.single k 1) = xL D k := by
  rw [monX_eq, Finset.prod_eq_single k]
  · simp [ZMod.val_one]
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · intro h
    exact absurd (Finset.mem_univ k) h

lemma monX_zero (D : Lifts H U X) : monX D 0 = 1 := by
  rw [monX_eq]
  simp

lemma monX_split (D : Lifts H U X) {α : Nb p g} {j : Ix g} (hj : α j ≠ 0) :
    monX D α = xL D j * monX D (Function.update α j (α j - 1)) := by
  rw [monX_eq, monX_eq, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
  have hrest : ∏ i ∈ Finset.univ.erase j, xL D i ^ (Function.update α j (α j - 1) i).val =
      ∏ i ∈ Finset.univ.erase j, xL D i ^ (α i).val :=
    Finset.prod_congr rfl fun i hi => by simp [Function.update_apply, Finset.ne_of_mem_erase hi]
  have hself : (Function.update α j (α j - 1) j) = α j - 1 := by simp [Function.update_apply]
  rw [hrest, hself]
  have hv1 : 1 ≤ (α j).val := Nat.one_le_iff_ne_zero.mpr (by rwa [Ne, ZMod.val_eq_zero])
  have hsub : (α j - 1).val = (α j).val - 1 := by
    rw [ZMod.val_sub (by rw [ZMod.val_one]; exact hv1), ZMod.val_one]
  rw [hsub, ← mul_assoc, ← pow_succ', Nat.sub_add_cancel hv1]

lemma monX_mem_sq (D : Lifts H U X) {α : Nb p g} (h0 : α ≠ 0) (h1 : ∀ k, α ≠ Pi.single k 1) :
    monX D α ∈ sqIdeal (augIdeal H.AA.carrier) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp h0
  have hj' : α j ≠ 0 := hj
  have hβ : Function.update α j (α j - 1) ≠ 0 := by
    intro hz
    apply h1 j
    funext i
    by_cases hi : i = j
    · subst hi
      rw [Pi.single_eq_same]
      simpa [Function.update_apply, sub_eq_zero] using congrFun hz i
    · rw [Pi.single_eq_of_ne hi]
      simpa [Function.update_apply, hi] using congrFun hz i
  exact Submodule.subset_span ⟨xL D j, D.x_mem j, monX D (Function.update α j (α j - 1)),
    monX_mem_aug D hβ, monX_split D hj'⟩

lemma sub_lin_mem_sq (hv : v.Integers R) (D : Lifts H U X) (hdet : (valM D).det ≠ 0)
    (hbasis : H.AA.carrier = Submodule.span R (Set.range fun (α : Nb p g) (y : Nb p g) =>
      ∏ j, (algebraMap R C (D.ε j) * D.u j y) ^ (α j).val))
    {f : Nb p g → C} (hf : f ∈ augIdeal H.AA.carrier) :
    ∃ c : Ix g → R, (∀ k, algebraMap R C (c k) = linX D f k) ∧
      f - ∑ k, c k • xL D k ∈ sqIdeal (augIdeal H.AA.carrier) := by
  classical
  have hfA : f ∈ Submodule.span R (Set.range fun α => monX D α) := by
    have h := (Submodule.mem_inf.mp hf).1
    rw [hbasis] at h
    exact h
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hfA
  have hf0 : f 0 = 0 := LinearMap.mem_ker.mp (Submodule.mem_inf.mp hf).2
  have hval : f = (valM D) *ᵥ (fun α => algebraMap R C (c α)) := by
    rw [← hc]
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def, Matrix.mulVec, dotProduct, valM,
      Matrix.of_apply]
    exact Finset.sum_congr rfl fun α _ => mul_comm _ _
  have hcoef : coefX D f = fun α => algebraMap R C (c α) := by
    rw [coefX, hval, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  refine ⟨fun k => c (Pi.single k 1), fun k => ?_, ?_⟩
  · rw [linX, hcoef]
  · set P : Nb p g → Prop := fun α => α ≠ 0 ∧ ∀ k, α ≠ Pi.single k 1 with hP
    have hw0 : algebraMap R C (c 0) = 0 := by
      have h := congrFun hval 0
      rw [hf0] at h
      simp only [Matrix.mulVec, dotProduct, valM, Matrix.of_apply] at h
      rw [Finset.sum_eq_single 0 (fun α _ hα => by rw [monX_zero_at D hα, zero_mul])
        (fun h => absurd (Finset.mem_univ 0) h), monX_zero] at h
      simpa using h.symm
    have hB : ∑ α, (if P α then 0 else c α • monX D α) = ∑ k, c (Pi.single k 1) • xL D k := by
      have hsub : ∑ α, (if P α then 0 else c α • monX D α) =
          ∑ α ∈ Finset.univ.image (fun k : Ix g => (Pi.single k (1 : ZMod p) : Nb p g)),
            (if P α then 0 else c α • monX D α) := by
        symm
        refine Finset.sum_subset (Finset.subset_univ _) fun α _ hα => ?_
        by_cases hPα : P α
        · simp [hPα]
        · rw [if_neg hPα]
          have h0 : α = 0 := by
            by_contra h0
            apply hPα
            refine ⟨h0, fun k hk => hα ?_⟩
            exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk.symm⟩
          subst h0
          rw [monX_zero]
          funext y
          simp [Algebra.smul_def, hw0]
      rw [hsub, Finset.sum_image (fun k _ k' _ h => by
        by_contra hne
        have h2 := congrFun h k
        rw [Pi.single_eq_same, Pi.single_eq_of_ne hne] at h2
        exact one_ne_zero h2)]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hnP : ¬ P (Pi.single k 1) := fun h => h.2 k rfl
      rw [if_neg hnP, monX_single]
    have hA : ∀ α, (if P α then c α • monX D α else 0) ∈ sqIdeal (augIdeal H.AA.carrier) := by
      intro α
      split_ifs with h
      · exact Submodule.smul_mem _ _ (monX_mem_sq D h.1 h.2)
      · exact Submodule.zero_mem _
    have hsum : f = ∑ α, (if P α then c α • monX D α else 0) +
        ∑ α, (if P α then 0 else c α • monX D α) := by
      rw [← Finset.sum_add_distrib, ← hc]
      refine Finset.sum_congr rfl fun α _ => ?_
      split_ifs <;> simp
    rw [← hB, hsum, add_sub_cancel_right]
    exact Submodule.sum_mem _ fun α _ => hA α

end Mono

end ReciprocityTheory.PGsh.Up
end
end

section -- merged from ReciprocityTheory.DualLattices.EvActStatement
noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def EvActStatement (D : Dat p g B Tw Dt Oe σ cp) : Prop :=
  ∀ (C : Type) [Field C] [Algebra (Tw.O : Type) C], ∀ a : Oe, ∀ f ∈ D.evImg C, ∃ f' ∈ D.evImg C,
    ∀ t : TT p g, f' (red p g t) = f (red p g (D.H.ρ a *ᵥ t))

end ReciprocityTheory.PGsh.Be2
end
end

section -- merged from ReciprocityTheory.DualLattices.EvHopfStatement
noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def EvHopfStatement (D : Dat p g B Tw Dt Oe σ cp) : Prop :=
  ∀ (C : Type) [Field C] [Algebra (Tw.O : Type) C], Function.Injective (algebraMap (Tw.O : Type) C) →
    (∀ f ∈ D.evImg C, addPull (Tw.O : Type) (Nb p g) f ∈ tensorSpan (Tw.O : Type) (D.evImg C)) ∧
      ∀ f ∈ D.evImg C, (fun x => f (-x)) ∈ D.evImg C

end ReciprocityTheory.PGsh.Be2
end
end

section -- merged from ReciprocityTheory.DualLattices.EvenTwoEvaluationSign
noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def EvenTwoEvaluationSign (D : Dat p g B Tw Dt Oe σ cp) : Prop :=
  ∀ (C : Type) [Field C] [Algebra (Tw.O : Type) C], IsDomain (Tw.O : Type) →
    Function.Injective (algebraMap (Tw.O : Type) C) → p = 2 → ∀ s : TT p g, ∃ f ∈ D.evImg C,
    ∀ t : TT p g, f (red p g t) = (-1 : C) ^ (PadicInt.toZMod (pair p g D.H.E s t)).val

end ReciprocityTheory.PGsh.Be2
end
end

section -- merged from ReciprocityTheory.DualLattices.EvLatStatement
noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def EvLatStatement (D : Dat p g B Tw Dt Oe σ cp) : Prop :=
  ∀ (C : Type) [Field C] [Algebra (Tw.O : Type) C], IsDomain (Tw.O : Type) →
    Function.Injective (algebraMap (Tw.O : Type) C) →
    IsLat (Tw.O : Type) (D.evImg C) ∧ D.evImg C ≤ intFun (Tw.O : Type) (Nb p g) ∧
      (1 : Nb p g → C) ∈ D.evImg C ∧ ∀ f f', f ∈ D.evImg C → f' ∈ D.evImg C → f * f' ∈ D.evImg C

end ReciprocityTheory.PGsh.Be2
end
end

section -- merged from ReciprocityTheory.DualLattices.EvHtStatement
noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def EvHtStatement (D : Dat p g B Tw Dt Oe σ cp) : Prop :=
  ∀ (C : Type) [Field C] [Algebra (Tw.O : Type) C], ∀ k : Fin g, ∃ f ∈ D.evImg C, ∀ t : TT p g,
    ∃ r : (Tw.O : Type), algebraMap (Tw.O : Type) C
      ((D.H.Ht *ᵥ (algebraMap ℤ_[p] (Tw.O : Type) ∘ t)) k) - f (red p g t) =
        algebraMap (Tw.O : Type) C (p * r)

end ReciprocityTheory.PGsh.Be2
end
end
