module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdinaryHeckeAlgebraIntegral

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.PlNormal
open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem core_ex {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (K P : Subgroup Γ) [P.Normal] (hK : IsOpen (K : Set Γ)) (hP : P ≤ K) :
    ∃ U : OpenNormalSubgroup Γ, P ≤ U.toSubgroup ∧ U.toSubgroup ≤ K := by
  haveI : Finite (Γ ⧸ K) := Subgroup.quotient_finite_of_isOpen K hK
  haveI : K.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hc : IsClosed (K.normalCore : Set Γ) := Subgroup.normalCore_isClosed K (K.isClosed_of_isOpen hK)
  have ho : IsOpen (K.normalCore : Set Γ) := Subgroup.isOpen_of_isClosed_of_finiteIndex _ hc
  exact ⟨{ toSubgroup := K.normalCore, isOpen' := ho, isNormal' := inferInstance },
    Subgroup.normal_le_normalCore.2 hP, K.normalCore_le⟩

private theorem pl_normal (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] (H : Subgroup Γ) :
    (PL l H).Normal := by
  refine ⟨fun a ha g => ?_⟩
  simp only [PL, Subgroup.mem_iInf] at ha ⊢
  intro U hU
  exact U.isNormal'.conj_mem a (ha U hU) g

private theorem pl_le (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] (H : OpenNormalSubgroup Γ) :
    PL l H.toSubgroup ≤ H.toSubgroup := by
  intro a ha
  simp only [PL, Subgroup.mem_iInf] at ha
  exact ha H fun h hh => ⟨0, by rw [pow_zero, pow_one]; exact hh⟩

theorem UpperTheory.V.Th.Sp.close :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (y : Pt G0.frame O n), (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1) → ∀ K : ℕ, ∀ᶠ N in atTop, ∀ j a b, mat y.ρ ((T.h N).p₀ (T.ph N j)) a b - mat y.ρ (T.sg j) a b ∈ maximalIdeal O ^ K := by
  intro l _ L G0 T n O _ _ _ y hPL K
  haveI := pl_normal l T.H.toSubgroup
  have hle := pl_le l T.H
  let R : G0.G₀ →* Matrix (Fin n) (Fin n) (O ⧸ maximalIdeal O ^ K) :=
    (Ideal.Quotient.mk (maximalIdeal O ^ K)).mapMatrix.toMonoidHom.comp (mat y.ρ)
  have hR : ∀ g i j, R g i j = Ideal.Quotient.mk (maximalIdeal O ^ K) (mat y.ρ g i j) := fun _ _ _ => rfl
  have h0 : IsLocallyConstant fun g : G0.G₀ => R g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g0
    have : ∀ᶠ g in nhds g0, ∀ i j, R g i j = R g0 i j :=
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
        (y.cont i j K).eventually_eq g0
    filter_upwards [this] with g hg
    exact Matrix.ext hg
  have ho : IsOpen ((R.ker.map G0.η.ker.subtype : Subgroup G0.Γ) : Set G0.Γ) :=
    G0.η_open.isOpenMap_subtype_val _ (h0.isOpen_fiber 1)
  have h1R : ∀ g, y.ρ g = 1 → R g = 1 := fun g h => by
    show (Ideal.Quotient.mk (maximalIdeal O ^ K)).mapMatrix (Units.coeHom _ (y.ρ g)) = 1
    rw [h, map_one, map_one]
  obtain ⟨V, h1, h2⟩ := core_ex _ (PL l T.H.toSubgroup) ho fun g hg =>
    ⟨⟨g, T.H_η g (hle hg)⟩, h1R _ (hPL _ hg), rfl⟩
  filter_upwards [Filter.eventually_all.2 fun j => T.ph_lim V j h1] with N hN j a b
  obtain ⟨u, hu, e1⟩ := h2 (hN j)
  have e2 : (T.h N).p₀ (T.ph N j) = u * T.sg j := Subtype.ext (by
    show (T.h N).p (T.ph N j) = (u : G0.Γ) * T.sg j
    rw [show (u : G0.Γ) = _ from e1, inv_mul_cancel_right])
  have e3 : R ((T.h N).p₀ (T.ph N j)) = R (T.sg j) := by
    rw [e2, map_mul, show R u = 1 from hu, one_mul]
  rw [← Ideal.Quotient.eq, ← hR, ← hR, e3]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.SpectralEigenvalues.HensNewton
open IsLocalRing Polynomial
open scoped Ring

private theorem hens_newton {R : Type} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (f : R[X]) (h₁ : f.eval 0 ∈ maximalIdeal R) (h₂ : IsUnit (f.derivative.eval 0)) :
    ∃ a : R, f.eval a = 0 ∧ a ∈ maximalIdeal R := by
  classical
  set I := maximalIdeal R with hI
  let c : ℕ → R := fun n => Nat.recOn n 0 fun _ b => b - f.eval b * (f.derivative.eval b)⁻¹ʳ
  have hc : ∀ n, c (n + 1) = c n - f.eval (c n) * (f.derivative.eval (c n))⁻¹ʳ := fun n => rfl
  have hev : ∀ (g : R[X]) (b : R), b ∈ I → g.eval b - g.eval 0 ∈ I := by
    intro g b hb
    obtain ⟨t, ht⟩ := sub_dvd_eval_sub b 0 g
    rw [ht, sub_zero]
    exact I.mul_mem_right _ hb
  have hcI : ∀ n, c n ∈ I := by
    intro n
    induction n with
    | zero => exact I.zero_mem
    | succ n ih =>
      rw [hc]
      refine I.sub_mem ih (I.mul_mem_right _ ?_)
      have := I.add_mem (hev f _ ih) h₁
      simpa using this
  have hu : ∀ n, IsUnit (f.derivative.eval (c n)) := by
    intro n
    by_contra hn
    have h3 : f.derivative.eval (c n) ∈ I := (mem_maximalIdeal _).2 hn
    have h4 := I.sub_mem h3 (hev f.derivative _ (hcI n))
    rw [sub_sub_cancel] at h4
    exact (mem_maximalIdeal _).1 h4 h₂
  have hf : ∀ n, f.eval (c n) ∈ I ^ (n + 1) := by
    intro n
    induction n with
    | zero => simpa [c] using h₁
    | succ n ih =>
      obtain ⟨k, hk⟩ := binomExpansion f (c n) (-(f.eval (c n) * (f.derivative.eval (c n))⁻¹ʳ))
      rw [hc, sub_eq_add_neg, hk]
      have h5 : f.eval (c n) + f.derivative.eval (c n) * -(f.eval (c n) * (f.derivative.eval (c n))⁻¹ʳ) = 0 := by
        rw [mul_neg, mul_left_comm, Ring.mul_inverse_cancel _ (hu n), mul_one, add_neg_cancel]
      rw [h5, zero_add]
      refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (show n + 1 + 1 ≤ (n + 1) * 2 by omega) ?_)
      rw [pow_mul]
      exact Ideal.pow_mem_pow (neg_mem (Ideal.mul_mem_right _ _ ih)) _
  have aux : ∀ m n, m ≤ n → c m ≡ c n [SMOD (I ^ m • ⊤ : Ideal R)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
    induction n, hmn using Nat.le_induction with
    | base => rfl
    | succ k hk ih =>
      rw [SModEq.sub_mem] at ih ⊢
      have h6 : f.eval (c k) * (f.derivative.eval (c k))⁻¹ʳ ∈ I ^ m :=
        Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (by omega) (hf k))
      have := (I ^ m).add_mem ih h6
      rw [hc]
      convert this using 1
      ring
  obtain ⟨a, ha⟩ := IsPrecomplete.prec' c (aux _ _)
  refine ⟨a, ?_, ?_⟩
  · suffices ∀ n, f.eval a ≡ 0 [SMOD (I ^ n • ⊤ : Ideal R)] by exact IsHausdorff.haus' _ this
    intro n
    specialize ha n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at ha ⊢
    refine (ha.symm.eval f).trans ?_
    rw [SModEq.zero]
    exact Ideal.pow_le_pow_right le_self_add (hf _)
  · specialize ha 1
    rw [pow_one, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem] at ha
    have := I.sub_mem (hcI 1) ha
    simpa using this

private theorem hens_one {R : Type} [CommRing R] [IsLocalRing R] [IsAdicComplete (maximalIdeal R) R]
    (P : R[X]) (a e w q u : R) (hq : q ∈ maximalIdeal R) (hu : IsUnit u)
    (h0 : P.eval a = e ^ 2 * w * q) (h1 : P.derivative.eval a = e * u) :
    ∃ y ∈ maximalIdeal R, P.eval (a + e * w * y) = 0 := by
  set T := taylor a P with hT
  set S := T.divX.divX with hS
  have hdec : T = C (P.eval a) + C (P.derivative.eval a) * X + X ^ 2 * S := by
    have e1 := T.divX_mul_X_add
    have e2 := T.divX.divX_mul_X_add
    rw [coeff_divX, zero_add, hT, taylor_coeff_one, ← hT, ← hS] at e2
    rw [hT, taylor_coeff_zero, ← hT, ← e2] at e1
    rw [← e1]
    ring
  obtain ⟨y, hy, hym⟩ := hens_newton (C q + C u * X + C w * X ^ 2 * S.comp (C (e * w) * X))
    (by simpa using hq) (by simpa [derivative_mul] using hu)
  refine ⟨y, hym, ?_⟩
  have h2 : P.eval (a + e * w * y) = T.eval (e * w * y) := by
    rw [hT, taylor_eval, add_comm]
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_comp] at hy
  rw [h2, hdec, h0, h1]
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
  linear_combination e ^ 2 * w * hy

private theorem hens_eval {R : Type} [CommRing R] (I : Ideal R) (F : R[X]) (h : ∀ k, F.coeff k ∈ I)
    (a : R) : F.eval a ∈ I := by
  rw [eval_eq_sum_range]
  exact I.sum_mem fun k _ => I.mul_mem_right _ (h k)

theorem UpperTheory.V.Th.Sp.hens :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (n : ℕ) (al : Fin n → O), Function.Injective al → ∀ K : ℕ, ∃ K' : ℕ, ∀ P : O[X], P.Monic → P.natDegree = n → (∀ k, P.coeff k - (∏ i, (X - C (al i))).coeff k ∈ maximalIdeal O ^ K') → ∃ α : Fin n → O, P = ∏ i, (X - C (α i)) ∧ ∀ i, α i - al i ∈ maximalIdeal O ^ K := by
  intro O _ _ _ _ n al hal K
  classical
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hm : maximalIdeal O = Ideal.span {p} := hp.maximalIdeal_eq
  have hpm : p ∈ maximalIdeal O := by rw [hm]; exact Ideal.mem_span_singleton_self p
  set e : Fin n → O := fun i => ∏ k ∈ Finset.univ.erase i, (al i - al k) with he
  have he0 : ∀ i, e i ≠ 0 := fun i =>
    Finset.prod_ne_zero_iff.2 fun k hk => sub_ne_zero.2 fun h => (Finset.ne_of_mem_erase hk) (hal h).symm
  have hN : ∀ i, ∃ N : ℕ, ∀ z ∈ maximalIdeal O ^ N, e i ^ 2 * p ^ K * p ∣ z := by
    intro i
    obtain ⟨N, hN⟩ := IsDiscreteValuationRing.associated_pow_irreducible
      (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 (he0 i)) (pow_ne_zero K hp.ne_zero)) hp.ne_zero) hp
    refine ⟨N, fun z hz => ?_⟩
    rw [hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hz
    exact hN.dvd.trans hz
  choose N hN using hN
  refine ⟨Finset.univ.sup N, fun P hP hdeg hco => ?_⟩
  have hroot : ∀ i, ∃ y ∈ maximalIdeal O, P.eval (al i + e i * p ^ K * y) = 0 := by
    intro i
    have hle : maximalIdeal O ^ (Finset.univ.sup N) ≤ maximalIdeal O ^ N i :=
      Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ i))
    have hG : (∏ j, (X - C (al j)) : O[X]) = (X - C (al i)) * ∏ j ∈ Finset.univ.erase i, (X - C (al j)) :=
      (Finset.mul_prod_erase _ (fun j => (X - C (al j) : O[X])) (Finset.mem_univ i)).symm
    have hF : ∀ k, (P - ∏ j, (X - C (al j))).coeff k ∈ maximalIdeal O ^ N i := fun k => by
      rw [coeff_sub]; exact hle (hco k)
    have hF' : ∀ k, (derivative (P - ∏ j, (X - C (al j)))).coeff k ∈ maximalIdeal O ^ N i := fun k => by
      rw [coeff_derivative]; exact Ideal.mul_mem_right _ _ (hF _)
    obtain ⟨s, hs⟩ := hN i _ (hens_eval _ _ hF (al i))
    obtain ⟨t, ht⟩ := hN i _ (hens_eval _ _ hF' (al i))
    rw [hG] at hs ht
    simp only [eval_sub, eval_mul, eval_X, eval_C, sub_self, zero_mul, sub_zero] at hs
    simp only [derivative_sub, derivative_mul, derivative_X, derivative_C, eval_sub, eval_add,
      eval_mul, eval_X, eval_C, sub_self, zero_mul, sub_zero, one_mul, add_zero, eval_prod] at ht
    refine hens_one P (al i) (e i) (p ^ K) (p * s) (1 + p * (e i * p ^ K * t))
      (Ideal.mul_mem_right _ _ hpm) ?_ (by rw [hs]; ring) ?_
    · by_contra hn
      have h3 := (maximalIdeal O).sub_mem ((mem_maximalIdeal _).2 hn)
        (Ideal.mul_mem_right (e i * p ^ K * t) _ hpm)
      rw [add_sub_cancel_right] at h3
      exact (mem_maximalIdeal _).1 h3 isUnit_one
    · have ht' : P.derivative.eval (al i) - e i = e i ^ 2 * p ^ K * p * t := ht
      linear_combination ht'
  choose y hy hy0 using hroot
  have hinj : Function.Injective fun i => al i + e i * p ^ K * y i := by
    intro i j hij
    by_contra hne
    obtain ⟨a, ha⟩ : al i - al j ∣ e i :=
      Finset.dvd_prod_of_mem (fun k => al i - al k) (Finset.mem_erase.2 ⟨Ne.symm hne, Finset.mem_univ _⟩)
    obtain ⟨b, hb⟩ : al j - al i ∣ e j :=
      Finset.dvd_prod_of_mem (fun k => al j - al k) (Finset.mem_erase.2 ⟨hne, Finset.mem_univ _⟩)
    have hij' : al i + e i * p ^ K * y i = al j + e j * p ^ K * y j := hij
    rw [ha, hb] at hij'
    have h1 : (al i - al j) * (1 - (-(a * p ^ K * y i) - b * p ^ K * y j)) = 0 := by
      linear_combination hij'
    have h2 := sub_eq_zero.1 ((mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 fun h => hne (hal h)))
    have h3 : (1 : O) ∈ maximalIdeal O := by
      rw [h2]
      exact sub_mem (neg_mem (Ideal.mul_mem_left _ _ (hy i))) (Ideal.mul_mem_left _ _ (hy j))
    exact (mem_maximalIdeal _).1 h3 isUnit_one
  refine ⟨fun i => al i + e i * p ^ K * y i, ?_, fun i => ?_⟩
  · have hGm : (∏ i, (X - C (al i + e i * p ^ K * y i)) : O[X]).Monic :=
      monic_prod_of_monic _ _ fun i _ => monic_X_sub_C _
    have hGd : (∏ i, (X - C (al i + e i * p ^ K * y i)) : O[X]).natDegree = n := by
      rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C _]
      simp only [natDegree_X_sub_C]
      simp
    refine eq_of_degree_le_of_eval_index_eq Finset.univ hinj.injOn ?_ ?_ ?_ ?_
    · rw [degree_eq_natDegree hP.ne_zero, hdeg]; simp
    · rw [degree_eq_natDegree hP.ne_zero, degree_eq_natDegree hGm.ne_zero, hdeg, hGd]
    · rw [hP.leadingCoeff, hGm.leadingCoeff]
    · intro i _
      rw [hy0 i, eval_prod]
      exact (Finset.prod_eq_zero (Finset.mem_univ i) (by simp)).symm
  · rw [add_sub_cancel_left]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hpm K))
end

open IsLocalRing Matrix Filter UpperTheory.V UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev UpperTheory.V.AlgebraTools UpperTheory.V.Th
open scoped TensorProduct

private theorem eig_dvd {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (F : O) (hF : F ≠ 0) :
    ∃ K : ℕ, ∀ b : O, b - F ∈ maximalIdeal O ^ K → b ∣ F := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨v, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hF hp
  refine ⟨v + 1, fun b hb => ?_⟩
  rw [hp.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hb
  obtain ⟨c, hc⟩ := hb
  have hun : IsUnit ((u : O) + p * c) := by
    by_contra hn
    have h1 : (u : O) + p * c ∈ maximalIdeal O := hn
    have h2 : p * c ∈ maximalIdeal O := Ideal.mul_mem_right _ _ hp.not_isUnit
    have h3 : (u : O) ∈ maximalIdeal O := by simpa using Ideal.sub_mem _ h1 h2
    exact h3 u.isUnit
  have hb' : b = ((u : O) + p * c) * p ^ v := by
    rw [sub_eq_iff_eq_add] at hc
    rw [hc, hu]; ring
  rw [hb', hu, hun.mul_left_dvd]
  exact Dvd.intro_left _ rfl

private theorem eig_fEl {O : Type} [CommRing O] (I : Ideal O) {q n : ℕ} (Nq : Fin q → ℕ)
    (hN : ∀ j, (Nq j : O) - 1 ∈ I) (a b : Fin q → Fin n → O) (h : ∀ j i, a j i - b j i ∈ I) :
    fEl Nq a - fEl (fun _ => 1) b ∈ I := by
  rw [← Ideal.Quotient.eq]
  have h1 : ∀ j, Ideal.Quotient.mk I (Nq j : O) = 1 := fun j => by
    rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]; exact hN j
  have h2 : ∀ j i, Ideal.Quotient.mk I (a j i) = Ideal.Quotient.mk I (b j i) := fun j i =>
    Ideal.Quotient.eq.2 (h j i)
  simp only [fEl, map_prod, map_mul, map_sub, h1, h2, Nat.cast_one, map_one]

private theorem eig_chp {O : Type} [CommRing O] (I : Ideal O) {n : ℕ} (A B : Matrix (Fin n) (Fin n) O)
    (h : ∀ a b, A a b - B a b ∈ I) (k : ℕ) : A.charpoly.coeff k - B.charpoly.coeff k ∈ I := by
  rw [← Ideal.Quotient.eq, ← Polynomial.coeff_map, ← Polynomial.coeff_map, ← Matrix.charpoly_map,
    ← Matrix.charpoly_map]
  have hAB : A.map (Ideal.Quotient.mk I) = B.map (Ideal.Quotient.mk I) := by
    ext a b
    exact Ideal.Quotient.eq.2 (h a b)
  rw [hAB]

theorem UpperTheory.V.Th.Sp.eig :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (y : Pt G0.frame O n) (al : Fin T.q → Fin n → O), (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → y.ρ g = 1) → Th.Eig y T al → ∃ F : O, F ≠ 0 ∧ ∀ᶠ N in atTop, ∃ α : Fin T.q → Fin n → O, (∀ j, (mat y.ρ ((T.h N).p₀ (T.ph N j))).charpoly = ∏ i, (Polynomial.X - Polynomial.C (α j i))) ∧ fEl (T.Nq N) α ∣ F := by
  intro l _ L G0 T n O _ _ _ hc _ y al hP hE
  haveI : IsAdicComplete (maximalIdeal O) O := hc.complete
  have hF : fEl (fun _ => 1) al ≠ 0 := by
    simp only [fEl, Nat.cast_one, one_mul]
    refine Finset.prod_ne_zero_iff.2 fun j _ => Finset.prod_ne_zero_iff.2 fun i _ =>
      Finset.prod_ne_zero_iff.2 fun i' hi' => ?_
    have hne : al j i - al j i' ≠ 0 := fun h0 =>
      (Finset.ne_of_mem_erase hi') ((hE j).1 (sub_eq_zero.1 h0)).symm
    exact mul_ne_zero hne hne
  obtain ⟨K, hK⟩ := eig_dvd _ hF
  refine ⟨_, hF, ?_⟩
  choose K' hK' using fun j => UpperTheory.V.Th.Sp.hens O n (al j) (hE j).1 K
  have hlO : (l : O) ∈ maximalIdeal O := by
    haveI : CharP (ResidueField O) l := hc.char
    rw [← residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero _ l
  filter_upwards [UpperTheory.V.Th.Sp.close l L G0 T n O y hP (Finset.univ.sup K'), eventually_ge_atTop K] with N hN hNK
  have key : ∀ j, ∃ α : Fin n → O, (mat y.ρ ((T.h N).p₀ (T.ph N j))).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C (α i)) ∧ ∀ i, α i - al j i ∈ maximalIdeal O ^ K := by
    intro j
    refine hK' j _ (Matrix.charpoly_monic _) (by rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]) fun k => ?_
    rw [← (hE j).2]
    exact Ideal.pow_le_pow_right (Finset.le_sup (f := K') (Finset.mem_univ j)) (eig_chp _ _ _ (hN j) k)
  choose α h1 h2 using key
  refine ⟨α, h1, hK _ (eig_fEl _ _ (fun j => ?_) _ _ h2)⟩
  obtain ⟨c, hc'⟩ := (T.Nq_mod N j).symm.dvd
  have h3 : (T.Nq N j : O) - 1 = (l : O) ^ N * (c : O) := by
    have := congrArg (Int.cast : ℤ → O) hc'
    simpa using this
  rw [h3]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right hNK (Ideal.pow_mem_pow hlO N))
