module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.FinCompl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.OrdBasic

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.LocAbs
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PrecompleteOfFinite
open TensorProduct in
private theorem precomplete_of_finite {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] : IsPrecomplete I M := by
  rw [← AdicCompletion.of_surjective_iff]
  intro y
  obtain ⟨z, rfl⟩ := AdicCompletion.ofTensorProduct_surjective_of_finite I M y
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul r x =>
    obtain ⟨c, rfl⟩ := AdicCompletion.of_surjective I R r
    refine ⟨c • x, ?_⟩
    rw [AdicCompletion.ofTensorProduct_tmul, map_smul]
    exact (algebraMap_smul (AdicCompletion I R) c (AdicCompletion.of I M x)).symm
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a + b, by rw [map_add (f := _), map_add (f := _), ha, hb]⟩

open Polynomial in
private theorem lift_idem {T : Type} [CommRing T] (I : Ideal T) [HenselianRing T I]
    (f : T ⧸ I) (hf : IsIdempotentElem f) :
    ∃ e : T, IsIdempotentElem e ∧ Ideal.Quotient.mk I e = f := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective f
  have hm : (X ^ 2 - X : T[X]).Monic := by
    nontriviality T
    apply monic_X_pow_sub
    simp
  have hf' : Ideal.Quotient.mk I a * Ideal.Quotient.mk I a = Ideal.Quotient.mk I a := hf
  obtain ⟨e, he, hea⟩ := HenselianRing.is_henselian (I := I) (X ^ 2 - X : T[X]) hm a
    (by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      simp only [eval_sub, eval_pow, eval_X, map_sub, pow_two, map_mul, eval_mul]
      rw [hf', sub_self])
    (by
      have h : eval a (derivative (X ^ 2 - X : T[X])) = 2 * a - 1 := by
        simp
        ring
      rw [h, map_sub, map_mul, map_one, map_ofNat]
      refine IsUnit.of_mul_eq_one (2 * Ideal.Quotient.mk I a - 1) ?_
      linear_combination 4 * hf')
  refine ⟨e, ?_, Ideal.Quotient.eq.mpr hea⟩
  have : e ^ 2 - e = 0 := by simpa using he
  show e * e = e
  linear_combination this

private theorem artin_idem {A : Type} [CommRing A] [IsArtinianRing A] (J : Ideal A) :
    ∃ (e : A) (n : ℕ), IsIdempotentElem e ∧ 1 - e ∈ J ∧ ∀ x ∈ J, x ^ n * e = 0 := by
  obtain ⟨n, hn⟩ := IsArtinian.monotone_stabilizes (R := A) (M := A)
    ⟨fun n => OrderDual.toDual (J ^ n), fun _ _ h => Ideal.pow_le_pow_right h⟩
  have h1 : J ^ n = J ^ (n + 1) := hn (n + 1) (by omega)
  have h2 : J ^ n = J ^ (n + n) := hn (n + n) (by omega)
  have hid : IsIdempotentElem (J ^ n) := by
    show J ^ n * J ^ n = J ^ n
    rw [← pow_add, ← h2]
  obtain ⟨f, hf, hJ⟩ := (Ideal.isIdempotentElem_iff_of_fg _ (IsNoetherian.noetherian _)).mp hid
  refine ⟨1 - f, n, hf.one_sub, ?_, ?_⟩
  · have : f ∈ J ^ (n + 1) := by
      rw [← h1, hJ]
      exact Submodule.mem_span_singleton_self f
    simpa using Ideal.pow_le_self (by omega) this
  · intro x hx
    have : x ^ n ∈ J ^ n := Ideal.pow_mem_pow hx n
    rw [hJ] at this
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
    have hf' : f * f = f := hf
    rw [← hc, smul_eq_mul]
    linear_combination (-c) * hf'

private theorem exists_scalar {Λ T : Type} [CommRing Λ] [CommRing T] [Algebra Λ T]
    {ι : Type} (t : ι → T) (a : ι → Λ) (h : Algebra.adjoin Λ (Set.range t) = ⊤) (J : Ideal T)
    (hJ : ∀ i, t i - algebraMap Λ T (a i) ∈ J) (s : T) :
    ∃ c : Λ, s - algebraMap Λ T c ∈ J := by
  have hs : s ∈ Algebra.adjoin Λ (Set.range t) := h ▸ Algebra.mem_top
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact ⟨a i, hJ i⟩
  | algebraMap r => exact ⟨r, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    refine ⟨c + d, ?_⟩
    have := J.add_mem hc hd
    convert this using 1
    rw [map_add (f := _)]; ring
  | mul x y _ _ hx hy =>
    obtain ⟨c, hc⟩ := hx
    obtain ⟨d, hd⟩ := hy
    refine ⟨c * d, ?_⟩
    have := J.add_mem (J.mul_mem_right y hc) (J.mul_mem_left (algebraMap Λ T c) hd)
    convert this using 1
    rw [map_mul]; ring

private theorem maximal_of_scalar {Λ T : Type} [CommRing Λ] [IsLocalRing Λ] [CommRing T]
    [Algebra Λ T] (J : Ideal T) (hne : J ≠ ⊤)
    (hm : Ideal.map (algebraMap Λ T) (IsLocalRing.maximalIdeal Λ) ≤ J)
    (hs : ∀ s : T, ∃ c : Λ, s - algebraMap Λ T c ∈ J) : J.IsMaximal := by
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h => hne ((Ideal.eq_top_iff_one J).mpr h), fun K x hJK hxJ hxK => ?_⟩
  obtain ⟨c, hc⟩ := hs x
  by_cases hu : IsUnit c
  · have h1 : algebraMap Λ T c ∈ K := by
      have := K.sub_mem hxK (hJK hc)
      simpa using this
    exact (Ideal.eq_top_iff_one K).mp (K.eq_top_of_isUnit_mem h1 (hu.map _))
  · exfalso
    have h1 : algebraMap Λ T c ∈ J := hm (Ideal.mem_map_of_mem _ hu)
    have := J.add_mem hc h1
    exact hxJ (by simpa using this)

theorem UpperTheory.Reformulated.B.Qe2.locAbs :
    ∀ (Λ T : Type) [inst : CommRing Λ] [inst_1 : IsLocalRing Λ] [IsNoetherianRing Λ]
    [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ] [inst_4 : CommRing T] [inst_5 : Algebra Λ T] [Module.Finite Λ T]
    (ι : Type) (t : ι → T) (a : ι → Λ),
    Algebra.adjoin Λ (Set.range t) = ⊤ →
      ∃ (e : T),
        IsIdempotentElem e ∧
          (∀ (i : ι),
              ∃ (n : ℕ),
                (t i - (Algebra.algebraMap Λ T : Λ → T) (a i)) ^ n * e ∈
                  Ideal.map (Algebra.algebraMap Λ T) (IsLocalRing.maximalIdeal Λ)) ∧
            (1 : T) - e ∈
                Ideal.map (Algebra.algebraMap Λ T) (IsLocalRing.maximalIdeal Λ) ⊔
                  Ideal.span (Set.range fun (i : ι) ↦ t i - (Algebra.algebraMap Λ T : Λ → T) (a i)) ∧
              (∀ (s : T),
                  ∃ (c : Λ),
                    s - (Algebra.algebraMap Λ T : Λ → T) c ∈
                      Ideal.map (Algebra.algebraMap Λ T) (IsLocalRing.maximalIdeal Λ) ⊔
                        Ideal.span (Set.range fun (i : ι) ↦ t i - (Algebra.algebraMap Λ T : Λ → T) (a i))) ∧
                (e ≠ (0 : T) →
                  (Ideal.map (Algebra.algebraMap Λ T) (IsLocalRing.maximalIdeal Λ) ⊔
                      Ideal.span (Set.range fun (i : ι) ↦ t i - (Algebra.algebraMap Λ T : Λ → T) (a i))).IsMaximal) := by
  intro Λ T _ _ _ _ _ _ _ ι t a h
  set I : Ideal T := Ideal.map (algebraMap Λ T) (IsLocalRing.maximalIdeal Λ) with hI
  set J : Ideal T := I ⊔ Ideal.span (Set.range fun i : ι ↦ t i - algebraMap Λ T (a i)) with hJ
  have hmem : ∀ i, t i - algebraMap Λ T (a i) ∈ J := fun i =>
    Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩)
  have hs := exists_scalar t a h J hmem
  by_cases htop : J = ⊤
  · exact ⟨0, IsIdempotentElem.zero, fun i => ⟨0, by simp⟩, by simp [htop], hs,
      fun h0 => absurd rfl h0⟩
  have hmax : J.IsMaximal := maximal_of_scalar J htop le_sup_left hs
  haveI : IsPrecomplete (IsLocalRing.maximalIdeal Λ) T := precomplete_of_finite _ T
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal Λ) T := {}
  haveI : IsAdicComplete I T := (IsAdicComplete.map_algebraMap_iff _ _).mpr this
  haveI : IsArtinianRing (T ⧸ I) := by
    letI : Field (Λ ⧸ IsLocalRing.maximalIdeal Λ) := Ideal.Quotient.field _
    haveI : Module.Finite (Λ ⧸ IsLocalRing.maximalIdeal Λ) (T ⧸ I) :=
      Module.Finite.of_restrictScalars_finite Λ _ _
    exact IsArtinianRing.of_finite (Λ ⧸ IsLocalRing.maximalIdeal Λ) (T ⧸ I)
  obtain ⟨f, n, hf, hfJ, hfn⟩ := artin_idem (J.map (Ideal.Quotient.mk I))
  obtain ⟨e, he, rfl⟩ := lift_idem I f hf
  refine ⟨e, he, fun i => ⟨n, ?_⟩, ?_, hs, fun _ => hmax⟩
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow]
    exact hfn _ (Ideal.mem_map_of_mem _ (hmem i))
  · have h1 : Ideal.Quotient.mk I (1 - e) ∈ J.map (Ideal.Quotient.mk I) := by
      rwa [map_sub, map_one]
    have h2 := Ideal.mem_quotient_iff_mem (I := I) (J := J) le_sup_left (x := 1 - e)
    exact h2.mp h1
end

open IsLocalRing

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.locAbs :
    ∀ (Λ T : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [CommRing T] [Algebra Λ T] [Module.Finite Λ T] (ι : Type) (t : ι → T) (a : ι → Λ), Algebra.adjoin Λ (Set.range t) = ⊤ → ∃ e : T, IsIdempotentElem e ∧ (∀ i, ∃ n : ℕ, (t i - algebraMap Λ T (a i)) ^ n * e ∈ (maximalIdeal Λ).map (algebraMap Λ T)) ∧ 1 - e ∈ (maximalIdeal Λ).map (algebraMap Λ T) ⊔ Ideal.span (Set.range fun i => t i - algebraMap Λ T (a i)) ∧ (∀ s : T, ∃ c : Λ, s - algebraMap Λ T c ∈ (maximalIdeal Λ).map (algebraMap Λ T) ⊔ Ideal.span (Set.range fun i => t i - algebraMap Λ T (a i))) ∧ (e ≠ 0 → ((maximalIdeal Λ).map (algebraMap Λ T) ⊔ Ideal.span (Set.range fun i => t i - algebraMap Λ T (a i))).IsMaximal) :=
  _root_.UpperTheory.Reformulated.B.Qe2.locAbs
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HidaCompleteRings.EigOfQuot
open UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite TensorProduct

private theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.common_ker_of_nilpotent
    {K Y ι : Type*} [Field K] [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    (T : ι → Module.End K Y) (hc : ∀ i j, Commute (T i) (T j)) (U : Submodule K Y) :
    U ≠ ⊥ → (∀ i, ∀ y ∈ U, T i y ∈ U) → (∀ i, ∀ y ∈ U, ∃ n : ℕ, (T i ^ n) y = 0) →
      ∃ y : Y, y ≠ 0 ∧ ∀ i, T i y = 0 := by
  suffices h : ∀ d : ℕ, ∀ V : Submodule K Y, Module.finrank K V = d → V ≠ ⊥ →
      (∀ i, ∀ y ∈ V, T i y ∈ V) → (∀ i, ∀ y ∈ V, ∃ n : ℕ, (T i ^ n) y = 0) →
      ∃ y : Y, y ≠ 0 ∧ ∀ i, T i y = 0 from h _ U rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V hd hV hinv hnil
  by_cases hall : ∀ i, ∀ y ∈ V, T i y = 0
  · obtain ⟨y, hyV, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
    exact ⟨y, hy0, fun i => hall i y hyV⟩
  push_neg at hall
  obtain ⟨i, z, hzV, hz⟩ := hall
  have hpowmem : ∀ k : ℕ, (T i ^ k) z ∈ V := by
    intro k
    induction k with
    | zero => simpa using hzV
    | succ k ihk =>
      rw [pow_succ', Module.End.mul_apply]
      exact hinv i _ ihk
  let W : Submodule K Y := V ⊓ LinearMap.ker (T i)
  have hWle : W ≤ V := inf_le_left
  have hWlt : W < V := by
    refine lt_of_le_of_ne hWle ?_
    intro hWV
    have : z ∈ W := hWV ▸ hzV
    exact hz (LinearMap.mem_ker.mp (Submodule.mem_inf.mp this).2)
  have hWne : W ≠ ⊥ := by
    classical
    have hex : ∃ n : ℕ, (T i ^ n) z = 0 := hnil i z hzV
    have hz0 : z ≠ 0 := fun h0 => hz (by rw [h0, map_zero])
    have hm0 : Nat.find hex ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [h0, pow_zero, Module.End.one_apply] at this
      exact hz0 this
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    have hspec := Nat.find_spec hex
    rw [hm] at hspec
    have hmin : (T i ^ m) z ≠ 0 := Nat.find_min hex (by omega)
    rw [Submodule.ne_bot_iff]
    refine ⟨(T i ^ m) z, Submodule.mem_inf.mpr ⟨hpowmem m, ?_⟩, hmin⟩
    rw [LinearMap.mem_ker, ← Module.End.mul_apply, ← pow_succ']
    exact hspec
  have hWinv : ∀ j, ∀ y ∈ W, T j y ∈ W := by
    intro j y hy
    obtain ⟨hyV, hyk⟩ := Submodule.mem_inf.mp hy
    refine Submodule.mem_inf.mpr ⟨hinv j y hyV, ?_⟩
    rw [LinearMap.mem_ker] at hyk ⊢
    rw [← Module.End.mul_apply, (hc i j).eq, Module.End.mul_apply, hyk, map_zero]
  have hWnil : ∀ j, ∀ y ∈ W, ∃ n : ℕ, (T j ^ n) y = 0 :=
    fun j y hy => hnil j y (hWle hy)
  exact ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hWlt) W rfl hWne hWinv hWnil

private theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.common_ker_of_quot
    {K Y Z ι : Type*} [Field K] [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y]
    [AddCommGroup Z] [Module K Z]
    (T : ι → Module.End K Y) (hc : ∀ i j, Commute (T i) (T j)) (φ : Y →ₗ[K] Z)
    (hφ : ∀ i y, φ (T i y) = 0) (U : Submodule K Y) :
    (∃ u ∈ U, φ u ≠ 0) → (∀ i, ∀ y ∈ U, T i y ∈ U) → ∃ y : Y, y ≠ 0 ∧ ∀ i, T i y = 0 := by
  intro hu hinv
  suffices h : ∀ d : ℕ, ∀ V : Submodule K Y, Module.finrank K V = d → (∃ u ∈ V, φ u ≠ 0) →
      (∀ i, ∀ y ∈ V, T i y ∈ V) → ∃ y : Y, y ≠ 0 ∧ ∀ i, T i y = 0 from h _ U rfl hu hinv
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro V hd hV hinv
  obtain ⟨u, huV, hu⟩ := hV
  have hVne : V ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    exact ⟨u, huV, fun h0 => hu (by rw [h0, map_zero])⟩
  by_cases hall : ∀ i, ∀ y ∈ V, ∃ n : ℕ, (T i ^ n) y = 0
  · exact UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.common_ker_of_nilpotent T hc V hVne hinv hall
  push_neg at hall
  obtain ⟨i, z, hzV, hz⟩ := hall
  let f : Module.End K V := (T i).restrict (hinv i)
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp (LinearMap.eventually_codisjoint_ker_pow_range_pow f)
  have hcod := hn (n + 1) (by omega)
  have hfpow : ∀ (k : ℕ) (w : V), ((f ^ k) w : Y) = (T i ^ k) (w : Y) := by
    intro k w
    induction k with
    | zero => simp
    | succ k ihk =>
      rw [pow_succ', Module.End.mul_apply, pow_succ', Module.End.mul_apply, ← ihk]
      rfl
  have hmem : (⟨u, huV⟩ : V) ∈ LinearMap.ker (f ^ (n + 1)) ⊔ LinearMap.range (f ^ (n + 1)) := by
    rw [codisjoint_iff.mp hcod]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨c, rfl⟩ := LinearMap.mem_range.mp hb
  have hφb : φ (((f ^ (n + 1)) c : V) : Y) = 0 := by
    rw [hfpow, pow_succ', Module.End.mul_apply, hφ]
  have hab' : (a : Y) + (((f ^ (n + 1)) c : V) : Y) = u := by
    have := congrArg Subtype.val hab
    simpa using this
  have hφa : φ (a : Y) ≠ 0 := by
    have h2 := congrArg φ hab'
    rw [map_add (f := _), hφb, add_zero] at h2
    rw [h2]
    exact hu
  have haker : (T i ^ (n + 1)) (a : Y) = 0 := by
    rw [← hfpow]
    rw [LinearMap.mem_ker.mp ha]
    rfl
  let W : Submodule K Y := V ⊓ LinearMap.ker (T i ^ (n + 1))
  have hWle : W ≤ V := inf_le_left
  have hWlt : W < V := by
    refine lt_of_le_of_ne hWle ?_
    intro hWV
    have : z ∈ W := hWV ▸ hzV
    exact hz (n + 1) (LinearMap.mem_ker.mp (Submodule.mem_inf.mp this).2)
  have hWinv : ∀ j, ∀ y ∈ W, T j y ∈ W := by
    intro j y hy
    obtain ⟨hyV, hyk⟩ := Submodule.mem_inf.mp hy
    refine Submodule.mem_inf.mpr ⟨hinv j y hyV, ?_⟩
    rw [LinearMap.mem_ker] at hyk ⊢
    rw [← Module.End.mul_apply, ((hc i j).pow_left (n + 1)).eq, Module.End.mul_apply, hyk,
      map_zero]
  have hWu : ∃ w ∈ W, φ w ≠ 0 :=
    ⟨(a : Y), Submodule.mem_inf.mpr ⟨a.2, LinearMap.mem_ker.mpr haker⟩, hφa⟩
  exact ih _ (hd ▸ Submodule.finrank_lt_finrank_of_lt hWlt) W rfl hWu hWinv

theorem UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.eigOfQuot :
    ∀ {K Y Z ι : Type*} [Field K] [AddCommGroup Y] [Module K Y] [FiniteDimensional K Y] [AddCommGroup Z] [Module K Z] (A : ι → Module.End K Y), (∀ i j, Commute (A i) (A j)) → ∀ (x : ι → K) (φ : Y →ₗ[K] Z), φ ≠ 0 → (∀ i y, φ (A i y) = x i • φ y) → ∃ y : Y, y ≠ 0 ∧ ∀ i, A i y = x i • y := by
  intro K Y Z ι _ _ _ _ _ _ A hA x φ hφ0 hφ
  let T : ι → Module.End K Y := fun i => A i - x i • (1 : Module.End K Y)
  have hT : ∀ i y, T i y = A i y - x i • y := by
    intro i y
    simp [T]
  have hc : ∀ i j, Commute (T i) (T j) := by
    intro i j
    exact ((hA i j).sub_right ((Commute.one_right (A i)).smul_right (x j))).sub_left
      (((Commute.one_left (A j)).smul_left (x i)).sub_right
        (((Commute.one_left 1).smul_left (x i)).smul_right (x j)))
  have hφT : ∀ i y, φ (T i y) = 0 := by
    intro i y
    rw [hT, map_sub, map_smul, hφ, sub_self]
  have hu : ∃ u ∈ (⊤ : Submodule K Y), φ u ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hφ0 (LinearMap.ext fun y => by simpa using hno y Submodule.mem_top)
  obtain ⟨y, hy0, hy⟩ := UpperTheory.V.AlgebraTools.AnnihilatorQuotientFinite.common_ker_of_quot T hc φ hφT ⊤ hu
    (fun _ _ _ => Submodule.mem_top)
  refine ⟨y, hy0, fun i => ?_⟩
  have := hy i
  rw [hT, sub_eq_zero] at this
  exact this
end
