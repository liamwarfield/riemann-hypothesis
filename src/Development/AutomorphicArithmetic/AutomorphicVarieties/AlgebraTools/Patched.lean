module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkInd

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ULimKer
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem exists_sum_of_mem_span_smul_top {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
    {n : ℕ} (g : Fin n → R) (x : M) (hx : x ∈ (Ideal.span (Set.range g) • ⊤ : Submodule R M)) :
    ∃ q : Fin n → M, x = ∑ c, g c • q c := by
  refine Submodule.smul_induction_on hx ?_ ?_
  · intro r hr m _
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hr
    refine ⟨fun i => c i • m, ?_⟩
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, mul_comm]
  · rintro x y ⟨q, rfl⟩ ⟨q', rfl⟩
    exact ⟨fun i => q i + q' i, by simp [smul_add, Finset.sum_add_distrib]⟩

theorem UpperTheory.V.AlgebraTools.ULim.mem_smul_top_iff :
    ∀ (R : Type) [CommRing R] (F : Filter ℕ), F ≤ atTop → ∀ (I : ℕ → Ideal R) (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (a : Ideal R), a.FG → Antitone I →
      ∀ p : ∀ i, M i, ULim.mk F I M p ∈ (a • ⊤ : Submodule R (ULim F I M)) ↔
        ∀ j, ∀ᶠ N in F, p N ∈ ((a ⊔ I j) • ⊤ : Submodule R (M N)) := by
  intro R _ F hF I M _ _ a ha hI p
  obtain ⟨n, g, hg⟩ := Submodule.fg_iff_exists_fin_generating_family.1 ha
  have hg' : Ideal.span (Set.range g) = a := hg
  have hga : ∀ c, g c ∈ a := fun c => hg' ▸ Ideal.subset_span ⟨c, rfl⟩
  constructor
  · intro hp j
    rw [← hg'] at hp
    obtain ⟨q, hq⟩ := exists_sum_of_mem_span_smul_top g _ hp
    choose q' hq' using fun c => ULim.mk_surjective F I M (q c)
    have h0 : ULim.mk F I M (p - ∑ c, g c • q' c) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, hq]
      simp only [map_smul, hq', sub_self]
    filter_upwards [ULim.mk_eq_zero.1 h0 j] with N hN
    have h1 : (∑ c, g c • q' c) N ∈ ((a ⊔ I j) • ⊤ : Submodule R (M N)) := by
      rw [Finset.sum_apply]
      exact Submodule.sum_mem _ fun c _ =>
        Submodule.smul_mem_smul (Ideal.mem_sup_left (hga c)) Submodule.mem_top
    have h2 := Submodule.add_mem ((a ⊔ I j) • ⊤ : Submodule R (M N)) (Submodule.smul_mono_left (le_sup_right : I j ≤ a ⊔ I j) hN) h1
    simpa using h2
  · intro hp
    obtain ⟨ν, hν, hP⟩ := exists_diag F hF
      (fun j N => p N ∈ ((a ⊔ I j) • ⊤ : Submodule R (M N))) hp
    have key : ∀ N, ∃ q : Fin n → M N, p N ∈ ((a ⊔ I (ν N)) • ⊤ : Submodule R (M N)) →
        p N - ∑ c, g c • q c ∈ (I (ν N) • ⊤ : Submodule R (M N)) := by
      intro N
      by_cases h : p N ∈ ((a ⊔ I (ν N)) • ⊤ : Submodule R (M N))
      · have h' := h
        rw [Submodule.sup_smul] at h'
        obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 h'
        rw [← hg'] at hy
        obtain ⟨q, hq⟩ := exists_sum_of_mem_span_smul_top g _ hy
        refine ⟨q, fun _ => ?_⟩
        rw [← hq, ← hyz, add_sub_cancel_left]
        exact hz
      · exact ⟨0, fun h' => absurd h' h⟩
    choose q hq using key
    have h0 : ULim.mk F I M (p - ∑ c, g c • fun N => q N c) = 0 := by
      refine ULim.mk_eq_zero.2 fun j => ?_
      filter_upwards [hP, hν.eventually_ge_atTop j] with N hN hj
      have := Submodule.smul_mono_left (hI hj) (hq N (hN _ le_rfl))
      simpa [Finset.sum_apply] using this
    rw [map_sub, sub_eq_zero] at h0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h0, map_sum]
    refine Submodule.sum_mem _ fun c _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem_smul (hga c) Submodule.mem_top
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QRegLim
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.qRegAt_uLim :
    ∀ (R σ : Type) [CommRing R] [Finite σ] (F : Filter ℕ), F ≤ atTop → ∀ (I : ℕ → Ideal R) (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (y : σ → R) (a k : ℕ), Antitone I → a < k →
      (∀ j, ∀ᶠ N in F, QRegAt (M N) y (I j) a) →
      QRegAt (ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ I j) M) y ⊥ a := by
  intro R σ _ _ F hF I M _ _ y a k hI hak hq
  classical
  set Y : Ideal R := Ideal.span (Set.range y) with hY
  have hYfg : Y.FG := ⟨(Set.finite_range y).toFinset, by simp [hY]⟩
  have hK : Antitone (fun j ↦ Y ^ k ⊔ I j) := fun i j hij ↦ sup_le_sup_left (hI hij) _
  have hk1 : Y ^ k ≤ Y ^ (a + 1) := Ideal.pow_le_pow_right (by omega)
  intro c hc
  choose p hp using fun α ↦ ULim.mk_surjective F (fun j ↦ Y ^ k ⊔ I j) M (c α)
  have hsum : ∑ α : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑α • c α =
      ULim.mk F (fun j ↦ Y ^ k ⊔ I j) M
        (fun N ↦ ∑ α : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑α • p α N) := by
    have e : (fun N ↦ ∑ α : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑α • p α N) =
        ∑ α : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑α • p α := by
      ext N
      simp [Finset.sum_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    simp [hp]
  rw [sup_bot_eq, hsum, ULim.mem_smul_top_iff R F hF _ M (Y ^ (a + 1)) hYfg.pow hK] at hc
  intro α
  rw [sup_bot_eq, ← hp α, ULim.mem_smul_top_iff R F hF _ M Y hYfg hK]
  intro j
  filter_upwards [hc j, hq j] with N hN hqN
  have hN' : ∑ β : GlobalTheory.MonoDeg σ a, GlobalTheory.monoVal y ↑β • p β N ∈
      (Y ^ (a + 1) ⊔ I j) • (⊤ : Submodule R (M N)) :=
    Submodule.smul_mono_left (sup_le le_sup_left (sup_le (hk1.trans le_sup_left) le_sup_right)) hN
  exact Submodule.smul_mono_left (sup_le_sup_left le_sup_right Y) (hqN (fun β ↦ p β N) hN' α)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ULimTrans
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.ULim.trans_ker :
    ∀ (R : Type) [CommRing R] (F : Filter ℕ), F ≤ atTop → ∀ (I : ℕ → Ideal R) (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] (a b : Ideal R), a.FG → Antitone I → ∀ h : b ≤ a,
      Function.Surjective (ULim.map F (I := fun j => b ⊔ I j) (I' := fun j => a ⊔ I j) (M := M) (fun _ => sup_le_sup_right h _) fun _ => LinearMap.id) ∧
      LinearMap.ker (ULim.map F (I := fun j => b ⊔ I j) (I' := fun j => a ⊔ I j) (M := M) (fun _ => sup_le_sup_right h _) fun _ => LinearMap.id) = a • ⊤ ∧
      (a • ⊤ : Submodule R (ULim F (fun j => a ⊔ I j) M)) = ⊥ := by
  intro R _ F hF I M _ _ a b ha hI h
  have hI1 : Antitone fun j => b ⊔ I j := fun i j hij => sup_le_sup_left (hI hij) b
  have hI2 : Antitone fun j => a ⊔ I j := fun i j hij => sup_le_sup_left (hI hij) a
  have e1 : ∀ j, a ⊔ (b ⊔ I j) = a ⊔ I j := fun j => by rw [← sup_assoc, sup_eq_left.mpr h]
  have e2 : ∀ j, a ⊔ (a ⊔ I j) = a ⊔ I j := fun j => by rw [← sup_assoc, sup_idem]
  refine ⟨?_, ?_, ?_⟩
  · intro y
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F (fun j => a ⊔ I j) M y
    exact ⟨ULim.mk F (fun j => b ⊔ I j) M p, by rw [ULim.map_mk]; rfl⟩
  · ext x
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F (fun j => b ⊔ I j) M x
    rw [LinearMap.mem_ker, ULim.map_mk, ULim.mk_eq_zero, ULim.mem_smul_top_iff R F hF _ M a ha hI1]
    simp only [LinearMap.id_apply, e1]
  · refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F (fun j => a ⊔ I j) M x
    rw [ULim.mem_smul_top_iff R F hF _ M a ha hI2] at hx
    rw [Submodule.mem_bot, ULim.mk_eq_zero]
    simpa only [e2] using hx
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TowerCompl
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TowerFin
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem tf_mem_smul_top_pi {R : Type} [CommRing R] (J : Ideal R) {r : ℕ} (x : Fin r → R) :
    x ∈ J • (⊤ : Submodule R (Fin r → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx (fun a ha m _ i => ?_) (fun y z hy hz i => ?_)
    · simpa using J.mul_mem_right (m i) ha
    · simpa using J.add_mem (hy i) (hz i)
  · intro hx
    rw [pi_eq_sum_univ x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

private theorem tf_isPrecomplete_pi {R : Type} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    (r : ℕ) : IsPrecomplete I (Fin r → R) := by
  refine ⟨fun f hf => ?_⟩
  have hc : ∀ i, ∃ L : R, ∀ n, f n i ≡ L [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec (I := I) inferInstance (f := fun n => f n i) (fun {m n} hmn => ?_)
    have := (tf_mem_smul_top_pi (I ^ m) _).1 (SModEq.sub_mem.1 (hf hmn)) i
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top]
    simpa using this
  choose L hL using hc
  refine ⟨L, fun n => ?_⟩
  rw [SModEq.sub_mem, tf_mem_smul_top_pi]
  intro i
  have := SModEq.sub_mem.1 (hL i n)
  rw [Ideal.smul_eq_mul, Ideal.mul_top] at this
  simpa using this

private theorem tf_key {R F : Type} [CommRing R] [AddCommGroup F] [Module R F] (a : Ideal R)
    [IsPrecomplete a F] (K : ℕ → Submodule R F) (hK : Antitone K)
    (h1 : ∀ n, (a ^ n • ⊤ : Submodule R F) ≤ K n)
    (h2 : ∀ n, K n ≤ (a ^ n • ⊤ : Submodule R F) ⊔ K (n + 1)) (k : ℕ) (x : F) (hx : x ∈ K k) :
    ∃ y ∈ (a ^ k • ⊤ : Submodule R F), ∀ n, x - y ∈ K n := by
  classical
  have step : ∀ n, ∀ v ∈ K n, ∃ y ∈ (a ^ n • ⊤ : Submodule R F), ∃ w ∈ K (n + 1), y + w = v :=
    fun n v hv => Submodule.mem_sup.1 (h2 n hv)
  choose hd hdm tl htlm hsum using step
  obtain ⟨w, hw0, hwS⟩ : ∃ w : ∀ j, {v : F // v ∈ K (k + j)}, (w 0).1 = x ∧
      ∀ j, (w (j + 1)).1 = tl (k + j) (w j).1 (w j).2 :=
    ⟨fun j => Nat.rec (motive := fun j => {v : F // v ∈ K (k + j)}) ⟨x, hx⟩
      (fun j v => ⟨tl (k + j) v.1 v.2, htlm _ _ _⟩) j, rfl, fun j => rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℕ → F, ∀ j, z j = hd (k + j) (w j).1 (w j).2 := ⟨_, fun _ => rfl⟩
  have hzm : ∀ j, z j ∈ (a ^ (k + j) • ⊤ : Submodule R F) := fun j => by rw [hz]; exact hdm _ _ _
  have hsplit : ∀ j, z j + (w (j + 1)).1 = (w j).1 := fun j => by rw [hz, hwS]; exact hsum _ _ _
  have hpart : ∀ j, x - ∑ i ∈ Finset.range j, z i = (w j).1 := by
    intro j
    induction j with
    | zero => simp [hw0]
    | succ j ih =>
      rw [Finset.sum_range_succ, ← sub_sub, ih, sub_eq_iff_eq_add']
      exact (hsplit j).symm
  have hcau : ∀ {m n : ℕ}, m ≤ n → (∑ i ∈ Finset.range m, z i) ≡ (∑ i ∈ Finset.range n, z i)
      [SMOD (a ^ m • ⊤ : Submodule R F)] := by
    intro m n hmn
    rw [SModEq.sub_mem, ← Finset.sum_range_add_sum_Ico _ hmn]
    have e : ∑ i ∈ Finset.range m, z i - (∑ i ∈ Finset.range m, z i + ∑ i ∈ Finset.Ico m n, z i)
        = -∑ i ∈ Finset.Ico m n, z i := by abel
    rw [e]
    refine Submodule.neg_mem _ (Submodule.sum_mem _ fun i hi => ?_)
    have := (Finset.mem_Ico.1 hi).1
    exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) (hzm i)
  obtain ⟨y, hy⟩ := IsPrecomplete.prec (I := a) inferInstance
    (f := fun n => ∑ i ∈ Finset.range n, z i) hcau
  refine ⟨y, ?_, fun n => ?_⟩
  · have h1' := SModEq.sub_mem.1 (hy k)
    have h2' : ∑ i ∈ Finset.range k, z i ∈ (a ^ k • ⊤ : Submodule R F) :=
      Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega)) (hzm i)
    have := Submodule.sub_mem _ h2' h1'
    simpa using this
  · have h1' := SModEq.sub_mem.1 (hy n)
    have e : x - y = (w n).1 + (∑ i ∈ Finset.range n, z i - y) := by rw [← hpart n]; abel
    rw [e]
    exact Submodule.add_mem _ (hK (Nat.le_add_left n k) (w n).2) (h1 n h1')

theorem UpperTheory.V.AlgebraTools.exists_tower_limit :
    ∀ (R : Type) [CommRing R] (a : Ideal R) [IsAdicComplete a R] (P : ℕ → Type) [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)] (π : ∀ k, P (k + 1) →ₗ[R] P k),
      (∀ k, Function.Surjective (π k)) → (∀ k, LinearMap.ker (π k) = a ^ k • ⊤) → (∀ k, (a ^ k • ⊤ : Submodule R (P k)) = ⊥) →
      Module.Finite R (P 1) →
      ∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M) (q : ∀ k, M →ₗ[R] P k), Module.Finite R M ∧
        (∀ k, Function.Surjective (q k)) ∧ (∀ k, LinearMap.ker (q k) = a ^ k • ⊤) ∧ (∀ k x, π k (q (k + 1) x) = q k x) ∧
        ∀ x : M, (∀ k, q k x = 0) → x = 0 := by
  intro R _ a _ P _ _ π hsurj hker hbot hfin
  classical
  have nak : ∀ {N : Type} [AddCommGroup N] [Module R N] (S : Submodule R N) (j : ℕ),
      (⊤ : Submodule R N) ≤ S ⊔ a • ⊤ → (a ^ j • ⊤ : Submodule R N) = ⊥ → S = ⊤ := by
    intro N _ _ S j hS hj
    have key : ∀ i, (⊤ : Submodule R N) ≤ S ⊔ a ^ i • ⊤ := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        calc (⊤ : Submodule R N) ≤ S ⊔ a • ⊤ := hS
          _ ≤ S ⊔ a • (S ⊔ a ^ i • ⊤) := sup_le_sup_left (Submodule.smul_mono le_rfl ih) _
          _ ≤ S ⊔ a ^ (i + 1) • ⊤ := by
            rw [Submodule.smul_sup, ← Submodule.mul_smul, ← pow_succ']
            exact sup_le le_sup_left (sup_le (Submodule.smul_le_right.trans le_sup_left) le_sup_right)
    have := key j
    rw [hj, sup_bot_eq] at this
    exact top_le_iff.1 this
  have hz : ∀ n (r : R) (v : P n), r ∈ a ^ n → r • v = 0 := fun n r v hr => by
    have := Submodule.smul_mem_smul hr (Submodule.mem_top (x := v))
    rw [hbot n] at this
    simpa using this
  have hP0 : ∀ v : P 0, v = 0 := fun v => by simpa using hz 0 1 v (by simp)
  obtain ⟨r, ψ1, hψ1⟩ := Module.Finite.exists_fin' R (P 1)
  haveI := tf_isPrecomplete_pi a r
  have lift : ∀ n (g : (Fin r → R) →ₗ[R] P n), ∃ h : (Fin r → R) →ₗ[R] P (n + 1), (π n).comp h = g :=
    fun n g => Module.projective_lifting_property (π n) g (hsurj n)
  choose L hL using lift
  obtain ⟨ψ', hψ'0, hψ'S⟩ : ∃ ψ' : ∀ j, (Fin r → R) →ₗ[R] P (j + 1), ψ' 0 = ψ1 ∧
      ∀ j, ψ' (j + 1) = L (j + 1) (ψ' j) :=
    ⟨fun j => Nat.rec (motive := fun j => (Fin r → R) →ₗ[R] P (j + 1)) ψ1
      (fun j g => L (j + 1) g) j, rfl, fun j => rfl⟩
  have hcomp' : ∀ j v, π (j + 1) (ψ' (j + 1) v) = ψ' j v := by
    intro j v
    have h := LinearMap.congr_fun (hL (j + 1) (ψ' j)) v
    rw [hψ'S]
    simpa using h
  have hψ's : ∀ j, Function.Surjective (ψ' j) := by
    intro j
    induction j with
    | zero => rw [hψ'0]; exact hψ1
    | succ j ih =>
      rw [← LinearMap.range_eq_top]
      have hS : (⊤ : Submodule R (P (j + 1 + 1))) ≤ LinearMap.range (ψ' (j + 1)) ⊔ a • ⊤ := by
        intro p _
        obtain ⟨f, hf⟩ := ih (π (j + 1) p)
        have hk : p - ψ' (j + 1) f ∈ LinearMap.ker (π (j + 1)) := by
          rw [LinearMap.mem_ker, map_sub, hcomp', hf, sub_self]
        rw [hker] at hk
        refine Submodule.mem_sup.2 ⟨ψ' (j + 1) f, LinearMap.mem_range_self _ f,
          p - ψ' (j + 1) f, ?_, by abel⟩
        exact Submodule.smul_mono_left (Ideal.pow_le_self (by omega)) hk
      exact nak _ (j + 1 + 1) hS (hbot (j + 1 + 1))
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ∀ n, (Fin r → R) →ₗ[R] P n, ∀ n, ψ n = (π n).comp (ψ' n) :=
    ⟨_, fun _ => rfl⟩
  have hcomp : ∀ n v, π n (ψ (n + 1) v) = ψ n v := by
    intro n v
    simp only [hψ, LinearMap.comp_apply, hcomp']
  have hψs : ∀ n, Function.Surjective (ψ n) := by
    intro n
    rw [hψ, LinearMap.coe_comp]
    exact (hsurj n).comp (hψ's n)
  obtain ⟨Msub, hmem⟩ : ∃ S : Submodule R (∀ k, P k),
      ∀ x, x ∈ S ↔ ∀ k, π k (x (k + 1)) = x k :=
    ⟨{ carrier := {x | ∀ k, π k (x (k + 1)) = x k}
       add_mem' := by
         intro x y hx hy
         simp only [Set.mem_setOf_eq] at hx hy ⊢
         intro k; simp [hx k, hy k]
       zero_mem' := by simp
       smul_mem' := by
         intro c x hx
         simp only [Set.mem_setOf_eq] at hx ⊢
         intro k; simp [hx k] }, fun x => Iff.rfl⟩
  have hφmem : ∀ v, LinearMap.pi (fun k => ψ k) v ∈ Msub :=
    fun v => (hmem _).2 fun k => by simpa using hcomp k v
  obtain ⟨φ, hφ⟩ : ∃ φ : (Fin r → R) →ₗ[R] Msub, ∀ v k, (φ v : ∀ k, P k) k = ψ k v :=
    ⟨LinearMap.codRestrict Msub (LinearMap.pi fun k => ψ k) hφmem, fun v k => rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ∀ k, Msub →ₗ[R] P k, ∀ k x, q k x = (x : ∀ k, P k) k :=
    ⟨fun k => (LinearMap.proj k).comp Msub.subtype, fun k x => rfl⟩
  have hsep : ∀ x : Msub, (∀ k, q k x = 0) → x = 0 := fun x h =>
    Subtype.ext (funext fun k => by simpa [hq] using h k)
  have hK : Antitone (fun n => LinearMap.ker (ψ n)) := antitone_nat_of_succ_le fun n v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [← hcomp, hv, map_zero]
  have h1 : ∀ n, (a ^ n • ⊤ : Submodule R (Fin r → R)) ≤ LinearMap.ker (ψ n) := fun n =>
    Submodule.smul_le.2 fun r hr v _ => by
      rw [LinearMap.mem_ker, map_smul]
      exact hz n r _ hr
  have h2 : ∀ n, LinearMap.ker (ψ n) ≤ (a ^ n • ⊤ : Submodule R (Fin r → R)) ⊔ LinearMap.ker (ψ (n + 1)) := by
    intro n v hv
    rw [LinearMap.mem_ker] at hv
    have hk : ψ (n + 1) v ∈ LinearMap.ker (π n) := by rw [LinearMap.mem_ker, hcomp, hv]
    rw [hker n, ← LinearMap.range_eq_top.2 (hψs (n + 1)), LinearMap.range_eq_map,
      ← Submodule.map_smul''] at hk
    obtain ⟨g, hg, hgv⟩ := Submodule.mem_map.1 hk
    refine Submodule.mem_sup.2 ⟨g, hg, v - g, ?_, by abel⟩
    rw [LinearMap.mem_ker, map_sub, hgv, sub_self]
  have hφs : Function.Surjective φ := by
    intro m
    have hm : ∀ k, π k ((m : ∀ k, P k) (k + 1)) = (m : ∀ k, P k) k := (hmem _).1 m.2
    have step : ∀ n (f : Fin r → R), ψ n f = (m : ∀ k, P k) n →
        ∃ g ∈ (a ^ n • ⊤ : Submodule R (Fin r → R)), ψ (n + 1) (f + g) = (m : ∀ k, P k) (n + 1) := by
      intro n f hf
      obtain ⟨f', hf'⟩ := hψs (n + 1) ((m : ∀ k, P k) (n + 1))
      have hd : f' - f ∈ LinearMap.ker (ψ n) := by
        rw [LinearMap.mem_ker, map_sub, ← hcomp, hf', hm, hf, sub_self]
      obtain ⟨g, hg, h, hh, hgh⟩ := Submodule.mem_sup.1 (h2 n hd)
      refine ⟨g, hg, ?_⟩
      rw [LinearMap.mem_ker] at hh
      have e : f + g = f' - h := by rw [eq_sub_iff_add_eq, add_assoc, hgh]; abel
      rw [e, map_sub, hf', hh, sub_zero]
    choose G hG hGψ using step
    have h0 : ψ 0 0 = (m : ∀ k, P k) 0 := by rw [map_zero]; exact (hP0 _).symm
    obtain ⟨s, hs0, hsS⟩ : ∃ s : ∀ n, {f : Fin r → R // ψ n f = (m : ∀ k, P k) n},
        (s 0).1 = 0 ∧ ∀ n, (s (n + 1)).1 = (s n).1 + G n (s n).1 (s n).2 :=
      ⟨fun n => Nat.rec (motive := fun n => {f : Fin r → R // ψ n f = (m : ∀ k, P k) n}) ⟨0, h0⟩
        (fun n t => ⟨t.1 + G n t.1 t.2, hGψ n t.1 t.2⟩) n, rfl, fun n => rfl⟩
    have hcau : ∀ {m' n : ℕ}, m' ≤ n →
        (s m').1 ≡ (s n).1 [SMOD (a ^ m' • ⊤ : Submodule R (Fin r → R))] := by
      intro m' n hmn
      induction n, hmn using Nat.le_induction with
      | base => exact SModEq.refl _
      | succ n hmn ih =>
        rw [SModEq.sub_mem] at ih ⊢
        rw [hsS, ← sub_sub]
        exact Submodule.sub_mem _ ih
          (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn) (hG _ _ _))
    obtain ⟨Lim, hLim⟩ := IsPrecomplete.prec (I := a) inferInstance (f := fun n => (s n).1) hcau
    refine ⟨Lim, Subtype.ext (funext fun k => ?_)⟩
    rw [hφ]
    have hdk : (s k).1 - Lim ∈ LinearMap.ker (ψ k) := h1 k (SModEq.sub_mem.1 (hLim k))
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hdk
    rw [← hdk]
    exact (s k).2
  refine ⟨Msub, inferInstance, inferInstance, q, Module.Finite.of_surjective φ hφs, ?_, ?_,
    fun k x => by rw [hq, hq]; exact (hmem _).1 x.2 k, hsep⟩
  · intro k p
    obtain ⟨v, hv⟩ := hψs k p
    exact ⟨φ v, by rw [hq, hφ, hv]⟩
  · intro k
    ext x
    constructor
    · intro hx
      rw [LinearMap.mem_ker, hq] at hx
      obtain ⟨v, rfl⟩ := hφs x
      rw [hφ] at hx
      obtain ⟨y, hy, hvy⟩ := tf_key a (fun n => LinearMap.ker (ψ n)) hK h1 h2 k v
        (LinearMap.mem_ker.2 hx)
      have hz0 : φ (v - y) = 0 := hsep _ fun n => by
        rw [hq, hφ]
        exact hvy n
      rw [map_sub, sub_eq_zero] at hz0
      rw [hz0]
      have hmap := Submodule.mem_map_of_mem (f := φ) hy
      rw [Submodule.map_smul''] at hmap
      exact Submodule.smul_mono le_rfl le_top hmap
    · intro hx
      exact (Submodule.smul_le.2 (fun r hr y _ => by
        rw [LinearMap.mem_ker, map_smul]
        exact hz k r _ hr) : (a ^ k • ⊤ : Submodule R Msub) ≤ LinearMap.ker (q k)) hx
end

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem tc_mod (R : Type) [CommRing R] (a : Ideal R) (k : ℕ) (N : Type) [AddCommGroup N]
    [Module R N] (h : (a ^ k • ⊤ : Submodule R N) = ⊥) :
    ∃ _ : Module (AdicCompletion a R) N, ∀ (s : AdicCompletion a R) (r : R),
      AdicCompletion.evalₐ a k s = Ideal.Quotient.mk _ r → ∀ x : N, s • x = r • x := by
  have ht : Module.IsTorsionBySet R N ((a ^ k : Ideal R) : Set R) := fun x b => by
    have hb : (b : R) • x ∈ (a ^ k • ⊤ : Submodule R N) :=
      Submodule.smul_mem_smul b.2 Submodule.mem_top
    rw [h] at hb
    exact (Submodule.mem_bot R).mp hb
  letI iq : Module (R ⧸ a ^ k) N := ht.module
  letI inst : Module (AdicCompletion a R) N :=
    Module.compHom N (AdicCompletion.evalₐ a k).toRingHom
  refine ⟨inst, fun s r hs x => ?_⟩
  show (AdicCompletion.evalₐ a k s) • x = r • x
  rw [hs]
  exact ht.mk_smul r x

private theorem tc_eval (R : Type) [CommRing R] (a : Ideal R) (k : ℕ) (s : AdicCompletion a R) :
    ∃ r : R, AdicCompletion.evalₐ a (k + 1) s = Ideal.Quotient.mk _ r ∧
      AdicCompletion.evalₐ a k s = Ideal.Quotient.mk _ r := by
  obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective a R s
  refine ⟨x (k + 1), AdicCompletion.evalₐ_mk a (k + 1) x, ?_⟩
  rw [AdicCompletion.evalₐ_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  have hc := x.property (Nat.le_succ k)
  rw [SModEq.sub_mem] at hc
  simpa [Ideal.smul_eq_mul, Ideal.mul_top] using hc

private theorem tc_smul {R S : Type} [CommRing R] [CommRing S] [Algebra R S] (a : Ideal R) (k : ℕ)
    (N : Type) [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] (x : N) :
    x ∈ ((a.map (algebraMap R S)) ^ k • ⊤ : Submodule S N) ↔ x ∈ (a ^ k • ⊤ : Submodule R N) := by
  rw [← Ideal.map_pow, ← Submodule.restrictScalars_mem R, Ideal.smul_restrictScalars,
    Submodule.restrictScalars_top]

theorem UpperTheory.V.AlgebraTools.exists_tower_limit_completion :
    ∀ (R : Type) [CommRing R] (a : Ideal R), a.FG → ∀ (P : ℕ → Type) [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)] (π : ∀ k, P (k + 1) →ₗ[R] P k),
      (∀ k, Function.Surjective (π k)) → (∀ k, LinearMap.ker (π k) = a ^ k • ⊤) → (∀ k, (a ^ k • ⊤ : Submodule R (P k)) = ⊥) →
      Module.Finite R (P 1) →
      ∃ (M : Type) (_ : AddCommGroup M) (_ : Module R M) (_ : Module (AdicCompletion a R) M) (_ : IsScalarTower R (AdicCompletion a R) M)
        (q : ∀ k, M →ₗ[R] P k), Module.Finite (AdicCompletion a R) M ∧ (∀ k, Function.Surjective (q k)) ∧
        (∀ k, LinearMap.ker (q k) = a ^ k • ⊤) ∧ (∀ k x, π k (q (k + 1) x) = q k x) ∧
        ∀ x : M, (∀ k, q k x = 0) → x = 0 := by
  intro R _ a ha P _ _ π hπ hker hkill hfin
  haveI : IsAdicComplete (a.map (algebraMap R (AdicCompletion a R))) (AdicCompletion a R) :=
    AdicCompletion.isAdicComplete_self a ha
  choose inst hinst using fun k => tc_mod R a k (P k) (hkill k)
  haveI tow : ∀ k, IsScalarTower R (AdicCompletion a R) (P k) := fun k => ⟨fun r s x => by
    obtain ⟨r₀, h₀⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ a k s)
    have h1 : AdicCompletion.evalₐ a k (r • s) = Ideal.Quotient.mk _ (r * r₀) := by
      rw [map_smul, ← h₀, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul]
    rw [hinst k (r • s) (r * r₀) h1, hinst k s r₀ h₀.symm, mul_smul]⟩
  let π' : ∀ k, P (k + 1) →ₗ[AdicCompletion a R] P k := fun k =>
    { toFun := π k
      map_add' := (π k).map_add
      map_smul' := fun s x => by
        obtain ⟨r, h1, h2⟩ := tc_eval R a k s
        show π k (s • x) = s • π k x
        rw [hinst (k + 1) s r h1, hinst k s r h2, (π k).map_smul] }
  have hker' : ∀ k, LinearMap.ker (π' k) = (a.map (algebraMap R (AdicCompletion a R))) ^ k • ⊤ := by
    intro k
    ext x
    rw [tc_smul (S := AdicCompletion a R) a k (P (k + 1)) x, ← hker k, LinearMap.mem_ker,
      LinearMap.mem_ker]
    all_goals exact Iff.rfl
  have hkill' : ∀ k, ((a.map (algebraMap R (AdicCompletion a R))) ^ k • ⊤ :
      Submodule (AdicCompletion a R) (P k)) = ⊥ := by
    intro k
    rw [eq_bot_iff]
    intro x hx
    rw [tc_smul (S := AdicCompletion a R) a k (P k) x, hkill k] at hx
    exact (Submodule.mem_bot _).mpr ((Submodule.mem_bot _).mp hx)
  have hfin' : Module.Finite (AdicCompletion a R) (P 1) :=
    Module.Finite.of_restrictScalars_finite R _ (P 1)
  obtain ⟨M, _, _, q, hfinM, hsurj, hkerq, hcompat, hsep⟩ :=
    UpperTheory.V.AlgebraTools.exists_tower_limit (AdicCompletion a R) (a.map (algebraMap R (AdicCompletion a R)))
      P π' (fun k => hπ k) hker' hkill' hfin'
  letI : Module R M := Module.compHom M (algebraMap R (AdicCompletion a R))
  haveI : IsScalarTower R (AdicCompletion a R) M := ⟨fun r s m => by
    show (r • s) • m = (algebraMap R (AdicCompletion a R) r) • (s • m)
    rw [Algebra.smul_def, mul_smul]⟩
  refine ⟨M, inferInstance, inferInstance, inferInstance, inferInstance,
    fun k => (q k).restrictScalars R, hfinM, fun k => hsurj k, ?_, fun k x => hcompat k x,
    fun x hx => hsep x hx⟩
  intro k
  ext x
  rw [LinearMap.mem_ker, ← tc_smul (S := AdicCompletion a R) a k M x, ← hkerq k, LinearMap.mem_ker]
  all_goals exact Iff.rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QRegTower
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.isQuasiRegularSeq_of_tower :
    ∀ (R σ : Type) [CommRing R] [Finite σ] (y : σ → R) (M : Type) [AddCommGroup M] [Module R M] (P : ℕ → Type) [∀ i, AddCommGroup (P i)] [∀ i, Module R (P i)] (q : ∀ k, M →ₗ[R] P k),
      (∀ k, Function.Surjective (q k)) → (∀ k, LinearMap.ker (q k) = Ideal.span (Set.range y) ^ k • ⊤) →
      (∀ a k, a < k → QRegAt (P k) y ⊥ a) → GlobalTheory.IsQuasiRegularSeq M y := by
  intro R σ _ _ y M _ _ P _ _ q hs hk hq
  rw [isQuasiRegularSeq_iff_qRegAt]
  intro a c hc α
  simp only [sup_bot_eq] at hc ⊢
  have h := hq a (a + 1) (Nat.lt_succ_self a) (fun β => q (a + 1) (c β)) (by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hk, LinearMap.mem_ker, map_sum] at hc
    simp only [map_smul] at hc
    rw [hc]
    exact zero_mem _) α
  simp only [sup_bot_eq] at h
  have htop : (⊤ : Submodule R (P (a + 1))) = Submodule.map (q (a + 1)) ⊤ := by
    rw [Submodule.map_top, LinearMap.range_eq_top.2 (hs _)]
  rw [htop, ← Submodule.map_smul''] at h
  have h2 : c α ∈ Submodule.comap (q (a + 1))
      (Submodule.map (q (a + 1)) (Ideal.span (Set.range y) • ⊤ : Submodule R M)) := h
  rw [Submodule.comap_map_eq, hk] at h2
  have hle : (Ideal.span (Set.range y) ^ (a + 1) • ⊤ : Submodule R M) ≤ Ideal.span (Set.range y) • ⊤ :=
    Submodule.smul_mono_left (Ideal.pow_le_self (Nat.succ_ne_zero a))
  rwa [sup_eq_left.2 hle] at h2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ULimScal
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.ULim.scal_eq :
    ∀ (R ι : Type) [CommRing R] (F : Filter ι) (I : ℕ → Ideal R) (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)],
      (∀ (r : ι → R) (s : R), (∀ j, ∀ᶠ N in F, ∀ x : M N, (r N - s) • x ∈ (I j • ⊤ : Submodule R (M N))) →
        ∀ x : ULim F I M, ULim.scal F I M r x = s • x) ∧
      (∀ s : R, (∀ j, ∀ᶠ N in F, ∀ x : M N, s • x ∈ (I j • ⊤ : Submodule R (M N))) → ∀ x : ULim F I M, s • x = 0) ∧
      (∀ (M' : ι → Type) [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)] (f : ∀ i, M i →ₗ[R] M' i) (g : ∀ i, M' i →ₗ[R] M i) (r : ι → R), (∀ i x, g i (f i x) = r i • x) →
        ∀ x : ULim F I M, ULim.map F (fun _ => le_rfl) g (ULim.map F (I' := I) (fun _ => le_rfl) f x) = ULim.scal F I M r x) := by
  intro R ι _ F I M _ _
  have hs : ∀ (r : ι → R) (p : ∀ i, M i), ULim.scal F I M r (ULim.mk F I M p) = ULim.mk F I M (fun i => r i • p i) := by
    intro r p
    simp only [ULim.scal, ULim.map_mk, LinearMap.smul_apply, LinearMap.id_apply]
  have hc : ∀ (s : R) (p : ∀ i, M i), s • ULim.mk F I M p = ULim.mk F I M (fun i => s • p i) := by
    intro s p
    rw [← map_smul]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro r s h x
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F I M x
    rw [← sub_eq_zero, hs, hc, ← map_sub, ULim.mk_eq_zero]
    intro j
    filter_upwards [h j] with N hN
    simpa [sub_smul] using hN (p N)
  · intro s h x
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F I M x
    rw [hc, ULim.mk_eq_zero]
    intro j
    filter_upwards [h j] with N hN
    exact hN (p N)
  · intro M' _ _ f g r hfg x
    obtain ⟨p, rfl⟩ := ULim.mk_surjective F I M x
    rw [ULim.map_mk, ULim.map_mk, hs]
    simp only [hfg]
end

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {R : Type} [CommRing R] (S : Type) [CommRing S] [Algebra R S]
  {X X' : Type} [AddCommGroup X] [Module R X] [AddCommGroup X'] [Module R X']

private theorem one_tmul_mem (a : Ideal R) {x : X} (hx : x ∈ (a • ⊤ : Submodule R X)) (s : S) :
    s ⊗ₜ[R] x ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] X)) := by
  refine Submodule.smul_induction_on hx (fun r hr n _ => ?_) (fun x y hx hy => ?_)
  · rw [TensorProduct.tmul_smul, ← algebraMap_smul S r]
    exact Submodule.smul_mem_smul (Ideal.mem_map_of_mem _ hr) Submodule.mem_top
  · rw [TensorProduct.tmul_add]
    exact add_mem hx hy

private theorem kill_tensor {r : R} (h : ∀ x : X, r • x = 0) (z : S ⊗[R] X) :
    algebraMap R S r • z = 0 := by
  induction z using TensorProduct.induction_on with
  | zero => exact smul_zero _
  | tmul s x =>
    rw [algebraMap_smul, ← TensorProduct.tmul_smul, h x, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

private theorem bot_tensor (a : Ideal R) (h : (a • ⊤ : Submodule R X) = ⊥) :
    (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] X)) = ⊥ := by
  rw [eq_bot_iff, Submodule.smul_le]
  intro s hs z hz
  clear hz
  rw [Submodule.mem_bot]
  have key : ∀ t ∈ a, ∀ w : S ⊗[R] X, algebraMap R S t • w = 0 := by
    intro t ht w
    apply kill_tensor S
    intro x
    have hm : t • x ∈ (a • ⊤ : Submodule R X) := Submodule.smul_mem_smul ht Submodule.mem_top
    rw [h] at hm
    exact (Submodule.mem_bot R).mp hm
  simp only [Ideal.map] at hs
  induction hs using Submodule.span_induction generalizing z with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    exact key t ht z
  | zero => exact zero_smul _ _
  | add x y _ _ hx hy => rw [add_smul, hx, hy, add_zero]
  | smul c x _ hx => rw [smul_eq_mul, mul_smul, hx, smul_zero]

private theorem ker_tensor (a : Ideal R) (t : X →ₗ[R] X') (ht : Function.Surjective t)
    (hk : LinearMap.ker t = a • ⊤) (h' : (a • ⊤ : Submodule R X') = ⊥) :
    Function.Surjective (t.baseChange S) ∧
      LinearMap.ker (t.baseChange S) = a.map (algebraMap R S) • ⊤ := by
  refine ⟨?_, ?_⟩
  · rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective S ht
  · have hex := lTensor_exact S (LinearMap.exact_subtype_ker_map t) ht
    ext w
    constructor
    · intro hw
      rw [LinearMap.mem_ker, LinearMap.baseChange_eq_ltensor] at hw
      obtain ⟨v, rfl⟩ := (hex w).mp hw
      clear hw
      induction v using TensorProduct.induction_on with
      | zero => rw [map_zero]; exact zero_mem _
      | tmul s x =>
        rw [LinearMap.lTensor_tmul, Submodule.coe_subtype]
        have hx : (x : X) ∈ (a • ⊤ : Submodule R X) := hk ▸ x.2
        exact one_tmul_mem S a hx s
      | add x y hx hy => rw [map_add]; exact add_mem hx hy
    · intro hw
      have hle : (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] X)) ≤
          LinearMap.ker (t.baseChange S) := by
        rw [Submodule.smul_le]
        intro r hr n _
        rw [LinearMap.mem_ker, LinearMap.map_smul]
        have hb := bot_tensor S a h'
        have hm : r • (t.baseChange S) n ∈ (a.map (algebraMap R S) • ⊤ : Submodule S (S ⊗[R] X')) :=
          Submodule.smul_mem_smul hr Submodule.mem_top
        rw [hb] at hm
        exact (Submodule.mem_bot S).mp hm
      exact hle hw

end SlopeTestRemainingChoices

theorem UpperTheory.V.AlgebraTools.exists_patched_module :
    ∀ (R σ : Type) [CommRing R] [Finite σ] (F : Filter ℕ), F ≤ atTop → ∀ (y : σ → R) (m : Ideal R) (f : R) (M : ℕ → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
      (S : Type) [CommRing S] [Algebra R S] [IsLocalization.Away f S] (𝔶 : Ideal S), 𝔶 = (Ideal.span (Set.range y)).map (algebraMap R S) →
      (∀ a j : ℕ, ∀ᶠ N in F, QRegAt (M N) y (m ^ j) a) →
      ∀ (Y : Type) [AddCommGroup Y] [Module R Y] [Module S Y] [IsScalarTower R S Y]
        (g : ULim F (fun j => Ideal.span (Set.range y) ⊔ m ^ j) M →ₗ[R] Y) [IsLocalizedModule (Submonoid.powers f) g], Module.Finite S Y →
      ∃ (MM : Type) (_ : AddCommGroup MM) (_ : Module S MM) (_ : Module (AdicCompletion 𝔶 S) MM) (_ : IsScalarTower S (AdicCompletion 𝔶 S) MM)
        (q : MM →ₗ[S] Y), Module.Finite (AdicCompletion 𝔶 S) MM ∧ Function.Surjective q ∧ LinearMap.ker q = 𝔶 • ⊤ ∧
        GlobalTheory.IsQuasiRegularSeq MM (fun s => algebraMap R S (y s)) ∧
        ∀ r : R, (∀ k : ℕ, ∃ e : ℕ, ∀ j : ℕ, ∀ᶠ N in F, ∀ x : M N,
            (f ^ e * r) • x ∈ ((Ideal.span (Set.range y) ^ k ⊔ m ^ j) • ⊤ : Submodule R (M N))) →
          ∀ x : MM, algebraMap R S r • x = 0 := by
  intro R σ _ _ F hF y m f M _ _ S _ _ _ 𝔶 h𝔶 hreg Y _ _ _ _ g _ hfin
  classical
  haveI : Module.Flat R S := IsLocalization.flat S (Submonoid.powers f)
  have haFG : (Ideal.span (Set.range y)).FG := Submodule.fg_span (Set.finite_range y)
  have hFG : 𝔶.FG := h𝔶 ▸ haFG.map _
  have anti : Antitone (fun j : ℕ => m ^ j) := fun i j hij => Ideal.pow_le_pow_right hij
  have hle : ∀ k : ℕ, Ideal.span (Set.range y) ^ (k + 1) ≤ Ideal.span (Set.range y) ^ k :=
    fun k => Ideal.pow_le_pow_right (Nat.le_succ k)
  have htk := fun k : ℕ => ULim.trans_ker R F hF (fun j => m ^ j) M
    (Ideal.span (Set.range y) ^ k) (Ideal.span (Set.range y) ^ (k + 1)) haFG.pow anti (hle k)
  have hS := fun k : ℕ => ker_tensor S (Ideal.span (Set.range y) ^ k) _ (htk k).1 (htk k).2.1 (htk k).2.2
  have hB := fun k : ℕ => bot_tensor S (Ideal.span (Set.range y) ^ k) (htk k).2.2
  have hmap : ∀ k : ℕ, (Ideal.span (Set.range y) ^ k).map (algebraMap R S) = 𝔶 ^ k := by
    intro k
    rw [Ideal.map_pow, h𝔶]
  have key : ∀ I : ℕ → Ideal R, I = (fun j => Ideal.span (Set.range y) ⊔ m ^ j) →
      Nonempty (S ⊗[R] ULim F I M ≃ₗ[S] Y) := by
    rintro I rfl
    exact ⟨(IsLocalizedModule.isBaseChange (Submonoid.powers f) S g).equiv⟩
  obtain ⟨e1⟩ := key (fun j => Ideal.span (Set.range y) ^ 1 ⊔ m ^ j) (by funext j; rw [pow_one])
  haveI := hfin
  haveI : Module.Finite S (S ⊗[R] ULim F (fun j => Ideal.span (Set.range y) ^ 1 ⊔ m ^ j) M) :=
    Module.Finite.equiv e1.symm
  obtain ⟨MM, i1, i2, i3, i4, qq, hfinMM, hsurj, hker, -, hzero⟩ :=
    exists_tower_limit_completion S 𝔶 hFG
      (fun k => S ⊗[R] ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M)
      (fun k => LinearMap.baseChange S
        (ULim.map F (fun x => sup_le_sup_right (hle k) ((fun j => m ^ j) x)) fun _ => LinearMap.id))
      (fun k => (hS k).1) (fun k => by rw [(hS k).2, hmap]) (fun k => by rw [← hmap]; exact hB k)
      inferInstance
  refine ⟨MM, i1, i2, i3, i4, e1.toLinearMap ∘ₗ qq 1, hfinMM, e1.surjective.comp (hsurj 1), ?_, ?_, ?_⟩
  · rw [LinearEquiv.ker_comp, hker 1, pow_one]
  · have hspan : Ideal.span (Set.range fun s => algebraMap R S (y s)) = 𝔶 := by
      rw [h𝔶, Ideal.map_span, ← Set.range_comp]
      rfl
    refine isQuasiRegularSeq_of_tower S σ (fun s => algebraMap R S (y s)) MM
      (fun k => S ⊗[R] ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M) qq hsurj
      (fun k => by rw [hker k, hspan]) ?_
    intro b k hbk
    have h1 := qRegAt_uLim R σ F hF (fun j => m ^ j) M y b k anti hbk (fun j => hreg b j)
    haveI : IsLocalizedModule (Submonoid.powers f)
        (TensorProduct.mk R S (ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M) 1) :=
      (isLocalizedModule_iff_isBaseChange (Submonoid.powers f) S _).mpr
        (TensorProduct.isBaseChange R _ S)
    have h2 := (qRegAt_map R S σ y ⊥ b).2 (Submonoid.powers f) _ _
      (TensorProduct.mk R S (ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M) 1) h1
    have h3 := ((qRegAt_map R S σ y ⊥ b).1
      (S ⊗[R] ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M)).mp h2
    rwa [Ideal.map_bot] at h3
  · intro r hr x
    apply hzero (algebraMap R S r • x)
    intro k
    obtain ⟨e, he⟩ := hr k
    have hP : ∀ z : ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M, (f ^ e * r) • z = 0 :=
      (ULim.scal_eq R ℕ F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M).2.1 (f ^ e * r) he
    have hQ : ∀ w : S ⊗[R] ULim F (fun j => Ideal.span (Set.range y) ^ k ⊔ m ^ j) M,
        algebraMap R S (f ^ e * r) • w = 0 := kill_tensor S hP
    have hu := (IsLocalization.Away.algebraMap_isUnit (S := S) f).pow e
    rw [LinearMap.map_smul, ← hu.smul_eq_zero, ← mul_smul, ← map_pow, ← map_mul]
    exact hQ _
