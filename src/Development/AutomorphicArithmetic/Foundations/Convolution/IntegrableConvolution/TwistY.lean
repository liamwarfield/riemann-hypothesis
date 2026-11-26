module

public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwTrace
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistPerm
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.RestScalar
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ZBasic
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc
public import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.TwistYA

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.JointEx
section -- merged from Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.JointNe
open GroundTheory.Automorphic UpperTheory.ConvolutionTheory.C
open scoped InnerProductSpace

namespace UpperTheory.ConvolutionTheory.L1

private lemma proj_comm {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Z : Submodule ℂ H) [Z.HasOrthogonalProjection] (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (hZ : ∀ z ∈ Z, T z ∈ Z) (x : H) : Z.starProjection (T x) = T (Z.starProjection x) := by
  have hp : Z.starProjection x ∈ Z := Submodule.starProjection_apply_mem Z x
  apply Submodule.eq_starProjection_of_mem_orthogonal (hZ _ hp)
  rw [Submodule.mem_orthogonal]
  intro z hz
  have hxo : x - Z.starProjection x ∈ Zᗮ := Submodule.sub_starProjection_mem_orthogonal x
  have hsym : ⟪z, T (x - Z.starProjection x)⟫_ℂ = ⟪T z, x - Z.starProjection x⟫_ℂ := by
    have := ContinuousLinearMap.adjoint_inner_left T (x - Z.starProjection x) z
    rw [← this, ← ContinuousLinearMap.star_eq_adjoint, hT.star_eq]
  rw [← map_sub, hsym]
  exact (Submodule.mem_orthogonal _ _).1 hxo _ (hZ z hz)

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.jointNe :
    UpperTheory.ConvolutionTheory.L1.JointNe := by
  intro Γ G H _ _ _ _ _ _ π V m ι E A U h i y hy
  obtain ⟨hcl, hinv, hirr⟩ := UpperTheory.ConvolutionTheory.L1.cutIrr Γ G H π V m ι E A U h
  have hmemVE : ∀ w, w ∈ eigIn V E 1 ↔ w ∈ V ∧ E w = w := by
    intro w
    simp [eigIn, Module.End.mem_eigenspace_iff, Submodule.mem_inf]
  have hmemZ : ∀ (k : Fin (m + 1)) w, w ∈ eigIn (eigIn V E 1) (A k) y ↔
      w ∈ eigIn V E 1 ∧ A k w = (y : ℂ) • w := by
    intro k w
    simp only [eigIn, Submodule.mem_inf, Module.End.mem_eigenspace_iff]
    rfl
  have hsa : ∀ k, IsSelfAdjoint (A k) := fun k =>
    (ContinuousLinearMap.nonneg_iff_isPositive.1 (h.A_pos k)).isSelfAdjoint
  have hAVE : ∀ j, ∀ w ∈ eigIn V E 1, A j w ∈ eigIn V E 1 := by
    intro j w hw
    obtain ⟨hwV, hwE⟩ := (hmemVE w).1 hw
    refine (hmemVE _).2 ⟨h.A_mem j w hwV, ?_⟩
    rw [← h.A_E, hwE]

  have hstep : ∀ j, eigIn (eigIn V E 1) (A j) y ≠ ⊥ → eigIn (eigIn V E 1) (A (j + 1)) y ≠ ⊥ := by
    intro j hj
    obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hj
    obtain ⟨hvE, hvA⟩ := (hmemZ j v).1 hv
    obtain ⟨hvV, hvE'⟩ := (hmemVE v).1 hvE
    have hvm : v ∈ V.map (U : H →ₗ[ℂ] H) := by rw [h.U_mem]; exact hvV
    obtain ⟨u, hu, rfl⟩ := hvm
    have hU : ∀ a b : H, U a = U b → a = b := fun a b hab => U.injective hab
    refine (Submodule.ne_bot_iff _).2 ⟨u, (hmemZ _ u).2 ⟨(hmemVE u).2 ⟨hu, ?_⟩, ?_⟩, ?_⟩
    · apply hU
      rw [h.U_E]
      exact hvE'
    · apply hU
      rw [h.U_A, map_smul]
      exact hvA
    · rintro rfl
      exact hv0 (by simp)
  have hall : ∀ j, eigIn (eigIn V E 1) (A j) y ≠ ⊥ := by
    have ht : ∀ t : Fin (m + 1), eigIn (eigIn V E 1) (A (i + t)) y ≠ ⊥ := by
      intro t
      induction t using Fin.induction with
      | zero => simpa using hy
      | succ t ih =>
        rw [← Fin.coeSucc_eq_succ, ← add_assoc]
        exact hstep _ ih
    intro j
    have := ht (j - i)
    rwa [add_sub_cancel] at this

  have hS : ∀ S : Finset (Fin (m + 1)), ∃ w ∈ eigIn V E 1, w ≠ 0 ∧ ∀ j ∈ S, A j w = (y : ℂ) • w := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      have hne : eigIn V E 1 ≠ ⊥ := by
        intro hb
        obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 (hall i)
        have := ((hmemZ i v).1 hv).1
        rw [hb] at this
        exact hv0 (by simpa using this)
      obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
      exact ⟨v, hv, hv0, by simp⟩
    | insert k S hk ih =>
      obtain ⟨w₀, hw₀, hw₀0, hw₀A⟩ := ih
      by_contra hno
      have hno' : ∀ w ∈ eigIn V E 1, (∀ j ∈ S, A j w = (y : ℂ) • w) → A k w = (y : ℂ) • w → w = 0 := by
        intro w hw hwS hwk
        by_contra hw0
        exact hno ⟨w, hw, hw0, fun j hj => by
          rcases Finset.mem_insert.1 hj with rfl | hj
          · exact hwk
          · exact hwS j hj⟩
      set Z := eigIn (eigIn V E 1) (A k) y with hZdef
      have hZcl : IsClosed (Z : Set H) := by
        have h2 : IsClosed {w : H | A k w = (y : ℂ) • w} :=
          isClosed_eq (A k).continuous (continuous_const_smul _)
        have : (Z : Set H) = (eigIn V E 1 : Set H) ∩ {w : H | A k w = (y : ℂ) • w} := by
          ext w
          exact hmemZ k w
        rw [this]
        exact hcl.inter h2
      haveI : CompleteSpace Z := hZcl.completeSpace_coe
      have hZA : ∀ j, ∀ z ∈ Z, A j z ∈ Z := by
        intro j z hz
        obtain ⟨hzVE, hzA⟩ := (hmemZ k z).1 hz
        refine (hmemZ k _).2 ⟨hAVE j z hzVE, ?_⟩
        rw [h.A_A, hzA, map_smul]
      have hZπ : ∀ j, j ≠ k → ∀ g, ∀ z ∈ Z, π (ι j g) z ∈ Z := by
        intro j hj g z hz
        obtain ⟨hzVE, hzA⟩ := (hmemZ k z).1 hz
        refine (hmemZ k _).2 ⟨hinv j g z hzVE, ?_⟩
        rw [h.A_ι k j (Ne.symm hj), hzA, map_smul]

      have hNo : ∀ w ∈ eigIn V E 1, (∀ j ∈ S, A j w = (y : ℂ) • w) → w ∈ Zᗮ := by
        intro w hw hwS
        rw [← Submodule.starProjection_apply_eq_zero_iff]
        have hp : Z.starProjection w ∈ Z := Submodule.starProjection_apply_mem Z w
        obtain ⟨hpVE, hpA⟩ := (hmemZ k _).1 hp
        refine hno' _ hpVE (fun j hj => ?_) hpA
        rw [← proj_comm Z (A j) (hsa j) (hZA j), hwS j hj, map_smul]
      let M : Submodule ℂ H :=
        { carrier := {w | w ∈ eigIn V E 1 ∧ ∀ g, π (ι k g) w ∈ Zᗮ}
          add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun g => by
            rw [map_add (f := _)]; exact Submodule.add_mem _ (ha.2 g) (hb.2 g)⟩
          zero_mem' := ⟨Submodule.zero_mem _, fun g => by
            rw [map_zero]; exact Submodule.zero_mem _⟩
          smul_mem' := fun c a ha => ⟨Submodule.smul_mem _ c ha.1, fun g => by
            rw [map_smul]; exact Submodule.smul_mem _ c (ha.2 g)⟩ }
      have hMmem : ∀ w, w ∈ M ↔ w ∈ eigIn V E 1 ∧ ∀ g, π (ι k g) w ∈ Zᗮ := fun w => Iff.rfl
      have hMle : M ≤ eigIn V E 1 := fun w hw => hw.1
      have hMcl : IsClosed (M : Set H) := by
        have : (M : Set H) = (eigIn V E 1 : Set H) ∩ ⋂ g, (π (ι k g)) ⁻¹' (Zᗮ : Set H) := by
          ext w
          simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
          exact hMmem w
        rw [this]
        exact hcl.inter (isClosed_iInter fun g =>
          (Submodule.isClosed_orthogonal Z).preimage (π (ι k g)).continuous)
      have hMinv : ∀ j g, ∀ v ∈ M, π (ι j g) v ∈ M := by
        intro j g v hv
        refine (hMmem _).2 ⟨hinv j g v hv.1, fun g' => ?_⟩
        by_cases hjk : j = k
        · subst hjk
          rw [← π.map_mul_apply, ← map_mul]
          exact hv.2 _
        · rw [← π.map_mul_apply, ((h.ι_comm k j (Ne.symm hjk)) g' g).eq, π.map_mul_apply]
          rw [Submodule.mem_orthogonal]
          intro z hz
          rw [π.inner_map_right, ← map_inv]
          exact (Submodule.mem_orthogonal _ _).1 (hv.2 g') _ (hZπ j hjk _ z hz)
      have hw₀M : w₀ ∈ M := by
        refine (hMmem _).2 ⟨hw₀, fun g => hNo _ (hinv k g w₀ hw₀) fun j hj => ?_⟩
        have hjk : j ≠ k := fun e => hk (e ▸ hj)
        rw [h.A_ι j k hjk, hw₀A j hj, map_smul]
      have hMtop : M = eigIn V E 1 := by
        rcases hirr M hMle hMcl hMinv with hb | he
        · exfalso
          rw [hb] at hw₀M
          exact hw₀0 (by simpa using hw₀M)
        · exact he
      obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).1 (hall k)
      have hzM : z ∈ M := by
        rw [hMtop]
        exact ((hmemZ k z).1 hz).1
      have hzo := hzM.2 1
      rw [map_one, π.map_one_apply] at hzo
      have := (Submodule.mem_orthogonal _ _).1 hzo z hz
      exact hz0 (inner_self_eq_zero.1 this)
  obtain ⟨w, hw, hw0, hwA⟩ := hS Finset.univ
  refine (Submodule.ne_bot_iff _).2 ⟨w, ?_, hw0⟩
  simp only [jointEig, Submodule.mem_iInf]
  exact fun j => (hmemZ j w).2 ⟨hw, hwA j (Finset.mem_univ j)⟩
end

noncomputable section

open GroundTheory.Automorphic UpperTheory.ConvolutionTheory.C

namespace UpperTheory.ConvolutionTheory.L1

section
variable {Γ G H : Type} [Group Γ] [TopologicalSpace Γ] [Group G] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H] {π : UnitaryRep Γ H} {V : Submodule ℂ H} {m : ℕ}
  {ι : Fin (m + 1) → G →* Γ} {E : H →L[ℂ] H} {A : Fin (m + 1) → H →L[ℂ] H} {U : H ≃ₗᵢ[ℂ] H}

private lemma mem_eigIn {W : Submodule ℂ H} {T : H →L[ℂ] H} {c : ℝ} {v : H} :
    v ∈ eigIn W T c ↔ v ∈ W ∧ T v = (c : ℂ) • v := by
  simp [eigIn, Submodule.mem_inf, Module.End.mem_eigenspace_iff]

private lemma closed_eigIn {W : Submodule ℂ H} (hW : IsClosed (W : Set H)) (T : H →L[ℂ] H) (c : ℝ) :
    IsClosed (eigIn W T c : Set H) := by
  have : (eigIn W T c : Set H) = (W : Set H) ∩ {v | T v = (c : ℂ) • v} := by
    ext v
    exact mem_eigIn
  rw [this]
  exact hW.inter (isClosed_eq T.continuous (continuous_const_smul _))

private lemma A_cut (h : Slots π V m ι E A U) (i : Fin (m + 1)) {v : H} (hv : v ∈ eigIn V E 1) :
    A i v ∈ eigIn V E 1 := by
  obtain ⟨h1, h2⟩ := mem_eigIn.1 hv
  simp only [Complex.ofReal_one, one_smul] at h2
  refine mem_eigIn.2 ⟨h.A_mem i v h1, ?_⟩
  rw [← h.A_E, h2]
  simp

private lemma U_cut (h : Slots π V m ι E A U) {v : H} (hv : v ∈ eigIn V E 1) :
    U v ∈ eigIn V E 1 := by
  obtain ⟨h1, h2⟩ := mem_eigIn.1 hv
  simp only [Complex.ofReal_one, one_smul] at h2
  refine mem_eigIn.2 ⟨?_, ?_⟩
  · rw [← h.U_mem]
    exact Submodule.mem_map_of_mem h1
  · rw [← h.U_E, h2]
    simp

private lemma fin_gen (x : Fin (m + 1)) : ∃ n : ℕ, n • (1 : Fin (m + 1)) = x := by
  induction x using Fin.induction with
  | zero => exact ⟨0, by simp⟩
  | succ a ih =>
    obtain ⟨n, hn⟩ := ih
    exact ⟨n + 1, by rw [succ_nsmul, hn, Fin.coeSucc_eq_succ]⟩

private lemma ne_all (h : Slots π V m ι E A U) {i : Fin (m + 1)}
    (hi : ∃ v ∈ eigIn V E 1, A i v ≠ 0) (j : Fin (m + 1)) : ∃ v ∈ eigIn V E 1, A j v ≠ 0 := by
  have step : ∀ n : ℕ, ∃ v ∈ eigIn V E 1, A (i - n • (1 : Fin (m + 1))) v ≠ 0 := by
    intro n
    induction n with
    | zero => simpa using hi
    | succ n ih =>
      obtain ⟨v, hv, hne⟩ := ih
      refine ⟨U v, U_cut h hv, ?_⟩
      have e : i - (n + 1) • (1 : Fin (m + 1)) + 1 = i - n • (1 : Fin (m + 1)) := by
        rw [succ_nsmul]
        abel
      have := h.U_A (i - (n + 1) • (1 : Fin (m + 1))) v
      rw [e] at this
      rw [← this]
      simpa using hne
  obtain ⟨n, hn⟩ := fin_gen (i - j)
  have := step n
  rwa [hn, sub_sub_cancel] at this

private lemma list_comm_A (h : Slots π V m ι E A U) (k : Fin (m + 1)) (L : List (Fin (m + 1))) (v : H) :
    A k ((L.map A).prod v) = (L.map A).prod (A k v) := by
  induction L generalizing v with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, ContinuousLinearMap.mul_apply]
    rw [h.A_A, ih]

private lemma list_comm_π (h : Slots π V m ι E A U) {k : Fin (m + 1)} {L : List (Fin (m + 1))}
    (hk : k ∉ L) (g : G) (v : H) :
    (L.map A).prod (π (ι k g) v) = π (ι k g) ((L.map A).prod v) := by
  induction L generalizing v with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, ContinuousLinearMap.mul_apply]
    have hka : a ≠ k := fun e => hk (by simp [e])
    have hkL : k ∉ L := fun e => hk (by simp [e])
    rw [ih hkL, h.A_ι a k hka]

private lemma list_mem (h : Slots π V m ι E A U) (L : List (Fin (m + 1))) {v : H}
    (hv : v ∈ eigIn V E 1) : (L.map A).prod v ∈ eigIn V E 1 := by
  induction L with
  | nil => simpa using hv
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, ContinuousLinearMap.mul_apply]
    exact A_cut h a ih

private lemma list_sa (h : Slots π V m ι E A U) (L : List (Fin (m + 1))) :
    IsSelfAdjoint (L.map A).prod := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have hc : (L.map A).prod * A a = A a * (L.map A).prod := by
      ext v
      simp only [ContinuousLinearMap.mul_apply]
      exact (list_comm_A h a L v).symm
    simp only [List.map_cons, List.prod_cons]
    rw [isSelfAdjoint_iff, star_mul, ih.star_eq, (IsSelfAdjoint.of_nonneg (h.A_pos a)).star_eq, hc]

private lemma list_zero (h : Slots π V m ι E A U) {k : Fin (m + 1)} {L : List (Fin (m + 1))}
    (hk : k ∈ L) {w : H} (hw : A k w = 0) : (L.map A).prod w = 0 := by
  induction L with
  | nil => simp at hk
  | cons a L ih =>
    simp only [List.map_cons, List.prod_cons, ContinuousLinearMap.mul_apply]
    rcases List.mem_cons.1 hk with e | e
    · subst e
      rw [list_comm_A h, hw, map_zero]
    · rw [ih e, map_zero]

private lemma list_ne (h : Slots π V m ι E A U) (hall : ∀ j, ∃ v ∈ eigIn V E 1, A j v ≠ 0)
    (hne : ∃ v ∈ eigIn V E 1, v ≠ 0) (L : List (Fin (m + 1))) (hL : L.Nodup) :
    ∃ v ∈ eigIn V E 1, (L.map A).prod v ≠ 0 := by
  induction L with
  | nil => simpa using hne
  | cons k L ih =>
    obtain ⟨u, hu, hQ⟩ := ih (List.nodup_cons.1 hL).2
    have hk : k ∉ L := (List.nodup_cons.1 hL).1
    obtain ⟨hcl, hinv, hirr⟩ := cutIrr Γ G H π V m ι E A U h
    by_contra hcon
    push_neg at hcon
    simp only [List.map_cons, List.prod_cons, ContinuousLinearMap.mul_apply] at hcon
    let M : Submodule ℂ H :=
      { carrier := {w | w ∈ eigIn V E 1 ∧ ∀ g, A k (π (ι k g) w) = 0}
        add_mem' := fun {a b} ha hb => ⟨Submodule.add_mem _ ha.1 hb.1, fun g => by
          rw [map_add (f := _), map_add (f := _), ha.2, hb.2, add_zero]⟩
        zero_mem' := ⟨Submodule.zero_mem _, fun g => by simp⟩
        smul_mem' := fun c a ha => ⟨Submodule.smul_mem _ c ha.1, fun g => by
          rw [map_smul, map_smul, ha.2, smul_zero]⟩ }
    have hMmem : ∀ w, w ∈ M ↔ w ∈ eigIn V E 1 ∧ ∀ g, A k (π (ι k g) w) = 0 := fun w => Iff.rfl
    have hMle : M ≤ eigIn V E 1 := fun w hw => hw.1
    have hMcl : IsClosed (M : Set H) := by
      have : (M : Set H) = (eigIn V E 1 : Set H) ∩ ⋂ g, {w | A k (π (ι k g) w) = 0} := by
        ext w
        simp [hMmem]
      rw [this]
      refine hcl.inter (isClosed_iInter fun g => ?_)
      exact isClosed_eq ((A k).continuous.comp (π (ι k g)).continuous) continuous_const
    have hMinv : ∀ i g, ∀ v ∈ M, π (ι i g) v ∈ M := by
      intro i g v hv
      refine ⟨hinv i g v hv.1, fun g' => ?_⟩
      by_cases e : i = k
      · subst e
        rw [← UnitaryRep.map_mul_apply, ← map_mul]
        exact hv.2 _
      · have hc : ι k g' * ι i g = ι i g * ι k g' := (h.ι_comm k i (Ne.symm e) g' g)
        rw [← UnitaryRep.map_mul_apply, hc, UnitaryRep.map_mul_apply, h.A_ι k i (Ne.symm e), hv.2, map_zero]
    have hQM : (L.map A).prod u ∈ M := by
      refine ⟨list_mem h L hu, fun g => ?_⟩
      rw [← list_comm_π h hk]
      exact hcon _ (hinv k g u hu)
    rcases hirr M hMle hMcl hMinv with e | e
    · rw [e] at hQM
      exact hQ ((Submodule.mem_bot ℂ).1 hQM)
    · obtain ⟨v, hv, hAv⟩ := hall k
      rw [← e] at hv
      have := hv.2 1
      simp only [map_one, UnitaryRep.map_one_apply] at this
      exact hAv this

private lemma fd_of_compact {T : H →L[ℂ] H} (hT : IsCompactOperator T) {x : ℂ} (hx : x ≠ 0)
    (P : Submodule ℂ H) (hP : IsClosed (P : Set H)) (hTP : ∀ v ∈ P, T v = x • v) :
    FiniteDimensional ℂ P := by
  have hC : IsCompact (closure (T '' Metric.closedBall 0 1)) :=
    hT.isCompact_closure_image_closedBall 1
  have hK : IsCompact ((fun z : H => x⁻¹ • z) '' closure (T '' Metric.closedBall 0 1)) :=
    hC.image (continuous_const_smul _)
  have hK' := hP.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  refine FiniteDimensional.of_isCompact_closedBall ℂ (c := (0 : P)) (r := 1) one_pos
    (hK'.of_isClosed_subset Metric.isClosed_closedBall ?_)
  intro p hp
  refine ⟨T p, subset_closure ⟨p, ?_, rfl⟩, ?_⟩
  · simpa using hp
  · simp only
    rw [hTP p p.2, smul_smul, inv_mul_cancel₀ hx, one_smul]

private lemma prj_fix {W : Submodule ℂ H} {v : H} (hv : v ∈ W) : prj W v = v :=
  (Submodule.starProjection_eq_self_iff).2 (Submodule.le_topologicalClosure _ hv)

private lemma prj_mem {W : Submodule ℂ H} (hW : IsClosed (W : Set H)) (v : H) : prj W v ∈ W := by
  have : prj W v ∈ W.topologicalClosure := by
    rw [prj, Submodule.starProjection_apply]
    exact Submodule.coe_mem _
  rwa [hW.submodule_topologicalClosure_eq] at this

private lemma spectral_ne {T : H →L[ℂ] H} (hT : IsCompactOperator T) (hsa : IsSelfAdjoint T) {u : H}
    (hu : T u ≠ 0) : ∃ (x : ℝ) (v : H), x ≠ 0 ∧ v ≠ 0 ∧ T v = (x : ℂ) • v := by
  obtain ⟨s, b, l, -, hb, hsum, -⟩ :=
    CompactSelfAdjoint.exists_hilbertBasis_eigenvectors_hasSum hT hsa
  by_cases hl : ∃ i, l i ≠ 0
  · obtain ⟨j, hj⟩ := hl
    exact ⟨l j, b j, hj, b.orthonormal.ne_zero j, hb j⟩
  · exfalso
    push_neg at hl
    apply hu
    rw [← (hsum u).tsum_eq]
    simp [hl]

end

end UpperTheory.ConvolutionTheory.L1

theorem UpperTheory.ConvolutionTheory.L1.jointEx :
    UpperTheory.ConvolutionTheory.L1.JointEx := by
  intro Γ G H _ _ _ _ _ _ π V m ι E A U h hcomp
  have hofn : List.ofFn A = (List.finRange (m + 1)).map A := List.ofFn_eq_map
  obtain ⟨hcl, -, -⟩ := cutIrr Γ G H π V m ι E A U h
  have hfd : ∀ x : ℝ, x ≠ 0 → FiniteDimensional ℂ (prodEig V E A x) := by
    intro x hx
    refine fd_of_compact hcomp (x := (x : ℂ)) (by exact_mod_cast hx) _ (closed_eigIn hcl _ _) ?_
    intro v hv
    obtain ⟨h1, h2⟩ := mem_eigIn.1 hv
    rw [ContinuousLinearMap.comp_apply, prj_fix h1]
    exact h2
  refine ⟨fun x hx => hfd x hx.ne', ?_⟩
  rintro ⟨i, v₀, hv₀, hne⟩
  have hall := ne_all h ⟨v₀, hv₀, hne⟩
  have hne0 : ∃ v ∈ eigIn V E 1, v ≠ 0 := ⟨v₀, hv₀, fun e => hne (by simp [e])⟩
  obtain ⟨u, hu, hQu⟩ := list_ne h hall hne0 (List.finRange (m + 1)) (List.nodup_finRange _)
  rw [← hofn] at hQu
  have hQmem : ∀ v ∈ eigIn V E 1, (List.ofFn A).prod v ∈ eigIn V E 1 := by
    intro v hv
    rw [hofn]
    exact list_mem h _ hv
  have hQsa : IsSelfAdjoint (List.ofFn A).prod := by
    rw [hofn]
    exact list_sa h _
  have hPm : ∀ v, prj (eigIn V E 1) v ∈ eigIn V E 1 := prj_mem hcl
  have hPsa : IsSelfAdjoint (prj (eigIn V E 1)) := isSelfAdjoint_starProjection _
  have hTeq : (List.ofFn A).prod ∘L prj (eigIn V E 1) =
      prj (eigIn V E 1) ∘L (List.ofFn A).prod ∘L prj (eigIn V E 1) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply]
    exact (prj_fix (hQmem _ (hPm v))).symm
  have hTsa : IsSelfAdjoint ((List.ofFn A).prod ∘L prj (eigIn V E 1)) := by
    rw [hTeq]
    have := hQsa.conj_adjoint (prj (eigIn V E 1))
    rwa [ContinuousLinearMap.isSelfAdjoint_iff'.1 hPsa] at this
  obtain ⟨lj, bj, hj, hv0, hTv⟩ := spectral_ne hcomp hTsa (u := u)
    (by rwa [ContinuousLinearMap.comp_apply, prj_fix hu])
  have hjc : (lj : ℂ) ≠ 0 := by exact_mod_cast hj
  rw [ContinuousLinearMap.comp_apply] at hTv
  have hvm : bj ∈ eigIn V E 1 := by
    have e : bj = (lj : ℂ)⁻¹ • (List.ofFn A).prod (prj (eigIn V E 1) (bj)) := by
      rw [hTv, smul_smul, inv_mul_cancel₀ hjc, one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (hQmem _ (hPm _))
  rw [prj_fix hvm] at hTv
  have hmemP : bj ∈ prodEig V E A lj := mem_eigIn.2 ⟨hvm, hTv⟩
  haveI := hfd lj hj
  have hinv : ∀ w ∈ prodEig V E A lj, (A 0 : H →ₗ[ℂ] H) w ∈ prodEig V E A lj := by
    intro w hw
    obtain ⟨h1, h2⟩ := mem_eigIn.1 hw
    refine mem_eigIn.2 ⟨A_cut h 0 h1, ?_⟩
    have := list_comm_A h 0 (List.finRange (m + 1)) w
    rw [← hofn] at this
    change (List.ofFn A).prod (A 0 w) = (lj : ℂ) • A 0 w
    rw [← this, h2, map_smul]
  haveI : Nontrivial (prodEig V E A lj) :=
    ⟨⟨⟨bj, hmemP⟩, 0, fun e => hv0 (congrArg Subtype.val e)⟩⟩
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((A 0 : H →ₗ[ℂ] H).restrict hinv)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  have hw1 : A 0 (w : H) = c • (w : H) := by
    have := congrArg Subtype.val (Module.End.HasEigenvector.apply_eq_smul hw)
    simpa using this
  have hw0 : (w : H) ≠ 0 := fun e => hw.2 (Subtype.ext e)
  have hEv : Module.End.HasEigenvalue (A 0 : H →ₗ[ℂ] H) c :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨Module.End.mem_eigenspace_iff.2 hw1, hw0⟩
  obtain ⟨r, rfl⟩ :=
    CompactSelfAdjoint.exists_real_of_hasEigenvalue (IsSelfAdjoint.of_nonneg (h.A_pos 0)) hEv
  obtain ⟨hwc, hwQ⟩ := mem_eigIn.1 w.2
  have hr0 : 0 ≤ r := by
    have hp := ContinuousLinearMap.nonneg_iff_isPositive.1 (h.A_pos 0)
    have h3 := hp.re_inner_nonneg_right (w : H)
    have h4 : 0 < ‖(w : H)‖ ^ 2 := by positivity
    have h5 : RCLike.re (inner ℂ (w : H) ((r : ℂ) • (w : H))) = r * ‖(w : H)‖ ^ 2 := by
      rw [inner_smul_right, ← inner_self_eq_norm_sq (𝕜 := ℂ) (w : H)]
      first
        | exact RCLike.re_ofReal_mul _ _
        | simp
    rw [hw1] at h3
    have h6 : 0 ≤ r * ‖(w : H)‖ ^ 2 := h5 ▸ h3
    by_contra hneg
    push_neg at hneg
    nlinarith
  have hrne : r ≠ 0 := by
    rintro rfl
    have hz : A 0 (w : H) = 0 := by simp [hw1]
    have := list_zero h (List.mem_finRange 0) hz
    rw [← hofn, hwQ] at this
    exact (smul_ne_zero hjc hw0) this
  refine ⟨r, lt_of_le_of_ne hr0 (Ne.symm hrne), ?_⟩
  refine jointNe Γ G H π V m ι E A U h 0 r fun e => ?_
  have hmem : (w : H) ∈ eigIn (eigIn V E 1) (A 0) r := mem_eigIn.2 ⟨hwc, hw1⟩
  rw [e] at hmem
  exact hw0 ((Submodule.mem_bot ℂ).1 hmem)
end
end

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.CuspidalSpectrum GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped ComplexConjugate InnerProductSpace Classical

namespace UpperTheory.ConvolutionTheory.L1.TY

section Hil
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private theorem pos_mul {O : H →L[ℂ] H} {W : Submodule ℂ H} (h : 0 ≤ O) (hc : Commute O (prj W)) : 0 ≤ O * prj W :=
  Commute.mul_nonneg h (prj_star _).nonneg hc

private theorem eig_one (V : Submodule ℂ H) {W : Submodule ℂ H} (hW : IsClosed (W : Set H)) : eigIn V (prj W) 1 = V ⊓ W := by
  ext v
  rw [mem_eigIn, Complex.ofReal_one, one_smul, Submodule.mem_inf]
  exact and_congr_right fun _ => ⟨fun h => h ▸ prj_mem hW v, prj_self⟩

private theorem fin_abs {m : ℕ} {V W₀ Wn Ty C : Submodule ℂ H} {W : Fin (m + 1) → Submodule ℂ H} {O : Fin (m + 1) → H →L[ℂ] H}
    {Oi : H →L[ℂ] H} (hV : IsClosed (V : Set H)) (h₀ : IsClosed (W₀ : Set H)) (hn : IsClosed (Wn : Set H))
    (hW : ∀ i, IsClosed (W i : Set H)) (hTy : Ty = Wn ⊓ W₀) (hWn : Wn = ⨅ i, W i) (hVC : V ≤ C)
    (hOi : Oi = (List.ofFn O).prod) (hQ : (List.ofFn fun i => prj (W i)).prod = prj Wn)
    (hc : ∀ i j, Commute (prj (W i)) (O j)) (hc' : ∀ j, Commute (prj Wn) (O j)) (hc₀ : Commute (prj Wn) (prj W₀))
    (hK : IsCompactOperator (Oi ∘L prj Ty ∘L prj C)) :
    (∀ x : ℝ, 0 < x → prodEig V (prj W₀) (fun i => O i * prj (W i)) x = eigIn (V ⊓ Ty) Oi x) ∧
    (∀ y : ℝ, 0 < y → jointEig V (prj W₀) (fun i => O i * prj (W i)) y = V ⊓ (⨅ i, eigIn ⊤ (O i) y) ⊓ Ty) ∧
    IsCompactOperator ((List.ofFn fun i => O i * prj (W i)).prod ∘L prj (eigIn V (prj W₀) 1)) ∧
    ∀ v ∈ V ⊓ Ty, O 0 v ≠ 0 → ∃ i, ∃ v ∈ eigIn V (prj W₀) 1, (O i * prj (W i)) v ≠ 0 := by
  have hprod : (List.ofFn fun i => O i * prj (W i)).prod = Oi * prj Wn := by
    rw [ofFn_mul _ _ _ fun i j _ => hc i j, hOi, hQ]
  have hOQ : Commute Oi (prj Wn) := by
    rw [hOi]
    refine Commute.list_prod_left _ _ fun x hx => ?_
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
    exact (hc' i).symm
  refine ⟨fun x hx => ?_, fun y hy => ?_, ?_, fun v hv h => ?_⟩
  · ext v
    rw [prodEig, eig_one V h₀, hprod, mem_eigIn, mem_eigIn, eig_mul hn hOQ hx.ne', hTy]
    simp only [Submodule.mem_inf]
    tauto
  · ext v
    have h2 := fun i => eig_mul (hW i) (hc i i).symm hy.ne' v
    simp only [jointEig, eig_one V h₀, hTy, hWn, Submodule.mem_iInf, Submodule.mem_inf, mem_eigIn, h2, Submodule.mem_top,
      true_and, forall_and, forall_const]
    tauto
  · rw [hprod, eig_one V h₀]
    have hcl : IsClosed ((V ⊓ W₀ : Submodule ℂ H) : Set H) := by
      rw [Submodule.coe_inf]; exact hV.inter h₀
    refine cast (congrArg _ (funext fun v => ?_)) (hK.comp_clm (prj (V ⊓ W₀)))
    have hu := prj_mem hcl v
    simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply]
    rw [prj_self (hVC hu.1), hTy, ← prj_mul hn h₀ hc₀, ContinuousLinearMap.mul_apply, prj_self hu.2]
  · rw [hTy, hWn] at hv
    refine ⟨0, v, eig_one V h₀ ▸ ⟨hv.1, hv.2.2⟩, ?_⟩
    rwa [ContinuousLinearMap.mul_apply, prj_self ((Submodule.mem_iInf _).1 hv.2.1 0)]

end Hil

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {n m : ℕ} {q : Pl F} {w₀ : PlacesOver E q}

private theorem lev_step (T : Ty σ n q w₀) (p : Pl F) (D : Split (incFin E p) (galFin σ p) m) (w : Fin (m + 1) ≃ PlacesOver E p)
    (hw : ∀ (b : CompletionsOver E p) i, completionMap p (w i).1 (D.e b i) = b (w i)) (i : Fin (m + 1)) :
    (T.J (w i).1).comap (mapGL n (completionMap p (w i).1)) = (T.J (w (i + 1)).1).comap (mapGL n (completionMap p (w (i + 1)).1)) := by
  obtain ⟨h1, -, -, -, -, -, h2, -⟩ := glueBasic _ _ _ _ m D n
  have hc : ∀ x j, GM.cmp (w j) x = mapGL n (completionMap p (w j).1) (D.comp n j x) := fun x j =>
    Units.ext (Matrix.ext fun a b => (hw _ j).symm)
  have key : ∀ j : Fin (m + 1), (T.J (w (j + 1)).1).comap (mapGL n (completionMap p (w (j + 1)).1)) ≤
      (T.J (w j).1).comap (mapGL n (completionMap p (w j).1)) := fun j g hg => by
    have h3 := (T.stable p (D.glue n (Pi.mulSingle (j + 1) g)) fun u => by
      obtain ⟨k, rfl⟩ := w.surjective u
      rw [hc, h1]
      by_cases e : k = j + 1
      · subst e
        rw [Pi.mulSingle_eq_same]
        exact hg
      · rw [Pi.mulSingle_eq_of_ne e, map_one]
        exact one_mem _).1 (w j)
    rwa [hc, h2, h1, Pi.mulSingle_eq_same] at h3
  exact le_antisymm (cyc_le (fun j => (T.J (w j).1).comap (mapGL n (completionMap p (w j).1))) key i) (key i)

private theorem place_inj {P : Finset (Pl F)} (w : ∀ p : P, Fin (m + 1) ≃ PlacesOver E p.1) {p p' : P} {i j : Fin (m + 1)}
    (h : (w p i).1 = (w p' j).1) : p = p' ∧ i = j := by
  obtain rfl : p = p' := Subtype.ext (by rw [← under_of_over (w p i), h, under_of_over])
  exact ⟨rfl, (w p).injective (Subtype.ext h)⟩

private def gen {P : Finset (Pl F)} (s : Fin (m + 1) → archGroup F n →* archGroup E n)
    (w : ∀ p : P, Fin (m + 1) ≃ PlacesOver E p.1) (i : Fin (m + 1)) :
    archGroup F n ⊕ (Σ p : P, GL (Fin n) (p.1.adicCompletion F)) → normOneGL (K := E) (n := n)
  | .inl g => archP E n (s i g)
  | .inr x => MultiplicityOne.finProj E n (AdelicGLn.localEmbedding (w x.1 i).1 (mapGL n (completionMap x.1.1 (w x.1 i).1) x.2))

private theorem gen_int (μ : Measure (normOneGL (K := E) (n := n))) [μ.IsHaarMeasure] {P : Finset (Pl F)}
    (s : Fin (m + 1) → archGroup F n →* archGroup E n) (w : ∀ p : P, Fin (m + 1) ≃ PlacesOver E p.1) (i : Fin (m + 1))
    (B : LL μ →L[ℂ] LL μ) (h1 : ∀ g, Commute B (rightRegularRep (rationalGLOne (K := E) (n := n)) μ (archP E n (s i g))))
    (h2 : ∀ p g, Commute B (rhoL μ (w p i).1 g)) (g : FreeGroup _) (v : LL μ) :
    B (rightRegularRep (rationalGLOne (K := E) (n := n)) μ (FreeGroup.lift (gen s w i) g) v) =
      rightRegularRep (rationalGLOne (K := E) (n := n)) μ (FreeGroup.lift (gen s w i) g) (B v) :=
  lift_int _ B _ _ (fun x v => by
    rcases x with g | ⟨p, g⟩
    · exact DFunLike.congr_fun (h1 g).eq v
    · exact DFunLike.congr_fun (h2 p _).eq v) g v

end UpperTheory.ConvolutionTheory.L1.TY

open UpperTheory.ConvolutionTheory.L1 UpperTheory.ConvolutionTheory.L1.TY in
set_option maxHeartbeats 6400000 in
theorem UpperTheory.ConvolutionTheory.L1.twistY :
    UpperTheory.ConvolutionTheory.L1.TwistY := by
  intro F E _ _ _ _ _ _ σ hσ m n hm hn μ _ θ hθ D s hs hposition νE _ νF _ b a aE aF hA q w₀ hq T V hV hVU hrk
  let P : Finset (Pl F) := insert q T.sp
  have hsp : ∀ p : P, GM.Split E p.1 := fun p => by
    rcases Finset.mem_insert.1 p.2 with h | h
    · exact h ▸ hq
    · exact (Finset.mem_filter.1 h).2
  have hmk : ∀ p : P, ∃ u : PlacesOver E p.1, ∀ x ∈ T.marked, x.under (𝓞 F) = p.1 → x = u.1 := fun p => by
    obtain ⟨p, hp⟩ := p
    by_cases e : p = q
    · subst e
      refine ⟨w₀, ?_⟩
      rintro x (rfl | ⟨v, hv, rfl⟩) hx
      · rfl
      · rw [under_of_over] at hx
        obtain rfl : v = p := hx
        exact absurd (Finset.mem_filter.1 hv).1 T.q_not
    · refine ⟨T.mk' p, ?_⟩
      rintro x (rfl | ⟨v, hv, rfl⟩) hx
      · rw [under_of_over] at hx
        exact absurd hx.symm e
      · rw [under_of_over] at hx
        subst hx
        rfl
  choose mk hmk using hmk
  choose Df w hw0 hw using fun p : P => finSplit F E σ hσ m hm p.1 (mk p) (hsp p)
  obtain ⟨U, hU, -, -⟩ := twistUnitary E n μ θ
  have hU' : ∀ v, U v = θ.U v := fun v => DFunLike.congr_fun hU v
  obtain ⟨tp1, tp2, tp3⟩ := twistPerm F E σ hσ m n μ θ hθ
  obtain ⟨-, ag2, ag3, -⟩ := archBasic F E σ m D n
  have hsurj : ∀ (p : P) i, Function.Surjective (mapGL n (completionMap p.1 (w p i).1)) := fun p i y => by
    obtain ⟨⟨e, he⟩, -⟩ := splitLoc F E p.1 (w p i) (hsp p _) n
    exact ⟨e.symm y, by rw [← he, e.apply_symm_apply]⟩
  let R : Fin (m + 1) → Set (Pl E) := fun i => Set.range fun p : P => (w p i).1
  let On : Set (Pl E) := {u | u.under (𝓞 F) ∈ (P : Set (Pl F))}
  have hOn : ∀ u ∈ On, ∃ p i, (w p i).1 = u := fun u hu =>
    ⟨⟨_, hu⟩, (w ⟨_, hu⟩).symm ⟨u, ⟨rfl⟩⟩, by rw [Equiv.apply_symm_apply]⟩
  have hOn' : ∀ p i, (w p i).1 ∈ On := fun p i => by
    show _ ∈ (P : Set (Pl F))
    rw [under_of_over]
    exact p.2
  have hRU : ⋃ i, R i = On := by
    ext u
    simp only [Set.mem_iUnion]
    exact ⟨fun ⟨i, p, e⟩ => e ▸ hOn' p i, fun h => by obtain ⟨p, i, e⟩ := hOn u h; exact ⟨i, p, e⟩⟩
  have hRd : ∀ i j, i ≠ j → Disjoint (R i) (R j) := fun i j hij => Set.disjoint_left.2 (by
    rintro _ ⟨p, rfl⟩ ⟨p', e⟩
    exact hij (place_inj w e).2.symm)
  have hRO : ∀ i, Disjoint (R i) Onᶜ := fun i => Set.disjoint_left.2 (by
    rintro _ ⟨p, rfl⟩ h
    exact h (hOn' p i))
  let O : Fin (m + 1) → LL μ →L[ℂ] LL μ := fun i => OComponent μ (s i) (hs i) νF a
  let Q : Set (Pl E) → LL μ →L[ℂ] LL μ := fun A => prj (GA μ T.J T.χ A)
  have hss : ∀ i j, i ≠ j → ∀ g h, Commute (s i g) (s j h) := fun i j hij g h => by
    rw [hposition, hposition]
    show _ * _ = _ * _
    rw [← ag3, ← ag3]
    exact congrArg _ (Pi.mulSingle_commute (f := fun _ : Fin (m + 1) => archGroup F n) hij g h).eq
  have hOc : ∀ (B : LL μ →L[ℂ] LL μ) i, (∀ g, Commute B (rightRegularRep (rationalGLOne (K := E) (n := n)) μ (archP E n (s i g)))) →
      Commute B (O i) := fun B i h => ContinuousLinearMap.ext fun v =>
    operatorAt_int μ (hs i) (hs i) νF a B (fun x u => DFunLike.congr_fun (h x).eq u) v
  have hrep : ∀ x y : normOneGL (K := E) (n := n), Commute x y →
      Commute (rightRegularRep (rationalGLOne (K := E) (n := n)) μ x) (rightRegularRep (rationalGLOne (K := E) (n := n)) μ y) := fun x y h =>
    ContinuousLinearMap.ext fun v => by
      simp only [ContinuousLinearMap.mul_apply]
      rw [← UnitaryRep.map_mul_apply, ← UnitaryRep.map_mul_apply, h.eq]
  have hQO : ∀ A i, Commute (Q A) (O i) := fun A i => hOc _ i fun g => (GA_arch μ A _).symm
  have hOa : ∀ i j, i ≠ j → ∀ g, Commute (O i) (rightRegularRep (rationalGLOne (K := E) (n := n)) μ (archP E n (s j g))) :=
    fun i j hij g => (hOc _ i fun x => hrep _ _ ((hss j i hij.symm g x).map _)).symm
  have hOO : ∀ i j, Commute (O i) (O j) := fun i j => by
    by_cases e : i = j
    · rw [e]
    · exact hOc _ j (hOa i j e)
  have hOr : ∀ i u g, Commute (O i) (rhoL μ u g) := fun i u g => (hOc _ i fun x => (hrep _ _ (arch_fin _ _)).symm).symm
  have hOV : ∀ i, ∀ v ∈ V, O i v ∈ V := fun i v hv => by
    have h := hOc (prj V) i fun g => ContinuousLinearMap.ext fun y => inv_commute _ hV.closed hV.inv _ y
    rw [← prj_self hv, ← ContinuousLinearMap.mul_apply, ← h.eq]
    exact prj_mem hV.closed _
  have hQQ : ∀ i j, Commute (Q (R i)) (Q (R j)) := fun i j => by
    by_cases e : i = j
    · rw [e]
    · exact GA_GA μ (hRd i j e)
  have hco : ∀ u, CO (T.J u) ∧ IsChr (T.J u) (T.χ u) := fun u => ⟨T.co u, T.chr u⟩
  have hcof : ∀ᶠ u in Filter.cofinite, T.J u = GLnLocal.integralGL (u.adicCompletion E) n ∧ T.χ u = 1 := by
    refine Filter.eventually_cofinite.2 (((insert q T.S).finite_toSet.biUnion fun v _ => finite_over (E := E) v).subset fun u hu => ?_)
    by_contra h
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop, exists_eq_right', Finset.coe_insert, Set.mem_insert_iff,
      Finset.mem_coe, not_or] at h
    exact hu (T.off u h.2 h.1)
  have hcomm : ∀ i j, i ≠ j → ∀ g h, Commute (FreeGroup.lift (gen s w i) g) (FreeGroup.lift (gen s w j) h) :=
    fun i j hij => lift_commute _ _ fun x y => by
      rcases x with g | ⟨p, g⟩ <;> rcases y with g' | ⟨p', g'⟩
      · exact (hss i j hij g g').map _
      · exact arch_fin _ _
      · exact (arch_fin _ _).symm
      · exact Commute.map ((UpperTheory.ConvolutionTheory.Tf.locEmb E n _).2.2.2.1 _ (fun e => hij (place_inj w e).2.symm) _ _) _
  have hUQ : ∀ i v, U (Q (R (i + 1)) v) = Q (R i) (U v) := fun i => by
    refine prj_equiv (GA_closed μ _) (GA_closed μ _) U fun v => ?_
    have h1 : ∀ j y, y ∈ GA μ T.J T.χ (R j) ↔ ∀ p : P, ∀ g ∈ (T.J (w p j).1).comap (mapGL n (completionMap p.1 (w p j).1)),
        rhoL μ (w p j).1 (mapGL n (completionMap p.1 (w p j).1) g) y = y := fun j y => by
      rw [mem_GA]
      constructor
      · intro h p g hg
        rw [h _ ⟨p, rfl⟩ _ hg, T.triv p.1 (hsp p) (w p j), Pi.one_apply, one_smul]
      · rintro h _ ⟨p, rfl⟩ x hx
        obtain ⟨g, rfl⟩ := hsurj p j x
        rw [h p g hx, T.triv p.1 (hsp p) (w p j), Pi.one_apply, one_smul]
    rw [h1, h1]
    refine forall_congr' fun p => ?_
    rw [lev_step T p.1 (Df p) (w p) (hw p) i]
    refine forall₂_congr fun g _ => ?_
    rw [hU', ← tp2 p.1 (Df p) (w p) (hw p) i g v, ← hU', ← hU']
    exact U.injective.eq_iff
  have S : Slots (rightRegularRep (rationalGLOne (K := E) (n := n)) μ) V m (fun i => FreeGroup.lift (gen s w i)) (Q Onᶜ)
      (fun i => O i * Q (R i)) U :=
    { summand := ⟨le_top, hV.closed, hV.inv, hV.ne_bot, hV.irred⟩
      ι_comm := hcomm
      rest := fun γ => by
        obtain ⟨A, h, rfl⟩ := MultiplicityOne.exists_archProj_mul_finProj γ
        have hfin : On.Finite := (P.finite_toSet.biUnion fun v _ => finite_over (E := E) v).subset fun u hu =>
          Set.mem_biUnion hu rfl
        obtain ⟨x, hx, h', e, h1⟩ := split_fin (prodM _ hcomm) hfin.toFinset (fun u hu y => by
          obtain ⟨p, i, rfl⟩ := hOn u (hfin.mem_toFinset.1 hu)
          obtain ⟨g, rfl⟩ := hsurj p i y
          have := mem_prodM _ hcomm i (FreeGroup.of (.inr ⟨p, g⟩))
          rwa [FreeGroup.lift_apply_of] at this) h
        have ha : archP E n ⟨A, Subgroup.mem_top A⟩ ∈ prodM _ hcomm := by
          rw [← ag2 ⟨A, Subgroup.mem_top A⟩, ← ofFn_mulSingle fun i => compA D n i _]
          have := map_list_prod ((archP E n).comp (MonoidHom.mk' (glueA D n) ag3))
            (List.ofFn fun i => (Pi.mulSingle i (compA D n i ⟨A, Subgroup.mem_top A⟩) : Fin (m + 1) → archGroup F n))
          refine (this ▸ Submonoid.list_prod_mem _ fun y hy => ?_ :
            ((archP E n).comp (MonoidHom.mk' (glueA D n) ag3)) _ ∈ _)
          rw [List.map_ofFn] at hy
          obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hy
          have := mem_prodM _ hcomm i (FreeGroup.of (.inl (compA D n i ⟨A, Subgroup.mem_top A⟩)))
          rw [FreeGroup.lift_apply_of, gen, hposition] at this
          exact this
        obtain ⟨g, hg⟩ := Submonoid.mul_mem _ ha hx
        obtain ⟨c, hc⟩ := restScalar E n μ V hV T.J T.χ hco hcof On (fun u hu => by
          by_cases hS : u.under (𝓞 F) ∈ T.S
          · exact hrk _ hS (fun h => hu (Finset.mem_insert_of_mem (Finset.mem_filter.2 ⟨hS, h⟩))) ⟨u, ⟨rfl⟩⟩
          · obtain ⟨e1, e2⟩ := T.off u hS fun h => hu (h ▸ Finset.mem_insert_self _ _ : _ ∈ P)
            rw [e1, e2]
            exact sphRank E n μ V hV u) h' fun u hu => h1 u (hfin.mem_toFinset.2 hu)
        refine ⟨g, _, c, ?_, fun v hv => hc _ ⟨GA_mem μ hV _ hv, prj_mem (GA_closed μ (J := T.J) (χ := T.χ) Onᶜ) v⟩⟩
        rw [← hg, e, mul_assoc]
        rfl
      E_sa := (prj_star _).isSelfAdjoint
      E_idem := fun v => prj_self (prj_mem (GA_closed μ _) v)
      E_mem := fun v hv => GA_mem μ hV _ hv
      E_ι := fun i => gen_int μ s w i _ (fun g => (GA_arch μ _ _).symm)
        fun p g => (GA_rhoL μ (Set.notMem_compl_iff.2 (hOn' p i)) g).symm
      A_pos := fun i => pos_mul (sqOp F n νF b a aF m hA.sq hA.pow hA.norm _ _).2.1 (hQO _ i).symm
      A_mem := fun i v hv => hOV i _ (GA_mem μ hV _ hv)
      A_E := fun i v => DFunLike.congr_fun ((hQO _ i).symm.mul_left (GA_GA μ (hRO i))).eq v
      A_A := fun i j v => DFunLike.congr_fun
        (((hOO i j).mul_left (hQO _ j)).mul_right ((hQO _ i).symm.mul_left (hQQ i j))).eq v
      A_ι := fun i j hij => gen_int μ s w j _ (fun g => (hOa i j hij g).mul_left (GA_arch μ _ _).symm)
        fun p g => (hOr i _ g).mul_left (GA_rhoL μ (Set.disjoint_right.1 (hRd i j hij) ⟨p, rfl⟩) g).symm
      U_mem := by
        rw [← hVU]
        congr 1
        exact LinearMap.ext hU'
      U_E := fun v => by
        rw [hU', hU']
        exact DFunLike.congr_fun (tp3 q w₀ T P).eq v
      U_A := fun i v => by
        show U (O (i + 1) (Q (R (i + 1)) v)) = O i (Q (R i) (U v))
        rw [← hUQ, hU', hU']
        exact operatorAt_int μ (hs _) (hs _) νF a θ.U (tp1 D s hposition i) _
      U_ι := fun i => lift_int _ U _ _ fun x v => by
        rw [hU', hU']
        rcases x with g | ⟨p, g⟩
        · exact tp1 D s hposition i g v
        · exact tp2 p.1 (Df p) (w p) (hw p) i g v }
  have hOi : Oinf μ νE aE = (List.ofFn O).prod := tensOp F E σ m D n νE νF hA.meas s hs hposition (LL μ) _ (fun _ => a) aE hA.tens
  have hty : T.typed μ = GA μ T.J T.χ Set.univ := by simp only [GA, Ty.typed, Set.mem_univ, iInf_true]
  obtain ⟨hPE, hJE, hcpt, hne⟩ := fin_abs (W := fun i => GA μ T.J T.χ (R i)) (Ty := T.typed μ) hV.closed
    (GA_closed μ (J := T.J) (χ := T.χ) Onᶜ) (GA_closed μ (J := T.J) (χ := T.χ) On) (fun i => GA_closed μ _)
    (by rw [← GA_union, Set.union_compl_self, hty]) (by rw [← hRU]; exact iInf_iUnion _ _) hV.le hOi
    (by rw [← hRU]; exact GA_prod μ _ R hRd) (fun i j => hQO _ j) (hQO _) (GA_GA μ disjoint_compl_right)
    (by rw [hty]; exact compact_typed μ hn νE hco hcof aE)
  obtain ⟨hfd, hex⟩ := jointEx _ _ _ _ V m _ _ _ U S hcpt
  refine ⟨fun ⟨v, hv, h0⟩ => ?_, fun y hy => ?_⟩
  · obtain ⟨y, hy, h⟩ := hex (hne v hv h0)
    exact ⟨y, hy, fun e => h ((hJE y hy).trans e)⟩
  · obtain ⟨c, hc, -, H⟩ := twTrace _ _ _ _ V m _ _ _ U S y hy (hfd _ (pow_pos hy _))
    refine ⟨c, hc, fun B hB1 hB2 => ?_⟩
    have hnm : ∀ j, j ≠ 0 → ∀ p, (w p j).1 ∉ T.marked := fun j hj p h =>
      hj (place_inj w ((hmk p _ h (under_of_over _)).trans (congrArg Subtype.val (hw0 p)).symm)).2
    have := H 0 B (fun j hj v => DFunLike.congr_fun ((hOc B j fun g => hB1 _).mul_right
        (GA_commute μ B (by rintro _ ⟨p, rfl⟩; exact hB2 _ (hnm j hj p)))).eq v)
      fun j hj => gen_int μ s w j B (fun g => hB1 _) fun p => hB2 _ (hnm j hj p)
    rw [hU] at this
    exact (congrArg (trOn · (B ∘L θ.U)) (hPE _ (pow_pos hy _))).symm.trans
      (this.trans (congrArg (fun X => c * trOn X B) (hJE y hy)))
