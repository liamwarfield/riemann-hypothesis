module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.ConsumerA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.FormalDegreeG2.FdCons

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.ConsumerC
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem cns_kType_iso {ε : Fin n → Bool} {Λ₁ Λ₂ : Fin n → ℝ} (h : Λ₁ = Λ₂) (T₁ : S7.KType ε Λ₁)
    (T₂ : S7.KType ε Λ₂) : ∃ φ : T₁.V ≃ₗᵢ[ℂ] T₂.V, ∀ k v, φ (T₁.op k v) = T₂.op k (φ v) := by
  subst h
  obtain ⟨φ, hφ, -⟩ := HW.kType_unique T₁ T₂
  exact ⟨φ, hφ⟩

theorem cns_kt_weight_eq {ε : Fin n → Bool} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {Λ₁ Λ₂ : Fin n → ℝ} {S₁ : Submodule ℂ H}
    (h₁ : Formalism.MainNotions.S.IsKTypeOf ε σ Λ₁ S₁) (h₂ : Formalism.MainNotions.S.IsKTypeOf ε σ Λ₂ ⊤) : Λ₁ = Λ₂ := by
  obtain ⟨-, hst1, -, ⟨v1, hv1S, hv10, hv1w⟩, hdom1⟩ := h₁
  obtain ⟨-, -, hirr2, ⟨v2, -, hv20, hv2w⟩, hdom2⟩ := h₂
  have hS1 : S₁ = ⊤ := by
    rcases hirr2 S₁ le_top hst1 with h | h
    · rw [h] at hv1S
      exact absurd ((Submodule.mem_bot ℂ).1 hv1S) hv10
    · exact h
  have c1 : Formalism.MainNotions.S.CDom ε Λ₁ Λ₂ := hdom2 Λ₁ v1 Submodule.mem_top hv10 hv1w
  have c2 : Formalism.MainNotions.S.CDom ε Λ₂ Λ₁ := hdom1 Λ₂ v2 (hS1 ▸ Submodule.mem_top) hv20 hv2w
  exact cdom_antisymm ε c1 c2

theorem cns_cpt_dec {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ)
    (ρ : S7.KG ε →* unitary (Matrix (Fin n) (Fin n) ℂ))
    (dρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ)
    (hc : Continuous (fun k : S7.KG ε => ((ρ k : unitary (Matrix (Fin n) (Fin n) ℂ)) : Matrix (Fin n) (Fin n) ℂ)))
    (hd : ∀ X, inK ε X → ∀ γ : ℝ → S7.KG ε, (∀ t : ℝ, S7.toMK (γ t) = NormedSpace.exp ((t : ℂ) • X)) →
      ∀ i j, HasDerivAt (fun t : ℝ => ((ρ (γ t) : unitary (Matrix (Fin n) (Fin n) ℂ)) :
        Matrix (Fin n) (Fin n) ℂ) i j) (dρ X i j) 0)
    (γw : Fin n → Fin n → ℝ) (hinj : Function.Injective γw)
    (hP1 : ∀ (ν : Fin n → ℝ) (x : PiLp 2 (fun _ : Fin n => T.V)), x ≠ 0 →
      Formalism.REAL.KHighest ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) ν x →
      ∃ s, ν = Λ + γw s ∧ HW.KDom ε (Λ + γw s))
    (hP2 : ∀ s, Module.finrank ℂ (HW.khwSub ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1)))
      (Λ + γw s)) ≤ 1)
    (hP3 : ∀ s, HW.KDom ε (Λ + γw s) → ∃ x : PiLp 2 (fun _ : Fin n => T.V), x ≠ 0 ∧
      Formalism.REAL.KHighest ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) (Λ + γw s) x)
    (Sm : Finset (Fin n)) (hSm : ∀ s, s ∈ Sm ↔ HW.KDom ε (Λ + γw s))
    (Λs : Fin n → Fin n → ℝ) (hΛs : ∀ s ∈ Sm, Λs s = Λ + γw s) (Ts : ∀ s, S7.KType ε (Λs s)) :
    ∃ j : ∀ s, (Ts s).V →ₗ[ℂ] PiLp 2 (fun _ : Fin n => T.V),
      (∀ s ∈ Sm, ∀ v w, inner ℂ (j s v) (j s w) = inner ℂ v w) ∧
      (∀ s ∈ Sm, ∀ k v, j s ((Ts s).op k v) = HW.tensOp T ρ k (j s v)) ∧
      (∀ s ∈ Sm, ∀ s' ∈ Sm, s ≠ s' → ∀ v v', inner ℂ (j s v) (j s' v') = 0) ∧
      ∀ x, ∃ v : ∀ s, (Ts s).V, x = ∑ s ∈ Sm, j s (v s) := by
  classical
  let R : HW.KRep ε :=
    { V := PiLp 2 (fun _ : Fin n => T.V), τ := HW.tensTau T ρ, cont := HW.tensTau_cont T ρ hc,
      dτ := HW.tensD T dρ, hasDeriv := fun X hX γ hγ => HW.tensD_hasDeriv T ρ dρ hX γ hγ (hd X hX γ hγ) }
  have hRu : R.units = HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1)) :=
    HW.tensKRep_units T ρ dρ hc hd
  have hRop : ∀ k, R.op k = HW.tensOp T ρ k := fun k => rfl
  obtain ⟨hrelR, hunitR⟩ := HW.kRepRel n ε R
  obtain ⟨m, x, μ, hx, horth, htop, -, -, hT⟩ := HW.compRed n ε R
  rw [hRu] at hrelR hunitR hx horth htop hT
  choose idx hidx hdom using fun i => hP1 (μ i) (x i) (hx i).1 (hx i).2
  have hidx_inj : Function.Injective idx := by
    intro i i' hii
    by_contra hne
    have hk : x i ∈ HW.khwSub ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1)))
        (Λ + γw (idx i)) := (HW.count_mem_khwSub_iff _ _ _ _).2 (by rw [← hidx i]; exact (hx i).2)
    have hk' : x i' ∈ HW.khwSub ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1)))
        (Λ + γw (idx i)) := (HW.count_mem_khwSub_iff _ _ _ _).2 (by rw [hii, ← hidx i']; exact (hx i').2)
    exact HW.count_not_two_of_finrank_le_one _ (hP2 (idx i)) hk hk' (hx i).1 (hx i').1
      (horth i i' hne _ (HW.count_mem_kSpan_self _ _ _) _ (HW.count_mem_kSpan_self _ _ _))
  have hpiece : ∀ (ν : Fin n → ℝ) (y : PiLp 2 (fun _ : Fin n => T.V)), y ≠ 0 →
      Formalism.REAL.KHighest ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) ν y →
      ∃ k, μ k = ν := by
    intro ν y hy0 hy
    by_contra hno
    push Not at hno
    apply hy0
    refine HW.count_eq_zero_of_orth _ htop y fun k z hz => ?_
    exact Formalism.REAL.kOrth _ n ε _ ν (μ k) y (x k) hrelR hunitR hy (hx k).2 (hno k).symm y
      (HW.count_mem_kSpan_self _ _ _) z hz
  have hsurj : ∀ s ∈ Sm, ∃ i, idx i = s := by
    intro s hs
    obtain ⟨y, hy0, hy⟩ := hP3 s ((hSm s).1 hs)
    obtain ⟨i, hi⟩ := hpiece _ y hy0 hy
    exact ⟨i, hinj (add_left_cancel ((hidx i).symm.trans hi))⟩
  have hmem : ∀ i, idx i ∈ Sm := fun i => (hSm _).2 (hdom i)
  have hj : ∀ s, ∃ js : (Ts s).V →ₗ[ℂ] PiLp 2 (fun _ : Fin n => T.V), s ∈ Sm → ∃ i, idx i = s ∧
      (∀ v, js v ∈ Formalism.REAL.kSpan ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) (x i)) ∧
      (∀ y ∈ Formalism.REAL.kSpan ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) (x i),
        ∃ v, js v = y) ∧
      (∀ v w, inner ℂ (js v) (js w) = inner ℂ v w) ∧
      (∀ k v, js ((Ts s).op k v) = HW.tensOp T ρ k (js v)) := by
    intro s
    by_cases hs : s ∈ Sm
    · obtain ⟨i, hi⟩ := hsurj s hs
      obtain ⟨Tk, φ, -, hφ, -, -⟩ := hT i
      obtain ⟨ψ, hψ⟩ := cns_kType_iso (show Λs s = μ i by rw [hΛs s hs, hidx i, hi]) (Ts s) Tk
      refine ⟨(Formalism.REAL.kSpan ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) (x i)).subtype
        ∘ₗ φ.toLinearEquiv.toLinearMap ∘ₗ ψ.toLinearEquiv.toLinearMap, fun _ => ⟨i, hi, ?_, ?_, ?_, ?_⟩⟩
      · intro v
        exact (φ (ψ v)).2
      · intro y hy
        refine ⟨ψ.symm (φ.symm ⟨y, hy⟩), ?_⟩
        show (φ (ψ (ψ.symm (φ.symm ⟨y, hy⟩)))).1 = y
        rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
      · intro v w
        show inner ℂ (φ (ψ v)).1 (φ (ψ w)).1 =
          inner ℂ v w
        rw [← Submodule.coe_inner, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]
      · intro k v
        show (φ (ψ ((Ts s).op k v))).1 = HW.tensOp T ρ k (φ (ψ v)).1
        rw [hψ, hφ, hRop]
    · exact ⟨0, fun h => absurd h hs⟩
  choose j hj using hj
  refine ⟨j, fun s hs => (hj s hs).choose_spec.2.2.2.1, fun s hs => (hj s hs).choose_spec.2.2.2.2,
    fun s hs s' hs' hne v v' => ?_, fun y => ?_⟩
  · obtain ⟨i, hi, hin, -⟩ := hj s hs
    obtain ⟨i', hi', hin', -⟩ := hj s' hs'
    have hii : i ≠ i' := fun h => hne (hi.symm.trans (h ▸ hi'))
    exact horth i i' hii _ (hin v) _ (hin' v')
  · have hy : y ∈ ⨆ i ∈ (univ : Finset (Fin m)),
        Formalism.REAL.kSpan ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) (x i) := by
      have e : (⨆ i ∈ (univ : Finset (Fin m)),
          Formalism.REAL.kSpan ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) (x i)) =
          ⨆ i, Formalism.REAL.kSpan ε (HW.tensAct (HW.kunits T) (fun a b => dρ (Matrix.single a b 1))) (x i) := by
        simp
      rw [e, htop]
      exact Submodule.mem_top
    obtain ⟨μf, hμf⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ y).1 hy
    have hv : ∀ s, ∃ v : (Ts s).V, s ∈ Sm → ∀ i, idx i = s → j s v = (μf i : PiLp 2 (fun _ : Fin n => T.V)) := by
      intro s
      by_cases hs : s ∈ Sm
      · obtain ⟨i, hi, -, hsur, -⟩ := hj s hs
        obtain ⟨v, hv⟩ := hsur _ (μf i).2
        refine ⟨v, fun _ i' hi' => ?_⟩
        have : i' = i := hidx_inj (hi'.trans hi.symm)
        subst this
        exact hv
      · exact ⟨0, fun h => absurd h hs⟩
    choose v hv using hv
    refine ⟨v, ?_⟩
    rw [← hμf]
    exact Finset.sum_bij (fun a _ => idx a) (fun a _ => hmem a) (fun a _ b _ h => hidx_inj h)
      (fun b hb => let ⟨a, ha⟩ := hsurj b hb; ⟨a, mem_univ _, ha⟩)
      (fun a _ => (hv (idx a) (hmem a) a rfl).symm)

end ReciprocityTheory.ChartRestriction.DS
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.Consumer
section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.ConsumerB
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

open MeasureTheory

def cns_Ok (ε : Fin n → Bool) (lam : Fin n → ℝ) (T : S7.KType ε (lowK ε lam))
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) : Prop :=
  (∃ h : ℝ, GapAtLeast ε lam h ∧ thrS ε < h) ∧ StdGap ε lam ∧ IsPsiFor ε lam T Ψ ∧ T.w ≠ 0 ∧
    (∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive) ∧
    (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w),
        MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
          inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2
          (Formalism.REAL.muG ε)) ∧
    HasGelfandChar (smE ε (rreg ε)) lam (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w))

theorem cns_data' {ε : Fin n → Bool} (hq : 1 ≤ S7.q0 ε) {lam : Fin n → ℝ} (hlam : S7.IsHCParam lam)
    {h : ℝ} (hh : GapAtLeast ε lam h) (hth : thrS ε < h) :
    ∃ (T : S7.KType ε (lowK ε lam)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), cns_Ok ε lam T Ψ := by
  obtain ⟨T, Ψ, h1, h2, h3, h4, h5, h6⟩ := cns_data hq hlam hh hth
  exact ⟨T, Ψ, ⟨h, hh, hth⟩, h1, h2, h3, h4, h5, h6⟩

theorem cns_family (dual : Bool) {ε : Fin n → Bool} (hq : 1 ≤ S7.q0 ε) {μ : Fin n → ℝ}
    (hμ : S7.IsHCParam μ) {h : ℝ} (hG : GapAtLeast ε μ h) (hth : thrS ε + 1 < h) :
    ∃ (lamS : Fin n → Fin n → ℝ) (Ts : ∀ s, S7.KType ε (lowK ε (lamS s)))
      (Ψs : ∀ s, Matrix (Fin n) (Fin n) ℂ → ((Ts s).V →L[ℂ] (Ts s).V)),
      (∀ s, cns_Ok ε (lamS s) (Ts s) (Ψs s)) ∧
      ∀ s, S7.IsHCParam (shiftF dual μ s) → lamS s = shiftF dual μ s := by
  classical
  have hth' : thrS ε < h - 1 := by linarith
  have key : ∀ s, ∃ (l : Fin n → ℝ) (T : S7.KType ε (lowK ε l))
      (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)),
      cns_Ok ε l T Ψ ∧ (S7.IsHCParam (shiftF dual μ s) → l = shiftF dual μ s) := by
    intro s
    by_cases hs : S7.IsHCParam (shiftF dual μ s)
    · obtain ⟨T, Ψ, hT⟩ := cns_data' hq hs (cns_shift_gap dual hG s) hth'
      exact ⟨_, T, Ψ, hT, fun _ => rfl⟩
    · obtain ⟨T, Ψ, hT⟩ := cns_data' hq hμ hG (by linarith)
      exact ⟨μ, T, Ψ, hT, fun h' => absurd h' hs⟩
  choose lamS Ts Ψs hok hsh using key
  exact ⟨lamS, Ts, Ψs, hok, hsh⟩

theorem cns_pole (dual : Bool) {ε : Fin n → Bool} {μ : Fin n → ℝ} (hμ : S7.IsHCParam μ)
    {T : S7.KType ε (lowK ε μ)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {v₀ : T.V}
    (hgap : StdGap ε μ) (hP : IsPsiFor ε μ T Ψ) (hv₀ : v₀ ≠ 0)
    (hW : (∀ v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀), ∀ w ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ v₀),
        MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
          inner ℂ ((w : smD ε (rreg ε)) : L2 ε) (rreg ε (Formalism.MainNotions.S.umat g) ((v : smD ε (rreg ε)) : L2 ε))) 2
          (Formalism.REAL.muG ε)))
    (hG : HasGelfandChar (smE ε (rreg ε)) μ (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    {z : ℂ} {f : Fin n → smD ε (rreg ε)} (hf : f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ v₀)))
    (hf0 : f ≠ 0) (he : eeF dual (smE ε (rreg ε)) f = z • f) :
    ∃ s, S7.IsHCParam (shiftF dual μ s) ∧ z = poleF dual μ s := by
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE (ε := ε) (σ := rreg ε) hσ
  have hsm : ∀ v : smD ε (rreg ε), IsSmoothVecU ε (rreg ε) (v : L2 ε) := fun v =>
    (mem_smD_iff ε (rreg ε) v).1 v.2
  have hV := datumV_isKIrrHW hP hv₀
  have hc := datumV_casimir hP v₀
  have hVK := datumV_kStable hP v₀
  obtain ⟨s, hs⟩ := (pole_match dual hσ hD hsm hgap hV hc hVK hW hG).1 z f hf hf0 he
  refine ⟨s, ?_, hs⟩
  by_contra hns
  have hr := ccA_ratio_zero dual hgap s (cns_sing dual hμ hns)
  exact hf0 ((pole_zero dual hσ hD hsm hgap hV hc hVK hW hG s).1 hr f hf (hs ▸ he))

theorem cns_toSum_core (dual : Bool) {ε : Fin n → Bool} {μ : Fin n → ℝ} (hμ : S7.IsHCParam μ)
    {T : S7.KType ε (lowK ε μ)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} (hok : cns_Ok ε μ T Ψ)
    (lamS : Fin n → Fin n → ℝ) (Ts : ∀ s, S7.KType ε (lowK ε (lamS s)))
    (Ψs : ∀ s, Matrix (Fin n) (Fin n) ℂ → ((Ts s).V →L[ℂ] (Ts s).V))
    (hS : ∀ s, cns_Ok ε (lamS s) (Ts s) (Ψs s))
    (hsh : ∀ s, S7.IsHCParam (shiftF dual μ s) → lamS s = shiftF dual μ s)
    {η f : Fin n → smD ε (rreg ε)} (hη : η ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w)))
    (hf : f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w))) :
    ∃ (ι : Type) (_ : Fintype ι) (sI : ι → Fin n) (vI wI : ∀ i, Hlam ε (Ψs (sI i)) (Ts (sI i)).w),
      (∀ i, S7.IsHCParam (shiftF dual μ (sI i)) ∧
        PI.UpqRep.IsKFin ε (sigLam ε (Ψs (sI i)) (Ts (sI i)).w) (vI i) ∧
        PI.UpqRep.IsKFin ε (sigLam ε (Ψs (sI i)) (Ts (sI i)).w) (wI i)) ∧
      ∀ g ∈ UJset ε, ∑ c, inner ℂ ((η c : smD ε (rreg ε)) : L2 ε)
          (tensGrp dual (rreg ε) g (fun d => ((f d : smD ε (rreg ε)) : L2 ε)) c) =
        ∑ i, inner ℂ (wI i) (sigLam ε (Ψs (sI i)) (Ts (sI i)).w g (vI i)) := by
  classical
  obtain ⟨⟨h0, hh0, hth0⟩, hgap, hP, hv, hpos, hW, hG⟩ := hok
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  obtain ⟨B, hdec, -⟩ := ee_decomp dual hσ hD hgap (datumV_isKIrrHW hP hv) (datumV_casimir hP T.w)
    (datumV_kStable hP T.w) hW
  obtain ⟨fb, hfb, rfl⟩ := hdec f hf
  have hcomp : ∀ i : {b // b ∈ B.filter (fun b => fb b ≠ 0)}, ∃ s, S7.IsHCParam (shiftF dual μ s) ∧
      ∃ x z : Hlam ε (Ψs s) (Ts s).w, PI.UpqRep.IsKFin ε (sigLam ε (Ψs s) (Ts s).w) x ∧
        PI.UpqRep.IsKFin ε (sigLam ε (Ψs s) (Ts s).w) z ∧
        ∀ g ∈ UJset ε, ∑ c, inner ℂ ((η c : smD ε (rreg ε)) : L2 ε)
          (tensGrp dual (rreg ε) g (fun d => ((fb i d : smD ε (rreg ε)) : L2 ε)) c) =
          inner ℂ z (sigLam ε (Ψs s) (Ts s).w g x) := by
    intro i
    have hi := (Finset.mem_filter.1 i.2).2
    obtain ⟨s, hs, hz⟩ := cns_pole dual hμ hgap hP hv hW hG (hfb i).1 hi (hfb i).2
    obtain ⟨⟨h', hh', hth'⟩, hgap', hP', hv', hpos', hW', hG'⟩ := hS s
    have he : eeF dual (smE ε (rreg ε)) (fb i) = poleF dual μ s • fb i := by rw [(hfb i).2, hz]
    exact ⟨s, hs, cns_term dual hgap hP hv hgap' hP' hv' hh0 hth0 hh' hth' hpos hpos' hW hW' hG hG' s
      (hsh s hs) (hfb i).1 he hη⟩
  choose sI hsI xI zI hx hz hEq using hcomp
  refine ⟨{b // b ∈ B.filter (fun b => fb b ≠ 0)}, inferInstance, sI, xI, zI,
    fun i => ⟨hsI i, hx i, hz i⟩, fun g hg => ?_⟩
  have h0 : ∀ b ∈ B, ∑ c, inner ℂ ((η c : smD ε (rreg ε)) : L2 ε)
      (tensGrp dual (rreg ε) g (fun d => ((fb b d : smD ε (rreg ε)) : L2 ε)) c) ≠ 0 → fb b ≠ 0 := by
    intro b _ hne hb
    apply hne
    simp [hb, tensGrp]
  rw [cns_tens_sum, ← Finset.sum_filter_of_ne h0, ← Finset.sum_coe_sort]
  exact Finset.sum_congr rfl fun i _ => hEq i g hg

theorem cns_ofSum_core (dual : Bool) {ε : Fin n → Bool} {μ lam' : Fin n → ℝ}
    {T : S7.KType ε (lowK ε μ)} {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} (hok : cns_Ok ε μ T Ψ)
    {T' : S7.KType ε (lowK ε lam')} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}
    (hok' : cns_Ok ε lam' T' Ψ') (s : Fin n) (hlam' : lam' = shiftF dual μ s) {x' z' : smD ε (rreg ε)}
    (hx' : x' ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' T'.w))
    (hz' : z' ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ' T'.w)) :
    ∃ f F : Fin n → smD ε (rreg ε), f ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w)) ∧
      F ∈ tensSub (genSub (smE ε (rreg ε)) (datumV ε Ψ T.w)) ∧
      ∀ g ∈ UJset ε, inner ℂ ((z' : smD ε (rreg ε)) : L2 ε) (rreg ε g ((x' : smD ε (rreg ε)) : L2 ε)) =
        ∑ c, inner ℂ ((f c : smD ε (rreg ε)) : L2 ε)
          (tensGrp dual (rreg ε) g (fun d => ((F d : smD ε (rreg ε)) : L2 ε)) c) := by
  obtain ⟨⟨h, hh, hth⟩, hgap, hP, hv, hpos, hW, hG⟩ := hok
  obtain ⟨⟨h', hh', hth'⟩, hgap', hP', hv', hpos', hW', hG'⟩ := hok'
  haveI := Hlam_nontrivial hgap hP hv
  haveI := Hlam_nontrivial hgap' hP' hv'
  obtain ⟨w, hw⟩ := exists_ne (0 : Hlam ε Ψ T.w)
  obtain ⟨w', hw'⟩ := exists_ne (0 : Hlam ε Ψ' T'.w)
  obtain ⟨⟨ι, hι, -, -⟩, -⟩ := cc_gk dual hgap hP hv hgap' hP' hv' hh hth hh' hth' hpos hpos' hW hW' hG hG'
    s hlam' hw hw'
  have hσ := rreg_isURepOn ε
  have hD := isDerivedOn_smE hσ
  obtain ⟨f, hf, hfe⟩ := (coef_of_emb dual hσ hD hgap (datumV_isKIrrHW hP hv) (datumV_casimir hP T.w)
    (datumV_kStable hP T.w) hgap' (datumV_isKIrrHW hP' hv') (datumV_casimir hP' T'.w)
    (datumV_kStable hP' T'.w) hι).2 z' hz' x' hx'
  exact ⟨f, ι x', hf, hι.1 x' hx', hfe⟩

end ReciprocityTheory.ChartRestriction.DS.G2

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

open MeasureTheory

theorem cns_zuck_nc {ε : Fin n → Bool} (hq : 1 ≤ S7.q0 ε) {μ : Fin n → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hμ : PI.UpqRep.IsHCParam μ) (hd : PI.UpqRep.IsDS ε μ σ) {h : ℝ} (hG : PI.ZuckTensor.GapAtLeast ε μ h)
    (hth : thrS ε + 1 < h) :
    ∃ X : PI.ZuckTensor.TensorDS n ε μ H σ, ∀ s, s ∈ X.Sm ↔ PI.UpqRep.IsHCParam (μ + Pi.single s 1) := by
  classical
  have hμ' : S7.IsHCParam μ := hμ
  have hG' : GapAtLeast ε μ h := hG
  obtain ⟨T, Ψ, hok⟩ := cns_data' hq hμ' hG' (by linarith)
  obtain ⟨lamS, Ts, Ψs, hS, hsh⟩ := cns_family false hq hμ' hG' hth
  obtain ⟨U, hU⟩ := equiv_sigLam_of_isDS hd hok.2.1 hok.2.2.1 hok.2.2.2.1
  have hU' := cns_symm_intertw U hU
  refine ⟨{ Sm := univ.filter (fun s => S7.IsHCParam (shiftF false μ s))
            Hs := fun s => Hlam ε (Ψs s) (Ts s).w
            σs := fun s => sigLam ε (Ψs s) (Ts s).w
            ds := ?_, inequiv := ?_, toSum := ?_, ofSum := ?_ }, ?_⟩
  · intro s hs
    have hs' := (mem_filter.1 hs).2
    refine ⟨hs', ?_⟩
    have e : (μ + Pi.single s 1) = lamS s := (hsh s hs').symm
    rw [e]
    exact isDS_sigLam (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1
  · rintro s hs s' hs' hne ⟨V, hV⟩
    apply hne
    have e := sigLam_inj (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 (hS s').2.1 (hS s').2.2.1 (hS s').2.2.2.1 V hV
    rw [hsh s (mem_filter.1 hs).2, hsh s' (mem_filter.1 hs').2] at e
    exact cns_shift_inj false μ e
  · intro v w x y hv hw
    obtain ⟨a, ha, hav⟩ := cns_kfin_gen hok.2.1 hok.2.2.1 hok.2.2.2.1 (cns_kfin_map U.symm hU' hv)
    obtain ⟨b, hb, hbw⟩ := cns_kfin_gen hok.2.1 hok.2.2.1 hok.2.2.2.1 (cns_kfin_map U.symm hU' hw)
    obtain ⟨ι, hι, sI, vI, wI, hI, hEq⟩ := cns_toSum_core false hμ' hok lamS Ts Ψs hS hsh
      (η := fun c => y c • b) (f := fun d => x d • a)
      (tset_mem.2 fun c => Submodule.smul_mem _ _ hb) (tset_mem.2 fun d => Submodule.smul_mem _ _ ha)
    refine ⟨ι, hι, sI, vI, wI, fun i => ⟨mem_filter.2 ⟨mem_univ _, (hI i).1⟩, (hI i).2.1, (hI i).2.2⟩,
      fun g hg => ?_⟩
    rw [← hEq g hg]
    simp only [Submodule.coe_smul]
    rw [← cns_coefV (rreg ε) g (a : L2 ε) (b : L2 ε) x y, ← U.apply_symm_apply v, ← U.apply_symm_apply w,
      cns_inner_tr hok.2.1 hok.2.2.1 hok.2.2.2.1 U hU hg, ← hav, ← hbw]
  · intro s hs v w hv hw
    have hs' := (mem_filter.1 hs).2
    obtain ⟨x', hx', hxv⟩ := cns_kfin_gen (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 hv
    obtain ⟨z', hz', hzw⟩ := cns_kfin_gen (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 hw
    obtain ⟨f, F, hf, hF, hfe⟩ := cns_ofSum_core false hok (hS s) s (hsh s hs') hx' hz'
    have hfm := tset_mem.1 hf
    have hFm := tset_mem.1 hF
    refine ⟨Fin n × Fin n, inferInstance,
      fun p => U ⟨((F p.2 : smD ε (rreg ε)) : L2 ε), cns_gen_mem_Hlam (hFm p.2)⟩,
      fun p => U ⟨((f p.1 : smD ε (rreg ε)) : L2 ε), cns_gen_mem_Hlam (hfm p.1)⟩,
      fun p => Pi.single p.2 1, fun p => Pi.single p.1 1,
      fun p => ⟨cns_kfin_map U hU (cns_kfin hok.2.1 hok.2.2.1 hok.2.2.2.1 (hFm p.2) _ rfl),
        cns_kfin_map U hU (cns_kfin hok.2.1 hok.2.2.1 hok.2.2.2.1 (hfm p.1) _ rfl)⟩, fun g hg => ?_⟩
    dsimp only
    rw [Submodule.coe_inner, sigLam_coe (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 hg, ← hxv, ← hzw, hfe g hg,
      cns_expandV]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [cns_inner_tr hok.2.1 hok.2.2.1 hok.2.2.2.1 U hU hg]
  · intro s
    exact ⟨fun hs => (mem_filter.1 hs).2, fun hs => mem_filter.2 ⟨mem_univ _, hs⟩⟩

theorem cns_zuckd_nc {ε : Fin n → Bool} (hq : 1 ≤ S7.q0 ε) {μ : Fin n → ℝ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hμ : PI.UpqRep.IsHCParam μ) (hd : PI.UpqRep.IsDS ε μ σ) {h : ℝ} (hG : PI.ZuckTensor.GapAtLeast ε μ h)
    (hth : thrS ε + 1 < h) :
    ∃ X : PI.ZuckTensor.TensorDSd n ε μ H σ, ∀ s, s ∈ X.Sm ↔ PI.UpqRep.IsHCParam (μ - Pi.single s 1) := by
  classical
  have hμ' : S7.IsHCParam μ := hμ
  have hG' : GapAtLeast ε μ h := hG
  obtain ⟨T, Ψ, hok⟩ := cns_data' hq hμ' hG' (by linarith)
  obtain ⟨lamS, Ts, Ψs, hS, hsh⟩ := cns_family true hq hμ' hG' hth
  obtain ⟨U, hU⟩ := equiv_sigLam_of_isDS hd hok.2.1 hok.2.2.1 hok.2.2.2.1
  have hU' := cns_symm_intertw U hU
  refine ⟨{ Sm := univ.filter (fun s => S7.IsHCParam (shiftF true μ s))
            Hs := fun s => Hlam ε (Ψs s) (Ts s).w
            σs := fun s => sigLam ε (Ψs s) (Ts s).w
            ds := ?_, inequiv := ?_, toSum := ?_, ofSum := ?_ }, ?_⟩
  · intro s hs
    have hs' := (mem_filter.1 hs).2
    refine ⟨hs', ?_⟩
    have e : (μ - Pi.single s 1) = lamS s := (hsh s hs').symm
    rw [e]
    exact isDS_sigLam (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1
  · rintro s hs s' hs' hne ⟨V, hV⟩
    apply hne
    have e := sigLam_inj (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 (hS s').2.1 (hS s').2.2.1 (hS s').2.2.2.1 V hV
    rw [hsh s (mem_filter.1 hs).2, hsh s' (mem_filter.1 hs').2] at e
    exact cns_shift_inj true μ e
  · intro v w x y hv hw
    obtain ⟨a, ha, hav⟩ := cns_kfin_gen hok.2.1 hok.2.2.1 hok.2.2.2.1 (cns_kfin_map U.symm hU' hv)
    obtain ⟨b, hb, hbw⟩ := cns_kfin_gen hok.2.1 hok.2.2.1 hok.2.2.2.1 (cns_kfin_map U.symm hU' hw)
    obtain ⟨ι, hι, sI, vI, wI, hI, hEq⟩ := cns_toSum_core true hμ' hok lamS Ts Ψs hS hsh
      (η := fun c => star (x c) • b) (f := fun d => star (y d) • a)
      (tset_mem.2 fun c => Submodule.smul_mem _ _ hb) (tset_mem.2 fun d => Submodule.smul_mem _ _ ha)
    refine ⟨ι, hι, sI, vI, wI, fun i => ⟨mem_filter.2 ⟨mem_univ _, (hI i).1⟩, (hI i).2.1, (hI i).2.2⟩,
      fun g hg => ?_⟩
    rw [← hEq g hg]
    simp only [Submodule.coe_smul]
    rw [← cns_coefVd (rreg ε) g (a : L2 ε) (b : L2 ε) x y, ← U.apply_symm_apply v, ← U.apply_symm_apply w,
      cns_inner_tr hok.2.1 hok.2.2.1 hok.2.2.2.1 U hU hg, ← hav, ← hbw]
  · intro s hs v w hv hw
    have hs' := (mem_filter.1 hs).2
    obtain ⟨x', hx', hxv⟩ := cns_kfin_gen (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 hv
    obtain ⟨z', hz', hzw⟩ := cns_kfin_gen (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 hw
    obtain ⟨f, F, hf, hF, hfe⟩ := cns_ofSum_core true hok (hS s) s (hsh s hs') hx' hz'
    have hfm := tset_mem.1 hf
    have hFm := tset_mem.1 hF
    refine ⟨Fin n × Fin n, inferInstance,
      fun p => U ⟨((F p.2 : smD ε (rreg ε)) : L2 ε), cns_gen_mem_Hlam (hFm p.2)⟩,
      fun p => U ⟨((f p.1 : smD ε (rreg ε)) : L2 ε), cns_gen_mem_Hlam (hfm p.1)⟩,
      fun p => Pi.single p.1 1, fun p => Pi.single p.2 1,
      fun p => ⟨cns_kfin_map U hU (cns_kfin hok.2.1 hok.2.2.1 hok.2.2.2.1 (hFm p.2) _ rfl),
        cns_kfin_map U hU (cns_kfin hok.2.1 hok.2.2.1 hok.2.2.2.1 (hfm p.1) _ rfl)⟩, fun g hg => ?_⟩
    dsimp only
    rw [Submodule.coe_inner, sigLam_coe (hS s).2.1 (hS s).2.2.1 (hS s).2.2.2.1 hg, ← hxv, ← hzw, hfe g hg,
      cns_expandVd]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [cns_inner_tr hok.2.1 hok.2.2.1 hok.2.2.2.1 U hU hg]
  · intro s
    exact ⟨fun hs => (mem_filter.1 hs).2, fun hs => mem_filter.2 ⟨mem_univ _, hs⟩⟩

end ReciprocityTheory.ChartRestriction.DS.G2
end
end
end

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.ConsumerD
noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

theorem cns_shift_int (dual : Bool) {μ : Fin n → ℝ} (hμ : S7.IsHCParam μ) (s : Fin n) :
    ∀ a, ∃ m : ℤ, shiftF dual μ s a - ((n : ℝ) - 1) / 2 = m := by
  intro a
  obtain ⟨m, hm⟩ := hμ.2 a
  by_cases has : a = s
  · subst has
    cases dual
    · exact ⟨m + 1, by simp only [shiftF, cond_false, Pi.add_apply, Pi.single_eq_same]; push_cast; linarith⟩
    · exact ⟨m - 1, by simp only [shiftF, cond_true, Pi.sub_apply, Pi.single_eq_same]; push_cast; linarith⟩
  · refine ⟨m, ?_⟩
    cases dual
    · simp only [shiftF, cond_false, Pi.add_apply, Pi.single_eq_of_ne has]
      linarith
    · simp only [shiftF, cond_true, Pi.sub_apply, Pi.single_eq_of_ne has]
      linarith

theorem cns_lowK_shiftV (ε : Fin n → Bool) (μ : Fin n → ℝ) (s : Fin n) :
    lowK ε (shiftF false μ s) = lowK ε μ + HW.stdWt n s := by
  funext a
  simp only [lowK, shiftF, cond_false, HW.stdWt, Pi.add_apply, Pi.sub_apply]
  ring

theorem cns_lowK_shiftVd (ε : Fin n → Bool) (μ : Fin n → ℝ) (s : Fin n) :
    lowK ε (shiftF true μ s) = lowK ε μ + HW.dualWt n s := by
  funext a
  simp only [lowK, shiftF, cond_true, HW.dualWt, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  ring

private theorem gap_lemma {ν : Fin n → ℝ} (h : S7.IsHCParam ν) :
    ∀ d : ℕ, ∀ a b : Fin n, b.val = a.val + d → (d : ℝ) ≤ ν a - ν b := by
  intro d
  induction d with
  | zero =>
    intro a b hab
    have : a = b := Fin.ext (by omega)
    subst this
    simp
  | succ d ih =>
    intro a b hab
    have hc : a.val + d < n := by omega
    have h1 := ih a ⟨a.val + d, hc⟩ rfl
    have hcb : (⟨a.val + d, hc⟩ : Fin n) < b := Fin.lt_iff_val_lt_val.mpr (by simp only; omega)
    have hlt := h.1 hcb
    obtain ⟨m1, hm1⟩ := h.2 b
    obtain ⟨m2, hm2⟩ := h.2 ⟨a.val + d, hc⟩
    have hint : ν ⟨a.val + d, hc⟩ - ν b = ((m2 - m1 : ℤ) : ℝ) := by push_cast; linarith
    have h0 : (0 : ℤ) < m2 - m1 := by
      have : (0 : ℝ) < ((m2 - m1 : ℤ) : ℝ) := by rw [← hint]; linarith
      exact_mod_cast this
    have h2 : (1 : ℝ) ≤ ν ⟨a.val + d, hc⟩ - ν b := by
      rw [hint]
      exact_mod_cast (by omega : (1 : ℤ) ≤ m2 - m1)
    push_cast
    linarith

private theorem lowK_diff_lemma_2 (ε : Fin n → Bool) (ν : Fin n → ℝ) (a b : Fin n) :
    lowK ε ν b - lowK ε ν a = ν b - ν a + (∑ c : Fin n,
      (((if b < c ∧ ε c ≠ ε b then 1 else 0 : ℝ) - (if c < b ∧ ε c ≠ ε b then 1 else 0)) -
        ((if b < c ∧ ε c = ε b then 1 else 0 : ℝ) - (if c < b ∧ ε c = ε b then 1 else 0)) -
      (((if a < c ∧ ε c ≠ ε a then 1 else 0 : ℝ) - (if c < a ∧ ε c ≠ ε a then 1 else 0)) -
        ((if a < c ∧ ε c = ε a then 1 else 0 : ℝ) - (if c < a ∧ ε c = ε a then 1 else 0))))) / 2 := by
  simp only [lowK, rhoN, rhoC, Pi.add_apply, Pi.sub_apply, Finset.card_filter, Finset.sum_sub_distrib]
  push_cast
  ring

private theorem term_lemma_3 {ε : Fin n → Bool} {a b : Fin n} (he : ε a = ε b) (hab : a < b) (c : Fin n) :
    (((if b < c ∧ ε c ≠ ε b then 1 else 0 : ℝ) - (if c < b ∧ ε c ≠ ε b then 1 else 0)) -
        ((if b < c ∧ ε c = ε b then 1 else 0 : ℝ) - (if c < b ∧ ε c = ε b then 1 else 0)) -
      (((if a < c ∧ ε c ≠ ε a then 1 else 0 : ℝ) - (if c < a ∧ ε c ≠ ε a then 1 else 0)) -
        ((if a < c ∧ ε c = ε a then 1 else 0 : ℝ) - (if c < a ∧ ε c = ε a then 1 else 0)))) ≤
      ((if a < c ∧ c ≤ b then 1 else 0 : ℝ) + (if a ≤ c ∧ c < b then 1 else 0)) ∧
    (ε c = ε a → (((if b < c ∧ ε c ≠ ε b then 1 else 0 : ℝ) - (if c < b ∧ ε c ≠ ε b then 1 else 0)) -
        ((if b < c ∧ ε c = ε b then 1 else 0 : ℝ) - (if c < b ∧ ε c = ε b then 1 else 0)) -
      (((if a < c ∧ ε c ≠ ε a then 1 else 0 : ℝ) - (if c < a ∧ ε c ≠ ε a then 1 else 0)) -
        ((if a < c ∧ ε c = ε a then 1 else 0 : ℝ) - (if c < a ∧ ε c = ε a then 1 else 0)))) =
      ((if a < c ∧ c ≤ b then 1 else 0 : ℝ) + (if a ≤ c ∧ c < b then 1 else 0))) := by
  rw [Fin.lt_iff_val_lt_val] at hab
  by_cases e : ε c = ε a
  · have e' : ε c = ε b := e.trans he
    refine ⟨?_, fun _ => ?_⟩
    all_goals
      simp only [e', he, ne_eq, not_true_eq_false, and_false, and_true, if_false, if_true,
        Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val]
      split_ifs <;> first | (exfalso; omega) | norm_num
  · have e' : ¬ ε c = ε b := fun h => e (h.trans he.symm)
    refine ⟨?_, fun h => absurd h e⟩
    simp only [e, e', ne_eq, not_false_eq_true, and_false, and_true, if_false, if_true,
      Fin.lt_iff_val_lt_val, Fin.le_iff_val_le_val]
    split_ifs <;> first | (exfalso; omega) | norm_num

private theorem sumR_lemma_4 {a b : Fin n} (hab : a < b) :
    ∑ c : Fin n, ((if a < c ∧ c ≤ b then 1 else 0 : ℝ) + (if a ≤ c ∧ c < b then 1 else 0)) = 2 * ((b.val - a.val : ℕ) : ℝ) := by
  rw [Finset.sum_add_distrib, Finset.sum_boole, Finset.sum_boole]
  have h1 : (Finset.univ.filter fun c : Fin n => a < c ∧ c ≤ b) = Finset.Ioc a b := by
    ext
    simp
  have h2 : (Finset.univ.filter fun c : Fin n => a ≤ c ∧ c < b) = Finset.Ico a b := by
    ext
    simp
  rw [h1, h2, Fin.card_Ioc, Fin.card_Ico]
  ring

theorem cns_hc_of_dom {ε : Fin n → Bool} (he : ∀ a b, ε a = ε b) {ν : Fin n → ℝ}
    (hint : ∀ a, ∃ m : ℤ, ν a - ((n : ℝ) - 1) / 2 = m) (hdom : HW.KDom ε (lowK ε ν)) : S7.IsHCParam ν := by
  classical
  refine ⟨fun a b hab => ?_, hint⟩
  have hd := lowK_diff_lemma_2 ε ν a b
  have hs := Finset.sum_congr rfl fun c (_ : c ∈ Finset.univ) => (term_lemma_3 (he a b) hab c).2 (he c a)
  rw [sumR_lemma_4 hab] at hs
  have hk := hdom a b hab (he a b)
  have hba : (1 : ℝ) ≤ ((b.val - a.val : ℕ) : ℝ) := by
    have := Fin.lt_iff_val_lt_val.mp hab
    exact_mod_cast (by omega : 1 ≤ b.val - a.val)
  linarith

theorem cns_dom_of_hc {ε : Fin n → Bool} {ν : Fin n → ℝ} (h : S7.IsHCParam ν) : HW.KDom ε (lowK ε ν) := by
  classical
  intro a b hab he
  have hd := lowK_diff_lemma_2 ε ν a b
  have hs := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => (term_lemma_3 he hab c).1
  rw [sumR_lemma_4 hab] at hs
  have hg := gap_lemma h (b.val - a.val) a b (by have := Fin.lt_iff_val_lt_val.mp hab; omega)
  linarith

theorem cns_kfin_fd {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    {ε : Fin n → Bool} (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : PI.UpqRep.IsKFin ε σ v := ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩

theorem cns_orth_sum {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] {ι : Type*} (Sm : Finset ι)
    {V : ι → Type*} [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace ℂ (V i)] (j : ∀ i, V i →ₗ[ℂ] E)
    (hI : ∀ i ∈ Sm, ∀ v w, inner ℂ (j i v) (j i w) = inner ℂ v w)
    (hO : ∀ i ∈ Sm, ∀ i' ∈ Sm, i ≠ i' → ∀ v v', inner ℂ (j i v) (j i' v') = 0) (b c : ∀ i, V i) :
    inner ℂ (∑ i ∈ Sm, j i (b i)) (∑ i ∈ Sm, j i (c i)) = ∑ i ∈ Sm, inner ℂ (b i) (c i) := by
  rw [sum_inner]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [inner_sum, Finset.sum_eq_single i]
  · exact hI i hi _ _
  · intro i' hi' hne
    exact hO i hi i' hi' (Ne.symm hne) _ _
  · intro h
    exact absurd hi h

theorem cns_key_std {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ) (k : S7.KG ε)
    (F G : PiLp 2 (fun _ : Fin n => T.V)) :
    inner ℂ G (HW.tensOp T (HW.stdRho ε) k F) =
      ∑ c, inner ℂ (G c) (tensGrp false (fun _ => T.op k) (S7.toMK k) (fun d => F d) c) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  unfold HW.tensOp HW.tensL HW.piIn tensGrp
  simp [Pi.single_apply]
  rfl

theorem cns_inv_entry {ε : Fin n → Bool} (k : S7.KG ε) (c d : Fin n) :
    (S7.toMK k)⁻¹ d c = star (S7.toMK k c d) := by
  have hu : S7.toMK k ∈ unitary (Matrix (Fin n) (Fin n) ℂ) := k.2.1
  rw [Matrix.inv_eq_left_inv (Unitary.star_mul_self_of_mem hu), Matrix.star_apply]

theorem cns_key_dual {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ) (k : S7.KG ε)
    (F G : PiLp 2 (fun _ : Fin n => T.V)) :
    inner ℂ G (HW.tensOp T (HW.rhoDual ε) k F) =
      ∑ c, inner ℂ (G c) (tensGrp true (fun _ => T.op k) (S7.toMK k) (fun d => F d) c) := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  unfold HW.tensOp HW.tensL HW.piIn tensGrp
  simp [Pi.single_apply]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [cns_inv_entry]
  rfl

theorem cns_zuck_cpt {ε : Fin n → Bool} (hpq : pOf ε = 0 ∨ qOf ε = 0) {μ : Fin n → ℝ} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hμ : PI.UpqRep.IsHCParam μ) (hd : PI.UpqRep.IsDS ε μ σ) :
    ∃ X : PI.ZuckTensor.TensorDS n ε μ H σ, ∀ s, s ∈ X.Sm ↔ PI.UpqRep.IsHCParam (μ + Pi.single s 1) := by
  classical
  have he := cmpt_eps_eq hpq
  have hμ' : S7.IsHCParam μ := hμ
  obtain ⟨T⟩ := HW.kType_exists ε μ hμ'
  obtain ⟨-, -, U0, hU0⟩ := compact_isDS_unique hpq hμ' hd T
  haveI : FiniteDimensional ℂ H := LinearEquiv.finiteDimensional U0.toLinearEquiv
  have hdat : ∀ s, ∃ lam' : Fin n → ℝ, ∃ T' : S7.KType ε (lowK ε lam'),
      ∃ σ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V), S7.IsHCParam lam' ∧ Formalism.MainNotions.S.IsDS ε lam' σ' ∧
        (∀ k, σ' (S7.toMK k) = T'.op k) ∧ (S7.IsHCParam (shiftF false μ s) → lam' = shiftF false μ s) := by
    intro s
    by_cases hs : S7.IsHCParam (shiftF false μ s)
    · obtain ⟨T'⟩ := HW.kType_exists ε _ hs
      obtain ⟨σ', h1, -, h3⟩ := isDS_compact hpq hs T'
      exact ⟨_, T', σ', hs, h1, h3, fun _ => rfl⟩
    · obtain ⟨σ', h1, -, h3⟩ := isDS_compact hpq hμ' T
      exact ⟨μ, T, σ', hμ', h1, h3, fun h => absurd h hs⟩
  choose lamS Ts σs hHC hDS hσT hsh using hdat
  obtain ⟨hP1, hP2, hP3⟩ := HW.pieriStd n ε (lowK ε μ) T
  have hSm : ∀ s, s ∈ univ.filter (fun s => S7.IsHCParam (shiftF false μ s)) ↔
      HW.KDom ε (lowK ε μ + HW.stdWt n s) := by
    intro s
    rw [mem_filter, ← cns_lowK_shiftV]
    exact ⟨fun h => cns_dom_of_hc h.2, fun h => ⟨mem_univ _, cns_hc_of_dom he (cns_shift_int false hμ' s) h⟩⟩
  have hΛs : ∀ s ∈ univ.filter (fun s => S7.IsHCParam (shiftF false μ s)),
      lowK ε (lamS s) = lowK ε μ + HW.stdWt n s := fun s hs => by
    rw [hsh s (mem_filter.1 hs).2, cns_lowK_shiftV]
  obtain ⟨j, hjI, hjE, hjO, hjS⟩ := cns_cpt_dec T (HW.stdRho ε) LinearMap.id (HW.stdRho_cont ε)
    (HW.stdRho_hasDeriv ε) (HW.stdWt n) (HW.stdWt_injective n) hP1 hP2 hP3 _ hSm (fun s => lowK ε (lamS s)) hΛs Ts
  refine ⟨{ Sm := univ.filter (fun s => S7.IsHCParam (shiftF false μ s))
            Hs := fun s => (Ts s).V
            σs := σs
            ds := ?_, inequiv := ?_, toSum := ?_, ofSum := ?_ }, ?_⟩
  · intro s hs
    have hs' := (mem_filter.1 hs).2
    refine ⟨hs', ?_⟩
    have e : (μ + Pi.single s 1) = lamS s := (hsh s hs').symm
    rw [e]
    exact hDS s
  · rintro s hs s' hs' hne ⟨V, hV⟩
    apply hne
    obtain ⟨S, hS⟩ := (hDS s).2.2.2.2.2.1
    have h1 := puniq_isKTypeOf_map V (fun g hg x => hV g (puniq_kset hg) x) hS
    obtain ⟨S', hS'⟩ := (hDS s').2.2.2.2.2.1
    have htop := (compact_isDS_unique hpq (hHC s') (hDS s') (Ts s')).2.1 S' hS'
    rw [htop] at hS'
    have e := cns_kt_weight_eq h1 hS'
    have e2 : lamS s = lamS s' := by
      funext a
      have := congrFun e a
      simp only [Formalism.QuantumDeterminants.lowK, PI.UpqRep.lowK, lowK, Pi.add_apply, Pi.sub_apply] at this
      linarith
    rw [hsh s (mem_filter.1 hs).2, hsh s' (mem_filter.1 hs').2] at e2
    exact cns_shift_inj false μ e2
  · intro v w x y hv hw
    obtain ⟨a, ha⟩ := hjS (WithLp.toLp 2 (fun d => x d • U0.symm v))
    obtain ⟨b, hb⟩ := hjS (WithLp.toLp 2 (fun c => y c • U0.symm w))
    refine ⟨{s // s ∈ univ.filter (fun s => S7.IsHCParam (shiftF false μ s))}, Finset.Subtype.fintype _, fun i => i.1,
      fun i => a i.1, fun i => b i.1, fun i => ⟨i.2, cns_kfin_fd _ _, cns_kfin_fd _ _⟩, fun g hg => ?_⟩
    obtain ⟨k, rfl⟩ := S7.exists_toMK (cmpt_inUJ_Kset he hg)
    simp only [hσT]
    rw [← U0.apply_symm_apply v, ← U0.apply_symm_apply w, ← hU0, LinearIsometryEquiv.inner_map_map,
      cns_coefV (fun _ => T.op k) (S7.toMK k) (U0.symm v) (U0.symm w) x y]
    have h1 := cns_key_std T k (WithLp.toLp 2 (fun d => x d • U0.symm v)) (WithLp.toLp 2 (fun c => y c • U0.symm w))
    simp only [PiLp.toLp_apply] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h1, ha, hb, map_sum,
      show (∑ s ∈ univ.filter (fun s => S7.IsHCParam (shiftF false μ s)), HW.tensOp T (HW.stdRho ε) k (j s (a s))) =
        ∑ s ∈ univ.filter (fun s => S7.IsHCParam (shiftF false μ s)), j s ((Ts s).op k (a s)) from
        Finset.sum_congr rfl fun s hs => (hjE s hs k (a s)).symm,
      cns_orth_sum _ j hjI hjO b (fun s => (Ts s).op k (a s)), ← Finset.sum_coe_sort]
    all_goals rfl
  · intro s hs v w hv hw
    refine ⟨Fin n × Fin n, inferInstance, fun p => U0 ((j s v) p.2), fun p => U0 ((j s w) p.1),
      fun p => Pi.single p.2 1, fun p => Pi.single p.1 1, fun p => ⟨cns_kfin_fd _ _, cns_kfin_fd _ _⟩,
      fun g hg => ?_⟩
    obtain ⟨k, rfl⟩ := S7.exists_toMK (cmpt_inUJ_Kset he hg)
    dsimp only
    rw [hσT, ← hjI s hs, hjE s hs, cns_key_std, cns_expandV]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← hU0, LinearIsometryEquiv.inner_map_map]
  · intro s
    exact ⟨fun hs => (mem_filter.1 hs).2, fun hs => mem_filter.2 ⟨mem_univ _, hs⟩⟩

theorem cns_zuckd_cpt {ε : Fin n → Bool} (hpq : pOf ε = 0 ∨ qOf ε = 0) {μ : Fin n → ℝ} {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hμ : PI.UpqRep.IsHCParam μ) (hd : PI.UpqRep.IsDS ε μ σ) :
    ∃ X : PI.ZuckTensor.TensorDSd n ε μ H σ, ∀ s, s ∈ X.Sm ↔ PI.UpqRep.IsHCParam (μ - Pi.single s 1) := by
  classical
  have he := cmpt_eps_eq hpq
  have hμ' : S7.IsHCParam μ := hμ
  obtain ⟨T⟩ := HW.kType_exists ε μ hμ'
  obtain ⟨-, -, U0, hU0⟩ := compact_isDS_unique hpq hμ' hd T
  haveI : FiniteDimensional ℂ H := LinearEquiv.finiteDimensional U0.toLinearEquiv
  have hdat : ∀ s, ∃ lam' : Fin n → ℝ, ∃ T' : S7.KType ε (lowK ε lam'),
      ∃ σ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V), S7.IsHCParam lam' ∧ Formalism.MainNotions.S.IsDS ε lam' σ' ∧
        (∀ k, σ' (S7.toMK k) = T'.op k) ∧ (S7.IsHCParam (shiftF true μ s) → lam' = shiftF true μ s) := by
    intro s
    by_cases hs : S7.IsHCParam (shiftF true μ s)
    · obtain ⟨T'⟩ := HW.kType_exists ε _ hs
      obtain ⟨σ', h1, -, h3⟩ := isDS_compact hpq hs T'
      exact ⟨_, T', σ', hs, h1, h3, fun _ => rfl⟩
    · obtain ⟨σ', h1, -, h3⟩ := isDS_compact hpq hμ' T
      exact ⟨μ, T, σ', hμ', h1, h3, fun h => absurd h hs⟩
  choose lamS Ts σs hHC hDS hσT hsh using hdat
  obtain ⟨hP1, hP2, hP3⟩ := HW.pieriDual n ε (lowK ε μ) T
  rw [← HW.dualD_units] at hP1 hP2 hP3
  have hSm : ∀ s, s ∈ univ.filter (fun s => S7.IsHCParam (shiftF true μ s)) ↔
      HW.KDom ε (lowK ε μ + HW.dualWt n s) := by
    intro s
    rw [mem_filter, ← cns_lowK_shiftVd]
    exact ⟨fun h => cns_dom_of_hc h.2, fun h => ⟨mem_univ _, cns_hc_of_dom he (cns_shift_int true hμ' s) h⟩⟩
  have hΛs : ∀ s ∈ univ.filter (fun s => S7.IsHCParam (shiftF true μ s)),
      lowK ε (lamS s) = lowK ε μ + HW.dualWt n s := fun s hs => by
    rw [hsh s (mem_filter.1 hs).2, cns_lowK_shiftVd]
  obtain ⟨j, hjI, hjE, hjO, hjS⟩ := cns_cpt_dec T (HW.rhoDual ε) HW.dualD (HW.continuous_rhoDual ε)
    (HW.hasDeriv_rhoDual ε) (HW.dualWt n) HW.dualWt_injective hP1 hP2 hP3 _ hSm (fun s => lowK ε (lamS s)) hΛs Ts
  refine ⟨{ Sm := univ.filter (fun s => S7.IsHCParam (shiftF true μ s))
            Hs := fun s => (Ts s).V
            σs := σs
            ds := ?_, inequiv := ?_, toSum := ?_, ofSum := ?_ }, ?_⟩
  · intro s hs
    have hs' := (mem_filter.1 hs).2
    refine ⟨hs', ?_⟩
    have e : (μ - Pi.single s 1) = lamS s := (hsh s hs').symm
    rw [e]
    exact hDS s
  · rintro s hs s' hs' hne ⟨V, hV⟩
    apply hne
    obtain ⟨S, hS⟩ := (hDS s).2.2.2.2.2.1
    have h1 := puniq_isKTypeOf_map V (fun g hg x => hV g (puniq_kset hg) x) hS
    obtain ⟨S', hS'⟩ := (hDS s').2.2.2.2.2.1
    have htop := (compact_isDS_unique hpq (hHC s') (hDS s') (Ts s')).2.1 S' hS'
    rw [htop] at hS'
    have e := cns_kt_weight_eq h1 hS'
    have e2 : lamS s = lamS s' := by
      funext a
      have := congrFun e a
      simp only [Formalism.QuantumDeterminants.lowK, PI.UpqRep.lowK, lowK, Pi.add_apply, Pi.sub_apply] at this
      linarith
    rw [hsh s (mem_filter.1 hs).2, hsh s' (mem_filter.1 hs').2] at e2
    exact cns_shift_inj true μ e2
  · intro v w x y hv hw
    obtain ⟨a, ha⟩ := hjS (WithLp.toLp 2 (fun d => star (y d) • U0.symm v))
    obtain ⟨b, hb⟩ := hjS (WithLp.toLp 2 (fun c => star (x c) • U0.symm w))
    refine ⟨{s // s ∈ univ.filter (fun s => S7.IsHCParam (shiftF true μ s))}, Finset.Subtype.fintype _, fun i => i.1,
      fun i => a i.1, fun i => b i.1, fun i => ⟨i.2, cns_kfin_fd _ _, cns_kfin_fd _ _⟩, fun g hg => ?_⟩
    obtain ⟨k, rfl⟩ := S7.exists_toMK (cmpt_inUJ_Kset he hg)
    simp only [hσT]
    rw [← U0.apply_symm_apply v, ← U0.apply_symm_apply w, ← hU0, LinearIsometryEquiv.inner_map_map,
      cns_coefVd (fun _ => T.op k) (S7.toMK k) (U0.symm v) (U0.symm w) x y]
    have h1 := cns_key_dual T k (WithLp.toLp 2 (fun d => star (y d) • U0.symm v))
      (WithLp.toLp 2 (fun c => star (x c) • U0.symm w))
    simp only [PiLp.toLp_apply] at h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← h1, ha, hb, map_sum,
      show (∑ s ∈ univ.filter (fun s => S7.IsHCParam (shiftF true μ s)), HW.tensOp T (HW.rhoDual ε) k (j s (a s))) =
        ∑ s ∈ univ.filter (fun s => S7.IsHCParam (shiftF true μ s)), j s ((Ts s).op k (a s)) from
        Finset.sum_congr rfl fun s hs => (hjE s hs k (a s)).symm,
      cns_orth_sum _ j hjI hjO b (fun s => (Ts s).op k (a s)), ← Finset.sum_coe_sort]
    all_goals rfl
  · intro s hs v w hv hw
    refine ⟨Fin n × Fin n, inferInstance, fun p => U0 ((j s v) p.2), fun p => U0 ((j s w) p.1),
      fun p => Pi.single p.1 1, fun p => Pi.single p.2 1, fun p => ⟨cns_kfin_fd _ _, cns_kfin_fd _ _⟩,
      fun g hg => ?_⟩
    obtain ⟨k, rfl⟩ := S7.exists_toMK (cmpt_inUJ_Kset he hg)
    dsimp only
    rw [hσT, ← hjI s hs, hjE s hs, cns_key_dual, cns_expandVd]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← hU0, LinearIsometryEquiv.inner_map_map]
  · intro s
    exact ⟨fun hs => (mem_filter.1 hs).2, fun hs => mem_filter.2 ⟨mem_univ _, hs⟩⟩

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2

open MeasureTheory

def ZuckG : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    PI.UpqRep.IsHCParam μ → PI.UpqRep.IsDS ε μ σ → ∀ h : ℝ, PI.ZuckTensor.GapAtLeast ε μ h → thrS ε + 1 < h →
      ∃ X : PI.ZuckTensor.TensorDS n ε μ H σ, ∀ s, s ∈ X.Sm ↔ PI.UpqRep.IsHCParam (μ + Pi.single s 1)

def ZuckDualG : Prop :=
  ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    PI.UpqRep.IsHCParam μ → PI.UpqRep.IsDS ε μ σ → ∀ h : ℝ, PI.ZuckTensor.GapAtLeast ε μ h → thrS ε + 1 < h →
      ∃ X : PI.ZuckTensor.TensorDSd n ε μ H σ, ∀ s, s ∈ X.Sm ↔ PI.UpqRep.IsHCParam (μ - Pi.single s 1)

theorem zuckG : ZuckG := by
  intro n ε μ H _ _ _ σ hμ hd h hG hth
  by_cases hq : 1 ≤ S7.q0 ε
  · exact cns_zuck_nc hq hμ hd hG hth
  · have h0 : S7.q0 ε = 0 := by omega
    have hpq : pOf ε = 0 ∨ qOf ε = 0 := by
      simp only [S7.q0] at h0
      omega
    exact cns_zuck_cpt hpq hμ hd

theorem zuckDualG : ZuckDualG := by
  intro n ε μ H _ _ _ σ hμ hd h hG hth
  by_cases hq : 1 ≤ S7.q0 ε
  · exact cns_zuckd_nc hq hμ hd hG hth
  · have h0 : S7.q0 ε = 0 := by omega
    have hpq : pOf ε = 0 ∨ qOf ε = 0 := by
      simp only [S7.q0] at h0
      omega
    exact cns_zuckd_cpt hpq hμ hd

end ReciprocityTheory.ChartRestriction.DS.G2
end
end

noncomputable section

open MeasureTheory

namespace ReciprocityTheory.ChartRestriction.DS.G2

theorem zuckerman_tensor_exists :
    ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
      PI.UpqRep.IsHCParam μ → PI.UpqRep.IsDS ε μ σ → ∀ h : ℝ, PI.ZuckTensor.GapAtLeast ε μ h → thrS ε + 1 < h →
        ∃ X : PI.ZuckTensor.TensorDS n ε μ H σ, ∀ s, s ∈ X.Sm ↔ PI.UpqRep.IsHCParam (μ + Pi.single s 1) :=
  zuckG

theorem zuckerman_dual_tensor_exists :
    ∀ (n : ℕ) (ε : Fin n → Bool) (μ : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      [CompleteSpace H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
      PI.UpqRep.IsHCParam μ → PI.UpqRep.IsDS ε μ σ → ∀ h : ℝ, PI.ZuckTensor.GapAtLeast ε μ h → thrS ε + 1 < h →
        ∃ X : PI.ZuckTensor.TensorDSd n ε μ H σ, ∀ s, s ∈ X.Sm ↔ PI.UpqRep.IsHCParam (μ - Pi.single s 1) :=
  zuckDualG

variable {n : ℕ}

section FdCons

open ReciprocityTheory.ChartRestriction.DS.S7

theorem formal_degree_constant_measure (n : ℕ) (ε : Fin n → Bool) : ∃ c : ℝ, 0 < c ∧
    ∀ (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H),
      Formalism.QuantumDeterminants.IsHCParam lam → Formalism.MainNotions.S.IsDS ε lam σ → ∀ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε lam h →
      thrS ε + 1 < h → 1 ≤ pOf ε → 1 ≤ qOf ε →
      (∀ μ : Fin n → ℝ, IsHCParam μ → GapAtLeast ε μ h →
        ∃ (T : KType ε (lowK ε μ)) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)), IsPsiFor ε μ T Ψ) →
      v ≠ 0 → Formalism.MainNotions.S.fdegOf (Formalism.REAL.muG ε) σ v = c * Formalism.QuantumDeterminants.fdegHC lam :=
  fdCons_muG n ε

end FdCons

end ReciprocityTheory.ChartRestriction.DS.G2
