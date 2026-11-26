module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IdxRatioConjSub
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmRowExp

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlueBackOf
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.GlueFwdOf
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.HermitianW0SpanZero
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MmIntOfGeneric
noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section G3

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def GlueFwd (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    ∀ Λ₂ : Submodule M.L.O V, H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ →
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' →
    ∃ θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩, IsomD H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ θ ∧
      ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H _ m₂ ↔ GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' m₁ m₂

def GlueBack (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    IsUnit (H.Dl f₂ f₂' (r + 1)) → MMInt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ →
    ∀ θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩, IsomD H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ θ →
    ∃ Λ₂ : Submodule M.L.O V, H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ ∧
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' ∧
      ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H _ m₂ ↔ GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' m₁ m₂

def GlueInj (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    ∀ Λ₂ Λ₂' : Submodule M.L.O V, H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ →
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' → H.IsGeneric ⟨Λ₂', f₂, f₂', t₁.T, t₁.T'⟩ →
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂' φ φ' →
      (∀ m₁ m₂, GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' m₁ m₂ ↔
        GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂' φ φ' m₁ m₂) → Λ₂ = Λ₂'

theorem mmInt_of_generic {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (Λ₂ : Submodule M.L.O V) (f₂ f₂' : Fin (r + 1) → V) (T T' : F)
    (hg : H.IsGeneric ⟨Λ₂, f₂, f₂', T, T'⟩) : MMInt H (⟨⊥, f₂, f₂', T, T'⟩ : Term V M r) := by
  have hsub : MMo H (⟨⊥, f₂, f₂', T, T'⟩ : Term V M r) ≤ Λ₂ := by
    refine (Submodule.span_le (R := M.L.O)).2 ?_
    rintro _ ⟨a, rfl⟩
    exact hg.2.1 a
  intro m hm m' hm'
  exact (hg.1.1.2.2 m).1 (hsub hm) m' (hsub hm')

theorem dd_ext {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    {t₁ t₂ : Term V M r} (θ θ' : DDt H t₁ ≃ₗ[M.L.O] DDt H t₂)
    (h : ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H t₂ m₂ ↔ θ' (ddMk H t₁ m₁) = ddMk H t₂ m₂) : θ = θ' := by
  apply LinearEquiv.ext
  intro x
  obtain ⟨m₁, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨m₂, hm₂⟩ := Submodule.Quotient.mk_surjective _ (θ (Submodule.Quotient.mk m₁))
  have h₁ : θ (ddMk H t₁ m₁) = ddMk H t₂ m₂ := hm₂.symm
  exact h₁.trans ((h m₁ m₂).1 h₁).symm

theorem glue_of (M : Model F E) (r n : ℕ) (hF : GlueFwd M r n) (hB : GlueBack M r n) (hI : GlueInj M r n) :
    Glue M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hyp
  have fw := hF V H hn t₁ f₂ f₂' φ φ' hyp
  have bk := hB V H hn t₁ f₂ f₂' φ φ' hyp
  have inj := hI V H hn t₁ f₂ f₂' φ φ' hyp
  let toθ : {Λ₂ : Submodule M.L.O V // H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ ∧
      ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ'} →
      {θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ //
        IsUnit (H.Dl f₂ f₂' (r + 1)) ∧ MMInt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ ∧
          IsomD H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ θ} :=
    fun x => ⟨(fw x.1 x.2.1 x.2.2).choose, x.2.1.1.2.2.2.1, mmInt_of_generic H x.1 f₂ f₂' t₁.T t₁.T' x.2.1,
      (fw x.1 x.2.1 x.2.2).choose_spec.1⟩
  have toθ_spec : ∀ x m₁ m₂, (toθ x).1 (ddMk H t₁ m₁) = ddMk H _ m₂ ↔
      GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ x.1 φ φ' m₁ m₂ :=
    fun x => (fw x.1 x.2.1 x.2.2).choose_spec.2
  have hinj : Function.Injective toθ := by
    intro x y hxy
    apply Subtype.ext
    refine inj x.1 y.1 x.2.1 x.2.2 y.2.1 y.2.2 fun m₁ m₂ => ?_
    rw [← toθ_spec x, ← toθ_spec y, hxy]
  have hsurj : Function.Surjective toθ := by
    intro θ
    obtain ⟨Λ₂, hg, hth, hrel⟩ := bk θ.2.1 θ.2.2.1 θ.1 θ.2.2.2
    refine ⟨⟨Λ₂, hg, hth⟩, Subtype.ext (dd_ext H _ _ fun m₁ m₂ => ?_)⟩
    rw [toθ_spec, hrel]
  exact ⟨Equiv.ofBijective toθ ⟨hinj, hsurj⟩, toθ_spec⟩

end G3

end Formalism.L2.SG.LsDatumA
end
end

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Psi

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}

theorem MMfam_mem_sup (t : Term V M r) (i : Fin (r + 1) ⊕ Fin (r + 1)) :
    H.MMfam t i ∈ H.Xp t.f ⊔ H.Xp t.f' := by
  have hf : ∀ a, t.f a ∈ H.Xp t.f ⊔ H.Xp t.f' := fun a =>
    Submodule.mem_sup_left (Submodule.subset_span ⟨a, rfl⟩)
  have hf' : ∀ a, t.f' a ∈ H.Xp t.f ⊔ H.Xp t.f' := fun a =>
    Submodule.mem_sup_right (Submodule.subset_span ⟨a, rfl⟩)
  unfold HermSp.MMfam
  rcases M.split with _ | g
  · rcases i with a | a
    · exact hf a
    · exact hf' a
  · rcases i with a | a
    · exact hf a
    · exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hf' a) (hf a))

theorem hermitian_W0_span_zero (t : Term V M r) {w m : V} (hw : w ∈ H.W0 t.f t.f')
    (hm : m ∈ Submodule.span E (Set.range (H.MMfam t))) : H.h w m = 0 := by
  have hle : Submodule.span E (Set.range (H.MMfam t)) ≤ H.Xp t.f ⊔ H.Xp t.f' :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact MMfam_mem_sup H t i)
  exact hw m (hle hm)

end Psi

end Formalism.L2.SG.LsDatumA
end
end

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Fwd

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

set_option maxHeartbeats 800000 in
theorem glueFwd_of (M : Model F E) (r n : ℕ) (hM : M.OK) (hC : CorrIso M r n) (hE : GlueEta M r) :
    GlueFwd M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hT Λ₂ hG₂ hTh
  set t₂ : Term V M r := { abelian₂ := Λ₂, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } with ht₂
  have memS : ∀ (t : Term V M r) (N : Submodule M.L.O V) (w : V),
      w ∈ ThSharp H t N ↔ (w ∈ H.W0 t.f t.f' ∧ ∀ n ∈ N, H.h w n ∈ M.L.O) :=
    fun _ _ _ => Iff.rfl
  have memL : ∀ (t : Term V M r) (w : V), w ∈ ThL H t ↔ (w ∈ t.abelian₂ ∧ w ∈ H.W0 t.f t.f') :=
    fun _ _ => Iff.rfl
  have hDl : IsUnit (H.Dl f₂ f₂' (r + 1)) := by
    obtain ⟨⟨_, _, _, hD, _⟩, _⟩ := hG₂
    exact hD
  have hG₁ : H.IsGeneric t₁ := by
    obtain ⟨h, -⟩ := id hT
    exact h
  obtain ⟨ψ, hψh, hψC⟩ := hC V H hn t₁ f₂ f₂' φ φ' hT hDl
  have key : ∀ (x : V) (hx : x ∈ H.W0 t₁.f t₁.f'), x ∈ t₁.abelian₂ ↔ (ψ ⟨x, hx⟩ : V) ∈ Λ₂ :=
    fun x hx => hTh x _ ((hψC x _).2 ⟨hx, rfl⟩)
  obtain ⟨η₁, hη₁a, hη₁b⟩ := hE hM V H t₁ hG₁
  obtain ⟨η₂, hη₂a, hη₂b⟩ := hE hM V H t₂ hG₂
  have fwd : ∀ (w : V) (hw : w ∈ ThSharp H t₁ (ThL H t₁)),
      (ψ ⟨w, ((memS _ _ _).1 hw).1⟩ : V) ∈ ThSharp H t₂ (ThL H t₂) := by
    intro w hw
    refine (memS _ _ _).2 ⟨(ψ _).2, ?_⟩
    intro n hn'
    obtain ⟨hnΛ, hnW⟩ := (memL _ _).1 hn'
    have h1 : (ψ (ψ.symm ⟨n, hnW⟩) : V) = n := by simp
    rw [← h1, hψh]
    refine ((memS _ _ _).1 hw).2 _ ((memL _ _).2 ⟨?_, (ψ.symm ⟨n, hnW⟩).2⟩)
    exact (key _ (ψ.symm ⟨n, hnW⟩).2).2 (by simpa [ht₂] using hnΛ)
  have bwd : ∀ (w : V) (hw : w ∈ ThSharp H t₂ (ThL H t₂)),
      (ψ.symm ⟨w, ((memS _ _ _).1 hw).1⟩ : V) ∈ ThSharp H t₁ (ThL H t₁) := by
    intro w hw
    refine (memS _ _ _).2 ⟨(ψ.symm _).2, ?_⟩
    intro n hn'
    obtain ⟨hnΛ, hnW⟩ := (memL _ _).1 hn'
    have h2 := hψh (ψ.symm ⟨w, ((memS _ _ _).1 hw).1⟩) ⟨n, hnW⟩
    simp only [LinearEquiv.apply_symm_apply] at h2
    rw [← h2]
    exact ((memS _ _ _).1 hw).2 _ ((memL _ _).2 ⟨(key n hnW).1 hnΛ, (ψ ⟨n, hnW⟩).2⟩)
  let e : ThSharp H t₁ (ThL H t₁) ≃ₗ[M.L.O] ThSharp H t₂ (ThL H t₂) :=
    { toFun := fun w => ⟨_, fwd w.1 w.2⟩
      invFun := fun w => ⟨_, bwd w.1 w.2⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        have h := congrArg Subtype.val
          (map_add ψ ⟨(a : V), ((memS _ _ _).1 a.2).1⟩ ⟨(b : V), ((memS _ _ _).1 b.2).1⟩)
        exact h
      map_smul' := by
        intro c a
        apply Subtype.ext
        have h := congrArg Subtype.val (map_smul ψ (c : E) ⟨(a : V), ((memS _ _ _).1 a.2).1⟩)
        exact h
      left_inv := by
        intro a
        apply Subtype.ext
        simp
      right_inv := by
        intro a
        apply Subtype.ext
        simp }
  have hPQ : Submodule.map (e : ThSharp H t₁ (ThL H t₁) →ₗ[M.L.O] ThSharp H t₂ (ThL H t₂))
      (Submodule.comap (ThSharp H t₁ (ThL H t₁)).subtype (ThL H t₁)) =
      Submodule.comap (ThSharp H t₂ (ThL H t₂)).subtype (ThL H t₂) := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨h1, -⟩ := (memL _ _).1 hy
      exact (memL _ _).2 ⟨(key _ _).1 h1, (ψ _).2⟩
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      obtain ⟨h1, -⟩ := (memL _ _).1 hx
      refine (memL _ _).2 ⟨?_, (ψ.symm ⟨(x : V), ((memS _ _ _).1 x.2).1⟩).2⟩
      exact (key _ (ψ.symm ⟨(x : V), ((memS _ _ _).1 x.2).1⟩).2).2 (by simpa [ht₂] using h1)
  let κ : DDW H t₁ (ThL H t₁) ≃ₗ[M.L.O] DDW H t₂ (ThL H t₂) := Submodule.Quotient.equiv _ _ e hPQ
  have hκ : ∀ w, κ (dwMk H t₁ (ThL H t₁) w) = dwMk H t₂ (ThL H t₂) (e w) := fun w => rfl
  have surj : ∀ m : MMsharp H t₁, ∃ w, η₁ (ddMk H t₁ m) = dwMk H t₁ (ThL H t₁) w := by
    intro m
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (η₁ (ddMk H t₁ m))
    exact ⟨w, hw.symm⟩
  have hh : ∀ a b : ThSharp H t₁ (ThL H t₁), H.h (e a : V) (e b : V) = H.h a b :=
    fun a b => hψh ⟨a, ((memS _ _ _).1 a.2).1⟩ ⟨b, ((memS _ _ _).1 b.2).1⟩
  refine ⟨(η₁.trans κ).trans η₂.symm, ?_, ?_⟩
  · intro x y x₂ y₂ hx hy
    obtain ⟨w, hw⟩ := surj x
    obtain ⟨w', hw'⟩ := surj y
    change η₂.symm (κ (η₁ (ddMk H t₁ x))) = _ at hx
    change η₂.symm (κ (η₁ (ddMk H t₁ y))) = _ at hy
    have hx' := (LinearEquiv.symm_apply_eq η₂).1 hx
    have hy' := (LinearEquiv.symm_apply_eq η₂).1 hy
    rw [hw, hκ] at hx'
    rw [hw', hκ] at hy'
    have a1 := hη₁b x y w w' hw hw'
    have a2 := hη₂b x₂ y₂ (e w) (e w') hx'.symm hy'.symm
    rw [hh] at a2
    have a3 := sub_mem a2 a1
    convert a3 using 1
    ring
  · intro m₁ m₂
    obtain ⟨w, hw⟩ := surj m₁
    have hmw : (m₁ : V) + w ∈ t₁.abelian₂ := (hη₁a m₁ w).1 hw
    change η₂.symm (κ (η₁ (ddMk H t₁ m₁))) = _ ↔ _
    rw [hw, hκ]
    constructor
    · intro h
      have h' := (LinearEquiv.symm_apply_eq η₂).1 h
      exact ⟨w, e w, (hψC _ _).2 ⟨((memS _ _ _).1 w.2).1, rfl⟩, hmw, (hη₂a m₂ (e w)).1 h'.symm⟩
    · rintro ⟨n₁, n₂, hc, h1, h2⟩
      obtain ⟨hn₁, hψn⟩ := (hψC n₁ n₂).1 hc
      have hd : n₁ - w ∈ H.W0 t₁.f t₁.f' := Submodule.sub_mem _ hn₁ ((memS _ _ _).1 w.2).1
      have hdL : n₁ - w ∈ t₁.abelian₂ := by
        have h4 := t₁.abelian₂.sub_mem h1 hmw
        simpa using h4
      have hψd : (ψ ⟨n₁ - w, hd⟩ : V) = n₂ - (e w : V) := by
        rw [← hψn]
        exact congrArg Subtype.val (map_sub ψ ⟨n₁, hn₁⟩ ⟨(w : V), ((memS _ _ _).1 w.2).1⟩)
      have h3 := (key _ hd).1 hdL
      rw [hψd] at h3
      have h5 := Λ₂.sub_mem h2 h3
      have h6 : (m₂ : V) + (e w : V) ∈ t₂.abelian₂ := by
        convert h5 using 1
        abel
      apply (LinearEquiv.symm_apply_eq η₂).2
      exact ((hη₂a m₂ (e w)).2 h6).symm

end Fwd

end Formalism.L2.SG.LsDatumA
end
end

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Back

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def GramMM (M : Model F E) (r n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V), Module.finrank E V = n →
  ∀ (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂'), LocalCountHypotheses H t₁ f₂ f₂' φ φ' →
    IsUnit (H.Dl f₂ f₂' (r + 1)) → IsUnit (H.gram (H.MMfam (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r))).det

def ThFG (M : Model F E) (r : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t : Term V M r), H.IsGeneric t → (ThL H t).FG

def ThSpan (M : Model F E) (r : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V) (t : Term V M r), H.IsGeneric t →
    Submodule.span E (ThL H t : Set V) = H.W0 t.f t.f'

set_option maxHeartbeats 800000 in
theorem glueBack_of (M : Model F E) (r n : ℕ) (hM : M.OK) (hC : CorrIso M r n) (hE : GlueEta M r) (hV : GlueConv M r)
    (hP : GenOfPrim M r n) (hG : GramMM M r n) (hFG : ThFG M r) (hS : ThSpan M r) : GlueBack M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hT hDl hMM θ hθ
  let t₀ : Term V M r := { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' }
  have memS : ∀ (t : Term V M r) (N : Submodule M.L.O V) (w : V),
      w ∈ ThSharp H t N ↔ (w ∈ H.W0 t.f t.f' ∧ ∀ n ∈ N, H.h w n ∈ M.L.O) :=
    fun _ _ _ => Iff.rfl
  have memL : ∀ (t : Term V M r) (w : V), w ∈ ThL H t ↔ (w ∈ t.abelian₂ ∧ w ∈ H.W0 t.f t.f') :=
    fun _ _ => Iff.rfl
  have hG₁ : H.IsGeneric t₁ := by
    obtain ⟨h, -⟩ := id hT
    exact h
  have hsd : ∀ x : V, x ∈ t₁.abelian₂ ↔ ∀ y ∈ t₁.abelian₂, H.h x y ∈ M.L.O := by
    obtain ⟨⟨⟨-, -, h⟩, -⟩, -⟩ := id hG₁
    exact h
  obtain ⟨ψ, hψh, hψC⟩ := hC V H hn t₁ f₂ f₂' φ φ' hT hDl
  obtain ⟨η₁, hη₁a, hη₁b⟩ := hE hM V H t₁ hG₁
  let g : ThL H t₁ →ₗ[M.L.O] V :=
    { toFun := fun x => (ψ ⟨x, ((memL _ _).1 x.2).2⟩ : V)
      map_add' := fun a b => by
        have h := congrArg Subtype.val
          (map_add ψ ⟨(a : V), ((memL _ _).1 a.2).2⟩ ⟨(b : V), ((memL _ _).1 b.2).2⟩)
        exact h
      map_smul' := fun c a => by
        have h := congrArg Subtype.val (map_smul ψ (c : E) ⟨(a : V), ((memL _ _).1 a.2).2⟩)
        exact h }
  have hg : ∀ y : ThL H t₁, g y = (ψ ⟨y, ((memL _ _).1 y.2).2⟩ : V) := fun _ => rfl
  obtain ⟨N₂, hN₂⟩ : ∃ N : Submodule M.L.O V, N = Submodule.map g ⊤ := ⟨_, rfl⟩
  have memN : ∀ v : V, v ∈ N₂ ↔ ∃ y, g y = v := by
    intro v
    rw [hN₂]
    simp only [Submodule.mem_map, Submodule.mem_top, true_and]
  have keyN : ∀ (x : V) (hx : x ∈ H.W0 t₁.f t₁.f'), x ∈ t₁.abelian₂ ↔ (ψ ⟨x, hx⟩ : V) ∈ N₂ := by
    intro x hx
    constructor
    · intro h
      exact (memN _).2 ⟨⟨x, (memL _ _).2 ⟨h, hx⟩⟩, rfl⟩
    · intro h
      obtain ⟨y, hy⟩ := (memN _).1 h
      rw [hg] at hy
      have h2 : (y : V) = x := congrArg Subtype.val (ψ.injective (Subtype.ext hy))
      rw [← h2]
      exact ((memL _ _).1 y.2).1
  have fwd : ∀ (w : V) (hw : w ∈ ThSharp H t₁ (ThL H t₁)),
      (ψ ⟨w, ((memS _ _ _).1 hw).1⟩ : V) ∈ ThSharp H t₀ N₂ := by
    intro w hw
    refine (memS _ _ _).2 ⟨(ψ _).2, ?_⟩
    intro n hn'
    obtain ⟨y, rfl⟩ := (memN _).1 hn'
    rw [hg, hψh]
    exact ((memS _ _ _).1 hw).2 _ y.2
  have bwd : ∀ (w : V) (hw : w ∈ ThSharp H t₀ N₂),
      (ψ.symm ⟨w, ((memS _ _ _).1 hw).1⟩ : V) ∈ ThSharp H t₁ (ThL H t₁) := by
    intro w hw
    refine (memS _ _ _).2 ⟨(ψ.symm _).2, ?_⟩
    intro n hn'
    obtain ⟨hnΛ, hnW⟩ := (memL _ _).1 hn'
    have h2 := hψh (ψ.symm ⟨w, ((memS _ _ _).1 hw).1⟩) ⟨n, hnW⟩
    simp only [LinearEquiv.apply_symm_apply] at h2
    rw [← h2]
    exact ((memS _ _ _).1 hw).2 _ ((memN _).2 ⟨⟨n, hn'⟩, rfl⟩)
  let e : ThSharp H t₁ (ThL H t₁) ≃ₗ[M.L.O] ThSharp H t₀ N₂ :=
    { toFun := fun w => ⟨_, fwd w.1 w.2⟩
      invFun := fun w => ⟨_, bwd w.1 w.2⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        have h := congrArg Subtype.val
          (map_add ψ ⟨(a : V), ((memS _ _ _).1 a.2).1⟩ ⟨(b : V), ((memS _ _ _).1 b.2).1⟩)
        exact h
      map_smul' := by
        intro c a
        apply Subtype.ext
        have h := congrArg Subtype.val (map_smul ψ (c : E) ⟨(a : V), ((memS _ _ _).1 a.2).1⟩)
        exact h
      left_inv := by
        intro a
        apply Subtype.ext
        simp
      right_inv := by
        intro a
        apply Subtype.ext
        simp }
  have hPQ : Submodule.map (e : ThSharp H t₁ (ThL H t₁) →ₗ[M.L.O] ThSharp H t₀ N₂)
      (Submodule.comap (ThSharp H t₁ (ThL H t₁)).subtype (ThL H t₁)) =
      Submodule.comap (ThSharp H t₀ N₂).subtype N₂ := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (memN _).2 ⟨⟨y, hy⟩, rfl⟩
    · intro hx
      refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
      obtain ⟨y, hy⟩ := (memN _).1 hx
      rw [hg] at hy
      have h4 : ψ.symm ⟨(x : V), ((memS _ _ _).1 x.2).1⟩ = ⟨(y : V), ((memL _ _).1 y.2).2⟩ :=
        (LinearEquiv.symm_apply_eq ψ).2 (Subtype.ext hy).symm
      have h3 : (e.symm x : V) = y := congrArg Subtype.val h4
      rw [h3]
      exact y.2
  let κ : DDW H t₁ (ThL H t₁) ≃ₗ[M.L.O] DDW H t₀ N₂ := Submodule.Quotient.equiv _ _ e hPQ
  have hκ : ∀ w, κ (dwMk H t₁ (ThL H t₁) w) = dwMk H t₀ N₂ (e w) := fun w => rfl
  have surj : ∀ m : MMsharp H t₁, ∃ w, η₁ (ddMk H t₁ m) = dwMk H t₁ (ThL H t₁) w := by
    intro m
    obtain ⟨w, hw⟩ := Submodule.Quotient.mk_surjective _ (η₁ (ddMk H t₁ m))
    exact ⟨w, hw.symm⟩
  have hh : ∀ a b : ThSharp H t₀ N₂, H.h (e.symm a : V) (e.symm b : V) = H.h a b := by
    intro a b
    have h := hψh (ψ.symm ⟨(a : V), ((memS _ _ _).1 a.2).1⟩) (ψ.symm ⟨(b : V), ((memS _ _ _).1 b.2).1⟩)
    simp only [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  let η : DDt H t₀ ≃ₗ[M.L.O] DDW H t₀ N₂ := (θ.symm.trans η₁).trans κ
  have hle : N₂ ≤ Submodule.restrictScalars M.L.O (H.W0 t₀.f t₀.f') := by
    intro v hv
    obtain ⟨y, rfl⟩ := (memN v).1 hv
    exact (ψ _).2
  have hfg : N₂.FG := by
    rw [hN₂]
    haveI : Module.Finite M.L.O (ThL H t₁) := Module.Finite.iff_fg.2 (hFG V H t₁ hG₁)
    exact (Module.Finite.fg_top).map g
  have hS1 := hS V H t₁ hG₁
  have hspan : Submodule.span E (N₂ : Set V) = H.W0 t₀.f t₀.f' := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro v hv
      exact hle hv
    · intro v hv
      have hu : ((ψ.symm ⟨v, hv⟩ : H.W0 t₁.f t₁.f') : V) ∈ Submodule.span E (ThL H t₁ : Set V) := by
        rw [hS1]
        exact (ψ.symm _).2
      have main : ∀ (x : V) (hx : x ∈ Submodule.span E (ThL H t₁ : Set V)),
          ∀ h : x ∈ H.W0 t₁.f t₁.f', (ψ ⟨x, h⟩ : V) ∈ Submodule.span E (N₂ : Set V) := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hx =>
          intro h
          exact Submodule.subset_span ((keyN x h).1 ((memL _ _).1 hx).1)
        | zero =>
          intro h
          have h0 : (⟨0, h⟩ : H.W0 t₁.f t₁.f') = 0 := rfl
          rw [h0, map_zero]
          exact Submodule.zero_mem _
        | add x y hx hy ihx ihy =>
          intro h
          have hx' : x ∈ H.W0 t₁.f t₁.f' := by
            rw [← hS1]
            exact hx
          have hy' : y ∈ H.W0 t₁.f t₁.f' := by
            rw [← hS1]
            exact hy
          have h0 : (⟨x + y, h⟩ : H.W0 t₁.f t₁.f') = ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
          rw [h0, map_add (f := _), Submodule.coe_add]
          exact Submodule.add_mem _ (ihx hx') (ihy hy')
        | smul a x hx ihx =>
          intro h
          have hx' : x ∈ H.W0 t₁.f t₁.f' := by
            rw [← hS1]
            exact hx
          have h0 : (⟨a • x, h⟩ : H.W0 t₁.f t₁.f') = a • ⟨x, hx'⟩ := rfl
          rw [h0, map_smul, Submodule.coe_smul]
          exact Submodule.smul_mem _ a (ihx hx')
      have h4 := main _ hu (ψ.symm ⟨v, hv⟩).2
      simpa using h4
  have hint : ∀ x ∈ N₂, ∀ y ∈ N₂, H.h x y ∈ M.L.O := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := (memN x).1 hx
    obtain ⟨b, rfl⟩ := (memN y).1 hy
    rw [hg, hg, hψh]
    exact (hsd _).1 ((memL _ _).1 a.2).1 _ ((memL _ _).1 b.2).1
  have hpair : ∀ (m m' : MMsharp H t₀) (w w' : ThSharp H t₀ N₂),
      η (ddMk H t₀ m) = dwMk H t₀ N₂ w → η (ddMk H t₀ m') = dwMk H t₀ N₂ w' →
      H.h m m' + H.h w w' ∈ M.L.O := by
    intro m m' w w' hw hw'
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (θ.symm (ddMk H t₀ m))
    obtain ⟨x', hx'⟩ := Submodule.Quotient.mk_surjective _ (θ.symm (ddMk H t₀ m'))
    have hθx : θ (ddMk H t₁ x) = ddMk H t₀ m := by
      rw [show ddMk H t₁ x = θ.symm (ddMk H t₀ m) from hx, LinearEquiv.apply_symm_apply]
    have hθx' : θ (ddMk H t₁ x') = ddMk H t₀ m' := by
      rw [show ddMk H t₁ x' = θ.symm (ddMk H t₀ m') from hx', LinearEquiv.apply_symm_apply]
    have h1 : η₁ (ddMk H t₁ x) = dwMk H t₁ (ThL H t₁) (e.symm w) := by
      apply κ.injective
      rw [hκ, LinearEquiv.apply_symm_apply, ← hw]
      show κ (η₁ (ddMk H t₁ x)) = κ (η₁ (θ.symm (ddMk H t₀ m)))
      rw [← hx]
      rfl
    have h1' : η₁ (ddMk H t₁ x') = dwMk H t₁ (ThL H t₁) (e.symm w') := by
      apply κ.injective
      rw [hκ, LinearEquiv.apply_symm_apply, ← hw']
      show κ (η₁ (ddMk H t₁ x')) = κ (η₁ (θ.symm (ddMk H t₀ m')))
      rw [← hx']
      rfl
    have a1 := hη₁b x x' (e.symm w) (e.symm w') h1 h1'
    rw [hh] at a1
    have a2 := hθ x x' m m' hθx hθx'
    have a3 := add_mem a2 a1
    convert a3 using 1
    ring
  have hGr := hG V H hn t₁ f₂ f₂' φ φ' hT hDl
  obtain ⟨Λ, ⟨hsd2, hprim, hcap, hη⟩, -⟩ :=
    hV hM V H t₀ hGr hMM N₂ hle hfg hspan hint η hpair
  have hgen := hP hM V H hn t₁ f₂ f₂' φ φ' hT hDl Λ hsd2 hprim
  have hthc : ThCond H t₁ t₀ Λ φ φ' := by
    intro n₁ n₂ hc
    obtain ⟨hn₁, rfl⟩ := (hψC n₁ n₂).1 hc
    rw [keyN n₁ hn₁, ← hcap]
    constructor
    · intro h
      exact (Submodule.mem_inf.1 h).1
    · intro h
      exact Submodule.mem_inf.2 ⟨h, (ψ _).2⟩
  refine ⟨Λ, hgen, hthc, ?_⟩
  intro m₁ m₂
  obtain ⟨w, hw⟩ := surj m₁
  have hmw : (m₁ : V) + w ∈ t₁.abelian₂ := (hη₁a m₁ w).1 hw
  have step : θ (ddMk H t₁ m₁) = ddMk H t₀ m₂ ↔ η (ddMk H t₀ m₂) = dwMk H t₀ N₂ (e w) := by
    constructor
    · intro h
      show κ (η₁ (θ.symm (ddMk H t₀ m₂))) = _
      rw [← h, LinearEquiv.symm_apply_apply, hw, hκ]
    · intro h
      have h2 : κ (η₁ (θ.symm (ddMk H t₀ m₂))) = κ (η₁ (ddMk H t₁ m₁)) := by
        rw [hw, hκ]
        exact h
      have h3 := η₁.injective (κ.injective h2)
      rw [← h3, LinearEquiv.apply_symm_apply]
  refine step.trans ((hη m₂ (e w)).trans ?_)
  constructor
  · intro h
    exact ⟨w, e w, (hψC _ _).2 ⟨((memS _ _ _).1 w.2).1, rfl⟩, hmw, h⟩
  · rintro ⟨n₁, n₂, hc, h1, h2⟩
    obtain ⟨hn₁, rfl⟩ := (hψC n₁ n₂).1 hc
    have hd : n₁ - w ∈ H.W0 t₁.f t₁.f' := Submodule.sub_mem _ hn₁ ((memS _ _ _).1 w.2).1
    have hdL : n₁ - w ∈ t₁.abelian₂ := by
      have h4 := t₁.abelian₂.sub_mem h1 hmw
      simpa using h4
    have h3 : (ψ ⟨n₁ - w, hd⟩ : V) ∈ Λ := by
      have h5 := (keyN _ hd).1 hdL
      rw [← hcap] at h5
      exact (Submodule.mem_inf.1 h5).1
    have hψd : (ψ ⟨n₁ - w, hd⟩ : V) = (ψ ⟨n₁, hn₁⟩ : V) - (e w : V) := by
      have h6 := congrArg Subtype.val (map_sub ψ ⟨n₁, hn₁⟩ ⟨(w : V), ((memS _ _ _).1 w.2).1⟩)
      exact h6
    rw [hψd] at h3
    have h5 := Λ.sub_mem h2 h3
    convert h5 using 1
    abel

end Back

end Formalism.L2.SG.LsDatumA
end
end

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Inj

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem hermSp_W0_eq_perp_span_range_MMfam {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f f' : Fin (r + 1) → V) : H.W0 f f' = H.perp (Submodule.span E (Set.range (Sum.elim f f'))) := by
  rw [Set.Sum.elim_range, Submodule.span_union]
  rfl

theorem span_frames_le_MM {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (t : Term V M r) :
    Submodule.span E (Set.range (Sum.elim t.f t.f')) ≤ Submodule.span E (Set.range (H.MMfam t)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  unfold HermSp.MMfam
  split
  · exact Submodule.subset_span ⟨i, rfl⟩
  · rename_i g _
    have hq : ((g.q : F)) ≠ 0 := by
      intro h0
      exact g.q_irr.ne_zero (Subtype.ext h0)
    set c : E := algebraMap F E ((g.q : F))⁻¹ with hc
    have hcu : IsUnit c := by
      rw [hc]
      exact (IsUnit.mk0 _ (inv_ne_zero hq)).map (algebraMap F E)
    rcases i with a | a
    · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
    · have h1 : t.f a ∈ Submodule.span E (Set.range (Sum.elim t.f fun b => c • (t.f' b - t.f b))) :=
        Submodule.subset_span ⟨Sum.inl a, rfl⟩
      have h2 : c • (t.f' a - t.f a) ∈ Submodule.span E (Set.range (Sum.elim t.f fun b => c • (t.f' b - t.f b))) :=
        Submodule.subset_span ⟨Sum.inr a, rfl⟩
      have h3 : t.f' a = t.f a + (((hcu.unit)⁻¹ : Eˣ) : E) • (c • (t.f' a - t.f a)) := by
        rw [smul_smul, IsUnit.val_inv_mul, one_smul]
        abel
      show t.f' a ∈ _
      rw [h3]
      exact Submodule.add_mem _ h1 (Submodule.smul_mem _ _ h2)

private theorem span_MMfam_eq_span_f_f' {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (t : Term V M r) :
    Submodule.span E (Set.range (H.MMfam t)) = Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
  refine le_antisymm ?_ (span_frames_le_MM H t)
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have h := MMfam_mem_sup H t i
  refine (sup_le ?_ ?_ : H.Xp t.f ⊔ H.Xp t.f' ≤ _) h
  · exact Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inl a, rfl⟩)
  · exact Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inr a, rfl⟩)

private theorem isCompl_span_perp_of_isGeneric {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (t : Term V M r) (ht : H.IsGeneric t) :
    IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f')))
      (H.perp (Submodule.span E (Set.range (Sum.elim t.f t.f')))) := by
  have h := isCompl_span_frames_W0 H t.f t.f' t.T t.T' ⟨ht.1.2.1.2.1, ht.1.2.1.2.2.1⟩
    ⟨ht.1.2.2.1.2.1, ht.1.2.2.1.2.2.1⟩ ht.1.2.2.2.1 (isUnit_Gdet H _ _ _ _ ht.1.2.2.2.2.1)
  rwa [hermSp_W0_eq_perp_span_range_MMfam] at h

private theorem mem_MMsharp_of_integral_pairing {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (t : Term V M r) (abelian₂ : Submodule (↥M.L.O) V) (hmem : ∀ a, H.MMfam t a ∈ abelian₂) (u : V)
    (hu : u ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')))
    (hint : ∀ y ∈ abelian₂, y ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) → H.h u y ∈ M.L.O) :
    u ∈ MMsharp H t := by
  refine ⟨by rw [span_MMfam_eq_span_f_f']; exact hu, ?_⟩
  intro m hm
  apply hint m
  · exact (Submodule.span_le.mpr (by rintro _ ⟨a, rfl⟩; exact hmem a)) hm
  · rw [← span_MMfam_eq_span_f_f' H t]
    exact Submodule.span_le_restrictScalars (↥M.L.O) E _ hm

theorem glueInj_of (M : Model F E) (r n : ℕ) (hM : M.OK) (hC : CorrIso M r n) : GlueInj M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hT Λ₂ Λ₂' hG hTh hG' hTh' hrel
  obtain ⟨ψ, hψh, hψ⟩ := hC V H hn t₁ f₂ f₂' φ φ' hT hG.1.2.2.2.1
  have hW₁ := hermSp_W0_eq_perp_span_range_MMfam H t₁.f t₁.f'
  have hW₂ := hermSp_W0_eq_perp_span_range_MMfam H f₂ f₂'
  have hU₁ := isCompl_span_perp_of_isGeneric H t₁ hT.1
  have key : ∀ A B : Submodule (↥M.L.O) V,
      H.IsGeneric { abelian₂ := A, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } →
      ThCond H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } A φ φ' →
      ThCond H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } B φ φ' →
      (∀ (m₁ : ↥(MMsharp H t₁))
          (m₂ : ↥(MMsharp H { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' })),
          GlueRel H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } A φ φ' m₁ m₂ →
          GlueRel H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } B φ φ' m₁ m₂) →
      A ≤ B := by
    intro A B hGA hThA hThB hAB x hx
    let U₂ : Submodule E V := Submodule.span E (Set.range (Sum.elim f₂ f₂'))
    let U₁ : Submodule E V := Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))
    have hU₂ : IsCompl U₂ (H.perp U₂) := isCompl_span_perp_of_isGeneric H _ hGA
    have gA := local_hermitian_glue F E M hM V H A hGA.1.1 U₂ hU₂
    have g₁ := local_hermitian_glue F E M hM V H t₁.abelian₂ hT.1.1.1 U₁ hU₁
    obtain ⟨p, hp, hpint, q, hq, hqint, hxpq⟩ : ∃ p ∈ U₂, (∀ y ∈ A, y ∈ U₂ → H.h p y ∈ M.L.O) ∧
        ∃ q ∈ H.perp U₂, (∀ y ∈ A, y ∈ H.perp U₂ → H.h q y ∈ M.L.O) ∧ p + q = x :=
      ⟨_, Submodule.coe_mem _, (gA.1 _ (Submodule.coe_mem _)).mp ⟨x, hx, rfl⟩,
       _, Submodule.coe_mem _, (gA.2 _ (Submodule.coe_mem _)).mp ⟨x, hx, rfl⟩,
       Submodule.projection_add_projection_eq_self hU₂ x⟩
    have hpS : p ∈ MMsharp H { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } :=
      mem_MMsharp_of_integral_pairing H _ A hGA.2.1 p hp hpint
    have hqW : q ∈ H.W0 f₂ f₂' := hW₂.ge hq
    obtain ⟨n₁, hψn₁⟩ : ∃ n₁ : ↥(H.W0 t₁.f t₁.f'), (ψ n₁ : V) = q := ⟨ψ.symm ⟨q, hqW⟩, by simp⟩
    have hcorr₁ : Corr H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } φ φ' (n₁ : V) q :=
      (hψ _ _).mpr ⟨n₁.2, hψn₁⟩
    have hn₁int : ∀ y ∈ t₁.abelian₂, y ∈ H.perp U₁ → H.h (n₁ : V) y ∈ M.L.O := by
      intro y hy hyp
      have hyW : y ∈ H.W0 t₁.f t₁.f' := hW₁.ge hyp
      have hc : Corr H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } φ φ' y
          (ψ ⟨y, hyW⟩ : V) := (hψ _ _).mpr ⟨hyW, rfl⟩
      have hyA : (ψ ⟨y, hyW⟩ : V) ∈ A := (hThA _ _ hc).mp hy
      have hyp2 : (ψ ⟨y, hyW⟩ : V) ∈ H.perp U₂ := hW₂.le (ψ ⟨y, hyW⟩).2
      have e : H.h (n₁ : V) y = H.h q (ψ ⟨y, hyW⟩ : V) := by
        rw [← hψn₁]
        exact (hψh n₁ ⟨y, hyW⟩).symm
      rw [e]
      exact hqint _ hyA hyp2
    have hn₁p : (n₁ : V) ∈ H.perp U₁ := hW₁.le n₁.2
    obtain ⟨z, hz, hzn⟩ := (g₁.2 _ hn₁p).mpr hn₁int
    have hmS : (U₁.linearProjOfIsCompl (H.perp U₁) hU₁ z : V) ∈ MMsharp H t₁ :=
      mem_MMsharp_of_integral_pairing H t₁ t₁.abelian₂ hT.1.2.1 _ (Submodule.coe_mem _)
        ((g₁.1 _ (Submodule.coe_mem _)).mp ⟨z, hz, rfl⟩)
    have hzsum : (U₁.linearProjOfIsCompl (H.perp U₁) hU₁ z : V) + (n₁ : V) = z := by
      rw [← hzn]
      exact Submodule.projection_add_projection_eq_self hU₁ z
    have hz' : (U₁.linearProjOfIsCompl (H.perp U₁) hU₁ z : V) + (n₁ : V) ∈ t₁.abelian₂ := by
      rw [hzsum]; exact hz
    have hglA : GlueRel H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } A φ φ'
        ⟨_, hmS⟩ ⟨p, hpS⟩ :=
      ⟨n₁, q, hcorr₁, hz', by show p + q ∈ A; rw [hxpq]; exact hx⟩
    obtain ⟨n₁', n₂', hc', h1', h2'⟩ := hAB _ _ hglA
    obtain ⟨hn₁'W, hψ'⟩ := (hψ _ _).mp hc'
    have h1'' : (U₁.linearProjOfIsCompl (H.perp U₁) hU₁ z : V) + n₁' ∈ t₁.abelian₂ := h1'
    have hd : n₁' - (n₁ : V) ∈ t₁.abelian₂ := by
      have h0 := t₁.abelian₂.sub_mem h1'' hz'
      rwa [add_sub_add_left_eq_sub] at h0
    have hdW : n₁' - (n₁ : V) ∈ H.W0 t₁.f t₁.f' := Submodule.sub_mem _ hn₁'W n₁.2
    have hψd : (ψ ⟨n₁' - n₁, hdW⟩ : V) = n₂' - q := by
      have e : (⟨n₁' - n₁, hdW⟩ : ↥(H.W0 t₁.f t₁.f')) = ⟨n₁', hn₁'W⟩ - n₁ := rfl
      rw [e, map_sub, Submodule.coe_sub, hψ', hψn₁]
    have hcd : Corr H t₁ { abelian₂ := ⊥, f := f₂, f' := f₂', T := t₁.T, T' := t₁.T' } φ φ'
        (n₁' - n₁) (n₂' - q) := (hψ _ _).mpr ⟨hdW, hψd⟩
    have hB : n₂' - q ∈ B := (hThB _ _ hcd).mp hd
    have h2'' : p + n₂' ∈ B := h2'
    have h0 := B.sub_mem h2'' hB
    have e : p + n₂' - (n₂' - q) = x := by rw [← hxpq]; abel
    rwa [e] at h0
  exact le_antisymm (key Λ₂ Λ₂' hG hTh hTh' (fun m₁ m₂ => (hrel m₁ m₂).mp))
    (key Λ₂' Λ₂ hG' hTh' hTh (fun m₁ m₂ => (hrel m₁ m₂).mpr))

end Inj

end Formalism.L2.SG.LsDatumA
