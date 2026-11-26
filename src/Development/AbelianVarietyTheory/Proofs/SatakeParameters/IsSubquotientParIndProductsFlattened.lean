module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InductionInStagesTwoFactorsEquiv
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InductionInStagesTwoFactorsEquiv
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SmGL.StagesTwo

open GlobalTheory.SmGL.MultiIrr

section Mid

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {β : Type} [Fintype β] [LinearOrder β] {m : β → Type} [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def blocks (h : a ⊕ b ≃ n) : parab k (two h) →* GL a k × GL b k :=
  (leviTwo k a b).symm.toMonoidHom.comp (leviProj k (two h))

theorem blocks_fst (h : a ⊕ b ≃ n) (q : parab k (two h)) (x y : a) :
    ((blocks k h q).1 : Matrix a a k) x y = (q : GL n k).val (h (.inl x)) (h (.inl y)) := rfl

theorem blocks_snd (h : a ⊕ b ≃ n) (q : parab k (two h)) (x y : b) :
    ((blocks k h q).2 : Matrix b b k) x y = (q : GL n k).val (h (.inr x)) (h (.inr y)) := rfl

def mid (h : a ⊕ b ≃ n) (ψ : (Σ j, m j) ≃ b) : Subgroup (GL n k) :=
  ((parab k ψ).comap ((MonoidHom.snd _ _).comp (blocks k h))).map (parab k (two h)).subtype

theorem mid_le (h : a ⊕ b ≃ n) (ψ : (Σ j, m j) ≃ b) : mid k h ψ ≤ parab k (two h) :=
  Subgroup.map_subtype_le _

theorem coe_mem_mid (h : a ⊕ b ≃ n) (ψ : (Σ j, m j) ≃ b) (q : parab k (two h)) :
    (q : GL n k) ∈ mid k h ψ ↔ (blocks k h q).2 ∈ parab k ψ :=
  Subgroup.mem_map_iff_mem Subtype.val_injective

def midIncl (h : a ⊕ b ≃ n) (ψ : (Σ j, m j) ≃ b) : mid k h ψ →* parab k (two h) :=
  Subgroup.inclusion (mid_le k h ψ)

def midSnd (h : a ⊕ b ≃ n) (ψ : (Σ j, m j) ≃ b) : mid k h ψ →* parab k ψ :=
  ((MonoidHom.snd _ _).comp ((blocks k h).comp (midIncl k h ψ))).codRestrict (parab k ψ)
    fun q => (coe_mem_mid k h ψ (midIncl k h ψ q)).1 q.2

def midProj (h : a ⊕ b ≃ n) (ψ : (Σ j, m j) ≃ b) : mid k h ψ →* Levi k m × GL a k :=
  ((leviProj k ψ).comp (midSnd k h ψ)).prod ((MonoidHom.fst _ _).comp ((blocks k h).comp (midIncl k h ψ)))

def midChar (ψ : (Σ j, m j) ≃ b) : Levi k m × GL a k →* ℂˣ :=
  (deltaHalf k (Two a b)).comp ((leviTwo k a b).toMonoidHom.comp
      ((MonoidHom.snd _ _).prod ((leviEmb k ψ).comp (MonoidHom.fst _ _)))) *
    (deltaHalf k m).comp (MonoidHom.fst _ _)

def midRep (h : a ⊕ b ≃ n) (ψ : (Σ j, m j) ≃ b) (ρ : Representation ℂ (Levi k m) W)
    (π : Representation ℂ (GL a k) V) : Representation ℂ (mid k h ψ) (W ⊗[ℂ] V) :=
  twist ((extTensor ρ π).comp (midProj k h ψ)) ((midChar k ψ).comp (midProj k h ψ))

end Mid

end GlobalTheory.SmGL.StagesTwo

namespace GlobalTheory.SmGL.StagesTwo

open GlobalTheory.SmGL.MultiIrr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {β : Type} [Fintype β] [LinearOrder β] {m : β → Type} [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
  {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]

theorem stage_one (h : a ⊕ b ≃ n) (ψ : (Σ j, m j) ≃ b) (σ₀ : Representation ℂ (GL a k) V)
    (ρ : Representation ℂ (Levi k m) W) (σ : Representation ℂ (mid k h ψ) U) (κ : V ⊗[ℂ] W ≃ₗ[ℂ] U)
    (hσ : ∀ (q : parab k (two h)) (hq : (q : GL n k) ∈ mid k h ψ) (hb : (blocks k h q).2 ∈ parab k ψ) x,
      σ ⟨q, hq⟩ (κ x) = ((deltaHalf k (Two a b) (leviProj k (two h) q) *
        deltaHalf k m (leviProj k ψ ⟨_, hb⟩) : ℂˣ) : ℂ) •
        κ (TensorProduct.map (σ₀ (blocks k h q).1) (ρ (leviProj k ψ ⟨_, hb⟩)) x)) :
    Nonempty ((ind₂ h (extTensor σ₀ (parInd ψ ρ))).Equiv (smInd (mid k h ψ) σ)) := by
  let j := ((emb₂ k h).comp (MonoidHom.inr _ _)).codRestrict (parab k (two h))
    fun _ => leviEmb_mem_parab k _ _
  refine smInd_stages (P' := parab k ψ) (mid_le k h ψ) (blocks k h) j ?_ (fun x => ?_)
    (fun q => coe_mem_mid k h ψ q) SplitFlip.isCompact_KO (fun x => exists_parab_mul _ x)
    ((deltaHalf k _).comp (leviTwo k _ _).toMonoidHom) ?_ σ₀ _ σ κ (fun q h1 h2 x => ?_) _ fun q x => rfl
  · exact (continuous_leviEmb k _).comp ((continuous_leviTwo k).comp (Continuous.prodMk_right 1))
  · exact (leviTwo k _ _).symm_apply_eq.2 (leviProj_leviEmb k _ _)
  · have h1' : IsSmoothChar (((deltaHalf k _).comp
        (leviTwo k a b).toMonoidHom).comp (MonoidHom.inr _ _)) :=
      ((isSmoothChar_deltaHalf k).comp _ (continuous_leviTwo k)).comp _ (Continuous.prodMk_right 1)
    filter_upwards [h1'.mem_nhds (one_mem _)] with u hu
    exact MonoidHom.mem_ker.1 hu
  · rw [hσ q h1 h2 x]
    show _ = (deltaHalf k _ (leviTwo k _ _ ((leviTwo k a b).symm (leviProj k (two h) q))) : ℂ) •
      κ (TensorProduct.map (σ₀ (blocks k h q).1) ((deltaHalf k _ (leviProj k ψ ⟨_, h2⟩) : ℂ) •
        ρ (leviProj k ψ ⟨_, h2⟩)) x)
    rw [MulEquiv.apply_symm_apply, TensorProduct.map_smul_right, LinearMap.smul_apply, map_smul, smul_smul,
      Units.val_mul]

end GlobalTheory.SmGL.StagesTwo

namespace GlobalTheory.SmGL.StagesTwo

open GlobalTheory.SmGL.MultiIrr

section Lex

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {β₀ β₁ : Type} [Fintype β₀] [LinearOrder β₀] [Fintype β₁] [LinearOrder β₁]
  {m : β₀ ⊕ₗ β₁ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)]

theorem sum_lex {M : Type} [AddCommMonoid M] (f : β₀ ⊕ₗ β₁ → M) :
    ∑ c, f c = ∑ i, f (toLex (Sum.inl i)) + ∑ j, f (toLex (Sum.inr j)) :=
  (toLex.sum_comp f).symm.trans (Fintype.sum_sum_type _)

theorem prod_lex {M : Type} [CommMonoid M] (f : β₀ ⊕ₗ β₁ → M) :
    ∏ c, f c = (∏ i, f (toLex (Sum.inl i))) * ∏ j, f (toLex (Sum.inr j)) :=
  (toLex.prod_comp f).symm.trans (Fintype.prod_sum_type _)

omit [∀ c, DecidableEq (m c)] in
theorem modExp_inl (i : β₀) : modExp m (toLex (Sum.inl i)) =
    modExp (fun i => m (toLex (Sum.inl i))) i + Fintype.card (Σ j, m (toLex (Sum.inr j))) := by
  simp only [modExp, Finset.sum_filter, Fintype.card_sigma, Nat.cast_sum]
  rw [sum_lex, sum_lex]
  simp [Sum.Lex.inl_lt_inl_iff, Sum.Lex.not_inr_lt_inl]
  ring

omit [∀ c, DecidableEq (m c)] in
theorem modExp_inr (j : β₁) : modExp m (toLex (Sum.inr j)) =
    modExp (fun j => m (toLex (Sum.inr j))) j - Fintype.card (Σ i, m (toLex (Sum.inl i))) := by
  simp only [modExp, Finset.sum_filter, Fintype.card_sigma, Nat.cast_sum]
  rw [sum_lex, sum_lex]
  simp [Sum.Lex.inr_lt_inr_iff, Sum.Lex.not_inr_lt_inl]
  ring

end Lex

end GlobalTheory.SmGL.StagesTwo

namespace GlobalTheory.SmGL.StagesTwo

open GlobalTheory.SmGL.MultiIrr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {β₀ β₁ : Type} [Fintype β₀] [LinearOrder β₀] [Fintype β₁] [LinearOrder β₁]
  {m : β₀ ⊕ₗ β₁ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)]
  {a b n V W U : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]

theorem deltaHalf_lex (g : Levi k m) :
    deltaHalf k m g = absPow k ((Fintype.card (Σ j, m (toLex (Sum.inr j))) : ℂ) / 2)
        (∏ i, GeneralLinearGroup.det (g (toLex (Sum.inl i)))) *
      absPow k (-(Fintype.card (Σ i, m (toLex (Sum.inl i))) : ℂ) / 2)
        (∏ j, GeneralLinearGroup.det (g (toLex (Sum.inr j)))) *
      deltaHalf k (fun i => m (toLex (Sum.inl i))) (fun i => g (toLex (Sum.inl i))) *
      deltaHalf k (fun j => m (toLex (Sum.inr j))) (fun j => g (toLex (Sum.inr j))) := by
  have A : ∀ i, absPow k ((modExp m (toLex (Sum.inl i)) : ℂ) / 2) (GeneralLinearGroup.det (g (toLex (Sum.inl i)))) =
      absPow k ((modExp (fun i => m (toLex (Sum.inl i))) i : ℂ) / 2) (GeneralLinearGroup.det (g (toLex (Sum.inl i)))) *
      absPow k ((Fintype.card (Σ j, m (toLex (Sum.inr j))) : ℂ) / 2) (GeneralLinearGroup.det (g (toLex (Sum.inl i)))) := by
    intro i
    rw [modExp_inl, ← MonoidHom.mul_apply, ← absPow_add]
    congr 2
    push_cast
    ring
  have B : ∀ j, absPow k ((modExp m (toLex (Sum.inr j)) : ℂ) / 2) (GeneralLinearGroup.det (g (toLex (Sum.inr j)))) =
      absPow k ((modExp (fun j => m (toLex (Sum.inr j))) j : ℂ) / 2) (GeneralLinearGroup.det (g (toLex (Sum.inr j)))) *
      absPow k (-(Fintype.card (Σ i, m (toLex (Sum.inl i))) : ℂ) / 2) (GeneralLinearGroup.det (g (toLex (Sum.inr j)))) := by
    intro j
    rw [modExp_inr, ← MonoidHom.mul_apply, ← absPow_add]
    congr 2
    push_cast
    ring
  rw [deltaHalf_apply, deltaHalf_apply, deltaHalf_apply, prod_lex, Finset.prod_congr rfl fun i _ => A i,
    Finset.prod_congr rfl fun j _ => B j, Finset.prod_mul_distrib, Finset.prod_mul_distrib, map_prod, map_prod]
  ac_rfl

variable (E : (Σ c, m c) ≃ n) (h : a ⊕ b ≃ n) (ψ₀ : (Σ i, m (toLex (Sum.inl i))) ≃ a)
  (ψ₁ : (Σ j, m (toLex (Sum.inr j))) ≃ b)

theorem parab_lex_le (h0 : ∀ i x, h (.inl (ψ₀ ⟨i, x⟩)) = E ⟨toLex (.inl i), x⟩)
    (h1 : ∀ j x, h (.inr (ψ₁ ⟨j, x⟩)) = E ⟨toLex (.inr j), x⟩) : parab k E ≤ parab k (two h) :=
  fun g hg => (mem_parab_two k).2 fun j' i' => by
    obtain ⟨⟨j, y⟩, rfl⟩ := ψ₁.surjective j'
    obtain ⟨⟨i, x⟩, rfl⟩ := ψ₀.surjective i'
    rw [h1, h0]
    exact mem_parab_iff.1 hg _ _ y x (Sum.Lex.inl_lt_inr _ _)

theorem mem_parab_lex_iff (h0 : ∀ i x, h (.inl (ψ₀ ⟨i, x⟩)) = E ⟨toLex (.inl i), x⟩)
    (h1 : ∀ j x, h (.inr (ψ₁ ⟨j, x⟩)) = E ⟨toLex (.inr j), x⟩) (q : parab k (two h)) :
    (q : GL n k) ∈ parab k E ↔ (blocks k h q).1 ∈ parab k ψ₀ ∧ (blocks k h q).2 ∈ parab k ψ₁ := by
  constructor
  · intro hq
    refine ⟨mem_parab_iff.2 fun i i' x y hlt => ?_, mem_parab_iff.2 fun j j' x y hlt => ?_⟩
    · rw [blocks_fst, h0, h0]
      exact mem_parab_iff.1 hq _ _ x y (Sum.Lex.inl_lt_inl_iff.2 hlt)
    · rw [blocks_snd, h1, h1]
      exact mem_parab_iff.1 hq _ _ x y (Sum.Lex.inr_lt_inr_iff.2 hlt)
  · rintro ⟨hA, hB⟩
    refine mem_parab_iff.2 fun c c' u v hlt => ?_
    obtain ⟨c, rfl⟩ := toLex.surjective c
    obtain ⟨c', rfl⟩ := toLex.surjective c'
    rcases c with i | j <;> rcases c' with i' | j'
    · rw [← h0, ← h0]
      exact mem_parab_iff.1 hA i i' u v (Sum.Lex.inl_lt_inl_iff.1 hlt)
    · exact absurd hlt Sum.Lex.not_inr_lt_inl
    · rw [← h1, ← h0]
      exact (mem_parab_two k).1 q.2 _ _
    · rw [← h1, ← h1]
      exact mem_parab_iff.1 hB j j' u v (Sum.Lex.inr_lt_inr_iff.1 hlt)

end GlobalTheory.SmGL.StagesTwo

namespace GlobalTheory.SmGL.StagesTwo

open GlobalTheory.SmGL.MultiIrr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {β₀ β₁ : Type} [Fintype β₀] [LinearOrder β₀] [Fintype β₁] [LinearOrder β₁]
  {m : β₀ ⊕ₗ β₁ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)]
  {a b n V W U : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]

omit [Fintype n] in
theorem midChar_midProj {β : Type} [Fintype β] [LinearOrder β] {m' : β → Type} [∀ j, Fintype (m' j)]
    [∀ j, DecidableEq (m' j)] [Fintype n] (h : a ⊕ b ≃ n) (ψ : (Σ j, m' j) ≃ b) (q : mid k h ψ) :
    midChar k ψ (midProj k h ψ q) =
      deltaHalf k (Two a b) (leviProj k (two h) (midIncl k h ψ q)) * deltaHalf k m' (leviProj k ψ (midSnd k h ψ q)) := by
  show deltaHalf k (Two a b) (leviTwo k a b ((blocks k h (midIncl k h ψ q)).1,
    leviEmb k ψ (leviProj k ψ (midSnd k h ψ q)))) * _ = _
  have e : leviProj k (two h) (midIncl k h ψ q) = leviTwo k a b (blocks k h (midIncl k h ψ q)) :=
    (MulEquiv.apply_symm_apply _ _).symm
  rw [e, deltaHalf_two, deltaHalf_two, det_leviEmb, ← det_parab k ψ (midSnd k h ψ q)]
  rfl

theorem stage_two (E : (Σ c, m c) ≃ n) (h : a ⊕ b ≃ n) (ψ₀ : (Σ i, m (toLex (Sum.inl i))) ≃ a)
    (ψ₁ : (Σ j, m (toLex (Sum.inr j))) ≃ b)
    (h0 : ∀ i x, h (.inl (ψ₀ ⟨i, x⟩)) = E ⟨toLex (.inl i), x⟩)
    (h1 : ∀ j x, h (.inr (ψ₁ ⟨j, x⟩)) = E ⟨toLex (.inr j), x⟩)
    (ρ₀ : Representation ℂ (Levi k fun i => m (toLex (Sum.inl i))) V)
    (ρ₁ : Representation ℂ (Levi k fun j => m (toLex (Sum.inr j))) W) (σ : Representation ℂ (Levi k m) U)
    (κ : V ⊗[ℂ] W ≃ₗ[ℂ] U)
    (hκ : ∀ g x, σ g (κ x) = κ (TensorProduct.map (ρ₀ fun i => g (toLex (.inl i)))
      (ρ₁ fun j => g (toLex (.inr j))) x)) :
    Nonempty ((smInd (mid k h ψ₁) (midRep k h ψ₁ ρ₁ (parInd ψ₀ ρ₀))).Equiv (parInd E σ)) := by
  have hle := parab_lex_le (k := k) E h ψ₀ ψ₁ h0 h1
  have hmem := mem_parab_lex_iff (k := k) E h ψ₀ ψ₁ h0 h1
  have eb : ∀ x : GL a k, blocks k h ⟨emb₂ k h (x, 1), leviEmb_mem_parab k _ _⟩ = (x, 1) := fun x =>
    (leviTwo k a b).symm_apply_eq.2 (leviProj_leviEmb k _ _)
  have hj : ∀ x : GL a k, (emb₂ k h).comp (MonoidHom.inl _ _) x ∈ mid k h ψ₁ := fun x =>
    (coe_mem_mid k h ψ₁ ⟨_, leviEmb_mem_parab k _ _⟩).2 (by
      show (blocks k h ⟨emb₂ k h (x, 1), leviEmb_mem_parab k _ _⟩).2 ∈ parab k ψ₁
      rw [eb]; exact one_mem _)
  let j := ((emb₂ k h).comp (MonoidHom.inl _ _)).codRestrict (mid k h ψ₁) hj
  refine smInd_stages (P' := parab k ψ₀) (ρ := (twist ρ₀ (deltaHalf k _)).comp (leviProj k ψ₀))
    (fun g hg => (coe_mem_mid k h ψ₁ ⟨g, hle hg⟩).2 ((hmem ⟨g, hle hg⟩).1 hg).2) (midProj k h ψ₁) j ?_
    (fun x => ?_) (fun q => ?_) SplitFlip.isCompact_KO (fun x => exists_parab_mul _ x) (midChar k ψ₁) ?_ ρ₁ _
    ((TensorProduct.comm ℂ W V).trans κ) (fun q h1' h2 x => ?_) _ fun q x => rfl
  · exact (continuous_leviEmb k _).comp ((continuous_leviTwo k).comp (Continuous.prodMk_left 1))
  · have e := eb x
    refine Prod.ext ?_ ?_
    · show leviProj k ψ₁ (midSnd k h ψ₁ (j x)) = 1
      have : midSnd k h ψ₁ (j x) = 1 := Subtype.ext (congrArg Prod.snd e)
      rw [this, map_one]
    · exact congrArg Prod.fst e
  · exact (hmem (midIncl k h ψ₁ q)).trans (and_iff_left ((coe_mem_mid k h ψ₁ _).1 q.2))
  · have hs : IsSmoothChar (((deltaHalf k _).comp (leviTwo k a b).toMonoidHom).comp (MonoidHom.inl _ _)) :=
      ((isSmoothChar_deltaHalf k).comp _ (continuous_leviTwo k)).comp _ (Continuous.prodMk_left 1)
    filter_upwards [hs.mem_nhds (one_mem _)] with u hu
    have := MonoidHom.mem_ker.1 hu
    show deltaHalf k _ (leviTwo k a b (u, leviEmb k ψ₁ 1)) * deltaHalf k _ 1 = 1
    rw [map_one, map_one, mul_one]
    exact this
  · let g := leviProj k E ⟨q, h1'⟩
    have e0 : leviProj k ψ₀ ⟨(midProj k h ψ₁ q).2, h2⟩ = fun i => g (toLex (.inl i)) :=
      funext fun i => Units.ext (Matrix.ext fun x y => by
        show (q : GL n k).val (h (.inl (ψ₀ ⟨i, x⟩))) (h (.inl (ψ₀ ⟨i, y⟩))) = (q : GL n k).val (E ⟨_, x⟩) (E ⟨_, y⟩)
        rw [h0, h0])
    have e1 : (midProj k h ψ₁ q).1 = fun j => g (toLex (.inr j)) :=
      funext fun j => Units.ext (Matrix.ext fun x y => by
        show (q : GL n k).val (h (.inr (ψ₁ ⟨j, x⟩))) (h (.inr (ψ₁ ⟨j, y⟩))) = (q : GL n k).val (E ⟨_, x⟩) (E ⟨_, y⟩)
        rw [h1, h1])
    have e2 : GeneralLinearGroup.det (midProj k h ψ₁ q).2 = ∏ i, GeneralLinearGroup.det (g (toLex (.inl i))) := by
      have := det_parab k ψ₀ ⟨_, h2⟩
      rwa [e0] at this
    have e3 : midChar k ψ₁ (midProj k h ψ₁ q) =
        absPow k ((Fintype.card b : ℂ) / 2) (GeneralLinearGroup.det (midProj k h ψ₁ q).2) *
        absPow k (-(Fintype.card a : ℂ) / 2) (GeneralLinearGroup.det (leviEmb k ψ₁ (midProj k h ψ₁ q).1)) *
        deltaHalf k _ (midProj k h ψ₁ q).1 := by
      show deltaHalf k (Two a b) (leviTwo k a b ((midProj k h ψ₁ q).2, leviEmb k ψ₁ (midProj k h ψ₁ q).1)) * _ = _
      rw [deltaHalf_two] <;> rfl
    have e4 : deltaHalf k m g = midChar k ψ₁ (midProj k h ψ₁ q) *
        deltaHalf k (fun i => m (toLex (Sum.inl i))) (fun i => g (toLex (.inl i))) := by
      rw [e3, e2, det_leviEmb, e1, deltaHalf_lex, ← Fintype.card_congr ψ₀, ← Fintype.card_congr ψ₁]
      ac_rfl
    have hc := TensorProduct.map_comm (ρ₀ fun i => g (toLex (.inl i))) (ρ₁ fun j => g (toLex (.inr j))) x
    show (deltaHalf k m g : ℂ) • σ g (κ (TensorProduct.comm ℂ W V x)) = (midChar k ψ₁ (midProj k h ψ₁ q) : ℂ) •
      κ (TensorProduct.comm ℂ W V (TensorProduct.map (ρ₁ (midProj k h ψ₁ q).1)
        ((deltaHalf k _ (leviProj k ψ₀ ⟨_, h2⟩) : ℂ) • ρ₀ (leviProj k ψ₀ ⟨_, h2⟩)) x))
    rw [hκ, e4, e0, e1, TensorProduct.map_smul_right, LinearMap.smul_apply, map_smul, map_smul, smul_smul,
      Units.val_mul, hc]

end GlobalTheory.SmGL.StagesTwo

namespace GlobalTheory.SmGL.StagesTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {β₀ β₁ : Type} [Fintype β₀] [LinearOrder β₀] [Fintype β₁] [LinearOrder β₁]
  {m : β₀ ⊕ₗ β₁ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)]
  {a b n V W U : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]

theorem ind₂_parInd_parInd_equiv_of (E : (Σ c, m c) ≃ n) (h : a ⊕ b ≃ n)
    (ψ₀ : (Σ i, m (toLex (Sum.inl i))) ≃ a) (ψ₁ : (Σ j, m (toLex (Sum.inr j))) ≃ b)
    (h0 : ∀ i x, h (.inl (ψ₀ ⟨i, x⟩)) = E ⟨toLex (.inl i), x⟩)
    (h1 : ∀ j x, h (.inr (ψ₁ ⟨j, x⟩)) = E ⟨toLex (.inr j), x⟩)
    (ρ₀ : Representation ℂ (Levi k fun i => m (toLex (Sum.inl i))) V)
    (ρ₁ : Representation ℂ (Levi k fun j => m (toLex (Sum.inr j))) W) (σ : Representation ℂ (Levi k m) U)
    (κ : V ⊗[ℂ] W ≃ₗ[ℂ] U)
    (hκ : ∀ g x, σ g (κ x) = κ (TensorProduct.map (ρ₀ fun i => g (toLex (.inl i)))
      (ρ₁ fun j => g (toLex (.inr j))) x)) :
    Nonempty ((ind₂ h (extTensor (parInd ψ₀ ρ₀) (parInd ψ₁ ρ₁))).Equiv (parInd E σ)) := by
  have hA := stage_one h ψ₁ (parInd ψ₀ ρ₀) ρ₁ (midRep k h ψ₁ ρ₁ (parInd ψ₀ ρ₀))
    (TensorProduct.comm ℂ _ _) fun q hq hb x => by
      have e := midChar_midProj h ψ₁ (⟨q, hq⟩ : mid k h ψ₁)
      show (midChar k ψ₁ (midProj k h ψ₁ ⟨q, hq⟩) : ℂ) • TensorProduct.map (ρ₁ (leviProj k ψ₁ ⟨_, hb⟩))
        (parInd ψ₀ ρ₀ (blocks k h q).1) (TensorProduct.comm ℂ _ _ x) = _
      rw [e, TensorProduct.map_comm]
      rfl
  have hB := stage_two E h ψ₀ ψ₁ h0 h1 ρ₀ ρ₁ σ κ hκ
  exact ⟨hA.some.trans hB.some⟩

theorem ind₂_parInd_parInd_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {β₀ β₁ a b n V W U : Type} [Fintype β₀] [LinearOrder β₀] [Fintype β₁] [LinearOrder β₁] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U] {m : β₀ ⊕ₗ β₁ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)] (E : (Σ c, m c) ≃ n) (h : a ⊕ b ≃ n) (ψ₀ : (Σ i, m (toLex (Sum.inl i))) ≃ a) (ψ₁ : (Σ j, m (toLex (Sum.inr j))) ≃ b), (∀ i x, h (.inl (ψ₀ ⟨i, x⟩)) = E ⟨toLex (.inl i), x⟩) → (∀ j x, h (.inr (ψ₁ ⟨j, x⟩)) = E ⟨toLex (.inr j), x⟩) → ∀ (ρ₀ : Representation ℂ (Levi k fun i => m (toLex (Sum.inl i))) V) (ρ₁ : Representation ℂ (Levi k fun j => m (toLex (Sum.inr j))) W) (σ : Representation ℂ (Levi k m) U) (κ : V ⊗[ℂ] W ≃ₗ[ℂ] U), (∀ g x, σ g (κ x) = κ (TensorProduct.map (ρ₀ fun i => g (toLex (.inl i))) (ρ₁ fun j => g (toLex (.inr j))) x)) → Nonempty ((ind₂ h (extTensor (parInd ψ₀ ρ₀) (parInd ψ₁ ρ₁))).Equiv (parInd E σ)) := by
  intro k _ _ _ _ β₀ β₁ a b n V W U _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m _ _ E h ψ₀ ψ₁ h0 h1 ρ₀ ρ₁ σ κ hκ
  exact ind₂_parInd_parInd_equiv_of E h ψ₀ ψ₁ h0 h1 ρ₀ ρ₁ σ κ hκ

end GlobalTheory.SmGL.StagesTwo
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InductionInStagesTwoFactorsEquivStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inductionInStages_twoFactors_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {β₀ β₁ a b n V W U : Type} [Fintype β₀] [LinearOrder β₀] [Fintype β₁] [LinearOrder β₁] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U] {m : β₀ ⊕ₗ β₁ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)] (E : (Σ c, m c) ≃ n) (h : a ⊕ b ≃ n) (ψ₀ : (Σ i, m (toLex (Sum.inl i))) ≃ a) (ψ₁ : (Σ j, m (toLex (Sum.inr j))) ≃ b), (∀ i x, h (.inl (ψ₀ ⟨i, x⟩)) = E ⟨toLex (.inl i), x⟩) → (∀ j x, h (.inr (ψ₁ ⟨j, x⟩)) = E ⟨toLex (.inr j), x⟩) → ∀ (ρ₀ : Representation ℂ (Levi k fun i => m (toLex (Sum.inl i))) V) (ρ₁ : Representation ℂ (Levi k fun j => m (toLex (Sum.inr j))) W) (σ : Representation ℂ (Levi k m) U) (κ : V ⊗[ℂ] W ≃ₗ[ℂ] U), (∀ g x, σ g (κ x) = κ (TensorProduct.map (ρ₀ fun i => g (toLex (.inl i))) (ρ₁ fun j => g (toLex (.inr j))) x)) → Nonempty ((ind₂ h (extTensor (parInd ψ₀ ρ₀) (parInd ψ₁ ρ₁))).Equiv (parInd E σ)) := by
  first | exact @GlobalTheory.SmGL.StagesTwo.ind₂_parInd_parInd_equiv | exact GlobalTheory.SmGL.StagesTwo.ind₂_parInd_parInd_equiv | (intros; apply GlobalTheory.SmGL.StagesTwo.ind₂_parInd_parInd_equiv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionProductEquivOfNoBlocks
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionProductEquivOfNoBlocks
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.EmptyProd

open GlobalTheory.SmGL.MultiIrr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def lineEquiv {α n : Type} [Fintype α] [LinearOrder α] [IsEmpty α] [Fintype n] [DecidableEq n]
    {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] (e : (Σ a, m a) ≃ n)
    {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)]
    (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) : IndSp e (piTensor σ) ≃ₗ[ℂ] ℂ :=
  haveI : IsEmpty n := ⟨fun x => isEmptyElim (e.symm x).1⟩
  haveI : Subsingleton (GL n k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  (LinearEquiv.ofBijective (ev _ 1) ⟨fun f g h =>
    Subtype.ext (Subtype.ext (funext fun x => by rw [Subsingleton.elim x 1]; exact h)), fun v =>
    ⟨⟨⟨fun _ => v, fun p _ => by rw [Subsingleton.elim p 1, map_one]; rfl⟩,
      mem_smooth_of_eventually _ (.of_forall fun _ _ => rfl)⟩, rfl⟩⟩).trans
    (PiTensorProduct.isEmptyEquiv _)

theorem multiProd_equiv_of_isEmpty : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α α' n : Type} [Fintype α] [LinearOrder α] [IsEmpty α] [Fintype α']
    [LinearOrder α'] [IsEmpty α'] [Fintype n] [DecidableEq n] {m : α → Type} [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] {m' : α' → Type} [∀ a, Fintype (m' a)] [∀ a, DecidableEq (m' a)]
    (e : (Σ a, m a) ≃ n) (e' : (Σ a, m' a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)]
    [∀ a, Module ℂ (X a)] {X' : α' → Type} [∀ a, AddCommGroup (X' a)] [∀ a, Module ℂ (X' a)]
    (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (σ' : ∀ a, Representation ℂ (GL (m' a) k) (X' a)),
    Nonempty ((multiProd e σ).Equiv (multiProd e' σ')) := by
  intro k _ _ _ _ α α' n _ _ _ _ _ _ _ _ m _ _ m' _ _ e e' X _ _ X' _ _ σ σ'
  haveI : IsEmpty n := ⟨fun x => isEmptyElim (e.symm x).1⟩
  haveI : Subsingleton (GL n k) := ⟨fun _ _ => Units.ext (Subsingleton.elim _ _)⟩
  refine ⟨Representation.Equiv.mk ((lineEquiv e σ).trans (lineEquiv e' σ').symm) fun g => ?_⟩
  rw [Subsingleton.elim g 1, map_one, map_one]
  rfl

end GlobalTheory.EmptyProd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionProductEquivOfNoBlocksStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.parabolicInductionProduct_equiv_of_no_blocks : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {α α' n : Type} [Fintype α] [LinearOrder α] [IsEmpty α] [Fintype α'] [LinearOrder α'] [IsEmpty α'] [Fintype n] [DecidableEq n] {m : α → Type} [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] {m' : α' → Type} [∀ a, Fintype (m' a)] [∀ a, DecidableEq (m' a)] (e : (Σ a, m a) ≃ n) (e' : (Σ a, m' a) ≃ n) {X : α → Type} [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] {X' : α' → Type} [∀ a, AddCommGroup (X' a)] [∀ a, Module ℂ (X' a)] (σ : ∀ a, Representation ℂ (GL (m a) k) (X a)) (σ' : ∀ a, Representation ℂ (GL (m' a) k) (X' a)), Nonempty ((multiProd e σ).Equiv (multiProd e' σ')) := by
  first | exact @GlobalTheory.EmptyProd.multiProd_equiv_of_isEmpty | exact GlobalTheory.EmptyProd.multiProd_equiv_of_isEmpty | (intros; apply GlobalTheory.EmptyProd.multiProd_equiv_of_isEmpty <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LexSumSplitFirstBlockStrictMono
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LexSumSplitFirstBlockStrictMono
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

namespace GlobalTheory

theorem lexSumSplit_strictMono : ∀ (s : ℕ) (t : Fin (s + 1) → ℕ), StrictMono fun c : Fin (t 0) ⊕ₗ (Σₗ i : Fin s, Fin (t i.succ)) => (Sum.elim (fun j => toLex (⟨0, j⟩ : Σ a, Fin (t a))) (fun x => toLex (⟨(ofLex x).1.succ, (ofLex x).2⟩ : Σ a, Fin (t a))) (ofLex c) : Σₗ a, Fin (t a)) := by
  intro s t a b hab
  induction a using Lex.rec with | _ a => ?_
  induction b using Lex.rec with | _ b => ?_
  rcases a with j | x <;> rcases b with j' | x'
  · have h : j < j' := Sum.Lex.inl_lt_inl_iff.mp hab
    simp only [ofLex_toLex, Sum.elim_inl]
    exact Sigma.Lex.right _ _ h
  · simp only [ofLex_toLex, Sum.elim_inl, Sum.elim_inr]
    exact Sigma.Lex.left _ _ (Fin.succ_pos _)
  · exact absurd hab (not_lt_of_gt (Sum.Lex.inl_lt_inr _ _))
  · have h : x < x' := Sum.Lex.inr_lt_inr_iff.mp hab
    simp only [ofLex_toLex, Sum.elim_inr]
    induction x using Lex.rec with | _ x => ?_
    induction x' using Lex.rec with | _ x' => ?_
    rcases x with ⟨i, j⟩
    rcases x' with ⟨i', j'⟩
    change Sigma.Lex (· < ·) (fun _ => (· < ·)) (⟨i, j⟩ : Σ a : Fin s, Fin (t a.succ)) ⟨i', j'⟩ at h
    change Sigma.Lex (· < ·) (fun _ => (· < ·)) (⟨i.succ, j⟩ : Σ a, Fin (t a)) ⟨i'.succ, j'⟩
    rcases h with ⟨_, _, hi⟩ | ⟨_, _, hj⟩
    · exact Sigma.Lex.left _ _ (Fin.succ_lt_succ_iff.mpr hi)
    · exact Sigma.Lex.right _ _ hj

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LexSumSplitFirstBlockStrictMonoStatement
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lexSum_splitFirstBlock_strictMono : ∀ (s : ℕ) (t : Fin (s + 1) → ℕ), StrictMono fun c : Fin (t 0) ⊕ₗ (Σₗ i : Fin s, Fin (t i.succ)) => (Sum.elim (fun j => toLex (⟨0, j⟩ : Σ a, Fin (t a))) (fun x => toLex (⟨(ofLex x).1.succ, (ofLex x).2⟩ : Σ a, Fin (t a))) (ofLex c) : Σₗ a, Fin (t a)) := by
  first | exact @GlobalTheory.lexSumSplit_strictMono | exact GlobalTheory.lexSumSplit_strictMono | (intros; apply GlobalTheory.lexSumSplit_strictMono <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSubquotientParIndProductsFlattened
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section
open ValuativeRel Matrix GlobalTheory.SmGL.MultiIrr GlobalTheory.LocGL
open scoped TensorProduct

namespace GlobalTheory.SmGL.Stages

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ind₂_equiv_right {a b n V W U : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype n] [DecidableEq n] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] (h : a ⊕ b ≃ n) (A : Representation ℂ (GL a k) V)
    {B : Representation ℂ (GL b k) W} {B' : Representation ℂ (GL b k) U} (φ : B.Equiv B') :
    Nonempty ((ind₂ h (extTensor A B)).Equiv (ind₂ h (extTensor A B'))) := by
  refine ⟨parIndEquiv _ (compEquiv (.mk (φ.toLinearEquiv.lTensor V) fun g => ?_) _)⟩
  refine TensorProduct.ext' fun v w => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.lTensor_tmul, extTensor_tmul]
  congr 1
  exact φ.toIntertwiningMap.isIntertwining _ _ _ _

theorem piTensor_tmulEquivDep {β₀ β₁ : Type} {Γ X : β₀ ⊕ₗ β₁ → Type} [∀ c, Group (Γ c)]
    [∀ c, AddCommGroup (X c)] [∀ c, Module ℂ (X c)] (ρ : ∀ c, Representation ℂ (Γ c) (X c)) (g : ∀ c, Γ c)
    (x : (⨂[ℂ] i, X (toLex (.inl i))) ⊗[ℂ] (⨂[ℂ] j, X (toLex (.inr j)))) :
    piTensor ρ g (PiTensorProduct.tmulEquivDep ℂ (fun c => X (toLex c)) x) =
      PiTensorProduct.tmulEquivDep ℂ (fun c => X (toLex c))
      (TensorProduct.map (piTensor (fun i => ρ (toLex (.inl i))) fun i => g (toLex (.inl i)))
        (piTensor (fun j => ρ (toLex (.inr j))) fun j => g (toLex (.inr j))) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact map_zero (piTensor ρ g)
  | add x y hx hy => simp only [map_add (f := _)]; exact (map_add (piTensor ρ g) _ _).trans (by rw [hx, hy]; rfl)
  | tmul v w =>
    induction v using PiTensorProduct.induction_on with
    | add v v' hv hv' => simp only [TensorProduct.add_tmul, map_add (f := _)]; exact (map_add (piTensor ρ g) _ _).trans (by rw [hv, hv']; rfl)
    | smul_tprod c v =>
      induction w using PiTensorProduct.induction_on with
      | add w w' hw hw' => simp only [TensorProduct.tmul_add, map_add (f := _)]; exact (map_add (piTensor ρ g) _ _).trans (by rw [hw, hw']; rfl)
      | smul_tprod c' w =>
        have key : piTensor ρ g (PiTensorProduct.tmulEquivDep ℂ (fun c => X (toLex c))
            (PiTensorProduct.tprod ℂ v ⊗ₜ PiTensorProduct.tprod ℂ w)) =
            PiTensorProduct.tmulEquivDep ℂ (fun c => X (toLex c))
              (PiTensorProduct.tprod ℂ (fun a => ρ (toLex (.inl a)) (g (toLex (.inl a))) (v a)) ⊗ₜ
                PiTensorProduct.tprod ℂ (fun a => ρ (toLex (.inr a)) (g (toLex (.inr a))) (w a))) := by
          rw [PiTensorProduct.tmulEquivDep_apply, PiTensorProduct.tmulEquivDep_apply]
          refine (piTensor_tprod ρ g _).trans ?_
          congr 1
          funext i
          rcases i with i | i <;> rfl
        simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_smul, TensorProduct.map_tmul,
          piTensor_tprod]
        rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul',
          ← TensorProduct.smul_tmul', map_smul, map_smul, map_smul, map_smul, ← key]
        exact (LinearMap.map_smul _ _ _).trans (congrArg _ (LinearMap.map_smul _ _ _))

def splitEquiv {s : ℕ} (t : Fin (s + 1) → ℕ) :
    (Fin (t 0) ⊕ₗ Σₗ i : Fin s, Fin (t i.succ)) ≃ Σₗ a, Fin (t a) where
  toFun c := Sum.elim (fun j => toLex (⟨0, j⟩ : Σ a, Fin (t a)))
    (fun x => toLex (⟨(ofLex x).1.succ, (ofLex x).2⟩ : Σ a, Fin (t a))) (ofLex c)
  invFun c := Fin.cases (motive := fun a => Fin (t a) → Fin (t 0) ⊕ₗ Σₗ i : Fin s, Fin (t i.succ))
    (fun j => toLex (.inl j)) (fun i j => toLex (.inr (toLex ⟨i, j⟩))) (ofLex c).1 (ofLex c).2
  left_inv c := by
    rcases c with j | ⟨i, j⟩ <;> rfl
  right_inv c := by
    obtain ⟨a, j⟩ := c
    induction a using Fin.cases <;> rfl

theorem stages_equiv (s : ℕ) : ∀ (d t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (X : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (X a b)] [∀ a b, Module ℂ (X a b)]
    (ρ : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (X a b)) (n : Type) [Fintype n] [DecidableEq n]
    (e : (Σ a, Fin (d a)) ≃ n),
    ∃ E : (Σ c : (Σₗ a, Fin (t a)), Fin (d' (ofLex c).1 (ofLex c).2)) ≃ n,
      Nonempty ((multiProd e fun a => multiProd (e' a) (ρ a)).Equiv
        (multiProd E fun c => ρ (ofLex c).1 (ofLex c).2)) := by
  induction s with
  | zero =>
    intro d t d' e' X _ _ ρ n _ _ e
    haveI : IsEmpty n := ⟨fun x => (e.symm x).1.elim0⟩
    haveI : IsEmpty (Σₗ a : Fin 0, Fin (t a)) := ⟨fun c => (ofLex c).1.elim0⟩
    haveI : IsEmpty (Σ c : (Σₗ a : Fin 0, Fin (t a)), Fin (d' (ofLex c).1 (ofLex c).2)) :=
      ⟨fun x => (ofLex x.1).1.elim0⟩
    let E : (Σ c : (Σₗ a : Fin 0, Fin (t a)), Fin (d' (ofLex c).1 (ofLex c).2)) ≃ n :=
      Equiv.equivOfIsEmpty _ _
    exact ⟨E, GlobalTheory.T.parabolicInductionProduct_equiv_of_no_blocks (k := k) _ _ _ _⟩
  | succ s ih =>
    intro d t d' e' X _ _ ρ n _ _ e
    have E1 := multiProd_succ_equiv (k := k) (m := fun a => Fin (d a))
      (X := fun a => IndSp (e' a) (piTensor (ρ a))) e fun a => multiProd (e' a) (ρ a)
    obtain ⟨E1⟩ := E1
    have E2 := ih (fun i => d i.succ) (fun i => t i.succ) (fun i => d' i.succ) (fun i => e' i.succ)
      (fun i => X i.succ) (fun i => ρ i.succ) _ (Equiv.refl _)
    obtain ⟨Er, ⟨E2⟩⟩ := E2
    let mS : Fin (t 0) ⊕ₗ (Σₗ i : Fin s, Fin (t i.succ)) → Type :=
      fun c => Fin (d' (ofLex (splitEquiv t c)).1 (ofLex (splitEquiv t c)).2)
    let Es : (Σ c, mS c) ≃ n := (Equiv.sumSigmaDistrib fun x => mS (toLex x)).trans
      ((Equiv.sumCongr (e' 0) Er).trans ((headTail _).trans e))
    have E4 := GlobalTheory.T.inductionInStages_twoFactors_equiv (k := k) (m := mS)
      (a := Fin (d 0)) (b := Σ i : Fin s, Fin (d i.succ)) (V := ⨂[ℂ] b, X 0 b) (W := ⨂[ℂ] c : Σₗ i : Fin s, Fin (t i.succ), X (ofLex c).1.succ (ofLex c).2)
      (U := ⨂[ℂ] c : Fin (t 0) ⊕ₗ (Σₗ i : Fin s, Fin (t i.succ)), X (ofLex (splitEquiv t c)).1 (ofLex (splitEquiv t c)).2) Es ((headTail _).trans e) (e' 0) Er
      (fun _ _ => rfl) (fun _ _ => rfl) (piTensor (ρ 0))
      (piTensor fun c : Σₗ i : Fin s, Fin (t i.succ) => ρ (ofLex c).1.succ (ofLex c).2)
      (piTensor fun c => ρ (ofLex (splitEquiv t c)).1 (ofLex (splitEquiv t c)).2)

      (PiTensorProduct.tmulEquivDep ℂ fun c => X (ofLex (splitEquiv t (toLex c))).1 (ofLex (splitEquiv t (toLex c))).2)
      fun g x => piTensor_tmulEquivDep (X := fun c => X (ofLex (splitEquiv t c)).1 (ofLex (splitEquiv t c)).2)
        (fun c => ρ (ofLex (splitEquiv t c)).1 (ofLex (splitEquiv t c)).2) g x
    obtain ⟨E4⟩ := E4
    have E2' : (multiProd (Equiv.refl _) fun i : Fin s => multiProd (e' i.succ) (ρ i.succ)).Equiv
        (parInd (m := fun j => mS (toLex (Sum.inr j))) Er (piTensor fun c : Σₗ i : Fin s, Fin (t i.succ) => ρ (ofLex c).1.succ (ofLex c).2)) := E2
    have E3 := ind₂_equiv_right ((headTail fun i => Fin (d i)).trans e)
      (parInd (α := Fin (t 0)) (m := fun i => mS (toLex (Sum.inl i))) (e' 0) (piTensor (ρ 0))) E2'
    obtain ⟨E3⟩ := E3
    let Esig : (Σ c : (Σₗ a, Fin (t a)), Fin (d' (ofLex c).1 (ofLex c).2)) ≃ n :=
      (Equiv.sigmaCongrLeft (β := fun c : Σₗ a, Fin (t a) => Fin (d' (ofLex c).1 (ofLex c).2))
        (splitEquiv t)).symm.trans Es
    have E5 := GlobalTheory.T.parabolicInductionProduct_block_renaming_equiv (k := k) (splitEquiv t) (GlobalTheory.T.lexSum_splitFirstBlock_strictMono s t) (splitEquiv t).surjective
      Esig Es (fun c' x => congrArg Es ((Equiv.sigmaCongrLeft
        (β := fun c : Σₗ a, Fin (t a) => Fin (d' (ofLex c).1 (ofLex c).2)) (splitEquiv t)).symm_apply_apply ⟨c', x⟩).symm) fun c => ρ (ofLex c).1 (ofLex c).2
    obtain ⟨E5⟩ := E5
    exact ⟨Esig, ⟨E1.symm.trans (E3.trans (E4.trans E5.symm))⟩⟩

theorem isSubquotient_multiProd_multiProd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (s n : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (t : Fin s → ℕ)
    (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (X : ∀ a, Fin (t a) → Type)
    [∀ a b, AddCommGroup (X a b)] [∀ a b, Module ℂ (X a b)]
    (ρ : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (X a b)) (_ : ∀ a b, IsSmooth (ρ a b)) :
    ∃ E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n,
      IsSubquotient (multiProd e fun a => multiProd (e' a) (ρ a))
        (multiProd E fun c => ρ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) := by
  have hφ := stages_equiv (k := k) s d t d' e' X ρ (Fin n) e
  obtain ⟨E0, ⟨φ⟩⟩ := hφ
  let F : Fin (∑ a, t a) ≃ Σₗ a, Fin (t a) := finSigmaFinEquiv.symm.trans toLex
  let E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n :=
    (Equiv.sigmaCongrLeft (β := fun c : Σₗ a, Fin (t a) => Fin (d' (ofLex c).1 (ofLex c).2)) F).trans E0
  have hψ := GlobalTheory.T.parabolicInductionProduct_block_renaming_equiv (k := k) F (GlobalTheory.T.finSigmaFinEquiv_symm_strictMono_toLex s t) F.surjective E0 E
    (fun _ _ => rfl) fun c => ρ (ofLex c).1 (ofLex c).2
  obtain ⟨ψ⟩ := hψ
  exact ⟨E, .of_injective (φ.trans ψ).toIntertwiningMap (φ.trans ψ).toLinearEquiv.injective⟩

end GlobalTheory.SmGL.Stages
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSubquotientParIndProductsFlattenedStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSubquotient_parInd_products_flattened : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s n : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (X : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (X a b)] [∀ a b, Module ℂ (X a b)] (ρ : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (X a b)), (∀ a b, IsSmooth (ρ a b)) → ∃ E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n, IsSubquotient (multiProd e fun a => multiProd (e' a) (ρ a)) (multiProd E fun c => ρ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) := by
  first | exact @GlobalTheory.SmGL.Stages.isSubquotient_multiProd_multiProd | exact GlobalTheory.SmGL.Stages.isSubquotient_multiProd_multiProd | (intros; apply GlobalTheory.SmGL.Stages.isSubquotient_multiProd_multiProd <;> assumption)
end
