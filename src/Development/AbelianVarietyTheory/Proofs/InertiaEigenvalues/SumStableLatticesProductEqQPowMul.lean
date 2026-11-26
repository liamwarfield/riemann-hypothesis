module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DltEqZero
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardStableLattices

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieLatticeProdComapInlAndMapSnd
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ClearDenominators
namespace GlobalTheory.ClearDenominatorsIntegral

open GlobalTheory.UnitLemma

theorem clear_denominators (K : UQ) {V : Type} [AddCommGroup V] [Module (UQ.E K) V] [Module (UQ.O K) V]
    [IsScalarTower (UQ.O K) (UQ.E K) V] (M : Submodule (UQ.O K) V) {x : V}
    (hx : x ∈ Submodule.span (UQ.E K) (↑M : Set V)) :
    ∃ (d : UQ.O K), d ≠ (0 : UQ.O K) ∧ d • x ∈ M := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact M.smul_mem _ h₁
    · rw [mul_smul]; exact M.smul_mem _ h₂
  | smul e y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors (UQ.O K)) e
    have hb : (b : UQ.O K) ≠ 0 := nonZeroDivisors.coe_ne_zero b
    refine ⟨(b : UQ.O K) * d, mul_ne_zero hb hd, ?_⟩
    have key : (b : UQ.O K) • (e • y) = a • y := by
      rw [← smul_assoc, Algebra.smul_def, mul_comm, hab, algebraMap_smul]
    rw [mul_comm, mul_smul, key, smul_smul, mul_comm, ← smul_smul]
    exact M.smul_mem _ h

theorem main : ∀ (K : GlobalTheory.UnitLemma.UQ) {V : Type} [inst : AddCommGroup V] [inst_1 : Module (GlobalTheory.UnitLemma.UQ.E K) V] [inst_2 : Module (GlobalTheory.UnitLemma.UQ.O K) V] [IsScalarTower (GlobalTheory.UnitLemma.UQ.O K) (GlobalTheory.UnitLemma.UQ.E K) V] (M : Submodule (GlobalTheory.UnitLemma.UQ.O K) V) {x : V}, x ∈ Submodule.span (GlobalTheory.UnitLemma.UQ.E K) (↑M : Set V) → ∃ (d : GlobalTheory.UnitLemma.UQ.O K), d ≠ (0 : GlobalTheory.UnitLemma.UQ.O K) ∧ d • x ∈ M :=
  fun K _ _ _ _ _ M _ hx => clear_denominators K M hx

end GlobalTheory.ClearDenominatorsIntegral
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieLatticeProdComapInlAndMapSnd
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.LinPair

theorem exists_smul_mem_of_mem_span (K : UQ) {V : Type} [AddCommGroup V] [Module K.E V] [Module K.O V]
    [IsScalarTower K.O K.E V] (M : Submodule K.O V) {x : V} (hx : x ∈ Submodule.span K.E (M : Set V)) :
    ∃ d : K.O, d ≠ 0 ∧ d • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.ClearDenominatorsIntegral.main
  | exact _root_.GlobalTheory.ClearDenominatorsIntegral.main
  | (apply _root_.GlobalTheory.ClearDenominatorsIntegral.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClearDenominatorsIntegral.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClearDenominatorsIntegral.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClearDenominatorsIntegral.main ..)

end GlobalTheory.UnitLemma.LinPair

open GlobalTheory.UnitLemma.LinPair in
theorem GlobalTheory.UnitLemma.InvAlg.lin_fst_snd : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A)),
    M ∈ (B₁.prod B₂).Lin →
    M.comap (LinearMap.inl K.O B₁.A B₂.A) ∈ B₁.Lin ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) ∈ B₂.Lin := by
  intro K B₁ B₂ M hM
  obtain ⟨⟨hfg, hspan⟩, hg, hσ⟩ := hM
  have hg' : ∀ y ∈ M, ((B₁.g * y.1, B₂.g * y.2) : B₁.A × B₂.A) ∈ M := fun y hy => hg y hy
  have hσ' : ∀ y ∈ M, ((B₁.σ y.1, B₂.σ y.2) : B₁.A × B₂.A) ∈ M := fun y hy => hσ y hy
  replace hspan : Submodule.span K.E (M : Set (B₁.A × B₂.A)) = ⊤ := hspan
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨⟨hfg.map _, ?_⟩, ?_, ?_⟩⟩
  ·
    apply Submodule.fg_of_fg_map_injective (LinearMap.inl K.O B₁.A B₂.A) LinearMap.inl_injective
    exact isNoetherian_submodule.1 (isNoetherian_of_fg_of_noetherian M hfg) _ (Submodule.map_comap_le _ _)
  · rw [Submodule.eq_top_iff']
    intro y
    have hy : (y, (0 : B₂.A)) ∈ Submodule.span K.E (M : Set (B₁.A × B₂.A)) := by
      rw [hspan]
      exact Submodule.mem_top
    obtain ⟨d, hd, hdy⟩ := exists_smul_mem_of_mem_span K M hy
    have hdE : algebraMap K.O K.E d ≠ 0 := by
      rw [Ne, ← (algebraMap K.O K.E).map_zero]
      exact fun h => hd (IsFractionRing.injective K.O K.E h)
    have hmem : d • y ∈ M.comap (LinearMap.inl K.O B₁.A B₂.A) := by
      simpa [Submodule.mem_comap] using hdy
    refine (Submodule.smul_mem_iff _ hdE).mp ?_
    rw [algebraMap_smul]
    exact Submodule.subset_span hmem
  · intro y hy
    have := hg' _ hy
    simpa [Submodule.mem_comap] using this
  · intro y hy
    have := hσ' _ hy
    simpa [Submodule.mem_comap] using this
  · rw [Submodule.map_coe]
    have : ⇑(LinearMap.snd K.O B₁.A B₂.A) = ⇑(LinearMap.snd K.E B₁.A B₂.A) := rfl
    rw [this, ← Submodule.map_span, hspan, Submodule.map_top, LinearMap.range_eq_top]
    exact LinearMap.snd_surjective
  · rintro _ ⟨m, hm, rfl⟩
    exact ⟨_, hg' m hm, rfl⟩
  · rintro _ ⟨m, hm, rfl⟩
    exact ⟨_, hσ' m hm, rfl⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieLatticeProdComapInlAndMapSndStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieLattice_prod_comap_inl_and_map_snd : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A)), M ∈ (B₁.prod B₂).Lin → M.comap (LinearMap.inl K.O B₁.A B₂.A) ∈ B₁.Lin ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) ∈ B₂.Lin := by
  first | exact @GlobalTheory.UnitLemma.InvAlg.lin_fst_snd | exact GlobalTheory.UnitLemma.InvAlg.lin_fst_snd | (intros; apply GlobalTheory.UnitLemma.InvAlg.lin_fst_snd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFullLatticeProdOfComapInlMapSnd
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFullLatticeProdOfComapInlMapSnd
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem isLat_of_comap_inl_of_map_snd (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A))
    (h₁ : IsLat K.O K.E (M.comap (LinearMap.inl K.O B₁.A B₂.A)))
    (h₂ : IsLat K.O K.E (M.map (LinearMap.snd K.O B₁.A B₂.A))) : IsLat K.O K.E M := by
  obtain ⟨f₁, s₁⟩ := h₁
  obtain ⟨f₂, s₂⟩ := h₂
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_of_fg_inf_ker (LinearMap.snd K.O B₁.A B₂.A) f₂ ?_
    have : M ⊓ LinearMap.ker (LinearMap.snd K.O B₁.A B₂.A) =
        (M.comap (LinearMap.inl K.O B₁.A B₂.A)).map (LinearMap.inl K.O B₁.A B₂.A) := by
      ext ⟨a, b⟩
      simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.snd_apply, Submodule.mem_map,
        Submodule.mem_comap, LinearMap.inl_apply]
      constructor
      · rintro ⟨hM, rfl⟩
        exact ⟨a, hM, rfl⟩
      · rintro ⟨c, hc, he⟩
        rw [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        exact ⟨hc, rfl⟩
    rw [this]
    exact f₁.map _
  · set S := Submodule.span K.E (M : Set (B₁.A × B₂.A)) with hS
    have hinl : ∀ a : B₁.A, ((a, 0) : B₁.A × B₂.A) ∈ S := by
      intro a
      have ha : a ∈ Submodule.span K.E ((M.comap (LinearMap.inl K.O B₁.A B₂.A) : Submodule K.O B₁.A) : Set B₁.A) := by
        rw [s₁]; trivial
      have hle : (Submodule.span K.E ((M.comap (LinearMap.inl K.O B₁.A B₂.A) : Submodule K.O B₁.A) : Set B₁.A)).map
          (LinearMap.inl K.E B₁.A B₂.A) ≤ S := by
        rw [Submodule.map_span]
        apply Submodule.span_mono
        rintro _ ⟨c, hc, rfl⟩
        exact hc
      exact hle ⟨a, ha, rfl⟩
    have hsnd : S.map (LinearMap.snd K.E B₁.A B₂.A) = ⊤ := by
      rw [hS, Submodule.map_span, ← s₂]
      congr 1
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have hb : b ∈ S.map (LinearMap.snd K.E B₁.A B₂.A) := by rw [hsnd]; trivial
    obtain ⟨y, hy, hyb⟩ := hb
    have : ((a, b) : B₁.A × B₂.A) = y + (a - y.1, 0) := by
      ext
      · simp
      · simp [← hyb]
    rw [this]
    exact S.add_mem hy (hinl _)

end GlobalTheory.UnitLemma
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsFullLatticeProdOfComapInlMapSndStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFullLattice_prod_of_comap_inl_map_snd : ∀ (K : UQ) (B₁ B₂ : InvAlg K) (M : Submodule K.O (B₁.A × B₂.A)), IsLat K.O K.E (M.comap (LinearMap.inl K.O B₁.A B₂.A)) → IsLat K.O K.E (M.map (LinearMap.snd K.O B₁.A B₂.A)) → IsLat K.O K.E M := by
  first | exact @GlobalTheory.UnitLemma.isLat_of_comap_inl_of_map_snd | exact GlobalTheory.UnitLemma.isLat_of_comap_inl_of_map_snd | (intros; apply GlobalTheory.UnitLemma.isLat_of_comap_inl_of_map_snd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardSigmaStableProdLatticeExtSq
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardSigmaStableProdLatticeExtSq
open GlobalTheory.UnitLemma Polynomial

noncomputable section
namespace GlobalTheory.SigmaExtCount

section
variable {R Q : Type} [CommRing R] [AddCommGroup Q] [Module R Q] (τ : Q →+ Q)
    (hττ : ∀ f : Q, τ (τ f) = f) (θ θ' u : R) (hθ : ∀ f : Q, τ (θ • f) = θ' • τ f)
    (hu : ∀ f : Q, τ (u • f) = -(u • τ f)) (hinv : ∀ f : Q, u • ((θ - θ') • f) = f)
include hττ hθ hu hinv

theorem half_snd (f : Q) : τ (u • (f - τ f)) = u • (f - τ f) := by
  rw [hu, map_sub, hττ, ← smul_neg, neg_sub]

theorem half_fst (f : Q) : τ (f - θ • (u • (f - τ f))) = f - θ • (u • (f - τ f)) := by
  have h2 : (θ - θ') • (u • (f - τ f)) = f - τ f := by rw [smul_comm, hinv]
  rw [map_sub, hθ, half_snd τ hττ θ θ' u hθ hu hinv f]
  rw [sub_smul] at h2
  generalize u • (f - τ f) = b at h2 ⊢
  rw [← sub_eq_zero]
  have : τ f - θ' • b - (f - θ • b) = (θ • b - θ' • b) - (f - τ f) := by abel
  rw [this, h2, sub_self]

theorem half_left (a b : Q) (ha : τ a = a) (hb : τ b = b) :
    u • ((a + θ • b) - τ (a + θ • b)) = b := by
  rw [map_add (f := _), hθ, ha, hb]
  have : a + θ • b - (a + θ' • b) = (θ - θ') • b := by rw [sub_smul]; abel
  rw [this, hinv]

def halfEquiv : {f : Q // τ f = f} × {f : Q // τ f = f} ≃ Q where
  toFun p := p.1.1 + θ • p.2.1
  invFun f := (⟨f - θ • (u • (f - τ f)), half_fst τ hττ θ θ' u hθ hu hinv f⟩,
    ⟨u • (f - τ f), half_snd τ hττ θ θ' u hθ hu hinv f⟩)
  left_inv p := by
    obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := p
    have h := half_left τ hττ θ θ' u hθ hu hinv a b ha hb
    ext <;> simp only [h] <;> abel
  right_inv f := by simp
end

section Torsor
variable {O : Type} [CommRing O] {A₁ A₂ : Type} [AddCommGroup A₁] [Module O A₁] [AddCommGroup A₂]
  [Module O A₂] (M₁ : Submodule O A₁) (M₂ : Submodule O A₂)

def Ext (M : Submodule O (A₁ × A₂)) : Prop :=
  M.comap (LinearMap.inl O A₁ A₂) = M₁ ∧ M.map (LinearMap.snd O A₁ A₂) = M₂

variable {M₁ M₂}

theorem Ext.exists {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) (b : M₂) : ∃ x, (x, (b : A₂)) ∈ M := by
  obtain ⟨b, hb⟩ := b
  rw [← hM.2, Submodule.mem_map] at hb
  obtain ⟨y, hy, e⟩ := hb
  exact ⟨y.1, by simpa [← e] using hy⟩

theorem Ext.sub_mem {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) {x x' : A₁} {b : A₂}
    (h : (x, b) ∈ M) (h' : (x', b) ∈ M) : x - x' ∈ M₁ := by
  rw [← hM.1, Submodule.mem_comap]
  have := M.sub_mem h h'
  simpa using this

def Ext.fn {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) (b : M₂) : A₁ ⧸ M₁ :=
  Submodule.Quotient.mk (Classical.choose (hM.exists b))

theorem Ext.fn_eq {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) {x : A₁} (b : M₂)
    (h : (x, (b : A₂)) ∈ M) : hM.fn b = Submodule.Quotient.mk x := by
  unfold Ext.fn
  rw [Submodule.Quotient.eq]
  exact hM.sub_mem (Classical.choose_spec (hM.exists b)) h

def Ext.lin {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) : M₂ →ₗ[O] A₁ ⧸ M₁ where
  toFun := hM.fn
  map_add' b b' := by
    obtain ⟨x, hx⟩ := hM.exists b
    obtain ⟨x', hx'⟩ := hM.exists b'
    rw [hM.fn_eq b hx, hM.fn_eq b' hx', hM.fn_eq (b + b') (x := x + x') (by simpa using M.add_mem hx hx')]
    simp
  map_smul' o b := by
    obtain ⟨x, hx⟩ := hM.exists b
    rw [hM.fn_eq b hx, hM.fn_eq (o • b) (x := o • x) (by simpa using M.smul_mem o hx)]
    simp

theorem Ext.lin_eq {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) {x : A₁} (b : M₂)
    (h : (x, (b : A₂)) ∈ M) : hM.lin b = Submodule.Quotient.mk x := hM.fn_eq b h

theorem Ext.mem_iff {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) (y : A₁ × A₂) :
    y ∈ M ↔ ∃ h : y.2 ∈ M₂, Submodule.Quotient.mk y.1 = hM.lin ⟨y.2, h⟩ := by
  constructor
  · intro hy
    have h2 : y.2 ∈ M₂ := by rw [← hM.2]; exact ⟨y, hy, rfl⟩
    exact ⟨h2, (hM.lin_eq ⟨y.2, h2⟩ hy).symm⟩
  · rintro ⟨h2, e⟩
    obtain ⟨x, hx⟩ := hM.exists ⟨y.2, h2⟩
    rw [hM.lin_eq _ hx, Submodule.Quotient.eq] at e
    have h0 : (y.1 - x, (0 : A₂)) ∈ M := by
      have : LinearMap.inl O A₁ A₂ (y.1 - x) ∈ M := by
        rw [← Submodule.mem_comap, hM.1]; exact e
      simpa using this
    have := M.add_mem hx h0
    simpa using this

def graphSub (f : M₂ →ₗ[O] A₁ ⧸ M₁) : Submodule O (A₁ × A₂) where
  carrier := {y | ∃ h : y.2 ∈ M₂, Submodule.Quotient.mk y.1 = f ⟨y.2, h⟩}
  add_mem' := by
    rintro a b ⟨ha, ea⟩ ⟨hb, eb⟩
    refine ⟨M₂.add_mem ha hb, ?_⟩
    show _ = f (⟨a.2, ha⟩ + ⟨b.2, hb⟩)
    rw [map_add (f := _), ← ea, ← eb]; simp
  zero_mem' := ⟨M₂.zero_mem, by
    show _ = f 0
    simp⟩
  smul_mem' := by
    rintro o a ⟨ha, ea⟩
    refine ⟨M₂.smul_mem o ha, ?_⟩
    show _ = f (o • ⟨a.2, ha⟩)
    rw [map_smul, ← ea]; simp

theorem mem_graphSub (f : M₂ →ₗ[O] A₁ ⧸ M₁) (y : A₁ × A₂) :
    y ∈ graphSub f ↔ ∃ h : y.2 ∈ M₂, Submodule.Quotient.mk y.1 = f ⟨y.2, h⟩ := Iff.rfl

theorem graphSub_ext (f : M₂ →ₗ[O] A₁ ⧸ M₁) : Ext M₁ M₂ (graphSub f) := by
  constructor
  · ext x
    simp only [Submodule.mem_comap, LinearMap.inl_apply, mem_graphSub]
    constructor
    · rintro ⟨h, e⟩
      have : f ⟨0, h⟩ = 0 := by
        have : (⟨0, h⟩ : M₂) = 0 := rfl
        rw [this, map_zero]
      rw [this, Submodule.Quotient.mk_eq_zero] at e; exact e
    · intro hx
      refine ⟨M₂.zero_mem, ?_⟩
      rw [(Submodule.Quotient.mk_eq_zero M₁).2 hx]
      have : (⟨0, M₂.zero_mem⟩ : M₂) = 0 := rfl
      rw [this, map_zero]
  · ext b
    simp only [Submodule.mem_map, LinearMap.snd_apply]
    constructor
    · rintro ⟨y, ⟨h, _⟩, rfl⟩; exact h
    · intro hb
      obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective M₁ (f ⟨b, hb⟩)
      exact ⟨(x, b), ⟨hb, hx⟩, rfl⟩

def extEquiv : {M : Submodule O (A₁ × A₂) // Ext M₁ M₂ M} ≃ (M₂ →ₗ[O] A₁ ⧸ M₁) where
  toFun M := M.2.lin
  invFun f := ⟨graphSub f, graphSub_ext f⟩
  left_inv M := by
    apply Subtype.ext
    ext y
    rw [mem_graphSub, M.2.mem_iff]
  right_inv f := by
    ext b
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective M₁ (f b)
    have hm : (x, (b : A₂)) ∈ graphSub f := ⟨b.2, hx⟩
    exact ((graphSub_ext f).lin_eq b hm).trans hx

end Torsor

section Twist
variable {O : Type} [CommRing O] {cO : O →+* O} {A₁ A₂ : Type} [AddCommGroup A₁] [Module O A₁]
  [AddCommGroup A₂] [Module O A₂] {M₁ : Submodule O A₁} {M₂ : Submodule O A₂}

def compat (g₁ : A₁ →ₗ[O] A₁) (g₂ : A₂ →ₗ[O] A₂) (hg₁ : M₁ ≤ M₁.comap g₁) (hg₂ : M₂ ≤ M₂.comap g₂) :
    Submodule O (M₂ →ₗ[O] A₁ ⧸ M₁) where
  carrier := {f | ∀ b : M₂, f ⟨g₂ b, hg₂ b.2⟩ = M₁.mapQ M₁ g₁ hg₁ (f b)}
  add_mem' := by
    intro f f' hf hf' b
    simp only [LinearMap.add_apply, hf b, hf' b, map_add (f := _)]
  zero_mem' := by intro b; simp
  smul_mem' := by
    intro o f hf b
    simp only [LinearMap.smul_apply, hf b, map_smul]

theorem gstab_iff (g₁ : A₁ →ₗ[O] A₁) (g₂ : A₂ →ₗ[O] A₂) (hg₁ : M₁ ≤ M₁.comap g₁)
    (hg₂ : M₂ ≤ M₂.comap g₂) {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) :
    (∀ y ∈ M, (g₁ y.1, g₂ y.2) ∈ M) ↔ hM.lin ∈ compat g₁ g₂ hg₁ hg₂ := by
  constructor
  · intro h b
    obtain ⟨x, hx⟩ := hM.exists b
    rw [hM.lin_eq b hx, Submodule.mapQ_apply]
    exact hM.lin_eq ⟨g₂ b, hg₂ b.2⟩ (h _ hx)
  · intro h y hy
    obtain ⟨h2, e⟩ := (hM.mem_iff y).1 hy
    rw [hM.mem_iff]
    refine ⟨hg₂ h2, ?_⟩
    have := h ⟨y.2, h2⟩
    simp only at this
    rw [this, ← e, Submodule.mapQ_apply]

variable (hcc : ∀ o, cO (cO o) = o) (σ₁ : A₁ →ₛₗ[cO] A₁) (σ₂ : A₂ →ₛₗ[cO] A₂)
  (hs₁ : M₁ ≤ M₁.comap σ₁) (hs₂ : M₂ ≤ M₂.comap σ₂)

def twist (f : M₂ →ₗ[O] A₁ ⧸ M₁) : M₂ →ₗ[O] A₁ ⧸ M₁ where
  toFun b := M₁.mapQ M₁ σ₁ hs₁ (f ⟨σ₂ b, hs₂ b.2⟩)
  map_add' b b' := by
    have : (⟨σ₂ (b + b' : M₂), hs₂ (b + b').2⟩ : M₂) = ⟨σ₂ b, hs₂ b.2⟩ + ⟨σ₂ b', hs₂ b'.2⟩ :=
      Subtype.ext (by simp)
    rw [this, map_add (f := _), map_add (f := _)]
  map_smul' o b := by
    have : (⟨σ₂ (o • b : M₂), hs₂ (o • b).2⟩ : M₂) = cO o • ⟨σ₂ b, hs₂ b.2⟩ :=
      Subtype.ext (by simp)
    rw [this, map_smul, LinearMap.map_smulₛₗ, hcc]
    rfl

theorem twist_apply (f : M₂ →ₗ[O] A₁ ⧸ M₁) (b : M₂) :
    twist hcc σ₁ σ₂ hs₁ hs₂ f b = M₁.mapQ M₁ σ₁ hs₁ (f ⟨σ₂ b, hs₂ b.2⟩) := rfl

def twistHom : (M₂ →ₗ[O] A₁ ⧸ M₁) →+ (M₂ →ₗ[O] A₁ ⧸ M₁) where
  toFun := twist hcc σ₁ σ₂ hs₁ hs₂
  map_zero' := by ext b; simp [twist_apply]
  map_add' f f' := by ext b; simp [twist_apply]

theorem twist_smul (r : O) (f : M₂ →ₗ[O] A₁ ⧸ M₁) :
    twist hcc σ₁ σ₂ hs₁ hs₂ (r • f) = cO r • twist hcc σ₁ σ₂ hs₁ hs₂ f := by
  ext b; simp [twist_apply]

theorem twist_twist (hσ₁ : ∀ x, σ₁ (σ₁ x) = x) (hσ₂ : ∀ x, σ₂ (σ₂ x) = x)
    (f : M₂ →ₗ[O] A₁ ⧸ M₁) : twist hcc σ₁ σ₂ hs₁ hs₂ (twist hcc σ₁ σ₂ hs₁ hs₂ f) = f := by
  ext b
  rw [twist_apply, twist_apply]
  have hb : (⟨σ₂ (σ₂ b), hs₂ (hs₂ b.2)⟩ : M₂) = b := Subtype.ext (hσ₂ _)
  simp only [hb]
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective M₁ (f b)
  rw [← hx, Submodule.mapQ_apply, Submodule.mapQ_apply, hσ₁]

theorem twist_mem (g₁ : A₁ →ₗ[O] A₁) (g₂ : A₂ →ₗ[O] A₂) (hg₁ : M₁ ≤ M₁.comap g₁)
    (hg₂ : M₂ ≤ M₂.comap g₂) (hc₁ : ∀ x, σ₁ (g₁ x) = g₁ (σ₁ x)) (hc₂ : ∀ x, σ₂ (g₂ x) = g₂ (σ₂ x))
    {f : M₂ →ₗ[O] A₁ ⧸ M₁} (hf : f ∈ compat g₁ g₂ hg₁ hg₂) :
    twist hcc σ₁ σ₂ hs₁ hs₂ f ∈ compat g₁ g₂ hg₁ hg₂ := by
  intro b
  rw [twist_apply, twist_apply]
  have hb : (⟨σ₂ (g₂ b), hs₂ (hg₂ b.2)⟩ : M₂) = ⟨g₂ (σ₂ b), hg₂ (hs₂ b.2)⟩ := Subtype.ext (hc₂ _)
  simp only [hb]
  rw [hf ⟨σ₂ b, hs₂ b.2⟩]
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective M₁ (f ⟨σ₂ b, hs₂ b.2⟩)
  rw [← hx]
  simp only [Submodule.mapQ_apply, hc₁]

theorem sstab_iff (hσ₂ : ∀ x, σ₂ (σ₂ x) = x) {M : Submodule O (A₁ × A₂)} (hM : Ext M₁ M₂ M) :
    (∀ y ∈ M, (σ₁ y.1, σ₂ y.2) ∈ M) ↔ twist hcc σ₁ σ₂ hs₁ hs₂ hM.lin = hM.lin := by
  constructor
  · intro h
    ext b
    rw [twist_apply]
    obtain ⟨x, hx⟩ := hM.exists ⟨σ₂ b, hs₂ b.2⟩
    rw [hM.lin_eq _ hx, Submodule.mapQ_apply]
    have := h _ hx
    simp only [hσ₂] at this
    exact (hM.lin_eq b this).symm
  · intro h y hy
    obtain ⟨h2, e⟩ := (hM.mem_iff y).1 hy
    rw [hM.mem_iff]
    refine ⟨hs₂ h2, ?_⟩
    simp only
    rw [← h, twist_apply]
    have hb : (⟨σ₂ (σ₂ y.2), hs₂ (hs₂ h2)⟩ : M₂) = ⟨y.2, h2⟩ := Subtype.ext (hσ₂ _)
    simp only [hb]
    rw [← e, Submodule.mapQ_apply]

end Twist

section Count
variable {O : Type} [CommRing O] {cO : O →+* O} {A₁ A₂ : Type} [AddCommGroup A₁] [Module O A₁]
  [AddCommGroup A₂] [Module O A₂] {M₁ : Submodule O A₁} {M₂ : Submodule O A₂}

theorem conj_inv_eq_neg (hcc : ∀ o, cO (cO o) = o) (θ : O) (hδ : IsUnit (θ - cO θ)) :
    cO ((hδ.unit⁻¹ : Oˣ) : O) = -((hδ.unit⁻¹ : Oˣ) : O) := by
  set u : O := ((hδ.unit⁻¹ : Oˣ) : O)
  have hu1 : u * (θ - cO θ) = 1 := hδ.val_inv_mul
  have h1 : cO u * (-(θ - cO θ)) = 1 := by
    have : cO (θ - cO θ) = -(θ - cO θ) := by rw [map_sub, hcc, neg_sub]
    rw [← this, ← map_mul, hu1, map_one]
  linear_combination (-u) * h1 + (-cO u) * hu1

theorem card_stable_sq (hcc : ∀ o, cO (cO o) = o) (θ : O) (hδ : IsUnit (θ - cO θ))
    (g₁ : A₁ →ₗ[O] A₁) (g₂ : A₂ →ₗ[O] A₂) (σ₁ : A₁ →ₛₗ[cO] A₁) (σ₂ : A₂ →ₛₗ[cO] A₂)
    (hg₁ : M₁ ≤ M₁.comap g₁) (hg₂ : M₂ ≤ M₂.comap g₂) (hs₁ : M₁ ≤ M₁.comap σ₁) (hs₂ : M₂ ≤ M₂.comap σ₂)
    (hσ₁ : ∀ x, σ₁ (σ₁ x) = x) (hσ₂ : ∀ x, σ₂ (σ₂ x) = x)
    (hc₁ : ∀ x, σ₁ (g₁ x) = g₁ (σ₁ x)) (hc₂ : ∀ x, σ₂ (g₂ x) = g₂ (σ₂ x)) :
    Nat.card {M : Submodule O (A₁ × A₂) // ((∀ y ∈ M, (g₁ y.1, g₂ y.2) ∈ M) ∧
      ∀ y ∈ M, (σ₁ y.1, σ₂ y.2) ∈ M) ∧ Ext M₁ M₂ M} ^ 2 =
    Nat.card {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁ y.1, g₂ y.2) ∈ M) ∧ Ext M₁ M₂ M} := by
  set Q := compat g₁ g₂ hg₁ hg₂
  let τQ : Q →+ Q :=
    { toFun := fun f => ⟨twist hcc σ₁ σ₂ hs₁ hs₂ f.1, twist_mem hcc σ₁ σ₂ hs₁ hs₂ g₁ g₂ hg₁ hg₂ hc₁ hc₂ f.2⟩
      map_zero' := Subtype.ext (map_zero (twistHom hcc σ₁ σ₂ hs₁ hs₂))
      map_add' := fun f f' => Subtype.ext (map_add (twistHom hcc σ₁ σ₂ hs₁ hs₂) f.1 f'.1) }
  have hτ : ∀ f : Q, ((τQ f : Q) : M₂ →ₗ[O] A₁ ⧸ M₁) = twist hcc σ₁ σ₂ hs₁ hs₂ f.1 := fun _ => rfl
  set u : O := ((hδ.unit⁻¹ : Oˣ) : O)
  have hcu := conj_inv_eq_neg hcc θ hδ
  have e := halfEquiv τQ (fun f => Subtype.ext (by rw [hτ, hτ, twist_twist hcc σ₁ σ₂ hs₁ hs₂ hσ₁ hσ₂]))
    θ (cO θ) u (fun f => Subtype.ext (by rw [hτ, Submodule.coe_smul, Submodule.coe_smul, hτ, twist_smul]))
    (fun f => Subtype.ext (by
      rw [hτ, Submodule.coe_smul, Submodule.coe_neg, Submodule.coe_smul, hτ, twist_smul, hcu, neg_smul]))
    (fun f => by rw [smul_smul, hδ.val_inv_mul, one_smul])
  have e1 : {M : Submodule O (A₁ × A₂) // (∀ y ∈ M, (g₁ y.1, g₂ y.2) ∈ M) ∧ Ext M₁ M₂ M} ≃ Q :=
    (Equiv.subtypeEquivRight (fun M => and_comm)).trans
      ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans
        (Equiv.subtypeEquiv extEquiv (fun M => gstab_iff g₁ g₂ hg₁ hg₂ M.2)))
  have e2 : {M : Submodule O (A₁ × A₂) // ((∀ y ∈ M, (g₁ y.1, g₂ y.2) ∈ M) ∧
      ∀ y ∈ M, (σ₁ y.1, σ₂ y.2) ∈ M) ∧ Ext M₁ M₂ M} ≃ {f : Q // τQ f = f} :=
    (Equiv.subtypeEquivRight (fun M => and_comm)).trans
      ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).symm.trans
        ((Equiv.subtypeEquiv extEquiv (fun M => and_congr (gstab_iff g₁ g₂ hg₁ hg₂ M.2)
          (sstab_iff hcc σ₁ σ₂ hs₁ hs₂ hσ₂ M.2))).trans
        ((Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ Q) (fun f => twist hcc σ₁ σ₂ hs₁ hs₂ f = f)).symm.trans
          (Equiv.subtypeEquivRight (fun f => by rw [Subtype.ext_iff, hτ])))))
  rw [Nat.card_congr e2, Nat.card_congr e1, sq, ← Nat.card_prod, Nat.card_congr e]

end Count

section Special
open GlobalTheory.UnitLemma

def conjFun (K : UQ) (o : K.O) : K.O := Classical.choose (K.c_int o)

theorem algebraMap_conjFun (K : UQ) (o : K.O) :
    algebraMap K.O K.E (conjFun K o) = K.c (algebraMap K.O K.E o) :=
  (Classical.choose_spec (K.c_int o)).symm

def conjO (K : UQ) : K.O →+* K.O where
  toFun := conjFun K
  map_one' := IsFractionRing.injective K.O K.E (by simp only [algebraMap_conjFun, map_one])
  map_mul' a b := IsFractionRing.injective K.O K.E (by simp only [algebraMap_conjFun, map_mul])
  map_zero' := IsFractionRing.injective K.O K.E (by simp only [algebraMap_conjFun, map_zero])
  map_add' a b := IsFractionRing.injective K.O K.E (by simp only [algebraMap_conjFun, map_add (f := _)])

theorem algebraMap_conjO (K : UQ) (o : K.O) :
    algebraMap K.O K.E (conjO K o) = K.c (algebraMap K.O K.E o) := algebraMap_conjFun K o

theorem conjO_conjO (K : UQ) (o : K.O) : conjO K (conjO K o) = o :=
  IsFractionRing.injective K.O K.E (by rw [algebraMap_conjO, algebraMap_conjO, K.c_c])

def sigmaSL {K : UQ} (B : InvAlg K) : B.A →ₛₗ[conjO K] B.A where
  toFun := B.σ
  map_add' := map_add B.σ
  map_smul' o a := by
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply K.O K.E B.A,
      IsScalarTower.algebraMap_apply K.O K.E B.A (conjO K o), B.σ_alg, algebraMap_conjO]

theorem sigmaSL_apply {K : UQ} (B : InvAlg K) (a : B.A) : sigmaSL B a = B.σ a := rfl

theorem card_sigma_stable_ext_sq : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g →
    ∀ (M₁ : Submodule K.O B₁.A) (M₂ : Submodule K.O B₂.A), M₁ ∈ B₁.Lin → M₂ ∈ B₂.Lin →
    Nat.card {M : Submodule K.O (B₁.A × B₂.A) // ((∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧
      ∀ y ∈ M, (B₁.σ y.1, B₂.σ y.2) ∈ M) ∧ M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧
      M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} ^ 2 =
    Nat.card {M : Submodule K.O (B₁.A × B₂.A) // (∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧
      M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} := by
  intro K B₁ B₂ h1 h2 M₁ M₂ hM₁ hM₂
  obtain ⟨θ, θ', hθ, hδ⟩ := K.c_res
  have hθ' : conjO K θ = θ' := IsFractionRing.injective K.O K.E (by rw [algebraMap_conjO, hθ])
  have hu : IsUnit (θ - conjO K θ) := by
    rw [hθ']
    by_contra h
    exact hδ ((IsLocalRing.mem_maximalIdeal _).2 (mem_nonunits_iff.2 h))
  have hmul : ∀ y : B₁.A × B₂.A, (B₁.g, B₂.g) * y =
      (LinearMap.mulLeft K.O B₁.g y.1, LinearMap.mulLeft K.O B₂.g y.2) := fun y => rfl
  have key := card_stable_sq (conjO_conjO K) θ hu (LinearMap.mulLeft K.O B₁.g)
    (LinearMap.mulLeft K.O B₂.g) (sigmaSL B₁) (sigmaSL B₂) (M₁ := M₁) (M₂ := M₂)
    (fun x hx => by simpa using hM₁.2.1 x hx) (fun x hx => by simpa using hM₂.2.1 x hx)
    (fun x hx => hM₁.2.2 x hx) (fun x hx => hM₂.2.2 x hx) B₁.σ_σ B₂.σ_σ
    (fun x => by simp [sigmaSL_apply, h1]) (fun x => by simp [sigmaSL_apply, h2])
  simp only [hmul]
  exact key

end Special

end GlobalTheory.SigmaExtCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardSigmaStableProdLatticeExtSqStatement
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_sigma_stable_prod_lattice_ext_sq : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g → ∀ (M₁ : Submodule K.O B₁.A) (M₂ : Submodule K.O B₂.A), M₁ ∈ B₁.Lin → M₂ ∈ B₂.Lin → Nat.card {M : Submodule K.O (B₁.A × B₂.A) // ((∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧ ∀ y ∈ M, (B₁.σ y.1, B₂.σ y.2) ∈ M) ∧ M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} ^ 2 = Nat.card {M : Submodule K.O (B₁.A × B₂.A) // (∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧ M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} := by
  first | exact @GlobalTheory.SigmaExtCount.card_sigma_stable_ext_sq | exact GlobalTheory.SigmaExtCount.card_sigma_stable_ext_sq | (intros; apply GlobalTheory.SigmaExtCount.card_sigma_stable_ext_sq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumStableLatticesProductEqQPowMul
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology

noncomputable section

namespace GlobalTheory.UnitLemma.FibSum

theorem fib_card (K : UQ) (B₁ B₂ : InvAlg K) (hg₁ : B₁.σ B₁.g = B₁.g) (hg₂ : B₂.σ B₂.g = B₂.g)
    (hres : resultant B₁.P B₂.P ≠ 0)
    (M₁ : Submodule K.O B₁.A) (M₂ : Submodule K.O B₂.A) (h₁ : M₁ ∈ B₁.Lin) (h₂ : M₂ ∈ B₂.Lin) :
    (Nat.card {M : Submodule K.O (B₁.A × B₂.A) // M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} : ℚ) =
      (K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P) := by
  have hI := GlobalTheory.T.card_stable_lattices_alt K.O K.E B₁.A B₂.A B₁.g B₂.g hres M₁ M₂ h₁.1 h₂.1 h₁.2.1 h₂.2.1
  have hH := GlobalTheory.T.card_sigma_stable_prod_lattice_ext_sq K B₁ B₂ hg₁ hg₂ M₁ M₂ h₁ h₂
  have e : {M : Submodule K.O (B₁.A × B₂.A) // M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} ≃
      {M : Submodule K.O (B₁.A × B₂.A) // ((∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧
        ∀ y ∈ M, (B₁.σ y.1, B₂.σ y.2) ∈ M) ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} :=
    { toFun := fun M => ⟨M.1, ⟨M.2.1.2.1, M.2.1.2.2⟩, M.2.2⟩
      invFun := fun M => ⟨M.1, ⟨GlobalTheory.T.isFullLattice_prod_of_comap_inl_map_snd K B₁ B₂ M.1 (by rw [M.2.2.1]; exact h₁.1)
          (by rw [M.2.2.2]; exact h₂.1), M.2.1.1, M.2.1.2⟩, M.2.2⟩
      left_inv := fun M => rfl
      right_inv := fun M => rfl }
  rw [Nat.card_congr e]
  have hq2 : (Nat.card (IsLocalRing.ResidueField K.O) : ℚ) = (K.q : ℚ) ^ 2 := by
    rw [K.card_res]; push_cast; ring
  rw [hq2] at hI
  have hqpos : (0 : ℚ) < K.q := by
    have : 0 < Nat.card (IsLocalRing.ResidueField K.O) := Nat.card_pos
    rw [K.card_res] at this
    exact_mod_cast pos_of_ne_zero (fun h => by simp [h] at this)
  have hsq : ((Nat.card {M : Submodule K.O (B₁.A × B₂.A) // ((∀ y ∈ M, (B₁.g, B₂.g) * y ∈ M) ∧
        ∀ y ∈ M, (B₁.σ y.1, B₂.σ y.2) ∈ M) ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = M₁ ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = M₂} : ℚ)) ^ 2 =
      ((K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P)) ^ 2 := by
    have hpw : ((K.q : ℚ) ^ 2) ^ val K.O (resultant B₁.P B₂.P) = ((K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P)) ^ 2 := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    have hP₁ : (LinearMap.mulLeft K.E B₁.g).charpoly = B₁.P := rfl
    have hP₂ : (LinearMap.mulLeft K.E B₂.g).charpoly = B₂.P := rfl
    rw [hP₁, hP₂, hpw] at hI
    rw [← hI]
    exact_mod_cast hH
  exact (pow_left_inj₀ (by positivity) (zpow_pos hqpos _).le two_ne_zero).1 hsq

theorem fibsum : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g → (B₁.P * B₂.P).Separable → ∀ (φ₁ : Submodule K.O B₁.A → ℚ) (φ₂ : Submodule K.O B₂.A → ℚ), {M ∈ B₁.Lin | φ₁ M ≠ 0}.Finite → {M ∈ B₂.Lin | φ₂ M ≠ 0}.Finite → {M ∈ (B₁.prod B₂).Lin | φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) ≠ 0}.Finite ∧ ∑ᶠ M ∈ (B₁.prod B₂).Lin, φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) = (K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P) * ((∑ᶠ M ∈ B₁.Lin, φ₁ M) * ∑ᶠ M ∈ B₂.Lin, φ₂ M) := by
  intro K B₁ B₂ hg₁ hg₂ hsep φ₁ φ₂ hf₁ hf₂
  have hres : resultant B₁.P B₂.P ≠ 0 := resultant_ne_zero _ _ hsep.isCoprime
  set v := val K.O (resultant B₁.P B₂.P) with hv
  set π : Submodule K.O (B₁.prod B₂).A → Submodule K.O B₁.A × Submodule K.O B₂.A := fun M =>
    (M.comap (LinearMap.inl K.O B₁.A B₂.A), M.map (LinearMap.snd K.O B₁.A B₂.A)) with hπ
  suffices key : ∀ F : Submodule K.O (B₁.prod B₂).A → ℚ, (∀ M, F M =
      φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A))) →
      {M | M ∈ (B₁.prod B₂).Lin ∧ F M ≠ 0}.Finite ∧ ∑ᶠ M ∈ (B₁.prod B₂).Lin, F M =
        (K.q : ℚ) ^ v * ((∑ᶠ M ∈ B₁.Lin, φ₁ M) * ∑ᶠ M ∈ B₂.Lin, φ₂ M) from key _ (fun _ => rfl)
  intro F hF
  set s₁ := hf₁.toFinset
  set s₂ := hf₂.toFinset
  have hs₁ : ∀ M, M ∈ s₁ ↔ M ∈ B₁.Lin ∧ φ₁ M ≠ 0 := fun M => by simp [s₁]
  have hs₂ : ∀ M, M ∈ s₂ ↔ M ∈ B₂.Lin ∧ φ₂ M ≠ 0 := fun M => by simp [s₂]
  have hfibfin : ∀ p ∈ s₁ ×ˢ s₂, {M | M ∈ (B₁.prod B₂).Lin ∧ π M = p}.Finite := by
    intro p hp
    rw [Finset.mem_product, hs₁, hs₂] at hp
    have hc := fib_card K B₁ B₂ hg₁ hg₂ hres p.1 p.2 hp.1.1 hp.2.1
    have hqpos : (0 : ℚ) < K.q := by
      have : 0 < Nat.card (IsLocalRing.ResidueField K.O) := Nat.card_pos
      rw [K.card_res] at this
      exact_mod_cast pos_of_ne_zero (fun h => by simp [h] at this)
    have hne : Nat.card {M : Submodule K.O (B₁.A × B₂.A) // M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = p.1 ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = p.2} ≠ 0 := by
      intro h0
      rw [h0] at hc
      exact (zpow_pos hqpos v).ne' (by simpa using hc.symm)
    have := Nat.finite_of_card_ne_zero hne
    refine (Set.finite_coe_iff.1 ?_)
    have e : {M | M ∈ (B₁.prod B₂).Lin ∧ π M = p} = {M | M ∈ (B₁.prod B₂).Lin ∧
        M.comap (LinearMap.inl K.O B₁.A B₂.A) = p.1 ∧ M.map (LinearMap.snd K.O B₁.A B₂.A) = p.2} := by
      ext M; simp only [Set.mem_setOf_eq, hπ, Prod.ext_iff]
    rw [e]; exact this
  set W := {M | M ∈ (B₁.prod B₂).Lin ∧ π M ∈ s₁ ×ˢ s₂} with hW
  have hWfin : W.Finite := by
    refine (Set.Finite.biUnion (t := fun p => {M | M ∈ (B₁.prod B₂).Lin ∧ π M = p})
      (s₁ ×ˢ s₂).finite_toSet hfibfin).subset ?_
    intro M hM
    exact Set.mem_biUnion (x := π M) hM.2 (show M ∈ {M' | M' ∈ (B₁.prod B₂).Lin ∧ π M' = π M} from ⟨hM.1, rfl⟩)
  have hsupp : ∀ M ∈ (B₁.prod B₂).Lin, F M ≠ 0 → M ∈ W := by
    intro M hM hFM
    have hl := GlobalTheory.T.lieLattice_prod_comap_inl_and_map_snd K B₁ B₂ M hM
    rw [hF M] at hFM
    refine ⟨hM, Finset.mem_product.2 ⟨(hs₁ _).2 ⟨hl.1, left_ne_zero_of_mul hFM⟩,
      (hs₂ _).2 ⟨hl.2, right_ne_zero_of_mul hFM⟩⟩⟩
  refine ⟨hWfin.subset fun M hM => hsupp M hM.1 hM.2, ?_⟩
  have hL : ∑ᶠ M ∈ (B₁.prod B₂).Lin, F M = ∑ M ∈ hWfin.toFinset, F M := by
    have hset : (B₁.prod B₂).Lin ∩ Function.support F = W ∩ Function.support F := by
      ext M
      simp only [Set.mem_inter_iff, Function.mem_support]
      exact ⟨fun h => ⟨hsupp M h.1 h.2, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [← finsum_mem_eq_finite_toFinset_sum _ hWfin, ← finsum_mem_inter_support,
      ← finsum_mem_inter_support (s := W), hset]
  have h1 : ∑ᶠ M ∈ B₁.Lin, φ₁ M = ∑ M ∈ s₁, φ₁ M := by
    have hset : B₁.Lin ∩ Function.support φ₁ = {M | M ∈ B₁.Lin ∧ φ₁ M ≠ 0} ∩ Function.support φ₁ := by
      ext M
      simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [← finsum_mem_eq_finite_toFinset_sum _ hf₁, ← finsum_mem_inter_support,
      ← finsum_mem_inter_support (s := {M | M ∈ B₁.Lin ∧ φ₁ M ≠ 0}), hset]
  have h2 : ∑ᶠ M ∈ B₂.Lin, φ₂ M = ∑ M ∈ s₂, φ₂ M := by
    have hset : B₂.Lin ∩ Function.support φ₂ = {M | M ∈ B₂.Lin ∧ φ₂ M ≠ 0} ∩ Function.support φ₂ := by
      ext M
      simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_setOf_eq]
      exact ⟨fun h => ⟨⟨h.1, h.2⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩
    rw [← finsum_mem_eq_finite_toFinset_sum _ hf₂, ← finsum_mem_inter_support,
      ← finsum_mem_inter_support (s := {M | M ∈ B₂.Lin ∧ φ₂ M ≠ 0}), hset]
  rw [hL, h1, h2, ← Finset.sum_fiberwise_of_maps_to (s := hWfin.toFinset) (t := s₁ ×ˢ s₂) (g := π)
    (fun M hM => ((Set.Finite.mem_toFinset hWfin).1 hM).2), Finset.sum_mul_sum, ← Finset.sum_product', Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hin : ∀ M ∈ hWfin.toFinset.filter (fun M => π M = p), F M = φ₁ p.1 * φ₂ p.2 := by
    intro M hM
    have hM' := (Finset.mem_filter.1 hM).2
    rw [hF, ← hM']
  rw [Finset.sum_congr rfl hin, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hp' := hp
  rw [Finset.mem_product, hs₁, hs₂] at hp'
  rw [← fib_card K B₁ B₂ hg₁ hg₂ hres p.1 p.2 hp'.1.1 hp'.2.1]
  congr 1
  rw [← Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro M
  simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, hW, hπ, Prod.ext_iff]
  constructor
  · rintro ⟨⟨h, _⟩, h'⟩; exact ⟨h, h'⟩
  · rintro ⟨h, h'⟩
    refine ⟨⟨h, ?_⟩, h'⟩
    rw [Finset.mem_product]; rw [h'.1, h'.2]; exact Finset.mem_product.1 hp

end GlobalTheory.UnitLemma.FibSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumStableLatticesProductEqQPowMulStatement
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc Polynomial Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_stableLattices_product_eq_q_pow_mul : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.σ B₁.g = B₁.g → B₂.σ B₂.g = B₂.g → (B₁.P * B₂.P).Separable → ∀ (φ₁ : Submodule K.O B₁.A → ℚ) (φ₂ : Submodule K.O B₂.A → ℚ), {M ∈ B₁.Lin | φ₁ M ≠ 0}.Finite → {M ∈ B₂.Lin | φ₂ M ≠ 0}.Finite → {M ∈ (B₁.prod B₂).Lin | φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) ≠ 0}.Finite ∧ ∑ᶠ M ∈ (B₁.prod B₂).Lin, φ₁ (M.comap (LinearMap.inl K.O B₁.A B₂.A)) * φ₂ (M.map (LinearMap.snd K.O B₁.A B₂.A)) = (K.q : ℚ) ^ val K.O (resultant B₁.P B₂.P) * ((∑ᶠ M ∈ B₁.Lin, φ₁ M) * ∑ᶠ M ∈ B₂.Lin, φ₂ M) := by
  first | exact @GlobalTheory.UnitLemma.FibSum.fibsum | exact GlobalTheory.UnitLemma.FibSum.fibsum | (intros; apply GlobalTheory.UnitLemma.FibSum.fibsum <;> assumption)
end
