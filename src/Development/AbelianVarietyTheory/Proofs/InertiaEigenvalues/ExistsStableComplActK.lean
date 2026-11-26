module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaximalIdealIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitOfClosure

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplementedSup
namespace GlobalTheory.ComplementedSup

theorem complemented_sup :
    (let d1 : {K : Type} → [inst : Field K] → {Γ V : Type} → [inst_1 : AddCommGroup V] → [inst_2 : Module K V] → (Γ → V →ₗ[K] V) → Submodule K V → Prop := @(fun {K : Type} [Field K] {Γ V : Type} [AddCommGroup V] [Module K V] (f : Γ → V →ₗ[K] V) (S : Submodule K V) ↦ ∀ (γ : Γ), ∀ v ∈ S, (f γ : V → V) v ∈ S); let d2 : {K : Type} → [inst : Field K] → {Γ V : Type} → [inst_1 : AddCommGroup V] → [inst_2 : Module K V] → (Γ → V →ₗ[K] V) → Submodule K V → Prop := @(fun {K : Type} [Field K] {Γ V : Type} [AddCommGroup V] [Module K V] (f : Γ → V →ₗ[K] V) (Y : Submodule K V) ↦ ∀ (W : Submodule K V), d1 f W → W ≤ Y → ∃ (C : Submodule K V), d1 f C ∧ C ≤ Y ∧ W ⊓ C = ⊥ ∧ W ⊔ C = Y); ∀ {K : Type} [inst : Field K] {Γ V : Type} [inst_1 : AddCommGroup V] [inst_2 : Module K V] {f : Γ → V →ₗ[K] V} {X U : Submodule K V}, d1 f X → d1 f U → d2 f X → d2 f U → d2 f (X ⊔ U)) := by
  intro d1 d2 K _ Γ V _ _ f X U hX hU hXc hUc

  have hsup : ∀ A B : Submodule K V, d1 f A → d1 f B → d1 f (A ⊔ B) := by
    intro A B hA hB γ v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hA γ a ha) (hB γ b hb)
  have hinf : ∀ A B : Submodule K V, d1 f A → d1 f B → d1 f (A ⊓ B) := by
    intro A B hA hB γ v hv
    exact Submodule.mem_inf.mpr ⟨hA γ v (Submodule.mem_inf.mp hv).1, hB γ v (Submodule.mem_inf.mp hv).2⟩
  intro W hW hWle

  obtain ⟨D, hD, hDX, hD1, hD2⟩ := hXc (W ⊓ X) (hinf W X hW hX) inf_le_right
  obtain ⟨B, hB, hBU, hB1, hB2⟩ := hUc ((W ⊔ X) ⊓ U) (hinf _ U (hsup W X hW hX) hU) inf_le_right
  refine ⟨D ⊔ B, hsup D B hD hB, sup_le_sup hDX hBU, ?_, ?_⟩
  ·
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwW, hwDB⟩ := Submodule.mem_inf.mp hw
    obtain ⟨d, hd, b, hb, rfl⟩ := Submodule.mem_sup.mp hwDB
    have hbA : b ∈ (W ⊔ X) ⊓ U := by
      refine Submodule.mem_inf.mpr ⟨?_, hBU hb⟩
      have hbd : b = (d + b) - d := by abel
      rw [hbd]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left hwW) (Submodule.mem_sup_right (hDX hd))
    have hb0 : b = 0 := by
      have hb' : b ∈ (W ⊔ X) ⊓ U ⊓ B := Submodule.mem_inf.mpr ⟨hbA, hb⟩
      rw [hB1] at hb'
      exact (Submodule.mem_bot K).mp hb'
    subst hb0
    rw [add_zero] at hwW ⊢
    have hd' : d ∈ W ⊓ X ⊓ D := Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨hwW, hDX hd⟩, hd⟩
    rw [hD1] at hd'
    exact hd'
  · apply le_antisymm
    · exact sup_le hWle (sup_le_sup hDX hBU)
    · have hX' : X ≤ W ⊔ (D ⊔ B) := by
        rw [← hD2]
        exact sup_le (le_trans inf_le_left le_sup_left) (le_trans le_sup_left le_sup_right)
      have hU' : U ≤ W ⊔ (D ⊔ B) := by
        rw [← hB2]
        exact sup_le (le_trans inf_le_left (sup_le le_sup_left hX')) (le_trans le_sup_right le_sup_right)
      exact sup_le hX' hU'

end GlobalTheory.ComplementedSup
end

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual GlobalTheory.Pass.LocDual.OneX

namespace GlobalTheory.BlockSum

section General

variable {K : Type} [Field K] {Γ : Type}

def StableUnder {V : Type} [AddCommGroup V] [Module K V] (f : Γ → V →ₗ[K] V)
    (S : Submodule K V) : Prop :=
  ∀ γ, ∀ v ∈ S, f γ v ∈ S

def HasRelCompl {V : Type} [AddCommGroup V] [Module K V] (f : Γ → V →ₗ[K] V)
    (Y : Submodule K V) : Prop :=
  ∀ W : Submodule K V, StableUnder f W → W ≤ Y →
    ∃ C : Submodule K V, StableUnder f C ∧ C ≤ Y ∧ W ⊓ C = ⊥ ∧ W ⊔ C = Y

variable {V : Type} [AddCommGroup V] [Module K V] {f : Γ → V →ₗ[K] V}

theorem hasRelCompl_sup {X U : Submodule K V} (hXs : StableUnder f X) (hUs : StableUnder f U)
    (hX : HasRelCompl f X) (hU : HasRelCompl f U) : HasRelCompl f (X ⊔ U) := by
  first
  | exact @_root_.GlobalTheory.ComplementedSup.complemented_sup
  | exact _root_.GlobalTheory.ComplementedSup.complemented_sup
  | (apply _root_.GlobalTheory.ComplementedSup.complemented_sup <;> assumption)
  | (intros; apply _root_.GlobalTheory.ComplementedSup.complemented_sup <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ComplementedSup.complemented_sup <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ComplementedSup.complemented_sup ..)

end General

section Blocks

variable {K : Type} [Field K] {Γ : Type} {ι : Type} [DecidableEq ι]
  {n : Type} [Fintype n] [DecidableEq n]

def blockAct (ρ : Γ → ι → Matrix n n K) (γ : Γ) : (ι → n → K) →ₗ[K] (ι → n → K) :=
  LinearMap.pi (fun b => (Matrix.mulVecLin (ρ γ b)).comp (LinearMap.proj b))

theorem blockAct_apply (ρ : Γ → ι → Matrix n n K) (γ : Γ) (v : ι → n → K) (b : ι) :
    blockAct ρ γ v b = (ρ γ b).mulVec (v b) := rfl

def blockSub (s : Set ι) : Submodule K (ι → n → K) where
  carrier := {v | ∀ b, b ∉ s → v b = 0}
  add_mem' := by
    intro v w hv hw b hb
    simp [hv b hb, hw b hb]
  zero_mem' := by
    intro b _
    rfl
  smul_mem' := by
    intro c v hv b hb
    simp [hv b hb]

theorem blockSub_stable (ρ : Γ → ι → Matrix n n K) (s : Set ι) :
    StableUnder (blockAct ρ) (blockSub s : Submodule K (ι → n → K)) := by
  intro γ v hv b hb
  rw [blockAct_apply, hv b hb, Matrix.mulVec_zero]

theorem blockSub_mono {s t : Set ι} (h : s ⊆ t) :
    (blockSub s : Submodule K (ι → n → K)) ≤ blockSub t :=
  fun _ hv b hb => hv b (fun hs => hb (h hs))

theorem blockSub_empty : (blockSub (∅ : Set ι) : Submodule K (ι → n → K)) = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  funext b
  exact hv b (Set.notMem_empty b)

theorem blockSub_univ : (blockSub (Set.univ : Set ι) : Submodule K (ι → n → K)) = ⊤ := by
  rw [eq_top_iff]
  intro v _ b hb
  exact absurd (Set.mem_univ b) hb

theorem blockSub_insert (b : ι) (s : Set ι) :
    (blockSub (insert b s) : Submodule K (ι → n → K)) = blockSub s ⊔ blockSub {b} := by
  apply le_antisymm
  · intro v hv
    refine Submodule.mem_sup.mpr ⟨Function.update v b 0, ?_, Pi.single b (v b), ?_, ?_⟩
    · intro c hc
      by_cases h : c = b
      · subst h; simp
      · rw [Function.update_of_ne h]
        exact hv c (by simp [h, hc])
    · intro c hc
      have h : c ≠ b := by simpa using hc
      simp [h]
    · funext c
      by_cases h : c = b
      · subst h; simp
      · simp [h]
  · exact sup_le (blockSub_mono (Set.subset_insert _ _))
      (blockSub_mono (Set.singleton_subset_iff.mpr (Set.mem_insert _ _)))

def BlockHasCompl (ρ : Γ → ι → Matrix n n K) (b : ι) : Prop :=
  ∀ S : Submodule K (n → K), (∀ γ, ∀ y ∈ S, (ρ γ b).mulVec y ∈ S) →
    ∃ D : Submodule K (n → K), (∀ γ, ∀ y ∈ D, (ρ γ b).mulVec y ∈ D) ∧ IsCompl S D

theorem hasRelCompl_single (ρ : Γ → ι → Matrix n n K) (b : ι) (hb : BlockHasCompl ρ b) :
    HasRelCompl (blockAct ρ) (blockSub ({b} : Set ι) : Submodule K (ι → n → K)) := by
  intro W hW hWY
  obtain ⟨D', hD's, hc⟩ := hb (W.map (LinearMap.proj b)) (by
    rintro γ _ ⟨v, hv, rfl⟩
    exact ⟨blockAct ρ γ v, hW γ v hv, rfl⟩)
  have hDle : D'.map (LinearMap.single K (fun _ : ι => n → K) b) ≤ blockSub {b} := by
    rintro _ ⟨y, _, rfl⟩ c hc
    have h : c ≠ b := by simpa using hc
    simp [h]
  refine ⟨D'.map (LinearMap.single K (fun _ : ι => n → K) b), ?_, hDle, ?_, ?_⟩
  · rintro γ _ ⟨y, hy, rfl⟩
    refine ⟨(ρ γ b).mulVec y, hD's γ y hy, ?_⟩
    funext c
    rw [blockAct_apply]
    by_cases h : c = b
    · subst h; simp
    · simp [h]
  · rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvW, hvD⟩ := Submodule.mem_inf.mp hv
    obtain ⟨y, hy, rfl⟩ := hvD
    have hy0 : y = 0 := by
      have hm : y ∈ W.map (LinearMap.proj b) ⊓ D' :=
        Submodule.mem_inf.mpr ⟨⟨_, hvW, by simp⟩, hy⟩
      rw [hc.inf_eq_bot] at hm
      exact (Submodule.mem_bot K).mp hm
    subst hy0
    simp
  · apply le_antisymm (sup_le hWY hDle)
    intro u hu
    have hub : u b ∈ W.map (LinearMap.proj b) ⊔ D' := by
      rw [hc.sup_eq_top]; trivial
    obtain ⟨s', ⟨v, hv, rfl⟩, d', hd', hsum⟩ := Submodule.mem_sup.mp hub
    refine Submodule.mem_sup.mpr ⟨v, hv, Pi.single b d', ⟨d', hd', by simp⟩, ?_⟩
    funext c
    by_cases h : c = b
    · subst h
      simpa using hsum
    · have h1 : u c = 0 := hu c (by simpa using h)
      have h2 : v c = 0 := hWY hv c (by simpa using h)
      simp [h, h1, h2]

theorem hasRelCompl_finset (ρ : Γ → ι → Matrix n n K) (hblk : ∀ b, BlockHasCompl ρ b)
    (s : Finset ι) :
    HasRelCompl (blockAct ρ) (blockSub (s : Set ι) : Submodule K (ι → n → K)) := by
  refine Finset.induction_on s ?_ ?_
  · intro W _ hWY
    rw [Finset.coe_empty, blockSub_empty] at hWY ⊢
    refine ⟨⊥, fun γ v hv => ?_, le_rfl, inf_bot_eq _, ?_⟩
    · rw [(Submodule.mem_bot K).mp hv, map_zero]; exact Submodule.zero_mem _
    · rw [sup_bot_eq]; exact le_antisymm hWY bot_le
  · intro b s _ ih
    rw [Finset.coe_insert, blockSub_insert]
    exact hasRelCompl_sup (blockSub_stable ρ _) (blockSub_stable ρ _) ih
      (hasRelCompl_single ρ b (hblk b))

theorem exists_stable_compl [Fintype ι] (ρ : Γ → ι → Matrix n n K)
    (hblk : ∀ b, BlockHasCompl ρ b) (W : Submodule K (ι → n → K))
    (hW : StableUnder (blockAct ρ) W) :
    ∃ C : Submodule K (ι → n → K), StableUnder (blockAct ρ) C ∧ IsCompl W C := by
  have h := hasRelCompl_finset ρ hblk Finset.univ W hW
    (by rw [Finset.coe_univ, blockSub_univ]; exact le_top)
  rw [Finset.coe_univ, blockSub_univ] at h
  obtain ⟨C, hCs, _, h1, h2⟩ := h
  exact ⟨C, hCs, ⟨disjoint_iff.mpr h1, codisjoint_iff.mpr h2⟩⟩

end Blocks

end GlobalTheory.BlockSum

namespace GlobalTheory.BlockSum


set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_stable_compl_actK : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (Xs : Set (D.nd.X i)), GoodR D.nd i r → ∀ {a : ℕ} (x : Fin a → ↥Xs)
    (W : Submodule (KK D.nd i) (Fin a → Fin D.R.nV → KK D.nd i)),
    (∀ γ : GE D.nd, ∀ v ∈ W, actK i r Xs x γ v ∈ W) →
    ∃ C : Submodule (KK D.nd i) (Fin a → Fin D.R.nV → KK D.nd i),
    (∀ γ : GE D.nd, ∀ v ∈ C, actK i r Xs x γ v ∈ C) ∧ IsCompl W C := by
  intro D i r Xs hG a x W hW
  let ρ : GE D.nd → Fin a → Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i) :=
    fun γ b => (mapM (toK D.nd i) (rTwO D.nd i r ↑(x b))) γ
  have hact : ∀ γ v, actK i r Xs x γ v = blockAct ρ γ v := fun γ v => rfl
  have hblk : ∀ b, BlockHasCompl ρ b := by
    intro b
    have hss := (hG ↑(x b)).2.1
    set c : GE D.nd → KK D.nd i :=
      fun γ => toK D.nd i ((((chiU D.nd i 1)⁻¹ γ : (D.nd.O i)ˣ)) : D.nd.O i) with hcdef
    have hrel : ∀ γ, ρ γ b = c γ • (↑(mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r ↑(x b)) γ) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (KK D.nd i)) := by
      intro γ
      ext j k
      simp [ρ, c, mapM, rTwO, twistM, mapRep, rO]
    have hc0 : ∀ γ, c γ ≠ 0 := fun γ =>
      ((((chiU D.nd i 1)⁻¹ γ : (D.nd.O i)ˣ)).isUnit.map (toK D.nd i)).ne_zero
    intro S hS
    obtain ⟨D', hD', hcompl⟩ := hss S (by
      intro g y hy
      have h := hS g y hy
      rw [hrel, Matrix.smul_mulVec] at h
      have h2 := S.smul_mem (c g)⁻¹ h
      rwa [smul_smul, inv_mul_cancel₀ (hc0 g), one_smul] at h2)
    refine ⟨D', fun g y hy => ?_, hcompl⟩
    rw [hrel, Matrix.smul_mulVec]
    exact D'.smul_mem _ (hD' g y hy)
  obtain ⟨C, hCs, hc⟩ := exists_stable_compl ρ hblk W (fun γ v hv => by
    rw [← hact]; exact hW γ v hv)
  exact ⟨C, fun γ v hv => by rw [hact]; exact hCs γ v hv, hc⟩

end GlobalTheory.BlockSum
