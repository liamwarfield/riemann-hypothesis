module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.Blocks
public import Lemmata.GeneralBFactLeftVariant.Imports
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.Formula

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.DimStep
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.DimStepB
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.DimStepA
noncomputable section

namespace PI.WeylForKWork.DimensionInduction

open scoped InnerProductSpace
open Module

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι κ : Type*}

def Stab (ρ : ι → H →L[ℂ] H) (W : Submodule ℂ H) : Prop := ∀ i, ∀ v ∈ W, ρ i v ∈ W

def Irr (ρ : ι → H →L[ℂ] H) (W : Submodule ℂ H) : Prop :=
  ∀ W' : Submodule ℂ H, W' ≤ W → Stab ρ W' → W' = ⊥ ∨ W' = W

structure Good (ρ : ι → H →L[ℂ] H) : Prop where
  isom : ∀ i v, ‖ρ i v‖ = ‖v‖
  inv : ∀ i, ∃ j, ∀ v, ρ i (ρ j v) = v
  mul : ∀ i i', ∃ k, ∀ v, ρ i (ρ i' v) = ρ k v
  one : ∃ i, ∀ v, ρ i v = v

def Comm (ρ : ι → H →L[ℂ] H) (c : H →ₗ[ℂ] H) : Prop := ∀ i v, c (ρ i v) = ρ i (c v)

def commSub (ρ : ι → H →L[ℂ] H) : Submodule ℂ (H →ₗ[ℂ] H) where
  carrier := {c | Comm ρ c}
  add_mem' := by
    intro c d hc hd
    have hc : Comm ρ c := hc
    have hd : Comm ρ d := hd
    show Comm ρ (c + d)
    intro i v
    simp only [LinearMap.add_apply, map_add (f := _), hc i v, hd i v]
  zero_mem' := by
    show Comm ρ 0
    intro i v
    simp
  smul_mem' := by
    intro a c hc
    have hc : Comm ρ c := hc
    show Comm ρ (a • c)
    intro i v
    simp only [LinearMap.smul_apply, map_smul, hc i v]

def slice (ρ : ι → H →L[ℂ] H) (x₀ : H) : Submodule ℂ H where
  carrier := {v | ∃ c : H →ₗ[ℂ] H, Comm ρ c ∧ c x₀ = v}
  add_mem' := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    exact ⟨c + d, (commSub ρ).add_mem hc hd, rfl⟩
  zero_mem' := ⟨0, (commSub ρ).zero_mem, rfl⟩
  smul_mem' := by
    rintro a _ ⟨c, hc, rfl⟩
    exact ⟨a • c, (commSub ρ).smul_mem a hc, rfl⟩

variable {ρ : ι → H →L[ℂ] H} {ρ' : κ → H →L[ℂ] H}

lemma Good.inner (hρ : Good ρ) (i : ι) (x y : H) : ⟪ρ i x, ρ i y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let L : H →ₗᵢ[ℂ] H := ⟨(ρ i : H →ₗ[ℂ] H), hρ.isom i⟩
  exact L.inner_map_map x y

lemma stab_orth (hρ : Good ρ) {W : Submodule ℂ H} (hW : Stab ρ W) : Stab ρ Wᗮ := by
  intro i v hv
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro w hw
  obtain ⟨j, hj⟩ := hρ.inv i
  rw [← hj w, hρ.inner i]
  exact hv _ (hW j w hw)

lemma stab_inf {W W' : Submodule ℂ H} (h : Stab ρ W) (h' : Stab ρ W') : Stab ρ (W ⊓ W') := by
  intro i v hv
  exact ⟨h i v hv.1, h' i v hv.2⟩

lemma proj_comm (hρ : Good ρ) {W : Submodule ℂ H} [FiniteDimensional ℂ W] (hW : Stab ρ W) :
    Comm ρ (W.starProjection : H →ₗ[ℂ] H) := by
  intro i v
  have hWo := stab_orth hρ hW
  show W.starProjection (ρ i v) = ρ i (W.starProjection v)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hW i _ (W.orthogonalProjection v).2
  · intro w hw
    rw [← map_sub]
    exact (Submodule.mem_orthogonal' W _).1 (hWo i _ (W.sub_starProjection_mem_orthogonal v)) w hw

lemma comm_comp {c d : H →ₗ[ℂ] H} (hc : Comm ρ c) (hd : Comm ρ d) : Comm ρ (c ∘ₗ d) := by
  intro i v
  show c (d (ρ i v)) = ρ i (c (d v))
  rw [hd i v, hc i (d v)]

lemma kill {c : H →ₗ[ℂ] H} (hc : Comm ρ c) {X : Submodule ℂ H} (hXs : Stab ρ X) (hXi : Irr ρ X)
    {x₁ : H} (hx₁ : x₁ ∈ X) (h0 : x₁ ≠ 0) (hk : c x₁ = 0) : ∀ x ∈ X, c x = 0 := by
  have hst : Stab ρ (LinearMap.ker c ⊓ X) := by
    intro i v hv
    refine ⟨?_, hXs i v hv.2⟩
    show c (ρ i v) = 0
    rw [hc i v, LinearMap.mem_ker.1 hv.1, map_zero]
  rcases hXi _ inf_le_right hst with h | h
  · exfalso
    have hm : x₁ ∈ LinearMap.ker c ⊓ X := ⟨LinearMap.mem_ker.2 hk, hx₁⟩
    rw [h] at hm
    exact h0 ((Submodule.mem_bot ℂ).1 hm)
  · intro x hx
    rw [← h] at hx
    exact LinearMap.mem_ker.1 hx.1

lemma into (hρ : Good ρ) {c : H →ₗ[ℂ] H} (hc : Comm ρ c) {X W : Submodule ℂ H} [FiniteDimensional ℂ W]
    (hW : Stab ρ W) (hXs : Stab ρ X) (hXi : Irr ρ X) {x₁ : H} (hx₁ : x₁ ∈ X) (h0 : x₁ ≠ 0)
    (hin : c x₁ ∈ W) : ∀ x ∈ X, c x ∈ W := by
  set P : H →ₗ[ℂ] H := (W.starProjection : H →ₗ[ℂ] H) with hP
  have hd : Comm ρ (c - P ∘ₗ c) :=
    (commSub ρ).sub_mem hc (comm_comp (proj_comm hρ hW) hc)
  have h1 : (c - P ∘ₗ c) x₁ = 0 := by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe,
      Submodule.starProjection_eq_self_iff.2 hin, sub_self]
  intro x hx
  have h2 := kill hd hXs hXi hx₁ h0 h1 x hx
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe,
    sub_eq_zero] at h2
  rw [h2]
  exact (W.orthogonalProjection (c x)).2

lemma stab_map {c : H →ₗ[ℂ] H} (hc : Comm ρ c) {X : Submodule ℂ H} (hX : Stab ρ X) :
    Stab ρ (X.map c) := by
  rintro i _ ⟨x, hx, rfl⟩
  exact ⟨ρ i x, hX i x hx, hc i x⟩

lemma stab_iSup {ν : Sort*} {F : ν → Submodule ℂ H} (hF : ∀ k, Stab ρ (F k)) :
    Stab ρ (⨆ k, F k) := by
  intro i v hv
  have hle : (⨆ k, F k) ≤ (⨆ k, F k).comap (ρ i : H →ₗ[ℂ] H) :=
    iSup_le fun k x hx => Submodule.mem_iSup_of_mem k (hF k i x hx)
  exact hle hv

theorem exists_hit (hρ : Good ρ) (hρ' : Good ρ') (hcomm : ∀ i j v, ρ i (ρ' j v) = ρ' j (ρ i v))
    {S X W : Submodule ℂ H} (hSρ' : Stab ρ' S)
    (hSirr : ∀ S' : Submodule ℂ H, S' ≤ S → Stab ρ S' → Stab ρ' S' → S' = ⊥ ∨ S' = S)
    (hXS : X ≤ S) (hXs : Stab ρ X) (hXi : Irr ρ X) {x₀ : H} (hx₀ : x₀ ∈ X) (h0 : x₀ ≠ 0)
    [FiniteDimensional ℂ W] (hWS : W ≤ S) (hW0 : W ≠ ⊥) (hWs : Stab ρ W) :
    ∃ c : H →ₗ[ℂ] H, Comm ρ c ∧ c x₀ ∈ W ∧ c x₀ ≠ 0 := by
  set P : H →ₗ[ℂ] H := (W.starProjection : H →ₗ[ℂ] H) with hP
  have hPc : Comm ρ P := proj_comm hρ hWs
  have hρ'c : ∀ j, Comm ρ (ρ' j : H →ₗ[ℂ] H) := fun j i v => (hcomm i j v).symm
  by_contra hne
  push_neg at hne
  have hzero : ∀ j, ∀ x ∈ X, P (ρ' j x) = 0 := by
    intro j
    have hcj : Comm ρ (P ∘ₗ (ρ' j : H →ₗ[ℂ] H)) := comm_comp hPc (hρ'c j)
    have hk : (P ∘ₗ (ρ' j : H →ₗ[ℂ] H)) x₀ = 0 := by
      refine hne _ hcj ?_
      simp only [LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe]
      exact (W.orthogonalProjection _).2
    exact kill hcj hXs hXi hx₀ h0 hk
  set T : Submodule ℂ H := ⨆ j, X.map (ρ' j : H →ₗ[ℂ] H) with hT
  have hTρ : Stab ρ T := stab_iSup fun j => stab_map (hρ'c j) hXs
  have hTρ' : Stab ρ' T := by
    intro j' v hv
    have hle : T ≤ T.comap (ρ' j' : H →ₗ[ℂ] H) := by
      refine iSup_le fun j => ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := hρ'.mul j' j
      show ρ' j' (ρ' j x) ∈ T
      rw [hk x]
      exact Submodule.mem_iSup_of_mem k ⟨x, hx, rfl⟩
    exact hle hv
  have hTS : T ≤ S := by
    refine iSup_le fun j => ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hSρ' j x (hXS hx)
  have hx₀T : x₀ ∈ T := by
    obtain ⟨o, ho⟩ := hρ'.one
    have hm : ρ' o x₀ ∈ T := Submodule.mem_iSup_of_mem o ⟨x₀, hx₀, rfl⟩
    rwa [ho] at hm
  rcases hSirr T hTS hTρ hTρ' with h | h
  · rw [h] at hx₀T
    exact h0 ((Submodule.mem_bot ℂ).1 hx₀T)
  · have hle : T ≤ LinearMap.ker P := by
      refine iSup_le fun j => ?_
      rintro _ ⟨x, hx, rfl⟩
      exact LinearMap.mem_ker.2 (hzero j x hx)
    apply hW0
    rw [eq_bot_iff]
    intro w hw
    have hwT : w ∈ T := by
      rw [h]
      exact hWS hw
    have h1 : P w = 0 := LinearMap.mem_ker.1 (hle hwT)
    have h2 : P w = w := by
      simp only [hP, ContinuousLinearMap.coe_coe]
      exact Submodule.starProjection_eq_self_iff.2 hw
    refine (Submodule.mem_bot ℂ).2 ?_
    rw [← h2]
    exact h1

theorem schur2 (hρ : Good ρ) {X W : Submodule ℂ H} [FiniteDimensional ℂ X] [FiniteDimensional ℂ W]
    (hXs : Stab ρ X) (hXi : Irr ρ X) (hWs : Stab ρ W) (hWi : Irr ρ W) {x₀ : H} (hx₀ : x₀ ∈ X)
    (h0 : x₀ ≠ 0) {c c' : H →ₗ[ℂ] H} (hc : Comm ρ c) (hc' : Comm ρ c') (hcW : c x₀ ∈ W)
    (hc0 : c x₀ ≠ 0) (hc'W : c' x₀ ∈ W) :
    finrank ℂ X = finrank ℂ W ∧ ∃ μ : ℂ, c' x₀ = μ • c x₀ := by
  have hAW : ∀ x : X, c x ∈ W := fun x => into hρ hc hWs hXs hXi hx₀ h0 hcW x x.2
  have hBW : ∀ x : X, c' x ∈ W := fun x => into hρ hc' hWs hXs hXi hx₀ h0 hc'W x x.2
  have hinj : Function.Injective (c.domRestrict X) := by
    intro a b hab
    by_contra hne
    rw [LinearMap.domRestrict_apply, LinearMap.domRestrict_apply] at hab
    have hab' : c ((a : H) - b) = 0 := by rw [map_sub, hab, sub_self]
    have hne' : (a : H) - b ≠ 0 := fun h => hne (Subtype.ext (sub_eq_zero.1 h))
    exact hc0 (kill hc hXs hXi (X.sub_mem a.2 b.2) hne' hab' x₀ hx₀)
  have hmapW : X.map c = W := by
    rcases hWi _ (by rintro _ ⟨x, hx, rfl⟩; exact hAW ⟨x, hx⟩) (stab_map hc hXs) with h | h
    · exfalso
      have hm : c x₀ ∈ X.map c := ⟨x₀, hx₀, rfl⟩
      rw [h] at hm
      exact hc0 ((Submodule.mem_bot ℂ).1 hm)
    · exact h
  have hrank : finrank ℂ X = finrank ℂ W := by
    rw [← hmapW, ← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]
  refine ⟨hrank, ?_⟩
  let A : X →ₗ[ℂ] W := (c.domRestrict X).codRestrict W hAW
  let B : X →ₗ[ℂ] W := (c'.domRestrict X).codRestrict W hBW
  have hAinj : Function.Injective A := fun a b hab => hinj (congrArg Subtype.val hab)
  have hAsurj : Function.Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).1 hAinj
  let e : X ≃ₗ[ℂ] W := LinearEquiv.ofBijective A ⟨hAinj, hAsurj⟩
  let T : Module.End ℂ X := e.symm.toLinearMap ∘ₗ B
  haveI : Nontrivial X := ⟨⟨⟨x₀, hx₀⟩, 0, fun h => h0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue T
  obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
  have hTv : T v = μ • v := hv.apply_eq_smul
  have hBv : B v = μ • A v :=
    calc B v = e (T v) := (e.apply_symm_apply (B v)).symm
      _ = e (μ • v) := by rw [hTv]
      _ = μ • e v := map_smul e μ v
      _ = μ • A v := rfl
  have hcv : c' v = μ • c v := congrArg Subtype.val hBv
  have hd : Comm ρ (c' - μ • c) := (commSub ρ).sub_mem hc' ((commSub ρ).smul_mem μ hc)
  have hdv : (c' - μ • c) v = 0 := by
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, hcv, sub_self]
  have hv0 : (v : H) ≠ 0 := fun h => hv.2 (Subtype.ext h)
  have hfin := kill hd hXs hXi v.2 hv0 hdv x₀ hx₀
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero] at hfin
  exact ⟨μ, hfin⟩

end PI.WeylForKWork.DimensionInduction
end
end

noncomputable section

namespace PI.WeylForKWork.DimensionInduction

open scoped InnerProductSpace
open Module

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι κ : Type*} {ρ : ι → H →L[ℂ] H} {ρ' : κ → H →L[ℂ] H}

theorem count (hρ : Good ρ) (hρ' : Good ρ') (hcomm : ∀ i j v, ρ i (ρ' j v) = ρ' j (ρ i v))
    {S X : Submodule ℂ H} [FiniteDimensional ℂ S] (hSρ' : Stab ρ' S)
    (hSirr : ∀ S' : Submodule ℂ H, S' ≤ S → Stab ρ S' → Stab ρ' S' → S' = ⊥ ∨ S' = S)
    (hXS : X ≤ S) (hXs : Stab ρ X) (hXi : Irr ρ X) {x₀ : H} (hx₀ : x₀ ∈ X) (h0 : x₀ ≠ 0) :
    ∀ n, ∀ W : Submodule ℂ H, W ≤ S → Stab ρ W → finrank ℂ W = n →
      finrank ℂ W = finrank ℂ X * finrank ℂ ↥(slice ρ x₀ ⊓ W) := by
  haveI : FiniteDimensional ℂ X := Submodule.finiteDimensional_of_le hXS
  intro n
  refine Nat.strong_induction_on n fun n ih => ?_
  intro W hWS hWs hWn
  haveI : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWS
  by_cases hW0 : W = ⊥
  · subst hW0
    simp
  obtain ⟨c, hc, hcW, hc0⟩ := exists_hit hρ hρ' hcomm hSρ' hSirr hXS hXs hXi hx₀ h0 hWS hW0 hWs
  have hcX : ∀ x ∈ X, c x ∈ W := into hρ hc hWs hXs hXi hx₀ h0 hcW
  have hYW : X.map c ≤ W := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcX x hx
  have hYs : Stab ρ (X.map c) := stab_map hc hXs
  haveI : FiniteDimensional ℂ (X.map c) := Submodule.finiteDimensional_of_le hYW
  have hinj : Function.Injective (c.domRestrict X) := by
    intro a b hab
    by_contra hne
    rw [LinearMap.domRestrict_apply, LinearMap.domRestrict_apply] at hab
    have hab' : c ((a : H) - b) = 0 := by rw [map_sub, hab, sub_self]
    have hne' : (a : H) - b ≠ 0 := fun h => hne (Subtype.ext (sub_eq_zero.1 h))
    exact hc0 (kill hc hXs hXi (X.sub_mem a.2 b.2) hne' hab' x₀ hx₀)
  have hYrank : finrank ℂ (X.map c) = finrank ℂ X := by
    rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj]
  have hYi : Irr ρ (X.map c) := by
    intro Y' hY'Y hY's
    have hst : Stab ρ (X ⊓ Y'.comap c) := stab_inf hXs (fun i v hv => by
      show c (ρ i v) ∈ Y'
      rw [hc i v]
      exact hY's i _ hv)
    rcases hXi _ inf_le_left hst with h | h
    · left
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hY'Y hy
      have hm : x ∈ X ⊓ Y'.comap c := ⟨hx, hy⟩
      rw [h] at hm
      rw [(Submodule.mem_bot ℂ).1 hm, map_zero]
      exact Submodule.zero_mem _
    · right
      apply le_antisymm hY'Y
      rintro _ ⟨x, hx, rfl⟩
      have hm : x ∈ X ⊓ Y'.comap c := by
        rw [h]
        exact hx
      exact hm.2
  have hYpos : 0 < finrank ℂ (X.map c) :=
    finrank_pos_iff_exists_ne_zero.2 ⟨⟨c x₀, x₀, hx₀, rfl⟩, fun h => hc0 (congrArg Subtype.val h)⟩
  have hW's : Stab ρ ((X.map c)ᗮ ⊓ W) := stab_inf (stab_orth hρ hYs) hWs
  have hW'S : (X.map c)ᗮ ⊓ W ≤ S := inf_le_right.trans hWS
  have hsum := Submodule.finrank_add_inf_finrank_orthogonal hYW
  have hsl : slice ρ x₀ ⊓ W = (ℂ ∙ c x₀) ⊔ (slice ρ x₀ ⊓ ((X.map c)ᗮ ⊓ W)) := by
    apply le_antisymm
    · rintro z ⟨⟨d, hd, rfl⟩, hzW⟩
      set P : H →ₗ[ℂ] H := ((X.map c).starProjection : H →ₗ[ℂ] H) with hP
      have hPd : Comm ρ (P ∘ₗ d) := comm_comp (proj_comm hρ hYs) hd
      have hPdY : (P ∘ₗ d) x₀ ∈ X.map c := by
        simp only [LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe]
        exact ((X.map c).orthogonalProjection _).2
      obtain ⟨μ, hμ⟩ := (schur2 hρ hXs hXi hYs hYi hx₀ h0 hc hPd ⟨x₀, hx₀, rfl⟩ hc0 hPdY).2
      refine Submodule.mem_sup.2 ⟨μ • c x₀, Submodule.smul_mem _ μ (Submodule.mem_span_singleton_self _),
        d x₀ - μ • c x₀, ⟨?_, ?_, ?_⟩, by abel⟩
      · exact ⟨d - μ • c, (commSub ρ).sub_mem hd ((commSub ρ).smul_mem μ hc), rfl⟩
      · rw [← hμ]
        simp only [LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe]
        exact (X.map c).sub_starProjection_mem_orthogonal _
      · exact W.sub_mem hzW (W.smul_mem μ hcW)
    · refine sup_le ?_ (inf_le_inf_left _ inf_le_right)
      exact (Submodule.span_singleton_le_iff_mem _ _).2 ⟨⟨c, hc, rfl⟩, hcW⟩
  have hdisj : (ℂ ∙ c x₀) ⊓ (slice ρ x₀ ⊓ ((X.map c)ᗮ ⊓ W)) = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hz1, -, hz2, -⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz1
    have hin := (Submodule.mem_orthogonal _ _).1 hz2 (c x₀) ⟨x₀, hx₀, rfl⟩
    rw [inner_smul_right] at hin
    rcases mul_eq_zero.1 hin with ha | ha
    · rw [ha, zero_smul]
      exact Submodule.zero_mem _
    · exact absurd (inner_self_eq_zero.1 ha) hc0
  have hrk1 : finrank ℂ (ℂ ∙ c x₀) = 1 := finrank_span_singleton hc0
  haveI : FiniteDimensional ℂ ↥(slice ρ x₀ ⊓ ((X.map c)ᗮ ⊓ W)) :=
    Submodule.finiteDimensional_of_le (inf_le_right.trans inf_le_right)
  have hsup := Submodule.finrank_sup_add_finrank_inf_eq (ℂ ∙ c x₀) (slice ρ x₀ ⊓ ((X.map c)ᗮ ⊓ W))
  rw [hdisj, finrank_bot, add_zero, ← hsl, hrk1] at hsup
  have hih := ih (finrank ℂ ↥((X.map c)ᗮ ⊓ W)) (by omega) _ hW'S hW's rfl
  rw [hsup, ← hsum, hYrank, hih]
  ring

theorem main (hρ : Good ρ) (hρ' : Good ρ') (hcomm : ∀ i j v, ρ i (ρ' j v) = ρ' j (ρ i v))
    {S X Y : Submodule ℂ H} [FiniteDimensional ℂ S] (hSρ : Stab ρ S) (hSρ' : Stab ρ' S)
    (hSirr : ∀ S' : Submodule ℂ H, S' ≤ S → Stab ρ S' → Stab ρ' S' → S' = ⊥ ∨ S' = S)
    (hXS : X ≤ S) (hX0 : X ≠ ⊥) (hXs : Stab ρ X) (hXi : Irr ρ X)
    (hYS : Y ≤ S) (hY0 : Y ≠ ⊥) (hYs : Stab ρ' Y) (hYi : Irr ρ' Y) :
    finrank ℂ S = finrank ℂ X * finrank ℂ Y := by
  haveI : FiniteDimensional ℂ X := Submodule.finiteDimensional_of_le hXS
  haveI : FiniteDimensional ℂ Y := Submodule.finiteDimensional_of_le hYS
  obtain ⟨x₀, hx₀, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX0
  obtain ⟨y₀, hy₀, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY0
  have hc1 := count hρ hρ' hcomm hSρ' hSirr hXS hXs hXi hx₀ h0 (finrank ℂ S) S le_rfl hSρ rfl
  rw [hc1]
  congr 1
  set U := slice ρ x₀ ⊓ S with hUdef
  have hUS : U ≤ S := inf_le_right
  haveI : FiniteDimensional ℂ U := Submodule.finiteDimensional_of_le hUS
  have hρ'c : ∀ j, Comm ρ (ρ' j : H →ₗ[ℂ] H) := fun j i v => (hcomm i j v).symm
  have hUs : Stab ρ' U := by
    rintro j _ ⟨⟨d, hd, rfl⟩, hS'⟩
    exact ⟨⟨(ρ' j : H →ₗ[ℂ] H) ∘ₗ d, comm_comp (hρ'c j) hd, rfl⟩, hSρ' j _ hS'⟩
  have hx₀U : x₀ ∈ U := ⟨⟨LinearMap.id, fun i v => rfl, rfl⟩, hXS hx₀⟩
  have hU0 : U ≠ ⊥ := by
    intro h
    rw [h] at hx₀U
    exact h0 ((Submodule.mem_bot ℂ).1 hx₀U)
  have hUi : Irr ρ' U := by
    intro U' hU'U hU's
    by_contra hne
    push_neg at hne
    obtain ⟨hU'0, hU'ne⟩ := hne
    have hU''le : U'ᗮ ⊓ U ≤ U := inf_le_right
    have hU''0 : U'ᗮ ⊓ U ≠ ⊥ := by
      intro h
      have hfr := Submodule.finrank_add_inf_finrank_orthogonal hU'U
      rw [h, finrank_bot, add_zero] at hfr
      exact hU'ne (Submodule.eq_of_le_of_finrank_eq hU'U hfr)
    obtain ⟨w, hwU'', hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU''0
    have hwS : w ∈ S := hUS (hU''le hwU'')
    have hTρ : Stab ρ (⨆ i, U'.map (ρ i : H →ₗ[ℂ] H)) := by
      intro i v hv
      have hle : (⨆ k, U'.map (ρ k : H →ₗ[ℂ] H)) ≤
          (⨆ k, U'.map (ρ k : H →ₗ[ℂ] H)).comap (ρ i : H →ₗ[ℂ] H) := by
        refine iSup_le fun k => ?_
        rintro _ ⟨z, hz, rfl⟩
        obtain ⟨m, hm⟩ := hρ.mul i k
        show ρ i (ρ k z) ∈ ⨆ k, U'.map (ρ k : H →ₗ[ℂ] H)
        rw [hm z]
        exact Submodule.mem_iSup_of_mem m ⟨z, hz, rfl⟩
      exact hle hv
    have hTρ' : Stab ρ' (⨆ i, U'.map (ρ i : H →ₗ[ℂ] H)) :=
      stab_iSup fun k => stab_map (fun j v => hcomm k j v) hU's
    have hTS : (⨆ i, U'.map (ρ i : H →ₗ[ℂ] H)) ≤ S := by
      refine iSup_le fun k => ?_
      rintro _ ⟨z, hz, rfl⟩
      exact hSρ k z (hUS (hU'U hz))
    have hT0 : (⨆ i, U'.map (ρ i : H →ₗ[ℂ] H)) ≠ ⊥ := by
      obtain ⟨u, huU', hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU'0
      obtain ⟨o, ho⟩ := hρ.one
      intro h
      have hm : ρ o u ∈ ⨆ i, U'.map (ρ i : H →ₗ[ℂ] H) := Submodule.mem_iSup_of_mem o ⟨u, huU', rfl⟩
      rw [h, ho] at hm
      exact hu0 ((Submodule.mem_bot ℂ).1 hm)
    have hTeq := (hSirr _ hTS hTρ hTρ').resolve_left hT0
    have key : ∀ k, ∀ z ∈ U', ⟪w, ρ k z⟫_ℂ = 0 := by
      intro k z hz
      obtain ⟨⟨d', hd', rfl⟩, -⟩ := hU'U hz
      by_cases hd0 : d' x₀ = 0
      · rw [hd0, map_zero, inner_zero_right]
      obtain ⟨⟨d'', hd'', hw_eq⟩, -⟩ := hU''le hwU''
      have hKs : Stab ρ (X.map d') := stab_map hd' hXs
      have hKi : Irr ρ (X.map d') := by
        intro Y' hY'Y hY's
        have hst : Stab ρ (X ⊓ Y'.comap d') := stab_inf hXs (fun i v hv => by
          show d' (ρ i v) ∈ Y'
          rw [hd' i v]
          exact hY's i _ hv)
        rcases hXi _ inf_le_left hst with h | h
        · left
          rw [eq_bot_iff]
          intro y hy
          obtain ⟨x, hx, rfl⟩ := hY'Y hy
          have hm : x ∈ X ⊓ Y'.comap d' := ⟨hx, hy⟩
          rw [h] at hm
          rw [(Submodule.mem_bot ℂ).1 hm, map_zero]
          exact Submodule.zero_mem _
        · right
          apply le_antisymm hY'Y
          rintro _ ⟨x, hx, rfl⟩
          have hm : x ∈ X ⊓ Y'.comap d' := by
            rw [h]
            exact hx
          exact hm.2
      set P : H →ₗ[ℂ] H := ((X.map d').starProjection : H →ₗ[ℂ] H) with hP
      have hPd : Comm ρ (P ∘ₗ d'') := comm_comp (proj_comm hρ hKs) hd''
      have hPdK : (P ∘ₗ d'') x₀ ∈ X.map d' := by
        simp only [LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe]
        exact ((X.map d').orthogonalProjection _).2
      obtain ⟨μ, hμ⟩ := (schur2 hρ hXs hXi hKs hKi hx₀ h0 hd' hPd ⟨x₀, hx₀, rfl⟩ hd0 hPdK).2
      have hPw : (X.map d').starProjection w = μ • d' x₀ := by
        rw [← hw_eq]
        simpa only [LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe] using hμ
      have horth : ⟪d' x₀, w⟫_ℂ = 0 := (Submodule.mem_orthogonal _ _).1 hwU''.1 _ hz
      have h1 : ⟪d' x₀, w - (X.map d').starProjection w⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal _ _).1 ((X.map d').sub_starProjection_mem_orthogonal w) _
          ⟨x₀, hx₀, rfl⟩
      rw [inner_sub_right, horth, hPw, inner_smul_right, zero_sub, neg_eq_zero] at h1
      have hμ0 : μ = 0 := by
        rcases mul_eq_zero.1 h1 with h | h
        · exact h
        · exact absurd (inner_self_eq_zero.1 h) hd0
      rw [hμ0, zero_smul] at hPw
      rw [← hd' k x₀]
      have hmemK : d' (ρ k x₀) ∈ X.map d' := ⟨ρ k x₀, hXs k x₀ hx₀, rfl⟩
      have h2 : ⟪d' (ρ k x₀), w - (X.map d').starProjection w⟫_ℂ = 0 :=
        (Submodule.mem_orthogonal _ _).1 ((X.map d').sub_starProjection_mem_orthogonal w) _ hmemK
      rw [hPw, sub_zero] at h2
      exact inner_eq_zero_symm.1 h2
    have hle : (⨆ i, U'.map (ρ i : H →ₗ[ℂ] H)) ≤ (ℂ ∙ w)ᗮ := by
      refine iSup_le fun k => ?_
      rintro _ ⟨z, hz, rfl⟩
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      exact key k z hz
    rw [hTeq] at hle
    have hww := Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hwS)
    exact hw0 (inner_self_eq_zero.1 hww)
  have hcomm' : ∀ j i v, ρ' j (ρ i v) = ρ i (ρ' j v) := fun j i v => (hcomm i j v).symm
  have hSirr' : ∀ S' : Submodule ℂ H, S' ≤ S → Stab ρ' S' → Stab ρ S' → S' = ⊥ ∨ S' = S :=
    fun S' h1 h2 h3 => hSirr S' h1 h3 h2
  obtain ⟨e, he, heU, he0⟩ := exists_hit hρ' hρ hcomm' hSρ hSirr' hYS hYs hYi hy₀ hy0 hUS hU0 hUs
  exact (schur2 hρ' hYs hYi hUs hUi hy₀ hy0 he he heU he0 heU).1.symm

end PI.WeylForKWork.DimensionInduction
end
end

noncomputable section

namespace PI.WeylForKWork

open PI PI.UpqRep Matrix DimensionInduction

lemma dimStep_one_mem {n : ℕ} (ε : Fin n → Bool) : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ Kset ε :=
  ⟨Submonoid.one_mem _, by rw [Matrix.one_mul, Matrix.mul_one]⟩

lemma dimStep_good {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (Kset (allPos n)) σ) :
    Good (fun g : Kset (allPos n) => σ g.1) := by
  refine ⟨fun g v => hσ.2.1 g.1 g.2 v, ?_, ?_, ?_⟩
  · intro g
    refine ⟨⟨star g.1, Kset_star _ g.2⟩, fun v => ?_⟩
    show σ g.1 (σ (star g.1) v) = v
    rw [← ContinuousLinearMap.comp_apply, ← hσ.1.2 _ g.2 _ (Kset_star _ g.2),
      Unitary.mul_star_self_of_mem g.2.1, hσ.1.1]
    rfl
  · intro g g'
    refine ⟨⟨g.1 * g'.1, Kset_mul _ g.2 g'.2⟩, fun v => ?_⟩
    show σ g.1 (σ g'.1 v) = σ (g.1 * g'.1) v
    rw [hσ.1.2 _ g.2 _ g'.2]
    rfl
  · refine ⟨⟨1, dimStep_one_mem _⟩, fun v => ?_⟩
    show σ 1 v = v
    rw [hσ.1.1]
    rfl

lemma dimStep_stab {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {W : Submodule ℂ H} :
    IsKStableOn (allPos n) σ W ↔ Stab (fun g : Kset (allPos n) => σ g.1) W :=
  ⟨fun h g v hv => h g.1 g.2 v hv, fun h g hg v hv => h ⟨g, hg⟩ v hv⟩

theorem dimension_induction_holds : DimStep := by
  intro p q H _ _ σ₁ σ₂ S X Y h1 h2 hcomm hS hS1 hS2 hSirr hXS hX0 hX1 hXi hYS hY0 hY2 hYi
  exact main (dimStep_good h1) (dimStep_good h2)
    (fun g g' v => by
      show σ₁ g.1 (σ₂ g'.1 v) = σ₂ g'.1 (σ₁ g.1 v)
      rw [← ContinuousLinearMap.comp_apply, hcomm _ g.2 _ g'.2]
      rfl)
    (dimStep_stab.1 hS1) (dimStep_stab.1 hS2)
    (fun S' h s1 s2 => hSirr S' h (dimStep_stab.2 s1) (dimStep_stab.2 s2))
    hXS hX0 (dimStep_stab.1 hX1) (fun X' h s => hXi X' h (dimStep_stab.2 s))
    hYS hY0 (dimStep_stab.1 hY2) (fun Y' h s => hYi Y' h (dimStep_stab.2 s))

end PI.WeylForKWork
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.Weights
noncomputable section

namespace PI.WeylForKWork

open PI PI.UpqRep Matrix
open scoped InnerProductSpace

def wtTorus {N : ℕ} (θ : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)

theorem wt_char_real (f : ℝ → ℂ) (hc : Continuous f) (hm : ∀ s t, f (s + t) = f s * f t)
    (h0 : f 0 = 1) (hn : ∀ t, ‖f t‖ = 1) :
    ∃ m : ℝ, ∀ t, f t = Complex.exp (((m * t : ℝ) : ℂ) * Complex.I) := by
  first | exact Bl.general_b_fact_left_variant.goal1 .. | (apply Bl.general_b_fact_left_variant.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_variant.goal1 <;> assumption)

theorem wt_common_eigvec {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ι : Type}
    (A : ι → (H →L[ℂ] H)) (W : Submodule ℂ H) [FiniteDimensional ℂ W] (hW : W ≠ ⊥)
    (hst : ∀ i, ∀ v ∈ W, A i v ∈ W) (hcomm : ∀ i j, ∀ v, A i (A j v) = A j (A i v)) :
    ∃ w ∈ W, w ≠ 0 ∧ ∀ i, ∃ c : ℂ, A i w = c • w := by
  classical
  have hex : ∃ n, ∃ W₀ : Submodule ℂ H, W₀ ≤ W ∧ W₀ ≠ ⊥ ∧ (∀ i, ∀ v ∈ W₀, A i v ∈ W₀) ∧
      Module.finrank ℂ W₀ = n := ⟨_, W, le_rfl, hW, hst, rfl⟩
  obtain ⟨W₀, hW₀W, hW₀, hW₀st, hW₀n⟩ := Nat.find_spec hex
  have hmin : ∀ W₁ : Submodule ℂ H, W₁ ≤ W → W₁ ≠ ⊥ → (∀ i, ∀ v ∈ W₁, A i v ∈ W₁) →
      Module.finrank ℂ W₀ ≤ Module.finrank ℂ W₁ := fun W₁ h1 h2 h3 => by
    rw [hW₀n]; exact Nat.find_min' hex ⟨W₁, h1, h2, h3, rfl⟩
  have : FiniteDimensional ℂ W₀ := Submodule.finiteDimensional_of_le hW₀W
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W₀).mp hW₀
  refine ⟨w, hW₀W hw, hw0, fun i => ?_⟩
  let f : Module.End ℂ W₀ := (A i : H →ₗ[ℂ] H).restrict (fun x hx => hW₀st i x hx)
  have : Nontrivial W₀ := Submodule.nontrivial_iff_ne_bot.mpr hW₀
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  let E : Submodule ℂ H := W₀ ⊓ LinearMap.ker ((A i : H →ₗ[ℂ] H) - c • LinearMap.id)
  have hmemE : ∀ x, x ∈ E ↔ x ∈ W₀ ∧ A i x = c • x := by
    intro x; simp [E, sub_eq_zero]
  have hEst : ∀ j, ∀ x ∈ E, A j x ∈ E := by
    intro j x hx
    rw [hmemE] at hx ⊢
    exact ⟨hW₀st j x hx.1, by rw [hcomm i j, hx.2, map_smul]⟩
  have hvE : (v : H) ∈ E := by
    rw [hmemE]
    refine ⟨v.2, ?_⟩
    have h1 := Module.End.mem_eigenspace_iff.mp hv.1
    have h2 := congrArg Subtype.val h1
    simpa [f] using h2
  have hE0 : E ≠ ⊥ := by
    rw [Submodule.ne_bot_iff]
    refine ⟨v, hvE, fun h => hv.2 ?_⟩
    exact Subtype.ext h
  have hEW : E ≤ W₀ := inf_le_left
  have hEeq : E = W₀ := Submodule.eq_of_le_of_finrank_le hEW (hmin E (hEW.trans hW₀W) hE0 hEst)
  have hwE : w ∈ E := hEeq ▸ hw
  exact ⟨c, ((hmemE w).mp hwE).2⟩

theorem wt_inner_iso {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (T : H →L[ℂ] H)
    (hT : ∀ v, ‖T v‖ = ‖v‖) (x y : H) : ⟪T x, T y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (⟨(T : H →ₗ[ℂ] H), hT⟩ : H →ₗᵢ[ℂ] H).inner_map_map x y

theorem wt_perp_stable {N : ℕ} (ε : Fin N → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (hσ : IsURepOn (Kset ε) σ) (X' X : Submodule ℂ H)
    (hX' : IsKStableOn ε σ X') (hX : IsKStableOn ε σ X) : IsKStableOn ε σ (X'ᗮ ⊓ X) := by
  intro g hg v hv
  refine ⟨?_, hX g hg v hv.2⟩
  show σ g v ∈ X'ᗮ
  rw [Submodule.mem_orthogonal]
  intro u hu
  have hg' : star g ∈ Kset ε := Kset_star ε hg
  have h1 : ⟪σ (star g) u, v⟫_ℂ = 0 := (Submodule.mem_orthogonal X' v).mp hv.1 _ (hX' _ hg' u hu)
  have h2 : σ g (σ (star g) u) = u := by
    have h3 := hσ.1.2 g hg (star g) hg'
    rw [Unitary.mul_star_self_of_mem hg.1, hσ.1.1] at h3
    have h4 := DFunLike.congr_fun h3 u
    simpa using h4.symm
  calc ⟪u, σ g v⟫_ℂ = ⟪σ g (σ (star g) u), σ g v⟫_ℂ := by rw [h2]
    _ = ⟪σ (star g) u, v⟫_ℂ := wt_inner_iso (σ g) (hσ.2.1 g hg) _ _
    _ = 0 := h1

theorem false_of_neg_smul_eq_smul {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (z : ℂ) (hz : z ≠ 0)
    (w : H) (hw : w ≠ 0) (h : (z * -1) • w = z • w) : False := by
  have e3 := sub_eq_zero.mpr h
  rw [← sub_smul, smul_eq_zero] at e3
  rcases e3 with h' | h'
  · apply hz; linear_combination (-1/2 : ℂ) * h'
  · exact hw h'

theorem weight_unique_holds : WtUniq := by
  intro n H _ _ σ μ μ' w hw h1 h2
  funext a
  by_contra hne
  have hd : μ a - μ' a ≠ 0 := sub_ne_zero.mpr hne
  have hT := PI.WeylForKInhab.diag_mem (allPos n) (Pi.single a (Real.pi / (μ a - μ' a)))
  have e1 := h1 _ hT
  have e2 := h2 _ hT
  rw [e1] at e2
  have s : ∀ ν : Fin n → ℝ, ∑ b, ν b * (Pi.single a (Real.pi / (μ a - μ' a)) : Fin n → ℝ) b =
      ν a * (Real.pi / (μ a - μ' a)) := by
    intro ν
    rw [Finset.sum_eq_single a]
    · rw [Pi.single_eq_same]
    · intro b _ hb; rw [Pi.single_eq_of_ne hb]; ring
    · intro hh; exact absurd (Finset.mem_univ a) hh
  rw [s, s] at e2
  have hc : (μ a - μ' a) * (Real.pi / (μ a - μ' a)) = Real.pi := mul_div_cancel₀ _ hd
  have hxy : μ a * (Real.pi / (μ a - μ' a)) = μ' a * (Real.pi / (μ a - μ' a)) + Real.pi := by
    linear_combination hc
  rw [hxy, Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I] at e2
  exact false_of_neg_smul_eq_smul _ (Complex.exp_ne_zero _) w hw e2

theorem torus_weight_exists : TorusWt := by
  intro N ε H _ _ σ W hσ hWf hW0 hWst
  have := hWf
  have hTK : ∀ θ : Fin N → ℝ, wtTorus θ ∈ Kset ε := fun θ => PI.WeylForKInhab.diag_mem ε θ
  have hTadd : ∀ θ θ' : Fin N → ℝ, wtTorus (θ + θ') = wtTorus θ * wtTorus θ' := by
    intro θ θ'
    simp only [wtTorus, diagonal_mul_diagonal]
    congr 1; funext a
    simp [add_mul, Complex.exp_add]
  have hσadd : ∀ θ θ' : Fin N → ℝ, ∀ v, σ (wtTorus (θ + θ')) v = σ (wtTorus θ) (σ (wtTorus θ') v) := by
    intro θ θ' v; rw [hTadd, hσ.1.2 _ (hTK θ) _ (hTK θ')]; rfl
  have hcomm : ∀ θ θ' : Fin N → ℝ, ∀ v, σ (wtTorus θ) (σ (wtTorus θ') v) = σ (wtTorus θ') (σ (wtTorus θ) v) := by
    intro θ θ' v; rw [← hσadd, ← hσadd, add_comm]
  obtain ⟨w, hwW, hw0, hwe⟩ := wt_common_eigvec (fun θ => σ (wtTorus θ)) W hW0 (fun θ v hv => hWst θ v hv) hcomm
  choose χ hχ using hwe
  have hχ' : ∀ θ, σ (wtTorus θ) w = χ θ • w := hχ
  have hinner : ⟪w, w⟫_ℂ ≠ 0 := inner_self_ne_zero.mpr hw0
  have hχeq : ∀ θ, χ θ = ⟪w, σ (wtTorus θ) w⟫_ℂ / ⟪w, w⟫_ℂ := by
    intro θ
    rw [hχ' θ, inner_smul_right, mul_div_assoc, div_self hinner, mul_one]
  have hTc : Continuous (fun θ : Fin N → ℝ => wtTorus θ) := by
    unfold wtTorus
    apply Continuous.matrix_diagonal
    exact continuous_pi fun a => by fun_prop
  have hχc : Continuous χ := by
    have h1 : Continuous (fun θ => σ (wtTorus θ) w) := (hσ.2.2 w).comp_continuous hTc hTK
    have : χ = fun θ => ⟪w, σ (wtTorus θ) w⟫_ℂ / ⟪w, w⟫_ℂ := funext hχeq
    rw [this]; exact (continuous_const.inner h1).div_const _
  have hsm : ∀ c d : ℂ, c • w = d • w → c = d := fun c d h => smul_left_injective ℂ hw0 h
  have hχadd : ∀ θ θ', χ (θ + θ') = χ θ * χ θ' := by
    intro θ θ'; apply hsm
    rw [← hχ', hσadd, hχ' θ', map_smul, hχ' θ, smul_smul, mul_comm]
  have hχ0 : χ 0 = 1 := by
    apply hsm
    rw [← hχ', one_smul]
    have : wtTorus (0 : Fin N → ℝ) = 1 := by simp [wtTorus]
    rw [this, hσ.1.1]; rfl
  have hχn : ∀ θ, ‖χ θ‖ = 1 := by
    intro θ
    have h := hσ.2.1 _ (hTK θ) w
    rw [hχ' θ, norm_smul] at h
    have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have h2 : (‖χ θ‖ - 1) * ‖w‖ = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · linarith
  have hcoord : ∀ a : Fin N, ∃ m : ℝ, ∀ t,
      χ (Pi.single a t) = Complex.exp (((m * t : ℝ) : ℂ) * Complex.I) := by
    intro a
    apply wt_char_real (fun t => χ (Pi.single a t))
    · exact hχc.comp ((LinearMap.single ℝ (fun _ : Fin N => ℝ) a).continuous_of_finiteDimensional)
    · intro s t; simp only [Pi.single_add]; exact hχadd _ _
    · simpa using hχ0
    · intro t; exact hχn _
  choose m hm using hcoord
  refine ⟨m, w, hwW, hw0, fun θ _ => ?_⟩
  show σ (wtTorus θ) w = _
  rw [hχ' θ]
  congr 1
  have hprod : ∀ s : Finset (Fin N),
      χ (∑ a ∈ s, Pi.single a (θ a)) = ∏ a ∈ s, χ (Pi.single a (θ a)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [hχ0]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, hχadd, ih]
  calc χ θ = χ (∑ a, Pi.single a (θ a)) := by rw [Finset.univ_sum_single]
    _ = ∏ a, χ (Pi.single a (θ a)) := hprod _
    _ = ∏ a, Complex.exp (((m a * θ a : ℝ) : ℂ) * Complex.I) :=
        Finset.prod_congr rfl fun a _ => hm a (θ a)
    _ = Complex.exp (((∑ a, m a * θ a : ℝ) : ℂ) * Complex.I) := by
        rw [← Complex.exp_sum]; congr 1; push_cast; rw [Finset.sum_mul]

theorem minimal_irreducible_exists : MinIrr := by
  classical
  intro p H _ _ σ₁ S μ v hσ hS hSst hvS hv0 hvw
  have hex : ∃ n, ∃ X : Submodule ℂ H, X ≤ S ∧ IsKStableOn (allPos p) σ₁ X ∧
      (∃ x ∈ X, x ≠ 0 ∧ IsWtOn (Kset (allPos p)) σ₁ μ x) ∧ Module.finrank ℂ X = n :=
    ⟨_, S, le_rfl, hSst, ⟨v, hvS, hv0, hvw⟩, rfl⟩
  obtain ⟨X, hXS, hXst, ⟨x, hxX, hx0, hxw⟩, hXn⟩ := Nat.find_spec hex
  have hmin : ∀ X₁ : Submodule ℂ H, X₁ ≤ S → IsKStableOn (allPos p) σ₁ X₁ →
      (∃ x ∈ X₁, x ≠ 0 ∧ IsWtOn (Kset (allPos p)) σ₁ μ x) →
      Module.finrank ℂ X ≤ Module.finrank ℂ X₁ := fun X₁ h1 h2 h3 => by
    rw [hXn]; exact Nat.find_min' hex ⟨X₁, h1, h2, h3, rfl⟩
  have : FiniteDimensional ℂ X := Submodule.finiteDimensional_of_le hXS
  refine ⟨X, hXS, hXst, ?_, x, hxX, hx0, hxw⟩
  intro X' hX'X hX'st
  have : FiniteDimensional ℂ X' := Submodule.finiteDimensional_of_le hX'X
  have : CompleteSpace X' := FiniteDimensional.complete ℂ X'
  have hX''st := wt_perp_stable (allPos p) σ₁ hσ X' X hX'st hXst
  have hxsup : x ∈ X' ⊔ X'ᗮ := by rw [Submodule.sup_orthogonal_of_hasOrthogonalProjection]; trivial
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hxsup
  have hzX : z ∈ X := by
    have : z = x - y := by rw [← hyz]; abel
    rw [this]; exact X.sub_mem hxX (hX'X hy)
  have hz'' : z ∈ X'ᗮ ⊓ X := ⟨hz, hzX⟩
  have hperp0 : ∀ u, u ∈ X' → u ∈ X'ᗮ → u = 0 := fun u h1 h2 =>
    inner_self_eq_zero.mp ((Submodule.mem_orthogonal X' u).mp h2 u h1)
  have hsplit : ∀ θ : Fin p → ℝ, diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset (allPos p) →
      σ₁ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) y =
        Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • y ∧
      σ₁ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) z =
        Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • z := by
    intro θ hT
    have hx := hxw θ hT
    have hAy := hX'st _ hT y hy
    have hAz := (hX''st _ hT z hz'').1
    set A := σ₁ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) with hA
    set e := Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) with he
    have hu1 : A y - e • y ∈ X' := X'.sub_mem hAy (X'.smul_mem e hy)
    have hu2 : A z - e • z ∈ X'ᗮ := X'ᗮ.sub_mem hAz (X'ᗮ.smul_mem e hz)
    have hsum : A y - e • y + (A z - e • z) = 0 := by
      rw [← hyz, map_add (f := _), smul_add] at hx
      rw [show A y - e • y + (A z - e • z) = (A y + A z) - (e • y + e • z) by abel, hx, sub_self]
    have hneg : A y - e • y = -(A z - e • z) := eq_neg_of_add_eq_zero_left hsum
    have h0y : A y - e • y = 0 := hperp0 _ hu1 (by rw [hneg]; exact X'ᗮ.neg_mem hu2)
    have h0z : A z - e • z = 0 := by rw [h0y] at hneg; exact neg_eq_zero.mp hneg.symm
    exact ⟨sub_eq_zero.mp h0y, sub_eq_zero.mp h0z⟩
  have hwy : IsWtOn (Kset (allPos p)) σ₁ μ y := fun θ hT => (hsplit θ hT).1
  have hwz : IsWtOn (Kset (allPos p)) σ₁ μ z := fun θ hT => (hsplit θ hT).2
  by_cases hy0 : y = 0
  · left
    have hzx : z = x := by rw [← hyz, hy0, zero_add]
    have hz0 : z ≠ 0 := by rw [hzx]; exact hx0
    have hle : X'ᗮ ⊓ X ≤ X := inf_le_right
    have heq : X'ᗮ ⊓ X = X := Submodule.eq_of_le_of_finrank_le hle
      (hmin _ (hle.trans hXS) hX''st ⟨z, hz'', hz0, hwz⟩)
    rw [Submodule.eq_bot_iff]
    intro u hu
    have hu' : u ∈ X'ᗮ ⊓ X := by rw [heq]; exact hX'X hu
    exact hperp0 u hu hu'.1
  · right
    exact Submodule.eq_of_le_of_finrank_le hX'X (hmin X' (hX'X.trans hXS) hX'st ⟨y, hy, hy0, hwy⟩)

end PI.WeylForKWork
end
end

theorem weylForK_of : PI.WeylForU → PI.WeylForK :=
  PI.WeylForKWork.weylForK_of_leaves PI.WeylForKWork.block_reindex_holds PI.WeylForKWork.block_diagonal_torus_holds
    PI.WeylForKWork.torus_weight_exists PI.WeylForKWork.weight_unique_holds PI.WeylForKWork.minimal_irreducible_exists
    PI.WeylForKWork.dominant_restriction_holds PI.WeylForKWork.dimension_induction_holds PI.WeylForKWork.weyl_formula_compact
