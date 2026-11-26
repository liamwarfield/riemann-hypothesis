module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanExists
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBaseFlagComplementIntegralLattice

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DualEquivSymmApply
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExtensionIdentityOfMemCompl
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NondegenerateOnOrthCompl
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

def GenusMassW : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h →
    ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    ∀ T₀ : Submodule (𝓞 K) V, IsLatIn (orthK h U) T₀ → Formalism.HermitianLatticesTheory.IsIntegralLat h T₀ →
    ∀ c : ℝ, MassConst K F (finrank K (orthK h U)) c →
      ∃ s : Finset (Submodule (𝓞 K) V),
        (∀ T ∈ s, IsLatIn (orthK h U) T ∧ SameGenusFix (F := F) h U T₀ T) ∧
        (∀ T, IsLatIn (orthK h U) T → SameGenusFix (F := F) h U T₀ T →
          ∃! T₁, T₁ ∈ s ∧ ∃ g ∈ isomFix h U, Formalism.HermitianLatticesTheory.gmap g T₁ = T) ∧
        (∀ T, IsLatIn (orthK h U) T → SameGenusFix (F := F) h U T₀ T → (stabFix h U T).Finite) ∧
        ((∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, discAut h (orthK h U) T₀ 𝔭.1 : ℕ) : ℝ) *
            ∑ T ∈ s, ((Nat.card (stabFix h U T) : ℕ) : ℝ)⁻¹ =
          c * nM F h (orthK h U) T₀ ^ finrank K (orthK h U) *
            ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, alphaStd K 𝔭.1 (finrank K (orthK h U)) /
              alphaStd K 𝔭.1 (finrank K (orthK h U) - cJ h (orthK h U) T₀ 𝔭.1)

end Formalism.L2.SG.Pf.Cnt

namespace Formalism.L2.SG.Pf.G9

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

theorem tprod_nat_ne_zero {ι : Type*} (f : ι → ℕ) (hf : ∀ i, f i ≠ 0) : ∏' i, f i ≠ 0 := by
  by_cases hm : Multipliable f
  · have e := hm.hasProd.eventually_mem (IsOpen.mem_nhds (isOpen_discrete {∏' i, f i}) rfl)
    obtain ⟨s, hs⟩ := e.exists
    rw [← Set.mem_singleton_iff.mp hs]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hf i
  · rw [tprod_eq_one_of_not_multipliable hm]
    exact one_ne_zero

theorem sum_eq_of_min {n n' : ℕ} (e : Fin n → ℕ) (e' : Fin n' → ℕ)
    (H : ∀ j, ∑ i, min (e i) j = ∑ i, min (e' i) j) : ∑ i, e i = ∑ i, e' i := by
  have h1 : ∀ i, e i ≤ ∑ i, e i + ∑ i, e' i := fun i =>
    le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (Nat.le_add_right _ _)
  have h2 : ∀ i, e' i ≤ ∑ i, e i + ∑ i, e' i := fun i =>
    le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) (Nat.le_add_left _ _)
  calc ∑ i, e i = ∑ i, min (e i) (∑ i, e i + ∑ i, e' i) :=
        Finset.sum_congr rfl fun i _ => (min_eq_left (h1 i)).symm
    _ = ∑ i, min (e' i) (∑ i, e i + ∑ i, e' i) := H _
    _ = ∑ i, e' i := Finset.sum_congr rfl fun i _ => min_eq_left (h2 i)

theorem card_ne_zero_eq {n : ℕ} (e : Fin n → ℕ) :
    (Finset.univ.filter fun i => e i ≠ 0).card = ∑ i, min (e i) 1 := by
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : e i = 0
  · rw [ite_eq_right (not_not.mpr hi), hi]
    simp
  · rw [ite_eq_left hi, min_eq_right (Nat.one_le_iff_ne_zero.mpr hi)]

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem mem_orthK {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {w : V} :
    w ∈ orthK h U ↔ ∀ u ∈ U, h u w = 0 := by
  simp [orthK, Submodule.mem_iInf, LinearMap.mem_ker]

theorem apply_mem_orthK {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) {w : V} (hw : w ∈ orthK h U) : g w ∈ orthK h U := by
  rw [mem_orthK] at hw ⊢
  intro u hu
  have e : h u (g w) = h (g u) (g w) := by rw [hg.2 u hu]
  rw [e, hg.1 u w]
  exact hw u hu

theorem gmap_inf_sub {g : V ≃ₗ[K] V} (X : Submodule K V) (h1 : ∀ x ∈ X, g x ∈ X)
    (h2 : ∀ x ∈ X, g.symm x ∈ X) (Λ : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap g (Λ ⊓ X.restrictScalars (𝓞 K)) =
      Formalism.HermitianLatticesTheory.gmap g Λ ⊓ X.restrictScalars (𝓞 K) := by
  have hinj : Function.Injective ((g : V →ₗ[K] V).restrictScalars (𝓞 K)) :=
    fun a b e => g.injective e
  rw [Formalism.HermitianLatticesTheory.gmap, Submodule.map_inf _ hinj]
  congr 1
  ext x
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact h1 y hy
  · intro hx
    exact ⟨g.symm x, h2 x hx, g.apply_symm_apply x⟩

theorem gmap_cutW {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) (Λ : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap g (Λ ⊓ (orthK h U).restrictScalars (𝓞 K)) =
      Formalism.HermitianLatticesTheory.gmap g Λ ⊓ (orthK h U).restrictScalars (𝓞 K) := by
  refine gmap_inf_sub _ (fun x hx => apply_mem_orthK hg hx) (fun x hx => ?_) Λ
  have := apply_mem_orthK ((isomFix h U).inv_mem hg) hx
  exact this

theorem gmap_cutU {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) (Λ : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap g (Λ ⊓ U.restrictScalars (𝓞 K)) =
      Formalism.HermitianLatticesTheory.gmap g Λ ⊓ U.restrictScalars (𝓞 K) := by
  refine gmap_inf_sub _ (fun x hx => by rw [hg.2 x hx]; exact hx) (fun x hx => ?_) Λ
  rw [g.symm_apply_eq.mpr (hg.2 x hx).symm]
  exact hx

theorem gmap_eq_self {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) {M : Submodule (𝓞 K) V} (hM : ∀ x ∈ M, x ∈ U) :
    Formalism.HermitianLatticesTheory.gmap g M = M := by
  ext x
  rw [Formalism.HermitianLatticesTheory.gmap, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, e⟩
    have e2 : g y = y := hg.2 y (hM y hy)
    rw [← e]
    change g y ∈ M
    rw [e2]
    exact hy
  · intro hx
    exact ⟨x, hx, hg.2 x (hM x hx)⟩

theorem cut_isLatIn {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsFullLattice K Λ) (X : Submodule K V) :
    IsLatIn X (Λ ⊓ X.restrictScalars (𝓞 K)) := by
  refine ⟨hΛ.toIsLattice.fg.of_le inf_le_left, le_antisymm ?_ ?_⟩
  · exact Submodule.span_le.mpr fun x hx => hx.2
  · intro x hx
    obtain ⟨r, hr, hrx⟩ := StabilizerLattices.exists_smul_mem hΛ x
    have hcut : r • x ∈ Λ ⊓ X.restrictScalars (𝓞 K) :=
      ⟨hrx, (X.restrictScalars (𝓞 K)).smul_mem r hx⟩
    have hr' : algebraMap (𝓞 K) K r ≠ 0 := by simpa using hr
    apply (Submodule.smul_mem_iff _ hr').mp
    rw [algebraMap_smul]
    exact Submodule.subset_span hcut

theorem integral_of_unimod {h : V →ₗ⋆[K] V →ₗ[K] K} {Λ : Submodule (𝓞 K) V}
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular h Λ) (X : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h (Λ ⊓ X) := by
  intro x hx y hy
  have hy' : y ∈ Formalism.HermitianLatticesTheory.dual h Λ := by
    rw [hU]
    exact hy.1
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap] at hy'
  exact hy' x hx.1

scoped instance fixAct (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) :
    MulAction (isomFix h U) (Submodule (𝓞 K) V) where
  smul g Λ := Formalism.HermitianLatticesTheory.gmap g.1 Λ
  one_smul := autSub_gmap_one
  mul_smul a b Λ := autSub_gmap_mul a.1 b.1 Λ

def stabEquiv (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (Λ : Submodule (𝓞 K) V) :
    MulAction.stabilizer (isomFix h U) Λ ≃ stabFix h U Λ where
  toFun a := ⟨a.1.1, a.1.2, MulAction.mem_stabilizer_iff.mp a.2⟩
  invFun b := ⟨⟨b.1, b.2.1⟩, MulAction.mem_stabilizer_iff.mpr b.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem card_stab (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (Λ : Submodule (𝓞 K) V) :
    Nat.card (MulAction.stabilizer (isomFix h U) Λ) = Nat.card (stabFix h U Λ) :=
  Nat.card_congr (stabEquiv h U Λ)

theorem finite_stab {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {Λ : Submodule (𝓞 K) V}
    (hfin : (stabFix h U Λ).Finite) :
    ((MulAction.stabilizer (isomFix h U) Λ : Set (isomFix h U))).Finite := by
  have := hfin.to_subtype
  exact Set.finite_coe_iff.mp (Finite.of_equiv _ (stabEquiv h U Λ).symm)

theorem nondegOn_U {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {U : Submodule K V}
    (hUW : IsCompl U (orthK h U)) : NondegOn h U := by
  intro x hx hxy
  have hxW : x ∈ orthK h U := by
    rw [mem_orthK]
    intro u hu
    rw [← hs.eq x u, hxy u hu, map_zero]
  exact (Submodule.disjoint_def.mp hUW.disjoint) x hx hxW

theorem nondegenerate_on_orth_compl {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hnd : Nondeg h)
    {U : Submodule K V} (hUW : IsCompl U (orthK h U)) : NondegOn h (orthK h U) := by
  intro x hx hxy
  apply hnd x
  intro v
  have hv : v ∈ U ⊔ orthK h U := by rw [hUW.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add (f := _), hxy w hw, ← hs.eq u x, (mem_orthK.mp hx) u hu, map_zero, add_zero]

theorem vJof_eq_of_jordan (h2 : JordanInv) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {X X' : Submodule K V} {L L' : Submodule (𝓞 K) V}
    (hL : IsLatIn X L) (hL' : IsLatIn X' L') {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {b a b' a'}
    (hJ : IsJordanIn h X L 𝔭 b a) (hJ' : IsJordanIn h X' L' 𝔭 b' a')
    (hiso : Nonempty (DiscMod h X L 𝔭 ≃ₗ[𝓞 K] DiscMod h X' L' 𝔭)) :
    vJof 𝔭 a = vJof 𝔭 a' ∧ cJof 𝔭 a = cJof 𝔭 a' := by
  have H := h2 K F V V hK hF h h hs hs X X' L L' hL hL' 𝔭 h𝔭 b a b' a' hJ hJ' hiso
  refine ⟨sum_eq_of_min _ _ H, ?_⟩
  unfold cJof
  rw [card_ne_zero_eq (fun i => vF 𝔭 (a i)), card_ne_zero_eq (fun i => vF 𝔭 (a' i))]
  exact H 1

theorem vJ_cJ_eq (h2 : JordanInv) (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {X : Submodule K V} {L : Submodule (𝓞 K) V}
    (hL : IsLatIn X L) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {b a}
    (hJ : IsJordanIn h X L 𝔭 b a) : vJ h X L 𝔭 = vJof 𝔭 a ∧ cJ h X L 𝔭 = cJof 𝔭 a := by
  have key : ∀ b' a', IsJordanIn h X L 𝔭 b' a' → vJof 𝔭 a' = vJof 𝔭 a ∧ cJof 𝔭 a' = cJof 𝔭 a :=
    fun b' a' hJ' => vJof_eq_of_jordan h2 hK hF hs hL hL h𝔭 hJ' hJ ⟨LinearEquiv.refl _ _⟩
  constructor
  · have e : {v | ∃ b a, IsJordanIn h X L 𝔭 b a ∧ v = vJof 𝔭 a} = {vJof 𝔭 a} := by
      ext v
      constructor
      · rintro ⟨b', a', hJ', rfl⟩
        exact (key b' a' hJ').1
      · rintro rfl
        exact ⟨b, a, hJ, rfl⟩
    unfold vJ
    rw [e, csInf_singleton]
  · have e : {v | ∃ b a, IsJordanIn h X L 𝔭 b a ∧ v = cJof 𝔭 a} = {cJof 𝔭 a} := by
      ext v
      constructor
      · rintro ⟨b', a', hJ', rfl⟩
        exact (key b' a' hJ').2
      · rintro rfl
        exact ⟨b, a, hJ, rfl⟩
    unfold cJ
    rw [e, csInf_singleton]

end Formalism.L2.SG.Pf.G9

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3
open scoped Formalism.L2.SG.Pf.G9

theorem glueMass_of (h1 : JordanExists) (h2 : JordanInv) (h6 : GlueLoc) (h8 : GlueProd)
    (hG : GenusMassW) : GlueMass := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs hnd U hUW hpos M hM hMi hne c hc
  classical
  have hnd' : h.Nondegenerate := ⟨hnd, fun y hy => hnd y fun x => by
    rw [← hs.eq x y, hy x, map_zero]⟩
  have hfull {Λ : Submodule (𝓞 K) V} (hΛ : Λ ∈ GlueSet h U M) :
      Submodule.IsFullLattice K Λ :=
    { toIsLattice := hΛ.1
      span_eq_top := GlobalTheory.LoopC.Base.span_eq_top_of_unimodular h hs hnd' hΛ.1 hΛ.2.1 }
  obtain ⟨Λ₀, hΛ₀⟩ := hne
  obtain ⟨T₀, hT⟩ : ∃ T₀, Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K) = T₀ := ⟨_, rfl⟩
  have hT₀ : IsLatIn (orthK h U) T₀ := hT ▸ G9.cut_isLatIn (hfull hΛ₀) _
  have hT₀i : Formalism.HermitianLatticesTheory.IsIntegralLat h T₀ := hT ▸ G9.integral_of_unimod hΛ₀.2.1 _
  obtain ⟨sY, hsY1, hsY2, hsYfin, hmass⟩ := hG K F V hK hF h hs hnd U hUW hpos T₀ hT₀ hT₀i c hc
  have hrefl : ∀ T, SameGenusFix (F := F) h U T T :=
    fun T _ _ => ⟨1, (isomFix h U).one_mem, autSub_gmap_one _⟩
  have hB : ∀ Λ ∈ GlueSet h U M, IsLatIn (orthK h U) (Λ ⊓ (orthK h U).restrictScalars (𝓞 K)) ∧
      SameGenusFix (F := F) h U T₀ (Λ ⊓ (orthK h U).restrictScalars (𝓞 K)) := by
    intro Λ hΛ
    have hl := G9.cut_isLatIn (hfull hΛ) (orthK h U)
    refine ⟨hl, ?_⟩
    have e1 := ((h8 K F V hK hF h hs hnd U hUW hpos M hM Λ hΛ _ hl).1).mpr (hrefl _)
    have e2 := ((h8 K F V hK hF h hs hnd U hUW hpos M hM Λ₀ hΛ₀ _ hl).1).mp e1
    rwa [hT] at e2
  have hfib0 : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → fibP h U 𝔭 M T₀ ≠ 0 :=
    ((h8 K F V hK hF h hs hnd U hUW hpos M hM Λ₀ hΛ₀ T₀ hT₀).1).mpr (by rw [hT]; exact hrefl _)
  have hfibeq : ∀ T, SameGenusFix (F := F) h U T₀ T → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
      fibP h U 𝔭 M T = fibP h U 𝔭 M T₀ := by
    intro T hg 𝔭 h𝔭
    obtain ⟨g, hg, e⟩ := hg 𝔭 h𝔭
    have e1 : fibP h U 𝔭 M T = fibP h U 𝔭 M (Formalism.HermitianLatticesTheory.gmap g T₀) := by
      unfold fibP
      rw [← LocalizedFibreSets.gmap_locF, e]
    rw [e1]
    exact (h6 K F V hK hF h hs hnd U hUW M T₀ hM hT₀ 𝔭 h𝔭).2 g hg
  have hdisc : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → fibP h U 𝔭 M T₀ = discAut h (orthK h U) T₀ 𝔭 :=
    fun 𝔭 h𝔭 => ((h6 K F V hK hF h hs hnd U hUW M T₀ hM hT₀ 𝔭 h𝔭).1 (hfib0 𝔭 h𝔭)).2
  have hfibcard : ∀ T, IsLatIn (orthK h U) T → SameGenusFix (F := F) h U T₀ T →
      Nat.card {Λ : Submodule (𝓞 K) V //
          Λ ∈ GlueSet h U M ∧ Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = T} =
        ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, discAut h (orthK h U) T₀ 𝔭.1 := by
    intro T hTl hg
    rw [(h8 K F V hK hF h hs hnd U hUW hpos M hM Λ₀ hΛ₀ T hTl).2]
    exact tprod_congr fun 𝔭 => by rw [hfibeq T hg 𝔭.1 𝔭.2, hdisc 𝔭.1 𝔭.2]
  have hN : ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, discAut h (orthK h U) T₀ 𝔭.1 ≠ 0 :=
    G9.tprod_nat_ne_zero _ fun 𝔭 => by rw [← hdisc 𝔭.1 𝔭.2]; exact hfib0 𝔭.1 𝔭.2
  let π : Submodule (𝓞 K) V → Submodule (𝓞 K) V := fun Λ => Λ ⊓ (orthK h U).restrictScalars (𝓞 K)
  let B : Set (Submodule (𝓞 K) V) :=
    {T | IsLatIn (orthK h U) T ∧ SameGenusFix (F := F) h U T₀ T}
  have hπ : ∀ (g : isomFix h U) (x : Submodule (𝓞 K) V), π (g • x) = g • π x :=
    fun g x => (G9.gmap_cutW g.2 x).symm
  have hA : ∀ g : isomFix h U, ∀ x ∈ GlueSet h U M, g • x ∈ GlueSet h U M := by
    intro g x hx
    obtain ⟨hx1, hx2, hx3⟩ := hx
    have hact := Formalism.HermitianLatticesTheory.isomAct (𝓞 K) K V h g.1 g.2.1 x
    refine ⟨hact.2.2.2.2.mpr hx1, hact.2.2.2.1.mpr hx2, ?_⟩
    change Formalism.HermitianLatticesTheory.gmap g.1 x ⊓ U.restrictScalars (𝓞 K) = M
    rw [← G9.gmap_cutU g.2, hx3]
    exact G9.gmap_eq_self g.2 fun y hy => by rw [← hM.2]; exact Submodule.subset_span hy
  have hsY1' : ∀ u ∈ sY, u ∈ B := fun u hu => hsY1 u hu
  have hY : ∀ y ∈ B, ∃! t, t ∈ sY ∧ ∃ g : isomFix h U, g • t = y := by
    intro y hy
    obtain ⟨t, ⟨ht, g, hg, e⟩, hu⟩ := hsY2 y hy.1 hy.2
    exact ⟨t, ⟨ht, ⟨g, hg⟩, e⟩, fun t' ⟨ht', ⟨g', hg'⟩, e'⟩ => hu t' ⟨ht', g', hg', e'⟩⟩
  have hfinY : ∀ y ∈ B, ((MulAction.stabilizer (isomFix h U) y : Set (isomFix h U))).Finite :=
    fun y hy => G9.finite_stab (hsYfin y hy.1 hy.2)
  have hfibfin : ∀ u ∈ B, {x | x ∈ GlueSet h U M ∧ π x = u}.Finite := by
    intro u hu
    have hc : Nat.card {x // x ∈ GlueSet h U M ∧ π x = u} ≠ 0 := by
      rw [hfibcard u hu.1 hu.2]
      exact hN
    exact Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero hc)
  obtain ⟨sX, hsX1, hsX2⟩ := OrbSum.exists_reps_of_cover (G := isomFix h U) (GlueSet h U M) hA
    (⋃ u ∈ (sY : Set (Submodule (𝓞 K) V)), {x | x ∈ GlueSet h U M ∧ π x = u})
    (sY.finite_toSet.biUnion fun u hu => hfibfin u (hsY1' u hu))
    (fun x hx => by
      obtain ⟨u, -, hx'⟩ := Set.mem_iUnion₂.mp hx
      exact hx'.1)
    (by
      intro x hx
      obtain ⟨u, ⟨hu, g, e⟩, -⟩ := hY (π x) (hB x hx)
      refine ⟨g⁻¹ • x, Set.mem_biUnion (Finset.mem_coe.mpr hu) ⟨hA _ x hx, ?_⟩, g,
        smul_inv_smul g x⟩
      rw [hπ, ← e, inv_smul_smul])
  refine ⟨sX, hsX1, ?_, ?_, ?_⟩
  · intro Λ hΛ
    obtain ⟨t, ⟨ht, g, e⟩, hu⟩ := hsX2 Λ hΛ
    exact ⟨t, ⟨ht, g.1, g.2, e⟩, fun t' ⟨ht', g', hg', e'⟩ => hu t' ⟨ht', ⟨g', hg'⟩, e'⟩⟩
  · intro Λ hΛ
    have hb := hB Λ (hsX1 Λ hΛ)
    refine (hsYfin _ hb.1 hb.2).subset ?_
    rintro g ⟨hg, e⟩
    exact ⟨hg, by rw [G9.gmap_cutW hg, e]⟩
  · have e1 : ∀ Λ ∈ sX, ((Nat.card (stabFix h U Λ) : ℕ) : ℝ)⁻¹ =
        ((Nat.card (MulAction.stabilizer (isomFix h U) Λ) : ℕ) : ℝ)⁻¹ :=
      fun Λ _ => by rw [G9.card_stab]
    rw [Finset.sum_congr rfl e1, OrbSum.sum_orbits_on π hπ (GlueSet h U M) B hA
      (fun x hx => hB x hx) sX sY hsX1 hsY1' hsX2 hY hfinY]
    have e2 : ∀ u ∈ sY, (Nat.card {x // x ∈ GlueSet h U M ∧ π x = u} : ℝ) /
        (Nat.card (MulAction.stabilizer (isomFix h U) u) : ℝ) =
        ((∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, discAut h (orthK h U) T₀ 𝔭.1 : ℕ) : ℝ) *
          ((Nat.card (stabFix h U u) : ℕ) : ℝ)⁻¹ := by
      intro u hu
      rw [G9.card_stab, div_eq_mul_inv]
      congr 1
      exact_mod_cast hfibcard u (hsY1 u hu).1 (hsY1 u hu).2
    rw [Finset.sum_congr rfl e2, ← Finset.mul_sum, hmass]
    have hJ : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
        vJ h (orthK h U) T₀ 𝔭 = vJ h U M 𝔭 ∧ cJ h (orthK h U) T₀ 𝔭 = cJ h U M 𝔭 := by
      intro 𝔭 h𝔭
      obtain ⟨b, a, hJM⟩ := (h1 K F V hK hF h hs).1 U M (G9.nondegOn_U hs hUW) hM hMi 𝔭 h𝔭
      obtain ⟨b', a', hJT⟩ :=
        (h1 K F V hK hF h hs).1 _ T₀ (G9.nondegenerate_on_orth_compl hs hnd hUW) hT₀ hT₀i 𝔭 h𝔭
      have hiso := ((h6 K F V hK hF h hs hnd U hUW M T₀ hM hT₀ 𝔭 h𝔭).1 (hfib0 𝔭 h𝔭)).1
      have E := G9.vJof_eq_of_jordan h2 hK hF hs hM hT₀ h𝔭 hJM hJT hiso
      have EM := G9.vJ_cJ_eq h2 hK hF hs hM h𝔭 hJM
      have ET := G9.vJ_cJ_eq h2 hK hF hs hT₀ h𝔭 hJT
      exact ⟨by rw [EM.1, ET.1, E.1], by rw [EM.2, ET.2, E.2]⟩
    have hnM : nM F h (orthK h U) T₀ = nM F h U M := by
      unfold nM
      exact tprod_congr fun 𝔭 => by rw [(hJ 𝔭.1 𝔭.2).1]
    rw [hnM]
    congr 1
    exact tprod_congr fun 𝔭 => by rw [(hJ 𝔭.1 𝔭.2).2]

end Formalism.L2.SG.Pf.Cnt
end
end

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalComplementGenusMass

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.G9

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def formOn (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) : ↥X →ₗ⋆[K] ↥X →ₗ[K] K :=
  (h.comp X.subtype).compl₂ X.subtype

@[simp] theorem formOn_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) (x y : ↥X) :
    formOn h X x y = h x y := rfl

theorem formOn_isSymm {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (X : Submodule K V) :
    (formOn h X).IsSymm :=
  ⟨fun x y => hs.eq (x : V) (y : V)⟩

def incl (X : Submodule K V) : ↥X →ₗ[𝓞 K] V := X.subtype.restrictScalars (𝓞 K)

theorem incl_injective (X : Submodule K V) : Function.Injective (incl X) := Subtype.val_injective

def push (X : Submodule K V) (L : Submodule (𝓞 K) ↥X) : Submodule (𝓞 K) V := L.map (incl X)

def pull (X : Submodule K V) (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) ↥X := L.comap (incl X)

theorem mem_push {X : Submodule K V} {L : Submodule (𝓞 K) ↥X} {v : V} :
    v ∈ push X L ↔ ∃ x ∈ L, (x : V) = v := Submodule.mem_map

theorem coe_mem_push {X : Submodule K V} {L : Submodule (𝓞 K) ↥X} {x : ↥X} :
    (x : V) ∈ push X L ↔ x ∈ L := by
  rw [mem_push]
  constructor
  · rintro ⟨y, hy, e⟩
    rwa [← Subtype.ext e]
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem push_le (X : Submodule K V) (L : Submodule (𝓞 K) ↥X) : ∀ v ∈ push X L, v ∈ X := by
  rintro v ⟨x, -, rfl⟩
  exact x.2

theorem push_pull {X : Submodule K V} {L : Submodule (𝓞 K) V} (hL : ∀ v ∈ L, v ∈ X) :
    push X (pull X L) = L := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hv
    exact ⟨⟨v, hL v hv⟩, hv, rfl⟩

theorem push_injective (X : Submodule K V) : Function.Injective (push X) :=
  Submodule.map_injective_of_injective (incl_injective X)

theorem algebraMap_ne_zero {𝔭 : Ideal (𝓞 F)} (_hp : 𝔭.IsPrime) {t : 𝓞 F} (ht : t ∉ 𝔭) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0 := by
  have ht0 : t ≠ 0 := fun e => ht (e ▸ 𝔭.zero_mem)
  have e : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := rfl
  rw [e]
  exact (map_ne_zero (algebraMap F K)).mpr (by exact_mod_cast ht0)

theorem mem_of_smul_mem {X : Submodule K V} {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {t : 𝓞 F}
    (ht : t ∉ 𝔭) {v : V} (hv : algebraMap (𝓞 F) (𝓞 K) t • v ∈ X) : v ∈ X := by
  have hne := algebraMap_ne_zero (K := K) hp ht
  have e : v = (algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t))⁻¹ •
      (algebraMap (𝓞 F) (𝓞 K) t • v) := by
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t) v, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [e]
  exact X.smul_mem _ hv

theorem push_locF (X : Submodule K V) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    push X (locF 𝔭 L) = locF 𝔭 (push X L) := by
  ext v
  rw [LocF.mem_locF_iff hp]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht, hx⟩ := (LocF.mem_locF_iff hp L x).1 hx
    exact ⟨t, ht, ⟨_, hx, (incl X).map_smul _ _⟩⟩
  · rintro ⟨t, ht, hy⟩
    have hv : v ∈ X := mem_of_smul_mem (K := K) hp ht (push_le X L _ hy)
    refine ⟨⟨v, hv⟩, (LocF.mem_locF_iff hp L _).2 ⟨t, ht, ?_⟩, rfl⟩
    rw [← coe_mem_push (X := X)]
    exact hy

theorem push_span (X : Submodule K V) (s : Set ↥X) :
    push X (Submodule.span (𝓞 K) s) = Submodule.span (𝓞 K) (((↑) : ↥X → V) '' s) :=
  Submodule.map_span (incl X) s

theorem isLatIn_push_iff_isLattice {X : Submodule K V} (L : Submodule (𝓞 K) ↥X) :
    IsLatIn X (push X L) ↔ Submodule.IsFullLattice K L := by
  have hspan : Submodule.span K ((push X L : Submodule (𝓞 K) V) : Set V) =
      (Submodule.span K (L : Set ↥X)).map X.subtype := by
    rw [Submodule.map_span]
    congr 1
  constructor
  · rintro ⟨hfg, hsp⟩
    refine
      { toIsLattice := Submodule.IsLattice.of_fg K
          (Submodule.fg_of_fg_map_injective _ (incl_injective X) hfg)
        span_eq_top := ?_ }
    apply Submodule.map_injective_of_injective X.injective_subtype
    rw [← hspan, hsp, Submodule.map_subtype_top]
  · intro hL
    refine ⟨hL.toIsLattice.fg.map _, ?_⟩
    rw [hspan, hL.span_eq_top, Submodule.map_subtype_top]

theorem isIntegralLat_push {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} (L : Submodule (𝓞 K) ↥X) :
    Formalism.HermitianLatticesTheory.IsIntegralLat h (push X L) ↔ Formalism.HermitianLatticesTheory.IsIntegralLat (formOn h X) L := by
  constructor
  · intro H x hx y hy
    exact H _ (coe_mem_push.mpr hx) _ (coe_mem_push.mpr hy)
  · rintro H _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact H x hx y hy

theorem isJordanIn_top {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V} {L : Submodule (𝓞 K) ↥X}
    {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {b : Fin (finrank K X) → V} {a : Fin (finrank K X) → 𝓞 F}
    (H : IsJordanIn h X (push X L) 𝔭 b a) :
    IsJordanIn (formOn h X) ⊤ L 𝔭 (fun i => ⟨b (Fin.cast (finrank_top K ↥X) i), H.1 _⟩)
      (fun i => a (Fin.cast (finrank_top K ↥X) i)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  refine ⟨fun _ => Submodule.mem_top, ?_, fun i j hij => h3 _ _ fun e => hij (Fin.cast_injective _ e),
    fun i => h4 _, fun i => h5 _⟩
  apply push_injective X
  rw [push_locF X hp, push_locF X hp, push_span]
  refine Eq.trans ?_ h2
  congr 2
  ext v
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨i, rfl⟩
    refine ⟨_, ⟨Fin.cast (finrank_top K ↥X).symm i, rfl⟩, ?_⟩
    rfl

section Ext

variable [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}

def extId (hc : IsCompl U (orthK h U)) (g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)) : V ≃ₗ[K] V :=
  (Submodule.prodEquivOfIsCompl U (orthK h U) hc).symm.trans
    (((LinearEquiv.refl K ↥U).prodCongr g).trans (Submodule.prodEquivOfIsCompl U (orthK h U) hc))

theorem extId_add (hc : IsCompl U (orthK h U)) (g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)) {u w : V}
    (hu : u ∈ U) (hw : w ∈ orthK h U) : extId hc g (u + w) = u + (g ⟨w, hw⟩ : V) := by
  have e1 : (Submodule.prodEquivOfIsCompl U (orthK h U) hc).symm (u + w) = (⟨u, hu⟩, ⟨w, hw⟩) := by
    rw [LinearEquiv.symm_apply_eq, Submodule.coe_prodEquivOfIsCompl']
  simp only [extId, LinearEquiv.trans_apply, e1, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, Submodule.coe_prodEquivOfIsCompl']

theorem exists_add (hc : IsCompl U (orthK h U)) (v : V) :
    ∃ u ∈ U, ∃ w ∈ orthK h U, u + w = v := by
  have hv : v ∈ U ⊔ orthK h U := by rw [hc.sup_eq_top]; exact Submodule.mem_top
  exact Submodule.mem_sup.mp hv

theorem extId_of_mem_U (hc : IsCompl U (orthK h U)) (g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)) {u : V}
    (hu : u ∈ U) : extId hc g u = u := by
  have := extId_add hc g hu (orthK h U).zero_mem
  rw [add_zero] at this
  rw [this]
  simp

theorem extension_identity_of_mem_compl (hc : IsCompl U (orthK h U)) (g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U))
    (w : ↥(orthK h U)) : extId hc g w = g w := by
  have := extId_add hc g U.zero_mem w.2
  rw [zero_add] at this
  rw [this, zero_add]

theorem extId_mem (hs : h.IsSymm) (hc : IsCompl U (orthK h U)) {g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)}
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom (formOn h (orthK h U))) : extId hc g ∈ isomFix h U := by
  refine ⟨fun v v' => ?_, fun u hu => extId_of_mem_U hc g hu⟩
  obtain ⟨u, hu, w, hw, rfl⟩ := exists_add hc v
  obtain ⟨u', hu', w', hw', rfl⟩ := exists_add hc v'
  rw [extId_add hc g hu hw, extId_add hc g hu' hw']
  have hg' : h (g ⟨w, hw⟩ : V) (g ⟨w', hw'⟩ : V) = h w w' := hg _ _
  have o1 : ∀ {x y : V}, x ∈ U → y ∈ orthK h U → h x y = 0 := fun hx hy => mem_orthK.mp hy _ hx
  have o2 : ∀ {x y : V}, x ∈ U → y ∈ orthK h U → h y x = 0 := fun {x y} hx hy => by
    rw [← hs.eq x y, o1 hx hy, map_zero]
  simp only [map_add (f := _), LinearMap.add_apply]
  rw [hg', o1 hu (g ⟨w', hw'⟩).2, o2 hu' (g ⟨w, hw⟩).2, o1 hu hw', o2 hu' hw]

theorem map_orthK {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) :
    (orthK h U).map (g : V →ₗ[K] V) = orthK h U := by
  ext x
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact apply_mem_orthK hg hy
  · intro hx
    exact ⟨g.symm x, apply_mem_orthK ((isomFix h U).inv_mem hg) hx, g.apply_symm_apply x⟩

def restr {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U) :=
  g.ofSubmodules (orthK h U) (orthK h U) (map_orthK hg)

theorem restr_apply {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) (w : ↥(orthK h U)) :
    (restr hg w : V) = g w :=
  LinearEquiv.ofSubmodules_apply _ _ _

theorem restr_mem {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) :
    restr hg ∈ Formalism.HermitianLatticesTheory.isom (formOn h (orthK h U)) := fun x y => by
  simp only [formOn_apply, restr_apply]
  exact hg.1 x y

theorem extId_restr (hc : IsCompl U (orthK h U)) {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) :
    extId hc (restr hg) = g := by
  apply LinearEquiv.ext
  intro v
  obtain ⟨u, hu, w, hw, rfl⟩ := exists_add hc v
  rw [extId_add hc _ hu hw, restr_apply, map_add (f := _), hg.2 u hu]

theorem restr_extId (hs : h.IsSymm) (hc : IsCompl U (orthK h U))
    {g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)} (hg : g ∈ Formalism.HermitianLatticesTheory.isom (formOn h (orthK h U))) :
    restr (extId_mem hs hc hg) = g := by
  apply LinearEquiv.ext
  intro w
  apply Subtype.ext
  exact (restr_apply _ w).trans (extension_identity_of_mem_compl hc g w)

theorem gmap_push {g : V ≃ₗ[K] V} (hg : g ∈ isomFix h U) (L : Submodule (𝓞 K) ↥(orthK h U)) :
    Formalism.HermitianLatticesTheory.gmap g (push (orthK h U) L) = push (orthK h U) (Formalism.HermitianLatticesTheory.gmap (restr hg) L) := by
  unfold Formalism.HermitianLatticesTheory.gmap push
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1

theorem gmap_extId_push (hs : h.IsSymm) (hc : IsCompl U (orthK h U))
    {g : ↥(orthK h U) ≃ₗ[K] ↥(orthK h U)} (hg : g ∈ Formalism.HermitianLatticesTheory.isom (formOn h (orthK h U)))
    (L : Submodule (𝓞 K) ↥(orthK h U)) :
    Formalism.HermitianLatticesTheory.gmap (extId hc g) (push (orthK h U) L) = push (orthK h U) (Formalism.HermitianLatticesTheory.gmap g L) := by
  rw [gmap_push (extId_mem hs hc hg), restr_extId hs hc hg]

end Ext

end Formalism.L2.SG.Pf.OrthogonalComplementGenusMass
end
end

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalComplementGenusMass

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mem_dual {Y : Type} [AddCommGroup Y] [Module K Y] [Module (𝓞 K) Y] [IsScalarTower (𝓞 K) K Y]
    {B : Y →ₗ⋆[K] Y →ₗ[K] K} {L : Submodule (𝓞 K) Y} {x : Y} :
    x ∈ Formalism.HermitianLatticesTheory.dual B L ↔ ∀ y ∈ L, B y x ∈ (1 : Submodule (𝓞 K) K) := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {X : Submodule K V}

theorem push_dualIn (L : Submodule (𝓞 K) ↥X) :
    push X (dualIn (formOn h X) ⊤ L) = dualIn h X (push X L) := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, mem_dual.mpr ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact mem_dual.mp hx.2 y hy
  · rintro ⟨hvX, hv⟩
    refine ⟨⟨v, hvX⟩, ⟨by simp, mem_dual.mpr fun y hy => ?_⟩, rfl⟩
    exact mem_dual.mp hv _ (coe_mem_push.mpr hy)

variable {𝔭 : Ideal (𝓞 F)}

theorem map_incl_dual (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    (locF 𝔭 (dualIn (formOn h X) ⊤ L)).map (incl X) = locF 𝔭 (dualIn h X (push X L)) := by
  change push X _ = _
  rw [push_locF X hp, push_dualIn]

def dualEquiv (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    ↥(locF 𝔭 (dualIn (formOn h X) ⊤ L)) ≃ₗ[𝓞 K] ↥(locF 𝔭 (dualIn h X (push X L))) :=
  (Submodule.equivMapOfInjective (incl X) (incl_injective X) _).trans
    (LinearEquiv.ofEq _ _ (map_incl_dual hp L))

theorem dualEquiv_apply (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X)
    (x : ↥(locF 𝔭 (dualIn (formOn h X) ⊤ L))) :
    ((dualEquiv (h := h) hp L x : ↥(locF 𝔭 (dualIn h X (push X L)))) : V) = ((x : ↥X) : V) := rfl

theorem dualEquiv_symm_apply (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X)
    (y : ↥(locF 𝔭 (dualIn h X (push X L)))) :
    ((((dualEquiv (h := h) hp L).symm y : ↥(locF 𝔭 (dualIn (formOn h X) ⊤ L))) : ↥X) : V) = (y : V) := by
  have := dualEquiv_apply hp L ((dualEquiv (h := h) hp L).symm y)
  rw [LinearEquiv.apply_symm_apply] at this
  exact this.symm

theorem map_dualEquiv (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    ((locF 𝔭 L).comap (locF 𝔭 (dualIn (formOn h X) ⊤ L)).subtype).map
        (dualEquiv (h := h) hp L : _ →ₗ[𝓞 K] _) =
      (locF 𝔭 (push X L)).comap (locF 𝔭 (dualIn h X (push X L))).subtype := by
  rw [Submodule.map_equiv_eq_comap_symm]
  ext y
  simp only [Submodule.mem_comap, Submodule.subtype_apply]
  rw [← coe_mem_push (X := X), push_locF X hp]
  exact Iff.of_eq (congrArg (fun v => v ∈ locF 𝔭 (push X L)) (dualEquiv_symm_apply (h := h) hp L y))

def discEquiv (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    DiscMod (formOn h X) ⊤ L 𝔭 ≃ₗ[𝓞 K] DiscMod h X (push X L) 𝔭 :=
  Submodule.Quotient.equiv _ _ (dualEquiv (h := h) hp L) (map_dualEquiv (h := h) hp L)

theorem discEquiv_mk (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X)
    (x : ↥(locF 𝔭 (dualIn (formOn h X) ⊤ L))) :
    discEquiv (h := h) hp L (Submodule.Quotient.mk x) = Submodule.Quotient.mk (dualEquiv (h := h) hp L x) := rfl

theorem discEquiv_symm_mk (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X)
    (y : ↥(locF 𝔭 (dualIn h X (push X L)))) :
    (discEquiv (h := h) hp L).symm (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm y) := rfl

def endEquiv (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    Module.End (𝓞 K) (DiscMod (formOn h X) ⊤ L 𝔭) ≃ Module.End (𝓞 K) (DiscMod h X (push X L) 𝔭) where
  toFun P := (discEquiv (h := h) hp L : _ →ₗ[𝓞 K] _) ∘ₗ P ∘ₗ ((discEquiv (h := h) hp L).symm : _ →ₗ[𝓞 K] _)
  invFun P := ((discEquiv (h := h) hp L).symm : _ →ₗ[𝓞 K] _) ∘ₗ P ∘ₗ (discEquiv (h := h) hp L : _ →ₗ[𝓞 K] _)
  left_inv P := by
    apply LinearMap.ext
    intro z
    simp
  right_inv P := by
    apply LinearMap.ext
    intro z
    simp

theorem discAut_push (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) ↥X) :
    discAut h X (push X L) 𝔭 = discAut (formOn h X) ⊤ L 𝔭 := by
  unfold discAut
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv (endEquiv (h := h) hp L) ?_)
  intro P
  constructor
  · intro H x y x' y' hx hy
    have hx' : Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm x') =
        P (Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm x)) := by
      rw [← discEquiv_symm_mk, hx, ← discEquiv_symm_mk]
      change (discEquiv (h := h) hp L).symm ((discEquiv (h := h) hp L) (P ((discEquiv (h := h) hp L).symm _))) = _
      rw [LinearEquiv.symm_apply_apply]
    have hy' : Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm y') =
        P (Submodule.Quotient.mk ((dualEquiv (h := h) hp L).symm y)) := by
      rw [← discEquiv_symm_mk, hy, ← discEquiv_symm_mk]
      change (discEquiv (h := h) hp L).symm ((discEquiv (h := h) hp L) (P ((discEquiv (h := h) hp L).symm _))) = _
      rw [LinearEquiv.symm_apply_apply]
    have := H _ _ _ _ hx' hy'
    simpa only [formOn_apply, dualEquiv_symm_apply] using this
  · intro H x y x' y' hx hy
    have hx' : Submodule.Quotient.mk (dualEquiv (h := h) hp L x') =
        (endEquiv (h := h) hp L P) (Submodule.Quotient.mk (dualEquiv (h := h) hp L x)) := by
      change _ = (discEquiv (h := h) hp L) (P ((discEquiv (h := h) hp L).symm (Submodule.Quotient.mk _)))
      rw [discEquiv_symm_mk, LinearEquiv.symm_apply_apply, ← hx, discEquiv_mk]
    have hy' : Submodule.Quotient.mk (dualEquiv (h := h) hp L y') =
        (endEquiv (h := h) hp L P) (Submodule.Quotient.mk (dualEquiv (h := h) hp L y)) := by
      change _ = (discEquiv (h := h) hp L) (P ((discEquiv (h := h) hp L).symm (Submodule.Quotient.mk _)))
      rw [discEquiv_symm_mk, LinearEquiv.symm_apply_apply, ← hy, discEquiv_mk]
    have := H _ _ _ _ hx' hy'
    simpa only [formOn_apply, dualEquiv_apply] using this

end Formalism.L2.SG.Pf.OrthogonalComplementGenusMass
end
end

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.OrthogonalComplementGenusMass

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}

def stabEquivW (hs : h.IsSymm) (hc : IsCompl U (orthK h U)) (N : Submodule (𝓞 K) ↥(orthK h U)) :
    stabFix h U (push (orthK h U) N) ≃ Formalism.ThetaLiftIndependence.autL (formOn h (orthK h U)) N where
  toFun g := ⟨restr g.2.1, restr_mem g.2.1, push_injective _ (by rw [← gmap_push g.2.1]; exact g.2.2)⟩
  invFun g := ⟨extId hc g.1, extId_mem hs hc g.2.1, by rw [gmap_extId_push hs hc g.2.1, g.2.2]⟩
  left_inv g := Subtype.ext (extId_restr hc g.2.1)
  right_inv g := Subtype.ext (restr_extId hs hc g.2.1)

theorem card_stab_push (hs : h.IsSymm) (hc : IsCompl U (orthK h U)) (N : Submodule (𝓞 K) ↥(orthK h U)) :
    Nat.card (stabFix h U (push (orthK h U) N)) = Nat.card (Formalism.ThetaLiftIndependence.autL (formOn h (orthK h U)) N) :=
  Nat.card_congr (stabEquivW hs hc N)

theorem sameGenusFix_push_iff (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hc : IsCompl U (orthK h U)) (A B : Submodule (𝓞 K) ↥(orthK h U)) :
    SameGenusFix (F := F) h U (push (orthK h U) A) (push (orthK h U) B) ↔
      Formalism.HermitianLatticesTheory.SameGenus (formOn h (orthK h U)) A B := by
  rw [GoodGenusOrbits.sameGenus_iff (F := F) hK hF A B]
  constructor
  · intro H 𝔭
    obtain ⟨g, hg, e⟩ := H 𝔭.1 𝔭.2
    refine ⟨restr hg, restr_mem hg, push_injective _ ?_⟩
    rw [← gmap_push hg, push_locF _ 𝔭.2.isPrime, push_locF _ 𝔭.2.isPrime]
    exact e
  · intro H 𝔭 h𝔭
    obtain ⟨g, hg, e⟩ := H ⟨𝔭, h𝔭⟩
    refine ⟨extId hc g, extId_mem hs hc hg, ?_⟩
    rw [← push_locF _ h𝔭.isPrime, ← push_locF _ h𝔭.isPrime, gmap_extId_push hs hc hg]
    exact congrArg _ e

end Formalism.L2.SG.Pf.OrthogonalComplementGenusMass
