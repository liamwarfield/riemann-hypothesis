module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.FibreCountOfPositions
public import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource

@[expose] public section

section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.InnerMemOneOfMemDualOrthLattice
section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.MemSupIsotropicOfDualPairing
section -- merged from Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.OrthLatticeIsIntegralOfUnimodular
noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Basic

variable (D : D7)

theorem orth_embedding_isometry (x y : (D.sp.X 0).V) :
    (D.sp.Y 0).hT (D.sp.iXY 0 x) (D.sp.iXY 0 y) = (D.sp.X 0).hT x y :=
  D.sp.iXY_isom 0 (by have := D.R.two_le_m; omega) x y

theorem orth_embedding_injective : Function.Injective (D.sp.iXY 0) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  refine (D.sp.X 0).nondeg.1 x fun y => ?_
  rw [← orth_embedding_isometry, hx]; simp

variable {D} {u : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u)

include he hz in
theorem orth_embedding_mem_orth_plus (x : (D.sp.X 0).V) : D.sp.iXY 0 x ∈ orth (hS D) (Xplus (lf D F0)) := by
  have h : Xplus (lf D F0) ≤ LinearMap.ker ((hS D).hT.flip (D.sp.iXY 0 x)) := by
    refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨a, rfl⟩
      show (hS D).hT (F0.e a) (D.sp.iXY 0 x) = 0
      rw [he]
      exact c_symm0 (D.sp.hyp_orthX a x).1
    · intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      show (hS D).hT F0.z (D.sp.iXY 0 x) = 0
      rw [hz]
      unfold D7.zmOf
      rw [map_smulₛₗ, LinearMap.smul_apply, c_symm0 (D.sp.zm_orth x), smul_zero]
  exact c_mem_orth.2 fun v hv => h hv

include he in
theorem eq_zero_of_embedding_mem_isotropic {x : (D.sp.X 0).V} (hx : D.sp.iXY 0 x ∈ Xsp (lf D F0)) : x = 0 := by
  have hx' : D.sp.iXY 0 x ∈ Submodule.span D.host.E (Set.range D.sp.hypE) := by rw [← he]; exact hx
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hx'
  have h0 : ∀ i, c i = 0 := by
    intro i
    have h1 := (D.sp.hyp_orthX i x).2
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc, map_sum, LinearMap.sum_apply] at h1
    simp only [map_smulₛₗ, LinearMap.smul_apply, D.sp.hyp_ef, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    simpa using h1
  apply orth_embedding_injective D
  rw [← hc, map_zero]
  exact Finset.sum_eq_zero fun i _ => by rw [h0 i, zero_smul]


include he hz in
theorem orth_space_posDef_every_place (hT : 0 < Tu D u) : Cnt.IsPosDef (D.sp.X 0).hT := by
  intro τ x hx
  have h1 := p_posX D (Tu D u) hT (lf D F0) τ (D.sp.iXY 0 x) (orth_embedding_mem_orth_plus F0 he hz x)
    (fun h => hx (eq_zero_of_embedding_mem_isotropic F0 he h))
  unfold nrm at h1
  rwa [orth_embedding_isometry] at h1

end Basic

section Lat

variable {D : D7} {T : D.host.E} (Λ : LatV D) (F : LFlag (D.sp.Y 0) D.R.rS T)

theorem mem_orthLattice_iff_mem_sub {x : (D.sp.X 0).V} : x ∈ L0X D Λ F ↔ D.sp.iXY 0 x ∈ L0sub Λ F := Iff.rfl

theorem orthLattice_isIntegral_of_unimodular (hu : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ) :
    Formalism.HermitianLatticesTheory.IsIntegralLat (D.sp.X 0).hT (L0X D Λ F) := by
  intro x hx y hy
  obtain ⟨l, hl, ξ, hξ, e⟩ := Submodule.mem_sup.1 ((mem_orthLattice_iff_mem_sub Λ F).1 hx).1.1
  obtain ⟨l', hl', ξ', hξ', e'⟩ := Submodule.mem_sup.1 ((mem_orthLattice_iff_mem_sub Λ F).1 hy).1.1
  rw [← orth_embedding_isometry, ← e, ← e']
  have h1 : (hS D).hT l ξ' = 0 := c_symm0 (c_mem_orth.1 hl.2 ξ' hξ')
  have h2 : (hS D).hT ξ l' = 0 := c_mem_orth.1 hl'.2 ξ hξ
  have h3 : (hS D).hT ξ ξ' = 0 := p_X_iso F hξ hξ'
  simp only [map_add (f := _), LinearMap.add_apply]
  rw [h1, h2, h3, add_zero, add_zero, add_zero]
  exact i_int Λ hu hl.1 hl'.1

end Lat

end Formalism.MainNotions.BridgeLemma₂

end
end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section One

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem star_mem_one_submodule {t : E} (h : t ∈ (1 : Submodule (𝓞 E) E)) : star t ∈ (1 : Submodule (𝓞 E) E) := by
  obtain ⟨o, rfl⟩ := Submodule.mem_one.1 h
  obtain ⟨o', ho'⟩ := i_star_int o
  exact Submodule.mem_one.2 ⟨o', ho'⟩

theorem mul_mem_one_submodule {s t : E} (hs : s ∈ (1 : Submodule (𝓞 E) E)) (h : t ∈ (1 : Submodule (𝓞 E) E)) :
    s * t ∈ (1 : Submodule (𝓞 E) E) := by
  obtain ⟨o, rfl⟩ := Submodule.mem_one.1 hs
  obtain ⟨o', rfl⟩ := Submodule.mem_one.1 h
  exact Submodule.mem_one.2 ⟨o * o', by simp⟩

end One

section Lat

variable {D : D7} {u : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u) (Λ : LatV D)

theorem isotropic_le_orth_self : Xsp (lf D F0) ≤ orth (hS D) (Xsp (lf D F0)) :=
  fun _ hx => c_mem_orth.2 fun _ hv => p_X_iso (lf D F0) hv hx

theorem mem_Lsub_iff_sup_and_orth {v : (hS D).V} : v ∈ Lsub Λ (lf D F0) ↔
    v ∈ Λ ⊔ toO (hS D) (Xsp (lf D F0)) ∧ v ∈ orth (hS D) (Xsp (lf D F0)) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hle : Lrep Λ (lf D F0) ⊔ toO (hS D) (Xsp (lf D F0)) ≤ Λ ⊔ toO (hS D) (Xsp (lf D F0)) :=
      sup_le_sup_right (inf_le_left : Λ ⊓ toO (hS D) (orth (hS D) (Xsp (lf D F0))) ≤ Λ) _
    exact ⟨hle h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    obtain ⟨l, hl, ξ, hξ, e⟩ := Submodule.mem_sup.1 h1
    refine Submodule.mem_sup.2 ⟨l, ⟨hl, ?_⟩, ξ, hξ, e⟩
    have : l = v - ξ := by rw [← e]; abel
    rw [this]
    exact (orth (hS D) (Xsp (lf D F0))).sub_mem h2 (isotropic_le_orth_self F0 hξ)

include he hz in
theorem orth_embedding_mem_orth_isotropic (x : (D.sp.X 0).V) : D.sp.iXY 0 x ∈ orth (hS D) (Xsp (lf D F0)) :=
  c_orth_anti (le_sup_left : Xsp (lf D F0) ≤ Xplus (lf D F0)) (orth_embedding_mem_orth_plus F0 he hz x)

include he hz in
theorem inner_z_orth_embedding_eq_zero (x : (D.sp.X 0).V) : (hS D).hT F0.z (D.sp.iXY 0 x) = 0 :=
  c_mem_orth.1 (orth_embedding_mem_orth_plus F0 he hz x) F0.z
    ((le_sup_right : _ ≤ Xplus (lf D F0)) (Submodule.mem_span_singleton_self _))


include he hz in
theorem mem_orthLattice_iff_image_mem_sup {x : (D.sp.X 0).V} :
    x ∈ L0X D Λ (lf D F0) ↔ D.sp.iXY 0 x ∈ Λ ⊔ toO (hS D) (Xsp (lf D F0)) := by
  rw [mem_orthLattice_iff_mem_sub]
  constructor
  · intro h
    exact ((mem_Lsub_iff_sup_and_orth F0 Λ).1 h.1).1
  · intro h
    exact ⟨(mem_Lsub_iff_sup_and_orth F0 Λ).2 ⟨h, orth_embedding_mem_orth_isotropic F0 he hz x⟩, inner_z_orth_embedding_eq_zero F0 he hz x⟩

include he hz in
theorem exists_smul_mem_orthLattice (hΛ : Submodule.IsFullLattice D.host.E Λ) (x : (D.sp.X 0).V) :
    ∃ c : 𝓞 D.host.E, c ≠ 0 ∧ c • x ∈ L0X D Λ (lf D F0) := by
  obtain ⟨c, hc, hcx⟩ := a_exists_smul_mem Λ hΛ (D.sp.iXY 0 x)
  refine ⟨c, hc, (mem_orthLattice_iff_image_mem_sup F0 he hz Λ).2 ?_⟩
  rw [LinearMap.map_smul_of_tower]
  exact Submodule.mem_sup_left hcx


include he hz in
theorem orthLattice_isLattice (hΛ : Submodule.IsLattice D.host.E Λ) (hu : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ) :
    Submodule.IsLattice D.host.E (L0X D Λ (lf D F0)) := by
  choose c hc hcM using fun i => exists_smul_mem_orthLattice F0 he hz Λ (a_full Λ hΛ hu) ((D.sp.X 0).frame i)
  set M₁ : Submodule (𝓞 D.host.E) (D.sp.X 0).V :=
    Submodule.span (𝓞 D.host.E) (Set.range fun i => c i • (D.sp.X 0).frame i) with hM₁def
  have hM₁ : M₁ ≤ L0X D Λ (lf D F0) := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hcM i)
  have hfg : M₁.FG := Submodule.fg_span (Set.finite_range _)
  have hs : spanE (D.sp.X 0) M₁ = ⊤ := by
    apply top_unique
    rw [← (D.sp.X 0).frame.span_eq]
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    have hm : c i • (D.sp.X 0).frame i ∈ spanE (D.sp.X 0) M₁ :=
      Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩)
    have hn : algebraMap (𝓞 D.host.E) D.host.E (c i) ≠ 0 := by simpa using hc i
    have := (spanE (D.sp.X 0) M₁).smul_mem (algebraMap (𝓞 D.host.E) D.host.E (c i))⁻¹ hm
    rw [← algebraMap_smul D.host.E (c i), smul_smul, inv_mul_cancel₀ hn, one_smul] at this
    exact this
  have hU : (⊤ : Submodule D.host.E (D.sp.X 0).V) ⊓ orth (D.sp.X 0) ⊤ = ⊥ := by
    rw [top_inf_eq, eq_bot_iff]
    intro y hy
    exact (Submodule.mem_bot _).2 ((D.sp.X 0).nondeg.2 y fun x => c_mem_orth.1 hy x trivial)
  obtain ⟨hdfg, -, -⟩ := g_dual_facts g_starInt hU hfg hs
  have hle : L0X D Λ (lf D F0) ≤ dualIn (D.sp.X 0) M₁ := by
    intro x hx
    refine g_mem_dualIn.2 ⟨fun y hy => ?_, by rw [hs]; trivial⟩
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 (orthLattice_isIntegral_of_unimodular Λ (lf D F0) hu y (hM₁ hy) x hx)
    exact ⟨o, ho⟩
  refine ⟨?_, ?_⟩
  · exact isNoetherian_submodule.1 (isNoetherian_of_fg_of_noetherian _ hdfg) _ hle
  · intro s hs hli
    exact (LinearIndependent.iff_fractionRing _ _).mp hli


include he in
theorem mem_sup_isotropic_of_dual_pairing (hΛ : Submodule.IsFullLattice D.host.E Λ) (hu : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ)
    (y : (hS D).V)
    (hy : ∀ m ∈ Λ ⊓ toO (hS D) (orth (hS D) (Xsp (lf D F0))), (hS D).hT m y ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)) :
    y ∈ Λ ⊔ toO (hS D) (Xsp (lf D F0)) := by
  let ℓ : Fin D.R.rS → Module.Dual D.host.E (hS D).V := fun a => (hS D).hT (F0.e a)
  have hℓ : LinearIndependent D.host.E ℓ := by
    rw [Fintype.linearIndependent_iff]
    intro c hc a
    have h1 : (hS D).hT (∑ a, star (c a) • F0.e a) = 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, ← hc]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [map_smulₛₗ, starRingEnd_apply, star_star]
    have h2 : ∑ a, star (c a) • F0.e a = 0 := (hS D).nondeg.1 _ (fun y => by rw [h1]; rfl)
    have h3 := Fintype.linearIndependent_iff.1 F0.e_indep _ h2 a
    simpa using h3
  let bb := Basis.extend hℓ.linearIndepOn_id
  let idx : Fin D.R.rS → hℓ.linearIndepOn_id.extend (Set.subset_univ _) :=
    fun a => ⟨ℓ a, hℓ.linearIndepOn_id.subset_extend _ ⟨a, rfl⟩⟩
  let f : Fin D.R.rS → (hS D).V := fun a =>
    (Module.evalEquiv D.host.E (hS D).V).symm (bb.coord (idx a))
  have hf : ∀ a b, (hS D).hT (F0.e a) (f b) = if a = b then 1 else 0 := by
    intro a b
    change ℓ a ((Module.evalEquiv D.host.E (hS D).V).symm (bb.coord (idx b))) = _
    rw [Module.apply_evalEquiv_symm_apply]
    have ha : bb (idx a) = ℓ a := Basis.extend_apply_self _ _
    classical
    rw [← ha, Basis.coord_apply, Basis.repr_self_apply]
    have hi : idx b = idx a ↔ a = b := by
      constructor
      · intro h
        have := congrArg Subtype.val h
        exact (hℓ.injective this).symm
      · rintro rfl
        rfl
    by_cases h : a = b
    · subst b
      simp only [if_pos rfl]
    · have hn : idx a ≠ idx b := fun hh => h (hi.mp hh.symm)
      simp only [if_neg h, if_neg hn]
  have DL := Formalism.HermitianLatticesTheory.dualLattice (𝓞 D.host.E) D.host.E (hS D).V (hS D).hT (hS D).herm (hS D).nondeg i_star_int
  have hlat : ∀ N : LatV D, N.FG → Submodule.IsFullLattice D.host.E (Λ ⊔ N) := by
    letI := hΛ
    intro N hN
    exact Submodule.IsFullLattice.of_le_of_fg D.host.E le_sup_left (hΛ.fg.sup hN)
  have hΛ₂ := (DL _ (hlat (Submodule.span (𝓞 D.host.E) {y}) (Submodule.fg_span (Set.finite_singleton y)))).1
  choose c hc hcf using fun a => a_exists_smul_mem _ hΛ₂ (f a)
  set ε : 𝓞 D.host.E := ∏ a, c a with hε
  have hε0 : ε ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hc a
  have hε1 : algebraMap (𝓞 D.host.E) D.host.E ε ≠ 0 := by simpa using hε0
  have hg : ∀ a, ε • f a ∈
      Formalism.HermitianLatticesTheory.dual (hS D).hT (Λ ⊔ Submodule.span (𝓞 D.host.E) {y}) := by
    intro a
    rw [hε, ← Finset.prod_erase_mul _ _ (Finset.mem_univ a), mul_smul]
    exact Submodule.smul_mem _ _ (hcf a)
  have hgΛ : ∀ a, ε • f a ∈ Λ := by
    intro a
    rw [← hu]
    exact (i_mem_dual _ _).2 fun l hl => (i_mem_dual _ _).1 (hg a) l (Submodule.mem_sup_left hl)
  have hgy : ∀ a, (hS D).hT (ε • f a) y ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
    intro a
    rw [← c_herm]
    exact star_mem_one_submodule ((i_mem_dual _ _).1 (hg a) y
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self y)))
  set δ : D.host.E := (star (algebraMap (𝓞 D.host.E) D.host.E ε))⁻¹ with hδ
  set N : LatV D := Submodule.span (𝓞 D.host.E) (Set.range fun a => δ • F0.e a) with hN
  have hB := (DL _ (hlat N (Submodule.fg_span (Set.finite_range _)))).2.1
  have hyB : y ∈ Λ ⊔ N := by
    rw [← hB]
    refine (i_mem_dual _ _).2 fun l hl => ?_
    have hlΛ : l ∈ Λ := by
      rw [← hu]
      exact (i_mem_dual _ _).2 fun l' hl' => (i_mem_dual _ _).1 hl l' (Submodule.mem_sup_left hl')
    have ho : ∀ a, ∃ o : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E o =
        (algebraMap (𝓞 D.host.E) D.host.E ε)⁻¹ * (hS D).hT (F0.e a) l := by
      intro a
      have h1 := (i_mem_dual _ _).1 hl (δ • F0.e a)
        (Submodule.mem_sup_right (Submodule.subset_span ⟨a, rfl⟩))
      rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, hδ, star_inv₀, star_star] at h1
      exact Submodule.mem_one.1 h1
    choose o ho using ho
    set l' : (hS D).V := ∑ a, o a • (ε • f a) with hl'
    have hl'Λ : l' ∈ Λ := Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (hgΛ a)
    have hm : l - l' ∈ Λ ⊓ toO (hS D) (orth (hS D) (Xsp (lf D F0))) := by
      refine ⟨Λ.sub_mem hlΛ hl'Λ, ?_⟩
      show l - l' ∈ orth (hS D) (Submodule.span D.host.E (Set.range F0.e))
      refine a_orth_of_frame _ _ fun b => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, hl', map_sum, sub_eq_zero]
      have : ∀ a, (hS D).hT (F0.e b) (o a • (ε • f a)) =
          if b = a then algebraMap (𝓞 D.host.E) D.host.E (o a) * algebraMap (𝓞 D.host.E) D.host.E ε else 0 := by
        intro a
        rw [← algebraMap_smul D.host.E (o a), ← algebraMap_smul D.host.E ε, map_smul, map_smul, hf]
        split_ifs <;> simp
      simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [ho b]
      field_simp
    have e : l = (l - l') + l' := by abel
    rw [e, map_add (f := _), LinearMap.add_apply]
    refine Submodule.add_mem _ (hy _ hm) ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hl', map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun a _ => ?_
    rw [← algebraMap_smul D.host.E (o a), map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
    exact mul_mem_one_submodule (star_mem_one_submodule (Submodule.mem_one.2 ⟨o a, rfl⟩)) (hgy a)
  have hNX : N ≤ toO (hS D) (Xsp (lf D F0)) := ?_
  · exact (sup_le_sup_left hNX Λ) hyB
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, rfl⟩
  show δ • F0.e a ∈ Submodule.span D.host.E (Set.range F0.e)
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end Lat

end Formalism.MainNotions.BridgeLemma₂

end
end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
open scoped nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

variable {D : D7} {u : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u) (Λ : LatV D)
  (hΛ : Submodule.IsLattice D.host.E Λ) (hu : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ) (hzΛ : F0.z ∈ Λ)
  (hprim : ∀ c : D.host.E, c • F0.z ∈ Lsub Λ (lf D F0) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c)
  (hT : Tu D u ≠ 0)

theorem z_mem_orth_isotropic : F0.z ∈ orth (hS D) (Xsp (lf D F0)) := a_orth_of_frame F0.e F0.z F0.z_orth


include he hΛ hu hzΛ hprim hT in
theorem exists_lattice_vector_inner_z_one : ∃ m ∈ Λ ⊓ toO (hS D) (orth (hS D) (Xsp (lf D F0))), (hS D).hT F0.z m = 1 := by
  have hfull : Submodule.IsFullLattice D.host.E Λ := by
    classical
    refine { toIsLattice := hΛ, span_eq_top := ?_ }
    rw [eq_top_iff]
    intro v _
    obtain ⟨S, hSgen⟩ := hΛ.fg
    obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset
      (nonZeroDivisors (𝓞 D.host.E)) (S.image (fun m => (hS D).hT m v))
    have hd0 : (algebraMap (𝓞 D.host.E) D.host.E d) ≠ 0 :=
      (IsFractionRing.injective (𝓞 D.host.E) D.host.E).ne (nonZeroDivisors.ne_zero hd)
    have hv : d • v ∈ Λ := by
      rw [← hu]
      apply (i_mem_dual _ _).2
      intro m hm
      rw [← hSgen] at hm
      induction hm using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha⟩ := hint ((hS D).hT x v) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
        apply Submodule.mem_one.2
        refine ⟨a, ?_⟩
        rw [← algebraMap_smul D.host.E, map_smul, smul_eq_mul]
        exact ha
      | zero => simp
      | add x y hx hy ihx ihy =>
        rw [map_add (f := _), LinearMap.add_apply]
        exact Submodule.add_mem _ ihx ihy
      | smul a x hx ih =>
        have ea : a • x = (algebraMap (𝓞 D.host.E) D.host.E a) • x := (algebraMap_smul D.host.E a x).symm
        rw [ea]
        rw [LinearMap.map_smulₛₗ₂]
        simp only [LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
        exact mul_mem_one_submodule (star_mem_one_submodule (Submodule.mem_one.2 ⟨a, rfl⟩)) ih
    have : v = (algebraMap (𝓞 D.host.E) D.host.E d)⁻¹ • (d • v) := by
      rw [← algebraMap_smul D.host.E d v, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hv)
  set M : LatV D := Λ ⊓ toO (hS D) (orth (hS D) (Xsp (lf D F0))) with hM
  set I : Ideal (𝓞 D.host.E) :=
    (M.map (((hS D).hT F0.z).restrictScalars (𝓞 D.host.E))).comap (Algebra.linearMap (𝓞 D.host.E) D.host.E) with hI
  have memI : ∀ o : 𝓞 D.host.E, o ∈ I ↔ ∃ m ∈ M, (hS D).hT F0.z m = algebraMap (𝓞 D.host.E) D.host.E o := by
    intro o
    rw [hI, Submodule.mem_comap, Submodule.mem_map]
    rfl
  have hzM : F0.z ∈ M := ⟨hzΛ, z_mem_orth_isotropic F0⟩
  have hI0 : I ≠ ⊥ := by
    intro h0
    have h1 : (-(Tu D u : 𝓞 D.host.E)) ∈ I := (memI _).2 ⟨F0.z, hzM, by rw [F0.z_norm]; simp⟩
    rw [h0, Ideal.mem_bot, neg_eq_zero] at h1
    exact hT (by exact_mod_cast h1)
  have hFI0 : (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hI0
  have hinv : (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹ ≤ 1 := by
    intro c hc
    rw [FractionalIdeal.mem_inv_iff hFI0] at hc
    have hy : star c • F0.z ∈ Λ ⊔ toO (hS D) (Xsp (lf D F0)) := by
      refine mem_sup_isotropic_of_dual_pairing F0 he Λ hfull hu _ fun m hm => ?_
      obtain ⟨i, hi⟩ := Submodule.mem_one.1 (i_int Λ hu hzΛ hm.1)
      have hiI : i ∈ I := (memI i).2 ⟨m, hm, hi.symm⟩
      obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1
        (hc _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨i, hiI, rfl⟩))
      rw [map_smul, smul_eq_mul, ← c_herm F0.z m, ← star_mul', ← hi, ← ho]
      exact star_mem_one_submodule (Submodule.mem_one.2 ⟨o, rfl⟩)
    obtain ⟨o, ho⟩ := hprim (star c) ((mem_Lsub_iff_sup_and_orth F0 Λ).2
      ⟨hy, (orth (hS D) (Xsp (lf D F0))).smul_mem _ (z_mem_orth_isotropic F0)⟩)
    obtain ⟨o', ho'⟩ := i_star_int o
    refine (FractionalIdeal.mem_one_iff _).2 ⟨o', ?_⟩
    rw [ho']
    show star (o : D.host.E) = c
    rw [ho, star_star]
  have h1 : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ I := by
    calc (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = I * (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹ :=
          (mul_inv_cancel₀ hFI0).symm
      _ ≤ I * 1 := by gcongr
      _ = I := mul_one _
  obtain ⟨x, hx, hx1⟩ := (FractionalIdeal.mem_coeIdeal _).1 (h1 (FractionalIdeal.one_mem_one _))
  obtain ⟨m, hm, e⟩ := (memI x).1 hx
  exact ⟨m, hm, by rw [e, hx1]⟩


include he hz hT in
theorem exists_decomp_orth_plus {v : (hS D).V} (hv : v ∈ orth (hS D) (Xsp (lf D F0))) (hvz : (hS D).hT F0.z v = 0) :
    ∃ w : (D.sp.X 0).V, ∃ ξ ∈ Xsp (lf D F0), v = D.sp.iXY 0 w + ξ := by
  have hW := (Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1
  have hv' : v ∈ orth (hS D) (Xplus (lf D F0)) := by
    have h : Xplus (lf D F0) ≤ LinearMap.ker ((hS D).hT.flip v) := by
      refine sup_le (fun x hx => c_mem_orth.1 hv x hx) (Submodule.span_le.2 ?_)
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hvz
    exact c_mem_orth.2 fun x hx => h hx
  rw [← hW] at hv'
  obtain ⟨a, ⟨w, rfl⟩, ξ, hξ, e⟩ := Submodule.mem_sup.1 hv'
  exact ⟨w, ξ, hξ, e.symm⟩


include he hz hT in
theorem inner_mem_one_of_mem_dual_orthLattice {m : (hS D).V} (hmΛ : m ∈ Λ) (hm : m ∈ orth (hS D) (Xsp (lf D F0)))
    (hmz : (hS D).hT F0.z m = 0) {w : (D.sp.X 0).V}
    (hw : w ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (L0X D Λ (lf D F0))) :
    (hS D).hT m (D.sp.iXY 0 w) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  obtain ⟨x, ξ, hξ, e⟩ := exists_decomp_orth_plus F0 he hz hT hm hmz
  have hx : x ∈ L0X D Λ (lf D F0) := by
    refine (mem_orthLattice_iff_image_mem_sup F0 he hz Λ).2 ?_
    have : D.sp.iXY 0 x = m + (-ξ) := by rw [e]; abel
    rw [this]
    exact Submodule.add_mem_sup hmΛ ((toO (hS D) (Xsp (lf D F0))).neg_mem hξ)
  rw [e, map_add (f := _), LinearMap.add_apply, orth_embedding_isometry, c_mem_orth.1 (orth_embedding_mem_orth_isotropic F0 he hz w) ξ hξ, add_zero]
  exact (i_mem_dual _ _).1 hw x hx


include he hz hΛ hu hzΛ hprim hT in
theorem dual_orthLattice_quotient_cyclic : ∃ w₁ ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (L0X D Λ (lf D F0)),
    (∀ w ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (L0X D Λ (lf D F0)), ∃ a : 𝓞 D.host.E, w + a • w₁ ∈ L0X D Λ (lf D F0)) ∧
    ∀ a : 𝓞 D.host.E, a • w₁ ∈ L0X D Λ (lf D F0) ↔ ((Tu D u : ℕ) : 𝓞 D.host.E) ∣ a := by
  obtain ⟨m₁, hm₁, hzm⟩ := exists_lattice_vector_inner_z_one F0 he Λ hΛ hu hzΛ hprim hT
  have hfull : Submodule.IsFullLattice D.host.E Λ := by
    classical
    refine { toIsLattice := hΛ, span_eq_top := ?_ }
    rw [eq_top_iff]
    intro v _
    obtain ⟨S, hSgen⟩ := hΛ.fg
    obtain ⟨⟨d, hd⟩, hint⟩ := IsLocalization.exist_integer_multiples_of_finset
      (nonZeroDivisors (𝓞 D.host.E)) (S.image (fun m => (hS D).hT m v))
    have hd0 : (algebraMap (𝓞 D.host.E) D.host.E d) ≠ 0 :=
      (IsFractionRing.injective (𝓞 D.host.E) D.host.E).ne (nonZeroDivisors.ne_zero hd)
    have hv : d • v ∈ Λ := by
      rw [← hu]
      apply (i_mem_dual _ _).2
      intro m hm
      rw [← hSgen] at hm
      induction hm using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨a, ha⟩ := hint ((hS D).hT x v) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
        apply Submodule.mem_one.2
        refine ⟨a, ?_⟩
        rw [← algebraMap_smul D.host.E, map_smul, smul_eq_mul]
        exact ha
      | zero => simp
      | add x y hx hy ihx ihy =>
        rw [map_add (f := _), LinearMap.add_apply]
        exact Submodule.add_mem _ ihx ihy
      | smul a x hx ih =>
        have ea : a • x = (algebraMap (𝓞 D.host.E) D.host.E a) • x := (algebraMap_smul D.host.E a x).symm
        rw [ea]
        rw [LinearMap.map_smulₛₗ₂]
        simp only [LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
        exact mul_mem_one_submodule (star_mem_one_submodule (Submodule.mem_one.2 ⟨a, rfl⟩)) ih
    have : v = (algebraMap (𝓞 D.host.E) D.host.E d)⁻¹ • (d • v) := by
      rw [← algebraMap_smul D.host.E d v, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hv)
  let t : D.host.E := (Tu D u : ℕ)
  have hTE : t ≠ 0 := Nat.cast_ne_zero.2 hT
  set B : LatV D := Λ ⊔ toO (hS D) (Xsp (lf D F0)) with hB
  have hstar : star t = t := by simp [t]
  have hzo := z_mem_orth_isotropic F0

  have hv1 : m₁ + t⁻¹ • F0.z ∈ orth (hS D) (Xsp (lf D F0)) :=
    (orth (hS D) (Xsp (lf D F0))).add_mem hm₁.2 ((orth (hS D) (Xsp (lf D F0))).smul_mem _ hzo)
  have hv2 : (hS D).hT F0.z (m₁ + t⁻¹ • F0.z) = 0 := by
    rw [map_add (f := _), map_smul, hzm, F0.z_norm, smul_eq_mul]
    field_simp
    ring
  obtain ⟨w₁, ξ₁, hξ₁, e₁⟩ := exists_decomp_orth_plus F0 he hz hT hv1 hv2
  have hK1 : D.sp.iXY 0 w₁ - t⁻¹ • F0.z ∈ B := by
    have : D.sp.iXY 0 w₁ - t⁻¹ • F0.z = m₁ + (-ξ₁) := by
      have : D.sp.iXY 0 w₁ = m₁ + t⁻¹ • F0.z - ξ₁ := by rw [e₁]; abel
      rw [this]; abel
    rw [this]
    exact Submodule.add_mem_sup hm₁.1 ((toO (hS D) (Xsp (lf D F0))).neg_mem hξ₁)
  have hmz : (hS D).hT m₁ F0.z = 1 := by rw [← c_herm, hzm, star_one]
  have hw₁ : w₁ ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (L0X D Λ (lf D F0)) := by
    refine (i_mem_dual _ _).2 fun x hx => ?_
    have e2 : D.sp.iXY 0 w₁ = m₁ + t⁻¹ • F0.z - ξ₁ := by rw [e₁]; abel
    rw [← orth_embedding_isometry, e2, map_sub, map_add (f := _), map_smul, c_symm0 (inner_z_orth_embedding_eq_zero F0 he hz x), smul_zero, add_zero,
      c_symm0 (c_mem_orth.1 (orth_embedding_mem_orth_isotropic F0 he hz x) ξ₁ hξ₁), sub_zero]
    obtain ⟨l, hl, ξ, hξ, e⟩ := Submodule.mem_sup.1 ((mem_orthLattice_iff_image_mem_sup F0 he hz Λ).1 hx)
    rw [← e, map_add (f := _), LinearMap.add_apply, c_mem_orth.1 hm₁.2 ξ hξ, add_zero]
    exact i_int Λ hu hl hm₁.1
  refine ⟨w₁, hw₁, ?_, ?_⟩
  · intro w hw

    have hα : t * (hS D).hT m₁ (D.sp.iXY 0 w) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
      have h1 : ((Tu D u : ℕ) : 𝓞 D.host.E) • m₁ + F0.z ∈ Λ := Λ.add_mem (Λ.smul_mem _ hm₁.1) hzΛ
      have h2 : ((Tu D u : ℕ) : 𝓞 D.host.E) • m₁ + F0.z ∈ orth (hS D) (Xsp (lf D F0)) :=
        (toO (hS D) (orth (hS D) (Xsp (lf D F0)))).add_mem
          ((toO (hS D) (orth (hS D) (Xsp (lf D F0)))).smul_mem _ hm₁.2) hzo
      have h3 : (hS D).hT F0.z (((Tu D u : ℕ) : 𝓞 D.host.E) • m₁ + F0.z) = 0 := by
        rw [map_add (f := _), ← algebraMap_smul D.host.E, map_smul, hzm, F0.z_norm]
        simp
      have h4 := inner_mem_one_of_mem_dual_orthLattice F0 he hz Λ hT h1 h2 h3 hw
      rw [map_add (f := _), LinearMap.add_apply, inner_z_orth_embedding_eq_zero F0 he hz w, add_zero, ← algebraMap_smul D.host.E,
        map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply] at h4
      have h5 : star (algebraMap (𝓞 D.host.E) D.host.E ((Tu D u : ℕ) : 𝓞 D.host.E)) = t := by
        rw [map_natCast]; exact hstar
      rwa [h5] at h4
    obtain ⟨α₀, hα₀⟩ := Submodule.mem_one.1 hα
    refine ⟨-α₀, (mem_orthLattice_iff_image_mem_sup F0 he hz Λ).2 ?_⟩
    have hy : D.sp.iXY 0 w + (algebraMap (𝓞 D.host.E) D.host.E (-α₀) * t⁻¹) • F0.z ∈ B := by
      refine mem_sup_isotropic_of_dual_pairing F0 he Λ hfull hu _ fun m hm => ?_
      obtain ⟨γ, hγ⟩ := Submodule.mem_one.1 (i_int Λ hu hzΛ hm.1)
      have h1 : m - γ • m₁ ∈ Λ := Λ.sub_mem hm.1 (Λ.smul_mem _ hm₁.1)
      have h2 : m - γ • m₁ ∈ orth (hS D) (Xsp (lf D F0)) :=
        (toO (hS D) (orth (hS D) (Xsp (lf D F0)))).sub_mem hm.2
          ((toO (hS D) (orth (hS D) (Xsp (lf D F0)))).smul_mem _ hm₁.2)
      have h3 : (hS D).hT F0.z (m - γ • m₁) = 0 := by
        rw [map_sub, ← algebraMap_smul D.host.E, map_smul, hzm, hγ]
        simp
      have h4 := inner_mem_one_of_mem_dual_orthLattice F0 he hz Λ hT h1 h2 h3 hw
      have h5 : (hS D).hT m (D.sp.iXY 0 w + (algebraMap (𝓞 D.host.E) D.host.E (-α₀) * t⁻¹) • F0.z) =
          (hS D).hT (m - γ • m₁) (D.sp.iXY 0 w) := by
        rw [map_add (f := _), map_smul, map_sub, LinearMap.sub_apply, ← algebraMap_smul D.host.E γ, map_smulₛₗ,
          LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, starRingEnd_apply, hγ, c_herm, map_neg, hα₀]
        field_simp
        ring
      rw [h5]
      exact h4
    have e3 : D.sp.iXY 0 (w + (-α₀) • w₁) =
        (D.sp.iXY 0 w + (algebraMap (𝓞 D.host.E) D.host.E (-α₀) * t⁻¹) • F0.z) +
          (-α₀) • (D.sp.iXY 0 w₁ - t⁻¹ • F0.z) := by
      rw [map_add (f := _), LinearMap.map_smul_of_tower, smul_sub, ← algebraMap_smul D.host.E (-α₀) (t⁻¹ • F0.z), smul_smul]
      abel
    rw [e3]
    exact B.add_mem hy (B.smul_mem _ hK1)
  · intro a
    constructor
    · intro ha
      have h1 := (mem_orthLattice_iff_image_mem_sup F0 he hz Λ).1 ha
      have h2 : (algebraMap (𝓞 D.host.E) D.host.E a * t⁻¹) • F0.z ∈ B := by
        have : (algebraMap (𝓞 D.host.E) D.host.E a * t⁻¹) • F0.z =
            D.sp.iXY 0 (a • w₁) - a • (D.sp.iXY 0 w₁ - t⁻¹ • F0.z) := by
          rw [LinearMap.map_smul_of_tower, smul_sub, ← algebraMap_smul D.host.E a (t⁻¹ • F0.z), smul_smul]
          abel
        rw [this]
        exact B.sub_mem h1 (B.smul_mem _ hK1)
      obtain ⟨o, ho⟩ := hprim _ ((mem_Lsub_iff_sup_and_orth F0 Λ).2
        ⟨h2, (orth (hS D) (Xsp (lf D F0))).smul_mem _ hzo⟩)
      refine ⟨o, ?_⟩
      apply RingOfIntegers.ext
      show algebraMap (𝓞 D.host.E) D.host.E a = algebraMap (𝓞 D.host.E) D.host.E (((Tu D u : ℕ) : 𝓞 D.host.E) * o)
      rw [map_mul, map_natCast]
      show algebraMap (𝓞 D.host.E) D.host.E a = t * (o : D.host.E)
      rw [ho]
      field_simp
    · rintro ⟨o, rfl⟩
      refine (mem_orthLattice_iff_image_mem_sup F0 he hz Λ).2 ?_
      have : D.sp.iXY 0 ((((Tu D u : ℕ) : 𝓞 D.host.E) * o) • w₁) =
          (((Tu D u : ℕ) : 𝓞 D.host.E) * o) • (D.sp.iXY 0 w₁ - t⁻¹ • F0.z) + o • F0.z := by
        rw [LinearMap.map_smul_of_tower, smul_sub,
          ← algebraMap_smul D.host.E (((Tu D u : ℕ) : 𝓞 D.host.E) * o) (t⁻¹ • F0.z), smul_smul, map_mul, map_natCast,
          ← algebraMap_smul D.host.E o F0.z]
        have : (t * algebraMap (𝓞 D.host.E) D.host.E o * t⁻¹) = algebraMap (𝓞 D.host.E) D.host.E o := by
          field_simp
        rw [this]
        abel
      rw [this]
      exact B.add_mem (B.smul_mem _ hK1) (Submodule.mem_sup_left (Λ.smul_mem _ hzΛ))

end Lat

end Formalism.MainNotions.BridgeLemma₂

end
end

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cyc

variable {D : D7} {V : Type} [AddCommGroup V] [Module D.host.E V] [Module (𝓞 D.host.E) V]
  [IsScalarTower (𝓞 D.host.E) D.host.E V] (h : V →ₗ⋆[D.host.E] V →ₗ[D.host.E] D.host.E)
  (M : Submodule (𝓞 D.host.E) V) (T : ℕ) (w₁ : V) (hw₁ : w₁ ∈ Formalism.HermitianLatticesTheory.dual h M)
  (hgen : ∀ w ∈ Formalism.HermitianLatticesTheory.dual h M, ∃ a : 𝓞 D.host.E, w + a • w₁ ∈ M)
  (hann : ∀ a : 𝓞 D.host.E, a • w₁ ∈ M ↔ ((T : ℕ) : 𝓞 D.host.E) ∣ a)


include hw₁ hgen in
theorem discriminant_one_generator : DiscGen h M 1 := by
  refine ⟨{Submodule.Quotient.mk ⟨w₁, hw₁⟩}, by simp, ?_⟩
  rw [eq_top_iff, Finset.coe_singleton]
  intro q _
  obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.mkQ_surjective _ q
  obtain ⟨a, ha⟩ := hgen w hw
  refine Submodule.mem_span_singleton.2 ⟨-a, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap]
  show (-a) • w₁ - w ∈ M
  have e : (-a) • w₁ - w = -(w + a • w₁) := by rw [neg_smul]; abel
  rw [e]
  exact M.neg_mem ha


include hw₁ hgen hann in
theorem corank_one_mod_prime_over (p : Ideal (𝓞 D.host.F)) (hp : p.IsMaximal) (hTp : ((T : ℕ) : 𝓞 D.host.F) ∈ p) :
    eP h M p = 1 := by
  set P : Ideal (𝓞 D.host.E) := pE D.host.F D.host.E p with hP
  set Md := Formalism.HermitianLatticesTheory.dual h M with hMd
  set K : Submodule (𝓞 D.host.E) Md := (M ⊔ P • Md).comap Md.subtype with hK
  have hTP : ((T : ℕ) : 𝓞 D.host.E) ∈ P := by
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) hTp
    rw [map_natCast] at this
    exact this
  have hstep : ∀ n ∈ P • Md, ∃ b ∈ P, n - b • w₁ ∈ M := by
    intro n hn
    refine Submodule.smul_induction_on hn ?_ ?_
    · intro r hr w hw
      obtain ⟨c, hc⟩ := hgen w hw
      refine ⟨-(r * c), P.neg_mem (P.mul_mem_right _ hr), ?_⟩
      have e : r • w - (-(r * c)) • w₁ = r • (w + c • w₁) := by
        rw [neg_smul, sub_neg_eq_add, smul_add, mul_smul]
      rw [e]
      exact M.smul_mem _ hc
    · rintro x y ⟨b, hb, hx⟩ ⟨b', hb', hy⟩
      refine ⟨b + b', P.add_mem hb hb', ?_⟩
      have e : x + y - (b + b') • w₁ = (x - b • w₁) + (y - b' • w₁) := by rw [add_smul]; abel
      rw [e]
      exact M.add_mem hx hy
  set φ : 𝓞 D.host.E →ₗ[𝓞 D.host.E] (Md ⧸ K) :=
    LinearMap.toSpanSingleton (𝓞 D.host.E) (Md ⧸ K) (Submodule.Quotient.mk ⟨w₁, hw₁⟩) with hφ
  have hφa : ∀ a, φ a = Submodule.Quotient.mk (a • (⟨w₁, hw₁⟩ : Md)) := fun a => by
    rw [hφ, LinearMap.toSpanSingleton_apply, Submodule.Quotient.mk_smul]
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.mkQ_surjective _ q
    obtain ⟨a, ha⟩ := hgen w hw
    refine ⟨-a, ?_⟩
    rw [hφa, Submodule.mkQ_apply, Submodule.Quotient.eq, hK, Submodule.mem_comap]
    show (-a) • w₁ - w ∈ M ⊔ P • Md
    have e : (-a) • w₁ - w = -(w + a • w₁) := by rw [neg_smul]; abel
    rw [e]
    exact Submodule.mem_sup_left (M.neg_mem ha)
  have hker : LinearMap.ker φ = P := by
    ext a
    rw [LinearMap.mem_ker, hφa, Submodule.Quotient.mk_eq_zero, hK, Submodule.mem_comap]
    show a • w₁ ∈ M ⊔ P • Md ↔ a ∈ P
    constructor
    · intro ha
      obtain ⟨m, hm, n, hn, e⟩ := Submodule.mem_sup.1 ha
      obtain ⟨b, hb, hnb⟩ := hstep n hn
      have h1 : (a - b) • w₁ ∈ M := by
        have : (a - b) • w₁ = m + (n - b • w₁) := by rw [sub_smul, ← e]; abel
        rw [this]
        exact M.add_mem hm hnb
      obtain ⟨o, ho⟩ := (hann _).1 h1
      have : a = ((T : ℕ) : 𝓞 D.host.E) * o + b := by rw [← ho]; ring
      rw [this]
      exact P.add_mem (P.mul_mem_right _ hTP) hb
    · intro ha
      exact Submodule.mem_sup_right (Submodule.smul_mem_smul ha hw₁)
  have hcard : Nat.card (Md ⧸ K) = Ideal.absNorm p ^ 2 := by
    rw [← Nat.card_congr (φ.quotKerEquivOfSurjective hsurj).toEquiv,
      Nat.card_congr (Submodule.quotEquivOfEq _ _ hker).toEquiv, ← Formalism.MainNotions.BridgeLemma.absNorm_pE]
    exact (Ideal.absNorm_eq_natCard P).symm
  have hq := Formalism.MainNotions.BridgeLemma.absNorm_ge_two p hp
  show Nat.log (Ideal.absNorm p ^ 2) (Nat.card (Md ⧸ K)) = 1
  rw [hcard]
  have := Nat.log_pow (b := Ideal.absNorm p ^ 2) (by nlinarith) 1
  rwa [pow_one] at this

end Cyc

theorem orthLattice_structure_of_det (D : D7) (u : D.what₂.Word)
    (hdet : ForPrimeFlagLattice D u fun F0 Λ =>
      latDetH (D.sp.X 0).hT (L0X D Λ (lf D F0)) = ((Tu D u ^ D.R.f : ℕ) : ℝ)) : BaseLatticeStructure D u := by
  intro hTp h3 hsp F0 he hz Λ hrow
  obtain ⟨hΛ, hu, hlift, hconv⟩ := hrow.2.1
  obtain ⟨w₁, hw₁, hgen, hann⟩ := dual_orthLattice_quotient_cyclic F0 he hz Λ hΛ hu hlift.1 hconv.2 hTp.ne_zero
  exact ⟨orthLattice_isLattice F0 he hz Λ hΛ hu, orthLattice_isIntegral_of_unimodular Λ (lf D F0) hu, hdet hTp h3 hsp F0 he hz Λ hrow,
    discriminant_one_generator _ _ w₁ hw₁ hgen, fun p hp hTpp => corank_one_mod_prime_over _ _ (Tu D u) w₁ hw₁ hgen hann p hp hTpp⟩

end Formalism.MainNotions.BridgeLemma₂

end
