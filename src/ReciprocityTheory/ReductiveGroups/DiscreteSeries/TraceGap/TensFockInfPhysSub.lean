module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.AdPhysApplySingle
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.DetOneSubEqSumMinors

@[expose] public section

section -- merged from ReciprocityTheory.ReductiveGroups.DiscreteSeries.TraceGap.TraceEqTraceRestrictOfRangeLe
noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

section LA

variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ Y]

theorem trace_eq_trace_restrict_of_range_le (f : Y →ₗ[ℂ] Y) (Y0 : Submodule ℂ Y)
    (h : LinearMap.range f ≤ Y0) :
    LinearMap.trace ℂ Y f =
      LinearMap.trace ℂ Y0 (f.restrict (fun x _ => h (LinearMap.mem_range_self f x))) := by
  have hm : ∀ x, f x ∈ Y0 := fun x => h (LinearMap.mem_range_self f x)
  calc LinearMap.trace ℂ Y f = LinearMap.trace ℂ Y (Y0.subtype ∘ₗ LinearMap.codRestrict Y0 f hm) := by
        rw [LinearMap.subtype_comp_codRestrict]
    _ = LinearMap.trace ℂ Y0 (LinearMap.codRestrict Y0 f hm ∘ₗ Y0.subtype) :=
        LinearMap.trace_comp_comm' _ _
    _ = _ := by
        congr 1

theorem trace_eq_add_of_isCompl (f : Y →ₗ[ℂ] Y) {K R : Submodule ℂ Y} (hKR : IsCompl K R)
    (hK : ∀ x ∈ K, f x ∈ K) (hR : ∀ x ∈ R, f x ∈ R) :
    LinearMap.trace ℂ Y f = LinearMap.trace ℂ K (f.restrict hK) + LinearMap.trace ℂ R (f.restrict hR) := by
  have hrK : LinearMap.range (f ∘ₗ K.projection R hKR) ≤ K := by
    rintro _ ⟨x, rfl⟩
    exact hK _ (Submodule.projection_apply_mem _ _)
  have hrR : LinearMap.range (f ∘ₗ R.projection K hKR.symm) ≤ R := by
    rintro _ ⟨x, rfl⟩
    exact hR _ (Submodule.projection_apply_mem _ _)
  have h1 : LinearMap.trace ℂ Y f = LinearMap.trace ℂ Y (f ∘ₗ K.projection R hKR) +
      LinearMap.trace ℂ Y (f ∘ₗ R.projection K hKR.symm) := by
    rw [← map_add (f := _), ← LinearMap.comp_add, Submodule.projection_add_projection_eq_id, LinearMap.comp_id]
  rw [h1, trace_eq_trace_restrict_of_range_le _ K hrK, trace_eq_trace_restrict_of_range_le _ R hrR]
  congr 2
  · ext x
    simp
  · ext x
    simp

end LA

section S4

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]

theorem str_eq_str_ker (Dl Γ B : Y →ₗ[ℂ] Y) (hD : ∀ x y, inner ℂ (Dl x) y = inner ℂ x (Dl y))
    (hΓD : ∀ x, Γ (Dl x) = -Dl (Γ x)) (hBD : ∀ x, B (Dl x) = Dl (B x)) :
    ∃ hk : ∀ x ∈ LinearMap.ker Dl, (Γ ∘ₗ B) x ∈ LinearMap.ker Dl,
      LinearMap.trace ℂ Y (Γ ∘ₗ B) = LinearMap.trace ℂ (LinearMap.ker Dl) ((Γ ∘ₗ B).restrict hk) := by
  have hDΓ : ∀ y, Dl (Γ y) = -Γ (Dl y) := fun y => by rw [hΓD, neg_neg]
  have hk : ∀ x ∈ LinearMap.ker Dl, (Γ ∘ₗ B) x ∈ LinearMap.ker Dl := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [LinearMap.comp_apply, hDΓ, ← hBD, hx, map_zero, map_zero, neg_zero]
  refine ⟨hk, ?_⟩
  have hsym : Dl.IsSymmetric := hD
  have hkr : IsCompl (LinearMap.ker Dl) (LinearMap.range Dl) := by
    have := (Submodule.isCompl_orthogonal (LinearMap.range Dl)).symm
    rwa [hsym.orthogonal_range] at this
  have hV : ∀ x ∈ LinearMap.range Dl, (Γ ∘ₗ B) x ∈ LinearMap.range Dl := by
    rintro _ ⟨y, rfl⟩
    refine ⟨-Γ (B y), ?_⟩
    rw [map_neg, hDΓ, neg_neg, LinearMap.comp_apply, hBD]
  rw [trace_eq_add_of_isCompl _ hkr hk hV]
  suffices h0 : LinearMap.trace ℂ (LinearMap.range Dl) ((Γ ∘ₗ B).restrict hV) = 0 by
    rw [h0, add_zero]
  have hDV : ∀ x ∈ LinearMap.range Dl, Dl x ∈ LinearMap.range Dl := fun x _ => LinearMap.mem_range_self Dl x
  have hΓV : ∀ x ∈ LinearMap.range Dl, Γ x ∈ LinearMap.range Dl := by
    rintro _ ⟨y, rfl⟩
    exact ⟨-Γ y, by rw [map_neg, hDΓ, neg_neg]⟩
  have hBV : ∀ x ∈ LinearMap.range Dl, B x ∈ LinearMap.range Dl := by
    rintro _ ⟨y, rfl⟩
    exact ⟨B y, (hBD y).symm⟩
  have hinj : Function.Injective (Dl.restrict hDV) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have hv' : (v : Y) ∈ LinearMap.ker Dl := by
      rw [LinearMap.mem_ker]
      have := congrArg Subtype.val (LinearMap.mem_ker.1 hv)
      simpa using this
    exact Subtype.ext (Submodule.disjoint_def.1 hkr.disjoint _ hv' v.2)
  set e := LinearEquiv.ofInjectiveEndo (Dl.restrict hDV) hinj
  have hsplit : (Γ ∘ₗ B).restrict hV = Γ.restrict hΓV ∘ₗ B.restrict hBV := by
    ext v
    rfl
  have hconj : e.conj ((Γ ∘ₗ B).restrict hV) = -((Γ ∘ₗ B).restrict hV) := by
    ext v
    obtain ⟨w, rfl⟩ : ∃ w, v = e w := ⟨e.symm v, (e.apply_symm_apply v).symm⟩
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.neg_apply]
    show ((Dl.restrict hDV) ((Γ ∘ₗ B).restrict hV w) : Y) = -(((Γ ∘ₗ B).restrict hV (Dl.restrict hDV w)) : Y)
    simp only [LinearMap.restrict_apply, LinearMap.comp_apply]
    rw [hDΓ, ← hBD]
  have ht := LinearMap.trace_conj' ((Γ ∘ₗ B).restrict hV) e
  rw [hconj, map_neg] at ht
  linear_combination -ht / 2

end S4

end ReciprocityTheory.ChartRestriction.DS.TRGap
end
end

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.ChartRestriction.DS.TRGap

variable {n : ℕ} {ε : Fin n → Bool}

section Supp

variable {N : Type*} [AddCommGroup N] [Module ℂ N]

theorem tco_physSub_zero {y : TensorProduct ℂ N (Fock n)} (hy : y ∈ physicalSubspace ε) {s : Finset (Fin (n * n))}
    {m : Fin (n * n)} (hm : m ∈ s) (hnp : ¬IsPhys ε (finProdFinEquiv.symm m)) :
    tcoef ((fockBasis n).coord s) y = 0 := by
  set x := finProdFinEquiv.symm m with hxdef
  have h0 : cmT (N := N) x.1 x.2 y = 0 := (mem_physicalSubspace_iff ε y).1 hy x.1 x.2 hnp
  have h1 : tcoef ((fockBasis n).coord s) (cpT (N := N) x.1 x.2 (cmT x.1 x.2 y)) = 0 := by
    rw [h0, map_zero, map_zero]
  change tcoef ((fockBasis n).coord s) (LinearMap.lTensor N (cpFock x.1 x.2)
    (LinearMap.lTensor N (cmFock x.1 x.2) y)) = 0 at h1
  have hxs : finProdFinEquiv x ∈ s := by
    rw [hxdef, Equiv.apply_symm_apply]
    exact hm
  rwa [tcoef_lTensor, tcoef_lTensor, LinearMap.comp_assoc, gc_coord_num, ite_eq_left hxs, one_smul] at h1

theorem tensFock_inf_physSub (L : Submodule ℂ N) :
    tensFock (n := n) L ⊓ physicalSubspace ε = LinearMap.range (TensorProduct.map L.subtype (physFock ε).subtype) := by
  apply le_antisymm
  · rintro y ⟨hyT, hyP⟩
    have hmem : ∀ s, tcoef ((fockBasis n).coord s) y ∈ L := fun s => tcoef_mem hyT _
    refine ⟨∑ S : LfIdx ε, (⟨tcoef ((fockBasis n).coord S.1) y, hmem S.1⟩ : L) ⊗ₜ
      (⟨fockBasis n S.1, physWedge_mem S⟩ : physFock ε), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [TensorProduct.map_tmul, Submodule.coe_subtype]
    symm
    calc y = ∑ s, tcoef ((fockBasis n).coord s) y ⊗ₜ fockBasis n s := tcoef_expand y
      _ = ∑ s ∈ univ.filter (fun s => s ⊆ lfPhysModes ε),
          tcoef ((fockBasis n).coord s) y ⊗ₜ fockBasis n s := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun s _ => ?_
        split_ifs with h
        · rfl
        · obtain ⟨m, hm, hmp⟩ := Finset.not_subset.1 h
          have hnp : ¬IsPhys ε (finProdFinEquiv.symm m) := by
            simpa [lfPhysModes, IsPhys] using hmp
          rw [tco_physSub_zero hyP hm hnp, TensorProduct.zero_tmul]
      _ = ∑ S : LfIdx ε, tcoef ((fockBasis n).coord S.1) y ⊗ₜ fockBasis n S.1 :=
        Finset.sum_subtype _ (fun s => by simp) _
  · rintro _ ⟨x, rfl⟩
    refine ⟨?_, ?_⟩
    · refine ⟨TensorProduct.map LinearMap.id (physFock ε).subtype x, ?_⟩
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp]
      rfl
    · show _ ∈ physicalSubspace ε
      rw [mem_physicalSubspace_iff]
      intro j b hjb
      induction x using TensorProduct.inductionOn with
      | tmul l f =>
        have hf := f.2
        simp only [physFock, Submodule.mem_iInf, LinearMap.mem_ker] at hf
        simp only [TensorProduct.map_tmul, cmT, LinearMap.id_apply, Submodule.coe_subtype, hf j b hjb,
          TensorProduct.tmul_zero]
      | add x x' hx hx' => rw [map_add (f := _), map_add (f := _), hx, hx', add_zero]

end Supp

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}

theorem str_tensFock_physSub (hD : IsDerivedOn ε σ D E) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε)
    {L : Submodule ℂ D} [FiniteDimensional ℂ L] (hL : ∀ x ∈ L, sigD hD hk x ∈ L)
    (hY0 : ∀ y ∈ tensFock (n := n) L ⊓ physicalSubspace ε, (gradT ∘ₗ wK hD hk) y ∈ tensFock L ⊓ physicalSubspace ε) :
    LinearMap.trace ℂ ↥(tensFock (n := n) L ⊓ physicalSubspace (N := D) ε)
        ((gradT ∘ₗ wK hD hk).restrict hY0) =
      LinearMap.trace ℂ L ((sigD hD hk).restrict hL) * physDet ε k := by
  set Φ := TensorProduct.map L.subtype (physFock ε).subtype with hΦ
  have hinj : Function.Injective Φ :=
    TensorProduct.map_injective_of_flat_flat _ _ L.injective_subtype (physFock ε).injective_subtype
  let e : TensorProduct ℂ L (physFock ε) ≃ₗ[ℂ] ↥(tensFock (n := n) L ⊓ physicalSubspace (N := D) ε) :=
    (LinearEquiv.ofInjective Φ hinj).trans (LinearEquiv.ofEq _ _ (tensFock_inf_physSub L).symm)
  have he : ∀ x, ((e x : ↥(tensFock (n := n) L ⊓ physicalSubspace (N := D) ε)) : TensorProduct ℂ D (Fock n)) = Φ x :=
    fun x => rfl
  set sL := (sigD hD hk).restrict hL
  set fP := (CliffordAlgebra.involute.toLinearMap ∘ₗ (ff ε k).toLinearMap).restrict (involute_ff_mapsTo k)
  have hsq : ∀ x, (gradT ∘ₗ wK hD hk) (Φ x) = Φ (TensorProduct.map sL fP x) := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul l f => rfl
    | add x x' hx hx' => rw [map_add (f := _), map_add (f := _), hx, hx', map_add (f := _), map_add (f := _)]
  have hconj : (gradT ∘ₗ wK hD hk).restrict hY0 = e.conj (TensorProduct.map sL fP) := by
    apply LinearMap.ext
    intro y
    apply Subtype.ext
    rw [LinearEquiv.conj_apply_apply, he, LinearMap.restrict_apply]
    show (gradT ∘ₗ wK hD hk) (y : TensorProduct ℂ D (Fock n)) = _
    rw [← hsq, ← he, LinearEquiv.apply_symm_apply]
  have : FiniteDimensional ℂ (Fock n) := Module.Finite.of_basis (fockBasis n)
  rw [hconj, LinearMap.trace_conj', LinearMap.trace_tensorProduct', ← strPhys_eq_trace, strPhys_eq_physDet]

end ReciprocityTheory.ChartRestriction.DS.TRGap
