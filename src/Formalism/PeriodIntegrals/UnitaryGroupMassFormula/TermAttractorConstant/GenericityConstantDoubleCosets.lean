module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.SpanFrameLtSucc

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.GeneratorMemLocalLatticeBackward
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.GpMfixMapLoc
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.GpMfixLeU
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.GpLocPSubE
section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.LocPBLatTransport
noncomputable section

open scoped Classical

namespace PI.TermAttrConst.UnitaryGroupMassFormula

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.DCRelEquiv PI.DCRelEquiv.UnitaryGroupMassFormula

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

abbrev fO (n : S.V ≃ₗ[E] S.V) : S.V →ₗ[𝓞 E] S.V := (n : S.V →ₗ[E] S.V).restrictScalars (𝓞 E)

theorem fO_apply (n : S.V ≃ₗ[E] S.V) (v : S.V) : fO n v = n v := rfl

theorem gmap_eq_map (n : S.V ≃ₗ[E] S.V) (M : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap n M = M.map (fO n) := rfl

theorem mem_gmap_iff (n : S.V ≃ₗ[E] S.V) (M : Submodule (𝓞 E) S.V) (v : S.V) :
    v ∈ Formalism.HermitianLatticesTheory.gmap n M ↔ n.symm v ∈ M := by
  rw [gmap_eq_map]
  constructor
  · rintro ⟨w, hw, rfl⟩
    simpa [fO_apply] using hw
  · intro hv
    exact ⟨n.symm v, hv, by simp [fO_apply]⟩

theorem mem_localization_iff (P : Ideal (𝓞 E)) [P.IsPrime] (M : Submodule (𝓞 E) S.V) (v : S.V) :
    v ∈ Formalism.HermitianLatticesTheory.localization₂ P M ↔ ∃ s ∈ P.primeCompl, s • v ∈ M := Iff.rfl

theorem locP_gmap (P : Ideal (𝓞 E)) [P.IsPrime] (n : S.V ≃ₗ[E] S.V) (M : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.localization₂ P (Formalism.HermitianLatticesTheory.gmap n M) = Formalism.HermitianLatticesTheory.gmap n (Formalism.HermitianLatticesTheory.localization₂ P M) := by
  ext v
  rw [mem_localization_iff, mem_gmap_iff, mem_localization_iff]
  constructor
  · rintro ⟨s, hs, hsv⟩
    refine ⟨s, hs, ?_⟩
    rw [mem_gmap_iff] at hsv
    have e : n.symm (s • v) = s • n.symm v := (fO n.symm).map_smul s v
    rwa [e] at hsv
  · rintro ⟨s, hs, hsv⟩
    refine ⟨s, hs, ?_⟩
    rw [mem_gmap_iff]
    have e : n.symm (s • v) = s • n.symm v := (fO n.symm).map_smul s v
    rwa [e]

theorem sup_span_swap {M : Submodule (𝓞 E) S.V} {a b : S.V} (h : a - b ∈ M) :
    M ⊔ Submodule.span (𝓞 E) {a} = M ⊔ Submodule.span (𝓞 E) {b} := by
  apply le_antisymm
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_singleton_le_iff_mem]
    have e : a = (a - b) + b := by abel
    rw [e]
    exact Submodule.add_mem _ (Submodule.mem_sup_left h)
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self b))
  · refine sup_le le_sup_left ?_
    rw [Submodule.span_singleton_le_iff_mem]
    have e : b = a - (a - b) := by abel
    rw [e]
    exact Submodule.sub_mem _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self a))
      (Submodule.mem_sup_left h)

theorem gmap_span_singleton (n : S.V ≃ₗ[E] S.V) (v : S.V) :
    Formalism.HermitianLatticesTheory.gmap n (Submodule.span (𝓞 E) {v}) = Submodule.span (𝓞 E) {n v} := by
  rw [gmap_eq_map, Submodule.map_span, Set.image_singleton, fO_apply]

theorem gmap_sup (n : S.V ≃ₗ[E] S.V) (A B : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.gmap n (A ⊔ B) = Formalism.HermitianLatticesTheory.gmap n A ⊔ Formalism.HermitianLatticesTheory.gmap n B := by
  rw [gmap_eq_map, gmap_eq_map, gmap_eq_map, Submodule.map_sup]

variable {Λ : Submodule (𝓞 E) S.V}

theorem autLam_maps {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {v : S.V} (hv : v ∈ Λ) : n v ∈ Λ := by
  have h : n v ∈ Formalism.HermitianLatticesTheory.gmap n Λ := (mem_gmap_iff n Λ (n v)).2 (by simpa using hv)
  rwa [hn.2] at h

theorem autLam_symm_maps {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {v : S.V} (hv : v ∈ Λ) :
    n.symm v ∈ Λ := by
  rw [← hn.2] at hv
  exact (mem_gmap_iff n Λ v).1 hv

theorem mem_XLam {F : LFlag S r T} {v : S.V} : v ∈ XLam Λ F ↔ v ∈ Λ ∧ v ∈ Xsp F := by
  unfold XLam
  rw [Submodule.mem_inf, Submodule.restrictScalars_mem]

theorem gmap_XLam_self {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) :
    Formalism.HermitianLatticesTheory.gmap n (XLam Λ F) = XLam Λ F := by
  have hni : n.symm ∈ NLam Λ F := nlam_inv hn
  ext v
  rw [mem_gmap_iff, mem_XLam, mem_XLam]
  constructor
  · rintro ⟨h1, h2⟩
    have a1 := autLam_maps hn.1 h1
    have a2 := nlam_maps_X hn _ h2
    simp only [LinearEquiv.apply_symm_apply] at a1 a2
    exact ⟨a1, a2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨autLam_symm_maps hn.1 h1, nlam_maps_X hni _ h2⟩

theorem nlam_z_sub {F : LFlag S r T} {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) (hz : F.fl.z ∈ Λ) :
    n F.fl.z - F.fl.z ∈ XLam Λ F :=
  mem_XLam.2 ⟨Submodule.sub_mem _ (autLam_maps hn.1 hz) hz, hn.2.2 _ (z_mem_orth F)⟩

theorem XLam_transport {F₁ F₂ : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V} {T₀ : E} {F : LFlag S r T₀}
    (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F₁) (hfr : ∀ a, frame F₂ a = n (m (frame F₁ a))) :
    XLam Λ F₂ = Formalism.HermitianLatticesTheory.gmap n (XLam Λ F₁) := by
  let g : S.V ≃ₗ[E] S.V := m.trans n
  have hfr' : ∀ a, frame F₂ a = g (frame F₁ a) := fun a => hfr a
  have hg : IsAutLam S Λ g := autLam_mul hn.1 hm.1
  have h1 : XLam Λ F₂ = Formalism.HermitianLatticesTheory.gmap g (XLam Λ F₁) := by
    ext v
    rw [mem_gmap_iff, mem_XLam, mem_XLam, Xsp_mem_transport hfr' v]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨autLam_symm_maps hg h1, h2⟩
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      have := autLam_maps hg h1
      simpa using this
  rw [h1]
  show Formalism.HermitianLatticesTheory.gmap (n * m) (XLam Λ F₁) = _
  rw [gmap_mul', gmap_XLam_self hm]

theorem UU_transport {F : LFlag S r T} {F₁ F₂ : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V}
    (hF : IsLift Λ F) (h₁ : IsLift Λ F₁) (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F₁)
    (hfr : ∀ a, frame F₂ a = n (m (frame F₁ a))) (hzt : F₂.zt = n (m F₁.zt)) :
    UU Λ F F₂ = Formalism.HermitianLatticesTheory.gmap n (UU Λ F F₁) := by
  unfold UU
  rw [gmap_sup, gmap_sup, gmap_sup, gmap_span_singleton, gmap_span_singleton, gmap_XLam_self hn,
    ← XLam_transport hn hm hfr, sup_assoc, sup_assoc (XLam Λ F ⊔ _)]
  have e1 : XLam Λ F ⊔ Submodule.span (𝓞 E) {F.zt} = XLam Λ F ⊔ Submodule.span (𝓞 E) {n F.zt} := by
    refine sup_span_swap ?_
    rw [hF.2]
    have := Submodule.neg_mem _ (nlam_z_sub hn hF.1)
    rwa [neg_sub] at this
  have e2 : XLam Λ F₂ ⊔ Submodule.span (𝓞 E) {F₂.zt} = XLam Λ F₂ ⊔ Submodule.span (𝓞 E) {n F₁.zt} := by
    refine sup_span_swap ?_
    rw [hzt, ← map_sub, XLam_transport hn hm hfr, mem_gmap_iff, LinearEquiv.symm_apply_apply, h₁.2]
    exact nlam_z_sub hm h₁.1
  rw [e1, e2]

theorem spanE_gmap (n : S.V ≃ₗ[E] S.V) (M : Submodule (𝓞 E) S.V) :
    spanE S (Formalism.HermitianLatticesTheory.gmap n M) = (spanE S M).map (n : S.V →ₗ[E] S.V) := by
  unfold spanE
  rw [gmap_eq_map, Submodule.map_coe]
  have e : ⇑(fO n) = ⇑(n : S.V →ₗ[E] S.V) := rfl
  rw [e, Submodule.span_image]

theorem BLat_transport {F : LFlag S r T} {F₁ F₂ : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V}
    (hF : IsLift Λ F) (h₁ : IsLift Λ F₁) (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F₁)
    (hfr : ∀ a, frame F₂ a = n (m (frame F₁ a))) (hzt : F₂.zt = n (m F₁.zt)) :
    BLat Λ F F₂ = Formalism.HermitianLatticesTheory.gmap n (BLat Λ F F₁) := by
  unfold BLat UUE
  rw [UU_transport hF h₁ hn hm hfr hzt, spanE_gmap]
  ext v
  rw [mem_gmap_iff, Submodule.mem_inf, Submodule.mem_inf, Submodule.restrictScalars_mem,
    Submodule.restrictScalars_mem, Submodule.mem_map_equiv]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨autLam_symm_maps hn.1 h1, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    have := autLam_maps hn.1 h1
    simpa using this

theorem locP_BLat_transport {F : LFlag S r T} {F₁ F₂ : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V}
    (hF : IsLift Λ F) (h₁ : IsLift Λ F₁) (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ F₁)
    (hfr : ∀ a, frame F₂ a = n (m (frame F₁ a))) (hzt : F₂.zt = n (m F₁.zt))
    (P : Ideal (𝓞 E)) [P.IsPrime] :
    Formalism.HermitianLatticesTheory.localization₂ P (BLat Λ F F₂) = Formalism.HermitianLatticesTheory.gmap n (Formalism.HermitianLatticesTheory.localization₂ P (BLat Λ F F₁)) := by
  rw [BLat_transport hF h₁ hn hm hfr hzt, locP_gmap]

end Gen

end PI.TermAttrConst.UnitaryGroupMassFormula
end
end

noncomputable section

open scoped Classical

namespace PI.TermAttrConst.UnitaryGroupMassFormula

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.DCRelEquiv PI.DCRelEquiv.UnitaryGroupMassFormula

section GP

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ}

theorem gp_osmul (o : 𝓞 E) (v : S.V) : o • v = (algebraMap (𝓞 E) E o) • v :=
  (algebraMap_smul E o v).symm

theorem gp_smul_comm (o : 𝓞 E) (c : E) (v : S.V) : o • (c • v) = c • (o • v) := by
  rw [gp_osmul, gp_osmul, smul_smul, smul_smul, mul_comm]

theorem gp_map_osmul (n : S.V ≃ₗ[E] S.V) (o : 𝓞 E) (v : S.V) : n (o • v) = o • n v := by
  rw [gp_osmul, gp_osmul, map_smul]

variable (p : Ideal (𝓞 E)) [p.IsPrime]

theorem gp_ne_zero {s : 𝓞 E} (hs : s ∈ p.primeCompl) : algebraMap (𝓞 E) E s ≠ 0 := by
  intro h
  apply hs
  have h0 : s = 0 := FaithfulSMul.algebraMap_injective (𝓞 E) E (h.trans (map_zero _).symm)
  rw [h0]
  exact p.zero_mem

theorem gp_le_locP (L : Submodule (𝓞 E) S.V) : L ≤ Formalism.HermitianLatticesTheory.localization₂ p L :=
  fun v hv => (mem_localization_iff p L v).2 ⟨1, p.primeCompl.one_mem, by simpa using hv⟩

theorem locP_mono {L L' : Submodule (𝓞 E) S.V} (h : L ≤ L') :
    Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p L' := by
  intro v hv
  obtain ⟨s, hs, hv⟩ := (mem_localization_iff p L v).1 hv
  exact (mem_localization_iff p L' v).2 ⟨s, hs, h hv⟩

theorem locP_locP_le (L : Submodule (𝓞 E) S.V) :
    Formalism.HermitianLatticesTheory.localization₂ p (Formalism.HermitianLatticesTheory.localization₂ p L) ≤ Formalism.HermitianLatticesTheory.localization₂ p L := by
  intro v hv
  obtain ⟨s, hs, hv⟩ := (mem_localization_iff p _ v).1 hv
  obtain ⟨t, ht, hv⟩ := (mem_localization_iff p L _).1 hv
  exact (mem_localization_iff p L v).2 ⟨t * s, p.primeCompl.mul_mem ht hs, by rw [mul_smul]; exact hv⟩

theorem locP_le {L L' : Submodule (𝓞 E) S.V} (h : L ≤ Formalism.HermitianLatticesTheory.localization₂ p L') :
    Formalism.HermitianLatticesTheory.localization₂ p L ≤ Formalism.HermitianLatticesTheory.localization₂ p L' :=
  (locP_mono p h).trans (locP_locP_le p L')

theorem gp_of_smul {L : Submodule (𝓞 E) S.V} {s : 𝓞 E} (hs : s ∈ p.primeCompl) {v : S.V}
    (h : s • v ∈ Formalism.HermitianLatticesTheory.localization₂ p L) : v ∈ Formalism.HermitianLatticesTheory.localization₂ p L :=
  locP_locP_le p L ((mem_localization_iff p _ v).2 ⟨s, hs, h⟩)

theorem gp_locP_sub_E {L : Submodule (𝓞 E) S.V} {U : Submodule E S.V} (hL : ∀ w ∈ L, w ∈ U) {v : S.V}
    (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ p L) : v ∈ U := by
  obtain ⟨s, hs, hv⟩ := (mem_localization_iff p L v).1 hv
  have h1 := hL _ hv
  rw [gp_osmul] at h1
  have h2 := U.smul_mem (algebraMap (𝓞 E) E s)⁻¹ h1
  rwa [smul_smul, inv_mul_cancel₀ (gp_ne_zero p hs), one_smul] at h2

def gpK (M N : Submodule (𝓞 E) S.V) (c : E) : Submodule (𝓞 E) S.V where
  carrier := {k | ∃ μ ∈ Formalism.HermitianLatticesTheory.localization₂ p M, ∃ ν ∈ Formalism.HermitianLatticesTheory.localization₂ p N, k = μ + c • ν}
  zero_mem' := ⟨0, zero_mem _, 0, zero_mem _, by simp⟩
  add_mem' := by
    rintro a b ⟨μ, hμ, ν, hν, rfl⟩ ⟨μ', hμ', ν', hν', rfl⟩
    exact ⟨μ + μ', add_mem hμ hμ', ν + ν', add_mem hν hν', by rw [smul_add]; abel⟩
  smul_mem' := by
    rintro o a ⟨μ, hμ, ν, hν, rfl⟩
    exact ⟨o • μ, Submodule.smul_mem _ o hμ, o • ν, Submodule.smul_mem _ o hν,
      by rw [smul_add, gp_smul_comm]⟩

theorem gp_mem_K {M N : Submodule (𝓞 E) S.V} {c : E} {k : S.V} :
    k ∈ gpK p M N c ↔ ∃ μ ∈ Formalism.HermitianLatticesTheory.localization₂ p M, ∃ ν ∈ Formalism.HermitianLatticesTheory.localization₂ p N, k = μ + c • ν := Iff.rfl

theorem gp_K_loc {M N : Submodule (𝓞 E) S.V} {c : E} {s : 𝓞 E} (hs : s ∈ p.primeCompl) {k : S.V}
    (hk : s • k ∈ gpK p M N c) : k ∈ gpK p M N c := by
  obtain ⟨μ, hμ, ν, hν, he⟩ := (gp_mem_K p).1 hk
  have hs0 := gp_ne_zero p hs
  set t : E := (algebraMap (𝓞 E) E s)⁻¹ with ht
  have hsμ : s • (t • μ) = μ := by rw [gp_osmul, smul_smul, ht, mul_inv_cancel₀ hs0, one_smul]
  have hsν : s • (t • ν) = ν := by rw [gp_osmul, smul_smul, ht, mul_inv_cancel₀ hs0, one_smul]
  refine (gp_mem_K p).2 ⟨t • μ, gp_of_smul p hs (by rw [hsμ]; exact hμ),
    t • ν, gp_of_smul p hs (by rw [hsν]; exact hν), ?_⟩
  have hk' : k = t • (s • k) := by rw [gp_osmul, smul_smul, ht, inv_mul_cancel₀ hs0, one_smul]
  rw [hk', he, smul_add, smul_comm t c ν]

theorem gp_core {M Λ N : Submodule (𝓞 E) S.V} {U : Submodule E S.V} {c : E}
    (hsat : ∀ w ∈ Formalism.HermitianLatticesTheory.localization₂ p Λ, w ∈ U → w ∈ Formalism.HermitianLatticesTheory.localization₂ p M) (hMU : ∀ w ∈ M, w ∈ U)
    (hN : N ≤ Formalism.HermitianLatticesTheory.localization₂ p Λ) {t s t' s' v w : S.V}
    (hv : v = c⁻¹ • (t - s)) (hvΛ : v ∈ Formalism.HermitianLatticesTheory.localization₂ p Λ) (hs : s ∈ U)
    (hs' : s' ∈ Formalism.HermitianLatticesTheory.localization₂ p M) (hw : w = c⁻¹ • (t' - s')) (hwN : w ∈ N)
    (hH : t - t' ∈ gpK p M N c) : v ∈ Formalism.HermitianLatticesTheory.localization₂ p (M ⊔ N) := by
  by_cases hc : c = 0
  · rw [hv, hc, inv_zero, zero_smul]
    exact zero_mem _
  obtain ⟨μ, hμ, ν, hν, he⟩ := (gp_mem_K p).1 hH
  have hq : v - w - ν = c⁻¹ • (μ - s + s') := by
    have ht : t = t' + (μ + c • ν) := by rw [← he]; abel
    rw [hv, hw, ht, show t' + (μ + c • ν) - s = (μ - s + s') + (t' - s') + c • ν by abel, smul_add, smul_add,
      smul_smul, inv_mul_cancel₀ hc, one_smul]
    abel
  have hqU : v - w - ν ∈ U := by
    rw [hq]
    refine U.smul_mem _ (U.add_mem (U.sub_mem (gp_locP_sub_E p hMU hμ) hs) (gp_locP_sub_E p hMU hs'))
  have hqΛ : v - w - ν ∈ Formalism.HermitianLatticesTheory.localization₂ p Λ :=
    sub_mem (sub_mem hvΛ (locP_locP_le p Λ (gp_le_locP p _ (hN hwN))))
      (locP_locP_le p Λ (locP_mono p hN hν))
  have hqM := hsat _ hqΛ hqU
  have hv' : v = (v - w - ν) + w + ν := by abel
  rw [hv']
  refine add_mem (add_mem (locP_mono p le_sup_left hqM) ?_) (locP_mono p le_sup_right hν)
  exact gp_le_locP p _ (Submodule.mem_sup_right hwN)

end GP

end PI.TermAttrConst.UnitaryGroupMassFormula
end
end

noncomputable section

open scoped Classical

namespace PI.TermAttrConst.UnitaryGroupMassFormula

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.DCRelEquiv PI.DCRelEquiv.UnitaryGroupMassFormula
  IsDedekindDomain

section GP2

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
  {Λ : Submodule (𝓞 E) S.V}

def gpMfix (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) : Submodule (𝓞 E) S.V :=
  Submodule.span (𝓞 E) ((XLam Λ F : Set S.V) ∪ {F.zt})

def gpGen (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T') (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E))
    (b : Fin (r + 1)) : S.V :=
  ((g : E)⁻¹) • (frame F' b - frameAct (frame F) ξ b)

def gpU (F : LFlag S r T) : Submodule E S.V := Xsp F ⊔ Submodule.span E {F.fl.z}

theorem gp_mplus_eq (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T')
    (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) :
    Mplus Λ g F F' ξ = gpMfix Λ F ⊔ Submodule.span (𝓞 E) (Set.range (gpGen g F F' ξ)) := by
  unfold Mplus gpMfix gpGen
  rw [Submodule.span_union]

theorem gp_X_iso (F : LFlag S r T) : ∀ v ∈ Xsp F, v ∈ orth S (Xsp F) := by
  have key : ∀ b, ∀ x ∈ Xsp F, S.hT x (F.fl.e b) = 0 := by
    intro b x hx
    dsimp only [Xsp, Formalism.MainNotions.S.FlagG.X] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact F.fl.e_iso a b
    | zero => simp
    | add y y' _ _ h1 h2 => rw [map_add (f := _), LinearMap.add_apply, h1, h2, add_zero]
    | smul c y _ h => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, h, smul_zero]
  intro v hv
  rw [mem_orth_iff]
  intro x hx
  dsimp only [Xsp, Formalism.MainNotions.S.FlagG.X] at hv
  induction hv using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨b, rfl⟩ := hy
    exact key b x hx
  | zero => simp
  | add y y' _ _ h1 h2 => rw [map_add (f := _), h1, h2, add_zero]
  | smul c y _ h => rw [map_smul, h, smul_zero]

theorem gp_Mfix_le_U (F : LFlag S r T) (hl : IsLift Λ F) : ∀ w ∈ gpMfix Λ F, w ∈ gpU F := by
  have h : gpMfix Λ F ≤ toO S (gpU F) := by
    refine Submodule.span_le.2 ?_
    rintro w (hw | hw)
    · exact Submodule.mem_sup_left (mem_XLam.1 hw).2
    · rw [Set.mem_singleton_iff] at hw
      rw [hw, hl.2]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  exact fun w hw => h hw

theorem gp_sat (p : Ideal (𝓞 E)) [p.IsPrime] (F : LFlag S r T) (hl : IsLift Λ F)
    (hprim : ∀ c : E, c • F.fl.z ∈ Lsub Λ F → ∃ o : 𝓞 E, (o : E) = c) :
    ∀ w ∈ Formalism.HermitianLatticesTheory.localization₂ p Λ, w ∈ gpU F → w ∈ Formalism.HermitianLatticesTheory.localization₂ p (gpMfix Λ F) := by
  intro w hw hU
  obtain ⟨s, hs, hsw⟩ := (mem_localization_iff p Λ w).1 hw
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hU
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  have hzΛ : F.fl.z ∈ Λ := hl.1
  have horth : s • (u + c • F.fl.z) ∈ orth S (Xsp F) := by
    rw [gp_osmul]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ (gp_X_iso F u hu)
      (Submodule.smul_mem _ _ (z_mem_orth F)))
  have hLsub : (algebraMap (𝓞 E) E s * c) • F.fl.z ∈ Lsub Λ F := by
    unfold Lsub Lrep
    rw [Submodule.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [Submodule.mem_sup]
      refine ⟨s • (u + c • F.fl.z), ?_, -((algebraMap (𝓞 E) E s) • u), ?_, ?_⟩
      · rw [Submodule.mem_inf]
        exact ⟨hsw, (Submodule.restrictScalars_mem _ _ _).2 horth⟩
      · rw [Submodule.restrictScalars_mem]
        exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hu)
      · rw [gp_osmul, smul_add, smul_smul]
        abel
    · rw [Submodule.restrictScalars_mem]
      exact Submodule.smul_mem _ _ (z_mem_orth F)
  obtain ⟨o, ho⟩ := hprim _ hLsub
  have heq : s • (u + c • F.fl.z) = (algebraMap (𝓞 E) E s) • u + o • F.fl.z := by
    have : o • F.fl.z = (algebraMap (𝓞 E) E s * c) • F.fl.z := by
      rw [gp_osmul]
      exact congrArg (· • F.fl.z) ho
    rw [this, gp_osmul, smul_add, smul_smul]
  have hoz : o • F.fl.z ∈ Λ := Submodule.smul_mem _ o hzΛ
  have hsu : (algebraMap (𝓞 E) E s) • u ∈ XLam Λ F := by
    refine mem_XLam.2 ⟨?_, Submodule.smul_mem _ _ hu⟩
    have : (algebraMap (𝓞 E) E s) • u = s • (u + c • F.fl.z) - o • F.fl.z := by rw [heq]; abel
    rw [this]
    exact Submodule.sub_mem _ hsw hoz
  refine (mem_localization_iff p _ _).2 ⟨s, hs, ?_⟩
  rw [heq]
  refine Submodule.add_mem _ (Submodule.subset_span (Set.mem_union_left _ hsu)) ?_
  refine Submodule.smul_mem _ o (Submodule.subset_span (Set.mem_union_right _ ?_))
  rw [Set.mem_singleton_iff, hl.2]

end GP2

end PI.TermAttrConst.UnitaryGroupMassFormula
end
end

noncomputable section

open scoped Classical

set_option linter.style.haveILetI false

namespace PI.TermAttrConst.UnitaryGroupMassFormula

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.DCRelEquiv PI.DCRelEquiv.UnitaryGroupMassFormula
  IsDedekindDomain

section GP3

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
  {Λ : Submodule (𝓞 E) S.V}

theorem gp_div (g : ℕ) : ∀ v ∈ Ideal.span {(g : 𝓞 E)} • Λ, ((g : E))⁻¹ • v ∈ Λ := by
  intro v hv
  refine Submodule.smul_induction_on hv ?_ ?_
  · intro a ha w hw
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 ha
    by_cases hg : (g : E) = 0
    · rw [hg, inv_zero, zero_smul]
      exact zero_mem _
    · have : ((g : E))⁻¹ • ((t * (g : 𝓞 E)) • w) = t • w := by
        rw [gp_osmul, gp_osmul, map_mul, map_natCast, smul_smul, mul_comm (algebraMap (𝓞 E) E t),
          ← mul_assoc, inv_mul_cancel₀ hg, one_mul]
      rw [this]
      exact Submodule.smul_mem _ t hw
  · intro a b ha hb
    rw [smul_add]
    exact add_mem ha hb

theorem gp_locΛ_map (p : Ideal (𝓞 E)) [p.IsPrime] {n : S.V ≃ₗ[E] S.V} (hn : IsAutLam S Λ n) {v : S.V}
    (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ p Λ) : n v ∈ Formalism.HermitianLatticesTheory.localization₂ p Λ := by
  obtain ⟨s, hs, hv⟩ := (mem_localization_iff p Λ v).1 hv
  exact (mem_localization_iff p Λ _).2 ⟨s, hs, by rw [← gp_map_osmul]; exact autLam_maps hn hv⟩

theorem gp_gen_mem (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) {F : LFlag S r T} {F' : LFlag S r T'}
    {ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)} (hξ : AdmWit Λ g F F' ξ) (hP : (g : 𝓞 E) ∈ P.asIdeal)
    (b : Fin (r + 1)) : (haveI := P.isPrime; gpGen g F F' ξ b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ) := by
  haveI := P.isPrime
  have h := hξ.2.2 b P hP
  obtain ⟨s, hs, hv⟩ := (mem_localization_iff P.asIdeal _ _).1 h
  refine (mem_localization_iff P.asIdeal Λ _).2 ⟨s, hs, ?_⟩
  unfold gpGen
  rw [gp_smul_comm]
  exact gp_div g _ hv

theorem gp_Mfix_map {F : LFlag S r T} (hl : IsLift Λ F) {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) :
    ∀ v ∈ gpMfix Λ F, n v ∈ gpMfix Λ F := by
  have h : gpMfix Λ F ≤ (gpMfix Λ F).comap (fO n) := by
    refine Submodule.span_le.2 ?_
    rintro w (hw | hw)
    · obtain ⟨h1, h2⟩ := mem_XLam.1 hw
      exact Submodule.subset_span (Set.mem_union_left _ (mem_XLam.2 ⟨autLam_maps hn.1 h1, nlam_maps_X hn _ h2⟩))
    · rw [Set.mem_singleton_iff] at hw
      rw [hw, hl.2]
      show n F.fl.z ∈ gpMfix Λ F
      have h1 : F.fl.z ∈ gpMfix Λ F := by
        refine Submodule.subset_span (Set.mem_union_right _ ?_)
        rw [Set.mem_singleton_iff, hl.2]
      have h2 : n F.fl.z - F.fl.z ∈ gpMfix Λ F :=
        Submodule.subset_span (Set.mem_union_left _ (nlam_z_sub hn hl.1))
      have := Submodule.add_mem _ h2 h1
      rwa [sub_add_cancel] at this
  exact fun v hv => h hv

theorem gp_Mfix_map_loc (p : Ideal (𝓞 E)) [p.IsPrime] {F : LFlag S r T} (hl : IsLift Λ F)
    {n : S.V ≃ₗ[E] S.V} (hn : n ∈ NLam Λ F) {v : S.V} (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ p (gpMfix Λ F)) :
    n v ∈ Formalism.HermitianLatticesTheory.localization₂ p (gpMfix Λ F) := by
  obtain ⟨s, hs, hv⟩ := (mem_localization_iff p _ v).1 hv
  exact (mem_localization_iff p _ _).2 ⟨s, hs, by rw [← gp_map_osmul]; exact gp_Mfix_map hl hn _ hv⟩

theorem gp_e_mem (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) {F' : LFlag S r T'} (hc : IsFixedConv Λ g F')
    (hP : (g : 𝓞 E) ∈ P.asIdeal) (a : Fin r) :
    (haveI := P.isPrime; F'.fl.e a ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F')) := by
  haveI := P.isPrime
  obtain ⟨c, -, hc1, heq⟩ := hc.1 P
  rw [heq]
  have : c a • F'.fl.e a ∈ Submodule.span (𝓞 E) (Set.range fun a => c a • F'.fl.e a) :=
    Submodule.subset_span ⟨a, rfl⟩
  rw [hc1 hP a, one_smul] at this
  exact gp_le_locP _ _ this

theorem gp_XLam_le (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) {F' : LFlag S r T'} (hc : IsFixedConv Λ g F')
    (hP : (g : 𝓞 E) ∈ P.asIdeal) (K : Submodule (𝓞 E) S.V)
    (hK : ∀ s ∈ P.asIdeal.primeCompl, ∀ k : S.V, s • k ∈ K → k ∈ K) (he : ∀ a, F'.fl.e a ∈ K) :
    (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F') ≤ K) := by
  haveI := P.isPrime
  obtain ⟨c, -, hc1, heq⟩ := hc.1 P
  rw [heq]
  intro v hv
  obtain ⟨s, hs, hv⟩ := (mem_localization_iff P.asIdeal _ v).1 hv
  refine hK s hs v ((Submodule.span_le.2 ?_) hv)
  rintro _ ⟨a, rfl⟩
  show c a • F'.fl.e a ∈ K
  rw [hc1 hP a, one_smul]
  exact he a

theorem gp_frame_loc (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) {F' : LFlag S r T'} (hl : IsLift Λ F')
    (hc : IsFixedConv Λ g F') (hP : (g : 𝓞 E) ∈ P.asIdeal) (b : Fin (r + 1)) :
    (haveI := P.isPrime; frame F' b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ) := by
  haveI := P.isPrime
  induction b using Fin.lastCases with
  | last =>
    rw [frame_last]
    exact gp_le_locP _ _ hl.1
  | cast i =>
    rw [frame_castSucc]
    refine locP_mono _ (fun v hv => (mem_XLam.1 hv).1) (gp_e_mem P g hc hP i)

theorem gp_frameAct_mem (P : HeightOneSpectrum (𝓞 E)) (g : ℕ) {F : LFlag S r T} (hl : IsLift Λ F)
    (hc : IsFixedConv Λ g F) (hP : (g : 𝓞 E) ∈ P.asIdeal)
    (ξ : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)) (b : Fin (r + 1)) :
    (haveI := P.isPrime; frameAct (frame F) ξ b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (gpMfix Λ F)) := by
  haveI := P.isPrime
  unfold frameAct
  refine Submodule.sum_mem _ fun a _ => ?_
  have e : ((ξ a b : 𝓞 E) : E) • frame F a = ξ a b • frame F a := (gp_osmul _ _).symm
  rw [e]
  refine Submodule.smul_mem _ _ ?_
  induction a using Fin.lastCases with
  | last =>
    rw [frame_last]
    refine gp_le_locP _ _ (Submodule.subset_span (Set.mem_union_right _ ?_))
    rw [Set.mem_singleton_iff, hl.2]
  | cast i =>
    rw [frame_castSucc]
    exact locP_mono _ (show XLam Λ F ≤ gpMfix Λ F from fun v hv => Submodule.subset_span
      (Set.mem_union_left _ hv)) (gp_e_mem P g hc hP i)

theorem gp_nlam_sub_X {F' : LFlag S r T'} {m : S.V ≃ₗ[E] S.V} (hm : m ∈ NLam Λ F') (b : Fin (r + 1)) :
    m (frame F' b) - frame F' b ∈ Xsp F' := by
  induction b using Fin.lastCases with
  | last =>
    rw [frame_last]
    exact hm.2.2 _ (z_mem_orth F')
  | cast i =>
    rw [frame_castSucc]
    exact Xflag_le_X F' i.1 (hm.2.1 i.1 _ (e_mem_Xflag F' i))

theorem gp_loc_X (p : Ideal (𝓞 E)) [p.IsPrime] {F' : LFlag S r T'} {v : S.V} (hv : v ∈ Formalism.HermitianLatticesTheory.localization₂ p Λ)
    (hX : v ∈ Xsp F') : v ∈ Formalism.HermitianLatticesTheory.localization₂ p (XLam Λ F') := by
  obtain ⟨s, hs, hv⟩ := (mem_localization_iff p Λ v).1 hv
  refine (mem_localization_iff p _ v).2 ⟨s, hs, mem_XLam.2 ⟨hv, ?_⟩⟩
  rw [gp_osmul]
  exact Submodule.smul_mem _ _ hX

end GP3

end PI.TermAttrConst.UnitaryGroupMassFormula
end
end

noncomputable section

open scoped Classical

set_option linter.style.haveILetI false

namespace PI.TermAttrConst.UnitaryGroupMassFormula

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.DCRelEquiv PI.DCRelEquiv.UnitaryGroupMassFormula
  IsDedekindDomain

section GP4

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}
  {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {F : LFlag S r T} {x y : LFlag S r T'} {n m : S.V ≃ₗ[E] S.V}
  {ξ ξ' : Matrix (Fin (r + 1)) (Fin (r + 1)) (𝓞 E)}

theorem generator_mem_local_lattice_forward (P : HeightOneSpectrum (𝓞 E)) (hFl : IsLift Λ F) (hFc : IsFixedConv Λ g F)
    (hxl : IsLift Λ x) (hxc : IsFixedConv Λ g x) (hn : n ∈ NLam Λ F) (hm : m ∈ NLam Λ x)
    (hfr : ∀ a, frame y a = n (m (frame x a))) (hξ : AdmWit Λ g F x ξ) (hξ' : AdmWit Λ g F y ξ')
    (hP : (g : 𝓞 E) ∈ P.asIdeal) (b : Fin (r + 1)) :
    (haveI := P.isPrime; gpGen g F y ξ' b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal
      (gpMfix Λ F ⊔ Submodule.span (𝓞 E) (Set.range fun a => n (gpGen g F x ξ a)))) := by
  haveI := P.isPrime
  set N := Submodule.span (𝓞 E) (Set.range fun a => n (gpGen g F x ξ a)) with hNdef
  by_cases hg : (g : E) = 0
  · unfold gpGen
    rw [hg, inv_zero, zero_smul]
    exact zero_mem _
  have hNΛ : N ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact gp_locΛ_map _ hn.1 (gp_gen_mem P g hξ hP a)
  have hdec : ∀ a, frame x a = frameAct (frame F) ξ a + (g : E) • gpGen g F x ξ a := by
    intro a
    unfold gpGen
    rw [smul_smul, mul_inv_cancel₀ hg, one_smul]
    abel
  have hK : ∀ a, n (frame x a) ∈ gpK P.asIdeal (gpMfix Λ F) N (g : E) := by
    intro a
    refine (gp_mem_K _).2 ⟨n (frameAct (frame F) ξ a),
      gp_Mfix_map_loc _ hFl hn (gp_frameAct_mem P g hFl hFc hP ξ a), n (gpGen g F x ξ a),
      gp_le_locP _ _ (Submodule.subset_span ⟨a, rfl⟩), ?_⟩
    rw [hdec a, map_add (f := _), map_smul]
  have hH : frame y b - n (frame x b) ∈ gpK P.asIdeal (gpMfix Λ F) N (g : E) := by
    have hd : m (frame x b) - frame x b ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ x) :=
      gp_loc_X _ (sub_mem (gp_locΛ_map _ hm.1 (gp_frame_loc P g hxl hxc hP b))
        (gp_frame_loc P g hxl hxc hP b)) (gp_nlam_sub_X hm b)
    have hle := gp_XLam_le P g hxc hP ((gpK P.asIdeal (gpMfix Λ F) N (g : E)).comap (fO n)) ?_ ?_
    · have h1 := hle hd
      rw [Submodule.mem_comap, fO_apply, map_sub] at h1
      rw [hfr b]
      exact h1
    · intro s hs k hk
      rw [Submodule.mem_comap, fO_apply] at hk ⊢
      rw [gp_map_osmul] at hk
      exact gp_K_loc _ hs hk
    · intro a
      rw [Submodule.mem_comap, fO_apply, ← frame_castSucc x a]
      exact hK _
  exact gp_core P.asIdeal (M := gpMfix Λ F) (Λ := Λ) (N := N) (U := gpU F) (c := (g : E))
    (gp_sat _ F hFl hFc.2) (gp_Mfix_le_U F hFl) hNΛ (t := frame y b) (s := frameAct (frame F) ξ' b)
    (t' := n (frame x b)) (s' := n (frameAct (frame F) ξ b)) (v := gpGen g F y ξ' b) (w := n (gpGen g F x ξ b)) rfl
    (gp_gen_mem P g hξ' hP b)
    (gp_locP_sub_E _ (gp_Mfix_le_U F hFl) (gp_frameAct_mem P g hFl hFc hP ξ' b))
    (gp_Mfix_map_loc _ hFl hn (gp_frameAct_mem P g hFl hFc hP ξ b))
    (by unfold gpGen; rw [map_smul, map_sub]) (Submodule.subset_span ⟨b, rfl⟩) hH

theorem generator_mem_local_lattice_backward (P : HeightOneSpectrum (𝓞 E)) (hFl : IsLift Λ F) (hFc : IsFixedConv Λ g F)
    (hxl : IsLift Λ x) (hxc : IsFixedConv Λ g x) (hyc : IsFixedConv Λ g y) (hn : n ∈ NLam Λ F)
    (hm : m ∈ NLam Λ x) (hfr : ∀ a, frame y a = n (m (frame x a))) (hξ : AdmWit Λ g F x ξ)
    (hξ' : AdmWit Λ g F y ξ') (hP : (g : 𝓞 E) ∈ P.asIdeal) (b : Fin (r + 1)) :
    (haveI := P.isPrime; n (gpGen g F x ξ b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal
      (gpMfix Λ F ⊔ Submodule.span (𝓞 E) (Set.range (gpGen g F y ξ')))) := by
  haveI := P.isPrime
  set N := Submodule.span (𝓞 E) (Set.range (gpGen g F y ξ')) with hNdef
  by_cases hg : (g : E) = 0
  · unfold gpGen
    rw [hg, inv_zero, zero_smul, map_zero]
    exact zero_mem _
  have hNΛ : N ≤ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, rfl⟩
    exact gp_gen_mem P g hξ' hP a
  have hdec : ∀ a, frame y a = frameAct (frame F) ξ' a + (g : E) • gpGen g F y ξ' a := by
    intro a
    unfold gpGen
    rw [smul_smul, mul_inv_cancel₀ hg, one_smul]
    abel
  have hH : n (frame x b) - frame y b ∈ gpK P.asIdeal (gpMfix Λ F) N (g : E) := by
    have hX : n (m (frame x b) - frame x b) ∈ Xsp y := by
      have hfr' : ∀ a, frame y a = (m.trans n) (frame x a) := fun a => hfr a
      rw [Xsp_mem_transport hfr', LinearEquiv.symm_trans_apply, LinearEquiv.symm_apply_apply]
      exact nlam_maps_X (nlam_inv hm) _ (gp_nlam_sub_X hm b)
    have hd : n (m (frame x b) - frame x b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ y) :=
      gp_loc_X _ (gp_locΛ_map _ hn.1 (sub_mem (gp_locΛ_map _ hm.1 (gp_frame_loc P g hxl hxc hP b))
        (gp_frame_loc P g hxl hxc hP b))) hX
    have hle := gp_XLam_le P g hyc hP (gpK P.asIdeal (gpMfix Λ F) N (g : E))
      (fun s hs k hk => gp_K_loc _ hs hk) (fun a => by
        rw [← frame_castSucc y a]
        exact (gp_mem_K _).2 ⟨frameAct (frame F) ξ' _, gp_frameAct_mem P g hFl hFc hP ξ' _,
          gpGen g F y ξ' _, gp_le_locP _ _ (Submodule.subset_span ⟨_, rfl⟩), hdec _⟩)
    have h1 := neg_mem (hle hd)
    rw [map_sub, ← hfr b, neg_sub] at h1
    exact h1
  exact gp_core P.asIdeal (M := gpMfix Λ F) (Λ := Λ) (N := N) (U := gpU F) (c := (g : E))
    (gp_sat _ F hFl hFc.2) (gp_Mfix_le_U F hFl) hNΛ (t := n (frame x b))
    (s := n (frameAct (frame F) ξ b)) (t' := frame y b) (s' := frameAct (frame F) ξ' b)
    (v := n (gpGen g F x ξ b)) (w := gpGen g F y ξ' b) (by unfold gpGen; rw [map_smul, map_sub]) (gp_locΛ_map _ hn.1 (gp_gen_mem P g hξ hP b))
    (gp_locP_sub_E _ (gp_Mfix_le_U F hFl) (gp_Mfix_map_loc _ hFl hn (gp_frameAct_mem P g hFl hFc hP ξ b)))
    (gp_frameAct_mem P g hFl hFc hP ξ' b) rfl (Submodule.subset_span ⟨b, rfl⟩) hH

theorem gp_mplus (P : HeightOneSpectrum (𝓞 E)) (hFl : IsLift Λ F) (hFc : IsFixedConv Λ g F)
    (hxl : IsLift Λ x) (hxc : IsFixedConv Λ g x) (hyc : IsFixedConv Λ g y) (hn : n ∈ NLam Λ F)
    (hm : m ∈ NLam Λ x) (hfr : ∀ a, frame y a = n (m (frame x a))) (hξ : AdmWit Λ g F x ξ)
    (hξ' : AdmWit Λ g F y ξ') (hP : (g : 𝓞 E) ∈ P.asIdeal) :
    (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ g F y ξ') =
      Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap n (Mplus Λ g F x ξ))) := by
  haveI := P.isPrime
  have hMfix_sub : ∀ v ∈ gpMfix Λ F, v ∈ Formalism.HermitianLatticesTheory.gmap n (Mplus Λ g F x ξ) := by
    intro v hv
    rw [mem_gmap_iff, gp_mplus_eq]
    exact Submodule.mem_sup_left (gp_Mfix_map hFl (nlam_inv hn) v hv)
  apply le_antisymm
  · refine locP_le _ ?_
    rw [gp_mplus_eq]
    refine sup_le (fun v hv => gp_le_locP _ _ (hMfix_sub v hv)) (Submodule.span_le.2 ?_)
    rintro _ ⟨b, rfl⟩
    refine locP_mono _ (sup_le (fun v hv => hMfix_sub v hv) (Submodule.span_le.2 ?_))
      (generator_mem_local_lattice_forward P hFl hFc hxl hxc hn hm hfr hξ hξ' hP b)
    rintro _ ⟨a, rfl⟩
    show n (gpGen g F x ξ a) ∈ Formalism.HermitianLatticesTheory.gmap n (Mplus Λ g F x ξ)
    rw [mem_gmap_iff, LinearEquiv.symm_apply_apply, gp_mplus_eq]
    exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, rfl⟩)
  · refine locP_le _ ?_
    intro v hv
    rw [mem_gmap_iff] at hv
    have key : Mplus Λ g F x ξ ≤ (Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ g F y ξ')).comap (fO n) := by
      rw [gp_mplus_eq (F' := x)]
      refine sup_le ?_ (Submodule.span_le.2 ?_)
      · intro w hw
        rw [Submodule.mem_comap, fO_apply, gp_mplus_eq]
        exact gp_le_locP _ _ (Submodule.mem_sup_left (gp_Mfix_map hFl hn w hw))
      · rintro _ ⟨b, rfl⟩
        show n (gpGen g F x ξ b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Mplus Λ g F y ξ')
        rw [gp_mplus_eq]
        exact generator_mem_local_lattice_backward P hFl hFc hxl hxc hyc hn hm hfr hξ hξ' hP b
    have h1 := key hv
    rw [Submodule.mem_comap, fO_apply, LinearEquiv.apply_symm_apply] at h1
    exact h1

end GP4

end PI.TermAttrConst.UnitaryGroupMassFormula
end
end

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TermAttractorConstant.RelevanceConstantDoubleCosets
noncomputable section

open scoped Classical

namespace PI.TermAttrConst.UnitaryGroupMassFormula

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def RelevanceConstantDoubleCosets : Prop :=
  ∀ (D : D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ →
      RelFun Λ (lf D F0) (PD D Λ (lf D F0) u') D.host.F

def GenericityConstantDoubleCosets : Prop :=
  ∀ (D : D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ →
      GenFun Λ (lf D F0) (PD D Λ (lf D F0) u') (gS D)

theorem termGFun_holds (D : D7) (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
    (Λ : Submodule (𝓞 D.host.E) (VS D).V) (_ : IsRowLat D F0 Λ) :
    GFun Λ (lf D F0) (PD D Λ (lf D F0) u') := gFun_all _ _ _

theorem termFun_of (hG : GenericityConstantDoubleCosets) (D : D7) (u u' : D.what₂.Word) : TermFun D u u' := by
  intro F0 Λ hΛ
  exact ⟨gFun_all _ _ _, cellFun_all _ _ _, relFun_all _ _ _ _, hG D u u' F0 Λ hΛ, feqFFun_all _ _ _⟩

end PI.TermAttrConst.UnitaryGroupMassFormula
end
end

noncomputable section

open scoped Classical

set_option linter.style.haveILetI false

namespace PI.TermAttrConst.UnitaryGroupMassFormula

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermDef PI.DCRelEquiv PI.DCRelEquiv.UnitaryGroupMassFormula
  IsDedekindDomain

section GenAll

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem gen_fwd {Λ : Submodule (𝓞 E) S.V} {g : ℕ} {F : LFlag S r T} {x y : LFlag S r T'}
    (hFl : IsLift Λ F) (hFc : IsFixedConv Λ g F) (hxl : IsLift Λ x) (hxc : IsFixedConv Λ g x)
    (hyc : IsFixedConv Λ g y) (hya : IsAdmissible Λ g F y) (hxy : DCRel Λ F x y)
    (hgx : IsGeneric Λ g F x) : IsGeneric Λ g F y := by
  obtain ⟨ξ', hξ'⟩ := hya
  obtain ⟨n, hn, m, hm, hfr, hzt⟩ := hxy
  obtain ⟨ξ, hξ, hgx⟩ := hgx
  refine ⟨ξ', hξ', fun P => ?_⟩
  haveI := P.isPrime
  have hB := locP_BLat_transport hFl hxl hn hm hfr hzt P.asIdeal
  constructor
  · intro hP
    rw [hB, (hgx P).1 hP, ← locP_gmap]
    exact (gp_mplus P hFl hFc hxl hxc hyc hn hm hfr hξ hξ' hP).symm
  · intro hP
    rw [hB, (hgx P).2 hP, ← locP_gmap, UU_transport hFl hxl hn hm hfr hzt]

theorem genFun_gen (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (Pc : LFlag S r T' → Prop) (g : ℕ)
    (hFl : IsLift Λ F) (hFc : IsFixedConv Λ g F)
    (hPc : ∀ x, Pc x → IsLift Λ x ∧ IsAdmissible Λ g F x ∧ IsFixedConv Λ g x) :
    GenFun Λ F Pc g := by
  intro x y hxy
  have hxy' : DCRel Λ F x.1 y.1 := hxy
  obtain ⟨hxl, hxa, hxc⟩ := hPc x.1 x.2
  obtain ⟨hyl, hya, hyc⟩ := hPc y.1 y.2
  have hyx : DCRel Λ F y.1 x.1 := (dCRelEquivAll_holds E S r T T' Λ F).symm hxy'
  exact ⟨gen_fwd hFl hFc hxl hxc hyc hya hxy', gen_fwd hFl hFc hyl hyc hxc hxa hyx⟩

end GenAll

section D7

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem genericity_constant_double_cosets : GenericityConstantDoubleCosets := by
  intro D u u' F0 Λ hΛ
  obtain ⟨-, ⟨-, -, hFl, hFc⟩, -⟩ := hΛ
  exact genFun_gen Λ (lf D F0) _ (gS D) hFl hFc fun x hx => ⟨hx.1, hx.2.1, hx.2.2.1⟩

end D7

end PI.TermAttrConst.UnitaryGroupMassFormula
