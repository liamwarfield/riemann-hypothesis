module

public import GroundTheory.LocalFields.UpperNumbering
public import GroundTheory.LocalFields.LubinTateLimitGalois

@[expose] public section

section -- merged from GroundTheory.LocalFields.ConductorTransport
noncomputable section

open ValuativeRel IsDiscreteValuationRing

namespace GroundTheory.LocalField

section Transport

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {L₁ : Type*} [Field L₁] [ValuativeRel L₁] [TopologicalSpace L₁] [IsNonarchimedeanLocalField L₁]
  [Algebra K L₁] [ValuativeExtension K L₁] [FiniteDimensional K L₁]
  {L₂ : Type*} [Field L₂] [ValuativeRel L₂] [TopologicalSpace L₂] [IsNonarchimedeanLocalField L₂]
  [Algebra K L₂] [ValuativeExtension K L₂] [FiniteDimensional K L₂]

def integerAlgEquivOfAlgEquiv (e : L₁ ≃ₐ[K] L₂) : 𝒪[L₁] ≃ₐ[𝒪[K]] 𝒪[L₂] :=
  AlgEquiv.ofAlgHom (integerAlgHom e.toAlgHom) (integerAlgHom e.symm.toAlgHom)
    (AlgHom.ext fun x => Subtype.ext (e.apply_symm_apply (x : L₂)))
    (AlgHom.ext fun x => Subtype.ext (e.symm_apply_apply (x : L₁)))


omit [IsNonarchimedeanLocalField K] in
theorem addVal_ringEquiv {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] (φ : R ≃+* S) (x : R) :
    addVal S (φ x) = addVal R x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  have hϖ' : Irreducible (φ ϖ) := (MulEquiv.irreducible_iff (f := (φ : R ≃* S))).mpr hϖ
  rw [map_mul, map_pow, addVal_def' u hϖ n]
  exact addVal_def' (Units.map (φ : R →* S) u) hϖ' n

theorem lowerIndex_autCongr (e : L₁ ≃ₐ[K] L₂) (σ : L₁ ≃ₐ[K] L₁) :
    lowerIndex K L₂ (e.autCongr σ) = lowerIndex K L₁ σ := by
  set φ := integerAlgEquivOfAlgEquiv e
  rw [lowerIndex, lowerIndex, ← φ.toEquiv.iInf_comp]
  refine iInf_congr fun x => ?_
  have h : integerAlgEquiv K L₂ (e.autCongr σ) (φ x) - φ x = φ (integerAlgEquiv K L₁ σ x - x) := by
    apply Subtype.ext
    change (e.autCongr σ) (e (x : L₁)) - e (x : L₁) = e (σ (x : L₁) - (x : L₁))
    simp [AlgEquiv.autCongr_apply]
  simp only [AlgEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  rw [h]
  exact addVal_ringEquiv (φ : 𝒪[L₁] ≃+* 𝒪[L₂]) _

theorem map_lowerRamificationGroup_autCongr (e : L₁ ≃ₐ[K] L₂) (i : ℤ) :
    (lowerRamificationGroup K L₁ i).map (e.autCongr : (L₁ ≃ₐ[K] L₁) →* (L₂ ≃ₐ[K] L₂)) =
      lowerRamificationGroup K L₂ i := by
  ext τ
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    rw [mem_lowerRamificationGroup_iff_lowerIndex] at hσ ⊢
    show _ ≤ lowerIndex K L₂ (e.autCongr σ)
    rw [lowerIndex_autCongr]
    exact hσ
  · intro hτ
    refine ⟨e.autCongr.symm τ, ?_, MulEquiv.apply_symm_apply _ _⟩
    rw [mem_lowerRamificationGroup_iff_lowerIndex] at hτ ⊢
    rw [← lowerIndex_autCongr e, MulEquiv.apply_symm_apply]
    exact hτ

theorem map_lowerRamificationGroupReal_autCongr (e : L₁ ≃ₐ[K] L₂) (t : ℝ) :
    (lowerRamificationGroupReal K L₁ t).map (e.autCongr : (L₁ ≃ₐ[K] L₁) →* (L₂ ≃ₐ[K] L₂)) =
      lowerRamificationGroupReal K L₂ t :=
  map_lowerRamificationGroup_autCongr e _

theorem herbrandPhi_eq_of_algEquiv (e : L₁ ≃ₐ[K] L₂) (u : ℝ) :
    herbrandPhi K L₂ u = herbrandPhi K L₁ u := by
  rcases le_or_gt (-1) u with hu | hu
  · rw [herbrandPhi_eq_sum_lowerIndex hu, herbrandPhi_eq_sum_lowerIndex hu]
    have hcard : Nat.card (lowerRamificationGroup K L₂ 0) = Nat.card (lowerRamificationGroup K L₁ 0) := by
      rw [← map_lowerRamificationGroup_autCongr e 0]
      exact Subgroup.card_map_of_injective e.autCongr.injective
    rw [hcard, ← Fintype.sum_equiv e.autCongr.toEquiv
      (fun σ => enatMin (lowerIndex K L₁ σ) (u + 1))
      (fun τ => enatMin (lowerIndex K L₂ τ) (u + 1))
      (fun σ => by
        show _ = enatMin (lowerIndex K L₂ (e.autCongr σ)) (u + 1)
        rw [lowerIndex_autCongr])]
  · rw [herbrandPhi_of_nonpos (by linarith), herbrandPhi_of_nonpos (by linarith)]

theorem herbrandPsi_eq_of_algEquiv (e : L₁ ≃ₐ[K] L₂) (v : ℝ) :
    herbrandPsi K L₂ v = herbrandPsi K L₁ v := by
  rw [herbrandPsi_eq_iff, herbrandPhi_eq_of_algEquiv e, herbrandPhi_herbrandPsi]

theorem map_upperRamificationGroup_autCongr (e : L₁ ≃ₐ[K] L₂) (v : ℝ) :
    (upperRamificationGroup K L₁ v).map (e.autCongr : (L₁ ≃ₐ[K] L₁) →* (L₂ ≃ₐ[K] L₂)) =
      upperRamificationGroup K L₂ v := by
  rw [upperRamificationGroup, upperRamificationGroup, herbrandPsi_eq_of_algEquiv e,
    map_lowerRamificationGroupReal_autCongr]

theorem upperRamificationGroup_eq_bot_of_ramificationIndex_eq_one [IsGalois K L₁]
    (he : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation L₁))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) = 1) {v : ℝ} (hv : -1 < v) : upperRamificationGroup K L₁ v = ⊥ := by
  have h0 : lowerRamificationGroup K L₁ 0 = ⊥ :=
    Subgroup.eq_bot_of_card_eq _ (by rw [card_lowerRamificationGroup_zero, he])
  rw [eq_bot_iff, ← h0, upperRamificationGroup, lowerRamificationGroupReal]
  apply lowerRamificationGroup_antitone
  have h1 : -1 < herbrandPsi K L₁ v := by
    rw [← herbrandPsi_of_nonpos (K := K) (L := L₁) (show (-1 : ℝ) ≤ 0 by norm_num)]
    exact herbrandPsi_strictMono hv
  exact Int.le_ceil_iff.mpr (by push_cast; linarith)

end Transport

section Restrict

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
  {L M : IntermediateField K Ω} [FiniteDimensional K L] [FiniteDimensional K M] [IsGalois K L]
  [IsGalois K M]

theorem map_upperRamificationGroup_restrictAut (h : L ≤ M) (v : ℝ) :
    (upperRamificationGroup K M v).map (restrictAut h) = upperRamificationGroup K L v := by
  set R := IntermediateField.restrict h
  let e : L ≃ₐ[K] R := IntermediateField.restrictAlgEquiv h
  have : IsGalois K R := IsGalois.of_algEquiv e
  have hH := map_upperRamificationGroup (K := K) (L := M) R v
  have hT := map_upperRamificationGroup_autCongr e.symm v
  have key : ∀ y : R, ((e.symm y : L) : Ω) = ((y : M) : Ω) := fun y => by
    conv_rhs => rw [← e.apply_symm_apply y]
    rfl
  have hcomp : (e.symm.autCongr : (R ≃ₐ[K] R) →* (L ≃ₐ[K] L)).comp
      (AlgEquiv.restrictNormalHom R) = restrictAut h := by
    ext σ x
    rw [restrictAut_apply]
    show ((e.symm ((σ.restrictNormal R) (e x)) : L) : Ω) = _
    rw [key]
    have h1 := AlgEquiv.restrictNormal_commutes σ R (e x)
    have h2 : (algebraMap R M (σ.restrictNormal R (e x)) : M) = ((σ.restrictNormal R (e x) : R) : M) :=
      rfl
    rw [← h2, h1]
    rfl
  rw [← hT, ← hH, Subgroup.map_map, hcomp]

end Restrict

end GroundTheory.LocalField
end
end

section -- merged from GroundTheory.LocalFields.LubinTateUnramified
noncomputable section

open IntermediateField Topology Filter

namespace GroundTheory.LocalField

open ValuativeRel

section Sup

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]

theorem algEquiv_ext_sup {F₁ F₂ : IntermediateField K Ω} [Normal K F₁] [Normal K F₂]
    {σ σ' : (F₁ ⊔ F₂ : IntermediateField K Ω) ≃ₐ[K] (F₁ ⊔ F₂ : IntermediateField K Ω)}
    (h₁ : restrictAut le_sup_left σ = restrictAut le_sup_left σ')
    (h₂ : restrictAut le_sup_right σ = restrictAut le_sup_right σ') : σ = σ' := by
  have key : ((F₁ ⊔ F₂ : IntermediateField K Ω).val.comp σ.toAlgHom) =
      ((F₁ ⊔ F₂ : IntermediateField K Ω).val.comp σ'.toAlgHom) := by
    refine algHom_ext_of_eq_adjoin K (sup_def F₁ F₂) fun x hx => ?_
    rcases hx with hx | hx
    · have := congrArg (fun τ : F₁ ≃ₐ[K] F₁ => ((τ ⟨x, hx⟩ : F₁) : Ω)) h₁
      simp only [restrictAut_apply] at this
      exact this
    · have := congrArg (fun τ : F₂ ≃ₐ[K] F₂ => ((τ ⟨x, hx⟩ : F₂) : Ω)) h₂
      simp only [restrictAut_apply] at this
      exact this
  exact AlgEquiv.ext fun x => Subtype.ext (congrArg (fun φ => φ x) key)

end Sup

section Tower

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

theorem ramificationIndex_dvd_of_le {F E : IntermediateField K Ω} [FiniteDimensional K F]
    [FiniteDimensional K E] (h : F ≤ E) : (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation F))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) ∣ (_root_.Ideal.ramificationIdx (_root_.IsLocalRing.maximalIdeal (_root_.Valuation.integer (_root_.ValuativeRel.valuation E))) (_root_.Valuation.integer (_root_.ValuativeRel.valuation K))) := by
  let : Algebra F E := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : ValuativeExtension F E := valuativeExtension_algHom (K := K) (IntermediateField.inclusion h)
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite K F E
  exact Dvd.intro _ (ramificationIndex_tower K F E).symm

theorem residueDegree_dvd_of_le {F E : IntermediateField K Ω} [FiniteDimensional K F]
    [FiniteDimensional K E] (h : F ≤ E) : ((IsLocalRing.maximalIdeal 𝒪[F]).inertiaDeg (𝒪[K])) ∣ ((IsLocalRing.maximalIdeal 𝒪[E]).inertiaDeg (𝒪[K])) := by
  let : Algebra F E := (IntermediateField.inclusion h).toRingHom.toAlgebra
  have : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : ValuativeExtension F E := valuativeExtension_algHom (K := K) (IntermediateField.inclusion h)
  exact Dvd.intro _ (residueDegree_tower K F E).symm

end Tower

namespace FormalGroup

section Unramified

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [IsSepClosed Ω]
variable {π : 𝒪[K]} (hπ : Irreducible π) {f : PowerSeries 𝒪[K]}

instance isGalois_sup (E₁ E₂ : IntermediateField K Ω) [IsGalois K E₁] [IsGalois K E₂] :
    IsGalois K (E₁ ⊔ E₂ : IntermediateField K Ω) :=
  isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

local instance lubinTateField_isGalois_of_card (hf : IsLubinTateSeries π f) (n : ℕ) :
    IsGalois K (lubinTateField Ω hπ hf n) :=
  IsGalois.of_card_aut_eq_finrank K _
    ((Nat.card_congr (lubinTateGalEquiv (Ω := Ω) hπ hf n).toEquiv).trans
      (card_units_quotient_eq_finrank (Ω := Ω) (hπ := hπ) hf n))

variable (hf : IsLubinTateSeries π f) {n : ℕ} (hn : 0 < n) {E : IntermediateField K Ω}
  (hE : IsUnramifiedSubextension E)


include hE hn in
theorem bijective_restrictAut_prod :
    haveI := hE.isGalois
    Function.Bijective ((restrictAut (le_sup_left (a := lubinTateField Ω hπ hf n) (b := E))).prod
      (restrictAut (le_sup_right (a := lubinTateField Ω hπ hf n) (b := E)))) := by
  have := hE.1
  have := hE.isGalois
  set M := lubinTateField Ω hπ hf n ⊔ E
  set Φ := (restrictAut (le_sup_left (a := lubinTateField Ω hπ hf n) (b := E))).prod
    (restrictAut (le_sup_right (a := lubinTateField Ω hπ hf n) (b := E)))
  have hinj : Function.Injective Φ := fun σ σ' h =>
    algEquiv_ext_sup (congrArg Prod.fst h) (congrArg Prod.snd h)
  refine hinj.bijective_of_nat_card_le ?_
  rw [Nat.card_prod, IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank,
    IsGalois.card_aut_eq_finrank]
  have he : ramificationIndex K (lubinTateField Ω hπ hf n) ∣ ramificationIndex K M :=
    ramificationIndex_dvd_of_le le_sup_left
  have hf' := residueDegree_dvd_of_le (le_sup_right (a := lubinTateField Ω hπ hf n) (b := E))
  rw [ramificationIndex_lubinTateField hπ hf hn] at he
  rw [residueDegree_eq_finrank_of_unramified K E hE.ramificationIndex_eq_one] at hf'
  rw [← ramificationIndex_mul_residueDegree K M]
  exact Nat.mul_le_mul (Nat.le_of_dvd (ramificationIndex_pos K M) he)
    (Nat.le_of_dvd (residueDegree_pos K M) hf')

variable [FiniteDimensional K E] {m : ℕ} (hEm : Module.finrank K E = m)


omit [IsSepClosed Ω] in
include hE hEm in
theorem frobenius_generates :
    (∀ σ : E ≃ₐ[K] E, σ ∈ Subgroup.zpowers (frobenius K E hE.ramificationIndex_eq_one)) ∧
      Nat.card (E ≃ₐ[K] E) = m := by
  refine ⟨fun σ => ?_, ?_⟩
  · rw [zpowers_frobenius]
    exact Subgroup.mem_top σ
  · rw [card_algEquiv_of_unramified K E hE.ramificationIndex_eq_one, hEm]

def lubinTateUnramifiedGalEquiv :
    ((lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω) ≃ₐ[K]
        (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω)) ≃*
      (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ × Multiplicative (ZMod m) :=
  haveI := hE.isGalois
  (MulEquiv.ofBijective _ (bijective_restrictAut_prod hπ hf hn hE)).trans
    (MulEquiv.prodCongr (lubinTateGalEquiv hπ hf n)
      (zmodMulEquivOfGenerator (frobenius_generates hE hEm).1
        (frobenius_generates hE hEm).2).symm)


include hn hE in
theorem lubinTateUnramified_mul_comm
    (σ τ : (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω) ≃ₐ[K]
      (lubinTateField Ω hπ hf n ⊔ E : IntermediateField K Ω)) :
    σ * τ = τ * σ :=
  (lubinTateUnramifiedGalEquiv hπ hf hn hE (m := Module.finrank K E) rfl).injective (by
    rw [map_mul, map_mul]
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_mul, Prod.fst_mul]
      exact mul_comm (G := (𝒪[K] ⧸ Ideal.span {π ^ n})ˣ) _ _
    · rw [Prod.snd_mul, Prod.snd_mul]
      exact mul_comm (G := Multiplicative (ZMod (Module.finrank K E))) _ _)

end Unramified

end FormalGroup

end GroundTheory.LocalField
end
end
