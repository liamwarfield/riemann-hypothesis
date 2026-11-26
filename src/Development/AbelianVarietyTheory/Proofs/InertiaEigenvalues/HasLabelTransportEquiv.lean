module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.H1MapSubgroup
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPlaceOverMoveValCc
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DenseFrobeniusSplitPlaces
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsReductionTeichmullerEmbeddingAtLocalisatio
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MaxUnramifiedActsOnLetterIdempotentImage
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousWittCbInclusionSmulWeakTopologyStatement
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PHomogeneousDifferenceLinear
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationAtRadiusConcaveContSlope
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationRadiusLaws
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachDeltaInvariantCoboundaries
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompactSpaceATopStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelTransportEquiv
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT
open Polynomial CategoryTheory

noncomputable section

namespace GlobalTheory.SerOSys.TranspLabel

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def permGL {α : Type} [Fintype α] [DecidableEq α] (π : α ≃ α) : GL α K :=
  ⟨π.symm.toPEquiv.toMatrix, π.toPEquiv.toMatrix, by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [PEquiv.toMatrix_apply, Matrix.one_apply], by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [PEquiv.toMatrix_apply, Matrix.one_apply]⟩

theorem glEquiv_perm {α : Type} [Fintype α] [DecidableEq α] (π : α ≃ α) (g : GL α K) :
    glEquiv K π g = permGL π * g * (permGL π)⁻¹ := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  show Matrix.reindex π π (g : Matrix α α K) =
    π.symm.toPEquiv.toMatrix * (g : Matrix α α K) * π.toPEquiv.toMatrix
  rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  rfl

def repIsoOf {G : Type} [Group G] (V W : FDRep ℂ G) (L : (V : Type) ≃ₗ[ℂ] (W : Type))
    (h : ∀ g v, L (V.ρ g v) = W.ρ g (L v)) : V ≅ W :=
  Action.mkIso (LinearEquiv.toFGModuleCatIso L) (fun g => by
    ext v
    exact h g v)

def rhoEquiv {G : Type} [Group G] (σ : FDRep ℂ G) (P : G) : (σ : Type) ≃ₗ[ℂ] (σ : Type) :=
  LinearEquiv.ofLinear (σ.ρ P) (σ.ρ P⁻¹)
    (LinearMap.ext fun v => by
      show (σ.ρ P * σ.ρ P⁻¹) v = v
      rw [← map_mul, mul_inv_cancel, map_one]; rfl)
    (LinearMap.ext fun v => by
      show (σ.ρ P⁻¹ * σ.ρ P) v = v
      rw [← map_mul, inv_mul_cancel, map_one]; rfl)

theorem rho_conj {G : Type} [Group G] (σ : FDRep ℂ G) (P X : G) (w : (σ : Type)) :
    σ.ρ P (σ.ρ X w) = σ.ρ (P * X * P⁻¹) (σ.ρ P w) := by
  rw [show σ.ρ (P * X * P⁻¹) (σ.ρ P w) = σ.ρ (P * X * P⁻¹ * P) w by rw [map_mul σ.ρ (P * X * P⁻¹) P]; rfl,
    inv_mul_cancel_right, map_mul]
  rfl

theorem lab_transp_transp {C : LabelConv K} (O : LabelMap K C) {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (σ : FDRep ℂ (GL α K)) (e : α ≃ β) (d : ℕ) (e₁ : α ≃ Fin d) (e₂ : β ≃ Fin d) :
    O.lab d (transp e₁ σ) = O.lab d (transp e₂ (transp e σ)) := by
  apply O.lab_iso
  let π : α ≃ α := e₁.trans (e.trans e₂).symm
  have hA : ∀ γ : GL (Fin d) K, (glEquiv K e).symm ((glEquiv K e₂).symm γ) =
      glEquiv K π ((glEquiv K e₁).symm γ) := by
    intro γ
    apply Units.ext
    ext i j
    simp [π, Formalism.L2.PT.coe_glEquiv_symm, Formalism.L2.PT.coe_glEquiv]
  refine ⟨repIsoOf _ _ (rhoEquiv σ (permGL π)) fun γ v => ?_⟩
  show σ.ρ (permGL π) (σ.ρ ((glEquiv K e₁).symm γ) v) =
    σ.ρ ((glEquiv K e).symm ((glEquiv K e₂).symm γ)) (σ.ρ (permGL π) v)
  rw [hA, glEquiv_perm]
  exact rho_conj σ _ _ v

theorem labO_transp {C : LabelConv K} (O : LabelMap K C) {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (e : α ≃ β) (σ : FDRep ℂ (GL α K)) :
    labO O (transp e σ) = labO O σ := by
  have key : ∀ (d : ℕ) (e₂ : β ≃ Fin d) (d' : ℕ) (e₁ : α ≃ Fin d'),
      O.lab d (transp e₂ (transp e σ)) = O.lab d' (transp e₁ σ) := by
    intro d e₂ d' e₁
    have hd : d = d' := by
      have h1 := Fintype.card_congr e₂
      have h2 := Fintype.card_congr e₁
      have h3 := Fintype.card_congr e
      simp only [Fintype.card_fin] at h1 h2
      omega
    subst hd
    exact (lab_transp_transp O σ e d e₁ e₂).symm
  exact key _ _ _ _

end GlobalTheory.SerOSys.TranspLabel

namespace GlobalTheory.SerOSys.TranspLabel

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

end GlobalTheory.SerOSys.TranspLabel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiedIsCrysDual
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.TiedDual

theorem tied_isCrys_dual : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsCrys (P.PD K) ρ → IsCrys (P.PD K) ρ.dual := by
  intro l _ P AI T hreg K LL V _ _ _ _ _ ρ hρ
  have := LL.2
  have : IsDomain P.R.B := GlobalTheory.RegularRing.isDomain_of_tied T K
  have e : ∀ (g : ↥(GK K)) z, (P.PD K).actB g z = P.actQ g z := fun g z => P.PD_actB K g z
  have hf : GlobalTheory.RegularRing.FracInv (P.PD K) := by
    intro x y hx h
    refine GlobalTheory.Per.FracInv.tied_frac_invariant l P AI T K y x hx fun g hg => ?_
    have h1 := h ⟨g, hg⟩
    rw [e, e] at h1
    rw [mul_comm, h1, mul_comm]
  have hu : GlobalTheory.RegularRing.LineUnit (P.PD K) := by
    intro b hb h
    refine hreg K b hb fun g hg => ?_
    obtain ⟨x, hx⟩ := h ⟨g, hg⟩
    exact ⟨x, by rw [← e ⟨g, hg⟩, hx, Algebra.smul_def]⟩
  exact GlobalTheory.RegularRing.dualCrys (P.PD K) ↥LL.1 hf hu V ρ hρ

end GlobalTheory.Per.TiedDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulLeJumpSumOfMemUpperRamificationNotMem
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulLeJumpSumOfMemUpperRamificationNotMem
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem card_mul_le_jumpSum_of_mem_upper_not_mem : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (B : Subgroup (L ≃ₐ[F] L)) (v : ℝ),
    lowerRamificationGroup F L 0 = ⊤ → ∀ σ ∈ upperRamificationGroup F L v, σ ∉ B →
      (Nat.card (L ≃ₐ[F] L) : ℝ) * v ≤ (jumpSum (wild F L) ⊤ B : ℝ) := by
  intro F L _ _ _ _ _ _ _ _ _ _ _ _ B v h0 σ hσ hσB
  have hσ1 : σ ≠ 1 := fun h ↦ hσB (h ▸ B.one_mem)
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (lowerIndex_ne_top (K := F) (L := L) hσ1)
  have hm1 : 1 ≤ m := by
    have : (1 : ℕ∞) ≤ lowerIndex F L σ := one_le_lowerIndex_iff.mpr (h0 ▸ Subgroup.mem_top σ)
    rw [← hm] at this
    exact_mod_cast this
  have hv := (mem_upperRamificationGroup_iff_of_lowerIndex_eq hm.symm).mp hσ
  have hcast : ((m : ℝ) - 1) = ((m - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hm1]; simp
  rw [hcast] at hv
  obtain ⟨hanti, hbot⟩ := GlobalTheory.T.wildLowerRamificationGroup_antitone_eventually_bot F L
  obtain ⟨n, hn⟩ := GlobalTheory.T.exists_initialSegment_not_inf_le_filtration (L ≃ₐ[F] L) (wild F L) ⊤ B hanti hbot
  have hjs := GlobalTheory.T.ramificationJumpSum_eq_sum_range (L ≃ₐ[F] L) (wild F L) ⊤ B n hanti hn
  have hphi := GlobalTheory.T.card_mul_herbrandPhi_natCast_totallyRamified F L h0 (m - 1)
  have hle : m - 1 ≤ n := by
    by_contra hlt
    push_neg at hlt
    have hmem : σ ∈ wild F L n := by
      rw [wild, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring,
        mem_lowerRamificationGroup_natCast_iff_lowerIndex, ← hm]
      exact_mod_cast (by omega : n + 1 + 1 ≤ m)
    have : ¬ (⊤ ⊓ wild F L n ≤ B) := fun h ↦ hσB (h ⟨Subgroup.mem_top σ, hmem⟩)
    exact lt_irrefl n ((hn n).mpr this)
  have hcard : (0 : ℝ) ≤ (Nat.card (L ≃ₐ[F] L) : ℝ) := Nat.cast_nonneg _
  calc (Nat.card (L ≃ₐ[F] L) : ℝ) * v ≤ (Nat.card (L ≃ₐ[F] L) : ℝ) * herbrandPhi F L ((m - 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hv hcard
    _ = ((∑ t ∈ Finset.range (m - 1), Nat.card ↥(wild F L t) : ℕ) : ℝ) := hphi
    _ ≤ (jumpSum (wild F L) ⊤ B : ℝ) := by
        rw [hjs]
        simp only [top_inf_eq]
        exact_mod_cast Finset.sum_le_sum_of_subset ((Finset.range_subset_range.mpr hle))

end GlobalTheory.PMon.Ram
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardMulLeJumpSumOfMemUpperRamificationNotMemStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_mul_le_jumpSum_of_mem_upperRamification_not_mem : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (B : Subgroup (L ≃ₐ[F] L)) (v : ℝ), lowerRamificationGroup F L 0 = ⊤ → ∀ σ ∈ upperRamificationGroup F L v, σ ∉ B → (Nat.card (L ≃ₐ[F] L) : ℝ) * v ≤ (jumpSum (wild F L) ⊤ B : ℝ) := by
  first | exact @GlobalTheory.PMon.Ram.card_mul_le_jumpSum_of_mem_upper_not_mem | exact GlobalTheory.PMon.Ram.card_mul_le_jumpSum_of_mem_upper_not_mem | (intros; apply GlobalTheory.PMon.Ram.card_mul_le_jumpSum_of_mem_upper_not_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoCrystallineExtensionCriterion
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoCrystallineExtensionCriterion
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.ExtCrysCrit

theorem cocycle_of_ext {G LL V₀ V₁ : Type} [Group G] [TopologicalSpace G] [Field LL] [TopologicalSpace LL]
    [AddCommGroup V₀] [Module LL V₀] [TopologicalSpace V₀] [ContinuousAdd V₀] [ContinuousSMul LL V₀]
    [AddCommGroup V₁] [Module LL V₁] [TopologicalSpace V₁] [IsModuleTopology LL V₁]
    (ρ₀ : Representation LL G V₀) (ρ₁ : Representation LL G V₁) (ι : V₀ →ₗ[LL] V₁)
    (hι : Function.Injective ι) (hιρ : ∀ g y, ι (ρ₀ g y) = ρ₁ g (ι y)) (x : V₁)
    (hx : Continuous fun g => ρ₁ g x) (c : G → V₀) (hc : ∀ g, ι (c g) = ρ₁ g x - x) :
    Continuous c ∧ ∀ g h, c (g * h) = c g + ρ₀ g (c h) := by
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective ι (LinearMap.ker_eq_bot.2 hι)
  have hrc : ∀ g, c g = r (ρ₁ g x) + (- r x) := by
    intro g
    rw [← sub_eq_add_neg, ← map_sub, ← hc, ← LinearMap.comp_apply, hr, LinearMap.id_apply]
  refine ⟨?_, fun g h => hι ?_⟩
  · have : c = fun g => r (ρ₁ g x) + (- r x) := funext hrc
    rw [this]
    exact ((IsModuleTopology.continuous_of_linearMap r).comp hx).add continuous_const
  · rw [map_add (f := _), hιρ, hc, hc, hc, map_mul, Module.End.mul_apply, map_sub]
    abel

theorem finrank_ext {LL V₀ V₁ V₂ : Type} [Field LL] [AddCommGroup V₀] [Module LL V₀] [AddCommGroup V₁]
    [Module LL V₁] [FiniteDimensional LL V₁] [AddCommGroup V₂] [Module LL V₂]
    (ι : V₀ →ₗ[LL] V₁) (π : V₁ →ₗ[LL] V₂) (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (hk : ∀ z, π z = 0 ↔ ∃ y, ι y = z) (h1 : Module.finrank LL V₂ = 1) :
    Module.finrank LL V₁ = Module.finrank LL V₀ + 1 := by
  have hk' : LinearMap.ker π = LinearMap.range ι := by
    ext z; rw [LinearMap.mem_ker, LinearMap.mem_range]; exact hk z
  have h := LinearMap.finrank_range_add_finrank_ker π
  rw [LinearMap.range_eq_top.2 hπ, finrank_top, hk', LinearMap.finrank_range_of_inj hι, h1] at h
  omega

theorem not_mem_range {LL V₀ V₁ V₂ : Type} [Field LL] [AddCommGroup V₀] [Module LL V₀] [AddCommGroup V₁]
    [Module LL V₁] [AddCommGroup V₂] [Module LL V₂]
    (ι : V₀ →ₗ[LL] V₁) (π : V₁ →ₗ[LL] V₂) (hk : ∀ z, π z = 0 ↔ ∃ y, ι y = z) (x : V₁) (hx : π x ≠ 0) :
    x ∉ LinearMap.range ι := by
  rintro ⟨y, rfl⟩
  exact hx ((hk _).2 ⟨y, rfl⟩)

theorem blochKato_ext_all : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm15 D := by
  intro D l _ K LL
  intro T Tp To ι π hses htriv hdim hcrys x hxT hπx c hc
  have key := GlobalTheory.CrysExtCrit.coboundary_iff_isCrys l (D.loc l) (D.locA l) (D.locT l) K LL T.V T.ρ Tp.V Tp.ρ ι.f ι.equiv hses.1
    (finrank_ext ι.f π.f hses.1 hses.2.1 hses.2.2.2.1 hdim) hcrys x
    (not_mem_range ι.f π.f hses.2.2.2.1 x hπx) c hc
  obtain ⟨hcont, hcoc⟩ := cocycle_of_ext T.ρ Tp.ρ ι.f hses.1 ι.equiv x (Tp.cont x) c hc
  exact ⟨fun h => key.1 h.2, fun h => ⟨⟨hcont, hcoc⟩, key.2 h⟩⟩

end GlobalTheory.ExtCrysCrit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoCrystallineExtensionCriterionStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKato_crystalline_extension_criterion : ∀ D : D7, Formalism.MainNotions.RamifiedCoefficientChains.adm15 D := by
  first | exact @GlobalTheory.ExtCrysCrit.blochKato_ext_all | exact GlobalTheory.ExtCrysCrit.blochKato_ext_all | (intros; apply GlobalTheory.ExtCrysCrit.blochKato_ext_all <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepIsoOfSimpleOfCentralIdempotentEq
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepIsoOfSimpleOfCentralIdempotentEq
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT
open Polynomial CategoryTheory

namespace GlobalTheory.SerOSys

theorem repIso_of_zIdem_eq_of_simple {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ)
    (h : Simple τ) (h' : Simple τ') (he : zIdem τ = zIdem τ') : RepIso τ.ρ τ'.ρ := by
  classical
  have hc0 : (Fintype.card Γ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have : Invertible (Nat.card Γ : ℂ) :=
    invertibleOfNonzero (by rw [Nat.card_eq_fintype_card]; exact hc0)
  have hco : ∀ γ, (Module.finrank ℂ τ : ℂ) * τ.character γ
      = (Module.finrank ℂ τ' : ℂ) * τ'.character γ := by
    intro γ
    have h1 := congrArg (fun z => z.coeff γ⁻¹) he
    simp only [zIdem_coeff, inv_inv] at h1
    have h2 := congrArg (fun x => (Fintype.card Γ : ℂ) * x) h1
    simp only [div_mul_eq_mul_div, mul_div_cancel₀ _ hc0, mul_div_assoc'] at h2
    simpa [FDRep.character, mul_div_cancel_left₀ _ hc0] using h2
  have hd : Module.finrank ℂ τ = Module.finrank ℂ τ' := by
    have h1 := hco 1
    rw [FDRep.char_one, FDRep.char_one] at h1
    have h2 : Module.finrank ℂ τ * Module.finrank ℂ τ
        = Module.finrank ℂ τ' * Module.finrank ℂ τ' := by exact_mod_cast h1
    exact Nat.mul_self_inj.1 h2
  have hs0 := FDRep.char_orthonormal τ τ
  rw [if_pos ⟨Iso.refl _⟩] at hs0
  have hpos : (Module.finrank ℂ τ : ℂ) ≠ 0 := by
    intro h0
    have h1 : Module.finrank ℂ τ = 0 := by exact_mod_cast h0
    have : Subsingleton τ := Module.finrank_zero_iff.1 h1
    have hz : ∀ g, τ.character g = 0 := fun g => by
      have : τ.ρ g = 0 := Subsingleton.elim _ _
      simp [FDRep.character, this]
    simp [hz] at hs0
  have hch : ∀ γ, τ'.character γ = τ.character γ := fun γ => by
    have h1 := hco γ
    rw [← hd] at h1
    exact (mul_left_cancel₀ hpos h1).symm
  have hs := FDRep.char_orthonormal τ τ'
  simp only [hch] at hs
  rw [hs0] at hs
  have hne : Nonempty (τ ≅ τ') := by
    by_contra hn
    rw [if_neg hn] at hs
    exact one_ne_zero hs
  obtain ⟨i⟩ := hne
  refine ⟨FDRep.isoToLinearEquiv i, fun γ v => ?_⟩
  rw [FDRep.Iso.conj_ρ i γ]
  simp [LinearEquiv.conj_apply]

end GlobalTheory.SerOSys
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepIsoOfSimpleOfCentralIdempotentEqStatement
open Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT GlobalTheory.SerOSys
open Polynomial CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.repIso_of_simple_of_centralIdempotent_eq : ∀ {Γ : Type} [Group Γ] [Fintype Γ] (τ τ' : FDRep ℂ Γ), Simple τ → Simple τ' → zIdem τ = zIdem τ' → RepIso τ.ρ τ'.ρ := by
  first | exact @GlobalTheory.SerOSys.repIso_of_zIdem_eq_of_simple | exact GlobalTheory.SerOSys.repIso_of_zIdem_eq_of_simple | (intros; apply GlobalTheory.SerOSys.repIso_of_zIdem_eq_of_simple <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonPiWachLatticeClosedWeak
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonPiWachLatticeClosedWeak
noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.WeakClosed
open scoped Topology

namespace GlobalTheory.WeakClosed

variable {l : ℕ} [Fact l.Prime]

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

theorem hausdorff_tilt_witt : letI := cbTop l; T2Space (Cb l) := by
  letI := cbValued l
  infer_instance

theorem ring_cb : letI := cbTop l; IsTopologicalRing (Cb l) := by
  letI := cbValued l
  infer_instance

theorem jD_piN_closed : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∃ τ : TopologicalSpace (TW (RW LL) T), letI := τ; T2Space (TW (RW LL) T) ∧ IsTopologicalAddGroup (TW (RW LL) T) ∧ (∀ b : TW (RW LL) T, Continuous (fun g : ↥(GK K) => TWact ((D.locA l).gRW LL (g : GQ l)) T g b)) ∧ Continuous (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ IsClosed (((F l).E K s LL h).tie.jD T '' (aN ((HW l).W K s LL h) T letπ : Set (((HW l).W K s LL h).DD T))) := by
  intro D HW F l _ K s LL h T _
  haveI := LL.2
  haveI : Module.Free ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.1
  haveI : Module.Finite ℤ_[l] ↥(OL LL) :=
    (GlobalTheory.Per.integers_completeDVR l LL).elim fun _ h => h.2.2.2.2.1
  obtain ⟨d, ⟨b⟩⟩ : ∃ d : ℕ, Nonempty (LatB T d) := GlobalTheory.Cyc.exists_basis_lat (R := ℤ_[l]) T
  let bO := Module.finBasis ℤ_[l] ↥(OL LL)
  letI τ := twTop T b
  letI tW : TopologicalSpace (WCb l) := wTop l
  letI := cbTop l
  haveI := hausdorff_tilt_witt (l := l)
  haveI := ring_cb (l := l)
  haveI : T2Space (WCb l) := GlobalTheory.WeakTop.t2Space_wittVector_product
  haveI : IsTopologicalRing (WCb l) := GlobalTheory.WeakTop.isTopologicalRing_witt
  letI := zlMod T
  haveI := zlTower T
  have hc : Continuous (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b) := continuous_induced_dom
  haveI hT2 : T2Space (TW (RW LL) T) :=
    T2Space.of_injective_continuous (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b).injective hc
  haveI hAG : IsTopologicalAddGroup (TW (RW LL) T) :=
    Topology.IsInducing.topologicalAddGroup (GlobalTheory.WeakTop.coords (WCb l) ↥(OL LL) b) ⟨rfl⟩
  refine ⟨τ, hT2, hAG, GlobalTheory.T.continuous_galois_orbit_wittTensorLatticeWeakTopology (D.locA l) T b, GlobalTheory.T.continuous_one_tmul_latB T b, ?_⟩
  obtain ⟨r, y, hy⟩ := GlobalTheory.T.exists_image_aN_eq_range_sum ((F l).E K s LL h) T
  rw [hy]
  letI := aTop (K := K) bO
  haveI := GlobalTheory.T.compactSpace_aTop' (K := K) bO
  refine (isCompact_range ?_).isClosed
  refine continuous_finsetSum _ fun i _ => ?_
  exact (GlobalTheory.T.continuous_wittCbInclusion_smul_weakTopology ((F l).E K s LL h) T b bO (y i)).comp (continuous_apply i)

end GlobalTheory.WeakClosed
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleComparisonPiWachLatticeClosedWeakStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleComparison_pi_wachLattice_closed_weak : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (T : Lt K LL), IsCrys ((D.loc l).PD K) T.ρ → ∃ τ : TopologicalSpace (TW (RW LL) T), letI := τ; T2Space (TW (RW LL) T) ∧ IsTopologicalAddGroup (TW (RW LL) T) ∧ (∀ b : TW (RW LL) T, Continuous (fun g : ↥(GK K) => TWact ((D.locA l).gRW LL (g : GQ l)) T g b)) ∧ Continuous (fun t : ↥T.L.T => (1 : RW LL) ⊗ₜ[↥(OL LL)] t) ∧ IsClosed (((F l).E K s LL h).tie.jD T '' (aN ((HW l).W K s LL h) T letπ : Set (((HW l).W K s LL h).DD T))) := by
  first | exact @GlobalTheory.WeakClosed.jD_piN_closed | exact GlobalTheory.WeakClosed.jD_piN_closed | (intros; apply GlobalTheory.WeakClosed.jD_piN_closed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationSubEqIntMulRadius
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationSubEqIntMulRadius
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

namespace GlobalTheory.PMon.Gauss

theorem vr_iterate_phi (l : ℕ) [Fact l.Prime] (x : Formalism.Per.Acris l) (hx : x ≠ 0) :
    ∀ k : ℕ, (φc l)^[k] x ≠ 0 ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      vr l r ((φc l)^[k] x) = (l : ℝ) ^ k * vr l (r / (l : ℝ) ^ k) x := by
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_lt.le
  have hl0 : (0 : ℝ) < l := by linarith
  intro k
  induction k with
  | zero => simp [hx]
  | succ k ih =>
    obtain ⟨hne, hv⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨((GlobalTheory.T.acrisValuation_radius_laws l 1 one_pos le_rfl).2.1 _ hne).1, ?_⟩
    intro r hr0 hr1
    rw [((GlobalTheory.T.acrisValuation_radius_laws l r hr0 hr1).2.1 _ hne).2]
    have h1 : 0 < r / l := div_pos hr0 hl0
    have h2 : r / l ≤ 1 := by rw [div_le_one hl0]; linarith
    rw [hv (r / l) h1 h2, pow_succ]
    have e : r / (l : ℝ) / (l : ℝ) ^ k = r / ((l : ℝ) ^ k * l) := by rw [div_div, mul_comm]
    rw [e]
    ring

theorem vr_sub_eq_int_mul : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ w w' : Formalism.Per.Acris l,
    (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w ≠ 0 → w' ≠ 0 →
    φc l w * w' = w * φc l w' → ∃ n : ℤ, ∀ r ∈ Set.Ioc (0 : ℝ) 1, vr l r w - vr l r w' = n * r := by
  intro l _ h s hsh w w' hfix hw hw' hrat
  have hl2 : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  obtain ⟨cA, kA, sA⟩ := GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l w hw
  obtain ⟨cB, kB, sB⟩ := GlobalTheory.T.acrisValuationAtRadius_concave_cont_slope l w' hw'
  have key := GlobalTheory.T.exists_int_sub_mul_eq_int_mul_of_homogeneous l h s 1 hl2 hsh le_rfl (fun r => vr l r w) (fun r => vr l r w')
    cA cB kA kB sA sB ?_ ?_
  · obtain ⟨n, hn⟩ := key
    exact ⟨n, fun r hr => by simpa using hn r hr⟩
  · rintro r ⟨hr0, hr1⟩
    have e1 := (vr_iterate_phi l w' hw' h).2 r hr0 hr1
    rw [hfix, (GlobalTheory.T.acrisValuation_radius_laws l r hr0 hr1).2.2.1 w' s hw'] at e1
    show (l : ℝ) ^ h * vr l (r / (l : ℝ) ^ h) w' = vr l r w' + s * r
    linarith
  · rintro r ⟨hr0, hr1⟩
    have hlr0 : 0 < (l : ℝ) * r := mul_pos hl0 hr0
    have hlr1 : (l : ℝ) * r ≤ 1 := by rw [le_div_iff₀ hl0] at hr1; linarith
    obtain ⟨hmul, hphi, -, -⟩ := GlobalTheory.T.acrisValuation_radius_laws l (l * r) hlr0 hlr1
    have e := congrArg (vr l (l * r)) hrat
    rw [hmul _ _ (hphi w hw).1 hw', hmul _ _ hw (hphi w' hw').1, (hphi w hw).2,
      (hphi w' hw').2] at e
    have hc : (l : ℝ) * r / l = r := by field_simp
    rw [hc] at e
    show vr l (l * r) w - ((1 : ℕ) : ℝ) * vr l (l * r) w' = l * (vr l r w - ((1 : ℕ) : ℝ) * vr l r w')
    simp only [Nat.cast_one, one_mul]
    linarith

end GlobalTheory.PMon.Gauss
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisValuationSubEqIntMulRadiusStatement
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acrisValuation_sub_eq_int_mul_radius : ∀ (l : ℕ) [Fact l.Prime] (h s : ℕ), s < h → ∀ w w' : Formalism.Per.Acris l, (φc l)^[h] w' = (l : Formalism.Per.Acris l) ^ s * w' → w ≠ 0 → w' ≠ 0 → φc l w * w' = w * φc l w' → ∃ n : ℤ, ∀ r ∈ Set.Ioc (0 : ℝ) 1, vr l r w - vr l r w' = n * r := by
  first | exact @GlobalTheory.PMon.Gauss.vr_sub_eq_int_mul | exact GlobalTheory.PMon.Gauss.vr_sub_eq_int_mul | (intros; apply GlobalTheory.PMon.Gauss.vr_sub_eq_int_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimOfQlDimensionFormula
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimOfQlDimensionFormula
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

noncomputable section

namespace GlobalTheory.BkCoeff

open GlobalTheory.PstCoeff

theorem isModuleTopology_of_tower (R LL V : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Field LL] [Algebra R LL] [TopologicalSpace LL] [IsTopologicalRing LL] [IsModuleTopology R LL]
    [AddCommGroup V] [Module LL V] [Module R V] [IsScalarTower R LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [IsModuleTopology LL V] : IsModuleTopology R V := by
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd LL V
  let e : V ≃ₗ[LL] (Fin (finrank LL V) → LL) := (Module.finBasis LL V).equivFun
  have h1 : Continuous e := IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have h2 : Continuous e.symm := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
  let e' : (Fin (finrank LL V) → LL) ≃L[R] V :=
    { e.symm.restrictScalars R with continuous_toFun := h2, continuous_invFun := h1 }
  exact IsModuleTopology.iso e'

section Coeff

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
  {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  (ρ : Representation LL ↥(GK K) V)

theorem actVB_resQ (g : ↥(GK K)) (x : V ⊗[ℚ_[l]] P.R.B) :
    actVB (P.PD K) (resQ ρ) g x = actVB (P.PD K) ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem galoisInvariants_restrictScalarsToQl : H0V (resQ ρ) = (H0V ρ).restrictScalars ℚ_[l] := by
  ext x
  simp [H0V, Submodule.mem_iInf, sub_eq_zero]

theorem FilV_resQ (a : ℤ) :
    FilV (P.PD K) (LL := ℚ_[l]) (V := V) a = (FilV (P.PD K) (LL := LL) (V := V) a).restrictScalars ℚ_[l] := by
  have h : ∀ y, AlgebraTensorModule.map (LinearMap.id : V →ₗ[ℚ_[l]] V)
      (((P.PD K).Fil a).restrictScalars ℚ_[l]).subtype y =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (((P.PD K).Fil a).restrictScalars ℚ_[l]).subtype y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  ext x
  simp only [FilV, Submodule.restrictScalars_mem, LinearMap.mem_range, h]

variable [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V] [ContinuousConstSMul ℚ_[l] V]

theorem mem_finiteCocycles_restrictScalars_Ql (c : ↥(GK K) → V) : c ∈ finiteCocycles (P.PD K) (resQ ρ) ↔ c ∈ finiteCocycles (P.PD K) ρ := by
  show (c ∈ continuousCocycles (resQ ρ) ∧ ∃ x, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) (resQ ρ) g x - x) ↔
    (c ∈ continuousCocycles ρ ∧ ∃ x, ∀ g, c g ⊗ₜ[ℚ_[l]] (1 : P.R.B) = actVB (P.PD K) ρ g x - x)
  simp only [actVB_resQ]
  exact Iff.rfl

def finiteCocyclesResEquiv : ↥(finiteCocycles (P.PD K) (resQ ρ)) ≃ₗ[ℚ_[l]] ↥(finiteCocycles (P.PD K) ρ) where
  toFun x := ⟨x.1, (mem_finiteCocycles_restrictScalars_Ql P ρ x.1).mp x.2⟩
  invFun x := ⟨x.1, (mem_finiteCocycles_restrictScalars_Ql P ρ x.1).mpr x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def h1fEquiv : FiniteCohomology (P.PD K) (resQ ρ) ≃ₗ[ℚ_[l]] FiniteCohomology (P.PD K) ρ :=
  (Submodule.Quotient.equiv _ (((B1 ρ).comap (finiteCocycles (P.PD K) ρ).subtype).restrictScalars ℚ_[l]) (finiteCocyclesResEquiv P ρ) (by
    rw [Submodule.map_equiv_eq_comap_symm]
    ext x
    exact Iff.rfl)).trans (Submodule.Quotient.restrictScalarsEquiv ℚ_[l] _)

end Coeff

end GlobalTheory.BkCoeff

namespace GlobalTheory

open GlobalTheory.PstCoeff GlobalTheory.BkCoeff

theorem bkADim_of_dimFormula : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l),
    GlobalTheory.Published.BlochKato.DimFormula (P.PD K) → Formalism.MainNotions.LocalSituation.bkADim (P.PD K) := by
  intro l _ P K hD LL _ _ _ O _ _ hO A hdR
  obtain ⟨-, hfin, hmt, htr, -⟩ := hO
  haveI := hfin
  haveI := hmt
  haveI := htr
  haveI : FiniteDimensional ℚ_[l] A.V := Module.Finite.trans LL A.V
  haveI : IsModuleTopology ℚ_[l] A.V := isModuleTopology_of_tower ℚ_[l] LL A.V
  obtain ⟨-, he⟩ := hD A.V (resQ (LL := LL) A.ρ) A.cont ((isDR_resQ_iff P A.ρ).mpr hdR)
  have hH1 : finrank ℚ_[l] (FiniteCohomology (P.PD K) (resQ A.ρ)) = finrank ℚ_[l] LL * finrank LL (FiniteCohomology (P.PD K) A.ρ) := by
    rw [(h1fEquiv P A.ρ).finrank_eq, finrank_mul_finrank]
  have hH0 : finrank ℚ_[l] ↥(H0V (resQ A.ρ)) = finrank ℚ_[l] LL * finrank LL ↥(H0V A.ρ) := by
    rw [galoisInvariants_restrictScalarsToQl, finrank_mul_finrank]
    rfl
  have hdR' : finrank ℚ_[l] ↥(DdR (P.PD K) (resQ A.ρ)) = finrank ℚ_[l] LL * finrank LL ↥(DdR (P.PD K) A.ρ) := by
    rw [DdR_resQ, finrank_mul_finrank]
    rfl
  have hF : finrank ℚ_[l] ↥(DdR (P.PD K) (resQ A.ρ) ⊓ FilV (P.PD K) (LL := ℚ_[l]) (V := A.V) 0) =
      finrank ℚ_[l] LL * finrank LL ↥(DdR (P.PD K) A.ρ ⊓ FilV (P.PD K) (LL := LL) (V := A.V) 0) := by
    rw [DdR_resQ, FilV_resQ P (LL := LL), ← Submodule.restrictScalars_inf, finrank_mul_finrank]
    rfl
  rw [hH1, hH0, hdR', hF] at he
  push_cast at he
  have hd : (finrank ℚ_[l] LL : ℤ) ≠ 0 := by exact_mod_cast (Module.finrank_pos (R := ℚ_[l]) (M := LL)).ne'
  refine mul_left_cancel₀ hd ?_
  rw [he]
  ring

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlochKatoDimOfQlDimensionFormulaStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blochKatoDim_of_Ql_dimensionFormula : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), GlobalTheory.Published.BlochKato.DimFormula (P.PD K) → Formalism.MainNotions.LocalSituation.bkADim (P.PD K) := by
  first | exact @GlobalTheory.bkADim_of_dimFormula | exact GlobalTheory.bkADim_of_dimFormula | (intros; apply GlobalTheory.bkADim_of_dimFormula <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoGaloisInvariantsTorsionCoeffOfSelmerSetup
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoGaloisInvariantsTorsionCoeffOfSelmerSetup
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published

namespace GlobalTheory.NoGlobalInv

theorem sub_one_mem_of_pow {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {l : ℕ} (hp : l.Prime)
    (hl : (l : Λ) ∈ IsLocalRing.maximalIdeal Λ) (u : Λ) {n : ℕ} (hu : u ^ (l ^ n) = 1) :
    u - 1 ∈ IsLocalRing.maximalIdeal Λ := by
  haveI := Fact.mk hp
  have h0 : ((l : ℕ) : IsLocalRing.ResidueField Λ) = 0 := by
    rw [← map_natCast (IsLocalRing.residue Λ)]
    exact (IsLocalRing.residue_eq_zero_iff _).2 hl
  haveI : CharP (IsLocalRing.ResidueField Λ) l := (CharP.charP_iff_prime_eq_zero hp).2 h0
  rw [← IsLocalRing.residue_eq_zero_iff]
  have h1 : (IsLocalRing.residue Λ u - 1) ^ (l ^ n) = 0 := by
    rw [sub_pow_char_pow, ← map_pow, hu]; simp
  simpa using pow_eq_zero_iff (pow_pos hp.pos n).ne' |>.1 h1

theorem exists_socle {Λ M : Type} [CommRing Λ] [AddCommGroup M] [Module Λ M] (I : Ideal Λ) (S : Submodule Λ M) :
    ∀ (n : ℕ) (x : M), x ∈ S → x ≠ 0 → (∀ a ∈ I ^ n, a • x = 0) →
      ∃ y ∈ S, y ≠ 0 ∧ ∀ a ∈ I, a • y = 0 := by
  intro n
  induction n with
  | zero => intro x _ hx h; exact absurd (by simpa using h 1 (by simp)) hx
  | succ n ih =>
    intro x hS hx h
    by_cases h1 : ∀ a ∈ I, a • x = 0
    · exact ⟨x, hS, hx, h1⟩
    push Not at h1
    obtain ⟨a, ha, hax⟩ := h1
    refine ih (a • x) (S.smul_mem a hS) hax fun b hb => ?_
    rw [smul_smul]
    exact h _ (by rw [pow_succ]; exact Ideal.mul_mem_mul hb ha)

theorem eq_zero_of_span {Γ O Λ B : Type} [CommRing O] [IsLocalRing O] [CommRing Λ] [Algebra O Λ]
    [AddCommGroup B] [Module Λ B] {r : ℕ} (hr : 2 ≤ r) (ρ : Γ → Matrix (Fin r) (Fin r) O)
    (hρ : Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => (ρ g).map (IsLocalRing.residue O)) = ⊤)
    (x : Fin r → B) (hx : ∀ a ∈ IsLocalRing.maximalIdeal O, ∀ j, algebraMap O Λ a • x j = 0)
    (hs : ∀ g, ∃ c : O, ∀ p, ∑ q, algebraMap O Λ (ρ g p q) • x q = algebraMap O Λ c • x p) : x = 0 := by
  classical
  have key : ∀ M : Matrix (Fin r) (Fin r) (IsLocalRing.ResidueField O), ∃ A : Matrix (Fin r) (Fin r) O,
      A.map (IsLocalRing.residue O) = M ∧
        ∃ c : O, ∀ p, ∑ q, algebraMap O Λ (A p q) • x q = algebraMap O Λ c • x p := by
    intro M
    have hM : M ∈ Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => (ρ g).map (IsLocalRing.residue O)) := hρ ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem M h => obtain ⟨g, rfl⟩ := h; exact ⟨ρ g, rfl, hs g⟩
    | zero => exact ⟨0, by ext; simp, 0, by simp⟩
    | add M M' _ _ h h' =>
      obtain ⟨A, rfl, c, hc⟩ := h
      obtain ⟨A', rfl, c', hc'⟩ := h'
      refine ⟨A + A', by ext; simp, c + c', fun p => ?_⟩
      simp only [Matrix.add_apply, map_add (f := _), add_smul, Finset.sum_add_distrib, hc, hc']
    | smul t M _ h =>
      obtain ⟨A, rfl, c, hc⟩ := h
      obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective t
      refine ⟨t • A, by ext; simp, t * c, fun p => ?_⟩
      simp only [Matrix.smul_apply, smul_eq_mul, map_mul, mul_smul, ← Finset.smul_sum, hc]
  have key2 : ∀ A : Matrix (Fin r) (Fin r) O,
      ∃ c : O, ∀ p, ∑ q, algebraMap O Λ (A p q) • x q = algebraMap O Λ c • x p := by
    intro A
    obtain ⟨A', hA, c, hc⟩ := key (A.map (IsLocalRing.residue O))
    refine ⟨c, fun p => ?_⟩
    rw [← hc]
    refine Finset.sum_congr rfl fun q _ => ?_
    have : A p q - A' p q ∈ IsLocalRing.maximalIdeal O := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact (congrFun (congrFun hA p) q).symm
    have := hx _ this q
    rwa [map_sub, sub_smul, sub_eq_zero] at this
  funext b
  haveI : Nontrivial (Fin r) := Fin.nontrivial_iff_two_le.2 hr
  obtain ⟨a, hab⟩ := exists_ne b
  obtain ⟨c, hc⟩ := key2 (Matrix.single a b 1)
  obtain ⟨c', hc'⟩ := key2 (Matrix.single b b 1)
  have h1 := hc a
  have h2 := hc' a
  have h3 := hc' b
  simp [Matrix.single_apply, hab.symm, apply_ite, ite_smul] at h1 h2 h3
  rw [Pi.zero_apply, h3, h1, smul_comm, ← h2, smul_zero]

theorem invariants_eq_bot {Γ O Λ B : Type} [Group Γ] [CommRing O] [IsLocalRing O] [CommRing Λ] [IsLocalRing Λ]
    [Algebra O Λ] [AddCommGroup B] [Module Λ B] {r : ℕ} (hr : 2 ≤ r) (ρ : Γ →* GL (Fin r) O) (χ : Γ →* Oˣ)
    (κ : Γ →* Λˣ) (hloc : IsLocalHom (algebraMap O Λ))
    (hρ : Submodule.span (IsLocalRing.ResidueField O)
      (Set.range fun g => (ρ g : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) = ⊤)
    (hκ : ∀ g, ((κ g : Λˣ) : Λ) - 1 ∈ IsLocalRing.maximalIdeal Λ) (hB : Tors Λ B) :
    (repOn (twGL ρ χ) κ B).invariants = ⊥ := by
  have hm : ∀ a ∈ IsLocalRing.maximalIdeal O, algebraMap O Λ a ∈ IsLocalRing.maximalIdeal Λ :=
    fun a ha hu => ha (hloc.map_nonunit a hu)
  rw [eq_bot_iff]
  intro x hx
  by_contra hx0
  choose n hn using fun j => hB (x j)
  obtain ⟨y, hy, hy0, hym⟩ := exists_socle (IsLocalRing.maximalIdeal Λ) _
    (Finset.univ.sup n) x hx hx0 (fun a ha => funext fun j =>
      hn j a (Ideal.pow_le_pow_right (Finset.le_sup (Finset.mem_univ j)) ha))
  refine hy0 (eq_zero_of_span (O := O) (Λ := Λ) hr (fun g => (ρ g : Matrix (Fin r) (Fin r) O)) hρ y
    (fun a ha j => congrFun (hym _ (hm a ha)) j) fun g => ⟨(χ g : O), fun p => ?_⟩)
  have hk' : ∀ q, ((κ g : Λˣ) : Λ) • y q = y q := fun q => by
    have := congrFun (hym _ (hκ g)) q
    rwa [Pi.smul_apply, sub_smul, one_smul, Pi.zero_apply, sub_eq_zero] at this
  have hg : ((κ g : Λˣ) : Λ) • ∑ q, algebraMap O Λ ((twGL ρ χ g : Matrix (Fin r) (Fin r) O) p q) • y q = y p :=
    congrFun (hy g) p
  rw [← hg, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [smul_comm ((κ g : Λˣ) : Λ), hk', smul_smul, ← map_mul]
  congr 2
  simp [twGL, scalGL, Matrix.diagonal_mul]

theorem noInv (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X)
    (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ)
    (Q : Finset (PlE D.host)) (h : Setup bkP i s κ Q) : NoInv i s κ := by
  intro B _ _ _ _ hB
  have hloc := h.2.1
  have hr : 100 ≤ D.R.r := h.1.2.2.2.2.2.2
  have hl0 : ((X.l i : ℕ) : X.O0 i) ∈ IsLocalRing.maximalIdeal (X.O0 i) := fun hu =>
    X.O_l i (by simpa using hu.map (algebraMap (X.O0 i) (X.O i)))
  have hl : ((X.l i : ℕ) : Λ) ∈ IsLocalRing.maximalIdeal Λ := fun hu =>
    hl0 (hloc.map_nonunit _ (by simpa using hu))
  refine invariants_eq_bot (by omega) (X.rhoS i s) (chiS i s) κ hloc h.1.2.1.1 (fun g => ?_) hB
  obtain ⟨m, hgm⟩ := h.2.2.2.2.1 g
  exact sub_one_mem_of_pow (X.lPrime i).out hl _ (n := m)
    (by rw [← Units.val_pow_eq_pow_val, hgm, Units.val_one])

end GlobalTheory.NoGlobalInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NoGaloisInvariantsTorsionCoeffOfSelmerSetupStatement
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.noGaloisInvariantsTorsionCoeff_of_selmerSetup : ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i) (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [Algebra (X.O0 i) Λ] (κ : GE N →* Λˣ) (Q : Finset (PlE D.host)), Setup bkP i s κ Q → NoInv i s κ := by
  first | exact @GlobalTheory.NoGlobalInv.noInv | exact GlobalTheory.NoGlobalInv.noInv | (intros; apply GlobalTheory.NoGlobalInv.noInv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubstInvariants
open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.SenLines GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen GlobalTheory.CycFr GlobalTheory.WachTie

namespace GlobalTheory.SenLines

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) {l : ℕ}

theorem isUnit_q_of_associated {m : ℕ} (h : Associated W.π₀₁ (X ^ m)) :
    IsUnit (algebraMap (LetA O n) W.EE (W.π₀ + ((PD.p : ℕ) : LetA O n))) := by
  obtain ⟨w, hw⟩ := h.symm
  have e : (W.π₀ : LetA O n) = letπ ^ m * fun _ => (w : O⟦X⟧) := funext fun _ => hw.symm
  have hu : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
    rw [e, map_mul, map_pow]
    exact (W.EE_π.pow _).mul (IsUnit.map _ (Pi.isUnit_iff.2 fun _ => w.isUnit))
  haveI := W.EE_complete
  have hJ := IsAdicComplete.le_jacobson_bot (Ideal.span {((PD.p : ℕ) : W.EE)})
    (Ideal.mem_span_singleton_self _)
  obtain ⟨u, hu⟩ := hu
  have h1 := (Ideal.mem_jacobson_bot.1 hJ (↑u⁻¹ : W.EE)).mul u.isUnit
  rw [map_add (f := _), map_natCast, ← hu]
  convert h1 using 1
  rw [add_mul, mul_assoc, Units.inv_mul]; ring

variable [Fact l.Prime] [IsDomain O] [CharZero O] [Algebra ℤ_[l] O] (hp : PD.p = l)
  (χ : W.Gam →* ℤ_[l]ˣ) (hχ : ∀ g, algebraMap ℤ_[l] O (χ g : ℤ_[l]) = (W.χΓ g : O))
include hp hχ

theorem exists_subst_invariants (ξ : O⟦X⟧) (hξ : Associated ξ (X ^ W.DelF.card))
    (h0 : constantCoeff ξ = 0) (hinv : ∀ δ ∈ W.DelF, W.γ₀ δ ξ = ξ) :
    ∃ j : O⟦X⟧ →ₐ[O] O⟦X⟧, j X = ξ ∧ Function.Injective j ∧
      ∀ a, (∃ b, j b = a) ↔ ∀ δ ∈ W.DelF, W.γ₀ δ a = a := by
  classical
  have hγ := γ₀_eq W hp χ hχ
  have hχi : Function.Injective χ := fun a b hab =>
    W.χΓ_inj (Units.ext (by rw [← hχ, ← hχ, hab]))
  let Δ : Subgroup ℤ_[l]ˣ := (CommGroup.torsion W.Gam).map χ
  have hΔ : (Δ : Set ℤ_[l]ˣ) = ↑(W.DelF.image χ) := by
    ext x
    simp only [Δ, Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, CommGroup.mem_torsion,
      Finset.coe_image, Finset.mem_coe, mem_DelF_iff]
  have hfa : ∀ p : ℤ_[l]ˣ → Prop, (∀ δ ∈ Δ, p δ) ↔ ∀ δ ∈ W.DelF, p (χ δ) := by
    intro p
    simp only [← SetLike.mem_coe, hΔ, Finset.coe_image, Set.forall_mem_image]
  haveI : Finite Δ := by
    change Finite (Δ : Set ℤ_[l]ˣ)
    rw [hΔ]; infer_instance
  have hcard : Nat.card Δ = W.DelF.card := by
    change Nat.card (Δ : Set ℤ_[l]ˣ) = _
    rw [hΔ, Nat.card_coe_set_eq, Set.ncard_coe_finset, Finset.card_image_of_injective _ hχi]
  have hs : HasSubst ξ := HasSubst.of_constantCoeff_zero' h0
  have hX : (substAlgHom hs : O⟦X⟧ →ₐ[O] O⟦X⟧) X = ξ := by rw [coe_substAlgHom, subst_X hs]
  obtain ⟨h2, h3⟩ := injective_and_range_eq_invariants Δ (substAlgHom hs : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (by rw [hX, hcard]; exact hξ)
    ((hfa _).2 fun δ hδ => by rw [← hγ, hX]; exact hinv δ hδ)
  refine ⟨_, hX, h2, fun a => ?_⟩
  rw [h3, hfa]; simp only [hγ]

theorem exists_qFrame_of_card [IsNoetherianRing O] (hl : l ≠ 2) (hc : W.DelF.card = l - 1)
    (σ : O⟦X⟧ ≃ₐ[O] O⟦X⟧) (hσ : σ X = X + C (l : O)) (g : W.Gam)
    (hg : (l : ℤ_[l]) ∣ (χ g : ℤ_[l]) - 1) : ∃ J, QFrame W g J := by
  have h2l := (Fact.out : l.Prime).two_le
  have hl0 : (l : O) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨p2, p3, w, hw⟩ := π₀₁_spec W hp χ hχ hl hc
  have hq := (φ₀_eq W hp).2
  have hγ := γ₀_eq W hp χ hχ
  have hX0 : (X : O⟦X⟧) ∣ W.π₀₁ := (dvd_pow_self _ (by omega)).trans p2.symm.dvd
  have h0 := X_dvd_iff.1 hX0
  obtain ⟨j, hj, hji, hjr⟩ := exists_subst_invariants W hp χ hχ _ p2 h0 p3
  let J : O⟦X⟧ →ₐ[O] O⟦X⟧ := j.comp σ
  have hJ : ∀ c, J c = j (σ c) := fun _ => rfl
  have hσ' : σ X = X + (l : O⟦X⟧) := by rw [hσ, map_natCast]
  have hJX : J X = W.π₀₁ + (l : O⟦X⟧) := by rw [hJ, hσ', map_add (f := _), hj, map_natCast]
  have hσl : σ (X - (l : O⟦X⟧)) = X := by rw [map_sub, hσ', map_natCast]; ring
  have hr : ∀ a, (∃ b, J b = a) ↔ ∀ δ ∈ W.DelF, W.γ₀ δ a = a := fun a => by
    rw [← hjr]
    exact ⟨fun ⟨b, hb⟩ => ⟨σ b, hb⟩, fun ⟨b, hb⟩ => ⟨σ.symm b, by rw [hJ, σ.apply_symm_apply, hb]⟩⟩
  have hk : ∀ c, constantCoeff (J c) = 0 → X - (l : O⟦X⟧) ∣ c := fun c h => by
    rw [hJ, constantCoeff_algHom j (hj ▸ hX0)] at h
    rw [← map_dvd_iff σ, hσl, X_dvd_iff, h]
  have hc0 : constantCoeff (J X) = (l : O) := by rw [hJX, map_add (f := _), h0, map_natCast, zero_add]
  have hwu : IsUnit w := by
    have h1 := congrArg constantCoeff hw
    rw [← hJX, hc0, map_mul, show constantCoeff (lvl l O 0) = (l : O) by simp [lvl]] at h1
    rw [isUnit_iff_constantCoeff, ← mul_left_cancel₀ hl0 ((mul_one _).trans h1)]
    exact isUnit_one
  have hass : Associated (J X) (lvl l O 0) := by
    rw [hJX, hw]; exact associated_mul_unit_left _ _ hwu
  have hne : J X ≠ 0 := fun h => hl0 (by rw [← hc0, h, map_zero])
  obtain ⟨y, hy⟩ : J X * X ∣ W.γ₀ g (J X) - J X := by
    have h1 := dvd_act_sub (O := O) 1 (χ g) 1 (by rwa [pow_one]) (J X)
    have h2 := mul_lvl (l := l) (O := O) 0
    rw [pow_zero, pow_one, add_sub_cancel_left, zero_add] at h2
    rw [act_one, ← hγ, ← h2, mul_comm] at h1
    exact (mul_dvd_mul_right hass.dvd _).trans h1
  have hinv := (hr (J X)).1 ⟨X, rfl⟩
  obtain ⟨y', hy'⟩ := (hr (X * y)).2 fun δ hδ => by
    apply mul_left_cancel₀ hne
    have h1 := congrArg (W.γ₀ δ) hy
    rw [mul_assoc, map_mul, map_sub, hinv δ hδ, hγ δ, hγ g, act_comm, ← hγ δ, hinv δ hδ,
      ← hγ g, hy, mul_assoc] at h1
    exact h1.symm
  obtain ⟨z, hz⟩ := hk y' (by rw [hy']; simp)
  have hs : IsUnit (1 + y') := by
    rw [← MulEquiv.isUnit_map σ, hz, map_add (f := _), map_mul, hσl, isUnit_iff_constantCoeff]
    simp
  refine ⟨J, hji.comp σ.injective, hr, by rw [hp, hJX], by rw [hp]; exact hk,
    ⟨hs.unit, ?_, ?_⟩, hq ▸ hass, isUnit_q_of_associated W p2⟩
  · rw [hs.unit_spec, map_add (f := _), map_one, hy']
    linear_combination hy
  · rw [hp, hs.unit_spec, add_sub_cancel_left]
    exact ⟨z, hz⟩

end Generic

theorem exists_qFrame : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ} (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n) (g : W.Gam), CaseA K LL → ((W.χΓ g : (↥(OL LL))ˣ) : ↥(OL LL)) = 1 + (l : ↥(OL LL)) → IsUnit (W.DelF.card : ↥(OL LL)) ∧ ∃ J, QFrame W g J := by
  intro l _ P K LL n W g ⟨hK, hl, h⟩ hg
  have p1 : Module.finrank ↥(K0 K) ↥K.1 = 1 := by
    rw [Algebra.finrank_eq_one_iff_bijective_algebraMap]
    exact ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, x.2, hK x.2⟩, rfl⟩⟩
  have hc := GlobalTheory.TorsionCard.card_torsion_mul_finrank P K LL W hl h.2.2.1
  rw [p1, mul_one] at hc
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.exists_cyclotomicChar_padicInt_units P K LL W
  obtain ⟨_, _, hu⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  obtain ⟨σ, hσ⟩ := GlobalTheory.NB.LT.exists_algEquiv_X_add_C (IsLocalRing.maximalIdeal ↥(OL LL))
    (l : ↥(OL LL)) hu
  refine ⟨?_, exists_qFrame_of_card W (P.PD_p K) χ hχ hl hc σ hσ g ?_⟩
  · have h1 := IsLocalRing.isUnit_or_isUnit_one_sub_self (l : ↥(OL LL))
    rw [hc, Nat.cast_sub (Fact.out : l.Prime).one_le, Nat.cast_one, ← IsUnit.neg_iff, neg_sub]
    exact h1.resolve_left hu
  · have h1 : (χ g : ℤ_[l]) = 1 + l := GlobalTheory.algebraMap_padicInt_OL_injective LL (by
      rw [hχ, hg, map_add (f := _), map_one, map_natCast])
    rw [h1, add_sub_cancel_left]

end GlobalTheory.SenLines
end
