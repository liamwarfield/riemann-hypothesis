module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjPlMemPlacesOver
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteContinuousCocyclesLocalGaloisRep

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst
  GlobalTheory.WeilDeligne TensorProduct Module GlobalTheory.CoeffExt

namespace GlobalTheory.PstExt

section Coord

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
  {LL LL' : Type} [Field LL] [Field LL'] [Algebra ℚ_[l] LL] [Algebra ℚ_[l] LL']
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V']
  [Module LL' V'] [IsScalarTower ℚ_[l] LL' V']
  {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL' ↥(GK K) V'}
  {ι : Type} [Fintype ι] [DecidableEq ι] {E : V' ≃ₗ[LL] (ι → V)}

theorem tensCoord_mulV (c : ↥(MaximalUnramifiedExtension l)) (x : V' ⊗[ℚ_[l]] Bst P) (i : ι) :
    tensCoord E (Bst P) (mulV P LL' V' c x) i = mulV P LL V c (tensCoord E (Bst P) x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add (f := _), Pi.add_apply, hx, hy]

variable (hE : ∀ g x i, E (ρ' g x) i = ρ g (E x i))
include hE

theorem tensCoord_stRep (g : ↥(GK K)) (x : V' ⊗[ℚ_[l]] Bst P) (i : ι) :
    tensCoord E (Bst P) (stRep P ρ' g x) i = stRep P ρ g (tensCoord E (Bst P) x i) := by
  change tensCoord E (Bst P) (AlgebraTensorModule.map (ρ' g)
    (actSt P (g : GQ l)).toLinearMap x) i =
    AlgebraTensorModule.map (ρ g) (actSt P (g : GQ l)).toLinearMap
      (tensCoord E (Bst P) x i)
  exact tensCoord_map E (ρ' g) (ρ g) (hE g) _ x i

theorem mem_Dpst_coord (x : V' ⊗[ℚ_[l]] Bst P) :
    x ∈ Dpst P ρ' ↔ ∀ i, tensCoord E (Bst P) x i ∈ Dpst P ρ := by
  constructor
  · intro hx i
    obtain ⟨K', hK⟩ := (mem_Dpst P ρ').1 hx
    exact (mem_Dpst P ρ).2 ⟨K', fun g hg => by rw [← tensCoord_stRep P hE, hK g hg]⟩
  · intro hx
    choose K' hK using fun i => (mem_Dpst P ρ).1 (hx i)
    have hsum : x = ∑ i, (tensCoord E (Bst P)).symm (Pi.single i (tensCoord E (Bst P) x i)) := by
      apply (tensCoord E (Bst P)).injective
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [LinearEquiv.apply_symm_apply]
      exact (Finset.univ_sum_single _).symm
    rw [hsum]
    refine Submodule.sum_mem _ fun i _ => (mem_Dpst P ρ').2 ⟨K' i, fun g hg => (tensCoord E (Bst P)).injective ?_⟩
    funext j
    rw [tensCoord_stRep P hE, LinearEquiv.apply_symm_apply]
    by_cases h : j = i
    · subst h
      simp [hK j g hg]
    · simp [Pi.single_eq_of_ne h]

def dpstCoord : DpstUr P ρ' ≃ₗ[↥(MaximalUnramifiedExtension l)] (ι → DpstUr P ρ) where
  toFun x i := toUr P ρ ⟨tensCoord E (Bst P) ((toUr P ρ').symm x).1 i,
    (mem_Dpst_coord P hE _).1 ((toUr P ρ').symm x).2 i⟩
  invFun y := toUr P ρ' ⟨(tensCoord E (Bst P)).symm fun i => ((toUr P ρ).symm (y i)).1,
    (mem_Dpst_coord P hE _).2 fun i => by
      rw [LinearEquiv.apply_symm_apply]
      exact ((toUr P ρ).symm (y i)).2⟩
  map_add' x y := by
    funext i
    exact Subtype.ext (congrFun (map_add (tensCoord E (Bst P)) x.1 y.1) i)
  map_smul' c x := by
    funext i
    exact Subtype.ext (tensCoord_mulV P c x.1 i)
  left_inv x := Subtype.ext ((tensCoord E (Bst P)).symm_apply_apply x.1)
  right_inv y := by
    funext i
    exact Subtype.ext (congrFun ((tensCoord E (Bst P)).apply_symm_apply fun i => (y i).1) i)

theorem isPst_of_coord (h : IsPst P ρ) : IsPst P ρ' := by
  unfold IsPst at h ⊢
  rw [(dpstCoord P hE).rank_eq, (E.restrictScalars ℚ_[l]).rank_eq, rank_fun, rank_fun, h]

end Coord

theorem isPst_enlarge : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l E Ω Gw O) {m : ℕ} {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1) (r₁ : ↥Gw →* GL (Fin m) ↥L₁.1),
    IsPst P (Bw.repE L₁ r₁) → IsPst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) := by
  intro l _ P E Ω _ _ _ Gw O _ _ _ Bw m L₁ L₂ hL r₁ h
  let _ : Algebra ↥L₁.1 ↥L₂.1 := (IntermediateField.inclusion hL).toRingHom.toAlgebra
  have : IsScalarTower ℚ_[l] ↥L₁.1 ↥L₂.1 := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := L₂.2
  have : FiniteDimensional ↥L₁.1 ↥L₂.1 := Module.Finite.of_restrictScalars_finite ℚ_[l] _ _
  have hρ : ∀ g, ∃ M : Matrix (Fin m) (Fin m) ↥L₁.1, (∀ x, Bw.repE L₁ r₁ g x = M.mulVec x) ∧
      ∀ x, Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁) g x =
        (M.map (algebraMap ↥L₁.1 ↥L₂.1)).mulVec x :=
    fun g => ⟨r₁ (Bw.e.symm g), fun _ => rfl, fun _ => rfl⟩
  exact isPst_of_coord P (E := GlobalTheory.Pst.vecCoord ↥L₁.1 ↥L₂.1 m) (vecCoord_rep hρ) h

end GlobalTheory.PstExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlargeStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst GlobalTheory.WeilDeligne TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPotentiallySemistable_coefficientField_enlarge : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) {m : ℕ} {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1) (r₁ : ↥Gw →* GL (Fin m) ↥L₁.1), IsPst P (Bw.repE L₁ r₁) → IsPst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) := by
  first | exact @GlobalTheory.PstExt.isPst_enlarge | exact GlobalTheory.PstExt.isPst_enlarge | (intros; apply GlobalTheory.PstExt.isPst_enlarge <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DpstRankLeDimension
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst
  GlobalTheory.WeilDeligne TensorProduct Module GlobalTheory.Pst.DpstMap

namespace GlobalTheory.Pst.DmapNonzero

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

theorem tensV_eq_rTensor {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V']
    [IsScalarTower ℚ_[l] LL V'] (f : V →ₗ[LL] V') (x : V ⊗[ℚ_[l]] Bst P) :
    tensV P f x = (f.restrictScalars ℚ_[l]).rTensor (Bst P) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

end GlobalTheory.Pst.DmapNonzero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitBCOfGalIso
noncomputable section

namespace GlobalTheory.SplitDetermines

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem spehLoc_unr (p : Part A.CG) (w : PlE H) (h : A.unr (A.locG p.π w)) : A.unr (spehLoc N A p w) := by
  unfold spehLoc
  induction List.range p.d with
  | nil => exact A.lpZero_unr w
  | cons k l ih => exact (A.unr_sum _ _).2 ⟨(A.unr_tw _ _).2 h, ih⟩

theorem isoLoc_unr_ae (P : List (Part A.CG)) : ∀ᶠ w in Filter.cofinite, A.unr (isoLoc N A P w) := by
  induction P with
  | nil => exact Filter.Eventually.of_forall fun w => A.lpZero_unr w
  | cons p P ih =>
    filter_upwards [ih, A.locG_unr_ae p.π] with w h1 h2
    exact (A.unr_sum _ _).2 ⟨spehLoc_unr N A p w h2, h1⟩

end GlobalTheory.SplitDetermines

namespace GlobalTheory.RowTie

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

end GlobalTheory.RowTie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFrobeniusConjInertiaPowModWild
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFrobeniusConjInertiaPowModWild
noncomputable section

namespace GlobalTheory.TameRel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem wild_conj {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {s u : G E Ω} (hs : s ∈ Dec (F := E) A)
    (hu : ∀ y : Ω, y ≠ 0 → A.valuation (u y / y - 1) < 1) :
    ∀ y : Ω, y ≠ 0 → A.valuation ((s * u * s⁻¹) y / y - 1) < 1 := by
  intro y hy
  set z := (s⁻¹ : G E Ω) y with hz
  have hsz : s z = y := mul_inv_apply y
  have hz0 : z ≠ 0 := by
    intro h; apply hy; rw [← hsz, h, map_zero]
  have e : (s * u * s⁻¹) y / y - 1 = s (u z / z - 1) := by
    rw [map_sub, map_div₀, map_one, hsz]
    rfl
  rw [e, GlobalTheory.TameLabels.valuation_apply_of_mem_Dec hs]
  exact hu z hz0

end GlobalTheory.TameRel

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem GlobalTheory.TameRel.main : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (k : Fin 2) (v : N.PlG k), ∀ γ ∈ Ine (F := H.E) (N.plOm.1 (A.plGw k v)), ∃ φ : G H.E N.Om, φ * γ * φ⁻¹ * (γ ^ H.g k)⁻¹ ∈ Ine (F := H.E) (N.plOm.1 (A.plGw k v)) ∧ φ * γ * φ⁻¹ * (γ ^ H.g k)⁻¹ ∈ wildSet N (N.plOm.1 (A.plGw k v)) := by
  intro R H what₂ N A k v γ hγ
  obtain ⟨φ, hφ⟩ := exists_isFrob (N.plOm.2 (A.plGw k v))
  rw [GlobalTheory.TameLabels.normV_eq_of_split (H.g_prime k) (N.g_split k) (A.plGw_over k v)] at hφ
  refine ⟨φ, ?_, ?_⟩
  · exact Subgroup.mul_mem _ (conj_mem_Ine hφ.1 hγ) (Subgroup.inv_mem _ (Subgroup.pow_mem _ hγ _))
  · have hu := GlobalTheory.TameLabels.wild_of_frob hγ hφ
    have hs : γ ^ H.g k ∈ Dec (F := H.E) (N.plOm.1 (A.plGw k v)) :=
      (Dec (F := H.E) _).pow_mem (Ine_le_Dec _ hγ) _
    have h := GlobalTheory.TameRel.wild_conj hs hu
    have e : γ ^ H.g k * ((γ ^ H.g k)⁻¹ * (φ * γ * φ⁻¹)) * (γ ^ H.g k)⁻¹ = φ * γ * φ⁻¹ * (γ ^ H.g k)⁻¹ := by
      group
    rw [e] at h
    exact h
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFrobeniusConjInertiaPowModWildStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frobenius_conj_inertia_pow_mod_wild : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (k : Fin 2) (v : N.PlG k), ∀ γ ∈ Ine (F := H.E) (N.plOm.1 (A.plGw k v)), ∃ φ : G H.E N.Om, φ * γ * φ⁻¹ * (γ ^ H.g k)⁻¹ ∈ Ine (F := H.E) (N.plOm.1 (A.plGw k v)) ∧ φ * γ * φ⁻¹ * (γ ^ H.g k)⁻¹ ∈ wildSet N (N.plOm.1 (A.plGw k v)) := by
  first | exact @GlobalTheory.TameRel.main | exact GlobalTheory.TameRel.main | (intros; apply GlobalTheory.TameRel.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacter
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

namespace GlobalTheory.MuCharProof

theorem charpoly_fin_one {k : Type} [CommRing k] (M : Matrix (Fin 1) (Fin 1) k) :
    M.charpoly = X - C (M 0 0) := by
  rw [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq]

theorem mem_list_sum {α β : Type} (L : List α) (f : α → Multiset β) {a : α} (ha : a ∈ L) {b : β}
    (hb : b ∈ f a) : b ∈ (L.map f).sum :=
  Multiset.mem_of_le (List.le_sum_of_mem (List.mem_map_of_mem ha)) hb

end GlobalTheory.MuCharProof
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidualRankPartExistsOfJointCondition
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidualRankPartExistsOfJointCondition
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

namespace GlobalTheory.StringRepresentationDecomposition

theorem rbEx_of_jointCond_rho : ∀ D : D7, GlobalDatumResidualRepCondition D → RbEx D := by
  intro D hrho i hHG
  obtain ⟨x, hx⟩ := hHG
  have hx' := hx
  obtain ⟨-, Sig, hSig, hgood⟩ := hx'
  obtain ⟨ρ₀, ξ, -, -, hρx⟩ := hrho i x hx Sig hSig hgood
  exact ⟨_, isRhoBar_of_isRhoOf D i x _ hρx⟩

end GlobalTheory.StringRepresentationDecomposition
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidualRankPartExistsOfJointConditionStatement
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residualRankPartExists_of_jointCondition : ∀ D : D7, GlobalDatumResidualRepCondition D → RbEx D := by
  first | exact @GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho | exact GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho | (intros; apply GlobalTheory.StringRepresentationDecomposition.rbEx_of_jointCond_rho <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthWeightStatement
noncomputable section

namespace GlobalTheory.FrobeniusCharacterNorms

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}

theorem normV_pos (w : PlE H) : 0 < normV w := by
  have h := GlobalTheory.LocalInv.one_lt_normV w
  have : (0 : ℝ) < ((normV w : ℕ) : ℝ) := by linarith
  exact_mod_cast this

theorem frob_one {w : PlE H} {a : A.LP w} (hu : A.unr a) (hd : A.lpDim a = 1) : ∃ c, A.frobEig a = {c} :=
  Multiset.card_eq_one.1 (by rw [A.frobEig_card a hu, hd])

theorem eta_frob (hAut : At.TieAut N A) (w : PlE H) : ∃ b, A.frobEig (A.locG A.etaT w) = {b} ∧ ‖b‖ = 1 := by
  obtain ⟨b, hb⟩ := frob_one (A.etaT_unr w) (A.locG_dim A.etaT w)
  refine ⟨b, hb, (A.tempered_unr _ (A.etaT_unr w)).1 (hAut.2.2.1 w) b ?_⟩
  rw [hb]
  exact Multiset.mem_singleton_self b

theorem norm_first_character_frobenius (hAut : At.TieAut N A) (i : N.Loc) {w : PlE H} (hw : SplitOut N i w)
    (huμ : A.unr (A.locG (A.muC i) w)) {B : ValuationSubring N.Om} {σ : G H.E N.Om}
    (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) :
    ‖A.iotaQC i (iotaOQ N A i (chi1 N i σ))‖ =
      (normV w : ℝ) ^ (((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2) := by
  obtain ⟨hu, hf⟩ := A.chi_mu i w hw
  have e : A.frobEig (A.lpTw (A.locG (A.tw (A.muC i) A.etaTinv) w) (((R.t : ℝ) - 1) / 2 + (1 - (R.nV : ℝ)) / 2)) =
      {A.iotaQC i (iotaOQ N A i (chi1 N i σ))} := hf B σ hB hσ
  rw [A.frobEig_tw _ _ hu, A.locG_tw] at e
  obtain ⟨m, hm⟩ := frob_one huμ (A.locG_dim (A.muC i) w)
  have hm1 : ‖m‖ = 1 := (A.tempered_unr _ huμ).1 (hAut.2.2.2 i w) m (by rw [hm]; exact Multiset.mem_singleton_self m)
  obtain ⟨b, hb, hb1⟩ := eta_frob hAut w
  obtain ⟨hui, hfi⟩ := A.etaTinv_def w
  have hfi' : A.frobEig (A.locG A.etaTinv w) = {b⁻¹} := by rw [hfi, hb, Multiset.map_singleton]
  have hfe := A.frobEig_char (A.locG (A.muC i) w) (A.locG A.etaTinv w) b⁻¹ huμ hui (A.locG_dim _ w) hfi'
  rw [hfe, hm, Multiset.map_singleton, Multiset.map_singleton, Multiset.singleton_inj] at e
  rw [← e, norm_mul, norm_mul, hm1, norm_inv, hb1, inv_one, one_mul, one_mul,
    Complex.norm_natCast_cpow_of_pos (normV_pos w), Complex.ofReal_re]

theorem eps_frob (i : N.Loc) {w : PlE H} (hl : w ∉ placesOver H.E (N.l i)) {B : ValuationSubring N.Om}
    {σ : G H.E N.Om} (hB : IsPlaceOver (F := H.E) B w) (hσ : IsFrob (F := H.E) B (normV w) σ) :
    A.iotaQC i (iotaOQ N A i ((Glob.epsO N i σ : (N.O i)ˣ) : N.O i)) = (normV w : ℂ) := by
  have hc := cycZ_of_isFrob (F := H.E) (Ω := N.Om) (l := N.l i) (by simpa [placesOver] using hl) hB hσ
  have e1 : ((Glob.epsO N i σ : (N.O i)ˣ) : N.O i) =
      algebraMap ℤ_[N.l i] (N.O i) ((cycZ H.E N.Om (N.l i) σ : ℤ_[N.l i]ˣ) : ℤ_[N.l i]) := rfl
  rw [e1, hc]
  show A.iotaQC i (A.iotaQ i (algebraMap (N.O i) (FractionRing (N.O i))
    (algebraMap ℤ_[N.l i] (N.O i) ((normV w : ℕ) : ℤ_[N.l i])))) = _
  rw [A.iotaQ_alg i, PadicInt.coe_natCast, map_natCast, map_natCast]

end GlobalTheory.FrobeniusCharacterNorms

namespace GlobalTheory.FrobeniusCharacterNorms

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.SumRepresentations Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

end GlobalTheory.FrobeniusCharacterNorms
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StringRankOneLengthAndMultisetSumSingleton
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

namespace GlobalTheory.SixthNumerics

theorem numerics : Numerics := by
  intro r t d n a A hr ht had hw hsum hpos hn hle
  have hd : d = t + 2 * a := by omega
  have hA : A ≠ 0 := by
    rintro rfl
    simp at hsum
    omega
  have hmem : ∀ x ∈ A, x = 1 := by
    intro x hx
    have h1 := Multiset.count_le_of_le x hle
    rw [Multiset.count_nsmul] at h1
    have hc : 1 ≤ Multiset.count x A := Multiset.one_le_count_iff_mem.mpr hx
    have h2 : d ≤ Multiset.count x (r ::ₘ Multiset.replicate t 1) :=
      le_trans (by nlinarith) h1
    by_contra hx1
    rw [Multiset.count_cons, Multiset.count_replicate] at h2
    split_ifs at h2 <;> omega
  have hrep : A = Multiset.replicate (Multiset.card A) 1 := Multiset.eq_replicate_card.mpr hmem
  have hcard : 1 ≤ Multiset.card A := Multiset.card_pos.mpr hA
  have h1 := Multiset.count_le_of_le 1 hle
  rw [Multiset.count_nsmul, Multiset.count_cons, Multiset.count_replicate_self] at h1
  have hc1 : Multiset.count 1 A = Multiset.card A := by
    conv_lhs => rw [hrep]
    exact Multiset.count_replicate_self _ _
  rw [hc1] at h1
  have hr1 : (1 : ℕ) ≠ r := by omega
  simp [hr1] at h1
  have hsum' : n = Multiset.card A := by
    rw [← hsum, hrep]; simp
  have : Multiset.card A = 1 := by nlinarith
  refine ⟨by omega, ?_⟩
  have : a = 0 := by nlinarith
  omega

theorem rest : Rest := by
  intro ι _ d A r hd hA hs
  have hc := congrArg Multiset.card hs
  have hc' : ∑ k, d k * Multiset.card (A k) = 1 := by
    rw [Multiset.card_sum] at hc
    simpa [Multiset.card_nsmul] using hc
  have hterm : ∀ k, 1 ≤ d k * Multiset.card (A k) := fun k =>
    Nat.mul_le_mul (hd k) (Multiset.card_pos.mpr (hA k))
  have hle : ∀ k, d k * Multiset.card (A k) = 1 := by
    intro k
    have := Finset.single_le_sum (f := fun k => d k * Multiset.card (A k))
      (fun i _ => Nat.zero_le _) (Finset.mem_univ k)
    have := hterm k
    omega
  have hcardle : Fintype.card ι ≤ 1 := by
    have := Finset.card_nsmul_le_sum Finset.univ (fun k => d k * Multiset.card (A k)) 1
      (fun k _ => hterm k)
    simp at this
    omega
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hs
  have hcard : Fintype.card ι = 1 := le_antisymm hcardle Fintype.card_pos
  refine ⟨hcard, fun k => ?_⟩
  have hdk : d k = 1 := Nat.eq_one_of_mul_eq_one_right (hle k)
  refine ⟨hdk, ?_⟩
  have hsub : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hcardle
  rw [Finset.sum_eq_single k (fun b _ hb => absurd (Subsingleton.elim b k) hb)
    (fun h => absurd (Finset.mem_univ k) h), hdk, one_smul] at hs
  exact hs

theorem numerics_and_rest : Numerics ∧ Rest := ⟨numerics, rest⟩

end GlobalTheory.SixthNumerics
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickIffThickEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickIffThickEmbedding
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem pageWord_thick_iff : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG),
    Roomy L C → ∀ i, (pageWord L j ε τ φ).thick i ↔ Thick D.host (letter τ φ i) := by
  intro D L C j ε τ φ hR i
  obtain ⟨hlo, -⟩ := bHat_window L C hR
  obtain ⟨hwM, hwle⟩ := GlobalTheory.T.maxSizeAtNonThickPlace_le_and_bound L C hR
  have hR' := hR
  obtain ⟨hC, hw, ht, hwb, -, hb⟩ := hR'
  obtain ⟨c, hc⟩ := D.R.t_odd
  have he := L.etaSz_pos
  have hS := L.Sc_pos
  have hLw : (0 : ℝ) ≤ (D.host.Lw : ℝ) := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hb' : (0 : ℝ) ≤ L.sc.b' := by linarith
  have h1 : (100 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
  have hbb : 100 * L.sc.b' ≤ L.sc.b := by nlinarith
  have hdiv : (D.R.t + 1) / 2 = c + 1 := by omega
  have hdivZ : ((D.R.t : ℤ) + 1) / 2 = (c : ℤ) + 1 := by omega
  have htc : (D.R.t : ℝ) = 2 * c + 1 := by exact_mod_cast hc
  have hc0 : (0 : ℝ) ≤ (c : ℝ) := Nat.cast_nonneg _
  have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ L.sc.b by linarith)
  have hle := Nat.le_ceil L.sc.b
  have hsub : c + 1 ≤ ⌈L.sc.b⌉₊ := by
    have : ((c + 1 : ℕ) : ℝ) ≤ (⌈L.sc.b⌉₊ : ℝ) := by push_cast; linarith
    exact_mod_cast this
  have hbH : bHat L + (c + 1) = ⌈L.sc.b⌉₊ := by
    unfold bHat
    rw [hdiv]
    omega
  have hfl := Nat.lt_floor_add_one L.etaSz
  have hη : etaHat L = ⌊L.etaSz⌋₊ + D.R.t + 2 := rfl
  have hsz : ((pageWord L j ε τ φ).sz i = ⌊(hcAt D (letter τ φ i)).e j⌋ + ((c : ℤ) + 1) ∧
        pos ε (letter τ φ i) = true) ∨
      ((pageWord L j ε τ φ).sz i = ⌊(hcAt D (letter τ φ i)).e j⌋ - ((c : ℤ) + 1) ∧
        pos ε (letter τ φ i) = false) := by
    show szT (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i)) = _ ∧ _ ∨
      szT (hcAt D (letter τ φ i)) j (pos ε (letter τ φ i)) = _ ∧ _
    unfold szT
    cases pos ε (letter τ φ i) <;> simp [hdivZ]
  have hbW : (pageWord L j ε τ φ).b = bHat L := rfl
  have hηW : (pageWord L j ε τ φ).η = etaHat L := rfl
  unfold WordData.thick
  rw [hbW, hηW, hη]
  generalize hE : ⌊(hcAt D (letter τ φ i)).e j⌋ = E at hsz
  constructor
  · rintro ⟨ha, hz⟩
    by_contra hnT
    have hEw : E ≤ (wMax D : ℤ) := hE ▸ hwle _ j hnT
    have hlt2 : ((wMax D + (c + 1) : ℕ) : ℝ) < (bHat L : ℝ) := by
      push_cast
      rw [htc] at hlo ht
      linarith
    have hlt3 : wMax D + (c + 1) < bHat L := by exact_mod_cast hlt2
    omega
  · intro hT
    obtain ⟨hA, hB⟩ := GlobalTheory.T.floor_size_bounds_at_thick_embedding L _ j hT
    rw [hE] at hA hB
    have hBE : ((⌈L.sc.b⌉₊ : ℤ)) ≤ E := by
      have : ((⌈L.sc.b⌉₊ : ℤ) : ℝ) < ((E + 1 : ℤ) : ℝ) := by push_cast; linarith
      have := Int.cast_lt.mp this
      omega
    have hEB : E < (⌈L.sc.b⌉₊ : ℤ) + (⌊L.etaSz⌋₊ : ℤ) + 2 := by
      have : ((E : ℤ) : ℝ) < (((⌈L.sc.b⌉₊ : ℤ) + (⌊L.etaSz⌋₊ : ℤ) + 2 : ℤ) : ℝ) := by push_cast; linarith
      exact Int.cast_lt.mp this
    omega

end GlobalTheory.HTW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualOrbitPageWordThickIffThickEmbeddingStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualOrbitPageWord_thick_iff_thickEmbedding : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ φ : D.R.GG), Roomy L C → ∀ i, (pageWord L j ε τ φ).thick i ↔ Thick D.host (letter τ φ i) := by
  first | exact @GlobalTheory.HTW.pageWord_thick_iff | exact GlobalTheory.HTW.pageWord_thick_iff | (intros; apply GlobalTheory.HTW.pageWord_thick_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenMDetNeZeroOfNontrivial
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

theorem jacobi_blocks_of_mul {R : Type} [CommRing R] {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β] (M Y : Matrix (α ⊕ β) (α ⊕ β) R) (d : R) (h : M * Y = d • (1 : Matrix (α ⊕ β) (α ⊕ β) R)) :
    M.toBlocks₁₁.det * Y.det = d ^ Fintype.card α * Y.toBlocks₂₂.det := by
  have hY : Y = Matrix.fromBlocks Y.toBlocks₁₁ Y.toBlocks₁₂ Y.toBlocks₂₁ Y.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks Y).symm
  have hM : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₁ M.toBlocks₂₂ :=
    (Matrix.fromBlocks_toBlocks M).symm
  have h' := h
  rw [hM, hY, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero] at h'
  obtain ⟨h11, h12, -, -⟩ := Matrix.fromBlocks_inj.mp h'
  have key : Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 1 * Y =
      Matrix.fromBlocks (d • 1) 0 Y.toBlocks₂₁ Y.toBlocks₂₂ := by
    conv_lhs => rw [hY]
    rw [Matrix.fromBlocks_multiply, h11, h12]
    simp
  have hd := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one,
    Matrix.det_smul, Matrix.det_one, mul_one] at hd
  exact hd

theorem genM_det_ne_zero_of_nontrivial (R : Type) [CommRing R] [Nontrivial R] (n : ℕ) : (genM R n).det ≠ 0 := by
  intro h
  have h1 := congrArg (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2) h
  have hm : (MvPolynomial.eval fun v : Fin n × Fin n => (1 : Matrix (Fin n) (Fin n) R) v.1 v.2).mapMatrix
      (genM R n) = 1 := by
    ext a b
    simp [genM]
  rw [RingHom.map_det, hm, Matrix.det_one, map_zero] at h1
  exact one_ne_zero h1

theorem exists_equiv_castLE_rev {n s : ℕ} (hs : s ≤ n) : ∃ e : Fin (n - s) ⊕ Fin s ≃ Fin n,
    (∀ a, e (.inl a) = Fin.castLE (Nat.sub_le n s) a) ∧ ∀ q, e (.inr q) = Fin.rev (Fin.castLE hs q) := by
  refine ⟨(Equiv.sumCongr (Equiv.refl _) Fin.revPerm).trans
    (finSumFinEquiv.trans (finCongr (Nat.sub_add_cancel hs))), ?_, ?_⟩
  · intro a
    ext
    simp
  · intro q
    have hq := q.isLt
    ext
    simp
    omega

theorem jacobi_adjugate_perm {R : Type} [CommRing R] [IsDomain R] {n s : ℕ} (hs : s ≤ n) (h1 : 1 ≤ s)
    (M : Matrix (Fin n) (Fin n) R) (hM : M.det ≠ 0) (σ : Equiv.Perm (Fin n)) : ∃ ε : ℤˣ,
    (Matrix.of fun q p : Fin s => M.adjugate (Fin.rev (Fin.castLE hs q)) (σ (Fin.castLE hs p))).det =
      (ε : ℤ) • (M.det ^ (s - 1) * (Matrix.of fun a b : Fin (n - s) =>
        M (σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) (Fin.castLE (Nat.sub_le n s) b)).det) := by
  obtain ⟨e, he1, he2⟩ := exists_equiv_castLE_rev hs
  obtain ⟨f, hf1, hf2⟩ : ∃ f : Fin (n - s) ⊕ Fin s ≃ Fin n,
      (∀ a, f (.inl a) = σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) ∧ ∀ p, f (.inr p) = σ (Fin.castLE hs p) :=
    ⟨(e.trans Fin.revPerm).trans σ, fun a => by simp [he1], fun p => by simp [he2]⟩
  have hmul : M.submatrix f e * M.adjugate.submatrix e f =
      M.det • (1 : Matrix (Fin (n - s) ⊕ Fin s) (Fin (n - s) ⊕ Fin s) R) := by
    rw [← Matrix.submatrix_mul M M.adjugate f e f e.bijective, Matrix.mul_adjugate]
    ext i j
    simp [Matrix.one_apply]
  have hJ := jacobi_blocks_of_mul _ _ _ hmul
  have hC : (M.submatrix f e).toBlocks₁₁ = Matrix.of fun a b : Fin (n - s) =>
      M (σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) (Fin.castLE (Nat.sub_le n s) b) := by
    ext a b
    simp [Matrix.toBlocks₁₁, hf1, he1]
  have hT : (M.adjugate.submatrix e f).toBlocks₂₂ = Matrix.of fun q p : Fin s =>
      M.adjugate (Fin.rev (Fin.castLE hs q)) (σ (Fin.castLE hs p)) := by
    ext q p
    simp [Matrix.toBlocks₂₂, hf2, he2]
  have hY : (M.adjugate.submatrix e f).det =
      ((Equiv.Perm.sign (e.trans f.symm) : ℤ) : R) * M.det ^ (n - 1) := by
    have hre : M.adjugate.submatrix e f = (M.adjugate.submatrix f f).submatrix (e.trans f.symm) id := by
      ext i j
      simp
    rw [hre, Matrix.det_permute, Matrix.det_submatrix_equiv_self, Matrix.det_adjugate, Fintype.card_fin]
  rw [hC, hT, hY, Fintype.card_fin] at hJ
  have hpow : M.det ^ (n - 1) = M.det ^ (n - s) * M.det ^ (s - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hpow] at hJ
  refine ⟨Equiv.Perm.sign (e.trans f.symm), ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero (n - s) hM)
  rw [zsmul_eq_mul]
  linear_combination -hJ

theorem cofAct_initMinor : ∀ (R : Type) [CommRing R] [IsDomain R] (n s : ℕ) (hs : s ≤ n), 1 ≤ s → ∀ σ : Equiv.Perm (Fin n), ∃ ε : ℤˣ, cofAct R n (initMinor R (fun a : Fin s => σ (Fin.castLE hs a)) hs) = (ε : ℤ) • ((genM R n).det ^ (s - 1) * initMinor R (fun a : Fin (n - s) => σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) (Nat.sub_le n s)) := by
  intro R _ _ n s hs h1 σ
  obtain ⟨ε, hε⟩ := jacobi_adjugate_perm hs h1 (genM R n) (genM_det_ne_zero_of_nontrivial R n) σ
  refine ⟨ε, ?_⟩
  have hlhs : cofAct R n (initMinor R (fun a : Fin s => σ (Fin.castLE hs a)) hs) =
      (Matrix.of fun q p : Fin s => (genM R n).adjugate (Fin.rev (Fin.castLE hs q)) (σ (Fin.castLE hs p))).det := by
    rw [initMinor, AlgHom.map_det, ← Matrix.det_transpose]
    congr 1
    ext q p
    simp [cofAct]
  have hrhs : (Matrix.of fun a b : Fin (n - s) =>
      genM R n (σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) (Fin.castLE (Nat.sub_le n s) b)).det =
      initMinor R (fun a : Fin (n - s) => σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) (Nat.sub_le n s) := by
    rw [initMinor]
    congr 1
  rw [hlhs, hε, hrhs]

end GlobalTheory.ValCmp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualContinuousIntegralOverEnlargedCoeff
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualContinuousIntegralOverEnlargedCoeff
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TwistedDualLoc

theorem continuous_T2O (D : D7) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i)
    (hρ : Continuous fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) :
    Continuous (T2O D.nd i ρ π) := by
  have h1 : Continuous fun g : GE D.nd => ((chiU D.nd i 1 g : (D.nd.O i)ˣ) : D.nd.O i) :=
    D.nd.chi_cont i 1
  have h2 : Continuous fun g : GE D.nd => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) :=
    GlobalTheory.LocalInv.eps_cont D.nd i
  have h3 : Continuous fun g : GE D.nd => ((ρ π g⁻¹ : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) := hρ.comp continuous_inv
  refine continuous_matrix fun a b => ?_
  have h : ∀ g : GE D.nd, T2O D.nd i ρ π g a b =
      ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) * (((chiU D.nd i 1 g : (D.nd.O i)ˣ) : D.nd.O i) *
        ((ρ π g⁻¹ : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) b a) := by
    intro g
    simp [T2O, WpO, rhoO, twistM, dualM]
  simp only [h]
  exact h2.mul (h1.mul (h3.matrix_elem b a))

theorem continuous_and_integral : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (LL' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ LL'.1) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) → Continuous (fun g => mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)) g) ∧ ∀ g a b, ‖((mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)) g a b : ↥LL'.1) : Om (D.nd.l i))‖ ≤ 1 := by
  intro D i w hw LL' h ρ π hρ
  have hc := GlobalTheory.WordJumpsCompare.continuous_loc D i w hw (T2O D.nd i ρ π) (continuous_T2O D i ρ π hρ)
  refine ⟨continuous_matrix fun a b => ?_, fun g a b => ?_⟩
  · exact Continuous.subtype_mk (continuous_subtype_val.comp (hc.matrix_elem a b)) _
  · exact GlobalTheory.LocalH1Finiteness.norm_toLL_le (D.nbr i w hw) _

end GlobalTheory.TwistedDualLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualContinuousIntegralOverEnlargedCoeffStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDual_continuous_integral_over_enlarged_coeff : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (LL' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ LL'.1) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) → Continuous (fun g => mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)) g) ∧ ∀ g a b, ‖((mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)) g a b : ↥LL'.1) : Om (D.nd.l i))‖ ≤ 1 := by
  first | exact @GlobalTheory.TwistedDualLoc.continuous_and_integral | exact GlobalTheory.TwistedDualLoc.continuous_and_integral | (intros; apply GlobalTheory.TwistedDualLoc.continuous_and_integral <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxNonThickSizeShiftedValueAndBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxNonThickSizeShiftedValueAndBounds
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

private theorem cast_succ_div_two_of_odd {t : ℕ} (ht : Odd t) :
    (((t + 1) / 2 : ℕ) : ℝ) = ((t : ℝ) + 1) / 2 := by
  obtain ⟨k, rfl⟩ := ht
  have h : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  rw [h]
  push_cast
  ring

theorem _root_.GlobalTheory.HTW.wHat_le : ∀ {D : _root_.Formalism.BasicNotions.D7} (L : _root_.Formalism.BasicNotions.SizeData₂ D) (C : ℝ),
    _root_.GlobalTheory.HTW.Roomy L C →
    (_root_.GlobalTheory.HTW.wHat D : ℝ) = _root_.GlobalTheory.HTW.wMax D + ((D.R.t : ℝ) + 1) / 2 ∧
    (_root_.GlobalTheory.HTW.wHat D : ℝ) + (L.etaSz + D.R.t + 2) ≤ 2 * L.sc.b' ∧
    (_root_.GlobalTheory.HTW.wHat D : ℝ) + _root_.GlobalTheory.HTW.sHat L + _root_.GlobalTheory.HTW.etaHat L + 1
      ≤ 2 * L.sc.b' := by
  intro D L C hL
  have hw : (_root_.GlobalTheory.HTW.wHat D : ℝ) =
      _root_.GlobalTheory.HTW.wMax D + ((D.R.t : ℝ) + 1) / 2 := by
    unfold _root_.GlobalTheory.HTW.wHat
    push_cast [cast_succ_div_two_of_odd D.R.t_odd]
    rfl
  have hmax := (_root_.GlobalTheory.HTW.wMax_le_and_ge L C hL).1
  have hR := hL
  unfold _root_.GlobalTheory.HTW.Roomy at hR
  obtain ⟨-, -, h3, h4, -, -⟩ := hR
  have hS := L.Sc_pos
  have hE := L.etaSz_pos
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hfS : (_root_.GlobalTheory.HTW.sHat L : ℝ) ≤ L.Sc := by
    unfold _root_.GlobalTheory.HTW.sHat
    exact Nat.floor_le hS.le
  have hfE : (_root_.GlobalTheory.HTW.etaHat L : ℝ) ≤ L.etaSz + D.R.t + 2 := by
    unfold _root_.GlobalTheory.HTW.etaHat
    push_cast
    linarith [Nat.floor_le hE.le]
  refine ⟨hw, ?_, ?_⟩
  · rw [hw]; nlinarith
  · rw [hw]; nlinarith

end GlobalTheory.HTW
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxNonThickSizeShiftedValueAndBoundsStatement
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxNonThickSizeShifted_value_and_bounds : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ), Roomy L C → (wHat D : ℝ) = wMax D + ((D.R.t : ℝ) + 1) / 2 ∧ (wHat D : ℝ) + (L.etaSz + D.R.t + 2) ≤ 2 * L.sc.b' ∧ (wHat D : ℝ) + sHat L + etaHat L + 1 ≤ 2 * L.sc.b' := by
  first | exact @GlobalTheory.HTW.wHat_le | exact GlobalTheory.HTW.wHat_le | (intros; apply GlobalTheory.HTW.wHat_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalCohomologyVanishesTameInertiaNoFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalCohomologyVanishesTameInertiaNoFixed
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

noncomputable section

namespace GlobalTheory.StringRepresentationDecomposition

theorem cycMod_eq_one_of_mem_Ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (r : ℕ) {A : ValuationSubring Ω}
    {v : HeightOneSpectrum (𝓞 F)} (hl : ((l : ℕ) : 𝓞 F) ∉ v.asIdeal) (h : IsPlaceOver A v)
    {σ : G F Ω} (hσ : σ ∈ Ine (F := F) A) : cycMod F Ω l r σ = 1 := by
  apply Units.ext
  have e := cycZ_toZModPow_eq hl h (q := 1) (fun x hx => by simpa using hσ.2 x hx) r
  simp only [Nat.cast_one, map_one] at e
  simpa [cycMod] using e

theorem tame_vanish : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (rho : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ContAction rho → (∃ γ : Dec (F := F) A, (γ : G F Ω) ∈ Ine (F := F) A ∧ Function.Bijective fun m : M => rho γ m - m) → H0 rho = ⊥ ∧ Subsingleton (H1 rho) ∧ Subsingleton (H2 rho) := by
  intro _ hTD hEC F Ω _ _ _ _ _ l _ M _ _ _ _ _ A v rho hA hl hrho hex
  obtain ⟨γ, hγI, hγ⟩ := hex

  have h0 : H0 rho = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro m hm
    have h1 : rho γ m = m := (Representation.mem_invariants rho m).mp hm γ
    apply hγ.1
    show rho γ m - m = rho γ 0 - 0
    rw [h1, map_zero, sub_self, sub_self]

  set χ := (cycMod F Ω l 1).comp (Dec (F := F) A).subtype with hχdef
  have hχ : χ γ = 1 := cycMod_eq_one_of_mem_Ine 1 hl hA hγI
  have hdual : Subsingleton (H0 ((twDual χ rho).comp (MonoidHom.id _))) := by
    have key : ∀ φ ∈ H0 ((twDual χ rho).comp (MonoidHom.id _)), φ = 0 := by
      intro φ hφ
      have h1 : twDual χ rho γ φ = φ := (Representation.mem_invariants _ φ).mp hφ γ
      apply DFunLike.ext
      intro x
      obtain ⟨m, rfl⟩ := hγ.2 x
      have h3 := congrArg (fun ψ : TDual (ZMod (l ^ 1)) M => ψ (rho γ m)) h1
      simp only [twDual_apply, hχ, Units.val_one, one_mul] at h3
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h3
      show φ (rho γ m - m) = 0
      exact (LinearMap.map_sub (φ : Module.Dual (ZMod (l ^ 1)) M) (rho γ m) m).trans (sub_eq_zero.mpr h3.symm)
    refine ⟨fun a b => ?_⟩
    exact Subtype.ext ((key a.1 a.2).trans (key b.1 b.2).symm)

  have hTD' := hTD F Ω l 1 M A rho v Nat.one_pos hA hrho
  have hinj := hTD'.2.2.2.2.1
  have h2 : Subsingleton (H2 rho) := by
    refine ⟨fun x y => hinj ?_⟩
    ext z
    rw [Subsingleton.elim z 0, map_zero, map_zero]

  have hc0 : Nat.card (H0 rho) = 1 := by
    rw [h0]; exact Nat.card_unique
  have hc2 : Nat.card (H2 rho) = 1 := Nat.card_eq_one_iff_unique.mpr ⟨h2, ⟨0⟩⟩
  have he := (hEC F Ω l 1 M A rho v Nat.one_pos hA hrho).2 hl
  have hc1 : Nat.card (H1 rho) = 1 := by rw [he, hc0, hc2]
  exact ⟨h0, (Nat.card_eq_one_iff_unique.mp hc1).1, h2⟩

end GlobalTheory.StringRepresentationDecomposition
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalCohomologyVanishesTameInertiaNoFixedStatement
open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCohomology_vanishes_tame_inertia_no_fixed : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (M : Type) [AddCommGroup M] [Module (ZMod (l ^ 1)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)) (rho : Representation (ZMod (l ^ 1)) (Dec (F := F) A) M), IsPlaceOver A v → ((l : ℕ) : 𝓞 F) ∉ v.asIdeal → ContAction rho → (∃ γ : Dec (F := F) A, (γ : G F Ω) ∈ Ine (F := F) A ∧ Function.Bijective fun m : M => rho γ m - m) → H0 rho = ⊥ ∧ Subsingleton (H1 rho) ∧ Subsingleton (H2 rho) := by
  first | exact @GlobalTheory.StringRepresentationDecomposition.tame_vanish | exact GlobalTheory.StringRepresentationDecomposition.tame_vanish | (intros; apply GlobalTheory.StringRepresentationDecomposition.tame_vanish <;> assumption)
end
end
