module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.RangeShape
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.ExistsNatSmulSingle
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearLift

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMLocKNonsplitEqNegOnePow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMLocKNonsplitEqNegOnePow
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.InertChar

open ValuativeRel

variable {F : Type} [Field F] [NumberField F]

theorem valued_eq_exp_ordL (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    Valued.v (x : v.adicCompletion F) = WithZero.exp (-Formalism.UG.ordL (x : v.adicCompletion F)) := by
  have h0 : Valued.v (x : v.adicCompletion F) ≠ 0 := (_root_.map_ne_zero _).2 x.ne_zero
  rw [← WithZero.exp_log h0]
  congr 1
  unfold Formalism.UG.ordL
  rw [dite_eq_right h0, neg_neg]
  have key : ∀ (z : WithZero (Multiplicative ℤ)) (h : z ≠ 0), WithZero.log z = Multiplicative.toAdd (WithZero.unzero h) := by
    intro z h
    cases z with
    | zero => exact absurd rfl h
    | coe a => rfl
  exact key _ h0

theorem ord_eq_ordL (v : HeightOneSpectrum (𝓞 F)) (x : (v.adicCompletion F)ˣ) :
    GlobalTheory.SmGL.ord (v.adicCompletion F) x = Formalism.UG.ordL (x : v.adicCompletion F) := by
  haveI : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have hE := ValuativeRel.isEquiv (valuation (v.adicCompletion F))
    (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)))
  obtain ⟨p, hp⟩ := HeightOneSpectrum.valuedAdicCompletion_surjective F v (WithZero.exp (-1 : ℤ))
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  obtain ⟨y, hy⟩ := ValuativeRel.valuation_surjective (uniformizer (v.adicCompletion F))
  have hpu : valuation (v.adicCompletion F) p = uniformizer (v.adicCompletion F) := by
    refine le_antisymm (le_uniformizer_iff.2 (hE.lt_one_iff_lt_one.2 ?_)) ?_
    · rw [hp, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega
    · have h1 : Valued.v y < 1 := hE.lt_one_iff_lt_one.1 (hy ▸ uniformizer_lt_one)
      rw [← hy, hE.le_iff_le, hp]
      rcases eq_or_ne (Valued.v y) 0 with h0 | h0
      · rw [h0]; exact zero_le
      · rw [← WithZero.exp_log h0] at h1 ⊢
        rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h1
        rw [WithZero.exp_le_exp]; omega
  set P : (v.adicCompletion F)ˣ := Units.mk0 p hp0
  have hP1 : GlobalTheory.SmGL.ord (v.adicCompletion F) P = 1 := GlobalTheory.SmGL.ord_eq_one hpu
  set m := Formalism.UG.ordL (x : v.adicCompletion F)
  set U : (v.adicCompletion F)ˣ := x * P ^ (-m)
  have hU : Valued.v (U : v.adicCompletion F) = 1 := by
    simp only [U, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, P, Units.val_mk0, hp]
    rw [valued_eq_exp_ordL v x, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    simp [m]
  have hU' : valuation (v.adicCompletion F) (U : v.adicCompletion F) = 1 := by
    apply le_antisymm
    · rw [← map_one (valuation (v.adicCompletion F)), hE.le_iff_le, hU, map_one]
    · rw [← map_one (valuation (v.adicCompletion F)), hE.le_iff_le, hU, map_one]
  have hU0 : GlobalTheory.SmGL.ord (v.adicCompletion F) U = 0 := GlobalTheory.SmGL.ord_eq_zero hU'
  let o : (v.adicCompletion F)ˣ →* Multiplicative ℤ :=
    MonoidHom.mk' (fun z => .ofAdd (GlobalTheory.SmGL.ord (v.adicCompletion F) z)) fun a b => by
      rw [GlobalTheory.SmGL.ord_mul, ofAdd_add]
  have hx : x = U * P ^ m := by simp [U]
  have : o x = o U * o P ^ m := by rw [hx, map_mul, map_zpow]
  have e2 : GlobalTheory.SmGL.ord (v.adicCompletion F) x = GlobalTheory.SmGL.ord (v.adicCompletion F) U +
      m * GlobalTheory.SmGL.ord (v.adicCompletion F) P := by
    have := congrArg Multiplicative.toAdd this
    simpa [o, mul_comm] using this
  rw [e2, hU0, hP1]; ring

end GlobalTheory.BCT.InertChar

open GlobalTheory.BCT.InertChar in
theorem GlobalTheory.BCT.inertChar_muLocK : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ w : Pl E, ¬ IsSplitAt w → ∀ k : Eˣ, ((μ.locK w k : ℂˣ) : ℂ) = (-1) ^ ordL (algebraMap E (w.adicCompletion E) (k : E)) := by
  intro E _ _ _ μ e hμ w hw k
  have h := hμ.2.2.1 w hw
  show ((μ.loc w (atFin w k) : ℂˣ) : ℂ) = _
  rw [h, GlobalTheory.SmGL.unrChar_apply, ord_eq_ordL]
  push_cast
  rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeCharCMLocKNonsplitEqNegOnePowStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryHeckeCharCM_locK_nonsplit_eq_neg_one_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (μ : HChar E) (e : InfinitePlace E → ℤ), IsMu μ e → ∀ w : Pl E, ¬ IsSplitAt w → ∀ k : Eˣ, ((μ.locK w k : ℂˣ) : ℂ) = (-1) ^ ordL (algebraMap E (w.adicCompletion E) (k : E)) := by
  first | exact @GlobalTheory.BCT.inertChar_muLocK | exact GlobalTheory.BCT.inertChar_muLocK | (intros; apply GlobalTheory.BCT.inertChar_muLocK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealCoordinateActionUnitaryPreservesHermitianFor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealCoordinateActionUnitaryPreservesHermitianFor
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical

noncomputable section

namespace GlobalTheory.RealWeilF

section Unitary

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem conj_tmul_one_F {σ : E →ₐ[F] E} {τ : E →+* ℂ} (hσ : ∀ x, τ (σ x) = star (τ x))
    {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmbF τ θ) (a : Ainf F) :
    starRingEnd ℂ (θ (a ⊗ₜ[F] (1 : E))) = θ (a ⊗ₜ[F] (1 : E)) := by
  refine DenseRange.induction_on (NumberField.InfiniteAdeleRing.denseRange_algebraMap F) a
    (isClosed_eq (Complex.continuous_conj.comp hθ.2) hθ.2) fun f => ?_
  have e : (algebraMap F (Ainf F) f) ⊗ₜ[F] (1 : E) = (1 : Ainf F) ⊗ₜ[F] (algebraMap F E f) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  rw [e, hθ.1, starRingEnd_apply, ← hσ, AlgHom.commutes]

theorem comp_cAF {σ : E →ₐ[F] E} {τ : E →+* ℂ} (hσ : ∀ x, τ (σ x) = star (τ x))
    {θ : Ainf F ⊗[F] E →+* ℂ} (hθ : IsInfEmbF τ θ) (z : AEF F E) :
    θ (infPartF F E (cAF σ z)) = starRingEnd ℂ (θ (infPartF F E z)) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add a b ha hb => simp only [map_add (f := _), ha, hb]
  | tmul a x =>
    have e : ∀ y : E, fstA F a ⊗ₜ[F] y = (fstA F a ⊗ₜ[F] (1 : E)) * ((1 : Ainf F) ⊗ₜ[F] y) := by
      intro y; simp
    have e2 : infPartF F E (cAF σ (a ⊗ₜ[F] x)) = fstA F a ⊗ₜ[F] (σ x) := rfl
    have e3 : infPartF F E (a ⊗ₜ[F] x) = fstA F a ⊗ₜ[F] x := rfl
    rw [e2, e3, e (σ x), e x, map_mul, map_mul, map_mul, conj_tmul_one_F hσ hθ, hθ.1, hθ.1, hσ]
    rfl

theorem compAtF_unitary {σ : E →ₐ[F] E} {tau : InfinitePlace F → (E →+* ℂ)}
    {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} (hσ : ∀ w x, tau w (σ x) = star (tau w x))
    (hθ : IsInfFamF tau θ) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (g : GAF σ J) (w : InfinitePlace F) :
    (compAtF θ w (mtF σ J g))ᴴ * J.map (tau w) * compAtF θ w (mtF σ J g) = J.map (tau w) := by
  have hg : ((mtF σ J g).map (cAF σ))ᵀ * JR (AF F) J * mtF σ J g = JR (AF F) J := g.2
  have hJ : (JR (AF F) J).map ((θ w).comp (infPartF F E)) = J.map (tau w) := by
    ext i j
    have : infPartF F E (inclR (AF F) (J i j)) = (1 : Ainf F) ⊗ₜ[F] J i j := rfl
    show θ w (infPartF F E (inclR (AF F) (J i j))) = _
    rw [this]
    exact (hθ w).1 (J i j)
  rw [← hJ]
  exact GlobalTheory.FockCompare.RealAction.unitary_map (cAF σ) ((θ w).comp (infPartF F E)) (comp_cAF (hσ w) (hθ w)) _ _ hg

theorem compAtF_mul_inv (θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)) {σ : E →ₐ[F] E} {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (g : GAF σ J) (w : InfinitePlace F) :
    compAtF θ w (mtF σ J g) * compAtF θ w (mtF σ J g⁻¹) = 1 := by
  have h1 : mtF σ J 1 = 1 := by unfold mtF; rw [map_one]; rfl
  rw [compAtF, compAtF, ← Matrix.map_mul, ← GlobalTheory.WeilPartsF.mtF_mul, mul_inv_cancel, h1,
    Matrix.map_one _ (map_zero _) (map_one _)]

end Unitary

theorem mMF_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ p : GAF σ JS × GAF σ JT, (mMF σ JS JT θ p)ᴴ * HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) * mMF σ JS JT θ p = HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT _ _ ξ₀ _ _ θ hθ ι _ p
  obtain ⟨g, h⟩ := p
  have hσ : ∀ w x, (B.emb w).1 (σ x) = star ((B.emb w).1 x) := fun w x => hB.cm.2.2.2 _ x
  unfold HMF
  rw [mMF_apply, blk_conjTranspose, blk_mul, blk_mul]
  congr 1 <;> funext w
  · rw [Matrix.mul_smul, Matrix.smul_mul, compAtF_unitary hσ hθ]
  · have h1 := compAtF_unitary hσ hθ JS g w
    have h2 := compAtF_mul_inv θ JS g w
    conv_rhs => rw [← h1, Matrix.mul_inv_rev, Matrix.mul_inv_rev, ← conjTranspose_nonsing_inv, inv_eq_right_inv h2]

end GlobalTheory.RealWeilF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealCoordinateActionUnitaryPreservesHermitianForStatement
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realCoordinateAction_unitary_preserves_hermitianForm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ p : GAF σ JS × GAF σ JT, (mMF σ JS JT θ p)ᴴ * HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) * mMF σ JS JT θ p = HMF JS JT ξ₀ (fun w : InfinitePlace F => (B.emb w).1) := by
  first | exact @GlobalTheory.RealWeilF.mMF_unitary | exact GlobalTheory.RealWeilF.mMF_unitary | (intros; apply GlobalTheory.RealWeilF.mMF_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachRingFactsUnramifiedLevelOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachRingFactsUnramifiedLevelOne
set_option autoImplicit false

noncomputable section

open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace

namespace GlobalTheory.WachPlace

theorem algHom_eq_subst {O : Type} [CommRing O] (f : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hf : constantCoeff (f X) = 0) (a : O⟦X⟧) : f a = a.subst (f X) := by
  have hs : HasSubst (f X) := HasSubst.of_constantCoeff_zero' hf
  have e : f = substAlgHom hs :=
    GlobalTheory.CycFr.algHom_ext_X f (substAlgHom hs) (X_dvd_iff.2 hf) (by rw [coe_substAlgHom, subst_X hs])
  conv_lhs => rw [e]
  rw [coe_substAlgHom]

theorem mem_mu_of_isOfFinOrder {l : ℕ} [Fact l.Prime] (h2 : l ≠ 2) (x : ℤ_[l]ˣ)
    (hx : IsOfFinOrder x) : (x : ℤ_[l]) ∈ mu l := by
  have hl : 0 < l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  rw [mu, Polynomial.mem_nthRootsFinset hl]
  have h := GlobalTheory.TorsionCard.eq_one_of_red h2 (x ^ (l - 1)) hx.pow
    (by rw [map_pow, ZMod.units_pow_card_sub_one_eq_one])
  rw [← Units.val_pow_eq_pow_val, h, Units.val_one]

theorem isUnit_sub_one_padicInt {l : ℕ} [Fact l.Prime] : IsUnit (((l - 1 : ℕ) : ℤ_[l])) := by
  have h1 : 1 ≤ l := (Fact.out : l.Prime).one_lt.le
  have e : ((l - 1 : ℕ) : ℤ_[l]) = -(1 - (l : ℤ_[l])) := by
    rw [Nat.cast_sub h1]; push_cast; ring
  rw [e, IsUnit.neg_iff]
  exact isUnit_one_sub_self_of_mem_nonunits _ (PadicInt.irreducible_p (p := l)).not_isUnit

section Situation

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {K LL : FinExt l} {n : ℕ}
  (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n)

theorem wach_φ₀_X : W.φ₀ X = (1 + X) ^ l - 1 := by rw [W.φ₀_X, W.q₀_def, P.PD_p K]

theorem wach_φ₀_eq (a : (↥(OL LL))⟦X⟧) : W.φ₀ a = phi l ↥(OL LL) a := by
  have hc : constantCoeff (W.φ₀ X) = 0 := by rw [wach_φ₀_X]; simp
  rw [algHom_eq_subst W.φ₀ hc a, wach_φ₀_X]; rfl

theorem wach_q₀_eq : W.q₀ = q l ↥(OL LL) := by
  have e1 := W.q₀_def
  rw [P.PD_p K, ← (q_multiplicative_holds l ↥(OL LL)).1] at e1
  exact mul_left_cancel₀ X_ne_zero e1

theorem wach_γ₀_eq (g : W.Gam) (z : ℤ_[l]) (hz : (W.χΓ g : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) z)
    (a : (↥(OL LL))⟦X⟧) : W.γ₀ g a = act l ↥(OL LL) z a := by
  have e := GlobalTheory.CycFr.eq_act_of_comm W.φ₀ (W.γ₀ g) z (wach_φ₀_X W) (W.γ₀_comm g) (W.γ₀_X g).1
    (by rw [(W.γ₀_X g).2, hz])
  rw [e, GlobalTheory.CycFr.act_apply]; rfl

theorem wach_χΓ_onto (hK : K.1 ≤ MaximalUnramifiedExtension l) (z : ℤ_[l]ˣ) :
    ∃ g : W.Gam, (W.χΓ g : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) (z : ℤ_[l]) := by
  obtain ⟨σ, hσ, hσz⟩ := GlobalTheory.UnramCyc.chi_onto_of_unramified P K hK z
  refine ⟨W.resΓ ⟨σ, hσ⟩, Subtype.val_injective ?_⟩
  have e := W.χΓ_res ⟨σ, hσ⟩
  rw [P.PD_χ K ⟨σ, hσ⟩] at e
  change algebraMap ↥(OL LL) ↥LL.1 _ = algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) _)
  rw [e]
  change algebraMap ℚ_[l] ↥LL.1 (P.χQ σ : ℚ_[l]) = _
  rw [hσz]; rfl

theorem wach_torsion_mem_mu (h2 : l ≠ 2) (δ : W.Gam) (hδ : δ ∈ W.DelF) :
    ∃ d ∈ mu l, (W.χΓ δ : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) d := by
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.exists_cyclotomicChar_padicInt_units P K LL W
  obtain ⟨k, hk, hδk⟩ := (W.DelF_def δ).1 hδ
  refine ⟨(χ δ : ℤ_[l]), mem_mu_of_isOfFinOrder h2 _ ?_, (hχ δ).symm⟩
  exact isOfFinOrder_iff_pow_eq_one.2 ⟨k, hk, by rw [← map_pow, hδk, map_one]⟩

theorem wach_mu_mem_torsion (hK : K.1 ≤ MaximalUnramifiedExtension l) (d : ℤ_[l]) (hd : d ∈ mu l) :
    ∃ δ ∈ W.DelF, (W.χΓ δ : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) d := by
  have hl : 0 < l - 1 := by have := (Fact.out : l.Prime).two_le; omega
  have hd1 : d ^ (l - 1) = 1 := (Polynomial.mem_nthRootsFinset hl (1 : ℤ_[l])).1 hd
  have hu : IsUnit d := IsUnit.of_pow_eq_one hd1 hl.ne'
  obtain ⟨g, hg⟩ := wach_χΓ_onto W hK hu.unit
  rw [hu.unit_spec] at hg
  refine ⟨g, (W.DelF_def g).2 ⟨l - 1, hl, W.χΓ_inj ?_⟩, hg⟩
  apply Units.ext
  rw [map_pow, Units.val_pow_eq_pow_val, hg, ← map_pow, hd1, map_one, map_one, Units.val_one]

theorem wach_invariants (hK : K.1 ≤ MaximalUnramifiedExtension l) (h2 : l ≠ 2) (a : (↥(OL LL))⟦X⟧) :
    (∀ δ ∈ W.DelF, W.γ₀ δ a = a) ↔ ∃ y, inc l ↥(OL LL) y = a := by
  have R := fixed_relation_holds l ↥(OL LL) h2 a
  constructor
  · intro ha
    obtain ⟨y, hy⟩ := R.1 (fun d hd => by
      obtain ⟨δ, hδ, hδd⟩ := wach_mu_mem_torsion W hK d hd
      rw [← wach_γ₀_eq W δ d hδd a, ha δ hδ])
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, hy⟩ δ hδ
    obtain ⟨d, hd, hδd⟩ := wach_torsion_mem_mu W h2 δ hδ
    rw [wach_γ₀_eq W δ d hδd]
    exact R.2 ⟨y, hy.symm⟩ d hd

theorem wach_card_isUnit (h2 : l ≠ 2) (hK : K.1 ≤ Ks K 1) : IsUnit (W.DelF.card : ↥(OL LL)) := by
  have hc := GlobalTheory.TorsionCard.card_torsion_mul_finrank P K LL W h2 hK
  have hu := (isUnit_sub_one_padicInt (l := l)).map (algebraMap ℤ_[l] ↥(OL LL))
  rw [map_natCast, ← hc, Nat.cast_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

end Situation

theorem ringFacts_of_caseA {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l)
    (hA : CaseA K LL) : RingFacts (H.W K 1 LL hA.2.2) :=
  ⟨wach_φ₀_eq _, wach_q₀_eq _, wach_γ₀_eq _, wach_χΓ_onto _ hA.1, wach_invariants _ hA.1 hA.2.1,
    wach_card_isUnit _ hA.2.1 hA.2.2.2.2.1⟩

end GlobalTheory.WachPlace

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WachRingFactsUnramifiedLevelOneStatement
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wachRingFacts_unramified_levelOne : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL), RingFacts (H.W K 1 LL hA.2.2) := by
  first | exact @GlobalTheory.WachPlace.ringFacts_of_caseA | exact GlobalTheory.WachPlace.ringFacts_of_caseA | (intros; apply GlobalTheory.WachPlace.ringFacts_of_caseA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitAtFnOfOfNotMem
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.Discrepancy

namespace GlobalTheory.FieldPair

section SlopeTestRemainingChoices

variable {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U) {y : X} (hy : y ∈ U)


include hU in
theorem unitAt_fnOf_of_not_mem {s : Γ(X, U)} (hs : s ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal) :
    UnitAt y (fnOf U (gen_mem hy) s) := by
  letI := X.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  haveI := hU.isLocalization_stalk ⟨y, hy⟩
  exact ⟨_, IsLocalization.map_units (X.presheaf.stalk y)
    (⟨s, hs⟩ : (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl), algebraMap_germ hy s⟩


include hU in
theorem regAt_exists_fraction {f : X.functionField} (hf : RegAt y f) :
    ∃ c s : Γ(X, U), s ∉ (hU.primeIdealOf ⟨y, hy⟩).asIdeal ∧
      f * fnOf U (gen_mem hy) s = fnOf U (gen_mem hy) c := by
  letI := X.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  haveI := hU.isLocalization_stalk ⟨y, hy⟩
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨⟨c, s⟩, e⟩ := IsLocalization.surj (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl a
  refine ⟨c, s, s.2, ?_⟩
  have e' := congrArg (algebraMap _ X.functionField) e
  rw [map_mul] at e'
  rw [← algebraMap_germ hy, ← algebraMap_germ hy]
  exact e'

end SlopeTestRemainingChoices

theorem isUnit_iff_inv_mem {K : Type} [Field K] {R : ValuationSubring K} (u : R) :
    IsUnit u ↔ (u : K) ≠ 0 ∧ (u : K)⁻¹ ∈ R := by
  constructor
  · rintro ⟨v, rfl⟩
    have h : ((v : R) : K) * ((v⁻¹ : Rˣ) : R) = 1 := by
      rw [← R.coe_mul, Units.mul_inv]; rfl
    exact ⟨left_ne_zero_of_mul_eq_one h, (inv_eq_of_mul_eq_one_right h) ▸ (v⁻¹ : Rˣ).1.2⟩
  · rintro ⟨h0, hi⟩
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hi⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩

theorem isPrimeOf_placeEquiv {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    (E : DivOver p) (x : X) :
    (placeEquiv p E).IsPrimeOf (locRing x) ↔ ∃ z, z ⤳ x ∧ E.IsAt z := by
  obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have ord0 : ∀ {b : X.functionField}, b ≠ 0 → b ∈ E.ring → b⁻¹ ∈ E.ring →
      (placeEquiv p E).ord b = 0 := fun {b} h0 h1 h2 => by
    have a1 := ((placeEquiv p E).ord_nonneg_iff h0).2 h1
    have a2 := ((placeEquiv p E).ord_nonneg_iff (inv_ne_zero h0)).2 h2
    rw [Place.ord_inv] at a2
    omega
  constructor
  · rintro ⟨hC, hP⟩
    have hT : E.Through x := (contains_placeEquiv E x).1 hC
    let φ : Γ(X, U) →+* E.ring :=
      (fnOf U (gen_mem hx)).codRestrict E.ring fun a => hT _ (regAt_fnOf hx _ a)
    let P : PrimeSpectrum Γ(X, U) := ⟨(IsLocalRing.maximalIdeal E.ring).comap φ, inferInstance⟩
    have memP (s : Γ(X, U)) : s ∉ P.asIdeal ↔
        (fnOf U (gen_mem hx) s ≠ 0 ∧ (fnOf U (gen_mem hx) s)⁻¹ ∈ E.ring) := by
      change φ s ∉ IsLocalRing.maximalIdeal E.ring ↔ _
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
      exact isUnit_iff_inv_mem (φ s)
    have hPQ : P ≤ hU.primeIdealOf ⟨x, hx⟩ := fun s hs => by_contra fun hs' =>
      have h := unitAt_fnOf_of_not_mem hU hx hs'
      (memP s).2 ⟨h.ne_zero, hT _ h.inv.regAt⟩ hs
    have hz : hU.fromSpec P ∈ U := by
      have : hU.fromSpec P ∈ Set.range hU.fromSpec := ⟨P, rfl⟩
      rwa [hU.range_fromSpec] at this
    let z : U := ⟨hU.fromSpec P, hz⟩
    have hP' : hU.primeIdealOf z = P :=
      hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf z)
    have hzx : (z : X) ⤳ x := by
      have h := ((PrimeSpectrum.le_iff_specializes P (hU.primeIdealOf ⟨x, hx⟩)).mp hPQ).map
        hU.fromSpec.continuous
      rwa [hU.fromSpec_primeIdealOf ⟨x, hx⟩] at h
    clear_value z
    refine ⟨z, hzx, fun f => ⟨fun hf => ?_, fun hf => ?_⟩⟩
    · obtain ⟨a, ha, b, hb, hb0, hord, e⟩ := hP f hf
      obtain ⟨b', t, ht, e2⟩ := regAt_exists_fraction hU hx (mem_locRing.1 hb)
      have hut := unitAt_fnOf_of_not_mem hU hx ht
      have htP : t ∉ P.asIdeal := (memP t).2 ⟨hut.ne_zero, hT _ hut.inv.regAt⟩
      have hb'0 : fnOf U (gen_mem hx) b' ≠ 0 := e2 ▸ mul_ne_zero hb0 hut.ne_zero
      have ht0 : (placeEquiv p E).ord (fnOf U (gen_mem hx) t) = 0 :=
        ord0 hut.ne_zero (hT _ hut.regAt) (hT _ hut.inv.regAt)
      have hob' : (placeEquiv p E).ord (fnOf U (gen_mem hx) b') = 0 := by
        rw [← e2, (placeEquiv p E).ord_mul hb0 hut.ne_zero, hord, ht0, add_zero]
      have hb'i : (fnOf U (gen_mem hx) b')⁻¹ ∈ E.ring :=
        ((placeEquiv p E).ord_nonneg_iff (inv_ne_zero hb'0)).1
          (by rw [Place.ord_inv, hob', neg_zero])
      have hb'P : b' ∉ P.asIdeal := (memP b').2 ⟨hb'0, hb'i⟩
      have hub' := unitAt_fnOf_of_not_mem hU z.2 (s := b') (by rw [hP']; exact hb'P)
      have hut' := unitAt_fnOf_of_not_mem hU z.2 (s := t) (by rw [hP']; exact htP)
      have hbz : UnitAt (z : X) b := by
        have eb : b = fnOf U (gen_mem hx) b' * (fnOf U (gen_mem hx) t)⁻¹ := by
          rw [← e2, mul_inv_cancel_right₀ hut.ne_zero]
        rw [eb]
        exact hub'.mul hut'.inv
      have haz : RegAt (z : X) a := regAt_of_specializes hzx (mem_locRing.1 ha)
      have ef : f = a * b⁻¹ := by rw [← e, mul_inv_cancel_right₀ hb0]
      rw [ef]
      exact haz.mul hbz.inv.regAt
    · obtain ⟨c, s, hs, e⟩ := regAt_exists_fraction hU z.2 hf
      have hs' : s ∉ P.asIdeal := by rw [← hP']; exact hs
      obtain ⟨hs0, hsi⟩ := (memP s).1 hs'
      have ef : f = fnOf U (gen_mem hx) c * (fnOf U (gen_mem hx) s)⁻¹ := by
        rw [← e, mul_inv_cancel_right₀ hs0]
      rw [ef]
      exact mul_mem (hT _ (regAt_fnOf hx _ c)) hsi
  · rintro ⟨z, hzx, hz⟩
    refine ⟨(contains_placeEquiv E x).2 (hz.through hzx), fun f hf => ?_⟩
    have hzU : z ∈ U := hzx.mem_open U.isOpen hx
    obtain ⟨c, s, hs, e⟩ := regAt_exists_fraction hU hzU ((hz f).1 hf)
    have hu := unitAt_fnOf_of_not_mem hU hzU hs
    exact ⟨_, mem_locRing.2 (regAt_fnOf hx _ c), _, mem_locRing.2 (regAt_fnOf hx _ s), hu.ne_zero,
      ord0 hu.ne_zero ((hz _).2 hu.regAt) ((hz _).2 hu.inv.regAt), e⟩

end GlobalTheory.FieldPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoeffShapeSmoothCompactSupport
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CutoffMulPolyMemCcMat
open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

namespace GlobalTheory.CutoffPoly

theorem contDiff_entry {n : ℕ} (i j : Fin n) : ContDiff ℝ ∞ (fun M : Fin n → Fin n → ℂ => M i j) :=
  (contDiff_apply ℝ (fun _ => ℂ) j).comp (contDiff_apply ℝ (fun _ => (Fin n → ℂ)) i)

theorem contDiff_eval {X σ : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (c : σ → X → ℂ)
    (hc : ∀ s, ContDiff ℝ ∞ (c s)) (P : MvPolynomial σ ℂ) :
    ContDiff ℝ ∞ (fun x => MvPolynomial.eval (fun s => c s x) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p s hp => simpa using hp.mul (hc s)

theorem cutoff_mul_poly_mem_ccMat : ∀ (n : ℕ) (ε : Fin n → Bool) (F : ℝ → ℝ) (R : ℝ), ContDiff ℝ ∞ F → (∀ x, R ≤ x → F x = 0) → ∀ P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ, (fun g : UJ ε => ((F (∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2) : ℝ) : ℂ) * MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (toM g) z.1 z.2) (fun z : Fin n × Fin n => star ((toM g) z.1 z.2))) P) ∈ CcMat (ujMat ε) := by
  intro n ε F R hF hR P
  refine mem_ccSmooth.2 ⟨?_, fun M : Fin n → Fin n → ℂ =>
    ((F (∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖M z.1.1 z.1.2‖ ^ 2) : ℝ) : ℂ) *
      MvPolynomial.eval (fun s => Sum.elim (fun (z : Fin n × Fin n) (M : Fin n → Fin n → ℂ) => M z.1 z.2)
        (fun (z : Fin n × Fin n) (M : Fin n → Fin n → ℂ) => star (M z.1 z.2)) s M) P, ?_, ?_⟩
  · refine HasCompactSupport.intro (GlobalTheory.T.isCompact_pseudoUnitary_offDiag_norm_sublevel n ε R) fun g hg => ?_
    have h : R ≤ ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2 :=
      (not_le.1 hg).le
    rw [hR _ h]; simp
  · refine ContDiff.mul (Complex.ofRealCLM.contDiff.comp (hF.comp ?_)) (contDiff_eval _ ?_ P)
    · exact ContDiff.sum fun z _ => (contDiff_norm_sq ℂ).comp (contDiff_entry _ _)
    · rintro (z | z)
      · exact contDiff_entry _ _
      · exact Complex.conjCLE.contDiff.comp (contDiff_entry z.1 z.2)
  · intro g
    congr 3
    funext s
    rcases s with z | z <;> rfl

end GlobalTheory.CutoffPoly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastSide
open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

namespace GlobalTheory.PolyShapeFinite

theorem main : ∀ (n : ℕ) (ε : Fin n → Bool) (F : ℝ → ℝ) (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ), IsBiFinite (KG ε) (fun g : UJ ε => ((F (∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2) : ℝ) : ℂ) * MvPolynomial.eval (Sum.elim (fun z : Fin n × Fin n => (toM g) z.1 z.2) (fun z : Fin n × Fin n => star ((toM g) z.1 z.2))) P) := by
  intro n ε F P
  let r : UJ ε → ℝ := fun g => ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2
  let ev : UJ ε → ((Fin n × Fin n) ⊕ (Fin n × Fin n)) → ℂ := fun g =>
    Sum.elim (fun z : Fin n × Fin n => (toM g) z.1 z.2) (fun z : Fin n × Fin n => star ((toM g) z.1 z.2))
  let L : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ →ₗ[ℂ] (UJ ε → ℂ) :=
    { toFun := fun Q g => ((F (r g) : ℝ) : ℂ) * MvPolynomial.eval (ev g) Q
      map_add' := fun Q Q' => by funext g; simp [mul_add]
      map_smul' := fun c Q => by funext g; simp [MvPolynomial.smul_eq_C_mul, mul_left_comm] }
  unfold IsBiFinite
  have hle : Submodule.span ℂ {φ : UJ ε → ℂ | ∃ k ∈ KG ε, ∃ k' ∈ KG ε, φ = fun g =>
      ((F (r (k * g * k')) : ℝ) : ℂ) * MvPolynomial.eval (ev (k * g * k')) P} ≤
      (MvPolynomial.restrictTotalDegree _ ℂ P.totalDegree).map L := by
    rw [Submodule.span_le]
    rintro φ ⟨k, hk, k', hk', rfl⟩
    obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.T.exists_poly_entries_conj_left_right_mul n (toM k) (toM k') P
    refine ⟨Q, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hQ, ?_⟩
    funext g
    have h1 : r (k * g * k') = r g := (GlobalTheory.T.offDiagBlockNorm_mul_invariant n ε).2 ⟨k, hk⟩ ⟨k', hk'⟩ g
    have h2 : toM (k * g * k') = toM k * toM g * toM k' := rfl
    have h3 : MvPolynomial.eval (ev (k * g * k')) P = MvPolynomial.eval (ev g) Q := by
      simp only [ev, h2]; exact hQe (toM g)
    show ((F (r g) : ℝ) : ℂ) * MvPolynomial.eval (ev g) Q = _
    rw [h1, h3]
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.PolyShapeFinite
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBiFiniteSubspace
open MeasureTheory Matrix GlobalTheory.Orb
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
open scoped ContDiff

namespace GlobalTheory

private lemma span_add_le {H : Type} [Group H] (K : Subgroup H) (f f' : H → ℂ) :
    Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => (f + f') (k * g * k')} ≤
      Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => f (k * g * k')} ⊔
      Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => f' (k * g * k')} := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨k, hk, k', hk', rfl⟩
  refine Submodule.mem_sup.2 ⟨_, Submodule.subset_span ⟨k, hk, k', hk', rfl⟩, _,
    Submodule.subset_span ⟨k, hk, k', hk', rfl⟩, ?_⟩
  funext g; simp

private lemma span_smul_le {H : Type} [Group H] (K : Subgroup H) (c : ℂ) (f : H → ℂ) :
    Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => (c • f) (k * g * k')} ≤
      Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => f (k * g * k')} := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨k, hk, k', hk', rfl⟩
  have : (fun g => (c • f) (k * g * k')) = c • fun g => f (k * g * k') := by funext g; simp
  rw [SetLike.mem_coe, this]
  exact Submodule.smul_mem _ c (Submodule.subset_span ⟨k, hk, k', hk', rfl⟩)

private lemma span_zero_le {H : Type} [Group H] (K : Subgroup H) :
    Submodule.span ℂ {φ : H → ℂ | ∃ k ∈ K, ∃ k' ∈ K, φ = fun g => (0 : H → ℂ) (k * g * k')} ≤ ⊥ := by
  refine Submodule.span_le.2 ?_
  rintro φ ⟨k, hk, k', hk', rfl⟩
  simp only [SetLike.mem_coe, Submodule.mem_bot]
  rfl

theorem isBiFinite_subspace : ∀ (H : Type) [Group H] (K : Subgroup H), IsBiFinite K (0 : H → ℂ) ∧
    (∀ f f' : H → ℂ, IsBiFinite K f → IsBiFinite K f' → IsBiFinite K (f + f')) ∧
    ∀ (c : ℂ) (f : H → ℂ), IsBiFinite K f → IsBiFinite K (c • f) := by
  intro H _ K
  refine ⟨?_, fun f f' hf hf' => ?_, fun c f hf => ?_⟩
  · unfold IsBiFinite
    exact Submodule.finiteDimensional_of_le (span_zero_le K)
  · unfold IsBiFinite at *
    exact Submodule.finiteDimensional_of_le (span_add_le K f f')
  · unfold IsBiFinite at *
    exact Submodule.finiteDimensional_of_le (span_smul_le K c f)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoeffShapeSmoothCompactSupport
open GlobalTheory.Orb GlobalTheory.PsCo.Pc1
open Formalism.REAL (UJ KG toM)

namespace GlobalTheory.ShapeSmoothFinite

theorem continuous_matCoord_ujMat {n : ℕ} (ε : Fin n → Bool) : Continuous (matCoord (ujMat ε)) :=
  (Units.continuous_val (M := Matrix (Fin n) (Fin n) ℂ)).comp continuous_subtype_val

theorem mem_ccMat_and_isBiFinite {n : ℕ} (ε : Fin n → Bool) (d : ℕ) (φ : Mat n → ℂ) (hφ : φ ∈ ShapeM ε d) :
    (fun g : UJ ε => φ (toM g)) ∈ CcMat (ujMat ε) ∧ IsBiFinite (KG ε) (fun g : UJ ε => φ (toM g)) := by
  obtain ⟨h0, hadd, hsmul⟩ := GlobalTheory.isBiFinite_subspace (UJ ε) (KG ε)
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    obtain ⟨H, P, ⟨hH, R, hR⟩, -, rfl⟩ := h
    exact ⟨GlobalTheory.CutoffPoly.cutoff_mul_poly_mem_ccMat n ε H R hH hR P, GlobalTheory.PolyShapeFinite.main n ε H P⟩
  | zero => exact ⟨Submodule.zero_mem _, h0⟩
  | add φ ψ _ _ h h' => exact ⟨Submodule.add_mem _ h.1 h'.1, hadd _ _ h.2 h'.2⟩
  | smul c φ _ h => exact ⟨Submodule.smul_mem _ c h.1, hsmul c _ h.2⟩

theorem stShape : GlobalTheory.PsCo.Pc1.StShape := by
  intro n ε d φ hφ
  obtain ⟨h1, h2⟩ := mem_ccMat_and_isBiFinite ε d φ hφ
  exact ⟨h1, h2, continuous_of_mem_ccSmooth (continuous_matCoord_ujMat ε) h1, (mem_ccSmooth.1 h1).1⟩

end GlobalTheory.ShapeSmoothFinite
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoCoeffShapeSmoothCompactSupportStatement
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pseudoCoeffShape_smooth_compactSupport : GlobalTheory.PsCo.Pc1.StShape := by
  first | exact @GlobalTheory.ShapeSmoothFinite.stShape | exact GlobalTheory.ShapeSmoothFinite.stShape | (intros; apply GlobalTheory.ShapeSmoothFinite.stShape <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLatticeSelfDualFgFullIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLatticeSelfDualFgFullIndex
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RatLattice

open GlobalTheory.SplitScalar GlobalTheory.CompletedLatticeFinite

theorem relIndex_comap_comap {G H : Type} [AddCommGroup G] [AddCommGroup H] (f : G →+ H) (A B : AddSubgroup H)
    (h : ∀ b ∈ B, ∃ x, f x ∈ B ∧ b - f x ∈ A) : (A.comap f).relIndex (B.comap f) = A.relIndex B := by
  rw [AddSubgroup.relIndex_comap, ← AddSubgroup.relIndex_sup_right B A,
    ← AddSubgroup.relIndex_sup_right ((B.comap f).map f) A]
  congr 1
  refine le_antisymm (sup_le_sup_right (AddSubgroup.map_comap_le _ _) _) (sup_le (fun b hb => ?_) le_sup_right)
  obtain ⟨x, hx, hb⟩ := h b hb
  rw [← add_sub_cancel (f x) b]
  exact AddSubgroup.add_mem_sup ⟨x, hx, rfl⟩ hb

theorem fg_of_denom {E : Type} [Field E] [NumberField E] {m n : ℕ} (L : AddSubgroup (Matrix (Fin m) (Fin n) E))
    (d : E) (hd : d ≠ 0) (h : ∀ x ∈ L, ∀ i j, IsIntegral ℤ (d * x i j)) : L.FG := by
  let f : Matrix (Fin m) (Fin n) (𝓞 E) →+ Matrix (Fin m) (Fin n) E :=
    AddMonoidHom.mk' (fun x => Matrix.of fun i j => d⁻¹ * (x i j : E)) fun x y => by
      ext i j
      simp [mul_add]
  have e : L = (L.comap f).map f := by
    refine (AddSubgroup.map_comap_eq_self fun x hx => ⟨Matrix.of fun i j => ⟨d * x i j, h x hx i j⟩, ?_⟩).symm
    ext i j
    show d⁻¹ * (d * x i j) = x i j
    rw [inv_mul_cancel_left₀ hd]
  have h1 : (AddSubgroup.toIntSubmodule (L.comap f)).FG := IsNoetherian.noetherian _
  have h2 := h1.map f.toIntLinearMap
  rw [e]
  exact (Submodule.fg_iff_addSubgroup_fg _).1 h2

variable {D : D7} {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

theorem exists_denom_latQ (hS : ΛS.FG) (hT : ΛT.FG) :
    ∃ d : D.host.E, d ≠ 0 ∧ ∀ x ∈ latQ S T ΛS ΛT, ∀ i j, IsIntegral ℤ (d * x i j) := by
  classical
  obtain ⟨dS, hdS, hS'⟩ := exists_denom ΛS hS
  obtain ⟨dT, hdT, hT'⟩ := exists_denom ΛT hT
  obtain ⟨dA, hdA, hA'⟩ := D.host.AA.2
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
    ((Finset.univ : Finset (Fin S.rank × Fin S.rank)).image fun p => S.gram p.1 p.2)
  have hdA0 : (dA : D.host.E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hdA
    exact_mod_cast this
  have hd : (dA : D.host.E) * dT * (star dS * (y : D.host.E)) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hdA0 hdT) (mul_ne_zero (star_ne_zero.2 hdS) (by exact_mod_cast hy0))
  set d : D.host.E := (dA : D.host.E) * dT * (star dS * (y : D.host.E)) with hdd
  have hgen : ∀ a ∈ D.host.AA, ∀ s ∈ ΛS, ∀ t ∈ ΛT, ∀ i j,
      IsIntegral ℤ (d * (a * t i * ∑ k, star (s k) * S.gram k j)) := by
    intro a ha s hs t ht i j
    have e : d * (a * t i * ∑ k, star (s k) * S.gram k j) =
        ((dA : D.host.E) * a) * (dT * t i) * ∑ k, star (dS * s k) * ((y : D.host.E) * S.gram k j) := by
      simp only [hdd, Finset.mul_sum, star_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    refine IsIntegral.mul (IsIntegral.mul ?_ (hT' t ht i)) (IsIntegral.sum _ fun k _ =>
      (isIntegral_star D (hS' s hs k)).mul ?_)
    · obtain ⟨b, hb⟩ := hA' a ha
      have : (dA : D.host.E) * a = (b : D.host.E) := hb.symm
      rw [this]
      exact b.isIntegral_coe
    · have := hy (S.gram k j) (Finset.mem_image.2 ⟨(k, j), Finset.mem_univ _, rfl⟩)
      simpa [zsmul_eq_mul] using this
  have hlat : ∀ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
      ∀ i j, finPart D (l i j) ∈ GlobalTheory.AdLat.hat1 D.host.F
        ((FractionalIdeal.spanSingleton (𝓞 D.host.E)⁰ d⁻¹ : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Set D.host.E) := by
    intro l hl i j
    induction hl using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, -, a, ha, s, hs, t, ht, rfl⟩ := hw
      exact AddSubgroup.subset_closure ⟨α, hα, _, (mem_spanSingleton_inv d hd _).2 (hgen a ha s hs t ht i j), rfl⟩
    | zero => rw [Matrix.zero_apply, RingHom.map_zero]; exact zero_mem _
    | add x z _ _ hx hz => rw [Matrix.add_apply, RingHom.map_add (f := _)]; exact add_mem hx hz
    | neg x _ hx => rw [Matrix.neg_apply, RingHom.map_neg]; exact neg_mem hx
  exact ⟨d, hd, fun x hx i j =>
    (mem_spanSingleton_inv d hd _).1 (((GlobalTheory.AdLat.adelicCompletion_fractionalIdeal_properties D.host.F D.host.E).2.1 _ (x i j)).1 (hlat _ hx i j))⟩

theorem exists_rat_add_nsmul (Λ : AddSubgroup (WO S T)) (hinf : ∀ u ∈ Λ, u.map (infPart D) = 0)
    (happ : ∀ γ : WO S T, γ.map (infPart D) = 0 → ∃ ρ ∈ ratL T S, ∃ u ∈ Λ, (γ - ρ - u).map (finPart D) = 0)
    {z : WO S T} (hz : z.map (infPart D) = 0) {N : ℕ} (hN : 0 < N) :
    ∃ y, ∃ u ∈ Λ, z = finRat S T y + N • u := by
  obtain ⟨γ, hγ, hNγ⟩ := GlobalTheory.RatSelfDual.exists_div hz hN
  obtain ⟨ρ, ⟨y₀, hy₀⟩, u, hu, hz⟩ := happ γ hγ
  have hγe : γ = finRat S T y₀ + u := by
    refine Matrix.ext fun i j => adele_ext ?_ ?_
    · have e0 : infPart D (γ i j) = 0 := congrFun (congrFun hγ i) j
      have e1 : infPart D (finRat S T y₀ i j) = 0 := congrFun (congrFun (finRat_inf S T y₀) i) j
      have e2 : infPart D (u i j) = 0 := congrFun (congrFun (hinf u hu) i) j
      rw [Matrix.add_apply, RingHom.map_add (f := _), e0, e1, e2, add_zero]
    · have e0 : finPart D (γ i j - ρ i j - u i j) = 0 := congrFun (congrFun hz i) j
      have e1 : finPart D (finRat S T y₀ i j) = finPart D (ρ i j) := by rw [← hy₀]; rfl
      rw [RingHom.map_sub, RingHom.map_sub, sub_sub, sub_eq_zero] at e0
      rw [Matrix.add_apply, RingHom.map_add (f := _), e1, e0]
  exact ⟨N • y₀, u, hu, by rw [← hNγ, hγe, nsmul_add, (finRat S T).map_nsmul]⟩

theorem actO_inv_actO (g : GA D S) (h : GA D T) (x : XF S T) :
    rhoF S T (g, h) (rhoF S T (g⁻¹, h⁻¹) x) = x ∧ rhoF S T (g⁻¹, h⁻¹) (rhoF S T (g, h) x) = x := by
  constructor
  · rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_inv_cancel, mul_inv_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]
  · rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, inv_mul_cancel, Prod.mk_one_one, map_one,
      Module.End.one_apply]

theorem mem_map_rhoF (A : Submodule (𝓞 D.host.E) (XF S T)) (g : GA D S) (h : GA D T) (x : XF S T) :
    x ∈ A.map (rhoF S T (g, h)) ↔ rhoF S T (g⁻¹, h⁻¹) x ∈ A :=
  ⟨fun ⟨y, hy, e⟩ => by rwa [← e, (actO_inv_actO g h y).2], fun hx => ⟨_, hx, (actO_inv_actO g h x).1⟩⟩

def finX (S T : HSp D) : Matrix (Fin T.rank) (Fin S.rank) D.host.E →+ XF S T :=
  AddMonoidHom.mk' (fun x => XF.mk (finRat S T x) (finRat_inf S T x)) fun x y => XF.ext ((finRat S T).map_add x y)

theorem rhoF_finX {g : GA D S} {h : GA D T} {a : Matrix (Fin S.rank) (Fin S.rank) D.host.E}
    {b : Matrix (Fin T.rank) (Fin T.rank) D.host.E} (ha : Formalism.L2.Theta.mt S g = a.map (incA D))
    (hb : Formalism.L2.Theta.mt T h⁻¹ = b.map (incA D)) (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    rhoF S T (g⁻¹, h⁻¹) (finX S T x) = finX S T (b * x * a) := by
  apply XF.ext
  show actO S T g⁻¹ h⁻¹ (finRat S T x) = finRat S T (b * x * a)
  rw [finRat_eq, finRat_eq, actO_smul, actO, inv_inv, ha, hb]
  congr 1
  exact ((Matrix.map_mul (f := incA D)).trans (congrArg (· * a.map (incA D)) (Matrix.map_mul (f := incA D)))).symm

theorem latQ_selfDual_fg_full_index : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → SelfDual (gamQ ψ S T) (latQ S T ΛS ΛT) ∧ (latQ S T ΛS ΛT).toAddSubgroup.FG ∧ (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • x ∈ latQ S T ΛS ΛT) ∧ ∀ (g : GA D S) (h : GA D T) (a : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (b : Matrix (Fin T.rank) (Fin T.rank) D.host.E), Formalism.L2.Theta.mt S g = a.map (incA D) → Formalism.L2.Theta.mt T h⁻¹ = b.map (incA D) → idx (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T (g, h))) = (latQ S T ΛS ΛT).toAddSubgroup.relIndex ((latQ S T ΛS ΛT).toAddSubgroup.comap (sandw b a).toAddMonoidHom) := by
  intro D ψ hψ S T ΛS ΛT hS hT
  obtain ⟨hdual, happ, -⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  have hden := GlobalTheory.VacUnique.Den.exists_nsmul_finRat_mem D S T ΛS ΛT
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice S ΛS hS)
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice T ΛT hT)
  refine ⟨fun x => ?_, ?_, fun x => ?_, fun g h a b ha hb => ?_⟩
  · refine (GlobalTheory.RatSelfDual.finRat_mem_iff D S T ψ _ hψ (fun u hu => latO_fin hu) hdual happ hden x).trans ?_
    exact forall₂_congr fun y _ => (GlobalTheory.RatSelfDual.psi_fin_iff hψ S T x y).symm
  · obtain ⟨d, hd, h⟩ := exists_denom_latQ (S := S) (T := T) hS.1.fg hT.1.fg
    exact fg_of_denom _ d hd h
  · obtain ⟨N, hN, h⟩ := hden x
    exact ⟨N, hN, by rwa [mem_latQ, map_nsmul]⟩
  · obtain ⟨N, hN, hmov⟩ := (GlobalTheory.LatLevel.level_of_generators D S T ΛS ΛT hS hT
      (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hS hT)).2 g⁻¹ h⁻¹
    rw [GlobalTheory.FinWeil.idx, ← relIndex_comap_comap (finX S T)]
    · congr 1
      refine AddSubgroup.ext fun x => (mem_map_rhoF _ g h (finX S T x)).trans ?_
      rw [rhoF_finX ha hb]
      rfl
    · intro z hz
      obtain ⟨y, u, hu, e⟩ := exists_rat_add_nsmul _ (fun u hu => latO_fin hu) happ z.fin hN
      have e' : z = finX S T y + N • XF.mk u (latO_fin hu) := XF.ext e
      have h1 : N • XF.mk u (latO_fin hu) ∈ (latF S T ΛS ΛT).map (rhoF S T (g, h)) := by
        rw [mem_map_rhoF, map_nsmul]
        exact hmov u hu
      refine ⟨y, ?_, ?_⟩
      · rw [← sub_eq_iff_eq_add.2 e']
        exact sub_mem hz h1
      · rw [sub_eq_iff_eq_add'.2 e']
        exact nsmul_mem (show XF.mk u (latO_fin hu) ∈ latF S T ΛS ΛT from hu) N

end GlobalTheory.RatLattice

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLatticeSelfDualFgFullIndexStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts GlobalTheory.FinWeil GlobalTheory.FinWeilO GlobalTheory.FockCompare GlobalTheory.VacUnique GlobalTheory.RatAut
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_lattice_selfDual_fg_full_index : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → SelfDual (gamQ ψ S T) (latQ S T ΛS ΛT) ∧ (latQ S T ΛS ΛT).toAddSubgroup.FG ∧ (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • x ∈ latQ S T ΛS ΛT) ∧ ∀ (g : GA D S) (h : GA D T) (a : Matrix (Fin S.rank) (Fin S.rank) D.host.E) (b : Matrix (Fin T.rank) (Fin T.rank) D.host.E), Formalism.L2.Theta.mt S g = a.map (incA D) → Formalism.L2.Theta.mt T h⁻¹ = b.map (incA D) → idx (latF S T ΛS ΛT) ((latF S T ΛS ΛT).map (rhoF S T (g, h))) = (latQ S T ΛS ΛT).toAddSubgroup.relIndex ((latQ S T ΛS ΛT).toAddSubgroup.comap (sandw b a).toAddMonoidHom) := by
  first | exact @GlobalTheory.RatLattice.latQ_selfDual_fg_full_index | exact GlobalTheory.RatLattice.latQ_selfDual_fg_full_index | (intros; apply GlobalTheory.RatLattice.latQ_selfDual_fg_full_index <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaEqOfReal
open NumberField Matrix
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem theta_eq_of_real : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D), IsStdChar D ψ (-1) →
    ∀ f f' : WO V W → ℂ, IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' →
      (∀ w : WO V W, w.map (finPart D) = 0 → f w = f' w) → f = f' := by
  intro D ψ V W _ f f' hf hf' h
  have h0 : f + (-1 : ℂ) • f' = 0 := GlobalTheory.TwistFactorCompare.theta_eq_zero_of_real
    (GlobalTheory.WeilVacMove.isTheta_add hf (GlobalTheory.WeilVacMove.isTheta_smul (-1) hf')) fun w hw => by
      rw [Pi.add_apply, Pi.smul_apply, h w hw, neg_one_smul, add_neg_cancel]
  rwa [neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at h0

end GlobalTheory.AdTh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncChartBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory.LogPair

theorem sncChart_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (d : ℕ) (s : ℕ) (L : Fin s → LB X) (σ : ∀ i, (L i).Sec) (C : SncChart f d L σ), IsPullback π f' f (spMap φ) → ∃ C' : SncChart f' d (fun i => (L i).pull π) (fun i => Cartier.secPull (σ i) π), C'.U = π ⁻¹ᵁ C.U := by
  intro R R' _ _ φ X X' f f' π d s L σ C hP
  obtain ⟨hA, hE⟩ := GlobalTheory.T.isEtaleCoordinatesOnOpen_baseChange_preimage R R' φ X X' f f' π C.U d C.t hP C.affine C.etale
  refine ⟨{
    U := π ⁻¹ᵁ C.U
    affine := hA
    t := fun a => (π.app C.U).hom (C.t a)
    etale := hE
    c := fun i => fun _ => C.c i
    le := fun i => (π.preimage_mono (C.le i)).trans (Cartier.pull_U (L i) π fun _ => C.c i).ge
    e := C.e
    inj := C.inj
    u := fun i => Units.map (π.app C.U).hom (C.u i)
    eq := fun i => ?_ }, rfl⟩
  show resG X' _ (resG X' _ ((π.app _).hom ((σ i).f (C.c i)))) = _
  rw [Cartier.resG_resG, ← Cartier.app_resG π (C.le i), C.eq i, map_mul]
  rcases h : C.e i with _ | a
  · simp
  · simp
end GlobalTheory.LogPair
end
