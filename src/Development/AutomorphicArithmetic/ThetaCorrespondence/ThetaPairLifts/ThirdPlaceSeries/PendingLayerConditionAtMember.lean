module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPendingObjectsDepthZeroAdmissibleEigenSpan
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitLocalOfGreen
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TiedConditionOfLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SClose
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsTrueReading
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FirstTermConditionHoldsAllStages
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsBisFurther
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIotaOQOfDataStatement

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerSide
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisDepthZeroEntrywise
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisBlockTypeSplit
set_option synthInstance.maxHeartbeats 200000

section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.PendOf GlobalTheory.LevelType
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.BlockTypeSplit
open ValuativeRel Polynomial
section Finite
end Finite
section Local
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
variable {p : ℕ} [Fact p.Prime] {r t : ℕ}
theorem block_type_split_local_alt (hP : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hp : resCard F = p) (L : GlobalTheory.GLq.LabelDatum p) {χ : Fˣ →* ℂˣ}
    (hχ : IsSmoothChar χ) (hχt : IsTame χ) {θ : (ZMod p)ˣ →* ℂˣ} (hθχ : CharLift θ χ) {u : ZMod p}
    (hθ : GlobalTheory.GLp.IsCharLab L θ u) (π : Irr F (r + t)) (ρ : FDRep ℂ (GL (Fin r) (ZMod p))) (hρ : CategoryTheory.Simple ρ)
    {f : (ZMod p)[X]} (hf : GlobalTheory.GLq.HasLabel L (fun x => ρ.character x) f) (hu : ¬ f.IsRoot u) {x : π.V}
    (hx : IsBlockVec χ π.π x) (hxρ : NotKilled π.π (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) x) :
    ∃ (π₁ : Irr F r) (π₂ : Irr F t), IsSpherical π₂.π ∧
      Nonempty (π.π.Equiv (prod₂ π₁.π (_root_.GlobalTheory.SmGL.twist π₂.π (detChar (Fin t) χ)))) ∧
      ∃ y, IsLevelOne π₁.π y ∧ NotKilled π₁.π (Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ) y := by
  classical
  have hBZ := hP.bz
  have hG := hP.geo
  have hM := hP.mp
  obtain ⟨v, hv, hb, ℓ, hℓ, hzv⟩ := GlobalTheory.T.exists_fixed_parahoricBlockVector_of_idempotent F p r t χ _ π.π _ x hp (GlobalTheory.SerOSys.zIdem_idem_central ρ hρ).1 hx hxρ
  obtain ⟨Y, _, _, τ, hτ, hsub, y, hy0, hy, hyρ⟩ :=
    GlobalTheory.T.tame_character_parahoric_invariant hM F p r t χ _ π.π _ v ℓ hp π.smooth π.irr hχt hv hb hℓ hzv
  obtain ⟨s, d, σ, hsupp, hle⟩ := GlobalTheory.T.parahoricBlockTypeVector_cuspidalSupport_tame_characters hBZ hG hP.unl hM F r t χ π v hχ hχt hv hb
  rcases hle.lt_or_eq with hlt | heq
  · exfalso
    obtain ⟨-, hσ, e₀, hπσ⟩ := hsupp
    obtain ⟨b, fr, gc, S, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG F).1 (hG F).2 e₀
      (two (stdSum (rfl : r + t = r + t))) (fun a => (σ a).smooth)
      (fun a => hasFiniteLength_of_isIrreducible (σ a).irr) hτ
      (hsub.trans (isSubquotient_jac_two _ (isSmooth_parInd _ _) hπσ))
    set A := {a | d a = 1 ∧ ∃ α : ℂˣ, Nonempty ((σ a).π.Equiv (detRep (Fin (d a)) (χ * unrChar F α)))} with hA
    obtain ⟨i, hi, hi0⟩ : ∃ i ∈ A, b.1 i true = 0 := by
      by_contra! hc
      have h2 := b.2.2 true
      have h3 : A.ncard ≤ ∑ i, b.1 i true := by
        rw [Set.ncard_eq_toFinset_card' A, Finset.card_eq_sum_ones]
        exact (Finset.sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.2 (hc i (Set.mem_toFinset.1 hi))).trans
          (Finset.sum_le_sum_of_subset (Finset.subset_univ _))
      simp only [Fintype.card_fin] at h2
      omega
    obtain ⟨hd, α, hα⟩ := hi
    have hi1 : b.1 i false = 1 := by
      have h1 := b.2.1 i
      simp [Fintype.sum_bool] at h1
      omega
    have hact := GlobalTheory.T.jacquetSubquotient_detCharacter_factors_integral F _ Bool (b.1 i) (fr i) _ (σ i).π _ (S i) hα (hrow i) false
    obtain ⟨w, hw⟩ := typeVec_first (fun j => multiProd (gc j) fun i => (S i j).ρ) (fun j => isSmooth_parInd _ _) hcol hyρ
    obtain ⟨φ, hφ0, hφ⟩ := GlobalTheory.T.exists_equivariantMap_of_levelTypeVector F p (Fin r) _ _ ρ w hp hw
    obtain ⟨v', hv', hpar⟩ := GlobalTheory.T.exists_parabolicTypeVector_of_equivariantMap F p (Fin s) (Fin r) (fun i => Fin (b.1 i false)) (gc false) _
      (fun i => (S i false).ρ) i θ χ _ ρ.ρ φ hp hθχ (fun g hg v => by
        rw [hact g hg v, MonoidHom.mul_apply,
          isUnram_unrChar F α _ (GlobalTheory.StepData.valuation_det_of_mem_KO hg), mul_one]) hφ0 hφ
    exact hu (isRoot_of_parVec L (gc false) i ρ hρ hf hθ (by rw [Fintype.card_fin, hi1]) hv' hpar)
  · obtain ⟨π₁, π₂, ⟨φ⟩, hno⟩ := GlobalTheory.T.irreducible_split_exact_twistCount_product hBZ hG hP.unl F r t χ π s d σ hχ hsupp heq.symm
    have hsph := GlobalTheory.T.spherical_twist_of_blockTypeVector hBZ hG hM F r t χ π π₁ π₂ v hχ hχt hno ⟨φ⟩ hv hb
    refine ⟨π₁, GlobalTheory.SplitPairLift.twistIrr π₂ hχ.inv, hsph, ?_, ?_⟩
    · have h := GlobalTheory.SplitPairLift.twist_twist_inv π₂ χ⁻¹
      rw [inv_inv] at h
      show Nonempty (π.π.Equiv (prod₂ π₁.π (_root_.GlobalTheory.SmGL.twist (_root_.GlobalTheory.SmGL.twist π₂.π (detChar (Fin t) χ⁻¹)) (detChar (Fin t) χ))))
      rw [h]
      exact ⟨φ⟩
    obtain ⟨E⟩ := Exponents.prod₂_equiv_multiProd F r t _ _ π₁.π π₂.π
    let Ψ := φ.trans E
    have hρs : ∀ i, IsSmooth (Exponents.twoRep π₁.π π₂.π i) := fun i => by
      cases i
      · exact π₁.smooth
      · exact π₂.smooth
    have hρl : ∀ i, HasFiniteLength (Exponents.twoRep π₁.π π₂.π i) := fun i => by
      cases i
      · exact hasFiniteLength_of_isIrreducible π₁.irr
      · exact hasFiniteLength_of_isIrreducible π₂.irr
    obtain ⟨b, fr, gc, S, hrow, hcol⟩ := exists_cell_of_isSubquotient (hG F).1 (hG F).2
      (two (stdSum (rfl : r + t = r + t))) (two (stdSum (rfl : r + t = r + t))) hρs hρl hτ
      (hsub.trans (isSubquotient_jac_two _ (isSmooth_parInd _ _)
        (IsSubquotient.of_injective Ψ.toIntertwiningMap Ψ.toLinearEquiv.injective)))
    obtain ⟨z, hz0, hz⟩ := GlobalTheory.T.levi_rep_parabolic_char F Bool (Two (Fin r) (Fin t)) _ (fun j => multiProd (gc j) fun i => (S i j).ρ)
      Y τ true χ y (fun j => isSmooth_parInd _ _) hχ hcol hy0 hy
    obtain ⟨w, hw0, hw⟩ := GlobalTheory.T.exists_levi_block_eigenvector_at_identity F Bool (fun i => Fin (b.1 i true)) (Fin t) (gc true) _
      (fun i => (S i true).ρ) χ z hz0 hz
    have hm : b.1 false true = 0 := by
      by_contra hm
      obtain ⟨z', hz'0, hz'⟩ := GlobalTheory.T.levi_rep_parabolic_char F Bool (fun i => Fin (b.1 i true)) _ (fun i => (S i true).ρ) _
        (piTensor fun i => (S i true).ρ) false χ w (fun i => (S i true).smooth) hχ (IsSubquotient.refl _) hw0 (hw false)
      obtain ⟨α, hα⟩ := GlobalTheory.T.inSupport_mul_unramifiedChar_of_integralEigenvector hBZ hG hM F _ _ (S false true).ρ χ z' (S false true).smooth (S false true).irr hχ
        (Nat.pos_of_ne_zero hm) hz'0 hz'
      exact hno α (GlobalTheory.T.charInCuspidalSupport_of_jacquet_subquotient_factor hBZ hG F r _ π₁.π Bool (b.1 false) (fr false) (S false) true _ π₁.smooth (hrow false) hα)
    have hm' : b.1 true false = 0 := by
      have h1 := b.2.1 false
      have h2 := b.2.2 false
      simp [Fintype.sum_bool] at h1 h2
      omega
    obtain ⟨w₁, hw₁⟩ := typeVec_first (fun j => multiProd (gc j) fun i => (S i j).ρ) (fun j => isSmooth_parInd _ _) hcol hyρ
    obtain ⟨φ₁, h1⟩ := GlobalTheory.T.jacquetSubquotient_firstFactor_of_emptySecondBlock F r (b.1 false) (fr false) _ π₁.π (S false) hm (hrow false)
    obtain ⟨φ₂, h2⟩ := GlobalTheory.T.parabolicInduction_emptySecond_isSubquotient_first F r (fun i => b.1 i false) (gc false) (fun i => S i false) hm'
    obtain ⟨y₁, hy₁⟩ := TypeVec.up π₁.smooth (h2.trans ((GlobalTheory.T.isSubquotientRepresentation_two_reindexings F _ _ φ₂ φ₁ _ (S false false).ρ).trans h1)) hw₁
    exact ⟨y₁, typeVec_iff _ _ _ hy₁⟩
end Local
open Formalism.BasicNotions GlobalTheory.HeightCounting in
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D),
    GreenLab Γ → _root_.GlobalTheory.PendOf.SplitLocalCondition hL D := by
  intro hP hL D Γ hΓ k v χ hχ u π ρ f ht hlab hser hu ⟨x, hx, hxρ⟩
  have hchi := _root_.UpperTheory.Lit.Dz.localGlobalCompatibility_cmDatum_alt hL D Γ k v χ hχ u ht hlab
  have h0 : idemOf D k ρ ≠ 0 := fun e => by
    obtain ⟨ℓ, -, h⟩ := hxρ
    refine h ?_
    rw [e]
    simp
  obtain ⟨L, h1, h2, hf⟩ := @exists_hasLabel _ ⟨D.host.g_prime k⟩ _ (D.ntypes.teichC_inj k) _ (Γ.ζ_gen k) (Γ.O k) (hΓ k)
    _ ρ hser.1 f h0 (by rw [← Γ.eSer_def]; exact hser.2)
  refine (And.right hchi L h1 h2).elim fun θ hθ => ?_
  exact @_root_.GlobalTheory.BlockTypeSplit.block_type_split_local_alt _ _ _ _ _ _ ⟨D.host.g_prime k⟩ _ _ hP (And.left hchi) L χ hχ ht θ hθ.1 u hθ.2 π ρ hser.1 f hf hu x hx hxρ
end GlobalTheory.BlockTypeSplit
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitLoc_of_greenLab_depth_zero : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (Γ : GrpSide D), GreenLab Γ → _root_.GlobalTheory.PendOf.SplitLocalCondition hL D := by
  first | exact @_root_.GlobalTheory.BlockTypeSplit.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.BlockTypeSplit.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.BlockTypeSplit.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsDepthZeroFixedVector
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.VectorAtSplitPlace
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreTail
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreTail
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.TypeVecEig
theorem main_alt_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = D.naut.plGw k v → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ F ∈ D.naut.typeV i PI, ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) = GlobalTheory.BlockType.blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • (P.M.loc i).real F := by
  intro hL D P S hT i PI k v s hw hsw c hcont hci F _hF x hx hh
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, j.1 + 1 = D.nd.j i :=
    ⟨⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, by have := D.nd.j_range i; simp only; omega⟩
  obtain ⟨ψ₀, ξ, hψ, hξ, hlev⟩ := P.H.level.uni i j hj k v s hsw
  have hcv := GlobalTheory.SplitConjVal.valuation_eq s c hcont hci
  obtain ⟨h1, h2⟩ := GlobalTheory.BlockConj.facts_of_mem s D.R.r D.R.t c hcv (s.loc D.R.nV x) hh
  obtain ⟨i1, -⟩ := GlobalTheory.BlockConj.facts_of_mem s D.R.r D.R.t c hcv (s.loc D.R.nV x)⁻¹
    (by
      have := (GlobalTheory.BlockType.blockGrp _ _ _).inv_mem hh
      convert this using 1
      exact map_inv (Matrix.GeneralLinearGroup.map (n := Fin (D.R.r + D.R.t)) c.toRingHom) _)
  have huni : NG.UniRT s D.R.r (s.loc D.R.nV x) := by
    refine ⟨⟨GlobalTheory.BlockConj.mem_GLint_of (fun a b => ?_) (fun a b => ?_), fun a b ha hb => ?_⟩,
      fun a b ha hb => ⟨fun hlt => ?_, fun he => ?_⟩⟩
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h1 a b)
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (i1 a b)
    · have := h2 a b hb
      split_ifs at this with e
      · rw [e] at ha; omega
      · rwa [sub_zero] at this
    · have := h2 a b hb
      split_ifs at this with e
      · rw [e] at hlt; omega
      · rwa [sub_zero] at this
    · subst he
      have := h2 a a ha
      split_ifs at this with e
      · exact this
      · exact absurd rfl e
  have hxJ : x ∈ (P.M.loc i).J := (hlev.mem x hx).2 huni
  have hTS : (P.M.loc i).real F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]; exact LinearMap.mem_range_self _ _
  have hrt := hTS.2 ⟨x, hxJ⟩
  let h : GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E) :=
    Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)
  have hh' : h ∈ GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t := hh
  have hdet := GlobalTheory.BlockConjDet.val_det_mul_sub_one_lt hh'
  have hne2 : (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_sub, Valuation.map_neg, map_one] at hdet
    exact lt_irrefl _ hdet
  have hc_det : c (NG.detDD s D.R.r (s.loc D.R.nV x)) =
      (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det := by
    let e : Fin D.R.t ≃ {y : Fin D.R.nV // D.R.r ≤ y.val} :=
      { toFun := fun a => ⟨Fin.natAdd D.R.r a, by simp⟩
        invFun := fun y => ⟨y.1.val - D.R.r, by
          have h1 := y.1.2; have h2 := y.2; change y.1.val < D.R.r + D.R.t at h1; omega⟩
        left_inv := fun a => by ext; simp
        right_inv := fun y => by ext; simp; have := y.2; omega }
    rw [NG.detDD, ← Matrix.det_submatrix_equiv_self e]
    exact c.toRingHom.map_det _
  have hF0 : NG.detDD s D.R.r (s.loc D.R.nV x) ≠ 0 := fun h0 => hne2 (by rw [← hc_det, h0, map_zero])
  let u := Units.mk0 _ hF0
  have hchr := hlev.chr x hxJ hx u rfl
  have hsup : ψ₀ (NG.supDiag s D.R.r (s.loc D.R.nV x)) = 1 := hψ.1 _ (by
    unfold NG.supDiag
    refine Valuation.map_sum_lt _ one_ne_zero fun p _ => Valuation.map_sum_lt _ one_ne_zero fun q _ => ?_
    split_ifs with h
    · have := h2 p q h.2
      split_ifs at this with e
      · rw [e] at h; omega
      · rwa [sub_zero] at this
    · rw [map_zero]; exact zero_lt_one)
  have hμ := hT.mu i s.w hw j hj
  have hξμ := GlobalTheory.ConjDense.eq_of_agree s c hcont hci (S i s.w hw).mu ξ hμ.1 hξ.1
    (fun k => by rw [hξ.2 k, hμ.2 k]) u
  have hbc : GlobalTheory.BlockType.blockChar (S i s.w hw).mu h =
      (((S i s.w hw).mu (Units.map c.toMonoidHom u) : ℂˣ) : ℂ) :=
    GlobalTheory.BlockType.blockChar_eq _ _ _ (by rw [← hc_det]; rfl)
  change _ = GlobalTheory.BlockType.blockChar (S i s.w hw).mu h • _
  rw [hbc, ← hξμ, hrt, hchr, hsup, one_mul]
end GlobalTheory.TypeVecEig
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsMoreTailStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_iso_split_place_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E) (hw : IsSplitPl D.host s.w), s.w = D.naut.plGw k v → ∀ c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E, Continuous c → (∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x) → ∀ F ∈ D.naut.typeV i PI, ∀ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x → Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t → NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) = GlobalTheory.BlockType.blockChar (S i s.w hw).mu (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • (P.M.loc i).real F := by
  exact _root_.GlobalTheory.TypeVecEig.main_alt_alt
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DzVecLoc
theorem vector_at_split_place (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (hC : GlobalTheory.HeightCounting.Up.CenLoc D P.M) (S : Reading P.T)
    (hT : _root_.GlobalTheory.NPin.IsFaithfulReading P S) (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E)
    (hw : IsSplitPl D.host s.w) (hs : s.w = D.naut.plGw k v) (ρ : FDRep ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))))
    (hρ : CategoryTheory.Simple ρ) (hocc : PairedCharacterCondition.RT.Occurs i PI k v (idemOf D k ρ)) :
    ∃ x, IsBlockVec (S i s.w hw).mu ((S i s.w hw).rep PI).π x ∧ NotKilled ((S i s.w hw).rep PI).π (idemOf D k ρ) x := by
  classical
  have hrep := hT.rep i s hw PI
  rcases hrep with ⟨c, T, hc, hcs, -, -, -⟩
  obtain ⟨F, hF, hne⟩ := hocc
  set z := idemOf D k ρ with hz
  have hzc : ∀ b, z * b = b * z := by
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    exact (GlobalTheory.SerOSys.zIdem_centralIdempotent ρ hρ).2
  have hcen := GlobalTheory.SeriesSupportTest.atPlace_central D k v z hzc
  obtain ⟨L, hLift, hCL⟩ := hC i
  have e : (P.M.loc i).real (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) F) =
      actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) ((P.M.loc i).real F) := by
    rw [NTypes.onMt, dite_eq_left hcen]; exact hCL ⟨_, hcen⟩ F
  have hne' : actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) ((P.M.loc i).real F) ≠ 0 := by
    rw [← e]; intro h0; apply hne; exact (P.M.loc i).real_inj (h0.trans (map_zero _).symm)
  let g : GL (Fin D.R.r) (ZMod (D.host.g k)) → G0g D.nd := fun h =>
    Pi.mulSingle (M := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) ⟨k, v⟩ h
  have hsum : actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v z) ((P.M.loc i).real F) =
      ∑ h, z.coeff h • NG.rt D.host.E D.R.nV (L (g h)) ((P.M.loc i).real F) := by
    unfold actSum Formalism.MainNotions.ArithmeticCylinders.atPlace
    rw [MonoidAlgebra.coeff_ofCoeff, Finsupp.sum_mapDomain_index
      (h := fun g c => c • NG.rt D.host.E D.R.nV (L g) ((P.M.loc i).real F))
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
    exact Finsupp.sum_fintype _ _ (fun _ => zero_smul _ _)
  have hg : ∀ h, ∃ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x ∧ IsLiftN h (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) ∧ NG.rt D.host.E D.R.nV (L (g h)) ((P.M.loc i).real F) = NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) := fun h =>
    _root_.GlobalTheory.T.lift_through_completion_iso_alt hL D P i PI k v s hs c hc hcs L hLift F hF h (g h) (by simp [g]) (fun kv hkv => by simp [g, Pi.mulSingle_eq_of_ne hkv])
  choose xs hxs using hg
  have hne'' : ∑ h, z.coeff h • NG.rt D.host.E D.R.nV (xs h) ((P.M.loc i).real F) ≠ 0 := by
    rw [hsum] at hne'
    simpa only [(hxs _).2.2] using hne'
  obtain ⟨U, hU, h1U, hθU⟩ := GlobalTheory.T.charOfLowerRightBlockDet_eventually_eq_one _ D.R.r D.R.t (S i s.w hw).mu (S i s.w hw).mu_ok.1
  have hFS : (P.M.loc i).real F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i PI) := by
    have := hF; rw [P.H.av.typeV] at this; exact this
  obtain ⟨y, hy, hyz⟩ := GlobalTheory.T.local_component_continuous_iso_fixed D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i PI) (P.H.av.irr i PI) s
    ((S i s.w hw).rep PI).toIrrRep (hT.rep i s hw PI) c hc hcs (GlobalTheory.BlockType.blockGrp _ D.R.r D.R.t)
    (GlobalTheory.BlockType.blockChar (S i s.w hw).mu) U (fun h hh => hh.1) (GlobalTheory.BlockType.kOne_le_blockGrp _ _) hU h1U
    (fun g hg _ => hθU g hg) _ hFS (_root_.GlobalTheory.T.completion_iso_split_place_alt hL D P S hT i PI k v s hw hs c hc hcs F hF) _ xs (fun h => z.coeff h)
    (fun h => (hxs h).1) hne''
  refine ⟨y, GlobalTheory.BlockType.isBlockVec_of _ _ _ hy, fun h => Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV (xs h)), fun h => (hxs h).2.1, ?_⟩
  rw [Finsupp.sum_fintype _ _ (by simp)]
  exact hyz
end GlobalTheory.DzVecLoc
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DzVecLoc
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), GlobalTheory.HeightCounting.Up.CenLoc D P.M → ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) ρ f, InSeries D k ρ f → PairedCharacterCondition.RT.Occurs i PI k v (idemOf D k ρ) → ∃ x, IsBlockVec (S i _ hw).mu ((S i _ hw).rep PI).π x ∧ NotKilled ((S i _ hw).rep PI).π (idemOf D k ρ) x := by
  intro _ hL D P hC S hT i PI k v hw ρ f hser hocc
  obtain ⟨s, hs⟩ := GlobalTheory.TypeBlockPf.splitAt D _ hw
  have key : ∀ (w : PlE D.host) (hw' : IsSplitPl D.host w), w = D.naut.plGw k v → ∃ x, IsBlockVec (S i w hw').mu ((S i w hw').rep PI).π x ∧ NotKilled ((S i w hw').rep PI).π (idemOf D k ρ) x := by
    intro w hw' hwv
    have e : w = s.w := hwv.trans hs.symm
    subst e
    exact _root_.GlobalTheory.DzVecLoc.vector_at_split_place hL D P hC S hT i PI k v s hw' hs ρ hser.1 hocc
  exact key _ hw rfl
end GlobalTheory.DzVecLoc
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blockVec_notKilled_of_occurs : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), GlobalTheory.HeightCounting.Up.CenLoc D P.M → ∀ S : Reading P.T, _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) ρ f, InSeries D k ρ f → PairedCharacterCondition.RT.Occurs i PI k v (idemOf D k ρ) → ∃ x, IsBlockVec (S i _ hw).mu ((S i _ hw).rep PI).π x ∧ NotKilled ((S i _ hw).rep PI).π (idemOf D k ρ) x := by
  first | exact @_root_.GlobalTheory.DzVecLoc.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.DzVecLoc.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.DzVecLoc.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroRow
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → GlobalTheory.HeightCounting.Up.CenLoc D P.M → GreenLab P.ty.grp → ChiTOk D P.cf → PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) := by
  intro hP hL D P hRow hLab hCen hGreen hChi
  obtain ⟨S, hS, -, -⟩ := _root_.GlobalTheory.T.exists_true_reading_with_laws_suppLaws hP.fin hL D P hRow
  have hLoc : _root_.GlobalTheory.PendOf.LocalDatumCondition hL D := _root_.GlobalTheory.DepthZeroAssembly.locDZ_of_split_reg_m_alt hL D
    (_root_.GlobalTheory.T.splitLoc_of_greenLab_depth_zero hP hL D P.ty.grp hGreen) (_root_.UpperTheory.Lit.Dz.blockTypeSplitProp hP hL D P.ty.grp hGreen)
  have hConj : ConjDual D := _root_.GlobalTheory.T.conjDual_of_labAll hP hL D P hLab
  intro i k v PI
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  intro ρ f hρ hser hocc hsq hu
  have hw : IsSplitPl D.host (D.naut.plGw k v) := GlobalTheory.T.isSplitPlace_of_over_type_prime D k _ (D.naut.plGw_over k v)
  obtain ⟨x, hx⟩ := _root_.GlobalTheory.T.exists_blockVec_notKilled_of_occurs hP hL D P hCen S hS i PI k v hw ρ f ⟨hρ, hser⟩ hocc
  obtain ⟨htame, hχ, u, hu', hlabχ⟩ := _root_.GlobalTheory.T.nonGalois_tame_label_mu_alt hP hL D P hChi S hS i k v hw
  obtain ⟨hmono, hlab⟩ := hLoc k v (S i _ hw).mu hχ (u : ZMod (D.host.g k)) ((S i _ hw).rep PI) ρ f htame hlabχ
    ⟨hρ, hser⟩ hsq (hu u hu') ⟨x, hx⟩
  have hrc : _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) _ ((S i _ hw).rep PI) = P.T.e _ (D.naut.locV i PI (D.naut.plGw k v)) := by
    rw [← hS.rc i _ hw]
    exact ((S i _ hw).locV PI).symm
  have hm0 : D.naut.mono0 (D.naut.locV i PI (D.naut.plGw k v)) := by
    rw [hrc] at hmono
    exact (P.T.mono0 _ _).2 hmono
  have hl : D.naut.items₂ k (D.naut.plGw k v) (D.naut.locV i PI (D.naut.plGw k v)) =
      f * (X - C (u : ZMod (D.host.g k))) ^ D.R.t := by
    rw [P.lab k v, ← hlab]
    unfold _root_.GlobalTheory.PendOf.localLabelPolynomial
    rw [hrc]
  have hf0 : D.ntypes.eSer k f ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hser
    exact GlobalTheory.SerOSys.ZSum.zIdem_ne_zero ρ hρ hser.symm
  have hdegf : f.natDegree = D.R.r := by
    by_contra hne
    exact hf0 (D.ntypes.eSer_zero k f fun h => hne h.2.1)
  have hfne : f ≠ 0 := by
    intro h; apply hf0; exact D.ntypes.eSer_zero k f fun h' => by rw [h] at h'; exact (h'.1.ne_zero rfl)
  have hdeg : (f * (X - C (u : ZMod (D.host.g k))) ^ D.R.t).natDegree = D.R.nV := by
    rw [natDegree_mul hfne (pow_ne_zero _ (X_sub_C_ne_zero _)), natDegree_pow, natDegree_X_sub_C, hdegf, mul_one]
    rfl
  refine ⟨u, hu', hm0, hl, fun w' hc => ?_⟩
  obtain ⟨hc1, -, hc3⟩ := hConj i PI k v w' hc
  have hroots : Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w' (D.naut.locV i PI w')) =
      (Formalism.CyclotomicNorms.rootsBar (f * (X - C (u : ZMod (D.host.g k))) ^ D.R.t)).map (·⁻¹) := by
    rw [hc3, hl]
  refine ⟨hc1 hm0, ?_, hroots⟩
  rw [← card_rootsBar, hroots, Multiset.card_map, card_rootsBar, hdeg]
end GlobalTheory.DepthZeroRow
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admDepthZero_of_rowMod_labAll_greenLab : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → GlobalTheory.HeightCounting.Up.CenLoc D P.M → GreenLab P.ty.grp → ChiTOk D P.cf → PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) := by
  first | exact @_root_.GlobalTheory.DepthZeroRow.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.DepthZeroRow.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.DepthZeroRow.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NonGaloisDepthZeroTame
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DepthZeroTameAltAlt
set_option synthInstance.maxHeartbeats 200000

section
section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroTame
theorem depthZero_tame_alt : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists)
    (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → ChiTOk D P.cf →
    DepthZ D := by
  intro hP hS hL D P hrow hlab hchi
  obtain ⟨S, hT, hLaws, -⟩ := _root_.GlobalTheory.T.exists_true_reading_with_laws_suppLaws hP.fin hL D P hrow
  have hfix : ∀ (i : D.nd.Loc) (PI : D.naut.AV i) (k : Fin 2) (v : D.nd.PlG k),
      TameLP D (D.naut.locV i PI (D.naut.plGw k v)) := by
    intro i PI k v
    have hw := GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v
    have htame := _root_.GlobalTheory.PendOf.isTame_reading_mu_at_split_plGw hL D P S hT i k v hw
    have hTB := _root_.GlobalTheory.T.type_block_of_tame_at_split_place hL D P S hT i _ hw ⟨k, D.naut.plGw_over k v⟩ htame
    obtain ⟨x, hx0, hx⟩ := hTB.2 PI
    have hfixd : x ∈ GlobalTheory.PRep.fixed ((S i _ hw).rep PI).π
        (GlobalTheory.SplitWeil.KOne ((D.naut.plGw k v).adicCompletion D.host.E) (Fin (D.R.r + D.R.t))) := by
      intro h
      have h' : ((S i _ hw).rep PI).π h x = x := GlobalTheory.JacBlock.KOne_le_stab htame hx h.2
      simpa using h'
    have hwild := _root_.GlobalTheory.DepthZeroLoc.main_m_alt hP.bz hS hL D _ _ ((S i _ hw).rep PI) ⟨x, hfixd, hx0⟩
      (UpperTheory.One.M.isQg_of_over D k _ (D.naut.plGw_over k v))
    intro σ hσI hσW
    have hd : D.naut.lpDim (D.naut.locV i PI (D.naut.plGw k v)) = D.R.r + D.R.t := by
      rw [← P.T.dim, (S i _ hw).locV PI, (hLaws i _ hw).dim]
    rw [P.T.inePol _ _ σ hσI, (S i _ hw).locV PI, hT.rc i _ hw, hwild σ hσW, hd]
  intro i PI k w hw
  obtain ⟨v, rfl | hc⟩ := GlobalTheory.TypePlaceCover.place_cover D k w hw
  · exact hfix i PI k v
  · exact ((_root_.GlobalTheory.T.conjDual_of_labAll hP hL D P hlab) i PI k v w hc).2.1 (hfix i PI k v)
end GlobalTheory.DepthZeroTame
end
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.DepthZeroTame
end GlobalTheory.DepthZeroTame
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthZ_of_rowMod_labAll_chiTOk : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → GlobalTheory.Published.DepthZeroSupport → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → ChiTOk D P.cf → DepthZ D := by
  first | exact @_root_.GlobalTheory.DepthZeroTame.depthZero_tame_alt | exact _root_.GlobalTheory.DepthZeroTame.depthZero_tame_alt | (intros; apply _root_.GlobalTheory.DepthZeroTame.depthZero_tame_alt <;> assumption)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.PinClose
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → GlobalTheory.Published.DepthZeroSupport →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) →
    LabAll D P.T → GlobalTheory.HeightCounting.Up.CenLoc D P.M → GreenLab P.ty.grp → ChiTOk D P.cf → SumRepresentations.tie0 D → SumRepresentations.adm5 D →
    ZLStable D → CenInt D → SerLL D → CoeffRingsHaveRootsOfUnity D → ∃ Q : PairedCharacterCondition.Pend D, PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q := by
  intro hPr hSu hL D P hRow hLab hCen hGr hChi ht0 ha5 hZL hCI hSer hZ
  obtain ⟨hIne, hDep, hGen⟩ := GlobalTheory.LabTies.main D P.T hLab
  have hCT : OnMtPreservesTypeV D := GlobalTheory.T.groupAlgebraCentre_keeps_typeSpaces_at_localisations D P.M P.H.av hCen
  have hDZ : DepthZ D := _root_.GlobalTheory.T.depthZ_of_rowMod_labAll_chiTOk hPr hSu hL D P hRow hLab hChi
  have hAdm : PairedCharacterCondition.RT.AdmDepthZeroTypes (D := D) := _root_.GlobalTheory.T.admDepthZero_of_rowMod_labAll_greenLab hPr hL D P hRow hLab hCen hGr hChi
  have hPar : ∀ S : Formalism.L2.ParC D, ∃ σ' : D.ntypes.Par,
      ∀ w, D.ntypes.locPar σ' w = isoLoc D.nd D.naut S.1 w := by
    intro S
    refine ⟨P.ty.par.eP.symm ⟨S.1, S.2⟩, fun w => ?_⟩
    rw [P.ty.par.locPar_def]
    have e := P.ty.par.eP.apply_symm_apply (⟨S.1, S.2⟩ : HeightCounting.ParC D)
    rw [e]
  exact GlobalTheory.T.exists_pending_objects_depthZero_admissible_eigenSpan D P.M P.H.hecke P.H.rational P.H.av hPar ht0 ha5 hIne hDep hGen hZL hCI hCT hSer hZ hDZ hAdm
end GlobalTheory.PinClose
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LiftSplitsLocally
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsAdmissibleCharacterTrivialAbove
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MainAltAltAltFurther
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterTrivialAbovePlaceAdmissible
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ChiOneAbove
theorem character_trivial_above_place_admissible_alt (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) :
    Formalism.MainNotions.SumRepresentations.adm5 D := by
  have hrig : IsobaricRigid D.nd D.naut := _root_.GlobalTheory.NPin.isobaricRigid_of_pin_alt hPr.fin hPr.js hL D P
  have han1 := GlobalTheory.RowClose.isobaricCuspidalMultiplicityOne_of_twisted _ _ _ D.nd D.naut hrig
  have han2 := GlobalTheory.SpehRigid.isobaricDiscreteSelfDualMultOne_of_isobaricSumMultOne _ _ _ D.nd D.naut hrig
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hPr.cheb D
  exact (Formalism.MainNotions.SumRepresentations.condition_iff_additive_maps D).2 ⟨han1, han2, fun Sg hSg => by
    have hd := (hcheb hSg.toFinset).closure_eq
    convert hd using 4 with σ
    simp [Set.Finite.mem_toFinset]⟩
end GlobalTheory.ChiOneAbove
end
section
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ChiOneAbove
theorem main_alt_alt_alt : ∀ (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc)
    (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
    Br.IsdRW D.loc D.nbr i w hw (PairedCharacterCondition.chiGL (D := D) i) ∧
    D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (PairedCharacterCondition.chiGL (D := D) i)) w =
      D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w)
        (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) := by
  intro hPr hL D P i w hw
  have hB : GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.BlockCharParam D := GlobalTheory.BlockCharInf.main D P.cf P.C P.tp P.chr
  have h2 : _root_.Formalism.MainNotions.SumRepresentations.adm2_alt D := _root_.UpperTheory.GalS.galClose_alt hPr hL D P
  have h5 := _root_.GlobalTheory.ChiOneAbove.character_trivial_above_place_admissible_alt hPr hL D P
  obtain ⟨ρ, hρc, haway, habove⟩ :=
    (_root_.UpperTheory.GalS.weak' h2 i).2.2 (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (GlobalTheory.ChiOneNoPt.sOne D)
      (GlobalTheory.ChiOneNoPt.integral D hB i)
  have hρ := GlobalTheory.ChiOneNoPt.eq_chi D h5 i w hw ρ hρc haway
  obtain ⟨hdR, hwd, -⟩ := habove w hw
  subst hρ
  refine ⟨((D.loc_tie i w hw).2.1 1 _ (GlobalTheory.JumpDictionaryFoundation.continuous_chiGL D i 1)).2.1.1 hdR, hwd⟩
end GlobalTheory.ChiOneAbove
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.ChiOneAbove
end GlobalTheory.ChiOneAbove
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isdRW_chiGL_at_places_over_l : ∀ (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), Br.IsdRW D.loc D.nbr i w hw (PairedCharacterCondition.chiGL (D := D) i) ∧ D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (PairedCharacterCondition.chiGL (D := D) i)) w = D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w) (((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) := by
  first | exact @_root_.GlobalTheory.ChiOneAbove.main_alt_alt_alt | exact _root_.GlobalTheory.ChiOneAbove.main_alt_alt_alt | (intros; apply _root_.GlobalTheory.ChiOneAbove.main_alt_alt_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlaceLabelOfConjugatePlace
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ConjugatePlacesCompletion
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MArtinTr
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL
theorem GlobalTheory.LocLanglands.artin_transport_m_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A A' : ValuationSubring Ω} {w w' : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (h' : IsPlaceOver A' w') (c : Ω ≃+* Ω) (j : E →+* E) (i : w.adicCompletion E ≃+* w'.adicCompletion E), (∀ z, c z ∈ A' ↔ z ∈ A) → (∀ x, c (algebraMap E Ω x) = algebraMap E Ω (j x)) → Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E _ (j x)) → ∀ {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}, _root_.UpperTheory.One.M.LawsM a ha ε (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h) → ∀ {a' : Weil h' →* (w'.adicCompletion E)ˣ} {ha' : IsLocalArtin h' a'} {ε' : EpsFamily A'}, _root_.UpperTheory.One.M.LawsM a' ha' ε' (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h') → ∀ (ξ : (w'.adicCompletion E)ˣ →* ℂˣ), IsSmoothChar ξ → ∀ (σ : Weil h) (σ' : Weil h'), (∀ z, c ((σ : G E Ω) z) = (σ' : G E Ω) (c z)) → ξ (Units.map i.toRingHom.toMonoidHom (a σ)) = ξ (a' σ') := by
  intro hL E Ω _ _ _ _ _ A A' w w' h h' c j i hcA hcj hi hij a ha ε H a' ha' ε' H' ξ hξ σ σ' hσ
  set iU : (w.adicCompletion E)ˣ →* (w'.adicCompletion E)ˣ := Units.map i.toRingHom.toMonoidHom with hiU
  have hcont : Continuous iU := Units.continuous_map hi
  have hs : IsSmoothChar (ξ.comp iU) := hξ.comp iU hcont
  obtain ⟨b, b', hb, hb', -, hρ⟩ := _root_.UpperTheory.One.M.New.field hL
    (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h) (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL h') c j i hcA hcj hi hij 1
    (IrrRep.det (Fin 1) (ξ.comp iU) hs) (IrrRep.det (Fin 1) ξ hξ) (LinearEquiv.refl ℂ ℂ) (by
      intro g v
      have hd : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom g) =
          iU (Matrix.GeneralLinearGroup.det g) := by
        ext
        simp [hiU, RingHom.map_det]
      show (LinearEquiv.refl ℂ ℂ) ((ξ.comp iU (Matrix.GeneralLinearGroup.det g) : ℂ) • v) = _
      show _ = ((ξ (Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map i.toRingHom g)) : ℂ) • v)
      rw [hd]
      rfl) (UpperTheory.One.M.good_ofChar _ hs)
  have e1 : WD.mk b = WD.lpOfChar h ((ξ.comp iU).comp a) (ha.smooth hs) := hb.trans (H.one _ hs)
  have e2 : WD.mk b' = WD.lpOfChar h' (ξ.comp a') (ha'.smooth hξ) := hb'.trans (H'.one _ hξ)
  have k := congrFun (congrArg (fun f : Module.End ℂ (Fin 1 → ℂ) => f (fun _ => 1)) (hρ σ σ' hσ)) 0
  simp only [b.rho_apply_of_mk_eq_lpOfChar _ _ e1, b'.rho_apply_of_mk_eq_lpOfChar _ _ e2] at k
  simp at k
  exact Units.ext (by simpa [hiU] using k)
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_places_completion_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A A' : ValuationSubring Ω} {w w' : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (h' : IsPlaceOver A' w') (c : Ω ≃+* Ω) (j : E →+* E) (i : w.adicCompletion E ≃+* w'.adicCompletion E), (∀ z, c z ∈ A' ↔ z ∈ A) → (∀ x, c (algebraMap E Ω x) = algebraMap E Ω (j x)) → Continuous i → (∀ x, i (algebraMap E _ x) = algebraMap E _ (j x)) → ∀ {a : Weil h →* (w.adicCompletion E)ˣ} {ha : IsLocalArtin h a} {ε : EpsFamily A}, _root_.UpperTheory.One.M.LawsM a ha ε (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h) → ∀ {a' : Weil h' →* (w'.adicCompletion E)ˣ} {ha' : IsLocalArtin h' a'} {ε' : EpsFamily A'}, _root_.UpperTheory.One.M.LawsM a' ha' ε' (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL h') → ∀ (ξ : (w'.adicCompletion E)ˣ →* ℂˣ), IsSmoothChar ξ → ∀ (σ : Weil h) (σ' : Weil h'), (∀ z, c ((σ : G E Ω) z) = (σ' : G E Ω) (c z)) → ξ (Units.map i.toRingHom.toMonoidHom (a σ)) = ξ (a' σ') := by
  first | exact @_root_.GlobalTheory.LocLanglands.artin_transport_m_alt | exact _root_.GlobalTheory.LocLanglands.artin_transport_m_alt | (intros; apply _root_.GlobalTheory.LocLanglands.artin_transport_m_alt <;> assumption)
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LabConjPlace
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL
end GlobalTheory.LabConjPlace
open GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.LabConjPlace in
theorem GlobalTheory.LabConjPlace.locComp_of_isRc_classMapD_cenLoc : ∀ (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), LabAll D P.T → ∀ (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (u : (ZMod (D.host.g k))ˣ), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) = X - C (u : ZMod (D.host.g k)) → ∀ (w' : PlE D.host), IsConjPl D.host (D.naut.plGw k v) w' → ∀ s : ℝ, D.naut.items₂ k w' (D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w') s) = X - C ((u⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)) := by
  intro hPr hL D P hLab S hS i k v hw hχ u _ hlab w' hc s
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨γ, hγ1, hγ2, hγ3⟩ := hLab
  have hw'over : w' ∈ placesOver D.host.E (D.host.g k) := by
    have h0 := D.naut.plGw_over k v
    simp only [placesOver, Set.mem_setOf_eq] at h0 ⊢
    exact (hc _ _ (by simp)).1 h0
  rw [hγ3 k w' hw'over, P.T.tw, WD.lab_lpTw]
  obtain ⟨jj, hjj⟩ : ∃ jj : Fin D.R.m, jj.1 + 1 = D.nd.j i :=
    ⟨⟨D.nd.j i - 1, by have := D.nd.j_range i; omega⟩, by have := D.nd.j_range i; simp; omega⟩
  set χ := D.naut.tw (D.naut.muC i) D.naut.etaTinv with hχdef
  set μH := P.tp.tup (D.nd.mu i) jj with hμH
  have e1 : (P.chr.e1 χ).1 = μH * P.cf.eta⁻¹ := by
    rw [hχdef, P.chr.tw, P.chr.muC i jj hjj, P.chr.etaTinv]
  have hcomp' : IsComp (P.chr.e1 χ).1 w' ((P.chr.e1 χ).1.loc w') := ⟨ParLaws.isSmoothChar_loc _ w', fun x => rfl⟩
  rw [_root_.GlobalTheory.T.T_e_locG_eq_rcAt_ofDet hPr.fin hL D P χ w' _ hcomp']
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w')); obtain ⟨a', ha', ε', H'⟩ := hOpn) | obtain ⟨a', ha', ε', -, H'⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 w')
  change WD.lab _ _ (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w') (GlobalTheory.LocGL.IrrGL.ofChar ((P.chr.e1 χ).1.loc w') hcomp'.1)) = _
  rw [H'.one]
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨a, ha, ε, Hw⟩ := hOpn) | obtain ⟨a, ha, ε, -, Hw⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
  have hlab' : WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v)
      (WD.lpOfChar (D.nd.plOm.2 (D.naut.plGw k v)) ((S i _ hw).mu.comp a) (ha.smooth hχ)) = X - C (u : ZMod (D.host.g k)) := by
    rw [← Hw.one _ hχ]; exact hlab
  have HS : TeichmullerInertiaLabelCondition (D.nd.plOm.1 (D.naut.plGw k v)) (D.naut.plGw k v) (D.ntypes.teichC k) (D.ntypes.tg k v) := by
    by_contra hn
    rw [WD.lab_of_not hn] at hlab'
    have := congrArg natDegree hlab'
    rw [natDegree_one, natDegree_X_sub_C] at this
    exact absurd this (by norm_num)
  have hdeg : (WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v)
      (WD.lpOfChar (D.nd.plOm.2 (D.naut.plGw k v)) ((S i _ hw).mu.comp a) (ha.smooth hχ))).natDegree =
      WD.lpDim (WD.lpOfChar (D.nd.plOm.2 (D.naut.plGw k v)) ((S i _ hw).mu.comp a) (ha.smooth hχ)) := by
    rw [hlab', natDegree_X_sub_C]; simp [WD.lpOfChar]
  have htame := WD.tame_of_natDegree_lab hdeg
  rw [WD.lpOfChar] at htame
  have hwild : ∀ σ : Weil (D.nd.plOm.2 (D.naut.plGw k v)), (σ : G _ _) ∈ Wild D.host.E (D.nd.plOm.1 (D.naut.plGw k v)) →
      ((S i _ hw).mu.comp a) σ = 1 := by
    intro σ hσ
    have := congrFun (LinearMap.congr_fun ((WD.tame_mk _).mp htame σ hσ) fun _ => 1) 0
    exact Units.ext (by simpa using this)
  have hval := (WD.lab_lpOfChar_eq_iff HS (ha.smooth hχ) hwild u).mp hlab'
  have hμw : μH.loc (D.naut.plGw k v) = (S i _ hw).mu := by
    obtain ⟨ξ₀, -, huniq, -⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E μH (D.naut.plGw k v)
    exact (huniq _ ⟨ParLaws.isSmoothChar_loc _ _, fun x => rfl⟩).trans (huniq _ (hS.mu i _ hw jj hjj)).symm
  obtain ⟨c, hcE, hcA, hcγ⟩ := hγ2 k v w' hc
  set τc : D.host.E ≃+* D.host.E := (D.host.conj : D.host.E ≃+* D.host.E) with hτc
  have hcE' : ∀ x, c (algebraMap D.host.E D.nd.Om x) = algebraMap D.host.E D.nd.Om (τc x) := hcE
  have hγ' : γ k w' = GlobalTheory.ConjTransport.conjG c τc hcE' (D.ntypes.tg k v) := by
    ext y
    rw [GlobalTheory.ConjTransport.conjG_apply]
    have := hcγ (c.symm y)
    rw [RingEquiv.apply_symm_apply] at this
    exact this
  have hIne' : γ k w' ∈ Ine (F := D.host.E) (D.nd.plOm.1 w') := by
    rw [hγ']; exact GlobalTheory.ConjTransport.conjG_mem_Ine c τc hcE' hcA HS.2.1
  have HS' : TeichmullerInertiaLabelCondition (D.nd.plOm.1 w') w' (D.ntypes.teichC k) (γ k w') :=
    ⟨GlobalTheory.TameLabels.normV_eq_of_split (D.host.g_prime k) (D.nd.g_split k) hw'over, hIne', HS.2.2⟩
  have hcsd : IsCSD D.host μH := by
    rw [hμH, ← P.chr.muC i jj hjj]; exact (P.chr.csd _).1 (D.naut.muC_csd i)
  obtain ⟨ic, hic, hicE, hicμ⟩ := GlobalTheory.T.conjSelfDual_heckeChar_conjugatePlace_component_inv D.host μH hcsd _ w' hc
  have htr : ∀ (σ : Weil (D.nd.plOm.2 (D.naut.plGw k v))) (σ' : Weil (D.nd.plOm.2 w')),
      (∀ z, c ((σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) z) = (σ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) (c z)) →
      μH.loc w' (a' σ') = ((S i _ hw).mu (a σ))⁻¹ := by
    intro σ σ' hσ
    rw [← _root_.GlobalTheory.T.conjugate_places_completion_alt hL (D.nd.plOm.2 (D.naut.plGw k v)) (D.nd.plOm.2 w') c τc.toRingHom ic
      (fun z => (hcA z).symm) hcE' hic hicE Hw H' (μH.loc w') (ParLaws.isSmoothChar_loc _ _) σ σ' hσ, hicμ, hμw]
  have heta : ∀ σ' : Weil (D.nd.plOm.2 w'), (σ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w') →
      P.cf.eta.loc w' (a' σ') = 1 := fun σ' hσ' => loc_artin_ine ha' _ (P.cf.isEta.unr w') σ' hσ'
  have hξ : ∀ σ', ((P.chr.e1 χ).1.loc w') (a' σ') = μH.loc w' (a' σ') * (P.cf.eta.loc w' (a' σ'))⁻¹ := by
    intro σ'; rw [e1]; rfl
  have hwild' : ∀ σ' : Weil (D.nd.plOm.2 w'), (σ' : G _ _) ∈ Wild D.host.E (D.nd.plOm.1 w') →
      (((P.chr.e1 χ).1.loc w').comp a') σ' = 1 := by
    intro σ' hσ'
    have hA' : ∀ y, y ∈ D.nd.plOm.1 w' ↔ c.symm y ∈ D.nd.plOm.1 (D.naut.plGw k v) := fun y => by
      rw [hcA, RingEquiv.apply_symm_apply]
    have hσw : GlobalTheory.ConjTransport.conjG c.symm τc.symm (GlobalTheory.ConjTransport.symm_alg c τc hcE') (σ' : G _ _) ∈
        Wild D.host.E (D.nd.plOm.1 (D.naut.plGw k v)) :=
      GlobalTheory.ConjTransport.conjG_mem_wild c.symm τc.symm _ hA' hσ'
    let σ : Weil (D.nd.plOm.2 (D.naut.plGw k v)) := ⟨_, Ine_le_Weil _ (Wild_le_Ine hσw)⟩
    have h1 := htr σ σ' (fun z => by
      show c (GlobalTheory.ConjTransport.conjG c.symm τc.symm _ (σ' : G _ _) z) = _
      rw [GlobalTheory.ConjTransport.conjG_apply, RingEquiv.symm_symm, RingEquiv.apply_symm_apply])
    have h2 := hwild σ hσw
    rw [MonoidHom.comp_apply] at h2
    rw [MonoidHom.comp_apply, hξ, h1, heta σ' (Wild_le_Ine hσ'), h2]
    simp
  rw [WD.lab_lpOfChar_eq_iff HS' _ hwild']
  rw [MonoidHom.comp_apply, hξ, htr ⟨D.ntypes.tg k v, Ine_le_Weil _ HS.2.1⟩ _ (fun z => (hcγ z).symm),
    heta _ hIne', inv_one, mul_one]
  have hx : algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k)) (u : ZMod (D.host.g k)) ≠ 0 :=
    (_root_.map_ne_zero _).2 u.ne_zero
  rw [MonoidHom.comp_apply] at hval
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, ← hval, map_inv₀]
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, inv_mul_cancel₀ hx, map_one]
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeLabel_of_conjugate_place_alt : ∀ (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), LabAll D P.T → ∀ (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (u : (ZMod (D.host.g k))ˣ), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu → _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) = X - C (u : ZMod (D.host.g k)) → ∀ (w' : PlE D.host), IsConjPl D.host (D.naut.plGw k v) w' → ∀ s : ℝ, D.naut.items₂ k w' (D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) w') s) = X - C ((u⁻¹ : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)) := by
  first | exact @_root_.GlobalTheory.LabConjPlace.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.LabConjPlace.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.LabConjPlace.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PlaceLabelFixedByConjugation
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MLabUnr
set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LabFixed
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL
theorem lab_rcAt_ofDet_mul_eq (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (k : Fin 2) (v : D.nd.PlG k)
    (ξ η : (HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v))ˣ →* ℂˣ) (hξ : IsSmoothChar ξ)
    (hη : IsSmoothChar η) (hu : ∀ x, Formalism.L2.Host.IsUnitAt (D.naut.plGw k v) x → η x = 1) (hξη : IsSmoothChar (ξ * η)) :
    WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 (ξ * η) hξη)) =
      WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 ξ hξ)) := by
  unfold _root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep
  first | (have hOpn := UpperTheory.One.M.opn _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))); obtain ⟨a, ha, ε, H⟩ := hOpn) | obtain ⟨a, ha, ε, -, H⟩ := _root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (D.nd.plOm.2 (D.naut.plGw k v))
  have e1 : LocLanglands.cls (Irr.ofDet 1 (ξ * η) hξη).toIrrRep = (GlobalTheory.LocGL.IrrGL.ofChar ξ hξ).tw η hη := by
    rw [GlobalTheory.LocGL.IrrGL.tw_ofChar]; rfl
  have e2 : LocLanglands.cls (Irr.ofDet 1 ξ hξ).toIrrRep = GlobalTheory.LocGL.IrrGL.ofChar ξ hξ := rfl
  rw [e1, e2, _root_.UpperTheory.One.M.LawsM.twist H _ _ _ (UpperTheory.One.M.good_ofChar ξ hξ), H.one η hη, lpChar_lpOfChar, WD.lab_lpTwist]
  intro σ
  have hd := ha.ord_eq (ineIncl _ σ)
  rw [deg_ineIncl, neg_zero] at hd
  apply hu
  have h0 : Valued.v ((a ((ineIncl _) σ) : (HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v))ˣ) :
      HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v)) ≠ 0 := by simp
  rw [GlobalTheory.SmGL.SphCompletion.ord_completion, neg_eq_zero] at hd
  unfold Formalism.L2.Host.IsUnitAt
  rw [← WithZero.exp_log h0, hd, WithZero.exp_zero]
end GlobalTheory.LabFixed
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.LabFixed
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL
theorem labLP_twist_eq_labAt_ofDet : ∀ (hPr : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)) (hχ : GlobalTheory.SmGL.IsSmoothChar (S i _ hw).mu) (s : ℝ), D.naut.items₂ k (D.naut.plGw k v) (D.naut.lpTw (D.naut.locG (D.naut.tw (D.naut.muC i) D.naut.etaTinv) (D.naut.plGw k v)) s) = _root_.GlobalTheory.PendOf.localLabelPolynomial hL D k v (Irr.ofDet 1 (S i _ hw).mu hχ) := by
  intro hPr hL D P S hT i k v hw hχ s
  haveI := host_isCMField D.host
  obtain ⟨j, hj⟩ : ∃ j : Fin D.R.m, (j : ℕ) + 1 = D.nd.j i := by
    have := D.nd.j_range i
    exact ⟨⟨D.nd.j i - 1, by omega⟩, by simp only; omega⟩
  have hμ : IsComp (P.tp.tup (D.nd.mu i) j) (D.naut.plGw k v) (S i _ hw).mu := hT.mu i _ hw j hj
  have hψ : (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 = P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹ := by
    rw [P.chr.tw, P.chr.muC i j hj, P.chr.etaTinv]
  have hc : IsComp (P.chr.e1 (D.naut.tw (D.naut.muC i) D.naut.etaTinv)).1 (D.naut.plGw k v)
      ((P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹).loc (D.naut.plGw k v)) := by
    rw [hψ]; exact ⟨ParLaws.isSmoothChar_loc _ _, fun x => rfl⟩
  rw [P.lab k v, P.T.tw, WD.lab_lpTw, _root_.GlobalTheory.RankOneComp.e_locG_eq_rcAt_ofDet_of_isComp hPr.fin hL D P _ _ _ hc, _root_.GlobalTheory.PendOf.localLabelPolynomial]
  have hηs : IsSmoothChar (P.cf.eta.loc (D.naut.plGw k v))⁻¹ := by
    have := ParLaws.isSmoothChar_loc (P.cf.eta⁻¹) (D.naut.plGw k v)
    convert this using 1
    exact MonoidHom.ext fun x => rfl
  have hu : ∀ x, Formalism.L2.Host.IsUnitAt (D.naut.plGw k v) x → (P.cf.eta.loc (D.naut.plGw k v))⁻¹ x = 1 := by
    intro x hx
    rw [MonoidHom.inv_apply, P.cf.isEta.unr _ x hx, inv_one]
  have e : (P.tp.tup (D.nd.mu i) j * P.cf.eta⁻¹).loc (D.naut.plGw k v) =
      (S i _ hw).mu * (P.cf.eta.loc (D.naut.plGw k v))⁻¹ := by
    rw [GlobalTheory.Published.ParamAboveModel.eq_loc hμ]
    rfl
  have key : ∀ (ξ' : (HeightOneSpectrum.adicCompletion D.host.E (D.naut.plGw k v))ˣ →* ℂˣ) (h' : IsSmoothChar ξ'),
      ξ' = (S i _ hw).mu * (P.cf.eta.loc (D.naut.plGw k v))⁻¹ →
      WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 ξ' h')) =
        WD.lab (D.ntypes.teichC k) (D.ntypes.tg k v) (_root_.GlobalTheory.NPin.weilDeligneOfLocalIrrep hL D (D.naut.plGw k v) 1 (Irr.ofDet 1 (S i _ hw).mu hχ)) := by
    rintro _ h' rfl
    exact _root_.GlobalTheory.LabFixed.lab_rcAt_ofDet_mul_eq hL D k v _ _ hχ hηs hu h'
  exact key _ _ e
end GlobalTheory.LabFixed
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.TieChiPin
theorem locComp_of_isRc_classMapD_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), (∀ i : D.nd.Loc, Nonempty (RowMod D P.rep (D.nd.j i))) → LabAll D P.T → ChiTOk D P.cf → PairedCharacterCondition.tieChi (D := D) := by
  intro hPr hL D P hRow hLab hChi i k hl v
  obtain ⟨S, hS, -, -⟩ := _root_.GlobalTheory.T.exists_true_reading_with_laws_suppLaws hPr.fin hL D P hRow
  have hsp : IsSplitPl D.host (D.naut.plGw k v) := GlobalTheory.T.isSplitPlace_of_over_type_prime D k _ (D.naut.plGw_over k v)
  obtain ⟨htame, hχ, u, hu, hlab⟩ := _root_.GlobalTheory.T.nonGalois_tame_label_mu_alt hPr hL D P hChi S hS i k v hsp
  refine ⟨u, hu, fun w hw => ⟨fun hw0 => ?_, fun hc => ?_⟩⟩
  · obtain ⟨hdR, hwd⟩ := _root_.GlobalTheory.T.isdRW_chiGL_at_places_over_l hPr hL D P i w hw
    refine ⟨hdR, ?_⟩
    rw [hwd, hw0]
    rw [_root_.GlobalTheory.LabFixed.labLP_twist_eq_labAt_ofDet hPr hL D P S hS i k v hsp hχ, hlab]
  · obtain ⟨hdR, hwd⟩ := _root_.GlobalTheory.T.isdRW_chiGL_at_places_over_l hPr hL D P i w hw
    refine ⟨hdR, ?_⟩
    rw [hwd]
    exact _root_.GlobalTheory.T.placeLabel_of_conjugate_place_alt hPr hL D P hLab S hS i k v hsp hχ u htame hlab w hc _
end GlobalTheory.TieChiPin
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AtMemAnd
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.HeightCounting.Up.PendLayer
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem atMem_mono {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p)
    (hpq : ∀ K B f T w Z Wt p0 t nch n c, p K B f T w Z Wt p0 t nch n c → q K B f T w Z Wt p0 t nch n c) : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun B f T _ H kp w Z Wt p0 t nch n xd c a b d =>
    hpq _ B f T w Z Wt p0 t nch n c (H kp w Z Wt p0 t nch n xd c a b d)
theorem atMem_and' {p q : _root_.GlobalTheory.HeightCounting.Up.LayPAlt hL} (h : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL p) (h' : _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL q) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun K B f T w Z Wt p0 t nch n c => p K B f T w Z Wt p0 t nch n c ∧ q K B f T w Z Wt p0 t nch n c :=
  EvG.imp (EvG.inter h h') fun _ _ _ _ _ hK => large₂.imp (large₂.inter hK.1 hK.2) fun _ _ _ _ H kp w Z Wt p0 t nch n xd c a b d =>
    ⟨H.1 kp w Z Wt p0 t nch n xd c a b d, H.2 kp w Z Wt p0 t nch n xd c a b d⟩
theorem atMem_mono_of_colPin {q : ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), w.Lt → Prop}
    (h : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), q B f T w Z) :
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ B f T w Z _ _ _ _ _ _ => q B f T w Z :=
  EvG.imp h fun _ _ _ _ _ hK => large₂.imp hK fun _ _ T _ H kp w Z _ _ _ _ _ _ _ _ _ _ => H kp T w Z
end GlobalTheory.HeightCounting.Up.PendLayer
end
end
end

set_option synthInstance.maxHeartbeats 200000

section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
noncomputable section
namespace GlobalTheory.HeightCounting.Up.PendLayer
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists}
theorem tieChi_of_labAll_green_chi_cen (hP : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt) (hS : GlobalTheory.Published.DepthZeroSupport) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (hX : GlobalTheory.NJoin.Agree X P.M P.rep) (hJ : JumpsCard D.nd D.naut)
    (hlab : GlobalTheory.PendOf.LabAll D P.T) (hgreen : GlobalTheory.PendOf.GreenLab P.ty.grp) (hchi : ChiTOk D P.cf)
    (hcen : CenLoc D P.M) (hzl : GlobalTheory.PendOf.ZLStable D) (hci : GlobalTheory.PendOf.CenInt D) (hroots : RootsLL D) :
    PairedCharacterCondition.tieChi (D := D) ∧ ∃ Q : PairedCharacterCondition.Pend D, PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q := by
  have hrow : ∀ i : D.nd.Loc, Nonempty (GlobalTheory.NPin.RowMod D P.rep (D.nd.j i)) := by
    intro i
    have h1 := (D.nd.j_range i).1
    have h2 := (D.nd.j_range i).2
    obtain ⟨Y, -⟩ := _root_.GlobalTheory.RowModCanon.main_alt_alt hP.hc hP.decay hL D P X hX ⟨D.nd.j i - 1, by omega⟩ (D.nd.j i) (by simp; omega)
    exact ⟨Y⟩
  have hA := _root_.UpperTheory.GalS.a_close_main hP.what₂ hL D P hJ
  have hZ := GlobalTheory.ZetaSer.rootsOfUnity_and_seriesIdempotent_rational D hroots
  exact ⟨_root_.GlobalTheory.TieChiPin.locComp_of_isRc_classMapD_cenLoc hP.what₂ hL D P hrow hlab hchi,
    _root_.GlobalTheory.PinClose.locComp_of_isRc_classMapD_cenLoc hP.what₂ hS hL D P hrow hlab hcen hgreen hchi hA.tie0 hA.a5 hzl hci (hZ.2 P.ty.grp) hZ.1⟩
theorem locComp_of_isRc_classMapD_cenLoc : HtCard → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → GlobalTheory.Published.DepthZeroSupport → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists,
    _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => PairedCharacterCondition.tieChi (D := w.D Z) ∧ ∃ Q : PairedCharacterCondition.Pend (w.D Z), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q := by
  intro hH hP hS hL
  have h1 := _root_.GlobalTheory.HeightCounting.Up.PendLayer.atMem_and' (_root_.GlobalTheory.T.cenLoc_zlStable_cenInt_at_members hL) (_root_.GlobalTheory.HeightCounting.Up.PendLayer.atMem_and' (_root_.GlobalTheory.HeightCounting.JumpsAt.jumpsCard_at_members_of_htCard hH hL)
    (_root_.GlobalTheory.HeightCounting.Up.PendLayer.atMem_and' (_root_.GlobalTheory.HeightCounting.Up.isTied_of_layer_member_alt hP hL) (_root_.GlobalTheory.HeightCounting.Up.PendLayer.atMem_mono_of_colPin (hL := hL) GlobalTheory.HeightCounting.Up.sizes_host_at_record)))
  refine _root_.GlobalTheory.HeightCounting.Up.PendLayer.atMem_mono h1 fun K B f T w Z Wt p0 t nch n c h => ?_
  obtain ⟨⟨hcen, hzl, hci⟩, hJ, ⟨X, hpin, -⟩, -, -, hroots, -⟩ := h
  have hM : X.P.M = c.a.all.gal.mt := hpin.M_eq
  exact _root_.GlobalTheory.HeightCounting.Up.PendLayer.tieChi_of_labAll_green_chi_cen hP hS (w.D Z) X.P X.X X.agree hJ hpin.lab hpin.green hpin.chiT (hM ▸ hcen) hzl hci hroots
end GlobalTheory.HeightCounting.Up.PendLayer
end
end
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tieChi_at_mem_of_depth_zero_inputs : (HtCard → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → GlobalTheory.Published.DepthZeroSupport → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.Up.MemberAtLayerPoint hL fun _ _ _ _ w Z _ _ t nch n c => PairedCharacterCondition.tieChi (D := w.D Z) ∧ ∃ Q : PairedCharacterCondition.Pend (w.D Z), PairedCharacterCondition.admDZ Q ∧ GlobalTheory.Pass.EigSpan Q) := by
  first | exact @_root_.GlobalTheory.HeightCounting.Up.PendLayer.locComp_of_isRc_classMapD_cenLoc | exact _root_.GlobalTheory.HeightCounting.Up.PendLayer.locComp_of_isRc_classMapD_cenLoc | (intros; apply _root_.GlobalTheory.HeightCounting.Up.PendLayer.locComp_of_isRc_classMapD_cenLoc <;> assumption)
end
end
