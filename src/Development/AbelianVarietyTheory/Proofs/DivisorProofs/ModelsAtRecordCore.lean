module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsogenyOfNcard
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EndoLbIsoSymmetryHypothesisExtendNormalModel
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasis
public import Development.AbelianVarietyTheory.Counterexamples.AbelianLawCounterexamples.HomExtendsOverDVRHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ClozelCohomologicalModel
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelsAtRecordCore
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh


set_option maxHeartbeats 1000000 in
theorem models_at_record_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.toCore.σ₀ → ∀ k : (T.U ((i : ℕ) + 1) σ).Comp, IsMod (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) σ).X k) ∧ IsONFr ((T.U ((i : ℕ) + 1) σ).X k) (fun τ => T.x₀ ((i : ℕ) + 1) σ τ.1) ∧ IsInvOf (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) σ).X k) (fun τ => T.x₀ ((i : ℕ) + 1) σ τ.1) (cart (R.MW i (sg0 D A))) ∧ ((T.U ((i : ℕ) + 1) σ).X k).p0 = (T.Q.Dw ((i : ℕ) + 1)).q ∧ D.R.r = (T.Q.Dw ((i : ℕ) + 1)).p + (T.Q.Dw ((i : ℕ) + 1)).q ∧ (T.Q.Dw ((i : ℕ) + 1)).p ≠ (T.Q.Dw ((i : ℕ) + 1)).q ∧ 1 ≤ D.R.r ∧ (T.Q.H.rt : D.host.E) = D.host.sqrtMinusD ∧ (∀ τ : D.host.E →+* ℂ, τ ∈ ((T.U ((i : ℕ) + 1) σ).X k).Ψ ↔ τ (T.Q.H.rt : D.host.E) = T.Q.H.rt0) ∧ (∀ hq : ((T.U ((i : ℕ) + 1) σ).X k).p0 + (T.Q.Dw ((i : ℕ) + 1)).p = D.R.r, IsBasOf (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) σ).X k) hq (fun τ => T.x₀ ((i : ℕ) + 1) σ τ.1) (onb (R.MW i (sg0 D A)))) ∧ Dom (wtA (κ i)) (Vc D i).rank ∧ (κ i).n = (Vc D i).rank ∧ LastPos (T.Q.Dw ((i : ℕ) + 1)) (wtA (κ i)) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hT i σ hσ k
  subst hσ
  have hj := inR i
  have hL := hT.laws
  have hg := T.toCore.good_σ₀
  have hU := hL.unf _ hj _ hg
  have hP := hL.pins
  have hr1 : 1 ≤ D.R.r := by
    have h2 := D.R.two_le_m
    have h3 := D.R.m_add_three_le_k
    simp only [Ranks.r]; omega
  have hdp : (T.Q.Dw ((i : ℕ) + 1)).p = (D.R.sigW ((i : ℕ) + 1)).1 := (hP.2.2.2 _ hj).1
  have hdq : (T.Q.Dw ((i : ℕ) + 1)).q = (D.R.sigW ((i : ℕ) + 1)).2 := (hP.2.2.2 _ hj).2.1
  have hp0 := (hU.2.1 k).1
  have hΨ := (hU.2.1 k).2
  have hres : res T (sg0 D A) = T.toCore.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0, res_embLL T hT.alg hP.2.2.1]
  have hx : IsModelBaseFrameFamily (R.MW i (sg0 D A)) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) T.toCore.σ₀) :=
    hres ▸ hT.x0 i (sg0 D A) (base_embedding_good T R hT.alg hP.2.2.1)
  have hε : ∀ ρ a, (R.MW i (sg0 D A)).ε ρ a = decide ((a : ℕ) < (T.Q.Dw ((i : ℕ) + 1)).p) := fun ρ a => by
    rw [hC.models.order i ρ a, hdp,
      show (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ hj.1 hj.2 _]
  have hM : ModelW (Wc D i) (rank_Wc i) ((T.U ((i : ℕ) + 1) T.toCore.σ₀).X k) := by
    obtain ⟨hr, hm⟩ := hL.modelW _ hj _ hg
    have hV : T.V ((i : ℕ) + 1) T.toCore.σ₀ = Wc D i := hL.spaceW _ hj _ hg
    have h1 := hm k
    revert hr
    rw [hV]
    exact fun _ _ h => h
  have hn : (κ i).n = (Vc D i).rank := by
    obtain ⟨τ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
    obtain ⟨τ', hτ'⟩ : ∃ τ', τ' ∈ ((T.U ((i : ℕ) + 1) T.toCore.σ₀).X k).Ψ := by
      by_cases h : ComplexEmbedding.conjugate τ ∈ ((T.U ((i : ℕ) + 1) T.toCore.σ₀).X k).Ψ
      · exact ⟨_, h⟩
      · exact ⟨τ, (((T.U ((i : ℕ) + 1) T.toCore.σ₀).X k).cmType τ).2 h⟩
    obtain ⟨t, -⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hP.1 τ' ((hΨ τ').1 hτ')
    rw [(hT.kap i t).2.2, D.sp.V_rank _ hj.1 hj.2]
  refine ⟨⟨hM, fun τ => ?_, ?_⟩, fun τ => hL.familyUniformisationBasePointOrthogonal _ hj _ hg k τ.1 τ.2, ?_, hp0, hU.1, ?_, hr1, hP.1.2.1, hΨ,
    fun hq => isBasOf_onb _ _ _ hx hq hε, hn ▸ dom_wtA (κ i), hn,
    lastPos_wtA_of_pins T.Q hP hj _ (lastPos_of_kapIs hT.kap i)⟩
  · rw [hΨ]
    exact ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi T.Q hP.1 τ, fun ⟨ρ, h⟩ => h ▸ hP.1.2.2.2 ρ⟩
  · have hU' := (Formalism.L2.PjFree.isUnf_ofPj _).2 hU
    obtain ⟨w⟩ := nonempty_uw hU'
    have h1 : ((T.U ((i : ℕ) + 1) T.toCore.σ₀).X k).κ0 = 2 * ((T.U ((i : ℕ) + 1) T.toCore.σ₀).X k).ξ0 :=
      (GlobalTheory.Dict.uw_lattice _ _ _ _ _ _ _ _ _ ((Formalism.L2.PjFree.goodEmb_iff _).2 hg) hU' hr1 w k).1
    rw [h1, hM.2, mul_neg]
  · exact isInvOf_cart _ _ _ hx (by have := hU.1; omega) hε
  · rw [hdp, hdq]
    have h3 := D.R.m_add_three_le_k
    simp only [Ranks.sigW]; omega

end GlobalTheory.AdTh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfSurjective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HolUnifEnd


open GlobalTheory GlobalTheory.SurjIsogeny GlobalTheory.IsogenyModel in
theorem exists_pow_eq_one_of_surjective (A B : Over (Sp ℂ)) [GrpObj A] [GrpObj B] (g : ℕ)
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) (hgA : SmoothOfRelativeDimension g A.hom)
    (hgB : SmoothOfRelativeDimension g B.hom) (ψ : A ⟶ B) [IsMonHom ψ] [Surjective ψ.left] :
    ∃ n : ℕ, 1 ≤ n ∧ ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ ψ = 1 → x ^ n = 1 := by
  have := hB.proper
  have := hA.proper
  have := hA.comm
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom hB.smooth
    hB.geomConnected
  have : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A.hom
    hA.smooth hA.geomConnected
  have : IsIntegral A.left := GeometricallyIntegral.isIntegral_of_subsingleton A.hom
  have : IsProper (ψ.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper ψ.left := IsProper.of_comp ψ.left B.hom
  have hA' : SmoothOfRelativeDimension g (ψ.left ≫ B.hom) := by rw [Over.w]; exact hgA
  obtain ⟨a, ha⟩ := ψ.left.surjective (genericPoint B.left)
  have : LocallyQuasiFinite ψ.left := by
    refine locallyQuasiFinite_of_finite_fibre ψ a ((Set.finite_singleton (genericPoint _)).subset ?_)
    intro x hx
    exact eq_genericPoint_of_apply_eq ψ.left B.hom hgB hA' (ha ▸ hx)
  have hf : IsFinite ψ.left := .of_isProper_of_locallyQuasiFinite _
  obtain ⟨Z, _, i, _, hi, hZ, hk⟩ := exists_kernel ψ
  have hm : Mono i := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono i.left))
  have := isCommMonObj_of_mono i
  obtain ⟨N, hN, hZN⟩ := FiniteFlatKilled.main ℂ Z hZ inferInstance
  refine ⟨N, hN, fun x hx => ?_⟩
  have h1 : i ^ N = 1 := by
    rw [← Category.id_comp i, ← MonObj.pow_comp, hZN, MonObj.one_comp]
  rw [← hk.lift_fst x (toUnit _) hx, ← MonObj.comp_pow, h1, MonObj.comp_one]

theorem exists_factor_pow (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (hA : IsAbelianScheme A)
    [IsSeparated A'.hom] [LocallyOfFiniteType A'.hom] (N : ℕ) (hN : 1 ≤ N) (φ : A ⟶ A') [IsMonHom φ]
    (h : ∀ y : 𝟙_ (Over (Sp ℂ)) ⟶ A, y ^ N = 1 → y ≫ φ = 1) :
    ∃ α : A ⟶ A', IsMonHom α ∧ (𝟙 A ^ N) ≫ α = φ := by
  have hunit : IsUnit ((N : ℕ) : Γ(Sp ℂ, ⊤)) := by
    have := (IsUnit.mk0 (N : ℂ) (by exact_mod_cast (show N ≠ 0 by omega))).map
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    rwa [map_natCast] at this
  obtain ⟨hmon, hfin, het, hsurj⟩ := abelianScheme_id_pow_finite_etale_surjective _ A N hA hunit
  have key : ∀ (T : Over (Sp ℂ)) (x : T ⟶ A), x ≫ (𝟙 A ^ N) = 1 → x ≫ φ = 1 := by
    intro T x hx
    let K := pullback (𝟙 A ^ N) η[A]
    let inc : K ⟶ A := pullback.fst ((𝟙 A ^ N)) η[A]
    have hinc : inc ≫ (𝟙 A ^ N) = 1 := by
      rw [pullback.condition, toUnit_unique (pullback.snd ((𝟙 A ^ N)) η[A]) (toUnit K)]; rfl
    have hp := (IsPullback.of_hasPullback ((𝟙 A ^ N)) η[A]).map (Over.forget (Sp ℂ))
    have he : Etale (pullback.snd ((𝟙 A ^ N)) η[A]).left :=
      MorphismProperty.of_isPullback (P := @Etale) hp het
    have hw : (pullback.snd ((𝟙 A ^ N)) η[A]).left = K.hom := by
      simpa using Over.w (pullback.snd ((𝟙 A ^ N)) η[A])
    rw [hw] at he
    have : IsReduced K.left := GlobalTheory.isReduced_of_smooth_of_isReduced K.hom
    have hk : inc ≫ φ = 1 := by
      refine Over.OverMorphism.ext ?_
      have : LocallyOfFiniteType ((inc ≫ φ).left ≫ A'.hom) := by rw [Over.w]; infer_instance
      refine ext_of_apply_eq A'.hom Set.univ isClosed_univ.isLocallyClosed dense_univ (fun z _ hz => ?_)
        ((Over.w _).trans (Over.w _).symm)
      let p : Over.mk (𝟙 (Sp ℂ)) ⟶ K :=
        Over.homMk (pointOfClosedPoint K.hom z hz) (pointOfClosedPoint_comp _ _ _)
      have hpN : (p ≫ inc) ^ N = 1 := by
        have : (p ≫ inc) ^ N = (p ≫ inc) ≫ (𝟙 A ^ N) := by rw [MonObj.comp_pow, Category.comp_id]
        rw [this, Category.assoc, hinc, MonObj.comp_one]
      have e : p ≫ inc ≫ φ = p ≫ 1 := by
        rw [MonObj.comp_one, ← Category.assoc]
        exact h _ hpN
      have e' := congrArg (fun q => q.left (IsLocalRing.closedPoint ℂ)) e
      have hz' : p.left (IsLocalRing.closedPoint ℂ) = z := pointOfClosedPoint_apply K.hom z hz _
      simp only [Over.comp_left] at e'
      rw [← hz']
      exact e'
    have hx' : x ≫ (𝟙 A ^ N) = toUnit T ≫ η[A] := hx
    rw [← pullback.lift_fst x (toUnit T) hx', Category.assoc]
    change _ ≫ inc ≫ φ = 1
    rw [hk, MonObj.comp_one]
  obtain ⟨⟨α, hα, hc⟩, -⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ A A A' ((𝟙 A ^ N)) φ hmon
    inferInstance inferInstance hsurj inferInstance key
  exact ⟨α, hα, hc⟩

theorem exists_isMonHom_of_map_lattice :
    ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (L : LB A.left) (u : HolUnif A L g) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
      (∀ x ∈ u.Λ, M x ∈ u.Λ) → ∃ α : A ⟶ A, IsMonHom α ∧ ∀ w, u.ex (M w) = u.ex w ≫ α := by
  intro A _ g hA hgA L u M hM
  obtain ⟨hL, -⟩ := abelianSchemeLaws_all
  obtain ⟨B, _, MB, i, r, m, hB, hgB, hMB, hamp, hK, hi, hr, hm, hri⟩ :=
    SS.PrincIsog.exists_isogeny_kTriv ℂ A g hA hgA
  obtain ⟨Q, i', r', -, hi', hr', hir'⟩ :=
    EighthPowerFactor.exists_polAV_hypS_retract ℂ B g hB hgB MB hMB hamp hK
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨v, -, -, -, -, -, hv1, hv2, -⟩ := thetaUnifAV_all Q rig hrig
  have hu := TorusTransfer.tangent_bijective u hgA
  haveI := hi; haveI := hr; haveI := hi'; haveI := hr'
  obtain ⟨J, hJ, hJΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom A Q.A hA Q.isAb L Q.L g Q.g u v
    hv1 hv2 (i ≫ i') inferInstance
  obtain ⟨R, hR, hRΛ, -, -⟩ := HomLinear.exists_linear_of_isMonHom Q.A A Q.isAb hA Q.L L Q.g g v u
    hu.1 hu.2 (r' ≫ r) inferInstance

  have hunit : IsUnit ((m : ℕ) : Γ(Sp ℂ, ⊤)) := by
    have := (IsUnit.mk0 (m : ℂ) (by exact_mod_cast (show m ≠ 0 by omega))).map
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    rwa [map_natCast] at this
  have hsB := (abelianScheme_id_pow_finite_etale_surjective _ B m hB hunit).2.2.2
  have : Surjective (r.left ≫ i.left) := by rw [← Over.comp_left, hri]; exact hsB
  have : Surjective i.left := Surjective.of_comp r.left i.left
  obtain ⟨n, hn, hkill⟩ := exists_pow_eq_one_of_surjective A B g hA hB hgA hgB i

  have hpt : ∀ x : 𝟙_ (Over (Sp ℂ)) ⟶ A, x ≫ (i ≫ i') ≫ (r' ≫ r) ≫ (i ≫ i') = (x ≫ i ≫ i') ^ m := by
    intro x
    simp only [Category.assoc]
    rw [reassoc_of% hir', reassoc_of% hri, ← Category.assoc x i, ← Category.assoc (x ≫ i), MonObj.comp_pow,
      Category.comp_id, MonObj.pow_comp, Category.assoc]
  have hsubv : ∀ a b, v.ex a = v.ex b → a - b ∈ v.Λ := by
    intro a b h
    rw [← v.ker]
    have e := v.ex_add (a - b) b
    rw [sub_add_cancel, h] at e
    have e2 := congrArg (· * (v.ex b)⁻¹) e
    simpa using e2.symm
  have hRJ : ∀ z, R (J z) = m • z := by
    intro z
    have hJy : ∀ t : ℂ, J (t • (R (J z) - m • z)) ∈ v.Λ := by
      intro t
      have h1 : v.ex (J (R (J (t • z)))) = v.ex (m • J (t • z)) := by
        rw [hJ, hR, hJ, holUnif_ex_nsmul_eq_pow, hJ, ← hpt]
        simp only [Category.assoc]
      have h2 := hsubv _ _ h1
      have h3 : t • (R (J z) - m • z) = R (J (t • z)) - m • (t • z) := by
        rw [map_smul, map_smul, smul_sub, smul_comm t m z]
      rw [h3, map_sub, map_nsmul]
      exact h2
    have hJy0 : J (R (J z) - m • z) = 0 :=
      LatticeHom.eq_zero_of_forall_smul_mem v.Λ v.discrete fun t => by rw [← map_smul]; exact hJy t
    have hker : ∀ t : ℂ, u.ex (t • (R (J z) - m • z)) ≫ i = 1 := by
      intro t
      have h2 : u.ex (t • (R (J z) - m • z)) ≫ i ≫ i' = 1 := by
        rw [← hJ, map_smul, hJy0, smul_zero, holUnif_ex_zero_eq_one]
      calc u.ex (t • (R (J z) - m • z)) ≫ i = u.ex (t • (R (J z) - m • z)) ≫ i ≫ i' ≫ r' := by
            rw [hir', Category.comp_id]
        _ = (u.ex (t • (R (J z) - m • z)) ≫ i ≫ i') ≫ r' := by simp only [Category.assoc]
        _ = 1 := by rw [h2, MonObj.one_comp]
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hy0 : R (J z) - m • z = 0 := LatticeHom.eq_zero_of_forall_smul_mem u.Λ u.discrete fun t => by
      rw [← u.ker]
      have e := hkill _ (hker ((n : ℂ)⁻¹ * t))
      rw [← holUnif_ex_nsmul_eq_pow, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, ← _root_.mul_assoc,
        mul_inv_cancel₀ hn0, _root_.one_mul] at e
      exact e
    exact sub_eq_zero.1 hy0

  obtain ⟨β, hβ, hβe⟩ := _root_.GlobalTheory.exists_isMonHom_of_map_lattice thetaUnifAV_all hL Q Q Q.g v v (J ∘ₗ M ∘ₗ R)
    rfl rfl (fun l hl => hJΛ _ (hM _ (hRΛ _ hl)))
  haveI := hβ
  have hφ : ∀ z, u.ex z ≫ (i ≫ i') ≫ β ≫ (r' ≫ r) = u.ex ((m * m) • M z) := by
    intro z
    have e := hβe (J z)
    simp only [LinearMap.comp_apply] at e
    rw [← Category.assoc, ← hJ, ← Category.assoc, ← e, ← hR, hRJ, hRJ, map_nsmul, smul_smul]
  have := hA.proper
  obtain ⟨α, hα, hαφ⟩ := exists_factor_pow A A hA (m * m) (Nat.one_le_iff_ne_zero.2 (by positivity))
    ((i ≫ i') ≫ β ≫ (r' ≫ r)) fun y hy => by
      obtain ⟨z, rfl⟩ := u.ex_onto y
      rw [← holUnif_ex_nsmul_eq_pow, u.ker] at hy
      rw [hφ, u.ker, ← map_nsmul]
      exact hM _ hy
  refine ⟨α, hα, fun w => ?_⟩
  have hN0 : ((m * m : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (show m * m ≠ 0 by positivity)
  have hw : (m * m) • (((m * m : ℕ) : ℂ)⁻¹ • w) = w := by
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ hN0, one_smul]
  calc u.ex (M w) = u.ex ((m * m) • M (((m * m : ℕ) : ℂ)⁻¹ • w)) := by rw [← map_nsmul, hw]
    _ = u.ex (((m * m : ℕ) : ℂ)⁻¹ • w) ≫ (i ≫ i') ≫ β ≫ (r' ≫ r) := (hφ _).symm
    _ = u.ex (((m * m : ℕ) : ℂ)⁻¹ • w) ≫ (𝟙 A ^ (m * m)) ≫ α := by rw [hαφ]
    _ = u.ex w ≫ α := by
      rw [← Category.assoc, MonObj.comp_pow, Category.comp_id, ← holUnif_ex_nsmul_eq_pow, hw]

end GlobalTheory.HolUnifEnd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairRecordCore
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.RecPairCore
open GlobalTheory.AdTh.RecPair

theorem isPair_record_core : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0), VStd D i → IsPair R.ψ R.θ (Vc D i) (Wc D i) (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).1 (Lift.chrTh (R.toLevCh.mu t) R.eta ((i : ℕ) + 1)).2 (R.ωP i t) ∧ (Vc D i).rank ≠ 0 ∧ (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) = L0c D (Vc D i) ∧ (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) = L0c D (Wc D i) ∧ IsSelfDualC (Vc D i) (R.ΛV i) ∧ IsSelfDualC (Wc D i) (R.ΛW i) ∧ (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) = (Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank : Set (Fin (Vc D i).rank → D.host.E)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F h i t hV
  have hL := h.lev
  have hW := h.thP.ωP i t
  have hr : Odd D.R.r := by
    have := D.R.m_add_three_le_k
    obtain ⟨a, ha⟩ := D.R.k_even
    obtain ⟨b, hb⟩ := D.R.m_even
    exact ⟨a + b - 1, by simp only [Ranks.r]; omega⟩
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hev : Even (Vc D i).rank := rV ▸ hr.add_odd D.R.t_odd
  have hη : GlobalTheory.WeilParts.IsEtaTilde D R.eta :=
    GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D _ _ hL.eta R.C.isEta _ _ _ hW.resS hW.resT (hev.add_odd (rW ▸ hr))
  have lV := coe_eq_of_frame (hL.βV i)
  have lW := coe_eq_of_frame (hL.βW i)
  refine ⟨⟨hW, h.models.inf, hV.1, hev, D.sp.V_sig _, D.sp.W_sig _, exp_mu hL i t, fun τ => ?_, fun v ε hv => ?_, ⟨_, hη⟩⟩,
    ?_, lV, lW, selfDual_of_coe lV, selfDual_of_coe lW, ?_⟩
  · obtain ⟨a, ha⟩ := exp_mu hL i t τ
    obtain ⟨s, hs⟩ := hr
    refine ⟨a - s - 1, ?_⟩
    have h3 := GlobalTheory.Mem.HeckeExp.hasInfExp_mul ha (GlobalTheory.Mem.HeckeExp.hasInfExp_inv (hη.2.2.2 τ))
    have e : ((a - s - 1 : ℤ) : ℚ) + ((Wc D i).rank : ℚ) / 2 = (a : ℚ) + -(1 / 2) := by
      rw [rW, hs]; push_cast; ring
    rw [e]
    exact h3
  · obtain ⟨-, e, ⟨⟨es, hes, -⟩, -⟩, -⟩ := h.thP.vP i t
    have key := fun P (hP : P.under (𝓞 D.host.F) = v) =>
      (GlobalTheory.levCh_unramified_places D T0 R.toLevCh A.μ0 hL t).2.2.2 P fun PP hPP => by
        rw [hP]
        exact under_ne (hes PP (Finset.mem_union.2 hPP)) hv
    have u1 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hL.mu0 i) v ε hv.1 fun P hP => (key P hP).2 i
    have u2 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ (hL.xi t) v ε hv.1 fun P hP => (key P hP).1
    have u3 := GlobalTheory.UnramOver.unramAt_of_unrAt D _ _ hL.eta v ε hv.1 fun P _ => R.C.isEta.unr P
    have u4 : GlobalTheory.WeilParts.UnramAt ε (R.toLevCh.mu t ((i : ℕ) + 1)) := fun x a b c => by
      show R.mu0 ((i : ℕ) + 1) x * R.xi t x = 1
      rw [u1 x a b c, u2 x a b c, one_mul]
    refine ⟨u4, fun x a b c => ?_⟩
    show R.toLevCh.mu t ((i : ℕ) + 1) x * (R.eta x)⁻¹ = 1
    rw [u4 x a b c, u3 x a b c, inv_one, one_mul]
  · rw [rV]
    exact (Nat.add_pos_left hr.pos _).ne'
  · rw [lV, ← GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice, hV.2]
    rfl

end GlobalTheory.AdTh.RecPairCore
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM Matrix

namespace GlobalTheory.FlatDegreeCompare

section Lie

variable {R K : Type} [CommRing R] [CommRing K]

def Indep {A : Over (Sp K)} [GrpObj A] {m : ℕ} (x : Fin m → (epsR K ⟶ A)) : Prop :=
  (∀ i, IsTangent (x i)) ∧ ∀ c c' w, IsLieComb c x w → IsLieComb c' x w → c = c'

theorem Indep.of_basis {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {n : ℕ} {e : Fin n → (epsR K ⟶ A)}
    (he : IsLieBasis e) : Indep e :=
  ⟨he.1, fun c _ w h h' => (he.2 w ((LieComb.lieComb_algebra K A n e he.1).2.1 c w h)).unique h h'⟩

theorem Indep.of_eigBasis {O : Type} [CommRing O] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {act : OAct O A}
    {χ : O →+* K} {m : ℕ} {x : Fin m → (epsR K ⟶ A)} (h : EigenvectorLieDegree.IsEigBasis act χ x) : Indep x := by
  refine ⟨fun i => (h.1 i).1, fun c c' w hc hc' => (h.2 w ?_).unique hc hc'⟩
  let y : Fin m → Serre.Lie act := fun i => Serre.Lie.mk act (x i) (h.1 i).1
  have hy : ∀ a i, a • y i = χ a • y i := fun a i => Serre.Lie.ext (Over.OverMorphism.ext ((h.1 i).2 a))
  obtain rfl := (Serre.Lie.isLieComb_iff c y w).1 hc
  refine ⟨Serre.Lie.isTangent _, fun a => ?_⟩
  have : a • ∑ i, c i • y i = χ a • ∑ i, c i • y i := by
    rw [Finset.smul_sum, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [smul_comm a, hy, smul_comm]
  exact congrArg (fun z : Serre.Lie act => z.hom.left) this

variable {f : R →+* K} {G : Over (Sp R)} [GrpObj G] {A : Over (Sp K)} [GrpObj A] {φ : A.left ⟶ G.left}

theorem exists_frame [IsLocalRing R] (hG : IsSemiAbelian G) (hφ : IsGrpPullback A G (spMap f) φ) {m : ℕ}
    {x : Fin m → (epsR K ⟶ A)} (hx : ∀ i, IsTangent (x i)) :
    ∃ (n : ℕ) (e : Fin n → (epsR R ⟶ G)) (e' : Fin n → (epsR K ⟶ A)) (P : Matrix (Fin m) (Fin n) K),
      IsLieBasis e ∧ IsLieBasis e' ∧ (∀ j, IsVecOver f φ (e j) (e' j)) ∧ ∀ i, IsLieComb (P i) e' (x i) := by
  have := hG.smooth
  obtain ⟨n, e, he⟩ := Chart.exists_isLieBasis G hG.smooth
  choose e' h _ using fun j => existsUnique_isVecOver hφ.1 (e j)
  have he' := Chart.isLieBasis_baseChange f hφ he h
  choose P hP _ using fun i => he'.2 _ (hx i)
  exact ⟨n, e, e', P, he, he', h, hP⟩

end Lie

section Local

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {k : Type} [Field k] [NumberField k]
  {t : SAB H (Sp k)} {m : ℕ} {x : Fin m → (epsR k ⟶ t.G)} {𝔭 : HeightOneSpectrum (𝓞 k)}

end Local

end GlobalTheory.FlatDegreeCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgEqOfLeRightStabiliser
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgEqOfLeRightStabiliser
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.BCT

theorem avg_eq_of_le_rStab : ∀ (H : Type) [Group H] (u : H → ℂ) (S : Subgroup H), S ≤ rStab u → S.index ≠ 0 →
    avg u = (S.index : ℂ)⁻¹ * ∑ᶠ q : H ⧸ S, u q.out := by
  intro H _ u S hS hi
  haveI : S.FiniteIndex := ⟨hi⟩
  haveI : (rStab u).FiniteIndex := Subgroup.finiteIndex_of_le hS
  have hRi : (rStab u).index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hu : ∀ x : H, u ((QuotientGroup.mk x : H ⧸ rStab u).out) = u x := by
    intro x
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (rStab u) x
    rw [hk]
    exact k.2 x
  let e := Subgroup.quotientEquivProdOfLE hS
  have he : ∀ q : H ⧸ S, ((e q).1 : H ⧸ rStab u) = QuotientGroup.mk q.out := by
    intro q
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  haveI : Fintype (H ⧸ S) := Fintype.ofFinite _
  haveI : Fintype (H ⧸ rStab u) := Fintype.ofFinite _
  haveI : Finite ((rStab u) ⧸ S.subgroupOf (rStab u)) := by
    have : Finite ((H ⧸ rStab u) × (rStab u) ⧸ S.subgroupOf (rStab u)) := Finite.of_equiv _ e
    exact Finite.prod_right (H ⧸ rStab u)
  haveI : Fintype ((rStab u) ⧸ S.subgroupOf (rStab u)) := Fintype.ofFinite _
  have hsum : ∑ᶠ q : H ⧸ S, u q.out =
      (S.relIndex (rStab u) : ℂ) * ∑ᶠ p : H ⧸ rStab u, u p.out := by
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    have h1 : ∀ q : H ⧸ S, u q.out = (fun p : (H ⧸ rStab u) × ((rStab u) ⧸ S.subgroupOf (rStab u)) =>
        u p.1.out) (e q) := by
      intro q
      simp only
      rw [he q, hu]
    rw [Finset.sum_congr rfl (fun q _ => h1 q), Equiv.sum_comp e (fun p => u p.1.out),
      Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.mul_sum]
    congr 1
    rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
  rw [avg, hsum, ← Subgroup.relIndex_mul_index hS]
  have h2 : (S.relIndex (rStab u) : ℂ) ≠ 0 := by
    have : S.relIndex (rStab u) ≠ 0 := by
      intro h0; apply hi; rw [← Subgroup.relIndex_mul_index hS, h0, zero_mul]
    exact_mod_cast this
  have h3 : ((rStab u).index : ℂ) ≠ 0 := by exact_mod_cast hRi
  push_cast
  field_simp

end GlobalTheory.BCT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgEqOfLeRightStabiliserStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.avg_eq_of_le_rightStabiliser : ∀ (H : Type) [Group H] (u : H → ℂ) (S : Subgroup H), S ≤ rStab u → S.index ≠ 0 → avg u = (S.index : ℂ)⁻¹ * ∑ᶠ q : H ⧸ S, u q.out := by
  first | exact @GlobalTheory.BCT.avg_eq_of_le_rStab | exact GlobalTheory.BCT.avg_eq_of_le_rStab | (intros; apply GlobalTheory.BCT.avg_eq_of_le_rStab <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.LB (resG_resG)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM germ_resM)
open GlobalTheory.QCoh (appLinear appLinear_apply stalkLinear)

namespace GlobalTheory.VB.Ker

section Algebra

variable {R M₁ M₂ M₃ : Type} [CommRing R] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [Module R M₁] [Module R M₂] [Module R M₃] {f : M₁ →ₗ[R] M₂} {g : M₂ →ₗ[R] M₃}

theorem bijective_sumElim_iff {ι κ : Type} [Fintype ι] [Fintype κ] (hf : Function.Injective f)
    (hfg : Function.Exact f g) (e : ι → M₁) (t : κ → M₂)
    (ht : Function.Bijective (Fintype.linearCombination R fun j => g (t j))) :
    Function.Bijective (Fintype.linearCombination R (Sum.elim (fun i => f (e i)) t)) ↔
      Function.Bijective (Fintype.linearCombination R e) := by
  have h1 (a : ι ⊕ κ → R) : Fintype.linearCombination R (Sum.elim (fun i => f (e i)) t) a =
      f (Fintype.linearCombination R e fun i => a (.inl i)) +
        Fintype.linearCombination R t fun j => a (.inr j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Fintype.linearCombination_apply, Fintype.sum_sum_type, map_sum]
  have h2 (b : κ → R) : g (Fintype.linearCombination R t b) =
      Fintype.linearCombination R (fun j => g (t j)) b := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Fintype.linearCombination_apply, map_sum]
  have h3 (b : κ → R) (m m' : M₁) (h : f m + Fintype.linearCombination R t b = f m') : b = 0 := by
    have := congrArg g h
    rw [map_add (f := _), hfg.apply_apply_eq_zero, hfg.apply_apply_eq_zero, zero_add, h2] at this
    exact ht.1 (this.trans (map_zero _).symm)
  constructor
  · refine fun H => ⟨(injective_iff_map_eq_zero _).2 fun a ha => ?_, fun m => ?_⟩
    · have : Sum.elim a (0 : κ → R) = 0 := H.1 (by
        rw [h1, map_zero]
        change f (Fintype.linearCombination R e a) + Fintype.linearCombination R t 0 = 0
        rw [ha, map_zero, map_zero, add_zero])
      exact funext fun i => congrFun this (.inl i)
    · obtain ⟨a, ha⟩ := H.2 (f m)
      rw [h1] at ha
      rw [h3 _ _ _ ha, map_zero, add_zero] at ha
      exact ⟨_, hf ha⟩
  · refine fun H => ⟨(injective_iff_map_eq_zero _).2 fun a ha => ?_, fun m => ?_⟩
    · rw [h1, ← map_zero f] at ha
      have hb := h3 _ _ _ ha
      rw [hb, map_zero, add_zero] at ha
      have ha' := H.1 ((hf ha).trans (map_zero _).symm)
      funext k
      rcases k with i | j
      exacts [congrFun ha' i, congrFun hb j]
    · obtain ⟨b, hb⟩ := ht.2 (g m)
      obtain ⟨n, hn⟩ := (hfg (m - Fintype.linearCombination R t b)).1 (by
        rw [map_sub, h2, hb, sub_self])
      obtain ⟨a, rfl⟩ := H.2 n
      exact ⟨Sum.elim a b, by rw [h1]; exact eq_sub_iff_add_eq.1 hn⟩

theorem nonempty_basis_of_exact [IsLocalRing R] {r s : ℕ} (hf : Function.Injective f)
    (hfg : Function.Exact f g) (hg : Function.Surjective g) (b : Module.Basis (Fin (r + s)) R M₂)
    (c : Module.Basis (Fin s) R M₃) : Nonempty (Module.Basis (Fin r) R M₁) := by
  have := Module.Free.of_basis b
  have := Module.Free.of_basis c
  have := Module.Finite.of_basis b
  have := Module.Finite.of_basis c
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property g LinearMap.id hg
  obtain ⟨φ, hφ, -⟩ := hfg.splitSurjectiveEquiv hf ⟨σ, hσ⟩
  let π : M₂ →ₗ[R] M₁ := LinearMap.fst R M₁ M₃ ∘ₗ φ.toLinearMap
  have hπ : π ∘ₗ f = LinearMap.id := by
    ext m
    simp [π, hφ]
  have : Module.Projective R M₁ := .of_split f π hπ
  have : Module.Finite R M₁ := .of_surjective π fun m => ⟨f m, LinearMap.congr_fun hπ m⟩
  have : Module.Free R M₁ := Module.free_of_flat_of_isLocalRing
  have h := φ.finrank_eq
  rw [Module.finrank_prod, Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis c,
    Fintype.card_fin, Fintype.card_fin] at h
  exact ⟨Module.finBasisOfFinrankEq R M₁ (by omega)⟩

theorem bijective_iff_isUnit_det {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R M₁)
    (v : ι → M₁) : Function.Bijective (Fintype.linearCombination R v) ↔ IsUnit (b.det v) := by
  rw [← Module.Basis.is_basis_iff_det, Function.Bijective, ← linearIndependent_iff_injective_fintypeLinearCombination,
    ← LinearMap.range_eq_top, Fintype.range_linearCombination]

end Algebra

variable {X : Scheme.{0}} {F : X.Modules} {U : X.Opens} {ι : Type} [Fintype ι]

theorem exists_germ_eq_family {x : X} (hx : x ∈ U) (a : ι → (F.presheaf.stalk x :)) :
    ∃ (V : X.Opens) (_ : V ≤ U) (hV : x ∈ V) (e : ι → Γ(F, V)),
      ∀ i, F.presheaf.germ V x hV (e i) = a i := by
  choose W hW b hb using fun i => F.presheaf.exists_germ_eq (a i)
  have hxV : x ∈ U ⊓ Finset.univ.inf W := ⟨hx, by
    rw [Opens.coe_finset_inf]; simpa using hW⟩
  have hV (i : ι) : U ⊓ Finset.univ.inf W ≤ W i :=
    inf_le_right.trans (Finset.inf_le (Finset.mem_univ i))
  exact ⟨_, inf_le_left, hxV, fun i => resM F (hV i) (b i), fun i => by rw [germ_resM, hb]⟩

theorem germ_det [DecidableEq ι] {e : ι → Γ(F, U)} (he : IsFrame e) (v : ι → Γ(F, U)) {x : X}
    (hx : x ∈ U) : X.presheaf.germ U x hx ((he.basis le_rfl).det v) =
      (he.stalkBasis x hx).det fun i => F.presheaf.germ U x hx (v i) := by
  rw [Module.Basis.det_apply, Module.Basis.det_apply]
  refine (RingHom.map_det (X.presheaf.germ U x hx).hom _).trans ?_
  congr 1
  ext i j
  rw [Module.Basis.toMatrix_apply]
  conv_rhs => rw [← (he.basis le_rfl).sum_repr (v j)]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, QCoh.germ_smul, IsFrame.basis_apply, resM_self]
  simp only [← he.stalkBasis_apply x hx]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, Module.Basis.repr_sum_self]
  rfl

theorem exists_isFrame_of_bijective_stalk {e : ι → Γ(F, U)} (he : IsFrame e) (v : ι → Γ(F, U))
    {x : X} (hx : x ∈ U) (hv : Function.Bijective (Fintype.linearCombination (X.presheaf.stalk x)
      fun i => (F.presheaf.germ U x hx (v i) : (F.presheaf.stalk x :)))) :
    ∃ (W : X.Opens) (h : W ≤ U), x ∈ W ∧ IsFrame fun i => resM F h (v i) := by
  classical
  rw [bijective_iff_isUnit_det (he.stalkBasis x hx), ← germ_det he] at hv
  refine ⟨X.basicOpen ((he.basis le_rfl).det v), X.basicOpen_le _,
    (X.mem_basicOpen _ x hx).2 hv, fun V h => ?_⟩
  simp only [resM_resM]
  rw [bijective_iff_isUnit_det (he.basis ((h.trans (X.basicOpen_le _)).trans le_rfl)),
    ← he.resG_det, ← resG_resG (X.basicOpen_le _) h]
  exact (X.toRingedSpace.isUnit_res_basicOpen _).map _

end GlobalTheory.VB.Ker

namespace GlobalTheory.VB

open Ker

theorem isVB_X₁_of_shortExact : ∀ (X : Scheme.{0}) (S : ShortComplex X.Modules) (r s : ℕ),
    S.ShortExact → IsVB S.X₂ (r + s) → IsVB S.X₃ s → IsVB S.X₁ r := by
  intro X S r s hS h₂ h₃ x
  have := hS.mono_f
  have := hS.epi_g
  have := h₂.isQuasicoherent
  have := h₃.isQuasicoherent
  obtain ⟨U₀, b₀, hx₀, hb₀⟩ := h₂ x
  obtain ⟨U, c, hU, hx, hle, hc⟩ := h₃.exists_affine hx₀
  choose t ht using fun j => QCoh.surjective_app_of_epi S.g hU (c j)
  have hex := (QCoh.exact_iff_stalkLinear S).1 hS.exact x
  obtain ⟨β⟩ := nonempty_basis_of_exact (QCoh.stalkLinear_injective S.f x) hex
    (QCoh.stalkLinear_surjective S.g x) (hb₀.stalkBasis x hx₀) (hc.stalkBasis x hx)
  obtain ⟨V, hV, hxV, e, he⟩ := exists_germ_eq_family hx β
  have hb := (hb₀.res (hV.trans hle)).comp_equiv finSumFinEquiv
  obtain ⟨W, hW, hxW, hv⟩ := exists_isFrame_of_bijective_stalk hb
    (Sum.elim (fun i => S.f.app V (e i)) fun j => resM S.X₂ hV (t j)) hxV (by
      have := (bijective_sumElim_iff (QCoh.stalkLinear_injective S.f x) hex β
        (fun j => S.X₂.presheaf.germ U x hx (t j)) (by
          simp only [QCoh.stalkLinear_germ, ht]
          exact hc.bijective_stalk x hx)).2 (by
          rw [Function.Bijective, ← linearIndependent_iff_injective_fintypeLinearCombination,
            ← LinearMap.range_eq_top, Fintype.range_linearCombination]
          exact ⟨β.linearIndependent, β.span_eq⟩)
      convert this using 3
      funext k
      rcases k with i | j
      · rw [Sum.elim_inl, Sum.elim_inl, ← he, QCoh.stalkLinear_germ]
      · rw [Sum.elim_inr, Sum.elim_inr, germ_resM])
  refine ⟨W, fun i => resM S.X₁ hW (e i), hxW, fun T hT => ?_⟩
  refine (bijective_sumElim_iff (f := appLinear S.f T) (g := appLinear S.g T)
    (QCoh.injective_app_of_mono S.f T) (QCoh.exact_app_of_exact_of_mono hS.exact T) _
    (fun j => resM S.X₂ ((hT.trans hW).trans hV) (t j)) ?_).1 ?_
  · simp only [appLinear_apply, app_resM, ht]
    exact hc T _
  · convert hv T hT using 3
    funext k
    rcases k with i | j
    · simp only [Sum.elim_inl, appLinear_apply, app_resM]
    · simp only [Sum.elim_inr, resM_resM]

end GlobalTheory.VB
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
noncomputable section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

namespace GlobalTheory.KapLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def stdH (w : Pl E) {n : ℕ} (v v' : Fin n → w.adicCompletion E) : w.adicCompletion E :=
  ∑ k, v k * cj w (v' k)

def Bridge (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) : Prop :=
  (∀ x, e (K.c x) = cj w (e x)) ∧ (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) ∧
    (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) ∧ qV E w = K.q ^ 2

def Fits (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K)
    (Q : (w.adicCompletion E)[X]) (u : B.A) : Prop :=
  Algebra.adjoin K.E {u} = ⊤ ∧ aeval u (Q.map e.symm.toRingHom) = 0 ∧ Module.finrank K.E B.A = Q.natDegree ∧
    u * B.σ u = 1

def IsModel (w : Pl E) {K : GlobalTheory.UnitLemma.UQ} (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K)
    (u x : B.A) {n : ℕ} (γ : GLw n w) : Prop :=
  ∃ ψ : B.A ≃+ (Fin n → w.adicCompletion E), (∀ (c : K.E) (y : B.A), ψ (c • y) = e c • ψ y) ∧
    (∀ y, ψ (u * y) = γ.val *ᵥ ψ y) ∧ ∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z)

def congSet (w : Pl E) (n k : ℕ) : Set (GLw n w) :=
  {g | g ∈ GlobalTheory.LFun.KGL w (n := n) ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤
    WithZero.exp (-(k : ℤ))}

theorem clRel_equiv {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) :
    Equivalence (fun x y : {x : B.Aˣ // B.σ (x : B.A) = x} =>
      ∃ u : B.Aˣ, (y.1 : B.A) = x.1 * (u * B.σ (u : B.A))) := by
  refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
  · rintro x y ⟨u, hu⟩
    refine ⟨u⁻¹, ?_⟩
    have h1 : ((u : B.A) * ((u⁻¹ : B.Aˣ) : B.A)) * (B.σ (u : B.A) * B.σ ((u⁻¹ : B.Aˣ) : B.A)) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one, one_mul]
    rw [hu]
    calc (x.1 : B.A) = x.1 * (((u : B.A) * ((u⁻¹ : B.Aˣ) : B.A)) * (B.σ (u : B.A) * B.σ ((u⁻¹ : B.Aˣ) : B.A))) := by
          rw [h1, mul_one]
      _ = _ := by ring
  · rintro x y z ⟨u, hu⟩ ⟨v, hv⟩
    exact ⟨u * v, by rw [hv, hu, Units.val_mul, map_mul]; ring⟩

theorem conjRel_equiv (G : Type) [Group G] :
    Equivalence (fun x y : G => ∃ g, y = g⁻¹ * x * (MonoidHom.id G) g) := by
  refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
  · rintro x y ⟨g, rfl⟩
    exact ⟨g⁻¹, by simp [mul_assoc]⟩
  · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
    exact ⟨g * h, by simp [mul_assoc]⟩

theorem cast_finsum {α : Type*} (f : α → ℚ) : ((∑ᶠ a, f a : ℚ) : ℂ) = ∑ᶠ a, (f a : ℂ) := by
  by_cases h : (Function.support f).Finite
  · exact map_finsum (Rat.castHom ℂ) h
  · have h' : ¬ (Function.support fun a => (f a : ℂ)).Finite := by
      simpa [Function.support] using h
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h']
    simp

end GlobalTheory.KapLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicUnitaryLocallyCompactHausdorff
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.UnipDom

namespace GlobalTheory.AdelicUnitaryTop

theorem lcsc_UA : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E),
    LocallyCompactSpace (UA σ J) ∧ SecondCountableTopology (UA σ J) ∧ T2Space (UA σ J) := by
  intro F E _ _ _ _ _ σ n J
  haveI := locallyCompact_adele F
  haveI := secondCountable_adele F
  haveI := t2Space_adeleRing_numberField F
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  obtain ⟨e⟩ := nonempty_homeomorph (F := F) (E := E) (AF F)
  haveI : LocallyCompactSpace (AE F E) := e.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (AE F E) := e.secondCountableTopology
  haveI : T2Space (AE F E) := e.isEmbedding.t2Space
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → AE F E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : LocallyCompactSpace (GL (Fin n) (AE F E)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → AE F E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (AE F E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GL (Fin n) (AE F E)) :=
    Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : T2Space (GL (Fin n) (AE F E)) := Units.isEmbedding_embedProduct.t2Space
  have hσ : Continuous (cA σ) := IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap
  have hc : IsClosed (UG (cA σ) (incM F J) : Set (GL (Fin n) (AE F E))) := by
    have hv : Continuous fun g : GL (Fin n) (AE F E) => (g : Matrix (Fin n) (Fin n) (AE F E)) :=
      Units.continuous_val
    exact isClosed_eq ((hv.matrix_transpose.matrix_mul continuous_const).matrix_mul
      (hv.matrix_map hσ)) continuous_const
  exact ⟨hc.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology,
    inferInstanceAs (T2Space (UG (cA σ) (incM F J)))⟩

end GlobalTheory.AdelicUnitaryTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameOfProjective
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB
open GlobalTheory.Twist (resM resM_resM resM_self)

namespace GlobalTheory.VB.Summand

theorem free_of_free_away {R M R' M' : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [CommRing R'] [Algebra R R'] [AddCommGroup M'] [Module R M'] [Module R' M']
    [IsScalarTower R R' M'] (r : R) [IsLocalization.Away r R'] (f : M →ₗ[R] M')
    [IsLocalizedModule (.powers r) f]
    [Module.Free (Localization (.powers r)) (LocalizedModule.Away r M)] : Module.Free R' M' := by
  set e := (IsLocalization.algEquiv (.powers r) (Localization (.powers r)) R').toRingEquiv
  have := RingHomInvPair.of_ringEquiv e
  have := RingHomInvPair.of_ringEquiv_symm e
  refine Module.Free.of_equiv (σ := (e : Localization (.powers r) →+* R'))
    { __ := IsLocalizedModule.iso (.powers r) f, map_smul' := ?_ }
  intro a x
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq (.powers r) a
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f s)).1
  simp [e, ← map_smul, ← smul_assoc]

variable {X : Scheme.{0}} {F G : X.Modules} {U : X.Opens}

theorem isFrame_of_affine_basis [G.IsQuasicoherent] (hU : IsAffineOpen U) {ι : Type} [Fintype ι]
    (b : Module.Basis ι Γ(X, U) Γ(G, U)) : IsFrame (F := G) (U := U) b := by
  refine isFrame_of_forall_exists fun V h x hx => ?_
  obtain ⟨W, hW, hxW, hle⟩ := QCoh.exists_affine_mem_le x hx
  refine ⟨W, hle, hxW, ?_⟩
  letI := QCoh.resAlgebra (hle.trans h)
  letI := QCoh.resModule G (hle.trans h)
  haveI := QCoh.res_isScalarTower G (hle.trans h)
  let b' := (QCoh.isBaseChange_resLinear G hU hW (hle.trans h)).basis b
  have hb (i : ι) : b' i = resM G (hle.trans h) (b i) := by
    rw [IsBaseChange.basis_apply]
    rfl
  have : Fintype.linearCombination Γ(X, W) (fun i => resM G (hle.trans h) (b i)) =
      b'.equivFun.symm.toLinearMap := by
    ext a : 1
    simp [Fintype.linearCombination_apply, hb]
  rw [this]
  exact b'.equivFun.symm.bijective

theorem exists_frame_of_projective [G.IsQuasicoherent] (hU : IsAffineOpen U)
    [Module.Finite Γ(X, U) Γ(G, U)] [Module.Projective Γ(X, U) Γ(G, U)] (y : U) :
    ∃ (V : X.Opens) (n : ℕ) (e : Fin n → Γ(G, V)), (y : X) ∈ V ∧ IsFrame e := by
  have := Module.finitePresentation_of_projective Γ(X, U) Γ(G, U)
  have := hU.isLocalization_stalk y
  have := QCoh.isLocalizedModule_germLinear G hU y
  have hbc := QCoh.isBaseChange_germLinear G hU y
  have : Module.Finite (X.presheaf.stalk (y : X)) (G.presheaf.stalk (y : X) :) :=
    .equiv hbc.equiv
  have : Module.Projective (X.presheaf.stalk (y : X)) (G.presheaf.stalk (y : X) :) :=
    .of_equiv hbc.equiv
  have : Module.Free (X.presheaf.stalk (y : X)) (G.presheaf.stalk (y : X) :) :=
    Module.free_of_flat_of_isLocalRing
  obtain ⟨f, hf, hfree, -⟩ := Module.FinitePresentation.exists_free_localizedModule_powers
    (hU.primeIdealOf y).asIdeal.primeCompl (QCoh.germLinear G y) (X.presheaf.stalk (y : X))
  have hxf := (QCoh.mem_primeCompl_primeIdealOf_iff hU y f).1 hf
  have := hU.isLocalization_basicOpen f
  have := QCoh.isLocalizedModule_resBasicOpen G hU f
  have : Module.Free Γ(X, X.basicOpen f) Γ(G, X.basicOpen f) :=
    free_of_free_away f (QCoh.resBasicOpen G f)
  have : Module.Finite Γ(X, X.basicOpen f) Γ(G, X.basicOpen f) :=
    Module.Finite.of_isLocalizedModule (.powers f) (QCoh.resBasicOpen G f)
  exact ⟨_, _, _, hxf, (isFrame_of_affine_basis (hU.basicOpen f)
    (Module.Free.chooseBasis _ _)).comp_equiv (Fintype.equivFin _).symm⟩

end GlobalTheory.VB.Summand
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBallFamMonoNegAdd
open Filter Topology GlobalTheory.VolBr

namespace GlobalTheory.VolBr

theorem isBallFam_mono_neg_add :
    ∀ (G : Type) [AddCommGroup G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B →
      (∀ r r', r ≤ r' → B r ⊆ B r') ∧ (∀ r x, x ∈ B r → -x ∈ B r) ∧
        (∀ r r' x y, x ∈ B r → y ∈ B r' → x + y ∈ B (r + r')) := by
  intro G _ Λ B hB
  have hneg : ∀ r x, x ∈ B r → -x ∈ B r := by
    intro r x hx
    have h := hB.sub_mem 0 r 0 x (hB.zero_mem 0 le_rfl) hx
    simpa using h
  refine ⟨?_, hneg, ?_⟩
  · intro r r' hrr' x hx
    have h := hB.sub_mem r (r' - r) x 0 hx (hB.zero_mem _ (sub_nonneg.mpr hrr'))
    simpa using h
  · intro r r' x y hx hy
    have h := hB.sub_mem r r' x (-y) hx (hneg r' y hy)
    simpa using h

end GlobalTheory.VolBr
end
