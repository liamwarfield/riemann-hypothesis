module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JEnd
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.JTwistA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.THasAutOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TLevelU
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.VwinOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TOrdVan

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.HVCore
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.THidaU
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
private theorem coef_isCoef (l : ℕ) [hl : Fact l.Prime] (c : Coef l) : Pa.IsCoef l c.O := by
  obtain ⟨hc, hf, hlm, -, -, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨hc, hf, (CharP.charP_iff_prime_eq_zero hl.out).2 ?_⟩
  rw [← map_natCast (IsLocalRing.residue c.O), IsLocalRing.residue_eq_zero_iff]
  exact hlm
private theorem locP_of (P : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) : _root_.UpperTheory.V.Pa.LocPAlt :=
  ⟨P.loc.bz, P.loc.geo, GlobalTheory.Published.TameLocal_of_duality P.coh.lt⟩
theorem UpperTheory.V.Hi.hida_unitary_of_printed_hida :
    _root_.UpperTheory.V.Af.HypothesesH' → _root_.UpperTheory.V.W.HidaUAlt := by
  intro P l _ L Ω _ _ _ _ _ _ s V hS _ c _ n hn r B Λ ι
  obtain ⟨R⟩ := _root_.UpperTheory.V.Hi.nonempty_unitaryHeckeData P l L Ω s n hn V (QData.empty V hS) c r ι Λ
  let K : (hset (QData.empty V hS) R.τ₀).Lev := ⟨fun q => Empty.elim q, fun q => Empty.elim q⟩
  obtain ⟨J, hJ⟩ := _root_.UpperTheory.V.Hi.exists_hecke_ideal P l L Ω s n hn V _ c r ι B Λ R K
  have hE := _root_.UpperTheory.Gal.projectedFormsSystemPart.decomposition_and_automorphicAway_of_isJ P l L Ω s n hn V _ c r ι B Λ R K hS J hJ
  have := coef_isCoef l c
  exact ⟨J, ⟨_root_.UpperTheory.V.Hi.ring_props_of_is_j_unitary_hecke_data P l L Ω s n hn V _ c r ι B Λ R K hS J hJ, _root_.UpperTheory.V.Hi.dense_of_is_j_unitary_hecke_data P l L Ω s n hn V _ c r ι B Λ R K hS J hJ,
    _root_.UpperTheory.V.Hi.hecke_ideal_point_properties P l L Ω s n hn V _ c r ι B Λ R K hS J hJ, hE.1, hE.2, _root_.UpperTheory.V.Z.Desc.W.twistOk_of_isJ P l L Ω s n hn V _ c r ι B Λ R K hS J hJ⟩,
    _root_.UpperTheory.V.Pa.has_automorphy_of_statement (locP_of P.litN) l L Ω s V c.O n r B J hS (_root_.UpperTheory.V.Hi.level_of_is_j_unitary_hecke_data P l L Ω s n hn V _ c r ι B Λ R K hS J hJ)⟩
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.GaloisCohomology UpperTheory.Top GlobalTheory.Mem.LiteralAutomorphy
namespace UpperTheory.V.HV.Core
open UpperTheory.V.Lit UpperTheory.V.W
theorem of_four_alt (hN : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hK : ∃ CK : ℝ, LemmaK CK) (h1 : CountI) (h2 : CountII) (h3 : CountIII) (h5 : CountV) : VWin := by
  obtain ⟨B, hB⟩ := Win.thmBab_of_lemmaK (_root_.UpperTheory.V.HV.U.pt_s hN) hN.coh.lfK hN.coh.ltK FW.ferreroWashington hK
  obtain ⟨CK, hL⟩ := hK
  exact vwin_of_counts (_root_.UpperTheory.V.HV.U.pt_s hN) hN.coh.lfK hN.coh.ltK hL (hB 401 (by norm_num))
    (Odd.thmBcFree_of (ML.iv (_root_.UpperTheory.V.HV.U.pt_s hN) hN.coh.uo)) h1 h2 h3 h5 (countZ X.propZ)
theorem modU_of_printsH (hH : _root_.UpperTheory.V.Af.HypothesesH') : _root_.UpperTheory.V.W.ModUAlt := _root_.UpperTheory.V.W.modularity_unitary_of_automorphy_hida_unitary hH.litN Pa.pFromAut (_root_.UpperTheory.V.Hi.hida_unitary_of_printed_hida hH)
end UpperTheory.V.HV.Core
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ThFinal
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreOf
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.HV UpperTheory.V.Alg GlobalTheory.GalOfCusp
private theorem ad_eq {H K : Type} [Group H] [CommRing K] {n : ℕ} (ρ : H →* GL (Fin n) K) (g : H) (X : Matrix (Fin n) (Fin n) K) :
    Loc.adGL ρ g X = W.mat ρ g * X * W.mat ρ g⁻¹ := by
  change _ = (ρ g : Matrix (Fin n) (Fin n) K) * X * (ρ g⁻¹ : GL (Fin n) K)
  rw [map_inv]
  rfl
private theorem cont_sub {H K : Type} [Group H] [TopologicalSpace H] [ContinuousInv H] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] {n : ℕ} {a y : H → Matrix (Fin n) (Fin n) K} (ha : Continuous a) (hy : Continuous y)
    (X : Matrix (Fin n) (Fin n) K) : Continuous fun g => y g - (a g * X * a g⁻¹ - X) :=
  hy.sub (((ha.matrix_mul continuous_const).matrix_mul (ha.comp continuous_inv)).sub continuous_const)
theorem UpperTheory.V.Th.core_of_ord_vanishing_two_phi_all :
    _root_.UpperTheory.V.Th.OrdVan2Alt → W.PhiAll → _root_.UpperTheory.V.Th.DenseThresholdMainCase := by
  intro hO hΦ l _ L Ω _ _ _ _ _ _ s V hV _ c _ n h2 h4 r h0 B ι x ρ hN P R hP hR z hz hzo
  obtain ⟨h, hh⟩ := hN.arith
  obtain ⟨hD, -⟩ := Det.redB x ρ hN.rep
  have hfull : Submodule.span (Qbar l) (Set.range (W.mat ρ)) = ⊤ :=
    KStar.Schema.span_eq_top_of_irreducible _ fun N hs => hN.irr N fun g _ => hs g
  have hI := (Ws.Eb.relKill B x ρ hfull hD).2
  obtain ⟨X₀, hpol, hext⟩ := Det.polNorm V.frame ρ P R z hR hz.2
  have heps : ∃ g : V.frame.G₀, V.frame.ε g ≠ 1 := by
    obtain ⟨g, -, hg⟩ := h0.2.2
    refine ⟨g, fun e => hg ?_⟩
    have e' : (V.frame.ε.comp V.frame.η.ker.subtype) g = 1 := e
    rw [W.GFrame.eps, MonoidHom.comp_apply, e', map_one]
  have hdet := regDet V.frame c.O ρ P (by omega) (hΦ l L Ω s V).2.1 heps hN.cont hN.irr hN.n3
  have hno : ∀ (v : W.Vl l L) i j, x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype := by
    intro v i j e
    by_cases hij : i = j
    · subst hij
      have h1 := (s.hA v.1 ((l : ℕ) : 𝓞 (W.Lp L))).2 v.2
      exact Det.epsDec (l := l) (L := L) (Ω := Ω) (s.A v.1) (s.w v.1) (s.hw v.1) ((s.hw v.1 ((l : ℕ) : 𝓞 L)).1 (by simpa only [map_natCast] using h1)) (left_eq_mul.1 e)
    · obtain ⟨g, hg, hf⟩ := hN.free v
      refine hf i j hij 1 one_pos ?_
      have e1 : V.ε (toGS Ω V.S' (W.resP L Ω (Subtype.val g))) = cycZ (W.Lp L) Ω l (W.resP L Ω (Subtype.val g)) :=
        DFunLike.congr_fun V.hε _
      have e2 : cycZ L Ω l (Subtype.val g) = 1 := e1.symm.trans hg
      have e3 : cycBar L Ω l (Subtype.val g) = 1 := by rw [cycBar, MonoidHom.comp_apply, e2, map_one]
      have e4 : x.psi v i g = x.psi v j g * cycBar L Ω l (Subtype.val g) := DFunLike.congr_fun e g
      rw [e3, mul_one] at e4
      simp only [pow_one]
      exact e4
  have hc : Continuous fun g : V.frame.G₀ => W.mat ρ g := Units.continuous_val.comp hN.cont
  refine (hO l L Ω s V c n r B ι x h ρ P hV h2 h4 h0 hh hD hN.cont hN.aut hfull hP hN.unr0 hno hdet
    (fun g => z g - Pa.dY V.frame (W.mat ρ) X₀ g) ⟨?_, fun g g' => ?_, hpol, fun u g hg => ?_, fun v => ?_⟩).elim hext
  · exact cont_sub hc (hz.1.comp continuous_subtype_val) X₀
  · have e1 : z ((g * g' : V.frame.G₀) : V.frame.Γ) = z g + W.mat ρ g * z g' * W.mat ρ g⁻¹ := by
      rw [← ad_eq, ← hR.ad]
      exact hz.2 _ _
    have e2 : W.mat ρ g * W.mat ρ g⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    simp only [e1, Pa.dY, _root_.mul_inv_rev, map_mul]
    noncomm_ring
  · simp only [hzo.ine u g hg, Pa.dY, W.mat, MonoidHom.comp_apply, map_inv, hI u g hg]
    simp
  · obtain ⟨a, X, ha⟩ := hzo.ord v
    refine ⟨a⁻¹, X - X₀, fun g => ?_⟩
    obtain ⟨a1, a2, a3, a4⟩ := ha g
    have e : z (V.frame.φ v g) - Pa.dY V.frame (W.mat ρ) X₀ (V.frame.φ v g) - Pa.dY V.frame (W.mat ρ) (X - X₀) (V.frame.φ v g) =
        z (V.frame.φ v g) - (Loc.adGL (ρ.comp (V.frame.φ v)) g X - X) := by
      rw [ad_eq]
      have e1 : ∀ t, W.mat (ρ.comp (V.frame.φ v)) t = W.mat ρ (V.frame.φ v t) := fun _ => rfl
      simp only [Pa.dY, e1, map_inv]
      noncomm_ring
    rw [inv_inv, e]
    exact ⟨a1, a2, a3, a4⟩
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AdLOf
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.HV GlobalTheory.GalOfCusp UpperTheory.V.Th
private theorem adL_conj {C G V : Type} [CommRing C] [Group G] [AddCommGroup V] [Module C V] (ρ : Representation C G V)
    (c : G → V) (hc : ∀ g h, c (g * h) = c g + ρ g (c h)) (γ g : G) :
    c g = ρ γ (c (γ⁻¹ * g * γ)) + c γ - ρ g (c γ) := by
  have h1 := hc γ (γ⁻¹ * g * γ)
  rw [← mul_assoc, mul_inv_cancel_left, hc] at h1
  rw [eq_sub_iff_add_eq, h1, add_comm]
private theorem adL_rho {C G V : Type} [CommRing C] [Group G] [AddCommGroup V] [Module C V] (ρ : Representation C G V)
    (γ g : G) (x : V) : ρ γ (ρ (γ⁻¹ * g * γ) x) = ρ g (ρ γ x) := by
  rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel_left, map_mul, Module.End.mul_apply]
private theorem adL_emb {F Ω K : Type} [Field F] [Field Ω] [Field K] [CharZero F] [Algebra F Ω] [IsAlgClosure F Ω]
    (j j₀ : Ω →+* K) (h : j₀.comp (algebraMap F Ω) = j.comp (algebraMap F Ω)) :
    ∃ γ : Ω ≃ₐ[F] Ω, ∀ y, j (γ y) = j₀ y := by
  letI : Algebra F K := (j.comp (algebraMap F Ω)).toAlgebra
  letI : Algebra Ω K := j.toAlgebra
  haveI : IsScalarTower F Ω K := IsScalarTower.of_algebraMap_eq' rfl
  let f : Ω →ₐ[F] K := { j₀ with commutes' := fun x => RingHom.congr_fun h x }
  exact ⟨f.restrictNormal' Ω, fun y => f.restrictNormal_commutes Ω y⟩
private theorem adL_above {F Ω : Type} [Field F] [NumberField F] [Field Ω] [CharZero Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime] (j : Ω →+* Formalism.BasicNotions.Loc.Om l) {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (φ : H →* Formalism.BasicNotions.Loc.GQ l) (ψ : H →* G F Ω) (hφ : Topology.IsOpenEmbedding φ) (hψ : Continuous ψ)
    (hj : ∀ h y, φ h (j y) = j (ψ h y))
    {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] (ρ : Representation C (G F Ω) V)
    (c : G F Ω → V) (hc : c ∈ Z1 ρ) (hb : Af.IsBK l ρ c) : (fun h => c (ψ h)) ∈ Loc.finiteCocycles φ (ρ.comp ψ) := by
  obtain ⟨j₀, hj₀, h0⟩ := hb.above (j.comp (algebraMap F Ω))
  obtain ⟨γ, hγ⟩ := adL_emb j j₀ hj₀
  let ψ' : H →* G F Ω := (MulAut.conj (γ⁻¹ : G F Ω)).toMonoidHom.comp ψ
  have hψ' : ∀ h, ψ' h = γ⁻¹ * ψ h * γ := fun h => by simp [ψ']
  obtain ⟨-, x, hx⟩ := (Loc.bkAbove (F := F) j₀ φ ψ' hφ (fun h y => by
    rw [← hγ, hj, ← hγ, hψ']
    simp) ρ c hc).2 h0
  refine ⟨⟨hc.1.comp hψ, fun g h => (congrArg c (map_mul ψ g h)).trans (hc.2 _ _)⟩,
    TensorProduct.AlgebraTensorModule.map (ρ γ) LinearMap.id x - c γ ⊗ₜ[ℚ_[l]] 1, fun h => ?_⟩
  have e : ∀ w, TensorProduct.AlgebraTensorModule.map (ρ γ) LinearMap.id (Loc.actC φ (ρ.comp ψ') h w) =
      Loc.actC φ (ρ.comp ψ) h (TensorProduct.AlgebraTensorModule.map (ρ γ) LinearMap.id w) := fun w => by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      simp only [Loc.actC, TensorProduct.AlgebraTensorModule.map_tmul, MonoidHom.comp_apply, hψ', adL_rho, LinearMap.id_apply]
    | add u v hu hv => simp only [map_add (f := _), hu, hv]
  have h2 := congrArg (TensorProduct.AlgebraTensorModule.map (ρ γ) LinearMap.id) (hx h)
  rw [map_sub, e, TensorProduct.AlgebraTensorModule.map_tmul] at h2
  have h3 : Loc.actC φ (ρ.comp ψ) h (c γ ⊗ₜ[ℚ_[l]] 1) = ρ (ψ h) (c γ) ⊗ₜ[ℚ_[l]] 1 := by simp [Loc.actC]
  change c (ψ h) ⊗ₜ[ℚ_[l]] _ = _
  rw [adL_conj ρ c hc.2 γ (ψ h), TensorProduct.sub_tmul, TensorProduct.add_tmul, map_sub, h3]
  simp only [LinearMap.id_apply, hψ'] at h2
  rw [h2]
  abel
open scoped Pointwise in
private theorem adL_ine {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {A : ValuationSubring Ω} (γ : G F Ω)
    {g : G F Ω} (hg : g ∈ Ine (F := F) (γ • A)) : γ⁻¹ * g * γ ∈ Ine (F := F) A := by
  have m : ∀ y : Ω, γ y ∈ γ • A ↔ y ∈ A := fun y => ValuationSubring.smul_mem_pointwise_smul_iff (g := γ)
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 : g • γ • A = γ • A := hg.1
    change (γ⁻¹ * g * γ) • A = A
    rw [mul_smul, mul_smul, h1, inv_smul_smul]
  · have h2 := hg.2 (γ x) (by rwa [ValuationSubring.valuation_le_one_iff, m, ← ValuationSubring.valuation_le_one_iff])
    have e : g (γ x) - γ x = γ ((γ⁻¹ * g * γ) x - x) := by simp
    rwa [e, valuation_lt_one_iff', m, ← map_inv₀, m, map_eq_zero_iff _ γ.injective, ← valuation_lt_one_iff'] at h2
private theorem adL_away {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {l : ℕ} [Fact l.Prime]
    {C V : Type} [CommRing C] [Algebra ℚ_[l] C] [AddCommGroup V] [Module C V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] C V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul C V] (ρ : Representation C (G F Ω) V)
    (c : G F Ω → V) (hc : c ∈ Z1 ρ) (hb : Af.IsBK l ρ c) (w : HeightOneSpectrum (𝓞 F)) (hw : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal)
    (A : ValuationSubring Ω) (hA : IsPlaceOver A w) : ∃ x : V, ∀ g ∈ Ine (F := F) A, c g = ρ g x - x := by
  obtain ⟨A₀, hA₀, x, hx⟩ := hb.away w hw
  obtain ⟨γ, rfl⟩ := exists_smul_eq_of_isPlaceOver (F := F) hA₀ hA
  refine ⟨ρ γ x - c γ, fun g hg => ?_⟩
  rw [adL_conj ρ c hc.2 γ g, hx _ (adL_ine γ hg), map_sub, adL_rho, map_sub]
  abel
private theorem adL_pr {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} (V : s.Lev) : Function.Surjective V.pr := fun g => by
  obtain ⟨τ, hτ⟩ : ∃ τ, toGS Ω V.S' τ = g.1 := QuotientGroup.mk_surjective g.1
  obtain ⟨σ, rfl⟩ := (V.hη τ).1 (by rw [hτ]; exact g.2)
  exact ⟨σ, Subtype.ext hτ⟩
private theorem adL_desc {n : ℕ} {A G H : Type} [CommRing A] [Group G] [Group H] (D : W.GDet n A G) (φ : H →* G)
    (hφ : Function.Surjective φ) (ρ : G →* GL (Fin n) A) (hD : D.comap φ = W.GDet.ofRep (W.mat (ρ.comp φ))) :
    D = W.GDet.ofRep (W.mat ρ) := by
  refine CA.d_gext _ _ fun g i _ _ => ?_
  obtain ⟨h, rfl⟩ := hφ g
  have e : (D.comap φ).chi (MonoidAlgebra.single h 1) = D.chi (MonoidAlgebra.single (φ h) 1) := by
    change D.D A[X] (MonoidAlgebra.mapDomainRingHom A[X] φ _) = D.D A[X] _
    congr 1
    rw [map_sub]
    simp
  unfold W.GDet.lam
  rw [← e, hD, (AlgebraTools.Det.repApi _).2.1, (AlgebraTools.Det.repApi _).2.1]
  rfl
private theorem adL_triv {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] {s : W.HidaSetting l L Ω} {V : s.Lev} {c : Coef l} {n : ℕ} {r : W.Resid V.frame c.O n} {B : W.UniversalOrdinaryDeterminantRing r}
    {ι : Qbar l ≃+* ℂ} {x : B.Pt} {ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)} (H : _root_.UpperTheory.V.Th.AutomorphicPointLocallyGeneric ι x ρ) :
    ∀ u, ∀ g ∈ r.Ip u, ρ g = 1 :=
  (Ws.Eb.relKill B x ρ ((AlgebraTools.Det.irrIffSpan (W.mat ρ)).1 fun N hN => H.irr N fun g _ v hv => hN g v hv)
    (adL_desc x.D V.pr (adL_pr V) ρ H.rep)).2
theorem UpperTheory.V.Th.adjointLiftingTheorem_of_locPrints_of_core :
    Loc.LocalPublishedTheorems → _root_.UpperTheory.V.Th.DenseThresholdMainCase → _root_.UpperTheory.V.Th.AdjointLiftingTheorem := by
  intro hP hC l _ L Ω _ _ _ _ _ _ s V hS hζ c hL n hn hn' r hr B ι x ρ H hpar P R hform hR z hz hb
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap L Ω).injective
  have hz' : (fun g => z (toGS Ω V.S' g)) ∈ Z1 (R.comp (toGS Ω V.S') :
      Representation (Qbar l) (G (W.Lp L) Ω) (Matrix (Fin n) (Fin n) (Qbar l))) :=
    ⟨hz.1.comp (continuous_toGS Ω _), fun g h => (congrArg z (map_mul _ g h)).trans (hz.2 _ _)⟩
  have he : V.frame.eps c.O (Qbar l) = V.frame.eps ℤ_[l] (Qbar l) := by
    unfold W.GFrame.eps
    rw [← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  refine hC l L Ω s V hS hζ c hL n hn hn' r hr B ι x ρ H P R (fun g => he ▸ hform g) hR z hz ⟨fun u g hg => ?_, fun v => ?_⟩
  · obtain ⟨X, hX⟩ := adL_away _ _ hz' hb u.1 (s.St_l u.1 u.2) (s.A u.1) (s.hA u.1)
    have h1 := adL_triv H u g hg
    obtain ⟨g', hg', rfl⟩ := hg.1
    have h2 := hX (W.resP L Ω g') hg'
    have h3 : ∀ g : V.frame.G₀, ρ g = 1 → Loc.adGL ρ g X = X := fun g h => by simp [Loc.adGL, h]
    exact h2.trans (sub_eq_zero.2 ((hR.ad (V.pr g') X).trans (h3 _ h1)))
  · obtain ⟨j, hj⟩ := (Loc.decEmb (F := W.Lp L) (Ω := Ω) (v := l)).1 (s.A v.1) v.1 (s.hA v.1) v.2
    have key : ∃ φ : ↥(Dec (F := L) (s.A v.1)) →* Formalism.BasicNotions.Loc.GQ l, Topology.IsOpenEmbedding φ ∧
        (∀ g y, φ g (j y) = j ((g : G L Ω) y)) ∧ (∀ g, φ g ∈ Loc.Iq l ↔ (g : G L Ω) ∈ Ine (F := L) (s.A v.1)) ∧
        (∀ g, Loc.cyc l l (φ g) = cycZ L Ω l (g : G L Ω)) := by
      rw [← hj]
      obtain ⟨φ, a, b, -, c, d, -⟩ := ((Loc.decEmb (F := L) (Ω := Ω) (v := l)).2 j).2
      exact ⟨φ, a, b, c, d l⟩
    obtain ⟨φ, a, b, hi, d⟩ := key
    have d' : ∀ g, Loc.cycA l l (Qbar l) (φ g) = cycBar L Ω l (g : G L Ω) := fun g => congrArg (Units.map _) (d g)
    have h3 := adL_above (F := W.Lp L) j φ ((W.resP L Ω).comp (Dec (F := L) (s.A v.1)).subtype) a
      (W.continuous_resP.comp continuous_subtype_val) b _ _ hz' hb
    have e : ((R.comp (toGS Ω V.S')).comp ((W.resP L Ω).comp (Dec (F := L) (s.A v.1)).subtype) :
        Representation (Qbar l) (Dec (F := L) (s.A v.1)) (Matrix (Fin n) (Fin n) (Qbar l))) =
        Loc.adGL (ρ.comp (V.frame.φ v)) :=
      MonoidHom.ext fun g => LinearMap.ext fun X => hR.ad (V.frame.φ v g) X
    rw [e] at h3
    obtain ⟨m, k, hm, hk, hψ⟩ := hpar v
    obtain ⟨g₀, hg₀, hf⟩ := H.free v
    have hI : V.frame.Iv v = (Loc.Iq l).comap φ := Subgroup.ext fun g => (hi g).symm
    rw [hI]
    haveI : CompactSpace (Dec (F := L) (s.A v.1)) := V.frame.cv v
    refine bkOrd hP l (Dec (F := L) (s.A v.1)) φ a n _ _ m k (H.cont.comp (V.frame.φ_cont v)) (H.flag v) hm hk
      (fun i i' g hg => ?_) ⟨g₀, ?_, hf⟩ _ h3
    · rw [d']
      exact hψ i i' g ((hi g).1 hg)
    · have h4 : cycZ (W.Lp L) Ω l (W.resP L Ω g₀.1) = 1 := by
        rw [← V.hε]
        exact hg₀
      have h5 : Loc.cyc l l (φ g₀) = 1 := (d g₀).trans h4
      exact (congrArg (Units.map _) h5).trans (map_one _)
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.Top UpperTheory.V.HV
namespace UpperTheory.V.Th
theorem core_alt_bis (hH : _root_.UpperTheory.V.Af.HypothesesH') (hC : Pa.CohP) : _root_.UpperTheory.V.Th.DenseThresholdMainCase := _root_.UpperTheory.V.Th.core_of_ord_vanishing_two_phi_all (_root_.UpperTheory.V.Th.ordinary_vanishing_two_of_printed_hida hH) (W.phiAll hC)
theorem adjoint_lifting_of_cohomology (hH : _root_.UpperTheory.V.Af.HypothesesH') (hC : Pa.CohP) : _root_.UpperTheory.V.Th.AdjointLiftingTheorem := _root_.UpperTheory.V.Th.adjointLiftingTheorem_of_locPrints_of_core (_root_.UpperTheory.V.HV.U.locPrints_of_litN hH.litN) (_root_.UpperTheory.V.Th.core_alt_bis hH hC)
end UpperTheory.V.Th
end
end
