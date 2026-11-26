module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevel
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSmulOfDecoEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization
noncomputable section

open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit
open Filter Topology

namespace GlobalTheory.HeckeSplit

variable {L : Type} [Field L] [NumberField L]

theorem eventually_unrAt (χ : Ideles L →* ℂˣ) (hχ : Continuous χ) :
    ∀ᶠ v in Filter.cofinite, UnrAt χ v := by
  have h : ∀ v : HeightOneSpectrum (𝓞 L), ∃ x : (v.adicCompletion L)ˣ,
      Valued.v (x : v.adicCompletion L) = 1 ∧
      (‖((χ (localIdele L v x) : ℂˣ) : ℂ) - 1‖ < 1 / 2 → UnrAt χ v) := fun v => by
    by_contra hc
    push Not at hc
    refine (hc 1 (map_one _)).2 fun x hx => Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]
    refine (hc _ ?_).1
    rw [Units.val_pow_eq_pow_val, map_pow, hx, one_pow]
  choose x hx hx' using h
  have hc : Continuous fun a : Ideles L => ‖((χ a : ℂˣ) : ℂ) - 1‖ :=
    ((Units.continuous_val.comp hχ).sub continuous_const).norm
  have h0 : Tendsto (fun v => localIdele L v (x v)) cofinite (𝓝 1) :=
    GlobalTheory.Mem.UnrAe.tendsto_localIdele x hx
  have h1 := (hc.tendsto 1).comp h0
  have h2 := h1.eventually_lt_const (u := 1 / 2) (by simp)
  exact h2.mono fun v hv => hx' v hv

theorem exists_level (χ : Ideles L →* ℂˣ) (hχ : Continuous χ) (v : HeightOneSpectrum (𝓞 L)) :
    ∃ n : ℕ, ∀ x : (v.adicCompletion L)ˣ,
      Valued.v ((x : v.adicCompletion L) - 1) ≤ WithZero.exp (-(n : ℤ)) → χ (localIdele L v x) = 1 := by
  have hc : Continuous fun a : (v.adicCompletion L)ˣ => ‖((χ (localIdele L v a) : ℂˣ) : ℂ) - 1‖ :=
    ((Units.continuous_val.comp (hχ.comp (GlobalTheory.Mem.UnrAe.continuous_localIdele v))).sub
      continuous_const).norm
  have h0 : {a : (v.adicCompletion L)ˣ | ‖((χ (localIdele L v a) : ℂˣ) : ℂ) - 1‖ < 1 / 2} ∈ 𝓝 1 :=
    (isOpen_lt hc continuous_const).mem_nhds (by simp)
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_comap] at h0
  obtain ⟨t, ht, hsub⟩ := h0
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.mp ht
  have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  refine ⟨(1 - WithZero.log (MonoidWithZeroHom.ValueGroup₀.embedding γ.1)).toNat + 1, fun x hx1 => ?_⟩
  have hlt : Valued.v ((x : v.adicCompletion L) - 1) < 1 := by
    refine hx1.trans_lt ?_
    rw [← WithZero.exp_zero]
    exact WithZero.exp_lt_exp.mpr (by omega)
  have hx' : Valued.v (x : v.adicCompletion L) = 1 := by
    have := Valuation.map_one_add_of_lt _ hlt
    simpa using this
  refine Units.ext (GlobalTheory.CharConductor.eq_one_of_pow_near_one fun m => ?_)
  rw [← Units.val_pow_eq_pow_val, ← map_pow, ← map_pow]
  apply hsub
  apply hγ
  simp only [Set.mem_ofPred_eq, Valuation.restrict_lt_iff_lt_embedding, Units.val_pow_eq_pow_val, Units.val_one]
  have h1 : Valued.v ((x : v.adicCompletion L) ^ m - 1) ≤ Valued.v ((x : v.adicCompletion L) - 1) := by
    induction m with
    | zero => simp
    | succ m ih =>
      have e : (x : v.adicCompletion L) ^ (m + 1) - 1 = x ^ m * (x - 1) + (x ^ m - 1) := by ring
      rw [e]
      refine Valuation.map_add_le _ ?_ ih
      rw [map_mul, map_pow, hx', one_pow, one_mul]
  refine (h1.trans hx1).trans_lt ?_
  conv_rhs => rw [← WithZero.exp_log hγ0]
  exact WithZero.exp_lt_exp.mpr (by omega)

def truncIdele (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L))) : Ideles L :=
  infIdele L (infPart L x) * ∏ v ∈ T, localIdele L v (finPart L v x)

theorem truncIdele_inv (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L))) :
    truncIdele x⁻¹ T = (truncIdele x T)⁻¹ := by
  simp only [truncIdele, map_inv, Finset.prod_inv_distrib, ← mul_inv]

open Classical in
theorem finPart_truncIdele (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L)))
    (v : HeightOneSpectrum (𝓞 L)) :
    finPart L v (truncIdele x T) = if v ∈ T then finPart L v x else 1 := by
  rw [truncIdele, map_mul, finPart_infIdele, one_mul, map_prod]
  split_ifs with h
  · rw [Finset.prod_eq_single_of_mem v h fun w _ hw => finPart_localIdele_ne L hw.symm _,
      finPart_localIdele]
  · exact Finset.prod_eq_one fun w hw => finPart_localIdele_ne L (v := w) (w := v) (fun e => h (by rw [e]; exact hw)) _

theorem infPart_truncIdele (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L))) :
    infPart L (truncIdele x T) = infPart L x := by
  rw [truncIdele, map_mul, infPart_infIdele, map_prod,
    Finset.prod_eq_one fun v _ => infPart_localIdele L v _, mul_one]

theorem coe_truncIdele (x : Ideles L) (T : Finset (HeightOneSpectrum (𝓞 L))) :
    ((truncIdele x T : Ideles L) : AdeleRing (𝓞 L) L) =
      ((x : AdeleRing (𝓞 L) L).1, GlobalTheory.HeckeProduct.cut (x : AdeleRing (𝓞 L) L).2 T) := by
  classical
  refine Prod.ext ?_ (Subtype.ext (funext fun v => ?_))
  · exact congrArg (fun u : (InfiniteAdeleRing L)ˣ => (u : InfiniteAdeleRing L)) (infPart_truncIdele x T)
  · have h := congrArg (fun u : (v.adicCompletion L)ˣ => (u : v.adicCompletion L))
      (finPart_truncIdele x T v)
    refine h.trans ?_
    by_cases hv : v ∈ T
    · simp only [hv, if_true]; exact (if_pos hv).symm
    · simp only [hv, if_false]; exact (if_neg hv).symm

theorem tendsto_truncIdele (x : Ideles L) :
    Tendsto (truncIdele x) atTop (𝓝 x) := by
  have h : ∀ x : Ideles L, Tendsto (fun T => ((truncIdele x T : Ideles L) : AdeleRing (𝓞 L) L))
      atTop (𝓝 (x : AdeleRing (𝓞 L) L)) := fun x => by
    simp only [coe_truncIdele]
    exact tendsto_const_nhds.prodMk_nhds (GlobalTheory.HeckeProduct.tendsto_cut _)
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  refine (h x).prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp ?_)
  have h2 := h x⁻¹
  simp only [truncIdele_inv] at h2
  exact h2

theorem char_eq_prod_local (χ : Ideles L →* ℂˣ) (hχ : Continuous χ) (x : Ideles L)
    (S : Finset (HeightOneSpectrum (𝓞 L)))
    (hS : ∀ v ∉ S, χ (localIdele L v (finPart L v x)) = 1) :
    χ x = χ (infIdele L (infPart L x)) * ∏ v ∈ S, χ (localIdele L v (finPart L v x)) := by
  classical
  have h1 := (hχ.tendsto x).comp (tendsto_truncIdele x)
  refine tendsto_nhds_unique h1 (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_ge_atTop S] with T hT
  change _ = χ (truncIdele x T)
  rw [truncIdele, map_mul, map_prod]
  congr 1
  exact Finset.prod_subset hT fun v _ hv => hS v hv

theorem continuous_char_factor : ∀ (L : Type) [Field L] [NumberField L] (χ : Ideles L →* ℂˣ), Continuous χ → (∀ᶠ v in Filter.cofinite, UnrAt χ v) ∧ (∀ v : HeightOneSpectrum (𝓞 L), ∃ n : ℕ, ∀ x : (v.adicCompletion L)ˣ, Valued.v ((x : v.adicCompletion L) - 1) ≤ WithZero.exp (-(n : ℤ)) → χ (localIdele L v x) = 1) ∧ ∀ (x : Ideles L) (S : Finset (HeightOneSpectrum (𝓞 L))), (∀ v ∉ S, χ (localIdele L v (finPart L v x)) = 1) → χ x = χ (infIdele L (infPart L x)) * ∏ v ∈ S, χ (localIdele L v (finPart L v x)) :=
  fun _ _ _ χ hχ => ⟨eventually_unrAt χ hχ, exists_level χ hχ, fun x S hS => char_eq_prod_local χ hχ x S hS⟩

end GlobalTheory.HeckeSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorizationStatement
open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_ideleChar_local_factorization : ∀ (L : Type) [Field L] [NumberField L] (χ : Ideles L →* ℂˣ), Continuous χ → (∀ᶠ v in Filter.cofinite, UnrAt χ v) ∧ (∀ v : HeightOneSpectrum (𝓞 L), ∃ n : ℕ, ∀ x : (v.adicCompletion L)ˣ, Valued.v ((x : v.adicCompletion L) - 1) ≤ WithZero.exp (-(n : ℤ)) → χ (localIdele L v x) = 1) ∧ ∀ (x : Ideles L) (S : Finset (HeightOneSpectrum (𝓞 L))), (∀ v ∉ S, χ (localIdele L v (finPart L v x)) = 1) → χ x = χ (infIdele L (infPart L x)) * ∏ v ∈ S, χ (localIdele L v (finPart L v x)) := by
  first | exact @GlobalTheory.HeckeSplit.continuous_char_factor | exact GlobalTheory.HeckeSplit.continuous_char_factor | (intros; apply GlobalTheory.HeckeSplit.continuous_char_factor <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentat
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentat
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
open Module TensorProduct

noncomputable section

namespace GlobalTheory.HTW.Rec

section Transport

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem finrank_eq_of_equiv_tensor {C : Type} [AddCommGroup C] [Module Qp C] (e : V ≃ₗ[LL] V')
    (S : Submodule LL (V ⊗[Qp] C)) (S' : Submodule LL (V' ⊗[Qp] C))
    (a : ∀ x ∈ S, SumJumps.ext1 Qp C e.toLinearMap x ∈ S')
    (b : ∀ x ∈ S', SumJumps.ext1 Qp C e.symm.toLinearMap x ∈ S) :
    finrank LL S = finrank LL S' := by
  have h1 : ∀ x : V ⊗[Qp] C, SumJumps.ext1 Qp C e.symm.toLinearMap
      (SumJumps.ext1 Qp C e.toLinearMap x) = x := by
    intro x
    rw [SumJumps.ext1_comp_ext1]
    convert SumJumps.ext1_id (LL := LL) x
    ext v; simp
  have h2 : ∀ x : V' ⊗[Qp] C, SumJumps.ext1 Qp C e.toLinearMap
      (SumJumps.ext1 Qp C e.symm.toLinearMap x) = x := by
    intro x
    rw [SumJumps.ext1_comp_ext1]
    convert SumJumps.ext1_id (LL := LL) x
    ext v; simp
  refine LinearEquiv.finrank_eq (LinearEquiv.ofLinear
    ((SumJumps.ext1 Qp C e.toLinearMap).restrict a)
    ((SumJumps.ext1 Qp C e.symm.toLinearMap).restrict b) ?_ ?_)
  · ext x
    simp [LinearMap.restrict_apply, h2]
  · ext x
    simp [LinearMap.restrict_apply, h1]

variable {ρ : Representation LL G V} {ρ' : Representation LL G V'}

theorem symm_equivariant (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (g : G) (v : V') :
    e.symm.toLinearMap (ρ' g v) = ρ g (e.symm.toLinearMap v) := by
  apply e.injective
  rw [he]
  simp

theorem finrank_dcris_eq_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v)) :
    finrank LL (Dcris PD ρ) = finrank LL (Dcris PD ρ') :=
  finrank_eq_of_equiv_tensor e _ _ (SumJumps.dcris_map PD e.toLinearMap he)
    (SumJumps.dcris_map PD e.symm.toLinearMap (symm_equivariant e he))

theorem finrank_fildR_eq_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v))
    (τ : K →ₐ[Qp] LL) (a : ℤ) :
    finrank LL (FildR PD ρ τ a) = finrank LL (FildR PD ρ' τ a) :=
  finrank_eq_of_equiv_tensor e _ _ (SumJumps.fildR_map PD e.toLinearMap he τ a)
    (SumJumps.fildR_map PD e.symm.toLinearMap (symm_equivariant e he) τ a)

theorem multV_eq_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v))
    (τ : K →ₐ[Qp] LL) (a : ℤ) : multV PD ρ τ a = multV PD ρ' τ a := by
  simp only [multV, finrank_fildR_eq_of_equiv PD e he]

theorem isCrys_of_equiv (e : V ≃ₗ[LL] V') (he : ∀ g v, e (ρ g v) = ρ' g (e v))
    (h : IsCrys PD ρ') : IsCrys PD ρ := by
  unfold IsCrys at h ⊢
  rw [finrank_dcris_eq_of_equiv PD e he, h, e.finrank_eq]

end Transport

theorem isCrys_multV_of_isMatRep {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (T : Lat K LL) {r : ℕ}
    (M : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1) (h : IsMatRep T M) :
    (IsCrys (P.PD K) (matRep M) → IsCrys (P.PD K) T.ρ) ∧
      ∀ τ u, multV (P.PD K) T.ρ τ u = multV (P.PD K) (matRep M) τ u := by
  obtain ⟨e, he⟩ := h
  have he' : ∀ g v, e (T.ρ g v) = matRep M g (e v) := by
    intro g v
    rw [he]
    simp [matRep, Matrix.toLinAlgEquiv'_apply]
  exact ⟨isCrys_of_equiv _ e he', fun τ u => multV_eq_of_equiv _ e he' τ u⟩

end GlobalTheory.HTW.Rec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsCrystallineJumpsOfIsIsoMatrixGaloisRepresentatStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCrystalline_jumps_of_isIsoMatrixGaloisRepresentation : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (T : Lat K LL) {r : ℕ} (M : ↥(GK K) →* Matrix (Fin r) (Fin r) ↥LL.1), IsMatRep T M → (IsCrys (P.PD K) (matRep M) → IsCrys (P.PD K) T.ρ) ∧ ∀ τ u, multV (P.PD K) T.ρ τ u = multV (P.PD K) (matRep M) τ u := by
  first | exact @GlobalTheory.HTW.Rec.isCrys_multV_of_isMatRep | exact GlobalTheory.HTW.Rec.isCrys_multV_of_isMatRep | (intros; apply GlobalTheory.HTW.Rec.isCrys_multV_of_isMatRep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodCoefficientRingIntegersPadicFiniteExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodCoefficientRingIntegersPadicFiniteExtension
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem goodO_finExt_integers :
    ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) :=
  GlobalTheory.Pass.goodO_ringOfIntegers

end GlobalTheory.HTW.Rec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodCoefficientRingIntegersPadicFiniteExtensionStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodCoefficientRing_integers_padicFiniteExtension : ∀ (l : ℕ) [Fact l.Prime] (LL : FinExt l), GoodO (Qp := ℚ_[l]) ↥LL.1 ↥(OL LL) := by
  first | exact @GlobalTheory.HTW.Rec.goodO_finExt_integers | exact GlobalTheory.HTW.Rec.goodO_finExt_integers | (intros; apply GlobalTheory.HTW.Rec.goodO_finExt_integers <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLetterEqPageWord
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLetterEqPageWord
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem recWord_letter_eq_pageWord : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ ψ : D.R.GG),
    Roomy L C → ∀ a : ZMod (orderOf ψ),
    (((recWord L j ε (letter τ ψ)).sz a : ℕ) : ℤ) = (pageWord L j ε τ ψ).sz a ∧
    (recWord L j ε (letter τ ψ)).Mi a = (pageWord L j ε τ ψ).Mi a ∧
    (recWord L j ε (letter τ ψ)).hi a = (pageWord L j ε τ ψ).hi a ∧
    (ThickN (bHat L) (etaHat L) (recWord L j ε (letter τ ψ)).sz a ↔ (pageWord L j ε τ ψ).thick a) := by
  intro D L C j ε τ ψ hR a
  have hB := GlobalTheory.T.twistedDualOrbitPageWord_box L C j ε τ ψ hR
  have hpos : (etaHat L : ℤ) < szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a)) := hB.2.2.2.2.2 a
  have h0 : 0 ≤ szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a)) := by omega
  have hc : ((szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a))).toNat : ℤ) =
      szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a)) := Int.toNat_of_nonneg h0
  have hS : (szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a)) + (sHat L : ℤ)).toNat =
      (szT (hcAt D (letter τ ψ a)) j (pos ε (letter τ ψ a))).toNat + sHat L := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact hc
  · simp only [recWord, pageWord, WordData.Mi, hS]
  · simp only [recWord, pageWord, WordData.hi, hS]
  · simp only [ThickN, recWord, pageWord, WordData.thick]
    omega

end GlobalTheory.HTW.Rec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualSizeWordLetterEqPageWordStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualSizeWord_letter_eq_pageWord : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (ε : ℤˣ) (τ ψ : D.R.GG), Roomy L C → ∀ a : ZMod (orderOf ψ), (((recWord L j ε (letter τ ψ)).sz a : ℕ) : ℤ) = (pageWord L j ε τ ψ).sz a ∧ (recWord L j ε (letter τ ψ)).Mi a = (pageWord L j ε τ ψ).Mi a ∧ (recWord L j ε (letter τ ψ)).hi a = (pageWord L j ε τ ψ).hi a ∧ (ThickN (bHat L) (etaHat L) (recWord L j ε (letter τ ψ)).sz a ↔ (pageWord L j ε τ ψ).thick a) := by
  first | exact @GlobalTheory.HTW.Rec.recWord_letter_eq_pageWord | exact GlobalTheory.HTW.Rec.recWord_letter_eq_pageWord | (intros; apply GlobalTheory.HTW.Rec.recWord_letter_eq_pageWord <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThickLetterWordHypothesesOfCommonConditions
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThickLetterWordHypothesesOfCommonConditions
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.RecS

theorem setting_of_wordBase : ∀ {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : NWord (RecS.nLet i w hw)), D.nd.l i ≠ 2 → RecS.WordBase L HW i r ρ π w hw Cx hG Wd → RecS.ThickLetterWordLatticeSurjectionHypotheses HW i r ρ π w hw Cx hG Wd := by
  intro D L HW i r ρ π w hw Cx hG Wd hl hB _ft T₁ T₂ F h1 h2 hF
  obtain ⟨ht1c, ht1w, ht1l⟩ := hB.t1 T₁ h1
  obtain ⟨ht2c, ht2low⟩ := hB.t2 T₂ h2
  refine ⟨⟨⟨?_, ?_⟩, ?_, ?_⟩, ⟨ht1c, ht2c, hF⟩, hB.small.1.2.2.2.2.2, ?_, fun a => ht2low _ft a, ?_, ht1l⟩
  · intro x y hxy
    have hv : ((algebraMap ↥(Loc.K0 (D.nbr i w hw).Kw) ↥(D.nbr i w hw).Kw.1 x : ↥(D.nbr i w hw).Kw.1) : Loc.Om (D.nd.l i)) =
        ((algebraMap ↥(Loc.K0 (D.nbr i w hw).Kw) ↥(D.nbr i w hw).Kw.1 y : ↥(D.nbr i w hw).Kw.1) : Loc.Om (D.nd.l i)) := by rw [hxy]
    exact Subtype.ext hv
  · intro y
    exact ⟨⟨y.1, show y.1 ∈ Loc.K0 (D.nbr i w hw).Kw from ⟨y.2, hB.unram y.2⟩⟩, Subtype.ext rfl⟩
  · exact (HW _).W_s _ 1 _ hG
  · rw [(D.loc _).PD_p]; exact hl
  · intro a
    have hw' := ht1w a
    have e : Wd.win a = (if Wd.up a then
        Set.Icc (Wd.sz a : ℤ) ((Wd.sz a : ℤ) + Wd.S) ∪ Set.Icc (-(Wd.η : ℤ)) Wd.η
      else Set.Icc (-(Wd.sz a : ℤ) - Wd.S) (-(Wd.sz a : ℤ)) ∪ Set.Icc (-(Wd.η : ℤ)) Wd.η) := by
      unfold NWord.win
      cases h : Wd.up a <;> ext u <;> simp [abs_le]
    rw [← e]; exact hw'
  · intro a ha
    rcases hB.num.thick_or a with h | h
    · exact absurd h ha
    · exact h

end GlobalTheory.HTW.RecS
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThickLetterWordHypothesesOfCommonConditionsStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thickLetterWord_hypotheses_of_common_conditions : ∀ {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : NWord (RecS.nLet i w hw)), D.nd.l i ≠ 2 → RecS.WordBase L HW i r ρ π w hw Cx hG Wd → RecS.ThickLetterWordLatticeSurjectionHypotheses HW i r ρ π w hw Cx hG Wd := by
  first | exact @GlobalTheory.HTW.RecS.setting_of_wordBase | exact GlobalTheory.HTW.RecS.setting_of_wordBase | (intros; apply GlobalTheory.HTW.RecS.setting_of_wordBase <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingReadsGaloisElement
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingReadsGaloisElement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem existsUnique_reads : ∀ {R : Ranks} (H : Host R) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (c : H.E →+* ↥K.1) (κ : H.E →+* ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1), ∃! g : R.GG, Reads H c κ τ g := by
  intro R H l _ K LL c κ τ
  haveI : IsGalois ℚ H.E := H.hostE_isGalois
  obtain ⟨σ, hσ⟩ := GlobalTheory.HTW.exists_aut_comp_eq_of_normal κ ((τ : ↥K.1 →+* ↥LL.1).comp c)
  obtain ⟨g, hg⟩ := (H.gal).symm.surjective σ
  have hg' : H.sigmaOf g = σ := hg
  refine ⟨g, fun x => ?_, fun g' hg2 => ?_⟩
  · rw [hg']
    exact hσ x
  · have e : H.sigmaOf g' = H.sigmaOf g := by
      refine AlgEquiv.ext fun x => ?_
      apply κ.injective
      rw [← hg2 x, hg']
      exact hσ x
    exact (H.gal).symm.injective e

end GlobalTheory.HTW.Rec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingReadsGaloisElementStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_embeddingReadsGaloisElement : ∀ {R : Ranks} (H : Host R) {l : ℕ} [Fact l.Prime] (K LL : FinExt l) (c : H.E →+* ↥K.1) (κ : H.E →+* ↥LL.1) (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1), ∃! g : R.GG, Reads H c κ τ g := by
  first | exact @GlobalTheory.HTW.Rec.existsUnique_reads | exact GlobalTheory.HTW.Rec.existsUnique_reads | (intros; apply GlobalTheory.HTW.Rec.existsUnique_reads <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingRestrictsToWachLetterUnrami
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingRestrictsToWachLetterUnrami
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

theorem existsUnique_over : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL),
    K.1 ≤ MaximalUnramifiedExtension l → ∀ a, ∃! τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Over W τ a := by
  intro l _ P K LL W hK a
  have hle : K.1 ≤ K0 K := le_inf le_rfl hK
  have hsurj : Function.Surjective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) := by
    intro x
    exact ⟨⟨x.1, hle x.2⟩, Subtype.ext rfl⟩
  let e : ↥(K0 K) ≃ₐ[ℚ_[l]] ↥K.1 :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1)
      ⟨(IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1).toRingHom.injective, hsurj⟩
  refine ⟨(W.emb a).comp e.symm.toAlgHom, ?_, ?_⟩
  · show ((W.emb a).comp e.symm.toAlgHom).comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = W.emb a
    ext x
    have : e.symm ((IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) x) = x := e.symm_apply_apply x
    simp only [AlgHom.comp_apply]
    exact congrArg (fun z => ((W.emb a z : ↥LL.1) : Om l)) this
  · intro τ hτ
    have hτ' : τ.comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) = W.emb a := hτ
    ext x
    obtain ⟨y, rfl⟩ := hsurj x
    have h1 : e.symm ((IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) y) = y := e.symm_apply_apply y
    have h2 := congrArg (fun f => f y) hτ'
    simp only [AlgHom.comp_apply] at h2 ⊢
    rw [h2]
    exact congrArg (fun z => ((W.emb a z : ↥LL.1) : Om l)) h1.symm

end GlobalTheory.HTW.Rec
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueEmbeddingRestrictsToWachLetterUnramiStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_embeddingRestrictsToWachLetter_unramified : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (W : Wach P K LL), K.1 ≤ MaximalUnramifiedExtension l → ∀ a, ∃! τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Over W τ a := by
  first | exact @GlobalTheory.HTW.Rec.existsUnique_over | exact GlobalTheory.HTW.Rec.existsUnique_over | (intros; apply GlobalTheory.HTW.Rec.existsUnique_over <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElevenLeInertOddPrimeImagQuadraticLargeScale
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LtPrime
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.InertPrimeLarge

theorem lt_prime : ∀ {D : D7} (L : SizeData₂ D) (l : ℕ), l.Prime → l ≠ 2 →
    jacobiSym (-(D.host.d : ℤ)) l ≠ 1 → L.sc.x ^ (L.sc.ez / 5) < l := by
  intro D L l hl h2 hj
  by_contra hlt
  push_neg at hlt
  have hle : l ≤ D.host.splitBound := le_trans (Nat.le_floor hlt) L.split_tie
  exact hj (D.host.split_small l hl h2 hle)

end GlobalTheory.InertPrimeLarge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElevenLeInertOddPrimeImagQuadraticLargeScale
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.InertPrimeEleven

theorem eleven_le : ∀ eps : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (l : ℕ),
    L.sc.ez = eps → x0 ≤ L.sc.x → l.Prime → InertUnr D l → 11 ≤ l := by
  intro eps heps
  refine ⟨(11 : ℝ) ^ (5 / eps), ?_⟩
  intro D L l he hx hl hin
  have hlt := GlobalTheory.InertPrimeLarge.lt_prime L l hl hin.ne_two hin.2.2.2
  rw [he] at hlt
  have h0 : (0 : ℝ) ≤ (11 : ℝ) ^ (5 / eps) := Real.rpow_nonneg (by norm_num) _
  have hmono : ((11 : ℝ) ^ (5 / eps)) ^ (eps / 5) ≤ L.sc.x ^ (eps / 5) :=
    Real.rpow_le_rpow h0 hx (by positivity)
  have h11 : ((11 : ℝ) ^ (5 / eps)) ^ (eps / 5) = 11 := by
    rw [← Real.rpow_mul (by norm_num)]
    have : 5 / eps * (eps / 5) = 1 := by field_simp
    rw [this, Real.rpow_one]
  have : (11 : ℝ) < l := by linarith
  exact_mod_cast this.le

end GlobalTheory.InertPrimeEleven
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElevenLeInertOddPrimeImagQuadraticLargeScaleStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eleven_le_inertOddPrimeImagQuadratic_large_scale : ∀ eps : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (l : ℕ), L.sc.ez = eps → x0 ≤ L.sc.x → l.Prime → InertUnr D l → 11 ≤ l := by
  first | exact @GlobalTheory.InertPrimeEleven.eleven_le | exact GlobalTheory.InertPrimeEleven.eleven_le | (intros; apply GlobalTheory.InertPrimeEleven.eleven_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxSizeAtNonThickPlaceLeParametersWindowEndsStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MaxSizeAtNonThickPlaceLeWindowEnds
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.HTW.Rec

theorem wB_nonneg {D : D7} (L : SizeData₂ D) : 0 ≤ wB L := by
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := by
    unfold Scale.b' Scale.a Scale.X'
    positivity
  have h0 : 0 ≤ L.sc.w'' D.R.n := by unfold Scale.w''; positivity
  have h1 := L.etaSz_pos
  exact le_trans (by linarith) (le_max_left _ _)

theorem floor_size_le_wB {D : D7} (L : SizeData₂ D) (g : D.R.GG) (j : Fin D.R.m) (hg : ¬ Thick D.host g) :
    ((⌊(hcAt D g).e j⌋.toNat : ℕ) : ℝ) ≤ wB L := by
  set ρ := D.eTau.symm ⟨plc g, plc_mem g⟩ with hρ
  have hρ' : (D.eTau ρ : D.R.GG) = plc g := by rw [hρ, Equiv.apply_symm_apply]
  have hj : j.1 + 1 ≤ D.R.m := j.2
  have hw : wj D (j.1 + 1) ρ = (((D.hc ρ).e j : ℚ) : ℝ) := by
    have hj' : j.1 + 1 - 1 < D.R.m := by have := j.2; omega
    rw [wj, dite_eq_left hj']
    have : (⟨j.1 + 1 - 1, hj'⟩ : Fin D.R.m) = j := Fin.ext (by simp)
    rw [this]
  have hthick : (D.eTau ρ : D.R.GG) ∉ D.host.thickPlaces := by rw [hρ']; exact hg
  have key : wj D (j.1 + 1) ρ ≤ wB L := by
    by_cases h2 : (D.eTau ρ : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht', e⟩ := Finset.mem_image.mp h2
      have a := (L.win_top _ (by omega) hj ρ ⟨t, ht'⟩ e.symm).2
      have b : (L.bT (⟨t, ht'⟩ : D.host.TT) : ℝ) ≤ ⨆ t : D.host.TT, (L.bT t : ℝ) :=
        le_ciSup (f := fun t : D.host.TT => (L.bT t : ℝ)) (Set.finite_range _).bddAbove ⟨t, ht'⟩
      exact le_trans (by linarith) (le_max_right _ _)
    · have a := (L.win_thin (j.1 + 1) (by omega) hj ρ ⟨(D.eTau ρ).2, h2, hthick⟩).2
      exact le_trans a (le_max_left _ _)
  rw [hw] at key
  have he : (hcAt D g).e j = (D.hc ρ).e j := rfl
  rw [he]
  rcases le_or_gt 0 ⌊(D.hc ρ).e j⌋ with h | h
  · rw [show ((⌊(D.hc ρ).e j⌋.toNat : ℕ) : ℝ) = ((⌊(D.hc ρ).e j⌋ : ℤ) : ℝ) by
      exact_mod_cast Int.toNat_of_nonneg h]
    have := Int.floor_le ((D.hc ρ).e j)
    have : (((⌊(D.hc ρ).e j⌋ : ℤ) : ℚ) : ℝ) ≤ (((D.hc ρ).e j : ℚ) : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith
  · rw [Int.toNat_eq_zero.2 h.le]
    simpa using wB_nonneg L

theorem wMax_le_wB : ∀ {D : D7} (L : SizeData₂ D), (wMax D : ℝ) ≤ wB L ∧ (wHat D : ℝ) ≤ wP L := by
  intro D L
  have hB := wB_nonneg L
  have h1 : wMax D ≤ ⌊wB L⌋₊ := by
    apply csSup_le'
    rintro s ⟨g, j, hg, rfl⟩
    exact Nat.le_floor (floor_size_le_wB L g j hg)
  have h2 : (wMax D : ℝ) ≤ wB L :=
    le_trans (by exact_mod_cast h1) (Nat.floor_le hB)
  refine ⟨h2, ?_⟩
  have h3 : (((D.R.t + 1) / 2 : ℕ) : ℝ) ≤ ((D.R.t : ℝ) + 1) / 2 := by
    have := Nat.cast_div_le (α := ℝ) (m := D.R.t + 1) (n := 2)
    push_cast at this
    exact this
  unfold wHat wP
  push_cast
  linarith

end GlobalTheory.HTW.Rec
end
end

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxSizeAtNonThickPlace_le_windowEnds : ∀ {D : D7} (L : SizeData₂ D), (wMax D : ℝ) ≤ wB L ∧ (wHat D : ℝ) ≤ wP L := by
  first | exact @GlobalTheory.HTW.Rec.wMax_le_wB | exact GlobalTheory.HTW.Rec.wMax_le_wB | (intros; apply GlobalTheory.HTW.Rec.wMax_le_wB <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TateDualMatrixRepContinuousCrystalline
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousCyclotomicCharacterPeriodDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousCyclotomicCharacterPeriodDatum
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.HTW.Rec

theorem continuous_cycLL_period : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l),
    Continuous (fun s => ((cycLL (P.PD K) ↥LL.1 s : (↥LL.1)ˣ) : ↥LL.1)) := by
  intro l _ P K LL
  have h := (GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.1
  have e : (fun g => ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1)) =
      fun g : ↥(GK K) => algebraMap ℚ_[l] ↥LL.1 (P.χQ (g : GQ l) : ℚ_[l]) := by
    funext g
    change algebraMap ℚ_[l] ↥LL.1 (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = _
    rw [P.PD_χ]
  rw [e]
  refine Continuous.subtype_mk (f := fun g : ↥(GK K) =>
    algebraMap ℚ_[l] (Om l) (P.χQ (g : GQ l) : ℚ_[l])) ?_ _
  exact (continuous_algebraMap ℚ_[l] (Om l)).comp (h.comp continuous_subtype_val)

end GlobalTheory.HTW.Rec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousCyclotomicCharacterPeriodDatumStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_cyclotomicCharacter_periodDatum : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l), Continuous (fun s => ((cycLL (P.PD K) ↥LL.1 s : (↥LL.1)ˣ) : ↥LL.1)) := by
  first | exact @GlobalTheory.HTW.Rec.continuous_cycLL_period | exact GlobalTheory.HTW.Rec.continuous_cycLL_period | (intros; apply GlobalTheory.HTW.Rec.continuous_cycLL_period <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsJumpVOfMultVNeZero
open NumberField IsDedekindDomain GlobalTheory.HTW Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.HTW.TwistDualLoc

def matGRep {G : Type} [Group G] [TopologicalSpace G] (Qp : Type) {LL : Type} (O : Type) [Field Qp]
    [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    [IsTopologicalRing LL] {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) LL) (hM : Continuous M) :
    GRep G Qp LL O where
  V := Fin k → LL
  ρ := matRep M
  cont x := by
    change Continuous fun g => (M g).mulVec x
    exact hM.matrix_mulVec continuous_const

section

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]

theorem isDual1_dot {k : ℕ} (M : G →* Matrix (Fin k) (Fin k) LL) :
    IsDual1 PD (matRep M) (matRep (twistM (dualM M) (cycLL PD LL))) (dotProductBilin LL LL) := by
  refine ⟨fun g x y => ?_, fun x hx => ?_, fun y hy => ?_, rfl⟩
  · change (M g).mulVec x ⬝ᵥ ((((cycLL PD LL g : LLˣ) : LL) • (M g⁻¹).transpose).mulVec y) =
      ((cycLL PD LL g : LLˣ) : LL) * (x ⬝ᵥ y)
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.mulVec_transpose,
      dotProduct_comm, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, ← map_mul,
      inv_mul_cancel, map_one, Matrix.one_mulVec, dotProduct_comm]
  · funext i
    have := hx (Pi.single i 1)
    simpa using this
  · funext i
    have := hy (Pi.single i 1)
    simpa using this

variable {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

end

end GlobalTheory.HTW.TwistDualLoc
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TateDualMatrixRepContinuousCrystalline
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.HTW.Rec

theorem tateDual_matRep_crys : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {k : ℕ} (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1), (∀ (A A' : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (Pr : A.V →ₗ[↥LL.1] A'.V →ₗ[↥LL.1] ↥LL.1), IsDual1 (P.PD K) A.ρ A'.ρ Pr → IsCrys (P.PD K) A.ρ → IsCrys (P.PD K) A'.ρ) → Continuous M → IsCrys (P.PD K) (matRep M) → Continuous (twistM (dualM M) (cycLL (P.PD K) ↥LL.1)) ∧ IsCrys (P.PD K) (matRep (twistM (dualM M) (cycLL (P.PD K) ↥LL.1))) := by
  intro l _ P K LL k M hT hM hC
  haveI : IsTopologicalRing ↥LL.1 := by
    first
      | infer_instance
      | exact Subring.instIsTopologicalRing LL.1.toSubring
      | exact inferInstanceAs (IsTopologicalRing ↥LL.1.toSubfield.toSubring)
  have hχ := GlobalTheory.T.continuous_cyclotomicCharacter_periodDatum P K LL
  have hinv : Continuous fun g : ↥(GK K) => M g⁻¹ := hM.comp continuous_inv
  have hc : Continuous (twistM (dualM M) (cycLL (P.PD K) ↥LL.1)) := by
    change Continuous fun g => ((cycLL (P.PD K) ↥LL.1 g : (↥LL.1)ˣ) : ↥LL.1) • (M g⁻¹).transpose
    exact hχ.smul hinv.matrix_transpose
  refine ⟨hc, ?_⟩
  exact hT (TwistDualLoc.matGRep ℚ_[l] ↥(OL LL) M hM)
    (TwistDualLoc.matGRep ℚ_[l] ↥(OL LL) _ hc) (dotProductBilin ↥LL.1 ↥LL.1)
    (TwistDualLoc.isDual1_dot (P.PD K) M) hC

end GlobalTheory.HTW.Rec
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TateDualMatrixRepContinuousCrystallineStatement
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateDual_matrixRep_continuous_crystalline : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {k : ℕ} (M : ↥(GK K) →* Matrix (Fin k) (Fin k) ↥LL.1), (∀ (A A' : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (Pr : A.V →ₗ[↥LL.1] A'.V →ₗ[↥LL.1] ↥LL.1), IsDual1 (P.PD K) A.ρ A'.ρ Pr → IsCrys (P.PD K) A.ρ → IsCrys (P.PD K) A'.ρ) → Continuous M → IsCrys (P.PD K) (matRep M) → Continuous (twistM (dualM M) (cycLL (P.PD K) ↥LL.1)) ∧ IsCrys (P.PD K) (matRep (twistM (dualM M) (cycLL (P.PD K) ↥LL.1))) := by
  first | exact @GlobalTheory.HTW.Rec.tateDual_matRep_crys | exact GlobalTheory.HTW.Rec.tateDual_matRep_crys | (intros; apply GlobalTheory.HTW.Rec.tateDual_matRep_crys <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIdeleClassGroupHomOpenKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIdeleClassGroupHomOpenKernel
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal

noncomputable section

open scoped nonZeroDivisors

namespace GlobalTheory.IdeleClass

variable (E : Type) [Field E] [NumberField E]

theorem localIdele_snd_self' (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ) :
    ((localIdele E v x : Ideles E) : AdeleRing (𝓞 E) E).2 v = x := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion E) : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletion E) v = x
  convert Pi.mulSingle_eq_same v (x : v.adicCompletion E)

theorem localIdele_snd_ne' (v w : HeightOneSpectrum (𝓞 E)) (h : w ≠ v) (x : (v.adicCompletion E)ˣ) :
    ((localIdele E v x : Ideles E) : AdeleRing (𝓞 E) E).2 w = 1 := by
  classical
  show (Pi.mulSingle v (x : v.adicCompletion E) : ∀ w : HeightOneSpectrum (𝓞 E), w.adicCompletion E) w = 1
  convert Pi.mulSingle_eq_of_ne h (x : v.adicCompletion E)

theorem classHom_val (a : Ideles E) :
    ((((GlobalTheory.Mem.UnitIndex.idealHom E).comp (GlobalTheory.Mem.UnitIndex.finIdele E)).toHomUnits a :
      (FractionalIdeal (𝓞 E)⁰ E)ˣ) : FractionalIdeal (𝓞 E)⁰ E) =
      GlobalTheory.Idele.idealOf (GlobalTheory.Mem.UnitIndex.finIdele E a) := rfl

theorem finIdele_apply (a : Ideles E) (v : HeightOneSpectrum (𝓞 E)) :
    ((GlobalTheory.Mem.UnitIndex.finIdele E a : (FiniteAdeleRing (𝓞 E) E)ˣ) : FiniteAdeleRing (𝓞 E) E) v =
      (a : AdeleRing (𝓞 E) E).2 v := rfl

theorem classHom_eq_one_of_mem_unitIdl {a : Ideles E} (ha : a ∈ GlobalTheory.Mem.Chr.unitIdl E) :
    GlobalTheory.Mem.UnitIndex.classHom E a = 1 := by
  have h : GlobalTheory.Idele.idealOf (GlobalTheory.Mem.UnitIndex.finIdele E a) = 1 := by
    rw [← GlobalTheory.Idele.smul_one_eq]
    exact (GlobalTheory.Idele.smul_eq_self_iff _ (one_ne_zero (α := FractionalIdeal (𝓞 E)⁰ E))).2 fun v => ha v
  have hu : ((GlobalTheory.Mem.UnitIndex.idealHom E).comp (GlobalTheory.Mem.UnitIndex.finIdele E)).toHomUnits a = 1 :=
    Units.ext (by rw [classHom_val, h]; rfl)
  show ClassGroup.mk E _ = 1
  rw [hu, map_one]

theorem unitIdl_le_ker : GlobalTheory.Mem.Chr.unitIdl E ≤ (GlobalTheory.Mem.UnitIndex.classHom E).ker :=
  fun _ ha => classHom_eq_one_of_mem_unitIdl E ha

theorem infConn_le_unitIdl : infConn E ≤ GlobalTheory.Mem.Chr.unitIdl E := by
  rintro _ ⟨y, -, rfl⟩ v
  show Valued.v (1 : v.adicCompletion E) = 1
  exact map_one _

theorem diagUnits_range_le_ker : (diagUnits E).range ≤ (GlobalTheory.Mem.UnitIndex.classHom E).ker := by
  rintro _ ⟨k, rfl⟩
  have hd : GlobalTheory.Mem.UnitIndex.finIdele E (diagUnits E k) =
      FiniteAdeleRing.unitEmbedding (𝓞 E) E k := Units.ext rfl
  show ClassGroup.mk E _ = 1
  rw [ClassGroup.mk_eq_one_iff, classHom_val, hd, GlobalTheory.Idele.idealOf_unitEmbedding,
    FractionalIdeal.coe_spanSingleton]
  exact ⟨⟨(k : E), rfl⟩⟩

theorem localIdele_mem_unitIdl (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ)
    (hx : IsUnitAt v x) : localIdele E v x ∈ GlobalTheory.Mem.Chr.unitIdl E := by
  intro w
  by_cases hw : w = v
  · subst hw
    rw [localIdele_snd_self']
    exact hx
  · rw [localIdele_snd_ne' E v w hw]
    exact map_one _

open Classical in
theorem ord_vw_localIdele_unif (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ)
    (hx : IsUnifAt v x) (w : HeightOneSpectrum (𝓞 E)) :
    GlobalTheory.Idele.ord_vw (GlobalTheory.Mem.UnitIndex.finIdele E (localIdele E v x)) w =
      if v = w then 1 else 0 := by
  rw [GlobalTheory.Idele.ord_vw, finIdele_apply]
  by_cases hw : w = v
  · subst hw
    rw [localIdele_snd_self', if_pos rfl]
    have hx' : Valued.v (x : w.adicCompletion E) = WithZero.exp (-1) := hx
    rw [hx', WithZero.log_exp]
    rfl
  · rw [localIdele_snd_ne' E v w hw, if_neg (Ne.symm hw), map_one]
    rfl

theorem classHom_localIdele_unif (v : HeightOneSpectrum (𝓞 E)) (x : (v.adicCompletion E)ˣ)
    (hx : IsUnifAt v x) :
    GlobalTheory.Mem.UnitIndex.classHom E (localIdele E v x) =
      ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  classical
  have hv : ((v.asIdeal : FractionalIdeal (𝓞 E)⁰ E)) ≠ 0 := by simpa using v.ne_bot
  have h : GlobalTheory.Idele.idealOf (GlobalTheory.Mem.UnitIndex.finIdele E (localIdele E v x)) =
      (v.asIdeal : FractionalIdeal (𝓞 E)⁰ E) := by
    refine GlobalTheory.Idele.eq_of_count_eq (GlobalTheory.Idele.idealOf_ne_zero _) hv fun w => ?_
    rw [GlobalTheory.Idele.count_idealOf, ord_vw_localIdele_unif E v x hx w,
      FractionalIdeal.count_maximal]
  have hu : ((GlobalTheory.Mem.UnitIndex.idealHom E).comp (GlobalTheory.Mem.UnitIndex.finIdele E)).toHomUnits
      (localIdele E v x) =
      FractionalIdeal.mk0 E ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ :=
    Units.ext (by rw [classHom_val, h, FractionalIdeal.coe_mk0])
  show ClassGroup.mk E _ = _
  rw [hu, ClassGroup.mk_mk0]

end GlobalTheory.IdeleClass

namespace GlobalTheory

theorem exists_ideleClassHom : ∀ (E : Type) [Field E] [NumberField E], ∃ cl : Ideles E →* ClassGroup (𝓞 E), IsOpen (cl.ker : Set (Ideles E)) ∧ (diagUnits E).range ⊔ infConn E ≤ cl.ker ∧ (∀ (v : HeightOneSpectrum (𝓞 E)) x, IsUnitAt v x → cl (localIdele E v x) = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) x, IsUnifAt v x → cl (localIdele E v x) = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  intro E _ _
  refine ⟨GlobalTheory.Mem.UnitIndex.classHom E,
    Subgroup.isOpen_mono (GlobalTheory.IdeleClass.unitIdl_le_ker E) GlobalTheory.Mem.UnitOpen.isOpen_unitIdl,
    sup_le (GlobalTheory.IdeleClass.diagUnits_range_le_ker E)
      ((GlobalTheory.IdeleClass.infConn_le_unitIdl E).trans (GlobalTheory.IdeleClass.unitIdl_le_ker E)),
    fun v x hx => GlobalTheory.IdeleClass.classHom_eq_one_of_mem_unitIdl E
      (GlobalTheory.IdeleClass.localIdele_mem_unitIdl E v x hx),
    fun v x hx => GlobalTheory.IdeleClass.classHom_localIdele_unif E v x hx⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIdeleClassGroupHomOpenKernelStatement
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ideleClassGroupHom_open_kernel : ∀ (E : Type) [Field E] [NumberField E], ∃ cl : Ideles E →* ClassGroup (𝓞 E), IsOpen (cl.ker : Set (Ideles E)) ∧ (diagUnits E).range ⊔ infConn E ≤ cl.ker ∧ (∀ (v : HeightOneSpectrum (𝓞 E)) x, IsUnitAt v x → cl (localIdele E v x) = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) x, IsUnifAt v x → cl (localIdele E v x) = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  first | exact @GlobalTheory.exists_ideleClassHom | exact GlobalTheory.exists_ideleClassHom | (intros; apply GlobalTheory.exists_ideleClassHom <;> assumption)
end
end
