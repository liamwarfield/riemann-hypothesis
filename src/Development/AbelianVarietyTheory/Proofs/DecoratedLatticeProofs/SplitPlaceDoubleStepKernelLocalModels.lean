module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitaryChartsAllFinitePlacesFrameLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineModelKappaTransformIsLocalModel
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalModelBoxProductOrthogonalSumTarget
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalS
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelJoinOnV0Three
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoprimeMultiplierOneSubNormCongrZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedThetaSeriesTermsLawsUnipotentRationalStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepKernelLocalModels
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepKernelLocalModels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LastKerLoc


open GlobalTheory.LocFlat.CFac in
theorem lastLoc : ∀ (D : D7), LastLoc D := by
  intro D k _ _ _ _ _ _ p ν hν ψ hψ ψk hχ ρ B S X T L'' o'' τ hL hτ s z₀ hs hz n n' Z _ _ _ _ _ _ FA F₀ FS FT FX hcore hFX T₁ T₂ hT₁ hT₂
  classical
  obtain ⟨-, hck, -⟩ := GlobalTheory.T.weilCharacter_splitPlace_exists_continuous_nontrivial D k p ψ hψ
  obtain ⟨hψc, hψ1⟩ := hck ψk hχ
  let κ : WO S L'' → WO B.L S := fun w => GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj B.L S ((rat τ : Mx D B.L.rank L''.rank) * w)
  let Bl : SB (Matrix Z n k) →ₗ[ℂ] SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (WO B.A S → WO S X → ℂ) :=
    LinearMap.mk₂ ℂ (fun Ψ₂ Ψ₁ u => o''.boxT S (T₂ Ψ₂) fun w => T₁ Ψ₁ ((B.o.resS S).symm (u, κ w)))
      (by intros; funext u v; simp only [OrthDec.boxT, map_add (f := _), Pi.add_apply, add_mul])
      (by intros; funext u v; simp only [OrthDec.boxT, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc])
      (by intros; funext u v; simp only [OrthDec.boxT, map_add (f := _), Pi.add_apply, mul_add])
      (by intros; funext u v; simp only [OrthDec.boxT, map_smul, Pi.smul_apply, smul_eq_mul]; ring)
  obtain ⟨Λ, hΛ1, hΛ2⟩ := GlobalTheory.T.exists_pair_space_linear_map_via_partial_fourier k ν hν ψk hψc hψ1 n n' Z _ Bl
  obtain ⟨hXi, hPsi⟩ := GlobalTheory.T.last_column_datum_tensor_mem_schwartzBruhat k ν hν ψk hψc hψ1 n n' Z
  obtain ⟨hHat, hDec⟩ := GlobalTheory.T.row_fourier_onto_and_span_transformed_last_row k ν hν ψk hψc hψ1 n Z
  have hBl : ∀ a Ψ u v, Bl a Ψ u v = T₂ a (o''.resT S v).1 * T₁ Ψ ((B.o.resS S).symm (u, κ (o''.resT S v).2)) :=
    fun _ _ _ _ => rfl
  refine ⟨Λ, ⟨?_, ?_⟩, ?_⟩
  · intro Ξ₂ v
    obtain ⟨N, a, c, g, hg, hsum⟩ := hDec Ξ₂
    have hsl := fun i => GlobalTheory.T.localModel_slice_firstSummand D k p ψ ρ B S s n n' FA F₀ FS hcore T₁ hT₁ (c i) (κ (o''.resT S v).2)
    choose T' hT' hT'eq using hsl
    obtain ⟨hz0, hlin⟩ := GlobalTheory.T.splitLocalPlace_local_models_linear_subspace D k p ψ n n' B.A S FA FS
    refine ⟨∑ i, (T₂ (a i) (o''.resT S v).1) • T' i, ?_, ?_⟩
    · refine Finset.sum_induction _ (fun T => p.IsModel ψ FA FS T) (fun _ _ h1 h2 => (hlin _ _ h1 h2).1) hz0 ?_
      intro i _
      exact (hlin _ _ (hT' i) (hT' i)).2 _
    · intro Ξ₁ Ξ hΞ u
      have hΞs : Ξ = ∑ i, prodSB Ξ₁ (g i) := by
        apply Subtype.ext
        funext q
        rw [hΞ, Submodule.coe_sum, Finset.sum_apply, hsum, Submodule.coe_sum, Finset.sum_apply, Finset.mul_sum]
        rfl
      have hPi : ∀ i, ∃ Ψ₁ : SB (Matrix n (n' ⊕ Unit) k), ∀ x, Ψ₁.1 x = Ξ₁.1 x.toCols₁ * (c i).1 (Matrix.of fun r _ => x r (Sum.inr ())) :=
        fun i => hPsi Ξ₁ (c i)
      choose Ψ hΨ using hPi
      have hterm : ∀ i, Λ (prodSB Ξ₁ (g i)) = Bl (a i) (Ψ i) := fun i =>
        hΛ2 Ξ₁ (a i) (c i) (Ψ i) (prodSB Ξ₁ (g i)) (hΨ i) (fun q => by rw [prodSB_apply, hg])
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hΞs, map_sum, Finset.sum_apply, Finset.sum_apply, LinearMap.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hterm, hBl, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, hT'eq i Ξ₁ (Ψ i) (hΨ i) u]
  · intro Ξ₁ u
    obtain ⟨FL, hFL, hsl⟩ := GlobalTheory.T.local_model_restricted_to_line_slice D k p ψ ρ B S s n n' FA F₀ FS hcore T₁ hT₁
    obtain ⟨TLS, hTLS, hTLSeq⟩ := hsl Ξ₁ u
    obtain ⟨FL'', hFL'', TL, hTL, hTLeq⟩ := GlobalTheory.T.lineModel_kappa_transform_isLocalModel D k p ν hν ψ hψ ψk hχ B.L S L'' B.ζ τ hL hτ s z₀ hs hz n FS FL hFL TLS hTLS
    let P : SB (Matrix (Z ⊕ Unit) n k) →ₗ[ℂ] SB (Matrix n n' k × Matrix (Z ⊕ Unit) n k) :=
      { toFun := fun g => prodSB Ξ₁ g
        map_add' := fun g g' => by apply Subtype.ext; funext q; simp [prodFn, mul_add]
        map_smul' := fun c g => by apply Subtype.ext; funext q; simp [prodFn]; ring }
    let TX : SB (Matrix (Z ⊕ Unit) n k) →ₗ[ℂ] (WO S X → ℂ) := LinearMap.proj u ∘ₗ Λ ∘ₗ P
    have hTXa : ∀ g, TX g = Λ (prodSB Ξ₁ g) u := fun _ => rfl
    refine ⟨TX, GlobalTheory.T.local_model_box_product_orthogonal_sum_target D k p ψ S X T L'' o'' n Z FS FT FL'' FX ?_ T₂ TL hT₂ hTL TX ?_, ?_⟩
    · rw [hFX]
      congr 1
      ext r j
      simp [Matrix.mul_apply, hFL'', Matrix.mulVec, dotProduct]
    · intro a b Φ hΦ
      obtain ⟨c, hc⟩ := hHat b
      obtain ⟨Ψ₁, hΨ₁⟩ := hPsi Ξ₁ c
      have h := hΛ2 Ξ₁ a c Ψ₁ (prodSB Ξ₁ Φ) hΨ₁ (fun q => by rw [prodSB_apply, hΦ, hc]; rfl)
      funext v
      rw [hTXa, h, hBl, OrthDec.boxT, hTLeq c b hc, hTLSeq c Ψ₁ hΨ₁]
    · intro Ξ₂ Ξ hΞ v
      have : Ξ = prodSB Ξ₁ Ξ₂ := Subtype.ext (funext hΞ)
      subst this
      rfl
  · intro Ψ₁ Ψ₂
    obtain ⟨Ξ, hΞ⟩ := hXi Ψ₁ Ψ₂
    refine ⟨Ξ, hΞ, fun u => ?_⟩
    rw [hΛ1 Ψ₁ Ψ₂ Ξ hΞ]
    rfl

end GlobalTheory.LastKerLoc

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDoubleStepKernelLocalModelsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_doubleStep_kernel_localModels : ∀ (D : D7), LastLoc D := by
  first | exact @GlobalTheory.LastKerLoc.lastLoc | exact GlobalTheory.LastKerLoc.lastLoc | (intros; apply GlobalTheory.LastKerLoc.lastLoc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AlVEmbHEqNegOneZpow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SemiTrace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tauE_star (D : D7) (τ : D.what₂.Tau) (x : D.host.E) :
    tauE D τ (star x) = starRingEnd ℂ (tauE D τ x) :=
  D.sp.cm.cmUnram.2.1 _ x

theorem sum_two_re_tauE (D : D7) (e : D.host.E) :
    ∑ t, (((2 * (tauE D t e).re : ℝ)) : ℂ) = ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) := by
  classical
  have h1 : ((Algebra.trace ℚ D.host.E e : ℚ) : ℂ) = ∑ σ : D.host.E →+* ℂ, σ e := by
    have := trace_eq_sum_embeddings (K := ℚ) (L := D.host.E) ℂ (x := e)
    rw [eq_ratCast] at this
    rw [this]
    exact (Fintype.sum_equiv (RingHom.equivRatAlgHom D.host.E ℂ) _ _ fun _ => rfl).symm
  have hi := GlobalTheory.StdRat.tauE_injective D
  have hcm := GlobalTheory.StdRat.tauE_cm D
  have hb : Function.Bijective (Sum.elim (tauE D) fun t => ComplexEmbedding.conjugate (tauE D t)) := by
    have hc : ∀ σ : D.host.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
      fun σ => star_star σ
    constructor
    · rintro (a | a) (b | b) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h
      · rw [hi h]
      · exact absurd ⟨a, h⟩ ((hcm (tauE D b)).1 ⟨b, rfl⟩)
      · exact absurd ⟨b, h.symm⟩ ((hcm (tauE D a)).1 ⟨a, rfl⟩)
      · have := congrArg ComplexEmbedding.conjugate h
        rw [hc, hc] at this
        rw [hi this]
    · intro σ
      by_cases h : ∃ t, tauE D t = ComplexEmbedding.conjugate σ
      · obtain ⟨t, ht⟩ := h
        exact ⟨Sum.inr t, by simp only [Sum.elim_inr]; rw [ht, hc]⟩
      · obtain ⟨t, ht⟩ := (hcm σ).2 h
        exact ⟨Sum.inl t, ht⟩
  have h4 := hb.sum_comp fun σ : D.host.E →+* ℂ => σ e
  rw [Fintype.sum_sum_type, ← h1] at h4
  simp only [Sum.elim_inl, Sum.elim_inr, ComplexEmbedding.conjugate_coe_eq] at h4
  rw [← h4, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Complex.add_conj]

theorem re_xi_mul_sq (u : ℝ) (hu : 0 < u) :
    (Complex.I * ((u⁻¹ : ℝ) : ℂ) * ((1 + Complex.I * (u : ℂ)) / 2) ^ 2).re = -1 / 2 := by
  have h : Complex.I * ((u⁻¹ : ℝ) : ℂ) * ((1 + Complex.I * (u : ℂ)) / 2) ^ 2
      = ((-1 / 2 : ℝ) : ℂ) + Complex.I * (((1 - u ^ 2) / (4 * u) : ℝ) : ℂ) := by
    have hu' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hu.ne'
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq, Complex.I_pow_three]
    ring
  rw [h]
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

end GlobalTheory.SemiTrace

namespace GlobalTheory.SemiTrace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem alV_embH_eq_neg_one_zpow : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (y : Formalism.L2.Col.HomE D.host.E a b) (k : ℤ), (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T ((LinearMap.toMatrix' (y)).reindex (finCongr hT.symm) (finCongr hS.symm)) ((LinearMap.toMatrix' (y)).reindex (finCongr hT.symm) (finCongr hS.symm))) → alV D.host.d sc (embH (tauE D) δ y) = (-1 : ℂ) ^ k := by
  intro D ψ θ S T a b hS hT δ sc hP y k hk
  subst hS hT
  have hd : 0 < Real.sqrt D.host.d :=
    Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero D.host.hyp.2.1.ne_zero))
  set M := (LinearMap.toMatrix' y).reindex (finCongr (rfl : T.rank = T.rank).symm) (finCongr (rfl : S.rank = S.rank).symm) with hMdef
  have hMij : ∀ i j, M i j = y (Pi.single j 1) i := by
    intro i j; simp [M, LinearMap.toMatrix'_apply]
  set s : D.what₂.Tau → ℝ := fun τ => ∑ i, ∑ j, Complex.normSq (tauE D τ (M i j)) with hs
  have hh : ∀ τ, tauE D τ (GlobalTheory.LatVac.hRat S T M M) = ((s τ : ℝ) : ℂ) := by
    intro τ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.LatVac.hRat, hP.gS, hP.gT, inv_one, Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, map_sum, map_mul, tauE_star, hs]
    simp only [apply_ite (⇑(tauE D τ)), map_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true, map_mul, tauE_star]
    push_cast
    rw [Finset.sum_comm]
    calc _ = ∑ j, ∑ i, ((Complex.normSq (tauE D τ (M i j)) : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
          simp only [Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Complex.normSq_eq_conj_mul_self]
      _ = _ := Finset.sum_comm
  have hτ : ∀ τ, (tauE D τ (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T M M)).re = -(s τ) / 2 := by
    intro τ
    rw [map_mul, map_mul, map_pow, map_div₀, map_add (f := _), map_one, map_ofNat, hh, hP.xi, Formalism.L2.Theta.tauE_sqrtMinusD,
      Complex.re_mul_ofReal, re_xi_mul_sq _ hd]
    ring
  have hk' : (k : ℂ) = ((-(∑ τ, s τ) : ℝ) : ℂ) := by
    have e1 := sum_two_re_tauE D (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T M M)
    rw [← hk] at e1
    push_cast at e1
    rw [← e1]
    simp only [hτ]
    push_cast
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun τ _ => ?_
    ring
  have hsc : sc * Complex.normSq δ = 2 * (Real.sqrt D.host.d)⁻¹ := by
    rw [← Complex.sq_norm]; exact hP.scale
  have hq : Formalism.L2.Th1.H.qOf (Real.sqrt D.host.d / 2) (HV sc) (embH (tauE D) δ y) = ∑ τ, s τ := by
    simp only [Formalism.L2.Th1.H.qOf, HV, LinearMap.mk₂'ₛₗ_apply, embH, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Complex.mul_conj]
    rw [show ((sc : ℂ) * ∑ x, ∑ x_1, ∑ x_2, ((Complex.normSq (δ * tauE D x (y (Pi.single x_2 1) x_1)) : ℝ) : ℂ)) =
        ((sc * ∑ x, ∑ x_1, ∑ x_2, Complex.normSq (δ * tauE D x (y (Pi.single x_2 1) x_1)) : ℝ) : ℂ) by push_cast; rfl,
      Complex.ofReal_re]
    simp_rw [Complex.normSq_mul, ← Finset.mul_sum]
    simp only [hs, hMij]
    rw [← mul_assoc sc, hsc]
    field_simp
  have hsum : ((∑ τ, s τ : ℝ) : ℂ) = -(k : ℂ) := by rw [hk']; push_cast; ring
  rw [alV, Formalism.L2.Th1.H.alphaQ, hq, hsum,
    show (Real.pi : ℂ) * Complex.I * -(k : ℂ) = ((-k : ℤ) : ℂ) * ((Real.pi : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_int_mul, Complex.exp_pi_mul_I, _root_.zpow_neg, ← _root_.inv_zpow, inv_neg, inv_one]
end GlobalTheory.SemiTrace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentDataStepLattice
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.MidVacLat

variable {D : D7}

theorem mt_mul' (V : HSp D) (g h : GA D V) : mt V (g * h) = mt V g * mt V h := rfl

theorem mt_one' (V : HSp D) : mt V 1 = 1 := rfl

theorem mt_mul_inv_mulVec (V : HSp D) (g : GA D V) (y : Fin V.rank → AE D) : mt V g *ᵥ (mt V g⁻¹ *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← mt_mul', mul_inv_cancel, mt_one', Matrix.one_mulVec]

theorem mulVec_mem_idAt {n : ℕ} (A : Matrix (Fin n) (Fin n) (AE D)) {P : GlobalTheory.FinPl.Pl D → Prop} {y : Fin n → AE D}
    (hy : ∀ i, y i ∈ GlobalTheory.FinPl.idAt D P) (i : Fin n) : (A *ᵥ y) i ∈ GlobalTheory.FinPl.idAt D P := by
  simp only [Matrix.mulVec, dotProduct]
  exact sum_mem fun j _ => Ideal.mul_mem_left _ _ (hy j)

theorem moves_inv {S : HSp D} {g : GA D S} {L M : GlobalTheory.FinPl.Lat S} {P : GlobalTheory.FinPl.Pl D → Prop}
    (h : GlobalTheory.FinPl.Moves S g L M P) : GlobalTheory.FinPl.Moves S g⁻¹ M L P := by
  intro y hy
  have e := h (mt S g⁻¹ *ᵥ y) (mulVec_mem_idAt _ hy)
  rw [mt_mul_inv_mulVec] at e
  exact e.symm

theorem smul_mem_latA {S : HSp D} {L : GlobalTheory.FinPl.Lat S} {P : GlobalTheory.FinPl.Pl D → Prop} {a : D.host.E} (ha : a ∈ D.host.AA)
    {y : Fin S.rank → AE D} (hy : y ∈ GlobalTheory.FinPl.latV S L P) :
    ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y ∈ GlobalTheory.FinPl.latA S L P := by
  induction hy using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨β, hβi, hβ, c, hc, x, hx, rfl⟩ := hz
    rw [Set.mem_singleton_iff] at hc
    subst hc
    refine AddSubgroup.subset_closure ⟨β, hβi, hβ, a, ha, x, hx, ?_⟩
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [smul_add]; exact add_mem hz hz'
  | neg z _ hz => rw [smul_neg]; exact neg_mem hz

theorem mulVec_mem_latA {S : HSp D} {g : GA D S} {L M : GlobalTheory.FinPl.Lat S} {P : GlobalTheory.FinPl.Pl D → Prop}
    (h : GlobalTheory.FinPl.Moves S g L M P) {z : Fin S.rank → AE D} (hz : z ∈ GlobalTheory.FinPl.latA S L P) :
    mt S g *ᵥ z ∈ GlobalTheory.FinPl.latA S M P := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβi, hβ, a, ha, x, hx, rfl⟩ := hy
    set y' : Fin S.rank → AE D := fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 * x i) with hy'
    have hy'm : y' ∈ GlobalTheory.FinPl.latV S L P := AddSubgroup.subset_closure ⟨β, hβi, hβ, 1, rfl, x, hx, rfl⟩
    have hsplit : (fun i => pairA D.host.F 0 β ⊗ₜ[D.host.F] (a * x i)) = ((1 : AF D.host.F) ⊗ₜ[D.host.F] a) • y' := by
      funext i
      simp only [hy', Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hsplit, Matrix.mulVec_smul]
    exact smul_mem_latA ha ((h y' (GlobalTheory.FinPl.FrameLat.latV_supp hy'm)).1 hy'm)
  | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [Matrix.mulVec_add]; exact add_mem hz hz'
  | neg z _ hz => rw [Matrix.mulVec_neg]; exact neg_mem hz

theorem actO_mem_latO {S T : HSp D} {Λ M : GlobalTheory.FinPl.Lat S} {Λ' M' : GlobalTheory.FinPl.Lat T} (hΛ : IsSelfDualC S Λ)
    (hM : IsSelfDualC S M) (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {P : GlobalTheory.FinPl.Pl D → Prop} {g : GA D S}
    {h : GA D T} (hg : GlobalTheory.FinPl.Moves S g Λ M P) (hh : GlobalTheory.FinPl.Moves T h Λ' M' P) {u : WO S T}
    (hu : u ∈ latO S T (Λ : Set _) (Λ' : Set _) P) : actO S T g h u ∈ latO S T (M : Set _) (M' : Set _) P := by
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T Λ Λ' hΛ hΛ' P] at hu
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T M M' hM hM' P]
  obtain ⟨hmx, hmap⟩ := hu
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · show (HMul.hMul (HMul.hMul (mt T h) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹)) i j ∈ _
    rw [Matrix.mul_apply]
    refine sum_mem fun l _ => Ideal.mul_mem_right _ _ ?_
    rw [Matrix.mul_apply]
    exact sum_mem fun k _ => Ideal.mul_mem_left _ _ (hmx k l)
  · change (HMul.hMul (HMul.hMul (mt T h) (u : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹)) *ᵥ y ∈ _
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 : mt S g⁻¹ *ᵥ y ∈ GlobalTheory.FinPl.latV S Λ P :=
      (moves_inv hg y (GlobalTheory.FinPl.FrameLat.latV_supp hy)).1 hy
    exact mulVec_mem_latA hh (hmap _ h1)

theorem actO_smul_left {S T : HSp D} (g : GA D S) (h : GA D T) (e : AE D) (x : WO S T) :
    actO S T g h (e • x) = e • actO S T g h x := by
  simp only [actO, Matrix.mul_smul, Matrix.smul_mul]

theorem actO_two_nsmul {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (2 • x) = 2 • actO S T g h x := by
  simp only [two_nsmul, actO, Matrix.mul_add, Matrix.add_mul]

theorem isHalf_actO {S T : HSp D} (g : GA D S) (h : GA D T) {e : AE D} {x : WO S T} (hx : IsHalf e x) :
    IsHalf e (actO S T g h x) := by
  have hx' : e • x = x := by
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact hx i j
  intro i j
  have := congrFun (congrFun (actO_smul_left g h e x) i) j
  rw [hx'] at this
  rw [Matrix.smul_apply, smul_eq_mul] at this
  exact this.symm

theorem actO_actO_inv {S T : HSp D} (g : GA D S) (h : GA D T) (x : WO S T) :
    actO S T g h (actO S T g⁻¹ h⁻¹ x) = x := by
  show HMul.hMul (HMul.hMul (mt T h) (HMul.hMul (HMul.hMul (mt T h⁻¹) (x : Matrix (Fin T.rank) (Fin S.rank) (AE D))) (mt S g⁻¹⁻¹))) (mt S g⁻¹) = x
  rw [inv_inv, Matrix.mul_assoc, Matrix.mul_assoc, ← mt_mul' S g g⁻¹, mul_inv_cancel,
    mt_one', Matrix.mul_one, ← Matrix.mul_assoc, ← mt_mul' T h h⁻¹, mul_inv_cancel,
    mt_one', Matrix.one_mul]

theorem isLatVac_move {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {Λ M : GlobalTheory.FinPl.Lat S} {Λ' M' : GlobalTheory.FinPl.Lat T} (hΛ : IsSelfDualC S Λ)
    (hM : IsSelfDualC S M) (hΛ' : IsSelfDualC T Λ') (hM' : IsSelfDualC T M') {b : GA D S} {b' : GA D T}
    (hb : GlobalTheory.FinPl.Moves S b Λ M fun _ => True) (hb' : GlobalTheory.FinPl.Moves T b' Λ' M' fun _ => True) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) (hv : IsLatVac (heisO ψ S T) (latO S T (Λ : Set _) (Λ' : Set _) fun _ => True) f) :
    IsLatVac (heisO ψ S T) (latO S T (M : Set _) (M' : Set _) fun _ => True) (om (b, b') f) := by
  have key : ∀ u, u ∈ latO S T (M : Set _) (M' : Set _) (fun _ => True) → actO S T b⁻¹ b'⁻¹ u ∈ latO S T (Λ : Set _) (Λ' : Set _) fun _ => True :=
    fun u hu => actO_mem_latO hM hΛ hM' hΛ' (moves_inv hb) (moves_inv hb') hu
  refine ⟨fun u hu => ?_, fun e he u hu hh => ?_⟩
  · have hw := key u hu
    have h2 : 2 • u = actO S T b b' (2 • actO S T b⁻¹ b'⁻¹ u) := by
      rw [actO_two_nsmul, actO_actO_inv]
    rw [h2, ← hW.om_heis b b' _ f hf, hv.1 _ hw]
  · have hw := key u hu
    have h1 : u = actO S T b b' (actO S T b⁻¹ b'⁻¹ u) := (actO_actO_inv b b' u).symm
    rw [h1, ← hW.om_heis b b' _ f hf, hv.2 e he _ hw (isHalf_actO _ _ hh)]

end GlobalTheory.MidVacLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JoinSubspaceRealDataExists
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain MeasureTheory
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.Theta Formalism.L2.SG.RowsJoinPinned
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.SRe GlobalTheory.Mem.SJ

namespace GlobalTheory.Mem.KJoinLat

theorem exists_read_of_latTie : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (n : ℕ), A3.fam3.Ok3 n → ∀ (S0 : IndefData (A3.side3 F.P0 F.ψ0 (R.toCx3 F).zs)) (p0 : BaseLevelRowSide D) (Sp : SPer (F.Dc (R.toCx3 F).zs)) (C : ColData (F.Dc (R.toCx3 F).zs) Sp ((R.toCx3 F).data F.cr true)) (NuC : ∀ u, Submodule (RingOfIntegers D.what₂.LL) (Fin ((F.Dc (R.toCx3 F).zs).a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 (F.Dc (R.toCx3 F).zs)), DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 C NuC I → ∃ Rd : Read D (R.toCx3 F) F.fc (twAt D.what₂.embLL A3.A.v0), HEq Rd.wU I.wU ∧ HEq Rd.eNu I.eNu ∧ HEq Rd.eRR I.eRR ∧ (∀ y, HEq (Rd.jV y) (I.jA A3.A.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec y))) ∧ Rd.ReadingFormsSpanGoodSubspace ∧ Rd.IotaRd F.cr ∧ Rd.NuTie ∧ (HLatTie (Formalism.BasicNotions.RowSide.sharp D).RR (A3.indefDown ((R.toCx3 F).data F.cr true)).RR (A3.indefDown ((R.toCx3 F).data F.cr true)).XE I.eRR → Rd.RRTie F.cr) ∧ ((∀ (u : D.what₂.Word) (x : Fin ((F.Dc (R.toCx3 F).zs).a (I.wU u)) → D.what₂.LL) (y : Fin ((A3.side3 F.P1 F.ψ1 (R.toCx3 F).zs).nV A3.A.μ0) → D.what₂.LL), D.what₂.embLL ((F.Dc (R.toCx3 F).zs).Pt (I.wU u) A3.A.μ0 x y) = D.what₂.perCol u (I.tup A3.A.μ0) (D.jN u (I.eNu u x)) (I.jA A3.A.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec y))) → Rd.DcPt) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F n hOk S0 p0 Sp C NuC I h
  obtain ⟨Rd, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    exists_read_of_matrix_tie D (R.toCx3 F) F.fc F.cr (I.tup A3.A.μ0) h.tup.mu0 h.tup.v0 (I.jA A3.A.μ0)
      (rH D A3.A F.P1 F.ψ1 A3.A.μ0) (rE D A3.A F.P1 F.ψ1 A3.A.μ0) (rV0 D A3.A F.P1 F.ψ1 A3.A.μ0) I.wU I.eNu I.eRR
      (h.sharp.forms A3.A.μ0) (GlobalTheory.range_goodProjector_eq_range_goodCoordinates D A3.A n hOk.ok2 F.P1 F.ψ1 A3.A.μ0) (h.sharp.iota A3.A.μ0)
      (fun u => ⟨_, h.cols.Nu u⟩)
  exact ⟨Rd, h1, h2, h3, h4, h5, h6, h7, fun hR => h8 ⟨_, hR⟩, h9⟩

theorem kernelJoin_thetaSurjective_goodPart_latticeCondition : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (n : ℕ), A3.fam3.Ok3 n → A3.fam3.TypesSep3 → R.WeakCharacterisation F → PrimRows3 R F → SchurAll D → (D.sp.Y 0).SigOK → ∀ (S0 : IndefData (A3.side3 F.P0 F.ψ0 (R.toCx3 F).zs)) (p0 : BaseLevelRowSide D) (C : ColData (F.Dc (R.toCx3 F).zs) (F.Sp (R.toCx3 F).zs) ((R.toCx3 F).data F.cr true)) (NuC : ∀ u, Submodule (RingOfIntegers D.what₂.LL) (Fin ((F.Dc (R.toCx3 F).zs).a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 (F.Dc (R.toCx3 F).zs)), DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 (R.toCx3 F).zs S0 ((R.toCx3 F).data F.cr true) p0 C NuC I → HLatTie (Formalism.BasicNotions.RowSide.sharp D).RR (A3.indefDown ((R.toCx3 F).data F.cr true)).RR (A3.indefDown ((R.toCx3 F).data F.cr true)).XE I.eRR → (∀ (u : D.what₂.Word) (x : Fin ((F.Dc (R.toCx3 F).zs).a (I.wU u)) → D.what₂.LL) (y : Fin ((A3.side3 F.P1 F.ψ1 (R.toCx3 F).zs).nV A3.A.μ0) → D.what₂.LL), D.what₂.embLL ((F.Dc (R.toCx3 F).zs).Pt (I.wU u) A3.A.μ0 x y) = D.what₂.perCol u (I.tup A3.A.μ0) (D.jN u (I.eNu u x)) (I.jA A3.A.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec y))) → ∃ (Rd : Read D (R.toCx3 F) F.fc (twAt D.what₂.embLL A3.A.v0)) (M : Seam Rd F.cr), HEq Rd.wU I.wU ∧ M.ChainTie ∧ M.GoodPartHasComplexCoordinates ∧ M.RowTie (F.eV (R.toCx3 F).zs) ∧ M.ColNorm ∧ (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ ∧ ∀ (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (Gd : GoodOp St) (hK : St.LevelSubgroupCharacter) (pw : ∀ u, PerW St hK u) (wdD : (F.Dc (R.toCx3 F).zs).Mem → D.what₂.Word) (bR : ∀ x, Fin ((F.Dc (R.toCx3 F).zs).a x) → (D.mem (wdD x)).A.Mram), (∀ u, wdD (I.wU u) = u) → F.Sp (R.toCx3 F).zs = spOf (twAt D.what₂.embLL A3.A.v0) (F.Dc (R.toCx3 F).zs) hK Gd wdD (fun x => pw (wdD x)) bR → (∀ u i, HEq (bR (I.wU u) i) (D.eMu u (D.jN u (I.eNu u (Pi.single i 1))))) → ∀ (t : GA D (D.sp.Y 0)) (c : ℝ), EvalTieT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) St Gd (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c → ∀ (sEE : (R.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (R.toCx3 F).zs).Sp.HH) (sEEc : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (HHX St)) (κS : ℂ), HEq sEE sEEc → κS ≠ 0 → (∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) R.HE.H) (hx : R.HE.e (Tw.out x) ∈ (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true))), sEEc x = Tw.mk (twAt D.what₂.embLL A3.A.v0) (κS • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) St Gd (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c ⟨R.HE.e (Tw.out x), hx⟩)) → ∀ (eE : D.what₂.EE →ₗ[ℂ] R.HE.H), (∀ y, eE (D.jEE (I.eRR y)) = Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) ((R.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y))) → ∀ (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St Gd) (v₀ : (R.MY 0).Vec) (a : ℂ), (∀ x, ((j x : EEC St Gd) : L2X St) =ᵐ[muX St] fun g => a * ev (R.MY 0) v₀ (R.HE.e (eE x)) ((Formalism.L2.SG.RowsJoinPinned.iotaX St h).symm g * t)) → ∀ u, ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (x : D.what₂.EE) (φ : D.what₂.Mu u) (T' : Cu St u hK), colDictL St (pw u).Tr hK T' = ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) → ⟪sEE (M.eR x), (F.fc (R.toCx3 F).zs).Sp.Pu (Rd.wU u) (cjv (twAt D.what₂.embLL A3.A.v0) (M.cφ u φ))⟫_ℂ = cj (twAt D.what₂.embLL A3.A.v0) (κ * ⟪((conjHH St Gd (j x) : HHX St) : L2X St), PuFun St u hK (pw u).Dt T'⟫_ℂ) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F n hOk hSep hCW hPR hSchur hSig S0 p0 C NuC I hDef hLat hPer
  obtain ⟨Rd, hwU, heNu, heRR, hjV, hV0, hIota, hNu, hRR, hDc⟩ :=
    exists_read_of_latTie D G Pl0 I0 T A3 Ks R F n hOk S0 p0 _ C NuC I hDef
  obtain ⟨M⟩ := seam_nonempty D _ _ _ _ _ Rd F.cr
  have hCx := cxFacts_of_prims D G Pl0 I0 T A3 Ks R F n hOk hSep hCW hPR
  have hRow := rows_eq_rows_level D _ _ _ _ _ Rd F.cr M _ hCx (hRR hLat)
  have hCV := chainTie_and_v0Onto D _ _ _ _ _ Rd F.cr M
  refine ⟨Rd, M, hwU, hCV.1 (hDc hPer), hCV.2 hV0,
    ⟨hRow.1, hRow.2.1, ⟨_, Real.sqrt_pos.2 (hCx.pos.2.2 true), hRow.2.2⟩, 1, one_ne_zero, fun y => by
      rw [one_smul]; exact RowB.theta_eq D _ _ _ _ _ Rd F.cr M _ hCx hIota y⟩,
    colNorm_of_nuTie D _ _ _ _ _ Rd F.cr M hNu, thetaMap_referenceTuple_goodPart_onto_rows D _ _ _ _ _ Rd F.cr _ hCx hIota hV0, ?_⟩
  intro St h Gd hK pw wdD bR hwd hSp hbR t c hEv sEE sEEc κS hS hκS hsEEc eE heE j v₀ a hj u
  have hwUe : Rd.wU = I.wU := eq_of_heq hwU
  have heRRe : Rd.eRR = I.eRR := eq_of_heq heRR
  have hME : ∀ x, M.eR x = Tw.mkL (twAt D.what₂.embLL A3.A.v0) R.HE.H (eE x) := by
    have hsp : Submodule.span ℂ (Set.range fun i => D.jEE (D.div.RR.b i)) = ⊤ := D.jEE_basis.2
    have hext := LinearMap.ext_on_range hsp (f := M.eR)
      (g := (Tw.mkL (twAt D.what₂.embLL A3.A.v0) R.HE.H).comp eE) (fun i => ?_)
    · exact fun x => LinearMap.congr_fun hext x
    · obtain ⟨y, hy⟩ := Rd.eRR.surjective (D.div.RR.b i)
      have h1 := heE y
      rw [← heRRe] at h1
      rw [← hy, M.eR_eq y]
      exact (congrArg (Tw.mkL (twAt D.what₂.embLL A3.A.v0) R.HE.H) h1).symm
  have hmem : ∀ x, R.HE.e (eE x) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true) := fun x => by
    have h1 := hRow.1 x
    rw [hME x] at h1
    exact h1
  let e : D.what₂.EE →ₗ[ℂ] R.toRealDat.EEat (R.toRealDat.levR F.lv2 true) :=
    LinearMap.codRestrict _ (R.HE.e ∘ₗ eE) hmem
  have hSch := SchurMove.schur_iotaX D _ (R.MY 0) (R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) St h R.θ _ _ t
    hSchur hSig hCW.base.models.inf (goodPart_le _ _ _ _ _)
  obtain ⟨κ₀, hκ₀, hκe⟩ := sEEofTT_eq_smul_conjHH D _ (R.MY 0) _ St Gd R.ν0 R.fd0
    (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c hSch hEv e j v₀ a hj
  have hkey : ∀ x, (sEEc (M.eR x)).out = (κS * κ₀) • conjHH St Gd (j x) := fun x => by
    have hx : R.HE.e (Tw.out (M.eR x)) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true) :=
      (congrArg (fun z => R.HE.e (Tw.out z) ∈ R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) (hME x)).mpr (hmem x)
    have h2 : (⟨R.HE.e (Tw.out (M.eR x)), hx⟩ : R.toRealDat.EEat (R.toRealDat.levR F.lv2 true)) = e x :=
      Subtype.ext (congrArg (fun z => R.HE.e (Tw.out z)) (hME x))
    exact (congrArg Tw.out (hsEEc (M.eR x) hx)).trans
      (GlobalTheory.Mem.SJ.KernelJoin.smul_apply_eq_of_eq _ h2 κS κ₀ (hκe x))
  have hwd' : ∀ u, wdD (Rd.wU u) = u := fun u => (congrArg wdD (congrFun hwUe u)).trans (hwd u)
  have hbR' := GlobalTheory.Mem.SJ.KernelJoin.heq_of_reindex _ bR (fun u v => D.eMu u (D.jN u v)) Rd.wU I.wU Rd.eNu I.eNu
    hwUe heNu hbR
  exact GlobalTheory.Mem.SJ.PairMain.pair_step D _ _ _ _ _ Rd F.cr M St Gd hK pw wdD bR hwd' hSp hbR' sEE sEEc hS j (κS * κ₀)
    (mul_ne_zero hκS hκ₀) hkey u

section
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX}
  {R : Formalism.L2.RecT ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR R} {P : RowSideFamily ex}
  {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)} {Spf : ∀ Zs, SPer (Dcf Zs)}
  {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem core_latTie {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    (Rl : RealDat3 D A3 Ks) (F : Face3 D A3) (n : ℕ) (hOk : A3.fam3.Ok3 n) (hSep : A3.fam3.TypesSep3)
    (hCh : Rl.WeakCharacterisation F) (hPrim : PrimRows3 Rl F) (hSchur : SchurAll D) (hSig : (D.sp.Y 0).SigOK)
    (Zs : DefSub A3.fam3.amb3) (hzs : (Rl.toCx3 F).zs = Zs)
    (S0 : IndefData (A3.side3 F.P0 F.ψ0 Zs)) (S1 : IndefData (A3.side3 F.P1 F.ψ1 Zs))
    (hs1 : HEq ((Rl.toCx3 F).data F.cr true) S1)
    (Dc : DefCols (A3.side3 F.P1 F.ψ1 Zs)) (hdc : F.Dc Zs = Dc) (Sp : SPer Dc) (hsp : HEq (F.Sp Zs) Sp)
    (p0 : BaseLevelRowSide D) (C : ColData Dc Sp S1) (NuC : ∀ u, Submodule (RingOfIntegers D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL))
    (I : DivisionCompatibilityDataThreeSided D A3 F.P0 F.ψ0 F.P1 F.ψ1 Zs S0 S1 p0 Dc)
    (hDef : DivDef3 D A3 F.P0 F.ψ0 F.P1 F.ψ1 Zs S0 S1 p0 C NuC I)
    (hLat : HLatTie (Formalism.BasicNotions.RowSide.sharp D).RR (A3.indefDown S1).RR (A3.indefDown S1).XE I.eRR)
    (hPt : ∀ (u : D.what₂.Word) (x : Fin (Dc.a (I.wU u)) → D.what₂.LL)
      (y : Fin ((A3.side3 F.P1 F.ψ1 Zs).nV A3.A.μ0) → D.what₂.LL),
      D.what₂.embLL (Dc.Pt (I.wU u) A3.A.μ0 x y) =
        D.what₂.perCol u (I.tup A3.A.μ0) (D.jN u (I.eNu u x)) (I.jA A3.A.μ0 ((rV0 D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec y)))
    (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (Gd : GoodOp St) (hK : St.LevelSubgroupCharacter)
    (pw : ∀ u, PerW St hK u) (wdD : Dc.Mem → D.what₂.Word) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram)
    (hwdD : ∀ u, wdD (I.wU u) = u)
    (hSp : HEq Sp (spOf (twAt D.what₂.embLL A3.A.v0) Dc hK Gd wdD (fun x => pw (wdD x)) bR))
    (hbR : ∀ u i, HEq (bR (I.wU u) i) (D.eMu u (D.jN u (I.eNu u (Pi.single i 1)))))
    (t : GA D (D.sp.Y 0)) (c : ℝ)
    (hEv : EvalTieT (Rl.MY 0) Rl.ν0 Rl.fd0 (Rl.toRealDat.EEat (Rl.toRealDat.levR F.lv2 true)) St Gd
      (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c)
    (sEE : (Rl.toCx3 F).EE →ₗ⋆[ℂ] (F.fc (Rl.toCx3 F).zs).Sp.HH)
    (sEEc : Tw (twAt D.what₂.embLL A3.A.v0) Rl.HE.H →ₗ⋆[ℂ] Tw (twAt D.what₂.embLL A3.A.v0) (HHX St)) (κS : ℂ)
    (hsE : HEq sEE sEEc) (hκ : κS ≠ 0)
    (hsee : ∀ (x : Tw (twAt D.what₂.embLL A3.A.v0) Rl.HE.H)
      (hx : Rl.HE.e (Tw.out x) ∈ (Rl.toRealDat.EEat (Rl.toRealDat.levR F.lv2 true))),
      sEEc x = Tw.mk (twAt D.what₂.embLL A3.A.v0) (κS • sEEofTT (Rl.MY 0) Rl.ν0 Rl.fd0
        (Rl.toRealDat.EEat (Rl.toRealDat.levR F.lv2 true)) St Gd (Formalism.L2.SG.RowsJoinPinned.iotaX St h).toMulEquiv t c
        ⟨Rl.HE.e (Tw.out x), hx⟩))
    (eE : D.what₂.EE →ₗ[ℂ] Rl.HE.H)
    (hRead : ∀ y y', HEq y y' → eE (D.jEE (I.eRR y)) = Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := Rl.HE.H)
      ((Rl.toCx3 F).iC F.cr true A3.A.μ0 (cpt A3.A.v0.embedding y'))) :
    ∃ (Rd : GlobalTheory.Mem.SJ.Read D (Rl.toCx3 F) F.fc (twAt D.what₂.embLL A3.A.v0)) (M : GlobalTheory.Mem.SJ.Seam Rd F.cr),
      HEq Rd.wU I.wU ∧ M.ChainTie ∧ M.GoodPartHasComplexCoordinates ∧ M.RowTie (F.eV (Rl.toCx3 F).zs) ∧ M.ColNorm ∧
      (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ ∧
      ∀ (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St Gd) (v₀ : (Rl.MY 0).Vec) (a : ℂ),
        (∀ x, ((j x : EEC St Gd) : L2X St) =ᵐ[muX St]
          fun g => a * ev (Rl.MY 0) v₀ (Rl.HE.e (eE x)) ((Formalism.L2.SG.RowsJoinPinned.iotaX St h).symm g * t)) →
        ∀ u, ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (x : D.what₂.EE) (φ : D.what₂.Mu u) (T' : Cu St u hK),
          colDictL St (pw u).Tr hK T' = ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) →
          ⟪sEE (M.eR x), (F.fc (Rl.toCx3 F).zs).Sp.Pu (Rd.wU u)
              (GlobalTheory.Mem.SJ.cjv (twAt D.what₂.embLL A3.A.v0) (M.cφ u φ))⟫_ℂ =
            cj (twAt D.what₂.embLL A3.A.v0) (κ * ⟪((conjHH St Gd (j x) : HHX St) : L2X St), PuFun St u hK (pw u).Dt T'⟫_ℂ) := by
  subst hzs
  subst hdc
  obtain rfl := eq_of_heq hs1
  obtain rfl := eq_of_heq hsp
  obtain ⟨Rd, M, hw, h1, h2, h3, h4, hon, hT⟩ :=
    kernelJoin_thetaSurjective_goodPart_latticeCondition D G Pl0 I0 T A3 Ks Rl F n hOk hSep hCh hPrim hSchur hSig S0 p0 C NuC I hDef hLat hPt
  exact ⟨Rd, M, hw, h1, h2, h3, h4, hon, fun j v₀ a hj => hT St h Gd hK pw wdD bR hwdD (eq_of_heq hSp) hbR t c hEv
    sEE sEEc κS hsE hκ hsee eE (fun y => hRead y y HEq.rfl) j v₀ a hj⟩

end

end GlobalTheory.Mem.KJoinLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTermSeriesSummableModerateGrowthUniform
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTermSeriesSummableModerateGrowthUniform
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.Unf.SigConv

variable {D : D7}

theorem mt_jX_eq {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {n : GA D V} (hn : n ∈ flagN d) :
    mt V n ⬝ d.jX = d.jX ⬝ blockX d n := by
  obtain ⟨T, b, -, h1, -⟩ := exists_blocks d hn
  have e3 : blockX d n = 1 + T := by
    rw [blockX, h1, Matrix.mul_add, d.pX_jX, cancel₂ d.pX_jX, Matrix.one_mul]
  rw [e3, h1, Matrix.mul_add, Matrix.mul_one]

theorem blockX_mul_inv {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {n : GA D V} (hn : n ∈ flagN d) :
    blockX d n ⬝ blockX d n⁻¹ = 1 := by
  have h1 := mt_jX_eq d (inv_mem hn)
  have h2 := mt_jX_eq d hn
  have h3 : d.jX ⬝ (blockX d n ⬝ blockX d n⁻¹) = d.jX := by
    rw [← Matrix.mul_assoc, ← h2, Matrix.mul_assoc, ← h1, ← Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, mt_one,
      Matrix.one_mul]
  have h4 : d.pX ⬝ (d.jX ⬝ (blockX d n ⬝ blockX d n⁻¹)) = d.pX ⬝ d.jX := by rw [h3]
  rwa [← Matrix.mul_assoc, d.pX_jX, Matrix.one_mul] at h4

theorem blockX_rat {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) {γ : GA D V} (hγ : γ ∈ GQ V) :
    ∃ B : Matrix (Fin ρ) (Fin ρ) D.host.E, rat B = blockX d γ :=
  mem_ratMx.1 (ratMx_mul (rat_mem d.qX) (ratMx_mul ((mem_GQ_iff V γ).1 hγ) (rat_mem d.e)))

def sumAbs (ψ : AddChar (AF D.host.F) ℂ) {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (W : HSp D)
    (vS : VolM D W.rank ρ) (Ψ : WO V W → ℂ) : ENNReal :=
  ∑' x : Matrix (Fin W.rank) (Fin ρ) D.host.E, ‖term ψ d W vS Ψ x‖ₑ

end GlobalTheory.Unf.SigConv


open GlobalTheory.Unf.SigConv in
theorem GlobalTheory.Unf.sum_term_bound : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (Φ : WO V W → ℂ), IsThetaFunO ψ V W Φ → ∃ (C : ℝ) (A : ℕ), ∀ g h, ∀ n ∈ flagN d, ∑' x : Matrix (Fin W.rank) (Fin ρ) D.host.E, ‖term ψ d W vS (om (n * g, h) Φ) x‖ₑ ≤ ENNReal.ofReal (C * (height V g * quotHeight W h) ^ A) := by
  intro D ψ V V₀ W ρ d χV χW om om' hW hW' vS Φ hΦ
  obtain ⟨C, A, hC⟩ := GlobalTheory.T.mixedCoordinate_absSum_weilTranslate_moderateGrowth D ψ V W χV χW om hW V₀ ρ d vS Φ hΦ
  have hT := fun Ψ (hΨ : IsThetaFunO ψ V W Ψ) => GlobalTheory.T.mixedThetaSeries_terms_laws_unipotent_rational D ψ V V₀ W ρ d χV χW om om' hW hW' vS Ψ hΨ

  have hA : ∀ g h, sumAbs ψ d W vS (om (g, h) Φ) ≤ ENNReal.ofReal (C * (height V g * height W h) ^ A) := by
    intro g h
    refine le_trans ?_ (hC g h 0)
    exact ENNReal.tsum_comp_le_tsum_of_injective (f := fun x : Matrix (Fin W.rank) (Fin ρ) D.host.E =>
        (⟨rat x, rat_mem x⟩ : ratMx D W.rank ρ))
      (fun x y hxy => rat_injective (congrArg Subtype.val hxy))
      (fun y : ratMx D W.rank ρ => ‖d.mixS W ψ vS.μ vS.𝓕 (om (g, h) Φ) y 0‖ₑ)

  have hB : ∀ Ψ, IsThetaFunO ψ V W Ψ → ∀ γ ∈ GQ V, γ ∈ flagN d →
      sumAbs ψ d W vS (om (γ, 1) Ψ) ≤ sumAbs ψ d W vS Ψ := by
    intro Ψ hΨ γ hQ hN
    obtain ⟨B, hB⟩ := blockX_rat d hQ
    have key : ∀ x, term ψ d W vS (om (γ, 1) Ψ) x = term ψ d W vS Ψ (x * B) :=
      fun x => (hT Ψ hΨ).2.1 γ hQ hN x (x * B) (by rw [rat_mul, hB])
    unfold sumAbs
    simp only [key]
    refine ENNReal.tsum_comp_le_tsum_of_injective (f := fun x => x * B) ?_ (fun y => ‖term ψ d W vS Ψ y‖ₑ)
    intro x y hxy
    apply rat_injective
    have hxy' : x * B = y * B := hxy
    have h5 := congrArg (fun z : Matrix (Fin W.rank) (Fin ρ) D.host.E => (rat z : Mx D W.rank ρ) ⬝ blockX d γ⁻¹) hxy'
    simp only [rat_mul, hB, Matrix.mul_assoc, blockX_mul_inv d hN, Matrix.mul_one] at h5
    exact h5

  have hD : ∀ Ψ, IsThetaFunO ψ V W Ψ → ∀ δ ∈ GQ W,
      sumAbs ψ d W vS (om (1, δ⁻¹) Ψ) ≤ sumAbs ψ d W vS Ψ := by
    intro Ψ hΨ δ hQ
    obtain ⟨M, hM⟩ := mem_ratMx.1 ((mem_GQ_iff W δ).1 hQ)
    have key : ∀ x, term ψ d W vS (om (1, δ⁻¹) Ψ) x = term ψ d W vS Ψ (M * x) :=
      fun x => (hT Ψ hΨ).2.2.1 δ⁻¹ (inv_mem hQ) x (M * x)
        (by rw [rat_mul, hM, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul])
    unfold sumAbs
    simp only [key]
    refine ENNReal.tsum_comp_le_tsum_of_injective (f := fun x => M * x) ?_ (fun y => ‖term ψ d W vS Ψ y‖ₑ)
    intro x y hxy
    apply rat_injective
    have hxy' : M * x = M * y := hxy
    have h5 := congrArg (fun z : Matrix (Fin W.rank) (Fin ρ) D.host.E => mt W δ⁻¹ ⬝ (rat z : Mx D W.rank ρ)) hxy'
    simp only [rat_mul, hM, ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul] at h5
    exact h5

  obtain ⟨K, hK, hcov⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D V ρ d.e (isIsoSub_e d)).1
  obtain ⟨c, hc⟩ := exists_height_le_of_isCompact V (hK.image continuous_subtype_val)
  set c' := max c 1 with hc'
  set C₀ := max C 0 with hC₀
  have hc'1 : 1 ≤ c' := le_max_right _ _
  have hC₀0 : 0 ≤ C₀ := le_max_right _ _
  set C' := C₀ * c' ^ A with hC'
  have hC'0 : 0 ≤ C' := mul_nonneg hC₀0 (pow_nonneg (zero_le_one.trans hc'1) _)

  have hN : ∀ g h, ∀ n ∈ flagN d, sumAbs ψ d W vS (om (n * g, h) Φ) ≤
      ENNReal.ofReal (C' * (height V g * height W h) ^ A) := by
    intro g h n hn
    obtain ⟨γ, hγ, k, hk, hnk⟩ := hcov ⟨n, hn⟩
    have hγQ : γ.1 ∈ GQ V := Subgroup.mem_subgroupOf.1 hγ
    have hn' : n = γ.1 * k.1 := congrArg Subtype.val hnk
    have hp : ((n * g, h) : GA D V × GA D W) = (γ.1, 1) * (k.1 * g, h) := by
      rw [hn']; ext <;> simp [mul_assoc]
    have hom : om (n * g, h) Φ = om (γ.1, 1) (om (k.1 * g, h) Φ) := by
      rw [hp, map_mul, Module.End.mul_apply]
    rw [hom]
    refine (hB _ (hW.om_pres _ _ hΦ) γ.1 hγQ γ.2).trans ((hA _ _).trans (ENNReal.ofReal_le_ofReal ?_))
    have hk' : height V k.1 ≤ c' := (hc _ ⟨k, hk, rfl⟩).trans (le_max_left _ _)
    have hkg : height V (k.1 * g) ≤ c' * height V g :=
      (height_mul_le V _ _).trans (mul_le_mul_of_nonneg_right hk' (height_pos V g).le)
    have hx0 : 0 ≤ height V (k.1 * g) * height W h := mul_nonneg (height_pos V _).le (height_pos W h).le
    have hx : height V (k.1 * g) * height W h ≤ c' * (height V g * height W h) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hkg (height_pos W h).le
    calc C * (height V (k.1 * g) * height W h) ^ A ≤ C₀ * (height V (k.1 * g) * height W h) ^ A :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hx0 _)
      _ ≤ C₀ * (c' * (height V g * height W h)) ^ A :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx0 hx _) hC₀0
      _ = C' * (height V g * height W h) ^ A := by rw [mul_pow, hC', mul_assoc]
  refine ⟨C', A, fun g h n hn => ?_⟩

  have hδ : ∀ δ : GQ W, sumAbs ψ d W vS (om (n * g, h) Φ) ≤
      ENNReal.ofReal (C' * (height V g * max (height W (δ.1 * h)) 0) ^ A) := by
    intro δ
    rw [max_eq_left (height_pos W _).le]
    have hp : ((n * g, h) : GA D V × GA D W) = (1, δ.1⁻¹) * (n * g, δ.1 * h) := by
      ext <;> simp [← mul_assoc]
    have hom : om (n * g, h) Φ = om (1, δ.1⁻¹) (om (n * g, δ.1 * h) Φ) := by
      rw [hp, map_mul, Module.End.mul_apply]
    rw [hom]
    exact (hD _ (hW.om_pres _ _ hΦ) δ.1 δ.2).trans (hN g _ n hn)
  let φ : ℝ → ENNReal := fun t => ENNReal.ofReal (C' * (height V g * max t 0) ^ A)
  have hmono : Monotone φ := by
    intro a b hab
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hC'0
    apply pow_le_pow_left₀ (mul_nonneg (height_pos V g).le (le_max_right _ _))
    exact mul_le_mul_of_nonneg_left (max_le_max hab le_rfl) (height_pos V g).le
  have hcont : Continuous φ := by
    refine ENNReal.continuous_ofReal.comp ?_
    fun_prop
  have hinf := hmono.map_ciInf_of_continuousAt (g := fun δ : GQ W => height W (δ.1 * h)) hcont.continuousAt
    ⟨1, by rintro _ ⟨_, rfl⟩; exact one_le_height W _⟩
  have hq : ENNReal.ofReal (C' * (height V g * quotHeight W h) ^ A) = φ (quotHeight W h) := by
    simp only [φ, max_eq_left (quotHeight_pos W h).le]
  change sumAbs ψ d W vS (om (n * g, h) Φ) ≤ _
  rw [hq, quotHeight, hinf]
  exact le_iInf hδ
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaTermSeriesSummableModerateGrowthUniformStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTermSeries_summable_moderateGrowth_uniform : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V V₀ W : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (χV χW : (AE D)ˣ →* Circle) (om : Om V W) (om' : Om V₀ W), IsWeilDatumO ψ V W χV χW om → IsWeilDatumO ψ V₀ W χV χW om' → ∀ (vS : VolM D W.rank ρ) (Φ : WO V W → ℂ), IsThetaFunO ψ V W Φ → ∃ (C : ℝ) (A : ℕ), ∀ g h, ∀ n ∈ flagN d, ∑' x : Matrix (Fin W.rank) (Fin ρ) D.host.E, ‖term ψ d W vS (om (n * g, h) Φ) x‖ₑ ≤ ENNReal.ofReal (C * (height V g * quotHeight W h) ^ A) := by
  first | exact @GlobalTheory.Unf.sum_term_bound | exact GlobalTheory.Unf.sum_term_bound | (intros; apply GlobalTheory.Unf.sum_term_bound <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BottomSphericalCardWeightIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdNBlockTriangular
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx

section
variable {k : Type*} [Field k] {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

theorem prodN_mul_apply {p : ℕ} {h : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} {g : GL (n ⊕ Fin c) k}
    (hh : h.BlockTriangular (lev p)) (hg : InN p g) (r s : n ⊕ Fin c) (hrs : lev p s ≤ lev p r) :
    (h * g.val) r s = h r s := by
  rw [Matrix.mul_apply, Finset.sum_eq_single s]
  · rw [hg s s le_rfl, Matrix.one_apply_eq, mul_one]
  · intro t _ hts
    by_cases hlt : lev p t < lev p r
    · rw [hh hlt, zero_mul]
    · rw [hg t s (hrs.trans (not_lt.mp hlt)), Matrix.one_apply_ne hts, mul_zero]
  · intro hs
    exact absurd (Finset.mem_univ s) hs

theorem prodN_blockTriangular {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : InN p g) :
    g.val.BlockTriangular (lev p) := by
  intro i j hij
  rw [hg i j hij.le, Matrix.one_apply_ne]
  rintro rfl
  exact lt_irrefl _ hij

theorem prodN_inN_of_mem {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ N k n c p) : InN p g := by
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => intro r s _; simp
  | mul x y _ _ hx hy =>
    intro r s hrs
    rw [Units.val_mul, prodN_mul_apply (prodN_blockTriangular hx) hy r s hrs]
    exact hx r s hrs
  | inv x _ hx =>
    intro r s hrs
    have : Invertible x.val := ⟨x.inv, x.inv_val, x.val_inv⟩
    have hb : (x⁻¹).val.BlockTriangular (lev p) := by
      rw [Matrix.coe_units_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular (prodN_blockTriangular hx)
    have key := prodN_mul_apply hb hx r s hrs
    rwa [← Units.val_mul, inv_mul_cancel, Units.val_one, eq_comm] at key

end

end GlobalTheory.RootEx
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BottomSphericalCardWeightIndex
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BottomWt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem relIndex_KO_ne_zero {n : Type} [Fintype n] [DecidableEq n] {J : Subgroup (GL n k)}
    (hJ : J ≤ KO k n) (ho : IsOpen (J : Set (GL n k))) : J.relIndex (KO k n) ≠ 0 := by
  haveI : CompactSpace (KO k n) := isCompact_iff_compactSpace.1 SplitFlip.isCompact_KO
  haveI : Finite ((KO k n) ⧸ J.subgroupOf (KO k n)) :=
    Subgroup.quotient_finite_of_isOpen _ (ho.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem N_one_apply_inl {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {u : GL (n ⊕ Fin c) k}
    (hu : u ∈ N k n c 1) (a b : n) : u.val (Sum.inl a) (Sum.inl b) = (1 : Matrix n n k) a b := by
  have := GlobalTheory.RootEx.prodN_inN_of_mem hu (Sum.inl a) (Sum.inl b) le_rfl
  simpa [Matrix.one_apply] using this

theorem mul_embX_inl {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {u : GL (n ⊕ Fin c) k}
    (hu : u ∈ N k n c 1) (g : GL n k) (a b : n) :
    (u * embX c g).val (Sum.inl a) (Sum.inl b) = g.val a b := by
  simp only [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, embX]
  simp [N_one_apply_inl hu, Matrix.one_apply]

theorem embX_mul_inl {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {u : GL (n ⊕ Fin c) k}
    (hu : u ∈ N k n c 1) (g : GL n k) (a b : n) :
    (embX c g * u).val (Sum.inl a) (Sum.inl b) = g.val a b := by
  simp only [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type, embX]
  simp [N_one_apply_inl hu, Matrix.one_apply]

theorem intM_embX {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {g : GL n k} (h : IntM g.val) :
    IntM (embX c g : GL (n ⊕ Fin c) k).val := by
  rintro (a | a) (b | b)
  · simpa [embX] using h a b
  · simp [embX]
  · simp [embX]
  · by_cases e : a = b
    · subst e; simp [embX]
    · simp [embX, Matrix.one_apply, e]

theorem prX_Cgrp_KO_one (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) :
    prX (Cgrp (KO k (n ⊕ Fin c)) 1) = KO k n := by
  ext g
  rw [mem_prX]
  constructor
  · rintro ⟨u, hu, hC⟩
    have hw : u * embX c g ∈ KO k (n ⊕ Fin c) := by simpa using (mem_Cgrp.1 hC).2
    obtain ⟨h1, h2⟩ := mem_KO.1 hw
    refine mem_KO.2 ⟨fun a b => ?_, fun a b => ?_⟩
    · rw [← mul_embX_inl hu g a b]; exact h1 _ _
    · have hu' : u⁻¹ ∈ N k n c 1 := inv_mem hu
      have e : (u * embX c g)⁻¹ = embX c g⁻¹ * u⁻¹ := by rw [_root_.mul_inv_rev, map_inv]
      rw [← embX_mul_inl hu' g⁻¹ a b, ← e]; exact h2 _ _
  · intro hg
    refine ⟨1, one_mem _, ?_⟩
    rw [one_mul, mem_Cgrp]
    refine ⟨Subgroup.mem_sup_left ⟨g, rfl⟩, ?_⟩
    simp only [inv_one, one_mul, mul_one]
    obtain ⟨h1, h2⟩ := mem_KO.1 hg
    refine mem_KO.2 ⟨intM_embX h1, ?_⟩
    rw [← map_inv]; exact intM_embX h2

theorem reGL_symm_mem_KO_iff {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b)
    {x : GL b k} : (reGL e).symm x ∈ KO k a ↔ x ∈ KO k b := by
  rw [mem_KO, mem_KO, ← map_inv, reGL_symm_val, reGL_symm_val]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using h1 (e.symm i) (e.symm j)
    · simpa using h2 (e.symm i) (e.symm j)
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => h1 _ _, fun i j => h2 _ _⟩

theorem twistChain_lev_zero {s : ℕ} {t κ : Type} [Fintype t] [DecidableEq t] [Fintype κ] [DecidableEq κ]
    (δ : kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → kˣ →* ℂˣ) (c : ℕ) (h : 0 + c = s + 1) :
    ((twistChain s t κ δ hδ η).lev 0 c h).J = KO k _ := by
  ext x
  change (plainFrame (k := k) (stdOrd κ t 0 c h)).conj.symm x ∈ (parahoric (κ ⊕ Fin (s + 1)) (Fin 0 × t) δ hδ).J ↔ _
  rw [mem_parahoric]
  have e : (plainFrame (k := k) (stdOrd κ t 0 c h)).conj.symm x = (reGL (stdOrd κ t 0 c h)).symm x := by
    simp [LatFrame.conj, plainFrame]
    rfl
  rw [e, reGL_symm_mem_KO_iff]
  exact ⟨fun H => H.1, fun H => ⟨H, fun i _ => i.1.elim0⟩⟩

end GlobalTheory.BottomWt

namespace GlobalTheory.QTw
open GlobalTheory.BottomWt

theorem QExt.bottom_one : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (PP : Formalism.L2.DIV.Pl D.host.E) (G : QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle) (E : QExt G χ), Fintype.card (E.Ch 0) = 1 ∧ (∀ α, E.wt 0 α = 1) ∧ E.idx 0 = 1 ∧ ∀ j, j ≤ G.s + 1 + 1 → E.idx j ≠ 0 := by
  intro D c v B PP G χ E
  have hz : E.A 0 G.s (zero_add _) = {1} := E.reps.zero _ _
  have hrep : ∀ α, E.rep 0 G.s (zero_add _) α = 1 := fun α => by
    have := (E.rep_bij 0 G.s (zero_add _)).mapsTo (Set.mem_univ α)
    rw [hz] at this
    exact this
  have hJ0 : ∀ c h, ((G.T E.δ E.tame E.η).lev 0 c h).J = KO G.k _ := fun c h =>
    twistChain_lev_zero E.δ E.tame E.η c h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Fintype.card_eq_one_iff]
    have h1 : (1 : GL _ G.k) ∈ E.A 0 G.s (zero_add _) := by rw [hz]; rfl
    obtain ⟨x, -, -⟩ := (E.rep_bij 0 G.s (zero_add _)).surjOn h1
    exact ⟨x, fun y => (E.rep_bij 0 G.s (zero_add _)).injOn (Set.mem_univ _) (Set.mem_univ _)
      ((hrep y).trans (hrep x).symm)⟩
  · intro α
    rw [E.wt_mid 0 G.s (zero_add _) α, hrep α, hJ0, prX_Cgrp_KO_one, (E.haar 0).2]
    simp
  · rw [E.idx_mid 0 (G.s + 1) (zero_add _), hJ0]
    exact Subgroup.relIndex_self _
  · intro j hj
    rcases Nat.lt_or_ge j (G.s + 2) with hl | hl
    · rw [E.idx_mid j (G.s + 1 - j) (by omega)]
      exact relIndex_KO_ne_zero (E.le _ _ _) (E.reg.2.2 _ _ _).1
    · obtain rfl : j = G.s + 1 + 1 := by omega
      rw [E.idx_top]
      exact relIndex_KO_ne_zero E.leT E.openT

end GlobalTheory.QTw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BottomSphericalCardWeightIndexStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottom_spherical_card_weight_index : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (PP : Formalism.L2.DIV.Pl D.host.E) (G : QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle) (E : QExt G χ), Fintype.card (E.Ch 0) = 1 ∧ (∀ α, E.wt 0 α = 1) ∧ E.idx 0 = 1 ∧ ∀ j, j ≤ G.s + 1 + 1 → E.idx j ≠ 0 := by
  exact @GlobalTheory.QTw.QExt.bottom_one
end
end
