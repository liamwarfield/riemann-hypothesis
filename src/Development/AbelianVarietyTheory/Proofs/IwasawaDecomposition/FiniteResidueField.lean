module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JEvExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnramifiedNonsplitExistsConjInvolutionUniformise
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOMulSource
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactActsOnRealVacuaByDetPowers
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteResidueField
open Formalism.BasicNotions GlobalTheory.Mem GlobalTheory.MemN NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.CoefInt

open IsLocalRing Topology

variable {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
  [FiniteDimensional ℚ_[l] K]


omit [FiniteDimensional ℚ_[l] K] in
theorem dvd_iff_norm_le {a : integralClosure ℤ_[l] K} (ha : a ≠ 0) (x : integralClosure ℤ_[l] K) :
    a ∣ x ↔ ‖((x : K) : PadicAlgCl l)‖ ≤ ‖((a : K) : PadicAlgCl l)‖ := by
  constructor
  · rintro ⟨y, rfl⟩
    have hy := (GlobalTheory.mem_integralClosure_padicInt_iff K y).mp y.2
    push_cast
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hy
  · intro h
    have h0 : (a : K) ≠ 0 := fun h0 => ha (Subtype.ext h0)
    have h1 : ((a : K) : PadicAlgCl l) ≠ 0 := fun h1 => h0 (Subtype.ext h1)
    have hm : (x : K) / (a : K) ∈ integralClosure ℤ_[l] K := by
      rw [GlobalTheory.mem_integralClosure_padicInt_iff, IntermediateField.coe_div, norm_div]
      exact div_le_one_of_le₀ h (norm_nonneg _)
    exact ⟨⟨_, hm⟩, Subtype.ext (mul_div_cancel₀ _ h0).symm⟩

theorem isAdic_maximalIdeal : IsAdic (maximalIdeal (integralClosure ℤ_[l] K)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (integralClosure ℤ_[l] K)
  have hind : IsInducing (fun x : integralClosure ℤ_[l] K => ((x : K) : PadicAlgCl l)) :=
    IsInducing.subtypeVal.comp IsInducing.subtypeVal
  have hlt : ‖((π : K) : PadicAlgCl l)‖ < 1 :=
    (GlobalTheory.mem_maximalIdeal_integralClosure_iff K π).1 hπ.not_isUnit
  have hpos : 0 < ‖((π : K) : PadicAlgCl l)‖ :=
    norm_pos_iff.2 fun h => hπ.ne_zero (Subtype.ext (Subtype.ext h))
  have hmem : ∀ (n : ℕ) (x : integralClosure ℤ_[l] K),
      x ∈ maximalIdeal (integralClosure ℤ_[l] K) ^ n ↔
        ‖((x : K) : PadicAlgCl l)‖ ≤ ‖((π : K) : PadicAlgCl l)‖ ^ n := fun n x => by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      dvd_iff_norm_le K (pow_ne_zero n hπ.ne_zero)]
    push_cast
    rw [norm_pow]
  have hn : ∀ s : Set (integralClosure ℤ_[l] K), s ∈ 𝓝 (0 : integralClosure ℤ_[l] K) ↔
      ∃ ε > 0, ∀ x : integralClosure ℤ_[l] K, ‖((x : K) : PadicAlgCl l)‖ < ε → x ∈ s := fun s => by
    rw [hind.nhds_eq_comap, ((Metric.nhds_basis_ball).comap _).mem_iff]
    refine exists_congr fun ε => and_congr_right fun _ => ?_
    simp [Set.subset_def]
  rw [isAdic_iff]
  refine ⟨fun n => ?_, fun s hs => ?_⟩
  · refine AddSubgroup.isOpen_of_mem_nhds
      (maximalIdeal (integralClosure ℤ_[l] K) ^ n).toAddSubgroup (g := 0) ?_
    exact (hn _).2 ⟨_, pow_pos hpos n, fun x hx => (hmem n x).2 hx.le⟩
  · obtain ⟨ε, hε, h⟩ := (hn s).1 hs
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hlt
    exact ⟨n, fun x hx => h x (((hmem n x).1 hx).trans_lt hn)⟩

theorem finite_residueField : Finite (ResidueField (integralClosure ℤ_[l] K)) := by
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful ℤ_[l] ℚ_[l] K
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom ℤ_[l] K
  have : Finite (ResidueField ℤ_[l]) := Finite.of_equiv _ (PadicInt.residueField).symm.toEquiv
  exact Module.finite_of_finite (ResidueField ℤ_[l])

theorem integers_laws : ∀ (l : ℕ) [Fact l.Prime] (LL : Loc.FinExt l), ∃ (_ : IsDiscreteValuationRing ↥(Loc.OL LL)), Module.Finite ℤ_[l] ↥(Loc.OL LL) ∧ IsAdic (IsLocalRing.maximalIdeal ↥(Loc.OL LL)) ∧ IsAdicComplete (IsLocalRing.maximalIdeal ↥(Loc.OL LL)) ↥(Loc.OL LL) ∧ Finite (IsLocalRing.ResidueField ↥(Loc.OL LL)) ∧ IsFractionRing ↥(Loc.OL LL) ↥LL.1 := by
  intro l _ LL
  have := LL.2
  exact ⟨GlobalTheory.isDiscreteValuationRing_integralClosure_padicInt l LL.1,
    GlobalTheory.finite_integralClosure_padicInt l LL.1, isAdic_maximalIdeal LL.1,
    GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local ℤ_[l] (integralClosure ℤ_[l] LL.1),
    finite_residueField LL.1, GlobalTheory.isFractionRing_integralClosure_padicInt l LL.1⟩

end GlobalTheory.CoefInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRankOneIsAvg
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology

namespace GlobalTheory.TypeSum

theorem eq_zero_of_sum_coef {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mx n → (H →L[ℂ] H)} {d : ℝ} (hd : IsFdeg (muG ε) σ d) {m : ℕ} {a y : Fin m → H} (ha : Orthonormal ℂ a)
    (h0 : ∀ g ∈ UJset ε, ∑ j, ⟪y j, σ g (a j)⟫_ℂ = 0) (k : Fin m) : y k = 0 := by
  have h1 : ∫ g, ∑ j, coefOn σ (a j) (y j) g * star (coefOn σ (a k) (y k) g) ∂(muG ε) = 0 := by
    have : ∀ g : UJ ε, ∑ j, coefOn σ (a j) (y j) g * star (coefOn σ (a k) (y k) g) = 0 := fun g => by
      rw [← Finset.sum_mul]
      have := h0 (umat g) g.2
      simp only [coefOn]
      rw [this, zero_mul]
    simp only [this, integral_zero]
  rw [integral_finsetSum _ fun j _ => (hd.2 _ _ _ _).1] at h1
  simp only [fun j => (hd.2 (a j) (y j) (a k) (y k)).2, orthonormal_iff_ite.1 ha, ite_mul, ite_div, one_mul, zero_mul,
    zero_div, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h1
  have hd' : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hd.1.ne'
  exact inner_self_eq_zero.1 ((div_eq_zero_iff.1 h1).resolve_right hd')

theorem exists_rank_one_isAvg : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ a c : H, a ≠ 0 ∧ c ≠ 0 ∧ IsKFin ε σ a ∧ IsKFin ε σ c ∧ IsAvg ε σ (fun w => ⟪c, w⟫_ℂ • a) := by
  intro n ε H _ _ _ σ h
  obtain ⟨hσ, -, -, ⟨d, hd⟩, b, hb, hb0⟩ := id h
  obtain ⟨A1, A2, A3, A4, A5⟩ := isAvg_closure n ε H σ hσ
  obtain ⟨B1, B2, -, -⟩ := kCoef_kAvg n ε H σ hσ
  have he := B1 b hb
  obtain ⟨m, a, c, ha, haK, hcK, hQ⟩ := GlobalTheory.T.compactAverage_kFinite_finiteRank n ε H σ h _ he
  have hQavg := A4 _ (by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1)
  have hc : ∃ k, c k ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply B2 b hb0
    rw [hQ]; simp [hc]
  obtain ⟨k, hk⟩ := hc
  let V : Submodule ℂ (Fin m × Fin m → ℂ) :=
    Submodule.span ℂ ((fun g (p : Fin m × Fin m) => ⟪c p.1, σ g (a p.2)⟫_ℂ) '' UJset ε)
  have hV : ∀ M ∈ V, IsAvg ε σ (fun w => ∑ i, ∑ j, (M (i, j) * ⟪c j, w⟫_ℂ) • a i) := by
    intro M hM
    induction hM using Submodule.span_induction with
    | mem M hM =>
      obtain ⟨g, hg, rfl⟩ := hM
      have := (A2 _ _ hQavg (A2 _ _ (A1 g hg) hQavg).2).2
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hQ, map_sum, map_smul, inner_sum, inner_smul_right, Finset.sum_smul] at this
      simpa only [mul_comm] using this
    | zero => simpa using A5
    | add M N _ _ hM hN =>
      simpa only [Pi.add_apply, add_mul, add_smul, Finset.sum_add_distrib] using (A2 _ _ hM hN).1
    | smul t M _ hM =>
      simpa only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul, mul_assoc] using A3 t _ hM
  have hN : (fun p : Fin m × Fin m => if p.2 = k then ⟪c p.1, c k⟫_ℂ else 0) ∈ V := by
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
    intro φ hφ
    rw [Submodule.mem_dualAnnihilator] at hφ
    have e : ∀ z : Fin m → H, φ (fun p => ⟪c p.1, z p.2⟫_ℂ) =
        ∑ j, ⟪∑ i, star (φ fun q => if (i, j) = q then 1 else 0) • c i, z j⟫_ℂ := fun z => by
      rw [LinearMap.pi_apply_eq_sum_univ, Fintype.sum_prod_type, Finset.sum_comm]
      simp [sum_inner, inner_smul_left, mul_comm]
    have hy := eq_zero_of_sum_coef hd ha (y := fun j => ∑ i, star (φ fun q => if (i, j) = q then 1 else 0) • c i)
      (fun g hg => by rw [← e fun j => σ g (a j)]; exact hφ _ (Submodule.subset_span ⟨g, hg, rfl⟩))
    have := e fun j => if j = k then c k else 0
    simp only [hy, inner_zero_left, Finset.sum_const_zero] at this
    refine Eq.trans (congrArg φ ?_) this
    funext p
    by_cases hp : p.2 = k <;> simp [hp]
  refine ⟨∑ i, ⟪c i, c k⟫_ℂ • a i, c k, fun h0 => hk ?_, hk,
    (kfin ε σ).sum_mem fun i _ => (kfin ε σ).smul_mem _ (haK i), hcK k, ?_⟩
  · have := ha.inner_right_fintype (fun i => ⟪c i, c k⟫_ℂ) k
    rw [h0, inner_zero_right] at this
    exact inner_self_eq_zero.1 this.symm
  · have := hV _ hN
    simp only [ite_mul, zero_mul, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
    simpa only [Finset.smul_sum, smul_smul, mul_comm] using this

end GlobalTheory.TypeSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CastGAMemGFset
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHaarFund
noncomputable section

namespace GlobalTheory.Mem.SJ.HaarMove

open MeasureTheory
open scoped Pointwise

theorem exists_haar_fund {G G' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] [MeasurableSpace G'] [BorelSpace G']
    (μ' : Measure G') [μ'.IsHaarMeasure] (ι : G ≃ₜ* G') (Γ : Subgroup G) (Γ' : Set G')
    (hΓ : ∀ g, g ∈ Γ ↔ ι g ∈ Γ') (F' : Set G') (hm : MeasurableSet F') (hc : ∀ y, ∃ γ ∈ Γ', γ * y ∈ F')
    (hd : ∀ γ ∈ Γ', γ ≠ 1 → μ' ((fun y => γ * y) '' F' ∩ F') = 0) (t : G) :
    ∃ (μ : Measure G) (F : Set G), μ.IsHaarMeasure ∧ IsFundamentalDomain Γ F μ ∧
      ∀ f : G → ℂ, ∫ g in F, f g ∂μ = ∫ x in F', f (ι.symm x * t) ∂μ' := by
  let e : G' ≃ᵐ G := (ι.symm.toHomeomorph.trans (Homeomorph.mulRight t)).toMeasurableEquiv
  have he : ∀ x, e x = ι.symm x * t := fun _ => rfl
  have hes : ∀ g, e.symm g = ι (g * t⁻¹) := fun g => by
    rw [MeasurableEquiv.symm_apply_eq, he]; simp
  have hH : (μ'.map e).IsHaarMeasure := by
    have h1 : (μ'.map ι.symm).IsHaarMeasure := ι.symm.isHaarMeasure_map μ'
    have h2 : μ'.map e = (μ'.map ι.symm).map (· * t) := by
      exact (Measure.map_map (measurable_mul_const t) (map_continuous ι.symm).measurable).symm
    rw [h2]; infer_instance
  refine ⟨μ'.map e, e.symm ⁻¹' F', hH, ?_, fun f => ?_⟩
  · refine IsFundamentalDomain.mk'' (e.symm.measurable hm).nullMeasurableSet (ae_of_all _ fun g => ?_)
      (fun γ hγ => ?_) (fun γ => (measurePreserving_mul_left (μ'.map e) (γ : G)).quasiMeasurePreserving)
    · obtain ⟨γ, hγ, h⟩ := hc (e.symm g)
      refine ⟨⟨ι.symm γ, (hΓ _).2 (by simpa using hγ)⟩, ?_⟩
      show e.symm (ι.symm γ * g) ∈ F'
      rw [hes] at h ⊢
      simpa [mul_assoc] using h
    · have h0 := hd (ι γ) ((hΓ _).1 γ.2) (fun h => hγ (Subtype.ext (ι.injective (by simpa using h))))
      rw [AEDisjoint, MeasurableEquiv.map_apply]
      refine measure_mono_null ?_ h0
      rintro x ⟨⟨g, hg, hx⟩, h2⟩
      refine ⟨⟨e.symm g, hg, ?_⟩, by simpa using h2⟩
      have hx' : (γ : G) * g = ι.symm x * t := hx
      show ι γ * e.symm g = x
      rw [hes, ← map_mul, ← mul_assoc, hx']; simp
  · rw [setIntegral_map_equiv]
    simp only [he]
    congr 2
    ext x; simp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult
open scoped InnerProductSpace TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem schur_of_bridge {D : D7} {V : HSp D} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} (M : DSModel V S)
    (θ : D.what₂.Tau → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (J : Set (GA D V))
    (χ : GA D V → ℂ) (hS : ∀ μ 𝓕, SchurMult θ M J χ μ 𝓕) (hθ : IsInfFam θ)
    (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (fund : Set I.GA)
    (hf : I.IsFundDom (I.muA μf) fund) (ι : GA D V ≃ₜ* I.GA) (hι : ∀ g, g ∈ GQ V ↔ ι g ∈ I.GFset) (t : GA D V)
    (T : MMap M) (hT : T ∈ Mult θ M J χ) (T' : MMap M) (hT' : T' ∈ Mult θ M J χ) :
    ∃ c : ℂ, ∀ v v' : M.Vec, ∫ x, star (T v (ι.symm x * t)) * T' v' (ι.symm x * t) ∂((I.muA μf).restrict fund) =
      c * ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : (I.muA μf).IsHaarMeasure := by
    unfold AutInst.muA Formalism.REAL.muG; infer_instance
  obtain ⟨μ, F, hμ, hF, hint⟩ := exists_haar_fund (I.muA μf) ι (GQ V) I.GFset hι fund hf.1 hf.2.1 hf.2.2 t
  obtain ⟨c, hc⟩ := hS μ F hθ hμ hF T hT T' hT'
  exact ⟨c, fun v v' => (hint fun g => star (T v g) * T' v' g).symm.trans (hc v v').2⟩

end GlobalTheory.Mem.SJ.HaarMove

end
end

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ.SchurMove

theorem castGA_mem_GFset {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA) :
    x ∈ I.GFset ↔ Formalism.L2.SG.RowsJoinPinned.castGA e x ∈ I'.GFset := by
  subst e; rfl

theorem schur_iotaX : ∀ (D : D7) (S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar) (M : DSModel (D.sp.Y 0) S) (E : Submodule ℂ (MMap M)) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : St.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : Formalism.IndefR.Datum.InfFam D) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)), SchurAll D → (D.sp.Y 0).SigOK → IsInfFam θ → E ≤ Mult θ M J χ → (∀ T ∈ E, ∀ T' ∈ E, ∃ c : ℂ, ∀ v v' : M.Vec, ∫ x, star (T v ((Formalism.L2.SG.RowsJoinPinned.iotaX St h).symm x * t)) * T' v' ((Formalism.L2.SG.RowsJoinPinned.iotaX St h).symm x * t) ∂(muX St) = c * ∏ τ, ⟪(v τ : M.H τ), (v' τ : M.H τ)⟫_ℂ) := by
  intro D S M E St h θ J χ t hS hsig hθ hE T hT T' hT'
  haveI := St.B.haar
  haveI := St.B.sf
  have hι : ∀ g, g ∈ GQ (D.sp.Y 0) ↔ Formalism.L2.SG.RowsJoinPinned.iotaX St h g ∈ St.B.I.GFset := by
    intro g
    rw [Formalism.IndefR.RationalEmbedding.iota_rat]
    exact castGA_mem_GFset _ _
  exact GlobalTheory.Mem.SJ.HaarMove.schur_of_bridge M θ J χ (fun μ 𝓕 => hS _ hsig S θ M J χ μ 𝓕) hθ St.B.I St.B.μf
    St.B.fund St.B.fund_spec (Formalism.L2.SG.RowsJoinPinned.iotaX St h) hι t T (hE hT) T' (hE hT')

end GlobalTheory.Mem.SJ.SchurMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodOperatorSpectrum
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerTwOfSmul
noncomputable section

namespace GlobalTheory.Mem.SJ.Pair

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links NumberField GlobalTheory.Mem.SJ
open scoped InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {Bs : DefBase D.what₂.LL} {A : DefAmb Bs} {X : CxData A} {fc : DefSub A → DefFace Bs} {s : Bool}
  {R : Read D X fc s} {cr : Crd A fc}

theorem cpt_single {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} (i : Fin n) :
    (fun k => σ ((Pi.single i 1 : Fin n → K) k)) = (Pi.single i 1 : Fin n → ℂ) := by
  funext k
  by_cases h : k = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

theorem sum_coord_jN (M : Seam R cr) (u : D.what₂.Word) (φ : D.what₂.Mu u) :
    ∑ i, M.cφ u φ i • D.jN u (R.eNu u (Pi.single i 1)) = φ := by
  have h : ∀ i, D.jN u (R.eNu u (Pi.single i 1)) = (M.cφ u).symm (Pi.single i 1) := fun i => by
    rw [← M.cφ_eq]
    exact congrArg _ (cpt_single D.what₂.embLL i)
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [h, ← map_smul, ← map_sum]
  rw [LinearEquiv.symm_apply_eq]
  funext k
  simp [Finset.sum_apply, Pi.single_apply]

theorem sum_coord_eMu (M : Seam R cr) (u : D.what₂.Word) (φ : D.what₂.Mu u) :
    ∑ i, M.cφ u φ i • D.eMu u (D.jN u (R.eNu u (Pi.single i 1))) = D.eMu u φ := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [← map_smul, ← map_sum]
  rw [sum_coord_jN]

theorem sum_coord_heq (M : Seam R cr) (u w : D.what₂.Word) (hw : w = u)
    (b : Fin ((fc X.zs).Dc.a (R.wU u)) → (D.mem w).A.Mram)
    (hb : ∀ i, HEq (b i) (D.eMu u (D.jN u (R.eNu u (Pi.single i 1))))) (φ : D.what₂.Mu u) :
    HEq (∑ i, M.cφ u φ i • b i) (D.eMu u φ) := by
  subst hw
  have : b = fun i => D.eMu w (D.jN w (R.eNu w (Pi.single i 1))) := funext fun i => eq_of_heq (hb i)
  subst this
  exact heq_of_eq (sum_coord_eMu M w φ)

theorem inner_tw_of_smul {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] (s : Bool) (x y : Tw s E) (κ₀ : ℂ) (v : E)
    (hx : Tw.out x = κ₀ • v) : ⟪x, y⟫_ℂ = cj s (starRingEnd ℂ κ₀ * ⟪v, Tw.out y⟫_ℂ) := by
  rw [Tw.inner_eq, hx, inner_smul_left]

end GlobalTheory.Mem.SJ.Pair

end
end

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.SJ.PairMain

theorem op_ramCrd_eq {D : D7} (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (hK : St.LevelSubgroupCharacter) (w u : D.what₂.Word) (hw : w = u)
    (p : PerW St hK w) (q : PerW St hK u) (hpq : HEq p q) {n : ℕ} (b : Fin n → (D.mem w).A.Mram) (c : Fin n → ℂ)
    (φ : (D.mem u).A.Mram) (hc : HEq (∑ i, c i • b i) φ) (T : Cu St u hK)
    (hT : colDictL St q.Tr hK T = ((φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ)) :
    (((p.op (ramCrd b c) : HHX St)) : L2X St) = PuFun St u hK q.Dt T := by
  subst hw
  obtain rfl := eq_of_heq hpq
  obtain rfl := eq_of_heq hc
  have h1 : ramCrd b c = Submodule.inclusion inf_le_left (∑ i, c i • b i) := by
    show Submodule.inclusion inf_le_left (Fintype.linearCombination ℂ b c) = _
    rw [Fintype.linearCombination_apply]
    rfl
  have h2 : (colDict St p.Tr hK p.hI p.hB).symm (Submodule.inclusion inf_le_left (∑ i, c i • b i)) = T := by
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [colDict_apply, hT]
    rfl
  rw [h1]
  simp only [PerW.op, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, h2]
  rfl

theorem pair_step : ∀ (D : D7) (Bs : DefBase D.what₂.LL) (A : DefAmb Bs) (X : CxData A) (fc : DefSub A → DefFace Bs) (s : Bool) (R : Read D X fc s) (cr : Crd A fc) (M : Seam R cr) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp St) (hK : St.LevelSubgroupCharacter) (pw : ∀ u, PerW St hK u) (wdD : (fc X.zs).Dc.Mem → D.what₂.Word) (bR : ∀ x, Fin ((fc X.zs).Dc.a x) → (D.mem (wdD x)).A.Mram), (∀ u, wdD (R.wU u) = u) → (fc X.zs).Sp = spOf s (fc X.zs).Dc hK G wdD (fun x => pw (wdD x)) bR → (∀ u i, HEq (bR (R.wU u) i) (D.eMu u (D.jN u (R.eNu u (Pi.single i 1))))) → ∀ (sEE : X.EE →ₗ⋆[ℂ] (fc X.zs).Sp.HH) (sEEc : X.EE →ₗ⋆[ℂ] Tw s (HHX St)), HEq sEE sEEc → ∀ (j : D.what₂.EE ≃ₗᵢ[ℂ] EEC St G) (κ₀ : ℂ), κ₀ ≠ 0 → (∀ F, Tw.out (sEEc (M.eR F)) = κ₀ • conjHH St G (j F)) → ∀ u, ∃ κ : ℂ, κ ≠ 0 ∧ ∀ (F : D.what₂.EE) (φ : D.what₂.Mu u) (T : Cu St u hK), colDictL St (pw u).Tr hK T = ((D.eMu u φ : (D.mem u).A.Mram) : (D.mem u).C.cls 0 → (D.mem u).C.Y 0 → ℂ) → ⟪sEE (M.eR F), (fc X.zs).Sp.Pu (R.wU u) (cjv s (M.cφ u φ))⟫_ℂ = cj s (κ * ⟪((conjHH St G (j F) : HHX St) : L2X St), PuFun St u hK (pw u).Dt T⟫_ℂ) := by
  intro D Bs A X fc s R cr M St G hK pw wdD bR hw hSp hb
  generalize (fc X.zs).Sp = SP at hSp ⊢
  subst hSp
  intro sEE sEEc hE j κ₀ hκ₀ hout u
  obtain rfl := eq_of_heq hE
  refine ⟨starRingEnd ℂ κ₀, (map_ne_zero _).2 hκ₀, ?_⟩
  intro F φ T hT
  refine (Pair.inner_tw_of_smul (E := HHX St) s (sEE (M.eR F) : Tw s (HHX St))
    ((spOf s (fc X.zs).Dc hK G wdD (fun x => pw (wdD x)) bR).Pu (R.wU u) (cjv s (M.cφ u φ)) : Tw s (HHX St)) κ₀
    ((conjHH St G (j F) : HHX St)) (hout F)).trans ?_
  congr 2
  have hcc : cjVec s _ (cjv s (M.cφ u φ)) = M.cφ u φ := funext fun i => cj_cj s _
  have hP : Tw.out (s := s) ((spOf s (fc X.zs).Dc hK G wdD (fun x => pw (wdD x)) bR).Pu (R.wU u) (cjv s (M.cφ u φ))) =
      (pw (wdD (R.wU u))).op (ramCrd (bR (R.wU u)) (M.cφ u φ)) :=
    (spOf_Pu s (fc X.zs).Dc hK G wdD (fun x => pw (wdD x)) bR (R.wU u) (cjv s (M.cφ u φ))).trans (by rw [hcc])
  have key := op_ramCrd_eq St hK _ u (hw u) _ _ (congr_arg_heq pw (hw u)) (bR (R.wU u)) (M.cφ u φ) _
    (Pair.sum_coord_heq M u _ (hw u) (bR (R.wU u)) (hb u) φ) T hT
  rw [Submodule.coe_inner]
  exact congrArg _ ((congrArg Subtype.val hP).trans key)

end GlobalTheory.Mem.SJ.PairMain
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagRefinementBundleComp
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagRefinementBundleComp
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

variable {ι : Type} {m : ι → ℕ}

theorem mat_chain {K₁ K₂ K₃ : Type} [Field K₁] [Field K₂] [Field K₃] (ψ : K₁ →+* K₂) (ψ' : K₂ →+* K₃)
    (A'' : Mat m K₃) (A' : Mat m K₂) (A : Mat m K₁) (hA' : ∀ τ, (A' τ).det ≠ 0) :
    A'' * (A'.map ψ')⁻¹ * (A' * (A.map ψ)⁻¹).map ψ' = A'' * (A.map (ψ'.comp ψ))⁻¹ := by
  rw [Mat.map_mul, Mat.map_inv, mul_assoc, ← mul_assoc (A'.map ψ')⁻¹,
    Mat.inv_mul (fun τ => by rw [Mat.det_map]; exact (map_ne_zero ψ').2 (hA' τ)), one_mul]
  congr 2

def valAt {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) {K : Type} [Field K]
    (q : Sp K ⟶ M.Z) : (M.O (q (IsLocalRing.closedPoint K))).toSubring →+* K :=
  RatModel.valHom q _ (RatModel.range_eq_singleton q (IsLocalRing.closedPoint K))

theorem valAt_apply {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) {K : Type} [Field K]
    (q : Sp K ⟶ M.Z) (x : (M.O (q (IsLocalRing.closedPoint K))).toSubring) : M.val q x = valAt M q x := rfl

end GlobalTheory.FlagBundle

namespace GlobalTheory.FlagBundle

variable {ι : Type} {m : ι → ℕ} {F : Type} [Field F] {Ω Ω' Ω'' : Type} [Field Ω] [Algebra F Ω] [Field Ω']
  [Algebra F Ω'] [Field Ω''] [Algebra F Ω'']

theorem val_chain {M' : RatModel F Ω'} {M'' : RatModel F Ω''} {φ : Ω →ₐ[F] Ω'}
    {φ' : Ω' →ₐ[F] Ω''} {f' : M''.Z ⟶ M'.Z} (hf' : M'.IsHom M'' φ' f') {K : Type} [Field K] (q : Sp K ⟶ M''.Z)
    {k k' : ι → ℕ} {A'' : Mat m Ω''} {A' : Mat m Ω'} {A : Mat m Ω} (hA' : ∀ τ, (A' τ).det ≠ 0)
    (h2 : Par k' (M''.O (q (IsLocalRing.closedPoint K))).toSubring (A'' * (A'.map φ')⁻¹))
    (h1 : Par k (M'.O (f' (q (IsLocalRing.closedPoint K)))).toSubring (A' * (A.map φ)⁻¹)) :
    (A'' * (A.map (φ'.comp φ))⁻¹).map (M''.val q) =
      (A'' * (A'.map φ')⁻¹).map (M''.val q) * (A' * (A.map φ)⁻¹).map (M'.val (q ≫ f')) := by
  have h1' : Par k (M''.O (q (IsLocalRing.closedPoint K))).toSubring ((A' * (A.map φ)⁻¹).map φ') :=
    h1.map (φ' : Ω' →+* Ω'') fun x hx => hf'.map_mem_O hx
  have e := mat_chain (φ : Ω →+* Ω') (φ' : Ω' →+* Ω'') A'' A' A hA'
  have e2 : (A'' * (A.map (φ'.comp φ))⁻¹) = A'' * (A'.map φ')⁻¹ * (A' * (A.map φ)⁻¹).map φ' := e.symm
  rw [e2, Par.map_mul_of h2 h1' (M''.val q) (valAt M'' q) (valAt_apply M'' q)]
  congr 1
  funext τ
  ext i j
  show M''.val q (φ' ((A' * (A.map φ)⁻¹) τ i j)) = M'.val (q ≫ f') ((A' * (A.map φ)⁻¹) τ i j)
  exact (hf'.val_comp q (IsLocalRing.closedPoint K) ((h1 τ).1 i j)).symm

theorem Refines.comp {M : RatModel F Ω} {M' : RatModel F Ω'} {M'' : RatModel F Ω''} {φ : Ω →ₐ[F] Ω'}
    {f : M'.Z ⟶ M.Z} {φ' : Ω' →ₐ[F] Ω''} {f' : M''.Z ⟶ M'.Z} {k k' k'' : ι → ℕ} {S : Fr M m k}
    {S' : Fr M' m k'} {S'' : Fr M'' m k''} (h1 : Refines S S' φ f) (h2 : Refines S' S'' φ' f') :
    Refines S S'' (φ'.comp φ) (f' ≫ f) := {
  le := le_trans h1.le h2.le
  hom := h1.hom.comp h2.hom
  sub z'' A'' hA'' A hA := by
    obtain ⟨A', hA'⟩ := S'.nonempty (f' z'')
    have e : A'' * (A.map (φ'.comp φ))⁻¹ = A'' * (A'.map φ')⁻¹ * (A' * (A.map φ)⁻¹).map φ' :=
      (mat_chain (φ : Ω →+* Ω') (φ' : Ω' →+* Ω'') A'' A' A (Fr.det_ne hA')).symm
    rw [e]
    exact ((h2.sub z'' A'' hA'' A' hA').mono h1.le le_rfl).mul
      ((h1.sub (f' z'') A' hA' A hA).map (φ' : Ω' →+* Ω'') fun x hx => h2.hom.map_mem_O hx)
  rad z'' g hg := h2.rad z'' (φ g) (h1.rad (f' z'') g hg)
  lifts K _ x A hA h hh := by
    obtain ⟨p', ⟨hp'x, A', hA', hP'⟩, hu1⟩ := h1.lifts K x A hA h hh
    obtain ⟨p'', ⟨hp'', A'', hA'', hP''⟩, hu2⟩ :=
      h2.lifts K p' A' hA' (h * ((A' * (A.map φ)⁻¹).map (M'.val p'))⁻¹) hP'
    have hAx : A ∈ S.S (f (p' (IsLocalRing.closedPoint K))) := by
      have h0 := hA; rw [← hp'x] at h0; exact h0
    have fac : ∀ q : Sp K ⟶ M''.Z, q ≫ f' = p' → ∀ B'' ∈ S''.S (q (IsLocalRing.closedPoint K)),
        (B'' * (A.map (φ'.comp φ))⁻¹).map (M''.val q) =
          (B'' * (A'.map φ')⁻¹).map (M''.val q) * (A' * (A.map φ)⁻¹).map (M'.val p') := by
      intro q hq B'' hB''
      have hq' : p' (IsLocalRing.closedPoint K) = f' (q (IsLocalRing.closedPoint K)) := by
        rw [← hq]; rfl
      have hA'q : A' ∈ S'.S (f' (q (IsLocalRing.closedPoint K))) := by rw [← hq']; exact hA'
      have hAq : A ∈ S.S (f (f' (q (IsLocalRing.closedPoint K)))) := by rw [← hq']; exact hAx
      rw [val_chain h2.hom q (Fr.det_ne hA') (h2.sub _ B'' hB'' A' hA'q) (h1.sub _ A' hA'q A hAq), hq]
    refine ⟨p'', ⟨by rw [← Category.assoc, hp'', hp'x], A'', hA'', ?_⟩, ?_⟩
    · rw [fac p'' hp'' A'' hA'', Mat.mul_inv_rev, ← mul_assoc]
      exact hP''
    · rintro q ⟨hqx, B'', hB'', hPq⟩
      have hq1 : q ≫ f' = p' := by
        refine hu1 (q ≫ f') ⟨by rw [Category.assoc, hqx], ?_⟩
        obtain ⟨A₁, hA₁⟩ := S'.nonempty ((q ≫ f') (IsLocalRing.closedPoint K))
        refine ⟨A₁, hA₁, ?_⟩
        have hA₁' : A₁ ∈ S'.S (f' (q (IsLocalRing.closedPoint K))) := hA₁
        have hAq : A ∈ S.S (f (f' (q (IsLocalRing.closedPoint K)))) := by
          have h0 := hA; rw [← hqx] at h0; exact h0
        have h2s := h2.sub _ B'' hB'' A₁ hA₁'
        rw [val_chain h2.hom q (Fr.det_ne hA₁') h2s (h1.sub _ A₁ hA₁' A hAq)] at hPq
        have hG : Par k' ⊤ ((B'' * (A₁.map φ')⁻¹).map (M''.val q)) :=
          h2s.map_of _ (valAt M'' q) (valAt_apply M'' q)
        have e : h * ((A₁ * (A.map φ)⁻¹).map (M'.val (q ≫ f')))⁻¹ =
            h * ((B'' * (A₁.map φ')⁻¹).map (M''.val q) * (A₁ * (A.map φ)⁻¹).map (M'.val (q ≫ f')))⁻¹ *
              (B'' * (A₁.map φ')⁻¹).map (M''.val q) := by
          rw [Mat.mul_inv_rev, mul_assoc, mul_assoc, Mat.inv_mul hG.det_ne, mul_one]
        rw [e]
        exact (hPq.mono h2.le le_rfl).mul hG
      refine hu2 q ⟨hq1, B'', hB'', ?_⟩
      rw [fac q hq1 B'' hB'', Mat.mul_inv_rev, ← mul_assoc] at hPq
      exact hPq }

end GlobalTheory.FlagBundle

theorem GlobalTheory.FlagBundle.refines_comp : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (Ω'' : Type) [Field Ω''] [Algebra F Ω''] (M'' : RatModel F Ω'') (φ' : Ω' →ₐ[F] Ω'') (f' : M''.Z ⟶ M'.Z) (ι : Type) (m k k' k'' : ι → ℕ) (S : Fr M m k) (S' : Fr M' m k') (S'' : Fr M'' m k''), Refines S S' φ f → Refines S' S'' φ' f' → Refines S S'' (φ'.comp φ) (f' ≫ f) :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h1 h2 => h1.comp h2
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagRefinementBundleCompStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFlagRefinementBundle_comp : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (Ω'' : Type) [Field Ω''] [Algebra F Ω''] (M'' : RatModel F Ω'') (φ' : Ω' →ₐ[F] Ω'') (f' : M''.Z ⟶ M'.Z) (ι : Type) (m k k' k'' : ι → ℕ) (S : Fr M m k) (S' : Fr M' m k') (S'' : Fr M'' m k''), Refines S S' φ f → Refines S' S'' φ' f' → Refines S S'' (φ'.comp φ) (f' ≫ f) := by
  first | exact @GlobalTheory.FlagBundle.refines_comp | exact GlobalTheory.FlagBundle.refines_comp | (intros; apply GlobalTheory.FlagBundle.refines_comp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryRealPointsActFockSubstitution
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryRealPointsActFockSubstitution
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefLift.FockAct

open GlobalTheory.AdTh.SourceBasis GlobalTheory.OrientedHeis

theorem unitMap_mul_mul {m n : ℕ} (B U : Matrix (Fin n) (Fin n) ℂ) (B' H : Matrix (Fin m) (Fin m) ℂ) (i : Fin m)
    (j : Fin n) : unitMap (B * U) (B' * H) i j = ∑ i', ∑ c, (H i' i * U⁻¹ j c) • unitMap B B' i' c := by
  have e : H * Matrix.single i j (1 : ℂ) * U⁻¹ = ∑ i', ∑ c, (H i' i * U⁻¹ j c) • Matrix.single i' c (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single (H * Matrix.single i j (1 : ℂ) * U⁻¹)]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
    congr 1
    rw [Matrix.mul_apply, Finset.sum_eq_single j (fun c _ hc => by simp [Matrix.mul_single_apply_of_ne, hc]) (by simp)]
    simp
  unfold unitMap
  calc _ = B' * (H * Matrix.single i j (1 : ℂ) * U⁻¹) * B⁻¹ := by
        rw [Matrix.mul_inv_rev]; simp only [Matrix.mul_assoc]
    _ = _ := by simp only [e, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D}

theorem pureTensorO_mul_mul (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    (BV U : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ) (BW H : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) (P : Pol D.what₂.Tau W.rank V.rank) :
    pureTensorO ψ θ V W (fun _ => 1) (fun _ => 1) (fun τ => BV τ * U τ) (fun τ => BW τ * H τ) f P =
      pureTensorO ψ θ V W (fun _ => 1) (fun _ => 1) BV BW f (subst (fun τ => (U τ)⁻¹) H P) := by
  have hadd : ∀ f f', IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → IsThetaFunO ψ V W (f + f') := fun f g hf hg => {
    quasi γ w := by simp only [Pi.add_apply, hf.quasi, hg.quasi, mul_add]
    level := by
      obtain ⟨U, hU, h1⟩ := hf.level
      obtain ⟨U', hU', h2⟩ := hg.level
      refine ⟨U ⊓ U', hU.inter hU', fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu.1 h0) w
      have e2 := congrFun (h2 u hu.2 h0) w
      unfold heisO at e1 e2 ⊢
      rw [Pi.add_apply, Pi.add_apply, mul_add, e1, e2]
    cont := hf.cont.add hg.cont
    smooth k L h1 h2 w := (hf.smooth k L h1 h2 w).add (hg.smooth k L h1 h2 w) }
  have hsm : ∀ (a : ℂ) f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (a • f) := fun c f hf => {
    quasi γ w := by rw [Pi.smul_apply, Pi.smul_apply, hf.quasi, smul_eq_mul, smul_eq_mul, mul_left_comm]
    level := by
      obtain ⟨U, hU, h1⟩ := hf.level
      refine ⟨U, hU, fun u hu h0 => ?_⟩
      funext w
      have e1 := congrFun (h1 u hu h0) w
      unfold heisO at e1 ⊢
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm, e1]
    cont := hf.cont.const_smul c
    smooth k L h1 h2 w := contDiff_const.mul (hf.smooth k L h1 h2 w) }
  have hA : ∀ (BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
      (BT : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) i f, IsThetaFunO ψ V W f →
      IsThetaFunO ψ V W (aPlusAll (heisO ψ V W) θ (fun _ => cplxO 1 1) BS BT i f) :=
    fun _ _ _ _ h => aPlus_th hψ hθ _ _ _ h
  have hm : ∀ (BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
      (BT : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) Q,
      IsThetaFunO ψ V W (pureTensorO ψ θ V W (fun _ => 1) (fun _ => 1) BS BT f Q) := fun BS BT Q =>
    GlobalTheory.Ker.FockAlg.pure_mem (P := IsThetaFunO ψ V W) hadd hsm (hA BS BT) hf Q
  have hX : ∀ (BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
      (BT : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) Q v,
      pureTensorO ψ θ V W (fun _ => 1) (fun _ => 1) BS BT f (MvPolynomial.X v * Q) =
        aPlusAll (heisO ψ V W) θ (fun _ => cplxO 1 1) BS BT v
          (pureTensorO ψ θ V W (fun _ => 1) (fun _ => 1) BS BT f Q) :=
    fun BS BT Q v => GlobalTheory.Ker.FockAlg.pure_X_mul (A := aPlusAll (heisO ψ V W) θ (fun _ => cplxO 1 1) BS BT)
      (P := IsThetaFunO ψ V W) hadd hsm (hA BS BT)
      (fun i j _ h => aPlus_comm hψ hθ i.1 _ (s := fun _ => 1) (fun τ => by simp) (fun τ => by simp) j.1 _ h)
      (fun _ _ _ h h' => aPlus_add hψ hθ _ _ _ h h') (fun _ a _ h => aPlus_smul hψ hθ _ _ _ a h) hf Q v
  have h1 := fun BS BT => GlobalTheory.FiniteFock.pureTensorO_one ψ θ V W (fun _ => 1) (fun _ => 1) BS BT f
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq, ← mul_one (MvPolynomial.C a), ← MvPolynomial.smul_eq_C_mul,
      map_smul, map_smul, h1, h1]
  | add P Q hP hQ => rw [map_add (f := _), map_add (f := _), map_add (f := _), hP, hQ]
  | mul_X P v hP =>
    obtain ⟨τ, i, j⟩ := v
    rw [mul_comm, hX, hP, map_mul]
    clear hP
    generalize (subst _ H P : Pol D.what₂.Tau W.rank V.rank) = Q
    rw [subst, MvPolynomial.aeval_X]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, hX]
    simp only [aPlusAll, aPlus]
    rw [unitMap_mul_mul, crea_sum hψ hθ _ (hm _ _ _), Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [crea_sum hψ hθ _ (hm _ _ _), Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [crea_smul hψ hθ τ _ (hm _ _ _) _ True (by simp), if_pos trivial, smul_comm]

theorem om_vac {χS χT : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    (hω : IsWeilDatumO ψ V W χS χT ω) (hθ : IsInfFam θ) (kV : V.SigOK) (kW : W.SigOK)
    {sS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D V τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D W τ) (sT τ))
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (hv : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (sS τ) (sT τ)) f) {g : GA D V} (hg : g ∈ GinfC V)
    {h : GA D W} (hh : h ∈ GinfC W)
    (cS : ∀ τ, sS τ * compAt θ τ (Formalism.L2.Theta.mt V g) = compAt θ τ (Formalism.L2.Theta.mt V g) * sS τ)
    (cT : ∀ τ, sT τ * compAt θ τ (Formalism.L2.Theta.mt W h) = compAt θ τ (Formalism.L2.Theta.mt W h) * sT τ) :
    ∃ c : ℂ, ω (g, h) f = c • f := by
  obtain ⟨x₁, x₂, y₁, y₂, hc⟩ := GlobalTheory.VacuumChar.vacuum_char D ψ θ V W χS χT ω hω hθ kV kW sS sT hS hT
  exact ⟨_, hc f hf hv g hg h hh cS cT⟩

open Classical in
theorem compAt_atTau {S : D.what₂.Tau → SPar} {M : DSModel V S} (hθ : IsInfFam θ) (h : AllPlus M) (τ : D.what₂.Tau)
    (u : Matrix.unitaryGroup (Fin V.rank) ℂ) (ρ : D.what₂.Tau) :
    onb M ρ * (if ρ = τ then (u : Matrix (Fin V.rank) (Fin V.rank) ℂ) else 1) =
      compAt θ ρ (Formalism.L2.Theta.mt V (atTau θ V τ (unfr M τ u))) * onb M ρ := by
  have s := GlobalTheory.PointAtPlaceHom.atTau_spec hθ V τ (h.unfr_mem τ u)
  split_ifs with e
  · subst e
    have e1 : compAt θ ρ (Formalism.L2.Theta.mt V (atTau θ V ρ (unfr M ρ u))) = unfr M ρ u := s.2.1
    rw [e1, unfr, onb, Matrix.mul_nonsing_inv_cancel_right _ _ (fr_det M ρ)]
  · have e1 : compAt θ ρ (Formalism.L2.Theta.mt V (atTau θ V τ (unfr M τ u))) = 1 := s.2.2 ρ e
    rw [e1, Matrix.mul_one, Matrix.one_mul]

theorem compAt_one (B : Matrix (Fin V.rank) (Fin V.rank) ℂ) (ρ : D.what₂.Tau) :
    B * 1 = compAt θ ρ (Formalism.L2.Theta.mt V 1) * B := by
  have e1 : compAt θ ρ (Formalism.L2.Theta.mt V 1) = 1 := GlobalTheory.PointAtPlaceHom.infMat_one V (θ ρ)
  rw [e1, Matrix.mul_one, Matrix.one_mul]

theorem om_ptOf {χS χT : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    {S S' : D.what₂.Tau → SPar} {M : DSModel V S} {M' : DSModel W S'} {f : WO V W → ℂ}
    (hω : IsWeilDatumO ψ V W χS χT ω) (hθ : IsInfFam θ) (kV : V.SigOK) (kW : W.SigOK) (hM : AllPlus M)
    (hM' : AllPlus M') (hf : IsThetaFunO ψ V W f)
    (hv : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) f) {g : GA D V} (hg : g ∈ GinfC V)
    {h : GA D W} (hh : h ∈ GinfC W) (U : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (H : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ)
    (hU : ∀ ρ, onb M ρ * U ρ = compAt θ ρ (Formalism.L2.Theta.mt V g) * onb M ρ)
    (hH : ∀ ρ, onb M' ρ * H ρ = compAt θ ρ (Formalism.L2.Theta.mt W h) * onb M' ρ) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ P, ω (g, h) (ptOf ψ θ M M' f P) = c • ptOf ψ θ M M' f (subst (fun ρ => (U ρ)⁻¹) H P) := by
  have e1 : cart M = fun _ => 1 := funext hM.cart
  have e2 : cart M' = fun _ => 1 := funext hM'.cart
  unfold ptOf
  rw [e1, e2] at hv ⊢
  obtain ⟨c, c0, hc⟩ : ∃ c : ℂ, c ≠ 0 ∧ ω (g, h) f = c • f := by
    by_cases f0 : f = 0
    · exact ⟨1, one_ne_zero, by rw [f0, map_zero, smul_zero]⟩
    obtain ⟨c, e⟩ := om_vac hω hθ kV kW (sS := fun _ => 1) (sT := fun _ => 1)
      (fun τ => ⟨by simp, by simp, by simpa using hM.posDef τ⟩) (fun τ => ⟨by simp, by simp, by simpa using hM'.posDef τ⟩)
      hf hv hg hh (fun τ => by simp) (fun τ => by simp)
    refine ⟨c, fun c0 => f0 ?_, e⟩
    rw [c0, zero_smul] at e
    have e' := congrArg (ω (g, h)⁻¹) e
    rwa [map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at e'
  refine ⟨c, c0, fun P => ?_⟩
  rw [(om_pureTensorO D ψ θ V W χS χT ω hω hθ (fun _ => 1) (fun _ => 1) (onb M) (fun ρ => onb M ρ * U ρ)
    (fun _ => 1) (fun _ => 1) (onb M') (fun ρ => onb M' ρ * H ρ) g h (fun τ => by simp) (fun τ => by simp) hU hH f hf P).2,
    hc, GlobalTheory.FiniteFock.pureTensorO_smul, pureTensorO_mul_mul hω.std hθ _ _ _ _ hf]

theorem fock_act : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (θ : InfFam D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ), IsWeilDatumO ψ V W χS χT ω → IsInfFam θ → V.SigOK → W.SigOK → AllPlus M → AllPlus M' → IsThetaFunO ψ V W f → (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) f) → ∀ τ, (∀ g : Matrix.unitaryGroup (Fin V.rank) ℂ, ∃ c : ℂ, c ≠ 0 ∧ ∀ P, ω (atTau θ V τ (unfr M τ g), 1) (ptOf ψ θ M M' f P) = c • ptOf ψ θ M M' f (colSub W.rank τ g P)) ∧ ∀ u : Matrix.unitaryGroup (Fin W.rank) ℂ, ∃ c : ℂ, c ≠ 0 ∧ ∀ P, ω (1, atTau θ W τ (unfr M' τ u)) (ptOf ψ θ M M' f P) = c • ptOf ψ θ M M' f (rowSub V.rank τ u P) := by
  classical
  intro D ψ V W χS χT ω θ S S' M M' f hω hθ kV kW hM hM' hf hv τ
  refine ⟨fun g => ?_, fun u => ?_⟩
  · have := om_ptOf hω hθ kV kW hM hM' hf hv (GlobalTheory.PointAtPlaceHom.atTau_mem V τ _) (one_mem _) _ (fun _ => 1)
      (compAt_atTau hθ hM τ g) (fun ρ => compAt_one _ ρ)
    have e : (fun ρ => (if ρ = τ then (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) else 1)⁻¹) =
        fun ρ => if ρ = τ then star (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) else 1 := by
      funext ρ
      split_ifs
      · exact Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.1 g.2)
      · exact inv_one
    rw [e] at this
    exact this
  · have := om_ptOf hω hθ kV kW hM hM' hf hv (one_mem _) (GlobalTheory.PointAtPlaceHom.atTau_mem W τ _) (fun _ => 1) _
      (fun ρ => compAt_one _ ρ) (compAt_atTau hθ hM' τ u)
    simp only [inv_one] at this
    exact this

end GlobalTheory.DefLift.FockAct

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryRealPointsActFockSubstitutionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory GlobalTheory.DefLift GlobalTheory.Chain
open scoped ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteUnitary_realPoints_act_fock_substitution : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (θ : InfFam D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (f : WO V W → ℂ), IsWeilDatumO ψ V W χS χT ω → IsInfFam θ → V.SigOK → W.SigOK → AllPlus M → AllPlus M' → IsThetaFunO ψ V W f → (∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) f) → ∀ τ, (∀ g : Matrix.unitaryGroup (Fin V.rank) ℂ, ∃ c : ℂ, c ≠ 0 ∧ ∀ P, ω (atTau θ V τ (unfr M τ g), 1) (ptOf ψ θ M M' f P) = c • ptOf ψ θ M M' f (colSub W.rank τ g P)) ∧ ∀ u : Matrix.unitaryGroup (Fin W.rank) ℂ, ∃ c : ℂ, c ≠ 0 ∧ ∀ P, ω (1, atTau θ W τ (unfr M' τ u)) (ptOf ψ θ M M' f P) = c • ptOf ψ θ M M' f (rowSub V.rank τ u P) := by
  first | exact @GlobalTheory.DefLift.FockAct.fock_act | exact GlobalTheory.DefLift.FockAct.fock_act | (intros; apply GlobalTheory.DefLift.FockAct.fock_act <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocUniqueOfIsSplitAt
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU.AU

theorem isLoc_unique_of_isSplitAt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : AU E n)
    (w : HeightOneSpectrum (𝓞 E)) (σ σ' : Irr (GL (Fin n) (w.adicCompletion E))),
    IsSplitAt w → π.IsLoc w σ → π.IsLoc w σ' → σ = σ' := by
  intro E _ _ _ n π w σ σ' hw h h'
  obtain ⟨U, rfl⟩ := AU.mk_surjective π
  obtain ⟨σ, rfl⟩ := Quotient.exists_rep (s := SmIrr.setoid _) σ
  obtain ⟨σ', rfl⟩ := Quotient.exists_rep (s := SmIrr.setoid _) σ'
  obtain ⟨e, he⟩ := GlobalTheory.T.splitPlace_unitaryLocalPoints_equiv_GL E n w hw
  obtain ⟨r, -, -, hc⟩ := GlobalTheory.T.exists_continuous_retraction_onto_unitaryLocalPoints E n w
  let s : GL (Fin n) (w.adicCompletion E) →* UA E n :=
    (locU n w).subtype.comp e.symm.toMulEquiv.toMonoidHom
  have hs : ∀ y, cLoc w (s y) = y := fun y => by
    have := he (e.symm y)
    rw [e.apply_symm_apply] at this
    exact this.symm
  have key : ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion E)), U.IsLocComp w τ →
      ∃ f : τ.ρ.IntertwiningMap (U.rep.comp s), f ≠ 0 := by
    rintro τ ⟨-, f, h0, hf, h2⟩
    refine ⟨⟨f.codRestrict U.V hf, fun y => LinearMap.ext fun v => Subtype.ext ?_⟩, fun e0 => h0 ?_⟩
    · have h3 := h2 (e.symm y) v
      have hy : ((cLoc w).comp (locU n w).subtype) (e.symm y) = y := hs y
      rw [hy] at h3
      exact h3
    · exact LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun e0 v)
  obtain ⟨f, hf⟩ := key σ h
  obtain ⟨f', hf'⟩ := key σ' h'
  have hcomm : ∀ g : UA E n, ∃ u, ∀ y, Commute ((s u)⁻¹ * g) (s y) := fun g =>
    ⟨e (r g), fun y => by
      have : s (e (r g)) = (r g : UA E n) := congrArg Subtype.val (e.symm_apply_apply (r g))
      rw [this]
      exact hc g (e.symm y)⟩
  exact Quotient.sound ((GlobalTheory.T.irreducibleRep_isotypic_of_centraliser_factor _ _ _ _ _ U.rep s σ.ρ σ'.ρ U.isIrreducible_rep σ.irred σ'.irred hcomm f hf).2 f' hf')

end GlobalTheory.DefU.AU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAffineSpaceCoveredMorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAffineSpaceCoveredMorphism
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

namespace GlobalTheory.FlagBundle

theorem ProjBundle.affCover (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (J : Type) [Fintype J] [DecidableEq J]
    (EE : M.Lat J) (s : J → Ω') (h : ProjBundle M EE M' φ f s) : AffCover M M' φ f (Fintype.card J - 1) := by
  refine ⟨h.hom, fun z' => ?_⟩
  obtain ⟨U₀, b, hz, hb, hE⟩ := EE.loc (f z')
  obtain ⟨W, hW, hzW, hle⟩ := exists_isAffineOpen_mem_and_subset (U := U₀) hz
  obtain ⟨hc, hch⟩ := h.chart W b hW ⟨_, hzW⟩ fun z hzz => hE z (hle hzz)
  obtain ⟨i, hi⟩ := hc z' hzW
  obtain ⟨U, hU, hUe, hR⟩ := hch i hi.1
  have hcard : Fintype.card {j // j ≠ i} = Fintype.card J - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  let e : Fin (Fintype.card J - 1) ≃ {j // j ≠ i} := (Fintype.equivFinOfCardEq hcard).symm
  have hmem : ∀ y, y ∈ U ↔ f y ∈ W ∧ M'.Div ((b.map φ).mulVec s) i y := fun y =>
    Set.ext_iff.1 hUe y
  refine ⟨U, W, fun k => (b.map φ).mulVec s (e k).1 / (b.map φ).mulVec s i, hU, hW, (hmem z').2 ⟨hzW, hi⟩,
    fun y hy => ((hmem y).1 hy).1, fun P hP => ?_, ?_⟩
  · apply MvPolynomial.rename_injective e e.injective
    rw [map_zero]
    refine (h.gen b hb i).2 _ ?_
    rw [MvPolynomial.eval₂_rename]
    exact hP
  · rw [hR]
    refine le_antisymm (Algebra.adjoin_le ?_) (Algebra.adjoin_mono (Set.union_subset_union_right _ ?_))
    · rintro x (hx | ⟨j, rfl⟩)
      · exact Algebra.subset_adjoin (Or.inl hx)
      · by_cases hj : j = i
        · subst hj
          show _ / _ ∈ _
          rw [div_self hi.1]
          exact one_mem _
        · refine Algebra.subset_adjoin (Or.inr ⟨e.symm ⟨j, hj⟩, ?_⟩)
          simp only [Equiv.apply_symm_apply]
    · rintro _ ⟨k, rfl⟩
      exact ⟨(e k).1, rfl⟩

end GlobalTheory.FlagBundle
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAffineSpaceCoveredMorphismStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAffineSpaceCoveredMorphism : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (J : Type) [Fintype J] [DecidableEq J] (EE : M.Lat J) (s : J → Ω'), ProjBundle M EE M' φ f s → AffCover M M' φ f (Fintype.card J - 1) := by
  first | exact @GlobalTheory.FlagBundle.ProjBundle.affCover | exact GlobalTheory.FlagBundle.ProjBundle.affCover | (intros; apply GlobalTheory.FlagBundle.ProjBundle.affCover <;> assumption)
end
end
