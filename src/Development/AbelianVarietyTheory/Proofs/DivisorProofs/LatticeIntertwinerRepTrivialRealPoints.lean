module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VwNatCastNonneg
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpOfOrder
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepTrivialRealPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepTrivialRealPoints
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

noncomputable section

namespace GlobalTheory.FinLatF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

section Abstract

variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R}
  {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}

theorem normOp_eq_self_of_le (h : IsHeis σ w γ W) (lam : ℕ →* ℂ) {A B : Submodule R X} (hB : SelfDual γ B)
    (hle : B ≤ A) {e : M} (he : Fixes W A e) : normOp lam W A B e = e := by
  obtain ⟨h1, h2⟩ := (sumOp_transversal h A B hB).2.2 hle
  rw [normOp, h1, h2 e he, map_one, inv_one, one_smul]

end Abstract

variable {nS nT : ℕ}

theorem fin_smul_mtF_sub_one {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF σ J}
    (hg : g ∈ GlobalTheory.WeilPartsF.GinfCF σ J) : pairA F 0 1 • (mtF σ J g - 1) = 0 := by
  have h : (mtF σ J g).map (finPartF F E) = 1 := congrArg Units.val (MonoidHom.mem_ker.1 hg)
  apply GlobalTheory.HeisThetaF.smul_eq_zero_of_map_finPartF
  ext i j
  rw [Matrix.map_apply, Matrix.sub_apply, RingHom.map_sub, Matrix.zero_apply, sub_eq_zero]
  refine (congrFun (congrFun h i) j).trans ?_
  rw [← Matrix.map_one (finPartF F E) (finPartF F E).map_zero (finPartF F E).map_one]
  rfl

theorem fin_smul_XFF (x : XFF F E nS nT) : pairA F 0 1 • (x : WOF F E nS nT) = x := by
  have h1 : pairA F 1 0 • (x : WOF F E nS nT) = 0 := GlobalTheory.HeisThetaF.smul_eq_zero_of_map_infPartF x.fin
  have h2 : pairA F 0 1 = 1 - pairA F 1 0 := Prod.ext (by show (0 : Ainf F) = 1 - 1; rw [sub_self])
    (by show (1 : Af F) = 1 - 0; rw [sub_zero])
  rw [h2, sub_smul, one_smul, h1, sub_zero]

theorem rhoFF_real {σ : E →ₐ[F] E} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
    {g : GAF σ JS} {h : GAF σ JT} (hg : g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS) (hh : h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT)
    (x : XFF F E nS nT) : rhoFF σ JS JT (g, h) x = x := by
  apply XFF.ext
  rw [coe_rhoFF]
  have hL : mtF σ JT h * (x : WOF F E nS nT) = x := by
    have : (mtF σ JT h - 1) * (x : WOF F E nS nT) = 0 := by
      rw [← fin_smul_XFF x, Matrix.mul_smul, ← Matrix.smul_mul, fin_smul_mtF_sub_one hh, Matrix.zero_mul]
    rwa [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at this
  have hR : (x : WOF F E nS nT) * mtF σ JS g⁻¹ = x := by
    have : (x : WOF F E nS nT) * (mtF σ JS g⁻¹ - 1) = 0 := by
      rw [← fin_smul_XFF x, Matrix.smul_mul, ← Matrix.mul_smul,
        fin_smul_mtF_sub_one (Subgroup.inv_mem _ hg), Matrix.mul_zero]
    rwa [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at this
  show mtF σ JT h * (x : WOF F E nS nT) * mtF σ JS g⁻¹ = x
  rw [hL, hR]

theorem IsLatRepF.real_triv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS, ∀ h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT, ∀ f, Om (g, h) f = f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ hc Λ w lam Om hR g hg h hh f
  have hσ : ∀ z : E, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have H := isHeis_opFF hσ hS hT hξ hc hR.hw
  have key : Om (g, h) = LinearMap.id := by
    refine LinearMap.ext_on hR.span ?_
    rintro _ ⟨x, e, he, rfl⟩
    have hfix : Om (g, h) e = e := by
      rw [hR.vac _ e he]
      exact normOp_eq_self_of_le H lam (hR.sd' _)
        (by rintro _ ⟨a, ha, rfl⟩; rw [rhoFF_real hg hh]; exact ha) he
    rw [hR.op, rhoFF_real hg hh, hfix, LinearMap.id_apply]
  rw [key, LinearMap.id_apply]

end GlobalTheory.FinLatF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepTrivialRealPointsStatement
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeIntertwinerRep_trivial_realPoints : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ g ∈ GlobalTheory.WeilPartsF.GinfCF σ JS, ∀ h ∈ GlobalTheory.WeilPartsF.GinfCF σ JT, ∀ f, Om (g, h) f = f := by
  first | exact @GlobalTheory.FinLatF.IsLatRepF.real_triv | exact GlobalTheory.FinLatF.IsLatRepF.real_triv | (intros; apply GlobalTheory.FinLatF.IsLatRepF.real_triv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMeanLogAreaLogThetaNormLe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.KerConjMean


open Classical in
private theorem meanInf_avg_le (K M : Type) [Field K] [NumberField K] [Field M] [Algebra ℚ M] [FiniteDimensional ℚ M]
    (i : K →+* M) (h : (M →ₐ[ℚ] ℂ) → ℝ) (h0 : ∀ ρ, 0 ≤ h ρ) :
    Formalism.PairingDivisionLocalBalance.meanInf K (fun p => (∑ᶠ ρ ∈ {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = p.embedding x}, h ρ) /
      Nat.card {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = p.embedding x}) ≤
      2 * ((∑ ρ, h ρ) / (Module.finrank ℚ M : ℝ)) := by
  letI : Algebra K M := i.toAlgebra
  haveI : IsScalarTower ℚ K M := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional K M := FiniteDimensional.right ℚ K M
  have hcard : ∀ σ : K →+* ℂ, (Nat.card {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = σ x} : ℝ) = Module.finrank K M := by
    intro σ
    have h1 := GlobalTheory.ArchMean.sum_comp_algHom K M (fun φ => if φ = σ.toRatAlgHom then 1 else 0)
    rw [Finset.sum_ite_eq' Finset.univ σ.toRatAlgHom, if_pos (Finset.mem_univ _), mul_one, Finset.sum_boole] at h1
    rw [← h1, Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 2
    refine Finset.filter_congr fun ρ _ => ?_
    rw [AlgHom.ext_iff]
    rfl
  have hsum : ∀ σ : K →+* ℂ, (∑ᶠ ρ ∈ {ρ : M →ₐ[ℚ] ℂ | ∀ x, ρ (i x) = σ x}, h ρ) =
      ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = σ), h ρ := by
    intro σ
    rw [← finsum_mem_coe_finset]
    refine finsum_mem_congr ?_ fun _ _ => rfl
    ext ρ
    simp [RingHom.ext_iff]
  have hle : ∑ p : InfinitePlace K, ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = p.embedding), h ρ ≤
      ∑ ρ, h ρ := by
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i) h]
    have hinj : Function.Injective (fun p : InfinitePlace K => p.embedding) := fun p q hpq => by
      rw [← p.mk_embedding, ← q.mk_embedding]
      exact congrArg _ hpq
    rw [← Finset.sum_image (s := Finset.univ) (g := fun p : InfinitePlace K => p.embedding)
      (f := fun σ : K →+* ℂ => ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = σ), h ρ)
      (fun p _ q _ hpq => hinj hpq)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun σ _ _ => Finset.sum_nonneg fun ρ _ => h0 ρ
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hk : (0 : ℝ) < Module.finrank K M := by exact_mod_cast Module.finrank_pos
  have ht : (Module.finrank ℚ K : ℝ) * Module.finrank K M = Module.finrank ℚ M := by
    exact_mod_cast Module.finrank_mul_finrank ℚ K M
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  simp only [hcard, hsum]
  rw [← Finset.sum_div, ← ht]
  generalize (∑ p : InfinitePlace K, ∑ ρ ∈ Finset.univ.filter (fun ρ : M →ₐ[ℚ] ℂ => (ρ : M →+* ℂ).comp i = p.embedding), h ρ) = S at *
  calc _ = 2 * (S / (Module.finrank ℚ K * Module.finrank K M : ℝ)) := by field_simp
    _ ≤ _ := by gcongr

end GlobalTheory.KerConjMean

theorem _root_.GlobalTheory.T.exists_const_mean_logArea_logThetaNorm_le : ∃ C1 : ℝ, 0 < C1 ∧ ∀ D : D7, GlobalTheory.NormSum.Inp D → ∀ δ t0 : ℂ, Crv D D.host.ccK δ → GL3Theta.IsTwoTorsionPointUnkilled D (lat D δ) t0 → ∀ L : ℝ, 1 ≤ L → Real.log D.host.rdE ≤ L → |logDerivativeAtOne D| ≤ L → Formalism.PairingDivisionLocalBalance.meanInf D.what₂.LL (fun p => avg D δ t0 p.embedding (hArea D δ t0)) ≤ C1 * L ∧ Formalism.PairingDivisionLocalBalance.meanInf D.what₂.LL (fun p => avg D δ t0 p.embedding (hTh D δ t0)) ≤ C1 * L := by
  obtain ⟨C₀, hC₀, hmean⟩ := GlobalTheory.T.exists_bound_means_posLog_area_normalisedTheta
  refine ⟨2 * C₀, by positivity, ?_⟩
  intro D hI δ t0 hc ht L hL hrL hdL
  obtain ⟨hdata, htor⟩ := (GlobalTheory.T.admJ_and_torsion_data_algebraic D hI.g1).2 _ δ hc
  have hwp : wpF (lamOf D D.host.ccK δ) t0 ∈ Qbar := by
    refine (htor t0 ⟨2, two_pos, by exact_mod_cast ht.1⟩ fun h0 => ?_).1
    obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
    have h1 := GlobalTheory.ArchNorm.mul_mem_lamOf D _ δ a h0
    rw [ha, mul_comm] at h1
    exact ht.2.1 h1
  have h2 : g2 (lat D δ) ∈ fld D δ t0 := IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
  have h3 : g3 (lat D δ) ∈ fld D δ t0 := IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
  have h4 : wpF (lat D δ) t0 ∈ fld D δ t0 := IntermediateField.subset_adjoin ℚ _ (Or.inr (by simp))
  haveI : FiniteDimensional ℚ (fld D δ t0) := by
    let b := Module.finBasis ℚ D.what₂.LL
    obtain ⟨M, hM1, -, hM⟩ := GlobalTheory.ArchNorm.exists_galois
      (Set.range (fun i => D.what₂.embLL (b i)) ∪ {g2 (lat D δ), g3 (lat D δ), wpF (lat D δ) t0})
      ((Set.finite_range _).union (Set.toFinite _)) (by
        rintro y (⟨i, rfl⟩ | rfl | rfl | rfl)
        · exact mem_algebraicClosure_iff.2
            ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom D.what₂.embLL.toRatAlgHom)
        · exact hdata.2.1
        · exact hdata.2.2
        · exact hwp)
    have hle : fld D δ t0 ≤ M := by
      refine IntermediateField.adjoin_le_iff.2 ?_
      rintro y (⟨y, rfl⟩ | hy)
      · set_option synthInstance.maxHeartbeats 100000 in
        rw [← b.sum_repr y, map_sum]
        refine sum_mem fun i _ => ?_
        rw [map_rat_smul]
        exact M.smul_mem (hM _ (Or.inl ⟨i, rfl⟩))
      · exact hM _ (Or.inr hy)
    exact FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  have htt : ∀ ρ, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj (fld D δ t0) ρ (lat D δ)) (tc D δ t0 ρ) := fun ρ => by
    have h := (hI.t0Ex _ δ hc).2 (fld D δ t0) ρ h2 h3
    unfold tc
    rw [dite_eq_left h]
    exact h.choose_spec
  obtain ⟨hu, hv⟩ := hmean D hI _ δ t0 hc ht L hL hrL hdL (fld D δ t0) h2 h3 h4 (tc D δ t0) htt
  let i : D.what₂.LL →+* fld D δ t0 := D.what₂.embLL.codRestrict (fld D δ t0) (embLL_mem D δ t0)
  refine ⟨(meanInf_avg_le D.what₂.LL (fld D δ t0) i (hArea D δ t0) fun ρ => Real.posLog_nonneg).trans ?_,
    (meanInf_avg_le D.what₂.LL (fld D δ t0) i (hTh D δ t0) fun ρ => Real.posLog_nonneg).trans ?_⟩
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hu zero_le_two
  · rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hv zero_le_two
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformDoubledTargetBoxProduct
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformDoubledTargetBoxProduct
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.DblThetaProd

theorem tsum_prod_mul {α β : Type} (f : α → ℂ) (g : β → ℂ) :
    ∑' p : α × β, f p.1 * g p.2 = (∑' a, f a) * (∑' b, g b) := by
  by_cases hf : Summable f
  · by_cases hg : Summable g
    · exact (tsum_mul_tsum_of_summable_norm ((summable_norm_iff (E := ℂ)).mpr hf)
        ((summable_norm_iff (E := ℂ)).mpr hg)).symm
    · rw [tsum_eq_zero_of_not_summable hg, mul_zero]
      by_cases h0 : ∀ a, f a = 0
      · simp [h0]
      · push_neg at h0
        obtain ⟨a, ha⟩ := h0
        refine tsum_eq_zero_of_not_summable fun hs => hg ?_
        have h1 : Summable fun b => f a * g b :=
          hs.comp_injective (i := fun b => (a, b)) (fun _ _ h => (Prod.ext_iff.mp h).2)
        simpa [ha] using h1.mul_left (f a)⁻¹
  · rw [tsum_eq_zero_of_not_summable hf, zero_mul]
    by_cases h0 : ∀ b, g b = 0
    · simp [h0]
    · push_neg at h0
      obtain ⟨b, hb⟩ := h0
      refine tsum_eq_zero_of_not_summable fun hs => hf ?_
      have h1 : Summable fun a => f a * g b :=
        hs.comp_injective (i := fun a => (a, b)) (fun _ _ h => (Prod.ext_iff.mp h).1)
      simpa [hb] using h1.mul_right (g b)⁻¹

theorem thetaTr_coDbl_boxFun : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JT JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (hA : JA = JTᵀ) (κ : Type) [Fintype κ] (co : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ),
      ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ,
        GlobalTheory.WeilSchrodinger.thetaTr F (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) B.ψ (boxFun φ₁ φ₂) =
          GlobalTheory.DblTargetDelta.deltaT (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  intro F E _ _ _ _ _ σ B hB hstd nS nT JT JA JB ξ hA κ _ co φ₁ _ φ₂ _
  have hψ : ∀ x, ‖B.ψ x‖ = 1 := hstd.1.2.1
  have hc : ∀ x, starRingEnd ℂ (B.ψ x) = B.ψ (-x) := fun x => by
    rw [AddChar.map_neg_eq_inv, Complex.inv_eq_conj (hψ x)]
  funext w
  rw [GlobalTheory.DblTargetDelta.deltaT_apply]
  have he : (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co).e w =
      (Sum.elim (co.e (GlobalTheory.DblTargetDelta.topR w)).1 (co.e (GlobalTheory.DblTargetDelta.botR w)).1,
        Sum.elim (co.e (GlobalTheory.DblTargetDelta.topR w)).2 (-(co.e (GlobalTheory.DblTargetDelta.botR w)).2)) := rfl
  have hn : co.e (-GlobalTheory.DblTargetDelta.botR w) = -(co.e (GlobalTheory.DblTargetDelta.botR w)) := map_neg _ _
  simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, he, hn]
  generalize co.e (GlobalTheory.DblTargetDelta.topR w) = p₁
  generalize co.e (GlobalTheory.DblTargetDelta.botR w) = p₂
  obtain ⟨x₁, y₁⟩ := p₁
  obtain ⟨x₂, y₂⟩ := p₂
  simp only

  set A : (κ → F) → (κ → AdeleRing (𝓞 F) F) := fun b i => algebraMap F (AdeleRing (𝓞 F) F) (b i) with hAdef
  have key : ∀ q : (κ → F) × (κ → F),
      schr B.ψ (Sum.elim x₁ x₂, Sum.elim y₁ (-y₂)) (boxFun φ₁ φ₂)
          (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.sumArrowEquivProdArrow κ κ F).symm q i)) =
        schr B.ψ (x₁, y₁) φ₁ (A q.1) *
          (B.ψ (-(A q.2 ⬝ᵥ y₂) - ⅟(2 : AF F) * (x₂ ⬝ᵥ y₂)) * φ₂ (A q.2 + x₂)) := by
    rintro ⟨a, b⟩
    have h1 : ((fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.sumArrowEquivProdArrow κ κ F).symm (a, b) i)) +
        Sum.elim x₁ x₂) ∘ Sum.inl = A a + x₁ := by
      funext i; simp [hAdef]
    have h2 : ((fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.sumArrowEquivProdArrow κ κ F).symm (a, b) i)) +
        Sum.elim x₁ x₂) ∘ Sum.inr = A b + x₂ := by
      funext i; simp [hAdef]
    simp only [GlobalTheory.WeilM.schr, GlobalTheory.WeilM.boxFun]
    rw [h1, h2, mul_mul_mul_comm, ← AddChar.map_add_eq_mul]
    congr 2
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, mul_neg,
      Finset.sum_neg_distrib, Equiv.sumArrowEquivProdArrow_symm_apply_inl,
      Equiv.sumArrowEquivProdArrow_symm_apply_inr, hAdef]
    ring
  rw [← (Equiv.sumArrowEquivProdArrow κ κ F).symm.tsum_eq]
  refine (tsum_congr key).trans ?_
  refine (tsum_prod_mul (fun a => schr B.ψ (x₁, y₁) φ₁ (A a))
    (fun b => B.ψ (-(A b ⬝ᵥ y₂) - ⅟(2 : AF F) * (x₂ ⬝ᵥ y₂)) * φ₂ (A b + x₂))).trans ?_
  congr 1
  rw [Complex.conj_tsum]
  conv_rhs => rw [← (Equiv.neg (κ → F)).tsum_eq]
  refine tsum_congr fun b => ?_
  have h3 : (fun i => algebraMap F (AdeleRing (𝓞 F) F) ((Equiv.neg (κ → F)) b i)) = -A b := by
    funext i; simp [hAdef]
  simp only [GlobalTheory.WeilM.schr, h3, map_mul, Complex.conj_conj, hc,
    Prod.fst_neg, Prod.snd_neg]
  simp only [neg_dotProduct, dotProduct_neg, neg_neg, neg_add, sub_eq_add_neg, mul_neg]

end GlobalTheory.DblThetaProd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformDoubledTargetBoxProductStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTransform_doubledTarget_boxProduct : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JT JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (hA : JA = JTᵀ) (κ : Type) [Fintype κ] (co : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ),
      ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ,
        GlobalTheory.WeilSchrodinger.thetaTr F (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) B.ψ (boxFun φ₁ φ₂) =
          GlobalTheory.DblTargetDelta.deltaT (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  first | exact @GlobalTheory.DblThetaProd.thetaTr_coDbl_boxFun | exact GlobalTheory.DblThetaProd.thetaTr_coDbl_boxFun | (intros; apply GlobalTheory.DblThetaProd.thetaTr_coDbl_boxFun <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdempotentCharacterValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdempotentCharacterValue
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SwapAtPlace

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem liftV_one_mul (v : Pl (F := F)) (b : AF F) :
    GlobalTheory.LatVac.liftV v 1 * b = GlobalTheory.LatVac.liftV v (evFin F v b) := by
  have h1 : ∀ z : AF F, At (evFin F v) z → GlobalTheory.LatVac.liftV v 1 * z = z := by
    intro z hz
    have := hz (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
    rw [smul_eq_mul] at this
    linear_combination -this
  have h2 := GlobalTheory.LatVac.at_liftV v 1 (b - GlobalTheory.LatVac.liftV v (evFin F v b))
    (by rw [map_sub, GlobalTheory.LatVac.evFin_liftV, sub_self])
  rw [smul_eq_mul] at h2
  have h3 := h1 _ (GlobalTheory.LatVac.at_liftV v (evFin F v b))
  linear_combination h2 + h3

omit [NumberField E] in
theorem smul_eq_map (v : Pl (F := F)) (a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) :
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • a =
      TensorProduct.map (GlobalTheory.LatVac.liftV v) LinearMap.id (compFin F E v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, hx, hy, map_add (f := _), map_add (f := _)]
  | tmul x b =>
    rw [TensorProduct.smul_tmul', smul_eq_mul, liftV_one_mul]
    simp [compFin, Algebra.TensorProduct.map_tmul]

theorem eq_zero_of_piW {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {a : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)}
    (ha : GlobalTheory.LatVac.liftV v (1 : Fv F v) • a = a) (h1 : piW t a = 0) (h2 : piW (t.comp σ) a = 0) : a = 0 := by
  have h0 : compFin F E v a = 0 :=
    split_ext h t (by rw [map_zero]; exact h1) (by rw [map_zero]; exact h2)
  rw [← ha, smul_eq_map, h0, map_zero]

omit [NumberField E] in
theorem one_sub_smul {m n : Type} {v : Pl (F := F)} {u : Matrix m n (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hu : At (evFin F v) u) :
    (1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • u = 0 :=
  hu _ (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])

theorem smul_eq_of_piW {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {v : Pl (F := F)} (t : E →ₐ[F] Fv F v) {m n : Type}
    {u : Matrix m n (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))} (hu : At (evFin F v) u) (g : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))
    (h1 : ∀ i j, piW t g * piW t (u i j) = 0) (h2 : ∀ i j, piW (t.comp σ) g * piW (t.comp σ) (u i j) = 0) :
    g • u = 0 := by
  have h0 := one_sub_smul hu
  rw [sub_smul, one_smul, sub_eq_zero] at h0
  ext i j
  have h3 : GlobalTheory.LatVac.liftV v (1 : Fv F v) • u i j = u i j := (congrFun (congrFun h0 i) j).symm
  refine eq_zero_of_piW h t ?_ ?_ ?_
  · rw [Matrix.smul_apply, smul_comm, h3]
  · rw [Matrix.smul_apply, smul_eq_mul, map_mul, h1]
  · rw [Matrix.smul_apply, smul_eq_mul, map_mul, h2]

theorem swap_at_acts : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ {a' d : ℕ} (J : Matrix (Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl J),
      ((w : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    At (evFin F v) (((w : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) ∧
    ∀ (u₁ u₂ : Matrix (Fin d) (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) u₁ → At (evFin F v) u₂ →
      (u₁.map (piW t) = 0 → u₂.map (piW t) = 0 →
        actB (cA σ) w (Matrix.fromCols u₁ u₂) = Matrix.fromCols (-u₂) (-u₁)) ∧
      (u₁.map (piW (t.comp σ)) = 0 → u₂.map (piW (t.comp σ)) = 0 →
        actB (cA σ) w (Matrix.fromCols u₁ u₂) = Matrix.fromCols u₂ u₁) := by
  intro F E _ _ _ _ _ σ h a' d J v t f hf _ _ ht htσ w hw
  refine ⟨?_, ?_⟩
  · intro r hr
    have h1 : r * GlobalTheory.LatVac.liftV v (1 : Fv F v) = 0 := GlobalTheory.LatVac.at_liftV v 1 r hr
    have h2 : r • f = 0 := by rw [← hf, smul_smul, h1, zero_smul]
    have h3 : r * (1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) = r := by rw [mul_sub, h1, mul_one, sub_zero]
    rw [hw, smul_sub, ← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, Matrix.fromBlocks_smul, smul_smul, h3,
      ← smul_assoc, h2, zero_smul, smul_zero, sub_self]
  · intro u₁ u₂ hu₁ hu₂
    have hact : actB (cA σ) w (Matrix.fromCols u₁ u₂) = Matrix.fromCols (f • u₂) (f • u₁) := by
      unfold actB
      rw [hw, Matrix.fromBlocks_transpose, Matrix.fromCols_mul_fromBlocks]
      simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_smul, Matrix.mul_one, one_sub_smul hu₁,
        one_sub_smul hu₂, zero_add, add_zero]
    have hneg : ∀ u : Matrix (Fin d) (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) u → u.map (piW t) = 0 → f • u = -u := by
      intro u hu h0
      have := smul_eq_of_piW h t hu (f + 1)
        (fun i j => by rw [show piW t (u i j) = 0 from congrFun (congrFun h0 i) j, mul_zero])
        (fun i j => by rw [map_add (f := _), htσ, map_one, neg_add_cancel, zero_mul])
      rwa [add_smul, one_smul, add_eq_zero_iff_eq_neg] at this
    have hpos : ∀ u : Matrix (Fin d) (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), At (evFin F v) u → u.map (piW (t.comp σ)) = 0 → f • u = u := by
      intro u hu h0
      have := smul_eq_of_piW h t hu (f - 1)
        (fun i j => by rw [map_sub, ht, map_one, sub_self, zero_mul])
        (fun i j => by rw [show piW (t.comp σ) (u i j) = 0 from congrFun (congrFun h0 i) j, mul_zero])
      rwa [sub_smul, one_smul, sub_eq_zero] at this
    exact ⟨fun h1 h2 => by rw [hact, hneg _ hu₁ h1, hneg _ hu₂ h2],
      fun h1 h2 => by rw [hact, hpos _ hu₁ h1, hpos _ hu₂ h2]⟩

end GlobalTheory.SwapAtPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdempotentCharacterValueStatement
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_idempotent_character_value : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ {a' d : ℕ} (J : Matrix (Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (v : Pl (F := F)) (t : E →ₐ[F] Fv F v) (f : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)),
    GlobalTheory.LatVac.liftV v (1 : Fv F v) • f = f → f * f = algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) →
    f * cA σ f = -algebraMap (AF F) (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (GlobalTheory.LatVac.liftV v 1) → piW t f = 1 → piW (t.comp σ) f = -1 →
    ∀ w : UG (cA σ) (dbl J),
      ((w : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) =
        Matrix.fromBlocks ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • (1 : Matrix (Fin a') (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))) (f • 1) (f • 1)
          ((1 - GlobalTheory.LatVac.liftV v (1 : Fv F v)) • 1) →
    At (evFin F v) (((w : GL (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) : Matrix (Fin a' ⊕ Fin a') (Fin a' ⊕ Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) - 1) ∧
    ∀ (u₁ u₂ : Matrix (Fin d) (Fin a') (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), At (evFin F v) u₁ → At (evFin F v) u₂ →
      (u₁.map (piW t) = 0 → u₂.map (piW t) = 0 →
        actB (cA σ) w (Matrix.fromCols u₁ u₂) = Matrix.fromCols (-u₂) (-u₁)) ∧
      (u₁.map (piW (t.comp σ)) = 0 → u₂.map (piW (t.comp σ)) = 0 →
        actB (cA σ) w (Matrix.fromCols u₁ u₂) = Matrix.fromCols u₂ u₁) := by
  first | exact @GlobalTheory.SwapAtPlace.swap_at_acts | exact GlobalTheory.SwapAtPlace.swap_at_acts | (intros; apply GlobalTheory.SwapAtPlace.swap_at_acts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoreIsometryOfFixesIsotropicFrame
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoreIsometryOfFixesIsotropicFrame
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

noncomputable section

namespace GlobalTheory.SphEis.CoreIsom

theorem cT_add' {A : Type} [CommRing A] (s : A →+* A) {p q : ℕ} (X Y : Matrix (Fin p) (Fin q) A) :
    cT s (X + Y) = cT s X + cT s Y := by
  ext i k; simp [cT]

theorem unitary_core {A : Type} [CommRing A] (s : A →+* A) {n j m : ℕ} {J : Matrix (Fin n) (Fin n) A}
    {J₀ : Matrix (Fin m) (Fin m) A} {C : Matrix (Fin n) (Fin j) A} {Z : Matrix (Fin n) (Fin m) A}
    {G : Matrix (Fin n) (Fin n) A} {M : Matrix (Fin m) (Fin m) A} {b : Matrix (Fin j) (Fin m) A}
    (hG : cT s G * J * G = J) (hcz : cT s C * J * Z = 0) (hzc : cT s Z * J * C = 0)
    (hcc : cT s C * J * C = 0) (hzz : cT s Z * J * Z = J₀) (hGZ : G * Z = Z * M + C * b) :
    cT s M * J₀ * M = J₀ := by
  have e : cT s (G * Z) * J * (G * Z) = J₀ := by
    calc cT s (G * Z) * J * (G * Z) = cT s Z * (cT s G * J * G) * Z := by
          rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = J₀ := by rw [hG, hzz]
  rw [hGZ, cT_add', Formalism.UG.cT_mul, Formalism.UG.cT_mul] at e
  have h : (cT s M * cT s Z + cT s b * cT s C) * J * (Z * M + C * b) =
      cT s M * (cT s Z * J * Z) * M + cT s M * (cT s Z * J * C) * b +
        (cT s b * (cT s C * J * Z) * M + cT s b * (cT s C * J * C) * b) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]; abel
  rw [h, hzz, hzc, hcz, hcc] at e
  simpa using e

theorem isUnit_of_form {A : Type} [CommRing A] (s : A →+* A) {m : ℕ} {J₀ M : Matrix (Fin m) (Fin m) A}
    (h : cT s M * J₀ * M = J₀) (hJ : IsUnit J₀.det) : IsUnit M := by
  rw [Matrix.isUnit_iff_isUnit_det]
  have e := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at e
  rw [← e] at hJ
  exact isUnit_of_mul_isUnit_right hJ

end GlobalTheory.SphEis.CoreIsom


open GlobalTheory.SphEis.CoreIsom in
theorem GlobalTheory.SphEis.core_isom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ g ∈ fixG σ J C, ∃ (g₀ : GAd σ J₀) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)), (matHom _ σ J g).1 * adMat F Z = adMat F Z * (matHom _ σ J₀ g₀).1 + adMat F C * b ∧ b = adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J g).1 * adMat F Z ∧ (matHom _ σ J₀ g₀).1 = adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * (matHom _ σ J g).1 * adMat F Z ∧ (g ∈ ratPts σ J → g₀ ∈ ratPts σ J₀) := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF g hg
  have hmap : ∀ {a b c d : ℕ} (X : Matrix (Fin a) (Fin b) E) (Y : Matrix (Fin a) (Fin c) E)
      (W : Matrix (Fin c) (Fin d) E), cT (sigR (AF F) σ) (adMat F X) * adMat F Y * adMat F W =
        adMat F (cT (σ : E →+* E) X * Y * W) := by
    intro a b c d X Y W
    rw [adMat, adMat, adMat, GlobalTheory.AutFunCounterexample.cT_map_gen, ← Matrix.map_mul, ← Matrix.map_mul]
  have hgC : (matHom _ σ J g).1 * adMat F C = adMat F C := hg
  have hCJ : adMat F (cT (σ : E →+* E) C * J) * (matHom _ σ J g).1 = adMat F (cT (σ : E →+* E) C * J) := by
    have h1 : (matHom _ σ J g⁻¹).1 * adMat F C = adMat F C * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by
      rw [Matrix.mul_one]
      conv_lhs => rw [← hgC]
      rw [← Matrix.mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one, Matrix.one_mul]
    have h2 := form_mul_of_mul_cols h1
    rwa [inv_inv, Formalism.UG.cT_one, Matrix.one_mul] at h2
  have hsum : adMat F C * adMat F (cT (σ : E →+* E) D * J) + adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
      adMat F D * adMat F (cT (σ : E →+* E) C * J) = 1 := by
    simp only [adMat]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add _),
      ← Matrix.map_add _ (map_add _), hF.sum, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨M, hM⟩ : ∃ M, M = adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * (matHom _ σ J g).1 * adMat F Z := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J g).1 * adMat F Z := ⟨_, rfl⟩
  have hZ : (matHom _ σ J g).1 * adMat F Z = adMat F Z * M + adMat F C * b := by
    calc (matHom _ σ J g).1 * adMat F Z = (adMat F C * adMat F (cT (σ : E →+* E) D * J) +
          adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) + adMat F D * adMat F (cT (σ : E →+* E) C * J)) *
          ((matHom _ σ J g).1 * adMat F Z) := by rw [hsum, Matrix.one_mul]
      _ = adMat F C * (adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J g).1 * adMat F Z) +
          adMat F Z * (adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * (matHom _ σ J g).1 * adMat F Z) +
          adMat F D * (adMat F (cT (σ : E →+* E) C * J) * (matHom _ σ J g).1 * adMat F Z) := by
        simp only [Matrix.add_mul, Matrix.mul_assoc]
      _ = adMat F Z * M + adMat F C * b := by
        rw [hCJ, ← hM, ← hb]
        have h0 : adMat F (cT (σ : E →+* E) C * J) * adMat F Z = 0 := by
          simp only [adMat]; rw [← Matrix.map_mul, hF.cz]; simp
        rw [h0, Matrix.mul_zero, add_zero, add_comm]
  have hG : cT (sigR (AF F) σ) (matHom _ σ J g).1 * adMat F J * (matHom _ σ J g).1 = adMat F J := g.2
  have hMu : cT (sigR (AF F) σ) M * adMat F J₀ * M = adMat F J₀ :=
    unitary_core (sigR (AF F) σ) hG (by rw [hmap, hF.cz]; simp) (by rw [hmap, hF.zc]; simp)
      (by rw [hmap, hF.cc]; simp) (by rw [hmap, hF.zz]) hZ
  have hdet : IsUnit (adMat F J₀).det := by
    rw [adMat, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (Ne.isUnit hF.herm₀.2).map _
  have hMU := isUnit_of_form _ hMu hdet
  let g₀ : GAd σ J₀ := ⟨hMU.unit, by
    show cT (sigR (AF F) σ) (hMU.unit : Matrix (Fin m) (Fin m) (AF F ⊗[F] E)) * adMat F J₀ * hMU.unit = adMat F J₀
    rw [hMU.unit_spec]; exact hMu⟩
  have hg₀ : (matHom _ σ J₀ g₀).1 = M := hMU.unit_spec
  refine ⟨g₀, b, ?_, hb, ?_, ?_⟩
  · rw [hg₀]; exact hZ
  · rw [hg₀]; exact hM
  · intro hr
    have hr' : (show HR (AF F) σ J from g).1 ∈ (Formalism.UG.UJ (σ : E →+* E) J).map (bc (inclR (F := F) (AF F))) := hr
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 hr'
    have hGx : (matHom _ σ J g).1 = adMat F (x : Matrix (Fin n) (Fin n) E) := by
      exact (congrArg Units.val hxg).symm
    have hMM : M = adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J) * (x : Matrix (Fin n) (Fin n) E) * Z) := by
      rw [hM, hGx]; simp only [adMat, Matrix.map_mul]
    have inj : Function.Injective (inclR (F := F) (E := E) (AF F)) := fun a c h =>
      Algebra.TensorProduct.includeRight_injective (AdeleRing.algebraMap_injective (𝓞 F) F) h
    have hM₀ : cT (σ : E →+* E) (J₀⁻¹ * (cT (σ : E →+* E) Z * J) * (x : Matrix (Fin n) (Fin n) E) * Z) * J₀ *
        (J₀⁻¹ * (cT (σ : E →+* E) Z * J) * (x : Matrix (Fin n) (Fin n) E) * Z) = J₀ := by
      apply Matrix.map_injective inj
      show adMat F _ = adMat F _
      rw [← hmap, ← hMM]; exact hMu
    have hM₀U := isUnit_of_form _ hM₀ (Ne.isUnit hF.herm₀.2)
    show (show HR (AF F) σ J₀ from g₀).1 ∈ (Formalism.UG.UJ (σ : E →+* E) J₀).map (bc (inclR (F := F) (AF F)))
    refine Subgroup.mem_map.2 ⟨hM₀U.unit, ?_, Units.ext ?_⟩
    · show cT (σ : E →+* E) (hM₀U.unit : Matrix (Fin m) (Fin m) E) * J₀ * hM₀U.unit = J₀
      rw [hM₀U.unit_spec]; exact hM₀
    · show (hM₀U.unit : Matrix (Fin m) (Fin m) E).map (inclR (F := F) (AF F)) = (matHom _ σ J₀ g₀).1
      rw [hM₀U.unit_spec, hg₀, hMM]
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoreIsometryOfFixesIsotropicFrameStatement
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coreIsometry_of_fixes_isotropicFrame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ g ∈ fixG σ J C, ∃ (g₀ : GAd σ J₀) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)), (matHom _ σ J g).1 * adMat F Z = adMat F Z * (matHom _ σ J₀ g₀).1 + adMat F C * b ∧ b = adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J g).1 * adMat F Z ∧ (matHom _ σ J₀ g₀).1 = adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) * (matHom _ σ J g).1 * adMat F Z ∧ (g ∈ ratPts σ J → g₀ ∈ ratPts σ J₀) := by
  first | exact @GlobalTheory.SphEis.core_isom | exact GlobalTheory.SphEis.core_isom | (intros; apply GlobalTheory.SphEis.core_isom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepSplitPlacePositiveScalar
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepSplitPlacePositiveScalar
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

noncomputable section

namespace GlobalTheory.FinLatSplitF

open GlobalTheory.FinLatF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}

theorem conj_conj_of_cm (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  let τ : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (S := E) (M := ℂ)).toRingHom
  exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])

theorem isSplitIdemF_conj {e : AEF F E} (he : IsSplitIdemF σ e) : IsSplitIdemF σ (cAF σ e) := by
  obtain ⟨h1, h2, v, ε, hpl, hsum⟩ := he
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hpl, ?_⟩
  · rw [GlobalTheory.SplitInvFormF.cAF_cAF ⟨h1, h2, v, ε, hpl, hsum⟩, mul_comm, h2]
  · rw [GlobalTheory.SplitInvFormF.cAF_cAF ⟨h1, h2, v, ε, hpl, hsum⟩, add_comm, hsum]

theorem hOF_actOF (hS : IsHermND σ JS) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    hOF σ JS JT (actOF σ JS JT g h x) (actOF σ JS JT g h y) = hOF σ JS JT x y := by
  have h1 : JS⁻¹.map (incAF F E) * JS.map (incAF F E) = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hS.2)]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  exact GlobalTheory.SymplOInv.sum_unitary (cAF σ) (JT.map (incAF F E)) (mtF σ JT h) (JS⁻¹.map (incAF F E))
    (JS.map (incAF F E)) (mtF σ JS g⁻¹) h1 h.2 (g⁻¹).2 x y

theorem symplOF_actOF (hS : IsHermND σ JS) (ξ₀ : E) (g : GAF σ JS) (h : GAF σ JT) (x y : WOF F E nS nT) :
    symplOF σ JS JT ξ₀ (actOF σ JS JT g h x) (actOF σ JS JT g h y) = symplOF σ JS JT ξ₀ x y := by
  unfold symplOF
  rw [hOF_actOF hS]

theorem gamFF_rhoFF (hS : IsHermND σ JS) (ξ₀ : E) (ψ : AddChar (AF F) ℂ) (p : GAF σ JS × GAF σ JT)
    (x y : XFF F E nS nT) :
    gamFF σ JS JT ξ₀ ψ (rhoFF σ JS JT p x) (rhoFF σ JS JT p y) = gamFF σ JS JT ξ₀ ψ x y := by
  rw [gamFF, gamFF, coe_rhoFF, coe_rhoFF, symplOF_actOF hS]

theorem off_smul_mtF {e : AEF F E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF σ J} (hg : SuppAtF σ e J g) :
    (1 - (e + cAF σ e)) • mtF σ J g = (1 - (e + cAF σ e)) • (1 : Matrix (Fin n) (Fin n) (AEF F E)) := by
  have h : (e + cAF σ e) • (mtF σ J g - 1) = mtF σ J g - 1 := Matrix.ext fun i j => hg i j
  rw [← sub_eq_zero, ← smul_sub, sub_smul, one_smul, h, sub_self]

theorem off_smul_mtF_inv {e : AEF F E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {g : GAF σ J}
    (hg : SuppAtF σ e J g) :
    (1 - (e + cAF σ e)) • mtF σ J g⁻¹ = (1 - (e + cAF σ e)) • (1 : Matrix (Fin n) (Fin n) (AEF F E)) := by
  have h : mtF σ J g * mtF σ J g⁻¹ = 1 := by
    unfold mtF
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  rw [← h, ← Matrix.smul_mul, off_smul_mtF hg, Matrix.smul_mul, Matrix.one_mul]

theorem off_smul_actOF {e : AEF F E} {g : GAF σ JS} {h : GAF σ JT} (hg : SuppAtF σ e JS g) (hh : SuppAtF σ e JT h)
    (u : WOF F E nS nT) : (1 - (e + cAF σ e)) • actOF σ JS JT g h u = (1 - (e + cAF σ e)) • u := by
  unfold actOF
  rw [← Matrix.smul_mul, ← Matrix.smul_mul, off_smul_mtF hh, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul,
    ← Matrix.mul_smul, off_smul_mtF_inv hg, Matrix.mul_smul, Matrix.mul_one]

end GlobalTheory.FinLatSplitF


open GlobalTheory.FinLatF GlobalTheory.FinLatSplitF in
theorem GlobalTheory.FinLatF.isLatRepF_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ e, IsSplitIdemF σ e → ∀ g h, SuppAtF σ e JS g → SuppAtF σ e JT h →
          ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ,
            (∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
              ℓ (heisOF σ JS JT ξ₀ B.ψ u f) = ℓ f) →
            ∀ f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ, ℓ (Om (g, h) f) = (r : ℂ) * ℓ f := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ _ hξ hc Λ w lam Om hL e he g k hg hk
  have hσ : ∀ x, σ (σ x) = x := conj_conj_of_cm hB.cm
  have he' : IsSplitIdemF σ (cAF σ e) := isSplitIdemF_conj he
  have hm : ∀ (a b : AEF F E) (x : XFF F E nS nT), mulFF a (mulFF b x) = (a * b) • x := fun a b x => smul_smul a b x
  have hcm : ∀ (a : AEF F E) (x : XFF F E nS nT),
      rhoFF σ JS JT (g, k) (mulFF a x) = mulFF a (rhoFF σ JS JT (g, k) x) :=
    fun a x => XFF.ext (actOF_smul _ _ _ _)
  obtain ⟨n, hn, hℓ⟩ := GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner_eq (isHeis_opFF hσ hS hT hξ hc hL.hw) lam _ hL.sd hL.span (rhoFF σ JS JT (g, k))
    (gamFF_rhoFF hS ξ₀ B.ψ _) (hL.sd' _) (hL.fin _) (Om (g, k)) (hL.op _) (hL.vac _) (mulFF e) (mulFF (cAF σ e))
    (fun x => by rw [hm, he.1]; rfl) (fun x => by rw [hm, he'.1]; rfl)
    (fun x => by rw [hm, he.2.1, zero_smul]) (fun x => by rw [hm, mul_comm, he.2.1, zero_smul])
    (fun x y => by rw [gamFF, gamFF, coe_mulFF, coe_mulFF, symplOF_smul σ JS JT hσ])
    (fun a ha => (hL.splitStab e he a ha).1) (fun a ha => (hL.splitStab e he a ha).2) (hcm e) (hcm _)
    (fun x => XFF.ext (by
      have := off_smul_actOF hg hk (x : WOF F E nS nT)
      rw [sub_smul, sub_smul, add_smul, add_smul, one_smul, one_smul, ← sub_sub, ← sub_sub] at this
      exact this))
  have hi := hL.fin (g, k)
  have hl := hL.sqrt _ hi (fun q hq hin => hL.splitIdx e he g k hg hk q hq hin)
  refine ⟨(Real.sqrt (idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, k))) : ℕ))⁻¹ * n,
    mul_pos (inv_pos.2 (Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hi)))) (Nat.cast_pos.2 hn),
    fun ℓ h1 f => ?_⟩
  have := hℓ (ℓ ∘ₗ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ).subtype) (fun u m => by
    have hu : ((mulFF (cAF σ e) u : XFF F E nS nT) : WOF F E nS nT) ∈ GlobalTheory.SplitInvFormF.conjHalf σ e nS nT :=
      fun i j => by
        show cAF σ e * (cAF σ e * (u : WOF F E nS nT) i j) = cAF σ e * (u : WOF F E nS nT) i j
        rw [← mul_assoc, he'.1]
    have hwu : (intAF F w • ((mulFF (cAF σ e) u : XFF F E nS nT) : WOF F E nS nT)) ∈
        GlobalTheory.SplitInvFormF.conjHalf σ e nS nT := fun i j => by
      show cAF σ e * (intAF F w * (cAF σ e * (u : WOF F E nS nT) i j)) =
        intAF F w * (cAF σ e * (u : WOF F E nS nT) i j)
      rw [mul_left_comm, ← mul_assoc (cAF σ e), he'.1]
    show ℓ (opFF hc w (mulFF (cAF σ e) u) m : WOF F E nS nT → ℂ) = ℓ m
    rw [coe_opFF, phaseF, GlobalTheory.SplitInvFormF.symplOHF_half he hwu hu, neg_zero, AddChar.map_zero_eq_one, one_smul]
    exact h1 _ hu _ m.2) f
  rw [hl] at this
  push_cast
  exact this

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntertwinerRepSplitPlacePositiveScalarStatement
open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeIntertwinerRep_splitPlace_positive_scalar : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (hc : GlobalTheory.FinLatF.HeisClosedF σ JS JT ξ₀ B.ψ) (Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)) (w : 𝓞 E)
        (lam : ℕ →* ℂ) (Om : GAF σ JS × GAF σ JT →* Module.End ℂ (GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ)),
        GlobalTheory.FinLatF.IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om →
        ∀ e, IsSplitIdemF σ e → ∀ g h, SuppAtF σ e JS g → SuppAtF σ e JT h →
          ∃ r : ℝ, 0 < r ∧ ∀ ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ,
            (∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
              ℓ (heisOF σ JS JT ξ₀ B.ψ u f) = ℓ f) →
            ∀ f : GlobalTheory.WeilPartsF.thetaSubF σ JS JT ξ₀ B.ψ, ℓ (Om (g, h) f) = (r : ℂ) * ℓ f := by
  first | exact @GlobalTheory.FinLatF.isLatRepF_split | exact GlobalTheory.FinLatF.isLatRepF_split | (intros; apply GlobalTheory.FinLatF.isLatRepF_split <;> assumption)
end
end
