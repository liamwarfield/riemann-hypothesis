module

public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.IntegralMul
public import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutProdA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumTransportAdelicSchwartzThetaTrans
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelEvaluationBijectiveSchwartz

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LatRepBI
noncomputable section

open scoped TensorProduct Matrix Topology
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.IndefR.DatumF GlobalTheory.FinLatF GlobalTheory.FinWeil

namespace PositivityTheory.ThKW.LatB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {nS nT : ℕ} {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)}

theorem fin_smul_self (u : XFF F E nS nT) :
    algebraMap (AF F) (AEF F E) (pairA F 0 1) • (u : WOF F E nS nT) = u := by
  have h0 : pairA F 1 0 • (u : WOF F E nS nT) = 0 := GlobalTheory.HeisThetaF.smul_eq_zero_of_map_infPartF (XFF.fin u)
  have h := PositivityTheory.ThKW.LatA.dec (u : WOF F E nS nT)
  rw [h0, zero_add] at h
  rw [algebraMap_smul]
  exact h.symm

theorem int_smul_mem {a : AEF F E} (ha : finPartF F E a ∈ hatO (F := F) E) {u : XFF F E nS nT}
    (hu : u ∈ (latF F E nS nT Λ).toAddSubgroup) : a • u ∈ (latF F E nS nT Λ).toAddSubgroup := by
  show ((a • u : XFF F E nS nT) : WOF F E nS nT) ∈ latOF F E nS nT Λ
  rw [XFF.coe_asmul, ← fin_smul_self u, smul_smul, mul_comm, fin_mul_eq]
  exact liftF_smul_mem ha hu

theorem int_smul_mem_map {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
    (p : GAF σ JS × GAF σ JT) {a : AEF F E} (ha : finPartF F E a ∈ hatO (F := F) E) {u : XFF F E nS nT}
    (hu : u ∈ ((latF F E nS nT Λ).map (rhoFF σ JS JT p)).toAddSubgroup) :
    a • u ∈ ((latF F E nS nT Λ).map (rhoFF σ JS JT p)).toAddSubgroup := by
  obtain ⟨y, hy, rfl⟩ := hu
  refine ⟨a • y, int_smul_mem ha hy, XFF.ext ?_⟩
  rw [coe_rhoFF, XFF.coe_asmul, XFF.coe_asmul, coe_rhoFF, actOF_smul]

theorem mul_e_zero {a e : AEF F E} (ha : finPartF F E a = 0)
    (hf : algebraMap (AF F) (AEF F E) (pairA F 0 1) * e = e) : a * e = 0 := by
  rw [← hf, ← mul_assoc, mul_comm a, fin_mul_eq, ha, map_zero, zero_mul]

theorem finPart_cAF_zero {a : AEF F E} (ha : finPartF F E a = 0) : finPartF F E (cAF σ a) = 0 := by
  have hr : infPartF F E (algebraMap (AF F) (AEF F E) (pairA F 1 0)) = 1 := rfl
  have hf : finPartF F E (algebraMap (AF F) (AEF F E) (pairA F 1 0)) = 0 := TensorProduct.zero_tmul _ _
  have e : a = algebraMap (AF F) (AEF F E) (pairA F 1 0) * a := by
    rw [← sub_eq_zero]
    refine GlobalTheory.SplitDetCharF.adele_tensor_ext _ ?_ ?_
    · rw [map_sub, map_mul, hr, one_mul, sub_self]
    · rw [map_sub, map_mul, hf, ha, zero_mul, sub_self]
  rw [e, map_mul, GlobalTheory.HeisThetaF.cAF_algebraMap, map_mul, hf, zero_mul]

theorem approx {k : ℕ} (hk : 0 < k) {z : Af F ⊗[F] E} (hz : z ∈ hatO (F := F) E) :
    ∃ (r : 𝓞 E) (s : AEF F E), finPartF F E s ∈ hatO (F := F) E ∧ finPartF F E (cAF σ s) ∈ hatO (F := F) E ∧
      z = finPartF F E (incAF F E (r : E) + k • s) := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, _, ⟨t, rfl⟩, rfl⟩ := hw
    obtain ⟨x, β, hβ, hx⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F k hk).2 α hα
    refine ⟨algebraMap (𝓞 F) (𝓞 E) x * t, pairA F 0 β ⊗ₜ[F] (t : E),
      AddSubgroup.subset_closure ⟨β, hβ, _, ⟨t, rfl⟩, rfl⟩,
      AddSubgroup.subset_closure ⟨β, hβ, _, ⟨sgOF σ t, rfl⟩, rfl⟩, ?_⟩
    rw [hx, map_add (f := _), map_nsmul]
    exact GlobalTheory.SplitIndex.tmul_split β (x : F) k (t : E)
  | zero => exact ⟨0, 0, by rw [map_zero]; exact zero_mem _,
      by rw [map_zero, map_zero]; exact zero_mem _, by simp⟩
  | add x x' _ _ h h' =>
    obtain ⟨r, s, h1, h2, rfl⟩ := h
    obtain ⟨r', s', h1', h2', rfl⟩ := h'
    refine ⟨r + r', s + s', by rw [map_add (f := _)]; exact add_mem h1 h1',
      by rw [map_add (f := _), map_add (f := _)]; exact add_mem h2 h2', ?_⟩
    rw [← map_add (f := _)]
    congr 1
    push_cast
    rw [map_add (f := _), smul_add]
    abel
  | neg x _ h =>
    obtain ⟨r, s, h1, h2, rfl⟩ := h
    refine ⟨-r, -s, by rw [map_neg]; exact neg_mem h1,
      by rw [map_neg, map_neg]; exact neg_mem h2, ?_⟩
    rw [← map_neg]
    congr 1
    push_cast
    rw [map_neg, smul_neg, neg_add]

theorem split_mem (h : IsCMExt F E σ) {e : AEF F E} (hee : e * e = e)
    (hf : algebraMap (AF F) (AEF F E) (pairA F 0 1) * e = e) (hec : e * cAF σ e = 0) {q : ℕ} (hq : q.Prime)
    (hin : InertQF σ q) {x : XFF F E nS nT} (hx : q • x ∈ (latF F E nS nT Λ).toAddSubgroup) :
    e • x ∈ (latF F E nS nT Λ).toAddSubgroup := by
  have heI : finPartF F E e ∈ hatO (F := F) E :=
    GlobalTheory.AdIdem.mem_hat_of_idempotent F E _ (by rw [← map_mul, hee])
  obtain ⟨r, s, hs, hs', hz⟩ := approx (σ := σ) hq.pos heI
  have h0 : finPartF F E (e - (incAF F E (r : E) + q • s)) = 0 := by rw [map_sub, ← hz, sub_self]
  have h0' := finPart_cAF_zero (σ := σ) h0
  rw [map_sub, map_add (f := _), map_nsmul, GlobalTheory.HeisLineF.cAF_incAF, ← coe_sgOF] at h0'
  refine GlobalTheory.SplitIndex.core_split ((incAF F E).comp (algebraMap (𝓞 E) E)) _
    (fun a => finPartF F E a ∈ hatO (F := F) E) (fun a ha u hu => int_smul_mem ha hu)
    (fun r => AddSubgroup.subset_closure ⟨1, fun v => GlobalTheory.AdLat.adele_one_integral F v, _, ⟨r, rfl⟩, rfl⟩)
    q x hx e (cAF σ e) s (cAF σ s) heI hs hs' hee hec r (sgOF σ r) (mul_e_zero h0 hf) (mul_e_zero h0' hf) ?_
  intro P hP hqP hr
  have := hin P hP hqP _ hr
  rwa [show sgOF σ (sgOF σ r) = r from RingOfIntegers.ext (sg_sg h _)] at this

theorem mtF_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (a b : GAF σ J) : mtF σ J (a * b) = mtF σ J a * mtF σ J b := by
  simp only [mtF, map_mul, Units.val_mul]

theorem mtF_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mtF σ J 1 = 1 := by
  simp only [mtF, map_one, Units.val_one]

theorem supp_smul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {e : AEF F E} {g : GAF σ J} (hg : SuppAtF σ e J g) :
    (1 - (e + cAF σ e)) • mtF σ J g = (1 - (e + cAF σ e)) • (1 : Matrix (Fin n) (Fin n) (AEF F E)) := by
  ext i j
  have := hg i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at this ⊢
  linear_combination -this

theorem supp_smul_inv {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {e : AEF F E} {g : GAF σ J} (hg : SuppAtF σ e J g) :
    (1 - (e + cAF σ e)) • mtF σ J g⁻¹ = (1 - (e + cAF σ e)) • (1 : Matrix (Fin n) (Fin n) (AEF F E)) := by
  calc (1 - (e + cAF σ e)) • mtF σ J g⁻¹ = ((1 - (e + cAF σ e)) • (1 : Matrix (Fin n) (Fin n) (AEF F E))) * mtF σ J g⁻¹ := by
        rw [Matrix.smul_mul, Matrix.one_mul]
    _ = ((1 - (e + cAF σ e)) • mtF σ J g) * mtF σ J g⁻¹ := by rw [supp_smul hg]
    _ = _ := by rw [Matrix.smul_mul, ← mtF_mul, mul_inv_cancel, mtF_one]

theorem act_supp {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {e : AEF F E}
    {g : GAF σ JS} {k : GAF σ JT} (hg : SuppAtF σ e JS g) (hk : SuppAtF σ e JT k) (y : WOF F E nS nT) :
    (1 - (e + cAF σ e)) • actOF σ JS JT g k y = (1 - (e + cAF σ e)) • y := by
  unfold actOF
  calc (1 - (e + cAF σ e)) • (mtF σ JT k * y * mtF σ JS g⁻¹)
      = ((1 - (e + cAF σ e)) • mtF σ JT k) * y * mtF σ JS g⁻¹ := by rw [Matrix.smul_mul, Matrix.smul_mul]
    _ = ((1 - (e + cAF σ e)) • (1 : Matrix (Fin nT) (Fin nT) (AEF F E))) * y * mtF σ JS g⁻¹ := by rw [supp_smul hk]
    _ = y * ((1 - (e + cAF σ e)) • mtF σ JS g⁻¹) := by
        rw [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul]
    _ = y * ((1 - (e + cAF σ e)) • (1 : Matrix (Fin nS) (Fin nS) (AEF F E))) := by rw [supp_smul_inv hg]
    _ = _ := by rw [Matrix.mul_smul, Matrix.mul_one]

theorem idx_main (h : IsCMExt F E σ) {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
    (hfin : ∀ p, idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT p)) ≠ 0) :
    ∀ e, IsSplitIdemF σ e → ∀ g k, SuppAtF σ e JS g → SuppAtF σ e JT k → ∀ q : ℕ, q.Prime → InertQF σ q →
    ¬ q ∣ idx (latF F E nS nT Λ) ((latF F E nS nT Λ).map (rhoFF σ JS JT (g, k))) := by
  intro e he g k hg hk q hq hin
  obtain ⟨hf, hfc, hcc⟩ := split_parts he
  have hc2 : cAF σ (cAF σ e) = e := GlobalTheory.HeisLineF.cAF_cAF σ (sg_sg h) e
  have hec : e * cAF σ e = 0 := he.2.1
  have heI : finPartF F E e ∈ hatO (F := F) E :=
    GlobalTheory.AdIdem.mem_hat_of_idempotent F E _ (by rw [← map_mul, he.1])
  have hcI : finPartF F E (cAF σ e) ∈ hatO (F := F) E :=
    GlobalTheory.AdIdem.mem_hat_of_idempotent F E _ (by rw [← map_mul, hcc])
  have hcI' : finPartF F E (1 - (e + cAF σ e)) ∈ hatO (F := F) E := by
    rw [map_sub, map_add (f := _), map_one]
    exact sub_mem (GlobalTheory.AdLat.one_tmul_mem_adelicCompletionOfElementSet F ⟨1, map_one _⟩) (add_mem heI hcI)
  refine GlobalTheory.SplitIndex.not_dvd_of_saturated _ _ (hfin (g, k)) hq fun x hx hqx => ?_
  refine GlobalTheory.SplitIndex.mem_of_parts _ e (cAF σ e) x (split_mem h he.1 hf hec hq hin hqx)
    (split_mem h hcc hfc (by rw [hc2, mul_comm, hec]) hq hin hqx) ?_
  obtain ⟨y, hy, rfl⟩ := hx
  have e1 : (1 - (e + cAF σ e)) • rhoFF σ JS JT (g, k) y = (1 - (e + cAF σ e)) • y :=
    XFF.ext (by rw [XFF.coe_asmul, XFF.coe_asmul, coe_rhoFF]; exact act_supp hg hk _)
  rw [e1]
  exact int_smul_mem hcI' hy

end PositivityTheory.ThKW.LatB

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.AutProd
noncomputable section

open scoped TensorProduct Matrix Topology Kronecker ComplexOrder Classical
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF MeasureTheory GlobalTheory.FinWeil GlobalTheory.FinLatF GlobalTheory.RealWeilF GlobalTheory.WeilPartsF

namespace PositivityTheory.ThKW

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {B : Base F E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E}
  {ξ₀ : E} {θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ)} {ι : (InfinitePlace F → ℂ) →+ AEF F E}
  {Λ : Submodule (𝓞 E) (Matrix (Fin nT) (Fin nS) E)} {hc : HeisClosedF σ JS JT ξ₀ B.ψ} {w : 𝓞 E} {lam : ℕ →* ℂ}
  {Om : GAF σ JS × GAF σ JT →* Module.End ℂ (thetaSubF σ JS JT ξ₀ B.ψ)}
  {s : Matrix (IxF F nS nT) (IxF F nS nT) ℂ}

variable {η : (AEF F E)ˣ →* Circle} {ε : AEF F E} {of oi : GAF σ JS × GAF σ JT →* Module.End ℂ (WOF F E nS nT → ℂ)}

theorem exists_fin (C : Ctx σ B JS JT ξ₀ θ ι) (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om) (h1 : IsHeckeCharF η)
    (h2 : ResEtaF η 1) (hε : IsHalfF σ ε) : ∃ of, IsFinWeilF σ JS JT ξ₀ B.ψ (η ^ nS) (η ^ nT) of ∧
      ∀ p (f : thetaSubF σ JS JT ξ₀ B.ψ), of p f = (zF σ JS JT η ε hε.idem p : ℂ) • (Om p f : WOF F E nS nT → ℂ) :=
  exists_fin_A C hO h1 h2 hε

theorem fin_inf_comm (C : Ctx σ B JS JT ξ₀ θ ι) (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi) (p q : GAF σ JS × GAF σ JT) (f : WOF F E nS nT → ℂ)
    (hf : IsThetaFunOF σ JS JT ξ₀ B.ψ f) : of p (oi q f) = oi q (of p f) :=
  fin_inf_comm_A C hO hof hi p q f hf

theorem datum_of_aut (C : Ctx σ B JS JT ξ₀ θ ι) (hG : GoodLat Λ) (hO : IsLatRepF σ JS JT ξ₀ B.ψ hc Λ w lam Om)
    (h1 : IsHeckeCharF η) (h2 : ResEtaF η 1) (hf : IsFinWeilF σ JS JT ξ₀ B.ψ (η ^ nS) (η ^ nT) of)
    (hof : ∀ p, ∃ z : ℂ, ∀ f : thetaSubF σ JS JT ξ₀ B.ψ, of p f = z • (Om p f : WOF F E nS nT → ℂ))
    (hi : IsInfWeilF σ JS JT ξ₀ B.ψ oi)
    (haut : ∀ γ ∈ GQF σ JS, ∀ γ' ∈ GQF σ JT, ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f → of (γ, γ') (oi (γ, γ') f) 0 = f 0) :
    ∃ ω, IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ (η ^ nS) (η ^ nT) ω :=
  datum_of_aut_A C hO h1 h2 hf hof hi haut

end PositivityTheory.ThKW

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ParsevalAdelicPairFundamental
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.ParsevalPolarization

open GlobalTheory.ThetaTransform

theorem polar_pt (z w : ℂ) : z * starRingEnd ℂ w =
    (((‖z + 1 * w‖ ^ 2 - ‖z + (-1) * w‖ ^ 2 : ℝ) : ℂ) +
      Complex.I * ((‖z + Complex.I * w‖ ^ 2 - ‖z + (-Complex.I) * w‖ ^ 2 : ℝ) : ℂ)) / 4 := by
  simp only [Complex.sq_norm, Complex.normSq_apply]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

theorem polar {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    (f₁ f₂ : X → ℂ) (g₁ g₂ : Y → ℂ) (c : ℝ)
    (hf : ∀ a : ℂ, Integrable (fun x => ‖f₁ x + a * f₂ x‖ ^ 2) μ)
    (hg : ∀ a : ℂ, Integrable (fun y => ‖g₁ y + a * g₂ y‖ ^ 2) ν)
    (h : ∀ a : ℂ, ∫ y, ‖g₁ y + a * g₂ y‖ ^ 2 ∂ν = c * ∫ x, ‖f₁ x + a * f₂ x‖ ^ 2 ∂μ) :
    ∫ y, g₁ y * starRingEnd ℂ (g₂ y) ∂ν = (c : ℂ) * ∫ x, f₁ x * starRingEnd ℂ (f₂ x) ∂μ := by
  have key : ∀ {Z : Type} [MeasurableSpace Z] (ρ : Measure Z) (k₁ k₂ : Z → ℂ),
      (∀ a : ℂ, Integrable (fun x => ‖k₁ x + a * k₂ x‖ ^ 2) ρ) →
      ∫ x, k₁ x * starRingEnd ℂ (k₂ x) ∂ρ =
        (((∫ x, ‖k₁ x + 1 * k₂ x‖ ^ 2 ∂ρ) - ∫ x, ‖k₁ x + (-1) * k₂ x‖ ^ 2 ∂ρ : ℝ) +
          Complex.I * (((∫ x, ‖k₁ x + Complex.I * k₂ x‖ ^ 2 ∂ρ) -
            ∫ x, ‖k₁ x + (-Complex.I) * k₂ x‖ ^ 2 ∂ρ : ℝ) : ℂ)) / 4 := by
    intro Z _ ρ k₁ k₂ hk
    simp_rw [polar_pt (k₁ _) (k₂ _)]
    rw [integral_div, integral_add, integral_const_mul, integral_complex_ofReal, integral_complex_ofReal,
      integral_sub (hk 1) (hk (-1)), integral_sub (hk Complex.I) (hk (-Complex.I))]
    · exact ((hk 1).sub (hk (-1))).ofReal
    · exact (((hk Complex.I).sub (hk (-Complex.I))).ofReal).const_mul _
  rw [key ν g₁ g₂ hg, key μ f₁ f₂ hf, h 1, h (-1), h Complex.I, h (-Complex.I)]
  push_cast
  ring

theorem thV_smul {F : Type} [Field F] [NumberField F] [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) {N : ℕ}
    (a : ℂ) (Φ : (Fin N → AF F) → ℂ) : thV ψ (a • Φ) = a • thV ψ Φ := by
  funext w
  simp only [thV, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  congr 1; funext ξ; ring

theorem parseval_adelic_pair_fundamental : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {B : Base F E}, B.IsGood σ → ∀ (N : ℕ),
    letI : MeasurableSpace (Fin N → AF F) := borel _
    letI : MeasurableSpace (VA F N) := borel _
    ∀ (ν : Measure (VA F N)), ν.IsAddHaarMeasure → ∀ 𝓕 : Set (VA F N),
      IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N)) 𝓕 ν →
      ∃ (μ : Measure (Fin N → AF F)) (c : ℝ), μ.IsAddHaarMeasure ∧ 0 < c ∧
        ∀ Φ₁ ∈ schA F (Fin N), ∀ Φ₂ ∈ schA F (Fin N),
          ∫ w in 𝓕, thV B.ψ Φ₁ w * starRingEnd ℂ (thV B.ψ Φ₂ w) ∂ν =
            (c : ℂ) * ∫ x, Φ₁ x * starRingEnd ℂ (Φ₂ x) ∂μ := by
  intro F E _ _ _ _ _ σ B hB N
  letI mA : MeasurableSpace (Fin N → AF F) := borel _
  letI mV : MeasurableSpace (VA F N) := borel _
  intro ν hν 𝓕 h𝓕
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : BorelSpace (Fin N → AF F) := ⟨rfl⟩
  have hR : IsTotallyReal F := hB.cm.1
  have hψ : IsCharAF F B.ψ := (GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB).1
  let μ : Measure (Fin N → AF F) := Measure.addHaar
  have hμ : μ.IsAddHaarMeasure := inferInstance
  obtain ⟨𝓕₁, h𝓕₁, h0, htop⟩ := GlobalTheory.T.exists_fundDomain_rationalPointsAdeleTuple_finite_pos F (Fin N) μ hμ
  obtain ⟨c₁, hc0, hctop, hc⟩ := GlobalTheory.T.lintegral_rationalPair_fundDomain_eq_iterated F (Fin N) μ hμ ν hν 𝓕 h𝓕 𝓕₁ h𝓕₁
  set K : ENNReal := c₁ * μ 𝓕₁ with hK
  have hK0 : K ≠ 0 := mul_ne_zero hc0 h0
  have hKt : K ≠ ⊤ := ENNReal.mul_ne_top hctop htop

  have hpar : ∀ Φ ∈ schA F (Fin N), ∫⁻ w in 𝓕, ‖thV B.ψ Φ w‖ₑ ^ 2 ∂ν = K * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
    intro Φ hΦ
    have hm := GlobalTheory.T.measurable_theta_sum_of_schrodinger F B.ψ hψ (Fin N) Φ hΦ
    have hG : @Measurable _ _ (borel _) _ (fun w : (Fin N → AF F) × (Fin N → AF F) =>
        ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr B.ψ w Φ)‖ₑ ^ 2) := Measurable.pow_const (measurable_enorm.comp hm) 2
    show ∫⁻ w in 𝓕, ‖GlobalTheory.WeilM.thetaSum F (GlobalTheory.WeilM.schr B.ψ w Φ)‖ₑ ^ 2 ∂ν = _
    rw [hc _ hG (fun γ hγ w => by
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, GlobalTheory.T.norm_adelicThetaSum_schroedinger_rationalPair_invariant F B.ψ hψ (Fin N) Φ γ hγ w])]
    simp_rw [GlobalTheory.T.lintegral_adelicThetaSum_sq_parseval_second_variable F B.ψ hψ (Fin N) μ hμ 𝓕₁ h𝓕₁ htop Φ hΦ]
    rw [lintegral_const_mul' _ _ htop, GlobalTheory.T.parseval_fundamental_domain_theta F (Fin N) μ hμ 𝓕₁ h𝓕₁ Φ hΦ, hK, mul_assoc]
  have henorm : ∀ z : ℂ, ‖‖z‖ ^ 2‖ₑ = ‖z‖ₑ ^ 2 := fun z => by
    rw [Real.enorm_eq_ofReal (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]

  have hΦint : ∀ Φ ∈ schA F (Fin N), Integrable (fun x => ‖Φ x‖ ^ 2) μ := fun Φ hΦ =>
    (GlobalTheory.WeilM.schA_memLp_two F (Fin N) μ hμ Φ hΦ).integrable_norm_pow two_ne_zero
  have hthint : ∀ Φ ∈ schA F (Fin N), Integrable (fun w => ‖thV B.ψ Φ w‖ ^ 2) (ν.restrict 𝓕) := by
    intro Φ hΦ
    have hm := GlobalTheory.T.measurable_theta_sum_of_schrodinger F B.ψ hψ (Fin N) Φ hΦ
    refine ⟨((hm.norm.pow_const 2).aestronglyMeasurable), ?_⟩
    show ∫⁻ w in 𝓕, ‖‖thV B.ψ Φ w‖ ^ 2‖ₑ ∂ν < ⊤
    simp_rw [henorm]
    rw [hpar Φ hΦ]
    refine ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hKt) ?_
    have := (hΦint Φ hΦ).2
    unfold HasFiniteIntegral at this
    simp_rw [henorm] at this
    exact this
  have hreal : ∀ Φ ∈ schA F (Fin N), ∫ w in 𝓕, ‖thV B.ψ Φ w‖ ^ 2 ∂ν = K.toReal * ∫ x, ‖Φ x‖ ^ 2 ∂μ := by
    intro Φ hΦ
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
        (hthint Φ hΦ).aestronglyMeasurable,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _) (hΦint Φ hΦ).aestronglyMeasurable]
    have e1 : ∀ z : ℂ, ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := fun z => by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    simp_rw [e1]
    rw [hpar Φ hΦ, ENNReal.toReal_mul]
  refine ⟨μ, K.toReal, hμ, ENNReal.toReal_pos hK0 hKt, fun Φ₁ hΦ₁ Φ₂ hΦ₂ => ?_⟩
  have hmem : ∀ a : ℂ, Φ₁ + a • Φ₂ ∈ schA F (Fin N) := fun a => add_mem hΦ₁ (Submodule.smul_mem _ a hΦ₂)
  have hth : ∀ a : ℂ, thV B.ψ (Φ₁ + a • Φ₂) = fun w => thV B.ψ Φ₁ w + a * thV B.ψ Φ₂ w := by
    intro a
    rw [thV_add hR hψ (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ₁ hΦ₁) (GlobalTheory.SchwartzDecay.decay_smul a (GlobalTheory.T.adelicRapidDecay_of_mem_adelicSchwartzSpace F N Φ₂ hΦ₂)),
      thV_smul]
    rfl
  have hfn : ∀ a : ℂ, (Φ₁ + a • Φ₂) = fun x => Φ₁ x + a * Φ₂ x := fun a => rfl
  refine polar μ (ν.restrict 𝓕) Φ₁ Φ₂ (thV B.ψ Φ₁) (thV B.ψ Φ₂) K.toReal (fun a => ?_) (fun a => ?_) (fun a => ?_)
  · have := hΦint _ (hmem a)
    rwa [hfn a] at this
  · have := hthint _ (hmem a)
    rwa [hth a] at this
  · have := hreal _ (hmem a)
    rwa [hth a, hfn a] at this

end PositivityTheory.ThKW.ParsevalPolarization

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.LamFormula
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.AdelicSchwartzProperties

open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem psi_cancel [Invertible (2 : AF F)] (ψ : AddChar (AF F) ℂ) (A C : AF F) (D : ℂ) :
    ψ (⅟2 * -A) * (ψ (C + ⅟2 * A) * D) = D * ψ C := by
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, show ⅟(2 : AF F) * -A + (C + ⅟2 * A) = C by ring]
  ring

theorem lam_formula {σ : E →ₐ[F] E} {B : Base F E} (hB : B.IsGood σ) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    (hν : ν.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) (N : ℕ)
    (α β : WOF F E nS nT ≃ₗ[AF F] (Fin N → AF F)) (e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N)
    (hCe : ∀ u v, e (dC (AF F ⊗[F] E) nT * u + dCd F JT * v) = (α v, β u))
    (he : ∀ w w', symplOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ w w' = symV (e w) (e w'))
    (hβc : Continuous β) (hβs : Continuous β.symm)
    (hr1 : ∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y : Fin N → F, β (ratWF x) = GlobalTheory.SWQ.rat y)
    (hr2 : ∀ y : Fin N → F, ∃ x : Matrix (Fin nT) (Fin nS) E, β (ratWF x) = GlobalTheory.SWQ.rat y) :
    ∃ c : ℂ, c ≠ 0 ∧ ∀ Φ ∈ schA F (Fin N), ∀ v : WOF F E nS nT,
      GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC (AF F ⊗[F] E) nT)
        (heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dCd F JT * v) (thV B.ψ Φ ∘ e)) =
        c * Φ (α v) := by
  classical
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS nT
  haveI := i1; haveI := i2; haveI := i3; haveI := i4; haveI := i5
  haveI hBor : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable E := GlobalTheory.ThetaParsevalInner.countable_numberField E
  haveI : Countable F := GlobalTheory.ThetaParsevalInner.countable_numberField F
  haveI : Countable (ratLF F E nS nT) := by
    refine Function.Surjective.countable
      (f := fun m : Fin nT → Fin nS → E => (⟨(incAF F E).toAddMonoidHom.mapMatrix (Matrix.of m),
        AddMonoidHom.mem_range.2 ⟨_, rfl⟩⟩ : ratLF F E nS nT)) ?_
    rintro ⟨r, m, rfl⟩
    exact ⟨m, rfl⟩
  obtain ⟨Nn, hNn⟩ := (GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact (WOF F E nS nT) (ratLF F E nS nT) K hK hKc).2
    (fun _ => (1 : ℂ)) continuous_const (fun _ _ _ => rfl)
  obtain ⟨h0, htop, -, -⟩ := hNn ν 𝓕 hν h𝓕
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := isFiniteMeasure_restrict.mpr htop
  haveI := hν
  have hstd := GlobalTheory.StdCharWeilDatum.isStdCharF_of_isGood F E σ B hB
  obtain ⟨hcont, hnorm, htriv, s0, hs0⟩ := hstd.1
  refine ⟨((ν 𝓕).toReal : ℂ), ?_, fun Φ hΦ v => ?_⟩
  · exact_mod_cast (ENNReal.toReal_pos h0 htop).ne'
  set x : Fin N → AF F := α v with hx
  obtain ⟨emb, hemb⟩ : ∃ emb : (Fin N → F) → (Fin N → AF F), emb = fun ξ i => algebraMap F (AF F) (ξ i) := ⟨_, rfl⟩
  obtain ⟨a, ha⟩ : ∃ a : (Fin N → F) → ℂ, a = fun ξ => Φ (emb ξ + x) := ⟨_, rfl⟩
  obtain ⟨ch, hch⟩ : ∃ ch : (Fin N → F) → WOF F E nS nT → ℂ, ch = fun ξ u => B.ψ (emb ξ ⬝ᵥ β u) := ⟨_, rfl⟩
  have hsum : Summable fun ξ => ‖a ξ‖ := by
    have h0 := GlobalTheory.WeilM.summable_norm_of_mem_schA F (GlobalTheory.SchwartzTranslate.schA_translate F x hΦ)
    subst ha hemb
    exact h0
  have hch_norm : ∀ ξ u, ‖ch ξ u‖ = 1 := fun ξ u => by rw [hch]; exact hnorm _
  have hch_cont : ∀ ξ, Continuous (ch ξ) := fun ξ => by
    rw [hch]; exact hcont.comp (continuous_const.dotProduct hβc)

  have hint : ∀ u : WOF F E nS nT,
      heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ (dCd F JT * v) (thV B.ψ Φ ∘ e)
        (dC (AF F ⊗[F] E) nT * u) = ∑' ξ, a ξ * ch ξ u := by
    intro u
    have h1 : e (dC (AF F ⊗[F] E) nT * u) = (0, β u) := by
      have := hCe u 0
      rwa [Matrix.mul_zero, add_zero, map_zero] at this
    have h2 : e (dCd F JT * v) = (α v, 0) := by
      have := hCe 0 v
      rwa [Matrix.mul_zero, zero_add, map_zero] at this
    simp only [heisOF, symplOHF, Function.comp_apply, he, h1, h2, hCe, GlobalTheory.ThetaOntoF.algebraMap_half]
    unfold thV GlobalTheory.WeilM.thetaSum GlobalTheory.WeilM.schr
    rw [← tsum_mul_left]
    congr 1
    funext ξ
    subst ha hch hemb
    simp only [symV, dotProduct_zero, zero_dotProduct, zero_sub]
    exact psi_cancel B.ψ _ _ _
  have hFint : ∀ ξ, Integrable (fun u => a ξ * ch ξ u) (ν.restrict 𝓕) := fun ξ =>
    (Integrable.of_bound (hch_cont _).aestronglyMeasurable 1 (ae_of_all _ fun u => (hch_norm _ _).le)).const_mul _
  have hnormint : ∀ ξ, ∫ u in 𝓕, ‖a ξ * ch ξ u‖ ∂ν = ‖a ξ‖ * ν.real 𝓕 := by
    intro ξ
    simp only [norm_mul, hch_norm, mul_one]
    rw [setIntegral_const, smul_eq_mul]; ring
  have hsumint : Summable fun ξ => ∫ u in 𝓕, ‖a ξ * ch ξ u‖ ∂ν := by
    simp_rw [hnormint]
    exact hsum.mul_right _
  have horth : ∀ ζ : Fin N → F, ∫ u in 𝓕, ch ζ u ∂ν = if ζ = 0 then (ν.real 𝓕 : ℂ) else 0 := by
    intro ζ
    split_ifs with hζ
    · subst hζ
      have : ∀ u, ch 0 u = 1 := fun u => by simp [hch, hemb]
      simp_rw [this]; rw [setIntegral_const]; simp
    · obtain ⟨i, hi⟩ : ∃ i, ζ i ≠ 0 := by
        by_contra h; push Not at h; exact hζ (funext h)
      refine GlobalTheory.ThetaParsevalInner.setIntegral_eq_zero_of_twist ν (ratLF F E nS nT) h𝓕 (h := ch ζ) ?_
        (c := β.symm (Pi.single i (algebraMap F (AF F) (ζ i)⁻¹ * s0))) (a := B.ψ s0) ?_ hs0
      · intro r hr u
        obtain ⟨x₀, rfl⟩ := hr
        obtain ⟨η, hη⟩ := hr1 x₀
        have hr' : β ((incAF F E).toAddMonoidHom.mapMatrix x₀) = GlobalTheory.SWQ.rat η := hη
        simp only [hch, map_add (f := _), hr', dotProduct_add, AddChar.map_add_eq_mul]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [show emb ζ ⬝ᵥ GlobalTheory.SWQ.rat η = algebraMap F (AF F) (ζ ⬝ᵥ η) by
          subst hemb; simp [dotProduct, map_sum, map_mul, GlobalTheory.SWQ.rat], htriv, one_mul]
      · intro u
        simp only [hch, map_add (f := _), LinearEquiv.apply_symm_apply, dotProduct_add, AddChar.map_add_eq_mul]
        congr 2
        rw [dotProduct_single, hemb]
        simp only
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
  unfold GlobalTheory.LagrTheta.lagrInt
  simp_rw [hint]
  rw [← integral_tsum_of_summable_integral_norm hFint hsumint]
  simp_rw [integral_const_mul, horth]
  rw [tsum_eq_single 0 (fun ξ hξ => by rw [if_neg hξ, mul_zero])]
  rw [if_pos rfl, ha, hemb]
  have hz : (fun i : Fin N => (0 : AF F)) + x = x := by funext i; simp
  simp only [Pi.zero_apply, map_zero]
  rw [hz, Measure.real]
  ring

end PositivityTheory.ThKW.AdelicSchwartzProperties

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.SmulMemConjHalf
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.SplitLagrF

open GlobalTheory.SplitInvFormF GlobalTheory.WeilSchrodinger.DblTargetF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {ξ₀ : E}
  {ψ : AddChar (AF F) ℂ}

theorem dC_mul_eq' (a : WOF F E nS nT) :
    dC F E nT * a = Matrix.of fun i j => Sum.elim (fun p => a p j) (fun p => a p j) (finSumFinEquiv.symm i) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with p | p
  · rw [Matrix.of_apply, Equiv.symm_apply_apply]; exact GlobalTheory.LagrThetaInv.dC_mul_inl a p j
  · rw [Matrix.of_apply, Equiv.symm_apply_apply]; exact GlobalTheory.LagrThetaInv.dC_mul_inr a p j

theorem aC_mul_eq (a : WOF F E nS nT) :
    aC F E nT * a = Matrix.of fun i j => Sum.elim (fun p => a p j) (fun p => -a p j) (finSumFinEquiv.symm i) := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  rcases i with p | p <;>
    simp only [aC, Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id, Matrix.of_apply] <;>
    simp [Matrix.one_apply]

theorem hOF_dC_aC (a y : WOF F E nS nT) :
    hOF σ JS (dblG JT) (dC F E nT * a) (aC F E nT * y) = hOF σ JS JT (a + a) y := by
  rw [dC_mul_eq', aC_mul_eq]
  unfold hOF
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [← finSumFinEquiv.sum_comp, Matrix.of_apply, Equiv.symm_apply_apply, GlobalTheory.LagrThetaInv.dblG_apply]
  simp only [Fintype.sum_sum_type]
  simp [dbl, Finset.sum_add_distrib, mul_add]

theorem hOF_aC_dC (a y : WOF F E nS nT) :
    hOF σ JS (dblG JT) (aC F E nT * y) (dC F E nT * a) = hOF σ JS JT y (a + a) := by
  rw [dC_mul_eq', aC_mul_eq]
  unfold hOF
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [← finSumFinEquiv.sum_comp, Matrix.of_apply, Equiv.symm_apply_apply, GlobalTheory.LagrThetaInv.dblG_apply]
  simp only [Fintype.sum_sum_type]
  simp [dbl, Finset.sum_add_distrib, mul_add, add_mul]

theorem commF_aC_dC (a y : WOF F E nS nT) :
    commF σ JS (dblG JT) ξ₀ ψ (aC F E nT * y) (dC F E nT * a) = commF σ JS JT ξ₀ ψ y (a + a) := by
  simp only [commF, symplOHF, symplOF, hOF_dC_aC, hOF_aC_dC]

theorem mul_mem_conjHalf {m : ℕ} {e : AEF F E} (M : Matrix (Fin m) (Fin nT) (AEF F E)) {y : WOF F E nS nT}
    (hy : y ∈ conjHalf σ e nS nT) : (M * y : WOF F E nS m) ∈ conjHalf σ e nS m := fun i j => by
  rw [Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_left_comm, hy k j]


variable (F E) in
def hlf : AEF F E := incAF F E (1 / 2)

theorem hlf_add : hlf F E + hlf F E = 1 := by
  unfold hlf
  rw [← map_add (f := _), show (1 / 2 : E) + 1 / 2 = 1 by norm_num, map_one]

theorem exists_decomp {e : AEF F E} {u : WOF F E nS (nT + nT)} (hu : u ∈ conjHalf σ e nS (nT + nT)) :
    ∃ a ∈ conjHalf σ e nS nT, ∃ b ∈ conjHalf σ e nS nT, u = dC F E nT * a + aC F E nT * b := by
  refine ⟨Matrix.of fun p j => hlf F E * (u (finSumFinEquiv (Sum.inl p)) j + u (finSumFinEquiv (Sum.inr p)) j),
    fun p j => ?_,
    Matrix.of fun p j => hlf F E * (u (finSumFinEquiv (Sum.inl p)) j - u (finSumFinEquiv (Sum.inr p)) j),
    fun p j => ?_, ?_⟩
  · rw [Matrix.of_apply, mul_left_comm, mul_add, hu, hu]
  · rw [Matrix.of_apply, mul_left_comm, mul_sub, hu, hu]
  · rw [dC_mul_eq', aC_mul_eq]
    ext i j
    obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
    rcases i with p | p <;>
      simp only [Matrix.add_apply, Matrix.of_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
    · linear_combination (-u (finSumFinEquiv (Sum.inl p)) j) * (hlf_add (F := F) (E := E))
    · linear_combination (-u (finSumFinEquiv (Sum.inr p)) j) * (hlf_add (F := F) (E := E))

theorem neg_hlf_add (g : WOF F E nS nT) : (-hlf F E) • g + (-hlf F E) • g = -g := by
  rw [← add_smul, ← neg_add, hlf_add, neg_one_smul]

theorem smul_mem_conjHalf {e : AEF F E} (c : AEF F E) {y : WOF F E nS nT}
    (hy : y ∈ conjHalf σ e nS nT) : c • y ∈ conjHalf σ e nS nT := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul, mul_left_comm, hy i j]

theorem lagrInt_smul {m : ℕ} (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT))
    (C : Matrix (Fin m) (Fin nT) (AF F ⊗[F] E)) (c : ℂ) (f : WOF F E nS m → ℂ) :
    GlobalTheory.LagrTheta.lagrInt ν 𝓕 C (c • f) = c * GlobalTheory.LagrTheta.lagrInt ν 𝓕 C f := by
  simp only [GlobalTheory.LagrTheta.lagrInt, Pi.smul_apply, smul_eq_mul, integral_const_mul]

theorem prof_smul (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)) (c : ℂ) (f : WOF F E nS (nT + nT) → ℂ)
    (y : WOF F E nS nT) : prof σ JS JT ξ₀ ψ ν 𝓕 (c • f) y = c * prof σ JS JT ξ₀ ψ ν 𝓕 f y := by
  unfold prof
  rw [GlobalTheory.WeilPartsF.heisOF_smul, lagrInt_smul]

theorem prof_zero (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)) (f : WOF F E nS (nT + nT) → ℂ) :
    prof σ JS JT ξ₀ ψ ν 𝓕 f 0 = GlobalTheory.LagrTheta.lagrInt ν 𝓕 (dC F E nT) f := by
  unfold prof
  rw [Matrix.mul_zero, heisOF_zero]

theorem prof_heis_aC (ν : Measure (WOF F E nS nT)) (𝓕 : Set (WOF F E nS nT)) {e : AEF F E} (he : IsSplitIdemF σ e)
    (f : WOF F E nS (nT + nT) → ℂ) {y b : WOF F E nS nT} (hy : y ∈ conjHalf σ e nS nT) (hb : b ∈ conjHalf σ e nS nT) :
    prof σ JS JT ξ₀ ψ ν 𝓕 (heisOF σ JS (dblG JT) ξ₀ ψ (aC F E nT * b) f) y = prof σ JS JT ξ₀ ψ ν 𝓕 f (y + b) := by
  unfold prof
  rw [Matrix.mul_add, GlobalTheory.SplitVacF.heisOF_add_half he (mul_mem_conjHalf _ hy) (mul_mem_conjHalf _ hb)]

theorem integrableOn_dC {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {f : WOF F E nS (nT + nT) → ℂ}
    (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ ψ f) : IntegrableOn (fun u : WOF F E nS nT => f (dC F E nT * u)) 𝓕 ν := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLatticeF.lattice F E nS nT
  haveI : BorelSpace (WOF F E nS nT) := ⟨rfl⟩
  haveI : Countable (ratLF F E nS nT) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI := GlobalTheory.HeisThetaF.isTopologicalRing_AEF (F := F) (E := E)
  have hfin := GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (G := WOF F E nS nT) (ratLF F E nS nT) hK hKc ν h𝓕
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  have hI : Continuous fun u : WOF F E nS nT => f (dC F E nT * u) :=
    hf.cont.comp (continuous_const.matrix_mul continuous_id)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hI.continuousOn
  refine Integrable.of_bound hI.aestronglyMeasurable C (Filter.Eventually.of_forall fun w => ?_)
  obtain ⟨_, ⟨γ, rfl⟩, h⟩ := hKc w
  have h1 := hC _ h
  have hr : ((incAF F E).toAddMonoidHom.mapMatrix γ : WOF F E nS nT) = ratWF γ := rfl
  have h2 := hf.quasi (GlobalTheory.LagrThetaInv.dC E nT * γ) (dC F E nT * w)
  rw [← dC_mul_ratWF, symplOHF_dC, neg_zero, AddChar.map_zero_eq_one, one_mul] at h2
  simp only [hr, Matrix.mul_add] at h1
  rwa [h2] at h1

variable {B : Base F E}

theorem prof_add (hB : B.IsGood σ) {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {f g : WOF F E nS (nT + nT) → ℂ}
    (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) (hg : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ g) (y : WOF F E nS nT) :
    prof σ JS JT ξ₀ B.ψ ν 𝓕 (f + g) y = prof σ JS JT ξ₀ B.ψ ν 𝓕 f y + prof σ JS JT ξ₀ B.ψ ν 𝓕 g y := by
  unfold prof
  rw [GlobalTheory.WeilPartsF.heisOF_add]
  exact integral_add
    (integrableOn_dC hν h𝓕 (GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB _ _ JS _ ξ₀ (aC F E nT * y) f hf))
    (integrableOn_dC hν h𝓕 (GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB _ _ JS _ ξ₀ (aC F E nT * y) g hg))

theorem prof_heis_dC (hB : B.IsGood σ) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {f : WOF F E nS (nT + nT) → ℂ}
    (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) (a y : WOF F E nS nT) :
    prof σ JS JT ξ₀ B.ψ ν 𝓕 (heisOF σ JS (dblG JT) ξ₀ B.ψ (dC F E nT * a) f) y =
      commF σ JS JT ξ₀ B.ψ y (a + a) * prof σ JS JT ξ₀ B.ψ ν 𝓕 f y := by
  unfold prof
  rw [heisOF_comm, lagrInt_smul, commF_aC_dC, lagrInt_heis_dC F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ ν 𝓕 hν h𝓕 _
    (GlobalTheory.HeisThetaF.isThetaFunOF_heisOF F E σ B hB _ _ JS _ ξ₀ (aC F E nT * y) f hf)]

theorem prof_heis_lift (hB : B.IsGood σ) (hS : IsHermND σ JS) (hT : IsHermND σ JT) (hξ : ξ₀ ≠ 0) (hσξ : σ ξ₀ = -ξ₀)
    {ν : Measure (WOF F E nS nT)} {𝓕 : Set (WOF F E nS nT)} (hν : ν.IsAddHaarMeasure)
    (h𝓕 : IsAddFundamentalDomain (ratLF F E nS nT) 𝓕 ν) {f : WOF F E nS (nT + nT) → ℂ}
    (hf : IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ f) (g y : WOF F E nS nT) :
    prof σ JS JT ξ₀ B.ψ ν 𝓕 (heisOF σ JS (dblG JT) ξ₀ B.ψ (dC F E nT * ((-hlf F E) • g : WOF F E nS nT)) f) y =
      commF σ JS JT ξ₀ B.ψ g y * prof σ JS JT ξ₀ B.ψ ν 𝓕 f y := by
  rw [prof_heis_dC hB hS hT hξ hσξ hν h𝓕 hf, neg_hlf_add, GlobalTheory.SplitVacF.commF_swap]

end GlobalTheory.SplitLagrF

end
end

section -- merged from Development.WeilBound.ThetaLifts.Reductions.WeilPairs.OneAddPow
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace PositivityTheory.ThKW.PhaseFourierInjectivity

open PositivityTheory.ThKW.ModulusFactorDefinition

section

variable {R : Type} [CommRing R] {n : ℕ}

abbrev aC (R : Type) [CommRing R] (n : ℕ) : Matrix (Fin (n + n)) (Fin n) R :=
  (Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (-1)).submatrix finSumFinEquiv.symm id

theorem CC_add : dC R n * (dC R n)ᵀ + aC R n * (aC R n)ᵀ = (2 : R) • 1 := by
  ext i j
  obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective j
  simp only [diagCols, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, id, Matrix.smul_apply, Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq]
  rcases p with p | p <;> rcases q with q | q <;> simp [Matrix.one_apply] <;> split_ifs <;>
    first | (simp_all; done) | (simp_all; norm_num; done) | norm_num

theorem C_D (J : Matrix (Fin n) (Fin n) R) :
    (dC R n)ᵀ * (dbl J).submatrix finSumFinEquiv.symm finSumFinEquiv.symm = J * (aC R n)ᵀ := by
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.transpose_submatrix, diagCols, dbl,
    Matrix.transpose_fromRows, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromBlocks]
  ext i j
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases q with q | q <;> simp [Matrix.one_apply]

theorem A_D (J : Matrix (Fin n) (Fin n) R) :
    (aC R n)ᵀ * (dbl J).submatrix finSumFinEquiv.symm finSumFinEquiv.symm = J * (dC R n)ᵀ := by
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.transpose_submatrix, diagCols, dbl,
    Matrix.transpose_fromRows, Matrix.transpose_fromRows, Matrix.fromCols_mul_fromBlocks]
  ext i j
  obtain ⟨q, rfl⟩ := finSumFinEquiv.surjective j
  simp only [Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases q with q | q <;> simp [Matrix.one_apply]

theorem A_C : (aC R n)ᵀ * dC R n = 0 := by
  rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, diagCols, Matrix.transpose_fromRows,
    Matrix.fromCols_mul_fromRows]
  simp

theorem C_A : (dC R n)ᵀ * aC R n = 0 := by
  have := congrArg Matrix.transpose (A_C (R := R) (n := n))
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at this

theorem ring_facts {A : Type} [Ring A] [Algebra R A] {Q Q' D N : A} {x y : R} (hxy : x * y = 1) (h1 : Q + Q' = 1)
    (hQ : Q * Q' = 0) (hQ' : Q' * Q = 0) :
    (x • Q + y • Q') * (y • Q + x • Q') = 1 ∧
    (Q * D * Q = 0 → Q' * D * Q' = 0 → (x • Q + y • Q') * D * (x • Q + y • Q') = D) ∧
    (N * Q = 0 → Q' * N = 0 → N * N = 0 ∧ (x • Q + y • Q') * N * (y • Q + x • Q') = (x * x) • N) := by
  have e1 : Q * Q = Q := by
    have := congrArg (Q * ·) h1
    simpa only [mul_add, hQ, add_zero, mul_one] using this
  have e2 : Q' * Q' = Q' := by
    have := congrArg (Q' * ·) h1
    simpa only [mul_add, hQ', zero_add, mul_one] using this
  have hyx : y * x = 1 := by rw [mul_comm, hxy]
  refine ⟨?_, fun a b => ?_, fun a b => ?_⟩
  · simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, e1, e2, hQ, hQ', smul_zero, add_zero, zero_add,
      hxy, hyx, one_smul, h1]
  · have hD : D = (Q + Q') * D * (Q + Q') := by rw [h1, one_mul, mul_one]
    conv_rhs => rw [hD]
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul, a, b, smul_zero, add_zero, zero_add,
      hxy, hyx, one_smul]
  · have c1 : Q * N = N := by
      have := congrArg (· * N) h1
      simpa only [add_mul, b, add_zero, one_mul] using this
    have c2 : N * Q' = N := by
      have := congrArg (N * ·) h1
      simpa only [mul_add, a, zero_add, mul_one] using this
    refine ⟨by rw [← c2, mul_assoc, ← mul_assoc Q', b, zero_mul, mul_zero], ?_⟩
    rw [add_mul, smul_mul_assoc, smul_mul_assoc, c1, b, smul_zero, add_zero, mul_add, mul_smul_comm, mul_smul_comm,
      smul_mul_assoc, smul_mul_assoc, a, c2, smul_zero, smul_zero, zero_add, smul_smul]

theorem one_add_pow {A : Type} [Ring A] {N : A} (h : N * N = 0) (m : ℕ) : (1 + N) ^ m = 1 + m • N := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, ih, add_mul, mul_add, mul_add, smul_mul_assoc m N N, h, succ_nsmul]; simp [add_assoc, add_comm N]

end

theorem conj_pow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (nT : ℕ) (JT : Matrix (Fin nT) (Fin nT) E), IsHermND σ JT → ∀ k : ℕ, 0 < k →
    ∃ (M : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT)) (t : GL (Fin nT) (AF F ⊗[F] E)),
      mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) M * dC (AF F ⊗[F] E) nT = dC (AF F ⊗[F] E) nT * t.1 ∧
      ∀ n : GAF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT),
        mtF σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) n * dC (AF F ⊗[F] E) nT = dC (AF F ⊗[F] E) nT →
        M * n * M⁻¹ = n ^ (k * k) := by
  intro F E _ _ _ _ _ σ n J hJ k hk
  let R := AF F ⊗[F] E
  let q : ℚ →+* R := (incAF F E).comp (algebraMap ℚ E)
  have hq : ∀ r, cAF σ (q r) = q r := fun r =>
    congrArg (incAF F E) (show σ (algebraMap ℚ E r) = algebraMap ℚ E r by simp)
  have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hxy : q k * q (k : ℚ)⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel₀ hk', map_one]
  have hyx : q (k : ℚ)⁻¹ * q k = 1 := by rw [mul_comm, hxy]
  have h2 : q (1 / 2) * 2 = 1 := by rw [← map_ofNat q 2, ← map_mul]; norm_num
  let Q : Matrix (Fin (n + n)) (Fin (n + n)) R := q (1 / 2) • (dC R n * (dC R n)ᵀ)
  let Q' : Matrix (Fin (n + n)) (Fin (n + n)) R := q (1 / 2) • (aC R n * (aC R n)ᵀ)
  let J' := J.map (incAF F E)
  let D : Matrix (Fin (n + n)) (Fin (n + n)) R := (dbl J').submatrix finSumFinEquiv.symm finSumFinEquiv.symm
  have hD : JR (AF F) (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) = D := by
    ext i j
    obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective i
    obtain ⟨r, rfl⟩ := finSumFinEquiv.surjective j
    simp only [JR, D, J', GlobalTheory.WeilSchrodinger.DblTargetF.dblG, dbl, Matrix.map_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.symm_apply_apply]
    rcases p with p | p <;> rcases r with r | r <;> simp
  have h1 : Q + Q' = 1 := by rw [← smul_add, CC_add, smul_smul, h2, one_smul]
  have hQ : Q * Q' = 0 := by
    simp only [Q, Q', Matrix.smul_mul, Matrix.mul_smul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (dC R n)ᵀ, C_A]; simp
  have hQ' : Q' * Q = 0 := by
    simp only [Q, Q', Matrix.smul_mul, Matrix.mul_smul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (aC R n)ᵀ, A_C]; simp
  have hQD : Q * D * Q = 0 := by
    simp only [Q, Matrix.smul_mul, Matrix.mul_smul]
    rw [Matrix.mul_assoc (dC R n), C_D, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (aC R n)ᵀ, A_C]; simp
  have hQD' : Q' * D * Q' = 0 := by
    simp only [Q', Matrix.smul_mul, Matrix.mul_smul]
    rw [Matrix.mul_assoc (aC R n), A_D, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (dC R n)ᵀ, C_A]; simp
  have hQ'C : Q' * dC R n = 0 := by
    simp only [Q', Matrix.smul_mul]
    rw [Matrix.mul_assoc, A_C]; simp
  have hQC : Q * dC R n = dC R n := by
    have := congrArg (· * dC R n) h1
    simpa only [Matrix.add_mul, hQ'C, add_zero, Matrix.one_mul] using this
  have f1 := fun N => ring_facts (D := D) (N := N) hxy h1 hQ hQ'
  have f2 := ring_facts (D := D) (N := 0) hyx h1 hQ hQ'
  let M : GL (Fin (n + n)) R := ⟨q k • Q + q (k : ℚ)⁻¹ • Q', q (k : ℚ)⁻¹ • Q + q k • Q', (f1 0).1, f2.1⟩
  have haC : (aC R n).map (cAF σ) = aC R n := by
    ext i j
    obtain ⟨p, rfl⟩ := finSumFinEquiv.surjective i
    simp only [Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
    rcases p with p | p <;> simp [Matrix.one_apply, apply_ite (cAF σ)]
  have hsm : ∀ (r : ℚ) (X : Matrix (Fin (n + n)) (Fin (n + n)) R), (q r • X).map (cAF σ) = q r • X.map (cAF σ) :=
    fun r X => by
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, hq]
  have hM : (M.1.map (cAF σ))ᵀ = M.1 := by
    show ((q k • Q + q (k : ℚ)⁻¹ • Q').map (cAF σ))ᵀ = q k • Q + q (k : ℚ)⁻¹ • Q'
    rw [Matrix.map_add _ (map_add _), hsm, hsm, hsm, hsm, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map,
      Matrix.transpose_map, dC_map, haC]
    simp only [Q, Q', Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hmem : M ∈ HR (AF F) σ (GlobalTheory.WeilSchrodinger.DblTargetF.dblG J) := by
    show (M.1.map (cAF σ))ᵀ * JR (AF F) _ * M.1 = JR (AF F) _
    rw [hM, hD]
    exact (f1 0).2.1 hQD hQD'
  let t : GL (Fin n) R := ⟨q k • 1, q (k : ℚ)⁻¹ • 1, by simp only [Matrix.smul_mul, Matrix.one_mul, smul_smul, hxy, one_smul],
    by simp only [Matrix.smul_mul, Matrix.one_mul, smul_smul, hyx, one_smul]⟩
  refine ⟨(⟨M, hmem⟩ : HR (AF F) σ _), t, ?_, fun g hg => ?_⟩
  · show (q k • Q + q (k : ℚ)⁻¹ • Q') * dC R n = dC R n * (q k • 1)
    rw [Matrix.add_mul, Matrix.smul_mul _ Q, Matrix.smul_mul _ Q', hQC, hQ'C, smul_zero, add_zero, Matrix.mul_smul,
      Matrix.mul_one]
  · set G := mtF σ _ g with hG
    have hu : (G.map (cAF σ))ᵀ * JR (AF F) _ * G = JR (AF F) _ := g.2
    rw [hD] at hu
    have hJu : IsUnit J'.det := by
      have := (Ne.isUnit hJ.2).map (incAF F E)
      rwa [RingHom.map_det] at this
    have a1 : (G - 1) * Q = 0 := by
      simp only [Q, Matrix.mul_smul]
      rw [← Matrix.mul_assoc, Matrix.sub_mul, hg, Matrix.one_mul, sub_self, Matrix.zero_mul, smul_zero]
    have a2 : (aC R n)ᵀ * (G - 1) = 0 := by
      have b1 : (dC R n)ᵀ * (G.map (cAF σ))ᵀ = (dC R n)ᵀ := by
        rw [← Matrix.transpose_mul, ← dC_map (cAF σ) n, ← Matrix.map_mul, hg]
      have b2 : (dC R n)ᵀ * D * G = (dC R n)ᵀ * D := by
        conv_rhs => rw [← hu, ← Matrix.mul_assoc, ← Matrix.mul_assoc, b1]
      rw [C_D] at b2
      have b3 : J' * ((aC R n)ᵀ * (G - 1)) = 0 := by
        rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, b2, sub_self]
      rw [← Matrix.one_mul (_ * _), ← Matrix.nonsing_inv_mul _ hJu, Matrix.mul_assoc, b3, Matrix.mul_zero]
    have a3 : Q' * (G - 1) = 0 := by
      simp only [Q', Matrix.smul_mul]
      rw [Matrix.mul_assoc, a2, Matrix.mul_zero, smul_zero]
    obtain ⟨n1, n2⟩ := (f1 (G - 1)).2.2 a1 a3
    refine Subtype.ext (Units.ext ?_)
    have e : mtF σ _ (g ^ (k * k)) = G ^ (k * k) := by
      rw [hG, mtF, mtF, map_pow, Units.val_pow_eq_pow_val]
    refine Eq.trans ?_ e.symm
    show (q k • Q + q (k : ℚ)⁻¹ • Q') * G * (q (k : ℚ)⁻¹ • Q + q k • Q') = _
    rw [← add_sub_cancel 1 G, one_add_pow n1, mul_add _ 1 (G - 1), mul_one, add_mul (q k • Q + q (k : ℚ)⁻¹ • Q'),
      (f1 0).1, n2, map_natCast, ← Nat.cast_mul, Nat.cast_smul_eq_nsmul]

end PositivityTheory.ThKW.PhaseFourierInjectivity

end
end
