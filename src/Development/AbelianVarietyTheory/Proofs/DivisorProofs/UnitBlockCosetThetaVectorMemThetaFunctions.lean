module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBlockCosetThetaVectorMemThetaFunctions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBlockCosetThetaVectorMemThetaFunctions
noncomputable section

open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
open scoped nonZeroDivisors
open GlobalTheory.InertSign

namespace GlobalTheory.FunObj.CosetTT

variable {D : D7}

theorem exists_nat_mul_mem_one (𝔪 : Ideal (𝓞 D.host.E)) : ∃ M : ℕ, 0 < M ∧ ∀ y : D.host.E,
    y ∈ ((((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) :
        FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : Submodule (𝓞 D.host.E) D.host.E)) →
    (M : D.host.E) * y ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  set 𝔫 : Ideal (𝓞 D.host.E) := D.host.conj • 𝔪
  by_cases h : 𝔫 = ⊥
  · refine ⟨1, one_pos, fun y hy => ?_⟩
    have h0 : ((𝔫 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = 0 := by
      rw [h]; exact FractionalIdeal.coeIdeal_bot
    rw [h0, div_zero, FractionalIdeal.coe_zero, Submodule.mem_bot] at hy
    rw [hy, mul_zero]; exact Submodule.zero_mem _
  · refine ⟨Ideal.absNorm 𝔫, Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff]), fun y hy => ?_⟩
    have hM : ((Ideal.absNorm 𝔫 : ℕ) : D.host.E) ∈ ((𝔫 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) := by
      rw [FractionalIdeal.mem_coeIdeal]
      exact ⟨(Ideal.absNorm 𝔫 : 𝓞 D.host.E), Ideal.absNorm_mem 𝔫, by simp⟩
    have hne : ((𝔫 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := by
      rwa [Ne, FractionalIdeal.coeIdeal_eq_zero]
    have hm := FractionalIdeal.mul_mem_mul hy hM
    rw [div_mul_cancel₀ _ hne] at hm
    have h1 := FractionalIdeal.coeIdeal_le_one (I := 𝔪) (P := D.host.E) hm
    rw [mul_comm]
    rwa [FractionalIdeal.mem_one_iff, ← Submodule.mem_one] at h1

end GlobalTheory.FunObj.CosetTT

namespace GlobalTheory.FunObj.CosetTT

variable {D : D7}

theorem skewLat_smul (𝔪 : Ideal (𝓞 D.host.E)) (d : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ v ∈ skewLat D 𝔪 d, (M : 𝓞 D.host.E) • v ∈ stdL D d := by
  obtain ⟨M, hM, h⟩ := exists_nat_mul_mem_one (D := D) 𝔪
  refine ⟨M, hM, fun v hv => ?_⟩
  simp only [skewLat, stdL, Submodule.mem_pi, Set.mem_univ, true_implies] at hv ⊢
  intro i
  have := h _ (hv i)
  simpa [Pi.smul_apply, Algebra.smul_def] using this

theorem homL_smul {𝔪 : Ideal (𝓞 D.host.E)} {a d M : ℕ}
    (hM : ∀ v ∈ skewLat D 𝔪 d, (M : 𝓞 D.host.E) • v ∈ stdL D d) :
    homL D (stdL D a) (skewLat D 𝔪 d) ≤ (homL D (stdL D a) (stdL D d)).comap
      (LinearMap.lsmul (𝓞 D.host.E) (Matrix (Fin d) (Fin a) D.host.E) (M : 𝓞 D.host.E)) := by
  refine Submodule.span_le.2 fun A hA => ?_
  simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.lsmul_apply]
  refine Submodule.subset_span fun x hx => ?_
  have e : ((M : 𝓞 D.host.E) • A).mulVec x = (M : 𝓞 D.host.E) • A.mulVec x := by
    funext i; simp [Matrix.mulVec, dotProduct, Finset.smul_sum, smul_mul_assoc]
  rw [e]
  exact hM _ (hA x hx)

theorem YYl_smul {𝔪 : Ideal (𝓞 D.host.E)} {a d M : ℕ}
    (hM : ∀ v ∈ skewLat D 𝔪 d, (M : 𝓞 D.host.E) • v ∈ stdL D d) :
    YYl D (stdL D a) (skewLat D 𝔪 d) ≤ (YYl D (stdL D a) (stdL D d)).comap
      (LinearMap.lsmul (𝓞 D.host.E) (Matrix (Fin d) (Fin a) D.host.E) (M : 𝓞 D.host.E)) := by
  refine Submodule.span_le.2 fun B hB => ?_
  obtain ⟨c, hc, A, hA, rfl⟩ := hB
  have hA' := homL_smul (a := a) hM hA
  simp only [Submodule.mem_comap, LinearMap.lsmul_apply] at hA'
  simp only [SetLike.mem_coe, Submodule.mem_comap, LinearMap.lsmul_apply]
  rw [Nat.cast_smul_eq_nsmul] at hA' ⊢
  rw [smul_comm]
  exact Submodule.subset_span ⟨c, hc, _, hA', rfl⟩

theorem la_skew_nsmul (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (𝔪 : Ideal (𝓞 D.host.E)) (a d : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ x ∈ La D (tor0 D cc δ) (stdL D a) (skewLat D 𝔪 d), M • x ∈ La0 D (tor0 D cc δ) a d := by
  obtain ⟨M, hM0, hM⟩ := skewLat_smul (D := D) 𝔪 d
  refine ⟨M, hM0, fun x hx => ?_⟩
  have key : La D (tor0 D cc δ) (stdL D a) (skewLat D 𝔪 d) ≤
      (La0 D (tor0 D cc δ) a d).comap (DistribSMul.toAddMonoidHom (VC D a d) M) := by
    refine (AddSubgroup.closure_le _).2 fun z hz => ?_
    obtain ⟨w, hw, A, hA, rfl⟩ := hz
    have hA' := YYl_smul (a := a) hM hA
    simp only [Submodule.mem_comap, LinearMap.lsmul_apply] at hA'
    simp only [SetLike.mem_coe, AddSubgroup.mem_comap, DistribSMul.toAddMonoidHom_apply]
    refine AddSubgroup.subset_closure ⟨w, hw, _, hA', ?_⟩
    funext τ i j
    simp [embV, tor0, Algebra.smul_def, nsmul_eq_mul]
    ring
  exact key hx

end GlobalTheory.FunObj.CosetTT

namespace GlobalTheory.FunObj.CosetTT

variable {D : D7}

theorem sd_stdL (n : ℕ) : SD D (stdL D n) := by
  obtain ⟨Lt, h1, h2, -⟩ := exists_lattice_of_adelic_point D n
  rw [← h2]; exact (h1 _).2

theorem wd_mem_TT_of_nsmul {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {a d : ℕ} {x : VC D a d}
    {M : ℕ} (hM : 0 < M) (hx : M • x ∈ La0 D (tor0 D cc δ) a d) {F : VC D a d → ℂ}
    (hF : F ∈ TT D (tor0 D cc δ) a d) : Wd D (tor0 D cc δ) x F ∈ TT D (tor0 D cc δ) a d := by
  have k : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) a d) := Or.inr ⟨_, _, sd_stdL a, sd_stdL d, rfl⟩
  have n0 := GlobalTheory.ThetaTriple.nice_of_klat hc k
  obtain ⟨hd, m, hm, hF⟩ := hF
  refine ⟨GlobalTheory.ThetaLevels.wd_entire D _ _ hd, m * M, Nat.mul_pos hm hM, fun y hy => ?_⟩
  have hmy := AddSubgroup.nsmul_mem _ hy m
  have h1 : bc D (tor0 D cc δ) ((m * M) • y) x = 1 := by
    rw [mul_comm, mul_smul, GlobalTheory.ThetaLevels.bc_nsmul_left, ← GlobalTheory.ThetaLevels.bc_nsmul_right]
    exact n0.2.1 _ hmy _ hx
  have h2 : bc D (tor0 D cc δ) x ((m * M) • y) = 1 := by
    rw [mul_comm, mul_smul, GlobalTheory.ThetaLevels.bc_nsmul_right, ← GlobalTheory.ThetaLevels.bc_nsmul_left]
    exact n0.2.1 _ hx _ hmy
  have h3 : Wd D (tor0 D cc δ) ((m * M) • y) F = F := by
    rw [mul_smul]; exact hF _ (AddSubgroup.nsmul_mem _ hy M)
  have h4 := Wd_Wd D (tor0 D cc δ) x ((m * M) • y) F
  rw [h3, h2, add_comm] at h4
  rw [Wd_Wd, h1, h4]

theorem iop_mem_TT {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hc : Crv D cc δ) {a d : ℕ}
    (B : AddSubgroup (VC D a d)) (hB : ∀ x ∈ B, ∃ M : ℕ, 0 < M ∧ M • x ∈ La0 D (tor0 D cc δ) a d)
    {F : VC D a d → ℂ} (hF : F ∈ TT D (tor0 D cc δ) a d) :
    Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) a d) B F ∈ TT D (tor0 D cc δ) a d := by
  set T := tor0 D cc δ
  set A := La0 D T a d
  by_cases hn : (A.addSubgroupOf B).index = 0
  · have h0 : Iop D T A B F = 0 := by funext z; simp [Iop, hn]
    rw [h0]; exact (GlobalTheory.FinWeil.TTs D T a d).zero_mem
  · haveI : Finite (B ⧸ A.addSubgroupOf B) := Nat.finite_of_card_ne_zero hn
    letI : Fintype (B ⧸ A.addSubgroupOf B) := Fintype.ofFinite _
    have hI : Iop D T A B F = ((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) •
        ∑ q : B ⧸ A.addSubgroupOf B, (al D T ((Quotient.out q : B) : VC D a d) *
          (wdPh D T ((Quotient.out q : B) : VC D a d))⁻¹) • Wd D T ((Quotient.out q : B) : VC D a d) F := by
      funext z
      simp only [Iop, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]
      rw [finsum_eq_sum_of_fintype]
      congr 1
      refine Finset.sum_congr rfl fun q _ => ?_
      have h0 : wdPh D T ((Quotient.out q : B) : VC D a d) ≠ 0 := Complex.exp_ne_zero _
      simp only [Wd]
      rw [mul_assoc, inv_mul_cancel_left₀ h0]
    rw [hI]
    refine (GlobalTheory.FinWeil.TTs D T a d).smul_mem _ (Submodule.sum_mem _ fun q _ => (GlobalTheory.FinWeil.TTs D T a d).smul_mem _ ?_)
    obtain ⟨M, hM, hx⟩ := hB _ (Quotient.out q : B).2
    exact wd_mem_TT_of_nsmul hc hM hx hF

theorem cosetV_mem_TT : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ →
    ∀ (o a d : ℕ) (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) →
      cosetV D δ 𝔪 o a d e0 ∈ TT D (tor0 D ⊤ δ) a d := by
  intro D δ hc 𝔪 _ o a d e0 he
  have hT := GlobalTheory.ThetaLevels.levels_closed D ⊤ δ hc a d
  have he' : e0 ∈ TT D (tor0 D ⊤ δ) a d := hT.1 _ _ (sd_stdL a) (sd_stdL d) e0 he
  obtain ⟨M, hM, hx⟩ := la_skew_nsmul (D := D) ⊤ δ 𝔪 a d
  have hI := iop_mem_TT hc (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) (fun x hx' => ⟨M, hM, hx x hx'⟩) he'
  exact hT.2.2.2 _ _ (hT.2.1 _ _ hI)

end GlobalTheory.FunObj.CosetTT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBlockCosetThetaVectorMemThetaFunctionsStatement
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitBlockCosetThetaVector_mem_thetaFunctions : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (o a d : ℕ) (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → cosetV D δ 𝔪 o a d e0 ∈ TT D (tor0 D ⊤ δ) a d := by
  first | exact @GlobalTheory.FunObj.CosetTT.cosetV_mem_TT | exact GlobalTheory.FunObj.CosetTT.cosetV_mem_TT | (intros; apply GlobalTheory.FunObj.CosetTT.cosetV_mem_TT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsLevi
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusMulVecX
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.LeviTorus

open Matrix

variable {R : Type} [CommRing R] {n m : ℕ}

section
variable (c : R →+* R) (J : Matrix (Fin n) (Fin n) R) (X Y : Fin n → R)

theorem conj_mulVec (hJ : ∀ i j, c (J j i) = -J i j) (V : Fin n → R) (hc : ∀ r, c (c r) = r) :
    (fun i => c ((J *ᵥ fun k => c (V k)) i)) = -(V ᵥ* J) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [mulVec, vecMul, dotProduct, map_sum, map_mul, hc, Pi.neg_apply]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hJ k i]; ring

theorem conj_dot (a b : Fin n → R) : c (a ⬝ᵥ b) = (fun i => c (a i)) ⬝ᵥ (fun i => c (b i)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [dotProduct, map_sum, map_mul]

theorem vmv_mulVec (u v w : Fin n → R) : vecMulVec u v *ᵥ w = (v ⬝ᵥ w) • u := by
  ext i
  simp [mulVec, dotProduct, vecMulVec, Finset.mul_sum, mul_comm, mul_left_comm]

end

section Props

variable {c : R →+* R} {J : Matrix (Fin n) (Fin n) R} {X Y : Fin n → R}
  (hc : ∀ r, c (c r) = r) (hJ : ∀ i j, c (J j i) = -J i j)
  (hXX : X ⬝ᵥ J *ᵥ (fun i => c (X i)) = 0) (hYY : Y ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 0)
  (hXY : X ⬝ᵥ J *ᵥ (fun i => c (Y i)) = 1)
include hc hJ hXY

theorem dot_yx : Y ⬝ᵥ J *ᵥ (fun i => c (X i)) = -1 := by
  rw [dotProduct_mulVec]
  have h := conj_mulVec c J hJ Y hc
  rw [show Y ᵥ* J = -(fun i => c ((J *ᵥ fun k => c (Y k)) i)) by rw [h, neg_neg]]
  rw [neg_dotProduct, ← conj_dot, dotProduct_comm (J *ᵥ _) X, hXY, map_one]


end Props

end GlobalTheory.LeviTorus

namespace GlobalTheory.LeviTorus

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2 τ, h.2.2.2 τ, star_star]

theorem cA_invol {σ : E →ₐ[F] E} (h : ∀ x, σ (σ x) = x) (a : AE F E) : cA σ (cA σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [cA, h]
  | add a b ha hb => simp [map_add (f := _), ha, hb]

theorem cA_incl (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR]

theorem form_incl (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    incV F x ⬝ᵥ incM F J *ᵥ (fun i => cA σ (incV F y i)) = inclR (F := F) (AF F) (form σ J x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [form, incV, incM, cA_incl, dotProduct, mulVec, map_sum, map_mul]

theorem vecMul_incM (σ : E →ₐ[F] E) {n k : ℕ} (J : Matrix (Fin n) (Fin n) E) (A : Matrix (Fin n) (Fin k) E) (y : Fin n → E) :
    (incM F J *ᵥ fun i => cA σ (incV F y i)) ᵥ* incM F A =
      fun j => inclR (F := F) (AF F) (form σ J (A *ᵥ Pi.single j 1) y) := by
  funext j
  rw [← form_incl]
  simp only [vecMul, dotProduct, incV, incM, Matrix.map_apply, mulVec_single_one]
  exact Finset.sum_congr rfl fun k _ => by rw [mul_comm]; rfl

end GlobalTheory.LeviTorus
end
end

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.LeviUnitary

open Matrix

section Ring

variable {R : Type} [CommRing R] {n m : ℕ} {ι : Matrix (Fin n) (Fin m) R} {π : Matrix (Fin m) (Fin n) R}

theorem ext_mul (hπ : π * ι = 1) (g h : Matrix (Fin m) (Fin m) R) :
    (1 + ι * (g - 1) * π) * (1 + ι * (h - 1) * π) = 1 + ι * (g * h - 1) * π := by
  have h1 : ι * (g - 1) * π * (ι * (h - 1) * π) = ι * ((g - 1) * (h - 1)) * π := by
    calc _ = ι * (g - 1) * (π * ι) * (h - 1) * π := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hπ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have h2 : g * h - 1 = (h - 1) + (g - 1) + (g - 1) * (h - 1) := by noncomm_ring
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, h1, h2]
  simp only [Matrix.mul_add, Matrix.add_mul, add_assoc]

theorem ext_unitary (c : R →+* R) {J : Matrix (Fin n) (Fin n) R} {J₁ : Matrix (Fin m) (Fin m) R} (hπ : π * ι = 1)
    (h1 : J * ι.map c = πᵀ * J₁) (h2 : ιᵀ * J = J₁ * π.map c) {g : Matrix (Fin m) (Fin m) R} (hg : gᵀ * J₁ * g.map c = J₁) :
    (1 + ι * (g - 1) * π)ᵀ * J * (1 + ι * (g - 1) * π).map c = J := by
  have hm : (1 + ι * (g - 1) * π).map c = 1 + ι.map c * (g.map c - 1) * π.map c := by
    rw [Matrix.map_add _ (map_add c), Matrix.map_mul, Matrix.map_mul, Matrix.map_sub _ (map_sub c),
      Matrix.map_one _ (map_zero c) (map_one c), Matrix.map_one _ (map_zero c) (map_one c)]
  have h3 : π.map c * ι.map c = 1 := by rw [← Matrix.map_mul, hπ, Matrix.map_one _ (map_zero c) (map_one c)]
  have ht : (1 + ι * (g - 1) * π)ᵀ = 1 + πᵀ * (gᵀ - 1) * ιᵀ := by
    simp only [transpose_add, transpose_mul, transpose_sub, transpose_one, Matrix.mul_assoc]
  have e1 : πᵀ * (gᵀ - 1) * ιᵀ * J = πᵀ * ((gᵀ - 1) * J₁) * π.map c := by
    rw [Matrix.mul_assoc _ ιᵀ, h2]; simp only [Matrix.mul_assoc]
  have e2 : J * (ι.map c * (g.map c - 1) * π.map c) = πᵀ * (J₁ * (g.map c - 1)) * π.map c := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1]; simp only [Matrix.mul_assoc]
  have e3 : πᵀ * ((gᵀ - 1) * J₁) * π.map c * (ι.map c * (g.map c - 1) * π.map c) =
      πᵀ * ((gᵀ - 1) * J₁ * (g.map c - 1)) * π.map c := by
    calc _ = πᵀ * ((gᵀ - 1) * J₁) * (π.map c * ι.map c) * (g.map c - 1) * π.map c := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h3, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have e4 : (gᵀ - 1) * J₁ + (J₁ * (g.map c - 1) + (gᵀ - 1) * J₁ * (g.map c - 1)) = 0 := by
    have : (gᵀ - 1) * J₁ + (J₁ * (g.map c - 1) + (gᵀ - 1) * J₁ * (g.map c - 1)) = gᵀ * J₁ * g.map c - J₁ := by noncomm_ring
    rw [this, hg, sub_self]
  rw [hm, ht, Matrix.add_mul, Matrix.one_mul, e1, Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, e2, e3, add_assoc,
    ← Matrix.add_mul, ← Matrix.add_mul, ← Matrix.mul_add, ← Matrix.mul_add, e4]
  simp

end Ring

theorem det_ne_zero_of_hasSig {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨rfl, A, hA⟩ := h
  intro h0
  let A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id finSumFinEquiv.symm
  have h1 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix
      finSumFinEquiv.symm finSumFinEquiv.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply]
  have h2 := congrArg Matrix.det h1
  rw [det_mul, det_mul, h0, det_submatrix_equiv_self, det_fromBlocks_zero₂₁, det_one, det_neg, det_one] at h2
  simp at h2
  exact absurd h2.symm (by simp)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem incM_mul {k l p : ℕ} (A : Matrix (Fin k) (Fin l) E) (A' : Matrix (Fin l) (Fin p) E) :
    incM F (A * A') = incM F A * incM F A' := Matrix.map_mul

theorem incM_conj {k l : ℕ} (A : Matrix (Fin k) (Fin l) E) :
    (incM F A).map (cA σ).toRingHom = incM F (A.map σ) := by
  ext i j
  exact GlobalTheory.LeviTorus.cA_incl σ (A i j)

theorem incM_mulVec {k l : ℕ} (A : Matrix (Fin k) (Fin l) E) (x : Fin l → E) :
    incM F A *ᵥ incV F x = incV F (A *ᵥ x) := by
  funext i
  set_option synthInstance.maxHeartbeats 100000 in
    simp [incM, incV, mulVec, dotProduct, map_sum, map_mul]

theorem exists_proj {B : Base F E} (hB : B.IsGood σ) {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {r s r₁ s₁ : ℕ}
    (hW : W.IsSkew σ B r s) (hW₁ : W₁.IsSkew σ B r₁ s₁) {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hA : H'.IsAdapted σ B W W₁ i₀ i₁) :
    ∃ π : Matrix (Fin d₁) (Fin d) E, π * H'.ι = 1 ∧ W.J * H'.ι.map σ = πᵀ * W₁.J ∧ H'.ιᵀ * W.J = W₁.J * π.map σ ∧
      π *ᵥ H'.x = 0 ∧ π *ᵥ H'.y = 0 := by
  have hσ := GlobalTheory.LeviTorus.sigma_invol hB.cm
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdet : IsUnit W₁.J.det := by
    have h := det_ne_zero_of_hasSig (hW₁.sig w)
    rw [det_smul] at h
    have h' := right_ne_zero_of_mul h
    rw [isUnit_iff_ne_zero]
    intro h0
    apply h'
    have := RingHom.map_det (B.emb w).1 W₁.J
    rw [h0, map_zero] at this
    exact this.symm
  have mm : ∀ {k l : ℕ} (A : Matrix (Fin k) (Fin l) E), (A.map σ).map σ = A := fun A => by
    ext i j; exact hσ _
  have mul : ∀ {k l p : ℕ} (A : Matrix (Fin k) (Fin l) E) (A' : Matrix (Fin l) (Fin p) E),
      (A * A').map σ = A.map σ * A'.map σ := fun A A' => Matrix.map_mul (f := σ.toRingHom)
  have sk : W.J.map σ = -W.Jᵀ := by ext i j; exact hW.skew j i
  have sk₁ : W₁.J.map σ = -W₁.Jᵀ := by ext i j; exact hW₁.skew j i
  set P : Matrix (Fin d₁) (Fin d) E := W₁.J⁻¹ * (H'.ιᵀ * W.J) with hP
  have h2 : H'.ιᵀ * W.J = W₁.J * P := by rw [hP, Matrix.mul_nonsing_inv_cancel_left _ _ hdet]
  have hz : ∀ z : Fin d → E, (∀ u, form σ W.J (H'.ι *ᵥ u) z = 0) → P.map σ *ᵥ z = 0 := by
    intro z hz
    have e1 : (H'.ιᵀ * W.J) *ᵥ (fun i => σ (z i)) = 0 := by
      funext j
      have := hz (Pi.single j 1)
      rw [form, mulVec_single_one] at this
      rw [← mulVec_mulVec]
      exact this
    have e2 : P *ᵥ (fun i => σ (z i)) = 0 := by rw [hP, ← mulVec_mulVec, e1, mulVec_zero]
    funext j
    have := congrArg σ (congrFun e2 j)
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [mulVec, dotProduct, map_sum, map_mul, hσ] using this
  refine ⟨P.map σ, ?_, ?_, by rw [mm, h2], hz _ fun u => (hA.orth u).1, hz _ fun u => (hA.orth u).2⟩
  · have : P * H'.ι.map σ = 1 := by rw [hP, Matrix.mul_assoc, hA.gram, Matrix.nonsing_inv_mul _ hdet]
    rw [← mm H'.ι, ← mul, this]
    exact Matrix.map_one _ (map_zero σ) (map_one σ)
  · have := congrArg (fun A => (Matrix.map A σ)ᵀ) h2
    simp only [mul, sk, sk₁, transpose_mul, transpose_neg, transpose_transpose, Matrix.neg_mul, Matrix.mul_neg,
      neg_inj] at this
    exact this

theorem exists_isLevi {B : Base F E} (hB : B.IsGood σ) {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {r s r₁ s₁ : ℕ}
    (hW : W.IsSkew σ B r s) (hW₁ : W₁.IsSkew σ B r₁ s₁) {H' : Plane E d d₁} {i₀ i₁ : ℕ} (hA : H'.IsAdapted σ B W W₁ i₀ i₁)
    (h₁ : UA σ W₁.J) : ∃ m : UA σ W.J, IsLevi H' 1 h₁ m := by
  obtain ⟨π, p1, p2, p3, p4, p5⟩ := exists_proj hB hW hW₁ hA
  have q1 : incM F π * incM F H'.ι = 1 := by
    rw [← incM_mul, p1]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have q2 : incM F W.J * (incM F H'.ι).map (cA σ).toRingHom = (incM F π)ᵀ * incM F W₁.J := by
    rw [incM_conj, ← incM_mul, p2, incM_mul]; rfl
  have q3 : (incM F H'.ι)ᵀ * incM F W.J = incM F W₁.J * (incM F π).map (cA σ).toRingHom := by
    rw [incM_conj, ← incM_mul, ← p3, incM_mul]; rfl
  have hfix : ∀ z, π *ᵥ z = 0 → (1 + incM F H'.ι * (mat h₁ - 1) * incM F π) *ᵥ incV F z = incV F z := by
    intro z hz
    have h0 : incV F (0 : Fin d₁ → E) = 0 := by funext i; exact map_zero _
    rw [add_mulVec, one_mulVec, ← mulVec_mulVec, incM_mulVec, hz, h0, mulVec_zero, add_zero]
  refine ⟨⟨⟨1 + incM F H'.ι * (mat h₁ - 1) * incM F π, 1 + incM F H'.ι * ((h₁.1⁻¹).1 - 1) * incM F π, ?_, ?_⟩, ?_⟩,
    ?_, ?_, ?_⟩
  · rw [ext_mul q1, mat, Units.mul_inv]; simp
  · rw [ext_mul q1, mat, Units.inv_mul]; simp
  · exact ext_unitary (cA σ).toRingHom q1 q2 q3 h₁.2
  · rw [Units.val_one, one_smul]; exact hfix _ p4
  · rw [inv_one, Units.val_one, map_one, one_smul]; exact hfix _ p5
  · show (1 + incM F H'.ι * (mat h₁ - 1) * incM F π) * incM F H'.ι = _
    rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, q1, Matrix.mul_one, Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]

end GlobalTheory.LeviUnitary

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedQuadraticDatumAtInertPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedQuadraticDatumAtInertPlace
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

namespace GlobalTheory.InertUQ

open IsDedekindDomain.HeightOneSpectrum

variable {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E))

theorem mem_max_iff (x : w.adicCompletionIntegers E) :
    x ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) ↔ Valued.v (x : w.adicCompletion E) < 1 := by
  have hI := Valuation.valuationSubring.integers (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  have hx : Valued.v (x : w.adicCompletion E) ≤ 1 := x.2
  constructor
  · intro hn
    refine lt_of_le_of_ne hx fun h => hn ?_
    exact (hI.isUnit_iff_valuation_eq_one (x := x)).2 h
  · intro hlt hu
    exact (ne_of_lt hlt) ((hI.isUnit_iff_valuation_eq_one (x := x)).1 hu)

private lemma withZero_lt_one_iff_le_exp_neg_one (g : WithZero (Multiplicative ℤ)) : g < 1 ↔ g ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · rw [← WithZero.exp_log hg, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

private lemma mem_span_pow_iff_valuation_le_exp_neg_one_pow (p : w.adicCompletionIntegers E)
    (hp : Valued.v (p : w.adicCompletion E) = WithZero.exp (-1 : ℤ)) (n : ℕ)
    (a : w.adicCompletionIntegers E) :
    a ∈ Ideal.span {p ^ n} ↔ Valued.v (a : w.adicCompletion E) ≤ WithZero.exp (-1 : ℤ) ^ n := by
  have hp0 : (p : w.adicCompletion E) ≠ 0 := by
    intro h
    rw [h, map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨b, rfl⟩
    have hb : Valued.v (b : w.adicCompletion E) ≤ 1 := b.2
    push_cast
    rw [map_mul, map_pow, hp]
    exact mul_le_of_le_one_right' hb
  · intro ha
    have hpos : (0 : WithZero (Multiplicative ℤ)) < WithZero.exp (-1 : ℤ) ^ n :=
      zero_lt_iff.2 (pow_ne_zero _ WithZero.exp_ne_zero)
    have hb : Valued.v ((a : w.adicCompletion E) / (p : w.adicCompletion E) ^ n) ≤ 1 := by
      rw [map_div₀, map_pow, hp]
      exact (div_le_one₀ hpos).2 ha
    refine ⟨⟨_, hb⟩, ?_⟩
    apply Subtype.ext
    push_cast
    field_simp

private lemma maximalIdeal_eq_span_of_valuation_eq_exp_neg_one (p : w.adicCompletionIntegers E)
    (hp : Valued.v (p : w.adicCompletion E) = WithZero.exp (-1 : ℤ)) :
    IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) = Ideal.span {p} := by
  ext a
  have h := mem_span_pow_iff_valuation_le_exp_neg_one_pow w p hp 1 a
  rw [pow_one, pow_one] at h
  rw [h, mem_max_iff, withZero_lt_one_iff_le_exp_neg_one]

theorem valuation_max_eq (ϖ : w.adicCompletion E) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ))
    (x : w.adicCompletion E) :
    (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation (w.adicCompletion E) x
      = Valued.v x := by
  have hϖ1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ]
    exact ((withZero_lt_one_iff_le_exp_neg_one _).2 le_rfl).le
  let p : w.adicCompletionIntegers E := ⟨ϖ, hϖ1⟩
  have hp : Valued.v (p : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := hϖ
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  have hp0 : p ≠ 0 := fun h => hϖ0 (congrArg Subtype.val h)
  have hVp : (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation
      (w.adicCompletion E) ϖ = WithZero.exp (-1 : ℤ) := by
    have h1 := (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation_of_algebraMap
      (K := w.adicCompletion E) p
    rw [(IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).intValuation_singleton hp0
      (maximalIdeal_eq_span_of_valuation_eq_exp_neg_one w p hp)] at h1
    exact h1
  have hVu : ∀ a : w.adicCompletionIntegers E, Valued.v (a : w.adicCompletion E) = 1 →
      (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation
        (w.adicCompletion E) a = 1 := by
    intro a ha
    have h1 := (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation_of_algebraMap
      (K := w.adicCompletion E) a
    refine h1.trans (HeightOneSpectrum.intValuation_eq_one_iff.2 fun hmem => ?_)
    have := (mem_max_iff w a).1 hmem
    rw [ha] at this
    exact lt_irrefl _ this
  by_cases hx : x = 0
  · simp [hx]
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  obtain ⟨k, hk⟩ : ∃ k : ℤ, Valued.v x = WithZero.exp k := ⟨_, (WithZero.exp_log hvx).symm⟩
  have hy : Valued.v (x * ϖ ^ k) = 1 := by
    rw [map_mul, map_zpow₀, hϖ, hk, ← WithZero.exp_zsmul, ← WithZero.exp_add, WithZero.exp_eq_one]
    simp
  have hV : (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation
      (w.adicCompletion E) (x * ϖ ^ k) = 1 := hVu ⟨x * ϖ ^ k, hy.le⟩ hy
  have hxe : x = (x * ϖ ^ k) * ϖ ^ (-k) := by
    rw [mul_assoc, ← zpow_add₀ hϖ0, add_neg_cancel, zpow_zero, mul_one]
  have e1 : (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation
      (w.adicCompletion E) x = (IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation
      (w.adicCompletion E) (x * ϖ ^ k) * (IsDiscreteValuationRing.maximalIdeal
        (w.adicCompletionIntegers E)).valuation (w.adicCompletion E) ϖ ^ (-k) := by
    rw [← map_zpow₀, ← Valuation.map_mul, ← hxe]
  have e2 : Valued.v x = Valued.v (x * ϖ ^ k) * Valued.v ϖ ^ (-k) := by
    rw [← map_zpow₀, ← Valuation.map_mul, ← hxe]
  rw [e1, e2, hV, hVp, hy, hϖ]

private lemma isAdicComplete_maximalIdeal_adicCompletionIntegers (ϖ : w.adicCompletion E) (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) :
    IsAdicComplete (IsLocalRing.maximalIdeal (w.adicCompletionIntegers E))
      (w.adicCompletionIntegers E) := by
  have hϖ1 : Valued.v ϖ ≤ 1 := by
    rw [hϖ]
    exact ((withZero_lt_one_iff_le_exp_neg_one _).2 le_rfl).le
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ
    exact WithZero.exp_ne_zero hϖ.symm
  let p : w.adicCompletionIntegers E := ⟨ϖ, hϖ1⟩
  have hp : Valued.v (p : w.adicCompletion E) = WithZero.exp (-1 : ℤ) := hϖ
  have hpow : ∀ (n : ℕ) (a : w.adicCompletionIntegers E),
      a ∈ (IsLocalRing.maximalIdeal (w.adicCompletionIntegers E)) ^ n ↔
        Valued.v (a : w.adicCompletion E) ≤ Valued.v ϖ ^ n := by
    intro n a
    rw [maximalIdeal_eq_span_of_valuation_eq_exp_neg_one w p hp, Ideal.span_singleton_pow, hϖ]
    exact mem_span_pow_iff_valuation_le_exp_neg_one_pow w p hp n a
  have hadic : IsAdic (IsLocalRing.maximalIdeal (w.adicCompletionIntegers E)) := by
    rw [isAdic_iff]
    constructor
    · intro n
      have hset : ((IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) ^ n : Ideal (w.adicCompletionIntegers E)) :
          Set (w.adicCompletionIntegers E)) =
          Subtype.val ⁻¹' {y : w.adicCompletion E |
            (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).restrict y ≤
              (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).restrict (ϖ ^ n)} := by
        ext a
        simp only [SetLike.mem_coe, Set.mem_preimage, Set.mem_ofPred_eq]
        rw [Valuation.restrict_le_iff, map_pow]
        exact hpow n a
      rw [hset]
      refine (Valued.isOpen_closedBall _ ?_).preimage continuous_subtype_val
      intro h0
      have h1 : Valued.v (ϖ ^ n) = 0 := by
        rw [← Valuation.embedding_restrict, h0, map_zero]
      exact pow_ne_zero n hϖ0 ((Valuation.zero_iff _).1 h1)
    · intro s hs
      obtain ⟨u, hu, hus⟩ := mem_nhds_subtype _ _ _ |>.1 hs
      rw [ZeroMemClass.coe_zero, Valued.mem_nhds_zero] at hu
      obtain ⟨γ, hγ⟩ := hu
      obtain ⟨n, hn⟩ := Valued.exists_pow_lt_of_le_exp_neg_one (R := w.adicCompletion E) hϖ.le
        (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding
          (f := ((Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))) : (w.adicCompletion E) →*₀ WithZero (Multiplicative ℤ)))).toMonoidHom γ)
      refine ⟨n, fun a ha => hus (hγ ?_)⟩
      show (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).restrict
        (a : w.adicCompletion E) < γ.1
      rw [Valuation.restrict_lt_iff_lt_embedding]
      exact lt_of_le_of_lt ((hpow n a).1 ha) (by simpa using hn)
  have hcl : IsClosed ((w.adicCompletionIntegers E : Set (w.adicCompletion E))) :=
    Valued.isClosed_valuationSubring _
  have : CompleteSpace (w.adicCompletionIntegers E) := hcl.completeSpace_coe
  exact hadic.isAdicComplete_iff.mpr ⟨inferInstance, inferInstance⟩

private lemma neg_log_valuation_eq_ordL (x : w.adicCompletion E) : -WithZero.log (Valued.v x) = ordL x := by
  unfold ordL
  split_ifs with h
  · rw [h, WithZero.log_zero, neg_zero]
  · congr 1
    conv_lhs => rw [← WithZero.coe_unzero h]
    rfl

theorem exists_uq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, ¬ IsSplitAt w → ∃ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) ∧ (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) ∧ (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) ∧ qV E w = K.q ^ 2 := by
  intro E _ _ _ hU w hw
  obtain ⟨-, hcc, hiso, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  obtain ⟨-, ⟨ϖ, q, hUI, hq⟩, -, -⟩ := hns hw
  obtain ⟨-, -, -, hϖ, ⟨x₀, hx₀, hx₀'⟩, hq2, hcard⟩ := hUI
  have hϖ' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hϖ
  have hc : Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) = q ^ 2 := hcard
  have := isAdicComplete_maximalIdeal_adicCompletionIntegers w ϖ hϖ'
  have : Finite (IsLocalRing.ResidueField (w.adicCompletionIntegers E)) := by
    apply Nat.finite_of_card_ne_zero
    rw [hc]
    exact pow_ne_zero 2 (by omega)
  have : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  let σ : w.adicCompletion E ≃+* w.adicCompletion E :=
    RingEquiv.ofRingHom (cj w) (cj w) (RingHom.ext hcc) (RingHom.ext hcc)
  have hx₀A : Valued.v x₀ ≤ 1 := hx₀
  have hσx₀ : Valued.v (σ x₀) ≤ 1 := by
    show Valued.v (cj w x₀) ≤ 1
    rw [hiso]
    exact hx₀A
  have hint : ∀ x : w.adicCompletionIntegers E, ∃ y : w.adicCompletionIntegers E,
      σ (algebraMap _ (w.adicCompletion E) x) = algebraMap _ (w.adicCompletion E) y := by
    intro x
    have hx : Valued.v (σ x) ≤ 1 := by
      show Valued.v (cj w x) ≤ 1
      rw [hiso]
      exact x.2
    exact ⟨⟨σ x, hx⟩, rfl⟩
  have hres : ∃ x y : w.adicCompletionIntegers E,
      σ (algebraMap _ (w.adicCompletion E) x) = algebraMap _ (w.adicCompletion E) y ∧
        x - y ∉ IsLocalRing.maximalIdeal (w.adicCompletionIntegers E) := by
    refine ⟨⟨x₀, hx₀A⟩, ⟨σ x₀, hσx₀⟩, rfl, fun hm => ?_⟩
    have h1 := (mem_max_iff w _).1 hm
    have h2 : Valued.v (x₀ - σ x₀) = 1 := by
      rw [Valuation.map_sub_swap]
      exact hx₀'
    push_cast at h1
    rw [h2] at h1
    exact lt_irrefl _ h1
  let K : GlobalTheory.UnitLemma.UQ :=
    { O := w.adicCompletionIntegers E
      E := w.adicCompletion E
      c := σ
      c_c := hcc
      c_int := hint
      c_res := hres
      q := q
      card_res := hc }
  refine ⟨K, RingEquiv.refl _, fun x => rfl, ?_, ?_, hq⟩
  · intro x
    constructor
    · rintro ⟨a, rfl⟩
      exact a.2
    · intro h
      exact ⟨⟨x, h⟩, rfl⟩
  · intro x
    show -WithZero.log ((IsDiscreteValuationRing.maximalIdeal (w.adicCompletionIntegers E)).valuation
      (w.adicCompletion E) x) = ordL x
    rw [valuation_max_eq w ϖ hϖ' x]
    exact neg_log_valuation_eq_ordL w x

end GlobalTheory.InertUQ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedQuadraticDatumAtInertPlaceStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramifiedQuadraticDatum_at_inertPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ w : Pl E, ¬ IsSplitAt w → ∃ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) ∧ (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) ∧ (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) ∧ qV E w = K.q ^ 2 := by
  first | exact @GlobalTheory.InertUQ.exists_uq | exact GlobalTheory.InertUQ.exists_uq | (intros; apply GlobalTheory.InertUQ.exists_uq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLinearHomProd
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

noncomputable section

namespace GlobalTheory.FlatCM.HomLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ} (X : CMObj H K ρ σ₁ p q)

def coords : Set (Fin p → E) :=
  {c | ∃ n : ℕ, 0 < n ∧ ∃ x : Fin p → 𝓞 E, (∀ a, (x a : E) = n * c a) ∧
    ∃ f : (X.A true).t.G ⟶ X.B.t.G, Serre.IsLinearHom (X.A true).t.act X.B.t.act f ∧
      f ^ n = ∏ a, ((X.A true).t.act.act (x a) ≫ phiP X a)}

def lat : Submodule (𝓞 E) (Fin p → E) := Submodule.span (𝓞 E) (coords X)

theorem isLinearHom_prod (x : Fin p → 𝓞 E) :
    Serre.IsLinearHom (X.A true).t.act X.B.t.act (∏ a, ((X.A true).t.act.act (x a) ≫ phiP X a)) := by
  classical
  refine Finset.prod_induction _ (Serre.IsLinearHom (X.A true).t.act X.B.t.act)
    (fun f g hf hg => hf.mul hg) (Serre.IsLinearHom.one _ _) fun a _ => ?_
  exact (Serre.IsLinearHom.act _ _).comp (X.lin (Sum.inl a))

theorem intl_mem (x : Fin p → 𝓞 E) : (fun a => (x a : E)) ∈ lat X :=
  Submodule.subset_span ⟨1, one_pos, x, fun a => by simp, _, isLinearHom_prod X x, pow_one _⟩

end GlobalTheory.FlatCM.HomLat

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarSumLeibniz
open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.CxForm

theorem coefwise_dbar_sum_smul {n : ℕ} {ι : Type} [Fintype ι] {c : ι → V n → ℂ} {F : ι → V n → Alt n} {v : V n}
    (hc : ∀ i, DifferentiableAt ℝ (c i) v)
    (hF : ∀ i S, DifferentiableAt ℝ (fun x => (bas n).repr (F i x) S) v) (w : V n) :
    coefwise (fun f => GlobalTheory.dbar f v w) (fun x => ∑ i, c i x • F i x) =
      ∑ i, (GlobalTheory.dbar (c i) v w • F i v + c i v • coefwise (fun f => GlobalTheory.dbar f v w) (F i)) := by
  have h (S : Finset (Fin (n + n))) :
      GlobalTheory.dbar (fun x => (bas n).repr (∑ i, c i x • F i x) S) v w =
        ∑ i, (c i v * GlobalTheory.dbar (fun x => (bas n).repr (F i x) S) v w +
          GlobalTheory.dbar (c i) v w * (bas n).repr (F i v) S) := by
    have e : (fun x => (bas n).repr (∑ i, c i x • F i x) S) =
        fun x => ∑ i, c i x * (bas n).repr (F i x) S := by
      funext x
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, Finsupp.finsetSum_apply]
    rw [e, GlobalTheory.dbar_sum (A := fun i x => c i x * (bas n).repr (F i x) S) (fun i _ => (hc i).mul (hF i S)),
      ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => GlobalTheory.dbar_mul (hc i) (hF i S) w
  simp only [coefwise, h, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [← (bas n).sum_repr (F i v)]
  simp only [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  rw [add_comm]

theorem dbarAt_sum_smul {n : ℕ} {ι : Type} [Fintype ι] {c : ι → V n → ℂ} {F : ι → V n → Alt n} {v : V n}
    (hc : ∀ i, DifferentiableAt ℝ (c i) v)
    (hF : ∀ i S, DifferentiableAt ℝ (fun x => (bas n).repr (F i x) S) v) :
    dbarAt (fun x => ∑ i, c i x • F i x) v =
      ∑ i, ((∑ a, GlobalTheory.dbar (c i) v (coordVec a) • dzb a) * F i v + c i v • dbarAt (F i) v) := by
  simp only [dbarAt, coefwise_dbar_sum_smul hc hF, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_add, mul_smul_comm, smul_mul_assoc, Finset.sum_mul, Finset.sum_add_distrib, Finset.smul_sum]

end GlobalTheory.CxForm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasDelFinsetSum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasDelFinsetSum
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

namespace GlobalTheory.CxForm.HolAtlas

theorem del_finset_sum {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) {N : ℕ}
    (α : Fin N → A.Fld) (hα : ∀ j, A.IsForm (α j)) : A.del (∑ j, α j) = ∑ j, A.del (α j) := by
  funext x
  have hloc : ∀ w, A.loc (∑ j, α j) x.1.1 w = ∑ j, A.loc (α j) x.1.1 w := by
    intro w
    by_cases hw : w ∈ (A.e x.1.1).target
    · simp only [GlobalTheory.CxForm.HolAtlas.loc, hw, dif_pos]
      exact Finset.sum_apply _ _ _
    · simp [GlobalTheory.CxForm.HolAtlas.loc, hw]
  have hx : x.crd ∈ (A.e x.1.1).target := x.ch.map_source x.2
  have hdiff : ∀ j S, DifferentiableAt ℝ (fun w => (GlobalTheory.CxForm.bas n).repr (A.loc (α j) x.1.1 w) S) x.crd :=
    fun j S => (((hα j).smooth x.1.1 S).differentiableOn (by simp)).differentiableAt
      ((A.e x.1.1).open_target.mem_nhds hx)
  have key : ∀ S u, GlobalTheory.del (fun w => (GlobalTheory.CxForm.bas n).repr (A.loc (∑ j, α j) x.1.1 w) S) x.crd u =
      ∑ j, GlobalTheory.del (fun w => (GlobalTheory.CxForm.bas n).repr (A.loc (α j) x.1.1 w) S) x.crd u := by
    intro S u
    have e : (fun w => (GlobalTheory.CxForm.bas n).repr (A.loc (∑ j, α j) x.1.1 w) S) =
        fun w => ∑ j ∈ Finset.univ, (GlobalTheory.CxForm.bas n).repr (A.loc (α j) x.1.1 w) S := by
      funext w; rw [hloc, map_sum, Finsupp.finsetSum_apply]
    rw [e, GlobalTheory.del_sum (fun j _ => hdiff j S), ContinuousLinearMap.sum_apply]
  rw [Finset.sum_apply]
  simp only [GlobalTheory.CxForm.HolAtlas.del, GlobalTheory.CxForm.delAt, GlobalTheory.CxForm.coefwise, key, Finset.sum_smul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Finset.sum_comm

end GlobalTheory.CxForm.HolAtlas
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasDelFinsetSumStatement
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holAtlas_del_finset_sum : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) {N : ℕ} (α : Fin N → A.Fld), (∀ j, A.IsForm (α j)) → A.del (∑ j, α j) = ∑ j, A.del (α j) := by
  first | exact @GlobalTheory.CxForm.HolAtlas.del_finset_sum | exact GlobalTheory.CxForm.HolAtlas.del_finset_sum | (intros; apply GlobalTheory.CxForm.HolAtlas.del_finset_sum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet
open IsDedekindDomain
open GlobalTheory.Doubling (absE absEv absEw)

namespace GlobalTheory.EisMidHt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}


variable (F) in
def adVec (z : Fin n → E) : Fin n → AF F ⊗[F] E := fun i => inclR (F := F) (AF F) (z i)


variable (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)

end GlobalTheory.EisMidHt

end
end
