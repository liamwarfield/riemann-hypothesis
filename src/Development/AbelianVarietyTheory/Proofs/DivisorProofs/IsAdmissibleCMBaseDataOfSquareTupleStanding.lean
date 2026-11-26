module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateSplittingUnramifiedHyperspecialFix

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStanding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.BaseGoodPlace

open GlobalTheory.Idele WithZero
open GlobalTheory.StdDual (codiff codiff_ne_zero)

theorem psiUnr_of_not_le {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : ¬ differentIdeal ℤ (𝓞 D.host.F) ≤ v.asIdeal) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PsiUnr ψ v := by
  classical
  intro x
  have hc := GlobalTheory.SplitUnram.count_codiff_eq_zero v (fun h => hv (Ideal.le_of_dvd h))
  set α : Af D.host.F := GlobalTheory.AdelicU.singleFin v x with hα
  have hαv : α v = x := GlobalTheory.AdelicU.evalV_singleFin_self v x
  have hαw : ∀ w, w ≠ v → α w = 0 := fun w hw => GlobalTheory.AdelicU.evalV_singleFin_ne hw x
  have h := GlobalTheory.SplitUnram.mem_adelicIdeal_codiff_iff hψ.1.1 (GlobalTheory.StdRat.stdChar_fin_rat D ψ hψ) α
  have key : (∀ y ∈ v.adicCompletionIntegers D.host.F, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.psiLoc ψ v (x * y) = 1) ↔
      ∀ β : Af D.host.F, (∀ w, β w ∈ w.adicCompletionIntegers D.host.F) → ψ (pairA D.host.F 0 (β * α)) = 1 := by
    constructor
    · intro H β hβ
      have e : β * α = GlobalTheory.AdelicU.singleFin v (x * β v) := by
        apply GlobalTheory.AdelicU.af_ext
        intro u
        by_cases hu : u = v
        · subst hu
          rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_self, GlobalTheory.AdelicU.evalV_singleFin_self]
          change β u * x = x * β u
          ring
        · rw [map_mul, hα, GlobalTheory.AdelicU.evalV_singleFin_ne hu, GlobalTheory.AdelicU.evalV_singleFin_ne hu, mul_zero]
      rw [e]
      exact H _ (hβ v)
    · intro H y hy
      have e : GlobalTheory.AdelicU.singleFin v y * α = GlobalTheory.AdelicU.singleFin v (x * y) := by
        rw [hα, ← GlobalTheory.AdelicU.singleFin_mul, mul_comm]
      have := H (GlobalTheory.AdelicU.singleFin v y) (fun w => by
        by_cases hw : w = v
        · subst hw
          change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin w y) ∈ _
          rw [GlobalTheory.AdelicU.evalV_singleFin_self]
          exact hy
        · change Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV _ w (GlobalTheory.AdelicU.singleFin v y) ∈ _
          rw [GlobalTheory.AdelicU.evalV_singleFin_ne hw]
          exact zero_mem _)
      rw [e] at this
      exact this
  rw [key, ← h, mem_adelicIdeal_iff codiff_ne_zero, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro H
    have := H v
    rwa [hc, neg_zero, exp_zero, hαv] at this
  · intro H w
    by_cases hw : w = v
    · subst hw
      rw [hc, neg_zero, exp_zero, hαv]
      exact H
    · rw [hαw w hw, map_zero]
      exact zero_le

end GlobalTheory.BaseGoodPlace

namespace GlobalTheory.BaseGoodPlace

theorem trInf_eq_trace (D : D7) (x : Ainf D.host.F) :
    GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.trInf D x = Algebra.trace ℝ (mixedEmbedding.mixedSpace D.host.F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F x) := by
  classical
  rw [Algebra.trace_prod_apply, PI.ProdFormulaE.Tr.trace_pi, PI.ProdFormulaE.Tr.trace_pi,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  simp only [Algebra.trace_complex_apply]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.HeisenbergWeilMatrices.trInf
  rw [← Fintype.sum_subtype_add_sum_subtype (fun w : InfinitePlace D.host.F => w.IsReal)]
  congr 1
  · refine Fintype.sum_congr _ _ fun w => ?_
    rw [InfinitePlace.mult_isReal, Nat.cast_one, one_mul, ← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply w.2,
      Complex.ofReal_re]
    simp
  · refine Fintype.sum_equiv (Equiv.subtypeEquivRight fun w => InfinitePlace.not_isReal_iff_isComplex) _ _ fun w => ?_
    have h := InfinitePlace.mult_isComplex ⟨w.1, InfinitePlace.not_isReal_iff_isComplex.1 w.2⟩
    simp only at h
    rw [h]
    push_cast
    rfl

end GlobalTheory.BaseGoodPlace

namespace GlobalTheory.BaseGoodPlace

theorem isStd_of_isStdChar {D : D7} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := by
  refine ⟨hψ.1.1, hψ.1.2.2.1, fun a ha => ?_⟩
  have h2 : a.2 = 0 := by
    have h0 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F (pairA D.host.F 0 1) = 0 := by
      show InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (0 : Ainf D.host.F) = 0
      exact map_zero _
    have := congrArg Prod.snd (ha (pairA D.host.F 0 1) h0)
    rw [smul_eq_mul] at this
    have e : (1 : Af D.host.F) * a.2 = 0 := this
    simpa using e
  have ha' : a = pairA D.host.F a.1 0 := Prod.ext rfl h2
  obtain ⟨θ, hθ⟩ := hψ.2.1
  have h := hψ.2.2 θ hθ a.1
  rw [GlobalTheory.DualPairCompare.sum_infFam θ hθ, trInf_eq_trace] at h
  rw [ha']
  change psiInf D.host.F ψ a.1 = _
  rw [h]
  congr 1
  push_cast
  change _ = -(2 * ↑Real.pi * Complex.I) * ((Algebra.trace ℝ (mixedEmbedding.mixedSpace D.host.F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F a.1) : ℝ) : ℂ)
  ring

end GlobalTheory.BaseGoodPlace

namespace GlobalTheory.BaseGoodPlace

theorem exists_ram_prime_of_le (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F))
    (hle : differentIdeal ℤ (𝓞 D.host.F) ≤ v.asIdeal) :
    ∃ p : ℕ, p ∣ D.host.QS * D.host.q * D.host.d ∧ (p : 𝓞 D.host.F) ∈ v.asIdeal := by
  obtain ⟨p, -, h1, h2⟩ := UpperTheory.Ram.Fun.exists_prime_of_different_le D.host v hle
  exact ⟨p, h1, h2⟩

end GlobalTheory.BaseGoodPlace

namespace GlobalTheory.FunObj

theorem base_isGood_of_standing : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (W : G.Weil) (t : T),
    SquareStanding G t → ∀ B : Base D.host.F D.host.E, B.ψ = W.ψ →
      (∀ v ∈ B.P, ∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) → B.IsGood D.sp.cm.sig := by
  intro D T L sc G μ₀ _hL W t hS B hB hP
  have hψ : IsStdChar D B.ψ (-1) := hB ▸ W.ψ_std
  refine { cm := GlobalTheory.AdelicU.isCMExt_host D
           galois := D.host.hostE_isGalois
           unram := GlobalTheory.InertOfConj.unram D
           std := GlobalTheory.BaseGoodPlace.isStd_of_isStdChar hψ
           inert := ?_
           psiP := ?_ }
  · intro v w hw
    have hns : ¬ Formalism.MainNotions.KudlaSiegelWeil.Split D v := by
      rintro ⟨w1, w2, hne, h1, h2⟩
      apply hne
      have key : ∀ u : HeightOneSpectrum (𝓞 D.host.E), Formalism.MainNotions.KudlaSiegelWeil.Over D u v → u = w := fun u hu => by
        have hle : w.asIdeal ≤ u.asIdeal := by
          rw [← hw]
          exact Ideal.map_le_iff_le_comap.2 (le_of_eq hu.symm)
        exact HeightOneSpectrum.ext (w.isMaximal.eq_of_le u.isPrime.ne_top hle).symm
      rw [key w1 h1, key w2 h2]
    obtain ⟨h2, h3, hd, -⟩ := Formalism.MainNotions.KudlaSiegelWeil.inert_conditions_hold D v hns
    exact ⟨h2, h3, GlobalTheory.BaseGoodPlace.psiUnr_of_not_le hψ v hd⟩
  · intro v hv
    obtain ⟨w, hw, rfl⟩ := hP v hv
    refine GlobalTheory.BaseGoodPlace.psiUnr_of_not_le hψ _ fun hle => ?_
    obtain ⟨p, hp, hpv⟩ := GlobalTheory.BaseGoodPlace.exists_ram_prime_of_le D _ hle
    have hpw : (p : 𝓞 D.host.E) ∈ w.asIdeal := by
      have h := hpv
      change (p : 𝓞 D.host.F) ∈ w.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) at h
      rwa [Ideal.mem_comap, map_natCast] at h
    apply hS.2 w hw
    obtain ⟨c, hc⟩ := hp
    rw [hc]
    push_cast
    exact w.asIdeal.mul_mem_right _ (w.asIdeal.mul_mem_right _ hpw)

end GlobalTheory.FunObj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdmissibleCMBaseDataOfSquareTupleStandingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdmissibleCMBaseData_of_squareTupleStanding : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (W : G.Weil) (t : T),
    SquareStanding G t → ∀ B : Base D.host.F D.host.E, B.ψ = W.ψ →
      (∀ v ∈ B.P, ∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) → B.IsGood D.sp.cm.sig := by
  first | exact @GlobalTheory.FunObj.base_isGood_of_standing | exact GlobalTheory.FunObj.base_isGood_of_standing | (intros; apply GlobalTheory.FunObj.base_isGood_of_standing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousInvolutiveLocalTransposeInverse
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousInvolutiveLocalTransposeInverse
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct

noncomputable section

namespace GlobalTheory.LocTwist

variable {R : Type} [CommRing R]

theorem map_Phi (a : ℕ) (c : R →+* R) : c.mapMatrix (GlobalTheory.Tw.Phi a R) = GlobalTheory.Tw.Phi a R := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, GlobalTheory.Tw.Phi, Matrix.of_apply]
  split_ifs <;> simp

theorem Phi_mul_self (a : ℕ) : GlobalTheory.Tw.Phi a R * GlobalTheory.Tw.Phi a R = ((-1 : R) ^ (a - 1)) • (1 : Matrix (Fin a) (Fin a) R) := by
  ext i k
  simp only [Matrix.mul_apply, GlobalTheory.Tw.Phi, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i.rev]
  · have h1 : (i : ℕ) + (i.rev : ℕ) + 1 = a := by rw [Fin.val_rev]; omega
    rw [if_pos h1]
    by_cases h : k = i
    · subst h
      rw [if_pos (by rw [Fin.val_rev]; omega), Matrix.one_apply_eq, mul_one, ← pow_add]
      congr 1
      rw [Fin.val_rev]; omega
    · rw [if_neg (fun h2 => h (Fin.ext (by rw [Fin.val_rev] at h2; omega))), Matrix.one_apply_ne (Ne.symm h), mul_zero, mul_zero]
  · intro j _ hj
    rw [if_neg (fun h => hj (Fin.ext (by rw [Fin.val_rev]; omega))), zero_mul]
  · simp

theorem thetaGL_val (a : ℕ) (c : R →+* R) (g : GL (Fin a) R) :
    (thetaGL a c g).val = GlobalTheory.Tw.Phi a R * (c.mapMatrix (g⁻¹).val)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ := rfl

theorem thetaGL_thetaGL (a : ℕ) (c : R →+* R) (hc : ∀ x, c (c x) = x) (g : GL (Fin a) R) :
    thetaGL a c (thetaGL a c g) = g := by
  apply Units.ext
  have hT : ∀ M : Matrix (Fin a) (Fin a) R, c.mapMatrix Mᵀ = (c.mapMatrix M)ᵀ := fun M => rfl
  have hcc : ∀ M : Matrix (Fin a) (Fin a) R, c.mapMatrix (c.mapMatrix M) = M := fun M => by
    ext i j; exact hc _
  rw [thetaGL_val, ← map_inv, thetaGL_val, inv_inv, map_mul, map_mul, map_Phi, hT, hT, map_Phi, hcc]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  have hP := Phi_mul_self (R := R) a
  have hPt : (GlobalTheory.Tw.Phi a R)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ = ((-1 : R) ^ (a - 1)) • (1 : Matrix (Fin a) (Fin a) R) := by
    rw [← Matrix.transpose_mul, hP, Matrix.transpose_smul, Matrix.transpose_one]
  have e : ∀ X : Matrix (Fin a) (Fin a) R, GlobalTheory.Tw.Phi a R * (GlobalTheory.Tw.Phi a R * (X * (GlobalTheory.Tw.Phi a R)ᵀ)) * (GlobalTheory.Tw.Phi a R)ᵀ
      = (GlobalTheory.Tw.Phi a R * GlobalTheory.Tw.Phi a R) * X * ((GlobalTheory.Tw.Phi a R)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ) := by
    intro X; simp only [Matrix.mul_assoc]
  rw [e, hP, hPt, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul, ← mul_pow]
  simp

theorem continuous_thetaGL [TopologicalSpace R] [IsTopologicalRing R] (a : ℕ) (c : R →+* R) (hc : Continuous c) :
    Continuous (thetaGL a c) := by
  rw [Units.continuous_iff]
  refine ⟨?_, ?_⟩
  · change Continuous fun g : GL (Fin a) R => GlobalTheory.Tw.Phi a R * ((g⁻¹).val.map c)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ
    exact (continuous_const.matrix_mul ((Units.continuous_coe_inv.matrix_map hc).matrix_transpose)).matrix_mul
      continuous_const
  · have : (fun g : GL (Fin a) R => ((thetaGL a c g)⁻¹).val) =
        fun g => GlobalTheory.Tw.Phi a R * (g.val.map c)ᵀ * (GlobalTheory.Tw.Phi a R)ᵀ := by
      funext g
      rw [← map_inv, thetaGL_val, inv_inv]
      rfl
    rw [this]
    exact (continuous_const.matrix_mul ((Units.continuous_val.matrix_map hc).matrix_transpose)).matrix_mul
      continuous_const

end GlobalTheory.LocTwist

theorem GlobalTheory.BCT.thL_continuous_involutive : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E →
    ∀ (n : ℕ) (w : Pl E), Continuous (thL n w) ∧ ∀ g : GLw n w, thL n w (thL n w g) = g := by
  intro E _ _ _ hU n w
  obtain ⟨hcont, hinv, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
  unfold thL
  split_ifs
  · exact ⟨continuous_id, fun g => rfl⟩
  · exact ⟨GlobalTheory.LocTwist.continuous_thetaGL n (cj w) hcont, GlobalTheory.LocTwist.thetaGL_thetaGL n (cj w) hinv⟩
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousInvolutiveLocalTransposeInverseStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_involutive_local_transpose_inverse : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), Continuous (thL n w) ∧ ∀ g : GLw n w, thL n w (thL n w g) = g := by
  first | exact @GlobalTheory.BCT.thL_continuous_involutive | exact GlobalTheory.BCT.thL_continuous_involutive | (intros; apply GlobalTheory.BCT.thL_continuous_involutive <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulIntSingle
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.ThetaDenom


variable (F : Type) [Field F] [NumberField F] in
def IsMulInt {κ : Type} (M : ℕ) (z : κ → AF F) : Prop :=
  (∀ i, (z i).1 = 0) ∧ ∀ v i, ‖evFin F v (z i)‖ ≤ ‖(M : Fv F v)‖

theorem IsMulInt.mono {F : Type} [Field F] [NumberField F] {κ : Type} {k m : ℕ} {a : κ → AF F}
    (h : IsMulInt F (k * m) a) : IsMulInt F m a := by
  refine ⟨h.1, fun v i => (h.2 v i).trans ?_⟩
  rw [Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (GlobalTheory.SmoothForms.denom_norm_natCast_le_one v k)

def sand {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (g : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)) (h : Matrix (Fin d) (Fin d) (AF F ⊗[F] E)) :
    Matrix (Fin n) (Fin d) (AF F ⊗[F] E) →ₗ[AF F] Matrix (Fin n) (Fin d) (AF F ⊗[F] E) where
  toFun X := g * X * hᵀ
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' a X := by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

end GlobalTheory.ThetaDenom

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperspecialFixesVacuaGoodInertPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperspecialFixesVacuaGoodInertPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
namespace GlobalTheory.FixAllGood
open GlobalTheory.Hk3 (UnrPl VacFix)

theorem unrPl_mul {D : D7} {P : Pl D.host.E} {χ χ' : (AE D)ˣ →* Circle} (h : UnrPl P χ) (h' : UnrPl P χ') :
    UnrPl P (χ * χ') := fun e f hP x a b c => by
  rw [MonoidHom.mul_apply, h e f hP x a b c, h' e f hP x a b c, mul_one]

theorem unrPl_inv {D : D7} {P : Pl D.host.E} {χ : (AE D)ˣ →* Circle} (h : UnrPl P χ) :
    UnrPl P χ⁻¹ := fun e f hP x a b c => by
  rw [MonoidHom.inv_apply, h e f hP x a b c, inv_one]

theorem unrPl_chrStep {D : D7} {P : Pl D.host.E} {μ : ℕ → (AE D)ˣ →* Circle} {η : (AE D)ˣ →* Circle} {j : ℕ}
    (hμ : UnrPl P (μ j)) (hη : UnrPl P η) :
    UnrPl P (Lift.chrStep μ η j).1 ∧ UnrPl P (Lift.chrStep μ η j).2 := by
  unfold Lift.chrStep
  split_ifs
  · exact ⟨unrPl_mul hμ (unrPl_inv hη), hμ⟩
  · exact ⟨hμ, unrPl_mul hμ (unrPl_inv hη)⟩

theorem unrPl_chrTh {D : D7} {P : Pl D.host.E} {μ : ℕ → (AE D)ˣ →* Circle} {η : (AE D)ˣ →* Circle} {j : ℕ}
    (hμ : UnrPl P (μ j)) (hη : UnrPl P η) :
    UnrPl P (Lift.chrTh μ η j).1 ∧ UnrPl P (Lift.chrTh μ η j).2 :=
  ⟨hμ, unrPl_mul hμ (unrPl_inv hη)⟩

theorem fixAll_of_good : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → ∀ t P, Good R.toRealDat t P → Formalism.DivisionValues.conjPl P = P → FixAll R.toRealDat t P := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F h _ t P hP _
  have hu := GlobalTheory.T.splittingCharacters_unramified_offLevels R.toRealDat F.lv2 h.base.lev t P hP
  have hm := D.R.two_le_m
  refine ⟨fun k hk => ?_, ?_, fun i => ?_⟩
  · have hc := unrPl_chrStep (hu.2 (k + 1) (Nat.le_add_left _ _) hk.le) hu.1
    exact GlobalTheory.ConjVacFix.vacFix_of_unrPl _ _ _ _ _ _ P (h.fullY t k hk).datum hc.1 hc.2
  · have hc := unrPl_chrStep (hu.2 D.R.m (by omega) le_rfl) hu.1
    exact GlobalTheory.ConjVacFix.vacFix_of_unrPl _ _ _ _ _ _ P (h.fullX t).datum hc.1 hc.2
  · have hc := unrPl_chrTh (hu.2 ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2) hu.1
    exact GlobalTheory.ConjVacFix.vacFix_of_unrPl _ _ _ _ _ _ P (h.fullP i t).datum hc.1 hc.2

end GlobalTheory.FixAllGood
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperspecialFixesVacuaGoodInertPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperspecial_fixes_vacua_good_inert_place : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → ∀ t P, Good R.toRealDat t P → Formalism.DivisionValues.conjPl P = P → FixAll R.toRealDat t P := by
  first | exact @GlobalTheory.FixAllGood.fixAll_of_good | exact GlobalTheory.FixAllGood.fixAll_of_good | (intros; apply GlobalTheory.FixAllGood.fixAll_of_good <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadrati
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadrati
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LFun

open IsDedekindDomain NumberField MeasureTheory Matrix in
open Classical in
open scoped TensorProduct ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
private theorem isUnit_of_isUnit_norm' {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Free R S] [Module.Finite R S] (z : S) (h : IsUnit (Algebra.norm R z)) : IsUnit z := by
  rw [Algebra.norm_apply, ← LinearMap.isUnit_iff_isUnit_det] at h
  obtain ⟨u, hu⟩ := h
  refine IsUnit.of_mul_eq_one (u.inv 1) ?_
  have := congrArg (fun f : Module.End R S => f 1) u.val_inv
  simp only [hu] at this
  simpa using this


open IsDedekindDomain NumberField MeasureTheory Matrix in
open Classical in
open scoped TensorProduct ComplexConjugate in
attribute [local instance] _root_.Formalism.BasicNotions.Host.cmStar _root_.GlobalTheory.LocalData.complRel
  _root_.GlobalTheory.LocalData.isLocalField _root_.GlobalTheory.FunObj.borelKw
  _root_.GlobalTheory.FunObj.borelSpaceKw in
theorem _root_.GlobalTheory.LFun.resEtaPow_of_resEta : ∀ (F E : Type) [Field F]
    [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 →
    ∀ (χ : (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E)ˣ →* Circle) (n : ℕ), _root_.GlobalTheory.LFun.ResEta F E χ n →
      _root_.GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)).toMonoidHom).range χ n := by
  intro F E _ _ _ _ _ h2 χ n hχ
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  obtain ⟨⟨η, hη⟩, hall⟩ := hχ
  have hηe := hη.eq_normSign
  intro a
  rw [show χ ((Units.map ↑(algebraMap (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F ⊗[F] E))) a) = η a ^ n from
    hall η hη a]
  split_ifs with ha
  · obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 ha
    obtain ⟨t, rfl⟩ := hy
    obtain ⟨w, rfl⟩ := hz
    rw [map_mul, hη.2.1 t, hη.2.2.1 w]
    simp
  · have hs : _root_.GlobalTheory.IdeleNormChar.normSign E a ≠ 1 := by
      intro h1
      obtain ⟨t, ht⟩ := (_root_.GlobalTheory.IdeleNormChar.normSign_eq_one_iff E a).1 h1
      obtain ⟨z, hz⟩ := _root_.GlobalTheory.QuadSymbol.mem_normGroup_iff.1 ht
      have hzu : IsUnit z :=
        isUnit_of_isUnit_norm' z (hz ▸ Units.isUnit _)
      apply ha
      have hn : Units.map (Algebra.norm (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) hzu.unit =
          a / _root_.GlobalTheory.QuadSymbol.toUnits F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) t := by
        ext
        simpa using hz
      have key : a = _root_.GlobalTheory.QuadSymbol.toUnits F (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) t *
          Units.map (Algebra.norm (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) hzu.unit := by
        rw [hn, mul_div_cancel]
      rw [key]
      exact mul_mem (Subgroup.mem_sup_left ⟨t, rfl⟩) (Subgroup.mem_sup_right ⟨_, rfl⟩)
    have hm : _root_.GlobalTheory.IdeleNormChar.normSign E a = -1 := (Int.units_eq_one_or _).resolve_left hs
    rw [hηe]
    simp [hm, _root_.GlobalTheory.IdeleNormChar.signToCircle]

end GlobalTheory.LFun
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictsToQuadraticSignPowOfRestrictsToQuadratiStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.restrictsToQuadraticSignPow_of_restrictsToQuadraticCharPow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], Module.finrank F E = 2 →
    ∀ (χ : (AF F ⊗[F] E)ˣ →* Circle) (n : ℕ), GlobalTheory.LFun.ResEta F E χ n →
      GlobalTheory.WeilM.ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ n := by
  first | exact @GlobalTheory.LFun.resEtaPow_of_resEta | exact GlobalTheory.LFun.resEtaPow_of_resEta | (intros; apply GlobalTheory.LFun.resEtaPow_of_resEta <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjMapApply
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DoublingEv

def conjMap {X Y : Type} (T : (X → ℂ) →ₗ[ℂ] (Y → ℂ)) : (X → ℂ) →ₗ[ℂ] (Y → ℂ) where
  toFun φ := star (T (star φ))
  map_add' φ φ' := by rw [star_add, map_add (f := _), star_add]
  map_smul' c φ := by rw [star_smul, map_smul, star_smul, star_star]; rfl

theorem conjMap_apply {X Y : Type} (T : (X → ℂ) →ₗ[ℂ] (Y → ℂ)) (φ : X → ℂ) :
    conjMap T φ = star (T (star φ)) := rfl

variable {R : Type}

def partR {κ κ' κ₁' : Type} (T : ((κ' → R) → ℂ) →ₗ[ℂ] ((κ₁' → R) → ℂ)) :
    ((κ ⊕ κ' → R) → ℂ) →ₗ[ℂ] ((κ ⊕ κ₁' → R) → ℂ) where
  toFun Φ s := T (fun x₂ => Φ (Sum.elim (s ∘ Sum.inl) x₂)) (s ∘ Sum.inr)
  map_add' Φ Ψ := by funext s; exact congrFun (map_add T (fun x₂ => Φ (Sum.elim (s ∘ Sum.inl) x₂)) (fun x₂ => Ψ (Sum.elim (s ∘ Sum.inl) x₂))) _
  map_smul' c Φ := by funext s; exact congrFun (map_smul T c (fun x₂ => Φ (Sum.elim (s ∘ Sum.inl) x₂))) _

def partL {κ κ₁ κ' : Type} (T : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) :
    ((κ ⊕ κ' → R) → ℂ) →ₗ[ℂ] ((κ₁ ⊕ κ' → R) → ℂ) where
  toFun Φ s := T (fun x₁ => Φ (Sum.elim x₁ (s ∘ Sum.inr))) (s ∘ Sum.inl)
  map_add' Φ Ψ := by funext s; exact congrFun (map_add T (fun x₁ => Φ (Sum.elim x₁ (s ∘ Sum.inr))) (fun x₁ => Ψ (Sum.elim x₁ (s ∘ Sum.inr)))) _
  map_smul' c Φ := by funext s; exact congrFun (map_smul T c (fun x₁ => Φ (Sum.elim x₁ (s ∘ Sum.inr)))) _

theorem partR_apply {κ κ' κ₁' : Type} (T : ((κ' → R) → ℂ) →ₗ[ℂ] ((κ₁' → R) → ℂ)) (Φ : (κ ⊕ κ' → R) → ℂ)
    (s : κ ⊕ κ₁' → R) : partR (κ := κ) T Φ s = T (fun x₂ => Φ (Sum.elim (s ∘ Sum.inl) x₂)) (s ∘ Sum.inr) := rfl

theorem partL_apply {κ κ₁ κ' : Type} (T : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) (Φ : (κ ⊕ κ' → R) → ℂ)
    (s : κ₁ ⊕ κ' → R) : partL (κ' := κ') T Φ s = T (fun x₁ => Φ (Sum.elim x₁ (s ∘ Sum.inr))) (s ∘ Sum.inl) := rfl

def evDbl {κ κ₁ : Type} (e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) :
    ((κ ⊕ κ → R) → ℂ) →ₗ[ℂ] ((κ₁ ⊕ κ₁ → R) → ℂ) :=
  partL e ∘ₗ partR (conjMap e)

theorem evDbl_apply {κ κ₁ : Type} (e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) (Φ : (κ ⊕ κ → R) → ℂ)
    (s : κ₁ ⊕ κ₁ → R) : evDbl e Φ s =
      e (fun x₁ => conjMap e (fun x₂ => Φ (Sum.elim x₁ x₂)) (s ∘ Sum.inr)) (s ∘ Sum.inl) := by
  simp only [evDbl, LinearMap.comp_apply, partL_apply, partR_apply, Sum.elim_comp_inl, Sum.elim_comp_inr]

theorem evDbl_boxFun {κ κ₁ : Type} (e : ((κ → R) → ℂ) →ₗ[ℂ] ((κ₁ → R) → ℂ)) (φ₁ φ₂ : (κ → R) → ℂ) :
    evDbl e (boxFun φ₁ φ₂) = boxFun (e φ₁) (conjMap e φ₂) := by
  funext s
  rw [evDbl_apply]
  have h1 : ∀ x₁ : κ → R, (fun x₂ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) = φ₁ x₁ • φ₂ := fun x₁ => by
    funext x₂; simp [boxFun]
  have h2 : (fun x₁ => conjMap e (fun x₂ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) (s ∘ Sum.inr)) =
      conjMap e φ₂ (s ∘ Sum.inr) • φ₁ := by
    funext x₁; rw [h1, map_smul]; simp [mul_comm]
  rw [h2, map_smul]
  simp [boxFun, mul_comm]

section Tame

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

def IsTame {κ κ' : Type} [Fintype κ] [Fintype κ'] (T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)) : Prop :=
  ∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ (ι : Type) (_ : Fintype ι)
    (P : ι → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (κ' → mixedEmbedding.mixedSpace F) ℂ)
    (g' : ι → (κ' → FiniteAdeleRing (𝓞 F) F) → ℂ), (∀ j, g' j ∈ SB (κ' → FiniteAdeleRing (𝓞 F) F)) ∧
      ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, T (pureA F f g) = ∑ j, pureA F (P j f) (g' j)

variable {F}

theorem IsTame.comp {κ κ' κ'' : Type} [Fintype κ] [Fintype κ'] [Fintype κ'']
    {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)} {T' : ((κ' → AF F) → ℂ) →ₗ[ℂ] ((κ'' → AF F) → ℂ)}
    (hT : IsTame F T) (hT' : IsTame F T') : IsTame F (T' ∘ₗ T) := by
  intro g hg
  obtain ⟨ι, _, P, g', hg', hP⟩ := hT g hg
  choose ι' inst P' g'' hg'' hP' using fun j => hT' (g' j) (hg' j)
  letI : ∀ j, Fintype (ι' j) := inst
  refine ⟨Σ j, ι' j, inferInstance, fun p => (P' p.1 p.2).comp (P p.1), fun p => g'' p.1 p.2,
    fun p => hg'' p.1 p.2, fun f => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.comp_apply, hP, map_sum, Fintype.sum_sigma]
  exact Finset.sum_congr rfl fun j _ => hP' j (P j f)

theorem IsTame.mapsTo {κ κ' : Type} [Fintype κ] [Fintype κ'] {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    (hT : IsTame F T) : ∀ φ ∈ schA F κ, T φ ∈ schA F κ' := by
  intro φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    obtain ⟨ι, _, P, g', hg', hP⟩ := hT g hg
    rw [hP]
    exact Submodule.sum_mem _ fun j _ => Submodule.subset_span ⟨P j f, g' j, hg' j, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem IsTame.comp_adm {κ κ' : Type} [Fintype κ] [Fintype κ'] {T : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ' → AF F) → ℂ)}
    (hT : IsTame F T) {l : ((κ' → AF F) → ℂ) →ₗ[ℂ] ℂ} (hl : l ∈ (adeleClass F).adm κ') :
    l ∘ₗ T ∈ (adeleClass F).adm κ := by
  intro g hg
  obtain ⟨ι, _, P, g', hg', hP⟩ := hT g hg
  choose L hL using fun j => hl (g' j) (hg' j)
  refine ⟨∑ j, (L j).comp (P j), fun f => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.comp_apply, hP, map_sum, ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => hL j (P j f)

end Tame

end GlobalTheory.DoublingEv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCompletelyAuxiliaryPlaceOutsideFinset
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCompletelyAuxiliaryPlaceOutsideFinset
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.GoodPlace

theorem ncard_primesOver_eq_two {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (h2 : Module.finrank F E = 2) {p : ℕ} (hp : p.Prime)
    (h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 E)).ncard = Module.finrank ℚ E)
    (v : HeightOneSpectrum (𝓞 F)) (hpv : (p : 𝓞 F) ∈ v.asIdeal) :
    (v.asIdeal.primesOver (𝓞 E)).ncard = 2 := by
  classical
  haveI := v.isMaximal
  have hs := Ideal.sum_ramification_inertia (𝓞 E) F E (p := v.asIdeal) v.ne_bot
  rw [h2] at hs
  rw [← hs, ← IsDedekindDomain.coe_primesOverFinset v.ne_bot, Set.ncard_coe_finset, Finset.card_eq_sum_ones]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [IsDedekindDomain.mem_primesOverFinset_iff v.ne_bot] at hq
  haveI := hq.1
  haveI := hq.2
  have hpq : (p : 𝓞 E) ∈ q := by
    simpa using (Ideal.mem_of_liesOver q v.asIdeal (p : 𝓞 F)).1 hpv
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal ≤ q := Ideal.map_le_iff_le_comap.2 (Ideal.LiesOver.over (P := q) (p := v.asIdeal)).le
  have he : v.asIdeal.ramificationIdx' q = 1 := by
    by_contra hne1
    have h3 := (Ideal.ramificationIdx'_ne_one_iff hle).1 hne1
    have h4 := h3 (Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) hpv)
    rw [map_natCast] at h4
    exact (GlobalTheory.LocSplit.split_prime hp h q hpq).1 h4
  have hcF := (GlobalTheory.ColClassCompare.unram_card_of_split (F := F) (E := E) hp h v.asIdeal hpv).2
  have hcE := (GlobalTheory.ColClassCompare.unram_card_of_split (F := E) (E := E) hp h q hpq).2
  have hf : v.asIdeal.inertiaDeg' q = 1 := by
    have hcomap : Ideal.comap (algebraMap (𝓞 F) (𝓞 E)) q = v.asIdeal := (Ideal.LiesOver.over (P := q) (p := v.asIdeal)).symm
    rw [Ideal.inertiaDeg', dite_eq_left hcomap]
    letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
    have hfin : Module.Finite (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ q) := inferInstance
    have := Module.natCard_eq_pow_finrank (K := 𝓞 F ⧸ v.asIdeal) (V := 𝓞 E ⧸ q)
    rw [hcF, hcE] at this
    exact (Nat.pow_right_injective hp.two_le (by simpa using this.symm))
  rw [he, hf]

end GlobalTheory.GoodPlace

namespace GlobalTheory.GoodPlace

theorem exists_good_place : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (P₀ : Finset (HeightOneSpectrum (𝓞 D.host.F))), ∃ v₁ : HeightOneSpectrum (𝓞 D.host.F), v₁ ∉ P₀ ∧
      SplitsFully D.host.E v₁ ∧ (∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v₁) ∧
      Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v₁) := by
  intro D T L sc G μ₀ _ t P₀
  classical
  set S : Finset (HeightOneSpectrum (𝓞 D.host.F)) :=
    P₀ ∪ (locPl G t).image (fun w => w.under (𝓞 D.host.F)) with hS
  have hn : D.host.QS ≠ 0 := D.host.QS_pos.ne'
  have hq : D.host.q ≠ 0 := D.host.hyp.1.ne_zero
  have hd : D.host.d ≠ 0 := D.host.hyp.2.1.ne_zero
  have hm : D.host.QS * D.host.q * D.host.d ≠ 0 := by positivity
  obtain ⟨p, hp, hlt, hc⟩ := Nat.exists_prime_gt_modEq_one (∑ u ∈ S, Ideal.absNorm u.asIdeal) hm
  obtain ⟨h1, -, -⟩ := GlobalTheory.HostSplit.split_completely_of_modEq_one D.R D.host p hp hc
  have h : (Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 D.host.E)).ncard = Module.finrank ℚ D.host.E := by
    rw [← GlobalTheory.HostSplit.ncard_placesOver _ hp]
    exact h1
  obtain ⟨v, hv⟩ := GlobalTheory.SplitChoice.exists_place_over D.host.F hp
  have hnot : ∀ u ∈ S, u ≠ v := by
    intro u hu e
    refine GlobalTheory.SplitChoice.natCast_notMem_of_absNorm_lt u hp ?_ (e ▸ hv)
    have := Finset.single_le_sum (f := fun u : HeightOneSpectrum (𝓞 D.host.F) => Ideal.absNorm u.asIdeal)
      (fun _ _ => Nat.zero_le _) hu
    omega
  refine ⟨v, fun hv0 => hnot v (Finset.mem_union_left _ hv0) rfl, ?_,
    fun w hw e => hnot _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hw)) e, ?_⟩
  · have hmax : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.1 hp).irreducible
    have hle : Ideal.span {(p : ℤ)} ≤ v.asIdeal.under ℤ := by
      rw [Ideal.span_singleton_le_iff_mem, Ideal.under_def, Ideal.mem_comap]
      simpa using hv
    have hunder : v.asIdeal.under ℤ = Ideal.span {(p : ℤ)} :=
      (hmax.eq_of_le (Ideal.IsPrime.under ℤ v.asIdeal).ne_top hle).symm
    unfold SplitsFully
    rw [hunder]
    exact h
  · rw [GlobalTheory.AdelicU.nonempty_split_iff (GlobalTheory.AdelicU.isCMExt_host D)]
    exact ncard_primesOver_eq_two (GlobalTheory.AdelicU.isCMExt_host D).2.2.1 hp h v hv

end GlobalTheory.GoodPlace
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCompletelyAuxiliaryPlaceOutsideFinsetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitCompletely_auxiliary_place_outside_finset : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (_hL : L.Is μ₀) (t : T)
    (P₀ : Finset (HeightOneSpectrum (𝓞 D.host.F))), ∃ v₁ : HeightOneSpectrum (𝓞 D.host.F), v₁ ∉ P₀ ∧
      SplitsFully D.host.E v₁ ∧ (∀ w ∈ locPl G t, w.under (𝓞 D.host.F) ≠ v₁) ∧
      Nonempty (D.host.E →ₐ[D.host.F] Fv D.host.F v₁) := by
  first | exact @GlobalTheory.GoodPlace.exists_good_place | exact GlobalTheory.GoodPlace.exists_good_place | (intros; apply GlobalTheory.GoodPlace.exists_good_place <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAdmissibleLocalComponentDefiniteUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAdmissibleLocalComponentDefiniteUnit
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.LocCompU

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isIrreducible_comp_of_surjective {H H' X : Type} [Group H] [Group H'] [AddCommGroup X] [Module ℂ X]
    (ρ : Representation ℂ H X) (φ : H' →* H) (hφ : Function.Surjective φ) (h : ρ.IsIrreducible) :
    Representation.IsIrreducible (ρ.comp φ) := by
  obtain ⟨h0, h1⟩ := (GlobalTheory.CuspRep.isIrreducible_iff _).1 h
  refine (GlobalTheory.CuspRep.isIrreducible_iff _).2 ⟨h0, fun W hW => h1 W fun g v hv => ?_⟩
  obtain ⟨g', rfl⟩ := hφ g
  exact hW g' v hv

theorem isClosed_UL (hU : Unr E) (n : ℕ) (w : Pl E) : IsClosed (UL n w : Set (GLw n w)) := by
  unfold UL
  split_ifs
  · exact isClosed_univ
  · have hc := (GlobalTheory.ConjAtPlace.main E hU w).1
    have : Continuous fun g : GLw n w =>
        cT (cj w) (g : Matrix (Fin n) (Fin n) _) * 1 * (g : Matrix (Fin n) (Fin n) _) := by
      refine Continuous.mul (Continuous.mul ?_ continuous_const) Units.continuous_val
      exact continuous_matrix fun i j => hc.comp (Units.continuous_val.matrix_elem _ _)
    exact isClosed_singleton.preimage this

theorem isOpen_isCompact_KL (hU : Unr E) (n : ℕ) (w : Pl E) :
    IsOpen (KL n w : Set (UL n w)) ∧ IsCompact (KL n w : Set (UL n w)) := by
  have hK := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
  rw [KL, Subgroup.coe_subgroupOf]
  exact ⟨hK.1.preimage continuous_subtype_val,
    (isClosed_UL hU n w).isClosedEmbedding_subtypeVal.isCompact_preimage hK.2⟩

theorem exists_equiv (hU : Unr E) (n : ℕ) (w : Pl E) :
    ∃ e : locU n w ≃ₜ* UL n w, ∀ x : locU n w, ((e x : UL n w) : GLw n w) = cLoc w (x : UA E n) := by
  by_cases hs : IsSplitAt w
  · obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w hs
    have h : UL n w = ⊤ := if_pos hs
    have hm : ∀ g : GLw n w, g ∈ UL n w := fun g => by rw [h]; exact Subgroup.mem_top _
    refine ⟨{ toFun := fun x => ⟨e x, hm _⟩
              invFun := fun g => e.symm g.1
              left_inv := fun x => by simp
              right_inv := fun g => Subtype.ext (by simp)
              map_mul' := fun x y => Subtype.ext (by simp)
              continuous_toFun := e.continuous.subtype_mk _
              continuous_invFun := e.symm.continuous.comp continuous_subtype_val }, fun x => he x⟩
  · obtain ⟨-, -, hv, hns, -⟩ := GlobalTheory.ConjAtPlace.main E hU w
    obtain ⟨e, he⟩ := GlobalTheory.DefU.Inert.locU_equiv E n w (cj w) (hns hs).1 hv
    have h : UL n w = UJ (cj w) 1 := if_neg hs
    rw [h]
    exact ⟨e, he⟩

theorem exists_unique_locComp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ w : Pl E,
    (∃ σ : SmIrr (UL n w), IsCompU π w σ ∧
      ∀ U : Subgroup (UL n w), IsOpen (U : Set (UL n w)) → FiniteDimensional ℂ (fixed σ.ρ U)) ∧
    ∀ σ σ' : SmIrr (UL n w), IsCompU π w σ → IsCompU π w σ' → Nonempty (σ.ρ.Equiv σ'.ρ) := by
  intro E _ _ _ hU n _ π hπ w
  obtain ⟨e, he⟩ := exists_equiv hU n w
  obtain ⟨hKo, hKc⟩ := isOpen_isCompact_KL hU n w
  have hesurj : Function.Surjective (e.toMulEquiv.symm.toMonoidHom) := e.symm.surjective
  refine ⟨?_, ?_⟩
  · obtain ⟨σ₀, hadm, hirr, f, hf0, hfm, hf⟩ := GlobalTheory.DefU.LocAdm.exists_admissible_comp E n ⟨π, hπ⟩ w
    let ρ : Representation ℂ (UL n w) σ₀.V := σ₀.ρ.comp e.toMulEquiv.symm.toMonoidHom
    have hρ : ∀ g v, ρ g v = σ₀.ρ (e.symm g) v := fun _ _ => rfl
    let σ : SmIrr (UL n w) :=
      { V := σ₀.V
        ρ := ρ
        smooth := fun v => (σ₀.smooth v).preimage e.symm.continuous
        irred := isIrreducible_comp_of_surjective σ₀.ρ _ hesurj σ₀.irred }
    refine ⟨σ, ⟨e.toMulEquiv.toMonoidHom, fun x => he x, σ.irred, f, hf0, hfm, fun x v => ?_⟩, fun U hUo => ?_⟩
    · change f (σ₀.ρ (e.symm (e x)) v) = _
      rw [e.symm_apply_apply]
      exact hf x v
    · let K' : Subgroup (locU n w) := (U ⊓ KL n w).comap e.toMulEquiv.toMonoidHom
      have hK'o : IsOpen (K' : Set (locU n w)) := by
        change IsOpen (e ⁻¹' ((U : Set (UL n w)) ∩ (KL n w : Set (UL n w))))
        exact (hUo.inter hKo).preimage e.continuous
      have hK'c : IsCompact (K' : Set (locU n w)) := by
        change IsCompact (e ⁻¹' ((U : Set (UL n w)) ∩ (KL n w : Set (UL n w))))
        exact e.toHomeomorph.isCompact_preimage.2 (hKc.inter_left (U.isClosed_of_isOpen hUo))
      haveI := hadm.2 K' hK'o hK'c
      have hle : fixed σ.ρ U ≤ fixed σ₀.ρ K' := by
        intro v hv k
        have h1 := hv ⟨e k, k.2.1⟩
        simp only [MonoidHom.one_apply, Units.val_one, one_smul] at h1 ⊢
        change σ₀.ρ (e.symm (e k)) v = v at h1
        rwa [e.symm_apply_apply] at h1
      exact Submodule.finiteDimensional_of_le hle
  · rintro σ σ' ⟨p, hp, -, f, hf0, hfm, hf⟩ ⟨p', hp', -, f', hf0', hfm', hf'⟩
    have hpe : ∀ x, p x = e x := fun x => Subtype.ext ((hp x).trans (he x).symm)
    have hpe' : ∀ x, p' x = e x := fun x => Subtype.ext ((hp' x).trans (he x).symm)
    have hps : Function.Surjective p := fun g => ⟨e.symm g, by rw [hpe, e.apply_symm_apply]⟩
    have hps' : Function.Surjective p' := fun g => ⟨e.symm g, by rw [hpe', e.apply_symm_apply]⟩
    obtain ⟨r, -, -, hr2⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
    let π' : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
    let F : Representation.IntertwiningMap (σ.ρ.comp p) (π'.rep.comp (locU n w).subtype) :=
      ⟨f.codRestrict π hfm, fun x => LinearMap.ext fun v => Subtype.ext (hf x v)⟩
    let F' : Representation.IntertwiningMap (σ'.ρ.comp p') (π'.rep.comp (locU n w).subtype) :=
      ⟨f'.codRestrict π hfm', fun x => LinearMap.ext fun v => Subtype.ext (hf' x v)⟩
    have hF0 : F ≠ 0 := fun h =>
      hf0 (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
    have hF0' : F' ≠ 0 := fun h =>
      hf0' (LinearMap.ext fun v => congrArg Subtype.val (DFunLike.congr_fun h v))
    obtain ⟨-, h2⟩ := GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (locU n w) π σ.V σ'.V π'.rep (locU n w).subtype
      (σ.ρ.comp p) (σ'.ρ.comp p') π'.isIrreducible_rep
      (isIrreducible_comp_of_surjective σ.ρ p hps σ.irred)
      (isIrreducible_comp_of_surjective σ'.ρ p' hps' σ'.irred)
      (fun g => ⟨r g, fun y => hr2 g y⟩) F hF0
    obtain ⟨T⟩ := h2 F' hF0'
    refine ⟨{ toLinearEquiv := T.toLinearEquiv, isIntertwining' := fun g => ?_ }⟩
    have h1 : p (e.symm g) = g := by rw [hpe, e.apply_symm_apply]
    have h1' : p' (e.symm g) = g := by rw [hpe', e.apply_symm_apply]
    have := T.isIntertwining' (e.symm g)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, h1, h1'] at this
    exact this

end GlobalTheory.BCT.LocCompU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAdmissibleLocalComponentDefiniteUnitStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_admissible_localComponent_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π → ∀ w : Pl E, (∃ σ : SmIrr (UL n w), IsCompU π w σ ∧ ∀ U : Subgroup (UL n w), IsOpen (U : Set (UL n w)) → FiniteDimensional ℂ (fixed σ.ρ U)) ∧ ∀ σ σ' : SmIrr (UL n w), IsCompU π w σ → IsCompU π w σ' → Nonempty (σ.ρ.Equiv σ'.ρ) := by
  first | exact @GlobalTheory.BCT.LocCompU.exists_unique_locComp | exact GlobalTheory.BCT.LocCompU.exists_unique_locComp | (intros; apply GlobalTheory.BCT.LocCompU.exists_unique_locComp <;> assumption)
end
end
