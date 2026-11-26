module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionOfNumericsModel
public import Development.AbelianVarietyTheory.Definitions.Divisors.P22

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerIntertwinerScalar
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

noncomputable section
open GroundTheory.Global

namespace GlobalTheory.SubstIntertw

variable (F : Type) [Field F] [NumberField F]

def stdChar : AddChar (AF F) ℂ where
  toFun a := (adelicChar F a : ℂ)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp [AddChar.map_add_eq_mul]

theorem stdChar_inl (z : InfiniteAdeleRing F) :
    Complex.exp (-(2 * Real.pi * Complex.I) *
      (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (infiniteAdeleInl z : AF F)) : ℝ)) =
      (adelicChar F (infiniteAdeleInl z) : ℂ) := by
  have h2 : adelicChar F (infiniteAdeleInl z) = Real.fourierChar (-infiniteTrace F z) := adelicChar_infinite z
  rw [h2, GlobalTheory.AdelicSvN.Weyl.trace_eq_mixedTrace, ← mixedTrace_homeomorphMixedSpace, homeomorphMixedSpace_apply,
    Real.fourierChar_apply]
  congr 1
  have : evI F (infiniteAdeleInl z) = InfiniteAdeleRing.ringEquiv_mixedSpace F z := rfl
  rw [this]
  push_cast
  ring

theorem isStd_stdChar : IsStd (stdChar F) := by
  refine ⟨continuous_subtype_val.comp continuous_adelicChar, fun x => ?_, fun a ha => ?_⟩
  · show (adelicChar F (algebraMap F (AF F) x) : ℂ) = 1
    rw [adelicChar_algebraMap]; rfl
  · have h0 : evI F ((0, 1) : AF F) = 0 := by
      show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : InfiniteAdeleRing F) = 0
      exact map_zero _
    have h2 : a.2 = 0 := by
      have := congrArg Prod.snd (ha ((0, 1) : AF F) h0)
      have e : (1 : FiniteAdeleRing (𝓞 F) F) * a.2 = 0 := this
      simpa using e
    obtain ⟨z, rfl⟩ : ∃ z : InfiniteAdeleRing F, a = infiniteAdeleInl z := ⟨a.1, Prod.ext rfl h2⟩
    exact (stdChar_inl F z).symm

end GlobalTheory.SubstIntertw

namespace GlobalTheory.SubstIntertw

open GroundTheory.Global


end GlobalTheory.SubstIntertw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceConjHeisenbergInvariantForm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceConjHeisenbergInvariantForm
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

noncomputable section

namespace GlobalTheory.SplitInvFormF

theorem exists_invForm_split : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ → f₀ ≠ 0 →
        ∃ ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ,
          (∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
            ℓ (heisOF σ JS JT ξ₀ B.ψ u f) = ℓ f) ∧
          ∃ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f ∧ ℓ f ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he f₀ hf₀ hf₀0
  obtain ⟨φ, hφ, hφ0, hd⟩ := GlobalTheory.T.splitPlace_thetaFunction_vacuum_conjugatePlace F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he f₀ hf₀ hf₀0
  obtain ⟨ℓ, h1, h2⟩ := GlobalTheory.HalfCoinv.exists_form (Y := conjHalf σ e nS nT) (ρ := heisL σ JS JT ξ₀ B.ψ)
    (B := commF σ JS JT ξ₀ B.ψ) (Θ := {g | IsThetaFunOF σ JS JT ξ₀ B.ψ g})
    (fun x hx x' hx' f => by
      show heisOF σ JS JT ξ₀ B.ψ x (heisOF σ JS JT ξ₀ B.ψ x' f) = heisOF σ JS JT ξ₀ B.ψ (x + x') f
      rw [heisOF_heisOF, symplOHF_half he hx hx', AddChar.map_zero_eq_one, one_smul])
    (fun f => heisOF_zero f) (fun u y f => heisOF_comm u y f)
    (fun u hu g hg => exists_nsmul_fix he hu hg) hφ0 hd
  exact ⟨ℓ, fun u hu f hf => h1 u hu f hf, φ, hφ, h2⟩

end GlobalTheory.SplitInvFormF

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceConjHeisenbergInvariantFormStatement
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

theorem _root_.GlobalTheory.T.exists_splitPlace_conjHeisenberg_invariantForm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, IsSplitIdemF σ e → ∀ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ → f₀ ≠ 0 →
        ∃ ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ,
          (∀ u : WOF F E nS nT, (∀ i j, cAF σ e * u i j = u i j) → ∀ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f →
            ℓ (heisOF σ JS JT ξ₀ B.ψ u f) = ℓ f) ∧
          ∃ f, IsThetaFunOF σ JS JT ξ₀ B.ψ f ∧ ℓ f ≠ 0 := by
  first | exact @GlobalTheory.SplitInvFormF.exists_invForm_split | exact GlobalTheory.SplitInvFormF.exists_invForm_split | (intros; apply GlobalTheory.SplitInvFormF.exists_invForm_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsolatedNonKltDivisorSmoothProjective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsolatedNonKltDivisorSmoothProjective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh

namespace GlobalTheory.KollarApp

theorem sum_Icc_cast_eq_choose (n : ℕ) :
    ∑ e ∈ Finset.Icc 1 n, (e : ℝ) = (((n + 1).choose 2 : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.choose_succ_succ (n + 1) 1]
    simp
    ring

theorem isolatedNonKlt_smooth : GlobalTheory.Published.IsolatedNonKltDivisor → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (q : X ⟶ Sp ℂ) (D : ℕ) [SmoothOfRelativeDimension D q], IsProjOver q → 1 ≤ D → letI := algebraΓOfHom q; ∀ (N₀ : LB X) (r : ℕ) (x : X), 0 < r → IsNef ℂ N₀ → IsBig ℂ N₀ → IsClosed ({x} : Set X) → (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e → topologicalKrullDim (Z : Set X) = e → (((D + 1).choose 2 : ℕ) : ℝ) ^ e < (interNumRed ℂ Z (fun _ : Fin e => N₀) : ℝ) / (r : ℝ) ^ e) → ∃ (m' : ℕ) (D₀ : CartierDiv X) (U : X.Opens), 0 < m' ∧ D₀.Eff ∧ (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' = interNumRed ℂ C ![N₀] / r) ∧ x ∈ U ∧ (∀ y ∈ U, y ≠ x → KltAt q D (qWeil D₀ m') y) ∧ ¬ KltAt q D (qWeil D₀ m') x := by
  intro hK X _ _ q D _ hproj hD
  letI := algebraΓOfHom q
  intro N₀ r x hr hnef hbig hx hint
  haveI := SmoothOfRelativeDimension.smooth D q
  haveI : GlobalTheory.IsNormalScheme X := isNormalScheme_of_smooth q
  have hdim : topologicalKrullDim X = D := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth q D inferInstance
  have hc : (0 : ℝ) < (((D + 1).choose 2 : ℕ) : ℝ) := by
    have : 0 < (D + 1).choose 2 := Nat.choose_pos (by omega)
    exact_mod_cast this
  have hsum : ∑ e ∈ Finset.Icc 1 D, (e : ℝ) / (((D + 1).choose 2 : ℕ) : ℝ) ≤ 1 := by
    rw [← Finset.sum_div, sum_Icc_cast_eq_choose, div_self hc.ne']
  obtain ⟨m, D₀, U, hm, hD₀, hnum, hxU, -, hklt, hnot⟩ :=
    hK X q D hproj hdim hD 0 r N₀ x (fun _ => (((D + 1).choose 2 : ℕ) : ℝ))
      ⟨by simp, fun z hz => absurd rfl hz, fun _ => le_rfl⟩
      (fun y => GlobalTheory.Discrepancy.kltAt_zero_of_smooth hdim y) hr hnef hbig hx (fun _ _ => hc)
      hint hsum
  refine ⟨m, D₀, U, hm, hD₀, hnum, hxU, fun y hy hyx => ?_, ?_⟩
  · simpa using hklt y hy hyx
  · simpa using hnot

end GlobalTheory.KollarApp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsolatedNonKltDivisorSmoothProjectiveStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isolated_nonKlt_divisor_smooth_projective : GlobalTheory.Published.IsolatedNonKltDivisor → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (q : X ⟶ Sp ℂ) (D : ℕ) [SmoothOfRelativeDimension D q], IsProjOver q → 1 ≤ D → letI := algebraΓOfHom q; ∀ (N₀ : LB X) (r : ℕ) (x : X), 0 < r → IsNef ℂ N₀ → IsBig ℂ N₀ → IsClosed ({x} : Set X) → (∀ (Z : Closeds X) (e : ℕ), IsIrreducible (Z : Set X) → x ∈ Z → 1 ≤ e → topologicalKrullDim (Z : Set X) = e → (((D + 1).choose 2 : ℕ) : ℝ) ^ e < (interNumRed ℂ Z (fun _ : Fin e => N₀) : ℝ) / (r : ℝ) ^ e) → ∃ (m' : ℕ) (D₀ : CartierDiv X) (U : X.Opens), 0 < m' ∧ D₀.Eff ∧ (∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB D₀] : ℚ) / m' = interNumRed ℂ C ![N₀] / r) ∧ x ∈ U ∧ (∀ y ∈ U, y ≠ x → KltAt q D (qWeil D₀ m') y) ∧ ¬ KltAt q D (qWeil D₀ m') x := by
  first | exact @GlobalTheory.KollarApp.isolatedNonKlt_smooth | exact GlobalTheory.KollarApp.isolatedNonKlt_smooth | (intros; apply GlobalTheory.KollarApp.isolatedNonKlt_smooth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExOfHeadWt
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NefStep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}


open Classical in
def stepEx (σ : E →+* ℂ) (j : ℕ) : Ix Dw → ℤ :=
  fun ix => ix.elim 0 fun p => if p.1 = σ ∧ (p.2 : ℕ) < j then 1 else 0


open Classical in
theorem exOf_tailWt (τ : Psi H) (k : ℕ) (hk : Dw.p ≤ k) :
    AllWt.exOf Dw (GlobalTheory.NefWt.tailWt τ k) 0 = stepEx (conjEmb τ.1) (Dw.p + Dw.q - 1 - k) := by
  refine FlagMod.exOf_ext rfl (fun τ' i hi => ?_) (fun τ' i hi => ?_)
  · have h1 : ¬ (τ' = τ ∧ k < (i : ℕ)) := fun h => by
      have := i.2; have := FlagMod.mult_of_mem (Dw := Dw) τ'; omega
    have h2 : ¬ (τ'.1 = conjEmb τ.1 ∧ (i : ℕ) < Dw.p + Dw.q - 1 - k) := fun h =>
      GlobalTheory.AllWt.conj_not_mem τ (h.1 ▸ τ'.2)
    simp only [GlobalTheory.NefWt.tailWt, stepEx, Option.elim, if_neg h1, if_neg h2]
  · have hq := FlagMod.mult_conj (Dw := Dw) τ'
    have hi' := i.2
    by_cases e : τ' = τ
    · subst e
      have : k < Dw.p + (Dw.q - 1 - (i : ℕ)) ↔ (i : ℕ) < Dw.p + Dw.q - 1 - k := by omega
      by_cases h : (i : ℕ) < Dw.p + Dw.q - 1 - k
      · simp [GlobalTheory.NefWt.tailWt, stepEx, h, this.2 h]
      · simp [GlobalTheory.NefWt.tailWt, stepEx, h, mt this.1 h]
    · have hc : conjEmb τ'.1 ≠ conjEmb τ.1 := fun h => e (Subtype.ext (by
        rw [← GlobalTheory.AllWt.conjEmb_conjEmb τ'.1, h, GlobalTheory.AllWt.conjEmb_conjEmb]))
      simp [GlobalTheory.NefWt.tailWt, stepEx, e, hc]


open Classical in
theorem exOf_headWt (τ : Psi H) (k : ℕ) (hk : k < Dw.p) :
    AllWt.exOf Dw (GlobalTheory.NefWt.headWt τ k) 0 = stepEx τ.1 (k + 1) := by
  refine FlagMod.exOf_ext rfl (fun τ' i hi => ?_) (fun τ' i hi => ?_)
  · by_cases e : τ' = τ
    · subst e
      by_cases h : (i : ℕ) ≤ k
      · simp [GlobalTheory.NefWt.headWt, stepEx, h, Nat.lt_succ_of_le h]
      · simp [GlobalTheory.NefWt.headWt, stepEx, h, show ¬ (i : ℕ) < k + 1 by omega]
    · have hc : τ'.1 ≠ τ.1 := fun h => e (Subtype.ext h)
      simp [GlobalTheory.NefWt.headWt, stepEx, e, hc]
  · have hq := FlagMod.mult_conj (Dw := Dw) τ'
    have h1 : ¬ (τ' = τ ∧ Dw.p + (Dw.q - 1 - (i : ℕ)) ≤ k) := fun h => by omega
    have h2 : ¬ (conjEmb τ'.1 = τ.1 ∧ (i : ℕ) < k + 1) := fun h =>
      GlobalTheory.AllWt.conj_not_mem τ' (h.1 ▸ τ.2)
    simp only [GlobalTheory.NefWt.headWt, stepEx, Option.elim, if_neg h1, if_neg h2, neg_zero]

variable {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} (X : FlagMod.FlagCover Y)
  (Z : Comp Xo c)

theorem L₀_tailWt (τ : Psi H) (k : ℕ) (hk : Dw.p ≤ k) :
    L₀ X Z (GlobalTheory.NefWt.tailWt τ k) = LL₀ X Z (stepEx (conjEmb τ.1) (Dw.p + Dw.q - 1 - k)) :=
  congrArg (LL₀ X Z) (exOf_tailWt τ k hk)

theorem L₀_headWt (τ : Psi H) (k : ℕ) (hk : k < Dw.p) :
    L₀ X Z (GlobalTheory.NefWt.headWt τ k) = LL₀ X Z (stepEx τ.1 (k + 1)) :=
  congrArg (LL₀ X Z) (exOf_headWt τ k hk)

end GlobalTheory.NefStep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweHighestWeightSupStableLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweHighestWeightSupStableLe
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem isKC_Eab_of_posC {p q : ℕ} {c d : Ix p q} (h : posC c d) : IsKC (Eab c d) := by
  intro a b hab
  have hcd : sameBlock c d := by
    cases c <;> cases d <;> simp_all [posC, sameBlock]
  simp only [Eab, Matrix.single_apply]
  split_ifs with h1
  · obtain ⟨rfl, rfl⟩ := h1
    exact absurd hcd hab
  · rfl

theorem sameBlock_refl {p q : ℕ} (a : Ix p q) : sameBlock a a := by
  cases a <;> trivial

theorem isKC_Eab_diag {p q : ℕ} (c : Ix p q) : IsKC (Eab c c) := by
  intro a b hab
  simp only [Eab, Matrix.single_apply]
  split_ifs with h1
  · rcases h1 with ⟨rfl, rfl⟩
    exact absurd (sameBlock_refl _) hab
  · rfl

theorem mem_hwSub_iff {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (v : V) :
    v ∈ hwSub act μ ↔ (∀ c, act (Eab c c) v = ((μ c : ℚ) : ℂ) • v) ∧ ∀ c d, posC c d → act (Eab c d) v = 0 := by
  simp [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem hw_sup_le (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (hG : Good act) (N N' : Submodule ℂ V) (hN : KStable act N) (hN' : KStable act N') (μ : Ix p q → ℚ) :
    (N ⊔ N') ⊓ hwSub act μ ≤ (N ⊓ hwSub act μ) ⊔ (N' ⊓ hwSub act μ) := by
  intro v hv
  obtain ⟨hvs, hvh⟩ := Submodule.mem_inf.1 hv
  obtain ⟨n, hn, n', hn', rfl⟩ := Submodule.mem_sup.1 hvs
  rw [mem_hwSub_iff] at hvh
  obtain ⟨hw, hpos⟩ := hvh
  have hI : KStable act (N ⊓ N') := fun X hX w hw' =>
    Submodule.mem_inf.2 ⟨hN X hX w (Submodule.mem_inf.1 hw').1, hN' X hX w (Submodule.mem_inf.1 hw').2⟩
  have h1 : ∀ c, act (Eab c c) n - ((μ c : ℚ) : ℂ) • n ∈ N ⊓ N' := by
    intro c
    refine Submodule.mem_inf.2 ⟨N.sub_mem (hN _ (isKC_Eab_diag c) n hn) (N.smul_mem _ hn), ?_⟩
    have e : act (Eab c c) n - ((μ c : ℚ) : ℂ) • n = -(act (Eab c c) n' - ((μ c : ℚ) : ℂ) • n') := by
      have := hw c
      rw [map_add (f := _), smul_add] at this
      rw [neg_sub, sub_eq_sub_iff_add_eq_add, this, add_comm]
    rw [e]
    exact N'.neg_mem (N'.sub_mem (hN' _ (isKC_Eab_diag c) n' hn') (N'.smul_mem _ hn'))
  have h2 : ∀ c d, posC c d → act (Eab c d) n ∈ N ⊓ N' := by
    intro c d hcd
    refine Submodule.mem_inf.2 ⟨hN _ (isKC_Eab_of_posC hcd) n hn, ?_⟩
    have e : act (Eab c d) n = -(act (Eab c d) n') := by
      have := hpos c d hcd
      rw [map_add (f := _)] at this
      exact eq_neg_of_add_eq_zero_left this
    rw [e]
    exact N'.neg_mem (hN' _ (isKC_Eab_of_posC hcd) n' hn')
  obtain ⟨n1, hn1N, hn1h, hd⟩ := GlobalTheory.T.exists_highestWeight_lift_mod_stable_subspace p q V act hG (N ⊓ N') N hI hN μ n hn h1 h2
  have hdN' : n + n' - n1 ∈ N' := by
    have : n + n' - n1 = (n - n1) + n' := by abel
    rw [this]
    exact N'.add_mem (Submodule.mem_inf.1 hd).2 hn'
  have hvH : n + n' ∈ hwSub act μ := (mem_hwSub_iff act μ _).2 ⟨hw, hpos⟩
  have : n + n' = n1 + (n + n' - n1) := by abel
  rw [this]
  exact Submodule.add_mem_sup (Submodule.mem_inf.2 ⟨hn1N, hn1h⟩)
    (Submodule.mem_inf.2 ⟨hdN', (hwSub act μ).sub_mem hvH hn1h⟩)

end GlobalTheory.HoweR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweHighestWeightSupStableLeStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeHighestWeight_sup_stable_le : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), Good act → ∀ N N' : Submodule ℂ V, KStable act N → KStable act N' → ∀ μ : Ix p q → ℚ, (N ⊔ N') ⊓ hwSub act μ ≤ (N ⊓ hwSub act μ) ⊔ (N' ⊓ hwSub act μ) := by
  first | exact @GlobalTheory.HoweR.hw_sup_le | exact GlobalTheory.HoweR.hw_sup_le | (intros; apply GlobalTheory.HoweR.hw_sup_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowDualEigenvectorMemSpanField
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowDualEigenvectorMemSpanField
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSExist

theorem ksRow_exists_lieComb : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {O : Type} [CommRing O] (a : OAct O A) (cO : O → O) (ψ : LinearMap.BilinForm K (HdR A)), (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) → (∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A) → LinearMap.IsPerfPair ψ → IsAdjointFor a cO ψ → KSRegular h → (∀ (z : O) (f : HdR A) (w : epsR K ⟶ A), IsKSValue h f w → IsKSValue h (act (dp0 K) (𝟙 _) a z f) (w ≫ a.act z)) → ∀ {ι : Type} {m : ι → ℕ} (χ : ι → O →+* K) (ub : ∀ σ, Fin (m σ) → (epsR K ⟶ A)) (hb : (Σ σ, Fin (m σ)) → HdR A), Submodule.span K (Set.range hb) ⊔ Fil A = ⊤ → LinearIndependent K (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) → (∀ k (z : O), act (dp0 K) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A) → (∀ σ (w : epsR K ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w) → ∀ (τ τb : ι), (∀ z, χ τb (cO z) = χ τ z) → ∀ (j : Fin (m τb)), ∃ cf : Fin (m τ) → K, ∃ w, IsLieComb cf (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨τb, j⟩ w := by
  intro K _ A _ _ A' _ i h O _ a cO ψ hiso hlag hperf hadj hK hEq ι m χ ub hb hspan hind heig hbasis τ τb hconj j
  classical

  have hsp : ⊤ ≤ Submodule.span K (Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) := by
    have e : (Fil A).mkQ '' Set.range hb =
        Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A) := by
      rw [← Set.range_comp]; rfl
    rw [← e, ← Submodule.map_span]
    intro q _
    obtain ⟨x, rfl⟩ := (Fil A).mkQ_surjective q
    have hx : x ∈ Submodule.span K (Set.range hb) ⊔ Fil A := hspan ▸ Submodule.mem_top
    obtain ⟨y, hy, g, hg, rfl⟩ := Submodule.mem_sup.1 hx
    refine ⟨y, hy, ?_⟩
    have hg0 : (Fil A).mkQ g = 0 := (Submodule.Quotient.mk_eq_zero _).2 hg
    rw [map_add (f := _), hg0, add_zero]
  let B := Module.Basis.mk hind hsp
  let k₀ : (Σ σ, Fin (m σ)) := ⟨τb, j⟩
  obtain ⟨f, hl⟩ := hperf.bijective_left.2 (B.coord k₀ ∘ₗ (Fil A).mkQ)
  have hval : ∀ x, ψ f x = B.coord k₀ ((Fil A).mkQ x) := fun x => by rw [hl]; rfl
  have hf : f ∈ Fil A := hlag f fun g hg => by
    have hg0 : (Fil A).mkQ g = 0 := (Submodule.Quotient.mk_eq_zero _).2 hg
    rw [hval, hg0, map_zero]
  have hδ : ∀ k, ψ f (hb k) = if k = k₀ then 1 else 0 := fun k => by
    have e : (Fil A).mkQ (hb k) = B k := by simp [B]
    rw [hval, e, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

  have hact : ∀ z, act (dp0 K) (𝟙 _) a z f = χ τ z • f := fun z => by
    haveI := a.hom z
    have hz : act (dp0 K) (𝟙 _) a z f ∈ Fil A := by
      rw [act_apply]; exact push_mem_Fil _ hf
    have hf' : act (dp0 K) (𝟙 _) a z f - χ τ z • f ∈ Fil A :=
      sub_mem hz (Submodule.smul_mem _ _ hf)
    have hker : (Submodule.span K (Set.range hb) ⊔ Fil A) ≤
        LinearMap.ker (ψ (act (dp0 K) (𝟙 _) a z f - χ τ z • f)) := by
      refine sup_le ((Submodule.span_le).2 ?_) fun g hg => hiso _ hf' g hg
      rintro _ ⟨k, rfl⟩
      have e := hiso f hf _ (heig k (cO z))
      rw [map_sub, map_smul, sub_eq_zero] at e
      have e2 := hadj z f (hb k)
      change ψ (act (dp0 K) (𝟙 _) a z f - χ τ z • f) (hb k) = 0
      rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, e2, e, hδ]
      by_cases hk : k = k₀
      · subst hk
        simp [k₀, hconj z]
      · simp [hk]
    have h0 : ψ (act (dp0 K) (𝟙 _) a z f - χ τ z • f) = 0 := by
      refine LinearMap.ext fun x => ?_
      have : x ∈ Submodule.span K (Set.range hb) ⊔ Fil A := hspan ▸ Submodule.mem_top
      exact hker this
    exact sub_eq_zero.1 (hperf.bijective_left.1 (h0.trans (map_zero ψ).symm))

  obtain ⟨w, hw, hu⟩ := hK f hf
  have htan : IsTangent w := by
    obtain ⟨k, -, l⟩ := hw
    exact l.1
  have heq : ∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ τ z) ≫ w := fun z => by
    have e1 := hEq z f w hw
    rw [hact z] at e1
    exact (hK _ (Submodule.smul_mem _ _ hf)).unique e1 (hw.smul _)
  obtain ⟨cf, hcf⟩ := hbasis τ w htan heq
  exact ⟨cf, w, hcf, f, hf, fun k => by convert hδ k, hw⟩

end GlobalTheory.KSExist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowDualEigenvectorMemSpanFieldStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencerRow_dual_eigenvector_mem_span_field : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {O : Type} [CommRing O] (a : OAct O A) (cO : O → O) (ψ : LinearMap.BilinForm K (HdR A)), (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) → (∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A) → LinearMap.IsPerfPair ψ → IsAdjointFor a cO ψ → KSRegular h → (∀ (z : O) (f : HdR A) (w : epsR K ⟶ A), IsKSValue h f w → IsKSValue h (act (dp0 K) (𝟙 _) a z f) (w ≫ a.act z)) → ∀ {ι : Type} {m : ι → ℕ} (χ : ι → O →+* K) (ub : ∀ σ, Fin (m σ) → (epsR K ⟶ A)) (hb : (Σ σ, Fin (m σ)) → HdR A), Submodule.span K (Set.range hb) ⊔ Fil A = ⊤ → LinearIndependent K (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) → (∀ k (z : O), act (dp0 K) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A) → (∀ σ (w : epsR K ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w) → ∀ (τ τb : ι), (∀ z, χ τb (cO z) = χ τ z) → ∀ (j : Fin (m τb)), ∃ cf : Fin (m τ) → K, ∃ w, IsLieComb cf (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨τb, j⟩ w := by
  first | exact @GlobalTheory.KSExist.ksRow_exists_lieComb | exact GlobalTheory.KSExist.ksRow_exists_lieComb | (intros; apply GlobalTheory.KSExist.ksRow_exists_lieComb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingPoint
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
open GlobalTheory.Twist GlobalTheory.SerreCriterion

set_option autoImplicit false
noncomputable section
namespace GlobalTheory
namespace IsolatedSec
variable {X : Scheme.{0}}

theorem exists_germ_eq_of_isolated {F : X.Modules} {y : X} (hy : IsClosed ({y} : Set X))
    {U : X.Opens} (hyU : y ∈ U) (hF : ∀ z ∈ U, z ∈ support F → z = y)
    (t : (F.presheaf.stalk y :)) : ∃ s : Γ(F, ⊤), F.presheaf.germ ⊤ y trivial s = t := by
  obtain ⟨V, hyV, s, rfl⟩ := F.presheaf.exists_germ_eq t
  let W : X.Opens := ⟨{y}ᶜ, hy.isOpen_compl⟩
  let C : Bool → X.Opens := fun b => if b then V ⊓ U else W
  have hzero : ∀ (O : X.Opens), O ≤ V ⊓ U ⊓ W → ∀ r : Γ(F, O), r = 0 := fun O hO r => by
    refine TopCat.Presheaf.section_ext (abSheaf F) O r 0 fun z hz => ?_
    have hz' := hO hz
    have hns : z ∉ support F := fun h => hz'.2 (hF z hz'.1.2 h)
    exact (notMem_support_iff.1 hns).elim _ _
  obtain ⟨g, hg⟩ := exists_sec_of_cover (F := F) C (fun _ => le_top)
    (fun z _ => by
      by_cases h : z = y
      · subst h; exact Opens.mem_iSup.2 ⟨true, ⟨hyV, hyU⟩⟩
      · exact Opens.mem_iSup.2 ⟨false, h⟩)
    (fun b => match b with
      | true => resM F (inf_le_left : V ⊓ U ≤ V) s
      | false => 0)
    (fun k l => by
      cases k <;> cases l
      · rfl
      · exact (hzero _ (le_inf inf_le_right inf_le_left) _).trans (hzero _ (le_inf inf_le_right inf_le_left) _).symm
      · exact (hzero _ (le_inf inf_le_left inf_le_right) _).trans (hzero _ (le_inf inf_le_left inf_le_right) _).symm
      · rfl)
  refine ⟨g, ?_⟩
  have hyVU : y ∈ V ⊓ U := ⟨hyV, hyU⟩
  have := congrArg (F.presheaf.germ (V ⊓ U) y hyVU) (hg true)
  dsimp only at this
  rw [germ_resM, germ_resM] at this
  exact this
end IsolatedSec

theorem exists_sec_mem_nonzeroLocus_of_isolated : ∀ (k : Type) [Field k] (X : Scheme.{0})
    [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → ∀ (L : LB X), L.IsLB →
    ∀ (J : X.IdealSheafData) (x : X) (U : X.Opens), IsClosed ({x} : Set X) → x ∈ U →
    (∀ y ∈ U, y ∈ J.support ↔ y = x) → Subsingleton (coh (twist (idealModule J) L) 1) →
    ∃ s : L.Sec, x ∈ nonzeroLocus s := by
  intro k _ X _ q _ L hL J x U hx hxU hJ h
  set φ := toSubscheme J with hφ
  let S : ShortComplex X.Modules :=
    ShortComplex.mk (kernel.ι φ) (cokernel.π (kernel.ι φ)) (cokernel.condition _)
  have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel _ }
  have hS' : (S.map (twistFunctor L)).ShortExact := Twist.shortExact_map hL hS
  have h' : Subsingleton (coh (twist (kernel φ) L) 1) := by
    exact h
  have hsurj := cohOn.app_surjective hS' ⊤ h'
  have hQ : ∀ z ∈ U, z ∈ support (twist S.X₃ L) → z = x := by
    intro z hzU hz
    rw [support_twist hL] at hz
    have := mem_support_iff.1 hz
    refine (hJ z hzU).1 (support_pushforward_subscheme_subset J ?_)
    exact mem_support_iff.2 (stalkLinear_injective (Abelian.factorThruCoimage φ) z).nontrivial
  have hxJ : x ∈ J.support := (hJ x hxU).2 rfl
  obtain ⟨c, hc⟩ := exists_chart hL x
  let t : Γ(QCoh.structureModule X, ⊤) := (structureModuleSectionsEquiv ⊤).symm 1
  have ht : structureModuleSectionsEquiv ⊤ t = 1 := LinearEquiv.apply_symm_apply _ _
  obtain ⟨b, hb⟩ := IsolatedSec.exists_germ_eq_of_isolated hx hxU hQ
    ((stalkEquiv S.X₃ hL c hc).symm (stalkLinear S.g x
      ((QCoh.structureModule X).presheaf.germ ⊤ x trivial t)))
  obtain ⟨a, rfl⟩ := hsurj b
  refine ⟨secOfTwist (𝟙 _) a, basicOpen_le_nonzeroLocus _ c ((X.mem_basicOpen _ x hc).2 ?_)⟩
  have hm : x ∈ ⊤ ⊓ L.U c := ⟨trivial, hc⟩
  replace hb := (stalkEquiv_germ hL c hc (V := ⊤) trivial _).symm.trans
    ((LinearEquiv.eq_symm_apply _).1 hb)
  have h₁ : stalkLinear S.g x ((QCoh.structureModule X).presheaf.germ _ x hm
      (coord (F := QCoh.structureModule X) a c)) =
      stalkLinear S.g x ((QCoh.structureModule X).presheaf.germ ⊤ x trivial t) :=
    (stalkLinear_germ S.g x hm _).trans hb
  have h₂ : stalkLinear φ x ((QCoh.structureModule X).presheaf.germ ⊤ x trivial t -
      (QCoh.structureModule X).presheaf.germ _ x hm (coord (F := structureModule X) a c)) = 0 := by
    rw [← Abelian.coimage.fac φ, stalkLinear_comp, LinearMap.comp_apply, map_sub]
    exact (congrArg _ (sub_eq_zero.2 h₁.symm)).trans (map_zero _)
  have h₃ := not_isUnit_of_toSubscheme_eq_zero J (y := x) hxJ _ h₂
  rw [map_sub, structureModuleStalkEquiv_germ] at h₃
  erw [structureModuleStalkEquiv_germ] at h₃
  rw [ht, map_one] at h₃
  have hu := (IsLocalRing.isUnit_or_isUnit_one_sub_self _).resolve_right h₃
  exact (congrArg IsUnit (X.presheaf.germ_res_apply (homOfLE _) x hc _)).mpr hu
end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionNonvanishingPointStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Cartier GlobalTheory.Discrepancy GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_nonvanishing_point : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ Sp k), IsProjOver q → ∀ (L : LB X), L.IsLB → ∀ (J : X.IdealSheafData) (x : X) (U : X.Opens), IsClosed ({x} : Set X) → x ∈ U → (∀ y ∈ U, y ∈ J.support ↔ y = x) → Subsingleton (coh (twist (idealModule J) L) 1) → ∃ s : L.Sec, x ∈ nonzeroLocus s := by
  first | exact @GlobalTheory.exists_sec_mem_nonzeroLocus_of_isolated | exact GlobalTheory.exists_sec_mem_nonzeroLocus_of_isolated | (intros; apply GlobalTheory.exists_sec_mem_nonzeroLocus_of_isolated <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormMulLeSqrtBergmanMulComponent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormMulLeSqrtBergmanMulComponent
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

open MeasureTheory

namespace GlobalTheory.HSApp.NormProd

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ)
  {D : D7} (V : TH.HSp D) (dict : Formalism.L2.Theta.GA D V → (k : U.Comp) × FD.Frame (U.X k).Ψ r) (μ : Measure (AutQ V))

theorem ptN_rdU_le {la : ∀ k, FD.Wt (U.X k).Ψ r} {f : Rul Xo c} (hf : rdU U f ∈ holSub U.X la)
    (z : (k : U.Comp) × FD.Frame (U.X k).Ψ r) : AllWt.ptN la (rdU U f) z ≤ (supE U.X la (rdU U f)).toReal := by
  by_cases h : z.2 ∈ (U.X z.1).dom
  · have h1 : ENNReal.ofReal (AllWt.ptN la (rdU U f) z) ≤ supE U.X la (rdU U f) :=
      le_iSup (fun p : FPt U.X => ENNReal.ofReal ((U.X p.1).pnorm (la p.1) (rdU U f p.1) p.2)) ⟨z.1, ⟨z.2, h⟩⟩
    exact (ENNReal.ofReal_le_iff_le_toReal (supE_ne_top U.X la hf)).1 h1
  · have h0 : AllWt.ptN la (rdU U f) z = 0 := by
      simp [AllWt.ptN, FD.Data.pnorm, rdU, h]
    rw [h0]; exact ENNReal.toReal_nonneg

theorem petE_rdU_ne_top (hμ : μ Set.univ ≤ 1) {la : ∀ k, FD.Wt (U.X k).Ψ r} {f : Rul Xo c}
    (hf : rdU U f ∈ holSub U.X la) : AllWt.petE V dict μ la (rdU U f) ≠ ⊤ := by
  have hb : ∀ᵐ q ∂μ, ‖AllWt.ptN la (rdU U f) (dict (Quotient.out q))‖ ≤ (supE U.X la (rdU U f)).toReal :=
    Filter.Eventually.of_forall fun q => by
      rw [Real.norm_of_nonneg (AllWt.ptN_nonneg _ _ _)]; exact ptN_rdU_le U hf _
  have hle : AllWt.petE V dict μ la (rdU U f) ≤
      eLpNorm' (fun _ : AutQ V => (supE U.X la (rdU U f)).toReal) 2 μ := by
    apply eLpNorm'_mono_ae (by norm_num)
    filter_upwards [hb] with q hq
    simpa [Real.norm_of_nonneg ENNReal.toReal_nonneg] using hq
  rw [eLpNorm'_const _ (by norm_num), Real.enorm_eq_ofReal ENNReal.toReal_nonneg] at hle
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by positivity) (ne_top_of_le_ne_top ENNReal.one_ne_top hμ))) hle

theorem eLpNorm_homN_ne_top (hμ : μ Set.univ ≤ 1) {G : WTZ E} {f : Rul Xo c}
    (hf : rdU U f ∈ holSub U.X (AllWt.modelWt U G)) :
    eLpNorm' (fun q : AutQ V => AllWt.homN U x G f (dict (Quotient.out q))) 2 μ ≠ ⊤ := by
  have : (fun q : AutQ V => AllWt.homN U x G f (dict (Quotient.out q))) =
      AllWt.lieFacZ Dw x G • fun q : AutQ V => AllWt.ptN (AllWt.modelWt U G) (rdU U f) (dict (Quotient.out q)) := rfl
  rw [this, eLpNorm'_const_smul _ (by norm_num)]
  exact ENNReal.mul_ne_top enorm_ne_top (petE_rdU_ne_top U V dict μ hμ hf)

theorem homN_le_of_berg (hμ : μ Set.univ ≤ 1) (y : FPt U.X) {B : ℝ} (hB0 : 0 ≤ B) {G : WTZ E}
    (hB : AllWt.bergE V dict μ (AllWt.modelWt U G) y ≤ ENNReal.ofReal B) {f : Rul Xo c}
    (hf : rdU U f ∈ holSub U.X (AllWt.modelWt U G)) :
    AllWt.homN U x G f ⟨y.1, y.2.1⟩ ≤ Real.sqrt B * AllWt.petAt U x V dict μ G f := by
  have hfin := petE_rdU_ne_top U V dict μ hμ hf
  have h1 : ENNReal.ofReal (AllWt.ptN (AllWt.modelWt U G) (rdU U f) ⟨y.1, y.2.1⟩) ^ 2 /
      AllWt.petE V dict μ (AllWt.modelWt U G) (rdU U f) ^ 2 ≤ ENNReal.ofReal B :=
    (le_iSup₂ (f := fun P (_ : P ∈ holSub U.X (AllWt.modelWt U G)) =>
      ENNReal.ofReal (AllWt.ptN (AllWt.modelWt U G) P ⟨y.1, y.2.1⟩) ^ 2 /
        AllWt.petE V dict μ (AllWt.modelWt U G) P ^ 2) (rdU U f) hf).trans hB
  rw [ENNReal.div_le_iff_le_mul (Or.inr ENNReal.ofReal_ne_top) (Or.inl (ENNReal.pow_ne_top hfin))] at h1
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top hfin)) h1
  rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal (AllWt.ptN_nonneg _ _ _), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hB0, ENNReal.toReal_pow] at h2
  have h3 := mul_le_mul_of_nonneg_left h2 (sq_nonneg (AllWt.lieFacZ Dw x G))
  have h4 : AllWt.homN U x G f ⟨y.1, y.2.1⟩ ^ 2 ≤ B * AllWt.petAt U x V dict μ G f ^ 2 := by
    unfold AllWt.homN AllWt.petAt
    nlinarith [h3]
  have h5 := Real.sqrt_le_sqrt h4
  rwa [Real.sqrt_sq (AllWt.homN_nonneg _ _ _ _ _), Real.sqrt_mul hB0, Real.sqrt_sq (AllWt.petAt_nonneg _ _ _ _ _ _ _)] at h5

end GlobalTheory.HSApp.NormProd

namespace GlobalTheory.HSApp


open MeasureTheory in
theorem petOn_mul_le : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (a b : AllWt.Weight (T.Q.Dw j)) (w : Cusp Z Y.U a) (f : Cusp Z Y.U b) (β : ℝ), 0 ≤ β → BergLe Z Y.U (fun _ => D.sp.W j) Y.dict a β → ∀ σ, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ (a + b) 0) σ (w.1 * f.1) ≤ Real.sqrt β * petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ a 0) σ w.1 * petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ b 0) σ f.1 := by
  intro D T j Y e o _ _ Z a b w f β hβ hB σ
  set σ' := goodOf Y.d.c₂ σ with hσ'
  have hg : GoodEmb Y.d.c₂ σ' := Formalism.L2.PjFree.goodEmb_goodOf Y.d.c₂ σ
  set μ := AllWt.muOn (Y.U σ') (D.sp.W j) (Y.dict σ') Z with hμdef
  have hμ : μ Set.univ ≤ 1 := AllWt.muPart_univ_le _ _ _
  have hwH := (AllWt.mem_cuspW.1 w.2.1).2 σ' hg
  have hfH := (AllWt.mem_cuspW.1 f.2.1).2 σ' hg
  have hab : AllWt.wtOf (T.Q.Dw j) (a + b) 0 = AllWt.wtOf (T.Q.Dw j) a 0 + AllWt.wtOf (T.Q.Dw j) b 0 :=
    AllWt.wtOf_add a b 0 0
  set Pa := AllWt.petAt (Y.U σ') (xiR D) (D.sp.W j) (Y.dict σ') μ (AllWt.wtOf (T.Q.Dw j) a 0) w.1 with hPa
  have hPa0 : 0 ≤ Pa := AllWt.petAt_nonneg _ _ _ _ _ _ _
  have hpt : ∀ z : (k : (Y.U σ').Comp) × FD.Frame ((Y.U σ').X k).Ψ D.R.r,
      AllWt.homN (Y.U σ') (xiR D) (AllWt.wtOf (T.Q.Dw j) (a + b) 0) (w.1 * f.1) z ≤
        (Real.sqrt β * Pa) * AllWt.homN (Y.U σ') (xiR D) (AllWt.wtOf (T.Q.Dw j) b 0) f.1 z := by
    intro z
    by_cases hz : z ∈ AllWt.framesOn (Y.U σ') Z
    · obtain ⟨h, -⟩ := id hz
      rw [hab, AllWt.homN_mul _ _ (AllWt.even_wtOf _ _) (AllWt.even_wtOf _ _) _ _ z h]
      refine mul_le_mul_of_nonneg_right ?_ (AllWt.homN_nonneg _ _ _ _ _)
      have hy := hB σ' hg ⟨z.1, ⟨z.2, h⟩⟩ hz
      exact NormProd.homN_le_of_berg (Y.U σ') (xiR D) (D.sp.W j) (Y.dict σ') μ hμ ⟨z.1, ⟨z.2, h⟩⟩ hβ hy hwH
    · have h0 : rdU (Y.U σ') w.1 z.1 z.2 = 0 := AllWt.rdU_eq_zero (Y.U σ') w.2.2 hz
      have h1 : AllWt.homN (Y.U σ') (xiR D) (AllWt.wtOf (T.Q.Dw j) (a + b) 0) (w.1 * f.1) z = 0 := by
        simp only [AllWt.homN, AllWt.ptN, FD.Data.pnorm, AllWt.rdU_mul, Pi.mul_apply, h0, zero_mul, norm_zero, mul_zero]
      rw [h1]
      exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hPa0) (AllWt.homN_nonneg _ _ _ _ _)
  have key : eLpNorm' (fun q : AutQ (D.sp.W j) => AllWt.homN (Y.U σ') (xiR D) (AllWt.wtOf (T.Q.Dw j) (a + b) 0)
      (w.1 * f.1) (Y.dict σ' (Quotient.out q))) 2 μ ≤
      ENNReal.ofReal (Real.sqrt β * Pa) * eLpNorm' (fun q : AutQ (D.sp.W j) => AllWt.homN (Y.U σ') (xiR D)
        (AllWt.wtOf (T.Q.Dw j) b 0) f.1 (Y.dict σ' (Quotient.out q))) 2 μ := by
    rw [← Real.enorm_eq_ofReal (mul_nonneg (Real.sqrt_nonneg _) hPa0), ← eLpNorm'_const_smul _ (by norm_num)]
    apply eLpNorm'_mono_ae (by norm_num)
    filter_upwards [] with q
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Real.norm_of_nonneg (AllWt.homN_nonneg _ _ _ _ _),
      Real.norm_of_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hPa0)
        (AllWt.homN_nonneg _ _ _ _ _))]
    exact hpt _
  have hfin : eLpNorm' (fun q : AutQ (D.sp.W j) => AllWt.homN (Y.U σ') (xiR D)
      (AllWt.wtOf (T.Q.Dw j) b 0) f.1 (Y.dict σ' (Quotient.out q))) 2 μ ≠ ⊤ := by
    have heq : (fun q : AutQ (D.sp.W j) => AllWt.homN (Y.U σ') (xiR D)
        (AllWt.wtOf (T.Q.Dw j) b 0) f.1 (Y.dict σ' (Quotient.out q))) =
        AllWt.lieFacZ (T.Q.Dw j) (xiR D) (AllWt.wtOf (T.Q.Dw j) b 0) •
          fun q : AutQ (D.sp.W j) => AllWt.ptN (AllWt.modelWt (Y.U σ') (AllWt.wtOf (T.Q.Dw j) b 0))
            (rdU (Y.U σ') f.1) (Y.dict σ' (Quotient.out q)) := rfl
    rw [heq, eLpNorm'_const_smul _ (by norm_num)]
    exact ENNReal.mul_ne_top enorm_ne_top (NormProd.petE_rdU_ne_top (Y.U σ') (D.sp.W j) (Y.dict σ') μ hμ hfH)
  have k2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) key
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) hPa0)] at k2
  show AllWt.petAt (Y.U σ') (xiR D) (D.sp.W j) (Y.dict σ') μ _ (w.1 * f.1) ≤
    Real.sqrt β * Pa * AllWt.petAt (Y.U σ') (xiR D) (D.sp.W j) (Y.dict σ') μ _ f.1
  rw [AllWt.petAt_eq, AllWt.petAt_eq (Y.U σ') (xiR D) (D.sp.W j) (Y.dict σ') μ (AllWt.wtOf (T.Q.Dw j) b 0)]
  exact k2

end GlobalTheory.HSApp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormMulLeSqrtBergmanMulComponentStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.petersson_norm_mul_le_sqrt_bergman_mul_component : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (a b : AllWt.Weight (T.Q.Dw j)) (w : Cusp Z Y.U a) (f : Cusp Z Y.U b) (β : ℝ), 0 ≤ β → BergLe Z Y.U (fun _ => D.sp.W j) Y.dict a β → ∀ σ, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ (a + b) 0) σ (w.1 * f.1) ≤ Real.sqrt β * petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ a 0) σ w.1 * petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf _ b 0) σ f.1 := by
  first | exact @GlobalTheory.HSApp.petOn_mul_le | exact GlobalTheory.HSApp.petOn_mul_le | (intros; apply GlobalTheory.HSApp.petOn_mul_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowDualEigenvectorMemSpanRing
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowDualEigenvectorMemSpanRing
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSRing

theorem ksRow_exists_lieComb_ring : ∀ {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed R) i) {O : Type} [CommRing O] (a : OAct O A) (cO : O → O) (ψ : LinearMap.BilinForm R (HdR A)), (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) → (∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A) → LinearMap.IsPerfPair ψ → IsAdjointFor a cO ψ → KSRegular h → (∀ (z : O) (f : HdR A) (w : epsR R ⟶ A), IsKSValue h f w → IsKSValue h (act (dp0 R) (𝟙 _) a z f) (w ≫ a.act z)) → ∀ {ι : Type} {m : ι → ℕ} (χ : ι → O →+* R) (ub : ∀ σ, Fin (m σ) → (epsR R ⟶ A)) (hb : (Σ σ, Fin (m σ)) → HdR A), Submodule.span R (Set.range hb) ⊔ Fil A = ⊤ → LinearIndependent R (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) → (∀ k (z : O), act (dp0 R) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A) → (∀ σ (w : epsR R ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w) → ∀ (τ τb : ι), (∀ z, χ τb (cO z) = χ τ z) → ∀ (j : Fin (m τb)), ∃ cf : Fin (m τ) → R, ∃ w, IsLieComb cf (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨τb, j⟩ w := by
  intro R _ A _ _ A' _ i h O _ a cO ψ hiso hlag hperf hadj hK hEq ι m χ ub hb hspan hind heig hbasis τ τb hconj j
  classical

  have hsp : ⊤ ≤ Submodule.span R (Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) := by
    have e : (Fil A).mkQ '' Set.range hb =
        Set.range fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A) := by
      rw [← Set.range_comp]; rfl
    rw [← e, ← Submodule.map_span]
    intro q _
    obtain ⟨x, rfl⟩ := (Fil A).mkQ_surjective q
    have hx : x ∈ Submodule.span R (Set.range hb) ⊔ Fil A := hspan ▸ Submodule.mem_top
    obtain ⟨y, hy, g, hg, rfl⟩ := Submodule.mem_sup.1 hx
    refine ⟨y, hy, ?_⟩
    have hg0 : (Fil A).mkQ g = 0 := (Submodule.Quotient.mk_eq_zero _).2 hg
    rw [map_add (f := _), hg0, add_zero]
  let B := Module.Basis.mk hind hsp
  let k₀ : (Σ σ, Fin (m σ)) := ⟨τb, j⟩
  obtain ⟨f, hl⟩ := hperf.bijective_left.2 (B.coord k₀ ∘ₗ (Fil A).mkQ)
  have hval : ∀ x, ψ f x = B.coord k₀ ((Fil A).mkQ x) := fun x => by rw [hl]; rfl
  have hf : f ∈ Fil A := hlag f fun g hg => by
    have hg0 : (Fil A).mkQ g = 0 := (Submodule.Quotient.mk_eq_zero _).2 hg
    rw [hval, hg0, map_zero]
  have hδ : ∀ k, ψ f (hb k) = if k = k₀ then 1 else 0 := fun k => by
    have e : (Fil A).mkQ (hb k) = B k := by simp [B]
    rw [hval, e, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]

  have hact : ∀ z, act (dp0 R) (𝟙 _) a z f = χ τ z • f := fun z => by
    haveI := a.hom z
    have hz : act (dp0 R) (𝟙 _) a z f ∈ Fil A := by
      rw [act_apply]; exact push_mem_Fil _ hf
    have hf' : act (dp0 R) (𝟙 _) a z f - χ τ z • f ∈ Fil A :=
      sub_mem hz (Submodule.smul_mem _ _ hf)
    have hker : (Submodule.span R (Set.range hb) ⊔ Fil A) ≤
        LinearMap.ker (ψ (act (dp0 R) (𝟙 _) a z f - χ τ z • f)) := by
      refine sup_le ((Submodule.span_le).2 ?_) fun g hg => hiso _ hf' g hg
      rintro _ ⟨k, rfl⟩
      have e := hiso f hf _ (heig k (cO z))
      rw [map_sub, map_smul, sub_eq_zero] at e
      have e2 := hadj z f (hb k)
      change ψ (act (dp0 R) (𝟙 _) a z f - χ τ z • f) (hb k) = 0
      rw [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, e2, e, hδ]
      by_cases hk : k = k₀
      · subst hk
        simp [k₀, hconj z]
      · simp [hk]
    have h0 : ψ (act (dp0 R) (𝟙 _) a z f - χ τ z • f) = 0 := by
      refine LinearMap.ext fun x => ?_
      have : x ∈ Submodule.span R (Set.range hb) ⊔ Fil A := hspan ▸ Submodule.mem_top
      exact hker this
    exact sub_eq_zero.1 (hperf.bijective_left.1 (h0.trans (map_zero ψ).symm))

  obtain ⟨w, hw, hu⟩ := hK f hf
  have htan : IsTangent w := by
    obtain ⟨k, -, l⟩ := hw
    exact l.1
  have heq : ∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ τ z) ≫ w := fun z => by
    have e1 := hEq z f w hw
    rw [hact z] at e1
    exact (hK _ (Submodule.smul_mem _ _ hf)).unique e1 (hw.smul _)
  obtain ⟨cf, hcf⟩ := hbasis τ w htan heq
  exact ⟨cf, w, hcf, f, hf, fun k => by convert hδ k, hw⟩

end GlobalTheory.KSRing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowDualEigenvectorMemSpanRingStatement
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencerRow_dual_eigenvector_mem_span_ring : ∀ {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed R) i) {O : Type} [CommRing O] (a : OAct O A) (cO : O → O) (ψ : LinearMap.BilinForm R (HdR A)), (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) → (∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A) → LinearMap.IsPerfPair ψ → IsAdjointFor a cO ψ → KSRegular h → (∀ (z : O) (f : HdR A) (w : epsR R ⟶ A), IsKSValue h f w → IsKSValue h (act (dp0 R) (𝟙 _) a z f) (w ≫ a.act z)) → ∀ {ι : Type} {m : ι → ℕ} (χ : ι → O →+* R) (ub : ∀ σ, Fin (m σ) → (epsR R ⟶ A)) (hb : (Σ σ, Fin (m σ)) → HdR A), Submodule.span R (Set.range hb) ⊔ Fil A = ⊤ → LinearIndependent R (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) → (∀ k (z : O), act (dp0 R) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A) → (∀ σ (w : epsR R ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w) → ∀ (τ τb : ι), (∀ z, χ τb (cO z) = χ τ z) → ∀ (j : Fin (m τb)), ∃ cf : Fin (m τ) → R, ∃ w, IsLieComb cf (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨τb, j⟩ w := by
  first | exact @GlobalTheory.KSRing.ksRow_exists_lieComb_ring | exact GlobalTheory.KSRing.ksRow_exists_lieComb_ring | (intros; apply GlobalTheory.KSRing.ksRow_exists_lieComb_ring <;> assumption)
end
end
