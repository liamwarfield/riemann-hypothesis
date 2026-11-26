module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
public import Development.AbelianVarietyTheory.Counterexamples.TwistSurvey.ConjModelCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthonormalFrameReadingEqConjugateDatumTheta
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeries
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaFunctionFundamentalDomainInnerProductBasic
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyAlgebraisationAbelianQuotientTower
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedCoordinatesPPowerDenominator
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularElementsBoundedPadic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStableComplBot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyAdicIntegralSpanClosedMulStar
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLabelAtUnfolding
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolRead.SecWt

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (conjEmb Coeff Level)

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {l : Level H}

theorem relab_inj (c : Coeff l) (σ : c.F →+* ℂ) : Function.Injective (relab (E := E) c σ) := fun τ τ' h => by
  ext a
  have h1 : σ (embF c τ a) = σ (embF c τ' a) := congrArg (fun f : E →+* ℂ => f a) h
  exact congrArg Subtype.val (σ.injective h1)

theorem relab_conjEmb (c : Coeff l) (σ : c.F →+* ℂ) (τ : E →+* ℂ) :
    relab c σ (conjEmb τ) = conjEmb (relab c σ τ) := by
  ext a
  have h1 : embF c (conjEmb τ) a = embF c τ (IsCMField.complexConj E a) :=
    Subtype.ext (IsCMField.complexEmbedding_complexConj E τ a).symm
  show σ (embF c (conjEmb τ) a) = starRingEnd ℂ (relab c σ τ a)
  rw [h1]
  exact IsCMField.complexEmbedding_complexConj E (relab c σ τ) a

theorem conj_cmHostRoot_ne_self : (starRingEnd ℂ) H.rt0 ≠ H.rt0 := by
  intro e
  have him : H.rt0.im = 0 := Complex.conj_eq_iff_im.1 e
  have hre := congrArg Complex.re H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  simp only [sq, Complex.mul_re, Complex.neg_re, Complex.natCast_re, him] at hre
  nlinarith [mul_self_nonneg H.rt0.re]

end

theorem tauE_inj (D : D7) : Function.Injective (tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem conjEmb_inj {E : Type} [Field E] : Function.Injective (conjEmb (E := E)) := fun a b h => by
  ext x
  exact star_injective (RingHom.congr_fun h x)

theorem wtA_pos {D : D7} (hne : ∀ s t, tauE D s ≠ conjEmb (tauE D t)) {j : ℕ} (w : WeightFamilies.Wt D j) (s : D.what₂.Tau) (n : ℕ) :
    wtA w (tauE D s, n) = ext0 (w.aP s) n := by
  unfold wtA
  simp only [show DV.tauEmb D = tauE D from rfl]
  rw [Finset.sum_eq_single s]
  · rw [if_pos rfl, if_neg (hne s s)]; rfl
  · intro t _ ht
    rw [if_neg (fun h => ht (tauE_inj D h).symm), if_neg (hne s t), add_zero]
  · simp

theorem wtA_neg {D : D7} (hne : ∀ s t, tauE D s ≠ conjEmb (tauE D t)) {j : ℕ} (w : WeightFamilies.Wt D j) (s : D.what₂.Tau) (n : ℕ) :
    wtA w (conjEmb (tauE D s), n) = ext0 (w.aM s) n := by
  unfold wtA
  simp only [show DV.tauEmb D = tauE D from rfl]
  rw [Finset.sum_eq_single s]
  · rw [if_neg (fun h => hne s s (Eq.symm h)), if_pos rfl, zero_add]
  · intro t _ ht
    rw [if_neg (fun h => hne t s (Eq.symm h)), if_neg (fun h => ht (tauE_inj D (conjEmb_inj h)).symm), add_zero]
  · simp

theorem aPl_cast (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (p n : ℕ) (hp : p = D.R.k + i) (hn : n < p) :
    (aPl D i p τ n : ℚ) =
      Formalism.L2.NTheta.lamAt (D.hc τ) n + (D.hc τ).e i - ((p : ℚ) - (n + 1)) - ((D.R.t : ℚ) + 1) / 2 := by
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  have h3 := Formalism.L2.NTheta.lamAt_add_add_le (D.hc τ) (p - 1 - n) n (by simp only [Ranks.r]; omega)
  have hl : Formalism.L2.NTheta.lamAt (D.hc τ) (n + (p - 1 - n)) = -(D.hc τ).b i := by
    unfold Formalism.L2.NTheta.lamAt
    rw [dite_eq_right (by omega), dite_eq_left (by omega)]
    congr 2
    exact Fin.ext (by simp only; omega)
  have hc : ((p - 1 - n : ℕ) : ℚ) = (p : ℚ) - (n + 1) := by
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]; push_cast; ring
  rw [hl, hc] at h3
  have g := (D.hc τ).gap_be i
  obtain ⟨z1, h1⟩ := Formalism.L2.NTheta.lamAt_int (D.hc τ) n
  obtain ⟨z2, h2⟩ := (D.hc τ).e_int i
  obtain ⟨s, hs⟩ := D.R.t_odd
  have ht : (D.R.t : ℚ) = 2 * s + 1 := by exact_mod_cast hs
  have hz : Formalism.L2.NTheta.lamAt (D.hc τ) n + (D.hc τ).e i - ((p : ℚ) - (n + 1)) - ((D.R.t : ℚ) + 1) / 2 =
      ((z1 + z2 - (p - (n + 1)) - (s + 1) : ℤ) : ℚ) := by
    rw [h1, h2, ht]; push_cast; ring
  have h0 : (0 : ℤ) ≤ z1 + z2 - (p - (n + 1)) - (s + 1) := by
    have : (0 : ℚ) ≤ ((z1 + z2 - (p - (n + 1)) - (s + 1) : ℤ) : ℚ) := by rw [← hz]; linarith
    exact_mod_cast this
  unfold aPl
  rw [if_pos hn, hz, Int.floor_intCast]
  exact_mod_cast Int.toNat_of_nonneg h0

theorem aMi_cast (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (p q c : ℕ) (hp : p = D.R.k + i) (hq : q = D.R.m - (i + 1))
    (hc : c < q) :
    (aMi D i p q τ (q - 1 - c) : ℚ) =
      -((D.hc τ).e i + Formalism.L2.NTheta.lamAt (D.hc τ) (p + c) + ((c : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2) := by
  have hk := D.R.m_add_three_le_k
  have hi := i.2
  have h3 := Formalism.L2.NTheta.lamAt_add_add_le (D.hc τ) c p (by simp only [Ranks.r]; omega)
  have hm : (i : ℕ) + 1 < D.R.m := by omega
  have hl : Formalism.L2.NTheta.lamAt (D.hc τ) p = -(D.hc τ).b ⟨i + 1, hm⟩ := by
    unfold Formalism.L2.NTheta.lamAt
    rw [dite_eq_right (by omega), dite_eq_left (by omega)]
    congr 2
    exact Fin.ext (by simp only; omega)
  rw [hl] at h3
  have g := (D.hc τ).gap_eb i hm
  obtain ⟨z1, h1⟩ := Formalism.L2.NTheta.lamAt_int (D.hc τ) (p + c)
  obtain ⟨z2, h2⟩ := (D.hc τ).e_int i
  obtain ⟨s, hs⟩ := D.R.t_odd
  have ht : (D.R.t : ℚ) = 2 * s + 1 := by exact_mod_cast hs
  have hz : -((D.hc τ).e i + Formalism.L2.NTheta.lamAt (D.hc τ) (p + c) + ((c : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2) =
      ((-(z2 + z1 + (c + 1) + s) : ℤ) : ℚ) := by
    rw [h1, h2, ht]; push_cast; ring
  have h0 : (0 : ℤ) ≤ -(z2 + z1 + (c + 1) + s) := by
    have : (0 : ℚ) ≤ ((-(z2 + z1 + (c + 1) + s) : ℤ) : ℚ) := by rw [← hz]; linarith
    exact_mod_cast this
  unfold aMi
  rw [if_pos (by omega), show q - (q - 1 - c) = c + 1 by omega, show p + (c + 1) - 1 = p + c by omega, Nat.cast_succ, hz,
    Int.floor_intCast]
  exact_mod_cast Int.toNat_of_nonneg h0

theorem laU_eq_wtCol : ∀ (D : D7) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), LawsJ T → AlgTie T → KapIs κ → ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), GoodEmb T.Q.c (res T σ) → ∀ (e : D.what₂.Tau → ℤ), (∀ ρ, (e ρ : ℚ) = (D.hc (lab σ ρ)).e i) → ∀ k (ρ : D.what₂.Tau) (τ : ((T.U ((i : ℕ) + 1) (res T σ)).X k).Ψ), τ.1 = tauE D ρ → ∀ c : Fin D.R.r, laU (T.U ((i : ℕ) + 1) (res T σ)) (wtA (κ i)) (κ i).n k τ c = wtCol (D.hc (lab σ ρ)) (D.R.sigW ((i : ℕ) + 1)).1 (D.R.sigW ((i : ℕ) + 1)).2 c + e ρ := by
  intro D T _ κ hl ha hκ i σ hσ e he k ρ τ hτ c
  have hlab := (GlobalTheory.ConjReading.branch_of_pins T ha hl.pins σ ρ).1 hσ
  have he' := he ρ
  generalize lab σ ρ = s at hlab he' ⊢
  have hrt : ∀ t, tauE D t (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := hl.pins.1.2.2.2
  have hne : ∀ s t, tauE D s ≠ conjEmb (tauE D t) := fun s t h => by
    have h1 := RingHom.congr_fun h (T.Q.H.rt : D.host.E)
    change _ = starRingEnd ℂ (tauE D t _) at h1
    rw [hrt, hrt] at h1
    exact conj_cmHostRoot_ne_self h1.symm
  have hrel : relab T.Q.c (res T σ) (tauE D s) = τ.1 := by
    rw [hτ, ← hlab]
    ext x
    show σ (algebraMap T.Q.c.F D.what₂.LL (embF T.Q.c (tauE D s) x)) = σ (labLL D s x)
    congr 1
    apply D.what₂.embLL.injective
    have h1 := RingHom.congr_fun (res_embLL T ha hl.pins.2.2.1) (embF T.Q.c (tauE D s) x)
    have h2 := RingHom.congr_fun D.embE_φ₀ ((D.host.sigmaOf (D.eTau s).1 : D.host.E →+* D.host.E) x)
    exact h1.trans h2.symm
  have hi1 : Function.invFun (relab T.Q.c (res T σ)) τ.1 = tauE D s := by
    rw [← hrel]; exact Function.leftInverse_invFun (relab_inj _ _) _
  have hi2 : Function.invFun (relab T.Q.c (res T σ)) (conjEmb τ.1) = conjEmb (tauE D s) := by
    rw [← hrel, ← relab_conjEmb]; exact Function.leftInverse_invFun (relab_inj _ _) _
  have hp0 : ((T.U ((i : ℕ) + 1) (res T σ)).X k).p0 = (D.R.sigW ((i : ℕ) + 1)).2 :=
    ((hl.unf _ (inR i) _ hσ).2.1 k).1.trans (hl.pins.2.2.2 _ (inR i)).2.1
  have hs : (Wc D i).sig (tauE D s) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (inR i).1 (inR i).2 _
  obtain ⟨hP, hM, hn⟩ := hκ i s
  rw [hs] at hP hM
  have hi := i.2
  have hc := c.2
  have hk := D.R.m_add_three_le_k
  have hp : (D.R.sigW ((i : ℕ) + 1)).1 = D.R.k + i := by simp only [Ranks.sigW]; omega
  have hq : (D.R.sigW ((i : ℕ) + 1)).2 = D.R.m - (i + 1) := rfl
  have hr : D.R.r = (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 := by
    rw [hp, hq]; simp only [Ranks.r]; omega
  obtain ⟨N, hN⟩ := (κ i).n_even
  have hN2 : (κ i).n / 2 = N := by omega
  have hNq : (N : ℚ) + N = ((D.R.sigW ((i : ℕ) + 1)).1 : ℚ) + (D.R.sigW ((i : ℕ) + 1)).2 + D.R.t := by
    have : N + N = (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 + D.R.t := by
      rw [← hN, hn, ← hr]; rfl
    exact_mod_cast this
  unfold laU wtCol
  rw [hi1, hi2, hp0, hN2, wtA_pos hne, wtA_neg hne, ← sub_eq_iff_eq_add, eq_comm, Int.floor_eq_iff]
  by_cases h : (c : ℕ) < (D.R.sigW ((i : ℕ) + 1)).2
  · have h1 : (D.R.sigW ((i : ℕ) + 1)).2 - 1 - c < (D.R.sigW ((i : ℕ) + 1)).2 := by omega
    have h2 := aMi_cast D i s _ _ c hp hq h
    rw [if_pos h, if_neg (not_le.2 h), ext0, dite_eq_left h1, hM]
    push_cast
    rw [h2, he']
    constructor <;> linarith
  · have h1 : (c : ℕ) - (D.R.sigW ((i : ℕ) + 1)).2 < (D.R.sigW ((i : ℕ) + 1)).1 := by omega
    have h2 := aPl_cast D i s _ _ hp h1
    rw [if_neg h, if_pos (not_lt.1 h), ext0, dite_eq_left h1, hP]
    simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_one]
    rw [h2, he']
    constructor <;> linarith

end GlobalTheory.HolRead.SecWt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerThetaFunctionsReadingTestFunctionFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerThetaFunctionsReadingTestFunctionFrames
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.Overlap

section Kernel

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} (X : Data E r)

theorem kZero_zero (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ) (x₁ x₂ : Frame X.Ψ r) :
    kZero X idx x₁ x₂ (0 : Fin n → Fin g → ℂ) 0 =
      ∏ τ : X.Ψ, (((aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det) ^ (n / 2))⁻¹ := by
  unfold kZero
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h : ∀ k, dblz X idx x₁ x₂ (0 : Fin n → Fin g → ℂ) 0 τ k = 0 := fun k => by
    have e : (fun a : Fin r => if (a : ℕ) < X.p0 then (0 : Fin n → Fin g → ℂ) k (idx.symm (τ, a))
        else (0 : Fin n → Fin g → ℂ) k (idx.symm (τ, a))) = 0 := by
      funext a
      simp
    funext c
    simp only [dblz, Matrix.of_apply, e, mulVec_zero, smul_zero]
  simp only [h, mulVec_zero, dotProduct_zero, Finset.sum_const_zero, mul_zero, Complex.exp_zero, mul_one]

theorem aLin_move {x₁ x₂ y₁ y₂ : Frame X.Ψ r} (τ : X.Ψ) {u : Matrix (Fin r) (Fin r) ℂ} (hu : IsUnit u.det)
    (hh : ∀ v w, hermC τ.1 X.Gm (u *ᵥ v) (u *ᵥ w) = hermC τ.1 X.Gm v w)
    (h₁ : mat y₁ τ = u * mat x₁ τ) (h₂ : mat y₂ τ = u * mat x₂ τ) :
    aLin X y₁ y₂ τ * u = aLin X x₁ x₂ τ := by
  refine Matrix.ext_of_mulVec_single fun c => ?_
  generalize (Pi.single c 1 : Fin r → ℂ) = w
  funext a
  rw [← mulVec_mulVec]
  by_cases ha : (a : ℕ) < X.p0
  · rw [DblPoint.aLin_mulVec_of_lt X _ _ _ _ ha, DblPoint.aLin_mulVec_of_lt X _ _ _ _ ha, h₂, ← hh w]
    rfl
  · rw [DblPoint.aLin_mulVec_of_not_lt X _ _ _ _ ha, DblPoint.aLin_mulVec_of_not_lt X _ _ _ _ ha, h₁,
      Matrix.mul_inv_rev, mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]

theorem det_move {x₁ x₂ y₁ y₂ : Frame X.Ψ r} (τ : X.Ψ) {u : Matrix (Fin r) (Fin r) ℂ}
    (hu : u.det * conj u.det = 1)
    (hh : ∀ v w, hermC τ.1 X.Gm (u *ᵥ v) (u *ᵥ w) = hermC τ.1 X.Gm v w)
    (h₁ : mat y₁ τ = u * mat x₁ τ) (h₂ : mat y₂ τ = u * mat x₂ τ) :
    (aLin X y₁ y₂ τ).det * (aAnti X y₁ y₂ τ).det = (aLin X x₁ x₂ τ).det * (aAnti X x₁ x₂ τ).det := by
  have hu' : IsUnit u.det := IsUnit.of_mul_eq_one _ hu
  have e : ∀ z₁ z₂ : Frame X.Ψ r, (aAnti X z₁ z₂ τ).det = conj (aLin X z₂ z₁ τ).det := fun z₁ z₂ => by
    rw [DblPoint.aLin_swap, ← RingHom.mapMatrix_apply, ← RingHom.map_det, Complex.conj_conj]
  rw [e, e, ← aLin_move X τ hu' hh h₁ h₂, ← aLin_move X τ hu' hh h₂ h₁, det_mul, det_mul, map_mul]
  linear_combination (-((aLin X y₁ y₂ τ).det * conj (aLin X y₂ y₁ τ).det)) * hu

end Kernel

variable {D : D7} {S T : HSp D} (C : GlobalTheory.Ker.Ctx S T)

theorem kZero_mvB {B B' : C.Bas} (hB : C.IsB B) (u : GA D T) :
    kZero C.X C.idx (C.xB (C.mvB u B)) (C.xB (C.mvB u B')) (0 : Fin S.rank → Fin C.g → ℂ) 0 =
      kZero C.X C.idx (C.xB B) (C.xB B') (0 : Fin S.rank → Fin C.g → ℂ) 0 := by
  rw [kZero_zero, kZero_zero]
  refine Finset.prod_congr rfl fun σ _ => ?_
  obtain ⟨τ, rfl⟩ := C.m.e.surjective σ
  have hU := GlobalTheory.Ker.ONBasis.compAt_unitary C τ u
  have hm : ∀ A : C.Bas, mat (C.xB (C.mvB u A)) (C.m.e τ) =
      (compAt C.θ τ (Formalism.L2.Theta.mt T u)).map conj * mat (C.xB A) (C.m.e τ) := fun A => by
    rw [GlobalTheory.Ker.ONBasis.mat_xB, GlobalTheory.Ker.ONBasis.mat_xB, ← Matrix.map_mul]
    rfl
  generalize compAt C.θ τ (Formalism.L2.Theta.mt T u) = U at hU hm
  have hG : (gramAt D T τ).det ≠ 0 := by
    intro h0
    have h1 := congrArg det (hB τ)
    have h2 := congrArg det (GlobalTheory.Ker.ONBasis.sgnM_sq C.X)
    rw [det_mul, det_mul, h0, mul_zero, zero_mul] at h1
    rw [det_mul, ← h1, zero_mul, det_one] at h2
    exact zero_ne_one h2
  rw [det_move C.X (C.m.e τ) (u := U.map conj) ?_ ?_ (hm B) (hm B')]
  · have h1 := congrArg det hU
    rw [det_mul, det_mul, det_conjTranspose] at h1
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, Complex.conj_conj]
    apply mul_right_cancel₀ hG
    rw [one_mul]
    refine Eq.trans ?_ h1
    rw [Complex.star_def]
    ring
  · intro v w
    have e : ∀ v : Fin T.rank → ℂ, U.map conj *ᵥ v = fun a => conj ((U *ᵥ star v) a) := fun v => by
      funext a
      simp [mulVec, dotProduct]
    have e' : ∀ v : Fin T.rank → ℂ, v = fun a => conj (star v a) := fun v => by
      funext a
      simp
    rw [e, e, GlobalTheory.Ker.ONBasis.hermC_conj]
    conv_rhs => rw [e' v, e' w, GlobalTheory.Ker.ONBasis.hermC_conj, ← hU]
    rw [star_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec (star (star v)) Uᴴ]

theorem ipO_Th {μ : Measure (WO S T)} {𝓕 : Set (WO S T)} (hμ : IsCovolOne (ratL T S) μ 𝓕)
    {x₁ x₂ : Frame C.X.Ψ T.rank} (h₁ : x₁ ∈ C.X.dom) (h₂ : x₂ ∈ C.X.dom) {φ₁ φ₂ : TF S.rank C.g}
    (s₁ : GlobalTheory.SW.IsSB φ₁) (s₂ : GlobalTheory.SW.IsSB φ₂) :
    GlobalTheory.Ker.ipO μ 𝓕 (C.Th x₁ φ₁) (C.Th x₂ φ₂) =
      dbl C.X C.bas C.idx φ₁ φ₂ 0 * kZero C.X C.idx x₁ x₂ (0 : Fin S.rank → Fin C.g → ℂ) 0 := by
  have h0 : GlobalTheory.Ker.IsRealPt (0 : WO S T) := Matrix.map_zero _ (map_zero _)
  have h := GlobalTheory.Ker.GaussKer.ipO_rho_Th D S T C μ 𝓕 hμ x₁ h₁ x₂ h₂ φ₁ φ₂ s₁ s₂ 0 0 h0 h0
  have hr : ∀ f, C.rho 0 f = f := fun f => by
    funext w
    simp [GlobalTheory.Ker.Ctx.rho, heisO, symplOH, symplO, hO]
  have hz : ∀ x, C.zOf x (0 : WO S T) = 0 := fun x => by
    funext k i
    simp [GlobalTheory.Ker.Ctx.zOf, GlobalTheory.Ker.zR, GlobalTheory.Ker.Ctx.realPt, compAt, hermC, mulVec, dotProduct]
  have hg : ∀ x, GlobalTheory.Ker.gaussR C.X C.bas C.idx x (0 : Fin S.rank → Fin C.g → ℂ) = 1 := fun x => by
    simp [GlobalTheory.Ker.gaussR, hx]
  rw [hr, hr, hz, hz, hg, hg] at h
  have e : (fun (k : Fin S.rank) (i : Fin C.g) => conj ((0 : Fin S.rank → Fin C.g → ℂ) k i)) = 0 := by
    funext k i
    simp
  rw [h, e, map_one, one_mul, one_mul]

theorem isBasOf_unique {W : HSp D} {X : Data D.host.E W.rank} (hm : IsMod W rfl X) {q0 : ℕ}
    (hq : X.p0 + q0 = W.rank) {x : Frame X.Ψ W.rank} {B B' : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ}
    (h : IsBasOf W rfl X hq x B) (h' : IsBasOf W rfl X hq x B') : B = B' := by
  funext ρ
  ext a i
  have hτ : tauE D ρ ∈ X.Ψ := (hm.psi _).2 ⟨ρ, rfl⟩
  by_cases hi : (i : ℕ) < q0
  · rw [h ρ ⟨_, hτ⟩ rfl (Sum.inl ⟨i, hi⟩) i a rfl, h' ρ ⟨_, hτ⟩ rfl (Sum.inl ⟨i, hi⟩) i a rfl]
  · have h1 : (i : ℕ) - q0 < X.p0 := by have := i.2; omega
    have h2 : (i : ℕ) = q0 + ((i : ℕ) - q0) := by omega
    rw [h ρ ⟨_, hτ⟩ rfl (Sum.inr ⟨_, h1⟩) i a h2, h' ρ ⟨_, hτ⟩ rfl (Sum.inr ⟨_, h1⟩) i a h2]

end GlobalTheory.AdTh.Overlap


open GlobalTheory.AdTh.Overlap in
theorem GlobalTheory.AdTh.inner_of_reads : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∃ G : Frame X.Ψ r → Frame X.Ψ r → ℂ, ∀ x x' : Frame X.Ψ r, IsONFr X x → IsONFr X x' → G x x' ≠ 0 ∧ (∀ u : GA D W, G (frMove θ W hr X u x) (frMove θ W hr X u x') = G x x') ∧ ∀ v : TF V.rank g, GlobalTheory.SW.IsSB v → v ≠ 0 → ∃ c : ℂ, c ≠ 0 ∧ ∀ y y' : Frame X.Ψ r, IsONFr X y → IsONFr X y' → ∀ (f f' : WO V W → ℂ) (κ κ' : ℂ), IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → Reads θ V W hr X bas idx f (κ • v) y → Reads θ V W hr X bas idx f' (κ' • v) y' → ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → ∫ w in 𝓕, f w * conj (f' w) ∂μ = κ * conj κ' * (c * G y y') := by
  intro D ψ θ V W r g hr X bas idx hstd hinf hV he hm hs
  subst hr
  obtain ⟨X', m, hq', hq, bas', idx', hs', -, -, -, -, -, -, H⟩ :=
    GlobalTheory.T.orthonormal_frame_reading_eq_conjugate_datum_theta D ψ θ V W g X bas idx hstd hinf he hV hm hs
  let C : GlobalTheory.Ker.Ctx V W := ⟨ψ, hstd, θ, hinf, X', m, g, X.p0, hq', bas', idx', hs', he⟩
  let Bx : Frame X.Ψ W.rank → C.Bas := fun x => Classical.epsilon fun B => IsBasOf W rfl X hq x B
  have hBx : ∀ x, IsONFr X x → IsBasOf W rfl X hq x (Bx x) := fun x hx => Classical.epsilon_spec (H x hx).1
  have hB : ∀ x, IsONFr X x → C.IsB (Bx x) := fun x hx => ((H x hx).2 _ (hBx x hx)).1
  have hd : ∀ x, IsONFr X x → C.xB (Bx x) ∈ C.X.dom := fun x hx =>
    GlobalTheory.Ker.ONBasis.mem_dom C.X (GlobalTheory.Ker.ONBasis.isONFr_xB C (hB x hx))
  have hmv : ∀ x, IsONFr X x → ∀ u, Bx (frMove θ W rfl X u x) = C.mvB u (Bx x) := fun x hx u => by
    obtain ⟨h1, h2⟩ := ((H x hx).2 _ (hBx x hx)).2.2.2.2.2.2.2.1 u
    exact isBasOf_unique hm hq (hBx _ h1) h2
  have hT : ∀ x, IsONFr X x → ∀ (f : WO V W → ℂ) (φ : TF V.rank g), GlobalTheory.SW.IsSB φ →
      ((IsThetaFunO ψ V W f ∧ Reads θ V W rfl X bas idx f φ x) ↔ f = C.Th (C.xB (Bx x)) φ) := fun x hx =>
    ((H x hx).2 _ (hBx x hx)).2.2.2.2.2.2.2.2
  have hne : ∀ x x', IsONFr X x → IsONFr X x' →
      kZero C.X C.idx (C.xB (Bx x)) (C.xB (Bx x')) (0 : Fin V.rank → Fin g → ℂ) 0 ≠ 0 := fun x x' hx hx' => by
    rw [kZero_zero]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => inv_ne_zero (pow_ne_zero _ (mul_ne_zero
      (DblPoint.det_aLin_ne_zero (hd x hx) (hd x' hx') τ) (DblPoint.det_aAnti_ne_zero (hd x hx) (hd x' hx') τ)))
  refine ⟨fun x x' => kZero C.X C.idx (C.xB (Bx x)) (C.xB (Bx x')) (0 : Fin V.rank → Fin g → ℂ) 0,
    fun x x' hx hx' => ⟨hne x x' hx hx', fun u => ?_, fun v hv hv0 => ⟨dbl C.X C.bas C.idx v v 0, fun hc => ?_, ?_⟩⟩⟩
  · beta_reduce
    rw [hmv x hx, hmv x' hx']
    exact kZero_mvB C (hB x hx) u
  · obtain ⟨⟨μ, 𝓕, hμ⟩, hip⟩ := GlobalTheory.Ker.ScalarProduct.ip_basic D V W C
    have h1 := ipO_Th C hμ (hd x hx) (hd x hx) hv hv
    rw [hc, zero_mul] at h1
    have h2 := (hip μ 𝓕 hμ _ ((hT x hx _ v hv).2 rfl).1).2.1 h1
    obtain ⟨l1, l2, -⟩ := GlobalTheory.Ker.Ctx.th_laws D V W C _ (hd x hx) v hv
    have h3 : GlobalTheory.SW.IsSB ((0 : ℂ) • v) := by
      obtain ⟨R, hR, -, -⟩ := hv
      exact ⟨R, hR, fun x hx => absurd (by simp) hx, fun x y hy => by simp⟩
    refine hv0 (((l1 _ h3).2 ?_).trans (zero_smul ℂ v))
    rw [l2, h2, zero_smul]
  · intro y y' hy hy' f f' κ κ' hf hf' rf rf' μ 𝓕 hμ
    have e := (hT y hy f _ rf.1).1 ⟨hf, rf⟩
    have e' := (hT y' hy' f' _ rf'.1).1 ⟨hf', rf'⟩
    rw [(GlobalTheory.Ker.Ctx.th_laws D V W C _ (hd y hy) v hv).2.1] at e
    rw [(GlobalTheory.Ker.Ctx.th_laws D V W C _ (hd y' hy') v hv).2.1] at e'
    have h1 := ipO_Th C hμ (hd y hy) (hd y' hy') hv hv
    refine Eq.trans ?_ (congrArg (κ * conj κ' * ·) h1)
    rw [e, e', GlobalTheory.Ker.ipO, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerThetaFunctionsReadingTestFunctionFramesStatement
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_thetaFunctions_reading_testFunction_frames : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∃ G : Frame X.Ψ r → Frame X.Ψ r → ℂ, ∀ x x' : Frame X.Ψ r, IsONFr X x → IsONFr X x' → G x x' ≠ 0 ∧ (∀ u : GA D W, G (frMove θ W hr X u x) (frMove θ W hr X u x') = G x x') ∧ ∀ v : TF V.rank g, GlobalTheory.SW.IsSB v → v ≠ 0 → ∃ c : ℂ, c ≠ 0 ∧ ∀ y y' : Frame X.Ψ r, IsONFr X y → IsONFr X y' → ∀ (f f' : WO V W → ℂ) (κ κ' : ℂ), IsThetaFunO ψ V W f → IsThetaFunO ψ V W f' → Reads θ V W hr X bas idx f (κ • v) y → Reads θ V W hr X bas idx f' (κ' • v) y' → ∀ (μ : Measure (WO V W)) (𝓕 : Set (WO V W)), IsCovolOne (ratL W V) μ 𝓕 → ∫ w in 𝓕, f w * conj (f' w) ∂μ = κ * conj κ' * (c * G y y') := by
  first | exact @GlobalTheory.AdTh.inner_of_reads | exact GlobalTheory.AdTh.inner_of_reads | (intros; apply GlobalTheory.AdTh.inner_of_reads <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoAlgebraisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfIsoOnAllReductions
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfIsoOnAllReductions
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LBReductions

theorem exists_kernel_approx {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R) {a b : ℕ}
    (D : Matrix (Fin b) (Fin a) R) : ∃ e : ℕ, ∀ v : Fin a → R, (∀ j, D.mulVec v j ∈ I ^ (e + 1)) →
      ∃ w : Fin a → R, D.mulVec w = 0 ∧ ∀ k, v k - w k ∈ I := by
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I (LinearMap.range D.mulVecLin)
  refine ⟨c, fun v hv => ?_⟩
  have h₁ : D.mulVec v ∈ I ^ (c + 1) • (⊤ : Submodule R (Fin b → R)) ⊓ LinearMap.range D.mulVecLin := by
    refine ⟨?_, v, rfl⟩
    rw [pi_eq_sum_univ (D.mulVec v)]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hv j) trivial
  rw [hc (c + 1) (Nat.le_succ c), Nat.add_sub_cancel_left, pow_one] at h₁
  have h₂ : D.mulVec v ∈ Submodule.map D.mulVecLin (I • ⊤) := by
    rw [Submodule.map_smul'', Submodule.map_top]
    exact Submodule.smul_mono le_rfl inf_le_right h₁
  obtain ⟨u, hu, huv⟩ := h₂
  have h₃ : ∀ k, u k ∈ I := by
    refine Submodule.smul_induction_on hu (fun r hr n _ k => I.mul_mem_right _ hr)
      fun x y hx hy k => I.add_mem (hx k) (hy k)
  refine ⟨v - u, ?_, fun k => by simpa using h₃ k⟩
  rw [Matrix.mulVec_sub, sub_eq_zero]
  exact huv.symm


open GlobalTheory.AbLaw.Seesaw in
theorem mem_basicOpen_loc₀ {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}}
    {f : X ⟶ Spec (CommRingCat.of R)} {N : LB X} (P : Perf f N) {v w : Fin P.a → R} (h : ∀ k, v k - w k ∈ I)
    {i : P.I} {x : X} (hI : I ≤ (f x).asIdeal) (hx : x ∈ X.basicOpen (loc₀ P v i)) :
    x ∈ X.basicOpen (loc₀ P w i) := by
  have hi : x ∈ P.W i := X.basicOpen_le _ hx
  rw [X.mem_basicOpen _ x hi] at hx ⊢
  by_contra hw
  have e : loc₀ P v i = loc₀ P w i + ∑ k, cst f (P.W i) (v k - w k) * P.u k i := by
    simp only [loc₀, map_sub, sub_mul, Finset.sum_sub_distrib, add_sub_cancel]
  refine (IsLocalRing.notMem_maximalIdeal.2 hx) ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [e, map_add (f := _), map_sum]
  refine Ideal.add_mem _ ((IsLocalRing.mem_maximalIdeal _).2 hw) (Ideal.sum_mem _ fun k _ => ?_)
  rw [map_mul]
  refine Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).2 fun hu => ?_)
  exact (mem_basicOpen_cst f _ _ hi).1 ((X.mem_basicOpen _ x hi).2 hu) (hI (h k))


open GlobalTheory.AbLaw.Seesaw in
theorem triv_of_levels {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R} (hI : I ≤ Ideal.jacobson ⊥)
    {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} [UniversallyClosed f] {N : LB X} (hN : N.IsLB)
    (P : Perf f N) {Y : ℕ → Scheme.{0}} {b : ∀ e, Y e ⟶ X}
    {q : ∀ e, Y e ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))} (hb : ∀ e, IsPullback (b e) (q e) f (thick R I e))
    (ht : ∀ e, Triv (N.pull (b e))) : Triv N := by
  obtain ⟨e, he⟩ := exists_kernel_approx I P.D₀
  obtain ⟨v', hv', hu, -⟩ := loc_of_triv P (hb e) hN (ht e)
  choose v hv using fun k => Ideal.Quotient.mk_surjective (v' k)
  obtain rfl : Ideal.Quotient.mk (I ^ (e + 1)) ∘ v = v' := funext hv
  obtain ⟨w, hw, hvw⟩ := he v fun j => by
    rw [← Ideal.Quotient.eq_zero_iff_mem, RingHom.map_mulVec]
    exact congrFun hv' j
  let G : X.Opens := ⨆ i, X.basicOpen (loc₀ P w i)
  have hZ : IsClosed (f '' (G : Set X)ᶜ) := f.isClosedMap _ G.isOpen.isClosed_compl
  have hG : ∀ x, x ∈ G := by
    intro x
    by_contra hx
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ (f x).isPrime.ne_top
    have hsp : f x ⤳ (⟨m, hm.isPrime⟩ : PrimeSpectrum R) := (PrimeSpectrum.le_iff_specializes _ _).1 hle
    obtain ⟨x', hx', hfx⟩ := hsp.mem_closed hZ ⟨x, hx, rfl⟩
    have hIm : I ≤ m := hI.trans (sInf_le ⟨bot_le, hm⟩)
    have hr : f x' ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (e + 1)))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, hfx]
      exact (Ideal.pow_le_self (Nat.succ_ne_zero e)).trans hIm
    obtain ⟨z, hz⟩ := hr
    obtain ⟨y, rfl, -⟩ := Scheme.exists_preimage_of_isPullback (hb e) x' z hz.symm
    obtain ⟨i, hi⟩ := exists_mem P (b e y)
    have h₁ := hu i
    rw [loc_comp P (hb e)] at h₁
    have h₂ := mem_of_isUnit h₁ (y := y) hi
    rw [← Scheme.preimage_basicOpen] at h₂
    exact hx' (TopologicalSpace.Opens.mem_iSup.2 ⟨i, mem_basicOpen_loc₀ P hvw (by rw [hfx]; exact hIm) h₂⟩)
  have hid : IsPullback (𝟙 X) f f (Spec.map (CommRingCat.ofHom (RingHom.id R))) := by
    rw [CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  refine GlobalTheory.AbTriv.triv_of_pull_id (triv_of_loc P hid (RingHom.id R ∘ w) ?_ fun y => ?_)
  · funext j
    rw [← RingHom.map_mulVec, hw]
    rfl
  · obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hG y)
    refine ⟨i, ?_⟩
    rw [loc_comp P hid, ← Scheme.preimage_basicOpen]
    exact hi

theorem lbIso_of_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), Smooth X.hom → IsProjBy X.hom → GeometricallyConnected X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → ∀ M M' : LB X.left, M.IsLB → M'.IsLB → (∀ e, LBIso (M.pull (b e)) (M'.pull (b e))) → LBIso M M' := by
  intro R _ _ I hI X hs hp _ Y b hb M M' hM hM' w
  have := isProper_of_isProjBy R _ _ hp
  have hN := LB.isLB_div hM' hM
  obtain ⟨P⟩ := nonempty_perf_of_smooth_isProjBy R _ _ hs hp _ hN
  exact triv_of_levels (IsAdicComplete.le_jacobson_bot I) hN P hb fun e =>
    GlobalTheory.AlgTower.triv_chart (GlobalTheory.AlgTower.chartPullDiv M' M _) (w e)

end GlobalTheory.LBReductions
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfIsoOnAllReductionsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_iso_of_iso_on_all_reductions : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (X : Over (Spec (CommRingCat.of R))), Smooth X.hom → IsProjBy X.hom → GeometricallyConnected X.hom → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (b : ∀ e, (Y e).left ⟶ X.left), (∀ e, IsPullback (b e) (Y e).hom X.hom (thick R I e)) → ∀ M M' : LB X.left, M.IsLB → M'.IsLB → (∀ e, LBIso (M.pull (b e)) (M'.pull (b e))) → LBIso M M' := by
  first | exact @GlobalTheory.LBReductions.lbIso_of_reductions | exact GlobalTheory.LBReductions.lbIso_of_reductions | (intros; apply GlobalTheory.LBReductions.lbIso_of_reductions <;> assumption)
end
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AlgUniq

theorem isPullback_square {S S' : Scheme.{0}} {G : Over S} {A : Over S'} {f : S' ⟶ S}
    {a : A.left ⟶ G.left} (hA : IsPullback a A.hom G.hom f)
    {φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left} (h : Geo.Tor.IsSquare a φ₂) :
    IsPullback φ₂ (A ⊗ A).hom (G ⊗ G).hom f := by
  have w₁ : (fst G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have w₂ : (snd G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have v₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have h₁ := h.1
  have h₂ := h.2
  refine ⟨⟨by rw [← w₁, reassoc_of% h₁, hA.w, reassoc_of% v₁]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst G G).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd G G).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply pullback.hom_ext
    · change _ ≫ (fst G G).left = _ ≫ (fst G G).left
      rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ a) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · change _ ≫ (snd G G).left = _ ≫ (snd G G).left
      rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ a) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ A.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₁]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₂]

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y)
    (c : Z ⟶ X) (e : b ≫ a = c) : LBIso (L.pull c) ((L.pull a).pull b) := by
  subst e
  exact LBIso.symm (LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b)
      (fun _ => b ≫ a) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
      (chartPullId _) (PolBaseChange.lbIso_refl (pull_isLB hL _)))

theorem square_comp {S S' : Scheme.{0}} {G G' : Over S} {A : Over S'} {a : A.left ⟶ G.left}
    {a' : A.left ⟶ G'.left} {g : G ⟶ G'} (hg : a ≫ g.left = a')
    {φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left} {φ₂' : (A ⊗ A).left ⟶ (G' ⊗ G').left}
    (h : Geo.Tor.IsSquare a φ₂) (h' : Geo.Tor.IsSquare a' φ₂') : φ₂ ≫ (g ⊗ₘ g).left = φ₂' := by
  have h₁ := h.1
  have h₂ := h.2
  apply pullback.hom_ext
  · change _ ≫ (fst G' G').left = _ ≫ (fst G' G').left
    rw [Category.assoc, ← Over.comp_left, tensorHom_fst, Over.comp_left, reassoc_of% h₁, hg, h'.1]
  · change _ ≫ (snd G' G').left = _ ≫ (snd G' G').left
    rw [Category.assoc, ← Over.comp_left, tensorHom_snd, Over.comp_left, reassoc_of% h₂, hg, h'.2]

theorem exists_iso_algebraisation : GlobalTheory.Published.FormalAlgebraisation.Morphisms → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (B B' : Over (Spec (CommRingCat.of R))) [GrpObj B] [GrpObj B'], IsAbelianScheme B → IsAbelianScheme B' → IsProjBy B.hom → ∀ (b : ∀ e, (Y e).left ⟶ B.left) (b' : ∀ e, (Y e).left ⟶ B'.left), (∀ e, IsGrpPullback (Y e) B (thick R I e) (b e)) → (∀ e, β e ≫ b (e + 1) = b e) → (∀ e, IsGrpPullback (Y e) B' (thick R I e) (b' e)) → (∀ e, β e ≫ b' (e + 1) = b' e) → ∃ g : B ≅ B', IsMonHom g.hom ∧ (∀ e, b e ≫ g.hom.left = b' e) ∧ (∀ g' : B ⟶ B', (∀ e, b e ≫ g'.left = b' e) → g' = g.hom) ∧ (∀ (M : LB B.left) (M' : LB B'.left), M.IsLB → M'.IsLB → (∀ e, LBIso (M.pull (b e)) (M'.pull (b' e))) → LBIso M (M'.pull g.hom.left)) ∧ ∀ (P : LB (B ⊗ B).left) (P' : LB (B' ⊗ B').left) (b₂ : ∀ e, (Y e ⊗ Y e).left ⟶ (B ⊗ B).left) (b₂' : ∀ e, (Y e ⊗ Y e).left ⟶ (B' ⊗ B').left), P.IsLB → P'.IsLB → (∀ e, Geo.Tor.IsSquare (b e) (b₂ e)) → (∀ e, Geo.Tor.IsSquare (b' e) (b₂' e)) → (∀ e, LBIso (P.pull (b₂ e)) (P'.pull (b₂' e))) → LBIso P (P'.pull (g.hom ⊗ₘ g.hom).left) := by
  intro H R _ _ I hI Y _ β B B' _ _ hB hB' hp b b' hb hβ hb' hβ'
  have := hB.proper
  have := hB'.proper
  obtain ⟨g, hg, hu⟩ := H.exists_iso hI (fun e => (hb e).1) hβ (fun e => (hb' e).1) hβ'
  obtain ⟨k, hk, hk', -⟩ := GlobalTheory.T.grpHom_algebraisation_of_reductions H R I hI B B' hB.proper hB'.proper Y Y β β b b' hb hβ hb' hβ'
    (fun e => 𝟙 _) (fun e => inferInstance)
    (fun e => by rw [Over.id_left, Over.id_left, Category.comp_id, Category.id_comp])
  have hkg : k = g.hom := hu k fun e => by rw [hk', Over.id_left, Category.id_comp]
  refine ⟨g, hkg ▸ hk, hg, hu, fun M M' hM hM' h => ?_, fun P P' b₂ b₂' hP hP' hs hs' h => ?_⟩
  · exact GlobalTheory.T.lineBundle_iso_of_iso_on_all_reductions R I hI B hB.smooth hp hB.geomConnected Y b (fun e => (hb e).1) M _ hM
      (pull_isLB hM' _) fun e => (h e).trans (pull_isLB hM _) (pull_isLB hM' _)
        (pull_isLB (pull_isLB hM' _) _) (lbIso_pull_comp hM' _ _ _ (hg e))
  · have hBB := AbelianSchemeGerms.isAbelianScheme_tensor B B hB hB
    exact GlobalTheory.T.lineBundle_iso_of_iso_on_all_reductions R I hI (B ⊗ B) hBB.smooth (isProjBy_tensor R B B hp hp) hBB.geomConnected
      (fun e => Y e ⊗ Y e) b₂ (fun e => isPullback_square (hb e).1 (hs e)) P _ hP
      (pull_isLB hP' _) fun e => (h e).trans (pull_isLB hP _) (pull_isLB hP' _)
        (pull_isLB (pull_isLB hP' _) _) (lbIso_pull_comp hP' _ _ _ (square_comp (hg e) (hs e) (hs' e)))

end GlobalTheory.AlgUniq
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastPosOfKapIs
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HolDict

theorem lamAt_last {R : Ranks} (h : HCParam R) (i : Fin R.m) (n : ℕ) (hn : n + 1 = R.k + i) :
    Formalism.L2.NTheta.lamAt h n = -h.b i := by
  have hk := R.m_add_three_le_k
  have hi := i.2
  have e : n - (R.k - 1) = i := by omega
  unfold Formalism.L2.NTheta.lamAt
  rw [dite_eq_right (by omega), dite_eq_left (by omega)]
  congr 2
  exact Fin.ext e

theorem lastPos_of_kapIs :
    ∀ (D : D7) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)), KapIs κ → ∀ i, (κ i).LastPos := by
  intro D κ h i τ k hk
  rw [(h i τ).1 k,
    show (Wc D i).sig (tauE D τ) = D.R.sigW ((i : ℕ) + 1) from D.sp.W_sigval _ (inR i).1 (inR i).2 _]
  have hp : (k : ℕ) + 1 = D.R.k + i := by
    rw [hk]
    simp only [Ranks.sigW]
    omega
  have hg := (D.hc τ).gap_be i
  have hq : (((D.R.sigW ((i : ℕ) + 1)).1 : ℕ) : ℚ) = ((k : ℕ) : ℚ) + 1 := by
    exact_mod_cast hk.symm
  simp only [aPl, if_pos k.2]
  rw [lamAt_last (D.hc τ) i k hp, hq]
  have h1 : (1 : ℤ) ≤ ⌊-(D.hc τ).b i + (D.hc τ).e i - (((k : ℕ) : ℚ) + 1 - (((k : ℕ) : ℚ) + 1)) -
      ((D.R.t : ℚ) + 1) / 2⌋ := by
    rw [Int.le_floor]
    push_cast
    linarith
  omega

end GlobalTheory.HolDict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootFlatPushforwardGeoFun
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.AtP

theorem den_factorization_le {p : ℕ} (hp : p.Prime) (q : ℚ) (e : ℕ) (k : ℤ) (m : ℕ) (hm : ¬ p ∣ m)
    (h : q * (p : ℚ) ^ e = k / m) : q.den.factorization p ≤ e := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero p)
  have hm0' : (m : ℚ) ≠ 0 := by exact_mod_cast hm0
  have hq : q = Rat.divInt k ((m * p ^ e : ℕ) : ℤ) := by
    rw [Rat.divInt_eq_div]
    push_cast
    have hp0 : (p : ℚ) ^ e ≠ 0 := pow_ne_zero _ (by exact_mod_cast hp.ne_zero)
    rw [eq_div_iff (mul_ne_zero hm0' hp0), mul_comm (m : ℚ), ← mul_assoc, h, div_mul_cancel₀ _ hm0']
  have hd : q.den ∣ m * p ^ e := by
    have := Rat.den_dvd k ((m * p ^ e : ℕ) : ℤ)
    rw [← hq] at this
    exact_mod_cast this
  have hne : m * p ^ e ≠ 0 := mul_ne_zero hm0 (pow_ne_zero _ hp.ne_zero)
  have := (Nat.factorization_le_iff_dvd (Rat.den_nz q) hne).2 hd p
  rw [Nat.factorization_mul hm0 (pow_ne_zero _ hp.ne_zero), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hm, hp.factorization_pow, Finsupp.single_eq_same, zero_add] at this
  exact this

end GlobalTheory.AtP

namespace GlobalTheory.AtP

theorem main : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β : G.Cˣ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (h₂ : Gr G 1), ∃ k : ℕ, ∀ y : grp G β, f' (h₂⁻¹ * toP1 G β y * h₂) ≠ 0 → (∀ i, ((Module.finBasis ℚ G.C).repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) i).den.factorization p ≤ k) ∧ (((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)).den.factorization p ≤ k := by
  intro p _ G β K' f' hf h₂
  have hp : p.Prime := Fact.out
  obtain ⟨B, e₁, hB⟩ := GlobalTheory.T.regular_elements_bounded_padic p G K' f' hf β h₂
  obtain ⟨e₂, he⟩ := GlobalTheory.T.bounded_coordinates_p_power_denominator p G B
  refine ⟨max e₁ e₂, fun y hy => ?_⟩
  obtain ⟨hb, k, m, hm, hs⟩ := hB y hy
  refine ⟨fun i => ?_, ?_⟩
  · obtain ⟨k', m', hm', hc⟩ := he _ hb i
    exact (den_factorization_le hp _ e₂ k' m' hm' hc).trans (le_max_right _ _)
  · rw [Units.val_inv_eq_inv_val]
    exact (den_factorization_le hp _ e₁ k m hm hs).trans (le_max_left _ _)

end GlobalTheory.AtP
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultLabelRank
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx GlobalTheory.TorCls
open scoped TensorProduct Classical

namespace GlobalTheory.TorCls

theorem exists_open_psiAway_mem_conj_level : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (β : G.Cˣ)
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t) (y : G.C) (r₁ : G.GAf),
    letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C);
    ∃ O : Set ((AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ), IsOpen O ∧ 1 ∈ O ∧ ∀ z ∈ O, InT G (AfP p) β y z →
      ∃ k ∈ L.K.toSubgroup, ((r₁ * k * r₁⁻¹ : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ) = psiAway G x z := by
  intro p _ G L β x t hx y r₁
  letI : TopologicalSpace (AfP p ⊗[ℚ] G.C) := moduleTopology (AfP p) (AfP p ⊗[ℚ] G.C)
  haveI : IsModuleTopology (AfP p) (AfP p ⊗[ℚ] G.C) := ⟨rfl⟩
  haveI : IsTopologicalRing (AfP p ⊗[ℚ] G.C) := IsModuleTopology.isTopologicalRing (AfP p) (AfP p ⊗[ℚ] G.C)
  let K' : Set G.GAf := (fun g : G.GAf => r₁⁻¹ * g * r₁) ⁻¹' (L.K : Set G.GAf)
  have hK'o : IsOpen K' :=
    L.K.isOpen.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  obtain ⟨V, hVo, hV⟩ := isOpen_induced_iff.1 hK'o
  refine ⟨psiAway G x ⁻¹' V, hVo.preimage ?_, ?_, ?_⟩
  · show Continuous (fun z : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ => ((x * z.1 * x⁻¹, z.2) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ))
    exact ((continuous_const.mul continuous_fst).mul continuous_const).prodMk continuous_snd
  · have h1 : (1 : G.GAf) ∈ K' := by
      show r₁⁻¹ * 1 * r₁ ∈ (L.K : Set G.GAf)
      rw [mul_one, inv_mul_cancel]
      exact L.K.one_mem
    rw [← hV] at h1
    show psiAway G x 1 ∈ V
    rw [map_one]
    exact h1
  · intro z hz hT
    have hw : psiAway G x z ∈ UPts G.star (AfP p) := by
      rw [psiAway_apply]
      exact conj_mul_star (starT G.star (AfP p)) (inC G (AfP p) (β : G.C)) x z.1 t (z.2 : AfP p) hx hT.1
    let g : G.GAf := ⟨psiAway G x z, hw⟩
    have hg : g ∈ K' := by
      rw [← hV]
      exact hz
    refine ⟨r₁⁻¹ * g * r₁, hg, ?_⟩
    have : r₁ * (r₁⁻¹ * g * r₁) * r₁⁻¹ = g := by group
    rw [this]

end GlobalTheory.TorCls
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisRingEventually
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisRingEventually
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

theorem isIntB_one_mul_eventually : ∀ (A : Type) [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A] (κ : Type)
    (b : Module.Basis κ ℚ A),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, IsIntB v b 1 ∧
      ∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z) := by
  intro A _ _ _ κ b
  haveI : Fintype κ := FiniteDimensional.fintypeBasisIndex b
  have hc : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ t : κ × κ × κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr (b t.1 * b t.2.1) t.2.2) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun t => rat_mem_adicCompletionIntegers_eventually _
  have h1 : ∀ᶠ v : HeightOneSpectrum ℤ in Filter.cofinite, ∀ k : κ,
      algebraMap ℚ (v.adicCompletion ℚ) (b.repr 1 k) ∈ v.adicCompletionIntegers ℚ :=
    Filter.eventually_all.2 fun k => rat_mem_adicCompletionIntegers_eventually _
  have hfin := Filter.eventually_cofinite.1 (hc.and h1)
  refine ⟨hfin.toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
  obtain ⟨hcv, h1v⟩ := hv
  refine ⟨fun k => ?_, fun y z hy hz k => ?_⟩
  · rw [Algebra.TensorProduct.one_def, repr_tmul_apply, one_mul]
    exact h1v k
  · set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum_tmul b v y, eq_sum_tmul b v z, Finset.sum_mul_sum, map_sum, Finsupp.finsetSum_apply]
      refine sum_mem fun i _ => ?_
      rw [map_sum, Finsupp.finsetSum_apply]
      refine sum_mem fun j _ => ?_
      rw [Algebra.TensorProduct.tmul_mul_tmul, repr_tmul_apply]
      exact mul_mem (mul_mem (hy i) (hz j)) (hcv (i, j, k))

end GlobalTheory.AdicSpan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdicIntegralTensorBasisRingEventuallyStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicIntegralTensorBasis_ring_eventually : ∀ (A : Type) [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A] (κ : Type) (b : Module.Basis κ ℚ A),
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, IsIntB v b 1 ∧
      ∀ y z, IsIntB v b y → IsIntB v b z → IsIntB v b (y * z) := by
  first | (exact @GlobalTheory.AdicSpan.isIntB_one_mul_eventually) | (exact GlobalTheory.AdicSpan.isIntB_one_mul_eventually) | (intros; apply GlobalTheory.AdicSpan.isIntB_one_mul_eventually  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLimsupShiftLe
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLimsupShiftLe
set_option autoImplicit false

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal Topology

namespace GlobalTheory.GrowthShift

theorem eventually_mul_inv_pow_le (D e : ℕ) {a : ℝ≥0∞} (ha : a < 1) :
    ∀ᶠ k : ℕ in atTop, a * ((k : ℝ≥0∞) ^ D)⁻¹ ≤ (((k + e : ℕ) : ℝ≥0∞) ^ D)⁻¹ := by
  lift a to NNReal using ha.ne_top
  have ha' : (a : ℝ) < 1 := by exact_mod_cast ha
  have h1 : Tendsto (fun k : ℕ => ((k : ℝ) / (k + (e : ℝ))) ^ D) atTop (𝓝 1) := by
    simpa using (tendsto_natCast_div_add_atTop (e : ℝ)).pow D
  filter_upwards [h1.eventually (lt_mem_nhds ha'), eventually_gt_atTop 0] with k hk hk0
  have hkR : (0 : ℝ) < k := Nat.cast_pos.2 hk0
  have hke : (0 : ℝ) < ((k : ℝ) + e) ^ D := by positivity
  rw [div_pow, lt_div_iff₀ hke] at hk
  have h2 : (a : ℝ≥0∞) * ((k + e : ℕ) : ℝ≥0∞) ^ D ≤ (k : ℝ≥0∞) ^ D := by
    have h3 : a * ((k + e : ℕ) : NNReal) ^ D ≤ (k : NNReal) ^ D := by
      rw [← NNReal.coe_le_coe]
      push_cast
      exact hk.le
    exact_mod_cast h3
  have n0 : (k : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hk0.ne')
  have nt : (k : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top k)
  rw [ENNReal.le_inv_iff_mul_le, mul_right_comm, ← div_eq_mul_inv, ENNReal.div_le_iff n0 nt, one_mul]
  exact h2

theorem growth_shift_le : ∀ (D e : ℕ) (r : ℕ → ℕ∞), growth D (fun k => r (k + e)) ≤ growth D r := by
  intro D e r
  refine ENNReal.le_of_forall_lt_one_mul_le fun a ha => ?_
  rw [growth, growth, ← ENNReal.limsup_const_mul_of_ne_top ha.ne_top,
    ← Filter.limsup_nat_add (fun τ : ℕ => (D.factorial : ℝ≥0∞) * (r τ : ℝ≥0∞) / (τ : ℝ≥0∞) ^ D) e]
  refine limsup_le_limsup ((eventually_mul_inv_pow_le D e ha).mono fun k hk => ?_)
  simp only [div_eq_mul_inv]
  rw [mul_left_comm]
  exact mul_le_mul_right hk _

end GlobalTheory.GrowthShift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLimsupShiftLeStatement
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankGrowthLimsup_shift_le : ∀ (D e : ℕ) (r : ℕ → ℕ∞), growth D (fun k => r (k + e)) ≤ growth D r := by
  first | exact @GlobalTheory.GrowthShift.growth_shift_le | exact GlobalTheory.GrowthShift.growth_shift_le | (intros; apply GlobalTheory.GrowthShift.growth_shift_le <;> assumption)
end
end
