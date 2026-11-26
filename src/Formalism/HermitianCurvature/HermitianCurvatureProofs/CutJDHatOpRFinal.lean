module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRAsm
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRvStepB
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapAAll

@[expose] public section

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDGaugeQQHatQQ
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

theorem jDHatOpQQ_of_opA_opR_residue_splitting (hA : JDOpA) (hR : JDOpR) (h1 : ResidueSplittingModelAlgebra) (h2 : MirrorResidueSplittingModelAlgebra)
    (h3 : JDHatLagrange) (h4 : JDHatNodes) : JDHatOpQQ := by
  obtain ⟨KA, hKA, hA⟩ := hA
  obtain ⟨KR, hKR, hR⟩ := hR
  refine ⟨max KA KR, le_max_of_le_left hKA, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr _ hGQ hML X hX
  have hAat := hA (max KA KR) (le_max_left _ _) E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hML
  have hRat := hR (max KA KR) (le_max_right _ _) E Wp Wq S T f χ ν' m₀ top A₀ hB v e L hFr hGQ hML
  have hAh : ∀ y, HReal (max KA KR) S T v e L (L.Ahat y) := fun y => by
    obtain ⟨Θ, _, hΘ, _, hJ⟩ := hAat y
    exact hReal_op Θ hΘ fun J hJ' => (hJ J hJ').1
  have hAhv : ∀ y, HReal (max KA KR) S T v e L (L.Ahatv y) := fun y => by
    obtain ⟨_, Θv, _, hΘv, hJ⟩ := hAat y
    exact hReal_op Θv hΘv fun J hJ' => (hJ J hJ').2
  have hRh : ∀ y : ℝ, HReal (max KA KR) S T v e L (RhM (D.parOf S v) L y) := fun y => by
    obtain ⟨Θ, _, hΘ, _, hJ⟩ := hRat y
    exact hReal_op Θ hΘ fun J hJ' => (hJ J hJ').1
  have hRhv : ∀ y : ℝ, HReal (max KA KR) S T v e L (RhvM (D.parOf S v) L y) := fun y => by
    obtain ⟨_, Θv, _, hΘv, hJ⟩ := hRat y
    exact hReal_op Θv hΘv fun J hJ' => (hJ J hJ').2
  have hx : ∀ y, xInvM (D.parOf S v) y ∈ Submonoid.closure (MA.bddSet (D.parOf S v) L) :=
    fun y => jdh_kap_mem _ L _
  obtain ⟨ν, hνi, hνr⟩ := h4 (D.parOf S v)
  have hR0n : ∀ j, HReal (max KA KR) S T v e L (L.R0 (ν j)) := fun j => by
    rw [h1 _ L hML _ (hνr j)]
    refine hReal_sub (hReal_mul (hx _) (hRh _)) (hReal_sum _ _ fun l hl => ?_)
    exact hReal_mul (Submonoid.mul_mem _ (Submonoid.mul_mem _ (hx _) (jdh_SSn_mem _ L l hl))
      (jdh_kap_mem _ L _)) (hAh _)
  have hR0vn : ∀ j, HReal (max KA KR) S T v e L (L.R0v (ν j)) := fun j => by
    rw [h2 _ L hML _ (hνr j)]
    refine hReal_sub (hReal_mul (hx _) (hRhv _)) (hReal_sum _ _ fun l hl => ?_)
    exact hReal_mul (Submonoid.mul_mem _ (Submonoid.mul_mem _ (hx _) (jdh_kap_mem _ L _))
      (jdh_SSns_mem _ L l hl)) (hAhv _)
  have key : HReal (max KA KR) S T v e L X := by
    simp only [MA.hatSet, Set.mem_union, Set.mem_range] at hX
    rcases hX with ((⟨y, rfl⟩ | ⟨y, rfl⟩) | ⟨y, rfl⟩) | ⟨y, rfl⟩
    · exact hAh y
    · rw [(h3 _ L ν hνi y).1]
      exact hReal_sum _ _ fun j _ => hReal_smul _ (hR0n j)
    · exact hAhv y
    · rw [(h3 _ L ν hνi y).2]
      exact hReal_sum _ _ fun j _ => hReal_smul _ (hR0vn j)
  exact key

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.MirrorResidueSplittingHolds
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.R.LevelData Formalism.FourierDecayAlt.P.RuleGD

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

section
variable {P : M.Par} {L : LevelData (A P (DQ P)) P.r}

theorem inverse_mul_regular_element {y : ℂ} (hy : RegY P y) : xInvM P y * xA P (DQ P) y = 1 := by
  unfold xInvM xA
  rw [← map_mul]
  have : ((fun π => (M.xC P π y)⁻¹) * fun π => M.xC P π y) = (1 : M.Ty P → ℂ) := by
    funext π; simp only [Pi.mul_apply, Pi.one_apply]; exact inv_mul_cancel₀ (hy π)
  rw [this, map_one]

theorem jdr_kap_DG (g : M.Ty P → ℂ) {z : A P (DQ P)} (hz : z ∈ Formalism.FourierDecayAlt.P.MAx3.H.DG P) :
    kap P (DQ P) g * z = z * kap P (DQ P) g := Formalism.FourierDecayAlt.P.MAx3.H.kap_comm_DG P g hz

theorem jdr_SC_DG {z : A P (DQ P)} (hz : z ∈ Formalism.FourierDecayAlt.P.MAx3.H.SC P) : z ∈ Formalism.FourierDecayAlt.P.MAx3.H.DG P := by
  obtain ⟨w, rfl⟩ := hz
  exact Formalism.FourierDecayAlt.P.MAx3.H.sc_memDG P w

end

theorem residue_splitting_holds : ResidueSplittingModelAlgebra := by
  intro P L hL y hy
  obtain ⟨hDr, hDrb, hDri, -⟩ := Formalism.FourierDecayAlt.P.MAx3.H.DrSC hL
  have hGG : L.GG = ggA P (DQ P) := hL.2.2.2.2.2.2.2.2.2.2.1
  have hGGsc : L.GG ∈ Formalism.FourierDecayAlt.P.MAx3.H.SC P := (Formalism.FourierDecayAlt.P.MAx3.H.levSC hL).2.2.2.2.2.2.2.2.1
  have hl0 : L.l0 y = l0A P (DQ P) y := by
    obtain ⟨-, -, -, -, -, -, -, -, hzb, -, -, hgi, hn, -, -⟩ := hL
    simp only [LevelData.l0, l0A, hn, hzb, hgi]
  set X := xInvM P y with hXdef
  set x := xA P (DQ P) y with hxdef
  have hXx : X * x = 1 := inverse_mul_regular_element hy
  have cD : X * L.Drb = L.Drb * X := jdr_kap_DG _ (jdr_SC_DG hDrb)
  have cG : X * L.GG = L.GG * X := jdr_kap_DG _ (jdr_SC_DG hGGsc)
  have hDriDr : L.Dri * L.Dr = 1 := by
    rw [Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (Formalism.FourierDecayAlt.P.MAx3.H.memDri L) (Formalism.FourierDecayAlt.P.MAx3.H.memDr L)]
    exact Formalism.FourierDecayAlt.P.MAx3.H.Dr_Dri' L

  have hterm : ∀ l ∈ Finset.Icc 1 (P.k - 1),
      X * SSn P L l * kap P (DQ P) (fun π => M.xEx P {l} π y) * L.Ahat y =
        X * L.Drb * (SS P (DQ P) l * kap P (DQ P) (fun π => M.xEx P {l} π y)) * L.Ar y := by
    intro l _
    have c1 : SS P (DQ P) l * L.Dr = L.Dr * SS P (DQ P) l := Formalism.FourierDecayAlt.P.MAx3.H.SS_comm_SC P l hDr
    have c2 : kap P (DQ P) (fun π => M.xEx P {l} π y) * L.Dr = L.Dr * kap P (DQ P) (fun π => M.xEx P {l} π y) :=
      jdr_kap_DG _ (jdr_SC_DG hDr)
    unfold SSn LevelData.Ahat
    calc X * (L.Drb * L.Dri * SS P (DQ P) l) * kap P (DQ P) (fun π => M.xEx P {l} π y) * (L.Dr * L.Ar y)
        = X * L.Drb * L.Dri * (SS P (DQ P) l * (kap P (DQ P) (fun π => M.xEx P {l} π y) * L.Dr)) * L.Ar y := by
          simp only [mul_assoc]
      _ = X * L.Drb * (L.Dri * L.Dr) * (SS P (DQ P) l * kap P (DQ P) (fun π => M.xEx P {l} π y)) * L.Ar y := by
          rw [c2, ← mul_assoc (SS P (DQ P) l), c1]; simp only [mul_assoc]
      _ = _ := by rw [hDriDr, mul_one]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.mul_sum]
  have hS21 : (∑ l ∈ Finset.Icc 1 (P.k - 1), SS P (DQ P) l * kap P (DQ P) (fun π => M.xEx P {l} π y)) =
      weightedSumBis P (DQ P) y := rfl
  rw [hS21]

  have hR : X * RhM P L y = L.R0 y + X * L.Drb * weightedSumBis P (DQ P) y * L.Ar y := by
    unfold RhM LevelData.R0 t21 t22
    rw [hl0, hGG]
    have e1 : X * (ggA P (DQ P) * x) = ggA P (DQ P) := by
      rw [← mul_assoc, ← hGG, cG, mul_assoc, hXx, mul_one]
    have e2 : X * (ggA P (DQ P) * x * l0A P (DQ P) y) = ggA P (DQ P) * l0A P (DQ P) y := by
      rw [← mul_assoc X, e1]
    calc X * (L.Drb * ((ggA P (DQ P) * x * l0A P (DQ P) y + weightedSumBis P (DQ P) y) * L.Ar y + ggA P (DQ P) * x * L.Br y))
        = L.Drb * ((X * (ggA P (DQ P) * x * l0A P (DQ P) y) + X * weightedSumBis P (DQ P) y) * L.Ar y +
            X * (ggA P (DQ P) * x) * L.Br y) := by
          rw [← mul_assoc, cD, mul_assoc]; simp only [mul_add, add_mul, mul_assoc]
      _ = L.Drb * ggA P (DQ P) * (l0A P (DQ P) y * L.Ar y + L.Br y) + X * L.Drb * weightedSumBis P (DQ P) y * L.Ar y := by
          rw [e1, e2, cD]; simp only [mul_add, add_mul, mul_assoc]; abel
  rw [hR]; abel

theorem mirror_residue_splitting_holds : MirrorResidueSplittingModelAlgebra := by
  intro P L hL y hy
  obtain ⟨hDr, hDrb, -, hDrbi⟩ := Formalism.FourierDecayAlt.P.MAx3.H.DrSC hL
  have hGG : L.GG = ggA P (DQ P) := hL.2.2.2.2.2.2.2.2.2.2.1
  have hGGsc : L.GG ∈ Formalism.FourierDecayAlt.P.MAx3.H.SC P := (Formalism.FourierDecayAlt.P.MAx3.H.levSC hL).2.2.2.2.2.2.2.2.1
  have hm0 : L.m0 y = m0A P (DQ P) y := by
    obtain ⟨-, -, -, -, -, -, hz, -, -, -, -, hgi, -, hns, -⟩ := hL
    simp only [LevelData.m0, m0A, hns, hz, hgi]
  have sDrb : star L.Drb = L.Dr := by
    unfold LevelData.Drb LevelData.Dr
    rw [Formalism.FourierDecayAlt.P.MAx3.H.star_list_prod', List.map_ofFn]
    have : (star ∘ L.cb) = L.c := funext fun l => by
      obtain ⟨-, -, hc, -, hcb, -⟩ := hL
      show star (L.cb l) = L.c l
      rw [hcb, hc]
      simp only [cbA, cA, sc, Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
      rfl
    rw [this, Formalism.FourierDecayAlt.P.MAx3.H.rev_prod L]
    intro x hx; obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact Formalism.FourierDecayAlt.P.MAx3.H.memF L (m_c L l)
  have sDri : star L.Dri = L.Drbi := by
    unfold LevelData.Dri LevelData.Drbi
    rw [Formalism.FourierDecayAlt.P.MAx3.H.star_list_prod', List.map_ofFn]
    have : (star ∘ L.ci) = L.cbi := funext fun l => by
      obtain ⟨-, -, -, hci, -, hcbi, -⟩ := hL
      show star (L.ci l) = L.cbi l
      rw [hci, hcbi]
      simp only [ciA, cbiA, sc, Matrix.scalar_apply, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
      rfl
    rw [this, Formalism.FourierDecayAlt.P.MAx3.H.rev_prod L]
    intro x hx; obtain ⟨l, rfl⟩ := List.mem_ofFn.1 hx; exact Formalism.FourierDecayAlt.P.MAx3.H.memF L (m_cbi L l)
  set X := xInvM P y with hXdef
  set x := xA P (DQ P) y with hxdef
  have hXx : X * x = 1 := inverse_mul_regular_element hy
  have cD : X * L.Dr = L.Dr * X := jdr_kap_DG _ (jdr_SC_DG hDr)
  have cG : X * L.GG = L.GG * X := jdr_kap_DG _ (jdr_SC_DG hGGsc)
  have hDrbiDrb : L.Drbi * L.Drb = 1 := by
    rw [Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (Formalism.FourierDecayAlt.P.MAx3.H.memDrbi L) (Formalism.FourierDecayAlt.P.MAx3.H.memDrb L)]
    exact Formalism.FourierDecayAlt.P.MAx3.H.Drb_Drbi' L
  have cDD : L.Dr * L.Drb = L.Drb * L.Dr :=
    Formalism.FourierDecayAlt.P.MAx3.H.cl_comm L (Formalism.FourierDecayAlt.P.MAx3.H.memDr L) (Formalism.FourierDecayAlt.P.MAx3.H.memDrb L)
  have hterm : ∀ l ∈ Finset.Icc 1 (P.k - 1),
      X * kap P (DQ P) (fun π => M.xEx P {l} π y) * star (SSn P L l) * L.Ahatv y =
        X * L.Dr * (kap P (DQ P) (fun π => M.xEx P {l} π y) * star (SS P (DQ P) l)) * L.Avr y := by
    intro l _
    have c1 : star (SS P (DQ P) l) * L.Dr = L.Dr * star (SS P (DQ P) l) := Formalism.FourierDecayAlt.P.MAx3.H.SSs_comm_SC l hDr
    have c2 : kap P (DQ P) (fun π => M.xEx P {l} π y) * L.Dr = L.Dr * kap P (DQ P) (fun π => M.xEx P {l} π y) :=
      jdr_kap_DG _ (jdr_SC_DG hDr)
    have hs : star (SSn P L l) = star (SS P (DQ P) l) * L.Drbi * L.Dr := by
      unfold SSn; rw [star_mul, star_mul, sDri, sDrb, mul_assoc]
    rw [hs]
    unfold LevelData.Ahatv
    calc X * kap P (DQ P) (fun π => M.xEx P {l} π y) * (star (SS P (DQ P) l) * L.Drbi * L.Dr) * (L.Drb * L.Avr y)
        = X * kap P (DQ P) (fun π => M.xEx P {l} π y) * star (SS P (DQ P) l) * (L.Drbi * (L.Dr * L.Drb)) *
            L.Avr y := by simp only [mul_assoc]
      _ = X * (kap P (DQ P) (fun π => M.xEx P {l} π y) * (star (SS P (DQ P) l) * L.Dr)) * L.Avr y := by
          rw [cDD, ← mul_assoc L.Drbi, hDrbiDrb, one_mul]; simp only [mul_assoc]
      _ = _ := by rw [c1, ← mul_assoc (kap P (DQ P) _), c2]; simp only [mul_assoc]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, ← Finset.mul_sum]
  have hS12 : (∑ l ∈ Finset.Icc 1 (P.k - 1), kap P (DQ P) (fun π => M.xEx P {l} π y) * star (SS P (DQ P) l)) =
      S12 P (DQ P) y := rfl
  rw [hS12]
  have hR : X * RhvM P L y = L.R0v y + X * L.Dr * S12 P (DQ P) y * L.Avr y := by
    unfold RhvM LevelData.R0v t12 t22
    rw [hm0, hGG]
    have e1 : X * (ggA P (DQ P) * x) = ggA P (DQ P) := by
      rw [← mul_assoc, ← hGG, cG, mul_assoc, hXx, mul_one]
    have e2 : X * (ggA P (DQ P) * x * m0A P (DQ P) y) = ggA P (DQ P) * m0A P (DQ P) y := by
      rw [← mul_assoc X, e1]
    calc X * (L.Dr * ((ggA P (DQ P) * x * m0A P (DQ P) y + S12 P (DQ P) y) * L.Avr y + ggA P (DQ P) * x * L.Bvr y))
        = L.Dr * ((X * (ggA P (DQ P) * x * m0A P (DQ P) y) + X * S12 P (DQ P) y) * L.Avr y +
            X * (ggA P (DQ P) * x) * L.Bvr y) := by
          rw [← mul_assoc, cD, mul_assoc]; simp only [mul_add, add_mul, mul_assoc]
      _ = L.Dr * ggA P (DQ P) * (m0A P (DQ P) y * L.Avr y + L.Bvr y) + X * L.Dr * S12 P (DQ P) y * L.Avr y := by
          rw [e1, e2, cD]; simp only [mul_add, add_mul, mul_assoc]; abel
  rw [hR]; abel

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatLagrange
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem jdl_pow (d : ℕ) (ν : Fin (d + 1) → ℝ) (hν : Function.Injective ν) (k : ℕ) (hk : k ≤ d) (y : ℂ) :
    y ^ k = ∑ j, lagC ν j y * ((ν j : ℝ) : ℂ) ^ k := by
  classical
  have hinj : Set.InjOn (fun j : Fin (d + 1) => ((ν j : ℝ) : ℂ)) (Finset.univ : Finset (Fin (d + 1))) :=
    fun a _ b _ h => hν (Complex.ofReal_injective h)
  have hdeg : (Polynomial.X ^ k : Polynomial ℂ).degree < (Finset.univ : Finset (Fin (d + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin, Polynomial.degree_X_pow]
    exact_mod_cast Nat.lt_succ_of_le hk
  have hf := Lagrange.eq_interpolate hinj hdeg
  have h := congrArg (Polynomial.eval y) hf
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Polynomial.eval_pow, Polynomial.eval_X] at h
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, mul_comm]
  congr 1
  unfold lagC Lagrange.basis
  rw [Polynomial.eval_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
  rw [div_eq_inv_mul]

theorem jdl_interp {R : Type} [Ring R] [Algebra ℂ R] (f : ℂ → R) (d : ℕ)
    (hf : Formalism.FourierDecayAlt.P.MAx3.G.PolyIn (fun s => f (0 + s)) d) (ν : Fin (d + 1) → ℝ) (hν : Function.Injective ν)
    (y : ℂ) : f y = ∑ j, lagC ν j y • f ((ν j : ℝ) : ℂ) := by
  obtain ⟨a, ha⟩ := hf
  have hf' : ∀ s, f s = ∑ k ∈ Finset.range (d + 1), s ^ k • a k := fun s => by simpa using ha s
  have e1 : f y = ∑ k ∈ Finset.range (d + 1), (∑ j, lagC ν j y * ((ν j : ℝ) : ℂ) ^ k) • a k := by
    rw [hf' y]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← jdl_pow d ν hν k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) y]
  rw [e1]
  simp only [hf', Finset.sum_smul, Finset.smul_sum, smul_smul]
  exact Finset.sum_comm

theorem hat_lagrange_decay_holds : JDHatLagrange := by
  intro P L ν hν y
  exact ⟨jdl_interp (fun s => L.R0 s) (P.r + 1) (Formalism.FourierDecayAlt.P.MAx3.G.raising_operator_polynomial P L 0) ν hν y,
    jdl_interp (fun s => L.R0v s) (P.r + 1) (Formalism.FourierDecayAlt.P.MAx3.L.raising_variant_polynomial P L 0) ν hν y⟩

end

end Formalism.FourierDecayAlt.P.CutMP
end

section -- merged from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatNodes
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem hat_nodes_decay_holds : JDHatNodes := by
  intro P
  classical
  obtain ⟨Mb, hMb⟩ : ∃ Mb : ℝ, Mb = 1 + ∑ π : M.Ty P, ∑ i ∈ Finset.Icc 1 (P.k - 1), |M.rho P π i| := ⟨_, rfl⟩
  refine ⟨fun j => Mb + ((j : ℕ) : ℝ), fun a b h => ?_, fun j π => ?_⟩
  · dsimp only at h
    have h' : ((a : ℕ) : ℝ) = ((b : ℕ) : ℝ) := add_left_cancel h
    exact Fin.ext (by exact_mod_cast h')
  · unfold M.xC
    rw [Finset.prod_ne_zero_iff]
    intro i hi
    have hle : |M.rho P π i| ≤ ∑ π' : M.Ty P, ∑ i' ∈ Finset.Icc 1 (P.k - 1), |M.rho P π' i'| := by
      calc |M.rho P π i| ≤ ∑ i' ∈ Finset.Icc 1 (P.k - 1), |M.rho P π i'| :=
            Finset.single_le_sum (f := fun i' => |M.rho P π i'|) (fun _ _ => abs_nonneg _) hi
        _ ≤ _ := Finset.single_le_sum (f := fun π' => ∑ i' ∈ Finset.Icc 1 (P.k - 1), |M.rho P π' i'|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ π)
    have hpos : 0 < Mb + ((j : ℕ) : ℝ) + M.rho P π i := by
      have h1 := neg_abs_le (M.rho P π i)
      have hj : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    have hc : (((Mb + ((j : ℕ) : ℝ) : ℝ) : ℂ) + ((M.rho P π i : ℝ) : ℂ)) =
        ((Mb + ((j : ℕ) : ℝ) + M.rho P π i : ℝ) : ℂ) := by push_cast; ring
    rw [hc]
    exact Complex.ofReal_ne_zero.2 (ne_of_gt hpos)

end

end Formalism.FourierDecayAlt.P.CutMP
end

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

theorem residue_operator_holds : JDOpR := jDOpR_of_vStepB mirror_residue_second_move

theorem hat_quadratic_operator_holds : JDHatOpQQ :=
  jDHatOpQQ_of_opA_opR_residue_splitting (jDOpA_of_parts polynomial_decay_admissible capelli_minors_holds) residue_operator_holds residue_splitting_holds
    mirror_residue_splitting_holds hat_lagrange_decay_holds hat_nodes_decay_holds

end Formalism.FourierDecayAlt.P.CutMP
