module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatSmulMatrixMulVecCompletedSelfDual
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLatticeIffIntegralMatrixSplitChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableLatticeEqZpowStdInertCompletion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceHyperspecialStableLatticeEqMultiple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqMultipleOfStandardLattice
open IsDedekindDomain NumberField Matrix

namespace GlobalTheory.LatticeBetweenMultiples

lemma one_add_mulVec_mem {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {n : ℕ}
    (S : AddSubgroup (Fin n → v.adicCompletion F))
    (hGL : ∀ x : GL (Fin n) (v.adicCompletion F), (∀ i j, x.1 i j ∈ v.adicCompletionIntegers F) →
      (∀ i j, (x⁻¹).1 i j ∈ v.adicCompletionIntegers F) → ∀ w ∈ S, x.1.mulVec w ∈ S)
    (N : Matrix (Fin n) (Fin n) (v.adicCompletion F)) (hN : N * N = 0)
    (hNi : ∀ i j, N i j ∈ v.adicCompletionIntegers F) {w : Fin n → v.adicCompletion F}
    (hw : w ∈ S) : (1 + N).mulVec w ∈ S := by
  have h1 : (1 + N) * (1 - N) = 1 := by
    rw [add_mul, one_mul, mul_sub, mul_one, hN, sub_zero, sub_add_cancel]
  have h2 : (1 - N) * (1 + N) = 1 := by
    rw [sub_mul, one_mul, mul_add, mul_one, hN, add_zero, add_sub_cancel_right]
  have h1m : ∀ i j, (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) i j ∈
      v.adicCompletionIntegers F := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  have hp : ∀ i j, (1 + N) i j ∈ v.adicCompletionIntegers F := by
    intro i j; rw [Matrix.add_apply]; exact add_mem (h1m i j) (hNi i j)
  have hm : ∀ i j, (1 - N) i j ∈ v.adicCompletionIntegers F := by
    intro i j; rw [Matrix.sub_apply]; exact sub_mem (h1m i j) (hNi i j)
  exact hGL ⟨1 + N, 1 - N, h1, h2⟩ hp hm w hw

theorem eq_multiple_of_standard_lattice : ∀ {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) {n : ℕ}
    (S : AddSubgroup (Fin n → v.adicCompletion F)),
    (∀ o ∈ v.adicCompletionIntegers F, ∀ w ∈ S, o • w ∈ S) →
    (∃ t : v.adicCompletion F, t ≠ 0 ∧ ∀ w : Fin n → v.adicCompletion F,
      (∀ i, w i ∈ v.adicCompletionIntegers F) → t • w ∈ S) →
    (∃ t : v.adicCompletion F, t ≠ 0 ∧ ∀ w ∈ S, ∀ i, t * w i ∈ v.adicCompletionIntegers F) →
    (∀ x : GL (Fin n) (v.adicCompletion F), (∀ i j, x.1 i j ∈ v.adicCompletionIntegers F) →
      (∀ i j, (x⁻¹).1 i j ∈ v.adicCompletionIntegers F) → ∀ w ∈ S, x.1.mulVec w ∈ S) →
    ∃ t : v.adicCompletion F, t ≠ 0 ∧ ∀ w, w ∈ S ↔ ∀ i, t * w i ∈ v.adicCompletionIntegers F := by
  intro F _ _ v n S hO ⟨tl, htl0, htl⟩ ⟨tu, htu0, htu⟩ hGL
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨1, one_ne_zero, fun w => ?_⟩
    have hw : w = 0 := Subsingleton.elim _ _
    subst hw
    exact ⟨fun _ i => i.elim0, fun _ => S.zero_mem⟩
  have memO : ∀ x : v.adicCompletion F, x ∈ v.adicCompletionIntegers F ↔ Valued.v x ≤ 1 :=
    fun x => Iff.rfl

  have hbd : ∀ w ∈ S, ∀ i, Valued.v (w i) ≤ (Valued.v tu)⁻¹ := by
    intro w hw i
    have h := (memO _).1 (htu w hw i)
    rw [map_mul] at h
    have hu : Valued.v tu ≠ 0 := (Valuation.ne_zero_iff _).2 htu0
    calc Valued.v (w i) = (Valued.v tu)⁻¹ * (Valued.v tu * Valued.v (w i)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hu, one_mul]
      _ ≤ (Valued.v tu)⁻¹ * 1 := by gcongr
      _ = (Valued.v tu)⁻¹ := mul_one _
  let P : ℤ → Prop := fun k => ∃ w ∈ S, ∃ i, Valued.v (w i) =
    ((Multiplicative.ofAdd k : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  obtain ⟨mB, hmB⟩ : ∃ m : Multiplicative ℤ, (m : WithZero (Multiplicative ℤ)) = (Valued.v tu)⁻¹ :=
    WithZero.ne_zero_iff_exists.1 (inv_ne_zero ((Valuation.ne_zero_iff _).2 htu0))
  have hPb : ∃ b : ℤ, ∀ z, P z → z ≤ b := by
    refine ⟨Multiplicative.toAdd mB, fun z ⟨w, hw, i, hz⟩ => ?_⟩
    have h := hbd w hw i
    rw [hz, ← hmB, WithZero.coe_le_coe] at h
    exact Multiplicative.ofAdd_le.1 (by simpa using h)
  let i₀' : Fin n := ⟨0, hn⟩
  have hPn : ∃ z, P z := by
    have hmem : tl • (fun _ => (1 : v.adicCompletion F)) ∈ S := htl _ (fun _ => one_mem _)
    obtain ⟨m, hm⟩ : ∃ m : Multiplicative ℤ, (m : WithZero (Multiplicative ℤ)) = Valued.v tl :=
      WithZero.ne_zero_iff_exists.1 ((Valuation.ne_zero_iff _).2 htl0)
    refine ⟨Multiplicative.toAdd m, _, hmem, i₀', ?_⟩
    simp [← hm]
  obtain ⟨lb, ⟨w₀, hw₀, i₀, hc⟩, hlb⟩ := Int.exists_greatest_of_bdd hPb hPn
  set c := w₀ i₀ with hcdef
  have hvc : Valued.v c ≠ 0 := by rw [hc]; exact WithZero.coe_ne_zero
  have hc0 : c ≠ 0 := fun h => hvc (by rw [h, map_zero])
  have hmax : ∀ w ∈ S, ∀ i, Valued.v (w i) ≤ Valued.v c := by
    intro w hw i
    by_cases h0 : w i = 0
    · rw [h0, map_zero]; exact zero_le'
    obtain ⟨m, hm⟩ : ∃ m : Multiplicative ℤ, (m : WithZero (Multiplicative ℤ)) = Valued.v (w i) :=
      WithZero.ne_zero_iff_exists.1 ((Valuation.ne_zero_iff _).2 h0)
    have hk := hlb (Multiplicative.toAdd m) ⟨w, hw, i, by simp [← hm]⟩
    rw [← hm, hc, WithZero.coe_le_coe]
    exact Multiplicative.toAdd_le.1 (by simpa using hk)
  have hint : ∀ w ∈ S, ∀ i, c⁻¹ * w i ∈ v.adicCompletionIntegers F := by
    intro w hw i
    rw [memO, map_mul, map_inv₀]
    calc (Valued.v c)⁻¹ * Valued.v (w i) ≤ (Valued.v c)⁻¹ * Valued.v c :=
          by gcongr; exact hmax w hw i
      _ = 1 := inv_mul_cancel₀ hvc

  have hsingle0 : Pi.single i₀ c ∈ S := by
    let N : Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
      fun a b => if b = i₀ ∧ a ≠ i₀ then -(c⁻¹ * w₀ a) else 0
    have hN : N * N = 0 := by
      funext a b
      simp only [Matrix.mul_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero (fun m _ => ?_)
      by_cases hm : m = i₀ <;> simp [N, hm]
    have hNi : ∀ i j, N i j ∈ v.adicCompletionIntegers F := by
      intro i j
      simp only [N]
      split_ifs
      · exact neg_mem (hint w₀ hw₀ i)
      · exact zero_mem _
    have h := one_add_mulVec_mem v S hGL N hN hNi hw₀
    convert h using 1
    funext a
    rw [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
    by_cases ha : a = i₀
    · subst ha
      simp [N, Matrix.mulVec, dotProduct, hcdef]
    · simp [N, Matrix.mulVec, dotProduct, ha, Pi.single_apply, ← hcdef]
      field_simp
      ring
  have hsingle : ∀ j, Pi.single j c ∈ S := by
    intro j
    by_cases hj : j = i₀
    · subst hj; exact hsingle0
    let N : Matrix (Fin n) (Fin n) (v.adicCompletion F) :=
      fun a b => if a = j ∧ b = i₀ then 1 else 0
    have hN : N * N = 0 := by
      funext a b
      simp only [Matrix.mul_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero (fun m _ => ?_)
      by_cases hm : m = i₀
      · subst hm; simp [N, Ne.symm hj]
      · simp [N, hm]
    have hNi : ∀ i k, N i k ∈ v.adicCompletionIntegers F := by
      intro i k
      simp only [N]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    have h := one_add_mulVec_mem v S hGL N hN hNi hsingle0
    have heq : (1 + N).mulVec (Pi.single i₀ c) = Pi.single i₀ c + Pi.single j c := by
      funext a
      rw [Matrix.add_mulVec, Matrix.one_mulVec]
      simp [N, Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [heq] at h
    simpa using S.sub_mem h hsingle0
  refine ⟨c⁻¹, inv_ne_zero hc0, fun w => ⟨fun hw i => hint w hw i, fun hw => ?_⟩⟩
  have hsum : w = ∑ j, (c⁻¹ * w j) • Pi.single j c := by
    funext a
    rw [Finset.sum_apply, Finset.sum_eq_single a]
    · simp only [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul]
      field_simp
    · intro b _ hb
      simp [Pi.single_apply, Ne.symm hb]
    · simp
  rw [hsum]
  exact S.sum_mem (fun j _ => hO _ (hw j) _ (hsingle j))

end GlobalTheory.LatticeBetweenMultiples
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceHyperspecialStableLatticeEqMultiple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.SplitLatMatch

open GlobalTheory.SplitHecke

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem half (V : HSp D) (e : Formalism.L2.Theta.AE D) (he : IsSplitIdem D e)
    (M : AddSubgroup (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)))
    (hM : ∀ a ∈ intAE D, ∀ z ∈ M, a • z ∈ M)
    (hf : ∀ z ∈ M, finPart D (e + cA D e) • z = z)
    (hb : ∃ N : ℕ, 0 < N ∧ (∀ y ∈ Formalism.L2.NTheta.LamHat V, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (finPart D (e + cA D e) • y) ∈ M) ∧ ∀ z ∈ M, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • z ∈ Formalism.L2.NTheta.LamHat V)
    (hK : ∀ g : GA D V, g ∈ KsphC V ∅ → SuppF V (e + cA D e) g → ∀ z ∈ M, (finMat D.sp.cm.sig V.gram g).mulVec z ∈ M) :
    ∃ a a' : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, finPart D e * a * a' = finPart D e ∧
      ∀ z, (finPart D e • z ∈ M ↔ (finPart D e * a) • z ∈ Formalism.L2.NTheta.LamHat V) := by
  obtain ⟨v, π, hπ⟩ := GlobalTheory.SplitChart.exists_chart e he
  obtain ⟨β, hβ⟩ := GlobalTheory.SplitFrame.exists_frame e v π he hπ V
  obtain ⟨φ, hφ⟩ := GlobalTheory.SplitFrame.exists_factor hπ
  have hπe : π e = 1 := GlobalTheory.SplitHomLattice.pi_idem he hπ
  have hpe : φ (finPart D e) = 1 := by rw [hφ]; exact hπe
  have hpp : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1]
  have hpO : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ hpp
  have hpq : finPart D e * finPart D (cA D e) = 0 := by rw [← map_mul, he.2.1, map_zero]
  have hφs : Function.Surjective φ := fun t => by
    obtain ⟨a, rfl⟩ := hπ.1 t
    exact ⟨finPart D a, hφ a⟩
  have hker : ∀ x, φ x = 0 → finPart D e * x = 0 := by
    intro x hx
    obtain ⟨a, rfl⟩ := GlobalTheory.SplitHecke.Stab.finPart_surj x
    rw [hφ] at hx
    rw [← map_mul, (hπ.2.1 a).1 hx, map_zero]
  let T : (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →+ (Fin V.rank → Fv D.host.F v) :=
    { toFun := fun z => (β⁻¹).1 *ᵥ fun k => φ (z k)
      map_zero' := by
        have : (fun k : Fin V.rank => φ ((0 : Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) k)) = 0 :=
          funext fun k => by rw [Pi.zero_apply, map_zero, Pi.zero_apply]
        simp only [this, Matrix.mulVec_zero]
      map_add' := by
        intro x y
        have : (fun k => φ ((x + y) k)) = (fun k => φ (x k)) + fun k => φ (y k) :=
          funext fun k => by rw [Pi.add_apply, map_add (f := _), Pi.add_apply]
        simp only [this, Matrix.mulVec_add] }
  have hT : ∀ z, T z = (β⁻¹).1 *ᵥ fun k => φ (z k) := fun z => rfl
  have hTs : ∀ (x : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) z, T (x • z) = φ x • T z := by
    intro x z
    rw [hT, hT, ← Matrix.mulVec_smul]
    congr 1
    funext k
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
  have hTp : ∀ z, T (finPart D e • z) = T z := by
    intro z; rw [hTs, hpe, one_smul]
  have hmem : ∀ z, finPart D e • z ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ i, T z i ∈ v.adicCompletionIntegers D.host.F := by
    intro z
    choose y hy using fun k => GlobalTheory.SplitHecke.Stab.finPart_surj (z k)
    have e1 : finPart D e • z = fun i => finPart D (e * y i) := funext fun i => by
      rw [Pi.smul_apply, smul_eq_mul, map_mul, hy]
    have e2 : (fun k => φ (z k)) = fun k => π (y k) := funext fun k => by rw [← hy, hφ]
    rw [e1, hβ y, hT, e2]
    exact forall_congr' fun i => isInt_Ov
  have hinj : ∀ z m, T z = T m → finPart D e • z = finPart D e • m := by
    intro z m h
    have h1 : (fun k => φ (z k)) = fun k => φ (m k) := by
      have := congrArg (fun u => β.1 *ᵥ u) h
      simpa only [hT, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec] using this
    funext k
    have h2 := hker (z k - m k) (by rw [map_sub, sub_eq_zero]; exact congrFun h1 k)
    rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    rw [mul_sub, sub_eq_zero] at h2
    exact h2
  let S : AddSubgroup (Fin V.rank → Fv D.host.F v) := M.map T
  have hS : ∀ z, T z ∈ S ↔ finPart D e • z ∈ M := by
    intro z
    constructor
    · rintro ⟨m, hm, h⟩
      rw [hinj z m h.symm]
      exact hM _ hpO m hm
    · intro h
      exact ⟨_, h, hTp z⟩
  obtain ⟨N, hN, hlo, hup⟩ := hb
  have : CharZero (Fv D.host.F v) := charZero_of_injective_algebraMap (algebraMap D.host.F (Fv D.host.F v)).injective
  have hN' : ((N : ℕ) : Fv D.host.F v) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hφN : φ ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) = (N : Fv D.host.F v) := map_natCast φ N
  have hf' : finPart D (e + cA D e) * finPart D e = finPart D e := by
    rw [map_add, add_mul, hpp, mul_comm (finPart D (cA D e)), hpq, add_zero]
  obtain ⟨t, ht, hSt⟩ := GlobalTheory.LatticeBetweenMultiples.eq_multiple_of_standard_lattice v S (by
      intro o ho w hw
      obtain ⟨m, hm, rfl⟩ := hw
      obtain ⟨a, ha⟩ := hπ.1 o
      refine ⟨finPart D (e * a) • m, hM _ ((hπ.2.2.2 a).2 (isInt_Ov.2 (ha ▸ ho))) m hm, ?_⟩
      rw [hTs, hφ, map_mul, hπe, one_mul, ha])
    (by
      refine ⟨N, hN', fun w hw => ?_⟩
      choose z hz using fun k => hφs ((β.1 *ᵥ w) k)
      have hTz : T z = w := by
        rw [hT, (funext hz : (fun k => φ (z k)) = β.1 *ᵥ w), Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, Matrix.one_mulVec]
      have hzL : finPart D e • z ∈ Formalism.L2.NTheta.LamHat V := (hmem z).2 (by rw [hTz]; exact hw)
      have h1 := hlo _ hzL
      rw [smul_smul (finPart D (e + cA D e)), hf'] at h1
      exact ⟨_, h1, by rw [hTs, hTp, hφN, hTz]⟩)
    (by
      refine ⟨N, hN', fun w hw i => ?_⟩
      obtain ⟨m, hm, rfl⟩ := hw
      have h2 : finPart D e • (((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • m) ∈ Formalism.L2.NTheta.LamHat V :=
        GlobalTheory.LatDual.smul_mem_lamHat V _ hpO _ (hup m hm)
      have h3 := (hmem _).1 h2 i
      rwa [hTs, hφN, Pi.smul_apply, smul_eq_mul] at h3)
    (by
      intro x hx1 hx2 w hw
      obtain ⟨m, hm, rfl⟩ := hw
      obtain ⟨g, hg, hgx⟩ := GlobalTheory.SplitOnto.exists_suppAt_rho_eq e v π he hπ V β x
      have hgK : g ∈ KsphC V ∅ := (GlobalTheory.SplitHecke.Stab.mem_KsphC_iff_gInt e v π he hπ V β hβ g hg).2 (by
        rw [hgx]
        exact ⟨fun i j => isInt_Ov.2 (hx1 i j), fun i j => isInt_Ov.2 (hx2 i j)⟩)
      refine ⟨_, hK g hgK hg m hm, ?_⟩
      have e1 : (fun k => φ ((finMat D.sp.cm.sig V.gram g *ᵥ m) k)) = (mt V g).map π *ᵥ fun k => φ (m k) := by
        funext k
        rw [RingHom.map_mulVec, GlobalTheory.SplitHecke.Stab.finMat_eq, Matrix.map_map]
        congr 2
        funext y
        exact hφ y
      rw [hT, hT, e1, ← hgx, rho_val, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc _ β.1, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one])
  obtain ⟨a, ha⟩ := hφs t
  obtain ⟨a', ha'⟩ := hφs t⁻¹
  refine ⟨a, a', ?_, fun z => ?_⟩
  · have := hker (a * a' - 1) (by rw [map_sub, map_mul, ha, ha', mul_inv_cancel₀ ht, map_one, sub_self])
    linear_combination this
  · rw [← hS, hSt, mul_smul, hmem, hTs, ha]
    simp only [Pi.smul_apply, smul_eq_mul]

end GlobalTheory.SplitLatMatch

namespace GlobalTheory.SplitLatMatch

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem lat_split : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : Formalism.L2.Theta.AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ (M : AddSubgroup (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))), (∀ a ∈ intAE D, ∀ z ∈ M, a • z ∈ M) → (∀ z ∈ M, finPart D (e + cA D e) • z = z) → (∃ N : ℕ, 0 < N ∧ (∀ y ∈ Formalism.L2.NTheta.LamHat V, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (finPart D (e + cA D e) • y) ∈ M) ∧ ∀ z ∈ M, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • z ∈ Formalism.L2.NTheta.LamHat V) → (∀ g : GA D V, g ∈ KsphC V ∅ → SuppF V (e + cA D e) g → ∀ z ∈ M, (finMat D.sp.cm.sig V.gram g).mulVec z ∈ M) → ∃ c : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), IsUnit c ∧ ∀ z, z ∈ M ↔ (finPart D (e + cA D e) • z = z ∧ c • z ∈ Formalism.L2.NTheta.LamHat V) := by
  intro D V P e hP M hMs hf hb hK
  have he : IsSplitIdem D e := hP.1
  have he' := GlobalTheory.SplitScalar.isSplitIdem_conj he
  obtain ⟨a, a', ha, hA⟩ := half V e he M hMs hf hb hK
  have hsum : cA D e + cA D (cA D e) = e + cA D e := by rw [cA_cA, add_comm]
  obtain ⟨b, b', hb', hB⟩ := half V (cA D e) he' M hMs (by rw [hsum]; exact hf) (by rw [hsum]; exact hb)
    (by rw [hsum]; exact hK)
  have hpp : finPart D e * finPart D e = finPart D e := by rw [← map_mul, he.1]
  have hqq : finPart D (cA D e) * finPart D (cA D e) = finPart D (cA D e) := by rw [← map_mul, he'.1]
  have hpq : finPart D e * finPart D (cA D e) = 0 := by rw [← map_mul, he.2.1, map_zero]
  have hpO : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ hpp
  have hqO : finPart D (cA D e) ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ hqq
  have hfe : finPart D (e + cA D e) = finPart D e + finPart D (cA D e) := map_add _ _ _
  rw [hfe] at hf
  rw [hfe]
  refine ⟨finPart D e * a + finPart D (cA D e) * b + (1 - (finPart D e + finPart D (cA D e))),
    isUnit_iff_exists_inv.2 ⟨finPart D e * a' + finPart D (cA D e) * b' + (1 - (finPart D e + finPart D (cA D e))),
      by linear_combination (a * a' - a - a' + 1) * hpp + (b * b' - b - b' + 1) * hqq +
        (a * b' + b * a' - a - a' - b - b' + 2) * hpq + ha + hb'⟩, fun z => ⟨fun hz => ⟨hf z hz, ?_⟩, fun ⟨hz, hc⟩ => ?_⟩⟩
  · have h1 := (hA z).1 (hMs _ hpO z hz)
    have h2 := (hB z).1 (hMs _ hqO z hz)
    have h3 := hf z hz
    have e1 : (finPart D e * a + finPart D (cA D e) * b + (1 - (finPart D e + finPart D (cA D e)))) • z =
        (finPart D e * a) • z + (finPart D (cA D e) * b) • z + (z - (finPart D e + finPart D (cA D e)) • z) := by
      funext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [e1, h3, sub_self, add_zero]
    exact add_mem h1 h2
  · have e2 : ∀ (p c : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), p * (finPart D e * a + finPart D (cA D e) * b + (1 - (finPart D e + finPart D (cA D e)))) = p * c →
        p • ((finPart D e * a + finPart D (cA D e) * b + (1 - (finPart D e + finPart D (cA D e)))) • z) = (p * c) • z := by
      intro p c h
      rw [smul_smul, h]
    have h1 : finPart D e • z ∈ M := (hA z).2 (by
      rw [← e2 (finPart D e) a (by linear_combination (a - 1) * hpp + (b - 1) * hpq)]
      exact GlobalTheory.LatDual.smul_mem_lamHat V _ hpO _ hc)
    have h2 : finPart D (cA D e) • z ∈ M := (hB z).2 (by
      rw [← e2 (finPart D (cA D e)) b (by linear_combination (b - 1) * hqq + (a - 1) * hpq)]
      exact GlobalTheory.LatDual.smul_mem_lamHat V _ hqO _ hc)
    rw [← hz, add_smul]
    exact add_mem h1 h2

end GlobalTheory.SplitLatMatch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceHyperspecialStableLatticeEqMultipleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_hyperspecialStable_lattice_eq_multiple : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : Formalism.L2.Theta.AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ (M : AddSubgroup (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))), (∀ a ∈ intAE D, ∀ z ∈ M, a • z ∈ M) → (∀ z ∈ M, finPart D (e + cA D e) • z = z) → (∃ N : ℕ, 0 < N ∧ (∀ y ∈ Formalism.L2.NTheta.LamHat V, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (finPart D (e + cA D e) • y) ∈ M) ∧ ∀ z ∈ M, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • z ∈ Formalism.L2.NTheta.LamHat V) → (∀ g : GA D V, g ∈ KsphC V ∅ → SuppF V (e + cA D e) g → ∀ z ∈ M, (finMat D.sp.cm.sig V.gram g).mulVec z ∈ M) → ∃ c : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), IsUnit c ∧ ∀ z, z ∈ M ↔ (finPart D (e + cA D e) • z = z ∧ c • z ∈ Formalism.L2.NTheta.LamHat V) := by
  first | exact @GlobalTheory.SplitLatMatch.lat_split | exact GlobalTheory.SplitLatMatch.lat_split | (intros; apply GlobalTheory.SplitLatMatch.lat_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceHyperspecialStableLatticeEqMultiple
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderCompletionSurjectiveFromIntegralAdeles
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderCompletionSurjectiveFromIntegralAdeles
open IsDedekindDomain NumberField
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.OrdLift

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem one_mem_intAf : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) ∈ Formalism.MainNotions.StandardLattice.intAf F := fun v => by
  rw [map_one]; exact one_mem _

theorem mul_mem_intA {x y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E} (hx : x ∈ GlobalTheory.PlaceComp.intA F E)
    (hy : y ∈ GlobalTheory.PlaceComp.intA F E) : x * y ∈ GlobalTheory.PlaceComp.intA F E :=
  by apply _root_.UpperTheory.Reformulated.B.Uc13.mul_mem_intA <;> assumption

end GlobalTheory.OrdLift

theorem GlobalTheory.OrdLift.ordAt_lift : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E),
    a ∈ GlobalTheory.PlaceComp.ordAt E v → ∃ t ∈ GlobalTheory.PlaceComp.intA F E, GlobalTheory.PlaceComp.evF E v t = a := by
  intro F E _ _ _ _ _ v a ha
  induction ha using Subring.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, x, rfl⟩ := hy
    refine ⟨Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v b ⊗ₜ[F] (x : E),
      AddSubgroup.subset_closure ⟨_, GlobalTheory.SplitIdem.singleV_mem_intAf F v ⟨b, hb⟩, x, rfl⟩, ?_⟩
    show Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.singleV F v b) ⊗ₜ[F] (x : E) = _
    rw [GlobalTheory.SplitIdem.evalV_singleV_same]
  | zero => exact ⟨0, zero_mem _, map_zero _⟩
  | one =>
    refine ⟨1, AddSubgroup.subset_closure ⟨1, GlobalTheory.OrdLift.one_mem_intAf F, 1, ?_⟩, map_one _⟩
    simp [Algebra.TensorProduct.one_def]
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨s + t, add_mem hs ht, map_add _ _ _⟩
  | neg x _ hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    exact ⟨-s, neg_mem hs, map_neg _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    exact ⟨s * t, GlobalTheory.OrdLift.mul_mem_intA F E hs ht, map_mul _ _ _⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderCompletionSurjectiveFromIntegralAdelesStatement
open IsDedekindDomain NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localOrderCompletion_surjective_from_integralAdeles : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E), a ∈ GlobalTheory.PlaceComp.ordAt E v → ∃ t ∈ GlobalTheory.PlaceComp.intA F E, GlobalTheory.PlaceComp.evF E v t = a := by
  first | exact @GlobalTheory.OrdLift.ordAt_lift | exact GlobalTheory.OrdLift.ordAt_lift | (intros; apply GlobalTheory.OrdLift.ordAt_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceHyperspecialStableLatticeEqMultiple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

noncomputable section

namespace GlobalTheory.InertLatMult

open GlobalTheory.PlaceComp GlobalTheory.SelfDualGenus

variable {D : D7} {n : ℕ}

def coord (v : HeightOneSpectrum (𝓞 D.host.F)) {K : Type} [CommRing K]
    (h : GL (Fin n) (Fv D.host.F v ⊗[D.host.F] D.host.E)) (ψ : (Fv D.host.F v ⊗[D.host.F] D.host.E) →+* K) :
    (Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) →+ (Fin n → K) where
  toFun z i := ψ (((h⁻¹).1 *ᵥ fun j => evF D.host.E v (z j)) i)
  map_zero' := by
    funext i
    show ψ (((h⁻¹).1 *ᵥ fun j => evF D.host.E v ((0 : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) j)) i) = 0
    have : (fun j => evF D.host.E v ((0 : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) j)) = 0 :=
      funext fun j => map_zero _
    rw [this, Matrix.mulVec_zero, Pi.zero_apply, map_zero]
  map_add' a b := by
    funext i
    show ψ (((h⁻¹).1 *ᵥ fun j => evF D.host.E v ((a + b) j)) i) =
      ψ (((h⁻¹).1 *ᵥ fun j => evF D.host.E v (a j)) i) + ψ (((h⁻¹).1 *ᵥ fun j => evF D.host.E v (b j)) i)
    have : (fun j => evF D.host.E v ((a + b) j)) = (fun j => evF D.host.E v (a j)) + fun j => evF D.host.E v (b j) :=
      funext fun j => map_add _ _ _
    rw [this, Matrix.mulVec_add, Pi.add_apply, map_add (f := _)]

section Coord

variable (v : HeightOneSpectrum (𝓞 D.host.F)) {K : Type} [CommRing K]
    (h : GL (Fin n) (Fv D.host.F v ⊗[D.host.F] D.host.E)) (ψ : (Fv D.host.F v ⊗[D.host.F] D.host.E) →+* K)

theorem coord_apply (z : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) (i : Fin n) :
    coord v h ψ z i = ψ (((h⁻¹).1 *ᵥ fun j => evF D.host.E v (z j)) i) := rfl

theorem coord_mul (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)
    (z : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    coord v h ψ (fun i => t * z i) = fun i => ψ (evF D.host.E v t) * coord v h ψ z i := by
  funext i
  have e : (fun j => evF D.host.E v (t * z j)) = evF D.host.E v t • fun j => evF D.host.E v (z j) := by
    funext j
    simp [map_mul]
  rw [coord_apply, coord_apply, e, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, map_mul]

theorem coord_mulVec (A : Matrix (Fin n) (Fin n) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))
    (z : Fin n → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :
    coord v h ψ (A *ᵥ z) = ((h⁻¹).1 * A.map (evF D.host.E v) * h.1).map ψ *ᵥ coord v h ψ z := by
  funext i
  have e1 : (fun j => evF D.host.E v ((A *ᵥ z) j)) = A.map (evF D.host.E v) *ᵥ fun j => evF D.host.E v (z j) :=
    funext fun j => RingHom.map_mulVec _ _ _ j
  have e2 : (h⁻¹).1 *ᵥ (A.map (evF D.host.E v) *ᵥ fun j => evF D.host.E v (z j)) =
      ((h⁻¹).1 * A.map (evF D.host.E v) * h.1) *ᵥ ((h⁻¹).1 *ᵥ fun j => evF D.host.E v (z j)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [coord_apply, e1, e2, RingHom.map_mulVec]
  rfl

end Coord

end GlobalTheory.InertLatMult



open GlobalTheory.PlaceComp GlobalTheory.SelfDualGenus GlobalTheory.InertLatMult in
theorem GlobalTheory.InertLatMult.lattice_eq_mult : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : Formalism.L2.Theta.AE D), (∃ v ε, IsPlaceIdem D v ε ∧ e = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε) → (∀ x : 𝓞 D.host.E, x ≠ 0 → (x ∈ P.asIdeal ↔ finPart D (e * incA D ((x : D.host.E)⁻¹)) ∉ intAE D)) → ∀ (M : AddSubgroup (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))), (∀ a ∈ intAE D, ∀ z ∈ M, a • z ∈ M) → (∀ z ∈ M, finPart D (e) • z = z) → (∃ N : ℕ, 0 < N ∧ (∀ y ∈ Formalism.L2.NTheta.LamHat V, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (finPart D (e) • y) ∈ M) ∧ ∀ z ∈ M, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • z ∈ Formalism.L2.NTheta.LamHat V) → (∀ g : GA D V, g ∈ KsphC V ∅ → SuppF V (e) g → ∀ z ∈ M, (finMat D.sp.cm.sig V.gram g).mulVec z ∈ M) → ∃ c : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), IsUnit c ∧ ∀ z, z ∈ M ↔ (finPart D (e) • z = z ∧ c • z ∈ Formalism.L2.NTheta.LamHat V) := by
  intro D V P e he hP M hMa hMe hN hG
  obtain ⟨v, ε, ⟨α, rfl, a1, a2⟩, rfl⟩ := he
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hI := GlobalTheory.PlaceComp.isIdemOf_algebraMap (E := D.host.E) a1 a2
  obtain ⟨x0, y, hy, hy1, hy2⟩ := GlobalTheory.SphLabelOps.exists_real_unif D P
  have hin := GlobalTheory.InertDoubleCoset.inert_of_idem (E := D.host.E) hI hP ⟨x0, y, hy, hy1, hy2⟩
  haveI := GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm
  obtain ⟨σ, π, hσE, hσσ, hσv, hσx, hσπ, hπ⟩ := GlobalTheory.T.exists_complexConj_isometry_inert_completion D.host.E v P hin
  obtain ⟨ψ, hψE, hψσ, hψO⟩ := GlobalTheory.T.exists_ringEquiv_tensor_inert_adicCompletion D.host.E v P hin σ hσE hσv
  obtain ⟨h, hfr, hon⟩ := GlobalTheory.PlaceComp.exists_orthonormal D.sp.cm V v
  obtain ⟨s1, -, s3⟩ := GlobalTheory.T.adelicUnitary_supportedAtFinitePlace_eq_localUnitary _ D.host.E D.sp.cm V v _ hI
  set e : Formalism.L2.Theta.AE D := algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (pairA D.host.F 0 α) with he_def
  set fe := finPart D e with hfe_def
  let ψ' : (Fv D.host.F v ⊗[D.host.F] D.host.E) →+* P.adicCompletion D.host.E := ψ
  let X := coord (D := D) (n := V.rank) v h ψ'
  have hfe1 : evF D.host.E v fe = 1 := hI.2.1
  have hfe0 : ∀ w, w ≠ v → evF D.host.E w fe = 0 := hI.2.2
  have hfe : fe * fe = fe := evF_ext fun w => by
    by_cases hw : w = v
    · subst hw; rw [map_mul, hfe1, mul_one]
    · rw [map_mul, hfe0 w hw, mul_zero]

  have supp0 : ∀ z : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      (∀ i, fe * z i = z i) → ∀ w, w ≠ v → ∀ i, evF D.host.E w (z i) = 0 := fun z hz w hw i => by
    rw [← hz i, map_mul, hfe0 w hw, zero_mul]
  have hinj : ∀ z z' : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      (∀ i, fe * z i = z i) → (∀ i, fe * z' i = z' i) → X z = X z' → z = z' := by
    intro z z' hz hz' e0
    have e1 : ((h⁻¹).1 *ᵥ fun j => evF D.host.E v (z j)) = ((h⁻¹).1 *ᵥ fun j => evF D.host.E v (z' j)) :=
      funext fun i => ψ.injective (congrFun e0 i)
    have e2 : (fun j => evF D.host.E v (z j)) = (fun j => evF D.host.E v (z' j)) := by
      have := congrArg (fun w => h.1 *ᵥ w) e1
      simpa only [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec] using this
    funext i
    refine evF_ext fun w => ?_
    by_cases hw : w = v
    · subst hw; exact congrFun e2 i
    · rw [supp0 z hz w hw i, supp0 z' hz' w hw i]
  have hsurj : ∀ w : Fin V.rank → P.adicCompletion D.host.E, ∃ z, (∀ i, fe * z i = z i) ∧ X z = w := by
    intro w
    refine ⟨fun j => sgT D.host.E v ((h.1 *ᵥ fun i => ψ.symm (w i)) j), fun i => ?_, ?_⟩
    · refine evF_ext fun u => ?_
      by_cases hu : u = v
      · subst hu; rw [map_mul, hfe1, one_mul]
      · rw [map_mul, hfe0 u hu, zero_mul, evF_sgT_ne hu]
    · funext i
      show ψ (((h⁻¹).1 *ᵥ fun j => evF D.host.E v (sgT D.host.E v ((h.1 *ᵥ fun i => ψ.symm (w i)) j))) i) = w i
      simp only [evF_sgT_self]
      rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      exact ψ.apply_symm_apply _
  have hmem : ∀ z : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      (∀ i, fe * z i = z i) → (z ∈ Formalism.L2.NTheta.LamHat V ↔ ∀ i, Valued.v (X z i) ≤ 1) := by
    intro z hz
    show z ∈ GlobalTheory.PlaceComp.lamHat D.host.F V ↔ _
    rw [mem_lamHat_iff]
    constructor
    · intro hl i
      have := ((hfr _).1 (hl v)) i
      rw [mem_ordAt_iff, hψO] at this
      exact this
    · intro hl w
      by_cases hw : w = v
      · subst hw
        refine (hfr _).2 fun i => ?_
        rw [mem_ordAt_iff, hψO]
        exact hl i
      · have : (fun i => evF D.host.E w (z i)) = 0 := funext fun i => supp0 z hz w hw i
        rw [this]
        exact zero_mem _

  have hback : ∀ x : GL (Fin V.rank) (P.adicCompletion D.host.E),
      Formalism.UG.bc ψ' (Formalism.UG.bc (ψ.symm : P.adicCompletion D.host.E →+* LocAlg v) x) = x :=
    fun x => Units.ext (Matrix.ext fun i j => ψ.apply_symm_apply _)
  have hO : ∀ z, z ∈ ordAt D.host.E v ↔ ψ' z ∈ Formalism.UG.Ov D.host.E P := fun z =>
    (mem_ordAt_iff v z).trans ((hψO z).trans (P.mem_adicCompletionIntegers (K := D.host.E)).symm)
  have hlift : ∀ U : GL (Fin V.rank) (P.adicCompletion D.host.E), U ∈ Formalism.UG.UJ σ 1 →
      (∀ i j, Valued.v (U.1 i j) ≤ 1) → (∀ i j, Valued.v ((U⁻¹).1 i j) ≤ 1) →
      ∃ g : GA D V, g ∈ KsphC V ∅ ∧ SuppF V e g ∧ ∀ z, X (finMat D.sp.cm.sig V.gram g *ᵥ z) = U.1 *ᵥ X z := by
    intro U hU i1 i2
    have h1 := GlobalTheory.InertDoubleCoset.bc_mem_UJ_one (σ' := locConj v) (ψ.symm : P.adicCompletion D.host.E →+* LocAlg v)
      (fun z => ψ.injective (by
        rw [hψσ]
        exact (ψ.apply_symm_apply _).trans (congrArg σ (ψ.apply_symm_apply _).symm))) hU
    obtain ⟨k, hk, ek⟩ := s3 _ (GlobalTheory.InertDoubleCoset.conj_mem_UJ _ (GlobalTheory.InertDoubleCoset.inv_frame _ hon) h1)
    have hk1 := (s1 k).1 hk
    have hconj : h⁻¹ * locMat D.sp.cm V v k * h = Formalism.UG.bc (ψ.symm : P.adicCompletion D.host.E →+* LocAlg v) U := by
      rw [ek]; group
    have hst : Stab D.sp.cm V k := by
      rw [GlobalTheory.T.stabilises_completedLattice_iff_localMatrix_integral _ D.host.E D.sp.cm V v h hfr k hk1.2, hconj,
        GlobalTheory.InertDoubleCoset.bc_mem_range_iff ψ' hO, hback, GlobalTheory.InertDoubleCoset.mem_range_iff]
      refine ⟨fun i j => (P.mem_adicCompletionIntegers (K := D.host.E)).2 (i1 i j),
        fun i j => (P.mem_adicCompletionIntegers (K := D.host.E)).2 (i2 i j)⟩
    refine ⟨k, (GlobalTheory.InertDoubleCoset.mem_KsphC_iff V k).2 ⟨hk1.1, hst⟩, hk, fun z => ?_⟩
    rw [coord_mulVec]
    congr 1
    have : (h⁻¹).1 * (finMat D.sp.cm.sig V.gram k).map (evF D.host.E v) * h.1 =
        (Formalism.UG.bc (ψ.symm : P.adicCompletion D.host.E →+* LocAlg v) U).1 := by
      rw [← hconj, ← locMat_val]; rfl
    rw [this]
    exact congrArg Units.val (hback U)

  have hsupM : ∀ z ∈ M, ∀ i, fe * z i = z i := fun z hz i => congrFun (hMe z hz) i
  have hint : ∀ a : P.adicCompletion D.host.E, Valued.v a ≤ 1 → ∃ t ∈ intAE D, ψ' (evF D.host.E v t) = a := by
    intro a ha
    have h0 : ψ.symm a ∈ ordAt D.host.E v := (mem_ordAt_iff v _).2 ((hψO _).2 (by rwa [ψ.apply_symm_apply]))
    obtain ⟨t, ht, et⟩ := GlobalTheory.T.localOrderCompletion_surjective_from_integralAdeles D.host.F D.host.E v _ h0
    exact ⟨t, ht, by show ψ (evF D.host.E v t) = a; rw [et]; exact ψ.apply_symm_apply a⟩
  have hinc : ∀ x : D.host.E, ψ' (evF D.host.E v (finPart D (incA D x))) = algebraMap D.host.E _ x := fun x => by
    show ψ _ = _
    rw [show finPart D (incA D x) = finP D.host.F D.host.E (inclR (AF D.host.F) x) from rfl, evF_finP_incl]
    exact hψE x
  let L : AddSubgroup (Fin V.rank → P.adicCompletion D.host.E) := M.map X
  have hLmem : ∀ z, (∀ i, fe * z i = z i) → (X z ∈ L ↔ z ∈ M) := fun z hz =>
    ⟨fun ⟨z', hz', e0⟩ => (hinj z' z (hsupM z' hz') hz e0) ▸ hz', fun hzM => ⟨z, hzM, rfl⟩⟩
  have hsmul : ∀ (t : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) (z : Fin V.rank → _),
      (∀ i, fe * z i = z i) → ∀ i, fe * (t * z i) = t * z i := fun t z hz i => by
    rw [mul_left_comm, hz i]
  obtain ⟨N, hNpos, hN1, hN2⟩ := hN
  have hNc : ψ' (evF D.host.E v ((N : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) =
      ((N : ℕ) : P.adicCompletion D.host.E) := by
    rw [map_natCast, map_natCast]
  have hN0 : ((N : ℕ) : P.adicCompletion D.host.E) ≠ 0 := by
    rw [← map_natCast (algebraMap D.host.E (P.adicCompletion D.host.E))]
    exact (_root_.map_ne_zero _).2 (Nat.cast_ne_zero.2 hNpos.ne')
  have hyv : Valued.v (algebraMap D.host.E (P.adicCompletion D.host.E) (y : D.host.E)) = WithZero.exp (-1 : ℤ) := by
    rw [GlobalTheory.Idele.valued_algebraMap, ← GlobalTheory.UnramCompletion.intValuation_eq_of_notMem_sq P hy1 hy2]
    exact HeightOneSpectrum.valuation_of_algebraMap P y
  obtain ⟨k, hk⟩ := GlobalTheory.T.stable_lattice_eq_zpow_std_inert_completion D.host.E P σ hσσ hσv hσx _ hyv V.rank L _ hN0
    (by
      rintro a ha _ ⟨z, hz, rfl⟩
      obtain ⟨t, ht, et⟩ := hint a ha
      refine ⟨fun i => t * z i, hMa t ht z hz, ?_⟩
      show X (fun i => t * z i) = a • X z
      rw [coord_mul]
      funext i
      rw [et]; rfl)
    (by
      intro w hw
      obtain ⟨z, hz, rfl⟩ := hsurj w
      have h1 := hN1 z ((hmem z hz).2 hw)
      have h2 : (finPart D e • z) = z := funext hz
      rw [h2] at h1
      refine ⟨_, h1, ?_⟩
      show X (fun i => ((N : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) * z i) = _
      rw [coord_mul, hNc]
      rfl)
    (by
      rintro _ ⟨z, hz, rfl⟩ i
      have h1 := (hmem _ (hsmul _ z (hsupM z hz))).1 (hN2 z hz) i
      have h2 : X (fun i => ((N : ℕ) : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) * z i) i =
          ((N : ℕ) : P.adicCompletion D.host.E) * X z i := by
        rw [coord_mul, hNc]
      rw [← h2]
      exact h1)
    (by
      rintro U hU i1 i2 _ ⟨z, hz, rfl⟩
      obtain ⟨g, hgK, hgS, hgX⟩ := hlift U hU i1 i2
      exact ⟨_, hG g hgK hgS z hz, hgX z⟩)
  have hy0 : (y : D.host.E) ≠ 0 := GlobalTheory.SphLabelOps.unif_ne_zero (D := D) hy2
  set a := finPart D (incA D ((y : D.host.E) ^ k)) with ha_def
  set b := finPart D (incA D ((y : D.host.E) ^ (-k))) with hb_def
  have hab : a * b = 1 := by
    rw [ha_def, hb_def, ← map_mul, ← map_mul, ← zpow_add₀ hy0, add_neg_cancel, zpow_zero, map_one, map_one]
  have hc : ∀ z : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, (∀ i, fe * z i = z i) →
      ((a * fe + (1 - fe)) • z) = fun i => a * z i := fun z hz => funext fun i => by
    show (a * fe + (1 - fe)) * z i = a * z i
    calc (a * fe + (1 - fe)) * z i = a * (fe * z i) + (z i - fe * z i) := by ring
      _ = a * z i := by rw [hz i, sub_self, add_zero]
  have hXa : ∀ z : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E, ∀ i,
      X (fun i => a * z i) i = algebraMap D.host.E (P.adicCompletion D.host.E) (y : D.host.E) ^ k * X z i :=
    fun z i => by rw [coord_mul, ha_def, hinc, map_zpow₀]
  refine ⟨a * fe + (1 - fe), ⟨⟨a * fe + (1 - fe), b * fe + (1 - fe), ?_, ?_⟩, rfl⟩, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · linear_combination (a * b - a - b + 1) * hfe + fe * hab
  · linear_combination (a * b - a - b + 1) * hfe + fe * hab
  · refine ⟨hMe z hz, ?_⟩
    rw [hc z (hsupM z hz), hmem _ (hsmul _ z (hsupM z hz))]
    intro i
    rw [hXa]
    exact (hk (X z)).1 ⟨z, hz, rfl⟩ i
  · rintro ⟨hz1, hz2⟩
    have hs : ∀ i, fe * z i = z i := fun i => congrFun hz1 i
    rw [hc z hs, hmem _ (hsmul _ z hs)] at hz2
    exact (hLmem z hs).1 ((hk (X z)).2 fun i => by rw [← hXa]; exact hz2 i)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceHyperspecialStableLatticeEqMultipleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_hyperspecialStable_lattice_eq_multiple : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : Formalism.L2.Theta.AE D), (∃ v ε, IsPlaceIdem D v ε ∧ e = algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) ε) → (∀ x : 𝓞 D.host.E, x ≠ 0 → (x ∈ P.asIdeal ↔ finPart D (e * incA D ((x : D.host.E)⁻¹)) ∉ intAE D)) → ∀ (M : AddSubgroup (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E))), (∀ a ∈ intAE D, ∀ z ∈ M, a • z ∈ M) → (∀ z ∈ M, finPart D (e) • z = z) → (∃ N : ℕ, 0 < N ∧ (∀ y ∈ Formalism.L2.NTheta.LamHat V, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (finPart D (e) • y) ∈ M) ∧ ∀ z ∈ M, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • z ∈ Formalism.L2.NTheta.LamHat V) → (∀ g : GA D V, g ∈ KsphC V ∅ → SuppF V (e) g → ∀ z ∈ M, (finMat D.sp.cm.sig V.gram g).mulVec z ∈ M) → ∃ c : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), IsUnit c ∧ ∀ z, z ∈ M ↔ (finPart D (e) • z = z ∧ c • z ∈ Formalism.L2.NTheta.LamHat V) := by
  first | exact @GlobalTheory.InertLatMult.lattice_eq_mult | exact GlobalTheory.InertLatMult.lattice_eq_mult | (intros; apply GlobalTheory.InertLatMult.lattice_eq_mult <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardFramesMatchCompletedLatticesAtPrime
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI

namespace GlobalTheory.LatMatch

section Abstract
variable {R : Type} [CommRing R] [Nontrivial R]

theorem card_eq_of_inv {a b : ℕ} (A : Matrix (Fin a) (Fin b) R) (B : Matrix (Fin b) (Fin a) R)
    (h1 : A * B = 1) (h2 : B * A = 1) : a = b := by
  let e : (Fin b → R) ≃ₗ[R] (Fin a → R) := LinearEquiv.ofLinear (Matrix.toLin' A) (Matrix.toLin' B)
    (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
  have := e.finrank_eq
  simpa using this.symm

end Abstract

theorem nontrivial_R (D : D7) : Nontrivial (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := by
  haveI : Nontrivial (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 D.host.F)
    exact (Formalism.UG.evalV D.host.F ⟨P, hP.isPrime,
      Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField D.host.F)⟩).toRingHom.domain_nontrivial
  exact (Algebra.TensorProduct.includeLeft_injective (R := D.host.F) (S := D.host.F)
    (A := Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (B := D.host.E) (algebraMap D.host.F D.host.E).injective).nontrivial


set_option maxHeartbeats 4000000 in
theorem frames_match_lattices : ∀ {D : D7} {V V' : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (Q : principalLevelFrame.RowPsi V n) (Q' : principalLevelFrame.RowPsi V' n), StdPsi hF Q → StdPsi hF Q' → ∀ (P : Pl D.host.E) (e f : Formalism.L2.Theta.AE D), IsPrimeIdem P e f → V'.rank = V.rank ∧ ∃ (J : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (J' : Matrix (Fin V.rank) (Fin V'.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), J * J' = 1 ∧ J' * J = 1 ∧ (∀ κ, finMat D.sp.cm.sig V'.gram (Q'.ψ κ) * J = J * finMat D.sp.cm.sig V.gram (Q.ψ κ)) ∧ ∀ y, finPart D f • y ∈ Formalism.L2.NTheta.LamHat V ↔ finPart D f • J.mulVec y ∈ Formalism.L2.NTheta.LamHat V' := by
  intro D V V' n hF Q Q' hQ hQ' P e f hP
  haveI := nontrivial_R D
  obtain ⟨⟨β, β', hb1, hb2, hK⟩, hU⟩ := hQ
  obtain ⟨⟨γ, γ', hc1, hc2, hK'⟩, hU'⟩ := hQ'
  have hr : V.rank = n := card_eq_of_inv β β' hb1 hb2
  have hr' : V'.rank = n := card_eq_of_inv γ γ' hc1 hc2
  refine ⟨hr'.trans hr.symm, ?_⟩
  let X : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := γ * β'
  let X' : Matrix (Fin V.rank) (Fin V'.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := β * γ'
  have hX1 : X * X' = 1 := by
    show γ * β' * (β * γ') = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc β' β γ', hb2, Matrix.one_mul, hc1]
  have hX2 : X' * X = 1 := by
    show β * γ' * (γ * β') = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc γ' γ β', hc2, Matrix.one_mul, hb1]
  have hconj : ∀ κ, finMat D.sp.cm.sig V'.gram (Q'.ψ κ) * X = X * finMat D.sp.cm.sig V.gram (Q.ψ κ) := by
    intro κ
    rw [hK' κ, hK κ]
    show _ * (γ * β') = γ * β' * _
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc γ' γ β', hc2, Matrix.one_mul, ← Matrix.mul_assoc β' β, hb2, Matrix.one_mul]
  obtain ⟨-, -, T3, -⟩ := GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V
  have hff : f * f = f := (T3 P e f hP).1
  set φ := finPart D f with hφdef
  have hφ : φ * φ = φ := by rw [hφdef, ← map_mul, hff]
  have hφint : φ ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D φ hφ
  have sm : ∀ (W : HSp D), ∀ a ∈ intAE D, ∀ y ∈ Formalism.L2.NTheta.LamHat W, a • y ∈ Formalism.L2.NTheta.LamHat W :=
    fun W a ha y hy => GlobalTheory.LatDual.smul_mem_lamHat W a ha y hy
  have nsm : ∀ (W : HSp D) (N : ℕ), ∀ y ∈ Formalism.L2.NTheta.LamHat W, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • y ∈ Formalism.L2.NTheta.LamHat W := by
    intro W N y hy
    rw [Nat.cast_smul_eq_nsmul]
    exact AddSubgroup.nsmul_mem _ hy N
  obtain ⟨N1, hN1, hB1⟩ := GlobalTheory.T.exists_nat_smul_matrix_mulVec_completedSelfDual V V' X
  obtain ⟨N2, hN2, hB2⟩ := GlobalTheory.T.exists_nat_smul_matrix_mulVec_completedSelfDual V' V X'
  let hom : (Fin V.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →+ (Fin V'.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) :=
    (DistribSMul.toAddMonoidHom _ φ).comp (Matrix.mulVecLin X).toAddMonoidHom
  have hhom : ∀ y, hom y = φ • X.mulVec y := fun y => rfl
  let M : AddSubgroup (Fin V'.rank → (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) := (Formalism.L2.NTheta.LamHat V).map hom
  have hM : ∀ z, z ∈ M ↔ ∃ y ∈ Formalism.L2.NTheta.LamHat V, φ • X.mulVec y = z := fun z => by
    simp only [M, AddSubgroup.mem_map, hhom]
  have c1 : ∀ a ∈ intAE D, ∀ z ∈ M, a • z ∈ M := by
    intro a ha z hz
    obtain ⟨y, hy, rfl⟩ := (hM z).1 hz
    refine (hM _).2 ⟨a • y, sm V a ha y hy, ?_⟩
    rw [Matrix.mulVec_smul, smul_comm]
  have c2 : ∀ z ∈ M, φ • z = z := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := (hM z).1 hz
    rw [smul_smul, hφ]
  have c3 : ∃ N : ℕ, 0 < N ∧ (∀ y ∈ Formalism.L2.NTheta.LamHat V', ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (φ • y) ∈ M) ∧
      ∀ z ∈ M, ((N : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • z ∈ Formalism.L2.NTheta.LamHat V' := by
    refine ⟨N1 * N2, Nat.mul_pos hN1 hN2, fun y hy => ?_, fun z hz => ?_⟩
    · refine (hM _).2 ⟨((N1 : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (((N2 : ℕ) : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X'.mulVec y), nsm V N1 _ (hB2 y hy), ?_⟩
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hX1, Matrix.one_mulVec]
      simp only [smul_smul, Nat.cast_mul]
      congr 1
      ring
    · obtain ⟨y, hy, rfl⟩ := (hM z).1 hz
      have h1 := nsm V' N2 _ (sm V' φ hφint _ (hB1 y hy))
      convert h1 using 1
      simp only [Matrix.mulVec_smul, smul_smul, Nat.cast_mul]
      congr 1
      ring
  have c4 : ∀ g : GA D V', g ∈ KsphC V' ∅ → SuppF V' f g → ∀ z ∈ M,
      (finMat D.sp.cm.sig V'.gram g).mulVec z ∈ M := by
    intro g hg _ z hz
    obtain ⟨y, hy, rfl⟩ := (hM z).1 hz
    obtain ⟨κ, hκ⟩ := Q'.onto g hg.1
    have hκU : κ ∈ ReciprocityTheory.Aut.Umax D.host.E n := (hU' κ).2 (by rw [hκ]; exact hg)
    have hk : Q.ψ κ ∈ KsphC V ∅ := (hU κ).1 hκU
    refine (hM _).2 ⟨(finMat D.sp.cm.sig V.gram (Q.ψ κ)).mulVec y, (hk.2.1 y).1 hy, ?_⟩
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hconj κ, hκ]
  have hcore : ∃ c : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E), IsUnit c ∧ ∀ z, z ∈ M ↔ (φ • z = z ∧ c • z ∈ Formalism.L2.NTheta.LamHat V') := by
    rcases hP with ⟨hI, hfe⟩ | ⟨hfe, hpl, hint⟩
    · have h := GlobalTheory.T.splitPlace_hyperspecialStable_lattice_eq_multiple V' P e hI M
      rw [← hfe] at h
      exact h c1 c2 c3 c4
    · rw [← hfe] at hpl hint
      exact GlobalTheory.T.inertPlace_hyperspecialStable_lattice_eq_multiple V' P f hpl hint M c1 c2 c3 c4
  obtain ⟨c, ⟨u, rfl⟩, hcM⟩ := hcore
  refine ⟨(u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X, (↑u⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X', ?_, ?_, ?_, ?_⟩
  · rw [Matrix.smul_mul (u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) X, Matrix.mul_smul X (↑u⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) X', smul_smul, hX1, Units.mul_inv, one_smul]
  · rw [Matrix.smul_mul (↑u⁻¹ : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) X', Matrix.mul_smul X' (u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) X, smul_smul, hX2, Units.inv_mul, one_smul]
  · intro κ
    rw [Matrix.mul_smul, Matrix.smul_mul, hconj κ]
  · intro y
    have e1 : φ • (((u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • X).mulVec y) = (u : (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) • (φ • X.mulVec y) := by
      rw [Matrix.smul_mulVec, smul_comm]
    rw [e1]
    constructor
    · intro h
      have hz : φ • X.mulVec y ∈ M := (hM _).2 ⟨φ • y, h, by rw [Matrix.mulVec_smul, smul_smul, hφ]⟩
      exact ((hcM _).1 hz).2
    · intro h
      have hz : φ • X.mulVec y ∈ M := (hcM _).2 ⟨by rw [smul_smul, hφ], h⟩
      obtain ⟨y', hy', hyy⟩ := (hM _).1 hz
      have := congrArg X'.mulVec hyy
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hX2,
        Matrix.one_mulVec, Matrix.one_mulVec] at this
      rw [← this]
      exact sm V φ hφint y' hy'

end GlobalTheory.LatMatch
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardFramesMatchCompletedLatticesAtPrimeStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardFrames_match_completedLattices_at_prime : ∀ {D : D7} {V V' : HSp D} {n : ℕ} (hF : D.host.F = maximalRealSubfield D.host.E) (Q : principalLevelFrame.RowPsi V n) (Q' : principalLevelFrame.RowPsi V' n), StdPsi hF Q → StdPsi hF Q' → ∀ (P : Pl D.host.E) (e f : Formalism.L2.Theta.AE D), IsPrimeIdem P e f → V'.rank = V.rank ∧ ∃ (J : Matrix (Fin V'.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (J' : Matrix (Fin V.rank) (Fin V'.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)), J * J' = 1 ∧ J' * J = 1 ∧ (∀ κ, finMat D.sp.cm.sig V'.gram (Q'.ψ κ) * J = J * finMat D.sp.cm.sig V.gram (Q.ψ κ)) ∧ ∀ y, finPart D f • y ∈ Formalism.L2.NTheta.LamHat V ↔ finPart D f • J.mulVec y ∈ Formalism.L2.NTheta.LamHat V' := by
  first | exact @GlobalTheory.LatMatch.frames_match_lattices | exact GlobalTheory.LatMatch.frames_match_lattices | (intros; apply GlobalTheory.LatMatch.frames_match_lattices <;> assumption)
end
