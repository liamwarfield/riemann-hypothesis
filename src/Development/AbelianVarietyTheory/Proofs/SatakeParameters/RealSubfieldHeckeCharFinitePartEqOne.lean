module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionSplitPlace
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.SharpPoly

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealSubfieldHeckeCharFinitePartEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealSubfieldHeckeCharFinitePartEqOne
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj finiteCompletionMap)

namespace GlobalTheory.HeckeFinTriv

theorem valued_natCast_le_one {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Valued.v (n : v.adicCompletion K) ≤ 1 := by
  induction n with
  | zero => rw [Nat.cast_zero, map_zero]; exact zero_le
  | succ n ih =>
    rw [Nat.cast_succ]
    exact Valuation.map_add_le _ ih (by rw [map_one])

theorem valued_natCast_le_of_dvd {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {M N : ℕ}
    (h : M ∣ N) : Valued.v (N : v.adicCompletion K) ≤ Valued.v (M : v.adicCompletion K) := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  exact mul_le_of_le_one_right' (valued_natCast_le_one v k)

theorem finPart_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ψ : HChar (maximalRealSubfield E)) (M : ℕ), (∀ a : Ideles (maximalRealSubfield E), a ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E) → (∀ w, (a : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).1 w = 1) → (∀ P : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Valued.v ((a : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 P - 1) ≤ Valued.v ((M : maximalRealSubfield E) : P.adicCompletion (maximalRealSubfield E))) → ψ.1 a = 1) → (∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → ψ.UnrAt (w.under (𝓞 (maximalRealSubfield E)))) → ∀ (w₀ : HeightOneSpectrum (𝓞 E)) (N : ℕ), M ∣ N → ∀ b : Ideles (maximalRealSubfield E), ideleMap (maximalRealSubfield E) E b ∈ levT E {w | GlobalTheory.UnitaryBC.IsSplitAt w ∧ w ≠ w₀} N → ψ.1 (GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b) = 1 := by
  intro E _ _ _ ψ M hlev hns w₀ N hMN b hb
  have he : ∀ w : HeightOneSpectrum (𝓞 E), (w.under (𝓞 (maximalRealSubfield E))).asIdeal.ramificationIdx' w.asIdeal ≠ 0 := fun w =>
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under (𝓞 (maximalRealSubfield E))).ne_bot
  have hc : ∀ w : HeightOneSpectrum (𝓞 E), (ideleMap (maximalRealSubfield E) E b).val.2 w =
      finiteCompletionMap (maximalRealSubfield E) E w (b.val.2 (w.under (𝓞 (maximalRealSubfield E)))) := fun w => rfl
  have hs : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) = v := fun v => by
    haveI := v.isPrime
    obtain ⟨⟨P, hP, hP'⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 E)))
    exact ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, HeightOneSpectrum.ext hP'.over.symm⟩

  have hunit : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Valued.v (b.val.2 v) = 1 := fun v => by
    obtain ⟨w, rfl⟩ := hs v
    have h := hb.1 w
    change Valued.v ((ideleMap (maximalRealSubfield E) E b).val.2 w) = 1 at h
    rw [hc, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, pow_eq_one_iff_of_nonneg zero_le (he w)] at h
    exact h

  have hcong : ∀ w : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w → w ≠ w₀ →
      Valued.v (b.val.2 (w.under (𝓞 (maximalRealSubfield E))) - 1) ≤ Valued.v (N : (w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) := fun w h1 h2 => by
    have h := hb.2 w ⟨h1, h2⟩
    change Valued.v ((ideleMap (maximalRealSubfield E) E b).val.2 w - 1) ≤ _ at h
    rwa [hc, ← map_one (finiteCompletionMap (maximalRealSubfield E) E w), ← map_sub, ← map_natCast (finiteCompletionMap (maximalRealSubfield E) E w),
      GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap,
      pow_le_pow_iff_left₀ zero_le zero_le (he w)] at h
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local (maximalRealSubfield E) ψ.1 ψ.2.1 (GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b)
    (GlobalTheory.Mem.Chr.finPartI_mem_unitIdl.2 hunit) (fun w => by rw [GlobalTheory.Mem.Chr.finPartI_fst]; rfl) ?_
  intro v x hx
  rw [GlobalTheory.Mem.Chr.finPartI_snd] at hx
  have hxu : Valued.v (x : v.adicCompletion (maximalRealSubfield E)) = 1 := by rw [hx]; exact hunit v
  by_cases hu : ψ.UnrAt v
  · exact hu x hxu
  obtain ⟨w, hw⟩ := hs v
  have hsp : GlobalTheory.UnitaryBC.IsSplitAt w := by
    by_contra hn
    exact hu (hw ▸ hns w hn)
  obtain ⟨u, hu1, hu2⟩ := hsp
  have hsp' : ∃ w' : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w' ∧ w' ≠ w₀ ∧ w'.under (𝓞 (maximalRealSubfield E)) = v := by
    by_cases h0 : w = w₀
    · refine ⟨u, ⟨w, fun e => hu1 e.symm, hu2.symm⟩, h0 ▸ hu1, hu2.trans hw⟩
    · exact ⟨w, ⟨u, hu1, hu2⟩, h0, hw⟩
  obtain ⟨w', hw'1, hw'2, rfl⟩ := hsp'
  have hxc : Valued.v ((x : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) - 1) ≤
      Valued.v ((M : (maximalRealSubfield E)) : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) := by
    rw [hx]
    refine (hcong w' hw'1 hw'2).trans ?_
    have e : ((M : (maximalRealSubfield E)) : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) = (M : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) := by
      rw [← map_natCast (algebraMap (maximalRealSubfield E) ((w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E))) M]; rfl
    rw [e]
    exact valued_natCast_le_of_dvd _ hMN
  have hself : ((GlobalTheory.Mem.Chr.localIdele (maximalRealSubfield E) (w'.under (𝓞 (maximalRealSubfield E))) x :
      AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 (w'.under (𝓞 (maximalRealSubfield E)))) = x :=
    GlobalTheory.Mem.LocTriv.ev_local_self _ x
  have hne : ∀ P, P ≠ w'.under (𝓞 (maximalRealSubfield E)) →
      ((GlobalTheory.Mem.Chr.localIdele (maximalRealSubfield E) (w'.under (𝓞 (maximalRealSubfield E))) x :
        AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 P) = 1 :=
    fun _ hP => GlobalTheory.Mem.LocTriv.ev_local_ne hP x
  apply hlev
  · intro P
    by_cases hP : P = w'.under (𝓞 (maximalRealSubfield E))
    · subst hP
      rw [hself]
      exact hxu
    · rw [hne P hP]
      exact map_one _
  · intro w
    rfl
  · intro P
    by_cases hP : P = w'.under (𝓞 (maximalRealSubfield E))
    · subst hP
      rw [hself]
      exact hxc
    · rw [hne P hP, sub_self, map_zero]
      exact zero_le

end GlobalTheory.HeckeFinTriv
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealSubfieldHeckeCharFinitePartEqOneStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realSubfield_heckeChar_finitePart_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ψ : HChar (maximalRealSubfield E)) (M : ℕ), (∀ a : Ideles (maximalRealSubfield E), a ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E) → (∀ w, (a : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).1 w = 1) → (∀ P : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Valued.v ((a : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 P - 1) ≤ Valued.v ((M : maximalRealSubfield E) : P.adicCompletion (maximalRealSubfield E))) → ψ.1 a = 1) → (∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → ψ.UnrAt (w.under (𝓞 (maximalRealSubfield E)))) → ∀ (w₀ : HeightOneSpectrum (𝓞 E)) (N : ℕ), M ∣ N → ∀ b : Ideles (maximalRealSubfield E), ideleMap (maximalRealSubfield E) E b ∈ levT E {w | GlobalTheory.UnitaryBC.IsSplitAt w ∧ w ≠ w₀} N → ψ.1 (GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b) = 1 := by
  first | exact @GlobalTheory.HeckeFinTriv.finPart_eq_one | exact GlobalTheory.HeckeFinTriv.finPart_eq_one | (intros; apply GlobalTheory.HeckeFinTriv.finPart_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ToMatrixCoMulSymm
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.UG Formalism.L2.DIV Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc.Emat

open Matrix

theorem gram_of_orth {E : Type} [Field E] [StarRing E] (σ : E →+* E) (hσ : ∀ x, σ x = star x) {N : ℕ}
    (J : Matrix (Fin N) (Fin N) E) (co : (Fin N → E) ≃ₗ[E] (Fin N → E)) (hCo : IsOrthCo σ J co) :
    star (LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E))) * LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)) = J := by
  ext i k
  have h := hCo (Pi.single i 1) (Pi.single k 1)
  rw [Matrix.mul_apply]
  have hl : ∀ a, (star (LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)))) i a * LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)) a k =
      σ (co (Pi.single i 1) a) * co (Pi.single k 1) a := by
    intro a
    rw [Matrix.star_apply, LinearMap.toMatrix'_apply, LinearMap.toMatrix'_apply, hσ]
    rfl
  rw [Finset.sum_congr rfl fun a _ => hl a, h]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hh
    exact absurd (Finset.mem_univ _) hh
  · intro b _ hb
    refine Finset.sum_eq_zero fun b' _ => ?_
    simp [Pi.single_apply, hb]
  · intro hh
    exact absurd (Finset.mem_univ _) hh

theorem toMatrix_toLE {E : Type} [Field E] {N : ℕ} (γ : GL (Fin N) E) :
    LinearMap.toMatrix' ((toLE γ : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)) = γ := by
  ext i j
  simp [toLE, LinearMap.toMatrix'_apply, Matrix.GeneralLinearGroup.toLin, Matrix.mulVec, dotProduct, Pi.single_apply]

theorem unit_mat' {n N : ℕ} (hk : n = N) {E' : Type} [Field E'] [StarRing E'] (co coi γ J : Matrix (Fin N) (Fin N) E')
    (h1 : star co * co = J) (h2 : star γ * J * γ = J) (h3 : co * coi = 1) :
    (co * γ * coi).submatrix (finCongr hk) (finCongr hk) * star ((co * γ * coi).submatrix (finCongr hk) (finCongr hk)) = 1 := by
  subst hk
  have e2 : ∀ A : Matrix (Fin n) (Fin n) E', A.submatrix (finCongr rfl) (finCongr rfl) = A := fun A => by ext x y; rfl
  rw [e2, mul_eq_one_comm]
  calc star (co * γ * coi) * (co * γ * coi) = star coi * (star γ * (star co * co) * γ) * coi := by
        simp only [star_mul, Matrix.mul_assoc]
    _ = star coi * (star co * co) * coi := by rw [h1, h2]
    _ = star (co * coi) * (co * coi) := by simp only [star_mul, Matrix.mul_assoc]
    _ = 1 := by rw [h3, star_one, Matrix.one_mul]

theorem star_eq_cT {E : Type} [Field E] [StarRing E] (σ : E →+* E) (hσ : ∀ x, σ x = star x) {N : ℕ} (M : Matrix (Fin N) (Fin N) E) :
    star M = cT σ M := by
  ext i k
  simp [cT, Matrix.star_apply, hσ]

theorem orth_of_gram {E : Type} [Field E] (σ : E →+* E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (co : (Fin N → E) ≃ₗ[E] (Fin N → E))
    (hM : cT σ (LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E))) * LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)) = J) :
    IsOrthCo σ J co := by
  intro x y
  set M := LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)) with hMdef
  have hx : ∀ z, co z = M *ᵥ z := fun z => by rw [hMdef, LinearMap.toMatrix'_mulVec]; rfl
  rw [← hM]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hx, Matrix.mulVec, dotProduct, cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul,
    Finset.sum_mul, Finset.mul_sum]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  ring

theorem toMatrix_stdG {E : Type} [Field E] {N : ℕ} (σ : E →+* E) (J : Matrix (Fin N) (Fin N) E) (γ : GL (Fin N) E) :
    LinearMap.toMatrix' ((stdG σ J γ : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)) =
      LinearMap.toMatrix' ((stdCo σ J : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)) * (γ : Matrix (Fin N) (Fin N) E) *
        LinearMap.toMatrix' (((stdCo σ J).symm : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)) := by
  rw [← toMatrix_toLE γ, ← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
  rfl

theorem toMatrix_co_mul_symm {E : Type} [Field E] {N : ℕ} (co : (Fin N → E) ≃ₗ[E] (Fin N → E)) :
    LinearMap.toMatrix' (co : (Fin N → E) →ₗ[E] (Fin N → E)) * LinearMap.toMatrix' ((co.symm : (Fin N → E) ≃ₗ[E] (Fin N → E)) : (Fin N → E) →ₗ[E] (Fin N → E)) = 1 := by
  rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_symm, LinearMap.toMatrix'_id]

end GlobalTheory.TwV.Xc.Emat

end


open GlobalTheory.TwV.Xc.Emat in
theorem GlobalTheory.TwV.Xc.eMat_unitary_det : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (σ : E →+* E), (∀ x, σ x = star x) → ∀ (a N : ℕ) (hr : a = N) (J : Matrix (Fin N) (Fin N) E) (crd : GL (Fin N) E), cT σ crd.1 * crd.1 = J → IsOrthCo σ J (stdCo σ J) ∧ ∀ g ∈ UJ σ J, eMat hr σ J g * star (eMat hr σ J g) = 1 ∧ (eMat hr σ J g).det = g.1.det := by
  intro E _ _ _ σ hσ a N hr J crd hcrd
  subst hr
  have hco : IsOrthCo σ J (stdCo σ J) := by
    refine Classical.epsilon_spec (p := IsOrthCo σ J) ⟨toLE crd, ?_⟩
    refine orth_of_gram σ J _ ?_
    rw [toMatrix_toLE]
    exact hcrd
  refine ⟨hco, fun g hg => ?_⟩
  have hg' : star (g : Matrix (Fin a) (Fin a) E) * J * (g : Matrix (Fin a) (Fin a) E) = J := by
    rw [star_eq_cT σ hσ]
    exact hg
  unfold eMat
  rw [toMatrix_stdG]
  refine ⟨unit_mat' rfl _ _ _ J (gram_of_orth σ hσ J _ hco) hg' (toMatrix_co_mul_symm _), ?_⟩
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_mul, Matrix.det_mul, mul_right_comm, ← Matrix.det_mul, toMatrix_co_mul_symm,
    Matrix.det_one, one_mul]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FormsSharpAtOfValTied
noncomputable section

namespace GlobalTheory.FormsSharpTie

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Forms Formalism.L2.KerInert.K2

theorem natW_antitone {n : ℕ} (l : DomWeight n) : Antitone l.natW := by
  intro a b h
  simp only [DomWeight.natW]
  exact Int.toNat_le_toNat (by have := l.anti h; omega)

theorem ratSpan_le_wtPol (D : D7) {n : ℕ} (lam : D.what₂.Tau → DomWeight n) :
    ∀ P ∈ RatSpan D lam, P ∈ WtPol ℂ (fun τ r => (lam τ).natW r) := by
  intro P hP
  have hle : RatSpan D lam ≤ (WtPol ℂ (fun τ r => (lam τ).natW r)).toAddSubgroup := by
    unfold RatSpan
    rw [AddSubgroup.closure_le]
    rintro p ⟨r, f, hf, rfl⟩
    show _ ∈ WtPol ℂ _
    apply Submodule.smul_mem
    apply GlobalTheory.KerWt.VV_le_WtPol lam
    unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat
    apply Submodule.subset_span
    refine ⟨fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ), fun τ => ?_, rfl⟩
    have h1 : MvPolynomial.map (Int.castRingHom ℂ) (f τ) ∈ delSq ℂ n (lam τ) := by
      rw [← GlobalTheory.Published.span_map_delSq ℤ ℂ (Int.castRingHom ℂ) n (lam τ)]
      exact Submodule.subset_span ⟨f τ, hf τ, rfl⟩
    exact Formalism.GradedWeylDivisibility.weylLeDual ℂ n n le_rfl _ (natW_antitone (lam τ)) h1
  exact hle hP

theorem eval_colSub {ι : Type} [Fintype ι] {a : ℕ} (β x : ι → Matrix (Fin a) (Fin a) ℂ) (p : Formalism.L2.DIV.Pol ℂ ι a) :
    MvPolynomial.eval (fun k : ι × Fin a × Fin a => x k.1 k.2.1 k.2.2) (colSub β p) =
      MvPolynomial.eval (fun k : ι × Fin a × Fin a => (x k.1 * β k.1) k.2.1 k.2.2) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [colSub]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, colSub, MvPolynomial.aeval_X, MvPolynomial.eval_X, Matrix.mul_apply]
    congr 1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp [mul_comm]

theorem zpow_mul_pow_toNat {x : ℂ} (hx : x ≠ 0) (s : ℤ) : x ^ s * x ^ (-s).toNat = x ^ s.toNat := by
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hx]
  congr 1
  omega

theorem isVLam_of_wtPol {ι : Type} [Fintype ι] {a : ℕ} {Y : Type} (fr g : Y → ι → Matrix (Fin a) (Fin a) ℂ)
    (B : ι → Matrix (Fin a) (Fin a) ℂ) (hB : ∀ τ, (B τ).det ≠ 0) (hg : ∀ y τ, (g y τ).det ≠ 0)
    (hfr : ∀ y τ, fr y τ = B τ * g y τ) (ν : ι → Fin a → ℕ) (s : ι → ℤ) (P : Formalism.L2.DIV.Pol ℂ ι a)
    (hP : P ∈ WtPol ℂ ν) :
    IsVLam fr (fun τ r => (ν τ r : ℤ) + s τ)
      (fun y => (∏ τ, (g y τ).det ^ s τ) * MvPolynomial.eval (fun x : ι × Fin a × Fin a => g y x.1 x.2.1 x.2.2) P) := by
  have hBu : ∀ τ, IsUnit (B τ).det := fun τ => isUnit_iff_ne_zero.2 (hB τ)
  have hg' : ∀ y τ, g y τ = (B τ)⁻¹ * fr y τ := by
    intro y τ
    rw [hfr, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hBu τ), Matrix.one_mul]
  refine ⟨?_, ?_⟩
  ·
    let sub : Formalism.L2.DIV.Pol ℂ ι a →ₐ[ℂ] Formalism.L2.DIV.Pol ℂ ι a :=
      MvPolynomial.aeval fun v => ∑ c, MvPolynomial.C ((B v.1)⁻¹ v.2.1 c) * MvPolynomial.X (v.1, c, v.2.2)
    have hsub : ∀ y (p : Formalism.L2.DIV.Pol ℂ ι a), MvPolynomial.eval (fun k : ι × Fin a × Fin a => fr y k.1 k.2.1 k.2.2) (sub p) =
        MvPolynomial.eval (fun k : ι × Fin a × Fin a => g y k.1 k.2.1 k.2.2) p := by
      intro y p
      induction p using MvPolynomial.induction_on with
      | C c => simp [sub]
      | add p q hp hq => simp only [map_add (f := _), hp, hq]
      | mul_X p v hp =>
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_mul, hp, sub, MvPolynomial.aeval_X, MvPolynomial.eval_X, hg', Matrix.mul_apply, map_sum]
        simp
    have hdet : ∀ y τ, MvPolynomial.eval (fun k : ι × Fin a × Fin a => g y k.1 k.2.1 k.2.2) (frDet ℂ a τ) = (g y τ).det := by
      intro y τ
      unfold frDet
      rw [RingHom.map_det]
      congr 1
      ext i k
      simp
    refine ⟨MvPolynomial.C (∏ τ, (B τ).det ^ (-s τ).toNat) * (∏ τ, sub (frDet ℂ a τ) ^ (s τ).toNat) * sub P,
      fun τ => (-s τ).toNat, fun y => ?_⟩
    simp only [frPolyG, LinearMap.coe_mk, AddHom.coe_mk, map_mul, map_prod, map_pow, MvPolynomial.eval_C, hsub, hdet]
    have e2 : ∀ τ, (g y τ).det ^ s τ * (g y τ).det ^ (-s τ).toNat = (g y τ).det ^ (s τ).toNat :=
      fun τ => zpow_mul_pow_toNat (hg y τ) (s τ)
    simp only [hfr, Matrix.det_mul, mul_pow, Finset.prod_mul_distrib]
    rw [← Finset.prod_congr rfl fun τ _ => e2 τ, Finset.prod_mul_distrib]
    ring
  ·
    intro y y₂ β hβ hy
    have hgy : ∀ τ, g y₂ τ = g y τ * β τ := by
      intro τ
      have h := hy τ
      rw [hfr, hfr, Matrix.mul_assoc] at h
      have h2 := congrArg (fun M => (B τ)⁻¹ * M) h
      simp only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (hBu τ), Matrix.one_mul] at h2
      exact h2
    have hdβ : ∀ τ, (β τ).det = ∏ r, β τ r r := fun τ =>
      Matrix.det_of_upperTriangular (fun r s h => (hβ τ).1 r s h)
    have hev : MvPolynomial.eval (fun x : ι × Fin a × Fin a => g y₂ x.1 x.2.1 x.2.2) P =
        (∏ τ, ∏ r, β τ r r ^ ν τ r) * MvPolynomial.eval (fun x : ι × Fin a × Fin a => g y x.1 x.2.1 x.2.2) P := by
      have := eval_colSub β (g y) P
      rw [hP β hβ, MvPolynomial.smul_eval] at this
      simp only [hgy]
      rw [← this]
    have hne : ∀ τ r, β τ r r ≠ 0 := fun τ r => (hβ τ).2 r
    have e3 : ∀ τ r, β τ r r ^ ((ν τ r : ℤ) + s τ) = β τ r r ^ ν τ r * β τ r r ^ s τ := by
      intro τ r
      rw [zpow_add₀ (hne τ r), zpow_natCast]
    dsimp only
    rw [hev]
    simp only [hgy, Matrix.det_mul, hdβ, mul_zpow, e3, Finset.prod_mul_distrib, ← Finset.prod_zpow]
    ring


open Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Finset in
theorem sharpWt_rat (D : D7) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ) (hj : j < D.R.m)
    (τ : D.what₂.Tau) (r : Fin (D.R.N j)) :
    ((((nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ : ℤ)) : ℚ) =
        ((((Tw.fm u μ).lam j τ).w r : ℤ) : ℚ) - (j : ℚ) * ((D.R.t : ℚ) + 1) / 2 := by
  have h1 := (GlobalTheory.KerWt.nu_t_identity D u j hj τ r).1
  have h2 := (D.chTw u μ).sSharp_eq j hj τ
  have h3 := (Tw.fm u μ).lam_eq j hj.le τ r
  have h2' : (((D.chTw u μ).sSharp j τ : ℤ) : ℝ) =
      (((D.hcW u τ).e ⟨j, hj⟩ : ℚ) : ℝ) - ((D.R.k : ℝ) + ((j : ℝ) + 1) * ((D.R.t : ℝ) + 1)) / 2 := by
    have := congrArg (fun q : ℚ => (q : ℝ)) h2
    simp only [sExp', Ranks.N] at this
    push_cast at this
    exact this
  have he : ∀ (k : ℕ) (hk : k < D.R.m), k = j → (D.hc τ).e ⟨k, hk⟩ = (D.hcW u τ).e ⟨j, hj⟩ := by
    rintro k hk rfl; rw [D.hcW_e]
  apply Rat.cast_injective (α := ℝ)
  have hw : ((((Tw.fm u μ).lam j τ).w r : ℤ) : ℝ) = (((((Tw.fm u μ).lam j τ).w r : ℤ) : ℚ) : ℝ) := by push_cast; rfl
  push_cast
  rw [h1, h2', hw, h3]
  unfold DV.nuRow DV.srcPar DV.wSz
  rw [dif_pos (show 1 ≤ j + 1 ∧ j + 1 ≤ D.R.m by omega), he _ _ (by omega)]
  simp only [Ranks.N]
  by_cases hr : r.1 < D.R.k
  · rw [dif_pos hr, dif_pos hr]
    simp only [hcToWeightQ, rhoVec]
    push_cast
    ring
  · have hb : (r.1 - D.R.k) / (D.R.t + 1) < D.R.m := by
      have := D.R.blk_lt hj.le r hr
      omega
    rw [dite_eq_right hr, dite_eq_right hr, dif_pos hb]
    have hdm := Nat.div_add_mod (r.1 - D.R.k) (D.R.t + 1)
    have hrk : (r.1 : ℝ) = D.R.k + (D.R.t + 1) * (((r.1 - D.R.k) / (D.R.t + 1) : ℕ) : ℝ) + (((r.1 - D.R.k) % (D.R.t + 1) : ℕ) : ℝ) := by
      have : r.1 = D.R.k + (D.R.t + 1) * ((r.1 - D.R.k) / (D.R.t + 1)) + (r.1 - D.R.k) % (D.R.t + 1) := by omega
      exact_mod_cast this
    simp only [wG]
    push_cast
    rw [hrk]
    ring

theorem nuT_sub_sSharp (D : D7) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ) (hj : j < D.R.m)
    (τ : D.what₂.Tau) (r : Fin (D.R.N j)) :
    (nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ = (lamTG (Tw.fm u μ) j τ).w r := by
  have h := sharpWt_rat D Tw u μ j hj τ r
  set z : ℤ := (nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ with hz
  set w : ℤ := ((Tw.fm u μ).lam j τ).w r with hw
  show z = ((Tw.fm u μ).lam j τ).w r - ((j * (D.R.t + 1) / 2 : ℕ) : ℤ)
  rw [← hw]
  generalize hn : j * (D.R.t + 1) = n
  have h2 : (2 * (w - z) : ℚ) = (n : ℚ) := by
    rw [← hn]; push_cast; rw [h]; ring
  have h3 : 2 * (w - z) = (n : ℤ) := by exact_mod_cast h2
  omega

theorem natW_add_shift {N : ℕ} (l : DomWeight N) (c : ℤ) (r : Fin N) :
    ((l.natW r : ℕ) : ℤ) + (shW l c).detShift = (shW l c).w r := by
  have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) r.2
  have hle : l.w ⟨N - 1, by omega⟩ ≤ l.w r := l.anti (show r ≤ ⟨N - 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))
  simp only [DomWeight.natW, DomWeight.detShift, shW, dif_pos hN]
  rw [Int.toNat_of_nonneg (by omega)]
  ring

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc0 : G.Consts} {Dx : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc0 Dx cX}

theorem formsSharpAt_of_valTied (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ) (hj : j < D.R.m)
    {T : ℕ} {bad : Set (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.host.F))}
    {eY : (D.chTw u μ).Y j ≃ Fr D j hj.le} {okW : D.what₂.places.Pl → Prop} {Ch : Type} {chOf : (D.chTw u μ).cls j → Ch}
    {lat : (D.chTw u μ).cls j → Submodule (NumberField.RingOfIntegers D.host.E) (Fin (D.R.N j) → D.host.E)}
    {K : ∀ β : Ch, LevelChart D T bad j hj.le (fun c : {c // chOf c = β} => (D.chTw u μ).stab j c.1) (fun c => lat c.1)}
    (hV : ValuationCompatibleChart (ex.tw.fm u μ) eY okW chOf K) (crd : GL (Fin (D.R.N j)) D.host.E)
    (hfrm : ∀ y τ, (t.O u μ).frm j y τ = atInf (embT D) crd.1 τ * (eY y).1 τ) :
    ∀ x, ∃ Q, SharpQ t ex.tw u μ j x Q := by
  intro x
  have hx := (hV.rat ((ex.tw.fm u μ).emb j x)).1 ⟨x, rfl⟩
  choose P hP hE using hx.2
  have hB : ∀ τ, (atInf (embT D) crd.1 τ).det ≠ 0 := by
    intro τ
    show ((crd : Matrix (Fin (D.R.N j)) (Fin (D.R.N j)) D.host.E).map (embT D τ)).det ≠ 0
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 (Matrix.isUnits_det_units crd).ne_zero
  have hg : ∀ y τ, ((eY y).1 τ).det ≠ 0 := fun y τ => ((eY y).2 τ).ne_zero
  have key : ∀ c, IsVLam ((t.O u μ).frm j) (fun τ r => (nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ)
      ((ex.tw.fm u μ).emb j x c) := by
    intro c
    have h1 := isVLam_of_wtPol ((t.O u μ).frm j) (fun y => (eY y).1) (fun τ => atInf (embT D) crd.1 τ) hB hg hfrm
      (fun τ r => ((ex.tw.fm u μ).lam j τ).natW r) (shiftOf (lamTG (ex.tw.fm u μ) j)) (P c)
      (ratSpan_le_wtPol D _ (P c) (hP c))
    have hw : (fun τ r => (nuT D u j τ r : ℤ) - (D.chTw u μ).sSharp j τ) =
        (fun τ r => ((((ex.tw.fm u μ).lam j τ).natW r : ℕ) : ℤ) + shiftOf (lamTG (ex.tw.fm u μ) j) τ) := by
      funext τ r
      rw [nuT_sub_sSharp D ex.tw u μ j hj τ r]
      exact (natW_add_shift _ _ r).symm
    have hf : (ex.tw.fm u μ).emb j x c = fun y => (∏ τ, ((eY y).1 τ).det ^ shiftOf (lamTG (ex.tw.fm u μ) j) τ) *
        MvPolynomial.eval (fun k : D.what₂.Tau × Fin (D.R.N j) × Fin (D.R.N j) => (eY y).1 k.1 k.2.1 k.2.2) (P c) := by
      funext y
      rw [hE c y]
      simp [fnOf]
    rw [hw, hf]
    exact h1
  have := fun c => forms_sharp_description Formalism.L2.KerInert.SharpPolyP.sharp_polynomial_frames D u (D.chTw u μ) (t.O u μ) j hj.le
    (nuT D u j) _ (key c)
  choose Q hQ hQE using this
  exact ⟨Q, hQ, hQE⟩


attribute [local instance] Formalism.BasicNotions.Host.cmStar in
theorem formsSharpAt_of_pins (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (St : GlobalTheory.TwU.ChainCharts D u μ)
    (A : GlobalTheory.TwU.AdData t u μ St) (dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt) (hP : GlobalTheory.TwU.AdPins A dtU)
    (okW : ℕ → D.what₂.places.Pl → Prop)
    (hV : ∀ j (hj : j < D.R.m), ValuationCompatibleChart (ex.tw.fm u μ) (St j hj.le).eY (okW j) (St j hj.le).chOf (St j hj.le).K) :
    ∀ j, j < D.R.m → ∀ x, ∃ Q, SharpQ t ex.tw u μ j x Q :=
  fun j hj => formsSharpAt_of_valTied t u μ j hj (hV j hj) (A.crd j hj.le) (hP.frm j hj.le)

end GlobalTheory.FormsSharpTie
end
end
