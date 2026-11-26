module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelSplitPlacesEqJetClassicalTheta
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometrySubspaceProperty

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleLevelPosOddBadPrimesPrimeToLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleLevelPosOddBadPrimesPrimeToLevel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TupLevel

theorem odd_absNorm {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (h : (2 : 𝓞 E) ∉ P.asIdeal) :
    Odd (Ideal.absNorm P.asIdeal) := by
  rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
  intro h2
  haveI := P.isPrime
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ P.ne_bot
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h2
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := 𝓞 E ⧸ P.asIdeal) 2 h2
  have h0 : x ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at hx
    exact absurd hx (by norm_num)
  have h1 : (2 : 𝓞 E ⧸ P.asIdeal) * x = 0 := by
    have := addOrderOf_nsmul_eq_zero x
    rw [hx, two_nsmul] at this
    rw [two_mul, this]
  rcases mul_eq_zero.1 h1 with h3 | h3
  · exact h (Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_ofNat]; exact h3))
  · exact h0 h3

theorem odd_levC {X : Formalism.L2.Col.Fields} {Pr : Formalism.L2.Col.Primes X}
    {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
    (hX : X.Ok) (hPr : Pr.Ok) (cst : Formalism.L2.Col.LocCst X (Formalism.L2.Col.rowSG Pr sel mu)) (u : Pr.Word)
    (h2 : ∀ P ∈ Formalism.L2.Col.Sall sel mu u, (2 : 𝓞 X.E) ∉ P.asIdeal) : Odd (levC sel mu cst u) := by
  have hp : Odd (∏ P : Formalism.L2.Col.rowSG Pr sel mu, Formalism.L2.Col.qOf P.1) :=
    Finset.prod_induction _ Odd (fun _ _ => Odd.mul) odd_one fun P _ =>
      odd_absNorm P.1 (h2 P.1 (Finset.mem_union.2 (Or.inr P.2)))
  obtain ⟨P₀, hP₀⟩ : (Pr.vT u).Nonempty := Finset.card_pos.1 (hPr.vT_card u ▸ hX.f_pos)
  have hT : Odd (Pr.T u) := hPr.vT_norm u P₀ hP₀ ▸ odd_absNorm P₀ (h2 P₀ (Finset.mem_union.2 (Or.inl hP₀)))
  exact hp.pow.mul (hT.mul hp.pow)

theorem levC_pos_odd_and_off : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (u : B.Word) (a : I.ι), 0 < levC I.sel (I.tup a) (I.cst a) u ∧ Odd (levC I.sel (I.tup a) (I.cst a) u) ∧ (∀ Q ∈ Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u, ((B.host.QS * B.host.q * B.host.d : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal) := by
  intro B X I hI _ u a
  obtain ⟨hXo, hPr, -⟩ := base_fields_primes_ok B X
  have hc : (B.primes X).cond = B.host.QS * B.host.q * B.host.d := rfl
  have h2 := fun Q (hQ : Q ∈ Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u) =>
    GlobalTheory.DatumJets.HidaSetting.notMem_Sall hPr hI.sel_ok u Nat.prime_two (hI.ram_mem 2 Nat.prime_two B.host.toHostRaw.two_dvd_condN)
      (by rw [hc]; exact B.host.toHostRaw.two_dvd_condN) hQ
  have ho : Odd (levC I.sel (I.tup a) (I.cst a) u) :=
    odd_levC hXo hPr (I.cst a) u fun Q hQ h => h2 Q hQ (by exact_mod_cast h)
  refine ⟨ho.pos, ho, fun Q hQ h => ?_⟩
  obtain ⟨l, n, -, hlP, hl, -⟩ := Ideal.exists_prime_and_absNorm_eq_pow Q.asIdeal
  by_cases hd : l ∣ B.host.QS * B.host.q * B.host.d
  · exact GlobalTheory.DatumJets.HidaSetting.notMem_Sall hPr hI.sel_ok u hl (hI.ram_mem l hl hd) (by rw [hc]; exact hd) hQ hlP
  · exact UpperTheory.Ram.natCast_notMem_of_coprime Q.isPrime.ne_top hlP ((Nat.Prime.coprime_iff_not_dvd hl).2 hd).symm h

end GlobalTheory.TupLevel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleLevelPosOddBadPrimesPrimeToLevelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tupleLevel_pos_odd_badPrimes_prime_to_level : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (u : B.Word) (a : I.ι), 0 < levC I.sel (I.tup a) (I.cst a) u ∧ Odd (levC I.sel (I.tup a) (I.cst a) u) ∧ (∀ Q ∈ Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u, ((B.host.QS * B.host.q * B.host.d : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal) := by
  first | exact @GlobalTheory.TupLevel.levC_pos_odd_and_off | exact GlobalTheory.TupLevel.levC_pos_odd_and_off | (intros; apply GlobalTheory.TupLevel.levC_pos_odd_and_off <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPolynomialJetValueEqJetLinearFormRescaled
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPolynomialJetValueEqJetLinearFormRescaled
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

namespace GlobalTheory.KJInf

theorem mvZ_scal_monomial {ι : Type} {a b : ℕ} (r : ι → ℂ) (k : ι × Fin b × Fin a →₀ ℕ) (c : ℂ) :
    mvZ (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ)) (fun τ => r τ • (1 : Matrix (Fin b) (Fin b) ℂ)) (MvPolynomial.monomial k c) =
      MvPolynomial.monomial k (c * k.prod fun v n => r v.1 ^ n) := by
  set M := mvZ (fun _ => (1 : Matrix (Fin a) (Fin a) ℂ)) (fun τ => r τ • (1 : Matrix (Fin b) (Fin b) ℂ)) with hM
  have hX : ∀ v : ι × Fin b × Fin a, M (MvPolynomial.X v) = MvPolynomial.C (r v.1) * MvPolynomial.X v := by
    intro v
    simp only [hM, mvZ, MvPolynomial.aeval_X]
    rw [Finset.sum_eq_single v.2.1]
    · rw [Finset.sum_eq_single v.2.2]
      · simp
      · intro j _ hj; simp [Matrix.one_apply_ne (Ne.symm hj)]
      · simp
    · intro i _ hi; simp [Matrix.one_apply_ne hi]
    · simp
  have hC : M (MvPolynomial.C c) = MvPolynomial.C c := by
    simp only [hM, mvZ, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
  rw [MvPolynomial.monomial_eq, map_mul, MvPolynomial.monomial_eq, hC]
  simp only [Finsupp.prod, map_prod, map_pow, hX, mul_pow, Finset.prod_mul_distrib, MvPolynomial.C_mul, mul_assoc]

end GlobalTheory.KJInf

namespace GlobalTheory.KJInf

theorem jetP_eq_jetL : ∀ (D : D7) (S T : HSp D) (s : ℂ) (cD : D.what₂.Tau → ℂ), (∀ τ, cD τ ≠ 0) → ∀ (G : VCx D.what₂.Tau S.rank T.rank → ℂ) (P : FP D.what₂.Tau S.rank T.rank), jetP S T rfl rfl s G P = jetL cD G (mvZ (fun _ => 1) (fun τ => (s / cD τ) • 1) P) := by
  intro D S T s cD hcD G P
  have hid : (fun v : FVar D T.rank S.rank => (v.1, Fin.cast rfl v.2.1, Fin.cast rfl v.2.2)) = id := by
    funext v; rfl
  unfold GlobalTheory.AdForm.jetP
  rw [hid]
  simp only [Finsupp.mapDomain_id]
  conv_rhs => rw [P.as_sum]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mvZ_scal_monomial]
  have hm : ∀ x : ℂ, (MvPolynomial.monomial k x : FP D.what₂.Tau S.rank T.rank) = x • MvPolynomial.monomial k 1 := by
    intro x; rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hm, map_smul, jetL_monomial, smul_eq_mul]
  unfold jetC
  rw [mul_assoc, ← mul_assoc (k.prod _), ← Finsupp.prod_mul]
  congr 2
  refine Finsupp.prod_congr fun v _ => ?_
  rw [← mul_pow, div_mul_cancel₀ _ (hcD v.1)]

end GlobalTheory.KJInf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockPolynomialJetValueEqJetLinearFormRescaledStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockPolynomialJetValue_eq_jetLinearForm_rescaled : ∀ (D : D7) (S T : HSp D) (s : ℂ) (cD : D.what₂.Tau → ℂ), (∀ τ, cD τ ≠ 0) → ∀ (G : VCx D.what₂.Tau S.rank T.rank → ℂ) (P : FP D.what₂.Tau S.rank T.rank), jetP S T rfl rfl s G P = jetL cD G (mvZ (fun _ => 1) (fun τ => (s / cD τ) • 1) P) := by
  first | exact @GlobalTheory.KJInf.jetP_eq_jetL | exact GlobalTheory.KJInf.jetP_eq_jetL | (intros; apply GlobalTheory.KJInf.jetP_eq_jetL <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ClassicalThetaOfDatumSmulMove
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ClassicalThetaOfDatumSmulMove
open NumberField IsDedekindDomain

namespace GlobalTheory.Corev.ThCLin

open _root_.Formalism.L2.Ker _root_.Formalism.L2.Th1.H

theorem hatS_mul_left {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (vol : ℝ) (SA : Finset V)
    (Φ : V → ℂ) (p : ℂ) (y : V) :
    hatS H vol SA (fun s => p * Φ s) y = p * hatS H vol SA Φ y := by
  simp only [hatS, mul_assoc, ← Finset.mul_sum]
  ring

theorem thC_smul_move : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ} (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (AA : Submodule (𝓞 E) E) (SS : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (c : ℕ) (p : ℂ) (Ξ : Formalism.L2.Col.HomE E a b → ℂ) (θ : Formalism.L2.Ker.VV ι a b → ℂ), Formalism.L2.Ker.thC emb δ d sc AA SS N N' c (fun x => p * Ξ x) θ = Formalism.L2.Ker.thC emb δ d sc AA SS N N' c Ξ (fun z => p * θ z) := by
  intro E _ _ _ ι _ a b emb δ d sc AA SS N N' c p Ξ θ
  have hon : onV emb δ (fun x => p * Ξ x) = fun v => p * onV emb δ Ξ v := by
    funext v
    unfold onV
    split_ifs <;> simp
  funext z
  simp only [thC, xiV, xiL, xiS, hon, hatS_mul_left, sumU, opU]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  ring

end GlobalTheory.Corev.ThCLin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ClassicalThetaOfDatumSmulMoveStatement
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classicalThetaOfDatum_smul_move : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] {ι : Type} [Fintype ι] {a b : ℕ} (emb : ι → E →+* ℂ) (δ : ℂ) (d : ℕ) (sc : ℝ) (AA : Submodule (𝓞 E) E) (SS : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 E))) (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a)) (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (c : ℕ) (p : ℂ) (Ξ : Formalism.L2.Col.HomE E a b → ℂ) (θ : Formalism.L2.Ker.VV ι a b → ℂ), Formalism.L2.Ker.thC emb δ d sc AA SS N N' c (fun x => p * Ξ x) θ = Formalism.L2.Ker.thC emb δ d sc AA SS N N' c Ξ (fun z => p * θ z) := by
  first | exact @GlobalTheory.Corev.ThCLin.thC_smul_move | exact GlobalTheory.Corev.ThCLin.thC_smul_move | (intros; apply GlobalTheory.Corev.ThCLin.thC_smul_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIdentityAtEveryTuple
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerTup

theorem jetP_cast (D : D7) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (s : ℂ) (cD : D.what₂.Tau → ℂ)
    (hcD : ∀ τ, cD τ ≠ 0) (G : VCx D.what₂.Tau a b → ℂ) (P : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    jetP S T hS hT s G P = jetL cD G (mvZ (fun _ => 1) (fun τ => (s / cD τ) • 1) (castP hS hT P)) := by
  subst hS hT
  have h1 : castP (D := D) (rfl : S.rank = S.rank) (rfl : T.rank = T.rank) P = P := by
    conv_rhs => rw [← MvPolynomial.rename_id_apply P]
    rfl
  rw [h1]
  exact GlobalTheory.T.fockPolynomialJetValue_eq_jetLinearForm_rescaled D S T s cD hcD G P

theorem jetC_zero {ι : Type} [Fintype ι] {a b : ℕ} (cD : ι → ℂ) (m : Formalism.L2.Ker.DVar ι a b →₀ ℕ) :
    jetC cD (fun _ : VCx ι a b => (0 : ℂ)) m = 0 := by
  change jetC cD (0 : VCx ι a b → ℂ) m = 0
  simp only [jetC, derivAt0, iteratedFDeriv_zero, Pi.zero_apply, zero_apply, mul_zero]

theorem jetP_zero (D : D7) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (s : ℂ)
    (P : MvPolynomial (FVar D T.rank S.rank) ℂ) : jetP S T hS hT s (fun _ => 0) P = 0 := by
  simp only [jetP, jetC_zero, mul_zero, Finset.sum_const_zero]

theorem jetL_zero {ι : Type} [Fintype ι] {a b : ℕ} (cD : ι → ℂ) : jetL cD (fun _ : VCx ι a b => (0 : ℂ)) = 0 := by
  have h : (fun m => jetC cD (fun _ : VCx ι a b => (0 : ℂ)) m) = 0 := funext fun m => jetC_zero cD m
  simp only [jetL, h, map_zero]

theorem toHom_surj {D : D7} (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b)
    (y : (Fin a → D.host.E) →ₗ[D.host.E] Fin b → D.host.E) : ∃ z, toHom S T hS hT z = y :=
  ⟨(Matrix.reindex (finCongr hT) (finCongr hS)).symm (LinearMap.toMatrix' y), by
    unfold toHom
    rw [Equiv.apply_symm_apply, Matrix.toLin'_toMatrix']⟩

theorem supp_per_of_inBox {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {a b : ℕ}
    (SS : Finset (HeightOneSpectrum (𝓞 E))) (cA cB : ℕ) (N : Submodule (𝓞 E) (Formalism.L2.Col.Sp E a))
    (N' : Submodule (𝓞 E) (Formalism.L2.Col.Sp E b)) (Ξ : Formalism.L2.Col.HomE E a b → K)
    (hB : GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree.InBox SS cA cB N N' Ξ) (f : K →+* ℂ) (p : ℂ) :
    (∀ y, p * f (Ξ y) ≠ 0 → ((cA * cB : ℕ) : E) • y ∈ Formalism.L2.Col.homAt SS N N') ∧
    (∀ y, ∀ z ∈ Formalism.L2.Col.homAt SS N N', p * f (Ξ (y + ((cA * cB : ℕ) : E) • z)) = p * f (Ξ y)) := by
  have key : ∀ (n : ℕ) (y : Formalism.L2.Col.HomE E a b), ((n : E) • y) = ((n : 𝓞 E) • y) := fun n y => by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  refine ⟨fun y hy => ?_, fun y z hz => ?_⟩
  · have hx : Ξ y ≠ 0 := fun h0 => hy (by rw [h0, map_zero, mul_zero])
    have h1 := hB.1 y hx
    rw [Formalism.L2.Col.divLat, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply] at h1
    rw [key, Nat.cast_mul, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ h1
  · have hz' : ((cA * cB : ℕ) : E) • z ∈ Formalism.L2.Col.mulLat cB (Formalism.L2.Col.homAt SS N N') := by
      rw [key, Nat.cast_mul, mul_comm, mul_smul]
      exact Submodule.mem_map.2 ⟨_, Submodule.smul_mem _ _ hz, rfl⟩
    rw [hB.2 y _ hz']

theorem jetP_zero' (D : D7) (S T : HSp D) {a b : ℕ} (hS : S.rank = a) (hT : T.rank = b) (s : ℂ)
    (P : MvPolynomial (FVar D T.rank S.rank) ℂ) : jetP S T hS hT s (0 : VCx D.what₂.Tau a b → ℂ) P = 0 :=
  jetP_zero D S T hS hT s P

theorem jetL_zero' {ι : Type} [Fintype ι] {a b : ℕ} (cD : ι → ℂ) : jetL cD (0 : VCx ι a b → ℂ) = 0 := jetL_zero cD

end GlobalTheory.KerTup


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 200000 in
open GlobalTheory.KerTup in
theorem GlobalTheory.KerTup.kernel_identity_tuple : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) ψ θ x vac c₀ kom dd w Ram rd cK, PinX I l Z ψ θ x vac c₀ → PinColL A ι ψ θ x vac c₀ kom dd w Ram rd cK → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) (s : ℂ), (∀ f, IsHol θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) ψ f → ∀ P, pureTensorO ψ θ _ _ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 = jetP _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s (ColDat.xiS θ i hi f) P) → ∀ α γ (c : {c // A.chOf i c = ι i α}) (c' : {c // A.chOf (i + 1) c = ι (i + 1) γ}) P, (volLev (x i).vol (A.U i (ι i α)) : ℂ) * thetaKO (kom i) (A.h i _ c) (A.h (i + 1) _ c') (pureTensorO ψ θ _ _ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (comb ψ _ _ (dd i α γ) (vac i)) P) = cK i * A.abelian₂ i c.1 c'.1 (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) := by
  intro B X I hI hP l Z u a Ch₀ Ch A ι ψ θ x vac c₀ kom dd w Ram rd cK hX hC i hi s hHol α γ c c' P
  obtain ⟨hStd, hGram, hEmb, hcD, hDet⟩ := GlobalTheory.T.trueColumnSteps_are_standardHermitianPairs I hI hP l Z ψ θ hX.std hX.inf
  obtain ⟨hFin, Φ, hSB, hΦv, hTh⟩ := hC.dat i hi α γ
  obtain ⟨hMv, hMv', hΞ⟩ := GlobalTheory.T.movedDatum_eq_finiteDatum_representativePair I hI hP l Z u a Ch₀ A hC.is i hi (ι i α) (ι (i + 1) γ) Φ hSB (w i α γ) hΦv c c'
  obtain ⟨xg, hxg⟩ := hDet _ (A.h i (ι i α) c)
  obtain ⟨yh, hyh⟩ := hDet _ (A.h (i + 1) (ι (i + 1) γ) c')
  have hV := (hX.mv i hi).2 a (A.chr (i + 1)) (kom i) (hC.is.chr ⟨i, hi⟩) (hC.om i hi) (A.h i _ c)
    (hC.is.h i (Nat.le_of_succ_le hi) _ c).1 (A.h (i + 1) _ c') (hC.is.h (i + 1) hi _ c').1 _ _ hMv hMv' xg yh hxg hyh
  have hχ := GlobalTheory.T.chainMove_characters_eq_rho_up_to_base I hI hP l Z u a Ch₀ A hC.is i hi _ _ c c' xg yh hxg hyh
  obtain ⟨hc0, hcov, h2qd⟩ := GlobalTheory.T.tupleLevel_pos_odd_badPrimes_prime_to_level I hI hP u a
  obtain ⟨hXo, hPr, -⟩ := base_fields_primes_ok B X
  have hi' : i < B.R.m := hi
  have hbox := GlobalTheory.LvT.Built.Box.inBox_xiAt B.fields (B.primes X) B.R I.Ch I.sel I.S (I.tup a) (I.cst a) (I.idx a) _ _ u i hXo hPr
    hI.sel_ok (hI.T_mem u) hI.g_mem (hI.idx_ok a) hi' ⟨_, _, _, _, hI.ch_tied⟩ c.1.1 c'.1.1 ((I.stp u a i).rep c.1)
    ((I.stp u a (i + 1)).rep c'.1)
  have hLH := (TC.laHyp_eSmooth_true I hI hP l Z a u i hi').1
  have hLa := (hLH.2.2.2.2.2 _ _ ⟨((I.stp u a i).rep c.1).1.1.deco.2.lat, ((I.stp u a i).rep c.1).1.1.deco.2.uni⟩
    ⟨((I.stp u a (i + 1)).rep c'.1).1.1.deco.2.lat, ((I.stp u a (i + 1)).rep c'.1).1.1.deco.2.uni⟩).2
  have he : B.fields.embC I.A.σ₀ = tauE (I.rec7 l Z) := funext hEmb
  rw [he, ColIn.A_AA] at hLa
  set N := ((I.stp u a i).rep c.1).1.1.deco.1.N with hN
  set N' := ((I.stp u a (i + 1)).rep c'.1).1.1.deco.1.N with hN'
  have hΞ' : ∀ z, Φ (actO _ _ (A.h i _ c)⁻¹ (A.h (i + 1) _ c')⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r)) =
      w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1)
        ((I.stp u a (i + 1)).rep c'.1) (toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) z)) :=
    fun z => hΞ z
  obtain ⟨hsupp, hper⟩ := supp_per_of_inBox _ _ _ _ _ _ hbox B.embLL (w i α γ)
  have hth : I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) =
      thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E)
        (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1
          ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) (I.A.e _ _ N N') := by
    rw [← he]
    have h2 : ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) = I.A.AA := (ColIn.A_AA I).symm
    rw [h2]
    rfl
  have hcore := fun (κ : ℂ) (E : VCx (I.rec7 l Z).what₂.Tau (B.R.N i) (B.R.N (i + 1)) → ℂ) => GlobalTheory.T.thetaKernel_splitPlaces_eq_jet_classicalTheta (I.rec7 l Z) ψ θ _ _ (B.R.N i) (B.R.N (i + 1)) (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi))
    (rankN (I.rec7 l Z) (i + 1) hi) I.A.δ I.A.sc (hStd i hi) s hHol (A.chr (i + 1)) (kom i) (hC.om i hi) A.e (ColIn.Sb I a u)
    hC.is.idem (vac i) Φ (comb ψ _ _ (dd i α γ) (vac i)) (hX.vc i hi) hSB hTh (A.h i _ c) (hC.is.h i (Nat.le_of_succ_le hi) _ c).1
    (A.h (i + 1) _ c') (hC.is.h (i + 1) hi _ c').1 N N' hMv hMv' (levC I.sel (I.tup a) (I.cst a) u) hc0 hcov h2qd hLa
    (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) hΞ' hsupp hper κ E
  have hjet := fun G => jetP_cast (I.rec7 l Z) _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s
    I.J.cD hcD G P
  have hxi0 : (∀ z, A.xi i hi (ι i α) (ι (i + 1) γ) z = 0) →
      ∀ y : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)), B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y) = 0 := by
    intro hz y
    obtain ⟨z, rfl⟩ := toHom_surj _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) y
    have h0 := (GlobalTheory.T.movedDatum_eq_finiteDatum_representativePair I hI hP l Z u a Ch₀ A hC.is i hi (ι i α) (ι (i + 1) γ) Φ hSB 0
      (fun z' => by simp only [hΦv z', hz z', mul_zero]) c c').2.2 z
    have h1 := (GlobalTheory.T.movedDatum_eq_finiteDatum_representativePair I hI hP l Z u a Ch₀ A hC.is i hi (ι i α) (ι (i + 1) γ) Φ hSB 1
      (fun z' => by simp only [hΦv z', hz z', mul_zero]) c c').2.2 z
    rw [h0, zero_mul, one_mul] at h1
    exact h1.symm
  by_cases hm : w i α γ ≠ 0 ∧ ∃ z, A.xi i hi (ι i α) (ι (i + 1) γ) z ≠ 0
  · obtain ⟨hw, hxz⟩ := hm
    have hVE : xiN θ _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) I.A.δ I.A.sc
        (kom i (A.h i _ c, A.h (i + 1) _ c') (vac i)) = fun z => (c₀ i * (A.chr (i + 1) (A.xr i (ι i α)) : ℂ) *
          (A.chr (i + 1) (A.xr (i + 1) (ι (i + 1) γ)) : ℂ)⁻¹ * ((I.chIn u a).rho i c.1 * (I.chIn u a).rho' i c'.1) * w i α γ) *
          ((w i α γ)⁻¹ * I.A.e _ _ N N' z) := by
      refine hV.trans (funext fun z => ?_)
      have h3 : I.A.e _ _ N N' z = I.A.chiF _ _ N N' * I.J.V.thMoved _ _ N N' z := rfl
      rw [h3, mul_assoc (c₀ i), hχ]
      field_simp
    have hwE : (fun z => w i α γ * ((w i α γ)⁻¹ * I.A.e _ _ N N' z)) = I.A.e _ _ N N' :=
      funext fun z => by rw [← mul_assoc, mul_inv_cancel₀ hw, one_mul]
    have hT : jetP _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s
        (thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E)
          (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) (fun z => (w i α γ)⁻¹ * I.A.e _ _ N N' z)) P =
        jetL I.J.cD (I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1))
          (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) := by
      have h6 : thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) (fun z => (w i α γ)⁻¹ * I.A.e _ _ N N' z) =
          I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) :=
        (GlobalTheory.T.classicalThetaOfDatum_smul_move _ _ _ _ _ _ _ _ _ _ _ _).trans ((congrArg (fun G => thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) G) hwE).trans hth.symm)
      exact (congrArg (fun t => jetP _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s t P) h6).trans (hjet _)
    rw [hcore _ _ hVE, hC.cst i hi α γ hxz]
    refine (congrArg (fun t => _ * (_ * t)) hT).trans ?_
    have hT'' : jetL I.J.cD (I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1))
          (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) * ((I.chIn u a).rho i c.1 * (I.chIn u a).rho' i c'.1) = A.abelian₂ i c.1 c'.1 (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) := mul_comm _ _
    refine Eq.trans ?_ (congrArg (fun t => _ * t) hT'')
    ring
  · have hΞz : (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) = fun _ => 0 := by
      funext y
      by_cases hw : w i α γ = 0
      · rw [hw, zero_mul]
      · have hz : ∀ z, A.xi i hi (ι i α) (ι (i + 1) γ) z = 0 := fun z => by_contra fun h => hm ⟨hw, z, h⟩
        rw [hxi0 hz y, mul_zero]
    have hT0 : jetP _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s
        (thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E)
          (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) (I.J.V.thMoved _ _ N N')) P = 0 := by
      have h5 : thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) (fun y => w i α γ * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) (I.J.V.thMoved _ _ N N') = 0 :=
        (congrArg (fun G : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)) → ℂ => thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) G (I.J.V.thMoved _ _ N N')) hΞz).trans (thC_zero _ _ _ _ _ _ _ _ _ _)
      exact (congrArg (fun t => jetP _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s t P) h5).trans (jetP_zero' _ _ _ _ _ s P)
    rw [hcore _ _ hV]
    refine (congrArg (fun t => _ * (_ * t)) hT0).trans ?_
    simp only [mul_zero]
    by_cases hxz : ∃ z, A.xi i hi (ι i α) (ι (i + 1) γ) z ≠ 0
    · have hw : w i α γ = 0 := by
        by_contra hw
        exact hm ⟨hw, hxz⟩
      rw [hC.cst i hi α γ hxz, hw]
      simp
    · have hz : ∀ z, A.xi i hi (ι i α) (ι (i + 1) γ) z = 0 := fun z => by_contra fun h => hxz ⟨z, h⟩
      have hth0 : I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) = 0 := by
        rw [hth]
        have h4 : (fun y => B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) y)) = fun _ => 0 := funext (hxi0 hz)
        exact (congrArg (fun G : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1)) → ℂ => thC (tauE (I.rec7 l Z)) I.A.δ (I.rec7 l Z).host.d I.A.sc ((I.rec7 l Z).host.AA0 : Submodule (𝓞 (I.rec7 l Z).host.E) (I.rec7 l Z).host.E) (ColIn.Sb I a u) N N' (levC I.sel (I.tup a) (I.cst a) u) G (I.A.e _ _ N N')) h4).trans (thC_zero _ _ _ _ _ _ _ _ _ _)
      have hL0 : A.abelian₂ i c.1 c'.1 (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) = 0 := by
        show ((I.chIn u a).rho i c.1 * (I.chIn u a).rho' i c'.1) • jetL I.J.cD (I.th u a i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1))
          (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) = 0
        rw [hth0, jetL_zero', LinearMap.zero_apply, smul_zero]
      exact ((congrArg (fun t => cK i * t) hL0).trans (mul_zero _)).symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIdentityAtEveryTupleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKernelIdentity_at_every_tuple : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch₀ Ch : ℕ → Type) (A : TwDat I l Z u a Ch₀) (ι : ∀ j, Ch j → Ch₀ j) ψ θ x vac c₀ kom dd w Ram rd cK, PinX I l Z ψ θ x vac c₀ → PinColL A ι ψ θ x vac c₀ kom dd w Ram rd cK → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) (s : ℂ), (∀ f, IsHol θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) ψ f → ∀ P, pureTensorO ψ θ _ _ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 = jetP _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) s (ColDat.xiS θ i hi f) P) → ∀ α γ (c : {c // A.chOf i c = ι i α}) (c' : {c // A.chOf (i + 1) c = ι (i + 1) γ}) P, (volLev (x i).vol (A.U i (ι i α)) : ℂ) * thetaKO (kom i) (A.h i _ c) (A.h (i + 1) _ c') (pureTensorO ψ θ _ _ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (comb ψ _ _ (dd i α γ) (vac i)) P) = cK i * A.abelian₂ i c.1 c'.1 (mvZ (fun _ => 1) (fun τ => (s / I.J.cD τ) • 1) (castP (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) P)) := by
  first | exact @GlobalTheory.KerTup.kernel_identity_tuple | exact GlobalTheory.KerTup.kernel_identity_tuple | (intros; apply GlobalTheory.KerTup.kernel_identity_tuple <;> assumption)
end
