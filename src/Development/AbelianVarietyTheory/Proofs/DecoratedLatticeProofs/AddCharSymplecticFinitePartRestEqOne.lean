module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCoefficientVectorReadingRealRepresentation
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransportedSchrodingerStandardLeviAction
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NormOneHomothetyCarriesSelfDualOfSplitComponent
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitNormVectorsOneOrbitSelfDualLatticeSplit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CoprimeScalingIdealValuationLe

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddCharSymplecticFinitePartRestEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfBComponentsMemCompletedLatticeOffConj
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfBComponentsMemCompletedLatticeOffConj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfBComp
open GlobalTheory.AdForm.HalfPairing GlobalTheory.LatVac

theorem comp_mem {D : D7} {S T : HSp D} {N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hc : D.host.ccK = ⊤) (hN : IsSelfDualC S N) {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)}
    (he : Formalism.L2.NTheta.IsIdemAt e P) (h0 : infPart D e = 0) {x : Formalism.L2.Col.HomE D.host.E S.rank T.rank}
    (hx : x ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N')) :
    ((LinearMap.toMatrix' x).map fun r => e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
  obtain ⟨s, hs, hsx⟩ := hx
  have hs' : s ∉ P.asIdeal := hs
  have hne : s ≠ 0 := fun h => hs' (h ▸ zero_mem _)
  have hs0 : (s : D.host.E) ≠ 0 := fun h => hne (RingOfIntegers.ext h)
  have h1 : finPart D (e * incA D ((s : D.host.E)⁻¹)) ∈ intAE D := by
    by_contra h
    exact hs' ((he.2 _ hne).2 h)
  have h4 := GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ h1 _
    (finTens_mem_latO (one_mem_intAf _) (toMatrix_mem_latRat hc hN hsx))
  convert h4 using 1
  ext i j
  rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  refine GlobalTheory.SplitScalar.adele_ext (by simp only [RingHom.map_mul, h0, zero_mul]) ?_
  have h6 : finPart D (finTens 1 (LinearMap.toMatrix' (s • x)) i j) =
      finPart D (incA D ((s : D.host.E) * LinearMap.toMatrix' x i j)) := rfl
  rw [RingHom.map_mul (finPart D) (_ * _), h6, ← RingHom.map_mul, mul_assoc, ← RingHom.map_mul (incA D),
    inv_mul_cancel_left₀ hs0]

theorem halfB_mem_locP {E : Type} [Field E] [NumberField E] [StarRing E] {a b : ℕ}
    {SS : Finset (HeightOneSpectrum (𝓞 E))} {M : Submodule (𝓞 E) (Formalism.L2.Col.HomE E a b)} {c : ℕ} (hc : 0 < c)
    {y : Formalism.L2.Col.HomE E a b} (hy : y ∈ halfBO SS M c) {P : HeightOneSpectrum (𝓞 E)} (hP : P ∈ SS) :
    y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M := by
  have h : ((c : E) ^ expS SS P)⁻¹ • y ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal M := (Submodule.mem_iInf _).1 hy P
  have he : expS SS P = 1 := by
    unfold expS; rw [if_pos hP]
  have hc' : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  rw [he, zpow_one] at h
  have := nsmul_mem h c
  rwa [← Nat.cast_smul_eq_nsmul E, smul_smul, mul_inv_cancel₀ hc', one_smul] at this


set_option maxHeartbeats 1000000 in
theorem ybmem : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y')) - ((LinearMap.toMatrix' y').map fun r => cA D e * incA D r) ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  intro D ψ θ S T δ sc hP e SS hE h2 N N' hN hN' c hc hcQ x' hx
  have hc0 : (c : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have hA : ((LinearMap.toMatrix' x').map fun r => e * incA D r : WO S T) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True := by
    obtain ⟨⟨es, hes, rfl⟩, -⟩ := hE
    have e1 : ((LinearMap.toMatrix' x').map fun r => (∑ PP ∈ SS, es PP) * incA D r : WO S T) =
        ∑ PP ∈ SS, ((LinearMap.toMatrix' x').map fun r => (es PP) * incA D r : WO S T) := by
      ext i j
      rw [Matrix.map_apply, Matrix.sum_apply, Finset.sum_mul]
      rfl
    rw [e1]
    refine sum_mem fun PP hPP => comp_mem hP.cc hN (hes PP hPP) ?_ (halfB_mem_locP hc hx hPP)
    exact GlobalTheory.PlaceVec.idemSum_infPart (P := {PP}) ⟨⟨es, fun Q hQ => by
      rw [Finset.mem_singleton.1 hQ]; exact hes PP hPP, (Finset.sum_singleton _ _).symm⟩, (hes PP hPP).1.2.1⟩
  have hcx : ((c : D.host.E) • x') ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N' :=
    GlobalTheory.ThetaMove.mem_of_locP fun Q => smul_mem_locP hc hx Q
  have hloc : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), ¬ (Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) →
      x' ∈ Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') := by
    intro Q hQ
    have h : ((c : D.host.E) ^ expS SS Q)⁻¹ • x' ∈
        Formalism.HermitianLatticesTheory.localization₂ Q.asIdeal (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') :=
      (Submodule.mem_iInf _).1 hx Q
    have he : expS SS Q = 0 := by
      unfold expS; rw [if_neg fun h => hQ (Or.inl h), if_neg fun h => hQ (Or.inr h)]
    rwa [he, zpow_zero, _root_.inv_one, one_smul] at h
  obtain ⟨d, hd0, hdx, hdQ⟩ := GlobalTheory.T.exists_denominator_avoiding_given_primes D.host.E S.rank T.rank _
    (fun Q => Q ∈ SS ∨ Formalism.L2.Col.conjPrime₂ Q ∈ SS) c hc x' hcx hloc
  obtain ⟨a₁, a₂, ha₁, ha₂, ho⟩ := GlobalTheory.T.offIdempotent_mem_ideal_two_integers D e SS hE c hc d hd0 hdQ
  have hB : a₁ • GlobalTheory.LatVac.finTens 1 (LinearMap.toMatrix' ((c : D.host.E) • x')) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True :=
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ha₁ _
      (GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) (toMatrix_mem_latRat hP.cc hN hcx))
  have hC : a₂ • GlobalTheory.LatVac.finTens 1 (LinearMap.toMatrix' ((d : D.host.E) • x')) ∈
      latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True :=
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ _ ha₂ _
      (GlobalTheory.LatVac.finTens_mem_latO (GlobalTheory.LatVac.one_mem_intAf _) (toMatrix_mem_latRat hP.cc hN hdx))
  convert add_mem hA (add_mem hB hC) using 1
  have hinf := GlobalTheory.PlaceVec.idemSum_infPart hE
  have hinfc := GlobalTheory.PlaceVec.infPart_cA hinf
  have i1 : ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) i j,
      infPart D (GlobalTheory.VacUnique.finRat S T M i j) = 0 := fun M i j => by
    have := congrFun (congrFun (GlobalTheory.VacUnique.finRat_inf S T M) i) j
    simpa using this
  have f1 : ∀ (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) i j,
      finPart D (GlobalTheory.VacUnique.finRat S T M i j) = finPart D (incA D (M i j)) := fun M i j => by
    rw [GlobalTheory.LatVacSign.finRat_eq]; rfl
  rw [← GlobalTheory.LatVacSign.finRat_eq, ← GlobalTheory.LatVacSign.finRat_eq]
  ext i j
  rw [Matrix.sub_apply, Matrix.add_apply, Matrix.add_apply, Matrix.map_apply, Matrix.map_apply, Matrix.smul_apply,
    Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · rw [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_mul, RingHom.map_mul,
      RingHom.map_mul, i1, i1, i1, hinf, hinfc]
    simp only [mul_zero, zero_mul, sub_zero, add_zero]
  · have hs : ∀ r : D.host.E, LinearMap.toMatrix' (r • x') i j = r * LinearMap.toMatrix' x' i j := fun r => by
      rw [map_smul]; rfl
    have ho' := congrArg (finPart D) ho
    rw [RingHom.map_sub, RingHom.map_sub, RingHom.map_one, RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_mul] at ho'
    rw [RingHom.map_sub, RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_mul, RingHom.map_mul,
      RingHom.map_mul, f1, f1, f1, hs, hs, RingHom.map_mul (incA D), RingHom.map_mul (incA D), RingHom.map_mul (finPart D),
      RingHom.map_mul (finPart D)]
    linear_combination (finPart D (incA D (LinearMap.toMatrix' x' i j))) * ho'

end GlobalTheory.HalfBComp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HalfBComponentsMemCompletedLatticeOffConjStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfB_components_mem_completedLattice_offConj : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y')) - ((LinearMap.toMatrix' y').map fun r => cA D e * incA D r) ∈ (latO S T (N : Set (Fin S.rank → D.host.E)) (N' : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  first | exact @GlobalTheory.HalfBComp.ybmem | exact GlobalTheory.HalfBComp.ybmem | (intros; apply GlobalTheory.HalfBComp.ybmem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddCharSymplecticFinitePartRestEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.FinRestComm

variable {D : D7}

theorem finPart_finRat_sub {S T : HSp D} (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (i : Fin T.rank)
    (j : Fin S.rank) : finPart D (GlobalTheory.VacUnique.finRat S T M i j - incA D (M i j)) = 0 := by
  rw [RingHom.map_sub]
  exact sub_eq_zero.2 ((GlobalTheory.LatVac.finPart_pair 1 (M i j)).trans (GlobalTheory.LatVac.finPart_incA (M i j)).symm)

theorem infPart_of_idemSum {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (hI : IsIdemSum e SS) :
    infPart D e = 0 := by
  obtain ⟨⟨es, hes, he⟩, -⟩ := hI
  subst he
  induction SS using Finset.induction_on with
  | empty => rw [Finset.sum_empty, RingHom.map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, RingHom.map_add (f := _), GlobalTheory.SplitScalar.infPart_splitIdem (hes a (Finset.mem_insert_self a s)).1,
      ih fun PP hPP => hes PP (Finset.mem_insert_of_mem hPP), add_zero]

theorem smul_rest_eq_zero {S T : HSp D} {e : AE D} (hee : e * e = e) (hinf : infPart D e = 0)
    (M : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    e • (GlobalTheory.VacUnique.finRat S T M - M.map (fun r => e * incA D r)) = 0 := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.zero_apply, smul_eq_mul, mul_sub,
    ← mul_assoc, hee, ← mul_sub]
  refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
  · rw [RingHom.map_mul, hinf, zero_mul, RingHom.map_zero]
  · rw [RingHom.map_mul, finPart_finRat_sub, mul_zero, RingHom.map_zero]

theorem char_sympl_rest_eq_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ψ (symplO S T ((GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r)) (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y'))) = 1 := by
  intro D ψ θ S T δ sc hP e SS hI h2 N N' hN hN' c hc hcP x' hx' y' hy'
  have hZ := GlobalTheory.T.halfA_components_mem_completedLattice_offPrimes D ψ θ S T δ sc hP e SS hI h2 N N' hN hN' c hc hcP x' hx'
  have hY := GlobalTheory.T.halfB_components_mem_completedLattice_offConj D ψ θ S T δ sc hP e SS hI h2 N N' hN hN' c hc hcP y' hy'
  have heZ := smul_rest_eq_zero (S := S) (T := T) (GlobalTheory.PlaceDatum.idemSum_mul_self hI) (infPart_of_idemSum hI)
    (LinearMap.toMatrix' x')
  have hsplit : GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y') =
      (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y') -
        (LinearMap.toMatrix' y').map (fun r => cA D e * incA D r)) +
      cA D e • (LinearMap.toMatrix' y').map (incA D) := by
    have : (LinearMap.toMatrix' y').map (fun r => cA D e * incA D r) =
        cA D e • (LinearMap.toMatrix' y').map (incA D) := Matrix.ext fun i j => rfl
    rw [this, sub_add_cancel]
  rw [hsplit, ← GlobalTheory.LatVac.symplHom_apply, map_add (f := _), AddChar.map_add_eq_mul, GlobalTheory.LatVac.symplHom_apply,
    GlobalTheory.LatVac.symplHom_apply, ← GlobalTheory.SplitScalar.symplO_smul, heZ, GlobalTheory.SplitScalar.symplO_zero_left,
    AddChar.map_zero_eq_one, mul_one]
  exact GlobalTheory.LatVac.char_sympl_eq_one hP.std hN hN' hZ hY

end GlobalTheory.FinRestComm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AddCharSymplecticFinitePartRestEqOneStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addChar_symplectic_finitePartRest_eq_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (N : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S N → IsSelfDualC T N' → ∀ (c : ℕ), 0 < c → Odd c → ∀ x' ∈ halfAO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∀ y' ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ψ (symplO S T ((GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' x')) - ((LinearMap.toMatrix' x').map fun r => e * incA D r)) (GlobalTheory.VacUnique.finRat S T (LinearMap.toMatrix' y'))) = 1 := by
  first | exact @GlobalTheory.FinRestComm.char_sympl_rest_eq_one | exact GlobalTheory.FinRestComm.char_sympl_rest_eq_one | (intros; apply GlobalTheory.FinRestComm.char_sympl_rest_eq_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduePairStabilizerKeepsIntegralLastCoordDiv
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduePairStabilizerKeepsIntegralLastCoordDiv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm

namespace GlobalTheory.PairKeep

theorem res_zero_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (c τ : k) (q : Unif k) (hτ : valuation k τ = valuation k ((q.1 : 𝒪[k]) : k)) (hc : valuation k c = 1)
    (x : k) (s : 𝒪[k]) (hs : (s : k) = c * x) :
    IsLocalRing.residue 𝒪[k] s = 0 ↔ ∃ t ∈ 𝒪[k], x = τ * t := by
  have hq := q.ne_zero
  have hvq : valuation k ((q.1 : 𝒪[k]) : k) ≠ 0 := by simpa using hq
  have hτ0 : τ ≠ 0 := by
    intro h; rw [h, map_zero] at hτ; exact hvq hτ.symm
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hc; exact zero_ne_one hc
  rw [IsLocalRing.residue_eq_zero_iff, q.mem_max_iff]
  constructor
  · rintro ⟨t, ht⟩
    have h1 : ((q.1 : 𝒪[k]) : k) / (c * τ) ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_div₀, map_mul, hc, hτ, one_mul, div_self hvq]
    refine ⟨_, mul_mem h1 t.2, ?_⟩
    have h2 : c * x = ((q.1 : 𝒪[k]) : k) * (t : k) := by rw [← hs, ht]; rfl
    field_simp
    linear_combination h2
  · rintro ⟨t, ht, rfl⟩
    have h1 : (c * τ) / ((q.1 : 𝒪[k]) : k) ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_div₀, map_mul, hc, hτ, one_mul, div_self hvq]
    refine ⟨⟨_, mul_mem h1 ht⟩, Subtype.ext ?_⟩
    rw [hs]
    change _ = ((q.1 : 𝒪[k]) : k) * (c * τ / ((q.1 : 𝒪[k]) : k) * t)
    field_simp

theorem keep : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m' m : ℕ) (hm : m' = m) (b b' : Matrix (Fin m') (Fin m') k), b * b' = 1 → b' * b = 1 →
    ∀ P : Pair k (Fin m'), (∀ x, x ∈ P.lat ↔ ∀ r, (b *ᵥ x) r ∈ 𝒪[k]) →
    ∀ (c τ : k) (q : Unif k), valuation k τ = valuation k ((q.1 : 𝒪[k]) : k) → valuation k c = 1 →
    (∀ u : Fin m' → k, (∀ r, u r ∈ 𝒪[k]) → ∀ r0 : Fin m', r0.1 + 1 = m' →
      ∃ s : 𝒪[k], (s : k) = c * u r0 ∧ P.HasVal (b' *ᵥ u) (IsLocalRing.residue 𝒪[k] s)) →
    ∀ g : GL (Fin m') k, g • P = P →
      (b * g.val * b').reindex (finCongr hm) (finCongr hm) * (b * (g⁻¹).val * b').reindex (finCongr hm) (finCongr hm) = 1 ∧
      (∀ u : Fin m → k, ((∀ r, u r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m → ∃ s ∈ 𝒪[k], u r0 = τ * s) ↔
        ((∀ r, ((b * g.val * b').reindex (finCongr hm) (finCongr hm) *ᵥ u) r ∈ 𝒪[k]) ∧
          ∀ r0 : Fin m, r0.1 + 1 = m → ∃ s ∈ 𝒪[k], ((b * g.val * b').reindex (finCongr hm) (finCongr hm) *ᵥ u) r0 = τ * s)) ∧
      (∀ u : Fin m → k, (∀ r, u r ∈ 𝒪[k]) ↔
        ∀ r, (((b * (g⁻¹).val * b').reindex (finCongr hm) (finCongr hm))ᵀ *ᵥ u) r ∈ 𝒪[k]) := by
  intro k _ _ _ _ m' m hm b b' hbb hb'b P hP c τ q hτ hc hval g hg
  subst hm
  simp only [finCongr_refl, Matrix.reindex_refl_refl]
  have hmul : ∀ g₁ g₂ : GL (Fin m') k, g₁ * g₂ = 1 → (b * g₁.val * b') * (b * g₂.val * b') = 1 := by
    intro g₁ g₂ h
    have h' : g₁.val * g₂.val = 1 := by rw [← Units.val_mul, h, Units.val_one]
    calc (b * g₁.val * b') * (b * g₂.val * b') = b * (g₁.val * (b' * b) * g₂.val) * b' := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hb'b, Matrix.mul_one, h', Matrix.mul_one, hbb]
  have hb' : ∀ (g : GL (Fin m') k) (u : Fin m' → k), b' *ᵥ ((b * g.val * b') *ᵥ u) = g • (b' *ᵥ u) := by
    intro g u
    change _ = g.val *ᵥ (b' *ᵥ u)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hb'b, Matrix.one_mul]
  have hlat : ∀ u : Fin m' → k, b' *ᵥ u ∈ P.lat ↔ ∀ r, u r ∈ 𝒪[k] := by
    intro u
    rw [hP, Matrix.mulVec_mulVec, hbb, Matrix.one_mulVec]
  have hint : ∀ g : GL (Fin m') k, g • P = P → ∀ u : Fin m' → k, (∀ r, u r ∈ 𝒪[k]) →
      ∀ r, ((b * g.val * b') *ᵥ u) r ∈ 𝒪[k] := by
    intro g hg u hu
    rw [← hlat, hb']
    have := ((P.hasVal_fn ⟨_, (hlat u).2 hu⟩).gl_smul g)
    rw [hg] at this
    exact this.mem
  have hlast : ∀ g : GL (Fin m') k, g • P = P → ∀ u : Fin m' → k,
      ((∀ r, u r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m', r0.1 + 1 = m' → ∃ s ∈ 𝒪[k], u r0 = τ * s) →
      ((∀ r, ((b * g.val * b') *ᵥ u) r ∈ 𝒪[k]) ∧
        ∀ r0 : Fin m', r0.1 + 1 = m' → ∃ s ∈ 𝒪[k], ((b * g.val * b') *ᵥ u) r0 = τ * s) := by
    intro g hg u ⟨hu, hu'⟩
    refine ⟨hint g hg u hu, fun r0 hr0 => ?_⟩
    obtain ⟨s, hs, hv⟩ := hval u hu r0 hr0
    obtain ⟨s', hs', hv'⟩ := hval _ (hint g hg u hu) r0 hr0
    have h1 := hv.gl_smul g
    rw [hg, ← hb'] at h1
    rw [← res_zero_iff c τ q hτ hc _ s' hs', hv'.unique h1, res_zero_iff c τ q hτ hc _ s hs]
    exact hu' r0 hr0
  have htr : ∀ g : GL (Fin m') k, g • P = P → ∀ u : Fin m' → k, (∀ r, u r ∈ 𝒪[k]) →
      ∀ r, ((b * g.val * b')ᵀ *ᵥ u) r ∈ 𝒪[k] := by
    intro g hg u hu r
    have h1 := hint g hg (Pi.single r 1) (fun j => by
      rw [Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _])
    rw [Matrix.mulVec_single_one] at h1
    change ∑ j, (b * g.val * b')ᵀ r j * u j ∈ 𝒪[k]
    exact sum_mem fun j _ => mul_mem (h1 j) (hu j)
  have hg' : g⁻¹ • P = P := by rw [inv_smul_eq_iff, hg]
  refine ⟨hmul _ _ (mul_inv_cancel g), fun u => ⟨hlast g hg u, fun h => ?_⟩, fun u => ⟨htr _ hg' u, fun h => ?_⟩⟩
  · have := hlast _ hg' _ h
    rwa [Matrix.mulVec_mulVec, hmul _ _ (inv_mul_cancel g), Matrix.one_mulVec] at this
  · have := htr _ hg _ h
    rwa [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hmul _ _ (inv_mul_cancel g), Matrix.transpose_one,
      Matrix.one_mulVec] at this

end GlobalTheory.PairKeep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduePairStabilizerKeepsIntegralLastCoordDivStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residuePairStabilizer_keeps_integralLastCoordDiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m' m : ℕ) (hm : m' = m) (b b' : Matrix (Fin m') (Fin m') k), b * b' = 1 → b' * b = 1 →
    ∀ P : Pair k (Fin m'), (∀ x, x ∈ P.lat ↔ ∀ r, (b *ᵥ x) r ∈ 𝒪[k]) →
    ∀ (c τ : k) (q : Unif k), valuation k τ = valuation k ((q.1 : 𝒪[k]) : k) → valuation k c = 1 →
    (∀ u : Fin m' → k, (∀ r, u r ∈ 𝒪[k]) → ∀ r0 : Fin m', r0.1 + 1 = m' →
      ∃ s : 𝒪[k], (s : k) = c * u r0 ∧ P.HasVal (b' *ᵥ u) (IsLocalRing.residue 𝒪[k] s)) →
    ∀ g : GL (Fin m') k, g • P = P →
      (b * g.val * b').reindex (finCongr hm) (finCongr hm) * (b * (g⁻¹).val * b').reindex (finCongr hm) (finCongr hm) = 1 ∧
      (∀ u : Fin m → k, ((∀ r, u r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m → ∃ s ∈ 𝒪[k], u r0 = τ * s) ↔
        ((∀ r, ((b * g.val * b').reindex (finCongr hm) (finCongr hm) *ᵥ u) r ∈ 𝒪[k]) ∧
          ∀ r0 : Fin m, r0.1 + 1 = m → ∃ s ∈ 𝒪[k], ((b * g.val * b').reindex (finCongr hm) (finCongr hm) *ᵥ u) r0 = τ * s)) ∧
      (∀ u : Fin m → k, (∀ r, u r ∈ 𝒪[k]) ↔
        ∀ r, (((b * (g⁻¹).val * b').reindex (finCongr hm) (finCongr hm))ᵀ *ᵥ u) r ∈ 𝒪[k]) := by
  first | exact @GlobalTheory.PairKeep.keep | exact GlobalTheory.PairKeep.keep | (intros; apply GlobalTheory.PairKeep.keep <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesSameSplitShapeCarriedByCentral
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesSameSplitShapeCarriedByCentral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch


set_option maxHeartbeats 1000000 in
theorem sMoves_of_wShape : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S S₀ A Ln : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A Ln) (ζ : Fin Ln.rank → D.host.E) (L L' : Lat S) (N N' : Lat A) (α α' β β' : Fin ρ → k) (γ δ c₀ : k) (a₀ : GA D A), IsLineVec Ln ζ → IsSelfDualC S L → IsSelfDualC S L' → WShape p d o ζ L α α' γ 1 N → WShape p d o ζ L' β β' δ a₀ N' → latV A N (· = p.v) = latV A N' (· = p.v) → c₀ ≠ 0 → (∀ i, valuation k (β i * c₀) = valuation k (α i)) → (∀ i, valuation k (β' i * c₀) = valuation k (α' i)) → valuation k (δ * c₀) = valuation k γ → ∃ (a : GA D A) (c : AE D), CenAt A p.v a ∧ NormOneAt p.v c ∧ SMoves S c (embA d o (a₀ * a)) L L' p.v := by
  intro D k _ _ _ _ p S S₀ A Ln ρ d o ζ L L' N N' α α' β β' γ δ c₀ a₀ hζ hL hL' hW hW' hN hc₀ hb hb' hd
  obtain ⟨c, hc, hpc⟩ := GlobalTheory.T.exists_normOneIdele_with_splitPlace_component D k p c₀ hc₀
  obtain ⟨c', hc', hpc'⟩ := GlobalTheory.T.exists_normOneIdele_with_splitPlace_component D k p c₀⁻¹ (inv_ne_zero hc₀)
  obtain ⟨a, haC, ha⟩ := GlobalTheory.T.exists_centralUnitary_scalar_of_normOneIdele D A p.v c' hc'
  refine ⟨a, c, haC, hc, ?_⟩
  apply GlobalTheory.T.normOneHomothety_carries_selfDual_of_splitComponent D k p S L L' c _ hL hL' hc
  set f : D.host.E →+* k := p.pr.comp (incA D) with hf
  have hatW : ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E), atW p X = X.map f := fun _ => rfl
  have hrat : ∀ {m n : ℕ} (X : Matrix (Fin m) (Fin n) D.host.E), atW p X = (rat X).map p.pr := fun _ => rfl
  have hkey : ∀ {n m l : ℕ} (M : Matrix (Fin n) (Fin l) (AE D)) (R : Matrix (Fin l) (Fin m) (AE D))
      (u : Fin m → k), M.map p.pr *ᵥ (R.map p.pr *ᵥ u) = (M * R).map p.pr *ᵥ u := by
    intro n m l M R u; rw [Matrix.mulVec_mulVec, Matrix.map_mul]

  have hsum : atW p d.e * atW p d.qX + atW p d.i₀ * atW p d.q0 + atW p d.e' * atW p d.qY = 1 := by
    simp only [hatW]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add f), ← Matrix.map_add _ (map_add f), d.sum_eq_one_rat,
      Matrix.map_one _ (map_zero f) (map_one f)]
  have hsumA : atW p o.iA * atW p o.qA + atW p o.iB * atW p o.qB = 1 := by
    simp only [hatW]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add f), o.iA_qA_add, Matrix.map_one _ (map_zero f) (map_one f)]
  have hrk : Ln.rank = 1 := hζ.1
  have j0 : Fin Ln.rank := ⟨0, by omega⟩
  have huniq : ∀ j : Fin Ln.rank, j = j0 := fun j => Fin.ext (by have := j.2; have := j0.2; omega)
  have hζ0 : ζ j0 ≠ 0 := by
    intro h0
    apply hζ.2
    have : ζ = 0 := funext fun j => by rw [huniq j, h0]; rfl
    simp [this]
  have hfζ : f (ζ j0) ≠ 0 := fun h => hζ0 (f.injective (by rw [h, map_zero]))
  set ζk : Fin Ln.rank → k := fun j => f (ζ j) with hζk
  set zv : Fin S.rank → k := fun r' => p.pr (incA D ((d.i₀ *ᵥ vecB o ζ) r')) with hzv
  have hz : zv = atW p (d.i₀ * o.iB) *ᵥ ζk := by
    funext r
    simp only [hzv, vecB, Matrix.mulVec_mulVec]
    exact RingHom.map_mulVec f (d.i₀ * o.iB) ζ r
  have hdec : ∀ x : Fin S.rank → k, ∃ (x1 x2 : Fin ρ → k) (t : k) (y : Fin A.rank → k),
      x = atW p d.e *ᵥ x1 + atW p d.e' *ᵥ x2 + t • zv +
        atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A 1).map p.pr *ᵥ y) := by
   intro x
   set x0 := atW p d.q0 *ᵥ x
   set w := atW p o.qB *ᵥ x0
   set y := atW p o.qA *ᵥ x0
   set t := w j0 / f (ζ j0)
   have hw : w = t • ζk := by
     funext j; rw [huniq j]; simp only [Pi.smul_apply, smul_eq_mul, hζk, t]; field_simp
   have hx : x = atW p d.e *ᵥ (atW p d.qX *ᵥ x) + atW p d.e' *ᵥ (atW p d.qY *ᵥ x) + t • zv +
       atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A 1).map p.pr *ᵥ y) := by
     rw [mt_one, Matrix.map_one _ (map_zero p.pr) (map_one p.pr), Matrix.one_mulVec, hz, ← Matrix.mulVec_smul, ← hw]
     have hm : atW p d.i₀ * (atW p o.iA * atW p o.qA + atW p o.iB * atW p o.qB) * atW p d.q0 =
         atW p d.i₀ * atW p d.q0 := by rw [hsumA, Matrix.mul_one]
     have h0 : atW p (d.i₀ * o.iA) *ᵥ y + atW p (d.i₀ * o.iB) *ᵥ w = atW p d.i₀ *ᵥ x0 := by
       simp only [y, w, x0, hatW, Matrix.map_mul, Matrix.mulVec_mulVec, ← Matrix.add_mulVec]
       simp only [← hatW]
       rw [← hm]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
     calc x = (1 : Matrix (Fin S.rank) (Fin S.rank) k) *ᵥ x := (Matrix.one_mulVec x).symm
       _ = _ := by
         rw [← hsum, Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
           ← Matrix.mulVec_mulVec, ← h0]
         abel
   exact ⟨_, _, _, _, hx⟩
  intro x
  obtain ⟨x1, x2, t, y, rfl⟩ := hdec x
  rw [hW x1 x2 t y]
  have jX : rat d.e = d.jX := rfl
  have jY : rat d.e' = d.jY := rfl
  have jA : rat (d.i₀ * o.iA) = d.j0 * o.jA := rat_mul _ _
  have jB : rat (d.i₀ * o.iB) = d.j0 * o.jB := rat_mul _ _
  have hGX : Formalism.L2.Theta.mt S (embA d o (a₀ ⬝ a)) ⬝ d.jX = d.jX := d.wittDecomp_anisotropicEmbedding_inclX _
  have hGY : Formalism.L2.Theta.mt S (embA d o (a₀ ⬝ a)) ⬝ d.jY = d.jY := d.wittDecomp_anisotropicEmbedding_inclY _
  have hG0' : Formalism.L2.Theta.mt S (embA d o (a₀ ⬝ a)) ⬝ d.j0 = d.j0 ⬝ Formalism.L2.Theta.mt S₀ (o.emb (a₀ ⬝ a, 1)) :=
    d.wittDecomp_anisotropicEmbedding_inclAnisotropic _
  have hG0 : ∀ {m : ℕ} (R : Matrix (Fin S₀.rank) (Fin m) (AE D)), Formalism.L2.Theta.mt S (embA d o (a₀ ⬝ a)) ⬝ (d.j0 ⬝ R) =
      d.j0 ⬝ (Formalism.L2.Theta.mt S₀ (o.emb (a₀ ⬝ a, 1)) ⬝ R) := by
    intro m R; rw [← Matrix.mul_assoc, hG0', Matrix.mul_assoc]
  have hBB : Formalism.L2.Theta.mt S₀ (o.emb (a₀ ⬝ a, 1)) ⬝ o.jB = o.jB := by rw [o.emb_jB, mt_one, Matrix.mul_one]
  have hAA : Formalism.L2.Theta.mt S₀ (o.emb (a₀ ⬝ a, 1)) ⬝ o.jA = o.jA ⬝ (Formalism.L2.Theta.mt A a₀ ⬝ Formalism.L2.Theta.mt A a) := by
    rw [o.emb_jA, mt_mul]
  set G := Formalism.L2.Theta.mt S (embA d o (a₀ * a)) with hG
  have T1 : G.map p.pr *ᵥ (atW p d.e *ᵥ x1) = atW p d.e *ᵥ x1 := by rw [hrat, hkey, jX, hGX]
  have T2 : G.map p.pr *ᵥ (atW p d.e' *ᵥ x2) = atW p d.e' *ᵥ x2 := by rw [hrat, hkey, jY, hGY]
  have hz' : zv = (d.j0 ⬝ o.jB).map p.pr *ᵥ ζk := by
    rw [← jB]; exact hz
  have T3 : G.map p.pr *ᵥ zv = zv := by
    rw [hz', hkey, hG0, hBB]
  have hms : ∀ {m n : ℕ} (r : AE D) (X : Matrix (Fin m) (Fin n) (AE D)), (r • X).map p.pr = p.pr r • X.map p.pr := by
    intro m n r X; ext i j; simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  have T4 : G.map p.pr *ᵥ (atW p (d.i₀ * o.iA) *ᵥ y) =
      c₀⁻¹ • (atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A a₀).map p.pr *ᵥ y)) := by
    rw [hrat, hkey, hkey, jA, hG0, hAA, ha, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_smul,
      hms, Matrix.smul_mulVec, hpc', Matrix.mul_assoc]
  have himg : p.pr c • (G.map p.pr *ᵥ (atW p d.e *ᵥ x1 + atW p d.e' *ᵥ x2 + t • zv +
      atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A 1).map p.pr *ᵥ y))) =
      atW p d.e *ᵥ (c₀ • x1) + atW p d.e' *ᵥ (c₀ • x2) + (c₀ * t) • zv +
        atW p (d.i₀ * o.iA) *ᵥ ((Formalism.L2.Theta.mt A a₀).map p.pr *ᵥ y) := by
    rw [mt_one, Matrix.map_one _ (map_zero p.pr) (map_one p.pr), Matrix.one_mulVec, Matrix.mulVec_add,
      Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, T1, T2, T3, T4, hpc]
    simp only [smul_add, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hc₀, one_smul]
  rw [himg, hW' (c₀ • x1) (c₀ • x2) (c₀ * t) y, hN]
  have hval : ∀ u u' z : k, valuation k (u * c₀) = valuation k u' → (u * (c₀ * z) ∈ 𝒪[k] ↔ u' * z ∈ 𝒪[k]) := by
    intro u u' z h
    rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, ← mul_assoc, map_mul, h, ← map_mul]
  refine and_congr (forall_congr' fun i => (hval _ _ _ (hb i)).symm)
    (and_congr (forall_congr' fun i => (hval _ _ _ (hb' i)).symm) (and_congr (hval _ _ _ hd).symm Iff.rfl))

end GlobalTheory.Core.Mi.LatMatch

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticesSameSplitShapeCarriedByCentralStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattices_same_splitShape_carried_by_central : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S S₀ A Ln : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A Ln) (ζ : Fin Ln.rank → D.host.E) (L L' : Lat S) (N N' : Lat A) (α α' β β' : Fin ρ → k) (γ δ c₀ : k) (a₀ : GA D A), IsLineVec Ln ζ → IsSelfDualC S L → IsSelfDualC S L' → WShape p d o ζ L α α' γ 1 N → WShape p d o ζ L' β β' δ a₀ N' → latV A N (· = p.v) = latV A N' (· = p.v) → c₀ ≠ 0 → (∀ i, valuation k (β i * c₀) = valuation k (α i)) → (∀ i, valuation k (β' i * c₀) = valuation k (α' i)) → valuation k (δ * c₀) = valuation k γ → ∃ (a : GA D A) (c : AE D), CenAt A p.v a ∧ NormOneAt p.v c ∧ SMoves S c (embA d o (a₀ * a)) L L' p.v := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.sMoves_of_wShape | exact GlobalTheory.Core.Mi.LatMatch.sMoves_of_wShape | (intros; apply GlobalTheory.Core.Mi.LatMatch.sMoves_of_wShape <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeSplitsOffUnitNormLineAtPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeSplitsOffUnitNormLineAtPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch.SplitOff

variable {D : D7}

theorem hermAt_eq (S : HSp D) (x y : Fin S.rank → AE D) :
    GlobalTheory.IwaPlace.hermAt S x y = (fun i => cA D (y i)) ⬝ᵥ (gA S *ᵥ x) := by
  simp only [GlobalTheory.IwaPlace.hermAt, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hermAt_mulVec (S : HSp D) {k : ℕ} (a : Mx D S.rank k) (x : Fin S.rank → AE D) (y : Fin k → AE D) :
    GlobalTheory.IwaPlace.hermAt S x (a *ᵥ y) = (fun i => cA D (y i)) ⬝ᵥ ((adj a ⬝ gA S) *ᵥ x) := by
  have h : (fun i => cA D ((a *ᵥ y) i)) = (fun i => cA D (y i)) ᵥ* adj a := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hermAt_eq, h, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec _ (adj a)]

theorem hermAt_jB {S A B : HSp D} (o : OrthDec S A B) (y : Fin S.rank → AE D) (l : Fin B.rank → AE D) :
    GlobalTheory.IwaPlace.hermAt S y (o.jB *ᵥ l) = GlobalTheory.IwaPlace.hermAt B (o.pB *ᵥ y) l := by
  rw [hermAt_mulVec, hermAt_eq, Matrix.mulVec_mulVec, o.pB_eq, ← Matrix.mul_assoc (gA B), gA_mul_giA, Matrix.one_mul]

theorem ratV_vecB {S A L : HSp D} (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) :
    ratV (vecB o ζ) = o.jB *ᵥ ratV ζ :=
  funext fun i => RingHom.map_mulVec (incA D) o.iB ζ i

theorem hermAt_smul (S : HSp D) (c a : AE D) (x y : Fin S.rank → AE D) :
    GlobalTheory.IwaPlace.hermAt S (c • x) (a • y) = c * cA D a * GlobalTheory.IwaPlace.hermAt S x y := by
  simp only [GlobalTheory.IwaPlace.hermAt, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem cA_incA (e : D.host.E) : cA D (incA D e) = incA D (star e) := rfl

theorem hermAt_ratV (S : HSp D) (x : Fin S.rank → D.host.E) :
    GlobalTheory.IwaPlace.hermAt S (ratV x) (ratV x) = incA D (star x ⬝ᵥ S.gram *ᵥ x) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [GlobalTheory.IwaPlace.hermAt, gA, rat, ratV, Matrix.map_apply, dotProduct, Matrix.mulVec, map_sum, map_mul,
    Finset.mul_sum, cA_incA, Pi.star_apply, mul_assoc]

end GlobalTheory.Core.Mi.LatMatch.SplitOff

namespace GlobalTheory.Core.Mi.LatMatch.SplitOff

variable {D : D7}

theorem eps_mem_idV (v : GlobalTheory.FinPl.Pl D) :
    algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) ∈ idV (1 : FI D) v := by
  apply AddSubgroup.subset_closure
  refine ⟨GlobalTheory.SelfDualAt.indP (· = v), ?_, ?_, 1, ?_, ?_⟩
  · intro w
    rw [GlobalTheory.SelfDualAt.evalV_indP]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · intro w hw
    rw [GlobalTheory.SelfDualAt.evalV_indP, if_neg hw]
  · exact FractionalIdeal.one_mem_one _
  · rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rfl

theorem incA_mul_mem_idV (c : D.host.E) {𝔞 : FI D} {v : GlobalTheory.FinPl.Pl D} {x : AE D} (hx : x ∈ idV 𝔞 v) :
    incA D c * x ∈ idV (FractionalIdeal.spanSingleton _ c * 𝔞) v := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨α, h1, h2, a, ha, rfl⟩ := hy
    apply AddSubgroup.subset_closure
    refine ⟨α, h1, h2, c * a, FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) ha, ?_⟩
    change ((1 : AF D.host.F) ⊗ₜ[D.host.F] c) * (_ ⊗ₜ[D.host.F] _) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem natInv_mul_mem_intAt {T : ℕ} {v : GlobalTheory.FinPl.Pl D} (hT : (T : 𝓞 D.host.F) ∉ v.asIdeal) {x : AE D}
    (hx : x ∈ intAt D (· = v)) : incA D ((T : D.host.E)⁻¹) * x ∈ intAt D (· = v) := by
  rw [← GlobalTheory.SeeSaw.idV_one_eq_intAt] at hx ⊢
  exact GlobalTheory.SeeSaw.idV_natInv_mul_le D 1 T v hT (incA_mul_mem_idV _ hx)

end GlobalTheory.Core.Mi.LatMatch.SplitOff

namespace GlobalTheory.Core.Mi.LatMatch.SplitOff

variable {D : D7}

theorem norm_factor {μ : D.host.E} (hμ : μ ≠ 0) (T : ℕ) (N : D.host.E) (hN : N = -(μ * star μ * (T : D.host.E))) :
    (incA D (star μ⁻¹) : AE D) * incA D N = -((incA D (T : D.host.E) : AE D) * incA D μ) := by
  have hstar : star μ ≠ 0 := star_ne_zero.2 hμ
  have e : star μ⁻¹ * N = -((T : D.host.E) * μ) := by
    rw [hN, star_inv₀]
    field_simp
  rw [← map_mul, e, map_neg, map_mul]

theorem nat_ne_zero {T : ℕ} {v : GlobalTheory.FinPl.Pl D} (hT : (T : 𝓞 D.host.F) ∉ v.asIdeal) : (T : D.host.E) ≠ 0 := by
  rintro h0
  apply hT
  have : T = 0 := by exact_mod_cast h0
  rw [this, Nat.cast_zero]
  exact zero_mem _

theorem cancel_mem {T : ℕ} {v : GlobalTheory.FinPl.Pl D} (hT : (T : 𝓞 D.host.F) ∉ v.asIdeal) {x : AE D}
    (h : incA D (T : D.host.E) * x ∈ intAt D (· = v)) : x ∈ intAt D (· = v) := by
  have h2 := natInv_mul_mem_intAt hT h
  rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ (nat_ne_zero hT), map_one, one_mul] at h2

theorem line_part {S A L : HSp D} (o : OrthDec S A L) {ζ : Fin L.rank → D.host.E} {M : Lat S} {μ : D.host.E} {T : ℕ}
    {v : GlobalTheory.FinPl.Pl D} (hM : IsSelfDualC S M) (hμ : μ ≠ 0) (hline : LineAt (vecB o ζ) μ M v)
    (hnorm : star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E))) (hT : (T : 𝓞 D.host.F) ∉ v.asIdeal)
    {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D (· = v)) (hyM : y ∈ latV S M (· = v)) (c : AE D)
    (hc : c ∈ idAt D (· = v)) (hl : o.pB *ᵥ y = c • ratV ζ) : incA D μ * c ∈ intAt D (· = v) := by
  have hεI : algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) ∈ intAt D (· = v) :=
    (GlobalTheory.SeeSaw.idV_one_eq_intAt D v _).1 (eps_mem_idV v)
  have hεc := GlobalTheory.SelfDualAt.algebraMap_placeIdempotent_mul (· = v) c hc
  have hεε := GlobalTheory.SelfDualAt.cA_alg (D := D) (GlobalTheory.SelfDualAt.cP (· = v))
  have ha : algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) * incA D μ⁻¹ ∈ idAt D (· = v) :=
    Ideal.mul_mem_right _ _ hεI.1
  have haM := (hline _ ha).2 (by
    rw [mul_left_comm, ← map_mul, mul_inv_cancel₀ hμ, map_one, mul_one]
    exact hεI)
  have hsd := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S M v hM
  have hh := ((hsd.2.2 y hy).1 hyM) _ haM
  have hXY := norm_factor (D := D) hμ T _ hnorm
  rw [ratV_vecB, ← Matrix.mulVec_smul, hermAt_jB, hl, hermAt_smul, hermAt_ratV, map_mul, hεε, cA_incA] at hh
  have key : c * (algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) * incA D (star μ⁻¹)) *
      incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ) = -(incA D (T : D.host.E) * (incA D μ * c)) := by
    linear_combination (algebraMap (AF D.host.F) (AE D) (GlobalTheory.SelfDualAt.cP (· = v)) * c) * hXY -
      (incA D (T : D.host.E) * incA D μ) * hεc
  rw [key] at hh
  rw [← GlobalTheory.SeeSaw.idV_one_eq_intAt] at hh
  have h3 := neg_mem hh
  rw [neg_neg, GlobalTheory.SeeSaw.idV_one_eq_intAt] at h3
  exact cancel_mem hT h3

end GlobalTheory.Core.Mi.LatMatch.SplitOff

namespace GlobalTheory.Core.Mi.LatMatch.SplitOff

theorem splitsAt : ∀ (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M : Lat S) (μ : D.host.E) (T : ℕ) (v : GlobalTheory.FinPl.Pl D), IsLineVec L ζ → IsSelfDualC S M → μ ≠ 0 → LineAt (vecB o ζ) μ M v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → (T : 𝓞 D.host.F) ∉ v.asIdeal → SplitsAt o M v := by
  intro D S A L o ζ M μ T v hζ hM hμ hline hnorm hT y hy
  have hsum : o.jA *ᵥ (o.pA *ᵥ y) + o.jB *ᵥ (o.pB *ᵥ y) = y := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, o.sum_eq_one, Matrix.one_mulVec]
  constructor
  · intro hyM
    have hs : ∀ j k : Fin L.rank, j = k := fun j k => Fin.ext (by have := hζ.1; omega)
    obtain ⟨i, hi⟩ : ∃ i, ζ i ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hζ.2
      rw [show ζ = 0 from funext hcon]
      simp
    have hl : o.pB *ᵥ y = ((o.pB *ᵥ y) i * incA D (ζ i)⁻¹) • ratV ζ := funext fun j => by
      rw [hs j i, Pi.smul_apply, smul_eq_mul, ratV, mul_assoc, ← map_mul, inv_mul_cancel₀ hi, map_one, mul_one]
    have hc : (o.pB *ᵥ y) i * incA D (ζ i)⁻¹ ∈ idAt D (· = v) :=
      Ideal.mul_mem_right _ _ (GlobalTheory.IwaPlace.mulVec_mem_idAt _ hy i)
    have hB : o.jB *ᵥ (o.pB *ᵥ y) ∈ latV S M (· = v) := by
      have hvec : o.jB *ᵥ (o.pB *ᵥ y) = ((o.pB *ᵥ y) i * incA D (ζ i)⁻¹) • ratV (vecB o ζ) := by
        conv_lhs => rw [hl]
        rw [Matrix.mulVec_smul, ratV_vecB]
      rw [hvec]
      exact (hline _ hc).2 (line_part o hM hμ hline hnorm hT hy hyM _ hc hl)
    refine ⟨?_, hB⟩
    rw [eq_sub_of_add_eq hsum]
    exact sub_mem hyM hB
  · rintro ⟨h1, h2⟩
    rw [← hsum]
    exact add_mem h1 h2

end GlobalTheory.Core.Mi.LatMatch.SplitOff

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeSplitsOffUnitNormLineAtPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLattice_splitsOff_unitNormLine_at_place : ∀ (D : D7) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (M : Lat S) (μ : D.host.E) (T : ℕ) (v : GlobalTheory.FinPl.Pl D), IsLineVec L ζ → IsSelfDualC S M → μ ≠ 0 → LineAt (vecB o ζ) μ M v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → (T : 𝓞 D.host.F) ∉ v.asIdeal → SplitsAt o M v := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.SplitOff.splitsAt | exact GlobalTheory.Core.Mi.LatMatch.SplitOff.splitsAt | (intros; apply GlobalTheory.Core.Mi.LatMatch.SplitOff.splitsAt <;> assumption)
end
end
