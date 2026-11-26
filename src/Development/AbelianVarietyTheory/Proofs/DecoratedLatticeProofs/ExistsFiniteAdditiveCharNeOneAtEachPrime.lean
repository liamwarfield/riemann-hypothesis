module

public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationCommFockPolynomialVectors
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledSpaceMaximalLevelLattice
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeOperatorMoveAcrossInvariantBilinear
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedCharTrivialOnIntegralUnitsAtPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSphericalVacuaToDoubledLatticeVacuum
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDoubledUnitaryChartSplitPlace
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegralKeepsDoublingDiagonalAdicCompletio
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFrameRescaleConjReductionsDiagonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiagonalConjEdgeSumAddCharFiniteField

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdditiveCharNeOneAtEachPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdditiveCharNeOneAtEachPrime
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FiniteCharNontrivial

theorem trace_eq_tau (I : AutInst) (x : I.E) :
    Algebra.trace ℚ I.E x = Algebra.trace ℚ I.F (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed x) := by
  have h1 : Algebra.trace ℚ I.E (star x) = Algebra.trace ℚ I.E x :=
    Algebra.trace_eq_of_algEquiv ((starRingAut : I.E ≃+* I.E).equivRatAlgEquiv _ _) x
  have h2 : Algebra.trace ℚ I.E (algebraMap I.F I.E (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed x)) =
      2 * Algebra.trace ℚ I.F (PI.ScPsiExists.UnitaryGroupMassFormula.tau I.cm.fixed x) := by
    rw [← Algebra.trace_trace (S := I.F), Algebra.trace_algebraMap, I.cm.deg2, map_nsmul, nsmul_eq_mul]
    norm_num
  rw [PI.ScPsiExists.UnitaryGroupMassFormula.tau_apply, map_add (f := _), h1] at h2
  linarith

theorem exists_away {E : Type} [Field E] [NumberField E] (g : 𝓞 E) (hg : g ≠ 0)
    (Q : HeightOneSpectrum (𝓞 E)) :
    ∃ j : 𝓞 E, j ∉ Q.asIdeal ∧ ∀ Q' : HeightOneSpectrum (𝓞 E), g ∈ Q'.asIdeal → Q' ≠ Q → j ∈ Q'.asIdeal := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 E) | v.asIdeal ∣ Ideal.span {g}}.Finite :=
    Ideal.finite_factors (by simpa using hg)
  have hch : ∀ v : HeightOneSpectrum (𝓞 E), ∃ a : 𝓞 E, a ∉ Q.asIdeal ∧ (v ≠ Q → a ∈ v.asIdeal) := by
    intro v
    by_cases hv : v = Q
    · exact ⟨1, (Ideal.ne_top_iff_one _).1 Q.isPrime.ne_top, fun h => (h hv).elim⟩
    · have hn : ¬ v.asIdeal ≤ Q.asIdeal := fun hle =>
        hv (HeightOneSpectrum.ext (v.isMaximal.eq_of_le Q.isPrime.ne_top hle))
      obtain ⟨a, ha, ha'⟩ := SetLike.not_le_iff_exists.1 hn
      exact ⟨a, ha', fun _ => ha⟩
  choose a ha ha' using hch
  refine ⟨∏ v ∈ hfin.toFinset, a v, ?_, ?_⟩
  · have := Q.isPrime
    intro h
    obtain ⟨v, -, hv⟩ := Ideal.IsPrime.prod_mem_iff.1 h
    exact ha v hv
  · intro Q' hQ' hne
    have hm : Q' ∈ hfin.toFinset := by
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
      exact hQ'
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem a hm) (ha' Q' hne)

theorem core (I : AutInst) (psiEf : I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F → ℂ)
    (hrat : ∀ x : I.E, psiEf (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) x) * psiEinf I x = 1)
    (g : ℕ) (hg : g ≠ 0) (Q : HeightOneSpectrum (𝓞 I.E)) (hgQ : ((g : ℕ) : 𝓞 I.E) ∈ Q.asIdeal)
    (hun : Algebra.IsUnramifiedAt ℤ Q.asIdeal) (j : 𝓞 I.E) (hj : j ∉ Q.asIdeal) :
    ∃ z : 𝓞 I.E, psiEf (divN I g (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)
      (algebraMap (𝓞 I.E) I.E (j * z)))) ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hgE : (g : I.E) ≠ 0 := Nat.cast_ne_zero.2 hg
  have htr : ∀ z : 𝓞 I.E, ∃ n : ℤ, Algebra.trace ℚ I.E
      ((g : I.E)⁻¹ * algebraMap (𝓞 I.E) I.E j * algebraMap (𝓞 I.E) I.E z) = n := by
    intro z
    have e : divN I g (Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) (algebraMap (𝓞 I.E) I.E (j * z))) =
        Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F)
          ((g : I.E)⁻¹ * algebraMap (𝓞 I.E) I.E j * algebraMap (𝓞 I.E) I.E z) := by
      have e1 : algebraMap I.F (I.E ⊗[I.F] Formalism.MainNotions.S.Af I.F) ((g : I.F)⁻¹) =
          Formalism.UG.inclE (F := I.F) (Formalism.MainNotions.S.Af I.F) ((g : I.E)⁻¹) := by
        rw [Algebra.TensorProduct.algebraMap_apply, map_inv₀, map_natCast]
        rfl
      rw [divN, e1, ← RingHom.map_mul, RingHom.map_mul (algebraMap (𝓞 I.E) I.E), mul_assoc]
    have h1 := hcon z
    rw [e] at h1
    have h2 := hrat ((g : I.E)⁻¹ * algebraMap (𝓞 I.E) I.E j * algebraMap (𝓞 I.E) I.E z)
    rw [h1, one_mul] at h2
    rw [trace_eq_tau]
    exact PsiCondAllPf.trace_of_psi I _ h2
  obtain ⟨d, hd, hdQ⟩ := PsiCondAllPf.exists_diff_not_mem Q hun
  obtain ⟨c, hc⟩ := PsiCondAllPf.mul_diff_int _ htr d hd
  have hcg : (g : 𝓞 I.E) * c = j * d := by
    apply RingOfIntegers.coe_injective
    rw [RingHom.map_mul, RingHom.map_mul, hc, map_natCast]
    field_simp
  have hm : j * d ∈ Q.asIdeal := hcg ▸ Ideal.mul_mem_right _ _ hgQ
  rcases Q.isPrime.mem_or_mem hm with h | h
  exacts [hj h, hdQ h]

theorem exists_psi_ne_one : ∀ (D : D7) (psiEf : (instOf D).E ⊗[(instOf D).F] Formalism.MainNotions.S.Af (instOf D).F → ℂ), (∀ x y, psiEf (x + y) = psiEf x * psiEf y) → (∀ x ∈ IntAf (instOf D).F (instOf D).E, psiEf x = 1) → (∀ x : (instOf D).E, psiEf (Formalism.UG.inclE (F := (instOf D).F) (Formalism.MainNotions.S.Af (instOf D).F) x) * psiEinf (instOf D) x = 1) → ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ Q' : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q'.asIdeal → Q' ≠ Q → resS D.host.F Q' s = 0) ∧ psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1) ≠ 1 := by
  intro D psiEf _ _ hrat Q hQ
  have hg : D.host.g 0 * D.host.g 1 ≠ 0 := mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
  obtain ⟨i, hi⟩ : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal := by
    have hQ' := hQ
    rw [Nat.cast_mul] at hQ'
    rcases Q.isPrime.mem_or_mem hQ' with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]
  have hun : Algebra.IsUnramifiedAt ℤ Q.asIdeal :=
    PsiCondAllPf.unram_of (D.host.g i) (D.host.g_prime i) Q hi
      (Formalism.L2.SG.Pf.TypedLoc.tower_ef D.host.E D.host.E (D.host.g_prime i) (D.nd.g_split i) Q hi).1
  obtain ⟨j, hj, hj'⟩ := exists_away ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) (Nat.cast_ne_zero.2 hg) Q
  obtain ⟨z, hz⟩ := core (instOf D) psiEf hrat _ hg Q hQ hun j hj
  let z' : 𝓞 D.host.E := z
  refine ⟨oToS D.host.F D.host.E (j * z'), fun Q' h1 h2 => ?_, hz⟩
  rw [resS_oToS, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ (hj' Q' h1 h2)

end GlobalTheory.FiniteCharNontrivial
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFiniteAdditiveCharNeOneAtEachPrimeStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdditiveChar_ne_one_at_each_prime : ∀ (D : D7) (psiEf : (instOf D).E ⊗[(instOf D).F] Formalism.MainNotions.S.Af (instOf D).F → ℂ), (∀ x y, psiEf (x + y) = psiEf x * psiEf y) → (∀ x ∈ IntAf (instOf D).F (instOf D).E, psiEf x = 1) → (∀ x : (instOf D).E, psiEf (Formalism.UG.inclE (F := (instOf D).F) (Formalism.MainNotions.S.Af (instOf D).F) x) * psiEinf (instOf D) x = 1) → ∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ Q' : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q'.asIdeal → Q' ≠ Q → resS D.host.F Q' s = 0) ∧ psiEf (divN (instOf D) (D.host.g 0 * D.host.g 1) s.1) ≠ 1 := by
  first | exact @GlobalTheory.FiniteCharNontrivial.exists_psi_ne_one | exact GlobalTheory.FiniteCharNontrivial.exists_psi_ne_one | (intros; apply GlobalTheory.FiniteCharNontrivial.exists_psi_ne_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PureTensorFockUnitScaledBasisMonomial
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PureTensorFockUnitScaledBasisMonomial
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.FockScal

open GlobalTheory.FockSubst

theorem foldr_scal {ι X : Type} {A A' : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop} (c : ι → ℂ)
    (hsm : ∀ (a : ℂ) f, P f → P (a • f)) (hA : ∀ i f, P f → P (A i f))
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f) (h : ∀ i f, P f → A' i f = c i • A i f)
    {f : X → ℂ} (hf : P f) (l : List ι) :
    P (l.foldr (fun i g => A i g) f) ∧
      l.foldr (fun i g => A' i g) f = (l.map c).prod • l.foldr (fun i g => A i g) f := by
  induction l with
  | nil => simpa using hf
  | cons i l ih =>
    refine ⟨hA _ _ ih.1, ?_⟩
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    rw [ih.2, h _ _ (hsm _ _ ih.1), Asm _ _ _ ih.1, smul_smul]

theorem pure_monomial {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (f : X → ℂ) (α : ι →₀ ℕ) :
    pureTensorL A f (MvPolynomial.monomial α 1) = opPow A α f := by
  unfold pureTensorL
  have := (MvPolynomial.basisMonomials ι ℂ).constr_basis ℂ (fun k : ι →₀ ℕ => opPow A k f) α
  rwa [MvPolynomial.coe_basisMonomials] at this

theorem prod_fiber {ι κ : Type} [Fintype κ] [DecidableEq κ] (g : ι → κ) (μ : κ → ℂ) (α : ι →₀ ℕ) :
    ((Finsupp.toMultiset α).toList.map fun i => μ (g i)).prod = ∏ τ, μ τ ^ (∑ v ∈ α.support with g v = τ, α v) := by
  rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index (by simp) (by intros; rw [pow_add]), Finsupp.prod,
    ← Finset.prod_fiberwise (s := α.support) (g := g)]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [(Finset.mem_filter.1 hv).2]

theorem pure_scal {ι κ X : Type} [Fintype κ] [DecidableEq κ] {A A' : ι → (X → ℂ) → (X → ℂ)} {P : (X → ℂ) → Prop}
    (g : ι → κ) (μ : κ → ℂ) (hsm : ∀ (a : ℂ) f, P f → P (a • f)) (hA : ∀ i f, P f → P (A i f))
    (Asm : ∀ i (a : ℂ) f, P f → A i (a • f) = a • A i f) (h : ∀ i f, P f → A' i f = μ (g i) • A i f)
    {f : X → ℂ} (hf : P f) (α : ι →₀ ℕ) :
    pureTensorL A' f (MvPolynomial.monomial α 1) =
      (∏ τ, μ τ ^ (∑ v ∈ α.support with g v = τ, α v)) • pureTensorL A f (MvPolynomial.monomial α 1) := by
  rw [pure_monomial, pure_monomial]
  unfold opPow
  rw [(foldr_scal (fun i => μ (g i)) hsm hA Asm h hf _).2, prod_fiber]

theorem unitMap_smul {m n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (B' : Matrix (Fin m) (Fin m) ℂ) {z : ℂ} (hz : z ≠ 0)
    (a : Fin m) (j : Fin n) : unitMap (z • B) B' a j = z⁻¹ • unitMap B B' a j := by
  have e : z • B = B * (z • (1 : Matrix (Fin n) (Fin n) ℂ)) := by simp
  have e' : (z • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹ = z⁻¹ • 1 :=
    Matrix.inv_eq_left_inv (by simp [smul_smul, hz])
  unfold unitMap
  rw [e, Matrix.mul_inv_rev, e']
  simp

theorem cplxO_pm {m n : ℕ} {s : Matrix (Fin n) (Fin n) ℂ} {t : Matrix (Fin m) (Fin m) ℂ} (hs : s = 1 ∨ s = -1)
    (ht : t = 1 ∨ t = -1) (a : Fin m) (j : Fin n) (u : Matrix (Fin m) (Fin n) ℂ) :
    cplxO s t u = ((if decide (s = 1 ↔ t = 1) then 1 else -1 : ℂ) * Complex.I) • u := by
  have h1 : (-1 : Matrix (Fin n) (Fin n) ℂ) ≠ 1 := fun h => by
    have := congrFun (congrFun h j) j
    simp at this
    norm_num at this
  have h2 : (-1 : Matrix (Fin m) (Fin m) ℂ) ≠ 1 := fun h => by
    have := congrFun (congrFun h a) a
    simp at this
    norm_num at this
  unfold cplxO
  rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp [h1, h2]

theorem pureTensorO_scal : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ ζ : D.what₂.Tau → ℂ, (∀ τ, ‖ζ τ‖ = 1) → ∀ α : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T x.s y.s (fun τ => ζ τ • x.B τ) y.B f (MvPolynomial.monomial α 1) = (∏ τ, (if (x.s τ = 1 ↔ y.s τ = 1) then (ζ τ)⁻¹ else ζ τ) ^ (∑ v ∈ α.support with v.1 = τ, α v)) • pureTensorO ψ θ S T x.s y.s x.B y.B f (MvPolynomial.monomial α 1) := by
  intro D ψ θ hψ hθ S T x y hx hy f hf ζ hζ α
  have hz : ∀ τ, ζ τ ≠ 0 := fun τ h => by simpa [h] using hζ τ
  let μ : D.what₂.Tau → ℂ := fun τ => if (x.s τ = 1 ↔ y.s τ = 1) then (ζ τ)⁻¹ else ζ τ
  have key : ∀ (i : FVar D T.rank S.rank) g, IsThetaFunO ψ S T g →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) (fun τ => ζ τ • x.B τ) y.B i g =
      μ i.1 • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B i g := by
    rintro ⟨ρ, a, j⟩ g hg
    simp only [aPlusAll, μ]
    rw [unitMap_smul _ _ (hz ρ), aPlus_dir_smul hψ hθ ρ _ _ hg _ _ (cplxO_pm (hx.pm ρ) (hy.pm ρ) a j _)]
    congr 1
    rw [map_inv₀, ← Complex.inv_eq_conj (hζ ρ), inv_inv]
    simp only [decide_eq_true_eq]
  have hA : ∀ i f, IsThetaFunO ψ S T f →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B i f) :=
    fun _ _ h => aPlus_th hψ hθ _ _ _ h
  have Asm : ∀ i (a : ℂ) f, IsThetaFunO ψ S T f →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B i (a • f) =
      a • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (x.s τ) (y.s τ)) x.B y.B i f :=
    fun _ a _ h => aPlus_smul hψ hθ _ _ _ a h
  unfold pureTensorO
  exact pure_scal (P := IsThetaFunO ψ S T) (fun v : FVar D T.rank S.rank => v.1) μ
    (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) hA Asm key hf α

end GlobalTheory.FockScal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PureTensorFockUnitScaledBasisMonomialStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pureTensorFock_unitScaledBasis_monomial : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∀ ζ : D.what₂.Tau → ℂ, (∀ τ, ‖ζ τ‖ = 1) → ∀ α : FVar D T.rank S.rank →₀ ℕ, pureTensorO ψ θ S T x.s y.s (fun τ => ζ τ • x.B τ) y.B f (MvPolynomial.monomial α 1) = (∏ τ, (if (x.s τ = 1 ↔ y.s τ = 1) then (ζ τ)⁻¹ else ζ τ) ^ (∑ v ∈ α.support with v.1 = τ, α v)) • pureTensorO ψ θ S T x.s y.s x.B y.B f (MvPolynomial.monomial α 1) := by
  first | exact @GlobalTheory.FockScal.pureTensorO_scal | exact GlobalTheory.FockScal.pureTensorO_scal | (intros; apply GlobalTheory.FockScal.pureTensorO_scal <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLocalZetaNonvanishingOfReal
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLocalZetaNonvanishingOfReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.ZetaNeProof

variable {D : D7}

theorem coefW_mul_lev {c : Com D} {s s' : PiLocalization₂ D} (p : Step c s s') (m : Measure (WO s.V s'.V))
    (X : Set (WO s.V s'.V)) (φ : PolF D s'.V.rank s.V.rank)
    (hlaw : ∀ κ ∈ Lev.levG s.V s.β s.L, (p.ω (κ, 1)) (p.pt φ) = Lev.levChi s.V s.β s.L κ • p.pt φ)
    (b : GA D s.V) (κ : GA D s.V) (hκ : κ ∈ Lev.levG s.V s.β s.L) :
    coefW p.ω m X (p.pt φ) (b * κ) = Lev.levChi s.V s.β s.L κ * coefW p.ω m X (p.pt φ) b := by
  have hmul : p.ω (b * κ, 1) = p.ω (b, 1) * p.ω (κ, 1) := by
    rw [← map_mul, Prod.mk_mul_mk, mul_one]
  have hv : p.ω (b * κ, 1) (p.pt φ) = Lev.levChi s.V s.β s.L κ • p.ω (b, 1) (p.pt φ) := by
    rw [hmul, Module.End.mul_apply, hlaw κ hκ, map_smul]
  unfold coefW
  rw [hv, ← integral_const_mul]
  congr 1
  funext w
  rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem hgtS_mul_lev {c : Com D} {s : PiLocalization₂ D} (hs : IsSelfDualC s.V s.Λ)
    (hstab : ∀ k ∈ Lev.levG s.V s.β s.L, ∀ v,
      GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v)
    (a : GL (Fin s.V.rank) (AE D)) (b : GinfC s.V) (κ : GA D s.V) (hκ : κ ∈ Lev.levG s.V s.β s.L) :
    hgtS c s a ((b : GA D s.V) * κ) =
      ∏ w, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtW s.V a w (GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V)) := by
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.doublingHeight_eq_one_lattice_stabilizer_components D s.V s.Λ hs
  have hκf : κ ∈ GfC s.V := (Subgroup.mem_inf.mp hκ).1
  unfold hgtS
  have hA : ∀ w, GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w ((b : GA D s.V) * κ) =
      GlobalTheory.AdelicU.projArch D.sp.cm.sig s.V.gram w (b : GA D s.V) := by
    intro w
    rw [map_mul, h2 κ hκf w, mul_one]
  have hF : ∀ v ∈ c.S, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v
      (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v ((b : GA D s.V) * κ)) = 1 := by
    intro v _
    rw [map_mul, h3 b b.2 v, one_mul]
    exact h1 v _ (hstab κ hκ v)
  simp only [hA]
  rw [Finset.prod_eq_one hF, mul_one]

theorem zetaNe_of_real : ∀ D : D7, MetEx D → LevFacts D → LevelLaw D → CoefSupp D → RealZeta D → ZetaNe D := by
  intro D hMet hLev hLaw hSupp hRZ
  intro hng c hc k hk s s' hs hs' p hp m X hcov
  obtain ⟨φ, v, hvK, hR⟩ := hRZ hng c hc k hk s s' hs hs' p hp m X hcov
  have hkm : k ≤ D.R.m := hk.le
  obtain ⟨ipD, ip, hip⟩ := hMet c hc k hkm s hs
  obtain ⟨_, _, hLF3, _, _, hLF6⟩ := hLev c hc k hkm s hs
  obtain ⟨hmOff, _, hAsub, _, mR, hmR, hint⟩ := GlobalTheory.T.pushforward_haar_realPoints_times_level D hLev c hc k hkm s hs
  have hpet := GlobalTheory.T.thetaChainStage_petersson_value_realLevelTranslate D c hc k hkm s hs ipD ip hip
  have hlaw := (hLaw hng c hc k hk s s' hs hs' p hp φ).1
  have hsupp := hSupp hng c hc k hk s s' hs hs' p hp m X hcov φ
  obtain ⟨hz, hzI⟩ := hR mR hmR
  refine ⟨φ, PiTensorProduct.tprod ℂ v, Submodule.subset_span ⟨v, hvK, rfl⟩, ?_⟩
  intro u hu
  have hipu : ip u u ≠ 0 := by
    intro h0
    have := hip.pos u hu
    rw [h0, Complex.zero_re] at this
    exact lt_irrefl _ this
  have hcipu : conj (ip u u) ≠ 0 := (map_ne_zero _).mpr hipu

  have hlawZ : ∀ (b : GinfC s.V), ∀ κ ∈ Lev.levG s.V s.β s.L,
      p.zint m X φ (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) ((b : GA D s.V) * κ) =
        conj (ip u u) * (coefW p.ω m X (p.pt φ) (b : GA D s.V) *
          conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) := by
    intro b κ hκ
    unfold Step.zint
    rw [coefW_mul_lev p m X φ hlaw _ κ hκ, hpet u v b κ hκ]
    have hn : Lev.levChi s.V s.β s.L κ * conj (Lev.levChi s.V s.β s.L κ) = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hLF6 κ hκ]
      norm_num
    simp only [map_mul]
    linear_combination (conj (ip u u) * coefW p.ω m X (p.pt φ) (b : GA D s.V) *
      conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (b : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) * hn

  have hoff : ∀ g ∈ intOff c s \ {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L},
      p.zint m X φ (PiLocalization₂.val u (PiTensorProduct.tprod ℂ v)) g = 0 := by
    rintro g ⟨hg, hgA⟩
    unfold Step.zint
    rw [hsupp g hg hgA, zero_mul]
  have hzInt : Integrable (fun g : GinfC s.V => coefW p.ω m X (p.pt φ) (g : GA D s.V) *
      conj (∏ τ, ⟪(v τ : s.M.H τ), s.M.rep τ (infMat D.sp.cm.sig s.V.gram (c.θ τ) (g : GA D s.V)) (v τ : s.M.H τ)⟫_ℂ)) mR := by
    by_contra hni
    exact hz (integral_undef hni)
  refine ⟨?_, ?_⟩
  · rw [setIntegral_eq_of_subset_of_forall_diff_eq_zero hmOff hAsub hoff]
    rw [(hint _ _ (hzInt.const_mul (conj (ip u u))) hlawZ).2, integral_const_mul]
    exact mul_ne_zero hcipu hz
  · intro a hmaj hcomp
    obtain ⟨s₁, hs₁, hI⟩ := hzI a hmaj hcomp
    refine ⟨s₁, hs₁, ?_⟩
    refine IntegrableOn.of_forall_diff_eq_zero (s := {g : GA D s.V | Lev.finE s.V g ∈ Formalism.L2.DIV.lev D.sp.cm s.V.gram s.β s.L}) ?_ hmOff ?_
    · refine (hint _ _ (hI.const_mul (conj (ip u u))) ?_).1
      intro b κ hκ
      rw [hlawZ b κ hκ, hgtS_mul_lev hs.selfDual hLF3 a b κ hκ, mul_assoc]
    · intro g hg
      rw [hoff g hg, zero_mul]

end GlobalTheory.ChainOnto.ZetaNeProof
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLocalZetaNonvanishingOfRealStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainLocalZetaNonvanishing_of_real : ∀ D : D7, MetEx D → LevFacts D → LevelLaw D → CoefSupp D → RealZeta D → ZetaNe D := by
  first | exact @GlobalTheory.ChainOnto.ZetaNeProof.zetaNe_of_real | exact GlobalTheory.ChainOnto.ZetaNeProof.zetaNe_of_real | (intros; apply GlobalTheory.ChainOnto.ZetaNeProof.zetaNe_of_real <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeParametersOfElementFromOneNonzeroValue
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StageCuspFormValueMemFullSphericalHeckeEigenpart
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StageCuspFormValueMemFullSphericalHeckeEigenpart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto.ValPart

theorem lift_compMultilinearMap {ι : Type*} [Fintype ι] {Mi : ι → Type*} [∀ i, AddCommGroup (Mi i)] [∀ i, Module ℂ (Mi i)]
    {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
    (L : E →ₗ[ℂ] F) (T : (Π i, Mi i) →ₘₗ[ℂ] E) :
    PiTensorProduct.lift (L.compMultilinearMap T) = L ∘ₗ PiTensorProduct.lift T := by
  apply PiTensorProduct.ext
  ext v
  simp

theorem valPart_mem : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D → LevFacts D → ForStage D fun c _ s =>
    ∀ (u : s.CC c) w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B →
      ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
        PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
          partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e := by
  intro hCRD D hMet hLev c hc j hj s hs u w B hw hB
  obtain ⟨-, hsphc, hsplit, -, hunif⟩ := GlobalTheory.T.thetaChainStage_level_spherical_off_set D c hc j hj s hs
  obtain ⟨-, hopc, hconjH⟩ := GlobalTheory.T.thetaChainStage_conjugate_values_hecke_operators hCRD D c hc j hj s hs
  have hlat := (GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hc j hj s hs).2
  obtain ⟨-, -, -, -, hmul, -⟩ := hLev c hc j hj s hs
  have hBV : GlobalTheory.LFun.IsParamFunV s.V c.S (fun g => conj (PiLocalization₂.val u w g)) B := (hlat _ B).1 hB
  obtain ⟨a, ha⟩ := GlobalTheory.T.sphericalOperator_eigenvalues_determined_by_params D s.V (levS s.V s.β s.L) (fun k => conj (Lev.levChi s.V s.β s.L k)) c.S hsphc B
  have heig : ∀ P d R, Hecke₂ s.V (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S P d R →
      heckeLin s.V R (PiLocalization₂.val u w) = conj (a P d) • PiLocalization₂.val u w := by
    intro P d R hR
    have h1 := ha _ hBV P d R ((hopc P d R).1 hR)
    rw [hconjH] at h1
    funext g
    have h2 := congrArg (starRingEnd ℂ) (congrFun h1 g)
    simpa [map_mul] using h2
  have hops := GlobalTheory.SphericalOps.spherical_ops s.V c.θ s.M (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S
    hunif hc.inf hmul hsplit
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hw (by simp [PiLocalization₂.val])
  refine ⟨fun P d => conj (a P d), ?_⟩
  have hT : PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
      Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) :=
    (mem_multT c.θ s.M _ _ _).1 u.2
  rw [mem_partFull]
  refine ⟨hT, fun P d R hR v => ?_⟩
  obtain ⟨hkeep, -, -⟩ := hops.2.2 P d R hR
  set T := PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) with hTdef
  have hT' : heckeOn s.M R T - conj (a P d) • T ∈ Mult c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) :=
    Submodule.sub_mem _ (hkeep T hT) (Submodule.smul_mem _ _ hT)
  have hmem : PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) ∈ s.CC c := by
    show _ ∈ MultT c.θ s.M _ _
    rw [mem_multT, LinearEquiv.symm_apply_apply]
    exact hT'
  let x : s.CC c := ⟨_, hmem⟩
  have hlift : PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) =
      heckeLin s.V R ∘ₗ (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) - conj (a P d) • (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) := by
    rw [map_sub, map_smul, heckeOn, postOn]
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [lift_compMultilinearMap, hTdef, LinearEquiv.apply_symm_apply]
  have hx : PiLocalization₂.val x w = 0 := by
    show PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) w = 0
    rw [hlift]
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply]
    rw [sub_eq_zero]
    exact heig P d R hR
  have hx0 := GlobalTheory.T.thetaChainStage_cuspFormMap_eq_zero_of_value_zero D hMet c hc j hj s hs x w hw0 hx
  have h3 : PiTensorProduct.lift (heckeOn s.M R T - conj (a P d) • T) = 0 := congrArg Subtype.val hx0
  have h4 : heckeOn s.M R T - conj (a P d) • T = 0 := by
    have h := congrArg PiTensorProduct.lift.symm h3
    rwa [LinearEquiv.symm_apply_apply, map_zero] at h
  have h5 := congrArg (fun U : MMap s.M => U v) h4
  simp only [sub_apply, smul_apply, zero_apply, sub_eq_zero] at h5
  simpa [heckeOn, postOn_apply] using h5

end GlobalTheory.ChainOnto.ValPart

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StageCuspFormValueMemFullSphericalHeckeEigenpartStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stageCuspFormValue_mem_fullSphericalHecke_eigenpart : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D → LevFacts D → ForStage D fun c _ s => ∀ (u : s.CC c) w B, PiLocalization₂.val u w ≠ 0 → ParFun c s (PiLocalization₂.val u w) B → ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ partFull c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) c.S e := by
  first | exact @GlobalTheory.ChainOnto.ValPart.valPart_mem | exact GlobalTheory.ChainOnto.ValPart.valPart_mem | (intros; apply GlobalTheory.ChainOnto.ValPart.valPart_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeParametersOfElementFromOneNonzeroValue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.ChainOnto.parOfVal_of_parts : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D → LevFacts D → ParOfVal D := by
  intro hP D hM hL c hc j hj s hs x w B hv hf
  obtain ⟨e, he⟩ := GlobalTheory.T.stageCuspFormValue_mem_fullSphericalHecke_eigenpart hP D hM hL c hc j hj s hs x w B hv hf
  exact (GlobalTheory.T.thetaChain_eigenPart_has_heckeParameters hP D c hc j hj s hs x e he).2 w B hv hf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeParametersOfElementFromOneNonzeroValueStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_parameters_of_element_from_one_nonzero_value : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, MetEx D → LevFacts D → ParOfVal D := by
  first | exact @GlobalTheory.ChainOnto.parOfVal_of_parts | exact GlobalTheory.ChainOnto.parOfVal_of_parts | (intros; apply GlobalTheory.ChainOnto.parOfVal_of_parts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalSectionGraphSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalSectionGraphSplitPlace
noncomputable section

namespace GlobalTheory.Core.Rk.KerSplit

section General

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.LFun
open Formalism.UG (ordL)
open Formalism.L2.Host (atFin unif unif_spec IsUnifAt IsUnitAt)

theorem locChar_eq_val_zpow {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {χ : (AF F ⊗[F] E)ˣ →* Circle} {w : HeightOneSpectrum (𝓞 E)} (h : UnrAt χ w) (y : (w.adicCompletion E)ˣ) :
    locChar χ w y = val χ w ^ ordL y.1 := by
  have hy : Valued.v y.1 ≠ 0 := by simp
  have h0 : Valued.v y.1 = WithZero.exp (-ordL y.1) := by
    rw [ordL, dite_eq_right hy, neg_neg]
    exact (WithZero.coe_unzero hy).symm
  have h1 : IsUnitAt w (y * (atFin w (unif w)) ^ (-ordL y.1)) := by
    have := unif_spec w
    unfold IsUnifAt at this
    unfold IsUnitAt
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, this, ← WithZero.exp_zsmul]
    nth_rewrite 1 [h0]
    rw [← WithZero.exp_add]
    simp
  have := h _ h1
  rwa [map_mul, map_zpow, zpow_neg, mul_inv_eq_one] at this

theorem npow_zpow_neg {r : ℝ≥0} {q : ℕ} {m : ℤ} (h : (r : ℝ) = (q : ℝ) ^ (-m)) (z : ℂ) :
    GlobalTheory.Doubling.npow r z = (q : ℂ) ^ (-z * (m : ℂ)) := by
  rw [GlobalTheory.Doubling.npow, h, Complex.ofReal_zpow, Complex.ofReal_natCast, ← Complex.cpow_intCast,
    ← Complex.cpow_mul]
  · congr 1; push_cast; ring
  · rw [← Complex.natCast_log, Complex.mul_im, Complex.ofReal_im, Complex.intCast_im]; simp [Real.pi_pos]
  · rw [← Complex.natCast_log, Complex.mul_im, Complex.ofReal_im, Complex.intCast_im]; simp [Real.pi_pos.le]


open GlobalTheory.AdelicU GlobalTheory.Doubling Formalism.UG in
set_option maxHeartbeats 800000 in
theorem char_value {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (hc : IsCMExt F E σ) {χ : (AF F ⊗[F] E)ˣ →* Circle} {v : HeightOneSpectrum (𝓞 F)}
    {w w' : HeightOneSpectrum (𝓞 E)} (h : w.under (𝓞 F) = v) (h' : w'.under (𝓞 F) = v) (hne : w ≠ w')
    (hall : ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 F) = v ↔ u = w ∨ u = w') (hU : UnrAt χ w) (hU' : UnrAt χ w')
    (hm : val χ w * val χ w' = 1) {n : ℕ} (d : Fin n → ℤ) (x : (Fv F v ⊗[F] E)ˣ)
    (o1 : ordL (toCompl h x.1) = ∑ i, max (d i) 0) (o2 : ordL (toCompl h' x.1) = -∑ i, min (d i) 0) (z : ℂ) :
    ((charAt χ⁻¹ v x : Circle) : ℂ) * GlobalTheory.Doubling.npow (absEv F E v x) z =
      (((val χ w)⁻¹ : ℂˣ) : ℂ) ^ (∑ i, d i) * (qV E w : ℂ) ^ (-z * ((∑ i, |d i| : ℤ) : ℂ)) := by
  have habs := GlobalTheory.T.norm_cmExtension_splitPlace_eq_zpow _ _ _ hc v w h w' h' hne x
  have hch := GlobalTheory.T.ideleCharacterFinitePlaceComponent_eq_mul_of_split _ _ χ⁻¹ v w h w' h' hne hall x
  have s1 : ∑ i, max (d i) 0 + -∑ i, min (d i) 0 = ∑ i, |d i| := by
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by rw [abs_eq_max_neg]; omega
  have s2 : ∑ i, max (d i) 0 + ∑ i, min (d i) 0 = ∑ i, d i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by omega
  rw [o1, o2, s1] at habs
  rw [locChar_eq_val_zpow hU.inv, locChar_eq_val_zpow hU'.inv, val_inv, val_inv, ← Units.val_mul] at hch
  change _ = (((val χ w)⁻¹ ^ ordL (toCompl h x.1) * (val χ w')⁻¹ ^ ordL (toCompl h' x.1) : ℂˣ) : ℂ) at hch
  rw [o1, o2, eq_inv_of_mul_eq_one_right hm, inv_inv, zpow_neg (val χ w), ← inv_zpow, ← zpow_add, s2,
    Units.val_zpow_eq_zpow_val] at hch
  rw [hch, npow_zpow_neg habs]

end General

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open GlobalTheory.LFun (locChar IsSplitChart IsInertChart KGL UnrAt)


set_option maxHeartbeats 1600000 in
theorem sphSec_split : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (χ : (AE D)ˣ →* Circle) (b : ℕ), ResEta D χ b → ∀ v : FinPl D, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → UnrAt χ w) → ∀ (s : ℂ) (φ : Gv (dblSp A) v → ℂ), IsSphSecAt A L v χ⁻¹ s φ → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (e : Gv A v ≃* GL (Fin A.rank) (w.adicCompletion D.host.E)), IsSplitChart D.sp.cm.sig A.gram L h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin A.rank → ℤ) (t : GL (Fin A.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := A.rank), ∀ k₂ ∈ KGL w (n := A.rank), φ (ioAt A v (e.symm (k₁ * t * k₂))) = (((GlobalTheory.LFun.val χ w)⁻¹ : ℂˣ) : ℂ) ^ (∑ i, d i) * (qV D.host.E w : ℂ) ^ (-((A.rank : ℂ) / 2 + s) * ((∑ i, |d i| : ℤ) : ℂ)) := by
  intro D A L hL χ b hχ v hv hU s φ hφ w h e he ϖ hϖ d t ht k₁ hk₁ k₂ hk₂
  haveI := hL.1
  have hc := isCMExt_host D
  obtain ⟨w', hne, hall, -⟩ := GlobalTheory.LFun.SplitChart.exists_conj_place hc h hv
  have h' : w'.under (𝓞 D.host.F) = v := (hall w').2 (Or.inr rfl)
  have hm : GlobalTheory.LFun.val χ w * GlobalTheory.LFun.val χ w' = 1 :=
    GlobalTheory.LFun.ResEta.val_mul_val hc.2.2.1 ((GlobalTheory.LFun.resEta_iff χ _).1 hχ) hne h h' (hU w h) (hU w' h')
  obtain ⟨f, hfK, hfi, hfP, hfa⟩ := GlobalTheory.T.exists_doubled_unitary_chart_split_place _ _ _ hc A.rank A.gram (GlobalTheory.Doubling.isHermND_gram A) (dblSp A).gram
    (gram_hdbl A) L v w h hv (IwSplit.isSelfDualAt_of_isSelfDualC hL v) e he
  obtain ⟨κ, hκ, hP, hl, hq⟩ := GlobalTheory.T.exists_integral_keepsDoublingDiagonal_adicCompletion _ w A.rank ϖ hϖ d t k₁ k₂ ht hk₁ hk₂
  have hp : f (ioAt A v (e.symm (k₁ * t * k₂)) * f.symm κ) = blkGL finSumFinEquiv (k₁ * t * k₂, 1) * κ := by
    rw [map_mul, f.apply_symm_apply, ioAt, hfi, e.apply_symm_apply, map_one]
  rw [← hp] at hP hl hq
  rw [← hφ.2.1 (f.symm κ) ((hfK _).2 (by rwa [f.apply_symm_apply]))]
  generalize ioAt A v (e.symm (k₁ * t * k₂)) * f.symm κ = g at hP hl hq ⊢
  obtain ⟨ha, ha'⟩ := hfa ⟨g, (hfP g).2 hP⟩
  have ha' := ha' w' h' hne
  have law := (mem_degPSH.1 hφ.1).1 ⟨g, (hfP g).2 hP⟩ 1
  generalize aH _ D.sp.cm.sig (dblSp A).gram ⟨g, (hfP g).2 hP⟩ = x at ha ha' law
  have o1 : Formalism.UG.ordL (GlobalTheory.LFun.toCompl h x.1) = ∑ i, max (d i) 0 := by rw [ha]; exact hl
  have o2 : Formalism.UG.ordL (GlobalTheory.LFun.toCompl h' x.1) = -∑ i, min (d i) 0 := by rw [ha']; exact congrArg _ hq
  rw [mul_one, hφ.2.2, mul_one] at law
  refine law.trans ?_
  rw [add_comm ((A.rank : ℂ) / 2) s]
  exact char_value hc h h' hne hall (hU w h) (hU w' h') hm d x o1 o2 _

end GlobalTheory.Core.Rk.KerSplit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SphericalSectionGraphSplitPlaceStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt)
open GlobalTheory.LFun (locChar IsSplitChart IsInertChart KGL UnrAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sphericalSection_graph_splitPlace : ∀ (D : D7) (A : HSp D) (L : Lat A), IsSelfDualC A L → ∀ (χ : (AE D)ˣ →* Circle) (b : ℕ), ResEta D χ b → ∀ v : FinPl D, Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v → (∀ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v → UnrAt χ w) → ∀ (s : ℂ) (φ : Gv (dblSp A) v → ℂ), IsSphSecAt A L v χ⁻¹ s φ → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (e : Gv A v ≃* GL (Fin A.rank) (w.adicCompletion D.host.E)), IsSplitChart D.sp.cm.sig A.gram L h e → ∀ ϖ, IsUnifV D.host.E w ϖ → ∀ (d : Fin A.rank → ℤ) (t : GL (Fin A.rank) (w.adicCompletion D.host.E)), t.1 = Matrix.diagonal (fun i => ϖ ^ d i) → ∀ k₁ ∈ KGL w (n := A.rank), ∀ k₂ ∈ KGL w (n := A.rank), φ (ioAt A v (e.symm (k₁ * t * k₂))) = (((GlobalTheory.LFun.val χ w)⁻¹ : ℂˣ) : ℂ) ^ (∑ i, d i) * (qV D.host.E w : ℂ) ^ (-((A.rank : ℂ) / 2 + s) * ((∑ i, |d i| : ℤ) : ℂ)) := by
  first | exact @GlobalTheory.Core.Rk.KerSplit.sphSec_split | exact GlobalTheory.Core.Rk.KerSplit.sphSec_split | (intros; apply GlobalTheory.Core.Rk.KerSplit.sphSec_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLValuesNonvanishing
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLValuesNonvanishing
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section General

variable {K : Type} [Field K] [NumberField K]

theorem locL_finsetSum {ι : Type} (s : Finset ι) (d : ι → GlobalTheory.LFun.Fam K) (w : HeightOneSpectrum (𝓞 K)) (x : ℂ) :
    GlobalTheory.LFun.locL (∑ i ∈ s, d i) w x = ∏ i ∈ s, GlobalTheory.LFun.locL (d i) w x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [GlobalTheory.LFun.locL]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha, GlobalTheory.LFun.locL_add, ih]

theorem bounded_single (T : Set (HeightOneSpectrum (𝓞 K))) (z : HeightOneSpectrum (𝓞 K) → ℂˣ)
    (hz : ∀ w, ‖(z w : ℂ)‖ = 1) : GlobalTheory.LFun.Bounded T (fun w => {z w}) 1 0 := fun w _ =>
  ⟨by simp, fun b hb => by rw [Multiset.mem_singleton.1 hb, Real.rpow_zero, hz]⟩

theorem eulerProd_add_segFam {ι : Type} (T : Set (HeightOneSpectrum (𝓞 K))) (A : GlobalTheory.LFun.Fam K) (s : Finset ι)
    (z : ι → HeightOneSpectrum (𝓞 K) → ℂˣ) (t : ℕ) (x : ℂ) (hA : GlobalTheory.LFun.Converges T A x)
    (hz : ∀ i ∈ s, ∀ l < t, GlobalTheory.LFun.Converges T (fun w => {z i w}) (x + ((t : ℂ) - 1) / 2 - l)) :
    GlobalTheory.LFun.eulerProd T (A + ∑ i ∈ s, GlobalTheory.LFun.segFam (z i) t) x = GlobalTheory.LFun.eulerProd T A x *
      ∏ i ∈ s, ∏ l ∈ Finset.range t, GlobalTheory.LFun.eulerProd T (fun w => {z i w}) (x + ((t : ℂ) - 1) / 2 - l) := by
  have h1 : HasProd (fun w : {w // w ∉ T} => ∏ i ∈ s, ∏ l ∈ Finset.range t,
      GlobalTheory.LFun.locL (fun u => {z i u}) w (x + ((t : ℂ) - 1) / 2 - l))
      (∏ i ∈ s, ∏ l ∈ Finset.range t, GlobalTheory.LFun.eulerProd T (fun w => {z i w}) (x + ((t : ℂ) - 1) / 2 - l)) :=
    hasProd_prod fun i hi => hasProd_prod fun l hl => (hz i hi l (Finset.mem_range.1 hl)).hasProd
  have h2 := hA.hasProd.mul h1
  show ∏' w : {w // w ∉ T}, _ = _
  refine HasProd.tprod_eq ?_
  convert h2 using 1
  funext w
  rw [GlobalTheory.LFun.locL_add, locL_finsetSum]
  simp only [GlobalTheory.LFun.locL_segFam']

end General

theorem chainLW_holds : ∀ D : D7, ChainLW D := by
  intro D c hc B hB k hk
  set T := GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) with hT
  have hrt : D.R.r + 5 ≤ D.R.t := D.R.rank_add_five_le
  have hrt' : (D.R.r : ℝ) + 5 ≤ D.R.t := by exact_mod_cast hrt
  have hΛ : ∀ i : ℕ, ∃ Λ : ℂ → ℂ, i ∈ Finset.Icc 1 k → Differentiable ℂ Λ ∧
      (∀ z : ℂ, 1 < z.re → Λ z = GlobalTheory.LFun.eulerProd T
        (fun w => {GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹) w}) z) ∧
      ∀ n : ℕ, 1 ≤ n → n ≤ D.R.t → Λ n ≠ 0 := by
    intro i
    by_cases hi : i ∈ Finset.Icc 1 k
    · have h1 := (Finset.mem_Icc.1 hi).1
      have h2 := (Finset.mem_Icc.1 hi).2
      obtain ⟨Λ, h⟩ := GlobalTheory.T.thetaChain_char_quotient_LFunction_entire_ne_zero D c hc i (k + 1) h1 (by omega) (by omega)
      exact ⟨Λ, fun _ => h⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose Λ hΛ using hΛ
  set A := GlobalTheory.LFun.twist B (GlobalTheory.LFun.val (F := D.host.F) (c.μ (k + 1)))⁻¹ with hA
  have hAb : GlobalTheory.LFun.Bounded T A D.R.r ((D.R.r : ℝ) / 2) :=
    hB.twist fun w _ => by simp [GlobalTheory.LFun.norm_val]
  let z : ℕ → HeightOneSpectrum (𝓞 D.host.E) → ℂˣ := fun i => GlobalTheory.LFun.val (F := D.host.F) (c.μ i * (c.μ (k + 1))⁻¹)
  have hzc : ∀ i, ∀ y : ℂ, 1 < y.re → GlobalTheory.LFun.Converges T (fun w => {z i w}) y := fun i y hy =>
    (bounded_single T (z i) fun w => GlobalTheory.LFun.norm_val _ _).converges (by simpa using hy)
  let H : ℂ → ℂ := fun x => GlobalTheory.LFun.eulerProd T A (x + 1 / 2) *
    ∏ i ∈ Finset.Icc 1 k, ∏ l ∈ Finset.range D.R.t, Λ i (x + 1 / 2 + ((D.R.t : ℂ) - 1) / 2 - l)
  have hEq : ∀ x : ℂ, ((D.R.r : ℝ) + D.R.t + 2) < x.re →
      H x = GlobalTheory.LFun.LSD D c.S (chainPar c B k) (c.chT (k + 1)) (x + 1 / 2) := by
    intro x hx
    have hre : ∀ l : ℕ, l < D.R.t → 1 < (x + 1 / 2 + ((D.R.t : ℂ) - 1) / 2 - l).re := by
      intro l hl
      have : (l : ℝ) + 1 ≤ D.R.t := by exact_mod_cast hl
      have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
      simp
      linarith
    show _ = GlobalTheory.LFun.eulerProd T (GlobalTheory.LFun.twist (chainPar c B k)
      (GlobalTheory.LFun.val (F := D.host.F) (c.chT (k + 1)))⁻¹) (x + 1 / 2)
    rw [GlobalTheory.T.thetaLiftChainHeckeParameter_twist_next_target_char D c B k, ← hA, eulerProd_add_segFam T A (Finset.Icc 1 k) z D.R.t (x + 1 / 2)
      (hAb.converges (by have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _; simp; linarith))
      (fun i _ l hl => hzc i _ (hre l hl))]
    refine congrArg (GlobalTheory.LFun.eulerProd T A (x + 1 / 2) * ·) (Finset.prod_congr rfl fun i hi => Finset.prod_congr rfl fun l hl => ?_)
    exact (hΛ i hi).2.1 _ (hre l (Finset.mem_range.1 hl))
  have hU : IsOpen (GlobalTheory.Cont.rightOf (((D.R.r : ℝ) + 1) / 2)) := GlobalTheory.Cont.isOpen_rightOf _
  have hD : DifferentiableOn ℂ H (GlobalTheory.Cont.rightOf (((D.R.r : ℝ) + 1) / 2)) := by
    refine DifferentiableOn.mul ?_ (Differentiable.differentiableOn ?_)
    · refine hAb.differentiableOn.comp (differentiableOn_id.add_const _) fun x hx => ?_
      simp only [GlobalTheory.Cont.mem_rightOf] at hx
      simp
      linarith
    · exact Differentiable.fun_finsetProd fun i hi => Differentiable.fun_finsetProd fun l _ =>
        (hΛ i hi).1.comp (by fun_prop)
  have hAn := hD.analyticOnNhd hU
  have hmem : ((D.R.t : ℂ) / 2) ∈ GlobalTheory.Cont.rightOf (((D.R.r : ℝ) + 1) / 2) := by
    simp only [GlobalTheory.Cont.mem_rightOf]
    simp
    linarith
  refine ⟨H ((D.R.t : ℂ) / 2), ?_, H, ⟨_, hmem, GlobalTheory.Cont.isRightDomain_rightOf _, hAn.meromorphicOn,
    (D.R.r : ℝ) + D.R.t + 2, fun x hx => hEq x hx⟩, hAn _ hmem, rfl⟩
  refine mul_ne_zero ((hAb.converges ?_).ne_zero) ?_
  · simp
    linarith
  · refine Finset.prod_ne_zero_iff.2 fun i hi => Finset.prod_ne_zero_iff.2 fun l hl => ?_
    have hl' := Finset.mem_range.1 hl
    have e : (D.R.t : ℂ) / 2 + 1 / 2 + ((D.R.t : ℂ) - 1) / 2 - l = ((D.R.t - l : ℕ) : ℂ) := by
      rw [Nat.cast_sub hl'.le]
      ring
    rw [e]
    exact (hΛ i hi).2.2 _ (by omega) (by omega)

end GlobalTheory.ChainOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLValuesNonvanishingStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChain_LValues_nonvanishing : ∀ D : D7, ChainLW D := by
  first | exact @GlobalTheory.ChainOnto.chainLW_holds | exact GlobalTheory.ChainOnto.chainLW_holds | (intros; apply GlobalTheory.ChainOnto.chainLW_holds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDiagonalFrameChangeUnweightingSymEdges
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDiagonalFrameChangeUnweightingSymEdges
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DiagFrameWeights

theorem isUnit_res {E : Type} [Field E] [NumberField E] (PP : Formalism.L2.DIV.Pl E) (x : Formalism.L2.DIV.kP PP) (hx : x ≠ 0) :
    IsUnit x := by
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  letI : Field (Formalism.L2.DIV.kP PP) := Ideal.Quotient.field PP.asIdeal
  exact isUnit_iff_ne_zero.mpr hx


set_option maxHeartbeats 1000000 in
theorem exists_diag_frame : ∀ {D : D7} {n : ℕ} (ρ k : ℕ) (Pg : Finset (Pl D.host.E)) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β₀ : GL (Fin n) (Formalism.IndefR.Lev.EAf D)), Formalism.L2.DIV.IsFrame β₀ Λ → ∀ a : ∀ PP : Pl D.host.E, Fin n → Fin n → kP PP, (∀ PP ∈ Pg, ∀ i j, Formalism.L2.DIV.symEdge ρ k i j → a PP i j ≠ 0) → ∃ β₃ : GL (Fin n) (Formalism.IndefR.Lev.EAf D), Formalism.L2.DIV.IsFrame β₃ Λ ∧ Formalism.L2.DIV.St β₃ = Formalism.L2.DIV.St β₀ ∧ ∀ PP ∈ Pg, ∀ y ∈ Formalism.L2.DIV.St β₀, (Formalism.L2.DIV.redFn β₃ PP y ∈ Formalism.L2.DIV.unipSym (kP PP) n ρ k ↔ Formalism.L2.DIV.redFn β₀ PP y ∈ Formalism.L2.DIV.unipSym (kP PP) n ρ k) ∧ (∑ i, ∑ j, if Formalism.L2.DIV.symEdge ρ k i j then a PP i j * ((Formalism.L2.DIV.redFn β₀ PP y : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) i j else 0) = Formalism.L2.DIV.edgeSum (Formalism.L2.DIV.symEdge ρ k) (Formalism.L2.DIV.redFn β₃ PP y) := by
  intro D n ρ k Pg Λ β₀ hβ a ha
  classical
  let w : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Fin n → Fin n → (Formalism.L2.DIV.kP PP)ˣ := fun PP i j =>
    if h : PP ∈ Pg ∧ Formalism.L2.DIV.symEdge ρ k i j then (isUnit_res PP (a PP i j) (ha PP h.1 i j h.2)).unit else 1
  let d : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Fin n → (Formalism.L2.DIV.kP PP)ˣ := fun PP =>
    GlobalTheory.SeeConjScale.forestLift (Formalism.L2.DIV.symEdge ρ k) (GlobalTheory.SeeConjScale.symEdge_lt ρ k) (w PP)
  have hd : ∀ PP ∈ Pg, ∀ i j, Formalism.L2.DIV.symEdge ρ k i j → (((d PP i)⁻¹ : (Formalism.L2.DIV.kP PP)ˣ) : Formalism.L2.DIV.kP PP) * (d PP j : Formalism.L2.DIV.kP PP) = a PP i j := by
    intro PP hPP i j h
    have e := congrArg Units.val (GlobalTheory.SeeConjScale.forestLift_edge (Formalism.L2.DIV.symEdge ρ k) (GlobalTheory.SeeConjScale.symEdge_lt ρ k)
      (GlobalTheory.SeeConjScale.symEdge_uniq ρ k) (w PP) h)
    rw [Units.val_mul] at e
    rw [e]
    simp only [w, dif_pos (And.intro hPP h), IsUnit.unit_spec]
  have hex : ∀ j : Fin n, ∃ u : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ,
      ∀ PP ∈ Pg, Formalism.L2.DIV.resS D.host.F PP u = d PP j :=
    fun j => GlobalTheory.FrameRescale.exists_unit_res (D := D) Pg (fun PP => d PP j)
  choose u hu using hex
  have hSt : ∀ M, M ∈ Formalism.L2.DIV.St (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) ↔ M ∈ Formalism.L2.DIV.St β₀ := by
    intro M
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨GlobalTheory.SeeConjRead.diagGL u * y * (GlobalTheory.SeeConjRead.diagGL u)⁻¹, (GlobalTheory.FrameRescale.frGL_mul β₀ (GlobalTheory.SeeConjRead.diagGL u) y).symm⟩
    · rintro ⟨y, rfl⟩
      refine ⟨(GlobalTheory.SeeConjRead.diagGL u)⁻¹ * y * GlobalTheory.SeeConjRead.diagGL u, ?_⟩
      rw [GlobalTheory.FrameRescale.frGL_mul]
      congr 1
      group
  have hred : ∀ PP ∈ Pg, ∀ M ∈ Formalism.L2.DIV.St β₀,
      Formalism.L2.DIV.redFn (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) PP M =
        (GlobalTheory.SeeConjRead.diagGL (d PP))⁻¹ * Formalism.L2.DIV.redFn β₀ PP M * GlobalTheory.SeeConjRead.diagGL (d PP) := by
    intro PP hPP M hM
    obtain ⟨y, rfl⟩ := hM
    have e1 : Formalism.L2.DIV.frGL β₀ y =
        Formalism.L2.DIV.frGL (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) ((GlobalTheory.SeeConjRead.diagGL u)⁻¹ * y * GlobalTheory.SeeConjRead.diagGL u) := by
      rw [GlobalTheory.FrameRescale.frGL_mul]
      congr 1
      group
    have hb : Formalism.UG.bc (Formalism.L2.DIV.resS D.host.F PP) (GlobalTheory.SeeConjRead.diagGL u) = GlobalTheory.SeeConjRead.diagGL (d PP) := by
      apply Units.ext
      ext i j
      show Formalism.L2.DIV.resS D.host.F PP (((GlobalTheory.SeeConjRead.diagGL u : GL (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf D.host.F D.host.E)) i j) =
        ((GlobalTheory.SeeConjRead.diagGL (d PP) : GL (Fin n) (Formalism.L2.DIV.kP PP)) : Matrix (Fin n) (Fin n) (Formalism.L2.DIV.kP PP)) i j
      rw [GlobalTheory.SeeConjRead.diagGL_val, GlobalTheory.SeeConjRead.diagGL_val, Matrix.diagonal_apply, Matrix.diagonal_apply]
      split_ifs with h
      · subst h
        exact hu i PP hPP
      · exact map_zero _
    have e3 := Formalism.L2.DIV.redFn_frGL (β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u)) PP ((GlobalTheory.SeeConjRead.diagGL u)⁻¹ * y * GlobalTheory.SeeConjRead.diagGL u)
    have e4 := Formalism.L2.DIV.redFn_frGL β₀ PP y
    rw [← e1] at e3
    rw [e3, e4, GlobalTheory.FrameRescale.bc_conj, hb]
  refine ⟨β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u), ?_, ?_, ?_⟩
  · intro x
    rw [hβ x]
    have hinv : ((β₀ * Formalism.L2.DIV.intGL D.host.F D.host.E n (GlobalTheory.SeeConjRead.diagGL u))⁻¹).val = Matrix.diagonal (fun i => ((((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Formalism.IndefR.Lev.EAf D)) *
          (β₀⁻¹).val := by
      rw [_root_.mul_inv_rev, Units.val_mul, ← map_inv, GlobalTheory.SeeConjRead.diagGL_inv, GlobalTheory.FrameRescale.intGL_diagGL_val]
    rw [hinv]
    refine forall_congr' fun i => ?_
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_diagonal]
    have hm : ((u i : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Formalism.IndefR.Lev.EAf D) * ((((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ) : (Formalism.L2.Herm.intAf D.host.F D.host.E)) : Formalism.IndefR.Lev.EAf D) = 1 := congrArg Subtype.val (u i).mul_inv
    constructor
    · intro h
      exact Subring.mul_mem _ ((u i)⁻¹ : (Formalism.L2.Herm.intAf D.host.F D.host.E)ˣ).val.2 h
    · intro h
      have h2 := Subring.mul_mem _ (u i).val.2 h
      rwa [← mul_assoc, hm, one_mul] at h2
  · ext M
    exact hSt M
  · intro PP hPP y hy
    rw [hred PP hPP y hy]
    refine ⟨(GlobalTheory.SeeConjRead.unipSym_conj_iff ρ k (d PP) _).symm, ?_⟩
    unfold Formalism.L2.DIV.edgeSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rw [GlobalTheory.SeeConjRead.diagGL_conj_apply, ← hd PP hPP i j h]
      ring
    · rfl

end GlobalTheory.DiagFrameWeights
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsDiagonalFrameChangeUnweightingSymEdgesStatement
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_diagonal_frame_change_unweighting_symEdges : ∀ {D : D7} {n : ℕ} (ρ k : ℕ) (Pg : Finset (Pl D.host.E)) (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β₀ : GL (Fin n) (Formalism.IndefR.Lev.EAf D)), Formalism.L2.DIV.IsFrame β₀ Λ → ∀ a : ∀ PP : Pl D.host.E, Fin n → Fin n → kP PP, (∀ PP ∈ Pg, ∀ i j, Formalism.L2.DIV.symEdge ρ k i j → a PP i j ≠ 0) → ∃ β₃ : GL (Fin n) (Formalism.IndefR.Lev.EAf D), Formalism.L2.DIV.IsFrame β₃ Λ ∧ Formalism.L2.DIV.St β₃ = Formalism.L2.DIV.St β₀ ∧ ∀ PP ∈ Pg, ∀ y ∈ Formalism.L2.DIV.St β₀, (Formalism.L2.DIV.redFn β₃ PP y ∈ Formalism.L2.DIV.unipSym (kP PP) n ρ k ↔ Formalism.L2.DIV.redFn β₀ PP y ∈ Formalism.L2.DIV.unipSym (kP PP) n ρ k) ∧ (∑ i, ∑ j, if Formalism.L2.DIV.symEdge ρ k i j then a PP i j * ((Formalism.L2.DIV.redFn β₀ PP y : GL (Fin n) (kP PP)) : Matrix (Fin n) (Fin n) (kP PP)) i j else 0) = Formalism.L2.DIV.edgeSum (Formalism.L2.DIV.symEdge ρ k) (Formalism.L2.DIV.redFn β₃ PP y) := by
  first | exact @GlobalTheory.DiagFrameWeights.exists_diag_frame | exact GlobalTheory.DiagFrameWeights.exists_diag_frame | (intros; apply GlobalTheory.DiagFrameWeights.exists_diag_frame <;> assumption)
end
end
