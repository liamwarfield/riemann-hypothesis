module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHopfIdealKerIdealOfBialgHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
public import Formalism.PieriBlockIdeals.LemmaWFromLattice
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddXMulDerivativeBinomial
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsGPull
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CuspidalProductMultiplicity
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowCharEqOfIsReducedFiniteStatement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInvariantDerivationFormalGroupLawIterate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInvariantDerivationFormalGroupLawIterate
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer

namespace GlobalTheory.LawDer

theorem map_pderiv_coeffChange {R S σ : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (f : MvPowerSeries σ R) (s : σ) :
    MvPowerSeries.map φ (MvPowerSeries.pderiv (R := R) s f) = MvPowerSeries.pderiv (R := S) s (MvPowerSeries.map φ f) := by
  ext m
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_map,
    map_mul, map_add, map_natCast, map_one]

theorem map_atZero {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    (H : MvPowerSeries (Fin d ⊕ Fin d) R) : map f (atZero H) = atZero (map f H) := by
  unfold atZero
  rw [map_subst (hasSubst_of_constantCoeff_zero (fun s => by cases s <;> simp))]
  congr 1
  funext s
  cases s <;> simp

theorem map_smul_coeffChange {R S σ : Type} [CommRing R] [CommRing S] (f : R →+* S) (a : R)
    (H : MvPowerSeries σ R) : map f (a • H) = f a • map f H := by
  ext m
  simp [MvPowerSeries.coeff_map, MvPowerSeries.coeff_smul]

theorem map_invDer {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (u : Fin d → R) (F : MvPowerSeries (Fin d) R) :
    map f (invDer μ u F) = invDer (fun i => map f (μ i)) (fun i => f (u i)) (map f F) := by
  unfold invDer
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul_coeffChange, map_atZero, map_pderiv_coeffChange, map_subst (hasSubst_of_constantCoeff_zero hμ)]

theorem map_invDer_iterate : ∀ (R S : Type) [CommRing R] [CommRing S] (f : R →+* S) (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) →
    ∀ (u : Fin d → R) (k : ℕ) (F : MvPowerSeries (Fin d) R),
    map f ((invDer μ u)^[k] F) = (invDer (fun i => map f (μ i)) (fun i => f (u i)))^[k] (map f F) := by
  intro R S _ _ f d μ hμ u k F
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', map_invDer f μ hμ, ih]

end GlobalTheory.LawDer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInvariantDerivationFormalGroupLawIterateStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_invariantDerivationFormalGroupLaw_iterate : ∀ (R S : Type) [CommRing R] [CommRing S] (f : R →+* S) (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (u : Fin d → R) (k : ℕ) (F : MvPowerSeries (Fin d) R), map f ((invDer μ u)^[k] F) = (invDer (fun i => map f (μ i)) (fun i => f (u i)))^[k] (map f F) := by
  first | exact @GlobalTheory.LawDer.map_invDer_iterate | exact GlobalTheory.LawDer.map_invDer_iterate | (intros; apply GlobalTheory.LawDer.map_invDer_iterate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallInvariantDifferentialDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveDvdOfForallDualDvd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveDvdOfForallDualDvd
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem projective_dvd_of_forall_dual_dvd :
    ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Module.Projective O M] (a : O) (b : M),
      (∀ φ : Module.Dual O M, a ∣ φ b) → ∃ z, b = a • z := by
  intro O M _ _ _ _ a b h
  obtain ⟨s, hs⟩ := Module.projective_def'.mp (inferInstance : Module.Projective O M)
  have hc : ∀ i : M, a ∣ s b i := fun i => h ((Finsupp.lapply i).comp s)
  choose c hc using hc
  refine ⟨∑ i ∈ (s b).support, c i • i, ?_⟩
  have hb : Finsupp.linearCombination O id (s b) = b := by
    simpa using LinearMap.congr_fun hs b
  rw [Finset.smul_sum]
  conv_lhs => rw [← hb]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_smul, ← hc i]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveDvdOfForallDualDvdStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_eq_of_forall_dual_dvd : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] [Module.Projective O M] (a : O) (b : M), (∀ φ : Module.Dual O M, a ∣ φ b) → ∃ z, b = a • z := by
  first | exact @GlobalTheory.projective_dvd_of_forall_dual_dvd | exact GlobalTheory.projective_dvd_of_forall_dual_dvd | (intros; apply GlobalTheory.projective_dvd_of_forall_dual_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallInvariantDifferentialDvd
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem dvd_of_forall_omega_dvd : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (n : ℕ)
    (a : O) (b : G.A n),
    (∀ (w : G.dual.omega) (φ : CartierDual O (G.A n)), dUnit (R := O) φ = w.1 n → a ∣ φ b) →
      (∃ z, b = a • z) ∧ ∀ w : G.dual.omega, ∃ φ : CartierDual O (G.A n), dUnit (R := O) φ = w.1 n := by
  intro p O _ G n a b h
  have hall : ∀ φ : CartierDual O (G.A n), a ∣ φ b := fun φ => by
    obtain ⟨w, hw⟩ := G.dual.omegaLevel_surjective n (dUnit (R := O) φ)
    exact h w φ hw.symm
  exact ⟨GlobalTheory.T.exists_smul_eq_of_forall_dual_dvd O (G.A n) a b (fun φ => hall (WithConv.toConv φ)),
    fun w => AugCot.d_surjective _ (w.1 n)⟩

end GlobalTheory.PDivGroup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallInvariantDifferentialDvdStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_of_forall_invariantDifferential_dvd : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (n : ℕ) (a : O) (b : G.A n), (∀ (w : G.dual.omega) (φ : CartierDual O (G.A n)), dUnit (R := O) φ = w.1 n → a ∣ φ b) → (∃ z, b = a • z) ∧ ∀ w : G.dual.omega, ∃ φ : CartierDual O (G.A n), dUnit (R := O) φ = w.1 n := by
  first | exact @GlobalTheory.PDivGroup.dvd_of_forall_omega_dvd | exact GlobalTheory.PDivGroup.dvd_of_forall_omega_dvd | (intros; apply GlobalTheory.PDivGroup.dvd_of_forall_omega_dvd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPowerSeriesFamilyToFractionsFormalGroupLawNat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPowerSeriesFamilyToFractionsFormalGroupLawNat
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem constantCoeff_nmul_zero {R : Type} [CommRing R] {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) :
    ∀ i, constantCoeff (nmul μ n i) = 0 := by
  induction n with
  | zero => intro i; simp [nmul]
  | succ n ih =>
    intro i
    have h0 : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun k => (X k : MvPowerSeries (Fin d) R)) j) = 0 := by
      intro j; cases j with
      | inl j => exact ih j
      | inr j => simp
    show constantCoeff ((fun v : Fin d → MvPowerSeries (Fin d) R => op μ v fun i => X i)^[n + 1]
      (fun _ => 0) i) = 0
    rw [Function.iterate_succ_apply']
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 (hμ i)

theorem up_nmul : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R),
    (∀ i, constantCoeff (μ i) = 0) → ∀ n : ℕ, up S (nmul μ n) = nmul (up S μ) n := by
  intro R S _ _ _ d μ hμ n
  induction n with
  | zero => funext i; simp [up, nmul]
  | succ n ih =>
    have h0 : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun k => (X k : MvPowerSeries (Fin d) R)) j) = 0 := by
      intro j; cases j with
      | inl j => exact constantCoeff_nmul_zero μ hμ n j
      | inr j => simp
    funext i
    show map (algebraMap R S) ((fun v : Fin d → MvPowerSeries (Fin d) R => op μ v fun i => X i)^[n + 1]
      (fun _ => 0) i) = (fun v : Fin d → MvPowerSeries (Fin d) S => op (up S μ) v fun i => X i)^[n + 1]
      (fun _ => 0) i
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    change map (algebraMap R S) (subst (Sum.elim (nmul μ n) fun i => X i) (μ i)) =
      subst (Sum.elim (nmul (up S μ) n) fun i => X i) (up S μ i)
    rw [map_subst (hasSubst_of_constantCoeff_zero h0), ← ih]
    congr 1
    funext j
    cases j with
    | inl j => rfl
    | inr j => simp

end GlobalTheory.QLog
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPowerSeriesFamilyToFractionsFormalGroupLawNatStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mapPowerSeriesFamilyToFractions_formalGroupLawNatMultiple : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ n : ℕ, up S (nmul μ n) = nmul (up S μ) n := by
  first | exact @GlobalTheory.QLog.up_nmul | exact GlobalTheory.QLog.up_nmul | (intros; apply GlobalTheory.QLog.up_nmul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfFiniteProjectiveAlgebra
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfFiniteProjectiveAlgebra
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.FinProjComplete

theorem smodEq_span_singleton_pow_iff {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (a : R) (n : ℕ) (x y : M) :
    x ≡ y [SMOD ((Ideal.span {a}) ^ n • ⊤ : Submodule R M)] ↔ ∃ z : M, x - y = a ^ n • z := by
  rw [SModEq.sub_mem, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
    Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨z, -, hz⟩; exact ⟨z, hz.symm⟩
  · rintro ⟨z, hz⟩; exact ⟨z, Submodule.mem_top, hz.symm⟩

end GlobalTheory.FinProjComplete

namespace GlobalTheory.FinProjComplete

theorem isAdicComplete_of_finite_projective : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A]
    [Algebra O A] [Module.Finite O A] [Module.Projective O A]
    [IsAdicComplete (Ideal.span {(p : O)}) O], IsAdicComplete (Ideal.span {(p : A)}) A := by
  intro p O A _ _ _ _ _ hO
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective O A
  have hfg' : ∀ x, f (g x) = x := fun x => LinearMap.congr_fun hfg x
  have key : ∀ (k : ℕ) (z : A), (p : A) ^ k • z = ((p : O) ^ k) • z := by
    intro k z
    rw [smul_eq_mul, Algebra.smul_def, map_pow, map_natCast]
  refine { toIsHausdorff := ⟨fun x hx => ?_⟩, toIsPrecomplete := ⟨fun s hs => ?_⟩ }
  · have hc : ∀ i, g x i = 0 := by
      intro i
      refine IsHausdorff.haus' (I := Ideal.span {(p : O)}) _ (fun k => ?_)
      obtain ⟨z, hz⟩ := (smodEq_span_singleton_pow_iff _ k x 0).1 (hx k)
      rw [smodEq_span_singleton_pow_iff]
      refine ⟨g z i, ?_⟩
      have := congrArg (fun y => g y i) hz
      simpa only [sub_zero, key, map_smul, Pi.smul_apply] using this
    have h0 : g x = 0 := funext hc
    rw [← hfg' x, h0, map_zero]
  · have hL : ∀ i, ∃ L : O, ∀ k,
        g (s k) i ≡ L [SMOD ((Ideal.span {(p : O)}) ^ k • ⊤ : Submodule O O)] := by
      intro i
      refine IsPrecomplete.prec' (I := Ideal.span {(p : O)}) _ (fun {m k} hmk => ?_)
      obtain ⟨z, hz⟩ := (smodEq_span_singleton_pow_iff _ m _ _).1 (hs hmk)
      rw [smodEq_span_singleton_pow_iff]
      refine ⟨g z i, ?_⟩
      have := congrArg (fun y => g y i) hz
      simpa only [map_sub, key, map_smul, Pi.smul_apply, Pi.sub_apply] using this
    choose L hL using hL
    refine ⟨f L, fun k => ?_⟩
    have hz' : ∀ i, ∃ z : O, g (s k) i - L i = (p : O) ^ k • z :=
      fun i => (smodEq_span_singleton_pow_iff _ k _ _).1 (hL i k)
    choose z hz using hz'
    have h2 : g (s k) - L = (p : O) ^ k • z := funext fun i => by simpa using hz i
    rw [smodEq_span_singleton_pow_iff]
    refine ⟨f z, ?_⟩
    calc s k - f L = f (g (s k) - L) := by rw [map_sub, hfg']
      _ = (p : A) ^ k • f z := by rw [h2, map_smul, key]

end GlobalTheory.FinProjComplete
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteOfFiniteProjectiveAlgebraStatement
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAdicComplete_of_finite_projective_algebra : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] [Module.Finite O A] [Module.Projective O A] [IsAdicComplete (Ideal.span {(p : O)}) O], IsAdicComplete (Ideal.span {(p : A)}) A := by
  first | exact @GlobalTheory.FinProjComplete.isAdicComplete_of_finite_projective | exact GlobalTheory.FinProjComplete.isAdicComplete_of_finite_projective | (intros; apply GlobalTheory.FinProjComplete.isAdicComplete_of_finite_projective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapComb
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.SmallSecond

theorem map_formalGroupLawCoboundaryOne_eq {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (f : MvPowerSeries (Fin d) R) :
    map φ (cob1 μ f) = cob1 (fun i => map φ (μ i)) (map φ f) := by
  unfold cob1 inL inR
  rw [map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero hμ),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _),
    map_subst (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)]
  simp only [map_X]

end GlobalTheory.SmallSecond

namespace GlobalTheory.SmallSecond

variable {B O Q C : Type} [CommRing B] [CommRing O] [CommRing Q] [CommRing C] [Algebra B Q]
  [Algebra O C] {θ : B →+* O} {Θ : Q →+* C}

theorem map_up {d : ℕ} (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) :
    (fun i => map Θ (up Q μ' i)) = up C (fun i => map θ (μ' i)) := by
  funext i; ext α; simp [up, coeff_map, hΘ]

theorem map_formalGroupLawCoboundaryOne_square {d : ℕ} (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (hμ : ∀ i, constantCoeff (μ' i) = 0)
    (f : MvPowerSeries (Fin d) Q) :
    map Θ (cob1 (up Q μ') f) = cob1 (up C (fun i => map θ (μ' i))) (map Θ f) := by
  rw [map_formalGroupLawCoboundaryOne_eq Θ _ (fun i => by simp [up, ← coeff_zero_eq_constantCoeff_apply, coeff_map,
    coeff_zero_eq_constantCoeff_apply, hμ]), map_up hΘ]

theorem map_comb {σ ι : Type} [Fintype ι] (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    map Θ (comb b e) = comb (fun i => θ (b i)) (fun i => map Θ (e i)) := by
  unfold comb
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ext α
  rw [coeff_map, MvPowerSeries.coeff_smul, MvPowerSeries.coeff_smul, coeff_map, map_mul, hΘ]

theorem ql_map {d : ℕ} (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (hμ : ∀ i, constantCoeff (μ' i) = 0)
    {f : MvPowerSeries (Fin d) Q} (hf : QL μ' ⊤ f) :
    QL (fun i => map θ (μ' i)) ⊤ (map Θ f) := by
  obtain ⟨h0, h1, h2⟩ := hf
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, h0,
      map_zero]
  · obtain ⟨b, -, hb⟩ := h1 i
    exact ⟨θ b, trivial, by simp only [lin, coeff_map] at hb ⊢; rw [hb, hΘ]⟩
  · rw [← map_formalGroupLawCoboundaryOne_square hΘ μ' hμ]
    intro α
    obtain ⟨b, -, hb⟩ := h2 α
    exact ⟨θ b, trivial, by rw [coeff_map, hb, hΘ]⟩

theorem formalGroupLawCoboundaryOne_map_eq_zero {d : ℕ} (hΘ : ∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b))
    (μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B) (hμ : ∀ i, constantCoeff (μ' i) = 0)
    {f : MvPowerSeries (Fin d) Q} (hf : In (RingHom.ker θ) (cob1 (up Q μ') f)) :
    cob1 (up C (fun i => map θ (μ' i))) (map Θ f) = 0 := by
  rw [← map_formalGroupLawCoboundaryOne_square hΘ μ' hμ]
  ext α
  obtain ⟨b, hb0, hb⟩ := hf α
  rw [coeff_map, hb, hΘ, RingHom.mem_ker.1 hb0, map_zero, map_zero]

end GlobalTheory.SmallSecond
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigToLieBijectiveAndDualRigOfOmegaBijectiveOfIsE
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonInvariantDifferentialsOfEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonInvariantDifferentialsOfEtale
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

theorem subsingleton_omega_of_isEt : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (G : PDivGroup p k), G.IsEt → Subsingleton G.omega ∧ Subsingleton G.dual.dual.omega := by
  intro p _ k _ _ _ G hG
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  have h1 : Subsingleton G.omega := by
    refine ⟨fun v w => ?_⟩
    have hz : ∀ u : G.omega, u = 0 := fun u => Subtype.ext (funext fun n => by
      haveI := hG n
      obtain ⟨a, ha⟩ := AugCot.d_surjective _ (u.1 n)
      obtain ⟨b, rfl⟩ := GlobalTheory.T.exists_pow_char_eq_of_isReduced_finite' p k (G.A n) a
      rw [← ha]
      exact dUnit_pow_prime hp b)
    rw [hz v, hz w]
  refine ⟨h1, ?_⟩
  have hinj : Function.Injective (omegaMap G G.dual.dual G.bidual.hom) := by
    refine Function.LeftInverse.injective (g := omegaMap G.dual.dual G G.bidual.inv) fun x => ?_
    rw [← LinearMap.comp_apply, ← omegaMap_comp, Iso.inv_hom_id, omegaMap_id, LinearMap.id_apply]
  exact hinj.subsingleton

end PDivGroup

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonInvariantDifferentialsOfEtaleStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsingleton_invariantDifferentials_of_etale : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (G : PDivGroup p k), G.IsEt → Subsingleton G.omega ∧ Subsingleton G.dual.dual.omega := by
  first | exact @GlobalTheory.PDivGroup.subsingleton_omega_of_isEt | exact GlobalTheory.PDivGroup.subsingleton_omega_of_isEt | (intros; apply GlobalTheory.PDivGroup.subsingleton_omega_of_isEt <;> assumption)
end
end

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

namespace GlobalTheory

namespace PDivGroup

theorem rigToLie_bijective_and_dual_rigOfOmega_bijective_of_isEt :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (h : (p : k) = 0)
      (G : PDivGroup p k), G.IsEt →
      Function.Bijective (G.rigToLie h) ∧ Function.Bijective G.dual.rigOfOmega := by
  intro p _ k _ _ _ h G hG
  obtain ⟨h1, h2⟩ := GlobalTheory.T.subsingleton_invariantDifferentials_of_etale p k G hG
  refine ⟨⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, G.rigToLie_surjective h⟩,
    ⟨G.dual.rigOfOmega_injective_of_eq_zero h, fun y => ?_⟩⟩
  · obtain ⟨w, rfl⟩ := (G.exact_rigOfOmega_rigToLie h x).1 hx
    rw [Subsingleton.elim w 0, map_zero]
  · refine (G.dual.exact_rigOfOmega_rigToLie h y).1 ?_
    exact LinearMap.ext fun w => by rw [Subsingleton.elim w 0, map_zero, LinearMap.zero_apply]

end PDivGroup

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffExpSub
open Formalism.BasicNotions Formalism.BasicNotions.Loc IsLocalRing

namespace GlobalTheory.WachExp

open PowerSeries

theorem ringHom_gam_X {l : ℕ} [Fact l.Prime] {O L : Type} [CommRing O] [Field L] [CharZero L] [Algebra ℚ L]
    [Algebra ℤ_[l] O] [Algebra ℤ_[l] L] [Algebra O L] [IsScalarTower ℤ_[l] O L] (φ : O⟦X⟧ →+* L⟦X⟧)
    (hφ : ∀ a : O, φ (C a) = C (algebraMap O L a)) (z : L) (hX : φ X = C z * exp L - 1) (hz : z ^ l = 1)
    (c : ℤ_[l]) (hc : (l : ℤ_[l]) ∣ c - 1) :
    φ (GlobalTheory.Fon.gam O c X) = C z * rescale (algebraMap ℤ_[l] L c) (exp L) - 1 := by
  let f : O⟦X⟧ →ₐ[O] L⟦X⟧ :=
    { toRingHom := φ
      commutes' := fun a => (congrArg φ (PowerSeries.algebraMap_apply (R := O) (A := O))).trans
        ((hφ a).trans (PowerSeries.algebraMap_apply (R := O) (A := L)).symm) }
  have h := GlobalTheory.HWL.Ser.map_gam_X f z hX 1 1 (by rw [pow_one]; exact hz) c (by simpa using hc)
  rw [pow_one] at h
  exact h

end GlobalTheory.WachExp

namespace GlobalTheory.WachExp

open PowerSeries

variable {l : ℕ} [Fact l.Prime] (LL : FinExt l)

theorem norm_root_sub_one_lt {z : ↥LL.1} (hz : z ^ l = 1) : ‖(((z - 1 : ↥LL.1)) : Om l)‖ < 1 := by
  have h : ((z : Om l)) ^ l ^ 1 = 1 := by
    rw [pow_one]; exact_mod_cast congrArg (fun y : ↥LL.1 => (y : Om l)) hz
  have := GlobalTheory.HWL.Ser.norm_sub_one_lt h
  push_cast
  exact this

theorem constantCoeff_exp_sub (z a : ↥LL.1) :
    constantCoeff (C z * rescale a (exp ↥LL.1) - 1) = z - 1 := by
  rw [map_sub, map_mul, GlobalTheory.HWL.Ser.constantCoeff_rescale_exp, constantCoeff_C, mul_one, map_one]

theorem ev_unique (x : PowerSeries ↥LL.1) (hx : ‖((constantCoeff x : ↥LL.1) : Om l)‖ < 1)
    (φ ψ : PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1)
    (hφ : ∀ a : ↥(OL LL), φ (C a) = C (a : ↥LL.1)) (hψ : ∀ a : ↥(OL LL), ψ (C a) = C (a : ↥LL.1))
    (hφX : φ X = x) (hψX : ψ X = x) : φ = ψ := by
  let φ' : PowerSeries ↥(OL LL) →ₐ[↥(OL LL)] PowerSeries ↥LL.1 :=
    { toRingHom := φ, commutes' := fun a => by change φ (C a) = C (a : ↥LL.1); exact hφ a }
  let ψ' : PowerSeries ↥(OL LL) →ₐ[↥(OL LL)] PowerSeries ↥LL.1 :=
    { toRingHom := ψ, commutes' := fun a => by change ψ (C a) = C (a : ↥LL.1); exact hψ a }
  have h := (GlobalTheory.HWL.SeriesEval.existsUnique_ev l LL x hx).1.unique (y₁ := φ') (y₂ := ψ') hφX hψX
  exact RingHom.ext fun f => AlgHom.congr_fun h f

theorem exists_ev (z : ↥LL.1) (hz : z ^ l = 1) :
    ∃ φ : PowerSeries ↥(OL LL) →+* PowerSeries ↥LL.1,
      (∀ a : ↥(OL LL), φ (C a) = C (a : ↥LL.1)) ∧ φ X = C z * exp ↥LL.1 - 1 := by
  have h := GlobalTheory.HWL.SeriesEval.existsUnique_ev l LL (C z * rescale 1 (exp ↥LL.1) - 1)
    (by rw [constantCoeff_exp_sub]; exact norm_root_sub_one_lt LL hz)
  obtain ⟨ev, hev, -⟩ := h.1
  refine ⟨ev.toRingHom, fun a => ?_, by
    change ev X = _
    rw [hev, rescale_one, RingHom.id_apply]⟩
  have := ev.commutes a
  exact this

theorem rescale_C' (r z : ↥LL.1) : rescale r (C z) = C z := by
  ext n
  by_cases h : n = 0 <;> simp [coeff_rescale, coeff_C, h]

end GlobalTheory.WachExp

namespace GlobalTheory.WachExp

open PowerSeries

end GlobalTheory.WachExp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompatiblePrimePowerRoots
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusPointOverFractionField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev

namespace GlobalTheory

theorem exists_compatible_primitive_prime_pow_roots :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharZero k],
      ∃ ζ : ℕ → kˣ, (∀ r, IsPrimitiveRoot (ζ r) (p ^ r)) ∧ ∀ r, ζ (r + 1) ^ p = ζ r := by
  intro p hp k _ _ _
  have hp' : p.Prime := hp.out

  have hroot : ∀ u : kˣ, ∃ v : kˣ, v ^ p = u := by
    intro u
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (u : k) hp'.pos
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hp'.ne_zero] at hz
      exact u.ne_zero hz.symm
    exact ⟨Units.mk0 z hz0, Units.ext (by simpa using hz)⟩
  choose f hf using hroot

  haveI : NeZero (p : k) := ⟨by exact_mod_cast hp'.ne_zero⟩
  obtain ⟨z₁, hz₁⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k p
  have hz₁0 : z₁ ≠ 0 := hz₁.ne_zero hp'.ne_zero
  have hu₁ : IsPrimitiveRoot (Units.mk0 z₁ hz₁0) p := by
    rw [← IsPrimitiveRoot.coe_units_iff]; simpa using hz₁

  have step : ∀ (n : ℕ) (x : kˣ), IsPrimitiveRoot (x ^ p) (p ^ (n + 1)) →
      IsPrimitiveRoot x (p ^ (n + 2)) := by
    intro n x hx
    rw [IsPrimitiveRoot.iff_orderOf] at hx ⊢
    have hdvd : orderOf x ∣ p ^ (n + 2) := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_succ', pow_mul, ← hx, pow_orderOf_eq_one]
    obtain ⟨i, hi, hio⟩ := (Nat.dvd_prime_pow hp').1 hdvd
    rcases Nat.lt_or_ge i (n + 2) with h | h
    · exfalso
      have h1 : (x ^ p) ^ (p ^ n) = 1 := by
        rw [← pow_mul, ← pow_succ', ← orderOf_dvd_iff_pow_eq_one, hio]
        exact Nat.pow_dvd_pow p (by omega)
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hx] at h2
      have := Nat.le_of_dvd (pow_pos hp'.pos n) h2
      have h3 : p ^ n < p ^ (n + 1) := Nat.pow_lt_pow_right hp'.one_lt (by omega)
      omega
    · rw [hio, le_antisymm hi h]
  let g : ℕ → kˣ := fun n => Nat.rec (Units.mk0 z₁ hz₁0) (fun _ u => f u) n
  have g0 : g 0 = Units.mk0 z₁ hz₁0 := rfl
  have gs : ∀ n, g (n + 1) = f (g n) := fun n => rfl
  have gprim : ∀ n, IsPrimitiveRoot (g n) (p ^ (n + 1)) := by
    intro n
    induction n with
    | zero => simpa [g0] using hu₁
    | succ n ih =>
      apply step
      rw [gs, hf]; exact ih
  refine ⟨fun r => match r with | 0 => 1 | r + 1 => g r, ?_, ?_⟩
  · intro r
    cases r with
    | zero => simpa using IsPrimitiveRoot.one
    | succ r => exact gprim r
  · intro r
    cases r with
    | zero => show g 0 ^ p = 1; simpa using (gprim 0).pow_eq_one
    | succ r => show g (r + 1) ^ p = g r; rw [gs, hf]

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compatible_prime_power_roots : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] [CharZero k], ∃ ζ : ℕ → kˣ, (∀ r, IsPrimitiveRoot (ζ r) (p ^ r)) ∧ ∀ r, ζ (r + 1) ^ p = ζ r := by
  first | (exact @GlobalTheory.exists_compatible_primitive_prime_pow_roots) | (exact GlobalTheory.exists_compatible_primitive_prime_pow_roots) | (intros; apply GlobalTheory.exists_compatible_primitive_prime_pow_roots  <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstFormalGroupLawNatMultipleEqCoboundarySum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstFormalGroupLawNatMultipleEqCoboundarySum
set_option autoImplicit false

noncomputable section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog.NmulSubst

theorem subst_zero_fun {R : Type} [CommRing R] {σ τ : Type} [Finite σ] (g : MvPowerSeries σ R) :
    subst (fun _ : σ => (0 : MvPowerSeries τ R)) g = C (constantCoeff g) := by
  have ha : HasSubst (fun _ : σ => (0 : MvPowerSeries τ R)) :=
    hasSubst_of_constantCoeff_zero fun _ => map_zero _
  ext e
  rw [coeff_subst ha, finsum_eq_single _ 0]
  · classical
    rw [Finsupp.prod_zero_index, coeff_one, coeff_C, coeff_zero_eq_constantCoeff_apply]
    split_ifs <;> simp
  · intro x hx
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra! hc
      exact hx (Finsupp.ext hc)
    have : (x.prod fun _ n => (0 : MvPowerSeries τ R) ^ n) = 0 :=
      Finset.prod_eq_zero (i := i) (Finsupp.mem_support_iff.2 hi) (zero_pow hi)
    rw [this, map_zero, smul_zero]

theorem nmul_succ {R : Type} [CommRing R] {d : ℕ} (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R)
    (k : ℕ) : nmul μ (k + 1) = op μ (nmul μ k) (fun i => X i) := by
  unfold nmul
  exact Function.iterate_succ_apply' _ _ _

theorem constantCoeff_nmul {R : Type} [CommRing R] {d : ℕ}
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) :
    ∀ i, constantCoeff (nmul μ n i) = 0 := by
  induction n with
  | zero => intro i; simp [nmul]
  | succ k ih =>
    intro i
    rw [nmul_succ]
    have hs : ∀ j, constantCoeff (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j)
      · exact ih j
      · exact constantCoeff_X _
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero hs) hs (hμ i)

end GlobalTheory.QLog.NmulSubst


open GlobalTheory.QLog.NmulSubst in
theorem GlobalTheory.QLog.subst_nmul_eq (R : Type) [CommRing R] (d : ℕ)
    (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (hμ : ∀ i, constantCoeff (μ i) = 0)
    (g : MvPowerSeries (Fin d) R) (n : ℕ) :
    subst (nmul μ n) g = C (constantCoeff g) + (n : R) • g +
      ∑ k ∈ Finset.range n, at2 (cob1 μ g) (nmul μ k) (fun i => X i) := by
  induction n with
  | zero =>
    have : nmul μ 0 = fun _ => 0 := rfl
    rw [this, subst_zero_fun]
    simp
  | succ k ih =>
    have hE : ∀ j, constantCoeff (Sum.elim (nmul μ k) (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j)
      · exact constantCoeff_nmul μ hμ k j
      · exact constantCoeff_X _
    have hsE := hasSubst_of_constantCoeff_zero hE
    have hμs : HasSubst μ := hasSubst_of_constantCoeff_zero hμ
    have hX : ∀ (f : Fin d → Fin d ⊕ Fin d),
        HasSubst (fun i => (X (f i) : MvPowerSeries (Fin d ⊕ Fin d) R)) :=
      fun _ => hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
    rw [nmul_succ]
    change subst (fun i => subst (Sum.elim (nmul μ k) fun i => X i) (μ i)) g = _
    rw [← subst_comp_subst_apply hμs hsE]
    have hsplit : subst μ g = cob1 μ g + inL g + inR g := by unfold cob1; abel
    have hL : subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) R)) (inL g) =
        subst (nmul μ k) g := by
      unfold inL
      rw [subst_comp_subst_apply (hX Sum.inl) hsE]
      congr 1
      funext i
      rw [subst_X hsE]
      rfl
    have hR : subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) R)) (inR g) = g := by
      unfold inR
      rw [subst_comp_subst_apply (hX Sum.inr) hsE]
      have : (fun i => subst (Sum.elim (nmul μ k) fun i => (X i : MvPowerSeries (Fin d) R))
          (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) R)) = X := by
        funext i
        rw [subst_X hsE]
        rfl
      rw [this, subst_self]
      rfl
    rw [hsplit, subst_add hsE, subst_add hsE, hL, hR, ih, Finset.sum_range_succ]
    change _ = _ + _ + (_ + subst (Sum.elim (nmul μ k) fun i => X i) (cob1 μ g))
    push_cast
    rw [add_smul, one_smul]
    abel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubstFormalGroupLawNatMultipleEqCoboundarySumStatement
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subst_formalGroupLawNatMultiple_eq_coboundary_sum : ∀ (R : Type) [CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ i, constantCoeff (μ i) = 0) → ∀ (g : MvPowerSeries (Fin d) R) (n : ℕ), subst (nmul μ n) g = C (constantCoeff g) + (n : R) • g + ∑ k ∈ Finset.range n, at2 (cob1 μ g) (nmul μ k) (fun i => X i) := by
  first | exact @GlobalTheory.QLog.subst_nmul_eq | exact GlobalTheory.QLog.subst_nmul_eq | (intros; apply GlobalTheory.QLog.subst_nmul_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericMultOneDimOf
noncomputable section

namespace GlobalTheory.GenericProduct

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne NumberField Module

def OneGenericVector : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 →
    ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ)
      (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → whDim ψ (parInd b σ) = 1

section Twist

variable {K P V : Type} [Field K] [Group P] [AddCommGroup V] [Module K V]

def twistInv (τ : Representation K P V) (c : P →* Kˣ) : Representation K P V where
  toFun h := (((c h)⁻¹ : Kˣ) : K) • τ h
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, map_mul, mul_inv, Units.val_mul, smul_mul_smul_comm]

theorem twistInv_apply (τ : Representation K P V) (c : P →* Kˣ) (h : P) :
    twistInv τ c h = (((c h)⁻¹ : Kˣ) : K) • τ h := rfl

theorem sum_trace_mul_inv [Fintype P] [CharZero K] [FiniteDimensional K V] (τ : Representation K P V) (c : P →* Kˣ) :
    ∑ h : P, LinearMap.trace K V (τ h) * (((c h)⁻¹ : Kˣ) : K) =
      (Nat.card P : K) * (finrank K (twistInv τ c).invariants : K) := by
  have hc : (Nat.card P : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  letI : Invertible (Nat.card P : K) := invertibleOfNonzero hc
  letI : Invertible (Fintype.card P : K) := invertibleOfNonzero (by rw [← Nat.card_eq_fintype_card]; exact hc)
  have h := Representation.card_inv_mul_sum_char_eq_finrank (twistInv τ c)
  rw [← h, mul_inv_cancel_left₀ hc]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Representation.character, twistInv_apply, map_smul, smul_eq_mul, mul_comm]

end Twist

theorem sum_unip_eq {F : Type} [Field F] {r : ℕ} [Fintype (unip F r)] {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ψ : AddChar F ℂ) (τ : Representation ℂ (GL (Fin r) F) V) :
    ∑ h : unip F r, LinearMap.trace ℂ V (τ h) * (((addCharHom ψ (supHom F r) h)⁻¹ : ℂˣ) : ℂ) =
      (Nat.card (unip F r) : ℂ) * (whDim ψ τ : ℂ) := by
  have h := sum_trace_mul_inv (τ.comp (unip F r).subtype) (addCharHom ψ (supHom F r))
  have e : (twistInv (τ.comp (unip F r).subtype) (addCharHom ψ (supHom F r))).invariants =
      eig τ (unip F r : Set (GL (Fin r) F)) fun g => ψ (edgeSum supEdge g) := by
    ext v
    simp only [Representation.mem_invariants, eig, Submodule.mem_iInf, LinearMap.mem_ker, twistInv_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    have key : ∀ g : unip F r, ((((addCharHom ψ (supHom F r) g)⁻¹ : ℂˣ) : ℂ) • (τ.comp (unip F r).subtype g) v = v ↔
        τ g v = ψ (edgeSum supEdge (g : GL (Fin r) F)) • v) := by
      intro g
      have hv : ψ (edgeSum supEdge (g : GL (Fin r) F)) = ((addCharHom ψ (supHom F r) g : ℂˣ) : ℂ) := rfl
      rw [hv, Units.val_inv_eq_inv_val, inv_smul_eq_iff₀ (Units.ne_zero _)]
      rfl
    exact ⟨fun H g hg => (key ⟨g, hg⟩).1 (H ⟨g, hg⟩), fun H g => (key g).2 (H g.1 g.2)⟩
  rw [e] at h
  exact h

def piEquiv {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H) ≃ ∀ i, H i where
  toFun x i := ⟨x.1 i, x.2 i (Set.mem_univ _)⟩
  invFun y := ⟨fun i => (y i).1, fun i _ => (y i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

attribute [local instance] resField finite_res

theorem genericMultOne (hL : OneGenericVector) : GenericMultOne := by
  classical
  intro E _ _ Pg r K _ _ s ψ hψ χ hχ
  obtain ⟨b, V, i1, i2, i3, σ, hσ, hs⟩ := hχ
  letI : Fintype (P0 Pg r ψ).H := Fintype.ofFinite _
  letI : ∀ PP : ↥Pg, Fintype (unip (kP PP.1) r) := fun PP => Fintype.ofFinite _
  apply s.injective
  let ψ' : ∀ PP : ↥Pg, AddChar (kP PP.1) ℂ := fun PP => s.toMonoidHom.compAddChar (ψ PP.1)
  have hψ' : ∀ PP : ↥Pg, ψ' PP ≠ 1 := by
    intro PP h
    refine hψ PP.1 PP.2 ?_
    ext x
    apply s.injective
    have := DFunLike.congr_fun h x
    simpa [ψ'] using this
  let e : (P0 Pg r ψ).H ≃ ∀ PP : ↥Pg, unip (kP PP.1) r := piEquiv fun PP : ↥Pg => unip (kP PP.1) r
  let f : ∀ PP : ↥Pg, unip (kP PP.1) r → ℂ := fun PP h =>
    LinearMap.trace ℂ _ (parInd (F := kP PP.1) (b PP) (σ PP) h) *
      (((addCharHom (ψ' PP) (supHom (kP PP.1) r) h)⁻¹ : ℂˣ) : ℂ)
  have hf : ∀ PP : ↥Pg, ∑ h, f PP h = (Nat.card (unip (kP PP.1) r) : ℂ) := by
    intro PP
    letI : Fintype (kP PP.1) := Fintype.ofFinite _
    haveI := finite_parInd (b PP) (σ PP)
    have h1 := sum_unip_eq (ψ' PP) (parInd (F := kP PP.1) (b PP) (σ PP))
    rw [hL (kP PP.1) (ψ' PP) (hψ' PP) r (V PP) (b PP) (σ PP) (hσ PP), Nat.cast_one, mul_one] at h1
    exact h1
  have hterm : ∀ h : (P0 Pg r ψ).H, s (χ (h : G0 Pg r) * ((((P0 Pg r ψ).chi h)⁻¹ : Kˣ) : K)) = ∏ PP, f PP (e h PP) := by
    intro h
    have hchi : (P0 Pg r ψ).chi h = ∏ PP : ↥Pg, addCharHom (ψ PP.1) (supHom (kP PP.1) r) (e h PP) := by
      exact MonoidHom.finsetProd_apply (fun PP : ↥Pg => (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp
        (LevelP.prj (fun PP : ↥Pg => unip (kP PP.1) r) PP)) Finset.univ h
    rw [map_mul, hs, hchi, Units.val_inv_eq_inv_val, map_inv₀, Units.coe_prod, map_prod, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    simp only [f, Units.val_inv_eq_inv_val]
    rfl
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_congr rfl fun h _ => hterm h, map_natCast, Nat.card_congr e, Nat.card_pi, Nat.cast_prod,
    ← Finset.prod_congr rfl fun PP _ => hf PP, Fintype.prod_sum]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

end GlobalTheory.GenericProduct
end
end
