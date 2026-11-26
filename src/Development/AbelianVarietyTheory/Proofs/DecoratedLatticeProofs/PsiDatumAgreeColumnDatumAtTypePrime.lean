module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelTestFunctionsAgreeRationalPoints
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtXCastAdd
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrFrobeniusLift

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiDatumAgreeColumnDatumAtTypePrime
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiDatumAgreeColumnDatumAtTypePrime
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.PsiStep

section Red
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem q_mem : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem P.asIdeal

theorem q_ne_zero : ((qOf P : ℕ) : E) ≠ 0 := by
  have h : qOf P ≠ 0 := by
    unfold qOf
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact P.ne_bot
  exact_mod_cast h

theorem intAt_q : IntAt P (qOf P : E) := by
  have := IntAt.coe P ((qOf P : ℕ) : 𝓞 E)
  rwa [map_natCast] at this

theorem reduction_natCast_eq_zero : redP P (qOf P : E) = 0 := by
  have := reduction_coe P ((qOf P : ℕ) : 𝓞 E)
  rw [map_natCast] at this
  rw [this]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (q_mem P)

theorem pow_red (k : ℕ) : IntAt P ((qOf P : E) ^ (k + 1)) ∧ redP P ((qOf P : E) ^ (k + 1)) = 0 := by
  induction k with
  | zero =>
    rw [zero_add, pow_one]
    exact ⟨intAt_q P, reduction_natCast_eq_zero P⟩
  | succ k ih =>
    rw [pow_succ]
    exact ⟨ih.1.mul (intAt_q P), by rw [reduction_mul ih.1 (intAt_q P), ih.2, zero_mul]⟩

theorem reduction_one' : redP P (1 : E) = 1 := by
  have := reduction_coe P 1
  rwa [map_one, map_one] at this

theorem valuation_one₂ : LocE.vP P (qOf P) (1 : E) = 0 := by
  have hq0 := q_ne_zero P
  have hex : ∃ z : ℤ, IsUnit (redP P ((1 : E) / (qOf P : E) ^ z)) :=
    ⟨0, by rw [zpow_zero, div_one, reduction_one']; exact isUnit_one⟩
  have hspec : IsUnit (redP P ((1 : E) / (qOf P : E) ^ LocE.vP P (qOf P) (1 : E))) := by
    unfold LocE.vP
    exact Classical.epsilon_spec hex
  by_contra hne
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg (LocE.vP P (qOf P) (1 : E))
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk, zpow_natCast] at hspec
    by_cases hI' : IntAt P ((1 : E) / (qOf P : E) ^ (k' + 1))
    · have e : (qOf P : E) ^ (k' + 1) * (1 / (qOf P : E) ^ (k' + 1)) = 1 := by field_simp
      have h0 : redP P ((qOf P : E) ^ (k' + 1) * (1 / (qOf P : E) ^ (k' + 1))) = 0 := by
        rw [reduction_mul (pow_red P k').1 hI', (pow_red P k').2, zero_mul]
      rw [e, reduction_one'] at h0
      exact one_ne_zero h0
    · rw [reduction_eq_zero_of_not_integral P hI'] at hspec
      exact not_isUnit_zero hspec
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk, _root_.zpow_neg, zpow_natCast, div_inv_eq_mul, one_mul, (pow_red P k').2] at hspec
    exact not_isUnit_zero hspec

theorem locChar_one_ne {K : Type} [Field K] (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) :
    LocE.locChar (qOf P) cq χ (1 : E) ≠ 0 := by
  unfold LocE.locChar
  rw [valuation_one₂, zpow_zero, zpow_zero, one_mul, div_one]
  unfold LocE.unitV
  rw [dite_eq_left (by rw [reduction_one']; exact isUnit_one)]
  exact Units.ne_zero _

end Red

end GlobalTheory.SymBridge.PsiStep

namespace GlobalTheory.SymBridge.PsiStep

section Mat
variable {E : Type} [Field E]

theorem joinCol_apply {n' c' n c : ℕ} (x₀ : HomE E n' n) (y' : Sp E n) (v : Fin (n' + c') → E) (i : Fin n) :
    joinCol (c' := c') (c := c) x₀ y' v (Fin.castAdd c i) =
      x₀ (fun l => v (Fin.castAdd c' l)) i + atNL E (n' + c') n' v * y' i := by
  simp [joinCol, Loc.inX, LinearMap.funLeft]
  rfl

end Mat

theorem om_one_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (Φ : Matrix b a k → ℂ) :
    om μ 1 1 Φ = Φ := by
  funext x
  simp [om, nabs]

end GlobalTheory.SymBridge.PsiStep

namespace GlobalTheory.SymBridge.PsiStep

theorem withCol_toLoc {E k : Type} [Field E] [NumberField E] [StarRing E]
    [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k)
    {A B : Type} {n' n c' c : ℕ} (e : A ≃ Fin n) (e' : B ≃ Fin n') (hc' : c' = 0 + 1) (hc : c = 0)
    (x₀ : HomE E n' n) (y' : Sp E n) :
    withCol (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
      toLoc ι ((e.sumCongr (finCongr hc.symm)).trans finSumFinEquiv) ((e'.sumCongr (finCongr hc'.symm)).trans finSumFinEquiv)
        (joinCol (c' := c') (c := c) x₀ y') := by
  subst hc' hc
  ext (r | r) (j | j)
  · simp only [withCol, fromBlocks_apply₁₁, toLoc, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
      finSumFinEquiv_apply_left, joinCol_apply]
    have h1 : (fun l : Fin n' => (Pi.single (Fin.castAdd (0 + 1) (e' j)) (1 : E) : Fin (n' + (0 + 1)) → E)
        (Fin.castAdd (0 + 1) l)) = Pi.single (e' j) 1 := by
      funext l
      simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castAdd]
    have h2 : atNL E (n' + (0 + 1)) n' (Pi.single (Fin.castAdd (0 + 1) (e' j)) 1) = 0 := by
      have hj := (e' j).isLt
      unfold atNL
      rw [dite_eq_left (by omega)]
      simp only [LinearMap.coe_proj, Function.eval, Pi.single_apply, Fin.ext_iff, Fin.val_castAdd]
      rw [if_neg (by omega)]
    rw [h1, h2, zero_mul, add_zero]
  · simp only [withCol, fromBlocks_apply₁₂, toLoc, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, joinCol_apply]
    have h1 : (fun l : Fin n' => (Pi.single (Fin.natAdd n' (finCongr (rfl : 0 + 1 = 0 + 1) j)) (1 : E) : Fin (n' + (0 + 1)) → E)
        (Fin.castAdd (0 + 1) l)) = 0 := by
      funext l
      have hl := l.isLt
      simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd, Pi.zero_apply]
      rw [if_neg (by omega)]
    have h2 : atNL E (n' + (0 + 1)) n' (Pi.single (Fin.natAdd n' (finCongr (rfl : 0 + 1 = 0 + 1) j)) 1) = 1 := by
      unfold atNL
      rw [dite_eq_left (by omega)]
      simp only [LinearMap.coe_proj, Function.eval, Pi.single_apply, Fin.ext_iff, Fin.val_natAdd]
      rw [if_pos (by omega)]
    rw [h1, map_zero, Pi.zero_apply, h2, one_mul]
    rw [zero_add (y' (e r))]
    rfl
  · exact r.elim0
  · exact r.elim0

end GlobalTheory.SymBridge.PsiStep

namespace GlobalTheory.SymBridge.PsiStep

section Main
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu)

theorem omPhi_one_one (i : ℕ) (x : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))) :
    omPhi Ch sel mu cst i P 1 1 x = PhiAt Ch mu cst.sharp i P.1 x := by
  have hm : muAt Ch sel mu cst i P 1 ≠ 0 := by
    unfold muAt
    exact locChar_one_ne _ _ _
  unfold omPhi Loc.om
  rw [map_one, map_one, Units.val_one, valuation_one₂]
  rw [mul_inv_cancel₀ hm]
  simp only [neg_zero, zero_mul, zpow_zero, one_mul]
  rfl

end Main

end GlobalTheory.SymBridge.PsiStep

namespace GlobalTheory.SymBridge


open PsiStep in
theorem psiAgree_of_atType : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (S : SymData k s R.k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → AtType Ch sel mu cst σ₀ P ι S → PsiAgree Ch sel mu cst σ₀ P ι S := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s S _ _ ν _ hA e' e he' he
  have hc1 : cOf R s = 0 + 1 := by unfold cOf; rw [hA.steps]; omega
  have hc0 : cOf R (s + 1) = 0 := by unfold cOf; rw [hA.steps]; omega
  have hrS : R.rS = S.ρ := by
    have := S.odd
    unfold Ranks.rS; rw [hA.steps]; omega
  have hr : R.r = R.k + s + 1 := by unfold Ranks.r; rw [hA.steps]; omega
  let E' : XIx (Fin R.k) (Fin R.t) s ⊕ Fin (0 + 1) ≃ Fin (R.N s + cOf R s) :=
    (e'.sumCongr (finCongr hc1.symm)).trans finSumFinEquiv
  let E₁ : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + cOf R (s + 1)) :=
    (e.sumCongr (finCongr hc0.symm)).trans finSumFinEquiv
  have hE' : IsOrd (yPos xPos (R.N s)) E' := by
    rintro (a | a)
    · simp [E', yPos, he' a]
    · simp [E', yPos]
  have hE₁ : IsOrd (yPos xPos (R.N (s + 1))) E₁ := by
    rintro (a | a)
    · simp [E₁, yPos, he a]
    · exact a.elim0
  have hPhi := GlobalTheory.T.symLevelTestFunctions_agree_rationalPoints X.E X.K k P.1 (qOf P.1) ι σ₀ (psi0P Ch P.1) (chiP Ch P.1) s R.k S hA.tie
    R.t s 0 rfl (R.N s) (cOf R s) (R.N (s + 1)) (cOf R (s + 1)) rfl rfl hc1 hc0 E' E₁ hE' hE₁
  refine ⟨1, one_ne_zero, fun x₀ y' => ?_⟩
  have hmat : withCol (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
      toLoc ι E₁ E' (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y') := by
    exact withCol_toLoc ι e e' hc1 hc0 x₀ y'
  rw [one_mul, Chain.Psi, om_one_one, hmat, hPhi, PsiAt, omPhi_one_one]
  unfold PhiAt
  rw [if_pos hA.mem, if_pos hA.sharp, hrS, hr]

end GlobalTheory.SymBridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PsiDatumAgreeColumnDatumAtTypePrimeStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psiDatum_agree_columnDatum_at_typePrime : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (S : SymData k s R.k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → AtType Ch sel mu cst σ₀ P ι S → PsiAgree Ch sel mu cst σ₀ P ι S := by
  first | exact @GlobalTheory.SymBridge.psiAgree_of_atType | exact GlobalTheory.SymBridge.psiAgree_of_atType | (intros; apply GlobalTheory.SymBridge.psiAgree_of_atType <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsOpenMirabolicProjectionToGL
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsOpenMirabolicProjectionToGL
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

namespace GlobalTheory.OpenPr

theorem continuous_embX {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]
    {A : Type} [Fintype A] [DecidableEq A] (c : ℕ) :
    Continuous (embX c : GL A k → GL (A ⊕ Fin c) k) := by
  rw [Units.continuous_iff]
  constructor
  · change Continuous fun x : GL A k => (fromBlocks (x : Matrix A A k) 0 0 1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k)
    exact (Units.continuous_val).matrix_fromBlocks continuous_const continuous_const continuous_const
  · change Continuous fun x : GL A k => (fromBlocks ((x⁻¹ : GL A k) : Matrix A A k) 0 0 1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) k)
    exact (Units.continuous_coe_inv).matrix_fromBlocks continuous_const continuous_const continuous_const

theorem isOpen_prX : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A : Type} [Fintype A] [DecidableEq A] {c : ℕ} (Ck : Subgroup (GL (A ⊕ Fin c) k)) (O : Set (GL (A ⊕ Fin c) k)), IsOpen O → (1 : GL (A ⊕ Fin c) k) ∈ O → (∀ z ∈ R k A c 1, z ∈ O → z ∈ Ck) → IsOpen (prX Ck : Set (GL A k)) := by
  intro k _ _ _ _ A _ _ c Ck O hO h1 hCk
  have hc : Continuous (embX c : GL A k → GL (A ⊕ Fin c) k) := continuous_embX c
  have hU : IsOpen ((embX c : GL A k → GL (A ⊕ Fin c) k) ⁻¹' O) := hO.preimage hc
  have h1U : (1 : GL A k) ∈ (embX c : GL A k → GL (A ⊕ Fin c) k) ⁻¹' O := by
    simp only [Set.mem_preimage, map_one]; exact h1
  have hsub : (embX c : GL A k → GL (A ⊕ Fin c) k) ⁻¹' O ⊆ (prX Ck : Set (GL A k)) := by
    intro x hx
    refine ⟨1, one_mem _, ?_⟩
    rw [one_mul]
    exact hCk _ (Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨x, rfl⟩)) hx
  exact Subgroup.isOpen_of_mem_nhds _ (Filter.mem_of_superset (hU.mem_nhds h1U) hsub)

end GlobalTheory.OpenPr
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsOpenMirabolicProjectionToGLStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_mirabolicProjectionToGL : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {A : Type} [Fintype A] [DecidableEq A] {c : ℕ} (Ck : Subgroup (GL (A ⊕ Fin c) k)) (O : Set (GL (A ⊕ Fin c) k)), IsOpen O → (1 : GL (A ⊕ Fin c) k) ∈ O → (∀ z ∈ R k A c 1, z ∈ O → z ∈ Ck) → IsOpen (prX Ck : Set (GL A k)) := by
  first | exact @GlobalTheory.OpenPr.isOpen_prX | exact GlobalTheory.OpenPr.isOpen_prX | (intros; apply GlobalTheory.OpenPr.isOpen_prX <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemStabLocalizedStdLatticeIffIntegralGL
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemStabLocalizedStdLatticeIffIntegralGL
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

noncomputable section
namespace GlobalTheory.VolBridge.StabRead

variable {E k : Type} [Field E] [NumberField E] [Field k] [ValuativeRel k]
  {P : HeightOneSpectrum (𝓞 E)} {ι : E →+* k}

theorem mem_stdAt_iff_int (hι : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) {M : ℕ} (v : Sp E M) :
    v ∈ stdAt E M P ↔ ∀ i, ι (v i) ∈ 𝒪[k] := by
  rw [GlobalTheory.Proof.mem_integralGLAtPrime_of_congruent_one_mod_pow.mem_stdAt]
  exact forall_congr' fun i => (hι _).symm

theorem single_mem_stdAt (hι : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) {M : ℕ} (m : Fin M) :
    (Pi.single m 1 : Sp E M) ∈ stdAt E M P := by
  rw [mem_stdAt_iff_int hι]
  intro i
  rw [Pi.single_apply]
  split_ifs
  · rw [map_one]; exact Subring.one_mem _
  · rw [map_zero]; exact Subring.zero_mem _

theorem map_mem_stdAt (hι : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) {M : ℕ} (y : Sp E M ≃ₗ[E] Sp E M)
    (hy : ∀ i m, ι (y (Pi.single m 1) i) ∈ 𝒪[k]) {v : Sp E M} (hv : v ∈ stdAt E M P) : y v ∈ stdAt E M P := by
  rw [mem_stdAt_iff_int hι] at hv ⊢
  intro i
  have e : y v = LinearMap.toMatrix' (y : Sp E M →ₗ[E] Sp E M) *ᵥ v := (LinearMap.toMatrix'_mulVec _ v).symm
  rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mulVec, dotProduct, LinearMap.toMatrix'_apply, map_sum, map_mul]
  exact Subring.sum_mem _ fun m _ => Subring.mul_mem _ (hy i m) (hv m)

end GlobalTheory.VolBridge.StabRead


open GlobalTheory.VolBridge.StabRead in
theorem GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO {E k : Type} [Field E] [NumberField E] [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (ι : E →+* k)
    (hι : ∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) {A : Type} [Fintype A] [DecidableEq A] {M : ℕ} (e : A ≃ Fin M)
    (x : Sp E M ≃ₗ[E] Sp E M) : x ∈ stabL E M (stdAt E M P) ↔ locHom ι e x ∈ KO k A := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff]
  constructor
  · intro hx
    have hx' : x⁻¹ ∈ stabL E M (stdAt E M P) := inv_mem hx
    refine ⟨fun a b => ?_, fun a b => ?_⟩
    · change ι (x (Pi.single (e b) 1) (e a)) ∈ 𝒪[k]
      exact (mem_stdAt_iff_int hι _).1 ((hx _).2 (single_mem_stdAt hι _)) _
    · change ι ((x⁻¹ : Sp E M ≃ₗ[E] Sp E M) (Pi.single (e b) 1) (e a)) ∈ 𝒪[k]
      exact (mem_stdAt_iff_int hι _).1 ((hx' _).2 (single_mem_stdAt hι _)) _
  · rintro ⟨h1, h2⟩
    have i1 : ∀ i m, ι (x (Pi.single m 1) i) ∈ 𝒪[k] := fun i m => by
      have h := h1 (e.symm i) (e.symm m)
      change ι (x (Pi.single (e (e.symm m)) 1) (e (e.symm i))) ∈ 𝒪[k] at h
      simpa only [Equiv.apply_symm_apply] using h
    have i2 : ∀ i m, ι ((x⁻¹ : Sp E M ≃ₗ[E] Sp E M) (Pi.single m 1) i) ∈ 𝒪[k] := fun i m => by
      have h := h2 (e.symm i) (e.symm m)
      change ι ((x⁻¹ : Sp E M ≃ₗ[E] Sp E M) (Pi.single (e (e.symm m)) 1) (e (e.symm i))) ∈ 𝒪[k] at h
      simpa only [Equiv.apply_symm_apply] using h
    intro v
    constructor
    · intro hv
      have h := map_mem_stdAt hι _ i2 hv
      have ev : (x⁻¹ : Sp E M ≃ₗ[E] Sp E M) (x v) = v := x.symm_apply_apply v
      rwa [ev] at h
    · exact map_mem_stdAt hι x i1
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemStabLocalizedStdLatticeIffIntegralGLStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_stabLocalizedStdLattice_iff_integralGL : ∀ {E k : Type} [Field E] [NumberField E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (ι : E →+* k), (∀ a, ι a ∈ 𝒪[k] ↔ IntAt P a) → ∀ {A : Type} [Fintype A] [DecidableEq A] {M : ℕ} (e : A ≃ Fin M) (x : Sp E M ≃ₗ[E] Sp E M), x ∈ stabL E M (stdAt E M P) ↔ locHom ι e x ∈ KO k A := by
  first | exact @GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO | exact GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO | (intros; apply GlobalTheory.VolBridge.mem_stabL_stdAt_iff_locHom_mem_KO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarOpenSubgroupVolumeInvEqRelIndex
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarOpenSubgroupVolumeInvEqRelIndex
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

namespace GlobalTheory.OpenVolIndex

theorem measure_toReal_inv_eq_relIndex : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (H L : Subgroup G), H ≤ L → IsOpen (H : Set G) → IsCompact (L : Set G) → μ (L : Set G) = 1 → (μ (H : Set G)).toReal⁻¹ = (H.relIndex L : ℝ) := by
  intro G _ _ _ _ _ μ _ H L hHL hH hL hμL
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have hHo : IsOpen ((H.subgroupOf L : Subgroup L) : Set L) :=
    hH.preimage continuous_subtype_val
  haveI : Finite (L ⧸ H.subgroupOf L) := Subgroup.quotient_finite_of_isOpen _ hHo
  haveI : (H.subgroupOf L).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have key := GlobalTheory.BaseModule.relIndex_mul_measure' H L hHL hH.measurableSet μ
  rw [hμL] at key
  have htop : μ (H : Set G) ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [hμL]; exact ENNReal.one_ne_top) (measure_mono hHL)
  have hr : (H.relIndex L : ℝ) * (μ (H : Set G)).toReal = 1 := by
    have := congrArg ENNReal.toReal key
    simpa [ENNReal.toReal_mul] using this
  exact (eq_inv_of_mul_eq_one_left hr).symm

end GlobalTheory.OpenVolIndex
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarOpenSubgroupVolumeInvEqRelIndexStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_open_subgroup_volume_inv_eq_relIndex : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (H L : Subgroup G), H ≤ L → IsOpen (H : Set G) → IsCompact (L : Set G) → μ (L : Set G) = 1 → (μ (H : Set G)).toReal⁻¹ = (H.relIndex L : ℝ) := by
  first | exact @GlobalTheory.OpenVolIndex.measure_toReal_inv_eq_relIndex | exact GlobalTheory.OpenVolIndex.measure_toReal_inv_eq_relIndex | (intros; apply GlobalTheory.OpenVolIndex.measure_toReal_inv_eq_relIndex <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsColSpaceAutToLocalGLMemOpenDense
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsColSpaceAutToLocalGLMemOpenDense
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

theorem GlobalTheory.denseGL_completion : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k), DenseRange ι → ∀ {A : Type} [Fintype A] [DecidableEq A] {M : ℕ} (e : A ≃ Fin M) (y : GL A k) (V : Set (GL A k)), IsOpen V → y ∈ V → ∃ x : Sp E M ≃ₗ[E] Sp E M, locHom ι e x ∈ V := by
  intro E k _ _ _ _ _ ι hι A _ _ M e y V hV hy
  haveI : T2Space k := by
    rw [t2Space_iff_disjoint_nhds]
    intro a b hab
    have hne : valuation k (a - b) ≠ 0 := (Valuation.ne_zero_iff _).2 (sub_ne_zero.2 hab)
    let γ : (ValueGroupWithZero k)ˣ := Units.mk0 _ hne
    rw [Filter.disjoint_iff]
    refine ⟨{z | valuation k (z - a) < γ}, (IsValuativeTopology.mem_nhds_iff').2 ⟨γ, subset_rfl⟩,
      {z | valuation k (z - b) < γ}, (IsValuativeTopology.mem_nhds_iff').2 ⟨γ, subset_rfl⟩, ?_⟩
    rw [Set.disjoint_left]
    intro z hz1 hz2
    have h := Valuation.map_sub_lt _ (show valuation k (z - b) < γ from hz2)
      (show valuation k (z - a) < γ from hz1)
    have e : (z - b) - (z - a) = a - b := by ring
    rw [e, Units.val_mk0] at h
    exact lt_irrefl _ h
  let φ : Matrix A A k → Matrix A A k × (Matrix A A k)ᵐᵒᵖ := fun m => (m, MulOpposite.op m⁻¹)
  have hφ : ∀ g : GL A k, φ g.val = Units.embedProduct _ g := by
    intro g
    refine Prod.ext rfl ?_
    simp [φ, Matrix.coe_units_inv]
  obtain ⟨W, hW, rfl⟩ := (Units.isInducing_embedProduct (M := Matrix A A k)).isOpen_iff.1 hV
  have hdet : y.val.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero
  have hinv : ContinuousAt (fun m : Matrix A A k => m⁻¹) y.val := by
    have h1 : (fun m : Matrix A A k => m⁻¹) = fun m => (m.det)⁻¹ • m.adjugate := by
      funext m; rw [Matrix.inv_def, Ring.inverse_eq_inv']
    rw [h1]
    exact ContinuousAt.smul ((continuousAt_inv₀ hdet).comp (continuous_id.matrix_det).continuousAt)
      (continuous_id.matrix_adjugate).continuousAt
  have hφc : ContinuousAt φ y.val :=
    ContinuousAt.prodMk continuousAt_id (MulOpposite.continuous_op.continuousAt.comp hinv)
  have hU : φ ⁻¹' W ∩ {m : Matrix A A k | m.det ≠ 0} ∈ nhds y.val := by
    refine Filter.inter_mem (hφc.preimage_mem_nhds (hW.mem_nhds ?_)) ?_
    · rw [hφ]; exact hy
    · exact (isOpen_compl_singleton.preimage (continuous_id.matrix_det)).mem_nhds hdet
  have hD : DenseRange (fun m : Matrix A A E => m.map ι) :=
    DenseRange.piMap (fun _ => DenseRange.piMap (fun _ => hι))
  obtain ⟨_, ⟨m', rfl⟩, hm'W, hm'd⟩ := Dense.inter_nhds_nonempty hD hU
  have hm'u : IsUnit m'.det := by
    refine isUnit_iff_ne_zero.2 ?_
    intro h0
    apply hm'd
    show (m'.map ι).det = 0
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  let n : Matrix (Fin M) (Fin M) E := m'.submatrix e.symm e.symm
  have hn : IsUnit n.det := by
    simpa [n, Matrix.det_submatrix_equiv_self] using hm'u
  refine ⟨Matrix.toLinearEquiv' n (Matrix.invertibleOfIsUnitDet n hn), ?_⟩
  show Units.embedProduct _ _ ∈ W
  rw [← hφ, locHom_val, GlobalTheory.SymBridge.toLoc_eq_map_toMatrix']
  have h2 : LinearMap.toMatrix' (Matrix.toLinearEquiv' n (Matrix.invertibleOfIsUnitDet n hn)).toLinearMap = n := by
    exact LinearMap.toMatrix'_toLin' n
  rw [h2]
  have h3 : n.submatrix e e = m' := by
    ext i j; simp [n]
  rw [h3]
  exact hm'W
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsColSpaceAutToLocalGLMemOpenDenseStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_colSpaceAutToLocalGL_mem_open_dense : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k), DenseRange ι → ∀ {A : Type} [Fintype A] [DecidableEq A] {M : ℕ} (e : A ≃ Fin M) (y : GL A k) (V : Set (GL A k)), IsOpen V → y ∈ V → ∃ x : Sp E M ≃ₗ[E] Sp E M, locHom ι e x ∈ V := by
  first | exact @GlobalTheory.denseGL_completion | exact GlobalTheory.denseGL_completion | (intros; apply GlobalTheory.denseGL_completion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsN1LocalHomMemOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsN1LocalHomMemOpen
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

noncomputable section
namespace GlobalTheory.VolBridge.NormOneIdeleAutomorphisms

variable {E : Type} [Field E] {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ}

def autOf (e : A ⊕ Fin c ≃ Fin (M + c')) (g : GL (A ⊕ Fin c) E) : (Fin (M + c') → E) ≃ₗ[E] (Fin (M + c') → E) :=
  LinearEquiv.ofLinear (Matrix.toLin' (g.val.submatrix e.symm e.symm)) (Matrix.toLin' ((g⁻¹).val.submatrix e.symm e.symm))
    (by rw [← Matrix.toLin'_mul, Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv, Matrix.toLin'_one])
    (by rw [← Matrix.toLin'_mul, Matrix.submatrix_mul_equiv, Units.inv_mul, Matrix.submatrix_one_equiv, Matrix.toLin'_one])

theorem autOf_apply (e : A ⊕ Fin c ≃ Fin (M + c')) (g : GL (A ⊕ Fin c) E) (v : Fin (M + c') → E) :
    autOf e g v = (g.val.submatrix e.symm e.symm).mulVec v := rfl

theorem autOf_inv_apply (e : A ⊕ Fin c ≃ Fin (M + c')) (g : GL (A ⊕ Fin c) E) (v : Fin (M + c') → E) :
    (autOf e g)⁻¹ v = ((g⁻¹).val.submatrix e.symm e.symm).mulVec v := rfl

theorem lev_symm (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)
    (l : Fin (M + c')) : lev (n := A) (c := c) 1 (e.symm l) = if l.val < M then 1 else l.val - M + 1 := by
  rcases hm : e.symm l with a | i
  · have h1 : l = e (Sum.inl a) := by rw [← hm]; simp
    have := eX_lt e hcc he a
    rw [← h1] at this
    simp [lev, this]
  · have h1 : l = e (Sum.inr i) := by rw [← hm]; simp
    have := he i
    rw [← h1] at this
    simp [lev, this]

theorem mulVec_fix (e : A ⊕ Fin c ≃ Fin (M + c')) (m : Matrix (A ⊕ Fin c) (A ⊕ Fin c) E)
    (hm : ∀ r s, lev 1 s ≤ lev 1 r → m r s = (1 : Matrix (A ⊕ Fin c) (A ⊕ Fin c) E) r s) (v : Fin (M + c') → E)
    (l : Fin (M + c')) (hv : ∀ j, v j ≠ 0 → lev (n := A) (c := c) 1 (e.symm j) ≤ lev 1 (e.symm l)) :
    (m.submatrix e.symm e.symm).mulVec v l = v l := by
  simp only [Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
  rw [Finset.sum_eq_single l]
  · rw [hm _ _ le_rfl, Matrix.one_apply_eq, one_mul]
  · intro j _ hj
    by_cases h0 : v j = 0
    · rw [h0, mul_zero]
    · rw [hm _ _ (hv j h0), Matrix.one_apply_ne (fun h => hj (e.symm.injective h).symm), zero_mul]
  · simp

theorem mem_normOneIdeles (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)
    (g : GL (A ⊕ Fin c) E) (hg : g ∈ N E A c 1) : autOf e g ∈ Loc.N1 E M c' := by
  have hL := lev_symm e hcc he
  have key : ∀ g : GL (A ⊕ Fin c) E, g ∈ N E A c 1 → ∀ (v : Fin (M + c') → E) (l : Fin (M + c')),
      (∀ j, v j ≠ 0 → lev (n := A) (c := c) 1 (e.symm j) ≤ lev 1 (e.symm l)) →
      (g.val.submatrix e.symm e.symm).mulVec v l = v l := fun g hg v l hv =>
    mulVec_fix e g.val (Model.mem_N_iff.1 hg) v l hv
  have hR : ∀ g : GL (A ⊕ Fin c) E, g ∈ N E A c 1 → ∀ r : (Fin (M + c') → E) ≃ₗ[E] (Fin (M + c') → E),
      (∀ v, r v = (g.val.submatrix e.symm e.symm).mulVec v) → Loc.R1cond E M c' r := by
    intro g hg r hr
    refine ⟨fun i v hv => ?_, ?_, fun i => ?_⟩
    · intro l hl
      simp only [Set.mem_setOf_eq, not_lt] at hl
      rw [hr, key g hg v l ?_]
      · exact hv l (by simpa using hl)
      · intro j hj
        have : j.val < M + i := by
          by_contra h
          exact hj (hv j (by simpa using h))
        rw [hL, hL]; split_ifs <;> omega
    · funext l
      rw [hr, key g hg _ l]
      intro j hj
      have : j.val = M := by
        by_contra h; exact hj (by simp [Loc.eN, h])
      rw [hL, hL]; split_ifs <;> omega
    · intro l hl
      simp only [Set.mem_setOf_eq, not_lt] at hl
      rw [Pi.sub_apply, hr, key g hg _ l, sub_self]
      intro j hj
      have : j.val = M + i := by
        by_contra h; exact hj (by simp [Loc.eN, h])
      rw [hL, hL]; split_ifs <;> omega
  refine ⟨⟨hR g hg _ (autOf_apply e g), hR g⁻¹ (inv_mem hg) _ (autOf_inv_apply e g)⟩, fun x => ?_⟩
  funext l
  rw [autOf_apply, key g hg _ l]
  intro j hj
  have : j.val < M := by
    by_contra h
    exact hj (by simp [Loc.inX, h])
  rw [hL, hL]; split_ifs <;> omega

theorem locHom_autOf {k : Type} [Field k] (ι : E →+* k) (e : A ⊕ Fin c ≃ Fin (M + c')) (g : GL (A ⊕ Fin c) E) :
    (locHom ι e (autOf e g)).val = g.val.map ι := by
  rw [locHom_val]
  ext i j
  simp [GlobalTheory.SymBridge.toLoc, autOf_apply, Matrix.mulVec_single_one]

end GlobalTheory.VolBridge.NormOneIdeleAutomorphisms

namespace GlobalTheory.VolBridge
open NormOneIdeleAutomorphisms

theorem exists_N1_local_hom_mem_open : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k), DenseRange ι → ∀ {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')), c' = c → (∀ i : Fin c, (e (Sum.inr i)).val = M + i.val) → ∀ u ∈ N k A c 1, ∀ V : Set (GL (A ⊕ Fin c) k), IsOpen V → u ∈ V → ∃ x ∈ Loc.N1 E M c', locHom ι e x ∈ V := by
  intro E k _ _ _ _ _ ι hι A _ _ M c c' e hcc he u hu V hV huV
  let f : (VolN.Ix A c 1 → k) → GL (A ⊕ Fin c) k := fun a => ((Model.mkNel 1 a : N k A c 1) : GL (A ⊕ Fin c) k)
  have hf : Continuous f := continuous_subtype_val.comp (VolN.continuous_mkNel 1)
  have hW : IsOpen (f ⁻¹' V) := hV.preimage hf
  have h0 : VolN.co 1 ⟨u, hu⟩ ∈ f ⁻¹' V := by
    show ((Model.mkNel 1 (VolN.co 1 ⟨u, hu⟩) : N k A c 1) : GL (A ⊕ Fin c) k) ∈ V
    rw [VolN.mkNel_co]; exact huV
  have hD : DenseRange (Pi.map fun (_ : VolN.Ix A c 1) => (ι : E → k)) := DenseRange.piMap fun _ => hι
  obtain ⟨b, hb⟩ := hD.exists_mem_open hW ⟨_, h0⟩
  refine ⟨autOf e ((Model.mkNel 1 b : N E A c 1) : GL (A ⊕ Fin c) E), mem_normOneIdeles e hcc he _ (Model.mkNel 1 b).2, ?_⟩
  have : locHom ι e (autOf e ((Model.mkNel 1 b : N E A c 1) : GL (A ⊕ Fin c) E)) = f (Pi.map (fun _ => (ι : E → k)) b) := by
    apply Units.ext
    rw [locHom_autOf]
    show _ = ((Model.mkNel 1 _ : N k A c 1) : GL (A ⊕ Fin c) k).val
    rw [VolN.val_mkNel, VolN.val_mkNel]
    ext r s
    simp only [Matrix.map_apply, Matrix.add_apply, map_add (f := _), VolN.ext0, Matrix.of_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [this]; exact hb

end GlobalTheory.VolBridge
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsN1LocalHomMemOpenStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_N1_locHom_mem_open : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k), DenseRange ι → ∀ {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')), c' = c → (∀ i : Fin c, (e (Sum.inr i)).val = M + i.val) → ∀ u ∈ N k A c 1, ∀ V : Set (GL (A ⊕ Fin c) k), IsOpen V → u ∈ V → ∃ x ∈ Loc.N1 E M c', locHom ι e x ∈ V := by
  first | exact @GlobalTheory.VolBridge.exists_N1_local_hom_mem_open | exact GlobalTheory.VolBridge.exists_N1_local_hom_mem_open | (intros; apply GlobalTheory.VolBridge.exists_N1_local_hom_mem_open <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemMirabolicProjectionIffColSpaceAutToLocalGL
section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemMirabolicProjectionIffColSpaceAutToLocalGL
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge

namespace GlobalTheory.VolBridge

section PrXIff
variable {E : Type} [Field E] {M c' : ℕ}

theorem inX_castAdd (v : Sp E M) (i : Fin M) : Loc.inX E M c' v (Fin.castAdd c' i) = v i := by
  simp [Loc.inX]

theorem inX_natAdd (v : Sp E M) (i : Fin c') : Loc.inX E M c' v (Fin.natAdd M i) = 0 := by
  simp [Loc.inX]

theorem extX_inX (y : Sp E M ≃ₗ[E] Sp E M) (v : Sp E M) :
    extX c' y (Loc.inX E M c' v) = Loc.inX E M c' (y v) := by
  funext l
  refine Fin.addCases (fun i => ?_) (fun i => ?_) l
  · rw [extX_castAdd, inX_castAdd]
    have h : (fun j => Loc.inX E M c' v (Fin.castAdd c' j)) = v := funext fun j => inX_castAdd v j
    rw [h]
  · rw [extX_natAdd, inX_natAdd, inX_natAdd]

variable {A : Type} {c : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c)
  (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)

include he in
theorem e_inl (a : A) : e (Sum.inl a) = Fin.castAdd c' (eX e hcc he a) := Fin.ext (by simp [eX_val])

include he in
theorem e_inr (i : Fin c) : e (Sum.inr i) = Fin.natAdd M (⟨i.val, hcc ▸ i.isLt⟩ : Fin c') := Fin.ext (by simp [he])

theorem single_inl (a : A) :
    (Pi.single (e (Sum.inl a)) 1 : Sp E (M + c')) = Loc.inX E M c' (Pi.single (eX e hcc he a) 1) := by
  rw [e_inl e hcc he]
  funext l
  refine Fin.addCases (fun i => ?_) (fun i => ?_) l
  · rw [inX_castAdd]
    by_cases h : i = eX e hcc he a
    · subst h; simp
    · rw [Pi.single_eq_of_ne (fun h' => h (Fin.castAdd_injective _ _ h')), Pi.single_eq_of_ne h]
  · rw [inX_natAdd, Pi.single_eq_of_ne]
    intro h
    have := congrArg Fin.val h
    simp at this
    omega

end PrXIff

section Blocks
variable {E k : Type} [Field E] [Field k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ}
  (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val)

theorem locHom_inl_inl (r : Sp E (M + c') ≃ₗ[E] Sp E (M + c')) (y : Sp E M ≃ₗ[E] Sp E M)
    (hr : ∀ v, r (Loc.inX E M c' v) = Loc.inX E M c' (y v)) (a b : A) :
    (locHom ι e r).val (Sum.inl a) (Sum.inl b) = (locHom ι (eX e hcc he) y).val a b := by
  show ι (r (Pi.single (e (Sum.inl b)) 1) (e (Sum.inl a))) = ι (y (Pi.single (eX e hcc he b) 1) (eX e hcc he a))
  rw [single_inl e hcc he, hr, e_inl e hcc he, inX_castAdd]

theorem locHom_extX (y : Sp E M ≃ₗ[E] Sp E M) :
    locHom ι e (extX c' y) = embX c (locHom ι (eX e hcc he) y) := by
  ext i j
  rw [GlobalTheory.RootEx.VolN.val_embX]
  show ι (extX c' y (Pi.single (e j) 1) (e i)) = _
  rcases i with a | s
  · rw [e_inl e hcc he, extX_castAdd]
    rcases j with b | t
    · rw [single_inl e hcc he]
      have h : (fun l => Loc.inX E M c' (Pi.single (eX e hcc he b) (1 : E)) (Fin.castAdd c' l)) = Pi.single (eX e hcc he b) 1 :=
        funext fun l => inX_castAdd _ l
      rw [h]
      rfl
    · have h : (fun l => (Pi.single (e (Sum.inr t)) (1 : E) : Sp E (M + c')) (Fin.castAdd c' l)) = 0 := by
        funext l
        rw [Pi.single_eq_of_ne]
        · rfl
        intro h'
        have := congrArg Fin.val h'
        simp [he] at this
        omega
      rw [h, map_zero]
      simp
  · rw [e_inr e hcc he, extX_natAdd]
    rcases j with b | t
    · rw [Pi.single_eq_of_ne]
      · simp
      intro h'
      have := congrArg Fin.val h'
      simp [eX_val] at this
      have := eX_lt e hcc he b
      omega
    · rw [e_inr e hcc he]
      by_cases h : s = t
      · subst h; simp
      · rw [Pi.single_eq_of_ne]
        · simp [Matrix.one_apply, h]
        intro h'
        have := congrArg Fin.val h'
        simp at this
        exact h (Fin.ext this)

end Blocks

theorem prX_iff_locHom : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val), (∀ x, x ∈ Loc.N1 E M c' ↔ locHom ι e x ∈ N k A c 1) → (∀ u ∈ N k A c 1, ∀ V : Set (GL (A ⊕ Fin c) k), IsOpen V → u ∈ V → ∃ x ∈ Loc.N1 E M c', locHom ι e x ∈ V) → ∀ (CE : Subgroup (Sp E (M + c') ≃ₗ[E] Sp E (M + c'))) (Ck : Subgroup (GL (A ⊕ Fin c) k)) (O : Set (GL (A ⊕ Fin c) k)), IsOpen O → (∀ z ∈ R k A c 1, z ∈ Ck ↔ z ∈ O) → Ck ≤ R k A c 1 → (∀ x, x ∈ CE ↔ locHom ι e x ∈ Ck) → ∀ y, y ∈ Loc.prX CE ↔ locHom ι (eX e hcc he) y ∈ prX Ck := by
  intro E k _ _ _ _ _ ι A _ _ M c c' e hcc he hN hdense CE Ck O hO hCkO hCkR hCE y
  constructor
  · rintro ⟨r, hr, hry⟩
    have hg : locHom ι e r ∈ Ck := (hCE r).1 hr
    obtain ⟨x', u, hu, hxu⟩ := GlobalTheory.RootEx.VolN.exists_of_mem_R (hCkR hg)
    have hu' := GlobalTheory.RootEx.Model.mem_N_iff.1 hu
    have hx' : x' = locHom ι (eX e hcc he) y := by
      ext a b
      rw [← locHom_inl_inl ι e hcc he r y hry a b, hxu, Units.val_mul, GlobalTheory.RootEx.VolN.val_embX, Matrix.mul_apply,
        Fintype.sum_sum_type]
      have h1 : ∀ a', u.val (Sum.inl a') (Sum.inl b) = if a' = b then 1 else 0 := fun a' => by
        rw [hu' (Sum.inl a') (Sum.inl b) le_rfl]
        simp [Matrix.one_apply]
      simp [h1]
    refine ⟨embX c x' * u * (embX c x')⁻¹, ?_, ?_⟩
    · have := GlobalTheory.RootEx.Model.conj_mem hu x'⁻¹
      simpa [map_inv, inv_inv] using this
    · rw [← hx']
      simpa [mul_assoc, ← hxu] using hg
  · rintro ⟨u, hu, huC⟩
    set x := locHom ι (eX e hcc he) y with hx
    have huO : u * embX c x ∈ O := (hCkO _ (hCkR huC)).1 huC
    have hV : IsOpen {v : GL (A ⊕ Fin c) k | v * embX c x ∈ O} := hO.preimage (continuous_mul_const _)
    obtain ⟨x₀, hx₀, hx₀V⟩ := hdense u hu _ hV huO
    refine ⟨x₀ * extX c' y, ?_, fun v => ?_⟩
    · rw [hCE, map_mul, locHom_extX ι e hcc he]
      have hR : locHom ι e x₀ * embX c x ∈ R k A c 1 :=
        mul_mem (Subgroup.mem_sup_right ((hN x₀).1 hx₀)) (Subgroup.mem_sup_left ⟨x, rfl⟩)
      exact (hCkO _ hR).2 hx₀V
    · show x₀ (extX c' y (Loc.inX E M c' v)) = _
      rw [extX_inX]
      exact (Subgroup.mem_inf.1 hx₀).2 (y v)

end GlobalTheory.VolBridge
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemMirabolicProjectionIffColSpaceAutToLocalGLStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.VolBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_mirabolicProjection_iff_colSpaceAutToLocalGL : ∀ {E k : Type} [Field E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k) {A : Type} [Fintype A] [DecidableEq A] {M c c' : ℕ} (e : A ⊕ Fin c ≃ Fin (M + c')) (hcc : c' = c) (he : ∀ i : Fin c, (e (Sum.inr i)).val = M + i.val), (∀ x, x ∈ Loc.N1 E M c' ↔ locHom ι e x ∈ N k A c 1) → (∀ u ∈ N k A c 1, ∀ V : Set (GL (A ⊕ Fin c) k), IsOpen V → u ∈ V → ∃ x ∈ Loc.N1 E M c', locHom ι e x ∈ V) → ∀ (CE : Subgroup (Sp E (M + c') ≃ₗ[E] Sp E (M + c'))) (Ck : Subgroup (GL (A ⊕ Fin c) k)) (O : Set (GL (A ⊕ Fin c) k)), IsOpen O → (∀ z ∈ R k A c 1, z ∈ Ck ↔ z ∈ O) → Ck ≤ R k A c 1 → (∀ x, x ∈ CE ↔ locHom ι e x ∈ Ck) → ∀ y, y ∈ Loc.prX CE ↔ locHom ι (eX e hcc he) y ∈ prX Ck := by
  first | exact @GlobalTheory.VolBridge.prX_iff_locHom | exact GlobalTheory.VolBridge.prX_iff_locHom | (intros; apply GlobalTheory.VolBridge.prX_iff_locHom <;> assumption)
end
end
