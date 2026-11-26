module

public import Mathlib

@[expose] public section

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField
open scoped WithZero

namespace Formalism.L2.Pj

section Base

variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K]

def vLa (la : HeightOneSpectrum R) (x : K) : ℤ := -WithZero.log (la.valuation K x)

end Base

section Dvr

variable (V : Type) {K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
  [Algebra V K'] [IsFractionRing V K']

def valV : Valuation K' ℤᵐ⁰ := (IsDiscreteValuationRing.maximalIdeal V).valuation K'

def vV (x : K') : ℤ := -WithZero.log (valV V x)

variable {V}

lemma valV_ne_zero {x : K'} (hx : x ≠ 0) : valV V x ≠ 0 := by
  simpa [valV] using hx

lemma vV_mul {x y : K'} (hx : x ≠ 0) (hy : y ≠ 0) : vV V (x * y) = vV V x + vV V y := by
  simp only [vV, map_mul, WithZero.log_mul (valV_ne_zero hx) (valV_ne_zero hy)]
  ring

lemma min_le_vV_add {x y : K'} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (vV V x) (vV V y) ≤ vV V (x + y) := by
  have h := (valV V).map_add x y
  rcases max_choice (valV V x) (valV V y) with hm | hm <;> rw [hm] at h
  · have := (WithZero.log_le_log (valV_ne_zero hxy) (valV_ne_zero hx)).2 h
    exact (min_le_left _ _).trans (by simp only [vV]; omega)
  · have := (WithZero.log_le_log (valV_ne_zero hxy) (valV_ne_zero hy)).2 h
    exact (min_le_right _ _).trans (by simp only [vV]; omega)

variable (V)

def nval (e : ℕ) (x : K') : EReal :=
  open Classical in if x = 0 then ⊤ else (((vV V x : ℝ) / e : ℝ) : EReal)

variable {V}

lemma nval_zero (e : ℕ) : nval V e (0 : K') = ⊤ := by simp [nval]

lemma nval_of_ne {e : ℕ} {x : K'} (hx : x ≠ 0) :
    nval V e x = (((vV V x : ℝ) / e : ℝ) : EReal) := by
  simp [nval, hx]

lemma nval_ne_bot (e : ℕ) (x : K') : nval V e x ≠ ⊥ := by
  unfold nval; split_ifs <;> simp

lemma nval_add (e : ℕ) (x y : K') : min (nval V e x) (nval V e y) ≤ nval V e (x + y) := by
  by_cases hxy : x + y = 0
  · rw [hxy, nval_zero]; exact le_top
  by_cases hx : x = 0
  · subst hx; simp
  by_cases hy : y = 0
  · subst hy; simp
  rw [nval_of_ne hx, nval_of_ne hy, nval_of_ne hxy]
  rcases min_le_iff.1 (min_le_vV_add (V := V) hx hy hxy) with h | h
  · exact min_le_iff.2 (Or.inl (EReal.coe_le_coe_iff.2
      (div_le_div_of_nonneg_right (by exact_mod_cast h) (Nat.cast_nonneg e))))
  · exact min_le_iff.2 (Or.inr (EReal.coe_le_coe_iff.2
      (div_le_div_of_nonneg_right (by exact_mod_cast h) (Nat.cast_nonneg e))))

lemma nval_mul (e : ℕ) (x y : K') : nval V e (x * y) = nval V e x + nval V e y := by
  by_cases hx : x = 0
  · subst hx; rw [zero_mul, nval_zero, EReal.top_add_of_ne_bot (nval_ne_bot e y)]
  by_cases hy : y = 0
  · subst hy; rw [mul_zero, nval_zero, EReal.add_top_of_ne_bot (nval_ne_bot e x)]
  rw [nval_of_ne hx, nval_of_ne hy, nval_of_ne (mul_ne_zero hx hy), vV_mul hx hy,
    Int.cast_add, add_div, EReal.coe_add]

lemma nval_mul_unit (e : ℕ) {u : K'} (hu : u ≠ 0) (hu0 : vV V u = 0) (x : K') :
    nval V e (u * x) = nval V e x := by
  rw [nval_mul, nval_of_ne hu, hu0]; simp

lemma nval_bc {V' K'' : Type} [CommRing V'] [IsDomain V'] [IsDiscreteValuationRing V'] [Field K'']
    [Algebra V' K''] [IsFractionRing V' K''] (i : K' →+* K'') {r : ℕ} (hr : 0 < r)
    (hi : ∀ x, vV V' (i x) = (r : ℤ) * vV V x) (e : ℕ) (x : K') :
    nval V' (r * e) (i x) = nval V e x := by
  by_cases hx : x = 0
  · subst hx; rw [map_zero, nval_zero, nval_zero]
  rw [nval_of_ne ((map_ne_zero i).2 hx), nval_of_ne hx, hi]
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  congr 1; push_cast; exact mul_div_mul_left _ _ hr'

end Dvr

structure CDVR where

  V : Type
  [cr : CommRing V]
  [dom : IsDomain V]
  [dvr : IsDiscreteValuationRing V]
  [cpl : IsAdicComplete (IsLocalRing.maximalIdeal V) V]
  [ch0 : CharZero V]

attribute [instance] CDVR.cr CDVR.dom CDVR.dvr CDVR.cpl CDVR.ch0

abbrev CDVR.Fr (T : CDVR) : Type := FractionRing T.V

def CDVR.FinRes (T : CDVR) : Prop := Finite (IsLocalRing.ResidueField T.V)

section Over

variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K]
  [IsFractionRing R K]

def OverLa (la : HeightOneSpectrum R) (V : Type) {K' : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Field K'] [Algebra V K'] [IsFractionRing V K'] (ι : K →+* K')
    (e : ℕ) : Prop :=
  0 < e ∧ ∀ a : K, vV V (ι a) = (e : ℤ) * vLa la a

variable {la : HeightOneSpectrum R} {V : Type} {K' : Type} [CommRing V] [IsDomain V]
  [IsDiscreteValuationRing V] [Field K'] [Algebra V K'] [IsFractionRing V K']

lemma nval_smul {ι : K →+* K'} {e : ℕ} (ho : OverLa la V ι e) {a : K} (ha : a ≠ 0) (x : K') :
    nval V e (ι a * x) = (((vLa la a : ℤ) : ℝ) : EReal) + nval V e x := by
  rw [nval_mul, nval_of_ne ((map_ne_zero ι).2 ha), ho.2 a]
  congr 1
  have he : (e : ℝ) ≠ 0 := by exact_mod_cast ho.1.ne'
  congr 1; push_cast; field_simp

lemma OverLa.bc {ι : K →+* K'} {e : ℕ} (ho : OverLa la V ι e) {V' K'' : Type} [CommRing V']
    [IsDomain V'] [IsDiscreteValuationRing V'] [Field K''] [Algebra V' K''] [IsFractionRing V' K'']
    (i : K' →+* K'') {r : ℕ} (hr : 0 < r) (hi : ∀ x, vV V' (i x) = (r : ℤ) * vV V x) :
    OverLa la V' (i.comp ι) (r * e) :=
  ⟨Nat.mul_pos hr ho.1, fun a => by rw [RingHom.comp_apply, hi, ho.2 a]; push_cast; ring⟩

structure IsEval {W : Type} {Cusp : W → Type} [∀ w, AddCommGroup (Cusp w)] [∀ w, Module K (Cusp w)]
    (wadd : W → W → W) (mulC : ∀ w w', Cusp w → Cusp w' → Cusp (wadd w w')) {F : Type} [Field F]
    (ι : K →+* F) (ev : ∀ w, Cusp w → F) : Prop where
  add : ∀ w f g, ev w (f + g) = ev w f + ev w g
  smul : ∀ w (a : K) f, ev w (a • f) = ι a * ev w f
  mul : ∀ w w' f g, ev (wadd w w') (mulC w w' f g) = ev w f * ev w' g

lemma IsEval.zero {W : Type} {Cusp : W → Type} [∀ w, AddCommGroup (Cusp w)] [∀ w, Module K (Cusp w)]
    {wadd : W → W → W} {mulC : ∀ w w', Cusp w → Cusp w' → Cusp (wadd w w')} {F : Type} [Field F]
    {ι : K →+* F} {ev : ∀ w, Cusp w → F} (h : IsEval wadd mulC ι ev) (w : W) : ev w 0 = 0 := by
  have := h.smul w 0 0
  rwa [zero_smul, map_zero, zero_mul] at this

end Over

section Norm

variable {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K))

lemma finitePlace_eq_zpow {a : K} (ha : a ≠ 0) :
    FinitePlace.mk la a = (Ideal.absNorm la.asIdeal : ℝ) ^ (-(vLa la a)) := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding',
    WithZeroMulInt.toNNReal_neg_apply _ ((la.valuation K).ne_zero_iff.2 ha)]
  simp [vLa, WithZero.toAdd_unzero_eq_log]

def nrmOf (v : EReal) : ℝ :=
  open Classical in if v = ⊤ then 0 else (Ideal.absNorm la.asIdeal : ℝ) ^ (-v.toReal)

lemma one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm la.asIdeal : ℝ) := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm la

lemma nrmOf_smul {a : K} (ha : a ≠ 0) {v : EReal} (hv : v ≠ ⊥) :
    nrmOf la ((((vLa la a : ℤ) : ℝ) : EReal) + v) = FinitePlace.mk la a * nrmOf la v := by
  rw [finitePlace_eq_zpow la ha]
  by_cases ht : v = ⊤
  · subst ht; simp [nrmOf]
  lift v to ℝ using ⟨ht, hv⟩
  simp only [nrmOf, ← EReal.coe_add, EReal.coe_ne_top, if_false, EReal.toReal_coe]
  rw [neg_add, Real.rpow_add (by linarith [one_lt_absNorm_real la]), ← Real.rpow_intCast]
  push_cast; ring_nf

end Norm

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.UnramBridgeHolds
open NumberField Polynomial

namespace Formalism.L2.Pj

attribute [local instance] FractionRing.liftAlgebra

theorem unramBridge_holds : ∀ (K : Type) [Field K] [NumberField K] [IsCMField K],
    (∀ P : Ideal (𝓞 K), P.IsMaximal → ∃ θ : 𝓞 K,
      θ - RingOfIntegers.mapRingEquiv (IsCMField.complexConj K : K ≃+* K) θ ∉ P) →
    Algebra.Unramified (𝓞 (maximalRealSubfield K)) (𝓞 K) := by
  intro K _ _ _ hθ
  set F := maximalRealSubfield K with hF
  have hsep : Algebra.IsSeparable (FractionRing (𝓞 F)) (FractionRing (𝓞 K)) := by
    refine Algebra.IsSeparable.of_equiv_equiv (FractionRing.algEquiv (𝓞 F) F).symm.toRingEquiv
          (FractionRing.algEquiv (𝓞 K) K).symm.toRingEquiv ?_
    ext _
    exact IsFractionRing.algEquiv_commutes (FractionRing.algEquiv (𝓞 F) F).symm
      (FractionRing.algEquiv (𝓞 K) K).symm _
  rw [Algebra.unramified_iff_forall]
  rintro ⟨Q, hQ⟩
  change Algebra.IsUnramifiedAt (𝓞 F) Q
  rcases eq_or_ne Q ⊥ with rfl | hne
  · exact Algebra.isUnramifiedAt_bot
  have hmax : Q.IsMaximal := hQ.isMaximal hne
  obtain ⟨θ, hθP⟩ := hθ Q hmax
  set θ' := RingOfIntegers.mapRingEquiv (IsCMField.complexConj K : K ≃+* K) θ with hθ'
  have hσ : θ' = IsCMField.ringOfIntegersComplexConj K θ := RingOfIntegers.ext rfl
  have hne' : θ - θ' ≠ 0 := fun h => hθP (h ▸ Ideal.zero_mem _)

  have hnotF : (θ : K) ∉ F := by
    intro hm
    apply hne'
    rw [sub_eq_zero, hσ]
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj]
    exact ((IsCMField.complexConj_eq_self_iff K _).mpr hm).symm

  have hfin : Module.finrank F K = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F K
  have hint : IsIntegral F (θ : K) := Algebra.IsIntegral.isIntegral _
  have hadj : Algebra.adjoin F {algebraMap (𝓞 K) K θ} = ⊤ := by
    have : IsSimpleOrder (IntermediateField F K) :=
      IntermediateField.isSimpleOrder_of_finrank_prime F K (hfin ▸ Nat.prime_two)
    rcases eq_bot_or_eq_top (IntermediateField.adjoin F {(θ : K)}) with h | h
    · exfalso
      rw [IntermediateField.adjoin_simple_eq_bot_iff, IntermediateField.mem_bot] at h
      obtain ⟨y, hy⟩ := h
      exact hnotF (hy ▸ y.2)
    · rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
      change (IntermediateField.adjoin F {(θ : K)}).toSubalgebra = ⊤
      rw [h, IntermediateField.top_toSubalgebra]
  have hmem := aeval_derivative_mem_differentIdeal (𝓞 F) F K θ hadj

  set f := minpoly (𝓞 F) θ with hf
  have hθint : IsIntegral (𝓞 F) θ := Algebra.IsIntegral.isIntegral _
  have hmonic : f.Monic := minpoly.monic hθint
  have hdeg : f.natDegree ≤ 2 := by
    have h1 : f = minpoly (𝓞 F) (algebraMap (𝓞 K) K θ) :=
      (minpoly.algebraMap_eq (FaithfulSMul.algebraMap_injective (𝓞 K) K) θ).symm
    have h2 := minpoly.isIntegrallyClosed_eq_field_fractions' F
      (IsIntegral.algebraMap hθint : IsIntegral (𝓞 F) (algebraMap (𝓞 K) K θ))
    have h3 : (minpoly F (algebraMap (𝓞 K) K θ)).natDegree ≤ 2 :=
      hfin ▸ minpoly.natDegree_le _
    rw [h2, Polynomial.natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective _ _)] at h3
    rw [h1]; exact h3
  set fK := f.map (algebraMap (𝓞 F) (𝓞 K)) with hfK
  have hKmonic : fK.Monic := hmonic.map _
  have hKdeg : fK.natDegree ≤ 2 := by
    rw [hfK, hmonic.natDegree_map]; exact hdeg
  have hr1 : fK.IsRoot θ := by
    rw [IsRoot, hfK, eval_map, ← aeval_def]; exact minpoly.aeval _ _
  have hr2 : fK.IsRoot θ' := by
    rw [IsRoot, hfK, eval_map, ← aeval_def, hσ]
    rw [show IsCMField.ringOfIntegersComplexConj K θ = (IsCMField.ringOfIntegersComplexConj K).toAlgHom θ from rfl,
      Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  set g := fK /ₘ (X - C θ) with hg
  have hfg : (X - C θ) * g = fK := (mul_divByMonic_eq_iff_isRoot).mpr hr1
  have hg2 : g.IsRoot θ' := by
    have := hr2
    rw [← hfg, IsRoot, eval_mul] at this
    rcases mul_eq_zero.mp this with h | h
    · exfalso; apply hne'; simp at h; rw [sub_eq_zero] at h ⊢; exact h.symm
    · exact h
  set h := g /ₘ (X - C θ') with hh
  have hgh : (X - C θ') * h = g := (mul_divByMonic_eq_iff_isRoot).mpr hg2
  have hfac : fK = (X - C θ) * ((X - C θ') * h) := by rw [hgh, hfg]
  have hhmonic : h.Monic := by
    have hm2 : ((X - C θ) * (X - C θ')).Monic := (monic_X_sub_C θ).mul (monic_X_sub_C θ')
    rw [hfac, ← mul_assoc] at hKmonic
    exact hm2.of_mul_monic_left hKmonic
  have hh1 : h = 1 := by
    rw [← hhmonic.natDegree_eq_zero]
    have := hKdeg
    rw [hfac, natDegree_mul (X_sub_C_ne_zero θ) (mul_ne_zero (X_sub_C_ne_zero θ') hhmonic.ne_zero),
      natDegree_mul (X_sub_C_ne_zero θ') hhmonic.ne_zero, natDegree_X_sub_C, natDegree_X_sub_C] at this
    omega
  have hval : aeval θ (derivative f) = θ - θ' := by
    rw [aeval_def, ← eval_map, ← derivative_map, ← hfK, hfac, hh1]
    simp [derivative_mul]
  rw [← not_dvd_differentIdeal_iff, Ideal.dvd_iff_le]
  intro hle
  exact hθP (hle (hval ▸ hmem))

end Formalism.L2.Pj
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.RowDeg
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open MvPolynomial

abbrev Letter (T : Type) (r : T → ℕ) (n : ℕ) : Type := Σ σ : T, Fin (r σ) × Fin n

variable {T : Type} (r : T → ℕ) (n : ℕ)

variable (k : Type) [Field k]

def lap (hinv : Matrix (Fin n) (Fin n) k) (τ τ' : T) (a : Fin (r τ)) (a' : Fin (r τ')) :
    MvPolynomial (Letter T r n) k →ₗ[k] MvPolynomial (Letter T r n) k :=
  ∑ b, ∑ b', hinv b b' •
    ((pderiv (⟨τ, a, b⟩ : Letter T r n)).toLinearMap ∘ₗ
      (pderiv (⟨τ', a', b'⟩ : Letter T r n)).toLinearMap)

def harmK (cc : T → T) (isX : T → Prop) (hinv : T → Matrix (Fin n) (Fin n) k) :
    Submodule k (MvPolynomial (Letter T r n) k) :=
  ⨅ (τ : T) (_ : isX τ) (a : Fin (r τ)) (a' : Fin (r (cc τ))),
    LinearMap.ker (lap r n k (hinv τ) τ (cc τ) a a')

def rowShift (σ : T) (i i' : Fin (r σ)) (t : k) :
    MvPolynomial (Letter T r n) k →ₐ[k] MvPolynomial (Letter T r n) k :=
  aeval fun ℓ => open Classical in
    if ∃ b : Fin n, ℓ = ⟨σ, i, b⟩ then X ℓ + C t * X ⟨σ, i', ℓ.2.2⟩ else X ℓ

def RowInv (P : MvPolynomial (Letter T r n) k) : Prop :=
  ∀ (σ : T) (i i' : Fin (r σ)), i' < i → ∀ t : k, rowShift r n k σ i i' t P = P

def RowDeg (a : T → ℕ → ℕ) (P : MvPolynomial (Letter T r n) k) : Prop :=
  ∀ m ∈ P.support, ∀ (σ : T) (i : Fin (r σ)), ∑ b : Fin n, m ⟨σ, i, b⟩ = a σ i

def HHa (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) : Set (MvPolynomial (Letter T r n) k) :=
  {P | P ∈ harmK r n k cc isX (fun _ => 1) ∧ RowInv r n k P ∧ RowDeg r n k a P}

def HaO (O : Subring k) (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ) :
    Set (MvPolynomial (Letter T r n) k) :=
  {P | P ∈ HHa r n k cc isX a ∧ ∀ m, P.coeff m ∈ O}

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
noncomputable section

namespace Formalism.L2.Pj

open MvPolynomial

structure TRing (K : Type) [Field K] : Type where
  n : ℕ
  I : Ideal (MvPolynomial (Fin n) K)
  rad : I.IsRadical

namespace TRing

variable {K : Type} [Field K]

abbrev R (p : TRing K) : Type := MvPolynomial (Fin p.n) K ⧸ p.I

end TRing

section Rules

variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)

abbrev Rules : Type := ∀ p : TRing K, pts p.R → p.R

def wchar [Fintype ι] {S : Type} [CommRing S] (e : ι → ℕ) (t : ι → Sˣ) : S :=
  ∏ i, ((t i : Sˣ) : S) ^ e i

def IsNatural (f : Rules pts) : Prop :=
  ∀ (p q : TRing K) (φ : p.R →ₐ[K] q.R) (y : pts p.R) (z : pts q.R), mapR φ y z → f q z = φ (f p y)

def IsWeight [Fintype ι] (e : ι → ℕ) (f : Rules pts) : Prop :=
  ∀ (p : TRing K) (t : ι → (p.R)ˣ) (y y' : pts p.R), borR t y y' → f p y' = wchar e t * f p y

def secW [Fintype ι] (e : ι → ℕ) : Submodule K (Rules pts) where
  carrier := {f | IsNatural pts mapR f ∧ IsWeight pts borR e f}
  zero_mem' := ⟨fun p q φ y z _ => by simp, fun p t y y' _ => by simp⟩
  add_mem' := fun {f g} hf hg =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h, hg.1 p q φ y z h],
     fun p t y y' h => by simp [hf.2 p t y y' h, hg.2 p t y y' h, mul_add]⟩
  smul_mem' := fun c f hf =>
    ⟨fun p q φ y z h => by simp [hf.1 p q φ y z h],
     fun p t y y' h => by simp [hf.2 p t y y' h]⟩

def FromTest {S : Type} [CommRing S] [Algebra K S] (y : pts S) : Prop :=
  ∃ (p : TRing K) (φ : p.R →ₐ[K] S) (y' : pts p.R), mapR φ y' y

def evalAt (f : Rules pts) {S : Type} [CommRing S] [Algebra K S] (y : pts S) : S :=
  open Classical in
  if h : FromTest pts mapR y then h.choose_spec.choose (f h.choose h.choose_spec.choose_spec.choose)
  else 0

theorem evalAt_add (f g : Rules pts) {S : Type} [CommRing S] [Algebra K S] (y : pts S) :
    evalAt pts mapR (f + g) y = evalAt pts mapR f y + evalAt pts mapR g y := by
  unfold evalAt; split_ifs <;> simp

theorem evalAt_smul (c : K) (f : Rules pts) {S : Type} [CommRing S] [Algebra K S] (y : pts S) :
    evalAt pts mapR (c • f) y = algebraMap K S c * evalAt pts mapR f y := by
  unfold evalAt; split_ifs <;> simp [Algebra.smul_def]

theorem evalAt_zero {S : Type} [CommRing S] [Algebra K S] (y : pts S) :
    evalAt pts mapR (0 : Rules pts) y = 0 := by
  unfold evalAt; split_ifs <;> simp

theorem evalAt_mul (f g : Rules pts) {S : Type} [CommRing S] [Algebra K S] (y : pts S) :
    evalAt pts mapR (f * g) y = evalAt pts mapR f y * evalAt pts mapR g y := by
  unfold evalAt; split_ifs <;> simp

theorem evalAt_one {S : Type} [CommRing S] [Algebra K S] (y : pts S) (h : FromTest pts mapR y) :
    evalAt pts mapR (1 : Rules pts) y = 1 := by
  unfold evalAt; rw [dite_eq_left h]; simp

def evalL {S : Type} [CommRing S] [Algebra K S] (y : pts S) : Rules pts →ₗ[K] S where
  toFun f := evalAt pts mapR f y
  map_add' f g := evalAt_add pts mapR f g y
  map_smul' c f := by rw [RingHom.id_apply, evalAt_smul, Algebra.smul_def]

def EvalWD : Prop :=
  ∀ (f : Rules pts), IsNatural pts mapR f →
    ∀ (S : Type) [CommRing S] [Algebra K S] (p q : TRing K) (φ : p.R →ₐ[K] S) (ψ : q.R →ₐ[K] S)
      (y : pts p.R) (z : pts q.R) (w : pts S), mapR φ y w → mapR ψ z w → φ (f p y) = ψ (f q z)

end Rules

section Complex

variable {K : Type} [Field K]

def CAt (_σ : K →+* ℂ) : Type := ℂ

instance (σ : K →+* ℂ) : CommRing (CAt σ) := inferInstanceAs (CommRing ℂ)
instance (σ : K →+* ℂ) : Algebra K (CAt σ) := σ.toAlgebra

def cabs {σ : K →+* ℂ} (z : CAt σ) : ℝ := ‖(show ℂ from z)‖

variable {ι : Type} [Fintype ι]
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)

def ptNorm (σ : K →+* ℂ) (fnorm : pts (CAt σ) → ι → ℝ) (e : ι → ℕ) (f : Rules pts)
    (y : pts (CAt σ)) : ℝ :=
  cabs (evalAt pts mapR f y) * ∏ i, |fnorm y i|⁻¹ ^ e i

theorem ptNorm_nonneg (σ : K →+* ℂ) (fnorm : pts (CAt σ) → ι → ℝ) (e : ι → ℕ) (f : Rules pts)
    (y : pts (CAt σ)) : 0 ≤ ptNorm pts mapR σ fnorm e f y :=
  mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => pow_nonneg (inv_nonneg.2 (abs_nonneg _)) _)

theorem ptNorm_zero (σ : K →+* ℂ) (fnorm : pts (CAt σ) → ι → ℝ) (e : ι → ℕ) (y : pts (CAt σ)) :
    ptNorm pts mapR σ fnorm e 0 y = 0 := by
  unfold ptNorm; rw [evalAt_zero]
  exact mul_eq_zero_of_left (norm_zero (E := ℂ)) _

def supAt (σ : K →+* ℂ) (fnorm : pts (CAt σ) → ι → ℝ) (e : ι → ℕ) (f : Rules pts) : ℝ :=
  ⨆ y : pts (CAt σ), ptNorm pts mapR σ fnorm e f y

def BddAt (σ : K →+* ℂ) (fnorm : pts (CAt σ) → ι → ℝ) (e : ι → ℕ) (f : Rules pts) : Prop :=
  BddAbove (Set.range (ptNorm pts mapR σ fnorm e f))

end Complex

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj

open MvPolynomial

variable (R : Type) [CommRing R] (ι : Type) (m : ℕ)

def orig : Ideal (MvPolynomial ι R) := Ideal.span (Set.range X)

abbrev Jet : Type := MvPolynomial ι R ⧸ orig R ι ^ (m + 1)

variable {R ι m}

theorem map_orig_pow {B : Type} [CommRing B] (f : MvPolynomial ι R →+* B) (k : ℕ) :
    Ideal.map f (orig R ι ^ k) = Ideal.span (Set.range fun i => f (X i)) ^ k := by
  rw [orig, Ideal.map_pow, Ideal.map_span, ← Set.range_comp]
  rfl

def liftJet {B : Type} [CommRing B] [Algebra R B] (f : MvPolynomial ι R →ₐ[R] B)
    (h : Ideal.span (Set.range fun i => f (X i)) ^ (m + 1) = ⊥) : Jet R ι m →ₐ[R] B :=
  Ideal.Quotient.liftₐ _ f fun a ha => by
    have : f a ∈ Ideal.map (f : MvPolynomial ι R →+* B) (orig R ι ^ (m + 1)) :=
      Ideal.mem_map_of_mem _ ha
    have h' : Ideal.span (Set.range fun i => (f : MvPolynomial ι R →+* B) (X i)) ^ (m + 1) = ⊥ := h
    rw [map_orig_pow, h'] at this
    exact (Submodule.mem_bot _).1 this

def jetMap {ι' : Type} (φ : ι → MvPolynomial ι' R) (hφ : ∀ i, φ i ∈ orig R ι') :
    Jet R ι m →ₐ[R] Jet R ι' m :=
  liftJet ((Ideal.Quotient.mkₐ R (orig R ι' ^ (m + 1))).comp (aeval φ)) (by
    apply le_bot_iff.1
    have h1 : Ideal.span (Set.range fun i =>
        ((Ideal.Quotient.mkₐ R (orig R ι' ^ (m + 1))).comp (aeval φ)) (X i)) =
        Ideal.map (Ideal.Quotient.mk (orig R ι' ^ (m + 1))) (Ideal.span (Set.range φ)) := by
      rw [Ideal.map_span, ← Set.range_comp]
      congr 1
      ext x
      simp
    rw [h1, ← Ideal.map_pow]
    have h2 : Ideal.span (Set.range φ) ^ (m + 1) ≤ orig R ι' ^ (m + 1) :=
      Ideal.pow_right_mono (Ideal.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hφ i)) _
    refine (Ideal.map_mono h2).trans ?_
    rw [Ideal.map_quotient_self])

theorem X_mem_orig {ι' : Type} (i : ι') : (X i : MvPolynomial ι' R) ∈ orig R ι' :=
  Ideal.subset_span ⟨i, rfl⟩

def jetIn {K : Type} (k : K) : Jet R ι m →ₐ[R] Jet R (K × ι) m :=
  jetMap (fun i => X (k, i)) fun i => X_mem_orig (k, i)

def jetScale (c : ι → R) : Jet R ι m →ₐ[R] Jet R ι m :=
  jetMap (fun i => C (c i) * X i) fun i => Ideal.mul_mem_left _ _ (X_mem_orig i)

def jetAug : Jet R ι m →ₐ[R] R :=
  liftJet (aeval fun _ => (0 : R)) (by
    have : Ideal.span (Set.range fun i => (aeval fun _ => (0 : R)) (X i : MvPolynomial ι R)) = ⊥ := by
      rw [Ideal.span_eq_bot]
      rintro _ ⟨i, rfl⟩
      simp
    rw [this, Ideal.bot_pow (Nat.succ_ne_zero m)])

def jetTan [DecidableEq ι] (ℓ : ι) : Jet R ι (m + 1) →ₐ[R] DualNumber R :=
  liftJet (aeval fun i => if i = ℓ then (DualNumber.eps : DualNumber R) else 0) (by
    apply le_bot_iff.1
    have h1 : Ideal.span (Set.range fun i =>
        (aeval fun i => if i = ℓ then (DualNumber.eps : DualNumber R) else 0) (X i : MvPolynomial ι R))
        ≤ Ideal.span {(DualNumber.eps : DualNumber R)} := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      by_cases h : i = ℓ
      · simp [h]
      · simp [h]
    refine (Ideal.pow_right_mono h1 _).trans ?_
    refine (Ideal.pow_le_pow_right (show 2 ≤ m + 1 + 1 by omega)).trans ?_
    rw [Ideal.span_singleton_pow]
    simp)

theorem sub_const_mem_orig (P : MvPolynomial ι R) :
    P - C (MvPolynomial.constantCoeff P) ∈ orig R ι := by
  induction P using MvPolynomial.induction_on
  next a =>
    simp
  next p q hp hq =>
    have h : p + q - C (MvPolynomial.constantCoeff (p + q)) =
        (p - C (MvPolynomial.constantCoeff p)) + (q - C (MvPolynomial.constantCoeff q)) := by
      simp only [map_add (f := _)]
      ring
    rw [h]
    exact Ideal.add_mem _ hp hq
  next p n _ =>
    simp only [map_mul, constantCoeff_X, mul_zero, map_zero, sub_zero]
    exact Ideal.mul_mem_left _ _ (X_mem_orig n)

def degLE [Fintype ι] [DecidableEq ι] (m : ℕ) : Finset (ι →₀ ℕ) :=
  ((Finset.univ : Finset (ι → Fin (m + 1))).image fun v =>
    Finsupp.equivFunOnFinite.symm fun i => (v i : ℕ)).filter fun e => (e.sum fun _ k => k) ≤ m

def psTrunc [Fintype ι] [DecidableEq ι] (m : ℕ) (f : MvPowerSeries ι R) : MvPolynomial ι R :=
  ∑ e ∈ degLE m, monomial e (MvPowerSeries.coeff e f)

def psJet [Fintype ι] [DecidableEq ι] (m : ℕ) (f : MvPowerSeries ι R) : Jet R ι m :=
  Ideal.Quotient.mk _ (psTrunc m f)

def jetSubstPS {ι' : Type} [Fintype ι'] [DecidableEq ι'] (φ : ι → MvPowerSeries ι' R) : Jet R ι m →ₐ[R] Jet R ι' m :=
  jetMap (fun i => psTrunc m (φ i) - C (MvPolynomial.constantCoeff (psTrunc m (φ i))))
    fun i => sub_const_mem_orig _

def jetTrunc : Jet R ι (m + 1) →ₐ[R] Jet R ι m :=
  Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right (by omega))

end Formalism.L2.Pj
end
end

section -- merged from Formalism.LocalToGlobal.ProjectiveLattices.ExistsOfValILeOne
noncomputable section

namespace Formalism.L2.Pj

open Matrix IsDedekindDomain

variable {V F : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F] [Algebra V F]
  [IsFractionRing V F]


variable (V) in
abbrev valI : Valuation F (WithZero (Multiplicative ℤ)) := (IsDiscreteValuationRing.maximalIdeal V).valuation F

theorem exists_of_valI_le_one {x : F} (h : valI (V := V) x ≤ 1) : ∃ a : V, algebraMap V F a = x := by
  have hall : ∀ w : IsDedekindDomain.HeightOneSpectrum V, w = IsDiscreteValuationRing.maximalIdeal V := by
    intro w
    first
    | exact IsDedekindDomain.HeightOneSpectrum.ext (IsLocalRing.eq_maximalIdeal w.isMaximal)
    | (ext1; exact IsLocalRing.eq_maximalIdeal w.isMaximal)
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one F x
    (fun w => by rw [hall w]; exact h)
  exact ⟨a, ha⟩

theorem exists_clear_col {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F) (hA : A.det ≠ 0) :
    ∃ Q : Matrix (Fin (n + 1)) (Fin (n + 1)) V, IsUnit Q.det ∧
      ∀ i : Fin n, (Q.map (algebraMap V F) * A) i.succ 0 = 0 := by
  obtain ⟨p, -, hp⟩ := Finset.exists_max_image Finset.univ
    (fun r => valI (V := V) (A r 0)) Finset.univ_nonempty
  have hcol : ∃ r, A r 0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hA (Matrix.det_eq_zero_of_column_eq_zero 0 h)
  have hp0 : A p 0 ≠ 0 := by
    obtain ⟨r, hr⟩ := hcol
    intro h0
    have := hp r (Finset.mem_univ _)
    rw [h0, map_zero] at this
    exact hr ((valI (V := V)).zero_iff.1 (le_antisymm this zero_le))
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 p
  let P : Matrix (Fin (n + 1)) (Fin (n + 1)) V := σ.permMatrix V
  have hc : ∀ i, ∃ a : V, algebraMap V F a = A (σ i) 0 / A p 0 := by
    intro i
    apply exists_of_valI_le_one
    rw [map_div₀]
    have hpos : valI (V := V) (A p 0) ≠ 0 := by simpa using hp0
    rw [div_le_one₀ (zero_lt_iff.2 hpos)]
    exact hp _ (Finset.mem_univ _)
  choose c hc using hc
  let E : Matrix (Fin (n + 1)) (Fin (n + 1)) V := Matrix.of fun i j =>
    if i = j then 1 else if j = 0 then -c i else 0
  refine ⟨E * P, ?_, ?_⟩
  · rw [Matrix.det_mul]
    refine IsUnit.mul ?_ ?_
    · have hE : E.det = 1 := by
        rw [Matrix.det_of_isLowerTriangular E]
        · simp [E]
        · intro i j hij
          have hij' : i < j := hij
          have hj : j ≠ 0 := fun h => by subst h; exact Fin.not_lt_zero _ hij'
          simp only [E, Matrix.of_apply, if_neg (ne_of_lt hij'), if_neg hj]
      rw [hE]; exact isUnit_one
    · simp only [P, Matrix.det_permutation]
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  · intro i
    rw [Matrix.map_mul, Matrix.mul_assoc, Matrix.mul_apply, Fin.sum_univ_succ]
    have hPA : ∀ r, (P.map (algebraMap V F) * A) r 0 = A (σ r) 0 := by
      intro r
      simp [P, Equiv.Perm.permMatrix, Matrix.mul_apply, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    simp only [hPA, Matrix.map_apply, E, Matrix.of_apply]
    rw [if_neg (Fin.succ_ne_zero i)]
    simp only [if_true, Fin.succ_ne_zero, map_neg, map_one, map_zero, zero_mul]
    rw [Finset.sum_eq_single i]
    · simp only [if_true, map_one, one_mul]
      rw [hc]
      have : σ 0 = p := by simp [σ]
      rw [this]
      field_simp
      ring
    · intro j _ hji
      rw [if_neg (fun h => hji (Fin.succ_injective _ h).symm)]
      simp
    · intro h; exact absurd (Finset.mem_univ i) h

theorem iwasawa : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) F), A.det ≠ 0 →
    ∃ (k : Matrix (Fin n) (Fin n) V) (U : Matrix (Fin n) (Fin n) F), IsUnit k.det ∧ U.BlockTriangular id ∧
      (∀ i, U i i ≠ 0) ∧ A = k.map (algebraMap V F) * U := by
  intro n
  induction n with
  | zero =>
    intro A _
    exact ⟨1, A, by simp, fun i => i.elim0, fun i => i.elim0, by ext i; exact i.elim0⟩
  | succ n ih =>
    intro A hA
    obtain ⟨Q, hQ, hQA⟩ := exists_clear_col (V := V) (n := n) A hA
    set B := Q.map (algebraMap V F) * A with hB
    have hdetB : B.det = B 0 0 * (B.submatrix Fin.succ Fin.succ).det := by
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      simp [hQA, B]
    have hQF : (Q.map (algebraMap V F)).det = algebraMap V F Q.det := by
      rw [RingHom.map_det]; rfl
    have hBne : B.det ≠ 0 := by
      rw [hB, Matrix.det_mul, hQF]
      exact mul_ne_zero (hQ.map (algebraMap V F)).ne_zero hA
    have hB00 : B 0 0 ≠ 0 := by intro h; apply hBne; rw [hdetB, h, zero_mul]
    obtain ⟨k', U', hk', hU', hd', hA'⟩ := ih (B.submatrix Fin.succ Fin.succ) (by
      intro h; apply hBne; rw [hdetB, h, mul_zero])
    let K : Matrix (Fin (n + 1)) (Fin (n + 1)) V := Matrix.of fun i j =>
      Fin.cases (Fin.cases 1 (fun _ => 0) j) (fun i' => Fin.cases 0 (fun j' => k' i' j') j) i
    let U : Matrix (Fin (n + 1)) (Fin (n + 1)) F := Matrix.of fun i j =>
      Fin.cases (B 0 j) (fun i' => Fin.cases 0 (fun j' => U' i' j') j) i
    have hKU : K.map (algebraMap V F) * U = B := by
      ext i j
      refine Fin.cases ?_ (fun i' => ?_) i
      · simp [K, U, Matrix.mul_apply, Fin.sum_univ_succ]
      · refine Fin.cases ?_ (fun j' => ?_) j
        · simp [K, U, Matrix.mul_apply, Fin.sum_univ_succ, hQA]
        · have h1 := congrFun (congrFun hA' i') j'
          simp only [Matrix.submatrix_apply] at h1
          rw [h1]
          simp [K, U, Matrix.mul_apply, Fin.sum_univ_succ]
    have hKdet : K.det = k'.det := by
      rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
      simp [K]
      rfl
    refine ⟨Q⁻¹ * K, U, ?_, ?_, ?_, ?_⟩
    · rw [Matrix.det_mul, hKdet]
      exact (Matrix.isUnit_nonsing_inv_det Q hQ).mul hk'
    · intro i j hij
      induction i using Fin.cases with
      | zero => exact absurd hij (Fin.not_lt_zero _)
      | succ i' =>
        induction j using Fin.cases with
        | zero => simp [U]
        | succ j' =>
          have : j' < i' := Fin.succ_lt_succ_iff.1 hij
          simpa [U] using hU' this
    · intro i
      induction i using Fin.cases with
      | zero => simpa [U] using hB00
      | succ i' => simpa [U] using hd' i'
    · rw [Matrix.map_mul, Matrix.mul_assoc, hKU, hB, ← Matrix.mul_assoc, ← Matrix.map_mul,
        Matrix.nonsing_inv_mul Q hQ, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

theorem upper_inv {m : ℕ} (U : Matrix (Fin m) (Fin m) F) (hU : U.BlockTriangular id) (hd : ∀ i, U i i ≠ 0) :
    U⁻¹.BlockTriangular id ∧ (∀ i, U⁻¹ i i ≠ 0) ∧ U * U⁻¹ = 1 := by
  have hdet : U.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular hU]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => hd i
  have hu : IsUnit U.det := isUnit_iff_ne_zero.mpr hdet
  letI := Matrix.invertibleOfIsUnitDet U hu
  have hinv : U⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hU
  refine ⟨hinv, fun i => ?_, Matrix.mul_nonsing_inv U hu⟩
  have h1 : (U⁻¹ * U) i i = 1 := by rw [Matrix.nonsing_inv_mul U hu, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
  · intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  · intro k _ hki
    rcases lt_or_gt_of_ne hki with hlt | hgt
    · rw [hinv hlt, zero_mul]
    · rw [hU hgt, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

theorem iwasawa' {n : ℕ} (A : Matrix (Fin n) (Fin n) F) (hA : A.det ≠ 0) :
    ∃ (k : Matrix (Fin n) (Fin n) V) (N : Matrix (Fin n) (Fin n) F), IsUnit k.det ∧ N.BlockTriangular id ∧
      (∀ i, N i i ≠ 0) ∧ A * N = k.map (algebraMap V F) := by
  obtain ⟨k, U, hk, hU, hd, hA⟩ := iwasawa (V := V) A hA
  obtain ⟨hinv, hdinv, hUU⟩ := upper_inv U hU hd
  refine ⟨k, U⁻¹, hk, hinv, hdinv, ?_⟩
  rw [hA, Matrix.mul_assoc, hUU, Matrix.mul_one]

end Formalism.L2.Pj
end
end
