module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralTensorAdelesEqAdelicCompletionOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsPowEqSpanNormOne
section -- merged from Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.LatticeFramesPrimeToLevel
noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host Neutral.B1
open scoped Matrix

section Adelic

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

abbrev Ad : Type := FiniteAdeleRing (𝓞 H.E) H.E

end Adelic

section abelian₂

variable {l : ℕ} [Fact l.Prime] (lam : (algebraicClosure ℚ ℂ) →+* ℂ_[l])

end abelian₂

abbrev Reps (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) : Type :=
  ∀ i, (D.chTw u μ).cls i → GL (Fin (D.R.N i)) (Ad D.host)

abbrev Frames (D : D7) (u : D.what₂.Word) (μ : D.what₂.Tup) : Type :=
  ∀ i, (D.chTw u μ).Y i → D.what₂.Tau → Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) ℂ

end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRationalFrame
noncomputable section

namespace GlobalTheory.UnUnitCmp

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts

section Units

variable {l : ℕ} [Fact l.Prime] {lam : (algebraicClosure ℚ ℂ) →+* ℂ_[l]}

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem emb_mem {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (x : K) : φ x ∈ algebraicClosure ℚ ℂ :=
  mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom φ.toRatAlgHom)

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) (φ : H.E →+* ℂ) {N : ℕ} (g : GL (Fin N) (Ad H))

end Units

section Rescale

variable {D : D7} {Dx : DivX D} {Tw : TwForms D}

end Rescale

section Ties

variable {D : D7} {Dx : DivX D} {Tw : TwForms D} {C : CharFrame D} {nch : NChoice D}

variable (E : KerEnt D Dx Tw) (Tp : TupTied D C nch) (g : ∀ u μ, Reps D u μ) (fr : ∀ u μ, Frames D u μ)

end Ties

end GlobalTheory.UnUnitCmp
end
end

noncomputable section

namespace GlobalTheory.KernelScalarUnit

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointHilbertLifts GlobalTheory.UnUnitCmp
open scoped nonZeroDivisors

section Ideals

variable {K : Type} [Field K] [NumberField K]

theorem exists_pow_eq_span {𝔞 𝔟 : Submodule (𝓞 K) K} (h : 𝔞 * 𝔟 = 1) :
    ∃ (n : ℕ) (a : K), 0 < n ∧ 𝔞 ^ n = Submodule.span (𝓞 K) {a} := by
  have hu : IsUnit 𝔞 := IsUnit.of_mul_eq_one 𝔟 h
  have hv : IsUnit 𝔟 := IsUnit.of_mul_eq_one 𝔞 (by rw [mul_comm]; exact h)
  let I : FractionalIdeal (𝓞 K)⁰ K := ⟨𝔞, FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit hu)⟩
  let J : FractionalIdeal (𝓞 K)⁰ K := ⟨𝔟, FractionalIdeal.isFractional_of_fg (Submodule.fg_of_isUnit hv)⟩
  have hIJ : I * J = 1 := by
    apply FractionalIdeal.coeToSubmodule_injective
    simp only [FractionalIdeal.coe_mul, FractionalIdeal.coe_one]
    exact h
  let U : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mkOfMulEqOne I J hIJ
  have h1 : ClassGroup.mk K (U ^ Fintype.card (ClassGroup (𝓞 K))) = 1 := by rw [map_pow, pow_card_eq_one]
  obtain ⟨a, ha⟩ := ClassGroup.mk_eq_one_iff.1 h1
  refine ⟨_, a, Fintype.card_pos (α := ClassGroup (𝓞 K)), ?_⟩
  rw [← ha, Units.val_pow_eq_pow_val, FractionalIdeal.coe_pow]
  rfl

omit [NumberField K] in
theorem map_mem_one (c : K →+* K) {x : K} (hx : x ∈ (1 : Submodule (𝓞 K) K)) : c x ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨r, rfl⟩ := Submodule.mem_one.1 hx
  exact Submodule.mem_one.2 ⟨⟨c r, map_isIntegral_int c r.isIntegral_coe⟩, rfl⟩

omit [NumberField K] in
theorem map_mem_pow (c : K →+* K) {𝔞 𝔟 : Submodule (𝓞 K) K} (h : ∀ x ∈ 𝔞, c x ∈ 𝔟) :
    ∀ (n : ℕ), ∀ x ∈ 𝔞 ^ n, c x ∈ 𝔟 ^ n
  | 0, x, hx => by rw [pow_zero] at *; exact map_mem_one c hx
  | n + 1, x, hx => by
    rw [pow_succ] at hx ⊢
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [map_mul c]
      exact Submodule.mul_mem_mul (map_mem_pow c h n a ha) (h b hb)
    · rw [map_add c]
      exact add_mem ha hb

theorem exists_pow_eq_span_normOne (c : K →+* K) (hc : ∀ x, c (c x) = x) {𝔞 𝔟 : Submodule (𝓞 K) K}
    (hb : ∀ x, x ∈ 𝔟 ↔ c x ∈ 𝔞) (h : 𝔞 * 𝔟 = 1) :
    ∃ (n : ℕ) (z : K), 0 < n ∧ c z * z = 1 ∧ 𝔞 ^ n = Submodule.span (𝓞 K) {z} := by
  obtain ⟨n, a, hn, ha⟩ := exists_pow_eq_span h
  have hb' : 𝔟 ^ n = Submodule.span (𝓞 K) {c a} := by
    apply le_antisymm
    · intro y hy
      have h1 := map_mem_pow c (fun x hx => (hb x).1 hx) n y hy
      rw [ha, Submodule.mem_span_singleton] at h1
      obtain ⟨r, hr⟩ := h1
      refine Submodule.mem_span_singleton.2 ⟨⟨c r, map_isIntegral_int c r.isIntegral_coe⟩, ?_⟩
      rw [← hc y, ← hr, Algebra.smul_def r, map_mul]
      rfl
    · rw [Submodule.span_singleton_le_iff_mem]
      exact map_mem_pow c (fun x hx => (hb _).2 (by rwa [hc])) n a (ha ▸ Submodule.mem_span_singleton_self a)
  have h2 : Submodule.span (𝓞 K) {a * c a} = 1 := by
    rw [← Set.singleton_mul_singleton, ← Submodule.span_mul_span, ← ha, ← hb', ← mul_pow, h, one_pow]
  have h0 : a * c a ≠ 0 := fun h0 => by
    rw [h0, Submodule.span_singleton_eq_bot.2 rfl] at h2
    have : (1 : K) ∈ (⊥ : Submodule (𝓞 K) K) := h2 ▸ Submodule.mem_one.2 ⟨1, map_one _⟩
    simp at this
  have a0 : a ≠ 0 := left_ne_zero_of_mul h0
  have c0 : c a ≠ 0 := right_ne_zero_of_mul h0
  refine ⟨n + n, a / c a, by omega, ?_, ?_⟩
  · rw [map_div₀, hc]; field_simp
  · rw [pow_add, ha, Submodule.span_mul_span, Set.singleton_mul_singleton, ← mul_one (Submodule.span (𝓞 K) {a / c a}), ← h2,
      Submodule.span_mul_span, Set.singleton_mul_singleton]
    congr 2
    field_simp

end Ideals

theorem normOne_pow (D : D7) : NormOnePowerPrincipal D := by
  let := D.host.cmStar
  have hs : ∀ x : D.host.E, star x = D.host.conj x := bridge_star_holds D.R D.host
  rintro 𝔞 ⟨𝔟, hb, h⟩
  obtain ⟨n, z, hn, hz, e⟩ := exists_pow_eq_span_normOne (D.host.conj : D.host.E →+* D.host.E)
    (fun x => by change D.host.conj (D.host.conj x) = x; rw [← hs, ← hs, star_star]) hb h
  have hz' : star z * z = 1 := by rw [hs]; exact hz
  exact ⟨n, ⟨z, hz', by rw [mul_comm]; exact hz'⟩, hn, e⟩

section Local

variable {K : Type} [Field K] [NumberField K] {C : Type} [NormedField C] [IsUltrametricDist C] (ψ : K →+* C)

omit [NumberField K] in
theorem norm_int_le (a : 𝓞 K) : ‖ψ (a : K)‖ ≤ 1 := norm_le_one_of_isIntegral (map_isIntegral_int ψ a.isIntegral_coe)

def ball (r : ℝ) (hr : 0 ≤ r) : Submodule (𝓞 K) K where
  carrier := {x | ‖ψ x‖ ≤ r}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, map_add (f := _)] at *
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  zero_mem' := by simpa using hr
  smul_mem' := fun c a ha => by
    simp only [Set.mem_ofPred_eq, Algebra.smul_def, map_mul, norm_mul] at *
    exact (mul_le_of_le_one_left (norm_nonneg _) (norm_int_le ψ c)).trans ha

end Local

section Det

variable (D : D7) {l : ℕ} [Fact l.Prime] (ψ : D.host.E →+* ℂ_[l]) {N : ℕ}
  {L₀ L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {P : Matrix (Fin N) (Fin N) D.host.E}

end Det

section Power

variable (D : D7) {l : ℕ} [Fact l.Prime] (lam : Qbar →+* ℂ_[l])

def lamTau (τ : D.what₂.Tau) : D.host.E →+* ℂ_[l] :=
  lam.comp ((embT D τ).codRestrict Qbar (emb_mem (embT D τ)))

theorem tauEmb_eq (τ : D.what₂.Tau) : tauEmb D lam τ = lamTau D lam τ := by
  funext x
  unfold tauEmb lamC
  rw [dite_eq_left (emb_mem (embT D τ) x)]
  rfl

end Power

section Main

variable {D : D7} {Dx : DivX D} {Tw : TwForms D}

variable (E : KerEnt D Dx Tw) (O : ∀ u μ, LiftObj D (D.chTw u μ))

end Main

end GlobalTheory.KernelScalarUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialOfSplitPlaceStabilizer
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialOfSplitPlaceStabilizer
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitStab

section Alg

variable {A : Type} [CommRing A] {n : ℕ} (σ : A →+* A) (J : Matrix (Fin n) (Fin n) A)

theorem hform_eq (x y : Fin n → A) :
    Formalism.UG.hform σ J x y = dotProduct (fun i => σ (x i)) (J.mulVec y) := by
  simp only [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_smul_left (a : A) (x y : Fin n → A) :
    Formalism.UG.hform σ J (fun i => a * x i) y = σ a * Formalism.UG.hform σ J x y := by
  simp only [hform_eq, dotProduct, map_mul, Finset.mul_sum, mul_assoc]

theorem hform_smul_right (a : A) (x y : Fin n → A) :
    Formalism.UG.hform σ J x (fun i => a * y i) = a * Formalism.UG.hform σ J x y := by
  have : (fun i => a * y i) = a • y := rfl
  rw [hform_eq, hform_eq, this, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hform_mulVec {g : Matrix (Fin n) (Fin n) A} (hg : Formalism.UG.cT σ g * J * g = J) (x y : Fin n → A) :
    Formalism.UG.hform σ J (g.mulVec x) (g.mulVec y) = Formalism.UG.hform σ J x y := by
  have e : (fun i => σ (g.mulVec x i)) = Matrix.vecMul (fun i => σ (x i)) (Formalism.UG.cT σ g) := by
    funext i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul, Formalism.UG.cT, Matrix.transpose_apply,
      Matrix.map_apply, mul_comm]
  rw [hform_eq, hform_eq, e, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

theorem stab_of_half (I : AddSubgroup A) (L : AddSubgroup (Fin n → A))
    (hL : ∀ y, y ∈ L ↔ ∀ z ∈ L, Formalism.UG.hform σ J z y ∈ I) {p : A}
    (hp : ∀ y ∈ L, (fun i => p * y i) ∈ L) (hq : ∀ y ∈ L, (fun i => σ p * y i) ∈ L)
    {g : Matrix (Fin n) (Fin n) A} (hg : Formalism.UG.cT σ g * J * g = J)
    (hs : ∀ i j, (p + σ p) * (g - 1) i j = (g - 1) i j)
    (h1 : ∀ y ∈ L, (fun i => p * g.mulVec y i) ∈ L)
    (h2 : ∀ y ∈ L, ∃ z ∈ L, (fun i => p * y i) = fun i => p * g.mulVec z i) (y : Fin n → A) :
    y ∈ L ↔ g.mulVec y ∈ L := by
  have fwd : ∀ y ∈ L, g.mulVec y ∈ L := by
    intro y hy
    have hc : (fun i => σ p * g.mulVec y i) ∈ L := by
      refine (hL _).2 fun z hz => ?_
      obtain ⟨z', hz', e⟩ := h2 z hz
      rw [hform_smul_right, ← hform_smul_left, e, hform_smul_left, hform_mulVec σ J hg, ← hform_smul_right]
      exact (hL _).1 (hq y hy) z' hz'
    have hs' : (p + σ p) • (g - 1) = g - 1 := Matrix.ext hs
    have e : (p + σ p) • (g.mulVec y - y) = g.mulVec y - y := by
      have := congrArg (fun m => Matrix.mulVec m y) hs'
      simpa only [Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec] using this
    have e2 : g.mulVec y = y + ((fun i => p * g.mulVec y i) + (fun i => σ p * g.mulVec y i) -
        (fun i => p * y i) - fun i => σ p * y i) := by
      funext i
      have := congrFun e i
      simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul] at this ⊢
      linear_combination -this
    rw [e2]
    exact add_mem hy (sub_mem (sub_mem (add_mem (h1 y hy) hc) (hp y hy)) (hq y hy))
  refine ⟨fwd y, fun hy => (hL _).2 fun z hz => ?_⟩
  rw [← hform_mulVec σ J hg]
  exact (hL _).1 hy _ (fwd z hz)

theorem supp_map {B : Type} [CommRing B] (φ : A →+* B) {f : A} {g : Matrix (Fin n) (Fin n) A}
    (hs : ∀ i j, f * (g - 1) i j = (g - 1) i j) (i j : Fin n) :
    φ f * (g.map φ - 1) i j = (g.map φ - 1) i j := by
  have e : (g.map φ - 1) i j = φ ((g - 1) i j) := by
    rw [Matrix.sub_apply, Matrix.sub_apply, map_sub, Matrix.map_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e, ← map_mul, hs]

end Alg

variable {D : D7}

theorem finPart_conj (x : Formalism.L2.Theta.AE D) :
    finPart D (cA D x) = sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul a e => rfl
  | add x y hx hy => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hx, hy]

theorem finMat_unitary (V : HSp D) (g : GA D V) :
    Formalism.UG.cT (sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig) (finMat D.sp.cm.sig V.gram g) *
      JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) V.gram * finMat D.sp.cm.sig V.gram g =
      JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) V.gram := by
  have h : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mt V g) * JR (AF D.host.F) V.gram * mt V g =
      JR (AF D.host.F) V.gram := g.2
  have h2 := congrArg (fun m => Matrix.map m (finPart D)) h
  simp only [Matrix.map_mul] at h2
  have e1 : (JR (AF D.host.F) V.gram).map (finPart D) = JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) V.gram := rfl
  have e2 : (mt V g).map (finPart D) = finMat D.sp.cm.sig V.gram g := rfl
  have e3 : (Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (mt V g)).map (finPart D) =
      Formalism.UG.cT (sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig) (finMat D.sp.cm.sig V.gram g) := by
    ext i j
    exact finPart_conj _
  rwa [e1, e2, e3] at h2

theorem mem_ksph_of_split : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (g : GA D V), IsSplitIdem D e → Formalism.L2.Theta.SuppAt e V g → (∀ y ∈ LamHat V, (fun a => finPart D e * (finMat D.sp.cm.sig V.gram g).mulVec y a) ∈ LamHat V) → (∀ y ∈ LamHat V, ∃ z ∈ LamHat V, (fun a => finPart D e * y a) = fun a => finPart D e * (finMat D.sp.cm.sig V.gram g).mulVec z a) → g ∈ KsphC V ∅ := by
  intro D V e g he hs h1 h2
  obtain ⟨hd, hm⟩ := GlobalTheory.LatDual.lamHat_selfDual_and_module V
  obtain ⟨i1, -, v, ε, ⟨α, rfl, -⟩, h4⟩ := he
  have hp : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, i1])
  have hq : sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig (finPart D e) ∈ intAE D :=
    GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ← RingHom.map_mul, i1])
  refine ⟨?_, ?_, fun v hv => absurd hv (Finset.notMem_empty v)⟩
  · have h5 : infPart D (e + cA D e) = 0 := by
      rw [h4]
      exact TensorProduct.zero_tmul _ _
    refine Units.ext (Matrix.ext fun i j => ?_)
    have h6 := congrArg (infPart D) (hs i j)
    rw [RingHom.map_mul, h5, zero_mul, Matrix.sub_apply, RingHom.map_sub] at h6
    have h7 : infPart D (mt V g i j) = infPart D ((1 : Matrix _ _ (Formalism.L2.Theta.AE D)) i j) :=
      sub_eq_zero.1 h6.symm
    refine h7.trans ?_
    rw [Units.val_one, Matrix.one_apply, Matrix.one_apply]
    split_ifs
    · exact RingHom.map_one _
    · exact RingHom.map_zero _
  · refine stab_of_half (sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.sp.cm.sig)
      (JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) V.gram) (intAE D) (LamHat V) hd (p := finPart D e)
      (hm _ hp) (hm _ hq) (finMat_unitary V g) (fun i j => ?_) h1 h2
    rw [← finPart_conj, ← RingHom.map_add (f := _)]
    exact supp_map (finPart D) hs i j

end GlobalTheory.SplitStab
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHyperspecialOfSplitPlaceStabilizerStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_hyperspecial_of_split_place_stabilizer : ∀ {D : D7} (V : HSp D) (e : Formalism.L2.Theta.AE D) (g : GA D V), IsSplitIdem D e → Formalism.L2.Theta.SuppAt e V g → (∀ y ∈ LamHat V, (fun a => finPart D e * (finMat D.sp.cm.sig V.gram g).mulVec y a) ∈ LamHat V) → (∀ y ∈ LamHat V, ∃ z ∈ LamHat V, (fun a => finPart D e * y a) = fun a => finPart D e * (finMat D.sp.cm.sig V.gram g).mulVec z a) → g ∈ KsphC V ∅ := by
  first | exact @GlobalTheory.SplitStab.mem_ksph_of_split | exact GlobalTheory.SplitStab.mem_ksph_of_split | (intros; apply GlobalTheory.SplitStab.mem_ksph_of_split <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothOfRelativeDimensionFibrePower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace GlobalTheory.FibPow

theorem smoothOfRelativeDimension_pow {X : Scheme.{0}} (A : Over X) (g : ℕ)
    (hA : SmoothOfRelativeDimension g A.hom) (k : ℕ) : SmoothOfRelativeDimension (k * g) (GlobalTheory.KS.pow A k).hom := by
  let e : GlobalTheory.KS.pow A k ≅ ReciprocityTheory.ChartRestriction.G.Out.powObj A k :=
    (limit.isLimit (Discrete.functor fun _ : Fin k => A)).conePointUniqueUpToIso
      (ReciprocityTheory.ChartRestriction.G.Out.powIsLimit A k)
  have hw : (GlobalTheory.KS.pow A k).hom = e.hom.left ≫ (ReciprocityTheory.ChartRestriction.G.Out.powObj A k).hom := (Over.w e.hom).symm
  have h1 := GlobalTheory.smoothOfRelativeDimension_powObj A g hA k
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have h2 : SmoothOfRelativeDimension (0 + k * g) (e.hom.left ≫ (ReciprocityTheory.ChartRestriction.G.Out.powObj A k).hom) :=
    inferInstance
  rw [hw]; simpa using h2

theorem smoothOfRelativeDimension_fibrePower : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (d g : ℕ),
    SmoothOfRelativeDimension d s → ∀ (A : Over X) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → ∀ k : ℕ, SmoothOfRelativeDimension (d + k * g) ((GlobalTheory.KS.pow A k).hom ≫ s) := by
  intro R _ X s d g hs A _ _ _ hA k
  have h := smoothOfRelativeDimension_pow A g hA k
  have h2 : SmoothOfRelativeDimension (k * g + d) ((GlobalTheory.KS.pow A k).hom ≫ s) := inferInstance
  rw [Nat.add_comm]; exact h2

end GlobalTheory.FibPow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParameterMonodromyZeroOfUnramified
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead

namespace GlobalTheory.TameType

theorem irreducible_twist {Γ V : Type} [Group Γ] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ Γ V}
    (h : ρ.IsIrreducible) (ν : Γ →* ℂˣ) : (twist ρ ν).IsIrreducible := by
  let f : Subrepresentation (twist ρ ν) → Subrepresentation ρ := fun S =>
    ⟨S.toSubmodule, fun g v hv => by
      have h1 := S.toSubmodule.smul_mem ((ν g)⁻¹ : ℂˣ).1 (S.apply_mem_toSubmodule g hv)
      simpa [smul_smul] using h1⟩
  have hn : (⊥ : Submodule ℂ V) ≠ ⊤ := fun e =>
    (bot_ne_top (α := Subrepresentation ρ)) (Subrepresentation.toSubmodule_injective e)
  have : Nontrivial (Subrepresentation (twist ρ ν)) := ⟨⊥, ⊤, fun e =>
    hn (congrArg Subrepresentation.toSubmodule e)⟩
  refine ⟨fun S => ?_⟩
  rcases eq_bot_or_eq_top (f S) with e | e
  · exact Or.inl (Subrepresentation.toSubmodule_injective (congrArg Subrepresentation.toSubmodule e :))
  · exact Or.inr (Subrepresentation.toSubmodule_injective (congrArg Subrepresentation.toSubmodule e :))

theorem charpoly_scalar {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (z : ℂ) :
    (z • (1 : Module.End ℂ V)).charpoly = (X - C z) ^ Module.finrank ℂ V := by
  classical
  rw [← LinearMap.charpoly_toMatrix _ (Module.finBasis ℂ V), map_smul, LinearMap.toMatrix_one,
    Matrix.smul_one_eq_diagonal, Matrix.charpoly_diagonal]
  simp

section WD

open GlobalTheory.WeilDeligne

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

theorem weilDeligneParameter_monodromy_zero_of_unramified {a : WD h} (ha : a.unr) : a.mono0 := by
  induction a using WD.ind
  exact (WD.monodromyZero_ofWeilDeligneRepClass_iff _).2 ((WD.unr_mk _).1 ha).1

theorem inePol_of_unr {a : WD h} (ha : a.unr) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B) :
    a.inePol σ = (X - 1) ^ a.lpDim := by
  induction a using WD.ind
  rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, ((WD.unr_mk _).1 ha).2, WD.lpDim_mk, LinearMap.charpoly_one]

theorem inePol_char_of_unr {a c : WD h} (ha : a.unr) (hc : c.lpDim = 1) {σ : G E Ω} (hσ : σ ∈ Ine (F := E) B)
    {z : ℂ} (hz : c.inePol σ = X - C z) : (a.lpChar c).inePol σ = (X - C z) ^ a.lpDim := by
  rw [← WD.lpDim_char a c hc]
  induction a using WD.ind with
  | hP m a =>
  induction c using WD.ind with
  | hP n c =>
    rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk] at hz
    have h1 := LinearMap.aeval_self_charpoly (c.ρ (ineIncl h ⟨σ, hσ⟩))
    rw [hz, map_sub, aeval_X, aeval_C, sub_eq_zero, Algebra.algebraMap_eq_smul_one] at h1
    rw [WD.lpChar_mk, WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, WD.lpDim_mk, WDRep.tensor_ρ,
      ((WD.unr_mk _).1 ha).2, h1, TensorProduct.map_smul_right, TensorProduct.map_one, charpoly_scalar]

end WD

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem inertialType_of_tame :
    ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
      (T : RowTie.WDTie N A) (S : SplitRead.Reading T) (i : N.Loc) (w : PlE H)
      (hw : IsSplitPl H w),
      TameSplitAll H.E → SplitRead.Laws S → SplitRead.TypeTame S i w hw →
      (∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
        A.inePol (A.locG (A.muC i) w) σ = X - C (iotaO N A i (chi1 N i σ))) →
      ∀ P : A.AV i, A.mono0 (A.locV i P w) ∧
        ∀ σ ∈ Ine (F := H.E) (N.plOm.1 w),
          A.inePol (A.locV i P w) σ =
            (X - 1) ^ R.r * (X - C (iotaO N A i (chi1 N i σ))) ^ R.t := by
  intro R H what₂ N A T S i w hw hTS hL hT hmu P
  obtain ⟨htame, hram, hv⟩ := hT
  obtain ⟨v, hv0, hv⟩ := hv P
  have L := hL i w hw
  have hs := (S i w hw).mu_ok.1
  obtain ⟨π₁, π₂, h1, h2, he⟩ := hTS w _ _ _ _ v hs htame hram hv0 hv
  let c : Irr (w.adicCompletion H.E) 1 :=
    { V := ℂ, π := detRep (Fin 1) (S i w hw).mu, smooth := (isSmooth_ofChar_iff _).2 hs.detChar,
      irr := isIrreducible_ofChar _ }
  let τ : Irr (w.adicCompletion H.E) R.t :=
    { V := π₂.V, π := twist π₂.π (detChar (Fin R.t) (S i w hw).mu), smooth := isSmooth_twist π₂.smooth hs.detChar,
      irr := irreducible_twist π₂.irr _ }
  have hc : Nonempty (c.π.Equiv (detRep (Fin 1) (S i w hw).mu)) := ⟨Representation.Equiv.refl _⟩
  have e1 := L.prod _ _ π₁ τ _ he
  have e2 := L.twist _ _ c π₂ τ hc ⟨Representation.Equiv.refl _⟩
  have u1 := (L.sph _ π₁).2 h1
  have u2 := (L.sph _ π₂).2 h2
  have eV := (S i w hw).locV P
  have eM := (S i w hw).locMu c hc
  rw [e1, e2] at eV
  refine ⟨?_, fun σ hσ => ?_⟩
  · rw [T.mono0, eV, WeilDeligne.WD.monomial_sum_iff, WeilDeligne.WD.monomial_char_iff _ _ (L.dim 1 c)]
    exact ⟨weilDeligneParameter_monodromy_zero_of_unramified u1, weilDeligneParameter_monodromy_zero_of_unramified u2⟩
  · have hz := hmu σ hσ
    rw [T.inePol _ _ _ hσ, eM] at hz
    rw [T.inePol _ _ _ hσ, eV, WeilDeligne.WD.inePol_sum, inePol_of_unr u1 hσ,
      inePol_char_of_unr u2 (L.dim 1 c) hσ hz, L.dim, L.dim]

end GlobalTheory.TameType
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralFiniteAdelesTensorIffLocalOrders
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralFiniteAdelesTensorIffLocalOrders
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

namespace GlobalTheory.PlaceComp.IntLocal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem exists_int_generators (E : Type) [Field E] [NumberField E] :
    ∃ (k : ℕ) (x : Fin k → 𝓞 E), ∀ w : 𝓞 E, ∃ n : Fin k → ℤ, w = ∑ j, n j • x j := by
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := 𝓞 E)
  refine ⟨k, s, fun w => ?_⟩
  have : w ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 this
  exact ⟨n, hn.symm⟩


omit [NumberField E] in
theorem mem_addClosure_of_mem_ordAt (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v ⊗[F] E)
    (hy : y ∈ ordAt E v) :
    y ∈ AddSubgroup.closure
      {y : Fv F v ⊗[F] E | ∃ a ∈ v.adicCompletionIntegers F, ∃ x : 𝓞 E, y = a ⊗ₜ[F] (x : E)} := by
  have h := Subring.mem_closure_iff.1 hy
  refine AddSubgroup.closure_mono ?_ h
  intro z hz
  induction hz using Submonoid.closure_induction with
  | mem z hz => exact hz
  | one => exact ⟨1, one_mem _, 1, rfl⟩
  | mul z w _ _ hz hw =>
    obtain ⟨a, ha, x, rfl⟩ := hz
    obtain ⟨b, hb, x', rfl⟩ := hw
    exact ⟨a * b, mul_mem ha hb, x * x', by
      rw [Algebra.TensorProduct.tmul_mul_tmul]; rfl⟩


omit [NumberField E] in
theorem exists_coeff {k : ℕ} (x : Fin k → 𝓞 E)
    (hx : ∀ w : 𝓞 E, ∃ n : Fin k → ℤ, w = ∑ j, n j • x j) (v : HeightOneSpectrum (𝓞 F))
    (y : Fv F v ⊗[F] E) (hy : y ∈ ordAt E v) :
    ∃ a : Fin k → Fv F v, (∀ j, a j ∈ v.adicCompletionIntegers F) ∧
      y = ∑ j, a j ⊗ₜ[F] (x j : E) := by
  have hy' := mem_addClosure_of_mem_ordAt v y hy
  clear hy
  induction hy' using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, w, rfl⟩ := hy
    obtain ⟨n, rfl⟩ := hx w
    refine ⟨fun j => n j • a, fun j => zsmul_mem ha _, ?_⟩
    show a ⊗ₜ[F] (algebraMap (𝓞 E) E (∑ j, n j • x j)) =
      ∑ j, (n j • a) ⊗ₜ[F] (algebraMap (𝓞 E) E (x j))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_zsmul, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TensorProduct.smul_tmul]
  | zero => exact ⟨0, fun _ => zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, ea⟩ := hy
    obtain ⟨b, hb, eb⟩ := hz
    exact ⟨a + b, fun j => add_mem (ha j) (hb j), by
      simp only [Pi.add_apply, ea, eb, TensorProduct.add_tmul, Finset.sum_add_distrib]⟩
  | neg y _ hy =>
    obtain ⟨a, ha, ea⟩ := hy
    exact ⟨-a, fun j => neg_mem (ha j), by
      simp only [Pi.neg_apply, ea, TensorProduct.neg_tmul, Finset.sum_neg_distrib]⟩

theorem mem_intA_iff :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (z : Af F ⊗[F] E),
      z ∈ intA F E ↔ ∀ v : HeightOneSpectrum (𝓞 F), evF E v z ∈ ordAt E v := by
  intro F E _ _ _ _ _ z
  constructor
  · intro hz v
    induction hz using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, x, rfl⟩ := hy
      exact Subring.subset_closure ⟨_, ha v, x, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
    | neg y _ hy => rw [map_neg]; exact neg_mem hy
  · intro h
    obtain ⟨k, x, hx⟩ := exists_int_generators E
    choose a ha ea using fun v => exists_coeff x hx v _ (h v)
    let A : Fin k → Af F := fun j =>
      ⟨fun v => a v j, Filter.Eventually.of_forall fun v => ha v j⟩
    have e : z = ∑ j, A j ⊗ₜ[F] (x j : E) := by
      apply evF_ext
      intro v
      set_option synthInstance.maxHeartbeats 100000 in
        rw [ea v, map_sum]
      exact Finset.sum_congr rfl fun j _ => rfl
    rw [e]
    exact sum_mem fun j _ => AddSubgroup.subset_closure ⟨A j, fun v => ha v j, x j, rfl⟩

end GlobalTheory.PlaceComp.IntLocal
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralFiniteAdelesTensorIffLocalOrdersStatement
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_integralFiniteAdelesTensor_iff_localOrders : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (z : Af F ⊗[F] E), z ∈ intA F E ↔ ∀ v : HeightOneSpectrum (𝓞 F), evF E v z ∈ ordAt E v := by
  first | exact @GlobalTheory.PlaceComp.IntLocal.mem_intA_iff | exact GlobalTheory.PlaceComp.IntLocal.mem_intA_iff | (intros; apply GlobalTheory.PlaceComp.IntLocal.mem_intA_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StabilisesCompletedLatticeIffLocalMatrixIntegral
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StabilisesCompletedLatticeIffLocalMatrixIntegral
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix

namespace GlobalTheory.PlaceComp.StabLoc

section Ring

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n] (O : Subring R)

theorem mem_range_iff (m : GL n R) :
    m ∈ (Formalism.UG.bc (n := n) O.subtype).range ↔
      ∀ y : n → R, (∀ i, y i ∈ O) ↔ ∀ i, m.1.mulVec y i ∈ O := by
  have key : ∀ (A : Matrix n n R), (∀ i j, A i j ∈ O) → ∀ y : n → R, (∀ i, y i ∈ O) →
      ∀ i, A.mulVec y i ∈ O := fun A hA y hy i =>
    O.sum_mem fun j _ => O.mul_mem (hA i j) (hy j)
  have hs : ∀ j i : n, (Pi.single j (1 : R) : n → R) i ∈ O := by
    intro j i
    by_cases h : i = j
    · subst h; simp [O.one_mem]
    · simp [h, O.zero_mem]
  constructor
  · rintro ⟨k, rfl⟩ y
    refine ⟨key _ (fun i j => (k.1 i j).2) y, fun h => ?_⟩
    have := key (Formalism.UG.bc (n := n) O.subtype k⁻¹).1 (fun i j => ((k⁻¹).1 i j).2) _ h
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
      Matrix.one_mulVec] at this
  · intro h
    have h1 : ∀ i j, m.1 i j ∈ O := fun i j => by
      simpa using (h (Pi.single j 1)).1 (hs j) i
    have h2 : ∀ i j, (m⁻¹).1 i j ∈ O := fun i j => by
      have := (h ((m⁻¹).1.mulVec (Pi.single j 1))).2 (by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
        exact hs j) i
      rwa [Matrix.mulVec_single_one] at this
    let A : Matrix n n O := Matrix.of fun i j => ⟨m.1 i j, h1 i j⟩
    let B : Matrix n n O := Matrix.of fun i j => ⟨(m⁻¹).1 i j, h2 i j⟩
    have hA : O.subtype.mapMatrix A = m.1 := rfl
    have hB : O.subtype.mapMatrix B = (m⁻¹).1 := rfl
    have hinj : Function.Injective (O.subtype.mapMatrix : Matrix n n O →+* Matrix n n R) :=
      fun X Y hXY => Matrix.ext fun i j => Subtype.ext (congrFun (congrFun hXY i) j)
    refine ⟨⟨A, B, hinj ?_, hinj ?_⟩, Units.ext rfl⟩
    · rw [map_mul, hA, hB, map_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    · rw [map_mul, hA, hB, map_one, ← Units.val_mul, inv_mul_cancel, Units.val_one]

end Ring

theorem stab_iff (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (h : GL (Fin V.rank) (Fv F v ⊗[F] E))
    (hh : IsFrameAt V v h) (g : HA (AF F) hc.sig V.gram) (hg : ∀ w, w ≠ v → locMat hc V w g = 1) :
    Stab hc V g ↔
      h⁻¹ * locMat hc V v g * h ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range := by
  have hev : ∀ w (y : Fin V.rank → Af F ⊗[F] E),
      (fun i => evF E w ((finMat hc.sig V.gram g).mulVec y i)) =
        (locMat hc V w g).1.mulVec fun i => evF E w (y i) := fun w y => by
    funext i
    rw [locMat_val]
    exact RingHom.map_mulVec (evF E w) _ y i
  have hloc : Stab hc V g ↔ ∀ x, x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v ↔
      (locMat hc V v g).1.mulVec x ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.latLoc (F := F) V v := by
    constructor
    · intro hs x
      have hx : ∀ w, w ≠ v → (fun i => evF E w (sgT E v (x i))) = 0 := fun w hw =>
        funext fun i => evF_sgT_ne hw _
      have hxv : (fun i => evF E v (sgT E v (x i))) = x := funext fun i => evF_sgT_self v _
      have := hs fun i => sgT E v (x i)
      rw [mem_lamHat_iff, mem_lamHat_iff] at this
      simp only [hev] at this
      constructor
      · intro h0
        have h1 := this.1 (fun w => by
          by_cases hw : w = v
          · subst hw; rw [hxv]; exact h0
          · rw [hx w hw]; exact zero_mem _) v
        rwa [hxv] at h1
      · intro h0
        have h1 := this.2 (fun w => by
          by_cases hw : w = v
          · subst hw; rw [hxv]; exact h0
          · rw [hx w hw, Matrix.mulVec_zero]; exact zero_mem _) v
        rwa [hxv] at h1
    · intro hs y
      rw [mem_lamHat_iff, mem_lamHat_iff]
      refine forall_congr' fun w => ?_
      rw [hev]
      by_cases hw : w = v
      · subst hw; exact hs _
      · rw [hg w hw, Units.val_one, Matrix.one_mulVec]
  rw [hloc, mem_range_iff]
  constructor
  · intro hs y
    have := hs (h.1.mulVec y)
    rw [hh, hh, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this
    rwa [Units.val_mul, Units.val_mul]
  · intro hs x
    have := hs ((h⁻¹).1.mulVec x)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_right, Units.val_mul,
      ← Matrix.mulVec_mulVec] at this
    rw [hh, hh]
    exact this

end GlobalTheory.PlaceComp.StabLoc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StabilisesCompletedLatticeIffLocalMatrixIntegralStatement
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stabilises_completedLattice_iff_localMatrix_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) (V : HSpace E) (v : HeightOneSpectrum (𝓞 F)) (h : GL (Fin V.rank) (Fv F v ⊗[F] E)), IsFrameAt V v h → ∀ g, (∀ w, w ≠ v → locMat hc V w g = 1) → (Stab hc V g ↔ h⁻¹ * locMat hc V v g * h ∈ (Formalism.UG.bc (n := Fin V.rank) (ordAt E v).subtype).range) := by
  first | exact @GlobalTheory.PlaceComp.StabLoc.stab_iff | exact GlobalTheory.PlaceComp.StabLoc.stab_iff | (intros; apply GlobalTheory.PlaceComp.StabLoc.stab_iff <;> assumption)
end
end
