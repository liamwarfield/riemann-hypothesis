module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsIdealInClassOfNormLeSqrtDiscr
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Formalism.HarderNarasimhan.ShiftInvariance

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeDedekindZetaRealValueAndLeZetaPow
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeDedekindZetaRealValueAndLeZetaPow
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.DedekindZetaBound

theorem term_eq_ofReal (a : ℕ → ℕ) {l : ℕ} (hl : 2 ≤ l) (n : ℕ) :
    LSeries.term (fun n => (a n : ℂ)) (l : ℂ) n = (((a n : ℝ) * ((n : ℝ) ^ l)⁻¹ : ℝ) : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · have : l ≠ 0 := by omega
    simp [this]
  · rw [LSeries.term_of_ne_zero hn, Complex.cpow_natCast, div_eq_mul_inv]
    push_cast
    rfl

theorem lseriesHasSum_zeta_pow {s : ℂ} (hs : 1 < s.re) (k : ℕ) :
    LSeriesHasSum (fun n => (((ArithmeticFunction.zeta ^ k : ArithmeticFunction ℕ) n : ℕ) : ℂ)) s
      (riemannZeta s ^ k) := by
  induction k with
  | zero =>
    have := hasSum_single (f := LSeries.term
      (fun n => (((ArithmeticFunction.zeta ^ 0 : ArithmeticFunction ℕ) n : ℕ) : ℂ)) s) 1
      (fun b hb => by
        rcases eq_or_ne b 0 with rfl | h0
        · simp
        · simp [LSeries.term_of_ne_zero h0, ArithmeticFunction.one_apply_ne hb])
    simpa [LSeriesHasSum] using this
  | succ k ih =>
    have := ArithmeticFunction.LSeriesHasSum_mul
      (f := ((ArithmeticFunction.zeta ^ k : ArithmeticFunction ℕ) : ArithmeticFunction ℂ))
      (g := ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) : ArithmeticFunction ℂ))
      ih (ArithmeticFunction.LSeriesHasSum_zeta hs)
    rw [← ArithmeticFunction.natCoe_mul] at this
    rw [pow_succ, pow_succ]
    exact this

theorem hasSum_zeta_pow {l : ℕ} (hl : 2 ≤ l) (k : ℕ) :
    HasSum (fun n : ℕ => (((ArithmeticFunction.zeta ^ k : ArithmeticFunction ℕ) n : ℕ) : ℝ) *
      ((n : ℝ) ^ l)⁻¹) ((∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) ^ k) := by
  have hs : 1 < ((l : ℂ)).re := by
    rw [Complex.natCast_re]; exact_mod_cast hl
  have h := lseriesHasSum_zeta_pow hs k
  have e : riemannZeta (l : ℂ) = ((∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l : ℝ) : ℂ) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, Complex.ofReal_tsum]
    refine tsum_congr fun m => ?_
    rw [Complex.cpow_natCast]
    push_cast
    rfl
  rw [e, ← Complex.ofReal_pow, LSeriesHasSum, funext (term_eq_ofReal _ hl)] at h
  exact Complex.hasSum_ofReal.1 h

theorem one_le_zetaE_and_le : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ), 2 ≤ l →
    1 ≤ zetaE E l ∧ zetaE E l ≤ (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) ^ Module.finrank ℚ E := by
  intro E _ _ l hl
  have h := hasSum_zeta_pow hl (Module.finrank ℚ E)
  set a : ℕ → ℝ := fun n =>
    (Nat.card {I : Ideal (𝓞 E) // Ideal.absNorm I = n} : ℝ) * ((n : ℝ) ^ l)⁻¹ with ha
  have h0 : ∀ n, 0 ≤ a n := fun n => by positivity
  have hle : ∀ n : ℕ, a n ≤
      (((ArithmeticFunction.zeta ^ Module.finrank ℚ E : ArithmeticFunction ℕ) n : ℕ) : ℝ) *
        ((n : ℝ) ^ l)⁻¹ := fun n => by
    rcases eq_or_ne n 0 with rfl | hn
    · have : l ≠ 0 := by omega
      simp [ha, this]
    · refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      exact_mod_cast GlobalTheory.ncard_ideal_absNorm_eq_le E hn
  have hsum : Summable a := Summable.of_nonneg_of_le h0 hle h.summable
  have e : zetaE E l = ∑' n, a n := by
    unfold zetaE dedekindZeta LSeries
    rw [funext (term_eq_ofReal _ hl), ← Complex.ofReal_tsum, Complex.ofReal_re]
  rw [e]
  refine ⟨le_trans ?_ (hsum.le_tsum 1 fun n _ => h0 n), hasSum_le hle hsum.hasSum h⟩
  simp [ha, Ideal.absNorm_eq_one_iff]

end GlobalTheory.DedekindZetaBound
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeDedekindZetaRealValueAndLeZetaPowStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_le_dedekindZetaRealValue_and_le_zeta_pow : ∀ (E : Type) [Field E] [NumberField E] (l : ℕ), 2 ≤ l → 1 ≤ zetaE E l ∧ zetaE E l ≤ (∑' m : ℕ, 1 / ((m : ℝ) + 1) ^ l) ^ Module.finrank ℚ E := by
  first | exact @GlobalTheory.DedekindZetaBound.one_le_zetaE_and_le | exact GlobalTheory.DedekindZetaBound.one_le_zetaE_and_le | (intros; apply GlobalTheory.DedekindZetaBound.one_le_zetaE_and_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsComplOfSaturated
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SaturatedHasComplement
namespace GlobalTheory.SaturatedSublatticeComplement

universe u_1 u_2

open Module

theorem saturated_has_complement {R : Type u_1} {V : Type u_2} [CommRing R] [IsDedekindDomain R]
    [AddCommGroup V] [Module R V] (N M : Submodule R V) (hNM : N ≤ M) (hM : M.FG)
    (hsat : ∀ (r : R) (y : V), r ≠ 0 → y ∈ M → r • y ∈ N → y ∈ N) :
    ∃ A : Submodule R V, A ⊓ N = ⊥ ∧ A ⊔ N = M := by
  classical
  let N' : Submodule R M := N.comap M.subtype
  haveI : Module.Finite R M := Module.Finite.iff_fg.mpr hM
  haveI : IsTorsionFree R (M ⧸ N') := by
    refine Module.IsTorsionFree.of_smul_eq_zero ?_
    intro r q hq
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    obtain ⟨m, rfl⟩ := N'.mkQ_surjective q
    have h1 : r • m ∈ N' := by
      rw [← Submodule.Quotient.mk_eq_zero]
      simpa using hq
    have h2 : (m : V) ∈ N := hsat r m hr m.2 (by simpa [N'] using h1)
    exact (Submodule.Quotient.mk_eq_zero N').mpr (by simpa [N'] using h2)
  haveI : Module.FinitePresentation R (M ⧸ N') := Module.finitePresentation_of_finite R _
  haveI : Module.Projective R (M ⧸ N') := Module.Flat.projective_of_finitePresentation
  obtain ⟨g, hg⟩ := Module.projective_lifting_property N'.mkQ LinearMap.id N'.mkQ_surjective
  have hg' : ∀ q, N'.mkQ (g q) = q := fun q => LinearMap.congr_fun hg q
  refine ⟨(LinearMap.range g).map M.subtype, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxA, hxN⟩
    obtain ⟨_, ⟨q, rfl⟩, rfl⟩ := hxA
    have hmem : g q ∈ N' := by simpa [N'] using hxN
    have hq0 : q = 0 := by
      rw [← hg' q]
      exact (Submodule.Quotient.mk_eq_zero N').mpr hmem
    simp [hq0]
  · apply le_antisymm
    · exact sup_le (by
        rintro x ⟨y, -, rfl⟩
        exact y.2) hNM
    · intro x hx
      let m : M := ⟨x, hx⟩
      have hd : m - g (N'.mkQ m) ∈ N' := by
        rw [← Submodule.Quotient.mk_eq_zero]
        have := hg' (N'.mkQ m)
        simp only [Submodule.mkQ_apply] at this ⊢
        rw [Submodule.Quotient.mk_sub, this, sub_self]
      have hx' : x = (g (N'.mkQ m) : V) + ((m - g (N'.mkQ m) : M) : V) := by simp [m]
      rw [hx']
      exact Submodule.add_mem_sup ⟨g (N'.mkQ m), ⟨_, rfl⟩, rfl⟩ (by simpa [N'] using hd)

theorem main : ∀ {R : Type u_1} {V : Type u_2} [inst : CommRing R] [IsDedekindDomain R]
    [inst_2 : AddCommGroup V] [inst_3 : Module R V] (N M : Submodule R V), N ≤ M →
    Submodule.FG M → (∀ (r : R) (y : V), r ≠ (0 : R) → y ∈ M → r • y ∈ N → y ∈ N) →
    ∃ (A : Submodule R V), A ⊓ N = ⊥ ∧ A ⊔ N = M :=
  fun N M h1 h2 h3 => saturated_has_complement N M h1 h2 h3

end GlobalTheory.SaturatedSublatticeComplement
end

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem exists_compl_of_saturated {R V : Type*} [CommRing R] [IsDedekindDomain R]
    [AddCommGroup V] [Module R V] (N M : Submodule R V) (hNM : N ≤ M) (hM : M.FG)
    (hsat : ∀ (r : R) (y : V), r ≠ 0 → y ∈ M → r • y ∈ N → y ∈ N) :
    ∃ A : Submodule R V, A ⊓ N = ⊥ ∧ A ⊔ N = M := by
  first
  | exact @_root_.GlobalTheory.SaturatedSublatticeComplement.main
  | exact _root_.GlobalTheory.SaturatedSublatticeComplement.main
  | (apply _root_.GlobalTheory.SaturatedSublatticeComplement.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SaturatedSublatticeComplement.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SaturatedSublatticeComplement.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SaturatedSublatticeComplement.main ..)

theorem saturatedFlag_splits : ∀ (E : Type) [Field E] [NumberField E] (n a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 E) (Fin n → E)), S 0 = ⊥ → Monotone S → (S (Fin.last a)).FG → (∀ i, ∀ y ∈ S (Fin.last a), y ∈ Submodule.span E (S i : Set (Fin n → E)) → y ∈ S i) → ∃ A : Fin a → Submodule (𝓞 E) (Fin n → E), ∀ i, A i ⊓ S i.castSucc = ⊥ ∧ A i ⊔ S i.castSucc = S i.succ := by
  intro E _ _ n a S _ hmono hfg hsat
  have key : ∀ i : Fin a, ∃ A : Submodule (𝓞 E) (Fin n → E),
      A ⊓ S i.castSucc = ⊥ ∧ A ⊔ S i.castSucc = S i.succ := by
    intro i
    have hle : S i.succ ≤ S (Fin.last a) := hmono (Fin.le_last _)
    refine exists_compl_of_saturated _ _ (hmono (Fin.castSucc_lt_succ).le)
      (Submodule.FG.of_le hfg hle) ?_
    intro r y hr hy hry
    apply hsat _ y (hle hy)
    have hr' : (algebraMap (𝓞 E) E r) ≠ 0 := by
      simpa using hr
    have : y = (algebraMap (𝓞 E) E r)⁻¹ • (r • y) := by
      rw [← algebraMap_smul E r y, smul_smul, inv_mul_cancel₀ hr', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hry)
  choose A hA using key
  exact ⟨A, hA⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealUnipotentRadicalEmbedsAdelicRadical
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealUnipotentRadicalEmbedsAdelicRadical
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

noncomputable section

namespace GlobalTheory.RadEmb

theorem hform_eq_dot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    Formalism.UG.hform (starRingEnd ℂ) A x y = star x ⬝ᵥ (A *ᵥ y) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

theorem hform_frame {n : ℕ} {ε : Fin n → Bool} {A P : Matrix (Fin n) (Fin n) ℂ} (h : Pᴴ * A * P = Jm ε)
    (x y : Fin n → ℂ) :
    Formalism.UG.hform (starRingEnd ℂ) A (P *ᵥ x) (P *ᵥ y) = star (Formalism.QuantumDeterminants.herm (Jm ε) x y) := by
  have e : star x ⬝ᵥ (Jm ε *ᵥ y) = star (Formalism.QuantumDeterminants.herm (Jm ε) x y) := by
    simp only [Formalism.QuantumDeterminants.herm, Jm, dotProduct, Matrix.mulVec_diagonal, star_sum, Pi.star_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp [mul_comm]
  rw [← e, ← h, hform_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec]

theorem inUnipRad_one (I : AutInst) {A : Type} [CommRing A] (s : A →+* A) (JA : Matrix (Fin I.n) (Fin I.n) A)
    (WA : Submodule A (Fin I.n → A)) : I.InUnipRad s JA WA 1 := by
  refine ⟨fun x _ => by simp, fun y _ => by simp, fun y x _ => by simp [Formalism.UG.hform]⟩

theorem span_isot (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (v : InfinitePlace I.F) (hW : I.IsIsot W) :
    ∀ x ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)),
    ∀ y ∈ Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)),
      Formalism.UG.hform (starRingEnd ℂ) (I.J.map (I.φ v)) x y = 0 := by
  have hφ : ∀ a, I.φ v (starRingEnd I.E a) = starRingEnd ℂ (I.φ v a) := fun a => I.cm.cmUnram.2.1 _ a
  intro x hx y hy
  rw [hform_eq_dot]
  induction hx using Submodule.span_induction with
  | mem x hx =>
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨b, hb, rfl⟩ := hy
      have := congrArg (I.φ v) (hW.2 a ha b hb)
      rw [← hform_eq_dot]
      set_option synthInstance.maxHeartbeats 100000 in
        simpa only [Formalism.UG.hform, map_sum, map_mul, hφ, map_zero, Matrix.map_apply] using this
    | zero => simp
    | add a b _ _ ha hb => rw [Matrix.mulVec_add, dotProduct_add, ha, hb, add_zero]
    | smul c a _ ha => rw [Matrix.mulVec_smul, dotProduct_smul, ha, smul_zero]
  | zero => simp
  | add a b _ _ ha hb => rw [star_add, add_dotProduct, ha, hb, add_zero]
  | smul c a _ ha => rw [star_smul, smul_dotProduct, ha, smul_zero]

theorem radical_embeds : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (v : InfinitePlace I.F), I.IsIsot W →
    ∃ Wv : Submodule ℂ (Fin I.n → ℂ), IsIsoC (I.ε v) Wv ∧
      ∀ m ∈ NW (I.ε v) Wv, (open Classical in ((Pi.mulSingle v m, 1) : I.GA)) ∈ I.NA W := by
  classical
  intro I W v hW
  have hP : ∀ u, I.P u * (I.P u)⁻¹ = 1 := fun u =>
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit u))
  have hQ : ∀ y, I.P v *ᵥ ((I.P v)⁻¹ *ᵥ y) = y := fun y => by
    rw [Matrix.mulVec_mulVec, hP, Matrix.one_mulVec]
  set WA := Submodule.span ℂ ((fun w : Fin I.n → I.E => fun i => I.φ v (w i)) '' (W : Set _)) with hWA
  have hf := hform_frame (I.P_spec v)
  refine ⟨WA.comap (I.P v).mulVecLin, ⟨?_, fun x hx y hy => ?_⟩, fun m hm => ⟨fun u => ?_, ?_⟩⟩
  · intro h
    apply hW.1
    rw [eq_bot_iff]
    intro w hw
    have h1 : (I.P v)⁻¹ *ᵥ (fun i => I.φ v (w i)) ∈ WA.comap (I.P v).mulVecLin := by
      rw [Submodule.mem_comap, Matrix.mulVecLin_apply, hQ]
      exact Submodule.subset_span ⟨w, hw, rfl⟩
    rw [h, Submodule.mem_bot] at h1
    have h2 := hQ (fun i => I.φ v (w i))
    rw [h1, Matrix.mulVec_zero] at h2
    rw [Submodule.mem_bot]
    funext i
    exact (map_eq_zero (I.φ v)).1 (congrFun h2 i).symm
  · have := span_isot I W v hW _ hx _ hy
    simp only [Matrix.mulVecLin_apply] at this
    rw [hf] at this
    exact star_eq_zero.1 this
  · by_cases hu : u = v
    · subst hu
      simp only [Pi.mulSingle_eq_same]
      have e : ∀ y, (I.P u * uMat m * (I.P u)⁻¹ - 1) *ᵥ y = I.P u *ᵥ ((umat m - 1) *ᵥ ((I.P u)⁻¹ *ᵥ y)) := by
        intro y
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hP]
      have mem : ∀ x ∈ WA, (I.P u)⁻¹ *ᵥ x ∈ WA.comap (I.P u).mulVecLin := fun x hx => by
        rw [Submodule.mem_comap, Matrix.mulVecLin_apply, hQ]; exact hx
      refine ⟨fun x hx => ?_, fun y hy => ?_, fun y x hx => ?_⟩
      · rw [e, hm.1 _ (mem x hx), Matrix.mulVec_zero]
      · rw [e]
        refine hm.2.1 _ fun x hx => ?_
        have := hy _ hx
        rw [← hQ y, Matrix.mulVecLin_apply, hf] at this
        exact star_eq_zero.1 this
      · rw [e, ← hQ x, hf, hm.2.2 _ _ (mem x hx), star_zero]
    · have e : uMat ((Pi.mulSingle v m : I.Ginf) u) = 1 := by
        rw [Pi.mulSingle_eq_of_ne hu]; rfl
      simp only [e, Matrix.mul_one, hP]
      exact inUnipRad_one I _ _ _
  · exact inUnipRad_one I _ _ _

end GlobalTheory.RadEmb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealUnipotentRadicalEmbedsAdelicRadicalStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realUnipotentRadical_embeds_adelicRadical : ∀ (I : AutInst) (W : Submodule I.E (Fin I.n → I.E)) (v : InfinitePlace I.F), I.IsIsot W → ∃ Wv : Submodule ℂ (Fin I.n → ℂ), IsIsoC (I.ε v) Wv ∧ ∀ m ∈ NW (I.ε v) Wv, (open Classical in ((Pi.mulSingle v m, 1) : I.GA)) ∈ I.NA W := by
  first | exact @GlobalTheory.RadEmb.radical_embeds | exact GlobalTheory.RadEmb.radical_embeds | (intros; apply GlobalTheory.RadEmb.radical_embeds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableAndNormAmplitudeLeOfPairings
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableAndNormAmplitudeLeOfPairings
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.OpNorm

theorem norm_le_sum_inner {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W] {ι : Type} [Fintype ι]
    (b : OrthonormalBasis ι ℂ W) (u : W) : ‖u‖ ≤ ∑ i, ‖⟪b i, u⟫_ℂ‖ := by
  calc ‖u‖ = ‖∑ i, ⟪b i, u⟫_ℂ • b i‖ := by rw [b.sum_repr']
    _ ≤ ∑ i, ‖⟪b i, u⟫_ℂ • b i‖ := norm_sum_le _ _
    _ = ∑ i, ‖⟪b i, u⟫_ℂ‖ := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [norm_smul, b.orthonormal.1 i, mul_one]

theorem rankOne_integral {X : Type} [MeasurableSpace X] (ν : Measure X)
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
    (f : X → Wp) (g : X → Wq) (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g ν) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ (v : Wp) (w : Wq), ‖v‖ = 1 → ‖w‖ = 1 →
      ∫⁻ x, ENNReal.ofReal (‖⟪v, f x⟫_ℂ‖ * ‖⟪w, g x⟫_ℂ‖) ∂ν ≤ ENNReal.ofReal K) :
    Integrable (fun x => (innerSL ℂ (g x)).smulRight (f x)) ν ∧
      ‖∫ x, (innerSL ℂ (g x)).smulRight (f x) ∂ν‖ ≤ K := by
  haveI := FiniteDimensional.complete ℂ Wp
  set T : X → (Wq →L[ℂ] Wp) := fun x => (innerSL ℂ (g x)).smulRight (f x) with hT
  set e := stdOrthonormalBasis ℂ Wp
  set b := stdOrthonormalBasis ℂ Wq
  have hcont : Continuous (Function.uncurry fun (a : Wq) (c : Wp) => (innerSL ℂ a).smulRight c) := by
    fun_prop
  have hmeas : AEStronglyMeasurable T ν := hcont.comp_aestronglyMeasurable₂ hg hf
  have hbd : ∀ x, ‖f x‖ * ‖g x‖ ≤ ∑ j, ∑ i, ‖⟪e j, f x⟫_ℂ‖ * ‖⟪b i, g x⟫_ℂ‖ := fun x => by
    rw [← Finset.sum_mul_sum]
    exact mul_le_mul (norm_le_sum_inner e _) (norm_le_sum_inner b _) (norm_nonneg _)
      (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hnormT : ∀ x, ‖T x‖ = ‖g x‖ * ‖f x‖ := fun x => by
    simp only [hT, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]
  have hterm : ∀ j i, AEMeasurable
      (fun x => ENNReal.ofReal (‖⟪e j, f x⟫_ℂ‖ * ‖⟪b i, g x⟫_ℂ‖)) ν := fun j i =>
    ((aestronglyMeasurable_const.inner hf).norm.mul
      (aestronglyMeasurable_const.inner hg).norm).aemeasurable.ennreal_ofReal
  have hfin : (∫⁻ x, ENNReal.ofReal ‖T x‖ ∂ν) < ⊤ := by
    calc (∫⁻ x, ENNReal.ofReal ‖T x‖ ∂ν)
        ≤ ∫⁻ x, ∑ j, ∑ i, ENNReal.ofReal (‖⟪e j, f x⟫_ℂ‖ * ‖⟪b i, g x⟫_ℂ‖) ∂ν := by
          refine lintegral_mono fun x => ?_
          rw [hnormT, mul_comm]
          refine (ENNReal.ofReal_le_ofReal (hbd x)).trans (le_of_eq ?_)
          rw [ENNReal.ofReal_sum_of_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity]
          exact Finset.sum_congr rfl fun j _ => ENNReal.ofReal_sum_of_nonneg fun _ _ => by positivity
      _ = ∑ j, ∑ i, ∫⁻ x, ENNReal.ofReal (‖⟪e j, f x⟫_ℂ‖ * ‖⟪b i, g x⟫_ℂ‖) ∂ν := by
          have hsum : ∀ j, AEMeasurable
              (fun x => ∑ i, ENNReal.ofReal (‖⟪e j, f x⟫_ℂ‖ * ‖⟪b i, g x⟫_ℂ‖)) ν := by
            intro j
            first
              | exact Finset.aemeasurable_fun_sum _ fun i _ => hterm j i
              | exact Finset.aemeasurable_sum' _ fun i _ => hterm j i
              | exact (Finset.aemeasurable_sum _ fun i _ => hterm j i).congr
                  (Filter.Eventually.of_forall fun x => by simp [Finset.sum_apply])
          rw [MeasureTheory.lintegral_finsetSum' _ fun j _ => hsum j]
          exact Finset.sum_congr rfl fun j _ => MeasureTheory.lintegral_finsetSum' _ fun i _ => hterm j i
      _ ≤ ∑ j, ∑ i, ENNReal.ofReal K :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun i _ =>
            h (e j) (b i) (e.orthonormal.1 j) (b.orthonormal.1 i)
      _ < ⊤ := by simp [ENNReal.mul_lt_top]
  have hi : Integrable T ν := ⟨hmeas, hasFiniteIntegral_iff_norm _ |>.2 hfin⟩
  refine ⟨hi, ?_⟩
  have key : ∀ (v : Wp) (w : Wq), ‖v‖ = 1 → ‖w‖ = 1 → ‖⟪v, (∫ x, T x ∂ν) w⟫_ℂ‖ ≤ K := by
    intro v w hv hw
    rw [ContinuousLinearMap.integral_apply hi w, ← integral_inner (hi.apply_continuousLinearMap w) v]
    refine (norm_integral_le_lintegral_norm _).trans (ENNReal.toReal_le_of_le_ofReal hK ?_)
    refine le_trans (le_of_eq (lintegral_congr fun x => ?_)) (h v w hv hw)
    show ENNReal.ofReal ‖⟪v, ⟪g x, w⟫_ℂ • f x⟫_ℂ‖ = ENNReal.ofReal (‖⟪v, f x⟫_ℂ‖ * ‖⟪w, g x⟫_ℂ‖)
    rw [inner_smul_right, norm_mul, norm_inner_symm, mul_comm]
  refine ContinuousLinearMap.opNorm_le_of_unit_norm hK fun w hw => ?_
  set y := (∫ x, T x ∂ν) w
  by_cases hy : y = 0
  · rw [hy, norm_zero]; exact hK
  have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hv : ‖((‖y‖⁻¹ : ℝ) : ℂ) • y‖ = 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hy'), inv_mul_cancel₀ hy'.ne']
  have hk := key _ w hv hw
  rw [inner_smul_left, norm_mul, Complex.conj_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.2 hy'), inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm] at hk
  calc ‖y‖ = ‖y‖⁻¹ * ‖y‖ ^ 2 := by rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hy'.ne', one_mul]
    _ ≤ K := hk

private theorem mul_mem_dualWeyl_complex {k r : ℕ} {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) :
    a * b ∈ GG k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  calc (a * b)ᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

private theorem measurableSet_of_isOpen' (k r : ℕ) : MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r} := by
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hc : IsClosed {x : Mt k r | (Matrix.of x)ᴴ * Hpk k r * Matrix.of x = Hpk k r} :=
    isClosed_eq ((hof.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hof) continuous_const
  exact hc.measurableSet

theorem integrable_and_norm_ampJ_le : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (ν : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (γ : Mat k r) (c K : ℝ), γ ∈ GG k r → ν {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → 0 < c → 0 ≤ K → (∀ (v : Wp) (w : Wq), ‖v‖ = 1 → ‖w‖ = 1 → ∫⁻ x, ENNReal.ofReal (‖⟪v, Φ (γ * Matrix.of x)⟫_ℂ‖ * ‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖) ∂ν ≤ ENNReal.ofReal K) → Integrable (fun x => (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x))) ν ∧ ‖(haveI := FiniteDimensional.complete ℂ Wp; ampJ ν c Φ Φ' γ)‖ ≤ K / c := by
  intro k r Wp _ _ _ Wq _ _ _ ν Φ Φ' γ c K hγ hν hΦ hΦ' hc hK h
  haveI := FiniteDimensional.complete ℂ Wp
  have hof : Continuous (fun x : Mt k r => (Matrix.of x : Mat k r)) := continuous_id
  have hS := measurableSet_of_isOpen' k r
  have hae : ν.restrict {x : Mt k r | Matrix.of x ∈ GG k r} = ν :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hν)
  have hf : AEStronglyMeasurable (fun x : Mt k r => Φ (γ * Matrix.of x)) ν := by
    rw [← hae]
    exact (hΦ.comp (continuous_const.mul hof).continuousOn fun x hx => mul_mem_dualWeyl_complex hγ hx).aestronglyMeasurable hS
  have hg : AEStronglyMeasurable (fun x : Mt k r => Φ' (Matrix.of x)) ν := by
    rw [← hae]
    exact (hΦ'.comp hof.continuousOn fun x hx => hx).aestronglyMeasurable hS
  obtain ⟨hi, hn⟩ := rankOne_integral ν _ _ hf hg K hK h
  refine ⟨hi, ?_⟩
  simp only [ampJ, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left hn (inv_nonneg.2 hc.le)

end GlobalTheory.Amp.OpNorm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableAndNormAmplitudeLeOfPairingsStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_and_norm_amplitude_le_of_pairings : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] {Wq : Type} [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (ν : Measure (Mt k r)) (Φ : Mat k r → Wp) (Φ' : Mat k r → Wq) (γ : Mat k r) (c K : ℝ), γ ∈ GG k r → ν {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → ContinuousOn Φ' (GG k r) → 0 < c → 0 ≤ K → (∀ (v : Wp) (w : Wq), ‖v‖ = 1 → ‖w‖ = 1 → ∫⁻ x, ENNReal.ofReal (‖⟪v, Φ (γ * Matrix.of x)⟫_ℂ‖ * ‖⟪w, Φ' (Matrix.of x)⟫_ℂ‖) ∂ν ≤ ENNReal.ofReal K) → Integrable (fun x => (innerSL ℂ (Φ' (Matrix.of x))).smulRight (Φ (γ * Matrix.of x))) ν ∧ ‖(haveI := FiniteDimensional.complete ℂ Wp; ampJ ν c Φ Φ' γ)‖ ≤ K / c := by
  first | exact @GlobalTheory.Amp.OpNorm.integrable_and_norm_ampJ_le | exact GlobalTheory.Amp.OpNorm.integrable_and_norm_ampJ_le | (intros; apply GlobalTheory.Amp.OpNorm.integrable_and_norm_ampJ_le <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LinearIndependentSkew
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.TwoSidedJac

open Kronecker

noncomputable def twoSided {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ) :
    Matrix (Fin a) (Fin b) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin b) ℂ where
  toFun T := A * T * B
  map_add' S T := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c T := by simp [Matrix.mul_smul, Matrix.smul_mul]

theorem twoSided_apply {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ)
    (T : Matrix (Fin a) (Fin b) ℂ) : twoSided A B T = A * T * B := rfl

theorem det_twoSided {a b : ℕ} (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ) :
    LinearMap.det (twoSided A B) = A.det ^ b * B.det ^ a := by
  rw [← LinearMap.det_toMatrix (Matrix.stdBasis ℂ (Fin a) (Fin b))]
  have h : LinearMap.toMatrix (Matrix.stdBasis ℂ (Fin a) (Fin b))
      (Matrix.stdBasis ℂ (Fin a) (Fin b)) (twoSided A B) = A ⊗ₖ Bᵀ := by
    ext ⟨i, j⟩ ⟨k, l⟩
    rw [LinearMap.toMatrix_apply, Matrix.stdBasis_eq_single, twoSided_apply]
    have hr : ∀ M : Matrix (Fin a) (Fin b) ℂ,
        (Matrix.stdBasis ℂ (Fin a) (Fin b)).repr M (i, j) = M i j := by
      intro M
      simp [Matrix.stdBasis]
    rw [hr]
    simp [Matrix.mul_apply, Matrix.single, Finset.sum_mul, ite_and]
  rw [h, Matrix.det_kronecker, Matrix.det_transpose]
  simp

section Skew

variable {a : ℕ} {ι : Type} [Fintype ι]

theorem star_coe (T : skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ)) :
    star (T : Matrix (Fin a) (Fin a) ℂ) = -(T : Matrix (Fin a) (Fin a) ℂ) :=
  skewAdjoint.mem_iff.mp T.2

theorem linearIndependent_skew
    (e : Module.Basis ι ℝ (skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ))) :
    LinearIndependent ℂ (fun i => (e i : Matrix (Fin a) (Fin a) ℂ)) := by
  have hR : ∀ g : ι → ℝ, ∑ i, (g i : ℂ) • (e i : Matrix (Fin a) (Fin a) ℂ) = 0 → ∀ i, g i = 0 := by
    intro g hg
    apply Fintype.linearIndependent_iff.mp e.linearIndependent g
    apply Subtype.ext
    simpa using hg
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h2 : ∑ i, (starRingEnd ℂ (g i)) • (e i : Matrix (Fin a) (Fin a) ℂ) = 0 := by
    have := congrArg star hg
    simp only [star_sum, star_smul, star_coe, smul_neg, Finset.sum_neg_distrib, star_zero,
      neg_eq_zero] at this
    exact this
  have hre : ∀ i, 2 * (g i).re = 0 := by
    apply hR
    have : ∀ i, ((2 * (g i).re : ℝ) : ℂ) = g i + starRingEnd ℂ (g i) := fun i =>
      (Complex.add_conj _).symm
    simp only [this, add_smul, Finset.sum_add_distrib, hg, h2, add_zero]
  have him : ∀ i, 2 * (g i).im = 0 := by
    apply hR
    have : ∀ i, ((2 * (g i).im : ℝ) : ℂ) = (-Complex.I) * (g i - starRingEnd ℂ (g i)) := by
      intro i
      rw [Complex.sub_conj]
      have := Complex.I_mul_I
      linear_combination ((2 * (g i).im : ℝ) : ℂ) * this
    simp only [this, mul_smul, ← Finset.smul_sum, sub_smul, Finset.sum_sub_distrib, hg, h2,
      sub_zero, smul_zero]
  intro i
  apply Complex.ext
  · have := hre i
    simpa using this
  · have := him i
    simpa using this

theorem span_skew
    (e : Module.Basis ι ℝ (skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ))) :
    ⊤ ≤ Submodule.span ℂ (Set.range fun i => (e i : Matrix (Fin a) (Fin a) ℂ)) := by
  have hS : ∀ T : Matrix (Fin a) (Fin a) ℂ, star T = -T →
      T ∈ Submodule.span ℂ (Set.range fun i => (e i : Matrix (Fin a) (Fin a) ℂ)) := by
    intro T hT
    have h := congrArg Subtype.val (e.sum_repr ⟨T, skewAdjoint.mem_iff.mpr hT⟩)
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
    rw [← h]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  intro T _
  have h1 := hS (T - star T) (by simp)
  have h2 := hS (Complex.I • (T + star T)) (by simp [star_smul, add_comm])
  have : T = (1 / 2 : ℂ) • ((T - star T) + (-Complex.I) • (Complex.I • (T + star T))) := by
    rw [smul_smul]
    simp only [neg_mul, Complex.I_mul_I, neg_neg, one_smul]
    module
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ h1 (Submodule.smul_mem _ _ h2))

theorem det_skew_eq
    (L : skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ) →ₗ[ℝ]
      skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ))
    (F : Matrix (Fin a) (Fin a) ℂ →ₗ[ℂ] Matrix (Fin a) (Fin a) ℂ)
    (h : ∀ T, (L T : Matrix (Fin a) (Fin a) ℂ) = F T) :
    ((LinearMap.det L : ℝ) : ℂ) = LinearMap.det F := by
  classical
  let e := Module.finBasis ℝ (skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ))
  let e' := Module.Basis.mk (linearIndependent_skew e) (span_skew e)
  have he : ∀ i, e' i = (e i : Matrix (Fin a) (Fin a) ℂ) := fun i => Module.Basis.mk_apply _ _ i
  rw [← LinearMap.det_toMatrix e, ← LinearMap.det_toMatrix e']
  have hm : LinearMap.toMatrix e' e' F = (LinearMap.toMatrix e e L).map Complex.ofRealHom := by
    ext i j
    rw [Matrix.map_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply, he, ← h]
    have h1 : (L (e j) : Matrix (Fin a) (Fin a) ℂ) =
        ∑ k, ((e.repr (L (e j)) k : ℝ) : ℂ) • e' k := by
      have h := congrArg Subtype.val (e.sum_repr (L (e j)))
      simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at h
      rw [← h]
      simp only [he, Complex.coe_smul]
    rw [h1, e'.repr_sum_self]
    rfl
  rw [hm]
  exact RingHom.map_det Complex.ofRealHom _

end Skew

theorem real_jacobians :
    (∀ (a b : ℕ) (A : Matrix (Fin a) (Fin a) ℂ) (B : Matrix (Fin b) (Fin b) ℂ) (L : Matrix (Fin a) (Fin b) ℂ →ₗ[ℝ] Matrix (Fin a) (Fin b) ℂ), (∀ T, L T = A * T * B) → LinearMap.det L = ‖A.det‖ ^ (2 * b) * ‖B.det‖ ^ (2 * a)) ∧ ∀ (a : ℕ) (A : Matrix (Fin a) (Fin a) ℂ) (L : skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ) →ₗ[ℝ] skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ)), (∀ T, ((L T : skewAdjoint.submodule ℝ (Matrix (Fin a) (Fin a) ℂ)) : Matrix (Fin a) (Fin a) ℂ) = A * (T : Matrix (Fin a) (Fin a) ℂ) * Aᴴ) → LinearMap.det L = ‖A.det‖ ^ (2 * a) := by
  refine ⟨fun a b A B L hL => ?_, fun a A L hL => ?_⟩
  · have : L = (twoSided A B).restrictScalars ℝ := LinearMap.ext hL
    rw [this, LinearMap.det_restrictScalars, Algebra.norm_complex_apply, det_twoSided,
      Complex.normSq_eq_norm_sq, norm_mul, norm_pow, norm_pow]
    ring
  · have h := det_skew_eq L (twoSided A Aᴴ) hL
    rw [det_twoSided, Matrix.det_conjTranspose, ← mul_pow] at h
    apply Complex.ofReal_injective
    rw [h, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, pow_mul]
    push_cast
    rfl

end GlobalTheory.TwoSidedJac
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubledFlagSumEqUnipotentDimAndLayerProd
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubledFlagSumEqUnipotentDimAndLayerProd
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory.DoubledFlag

theorem _root_.GlobalTheory.DoubledFlag.sum_range_double {M : Type} [AddCommMonoid M] (a : ℕ) (f : ℕ → M) :
    ∑ s ∈ range (2 * a + 1), f s = ∑ i : Fin a, (f i + f (2 * a - i)) + f a := by
  rw [show 2 * a + 1 = (a + 1) + a by ring, Finset.sum_range_add, Finset.sum_range_succ,
    Fin.sum_univ_eq_sum_range (fun i => f i + f (2 * a - i)), Finset.sum_add_distrib,
    ← Finset.sum_range_reflect (fun x => f (a + 1 + x)) a]
  have h : ∀ x ∈ range a, f (a + 1 + (a - 1 - x)) = f (2 * a - x) := fun x hx => by
    rw [Finset.mem_range] at hx; congr 1; omega
  rw [Finset.sum_congr rfl h]
  abel

theorem _root_.GlobalTheory.DoubledFlag.sum_eq_dimN_and_layerProd_eq : ∀ (n a : ℕ) (j : Fin a → ℕ) (D : ℕ → ℝ) (ν : ℕ → ℕ), (∀ i, 1 ≤ j i) → (∀ s, 0 < D s) → D 0 = 1 → ν 0 = 0 → (∀ i : Fin a, ν (i + 1) = ν i + j i) → 2 * ν a ≤ n → (∀ s, s ≤ a → D (2 * a + 1 - s) = D s ∧ ν (2 * a + 1 - s) + ν s = n) → ∑ s ∈ Finset.range (2 * a + 1), (ν (s + 1) - ν s) * ν s = _root_.GlobalTheory.FlagMeas.dimN n j ∧ _root_.GlobalTheory.Count.layerProd n 1 j (fun i : Fin a => (D (i + 1) / D i) ^ (-(1 : ℝ) / j i)) id = (∏ s ∈ Finset.range (2 * a + 1), D s ^ ν (s + 1) / D (s + 1) ^ ν s)⁻¹ := by
  intro n a j D ν hj hD hD0 hν0 hν hna hsym
  have hJ : ν a = ∑ i, j i := by
    have h1 : ∀ m, m ≤ a → ν m = ∑ i ∈ range m, if h : i < a then j ⟨i, h⟩ else 0 := by
      intro m hm
      induction m with
      | zero => simp [hν0]
      | succ m ih =>
        rw [Finset.sum_range_succ, ← ih (by omega), dite_eq_left (by omega)]
        exact hν ⟨m, by omega⟩
    rw [h1 a le_rfl, ← Fin.sum_univ_eq_sum_range (fun i => if h : i < a then j ⟨i, h⟩ else 0)]
    simp
  have hmid : ν (a + 1) + ν a = n := by
    have h := (hsym a le_rfl).2
    rwa [show 2 * a + 1 - a = a + 1 by omega] at h
  have hlow : ∀ i : Fin a, (ν (i + 1) - ν i) * ν i = j i * ν i := by
    intro i; rw [hν i, Nat.add_sub_cancel_left]
  have hhigh : ∀ i : Fin a, (ν (2 * a - i + 1) - ν (2 * a - i)) * ν (2 * a - i) + j i * ν (i + 1)
      = j i * n := by
    intro i
    have hi := i.isLt
    have h1 := (hsym i (by omega)).2
    have h2 := (hsym (i + 1) (by omega)).2
    have h3 := hν i
    rw [show 2 * a + 1 - (i : ℕ) = 2 * a - i + 1 by omega] at h1
    rw [show 2 * a + 1 - ((i : ℕ) + 1) = 2 * a - i by omega] at h2
    rw [show ν (2 * a - i + 1) - ν (2 * a - i) = j i by omega, ← mul_add, h2]
  have hsq : ν a * ν a = ∑ i, j i ^ 2 + 2 * ∑ i, ∑ k ∈ univ.filter (fun k => i < k), j i * j k := by
    have hsplit : ∀ i k : Fin a, j i * j k = ((if i < k then j i * j k else 0) +
        (if k < i then j k * j i else 0)) + (if i = k then j i ^ 2 else 0) := by
      intro i k
      rcases lt_trichotomy i k with h | h | h
      · simp [h, h.ne, not_lt.2 h.le]
      · subst h; simp [sq]
      · simp [h, h.ne', not_lt.2 h.le]; ring
    rw [hJ, Finset.sum_mul_sum]
    rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => hsplit i k]
    simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_filter, Finset.mem_univ, if_true]
    rw [Finset.sum_comm (f := fun i k => if k < i then j k * j i else 0)]
    ring
  refine ⟨?_, ?_⟩
  · rw [_root_.GlobalTheory.DoubledFlag.sum_range_double]
    have hF : ∑ i : Fin a, ((ν (i + 1) - ν i) * ν i + (ν (2 * a - i + 1) - ν (2 * a - i)) * ν (2 * a - i))
        + ∑ i, j i ^ 2 = n * ν a := by
      rw [← Finset.sum_add_distrib, hJ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have h := hhigh i
      rw [hν i] at h
      rw [hlow i]
      nlinarith
    unfold _root_.GlobalTheory.FlagMeas.dimN
    rw [← hJ]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 * ν a := ⟨n - 2 * ν a, by omega⟩
    rw [show ν (a + 1) - ν a = m by omega, show m + 2 * ν a - 2 * ν a = m by omega]
    nlinarith
  · obtain ⟨d, rfl⟩ : ∃ d : ℕ → ℝ, D = fun s => Real.exp (d s) :=
      ⟨fun s => Real.log (D s), funext fun s => (Real.exp_log (hD s)).symm⟩
    have hd0 : d 0 = 0 := by simpa using hD0
    have hdsym : ∀ s, s ≤ a → d (2 * a + 1 - s) = d s := fun s hs => by
      simpa using (hsym s hs).1
    have hc : ∀ i : Fin a, (Real.exp (d (i + 1)) / Real.exp (d i)) ^ (-(1 : ℝ) / j i)
        = Real.exp ((d i - d (i + 1)) / j i) := by
      intro i
      rw [← Real.exp_sub, ← Real.exp_mul]
      congr 1
      ring
    have htail : ∀ i : Fin a, ∑ k ∈ univ.filter (fun k => i < k), (j k : ℝ) = ν a - ν ((i : ℕ) + 1) := by
      intro i
      have hi := i.isLt
      have e : ∀ k : Fin a, (j k : ℝ) = ν ((k : ℕ) + 1) - ν k := fun k => by
        rw [hν k]; push_cast; ring
      simp only [e, Finset.sum_filter, Fin.lt_iff_val_lt_val]
      rw [Fin.sum_univ_eq_sum_range (fun x => if (i : ℕ) < x then (ν (x + 1) : ℝ) - ν x else 0) a,
        ← Finset.sum_filter,
        show (range a).filter (fun x => (i : ℕ) < x) = Ico ((i : ℕ) + 1) a by
          ext x; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega,
        Finset.sum_Ico_eq_sub _ (by omega), Finset.sum_range_sub (fun x => (ν x : ℝ)),
        Finset.sum_range_sub (fun x => (ν x : ℝ))]
      ring
    simp only [hc]
    unfold _root_.GlobalTheory.Count.layerProd
    simp only [id, ← Real.exp_nat_mul, ← Real.exp_sub, ← Real.exp_add, ← Real.exp_sum, ← Real.exp_neg,
      pow_one, mul_one]
    rw [Real.exp_eq_exp, ← hJ, _root_.GlobalTheory.DoubledFlag.sum_range_double, eq_neg_iff_add_eq_zero, ← add_assoc,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      Finset.sum_congr (s₁ := (univ : Finset (Fin a))) rfl (g := fun i : Fin a =>
        (2 * (ν ((i : ℕ) + 1) : ℝ) * d ((i : ℕ) + 1) - n * d ((i : ℕ) + 1)) - (2 * (ν i : ℝ) * d i - n * d i)) ?_,
      Fin.sum_univ_eq_sum_range (fun x => (2 * (ν (x + 1) : ℝ) * d (x + 1) - n * d (x + 1)) - (2 * (ν x : ℝ) * d x - n * d x)),
      Finset.sum_range_sub (fun x => 2 * (ν x : ℝ) * d x - n * d x)]
    · have hm : (ν (a + 1) : ℝ) = n - ν a := by rw [eq_sub_iff_add_eq]; exact_mod_cast hmid
      have hda : d (a + 1) = d a := by rw [← hdsym a le_rfl]; congr 1; omega
      rw [hm, hda, hν0, hd0]
      push_cast
      ring
    · intro i _
      have hi := i.isLt
      have hji : (j i : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by have := hj i; omega)
      have h1 := (hsym i (by omega)).2
      have h2 := (hsym (i + 1) (by omega)).2
      rw [show 2 * a + 1 - (i : ℕ) = 2 * a - i + 1 by omega] at h1
      rw [show 2 * a + 1 - ((i : ℕ) + 1) = 2 * a - i by omega] at h2
      have e1 : (ν (2 * a - i + 1) : ℝ) = n - ν i := by rw [eq_sub_iff_add_eq]; exact_mod_cast h1
      have e2 : (ν (2 * a - i) : ℝ) = n - ν ((i : ℕ) + 1) := by rw [eq_sub_iff_add_eq]; exact_mod_cast h2
      have e3 : (ν ((i : ℕ) + 1) : ℝ) = ν i + j i := by exact_mod_cast hν i
      have f1 : d (2 * a - i + 1) = d i := by rw [← hdsym i (by omega)]; congr 1; omega
      have f2 : d (2 * a - i) = d ((i : ℕ) + 1) := by rw [← hdsym (i + 1) (by omega)]; congr 1; omega
      rw [Finset.sum_congr rfl (g := fun k => 4 * (d i - d ((i : ℕ) + 1)) * (j k : ℝ))
          fun k _ => by push_cast; field_simp; ring, ← Finset.mul_sum, htail i, e1, e2, f1, f2, e3]
      push_cast [Nat.cast_sub hna]
      field_simp
      ring

end GlobalTheory.DoubledFlag
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DoubledFlagSumEqUnipotentDimAndLayerProdStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubledFlag_sum_eq_unipotentDim_and_layerProd : ∀ (n a : ℕ) (j : Fin a → ℕ) (D : ℕ → ℝ) (ν : ℕ → ℕ), (∀ i, 1 ≤ j i) → (∀ s, 0 < D s) → D 0 = 1 → ν 0 = 0 → (∀ i : Fin a, ν (i + 1) = ν i + j i) → 2 * ν a ≤ n → (∀ s, s ≤ a → D (2 * a + 1 - s) = D s ∧ ν (2 * a + 1 - s) + ν s = n) → ∑ s ∈ Finset.range (2 * a + 1), (ν (s + 1) - ν s) * ν s = dimN n j ∧ layerProd n 1 j (fun i : Fin a => (D (i + 1) / D i) ^ (-(1 : ℝ) / j i)) id = (∏ s ∈ Finset.range (2 * a + 1), D s ^ ν (s + 1) / D (s + 1) ^ ν s)⁻¹ := by
  first | exact @GlobalTheory.DoubledFlag.sum_eq_dimN_and_layerProd_eq | exact GlobalTheory.DoubledFlag.sum_eq_dimN_and_layerProd_eq | (intros; apply GlobalTheory.DoubledFlag.sum_eq_dimN_and_layerProd_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOperatorNormFinalArithmeticLe
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOperatorNormFinalArithmeticLe
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp

theorem absArith_const (r : ℕ) (hr : 1 ≤ r) :
    (4 * r : ℝ) ^ (11 * r ^ 2) * ((r + 1) * 24) * 4 ^ (24 * r ^ 3 + 1) * (r : ℝ) ^ (2 * r) *
      Real.exp 1 ^ (r * (r + 2)) ≤ (4 * r : ℝ) ^ (44 * r ^ 3) := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h4 : (4 : ℝ) ≤ 4 * r := by linarith
  have h1 : ((r : ℝ) + 1) * 24 ≤ (4 * r : ℝ) ^ 3 := by
    have : (r : ℝ) ≤ (r : ℝ) ^ 3 := le_self_pow₀ hr' (by norm_num)
    nlinarith
  have he : Real.exp 1 ≤ 4 * r := by
    have := Real.exp_one_lt_d9
    linarith
  have hexp : 11 * r ^ 2 + 3 + (24 * r ^ 3 + 1) + 2 * r + r * (r + 2) ≤ 44 * r ^ 3 := by
    have a1 : r ≤ r ^ 3 := Nat.le_self_pow (by norm_num) r
    have a2 : r ^ 2 ≤ r ^ 3 := Nat.pow_le_pow_right hr (by norm_num)
    nlinarith
  calc _ ≤ (4 * r : ℝ) ^ (11 * r ^ 2) * (4 * r : ℝ) ^ 3 * (4 * r : ℝ) ^ (24 * r ^ 3 + 1) *
        (4 * r : ℝ) ^ (2 * r) * (4 * r : ℝ) ^ (r * (r + 2)) := by
        gcongr
        linarith
    _ = (4 * r : ℝ) ^ (11 * r ^ 2 + 3 + (24 * r ^ 3 + 1) + 2 * r + r * (r + 2)) := by
        simp only [pow_add]
    _ ≤ _ := pow_le_pow_right₀ (by linarith) hexp

theorem absArith_shift (r m : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m) :
    (Real.pi * Real.exp 1 / m) ^ (r * m) * 4 ^ m * (2 ^ r) ^ m ≤
      Real.exp 1 ^ (r * (r + 2)) *
        (8 * Real.pi * Real.exp 1 / ((m + r + 2 : ℕ) : ℝ)) ^ (r * m) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hk' : (0 : ℝ) < ((m + r + 2 : ℕ) : ℝ) := by positivity
  have hpe : 0 < Real.pi * Real.exp 1 := by positivity
  have h1 : (((m + r + 2 : ℕ) : ℝ) / m) ^ m ≤ Real.exp 1 ^ (r + 2) := by
    have h2 : ((m + r + 2 : ℕ) : ℝ) / m ≤ Real.exp (((r + 2 : ℕ) : ℝ) / m) := by
      have := Real.add_one_le_exp (((r + 2 : ℕ) : ℝ) / m)
      refine le_trans (le_of_eq ?_) this
      push_cast
      field_simp
      ring
    calc _ ≤ Real.exp (((r + 2 : ℕ) : ℝ) / m) ^ m := by gcongr
      _ = Real.exp 1 ^ (r + 2) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
        congr 1
        field_simp
  have h3 : (((m + r + 2 : ℕ) : ℝ) / m) ^ (r * m) ≤ Real.exp 1 ^ (r * (r + 2)) := by
    rw [mul_comm r m, mul_comm r (r + 2), pow_mul, pow_mul]
    gcongr
  have h4 : (4 : ℝ) ^ m ≤ 4 ^ (r * m) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_mul_of_pos_left m hr)
  calc _ ≤ (Real.pi * Real.exp 1 / m) ^ (r * m) * 4 ^ (r * m) * (2 ^ r) ^ m := by gcongr
    _ = (((m + r + 2 : ℕ) : ℝ) / m) ^ (r * m) *
        (8 * Real.pi * Real.exp 1 / ((m + r + 2 : ℕ) : ℝ)) ^ (r * m) := by
        rw [← pow_mul, ← mul_pow, ← mul_pow, ← mul_pow]
        congr 1
        field_simp
        ring
    _ ≤ _ := by gcongr

theorem absArith : ∀ (k r : ℕ) (H₁ De D : ℝ), 1 ≤ r → 2 * r + 6 ≤ k → 1 ≤ H₁ → 1 ≤ De → 0 < D → ((4 * r : ℝ) ^ (11 * r ^ 2) * De ^ (12 * r ^ 2) * (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) * 4 ^ (k - 2 - r) * ((r + 1) * 4 ^ (24 * r ^ 3 + 1))) * 24 * (r : ℝ) ^ (2 * r) * H₁ ^ (24 * r ^ 3) * De ^ (2 * r) * (2 ^ r / D) ^ (k - 2 - r) ≤ absBd k r H₁ De D := by
  intro k r H₁ De D hr hk hH hDe hD
  obtain ⟨m, rfl⟩ : ∃ m, k = m + r + 2 := ⟨k - 2 - r, by omega⟩
  have hm : 1 ≤ m := by omega
  have hmk : m + r + 2 - 2 - r = m := by omega
  unfold absBd
  rw [hmk]
  have hA := absArith_const r hr
  have hB := absArith_shift r m hr hm
  have hC : De ^ (12 * r ^ 2) * De ^ (2 * r) ≤ De ^ (14 * r ^ 2) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hDe (by nlinarith)
  have hH0 : 0 ≤ H₁ := by linarith
  have hDe0 : 0 ≤ De := by linarith
  calc _ = ((4 * r : ℝ) ^ (11 * r ^ 2) * ((r + 1) * 24) * 4 ^ (24 * r ^ 3 + 1) * (r : ℝ) ^ (2 * r)) *
        ((Real.pi * Real.exp 1 / m) ^ (r * m) * 4 ^ m * (2 ^ r) ^ m) *
        (De ^ (12 * r ^ 2) * De ^ (2 * r)) * H₁ ^ (24 * r ^ 3) * (D ^ m)⁻¹ := by
        rw [div_pow (2 ^ r : ℝ) D m, div_eq_mul_inv ((2 ^ r : ℝ) ^ m)]
        ring
    _ ≤ ((4 * r : ℝ) ^ (11 * r ^ 2) * ((r + 1) * 24) * 4 ^ (24 * r ^ 3 + 1) * (r : ℝ) ^ (2 * r)) *
        (Real.exp 1 ^ (r * (r + 2)) *
          (8 * Real.pi * Real.exp 1 / ((m + r + 2 : ℕ) : ℝ)) ^ (r * m)) *
        De ^ (14 * r ^ 2) * H₁ ^ (24 * r ^ 3) * (D ^ m)⁻¹ := by gcongr
    _ = ((4 * r : ℝ) ^ (11 * r ^ 2) * ((r + 1) * 24) * 4 ^ (24 * r ^ 3 + 1) * (r : ℝ) ^ (2 * r) *
        Real.exp 1 ^ (r * (r + 2))) * H₁ ^ (24 * r ^ 3) * De ^ (14 * r ^ 2) *
          (8 * Real.pi * Real.exp 1 / ((m + r + 2 : ℕ) : ℝ)) ^ (r * m) * (D ^ m)⁻¹ := by
        ac_rfl
    _ ≤ _ := by gcongr

end GlobalTheory.Amp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOperatorNormFinalArithmeticLeStatement
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitudeOperatorNorm_finalArithmetic_le : ∀ (k r : ℕ) (H₁ De D : ℝ), 1 ≤ r → 2 * r + 6 ≤ k → 1 ≤ H₁ → 1 ≤ De → 0 < D → ((4 * r : ℝ) ^ (11 * r ^ 2) * De ^ (12 * r ^ 2) * (Real.pi * Real.exp 1 / ((k - 2 - r : ℕ) : ℝ)) ^ (r * (k - 2 - r)) * 4 ^ (k - 2 - r) * ((r + 1) * 4 ^ (24 * r ^ 3 + 1))) * 24 * (r : ℝ) ^ (2 * r) * H₁ ^ (24 * r ^ 3) * De ^ (2 * r) * (2 ^ r / D) ^ (k - 2 - r) ≤ absBd k r H₁ De D := by
  first | exact @GlobalTheory.Amp.absArith | exact GlobalTheory.Amp.absArith | (intros; apply GlobalTheory.Amp.absArith <;> assumption)
end
end
