module

public import Formalism.LocalToGlobal.IndefiniteReal.CxPassSk
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.StdCharExists
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FiniteAdeleSndAlgebraMap
public import ReciprocityTheory.AdeleApproximation.AdeleIntA

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem
section -- merged from Formalism.LocalToGlobal.IndefiniteReal.PHeisThA
noncomputable section

open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Heis
  IsDedekindDomain NumberField Formalism.IndefR.PHeisFC
open scoped TensorProduct ContDiff

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Formalism.IndefR.PHeisTh

section Tens

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] [FiniteDimensional F E]

theorem repr_snd (z : AF F ⊗[F] E) (k : Fin (Module.finrank F E)) :
    (Algebra.TensorProduct.basis (Af F) (Module.finBasis F E)).repr
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) k = (cE F E z k).2 := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.zero_apply]; rfl
  | tmul a e =>
    show _ = ((bA F E).equivFun (a ⊗ₜ[F] e) k).2
    rw [Algebra.TensorProduct.map_tmul, Module.Basis.equivFun_apply, Algebra.TensorProduct.basis_repr_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
    simp [sndA]
    rfl
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy, Pi.add_apply]; rfl

theorem repr_fst (z : AF F ⊗[F] E) (k : Fin (Module.finrank F E)) :
    (Algebra.TensorProduct.basis (Ainf F) (Module.finBasis F E)).repr
      (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) z) k = (cE F E z k).1 := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.zero_apply]; rfl
  | tmul a e =>
    show _ = ((bA F E).equivFun (a ⊗ₜ[F] e) k).1
    rw [Algebra.TensorProduct.map_tmul, Module.Basis.equivFun_apply, Algebra.TensorProduct.basis_repr_tmul,
      Algebra.TensorProduct.basis_repr_tmul]
    simp [fstA]
    rfl
  | add x y hx hy => simp only [map_add (f := _), Finsupp.add_apply, hx, hy, Pi.add_apply]; rfl

theorem trace_tmul (e : E) :
    Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  have h : Algebra.lmul (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) =
      (Algebra.lmul F E e).baseChange (AF F) := by
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a m => simp [LinearMap.baseChange_tmul, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
  rw [Algebra.trace_apply, h, LinearMap.trace_baseChange]
  rfl

end Tens

section Sympl

variable {D : D7}

theorem cA_algebraMap (c : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) c) = algebraMap (AF D.host.F) (AE D) c := by
  show (Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig) (c ⊗ₜ[D.host.F] (1 : D.host.E)) =
    c ⊗ₜ[D.host.F] (1 : D.host.E)
  rw [Algebra.TensorProduct.map_tmul, map_one]
  rfl

theorem cA_smul (c : AF D.host.F) (z : AE D) : cA D (c • z) = c • cA D z := by
  rw [Algebra.smul_def, map_mul, cA_algebraMap, ← Algebra.smul_def]

end Sympl

end Formalism.IndefR.PHeisTh

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (S T : HSp D)

theorem hO_add_left (x x' y : WO S T) : hO S T (x + x') y = hO S T x y + hO S T x' y := by
  unfold hO
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem hO_add_right (x y y' : WO S T) : hO S T x (y + y') = hO S T x y + hO S T x y' := by
  unfold hO
  simp only [Matrix.add_apply, map_add (f := _), mul_add, add_mul, Finset.sum_add_distrib]

theorem symplO_add_left (x x' y : WO S T) : symplO S T (x + x') y = symplO S T x y + symplO S T x' y := by
  unfold symplO
  rw [hO_add_left, mul_add, map_add (f := _)]

theorem symplO_add_right (x y y' : WO S T) : symplO S T x (y + y') = symplO S T x y + symplO S T x y' := by
  unfold symplO
  rw [hO_add_right, mul_add, map_add (f := _)]

theorem symplO_zero_left (y : WO S T) : symplO S T 0 y = 0 := by
  have h := symplO_add_left S T 0 0 y
  rw [add_zero] at h
  linear_combination -1 * h

theorem symplO_zero_right (x : WO S T) : symplO S T x 0 = 0 := by
  have h := symplO_add_right S T x 0 0
  rw [add_zero] at h
  linear_combination -1 * h

theorem symplO_neg_left (x y : WO S T) : symplO S T (-x) y = -symplO S T x y := by
  have h := symplO_add_left S T x (-x) y
  have h0 : x + -x = 0 := by simp
  rw [h0, symplO_zero_left] at h
  linear_combination -1 * h

theorem symplO_neg_right (x y : WO S T) : symplO S T x (-y) = -symplO S T x y := by
  have h := symplO_add_right S T x y (-y)
  have h0 : y + -y = 0 := by simp
  rw [h0, symplO_zero_right] at h
  linear_combination -1 * h

abbrev MO : Type := Matrix (Fin T.rank) (Fin S.rank) (AE D)

def hOM (x y : MO S T) : Matrix (Fin S.rank) (Fin S.rank) (AE D) :=
  HMul.hMul (HMul.hMul (HMul.hMul (Brg.GI S) (y.map (cA D))ᵀ) (Brg.GG T)) x

theorem hO_eq_trace (x y : MO S T) : hO S T x y = (hOM S T x y).trace := by
  unfold hO hOM
  simp only [Brg.GI, Brg.GG, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.map_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  conv_lhs => arg 2; ext d; rw [Finset.sum_comm]

theorem cA_trace {k : ℕ} (M : Matrix (Fin k) (Fin k) (AE D)) : cA D M.trace = ((M.map (cA D))ᵀ).trace := by
  rw [Matrix.trace_transpose]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem hO_swap (x y : MO S T) : hO S T y x = cA D (hO S T x y) := by
  have e0 : (y.map (cA D)).map (cA D) = y := by ext i j; simp [cA_cA]
  have e2 : ((hOM S T x y).map (cA D))ᵀ =
      HMul.hMul (HMul.hMul (HMul.hMul (x.map (cA D))ᵀ (Brg.GG T)) y) (Brg.GI S) := by
    unfold hOM
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_mul, Brg.GI_herm, Brg.GG_herm, Matrix.transpose_map, e0, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
  rw [hO_eq_trace, hO_eq_trace, cA_trace, e2, Matrix.trace_mul_comm]
  unfold hOM
  simp only [Matrix.mul_assoc]

theorem symplO_swap (x y : WO S T) : symplO S T y x = -symplO S T x y := by
  unfold symplO
  rw [hO_swap S T x y]
  have e : incA D D.host.xi0 * cA D (hO S T x y) = cA D (cA D (incA D D.host.xi0) * hO S T x y) := by
    rw [map_mul, cA_cA]
  rw [e, Brg.trace_cA, Brg.cA_inc, Brg.star_purely_imaginary_eq_neg, map_neg, neg_mul, map_neg]

theorem symplOH_add_left (x x' y : WO S T) :
    symplOH S T (x + x') y = symplOH S T x y + symplOH S T x' y := by
  unfold symplOH
  rw [symplO_add_left, mul_add]

theorem symplOH_add_right (x y y' : WO S T) :
    symplOH S T x (y + y') = symplOH S T x y + symplOH S T x y' := by
  unfold symplOH
  rw [symplO_add_right, mul_add]

theorem symplOH_swap (x y : WO S T) : symplOH S T y x = -symplOH S T x y := by
  unfold symplOH
  rw [symplO_swap, mul_neg]

theorem symplOH_two (x y : WO S T) : symplOH S T x y + symplOH S T x y = symplO S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add (f := _)]
  norm_num

theorem incA_eq_tmul (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

theorem trace_incA (e : D.host.E) :
    Algebra.trace (AF D.host.F) (AE D) (incA D e) = algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E e) := by
  rw [incA_eq_tmul]
  exact Formalism.IndefR.PHeisTh.trace_tmul _

end Formalism.IndefR.Fin

end
end

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.NormNatCastLtOne
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain Topology Filter

namespace Formalism.IndefR.Fin.U1

variable {F : Type} [Field F] [NumberField F]

theorem norm_le_one_iff_int (v : HeightOneSpectrum (𝓞 F)) (x : v.adicCompletion F) :
    ‖x‖ ≤ 1 ↔ x ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  exact Valued.toNormedField.norm_le_one_iff

theorem norm_nat_le_one (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) : ‖(m : v.adicCompletion F)‖ ≤ 1 := (norm_le_one_iff_int v _).mpr (natCast_mem _ m)

theorem nat_ne_zero_fin (v : HeightOneSpectrum (𝓞 F)) {m : ℕ} (hm : m ≠ 0) : (m : v.adicCompletion F) ≠ 0 := by
  rw [← map_natCast (algebraMap F (v.adicCompletion F)) m]
  exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr hm)

theorem natCast_apply' (N : ℕ) (v : HeightOneSpectrum (𝓞 F)) : (N : Af F) v = (N : v.adicCompletion F) := by
  first
  | rfl
  | simp

theorem natCast_mul_apply' (N : ℕ) (z : Af F) (v : HeightOneSpectrum (𝓞 F)) :
    ((N : Af F) * z) v = (N : v.adicCompletion F) * z v := by
  rw [← natCast_apply' N v]
  rfl

theorem norm_natCast_lt_one' (v : HeightOneSpectrum (𝓞 F)) (c : ℕ) (hc : Ideal.absNorm v.asIdeal ∣ c) :
    ‖(c : v.adicCompletion F)‖ < 1 := by
  have hmem : ((c : ℕ) : 𝓞 F) ∈ v.asIdeal := by
    obtain ⟨k, hk⟩ := hc
    rw [hk, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem v.asIdeal)
  rw [Valued.toNormedField.norm_lt_one_iff]
  have h1 : ((c : v.adicCompletion F)) = ((algebraMap (𝓞 F) F (c : 𝓞 F) : F) : v.adicCompletion F) := by
    rw [map_natCast]
    first
    | exact (map_natCast (algebraMap F (v.adicCompletion F)) c).symm
    | norm_cast
    | rfl
  rw [h1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact (v.intValuation_lt_one_iff_mem _).mpr hmem

theorem finNhd (U : Set (Af F)) (hU : U ∈ 𝓝 (0 : Af F)) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ z : Af F, (∀ v, z v ∈ v.adicCompletionIntegers F) → (N : Af F) * z ∈ U := by
  classical
  have hAopen : ∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen ((v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun _ => Valued.isOpen_valuationSubring _
  have hU' : U ∈ Filter.map (RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite)
      (𝓝 (fun v => ⟨0, zero_mem (v.adicCompletionIntegers F)⟩)) := by
    rw [← RestrictedProduct.nhds_eq_map_structureMap hAopen]
    exact hU
  have hU2 : (RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite) ⁻¹'
      (U : Set (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
        (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite)) ∈
      𝓝 (fun v : HeightOneSpectrum (𝓞 F) => (⟨0, zero_mem (v.adicCompletionIntegers F)⟩ :
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)))) := hU'
  rw [nhds_pi, Filter.mem_pi] at hU2
  obtain ⟨I, hI, t, ht, hIt⟩ := hU2
  have hε : ∀ v : HeightOneSpectrum (𝓞 F), ∃ ε > (0 : ℝ),
      ∀ y : (v.adicCompletionIntegers F : Set (v.adicCompletion F)),
        ‖(y : v.adicCompletion F)‖ < ε → y ∈ t v := by
    intro v
    obtain ⟨u, hu, hut⟩ := (mem_nhds_subtype _ _ _).1 (ht v)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hu
    refine ⟨ε, hε, fun y hy => hut (hball ?_)⟩
    simpa [Metric.mem_ball, dist_zero_right] using hy
  choose ε hεpos hεt using hε
  set c : ℕ := ∏ v ∈ hI.toFinset, Ideal.absNorm v.asIdeal with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef, Finset.prod_ne_zero_iff]
    intro v _
    exact (lt_trans zero_lt_one (HeightOneSpectrum.one_lt_absNorm v)).ne'
  have hcv : ∀ v ∈ I, ‖(c : v.adicCompletion F)‖ < 1 := fun v hv =>
    norm_natCast_lt_one' v c (Finset.dvd_prod_of_mem _ (hI.mem_toFinset.2 hv))
  have hev : ∀ v ∈ I, ∀ᶠ k in atTop, ‖(c : v.adicCompletion F)‖ ^ k < ε v := fun v hv =>
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) (hcv v hv)).eventually
      (Iio_mem_nhds (hεpos v))
  obtain ⟨k, hk⟩ := ((Filter.eventually_all_finite hI).2 hev).exists
  refine ⟨c ^ k, Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hc0), fun z hz => ?_⟩
  have hmem : ∀ v, (((c ^ k : ℕ) : FiniteAdeleRing (𝓞 F) F) * z) v ∈
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    intro v
    rw [natCast_mul_apply']
    exact mul_mem (natCast_mem _ _) (hz v)
  have hx : ((c ^ k : ℕ) : FiniteAdeleRing (𝓞 F) F) * z = RestrictedProduct.structureMap
      (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) cofinite
      (fun v => ⟨_, hmem v⟩) := by
    ext v
    rfl
  rw [hx]
  apply hIt
  intro v hv
  apply hεt
  show ‖(((c ^ k : ℕ) : FiniteAdeleRing (𝓞 F) F) * z) v‖ < ε v
  rw [natCast_mul_apply', norm_mul, Nat.cast_pow, norm_pow]
  have hz1 : ‖z v‖ ≤ 1 := (norm_le_one_iff_int v _).2 (hz v)
  calc ‖(c : v.adicCompletion F)‖ ^ k * ‖z v‖ ≤ ‖(c : v.adicCompletion F)‖ ^ k * 1 :=
        mul_le_mul_of_nonneg_left hz1 (pow_nonneg (norm_nonneg _) _)
    _ < ε v := by rw [mul_one]; exact hk v hv

theorem int_of_le (y : Af F) (N M : ℕ) (hN : N ≠ 0)
    (hy : ∀ v, ‖y v‖ ≤ ‖(N : v.adicCompletion F)‖ * ‖(M : v.adicCompletion F)‖) :
    ∃ z : Af F, (∀ v, z v ∈ v.adicCompletionIntegers F) ∧ y = (N : Af F) * z := by
  refine ⟨algebraMap F (Af F) ((N : F)⁻¹) * y, fun v => ?_, ?_⟩
  · rw [← norm_le_one_iff_int]
    show ‖algebraMap F (v.adicCompletion F) ((N : F)⁻¹) * y v‖ ≤ 1
    have hN0 : 0 < ‖(N : v.adicCompletion F)‖ := norm_pos_iff.2 (nat_ne_zero_fin v hN)
    rw [map_inv₀, map_natCast, norm_mul, norm_inv, inv_mul_le_iff₀ hN0, mul_one]
    calc ‖y v‖ ≤ ‖(N : v.adicCompletion F)‖ * ‖(M : v.adicCompletion F)‖ := hy v
      _ ≤ ‖(N : v.adicCompletion F)‖ * 1 := mul_le_mul_of_nonneg_left (norm_nat_le_one v M) hN0.le
      _ = ‖(N : v.adicCompletion F)‖ := mul_one _
  · rw [← mul_assoc, ← map_natCast (algebraMap F (Af F)) N, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.2 hN), map_one, one_mul]

end Formalism.IndefR.Fin.U1

end
end
