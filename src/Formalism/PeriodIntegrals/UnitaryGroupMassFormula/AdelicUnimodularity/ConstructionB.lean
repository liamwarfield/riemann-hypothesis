module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.KCountable
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.CartierFrobeniusFormLocal
public import Lemmata.NatMulIsIntegral.ExistsNatMulIsIntegral

@[expose] public section

section -- merged from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.ExistsNatVec
noncomputable section

namespace PI.WAU.B

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.UG Matrix
open scoped TensorProduct

theorem exists_gen {E : Type} [Field E] [NumberField E] {n : ℕ}
    (Lb : Submodule (𝓞 E) (Fin n → E)) (hfin : Module.Finite (𝓞 E) Lb) :
    ∃ (k : ℕ) (m : Fin k → Fin n → E), (∀ i, m i ∈ Lb) ∧
      (∀ l ∈ Lb, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i) := by
  have : Module.Finite ℤ Lb := Module.Finite.trans (𝓞 E) Lb
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := ℤ) (M := Lb)
  refine ⟨k, fun i => (s i : Fin n → E), fun i => (s i).2, fun l hl => ?_⟩
  have hmem : (⟨l, hl⟩ : Lb) ∈ Submodule.span ℤ (Set.range s) := hs ▸ Submodule.mem_top
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hmem
  refine ⟨z, ?_⟩
  have h2 := congrArg Subtype.val hz
  simp only [Submodule.coe_sum] at h2
  exact h2.symm

theorem exists_nat_E {E : Type} [Field E] [NumberField E] (e : E) :
    ∃ c : ℕ, 0 < c ∧ ∃ t : 𝓞 E, (c : E) * e = algebraMap (𝓞 E) E t := by
  obtain ⟨⟨a, ⟨d, hd⟩⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 E)) e
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.absNorm_mem (Ideal.span {d}))
  refine ⟨Ideal.absNorm (Ideal.span {d}), ?_, c * a, ?_⟩
  · rw [Nat.pos_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hd0
  · have h1 : ((Ideal.absNorm (Ideal.span {d}) : ℕ) : E) =
        algebraMap (𝓞 E) E c * algebraMap (𝓞 E) E d := by
      rw [← map_mul, hc, map_natCast]
    simp only at h
    rw [h1, map_mul, ← h]
    ring

theorem common_nat {ι : Type} [Fintype ι] (P : ι → ℕ → Prop)
    (hP : ∀ i N M, P i N → P i (N * M)) (h : ∀ i, ∃ N, 0 < N ∧ P i N) :
    ∃ N, 0 < N ∧ ∀ i, P i N := by
  classical
  choose f hf0 hf using h
  refine ⟨∏ i, f i, Finset.prod_pos fun i _ => hf0 i, fun i => ?_⟩
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem f (Finset.mem_univ i)
  rw [hk]
  exact hP i _ _ (hf i)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

abbrev incA (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (a : Af F) :
    E ⊗[F] Af F :=
  (Algebra.TensorProduct.includeRight : Af F →ₐ[F] E ⊗[F] Af F) a

abbrev ivec (x : Fin n → E) : Fin n → E ⊗[F] Af F := fun i => inclE (F := F) (Af F) (x i)

theorem left_mem (t : 𝓞 E) : ((algebraMap (𝓞 E) E t) ⊗ₜ[F] (1 : Af F)) ∈ IntAf F E :=
  Subring.subset_closure (Or.inl ⟨⟨algebraMap (𝓞 E) E t, ⟨t, rfl⟩⟩, rfl⟩)

theorem incA_mem {a : Af F} (ha : a ∈ intAd F) : incA F E a ∈ IntAf F E :=
  Subring.subset_closure (Or.inr ⟨⟨a, ha⟩, rfl⟩)

theorem ivec_mem {L : Submodule (𝓞 E) (Fin n → E)} {x : Fin n → E} (hx : x ∈ L) :
    ivec (F := F) x ∈ lamAf (F := F) L :=
  Submodule.subset_span ⟨⟨x, hx⟩, rfl⟩

theorem smulO_mem {L : Submodule (𝓞 E) (Fin n → E)} {o : E ⊗[F] Af F} (ho : o ∈ IntAf F E)
    {w : Fin n → E ⊗[F] Af F} (hw : w ∈ lamAf (F := F) L) : o • w ∈ lamAf (F := F) L :=
  Submodule.smul_mem _ (⟨o, ho⟩ : IntAf F E) hw

theorem nsmul_lam {L : Submodule (𝓞 E) (Fin n → E)} {w : Fin n → E ⊗[F] Af F} {N : ℕ}
    (hw : N • w ∈ lamAf (F := F) L) (M : ℕ) : (N * M) • w ∈ lamAf (F := F) L := by
  rw [mul_comm, mul_smul]
  exact nsmul_mem hw M

def Tset {k : ℕ} (m : Fin k → Fin n → E) : Set (Fin n → E ⊗[F] Af F) :=
  {w | ∃ a : Fin k → Af F, (∀ j, a j ∈ intAd F) ∧ w = ∑ j, incA F E (a j) • ivec (F := F) (m j)}

section T

variable {k : ℕ} {m : Fin k → Fin n → E}

theorem T_zero : (0 : Fin n → E ⊗[F] Af F) ∈ Tset (F := F) m :=
  ⟨0, fun _ => zero_mem _, by simp⟩

theorem T_add {w w' : Fin n → E ⊗[F] Af F} (hw : w ∈ Tset (F := F) m) (hw' : w' ∈ Tset (F := F) m) :
    w + w' ∈ Tset (F := F) m := by
  obtain ⟨a, ha, rfl⟩ := hw
  obtain ⟨a', ha', rfl⟩ := hw'
  refine ⟨a + a', fun j => add_mem (ha j) (ha' j), ?_⟩
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.add_apply, map_add (f := _), add_smul]

theorem T_neg {w : Fin n → E ⊗[F] Af F} (hw : w ∈ Tset (F := F) m) : -w ∈ Tset (F := F) m := by
  obtain ⟨a, ha, rfl⟩ := hw
  refine ⟨-a, fun j => neg_mem (ha j), ?_⟩
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.neg_apply, map_neg, neg_smul]

theorem T_smulA {b : Af F} (hb : b ∈ intAd F) {w : Fin n → E ⊗[F] Af F}
    (hw : w ∈ Tset (F := F) m) : incA F E b • w ∈ Tset (F := F) m := by
  obtain ⟨a, ha, rfl⟩ := hw
  refine ⟨fun j => b * a j, fun j => mul_mem hb (ha j), ?_⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [smul_smul]

theorem T_sum {ι : Type} (s : Finset ι) (f : ι → Fin n → E ⊗[F] Af F)
    (h : ∀ i ∈ s, f i ∈ Tset (F := F) m) : ∑ i ∈ s, f i ∈ Tset (F := F) m := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using T_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact T_add (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem ivec_zsum (z : Fin k → ℤ) :
    ivec (F := F) (∑ i, z i • m i) = ∑ i, incA F E (z i : Af F) • ivec (F := F) (m i) := by
  funext r
  set_option synthInstance.maxHeartbeats 100000 in
    simp [ivec, Finset.sum_apply, map_sum, map_zsmul, Int.cast_smul_eq_zsmul]

theorem T_gen {L : Submodule (𝓞 E) (Fin n → E)}
    (hgen : ∀ l ∈ L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i) {x : Fin n → E} (hx : x ∈ L) :
    ivec (F := F) x ∈ Tset (F := F) m := by
  obtain ⟨z, rfl⟩ := hgen x hx
  exact ⟨fun i => (z i : Af F), fun i => intCast_mem _ _, ivec_zsum z⟩

theorem left_smul_ivec (t : 𝓞 E) (x : Fin n → E) :
    ((algebraMap (𝓞 E) E t) ⊗ₜ[F] (1 : Af F)) • ivec (F := F) x = ivec (F := F) (t • x) := by
  funext r
  simp [ivec, inclE, Algebra.TensorProduct.tmul_mul_tmul, Algebra.smul_def]

theorem T_smul_left {L : Submodule (𝓞 E) (Fin n → E)} (hm : ∀ i, m i ∈ L)
    (hgen : ∀ l ∈ L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i) (t : 𝓞 E) {w : Fin n → E ⊗[F] Af F}
    (hw : w ∈ Tset (F := F) m) :
    ((algebraMap (𝓞 E) E t) ⊗ₜ[F] (1 : Af F)) • w ∈ Tset (F := F) m := by
  obtain ⟨a, ha, rfl⟩ := hw
  rw [Finset.smul_sum]
  refine T_sum _ _ fun j _ => ?_
  rw [smul_comm, left_smul_ivec]
  exact T_smulA (ha j) (T_gen hgen (L.smul_mem t (hm j)))

theorem T_smulO {L : Submodule (𝓞 E) (Fin n → E)} (hm : ∀ i, m i ∈ L)
    (hgen : ∀ l ∈ L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i) {o : E ⊗[F] Af F}
    (ho : o ∈ IntAf F E) : ∀ w ∈ Tset (F := F) m, o • w ∈ Tset (F := F) m := by
  unfold IntAf tensInt at ho
  induction ho using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨⟨s, hs⟩, rfl⟩ | ⟨⟨a, ha⟩, rfl⟩
    · obtain ⟨t, rfl⟩ := hs
      intro w hw
      exact T_smul_left hm hgen t hw
    · intro w hw
      exact T_smulA ha hw
  | zero => intro w _; rw [zero_smul]; exact T_zero
  | one => intro w hw; rwa [one_smul]
  | add x y _ _ hx hy => intro w hw; rw [add_smul]; exact T_add (hx w hw) (hy w hw)
  | neg x _ hx => intro w hw; rw [neg_smul]; exact T_neg (hx w hw)
  | mul x y _ _ hx hy => intro w hw; rw [mul_smul]; exact hx _ (hy w hw)

theorem lam_sub_alt {L : Submodule (𝓞 E) (Fin n → E)} (hm : ∀ i, m i ∈ L)
    (hgen : ∀ l ∈ L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i) {w : Fin n → E ⊗[F] Af F}
    (hw : w ∈ lamAf (F := F) L) : w ∈ Tset (F := F) m := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨⟨y, hy⟩, rfl⟩ := hx
    exact T_gen hgen hy
  | zero => exact T_zero
  | add x y _ _ hx hy => exact T_add hx hy
  | smul o x _ hx => exact T_smulO hm hgen o.2 x hx

theorem mulVec_lam {L : Submodule (𝓞 E) (Fin n → E)} (hm : ∀ i, m i ∈ L)
    (hgen : ∀ l ∈ L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i)
    (P : Matrix (Fin n) (Fin n) (E ⊗[F] Af F))
    (hP : ∀ j, P *ᵥ ivec (F := F) (m j) ∈ lamAf (F := F) L) {w : Fin n → E ⊗[F] Af F}
    (hw : w ∈ lamAf (F := F) L) : P *ᵥ w ∈ lamAf (F := F) L := by
  obtain ⟨a, ha, rfl⟩ := lam_sub_alt hm hgen hw
  rw [Matrix.mulVec_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [Matrix.mulVec_smul]
  exact smulO_mem (incA_mem (ha j)) (hP j)

end T

theorem exists_nat_R (r : E ⊗[F] Af F) : ∃ N : ℕ, 0 < N ∧ (N : E ⊗[F] Af F) * r ∈ IntAf F E := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by simp⟩
  | tmul e a =>
    obtain ⟨c, hc0, t, ht⟩ := exists_nat_E e
    obtain ⟨N, hN0, hN⟩ := exists_nat_adele a
    refine ⟨c * N, Nat.mul_pos hc0 hN0, ?_⟩
    have e1 : ((c * N : ℕ) : E ⊗[F] Af F) * (e ⊗ₜ[F] a) =
        ((algebraMap (𝓞 E) E t) ⊗ₜ[F] (1 : Af F)) * incA F E ((N : Af F) * a) := by
      calc ((c * N : ℕ) : E ⊗[F] Af F) * (e ⊗ₜ[F] a) = (c * N) • (e ⊗ₜ[F] a) :=
            (nsmul_eq_mul _ _).symm
        _ = (c • e) ⊗ₜ[F] (N • a) := by
            rw [← TensorProduct.smul_tmul', TensorProduct.tmul_smul, mul_smul]
        _ = ((c : E) * e) ⊗ₜ[F] ((N : Af F) * a) := by rw [nsmul_eq_mul, nsmul_eq_mul]
        _ = _ := by
            rw [ht]
            simp [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.includeRight_apply]
    rw [e1]
    exact mul_mem (left_mem t) (incA_mem (fun v => hN v))
  | add x y hx hy =>
    obtain ⟨N1, h1, hx⟩ := hx
    obtain ⟨N2, h2, hy⟩ := hy
    refine ⟨N2 * N1, Nat.mul_pos h2 h1, ?_⟩
    have e1 : ((N2 * N1 : ℕ) : E ⊗[F] Af F) * (x + y) =
        (N2 : E ⊗[F] Af F) * ((N1 : E ⊗[F] Af F) * x) +
          (N1 : E ⊗[F] Af F) * ((N2 : E ⊗[F] Af F) * y) := by
      push_cast; ring
    rw [e1]
    exact add_mem (mul_mem (natCast_mem _ _) hx) (mul_mem (natCast_mem _ _) hy)

theorem exists_nat_L {L : Submodule (𝓞 E) (Fin n → E)}
    {z : Fin n → E} (hz : z ∈ Submodule.span E (L : Set (Fin n → E))) :
    ∃ N : ℕ, 0 < N ∧ N • z ∈ L := by
  first | exact Bl.NatMulIsIntegral.goal1 .. | (apply Bl.NatMulIsIntegral.goal1 <;> assumption) | (intros; apply Bl.NatMulIsIntegral.goal1 <;> assumption)

theorem exists_nat_vec {L : Submodule (𝓞 E) (Fin n → E)}
    (hspan : Submodule.span E (L : Set (Fin n → E)) = ⊤) (w : Fin n → E ⊗[F] Af F) :
    ∃ N : ℕ, 0 < N ∧ N • w ∈ lamAf (F := F) L := by
  classical
  have hi : ∀ i, ∃ N, 0 < N ∧ N • ((w i) • (Pi.single i 1 : Fin n → E ⊗[F] Af F)) ∈
      lamAf (F := F) L := by
    intro i
    obtain ⟨A, hA0, hA⟩ := exists_nat_R (F := F) (E := E) (w i)
    obtain ⟨B, hB0, hB⟩ := exists_nat_L (L := L) (z := Pi.single i 1)
      (by rw [hspan]; exact Submodule.mem_top)
    refine ⟨A * B, Nat.mul_pos hA0 hB0, ?_⟩
    have e1 : ivec (F := F) (B • (Pi.single i 1 : Fin n → E)) =
        (B : E ⊗[F] Af F) • (Pi.single i 1 : Fin n → E ⊗[F] Af F) := by
      funext j
      by_cases h : j = i
      · subst h; simp [ivec]
      · simp [ivec, Pi.single_apply, h]
    have e2 : (A * B) • ((w i) • (Pi.single i 1 : Fin n → E ⊗[F] Af F)) =
        ((A : E ⊗[F] Af F) * w i) • ivec (F := F) (B • (Pi.single i 1 : Fin n → E)) := by
      rw [e1, smul_smul, ← Nat.cast_smul_eq_nsmul (E ⊗[F] Af F), smul_smul]
      congr 1
      push_cast; ring
    rw [e2]
    exact smulO_mem hA (ivec_mem hB)
  obtain ⟨N, hN0, hN⟩ := common_nat
    (fun i N => N • ((w i) • (Pi.single i 1 : Fin n → E ⊗[F] Af F)) ∈ lamAf (F := F) L)
    (fun i N M h => nsmul_lam h M) hi
  refine ⟨N, hN0, ?_⟩
  have ew : w = ∑ i, (w i) • (Pi.single i 1 : Fin n → E ⊗[F] Af F) := by
    funext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [ew, Finset.smul_sum]
  exact Submodule.sum_mem _ fun i _ => hN i

end PI.WAU.B
end
end

noncomputable section

namespace PI.WAU.B

open Formalism.MainNotions.S MeasureTheory NumberField IsDedekindDomain Formalism.UG Matrix PI.WAU.B
open scoped TensorProduct

theorem cover_of {G : Type} [Group G] (K : Set G) (P : G → Prop) {C : Type} [Countable C]
    (f : G → C) (hf : ∀ x y, P x → P y → f x = f y → y⁻¹ * x ∈ K) :
    ∃ s : Set G, s.Countable ∧ ∀ x, P x → ∃ y ∈ s, y⁻¹ * x ∈ K := by
  classical
  refine ⟨Set.range fun c : {c : C // ∃ x, P x ∧ f x = c} => c.2.choose, Set.countable_range _,
    fun x hx => ?_⟩
  let c : {c : C // ∃ x, P x ∧ f x = c} := ⟨f x, x, hx, rfl⟩
  obtain ⟨hP, hfc⟩ := c.2.choose_spec
  exact ⟨c.2.choose, ⟨c, rfl⟩, hf x _ hx hP hfc.symm⟩

theorem nsmul_cancel {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {N : ℕ}
    (hN : 0 < N) {v w : V} (h : N • v = N • w) : v = w := by
  have h' : (N : K) • v = (N : K) • w := by
    rw [Nat.cast_smul_eq_nsmul K, Nat.cast_smul_eq_nsmul K]
    exact h
  exact smul_right_injective V (Nat.cast_ne_zero.mpr hN.ne') h'

section

variable (I : AutInst) {k : ℕ} (m : Fin k → Fin I.n → I.E)

theorem fmat_inv_mul (y : I.Gf) : I.fmat y⁻¹ * I.fmat y = 1 := by
  rw [show I.fmat y⁻¹ * I.fmat y = I.fmat (y⁻¹ * y) from rfl, inv_mul_cancel]
  rfl

theorem fmat_mul_inv (y : I.Gf) : I.fmat y * I.fmat y⁻¹ = 1 := by
  rw [show I.fmat y * I.fmat y⁻¹ = I.fmat (y * y⁻¹) from rfl, mul_inv_cancel]
  rfl

def PN (N : ℕ) (x : I.Gf) : Prop :=
  0 < N ∧ ∀ j, N • (I.fmat x *ᵥ ivec (F := I.F) (m j)) ∈ I.Lf ∧
    N • (I.fmat x⁻¹ *ᵥ ivec (F := I.F) (m j)) ∈ I.Lf

def fN (N : ℕ) (x : I.Gf) : Fin k → Fin k → Bad I.F (N * N) → I.F := by
  classical
  exact fun j => if h : N • (I.fmat x *ᵥ ivec (F := I.F) (m j)) ∈ Tset (F := I.F) m then
    fun i => cls (N * N) (h.choose i) else fun _ _ => 0

theorem half (hm : ∀ i, m i ∈ I.L) (hgen : ∀ l ∈ I.L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i)
    {N : ℕ} {x y : I.Gf} (hx : PN I m N x) (hy : PN I m N y) (he : fN I m N x = fN I m N y)
    (j : Fin k) : (I.fmat y⁻¹ * I.fmat x) *ᵥ ivec (F := I.F) (m j) ∈ I.Lf := by
  classical
  obtain ⟨hN, hxj⟩ := hx
  obtain ⟨_, hyj⟩ := hy
  have hTx : N • (I.fmat x *ᵥ ivec (F := I.F) (m j)) ∈ Tset (F := I.F) m :=
    lam_sub_alt hm hgen (hxj j).1
  have hTy : N • (I.fmat y *ᵥ ivec (F := I.F) (m j)) ∈ Tset (F := I.F) m :=
    lam_sub_alt hm hgen (hyj j).1
  have hej := congrFun he j
  simp only [fN, dif_pos hTx, dif_pos hTy] at hej
  obtain ⟨haI, haE⟩ := hTx.choose_spec
  obtain ⟨ha'I, ha'E⟩ := hTy.choose_spec

  have hb : ∀ i, ∃ b : Af I.F, (∀ v, b v ∈ v.adicCompletionIntegers I.F) ∧
      hTx.choose i - hTy.choose i = ((N * N : ℕ) : Af I.F) * b := fun i =>
    cls_eq (Nat.mul_pos hN hN) (haI i) (ha'I i) (congrFun hej i)
  choose b hbI hbE using hb
  set w : Fin I.n → I.E ⊗[I.F] Af I.F := ∑ i, incA I.F I.E (b i) • ivec (F := I.F) (m i) with hwdef
  have hw : w ∈ I.Lf :=
    Submodule.sum_mem _ fun i _ => smulO_mem (incA_mem (hbI i)) (ivec_mem (hm i))
  have hdiff : N • (I.fmat x *ᵥ ivec (F := I.F) (m j) - I.fmat y *ᵥ ivec (F := I.F) (m j)) =
      N • (N • w) := by
    rw [smul_sub, haE, ha'E, ← Finset.sum_sub_distrib, hwdef, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul, ← map_sub, hbE i, map_mul, map_natCast, mul_smul, Nat.cast_smul_eq_nsmul,
      smul_smul]
  have hd : I.fmat x *ᵥ ivec (F := I.F) (m j) - I.fmat y *ᵥ ivec (F := I.F) (m j) = N • w :=
    nsmul_cancel (K := I.F) hN hdiff
  have hxu : I.fmat x *ᵥ ivec (F := I.F) (m j) = I.fmat y *ᵥ ivec (F := I.F) (m j) + N • w := by
    rw [← hd]
    abel
  rw [← Matrix.mulVec_mulVec, hxu, Matrix.mulVec_add, Matrix.mulVec_mulVec, fmat_inv_mul I y,
    Matrix.one_mulVec]
  refine Submodule.add_mem _ (ivec_mem (hm j)) ?_
  have hP : ∀ i, (N • I.fmat y⁻¹) *ᵥ ivec (F := I.F) (m i) ∈ I.Lf := fun i => by
    rw [Matrix.smul_mulVec]
    exact (hyj i).2
  have h2 := mulVec_lam hm hgen (N • I.fmat y⁻¹) hP hw
  rwa [Matrix.smul_mulVec, ← Matrix.mulVec_smul] at h2

theorem step (hm : ∀ i, m i ∈ I.L) (hgen : ∀ l ∈ I.L, ∃ z : Fin k → ℤ, l = ∑ i, z i • m i)
    {N : ℕ} {x y : I.Gf} (hx : PN I m N x) (hy : PN I m N y) (he : fN I m N x = fN I m N y) :
    y⁻¹ * x ∈ I.Kset := by
  show ∀ w, w ∈ I.Lf ↔
    (((y⁻¹ * x : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix _ _ _) *ᵥ w ∈ I.Lf
  have hco : (((y⁻¹ * x : I.Gf) : GL (Fin I.n) (I.E ⊗[I.F] Af I.F)) : Matrix _ _ _) =
      I.fmat y⁻¹ * I.fmat x := rfl
  intro w
  rw [hco]
  constructor
  · intro hw
    exact mulVec_lam hm hgen _ (half I m hm hgen hx hy he) hw
  · intro hw
    have h2 := mulVec_lam hm hgen _ (half I m hm hgen hy hx he.symm) hw
    have h1 : I.fmat x⁻¹ * I.fmat y * (I.fmat y⁻¹ * I.fmat x) = 1 := by
      rw [mul_assoc, ← mul_assoc (I.fmat y), fmat_mul_inv, one_mul, fmat_inv_mul]
    rwa [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] at h2

theorem exists_PN (x : I.Gf) : ∃ N, PN I m N x := by
  classical
  have hA : ∀ j, ∃ N : ℕ, 0 < N ∧ N • (I.fmat x *ᵥ ivec (F := I.F) (m j)) ∈ I.Lf :=
    fun j => exists_nat_vec I.L_span _
  have hB : ∀ j, ∃ N : ℕ, 0 < N ∧ N • (I.fmat x⁻¹ *ᵥ ivec (F := I.F) (m j)) ∈ I.Lf :=
    fun j => exists_nat_vec I.L_span _
  choose A hA0 hA using hA
  choose B hB0 hB using hB
  refine ⟨(∏ j, A j) * ∏ j, B j, ?_, fun j => ⟨?_, ?_⟩⟩
  · exact Nat.mul_pos (Finset.prod_pos fun j _ => hA0 j) (Finset.prod_pos fun j _ => hB0 j)
  · obtain ⟨M, hM⟩ := Finset.dvd_prod_of_mem A (Finset.mem_univ j)
    rw [hM, mul_assoc]
    exact nsmul_lam (hA j) _
  · obtain ⟨M, hM⟩ := Finset.dvd_prod_of_mem B (Finset.mem_univ j)
    rw [hM, show (∏ j, A j) * (B j * M) = B j * (M * ∏ j, A j) by ring]
    exact nsmul_lam (hB j) _

end

end PI.WAU.B

namespace PI.WAU

open PI.WAU.B

theorem compact_countable : KCountable := by
  intro I
  obtain ⟨k, m, hm, hgen⟩ := exists_gen I.L (Module.Finite.iff_fg.mpr I.L_fg)
  have hcov : ∀ N : ℕ, ∃ s : Set I.Gf, s.Countable ∧
      ∀ x, PN I m N x → ∃ y ∈ s, y⁻¹ * x ∈ I.Kset := by
    intro N
    haveI : Countable (Bad I.F (N * N) → I.F) := countable_cls (N * N)
    exact cover_of I.Kset (PN I m N) (fN I m N) fun x y hx hy he => step I m hm hgen hx hy he
  choose s hs hsK using hcov
  refine ⟨⋃ N, s N, Set.countable_iUnion hs, fun x => ?_⟩
  obtain ⟨N, hN⟩ := exists_PN I m x
  obtain ⟨y, hy, hyK⟩ := hsK N x hN
  exact ⟨y, Set.mem_iUnion.mpr ⟨N, hy⟩, hyK⟩

end PI.WAU
