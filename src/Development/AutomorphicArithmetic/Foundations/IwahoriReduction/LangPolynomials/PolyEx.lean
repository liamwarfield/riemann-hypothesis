module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialPrimitiveRootOfCyclotomicInertia
public import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.DvdOfNormLe

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PolyEx
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

theorem UpperTheory.Kd.C7.pPolyEx :
    UpperTheory.Kd.C7.SPolyEx := by
  intro l _ _ Ω _ _ _ A hA ζ hζ m u hu hinv
  obtain ⟨P, hP, hev⟩ := GlobalTheory.T.exists_polynomial_primitiveRoot_of_cyclotomic_inertia_fixed l Ω A hA m (ζ m) (hζ m).1 u hu
    (fun s hs h1 => hinv s ⟨hs, MonoidHom.mem_ker.2 h1⟩)
  have hsub : (↑P.coeffs : Set Ω) ⊆ (R0 A : Set Ω) := fun z hz => hP z hz
  refine ⟨P.toSubring (R0 A) hsub, ?_⟩
  unfold pv
  rw [← Polynomial.eval_map, Polynomial.map_toSubring, hev]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.PresTr
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7
open scoped Pointwise

private theorem pt_pv {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {τ : G ℚ Ω}
    (hτ : τ ∈ Ine (F := ℚ) A) (P : Polynomial (R0 A)) (z : Ω) (b : ℕ) (hz : τ z = z ^ b) :
    pv (Polynomial.expand (R0 A) b P) z = τ (pv P z) := by
  unfold pv
  rw [Polynomial.expand_eq_comp_X_pow, Polynomial.eval₂_comp, Polynomial.eval₂_X_pow, ← hz]
  have hc : ((τ : Ω →+* Ω)).comp (R0 A).subtype = (R0 A).subtype := by
    ext r
    exact r.2.2 τ hτ
  have e : (τ : Ω →+* Ω) (Polynomial.eval₂ (R0 A).subtype z P)
      = Polynomial.eval₂ (R0 A).subtype ((τ : Ω →+* Ω) z) P := by
    rw [Polynomial.hom_eval₂, hc]
  exact e.symm

private theorem pt_mem {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {τ : G ℚ Ω}
    (hτ : τ ∈ Ine (F := ℚ) A) {x : Ω} (hx : x ∈ A) : τ x ∈ A := by
  have h := mem_Dec.mp (Ine_le_Dec A hτ)
  have h2 := ValuationSubring.smul_mem_pointwise_smul τ x A hx
  rw [h] at h2
  exact h2

private theorem pt_cg {l : ℕ} [Fact l.Prime] {n : ℕ} {ι : Type} [Fintype ι] (o : ι → Qbar l) (ho : ∀ i, ‖o i‖ ≤ 1)
    (k : ι → ZMod (l ^ n)) (b : ℕ) (x : Qbar l) (h : Cg n x (∑ i, o i * ((k i).val : Qbar l))) :
    Cg n ((b : Qbar l) * x) (∑ i, o i * ((((b : ZMod (l ^ n)) * k i).val : ℕ) : Qbar l)) := by
  unfold Cg at h ⊢
  haveI : NeZero (l ^ n) := ⟨(pow_pos (Nat.Prime.pos Fact.out) n).ne'⟩
  have hc : ∀ i, (((((b : ZMod (l ^ n)) * k i).val : ℕ) : Qbar l))
      = (b : Qbar l) * ((k i).val : Qbar l) - (l : Qbar l) ^ n * (((b * (k i).val) / l ^ n : ℕ) : Qbar l) := by
    intro i
    have h1 : ((b : ZMod (l ^ n)) * k i).val = (b * (k i).val) % l ^ n := by
      rw [← ZMod.val_natCast (l ^ n) (b * (k i).val)]
      congr 1
      push_cast
      rw [ZMod.natCast_zmod_val]
    rw [h1]
    have h3 : ((b * (k i).val : ℕ) : Qbar l) = (((b * (k i).val) % l ^ n : ℕ) : Qbar l)
        + (l : Qbar l) ^ n * (((b * (k i).val) / l ^ n : ℕ) : Qbar l) := by
      rw [← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]
    rw [Nat.cast_mul] at h3
    linear_combination -h3
  have hs : ∑ i, o i * ((((b : ZMod (l ^ n)) * k i).val : ℕ) : Qbar l)
      = ∑ i, (b : Qbar l) * (o i * ((k i).val : Qbar l))
        - ∑ i, o i * ((l : Qbar l) ^ n * (((b * (k i).val) / l ^ n : ℕ) : Qbar l)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by rw [hc]; ring)
  have key : (b : Qbar l) * x - ∑ i, o i * ((((b : ZMod (l ^ n)) * k i).val : ℕ) : Qbar l)
      = (b : Qbar l) * (x - ∑ i, o i * ((k i).val : Qbar l))
        + ∑ i, o i * ((l : Qbar l) ^ n * (((b * (k i).val) / l ^ n : ℕ) : Qbar l)) := by
    rw [hs, mul_sub, Finset.mul_sum]
    ring
  rw [key]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    calc ‖(b : Qbar l)‖ * ‖x - ∑ i, o i * ((k i).val : Qbar l)‖ ≤ 1 * ‖(l : Qbar l) ^ n‖ :=
          mul_le_mul (IsUltrametricDist.norm_natCast_le_one _ _) h (norm_nonneg _) zero_le_one
      _ = ‖(l : Qbar l) ^ n‖ := one_mul _
  · refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) (fun i _ => ?_)
    rw [norm_mul, norm_mul]
    calc ‖o i‖ * (‖(l : Qbar l) ^ n‖ * ‖(((b * (k i).val) / l ^ n : ℕ) : Qbar l)‖)
        ≤ 1 * (‖(l : Qbar l) ^ n‖ * 1) := by
          gcongr
          · exact ho i
          · exact IsUltrametricDist.norm_natCast_le_one _ _
      _ = ‖(l : Qbar l) ^ n‖ := by ring

theorem UpperTheory.Kd.C7.pPresTr :
    UpperTheory.Kd.C7.SPresTr := by
  intro l _ hl Ω _ _ _ A hOver c β ζ hR Z hI b hb m n P hB
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : NeZero (l : Ω) := ⟨Nat.cast_ne_zero.mpr (Nat.Prime.ne_zero Fact.out)⟩
  haveI : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  have hbu : IsUnit (b : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hb ?_)
    have h' : ‖((b : ℤ) : ℤ_[l])‖ < 1 := by simpa using h
    exact Int.natCast_dvd_natCast.mp ((PadicInt.norm_int_lt_one_iff_dvd _).mp h')
  obtain ⟨τ, hτ, hτc⟩ := (pFrobEx l hl Ω A hOver).2.2 hbu.unit
  have hmodpow : ∀ (t : Ω) (N a : ℕ), t ^ N = 1 → t ^ a = t ^ (a % N) := by
    intro t N a ht
    conv_lhs => rw [← Nat.mod_add_div a N]
    rw [pow_add, pow_mul, ht, one_pow, mul_one]
  have hτpow : ∀ (t : Ω) (r : ℕ), t ^ l ^ r = 1 → τ t = t ^ b := by
    intro t r ht
    have hs := cyclotomicCharacter.spec l (MulSemiringAction.toRingAut (G ℚ Ω) Ω τ) t ht
    have e1 : cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω τ) = hbu.unit := hτc
    rw [e1, IsUnit.unit_spec, map_natCast, ZMod.val_natCast] at hs
    rw [hmodpow t (l ^ r) b ht]
    exact hs
  have hcyc : cycMod ℚ Ω l m τ = un b hb m := by
    apply Units.ext
    show (PadicInt.toZModPow m) ((cycZ ℚ Ω l τ : ℤ_[l])) = _
    rw [hτc, IsUnit.unit_spec, map_natCast]
    simp [un]
  have hu' : ∀ i, pv (Polynomial.expand (R0 A) b (P i)) (ζ m) = τ (pv (P i) (ζ m)) := fun i =>
    pt_pv hτ (P i) (ζ m) b (hτpow (ζ m) m (hR m).1.pow_eq_one)
  unfold BPres KumPres at hB ⊢
  obtain ⟨hprim, hnm, hunits, hnorm, hmain⟩ := hB
  refine ⟨hprim, hnm, fun i => ?_, hnorm, ?_⟩
  · dsimp only
    rw [hu' i]
    obtain ⟨h1, h2, h3⟩ := hunits i
    refine ⟨pt_mem hτ h1, (map_ne_zero τ).mpr h2, ?_⟩
    rw [← map_inv₀]
    exact pt_mem hτ h3
  · intro s hs hcs hsz
    have hs' : τ⁻¹ * s * τ ∈ Ine A := mul_mem (mul_mem (inv_mem hτ) hs) hτ
    have hcs' : cycMod ℚ Ω l m (τ⁻¹ * s * τ) = 1 := by simp [hcs]
    have hsz' : (τ⁻¹ * s * τ) (ζ n) = ζ n := fix_of_cycMod hnm hcs' hprim.pow_eq_one
    obtain ⟨k, hk, hcg⟩ := hmain _ hs' hcs' hsz'
    haveI : NeZero (l ^ n) := ⟨(pow_pos (Nat.Prime.pos Fact.out) n).ne'⟩
    refine ⟨fun i => (b : ZMod (l ^ n)) * k i, fun i => ?_, ?_⟩
    · obtain ⟨v, hv1, hv2⟩ := hk i
      refine ⟨τ v, ?_, ?_⟩
      · show (τ v) ^ l ^ n = pv (Polynomial.expand (R0 A) b (P i)) (ζ m)
        rw [hu' i, ← map_pow, hv1]
      · have e2 : s (τ v) = τ ((τ⁻¹ * s * τ) v) := by
          rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
        have h1 : ((b : ZMod (l ^ n)) * k i).val = (b * (k i).val) % l ^ n := by
          rw [← ZMod.val_natCast (l ^ n) (b * (k i).val)]
          congr 1
          push_cast
          rw [ZMod.natCast_zmod_val]
        rw [e2, hv2, map_mul, map_pow, hτpow (ζ n) n hprim.pow_eq_one, ← pow_mul, h1,
          ← hmodpow (ζ n) (l ^ n) _ hprim.pow_eq_one]
    · have hHm : τ⁻¹ * s * τ ∈ Hm l A m := Subgroup.mem_inf.mpr ⟨hs', hcs'⟩
      have hC := (pConj l hl Ω A hOver c Z hI m _ hHm τ hτ).2 (un b hb m)
      have e3 : τ * (τ⁻¹ * s * τ) * τ⁻¹ = s := by group
      rw [e3, hcyc, mul_inv_cancel] at hC
      show Cg n ((b : Qbar l) * Z m s (1 * un b hb m)) _
      rw [one_mul, hC]
      exact pt_cg β.val hnorm k b _ hcg
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.RepSmul
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

private theorem rs_dl_mul {R : Type} [CommRing R] {f g : PowerSeries R} (hf : IsUnit f) (hg : IsUnit g) :
    dl (f * g) = dl f + dl g := by
  obtain ⟨u, rfl⟩ := hf
  obtain ⟨v, rfl⟩ := hg
  have hu : (u : PowerSeries R) * ↑u⁻¹ = 1 := u.mul_inv
  have hv : (v : PowerSeries R) * ↑v⁻¹ = 1 := v.mul_inv
  have hinv : Ring.inverse ((u : PowerSeries R) * v) = ↑v⁻¹ * ↑u⁻¹ := by
    rw [← Units.val_mul, Ring.inverse_unit, mul_inv_rev, Units.val_mul]
  simp only [dl, dd, Ring.inverse_unit, Derivation.leibniz, smul_eq_mul, hinv]
  linear_combination ((1 + PowerSeries.X) * PowerSeries.derivative (R := R) v * ↑v⁻¹) * hu +
    ((1 + PowerSeries.X) * PowerSeries.derivative (R := R) u * ↑u⁻¹) * hv

private theorem rs_dl_one {R : Type} [CommRing R] : dl (1 : PowerSeries R) = 0 := by
  simp [dl, dd]

private theorem rs_dl_pow {R : Type} [CommRing R] {f : PowerSeries R} (hf : IsUnit f) (a : ℕ) :
    dl (f ^ a) = (a : PowerSeries R) * dl f := by
  induction a with
  | zero => simp [rs_dl_one]
  | succ a ih => rw [pow_succ, rs_dl_mul (hf.pow a) hf, ih]; push_cast; ring

private theorem rs_dl_prod {R : Type} [CommRing R] {ι : Type} (s : Finset ι) (F : ι → PowerSeries R)
    (hF : ∀ k, IsUnit (F k)) (a : ι → ℕ) :
    IsUnit (∏ k ∈ s, F k ^ a k) ∧ dl (∏ k ∈ s, F k ^ a k) = ∑ k ∈ s, (a k : PowerSeries R) * dl (F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [rs_dl_one]
  | insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.sum_insert hk]
    have hk' : IsUnit (F k ^ a k) := (hF k).pow _
    refine ⟨hk'.mul ih.1, ?_⟩
    rw [rs_dl_mul hk' ih.1, ih.2, rs_dl_pow (hF k)]

private theorem rs_alg_le {l : ℕ} [Fact l.Prime] (z : ℤ_[l]) : ‖algebraMap ℤ_[l] (PadicAlgCl l) z‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l), PadicAlgCl.norm_extends l]
  exact PadicInt.norm_le_one z

private theorem rs_sum_le {l : ℕ} [Fact l.Prime] {ι : Type} [Fintype ι] (e : ι → PadicAlgCl l) (he : ∀ i, ‖e i‖ ≤ 1)
    (z : ι → ℤ_[l]) : ‖∑ i, e i * algebraMap ℤ_[l] (PadicAlgCl l) (z i)‖ ≤ 1 := by
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [norm_mul]
  exact mul_le_one₀ (he i) (norm_nonneg _) (rs_alg_le _)

private theorem rs_mat {l : ℕ} [Fact l.Prime] {c : Coef l} (β : Bas c) (b : c.O) (k : Fin β.d) :
    (b : PadicAlgCl l) * β.val k = ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.mat b i k) := by
  simp only [Bas.val, Bas.mat, Algebra.leftMulMatrix_eq_repr_mul]
  conv_lhs => rw [← MulMemClass.coe_mul, ← β.e.sum_repr (b * β.e k)]
  simp [Algebra.smul_def, mul_comm]

private theorem rs_b_le {l : ℕ} [Fact l.Prime] {c : Coef l} (β : Bas c) (he : ∀ i, ‖β.val i‖ ≤ 1) (b : c.O) :
    ‖(b : PadicAlgCl l)‖ ≤ 1 := by
  have h : (b : PadicAlgCl l) = ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.e.repr b i) := by
    conv_lhs => rw [← β.e.sum_repr b]
    simp [Bas.val, Algebra.smul_def, mul_comm]
  rw [h]
  exact rs_sum_le _ he _

private theorem rs_cg {l : ℕ} [Fact l.Prime] {c : Coef l} (β : Bas c) (he : ∀ i, ‖β.val i‖ ≤ 1) (b : c.O) (n : ℕ)
    (z : Qbar l) (x y : Fin β.d → ℕ) (hz : Cg n z (∑ i, β.val i * (x i : Qbar l)))
    (hy : ∀ i, ∃ w : ℤ_[l], ∑ k, β.mat b i k * (x k : ℤ_[l]) = y i + (l : ℤ_[l]) ^ n * w) :
    Cg n ((b : PadicAlgCl l) * z) (∑ i, β.val i * (y i : Qbar l)) := by
  choose w hw using hy
  unfold Cg at hz ⊢
  have hb := rs_b_le β he b
  have hsum : (b : PadicAlgCl l) * ∑ k, β.val k * (x k : Qbar l)
      = ∑ i, β.val i * (y i : Qbar l) + (l : PadicAlgCl l) ^ n * ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (w i) := by
    calc (b : PadicAlgCl l) * ∑ k, β.val k * (x k : Qbar l)
        = ∑ k, ((b : PadicAlgCl l) * β.val k) * (x k : Qbar l) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ = ∑ k, ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (β.mat b i k) * (x k : Qbar l) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [rs_mat β b k, Finset.sum_mul]
      _ = ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (∑ k, β.mat b i k * (x k : ℤ_[l])) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun i _ => ?_
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [map_mul, map_natCast]
          ring
      _ = _ := by
          simp only [hw, map_add (f := _), map_mul, map_pow, map_natCast, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
  have key : (b : PadicAlgCl l) * z - ∑ i, β.val i * (y i : Qbar l)
      = (b : PadicAlgCl l) * (z - ∑ i, β.val i * (x i : Qbar l))
        + (l : PadicAlgCl l) ^ n * ∑ i, β.val i * algebraMap ℤ_[l] (PadicAlgCl l) (w i) := by
    rw [mul_sub, hsum]
    ring
  rw [key]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [norm_mul]
    calc ‖(b : PadicAlgCl l)‖ * ‖z - ∑ i, β.val i * (x i : Qbar l)‖ ≤ 1 * ‖(l : PadicAlgCl l) ^ n‖ :=
          mul_le_mul hb hz (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  · rw [norm_mul]
    calc _ ≤ ‖(l : PadicAlgCl l) ^ n‖ * 1 := mul_le_mul_of_nonneg_left (rs_sum_le _ he _) (norm_nonneg _)
      _ = _ := mul_one _

private theorem rs_unit {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {ι : Type} [Fintype ι] (u : ι → Ω)
    (hu : ∀ i, u i ∈ A ∧ u i ≠ 0 ∧ (u i)⁻¹ ∈ A) (a : ι → ℕ) :
    ∏ k, u k ^ a k ∈ A ∧ ∏ k, u k ^ a k ≠ 0 ∧ (∏ k, u k ^ a k)⁻¹ ∈ A := by
  classical
  suffices h : ∀ s : Finset ι, ∏ k ∈ s, u k ^ a k ∈ A ∧ ∏ k ∈ s, u k ^ a k ≠ 0 ∧ (∏ k ∈ s, u k ^ a k)⁻¹ ∈ A from h _
  intro s
  induction s using Finset.induction_on with
  | empty => simp [A.one_mem]
  | insert k s hk ih =>
    rw [Finset.prod_insert hk]
    obtain ⟨h1, h2, h3⟩ := hu k
    refine ⟨mul_mem (pow_mem h1 _) ih.1, mul_ne_zero (pow_ne_zero _ h2) ih.2.1, ?_⟩
    rw [mul_inv, ← inv_pow]
    exact mul_mem (pow_mem h3 _) ih.2.2

private theorem rs_kum {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {z : Ω} (hz : z ^ l ^ n = 1)
    (s : G ℚ Ω) {ι : Type} [Fintype ι] (u : ι → Ω) (x : ι → ZMod (l ^ n)) (hx : ∀ k, KumVal n z (u k) s (x k)) (a : ι → ℕ) :
    KumVal (l := l) n z (∏ k, u k ^ a k) s ((∑ k, a k * (x k).val : ℕ) : ZMod (l ^ n)) := by
  classical
  choose v hv using hx
  refine ⟨∏ k, v k ^ a k, ?_, ?_⟩
  · rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← pow_mul, mul_comm (a k), pow_mul, (hv k).1]
  · rw [map_prod]
    have hmod : z ^ (((∑ k, a k * (x k).val : ℕ) : ZMod (l ^ n))).val = z ^ (∑ k, a k * (x k).val) := by
      rw [ZMod.val_natCast]
      conv_rhs => rw [← Nat.mod_add_div (∑ k, a k * (x k).val) (l ^ n), pow_add, pow_mul, hz, one_pow, mul_one]
    rw [hmod, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [map_pow, (hv k).2, mul_pow, ← pow_mul, mul_comm (a k)]

theorem UpperTheory.Kd.C7.pRepSmul :
    UpperTheory.Kd.C7.SRepSmul := by
  intro l hl hl2 Ω _ _ _ A hA jj Φ c β ζ hζ Z D b hRep
  classical
  haveI : IsAdicComplete (Ideal.span {(l : Φ.R)}) Φ.R := Φ.fl.complete
  unfold Rep at hRep ⊢
  obtain ⟨c₁, m₁, hR⟩ := hRep
  refine ⟨c₁, max m₁ 1, fun m hm => ?_⟩
  have hm1 : m₁ ≤ m := le_trans (le_max_left _ _) hm
  have hm0 : 1 ≤ m := le_trans (le_max_right _ _) hm
  obtain ⟨P, hB, hLC⟩ := hR m hm1
  set n := m - c₁ with hn
  let a : Fin β.d → Fin β.d → ℕ := fun i k => PadicInt.appr (β.mat b i k) n
  have ha : ∀ i k, ∃ t : ℤ_[l], β.mat b i k = (a i k : ℤ_[l]) + (l : ℤ_[l]) ^ n * t := by
    intro i k
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec n (β.mat b i k))
    exact ⟨t, by linear_combination (-1 : ℤ_[l]) * ht⟩
  choose t ht using ha
  let P' : Fin β.d → Polynomial (R0 A) := fun i => ∏ k, P k ^ a i k
  unfold BPres KumPres at hB ⊢
  obtain ⟨hprim, hnm, hunits, hval, hK⟩ := hB
  have hpv : ∀ i, pv (P' i) (ζ m) = ∏ k, pv (P k) (ζ m) ^ a i k := by
    intro i
    simp only [P', pv, Polynomial.eval₂_finsetProd, Polynomial.eval₂_pow]
  refine ⟨P', ⟨hprim, hnm, fun i => ?_, hval, fun s hs hcyc hfix => ?_⟩, fun i => ?_⟩
  · beta_reduce
    rw [hpv i]
    exact rs_unit A _ hunits (a i)
  · obtain ⟨k, hk, hcg⟩ := hK s hs hcyc hfix
    refine ⟨fun i => ((∑ k', a i k' * (k k').val : ℕ) : ZMod (l ^ n)), fun i => ?_, ?_⟩
    · beta_reduce
      rw [hpv i]
      exact rs_kum hprim.pow_eq_one s _ k hk (a i)
    · refine rs_cg β hval b n _ (fun k' => (k k').val)
        (fun i => (((∑ k', a i k' * (k k').val : ℕ) : ZMod (l ^ n))).val) hcg fun i => ?_
      beta_reduce
      refine ⟨((∑ k', a i k' * (k k').val) / l ^ n : ℕ) + ∑ k', t i k' * ((k k').val : ℤ_[l]), ?_⟩
      have hcast : ((∑ k', a i k' * (k k').val : ℕ) : ℤ_[l])
          = ((∑ k', a i k' * (k k').val) % l ^ n : ℕ) + (l : ℤ_[l]) ^ n * ((∑ k', a i k' * (k k').val) / l ^ n : ℕ) := by
        conv_lhs => rw [← Nat.mod_add_div (∑ k', a i k' * (k k').val) (l ^ n)]
        push_cast
        ring
      have e1 : ∑ k', β.mat b i k' * ((k k').val : ℤ_[l])
          = ((∑ k', a i k' * (k k').val : ℕ) : ℤ_[l]) + (l : ℤ_[l]) ^ n * ∑ k', t i k' * ((k k').val : ℤ_[l]) := by
        push_cast
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k' _ => ?_
        rw [ht i k']
        ring
      rw [e1, ZMod.val_natCast]
      linear_combination hcast
  · let ψ : Polynomial (R0 A) →+* PowerSeries Φ.R :=
      (Polynomial.eval₂RingHom PowerSeries.C (1 + PowerSeries.X)).comp (Polynomial.mapRingHom Φ.i0)
    have hψ : ∀ F, Φ.ser F = ψ F := fun F => rfl
    have hunit : ∀ k, IsUnit (Φ.ser (P k)) := fun k =>
      (pWD l hl2 Ω A hA jj Φ ζ hζ m hm0 (P k)).2 (hunits k)
    have hser : Φ.ser (P' i) = ∏ k, Φ.ser (P k) ^ a i k := by
      simp only [hψ, P', map_prod, map_pow]
    have hfixR : ∀ (f : Φ.R →+* Φ.R) (z : ℤ_[l]), f (algebraMap ℤ_[l] Φ.R z) = algebraMap ℤ_[l] Φ.R z :=
      fun f z => RingHom.congr_fun (padicHom_ext l (f.comp (algebraMap ℤ_[l] Φ.R)) (algebraMap ℤ_[l] Φ.R)) z
    have htw : Φ.tw m (Φ.act (β.mat b) D i)
        = ∑ k, PowerSeries.C (algebraMap ℤ_[l] Φ.R (β.mat b i k)) * Φ.tw m (D k) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Fr.tw, Fr.act, map_sum, map_mul, PowerSeries.map_C, hfixR]
    unfold LC at hLC ⊢
    set_option synthInstance.maxHeartbeats 100000 in
      rw [htw, hser, (rs_dl_prod Finset.univ (fun k => Φ.ser (P k)) hunit (a i)).2, map_sum, map_sum,
      ← Finset.sum_sub_distrib]
    refine Ideal.sum_mem _ fun k _ => ?_
    have hdiff : ev Φ.R l m (PowerSeries.C (algebraMap ℤ_[l] Φ.R (β.mat b i k)))
        - ev Φ.R l m ((a i k : ℕ) : PowerSeries Φ.R) ∈ Ideal.span {(l : lev Φ.R l m) ^ n} := by
      have e : PowerSeries.C (algebraMap ℤ_[l] Φ.R (β.mat b i k)) - ((a i k : ℕ) : PowerSeries Φ.R)
          = (l : PowerSeries Φ.R) ^ n * PowerSeries.C (algebraMap ℤ_[l] Φ.R (t i k)) := by
        rw [ht i k]
        simp only [map_add (f := _), map_mul, map_pow, map_natCast]
        ring
      rw [← map_sub, e, map_mul, map_pow, map_natCast]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [map_mul, map_mul]
    have e2 : ev Φ.R l m (PowerSeries.C (algebraMap ℤ_[l] Φ.R (β.mat b i k))) * ev Φ.R l m (Φ.tw m (D k))
        - ev Φ.R l m ((a i k : ℕ) : PowerSeries Φ.R) * ev Φ.R l m (dl (Φ.ser (P k)))
        = ev Φ.R l m (PowerSeries.C (algebraMap ℤ_[l] Φ.R (β.mat b i k)))
            * (ev Φ.R l m (Φ.tw m (D k)) - ev Φ.R l m (dl (Φ.ser (P k))))
          + (ev Φ.R l m (PowerSeries.C (algebraMap ℤ_[l] Φ.R (β.mat b i k)))
            - ev Φ.R l m ((a i k : ℕ) : PowerSeries Φ.R)) * ev Φ.R l m (dl (Φ.ser (P k))) := by
      ring
    rw [e2]
    exact add_mem (Ideal.mul_mem_left _ _ (hLC k)) (Ideal.mul_mem_right _ _ hdiff)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.IwahoriReduction.LangPolynomials.SplitPow
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col UpperTheory.Kd.C7

namespace UpperTheory.Kd.C7.CoboundaryRoots

variable {l : ℕ} [Fact l.Prime]

private theorem root_mem (c : Coef l) {x : Qbar l} (hx : x ^ (l - 1) = 1) : x ∈ c.O := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod l)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hg
  have h1 : IsPrimitiveRoot (g : ZMod l) (l - 1) := by
    rw [IsPrimitiveRoot.coe_units_iff, ← hg]; exact IsPrimitiveRoot.orderOf g
  have h2 := h1.map_of_injective (f := WittVector.teichmuller l) (fun a b h => by
    simpa using congrArg (fun w : WittVector l (ZMod l) => w.coeff 0) h)
  have h3 := h2.map_of_injective (f := WittVector.equiv l) (WittVector.equiv l).injective
  have hinj : Function.Injective (algebraMap ℤ_[l] (Qbar l)) := by
    intro a b h
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l), IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l) b] at h
    exact Subtype.ext ((algebraMap ℚ_[l] (Qbar l)).injective h)
  have h4 := h3.map_of_injective (f := algebraMap ℤ_[l] (Qbar l)) hinj
  haveI : NeZero (l - 1) := ⟨by have := (Fact.out : l.Prime).two_le; omega⟩
  obtain ⟨i, -, hi⟩ := h4.eq_pow_of_pow_eq_one hx
  rw [← hi]
  exact c.O.pow_mem (c.O.algebraMap_mem _) i

private theorem nsub (x y : Qbar l) : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg, ← norm_neg y]
  exact IsUltrametricDist.norm_add_le_max _ _

private theorem nint (m : ℤ) : ‖((m : ℤ) : Qbar l)‖ ≤ 1 := by
  rw [← map_intCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
  exact Padic.norm_int_le_one m

private theorem nnat {m : ℕ} (h : ¬ l ∣ m) : ‖((m : ℕ) : Qbar l)‖ = 1 := by
  rw [← map_natCast (algebraMap ℚ_[l] (Qbar l)), norm_algebraMap']
  exact Padic.norm_natCast_eq_one_iff.2 (((Fact.out : l.Prime).coprime_iff_not_dvd).2 h)

private theorem nO (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 := by
  obtain ⟨⟨β⟩, h⟩ := pBasEx l c
  obtain ⟨v, hv⟩ : ∃ v : Fin β.d → ℤ_[l], ∑ i, v i • β.e i = ⟨x, hx⟩ := ⟨_, β.e.sum_repr _⟩
  have h1 := congrArg (fun y : c.O => (y : Qbar l)) hv
  simp only [AddSubmonoidClass.coe_finsetSum] at h1
  rw [← h1]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  have e : ((v i • β.e i : c.O) : Qbar l) = algebraMap ℚ_[l] (Qbar l) (v i : ℚ_[l]) * β.val i := by
    rw [← show algebraMap ℤ_[l] (Qbar l) (v i) = algebraMap ℚ_[l] (Qbar l) (v i : ℚ_[l]) from
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l) (v i), ← Algebra.smul_def]
    rfl
  rw [e, norm_mul, norm_algebraMap']
  exact mul_le_one₀ (v i).2 (norm_nonneg _) ((h β).1 i)

private theorem invO (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) (h1 : ‖x‖ = 1) : x⁻¹ ∈ c.O := by
  obtain ⟨⟨β⟩, h⟩ := pBasEx l c
  exact (h β).2.2.2 x hx h1

private theorem ndv {r : ℕ} (hr : 1 ≤ r) (x : (ZMod (l ^ r))ˣ) : ¬ l ∣ (x : ZMod (l ^ r)).val := by
  intro h
  have hc := ZMod.val_coe_unit_coprime x
  have hd : l ∣ Nat.gcd (x : ZMod (l ^ r)).val (l ^ r) := Nat.dvd_gcd h (dvd_pow_self l (by omega))
  rw [Nat.Coprime.gcd_eq_one hc] at hd
  exact (Fact.out : l.Prime).one_lt.ne' (Nat.dvd_one.1 hd)

private theorem phi_pow (φ : DirichletCharacter (Qbar l) l) {m : ℕ} (h : ¬ l ∣ m) : φ (m : ZMod l) ^ (l - 1) = 1 := by
  have hm : (m : ZMod l) ≠ 0 := by rwa [Ne, ZMod.natCast_eq_zero_iff]
  rw [← map_pow, ZMod.pow_card_sub_one_eq_one hm, map_one]

private theorem nphi (φ : DirichletCharacter (Qbar l) l) {m : ℕ} (h : ¬ l ∣ m) : ‖φ (m : ZMod l)‖ = 1 := by
  have h3 : ‖φ (m : ZMod l)‖ ^ (l - 1) = 1 := by rw [← norm_pow, phi_pow φ h, norm_one]
  have hl : l - 1 ≠ 0 := by have := (Fact.out : l.Prime).two_le; omega
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hl).1 h3

private noncomputable def E (φ : DirichletCharacter (Qbar l) l) (k a : ℕ) : Qbar l :=
  (φ (a : ZMod l))⁻¹ * ((a : Qbar l) ^ k)⁻¹

private theorem E_mul (φ : DirichletCharacter (Qbar l) l) (k a b : ℕ) : E φ k (a * b) = E φ k a * E φ k b := by
  simp only [E, Nat.cast_mul, map_mul, mul_pow, mul_inv]
  ring

private theorem E_mem (c : Coef l) (φ : DirichletCharacter (Qbar l) l) (k : ℕ) {a : ℕ} (ha : ¬ l ∣ a) : E φ k a ∈ c.O :=
  c.O.mul_mem (invO c (root_mem c (phi_pow φ ha)) (nphi φ ha))
    (invO c (c.O.pow_mem (natCast_mem c.O a) k) (by rw [norm_pow, nnat ha, one_pow]))

private theorem E_cong (φ : DirichletCharacter (Qbar l) l) (k : ℕ) {r a b : ℕ} (hr : 1 ≤ r) (ha : ¬ l ∣ a) (hb : ¬ l ∣ b)
    (h : a ≡ b [MOD l ^ r]) : ‖E φ k a - E φ k b‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  have hphi : (a : ZMod l) = (b : ZMod l) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).2 (h.of_dvd (dvd_pow_self l (by omega)))
  obtain ⟨m, hm⟩ := Nat.modEq_iff_dvd.1 (h.pow k)
  have hmQ : (b : Qbar l) ^ k - (a : Qbar l) ^ k = ((l : ℕ) : Qbar l) ^ r * (m : Qbar l) := by
    have := congrArg (fun z : ℤ => (z : Qbar l)) hm
    push_cast at this
    exact this
  have nz : ∀ z : Qbar l, ‖z‖ = 1 → z ≠ 0 := fun z hz h => by rw [h, norm_zero] at hz; exact zero_ne_one hz
  have haQ := nz _ (nnat ha)
  have hbQ := nz _ (nnat hb)
  have hpb := nz _ (nphi φ hb)
  have key : E φ k a - E φ k b = (φ (b : ZMod l))⁻¹ * ((a : Qbar l) ^ k)⁻¹ * ((b : Qbar l) ^ k)⁻¹ *
      ((b : Qbar l) ^ k - (a : Qbar l) ^ k) := by
    simp only [E]; rw [hphi]; field_simp
  rw [key, hmQ]
  simp only [norm_mul, norm_inv, norm_pow, nphi φ hb, nnat ha, nnat hb, one_pow, inv_one, one_mul]
  exact mul_le_of_le_one_right (by positivity) (nint m)

private theorem eta_mem (c : Coef l) (φ : DirichletCharacter (Qbar l) l) (k : ℕ) {r : ℕ} (hr : 1 ≤ r)
    (x : (ZMod (l ^ r))ˣ) : eta φ k r x ∈ c.O := E_mem c φ k (ndv hr x)

private theorem eta_mul (φ : DirichletCharacter (Qbar l) l) (k : ℕ) {r : ℕ} (hr : 1 ≤ r) (y x : (ZMod (l ^ r))ˣ) :
    ‖eta φ k r (y * x) - eta φ k r y * eta φ k r x‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  have h := E_cong φ k hr (ndv hr (y * x)) (b := (y : ZMod (l ^ r)).val * (x : ZMod (l ^ r)).val)
    (fun h => ((Fact.out : l.Prime).dvd_mul.1 h).elim (ndv hr y) (ndv hr x))
    (by rw [Units.val_mul, ZMod.val_mul]; exact Nat.mod_modEq _ _)
  rw [E_mul] at h
  exact h

private theorem eta_red (φ : DirichletCharacter (Qbar l) l) (k : ℕ) {r : ℕ} (hr : 1 ≤ r) (y : (ZMod (l ^ (r + 1)))ˣ) :
    ‖eta φ k (r + 1) y - eta φ k r (red l r y)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  refine E_cong φ k hr (ndv (by omega) y) (ndv hr (red l r y)) ?_
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val]
  simp [ZMod.natCast_val]

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {A : ValuationSubring Ω} {c : Coef l} {Z : Sy Ω l}

private theorem sp_mem (hZ : IwI c A Z) (φ : DirichletCharacter (Qbar l) l) (k : ℕ) {r : ℕ} (hr : 1 ≤ r) {s : G ℚ Ω}
    (hs : s ∈ Ine (F := ℚ) A) : sp (eta φ k r) (Z r) s ∈ c.O :=
  c.O.sum_mem fun x _ => c.O.mul_mem (eta_mem c φ k hr x) (hZ.int r s hs x)

private theorem sp_succ (hZ : IwI c A Z) (φ : DirichletCharacter (Qbar l) l) (k : ℕ) {r : ℕ} (hr : 1 ≤ r) {s : G ℚ Ω}
    (hs : s ∈ Ine (F := ℚ) A) : Cg r (sp (eta φ k (r + 1)) (Z (r + 1)) s) (sp (eta φ k r) (Z r) s) := by
  have e : sp (eta φ k r) (Z r) s = ∑ y, eta φ k r (red l r y) * Z (r + 1) s y := by
    unfold sp
    rw [← Finset.sum_fiberwise (s := Finset.univ) (g := red l r)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hZ.nrm r s hs x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    rw [(Finset.mem_filter.1 hy).2]
  rw [Cg, e, sp, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun y _ => ?_
  rw [← sub_mul, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (nO c (hZ.int _ s hs y))).trans (eta_red φ k hr y)

private theorem sp_mul (hZ : IwI c A Z) (φ : DirichletCharacter (Qbar l) l) (k : ℕ) {r : ℕ} (hr : 1 ≤ r) {s t : G ℚ Ω}
    (hs : s ∈ Ine (F := ℚ) A) (ht : t ∈ Ine (F := ℚ) A) :
    ‖sp (eta φ k r) (Z r) (s * t) - (sp (eta φ k r) (Z r) s +
      eta φ k r (cycMod ℚ Ω l r s) * sp (eta φ k r) (Z r) t)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  have h1 : sp (eta φ k r) (Z r) (s * t) = sp (eta φ k r) (Z r) s +
      ∑ y, eta φ k r (y * cycMod ℚ Ω l r s) * Z r t y := by
    unfold sp
    rw [Finset.sum_congr rfl fun x _ => by rw [hZ.coc r s hs t ht x, mul_add], Finset.sum_add_distrib]
    congr 1
    exact Fintype.sum_equiv (Equiv.mulRight (cycMod ℚ Ω l r s)⁻¹) _ _ (fun x => by
      rw [Equiv.coe_mulRight, inv_mul_cancel_right])
  rw [h1, add_sub_add_left_eq_sub, sp, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun y _ => ?_
  rw [← mul_assoc, ← sub_mul, norm_mul, mul_comm (eta φ k r (cycMod ℚ Ω l r s))]
  exact (mul_le_of_le_one_right (norm_nonneg _) (nO c (hZ.int _ t ht y))).trans (eta_mul φ k hr y _)

private theorem sp_triv (hZ : IwI c A Z) {r : ℕ} (η : (ZMod (l ^ r))ˣ → Qbar l) {h m : G ℚ Ω}
    (hh : h ∈ Ine (F := ℚ) A) (hm : m ∈ Ine (F := ℚ) A) (hc : cycMod ℚ Ω l r h = 1) :
    sp η (Z r) (h * m) = sp η (Z r) h + sp η (Z r) m := by
  simp only [sp, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hZ.coc r h hh m hm x, hc, inv_one, mul_one, mul_add]

private theorem comm_triv {M G' : Type*} [CommGroup M] [Group G'] (f : G' →* M) (x y : G') :
    f (x * y * x⁻¹ * y⁻¹) = 1 := by
  simp only [map_mul, map_inv]
  rw [mul_right_comm (f x), mul_inv_cancel_right, mul_inv_cancel]

private theorem eta_gam (φ : DirichletCharacter (Qbar l) l) (k : ℕ) {r : ℕ} (hr : 2 ≤ r) {t : G ℚ Ω}
    (ht : (cycZ ℚ Ω l t : ℤ_[l]) = ((1 + l : ℕ) : ℤ_[l])) :
    eta φ k r (cycMod ℚ Ω l r t) = (((1 + l : ℕ) : Qbar l) ^ k)⁻¹ := by
  have hl2 := (Fact.out : l.Prime).two_le
  have hlt : 1 + l < l ^ r := by
    have h1 : l ^ 2 ≤ l ^ r := Nat.pow_le_pow_right (by omega) hr
    nlinarith
  have hv : ((cycMod ℚ Ω l r t : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)).val = 1 + l := by
    have : ((cycMod ℚ Ω l r t : (ZMod (l ^ r))ˣ) : ZMod (l ^ r)) = PadicInt.toZModPow r (cycZ ℚ Ω l t : ℤ_[l]) := rfl
    rw [this, ht, map_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  simp only [eta, hv]
  have h1 : ((1 + l : ℕ) : ZMod l) = 1 := by push_cast; simp
  rw [h1, map_one, inv_one, one_mul]

private theorem split_pow (c : Coef l) {k : ℕ} (hk : 1 ≤ k) :
    ∃ (c₂ : ℕ) (v : Qbar l), v ∈ c.O ∧ ((l : ℕ) : Qbar l) ^ c₂ = ((((1 + l : ℕ) : Qbar l) ^ k)⁻¹ - 1) * v := by
  have hl2 := (Fact.out : l.Prime).two_le
  have h1 : 1 < (1 + l) ^ k := Nat.one_lt_pow (by omega) (by omega)
  obtain ⟨e, m, hm, hN⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := (1 + l) ^ k - 1) (by omega) l (by omega)
  have hN' : (1 + l) ^ k = l ^ e * m + 1 := by omega
  have hQ : ((1 + l : ℕ) : Qbar l) ^ k = (l : Qbar l) ^ e * m + 1 := by exact_mod_cast congrArg (Nat.cast (R := Qbar l)) hN'
  have hm0 : (m : Qbar l) ≠ 0 := fun h => by have := nnat hm; rw [h, norm_zero] at this; exact zero_ne_one this
  have hb0 : ((1 + l : ℕ) : Qbar l) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (by omega))
  refine ⟨e, -(((1 + l : ℕ) : Qbar l) ^ k * (m : Qbar l)⁻¹),
    c.O.neg_mem (c.O.mul_mem (c.O.pow_mem (natCast_mem c.O _) k) (invO c (natCast_mem c.O m) (nnat hm))), ?_⟩
  generalize ((1 + l : ℕ) : Qbar l) ^ k = B at hQ hb0
  field_simp
  rw [hQ]; ring

end UpperTheory.Kd.C7.CoboundaryRoots

open UpperTheory.Kd.C7.CoboundaryRoots in
theorem UpperTheory.Kd.C7.pCob :
    UpperTheory.Kd.C7.SCob := by
  intro l _ hl2 Ω _ _ _ A hA c Z hZ φ k hk hsp
  have hu : IsUnit ((1 + l : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    simp
  obtain ⟨t, htI, ht⟩ := (pFrobEx l hl2 Ω A hA).2.2 hu.unit
  have ht' : (cycZ ℚ Ω l t : ℤ_[l]) = ((1 + l : ℕ) : ℤ_[l]) := by rw [ht]; rfl
  obtain ⟨z, hzO, hz⟩ := exists_limit_coef l c Unit (fun n _ => sp (eta φ k (n + 1)) (Z (n + 1)) t)
    (fun n _ => sp_mem hZ φ k (by omega) htI)
    (fun n _ => (sp_succ hZ φ k (r := n + 1) (by omega) htI).trans (GlobalTheory.Ord2.norm_l_pow_anti (by omega)))
  obtain ⟨c₂, v, hvO, hv⟩ := split_pow c hk
  refine ⟨c₂, v * z (), c.O.mul_mem hvO (hzO ()), fun s hs n => ?_⟩
  obtain ⟨r₀, hr₀⟩ := hsp n
  refine ⟨max r₀ (n + 2), fun r hr => ?_⟩
  have hr0 : r₀ ≤ r := le_trans (le_max_left _ _) hr
  have hr2 : n + 2 ≤ r := le_trans (le_max_right _ _) hr
  obtain ⟨q, rfl⟩ : ∃ q, r = q + 1 := ⟨r - 1, by omega⟩
  have hr1 : 1 ≤ q + 1 := by omega
  have hlim : ‖z () - sp (eta φ k (q + 1)) (Z (q + 1)) t‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ :=
    (hz q ()).trans (GlobalTheory.Ord2.norm_l_pow_anti (by omega))
  have hhI : t * s * t⁻¹ * s⁻¹ ∈ Ine (F := ℚ) A :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ htI hs) (Subgroup.inv_mem _ htI)) (Subgroup.inv_mem _ hs)
  have hsmall := hr₀ _ hr0 _ hhI (comm_triv _ t s)
  have hts : t * s = (t * s * t⁻¹ * s⁻¹) * (s * t) := by group
  have hB := sp_triv hZ (eta φ k (q + 1)) hhI (Subgroup.mul_mem _ hs htI) (comm_triv _ t s)
  rw [← hts] at hB
  have hAa := sp_mul hZ φ k hr1 htI hs
  rw [eta_gam φ k (by omega) ht'] at hAa
  have hCa := sp_mul hZ φ k hr1 hs htI
  have hrle : ‖((l : ℕ) : Qbar l) ^ (q + 1)‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := GlobalTheory.Ord2.norm_l_pow_anti (by omega)
  have hρ : ‖eta φ k (q + 1) (cycMod ℚ Ω l (q + 1) s) - 1‖ ≤ 1 :=
    nO c (c.O.sub_mem (eta_mem c φ k hr1 _) c.O.one_mem)
  rw [Cg, sub_zero] at hsmall
  rw [Cg, hv]
  generalize sp (eta φ k (q + 1)) (Z (q + 1)) (t * s * t⁻¹ * s⁻¹) = fh at hsmall hB
  generalize sp (eta φ k (q + 1)) (Z (q + 1)) (t * s) = fts at hB hAa
  generalize sp (eta φ k (q + 1)) (Z (q + 1)) (s * t) = fst at hB hCa
  generalize sp (eta φ k (q + 1)) (Z (q + 1)) s = X at hAa hCa ⊢
  generalize sp (eta φ k (q + 1)) (Z (q + 1)) t = T at hAa hCa hlim
  generalize eta φ k (q + 1) (cycMod ℚ Ω l (q + 1) s) = ρ at hCa hρ ⊢
  generalize (((1 + l : ℕ) : Qbar l) ^ k)⁻¹ = β at hAa ⊢
  have e : (β - 1) * v * X - (ρ - 1) * (v * z ()) =
      v * (((fh - (fts - (T + β * X))) + (fst - (X + ρ * T))) - (ρ - 1) * (z () - T)) := by
    rw [hB]; ring
  rw [e, norm_mul]
  refine (mul_le_of_le_one_left (norm_nonneg _) (nO c hvO)).trans ((nsub _ _).trans (max_le ?_ ?_))
  · exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le ((nsub _ _).trans (max_le hsmall (hAa.trans hrle))) (hCa.trans hrle))
  · rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) hρ).trans hlim
end
