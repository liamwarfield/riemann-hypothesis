module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoRankDivPowOfChooseBounds
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoRankDivPowOfChooseBounds
open Filter Topology

namespace GlobalTheory

theorem tendsto_div_add_const_pow_div_pow (e K : ℝ) (he : e ≠ 0) (D : ℕ) :
    Tendsto (fun m : ℕ => ((m : ℝ) / e + K) ^ D / (m : ℝ) ^ D) atTop (𝓝 ((1 / e) ^ D)) := by
  have h1 : Tendsto (fun m : ℕ => (1 / e + K / (m : ℝ)) ^ D) atTop (𝓝 ((1 / e) ^ D)) := by
    have := ((tendsto_const_div_atTop_nhds_zero_nat K).const_add (1 / e)).pow D
    simpa using this
  refine h1.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with m hm
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [← div_pow]
  congr 1
  field_simp

theorem tendsto_rank_div_pow_of_choose_bounds (D e δ : ℕ) (r : ℕ → ℕ) (he : 0 < e)
    (h : ∀ s : ℕ, s < e → ∃ c c' : ℕ, ∀ q : ℕ,
      δ * (q + D).choose D ≤ r (e * (q + c) + s) ∧ r (e * q + s) ≤ δ * (q + c' + D).choose D) :
    Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop
      (𝓝 (δ / ((e : ℝ) ^ D * D.factorial))) := by
  choose! c c' hc using h
  set C := ∑ s ∈ Finset.range e, c s with hC
  set C' := ∑ s ∈ Finset.range e, c' s with hC'
  have hcC : ∀ s, s < e → c s ≤ C := fun s hs =>
    Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hs)
  have hcC' : ∀ s, s < e → c' s ≤ C' := fun s hs =>
    Finset.single_le_sum (f := c') (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hs)
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hDf : (0 : ℝ) < D.factorial := by exact_mod_cast D.factorial_pos
  have hlim : ∀ K : ℝ, Tendsto (fun m : ℕ => (δ : ℝ) / D.factorial *
      (((m : ℝ) / e + K) ^ D / (m : ℝ) ^ D)) atTop (𝓝 (δ / ((e : ℝ) ^ D * D.factorial))) := by
    intro K
    have := (tendsto_div_add_const_pow_div_pow e K heR.ne' D).const_mul ((δ : ℝ) / D.factorial)
    convert this using 2
    rw [div_pow, one_pow]
    field_simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hlim (-(C : ℝ))) (hlim ((C' + D : ℕ) : ℝ)) ?_ ?_
  · filter_upwards [eventually_ge_atTop (e * C + 1)] with m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hs : m % e < e := Nat.mod_lt _ he
    have hm_eq : e * (m / e) + m % e = m := Nat.div_add_mod m e
    have hqC : C ≤ m / e := (Nat.le_div_iff_mul_le he).2 (by nlinarith)
    have hcs := hcC (m % e) hs
    have h1 := (hc (m % e) hs (m / e - c (m % e))).1
    rw [Nat.sub_add_cancel (by omega : c (m % e) ≤ m / e), hm_eq] at h1
    have h2 := Nat.pow_le_choose (α := ℝ) D (m / e - c (m % e) + D)
    have h3 : m / e - c (m % e) + D + 1 - D = m / e - c (m % e) + 1 := by omega
    rw [h3] at h2
    have hmR : (m : ℝ) = e * ((m / e : ℕ) : ℝ) + ((m % e : ℕ) : ℝ) := by exact_mod_cast hm_eq.symm
    have hsR : ((m % e : ℕ) : ℝ) < e := by exact_mod_cast hs
    have hlt : (m : ℝ) / e < ((m / e : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ heR]; nlinarith
    have hge : (C : ℝ) ≤ (m : ℝ) / e := by
      rw [le_div_iff₀ heR]
      have : ((e * C : ℕ) : ℝ) ≤ m := by exact_mod_cast (show e * C ≤ m by omega)
      push_cast at this; linarith
    have hcsR : (c (m % e) : ℝ) ≤ C := by exact_mod_cast hcs
    have hx : (m : ℝ) / e + -(C : ℝ) ≤ ((m / e - c (m % e) + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_add, Nat.cast_sub (by omega), Nat.cast_one]; linarith
    have hx0 : 0 ≤ (m : ℝ) / e + -(C : ℝ) := by linarith
    have hA : (δ : ℝ) / D.factorial * ((m : ℝ) / e + -(C : ℝ)) ^ D ≤ r m := by
      calc (δ : ℝ) / D.factorial * ((m : ℝ) / e + -(C : ℝ)) ^ D
          ≤ (δ : ℝ) / D.factorial * (((m / e - c (m % e) + 1 : ℕ) : ℝ)) ^ D := by gcongr
        _ = (δ : ℝ) * ((((m / e - c (m % e) + 1 : ℕ) : ℝ)) ^ D / D.factorial) := by ring
        _ ≤ (δ : ℝ) * ((m / e - c (m % e) + D).choose D : ℝ) := by gcongr
        _ ≤ r m := by exact_mod_cast h1
    calc (δ : ℝ) / D.factorial * (((m : ℝ) / e + -(C : ℝ)) ^ D / (m : ℝ) ^ D)
        = (δ : ℝ) / D.factorial * ((m : ℝ) / e + -(C : ℝ)) ^ D / (m : ℝ) ^ D := by ring
      _ ≤ (r m : ℝ) / (m : ℝ) ^ D := by gcongr
  · filter_upwards [eventually_ge_atTop 1] with m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have hs : m % e < e := Nat.mod_lt _ he
    have hm_eq : e * (m / e) + m % e = m := Nat.div_add_mod m e
    have h1 := (hc (m % e) hs (m / e)).2
    rw [hm_eq] at h1
    have h2 := Nat.choose_le_pow_div (α := ℝ) D (m / e + c' (m % e) + D)
    have hmR : (m : ℝ) = e * ((m / e : ℕ) : ℝ) + ((m % e : ℕ) : ℝ) := by exact_mod_cast hm_eq.symm
    have hs0 : (0 : ℝ) ≤ ((m % e : ℕ) : ℝ) := Nat.cast_nonneg _
    have hle : ((m / e : ℕ) : ℝ) ≤ (m : ℝ) / e := by
      rw [le_div_iff₀ heR]; nlinarith
    have hcsR : (c' (m % e) : ℝ) ≤ C' := by exact_mod_cast hcC' (m % e) hs
    have hx : ((m / e + c' (m % e) + D : ℕ) : ℝ) ≤ (m : ℝ) / e + ((C' + D : ℕ) : ℝ) := by
      push_cast; linarith
    have hA : (r m : ℝ) ≤ (δ : ℝ) / D.factorial * ((m : ℝ) / e + ((C' + D : ℕ) : ℝ)) ^ D := by
      calc (r m : ℝ) ≤ (δ : ℝ) * ((m / e + c' (m % e) + D).choose D : ℝ) := by exact_mod_cast h1
        _ ≤ (δ : ℝ) * (((m / e + c' (m % e) + D : ℕ) : ℝ) ^ D / D.factorial) := by gcongr
        _ = (δ : ℝ) / D.factorial * (((m / e + c' (m % e) + D : ℕ) : ℝ)) ^ D := by ring
        _ ≤ _ := by gcongr
    calc (r m : ℝ) / (m : ℝ) ^ D
        ≤ (δ : ℝ) / D.factorial * ((m : ℝ) / e + ((C' + D : ℕ) : ℝ)) ^ D / (m : ℝ) ^ D := by gcongr
      _ = _ := by ring

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoRankDivPowOfChooseBoundsStatement
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_div_pow_of_choose_bounds : ∀ (D e δ : ℕ) (r : ℕ → ℕ), 0 < e → (∀ s : ℕ, s < e → ∃ c c' : ℕ, ∀ q : ℕ, δ * (q + D).choose D ≤ r (e * (q + c) + s) ∧ r (e * q + s) ≤ δ * (q + c' + D).choose D) → Tendsto (fun m : ℕ => (r m : ℝ) / (m : ℝ) ^ D) atTop (𝓝 (δ / ((e : ℝ) ^ D * D.factorial))) := by
  first | exact @GlobalTheory.tendsto_rank_div_pow_of_choose_bounds | exact GlobalTheory.tendsto_rank_div_pow_of_choose_bounds | (intros; apply GlobalTheory.tendsto_rank_div_pow_of_choose_bounds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapEqMk
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KummerAlg

open MvPolynomial

variable {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L] {q : ℕ}

def rels (φ : (Π _ : Fin q, L) →ₘₗ[B] B) : Set (MvPolynomial L B) :=
  Set.range (fun p : L × L => X (p.1 + p.2) - X p.1 - X p.2) ∪
  Set.range (fun p : B × L => X (p.1 • p.2) - C p.1 * X p.2) ∪
  Set.range (fun ℓ : Fin q → L => ∏ i, X (ℓ i) - C (φ ℓ))

def ideal (φ : (Π _ : Fin q, L) →ₘₗ[B] B) : Ideal (MvPolynomial L B) :=
  Ideal.span (rels φ)

abbrev Alg (φ : (Π _ : Fin q, L) →ₘₗ[B] B) : Type :=
  MvPolynomial L B ⧸ ideal φ

variable (φ : (Π _ : Fin q, L) →ₘₗ[B] B)

theorem algebraMap_eq_mk (c : B) : algebraMap B (Alg φ) c = Ideal.Quotient.mk _ (C c) := rfl

theorem add_mem (a b : L) : X (a + b) - X a - X b ∈ ideal φ :=
  Ideal.subset_span (Or.inl (Or.inl ⟨(a, b), rfl⟩))

theorem smul_mem (c : B) (a : L) : X (c • a) - C c * X a ∈ ideal φ :=
  Ideal.subset_span (Or.inl (Or.inr ⟨(c, a), rfl⟩))

theorem prod_mem (ℓ : Fin q → L) : ∏ i, X (ℓ i) - C (φ ℓ) ∈ ideal φ :=
  Ideal.subset_span (Or.inr ⟨ℓ, rfl⟩)

def gen : L →ₗ[B] Alg φ where
  toFun ℓ := Ideal.Quotient.mk _ (X ℓ)
  map_add' a b := by
    rw [← sub_eq_zero, sub_add_eq_sub_sub, ← map_sub, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact add_mem φ a b
  map_smul' c a := by
    rw [← sub_eq_zero, RingHom.id_apply, Algebra.smul_def, algebraMap_eq_mk,
      ← map_mul, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact smul_mem φ c a

theorem gen_apply (ℓ : L) : gen φ ℓ = Ideal.Quotient.mk _ (X ℓ) := rfl

theorem prod_gen (ℓ : Fin q → L) : ∏ i, gen φ (ℓ i) = algebraMap B (Alg φ) (φ ℓ) := by
  rw [← sub_eq_zero]
  simp only [gen_apply, ← map_prod, algebraMap_eq_mk]
  rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact prod_mem φ ℓ

def scalePoly (t : B) : MvPolynomial L B →ₐ[B] MvPolynomial L B := aeval fun ℓ => C t * X ℓ

theorem scalePoly_X (t : B) (ℓ : L) : scalePoly t (X ℓ) = C t * X ℓ := by simp [scalePoly]

theorem scalePoly_C (t c : B) : scalePoly (L := L) t (C c) = C c := by
  simp [scalePoly, aeval_C, MvPolynomial.algebraMap_eq]

theorem le_comap_scale (t : B) (ht : t ^ q = 1) : ideal φ ≤ (ideal φ).comap (scalePoly t) := by
  rw [ideal, Ideal.span_le]
  rintro r ((⟨⟨a, b⟩, rfl⟩ | ⟨⟨c, a⟩, rfl⟩) | ⟨ℓ, rfl⟩)
  · change scalePoly t _ ∈ ideal φ
    have : scalePoly t (X (a + b) - X a - X b) = C t * (X (a + b) - X a - X b) := by
      simp only [map_sub, scalePoly_X]; ring
    rw [this]; exact Ideal.mul_mem_left _ _ (add_mem φ a b)
  · change scalePoly t _ ∈ ideal φ
    have : scalePoly t (X (c • a) - C c * X a) = C t * (X (c • a) - C c * X a) := by
      simp only [map_sub, map_mul, scalePoly_X, scalePoly_C]; ring
    rw [this]; exact Ideal.mul_mem_left _ _ (smul_mem φ c a)
  · change scalePoly t _ ∈ ideal φ
    have : scalePoly t (∏ i, X (ℓ i) - C (φ ℓ)) = ∏ i, X (ℓ i) - C (φ ℓ) := by
      simp only [map_sub, map_prod, scalePoly_X, scalePoly_C, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← map_pow, ht, map_one, one_mul]
    rw [this]; exact prod_mem φ ℓ

def scale (t : B) (ht : t ^ q = 1) : Alg φ →ₐ[B] Alg φ :=
  Ideal.quotientMapₐ (ideal φ) (scalePoly t) (le_comap_scale φ t ht)

theorem scale_mk (t : B) (ht : t ^ q = 1) (p : MvPolynomial L B) :
    scale φ t ht (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (scalePoly t p) := rfl

theorem scale_gen (t : B) (ht : t ^ q = 1) (ℓ : L) : scale φ t ht (gen φ ℓ) = t • gen φ ℓ := by
  rw [gen_apply, scale_mk, scalePoly_X, map_mul, Algebra.smul_def, algebraMap_eq_mk]

theorem scale_ext {f g : Alg φ →ₐ[B] Alg φ} (h : ∀ ℓ, f (gen φ ℓ) = g (gen φ ℓ)) : f = g :=
  Ideal.Quotient.algHom_ext B (MvPolynomial.algHom_ext fun ℓ => h ℓ)

theorem scale_comp (s t : B) (hs : s ^ q = 1) (ht : t ^ q = 1) :
    (scale φ s hs).comp (scale φ t ht) = scale φ (s * t) (by rw [mul_pow, hs, ht, one_mul]) :=
  scale_ext φ fun ℓ => by
    rw [AlgHom.comp_apply, scale_gen, map_smul, scale_gen, scale_gen, smul_smul, mul_comm]

theorem scale_eq_id (t : B) (ht : t ^ q = 1) (h1 : t = 1) : scale φ t ht = AlgHom.id B (Alg φ) :=
  scale_ext φ fun ℓ => by rw [scale_gen, h1, one_smul, AlgHom.id_apply]

theorem scale_congr (s t : B) (hs : s ^ q = 1) (ht : t ^ q = 1) (h : s = t) :
    scale φ s hs = scale φ t ht := by subst h; rfl

def tw (ζ : B) (g : ZMod q) : B := ζ ^ g.val

theorem tw_add [NeZero q] {ζ : B} (hζ : ζ ^ q = 1) (g h : ZMod q) :
    tw ζ (g + h) = tw ζ g * tw ζ h := by
  rw [tw, tw, tw, ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div (g.val + h.val) q, pow_add, pow_mul, hζ, one_pow, mul_one]

theorem tw_pow {ζ : B} (hζ : ζ ^ q = 1) (g : ZMod q) : tw ζ g ^ q = 1 := by
  rw [tw, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]

theorem tw_zero (ζ : B) : tw ζ (0 : ZMod q) = 1 := by simp [tw]

theorem tw_mul_tw_neg [NeZero q] {ζ : B} (hζ : ζ ^ q = 1) (g : ZMod q) :
    tw ζ g * tw ζ (-g) = 1 := by rw [← tw_add hζ, add_neg_cancel, tw_zero]

def act [NeZero q] (ζ : B) (hζ : ζ ^ q = 1) : Multiplicative (ZMod q) →* (Alg φ ≃ₐ[B] Alg φ) where
  toFun g := AlgEquiv.ofAlgHom (scale φ (tw ζ g.toAdd) (tw_pow hζ _))
    (scale φ (tw ζ (-g.toAdd)) (tw_pow hζ _))
    (by rw [scale_comp]; exact scale_eq_id φ _ _ (tw_mul_tw_neg hζ _))
    (by rw [scale_comp]; exact scale_eq_id φ _ _ (by rw [mul_comm]; exact tw_mul_tw_neg hζ _))
  map_one' := AlgEquiv.ext fun x => by
    change scale φ (tw ζ (0 : ZMod q)) (tw_pow hζ 0) x = x
    rw [scale_eq_id φ _ _ (tw_zero ζ)]; rfl
  map_mul' g h := AlgEquiv.ext fun x => by
    change scale φ (tw ζ (g.toAdd + h.toAdd)) (tw_pow hζ _) x =
      scale φ (tw ζ g.toAdd) (tw_pow hζ _) (scale φ (tw ζ h.toAdd) (tw_pow hζ _) x)
    rw [← AlgHom.comp_apply, scale_comp]
    exact DFunLike.congr_fun (scale_congr φ _ _ _ _ (tw_add hζ _ _)) x

theorem act_gen [NeZero q] (ζ : B) (hζ : ζ ^ q = 1) (g : ZMod q) (ℓ : L) :
    act φ ζ hζ (Multiplicative.ofAdd g) (gen φ ℓ) = ζ ^ g.val • gen φ ℓ :=
  scale_gen φ _ (tw_pow hζ _) ℓ

end GlobalTheory.KummerAlg
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqOneOfForallPrimeMaximal
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqOneOfForallPrimeMaximal
open PrimeSpectrum

namespace GlobalTheory

variable {R : Type} [CommRing R]

theorem exists_mul_pow_eq_zero_of_forall_isMaximal
    (hR : ∀ P : Ideal R, P.IsPrime → P.IsMaximal) {p : Ideal R} [hp : p.IsPrime] {a : R}
    (ha : a ∈ p) : ∃ t ∉ p, ∃ n : ℕ, t * a ^ n = 0 := by
  by_contra! H
  have hdis : Disjoint ((⊥ : Ideal R) : Set R)
      ((p.primeCompl ⊔ Submonoid.powers a : Submonoid R) : Set R) := by
    rw [Set.disjoint_left]
    rintro x hx hxS
    rw [SetLike.mem_coe, Ideal.mem_bot] at hx
    subst hx
    obtain ⟨y, hy, z, hz, hyz⟩ := Submonoid.mem_sup.mp hxS
    obtain ⟨n, rfl⟩ := hz
    exact H y hy n hyz
  obtain ⟨q, hq, -, hqd⟩ := Ideal.exists_le_prime_disjoint ⊥ _ hdis
  have hqp : q ≤ p := by
    intro x hx
    by_contra hxp
    exact Set.disjoint_left.mp hqd hx
      (Submonoid.mem_sup_left (show x ∈ p.primeCompl from hxp))
  have hqp' := (hR q hq).eq_of_le hp.ne_top hqp
  have haq : a ∉ q := fun h => Set.disjoint_left.mp hqd h
    (Submonoid.mem_sup_right (Submonoid.mem_powers a))
  exact haq (hqp' ▸ ha)

theorem isClopen_basicOpen_of_forall_isMaximal
    (hR : ∀ P : Ideal R, P.IsPrime → P.IsMaximal) (a : R) :
    IsClopen ((basicOpen a : TopologicalSpace.Opens (PrimeSpectrum R)) : Set (PrimeSpectrum R)) := by
  refine ⟨?_, (basicOpen a).isOpen⟩
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  have hax : a ∈ x.asIdeal := by
    simpa [Set.mem_compl_iff, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] using hx
  obtain ⟨t, ht, n, htn⟩ := exists_mul_pow_eq_zero_of_forall_isMaximal hR hax
  refine ⟨(basicOpen t : Set (PrimeSpectrum R)), ?_, (basicOpen t).isOpen, ht⟩
  intro y hy hya
  rw [SetLike.mem_coe, PrimeSpectrum.mem_basicOpen] at hy hya
  have : t * a ^ n ∈ y.asIdeal := htn ▸ y.asIdeal.zero_mem
  rcases y.isPrime.mem_or_mem this with h | h
  · exact hy h
  · exact hya (y.isPrime.mem_of_pow_mem n h)

theorem exists_isIdempotentElem_mul_of_forall_isMaximal
    (hR : ∀ P : Ideal R, P.IsPrime → P.IsMaximal) (a : R) :
    ∃ e b : R, IsIdempotentElem e ∧ a * b = e ∧ ∀ p : Ideal R, p.IsPrime → a ∉ p → e ∉ p := by
  let c : TopologicalSpace.Clopens (PrimeSpectrum R) :=
    ⟨(basicOpen a : Set (PrimeSpectrum R)), isClopen_basicOpen_of_forall_isMaximal hR a⟩
  let e := (isIdempotentElemEquivClopens (R := R)).symm c
  have he : basicOpen e.1 = basicOpen a := by
    rw [basicOpen_isIdempotentElemEquivClopens_symm]; rfl
  obtain ⟨k, hk⟩ := (basicOpen_le_basicOpen_iff _ _).mp he.le
  have hmem : e.1 ∈ Ideal.span {a} := by
    rw [← e.2.pow_succ_eq k, pow_succ']
    exact Ideal.mul_mem_left _ _ hk
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hmem
  refine ⟨e.1, b, e.2, by rw [mul_comm, hb], fun p hp hap => ?_⟩
  have h1 : (⟨p, hp⟩ : PrimeSpectrum R) ∈ basicOpen a := hap
  rw [← he] at h1
  exact h1

theorem free_of_invertible_of_forall_isMaximal
    (hR : ∀ P : Ideal R, P.IsPrime → P.IsMaximal) (M : Type) [AddCommGroup M] [Module R M]
    (hM : Module.Invertible R M) : Module.Free R M := by
  classical
  obtain ⟨S, hS⟩ := ((Module.Invertible.linearEquiv R M).symm 1).exists_finset
  replace hS : 1 = ∑ i ∈ S, i.1 i.2 := by
    simpa [LinearEquiv.symm_apply_eq, Module.Invertible.linearEquiv] using hS
  letI : LinearOrder (Module.Dual R M × M) := IsWellOrder.linearOrder WellOrderingRel
  choose e b he hab hep using
    fun i : Module.Dual R M × M => exists_isIdempotentElem_mul_of_forall_isMaximal hR (i.1 i.2)

  let Q : Module.Dual R M × M → R := fun l => ∏ j ∈ S with j < l, (1 - e j)
  let e' : Module.Dual R M × M → R := fun l => e l * Q l
  have hQi : ∀ l, IsIdempotentElem (Q l) := fun l =>
    Finset.prod_induction _ IsIdempotentElem (fun _ _ h1 h2 => h1.mul h2)
      IsIdempotentElem.one (fun j _ => (he j).one_sub)
  have he'i : ∀ l, IsIdempotentElem (e' l) := fun l => (he l).mul (hQi l)
  have hlt : ∀ k ∈ S, ∀ l ∈ S, k < l → e k * e' l = 0 := by
    intro k hk l _ hkl
    have hmem : k ∈ S.filter (· < l) := Finset.mem_filter.mpr ⟨hk, hkl⟩
    simp only [e', Q]
    rw [← Finset.mul_prod_erase _ _ hmem]
    linear_combination (-(e l * ∏ x ∈ (S.filter (· < l)).erase k, (1 - e x))) * (he k).eq
  have horth : ∀ k ∈ S, ∀ l ∈ S, k ≠ l → e' k * e' l = 0 := by
    intro k hk l hl hkl
    rcases lt_or_gt_of_ne hkl with h | h
    · have := hlt k hk l hl h
      simp only [e'] at this ⊢
      linear_combination Q k * this
    · have := hlt l hl k hk h
      simp only [e'] at this ⊢
      linear_combination Q l * this

  let x : M := ∑ k ∈ S, e' k • k.2
  let φ : Module.Dual R M := ∑ l ∈ S, (b l * e' l) • l.1
  have hφx : φ x = ∑ l ∈ S, e' l := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [φ, x, LinearMap.sum_apply, LinearMap.smul_apply, map_sum,
      map_smul, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.sum_eq_single l]
    · have h1 := (he'i l).eq
      have h2 := hab l
      have h3 : e' l * e l = e' l := by
        simp only [e']; linear_combination Q l * (he l).eq
      linear_combination (b l * l.1 l.2) * h1 + e' l * h2 + h3
    · intro k hk hkl
      have := horth l hl k hk (Ne.symm hkl)
      linear_combination (b k * k.1 l.2) * this
    · intro h; exact absurd hl h
  have hsum : ∑ l ∈ S, e' l = 1 - ∏ i ∈ S, (1 - e i) := by
    rw [Finset.prod_one_sub_ordered S e]; ring
  have hunit : IsUnit (1 - ∏ i ∈ S, (1 - e i)) := by
    by_contra hnu
    obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits hnu
    obtain ⟨i, hi, him⟩ : ∃ i ∈ S, i.1 i.2 ∉ m := by
      by_contra! hall
      exact hm.ne_top ((Ideal.eq_top_iff_one _).mpr (hS ▸ Ideal.sum_mem _ hall))
    have hei := hep i m hm.isPrime him
    have h1 : 1 - e i ∈ m := by
      have : e i * (1 - e i) ∈ m := by
        rw [mul_sub, mul_one, (he i).eq, sub_self]; exact m.zero_mem
      exact (hm.isPrime.mem_or_mem this).resolve_left hei
    have hP : ∏ i ∈ S, (1 - e i) ∈ m := by
      rw [← Finset.mul_prod_erase _ _ hi]; exact m.mul_mem_right _ h1
    exact hm.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using m.add_mem hxm hP))
  rw [← hsum, ← hφx] at hunit
  exact .of_equiv <| .symm <| .ofBijective φ (Module.Invertible.bijective_of_surjective <|
    LinearMap.range_eq_top.mp <| Ideal.eq_top_of_isUnit_mem _ ⟨x, rfl⟩ hunit)

theorem pic_eq_one_of_forall_isMaximal :
    ∀ (R : Type) [CommRing R], (∀ P : Ideal R, P.IsPrime → P.IsMaximal) →
      ∀ c : CommRing.Pic R, c = 1 := by
  intro R _ hR c
  have : Subsingleton (CommRing.Pic R) := CommRing.Pic.subsingleton_iff.mpr
    fun M _ _ hM => free_of_invertible_of_forall_isMaximal hR M hM
  exact Subsingleton.elim _ _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PicEqOneOfForallPrimeMaximalStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pic_eq_one_of_forall_prime_maximal : ∀ (R : Type) [CommRing R], (∀ P : Ideal R, P.IsPrime → P.IsMaximal) → ∀ c : CommRing.Pic R, c = 1 := by
  first | (exact @GlobalTheory.pic_eq_one_of_forall_isMaximal) | (exact GlobalTheory.pic_eq_one_of_forall_isMaximal) | (intros; apply GlobalTheory.pic_eq_one_of_forall_isMaximal  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableNormMulPowOfBounded
namespace GlobalTheory.SummableSeriesBounds

open PowerSeries Filter Topology

variable {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]

def bdd (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] :
    Subring (PowerSeries C) where
  carrier := {Φ | ∃ b : ℝ, ∀ n : ℕ, ‖coeff n Φ‖ ≤ b}
  mul_mem' := by
    rintro Φ Ψ ⟨a, ha⟩ ⟨b, hb⟩
    have ha0 : 0 ≤ a := (norm_nonneg _).trans (ha 0)
    have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
    refine ⟨a * b, fun n => ?_⟩
    rw [coeff_mul]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg ha0 hb0) ?_
    intro p _
    rw [norm_mul]
    exact mul_le_mul (ha _) (hb _) (norm_nonneg _) ha0
  one_mem' := ⟨1, fun n => by
    rw [coeff_one]; split_ifs <;> simp⟩
  add_mem' := by
    rintro Φ Ψ ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, fun n => ?_⟩
    rw [map_add (f := _)]
    exact (norm_add_le _ _).trans (add_le_add (ha n) (hb n))
  zero_mem' := ⟨0, fun n => by simp⟩
  neg_mem' := by
    rintro Φ ⟨a, ha⟩
    exact ⟨a, fun n => by simpa using ha n⟩

theorem summable_norm_mul_pow_of_bounded {π : C} (hπ : ‖π‖ < 1) {a : ℕ → C} {b : ℝ} (hb : ∀ n, ‖a n‖ ≤ b) :
    Summable fun n => ‖a n * π ^ n‖ := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one (norm_nonneg π) hπ).mul_left b)
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right (hb n) (by positivity)

theorem summable_norm_bdd {π : C} (hπ : ‖π‖ < 1) (Φ : bdd C) :
    Summable fun n => ‖coeff n (Φ : PowerSeries C) * π ^ n‖ := by
  obtain ⟨b, hb⟩ := Φ.2
  exact summable_norm_mul_pow_of_bounded hπ hb

noncomputable def ev [CompleteSpace C] {π : C} (hπ : ‖π‖ < 1) : bdd C →+* C where
  toFun Φ := ∑' n, coeff n (Φ : PowerSeries C) * π ^ n
  map_one' := by
    rw [tsum_eq_single 0]
    · simp
    · intro n hn
      simp [coeff_one, hn]
  map_zero' := by simp
  map_add' Φ Ψ := by
    rw [← (summable_norm_bdd hπ Φ).of_norm.tsum_add (summable_norm_bdd hπ Ψ).of_norm]
    refine tsum_congr fun n => ?_
    simp [add_mul]
  map_mul' Φ Ψ := by
    rw [tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm (summable_norm_bdd hπ Φ)
      (summable_norm_bdd hπ Ψ)]
    refine tsum_congr fun n => ?_
    rw [Subring.coe_mul, coeff_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : p.1 + p.2 = n := by simpa using hp
    rw [← hp', pow_add]
    ring

omit [IsUltrametricDist C] in
theorem coeff_zero_lin (π : C) (G : PowerSeries C) :
    coeff 0 ((X - PowerSeries.C π) * G) = -(π * coeff 0 G) := by
  rw [sub_mul, map_sub, coeff_C_mul]
  simp

omit [IsUltrametricDist C] in
theorem coeff_succ_lin (π : C) (G : PowerSeries C) (n : ℕ) :
    coeff (n + 1) ((X - PowerSeries.C π) * G) = coeff n G - π * coeff (n + 1) G := by
  rw [sub_mul, map_sub, coeff_C_mul, coeff_succ_X_mul]

noncomputable def lin (π : C) : bdd C :=
  ⟨X - PowerSeries.C π, ⟨1 + ‖π‖, fun n => by
    rw [map_sub]
    refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
    · rw [coeff_X]; split_ifs <;> simp
    · rw [coeff_C]; split_ifs <;> simp⟩⟩

theorem lin_ne_zero (π : C) : lin π ≠ 0 := by
  intro h
  have := congrArg (fun Φ : bdd C => coeff 1 (Φ : PowerSeries C)) h
  simp [lin, coeff_C, coeff_X] at this

theorem ev_lin [CompleteSpace C] {π : C} (hπ : ‖π‖ < 1) : ev hπ (lin π) = 0 := by
  change ∑' n, coeff n (X - PowerSeries.C π : PowerSeries C) * π ^ n = 0
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ, coeff_C, coeff_X]
  · intro n hn
    have h0 : n ≠ 0 := by rintro rfl; simp at hn
    have h1 : n ≠ 1 := by rintro rfl; simp at hn
    simp [coeff_C, coeff_X, h0, h1]

theorem lin_dvd [CompleteSpace C] {π : C} (hπ : ‖π‖ < 1) (Φ : bdd C) (h : ev hπ Φ = 0) :
    lin π ∣ Φ := by
  obtain ⟨b, hb⟩ := Φ.2
  have hs : ∀ m, Summable fun k => ‖coeff (k + m) (Φ : PowerSeries C) * π ^ k‖ :=
    fun m => summable_norm_mul_pow_of_bounded hπ (a := fun k => coeff (k + m) (Φ : PowerSeries C))
      (fun k => hb _)
  let g : ℕ → C := fun m => ∑' k, coeff (k + m) (Φ : PowerSeries C) * π ^ k
  have hg : ∀ m, g m = coeff m (Φ : PowerSeries C) + π * g (m + 1) := by
    intro m
    simp only [g]
    rw [(hs m).of_norm.tsum_eq_zero_add, ← tsum_mul_left]
    congr 1
    · simp
    · refine tsum_congr fun k => ?_
      rw [show k + 1 + m = k + (m + 1) by ring]
      ring
  have hg0 : g 0 = 0 := h
  have hgb : ∀ m, ‖g m‖ ≤ ∑' k, b * ‖π‖ ^ k := by
    intro m
    refine tsum_of_norm_bounded
      ((summable_geometric_of_lt_one (norm_nonneg π) hπ).mul_left b).hasSum fun k => ?_
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hb _) (by positivity)
  refine ⟨⟨PowerSeries.mk fun n => g (n + 1), ⟨_, fun n => by rw [coeff_mk]; exact hgb _⟩⟩, ?_⟩
  apply Subtype.ext
  change (Φ : PowerSeries C) = (X - PowerSeries.C π) * PowerSeries.mk fun n => g (n + 1)
  ext n
  cases n with
  | zero =>
    rw [coeff_zero_lin, coeff_mk]
    have := hg 0
    rw [hg0] at this
    linear_combination -this
  | succ n =>
    rw [coeff_succ_lin, coeff_mk, coeff_mk]
    linear_combination -hg (n + 1)

theorem bound_of_lin_mul {π : C} (hπ : ‖π‖ < 1) {G : PowerSeries C} {b c : ℝ}
    (hc : ∀ n, ‖coeff n G‖ ≤ c) (hb : ∀ n, ‖coeff n ((X - PowerSeries.C π) * G)‖ ≤ b) (m : ℕ) :
    ‖coeff m G‖ ≤ b := by
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
  have key : ∀ k m, ‖coeff m G‖ ≤ max b (‖π‖ ^ k * c) := by
    intro k
    induction k with
    | zero => intro m; simpa using Or.inr (hc m)
    | succ k ih =>
      intro m
      have e : coeff m G = coeff (m + 1) ((X - PowerSeries.C π) * G) + π * coeff (m + 1) G := by
        rw [coeff_succ_lin]; ring
      rw [e]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ((hb _).trans (le_max_left _ _)) ?_)
      rw [norm_mul]
      refine (mul_le_mul_of_nonneg_left (ih (m + 1)) (norm_nonneg _)).trans ?_
      rw [mul_max_of_nonneg _ _ (norm_nonneg _)]
      refine max_le_max (mul_le_of_le_one_left hb0 hπ.le) (le_of_eq (by ring))
  have ht : Tendsto (fun k : ℕ => max b (‖π‖ ^ k * c)) atTop (𝓝 (max b (0 * c))) :=
    tendsto_const_nhds.max ((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hπ).mul_const c)
  rw [zero_mul, max_eq_left hb0] at ht
  exact ge_of_tendsto' ht fun k => key k m

theorem bound_of_lin_pow_mul {π : C} (hπ : ‖π‖ < 1) {b : ℝ} (n : ℕ) (G : bdd C)
    (hb : ∀ m, ‖coeff m ((lin π ^ n * G : bdd C) : PowerSeries C)‖ ≤ b) (m : ℕ) :
    ‖coeff m (G : PowerSeries C)‖ ≤ b := by
  induction n generalizing m with
  | zero => simpa using hb m
  | succ n ih =>
    refine ih (fun j => ?_) m
    obtain ⟨c, hc⟩ := (lin π ^ n * G).2
    refine bound_of_lin_mul hπ hc (fun i => ?_) j
    have := hb i
    rwa [pow_succ', mul_assoc, Subring.coe_mul] at this

theorem decay {π : C} (hπ : ‖π‖ < 1) {b : ℝ} {G : PowerSeries C} (hb : ∀ m, ‖coeff m G‖ ≤ b)
    (n m : ℕ) : ‖coeff m ((X - PowerSeries.C π) ^ n * G)‖ ≤ ‖π‖ ^ (n - m) * b := by
  have hb0 : 0 ≤ b := (norm_nonneg _).trans (hb 0)
  induction n generalizing m with
  | zero => simpa using hb m
  | succ n ih =>
    rw [pow_succ', mul_assoc]
    cases m with
    | zero =>
      rw [coeff_zero_lin, norm_neg, norm_mul]
      refine (mul_le_mul_of_nonneg_left (ih 0) (norm_nonneg _)).trans (le_of_eq ?_)
      simp only [Nat.sub_zero]; ring
    | succ m =>
      rw [coeff_succ_lin, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · simpa using ih m
      · rw [norm_neg, norm_mul]
        refine (mul_le_mul_of_nonneg_left (ih (m + 1)) (norm_nonneg _)).trans ?_
        rw [← mul_assoc, ← pow_succ']
        refine mul_le_mul_of_nonneg_right ?_ hb0
        exact pow_le_pow_of_le_one (norm_nonneg _) hπ.le (by omega)

theorem eq_zero_of_forall_dvd {π : C} (hπ : ‖π‖ < 1) (Φ : bdd C) (h : ∀ n, lin π ^ n ∣ Φ) :
    Φ = 0 := by
  obtain ⟨b, hb⟩ := Φ.2
  apply Subtype.ext
  ext m
  have key : ∀ n, ‖coeff m (Φ : PowerSeries C)‖ ≤ ‖π‖ ^ n * b := by
    intro n
    obtain ⟨G, hG⟩ := h (n + m)
    have h1 := bound_of_lin_pow_mul hπ (n + m) G (by rw [← hG]; exact hb)
    have h2 := decay hπ h1 (n + m) m
    rw [Nat.add_sub_cancel] at h2
    rw [hG]
    exact h2
  have ht : Tendsto (fun k : ℕ => ‖π‖ ^ k * b) atTop (𝓝 (0 * b)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hπ).mul_const b
  rw [zero_mul] at ht
  have := ge_of_tendsto' ht key
  simpa using this

theorem main (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C]
    (π : C) (hπ : ‖π‖ < 1) :
    ∃ (B : Subring (PowerSeries C)) (ev : B →+* C) (t : B),
      (∀ Φ : PowerSeries C, Φ ∈ B ↔ ∃ b : ℝ, ∀ n : ℕ, ‖coeff n Φ‖ ≤ b) ∧
      (∀ Φ : B, ev Φ = ∑' n : ℕ, coeff n (Φ : PowerSeries C) * π ^ n) ∧ t ≠ 0 ∧
      (∀ Φ : B, ev Φ = 0 ↔ t ∣ Φ) ∧ ∀ Φ : B, Φ ≠ 0 → ∃ n : ℕ, ¬ t ^ n ∣ Φ := by
  refine ⟨bdd C, ev hπ, lin π, fun _ => Iff.rfl, fun _ => rfl, lin_ne_zero π,
    fun Φ => ⟨lin_dvd hπ Φ, ?_⟩, fun Φ hΦ => ?_⟩
  · rintro ⟨G, rfl⟩
    rw [map_mul, ev_lin, zero_mul]
  · by_contra hc
    push_neg at hc
    exact hΦ (eq_zero_of_forall_dvd hπ Φ hc)

end GlobalTheory.SummableSeriesBounds
end
