module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.Arith

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.PDensM
namespace PositivityTheory.KB.SpectralGap.WordTransvectionCongruences

open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace

theorem two_le_prod {L : Type*} [Field L] [NumberField L] (π : 𝓞 L) (hπ : ¬ IsUnit π) (h0 : π ≠ 0) :
    (2 : ℝ) ≤ ∏ w : InfinitePlace L, w (π : L) ^ w.mult := by
  have h2 : |(Algebra.norm ℚ (π : L))| ≠ 1 := by
    intro h
    apply hπ
    rw [NumberField.isUnit_iff_norm]
    simpa [RingOfIntegers.coe_norm] using h
  rw [NumberField.InfinitePlace.prod_eq_abs_norm, ← Algebra.coe_norm_int] at *
  have h1 : Algebra.norm ℤ π ≠ 0 := Algebra.norm_ne_zero_iff.mpr h0
  set n := Algebra.norm ℤ π
  have h3 : |n| ≠ 1 := by
    intro h
    apply h2
    exact_mod_cast h
  have h4 : 2 ≤ |n| := by
    have := abs_pos.mpr h1
    omega
  exact_mod_cast h4

theorem exists_small {L : Type*} [Field L] [NumberField L] (π : 𝓞 L) (hπ : ¬ IsUnit π) (h0 : π ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y : 𝓞 L, y ≠ 0 ∧ ∃ k : ℕ, ∀ w : InfinitePlace L, w ((y : L) / (π : L) ^ k) < ε := by
  have hP := two_le_prod π hπ h0
  set P := ∏ w : InfinitePlace L, w (π : L) ^ w.mult with hPdef
  set E : ℝ := ∏ w : InfinitePlace L, ε ^ w.mult with hEdef
  have hE : 0 < E := Finset.prod_pos fun w _ => pow_pos hε _
  have hc : (0 : ℝ) < mixedEmbedding.convexBodyLTFactor L := by
    have := mixedEmbedding.convexBodyLTFactor_ne_zero L
    positivity
  have hB := mixedEmbedding.minkowskiBound_lt_top L 1
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt
    ((mixedEmbedding.minkowskiBound L 1).toReal / (mixedEmbedding.convexBodyLTFactor L * E))
    (by linarith : (1 : ℝ) < P)
  have hπw : ∀ w : InfinitePlace L, 0 < w (π : L) := fun w => by
    rw [InfinitePlace.pos_iff]
    exact_mod_cast h0
  let f : InfinitePlace L → NNReal := fun w => ⟨ε * w (π : L) ^ k, by have := hπw w; positivity⟩
  have hf : ((∏ w, f w ^ w.mult : NNReal) : ℝ) = E * P ^ k := by
    rw [NNReal.coe_prod, hEdef, hPdef, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun w _ => ?_
    change (ε * w (π : L) ^ k) ^ w.mult = _
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k]
  obtain ⟨a, ha0, ha⟩ := mixedEmbedding.exists_ne_zero_mem_ringOfIntegers_lt L (f := f) (by
    rw [mixedEmbedding.convexBodyLT_volume, ← ENNReal.coe_mul]
    rw [← ENNReal.toReal_lt_toReal hB.ne ENNReal.coe_ne_top]
    rw [ENNReal.coe_toReal, NNReal.coe_mul, hf]
    rw [div_lt_iff₀ (by positivity)] at hk
    linarith)
  refine ⟨a, ha0, k, fun w => ?_⟩
  rw [map_div₀, map_pow, div_lt_iff₀ (pow_pos (hπw w) _)]
  exact ha w

theorem exists_near {L : Type*} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] :
    ∃ R : ℝ, ∀ v : InfinitePlace L → ℂ, ∃ a : 𝓞 L, ∀ w, ‖v w - w.embedding (a : L)‖ ≤ R := by
  classical
  set b := mixedEmbedding.latticeBasis L
  refine ⟨∑ i, ‖b i‖, fun v => ?_⟩
  let x : mixedEmbedding.mixedSpace L := (0, fun w => v w.1)
  have hm := (ZSpan.floor b x).2
  rw [mixedEmbedding.mem_span_latticeBasis] at hm
  obtain ⟨a, ha⟩ := hm
  refine ⟨a, fun w => ?_⟩
  have hw : w.IsComplex := IsTotallyComplex.isComplex w
  have hfr := ZSpan.norm_fract_le b x
  rw [ZSpan.fract_apply, ← ha] at hfr
  refine le_trans ?_ hfr
  refine le_trans ?_ (norm_snd_le _)
  refine le_trans (le_of_eq ?_) (norm_le_pi_norm _ ⟨w, hw⟩)
  simp [x, mixedEmbedding.mixedEmbedding_apply_isComplex]

theorem dense_pow {L : Type*} [Field L] [NumberField L] [_root_.NumberField.IsTotallyComplex L] (π : 𝓞 L)
    (hπ : ¬ IsUnit π) (h0 : π ≠ 0) :
    Dense {z : InfinitePlace L → ℂ | ∃ t : 𝓞 L, ∃ k : ℕ,
      z = fun w => w.embedding ((t : L) / (π : L) ^ k)} := by
  obtain ⟨R, hR⟩ := exists_near (L := L)
  rw [Metric.dense_iff]
  intro z δ hδ
  have hε : 0 < δ / (|R| + 1) := by positivity
  obtain ⟨y, hy0, k, hyk⟩ := exists_small π hπ h0 hε
  set q : L := (y : L) / (π : L) ^ k with hqdef
  have hq : q ≠ 0 := div_ne_zero (by exact_mod_cast hy0) (pow_ne_zero _ (by exact_mod_cast h0))
  obtain ⟨a, ha⟩ := hR (fun w => z w / w.embedding q)
  refine ⟨fun w => w.embedding (((a * y : 𝓞 L) : L) / (π : L) ^ k), ?_, a * y, k, rfl⟩
  rw [Metric.mem_ball, dist_pi_lt_iff hδ]
  intro w
  have heq : w.embedding q ≠ 0 := by
    rw [ne_eq, map_eq_zero]
    exact hq
  have hsplit : z w - w.embedding (((a * y : 𝓞 L) : L) / (π : L) ^ k)
      = (z w / w.embedding q - w.embedding (a : L)) * w.embedding q := by
    rw [show (((a * y : 𝓞 L) : L) / (π : L) ^ k) = (a : L) * q by
      rw [hqdef]; push_cast; ring]
    rw [map_mul, sub_mul, div_mul_cancel₀ _ heq]
  rw [dist_comm, dist_eq_norm, hsplit, norm_mul, InfinitePlace.norm_embedding_eq]
  have h1 := ha w
  have h2 := hyk w
  have hR0 : 0 ≤ R := le_trans (norm_nonneg _) h1
  have hwq : 0 ≤ w q := by positivity
  have h3 : ‖z w / w.embedding q - w.embedding (a : L)‖ * w q ≤ |R| * (δ / (|R| + 1)) :=
    calc ‖z w / w.embedding q - w.embedding (a : L)‖ * w q ≤ R * (δ / (|R| + 1)) :=
          mul_le_mul h1 h2.le hwq hR0
      _ = |R| * (δ / (|R| + 1)) := by rw [abs_of_nonneg hR0]
  have h4 : |R| * (δ / (|R| + 1)) < δ := by
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [abs_nonneg R]
  linarith

end PositivityTheory.KB.SpectralGap.WordTransvectionCongruences
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.ArithmeticGapBounds.PDensG
namespace PositivityTheory.KB.SpectralGap.WordTransvectionCongruences

open Matrix

theorem diagonal_decomposition_transvections {ι F : Type*} [Fintype ι] [DecidableEq ι] [Field F] {i j : ι} (hij : i ≠ j)
    {a : F} (ha : a ≠ 0) :
    SpecialLinearGroup.diag2n hij a ha = SpecialLinearGroup.transvection hij a *
      SpecialLinearGroup.transvection hij.symm (-a⁻¹) * SpecialLinearGroup.transvection hij a *
      SpecialLinearGroup.transvection hij (-1) * SpecialLinearGroup.transvection hij.symm 1 *
      SpecialLinearGroup.transvection hij (-1) := by
  apply SpecialLinearGroup.coeMonoidHom_injective
  simp only [map_mul, SpecialLinearGroup.coeMonoidHom_apply, SpecialLinearGroup.diag2n_coe, SpecialLinearGroup.transvection_coe, mul_add, add_mul,
    one_mul, mul_one, single_mul_single_same]
  simp only [single_mul_single_of_ne _ _ _ _ hij.symm, single_mul_single_of_ne _ _ _ _ hij,
    zero_add, add_zero, single_mul_single_same, zero_mul, mul_zero]
  ext x y
  by_cases hxi : i = x
  · subst x
    by_cases hyi : i = y
    · subst y; (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
    by_cases hyj : j = y
    · subst y; (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
    (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
  by_cases hxj : j = x
  · subst x
    by_cases hyi : i = y
    · subst y; (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
    by_cases hyj : j = y
    · subst y; (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
    (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
  by_cases hyi : i = y
  · subst y; (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
  by_cases hyj : j = y
  · subst y; (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))
  (simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, diagonal_apply, hij, hij.symm, ha, *]
        <;> (try field_simp) <;> (try ring) <;> (try (split_ifs <;> simp_all)))

theorem sl_top {ι F : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι] [Field F]
    (S : Subgroup (SpecialLinearGroup ι F))
    (h : ∀ (i j : ι) (hij : i ≠ j) (c : F), SpecialLinearGroup.transvection hij c ∈ S) : S = ⊤ := by
  have hdiag : ∀ (i j : ι) (hij : i ≠ j) {c : F} (hc : c ≠ 0),
      SpecialLinearGroup.diag2n hij c hc ∈ S := by
    intro i j hij c hc
    rw [diagonal_decomposition_transvections hij hc]
    exact S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (S.mul_mem (h _ _ _ _) (h _ _ _ _))
      (h _ _ _ _)) (h _ _ _ _)) (h _ _ _ _)) (h _ _ _ _)
  refine eq_top_iff.2 fun M _ => ?_
  exact SpecialLinearGroup.diagonal_transvection_induction' (· ∈ S) M hdiag h
    (fun _ _ => S.mul_mem)

end PositivityTheory.KB.SpectralGap.WordTransvectionCongruences
end

noncomputable section

open NumberField Matrix

namespace PositivityTheory.KB.SpectralGap

namespace WordTransvectionCongruences

variable {L : Type} [Field L] [NumberField L] {N : ℕ}

theorem exists_third {N : ℕ} (hN : 3 ≤ N) (i j : Fin N) : ∃ k : Fin N, k ≠ i ∧ k ≠ j := by
  by_contra hc
  push_neg at hc
  have hsub : (Finset.univ : Finset (Fin N)) ⊆ {i, j} := by
    intro k _
    by_cases hk : k = i
    · simp [hk]
    · simp [hc k hk]
  have h1 := Finset.card_le_card hsub
  have h2 : ({i, j} : Finset (Fin N)).card ≤ 2 := by
    calc ({i, j} : Finset (Fin N)).card ≤ ({j} : Finset (Fin N)).card + 1 := Finset.card_insert_le _ _
      _ = 2 := by simp
  rw [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem mo_tv {i j : Fin N} (h : i ≠ j) (t : 𝓞 L) :
    mo L N (SpecialLinearGroup.transvection h t) = transvection i j (t : L) := by
  ext a b
  simp [mo, mt, SpecialLinearGroup.transvection_coe, Matrix.transvection, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem integral_transvection_mem_slIntegers_conjugate_zero (π : 𝓞 L) {i j : Fin N} (h : i ≠ j) (t : 𝓞 L) :
    SpecialLinearGroup.transvection h (t : L) ∈ Kg L N π 0 := by
  show ∃ γ, dg L N π 0 * (mt L N) (SpecialLinearGroup.transvection h (t : L)) = (mo L N) γ * dg L N π 0
  refine ⟨SpecialLinearGroup.transvection h t, ?_⟩
  have hd : dg L N π 0 = 1 := by
    ext a b
    simp [dg, Matrix.diagonal, Matrix.one_apply]
  rw [hd, mo_tv]
  simp [mt, SpecialLinearGroup.transvection_coe, Matrix.transvection]

theorem mem_parahoricTimesPrincipalCongruence_iff (π : 𝓞 L) (hπ : (π : L) ≠ 0) {i j : Fin N} (h : i ≠ j) (hi : (i : ℕ) = 0) (t : 𝓞 L) :
    SpecialLinearGroup.transvection h ((t : L) / π) ∈ Kg L N π 1 := by
  show ∃ γ, dg L N π 1 * (mt L N) (SpecialLinearGroup.transvection h ((t : L) / π)) = (mo L N) γ * dg L N π 1
  refine ⟨SpecialLinearGroup.transvection h t, ?_⟩
  rw [mo_tv]
  have hj : ¬ ((j : ℕ) < 1) := by
    intro hj
    apply h
    ext
    omega
  have hi' : (i : ℕ) < 1 := by omega
  ext a b
  simp only [mt, dg, SpecialLinearGroup.coeMonoidHom_apply, SpecialLinearGroup.transvection_coe,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transvection, Matrix.add_apply, Matrix.one_apply,
    Matrix.single_apply]
  by_cases hab : i = a ∧ j = b
  · obtain ⟨rfl, rfl⟩ := hab
    simp [h, hi', hj]
    field_simp
  · simp only [hab, if_false, add_zero]
    split_ifs <;> simp_all

theorem comm_mem {G : Subgroup (SpecialLinearGroup (Fin N) L)} {i j k : Fin N} (hik : i ≠ k) (hkj : k ≠ j)
    (hij : i ≠ j) {a b : L} (ha : SpecialLinearGroup.transvection hik a ∈ G)
    (hb : SpecialLinearGroup.transvection hkj b ∈ G) : SpecialLinearGroup.transvection hij (a * b) ∈ G := by
  have hn : ∀ (p q : Fin N) (x : L), Matrix.single p q (-x) = -Matrix.single p q x := by
    intro p q x
    ext r s
    simp [Matrix.single_apply]
    split_ifs <;> simp
  have m1 : ∀ {p q : Fin N} (hpq : p ≠ q) (x : L),
      (1 + Matrix.single p q x) * (1 + Matrix.single p q (-x)) = (1 : Matrix (Fin N) (Fin N) L) := by
    intro p q hpq x
    have z : Matrix.single p q x * Matrix.single p q (-x) = (0 : Matrix (Fin N) (Fin N) L) :=
      Matrix.single_mul_single_of_ne (h := hpq.symm) ..
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, z, Matrix.one_mul, Matrix.one_mul, Matrix.mul_one, hn]
    abel
  have hinv : ∀ {p q : Fin N} (hpq : p ≠ q) (x : L),
      (SpecialLinearGroup.transvection hpq x)⁻¹ = SpecialLinearGroup.transvection hpq (-x) := by
    intro p q hpq x
    rw [inv_eq_iff_mul_eq_one]
    exact Subtype.ext (m1 hpq x)
  have m : (1 + Matrix.single i k a) * (1 + Matrix.single k j b) * (1 + Matrix.single i k (-a)) *
      (1 + Matrix.single k j (-b)) = (1 + Matrix.single i j (a * b) : Matrix (Fin N) (Fin N) L) := by
    simp [Matrix.add_mul, Matrix.mul_add, Matrix.single_mul_single_same, Matrix.single_mul_single_of_ne, hik, hkj, hij, hik.symm, hkj.symm, hij.symm]
    simp only [hn]
    abel
  have hx := G.mul_mem (G.mul_mem (G.mul_mem ha hb) (G.inv_mem ha)) (G.inv_mem hb)
  rw [hinv, hinv] at hx
  convert hx using 1
  exact Subtype.ext m.symm

theorem mem_sup (π : 𝓞 L) (hπ : (π : L) ≠ 0) (hN : 3 ≤ N) (m : ℕ) :
    ∀ {i j : Fin N} (h : i ≠ j) (t : 𝓞 L),
      SpecialLinearGroup.transvection h ((t : L) / (π : L) ^ m) ∈ Kg L N π 0 ⊔ Kg L N π 1 := by
  obtain ⟨z, hz⟩ : ∃ z : Fin N, (z : ℕ) = 0 := ⟨⟨0, by omega⟩, rfl⟩
  induction m with
  | zero =>
    intro i j h t
    simpa using Subgroup.mem_sup_left (S := Kg L N π 0) (T := Kg L N π 1) (integral_transvection_mem_slIntegers_conjugate_zero π h t)
  | succ m ih =>
    have hK1 : ∀ {j : Fin N} (hzj : z ≠ j),
        SpecialLinearGroup.transvection hzj (((1 : 𝓞 L) : L) / π) ∈ Kg L N π 0 ⊔ Kg L N π 1 :=
      fun hzj => Subgroup.mem_sup_right (mem_parahoricTimesPrincipalCongruence_iff π hπ hzj hz 1)
    have hK0 : ∀ {i j : Fin N} (hij : i ≠ j),
        SpecialLinearGroup.transvection hij (((1 : 𝓞 L) : L)) ∈ Kg L N π 0 ⊔ Kg L N π 1 :=
      fun hij => Subgroup.mem_sup_left (integral_transvection_mem_slIntegers_conjugate_zero π hij 1)
    have c1 : ∀ {i j : Fin N} (h : i ≠ j) (t : 𝓞 L), i ≠ z → j ≠ z →
        SpecialLinearGroup.transvection h ((t : L) / (π : L) ^ (m + 1)) ∈ Kg L N π 0 ⊔ Kg L N π 1 := by
      intro i j h t hiz hjz
      have := comm_mem hiz (Ne.symm hjz) h (ih hiz t) (hK1 (Ne.symm hjz))
      convert this using 2
      push_cast
      field_simp
      ring
    have c0 : ∀ {j : Fin N} (h : z ≠ j) (t : 𝓞 L),
        SpecialLinearGroup.transvection h ((t : L) / (π : L) ^ (m + 1)) ∈ Kg L N π 0 ⊔ Kg L N π 1 := by
      intro j h t
      obtain ⟨k, hkz, hkj⟩ := exists_third hN z j
      have := comm_mem (Ne.symm hkz) hkj h (hK1 (Ne.symm hkz)) (ih hkj t)
      convert this using 2
      push_cast
      field_simp
      ring
    have c2 : ∀ {i : Fin N} (h : i ≠ z) (t : 𝓞 L),
        SpecialLinearGroup.transvection h ((t : L) / (π : L) ^ (m + 1)) ∈ Kg L N π 0 ⊔ Kg L N π 1 := by
      intro i h t
      obtain ⟨k, hki, hkz⟩ := exists_third hN i z
      have := comm_mem (Ne.symm hki) hkz h (c1 (Ne.symm hki) t h hkz) (hK0 hkz)
      convert this using 2
      push_cast
      ring
    intro i j h t
    by_cases hi : i = z
    · subst hi
      exact c0 h t
    · by_cases hj : j = z
      · subst hj
        exact c2 h t
      · exact c1 h t hi hj

theorem jS_tv {i j : Fin N} (h : i ≠ j) (c : L) :
    jS L N (SpecialLinearGroup.transvection h c) = fun w => SpecialLinearGroup.transvection h (w.embedding c) := by
  funext w
  ext a b
  simp [jS, SpecialLinearGroup.transvection_coe, Matrix.one_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem continuous_tv {ι : Type} [Fintype ι] [DecidableEq ι] {i j : ι} (h : i ≠ j) :
    Continuous fun c : ℂ => SpecialLinearGroup.transvection h c := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.single_apply]
  split_ifs <;> fun_prop

end WordTransvectionCongruences

open WordTransvectionCongruences in
theorem dens_holds : Dens := by
  classical
  intro L _ _ hL π hp N hN
  haveI : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hπ : (π : L) ≠ 0 := by exact_mod_cast hp.ne_zero
  set H := Subgroup.map (jS L N) (Kg L N π 0 ⊔ Kg L N π 1) with hH
  have hv : ∀ {i j : Fin N} (h : i ≠ j) (v : InfinitePlace L → ℂ),
      (fun w => SpecialLinearGroup.transvection h (v w)) ∈ H.topologicalClosure := by
    intro i j h v
    have hc : Continuous fun u : InfinitePlace L → ℂ => (fun w => SpecialLinearGroup.transvection h (u w) : Sp L N) :=
      continuous_pi fun w => (continuous_tv h).comp (continuous_apply w)
    have hd := WordTransvectionCongruences.dense_pow π hp.not_unit hp.ne_zero
    have hr := hc.range_subset_closure_image_dense hd ⟨v, rfl⟩
    rw [← SetLike.mem_coe, Subgroup.topologicalClosure_coe]
    refine closure_mono ?_ hr
    rintro _ ⟨z, ⟨t, k, rfl⟩, rfl⟩
    refine ⟨_, mem_sup π hπ hN k h t, ?_⟩
    rw [jS_tv]
  have htop : H.topologicalClosure = ⊤ := by
    rw [eq_top_iff, ← Subgroup.pi_top Set.univ, Subgroup.pi_le_iff]
    intro w₀
    rw [Subgroup.map_le_iff_le_comap]
    have hs := WordTransvectionCongruences.sl_top (Subgroup.comap
        (MonoidHom.mulSingle (fun _ : InfinitePlace L => Matrix.SpecialLinearGroup (Fin N) ℂ) w₀)
        H.topologicalClosure) (by
      intro i j h c
      rw [Subgroup.mem_comap]
      convert hv h (Pi.single w₀ c) using 1
      funext w
      rw [MonoidHom.mulSingle_apply]
      by_cases hw : w = w₀
      · subst hw
        simp
      · rw [Pi.mulSingle_eq_of_ne hw, Pi.single_eq_of_ne hw]
        ext a b
        simp [SpecialLinearGroup.transvection_coe, Matrix.transvection])
    rw [hs]
  rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, htop, Subgroup.coe_top]

end PositivityTheory.KB.SpectralGap
