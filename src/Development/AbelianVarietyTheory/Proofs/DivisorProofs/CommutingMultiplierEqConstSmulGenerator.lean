module

public import Mathlib

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingMultiplierEqConstSmulGenerator
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingMapEqSmulMultiplier
namespace GlobalTheory

theorem commuting_map_eq_smul_multiplier :
  ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B] (W W' : Submodule ℂ B) [FiniteDimensional ℂ W] (h h' : B), h * h' = 1 → (∀ w ∈ W', h' * w ∈ W) → ∀ T : W →ₗ[ℂ] W', T ≠ 0 → (∀ f g : W, (T f : B) * (g : B) = (f : B) * (T g : B)) → ∃ a : ℂ, a ≠ 0 ∧ ∀ f : W, (T f : B) = a • (h * (f : B)) := by
  intro B _ _ _ W W' _ h h' hhh hW T hT hcomm
  let S : W →ₗ[ℂ] W :=
    { toFun := fun f => ⟨h' * (T f : B), hW _ (T f).2⟩
      map_add' := fun f g => by ext; simp [mul_add]
      map_smul' := fun c f => by ext; simp [mul_smul_comm] }
  haveI : Nontrivial W := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hT
    ext f
    rw [Subsingleton.elim f 0]
    simp
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue S
  obtain ⟨f₀, hf₀⟩ := ha.exists_hasEigenvector
  have hS : S f₀ = a • f₀ := hf₀.apply_eq_smul
  have h0 : (T f₀ : B) = a • (h * (f₀ : B)) := by
    have hc : h' * (T f₀ : B) = a • (f₀ : B) := by
      have := congrArg (fun x : W => (x : B)) hS
      simpa [S] using this
    calc (T f₀ : B) = h * (h' * T f₀) := by rw [← mul_assoc, hhh, one_mul]
    _ = h * (a • (f₀ : B)) := by rw [hc]
    _ = a • (h * (f₀ : B)) := mul_smul_comm _ _ _
  have hf0ne : (f₀ : B) ≠ 0 := by
    intro hz
    exact hf₀.2 (Subtype.ext hz)
  have key : ∀ f : W, (T f : B) = a • (h * (f : B)) := by
    intro f
    have hx := hcomm f f₀
    rw [h0] at hx
    apply mul_right_cancel₀ hf0ne
    rw [hx]
    simp only [Algebra.smul_def]
    ring
  refine ⟨a, ?_, key⟩
  rintro rfl
  apply hT
  ext f
  simp [key f]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingMultiplierEqConstSmulGenerator
namespace GlobalTheory

theorem commuting_multiplier_eq_const_smul_generator
    (K A B : Type) [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra ℂ B]
    (σ : K →+* ℂ) (rd : A →+* B)
    (hsemi : ∀ (a : K) (f : A), rd (a • f) = σ a • rd f)
    (R : Subalgebra ℂ B) [IsDomain R] (V V' : Submodule K A)
    [FiniteDimensional K V] [FiniteDimensional K V']
    (hV : ∀ f ∈ V, rd f ∈ R) (hV' : ∀ f ∈ V', rd f ∈ R)
    (hind : ∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V) → LinearIndependent K b →
      LinearIndependent ℂ (fun i => rd (b i)))
    (hind' : ∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V') → LinearIndependent K b →
      LinearIndependent ℂ (fun i => rd (b i)))
    (h h' : B) (hh : h ∈ R) (hh' : h' ∈ R) (hhh : h * h' = 1)
    (hsub : ∀ f ∈ V', h' * rd f ∈ Submodule.span ℂ (rd '' (V : Set A)))
    (T : V →ₗ[K] V') (hT : T ≠ 0)
    (hcomm : ∀ f g : V, (T f : A) * (g : A) = (f : A) * (T g : A)) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ f : V, rd (T f) = a • (h * rd f) := by
  classical
  have expand : ∀ (U : Submodule K A) [FiniteDimensional K U] (f : U),
      rd (f : A) = ∑ j, σ ((Module.finBasis K U).repr f j) •
        rd ((Module.finBasis K U j : U) : A) := by
    intro U _ f
    conv_lhs => rw [← (Module.finBasis K U).sum_repr f]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, hsemi]
  set bV := Module.finBasis K V with hbV
  set bV' := Module.finBasis K V' with hbV'
  let gV : Fin (Module.finrank K V) → R := fun j => ⟨rd (bV j : A), hV _ (bV j).2⟩
  let gV' : Fin (Module.finrank K V') → R := fun j => ⟨rd (bV' j : A), hV' _ (bV' j).2⟩
  have liV : LinearIndependent ℂ gV := by
    apply LinearIndependent.of_comp R.val.toLinearMap
    exact hind _ (fun j => (bV j : A)) (fun j => (bV j).2)
      (bV.linearIndependent.map' V.subtype V.ker_subtype)
  have liV' : LinearIndependent ℂ gV' := by
    apply LinearIndependent.of_comp R.val.toLinearMap
    exact hind' _ (fun j => (bV' j : A)) (fun j => (bV' j).2)
      (bV'.linearIndependent.map' V'.subtype V'.ker_subtype)
  let W := Submodule.span ℂ (Set.range gV)
  let W' := Submodule.span ℂ (Set.range gV')
  have eqV : ∀ f : V, (⟨rd f, hV _ f.2⟩ : R) = ∑ j, σ (bV.repr f j) • gV j := by
    intro f
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, gV]
    exact expand V f
  have eqV' : ∀ f : V', (⟨rd f, hV' _ f.2⟩ : R) = ∑ j, σ (bV'.repr f j) • gV' j := by
    intro f
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul, gV']
    exact expand V' f
  have memW : ∀ f : V, (⟨rd f, hV _ f.2⟩ : R) ∈ W := by
    intro f
    rw [eqV f]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  have memW' : ∀ f : V', (⟨rd f, hV' _ f.2⟩ : R) ∈ W' := by
    intro f
    rw [eqV' f]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))
  let bW : Module.Basis (Fin (Module.finrank K V)) ℂ W := Module.Basis.span liV
  have bW_apply : ∀ j, (bW j : R) = gV j := fun j => congrArg Subtype.val (Module.Basis.span_apply liV j)
  let img : Fin (Module.finrank K V) → W' := fun j => ⟨⟨rd (T (bV j) : A), hV' _ (T (bV j)).2⟩, memW' (T (bV j))⟩
  let Tc : W →ₗ[ℂ] W' := bW.constr ℂ img
  have Tc_rd : ∀ f : V, Tc ⟨⟨rd f, hV _ f.2⟩, memW f⟩ = ⟨⟨rd (T f : A), hV' _ (T f).2⟩, memW' (T f)⟩ := by
    intro f
    have e1 : (⟨⟨rd f, hV _ f.2⟩, memW f⟩ : W) = ∑ j, σ (bV.repr f j) • bW j := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, bW_apply]
      exact eqV f
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum]
    simp only [map_smul, Tc, Module.Basis.constr_basis]
    apply Subtype.ext; apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, AddSubmonoidClass.coe_finsetSum,
      SetLike.val_smul, img]
    conv_rhs => rw [← bV.sum_repr f]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, Submodule.coe_sum, Submodule.coe_smul, hsemi]
  have Tc_basis : ∀ i, Tc (bW i) = img i := fun i => by
    simp only [Tc, Module.Basis.constr_basis]
  haveI : FiniteDimensional ℂ W := Module.Finite.of_basis bW
  have Tc_ne : Tc ≠ 0 := by
    obtain ⟨f, hf⟩ : ∃ f, T f ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact hT (LinearMap.ext hc)
    have hfA : (T f : A) ≠ 0 := fun hz => hf (Subtype.ext hz)
    have li1 : LinearIndependent ℂ (fun _ : Fin 1 => rd (T f : A)) :=
      hind' 1 (fun _ => (T f : A)) (fun _ => (T f).2)
        (linearIndependent_unique_iff.mpr hfA)
    have hne : rd (T f : A) ≠ 0 := li1.ne_zero 0
    intro h0
    apply hne
    have := congrArg (fun x : W' => ((x : R) : B)) (Tc_rd f)
    simp only [h0, LinearMap.zero_apply] at this
    simpa using this.symm
  have spanLe : Submodule.span ℂ (rd '' (V : Set A)) ≤ W.map R.val.toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨⟨rd f, hV _ hf⟩, memW ⟨f, hf⟩, rfl⟩
  have hW'W : ∀ w ∈ W', (⟨h', hh'⟩ : R) * w ∈ W := by
    intro w hw
    have hle : W' ≤ W.comap (LinearMap.mulLeft ℂ (⟨h', hh'⟩ : R)) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      show (⟨h', hh'⟩ : R) * gV' i ∈ W
      obtain ⟨z, hz, hzeq⟩ := spanLe (hsub _ (bV' i).2)
      have : z = (⟨h', hh'⟩ : R) * gV' i := Subtype.ext hzeq
      rw [← this]; exact hz
    exact hle hw
  have hcommTc : ∀ x y : W, ((Tc x : R)) * (y : R) = (x : R) * (Tc y : R) := by
    let B1 : W →ₗ[ℂ] W →ₗ[ℂ] R := (LinearMap.mul ℂ R).compl₁₂ (W'.subtype ∘ₗ Tc) W.subtype
    let B2 : W →ₗ[ℂ] W →ₗ[ℂ] R := (LinearMap.mul ℂ R).compl₁₂ W.subtype (W'.subtype ∘ₗ Tc)
    have hB : B1 = B2 := by
      refine bW.ext fun i => bW.ext fun j => ?_
      simp only [B1, B2, LinearMap.compl₁₂_apply, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearMap.mul_apply', Tc_basis, bW_apply]
      apply Subtype.ext
      simp only [img, gV, Subalgebra.coe_mul, ← map_mul]
      rw [hcomm]
    intro x y
    have := LinearMap.congr_fun₂ hB x y
    simpa [B1, B2] using this
  have hhhR : (⟨h, hh⟩ : R) * ⟨h', hh'⟩ = 1 := Subtype.ext (by simpa using hhh)
  obtain ⟨a, ha, hkey⟩ := commuting_map_eq_smul_multiplier R W W' ⟨h, hh⟩ ⟨h', hh'⟩ hhhR hW'W Tc Tc_ne hcommTc
  refine ⟨a, ha, fun f => ?_⟩
  have := congrArg Subtype.val (hkey ⟨⟨rd f, hV _ f.2⟩, memW f⟩)
  rw [Tc_rd] at this
  simpa using this

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingMultiplierEqConstSmulGeneratorStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commuting_multiplier_eq_const_smul_generator_alt : ∀ (K A B : Type) [Field K] [CommRing A] [Algebra K A] [CommRing B] [Algebra ℂ B] (σ : K →+* ℂ) (rd : A →+* B), (∀ (a : K) (f : A), rd (a • f) = σ a • rd f) → ∀ (R : Subalgebra ℂ B) [IsDomain R] (V V' : Submodule K A) [FiniteDimensional K V] [FiniteDimensional K V'], (∀ f ∈ V, rd f ∈ R) → (∀ f ∈ V', rd f ∈ R) → (∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V) → LinearIndependent K b → LinearIndependent ℂ (fun i => rd (b i))) → (∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ V') → LinearIndependent K b → LinearIndependent ℂ (fun i => rd (b i))) → ∀ h h' : B, h ∈ R → h' ∈ R → h * h' = 1 → (∀ f ∈ V', h' * rd f ∈ Submodule.span ℂ (rd '' (V : Set A))) → ∀ T : V →ₗ[K] V', T ≠ 0 → (∀ f g : V, (T f : A) * (g : A) = (f : A) * (T g : A)) → ∃ a : ℂ, a ≠ 0 ∧ ∀ f : V, rd (T f) = a • (h * rd f) := by
  first | exact @GlobalTheory.commuting_multiplier_eq_const_smul_generator | exact GlobalTheory.commuting_multiplier_eq_const_smul_generator | (intros; apply GlobalTheory.commuting_multiplier_eq_const_smul_generator <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtCharSeriesCoefZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtCharSeriesCoefZero
open Filter Topology

namespace GlobalTheory.CharSeriesCoef

noncomputable def avg {Y ι : Type} [AddCommGroup Y] [Fintype ι] (w : ι → Y)
    (χ : AddChar Y ℂ) : ℂ :=
  (Fintype.card ι : ℂ)⁻¹ * ∑ i, χ (w i)

theorem norm_avg_le_one_of {ι : Type} [Fintype ι] (f : ι → ℂ) (hf : ∀ i, ‖f i‖ ≤ 1) :
    ‖(Fintype.card ι : ℂ)⁻¹ * ∑ i, f i‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with h | h
  · simp [h]
  have hc : (0:ℝ) < Fintype.card ι := by exact_mod_cast h
  rw [norm_mul, norm_inv, Complex.norm_natCast, inv_mul_le_iff₀ hc, mul_one]
  calc ‖∑ i, f i‖ ≤ ∑ i, ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : ι, (1:ℝ) := Finset.sum_le_sum (fun i _ => hf i)
    _ = Fintype.card ι := by simp

theorem avg_prod {Y ι : Type} [AddCommGroup Y] [Fintype ι] (w : ι → Y) (y : Y) (K : ℕ)
    (χ : AddChar Y ℂ) :
    avg (fun ik : ι × Fin K => w ik.1 + (ik.2 : ℕ) • y) χ
      = avg w χ * ((K : ℂ)⁻¹ * ∑ k : Fin K, χ y ^ (k : ℕ)) := by
  unfold avg
  rw [Fintype.sum_prod_type]
  simp only [AddChar.map_add_eq_mul, AddChar.map_nsmul_eq_pow]
  rw [← Finset.sum_mul_sum, Fintype.card_prod, Fintype.card_fin]
  push_cast
  rw [mul_inv]
  ring

theorem geom_avg_le {ζ : ℂ} (hζ : ζ ≠ 1) (h1 : ‖ζ‖ = 1) (K : ℕ) (hK : 0 < K) :
    ‖(K:ℂ)⁻¹ * ∑ k : Fin K, ζ ^ (k:ℕ)‖ ≤ 2 / (K * ‖ζ - 1‖) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => ζ ^ k) K, geom_sum_eq hζ K]
  have hz : 0 < ‖ζ - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hζ)
  have hKpos : (0:ℝ) < K := by exact_mod_cast hK
  have hnum : ‖ζ ^ K - 1‖ ≤ 2 := by
    calc ‖ζ ^ K - 1‖ ≤ ‖ζ ^ K‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, h1]; norm_num
  rw [norm_mul, norm_div, norm_inv, Complex.norm_natCast]
  calc (K:ℝ)⁻¹ * (‖ζ ^ K - 1‖ / ‖ζ - 1‖) ≤ (K:ℝ)⁻¹ * (2 / ‖ζ - 1‖) := by gcongr
    _ = 2 / (K * ‖ζ - 1‖) := by field_simp

theorem exists_avg {Y Ξ : Type} [AddCommGroup Y] [Zero Ξ] (e : Ξ → AddChar Y ℂ)
    (hn : ∀ a y, ‖e a y‖ = 1) (hne : ∀ a, a ≠ 0 → ∃ y, e a y ≠ 1)
    (δ : ℝ) (hδ : 0 < δ) (T : Finset Ξ) (h0 : (0:Ξ) ∉ T) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι) (w : ι → Y),
      ∀ b ∈ T, ‖avg w (e b)‖ ≤ δ := by
  classical
  revert h0
  refine Finset.induction_on T ?_ ?_
  · intro _
    exact ⟨Unit, inferInstance, inferInstance, fun _ => 0, by simp⟩
  · intro a T ha ih h0
    have ha0 : a ≠ 0 := fun h => h0 (by simp [h])
    have hT0 : (0:Ξ) ∉ T := fun h => h0 (Finset.mem_insert_of_mem h)
    obtain ⟨ι, _, _, w, hw⟩ := ih hT0
    obtain ⟨y, hy⟩ := hne a ha0
    have hz : 0 < ‖e a y - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hy)
    obtain ⟨K, hK⟩ := exists_nat_gt (2 / (δ * ‖e a y - 1‖))
    have hK0 : (0:ℝ) < K := lt_trans (by positivity) hK
    have hKn : 0 < K := by exact_mod_cast hK0
    haveI : Nonempty (Fin K) := ⟨⟨0, hKn⟩⟩
    refine ⟨ι × Fin K, inferInstance, inferInstance,
      fun ik => w ik.1 + (ik.2 : ℕ) • y, ?_⟩
    intro b hb
    rw [avg_prod, norm_mul]
    have hA : ‖avg w (e b)‖ ≤ 1 := norm_avg_le_one_of _ (fun i => (hn b _).le)
    have hG : ‖(K:ℂ)⁻¹ * ∑ k : Fin K, e b y ^ (k:ℕ)‖ ≤ 1 := by
      have := norm_avg_le_one_of (ι := Fin K) (fun k => e b y ^ (k:ℕ))
        (fun k => by rw [norm_pow, hn]; simp)
      simpa using this
    rcases Finset.mem_insert.mp hb with rfl | hbT
    · have hg := geom_avg_le hy (hn b y) K hKn
      have : 2 / (K * ‖e b y - 1‖) ≤ δ := by
        rw [div_le_iff₀ (by positivity)]
        rw [div_lt_iff₀ (by positivity)] at hK
        nlinarith
      calc ‖avg w (e b)‖ * ‖(K:ℂ)⁻¹ * ∑ k : Fin K, e b y ^ (k:ℕ)‖ ≤ 1 * δ := by
            gcongr
            exact hg.trans this
        _ = δ := one_mul δ
    · calc ‖avg w (e b)‖ * ‖(K:ℂ)⁻¹ * ∑ k : Fin K, e b y ^ (k:ℕ)‖ ≤ δ * 1 := by
            gcongr
            exact hw b hbT
        _ = δ := mul_one δ

theorem continuousAt_coef_zero {Y Ξ P : Type} [AddCommGroup Y] [Zero Ξ] [TopologicalSpace P]
    (e : Ξ → AddChar Y ℂ)
    (hn : ∀ a y, ‖e a y‖ = 1) (he0 : ∀ y, e 0 y = 1) (hne : ∀ a, a ≠ 0 → ∃ y, e a y ≠ 1)
    (c : P → Ξ → ℂ) (p0 : P) (M : Ξ → ℝ) (hM : Summable M)
    (hb : ∀ᶠ p in 𝓝 p0, ∀ a, ‖c p a‖ ≤ M a)
    (hc : ∀ y, ContinuousAt (fun p => ∑' a, e a y * c p a) p0) :
    ContinuousAt (fun p => c p 0) p0 := by
  classical
  have hM0 : ∀ a, 0 ≤ M a := fun a => (norm_nonneg _).trans (hb.self_of_nhds a)
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  set S := ∑' a, M a with hSdef
  have hS : 0 ≤ S := tsum_nonneg hM0
  obtain ⟨s, hs⟩ : ∃ s : Finset Ξ, S - ∑ a ∈ s, M a < ε / 6 := by
    have h2 := (Metric.tendsto_nhds.mp hM.hasSum) (ε / 6) (by positivity)
    obtain ⟨s, hs⟩ := h2.exists
    refine ⟨s, ?_⟩
    rw [Real.dist_eq] at hs
    linarith [neg_abs_le (∑ a ∈ s, M a - S)]
  set δ := ε / 6 / (S + 1) with hδdef
  have hδ : 0 < δ := by positivity
  have hδS : δ * S ≤ ε / 6 := by
    have : δ * (S + 1) = ε / 6 := div_mul_cancel₀ _ (by positivity)
    nlinarith
  obtain ⟨ι, _, _, w, hw⟩ := exists_avg e hn hne δ hδ (s.erase 0) (by simp)
  set α : Ξ → ℂ := fun b => avg w (e b) with hαdef
  have hα1 : ∀ b, ‖α b‖ ≤ 1 := fun b => norm_avg_le_one_of _ (fun i => (hn b _).le)
  have hα0 : α 0 = 1 := by
    simp only [hαdef, avg, he0, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero)
  let A : P → ℂ := fun p => (Fintype.card ι : ℂ)⁻¹ * ∑ i, ∑' a, e a (w i) * c p a
  have hAc : ContinuousAt A p0 :=
    continuousAt_const.mul (tendsto_finsetSum _ (fun i _ => hc (w i)))

  have key : ∀ p, (∀ a, ‖c p a‖ ≤ M a) → ‖A p - c p 0‖ ≤ δ * S + (S - ∑ a ∈ s, M a) := by
    intro p hp
    have hsum : ∀ i, HasSum (fun a => e a (w i) * c p a) (∑' a, e a (w i) * c p a) := by
      intro i
      refine (Summable.of_norm_bounded hM (fun a => ?_)).hasSum
      rw [norm_mul, hn, one_mul]; exact hp a
    have h1 : HasSum (fun a => α a * c p a) (A p) := by
      have := (hasSum_sum (s := Finset.univ) (fun i _ => hsum i)).mul_left
        ((Fintype.card ι : ℂ)⁻¹)
      have hfun : (fun a => α a * c p a)
          = fun a => (Fintype.card ι : ℂ)⁻¹ * ∑ i, e a (w i) * c p a := by
        funext a
        simp only [hαdef, avg, Finset.sum_mul, mul_assoc]
      rw [hfun]; exact this
    have h2 : HasSum (fun a : Ξ => if a = (0:Ξ) then c p 0 else 0) (c p 0) := hasSum_ite_eq (0:Ξ) (c p 0)
    have h3 : HasSum (fun a => α a * c p a - if a = 0 then c p 0 else 0) (A p - c p 0) :=
      HasSum.sub h1 h2
    have hg : HasSum (fun a => δ * M a + (M a - if a ∈ s then M a else 0))
        (δ * S + (S - ∑ a ∈ s, M a)) := by
      refine (hM.hasSum.mul_left δ).add (hM.hasSum.sub ?_)
      have : HasSum (fun a => if a ∈ s then M a else 0) (∑ b ∈ s, if b ∈ s then M b else 0) :=
        hasSum_sum_of_ne_finset_zero (fun b hb => if_neg hb)
      have e2 : (∑ b ∈ s, if b ∈ s then M b else 0) = ∑ b ∈ s, M b :=
        Finset.sum_congr rfl (fun b hb => if_pos hb)
      rw [e2] at this
      exact this
    refine h3.norm_le_of_bounded hg (fun a => ?_)
    have hMa := hM0 a
    by_cases ha : a = 0
    · subst ha
      simp only [hα0, one_mul, if_true, sub_self, norm_zero]
      split_ifs <;> nlinarith [mul_nonneg hδ.le hMa]
    · simp only [ha, if_false, sub_zero]
      by_cases has : a ∈ s
      · simp only [has, if_true, sub_self, add_zero]
        rw [norm_mul]
        have := hw a (Finset.mem_erase.mpr ⟨ha, has⟩)
        exact mul_le_mul this (hp a) (norm_nonneg _) hδ.le
      · simp only [has, if_false, sub_zero]
        rw [norm_mul]
        have : ‖α a‖ * ‖c p a‖ ≤ 1 * M a := mul_le_mul (hα1 a) (hp a) (norm_nonneg _) zero_le_one
        nlinarith
  have hAev := (Metric.tendsto_nhds.mp hAc) (ε / 3) (by positivity)
  have hp0 := key p0 hb.self_of_nhds
  filter_upwards [hb, hAev] with p hp hAp
  have hpk := key p hp
  rw [dist_eq_norm] at hAp ⊢
  have : c p 0 - c p0 0 = -(A p - c p 0) + (A p - A p0) + (A p0 - c p0 0) := by ring
  rw [this]
  calc ‖-(A p - c p 0) + (A p - A p0) + (A p0 - c p0 0)‖
      ≤ ‖-(A p - c p 0)‖ + ‖A p - A p0‖ + ‖A p0 - c p0 0‖ := norm_add₃_le
    _ < ε := by rw [norm_neg]; linarith

end GlobalTheory.CharSeriesCoef

theorem GlobalTheory.continuousAt_charSeries_coef_zero :
    ∀ {Y Ξ P : Type} [AddCommGroup Y] [Zero Ξ] [TopologicalSpace P] (e : Ξ → AddChar Y ℂ),
    (∀ a y, ‖e a y‖ = 1) → (∀ y, e 0 y = 1) → (∀ a, a ≠ 0 → ∃ y, e a y ≠ 1) →
    ∀ (c : P → Ξ → ℂ) (p0 : P) (M : Ξ → ℝ), Summable M → (∀ᶠ p in nhds p0, ∀ a, ‖c p a‖ ≤ M a) →
    (∀ y, ContinuousAt (fun p => ∑' a, e a y * c p a) p0) → ContinuousAt (fun p => c p 0) p0 :=
  fun e hn he0 hne c p0 M hM hb hc =>
    GlobalTheory.CharSeriesCoef.continuousAt_coef_zero e hn he0 hne c p0 M hM hb hc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtCharSeriesCoefZeroStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousAt_coeff_zero_of_continuousAt_char_series : ∀ {Y Ξ P : Type} [AddCommGroup Y] [Zero Ξ] [TopologicalSpace P] (e : Ξ → AddChar Y ℂ),
    (∀ a y, ‖e a y‖ = 1) → (∀ y, e 0 y = 1) → (∀ a, a ≠ 0 → ∃ y, e a y ≠ 1) →
    ∀ (c : P → Ξ → ℂ) (p0 : P) (M : Ξ → ℝ), Summable M → (∀ᶠ p in nhds p0, ∀ a, ‖c p a‖ ≤ M a) →
    (∀ y, ContinuousAt (fun p => ∑' a, e a y * c p a) p0) → ContinuousAt (fun p => c p 0) p0 := by
  first | exact @GlobalTheory.continuousAt_charSeries_coef_zero | exact GlobalTheory.continuousAt_charSeries_coef_zero | (intros; apply GlobalTheory.continuousAt_charSeries_coef_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanHeisenbergTranslatesOfVacuum
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanHeisenbergTranslatesOfVacuum
open Matrix
open scoped ComplexOrder

namespace GlobalTheory.HeisVacuum

theorem mem_span_translates_vacuum (X M : Type) [AddCommGroup X] [AddCommGroup M] [Module ℂ M]
    (β : X → X → ℂ) (ρ : X → M →ₗ[ℂ] M) (Λ : AddSubgroup X) (e : M)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z) (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hd : ∀ x, β x x = 1) (h0 : ∀ v, ρ 0 v = v)
    (hρ : ∀ x y v, ρ x (ρ y v) = β x y • ρ (x + y) v)
    (hΛ : ∀ x, x ∈ Λ ↔ ∀ a ∈ Λ, β x a ^ 2 = 1)
    (hdiv : ∀ N : ℕ, 0 < N → ∀ x : X, ∃ y : X, N • y = x)
    (hfin : ∀ N : ℕ, 0 < N → ∃ R : Set X, R.Finite ∧ ∀ t ∈ Λ, ∃ r ∈ R, ∃ u ∈ Λ, t = r + N • u)
    (he : e ≠ 0) (hε : ∀ u ∈ Λ, ∃ ε : ℂ, ρ u e = ε • e) (h2 : ∀ u ∈ Λ, ρ (2 • u) e = e)
    (hvac : ∀ v : M, (∀ u ∈ Λ, ∀ ε : ℂ, ρ u e = ε • e → ρ u v = ε • v) → ∃ c : ℂ, v = c • e)
    (v : M) (hv : ∃ N : ℕ, 0 < N ∧ ∀ u ∈ Λ, ρ (N • u) v = v) :
    v ∈ Submodule.span ℂ (Set.range fun x => ρ x e) := by
  classical
  obtain ⟨N, hN, hv⟩ := hv
  have hsym : ∀ x y, β x y * β y x = 1 := by
    intro x y
    have := hd (x + y)
    rw [hl, hr, hr, hd, hd] at this
    simpa using this
  have hne : ∀ x y, β x y ≠ 0 := fun x y => left_ne_zero_of_mul_eq_one (hsym x y)
  have hz1 : ∀ y, β 0 y = 1 := by
    intro y
    have := hl 0 0 y
    rw [add_zero] at this
    exact (mul_eq_left₀ (hne 0 y)).1 this.symm
  have hz2 : ∀ y, β y 0 = 1 := by
    intro y
    have := hsym y 0
    rwa [hz1, mul_one] at this
  have hp1 : ∀ (n : ℕ) x y, β (n • x) y = β x y ^ n := by
    intro n x y
    induction n with
    | zero => simp [hz1]
    | succ n ih => rw [succ_nsmul, hl, ih, pow_succ]
  have hp2 : ∀ (n : ℕ) x y, β x (n • y) = β x y ^ n := by
    intro n x y
    induction n with
    | zero => simp [hz2]
    | succ n ih => rw [succ_nsmul, hr, ih, pow_succ]
  have hcomm : ∀ x y w, ρ x (ρ y w) = β x y ^ 2 • ρ y (ρ x w) := by
    intro x y w
    rw [hρ, hρ, smul_smul, add_comm y x, pow_two, mul_assoc, hsym, mul_one]
  have hinv : ∀ t w, ρ t (ρ (-t) w) = w := by
    intro t w
    have := hr t t (-t)
    rw [add_neg_cancel, hz2, hd, one_mul] at this
    rw [hρ, add_neg_cancel, h0, ← this, one_smul]
  choose! ε hε using hε
  have huniq : ∀ u ∈ Λ, ∀ c : ℂ, ρ u e = c • e → c = ε u := by
    intro u hu c hc
    rw [hε u hu] at hc
    exact (smul_left_injective ℂ he hc).symm
  have hεne : ∀ u ∈ Λ, ε u ≠ 0 := by
    intro u hu h
    have := hinv (-u) e
    rw [neg_neg, hε u hu, h, zero_smul, map_zero] at this
    exact he this.symm
  have hεmul : ∀ u ∈ Λ, ∀ u' ∈ Λ, ε u * ε u' = β u u' * ε (u + u') := by
    intro u hu u' hu'
    have := hρ u u' e
    rw [hε u' hu', map_smul, hε u hu, hε _ (Λ.add_mem hu hu'), smul_smul, smul_smul, mul_comm] at this
    exact smul_left_injective ℂ he this
  let A : Λ → M → M := fun u w => (ε u)⁻¹ • ρ u w
  have hA : ∀ (u u' : Λ) w, A u (A u' w) = A (u + u') w := by
    intro u u' w
    simp only [A, map_smul, hρ, smul_smul, AddSubgroup.coe_add]
    congr 1
    have h1 := hεmul u u.2 u' u'.2
    have h3 := hεne u u.2
    have h4 := hεne u' u'.2
    have h5 := hεne _ (Λ.add_mem u.2 u'.2)
    field_simp
    rw [h1, mul_comm]
  have hA0 : ∀ w, A 0 w = w := by
    intro w
    have : (1 : ℂ) = ε 0 := huniq 0 Λ.zero_mem 1 (by rw [h0, one_smul])
    simp [A, h0, ← this]
  set K : ℕ := 2 * N with hK
  have hKpos : 0 < K := by omega
  have hεK : ∀ u ∈ Λ, ε (K • u) = 1 := by
    intro u hu
    refine (huniq _ (Λ.nsmul_mem hu K) 1 ?_).symm
    rw [one_smul, hK, mul_comm, mul_nsmul]
    exact h2 _ (Λ.nsmul_mem hu N)
  have hvK : ∀ u ∈ Λ, ρ (K • u) v = v := by
    intro u hu
    rw [hK, mul_nsmul]
    exact hv _ (Λ.nsmul_mem hu 2)
  let H : AddSubgroup Λ := (nsmulAddMonoidHom K : Λ →+ Λ).range
  have hQ : Finite (Λ ⧸ H) := by
    obtain ⟨R, hR, hR'⟩ := hfin K hKpos
    have : Finite {x : Λ // (x : X) ∈ R} := by
      have : Finite R := hR
      exact Finite.of_injective (fun x : {x : Λ // (x : X) ∈ R} => (⟨x.1, x.2⟩ : R))
        (fun a b h => Subtype.ext (Subtype.ext (congrArg (fun z : R => (z : X)) h)))
    refine Finite.of_surjective (fun x : {x : Λ // (x : X) ∈ R} => (QuotientAddGroup.mk x.1 : Λ ⧸ H)) ?_
    intro q
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨r, hr, u, hu, htu⟩ := hR' t t.2
    have hrΛ : r ∈ Λ := by
      have : r = t - K • u := by rw [htu]; abel
      rw [this]
      exact Λ.sub_mem t.2 (Λ.nsmul_mem hu K)
    refine ⟨⟨⟨r, hrΛ⟩, hr⟩, ?_⟩
    refine QuotientAddGroup.eq.2 ⟨⟨u, hu⟩, Subtype.ext ?_⟩
    simp [htu]
  have := Fintype.ofFinite (Λ ⧸ H)
  have hwell : ∀ w, (∀ u ∈ Λ, ρ (K • u) w = w) → ∀ x y : Λ,
      (QuotientAddGroup.mk x : Λ ⧸ H) = QuotientAddGroup.mk y → A x w = A y w := by
    intro w hw x y hxy
    obtain ⟨u, hu⟩ := QuotientAddGroup.eq.1 hxy
    have h1 : y = x + K • u := by
      have : K • u = -x + y := hu
      rw [this]; abel
    have h3 : A (K • u) w = w := by
      simp only [A, AddSubgroup.coe_nsmul, hεK u u.2, hw u u.2, inv_one, one_smul]
    rw [h1, ← hA, h3]
  have hAsum : ∀ (u : Λ) (f : Λ ⧸ H → M), A u (∑ q, f q) = ∑ q, A u (f q) := by
    intro u f
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [A, map_sum, Finset.smul_sum]
  have hP : ∀ w, (∀ u ∈ Λ, ρ (K • u) w = w) → ∃ c : ℂ, (∑ q : Λ ⧸ H, A q.out w) = c • e := by
    intro w hw
    apply hvac
    intro u hu c hc
    rw [huniq u hu c hc]
    have h1 : A ⟨u, hu⟩ (∑ q : Λ ⧸ H, A q.out w) = ∑ q : Λ ⧸ H, A q.out w := by
      rw [hAsum]
      refine Fintype.sum_equiv (Equiv.addLeft (QuotientAddGroup.mk ⟨u, hu⟩ : Λ ⧸ H)) _ _ ?_
      intro q
      rw [hA]
      apply hwell w hw
      simp
    conv_rhs => rw [← h1]
    simp only [A, smul_smul, mul_inv_cancel₀ (hεne u hu), one_smul]
  let Tg : AddSubgroup X := Λ.comap (nsmulAddMonoidHom K : X →+ X)
  have hTg : ∀ t, t ∈ Tg ↔ K • t ∈ Λ := fun t => Iff.rfl
  let S := Submodule.span ℂ (Set.range fun x => ρ x e)
  have hmem : ∀ t ∈ Tg, (∑ q : Λ ⧸ H, β t (q.out : Λ) ^ 2 • A q.out v) ∈ S := by
    intro t ht
    obtain ⟨c, hc⟩ := hP (ρ (-t) v) (by
      intro u hu
      rw [hcomm, hvK u hu, hp1, ← hp2, (hΛ u).1 hu _ ((hTg _).1 (Tg.neg_mem ht)), one_smul])
    have h1 := congrArg (ρ t) hc
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_smul] at h1
    have h3 : c • ρ t e ∈ S := S.smul_mem c (Submodule.subset_span ⟨t, rfl⟩)
    rw [← h1] at h3
    convert h3 using 2 with q
    simp only [A, map_smul]
    rw [hcomm t, hinv, smul_comm]
  let χ : Λ ⧸ H → (Multiplicative Tg →* ℂ) := fun q =>
    { toFun := fun t => β (t.toAdd : Tg) (q.out : Λ) ^ 2
      map_one' := by simp [hz1]
      map_mul' := by intro a b; simp [hl, mul_pow] }
  have hχ : Function.Injective χ := by
    intro q q' h
    have h1 : ∀ t ∈ Tg, β t (q.out : Λ) ^ 2 = β t (q'.out : Λ) ^ 2 := fun t ht =>
      DFunLike.congr_fun h (Multiplicative.ofAdd ⟨t, ht⟩)
    obtain ⟨y, hy⟩ := hdiv K hKpos (-((q.out : Λ) : X) + (q'.out : Λ))
    have hyΛ : y ∈ Λ := by
      rw [hΛ]
      intro a ha
      obtain ⟨t, rfl⟩ := hdiv K hKpos a
      have h3 := h1 t ha
      have h4 : ((q'.out : Λ) : X) = (q.out : Λ) + K • y := by rw [hy]; abel
      rw [h4, hr, mul_pow, hp2, ← hp1 K] at h3
      have h5 : β (K • t) y ^ 2 = 1 :=
        (mul_eq_left₀ (pow_ne_zero 2 (hne _ _))).1 h3.symm
      have h6 := congrArg (· ^ 2) (hsym y (K • t))
      simpa [mul_pow, h5] using h6
    rw [← QuotientAddGroup.out_eq' q, ← QuotientAddGroup.out_eq' q']
    exact QuotientAddGroup.eq.2 ⟨⟨y, hyΛ⟩, Subtype.ext (by simpa using hy)⟩
  have hli : LinearIndependent ℂ (fun q => (χ q : Multiplicative Tg → ℂ)) :=
    (linearIndependent_monoidHom (Multiplicative Tg) ℂ).comp χ hχ
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  have h1 := Fintype.linearIndependent_iff.1 hli (fun q => φ (S.mkQ (A q.out v))) (by
    funext t
    have h3 := (Submodule.Quotient.mk_eq_zero S).2 (hmem _ (t.toAdd).2)
    have h4 := congrArg φ h3
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Submodule.mkQ_apply, map_sum, map_sum, map_zero] at h4
    simp only [map_smul, smul_eq_mul] at h4
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [← h4]
    exact Finset.sum_congr rfl fun q _ => mul_comm _ _) 0
  have h3 : A (0 : Λ ⧸ H).out v = v := by
    rw [hwell v hvK _ 0 (by simp), hA0]
  simpa [h3] using h1

end GlobalTheory.HeisVacuum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSpanHeisenbergTranslatesOfVacuumStatement
open Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_heisenberg_translates_of_vacuum : ∀ (X M : Type) [AddCommGroup X] [AddCommGroup M] [Module ℂ M] (β : X → X → ℂ) (ρ : X → M →ₗ[ℂ] M) (Λ : AddSubgroup X) (e : M), (∀ x y z, β (x + y) z = β x z * β y z) → (∀ x y z, β x (y + z) = β x y * β x z) → (∀ x, β x x = 1) → (∀ v, ρ 0 v = v) → (∀ x y v, ρ x (ρ y v) = β x y • ρ (x + y) v) → (∀ x, x ∈ Λ ↔ ∀ a ∈ Λ, β x a ^ 2 = 1) → (∀ N : ℕ, 0 < N → ∀ x : X, ∃ y : X, N • y = x) → (∀ N : ℕ, 0 < N → ∃ R : Set X, R.Finite ∧ ∀ t ∈ Λ, ∃ r ∈ R, ∃ u ∈ Λ, t = r + N • u) → e ≠ 0 → (∀ u ∈ Λ, ∃ ε : ℂ, ρ u e = ε • e) → (∀ u ∈ Λ, ρ (2 • u) e = e) → (∀ v : M, (∀ u ∈ Λ, ∀ ε : ℂ, ρ u e = ε • e → ρ u v = ε • v) → ∃ c : ℂ, v = c • e) → ∀ v : M, (∃ N : ℕ, 0 < N ∧ ∀ u ∈ Λ, ρ (N • u) v = v) → v ∈ Submodule.span ℂ (Set.range fun x => ρ x e) := by
  first | exact @GlobalTheory.HeisVacuum.mem_span_translates_vacuum | exact GlobalTheory.HeisVacuum.mem_span_translates_vacuum | (intros; apply GlobalTheory.HeisVacuum.mem_span_translates_vacuum <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleAtHeightOnePrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleAtHeightOnePrimes
open IsLocalRing

namespace GlobalTheory.PurityDisc
open TensorProduct

theorem trace_one_tmul (R A S : Type) [CommRing R] [CommRing A] [Algebra R A] [CommRing S]
    [Algebra R S] [Module.Free R A] [Module.Finite R A] (a : A) :
    Algebra.trace S (S ⊗[R] A) (1 ⊗ₜ a) = algebraMap R S (Algebra.trace R A a) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← LinearMap.trace_baseChange, Algebra.baseChange_lmul]

theorem discr_baseChange (R A S : Type) [CommRing R] [CommRing A] [Algebra R A] [CommRing S]
    [Algebra R S] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) :
    Algebra.discr S (Algebra.TensorProduct.basis S b) = algebraMap R S (Algebra.discr R b) := by
  haveI := Module.Free.of_basis b
  haveI := Module.Finite.of_basis b
  rw [Algebra.discr_def, Algebra.discr_def, RingHom.map_det]
  congr 1
  ext i j
  simp [Algebra.traceMatrix_apply, Algebra.traceForm_apply, Algebra.TensorProduct.basis_apply,
    Algebra.TensorProduct.tmul_mul_tmul, trace_one_tmul]

theorem trace_pi (K σ : Type) [Field K] [Fintype σ] [DecidableEq σ] (z : σ → K) :
    Algebra.trace K (σ → K) z = ∑ i, z i := by
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun K σ), Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, Pi.single_apply]

theorem traceForm_pi_nondegenerate (K σ : Type) [Field K] [Fintype σ] [DecidableEq σ] :
    (Algebra.traceForm K (σ → K)).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · funext i
    have h := hx (Pi.single i 1)
    rw [Algebra.traceForm_apply, trace_pi] at h
    simpa [Pi.single_apply] using h
  · funext i
    have h := hx (Pi.single i 1)
    rw [Algebra.traceForm_apply, trace_pi] at h
    simpa [Pi.single_apply] using h

theorem discr_ne_zero_of_etale (K A : Type) [Field K] [CommRing A] [Algebra K A] {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K A) [Algebra.Etale K A] :
    Algebra.discr K b ≠ 0 := by
  classical
  let L := AlgebraicClosure K
  let e := Algebra.FormallyEtale.equivPiOfIsSepClosed L (L ⊗[K] A)
  haveI : Module.Finite L (L ⊗[K] A) := Module.Finite.of_basis (Algebra.TensorProduct.basis L b)
  haveI : IsArtinianRing (L ⊗[K] A) := isArtinian_of_tower L inferInstance
  haveI : Fintype (PrimeSpectrum (L ⊗[K] A)) := Fintype.ofFinite _
  let c := (Algebra.TensorProduct.basis L b).map e.toLinearEquiv
  have hc : Algebra.discr L c ≠ 0 := by
    have h := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero c).mp
      (traceForm_pi_nondegenerate L (PrimeSpectrum (L ⊗[K] A)))
    rw [Algebra.discr_def]
    convert h using 2
    ext i j
    rw [Algebra.traceForm_toMatrix, Algebra.traceMatrix_apply, Algebra.traceForm_apply]
  have h2 : Algebra.discr L c = Algebra.discr L (Algebra.TensorProduct.basis L b) := by
    rw [Algebra.discr_eq_discr_of_algEquiv (Algebra.TensorProduct.basis L b) e]
    rfl
  rw [h2, discr_baseChange] at hc
  intro h
  exact hc (by rw [h, map_zero])

theorem exists_dual (R A : Type) [CommRing R] [CommRing A] [Algebra R A] {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (h : IsUnit (Algebra.discr R b)) :
    ∃ d : ι → A, ∀ i j, Algebra.trace R A (b i * d j) = if i = j then 1 else 0 := by
  classical
  set M := Algebra.traceMatrix R b
  have hM : IsUnit M.det := by rwa [Algebra.discr_def] at h
  refine ⟨fun j => ∑ k, M⁻¹ k j • b k, fun i j => ?_⟩
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hM
  have := congrFun (congrFun h1 i) j
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← this, Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_smul_comm, LinearMap.map_smul, smul_eq_mul, mul_comm]
  simp [M, Algebra.traceMatrix_apply, Algebra.traceForm_apply]

theorem formallyUnramified_of_dual (R A : Type) [CommRing R] [CommRing A] [Algebra R A] {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (d : ι → A)
    (hd : ∀ i j, Algebra.trace R A (b i * d j) = if i = j then 1 else 0) :
    Algebra.FormallyUnramified R A := by
  classical
  haveI := Module.Free.of_basis b
  haveI := Module.Finite.of_basis b
  set T := Algebra.trace R A

  have hrepr : ∀ (z : A) (i : ι), b.repr z i = T (z * d i) := by
    intro z i
    conv_rhs => rw [← b.sum_repr z]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_mul, map_sum]
    simp_rw [smul_mul_assoc, LinearMap.map_smul, hd, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp

  have hnd : ∀ u : A, (∀ k, T (u * b k) = 0) → u = 0 := by
    intro u hu
    rw [← b.sum_repr u]
    refine Finset.sum_eq_zero fun j _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hrepr, ← b.sum_repr (d j), Finset.mul_sum, map_sum]
    simp_rw [mul_smul_comm, LinearMap.map_smul, hu, smul_zero, Finset.sum_const_zero, zero_smul]

  have hexp : ∀ z : A, ∑ i, T (z * b i) • d i = z := by
    intro z
    rw [← sub_eq_zero]
    refine hnd _ fun k => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sub_mul, map_sub, Finset.sum_mul, map_sum]
    simp_rw [smul_mul_assoc, LinearMap.map_smul, mul_comm (d _) (b k), hd, smul_eq_mul,
      mul_ite, mul_one, mul_zero]
    simp
  rw [Algebra.FormallyUnramified.iff_exists_tensorProduct]
  refine ⟨∑ i, b i ⊗ₜ[R] d i, fun s => ?_, ?_⟩
  · rw [sub_mul, sub_eq_zero, Finset.mul_sum, Finset.mul_sum]
    simp_rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    symm
    calc ∑ i, (s * b i) ⊗ₜ[R] d i
        = ∑ i, ∑ j, (T (s * b i * d j) • b j) ⊗ₜ[R] d i := by
          refine Finset.sum_congr rfl fun i _ => ?_
          conv_lhs => rw [← b.sum_repr (s * b i)]
          rw [TensorProduct.sum_tmul]
          simp_rw [hrepr]
      _ = ∑ j, b j ⊗ₜ[R] (∑ i, T ((s * d j) * b i) • d i) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [TensorProduct.tmul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [TensorProduct.smul_tmul]
          congr 2
          ring_nf
      _ = ∑ j, b j ⊗ₜ[R] (s * d j) := by simp_rw [hexp]
  · rw [map_sum]
    simp_rw [Algebra.TensorProduct.lmul'_apply_tmul]
    rw [← sub_eq_zero]
    refine hnd _ fun k => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [sub_mul, one_mul, map_sub, sub_eq_zero, Finset.sum_mul, map_sum]
    rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, Algebra.leftMulMatrix_eq_repr_mul, hrepr]
    congr 1
    ring

theorem etale_of_isUnit_discr (R A : Type) [CommRing R] [CommRing A] [Algebra R A] {ι : Type}
    [Fintype ι] [DecidableEq ι] (b : Module.Basis ι R A) (h : IsUnit (Algebra.discr R b)) :
    Algebra.Etale R A := by
  haveI := Module.Free.of_basis b
  haveI := Module.Finite.of_basis b
  obtain ⟨d, hd⟩ := exists_dual R A b h
  haveI := formallyUnramified_of_dual R A b d hd
  haveI : Module.FinitePresentation R A := Module.finitePresentation_of_projective R A
  haveI : Algebra.FinitePresentation R A := inferInstance
  exact Algebra.Etale.of_formallyUnramified_of_flat

theorem exists_height_one_mem (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] {x : R}
    (hx : x ≠ 0) (hu : ¬ IsUnit x) : ∃ P : Ideal R, P.IsPrime ∧ P.height = 1 ∧ x ∈ P := by
  have hne : Ideal.span {x} ≠ ⊤ := by
    rwa [Ne, Ideal.span_singleton_eq_top]
  obtain ⟨M, hM, hxM⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨P, hmin, -⟩ := Ideal.exists_minimalPrimes_le hxM
  have hP : P.IsPrime := hmin.1.1
  have hxP : x ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hmin.1.2
  have : (Ideal.span {x}).IsPrincipal := ⟨⟨x, rfl⟩⟩
  have h1 : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hmin
  have hP0 : P ≠ ⊥ := fun h => hx (by rw [h] at hxP; exact hxP)
  have h0 : P.height ≠ 0 := fun h => hP0 (Ideal.height_eq_zero_iff_eq_bot.mp h)
  exact ⟨P, hP, le_antisymm h1 (Order.one_le_iff_ne_zero.mpr h0), hxP⟩

theorem etale_of_etale_height_one : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A],
    ¬ IsField R →
    (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → Algebra.Etale (Localization.AtPrime p)
      (TensorProduct R (Localization.AtPrime p) A)) → Algebra.Etale R A := by
  intro R A _ _ _ _ _ _ _ _ hR hp
  classical
  let b := Module.Free.chooseBasis R A
  have key : ∀ p : Ideal R, p.IsPrime → p.height = 1 → Algebra.discr R b ∉ p := by
    intro p hp' h1
    haveI := hp'
    haveI := hp p h1
    let Rp := Localization.AtPrime p
    let κ := ResidueField Rp
    have h := discr_ne_zero_of_etale κ (κ ⊗[Rp] (Rp ⊗[R] A))
      (Algebra.TensorProduct.basis κ (Algebra.TensorProduct.basis Rp b))
    rw [discr_baseChange, discr_baseChange] at h
    have hu : IsUnit (algebraMap R Rp (Algebra.discr R b)) := by
      by_contra hn
      exact h ((residue_eq_zero_iff _).mpr ((mem_maximalIdeal _).mpr hn))
    exact (IsLocalization.AtPrime.isUnit_to_map_iff Rp p _).mp hu
  have hd : IsUnit (Algebra.discr R b) := by
    by_contra hn
    by_cases h0 : Algebra.discr R b = 0
    · obtain ⟨y, hy0, hyu⟩ : ∃ y : R, y ≠ 0 ∧ ¬ IsUnit y := by
        by_contra H
        push_neg at H
        exact hR ⟨exists_pair_ne R, mul_comm, fun {a} ha => (H a ha).exists_right_inv⟩
      obtain ⟨P, hP, h1, hyP⟩ := exists_height_one_mem R hy0 hyu
      exact key P hP h1 (h0 ▸ P.zero_mem)
    · obtain ⟨P, hP, h1, hdP⟩ := exists_height_one_mem R h0 hn
      exact key P hP h1 hdP
  exact etale_of_isUnit_discr R A b hd

end GlobalTheory.PurityDisc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOfEtaleAtHeightOnePrimesStatement
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_of_etale_at_height_one_primes : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] [CommRing A] [Algebra R A] [Module.Free R A] [Module.Finite R A], ¬ IsField R → (∀ (p : Ideal R) [p.IsPrime], p.height = 1 → Algebra.Etale (Localization.AtPrime p) (TensorProduct R (Localization.AtPrime p) A)) → Algebra.Etale R A := by
  first | exact @GlobalTheory.PurityDisc.etale_of_etale_height_one | exact GlobalTheory.PurityDisc.etale_of_etale_height_one | (intros; apply GlobalTheory.PurityDisc.etale_of_etale_height_one <;> assumption)
end
end
