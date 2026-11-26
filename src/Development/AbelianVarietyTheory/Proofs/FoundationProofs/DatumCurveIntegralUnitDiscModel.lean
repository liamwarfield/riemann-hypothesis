module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralJAndAlgebraicData
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsogenyNumeratorCoeffNormLeOne
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormXLeOneOfNsmulEqZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TorsionPointTransportEmbedding
namespace GlobalTheory

open _root_.WeierstrassCurve

theorem nsmul_some_map_eq_zero_iff {F K : Type} [Field F] [Field K] [DecidableEq F] [DecidableEq K]
    (i : F →+* K) (W : WeierstrassCurve F) (x y : F) (N : ℕ)
    (h₀ : W.toAffine.Nonsingular x y) (h : (W.map i).toAffine.Nonsingular (i x) (i y)) :
    N • (Affine.Point.some (i x) (i y) h) = 0 ↔ N • (Affine.Point.some x y h₀) = 0 := by
  letI : Algebra F K := i.toAlgebra
  let φ : W.toAffine.Point →+ (W.map i).toAffine.Point :=
    Affine.Point.map (W' := W.toAffine) (Algebra.ofId F K)
  have hφ : Function.Injective φ := Affine.Point.map_injective (W' := W.toAffine) (Algebra.ofId F K)
  have e : φ (Affine.Point.some x y h₀) = Affine.Point.some (i x) (i y) h := rfl
  rw [← e, ← map_nsmul, map_eq_zero_iff φ hφ]

theorem torsion_point_transport_embedding :
    ∀ (F K K' : Type) [Field F] [Field K] [Field K'] [DecidableEq K] [DecidableEq K'] (i : F →+* K) (j : F →+* K') (A B x y : F) (N : ℕ) (h : (⟨0, 0, 0, i A, i B⟩ : WeierstrassCurve K).toAffine.Nonsingular (i x) (i y)), N • (WeierstrassCurve.Affine.Point.some (i x) (i y) h) = 0 → ∃ h' : (⟨0, 0, 0, j A, j B⟩ : WeierstrassCurve K').toAffine.Nonsingular (j x) (j y), N • (WeierstrassCurve.Affine.Point.some (j x) (j y) h') = 0 := by
  intro F K K' _ _ _ _ _ i j A B x y N
  classical
  let W : WeierstrassCurve F := ⟨0, 0, 0, A, B⟩
  have ei : (⟨0, 0, 0, i A, i B⟩ : WeierstrassCurve K) = W.map i := by
    ext <;> simp [W, WeierstrassCurve.map]
  have ej : (⟨0, 0, 0, j A, j B⟩ : WeierstrassCurve K') = W.map j := by
    ext <;> simp [W, WeierstrassCurve.map]
  rw [ei, ej]
  intro h hN
  have h₀ : W.toAffine.Nonsingular x y := (W.toAffine.map_nonsingular i.injective x y).mp h
  have h' : (W.map j).toAffine.Nonsingular (j x) (j y) :=
    (W.toAffine.map_nonsingular j.injective x y).mpr h₀
  exact ⟨h', (nsmul_some_map_eq_zero_iff j W x y N h₀ h').mpr
    ((nsmul_some_map_eq_zero_iff i W x y N h₀ h).mp hN)⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRelationGradient
open MvPolynomial

namespace GlobalTheory
namespace UnramifiedHensel

theorem exists_relation_gradient {R A k ι : Type} [CommRing R] [CommRing A] [Field k]
    [Fintype ι] [DecidableEq ι] (ev : MvPolynomial ι R →+* A) (hev : Function.Surjective ev)
    (red : A →+* k) (hred : ∀ c : k, ∃ w : R, red (ev (C w)) = c)
    (h : ∀ φ : A →+* DualNumber k, (∀ a, (φ a).fst = red a) → (∀ w, (φ (ev (C w))).snd = 0) →
      ∀ i, (φ (ev (X i))).snd = 0) (i : ι) :
    ∃ G : MvPolynomial ι R, ev G = 0 ∧
      ∀ j, red (ev (pderiv j G)) = if j = i then 1 else 0 := by
  let Γ : Submodule k (ι → k) :=
    { carrier := {γ | ∃ G : MvPolynomial ι R, ev G = 0 ∧ ∀ j, red (ev (pderiv j G)) = γ j}
      add_mem' := by
        rintro a b ⟨G, hG, ha⟩ ⟨H, hH, hb⟩
        exact ⟨G + H, by simp [hG, hH], fun j => by simp [ha, hb]⟩
      zero_mem' := ⟨0, by simp, fun j => by simp⟩
      smul_mem' := by
        rintro c a ⟨G, hG, ha⟩
        obtain ⟨w, hw⟩ := hred c
        refine ⟨C w * G, by simp [hG], fun j => ?_⟩
        rw [pderiv_C_mul]
        simp [ha, hw] }
  suffices hΓ : Γ = ⊤ by
    have : (fun j => if j = i then (1 : k) else 0) ∈ Γ := by rw [hΓ]; trivial
    exact this
  by_contra hne
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.2 hne)
    inferInstance
  let v : ι → k := fun j => f (Pi.single j 1)
  have hfv : ∀ γ : ι → k, f γ = ∑ j, γ j * v j := by
    intro γ
    conv_lhs => rw [pi_eq_sum_univ' γ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [v, map_sum]
  let ψ : MvPolynomial ι R →+* DualNumber k :=
    eval₂Hom ((TrivSqZeroExt.inlHom k k).comp (red.comp (ev.comp C)))
      (fun j => (TrivSqZeroExt.inl (red (ev (X j))) + TrivSqZeroExt.inr (v j) : DualNumber k))
  have hψ : ∀ F, (ψ F).fst = red (ev F) ∧
      (ψ F).snd = ∑ j, red (ev (pderiv j F)) * v j := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C a => simp [ψ]
    | add p q hp hq => simp [hp.1, hp.2, hq.1, hq.2, add_mul, Finset.sum_add_distrib]
    | mul_X p n hp =>
      have h1 : (ψ (X n)).fst = red (ev (X n)) := by simp [ψ]
      have h2 : (ψ (X n)).snd = v n := by simp [ψ]
      refine ⟨by simp [hp.1, h1], ?_⟩
      rw [map_mul, DualNumber.snd_mul, hp.1, hp.2, h1, h2]
      have : ∀ j, red (ev (pderiv j (p * X n))) * v j =
          red (ev (pderiv j p)) * v j * red (ev (X n)) +
            (if j = n then red (ev p) * v n else 0) := by
        intro j
        rw [pderiv_mul, pderiv_X]
        by_cases hj : j = n
        · subst hj; simp; ring
        · simp [hj, Pi.single_apply, Ne.symm hj]; ring
      simp only [this, Finset.sum_add_distrib, Finset.sum_mul]
      simp [add_comm]
  have hker : RingHom.ker ev ≤ RingHom.ker ψ := by
    intro F hF
    rw [RingHom.mem_ker] at hF ⊢
    ext
    · simp [(hψ F).1, hF]
    · rw [(hψ F).2, ← hfv (fun j => red (ev (pderiv j F)))]
      have : f (fun j => red (ev (pderiv j F))) ∈ Γ.map f :=
        Submodule.mem_map_of_mem ⟨F, hF, fun _ => rfl⟩
      rw [hf] at this
      simpa using this
  let φ : A →+* DualNumber k := ev.liftOfSurjective hev ⟨ψ, hker⟩
  have hφ : ∀ F, φ (ev F) = ψ F := fun F => RingHom.liftOfSurjective_comp_apply _ _ _ F
  have hv := h φ (fun a => by obtain ⟨F, rfl⟩ := hev a; rw [hφ, (hψ F).1])
    (fun w => by rw [hφ, (hψ _).2]; simp)
  apply hf0
  ext j
  have := hv j
  rw [hφ] at this
  have h2 : (ψ (X j)).snd = v j := by simp [ψ]
  simpa [v, h2] using this

section
variable {K : Type} [NormedField K] [IsUltrametricDist K] {R ι : Type} [CommRing R]

theorem norm_eval_le_one (c : R →+* K) (hc : ∀ w, ‖c w‖ ≤ 1) (x : ι → K) (hx : ∀ i, ‖x i‖ ≤ 1)
    (G : MvPolynomial ι R) : ‖eval₂ c x G‖ ≤ 1 := by
  induction G using MvPolynomial.induction_on with
  | C a => simpa using hc a
  | add p q hp hq =>
    rw [eval₂_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hp hq)
  | mul_X p n hp =>
    rw [eval₂_mul, eval₂_X, norm_mul]
    exact mul_le_one₀ hp (norm_nonneg _) (hx n)

theorem norm_sum_le_of_le [Fintype ι] (a : ι → K) {r : ℝ} (hr : 0 ≤ r) (ha : ∀ i, ‖a i‖ ≤ r) :
    ‖∑ i, a i‖ ≤ r :=
  IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hr (fun i _ => ha i)

theorem taylor_bound [Fintype ι] [DecidableEq ι] (c : R →+* K) (hc : ∀ w, ‖c w‖ ≤ 1)
    (x y : ι → K) (hx : ∀ i, ‖x i‖ ≤ 1) (hy : ∀ i, ‖y i‖ ≤ 1) {r : ℝ} (hr : 0 ≤ r)
    (hxy : ∀ i, ‖y i - x i‖ ≤ r) (G : MvPolynomial ι R) :
    ‖eval₂ c y G - eval₂ c x G - ∑ j, eval₂ c x (pderiv j G) * (y j - x j)‖ ≤ r * r := by
  induction G using MvPolynomial.induction_on with
  | C a => simpa using mul_nonneg hr hr
  | add p q hp hq =>
    have : eval₂ c y (p + q) - eval₂ c x (p + q) -
        ∑ j, eval₂ c x (pderiv j (p + q)) * (y j - x j) =
        (eval₂ c y p - eval₂ c x p - ∑ j, eval₂ c x (pderiv j p) * (y j - x j)) +
        (eval₂ c y q - eval₂ c x q - ∑ j, eval₂ c x (pderiv j q) * (y j - x j)) := by
      simp only [map_add (f := _), eval₂_add, add_mul, Finset.sum_add_distrib]; ring
    rw [this]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hp hq)
  | mul_X p n hp =>
    have h1 : ∀ j, eval₂ c x (pderiv j (p * X n)) * (y j - x j) =
        eval₂ c x (pderiv j p) * (y j - x j) * x n +
          (if j = n then eval₂ c x p * (y n - x n) else 0) := by
      intro j
      rw [pderiv_mul, pderiv_X]
      by_cases hj : j = n
      · subst hj; simp [eval₂_mul]; ring
      · simp [hj, Pi.single_apply, Ne.symm hj, eval₂_mul]; ring
    have hL : ‖∑ j, eval₂ c x (pderiv j p) * (y j - x j)‖ ≤ r := by
      refine norm_sum_le_of_le _ hr fun j => ?_
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (norm_eval_le_one c hc x hx _)).trans (hxy j)
    have : eval₂ c y (p * X n) - eval₂ c x (p * X n) -
        ∑ j, eval₂ c x (pderiv j (p * X n)) * (y j - x j) =
        y n * (eval₂ c y p - eval₂ c x p - ∑ j, eval₂ c x (pderiv j p) * (y j - x j)) +
        (y n - x n) * ∑ j, eval₂ c x (pderiv j p) * (y j - x j) := by
      simp only [h1, Finset.sum_add_distrib, ← Finset.sum_mul, eval₂_mul, eval₂_X]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hy n)).trans hp
    · rw [norm_mul]
      exact mul_le_mul (hxy n) hL (norm_nonneg _) hr

theorem mem_of_gradient [Fintype ι] [DecidableEq ι] (W : Subring K) (hW : IsClosed (W : Set K))
    (hc : ∀ w ∈ W, ‖w‖ ≤ 1) (x : ι → K) (hx : ∀ i, ‖x i‖ ≤ 1)
    (h0 : ∀ i, ∃ w ∈ W, ‖x i - w‖ < 1) (G : ι → MvPolynomial ι W)
    (hG : ∀ i, eval₂ W.subtype x (G i) = 0)
    (hd : ∀ i j, ‖(if j = i then 1 else 0) - eval₂ W.subtype x (pderiv j (G i))‖ < 1) (i : ι) :
    x i ∈ W := by
  have hc' : ∀ w : W, ‖W.subtype w‖ ≤ 1 := fun w => hc w w.2
  choose y0 hy0W hy0 using h0
  obtain ⟨ρ, hρ0, hρ1, hρy, hρd⟩ : ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ (∀ i, ‖y0 i - x i‖ ≤ ρ) ∧
      ∀ i j, ‖(if j = i then 1 else 0) - eval₂ W.subtype x (pderiv j (G i))‖ ≤ ρ := by
    refine ⟨max ‖fun i => y0 i - x i‖
      ‖fun i j => (if j = i then 1 else 0) - eval₂ W.subtype x (pderiv j (G i))‖,
      le_max_of_le_left (norm_nonneg _), max_lt ?_ ?_, fun i => le_max_of_le_left ?_,
      fun i j => le_max_of_le_right ?_⟩
    · rw [pi_norm_lt_iff one_pos]; intro i; rw [norm_sub_rev]; exact hy0 i
    · rw [pi_norm_lt_iff one_pos]; intro i; rw [pi_norm_lt_iff one_pos]; exact hd i
    · exact norm_le_pi_norm (fun i => y0 i - x i) i
    · exact (norm_le_pi_norm
        (fun j => (if j = i then 1 else 0) - eval₂ W.subtype x (pderiv j (G i))) j).trans
        (norm_le_pi_norm
        (fun i j => (if j = i then 1 else 0) - eval₂ W.subtype x (pderiv j (G i))) i)
  have key : ∀ n : ℕ, ∃ y : ι → W, ∀ i, ‖(y i : K) - x i‖ ≤ ρ ^ (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨fun i => ⟨y0 i, hy0W i⟩, fun i => by simpa using hρy i⟩
    | succ n ih =>
      obtain ⟨y, hy⟩ := ih
      refine ⟨fun i => y i - eval y (G i), fun i => ?_⟩
      have hr : 0 ≤ ρ ^ (n + 1) := pow_nonneg hρ0 _
      have hT := taylor_bound W.subtype hc' x (fun i => (y i : K)) hx (fun i => hc' (y i)) hr hy
        (G i)
      have he : ((eval y (G i) : W) : K) = eval₂ W.subtype (fun i => (y i : K)) (G i) := by
        have := eval₂_comp_left W.subtype (RingHom.id W) y (G i)
        simpa [Function.comp_def] using this
      have : ((y i - eval y (G i) : W) : K) - x i =
          ∑ j, ((if j = i then 1 else 0) - eval₂ W.subtype x (pderiv j (G i))) * (y j - x j) +
          -(eval₂ W.subtype (fun i => (y i : K)) (G i) - eval₂ W.subtype x (G i) -
            ∑ j, eval₂ W.subtype x (pderiv j (G i)) * (y j - x j)) := by
        simp only [sub_mul, Finset.sum_sub_distrib, hG, ite_mul, one_mul, zero_mul,
          Finset.sum_ite_eq', Finset.mem_univ, if_true]
        push_cast
        rw [he]; ring
      rw [this]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · refine norm_sum_le_of_le _ (pow_nonneg hρ0 _) fun j => ?_
        rw [norm_mul, pow_succ' ρ (n + 1)]
        exact mul_le_mul (hρd i j) (hy j) (norm_nonneg _) hρ0
      · rw [norm_neg, pow_succ ρ (n + 1)]
        refine hT.trans (mul_le_mul_of_nonneg_left ?_ hr)
        rw [pow_succ]
        exact mul_le_of_le_one_left hρ0 (pow_le_one₀ hρ0 hρ1.le)
  have : x i ∈ closure (W : Set K) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hρ1
    obtain ⟨y, hy⟩ := key n
    refine ⟨y i, (y i).2, ?_⟩
    rw [dist_comm, dist_eq_norm]
    refine (hy i).trans_lt (lt_of_le_of_lt ?_ hn)
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg hρ0 _) hρ1.le
  rwa [hW.closure_eq] at this

end

theorem subset_of_unramified (K : Type) [NormedField K] [IsUltrametricDist K] (W : Subring K)
    (hW : IsClosed (W : Set K)) (hc : ∀ w ∈ W, ‖w‖ ≤ 1)
    (hres : ∀ x : K, ‖x‖ ≤ 1 → ∃ w ∈ W, ‖x - w‖ < 1) (s : Set K) (hs : s.Finite)
    (hs1 : ∀ x ∈ s, ‖x‖ ≤ 1)
    (h : ∀ (k : Type) [Field k] (φ : Subring.closure ((W : Set K) ∪ s) →+* DualNumber k),
      (∀ a : Subring.closure ((W : Set K) ∪ s), ‖(a : K)‖ = 1 → (φ a).fst ≠ 0) →
      (∀ a : Subring.closure ((W : Set K) ∪ s), (a : K) ∈ W → (φ a).snd = 0) →
      ∀ a : Subring.closure ((W : Set K) ∪ s), (a : K) ∈ s → (φ a).snd = 0) :
    s ⊆ (W : Set K) := by
  classical
  haveI : Fintype s := hs.fintype
  let A := Subring.closure ((W : Set K) ∪ s)
  let O := (NormedField.valuation (K := K)).valuationSubring
  have hO : ∀ z : K, z ∈ O ↔ ‖z‖ ≤ 1 := by
    intro z
    simp only [O, Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
    exact Iff.rfl
  have hm : ∀ z : O, IsLocalRing.residue O z = 0 ↔ ‖(z : K)‖ < 1 := by
    intro z
    rw [IsLocalRing.residue_eq_zero_iff, Valuation.mem_maximalIdeal_iff]
    exact Iff.rfl
  have hAO : A ≤ O.toSubring := by
    refine Subring.closure_le.2 ?_
    rintro z (hz | hz)
    · exact (hO z).2 (hc z hz)
    · exact (hO z).2 (hs1 z hz)
  have hWA : W ≤ A := fun z hz => Subring.subset_closure (Or.inl hz)
  let x : s → A := fun i => ⟨i, Subring.subset_closure (Or.inr i.2)⟩
  let ev : MvPolynomial s W →+* A := eval₂Hom (Subring.inclusion hWA) x
  have hevK : ∀ F, ((ev F : A) : K) = eval₂ W.subtype (fun i : s => (i : K)) F := by
    intro F
    have := eval₂_comp_left A.subtype (Subring.inclusion hWA) x F
    exact this
  have hev : Function.Surjective ev := by
    rintro ⟨a, ha⟩
    have : a ∈ (A.subtype.comp ev).range := by
      refine (Subring.closure_le (t := (A.subtype.comp ev).range)).2 ?_ ha
      rintro z (hz | hz)
      · exact ⟨C ⟨z, hz⟩, by simp [ev]⟩
      · exact ⟨X ⟨z, hz⟩, by simp [ev, x]⟩
    obtain ⟨F, hF⟩ := this
    exact ⟨F, Subtype.ext hF⟩
  let inc : A →+* O := Subring.inclusion hAO
  let red : A →+* IsLocalRing.ResidueField O := (IsLocalRing.residue O).comp inc
  have hred0 : ∀ a : A, red a = 0 ↔ ‖(a : K)‖ < 1 := fun a => hm (inc a)
  have hred : ∀ c, ∃ w : W, red (ev (C w)) = c := by
    intro c
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective c
    obtain ⟨w, hw, hzw⟩ := hres z ((hO _).1 z.2)
    refine ⟨⟨w, hw⟩, ?_⟩
    symm
    rw [← sub_eq_zero]
    have : IsLocalRing.residue O (z - inc (ev (C ⟨w, hw⟩))) = 0 := by
      rw [hm]
      have : ((inc (ev (C ⟨w, hw⟩)) : O) : K) = w := by
        change ((ev (C ⟨w, hw⟩) : A) : K) = w
        rw [hevK]; simp
      push_cast
      rwa [this]
    rwa [map_sub] at this
  have hG := exists_relation_gradient ev hev red hred (fun φ h1 h2 i => by
    refine h _ φ (fun a ha => ?_) (fun a ha => ?_) _ ?_
    · rw [h1, Ne, hred0, ha]; exact lt_irrefl _
    · have : a = ev (C ⟨a, ha⟩) := Subtype.ext (by rw [hevK]; simp)
      rw [this]; exact h2 _
    · rw [hevK]; simp)
  choose G hG0 hG1 using hG
  intro z hz
  refine mem_of_gradient W hW hc (fun i : s => (i : K)) (fun i => hs1 i i.2)
    (fun i => hres i (hs1 i i.2)) G (fun i => ?_) (fun i j => ?_) ⟨z, hz⟩
  · rw [← hevK, hG0]; rfl
  · have : red ((if j = i then 1 else 0) - ev (pderiv j (G i))) = 0 := by
      rw [map_sub, hG1]; split_ifs <;> simp
    rw [hred0] at this
    rw [← hevK]
    convert this using 2
    split_ifs <;> simp

end UnramifiedHensel
end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModel
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum Polynomial
open scoped BigOperators

noncomputable section

namespace GlobalTheory.UnitModel

section Dual

variable {k : Type} [Field k]

def fstP (f : (DualNumber k)[X]) : k[X] := f.map (TrivSqZeroExt.fstHom k k k).toRingHom

def sndP (f : (DualNumber k)[X]) : k[X] := ∑ i ∈ f.support, monomial i (f.coeff i).snd

@[simp] theorem coeff_fstP (f : (DualNumber k)[X]) (i : ℕ) : (fstP f).coeff i = (f.coeff i).fst := by
  simp [fstP]

@[simp] theorem coeff_sndP (f : (DualNumber k)[X]) (i : ℕ) : (sndP f).coeff i = (f.coeff i).snd := by
  rw [sndP, finsetSum_coeff, Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [coeff_monomial, hj]
  · intro hi
    simp [notMem_support_iff.1 hi]

theorem sndP_add (f g : (DualNumber k)[X]) : sndP (f + g) = sndP f + sndP g := by ext; simp
theorem sndP_sub (f g : (DualNumber k)[X]) : sndP (f - g) = sndP f - sndP g := by ext; simp
theorem sndP_mul (f g : (DualNumber k)[X]) : sndP (f * g) = fstP f * sndP g + sndP f * fstP g := by
  ext i
  simp only [coeff_mul, coeff_add, coeff_sndP, coeff_fstP, TrivSqZeroExt.snd_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => DualNumber.snd_mul _ _
theorem sndP_C (a : DualNumber k) : sndP (C a) = C a.snd := by
  ext i
  simp only [coeff_sndP, coeff_C]
  split_ifs <;> simp
theorem sndP_X : sndP (X : (DualNumber k)[X]) = 0 := by
  ext i
  simp only [coeff_sndP, coeff_X]
  split_ifs <;> simp
theorem sndP_derivative (f : (DualNumber k)[X]) : sndP (derivative f) = derivative (sndP f) := by
  ext i
  simp [coeff_derivative]
theorem sndP_two : sndP (2 : (DualNumber k)[X]) = 0 := by
  rw [show (2 : (DualNumber k)[X]) = C 1 + C 1 by simp; norm_num, sndP_add, sndP_C]; simp
theorem fstP_add (f g : (DualNumber k)[X]) : fstP (f + g) = fstP f + fstP g := Polynomial.map_add _
theorem fstP_sub (f g : (DualNumber k)[X]) : fstP (f - g) = fstP f - fstP g := Polynomial.map_sub _
theorem fstP_mul (f g : (DualNumber k)[X]) : fstP (f * g) = fstP f * fstP g := Polynomial.map_mul _
theorem fstP_pow (f : (DualNumber k)[X]) (n : ℕ) : fstP (f ^ n) = fstP f ^ n := Polynomial.map_pow _ _
theorem fstP_C (a : DualNumber k) : fstP (C a) = C a.fst := Polynomial.map_C _
theorem fstP_X : fstP (X : (DualNumber k)[X]) = X := Polynomial.map_X _
theorem fstP_two : fstP (2 : (DualNumber k)[X]) = 2 := Polynomial.map_ofNat _ _
theorem fstP_derivative (f : (DualNumber k)[X]) : fstP (derivative f) = derivative (fstP f) :=
  (derivative_map _ _).symm
theorem sndP_pow (f : (DualNumber k)[X]) (n : ℕ) :
    sndP (f ^ (n + 1)) = (n + 1 : ℕ) * fstP f ^ n * sndP f := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, sndP_mul, ih, fstP_pow]; push_cast; ring

theorem snd_eval (f : (DualNumber k)[X]) (c : DualNumber k) :
    (f.eval c).fst = (fstP f).eval c.fst ∧
    (f.eval c).snd = (sndP f).eval c.fst + (derivative (fstP f)).eval c.fst * c.snd := by
  induction f using Polynomial.induction_on with
  | C a => simp [fstP_C, sndP_C]
  | add p q hp hq => simp [fstP_add, sndP_add, hp.1, hp.2, hq.1, hq.2]; ring
  | monomial n a h =>
    rw [pow_succ, ← mul_assoc]
    generalize C a * X ^ n = g at h
    simp [fstP_mul, sndP_mul, fstP_X, sndP_X, h.1, h.2]; ring

theorem degree_sndP_lt {f : (DualNumber k)[X]} (hf : f.Monic) : (sndP f).degree < (f.natDegree : WithBot ℕ) := by
  rw [degree_lt_iff_coeff_zero]
  intro i hi
  rw [coeff_sndP]
  rcases hi.eq_or_lt with e | e
  · rw [← e, hf.coeff_natDegree]; simp
  · rw [coeff_eq_zero_of_natDegree_lt e]; simp

theorem rigid_dual (m : ℕ) (A B a : DualNumber k) (n h : (DualNumber k)[X]) (h2 : (2 : k) ≠ 0) (h3 : (3 : k) ≠ 0)
    (ha : a.snd = 0) (ha0 : a.fst ≠ 0) (hsq : a ^ 2 = -(2 * (m : DualNumber k) + 1))
    (hΔ : -16 * (4 * A ^ 3 + 27 * B ^ 2) = 1) (hn : n.Monic) (hh : h.Monic) (dn : n.natDegree = 2 * m + 1)
    (dh : h.natDegree = m) (hc : IsCoprime (fstP n) (fstP h))
    (e : (X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) ^ 2 =
      n ^ 3 + C (a ^ 4 * A) * n * h ^ 4 + C (a ^ 6 * B) * h ^ 6) :
    A.snd = 0 ∧ B.snd = 0 ∧ sndP n = 0 ∧ sndP h = 0 := by
  have e1 := congrArg fstP e
  have e2 := congrArg sndP e
  simp only [fstP_add, fstP_sub, fstP_mul, fstP_pow, fstP_C, fstP_X, fstP_two, fstP_derivative,
    TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow] at e1
  have p2 := fun f : (DualNumber k)[X] => sndP_pow f 1
  have p3 := fun f : (DualNumber k)[X] => sndP_pow f 2
  have p4 := fun f : (DualNumber k)[X] => sndP_pow f 3
  have p6 := fun f : (DualNumber k)[X] => sndP_pow f 5
  have s4 : (a ^ 4 * A).snd = a.fst ^ 4 * A.snd := by simp [TrivSqZeroExt.snd_pow, ha]
  have s6 : (a ^ 6 * B).snd = a.fst ^ 6 * B.snd := by simp [TrivSqZeroExt.snd_pow, ha]
  simp only [Nat.reduceAdd] at p2 p3 p4 p6
  simp only [p2, p3, p4, p6, sndP_add, sndP_sub, sndP_mul, sndP_C, sndP_X, sndP_two, sndP_derivative, s4, s6,
    fstP_add, fstP_sub, fstP_mul, fstP_pow, fstP_C, fstP_X, fstP_two, fstP_derivative,
    TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_pow] at e2
  have f1 := congrArg (TrivSqZeroExt.fstHom k k k) hΔ
  have f2 := congrArg (TrivSqZeroExt.fstHom k k k) hsq
  simp only [map_mul, map_add (f := _), map_pow, map_neg, map_ofNat, map_one, map_natCast, TrivSqZeroExt.fstHom_apply] at f1 f2
  have f3 : -16 * (12 * A.fst ^ 2 * A.snd + 54 * B.fst * B.snd) = 0 := by
    have t : ∀ j : ℕ, ((j : DualNumber k)).snd = 0 ∧ ((j : DualNumber k)).fst = j := fun j => by simp
    have g := congrArg TrivSqZeroExt.snd hΔ
    have t4 := t 4
    have t16 := t 16
    have t27 := t 27
    simp only [Nat.cast_ofNat] at t4 t16 t27
    rw [show A ^ 3 = A * A * A by ring, sq] at g
    simp only [DualNumber.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_neg, TrivSqZeroExt.fst_neg,
      TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_one, t4, t16, t27] at g
    linear_combination g
  have h16 : (-16 : k) ≠ 0 := by
    rw [show (-16 : k) = -(2 ^ 4) by norm_num]
    exact neg_ne_zero.2 (pow_ne_zero _ h2)
  refine GlobalTheory.TangentRigid.first_order_rigid k m A.fst B.fst a.fst A.snd B.snd (fstP n) (fstP h) (sndP n) (sndP h) h2 h3 ha0 f2
    (fun h0 => by rw [h0] at f1; simp at f1) ((mul_eq_zero.1 f3).resolve_left h16) (hn.map _) (hh.map _)
    ((hn.natDegree_map _).trans dn) ((hh.natDegree_map _).trans dh) (dn ▸ degree_sndP_lt hn)
    (dh ▸ degree_sndP_lt hh) hc e1 ?_
  push_cast at e2
  linear_combination e2

end Dual

section Rigid

variable {K : Type} [NormedField K] [IsUltrametricDist K]

theorem norm_le_one_of_mem_closure {t : Set K} (ht : ∀ x ∈ t, ‖x‖ ≤ 1) {x : K} (hx : x ∈ Subring.closure t) :
    ‖x‖ ≤ 1 := by
  induction hx using Subring.closure_induction with
  | mem x hx => exact ht x hx
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  | neg x _ hx => simpa using hx
  | mul x y _ _ hx hy => rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

theorem norm_multiset_prod_eq_one {s : Multiset K} (h : ∀ x ∈ s, ‖x‖ = 1) : ‖s.prod‖ = 1 := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, norm_mul, h a (by simp), ih fun x hx => h x (by simp [hx]), one_mul]

theorem units_at_root {A B A' B' : K} {n h : K[X]} (h2 : ‖(2 : K)‖ = 1) (hh : h.Monic) (hs : h.Splits)
    (hc : IsCoprime n h)
    (e : (X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) ^ 2 =
      n ^ 3 + C A' * n * h ^ 4 + C B' * h ^ 6)
    (hF : ∀ x, h.IsRoot x → ‖x ^ 3 + A * x + B‖ = 1)
    (hd : ∀ x y, h.IsRoot x → h.IsRoot y → x ≠ y → ‖x - y‖ = 1) {r : K} (hr : h.IsRoot r) :
    ‖n.eval r‖ = 1 ∧ ‖(derivative h).eval r‖ = 1 := by
  have h0 : h.eval r = 0 := hr
  have n0 : n.eval r ≠ 0 := fun hn => by
    obtain ⟨u, v, huv⟩ := hc
    have := congrArg (eval r) huv
    simp [hn, h0] at this
  have e1 := congrArg (eval r) e
  simp only [eval_add, eval_mul, eval_pow, eval_sub, eval_X, eval_C, h0, eval_ofNat] at e1
  have e2 : n.eval r = 2 ^ 2 * (r ^ 3 + A * r + B) * (derivative h).eval r ^ 2 :=
    mul_left_cancel₀ (pow_ne_zero 2 n0) (by linear_combination -e1)
  have d0 : (derivative h).eval r ≠ 0 := fun hn => n0 (by rw [e2, hn]; ring)
  have hm : r ∈ h.roots := (mem_roots hh.ne_zero).2 hr
  have e3 : (derivative h).eval r = ((h.roots.erase r).map fun a => r - a).prod := by
    conv_lhs => rw [hs.eq_prod_roots_of_monic hh]
    exact eval_multiset_prod_X_sub_C_derivative hm
  have d1 : ‖(derivative h).eval r‖ = 1 := by
    rw [e3] at d0 ⊢
    refine norm_multiset_prod_eq_one fun x hx => ?_
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hx
    refine hd r y hr ((mem_roots hh.ne_zero).1 (Multiset.mem_of_mem_erase hy)) fun hry => d0 ?_
    exact Multiset.prod_eq_zero (by subst hry; rwa [sub_self] at hx)
  exact ⟨by rw [e2, norm_mul, norm_mul, norm_pow, norm_pow, h2, d1, hF r hr]; simp, d1⟩

theorem rigid (W : Subring K) (hW : IsClosed (W : Set K)) (hW1 : ∀ w ∈ W, ‖w‖ ≤ 1)
    (hW2 : ∀ x : K, ‖x‖ ≤ 1 → ∃ w ∈ W, ‖x - w‖ < 1) {A B a : K} {m : ℕ} {n h : K[X]}
    (h2 : ‖(2 : K)‖ = 1) (h3 : ‖(3 : K)‖ = 1) (hA : ‖A‖ ≤ 1) (hB : ‖B‖ ≤ 1) (ha : ‖a‖ = 1)
    (hsq : a ^ 2 = -(2 * (m : K) + 1)) (hΔ : -16 * (4 * A ^ 3 + 27 * B ^ 2) = 1) (hn : n.Monic) (hh : h.Monic)
    (dn : n.natDegree = 2 * m + 1) (dh : h.natDegree = m) (hs : h.Splits) (hc : IsCoprime n h)
    (e : (X ^ 3 + C A * X + C B) * (derivative n * h - 2 * n * derivative h) ^ 2 =
      n ^ 3 + C (a ^ 4 * A) * n * h ^ 4 + C (a ^ 6 * B) * h ^ 6)
    (hI : ∀ x, h.IsRoot x → ‖x‖ ≤ 1) (hF : ∀ x, h.IsRoot x → ‖x ^ 3 + A * x + B‖ = 1)
    (hd : ∀ x y, h.IsRoot x → h.IsRoot y → x ≠ y → ‖x - y‖ = 1) : A ∈ W ∧ B ∈ W := by
  have hprod := hs.eq_prod_roots_of_monic hh
  have lift_h : ∀ S : Subring K, (∀ x, h.IsRoot x → x ∈ S) →
      ∃ T : Multiset S, (T.map fun r => X - C r).prod.map S.subtype = h := fun S hS => by
    obtain ⟨T, hT⟩ : ∃ T : Multiset S, T.map S.subtype = h.roots :=
      ⟨h.roots.attach.map fun r => ⟨r.1, hS _ ((mem_roots hh.ne_zero).1 r.2)⟩, by simp⟩
    refine ⟨T, ?_⟩
    rw [hprod, ← hT, Polynomial.map_multiset_prod]
    simp
  have hhI : ∀ i, ‖h.coeff i‖ ≤ 1 := fun i => by
    obtain ⟨T, hT⟩ := lift_h (Subring.closure {x | ‖x‖ ≤ 1}) fun x hx => Subring.subset_closure (hI x hx)
    rw [← hT, coeff_map]
    exact norm_le_one_of_mem_closure (fun _ h => h) (Subtype.prop _)
  have hnI := GlobalTheory.isogeny_numerator_coeff_norm_le_one K A B _ _ n h hA hB (by simpa [ha] using hA) (by simpa [ha] using hB) hhI e
  set s : Set K := {A, B, a} ∪ {x | h.IsRoot x} ∪ Set.range n.coeff with hs_def
  have hfin : s.Finite := by
    refine ((Set.toFinite _).union ?_).union ?_
    · exact (h.roots.toFinset.finite_toSet).subset fun x hx => by simpa [hh.ne_zero] using hx
    · refine ((n.coeffs.finite_toSet).insert 0).subset ?_
      rintro _ ⟨i, rfl⟩
      by_cases hi : n.coeff i = 0
      · exact Or.inl hi
      · exact Or.inr (coeff_mem_coeffs hi)
  have key := GlobalTheory.UnramifiedHensel.subset_of_unramified K W hW hW1 hW2 s hfin ?_ ?_
  · exact ⟨key (by simp [s]), key (by simp [s])⟩
  · rintro x (((rfl | rfl | rfl) | hx) | ⟨i, rfl⟩)
    exacts [hA, hB, ha.le, hI x hx, hnI i]
  have hS : ∀ x ∈ s, x ∈ Subring.closure ((W : Set K) ∪ s) := fun x hx => Subring.subset_closure (Or.inr hx)
  generalize Subring.closure ((W : Set K) ∪ s) = S at hS ⊢
  intro k _ φ hu _
  let A₀ : S := ⟨A, hS _ (by simp [s])⟩
  let B₀ : S := ⟨B, hS _ (by simp [s])⟩
  let a₀ : S := ⟨a, hS _ (by simp [s])⟩
  obtain ⟨T, hT⟩ := lift_h S fun x hx => hS _ (Or.inl (Or.inr hx))
  obtain ⟨n₀, hn₀, dn₀, mn₀⟩ := lifts_and_natDegree_eq_and_monic (f := S.subtype) (p := n)
    ((lifts_iff_coeff_lifts _).2 fun i => ⟨⟨_, hS _ (Or.inr ⟨i, rfl⟩)⟩, rfl⟩) hn
  set h₀ := (T.map fun r => X - C r).prod with h₀_def
  have mh₀ : h₀.Monic := monic_multiset_prod_of_monic _ _ fun r _ => monic_X_sub_C r
  have dh₀ : h₀.natDegree = m := by rw [← dh, ← hT, mh₀.natDegree_map]
  have e₀ : (X ^ 3 + C A₀ * X + C B₀) * (derivative n₀ * h₀ - 2 * n₀ * derivative h₀) ^ 2 =
      n₀ ^ 3 + C (a₀ ^ 4 * A₀) * n₀ * h₀ ^ 4 + C (a₀ ^ 6 * B₀) * h₀ ^ 6 := by
    apply map_injective S.subtype Subtype.val_injective
    simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_C, map_X,
      Polynomial.map_ofNat, ← derivative_map, hT, hn₀]
    exact e
  have hev : ∀ (f : S[X]) (r : S), (fstP (f.map φ)).eval (φ r).fst = (φ (f.eval r)).fst := fun f r => by
    rw [← (snd_eval _ _).1, eval_map, eval₂_at_apply]
  have hev' : ∀ (f : S[X]) (r : S), ((f.eval r : S) : K) = (f.map S.subtype).eval (r : K) := fun f r => by
    rw [eval_map]; exact (eval₂_at_apply S.subtype r).symm
  have k2 : (2 : k) ≠ 0 := by have := hu 2 h2; rwa [map_ofNat] at this
  have k3 : (3 : k) ≠ 0 := by have := hu 3 h3; rwa [map_ofNat] at this
  have hsq₀ : φ a₀ ^ 2 = -(2 * (m : DualNumber k) + 1) := by
    have : a₀ ^ 2 = -(2 * (m : S) + 1) := S.subtype_injective (by
      simp only [map_pow, map_neg, map_add (f := _), map_mul, map_ofNat, map_one, map_natCast]; exact hsq)
    simpa [map_ofNat] using congrArg φ this
  have ha₀ : (φ a₀).snd = 0 := by
    have g := congrArg TrivSqZeroExt.snd hsq₀
    rw [show -(2 * (m : DualNumber k) + 1) = -((2 * m + 1 : ℕ) : DualNumber k) by push_cast; ring, sq,
      DualNumber.snd_mul, TrivSqZeroExt.snd_neg, TrivSqZeroExt.snd_natCast, neg_zero] at g
    exact (mul_eq_zero.1 (show (2 * (φ a₀).fst) * (φ a₀).snd = 0 by linear_combination g)).resolve_left
      (mul_ne_zero k2 (hu a₀ ha))
  have hroot : ∀ r ∈ T, h.IsRoot (r : K) := fun r hr => by
    rw [IsRoot, ← hT, ← hev', h₀_def, eval_multiset_prod, Multiset.prod_eq_zero]
    · rfl
    · simp only [Multiset.map_map, Multiset.mem_map]
      exact ⟨r, hr, by simp⟩
  have hco : IsCoprime (fstP (n₀.map φ)) (fstP (h₀.map φ)) := by
    have : ∀ T' : Multiset S, (∀ r ∈ T', h.IsRoot (r : K)) →
        IsCoprime (fstP (n₀.map φ)) (fstP ((T'.map fun r => X - C r).prod.map φ)) := fun T' hT' => by
      induction T' using Multiset.induction_on with
      | empty => simpa [fstP] using isCoprime_one_right
      | cons r T' ih =>
        rw [Multiset.map_cons, Multiset.prod_cons, Polynomial.map_mul, fstP_mul]
        refine IsCoprime.mul_right ?_ (ih fun x hx => hT' x (by simp [hx]))
        rw [Polynomial.map_sub, map_X, map_C, fstP_sub, fstP_X, fstP_C, isCoprime_comm,
          (irreducible_X_sub_C _).coprime_iff_not_dvd, dvd_iff_isRoot, IsRoot, hev]
        refine hu _ ?_
        rw [hev', hn₀]
        exact (units_at_root h2 hh hs hc e hF hd (hT' r (by simp))).1
    exact this T hroot
  obtain ⟨r1, r2, r3, r4⟩ := rigid_dual m (φ A₀) (φ B₀) (φ a₀) (n₀.map φ) (h₀.map φ) k2 k3 ha₀ (hu a₀ ha) hsq₀
    (by
      have : -16 * (4 * A₀ ^ 3 + 27 * B₀ ^ 2) = 1 := S.subtype_injective (by
      simp only [map_pow, map_neg, map_add (f := _), map_mul, map_ofNat, map_one, map_natCast]; exact hΔ)
      simpa [map_ofNat] using congrArg φ this)
    (mn₀.map _) (mh₀.map _) (by rw [mn₀.natDegree_map, dn₀, dn]) (by rw [mh₀.natDegree_map, dh₀]) hco
    (by simpa only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_C, map_X,
      Polynomial.map_ofNat, ← derivative_map, map_mul, map_pow] using congrArg (Polynomial.map φ) e₀)
  rintro x (((hx | hx | hx) | hx) | ⟨i, hx⟩)
  · rwa [show x = A₀ from Subtype.ext hx]
  · rwa [show x = B₀ from Subtype.ext hx]
  · rwa [show x = a₀ from Subtype.ext hx]
  · have z : h₀.eval x = 0 := Subtype.ext (by rw [hev', hT]; exact hx)
    have g := (snd_eval (h₀.map φ) (φ x)).2
    rw [eval_map, eval₂_at_apply, z, r4, ← fstP_derivative, derivative_map, hev] at g
    have u : (φ ((derivative h₀).eval x)).fst ≠ 0 := hu _ (by
      rw [hev', ← derivative_map, hT]
      exact (units_at_root h2 hh hs hc e hF hd hx).2)
    simpa [u] using g
  · have : x = n₀.coeff i := Subtype.ext (by rw [← hx, ← hn₀, coeff_map]; rfl)
    have g := coeff_sndP (n₀.map φ) i
    rw [r3, coeff_map] at g
    rw [this, ← g, coeff_zero]

end Rigid

section Padic

variable {p : ℕ} [Fact p.Prime]

theorem norm_natCast_eq_one {N : ℕ} (h : ¬ p ∣ N) : ‖(N : ℂ_[p])‖ = 1 := by
  have h1 := PadicComplex.norm_extends' p (N : ℚ_[p])
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p])]
  exact h1.trans <| Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 h)

theorem norm_le_one_of_isIntegral {K : Type} [NormedField K] [IsUltrametricDist K] {x : K} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have := (Valuation.integer.integers (NormedField.valuation (K := K))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at this
  exact_mod_cast this

theorem norm_map_le_one {F K : Type} [CommRing F] [NormedField K] [IsUltrametricDist K] (f : F →+* K) {x : F}
    (hx : IsIntegral ℤ x) : ‖f x‖ ≤ 1 :=
  norm_le_one_of_isIntegral (hx.map f.toIntAlgHom)

theorem norm_le_one_of_mem_Wp {w : ℂ_[p]} (hw : w ∈ GL3Theta.Wp p) : ‖w‖ ≤ 1 := by
  refine closure_minimal (t := {x : ℂ_[p] | ‖x‖ ≤ 1}) (fun x hx => norm_le_one_of_mem_closure ?_ hx)
    (isClosed_le continuous_norm continuous_const) hw
  rintro ζ ⟨n, hn, -, hζ⟩
  have := congrArg norm hζ
  rw [norm_pow, norm_one] at this
  exact ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 this).le

theorem exists_integral_model (lam : Qbar →+* ℂ_[p]) (A B : Qbar) (hΔ : -16 * (4 * A ^ 3 + 27 * B ^ 2) = 1)
    (hj : IsIntegral ℤ ((-48 * (A : ℂ)) ^ 3)) :
    ∃ (C : WeierstrassCurve.VariableChange ℂ_[p]) (E : WeierstrassCurve ℂ_[p]),
      C • (⟨0, 0, 0, lam A, lam B⟩ : WeierstrassCurve ℂ_[p]) = E ∧ ‖E.a₁‖ ≤ 1 ∧ ‖E.a₂‖ ≤ 1 ∧ ‖E.a₃‖ ≤ 1 ∧
      ‖E.a₄‖ ≤ 1 ∧ ‖E.a₆‖ ≤ 1 ∧ E.Δ = 1 := by
  obtain ⟨E, i1, i2, i3, i4, i6, hE, hc⟩ := CMCurves.exists_integral_curve hj
  have mem : ∀ {x : ℂ}, IsIntegral ℤ x → x ∈ Qbar := fun hx =>
    mem_algebraicClosure_iff.mpr (hx.tower_top (A := ℚ)).isAlgebraic
  have nrm : ∀ {x : ℂ} (hx : IsIntegral ℤ x), ‖lam ⟨x, mem hx⟩‖ ≤ 1 := fun {x} hx =>
    norm_map_le_one lam
      ((isIntegral_algHom_iff (Qbar.val.toRingHom.toIntAlgHom) Subtype.val_injective).mp hx)
  let E₀ : WeierstrassCurve Qbar := ⟨⟨_, mem i1⟩, ⟨_, mem i2⟩, ⟨_, mem i3⟩, ⟨_, mem i4⟩, ⟨_, mem i6⟩⟩
  have hE₀ : E₀.map Qbar.val.toRingHom = E := rfl
  have d₀ : E₀.Δ = 1 := Qbar.val.toRingHom.injective (by rw [← WeierstrassCurve.map_Δ, hE₀, hE, map_one])
  have c₀ : E₀.c₄ ^ 3 = (-48 * A) ^ 3 := Qbar.val.toRingHom.injective (by
    rw [map_pow, ← WeierstrassCurve.map_c₄, hE₀, hc, map_pow, map_mul, map_neg, map_ofNat]; rfl)
  set V : WeierstrassCurve ℂ_[p] := ⟨0, 0, 0, lam A, lam B⟩ with hV
  have d₁ : (E₀.map lam).Δ = 1 := by rw [WeierstrassCurve.map_Δ, d₀, map_one]
  have d₂ : V.Δ = 1 := by
    have := congrArg lam hΔ
    simp only [map_mul, map_add (f := _), map_pow, map_neg, map_ofNat, map_one] at this
    simp only [hV, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    linear_combination this
  have : (E₀.map lam).IsElliptic := ⟨d₁ ▸ isUnit_one⟩
  have : V.IsElliptic := ⟨d₂ ▸ isUnit_one⟩
  obtain ⟨C, hC⟩ := WeierstrassCurve.exists_variableChange_of_j_eq V (E₀.map lam) (by
    rw [WeierstrassCurve.j, WeierstrassCurve.j, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val,
      WeierstrassCurve.coe_Δ', WeierstrassCurve.coe_Δ', d₁, d₂, WeierstrassCurve.map_c₄, ← map_pow, c₀]
    simp only [hV, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, map_pow, map_mul, map_neg, map_ofNat]
    ring)
  exact ⟨C, _, hC, nrm i1, nrm i2, nrm i3, nrm i4, nrm i6, d₁⟩

theorem invariants_mem (hp : 5 ≤ p) (lam : Qbar →+* ℂ_[p]) (L : PeriodPair) (A B α : Qbar) (m : ℕ)
    (eA : (A : ℂ) = -L.g₂ / 4) (eB : (B : ℂ) = -L.g₃ / 4) (hΔ : -16 * (4 * A ^ 3 + 27 * B ^ 2) = 1)
    (hA : ‖lam A‖ ≤ 1) (hB : ‖lam B‖ ≤ 1) (hm : ¬ p ∣ 2 * m + 1) (hα : α ^ 2 = -(2 * (m : Qbar) + 1))
    (hL : ∀ l ∈ L.lattice, (α : ℂ) * l ∈ L.lattice)
    (ht : ∀ t ∉ L.lattice, ((2 * m + 1 : ℕ) : ℂ) * t ∈ L.lattice →
      L.weierstrassP t ∈ Qbar ∧ L.derivWeierstrassP t ∈ Qbar) :
    lam A ∈ GL3Theta.Wp p ∧ lam B ∈ GL3Theta.Wp p := by
  let i : Qbar →+* ℂ := Qbar.val.toRingHom
  have hi : ∀ x : Qbar, i x = x := fun _ => rfl
  have hα' : (α : ℂ) ^ 2 = -(2 * (m : ℂ) + 1) := by
    have := congrArg i hα
    simp only [map_pow, map_neg, map_add (f := _), map_mul, map_ofNat, map_one, map_natCast] at this
    exact this
  have tor : ∀ t, (α : ℂ) * t ∈ L.lattice → ((2 * m + 1 : ℕ) : ℂ) * t ∈ L.lattice := fun t h => by
    have := L.lattice.neg_mem (hL _ h)
    rwa [show -((α : ℂ) * (α * t)) = ((2 * m + 1 : ℕ) : ℂ) * t by push_cast; linear_combination (-t) * hα'] at this
  have g2m : L.g₂ ∈ Qbar := by
    rw [show L.g₂ = -4 * (A : ℂ) by rw [eA]; ring]
    exact mul_mem (neg_mem (ofNat_mem _ 4)) A.2
  have g3m : L.g₃ ∈ Qbar := by
    rw [show L.g₃ = -4 * (B : ℂ) by rw [eB]; ring]
    exact mul_mem (neg_mem (ofNat_mem _ 4)) B.2
  obtain ⟨n, h, hn, hh, dn, dh, hc, hk, hr, e⟩ := GlobalTheory.exists_mul_sqrt_neg_odd_polynomial_identity L α m Qbar.toSubfield hα' hL
    (GlobalTheory.relIndex_map_mulLeft_lattice_of_sq_eq_neg L α (2 * m + 1) (by omega) (by push_cast; exact hα') hL) g2m g3m α.2
    fun t h1 h2 => (ht t h1 (tor t h2)).1
  obtain ⟨n₀, hn₀, dn₀, mn₀⟩ := lifts_and_natDegree_eq_and_monic (f := i) (p := n)
    ((lifts_iff_coeff_lifts _).2 fun j => ⟨⟨_, hk j⟩, rfl⟩) hn
  obtain ⟨T, hT⟩ : ∃ T : Multiset Qbar, T.map i = h.roots :=
    ⟨h.roots.attach.map fun r => ⟨r.1, by
      obtain ⟨t, h1, h2, h3⟩ := hr _ ((mem_roots hh.ne_zero).1 r.2)
      exact h3 ▸ (ht t h1 (tor t h2)).1⟩, by simp [hi]⟩
  set h₀ := (T.map fun r => X - C r).prod with h₀_def
  have hh₀ : h₀.map i = h := by
    rw [(IsAlgClosed.splits h).eq_prod_roots_of_monic hh, ← hT, Polynomial.map_multiset_prod]
    simp
  have mh₀ : h₀.Monic := monic_multiset_prod_of_monic _ _ fun r _ => monic_X_sub_C r
  have e₀ : (X ^ 3 + C A * X + C B) * (derivative n₀ * h₀ - 2 * n₀ * derivative h₀) ^ 2 =
      n₀ ^ 3 + C (α ^ 4 * A) * n₀ * h₀ ^ 4 + C (α ^ 6 * B) * h₀ ^ 6 := by
    apply map_injective i i.injective
    simp only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_C, map_X,
      Polynomial.map_ofNat, ← derivative_map, hh₀, hn₀, map_mul, map_pow, hi, eA, eB]
    simpa only [map_mul, map_pow] using e
  have pts : ∀ x, (h₀.map lam).IsRoot x → ∃ (y : ℂ_[p])
      (hxy : (⟨0, 0, 0, lam A, lam B⟩ : WeierstrassCurve ℂ_[p]).toAffine.Nonsingular x y),
      (2 * m + 1) • (WeierstrassCurve.Affine.Point.some x y hxy) = 0 := fun x hx => by
    rw [IsRoot, h₀_def, Polynomial.map_multiset_prod, eval_multiset_prod, Multiset.prod_eq_zero_iff] at hx
    simp only [Multiset.map_map, Multiset.mem_map, Function.comp_apply, Polynomial.map_sub, map_X, map_C,
      eval_sub, eval_X, eval_C, sub_eq_zero] at hx
    obtain ⟨r, hrT, rfl⟩ := hx
    obtain ⟨t, h1, h2, h3⟩ := hr (i r) ((mem_roots hh.ne_zero).1 (hT ▸ Multiset.mem_map_of_mem i hrT))
    let y : Qbar := ⟨L.derivWeierstrassP t / 2, div_mem (ht t h1 (tor t h2)).2 (ofNat_mem _ 2)⟩
    have z : (2 * m + 1) • latticePoint L t = 0 := by
      rw [← latticePointHom_apply, ← map_nsmul, latticePointHom_apply, nsmul_eq_mul]
      exact latticePoint_of_mem L (tor t h2)
    rw [latticePoint_of_notMem L h1] at z
    have key : ∀ (V : WeierstrassCurve ℂ) (a b : ℂ) (hab : V.toAffine.Nonsingular a b), V = ⟨0, 0, 0, i A, i B⟩ →
        a = i r → b = i y → (2 * m + 1) • (WeierstrassCurve.Affine.Point.some a b hab) = 0 →
        ∃ h' : (⟨0, 0, 0, lam A, lam B⟩ : WeierstrassCurve ℂ_[p]).toAffine.Nonsingular (lam r) (lam y),
          (2 * m + 1) • (WeierstrassCurve.Affine.Point.some _ _ h') = 0 := by
      rintro _ _ _ hab rfl rfl rfl z
      exact GlobalTheory.torsion_point_transport_embedding Qbar ℂ ℂ_[p] i lam A B r y _ hab z
    exact ⟨lam y, key _ _ _ _ (by rw [latticeCurve, hi, hi, eA, eB]) h3 rfl z⟩
  have n2 : ‖(2 : ℂ_[p])‖ = 1 := norm_natCast_eq_one (N := 2) fun h => by have := Nat.le_of_dvd two_pos h; omega
  have n3 : ‖(3 : ℂ_[p])‖ = 1 := norm_natCast_eq_one (N := 3) fun h => by have := Nat.le_of_dvd three_pos h; omega
  have nN := norm_natCast_eq_one hm
  have hΔ' : -16 * (4 * lam A ^ 3 + 27 * lam B ^ 2) = 1 := by
    simpa only [map_mul, map_add (f := _), map_pow, map_neg, map_ofNat, map_one] using congrArg lam hΔ
  have hsq : lam α ^ 2 = -(2 * (m : ℂ_[p]) + 1) := by
    simpa only [map_pow, map_neg, map_add (f := _), map_mul, map_ofNat, map_one, map_natCast] using congrArg lam hα
  have na : ‖lam α‖ = 1 := by
    have := congrArg norm hsq
    push_cast at nN
    rw [norm_pow, norm_neg, nN] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 this
  have nD : ‖4 * lam A ^ 3 + 27 * lam B ^ 2‖ = 1 := by
    have := congrArg norm hΔ'
    rwa [norm_mul, norm_neg, show (16 : ℂ_[p]) = 2 ^ 4 by norm_num, norm_pow, n2, one_pow, one_mul, norm_one] at this
  have tI := fun x y h => GlobalTheory.TorsionIntegral.norm_x_le_one_of_nsmul_eq_zero ℂ_[p] (lam A) (lam B) (2 * m + 1) x y h hA hB nN
  have tU := GlobalTheory.torsion_points_distinct_mod_maximal_ideal ℂ_[p] (lam A) (lam B) (2 * m + 1) hA hB n2 nD (odd_two_mul_add_one m) tI
  refine rigid (GL3Theta.Wp p) (Subring.isClosed_topologicalClosure _) (fun _ => norm_le_one_of_mem_Wp)
    (GlobalTheory.exists_mem_Wp_norm_sub_lt_one p) (n := n₀.map lam) (h := h₀.map lam) n2 n3 hA hB na hsq hΔ' (mn₀.map _) (mh₀.map _)
    (by rw [mn₀.natDegree_map, dn₀, dn]) (by rw [mh₀.natDegree_map, ← mh₀.natDegree_map i, hh₀, dh])
    (IsAlgClosed.splits _) ?_ ?_ ?_ ?_ ?_
  · rw [isCoprime_map, ← isCoprime_map i, hn₀, hh₀]
    exact hc
  · simpa only [Polynomial.map_add (f := _), Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_sub, map_C, map_X,
      Polynomial.map_ofNat, ← derivative_map, map_mul, map_pow] using congrArg (Polynomial.map lam) e₀
  · intro x hx
    obtain ⟨y, hxy, z⟩ := pts x hx
    exact tI x y hxy z
  · intro x hx
    obtain ⟨y, hxy, z⟩ := pts x hx
    exact (tU x y hxy z).1
  · intro x x' hx hx'
    obtain ⟨y, hxy, z⟩ := pts x hx
    obtain ⟨y', hxy', z'⟩ := pts x' hx'
    exact (tU x y hxy z).2 x' y' hxy' z'

end Padic

theorem modelEx_holds : ∀ D : D7, GL3Theta.modelEx D := by
  intro D p _ lam cc δ h1 _ h2
  have hD := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨L, hL, hΔ, hj⟩ := GlobalTheory.CurveAlgebraic.exists_periodPair D hD cc δ ⟨h1, h2⟩
  obtain ⟨e2, e3, -, -, hwp, -⟩ := GlobalTheory.LatticeInvariants.invariants_dictionary L _ hL
  obtain ⟨⟨-, m2, m3⟩, ht⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hD).2 cc δ ⟨h1, h2⟩
  have a2 : -(g2 (lamOf D cc δ)) / 4 ∈ Qbar := div_mem (neg_mem m2) (ofNat_mem _ 4)
  have a3 : -(g3 (lamOf D cc δ)) / 4 ∈ Qbar := div_mem (neg_mem m3) (ofNat_mem _ 4)
  let A : Qbar := ⟨_, a2⟩
  let B : Qbar := ⟨_, a3⟩
  have eA : (A : ℂ) = -L.g₂ / 4 := by rw [← e2]
  have eB : (B : ℂ) = -L.g₃ / 4 := by rw [← e3]
  have hV : wModel lam (lamOf D cc δ) = ⟨0, 0, 0, lam A, lam B⟩ := by
    rw [wModel, lamC, lamC, dite_eq_left a2, dite_eq_left a3]
  have hΔ' : -16 * (4 * A ^ 3 + 27 * B ^ 2) = 1 := Qbar.val.toRingHom.injective (by
    simp only [map_pow, map_neg, map_add (f := _), map_mul, map_ofNat, map_one]
    change -16 * (4 * (A : ℂ) ^ 3 + 27 * (B : ℂ) ^ 2) = 1
    rw [eA, eB]
    linear_combination hΔ)
  have hj' : IsIntegral ℤ ((-48 * (A : ℂ)) ^ 3) := by
    rwa [eA, show (-48 * (-L.g₂ / 4)) ^ 3 = 1728 * L.g₂ ^ 3 by ring]
  have hΔp : -16 * (4 * lam A ^ 3 + 27 * lam B ^ 2) = 1 := by
    simpa only [map_mul, map_add (f := _), map_pow, map_neg, map_ofNat, map_one] using congrArg lam hΔ'
  have d₂ : (wModel lam (lamOf D cc δ)).Δ = 1 := by
    simp only [hV, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    linear_combination hΔp
  refine ⟨?_, fun hp hin => ⟨1, ?_⟩, fun C hC => ?_⟩
  · obtain ⟨C, E, hC, i1, i2, i3, i4, i6, hE⟩ := exists_integral_model lam A B hΔ' hj'
    refine ⟨C, ?_⟩
    simp only [GL3Theta.IsModelU, hV, hC, IsIntP, hE, norm_one]
    exact ⟨i1, i2, i3, i4, i6, trivial⟩
  · have n2 : ‖(2 : ℂ_[p])‖ = 1 := norm_natCast_eq_one (N := 2) fun h => by have := Nat.le_of_dvd two_pos h; omega
    have n3 : ‖(3 : ℂ_[p])‖ = 1 :=
      norm_natCast_eq_one (N := 3) fun h => by have := Nat.le_of_dvd three_pos h; omega
    have hA : ‖lam A‖ ≤ 1 := by
      have i0 : IsIntegral ℤ ((-48 * A) ^ 3) :=
        (isIntegral_algHom_iff (Qbar.val.toRingHom.toIntAlgHom) Subtype.val_injective).mp (by
          rw [map_pow, map_mul, map_neg, map_ofNat]; exact hj')
      have := norm_map_le_one lam i0
      rw [map_pow, map_mul, map_neg, map_ofNat, show (48 : ℂ_[p]) = 2 ^ 4 * 3 by norm_num, norm_pow, norm_mul,
        norm_neg, norm_mul, norm_pow, n2, n3, one_pow, one_mul, one_mul] at this
      exact (pow_le_one_iff_of_nonneg (norm_nonneg _) three_ne_zero).1 this
    have hB : ‖lam B‖ ≤ 1 := by
      have e : 2 ^ 4 * 3 ^ 3 * lam B ^ 2 = -1 + -(2 ^ 6 * lam A ^ 3) := by linear_combination -hΔp
      have := IsUltrametricDist.norm_add_le_max (-1 : ℂ_[p]) (-(2 ^ 6 * lam A ^ 3))
      rw [← e] at this
      simp only [norm_mul, norm_pow, norm_neg, n2, n3, one_pow, one_mul, norm_one] at this
      exact (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1
        (this.trans (max_le le_rfl (pow_le_one₀ (norm_nonneg _) hA)))
    obtain ⟨m, hm⟩ : ∃ m, D.host.d = 2 * m + 1 := ⟨D.host.d / 2, by have := D.host.hyp.2.2.2.1; omega⟩
    have hpm : ¬ p ∣ 2 * m + 1 := fun hdvd => by
      rw [GL3Theta.InertK, jacobiSym.eq_zero_iff_not_coprime.2] at hin
      · exact absurd hin (by norm_num)
      · rw [Int.neg_gcd, Int.gcd_natCast_natCast, hm, Nat.gcd_eq_right hdvd]
        omega
    have hb := Formalism.FrobeniusOrbits.SplitK.bK_sq (D.host.sqd_sq)
    obtain ⟨b, hb⟩ : ∃ b : D.host.K, b ^ 2 = -(D.host.d : D.host.K) := ⟨_, hb⟩
    have hbi : IsIntegral ℤ b := IsIntegral.of_pow two_pos (by
      rw [hb]; exact (isIntegral_natCast _).neg)
    have hbc : D.host.φ₀ (b : D.host.E) ^ 2 = -(2 * (m : ℂ) + 1) := by
      have := congrArg (D.host.φ₀.comp D.host.K.val.toRingHom) hb
      rw [map_pow, map_neg, map_natCast, hm] at this
      push_cast at this
      exact this
    have hbq : D.host.φ₀ (b : D.host.E) ∈ Qbar := mem_algebraicClosure_iff.mpr
      ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b : D.host.E)).algHom D.host.φ₀.toRatAlgHom)
    obtain ⟨-, -, -, -, hcm⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hD cc δ ⟨h1, h2⟩
    obtain ⟨wA, wB⟩ := invariants_mem hp lam L A B ⟨_, hbq⟩ m eA eB hΔ' hA hB hpm
      (Qbar.val.toRingHom.injective (by
        simp only [map_pow, map_neg, map_add (f := _), map_mul, map_ofNat, map_one, map_natCast]
        exact hbc))
      (fun l hl => (hL _).1 (hcm ⟨b, hbi⟩ l ((hL _).2 hl)))
      (fun t h3 h4 => by
        have h5 : t ∉ lamOf D cc δ := fun h => h3 ((hL _).1 h)
        rw [← (hwp t h5).1, ← (hwp t h5).2]
        exact ht t ⟨2 * m + 1, by omega, (hL _).2 h4⟩ h5)
    refine ⟨?_, ?_⟩
    · simp only [GL3Theta.IsModelU, one_smul, d₂, norm_one, IsIntP]
      simp [hV, hA, hB]
    · simp only [GL3Theta.ModelOverW, one_smul, hV]
      exact ⟨zero_mem _, zero_mem _, zero_mem _, wA, wB⟩
  · have := hC.2.2.2.2.2
    rw [WeierstrassCurve.variableChange_Δ, d₂, mul_one, norm_pow, Units.val_inv_eq_inv_val, norm_inv,
      pow_eq_one_iff_of_nonneg (by positivity) (by norm_num)] at this
    exact inv_eq_one.1 this

end GlobalTheory.UnitModel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DatumCurveIntegralUnitDiscModelStatement
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.datum_curve_integral_unitDisc_model : ∀ D : D7, GL3Theta.modelEx D := by
  first | exact @GlobalTheory.UnitModel.modelEx_holds | exact GlobalTheory.UnitModel.modelEx_holds | (intros; apply GlobalTheory.UnitModel.modelEx_holds <;> assumption)
end
