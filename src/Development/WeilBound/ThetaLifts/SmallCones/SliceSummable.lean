module

public import Development.WeilBound.ThetaLifts.SmallCones.ExpAlg

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.SmallCones.ExpSum
noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix Classical
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst

theorem summable_lat_wt {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (L : Submodule ℤ V) [DiscreteTopology L] {k : ℕ} (hk : Module.finrank ℤ L < k) :
    Summable fun z : L => ((1 + ‖z‖)⁻¹) ^ k := by
  refine Summable.of_nonneg_of_le (fun z => by positivity) (fun z => ?_)
    ((ZLattice.summable_norm_pow_inv L k hk).add (hasSum_ite_eq (0 : L) (1 : ℝ)).summable)
  by_cases hz : z = 0
  · subst hz
    simp only [if_pos rfl, norm_zero, add_zero, inv_one, one_pow]
    exact le_add_of_nonneg_left (by positivity)
  · have h0 : 0 < ‖z‖ := norm_pos_iff.2 hz
    simp only [hz, if_false, add_zero]
    gcongr
    linarith

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def sz {κ : Type} [Fintype κ] (y : κ → AF F) : ℝ := 1 + ∑ j, ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (y j))

theorem norm_le_sz {κ : Type} [Fintype κ] (y : κ → AF F) : 1 + ‖fun j => evI F (y j)‖ ≤ sz y := by
  have h0 : ∀ j, 0 ≤ ∑ w : InfinitePlace F, mixedEmbedding.normAtPlace w (evI F (y j)) := fun j =>
    Finset.sum_nonneg fun w _ => mixedEmbedding.normAtPlace_nonneg _ _
  refine add_le_add_right ((pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ => h0 j)).2 fun j => ?_) 1
  refine le_trans ?_ (Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ j))
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  exact Finset.sup'_le _ _ fun w _ => Finset.single_le_sum (f := fun w => mixedEmbedding.normAtPlace w (evI F (y j)))
    (fun w _ => mixedEmbedding.normAtPlace_nonneg _ _) (Finset.mem_univ w)

theorem sz_pos {κ : Type} [Fintype κ] (y : κ → AF F) : 0 < sz y := lt_of_lt_of_le (by positivity) (norm_le_sz y)

theorem summable_wt {κ : Type} [Fintype κ] {C : Set (κ → Af F)} (hC : IsCompact C) : ∃ N : ℕ, Summable fun ξ : κ → F =>
    if (fun j => (algebraMap F (AF F) (ξ j)).2) ∈ C then (sz (fun j => algebraMap F (AF F) (ξ j)) ^ N)⁻¹ else 0 := by
  obtain ⟨N, hN, hK⟩ := exists_nat_mul_integral_of_isCompact F hC
  haveI := discreteTopology_denomLattice F κ hN
  refine ⟨Module.finrank ℤ (denomLattice F κ N) + 1, ?_⟩
  let S : Set (κ → F) := {ξ | (fun i => mixedEmbedding F (ξ i)) ∈ denomLattice F κ N}
  refine ((Subtype.val_injective (p := fun ξ => ξ ∈ S)).summable_iff ?_).1 ?_
  · intro ξ hξ
    refine if_neg fun h0 => hξ ⟨⟨ξ, fun i => ?_⟩, rfl⟩
    obtain ⟨y, hy⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 ((N : F) * ξ i) fun v => by
      rw [map_mul, map_natCast]
      exact hK _ h0 i v
    refine ⟨y, ?_⟩
    have h2 := congrArg (mixedEmbedding F) hy
    rw [← nsmul_eq_mul, map_nsmul, ← Nat.cast_smul_eq_nsmul ℝ] at h2
    exact h2.symm
  · let j : S → denomLattice F κ N := fun ξ => ⟨_, ξ.2⟩
    have hj : Function.Injective j := fun a b h => Subtype.ext (funext fun i =>
      mixedEmbedding_injective F (congrFun (congrArg Subtype.val h) i))
    refine Summable.of_nonneg_of_le (fun ξ => ?_) (fun ξ => ?_)
      ((summable_lat_wt (denomLattice F κ N) (Nat.lt_succ_self _)).comp_injective hj)
    · simp only [Function.comp_apply]
      split_ifs
      · exact inv_nonneg.2 (pow_pos (sz_pos _) _).le
      · exact le_rfl
    · simp only [Function.comp_apply]
      split_ifs
      · rw [inv_pow]
        refine inv_anti₀ (by positivity) (pow_le_pow_left₀ (by positivity) ?_ _)
        have h := norm_le_sz (fun i => algebraMap F (AF F) (ξ.1 i))
        have e : (fun i => evI F (algebraMap F (AF F) (ξ.1 i))) = fun i => mixedEmbedding F (ξ.1 i) :=
          funext fun i => (InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp F).symm
        rw [e] at h
        exact h
      · positivity

variable {n d n₁ d₁ m : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
  {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E}
  {I : Set (Ten F E n d)} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {u z : Fin m → Matrix (Fin n) (Fin d) E}

theorem slice_bound (hS : Slice) (hB : B.IsGood σ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) (he : IsEv B M M₁ ι ι' I e)
    (hD : Dual σ X W I u z) {l} (hl : l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁)) {φ} (hφ : φ ∈ SB (Fin n × Fin d → Af F)) :
    ∃ (wt : (Fin m → F) → ℝ) (P : SInf F (Fin n × Fin d) → ℝ), Summable wt ∧ Continuous P ∧ P 0 = 0 ∧
      ∀ y (f : SInf F (Fin n × Fin d)),
        ‖l (e (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) (pureA F f φ)))‖ ≤ P f * wt y := by
  obtain ⟨r, φ₁, C, A, h1, hC, -, h2, h3, h4⟩ := hS F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e he m u z hD φ hφ
  obtain ⟨N, hN⟩ := summable_wt hC
  choose T hT using fun i => hl (φ₁ i) (h1 i)
  choose p hp hq using fun i => h4 ((normSeminorm ℂ ℂ).comp (T i).toLinearMap) N (T i).continuous.norm
  refine ⟨_, fun f => ∑ i, p i f, hN, continuous_finsetSum _ fun i _ => hp i, by simp, fun y f => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, map_sum]
  simp only [hT]
  split_ifs with hy
  · rw [Finset.sum_mul]
    refine norm_sum_le_of_le _ fun i _ => ?_
    rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos (sz_pos _) _)]
    exact hq i i _ f
  · simp [h3 _ _ hy]

end PositivityTheory.ThKCT
end
end

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d n₁ d₁ m : ℕ} {B : Base F E} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
  {M : Model σ X W} {M₁ : Model σ X₁ W₁} {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E}
  {I : Set (Ten F E n d)} {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} {u z : Fin m → Matrix (Fin n) (Fin d) E}

def rhoL (B : Base F E) (M : Model σ X W) (w : Ten F E n d) : Fn F n d →ₗ[ℂ] Fn F n d where
  toFun := M.co.rho B.ψ w
  map_add' := rho_add _ _ _
  map_smul' := rho_smul _ _ _

theorem slice_summable (hS : Slice) (hB : B.IsGood σ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) (he : IsEv B M M₁ ι ι' I e)
    (hD : Dual σ X W I u z) {l} (hl : l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁)) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
    Summable fun y : Fin m → F => l (e (rhoL B M (lin u fun j => algebraMap F (AF F) (y j)) Φ)) := by
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, hg, rfl⟩ := h
    obtain ⟨wt, P, h1, -, -, h2⟩ := slice_bound hS hB hM hM₁ he hD hl hg
    exact Summable.of_norm_bounded (h1.mul_left (P f)) fun y => h2 y f
  | zero => simpa using summable_zero
  | add Φ Ψ _ _ h1 h2 => simpa only [map_add (f := _)] using h1.add h2
  | smul c Φ _ h => simpa only [map_smul, smul_eq_mul] using h.mul_left c

theorem slice_adm (hS : Slice) (hB : B.IsGood σ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) (he : IsEv B M M₁ ι ι' I e)
    (hD : Dual σ X W I u z) {l} (hl : l ∈ (adeleClass F).adm (Fin n₁ × Fin d₁)) :
    ∃ L ∈ (adeleClass F).adm (Fin n × Fin d), ∀ Φ ∈ schA F (Fin n × Fin d),
      HasSum (fun y : Fin m → F => l (e (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) Φ))) (L Φ) := by
  let L₀ : schA F (Fin n × Fin d) →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => ∑' y : Fin m → F, l (e (rhoL B M (lin u fun j => algebraMap F (AF F) (y j)) Φ.1))
      map_add' := fun Φ Ψ => by
        simp only [Submodule.coe_add, map_add (f := _)]
        exact (slice_summable hS hB hM hM₁ he hD hl Φ.2).tsum_add (slice_summable hS hB hM hM₁ he hD hl Ψ.2)
      map_smul' := fun c Φ => by
        simp only [Submodule.coe_smul, map_smul, smul_eq_mul, RingHom.id_apply]
        exact tsum_mul_left }
  obtain ⟨L, hL⟩ := LinearMap.exists_extend L₀
  have hL' : ∀ Φ ∈ schA F (Fin n × Fin d),
      HasSum (fun y : Fin m → F => l (e (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) Φ))) (L Φ) := fun Φ hΦ => by
    rw [show L Φ = L₀ ⟨Φ, hΦ⟩ from LinearMap.congr_fun hL ⟨Φ, hΦ⟩]
    exact (slice_summable hS hB hM hM₁ he hD hl hΦ).hasSum
  refine ⟨L, fun g hg => ?_, hL'⟩
  obtain ⟨wt, P, h1, h2, h3, h4⟩ := slice_bound hS hB hM hM₁ he hD hl hg
  let T : SInf F (Fin n × Fin d) →ₗ[ℂ] ℂ :=
    { toFun := fun f => L (pureA F f g)
      map_add' := fun f₁ f₂ => by
        rw [← map_add (f := _)]; congr 1; funext x; simp [pureA, add_mul]
      map_smul' := fun c f => by
        rw [RingHom.id_apply, ← map_smul]; congr 1; funext x; simp [pureA, mul_assoc] }
  refine ⟨⟨T, continuous_of_continuousAt_zero T ?_⟩, fun f => rfl⟩
  rw [ContinuousAt, map_zero]
  refine squeeze_zero_norm (a := fun f => P f * ∑' y, wt y) (fun f => ?_) ?_
  · exact (hL' _ (Submodule.subset_span ⟨f, g, hg, rfl⟩)).norm_le_of_bounded (h1.hasSum.mul_left (P f)) fun y => h4 y f
  · simpa [h3] using (h2.tendsto 0).mul_const (∑' y, wt y)

theorem term_zero (h : IsStd B.ψ) (a : (Fin m → F) → Fn F n d → ℂ)
    (ha : ∀ y t, ∀ Φ ∈ schA F (Fin n × Fin d), a y (M.co.rho B.ψ (lin z t) Φ) =
      B.ψ (-((fun j => algebraMap F (AF F) (y j)) ⬝ᵥ t)) * a y Φ)
    (h0 : ∀ Φ ∈ schA F (Fin n × Fin d), HasSum (fun y => a y Φ) 0) (y) {Φ} (hΦ : Φ ∈ schA F (Fin n × Fin d)) : a y Φ = 0 := by
  refine fourier_uniq h (fun y => a y Φ) (h0 Φ hΦ).summable (fun t => ?_) y
  rw [← (h0 _ (rho_mem M h (lin z (-t)) hΦ)).tsum_eq]
  exact tsum_congr fun y => by rw [ha y _ Φ hΦ, dotProduct_neg, neg_neg, mul_comm]

theorem thetaExp_of (hS : Slice) : ThetaExp := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e he m u z hP
  have h := hB.std
  obtain ⟨l, hl, hθ⟩ := (GlobalTheory.CompanionTheory.ThetaAdm.theta_adm F (Fin n₁ × Fin d₁)).2.1
  obtain ⟨L, hL, hs⟩ := slice_adm hS hB hM hM₁ he hP.toDual hl
  have hs' : ∀ Φ ∈ schA F (Fin n × Fin d), HasSum (fun y : Fin m → F =>
      thetaSum F (e (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) Φ))) (L Φ) := fun Φ hΦ => by
    simpa only [hθ _ (he.maps _ (rho_mem M h _ hΦ))] using hs Φ hΦ
  have hu : ∀ a : Fin m → F, ∀ Φ ∈ schA F (Fin n × Fin d),
      L (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (a j)) Φ) = L Φ := fun a Φ hΦ => by
    refine (hs' _ (rho_mem M h _ hΦ)).unique ?_
    have := (Equiv.addRight a).hasSum_iff.2 (hs' Φ hΦ)
    convert this using 2 with y
    rw [rho_rho_of _ _ _ _ (sy_lin_uu M hP _ _), ← lin_add]
    simp only [Function.comp_apply, Equiv.coe_addRight, Pi.add_apply, map_add (f := _)]
    rfl
  have hz : ∀ b : Fin m → F, ∀ Φ ∈ schA F (Fin n × Fin d),
      L (M.co.rho B.ψ (lin z fun j => algebraMap F (AF F) (b j)) Φ) = L Φ := fun b Φ hΦ => by
    refine (hs' _ (rho_mem M h _ hΦ)).unique ?_
    convert hs' Φ hΦ using 2 with y
    rw [ev_rho_uz h he hP _ _ hΦ,
      show -((fun j => algebraMap F (AF F) (y j)) ⬝ᵥ fun j => algebraMap F (AF F) (b j)) = algebraMap F (AF F) (-(y ⬝ᵥ b)) by
        simp [dotProduct], h.2.1, one_smul]
  have hm : ∀ x₁ : Matrix (Fin n₁) (Fin d₁) E, ∀ Φ ∈ schA F (Fin n × Fin d),
      L (M.co.rho B.ψ (incM F ι * incM F x₁ * (incM F ι')ᵀ) Φ) = L Φ := fun x₁ Φ hΦ => by
    refine (hs' _ (rho_mem M h _ hΦ)).unique ?_
    convert hs' Φ hΦ using 2 with y
    obtain ⟨a, b, hab⟩ := hM₁.rat x₁
    rw [ev_rho_um h he hP _ _ hΦ, Darboux.rho, hab, theta_schr_rat h]
  obtain ⟨c, hc⟩ := thetaUniq_of F (Fin n × Fin d) B.ψ h L hL fun ξ η Φ hΦ => by
    obtain ⟨x, hx⟩ := rat_surj hB.cm.2.2.1 M.co.e hM.rat ξ η
    obtain ⟨a, b, x₁, hr⟩ := rho_rat (M := M) h hP x
    rw [← hx, ← Darboux.rho, hr, hu _ _ (rho_mem M h _ (rho_mem M h _ hΦ)), hz _ _ (rho_mem M h _ hΦ), hm _ _ hΦ]
  have hc0 : c ≠ 0 := by
    rintro rfl
    obtain ⟨Φ, hΦ, hne⟩ := ev_ne_zero hM hM₁ he
    refine hne (thetaInj_of F _ B.ψ h _ (he.maps Φ hΦ) fun w => ?_)
    obtain ⟨w, rfl⟩ := M₁.co.e.surjective w
    have := term_zero (M := M) (z := z) h
      (fun y Φ => thetaSum F (e (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) Φ)))
      (fun y t Φ hΦ => by rw [ev_rho_uz h he hP _ _ hΦ, thetaSum_smul])
      (fun Φ hΦ => by simpa only [hc Φ hΦ, zero_mul] using hs' Φ hΦ) 0 (rho_mem M h (incM F ι * w * (incM F ι')ᵀ) hΦ)
    rwa [show (fun j => algebraMap F (AF F) ((0 : Fin m → F) j)) = 0 from funext fun j => map_zero _, lin_zero, rho_zero,
      he.Heisenberg₂ _ _ hΦ] at this
  refine ⟨c⁻¹, inv_ne_zero hc0, fun Φ hΦ => ?_⟩
  simpa only [hc Φ hΦ, inv_mul_cancel_left₀ hc0] using (hs' Φ hΦ).mul_left c⁻¹

theorem evUniq_of (hE : ThetaExp) : EvUniq := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e e' he he' m u z hP
  have h := hB.std
  obtain ⟨C, hC, hs⟩ := hE F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e he m u z hP
  obtain ⟨C', hC', hs'⟩ := hE F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ hB hM hM₁ ι ι' I e' he' m u z hP
  refine ⟨C'⁻¹ * C, mul_ne_zero (inv_ne_zero hC') hC, fun Φ hΦ => ?_⟩
  have key : C • e Φ + (-C') • e' Φ = 0 := by
    refine thetaInj_of F _ B.ψ h _ (add_mem (Submodule.smul_mem _ _ (he.maps Φ hΦ)) (Submodule.smul_mem _ _ (he'.maps Φ hΦ)))
      fun w => ?_
    obtain ⟨w, rfl⟩ := M₁.co.e.surjective w
    have := term_zero (M := M) (z := z) h
      (fun y Φ => C * thetaSum F (e (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) Φ)) -
        C' * thetaSum F (e' (M.co.rho B.ψ (lin u fun j => algebraMap F (AF F) (y j)) Φ)))
      (fun y t Φ hΦ => by rw [ev_rho_uz h he hP _ _ hΦ, ev_rho_uz h he' hP _ _ hΦ, thetaSum_smul, thetaSum_smul]; ring)
      (fun Φ hΦ => by simpa only [sub_self] using (hs Φ hΦ).sub (hs' Φ hΦ)) 0 (rho_mem M h (incM F ι * w * (incM F ι')ᵀ) hΦ)
    rw [show (fun j => algebraMap F (AF F) ((0 : Fin m → F) j)) = 0 from funext fun j => map_zero _, lin_zero, rho_zero,
      he.Heisenberg₂ _ _ hΦ, he'.Heisenberg₂ _ _ hΦ] at this
    rw [← Darboux.rho, rho_add, rho_smul, rho_smul,
      thetaSum_add F (Submodule.smul_mem _ _ (rho_mem M₁ h _ (he.maps Φ hΦ))) (Submodule.smul_mem _ _ (rho_mem M₁ h _ (he'.maps Φ hΦ))),
      thetaSum_smul, thetaSum_smul, ← this]
    ring
  rw [mul_smul, eq_neg_of_add_eq_zero_left key, neg_smul, neg_neg, smul_smul, inv_mul_cancel₀ hC', one_smul]

end PositivityTheory.ThKCT
