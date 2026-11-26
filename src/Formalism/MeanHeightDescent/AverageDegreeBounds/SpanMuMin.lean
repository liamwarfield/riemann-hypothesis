module

public import Formalism.MeanHeightDescent.MuMaxMinkowski
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FinSup
public import Formalism.MeanHeightDescent.BadRowsNumeric
public import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtImage

@[expose] public section

section -- merged from Formalism.MeanHeightDescent.AverageDegreeBounds.SpanMuMin
open Module NumberField

noncomputable section

namespace Formalism.ExtensionFiltration

open Formalism.HN

section

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V]
  [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι]

theorem majAt_self_re (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K)
    (x : V) : (Formalism.HermitianLatticesTheory.majAt b X v x x).re = Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 := by
  unfold Formalism.HermitianLatticesTheory.majAt Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity)), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re] <;> ring

theorem rkK_span_singleton (x : V) (hx : x ≠ 0) :
    rkK (K := K) (Submodule.span (𝓞 K) ({x} : Set V)) = 1 := by
  unfold rkK
  rw [Submodule.span_span_of_tower, finrank_span_singleton hx]

theorem muDef_line (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (x : V) (hx : x ≠ 0) (Λ : ℝ)
    (hn : ∀ v, Formalism.HermitianLatticesTheory.normAt b X v x ≤ Real.exp Λ) :
    -(2 * Λ) ≤ muDef b X (Submodule.span (𝓞 K) ({x} : Set V)) := by
  classical
  set L := Submodule.span (𝓞 K) ({x} : Set V) with hLdef
  have hFG : L.FG := Submodule.fg_span_singleton x
  have hne : L ≠ ⊥ := by
    rw [hLdef, Ne, Submodule.span_singleton_eq_bot]
    exact hx
  obtain ⟨-, -, hpos⟩ := Formalism.HN.place_lattice_structure K V ι b X hX L hFG
  have hmu := (Formalism.HN.size_maximal_slope K V ι b X hX L hFG hne).2.1
  have hli : LinearIndependent K ![x] := linearIndependent_unique_iff.mpr (by simpa using hx)
  have hr : Set.range ![x] = ({x} : Set V) := by
    rw [Set.range_unique]
    simp
  obtain ⟨hht, -⟩ := Formalism.HN.height_gram_determinant K V ι b X hX 1 ![x] hli
  rw [hr] at hht
  have hg : ∀ v, (gramPl b X v ![x]).det.re = Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 := by
    intro v
    rw [Matrix.det_unique]
    exact majAt_self_re b X v x
  simp only [hg] at hht
  have hrk : rkK (K := K) L = 1 := rkK_span_singleton x hx
  have hnPl : 0 < nPl K := Fintype.card_pos
  have hle : ht b X L ≤ (Real.exp Λ ^ 2) ^ nPl K := by
    rw [hht]
    calc ∏ v, Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 ≤ ∏ _v : InfinitePlace K, Real.exp Λ ^ 2 :=
          Finset.prod_le_prod₀ (fun v _ => by positivity)
            (fun v _ => pow_le_pow_left₀ (by unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm; exact Real.sqrt_nonneg _)
              (hn v) 2)
      _ = (Real.exp Λ ^ 2) ^ nPl K := by rw [Finset.prod_const, Finset.card_univ]; rfl
  have hlog : Real.log (ht b X L) ≤ (nPl K : ℝ) * (2 * Λ) := by
    have h1 := Real.log_le_log hpos hle
    rwa [Real.log_pow, Real.log_pow, Real.log_exp] at h1
  rw [hmu]
  unfold size
  rw [hrk, Real.log_rpow hpos]
  have hn' : (0 : ℝ) < nPl K := by exact_mod_cast hnPl
  have key : 1 / (2 * (nPl K : ℝ) * ((1 : ℕ) : ℝ)) * Real.log (ht b X L) ≤ Λ := by
    rw [Nat.cast_one, mul_one, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith
  linarith

theorem muMin_line (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (x : V) (hx : x ≠ 0) (θ : ℝ)
    (hθ : θ ≤ slope (Formalism.HermitianLatticesTheory.realize b X) (Submodule.span (𝓞 K) ({x} : Set V))) :
    θ ≤ muMin (Formalism.HermitianLatticesTheory.realize b X) (Submodule.span (𝓞 K) ({x} : Set V)) := by
  classical
  have hFG : (Submodule.span (𝓞 K) ({x} : Set V)).FG := Submodule.fg_span_singleton x
  obtain ⟨hLat, hrkL, -⟩ := Formalism.HN.place_lattice_structure K V ι b X hX _ hFG
  have hne : Submodule.span (𝓞 K) ({x} : Set V) ≠ ⊥ := by
    rw [Ne, Submodule.span_singleton_eq_bot]
    exact hx
  obtain ⟨-, hmin, -, -, -⟩ := Formalism.HN.slope_characterization (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) _ hLat hne
  rw [hmin]
  intro N hN
  obtain ⟨-, hmono, -, hzero, hdeg0, -⟩ := Formalism.HN.saturation_basic_properties (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) _ hLat
  have hK : 0 < Module.finrank ℚ K := Module.finrank_pos
  rw [rkK_span_singleton x hx, mul_one] at hrkL
  by_cases hN0 : N = ⊥
  · subst hN0
    rw [hdeg0, (hzero ⊥ bot_le).mpr rfl]
    have hpos : (0 : ℝ) < (rk (Formalism.HermitianLatticesTheory.realize b X) (Submodule.span (𝓞 K) ({x} : Set V)) : ℝ) := by
      rw [hrkL]; exact_mod_cast hK
    have hθ' : θ ≤ deg (Formalism.HermitianLatticesTheory.realize b X) (Submodule.span (𝓞 K) ({x} : Set V)) /
        (rk (Formalism.HermitianLatticesTheory.realize b X) (Submodule.span (𝓞 K) ({x} : Set V)) : ℝ) := hθ
    rw [le_div_iff₀ hpos] at hθ'
    simpa using hθ'
  · have hNoeth : IsNoetherian (𝓞 K) (Submodule.span (𝓞 K) ({x} : Set V)) :=
      isNoetherian_of_fg_of_noetherian _ hFG
    have hNFG : N.FG := by
      have h1 := (IsNoetherian.noetherian (N.comap (Submodule.span (𝓞 K) ({x} : Set V)).subtype)).map
        (Submodule.span (𝓞 K) ({x} : Set V)).subtype
      rwa [Submodule.map_comap_subtype, inf_eq_right.mpr hN] at h1
    obtain ⟨-, hrkN, -⟩ := Formalism.HN.place_lattice_structure K V ι b X hX N hNFG
    haveI : FiniteDimensional K V := Module.Finite.of_basis b
    have hkN : rkK (K := K) N = 1 := by
      have hle : Submodule.span K (N : Set V) ≤ Submodule.span K ({x} : Set V) := by
        rw [Submodule.span_le]
        intro y hy
        have hy' := hN hy
        rw [Submodule.mem_span_singleton] at hy'
        obtain ⟨a, rfl⟩ := hy'
        rw [SetLike.mem_coe, ← algebraMap_smul K a x]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
      have h1 : rkK (K := K) N ≤ 1 := by
        unfold rkK
        calc Module.finrank K (Submodule.span K (N : Set V))
            ≤ Module.finrank K (Submodule.span K ({x} : Set V)) := Submodule.finrank_mono hle
          _ = 1 := finrank_span_singleton hx
      have h2 : 0 < rkK (K := K) N := by
        unfold rkK
        apply Module.finrank_pos_iff_exists_ne_zero.mpr
        obtain ⟨y, hyN, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
        exact ⟨⟨y, Submodule.subset_span hyN⟩, fun h => hy0 (congrArg Subtype.val h)⟩
      omega
    rw [hkN, mul_one] at hrkN
    have hrkNL : rk (Formalism.HermitianLatticesTheory.realize b X) N = rk (Formalism.HermitianLatticesTheory.realize b X) (Submodule.span (𝓞 K) ({x} : Set V)) := by
      rw [hrkN, hrkL]
    rw [hrkNL, sub_self, mul_zero, sub_nonneg]
    exact (hmono N _ hN le_rfl).2 hrkNL

end

theorem span_min_slope : SpanMuMin := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX B Λ hB hB0 hs
  obtain ⟨s, hsB, hsn, hspan⟩ := hs
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  set θ : ℝ := (-(2 * Λ) + Real.log 2 - logDisc K / (Module.finrank ℚ K : ℝ)) / 2 with hθ
  obtain ⟨hlat, hrkB, -⟩ := place_lattice_structure K V ι b X hX B hB
  obtain ⟨hsat, hmin, hcont, -⟩ :=
    hnStep_of degree_supermodular slope_characterization maximal_slope_ratio finite_supremum_slopes real_saturation_property saturation_basic_properties
      (𝓞 K) V _ ρ B hlat θ
  set S := hnStep ρ B θ with hS
  have hmem : ∀ x ∈ s, x ∈ S := by
    intro x hx
    by_cases hx0 : x = 0
    · rw [hx0]; exact S.zero_mem
    · have hle : Submodule.span (𝓞 K) ({x} : Set V) ≤ B :=
        (Submodule.span_singleton_le_iff_mem x B).2 (hsB hx)
      have hne : Submodule.span (𝓞 K) ({x} : Set V) ≠ ⊥ := fun h =>
        hx0 ((Submodule.span_singleton_eq_bot).1 h)
      have hmu := muDef_line b X hX x hx0 Λ (hsn x hx)
      have hsl : θ ≤ slope ρ (Submodule.span (𝓞 K) ({x} : Set V)) := by
        unfold muDef at hmu
        rw [hθ]
        linarith
      exact hcont _ hle hne (muMin_line b X hX x hx0 θ hsl) (Submodule.mem_span_singleton_self x)
  have hSfg : S.FG := Submodule.FG.of_le hB hsat.1
  have hrkS := (place_lattice_structure K V ι b X hX S hSfg).2.1
  have hspanEq : Submodule.span K (S : Set V) = Submodule.span K (B : Set V) := by
    refine le_antisymm (Submodule.span_mono hsat.1) (Submodule.span_le.2 ?_)
    intro y hy
    exact Submodule.span_mono (fun x hx => hmem x hx) (hspan hy)
  have hrkK : rkK (K := K) S = rkK (K := K) B := by
    unfold rkK
    rw [hspanEq]
  have hBS : B = S :=
    (saturation_basic_properties (𝓞 K) V _ ρ B hlat).2.2.1 S B hsat hsat.1 le_rfl (by rw [hrkB, hrkS, hrkK])
  have hfin : θ ≤ muMin ρ B := by
    have := hmin (by rw [← hBS]; exact hB0)
    rwa [← hBS] at this
  unfold muMinDef
  rw [hθ] at hfin
  linarith

end Formalism.ExtensionFiltration
end
end

section -- merged from Formalism.MeanHeightDescent.AverageDegreeBounds.CovolumeAssemblyHolds
open Module NumberField

noncomputable section

namespace Formalism.ExtensionFiltration

theorem log_covolume_slope_mu :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
      (d : ℕ), 0 < d → ∀ X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ,
      (∀ v, IsUnit (X v).det) → ∀ M : Submodule (𝓞 K) (Fin d → K),
      Submodule.IsFullLattice K M →
      Formalism.DivisionValues.lcv X M = -((d : ℝ) * Formalism.HN.muDef (Pi.basisFun K (Fin d)) X M) := by
  intro K _ _ _ _ d hd X hX M hM
  have hfg : M.FG := hM.toIsLattice.fg
  have hspan : Submodule.span K (M : Set (Fin d → K)) = ⊤ :=
    Submodule.IsFullLattice.span_eq_top (self := hM)
  have hrk : Formalism.HN.rkK M = d := by
    unfold Formalism.HN.rkK
    rw [hspan]
    simp
  have hne : M ≠ ⊥ := by
    intro h
    have h2 : Formalism.HN.rkK (⊥ : Submodule (𝓞 K) (Fin d → K)) = 0 := by
      unfold Formalism.HN.rkK
      simp
    rw [h, h2] at hrk
    omega
  obtain ⟨-, hmu, -⟩ := Formalism.HN.size_maximal_slope K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX M hfg hne
  have hht : 0 < Formalism.HN.ht (Pi.basisFun K (Fin d)) X M :=
    (Formalism.HN.place_lattice_structure K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X hX M hfg).2.2
  have hn : (finrank ℚ K : ℝ) = 2 * (Formalism.HN.nPl K : ℝ) := by
    exact_mod_cast Formalism.HN.sizeMu_finrank_eq K
  have hf : (0 : ℝ) < Formalism.HN.nPl K := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card (InfinitePlace K))
  have hDr : (0 : ℝ) < d := by exact_mod_cast hd
  rw [hmu, Formalism.HN.size, Real.log_rpow hht, hrk, Formalism.DivisionValues.lcv, hn]
  field_simp


end Formalism.ExtensionFiltration
end
end

section -- merged from Formalism.MeanHeightDescent.AverageDegreeBounds.MuMaxMinkowski
open Module NumberField

noncomputable section

namespace Formalism.ExtensionFiltration

open Formalism.HN

section

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
  [Module K V] [Fintype ι] [DecidableEq ι]

theorem mink_norm_sq_realize (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V) :
    ‖Formalism.HermitianLatticesTheory.realize b X x‖ ^ 2 = ∑ v, Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 := by
  have h1 : ∀ v, Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 = ∑ i, ‖Formalism.HermitianLatticesTheory.fcoord b X v x i‖ ^ 2 := by
    intro v
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm
    exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => by positivity))
  simp only [h1]
  unfold Formalism.HermitianLatticesTheory.realize Formalism.HermitianLatticesTheory.realizeRaw
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two]
  simp [Real.norm_eq_abs, sq_abs, Complex.sq_norm, Complex.normSq_apply]
  ring

theorem mink_normAt_pos (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (v : InfinitePlace K) (x : V) (hx : x ≠ 0) :
    0 < Formalism.HermitianLatticesTheory.normAt b X v x := by
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.cnorm
  apply Real.sqrt_pos.mpr
  have hne : Formalism.HermitianLatticesTheory.fcoord b X v x ≠ 0 := by
    unfold Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
    intro h0
    have h1 : (fun i => v.embedding (b.repr x i)) = 0 := by
      have h3 := congrArg (fun w => (X v).mulVec w) h0
      simp only [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (hX v), Matrix.one_mulVec,
        Matrix.mulVec_zero] at h3
      exact h3
    apply hx
    have h2 : b.repr x = 0 := by
      ext i
      have h4 := congrFun h1 i
      simp only [Pi.zero_apply] at h4
      rw [Finsupp.zero_apply]
      exact (map_eq_zero v.embedding).mp h4
    exact b.repr.map_eq_zero_iff.mp h2
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
  have hpos : 0 < ‖Formalism.HermitianLatticesTheory.fcoord b X v x i‖ ^ 2 := pow_pos (norm_pos_iff.mpr hi) 2
  exact lt_of_lt_of_le hpos (Finset.single_le_sum (f := fun j => ‖Formalism.HermitianLatticesTheory.fcoord b X v x j‖ ^ 2)
    (fun j _ => by positivity) (Finset.mem_univ i))

theorem mink_am_gm {σ : Type} [Fintype σ] [Nonempty σ] (a : σ → ℝ) (ha : ∀ v, 0 < a v) :
    (Fintype.card σ : ℝ) * Real.exp (2 * ((1 / (Fintype.card σ : ℝ)) * ∑ v, Real.log (a v))) ≤
      ∑ v, a v ^ 2 := by
  set n : ℝ := (Fintype.card σ : ℝ) with hn_def
  have hn : 0 < n := Nat.cast_pos.mpr Fintype.card_pos
  have hw : ∑ _v : σ, (1 / n) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hn_def, mul_one_div_cancel hn.ne']
  have hJ := convexOn_exp.map_sum_le (t := Finset.univ) (w := fun _ => 1 / n)
    (p := fun v => 2 * Real.log (a v)) (fun _ _ => by positivity) hw (fun _ _ => Set.mem_univ _)
  simp only [smul_eq_mul] at hJ
  have hexp : ∀ v, Real.exp (2 * Real.log (a v)) = a v ^ 2 := fun v => by
    rw [two_mul, Real.exp_add, Real.exp_log (ha v)]
    ring
  have hL : ∑ v, 1 / n * (2 * Real.log (a v)) = 2 * (1 / n * ∑ v, Real.log (a v)) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  have hR : ∑ v, 1 / n * Real.exp (2 * Real.log (a v)) = 1 / n * ∑ v, a v ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [hexp v]
  rw [hL, hR] at hJ
  have h3 : n * (1 / n * ∑ v, a v ^ 2) = ∑ v, a v ^ 2 := by
    rw [← mul_assoc, mul_one_div_cancel hn.ne', one_mul]
  exact (mul_le_mul_of_nonneg_left hJ hn.le).trans_eq h3

end

theorem max_slope_minkowski : MuMaxMinkowski := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX B La hBfg hB0 hshort
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  obtain ⟨hlat, hrk, -⟩ := place_lattice_structure K V ι b X hX B hBfg
  have hinj : Function.Injective ρ := PlaceLattice.realize_injective b X hX
  have hnf := sizeMu_finrank_eq K
  have hf : (0 : ℝ) < (nPl K : ℝ) := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this
  have hj : (0 : ℝ) < (rkK B : ℝ) := by
    have : Module.Finite K V := Module.Finite.of_basis b
    have h : Submodule.span K (B : Set V) ≠ ⊥ := by
      intro h
      apply hB0
      rw [Submodule.span_eq_bot] at h
      exact (Submodule.eq_bot_iff _).2 (fun x hx => h x hx)
    have : 0 < rkK (K := K) B :=
      Nat.lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.2 h)
    exact_mod_cast this
  have hdisc : DiscreteTopology (zl ρ B) := hlat.2

  have hne : ∀ N : Submodule (𝓞 K) V, N ≠ ⊥ → zl ρ N ≠ ⊥ := by
    intro N hN h
    apply hN
    refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    have hm : ρ x ∈ zl ρ N := ⟨x, hx, rfl⟩
    rw [h, Submodule.mem_bot] at hm
    exact hinj (by rw [hm, map_zero])
  have hmono : ∀ N : Submodule (𝓞 K) V, N ≤ B → zl ρ N ≤ zl ρ B := by
    rintro N hN y ⟨x, hx, rfl⟩
    exact ⟨x, hN hx, rfl⟩

  set r : ℝ := Real.sqrt (nPl K : ℝ) * Real.exp (-La) with hr
  have hr0 : 0 < r := mul_pos (Real.sqrt_pos.2 hf) (Real.exp_pos _)
  have hmin : ∀ y ∈ zl ρ B, y ≠ 0 → r ≤ ‖y‖ := by
    rintro y ⟨x, hx, rfl⟩ hy
    have hx0 : x ≠ 0 := fun h => hy (by rw [h]; exact map_zero ρ)
    have h1 := hshort x hx hx0
    have h2 := mink_am_gm (fun v => Formalism.HermitianLatticesTheory.normAt b X v x)
      (fun v => mink_normAt_pos b X hX v x hx0)
    have h3 : ‖ρ x‖ ^ 2 = ∑ v, Formalism.HermitianLatticesTheory.normAt b X v x ^ 2 := mink_norm_sq_realize b X x
    have h4 : r ^ 2 ≤ ‖ρ x‖ ^ 2 := by
      rw [h3, hr, mul_pow, Real.sq_sqrt hf.le]
      refine le_trans (mul_le_mul_of_nonneg_left ?_ hf.le) h2
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.2
      have : (1 / (nPl K : ℝ)) * ∑ v, Real.log (Formalism.HermitianLatticesTheory.normAt b X v x) =
          (1 / (Fintype.card (InfinitePlace K) : ℝ)) * ∑ v, Real.log (Formalism.HermitianLatticesTheory.normAt b X v x) := rfl
      push_cast
      linarith
    exact (pow_le_pow_iff_left₀ hr0.le (norm_nonneg _) (by norm_num)).1 h4
  have hM := Formalism.F.muMaxLeMin _ (zl ρ B) hdisc (hne B hB0) r hr0 hmin

  have hle : muMax ρ B ≤ Formalism.F.muMax (zl ρ B) := by
    refine csSup_le ⟨_, B, le_rfl, hB0, rfl⟩ ?_
    rintro t ⟨N, hN, hN0, rfl⟩
    exact Formalism.F.slopeLeMuMax _ (zl ρ B) (zl ρ N) hdisc (hmono N hN) (hne N hN0)
  have hrkR : (Formalism.F.rk (zl ρ B) : ℝ) = 2 * (nPl K : ℝ) * (rkK B : ℝ) := by
    have : Formalism.F.rk (zl ρ B) = 2 * nPl K * rkK B := by rw [← hnf]; exact hrk
    rw [this]; push_cast; ring
  have hlogr : Real.log r = Real.log (nPl K : ℝ) / 2 - La := by
    rw [hr, Real.log_mul (Real.sqrt_pos.2 hf).ne' (Real.exp_pos _).ne', Real.log_sqrt hf.le,
      Real.log_exp]
    ring
  have hlogrk : Real.log (Formalism.F.rk (zl ρ B) : ℝ) =
      Real.log 2 + Real.log (nPl K : ℝ) + Real.log (rkK B : ℝ) := by
    rw [hrkR, Real.log_mul (by positivity) hj.ne', Real.log_mul (by norm_num) hf.ne']
  rw [hlogr, hlogrk] at hM
  unfold muMaxDef
  linarith

end Formalism.ExtensionFiltration
end
end

section -- merged from Formalism.MeanHeightDescent.AverageDegreeBounds.DescentSlope
open Module NumberField

noncomputable section

namespace Formalism.ExtensionFiltration

open Formalism.HN

theorem slope_image_injective
    {K V ι W κ : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ)
    (hX : ∀ v, IsUnit (X v).det) (hX' : ∀ v, IsUnit (X' v).det)
    (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) (hAfg : A.FG) (hA0 : A ≠ ⊥)
    (hinj : Function.Injective φ) :
    rkK (A.map (φ.restrictScalars (𝓞 K))) = rkK A ∧
      2 * slope (Formalism.HermitianLatticesTheory.realize b X) A - htMap b X b' X' φ ≤
        2 * slope (Formalism.HermitianLatticesTheory.realize b' X') (A.map (φ.restrictScalars (𝓞 K))) := by
  have : FiniteDimensional K V := Module.Finite.of_basis b
  have hrkeq := sizeIneq_rk φ A
  obtain ⟨hsat, hht⟩ := height_image_formula K V ι W κ b X b' X' hX hX' φ A hAfg
  have hker : A ⊓ (LinearMap.ker φ).restrictScalars (𝓞 K) = ⊥ := by
    rw [LinearMap.ker_eq_bot.2 hinj, Submodule.restrictScalars_bot, inf_bot_eq]
  rw [hker] at hrkeq hsat hht
  have hrkbot : rkK (K := K) (⊥ : Submodule (𝓞 K) V) = 0 := by
    unfold rkK
    simp
  rw [hrkbot, add_zero] at hrkeq
  refine ⟨hrkeq, ?_⟩
  set I := A.map (φ.restrictScalars (𝓞 K)) with hIdef
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  set ρ' := Formalism.HermitianLatticesTheory.realize b' X' with hρ'
  have hIfg : I.FG := hAfg.map _
  have hI0 : I ≠ ⊥ := by
    intro h
    apply hA0
    rw [eq_bot_iff]
    intro x hx
    have hm : φ x ∈ I := ⟨x, hx, rfl⟩
    rw [h] at hm
    have h0 : φ x = 0 := (Submodule.mem_bot _).1 hm
    exact (Submodule.mem_bot _).2 (hinj (by rw [h0, map_zero]))
  obtain ⟨hAlat, -, -⟩ := place_lattice_structure K V ι b X hX A hAfg
  obtain ⟨-, -, hhtI⟩ := place_lattice_structure K W κ b' X' hX' I hIfg
  obtain ⟨-, -, hsQ, -, -, -⟩ := size_maximal_slope K V ι b X hX A hAfg hA0
  have hSI := (size_maximal_slope K W κ b' X' hX' I hIfg hI0).1
  have hSBA := saturation_basic_properties (𝓞 K) V _ ρ A hAlat
  have hq := hSBA.2.2.2.2.2.2.2 ⊥ hsat
  have hrb : rk ρ (⊥ : Submodule (𝓞 K) V) = 0 := (hSBA.2.2.2.1 ⊥ bot_le).2 rfl
  have hdb : deg ρ (⊥ : Submodule (𝓞 K) V) = 0 := hSBA.2.2.2.2.1
  have hslQ : Formalism.F.slope (Formalism.F.quot (zl ρ A) (zl ρ (⊥ : Submodule (𝓞 K) V))) = slope ρ A := by
    unfold Formalism.F.slope
    rw [hq.1, hq.2.2, hrb, hdb, Nat.sub_zero, sub_zero]
    rfl
  have hsQ' := hsQ ⊥ hsat (Ne.symm hA0)
  rw [hslQ] at hsQ'
  set P := ∏ v, opNormAt b X b' X' v φ with hPdef
  have hP : 0 ≤ P := Finset.prod_nonneg (fun v _ => norm_nonneg _)
  have hf : (0 : ℝ) < nPl K := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this
  have hs : (0 : ℝ) < rkK I := by
    rw [hrkeq]
    have h : Submodule.span K (A : Set V) ≠ ⊥ := by
      intro h
      apply hA0
      rw [Submodule.span_eq_bot] at h
      exact (Submodule.eq_bot_iff _).2 (fun x hx => h x hx)
    have : 0 < rkK (K := K) A :=
      Nat.lt_of_lt_of_le Nat.zero_lt_one (Submodule.one_le_finrank_iff.2 h)
    exact_mod_cast this
  have hrkR : ((rkK A : ℝ) - rkK (K := K) (⊥ : Submodule (𝓞 K) V)) = rkK I := by
    rw [hrkbot, hrkeq]; simp
  rw [Finset.prod_pow, ← hPdef] at hht
  have hX0 : 0 ≤ P ^ (2 * rkK I) := pow_nonneg hP _
  have hQpos : 0 < htQ b X A ⊥ := pos_of_mul_pos_right (lt_of_lt_of_le hhtI hht) hX0
  have hPpos : 0 < P := by
    rcases hP.lt_or_eq with h | h
    · exact h
    · exfalso
      have hne : 2 * rkK I ≠ 0 := by
        have : 0 < rkK I := by exact_mod_cast hs
        omega
      rw [← h, zero_pow hne, zero_mul] at hht
      exact absurd hhtI (not_lt.2 hht)
  have he : (0 : ℝ) ≤ 1 / (2 * (nPl K : ℝ) * (rkK I : ℝ)) := by positivity
  have hcore : size b' X' I ≤ P ^ ((1 : ℝ) / (nPl K : ℝ)) * sizeQ b X A ⊥ := by
    unfold size sizeQ
    rw [hrkR]
    calc ht b' X' I ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ)))
        ≤ (P ^ (2 * rkK I) * htQ b X A ⊥) ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) :=
          Real.rpow_le_rpow hhtI.le hht he
      _ = (P ^ (2 * rkK I)) ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) *
            htQ b X A ⊥ ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) :=
          Real.mul_rpow hX0 hQpos.le
      _ = P ^ ((1 : ℝ) / (nPl K : ℝ)) *
            htQ b X A ⊥ ^ ((1 : ℝ) / (2 * (nPl K : ℝ) * (rkK I : ℝ))) := by
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul hP]
          congr 1
          push_cast
          field_simp
  rw [hSI, hsQ', Real.rpow_def_of_pos hPpos, ← Real.exp_add, Real.exp_le_exp] at hcore
  have hht2 : htMap b X b' X' φ = 2 * (Real.log P * (1 / (nPl K : ℝ))) := by
    unfold htMap
    have hne : ∀ v ∈ (Finset.univ : Finset (InfinitePlace K)), opNormAt b X b' X' v φ ≠ 0 := by
      intro v hv h0
      exact hPpos.ne' (Finset.prod_eq_zero hv h0)
    rw [hPdef, Real.log_prod hne]
    simp only [Real.log_pow]
    rw [← Finset.mul_sum]
    push_cast
    ring
  rw [hht2]
  linarith

theorem descent_slope : DescentSlope := by
  intro K V ι W κ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ b X b' X' hX hX' φ A B hAfg hBfg hA0 hinj hIB
  obtain ⟨hrkeq, hsl⟩ := slope_image_injective b X b' X' hX hX' φ A hAfg hA0 hinj
  set I := A.map (φ.restrictScalars (𝓞 K)) with hIdef
  set ρ := Formalism.HermitianLatticesTheory.realize b X with hρ
  set ρ' := Formalism.HermitianLatticesTheory.realize b' X' with hρ'
  have hIfg : I.FG := hAfg.map _
  have hI0 : I ≠ ⊥ := by
    intro h
    apply hA0
    rw [eq_bot_iff]
    intro x hx
    have hm : φ x ∈ I := ⟨x, hx, rfl⟩
    rw [h] at hm
    have h0 : φ x = 0 := (Submodule.mem_bot _).1 hm
    exact (Submodule.mem_bot _).2 (hinj (by rw [h0, map_zero]))
  have hB0 : B ≠ ⊥ := fun h => hI0 (le_bot_iff.mp (h ▸ hIB))
  obtain ⟨hBlat, hrkB, -⟩ := place_lattice_structure K W κ b' X' hX' B hBfg
  obtain ⟨-, hrkI, -⟩ := place_lattice_structure K W κ b' X' hX' I hIfg
  have hSBB := saturation_basic_properties (𝓞 K) W _ ρ' B hBlat
  have hMB := slope_characterization (𝓞 K) W _ ρ' B hBlat hB0
  have hmin := (hMB.2.1 (muMin ρ' B)).1 le_rfl I hIB
  have hrkIpos : 0 < rk ρ' I := by
    rcases Nat.eq_zero_or_pos (rk ρ' I) with h | h
    · exact absurd ((hSBB.2.2.2.1 I hIB).1 h) hI0
    · exact h
  have hrkBpos : 0 < rk ρ' B := by
    rcases Nat.eq_zero_or_pos (rk ρ' B) with h | h
    · exact absurd ((hSBB.2.2.2.1 B le_rfl).1 h) hB0
    · exact h
  have hdI : deg ρ' I = slope ρ' I * (rk ρ' I : ℝ) := by
    have : (rk ρ' I : ℝ) ≠ 0 := by exact_mod_cast hrkIpos.ne'
    show deg ρ' I = deg ρ' I / (rk ρ' I : ℝ) * (rk ρ' I : ℝ)
    field_simp
  have hdB : deg ρ' B = slope ρ' B * (rk ρ' B : ℝ) := by
    have : (rk ρ' B : ℝ) ≠ 0 := by exact_mod_cast hrkBpos.ne'
    show deg ρ' B = deg ρ' B / (rk ρ' B : ℝ) * (rk ρ' B : ℝ)
    field_simp
  have hn : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by
    exact_mod_cast (Module.finrank_pos : 0 < Module.finrank ℚ K)
  rw [hdI, hdB, hrkB, hrkI, hrkeq] at hmin
  push_cast at hmin
  have hmin' : muMin ρ' B * ((rkK B : ℝ) - rkK A) ≤
      slope ρ' B * (rkK B : ℝ) - slope ρ' I * (rkK A : ℝ) := by
    refine le_of_mul_le_mul_left ?_ hn
    linarith
  have hra : (0 : ℝ) ≤ (rkK A : ℝ) := Nat.cast_nonneg _
  have h2 := mul_le_mul_of_nonneg_left hsl hra
  unfold muDef muMinDef
  simp only [← hρ, ← hρ']
  nlinarith [h2, hmin']

end Formalism.ExtensionFiltration
end
end
