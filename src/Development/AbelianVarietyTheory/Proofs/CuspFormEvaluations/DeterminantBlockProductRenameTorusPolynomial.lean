module

public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
public import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsIdempotentElemRangeSpMapSubset
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRankOneCuspLatticeDataOfPrincipal

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DeterminantBlockProductRenameTorusPolynomial
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DeterminantBlockProductRenameTorusPolynomial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BlockRen

section Deriv

open scoped ContDiff

variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]

theorem polyDeriv_eq_sum {θ : W → ℂ} {x : W} (hθ : ContDiffAt ℂ ω θ x) {T : Type}
    (P : MvPolynomial T ℂ) (u : T → W) :
    I2.polyDeriv P u θ x =
      ∑ m ∈ P.support, P.coeff m * mD θ x ((Finsupp.toMultiset m).map u) := by
  unfold I2.polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1

  have hs : (Finsupp.toMultiset m).map u = (((Finsupp.toMultiset m).toList.map u : List W) : Multiset W) := by
    rw [← Multiset.map_coe, Multiset.coe_toList]
  have hlen : ((Finsupp.toMultiset m).toList.map u).length = Multiset.card (Finsupp.toMultiset m) := by
    rw [List.length_map, Multiset.length_toList]
  rw [hs, mD_coe hθ, lD_eq θ x _ hlen]
  congr 1
  funext k
  simp [List.get_eq_getElem]

theorem polyDeriv_rename {θ : W → ℂ} {x : W} (hθ : ContDiffAt ℂ ω θ x) {T κ : Type} (ρ : T → κ)
    (hρ : Function.Injective ρ) (P : MvPolynomial T ℂ) (v : κ → W) :
    I2.polyDeriv (MvPolynomial.rename ρ P) v θ x = I2.polyDeriv P (v ∘ ρ) θ x := by
  classical
  rw [polyDeriv_eq_sum hθ, polyDeriv_eq_sum hθ, MvPolynomial.support_rename_of_injective hρ,
    Finset.sum_image fun a _ b _ h => Finsupp.mapDomain_injective hρ h]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain ρ hρ, ← Finsupp.toMultiset_map, Multiset.map_map]

theorem contDiffAt_of_diff [FiniteDimensional ℂ W]
    {F : W → ℂ} (hF : Differentiable ℂ F) (x : W) : ContDiffAt ℂ ω F x := by

  let e : W ≃L[ℂ] (Fin (Module.finrank ℂ W) → ℂ) :=
    (Module.finBasis ℂ W).equivFun.toContinuousLinearEquiv
  have hG : AnalyticOnNhd ℂ (F ∘ e.symm) Set.univ :=
    ReciprocityTheory.AnForm.Osgood.osgood _ Set.univ _ isOpen_univ
      (hF.comp e.symm.differentiable).differentiableOn
  have hA := (hG (e x) (Set.mem_univ _)).comp
    ((e : W →L[ℂ] (Fin (Module.finrank ℂ W) → ℂ)).analyticAt x)
  have hFe : (F ∘ e.symm) ∘ e = F := by
    funext y
    simp
  rw [hFe] at hA
  exact hA.contDiffAt

end Deriv

theorem polyDeriv_scale {J W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {P : MvPolynomial J ℂ} {d : ℕ}
    (hP : P.IsHomogeneous d) (c : ℂ) (u : J → W) (F : W → ℂ) (x : W) :
    I2.polyDeriv P (fun l => c • u l) F x = c ^ d * I2.polyDeriv P u F x := by
  unfold I2.polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_

  have hd : Multiset.card (Finsupp.toMultiset m) = d := by
    have h := hP (MvPolynomial.mem_support_iff.mp hm)
    simp [Finsupp.weight_apply] at h
    rw [Finsupp.card_toMultiset]
    exact h
  rw [ContinuousMultilinearMap.map_smul_univ (c := fun _ => c)]
  have hc : (∏ _k : Fin (Multiset.card (Finsupp.toMultiset m)), c) = c ^ d := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, hd]
  rw [hc, smul_eq_mul]
  ring

theorem det_X_isHomogeneous {J K : Type} [CommRing K] (i : ℕ) (f : Fin i → Fin i → J) :
    (Matrix.of fun a b : Fin i => (MvPolynomial.X (f a b) : MvPolynomial J K)).det.IsHomogeneous i := by
  rw [Matrix.det_apply]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun s _ => ?_

  have hprod : (∏ a, (Matrix.of fun a b : Fin i => (MvPolynomial.X (f a b) : MvPolynomial J K)) (s a) a).IsHomogeneous i := by
    have h := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin i))
      (fun a => (MvPolynomial.X (f (s a) a) : MvPolynomial J K)) (fun _ => 1)
      (fun a _ => MvPolynomial.isHomogeneous_X K _)
    simpa using h
  rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
  · rw [h, one_smul]
    exact hprod
  · rw [h, Units.neg_smul, one_smul]
    exact hprod.neg

theorem blockProd_rename : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (K : Type) [Field K] (σ : K →+* ℂ) (P : MvPolynomial (LtN Dw n) K), IsBlockProd P → ∀ (dim : (E →+* ℂ) → ℕ) (rl : (E →+* ℂ) → (E →+* ℂ)) (hd : ∀ τ, Dw.mult τ ≤ dim (rl τ)), Function.Injective rl → P ≠ 0 ∧ P.IsHomogeneous P.totalDegree ∧ ∃ (nb : ℕ) (bs : Fin nb → I2.Block E n dim), I2.Disj bs ∧ I2.DF bs = P.totalDegree ∧ ∀ (t : ℂ) (F : (Fin n → I2.Vsp dim) → ℂ), Differentiable ℂ F → I2.polyDeriv (MvPolynomial.map σ P) (fun ℓ => t • I2.dir ((ℓ.2.2, ⟨rl ℓ.1, Fin.castLE (hd ℓ.1) ℓ.2.1⟩) : I2.Letter n dim)) F 0 = t ^ P.totalDegree * I2.polyDeriv (I2.P1 bs) I2.dir F 0 := by
  intro E _ _ _ H Dw n K _ σ P hP dim rl hd hrl
  obtain ⟨nb, bs0, hdisj, rfl⟩ := hP
  classical

  have hdeg : (∏ j, (bs0 j).poly K).IsHomogeneous (∑ j, (bs0 j).i * (bs0 j).c) := by
    refine MvPolynomial.IsHomogeneous.prod _ _ _ fun j _ => ?_
    exact (det_X_isHomogeneous (K := K) (bs0 j).i
      (fun a b => (⟨(bs0 j).τ, Fin.castLE (bs0 j).hi a, (bs0 j).col b⟩ : LtN Dw n))).pow (bs0 j).c
  have hne : (∏ j, (bs0 j).poly K) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun j _ => GlobalTheory.BlockThInhab.poly_ne_zero Dw n K (bs0 j)
  have htot : (∏ j, (bs0 j).poly K).totalDegree = ∑ j, (bs0 j).i * (bs0 j).c :=
    hdeg.totalDegree hne

  let bs : Fin nb → I2.Block E n dim := fun j =>
    ⟨rl (bs0 j).τ, (bs0 j).i, (bs0 j).hi.trans (hd _), (bs0 j).c, (bs0 j).hc, (bs0 j).col, (bs0 j).col_inj⟩
  refine ⟨hne, htot ▸ hdeg, nb, bs, ?_, ?_, ?_⟩
  · intro j j' hjj' a a'
    exact hdisj j j' hjj' a a'
  · rw [htot]
    rfl
  · intro t F hF
    rw [htot]
    let ρ : LtN Dw n → I2.Letter n dim := fun ℓ => (ℓ.2.2, ⟨rl ℓ.1, Fin.castLE (hd ℓ.1) ℓ.2.1⟩)
    have hρ : Function.Injective ρ := by
      rintro ⟨τ, a, b⟩ ⟨τ', a', b'⟩ h
      simp only [ρ, Prod.mk.injEq, Sigma.mk.injEq] at h
      obtain ⟨rfl, h1, h2⟩ := h
      obtain rfl := hrl h1
      have h3 := Fin.castLE_injective (hd τ) (eq_of_heq h2)
      subst h3
      rfl

    have hP1 : MvPolynomial.rename ρ (MvPolynomial.map σ (∏ j, (bs0 j).poly K)) = I2.P1 bs := by
      simp only [map_prod, I2.P1]
      refine Finset.prod_congr rfl fun j _ => ?_
      simp only [Bk.poly, I2.Block.poly, map_pow, RingHom.map_det, AlgHom.map_det]
      congr 2
      ext a b
      simp [ρ, bs]
    have hhom : (I2.P1 bs).IsHomogeneous (∑ j, (bs0 j).i * (bs0 j).c) := by
      refine MvPolynomial.IsHomogeneous.prod _ _ _ fun j _ => ?_
      exact (det_X_isHomogeneous (K := ℂ) (bs0 j).i
        (fun a b => (((bs0 j).col b, ⟨rl (bs0 j).τ, Fin.castLE ((bs0 j).hi.trans (hd _)) a⟩) : I2.Letter n dim))).pow (bs0 j).c
    refine (polyDeriv_rename (contDiffAt_of_diff hF 0) ρ hρ _ (fun l => t • I2.dir l)).symm.trans ?_
    rw [hP1]
    exact polyDeriv_scale hhom t I2.dir F 0

end GlobalTheory.BlockRen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.DeterminantBlockProductRenameTorusPolynomialStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinantBlockProduct_rename_torusPolynomial : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ) (K : Type) [Field K] (σ : K →+* ℂ) (P : MvPolynomial (LtN Dw n) K), IsBlockProd P → ∀ (dim : (E →+* ℂ) → ℕ) (rl : (E →+* ℂ) → (E →+* ℂ)) (hd : ∀ τ, Dw.mult τ ≤ dim (rl τ)), Function.Injective rl → P ≠ 0 ∧ P.IsHomogeneous P.totalDegree ∧ ∃ (nb : ℕ) (bs : Fin nb → I2.Block E n dim), I2.Disj bs ∧ I2.DF bs = P.totalDegree ∧ ∀ (t : ℂ) (F : (Fin n → I2.Vsp dim) → ℂ), Differentiable ℂ F → I2.polyDeriv (MvPolynomial.map σ P) (fun ℓ => t • I2.dir ((ℓ.2.2, ⟨rl ℓ.1, Fin.castLE (hd ℓ.1) ℓ.2.1⟩) : I2.Letter n dim)) F 0 = t ^ P.totalDegree * I2.polyDeriv (I2.P1 bs) I2.dir F 0 := by
  first | exact @GlobalTheory.BlockRen.blockProd_rename | exact GlobalTheory.BlockRen.blockProd_rename | (intros; apply GlobalTheory.BlockRen.blockProd_rename <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RealBounds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RunParametersOfLower

theorem real_bounds (f r m ρ w D q t : ℝ) (hf : 1 ≤ f) (hr : 1 ≤ r) (hm : 1 ≤ m) (hmf : m ≤ f)
    (hf2 : f ^ 2 ≤ ρ) (hρ : 16 ≤ ρ) (hw0 : 0 ≤ w) (hw : w ≤ f ^ 2) (hD : 1 ≤ D)
    (hq : (ρ ^ 7) ^ 4 * (90 * (f * r + D)) * D * r ≤ q)
    (ht : t = q * (q / (90 * (f * r + D) * (ρ ^ 7) ^ 4))) :
    (2 * f * m) ^ 2 * (2 * w * ρ) * (f * (90 * (f * r + D)) * (ρ ^ 7) ^ 3) < q ∧
    1 ≤ q / (90 * (f * r + D) * (ρ ^ 7) ^ 4) ∧
    90 * m ^ 2 * (2 * f * m) ^ 2 * ρ ≤ q / 2 ∧ D ≤ q ∧
    4 * D * (7 + Real.log (q * D)) + 2 * f * m + 1 ≤ t ∧
    f * r * Real.log 2 + 2 * (2 * f * m) + 3 + (D + 1) * (r * Real.log r + 3 * r + 3) ≤ t := by
  have hρ1 : (1 : ℝ) ≤ ρ := by linarith
  have hρ0 : (0 : ℝ) < ρ := by linarith
  have hN : r ≤ f * r := by nlinarith
  have hN1 : 1 ≤ f * r := by linarith
  have hfρ : f ≤ ρ := by nlinarith
  have hfm : f * m ≤ ρ := by nlinarith
  have hm2 : m ^ 2 ≤ ρ := by nlinarith
  have hd0 : 0 ≤ 2 * f * m := by positivity
  have hd : 2 * f * m ≤ 2 * ρ := by linarith
  have hwρ : w ≤ ρ := hw.trans hf2
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have hlogr : Real.log r ≤ r := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < r by linarith); linarith
  have h3' : f * r * Real.log 2 ≤ f * r * 1 := by gcongr
  obtain ⟨N, hNdef⟩ : ∃ N, N = f * r := ⟨_, rfl⟩
  rw [← hNdef] at hq ht hN hN1 h3' ⊢
  obtain ⟨S, hS⟩ : ∃ S, S = 90 * (N + D) := ⟨_, rfl⟩
  rw [← hS] at hq ht ⊢
  have hS180 : 180 ≤ S := by linarith
  have hS0 : 0 < S := by linarith
  have hB : 0 < S * (ρ ^ 7) ^ 4 := by positivity
  have hDr : 1 ≤ D * r := one_le_mul_of_one_le_of_one_le hD hr
  have hDDr : D ≤ D * r := by nlinarith
  have hrDr : r ≤ D * r := by nlinarith
  have hq' : D * r * (S * (ρ ^ 7) ^ 4) ≤ q := by linarith
  have hBq : S * (ρ ^ 7) ^ 4 ≤ q := by
    have := mul_le_mul_of_nonneg_right hDr hB.le
    linarith
  have hq0 : 0 < q := by linarith
  have hb : D * r ≤ q / (S * (ρ ^ 7) ^ 4) := by rw [le_div_iff₀ hB]; exact hq'
  have htq : q * (D * r) ≤ t := by rw [ht]; gcongr
  have hT : ρ ^ 5 ≤ (ρ ^ 7) ^ 4 := by
    rw [← pow_mul]; exact pow_le_pow_right₀ hρ1 (by norm_num)
  have hT4 : 16 * ρ ^ 4 ≤ ρ ^ 5 := by
    rw [pow_succ' ρ 4]; gcongr
  have hT1 : ρ ≤ ρ ^ 4 := le_self_pow₀ hρ1 (by norm_num)
  have hqT : 180 * (ρ ^ 7) ^ 4 ≤ q := by
    have : 180 * (ρ ^ 7) ^ 4 ≤ S * (ρ ^ 7) ^ 4 := by gcongr
    linarith
  have hSρ : S * ρ ≤ q := by
    have : S * ρ ≤ S * (ρ ^ 7) ^ 4 := by
      have : ρ ≤ (ρ ^ 7) ^ 4 := by linarith
      gcongr
    linarith
  have hS16 : S * 16 ≤ S * ρ := by gcongr
  have hDq : D ≤ q := by linarith
  refine ⟨?_, by linarith, ?_, hDq, ?_, ?_⟩
  · have h1 : (2 * f * m) ^ 2 * (2 * w * ρ) * (f * S * (ρ ^ 7) ^ 3) ≤
        (2 * ρ) ^ 2 * (2 * ρ * ρ) * (ρ * S * (ρ ^ 7) ^ 3) := by
      gcongr
    have h2 : (2 * ρ) ^ 2 * (2 * ρ * ρ) * (ρ * S * (ρ ^ 7) ^ 3) = 8 * (S * ρ ^ 26) := by ring
    have h3 : S * (ρ ^ 7) ^ 4 = ρ ^ 2 * (S * ρ ^ 26) := by ring
    have h4 : 0 < S * ρ ^ 26 := by positivity
    have h5 : 8 * (S * ρ ^ 26) < ρ ^ 2 * (S * ρ ^ 26) :=
      mul_lt_mul_of_pos_right (by nlinarith) h4
    linarith
  · have h1 : 90 * m ^ 2 * (2 * f * m) ^ 2 * ρ ≤ 90 * ρ * (2 * ρ) ^ 2 * ρ := by gcongr
    have h2 : 90 * ρ * (2 * ρ) ^ 2 * ρ = 360 * ρ ^ 4 := by ring
    linarith
  · have h1 : Real.log q = Real.log (q / 16) + Real.log 16 := by
      rw [Real.log_div hq0.ne' (by norm_num)]; ring
    have h2 : Real.log (q / 16) ≤ q / 16 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    have h3 : Real.log 16 ≤ 16 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h4 : Real.log D ≤ Real.log q := Real.log_le_log (by linarith) hDq
    have h5 : Real.log (q * D) = Real.log q + Real.log D := Real.log_mul hq0.ne' (by linarith)
    have h6 : 4 * D * (7 + Real.log (q * D)) ≤ 4 * D * (q / 8 + 37) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
    have h7 : (2 * ρ + 1) * 1 ≤ (2 * ρ + 1) * D := by gcongr
    have h8 : (q / 2 + 148 + (2 * ρ + 1)) * D ≤ q * D := by
      apply mul_le_mul_of_nonneg_right _ (by linarith); linarith
    have h9 : q * D ≤ q * (D * r) := by gcongr
    linarith
  · have h2' : 0 ≤ Real.log r := Real.log_nonneg hr
    have h4 : r * Real.log r + 3 * r + 3 ≤ r * (N + 6) := by
      have : r * Real.log r ≤ r * N := by
        apply mul_le_mul_of_nonneg_left _ (by linarith); linarith
      linarith
    have h5 : (D + 1) * (r * Real.log r + 3 * r + 3) ≤ (2 * D) * (r * (N + 6)) := by
      apply mul_le_mul (by linarith) h4 (by positivity) (by positivity)
    have h6 : (N + 4 * ρ + 3) * 1 ≤ (N + 4 * ρ + 3) * (D * r) := by gcongr
    have h7 : (N + 4 * ρ + 3 + 2 * (N + 6)) * (D * r) ≤ q * (D * r) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith); linarith
    linarith

theorem runOK_of_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r DF q m : ℕ), 1 ≤ DF → 2 ≤ I2.PT.f E * r → 1 ≤ m → m ^ 4 ≤ I2.PT.f E → (I2.PT.f E : ℝ) ^ 2 ≤ I2.PT.rd E → 16 ≤ I2.PT.rd E → I2.RR (E := E) ^ 4 * (90 * (I2.PT.f E * r + DF)) * DF * r ≤ q → RunOK E r DF q (Real.sqrt (90 * (I2.PT.f E * r + DF))) m := by
  intro E _ _ _ r DF q m hDF hfr hm1 hmf hf2 hrd hlo
  have hf : 1 ≤ I2.PT.f E := by
    rcases Nat.eq_zero_or_pos (I2.PT.f E) with h | h
    · rw [h] at hfr; omega
    · exact h
  have hr : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h] at hfr; omega
    · exact h
  have hmf' : m ≤ I2.PT.f E := (Nat.le_self_pow (by norm_num) m).trans hmf
  have hfR : (1 : ℝ) ≤ I2.PT.f E := by exact_mod_cast hf
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hDR : (1 : ℝ) ≤ DF := by exact_mod_cast hDF
  have hmfR : (m : ℝ) ≤ I2.PT.f E := by exact_mod_cast hmf'
  have hfrR : (2 : ℝ) ≤ I2.PT.f E * r := by exact_mod_cast hfr
  have hfrd : (I2.PT.f E : ℝ) ≤ I2.PT.rd E := by nlinarith
  have hw : (I2.PT.f E : ℝ) ^ ((3 : ℝ) / 2) ≤ (I2.PT.f E : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hfR (by norm_num)
  have hS0 : (0 : ℝ) < 90 * (I2.PT.f E * r + DF) := by positivity
  have hsq : Real.sqrt (90 * (I2.PT.f E * r + DF)) ^ 2 = 90 * (I2.PT.f E * r + DF) := Real.sq_sqrt hS0.le
  obtain ⟨c1, c2, c3, c4, c5, c6⟩ := real_bounds (I2.PT.f E) r m (I2.PT.rd E) _ DF q
    (I2.t0 (E := E) q (Real.sqrt (90 * (I2.PT.f E * r + DF)))) hfR hrR hmR hmfR hf2 hrd
    (by positivity) hw hDR hlo (by unfold I2.t0 I2.b0 I2.RR; rw [hsq])
  have hc4 : DF ≤ q := by exact_mod_cast c4
  have hq1 : 1 ≤ q := hDF.trans hc4
  have hq0 : (0 : ℝ) < q := by linarith
  have hρ0 : 0 < I2.PT.rd E := by linarith
  have hd : (I2.dstar (E := E) m : ℝ) = 2 * I2.PT.f E * m := by unfold I2.dstar; push_cast; ring
  intro X hX hdim
  subst hX
  refine ⟨⟨q, _, m, hq1, hDF, hfr, hdim, hm1, hmf, hfrd, hf2, hrd, ?_, ?_, ?_, ?_,
    hc4, ?_, ?_⟩, rfl, rfl, rfl⟩
  · rw [hsq]
    unfold I2.PT.gA
    push_cast
    constructor <;> linarith
  · unfold I2.th I2.omStar I2.RR
    rw [Real.sq_sqrt (by positivity), ← mul_div_assoc, div_lt_one hq0, hsq, hd]
    exact c1
  · unfold I2.b0 I2.RR; rw [hsq]; exact c2
  · unfold I2.M1
    rw [hd]; exact c3
  · rw [hd]; linarith
  · unfold I2.PT.gA
    rw [hd]
    push_cast
    linarith

end GlobalTheory.RunParametersOfLower
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsotropicEnumerationSurjectiveLocalRing
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsotropicEnumerationSurjectiveLocalRing
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace IsotropicEnum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

theorem comp_list_prod {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] (h : T' ⟶ T) (L : List (T ⟶ G)) :
    h ≫ L.prod = (L.map fun x => h ≫ x).prod := by
  induction L with
  | nil => simp [MonObj.comp_one]
  | cons x L ih => simp [MonObj.comp_mul, ih]

theorem inZh_comp (Xo : Moduli Dw l) {n : ℕ} (Λ : GenLat E n) (N : ℕ) {T T' : Over Xo.X} (h : T' ⟶ T)
    {a : Fin n → (T ⟶ Xo.univ.t.G)} (ha : InZh Xo Λ N a) : InZh Xo Λ N (fun b => h ≫ a b) := by
  refine ⟨fun b => ?_, fun mu hmu cm hcm i => ?_⟩
  · rw [← MonObj.comp_pow, ha.1 b, MonObj.comp_one]
  · have h1 := ha.2 mu hmu cm hcm i
    have hl : (List.ofFn fun j => (h ≫ a j) ≫ Xo.univ.t.act.act (cm i j)) =
        (List.ofFn fun j => a j ≫ Xo.univ.t.act.act (cm i j)).map fun y => h ≫ y := by
      simp [List.map_ofFn, Function.comp_def, Category.assoc]
    rw [hl, ← comp_list_prod, h1, MonObj.comp_one]

theorem ev_sum {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
    (I : TateIso Dw k Q act e) {m : ℕ} (hm : 0 < m) {n : ℕ} (v : Fin n → Dw.La) :
    I.ev m (∑ j, v j) = (List.ofFn fun j => I.ev m (v j)).prod := by

  have h0 : I.ev m 0 = 1 := by
    have h := I.add m 0 0
    rw [add_zero] at h
    exact mul_left_cancel (h.symm.trans (_root_.mul_one _).symm)
  induction n with
  | zero => simp [h0]
  | succ n ih => rw [Fin.sum_univ_succ, I.add, ih (fun j => v j.succ), List.ofFn_succ, List.prod_cons]

theorem exists_eq_of_isAlgClosed (Xo : Moduli Dw l) {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ Xo.X)
    {n : ℕ} (Λ : GenLat E n) {N : ℕ} (hΛ : Λ.Unimod) (hN : 0 < N)
    (hle : Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La)
    (w : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (hw : ∀ i, InZh Xo Λ N (w i))
    (hinj : Function.Injective w) (a : Fin n → (ptO Xo x ⟶ Xo.univ.t.G)) (ha : InZh Xo Λ N a) : ∃ i, w i = a := by
  classical
  obtain ⟨-, I, -⟩ := Xo.univ.geom K x (Spec.preimage (x ≫ Xo.s)).hom
    (by simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage])
  have hM : 0 < N ^ 2 := pow_pos hN 2

  have evEq : ∀ u u' : Dw.La, Dw.ModN (N ^ 2) (u - u') → I.ev (N ^ 2) u = I.ev (N ^ 2) u' := by
    intro u u' h
    have h1 : I.ev (N ^ 2) (u - u') = 1 := (I.ker _ hM _).2 h
    have h2 := I.add (N ^ 2) (u - u') u'
    rw [sub_add_cancel, h1, _root_.one_mul] at h2
    exact h2

  have key : ∀ c : Fin n → (ptO Xo x ⟶ Xo.univ.t.G), InZh Xo Λ N c →
      ∃ y : Fin n → Dw.La, (∀ (mu : Matrix (Fin n) (Fin n) E), (∀ v ∈ Λ.La, mu.mulVec v ∈ stdLat E n) →
        ∀ cm : Fin n → Fin n → 𝓞 E, (∀ i j, (cm i j : E) = (N : E) * mu i j) →
          ∀ i, Dw.ModN (N ^ 2) (∑ j, cm i j • y j)) ∧ ∀ b, I.ev (N ^ 2) (y b) = c b := by
    intro c hc
    have hy : ∀ b, ∃ y, I.ev (N ^ 2) y = c b := fun b => (I.onto _ hM (c b)).1 (hc.1 b)
    choose y hy using hy
    refine ⟨y, fun mu hmu cm hcm i => ?_, hy⟩
    have h1 := hc.2 mu hmu cm hcm i
    refine (I.ker _ hM _).1 ?_
    have hfun : (fun j => I.ev (N ^ 2) (cm i j • y j)) = fun j => c j ≫ Xo.univ.t.act.act (cm i j) := by
      funext j
      simp only [I.lin, hy]
    rw [ev_sum I hM, hfun]
    exact h1
  obtain ⟨zz, -, -, hcover⟩ := ZCount.exists_class_representatives E H Dw n Λ N hΛ hN hle
  have hf : ∀ i, ∃ j, w i = fun b => I.ev (N ^ 2) (zz j b) := by
    intro i
    obtain ⟨y, hy, hyw⟩ := key (w i) (hw i)
    obtain ⟨j, hj⟩ := hcover y hy
    refine ⟨j, funext fun b => ?_⟩
    rw [← hyw b]
    exact evEq _ _ (hj b)
  choose f hf using hf

  have finj : Function.Injective f := by
    intro i i' h
    apply hinj
    rw [hf i, hf i', h]
  have fsurj : Function.Surjective f := Finite.surjective_of_injective finj
  obtain ⟨y, hy, hya⟩ := key a ha
  obtain ⟨j, hj⟩ := hcover y hy
  obtain ⟨i, rfl⟩ := fsurj j
  refine ⟨i, ?_⟩
  rw [hf i]
  funext b
  rw [← hya b]
  exact (evEq _ _ (hj b)).symm

end IsotropicEnum


open IsotropicEnum in
theorem isotropic_enumeration_onto_of_isLocalRing :
    Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : Type) [CommRing T] [IsLocalRing T] (x0 : Sp T ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∀ z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo x0 z → (∀ a, InZh Xo Λ N a → ∃ i, z i = a) ∧ ∀ z' : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G), (∀ i, InZh Xo Λ N (z' i)) → GeoInj Xo x0 z' → ∃ σ : Equiv.Perm (Fin (Λ.zCard N (Dw.p + Dw.q))), ∀ i, z' i = z (σ i) := by
  intro hL E _ _ _ H Dw l Xo T _ _ x0 n Λ N hΛ hN hle z hz hzi
  classical

  let ψ : T →+* AlgebraicClosure (IsLocalRing.ResidueField T) :=
    (algebraMap (IsLocalRing.ResidueField T) (AlgebraicClosure (IsLocalRing.ResidueField T))).comp
      (IsLocalRing.residue T)
  let g : ptO Xo (spMap ψ ≫ x0) ⟶ ptO Xo x0 := Over.homMk (spMap ψ) rfl
  have hA : ∀ (zz : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G)),
      (∀ i, InZh Xo Λ N (zz i)) → GeoInj Xo x0 zz → ∀ a, InZh Xo Λ N a → ∃ i, zz i = a := by
    intro zz hzz hgi a ha
    obtain ⟨i, hi⟩ := exists_eq_of_isAlgClosed Xo (spMap ψ ≫ x0) Λ hΛ hN hle
      (fun i b => g ≫ zz i b) (fun i => inZh_comp Xo Λ N g (hzz i)) (hgi _ ψ g rfl)
      (fun b => g ≫ a b) (inZh_comp Xo Λ N g ha)
    refine ⟨i, funext fun b => ?_⟩
    have hib : g ≫ zz i b = g ≫ a b := congrFun hi b

    obtain ⟨e, he, hiff⟩ := exists_isIdempotentElem_torsion_eq hL E H Dw l Xo T x0 (N ^ 2) (pow_pos hN 2)
      (zz i b) (a b) ((hzz i).1 b) (ha.1 b)
    have hψ : ψ e = 1 := (hiff _ ψ).2 (congrArg (fun f => f.left) hib)
    have hmul : e * (1 - e) = 0 := by rw [mul_sub, _root_.mul_one, he.eq, sub_self]
    have he1 : e = 1 := by
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
      · exact (sub_eq_zero.1 ((hu.mul_right_eq_zero).1 hmul)).symm
      · rw [(hu.mul_left_eq_zero).1 hmul, map_zero] at hψ
        exact absurd hψ zero_ne_one
    have hid := (hiff T (RingHom.id T)).1 (by rw [he1, map_one])
    have hsp : spMap (RingHom.id T) = 𝟙 _ := by simp [spMap]
    rw [hsp, Category.id_comp, Category.id_comp] at hid
    exact Over.OverMorphism.ext hid
  refine ⟨hA z hz hzi, fun z' hz' hzi' => ?_⟩
  have hsel : ∀ i, ∃ j, z j = z' i := fun i => hA z hz hzi (z' i) (hz' i)
  choose σ' hσ' using hsel
  have hinj' : Function.Injective z' := by
    intro i i' h
    apply hzi' _ ψ g rfl
    show (fun b => g ≫ z' i b) = fun b => g ≫ z' i' b
    rw [h]
  have σinj : Function.Injective σ' := by
    intro i i' h
    apply hinj'
    rw [← hσ' i, ← hσ' i', h]
  exact ⟨Equiv.ofBijective σ' ⟨σinj, Finite.surjective_of_injective σinj⟩, fun i => (hσ' i).symm⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsotropicEnumerationSurjectiveLocalRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_enumeration_surjective_local_ring : Laws → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (T : Type) [CommRing T] [IsLocalRing T] (x0 : Sp T ⟶ Xo.X) (n : ℕ) (Λ : GenLat E n) (N : ℕ), Λ.Unimod → 0 < N → Ideal.span {(N : 𝓞 E)} • stdLat E n ≤ Λ.La → ∀ z : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G), (∀ i, InZh Xo Λ N (z i)) → GeoInj Xo x0 z → (∀ a, InZh Xo Λ N a → ∃ i, z i = a) ∧ ∀ z' : Fin (Λ.zCard N (Dw.p + Dw.q)) → Fin n → (ptO Xo x0 ⟶ Xo.univ.t.G), (∀ i, InZh Xo Λ N (z' i)) → GeoInj Xo x0 z' → ∃ σ : Equiv.Perm (Fin (Λ.zCard N (Dw.p + Dw.q))), ∀ i, z' i = z (σ i) := by
  first | exact @GlobalTheory.isotropic_enumeration_onto_of_isLocalRing | exact GlobalTheory.isotropic_enumeration_onto_of_isLocalRing | (intros; apply GlobalTheory.isotropic_enumeration_onto_of_isLocalRing <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsRepsLevelTranslates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory

section

variable {E : Type} [Field E] [NumberField E] {dim : (E →+* ℂ) → ℕ}

theorem levReps_act_mul (a b : 𝓞 E) (v : I2.Vsp dim) : I2.act a (I2.act b v) = I2.act (a * b) v := by
  ext i
  simp only [I2.act, RingOfIntegers.coe_eq_algebraMap, map_mul]
  exact (mul_assoc _ _ _).symm

theorem levReps_act_nat (m : ℕ) (v : I2.Vsp dim) : I2.act (m : 𝓞 E) v = (m : ℂ) • v := by
  ext i
  simp [I2.act]

theorem levReps_act_smul (a : 𝓞 E) (c : ℂ) (v : I2.Vsp dim) : I2.act a (c • v) = c • I2.act a v := by
  ext i
  simp [I2.act]
  ring

theorem levReps_act_add (a : 𝓞 E) (v w : I2.Vsp dim) : I2.act a (v + w) = I2.act a v + I2.act a w := by
  ext i
  simp [I2.act, mul_add]

theorem levReps_act_neg (a : 𝓞 E) (v : I2.Vsp dim) : I2.act a (-v) = -I2.act a v := by
  ext i
  simp [I2.act]

end

theorem isReps_level_translates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (T : I2.PT E) (mk : Dw.La →+ I2.Vsp T.dim) (α : 𝓞 E), α * H.bar α = (l.M : 𝓞 E) → l.Mb = Ideal.span {H.bar α} → (∀ a, mk a ∈ T.L) → (∀ (β : 𝓞 E) a, mk (β • a) = I2.act β (mk a)) → (∀ a, (∃ v ∈ T.L, mk a = (l.M : ℂ) • v) → ∃ b, a = l.M • b) → (∀ v ∈ T.L, ∃ a, ∃ v' ∈ T.L, v = mk a + (l.M : ℂ) • v') → ∀ x2 : LevQ Dw l → Dw.La, (∀ q, x2 q ∈ (Ideal.span {(2 : 𝓞 E)} * (l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) ^ 2) • (⊤ : Submodule (𝓞 E) Dw.La)) → (∀ q, x2 q - levRep q ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) → ∀ n : ℕ, ∃ K : Finset (Fin n → I2.Vsp T.dim), I2.IsReps T l.M n (vspActL α) K ∧ ∀ b ∈ K, ∃ q : Fin n → LevQ Dw l, b = fun i => I2.act (H.bar α) (-(((l.M : ℂ) ^ 2)⁻¹ • mk (x2 (q i)))) := by
  intro E _ _ _ H Dw l T mk α hα hMb hL hlin hinj hsurj x2 hx2 hrep n
  classical
  haveI : Finite (LevQ Dw l) := (card_levQ E H Dw l).1
  haveI : Fintype (LevQ Dw l) := Fintype.ofFinite _
  have hM : (l.M : ℂ) ≠ 0 := by
    have := l.three_le
    exact Nat.cast_ne_zero.2 (by omega)
  have hbb : H.bar (H.bar α) = α := by
    apply Subtype.ext
    change ((H.bar (H.bar α) : 𝓞 E) : E) = (α : E)
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply]
  have hmap : l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {α} := by
    rw [hMb, Ideal.map_span, Set.image_singleton]
    exact congrArg (fun z => Ideal.span {z}) hbb
  have hsm : ∀ (c : 𝓞 E) (y : Dw.La), y ∈ Ideal.span {c} • (⊤ : Submodule (𝓞 E) Dw.La) ↔ ∃ z, y = c • z := by
    intro c y
    rw [Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨fun ⟨z, _, h⟩ => ⟨z, h.symm⟩, fun ⟨z, h⟩ => ⟨z, trivial, h.symm⟩⟩
  have hu : ∀ q, ∃ u : Dw.La, x2 q = α • α • u := by
    intro q
    have h := hx2 q
    rw [hmap, Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton, hsm] at h
    obtain ⟨z, hz⟩ := h
    refine ⟨(2 : 𝓞 E) • z, ?_⟩
    rw [hz, smul_smul, smul_smul]
    congr 1
    ring
  have hcls : ∀ q, (Submodule.Quotient.mk (x2 q) : LevQ Dw l) = q := by
    intro q
    rw [(Submodule.Quotient.eq _).2 (hrep q)]
    exact Classical.choose_spec (Submodule.Quotient.mk_surjective _ q)
  obtain ⟨r, s, hrs⟩ : ∃ r s : 𝓞 E, r * H.bar α + s * α = 1 := by
    have h := l.coprime
    rw [hmap, hMb, Ideal.eq_top_iff_one, ← Ideal.span_insert, Ideal.mem_span_pair] at h
    exact h
  set t : LevQ Dw l → I2.Vsp T.dim := fun q => I2.act (H.bar α) (-(((l.M : ℂ) ^ 2)⁻¹ • mk (x2 q))) with ht
  have hαt : ∀ q, I2.act α (t q) = -((l.M : ℂ)⁻¹ • mk (x2 q)) := by
    intro q
    simp only [ht]
    rw [levReps_act_mul, hα, levReps_act_nat, smul_neg, smul_smul]
    congr 2
    field_simp
  have hMt : ∀ q, (l.M : ℂ) • t q ∈ T.L := by
    intro q
    obtain ⟨u, hq⟩ := hu q
    have : (l.M : ℂ) • t q = -mk (α • u) := by
      simp only [ht]
      rw [hq, hlin α (α • u), levReps_act_neg, levReps_act_smul, levReps_act_mul, mul_comm (H.bar α), hα,
        levReps_act_nat, smul_neg, smul_smul, smul_smul]
      have : (l.M : ℂ) * ((l.M : ℂ) ^ 2)⁻¹ * l.M = 1 := by field_simp
      rw [this, one_smul]
    rw [this]
    exact T.L.neg_mem (hL _)
  have hsub : ∀ (b : I2.Vsp T.dim) q, vspActL α (b - t q) = I2.act α b + (l.M : ℂ)⁻¹ • mk (x2 q) := by
    intro b q
    rw [map_sub]
    change I2.act α b - I2.act α (t q) = _
    rw [hαt, sub_neg_eq_add]
  have hex : ∀ b : I2.Vsp T.dim, (l.M : ℂ) • b ∈ T.L → ∃ q, vspActL α (b - t q) ∈ T.L := by
    intro b hb
    obtain ⟨a, v', hv', hab⟩ := hsurj _ hb
    refine ⟨Submodule.Quotient.mk (-(α • a)), ?_⟩
    set q : LevQ Dw l := Submodule.Quotient.mk (-(α • a)) with hq
    have h1 : x2 q - -(α • a) ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La) :=
      (Submodule.Quotient.eq _).1 ((hcls q).trans hq)
    rw [hMb, hsm] at h1
    obtain ⟨d, hd⟩ := h1
    obtain ⟨u, hqu⟩ := hu q
    have h2 : x2 q + α • a = (l.M : 𝓞 E) • (r • (α • u + a) + s • d) := by
      have e1 : x2 q + α • a = α • (α • u + a) := by rw [hqu, smul_add]
      have e2 : x2 q + α • a = H.bar α • d := by rw [← hd, sub_neg_eq_add]
      calc x2 q + α • a = (r * H.bar α + s * α) • (x2 q + α • a) := by rw [hrs, one_smul]
        _ = (r * H.bar α) • α • (α • u + a) + (s * α) • H.bar α • d := by rw [add_smul, ← e1, ← e2]
        _ = _ := by
          rw [← hα, smul_add (α * H.bar α)]
          simp only [smul_smul (r * H.bar α), smul_smul (s * α), smul_smul (α * H.bar α)]
          congr 2 <;> ring
    have hb' : b = (l.M : ℂ)⁻¹ • mk a + v' := by
      calc b = (l.M : ℂ)⁻¹ • (l.M : ℂ) • b := by rw [smul_smul, inv_mul_cancel₀ hM, one_smul]
        _ = _ := by rw [hab, smul_add, smul_smul, inv_mul_cancel₀ hM, one_smul]
    have h3 : vspActL α (b - t q) = mk (r • (α • u + a) + s • d) + I2.act α v' := by
      rw [hsub, hb', levReps_act_add, levReps_act_smul, ← hlin, add_right_comm, ← smul_add, ← map_add (f := _),
        add_comm (α • a), h2, hlin, levReps_act_nat, smul_smul, inv_mul_cancel₀ hM, one_smul]
    rw [h3]
    exact T.L.add_mem (hL _) (T.stable _ _ hv')
  have huniq : ∀ (b : I2.Vsp T.dim) q q', vspActL α (b - t q) ∈ T.L → vspActL α (b - t q') ∈ T.L → q = q' := by
    intro b q q' h h'
    have h1 := T.L.sub_mem h h'
    rw [hsub, hsub, add_sub_add_left_eq_sub, ← smul_sub, ← map_sub] at h1
    obtain ⟨z, hz⟩ := hinj (x2 q - x2 q') ⟨_, h1, by rw [smul_smul, mul_inv_cancel₀ hM, one_smul]⟩
    rw [← hcls q, ← hcls q']
    refine (Submodule.Quotient.eq _).2 ?_
    rw [hMb, hsm]
    exact ⟨α • z, by rw [hz, smul_smul, mul_comm, hα, Nat.cast_smul_eq_nsmul]⟩
  refine ⟨Finset.univ.image (fun q : Fin n → LevQ Dw l => fun i => t (q i)), ⟨?_, ?_⟩, ?_⟩
  · intro b hb k
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hb
    exact hMt _
  · intro b hb
    choose q hq using fun k => hex (b k) (hb k)
    refine ⟨fun i => t (q i), ⟨Finset.mem_image.2 ⟨q, Finset.mem_univ _, rfl⟩, hq⟩, ?_⟩
    rintro b' ⟨hb', h'⟩
    obtain ⟨q', -, rfl⟩ := Finset.mem_image.1 hb'
    funext k
    rw [huniq (b k) _ _ (h' k) (hq k)]
  · intro b hb
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hb
    exact ⟨q, rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HmEqDiagonal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HermDiag

private theorem hermForm_eq_star_swap {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) (hA : A.IsHermitian)
    (z w : Fin g → ℂ) : hermForm A z w = star (hermForm A w z) := by
  unfold hermForm
  simp only [dotProduct, Matrix.mulVec, star_sum, star_mul', Finset.mul_sum, Pi.star_apply, star_star]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hA.apply j i]
  ring

private theorem eq_of_im_hermForm_eq_of_real_span_eq_univ {g : ℕ} {La : Type} [AddCommGroup La] (A B : Matrix (Fin g) (Fin g) ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (P : La →+ (Fin g → ℂ))
    (hP : Submodule.span ℝ (Set.range P) = ⊤)
    (h : ∀ a b, (hermForm A (P a) (P b)).im = (hermForm B (P a) (P b)).im) : A = B := by
  let L : (Fin g → ℂ) → (Fin g → ℂ) →ₗ[ℝ] ℝ := fun w =>
    { toFun := fun z => (hermForm A z w).im - (hermForm B z w).im
      map_add' := fun z z' => by
        simp only [hermForm, add_dotProduct, Complex.add_im]; ring
      map_smul' := fun t z => by
        simp only [hermForm, smul_dotProduct, Complex.smul_im, RingHom.id_apply, smul_eq_mul]; ring }
  have hL : ∀ w z, L w z = (hermForm A z w).im - (hermForm B z w).im := fun _ _ => rfl
  have zero_of : ∀ w, (∀ a, L w (P a) = 0) → ∀ z, L w z = 0 := by
    intro w hw z
    have h0 : L w = 0 := LinearMap.ext_on hP (fun y hy => by
      obtain ⟨a, rfl⟩ := hy
      simpa using hw a)
    rw [h0]; rfl
  have key1 : ∀ a z, L (P a) z = 0 := fun a => zero_of _ (fun b => by rw [hL, h b a, sub_self])
  have key2 : ∀ z w, L w z = 0 := by
    intro z w
    refine zero_of w (fun a => ?_) z
    have h1 := key1 a w
    rw [hL] at h1 ⊢
    rw [hermForm_eq_star_swap A hA (P a) w, hermForm_eq_star_swap B hB (P a) w]
    simp only [Complex.star_def, Complex.conj_im]
    linarith
  ext i j
  apply Complex.ext
  · have h1 := key2 (Pi.single i Complex.I) (Pi.single j 1)
    rw [hL] at h1
    simp [hermForm, Matrix.mulVec, dotProduct, Pi.single_apply] at h1
    linarith
  · have h1 := key2 (Pi.single i 1) (Pi.single j 1)
    rw [hL] at h1
    simp [hermForm, Matrix.mulVec, dotProduct, Pi.single_apply] at h1
    linarith

theorem hm_eq_diagonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (W : UnfAt U k x) (Wu : UnitAt W), GoodEmb c σ → IsUnf U → (U.X k).IsOrtho x.1 → Wu.Hm = Matrix.diagonal fun j => ((2 * ‖relab c σ (W.e j).1 (U.X k).ξ0‖ : ℝ) : ℂ) := by
  intro E _ _ _ H Dw l Xo c σ r U k x W Wu hg hU ho
  obtain ⟨hr, htype, -⟩ := hU
  obtain ⟨hp0, hΨ⟩ := htype k
  have hbij : Function.Bijective (relab c σ) := by
    rw [← Finite.injective_iff_bijective]
    intro τ₁ τ₂ h12
    ext y
    have h1 : σ (Formalism.L2.Pj.embF c τ₁ y) = σ (Formalism.L2.Pj.embF c τ₂ y) :=
      congrArg (fun f : E →+* ℂ => f y) h12
    exact congrArg Subtype.val (σ.injective h1)
  have hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
    intro τ
    have h1 : (H.rt : E) ^ 2 = -(H.d : E) := by
      have := congrArg (fun t : 𝓞 E => (t : E)) H.rt_sq
      simpa using this
    have h2 : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
      rw [← map_pow, h1, map_neg, map_natCast, H.sqrt_neg_disc_sq]
    exact sq_eq_sq_iff_eq_or_eq_neg.mp h2
  have hkey : ∀ τ : E →+* ℂ, relab c σ τ (H.rt : E) = H.rt0 ↔ τ (H.rt : E) = H.rt0 := by
    intro τ
    have hg' : σ (IntermediateField.inclusion c.le (baseKA l).ρ) = H.rt0 := hg
    have hρ : ((IntermediateField.inclusion c.le (baseKA l).ρ : c.F) : ℂ) = H.rt0 := rfl
    rcases hsq τ with h | h
    · have e : Formalism.L2.Pj.embF c τ (H.rt : E) = IntermediateField.inclusion c.le (baseKA l).ρ :=
        Subtype.ext (h.trans hρ.symm)
      have h3 : relab c σ τ (H.rt : E) = H.rt0 := by
        show σ (Formalism.L2.Pj.embF c τ (H.rt : E)) = H.rt0
        rw [e, hg']
      rw [h3, h]
    · have e : Formalism.L2.Pj.embF c τ (H.rt : E) = -IntermediateField.inclusion c.le (baseKA l).ρ :=
        Subtype.ext (by
          show τ (H.rt : E) = -((IntermediateField.inclusion c.le (baseKA l).ρ : c.F) : ℂ)
          rw [h, hρ])
      have h3 : relab c σ τ (H.rt : E) = -H.rt0 := by
        show σ (Formalism.L2.Pj.embF c τ (H.rt : E)) = -H.rt0
        rw [e, map_neg, hg']
      rw [h3, h]
  have hpm : ∀ τ, relab c σ τ ∈ (U.X k).Ψ → Dw.mult τ = Dw.p := by
    intro τ hτ
    rw [hΨ, hkey] at hτ
    unfold Geo.Tor.Datum.mult
    rw [if_pos hτ]
  have hqm : ∀ τ, relab c σ τ ∉ (U.X k).Ψ → Dw.mult τ = Dw.q := by
    intro τ hτ
    rw [hΨ, hkey] at hτ
    unfold Geo.Tor.Datum.mult
    rw [if_neg hτ]
  obtain ⟨f, hf⟩ := GlobalTheory.FrameUnif.exists_letter_equiv (U.X k).Ψ (U.X k).cmType Dw.p Dw.q r hr
    (relab c σ) hbij Dw.mult hpm hqm
  set idx : Fin W.g ≃ (U.X k).Ψ × Fin r := W.e.trans f with hidx
  have hz : ∀ a j, W.Pm a j = if ((idx j).2 : ℕ) < Dw.q then
      FD.hermC (idx j).1.1 (U.X k).Gm (FD.col (FD.mat x.1 (idx j).1) (idx j).2)
        (FD.Data.emb (idx j).1.1 (W.φ k a : Fin r → E))
      else ((FD.mat x.1 (idx j).1)⁻¹.mulVec (FD.Data.emb (idx j).1.1 (W.φ k a : Fin r → E))) (idx j).2 := by
    intro a j
    rw [W.pm_eq a j]
    unfold Formalism.L2.Pj.perFr
    have hj : idx j = f (W.e j) := rfl
    rw [hj]
    rcases hf (W.e j) with ⟨hin, h1, h2⟩ | ⟨hout, h1, h2, h3⟩
    · have hi : (U.X k).p0 + ((W.e j).2 : ℕ) < r := by
        have := (f (W.e j)).2.isLt
        omega
      rw [dite_eq_left hin, dite_eq_left hi, if_neg (by omega)]
      have e1 : (f (W.e j)).1 = ⟨relab c σ (W.e j).1, hin⟩ := Subtype.ext h1
      have e2 : (f (W.e j)).2 = ⟨(U.X k).p0 + ((W.e j).2 : ℕ), hi⟩ := Fin.ext (by
        show ((f (W.e j)).2 : ℕ) = (U.X k).p0 + ((W.e j).2 : ℕ)
        omega)
      rw [e1, e2]
    · have hcj : conjEmb (relab c σ (W.e j).1) = (f (W.e j)).1.1 := by
        rw [h1]
        exact RingHom.ext fun y => by rw [ComplexEmbedding.conjugate_coe_eq]; rfl
      have hin' : conjEmb (relab c σ (W.e j).1) ∈ (U.X k).Ψ := by
        rw [hcj]
        exact (f (W.e j)).1.2
      have hi : (U.X k).p0 - 1 - ((W.e j).2 : ℕ) < r := by
        have := (f (W.e j)).2.isLt
        omega
      rw [dite_eq_right hout, dite_eq_left hin', dite_eq_left hi, if_pos (by omega)]
      have e1 : (f (W.e j)).1 = ⟨conjEmb (relab c σ (W.e j).1), hin'⟩ := Subtype.ext hcj.symm
      have e2 : (f (W.e j)).2 = ⟨(U.X k).p0 - 1 - ((W.e j).2 : ℕ), hi⟩ := Fin.ext (by
        show ((f (W.e j)).2 : ℕ) = (U.X k).p0 - 1 - ((W.e j).2 : ℕ)
        omega)
      rw [e1, e2]
  have hcc : FD.cc (-(U.X k).ξ0) = -(-(U.X k).ξ0) := by
    have h := (U.X k).ξ0_im
    unfold FD.cc at h ⊢
    rw [map_neg, h]
  have hx : ∀ τ : (U.X k).Ψ, FD.gram τ.1 (U.X k).Gm (FD.mat x.1 τ) =
      Matrix.diagonal fun a : Fin r => ((FD.sgn Dw.q (a : ℕ) : ℝ) : ℂ) := by
    intro τ
    rw [← hp0]
    exact ho τ
  set D0 : Matrix (Fin W.g) (Fin W.g) ℂ :=
    Matrix.diagonal fun j => ((2 * ((idx j).1.1 (-(U.X k).ξ0)).im : ℝ) : ℂ) with hD0
  have hD : ∀ a b, (hermForm Wu.Hm (W.Pm a) (W.Pm b)).im = (hermForm D0 (W.Pm a) (W.Pm b)).im := by
    intro a b
    rw [Wu.c1 a b, hD0, GlobalTheory.OrthoHerm.im_diag_eq_trace Dw.q (-(U.X k).ξ0) (U.X k).Gm (U.X k).Ψ
      (U.X k).cmType idx hcc x.1 hx (W.φ k a : Fin r → E) (W.φ k b : Fin r → E) (W.Pm a) (W.Pm b)
      (hz a) (hz b), ← W.isom k a b]
    push_cast
    rfl
  have hD0h : D0.IsHermitian := by
    rw [hD0]
    apply Matrix.isHermitian_diagonal_of_self_adjoint
    ext j
    simp
  obtain ⟨-, -, -, hspan, -⟩ := W.per
  have hHm : Wu.Hm = D0 := eq_of_im_hermForm_eq_of_real_span_eq_univ Wu.Hm D0 Wu.herm hD0h W.Pm hspan hD
  rw [hHm, hD0]
  congr 1
  funext j
  have hpos := Wu.pos (Pi.single j 1) (by simp)
  rw [hHm, hD0] at hpos
  have hdiag : (hermForm (Matrix.diagonal fun j => ((2 * ((idx j).1.1 (-(U.X k).ξ0)).im : ℝ) : ℂ))
      (Pi.single j 1) (Pi.single j 1)).re = 2 * ((idx j).1.1 (-(U.X k).ξ0)).im := by
    simp [hermForm]
  rw [hdiag, map_neg, Complex.neg_im] at hpos
  have hre : ((idx j).1.1 (U.X k).ξ0).re = 0 := by
    have h1 : starRingEnd ℂ ((idx j).1.1 (U.X k).ξ0) = -((idx j).1.1 (U.X k).ξ0) := by
      rw [← NumberField.IsCMField.complexEmbedding_complexConj (φ := (idx j).1.1) (x := (U.X k).ξ0),
        ← map_neg]
      congr 1
      exact (U.X k).ξ0_im
    have h2 := congrArg Complex.re h1
    simp at h2
    linarith
  have hnorm : ‖relab c σ (W.e j).1 (U.X k).ξ0‖ = ‖(idx j).1.1 (U.X k).ξ0‖ := by
    have hj : idx j = f (W.e j) := rfl
    rw [hj]
    rcases hf (W.e j) with ⟨-, h1, -⟩ | ⟨-, h1, -, -⟩
    · rw [h1]
    · rw [h1, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]
  have hfin : ((idx j).1.1 (-(U.X k).ξ0)).im = ‖relab c σ (W.e j).1 (U.X k).ξ0‖ := by
    rw [hnorm, ← (Complex.abs_im_eq_norm).mpr hre, map_neg, Complex.neg_im,
      abs_of_neg (by linarith)]
  rw [hfin]

end GlobalTheory.HermDiag
end
