module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSandwichOfHodgeTateFree

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.TrivflagNef
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsVanishingIdeal
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.GfCurve
section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.GeoNumNonnegOfRegular
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Bridge.GeoNum (red red_surjective ker_red comap_map_eq quotEquiv)

namespace PositivityTheory.HtPt.Gf

variable {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]

theorem geoNum_nonneg_of_regular (p : ℕ) [Fact p.Prime] {W : Ideal (MRing J)} (hW : IsMultiProjPrime W)
    (hp : (p : MRing J) ∈ W) (hdim : ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞))
    {f g : MRing J} {bf bg : K → ℕ} {a : K → ℤ} (hf : IsMultiHomog f bf) (hg : IsMultiHomog g bg)
    (ha : ∀ k, (bf k : ℤ) - bg k = a k) (hfW : f ∉ W) (hgW : g ∉ W)
    (hreg : ∀ t : ∀ k, J k, (∀ k, (X ⟨k, t k⟩ : MRing J) ∉ W) → ∃ (n : ℕ) (c : K → ℕ) (v : MRing J),
      ¬ p ∣ n ∧ n * mon t c * f - v * g ∈ W) : 0 ≤ geoNum 1 W (fun _ => a) := by
  classical
  have hC : (MvPolynomial.C (p : ℤ) : MRing J) ∈ W := by
    simpa [map_natCast] using hp
  have hker : RingHom.ker (red (ι := J) p) ≤ W := by
    rw [ker_red]
    exact (Ideal.span_le).2 (by simpa using hC)
  set P := Ideal.map (red (ι := J) p) W with hPdef
  have hcomap : Ideal.comap (red (ι := J) p) P = W := comap_map_eq p hker
  have hWp : W.IsPrime := hW.1
  have hPprime : P.IsPrime := Ideal.map_isPrime_of_surjective (red_surjective p) hker
  have hsupp : ∀ h : MRing J, ∀ b : K → ℕ, IsMultiHomog h b →
      GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomog (red (ι := J) p h) b := by
    intro h b hh
    rw [GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff]
    intro m hm k
    exact hh m (MvPolynomial.support_map_subset _ _ hm) k
  have hPhom : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiHomogIdeal P := by
    rw [GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff]
    obtain ⟨S, hS, rfl⟩ := hW.2.1
    refine ⟨(red (ι := J) p) '' S, ?_, ?_⟩
    · rintro _ ⟨h, hh, rfl⟩
      obtain ⟨b, hb⟩ := hS h hh
      exact ⟨b, (GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff _ _).1 (hsupp h b hb)⟩
    · rw [hPdef, Ideal.map_span]
  have hPrel : GroundTheory.Heights₂.Heights.NumbersDVR.IsRelevant P := by
    rw [← GroundTheory.Heights₂.Heights.Bridge.GeoNum.isRelevant_comap_iff p P, hcomap]
    exact hW.2.2
  have hPm : GroundTheory.Heights₂.Heights.NumbersDVR.IsMultiProjPrime P := ⟨hPprime, hPhom, hPrel⟩
  have hdimP : ringKrullDim (GroundTheory.Heights₂.Heights.NumbersDVR.MRing J (ZMod p) ⧸ P) =
      ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    rw [← hdim, ← ringKrullDim_eq_of_ringEquiv (quotEquiv p P), hcomap]
  have hreg' : GroundTheory.Heights₂.Heights.Model.IsRegularSection P a (red (ι := J) p f) (red (ι := J) p g) := by
    refine ⟨⟨bf, bg, hsupp f bf hf, hsupp g bg hg, funext ha⟩, ?_, ?_, ?_⟩
    · intro hm
      exact hfW (by rw [← hcomap]; exact hm)
    · intro hm
      exact hgW (by rw [← hcomap]; exact hm)
    · intro W' hW' hPW'
      set W'' := Ideal.comap (red (ι := J) p) W'
      have hW'pr : W'.IsPrime := hW'.1
      have hW''pr : W''.IsPrime := Ideal.comap_isPrime _ _
      have hWW'' : W ≤ W'' := by
        rw [← hcomap]
        exact Ideal.comap_mono hPW'
      have hrel : IsRelevant W'' :=
        (GroundTheory.Heights₂.Heights.Bridge.GeoNum.isRelevant_comap_iff p W').2 hW'.relevant
      choose t ht using hrel
      obtain ⟨n, c, v, hn, hv⟩ := hreg t (fun k hk => ht k (hWW'' hk))
      refine ⟨red (ι := J) p ((n : MRing J) * mon t c), red (ι := J) p v, ?_, ?_⟩
      · intro hu
        have hu' : ((n : MRing J) * mon t c) ∈ W'' := hu
        rcases hW''pr.mem_or_mem hu' with h1 | h1
        · exact natCast_not_mem hW''pr.ne_top (hWW'' hp) hn h1
        · exact mon_not_mem hW''pr ht c h1
      · have := Ideal.mem_map_of_mem (red (ι := J) p) hv
        simpa [map_sub, map_mul] using this
  have key := GroundTheory.Heights₂.Heights.Model.SectionNef.proof K J (ZMod p) P hPm hdimP a
    (red (ι := J) p f) (red (ι := J) p g) hreg'
  rw [GroundTheory.Heights₂.Heights.Bridge.intNum_map_eq_geoNum p 1 W hW hC hdim] at key
  have hfun : (![a] : Fin 1 → K → ℤ) = fun _ => a := by
    funext i
    fin_cases i
    rfl
  rwa [hfun] at key

end PositivityTheory.HtPt.Gf
end

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace PositivityTheory.HtPt.Gf

theorem curve_sec_nef : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (W : Ideal (MRing J)) (a : K → ℤ) (r : (∀ k, J k) → Ω), IsMultiProjPrime W → mCoordIdeal y ≤ W → charOf W = p → ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) → (∀ s, mseg y s ≠ 0 → r s ∈ chartRing o (mseg y) s) → (∀ s t, mseg y s ≠ 0 → mseg y t ≠ 0 → ∃ (n : ℕ) (z : Ω), z ∈ chartRing o (mseg y) t ∧ (mseg y s / mseg y t) ^ n * (r s * chartMon y s a / chartMon y t a - r t) = p * z) → (∃ (s : ∀ k, J k) (n d : ℕ) (g : MRing J), (∀ k, (X ⟨k, s k⟩ : MRing J) ∉ W) ∧ ¬ p ∣ n ∧ IsMultiHomog g (fun _ => d) ∧ g ∉ W ∧ n * r s * mseg y s ^ d = aeval y g) → 0 ≤ geoNum 1 W (fun _ => a) := by
  intro Ω _ _ K _ J _ y p _ o _ _ ho W a r hW hle hch hdim hr hov ⟨s, n, d, g, hs, hn, hg, hgW, hgy⟩
  have hp := natCast_mem_of_charOf hch
  have hP := hW.1
  have hs0 := mseg_ne_zero hle hs
  let ap : K → ℕ := fun k => (a k).toNat
  let am : K → ℕ := fun k => (-a k).toNat
  refine geoNum_nonneg_of_regular p hW hp hdim (hom_mul hg (hom_mon s ap))
    (hom_mul (hom_mon s fun _ => d) (hom_mon s am)) (fun k => ?_)
    (fun h => (hP.mem_or_mem h).elim hgW (mon_not_mem hP hs _))
    (fun h => (hP.mem_or_mem h).elim (mon_not_mem hP hs _) (mon_not_mem hP hs _)) fun t ht => ?_
  · simp only [Pi.add_apply, ap, am]
    omega
  have ht0 := mseg_ne_zero hle ht
  obtain ⟨m, z, hz, hrel⟩ := hov s t hs0 ht0
  obtain ⟨n₁, e₁, g₁, hn₁, hg₁, hy₁⟩ := exists_rep ho ht0 (hr t ht0)
  obtain ⟨n₂, e₂, g₂, hn₂, hg₂, hy₂⟩ := exists_rep ho ht0 hz
  refine ⟨n₁ * n₂, (fun _ => e₁ + e₂) + am, n * (n₂ * (g₁ * mon t (fun _ => e₂) * mon t ap)),
    fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim hn₁ hn₂, ?_⟩
  have hsplit : mon t ((fun _ => e₁ + e₂) + am) = mon t (fun _ => e₁ + e₂) * mon t am := by
    simp [mon, pow_add, Finset.prod_mul_distrib]
  have hz0 : mon s (fun _ => m) * (((n₁ * n₂ : ℕ) : MRing J) * (mon t (fun _ => e₁ + e₂) * mon t am * (g * mon s ap)) -
      n * (n₂ * (g₁ * mon t (fun _ => e₂) * mon t ap * (mon s (fun _ => d) * mon s am)))) -
      p * (n * (n₁ * (g₂ * mon t (fun _ => e₁ + m) * mon s (fun _ => d) * mon s am * mon t ap))) ∈
        mCoordIdeal y := by
    refine mem_mCoordIdeal (d := fun k => m + e₁ + e₂ + d + ap k + am k) (hom_sub (hom_of_eq (hom_mul (hom_mon _ _)
      (hom_sub (hom_nat_mul _ (hom_mul (hom_mul (hom_mon _ _) (hom_mon _ _)) (hom_mul hg (hom_mon _ _))))
        (hom_nat_mul _ (hom_nat_mul _ (hom_of_eq (hom_mul (hom_mul (hom_mul hg₁ (hom_mon _ _)) (hom_mon _ _))
          (hom_mul (hom_mon _ _) (hom_mon _ _))) fun k => ?_))))) fun k => ?_)
      (hom_nat_mul _ (hom_nat_mul _ (hom_nat_mul _ (hom_of_eq (hom_mul (hom_mul (hom_mul (hom_mul hg₂ (hom_mon _ _))
        (hom_mon _ _)) (hom_mon _ _)) (hom_mon _ _)) fun k => ?_))))) ?_
    · simp only [Pi.add_apply]; omega
    · simp only [Pi.add_apply]; omega
    · simp only [Pi.add_apply]; omega
    rw [chartMon_eq_div hs0, chartMon_eq_div ht0] at hrel
    have hne : ∀ {u : ∀ k, J k}, mseg y u ≠ 0 → ∀ c, aeval y (mon u c) ≠ 0 := fun hu c => by
      rw [aeval_mon]
      exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (Finset.prod_ne_zero_iff.1 hu k (Finset.mem_univ k))
    have h1 := hne hs0 am
    have h2 := hne ht0 am
    have h3 := hne ht0 ap
    simp only [map_sub, map_mul, map_natCast, aeval_mon_const, ← hgy, ← hy₁, ← hy₂]
    change (mseg y s / mseg y t) ^ m * (r s * (aeval y (mon s ap) / aeval y (mon s am)) /
      (aeval y (mon t ap) / aeval y (mon t am)) - r t) = p * z at hrel
    generalize aeval y (mon s ap) = A at *
    generalize aeval y (mon s am) = B at *
    generalize aeval y (mon t ap) = A' at *
    generalize aeval y (mon t am) = B' at *
    rw [div_pow] at hrel
    field_simp at hrel
    push_cast
    linear_combination (n * n₁ * n₂ * mseg y t ^ (e₁ + e₂) * mseg y s ^ d) * hrel
  have h1 := (Ideal.add_mem_iff_left W (W.neg_mem (W.mul_mem_right _ hp))).1 (by
    rw [← sub_eq_add_neg]; exact hle hz0)
  have h2 := (hP.mem_or_mem h1).resolve_left (mon_not_mem hP hs _)
  rw [hsplit]
  convert h2 using 1
  ring

end PositivityTheory.HtPt.Gf
end

section -- merged from Development.WeilBound.CoreStatements.HodgeTatePoints.ExistsMinorNeZero
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT

namespace PositivityTheory.HtPt.Gf

theorem minor_mul_upper {B : Type} [CommRing B] {N i : ℕ} (hi : i ≤ N) (g U : Matrix (Fin N) (Fin N) B)
    (J : Fin i → Fin N) (hU : ∀ a b, b < a → U a b = 0) :
    ((g * U).submatrix J (Fin.castLE hi)).det =
      (g.submatrix J (Fin.castLE hi)).det * ∏ l : Fin i, U (Fin.castLE hi l) (Fin.castLE hi l) := by
  have h : (g * U).submatrix J (Fin.castLE hi) =
      g.submatrix J (Fin.castLE hi) * U.submatrix (Fin.castLE hi) (Fin.castLE hi) := by
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    rw [← Finset.sum_subset (Finset.subset_univ ((Finset.univ : Finset (Fin i)).map (Fin.castLEEmb hi))) ?_,
      Finset.sum_map]
    · rfl
    · intro k _ hk
      have hki : i ≤ (k : ℕ) := by
        by_contra hlt
        push_neg at hlt
        exact hk (Finset.mem_map.2 ⟨⟨k, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      have hlt : Fin.castLE hi b < k := by
        rw [Fin.lt_def, Fin.coe_castLE]
        omega
      rw [hU k (Fin.castLE hi b) hlt, mul_zero]
  have hT : (U.submatrix (Fin.castLE hi) (Fin.castLE hi)).IsUpperTriangular := by
    intro a b hab
    have hab' : Fin.castLE hi b < Fin.castLE hi a := by
      rw [Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]
      exact hab
    exact hU _ _ hab'
  rw [h, Matrix.det_mul, Matrix.det_of_upperTriangular hT]
  rfl

private theorem cb_lemma {B : Type} [CommRing B] {i N : ℕ} (A : Matrix (Fin i) (Fin N) B)
    (C : Matrix (Fin N) (Fin i) B) :
    (A * C).det = ∑ p : Fin i → Fin N, (∏ a, A a (p a)) * (C.submatrix p id).det := by
  have key : ∀ p : Fin i → Fin N, (C.submatrix p id).det =
      ∑ σ : Equiv.Perm (Fin i), Equiv.Perm.sign σ • ∏ a, C (p a) (σ a) := by
    intro p
    rw [← Matrix.det_transpose, Matrix.det_apply]
    rfl
  simp_rw [key]
  rw [← Matrix.det_transpose, Matrix.det_apply]
  simp only [Matrix.transpose_apply, Matrix.mul_apply]
  simp_rw [Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.smul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib, mul_smul_comm]

private theorem matAct_of_span_residue_spans {B : Type} [CommRing B] {N i : ℕ} (hi : i ≤ N) (g : Matrix (Fin N) (Fin N) B)
    (hg : IsUnit g.det) :
    Ideal.span (Set.range fun J : Fin i → Fin N => (g.submatrix J (Fin.castLE hi)).det) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have h1 : g⁻¹.submatrix (Fin.castLE hi) id * g.submatrix id (Fin.castLE hi) = 1 := by
    rw [← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id, Matrix.nonsing_inv_mul g hg]
    exact Matrix.submatrix_one _ (Fin.castLE_injective hi)
  have h2 := cb_lemma (g⁻¹.submatrix (Fin.castLE hi) id) (g.submatrix id (Fin.castLE hi))
  rw [h1, Matrix.det_one] at h2
  rw [h2]
  exact Ideal.sum_mem _ fun p _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨p, rfl⟩)

theorem lead_minor : ∀ (B : Type) [CommRing B] (N i : ℕ) (hi : i ≤ N), (∀ (g U : Matrix (Fin N) (Fin N) B) (J : Fin i → Fin N), (∀ a b, b < a → U a b = 0) → ((g * U).submatrix J (Fin.castLE hi)).det = (g.submatrix J (Fin.castLE hi)).det * ∏ l : Fin i, U (Fin.castLE hi l) (Fin.castLE hi l)) ∧ ∀ g : Matrix (Fin N) (Fin N) B, IsUnit g.det → Ideal.span (Set.range fun J : Fin i → Fin N => (g.submatrix J (Fin.castLE hi)).det) = ⊤ := by
  intro B _ N i hi
  exact ⟨fun g U J hU => minor_mul_upper hi g U J hU, fun g hg => matAct_of_span_residue_spans hi g hg⟩

theorem abel_nat (lam x : ℕ → ℝ) (n : ℕ) (hl : ∀ i, i + 1 ≤ n → lam (i + 1) ≤ lam i)
    (hx : ∀ i, i ≤ n → 0 ≤ ∑ l ∈ Finset.range i, x l) :
    lam n * ∑ l ∈ Finset.range (n + 1), x l ≤ ∑ l ∈ Finset.range (n + 1), lam l * x l := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun j hj => hl j (by omega)) (fun j hj => hx j (by omega))
    have hs := hx (n + 1) le_rfl
    have hln := hl n le_rfl
    rw [Finset.sum_range_succ x (n + 1), Finset.sum_range_succ (fun l => lam l * x l) (n + 1)]
    nlinarith [mul_nonneg (sub_nonneg.2 hln) hs]

theorem abel_sum : ∀ (N : ℕ) (lam x : Fin N → ℝ), (∀ i j, i ≤ j → lam j ≤ lam i) → (∀ i : ℕ, i ≤ N → 0 ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin N => (l : ℕ) < i), x l) → ∑ l, x l = 0 → 0 ≤ ∑ l, lam l * x l := by
  intro N lam x hl hx hsum
  cases N with
  | zero => simp
  | succ n =>
    obtain ⟨x', hx'⟩ : ∃ f : ℕ → ℝ, ∀ l : Fin (n + 1), f l = x l :=
      ⟨fun k => if h : k < n + 1 then x ⟨k, h⟩ else 0, fun l => by simp [l.isLt]⟩
    obtain ⟨lam', hlam'⟩ : ∃ f : ℕ → ℝ, ∀ l : Fin (n + 1), f l = lam l :=
      ⟨fun k => if h : k < n + 1 then lam ⟨k, h⟩ else 0, fun l => by simp [l.isLt]⟩
    have hsx : ∀ i, i ≤ n + 1 → ∑ l ∈ Finset.range i, x' l =
        ∑ l ∈ Finset.univ.filter (fun l : Fin (n + 1) => (l : ℕ) < i), x l := by
      intro i hi
      have e : ∀ l : Fin (n + 1), (if (l : ℕ) < i then x l else 0) =
          (fun k => if k < i then x' k else 0) (l : ℕ) := by
        intro l
        simp only [hx']
      rw [Finset.sum_filter, Finset.sum_congr rfl (fun l _ => e l),
        Fin.sum_univ_eq_sum_range (fun k => if k < i then x' k else 0), ← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext k
      simp only [Finset.mem_range, Finset.mem_filter]
      omega
    have htot : ∑ l ∈ Finset.range (n + 1), x' l = 0 := by
      rw [← Fin.sum_univ_eq_sum_range x' (n + 1)]
      simp only [hx']
      exact hsum
    have hprod : ∑ l ∈ Finset.range (n + 1), lam' l * x' l = ∑ l, lam l * x l := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => lam' k * x' k) (n + 1)]
      simp only [hx', hlam']
    have hl' : ∀ i, i + 1 ≤ n → lam' (i + 1) ≤ lam' i := by
      intro i hi
      have h1 := hlam' ⟨i + 1, by omega⟩
      have h2 := hlam' ⟨i, by omega⟩
      simp only at h1 h2
      rw [h1, h2]
      exact hl _ _ (Fin.mk_le_mk.2 (by omega))
    have hx'' : ∀ i, i ≤ n → 0 ≤ ∑ l ∈ Finset.range i, x' l := by
      intro i hi
      rw [hsx i (by omega)]
      exact hx i (by omega)
    have key := abel_nat lam' x' n hl' hx''
    rw [htot, hprod, mul_zero] at key
    exact key

end PositivityTheory.HtPt.Gf
end

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace PositivityTheory.HtPt.Gf

section Det

variable {o Ω : Type} [CommRing o] [CommRing Ω] [Algebra o Ω] (A : Subalgebra o Ω) {n : Type} [Fintype n]
  [DecidableEq n]

theorem det_mem {M : Matrix n n Ω} (h : ∀ i j, M i j ∈ A) : M.det ∈ A := by
  rw [Matrix.det_apply']
  exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => h _ _)

theorem det_add_smul {M Z : Matrix n n Ω} {c : Ω} (hM : ∀ i j, M i j ∈ A) (hZ : ∀ i j, Z i j ∈ A) (hc : c ∈ A) :
    ∃ z ∈ A, (M + c • Z).det = M.det + c * z := by
  let M' : Matrix n n A := fun i j => ⟨M i j, hM i j⟩
  let Z' : Matrix n n A := fun i j => ⟨Z i j, hZ i j⟩
  let c' : A := ⟨c, hc⟩
  have h : (M' + c' • Z').det - M'.det ∈ Ideal.span {c'} := by
    rw [← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Ideal.Quotient.eq, add_sub_cancel_left]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.1 h
  refine ⟨z, z.2, ?_⟩
  have := congrArg A.val hz
  rw [map_sub, AlgHom.map_det, AlgHom.map_det, map_mul] at this
  exact eq_add_of_sub_eq' this

end Det

section Van

variable {Ω : Type} [Field Ω] [CharZero Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)]
  {y : (Σ k, J k) → Ω} {p : ℕ} [hp : Fact p.Prime] {o : Type} [CommRing o] [Algebra o Ω]

theorem exists_vanishing_ideal
    (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω))
    {W : Ideal (MRing J)} (hP : W.IsPrime) (hle : mCoordIdeal y ≤ W) (hpW : (p : MRing J) ∈ W) {s : ∀ k, J k}
    (hs : ∀ k, (X ⟨k, s k⟩ : MRing J) ∉ W) :
    ∃ I : Ideal (chartRing o (mseg y) s), I ≠ ⊤ ∧ (p : chartRing o (mseg y) s) ∈ I ∧ ∀ x, x ∉ I →
      ∃ (n d : ℕ) (g : MRing J), ¬ p ∣ n ∧ IsMultiHomog g (fun _ => d) ∧ g ∉ W ∧
        n * (x : Ω) * mseg y s ^ d = aeval y g := by
  have hs0 := mseg_ne_zero hle hs
  let I : Ideal (chartRing o (mseg y) s) :=
    { carrier := {x | ∃ (n d : ℕ) (g : MRing J), ¬ p ∣ n ∧ IsMultiHomog g (fun _ => d) ∧ g ∈ W ∧
        n * (x : Ω) * mseg y s ^ d = aeval y g}
      zero_mem' := ⟨1, 0, 0, hp.out.not_dvd_one, hom_zero _, zero_mem _, by simp⟩
      add_mem' := by
        rintro u v ⟨n, d, g, h1, h2, h3, h4⟩ ⟨n', d', g', h1', h2', h3', h4'⟩
        refine ⟨n * n', d + d', n' * (g * mon s fun _ => d') + n * (mon s (fun _ => d) * g'),
          fun h => (hp.out.dvd_mul.1 h).elim h1 h1',
          hom_add (hom_nat_mul _ (hom_mul h2 (hom_mon _ _))) (hom_nat_mul _ (hom_mul (hom_mon _ _) h2')),
          add_mem (W.mul_mem_left _ (W.mul_mem_right _ h3)) (W.mul_mem_left _ (W.mul_mem_left _ h3')), ?_⟩
        simp only [map_add (f := _), map_mul, map_natCast, aeval_mon_const, ← h4, ← h4']
        push_cast; ring
      smul_mem' := by
        rintro u v ⟨n', d', g', h1', h2', h3', h4'⟩
        obtain ⟨n, d, g, h1, h2, h4⟩ := exists_rep ho hs0 u.2
        refine ⟨n * n', d + d', g * g', fun h => (hp.out.dvd_mul.1 h).elim h1 h1', hom_mul h2 h2',
          W.mul_mem_left _ h3', ?_⟩
        simp only [map_mul, ← h4, ← h4', smul_eq_mul]
        push_cast; ring }
  refine ⟨I, fun h => ?_, ⟨1, 0, p * mon s fun _ => 0, hp.out.not_dvd_one, hom_nat_mul _ (hom_mon _ _),
    W.mul_mem_right _ hpW, by simp [aeval_mon_const]⟩, fun x hx => ?_⟩
  · obtain ⟨n, d, g, h1, h2, h3, h4⟩ := (Ideal.eq_top_iff_one I).1 h
    have h5 : (n : MRing J) * mon s (fun _ => d) - g ∈ W := hle (mem_mCoordIdeal
      (hom_sub (hom_nat_mul _ (hom_mon _ _)) h2) (by simp [aeval_mon_const, ← h4]))
    have h6 : (n : MRing J) * mon s (fun _ => d) ∈ W := by simpa using add_mem h5 h3
    exact (hP.mem_or_mem h6).elim (natCast_not_mem hP.ne_top hpW h1) (mon_not_mem hP hs _)
  · obtain ⟨n, d, g, h1, h2, h4⟩ := exists_rep ho hs0 x.2
    exact ⟨n, d, g, h1, h2, fun h3 => hx ⟨n, d, g, h1, h2, h3, h4⟩, h4⟩

end Van

theorem sum_filter_lt {M : Type} [AddCommMonoid M] {N i : ℕ} (hi : i ≤ N) (f : Fin N → M) :
    ∑ l ∈ Finset.univ.filter (fun l : Fin N => (l : ℕ) < i), f l = ∑ l : Fin i, f (Fin.castLE hi l) := by
  symm
  refine Finset.sum_bij (fun l _ => Fin.castLE hi l) (by simp) (fun a _ b _ h => Fin.castLE_injective hi h) ?_
    (fun _ _ => rfl)
  intro b hb
  exact ⟨⟨b, by simpa using hb⟩, by simp, rfl⟩

theorem trivflag_deg : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o Ω] (ho : ∀ x : Ω, x ∈ (algebraMap o Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)) (W : Ideal (MRing J)) (N : ℕ) (b : Fin N → K → ℤ), IsMultiProjPrime W → mCoordIdeal y ≤ W → charOf W = p → ringKrullDim (MRing J ⧸ W) = ((1 + Fintype.card K : ℕ) : WithBot ℕ∞) → Num.TrivFlagMod o (p : o) y N b → (∀ i : ℕ, i ≤ N → ∑ l ∈ Finset.univ.filter (fun l : Fin N => (l : ℕ) < i), geoNum 1 W (fun _ => b l) ≤ 0) ∧ ∑ l, geoNum 1 W (fun _ => b l) = 0 := by
  intro Ω _ _ K _ J _ y p _ o _ _ ho W N b hW hle hch hdim ⟨g, h1, h2⟩
  have hpW := natCast_mem_of_charOf hch
  choose s₀ hs₀ using hW.2.2
  have hs0 := mseg_ne_zero hle hs₀
  obtain ⟨I, hI, hpI, hrep⟩ := exists_vanishing_ideal ho hW.1 hle hpW hs₀
  obtain ⟨c, hc⟩ := geoNum_one_linear W
  simp only [map_natCast] at h1 h2
  have hg : ∀ s, mseg y s ≠ 0 → ∀ i j, g s i j ∈ chartRing o (mseg y) s := fun s hs => (h1 s hs).1
  choose! h hh ρ hρ hdet using fun s hs => (h1 s hs).2
  have hsum : ∀ {ι : Type} [Fintype ι] (β : ι → K → ℤ),
      geoNum 1 W (fun _ => ∑ l, β l) = ∑ l, geoNum 1 W (fun _ => β l) := by
    intro ι _ β
    simp only [hc, Finset.sum_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hneg : ∀ a : K → ℤ, geoNum 1 W (fun _ => -a) = -geoNum 1 W (fun _ => a) := by
    intro a
    simp [hc]

  have hmin : ∀ (i : ℕ) (hi : i ≤ N) (J₀ : Fin i → Fin N) s t, mseg y s ≠ 0 → mseg y t ≠ 0 →
      ∃ (m : ℕ) (z : Ω), z ∈ chartRing o (mseg y) t ∧
        (mseg y s / mseg y t) ^ m * (((g s).submatrix J₀ (Fin.castLE hi)).det -
          ((g t).submatrix J₀ (Fin.castLE hi)).det * (chartMon y s (∑ l, b (Fin.castLE hi l)) /
            chartMon y t (∑ l, b (Fin.castLE hi l)))) = p * z := by
    intro i hi J₀ s t hs ht
    obtain ⟨m, U, Z, hU, hZ, hU0, hUd, -, e⟩ := h2 s t hs ht
    obtain ⟨z, hz, ez⟩ := det_add_smul (chartRing o (mseg y) t)
      (M := (g t * U).submatrix J₀ (Fin.castLE hi)) (Z := Z.submatrix J₀ (Fin.castLE hi)) (c := p)
      (fun a a' => by
        rw [Matrix.submatrix_apply, Matrix.mul_apply]
        exact sum_mem fun l _ => mul_mem (hg t ht _ _) (hU _ _))
      (fun a a' => hZ _ _) (natCast_mem _ _)
    refine ⟨m * i, z, hz, ?_⟩
    have e1 : (g t * U).submatrix J₀ (Fin.castLE hi) + (p : Ω) • Z.submatrix J₀ (Fin.castLE hi) =
        (mseg y s / mseg y t) ^ m • (g s).submatrix J₀ (Fin.castLE hi) :=
      (congrArg (fun M : Matrix (Fin N) (Fin N) Ω => M.submatrix J₀ (Fin.castLE hi)) e).symm
    rw [e1, Matrix.det_smul, minor_mul_upper hi _ _ _ hU0] at ez
    simp only [hUd, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      Finset.prod_div_distrib, ← pow_mul] at ez
    rw [chartMon_sum hs, chartMon_sum ht]
    linear_combination ez

  let G : Matrix (Fin N) (Fin N) (chartRing o (mseg y) s₀) := fun i j => ⟨g s₀ i j, hg s₀ hs0 i j⟩
  have hG : ∀ {i : ℕ} (u v : Fin i → Fin N), (((G.submatrix u v).det : chartRing o (mseg y) s₀) : Ω) =
      ((g s₀).submatrix u v).det := fun u v => (chartRing o (mseg y) s₀).val.map_det _
  have hone : Ideal.Quotient.mk I G.det * Ideal.Quotient.mk I ⟨h s₀, hh s₀ hs0⟩ = 1 := by
    rw [← map_mul, ← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq]
    have : G.det * ⟨h s₀, hh s₀ hs0⟩ - 1 = p * ⟨ρ s₀, hρ s₀ hs0⟩ := by
      apply Subtype.ext
      have := hG id id
      simp only [Matrix.submatrix_id_id] at this
      simp [this, hdet s₀ hs0]
    rw [this]
    exact I.mul_mem_right _ hpI
  have hnt : Nontrivial (chartRing o (mseg y) s₀ ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
  have hstep : ∀ (i : ℕ) (hi : i ≤ N), ∑ l : Fin i, geoNum 1 W (fun _ => b (Fin.castLE hi l)) ≤ 0 := by
    intro i hi
    obtain ⟨J₀, hJ₀⟩ : ∃ J₀ : Fin i → Fin N, (G.submatrix J₀ (Fin.castLE hi)).det ∉ I := by
      by_contra hall
      push Not at hall
      have := (lead_minor _ N i hi).2 ((Ideal.Quotient.mk I).mapMatrix G)
        (by rw [← RingHom.map_det]; exact IsUnit.of_mul_eq_one _ hone)
      refine bot_ne_top (α := Ideal (chartRing o (mseg y) s₀ ⧸ I)) (le_antisymm bot_le (this ▸ ?_))
      rw [Ideal.span_le]
      rintro _ ⟨J₀, rfl⟩
      have e : ((Ideal.Quotient.mk I).mapMatrix G).submatrix J₀ (Fin.castLE hi) =
        (Ideal.Quotient.mk I).mapMatrix (G.submatrix J₀ (Fin.castLE hi)) := rfl
      simp only [e, ← RingHom.map_det, SetLike.mem_coe, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]
      exact hall J₀
    obtain ⟨n, d, f, e1, e2, e3, e4⟩ := hrep _ hJ₀
    rw [hG] at e4
    have key := curve_sec_nef Ω K J y p o ho W (-∑ l, b (Fin.castLE hi l))
      (fun s => ((g s).submatrix J₀ (Fin.castLE hi)).det) hW hle hch hdim
      (fun s hs => det_mem _ fun a a' => hg s hs _ _) (fun s t hs ht => ?_) ⟨s₀, n, d, f, hs₀, e1, e2, e3, e4⟩
    · rw [hneg, hsum] at key
      linarith
    · obtain ⟨m, z, hz, e⟩ := hmin i hi J₀ s t hs ht
      obtain ⟨n', hn'⟩ := exists_pow_mul_trans_mem (o := o) hs ht (-∑ l, b (Fin.castLE hi l))
      refine ⟨n' + m, _, mul_mem hn' hz, ?_⟩
      have a1 := chartMon_ne_zero hs (∑ l, b (Fin.castLE hi l))
      have a2 := chartMon_ne_zero ht (∑ l, b (Fin.castLE hi l))
      rw [chartMon_neg, chartMon_neg, mul_left_comm, ← e]
      field_simp
      ring
  refine ⟨fun i hi => by rw [sum_filter_lt hi]; exact hstep i hi, le_antisymm (hstep N le_rfl) ?_⟩
  have hhI : (⟨h s₀, hh s₀ hs0⟩ : chartRing o (mseg y) s₀) ∉ I := fun hm => by
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hm, mul_zero] at hone
    exact zero_ne_one hone
  obtain ⟨n, d, f, e1, e2, e3, e4⟩ := hrep _ hhI
  rw [← hsum]
  refine curve_sec_nef Ω K J y p o ho W (∑ l, b l) h hW hle hch hdim hh (fun s t hs ht => ?_)
    ⟨s₀, n, d, f, hs₀, e1, e2, e3, e4⟩
  obtain ⟨m, z, hz, e⟩ := hmin N le_rfl id s t hs ht
  change (mseg y s / mseg y t) ^ m * ((g s).det - (g t).det * (chartMon y s (∑ l, b l) /
    chartMon y t (∑ l, b l))) = p * z at e
  obtain ⟨n₁, hn₁⟩ := exists_pow_mul_trans_mem (o := o) hs ht (∑ l, b l)
  obtain ⟨n₂, hn₂⟩ := exists_pow_mul_mem_chartRing (mseg y) s t hs (hh s hs)
  obtain ⟨n₃, hn₃⟩ := exists_pow_mul_mem_chartRing (mseg y) s t hs (hρ s hs)
  have hf := div_mem_chartRing (o := o) (mseg y) t s
  have d1 := hdet s hs
  have d2 := hdet t ht
  rw [mul_div_assoc]
  generalize chartMon y s (∑ l, b l) / chartMon y t (∑ l, b l) = γ at *
  generalize mseg y s / mseg y t = φ at *
  refine ⟨m + n₁ + n₂ + n₃, φ ^ (m + n₁ + n₂) * (φ ^ n₃ * ρ s) * h t - φ ^ (m + n₃) * (φ ^ n₁ * γ) * (φ ^ n₂ * h s) * ρ t -
    φ ^ (n₁ + n₃) * z * (φ ^ n₂ * h s) * h t, sub_mem (sub_mem (mul_mem (mul_mem (pow_mem hf _) hn₃) (hh t ht))
      (mul_mem (mul_mem (mul_mem (pow_mem hf _) hn₁) hn₂) (hρ t ht)))
      (mul_mem (mul_mem (mul_mem (pow_mem hf _) hz) hn₂) (hh t ht)), ?_⟩
  linear_combination (-φ ^ (n₁ + n₂ + n₃) * h s * h t) * e + φ ^ (m + n₁ + n₂ + n₃) * h t * d1 -
    φ ^ (m + n₁ + n₂ + n₃) * γ * h s * d2

end PositivityTheory.HtPt.Gf
end

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace PositivityTheory.HtPt.Gf

theorem trivflag_nef : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : Top.RootModel Ψ N) [CharZero M.Ω] (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o M.Ω] (ho : ∀ x : M.Ω, x ∈ (algebraMap o M.Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : M.Ω) / (b : M.Ω)), (∀ τ, Num.TrivFlagMod o (p : o) M.y N (fun i => M.xdeg (τ, i))) → ∀ mu : Top.Wt Ψ N, Top.Dominant mu → M.NefAt p mu 0 := by
  intro Ψ _ N M _ p _ o _ _ ho hτ mu hmu
  intro W hW
  obtain ⟨h1, h2, h3, h4⟩ := hW
  have key : ∀ τ : Ψ, 0 ≤ ∑ i : Fin N, mu τ i * (-(geoNum 1 W (fun _ : Fin 1 => M.xdeg (τ, i)) : ℝ)) := by
    intro τ
    obtain ⟨hp, ht⟩ := trivflag_deg M.Ω M.K M.ι M.y p o ho W N (fun i => M.xdeg (τ, i)) h1 h2 h3 h4 (hτ τ)
    apply abel_sum N (mu τ) (fun i => -(geoNum 1 W (fun _ : Fin 1 => M.xdeg (τ, i)) : ℝ))
    · intro a b hab
      exact hmu τ a b hab
    · intro i hi
      have := hp i hi
      simp only [Finset.sum_neg_distrib, neg_nonneg]
      exact_mod_cast this
    · simp only [Finset.sum_neg_distrib, neg_eq_zero]
      exact_mod_cast ht
  unfold Top.RootModel.curveDeg
  rw [Fintype.sum_option]
  simp only [Top.RootModel.coef, Top.RootModel.line, zero_div, zero_mul, zero_add, M.x_deg]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_nonneg fun τ _ => ?_
  refine le_of_le_of_eq (key τ) ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end PositivityTheory.HtPt.Gf
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TrivflagNefFibre
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT

theorem trivflag_nef_fibre : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : Top.RootModel Ψ N) [CharZero M.Ω] (p : ℕ) [Fact p.Prime] (o : Type) [CommRing o] [Algebra o M.Ω] (ho : ∀ x : M.Ω, x ∈ (algebraMap o M.Ω).range ↔ ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : M.Ω) / (b : M.Ω)), (∀ τ, Num.TrivFlagMod o (p : o) M.y N (fun i => M.xdeg (τ, i))) → ∀ mu : Top.Wt Ψ N, Top.Dominant mu → M.NefAt p mu 0 :=
  @PositivityTheory.HtPt.Gf.trivflag_nef

end GlobalTheory.CompanionTheory.Ar.HT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootLinesWeightBoundOfFree
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles

namespace GlobalTheory.CompanionTheory.Ar.HT

def zpLocSubring (Ω : Type) [Field Ω] [CharZero Ω] (p : ℕ) [hp : Fact p.Prime] : Subring Ω where
  carrier := {x | ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : Ω) / (b : Ω)}
  mul_mem' := by
    rintro x y ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * a', b * b', ?_, ?_⟩
    · intro h; rcases hp.out.dvd_mul.1 h with h | h <;> contradiction
    · push_cast; rw [div_mul_div_comm]
  one_mem' := ⟨1, 1, hp.out.not_dvd_one, by simp⟩
  add_mem' := by
    rintro x y ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    have h0 : (b : Ω) ≠ 0 := by
      rintro h; exact hb (by rw [Nat.cast_eq_zero.1 h]; exact dvd_zero p)
    have h0' : (b' : Ω) ≠ 0 := by
      rintro h; exact hb' (by rw [Nat.cast_eq_zero.1 h]; exact dvd_zero p)
    refine ⟨a * b' + a' * b, b * b', ?_, ?_⟩
    · intro h; rcases hp.out.dvd_mul.1 h with h | h <;> contradiction
    · rw [div_add_div _ _ h0 h0']; push_cast; ring
  zero_mem' := ⟨0, 1, hp.out.not_dvd_one, by simp⟩
  neg_mem' := by
    rintro x ⟨a, b, hb, rfl⟩
    exact ⟨-a, b, hb, by push_cast; ring⟩

theorem rootModel_nefAt_of_hodgeCpt : FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [Fintype (CMType H)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω) (p : ℕ), p ∈ S → HTFree 𝔐 p → Fl.RootLines M.xdeg e → ∀ mu : Top.Wt (CMType H) (D.p + D.q), Top.Dominant mu → M.NefAt p mu 0 := by
  intro hF E _ _ _ H _ D l Xo c O _ β Y S M 𝔐 Fl e p hpS hfree hroot mu hmu
  rcases Nat.eq_zero_or_pos (D.p + D.q) with h0 | hpos
  · intro W _
    unfold Top.RootModel.curveDeg
    refine le_of_eq (Finset.sum_eq_zero fun j _ => ?_).symm
    cases j with
    | none => simp [Top.RootModel.coef]
    | some r => exact absurd r.2.2 (by omega)
  · haveI : Fact p.Prime := ⟨𝔐.S_prime p hpS⟩
    haveI : CharZero M.Ω := (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance
    let o := zpLocSubring M.Ω p
    letI : Algebra o M.Ω := o.subtype.toAlgebra
    have ho : ∀ x : M.Ω, x ∈ (algebraMap o M.Ω).range ↔
        ∃ (a : ℤ) (b : ℕ), ¬ p ∣ b ∧ x = (a : M.Ω) / (b : M.Ω) := by
      intro x
      change x ∈ o.subtype.range ↔ _
      rw [Subring.range_subtype]
      rfl
    have h1 := trivFlagMod_rootLines_model hF E H D l Xo c O β Y S M.Ω M.K M.ι M.y 𝔐 p hpS hpos o ho Fl
      M.xdeg e hfree hroot
    have hR := 𝔐.R_ge p hpS
    have h2 : ∀ τ, Num.TrivFlagMod o (p : o) M.y (D.p + D.q) (fun i => M.xdeg (τ, i)) := fun τ =>
      trivFlagMod_of_dvd o M.Ω M.K M.ι M.y _ _ _ _ (dvd_pow_self (p : o) (by omega)) (h1 τ)
    exact trivflag_nef_fibre (CMType H) (D.p + D.q) M p o ho h2 mu hmu

end GlobalTheory.CompanionTheory.Ar.HT
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootLinesWeightBoundOfFreeStatement
open CategoryTheory AlgebraicGeometry NumberField MvPolynomial GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_lines_weight_bound_of_free : FarguesHodgeTate → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [Fintype (CMType H)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (M : Top.RootModel (CMType H) (D.p + D.q)) (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (e : CMType H × Fin (D.p + D.q) → M.Ω) (p : ℕ), p ∈ S → HTFree 𝔐 p → Fl.RootLines M.xdeg e → ∀ mu : Top.Wt (CMType H) (D.p + D.q), Top.Dominant mu → M.NefAt p mu 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.rootModel_nefAt_of_hodgeCpt | exact GlobalTheory.CompanionTheory.Ar.HT.rootModel_nefAt_of_hodgeCpt | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.rootModel_nefAt_of_hodgeCpt <;> assumption)
end
