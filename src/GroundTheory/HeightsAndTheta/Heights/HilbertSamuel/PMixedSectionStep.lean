module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionMixed
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullSectionIntegral
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockCoeffCycle
public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeNull

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedSectionStep
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace MixedSectionInduction

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


open Classical in
theorem cycR_eq_finsum (I : Ideal (MRing ι) → (n : ℕ) → (Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) → ℝ) (P : Ideal (MRing ι)) {n : ℕ}
    (L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (s : MRing ι) :
    cycR I P L s = ∑ᶠ W : Ideal (MRing ι), (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s W : ℝ) *
      (if IsHorizontal W then I W n L else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W)) := by
  unfold cycR
  rw [finsum_mem_def]
  congr 1
  funext W
  by_cases hW : W ∈ divSupp P s
  · rw [Set.indicator_of_mem hW, GroundTheory.Heights₂.Heights.Inter.divCycle_apply_of_mem hW]
  · rw [Set.indicator_of_notMem hW, GroundTheory.Heights₂.Heights.Inter.divCycle_apply_of_not_mem hW]
    simp

end MixedSectionInduction


open MixedSectionInduction in
theorem MixedSectionStep.proof (hS : SmallSectionMixed.Statement) (hR : GroundTheory.Heights₂.Heights.Inter.RatR.Statement)
    (hI : IntegralAgainstPositive.Statement) (hK : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.KleimanNefIntersectionNonneg)
    (hE : ZCombExpand.Statement) : MixedSectionStep.Statement := by
  classical
  intro K _ ι _ P P0 d M H II hII hd hP hP0 hMs hMn hMc hMW hHa hHs hHb hHc hAt q p hp hpos
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  change MixedKleiman.AtDim n at hAt
  have hn : 1 ≤ n := by omega
  obtain ⟨m, f, g, hm, hfg, hdiv, hbd⟩ :=
    hS K ι P P0 (n + 1) M H p q II hII (by omega) hP hP0 hMs hMn hMc hHa hHs hHb hHc hp hpos
  have hMsm : IsSmoothHerm M := hMs.1
  have hHsm : IsSmoothHerm H := hHs.1
  let L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun j => if (j : ℕ) = 0 then M else HermLine.zcomb M H (q : ℤ) (p : ℤ)
  let F : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun j => if (j : ℕ) = 0 then M else HermLine.zcomb M H (q : ℤ) (p : ℤ)
  have hLsp : ∀ j, IsSemipositiveRel P0 P (L j) := fun j => by
    simp only [L]
    split_ifs
    · exact hMs
    · exact SmallSectionMixedAlt.isSemipositiveRel_zcomb hMs hHs q p
  have hFs : ∀ j, IsSmoothHerm (F j) := fun j => by
    simp only [F]
    split_ifs
    · exact hMsm
    · exact ZCombLimit.isSmoothHerm_zcomb_int hMsm hHsm _ _
  have hsnoc : ∀ X, Fin.snoc L X = Function.update F (Fin.last n) X := by
    intro X
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [Fin.snoc_last, Function.update_self]
    · rw [Fin.snoc_castSucc, Function.update_of_ne (Fin.castSucc_lt_last i).ne]
      rfl
  have hFN : Function.update F (Fin.last n) (HermLine.zcomb M H (q : ℤ) (p : ℤ)) = F := by
    funext j
    by_cases hj : j = Fin.last n
    · subst hj
      rw [Function.update_self]
      simp only [F, Fin.val_last]
      rw [if_neg (by omega)]
    · rw [Function.update_of_ne hj]

  have hscale : II K ι P (n + 1) (Fin.snoc L (HermLine.zcomb M H ((m * q : ℕ) : ℤ) ((m * p : ℕ) : ℤ))) =
      (m : ℝ) * II K ι P (n + 1) F := by
    have e1 := ZCombLimit.fam_update_zcomb_int (hII K ι) hP F hFs (Fin.last n) hMsm hHsm
      ((m * q : ℕ) : ℤ) ((m * p : ℕ) : ℤ)
    have e2 := ZCombLimit.fam_update_zcomb_int (hII K ι) hP F hFs (Fin.last n) hMsm hHsm (q : ℤ) (p : ℤ)
    rw [hFN] at e2
    rw [hsnoc, e1, e2]
    push_cast
    ring
  have hpts : ∀ {W : Ideal (MRing ι)}, P ≤ W → mcPts W ⊆ mcPts P := fun hPW z hz =>
    ⟨hz.1, fun f hf => hz.2 f (hPW hf)⟩
  have hchar : ∀ W W' : Ideal (MRing ι), W ≤ W' → charOf W ≠ 0 → charOf W' ≠ 0 := by
    intro W W' hle hW hW'
    apply hW
    unfold charOf at hW' ⊢
    rw [Int.natAbs_eq_zero, ← Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero] at hW' ⊢
    exact le_bot_iff.mp (hW' ▸ Ideal.comap_mono hle)
  obtain ⟨α, β, hfα, hgβ, hfP, hgP, hαβ⟩ := hfg

  have key : ∀ W ∈ divSupp P f, 0 ≤ (if IsHorizontal W then II K ι W n L
      else (geoNum n W (fun j => (L j).a) : ℝ) * Real.log (charOf W)) := by
    intro W hW
    obtain ⟨hH, hV⟩ := divSuppArith K ι P n
      (HermLine.ofMetrics (fun k => fsMetric (ι := ι k)) (fun k => (α k : ℤ))) f W hP ⟨α, fun _ => rfl, hfα, hfP⟩ hW
    have hPW : P ≤ W := le_trans le_sup_left hW.1.1.2
    split_ifs with hWh
    ·
      have hWv := hH hWh
      rw [(hE K ι (II K ι) (hII K ι) W n M H q p hWv hMsm hHsm).2 hn]
      refine Finset.sum_nonneg fun i hi => mul_nonneg (by positivity) ?_
      have hi' := Finset.mem_range.mp hi
      exact hAt K ι W P0 M H (fun _ => 1) II hII hn hWv (hP0.trans hPW)
        ⟨hMsm, fun z hz => hMs.2 z (hpts hPW hz)⟩ (fun W' h1 h2 => hMn W' h1 (hPW.trans h2)) hMc
        (fun W' h1 h2 => hMW W' h1 (hPW.trans h2)) (by rw [hHa]; funext k; simp)
        ⟨hHsm, fun z hz => hHs.2 z (hpts hPW hz)⟩ (fun z hz => hHb z (hpts hPW hz)) hHc (n - i) (by omega)
    ·
      by_cases hc : charOf W = 0
      · simp [hc]
      have hg : 0 ≤ geoNum n W (fun j => (L j).a) := by
        refine hK K ι W n _ (hV hWh).1 hc (hV hWh).2.2 fun j => ?_
        intro W' h1 h2 h3
        have hM' : 0 ≤ geoNum 1 W' (fun _ => M.a) := hMn W' h1 (hPW.trans h2) (hchar W W' h2 hc) h3
        simp only [L]
        split_ifs
        · exact hM'
        · show 0 ≤ geoNum 1 W' (fun _ => (q : ℤ) • M.a + (p : ℤ) • H.a)
          rw [ShiftedNefBig.geoNum_one_add]
          have hH' : 0 ≤ geoNum 1 W' (fun _ => (p : ℤ) • H.a) :=
            ProjLine.nefOnFibres_of_nonneg W' _ (fun k => by rw [hHa]; simp) W' h1 le_rfl
              (hchar W W' h2 hc) h3
          exact add_nonneg (mul_nonneg (Nat.cast_nonneg q) hM') hH'
      exact mul_nonneg (by exact_mod_cast hg) (Real.log_natCast_nonneg _)

  have hcyc : cycR (II K ι) P L g ≤ cycR (II K ι) P L f := by
    rw [cycR_eq_finsum, cycR_eq_finsum]
    refine finsum_le_finsum' ?_ ?_ fun W => ?_
    · exact Set.Finite.subset (Finsupp.hasFiniteSupport (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P g)) fun W hW h => hW (by simp [h])
    · exact Set.Finite.subset (Finsupp.hasFiniteSupport (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f)) fun W hW h => hW (by simp [h])
    · have hle : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P g W ≤ ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f W := hdiv W
      by_cases hW : W ∈ divSupp P f
      · exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hle) (key W hW)
      · have h0 : ReciprocityTheory.ChartRestriction.G.Geo.divCycle P f W = 0 := GroundTheory.Heights₂.Heights.Inter.divCycle_apply_of_not_mem hW
        rw [h0] at hle ⊢
        rw [Nat.le_zero.mp hle]

  have hint : ptsIntegral P (pot L)
      (logNormRat (HermLine.zcomb M H ((m * q : ℕ) : ℤ) ((m * p : ℕ) : ℤ)) f g) ≤ 0 := by
    refine hI K ι P P0 n L _ hP0 hLsp fun z hz => ?_
    have hpos := (HermLine.zcomb M H ((m * q : ℕ) : ℤ) ((m * p : ℕ) : ℤ)).pos z hz.1
    unfold logNormRat
    refine Real.log_nonpos (by positivity) ((div_le_one hpos).mpr ?_)
    by_cases hg0 : ‖eval z (map (Int.castRingHom ℂ) g)‖ = 0
    · rw [hg0, div_zero]
      exact hpos.le
    · rw [div_le_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hg0))]
      linarith [hbd z hz]
  have hNm : IsSmoothHerm (HermLine.zcomb M H ((m * q : ℕ) : ℤ) ((m * p : ℕ) : ℤ)) :=
    ZCombLimit.isSmoothHerm_zcomb_int hMsm hHsm _ _
  have hrec := hR K ι (II K ι) (hII K ι) P n L _ f g hP (fun j => (hLsp j).1) hNm
    ⟨α, β, hfα, hgβ, hfP, hgP, hαβ⟩
  rw [hscale] at hrec
  have hnn : 0 ≤ (m : ℝ) * II K ι P (n + 1) F := by
    rw [hrec]
    unfold recRRat
    linarith
  exact (mul_nonneg_iff_of_pos_left (by exact_mod_cast hm : (0 : ℝ) < m)).mp hnn

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLocIdealKer
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace LocIdealKer

variable {S : Type} [CommRing S] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
  {𝓜 : (K → ℤ) → Submodule S M}

def degProducts (𝓜 : (K → ℤ) → Submodule S M) (P : Ideal (MRingOver S ι)) (D : K → ℤ) : Set M :=
  {x | ∃ (p : MRingOver S ι) (b : K → ℕ) (n : M), p ∈ P ∧ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog p b ∧
    n ∈ 𝓜 (D - fun k => (b k : ℤ)) ∧ x = p • n}

theorem span_degProducts_le (h𝓜 : KH.IsMGraded S ι 𝓜) (P : Ideal (MRingOver S ι)) (D : K → ℤ) :
    Submodule.span S (degProducts 𝓜 P D) ≤ 𝓜 D := by
  rw [Submodule.span_le]
  rintro _ ⟨p, b, n, -, hp, hn, rfl⟩
  have := h𝓜.2 b _ p n hp hn
  rwa [sub_add_cancel] at this

theorem exists_near (h𝓜 : KH.IsMGraded S ι 𝓜) {P : Ideal (MRingOver S ι)} (hP : IsMultiHomogIdeal P)
    (D : K → ℤ) {x : M} (hx : x ∈ (P • ⊤ : Submodule (MRingOver S ι) M)) :
    ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), x - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j := by
  classical
  obtain ⟨G, hG, hPG⟩ := hP
  have hadd : ∀ x₁ x₂ : M,
      (∃ y ∈ Submodule.span S (degProducts 𝓜 P D), x₁ - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j) →
      (∃ y ∈ Submodule.span S (degProducts 𝓜 P D), x₂ - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j) →
      ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), x₁ + x₂ - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j := by
    rintro x₁ x₂ ⟨y₁, hy₁, e₁⟩ ⟨y₂, hy₂, e₂⟩
    refine ⟨y₁ + y₂, add_mem hy₁ hy₂, ?_⟩
    rw [add_sub_add_comm]
    exact add_mem e₁ e₂
  have hzero : ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), (0 : M) - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j :=
    ⟨0, zero_mem _, by rw [sub_zero]; exact zero_mem _⟩

  have hgen : ∀ g ∈ G, ∀ n : M,
      ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), g • n - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j := by
    intro g hg n
    obtain ⟨b, hb⟩ := hG g hg
    have hgP : g ∈ P := by rw [hPG]; exact Ideal.subset_span hg
    have hn : n ∈ ⨆ j, 𝓜 j := by
      rw [h𝓜.1.submodule_iSup_eq_top]
      exact Submodule.mem_top
    refine Submodule.iSup_induction (motive := fun n => ∃ y ∈ Submodule.span S (degProducts 𝓜 P D),
      g • n - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j) 𝓜 hn ?_ ?_ ?_
    · intro j n hn
      have hgn := h𝓜.2 b j g n hb hn
      by_cases hj : (j + fun k => (b k : ℤ)) = D
      · refine ⟨g • n, Submodule.subset_span ⟨g, b, n, hgP, hb, ?_, rfl⟩, ?_⟩
        · rw [← hj, add_sub_cancel_right]
          exact hn
        · rw [sub_self]
          exact zero_mem _
      · refine ⟨0, zero_mem _, ?_⟩
        rw [sub_zero]
        exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hj hgn)
    · rw [smul_zero]
      exact hzero
    · intro n₁ n₂ h₁ h₂
      rw [smul_add]
      exact hadd _ _ h₁ h₂

  have hP' : ∀ p ∈ P, ∀ n : M,
      ∃ y ∈ Submodule.span S (degProducts 𝓜 P D), p • n - y ∈ ⨆ (j) (_ : j ≠ D), 𝓜 j := by
    intro p hp
    rw [hPG] at hp
    induction hp using Submodule.span_induction with
    | mem g hg => exact hgen g hg
    | zero =>
      intro n
      rw [zero_smul]
      exact hzero
    | add p q _ _ hp hq =>
      intro n
      rw [add_smul]
      exact hadd _ _ (hp n) (hq n)
    | smul r p _ hp =>
      intro n
      rw [smul_eq_mul, mul_comm, mul_smul]
      exact hp (r • n)
  exact Submodule.smul_induction_on hx (fun p hp n _ => hP' p hp n) (fun x₁ x₂ h₁ h₂ => hadd _ _ h₁ h₂)

theorem mem_span_degProducts (h𝓜 : KH.IsMGraded S ι 𝓜) {P : Ideal (MRingOver S ι)} (hP : IsMultiHomogIdeal P)
    {D : K → ℤ} {x : M} (hx : x ∈ (P • ⊤ : Submodule (MRingOver S ι) M)) (hxD : x ∈ 𝓜 D) :
    x ∈ Submodule.span S (degProducts 𝓜 P D) := by
  obtain ⟨y, hy, hd⟩ := exists_near h𝓜 hP D hx
  have hc : x - y ∈ 𝓜 D := sub_mem hxD (span_degProducts_le h𝓜 P D hy)
  have h0 : x - y = 0 := Submodule.disjoint_def.mp (h𝓜.1.submodule_iSupIndep D) _ hc hd
  rw [sub_eq_zero] at h0
  rw [h0]
  exact hy

theorem proof : LocIdealKer.Statement := by
  intro S _ K _ ι _ M _ _ _ _ 𝓜 P T d h𝓜 hP hT w hw
  classical
  let _ : LinearOrder K := LinearOrder.lift' (Fintype.equivFin K) (Fintype.equivFin K).injective
  let _ : ∀ k, LinearOrder (ι k) := fun k =>
    LinearOrder.lift' (Fintype.equivFin (ι k)) (Fintype.equivFin (ι k)).injective
  set N := (P • ⊤ : Submodule (MRingOver S ι) M) with hN
  set L := IsLocalizedModule.map T (LocalizedModule.mkLinearMap T M)
    (LocalizedModule.mkLinearMap T (M ⧸ N)) N.mkQ with hL
  have hLmk : ∀ (m : M) (t : T), L (LocalizedModule.mk m t) = LocalizedModule.mk (N.mkQ m) t := by
    intro m t
    rw [hL, IsLocalizedModule.mk_eq_mk', IsLocalizedModule.map_mk', ← IsLocalizedModule.mk_eq_mk']
  constructor
  ·
    have hkill : ∀ p ∈ P, ∀ z : LocalizedModule T (M ⧸ N), p • z = 0 := by
      intro p hp z
      induction z using LocalizedModule.induction_on with
      | h q t =>
        obtain ⟨n, rfl⟩ := Submodule.mkQ_surjective N q
        rw [LocalizedModule.smul'_mk, ← map_smul, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero N).2
          (Submodule.smul_mem_smul hp Submodule.mem_top), LocalizedModule.zero_mk]
    intro hwP
    clear hw
    induction hwP using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, a, y, hp, -, -, rfl⟩ := hx
      rw [map_smul]
      exact hkill p hp _
    | zero => exact map_zero L
    | add x y _ _ hx hy => rw [map_add (f := _), hx, hy, add_zero]
    | smul s x _ hx =>
      rw [← algebraMap_smul (MRingOver S ι) s x, map_smul, hx, smul_zero]
  · intro h0
    obtain ⟨m, t, a, ht, hm, rfl⟩ := GenSESStep.locPart_normal h𝓜 hw
    rw [hLmk, ← LocalizedModule.zero_mk (1 : T), LocalizedModule.mk_eq] at h0
    obtain ⟨u, hu⟩ := h0
    rw [one_smul, smul_zero, smul_zero, Submonoid.smul_def, ← map_smul, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero] at hu
    obtain ⟨e, he⟩ := hT u u.2
    set D : K → ℤ := (d + fun k => (a k : ℤ)) + fun k => (e k : ℤ) with hD
    have humD : (u : MRingOver S ι) • m ∈ 𝓜 D := h𝓜.2 e _ _ m he hm
    have hspan := mem_span_degProducts h𝓜 hP hu humD
    have hut : ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog ((u * t : T) : MRingOver S ι) (e + a) := GenSESStep.isMultiHomog_mul he ht
    rw [← LocalizedModule.mk_cancel_common_left u t m, Submonoid.smul_def]
    generalize (u : MRingOver S ι) • m = x at hspan ⊢
    induction hspan using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, b, n, hp, hpb, hn, rfl⟩ := hx
      rw [← LocalizedModule.smul'_mk]
      refine Submodule.subset_span ⟨p, b, _, hp, hpb, GenSESStep.mk_mem_locPart n (u * t) (e + a) hut ?_, rfl⟩
      have edeg : ((d - fun k => (b k : ℤ)) + fun k => ((e + a) k : ℤ)) = D - fun k => (b k : ℤ) := by
        funext k
        simp only [hD, Pi.add_apply, Pi.sub_apply, Nat.cast_add]
        ring
      rw [edeg]
      exact hn
    | zero =>
      rw [LocalizedModule.zero_mk]
      exact zero_mem _
    | add x y _ _ hx hy =>
      rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_add, ← IsLocalizedModule.mk_eq_mk',
        ← IsLocalizedModule.mk_eq_mk']
      exact add_mem hx hy
    | smul s x _ hx =>
      rw [← LocalizedModule.smul'_mk]
      exact Submodule.smul_mem _ s hx

end LocIdealKer

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockHorizDiv
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace TwoBlockHorizDiv

section Local

variable {R : Type*} [CommRing R]

theorem length_loc_eq (W : Ideal R) [W.IsPrime] {J₁ J₂ : Ideal R} (h : J₁ ≤ J₂) {t : R} (ht : t ∉ W)
    (htJ : ∀ a ∈ J₂, t * a ∈ J₁) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J₁)) =
      Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl (R ⧸ J₂)) := by
  let q : (R ⧸ J₁) →ₗ[R] (R ⧸ J₂) := Submodule.factor h
  let φ := IsLocalizedModule.mapExtendScalars W.primeCompl (LocalizedModule.mkLinearMap W.primeCompl (R ⧸ J₁))
    (LocalizedModule.mkLinearMap W.primeCompl (R ⧸ J₂)) (Localization.AtPrime W) q
  have hsurj : Function.Surjective φ :=
    IsLocalizedModule.map_surjective W.primeCompl _ _ q (Submodule.factor_surjective h)
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    induction y using LocalizedModule.induction_on with
    | h m s =>
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      have h0 : LocalizedModule.mk (q (Submodule.Quotient.mk a)) s = 0 := by
        rw [← hy]
        exact (IsLocalizedModule.map_LocalizedModules W.primeCompl q _ s).symm
      rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.mk'_eq_zero'] at h0 ⊢
      obtain ⟨u, hu⟩ := h0
      refine ⟨⟨t, ht⟩ * u, ?_⟩
      change u • (Submodule.Quotient.mk a : R ⧸ J₂) = 0 at hu
      rw [Submonoid.smul_def, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul] at hu ⊢
      have := htJ _ hu
      simpa [mul_assoc] using this
  exact (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).length_eq

theorem multAt_eq_of_mul {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
    (W : Ideal (MRingOver R ι)) [W.IsPrime] {J₁ J₂ : Ideal (MRingOver R ι)} {t₁ t₂ : MRingOver R ι} (h₁ : t₁ ∉ W)
    (h₂ : t₂ ∉ W) (hJ₁ : ∀ a ∈ J₂, t₁ * a ∈ J₁) (hJ₂ : ∀ a ∈ J₁, t₂ * a ∈ J₂) : multAt J₁ W = multAt J₂ W := by
  have e₁ := length_loc_eq W (le_sup_left : J₁ ≤ J₁ ⊔ J₂) h₁ fun a ha => by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp ha
    rw [mul_add]
    exact J₁.add_mem (J₁.mul_mem_left _ hy) (hJ₁ z hz)
  have e₂ := length_loc_eq W (le_sup_right : J₂ ≤ J₁ ⊔ J₂) h₂ fun a ha => by
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp ha
    rw [mul_add]
    exact J₂.add_mem (hJ₂ y hy) (J₂.mul_mem_left _ hz)
  unfold multAt
  rw [dite_eq_left ‹W.IsPrime›, dite_eq_left ‹W.IsPrime›, e₁, e₂]

theorem mem_minimalPrimes_iff {I₁ I₂ W : Ideal R}
    (h : ∀ Q : Ideal R, Q.IsPrime → Q ≤ W → (I₁ ≤ Q ↔ I₂ ≤ Q)) :
    W ∈ I₁.minimalPrimes ↔ W ∈ I₂.minimalPrimes := by
  have key : ∀ {I₁ I₂ : Ideal R}, (∀ Q : Ideal R, Q.IsPrime → Q ≤ W → (I₁ ≤ Q ↔ I₂ ≤ Q)) →
      W ∈ I₁.minimalPrimes → W ∈ I₂.minimalPrimes := by
    intro I₁ I₂ h hW
    refine ⟨⟨hW.1.1, (h W hW.1.1 le_rfl).1 hW.1.2⟩, fun Q hQ hQW => hW.2 ⟨hQ.1, (h Q hQ.1 hQW).2 hQ.2⟩ hQW⟩
  exact ⟨key h, key fun Q hQ hQW => (h Q hQ hQW).symm⟩

end Local

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem rel_mem' {x x' : Ix κ → Ω} {c : κ} {l : Ix κ → ℤ} (hl : x ⟨(), c⟩ = ∑ j, (l j : Ω) * x' j)
    (k : Ix κ) (n : Ix κ → ℤ) (hn : ∑ j, (n j : Ω) * x' j = x k) :
    X ⟨0, k.2⟩ * twoBlockNum l - X ⟨0, c⟩ * ∑ j : Ix κ, C (n j) * X ⟨1, j.2⟩ ∈ twoBlockIdeal x x' := by
  show mConeMap (pair x x') _ = 0
  rw [map_sub, map_mul, map_mul, TwoBlockCoeffCycle.mConeMap_X, TwoBlockCoeffCycle.mConeMap_X, twoBlockNum,
    TwoBlockCoeffCycle.mConeMap_lin, TwoBlockCoeffCycle.mConeMap_lin]
  simp only [TwoBlockCoeffCycle.pair_one, TwoBlockCoeffCycle.pair_zero', ← hl, hn]
  ring

theorem intCast_not_mem {ι : Fin 2 → Type} [∀ k, Fintype (ι k)] {Q : Ideal (MRing ι)} (hQ : IsHorizontal Q) {d : ℤ}
    (hd : d ≠ 0) : (d : MRing ι) ∉ Q := by
  intro h
  have : d ∈ Q.comap (C : ℤ →+* MRing ι) := by
    rw [Ideal.mem_comap, eq_intCast]
    exact h
  rw [hQ, Ideal.mem_bot] at this
  exact hd this

theorem mul_mem_of_sup {R : Type*} [CommRing R] {P J : Ideal R} {s t : R} (hP : P ≤ J) (hs : t * s ∈ J) :
    ∀ a ∈ P ⊔ Ideal.span {s}, t * a ∈ J := by
  intro a ha
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp ha
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp hz
  rw [mul_add, mul_left_comm]
  exact J.add_mem (J.mul_mem_left _ (hP hy)) (J.mul_mem_left _ hs)

theorem den_rel {x : Ix κ → Ω} {B : Matrix (Ix κ) (Ix κ) ℚ} {c : κ} {l : Ix κ → ℤ}
    (hl : x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ j₀ : κ, (d : MRing (FinTwoTypeFamily κ)) * X ⟨0, c⟩ * X ⟨1, j₀⟩ ∈
      twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockNum l} := by
  obtain ⟨d, hd0, hdB⟩ := ChangeOfLattice.exists_clear_den B
  refine ⟨d, by exact_mod_cast hd0, fun j₀ => ?_⟩
  let j : Ix κ := ⟨(), j₀⟩
  choose N hN using hdB j
  have hNx : ∑ k, (N k : Ω) * x k = ((d : ℤ) : Ω) * matAct B x j := by
    simp only [matAct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : ((N k : ℚ) : Ω) = ((d : ℚ) : Ω) * ((B j k : ℚ) : Ω) := by rw [← hN k]; push_cast; ring
    push_cast at this ⊢
    rw [this]
    ring
  have hrel := TwoBlockCoeffCycle.rel_mem hl (d : ℤ) N j hNx
  have := Submodule.add_mem_sup hrel
    (Ideal.mul_mem_right (∑ k : Ix κ, C (N k) * X ⟨0, k.2⟩) _ (Ideal.mem_span_singleton_self (twoBlockNum l)))
  simpa using this

theorem num_rel {x : Ix κ → Ω} {B : Matrix (Ix κ) (Ix κ) ℚ} {c : κ} {l : Ix κ → ℤ}
    (hsp : Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)))
    (hl : x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j) (i₀ : κ) :
    X ⟨0, i₀⟩ * twoBlockNum l ∈ twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c} := by
  let k : Ix κ := ⟨(), i₀⟩
  have hk : x k ∈ Submodule.span ℤ (Set.range (matAct B x)) := hsp (Submodule.subset_span ⟨k, rfl⟩)
  obtain ⟨n, hn⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp hk
  have hn' : ∑ j, (n j : Ω) * matAct B x j = x k := by simpa [zsmul_eq_mul] using hn
  have hrel := rel_mem' hl k n hn'
  have := Submodule.add_mem_sup hrel
    (Ideal.mul_mem_right (∑ j : Ix κ, C (n j) * X ⟨1, j.2⟩) _ (Ideal.mem_span_singleton_self (twoBlockDen c)))
  simpa [twoBlockDen] using this

theorem sup_le_iff_of_horiz {x : Ix κ → Ω} {B : Matrix (Ix κ) (Ix κ) ℚ} {c : κ} {l : Ix κ → ℤ}
    (hsp : Submodule.span ℤ (Set.range x) ≤ Submodule.span ℤ (Set.range (matAct B x)))
    (hl : x ⟨(), c⟩ = ∑ j, (l j : Ω) * matAct B x j) {Q : Ideal (MRing (FinTwoTypeFamily κ))} (hQ : Q.IsPrime)
    (hH : IsHorizontal Q) (hR : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant Q) :
    twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockNum l} ≤ Q ↔
      twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c} ≤ Q := by
  obtain ⟨i₀, hi₀⟩ := hR 0
  obtain ⟨j₀, hj₀⟩ := hR 1
  obtain ⟨d, hd0, hd⟩ := den_rel (c := c) (l := l) hl
  constructor
  · intro h
    refine sup_le (le_sup_left.trans h) ((Ideal.span_singleton_le_iff_mem _).2 ?_)
    rcases hQ.mem_or_mem (h (hd j₀)) with h1 | h1
    · rcases hQ.mem_or_mem h1 with h2 | h2
      · exact absurd h2 (intCast_not_mem hH hd0)
      · exact h2
    · exact absurd h1 hj₀
  · intro h
    refine sup_le (le_sup_left.trans h) ((Ideal.span_singleton_le_iff_mem _).2 ?_)
    rcases hQ.mem_or_mem (h (num_rel hsp hl i₀)) with h1 | h1
    · exact absurd h1 hi₀
    · exact h1

end TwoBlockHorizDiv


open TwoBlockHorizDiv in
theorem TwoBlockHorizDiv.proof : TwoBlockHorizDiv.Statement := by
  intro Ω _ _ κ _ x B c l hsp hl W hW
  have hiff : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant W → ∀ Q : Ideal (MRing (FinTwoTypeFamily κ)), Q.IsPrime → Q ≤ W →
      (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockNum l} ≤ Q ↔
        twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c} ≤ Q) := by
    intro hr Q hQ hQW
    have hH : IsHorizontal Q := by
      unfold IsHorizontal at hW ⊢
      exact le_bot_iff.mp (hW ▸ Ideal.comap_mono hQW)
    have hR : ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant Q := fun k => (hr k).imp fun i hi h => hi (hQW h)
    exact sup_le_iff_of_horiz hsp hl hQ hH hR
  refine ⟨⟨fun ⟨hm, hr⟩ => ⟨(mem_minimalPrimes_iff (hiff hr)).1 hm, hr⟩,
    fun ⟨hm, hr⟩ => ⟨(mem_minimalPrimes_iff (hiff hr)).2 hm, hr⟩⟩, ?_⟩
  rintro ⟨hm, hr⟩
  have : W.IsPrime := hm.1.1
  obtain ⟨i₀, hi₀⟩ := hr 0
  obtain ⟨j₀, hj₀⟩ := hr 1
  obtain ⟨d, hd0, hd⟩ := den_rel (c := c) (l := l) hl
  refine multAt_eq_of_mul W (t₁ := (d : MRing (FinTwoTypeFamily κ)) * X ⟨1, j₀⟩) (t₂ := X ⟨0, i₀⟩) ?_ hi₀ ?_ ?_
  · intro h
    rcases Ideal.IsPrime.mem_or_mem ‹W.IsPrime› h with h1 | h1
    · exact intCast_not_mem hW hd0 h1
    · exact hj₀ h1
  · refine mul_mem_of_sup le_sup_left ?_
    have : (d : MRing (FinTwoTypeFamily κ)) * X ⟨1, j₀⟩ * twoBlockDen c = (d : MRing (FinTwoTypeFamily κ)) * X ⟨0, c⟩ * X ⟨1, j₀⟩ := by
      rw [twoBlockDen]; ring
    rw [this]
    exact hd j₀
  · exact mul_mem_of_sup le_sup_left (num_rel hsp hl i₀)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTranscRatioDeg
section -- merged from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.LinearIndependentAdjoinOfTranscendental
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

namespace TranscRatioDeg

open Polynomial

theorem transcendental_subfieldClosure {E : Type*} [Field E] {ι : Type*} (u : ι → E) (t : E)
    (ht : Transcendental (Algebra.adjoin ℤ (Set.range u)) t) :
    Transcendental (Subfield.closure (Set.range u)) t := by
  have hR : ∀ x, x ∈ Algebra.adjoin ℤ (Set.range u) ↔ x ∈ Subring.closure (Set.range u) := fun x => by
    rw [Algebra.adjoin_int]; rfl
  set R := Algebra.adjoin ℤ (Set.range u)
  set Q := Subfield.closure (Set.range u)
  have hmem : ∀ x : R, (x : E) ∈ Q := fun x => Subfield.subring_closure_le _ ((hR x).1 x.2)
  let _ : Algebra R Q := RingHom.toAlgebra
    { toFun := fun x => ⟨x.1, hmem x⟩, map_one' := rfl, map_mul' := fun _ _ => rfl,
      map_zero' := rfl, map_add' := fun _ _ => rfl }
  have : IsScalarTower R Q E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : FaithfulSMul R Q := (faithfulSMul_iff_algebraMap_injective R Q).2
    (fun a b h => Subtype.ext (congrArg Subtype.val h :))
  have : IsFractionRing R Q := IsFractionRing.of_field R Q (fun z => by
    obtain ⟨y, hy, z', hz', h⟩ := Subfield.mem_closure_iff.1 z.2
    exact ⟨⟨y, (hR y).2 hy⟩, ⟨z', (hR z').2 hz'⟩, Subtype.ext (by rw [Subfield.coe_div]; exact h.symm)⟩)
  intro halg
  exact ht ((IsFractionRing.isAlgebraic_iff R Q E).2 halg)

theorem transcendental_of_subfield {E : Type*} [Field E] {S : Type*} [CommRing S] [Algebra S E]
    (Q : Subfield E) (h : ∀ x : S, algebraMap S E x ∈ Q) (hinj : Function.Injective (algebraMap S E))
    {t : E} (ht : Transcendental Q t) : Transcendental S t := by
  rintro ⟨p, hp0, hp⟩
  let φ : S →+* Q := (algebraMap S E).codRestrict Q h
  have hφ : Function.Injective φ := fun a b hab => hinj (congrArg Subtype.val hab :)
  refine ht ⟨p.map φ, (Polynomial.map_ne_zero_iff hφ).2 hp0, ?_⟩
  rw [aeval_def, eval₂_map]
  exact hp


open scoped IntermediateField.algebraAdjoinAdjoin in
theorem linearIndependent_adjoin_of_transcendental {K E : Type*} [Field K] [Field E] [Algebra K E]
    (A : IntermediateField K E) {t : E} (ht : Transcendental A t) {κ : Type*} {b : κ → A}
    (hb : LinearIndependent K b) :
    LinearIndependent (IntermediateField.adjoin K {t}) (A.val ∘ b) :=
  open scoped IntermediateField.algebraAdjoinAdjoin in by
  letI : Algebra (Algebra.adjoin K {t}) (IntermediateField.adjoin K {t}) :=
    (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin K {t})).toAlgebra
  letI : FaithfulSMul (Algebra.adjoin K {t}) (IntermediateField.adjoin K {t}) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h =>
      Subtype.ext (by simpa using congrArg (fun x : IntermediateField.adjoin K {t} => (x : E)) h)
  letI : IsFractionRing (Algebra.adjoin K {t}) (IntermediateField.adjoin K {t}) :=
    IsFractionRing.of_field _ _ fun ⟨_, h⟩ =>
      have ⟨x, hx, y, hy, eq⟩ := IntermediateField.mem_adjoin_iff_div.mp h
      ⟨⟨x, hx⟩, ⟨y, hy⟩, Subtype.ext eq⟩
  letI : IsScalarTower (Algebra.adjoin K {t}) (IntermediateField.adjoin K {t}) E :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine (LinearIndependent.iff_fractionRing (Algebra.adjoin K {t})
    (IntermediateField.adjoin K {t})).1 ?_
  rw [linearIndependent_iff']
  intro s g hg i hi
  have hp : ∀ j, ∃ p : K[X], aeval t p = (g j : E) := fun j => by
    have h : (g j : E) ∈ (aeval t : K[X] →ₐ[K] E).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]
      exact (g j).2
    obtain ⟨p, hp⟩ := h
    exact ⟨p, hp⟩
  choose p hp using hp
  have hsum : ∑ j ∈ s, aeval t (p j) * (b j : E) = 0 := by
    simpa [hp, Subalgebra.smul_def] using hg
  let P : A[X] := ∑ j ∈ s, C (b j) * (p j).map (algebraMap K A)
  have hP : aeval t P = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [P, map_sum, map_mul, aeval_C, aeval_map_algebraMap]
    rw [← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    rfl
  have hP0 : P = 0 := by
    by_contra hne
    exact ht ⟨P, hne, hP⟩
  have hcoeff : ∀ n, ∑ j ∈ s, (p j).coeff n • b j = 0 := by
    intro n
    have := congrArg (fun q => q.coeff n) hP0
    simp only [P, finsetSum_coeff, coeff_C_mul, coeff_map, coeff_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Algebra.smul_def, mul_comm]
  have hpi : p i = 0 := by
    ext n
    exact linearIndependent_iff'.1 hb s (fun j => (p j).coeff n) (hcoeff n) i hi
  apply Subtype.ext
  rw [← hp i, hpi, map_zero]
  rfl

theorem finrank_adjoin_eq_of_transcendental {K E : Type*} [Field K] [Field E] [Algebra K E]
    (A : IntermediateField K E) {t : E} (ht : Transcendental A t) :
    Module.finrank (IntermediateField.adjoin K {t})
      (IntermediateField.adjoin (IntermediateField.adjoin K {t}) (A : Set E)) = Module.finrank K A := by
  set L := IntermediateField.adjoin K {t}
  let a := Module.Free.chooseBasis K A
  have hind : LinearIndependent L (A.val ∘ a) :=
    linearIndependent_adjoin_of_transcendental A ht a.linearIndependent
  by_cases hfin : Module.Finite K A
  · have H : A.LinearDisjoint L := IntermediateField.LinearDisjoint.of_basis_left a hind
    have hr := H.adjoin_rank_eq_rank_left_of_isAlgebraic_left
    exact congrArg Cardinal.toNat hr
  · rw [Module.finrank_of_not_finite hfin]
    set M := IntermediateField.adjoin L (A : Set E)
    letI : Module.Free L M := Module.Free.of_divisionRing L M
    refine Module.finrank_of_not_finite (M := M) ?_
    intro hfin'
    apply hfin
    let f : Module.Free.ChooseBasisIndex K A → M :=
      fun k => ⟨A.val (a k), IntermediateField.subset_adjoin L _ (a k).2⟩
    have hf : LinearIndependent L f := LinearIndependent.of_comp M.val.toLinearMap hind
    have : Finite (Module.Free.ChooseBasisIndex K A) := hf.finite
    exact Module.Finite.of_basis a

theorem finrank_adjoin_congr {E Φ L : Type*} [Field E] [Field Φ] [Field L] [Algebra Φ E] [Algebra L E]
    {S T : Set E} (h : (algebraMap Φ E).fieldRange = (algebraMap L E).fieldRange)
    (hST : Subfield.closure (Set.range (algebraMap Φ E) ∪ S) =
      Subfield.closure (Set.range (algebraMap L E) ∪ T)) :
    Module.finrank Φ (IntermediateField.adjoin Φ S) = Module.finrank L (IntermediateField.adjoin L T) := by
  let i : Φ ≃+* L := ((algebraMap Φ E).rangeRestrictFieldEquiv.trans (RingEquiv.subfieldCongr h)).trans
    (algebraMap L E).rangeRestrictFieldEquiv.symm
  have hi : ∀ r, algebraMap L E (i r) = algebraMap Φ E r := fun r => by
    simp only [i, RingEquiv.trans_apply, RingHom.rangeRestrictFieldEquiv_apply_symm_apply]
    rfl
  have hmem : ∀ x : E, x ∈ IntermediateField.adjoin Φ S ↔ x ∈ IntermediateField.adjoin L T := fun x => by
    rw [← IntermediateField.mem_toSubfield, ← IntermediateField.mem_toSubfield,
      IntermediateField.adjoin_toSubfield, IntermediateField.adjoin_toSubfield, hST]
  let j : IntermediateField.adjoin Φ S ≃+ IntermediateField.adjoin L T :=
    { toFun := fun x => ⟨x.1, (hmem x.1).1 x.2⟩, invFun := fun x => ⟨x.1, (hmem x.1).2 x.2⟩,
      left_inv := fun _ => rfl, right_inv := fun _ => rfl, map_add' := fun _ _ => rfl }
  have hr := rank_eq_of_equiv_equiv i j i.bijective (fun r m => Subtype.ext (by
    simp only [j, AddEquiv.coe_mk, Equiv.coe_fn_mk, Algebra.smul_def]
    rw [IntermediateField.coe_mul, IntermediateField.coe_mul]
    exact congrArg (· * (m : E)) (hi r).symm))
  exact congrArg Cardinal.toNat hr

end TranscRatioDeg

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

theorem TranscRatioDeg.proof : TranscRatioDeg.Statement := by
  intro ι E _ _ u D e w i₀ Φ _ _ hi₀ he hw ht hΦ
  have ht0 : w 0 ≠ 0 := by
    intro h0
    apply ht
    rw [h0]
    exact isAlgebraic_zero
  have hwk : ∀ k, w k = w 0 * (u (e k) / u (e 0)) := fun k => by
    rw [mul_div_assoc', ← hw k, mul_div_cancel_right₀ _ (he 0)]

  have hfn : ∀ {κ : Type} (v : κ → E) (K : Subfield E), (∀ i j, v i / v j ∈ K) →
      ∀ x ∈ fnField v, x ∈ K := by
    intro κ v K hK x hx
    have : (fnField v).toSubfield ≤ K := by
      unfold fnField
      rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
      rintro _ (⟨q, rfl⟩ | ⟨i, j, rfl⟩)
      · rw [eq_ratCast]
        exact SubfieldClass.ratCast_mem K q
      · exact hK i j
    exact this hx
  have hrat : ∀ i j, u i / u j ∈ fnField u := fun i j =>
    IntermediateField.subset_adjoin ℚ _ ⟨i, j, rfl⟩
  have hle : fnField (u ∘ e) ≤ fnField u := fun x hx =>
    hfn (u ∘ e) (fnField u).toSubfield (fun k l => hrat (e k) (e l)) x hx
  set F₀ := fnField (u ∘ e)
  set A := IntermediateField.extendScalars hle
  set L := IntermediateField.adjoin F₀ {w 0}

  have hL : ∀ x, x ∈ L ↔ x ∈ Subfield.closure (Set.range w) := by
    have h1 : L.toSubfield ≤ Subfield.closure (Set.range w) := by
      rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
      rintro _ (⟨⟨x, hx⟩, rfl⟩ | h)
      · refine hfn (u ∘ e) _ (fun k l => ?_) x hx
        have : (u ∘ e) k / (u ∘ e) l = w k / w l := by
          rw [hwk k, hwk l]
          field_simp [ht0, he 0, he l]
          simp only [Function.comp_apply]
          ring
        rw [this]
        exact div_mem (Subfield.subset_closure ⟨k, rfl⟩) (Subfield.subset_closure ⟨l, rfl⟩)
      · rw [Set.mem_singleton_iff.1 h]
        exact Subfield.subset_closure ⟨0, rfl⟩
    have h2 : Subfield.closure (Set.range w) ≤ L.toSubfield := by
      rw [Subfield.closure_le]
      rintro _ ⟨k, rfl⟩
      rw [hwk k]
      have hr : u (e k) / u (e 0) ∈ F₀ := IntermediateField.subset_adjoin ℚ _ ⟨k, 0, rfl⟩
      exact mul_mem (IntermediateField.mem_adjoin_simple_self F₀ (w 0))
        (IntermediateField.algebraMap_mem L (⟨_, hr⟩ : F₀))
    exact fun x => ⟨fun hx => h1 hx, fun hx => h2 hx⟩
  have hLset : Set.range (algebraMap L E) = (Subfield.closure (Set.range w) : Set E) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (hL _).1 y.2
    · intro hx
      exact ⟨⟨x, (hL x).2 hx⟩, rfl⟩

  have hQ : ∀ x ∈ fnField u, x ∈ Subfield.closure (Set.range u) := hfn u _ fun i j =>
    div_mem (Subfield.subset_closure ⟨i, rfl⟩) (Subfield.subset_closure ⟨j, rfl⟩)
  have htA : Transcendental A (w 0) :=
    TranscRatioDeg.transcendental_of_subfield (Subfield.closure (Set.range u)) (fun x => hQ _ x.2)
      (algebraMap A E).injective (TranscRatioDeg.transcendental_subfieldClosure u (w 0) ht)
  have key := TranscRatioDeg.finrank_adjoin_eq_of_transcendental A htA
  have hproj : projDeg u e = Module.finrank F₀ A := IntermediateField.relfinrank_eq_finrank_of_le hle
  rw [hproj, ← key]
  apply TranscRatioDeg.finrank_adjoin_congr
  · rw [hΦ]
    apply SetLike.ext'
    rw [RingHom.coe_fieldRange, hLset]
  · rw [← RingHom.coe_fieldRange, hΦ, hLset]
    apply le_antisymm
    · rw [Subfield.closure_le]
      rintro _ (h | ⟨i, rfl⟩)
      · exact Subfield.subset_closure (Or.inl h)
      · exact Subfield.subset_closure (Or.inr (hrat i i₀))
    · rw [Subfield.closure_le]
      rintro x (h | h)
      · exact Subfield.subset_closure (Or.inl h)
      · refine hfn u _ (fun i j => ?_) x h
        have : u i / u j = (u i / u i₀) / (u j / u i₀) := by
          rw [div_div_div_cancel_right₀ hi₀]
        rw [this]
        exact div_mem (Subfield.subset_closure (Or.inr ⟨i, rfl⟩))
          (Subfield.subset_closure (Or.inr ⟨j, rfl⟩))

end GroundTheory.Heights₂.Heights.HilbertSamuel
end
