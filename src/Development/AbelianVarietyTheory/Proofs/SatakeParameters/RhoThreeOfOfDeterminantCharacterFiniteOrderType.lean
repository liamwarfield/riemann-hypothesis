module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsComplexConjIsometryInertCompletion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoThreeOfOfDeterminantCharacterFiniteOrderType
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoThreeOfOfDeterminantCharacterFiniteOrderType
noncomputable section

namespace GlobalTheory.KerJ.RhoThree

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.Host GlobalTheory.KerJ NumberField Classical

theorem embT_mem (D : D7) (τ : D.what₂.Tau) (x : D.host.E) : embT D τ x ∈ Qbar := by
  have hx : IsAlgebraic ℚ x := Algebra.IsAlgebraic.isAlgebraic x
  have : IsAlgebraic ℚ ((embT D τ).toRatAlgHom x) := hx.algHom _
  exact (mem_algebraicClosure_iff).2 this

theorem norm_emb_unitary (D : D7) (φ : D.host.E →+* ℂ) (z : letI := D.host.cmStar; unitary D.host.E) :
    ‖φ (z : D.host.E)‖ = 1 := by
  let := D.host.cmStar
  have : IsCMField D.host.E := D.host.isCMField_hostE
  have h1 : star (z : D.host.E) * (z : D.host.E) = 1 := z.2.1
  have h2 : φ (star (z : D.host.E)) = starRingEnd ℂ (φ (z : D.host.E)) :=
    IsCMField.complexEmbedding_complexConj D.host.E φ _
  have h3 : starRingEnd ℂ (φ (z : D.host.E)) * φ (z : D.host.E) = 1 := by
    rw [← h2, ← map_mul, h1, map_one]
  have h4 : ‖φ (z : D.host.E)‖ * ‖φ (z : D.host.E)‖ = 1 := by
    have := congrArg norm h3
    rwa [norm_mul, RCLike.norm_conj, norm_one] at this
  nlinarith [norm_nonneg (φ (z : D.host.E))]

theorem algebraic_modulus_one_of_finiteOrder_char (D : D7) (ρ : D.Dt →* ℂˣ) (s : D.what₂.Tau → ℤ) (t : D.Dt) (h : ℕ)
    (z : letI := D.host.cmStar; unitary D.host.E) (hp : PowRat D t h z)
    (hU : ∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ ρ k ^ n = 1)
    (hz : ((ρ (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E)) ^ (s τ)) :
    Mod1E ((ρ t : ℂˣ) : ℂ) := by
  obtain ⟨h0, k, hk, e⟩ := hp
  obtain ⟨n, hn, h1⟩ := hU k hk
  have e1 : ρ t ^ (h * n) = ρ (D.e1Dt z) ^ n := by
    rw [pow_mul, ← map_pow, e, map_mul, mul_pow, h1, mul_one]
  have e2 : ((ρ t : ℂˣ) : ℂ) ^ (h * n) = (∏ τ, (embT D τ (z : D.host.E)) ^ (s τ)) ^ n := by
    rw [← hz, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, e1]
  have hpos : 0 < h * n := Nat.mul_pos h0 hn
  have hw : (∏ τ, (embT D τ (z : D.host.E)) ^ (s τ)) ∈ Qbar :=
    prod_mem fun τ _ => zpow_mem (embT_mem D τ _) _
  have hm : ((ρ t : ℂˣ) : ℂ) ∈ Qbar := by
    have h2 : ((ρ t : ℂˣ) : ℂ) ^ (h * n) ∈ Qbar := e2 ▸ pow_mem hw n
    exact (mem_algebraicClosure_iff).2 (((mem_algebraicClosure_iff).1 h2).of_pow hpos)
  refine ⟨hm, fun r => ?_⟩
  have e3 : (⟨((ρ t : ℂˣ) : ℂ), hm⟩ : Qbar) ^ (h * n) =
      (∏ τ, (⟨embT D τ (z : D.host.E), embT_mem D τ _⟩ : Qbar) ^ (s τ)) ^ n := by
    apply Subtype.ext
    push_cast
    exact e2
  have h3 : ‖r ⟨((ρ t : ℂˣ) : ℂ), hm⟩‖ ^ (h * n) = 1 := by
    rw [← norm_pow, ← map_pow, e3, map_pow, map_prod, norm_pow, norm_prod]
    rw [Finset.prod_eq_one, one_pow]
    intro τ _
    have h4 := norm_emb_unitary D (r.comp ((embT D τ).codRestrict Qbar (embT_mem D τ))) z
    rw [map_zpow₀, norm_zpow, show r ⟨embT D τ (z : D.host.E), embT_mem D τ _⟩ =
      (r.comp ((embT D τ).codRestrict Qbar (embT_mem D τ))) (z : D.host.E) from rfl, h4, one_zpow]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hpos.ne').1 h3

theorem zpow_hom_apply {G : Type*} [CommGroup G] (f : G →* ℂˣ) (a : ℤ) (x : G) : (f ^ a) x = f x ^ a :=
  map_zpow (MonoidHom.eval x) f a

theorem half_cast (R : Ranks) (j : ℕ) : (((R.N j / 2 : ℕ) : ℤ) : ℚ) = (R.N j : ℚ) / 2 := by
  obtain ⟨a, ha⟩ : Even (R.N j) := R.k_even.add (R.t_odd.add_one.mul_left j)
  have h1 : R.N j / 2 = a := by omega
  rw [h1, ha]
  push_cast
  ring

theorem prod_type {ι : Type*} [Fintype ι] (x : ι → ℂ) (hx : ∀ τ, x τ ≠ 0) (e : ι → ℤ) (b c : ℤ) :
    (∏ τ, x τ ^ e τ) ^ b * (∏ τ, (x τ)⁻¹) ^ c = ∏ τ, x τ ^ (b * e τ - c) := by
  rw [← Finset.prod_zpow, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← zpow_mul, inv_zpow, ← zpow_neg, mul_comm (e τ) b, sub_eq_add_neg, zpow_add₀ (hx τ)]

theorem emb_ne (D : D7) (τ : D.what₂.Tau) (z : letI := D.host.cmStar; unitary D.host.E) :
    embT D τ (z : D.host.E) ≠ 0 := by
  intro h0
  have := norm_emb_unitary D (embT D τ) z
  rw [h0, norm_zero] at this
  exact zero_ne_one this

theorem rhoThreeOf_of_mtType : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ),
    MtType u mt → rhoThreeOf D C mt := by
  intro D u C mt hT i hi
  obtain ⟨hU, e, he, hz⟩ := hT i hi
  have eS : ∀ τ, C.sSharp i τ = e τ - ((D.R.N (i + 1) / 2 : ℕ) : ℤ) := fun τ => by
    apply Int.cast_injective (α := ℚ)
    rw [C.sSharp_eq i hi τ, Int.cast_sub, he τ, half_cast]
    simp only [sExp']
  have eD : ∀ τ, C.sDiv i τ = e τ - ((D.R.N i / 2 : ℕ) : ℤ) := fun τ => by
    apply Int.cast_injective (α := ℚ)
    rw [C.sDiv_eq i hi τ, Int.cast_sub, he τ, half_cast]
    simp only [sExp, Nat.add_sub_cancel]
  have hk : ∀ k ∈ D.UO, rhoOf D mt i k = (mt (i + 1) k)⁻¹ ∧ rhoOf' D mt i k = mt (i + 1) k := fun k hk => by
    constructor
    · simp [rhoOf, zpow_hom_apply, D.chiD_UO k hk]
    · simp [rhoOf', zpow_hom_apply, D.chiD_UO k hk]
  have hV : ∀ z : (letI := D.host.cmStar; unitary D.host.E),
      ((rhoOf D mt i (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E)) ^ (-C.sSharp i τ) ∧
      ((rhoOf' D mt i (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E)) ^ (C.sDiv i τ) := fun z => by
    have hc : ((D.chiD (D.e1Dt z) : ℂˣ) : ℂ) = ∏ τ, (embT D τ (z : D.host.E))⁻¹ := D.rest_detCharacter_on_unitary_eq z
    constructor
    · have h1 := prod_type (fun τ => embT D τ (z : D.host.E)) (fun τ => emb_ne D τ z) e (-1)
        (-((D.R.N (i + 1) / 2 : ℕ) : ℤ))
      simp only [rhoOf, MonoidHom.mul_apply, zpow_hom_apply, Units.val_mul, Units.val_zpow_eq_zpow_val, MonoidHom.inv_apply,
        Units.val_inv_eq_inv_val, hc, hz z]
      rw [← zpow_neg_one, h1]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [eS τ]
      congr 1
      ring
    · have h1 := prod_type (fun τ => embT D τ (z : D.host.E)) (fun τ => emb_ne D τ z) e 1
        (((D.R.N i / 2 : ℕ) : ℤ))
      simp only [rhoOf', MonoidHom.mul_apply, zpow_hom_apply, Units.val_mul, Units.val_zpow_eq_zpow_val, hc, hz z]
      rw [← zpow_one (∏ τ, embT D τ (z : D.host.E) ^ e τ), h1]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [eD τ]
      congr 1
      ring
  have hU1 : ∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ rhoOf D mt i k ^ n = 1 := fun k hk' => by
    obtain ⟨n, hn, h1⟩ := hU k hk'
    exact ⟨n, hn, by rw [(hk k hk').1, inv_pow, h1, inv_one]⟩
  have hU2 : ∀ k ∈ D.UO, ∃ n : ℕ, 0 < n ∧ rhoOf' D mt i k ^ n = 1 := fun k hk' => by
    obtain ⟨n, hn, h1⟩ := hU k hk'
    exact ⟨n, hn, by rw [(hk k hk').2, h1]⟩
  refine ⟨fun t h z hp => ⟨algebraic_modulus_one_of_finiteOrder_char D _ _ t h z hp hU1 (hV z).1, algebraic_modulus_one_of_finiteOrder_char D _ _ t h z hp hU2 (hV z).2⟩, fun k hk' => ?_, hV⟩
  obtain ⟨n, hn, h1⟩ := hU k hk'
  exact ⟨n, hn, by rw [(hk k hk').1, inv_pow, h1, inv_one], by rw [(hk k hk').2, h1]⟩

end GlobalTheory.KerJ.RhoThree
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoThreeOfOfDeterminantCharacterFiniteOrderTypeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.Host GlobalTheory.KerJ NumberField Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rhoThreeOf_of_determinantCharacterFiniteOrderType : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ), MtType u mt → rhoThreeOf D C mt := by
  first | exact @GlobalTheory.KerJ.RhoThree.rhoThreeOf_of_mtType | exact GlobalTheory.KerJ.RhoThree.rhoThreeOf_of_mtType | (intros; apply GlobalTheory.KerJ.RhoThree.rhoThreeOf_of_mtType <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BTLeFiveQuarters
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.Ggeo

theorem bT_le_five_quarters {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (t : D.host.TT) :
    (L.bT t : ℝ) ≤ L.sc.b' + L.sc.b' / 4 := by
  have hx1 := L.sc.one_lt_alt
  have hx : 0 < L.sc.x := lt_trans one_pos hx1
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hx hb) (Real.exp_pos _)
  have hk : (0 : ℝ) < D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < D.R.k)
  have hLa : 0 ≤ L.LaG := by
    have h1 := P.S_le
    have h2 := L.Sc_pos
    have h3 : 0 < L.LaG * L.sc.b' / D.R.k := by linarith
    have h4 : 0 < L.LaG * L.sc.b' := (div_pos_iff_of_pos_right hk).1 h3
    exact ((mul_pos_iff_of_pos_right hb').1 h4).le
  have hr := P.rho_le
  have hx2 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by norm_num)
  have h5 : 0 ≤ P.Crho * Real.log L.sc.x * L.LaG / D.R.k :=
    div_nonneg (mul_nonneg (mul_nonneg P.Crho_pos.le (Real.log_nonneg hx1.le)) hLa) hk.le
  unfold LevelStarExponents.rhoP at hr
  have h6 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4 := by
    have : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
        4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
    linarith
  have h7 := P.bT_le t
  have h8 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
      (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
  have h9 := mul_le_mul_of_nonneg_right h6 hb'.le
  linarith

theorem wPl_windows : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (Fm.L x i).sc.w'' (Fm.D x i).R.n ≤ wPl (Fm.D x i) (j + 1) z ∧ wPl (Fm.D x i) (j + 1) z ≤ (Fm.L x i).sc.b + (Fm.L x i).etaSz + 1 ∧ (IsTopPl (Fm.D x i) z → (Fm.L x i).sc.b' ≤ wPl (Fm.D x i) (j + 1) z ∧ wPl (Fm.D x i) (j + 1) z ≤ 2 * (Fm.L x i).sc.b') := by
  intro eps Fm
  obtain ⟨x0, h0⟩ := GlobalTheory.T.scale_family_size_relations_eventually Fm
  refine ⟨x0, fun x hx hx1 i j hj z => ?_⟩
  obtain ⟨-, -, -, heta, hw, h4, h2b, -, -, -⟩ := h0 x hx hx1 i
  have P := Fm.params x hx1 i
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  have hxp : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hxp hb) (Real.exp_pos _)
  have he := L.etaSz_pos
  have hq : L.sc.b' / L.sc.x ≤ L.sc.b' / 4 := div_le_div_of_nonneg_left hb'.le (by norm_num) h4
  have hq0 : 0 < L.sc.b' / L.sc.x := div_pos hb' hxp
  have htop : ∀ (τ : D.what₂.Tau) (t : D.host.TT), (D.eTau τ : D.R.GG) = D.R.tau1 t →
      L.sc.b' ≤ wj D (j + 1) τ ∧ wj D (j + 1) τ ≤ 2 * L.sc.b' := by
    intro τ t ht
    obtain ⟨a1, a2⟩ := L.win_top (j + 1) (by omega) (by omega) τ t ht
    have a3 := L.bT_ge t
    have a4 := bT_le_five_quarters P t
    constructor <;> linarith
  unfold wPl
  refine ⟨?_, ?_, ?_⟩
  · by_cases h1 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.thickPlaces
    · have := (L.win_thick (j + 1) (by omega) (by omega) _ h1).1
      linarith
    by_cases h2 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht, e⟩ := Finset.mem_image.mp h2
      have := (htop _ ⟨t, ht⟩ e.symm).1
      linarith
    · exact (L.win_thin (j + 1) (by omega) (by omega) _ ⟨(D.eTau _).2, h2, h1⟩).1
  · by_cases h1 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.thickPlaces
    · exact (L.win_thick (j + 1) (by omega) (by omega) _ h1).2
    by_cases h2 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht, e⟩ := Finset.mem_image.mp h2
      have := (htop _ ⟨t, ht⟩ e.symm).2
      linarith
    · have := (L.win_thin (j + 1) (by omega) (by omega) _ ⟨(D.eTau _).2, h2, h1⟩).2
      linarith
  · rintro ⟨hz1, hz2⟩
    refine htop _ ⟨z.2, hz2⟩ ?_
    unfold tauPl
    rw [Equiv.apply_symm_apply]
    simp [plGG, hz1]

end GlobalTheory.Ggeo
end
