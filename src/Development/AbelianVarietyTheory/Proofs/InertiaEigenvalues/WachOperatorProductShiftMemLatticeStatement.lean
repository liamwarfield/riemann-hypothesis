module

public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsPrimOfGood
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsAdicCompleteOfLe
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VecPairApply

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachShiftMemOfExpansions
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiltLaurentProdPreserves
open PowerSeries

namespace GlobalTheory

theorem filtLaurent_prod_preserves {L : Type} [Field L] (D : Module.End L L⟦X⟧) (e : ℕ → L)
    (hD : ∀ (i : ℕ) (f : L⟦X⟧), X ^ i ∣ f → X ^ (i + 1) ∣ D f - e i • f)
    (c : ℤ → L) (xs : List ℤ) (i : ℕ) (f : L⟦X⟧) (hf : X ^ i ∣ f) :
    X ^ i ∣ Polynomial.aeval D
      (xs.map fun x => (Polynomial.X - Polynomial.C (c x) : Polynomial L)).prod f := by
  induction xs with
  | nil => simpa using hf
  | cons x xs ih =>
    rw [List.map_cons, List.prod_cons, map_mul, Module.End.mul_apply]
    set g := Polynomial.aeval D
      (xs.map fun x => (Polynomial.X - Polynomial.C (c x) : Polynomial L)).prod f
    have h1 : X ^ i ∣ D g - e i • g := (pow_dvd_pow X (Nat.le_succ i)).trans (hD i g ih)
    have h2 : Polynomial.aeval D (Polynomial.X - Polynomial.C (c x) : Polynomial L) g
        = (D g - e i • g) + (e i - c x) • g := by
      simp [sub_smul, Module.algebraMap_end_apply]
    rw [h2]
    exact dvd_add h1 (Dvd.dvd.trans ih ⟨PowerSeries.C (e i - c x), by
      rw [PowerSeries.smul_eq_C_mul, mul_comm]⟩)

theorem filtLaurent_prod_raises {L : Type} [Field L] (D : Module.End L L⟦X⟧) (c : ℤ → L) (K : ℤ)
    (hD : ∀ (i : ℕ) (f : L⟦X⟧), X ^ i ∣ f → X ^ (i + 1) ∣ D f - c (-(K + i)) • f)
    (n : ℕ) : ∀ (xs : List ℤ) (i : ℕ) (f : L⟦X⟧), X ^ i ∣ f →
      (∀ l : ℕ, i ≤ l → l < i + n → -(K + l) ∈ xs) →
      X ^ (i + n) ∣ Polynomial.aeval D
        (xs.map fun x => (Polynomial.X - Polynomial.C (c x) : Polynomial L)).prod f := by
  induction n with
  | zero => exact fun xs i f hf _ => filtLaurent_prod_preserves D _ hD c xs i f hf
  | succ n ih =>
    intro xs i f hf hxs
    have hx : -(K + i) ∈ xs := hxs i le_rfl (by omega)
    have hperm := ((List.perm_cons_erase hx).map
      fun x => (Polynomial.X - Polynomial.C (c x) : Polynomial L)).prod_eq
    rw [hperm, List.map_cons, List.prod_cons, mul_comm, map_mul, Module.End.mul_apply]
    have h2 : Polynomial.aeval D (Polynomial.X - Polynomial.C (c (-(K + i))) : Polynomial L) f
        = D f - c (-(K + i)) • f := by
      simp [Module.algebraMap_end_apply]
    rw [h2, show i + (n + 1) = (i + 1) + n by omega]
    refine ih _ (i + 1) _ (hD i f hf) fun l hl hl' => ?_
    exact (List.mem_erase_of_ne (by omega)).2 (hxs l (by omega) (by omega))

noncomputable def filtLaurentDiag {L : Type} [Field L] (w : ℕ → L) : Module.End L L⟦X⟧ where
  toFun f := PowerSeries.mk fun i => w i * coeff i f
  map_add' f g := by ext i; simp [mul_add]
  map_smul' a f := by ext i; simp [mul_left_comm]

theorem filtLaurent_triangular {L : Type} [Field L] (w : ℕ → L) (p : L⟦X⟧)
    (hp : constantCoeff p ≠ 0) (i : ℕ) (a : L) (ha : constantCoeff p * a = w i)
    (f : L⟦X⟧) (hf : X ^ i ∣ f) :
    X ^ (i + 1) ∣ (LinearMap.mulLeft L p⁻¹ ∘ₗ filtLaurentDiag w) f - a • f := by
  have h1 : (LinearMap.mulLeft L p⁻¹ ∘ₗ filtLaurentDiag w) f - a • f
      = p⁻¹ * (filtLaurentDiag w f - a • (p * f)) := by
    rw [mul_sub, mul_smul_comm, ← mul_assoc, PowerSeries.inv_mul_cancel _ hp, one_mul]
    rfl
  rw [h1]
  refine Dvd.dvd.mul_left ?_ _
  rw [X_pow_dvd_iff]
  intro l hl
  have hpf : X ^ i ∣ p * f := hf.mul_left p
  rcases Nat.lt_succ_iff_lt_or_eq.1 hl with h | rfl
  · simp [filtLaurentDiag, X_pow_dvd_iff.1 hf l h, X_pow_dvd_iff.1 hpf l h]
  · obtain ⟨g, rfl⟩ := hf
    have e1 : coeff l (X ^ l * g) = constantCoeff g := by
      simpa using coeff_X_pow_mul g l 0
    have e2 : coeff l (p * (X ^ l * g)) = constantCoeff p * constantCoeff g := by
      rw [mul_left_comm]
      simpa using coeff_X_pow_mul (p * g) l 0
    simp only [map_sub, filtLaurentDiag, LinearMap.coe_mk, AddHom.coe_mk, coeff_mk, map_smul,
      e1, e2, smul_eq_mul, ← ha]
    ring

theorem filtLaurent_shift_line : ∀ (L : Type) [Field L] (M : Type) [AddCommGroup M] [Module L M] (Fl : ℤ → Submodule L M), Antitone Fl → ∀ (u : Lˣ) (p : PowerSeries L) (c : ℤ → L), PowerSeries.constantCoeff p ≠ 0 → (∀ x : ℤ, PowerSeries.constantCoeff p * c x = ((u ^ (-x) : Lˣ) : L) - 1) → ∀ (y' Y : ℕ) (xs : List ℤ), (∀ (a : ℤ) (j : ℕ), Fl (a + 1) ≠ Fl a → y' < j → j ≤ Y → a + (j : ℤ) ∈ xs) → ∀ seq : ℕ → ℤ → M, (∀ m, ∃ k₀ : ℤ, ∀ k < k₀, seq m k = 0) → (∀ m < xs.length, ∀ k : ℤ, ∑ᶠ j : ℕ, PowerSeries.coeff j p • (seq (m + 1) (k - j) + c (xs.getD m 0) • seq m (k - j)) = (((u ^ k : Lˣ) : L) - 1) • seq m k) → (∀ k : ℤ, seq 0 k ∈ Fl (-k - Y)) → ∀ k : ℤ, seq xs.length k ∈ Fl (-k - y') := by
  intro L _ M _ _ Fl hFl u p c hp hc y' Y xs hxs seq hbd hrec h0 k
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro φ hφ
  rw [Submodule.mem_dualAnnihilator] at hφ
  choose k₀ hk₀ using hbd

  have core : ∀ (K : ℤ), (∀ m ≤ xs.length, K ≤ k₀ m) → ∀ i n : ℕ,
      (∀ l < i, φ (seq 0 (K + l)) = 0) → (∀ l : ℕ, i ≤ l → l < i + n → -(K + l) ∈ xs) →
      ∀ l < i + n, φ (seq xs.length (K + l)) = 0 := by
    intro K hK i n hi hn
    set w : ℕ → L := fun l => ((u ^ (K + l) : Lˣ) : L) - 1 with hw
    set D : Module.End L L⟦X⟧ := LinearMap.mulLeft L p⁻¹ ∘ₗ filtLaurentDiag w with hDdef
    set G : ℕ → L⟦X⟧ := fun m => PowerSeries.mk fun l => φ (seq m (K + l)) with hG
    have hstep : ∀ m < xs.length, G (m + 1) = D (G m) - c (xs.getD m 0) • G m := by
      intro m hm
      have key : p * (G (m + 1) + c (xs.getD m 0) • G m) = filtLaurentDiag w (G m) := by
        ext l
        have h1 := hrec m hm (K + l)
        rw [finsum_eq_sum_of_support_subset (s := Finset.range (l + 1))] at h1
        · have h2 := congrArg φ h1
          rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
            (fun a b => coeff a p * coeff b (G (m + 1) + c (xs.getD m 0) • G m))]
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, map_smul] at h2
          simp only [filtLaurentDiag, LinearMap.coe_mk, AddHom.coe_mk, coeff_mk, hG, hw]
          rw [← smul_eq_mul, ← h2]
          refine Finset.sum_congr rfl fun j hj => ?_
          have hj' : j ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
          have : K + ((l - j : ℕ) : ℤ) = K + l - j := by omega
          simp only [map_add (f := _), map_smul, coeff_mk, this, smul_eq_mul]
        · intro j hj
          by_contra hj'
          have hj'' : l + 1 ≤ j := by simpa using hj'
          have a1 := hK m hm.le
          have a2 := hK (m + 1) hm
          apply hj
          simp only
          rw [hk₀ (m + 1) _ (by omega), hk₀ m _ (by omega)]
          simp
      rw [eq_sub_iff_add_eq, hDdef, LinearMap.comp_apply, ← key, LinearMap.mulLeft_apply,
        ← mul_assoc, PowerSeries.inv_mul_cancel _ hp, one_mul]
    have hall : ∀ m ≤ xs.length, G m = Polynomial.aeval D
        ((xs.take m).map fun x => (Polynomial.X - Polynomial.C (c x) : Polynomial L)).prod
          (G 0) := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        intro hm
        have hm' : m < xs.length := hm
        rw [hstep m hm', List.take_succ_eq_append_getElem hm', List.map_append, List.prod_append,
          mul_comm, map_mul, Module.End.mul_apply, ← ih hm'.le, List.getD_eq_getElem _ _ hm']
        simp [Module.algebraMap_end_apply]
    have hfin := filtLaurent_prod_raises D c K (fun l f hf =>
      filtLaurent_triangular w p hp l _ (by rw [hc, neg_neg]) f hf) n xs i (G 0)
      (X_pow_dvd_iff.2 fun l hl => by simpa [hG] using hi l hl) hn
    have h3 := hall xs.length le_rfl
    rw [List.take_length] at h3
    rw [← h3] at hfin
    intro l hl
    simpa [hG] using X_pow_dvd_iff.1 hfin l hl
  obtain ⟨K₀, hK₀⟩ := ((Set.finite_le_nat xs.length).image k₀).bddBelow
  have hK₁ : ∀ m ≤ xs.length, K₀ ≤ k₀ m := fun m hm => hK₀ ⟨m, hm, rfl⟩
  by_cases hex : ∃ a : ℤ, ¬ ∀ v ∈ Fl a, φ v = 0
  · have hbdd : ∀ a : ℤ, (¬ ∀ v ∈ Fl a, φ v = 0) → a < -k - y' := by
      intro a ha
      by_contra h
      exact ha fun v hv => hφ v (hFl (not_lt.1 h) hv)
    obtain ⟨a, ha, hmax⟩ := Int.exists_greatest_of_bdd
      ⟨-k - y', fun a ha => (hbdd a ha).le⟩ hex
    have ha1 : ∀ v ∈ Fl (a + 1), φ v = 0 := by
      by_contra h
      have := hmax _ h
      omega
    have hjump : Fl (a + 1) ≠ Fl a := fun h => ha (h ▸ ha1)
    have hlt := hbdd a ha
    set K := min K₀ (min k (-a - Y)) with hK
    have := core K (fun m hm => (min_le_left _ _).trans (hK₁ m hm)) (-a - Y - K).toNat (Y - y')
      (fun l hl => ha1 _ (hFl (by omega) (h0 _)))
      (fun l hl hl' => by
        have := hxs a (-(K + l) - a).toNat hjump (by omega) (by omega)
        convert this using 1
        omega) (k - K).toNat (by omega)
    convert this using 3
    omega
  · push Not at hex
    set K := min K₀ k with hK
    have := core K (fun m hm => (min_le_left _ _).trans (hK₁ m hm)) ((k - K).toNat + 1) 0
      (fun l _ => hex _ _ (h0 _)) (fun l hl hl' => by omega) (k - K).toNat (by omega)
    convert this using 3
    omega

end GlobalTheory
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace GlobalTheory

section Core

open TensorProduct Formalism.MainNotions.RamifiedCoefficientChains.Sh Formalism.MainNotions.N.Pv.LocalLengthBound.Ser Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt
open Formalism.MainNotions.CrystallineLiftingInputs (DL)
open Formalism.MainNotions.LiftingTheory (qp)
open Formalism.MainNotions.WachCoordinates (FilLev)

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem wachExp_diag_shift_iff {M : Type} [AddCommGroup M] [Module LL M] {Fl : ℤ → Submodule LL M}
    (hF : Antitone Fl) {m : ℤ} {d : ℤ → M} (hd : ∀ k < m, d k = 0) (u : PowerSeries LL)
    (hu : IsUnit u) (y : ℕ) :
    (∀ k, conv ((u * PowerSeries.X) ^ y) d k ∈ Fl (-k)) ↔ ∀ k, d k ∈ Fl (-k - y) := by
  have hd' : LB m d := hd
  have hu0 : PowerSeries.constantCoeff (u ^ y) ≠ 0 :=
    ((hu.pow y).map PowerSeries.constantCoeff).ne_zero
  have e : conv ((u * PowerSeries.X) ^ y) d = fun k => smulS (u ^ y) d (k - y) := by
    show smulS ((u * PowerSeries.X) ^ y) d = _
    rw [mul_comm, mul_pow, smulS_mul hd', smulS_X_pow (LB_smulS hd' _)]
  rw [e]
  constructor
  · intro h k
    have h1 : Dg Fl (-(y : ℤ)) (smulS (u ^ y) d) := fun j => by
      have := h (j + y)
      simp only [add_sub_cancel_right] at this
      rwa [show -(y : ℤ) - j = -(j + y) by ring]
    have h2 := Dg_smulS hF (LB_smulS hd' _) h1 (u ^ y)⁻¹ k
    rw [smulS_inv hd' _ hu0] at h2
    rwa [show -k - (y : ℤ) = -(y : ℤ) - k by ring]
  · intro h k
    have h1 : Dg Fl (-(y : ℤ)) d := fun j => by
      rw [show -(y : ℤ) - j = -j - y by ring]; exact h j
    have h2 := Dg_smulS hF hd' h1 (u ^ y) (k - y)
    rwa [show -(y : ℤ) - (k - y) = -k by ring] at h2

theorem wachExp_mem_iff (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hRg : ExpRing W)
    (hRu : ExpRules W) (hCr : ExpCrit W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) (i : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (x : W.DD T) (d : ℤ → T.V ⊗[Qp] BdR) (hx : DL W T i x) (hd : IsExp W T i ζ x d)
    (Y : ℕ) (hY : qp W ^ Y • x ∈ W.N T) (y : ℕ) :
    qp W ^ y • x ∈ W.N T ↔ ∀ k, d k ∈ FilLev W T i 0 (-k - y) := by
  have hK : Module.finrank K₀ K = 1 := Formalism.MainNotions.UnusedSlot80.SatW.finrank_one_of_bij' hA.1
  obtain ⟨h9r, -⟩ := (h9 T hT hA.2.1 hA.2.2).2.2 hK
  have hR := Formalism.MainNotions.LiftingTheory.lifta_ring_of W h9r
  have hqΔ := Formalism.MainNotions.LiftingTheory.lifta_qΔ W hR.πΔ
  have hDL : DL W T i (qp W ^ y • x) := by
    refine ⟨by rw [smul_comm, hx.1], fun δ hδ => ?_⟩
    rw [γD_smul', map_pow, hqΔ δ hδ, hx.2 δ hδ]
  obtain ⟨⟨u, hu, hq⟩, -, -⟩ := hRg hA i ζ hζ
  have hE := (hRu hA T hT i ζ hζ).2.2.2.2.1 (qp W ^ y) x d hd
  have hN : qp W ^ Y • (qp W ^ y • x) ∈ W.N T := by
    rw [smul_comm]; exact (W.N T).smul_mem _ hY
  rw [(hCr hA T hT i ζ hζ _ _ hDL hE).1 ⟨Y, hN⟩, map_pow, hq]
  obtain ⟨m, hm⟩ := hd.1
  exact wachExp_diag_shift_iff (Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T i 0) hm u hu y

theorem wachShift_mem_of_exp [NeZero n] (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hRg : ExpRing W) (hRu : ExpRules W) (hCr : ExpCrit W) (hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL)
    (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (hp : (PD.p : LL) ≠ 0) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) (i : ZMod n) (y' Y : ℕ) (cO : ℤ → O)
    (hc : ∀ x : ℤ, ((PD.p : ℕ) : O) * cO x = 1 - (((W.χΓ W.gam) ^ (-x) : Oˣ) : O))
    (xs : List ℤ)
    (hxs : ∀ (τ : K →ₐ[Qp] LL) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over W τ i → IsJumpV PD T.ρ τ a →
      y' < j → j ≤ Y → a + (j : ℤ) ∈ xs)
    (seq : ℕ → W.DD T) (h0 : DL W T i (seq 0)) (h0N : qp W ^ Y • seq 0 ∈ W.N T)
    (hrec : ∀ k < xs.length, W.π₀ • (seq (k + 1) + cO (xs.getD k 0) • seq k) =
      W.γD T W.gam (seq k) - seq k) :
    DL W T i (seq xs.length) ∧ qp W ^ y' • seq xs.length ∈ W.N T := by
  classical
  have hU := Formalism.MainNotions.UnusedSlot35.DssRec.π₀_unit W h9 hA T hT
  have hDS := rToolMod_dStab W h9
  have hQ : ∀ k ≤ xs.length, QLattice W T i Y (seq k) := by
    intro k
    induction k with
    | zero => exact fun _ => ⟨h0, h0N⟩
    | succ k ih =>
      intro hk
      have hk' : k < xs.length := hk
      have e : seq (k + 1) = derivationOnWachModule W T (seq k) + (-cO (xs.getD k 0)) • seq k := by
        have h1 : seq (k + 1) + cO (xs.getD k 0) • seq k = derivationOnWachModule W T (seq k) :=
          Formalism.MainNotions.UnusedSlot35.DssRec.smul_inj W.π₀ hU (by rw [hrec k hk', uniformizer_smul_derivation W T hU]; rfl)
        rw [← h1, neg_smul, add_neg_cancel_right]
      rw [e]
      exact qLattice_add W T (qLattice_derivation W T hDS hA hT i Y (ih hk'.le))
        (qLattice_smul W T _ (ih hk'.le))
  refine ⟨(hQ _ le_rfl).1, ?_⟩
  obtain ⟨⟨u, hu, hq⟩, hπ0, -⟩ := hRg hA i ζ hζ
  obtain ⟨hex, -, hadd, hsO, hsA, hγ, -⟩ := hRu hA T hT i ζ hζ
  have hqne : W.lev i ζ (qp W ^ Y) ≠ 0 := by
    rw [map_pow, hq]
    exact pow_ne_zero _ (mul_ne_zero hu.ne_zero PowerSeries.X_ne_zero)
  have hf : ∀ k : ℕ, ∃ d : ℤ → T.V ⊗[Qp] BdR, (∃ m : ℤ, ∀ j < m, d j = 0) ∧
      (k ≤ xs.length → IsExp W T i ζ (seq k) d) := by
    intro k
    by_cases hk : k ≤ xs.length
    · obtain ⟨d, hd, -⟩ := hex (seq k) _ (hQ k hk).2 hqne
      exact ⟨d, hd.1, fun _ => hd⟩
    · exact ⟨0, ⟨0, fun _ _ => rfl⟩, fun h => absurd h hk⟩
  choose f hfb hfe using hf
  rw [wachExp_mem_iff W h9 hRg hRu hCr hA T hT i ζ hζ _ _ (hQ _ le_rfl).1 (hfe _ le_rfl) Y
    (hQ _ le_rfl).2 y']
  have hf0 := (wachExp_mem_iff W h9 hRg hRu hCr hA T hT i ζ hζ _ _ h0 (hfe 0 (Nat.zero_le _)) Y
    h0N Y).1 h0N
  let uL : LLˣ := Units.map (algebraMap O LL : O →* LL) (W.χΓ W.gam)
  refine filtLaurent_shift_line LL _ (fun a => FilLev W T i 0 a)
    (Formalism.MainNotions.UnusedSlot80.LevR.filLev_anti W T i 0) uL (W.lev i ζ W.π₀) (fun x => algebraMap O LL (cO x))
    (by rw [hπ0]; exact neg_ne_zero.2 hp) (fun x => ?_) y' Y xs (fun a j ha hj hj' => ?_) f hfb
    (fun m hm k => ?_) hf0
  · have h1 := congrArg (algebraMap O LL) (hc x)
    rw [map_mul, map_natCast, map_sub, map_one] at h1
    have h2 : ((uL ^ (-x) : LLˣ) : LL) = algebraMap O LL (((W.χΓ W.gam) ^ (-x) : Oˣ) : O) := by
      rw [← map_zpow]; rfl
    rw [hπ0, h2]
    linear_combination -h1
  · let e : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hA.1
    let τ : K →ₐ[Qp] LL := (W.emb i).comp e.symm.toAlgHom
    have hτ : Formalism.MainNotions.LiftingTheory.Over W τ i := by
      apply AlgHom.ext
      intro z
      show W.emb i (e.symm (e z)) = W.emb i z
      rw [e.symm_apply_apply]
    have hF : ∀ b : ℤ, FildR PD T.ρ τ b = FilLev W T i 0 b := by
      intro b
      rw [((hD hA.1 T.V T.ρ hT).2 τ).2.2 b, show τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = W.emb i from hτ]
      unfold FilLev
      simp only [Nat.cast_zero, sub_zero, pow_zero, Module.End.one_eq_id, Submodule.map_id]
    refine hxs τ a j hτ ?_ hj hj'
    unfold IsJumpV
    rw [hF, hF]
    exact ha
  · have e1 := hfe m hm.le
    have e2 := hfe (m + 1) hm
    have hL := hsA W.π₀ _ _ (hadd _ _ _ _ e2 (hsO (cO (xs.getD m 0)) _ _ e1))
    have hR := hadd _ _ _ _ (hγ _ _ e1) (hsO (-1) _ _ e1)
    have ex : W.γ T (seq m) + (-1 : O) • seq m =
        W.π₀ • (seq (m + 1) + cO (xs.getD m 0) • seq m) := by
      rw [hrec m hm, neg_one_smul, ← sub_eq_add_neg]; rfl
    rw [ex] at hR
    have hN : qp W ^ Y • (W.π₀ • (seq (m + 1) + cO (xs.getD m 0) • seq m)) ∈ W.N T := by
      rw [smul_comm]
      exact (W.N T).smul_mem _
        (qLattice_add W T (hQ (m + 1) hm) (qLattice_smul W T _ (hQ m hm.le))).2
    have h3 := congrFun ((hex _ _ hN hqne).unique hL hR) k
    have h2 : ((uL ^ k : LLˣ) : LL) = (algebraMap O LL (W.χΓ W.gam : O)) ^ k := by
      rw [Units.val_zpow_eq_zpow_val]; rfl
    rw [h2, sub_smul, one_smul]
    refine Eq.trans ?_ (h3.trans ?_)
    · rfl
    · simp [sub_eq_add_neg]

end Core

set_option synthInstance.maxHeartbeats 100000 in
theorem wachShift_mem_of_expansions : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc), ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL), Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hA.2.2) → Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing ((HW l).W K 1 LL hA.2.2) → Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules ((HW l).W K 1 LL hA.2.2) → Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit ((HW l).W K 1 LL hA.2.2) → Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris ((D.loc l).PD K) ↥LL.1 → ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (y' Y : ℕ) (cO : ℤ → ↥(OL LL)), (∀ x : ℤ, ((l : ℕ) : ↥(OL LL)) * cO x = 1 - (((((HW l).W K 1 LL hA.2.2).χΓ ((HW l).W K 1 LL hA.2.2).gam) ^ (-x) : (↥(OL LL))ˣ) : ↥(OL LL))) → ∀ xs : List ℤ, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over ((HW l).W K 1 LL hA.2.2) τ i → IsJumpV ((D.loc l).PD K) T.ρ τ a → y' < j → j ≤ Y → a + (j : ℤ) ∈ xs) → ∀ seq : ℕ → ((HW l).W K 1 LL hA.2.2).DD T, Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL hA.2.2) T i (seq 0) → Formalism.MainNotions.LiftingTheory.qp ((HW l).W K 1 LL hA.2.2) ^ Y • seq 0 ∈ ((HW l).W K 1 LL hA.2.2).N T → (∀ k < xs.length, ((HW l).W K 1 LL hA.2.2).π₀ • (seq (k + 1) + cO (xs.getD k 0) • seq k) = ((HW l).W K 1 LL hA.2.2).γD T ((HW l).W K 1 LL hA.2.2).gam (seq k) - seq k) → Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL hA.2.2) T i (seq xs.length) ∧ Formalism.MainNotions.LiftingTheory.qp ((HW l).W K 1 LL hA.2.2) ^ y' • seq xs.length ∈ ((HW l).W K 1 LL hA.2.2).N T := by
  intro D HW l _ K LL hA h9 hRg hRu hCr hD T hT i y' Y cO hc xs hxs seq h0 h0N hrec
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  haveI : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨ζ, hζ⟩ := Formalism.MainNotions.UnusedSlot80.exists_prim_of_good D hA.2.2
  refine wachShift_mem_of_exp _ h9 hRg hRu hCr hD
    (Formalism.MainNotions.UnusedSlot80.caseA_of_le_Kur_of_ne_two (D.loc l) (HW l) hA.2.2 hA.1 hA.2.1) ?_ ζ (by rw [hp]; exact hζ) T hT i y' Y
    cO (fun x => by rw [hp]; exact hc x) xs hxs seq h0 h0N hrec
  rw [hp]
  exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpansionRulesCriterionOddRootOfUnityCaseA
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPointOverLetter
noncomputable section
open Classical

namespace GlobalTheory.LevelClauseOdd

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem exists_point_over_letter (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL)
    (c : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (hζ : IsPrimitiveRoot ζ l) :
    ∃ τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, Formalism.MainNotions.DeltaInvariantLattices.ptK D.loc HW hA.2.2 c ζ τ := by
  have : Algebra.IsAlgebraic ↥(K0 K) (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) _
  obtain ⟨σ, hσ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ_[l]) (L := ↥(K0 K))
    (M := Om l) (E := Om l) ((LL.1.val).comp (((HW l).W K 1 LL hA.2.2).emb c))
  have hσx : ∀ x : ↥(K0 K),
      σ (x : Om l) = ((((HW l).W K 1 LL hA.2.2).emb c x : ↥LL.1) : Om l) := fun x => by
    have := congrArg (fun f => f x) hσ
    simpa [AlgHom.domRestrict] using this
  have hζ₁ := Formalism.MainNotions.UnusedSlot80.LevR.root_of_unity_primitive D l
  have hσinj : Function.Injective σ := σ.toRingHom.injective
  have hζO : IsPrimitiveRoot ((ζ : ↥LL.1) : Om l) l :=
    hζ.map_of_injective (f := LL.1.val) Subtype.val_injective
  have hσζ₁ : IsPrimitiveRoot (σ ((D.loc l).ζQ 1)) l := hζ₁.map_of_injective hσinj
  have : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  obtain ⟨b, -, hb⟩ := hσζ₁.eq_pow_of_pow_eq_one hζO.pow_eq_one
  have hβ : IsPrimitiveRoot ((D.loc l).ζQ 1 ^ b) l := by
    apply IsPrimitiveRoot.of_map_of_injective (f := σ) _ hσinj
    rw [map_pow, hb]
    exact hζO
  obtain ⟨g, hg⟩ := Formalism.MainNotions.UnusedSlot80.LevR.trans_prim (D.loc l) ((HW l).W K 1 LL hA.2.2)
    (Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F h9 l K LL hA) hζ₁ _ hβ
  have hmem : ∀ y, ((σ.comp (g : GQ l).toAlgHom).comp (Ks K 1).val) y ∈ LL.1 :=
    hA.2.2.2.2.2 _
  let τs : ↥(Ks K 1) →ₐ[ℚ_[l]] ↥LL.1 :=
    ((σ.comp (g : GQ l).toAlgHom).comp (Ks K 1).val).codRestrict LL.1.toSubalgebra hmem
  refine ⟨τs.comp (IntermediateField.inclusion hA.2.2.2.2.1), τs,
    ⟨fun x y hxy => ?_, fun y hy => ?_⟩, fun x y hxy => ?_⟩
  · apply Subtype.ext
    show σ ((g : GQ l) (y : Om l)) = _
    have hgx : (g : GQ l) (x : Om l) = x :=
      (IntermediateField.mem_fixingSubgroup_iff K.1 (g : GQ l)).mp g.2 _
        ((inf_le_left : K0 K ≤ K.1) x.2)
    rw [hxy, hgx, hσx]
  · apply Subtype.ext
    show σ ((g : GQ l) (y : Om l)) = _
    rw [hy, hg, map_pow, hb]
  · show τs _ = τs y
    congr 1
    exact Subtype.ext hxy.symm

theorem clause_at_levels (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL) :
    Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration ((HW l).W K 1 LL hA.2.2) := by
  have tie := ((Cm l).C K 1 LL hA.2.2).tie
  have hs := (HW l).W_s K 1 LL hA.2.2
  have hp : ((((D.loc l).PD K).p : ℕ) : ↥LL.1) ≠ 0 := by
    intro h
    have hv := ((HW l).W K 1 LL hA.2.2).v_l
    rw [h, AddValuation.map_zero] at hv
    exact WithTop.top_ne_one hv
  have hsurj : Function.Surjective (algebraMap ↥(K0 K) ↥K.1) :=
    fun x => ⟨⟨x, x.2, hA.1 x.2⟩, rfl⟩
  refine Formalism.MainNotions.UnusedSlot80.LevR.level_condition_of_level_zero _ ((Cm l).C K 1 LL hA.2.2).tie.levB hs
    ((Cm l).C K 1 LL hA.2.2).tie.levN_eq ((Cm l).C K 1 LL hA.2.2).tie.levB_φ hp ?_
  intro T hT c ζ hζ
  have hζl : IsPrimitiveRoot ζ l := by rwa [(D.loc l).PD_p] at hζ
  obtain ⟨τ, hτ⟩ := exists_point_over_letter D HW F h9 l K LL hA c ζ hζl
  have hover : ∀ x : ↥(K0 K), τ (algebraMap ↥(K0 K) ↥K.1 x) = ((HW l).W K 1 LL hA.2.2).emb c x := by
    obtain ⟨τs, ⟨hemb, -⟩, hres⟩ := hτ
    intro x
    have hy : (x : Om l) ∈ Ks K 1 := (le_sup_left : K0 K ≤ Ks K 1) x.2
    rw [hres (algebraMap ↥(K0 K) ↥K.1 x) ⟨x, hy⟩ rfl]
    exact hemb x ⟨x, hy⟩ rfl
  have h4' := ((h4 l K 1 LL hA.2.2 T hT).2 c ζ τ hτ).2
  exact Formalism.MainNotions.UnusedSlot80.LevR.lev0 _ T c ζ τ (Formalism.MainNotions.UnusedSlot80.LevR.ιDi_le _ T c τ hover hsurj) h4'


set_option maxHeartbeats 800000 in
theorem torsion_transitive (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL) :
    Formalism.MainNotions.N.Pv.LocalLengthBound.PtTrans ((HW l).W K 1 LL hA.2.2) := by
  have hl3' : 3 ≤ l := by
    have h2 := (Fact.out : l.Prime).two_le
    have hodd : l ≠ 2 := hA.2.1
    omega
  set W := (HW l).W K 1 LL hA.2.2 with hW
  intro ζ ζ' hζ hζ'
  have hpl : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  rw [hpl] at hζ hζ'
  have hcard := Formalism.MainNotions.UnusedSlot80.LevR.card_delF D HW F h9 l K LL hA
  have hv : (D.loc l).v LL ((l : ℕ) : ↥LL.1) = 1 := (D.loc l).v_l LL
  have hvO := (D.loc l).v_O LL
  have hl0 : ((l : ℕ) : ↥LL.1) ≠ 0 := by
    intro h; rw [h, AddValuation.map_zero] at hv; exact WithTop.top_ne_coe hv

  have hcong : ∀ δ : ↥W.DelF, ∃ a : ℕ,
      ((1 : ℕ) : WithTop ℚ) ≤ (D.loc l).v LL
        (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ δ : ↥(OL LL)) - (a : ↥LL.1)) := by
    intro δ
    obtain ⟨g, hg⟩ := W.resΓ_onto δ
    obtain ⟨a, ha, -⟩ := (D.loc l).χQ_cyc (g : GQ l) 1 ((D.loc l).ζQ 1)
      (by rw [pow_one]; exact (Formalism.MainNotions.UnusedSlot80.LevR.root_of_unity_primitive D l).pow_eq_one)
    refine ⟨a, ?_⟩
    have hres := W.χΓ_res g
    have hPD := (D.loc l).PD_χ K g
    rw [← hg, hres, hPD]
    set t : ℚ_[l] := ((D.loc l).χQ (g : GQ l) : ℚ_[l]) - (a : ℚ_[l]) with ht
    have hlQ : ((l : ℕ) : ℚ_[l]) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
    have e : algebraMap ℚ_[l] ↥LL.1 ((D.loc l).χQ (g : GQ l) : ℚ_[l]) - (a : ↥LL.1) =
        ((l : ℕ) : ↥LL.1) * algebraMap ℚ_[l] ↥LL.1 (t / (l : ℚ_[l])) := by
      rw [map_div₀, map_natCast, mul_div_cancel₀ _ hl0, ht, map_sub, map_natCast]
    rw [e, AddValuation.map_mul, hv]
    have hz : ‖t / (l : ℚ_[l])‖ ≤ 1 := by
      rw [norm_div, Padic.norm_p, div_le_one (by
        first
          | positivity
          | exact inv_pos.mpr (by exact_mod_cast (Fact.out : l.Prime).pos))]
      have := ha
      simpa [zpow_neg, zpow_one] using this
    have hint : algebraMap ℚ_[l] ↥LL.1 (t / (l : ℚ_[l])) ∈ OL LL := by
      have e2 : algebraMap ℚ_[l] ↥LL.1 (t / (l : ℚ_[l])) =
          algebraMap ℤ_[l] ↥LL.1 (⟨t / (l : ℚ_[l]), hz⟩ : ℤ_[l]) :=
        (IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥LL.1 (⟨t / (l : ℚ_[l]), hz⟩ : ℤ_[l])).symm
      rw [e2]
      exact (algebraMap ℤ_[l] ↥(OL LL) (⟨t / (l : ℚ_[l]), hz⟩ : ℤ_[l])).2
    exact le_add_of_nonneg_right ((hvO _).2 hint)
  choose aδ haδ using hcong

  have hvunit : ∀ w : (↥(OL LL))ˣ, (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL))) = 0 := by
    intro w
    have h1 := (hvO (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL)))).2 (w : ↥(OL LL)).2
    have h2 := (hvO (algebraMap ↥(OL LL) ↥LL.1 ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)))).2
      ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL)).2
    have h3 : (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (w : ↥(OL LL))) +
        (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 ((w⁻¹ : (↥(OL LL))ˣ) : ↥(OL LL))) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, Units.mul_inv, map_one, AddValuation.map_one]
    exact le_antisymm (le_trans (le_add_of_nonneg_right h2) h3.le) h1
  have hne : ∀ δ, ((aδ δ : ℕ) : ZMod l) ≠ 0 := by
    intro δ h
    rw [ZMod.natCast_eq_zero_iff] at h
    obtain ⟨c, hc⟩ := h
    have hva : (1 : WithTop ℚ) ≤ (D.loc l).v LL ((aδ δ : ℕ) : ↥LL.1) := by
      rw [hc, Nat.cast_mul, AddValuation.map_mul, hv]
      exact le_add_of_nonneg_right (Formalism.MainNotions.N.Pv.LocalLengthBound.Val.v_natCast_nonneg _ c)
    have hsum := AddValuation.map_add ((D.loc l).v LL)
      (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ δ : ↥(OL LL)) - (aδ δ : ↥LL.1))
      ((aδ δ : ℕ) : ↥LL.1)
    rw [sub_add_cancel, hvunit] at hsum
    have h1 := haδ δ
    rw [Nat.cast_one] at h1
    exact absurd hsum (not_le.2 (lt_of_lt_of_le (by exact_mod_cast zero_lt_one) (le_min h1 hva)))
  let U : ↥W.DelF → (ZMod l)ˣ := fun δ => Units.mk0 _ (hne δ)
  have hUinj : Function.Injective U := by
    intro δ δ' h
    have h1 : ((aδ δ : ℕ) : ZMod l) = ((aδ δ' : ℕ) : ZMod l) := congrArg Units.val h
    rw [ZMod.natCast_eq_natCast_iff'] at h1
    set χd := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ δ : ↥(OL LL))
    set χd' := algebraMap ↥(OL LL) ↥LL.1 (W.χΓ δ' : ↥(OL LL))

    have hdiff : (1 : WithTop ℚ) ≤ (D.loc l).v LL (χd - χd') := by
      have e : χd - χd' = (χd - (aδ δ : ↥LL.1)) - (χd' - (aδ δ' : ↥LL.1)) +
          ((aδ δ : ↥LL.1) - (aδ δ' : ↥LL.1)) := by ring
      rw [e]
      have hA1 := haδ δ
      have hA2 := haδ δ'
      rw [Nat.cast_one] at hA1 hA2
      refine le_trans (le_min (le_trans (le_min hA1 hA2) (AddValuation.map_sub ((D.loc l).v LL) _ _)) ?_)
        (AddValuation.map_add ((D.loc l).v LL) _ _)

      rcases le_total (aδ δ') (aδ δ) with hle | hle
      · have hd : l ∣ aδ δ - aδ δ' := (Nat.modEq_iff_dvd' hle).1 h1.symm
        obtain ⟨c, hc⟩ := hd
        have e2 : ((aδ δ : ℕ) : ↥LL.1) - ((aδ δ' : ℕ) : ↥LL.1) = ((aδ δ - aδ δ' : ℕ) : ↥LL.1) := by
          rw [Nat.cast_sub hle]
        rw [e2, hc, Nat.cast_mul, AddValuation.map_mul, hv]
        exact le_add_of_nonneg_right (Formalism.MainNotions.N.Pv.LocalLengthBound.Val.v_natCast_nonneg _ c)
      · have hd : l ∣ aδ δ' - aδ δ := (Nat.modEq_iff_dvd' hle).1 h1
        obtain ⟨c, hc⟩ := hd
        have e2 : ((aδ δ : ℕ) : ↥LL.1) - ((aδ δ' : ℕ) : ↥LL.1) = -((aδ δ' - aδ δ : ℕ) : ↥LL.1) := by
          rw [Nat.cast_sub hle]; ring
        rw [e2, AddValuation.map_neg, hc, Nat.cast_mul, AddValuation.map_mul, hv]
        exact le_add_of_nonneg_right (Formalism.MainNotions.N.Pv.LocalLengthBound.Val.v_natCast_nonneg _ c)

    set g := (δ : W.Gam) * (δ' : W.Gam)⁻¹
    have hξ : algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL)) = χd * χd'⁻¹ := by
      have hχ'0 : χd' ≠ 0 := by
        intro h0
        have := hvunit (W.χΓ δ')
        change (D.loc l).v LL χd' = 0 at this
        rw [h0, AddValuation.map_zero] at this
        exact WithTop.top_ne_coe this
      rw [eq_mul_inv_iff_mul_eq₀ hχ'0]
      simp only [χd, χd', g, ← map_mul, ← Units.val_mul, ← map_mul (W.χΓ), inv_mul_cancel_right]
    have hξ1 : (1 : WithTop ℚ) ≤ (D.loc l).v LL (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL)) - 1) := by
      have hχ'0 : χd' ≠ 0 := by
        intro h0
        have := hvunit (W.χΓ δ')
        change (D.loc l).v LL χd' = 0 at this
        rw [h0, AddValuation.map_zero] at this
        exact WithTop.top_ne_coe this
      have e : χd * χd'⁻¹ - 1 = (χd - χd') * χd'⁻¹ := by field_simp
      rw [hξ, e, AddValuation.map_mul]
      have hinv : (D.loc l).v LL χd'⁻¹ = 0 := by
        have := hvunit (W.χΓ δ')⁻¹
        simpa [χd', map_inv₀] using this
      rw [hinv, add_zero]
      exact hdiff

    obtain ⟨k, hk, hδk⟩ := (W.DelF_def δ).1 δ.2
    obtain ⟨k', hk', hδk'⟩ := (W.DelF_def δ').1 δ'.2
    have hgk : g ^ (k * k') = 1 := by
      simp only [g, mul_pow, inv_pow]
      rw [pow_mul, hδk, one_pow, one_mul, mul_comm k k', pow_mul, hδk', one_pow, inv_one]
    have hξk : (algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL))) ^ (k * k') = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, hgk, map_one, Units.val_one, map_one]
    have hl3 : 3 ≤ l := by
      have h2 := (Fact.out : l.Prime).two_le
      have hodd : l ≠ 2 := hA.2.1
      omega
    have hξeq : algebraMap ↥(OL LL) ↥LL.1 (W.χΓ g : ↥(OL LL)) = 1 := by
      by_contra hne1
      exact Formalism.MainNotions.N.Pv.LocalLengthBound.Val.pow_ne_one_of_close ((D.loc l).v LL) (Fact.out : l.Prime) hv hl3
        (k * k') _ (Nat.mul_pos hk hk') hξ1 hne1 hξk
    have hg1 : g = 1 := by
      apply W.χΓ_inj
      rw [map_one]
      apply Units.ext
      apply Subtype.val_injective
      simpa using hξeq
    exact Subtype.ext (mul_inv_eq_one.1 hg1)
  have hUbij : Function.Bijective U := by
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hUinj, by rw [Fintype.card_coe, hcard, ZMod.card_units]⟩

  obtain ⟨b, hb, hζb⟩ := hζ.eq_pow_of_pow_eq_one hζ'.pow_eq_one
  have hb0 : ((b : ℕ) : ZMod l) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hd
    have : b = 0 := Nat.eq_zero_of_dvd_of_lt hd hb
    subst this
    rw [pow_zero] at hζb
    exact hζ'.ne_one (Fact.out : l.Prime).one_lt hζb.symm
  obtain ⟨δ, hδ⟩ := hUbij.2 (Units.mk0 _ hb0)
  have h1 : ((aδ δ : ℕ) : ZMod l) = ((b : ℕ) : ZMod l) := congrArg Units.val hδ
  rw [ZMod.natCast_eq_natCast_iff] at h1
  have hpowmod : ∀ m : ℕ, ζ ^ m = ζ ^ (m % l) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m l, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  refine ⟨δ, δ.2, aδ δ, ?_, haδ δ⟩
  rw [hpowmod, h1, ← hpowmod, hζb]

theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm → Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F →
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL),
      Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration ((HW l).W K 1 LL hA.2.2) ∧
        Formalism.MainNotions.N.Pv.LocalLengthBound.PtTrans ((HW l).W K 1 LL hA.2.2) :=
  fun D HW F Cm h4 h9 l _ K LL hA =>
    ⟨clause_at_levels D HW F Cm h4 h9 l K LL hA, torsion_transitive D HW F h9 l K LL hA⟩

end GlobalTheory.LevelClauseOdd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpansionRulesCriterionOddRootOfUnityCaseA
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

noncomputable section

namespace GlobalTheory.ExpansionsOdd


set_option maxHeartbeats 800000 in
theorem main : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm →
    ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL),
      Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing ((HW l).W K 1 LL hA.2.2) ∧ Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules ((HW l).W K 1 LL hA.2.2) ∧
        Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit ((HW l).W K 1 LL hA.2.2) := by
  intro D HW F Cm hN l _ K LL hA
  obtain ⟨p1, -, p3, p4, p5, -, -, -, p9, -⟩ := hN
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI := Formalism.MainNotions.UnusedSlot80.neZero_finrank_max_unramified K
  haveI : IsLocalRing ↥(OL LL) := Formalism.MainNotions.LiftingTheory.lkd_local (D.loc l) LL
  haveI : IsFractionRing ↥(OL LL) ↥LL.1 := Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal ↥(OL LL)) ↥(OL LL) :=
    Formalism.MainNotions.N.Pv.LocalLengthBound.OLC.complete_max LL
  have hLT := GlobalTheory.LevelClauseOdd.main D HW F Cm p4 p9 l K LL hA
  have C := ((Cm l).C K 1 LL hA.2.2).tie
  have hs : ((HW l).W K 1 LL hA.2.2).s = 1 := (HW l).W_s K 1 LL hA.2.2
  have hG := Formalism.MainNotions.N.Pv.LocalLengthBound.gam_of_tie _ hs C
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hA.2.2) := p9 l K 1 LL hA.2.2
  refine ⟨fun hCA => ?_, Formalism.MainNotions.N.Pv.LocalLengthBound.expRules_of _ hLT.1 hG.1 hG.2, ?_⟩
  · have hring : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP ((HW l).W K 1 LL hA.2.2) :=
      (((h9 _ (Formalism.MainNotions.LiftingTheory.gen_one_crys ((HW l).W K 1 LL hA.2.2))) hs hCA.2.2).2.2 (Formalism.MainNotions.UnusedSlot80.finrank_K0_eq_one_of_le_Kur hA.1)).1
    exact Formalism.MainNotions.N.Pv.LocalLengthBound.expRing_of _ hring hCA
  · have hlm : ((((D.loc l).PD K).p : ℕ) : ↥(OL LL)) ∈ IsLocalRing.maximalIdeal ↥(OL LL) := by
      rw [(D.loc l).PD_p K]; exact Formalism.MainNotions.N.Pv.LocalLengthBound.l_mem_maxOL (D.loc l) LL
    have hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris ((D.loc l).PD K) ↥LL.1 :=
      GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l (D.loc l) (D.locA l) (D.locT l) K LL
    have hB : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool ((HW l).W K 1 LL hA.2.2) := Formalism.MainNotions.RamifiedCoefficientChains.Sh.basTool_of _ h9
    exact Formalism.MainNotions.N.Pv.LocalLengthBound.expCrit_of _ Subtype.val_injective hlm (Formalism.MainNotions.UnusedSlot80.BCF.isFrac_OL LL)
      (p1 l K 1 LL hA.2.2) (p3 l K 1 LL hA.2.2) hLT.1 (p5 l K 1 LL hA.2.2) h9 hD hB C
      (p4 l K 1 LL hA.2.2) hLT.2

end GlobalTheory.ExpansionsOdd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExpansionRulesCriterionOddRootOfUnityCaseAStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_rules_criterion_odd_root_of_unity_caseA : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL), Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing ((HW l).W K 1 LL hA.2.2) ∧ Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules ((HW l).W K 1 LL hA.2.2) ∧ Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit ((HW l).W K 1 LL hA.2.2) := by
  first | exact @GlobalTheory.ExpansionsOdd.main | exact GlobalTheory.ExpansionsOdd.main | (intros; apply GlobalTheory.ExpansionsOdd.main <;> assumption)
end
end

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem _root_.GlobalTheory.T.wachOperatorProduct_shift_mem_lattice : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), Formalism.MainNotions.DeltaInvariantLattices.DeltaInvariantNormBound D HW F Cm → ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : Loc.CaseA K LL), ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (y' Y : ℕ) (cO : ℤ → ↥(OL LL)), (∀ x : ℤ, ((l : ℕ) : ↥(OL LL)) * cO x = 1 - (((((HW l).W K 1 LL hA.2.2).χΓ ((HW l).W K 1 LL hA.2.2).gam) ^ (-x) : (↥(OL LL))ˣ) : ↥(OL LL))) → ∀ xs : List ℤ, (∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) (j : ℕ), Formalism.MainNotions.LiftingTheory.Over ((HW l).W K 1 LL hA.2.2) τ i → IsJumpV ((D.loc l).PD K) T.ρ τ a → y' < j → j ≤ Y → a + (j : ℤ) ∈ xs) → ∀ seq : ℕ → ((HW l).W K 1 LL hA.2.2).DD T, Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL hA.2.2) T i (seq 0) → Formalism.MainNotions.LiftingTheory.qp ((HW l).W K 1 LL hA.2.2) ^ Y • seq 0 ∈ ((HW l).W K 1 LL hA.2.2).N T → (∀ k < xs.length, ((HW l).W K 1 LL hA.2.2).π₀ • (seq (k + 1) + cO (xs.getD k 0) • seq k) = ((HW l).W K 1 LL hA.2.2).γD T ((HW l).W K 1 LL hA.2.2).gam (seq k) - seq k) → Formalism.MainNotions.CrystallineLiftingInputs.DL ((HW l).W K 1 LL hA.2.2) T i (seq xs.length) ∧ Formalism.MainNotions.LiftingTheory.qp ((HW l).W K 1 LL hA.2.2) ^ y' • seq xs.length ∈ ((HW l).W K 1 LL hA.2.2).N T := by
  intro D HW F Cm hN l _ K LL hA
  have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K 1 LL hA.2.2) :=
    hN.2.2.2.2.2.2.2.2.1 l K 1 LL hA.2.2
  obtain ⟨hRg, hRu, hCr⟩ :=
    GlobalTheory.T.expansion_rules_criterion_odd_root_of_unity_caseA D HW F Cm hN l K LL hA
  have hD : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris ((D.loc l).PD K) ↥LL.1 :=
    fun hb V _ _ _ _ _ ρ hc =>
      GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l (D.loc l) (D.locA l) (D.locT l) K LL hb V ρ hc
  intro T hT i y' Y cO hc xs hxs seq h0 h0N hrec
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  have : FiniteDimensional ℚ_[l] ↥(K0 K) := ((D.loc l).PD K).finK₀
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  obtain ⟨ζ, hζ⟩ := Formalism.MainNotions.UnusedSlot80.exists_prim_of_good D hA.2.2
  refine GlobalTheory.wachShift_mem_of_exp _ h9 hRg hRu hCr hD
    (Formalism.MainNotions.UnusedSlot80.caseA_of_le_Kur_of_ne_two (D.loc l) (HW l) hA.2.2 hA.1 hA.2.1)
    ?_ ζ (by rw [hp]; exact hζ) T hT i y' Y cO (fun x => by rw [hp]; exact hc x) xs hxs seq h0 h0N hrec
  rw [hp]
  exact Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
