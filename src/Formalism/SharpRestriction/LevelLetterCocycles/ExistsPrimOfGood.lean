module

public import Formalism.SharpRestriction.LevelLetterCocycles.LevelOneUniformizerCoeffVanish
public import Formalism.SharpRestriction.LevelLetterCocycles.DlOfQp

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevelZeroMembershipOfHorizontal
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowerZeroEqQ
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.VanishOfXU
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.CoeffAlgMul
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.CrystallineFiltrationAntitone
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.StageStep
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.CrA

variable {K : Type*} [Field K] {d : ℕ}

def PiLocalization₂ (G : ℤ → Submodule K (Fin d → K)) (hi u : ℤ) : Prop :=
  ∃ (S : Set (Fin d → K)) (ℓ : (Fin d → K) → ℤ), LinearIndepOn K id S ∧
    (∀ x ∈ S, x ∈ G (ℓ x) ∧ u ≤ ℓ x ∧ ℓ x ≤ hi) ∧ S ⊆ G u ∧
    ∀ u', u ≤ u' → u' ≤ hi → G u' ≤ Submodule.span K {x | x ∈ S ∧ u' ≤ ℓ x}

theorem stage_top (G : ℤ → Submodule K (Fin d → K)) (hi : ℤ) : PiLocalization₂ G hi hi := by
  unfold PiLocalization₂
  obtain ⟨b, hbt, hspan, hli⟩ := exists_linearIndependent K (G hi : Set (Fin d → K))
  refine ⟨b, fun _ => hi, hli, fun x hx => ⟨hbt hx, le_rfl, le_rfl⟩, hbt, ?_⟩
  intro u' h1 h2 v hv
  have hsub : b ⊆ {x | x ∈ b ∧ u' ≤ (fun _ => hi) x} := fun x hx => ⟨hx, h2⟩
  refine Submodule.span_mono hsub ?_
  rw [hspan, Submodule.span_eq]
  rwa [← le_antisymm h2 h1]

theorem stage_step (G : ℤ → Submodule K (Fin d → K)) (hG : Antitone G) (hi u : ℤ) (hu : u < hi)
    (h : PiLocalization₂ G hi (u + 1)) : PiLocalization₂ G hi u := by
  unfold PiLocalization₂ at h ⊢
  obtain ⟨S, ℓ, hli, hmem, hSG, hspan⟩ := h
  have hSu : S ⊆ (G u : Set (Fin d → K)) := fun x hx => hG (by omega : u ≤ u + 1) (hSG hx)
  obtain ⟨b, hbt, hSb, htb, hlib⟩ := exists_linearIndepOn_id_extension hli hSu
  refine ⟨b, fun x => if x ∈ S then ℓ x else u, hlib, ?_, hbt, ?_⟩
  · intro x hx
    by_cases hxS : x ∈ S
    · obtain ⟨h1, h2, h3⟩ := hmem x hxS
      simp only [hxS, if_true]
      exact ⟨h1, by omega, h3⟩
    · simp only [hxS, if_false]
      exact ⟨hbt hx, le_rfl, hu.le⟩
  · intro u' h1 h2
    rcases eq_or_lt_of_le h1 with rfl | hlt
    · intro v hv
      have hsub : b ⊆ {x | x ∈ b ∧ u ≤ (fun x => if x ∈ S then ℓ x else u) x} := by
        intro x hx
        refine ⟨hx, ?_⟩
        by_cases hxS : x ∈ S
        · have h3 := (hmem x hxS).2.1
          simp only [hxS, if_true]
          omega
        · simp only [hxS, if_false]
          exact le_rfl
      exact Submodule.span_mono hsub (htb hv)
    · refine (hspan u' (by omega) h2).trans (Submodule.span_mono ?_)
      rintro x ⟨hxS, hx⟩
      exact ⟨hSb hxS, by simpa [hxS] using hx⟩

theorem stage_all (G : ℤ → Submodule K (Fin d → K)) (hG : Antitone G) (hi : ℤ) :
    ∀ u ≤ hi, PiLocalization₂ G hi u := by
  have key : ∀ k : ℕ, PiLocalization₂ G hi (hi - k) := by
    intro k
    induction k with
    | zero => simpa using stage_top G hi
    | succ k ih =>
      refine stage_step G hG hi (hi - ((k + 1 : ℕ) : ℤ)) (by push_cast; omega) ?_
      have e : hi - ((k + 1 : ℕ) : ℤ) + 1 = hi - (k : ℤ) := by push_cast; ring
      rw [e]
      exact ih
  intro u hu
  have h := key (hi - u).toNat
  rwa [Int.toNat_of_nonneg (by omega), sub_sub_cancel] at h

theorem adapted (G : ℤ → Submodule K (Fin d → K)) (hG : Antitone G) (lo hi : ℤ) (hlh : lo ≤ hi)
    (hlo : G lo = ⊤) :
    ∃ (I : ℕ) (P : Fin I → Fin d → K) (Q : Fin I → Fin d → K) (h : Fin I → ℤ),
      (∀ c : Fin d → K, c = ∑ i, (∑ m, Q i m * c m) • P i) ∧
      (∀ i, P i ∈ G (h i)) ∧ (∀ i, lo ≤ h i ∧ h i ≤ hi) ∧
      ∀ u : ℤ, u ≤ hi → ∀ c ∈ G u, ∀ i, h i < u → ∑ m, Q i m * c m = 0 := by
  obtain ⟨S, ℓ, hli, hmem, _, hspan⟩ := stage_all G hG hi lo hlh
  have hfin : S.Finite := LinearIndependent.set_finite_of_isNoetherian hli
  have := hfin.fintype
  have hsp : ⊤ ≤ Submodule.span K (Set.range ((↑) : S → Fin d → K)) := by
    rw [Subtype.range_coe, ← hlo]
    exact (hspan lo le_rfl hlh).trans (Submodule.span_mono fun x hx => hx.1)
  let B0 : Module.Basis S K (Fin d → K) := Module.Basis.mk (v := ((↑) : S → Fin d → K)) hli hsp
  let e := Fintype.equivFin S
  let B := B0.reindex e
  have hB : ∀ i, B i = ((e.symm i : S) : Fin d → K) := fun i => by
    simp only [B, B0, Module.Basis.reindex_apply]
    exact Module.Basis.mk_apply hli hsp (e.symm i)
  have hQ : ∀ (c : Fin d → K) i, ∑ m, B.repr (Pi.single m 1) i * c m = B.repr c i := by
    intro c i
    conv_rhs => rw [← Finset.univ_sum_single c]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hs : (Pi.single m (c m) : Fin d → K) = c m • Pi.single m 1 := by
      ext j
      by_cases hj : j = m
      · subst hj
        simp
      · simp [hj]
    rw [hs, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]
  refine ⟨Fintype.card S, fun i => B i, fun i m => B.repr (Pi.single m 1) i, fun i => ℓ (B i),
    ?_, ?_, ?_, ?_⟩
  · intro c
    simp only [hQ]
    exact (B.sum_repr c).symm
  · intro i
    show B i ∈ G (ℓ (B i))
    rw [hB]
    exact (hmem _ (e.symm i).2).1
  · intro i
    show lo ≤ ℓ (B i) ∧ ℓ (B i) ≤ hi
    rw [hB]
    obtain ⟨_, h1, h2⟩ := hmem _ (e.symm i).2
    exact ⟨h1, h2⟩
  · intro u hu c hc i hi'
    have hi'' : ℓ (B i) < u := hi'
    show ∑ m, B.repr (Pi.single m 1) i * c m = 0
    rw [hQ]
    by_cases hul : u ≤ lo
    · exfalso
      have h1 := (hmem _ (e.symm i).2).2.1
      rw [hB] at hi''
      omega
    · have hcs := hspan u (by omega) hu hc
      have hset : {x | x ∈ S ∧ u ≤ ℓ x} = B '' {j | u ≤ ℓ (B j)} := by
        ext x
        constructor
        · rintro ⟨hxS, hx⟩
          refine ⟨e ⟨x, hxS⟩, ?_, ?_⟩
          · show u ≤ ℓ (B (e ⟨x, hxS⟩))
            rw [hB, Equiv.symm_apply_apply]
            exact hx
          · rw [hB, Equiv.symm_apply_apply]
        · rintro ⟨j, hj, rfl⟩
          exact ⟨by rw [hB]; exact (e.symm j).2, hj⟩
      rw [hset, Module.Basis.mem_span_image] at hcs
      by_contra hne
      have hmemi := hcs (Finsupp.mem_support_iff.2 hne)
      exact absurd (show u ≤ ℓ (B i) from hmemi) (not_le.2 hi'')

end Formalism.MainNotions.UnusedSlot80.CrA
end
end

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.CrD

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup PowerSeries TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

def dvL (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) :
    (Fin d → LL) →ₗ[LL] T.V ⊗[Qp] B where
  toFun c := dv W T e b c
  map_add' c c' := by simp [dv, add_smul, Finset.sum_add_distrib]
  map_smul' r c := by simp [dv, smul_smul, Finset.smul_sum]

theorem dvL_apply (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c : Fin d → LL) :
    dvL W T e b c = dv W T e b c := rfl

theorem crystalline_filtration_antitone (T : LocLat G Qp LL O) (a : ZMod n) : Antitone fun u => FilS W T a 0 u :=
  fun _ _ hab => Submodule.map_mono (inf_le_inf_right _
    (Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti (PD := PD) (ρ := T.ρ) hab))

theorem exists_lpow (hvl : v (PD.p : LL) = 1) (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) (x : LL) :
    ∃ κ : ℕ, ∃ o : O, algebraMap O LL o = (PD.p : LL) ^ κ * x := by
  by_cases hx : x = 0
  · exact ⟨0, 0, by simp [hx]⟩
  have hne : v x ≠ ⊤ := by rwa [ne_eq, AddValuation.top_iff]
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp hne
  refine ⟨⌈-q⌉₊, hO2 _ ?_⟩
  rw [AddValuation.map_mul, AddValuation.map_pow, hvl, ← hq]
  have h1 : ((⌈-q⌉₊ : ℕ) • (1 : WithTop ℚ)) = (((⌈-q⌉₊ : ℕ) : ℚ) : WithTop ℚ) := by
    rw [← WithTop.coe_one, ← WithTop.coe_nsmul, nsmul_eq_mul, mul_one]
  rw [h1, ← WithTop.coe_add, WithTop.coe_nonneg]
  have := Nat.le_ceil (-q)
  linarith

theorem exists_lpow_fin (hvl : v (PD.p : LL) = 1) (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x) {ι : Type}
    [Fintype ι] (x : ι → LL) : ∃ κ : ℕ, ∀ i, ∃ o : O, algebraMap O LL o = (PD.p : LL) ^ κ * x i := by
  choose κ o ho using fun i => exists_lpow hvl hO2 (x i)
  refine ⟨∑ i, κ i, fun i => ⟨((PD.p : ℕ) : O) ^ (∑ j, κ j - κ i) * o i, ?_⟩⟩
  have hle : κ i ≤ ∑ j, κ j := Finset.single_le_sum (fun j _ => Nat.zero_le (κ j)) (Finset.mem_univ i)
  rw [map_mul, ho, map_pow, map_natCast, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem lamUp_eq (A : ArcP n) (c' : ZMod n) (e : ℕ) :
    Formalism.MainNotions.UnusedSlot80.LevC.LamUp W A c' e = ∏ s ∈ Finset.range e,
      ps W (s + 1) ^ A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) (s + 1) := by
  unfold Formalism.MainNotions.UnusedSlot80.LevC.LamUp abelian₂
  rw [map_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [map_pow, ← Formalism.MainNotions.UnusedSlot80.LevC.ps_succ, Formalism.MainNotions.UnusedSlot80.LevC.hs_succ]
  congr 2
  push_cast; ring

variable [IsDomain O]

theorem cc_lev_piLamUp (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (A : ArcP n) (c' : ZMod n) (e : ℕ)
    (a : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    constantCoeff (W.lev a ζ (W.π₀ * Formalism.MainNotions.UnusedSlot80.LevC.LamUp W A c' e)) ≠ 0 := by
  obtain ⟨S, -, hS⟩ := Formalism.MainNotions.UnusedSlot80.DivLevR.lev_qP_X (W := W) hR a ζ hζ
  have hq0 : constantCoeff (W.lev a ζ (Formalism.MainNotions.WachCoordinates.qP W)) = 0 := by
    rw [hS, map_mul, constantCoeff_X, zero_mul]
  have hp : (PD.p : LL) ≠ 0 := Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W
  have hπ : constantCoeff (W.lev a ζ W.π₀) = -(PD.p : LL) := by
    have e1 : W.π₀ = Formalism.MainNotions.WachCoordinates.qP W - ((PD.p : ℕ) : LetA O n) := by
      unfold Formalism.MainNotions.WachCoordinates.qP; ring
    rw [e1, map_sub, map_sub, hq0, map_natCast, map_natCast]; ring
  have hps : ∀ s : ℕ, constantCoeff (W.lev a ζ (ps W (s + 1))) = (PD.p : LL) := by
    intro s
    obtain ⟨x, hx⟩ := Formalism.MainNotions.UnusedSlot80.ToolsR.φpow_qP (W := W) hR (s + 1) (by omega)
    have e1 : ps W (s + 1) = ((PD.p : ℕ) : LetA O n) + Formalism.MainNotions.WachCoordinates.qP W * x := by
      have := Formalism.MainNotions.UnusedSlot80.ToolsR.pS_sub (W := W) (s + 1)
      rw [hx] at this
      have e2 : ps W (s + 1) = Formalism.MainNotions.WachCoordinates.pS W (s + 1) := rfl
      rw [e2, ← this]; ring
    rw [e1, map_add (f := _), map_mul, map_add (f := _), map_mul, hq0, zero_mul, add_zero, map_natCast, map_natCast]
  rw [lamUp_eq, map_mul, map_prod, map_mul, map_prod, hπ]
  refine mul_ne_zero (neg_ne_zero.mpr hp) (Finset.prod_ne_zero_iff.mpr fun s _ => ?_)
  rw [map_pow, map_pow, hps]
  exact pow_ne_zero _ hp

theorem X_pow_dvd_of_unit {U F : PowerSeries LL} (hU : constantCoeff U ≠ 0) {k : ℕ}
    (h : ∀ j < k, coeff j (U * F) = 0) : ∀ j < k, coeff j F = 0 := by
  have h1 : (X : PowerSeries LL) ^ k ∣ U * F := X_pow_dvd_iff.mpr h
  have h2 : (X : PowerSeries LL) ^ k ∣ F := by
    obtain ⟨g, hg⟩ := h1
    refine ⟨U⁻¹ * g, ?_⟩
    calc F = U⁻¹ * (U * F) := by rw [← mul_assoc, PowerSeries.inv_mul_cancel _ hU, one_mul]
      _ = X ^ k * (U⁻¹ * g) := by rw [hg]; ring
  exact X_pow_dvd_iff.mp h2

end Formalism.MainNotions.UnusedSlot80.CrD
end
end

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.CrD

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup PowerSeries TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem coeff_alg_mul (o : O) (F : PowerSeries LL) (j : ℕ) :
    coeff j (algebraMap O (PowerSeries LL) o * F) = algebraMap O LL o * coeff j F := by
  rw [IsScalarTower.algebraMap_apply O LL (PowerSeries LL)]
  first
    | rw [← PowerSeries.smul_eq_C_mul]; simp
    | simp [Algebra.algebraMap_eq_smul_one]

theorem dv_smul' (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (r : LL) (c : Fin d → LL) :
    dv W T e b (r • c) = r • dv W T e b c := by
  rw [← dvL_apply, map_smul, dvL_apply]

variable [IsDomain O] [NeZero n] [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]

theorem secIn_of_fil (C : Formalism.MainNotions.UnusedSlot80.LevC.Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n)
    (hc' : c' ∈ A.cuts) (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e : ℕ) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (f : Fin d → W.EE) (u : Fin d → LetA O n) (hu : ∀ m, u m ∈ W.AΔ)
    (hf : ∀ m, algebraMap (LetA O n) W.EE (ps W 0 ^ A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0) * f m =
      algebraMap (LetA O n) W.EE (letE (c' + ((e + 1 : ℕ) : ZMod n)) *
        (W.π₀ * Formalism.MainNotions.UnusedSlot80.LevC.LamUp W A c' e) * u m))
    (hfil : ∀ j : ℕ, (j : ℤ) < 2 * (A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 : ℤ) →
      dv W T (e + 1) b (fun m => coeff j (W.lev (c' + ((e + 1 : ℕ) : ZMod n)) ζ
        (W.π₀ * Formalism.MainNotions.UnusedSlot80.LevC.LamUp W A c' e * u m))) ∈
        FilS W T (c' + ((e + 1 : ℕ) : ZMod n)) 0
          ((A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 : ℤ) - j)) :
    ∃ κ : ℕ, SecIn W (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1)
      (condNN W T (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) b) fun m => lE W κ * f m := by
  set a : ZMod n := c' + ((e + 1 : ℕ) : ZMod n) with ha
  set H : ℕ := A.Hs a (e + 1) 0 with hH
  set LU := Formalism.MainNotions.UnusedSlot80.LevC.LamUp W A c' e with hLU
  have hinj := C.hinj
  have hp : (PD.p : LL) ≠ 0 := Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W

  let Gf : ℤ → Submodule LL (Fin d → LL) := fun w => (FilS W T a 0 w).comap (dvL W T (e + 1) b)
  have hGa : Antitone Gf := fun _ _ h => Submodule.comap_mono (crystalline_filtration_antitone W T a h)
  have hlow : ∀ c₀ : Fin d → O, dvO W T (e + 1) b c₀ ∈ FilS W T a 0 (-(H : ℤ)) := fun c₀ =>
    Formalism.MainNotions.UnusedSlot80.LevC.dvO_filLow W C.hbij A hA c' hc' T hT b hb (e + 1) 0 (by omega) c₀
  have hGtop : Gf (-(H : ℤ)) = ⊤ := by
    rw [eq_top_iff]
    intro c _
    show dv W T (e + 1) b c ∈ FilS W T a 0 (-(H : ℤ))
    have hc : c = ∑ m, c m • (Pi.single m (1 : LL) : Fin d → LL) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hc, ← dvL_apply, map_sum]
    refine Submodule.sum_mem _ fun m _ => ?_
    rw [map_smul, dvL_apply]
    refine Submodule.smul_mem _ _ ?_
    have h1 := hlow (Pi.single m 1)
    have h2 : dvO W T (e + 1) b (Pi.single m 1) = dv W T (e + 1) b (Pi.single m 1) := by
      unfold dvO; congr 1; funext k; by_cases hk : k = m
      · subst hk; simp
      · simp [Pi.single_apply, hk]
    rwa [h2] at h1
  obtain ⟨I, P, Q, h, hPQ, hPG, hlev, hvan⟩ :=
    Formalism.MainNotions.UnusedSlot80.CrA.adapted Gf hGa (-(H : ℤ)) (H : ℤ) (by omega) hGtop
  obtain ⟨κ1, hP1⟩ := exists_lpow_fin W.v_l C.hO2 (fun im : Fin I × Fin d => P im.1 im.2)
  obtain ⟨κ2, hQ1⟩ := exists_lpow_fin W.v_l C.hO2 (fun im : Fin I × Fin d => Q im.1 im.2)
  choose P' hP' using hP1
  choose Q' hQ' using hQ1

  let k : Fin I → ℕ := fun i => ((H : ℤ) - h i).toNat
  let Vp : Fin I → LetA O n := fun i => ∑ m, algebraMap O (LetA O n) (Q' (i, m)) * u m
  let g : Fin I → W.EE := fun i => ∑ m, algebraMap O W.EE (Q' (i, m)) * f m
  let c₀ : Fin I → Fin d → O := fun i m => P' (i, m)
  let α : Fin I → ℕ → ℤ := fun i s => if s = 0 then (k i : ℤ) - H else (A.Hs a (e + 1) s : ℤ)
  have hVpA : ∀ i, Vp i ∈ W.AΔ := fun i =>
    Subalgebra.sum_mem _ fun m _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (hu m)

  have hvan' : ∀ i, ∀ j < k i, coeff j (W.lev a ζ (Vp i)) = 0 := by
    intro i
    apply X_pow_dvd_of_unit (cc_lev_piLamUp W C.hR A c' e a ζ hζ)
    intro j hj
    have hjH : (j : ℤ) < (H : ℤ) - h i := Int.lt_toNat.mp hj
    have hk2 : (j : ℤ) < 2 * (H : ℤ) := by
      have := (hlev i).1
      omega
    have hmem : (fun m => coeff j (W.lev a ζ (W.π₀ * LU * u m))) ∈ Gf ((H : ℤ) - j) := hfil j hk2
    have hz := hvan ((H : ℤ) - j) (by omega) _ hmem i (by omega)
    rw [← map_mul]
    have e1 : W.π₀ * LU * Vp i = ∑ m, algebraMap O (LetA O n) (Q' (i, m)) * (W.π₀ * LU * u m) := by
      simp only [Vp, Finset.mul_sum]
      exact Finset.sum_congr rfl fun m _ => by ring
    have e2 : ∀ m, coeff j (W.lev a ζ (algebraMap O (LetA O n) (Q' (i, m)) * (W.π₀ * LU * u m))) =
        (PD.p : LL) ^ κ2 * (Q i m * coeff j (W.lev a ζ (W.π₀ * LU * u m))) := by
      intro m
      rw [map_mul, AlgHom.commutes, coeff_alg_mul, hQ']
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum, map_sum, Finset.sum_congr rfl (fun m _ => e2 m), ← Finset.mul_sum, hz, mul_zero]

  have hdiv : ∀ i, ∃ h' ∈ W.AΔ, letE a * Vp i = ps W 0 ^ k i * h' := fun i =>
    Formalism.MainNotions.UnusedSlot80.DivLevR.divLev_of (W := W) C.hR (not_isUnit_p W C.hV) C.hinj a ζ hζ (Vp i) (hVpA i)
      (k i) (hvan' i)
  choose h' hh'A hh' using hdiv

  have hgV : ∀ i, algebraMap (LetA O n) W.EE (ps W 0 ^ H) * g i =
      algebraMap (LetA O n) W.EE (letE a * (W.π₀ * LU) * Vp i) := by
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [g, Vp, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [IsScalarTower.algebraMap_apply O (LetA O n) W.EE, mul_left_comm, hf m, ← map_mul]
    congr 1; ring
  have hunit : IsUnit (algebraMap (LetA O n) W.EE (ps W 0)) := Formalism.MainNotions.UnusedSlot80.LevC.ps_unitE W C.hR 0
  refine ⟨κ1 + κ2, I, g, c₀, α, fun i => ⟨?_, ?_⟩, fun m => ?_⟩
  ·
    have hnum : ∏ s ∈ Finset.range (e + 1), ps W s ^ (α i s).toNat =
        LU * ps W 0 ^ ((k i : ℤ) - H).toNat := by
      rw [Finset.prod_range_succ', hLU, lamUp_eq]
      congr 1
      all_goals (try (refine Finset.prod_congr rfl fun s _ => ?_; simp only [α, if_neg (Nat.succ_ne_zero s), Int.toNat_natCast]))
    have hden : ∏ s ∈ Finset.range (e + 1), ps W s ^ (-(α i s)).toNat =
        ps W 0 ^ ((H : ℤ) - k i).toNat := by
      rw [Finset.prod_range_succ']
      have h1 : ∏ s ∈ Finset.range e, ps W (s + 1) ^ (-(α i (s + 1))).toNat = 1 :=
        Finset.prod_eq_one fun s _ => by
          simp only [α, if_neg (Nat.succ_ne_zero s)]
          rw [Int.toNat_eq_zero.2 (by omega), pow_zero]
      rw [h1, one_mul]
      simp only [α, if_pos rfl, neg_sub]
    refine ⟨W.π₀ * h' i, W.AΔ.mul_mem C.hR.1 (hh'A i), ?_⟩
    rw [hnum, hden]
    have hk : ((H : ℤ) - k i).toNat + k i = H + ((k i : ℤ) - H).toNat := by omega
    have hl2 : letE a * Vp i = letE a * (ps W 0 ^ k i * h' i) := by
      rw [← hh' i, ← mul_assoc, Formalism.MainNotions.UnusedSlot80.DivLevR.letE_idem]
    apply (hunit.pow (k i)).mul_left_cancel
    rw [← map_pow, ← mul_assoc, ← map_mul, ← pow_add, add_comm, hk, pow_add, map_mul, mul_comm
      (algebraMap (LetA O n) W.EE (ps W 0 ^ H)), mul_assoc, hgV i, ← map_mul, ← map_mul]
    congr 1
    have e3 : letE a * (W.π₀ * LU) * Vp i = (W.π₀ * LU) * (letE a * Vp i) := by ring
    rw [e3, hl2]
    ring
  ·
    intro s hs
    rcases Nat.eq_zero_or_pos s with rfl | hs1
    · have e1 : -(α i 0) = (H : ℤ) - k i := by simp only [α, if_pos rfl]; ring
      rw [e1]
      have e2 : dvO W T (e + 1) b (c₀ i) = ((PD.p : LL) ^ κ1) • dv W T (e + 1) b (P i) := by
        unfold dvO
        rw [← dv_smul']
        congr 1; funext m; simp [c₀, hP', smul_eq_mul]
      rw [e2]
      refine Submodule.smul_mem _ _ (crystalline_filtration_antitone W T a ?_ (hPG i))
      have := (hlev i).1
      show (H : ℤ) - ((H : ℤ) - h i).toNat ≤ h i
      omega
    · have e1 : α i s = (A.Hs a (e + 1) s : ℤ) := by simp only [α, if_neg (by omega : s ≠ 0)]
      rw [e1]
      exact Formalism.MainNotions.UnusedSlot80.LevC.dvO_filLow W C.hbij A hA c' hc' T hT b hb (e + 1) s hs (c₀ i)
  ·
    have hδ : ∀ m', ∑ i, Q' (i, m') * P' (i, m) =
        if m = m' then ((PD.p : ℕ) : O) ^ (κ1 + κ2) else 0 := by
      intro m'
      apply hinj
      have h1 := congrFun (hPQ (Pi.single m' 1)) m
      have h2 : ∀ i, ∑ m'', Q i m'' * (Pi.single m' (1 : LL) : Fin d → LL) m'' = Q i m' := by
        intro i; simp [Pi.single_apply]
      simp only [h2, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp_rw [map_mul, hQ', hP']
      have h3 : ∑ i, (PD.p : LL) ^ κ2 * Q i m' * ((PD.p : LL) ^ κ1 * P i m) =
          (PD.p : LL) ^ (κ1 + κ2) * ∑ i, Q i m' * P i m := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [h3, ← h1]
      by_cases hmm : m = m'
      · subst hmm; simp
      · simp [hmm, Pi.single_apply, Ne.symm hmm]
    show lE W (κ1 + κ2) * f m = ∑ i, g i * algebraMap O W.EE (c₀ i m)
    simp only [g, c₀, Finset.sum_mul]
    rw [Finset.sum_comm]
    have h4 : ∀ m', ∑ i, algebraMap O W.EE (Q' (i, m')) * f m' * algebraMap O W.EE (P' (i, m)) =
        f m' * algebraMap O W.EE (∑ i, Q' (i, m') * P' (i, m)) := by
      intro m'
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_mul]; ring
    simp_rw [h4, hδ]
    rw [Finset.sum_eq_single m]
    · simp [lE, mul_comm]
    · intro m' _ hm'; simp [Ne.symm hm']
    · intro h0; exact absurd (Finset.mem_univ m) h0

end Formalism.MainNotions.UnusedSlot80.CrD
end
end

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.CrC

open Formalism.MainNotions.N.Pv.LocalLengthBound.Ser PowerSeries

variable {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

theorem smulS_delta (g : PowerSeries LL) (w : V) (j : ℕ) :
    smulS g (fun k : ℤ => if k = 0 then w else 0) (j : ℤ) = coeff j g • w := by
  have hLB : LB 0 (fun k : ℤ => if k = 0 then w else 0) := by
    intro k hk
    simp [ne_of_lt hk]
  rw [smulS_eq_sum hLB g (j : ℤ) (j + 1) (by omega)]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    rw [if_neg (by omega)]
    simp
  · intro hj
    simp at hj

theorem LB_delta (w : V) : LB 0 (fun k : ℤ => if k = 0 then w else 0) := by
  intro k hk
  simp [ne_of_lt hk]

theorem LB_fsum {ι : Type} (s : Finset ι) {m : ℤ} (F : ι → ℤ → V) (hF : ∀ i, LB m (F i)) :
    LB m (∑ i ∈ s, F i) := by
  refine Finset.induction_on s (fun k _ => by simp) ?_
  intro a s ha ih
  rw [Finset.sum_insert ha]
  exact LB_add (hF a) ih

theorem smulS_fsum {ι : Type} (s : Finset ι) (g : PowerSeries LL) {m : ℤ} (F : ι → ℤ → V)
    (hF : ∀ i, LB m (F i)) : smulS g (∑ i ∈ s, F i) = ∑ i ∈ s, smulS g (F i) := by
  refine Finset.induction_on s ?_ ?_
  · funext k
    simp [smulS]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, smulS_add (hF a) (LB_fsum s F hF), ih]

theorem smulS_shift (g : PowerSeries LL) {m : ℤ} {F : ℤ → V} (hF : LB m F) (H : ℕ) :
    smulS (X ^ H * g) F = fun r => smulS g F (r - H) := by
  rw [smulS_mul hF, smulS_X_pow (LB_smulS hF g)]

theorem LB_of_unit {U : PowerSeries LL} (hU : constantCoeff U ≠ 0) {m N : ℤ} {F : ℤ → V} (hF : LB m F)
    (h : LB N (smulS U F)) : LB N F := by
  have h2 := LB_smulS h U⁻¹
  rwa [smulS_inv hF U hU] at h2

theorem vanish_of_XU {U : PowerSeries LL} (hU : constantCoeff U ≠ 0) {m : ℤ} {F : ℤ → V} (hF : LB m F)
    (H : ℕ) (N : ℤ) (h : ∀ r < N + H, smulS (X ^ H * U) F r = 0) : LB N F := by
  apply LB_of_unit hU hF
  intro r hr
  have := h (r + H) (by omega)
  rw [smulS_shift U hF H] at this
  simpa using this

end Formalism.MainNotions.UnusedSlot80.CrC
end
end

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.CrC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup PowerSeries TensorProduct
  Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)
    (levB : ∀ T : LocLat G Qp LL O, ZMod n → LL → ↥(W.N T) →+ (ℤ → T.V ⊗[Qp] B))

theorem φD_smulA' (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

theorem lA_eq (t : ℕ) : lA W ^ t = algebraMap O (LetA O n) (((PD.p : ℕ) : O) ^ t) := by
  simp [lA, map_pow, map_natCast]

theorem frobenius_power_zero_eq_q : ps W 0 = Formalism.MainNotions.WachCoordinates.qP W := by
  rw [Formalism.MainNotions.UnusedSlot80.LevC.ps_zero]; rfl

variable [IsDomain O] [NeZero n]

theorem fil_of_rep (C : Formalism.MainNotions.UnusedSlot80.LevC.Ctx W) (Ti : Formalism.MainNotions.UnusedSlot80.LevE.Comparison₂ W levB)
    (E1 : Formalism.MainNotions.UnusedSlot80.LevE.ExpFrame0 W levB) (E2 : Formalism.MainNotions.UnusedSlot80.LevE.ExpNoNeg0 W levB)
    (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts)
    (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hb : IsHor W T c' b sol) (e : ℕ) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (x : W.DD T) (k : ℕ) (f : Fin d → W.EE) (u : Fin d → LetA O n)
    (hf : ∀ m, algebraMap (LetA O n) W.EE (ps W 0 ^ A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0) * f m =
      algebraMap (LetA O n) W.EE (letE (c' + ((e + 1 : ℕ) : ZMod n)) *
        (W.π₀ * Formalism.MainNotions.UnusedSlot80.LevC.LamUp W A c' e) * u m))
    (hr : RepVV W T c' (e + 1) (A.M PD.p) (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1)) b sol
      (lA W ^ k • x) f)
    (hx : InFNc W T (c' + ((e + 1 : ℕ) : ZMod n)) 1 x) :
    ∀ j : ℕ, (j : ℤ) < 2 * (A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 : ℤ) →
      dv W T (e + 1) b (fun m => coeff j (W.lev (c' + ((e + 1 : ℕ) : ZMod n)) ζ
        (W.π₀ * Formalism.MainNotions.UnusedSlot80.LevC.LamUp W A c' e * u m))) ∈
        FilS W T (c' + ((e + 1 : ℕ) : ZMod n)) 0
          ((A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0 : ℤ) - j) := by
  set a : ZMod n := c' + ((e + 1 : ℕ) : ZMod n) with ha
  set H : ℕ := A.Hs a (e + 1) 0 with hH
  set LU := Formalism.MainNotions.UnusedSlot80.LevC.LamUp W A c' e with hLU
  set Λe := abelian₂ W A (c' + (e : ZMod n)) e with hΛe
  have hp : (PD.p : LL) ≠ 0 := Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W
  obtain ⟨κ, κ', Hh, a', hHh, ha', hP⟩ := hr
  obtain ⟨y, hyP, hyeq⟩ := hP
  obtain ⟨x0, hx0, -, hxx⟩ := hx
  have hxN : x ∈ W.N T := by rw [hxx, one_smul]; exact hx0.1
  have hΛ : abelian₂ W A a (e + 1) = ps W 0 ^ H * LU := Formalism.MainNotions.UnusedSlot80.LevC.lam_succ W A c' e
  let U : Fin d → LetA O n := fun m => letE a * (W.π₀ * LU) * u m
  have ha'U : ∀ m, a' m = LU * U m := by
    intro m
    apply W.EE_inj
    rw [← (ha' m).2, hΛ, map_mul, map_mul, mul_comm (algebraMap (LetA O n) W.EE (ps W 0 ^ H)), mul_assoc,
      hf m]
  obtain ⟨w, hw⟩ := C.hR.2.2.2.2.1
  rw [Formalism.MainNotions.UnusedSlot80.ToolsR.eat_qP] at hw
  have hq : W.q = (w : LetA O n) * ps W 0 := by rw [hw, frobenius_power_zero_eq_q]
  have hφ : ∀ z, W.φD T (Λe • ((W.φD T) ^ e) z) = LU • ((W.φD T) ^ (e + 1)) z := by
    intro z
    rw [φD_smulA', Formalism.MainNotions.UnusedSlot80.PhiPowers.pow_apply_succ]
    rfl
  have hZmem : ∀ z, Formalism.MainNotions.LiftingTheory.InNΔi W T c' z → W.q ^ H • W.φD T (Λe • ((W.φD T) ^ e) z) ∈ W.N T := by
    intro z hz
    have hin := Formalism.MainNotions.UnusedSlot80.ArcC.arc_up W C.hs C.hR C.h5 A hA c' hc' (e + 1) T hT
      (((W.φD T) ^ (e + 1)) z) (by simpa using Formalism.MainNotions.UnusedSlot80.Relay2.Pp_gen W T c' (e + 1) W.AΔ.one_mem hz)
    obtain ⟨y1, hy1, -, hy1e⟩ := hin
    have e1 : W.q ^ H • W.φD T (Λe • ((W.φD T) ^ e) z) =
        ((w : LetA O n) ^ H) • (abelian₂ W A a (e + 1) • ((W.φD T) ^ (e + 1)) z) := by
      rw [hφ, hq, hΛ, smul_smul, smul_smul, mul_pow]; congr 1; ring
    rw [e1, hy1e, one_smul]
    exact (W.N T).smul_mem _ hy1.1
  set μ : LetA O n := W.q ^ H * LU with hμ
  have hμφ : ∀ z, μ • ((W.φD T) ^ (e + 1)) z = W.q ^ H • W.φD T (Λe • ((W.φD T) ^ e) z) := by
    intro z; rw [hφ, hμ, smul_smul]

  have hPy : ∀ z ∈ Pp W T c' (e + 1), ∃ hN : μ • z ∈ W.N T, ∀ r : ℤ, r < H →
      levB T a ζ ⟨μ • z, hN⟩ r = 0 := by
    refine Formalism.MainNotions.UnusedSlot80.Relay2.Pp_ind W T c' (e + 1) _ ?_ ?_ ?_ ?_
    · refine ⟨by rw [smul_zero]; exact (W.N T).zero_mem, fun r _ => ?_⟩
      have : (⟨μ • (0 : W.DD T), by rw [smul_zero]; exact (W.N T).zero_mem⟩ : ↥(W.N T)) = 0 :=
        Subtype.ext (by simp)
      rw [this, map_zero]; rfl
    · rintro x1 y1 ⟨h1, v1⟩ ⟨h2, v2⟩
      refine ⟨by rw [smul_add]; exact (W.N T).add_mem h1 h2, fun r hr => ?_⟩
      have : (⟨μ • (x1 + y1), by rw [smul_add]; exact (W.N T).add_mem h1 h2⟩ : ↥(W.N T)) =
          ⟨μ • x1, h1⟩ + ⟨μ • y1, h2⟩ := Subtype.ext (by simp [smul_add])
      rw [this, map_add (f := _), Pi.add_apply, v1 r hr, v2 r hr, add_zero]
    · rintro x1 ⟨h1, v1⟩
      refine ⟨by rw [smul_neg]; exact (W.N T).neg_mem h1, fun r hr => ?_⟩
      have : (⟨μ • (-x1), by rw [smul_neg]; exact (W.N T).neg_mem h1⟩ : ↥(W.N T)) =
          -⟨μ • x1, h1⟩ := Subtype.ext (by simp [smul_neg])
      rw [this, map_neg, Pi.neg_apply, v1 r hr, neg_zero]
    · intro a0 ha0 z hz
      have hZ := hZmem z hz
      have e1 : μ • (a0 • ((W.φD T) ^ (e + 1)) z) = a0 • (W.q ^ H • W.φD T (Λe • ((W.φD T) ^ e) z)) := by
        rw [← hμφ, smul_comm]
      have hN : μ • (a0 • ((W.φD T) ^ (e + 1)) z) ∈ W.N T := by rw [e1]; exact (W.N T).smul_mem _ hZ
      refine ⟨hN, fun r hr => ?_⟩
      have e2 : (⟨μ • (a0 • ((W.φD T) ^ (e + 1)) z), hN⟩ : ↥(W.N T)) = a0 • ⟨_, hZ⟩ :=
        Subtype.ext e1
      rw [e2, Formalism.MainNotions.UnusedSlot80.LevE.levB_smul W levB Ti.hEq Ti.hsupp]
      have hLB : LB (H : ℤ) (levB T a ζ ⟨_, hZ⟩) := fun r' hr' =>
        E2 A hA c' hc' T hT e ζ hζ z hz H hZ r' hr'
      exact LB_smulS hLB _ r hr
  have hHhN : ∀ m, Formalism.MainNotions.LiftingTheory.InNΔi W T c' (Hh m) := fun m =>
    Formalism.MainNotions.UnusedSlot80.LevE.hor_mem (W := W) T c' b hb.1 sol C.hR.1 (A.M PD.p) κ m (hHh m)
  have hZ : ∀ m, W.q ^ H • W.φD T (Λe • ((W.φD T) ^ e) (Hh m)) ∈ W.N T := fun m => hZmem _ (hHhN m)
  obtain ⟨hYN, hYv⟩ := hPy y hyP

  have key : (μ * LU * (lA W ^ (κ' + κ + k) * ps W 0 ^ H)) • (⟨x, hxN⟩ : ↥(W.N T)) =
      ∑ m, (lA W ^ κ' * LU * U m) • (⟨_, hZ m⟩ : ↥(W.N T)) +
        (W.π₀ * abelian₂ W A a (e + 1) ^ 2) • (⟨μ • y, hYN⟩ : ↥(W.N T)) := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_sum]
    simp_rw [← hμφ]
    have hsum : ∑ m, (lA W ^ κ' * LU * U m) • (μ • ((W.φD T) ^ (e + 1)) (Hh m)) =
        (lA W ^ κ' * μ) • ∑ m, a' m • ((W.φD T) ^ (e + 1)) (Hh m) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [ha'U m, smul_smul, smul_smul]; congr 1; ring
    rw [hsum]
    rw [hΛ] at hyeq ⊢
    have h1 : lA W ^ κ' • ∑ m, a' m • ((W.φD T) ^ (e + 1)) (Hh m) =
        lA W ^ κ' • (lA W ^ κ • (ps W 0 ^ H * LU) • (lA W ^ k • x)) -
          (W.π₀ * (ps W 0 ^ H * LU) ^ 2) • y := by
      rw [← hyeq, smul_sub, sub_sub_cancel]
    rw [mul_smul (lA W ^ κ') μ, smul_comm (lA W ^ κ') μ, h1, smul_sub,
      smul_comm (W.π₀ * (ps W 0 ^ H * LU) ^ 2) μ y, sub_add_cancel]
    simp only [smul_smul]
    congr 1
    ring
  have hL := congrArg (levB T a ζ) key
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_add (f := _), map_sum] at hL
  simp only [Formalism.MainNotions.UnusedSlot80.LevE.levB_smul W levB Ti.hEq Ti.hsupp] at hL
  obtain ⟨mx, hmx⟩ := Ti.hsupp T a ζ ⟨x, hxN⟩
  let F' : Fin d → ℤ → T.V ⊗[Qp] B := fun m r => if r = 0 then ((PD.p : LL) ^ κ) •
    ((φVB PD (LL := LL) (V := T.V)) ^ (e + 1)) (cmpD W T (b m)) else 0
  have hF'LB : ∀ m, LB 0 (F' m) := fun m => LB_delta _
  have hHh' : H ≤ A.h := by
    simp only [hH, ArcP.Hs]
    split_ifs
    · exact hA.2.2.2.2.2.1
    · exact le_rfl
  have hM : 3 * (H : ℤ) ≤ (((PD.p - 1) * A.M PD.p : ℕ) : ℤ) + H := by
    have h2 : 2 * A.h < (PD.p - 1) * A.M PD.p := by
      unfold ArcP.M
      exact Nat.lt_mul_div_succ _ (by have := PD.hp.two_le; omega)
    have h3 : 2 * H < (PD.p - 1) * A.M PD.p := by omega
    omega
  have hfr : ∀ m, ∀ r < 3 * (H : ℤ), levB T a ζ ⟨_, hZ m⟩ r =
      smulS (W.lev a ζ (W.q ^ H * LU)) (F' m) r := by
    intro m r hr
    exact E1 A hA c' hc' T hT b sol hb e ζ hζ (A.M PD.p) κ m (Hh m) (hHh m) H (hZ m) r (by omega)
  have hterm : ∀ m, ∀ r < 3 * (H : ℤ),
      smulS (W.lev a ζ (lA W ^ κ' * LU * U m)) (levB T a ζ ⟨_, hZ m⟩) r =
      smulS (W.lev a ζ (W.q ^ H * LU * LU)) (smulS (W.lev a ζ (lA W ^ κ' * U m)) (F' m)) r := by
    intro m r hr
    obtain ⟨mm, hmm⟩ := Ti.hsupp T a ζ ⟨_, hZ m⟩
    have hA1 : LB (min mm 0) (levB T a ζ ⟨_, hZ m⟩) := LB_mono hmm (min_le_left _ _)
    have hA2 : LB (min mm 0) (smulS (W.lev a ζ (W.q ^ H * LU)) (F' m)) :=
      LB_mono (LB_smulS (hF'LB m) _) (min_le_right _ _)
    rw [Formalism.MainNotions.UnusedSlot80.LevE.smulS_congr_lt hA1 hA2 _ (3 * H) (hfr m) r hr]
    rw [← smulS_mul (hF'LB m), ← smulS_mul (hF'LB m), ← map_mul, ← map_mul,
      show lA W ^ κ' * LU * U m * (W.q ^ H * LU) = W.q ^ H * LU * LU * (lA W ^ κ' * U m) by ring]

  obtain ⟨S, hS0, hSq⟩ := Formalism.MainNotions.UnusedSlot80.DivLevR.lev_qP_X (W := W) C.hR a ζ hζ
  have hps0 : W.lev a ζ (ps W 0) = X * S := by rw [frobenius_power_zero_eq_q]; exact hSq
  have hcorr : ∀ r < 3 * (H : ℤ),
      smulS (W.lev a ζ (W.π₀ * abelian₂ W A a (e + 1) ^ 2)) (levB T a ζ ⟨μ • y, hYN⟩) r = 0 := by
    intro r hr
    have hYLB : LB (H : ℤ) (levB T a ζ ⟨μ • y, hYN⟩) := fun r' hr' => hYv r' hr'
    have e1 : W.lev a ζ (W.π₀ * abelian₂ W A a (e + 1) ^ 2) =
        X ^ (2 * H) * (W.lev a ζ W.π₀ * S ^ (2 * H) * W.lev a ζ LU ^ 2) := by
      rw [hΛ, map_mul, map_pow, map_mul, map_pow, hps0]; ring
    rw [e1, smulS_shift _ hYLB]
    exact LB_smulS hYLB _ _ (by omega)

  obtain ⟨u0, hu0, hu0c⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.lev_q_simple W a ζ hζ
  have hLUc : constantCoeff (W.lev a ζ LU) ≠ 0 := by
    have := Formalism.MainNotions.UnusedSlot80.CrD.cc_lev_piLamUp W C.hR A c' e a ζ hζ
    rw [map_mul, map_mul] at this
    exact right_ne_zero_of_mul this
  set Dd : ℤ → T.V ⊗[Qp] B := smulS (W.lev a ζ (lA W ^ (κ' + κ + k) * ps W 0 ^ H)) (levB T a ζ ⟨x, hxN⟩) -
    ∑ m, smulS (W.lev a ζ (lA W ^ κ' * U m)) (F' m) with hDd
  have hGLB : ∀ m, LB (min mx 0) (smulS (W.lev a ζ (lA W ^ κ' * U m)) (F' m)) := fun m =>
    LB_mono (LB_smulS (hF'LB m) _) (min_le_right _ _)
  have hXLB : LB (min mx 0) (smulS (W.lev a ζ (lA W ^ (κ' + κ + k) * ps W 0 ^ H)) (levB T a ζ ⟨x, hxN⟩)) :=
    LB_smulS (LB_mono hmx (min_le_left _ _)) _
  have hDLB : LB (min mx 0) Dd := LB_sub hXLB (LB_fsum _ _ hGLB)
  have hDv : LB (2 * (H : ℤ)) Dd := by
    have hU : constantCoeff (u0 ^ H * W.lev a ζ LU * W.lev a ζ LU) ≠ 0 := by
      rw [map_mul, map_mul, map_pow]
      exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ hu0c) hLUc) hLUc
    apply vanish_of_XU hU hDLB H (2 * H)
    intro r hr
    have e1 : X ^ H * (u0 ^ H * W.lev a ζ LU * W.lev a ζ LU) = W.lev a ζ (W.q ^ H * LU * LU) := by
      rw [map_mul, map_mul, map_pow, hu0]; ring
    rw [e1, hDd, smulS_sub hXLB (LB_fsum _ _ hGLB), smulS_fsum _ _ _ hGLB, Pi.sub_apply, Finset.sum_apply]
    have hl := congrFun hL r
    simp only [Pi.add_apply, Finset.sum_apply] at hl
    rw [hcorr r (by omega), add_zero] at hl
    have e2 : smulS (W.lev a ζ (W.q ^ H * LU * LU))
        (smulS (W.lev a ζ (lA W ^ (κ' + κ + k) * ps W 0 ^ H)) (levB T a ζ ⟨x, hxN⟩)) r =
        smulS (W.lev a ζ (μ * LU * (lA W ^ (κ' + κ + k) * ps W 0 ^ H))) (levB T a ζ ⟨x, hxN⟩) r := by
      rw [← smulS_mul hmx, ← map_mul]
    rw [e2, hl, sub_eq_zero]
    exact Finset.sum_congr rfl fun m _ => hterm m r (by omega)

  intro j hj
  have hLv : ∀ i : ℤ, levB T a ζ ⟨x, hxN⟩ i ∈ FilS W T a 0 (0 - i) := by
    intro i
    have h := (h4 T hT.1 a 0 ζ (by simpa using hζ)).1 ⟨x, hxN⟩ i
    rw [Ti.hEq] at h
    rw [zero_sub]
    exact Formalism.MainNotions.UnusedSlot80.LevR.mem_of_map_ιV (PD := PD) (S := FilS W T a 0 (-i)) h
  have hDj := hDv j hj
  rw [hDd, Pi.sub_apply, sub_eq_zero, Finset.sum_apply] at hDj
  have e1 : W.lev a ζ (lA W ^ (κ' + κ + k) * ps W 0 ^ H) =
      X ^ H * (W.lev a ζ (lA W ^ (κ' + κ + k)) * S ^ H) := by
    simp only [map_mul, map_pow, hps0]; ring
  have hmemL : smulS (W.lev a ζ (lA W ^ (κ' + κ + k) * ps W 0 ^ H)) (levB T a ζ ⟨x, hxN⟩) j ∈
      FilS W T a 0 ((H : ℤ) - j) := by
    rw [e1, smulS_shift _ hmx]
    have := Dg_smulS (Formalism.MainNotions.UnusedSlot80.CrD.crystalline_filtration_antitone W T a) hmx hLv
      (W.lev a ζ (lA W ^ (κ' + κ + k)) * S ^ H) ((j : ℤ) - H)
    rwa [show (0 : ℤ) - ((j : ℤ) - H) = (H : ℤ) - j by ring] at this
  rw [hDj] at hmemL
  have e2 : ∀ m, smulS (W.lev a ζ (lA W ^ κ' * U m)) (F' m) j =
      ((PD.p : LL) ^ κ' * (PD.p : LL) ^ κ) • (coeff j (W.lev a ζ (W.π₀ * LU * u m)) •
        ((φVB PD (LL := LL) (V := T.V)) ^ (e + 1)) (cmpD W T (b m))) := by
    intro m
    show smulS _ (fun r : ℤ => if r = 0 then _ else 0) (j : ℤ) = _
    rw [smulS_delta, lA_eq, map_mul, AlgHom.commutes, Formalism.MainNotions.UnusedSlot80.CrD.coeff_alg_mul, map_pow, map_natCast]
    have hU : W.lev a ζ (U m) = W.lev a ζ (W.π₀ * LU * u m) := by
      show W.lev a ζ (letE a * (W.π₀ * LU) * u m) = _
      rw [mul_assoc, Formalism.MainNotions.UnusedSlot80.DivLevR.lev_letE_mul]
    rw [hU, smul_smul, smul_smul]
    congr 1
    ring
  simp_rw [e2] at hmemL
  rw [← Finset.smul_sum] at hmemL
  have hne : ((PD.p : LL) ^ κ' * (PD.p : LL) ^ κ) ≠ 0 := mul_ne_zero (pow_ne_zero _ hp) (pow_ne_zero _ hp)
  have := (Submodule.smul_mem_iff _ hne).mp hmemL
  simpa [dv] using this

end Formalism.MainNotions.UnusedSlot80.CrC
end
end

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.CrC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)
    (levB : ∀ T : LocLat G Qp LL O, ZMod n → LL → ↥(W.N T) →+ (ℤ → T.V ⊗[Qp] B))

variable [IsDomain O] [NeZero n] [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]

theorem level_zero_membership_of_horizontal (C : Formalism.MainNotions.UnusedSlot80.LevC.Ctx W) (Ti : Formalism.MainNotions.UnusedSlot80.LevE.Comparison₂ W levB)
    (E1 : Formalism.MainNotions.UnusedSlot80.LevE.ExpFrame0 W levB) (E2 : Formalism.MainNotions.UnusedSlot80.LevE.ExpNoNeg0 W levB)
    (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W) (hζex : ∃ ζ : LL, IsPrimitiveRoot ζ PD.p) (A : ArcP n) (hA : A.OK)
    (c' : ZMod n) (hc' : c' ∈ A.cuts) (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol) (e : ℕ) :
    Formalism.MainNotions.UnusedSlot80.LevC.LevelZeroModP (W := W) A c' e T b sol := by
  intro x k f _ hr hfr hx
  obtain ⟨ζ, hζ⟩ := hζex
  choose u hu hfu using hfr
  exact Formalism.MainNotions.UnusedSlot80.CrD.secIn_of_fil W C A hA c' hc' T hT b hb.1 e ζ hζ f u hu hfu
    (fil_of_rep W levB C Ti E1 E2 h4 A hA c' hc' T hT b sol hb e ζ hζ x k f u hfu hr hx)

end Formalism.MainNotions.UnusedSlot80.CrC
end
end

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.Crit0

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def LevelMapsCompatible (W : LocWach PD LL O v n) (levB : ∀ T : LocLat G Qp LL O, ZMod n → LL → ↥(W.N T) →+ (ℤ → T.V ⊗[Qp] B))
    [IsDomain O] [NeZero n] : Prop :=
  LevC.Ctx W → LevE.Comparison₂ W levB → LevE.ExpFrame0 W levB → LevE.ExpNoNeg0 W levB → Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W →
    (∃ ζ : LL, IsPrimitiveRoot ζ PD.p) → ∀ A : ArcP n, A.OK → ∀ c' ∈ A.cuts, ∀ T : LocLat G Qp LL O, Win W A T →
      ∀ {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL), IsHor W T c' b sol →
        ∀ e : ℕ, LevC.LevelZeroModP (W := W) A c' e T b sol

end Formalism.MainNotions.UnusedSlot80.Crit0

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

theorem exists_prim_of_good (D : D7) {l : ℕ} [Fact l.Prime] {K LL : FinExt l} (hG : Good K 1 LL) :
    ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l := by
  have hmem : (D.loc l).ζQ 1 ∈ Ks K 1 := by
    apply (le_sup_right : IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ 1) = 1} ≤ Ks K 1)
    apply IntermediateField.subset_adjoin
    show (D.loc l).ζQ 1 ^ (l ^ 1) = 1
    rw [pow_one, (D.loc l).ζQ_succ 0, (D.loc l).ζQ_zero]
  have hLL : (D.loc l).ζQ 1 ∈ LL.1 := hG.2.2.2 (Ks K 1).val ⟨_, hmem⟩
  refine ⟨⟨_, hLL⟩, ?_⟩
  exact IsPrimitiveRoot.of_map_of_injective (f := LL.1.val) (hf := Subtype.val_injective)
    (LevR.root_of_unity_primitive D l)

theorem lev0MpL_of_from (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hAdm : AdmArcA D HW F Cm) (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hW : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL), CaseA K LL → 5 ≤ l →
      haveI := neZero_finrank_max_unramified K
      Crit0.LevelMapsCompatible ((HW l).W K 1 LL hG) ((Cm l).C K 1 LL hG).tie.levB) :
    LevelZeroModPLocal D HW := by
  intro l _ K LL hG hCA h5l A hA c' hc' T hT d b sol hb e
  have := neZero_finrank_max_unramified K
  have C := ctx_of D HW F Cm hAdm l K LL hG hCA h5l
  have Ti := levETie_of D HW F Cm h4 l K LL hG
  have E1 := LevE.expFrame0_of Ti C.hs C.hR C.hp0 C.h5 C.hH C.hCA
  have E2 := LevE.expNoNeg0_of Ti C.hs C.hR C.hp0 C.h5
  have h4' := Strict.p4YL D HW F (levCoeff_of_pt D HW F Cm h4 (points_exist_of_ring_condition D HW F h9)) l K LL hG hCA h5l
  obtain ⟨ζ, hζ⟩ := exists_prim_of_good D hG
  have hζ' : ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ ((D.loc l).PD K).p := ⟨ζ, by rw [(D.loc l).PD_p]; exact hζ⟩
  exact hW l K LL hG hCA h5l C Ti E1 E2 h4' hζ' A hA c' hc' T hT b sol hb e

theorem lev0MpL_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hAdm : AdmArcA D HW F Cm) (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) : LevelZeroModPLocal D HW :=
  lev0MpL_of_from D HW F Cm hAdm h4 h9 fun l _ K LL hG _ _ => by
    haveI := neZero_finrank_max_unramified K
    haveI := eq_sum_herm_smul_frame_of_inW (D.loc l) K LL
    intro C Ti E1 E2 h4' hζ A hA c' hc' T hT d b sol hb e
    exact CrC.level_zero_membership_of_horizontal _ _ C Ti E1 E2 h4' hζ A hA c' hc' T hT b sol hb e

end Formalism.MainNotions.UnusedSlot80
