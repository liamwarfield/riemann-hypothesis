module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ExistsPhiBridge
public import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DvOSmulO
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ProdTwoLevelsEqConst
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLenThreeThickLetters
open scoped TensorProduct

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

namespace ArcLengthThreeFiltration

theorem φVB_inj (T : LocLat G Qp LL O) : Function.Injective (φVB PD (LL := LL) (V := T.V)) := by
  have hφ : Function.Injective (PD.φ.toLinearMap) := by simpa using PD.φ_inj
  have h : ⇑(φVB PD (LL := LL) (V := T.V)) = ⇑(LinearMap.lTensor T.V PD.φ.toLinearMap) := by
    funext x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a c => simp [φVB]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]
  rw [h]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hφ

theorem crisMap_φ {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) (x : T₁.V ⊗[Qp] B) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (φVB PD (LL := LL) (V := T₁.V) x) =
      φVB PD (LL := LL) (V := T₂.V) (Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a c => simp [φVB, Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

variable (W : LocWach PD LL O v n)

theorem dv_succ (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → LL) :
    dv W T (e + 1) b c₀ = φVB PD (LL := LL) (V := T.V) (dv W T e b c₀) := by
  first
  | (simp only [dv, pow_succ', Module.End.mul_apply, map_sum, map_smul]; done)
  | (simp only [dv, pow_succ', LinearMap.mul_apply, map_sum, map_smul]; done)
  | (simp [dv, LinearMap.pow_apply, Function.iterate_succ_apply']; done)
  | (simp [dv, pow_succ']; exact (trivial : True))

theorem dv_add (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ c₁ : Fin d → LL) :
    dv W T e b (c₀ + c₁) = dv W T e b c₀ + dv W T e b c₁ := by
  simp only [dv, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem dv_smul (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (t : LL) (c₀ : Fin d → LL) :
    dv W T e b (t • c₀) = t • dv W T e b c₀ := by
  simp only [dv, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem dv_sum (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) {ι : Type*} (s : Finset ι)
    (c₀ : ι → Fin d → LL) : dv W T e b (∑ i ∈ s, c₀ i) = ∑ i ∈ s, dv W T e b (c₀ i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simpa using dv_smul W T e b 0 0
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, dv_add, ih]

theorem dv_eq_sum (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → LL) :
    dv W T e b c₀ = ∑ m, c₀ m • dv W T e b (Pi.single m 1) := by
  have h : c₀ = ∑ m, c₀ m • (Pi.single m 1 : Fin d → LL) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [h]
  rw [dv_sum]
  simp only [dv_smul]

theorem dvO_eq (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → O) :
    dvO W T e b c₀ = ∑ m, algebraMap O LL (c₀ m) • dv W T e b (Pi.single m 1) := by
  first
  | (unfold dvO; exact dv_eq_sum W T e b _)
  | (simp only [dvO]; exact dv_eq_sum W T e b _)

theorem dvO_single (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (k : Fin d) :
    dvO W T e b (Pi.single k 1) = dv W T e b (Pi.single k 1) := by
  rw [dvO_eq]
  simp [Pi.single_apply, apply_ite (algebraMap O LL), ite_smul]

theorem filS_anti (T : LocLat G Qp LL O) (a : ZMod n) (s : ℕ) {u u' : ℤ} (h : u ≤ u') :
    FilS W T a s u' ≤ FilS W T a s u := by
  unfold FilS
  apply Submodule.map_mono
  apply inf_le_inf_right
  unfold FilCris
  apply inf_le_inf_left
  apply Submodule.comap_mono
  unfold FilV
  have hF : PD.Fil u' ≤ PD.Fil u := antitone_int_of_succ_le PD.Fil_anti h
  intro y hy
  rw [LinearMap.mem_range] at hy
  obtain ⟨z, rfl⟩ := hy
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a c => exact LinearMap.mem_range.mpr ⟨a ⊗ₜ ⟨c.1, hF c.2⟩, by simp⟩
  | add z w hz hw => rw [map_add (f := _)]; exact Submodule.add_mem _ hz hw

theorem filS_zero_iff (T : LocLat G Qp LL O) (a : ZMod n) (u : ℤ) (x : T.V ⊗[Qp] B) :
    x ∈ FilS W T a 0 u ↔ x ∈ FilCris PD T.ρ u ⊓ DcrisL PD T.ρ (W.emb a) := by
  unfold FilS
  simp [pow_zero, Submodule.map_id]
  try rfl

theorem filS_one_of (T : LocLat G Qp LL O) (a : ZMod n) (u : ℤ) (x : T.V ⊗[Qp] B)
    (hx : x ∈ FilS W T a 0 u) : φVB PD (LL := LL) (V := T.V) x ∈ FilS W T (a + 1) 1 u := by
  rw [filS_zero_iff] at hx
  unfold FilS
  rw [pow_one, Nat.cast_one, add_sub_cancel_right]
  exact Submodule.mem_map_of_mem hx

theorem filS_zero_of (T : LocLat G Qp LL O) (a : ZMod n) (u : ℤ) (x : T.V ⊗[Qp] B)
    (hx : φVB PD (LL := LL) (V := T.V) x ∈ FilS W T (a + 1) 1 u) : x ∈ FilS W T a 0 u := by
  rw [filS_zero_iff]
  unfold FilS at hx
  rw [pow_one, Nat.cast_one, add_sub_cancel_right, Submodule.mem_map] at hx
  obtain ⟨y, hy, hyx⟩ := hx
  rw [← φVB_inj T hyx]
  exact hy

theorem repVV_smulA {T : LocLat G Qp LL O} {c' : ZMod n} {e M : ℕ} {Λ : LetA O n} {d : ℕ}
    {b : Fin d → W.DD T} {sol : Fin d → ℕ → Fin d → LL} {x : W.DD T} {f : Fin d → W.EE}
    (h : RepVV W T c' e M Λ b sol x f) {t : LetA O n} (ht : t ∈ W.AΔ) :
    RepVV W T c' e M Λ b sol (t • x) (fun k => algebraMap (LetA O n) W.EE t * f k) := by
  unfold RepVV at h ⊢
  obtain ⟨κ, κ', Hh, a, hH, ha, hIn⟩ := h
  refine ⟨κ, κ', Hh, fun k => t * a k, hH, fun k => ⟨mul_mem ht (ha k).1, ?_⟩, ?_⟩
  · dsimp only
    rw [map_mul, ← (ha k).2]
    ring
  · have he : lA W ^ κ' • (lA W ^ κ • Λ • (t • x) - ∑ k, (t * a k) • ((W.φD T) ^ e) (Hh k)) =
        t • (lA W ^ κ' • (lA W ^ κ • Λ • x - ∑ k, a k • ((W.φD T) ^ e) (Hh k))) := by
      simp only [smul_sub, Finset.smul_sum, smul_smul, mul_comm, mul_assoc, mul_left_comm]
    rw [he]
    exact Formalism.MainNotions.N.FrobeniusPowerSeries.TypesA.inMultiple_smul (ha := ht) (h := hIn)

section ThetaShiftProofs
variable {b w S η : ℕ} {up : ZMod n → Bool} {size : ZMod n → ℕ}

theorem arc_ty [NeZero n] (i : ZMod n) :
    (arcOf b w S η up size).ty i = if up i then .up (size i) else .down (size i) := rfl

theorem arc_thick [NeZero n] (i : ZMod n) : ((arcOf b w S η up size).ty i).thick := by
  rw [arc_ty]
  split <;> rfl

theorem arc_len_three_thick_letters [NeZero n] {c : ZMod n} (hlen : (arcOf b w S η up size).len c = 3) :
    Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size c ∧ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 1) ∧
      ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 2) := by
  unfold arcOf at hlen
  dsimp only at hlen
  have hpos : 0 < sInf {d : ℕ | 1 ≤ d ∧ ¬Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} := by
    rw [hlen]; norm_num
  have hne := Nat.nonempty_of_pos_sInf hpos
  have h3 := Nat.sInf_mem hne
  rw [hlen] at h3
  have hlt : ∀ d : ℕ, 1 ≤ d → d < 3 → Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1) := by
    intro d hd1 hd3
    by_contra hT
    have hle := Nat.sInf_le
      (show d ∈ {d : ℕ | 1 ≤ d ∧ ¬Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} from ⟨hd1, hT⟩)
    rw [hlen] at hle
    omega
  refine ⟨?_, ?_, ?_⟩
  · have h1 := hlt 1 le_rfl (by norm_num)
    rwa [show c - ((1 : ℕ) : ZMod n) + 1 = c by push_cast; ring] at h1
  · have h1 := hlt 2 (by norm_num) (by norm_num)
    rwa [show c - ((2 : ℕ) : ZMod n) + 1 = c - 1 by push_cast; ring] at h1
  · have h1 := h3.2
    rwa [show c - ((3 : ℕ) : ZMod n) + 1 = c - 2 by push_cast; ring] at h1

theorem arc_types [NeZero n] {c : ZMod n} (halt : Alt b η up size) (hD : up (c - 2) = false) :
    up (c - 1) = true ∧ up c = false := by
  unfold Alt at halt
  have h1 := (halt (c - 2)).1
  have h2 := (halt (c - 1)).1
  rw [show c - 2 + 1 = c - 1 by ring, hD] at h1
  rw [show c - 1 + 1 = c by ring] at h2
  have e1 : up (c - 1) = true := by simpa using h1
  refine ⟨e1, ?_⟩
  rw [e1] at h2
  simpa using h2

theorem lam_inner [NeZero n] {c : ZMod n} (hlen : (arcOf b w S η up size).len c = 3) :
    abelian₂ W (arcOf b w S η up size) (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n) + ((2 : ℕ) : ZMod n)) 2 =
      ps W 0 ^ (arcOf b w S η up size).h * ps W 1 ^ (arcOf b w S η up size).G₀ := by
  unfold abelian₂
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  have hs0 : ∀ a : ZMod n, (arcOf b w S η up size).Hs a 2 0 = (arcOf b w S η up size).h := by
    intro a
    unfold Formalism.MainNotions.ArcLiftingSetup.ArcP.Hs
    rw [if_neg]
    rintro (hc | hc)
    · simp only [arcOf] at hc
      split at hc <;> simp at hc
    · norm_num [arcOf] at hc
  have hs1 : ∀ a : ZMod n, (arcOf b w S η up size).Hs a 2 1 = (arcOf b w S η up size).G₀ := by
    intro a
    unfold Formalism.MainNotions.ArcLiftingSetup.ArcP.Hs
    rw [if_pos (Or.inr (by simp [arcOf]))]
  rw [hs0, hs1]

end ThetaShiftProofs

end ArcLengthThreeFiltration
end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

open scoped TensorProduct

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [IsDomain O] [IsDiscreteValuationRing O]

namespace ArcLengthThreeFiltration

open PowerSeries

variable {W : LocWach PD LL O v n} (Br : PhiBridge W)

def ea (a : ZMod n) (F : PowerSeries O) : W.EE :=
  algebraMap (LetA O n) W.EE (letE a * Br.cst F)

theorem letE_mul_self (a : ZMod n) : (letE a : LetA O n) * letE a = letE a := by
  funext i
  simp only [Formalism.BasicNotions.letE, Pi.mul_apply, Pi.single_apply]
  split_ifs <;> simp

theorem ea_add (a : ZMod n) (F F' : PowerSeries O) : ea Br a (F + F') = ea Br a F + ea Br a F' := by
  have h : Br.cst (F + F') = Br.cst F + Br.cst F' := funext fun _ => map_add Br.ι F F'
  unfold Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea
  rw [h, mul_add, map_add (f := _)]

theorem ea_zero (a : ZMod n) : ea Br a 0 = 0 := by
  have h : Br.cst 0 = 0 := funext fun _ => map_zero Br.ι
  unfold Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea
  rw [h, mul_zero, map_zero]

theorem cst_mul_ea (a : ZMod n) (G F : PowerSeries O) :
    algebraMap (LetA O n) W.EE (Br.cst G) * ea Br a F = ea Br a (G * F) := by
  have h : Br.cst (G * F) = Br.cst G * Br.cst F := funext fun _ => map_mul Br.ι G F
  unfold Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea
  rw [← map_mul, h]
  congr 1
  ring

theorem ea_C_mul (a : ZMod n) (x : O) (F : PowerSeries O) :
    ea Br a (C x * F) = algebraMap O W.EE x * ea Br a F := by
  have h1 : Br.cst (C x * F) = algebraMap O (LetA O n) x * Br.cst F := by
    funext i
    show Br.ι (C x * F) = (algebraMap O (LetA O n) x) i * Br.ι F
    rw [← PowerSeries.smul_eq_C_mul, map_smul, Algebra.smul_def]
    rfl
  unfold Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea
  rw [h1, mul_left_comm, map_mul, ← IsScalarTower.algebraMap_apply]

theorem ea_sum (a : ZMod n) {ι : Type*} (s : Finset ι) (F : ι → PowerSeries O) :
    ea Br a (∑ i ∈ s, F i) = ∑ i ∈ s, ea Br a (F i) := by
  have h1 : Br.cst (∑ i ∈ s, F i) = ∑ i ∈ s, Br.cst (F i) := by
    funext j
    rw [Finset.sum_apply]
    exact map_sum Br.ι F s
  unfold Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, Finset.mul_sum, map_sum]

theorem ea_inj (a : ZMod n) {F F' : PowerSeries O} (h : ea Br a F = ea Br a F') : F = F' := by
  unfold Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea at h
  have h1 := congrFun (W.EE_inj h) a
  simp only [Pi.mul_apply, Formalism.BasicNotions.letE, Pi.single_eq_same, one_mul] at h1
  exact Br.inj h1

theorem letE_mul_AΔ (a : ZMod n) {u : LetA O n} (hu : u ∈ W.AΔ) :
    ∃ U : PowerSeries O, letE a * u = letE a * Br.cst U := by
  obtain ⟨U, hU⟩ := Br.range u hu a
  refine ⟨U, ?_⟩
  funext i
  simp only [Pi.mul_apply, Formalism.BasicNotions.letE]
  by_cases h : i = a
  · subst h
    simp only [Pi.single_eq_same, one_mul]
    exact hU
  · simp [Pi.single_apply, h]

theorem inFr_ea (a : ZMod n) {N D : PowerSeries O} {f : W.EE} (h : InFr W a (Br.cst N) (Br.cst D) f) :
    ∃ U : PowerSeries O, algebraMap (LetA O n) W.EE (Br.cst D) * f = ea Br a (N * U) := by
  unfold Formalism.MainNotions.ArcLiftingSetup.InFr at h
  obtain ⟨u, hu, h⟩ := h
  obtain ⟨U, hU⟩ := letE_mul_AΔ Br a hu
  refine ⟨U, ?_⟩
  rw [h]
  unfold Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthThreeFiltration.ea
  congr 1
  have hc : Br.cst (N * U) = Br.cst N * Br.cst U := funext fun _ => map_mul Br.ι N U
  rw [hc]
  calc (letE a : LetA O n) * Br.cst N * u = Br.cst N * ((letE a : LetA O n) * u) := by ring
    _ = Br.cst N * ((letE a : LetA O n) * Br.cst U) := by rw [hU]
    _ = (letE a : LetA O n) * (Br.cst N * Br.cst U) := by ring

theorem p_zero : Br.P.p 0 = X := rfl

theorem ps_cst (s : ℕ) : ps W s = Br.cst (Br.P.p s) := by
  induction s with
  | zero =>
    unfold Formalism.MainNotions.ArcLiftingSetup.ps
    rw [pow_zero, AlgHom.one_apply]
    funext i
    show W.π₀₁ + ((PD.p : ℕ) : PowerSeries O) = Br.ι X
    rw [Br.ι_X, map_natCast]
  | succ s ih =>
    unfold Formalism.MainNotions.ArcLiftingSetup.ps at ih ⊢
    rw [pow_succ', AlgHom.mul_apply, ih]
    funext i
    show W.φ₀ (Br.ι (Br.P.p s)) = Br.ι (Br.P.p (s + 1))
    rw [← Br.ι_φ]
    congr 1
    show Br.P.φ ((Br.P.φ : PowerSeries O → PowerSeries O)^[s] X) = (Br.P.φ : PowerSeries O → PowerSeries O)^[s + 1] X
    rw [Function.iterate_succ_apply']

theorem prod_two_levels_eq_const (F : ℕ → ℕ) :
    (∏ s ∈ Finset.range 2, ps W s ^ F s) = Br.cst (X ^ F 0 * Br.P.p 1 ^ F 1) := by
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
  rw [ps_cst Br, ps_cst Br]
  funext i
  simp only [Pi.mul_apply, Pi.pow_apply]
  show Br.ι X ^ F 0 * Br.ι (Br.P.p 1) ^ F 1 = Br.ι (X ^ F 0 * Br.P.p 1 ^ F 1)
  rw [map_mul, map_pow, map_pow]

theorem toNat_split (m : ℕ) (α : ℤ) (h : -(m : ℤ) ≤ α) :
    m + α.toNat = (-α).toNat + (m + α).toNat := by
  omega

end ArcLengthThreeFiltration
end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.MemPairXIff
noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries
namespace ArcLengthThreeFiltration

open PowerSeries

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

theorem mem_pair_X_iff (a : O) (f : O⟦X⟧) (B : ℕ) :
    f ∈ Ideal.span {C a, (X : O⟦X⟧) ^ B} ↔ ∀ j < B, a ∣ coeff j f := by
  constructor
  · intro hf j hj
    obtain ⟨u, w, huw⟩ := Ideal.mem_span_pair.mp hf
    rw [← huw, map_add (f := _), PowerSeries.coeff_mul_C, PowerSeries.coeff_mul_X_pow', if_neg (by omega), add_zero]
    exact dvd_mul_left _ _
  · intro h
    choose c hc using h
    set g : O⟦X⟧ := PowerSeries.mk fun j => if hj : j < B then c j hj else 0 with hg
    have hdvd : (X : O⟦X⟧) ^ B ∣ f - C a * g := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      rw [map_sub, PowerSeries.coeff_C_mul, hg, PowerSeries.coeff_mk, dite_eq_left hm, ← hc m hm, sub_self]
    obtain ⟨w, hw⟩ := hdvd
    rw [Ideal.mem_span_pair]
    exact ⟨g, w, by linear_combination (-1 : O⟦X⟧) * hw⟩

private theorem exists_unit_natCast_eq_mul_uniformizer_pow_eO {l : ℕ} {ϖ : O} (hϖ : Irreducible ϖ) (hl0 : (l : O) ≠ 0) :
    ∃ u : Oˣ, (l : O) = ↑u * ϖ ^ eO (O := O) l := by
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hl0 hϖ
  have hl' : (l : O) = ↑u⁻¹ * ϖ ^ n := by
    rw [← hu, mul_comm (l : O), ← mul_assoc, Units.inv_mul, one_mul]
  have he : eO (O := O) l = n := by
    unfold eO
    rw [IsDiscreteValuationRing.addVal_def (l : O) u⁻¹ hϖ n hl']
    simp
  exact ⟨u⁻¹, by rw [he]; exact hl'⟩

theorem pair_l_eq {l : ℕ} [Fact l.Prime] {ϖ : O} (hϖ : Irreducible ϖ) (hl0 : (l : O) ≠ 0) (s : ℕ)
    (g : O⟦X⟧) :
    Ideal.span {(C (l : O) : O⟦X⟧) ^ s, g} = Ideal.span {C ϖ ^ (eO (O := O) l * s), g} := by
  obtain ⟨u, hu⟩ := exists_unit_natCast_eq_mul_uniformizer_pow_eO hϖ hl0
  have hC : (C (l : O) : O⟦X⟧) ^ s = C ϖ ^ (eO (O := O) l * s) * C ((u : O) ^ s) := by
    rw [hu, map_mul, map_pow, map_pow, mul_pow, ← pow_mul, mul_comm]
  rw [Ideal.span_insert, Ideal.span_insert, hC,
    Ideal.span_singleton_mul_right_unit (((Units.isUnit u).pow s).map C)]

theorem eO_pos {l : ℕ} [Fact l.Prime] {ϖ : O} (hϖ : Irreducible ϖ) (hl0 : (l : O) ≠ 0)
    (hl : (l : O) ∈ IsLocalRing.maximalIdeal O) : 1 ≤ eO (O := O) l := by
  obtain ⟨u, hu⟩ := exists_unit_natCast_eq_mul_uniformizer_pow_eO hϖ hl0
  by_contra h0
  have h0' : eO (O := O) l = 0 := by omega
  rw [h0', pow_zero, mul_one] at hu
  have hn := (IsLocalRing.mem_maximalIdeal _).mp hl
  rw [hu] at hn
  exact hn (Units.isUnit u)

theorem cancel_l {l : ℕ} [Fact l.Prime] {ϖ : O} (hϖ : Irreducible ϖ) (hl0 : (l : O) ≠ 0) (k s B : ℕ)
    (hks : k ≤ s) (f : O⟦X⟧)
    (h : C (l : O) ^ k * f ∈ Ideal.span {C ϖ ^ (eO (O := O) l * s), (X : O⟦X⟧) ^ B}) :
    f ∈ Ideal.span {C ϖ ^ (eO (O := O) l * (s - k)), (X : O⟦X⟧) ^ B} := by
  obtain ⟨u, hu⟩ := exists_unit_natCast_eq_mul_uniformizer_pow_eO hϖ hl0
  rw [← map_pow] at h ⊢
  rw [mem_pair_X_iff] at h ⊢
  intro j hj
  have hj' := h j hj
  rw [← map_pow, PowerSeries.coeff_C_mul, hu] at hj'
  have hpow : ϖ ^ (eO (O := O) l * s) = ϖ ^ (eO (O := O) l * (s - k)) * ϖ ^ (eO (O := O) l * k) := by
    rw [← pow_add, ← mul_add, Nat.sub_add_cancel hks]
  have hrw : ((u : O) * ϖ ^ eO (O := O) l) ^ k * coeff j f =
      (((u ^ k : Oˣ) : O) * coeff j f) * ϖ ^ (eO (O := O) l * k) := by
    rw [Units.val_pow_eq_pow_val, mul_pow, ← pow_mul]
    ring
  rw [hpow, hrw] at hj'
  have hne : ϖ ^ (eO (O := O) l * k) ≠ 0 := pow_ne_zero _ hϖ.ne_zero
  exact Units.dvd_mul_left.mp ((mul_dvd_mul_iff_right hne).mp hj')

theorem content_notMem {l : ℕ} [Fact l.Prime] (P : PhiData O l) (σ A S y b₁ η s₁ : ℕ)
    (hs : 2 * σ < s₁) (hk : A + s₁ - 1 < b₁ - η) (hy1 : 1 ≤ y)
    (hc2 : ¬ (((s₁ : ℝ) - 2 * σ) ≤ max 0 ((y : ℝ) - ((b₁ - η - (A + s₁ - 1) : ℕ) : ℝ) / l + 2 + Real.logb l y))) :
    C (l : O) ^ (2 * σ) * (X - C (l : O)) ^ A * X ^ S * P.p 1 ^ y ∉
      Ideal.span {(C (l : O) : O⟦X⟧) ^ s₁, (X : O⟦X⟧) ^ (b₁ + S - η)} := by
  intro hmem
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hs1 : 1 ≤ s₁ := by omega
  set t := s₁ - 2 * σ with ht
  have ht1 : 1 ≤ t := by omega
  set B := b₁ - η - (A + s₁ - 1) with hBdef
  have hB : 1 ≤ B := by omega
  have hre : C (l : O) ^ (2 * σ) * (X - C (l : O)) ^ A * X ^ S * P.p 1 ^ y =
      C (l : O) ^ (2 * σ) * ((X - C (l : O)) ^ A * X ^ S * P.p 1 ^ y) := by ring
  rw [hre, pair_l_eq hϖ P.hl0 s₁] at hmem
  have hG := cancel_l hϖ P.hl0 (2 * σ) s₁ (b₁ + S - η) (by omega) _ hmem
  rw [← ht, ← pair_l_eq hϖ P.hl0 t] at hG
  obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp (PhiData.X_pow_mem_span_q_pow_l_pow (l := l) hϖ A t ht1)
  have hK : (X : O⟦X⟧) ^ (A + t - 1 + S) * P.p 1 ^ y ∈
      Ideal.span {(C (l : O) : O⟦X⟧) ^ t, (X : O⟦X⟧) ^ (b₁ + S - η)} := by
    have hexp : (X : O⟦X⟧) ^ (A + t - 1 + S) * P.p 1 ^ y =
        a * ((X - C (l : O)) ^ A * X ^ S * P.p 1 ^ y) + (b * X ^ S * P.p 1 ^ y) * C (l : O) ^ t := by
      rw [pow_add, ← hab]
      ring
    rw [hexp]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hG) (Ideal.mul_mem_left _ _ ?_)
    exact Ideal.subset_span (Set.mem_insert _ _)
  rw [← map_pow, mem_pair_X_iff] at hK
  have hP : P.p 1 ^ y ∈ Ideal.span {(C (l : O) : O⟦X⟧) ^ t, (X : O⟦X⟧) ^ B} := by
    rw [← map_pow, mem_pair_X_iff]
    intro j hj
    have h2 := hK (j + (A + t - 1 + S)) (by omega)
    rwa [PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel] at h2
  rw [pair_l_eq hϖ P.hl0 t] at hP
  have hdX : IsDist ((X : O⟦X⟧) ^ B) := by
    unfold IsDist
    rw [map_pow, PowerSeries.map_X]
    exact pow_ne_zero _ PowerSeries.X_ne_zero
  have hle := (mem_iff_le_cont hϖ hdX _ _).mp hP
  obtain ⟨hne, hbd⟩ := PhiData.constant_le_rpow_of_three_le P hϖ B y hB hy1
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
  rw [← hn] at hle hbd
  have hle' : eO (O := O) l * t ≤ n := by exact_mod_cast hle
  have he := eO_pos hϖ P.hl0 P.hl
  have hle'' : ((eO (O := O) l : ℝ) * t) ≤ (eO (O := O) l : ℝ) *
      max 0 ((y : ℝ) - B / l + 2 + Real.logb l y) := by
    have : ((eO (O := O) l * t : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hle'
    simp only [ENat.toNat_coe] at hbd
    push_cast at this
    linarith
  have hepos : (0 : ℝ) < eO (O := O) l := by exact_mod_cast he
  have htle := le_of_mul_le_mul_left hle'' hepos
  apply hc2
  have : ((t : ℕ) : ℝ) = (s₁ : ℝ) - 2 * σ := by
    rw [ht]
    push_cast [show 2 * σ ≤ s₁ by omega]
    ring
  rw [← this]
  exact htle

end ArcLengthThreeFiltration
end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

open scoped TensorProduct

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

namespace ArcLengthThreeFiltration

open PowerSeries

variable {W : LocWach PD LL O v n} (Br : PhiBridge W)

theorem dvO_smulO (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (r : O) (x : Fin d → O) :
    dvO W T e b (fun k => r * x k) = algebraMap O LL r • dvO W T e b x := by
  unfold dvO dv
  simp only [map_mul, mul_smul, Finset.smul_sum]

theorem dvO_lin (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) {I : ℕ} (t : Fin I → O)
    (c : Fin I → Fin d → O) :
    dvO W T e b (fun k => ∑ i, t i * c i k) = ∑ i, algebraMap O LL (t i) • dvO W T e b (c i) := by
  unfold dvO dv
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, Finset.sum_smul, mul_smul, Finset.smul_sum]
  exact Finset.sum_comm

theorem isDist_XP (i j : ℕ) : IsDist ((X : PowerSeries O) ^ i * Br.P.p 1 ^ j) := by
  unfold IsDist PhiData.p
  simp only [Function.iterate_one]
  have hp1 : 1 ≤ PD.p := Nat.pos_of_ne_zero (fun h => Br.P.hl0 (by rw [h, Nat.cast_zero]))
  have hC : (PowerSeries.C (PD.p : O) : O⟦X⟧) = (PD.p : O⟦X⟧) := map_natCast _ _
  have h0 := Br.P.hφ0
  rw [hC, map_sub, map_natCast] at h0
  have hφX : Br.P.φ X = Br.P.u * (X - (PD.p : O⟦X⟧)) * X ^ (PD.p - 1) + (PD.p : O⟦X⟧) := by
    rw [← h0]
    ring
  have hp0 : ((PD.p : ℕ) : (IsLocalRing.ResidueField O)⟦X⟧) = 0 := by
    have h1 : ((PD.p : ℕ) : IsLocalRing.ResidueField O) = 0 := by
      rw [← map_natCast (IsLocalRing.residue O)]
      exact (IsLocalRing.residue_eq_zero_iff _).mpr Br.P.hl
    rw [← map_natCast (PowerSeries.C (R := IsLocalRing.ResidueField O)), h1, map_zero]
  have hm : (Br.P.φ X).map (IsLocalRing.residue O) = (Br.P.u.map (IsLocalRing.residue O)) * X ^ PD.p := by
    rw [hφX, map_add (f := _), map_mul, map_mul, map_pow, map_sub, PowerSeries.map_X, map_natCast, hp0, sub_zero,
      add_zero, mul_assoc, ← pow_succ', Nat.sub_add_cancel hp1]
  have hu0 : Br.P.u.map (IsLocalRing.residue O) ≠ 0 :=
    (Br.P.hu.map (PowerSeries.map (IsLocalRing.residue O))).ne_zero
  rw [map_mul, map_pow, map_pow, PowerSeries.map_X, hm]
  exact mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero)
    (pow_ne_zero _ (mul_ne_zero hu0 (pow_ne_zero _ PowerSeries.X_ne_zero)))

theorem coef_fil (hinj : Function.Injective (algebraMap O LL)) {T : LocLat G Qp LL O} {d : ℕ}
    (b : Fin d → W.DD T) (a : ZMod n)
    (h₀ h₁ m₀ m₁ η : ℕ) (hm₀ : m₀ ≤ h₀) (hm₁ : m₁ ≤ h₁) (bs : ℤ)
    (hq : IsUnit (algebraMap (LetA O n) W.EE (qA W))) (hp : IsUnit (algebraMap (LetA O n) W.EE (ps W 1)))
    (hli : ∀ c₀ : Fin d → O, dvO W T 2 b c₀ = 0 → c₀ = 0)
    (hTop0 : ∀ (c₀ : Fin d → O) (u : ℤ), (m₀ : ℤ) < u → dvO W T 2 b c₀ ∈ FilS W T a 0 u → dvO W T 2 b c₀ = 0)
    (hTop1 : ∀ (c₀ : Fin d → O) (u : ℤ), (m₁ : ℤ) < u → dvO W T 2 b c₀ ∈ FilS W T a 1 u → dvO W T 2 b c₀ = 0)
    (hGap : ∀ (c₀ : Fin d → O) (u : ℤ), (η : ℤ) + 1 ≤ u → dvO W T 2 b c₀ ∈ FilS W T a 0 u →
      dvO W T 2 b c₀ ∈ FilS W T a 0 bs)
    (f : Fin d → W.EE) (hf : InNL W T a 2 (Br.cst (X ^ h₀ * Br.P.p 1 ^ h₁)) b f) :
    ∃ Gs : Fin d → PowerSeries O,
      (∀ k, algebraMap (LetA O n) W.EE (Br.cst (X ^ m₀ * Br.P.p 1 ^ m₁)) * f k = ea Br a (Gs k)) ∧
      ∀ j < m₀ - η, dvO W T 2 b (fun k => coeff j (Gs k)) ∈ FilS W T a 0 bs := by
  classical
  have := Fact.mk PD.hp
  obtain ⟨hfr, κ, I, g, c₀, α, hmon, hsum⟩ := hf
  have hXu : IsUnit (algebraMap (LetA O n) W.EE (Br.cst X)) := Br.qA_eq ▸ hq
  have hPu : IsUnit (algebraMap (LetA O n) W.EE (Br.cst (Br.P.p 1))) := (ps_cst Br 1) ▸ hp
  have hcu : ∀ i j : ℕ, IsUnit (algebraMap (LetA O n) W.EE (Br.cst (X ^ i * Br.P.p 1 ^ j))) := by
    intro i j; rw [Br.cst_mul, Br.cst_pow, Br.cst_pow, map_mul, map_pow, map_pow]
    exact (hXu.pow i).mul (hPu.pow j)
  let good : Fin I → Prop := fun i => dvO W T 2 b (c₀ i) ≠ 0
  have hbad : ∀ i, ¬ good i → c₀ i = 0 := fun i hi => hli _ (not_not.1 hi)
  have hα0 : ∀ i, good i → -(m₀ : ℤ) ≤ α i 0 := by
    intro i hi
    by_contra hc
    exact hi (hTop0 _ (-(α i 0)) (by omega) ((hmon i).2 0 (by norm_num)))
  have hα1 : ∀ i, good i → -(m₁ : ℤ) ≤ α i 1 := by
    intro i hi
    by_contra hc
    exact hi (hTop1 _ (-(α i 1)) (by omega) ((hmon i).2 1 (by norm_num)))
  have hI : ∀ i, InFr W a (Br.cst (X ^ (α i 0).toNat * Br.P.p 1 ^ (α i 1).toNat))
      (Br.cst (X ^ (-(α i 0)).toNat * Br.P.p 1 ^ (-(α i 1)).toNat)) (g i) := by
    intro i
    have h := (hmon i).1
    unfold InId at h
    rwa [prod_two_levels_eq_const Br, prod_two_levels_eq_const Br] at h
  choose U hU using fun i => inFr_ea Br a (hI i)
  let Gi : Fin I → PowerSeries O := fun i =>
    if good i then X ^ (m₀ + α i 0).toNat * (Br.P.p 1 ^ (m₁ + α i 1).toNat * U i) else 0
  have hG : ∀ i k, algebraMap (LetA O n) W.EE (Br.cst (X ^ m₀ * Br.P.p 1 ^ m₁)) *
      (g i * algebraMap O W.EE (c₀ i k)) = ea Br a (C (c₀ i k) * Gi i) := by
    intro i k
    by_cases hi : good i
    · rw [ea_C_mul, ← mul_assoc, mul_comm (algebraMap O W.EE (c₀ i k))]
      congr 1
      refine (hcu (-(α i 0)).toNat (-(α i 1)).toNat).mul_left_cancel ?_
      rw [← mul_assoc, mul_comm (algebraMap (LetA O n) W.EE _) (algebraMap (LetA O n) W.EE _), mul_assoc,
        hU i, cst_mul_ea, cst_mul_ea]
      congr 1
      simp only [Gi, if_pos hi]
      have e0 := toNat_split m₀ (α i 0) (hα0 i hi)
      have e1 := toNat_split m₁ (α i 1) (hα1 i hi)
      calc X ^ m₀ * Br.P.p 1 ^ m₁ * (X ^ (α i 0).toNat * Br.P.p 1 ^ (α i 1).toNat * U i)
          = X ^ (m₀ + (α i 0).toNat) * Br.P.p 1 ^ (m₁ + (α i 1).toNat) * U i := by ring
        _ = X ^ ((-(α i 0)).toNat + (m₀ + α i 0).toNat) *
              Br.P.p 1 ^ ((-(α i 1)).toNat + (m₁ + α i 1).toNat) * U i := by rw [e0, e1]
        _ = _ := by ring
    · rw [hbad i hi]
      simp [Gi, if_neg hi, ea_zero]
  let V : Fin d → PowerSeries O := fun k => ∑ i, C (c₀ i k) * Gi i
  have hV : ∀ k, lE W κ * (algebraMap (LetA O n) W.EE (Br.cst (X ^ m₀ * Br.P.p 1 ^ m₁)) * f k) =
      ea Br a (V k) := by
    intro k
    have hs := hsum k
    simp only at hs
    simp only [V]
    rw [mul_left_comm, hs, Finset.mul_sum, ea_sum]
    exact Finset.sum_congr rfl fun i _ => hG i k
  have hΛ : ∀ k, ∃ U' : PowerSeries O,
      algebraMap (LetA O n) W.EE (Br.cst (X ^ (h₀ - m₀) * Br.P.p 1 ^ (h₁ - m₁))) *
        (algebraMap (LetA O n) W.EE (Br.cst (X ^ m₀ * Br.P.p 1 ^ m₁)) * f k) = ea Br a U' := by
    intro k
    obtain ⟨u, hu, hfu⟩ := hfr k
    obtain ⟨U', hU'⟩ := letE_mul_AΔ Br a hu
    refine ⟨U', ?_⟩
    have eX : X ^ (h₀ - m₀) * Br.P.p 1 ^ (h₁ - m₁) * (X ^ m₀ * Br.P.p 1 ^ m₁) = X ^ h₀ * Br.P.p 1 ^ h₁ := by
      rw [show X ^ (h₀ - m₀) * Br.P.p 1 ^ (h₁ - m₁) * (X ^ m₀ * Br.P.p 1 ^ m₁) =
        X ^ (h₀ - m₀ + m₀) * Br.P.p 1 ^ (h₁ - m₁ + m₁) by ring, Nat.sub_add_cancel hm₀, Nat.sub_add_cancel hm₁]
    rw [← mul_assoc, ← map_mul, ← Br.cst_mul, eX, hfu, mul_one, hU']
    rfl
  choose U' hU' using hΛ
  have hZV : ∀ k, (X ^ (h₀ - m₀) * Br.P.p 1 ^ (h₁ - m₁)) * V k = C (((PD.p : ℕ) : O) ^ κ) * U' k := by
    intro k
    apply ea_inj Br a
    rw [← cst_mul_ea, ← hV k, ea_C_mul, ← hU' k]
    simp only [lE, map_pow, map_natCast]
    ring
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hl0 : ((PD.p : ℕ) : O) ≠ 0 := Br.P.hl0
  obtain ⟨w₀, hw₀⟩ := l_eq_unit_mul_pow hϖ hl0
  have hCl : C (((PD.p : ℕ) : O) ^ κ) = C ((w₀ : O) ^ κ) * C ϖ ^ (eO (O := O) PD.p * κ) := by
    rw [hw₀, mul_pow, ← pow_mul, map_mul, map_pow, map_pow]
  have hZnd : ¬ C ϖ ∣ (X ^ (h₀ - m₀) * Br.P.p 1 ^ (h₁ - m₁)) :=
    ContD.not_dvd_of_isDist hϖ (isDist_XP Br _ _)
  have hdvd : ∀ k, C (((PD.p : ℕ) : O) ^ κ) ∣ V k := by
    intro k
    have h1 : C ϖ ^ (eO (O := O) PD.p * κ) ∣ (X ^ (h₀ - m₀) * Br.P.p 1 ^ (h₁ - m₁)) * V k := by
      rw [hZV k, hCl]; exact ⟨C ((w₀ : O) ^ κ) * U' k, by ring⟩
    have h2 := ContD.pow_dvd_of_dvd_mul hϖ hZnd _ _ h1
    rw [hCl]
    exact (IsUnit.mul_left_dvd ((w₀.isUnit.pow κ).map C)).2 h2
  choose Gs hGs using hdvd
  have hCne : C (((PD.p : ℕ) : O) ^ κ) ≠ (0 : PowerSeries O) := by
    intro h
    have h2 : ((PD.p : ℕ) : O) ^ κ = 0 := by simpa using congrArg (coeff 0) h
    exact pow_ne_zero κ hl0 h2
  have hZG : ∀ k, (X ^ (h₀ - m₀) * Br.P.p 1 ^ (h₁ - m₁)) * Gs k = U' k := by
    intro k
    apply mul_left_cancel₀ hCne
    rw [← hZV k, hGs k]; ring
  refine ⟨Gs, fun k => ?_, fun j hj => ?_⟩
  · apply (hcu (h₀ - m₀) (h₁ - m₁)).mul_left_cancel
    rw [hU' k, cst_mul_ea, hZG k]
  · have hco : (fun k => ((PD.p : ℕ) : O) ^ κ * coeff j (Gs k)) = fun k => ∑ i, coeff j (Gi i) * c₀ i k := by
      funext k
      have h3 := congrArg (coeff j) (hGs k)
      rw [coeff_C_mul] at h3
      rw [← h3]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [V, map_sum, coeff_C_mul]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hmem : dvO W T 2 b (fun k => ((PD.p : ℕ) : O) ^ κ * coeff j (Gs k)) ∈ FilS W T a 0 bs := by
      rw [hco, dvO_lin]
      refine Submodule.sum_mem _ fun i _ => ?_
      by_cases h0 : coeff j (Gi i) = 0
      · rw [h0, map_zero, zero_smul]; exact Submodule.zero_mem _
      · refine Submodule.smul_mem _ _ ?_
        have hi : good i := fun hz => h0 (by simp only [Gi]; rw [if_neg (fun h => h hz)]; exact map_zero _)
        have hle : (m₀ + α i 0).toNat ≤ j := by
          by_contra hlt
          apply h0
          simp only [Gi, if_pos hi]
          rw [coeff_X_pow_mul', if_neg hlt]
        have hα : (η : ℤ) + 1 ≤ -(α i 0) := by
          have h4 := hα0 i hi
          have h5 := Int.toNat_of_nonneg (show 0 ≤ (m₀ : ℤ) + α i 0 by omega)
          have h6 : (((m₀ + α i 0).toNat : ℕ) : ℤ) ≤ j := by exact_mod_cast hle
          omega
        exact hGap _ _ hα ((hmon i).2 0 (by norm_num))
    rw [dvO_smulO] at hmem
    refine (Submodule.smul_mem_iff _ ?_).1 hmem
    rw [map_pow, map_natCast]
    refine pow_ne_zero _ fun h => hl0 (hinj ?_)
    rw [map_natCast, h, map_zero]

end ArcLengthThreeFiltration
end Formalism.MainNotions.N.FrobeniusPowerSeries
end
end

open scoped TensorProduct

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

namespace ArcLengthThreeFiltration

open PowerSeries

variable {W : LocWach PD LL O v n} (Br : PhiBridge W)

theorem ea_sub (a : ZMod n) (F F' : PowerSeries O) : ea Br a (F - F') = ea Br a F - ea Br a F' := by
  have h := ea_add Br a (F - F') F'
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem ea_mul_algO (a : ZMod n) (F : PowerSeries O) (x : O) :
    ea Br a F * algebraMap O W.EE x = ea Br a (F * C x) := by
  rw [mul_comm F, ea_C_mul, mul_comm]

theorem ea_mul_cst (a : ZMod n) (F G : PowerSeries O) :
    ea Br a F * algebraMap (LetA O n) W.EE (Br.cst G) = ea Br a (F * G) := by
  rw [mul_comm, cst_mul_ea, mul_comm G]

theorem ea_def (a : ZMod n) (F : PowerSeries O) :
    ea Br a F = algebraMap (LetA O n) W.EE (letE a * 1 * Br.cst F) := by
  unfold ea; rw [mul_one]

theorem inFr_one_ea (a : ZMod n) (G F : PowerSeries O) :
    InFr W a 1 (Br.cst G) (ea Br a F) :=
  ⟨Br.cst (G * F), Br.cst_mem _, by rw [cst_mul_ea, ea_def]⟩

theorem inId_two (a : ZMod n) (α : ℕ → ℤ) (g : W.EE) :
    InId W a 2 α g ↔ InFr W a (Br.cst (X ^ (α 0).toNat * Br.P.p 1 ^ (α 1).toNat))
      (Br.cst (X ^ (-(α 0)).toNat * Br.P.p 1 ^ (-(α 1)).toNat)) g := by
  unfold InId
  rw [prod_two_levels_eq_const Br, prod_two_levels_eq_const Br]

theorem pi0_eq_cst_X_sub_C_prime : W.π₀ = Br.cst (X - C ((PD.p : ℕ) : O)) := Br.π₀_eq

theorem phi_sq_pi0_pow_power_series (h G : ℕ) :
    ∃ N : ℕ, ∃ w ∈ W.AΔ, ((W.φA ^ 2) W.π₀) ^ N = W.π₀ * (Br.cst (X ^ h * Br.P.p 1 ^ G)) ^ 2 * w := by
  have hpF : Fact PD.p.Prime := ⟨PD.hp⟩
  have hl1 : 1 ≤ PD.p - 1 := by have := PD.hp.two_le; omega
  set N := 2 * h + 2 * G + 1 with hN
  have hφ2 : (W.φA ^ 2) W.π₀ = Br.cst (Br.P.φ (Br.P.φ (X - C ((PD.p : ℕ) : O)))) := by
    rw [pow_two, AlgHom.mul_apply, pi0_eq_cst_X_sub_C_prime Br, Br.φA_cst, Br.φA_cst]
  have hφφ : Br.P.φ (Br.P.φ (X - C ((PD.p : ℕ) : O))) =
      Br.P.φ Br.P.u * Br.P.u * (X - C ((PD.p : ℕ) : O)) * X ^ (PD.p - 1) * Br.P.p 1 ^ (PD.p - 1) := by
    rw [Br.P.hφ0, map_mul, map_mul, map_pow, Br.P.hφ0]
    have : Br.P.φ X = Br.P.p 1 := rfl
    rw [this]; ring
  have e1 : (PD.p - 1) * N = 2 * h + ((PD.p - 1) * N - 2 * h) := by
    have : 2 * h ≤ (PD.p - 1) * N := by nlinarith
    omega
  have e2 : (PD.p - 1) * N = 2 * G + ((PD.p - 1) * N - 2 * G) := by
    have : 2 * G ≤ (PD.p - 1) * N := by nlinarith
    omega
  have e3 : N = 1 + (N - 1) := by omega
  refine ⟨N, Br.cst ((Br.P.φ Br.P.u * Br.P.u) ^ N * (X - C ((PD.p : ℕ) : O)) ^ (N - 1) *
      X ^ ((PD.p - 1) * N - 2 * h) * Br.P.p 1 ^ ((PD.p - 1) * N - 2 * G)), Br.cst_mem _, ?_⟩
  rw [hφ2, hφφ, pi0_eq_cst_X_sub_C_prime Br, ← Br.cst_pow, ← Br.cst_pow, ← Br.cst_mul, ← Br.cst_mul]
  congr 1
  have : (Br.P.φ Br.P.u * Br.P.u * (X - C ((PD.p : ℕ) : O)) * X ^ (PD.p - 1) * Br.P.p 1 ^ (PD.p - 1)) ^ N =
      (Br.P.φ Br.P.u * Br.P.u) ^ N * (X - C ((PD.p : ℕ) : O)) ^ N * X ^ ((PD.p - 1) * N) *
        Br.P.p 1 ^ ((PD.p - 1) * N) := by
    rw [mul_pow, mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul]
  rw [this, show (X : PowerSeries O) ^ ((PD.p - 1) * N) = X ^ (2 * h) * X ^ ((PD.p - 1) * N - 2 * h) by
      rw [← pow_add, ← e1],
    show Br.P.p 1 ^ ((PD.p - 1) * N) = Br.P.p 1 ^ (2 * G) * Br.P.p 1 ^ ((PD.p - 1) * N - 2 * G) by
      rw [← pow_add, ← e2],
    show (X - C ((PD.p : ℕ) : O)) ^ N = (X - C ((PD.p : ℕ) : O)) * (X - C ((PD.p : ℕ) : O)) ^ (N - 1) by
      rw [← pow_succ', Nat.sub_add_cancel (show 1 ≤ N by omega)]]
  ring

theorem coeff_zero_of_coord (hinj : Function.Injective (algebraMap O LL)) (a : ZMod n) (K h : ℕ)
    (Y D : PowerSeries O) (u : LetA O n) (hu : u ∈ W.AΔ)
    (hK : algebraMap (LetA O n) W.EE (letE a) * (lE W K * ea Br a D) =
      algebraMap (LetA O n) W.EE (letE a * (W.π₀ * Br.cst (X ^ h * Y)) * u)) :
    ∀ j < h, coeff j D = 0 := by
  obtain ⟨U, hU⟩ := letE_mul_AΔ Br a hu
  have e1 : algebraMap (LetA O n) W.EE (letE a) * (lE W K * ea Br a D) =
      ea Br a (C (((PD.p : ℕ) : O) ^ K) * D) := by
    rw [ea_C_mul]; unfold ea
    simp only [lE, map_pow, map_natCast]
    rw [show (algebraMap (LetA O n) W.EE) (letE a) * (((PD.p : ℕ) : W.EE) ^ K *
        (algebraMap (LetA O n) W.EE) (letE a * Br.cst D)) = ((PD.p : ℕ) : W.EE) ^ K *
        (algebraMap (LetA O n) W.EE) ((letE a * letE a) * Br.cst D) by rw [map_mul, map_mul, map_mul]; ring,
      letE_mul_self]
  have e2 : algebraMap (LetA O n) W.EE (letE a * (W.π₀ * Br.cst (X ^ h * Y)) * u) =
      ea Br a ((X - C ((PD.p : ℕ) : O)) * (X ^ h * Y) * U) := by
    unfold ea
    congr 1
    rw [show letE a * (W.π₀ * Br.cst (X ^ h * Y)) * u = (W.π₀ * Br.cst (X ^ h * Y)) * (letE a * u) by ring, hU,
      pi0_eq_cst_X_sub_C_prime Br, Br.cst_mul ((X - C ((PD.p : ℕ) : O)) * (X ^ h * Y)) U,
      Br.cst_mul (X - C ((PD.p : ℕ) : O)) (X ^ h * Y)]
    ring
  rw [e1, e2] at hK
  have hD := ea_inj Br a hK
  intro j hj
  have h1 := congrArg (coeff j) hD
  rw [coeff_C_mul, show (X - C ((PD.p : ℕ) : O)) * (X ^ h * Y) * U = X ^ h * ((X - C ((PD.p : ℕ) : O)) * Y * U) by ring,
    coeff_X_pow_mul', if_neg (by omega)] at h1
  have hpF : Fact PD.p.Prime := ⟨PD.hp⟩
  exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ Br.P.hl0)

theorem dvd_of_not_dvd {x y : O} (h : ¬ y ∣ x) : x ∣ y := by
  by_cases hx : x = 0
  · exact absurd (hx ▸ dvd_zero y) h
  by_cases hy : y = 0
  · exact hy ▸ dvd_zero x
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  obtain ⟨m', u', rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
  rcases le_or_gt m m' with hm | hm
  · refine ⟨↑u⁻¹ * u' * ϖ ^ (m' - m), ?_⟩
    rw [show ϖ ^ m' = ϖ ^ m * ϖ ^ (m' - m) by rw [← pow_add, Nat.add_sub_cancel' hm]]
    have : (u : O) * ↑u⁻¹ = 1 := u.mul_inv
    linear_combination (-(↑u' * ϖ ^ m * ϖ ^ (m' - m))) * this
  · exfalso; apply h
    refine ⟨↑u'⁻¹ * u * ϖ ^ (m - m'), ?_⟩
    rw [show ϖ ^ m = ϖ ^ m' * ϖ ^ (m - m') by rw [← pow_add, Nat.add_sub_cancel' hm.le]]
    have : (u' : O) * ↑u'⁻¹ = 1 := u'.mul_inv
    linear_combination (-(↑u * ϖ ^ m' * ϖ ^ (m - m'))) * this

end ArcLengthThreeFiltration
end Formalism.MainNotions.N.FrobeniusPowerSeries
