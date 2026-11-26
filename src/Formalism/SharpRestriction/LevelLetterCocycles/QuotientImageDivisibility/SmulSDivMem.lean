module

public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExistsXPowMul
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.GammaLevelsExpansion

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.SmulSDivMem
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section Div2

variable {LL : Type} [Field LL] {V : Type} [AddCommGroup V] [Module LL V]

theorem smulS_div_mem {m : ℤ} {e : ℤ → V} (he : LB m e) (D : Submodule LL V) (hD : ∀ k, e k ∈ D)
    (f : PowerSeries LL) (hf : f ≠ 0) :
    ∃ (m' : ℤ) (d : ℤ → V), LB m' d ∧ smulS f d = e ∧ ∀ k, d k ∈ D := by
  obtain ⟨w, u, hu, rfl⟩ := exists_X_pow_mul f hf
  set e' : ℤ → V := fun k => e (k + w) with he'
  have hLB' : LB (m - w) e' := fun k hk => he _ (by omega)
  refine ⟨m - w, smulS u⁻¹ e', LB_smulS hLB' _, ?_, smulS_mem hLB' D (fun k => hD _) _⟩
  rw [smulS_mul (LB_smulS hLB' _), ← smulS_mul hLB', PowerSeries.mul_inv_cancel _ hu,
    smulS_one hLB', smulS_X_pow hLB']
  funext k
  simp [he']

theorem smulS_linMap {V' : Type} [AddCommGroup V'] [Module LL V'] (Φ : V →ₗ[LL] V') {m : ℤ}
    {f : ℤ → V} (hf : LB m f) (g : PowerSeries LL) (k : ℤ) :
    Φ (smulS g f k) = smulS g (fun j => Φ (f j)) k := by
  have hf' : LB m (fun j => Φ (f j)) := fun j hj => by simp [hf j hj]
  obtain ⟨N, hN⟩ : ∃ N : ℕ, k - m < N :=
    ⟨Int.toNat (k - m) + 1, by have := Int.self_le_toNat (k - m); push_cast; omega⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [smulS_eq_sum hf g k N hN, smulS_eq_sum hf' g k N hN, map_sum]
  simp [map_smul]

end Div2

section Rules

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem levN_smulS (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) (a : LetA O n) (x : ↥(W.N T)) :
    W.levN T i ζ (a • x) = smulS (W.lev i ζ a) (W.levN T i ζ x) := by
  funext k
  rw [W.levN_smul]
  rfl

theorem isExp_unique (T : LocLat G Qp LL O) (i : ZMod n) (ζ : LL) {x : W.DD T}
    {d d' : ℤ → T.V ⊗[Qp] BdR} (hd : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d)
    (hd' : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d') : d = d' := by
  obtain ⟨⟨m, hm⟩, a, ha, hla, he⟩ := hd
  obtain ⟨⟨m', hm'⟩, a', ha', hla', he'⟩ := hd'
  have hdl : LB (min m m') d := fun k hk => hm k (by omega)
  have hdl' : LB (min m m') d' := fun k hk => hm' k (by omega)
  have hlev : W.levN T i ζ ⟨a • x, ha⟩ = smulS (W.lev i ζ a) d := funext he
  have hlev' : W.levN T i ζ ⟨a' • x, ha'⟩ = smulS (W.lev i ζ a') d' := funext he'
  have e : a' • (⟨a • x, ha⟩ : ↥(W.N T)) = a • (⟨a' • x, ha'⟩ : ↥(W.N T)) :=
    Subtype.ext (by simp only [SetLike.val_smul]; rw [smul_smul, smul_smul, mul_comm])
  have h := congrArg (W.levN T i ζ) e
  rw [levN_smulS, levN_smulS, hlev, hlev', ← smulS_mul hdl, ← smulS_mul hdl', mul_comm] at h
  exact smulS_inj hdl hdl' _ (mul_ne_zero hla hla') h

theorem expRules_of (h4 : Formalism.MainNotions.WachCoordinates.LevelMapHodgeFiltration W) (hN : GamN W) (hA' : GamA W) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W := by
  intro hA T hT i ζ hζ
  have hLv : ∀ (x : ↥(W.N T)) (k : ℤ), W.levN T i ζ x k ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i := fun x k => by
    have := (h4 T hT i 0 ζ (by rwa [zero_add, pow_one])).1 x k
    rw [Formalism.MainNotions.UnusedSlot80.LevR.filLev_zero] at this
    exact (Submodule.mem_inf.1 this).1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x a ha hla
    obtain ⟨m, hm⟩ := W.levN_supp T i ζ ⟨a • x, ha⟩
    obtain ⟨m', d, hd, hde⟩ := smulS_div (m := m) hm _ hla
    have hE : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d :=
      ⟨⟨m', hd⟩, a, ha, hla, fun k => (congrFun hde k).symm⟩
    exact ⟨d, hE, fun d' hd' => isExp_unique W T i ζ hd' hE⟩
  ·
    intro x d _ hx k
    obtain ⟨⟨m, hm⟩, a, ha, hla, he⟩ := hx
    obtain ⟨m₀, hm₀⟩ := W.levN_supp T i ζ ⟨a • x, ha⟩
    obtain ⟨m', d₀, hd₀, hde₀, hmem⟩ := smulS_div_mem (m := m₀) hm₀ (Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i)
      (fun k => hLv _ k) _ hla
    have hE₀ : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ x d₀ :=
      ⟨⟨m', hd₀⟩, a, ha, hla, fun k => (congrFun hde₀ k).symm⟩
    rw [isExp_unique W T i ζ ⟨⟨m, hm⟩, a, ha, hla, he⟩ hE₀]
    exact hmem k
  ·
    rintro x y d e ⟨⟨m, hm⟩, a, ha, hla, hd⟩ ⟨⟨m', hm'⟩, b, hb, hlb, he⟩
    have hdl : LB (min m m') d := fun k hk => hm k (by omega)
    have hel : LB (min m m') e := fun k hk => hm' k (by omega)
    have hmem : (a * b) • (x + y) ∈ W.N T := by
      rw [smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
      exact (W.N T).add_mem ((W.N T).smul_mem b ha) ((W.N T).smul_mem a hb)
    refine ⟨⟨min m m', LB_add hdl hel⟩, a * b, hmem, by rw [map_mul]; exact mul_ne_zero hla hlb,
      fun k => ?_⟩
    have e1 : (⟨(a * b) • (x + y), hmem⟩ : ↥(W.N T)) =
        b • (⟨a • x, ha⟩ : ↥(W.N T)) + a • (⟨b • y, hb⟩ : ↥(W.N T)) :=
      Subtype.ext (by
        simp only [Submodule.coe_add, SetLike.val_smul]
        rw [smul_add, smul_smul, smul_smul, mul_comm b a])
    rw [e1, map_add (f := _), Pi.add_apply, levN_smulS, levN_smulS, funext hd, funext he]
    show smulS (W.lev i ζ b) (smulS (W.lev i ζ a) d) k + smulS (W.lev i ζ a) (smulS (W.lev i ζ b) e) k =
      smulS (W.lev i ζ (a * b)) (d + e) k
    rw [map_mul, smulS_add hdl hel, ← smulS_mul hdl, ← smulS_mul hel, mul_comm (W.lev i ζ b)]
    rfl
  ·
    rintro c x d ⟨⟨m, hm⟩, a, ha, hla, hd⟩
    have hmem : a • (c • x) ∈ W.N T := by
      rw [smul_comm]; exact (W.N T).smul_of_tower_mem c ha
    refine ⟨⟨m, fun k hk => by simp [hm k hk]⟩, a, hmem, hla, fun k => ?_⟩
    have e1 : (⟨a • (c • x), hmem⟩ : ↥(W.N T)) =
        (algebraMap O (LetA O n) c) • (⟨a • x, ha⟩ : ↥(W.N T)) :=
      Subtype.ext (by
        simp only [SetLike.val_smul]
        rw [algebraMap_smul, smul_comm])
    rw [e1, levN_smulS, funext hd, AlgHom.commutes, PowerSeries.algebraMap_apply]
    show smulS (PowerSeries.C (algebraMap O LL c)) (smulS (W.lev i ζ a) d) k =
      smulS (W.lev i ζ a) (fun k => algebraMap O LL c • d k) k
    rw [smulS_C (LB_smulS hm _)]
    have e2 : (fun k => algebraMap O LL c • d k) = algebraMap O LL c • d := rfl
    rw [e2, smulS_smul hm]
  ·
    rintro a' x d ⟨⟨m, hm⟩, a, ha, hla, hd⟩
    have hmem : a • (a' • x) ∈ W.N T := by
      rw [smul_comm]; exact (W.N T).smul_mem a' ha
    refine ⟨⟨m, LB_smulS hm _⟩, a, hmem, hla, fun k => ?_⟩
    have e1 : (⟨a • (a' • x), hmem⟩ : ↥(W.N T)) = a' • (⟨a • x, ha⟩ : ↥(W.N T)) :=
      Subtype.ext (by simp only [SetLike.val_smul]; rw [smul_comm])
    rw [e1, levN_smulS, funext hd]
    show smulS (W.lev i ζ a') (smulS (W.lev i ζ a) d) k = smulS (W.lev i ζ a) (smulS (W.lev i ζ a') d) k
    rw [smulS_comm hm]
  ·
    rintro x d ⟨⟨m, hm⟩, a, ha, hla, hd⟩
    have hχ : algebraMap O LL (W.χΓ W.gam : O) ≠ 0 :=
      ((Units.isUnit (W.χΓ W.gam)).map (algebraMap O LL)).ne_zero
    have hγN' : W.γ T (a • x) ∈ W.N T := W.N_Γ T W.gam _ ha
    have hmem : W.γA W.gam a • W.γ T x ∈ W.N T := by
      have h := hγN'
      change W.γD T W.gam (a • x) ∈ W.N T at h
      rw [RL.γD_smulA] at h
      exact h
    refine ⟨⟨m, LB_resc hm _⟩, W.γA W.gam a, hmem, ?_, fun k => ?_⟩
    · rw [hA' i ζ hζ a]
      intro h0
      exact hla (PowerSeries.rescale_injective hχ (h0.trans (map_zero _).symm))
    · have e1 : (⟨W.γA W.gam a • W.γ T x, hmem⟩ : ↥(W.N T)) =
          ⟨W.γ T ((⟨a • x, ha⟩ : ↥(W.N T)) : W.DD T), hγN'⟩ :=
        Subtype.ext (RL.γD_smulA W T W.gam a x).symm
      rw [e1, hN T hT i ζ hζ ⟨a • x, ha⟩ hγN' k, funext hd, hA' i ζ hζ a]
      show algebraMap O LL (W.χΓ W.gam : O) ^ k • smulS (W.lev i ζ a) d k =
        smulS (PowerSeries.rescale (algebraMap O LL (W.χΓ W.gam : O)) (W.lev i ζ a))
          (resc (algebraMap O LL (W.χΓ W.gam : O)) d) k
      rw [smulS_rescale hm _ hχ]
      rfl
  ·
    rintro T' F hT' x d ⟨⟨m, hm⟩, a, ha, hla, hd⟩
    have hmem : a • W.map F x ∈ W.N T' := by
      rw [← RL.map_smulA]; exact W.map_N F hT hT' _ ha
    refine ⟨⟨m, fun k hk => by simp [hm k hk]⟩, a, hmem, hla, fun k => ?_⟩
    have e1 : (⟨a • W.map F x, hmem⟩ : ↥(W.N T')) =
        ⟨W.map F ((⟨a • x, ha⟩ : ↥(W.N T)) : W.DD T), by rw [← RL.map_smulA] at hmem; exact hmem⟩ :=
      Subtype.ext (RL.map_smulA W F a x).symm
    rw [e1, W.levN_map F hT hT' i ζ, hd]
    exact smulS_linMap _ hm _ k

end Rules

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.QpEqUnit
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries Formalism.MainNotions.N.Pv.LocalLengthBound.Ser TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Trans

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem qp_eq_unit (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) :
    ∃ U : (LetA O n)ˣ, Formalism.MainNotions.LiftingTheory.qp W = (U : LetA O n) * W.Q := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  have hE : Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ : ZMod n => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))
      W.π₀ = Formalism.MainNotions.LiftingTheory.qp W := by
    funext i
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, Formalism.MainNotions.LiftingTheory.qp, LocWach.π₀]
  rw [hE] at hw
  refine ⟨w⁻¹, ?_⟩
  rw [Q_eq_q W hs, hw, ← mul_assoc, Units.inv_mul, one_mul]

theorem trans_d [IsDomain O] (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (c : ZMod n)
    (δ : W.Gam) (hδ : δ ∈ W.DelF) (ζ ζ' : LL) (χ : LL) (hχ0 : χ ≠ 0)
    (hΔN : ∀ (x : ↥(W.N T)) (hx : W.γD T δ x ∈ W.N T) (k : ℤ),
      W.levN T c ζ ⟨W.γD T δ x, hx⟩ k = χ ^ k • W.levN T c ζ' x k)
    (hΔA : ∀ f : LetA O n, W.lev c ζ (W.γA δ f) = PowerSeries.rescale χ (W.lev c ζ' f))
    {w : W.DD T} (hwΔ : W.γD T δ w = w) {K : ℕ} (hK : W.Q ^ K • w ∈ W.N T)
    (u u' : PowerSeries LL) (hu : W.lev c ζ W.q = X * u) (hu' : W.lev c ζ' W.q = X * u')
    (hu0 : constantCoeff u ≠ 0)
    {dz dz' : ℤ → T.V ⊗[Qp] BdR} (hdz : ∃ m, LB m dz) (hdz' : ∃ m, LB m dz')
    (ez : W.levN T c ζ ⟨W.Q ^ K • w, hK⟩ = smulS ((X * u) ^ K) dz)
    (ez' : W.levN T c ζ' ⟨W.Q ^ K • w, hK⟩ = smulS ((X * u') ^ K) dz') :
    dz = resc χ dz' := by
  obtain ⟨m, hm⟩ := hdz
  obtain ⟨m', hm'⟩ := hdz'
  have hQ : W.Q = W.q := Q_eq_q W hs
  obtain ⟨U, hU⟩ := qp_eq_unit W hs hR
  have hxeq : Formalism.MainNotions.LiftingTheory.qp W ^ K • w = (U : LetA O n) ^ K • (W.Q ^ K • w) := by
    rw [hU, mul_pow, mul_smul]
  have hxN : Formalism.MainNotions.LiftingTheory.qp W ^ K • w ∈ W.N T := by
    rw [hxeq]; exact (W.N T).smul_mem _ hK
  have hxΔ : W.γD T δ (Formalism.MainNotions.LiftingTheory.qp W ^ K • w) = Formalism.MainNotions.LiftingTheory.qp W ^ K • w := by
    rw [Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA', map_pow, (qp_mem_AΔ W hR) δ hδ, hwΔ]
  set x : ↥(W.N T) := ⟨Formalism.MainNotions.LiftingTheory.qp W ^ K • w, hxN⟩ with hxdef
  have hγx : W.γD T δ (x : W.DD T) ∈ W.N T := by rw [hxdef]; simp only; rw [hxΔ]; exact hxN
  have h1 : W.levN T c ζ x = resc χ (W.levN T c ζ' x) := by
    funext k
    simp only [resc]
    have hxx : (⟨W.γD T δ (x : W.DD T), hγx⟩ : ↥(W.N T)) = x := Subtype.ext hxΔ
    rw [← hΔN x hγx k, hxx]
  have hsplit : x = (U : LetA O n) ^ K • (⟨W.Q ^ K • w, hK⟩ : ↥(W.N T)) := Subtype.ext hxeq
  have h2 : ∀ (z : LL) (uz : PowerSeries LL) (dd : ℤ → T.V ⊗[Qp] BdR) (mm : ℤ), LB mm dd →
      W.levN T c z ⟨W.Q ^ K • w, hK⟩ = smulS ((X * uz) ^ K) dd →
      W.levN T c z x = smulS ((W.lev c z (U : LetA O n) * (X * uz)) ^ K) dd := by
    intro z uz dd mm hdd e
    rw [hsplit]
    have this : W.levN T c z ((U : LetA O n) ^ K • (⟨W.Q ^ K • w, hK⟩ : ↥(W.N T))) =
        smulS (W.lev c z ((U : LetA O n) ^ K)) (W.levN T c z ⟨W.Q ^ K • w, hK⟩) :=
      funext fun k => W.levN_smul T c z ((U : LetA O n) ^ K) ⟨W.Q ^ K • w, hK⟩ k
    rw [this, e, ← smulS_mul hdd, map_pow, ← mul_pow]
  have hz := h2 ζ u dz m hm ez
  have hz' := h2 ζ' u' dz' m' hm' ez'
  have hresc : PowerSeries.rescale χ (W.lev c ζ' (U : LetA O n) * (X * u')) =
      W.lev c ζ (U : LetA O n) * (X * u) := by
    have e1 : W.lev c ζ' (U : LetA O n) * (X * u') = W.lev c ζ' (Formalism.MainNotions.LiftingTheory.qp W) := by
      rw [hU, map_mul, hQ, hu']
    have e2 : W.lev c ζ (U : LetA O n) * (X * u) = W.lev c ζ (Formalism.MainNotions.LiftingTheory.qp W) := by
      rw [hU, map_mul, hQ, hu]
    rw [e1, e2, ← hΔA, (qp_mem_AΔ W hR) δ hδ]
  rw [h1, hz', ← smulS_rescale hm' χ hχ0, map_pow, hresc] at hz
  have hUc : constantCoeff (W.lev c ζ (U : LetA O n) * u) ≠ 0 := by
    rw [map_mul]
    refine mul_ne_zero ?_ hu0
    have hu1 : IsUnit (W.lev c ζ (U : LetA O n)) := (Units.isUnit U).map _
    exact (PowerSeries.isUnit_iff_constantCoeff.1 hu1).ne_zero
  have e3 : W.lev c ζ (U : LetA O n) * (X * u) = X * (W.lev c ζ (U : LetA O n) * u) := by ring
  rw [e3] at hz
  exact div_unique (m := min m m') (LB_mono hm (min_le_left _ _))
    (LB_mono (LB_resc hm' χ) (min_le_right _ _)) _ hUc K hz.symm

end Trans

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.FrobeniusSqComparisonLetter
noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section At

variable (W : LocWach PD LL O v n)

theorem mkQ_mem_map_iff {M : Type} [AddCommGroup M] [Module O M] {K X : Submodule O M}
    (hK : K ≤ X) (z : M) : K.mkQ z ∈ X.map K.mkQ ↔ z ∈ X := by
  rw [← Submodule.mem_comap, Submodule.comap_map_mkQ, sup_eq_right.2 hK]

theorem cmpD_sub (T : LocLat G Qp LL O) {x y : W.DD T} (hx : x ∈ W.N T) (hy : y ∈ W.N T) :
    Formalism.MainNotions.ArcLiftingSetup.cmpD W T (x - y) = Formalism.MainNotions.ArcLiftingSetup.cmpD W T x - Formalism.MainNotions.ArcLiftingSetup.cmpD W T y := by
  have h := cmpD_add W T ((W.N T).sub_mem hx hy) hy
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem frobenius_sq_comparison_letter (T : LocLat G Qp LL O) (c : ZMod n) {y : W.DD T}
    (hy : y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1 - 1)) :
    φVB PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T y)) ∈
      DcrisL PD T.ρ (W.emb (c - 1)) := by
  have h0 : Formalism.MainNotions.ArcLiftingSetup.cmpD W T y ∈ DcrisL PD T.ρ (W.emb (c - 1 - 1 - 1)) := by
    rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T (NDl_N W T hy)]
    exact Formalism.MainNotions.UnusedSlot80.ArcF.cmp_mem_letter W T _ (NDl_N W T hy) (NDl_DL W T hy).1
  have h2 := Formalism.MainNotions.UnusedSlot80.ArcF.φVB_letter W T _ (Formalism.MainNotions.UnusedSlot80.ArcF.φVB_letter W T _ h0)
  have e : c - 1 - 1 - 1 + 1 + 1 = c - 1 := by ring
  rw [e] at h2
  exact h2

theorem frobenius_sq_mem_lattice_image (T : LocLat G Qp LL O) (c : ZMod n) {y : W.DD T}
    (hy : y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T (c - 1 - 1 - 1)) :
    φVB PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T y)) ∈
      (fun z => φVB PD (LL := LL) (V := T.V) (φVB PD (LL := LL) (V := T.V) z)) ''
        Formalism.MainNotions.CrystallineLiftingInputs.Dlat W T (c - 1 - 1 - 1) :=
  ⟨Formalism.MainNotions.ArcLiftingSetup.cmpD W T y, ⟨y, NDl_N W T hy, NDl_DL W T hy,
    Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T (NDl_N W T hy)⟩, rfl⟩

variable [IsDomain O] [IsPrincipalIdealRing O] [IsFractionRing O LL]

theorem frobenius_sq_bound_at (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (h3₁ : Formalism.MainNotions.DeltaInvariantLattices.p3 W T₁) (h3₂ : Formalism.MainNotions.DeltaInvariantLattices.p3 W T₂)
    (hmod₁ : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T₁ W.π₀) (hmod₂ : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T₂ W.π₀)
    {c : ZMod n} {kB hh bb η' b' m : ℕ} {cc : ℝ}
    (hM₁ : ∀ z ∈ W.Nl T₁ (c - 1), W.Q ^ kB • W.φD T₁ z ∈ W.N T₁)
    (hM₂ : ∀ z ∈ W.Nl T₂ (c - 1), W.Q ^ kB • W.φD T₂ z ∈ W.N T₂)
    (hU : ∀ y ∈ W.Nl T₂ (c - 1), W.Q ^ bb • y ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T₂ (W.Nl T₂ (c - 1 - 1)))
    (hMη : ∀ z ∈ W.Nl T₂ (c - 1 - 1), W.Q ^ η' • W.φD T₂ z ∈ W.N T₂)
    (hM₂' : ∀ z ∈ W.Nl T₂ (c - 1 - 1 - 1), W.Q ^ hh • W.φD T₂ z ∈ W.N T₂)
    (hDc : ∃ s : Finset (W.DD T₂), s.card ≤ m ∧ (↑s : Set (W.DD T₂)) ⊆ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c ∧
      ∃ L kO : ℕ, Module.length O (↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c) ⧸
          (Xd W T₂ c kB ⊔ Submodule.span O (↑s : Set (W.DD T₂))).comap
            (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c).subtype) ≤ (L : ℕ∞) ∧
        lenOl PD (O := O) = kO ∧ (L : ℝ) ≤ cc * kO)
    (hDc2 : ∃ s : Finset (W.DD T₂), s.card ≤ m ∧
      (↑s : Set (W.DD T₂)) ⊆ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ (c - 1 - 1) ∧
      ∃ L kO : ℕ, Module.length O (↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ (c - 1 - 1)) ⧸
          (Xd W T₂ (c - 1 - 1) hh ⊔ Submodule.span O (↑s : Set (W.DD T₂))).comap
            (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ (c - 1 - 1)).subtype) ≤ (L : ℕ∞) ∧
        lenOl PD (O := O) = kO ∧ (L : ℝ) ≤ cc * kO)
    [FiniteDimensional LL ↥(DcrisL PD T₂.ρ (W.emb (c - 1)))]
    (hRk : Module.finrank LL ↥((DcrisL PD T₂.ρ (W.emb (c - 1))).map
      (FilCris PD T₂.ρ (b' : ℤ)).mkQ) ≤ m)
    {k : ℤ}
    (hGc : ∀ x ∈ (fun z => φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) z)) ''
        Formalism.MainNotions.CrystallineLiftingInputs.Dlat W T₂ (c - 1 - 1 - 1),
      x ∈ FilCris PD T₂.ρ (b' : ℤ) → (PD.p : LL) ^ k • x ∈ Formalism.MainNotions.CrystallineLiftingInputs.DlatImg W F (c - 1))
    {e pad : ℕ} (hexp : (e : ℤ) + hh = pad + k + bb)
    (FF : Type) [AddCommGroup FF] [Module O FF] [Module.Finite O FF]
    (Fs : Submodule O FF) (w : ↥Fs →ₗ[O] W.DD T₂)
    (hw : ∀ f : ↥Fs, w f ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c) :
    ∃ (F' : Submodule O FF) (hF' : F' ≤ Fs),
      Formalism.MainNotions.RamifiedCoefficientChains.S9.PChain (lenOl PD (O := O)) m cc Fs F' 3 2 ∧
      ∀ f : ↥F', ∃ x : W.DD T₁, Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c x ∧
        Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ 1 (((PD.p : O) ^ e) • w (Submodule.inclusion hF' f) - W.map F x) := by
  have hp : (PD.p : LL) ≠ 0 := Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W
  have φinj := Formalism.MainNotions.UnusedSlot80.ArcF.φVB_inj (PD := PD) T₂
  have hwN : ∀ f, w f ∈ W.N T₂ := fun f => NDl_N W T₂ (hw f)

  set K5 := Kc W T₂ c with hK5def
  have hK5 := Kc_le W T₂ c kB h3₂ hmod₂ hR
  set ψ5 : ↥Fs →ₗ[O] ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c) ⧸ K5 :=
    K5.mkQ ∘ₗ LinearMap.codRestrict (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c) w hw with hψ5
  obtain ⟨s5, hs5, hs5N, L5, kO5, hL5, hkO5, hLc5⟩ := hDc
  have ch5 := pchain_DN W T₂ c kB K5 hK5 s5 hs5 hs5N L5 kO5 hL5 hkO5 hLc5 Fs ψ5
  set F5 := kerSub Fs ψ5 (((Xd W T₂ c kB).comap (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c).subtype).map K5.mkQ)
  have hF5 : F5 ≤ Fs := kerSub_le _ _ _
  have mem5 : ∀ f : ↥F5, w ⟨f, hF5 f.2⟩ ∈ Xd W T₂ c kB := by
    intro f
    have h := (mem_kerSub_coe Fs ψ5 _ ⟨f, hF5 f.2⟩).1 f.2
    exact (mkQ_mem_map_iff hK5 _).1 h
  have ex1 : ∀ f : ↥F5, ∃ y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ (c - 1),
      Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (w ⟨f, hF5 f.2⟩) =
        (PD.p : LL) ^ kB • φVB PD (LL := LL) (V := T₂.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ y) :=
    fun f => cmp_of_mem_X W T₂ hs hR h3₂ hM₂ (mem5 f)
  choose y1 hy1 e1 using ex1
  have ex2 : ∀ f : ↥F5, ∃ y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ (c - 1 - 1),
      (PD.p : LL) ^ bb • Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y1 f) =
        φVB PD (LL := LL) (V := T₂.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ y) :=
    fun f => cmp_up W T₂ hs h3₂ hmod₂ hU hMη (hy1 f)
  choose y2 hy2 e2 using ex2
  have hy1N : ∀ f, y1 f ∈ W.N T₂ := fun f => NDl_N W T₂ (hy1 f)
  have hy2N : ∀ f, y2 f ∈ W.N T₂ := fun f => NDl_N W T₂ (hy2 f)
  have add1 : ∀ f g : ↥F5, Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y1 (f + g)) =
      Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y1 f) + Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y1 g) := by
    intro f g
    apply φinj
    apply smul_right_injective _ (pow_ne_zero kB hp)
    have hwa : w ⟨((f + g : ↥F5) : FF), hF5 (f + g).2⟩ = w ⟨f, hF5 f.2⟩ + w ⟨g, hF5 g.2⟩ := by
      rw [← map_add (f := _)]; rfl
    simp only
    rw [← e1 (f + g), hwa, cmpD_add W T₂ (hwN _) (hwN _), e1 f, e1 g, map_add (f := _), smul_add]
  have smul1 : ∀ (o : O) (f : ↥F5), Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y1 (o • f)) =
      algebraMap O LL o • Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y1 f) := by
    intro o f
    apply φinj
    apply smul_right_injective _ (pow_ne_zero kB hp)
    have hwa : w ⟨((o • f : ↥F5) : FF), hF5 (o • f).2⟩ = o • w ⟨f, hF5 f.2⟩ := by
      rw [← map_smul]; rfl
    simp only
    rw [← e1 (o • f), hwa, cmpD_osmul W T₂ o (hwN _), e1 f, map_smul, smul_comm]
  have add2 : ∀ f g : ↥F5, Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y2 (f + g)) =
      Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y2 f) + Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y2 g) := by
    intro f g
    apply φinj
    rw [map_add (f := _), ← e2, ← e2, ← e2, add1, smul_add]
  have smul2 : ∀ (o : O) (f : ↥F5), Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y2 (o • f)) =
      algebraMap O LL o • Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y2 f) := by
    intro o f
    apply φinj
    rw [map_smul, ← e2, ← e2, smul1, smul_comm]

  set K6 := Kc W T₂ (c - 1 - 1) with hK6def
  have hK6 := Kc_le W T₂ (c - 1 - 1) hh h3₂ hmod₂ hR
  let ψ6 : ↥F5 →ₗ[O] ↥(Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ (c - 1 - 1)) ⧸ K6 :=
    { toFun := fun f => K6.mkQ ⟨y2 f, hy2 f⟩
      map_add' := fun f g => by
        rw [← map_add (f := _)]
        apply (Submodule.Quotient.eq _).2
        show Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y2 (f + g) - (y2 f + y2 g)) = 0
        rw [cmpD_sub W T₂ (hy2N _) ((W.N T₂).add_mem (hy2N _) (hy2N _)),
          cmpD_add W T₂ (hy2N _) (hy2N _), add2, sub_self]
      map_smul' := fun o f => by
        rw [RingHom.id_apply, ← map_smul]
        apply (Submodule.Quotient.eq _).2
        show Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y2 (o • f) - o • y2 f) = 0
        have hoN : o • y2 f ∈ W.N T₂ := by
          rw [← algebraMap_smul (LetA O n)]; exact (W.N T₂).smul_mem _ (hy2N f)
        rw [cmpD_sub W T₂ (hy2N _) hoN, cmpD_osmul W T₂ o (hy2N f), smul2, sub_self] }
  obtain ⟨s6, hs6, hs6N, L6, kO6, hL6, hkO6, hLc6⟩ := hDc2
  have ch6 := pchain_DN W T₂ (c - 1 - 1) hh K6 hK6 s6 hs6 hs6N L6 kO6 hL6 hkO6 hLc6 F5 ψ6
  set F6 := kerSub F5 ψ6
    (((Xd W T₂ (c - 1 - 1) hh).comap (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ (c - 1 - 1)).subtype).map K6.mkQ)
  have hF6 : F6 ≤ F5 := kerSub_le _ _ _
  have mem6 : ∀ f : ↥F6, y2 ⟨f, hF6 f.2⟩ ∈ Xd W T₂ (c - 1 - 1) hh := by
    intro f
    have h := (mem_kerSub_coe F5 ψ6 _ ⟨f, hF6 f.2⟩).1 f.2
    exact (mkQ_mem_map_iff hK6 _).1 h
  have ex3 : ∀ f : ↥F6, ∃ y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ (c - 1 - 1 - 1),
      Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y2 ⟨f, hF6 f.2⟩) =
        (PD.p : LL) ^ hh • φVB PD (LL := LL) (V := T₂.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ y) :=
    fun f => cmp_of_mem_X W T₂ hs hR h3₂ hM₂' (mem6 f)
  choose y3 hy3 e3 using ex3
  set ell : ↥F6 → T₂.V ⊗[Qp] B := fun f =>
    φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y3 f)))
    with hell
  have add3 : ∀ f g : ↥F6, ell (f + g) = ell f + ell g := by
    intro f g
    have h : Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y3 (f + g)) =
        Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y3 f) + Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y3 g) := by
      apply φinj
      apply smul_right_injective _ (pow_ne_zero hh hp)
      have h5 : (⟨((f + g : ↥F6) : FF), hF6 (f + g).2⟩ : ↥F5) = ⟨f, hF6 f.2⟩ + ⟨g, hF6 g.2⟩ := rfl
      simp only
      rw [← e3 (f + g), h5, add2, e3 f, e3 g, map_add (f := _), smul_add]
    simp only [hell, h, map_add (f := _)]
  have smul3 : ∀ (o : O) (f : ↥F6), ell (o • f) = algebraMap O LL o • ell f := by
    intro o f
    have h : Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y3 (o • f)) = algebraMap O LL o • Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y3 f) := by
      apply φinj
      apply smul_right_injective _ (pow_ne_zero hh hp)
      have h5 : (⟨((o • f : ↥F6) : FF), hF6 (o • f).2⟩ : ↥F5) = o • ⟨f, hF6 f.2⟩ := rfl
      simp only
      rw [← e3 (o • f), h5, smul2, e3 f, map_smul, smul_comm]
    simp only [hell, h, map_smul]

  let ψ7 : ↥F6 →+ (T₂.V ⊗[Qp] B) ⧸ FilCris PD T₂.ρ (b' : ℤ) :=
    { toFun := fun f => (FilCris PD T₂.ρ (b' : ℤ)).mkQ (ell f)
      map_zero' := by
        have h := add3 0 0
        rw [add_zero] at h
        have h0 : ell 0 = 0 := by
          have := congrArg (fun z => z - ell 0) h
          simpa using this.symm
        rw [h0, map_zero]
      map_add' := fun f g => by rw [add3, map_add (f := _)] }
  have hψ7 : ∀ (o : O) (x : ↥F6), ψ7 (o • x) = algebraMap O LL o • ψ7 x := by
    intro o x
    show (FilCris PD T₂.ρ (b' : ℤ)).mkQ (ell (o • x)) =
      algebraMap O LL o • (FilCris PD T₂.ρ (b' : ℤ)).mkQ (ell x)
    rw [smul3, map_smul]
  have hletter : ∀ f : ↥F6, ell f ∈ DcrisL PD T₂.ρ (W.emb (c - 1)) := fun f =>
    frobenius_sq_comparison_letter W T₂ c (hy3 f)
  have hrank : Module.finrank LL ↥(Submodule.span LL (Set.range ψ7)) ≤ m := by
    have hsub : Submodule.span LL (Set.range ψ7) ≤
        (DcrisL PD T₂.ρ (W.emb (c - 1))).map (FilCris PD T₂.ρ (b' : ℤ)).mkQ := by
      rw [Submodule.span_le]
      rintro _ ⟨f, rfl⟩
      exact ⟨ell f, hletter f, rfl⟩
    exact (Submodule.finrank_mono hsub).trans hRk
  have ch7 := pchain_of_gen (pstep_rank (lenO := lenOl PD (O := O)) (m := m) (c := cc) F6 ψ7 hψ7 hrank)
  set F7 := zeroSub F6 ψ7 hψ7
  have hF7 : F7 ≤ F6 := zeroSub_le _ _ _
  have chain : Formalism.MainNotions.RamifiedCoefficientChains.S9.PChain (lenOl PD (O := O)) m cc Fs F7 3 2 :=
    ((ch5.trans ch6).trans ch7).mono (by norm_num) (by norm_num)
  refine ⟨F7, chain.le, chain, fun f => ?_⟩
  set f6 : ↥F6 := ⟨f, hF7 f.2⟩
  set f5 : ↥F5 := ⟨f, hF6 (hF7 f.2)⟩
  have hz : ψ7 f6 = 0 := (mem_zeroSub_coe F6 ψ7 hψ7 f6).1 f.2
  have hFil : ell f6 ∈ FilCris PD T₂.ρ (b' : ℤ) := (Submodule.Quotient.mk_eq_zero _).1 hz
  have hG := hGc (ell f6) (frobenius_sq_mem_lattice_image W T₂ c (hy3 f6)) hFil
  have hy : w ⟨f, hF5 f5.2⟩ ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c := hw _
  obtain ⟨x, hx1, hx2⟩ := exists_inI_inPN_pow_smul_sub_map W hs hR F h3₁ h3₂ hmod₁ hmod₂ hM₁ hM₂ hy
    (d1 := Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y1 f5)) (d2 := Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y2 f5))
    (d3 := Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (y3 f6)) (s₁ := 0) (s₂ := 0)
    (by rw [pow_zero, one_smul]; exact e1 f5) (e2 f5) (by rw [pow_zero, one_smul]; exact e3 f6) hG hexp
  refine ⟨x, hx1, ?_⟩
  have hxe : ((PD.p : O) ^ (e + 0 + 0)) = (PD.p : O) ^ e := by simp
  rw [hxe] at hx2
  exact hx2

end At

end Formalism.MainNotions.N.Pv.LocalLengthBound
end
end
