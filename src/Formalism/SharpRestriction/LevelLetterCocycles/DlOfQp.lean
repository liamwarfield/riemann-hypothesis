module

public import Formalism.SharpRestriction.LevelLetterCocycles.JumpsInLetterOfEvenIndex
public import Formalism.SharpRestriction.LevelLetterCocycles.EvaluationAtUniformizerPower
public import Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesOfLevelZeroParts
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.IsExpSmulA

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.DlOfQp
noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.GM

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.RamifiedCoefficientChains.S9.LD Formalism.MainNotions.RamifiedCoefficientChains.S9.DetD
  Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB Formalism.MainNotions.RamifiedCoefficientChains.S9.DetS TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

theorem filLev_anti (T : LocLat G Qp LL O) (i : ZMod n) :
    Antitone fun a : ℤ => Formalism.MainNotions.WachCoordinates.FilLev W T i 0 a := by
  intro a b hab
  exact Submodule.map_mono (Submodule.map_mono
    (inf_le_inf_right _ fun x hx => Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ hab hx))

theorem ιDi_le_fil (hbij : Function.Bijective (algebraMap K₀ K)) (T : LocLat G Qp LL O) (i : ZMod n)
    (H : ℕ) (hJ : ∀ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ i → ∀ a, IsJumpV PD T.ρ τ a → -(H : ℤ) ≤ a)
    (a : ℤ) (ha : a ≤ -(H : ℤ)) : Formalism.MainNotions.DeltaInvariantLattices.ιDi W T i ≤ Formalism.MainNotions.WachCoordinates.FilLev W T i 0 a := by
  intro z hz
  obtain ⟨x, hx, rfl⟩ := hz
  obtain ⟨τ, hτ, hover⟩ := Formalism.MainNotions.UnusedSlot80.LevC.tau_over W hbij i
  have h1 := Formalism.MainNotions.UnusedSlot80.LevC.fil_low W T i τ hover hbij.2 H (hJ τ hτ) hx
  have h2 := Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ ha h1
  refine ⟨x, ⟨x, ⟨h2, by simpa using hx⟩, by simp⟩, rfl⟩

theorem qp_smul_gE (hq : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) (T : LocLat G Qp LL O)
    (h c : ℕ) {r : ℕ} (e' : Fin r → W.DD T) (Z : Matrix (Fin r) (Fin r) (PowerSeries O)) (k : Fin r) :
    Formalism.MainNotions.LiftingTheory.qp W ^ c • gE W T h c e' Z k = Formalism.MainNotions.LiftingTheory.qp W ^ h • ftE W T e' Z k := by
  unfold gE
  rw [← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ c), smul_smul, map_pow, ← mul_pow,
    Ring.mul_inverse_cancel _ hq, one_pow, one_smul]

theorem qp_pow_inj (hq : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) (T : LocLat G Qp LL O)
    (c : ℕ) (z : W.DD T) (hz : Formalism.MainNotions.LiftingTheory.qp W ^ c • z = 0) : z = 0 := by
  calc z = ((Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) ^ c *
        (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W)) ^ c) • z := by
          rw [← mul_pow, Ring.inverse_mul_cancel _ hq, one_pow, one_smul]
    _ = (Ring.inverse (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) ^ c •
        (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ c) • z) := by rw [smul_smul, map_pow]
    _ = 0 := by rw [algebraMap_smul, hz, smul_zero]

theorem qp_mem_AΔ : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ :=
  W.AΔ.add_mem (Formalism.MainNotions.RamifiedCoefficientChains.S9.LD.uniformizer_mem_delta_invariants W) (W.AΔ.natCast_mem _)

theorem dl_of_qp (hq : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W))) (T : LocLat G Qp LL O)
    (i : ZMod n) (c : ℕ) (g y : W.DD T) (hgy : Formalism.MainNotions.LiftingTheory.qp W ^ c • g = y)
    (hy : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i y) : Formalism.MainNotions.CrystallineLiftingInputs.DL W T i g := by
  constructor
  · apply sub_eq_zero.1
    apply qp_pow_inj W hq T c
    rw [smul_sub, smul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ c) (letE i : LetA O n) g, hgy, hy.1, sub_self]
  · intro δ hδ
    apply sub_eq_zero.1
    apply qp_pow_inj W hq T c
    have hA : W.γA δ (Formalism.MainNotions.LiftingTheory.qp W ^ c) = Formalism.MainNotions.LiftingTheory.qp W ^ c :=
      W.AΔ.pow_mem (qp_mem_AΔ W) c δ hδ
    have e := Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.γD_smulA W T δ (Formalism.MainNotions.LiftingTheory.qp W ^ c) g
    rw [hA, hgy, hy.2 δ hδ] at e
    rw [smul_sub, ← e, hgy, sub_self]

theorem ring_clauses_at_uniformizer (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.Ring9 W := by
  have hfin1 : finrank K₀ K = 1 := by
    have := (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1).finrank_eq
    rw [Module.finrank_self] at this
    exact this.symm
  obtain ⟨-, -, h9'⟩ := h9 T hT hA.2.1 hA.2.2
  obtain ⟨hring, -⟩ := h9' hfin1
  exact hring

theorem gE_mem (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hRu : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W) (hEC : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit W)
    {d : ℕ} {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ}
    (hS : SetCS W d T₁ T₂ F b S η m) (i : ZMod n) (hi : i ∈ evens n d)
    (e' : Fin (finrank LL T₂.V) → W.DD T₂) (m' : ℕ) (u : Fin m' → ℤ)
    (had : AdaptData W T₂ i (b i + S) η m e' m' u) (σ : ℕ) (Z : Matrix _ _ (PowerSeries O))
    (hZP : ZProps W T₂ i (b i + S + η) σ e' had.1 Z) (j : Fin m') (hmr : m' ≤ finrank LL T₂.V) :
    gE W T₂ (b i + S) ((b i + S : ℕ) + u j).toNat e' Z (Fin.castLE hmr j) ∈ NDl W T₂ i := by
  have hie : (i.val + d) % 2 = 0 := (Finset.mem_filter.1 hi).2
  have hCA : Formalism.MainNotions.LiftingTheory.CaseA W := hS.1
  have hT : IsCrys PD T₂.ρ := hS.2.2.2.2.2.1.2.1
  have hl11 : 11 ≤ PD.p := hS.2.1
  obtain ⟨ζ, hζ⟩ := hS.2.2.2.2.1
  obtain ⟨-, hπu, w, hw⟩ := DetS.uniformizer_unit_and_q_factor W h9 hCA T₂ hT (by omega)
  have hq := DetS.qp_unit W hπu
  have hR9 := ring_clauses_at_uniformizer W h9 hCA T₂ hT
  obtain ⟨-, -, hmr', hwin, hfil, -⟩ := id had
  have hηb := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_eta_lt W hS i
  set h : ℕ := b i + S with hhdef
  set k : Fin (finrank LL T₂.V) := Fin.castLE hmr j with hkdef
  set c : ℕ := ((h : ℤ) + u j).toNat with hcdef
  have hc : (c : ℤ) = h + u j := Int.toNat_of_nonneg (by have := (hwin j).1; omega)

  have hyN : Formalism.MainNotions.LiftingTheory.qp W ^ h • ftE W T₂ e' Z k ∈ NDl W T₂ i := by
    unfold ftE
    rw [Finset.smul_sum]
    refine Submodule.sum_mem _ fun m₁ _ => ?_
    rw [smul_comm, pow_one]
    have hm := DetA.qpφ_mem W hE hC hQ h5 h9 hS i hie e' had.1 m₁
    have ha := Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_mem_invariants W hR9 (Z m₁ k)
    refine ⟨(W.N T₂).smul_mem _ hm.1, ?_, fun δ hδ => ?_⟩
    · rw [smul_comm (letE i : LetA O n), hm.2.1]
    · rw [Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.γD_smulA W T₂ δ, ha δ hδ, hm.2.2 δ hδ]
  have hgy := qp_smul_gE W hq T₂ h c e' Z k
  have hgDL := dl_of_qp W hq T₂ i c _ _ hgy hyN.2

  obtain ⟨u0, hlq, hu0⟩ := Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.lev_q_X_mul W i ζ hζ (by omega)
    (Formalism.MainNotions.N.Pv.LocalLengthBound.p_ne_zero_LL W)
  set U : PowerSeries LL := W.lev i ζ ((↑w⁻¹ : (LetA O n)ˣ) : LetA O n) * u0 with hUdef
  have hwq : W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W) = PowerSeries.X * U := by
    have e : Formalism.MainNotions.LiftingTheory.qp W = ((↑w⁻¹ : (LetA O n)ˣ) : LetA O n) * W.q := by
      rw [hw, ← mul_assoc, Units.inv_mul, one_mul]
    rw [e, map_mul, hlq, hUdef]; ring
  have hU : PowerSeries.constantCoeff U ≠ 0 := by
    rw [hUdef, map_mul]
    refine mul_ne_zero ?_ hu0
    exact (PowerSeries.isUnit_iff_constantCoeff.1 ((Units.isUnit _).map (W.lev i ζ))).ne_zero
  have hU0 : U ≠ 0 := fun h0 => hU (by rw [h0, map_zero])
  have hlevpow : ∀ t : ℕ, W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ t) = PowerSeries.X ^ t * U ^ t := by
    intro t; rw [map_pow, hwq, mul_pow]
  have hlevne : ∀ t : ℕ, W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ t) ≠ 0 := by
    intro t; rw [hlevpow]; exact mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (pow_ne_zero _ hU0)

  obtain ⟨hEx, hDi, -, -, hconv, -, -⟩ := hRu hCA T₂ hT i ζ hζ
  obtain ⟨df, hdf, -⟩ := hEx (ftE W T₂ e' Z k) _ hyN.1 (hlevne h)
  obtain ⟨dg, hdg, -⟩ := hEx (gE W T₂ h c e' Z k) (Formalism.MainNotions.LiftingTheory.qp W ^ c) (by rw [hgy]; exact hyN.1)
    (hlevne c)
  have hy1 := hconv (Formalism.MainNotions.LiftingTheory.qp W ^ h) _ df hdf
  have hy2 := hconv (Formalism.MainNotions.LiftingTheory.qp W ^ c) _ dg hdg
  rw [hgy] at hy2
  have huniq := (hEx (Formalism.MainNotions.LiftingTheory.qp W ^ h • ftE W T₂ e' Z k) 1 (by rw [one_smul]; exact hyN.1)
    (by rw [map_one]; exact one_ne_zero)).unique hy2 hy1
  obtain ⟨mg, hmg⟩ := hdg.1
  have hi1 : i - 1 + ((1 : ℕ) : ZMod n) = i := by push_cast; ring
  have hZ := hZP.2 k ζ hζ df (by rw [hi1]; exact hdf)
  have hv : ιV PD (LL := LL) (V := T₂.V) ((φVB PD (LL := LL) (V := T₂.V))^[1]
      (W.cmp T₂ ⟨e' k, (had.1.1 k).1⟩)) ∈ Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 (u j) := by
    rw [Function.iterate_one]; exact hfil j _
  set Fil : ℤ → Submodule LL (T₂.V ⊗[Qp] BdR) := fun a => Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 a with hFil
  have hanti : Antitone Fil := filLev_anti W T₂ i
  have hLBf : Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB 0 df := by
    intro t ht
    rw [hZ t (by omega), ite_eq_right (by omega)]
  set Ff := Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS (U ^ h) df with hFf
  set E := Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS (U ^ c) dg with hEdef
  have hF_mem : ∀ s : ℤ, s < ((h + η : ℕ) : ℤ) → Ff s ∈ Fil (u j) := by
    intro s hs
    rw [hFf, Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_eq_sum hLBf (U ^ h) s (s.toNat + 1)
      (by have := Int.self_le_toNat s; omega)]
    refine Submodule.sum_mem _ fun t _ => Submodule.smul_mem _ _ ?_
    rw [hZ _ (by omega)]
    split_ifs
    · exact Submodule.smul_mem _ _ hv
    · exact Submodule.zero_mem _
  have hF_neg : ∀ s : ℤ, s < 0 → Ff s = 0 := fun s hs =>
    Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB_smulS hLBf (U ^ h) s hs
  have hEF : ∀ t : ℤ, E t = Ff (t + u j) := by
    intro t
    have e1 : Formalism.MainNotions.RamifiedCoefficientChains.Sh.conv (W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ c)) dg = fun s => E (s - c) := by
      rw [hlevpow, Formalism.MainNotions.N.Pv.LocalLengthBound.conv_eq, Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_mul hmg,
        Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_X_pow (Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB_smulS hmg _)]
    have e2 : Formalism.MainNotions.RamifiedCoefficientChains.Sh.conv (W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ h)) df = fun s => Ff (s - h) := by
      rw [hlevpow, Formalism.MainNotions.N.Pv.LocalLengthBound.conv_eq, Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_mul hLBf,
        Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_X_pow (Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB_smulS hLBf _)]
    have e3 := congrFun huniq (t + c)
    rw [e1, e2] at e3
    simp only at e3
    rw [show t + (c : ℤ) - c = t by ring, show t + (c : ℤ) - h = t + u j by omega] at e3
    exact e3
  have hEDi : ∀ t, E t ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ i := fun t =>
    Formalism.MainNotions.N.Pv.LocalLengthBound.smulS_mem hmg _ (hDi _ dg hgDL hdg) (U ^ c) t
  have hlow : ∀ a : ℤ, a ≤ -(h : ℤ) → Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ i ≤ Fil a := by
    intro a ha
    refine ιDi_le_fil W hCA.1 T₂ i h (fun τ hτ a' ha' => ?_) a ha
    have hw2 := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumps₂ W hE hC hQ hS i τ hτ a' ha'
    unfold JumpWinS at hw2
    rw [ite_eq_left hie] at hw2
    simp only [Set.mem_union, Set.mem_Icc] at hw2
    rw [hhdef]; push_cast at hw2 ⊢
    omega
  have hDgE : Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.Dg Fil 0 E := by
    intro t
    by_cases ht : t + u j < ((h + η : ℕ) : ℤ)
    · rw [hEF t]
      by_cases h0 : t + u j < 0
      · rw [hF_neg _ h0]; exact Submodule.zero_mem _
      · exact hanti (show 0 - t ≤ u j by omega) (hF_mem _ ht)
    · exact hlow (0 - t) (by have := (hwin j).2; push_cast at ht; omega) (hEDi t)
  have hUc : PowerSeries.constantCoeff (U ^ c) ≠ 0 := by rw [map_pow]; exact pow_ne_zero _ hU
  have hdg_eq : dg = Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS (U ^ c)⁻¹ E :=
    (Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.smulS_inv hmg (U ^ c) hUc).symm
  have hDg : Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.Dg Fil 0 dg := by
    rw [hdg_eq]
    exact Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.Dg_smulS hanti (Formalism.MainNotions.N.Pv.LocalLengthBound.Ser.LB_smulS hmg _) hDgE _
  have hcrit := (hEC hCA T₂ hT i ζ hζ _ dg hgDL hdg).1 ⟨c, by rw [hgy]; exact hyN.1⟩
  refine ⟨hcrit.2 fun t => ?_, hgDL⟩
  have := hDg t
  simpa [hFil] using this

theorem gMem_of (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hRu : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W) (hEC : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit W) : GMem W :=
  fun _ _ _ _ _ _ _ _ hS i hi e' m' u had σ Z hZP j hmr =>
    gE_mem W hE hC hQ h5 h9 hRu hEC hS i hi e' m' u had σ Z hZP j hmr

end Formalism.MainNotions.RamifiedCoefficientChains.S9.GM
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LevLetEMul
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.DivLevR

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup PowerSeries

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} {W : LocWach PD LL O v n}

theorem letE_mem (a : ZMod n) : (letE a : LetA O n) ∈ W.AΔ := by
  intro δ _
  funext i
  simp only [LocWach.γA, letγ, AlgHom.pi_apply, AlgHom.comp_apply, Pi.evalAlgHom_apply, letE,
    Pi.single_apply]
  split_ifs <;> simp

theorem letE_idem (a : ZMod n) : (letE a : LetA O n) * letE a = letE a := by
  funext i
  simp only [Pi.mul_apply, letE, Pi.single_apply]
  split_ifs <;> simp

theorem lev_letE' (a : ZMod n) (ζ : LL) : W.lev a ζ (letE a : LetA O n) = 1 := by
  have h : W.lev a ζ (1 - letE a) = 0 := W.lev_letter a ζ _ (by simp [letE])
  rw [map_sub, map_one, sub_eq_zero] at h
  exact h.symm

theorem lev_letE_mul (a : ZMod n) (ζ : LL) (g : LetA O n) :
    W.lev a ζ ((letE a : LetA O n) * g) = W.lev a ζ g := by
  rw [map_mul, lev_letE', one_mul]

theorem lev_q_X (a : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    ∃ R : PowerSeries LL, constantCoeff R ≠ 0 ∧ W.lev a ζ W.q = X * R := by
  have hζ1 : IsPrimitiveRoot ζ (PD.p ^ 1) := by rwa [pow_one]
  obtain ⟨E, hE0, hED, hE⟩ := W.lev_π a ζ ⟨1, hζ1⟩
  have hq : (letπ : LetA O n) * W.q = (1 + letπ) ^ PD.p - 1 := by
    funext i
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, Pi.add_apply, Pi.one_apply, letπ,
      LocWach.q, W.q₀_def]
  set F : PowerSeries LL := C ζ * E with hF
  have hL := congrArg (W.lev a ζ) hq
  simp only [map_mul, map_sub, map_pow, map_add (f := _), map_one] at hL
  rw [hE] at hL
  set P := W.lev a ζ letπ with hP
  set Lq := W.lev a ζ W.q with hLq
  have hP0 : constantCoeff P = ζ - 1 := by
    have := congrArg constantCoeff hE
    rw [map_add (f := _), map_one, map_mul, constantCoeff_C, hE0, mul_one] at this
    linear_combination this
  have hζne : ζ ≠ 1 := hζ.ne_one PD.hp.one_lt
  have hζp : ζ ^ PD.p = 1 := hζ.pow_eq_one
  have hsub : ζ - 1 ≠ 0 := sub_ne_zero.mpr hζne

  have h0 := congrArg constantCoeff hL
  rw [map_mul, map_sub, map_pow, map_one, hF, map_mul, constantCoeff_C, hE0, mul_one, hζp,
    sub_self, hP0] at h0
  have hLq0 : constantCoeff Lq = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h hsub
    · exact h
  obtain ⟨R, hR⟩ := X_dvd_iff.mpr hLq0
  refine ⟨R, ?_, hR⟩
  intro hR0

  have hD : derivative (R := LL) F = F := by
    rw [hF, Derivation.leibniz, hED]
    simp
  have hd := congrArg (fun f => constantCoeff (derivative (R := LL) f)) hL
  rw [map_sub, Derivation.leibniz_pow, hD, Derivation.map_one_eq_zero, sub_zero] at hd
  obtain ⟨R', hR'⟩ := X_dvd_iff.mpr hR0
  have hLq2 : Lq = X ^ 2 * R' := by rw [hR, hR']; ring
  rw [hLq2, Derivation.leibniz, Derivation.leibniz, Derivation.leibniz_pow] at hd
  simp only [smul_eq_mul, map_add (f := _), map_mul, map_pow, map_nsmul, constantCoeff_X] at hd
  have hF0 : constantCoeff F = ζ := by rw [hF, map_mul, constantCoeff_C, hE0, mul_one]
  rw [hF0] at hd
  have hpζ : (PD.p : LL) * ζ ^ PD.p = 0 := by
    have e : (PD.p - 1) + 1 = PD.p := Nat.sub_add_cancel PD.hp.one_le
    have := hd
    simp only [nsmul_eq_mul] at this
    rw [← pow_succ, e] at this
    rw [← this]
    simp
  rw [hζp, mul_one] at hpζ
  have h2 := W.v_l
  rw [hpζ, AddValuation.map_zero] at h2
  exact absurd h2 (by simp)

section Div

variable [IsDomain O]

theorem lev_qP_X (hR : ToolsR.RingP W) (a : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) :
    ∃ S : PowerSeries LL, constantCoeff S ≠ 0 ∧ W.lev a ζ (qP W) = X * S := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  rw [ToolsR.eat_qP] at hw
  obtain ⟨R, hR0, hRq⟩ := lev_q_X (W := W) a ζ hζ
  have hLw : IsUnit (W.lev a ζ (w : LetA O n)) := w.isUnit.map _
  have hcw : constantCoeff (W.lev a ζ (w : LetA O n)) ≠ 0 := (hLw.map constantCoeff).ne_zero
  have e : X * R = W.lev a ζ (w : LetA O n) * W.lev a ζ (qP W) := by rw [← hRq, hw, map_mul]
  have h0 : constantCoeff (W.lev a ζ (qP W)) = 0 := by
    have := congrArg constantCoeff e
    rw [map_mul, map_mul, constantCoeff_X, zero_mul] at this
    rcases mul_eq_zero.mp this.symm with h | h
    · exact absurd h hcw
    · exact h
  obtain ⟨S, hS⟩ := X_dvd_iff.mpr h0
  refine ⟨S, ?_, hS⟩
  rw [hS, mul_left_comm] at e
  have e2 := mul_left_cancel₀ X_ne_zero e
  intro hS0
  apply hR0
  rw [e2, map_mul, hS0, mul_zero]

variable [IsAdicComplete (Ideal.span {((PD.p : ℕ) : O)}) O]

theorem step (hR : ToolsR.RingP W) (hpu : ¬ IsUnit ((PD.p : ℕ) : O))
    (hinj : Function.Injective (algebraMap O LL)) (a : ZMod n) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (g : LetA O n) (hg : g ∈ W.AΔ) (h0 : coeff 0 (W.lev a ζ g) = 0) :
    ∃ h ∈ W.AΔ, (letE a : LetA O n) * g = qP W * h := by
  obtain ⟨f, hf, -⟩ := hR.2.1 g hg
  set I : Ideal O := Ideal.span {((PD.p : ℕ) : O)} with hIdef
  have : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr (by
    rw [Ne, hIdef, Ideal.span_singleton_eq_top]; exact hpu)
  have hpI : Ideal.Quotient.mk I ((PD.p : ℕ) : O) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  set D : PowerSeries O := X + C ((PD.p : ℕ) : O) with hD
  have hmap : D.map (Ideal.Quotient.mk I) = X := by
    rw [hD, map_add (f := _), map_X, map_C, hpI, map_zero, add_zero]
  have hord : (D.map (Ideal.Quotient.mk I)).order.toNat = 1 := by rw [hmap, order_X]; rfl
  have hdiv : D.IsWeierstrassDivisorAt I := by
    unfold IsWeierstrassDivisorAt
    rw [hord, hD, map_add (f := _), coeff_C, if_neg one_ne_zero, add_zero]
    simp [coeff_X]
  have HD := hdiv.isWeierstrassDivisionAt_div_mod (f := f a)
  set H := hdiv.div (f a)
  set r := hdiv.mod (f a)
  have hdeg : r.degree < 1 := by
    have := HD.degree_lt
    rw [hord] at this
    exact_mod_cast this
  have heq : f a = D * H + (r : PowerSeries O) := HD.eq_mul_add
  have hr : (r : PowerSeries O) = r.coeff 0 • (1 : PowerSeries O) := by
    have hle : r.degree ≤ 0 := by
      exact Nat.WithBot.lt_one_iff_le_zero.mp hdeg
    conv_lhs => rw [Polynomial.eq_C_of_degree_le_zero hle]
    rw [Polynomial.coe_C, smul_eq_C_mul, mul_one]
  have hDn : D = X + ((PD.p : ℕ) : PowerSeries O) := by rw [hD, map_natCast]
  have ha0 : constantCoeff W.π₀₁ = 0 := ToolsR.π₀₁_cc hR
  have hs0 := HasSubst.of_constantCoeff_zero' ha0
  have hga : g a = (W.π₀₁ + ((PD.p : ℕ) : PowerSeries O)) * subst W.π₀₁ H +
      r.coeff 0 • (1 : PowerSeries O) := by
    rw [hf a]
    change subst W.π₀₁ (f a) = _
    rw [heq, hr, hDn, ← coe_substAlgHom hs0, map_add (f := _), map_mul, map_add (f := _), substAlgHom_X, map_natCast,
      map_smul, map_one]
  set h : LetA O n := Pi.single a (subst W.π₀₁ H) with hh
  have key : (letE a : LetA O n) * g = qP W * h + r.coeff 0 • (letE a : LetA O n) := by
    funext i
    by_cases hi : i = a
    · subst hi
      simp only [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, hh, letE, Pi.single_eq_same, one_mul,
        hga, qP, LocWach.π₀, Pi.natCast_apply]
    · simp [Pi.mul_apply, Pi.add_apply, Pi.smul_apply, hh, letE, Pi.single_eq_of_ne hi]
  obtain ⟨S, -, hS⟩ := lev_qP_X hR a ζ hζ
  have hL := congrArg (fun x => coeff 0 (W.lev a ζ x)) key
  simp only [map_add (f := _), map_mul, map_smul, lev_letE', hS, one_mul] at hL
  rw [h0, mul_assoc, coeff_zero_X_mul, zero_add, coeff_smul, coeff_zero_eq_constantCoeff,
    map_one, Algebra.smul_def, mul_one] at hL
  have hc : r.coeff 0 = 0 := hinj (by rw [← hL, map_zero])
  rw [hc, zero_smul, add_zero] at key
  refine ⟨h, ?_, key⟩
  refine ToolsR.cancel_AΔ (ToolsR.qP_AΔ hR) (fun i hq => by
    have := congrArg constantCoeff hq
    simp only [qP, Pi.add_apply, LocWach.π₀, Pi.natCast_apply, map_add (f := _), ToolsR.π₀₁_cc hR, map_natCast,
      zero_add, map_zero] at this
    have h1 : ((PD.p : ℕ) : LL) = 0 := by
      rw [← map_natCast (algebraMap O LL), this, map_zero]
    have h2 := W.v_l
    rw [h1, AddValuation.map_zero] at h2
    exact absurd h2 (by simp)) ?_
  rw [← key]
  exact W.AΔ.mul_mem (letE_mem a) hg

theorem divLev_of (hR : ToolsR.RingP W) (hpu : ¬ IsUnit ((PD.p : ℕ) : O))
    (hinj : Function.Injective (algebraMap O LL)) (a : ZMod n) (ζ : LL)
    (hζ : IsPrimitiveRoot ζ PD.p) : LevC.DivLev (W := W) a ζ := by
  intro g hg k
  induction k generalizing g with
  | zero =>
    intro _
    exact ⟨letE a * g, W.AΔ.mul_mem (letE_mem a) hg, by simp⟩
  | succ k ih =>
    intro hv
    obtain ⟨S, hS0, hLqP⟩ := lev_qP_X hR a ζ hζ
    obtain ⟨h1, h1m, e1⟩ := step hR hpu hinj a ζ hζ g hg (hv 0 (Nat.succ_pos _))
    have hLg : W.lev a ζ g = X * (S * W.lev a ζ h1) := by
      rw [← lev_letE_mul, e1, map_mul, hLqP, mul_assoc]
    have hv1 : ∀ j < k, coeff j (W.lev a ζ h1) = 0 := by
      have hd : X ^ (k + 1) ∣ X * (S * W.lev a ζ h1) := by
        rw [← hLg]
        exact X_pow_dvd_iff.mpr hv
      rw [pow_succ', mul_dvd_mul_iff_left X_ne_zero] at hd
      have hSu : IsUnit S := by
        rw [isUnit_iff_constantCoeff]
        exact isUnit_iff_ne_zero.mpr hS0
      exact X_pow_dvd_iff.mp ((hSu.dvd_mul_left).mp hd)
    obtain ⟨h2, h2m, e2⟩ := ih h1 h1m hv1
    refine ⟨h2, h2m, ?_⟩
    have hps : ps W 0 = qP W := by
      rw [ps, pow_zero]
      rfl
    rw [hps, ← letE_idem a, mul_assoc, e1, mul_left_comm, e2, hps, ← mul_assoc, ← pow_succ']

end Div

end Formalism.MainNotions.UnusedSlot80.DivLevR
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.QPowSmulFrobeniusMem
noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains
open Formalism.MainNotions.N.Pv.LocalLengthBound.Ser

section LemGAxF

variable {R M : Type} [Field R] [AddCommGroup M] [Module R M]

def lemGAx_F (B K : ℤ) (c : M) (k : ℤ) : Submodule R M :=
  if k < -B then ⊥ else if k < K then Submodule.span R {c} else ⊤

theorem lemGAx_F_mono (B K : ℤ) (c : M) : Monotone (lemGAx_F (R := R) B K c) := by
  intro a a' h
  unfold lemGAx_F
  split_ifs <;> first | exact bot_le | exact le_top | exact le_rfl | (exfalso; omega)

end LemGAxF

section LemGAx

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem lemGAx_pull1N (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (c : ZMod n) (k : ℕ)
    (hgen : ∀ x, x ∈ W.N T → Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x →
      Formalism.MainNotions.LiftingTheory.qp W ^ k • W.φD T x ∈ W.N T) :
    ∀ p ∈ Formalism.MainNotions.CrystallineLiftingInputs.pullJ W T c 1, Formalism.MainNotions.LiftingTheory.qp W ^ k • p ∈ W.N T := by
  intro p hp
  induction hp using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨x, ⟨hxN, hxD⟩, rfl⟩ := hg
    simpa using hgen x hxN hxD
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ a hx

theorem q_pow_smul_frobenius_mem (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W)
    (hs : W.s = 1) {M h : ZMod n → ℕ} (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h) (c : ZMod n) :
    ∀ x, x ∈ W.N T → Formalism.MainNotions.CrystallineLiftingInputs.DL W T c x →
      Formalism.MainNotions.LiftingTheory.qp W ^ M (c + 1) • W.φD T x ∈ W.N T := by
  intro x hxN hxD
  have hxl : x ∈ W.Nl T (c + 1 - 1) := by
    rw [add_sub_cancel_right]
    exact ⟨x, hxN, by rw [LinearMap.smul_apply, LinearMap.id_apply, hxD.1]⟩
  exact (Formalism.MainNotions.LiftingTheory.lifta_Qq W hR hs T _ _).1 (h5.1 (c + 1) x hxl)

theorem lemGAx_parity {n : ℕ} [NeZero n] (hn : Even n) (d : ℕ) (i : ZMod n) (hi : (i.val + d) % 2 = 1) :
    ((i - 1).val + d) % 2 = 0 := by
  have := parity_succ hn d (i - 1)
  rw [sub_add_cancel] at this
  omega

theorem lemGA_x_of [NeZero n] (W : LocWach PD LL O v n)
    (hER : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRing W) (hEU : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W)
    (hEC : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpCrit W) (hTH : Formalism.MainNotions.CrystallineLiftingInputs.THor W)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (hR : Formalism.MainNotions.LiftingTheory.lifta_Ring W)
    (hJ : ∀ (d : ℕ) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) (b : ZMod n → ℕ) (S η m : ℕ),
      SetCS W d T₁ T₂ F b S η m → Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T₂ (MiW d b S η) (hiW d b S η)) :
    GammaActionLemma W := by
  intro d T₁ T₂ F b S η m hS i hi y hy hyD hFil la hla
  obtain ⟨htr, hlaD, hlaP, -⟩ := hla
  have hA : Formalism.MainNotions.LiftingTheory.CaseA W := hS.1
  have hl : 11 ≤ PD.p := hS.2.1
  have hn : Even n := hS.2.2.1
  have hT : IsCrys PD T₂.ρ := hS.2.2.2.2.2.1.2.1
  have hπ : W.π₀ ∈ W.AΔ := hR.πΔ
  have hq : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ := W.AΔ.add_mem hπ (W.AΔ.natCast_mem _)
  have hp1 : Formalism.MainNotions.LiftingTheory.pk W 1 ∈ W.AΔ := Formalism.MainNotions.UnusedSlot80.Relay2.pk_mem_AΔ W hπ 1
  have hJ2 := hJ d T₁ T₂ F b S η m hS
  have hp5 := h5 T₂ (MiW d b S η) (hiW d b S η) hT hJ2
  have hpar1 := lemGAx_parity hn d i hi
  have hMi : MiW d b S η i = η := by unfold MiW; rw [if_neg (by omega)]
  have hM2 : MiW d b S η (i - 1 + 1) = η := by rw [sub_add_cancel]; exact hMi
  have hbH : b i ≤ hpar n b S := by
    unfold hpar; exact le_trans (Finset.le_sup (Finset.mem_univ i)) (Nat.le_add_right _ _)
  set H := hpar n b S + η with hH
  set σ := lemG_sig PD.p H with hσ
  set h₂ := b (i - 1) + S with hh₂

  have hg2 : ∀ x, x ∈ W.N T₂ → Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ (i - 1) x →
      Formalism.MainNotions.LiftingTheory.qp W ^ η • W.φD T₂ x ∈ W.N T₂ := by
    intro x hxN hxD
    have := q_pow_smul_frobenius_mem W T₂ hR hA.2.1 hp5 (i - 1) x hxN hxD
    rwa [hM2] at this
  have hm0 : Formalism.MainNotions.LiftingTheory.qp W ^ η • (Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂ • la) ∈ W.N T₂ :=
    lemGAx_pull1N W T₂ (i - 1) η hg2 _ hlaP

  obtain ⟨Uq, hUq⟩ := hR.qU
  set x : W.DD T₂ := ((Uq⁻¹ : W.EEˣ) : W.EE) ^ b i • (Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂ • la) with hxdef
  have hxe : Formalism.MainNotions.LiftingTheory.qp W ^ b i • x = Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂ • la := by
    rw [hxdef, ← algebraMap_smul W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ b i), smul_smul, map_pow, ← hUq, ← mul_pow,
      Units.mul_inv, one_pow, one_smul]
  have hqU : IsUnit (algebraMap (LetA O n) W.EE (Formalism.MainNotions.LiftingTheory.qp W ^ b i)) := by
    rw [map_pow]; exact hR.qU.pow _
  have hxD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ i x := by
    refine ⟨?_, fun δ hδ => ?_⟩
    · apply Formalism.MainNotions.UnusedSlot80.SatW.smul_cancel W T₂ hqU
      rw [smul_comm, hxe, smul_comm, hlaD.1]
    · apply Formalism.MainNotions.UnusedSlot80.SatW.smul_cancel W T₂ hqU
      calc Formalism.MainNotions.LiftingTheory.qp W ^ b i • W.γD T₂ δ x
          = W.γA δ (Formalism.MainNotions.LiftingTheory.qp W ^ b i) • W.γD T₂ δ x := by rw [(W.AΔ.pow_mem hq (b i)) δ hδ]
        _ = W.γD T₂ δ (Formalism.MainNotions.LiftingTheory.qp W ^ b i • x) :=
            (Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA' W T₂ δ _ x).symm
        _ = W.γD T₂ δ (Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂ • la) := by rw [hxe]
        _ = W.γA δ (Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂) • W.γD T₂ δ la :=
            Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA' W T₂ δ _ la
        _ = Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂ • la := by rw [(W.AΔ.pow_mem hp1 h₂) δ hδ, hlaD.2 δ hδ]
        _ = Formalism.MainNotions.LiftingTheory.qp W ^ b i • x := hxe.symm
  have hmx : Formalism.MainNotions.LiftingTheory.qp W ^ (b i + η) • x ∈ W.N T₂ := by
    rw [pow_add, mul_comm, mul_smul, hxe]; exact hm0

  obtain ⟨ζ, hζ⟩ := hS.2.2.2.2.1
  obtain ⟨⟨u, hu, hlq⟩, -, -⟩ := hER hA i ζ hζ
  have hu0 : PowerSeries.constantCoeff u ≠ 0 := (PowerSeries.isUnit_iff_constantCoeff.1 hu).ne_zero
  have hlevq : W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ (b i + η)) =
      PowerSeries.X ^ (b i + η) * u ^ (b i + η) := by
    rw [map_pow, hlq, mul_pow, mul_comm]
  have hlev0 : W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ (b i + η)) ≠ 0 := by
    rw [hlevq]
    exact mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (pow_ne_zero _ hu.ne_zero)
  obtain ⟨dx, hdx, -⟩ := (hEU hA T₂ hT i ζ hζ).1 x _ hmx hlev0
  obtain ⟨m₀, hm₀⟩ := hdx.1
  have hLB : LB m₀ dx := hm₀
  have hrel : W.levN T₂ i ζ ⟨_, hmx⟩ = fun k => smulS (u ^ (b i + η)) dx (k - ((b i + η : ℕ) : ℤ)) := by
    have h1 := Formalism.MainNotions.N.Pv.LocalLengthBound.isExp_smulA W T₂ i ζ hdx (Formalism.MainNotions.LiftingTheory.qp W ^ (b i + η))
    have h2 := Formalism.MainNotions.N.Pv.LocalLengthBound.isExp_self W T₂ i ζ hmx
    rw [Formalism.MainNotions.N.Pv.LocalLengthBound.isExp_unique W T₂ i ζ h2 h1, hlevq, smulS_mul hLB,
      smulS_X_pow (LB_smulS hLB _)]
  have hsh : ∀ k : ℤ, smulS (u ^ (b i + η)) dx k =
      W.levN T₂ i ζ ⟨_, hmx⟩ (k + ((b i + η : ℕ) : ℤ)) := by
    intro k; rw [hrel]; simp

  have hyΔ : Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (i - 2) y :=
    Formalism.MainNotions.UnusedSlot80.Relay2.InNΔi_of W T₂ (i - 2) ⟨hy, hyD.2⟩ hyD.1
  have hyI : Formalism.MainNotions.CrystallineLiftingInputs.InI W T₂ (i - 2) y := by
    refine ⟨hyD, ⟨0, 0, by simpa using hy⟩, ?_⟩
    obtain ⟨x', hx', he⟩ := Formalism.MainNotions.LiftingTheory.coreH_graded_of W h9 hA T₂ hT (i - 2) 0 y hyΔ
    refine ⟨x', hx'.1.1, hx'.1.2, ?_⟩
    simpa using he
  have hTC : Formalism.MainNotions.CrystallineLiftingInputs.TCase PD.p 2 1 (2 * H) σ := Or.inr ⟨rfl, rfl, rfl⟩
  have hk : (Formalism.MainNotions.LiftingTheory.qp W ^ η * Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂) • la ∈ W.N T₂ := by
    rw [mul_smul]; exact hm0
  have hmm : (⟨Formalism.MainNotions.LiftingTheory.qp W ^ (b i + η) • x, hmx⟩ : ↥(W.N T₂)) = ⟨_, hk⟩ := by
    apply Subtype.ext
    show Formalism.MainNotions.LiftingTheory.qp W ^ (b i + η) • x = (Formalism.MainNotions.LiftingTheory.qp W ^ η * Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂) • la
    rw [pow_add, mul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ b i), mul_smul, hxe, mul_smul]
  obtain ⟨hneg, hcoef⟩ := hTH hA hl 2 1 (2 * H) σ hTC T₂ hT (i - 2) y la hy hyI htr ζ (η + 2 * H) η
    (Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂) hk (Or.inl ⟨hζ, rfl⟩)
  have e2 : i - 2 + ((2 : ℕ) : ZMod n) = i := by push_cast; ring
  rw [e2] at hneg hcoef
  set c0 : TensorProduct Qp T₂.V BdR := (PD.p : LL) ^ σ • ιV PD (LL := LL) (V := T₂.V)
    ((φVB PD (LL := LL) (V := T₂.V))^[2] (W.cmp T₂ ⟨y, hy⟩)) with hc0
  have hlevk : W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ η * Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂) =
      PowerSeries.X ^ η * (u ^ η * W.lev i ζ (Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂)) := by
    rw [map_mul, map_pow (W.lev i ζ) (Formalism.MainNotions.LiftingTheory.qp W) η, hlq, mul_pow, mul_comm (u ^ η), mul_assoc]
  have hc00 : ∀ r : ℕ, r < η →
      PowerSeries.coeff r (W.lev i ζ (Formalism.MainNotions.LiftingTheory.qp W ^ η * Formalism.MainNotions.LiftingTheory.pk W 1 ^ h₂)) = 0 := by
    intro r hr
    rw [hlevk, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]

  have hg : ∀ k : ℤ, smulS (u ^ (b i + η)) dx k ∈
      lemGAx_F (R := LL) (b i : ℤ) (((2 * H : ℕ) : ℤ) - (b i : ℤ)) c0 k := by
    intro k
    rw [hsh, hmm]
    unfold lemGAx_F
    by_cases hk0 : k + ((b i + η : ℕ) : ℤ) < 0
    · rw [hneg _ hk0]
      split_ifs <;> exact Submodule.zero_mem _
    · obtain ⟨r, hr⟩ : ∃ r : ℕ, k + ((b i + η : ℕ) : ℤ) = r :=
        ⟨(k + ((b i + η : ℕ) : ℤ)).toNat, by omega⟩
      rw [hr]
      push_cast at hr
      split_ifs with h1 h2
      · rw [hcoef r (by omega), hc00 r (by omega), zero_smul]
        exact Submodule.zero_mem _
      · rw [hcoef r (by push_cast at h2; omega)]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
      · trivial
  have hF := Formalism.MainNotions.UnusedSlot80.LevR.laurent_div (lemGAx_F (R := LL) (b i : ℤ) (((2 * H : ℕ) : ℤ) - (b i : ℤ)) c0)
    (lemGAx_F_mono _ _ _) hm₀ (u ^ (b i + η)) (by rw [map_pow]; exact pow_ne_zero _ hu0) hg

  have hcy : W.cmp T₂ ⟨y, hy⟩ ∈ DcrisL PD T₂.ρ (W.emb (i - 2)) := by
    have h := W.cmp_letter T₂ (i - 2) ⟨y, hy⟩
    have e : ((letE (i - 2) : LetA O n) • (⟨y, hy⟩ : ↥(W.N T₂))) = ⟨y, hy⟩ := Subtype.ext hyD.1
    rwa [e] at h
  have hφy : (φVB PD (LL := LL) (V := T₂.V))^[2] (W.cmp T₂ ⟨y, hy⟩) ∈ DcrisL PD T₂.ρ (W.emb i) := by
    have h := Formalism.MainNotions.UnusedSlot80.UnivC.φVB_pow_letter W T₂ (i - 2) 2 hcy
    rwa [e2, Module.End.pow_apply] at h
  have hc0mem : ∀ k : ℤ, -(b i : ℤ) ≤ k →
      c0 ∈ Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ i ⊓ FilV PD (LL := LL) (V := T₂.V) (-k) := by
    intro k hk
    refine Submodule.mem_inf.2 ⟨Submodule.smul_mem _ _ ⟨_, hφy, rfl⟩, Submodule.smul_mem _ _ ?_⟩
    have hF0 : ιV PD (LL := LL) (V := T₂.V)
        ((φVB PD (LL := LL) (V := T₂.V))^[2] (W.cmp T₂ ⟨y, hy⟩)) ∈
          FilV PD (LL := LL) (V := T₂.V) (b i : ℤ) := (Submodule.mem_inf.1 hFil).2
    exact Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (PD := PD) (show -k ≤ (b i : ℤ) by omega) hF0
  set τ := Formalism.MainNotions.N.Pv.LocalLengthBound.tauOf W hA.1 i with hτ
  have hover : Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ i := by
    apply AlgHom.ext
    intro c
    rw [AlgHom.comp_apply, IsScalarTower.coe_toAlgHom']
    exact Formalism.MainNotions.N.Pv.LocalLengthBound.tauOf_over W hA.1 i c
  have hjump : ∀ a, IsJumpV PD T₂.ρ τ a → -(η : ℤ) ≤ a := by
    intro a ha
    have := (hJ2 τ i hover a ha).1
    rwa [hMi] at this
  have hDi : Formalism.MainNotions.DeltaInvariantLattices.ιDi W T₂ i ≤ FilV PD (LL := LL) (V := T₂.V) (-(η : ℤ)) := by
    intro z hz
    have h1 := Formalism.MainNotions.UnusedSlot80.LevR.ιDi_le W T₂ i τ (Formalism.MainNotions.N.Pv.LocalLengthBound.tauOf_over W hA.1 i) hA.1.2 hz
    rw [← Formalism.MainNotions.UnusedSlot80.UnivF.fildR_eq_top_of (PD := PD) (ρ := T₂.ρ) τ (-(η : ℤ)) hjump] at h1
    exact (Submodule.mem_inf.1 h1).2

  have hxN : x ∈ W.N T₂ := by
    refine ((hEC hA T₂ hT i ζ hζ x dx hxD hdx).1 ⟨b i + η, hmx⟩).2 fun k => ?_
    have hk := hF k
    rw [Formalism.MainNotions.UnusedSlot80.LevR.filLev_zero W T₂ i (-k)]
    unfold lemGAx_F at hk
    split_ifs at hk with h1 h2
    · rw [(Submodule.mem_bot LL).1 hk]; exact Submodule.zero_mem _
    · exact (Submodule.span_le.2 (Set.singleton_subset_iff.2 (hc0mem k (by omega)))) hk
    · refine Submodule.mem_inf.2 ⟨(hEU hA T₂ hT i ζ hζ).2.1 x dx hxD hdx k, ?_⟩
      refine Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (PD := PD) (show -k ≤ -(η : ℤ) by push_cast at h2; omega)
        (hDi ((hEU hA T₂ hT i ζ hζ).2.1 x dx hxD hdx k))
  exact ⟨x, hxN, hxD, hxe⟩

end LemGAx

end Formalism.MainNotions.RamifiedCoefficientChains.S9
end
end
