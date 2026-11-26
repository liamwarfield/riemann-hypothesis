module

public import Formalism.SharpRestriction.LevelLetterCocycles.ExistsPrimOfGood
public import Formalism.SharpRestriction.LevelLetterCocycles.SecOfPInt
public import Formalism.SharpRestriction.LevelLetterCocycles.CancelUnitMulUniformizerPow

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.PolarToPoleOfCtx
noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80.PhiPowers

variable [IsDomain O] [NeZero n]

theorem dvO_zero_hw (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (T : LocLat G Qp LL O)
    (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e : ℕ)
    (a : ZMod n) (s : ℕ) (u : ℤ) (hu : (Hw A.G₀ A.S A.η (A.ty (a - (s : ZMod n))) : ℤ) < u)
    (c₀ : Fin d → O) (h : dvO W T e b c₀ ∈ FilS W T a s u) : c₀ = 0 := by
  obtain ⟨y, ⟨hyF, hyD⟩, hye⟩ := h
  set i : ZMod n := a - (s : ZMod n) with hidef
  obtain ⟨τ, hτ, hover⟩ := tau_over W C.hbij i
  have hJ : ∀ z, IsJumpV PD T.ρ τ z → z ≤ (Hw A.G₀ A.S A.η (A.ty i) : ℤ) := fun z hz =>
    (Formalism.MainNotions.UnusedSlot80.PhiPowers.win_sub A.G₀ A.S A.η (A.ty i) (hA.2.2.2.2.1 i) (hT.2 i τ hτ z hz)).2
  have hy0 := fil_high W T i τ hover C.hbij.2 _ hJ u hu hyD hyF
  rw [hy0, map_zero] at hye
  have hfb := (Formalism.MainNotions.UnusedSlot80.ArcF.frame_basis W C.hs C.hV T (C.h3 T hT.1)
    (C.h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT)) (C.hmod T hT.1) c' e b hb).1
  have hdv : dvO W T e b c₀ = ∑ m, algebraMap O LL (c₀ m) • dv W T e b (Pi.single m 1) := by
    simp only [Formalism.MainNotions.UnusedSlot80.ArcF.dv_single]; rfl
  have hsum : ∑ m, algebraMap O LL (c₀ m) • dv W T e b (Pi.single m 1) = 0 := by rw [← hdv, ← hye]
  funext m
  apply C.hinj
  rw [Fintype.linearIndependent_iff.1 hfb _ hsum m]
  simp

theorem filS_anti (T : LocLat G Qp LL O) (a : ZMod n) (s : ℕ) {u w : ℤ} (h : w ≤ u) :
    FilS W T a s u ≤ FilS W T a s w := by
  apply Submodule.map_mono
  intro x hx
  exact ⟨Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ h hx.1, hx.2⟩

theorem inId_zero (a : ZMod n) (e : ℕ) : InId W a e (fun _ => 0) 0 :=
  ⟨0, W.AΔ.zero_mem, by simp⟩

theorem condPole_of_polar (C : Ctx W) (A : ArcP n) (hA : A.OK) (c' : ZMod n) (T : LocLat G Qp LL O)
    (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (c : ZMod n)
    (α : ℕ → ℤ) (c₀ : Fin d → O) (hc₀ : c₀ ≠ 0)
    (hP : Formalism.MainNotions.UnusedSlot80.LevC.condPolar (W := W) T c (A.len c) b α c₀) :
    condPole W A T c b α c₀ := by
  intro s hs
  have key : 0 ≤ α s ∨ -(Hw A.G₀ A.S A.η (A.ty (c - (s : ZMod n))) : ℤ) ≤ α s ∧
      dvO W T (A.len c) b c₀ ∈ FilS W T c s (-(α s)) := by
    rcases hP s hs with h | h
    · exact Or.inl h
    · by_cases h0 : 0 ≤ α s
      · exact Or.inl h0
      · refine Or.inr ⟨?_, h⟩
        by_contra hlt
        exact hc₀ (dvO_zero_hw W C A hA c' T hT b hb (A.len c) c s (-(α s)) (by omega) c₀ h)
  cases hty : A.ty (c - (s : ZMod n)) with
  | thin =>
    rw [hty] at key
    simp only [Hw] at key
    rcases key with h | ⟨h, -⟩ <;> omega
  | up bs =>
    rw [hty] at key
    simp only [Hw] at key
    rcases key with h | ⟨h, -⟩ <;> push_cast at h ⊢ <;> omega
  | down bs =>
    rcases key with h | ⟨-, h⟩
    · exact Or.inl h
    · by_cases h0 : 0 ≤ α s
      · exact Or.inl h0
      · exact Or.inr (filS_anti W T c s (by omega) h)

variable {W}

theorem polarToPole_of_ctx (C : Ctx W) : Formalism.MainNotions.UnusedSlot80.Split.PolarToPole W := by
  intro _ _ A hA T₂ hT c hc d b sol hb f hS
  obtain ⟨I, g, c₀, α, hg, hF⟩ := hS
  refine ⟨I, fun i => if c₀ i = 0 then 0 else g i, c₀, fun i => if c₀ i = 0 then fun _ => 0 else α i,
    fun i => ?_, fun k => ?_⟩
  · by_cases h0 : c₀ i = 0
    · simp only [h0, if_true]
      refine ⟨inId_zero W c (A.len c), ?_⟩
      intro s _
      cases A.ty (c - (s : ZMod n)) with
      | thin => simp
      | up bs => simp
      | down bs => exact Or.inl le_rfl
    · simp only [h0, if_false]
      exact ⟨(hg i).1, condPole_of_polar W C A hA _ T₂ hT b hb.1 c (α i) (c₀ i) h0 (hg i).2⟩
  · rw [hF k]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h0 : c₀ i = 0
    · simp [h0]
    · simp [h0]

end Formalism.MainNotions.UnusedSlot80.LevC

namespace Formalism.MainNotions.UnusedSlot80.Split

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

theorem polarToPoleL_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h : AdmArcA D HW F Cm) : PolarToPoleL D HW := by
  intro l _ K LL hG hCA h5l
  have := neZero_finrank_max_unramified K
  exact LevC.polarToPole_of_ctx (ctx_of D HW F Cm h l K LL hG hCA h5l)

end Formalism.MainNotions.UnusedSlot80.Split
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.SplitShapeLRec
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.SplitPolarLOf
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.IntAOfNonpol
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.LetterPull
noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.SplitP

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.TruncatedSeriesCountingBounds

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem dv_sum (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → LL) :
    dv W T e b c₀ = ∑ k, c₀ k • dv W T e b (Pi.single k 1) := by
  unfold dv
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Formalism.MainNotions.UnusedSlot80.ArcF.dv_single]
  unfold dv
  rfl

theorem dvO_sum (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c : Fin d → O) :
    dvO W T e b c = ∑ k, algebraMap O LL (c k) • dv W T e b (Pi.single k 1) := by
  unfold dvO; rw [dv_sum]

theorem dvO_smul (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (o : O) (c : Fin d → O) :
    dvO W T e b (fun k => o * c k) = algebraMap O LL o • dvO W T e b c := by
  rw [dvO_sum, dvO_sum, Finset.smul_sum]
  simp only [map_mul, mul_smul]

theorem coef_eq {M : Type} [AddCommGroup M] [Module LL M] {dY : ℕ} (u : Fin dY → M)
    (hu : LinearIndependent LL u) (x y : Fin dY → LL) (h : ∑ j, x j • u j = ∑ j, y j • u j) : x = y := by
  funext j
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hu (fun j => x j - y j)
    (by simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]) j)

include W in
theorem int_vec (hV : ValRing (LL := LL) O v) {ι₀ : Type} [Fintype ι₀] (ρ : ι₀ → LL) :
    ∃ (m : ℕ) (r : ι₀ → O), ∀ i, algebraMap O LL (r i) = (PD.p : LL) ^ m * ρ i := by
  choose mm oo hoo using fun i => Formalism.MainNotions.UnusedSlot80.ArcF.exists_pow_mul W hV (ρ i)
  refine ⟨∑ i, mm i, fun i => ((PD.p : ℕ) : O) ^ (∑ j, mm j - mm i) * oo i, fun i => ?_⟩
  have hle : mm i ≤ ∑ j, mm j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [map_mul, hoo, map_pow, map_natCast, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]

theorem letter_pull [FiniteDimensional Qp LL] (hK : Function.Bijective (algebraMap K₀ K))
    (h9 : DcrisExactStrict PD LL) (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L)
    (hses : IsSESLat (Qp := Qp) ι π) (h2 : IsCrys PD T₂.ρ) (hY : IsCrys PD Y.ρ) (τ₀ : K₀ →ₐ[Qp] LL)
    {ξ : T₂.V ⊗[Qp] B} (hξ : ξ ∈ Dcris PD T₂.ρ) (h : crisMap B ι.f ξ ∈ DcrisL PD Y.ρ τ₀) :
    ξ ∈ DcrisL PD T₂.ρ τ₀ := by
  have hinj := (ses_exact PD hK h9 T₂ Y W.one ι π hses h2 hY (Formalism.MainNotions.LiftingTheory.gen_one_crys W)).1
  have hL := (Strict.mem_DcrisL_iff PD τ₀ _).1 h
  rw [Strict.mem_DcrisL_iff]
  refine ⟨hξ, fun c => ?_⟩
  have hm : mulVB (LL := LL) (V := T₂.V) (B := B) c ξ - τ₀ c • ξ ∈ Dcris PD T₂.ρ :=
    (Dcris PD T₂.ρ).sub_mem (mulVB_Dcris PD c hξ) ((Dcris PD T₂.ρ).smul_mem _ hξ)
  exact sub_eq_zero.1 (hinj _ hm (by rw [map_sub, map_smul, Strict.crisMap_mulVB, hL.2 c, sub_self]))

variable [IsDomain O]

theorem pull_vec [FiniteDimensional Qp LL] (hK : Function.Bijective (algebraMap K₀ K))
    (h9 : DcrisExactStrict PD LL) (hV : ValRing (LL := LL) O v) (hinj : Function.Injective (algebraMap O LL))
    (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L)
    (hses : IsSESLat (Qp := Qp) ι π) (h2 : IsCrys PD T₂.ρ) (hY : IsCrys PD Y.ρ) (a : ZMod n) (e : ℕ)
    {d dY : ℕ} (b : Fin d → W.DD T₂) (bY : Fin dY → W.DD Y)
    (hspan2 : Submodule.span LL (Set.range fun k => dv W T₂ e b (Pi.single k 1)) = DcrisL PD T₂.ρ (W.emb a))
    (hindY : LinearIndependent LL fun j => dv W Y e bY (Pi.single j 1))
    (hspanY : Submodule.span LL (Set.range fun j => dv W Y e bY (Pi.single j 1)) = DcrisL PD Y.ρ (W.emb a))
    (o : Fin d → Fin dY → O)
    (ho : ∀ k, crisMap B ι.f (dv W T₂ e b (Pi.single k 1)) =
      ∑ j, algebraMap O LL (o k j) • dv W Y e bY (Pi.single j 1))
    (α : ℕ → ℤ) (cY : Fin dY → O) (hN : ∀ s < e, dvO W Y e bY cY ∈ FilS W Y a s (-(α s)))
    (hpol : ∃ s < e, α s < 0) :
    ∃ (m : ℕ) (r : Fin d → O), (∀ j, ∑ k, r k * o k j = ((PD.p : ℕ) : O) ^ m * cY j) ∧
      ∀ s < e, α s < 0 → dvO W T₂ e b r ∈ FilS W T₂ a s (-(α s)) := by
  have hpull : ∀ s < e, α s < 0 → ∃ ξ ∈ Dcris PD T₂.ρ, ξ ∈ FilS W T₂ a s (-(α s)) ∧
      crisMap B ι.f ξ = dvO W Y e bY cY := by
    intro s hs hneg
    obtain ⟨ν, hν, hνlam⟩ := Submodule.mem_map.1 (hN s hs)
    obtain ⟨μ, hμ, hμν⟩ := fil_pull PD W hK h9 T₂ Y ι π hses h2 hY (-(α s)) (by omega) _ hν
    refine ⟨((φVB PD (LL := LL) (V := T₂.V)) ^ s) μ, φVB_pow_Dcris PD s hμ.1.1, ⟨μ, hμ, rfl⟩, ?_⟩
    rw [crisMap_φVB_pow, hμν]
    exact hνlam
  obtain ⟨s₀, hs₀, hneg₀⟩ := hpol
  obtain ⟨ξ, hξD, -, hξlam⟩ := hpull s₀ hs₀ hneg₀
  have hinjD := (ses_exact PD hK h9 T₂ Y W.one ι π hses h2 hY (Formalism.MainNotions.LiftingTheory.gen_one_crys W)).1
  have hall : ∀ s < e, α s < 0 → ξ ∈ FilS W T₂ a s (-(α s)) := by
    intro s hs hneg
    obtain ⟨ξ', hξ'D, hξ'F, hξ'lam⟩ := hpull s hs hneg
    have h0 : ξ' - ξ = 0 := hinjD _ ((Dcris PD T₂.ρ).sub_mem hξ'D hξD) (by rw [map_sub, hξ'lam, hξlam, sub_self])
    rw [← sub_eq_zero.1 h0]
    exact hξ'F
  have hlamL : dvO W Y e bY cY ∈ DcrisL PD Y.ρ (W.emb a) := by
    rw [← hspanY, dvO_sum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hξL := letter_pull W hK h9 T₂ Y ι π hses h2 hY (W.emb a) hξD (by rw [hξlam]; exact hlamL)
  rw [← hspan2] at hξL
  obtain ⟨ρ, hρ⟩ := (Submodule.mem_span_range_iff_exists_fun LL).1 hξL
  obtain ⟨m, r, hr⟩ := int_vec W hV ρ
  have hdvr : dvO W T₂ e b r = (PD.p : LL) ^ m • ξ := by
    rw [dvO_sum, ← hρ, Finset.smul_sum]
    simp only [hr, mul_smul]
  refine ⟨m, r, fun j => ?_, fun s hs hneg => ?_⟩
  · have h1 : crisMap B ι.f (dvO W T₂ e b r) = ∑ j, (∑ k, algebraMap O LL (r k) * algebraMap O LL (o k j)) •
        dv W Y e bY (Pi.single j 1) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [dvO_sum, map_sum]
      simp only [map_smul, ho, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    have h2' : crisMap B ι.f (dvO W T₂ e b r) = ∑ j, ((PD.p : LL) ^ m * algebraMap O LL (cY j)) •
        dv W Y e bY (Pi.single j 1) := by
      rw [hdvr, map_smul, hξlam, dvO_sum, Finset.smul_sum]
      simp only [smul_smul]
    have := congrFun (coef_eq _ hindY _ _ (h1.symm.trans h2')) j
    apply hinj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_mul, map_pow, map_natCast]
    simpa only [map_mul] using this
  · rw [hdvr]
    exact Submodule.smul_mem _ _ (hall s hs hneg)

theorem o_inj [FiniteDimensional Qp LL] (hK : Function.Bijective (algebraMap K₀ K))
    (h9 : DcrisExactStrict PD LL) (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L)
    (hses : IsSESLat (Qp := Qp) ι π) (h2 : IsCrys PD T₂.ρ) (hY : IsCrys PD Y.ρ) (a : ZMod n) (e : ℕ)
    {d dY : ℕ} (b : Fin d → W.DD T₂) (bY : Fin dY → W.DD Y)
    (hind2 : LinearIndependent LL fun k => dv W T₂ e b (Pi.single k 1))
    (hspan2 : Submodule.span LL (Set.range fun k => dv W T₂ e b (Pi.single k 1)) = DcrisL PD T₂.ρ (W.emb a))
    (hindY : LinearIndependent LL fun j => dv W Y e bY (Pi.single j 1))
    (o : Fin d → Fin dY → O)
    (ho : ∀ k, crisMap B ι.f (dv W T₂ e b (Pi.single k 1)) =
      ∑ j, algebraMap O LL (o k j) • dv W Y e bY (Pi.single j 1))
    (ρ : Fin d → LL) (hρ : ∀ j, ∑ k, ρ k * algebraMap O LL (o k j) = 0) : ρ = 0 := by
  have hinjD := (ses_exact PD hK h9 T₂ Y W.one ι π hses h2 hY (Formalism.MainNotions.LiftingTheory.gen_one_crys W)).1
  set ξ := ∑ k, ρ k • dv W T₂ e b (Pi.single k 1) with hξ
  have hξD : ξ ∈ Dcris PD T₂.ρ := by
    have : ξ ∈ DcrisL PD T₂.ρ (W.emb a) := by
      rw [← hspan2]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    exact ((Strict.mem_DcrisL_iff PD _ ξ).1 this).1
  have h0 : crisMap B ι.f ξ = 0 := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hξ, map_sum]
    simp only [map_smul, ho, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hρ, zero_smul, Finset.sum_const_zero]
  have hξ0 := hinjD ξ hξD h0
  funext k
  exact Fintype.linearIndependent_iff.1 hind2 ρ (by rw [← hξ, hξ0]) k


include W in
theorem right_inv (hV : ValRing (LL := LL) O v) (hinj : Function.Injective (algebraMap O LL)) {d dY : ℕ}
    (o : Fin d → Fin dY → O)
    (hinjo : ∀ ρ : Fin d → LL, (∀ j, ∑ k, ρ k * algebraMap O LL (o k j) = 0) → ρ = 0) :
    ∃ (q : ℕ) (D : Fin dY → Fin d → O), ∀ k m, ∑ j, o k j * D j m =
      if k = m then ((PD.p : ℕ) : O) ^ q else 0 := by
  let oL : Matrix (Fin d) (Fin dY) LL := fun k j => algebraMap O LL (o k j)
  let f : (Fin d → LL) →ₗ[LL] (Fin dY → LL) := Matrix.vecMulLinear oL
  have hf : ∀ ρ j, f ρ j = ∑ k, ρ k * algebraMap O LL (o k j) := fun ρ j => by
    show (Matrix.vecMul ρ oL) j = _
    rfl
  have hker : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot'.2 fun ρ hρ =>
    hinjo ρ fun j => by rw [← hf, hρ]; rfl
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hker
  let Dl : Fin dY → Fin d → LL := fun j m => g (Pi.single j 1) m
  have key : ∀ k m, ∑ j, algebraMap O LL (o k j) * Dl j m = if k = m then 1 else 0 := by
    intro k m
    have hv : f (Pi.single k 1) = ∑ j, algebraMap O LL (o k j) • (Pi.single j 1 : Fin dY → LL) := by
      funext j'
      rw [hf, Finset.sum_apply]
      simp [Pi.single_apply]
    have h1 := congrArg (fun φ : (Fin d → LL) →ₗ[LL] (Fin d → LL) => φ (Pi.single k 1)) hg
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.comp_apply, LinearMap.id_apply, hv, map_sum, map_smul] at h1
    have h2 := congrFun h1 m
    rw [Finset.sum_apply] at h2
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    rw [h2]
    by_cases hkm : k = m
    · subst hkm; simp
    · simp [Ne.symm hkm, hkm]
  obtain ⟨q, D, hD⟩ := int_vec W hV fun x : Fin dY × Fin d => Dl x.1 x.2
  refine ⟨q, fun j m => D (j, m), fun k m => hinj ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_mul, hD]
  have : ∑ j, algebraMap O LL (o k j) * ((PD.p : LL) ^ q * Dl j m) =
      (PD.p : LL) ^ q * ∑ j, algebraMap O LL (o k j) * Dl j m := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, key]
  split_ifs <;> simp

end Formalism.MainNotions.UnusedSlot80.SplitP
end
end

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.SplitP

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.TruncatedSeriesCountingBounds

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

variable [IsDomain O]

theorem intA_inFr {a : ZMod n} {Λ : LetA O n} (hΛ : Λ ∈ W.AΔ) {g : W.EE} (h : IntA W a g) : InFr W a 1 Λ g := by
  obtain ⟨u, hu, rfl⟩ := h
  refine ⟨Λ * u, W.AΔ.mul_mem hΛ hu, ?_⟩
  rw [← map_mul]
  congr 1
  ring

theorem intA_add {a : ZMod n} {g g' : W.EE} (h : IntA W a g) (h' : IntA W a g') : IntA W a (g + g') := by
  obtain ⟨u, hu, rfl⟩ := h
  obtain ⟨u', hu', rfl⟩ := h'
  exact ⟨u + u', W.AΔ.add_mem hu hu', by rw [← map_add (f := _), mul_add]⟩

theorem intA_neg {a : ZMod n} {g : W.EE} (h : IntA W a g) : IntA W a (-g) := by
  obtain ⟨u, hu, rfl⟩ := h
  exact ⟨-u, W.AΔ.neg_mem hu, by rw [← map_neg, mul_neg]⟩

theorem intA_sub {a : ZMod n} {g g' : W.EE} (h : IntA W a g) (h' : IntA W a g') : IntA W a (g - g') := by
  rw [sub_eq_add_neg]; exact intA_add W h (intA_neg W h')

theorem intA_zero {a : ZMod n} : IntA W a 0 := ⟨0, W.AΔ.zero_mem, by simp⟩

theorem intA_mul {a : ZMod n} {g : W.EE} (h : IntA W a g) {c : LetA O n} (hc : c ∈ W.AΔ) :
    IntA W a (algebraMap (LetA O n) W.EE c * g) := by
  obtain ⟨u, hu, rfl⟩ := h
  exact ⟨c * u, W.AΔ.mul_mem hc hu, by rw [← map_mul]; congr 1; ring⟩

theorem intA_omul {a : ZMod n} {g : W.EE} (h : IntA W a g) (o : O) : IntA W a (g * algebraMap O W.EE o) := by
  rw [mul_comm, IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
  exact intA_mul W h (W.AΔ.algebraMap_mem o)

theorem intA_sum {a : ZMod n} {ι₀ : Type} (s : Finset ι₀) (g : ι₀ → W.EE) (h : ∀ i ∈ s, IntA W a (g i)) :
    IntA W a (∑ i ∈ s, g i) := by
  induction s using Finset.induction_on with
  | empty => simpa using intA_zero W
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact intA_add W (h j (Finset.mem_insert_self j s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem intA_lE [NeZero n] {a : ZMod n} {g : W.EE} (h : IntA W a g) (t : ℕ) : IntA W a (lE W t * g) := by
  rw [LevC.lE_eq]; exact intA_mul W h (LevC.lA_mem W t)

theorem intA_of_inFr {a : ZMod n} {N : LetA O n} (hN : N ∈ W.AΔ) {g : W.EE} (h : InFr W a N 1 g) : IntA W a g := by
  obtain ⟨u, hu, hg⟩ := h
  refine ⟨N * u, W.AΔ.mul_mem hN hu, ?_⟩
  rw [map_one, one_mul] at hg
  rw [hg, mul_assoc]

variable [NeZero n]

theorem intA_of_nonpol (hπ : W.π₀ ∈ W.AΔ) {a : ZMod n} {e : ℕ} {α : ℕ → ℤ} {g : W.EE}
    (hα : ∀ s < e, 0 ≤ α s) (h : InId W a e α g) : IntA W a g := by
  have hden : ∏ s ∈ Finset.range e, ps W s ^ (-(α s)).toNat = 1 := by
    refine Finset.prod_eq_one fun s hs => ?_
    have : (-(α s)).toNat = 0 := by have := hα s (Finset.mem_range.1 hs); omega
    rw [this, pow_zero]
  unfold InId at h
  rw [hden] at h
  exact intA_of_inFr W (W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W hπ s) _) h

theorem polar_core [FiniteDimensional Qp LL] (C : LevC.Ctx W) (h9 : DcrisExactStrict PD LL)
    (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts) (e : ℕ) (a : ZMod n)
    (hac : c' + (e : ZMod n) = a)
    (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L)
    (hT₂ : Win W A T₂) (hWY : Win W A Y) (hses : IsSESLat (Qp := Qp) ι π)
    {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T₂ c' b sol)
    {dY : ℕ} (bY : Fin dY → W.DD Y) (solY : Fin dY → ℕ → Fin dY → LL) (hbY : IsHor W Y c' bY solY)
    (hind2 : LinearIndependent LL fun k => dv W T₂ e b (Pi.single k 1))
    (hspan2 : Submodule.span LL (Set.range fun k => dv W T₂ e b (Pi.single k 1)) = DcrisL PD T₂.ρ (W.emb a))
    (hindY : LinearIndependent LL fun j => dv W Y e bY (Pi.single j 1))
    (hspanY : Submodule.span LL (Set.range fun j => dv W Y e bY (Pi.single j 1)) = DcrisL PD Y.ρ (W.emb a))
    (hNY : ∀ x, InFNc W Y a 1 x → ∃ f, InNL W Y a e (abelian₂ W A a e) bY f ∧
      RepVV W Y c' e (A.M PD.p) (abelian₂ W A a e) bY solY (lA W ^ A.σ PD.p • x) f)
    (w : W.DD T₂) (p x : W.DD Y) (hw : InFP W T₂ c' e 1 (abelian₂ W A a e • w)) (hp : p ∈ Pp W Y c' e)
    (hxN : InFNc W Y a 1 x) (hpx : W.map ι w = p - x) :
    ∃ (κ : ℕ) (f : Fin d → W.EE), RepVV W T₂ c' e (A.M PD.p) (abelian₂ W A a e) b sol (lA W ^ κ • w) f ∧
      SecIn W a e (LevC.condPolar (W := W) T₂ a e b) f := by
  have h2 := hT₂.1
  have hY := hWY.1
  set M : ℕ := A.M PD.p with hM
  set σ : ℕ := A.σ PD.p with hσ
  set Λ : LetA O n := abelian₂ W A a e with hΛ
  have hΛm : Λ ∈ W.AΔ := W.AΔ.prod_mem fun s _ => W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.PhiPowers.ps_mem_AΔ W C.hR.1 s) _

  obtain ⟨κ₁, F, hF, hFr⟩ := LevC.secOfP' W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e T₂ h2 b sol hb w
    (by rw [hac]; exact hw)
  rw [hac] at hF hFr

  choose mo hmo hmox hE using fun k => frame_const W C.hR ι h2 hY c' b hb.1 bY hbY.1 k
  set o : Fin d → Fin dY → O := fun k j => PowerSeries.constantCoeff (mo k j c') with ho
  have hFY := repVV_map W C ι h2 hY A hA a c' e b sol hb bY solY hbY o hE hF
  rw [Formalism.MainNotions.UnusedSlot80.Relay2.mapA_smul] at hFY
  have hdv : ∀ k, crisMap B ι.f (dv W T₂ e b (Pi.single k 1)) =
      ∑ j, algebraMap O LL (o k j) • dv W Y e bY (Pi.single j 1) := fun k =>
    dv_map W ι h2 hY c' e b hb.1 bY hbY.1 k (mo k) (hmox k)

  obtain ⟨κp, G, hG, hGint⟩ := secOfP_int W C.hinj C.hO2 C.hR C.hTr C.hH C.hCA C.h5p A hA c' e Y hY bY solY hbY p
    ⟨p, hp, (one_smul _ _).symm⟩
  rw [hac] at hG hGint
  obtain ⟨fx, ⟨hfxr, κx, hSx⟩, hRx⟩ := hNY x hxN

  have R1 := LevC.repVV_lA Y c' e M Λ bY solY (W.map ι w) _ (κp + σ) κ₁ hFY
  have R2 := LevC.repVV_lA Y c' e M Λ bY solY p G (κ₁ + σ) κp hG
  have R3 := LevC.repVV_lA Y c' e M Λ bY solY x fx (κ₁ + κp) σ hRx
  rw [show κp + (κ₁ + σ) = κ₁ + (κp + σ) by omega] at R2
  rw [show σ + (κ₁ + κp) = κ₁ + (κp + σ) by omega] at R3
  have R23 := LevC.repVV_sub W C.hinj Y c' e M Λ bY solY _ _ _ _ R2 R3
  rw [← smul_sub, ← hpx] at R23
  have hfr1 : ∀ j, InFr W a 1 Λ (lE W (κp + σ) * ∑ k, F k * algebraMap O W.EE (o k j)) := fun j =>
    Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (LevC.inFr_sum W _ _ fun k _ => by
      rw [mul_comm, IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
      exact LevC.inFr_mulA W (hFr k) (W.AΔ.algebraMap_mem _)) _
  have hfr23 : ∀ j, InFr W a 1 Λ (lE W (κ₁ + σ) * G j - lE W (κ₁ + κp) * fx j) := fun j =>
    LevC.inFr_sub W (Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (intA_inFr W hΛm (hGint j)) _)
      (Formalism.MainNotions.UnusedSlot80.ArcF.inFr_lE W (hfxr j) _)
  obtain ⟨t, ht⟩ := LevC.sec_unique W C.hinj C.hV C.hO2 C.hs C.hR C.hp0 C.h5 C.hTr C.hH C.hCA C.h5p Y
    (C.h3 Y hY) (C.hmod Y hY) A hA c' hc' hWY bY solY hbY e _ _ _ (by rw [hac]; exact R1) (by rw [hac]; exact R23)
    (by rw [hac]; exact hfr1) (by rw [hac]; exact hfr23)
  rw [hac] at ht
  choose u hu hue using ht
  simp only [map_one, one_mul, Pi.sub_apply] at hue
  set ε : Fin dY → W.EE := fun j => algebraMap (LetA O n) W.EE (letE a * (W.π₀ * Λ) * u j) with hεdef
  have hε : ∀ j, IntA W a (ε j) := fun j =>
    ⟨W.π₀ * Λ * u j, W.AΔ.mul_mem (W.AΔ.mul_mem C.hR.1 hΛm) (hu j), by
      show algebraMap (LetA O n) W.EE (letE a * (W.π₀ * Λ) * u j) = _
      congr 1
      ring⟩
  obtain ⟨I, g, cc, α, hgα, hfx⟩ := hSx

  have hpv : ∀ i, ∃ (m : ℕ) (r : Fin d → O), (∃ s < e, α i s < 0) →
      (∀ j, ∑ k, r k * o k j = ((PD.p : ℕ) : O) ^ m * cc i j) ∧
        ∀ s < e, α i s < 0 → dvO W T₂ e b r ∈ FilS W T₂ a s (-(α i s)) := by
    intro i
    by_cases hi : ∃ s < e, α i s < 0
    · obtain ⟨m, r, h⟩ := pull_vec W C.hbij h9 C.hV C.hinj T₂ Y ι π hses h2 hY a e b bY hspan2 hindY hspanY o hdv
        (α i) (cc i) (hgα i).2 hi
      exact ⟨m, r, fun _ => h⟩
    · exact ⟨0, 0, fun h => absurd h hi⟩
  choose mi ri hri using hpv
  set M0 : ℕ := ∑ i, mi i with hM0
  set r' : Fin I → Fin d → O := fun i k => ((PD.p : ℕ) : O) ^ (M0 - mi i) * ri i k with hr'def
  set pol : Fin I → Prop := fun i => ∃ s < e, α i s < 0 with hpol
  have hr'1 : ∀ i, pol i → ∀ j, ∑ k, r' i k * o k j = ((PD.p : ℕ) : O) ^ M0 * cc i j := by
    intro i hi j
    have hle : mi i ≤ M0 := Finset.single_le_sum (fun j _ => Nat.zero_le (mi j)) (Finset.mem_univ i)
    have h1 := (hri i hi).1 j
    calc ∑ k, r' i k * o k j = ((PD.p : ℕ) : O) ^ (M0 - mi i) * ∑ k, ri i k * o k j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by simp only [hr'def]; ring
      _ = ((PD.p : ℕ) : O) ^ M0 * cc i j := by
          rw [h1, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  have hr'2 : ∀ i, pol i → ∀ s < e, α i s < 0 → dvO W T₂ e b (r' i) ∈ FilS W T₂ a s (-(α i s)) := by
    intro i hi s hs hneg
    rw [show r' i = fun k => ((PD.p : ℕ) : O) ^ (M0 - mi i) * ri i k from rfl, dvO_smul]
    exact Submodule.smul_mem _ _ ((hri i hi).2 s hs hneg)

  set Spol : Fin dY → W.EE := fun j => ∑ i, if pol i then g i * algebraMap O W.EE (cc i j) else 0 with hSpol
  set Snp : Fin dY → W.EE := fun j => ∑ i, if pol i then 0 else g i * algebraMap O W.EE (cc i j) with hSnpdef
  have hsplit : ∀ j, lE W κx * fx j = Spol j + Snp j := fun j => by
    have hfxj : lE W κx * fx j = ∑ i, g i * algebraMap O W.EE (cc i j) := hfx j
    rw [hfxj, hSpol, hSnpdef, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  have hSnp : ∀ j, IntA W a (Snp j) := fun j => intA_sum W _ _ fun i _ => by
    by_cases hi : pol i
    · rw [if_pos hi]; exact intA_zero W
    · rw [if_neg hi]
      refine intA_omul W (intA_of_nonpol W C.hR.1 (fun s hs => ?_) (hgα i).1) _
      by_contra hlt
      exact hi ⟨s, hs, not_le.mp hlt⟩
  set Pv : Fin d → W.EE := fun k => ∑ i, if pol i then g i * algebraMap O W.EE (r' i k) else 0 with hPvdef
  have hPv : ∀ j, ∑ k, Pv k * algebraMap O W.EE (o k j) = lE W M0 * Spol j := fun j => by
    simp only [hPvdef, hSpol, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : pol i
    · simp only [if_pos hi]
      have h3 : ∑ k, g i * algebraMap O W.EE (r' i k) * algebraMap O W.EE (o k j) =
          g i * algebraMap O W.EE (∑ k, r' i k * o k j) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by simp only [map_mul]; ring
      rw [h3, hr'1 i hi j]
      simp only [map_mul, map_pow, map_natCast]
      unfold lE
      ring
    · simp only [if_neg hi, zero_mul, Finset.sum_const_zero, mul_zero]
  set Mt : ℕ := M0 + κx + t + κp + σ with hMt
  set Z : Fin d → W.EE := fun k => lE W Mt * F k + lE W (t + κ₁ + κp) * Pv k with hZdef
  set R : Fin dY → W.EE := fun j => lE W M0 * (lE W (κx + t + κ₁ + σ) * G j + lE W κx * ε j -
    lE W (t + κ₁ + κp) * Snp j) with hRdef
  have hZR : ∀ j, ∑ k, Z k * algebraMap O W.EE (o k j) = R j := fun j => by
    have e1 : ∑ k, Z k * algebraMap O W.EE (o k j) = lE W Mt * ∑ k, F k * algebraMap O W.EE (o k j) +
        lE W (t + κ₁ + κp) * ∑ k, Pv k * algebraMap O W.EE (o k j) := by
      simp only [hZdef, add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    rw [e1, hPv j]
    have h1 := hue j
    have h2 := hsplit j
    simp only [hRdef, hMt, lE] at h1 h2 ⊢
    linear_combination (((PD.p : ℕ) : W.EE) ^ (M0 + κx)) * h1 - (((PD.p : ℕ) : W.EE) ^ (M0 + t + κ₁ + κp)) * h2

  obtain ⟨q, D, hD⟩ := right_inv W C.hV C.hinj o
    (o_inj W C.hbij h9 T₂ Y ι π hses h2 hY a e b bY hind2 hspan2 hindY o hdv)
  have hZq : ∀ m, lE W q * Z m = ∑ j, R j * algebraMap O W.EE (D j m) := fun m => by
    have e2 : ∑ j, R j * algebraMap O W.EE (D j m) = ∑ k, Z k * algebraMap O W.EE (∑ j, o k j * D j m) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [← hZR, Finset.sum_mul, map_sum, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by simp only [map_mul]; ring
    rw [e2]
    simp only [hD, apply_ite (algebraMap O W.EE), map_zero, mul_ite, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, map_pow, map_natCast]
    unfold lE
    ring
  have hInt : ∀ m, IntA W a (∑ j, R j * algebraMap O W.EE (D j m)) := fun m =>
    intA_sum W _ _ fun j _ => intA_omul W (intA_lE W (intA_sub W (intA_add W (intA_lE W (hGint j) _)
      (intA_lE W (hε j) _)) (intA_lE W (hSnp j) _)) _) _
  set cp : Fin I → Fin d → O := fun i k =>
    if pol i then -(((PD.p : ℕ) : O) ^ (q + (t + κ₁ + κp)) * r' i k) else 0 with hcpdef
  have hfin : ∀ m, lE W (q + Mt) * F m =
      (∑ j, R j * algebraMap O W.EE (D j m)) + ∑ i, g i * algebraMap O W.EE (cp i m) := fun m => by
    rw [← hZq m]
    have e3 : ∑ i, g i * algebraMap O W.EE (cp i m) = -(lE W (q + (t + κ₁ + κp)) * Pv m) := by
      rw [hPvdef, Finset.mul_sum, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : pol i
      · simp only [hcpdef, if_pos hi, map_neg, map_mul, map_pow, map_natCast]
        unfold lE
        ring
      · simp only [hcpdef, if_neg hi, map_zero, mul_zero, neg_zero]
    rw [e3, hZdef]
    simp only [hMt]
    unfold lE
    ring
  refine ⟨κ₁ + (q + Mt), fun m => lE W (q + Mt) * F m, LevC.repVV_lA T₂ c' e M Λ b sol w F (q + Mt) κ₁ hF, ?_⟩
  have hS1 : SecIn W a e (LevC.condPolar (W := W) T₂ a e b)
      (fun m => ∑ j, R j * algebraMap O W.EE (D j m)) := by
    refine ⟨d, fun m₀ => ∑ j, R j * algebraMap O W.EE (D j m₀), fun m₀ => Pi.single m₀ 1, fun _ _ => 0,
      fun m₀ => ⟨?_, fun s _ => Or.inl le_rfl⟩, fun k => ?_⟩
    · obtain ⟨uu, huu, hug⟩ := hInt m₀
      show InFr W a (∏ s ∈ Finset.range e, ps W s ^ ((0 : ℤ)).toNat)
        (∏ s ∈ Finset.range e, ps W s ^ (-(0 : ℤ)).toNat) _
      simp only [neg_zero, Int.toNat_zero, pow_zero, Finset.prod_const_one]
      exact ⟨uu, huu, by rw [map_one, one_mul, hug, mul_one]⟩
    · simp [Pi.single_apply]
  have hS2 : SecIn W a e (LevC.condPolar (W := W) T₂ a e b)
      (fun m => ∑ i, g i * algebraMap O W.EE (cp i m)) := by
    refine ⟨I, g, cp, α, fun i => ⟨(hgα i).1, fun s hs => ?_⟩, fun k => rfl⟩
    by_cases hneg : α i s < 0
    · right
      have hi : pol i := ⟨s, hs, hneg⟩
      have e4 : cp i = fun k => (-((PD.p : ℕ) : O) ^ (q + (t + κ₁ + κp))) * r' i k := by
        funext k; simp only [hcpdef, if_pos hi]; ring
      rw [e4, dvO_smul]
      exact Submodule.smul_mem _ _ (hr'2 i hi s hs hneg)
    · left
      exact not_lt.mp hneg
  have hS := LevC.secIn_add W hS1 hS2
  convert hS using 1
  funext m
  rw [Pi.add_apply]
  exact hfin m

end Formalism.MainNotions.UnusedSlot80.SplitP
end
end

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.SplitP

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.TruncatedSeriesCountingBounds

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

variable [IsDomain O] [NeZero n]

theorem splitPolar_of [FiniteDimensional Qp LL] (C : LevC.Ctx W) (hArc : ArcCore W)
    (hJ : Formalism.MainNotions.LiftingTheory.coreJumps PD LL O) (h9 : DcrisExactStrict PD LL) : Split.SplitPolar W := by
  intro _ _ A hA T₂ Y ι π hT₂ hY hses c hc w hI hP hpx d b sol hb
  obtain ⟨p, hp, x, hx, hpx⟩ := hpx
  have hac : c - ((A.len c : ℕ) : ZMod n) + ((A.len c : ℕ) : ZMod n) = c := sub_add_cancel _ _
  have hc' : c - ((A.len c : ℕ) : ZMod n) ∈ A.cuts := ((hA.2.2.1 c hc).2.2).1
  have hje : A.j ≤ A.len c := hA.2.2.2.1 c hc
  have hWY : Win W A Y := Formalism.MainNotions.UnusedSlot80.Split2.win_ext W A hJ (Formalism.MainNotions.LiftingTheory.lone_HOne0 W) hT₂ hY hses
  obtain ⟨dY, bY, hbYf⟩ := Formalism.MainNotions.UnusedSlot80.Relay2.frame_exists W Y (c - ((A.len c : ℕ) : ZMod n)) (C.hmod Y hY)
  obtain ⟨solY, hbY⟩ := Formalism.MainNotions.UnusedSlot80.UnivF.hor_exists W C.hH C.hCA Y hY _ bY hbYf
  obtain ⟨-, hAC⟩ := hArc C.hCA C.h5p A hA c hc (A.len c) hje le_rfl
  obtain ⟨-, -, -, h2f⟩ := hAC T₂ hT₂
  obtain ⟨⟨hind2, hspan2⟩, -⟩ := h2f d b sol hb
  obtain ⟨-, -, -, hYf⟩ := hAC Y hWY
  obtain ⟨⟨hindY, hspanY⟩, -, -, hNY, -⟩ := hYf dY bY solY hbY
  rw [hac] at hspan2 hspanY hNY
  have hxe : x = p - W.map ι w := by rw [hpx]; abel
  have hxN : InFNc W Y c 1 x := by
    refine ⟨x, ⟨Formalism.MainNotions.UnusedSlot80.Split2.N_of_Nl W hx, fun δ hδ => ?_⟩,
      Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W Y c hx, (one_smul _ _).symm⟩
    rw [hxe, map_sub, Formalism.MainNotions.UnusedSlot80.Relay2.Pp_Δ W Y _ _ p hp δ hδ, ← W.map_γ, hI.2.1 δ hδ]
  exact polar_core W C h9 A hA _ hc' (A.len c) c hac T₂ Y ι π hT₂ hWY hses b sol hb bY solY hbY hind2 hspan2
    hindY hspanY hNY w p x hP hp hxN hpx

end Formalism.MainNotions.UnusedSlot80.SplitP

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

theorem splitPolarL_of (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hAdm : AdmArcA D HW F Cm) (hArc : ArcCoordinatesTheorem D HW F Cm) (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F)
    (h9 : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D) : Split.SplitPolarL D HW := by
  intro l _ K LL hG hCA h5l
  have := neZero_finrank_max_unramified K
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have C := ctx_of D HW F Cm hAdm l K LL hG hCA h5l
  exact SplitP.splitPolar_of _ C ((hArc hAdm) l K LL hG hCA h5l).1 (h23 l K LL) (h9 l K LL)

end Formalism.MainNotions.UnusedSlot80
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.ArcCoordinatesAdmittedOfLevels
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem arc_coordinates_of_levels (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : LevelZeroModPLocal D HW) (h2 : LevelZeroModPRefinedLocal D HW) : ArcCoordinatesTheorem D HW F Cm :=
  arc_coordinates_of_level_zero_parts D HW F Cm h1 h2

end Formalism.MainNotions.UnusedSlot80
end
end

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

theorem splitShapeL_rec (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hArc : AdmArcA D HW F Cm) (h1 : LevelZeroModPLocal D HW) (h2 : LevelZeroModPRefinedLocal D HW) (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F)
    (h9 : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D) : Split.SplitShapeL D HW :=
  Split.splitShapeL_of_pieces D HW (splitPolarL_of D HW F Cm hArc (arc_coordinates_of_levels D HW F Cm h1 h2) h23 h9)
    (Split.polarToPoleL_of D HW F Cm hArc)

end Formalism.MainNotions.UnusedSlot80
end
end

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.SplittingOfLiteratureExactness
noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem ddExactL_of_litFont (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (h : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F) : Split.DDExactL D HW := by
  intro l _ K LL hG hCA _ T₂ Y ι π _ _ hses
  obtain ⟨hinj, -, hker⟩ := (h l K LL hCA).2.1 T₂ Y _ ι π hses
  refine ⟨fun x => (hker _).2 ⟨x, rfl⟩, fun x hx => hinj (by rw [hx, map_zero]), fun u hu => (hker u).1 hu⟩

theorem splitting_of_literature_exactness (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (hA : AdmSplitA D HW F Cm) (h6 : Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F) (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F)
    (hTr : Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F) (hWX : Formalism.MainNotions.LiftingTheory.WachKillsQuotients D HW F) (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F)
    (hS : Split.SplitShapeL D HW) : SplittingArcLifting D HW F Cm :=
  splitting_general_of_exactness D HW F Cm hA h6 hH hTr hWX (ddExactL_of_litFont D HW F hFont) hS

end Formalism.MainNotions.UnusedSlot80
end
end

noncomputable section

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

theorem arc_coordinates_of_frobenius (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (h2 : LevelZeroModPRefinedLocal D HW) : ArcCoordinatesTheorem D HW F Cm := fun hA =>
  arc_coordinates_of_levels D HW F Cm (lev0MpL_of D HW F Cm hA h4 h9) h2 hA

theorem arc_coordinates_of_frobenius_levels (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hA : AdmArcA D HW F Cm) (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F) (h2 : LevelZeroModPRefinedLocal D HW) : ArcLiftingCoordinates D HW F Cm :=
  arc_coordinates_of_frobenius D HW F Cm h4 h9 h2 hA

theorem split_case_A_of_hypotheses (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (hA : AdmSplitA D HW F Cm) (hArc : AdmArcA D HW F Cm)
    (h4 : Formalism.MainNotions.DeltaInvariantLattices.P4 D HW F Cm) (h6 : Formalism.MainNotions.DeltaInvariantLattices.P6 D HW F) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9 D HW F)
    (hH : Formalism.MainNotions.LiftingTheory.ConclusionH D HW F) (hTr : Formalism.MainNotions.LiftingTheory.ExistsUnitClasses D HW F) (hWX : Formalism.MainNotions.LiftingTheory.WachKillsQuotients D HW F)
    (hFont : Formalism.MainNotions.InvariantsGenerators.LitFont D HW F) (h23 : Formalism.MainNotions.LiftingTheory.adm23 D HW F) (h17 : Formalism.MainNotions.TruncatedSeriesCountingBounds.adm9 D)
    (h2 : LevelZeroModPRefinedLocal D HW) : SplittingArcLifting D HW F Cm :=
  splitting_of_literature_exactness D HW F Cm hA h6 hH hTr hWX hFont
    (splitShapeL_rec D HW F Cm hArc (lev0MpL_of D HW F Cm hArc h4 h9) h2 h23 h17)

end Formalism.MainNotions.UnusedSlot80
