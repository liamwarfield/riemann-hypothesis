module

public import Formalism.SharpRestriction.LevelLetterCocycles.IndepStep
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalizationQuotientSeparatedDvd

@[expose] public section

section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.SecInTransport
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.TmulMemFilV
section -- merged from Formalism.SharpRestriction.LevelLetterCocycles.FrameInvPoly
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

theorem indep (hinj : Function.Injective (algebraMap O LL)) (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing (LL := LL) O v)
    (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    (h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
      Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (T : LocLat G Qp LL O) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts) (hT : Win W A T) {d : ℕ}
    (b : Fin d → W.DD T) (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e : ℕ) (c : Fin d → LetA O n)
    (hc : ∀ m, c m ∈ W.AΔ) (hcl : ∀ m, letE (c' + (e : ZMod n)) * c m = c m)
    (h0 : ∑ m, c m • ((W.φD T) ^ e) (b m) = 0) : ∀ m, c m = 0 := by
  obtain ⟨h3r, -⟩ := Formalism.MainNotions.UnusedSlot80.SatW.ring_clauses W hR
  have hπU := Formalism.MainNotions.UnusedSlot80.SatW.isUnit_EE_of_UPi W (Formalism.MainNotions.UnusedSlot80.SatW.UPi_π₀ W h3r)
  have key : ∀ k : ℕ, ∀ c : Fin d → LetA O n, (∀ m, c m ∈ W.AΔ) →
      (∀ m, letE (c' + (e : ZMod n)) * c m = c m) → ∑ m, c m • ((W.φD T) ^ e) (b m) = 0 →
      ∀ m, ∃ c₁ : LetA O n, c m = W.π₀ ^ k * c₁ := by
    intro k
    induction k with
    | zero => intro c _ _ _ m; exact ⟨c m, by simp⟩
    | succ k ih =>
      intro c hc hcl h0 m
      choose c₁ hc₁ hc₁l hcm using indep_step W hinj hV hs hR hp0 h5 T h3 hmod A hA c' hc' hT b hb e c hc hcl h0
      have h0' : ∑ m, c₁ m • ((W.φD T) ^ e) (b m) = 0 := by
        refine Formalism.MainNotions.UnusedSlot80.SatW.smul_cancel W T hπU ?_
        rw [smul_zero, Finset.smul_sum, ← h0]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [smul_smul, ← hcm m]
      obtain ⟨c₂, hc₂⟩ := ih c₁ hc₁ hc₁l h0' m
      exact ⟨c₂, by rw [hcm m, hc₂, pow_succ]; ring⟩
  intro m
  obtain ⟨w, -, hw⟩ := Formalism.MainNotions.UnusedSlot80.ToolsR.π₀_comp hR
  funext i
  refine PowerSeries.ext fun j => ?_
  obtain ⟨c₁, hc₁⟩ := key (j + 1) c hc hcl h0 m
  have hl : 2 ≤ PD.p := PD.hp.two_le
  have hdvd : (PowerSeries.X : PowerSeries O) ^ ((PD.p - 1) * (j + 1)) ∣ c m i := by
    rw [hc₁, Pi.mul_apply, Pi.pow_apply, show W.π₀ i = W.π₀₁ from rfl, hw, mul_pow, ← pow_mul]
    exact ⟨w ^ (j + 1) * c₁ i, by ring⟩
  rw [PowerSeries.X_pow_dvd_iff.1 hdvd j (by nlinarith [Nat.sub_add_cancel (by omega : 1 ≤ PD.p)])]
  simp


omit [NeZero n] in
theorem frame_inv_poly' (hinj : Function.Injective (algebraMap O LL)) {d : ℕ}
    (sol : Fin d → ℕ → Fin d → LL) (hsol0 : ∀ k, sol k 0 = Pi.single k 1) (M κ : ℕ)
    (yy : Fin d → ℕ → Fin d → O) (hyy : ∀ k, ∀ r < M, ∀ m, algebraMap O LL (yy k r m) = (PD.p : LL) ^ κ * sol k r m)
    (zz : ℕ → Fin d → Fin d → O)
    (hzz : ∀ r < M, ∀ k m, algebraMap O LL (zz r k m) = (PD.p : LL) ^ κ *
      PowerSeries.coeff r ((Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' :
        Matrix (Fin d) (Fin d) (PowerSeries LL))⁻¹ k m))
    {R : Type} [CommRing R] [Algebra O R] (Y : R) (k k' : Fin d) :
    ∃ ρ : Polynomial O, ∑ m, (∑ r ∈ Finset.range M, algebraMap O R (zz r k m) * Y ^ r) *
        (∑ r ∈ Finset.range M, algebraMap O R (yy k' r m) * Y ^ r) =
      algebraMap O R (((PD.p : ℕ) : O) ^ (2 * κ) * if k = k' then 1 else 0) + Y ^ M * Polynomial.aeval Y ρ := by
  set Hps : Matrix (Fin d) (Fin d) (PowerSeries LL) :=
    Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' with hHps
  have hdet : IsUnit Hps.det := by
    rw [PowerSeries.isUnit_iff_constantCoeff, RingHom.map_det]
    have h1 : (PowerSeries.constantCoeff : PowerSeries LL →+* LL).mapMatrix Hps = 1 := by
      ext i k
      simp only [RingHom.mapMatrix_apply, Matrix.map_apply, hHps, Matrix.of_apply,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_mk, hsol0,
        Matrix.one_apply, Pi.single_apply]
    rw [h1, Matrix.det_one]
    exact isUnit_one
  have hinv : Hps⁻¹ * Hps = 1 := Matrix.nonsing_inv_mul Hps hdet
  have hcoef : ∀ t, ∑ m, ∑ x ∈ Finset.HasAntidiagonal.antidiagonal t,
      PowerSeries.coeff x.1 (Hps⁻¹ k m) * sol k' x.2 m = if t = 0 ∧ k = k' then 1 else 0 := by
    intro t
    have h := congrArg (fun Q : Matrix (Fin d) (Fin d) (PowerSeries LL) => PowerSeries.coeff t (Q k k')) hinv
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mul_apply, map_sum, PowerSeries.coeff_mul, hHps, Matrix.of_apply,
      PowerSeries.coeff_mk] at h
    rw [h, Matrix.one_apply]
    by_cases hm : k = k'
    · by_cases ht : t = 0
      · subst ht; simp [hm]
      · simp [hm, ht, PowerSeries.coeff_one]
    · simp [hm]
  let GP : Fin d → Polynomial O := fun m =>
    ∑ r ∈ Finset.range M, Polynomial.C (zz r k m) * Polynomial.X ^ r
  let HP : Fin d → Polynomial O := fun m =>
    ∑ r ∈ Finset.range M, Polynomial.C (yy k' r m) * Polynomial.X ^ r
  have hGPc : ∀ m i, (GP m).coeff i = if i < M then zz i k m else 0 := by
    intro m i
    simp only [GP, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range]
  have hHPc : ∀ m i, (HP m).coeff i = if i < M then yy k' i m else 0 := by
    intro m i
    simp only [HP, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_range]
  set cst : O := ((PD.p : ℕ) : O) ^ (2 * κ) * if k = k' then 1 else 0 with hcst
  set Q : Polynomial O := ∑ m, GP m * HP m - Polynomial.C cst with hQdef
  have hQ : ∀ t < M, Q.coeff t = 0 := by
    intro t ht
    apply hinj
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, hQdef, Polynomial.coeff_sub, Polynomial.finsetSum_coeff, Polynomial.coeff_C, map_sub,
      map_sum]
    have hk : ∀ m, algebraMap O LL ((GP m * HP m).coeff t) = (PD.p : LL) ^ (2 * κ) *
        ∑ x ∈ Finset.HasAntidiagonal.antidiagonal t, PowerSeries.coeff x.1 (Hps⁻¹ k m) * sol k' x.2 m := by
      intro m
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Polynomial.coeff_mul, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx' := Finset.HasAntidiagonal.mem_antidiagonal.1 hx
      rw [hGPc, hHPc, if_pos (by omega), if_pos (by omega), map_mul, hzz x.1 (by omega),
        hyy k' x.2 (by omega)]
      ring
    rw [Finset.sum_congr rfl fun m _ => hk m, ← Finset.mul_sum, hcoef t, hcst]
    by_cases ht0 : t = 0
    · subst ht0
      by_cases hm : k = k' <;> simp [hm]
    · simp [ht0]
  obtain ⟨ρ, hρ⟩ := (Polynomial.X_pow_dvd_iff).2 hQ
  refine ⟨ρ, ?_⟩
  have h := congrArg (Polynomial.aeval Y) hρ
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hQdef, map_sub, map_sum, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, GP, HP,
    Polynomial.aeval_X] at h
  rw [← h]
  ring

theorem sec_unique (hinj : Function.Injective (algebraMap O LL)) (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing (LL := LL) O v)
    (hO2 : ∀ x : LL, 0 ≤ v x → ∃ o : O, algebraMap O LL o = x)
    (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) (hp0 : ((PD.p : ℕ) : O) ≠ 0)
    (h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
      Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (hTr : Formalism.MainNotions.LiftingTheory.coreTr W) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5p : 5 ≤ PD.p)
    (T : LocLat G Qp LL O) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts) (hT : Win W A T) {d : ℕ}
    (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL) (hb : IsHor W T c' b sol) (e : ℕ)
    (x : W.DD T) (f g : Fin d → W.EE)
    (hf : RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol x f)
    (hg : RepVV W T c' e (A.M PD.p) (abelian₂ W A (c' + (e : ZMod n)) e) b sol x g)
    (hfr : ∀ k, InFr W (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) (f k))
    (hgr : ∀ k, InFr W (c' + (e : ZMod n)) 1 (abelian₂ W A (c' + (e : ZMod n)) e) (g k)) :
    ∃ t : ℕ, ∀ k, InFr W (c' + (e : ZMod n)) (W.π₀ * abelian₂ W A (c' + (e : ZMod n)) e) 1
      (lE W t * (f k - g k)) := by
  have hl : 2 ≤ PD.p := PD.hp.two_le
  set a : ZMod n := c' + (e : ZMod n) with hadef
  set Λ : LetA O n := abelian₂ W A a e with hΛdef
  set M : ℕ := A.M PD.p with hMdef
  obtain ⟨U, hU⟩ := lam_unit W hR A a e
  have hΛc : ∀ y z : W.EE, algebraMap (LetA O n) W.EE Λ * y = algebraMap (LetA O n) W.EE Λ * z → y = z :=
    fun y z h => by
      have hU' : (U : W.EE) = algebraMap (LetA O n) W.EE Λ := hU
      rw [← hU'] at h
      have := congrArg (fun w => ((U⁻¹ : W.EEˣ) : W.EE) * w) h
      simpa only [← mul_assoc, Units.inv_mul, one_mul] using this
  have h0 := repVV_sub W hinj T c' e M Λ b sol x x f g hf hg
  rw [sub_self, repVV_iff] at h0
  obtain ⟨κ, Hh, hHh, hRV⟩ := h0
  set K : ℕ := κ + Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M with hKdef
  have hRV' := rv_up W T c' e Λ κ (Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M) Hh 0 (f - g) hRV
  obtain ⟨κ', aa, haa, hP⟩ := hRV'
  choose yy hyy hHe using fun k => horTr_scale W T b sol M κ (Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M) k (hHh k)

  choose uf huf hfu using hfr
  choose ug hug hgu using hgr
  have haa_eq : ∀ k, aa k = letE a * (uf k - ug k) := by
    intro k
    apply W.EE_inj
    rw [← (haa k).2, Pi.sub_apply, mul_sub, hfu k, hgu k, ← map_sub]
    congr 1; ring
  have haal : ∀ k, letE a * aa k = aa k := by
    intro k; rw [haa_eq k, ← mul_assoc, letE_mul_self]

  simp only [smul_zero, zero_sub, smul_neg] at hP
  obtain ⟨p, hp, hpe⟩ := hP
  obtain ⟨δ, hδ, hpδ⟩ := Formalism.MainNotions.UnusedSlot80.ArcF.Pp_repr W T c' e b hb.1 p hp
  set Y : LetA O n := (W.φA ^ e) W.π₀ with hYdef
  have hY : Y ∈ W.AΔ := φA_pow_mem_AΔ W hR.1 e
  let HY : Fin d → Fin d → LetA O n := fun m k =>
    ∑ r ∈ Finset.range M, algebraMap O (LetA O n) (yy k r m) * Y ^ r
  have hφH : ∀ k, ((W.φD T) ^ e) (lA W ^ Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M • Hh k) =
      ∑ m, HY m k • ((W.φD T) ^ e) (b m) := by
    intro k
    rw [hHe k, Formalism.MainNotions.UnusedSlot80.ArcF.phi_trunc]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    simp only [HY, ← hYdef]
    exact Finset.sum_congr rfl fun r _ => mul_comm _ _

  let E : Fin d → LetA O n := fun m => lA W ^ κ' * ∑ k, aa k * HY m k
  have hrel : ∑ m, (letE a * (E m + W.π₀ * Λ ^ 2 * δ m)) • ((W.φD T) ^ e) (b m) = 0 := by
    have h1 : lA W ^ κ' • ∑ k, aa k • ((W.φD T) ^ e) (lA W ^ Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p M • Hh k) =
        ∑ m, E m • ((W.φD T) ^ e) (b m) := by
      simp only [hφH, Finset.smul_sum, smul_smul, E]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.mul_sum, Finset.sum_smul]
    have h2 : ∑ m, (E m + W.π₀ * Λ ^ 2 * δ m) • ((W.φD T) ^ e) (b m) = 0 := by
      rw [show ∑ m, (E m + W.π₀ * Λ ^ 2 * δ m) • ((W.φD T) ^ e) (b m) =
          (∑ m, E m • ((W.φD T) ^ e) (b m)) + (W.π₀ * Λ ^ 2) • p by
        simp only [add_smul, Finset.sum_add_distrib, hpδ, Finset.smul_sum, mul_smul], ← h1, ← hpe,
        add_neg_cancel]
    simp only [mul_smul]
    rw [← Finset.smul_sum, h2, smul_zero]
  have hEl : ∀ m, letE a * E m = E m := by
    intro m
    simp only [E, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← haal k]; ring_nf; rw [sq, letE_mul_self]
  have hind := indep W hinj hV hs hR hp0 h5 T h3 hmod A hA c' hc' hT b hb.1 e _
    (fun m => W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a)
      (W.AΔ.add_mem (W.AΔ.mul_mem (lA_mem W κ') (W.AΔ.sum_mem fun k _ => W.AΔ.mul_mem (haa k).1
        (W.AΔ.sum_mem fun r _ => W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (W.AΔ.pow_mem hY r))))
        (W.AΔ.mul_mem (W.AΔ.mul_mem hR.1 (W.AΔ.pow_mem (Formalism.MainNotions.UnusedSlot80.ArcC.lam_mem_AΔ W hR.1 A a e) 2)) (hδ m))))
    (fun m => by rw [← mul_assoc, letE_mul_self]) hrel
  have hEm : ∀ m, E m = -(W.π₀ * Λ ^ 2 * (letE a * δ m)) := by
    intro m
    have := hind m
    rw [mul_add, hEl m] at this
    linear_combination this

  have hHc := hH hCA T hT.1 c'
  have hH5 := hHc.2.2.2.2 d b hb.1 sol hb.2
  have h4 := hHc.2.2.2.1
  choose g' hg' using fun r k m => Formalism.MainNotions.UnusedSlot80.Relay2.int_of_bd W hO2 r (h4 r) _ (hH5.2 k m r)
  let zz : ℕ → Fin d → Fin d → O := fun r k m =>
    ((PD.p : ℕ) : O) ^ (K - Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r) * g' r k m
  have hzz : ∀ r < M, ∀ k m, algebraMap O LL (zz r k m) = (PD.p : LL) ^ K *
      PowerSeries.coeff r ((Matrix.of fun m' k' => PowerSeries.mk fun r' => sol k' r' m' :
        Matrix (Fin d) (Fin d) (PowerSeries LL))⁻¹ k m) := by
    intro r hr k m
    have hle : Formalism.MainNotions.UnusedSlot80.Relay2.Ex PD.p r ≤ K :=
      (Formalism.MainNotions.UnusedSlot80.Relay2.Ex_mono PD.p hl hr.le).trans (Nat.le_add_left _ _)
    simp only [zz, map_mul, map_pow, map_natCast, hg']
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
  choose ρ hρ using fun k k' =>
    frame_inv_poly' (PD := PD) hinj sol (fun k => (hb.2 k).2) M K yy hyy zz hzz Y k k'
  obtain ⟨ν, hν, hYM⟩ := yM_gen W hTr hCA hR.1 h5p A hA a e
  have hYM' : Y ^ M = W.π₀ * Λ ^ 2 * ν := by rw [hYdef, hMdef, hYM]
  let GY : Fin d → Fin d → LetA O n := fun k m =>
    ∑ r ∈ Finset.range M, algebraMap O (LetA O n) (zz r k m) * Y ^ r
  have hGY : ∀ k m, GY k m ∈ W.AΔ := fun k m => W.AΔ.sum_mem fun r _ =>
    W.AΔ.mul_mem (W.AΔ.algebraMap_mem _) (W.AΔ.pow_mem hY r)
  have hpK : algebraMap O (LetA O n) (((PD.p : ℕ) : O) ^ (2 * K)) = lA W ^ (2 * K) := by
    rw [map_pow, map_natCast]; rfl
  refine ⟨κ' + 2 * K, fun k₀ => ?_⟩
  set θ : LetA O n := -(∑ m, GY k₀ m * (letE a * δ m)) -
    lA W ^ κ' * ν * ∑ k, aa k * Polynomial.aeval Y (ρ k₀ k) with hθ
  have hθΔ : θ ∈ W.AΔ := W.AΔ.sub_mem (W.AΔ.neg_mem (W.AΔ.sum_mem fun m _ => W.AΔ.mul_mem (hGY k₀ m)
      (W.AΔ.mul_mem (Formalism.MainNotions.UnusedSlot80.SatPW.letE_mem_AΔ W a) (hδ m))))
    (W.AΔ.mul_mem (W.AΔ.mul_mem (lA_mem W κ') hν) (W.AΔ.sum_mem fun k _ => W.AΔ.mul_mem (haa k).1
      (Formalism.MainNotions.UnusedSlot80.ArcF.aeval_mem_AΔ W hY _)))
  have hkey : lA W ^ (κ' + 2 * K) * aa k₀ = W.π₀ * Λ ^ 2 * θ := by
    have hS1 : ∑ m, GY k₀ m * E m = lA W ^ κ' * ∑ k, aa k * (∑ m, GY k₀ m * HY m k) := by
      simp only [E, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => by ring
    have hS2 : ∑ k, aa k * (∑ m, GY k₀ m * HY m k) =
        lA W ^ (2 * K) * aa k₀ + Y ^ M * ∑ k, aa k * Polynomial.aeval Y (ρ k₀ k) := by
      have : ∀ k, aa k * (∑ m, GY k₀ m * HY m k) =
          lA W ^ (2 * K) * ((if k₀ = k then 1 else 0) * aa k) + Y ^ M * (aa k * Polynomial.aeval Y (ρ k₀ k)) := by
        intro k
        have h := hρ k₀ k
        simp only [GY, HY] at h ⊢
        rw [h, map_mul, hpK, apply_ite (algebraMap O (LetA O n)), map_one, map_zero]
        ring
      rw [Finset.sum_congr rfl fun k _ => this k, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    have hS3 : ∑ m, GY k₀ m * E m = -(W.π₀ * Λ ^ 2 * ∑ m, GY k₀ m * (letE a * δ m)) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun m _ => by rw [hEm m]; ring
    rw [hS1, hS2, hYM'] at hS3
    rw [hθ, pow_add]
    linear_combination hS3
  have hlet : ∀ k, algebraMap (LetA O n) W.EE (letE a) * (f - g) k = (f - g) k := by
    intro k
    apply hΛc
    rw [← mul_assoc, mul_comm (algebraMap (LetA O n) W.EE Λ), mul_assoc, (haa k).2, ← map_mul, haal k]
  have hX : letE a * ∑ m, GY k₀ m * (letE a * δ m) = ∑ m, GY k₀ m * (letE a * δ m) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    linear_combination (GY k₀ m * δ m) * (letE_mul_self (O := O) a)
  have hZ : letE a * ∑ k, aa k * Polynomial.aeval Y (ρ k₀ k) = ∑ k, aa k * Polynomial.aeval Y (ρ k₀ k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, haal k]
  have hθl : letE a * θ = θ := by
    rw [hθ]
    linear_combination -hX - (lA W ^ κ' * ν) * hZ
  refine ⟨θ, hθΔ, ?_⟩
  rw [map_one, one_mul]
  apply hΛc
  have hfg : algebraMap (LetA O n) W.EE Λ * (f k₀ - g k₀) = algebraMap (LetA O n) W.EE (aa k₀) := (haa k₀).2
  have hlE : lE W (κ' + 2 * K) = algebraMap (LetA O n) W.EE (lA W ^ (κ' + 2 * K)) := by
    unfold lE lA; rw [map_pow, map_natCast]
  calc algebraMap (LetA O n) W.EE Λ * (lE W (κ' + 2 * K) * (f k₀ - g k₀))
      = lE W (κ' + 2 * K) * (algebraMap (LetA O n) W.EE Λ * (f k₀ - g k₀)) := by ring
    _ = algebraMap (LetA O n) W.EE (lA W ^ (κ' + 2 * K) * aa k₀) := by rw [hfg, hlE, map_mul]
    _ = algebraMap (LetA O n) W.EE Λ * algebraMap (LetA O n) W.EE (letE a * (W.π₀ * Λ) * θ) := by
      rw [hkey, ← map_mul]
      refine congrArg (algebraMap (LetA O n) W.EE) ?_
      conv_lhs => rw [← hθl]
      ring

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem tmul_mem_filV (x : V) {y : BdR} {a : ℤ} (hy : y ∈ PD.Fil a) :
    x ⊗ₜ[Qp] y ∈ FilV PD (LL := LL) (V := V) a :=
  ⟨x ⊗ₜ[Qp] (⟨y, hy⟩ : ↥((PD.Fil a).restrictScalars Qp)), by
    simp [TensorProduct.AlgebraTensorModule.map_tmul]⟩

theorem filV_exh (z : V ⊗[Qp] BdR) : ∃ a, z ∈ FilV PD (LL := LL) (V := V) a := by
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul x y =>
    obtain ⟨a, ha⟩ := PD.Fil_exh y
    exact ⟨a, tmul_mem_filV x ha⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, Submodule.add_mem _ (Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (min_le_left a b) ha)
      (Formalism.MainNotions.UnusedSlot80.LevR.filV_anti (min_le_right a b) hb)⟩

theorem filV_sep (z : V ⊗[Qp] BdR) (h : ∀ a, z ∈ FilV PD (LL := LL) (V := V) a) : z = 0 := by
  have hfree : Module.Free Qp V := Module.Free.of_divisionRing Qp V
  let 𝔟 := Module.Free.chooseBasis Qp V
  let E := TensorProduct.equivFinsuppOfBasisLeft (N := BdR) 𝔟
  have hcoord : ∀ a, ∀ w ∈ FilV PD (LL := LL) (V := V) a, ∀ i, E w i ∈ PD.Fil a := by
    intro a w hw i
    obtain ⟨u, rfl⟩ := hw
    induction u using TensorProduct.induction_on with
    | zero => simp [(PD.Fil a).zero_mem]
    | tmul x y =>
      simp only [TensorProduct.AlgebraTensorModule.map_tmul, LinearMap.id_apply, Submodule.coe_subtype]
      rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul]
      simp only [Finsupp.mapRange_apply]
      have : (𝔟.repr x i) • (y : BdR) = algebraMap Qp K (𝔟.repr x i) • (y : BdR) := by
        rw [algebraMap_smul]
      rw [this]
      exact (PD.Fil a).smul_mem _ y.2
    | add u₁ u₂ h₁ h₂ =>
      rw [map_add (f := _), map_add (f := _), Finsupp.add_apply]
      exact (PD.Fil a).add_mem h₁ h₂
  have hE : E z = 0 := by
    ext i
    exact PD.Fil_sep _ fun a => hcoord a z (h a) i
  exact E.injective (by rw [hE, map_zero])

end Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

open Formalism.MainNotions.ArcLiftingSetup

theorem fil_step (T : LocLat G Qp LL O) (c : ZMod n) (τ : K →ₐ[Qp] LL)
    (hover : ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb c x) (hsurj : Function.Surjective (algebraMap K₀ K))
    (a : ℤ) (hna : ¬ IsJumpV PD T.ρ τ a) {x : T.V ⊗[Qp] B} (hxD : x ∈ DcrisL PD T.ρ (W.emb c))
    (hx : x ∈ FilCris PD T.ρ a) : x ∈ FilCris PD T.ρ (a + 1) := by
  have hι : ιV PD (LL := LL) (V := T.V) x ∈ DdRE PD T.ρ τ :=
    Formalism.MainNotions.UnusedSlot80.LevR.ιDi_le W T c τ hover hsurj ⟨x, hxD, rfl⟩
  have h1 : ιV PD (LL := LL) (V := T.V) x ∈ FildR PD T.ρ τ a := ⟨hι, hx.2⟩
  have heq : FildR PD T.ρ τ (a + 1) = FildR PD T.ρ τ a := by
    by_contra hne; exact hna hne
  rw [← heq] at h1
  exact ⟨hx.1, h1.2⟩

theorem fil_low (T : LocLat G Qp LL O) (c : ZMod n) (τ : K →ₐ[Qp] LL)
    (hover : ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb c x) (hsurj : Function.Surjective (algebraMap K₀ K))
    (H : ℕ) (hJ : ∀ a, IsJumpV PD T.ρ τ a → -(H : ℤ) ≤ a) {x : T.V ⊗[Qp] B}
    (hxD : x ∈ DcrisL PD T.ρ (W.emb c)) : x ∈ FilCris PD T.ρ (-(H : ℤ)) := by
  obtain ⟨u₀, hu₀⟩ := filV_exh (PD := PD) (LL := LL) (ιV PD (LL := LL) (V := T.V) x)
  have hx0 : x ∈ FilCris PD T.ρ u₀ := ⟨hxD.1, hu₀⟩
  by_cases hle : -(H : ℤ) ≤ u₀
  · exact Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ hle hx0
  · have key : ∀ k : ℕ, u₀ + k ≤ -(H : ℤ) → x ∈ FilCris PD T.ρ (u₀ + k) := by
      intro k
      induction k with
      | zero => intro _; simpa using hx0
      | succ k ih =>
        intro hk
        have := fil_step W T c τ hover hsurj (u₀ + k) (fun hj => by have := hJ _ hj; push_cast at hk; omega)
          hxD (ih (by push_cast at hk; omega))
        push_cast; rwa [← add_assoc]
    have := key (-(H : ℤ) - u₀).toNat (by omega)
    rwa [show u₀ + ((-(H : ℤ) - u₀).toNat : ℤ) = -(H : ℤ) by omega] at this

theorem fil_high (T : LocLat G Qp LL O) (c : ZMod n) (τ : K →ₐ[Qp] LL)
    (hover : ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb c x) (hsurj : Function.Surjective (algebraMap K₀ K))
    (H : ℕ) (hJ : ∀ a, IsJumpV PD T.ρ τ a → a ≤ (H : ℤ)) (u : ℤ) (hu : (H : ℤ) < u) {x : T.V ⊗[Qp] B}
    (hxD : x ∈ DcrisL PD T.ρ (W.emb c)) (hx : x ∈ FilCris PD T.ρ u) : x = 0 := by
  have key : ∀ k : ℕ, x ∈ FilCris PD T.ρ (u + k) := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih =>
      have := fil_step W T c τ hover hsurj (u + k) (fun hj => by have := hJ _ hj; omega) hxD ih
      push_cast; rwa [← add_assoc]
  have hall : ∀ a, ιV PD (LL := LL) (V := T.V) x ∈ FilV PD (LL := LL) (V := T.V) a := by
    intro a
    by_cases ha : a ≤ u
    · exact Formalism.MainNotions.UnusedSlot80.LevR.filV_anti ha hx.2
    · have := (key (a - u).toNat).2
      rwa [show u + ((a - u).toNat : ℤ) = a by omega] at this
  have h0 := filV_sep (PD := PD) _ hall
  exact Formalism.MainNotions.UnusedSlot80.LevR.ιV_inj (by rw [h0, map_zero])

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

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

theorem secIn_zero {a : ZMod n} {e d : ℕ} (cond : (ℕ → ℤ) → (Fin d → O) → Prop) :
    SecIn W a e cond (fun _ => 0) :=
  ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun k => by simp⟩

theorem secIn_add {a : ZMod n} {e d : ℕ} {cond : (ℕ → ℤ) → (Fin d → O) → Prop} {F F' : Fin d → W.EE}
    (h : SecIn W a e cond F) (h' : SecIn W a e cond F') : SecIn W a e cond (F + F') := by
  obtain ⟨I, g, c₀, α, hg, hF⟩ := h
  obtain ⟨I', g', c₀', α', hg', hF'⟩ := h'
  refine ⟨I + I', Fin.append g g', Fin.append c₀ c₀', Fin.append α α', fun i => ?_, fun k => ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [Fin.append_left]; exact hg i
    · simp only [Fin.append_right]; exact hg' i
  · rw [Pi.add_apply, hF k, hF' k, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]

theorem inFr_mulA {a : ZMod n} {num den : LetA O n} {f : W.EE} (h : InFr W a num den f) {c : LetA O n}
    (hc : c ∈ W.AΔ) : InFr W a num den (algebraMap (LetA O n) W.EE c * f) := by
  obtain ⟨u, hu, hf⟩ := h
  refine ⟨c * u, W.AΔ.mul_mem hc hu, ?_⟩
  rw [mul_left_comm, hf, ← map_mul]
  congr 1; ring

theorem inFr_add {a : ZMod n} {num den : LetA O n} {f f' : W.EE} (h : InFr W a num den f)
    (h' : InFr W a num den f') : InFr W a num den (f + f') := by
  obtain ⟨u, hu, hf⟩ := h
  obtain ⟨u', hu', hf'⟩ := h'
  refine ⟨u + u', W.AΔ.add_mem hu hu', ?_⟩
  rw [mul_add, hf, hf', ← map_add (f := _)]
  congr 1; ring

theorem inFr_sub {a : ZMod n} {num den : LetA O n} {f f' : W.EE} (h : InFr W a num den f)
    (h' : InFr W a num den f') : InFr W a num den (f - f') := by
  obtain ⟨u, hu, hf⟩ := h
  obtain ⟨u', hu', hf'⟩ := h'
  refine ⟨u - u', W.AΔ.sub_mem hu hu', ?_⟩
  rw [mul_sub, hf, hf', ← map_sub]
  congr 1; ring

theorem inFr_zero {a : ZMod n} {num den : LetA O n} : InFr W a num den 0 :=
  ⟨0, W.AΔ.zero_mem, by simp⟩

theorem inFr_sum {a : ZMod n} {num den : LetA O n} {ι : Type} (s : Finset ι) (F : ι → W.EE)
    (h : ∀ j ∈ s, InFr W a num den (F j)) : InFr W a num den (∑ j ∈ s, F j) := by
  induction s using Finset.induction_on with
  | empty => simpa using inFr_zero W
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact inFr_add W (h j (Finset.mem_insert_self j s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem secIn_mulA {a : ZMod n} {e d : ℕ} {cond : (ℕ → ℤ) → (Fin d → O) → Prop} {F : Fin d → W.EE}
    (h : SecIn W a e cond F) {c : LetA O n} (hc : c ∈ W.AΔ) :
    SecIn W a e cond (fun k => algebraMap (LetA O n) W.EE c * F k) := by
  obtain ⟨I, g, c₀, α, hg, hF⟩ := h
  refine ⟨I, fun i => algebraMap (LetA O n) W.EE c * g i, c₀, α, fun i => ⟨inFr_mulA W (hg i).1 hc, (hg i).2⟩,
    fun k => ?_⟩
  show algebraMap (LetA O n) W.EE c * F k = _
  rw [hF k, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem dvO_succ (T : LocLat G Qp LL O) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → O) :
    dvO W T (e + 1) b c₀ = Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V) (dvO W T e b c₀) := by
  unfold dvO dv
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_smul, pow_succ', Module.End.mul_apply]

theorem dvO_add (T : LocLat G Qp LL O) (e s : ℕ) {d : ℕ} (b : Fin d → W.DD T) (c₀ : Fin d → O) :
    dvO W T (e + s) b c₀ = ((Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) ^ s) (dvO W T e b c₀) := by
  induction s with
  | zero => simp
  | succ s ih => rw [← add_assoc, dvO_succ, ih, pow_succ', Module.End.mul_apply]

theorem filS_succ (T : LocLat G Qp LL O) (a : ZMod n) (t : ℕ) (u : ℤ) :
    FilS W T (a + 1) (t + 1) u = (FilS W T a t u).map (Formalism.WeaklyAdmissibleFiltrations.φVB PD (LL := LL) (V := T.V)) := by
  unfold FilS
  rw [show a + 1 - ((t + 1 : ℕ) : ZMod n) = a - (t : ZMod n) by push_cast; ring, ← Submodule.map_comp]
  congr 1
  rw [pow_succ', Module.End.mul_eq_comp]

variable [IsDomain O]

theorem secIn_transport (T : LocLat G Qp LL O) (a : ZMod n) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T)
    (H : ℕ) {v : LetA O n} (hv : v ∈ W.AΔ) (hπ : W.π₀ ∈ W.AΔ)
    (hlow : ∀ c₀ : Fin d → O, dvO W T (e + 1) b c₀ ∈ FilS W T (a + 1) 0 (-(H : ℤ))) (F : Fin d → W.EE)
    (hF : SecIn W a e (condNN W T a e b) F) :
    SecIn W (a + 1) (e + 1) (condNN W T (a + 1) (e + 1) b)
      (fun k => algebraMap (LetA O n) W.EE (ps W 0 ^ H * v) * W.φE (F k)) := by
  obtain ⟨I, g, c₀, α, hg, hFe⟩ := hF
  refine ⟨I, fun i => algebraMap (LetA O n) W.EE (ps W 0 ^ H * v) * W.φE (g i), c₀,
    fun i s => if s = 0 then (H : ℤ) else α i (s - 1), fun i => ⟨?_, ?_⟩, fun k => ?_⟩
  · obtain ⟨u, hu, hgu⟩ := (hg i).1
    refine ⟨v * W.φA u, W.AΔ.mul_mem hv (Formalism.MainNotions.UnusedSlot80.ToolsR.φ_AΔ hu), ?_⟩
    have hl : W.φA (letE a : LetA O n) = letE (a + 1) := by
      have := φA_letE W (a + 1); rwa [show a + 1 - 1 = a by ring] at this
    have h1 := congrArg W.φE hgu
    rw [map_mul, φE_alg, φE_alg, map_mul W.φA, map_mul W.φA, hl] at h1
    have hnum : W.φA (∏ s ∈ Finset.range e, ps W s ^ (α i s).toNat) =
        ∏ s ∈ Finset.range e, ps W (s + 1) ^ (α i s).toNat := by
      rw [map_prod]; exact Finset.prod_congr rfl fun s _ => by rw [map_pow, ← ps_succ]
    have hden : W.φA (∏ s ∈ Finset.range e, ps W s ^ (-(α i s)).toNat) =
        ∏ s ∈ Finset.range e, ps W (s + 1) ^ (-(α i s)).toNat := by
      rw [map_prod]; exact Finset.prod_congr rfl fun s _ => by rw [map_pow, ← ps_succ]
    rw [hnum, hden] at h1
    show algebraMap (LetA O n) W.EE (∏ s ∈ Finset.range (e + 1), ps W s ^
        (-(if s = 0 then (H : ℤ) else α i (s - 1))).toNat) *
        (algebraMap (LetA O n) W.EE (ps W 0 ^ H * v) * W.φE (g i)) =
      algebraMap (LetA O n) W.EE ((letE (a + 1) * ∏ s ∈ Finset.range (e + 1), ps W s ^
        (if s = 0 then (H : ℤ) else α i (s - 1)).toNat) * (v * W.φA u))
    rw [Finset.prod_range_succ', Finset.prod_range_succ']
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, Int.toNat_natCast,
      Int.toNat_eq_zero.2 (by omega : -(H : ℤ) ≤ 0), pow_zero, mul_one]
    rw [mul_left_comm, h1]
    simp only [map_mul]
    ring
  · intro s hs
    rcases s with _ | t
    · beta_reduce
      simp only [↓reduceIte]
      exact hlow (c₀ i)
    · beta_reduce
      simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [filS_succ, dvO_succ]
      exact Submodule.mem_map_of_mem ((hg i).2 t (by omega))
  · show algebraMap (LetA O n) W.EE (ps W 0 ^ H * v) * W.φE (F k) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hFe k, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul W.φE, AlgHom.commutes]
    ring

end Formalism.MainNotions.UnusedSlot80.LevC
end
end

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

theorem tau_over (hbij : Function.Bijective (algebraMap K₀ K)) (c : ZMod n) :
    ∃ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ c ∧ ∀ x : K₀, τ (algebraMap K₀ K x) = W.emb c x := by
  let E : K₀ ≃ₐ[Qp] K := AlgEquiv.ofBijective (IsScalarTower.toAlgHom Qp K₀ K) hbij
  refine ⟨(W.emb c).comp E.symm.toAlgHom, ?_, fun x => ?_⟩
  · ext x
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe]
    congr 1
    exact E.symm_apply_apply x
  · simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.coe_coe]
    congr 1
    exact E.symm_apply_apply x

theorem dvO_letter (T : LocLat G Qp LL O) (c' : ZMod n) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e : ℕ) (c₀ : Fin d → O) :
    dvO W T e b c₀ ∈ DcrisL PD T.ρ (W.emb (c' + (e : ZMod n))) := by
  unfold dvO dv
  refine Submodule.sum_mem _ fun m _ => Submodule.smul_mem _ _ ?_
  have hbN : b m ∈ W.N T := (hb.1 m).1.1
  have hbl : (letE c' : LetA O n) • b m = b m := Formalism.MainNotions.UnusedSlot80.ArcF.letter_of_Nl W T c' (hb.1 m).2
  have hcl : cmpD W T (b m) ∈ DcrisL PD T.ρ (W.emb c') := by
    rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hbN]; exact Formalism.MainNotions.UnusedSlot80.ArcF.cmp_mem_letter W T c' hbN hbl
  exact Formalism.MainNotions.UnusedSlot80.ArcF.φVB_pow_letter W T c' hcl e

variable [IsDomain O]

theorem dvO_filLow (hbij : Function.Bijective (algebraMap K₀ K)) (A : ArcP n) (hA : A.OK) (c' : ZMod n)
    (hc' : c' ∈ A.cuts) (T : LocLat G Qp LL O) (hT : Win W A T) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e s : ℕ) (hse : s < e) (c₀ : Fin d → O) :
    dvO W T e b c₀ ∈ FilS W T (c' + (e : ZMod n)) s (-(A.Hs (c' + (e : ZMod n)) e s : ℤ)) := by
  set i : ZMod n := c' + ((e - s : ℕ) : ZMod n) with hidef
  obtain ⟨τ, hτ, hover⟩ := tau_over W hbij i
  have hJ : ∀ a, IsJumpV PD T.ρ τ a → -(A.Hs (c' + (e : ZMod n)) e s : ℤ) ≤ a := by
    intro a ha
    have hw := Formalism.MainNotions.UnusedSlot80.PhiPowers.win_sub A.G₀ A.S A.η (A.ty i) (hA.2.2.2.2.1 i) (hT.2 i τ hτ a ha)
    have hle := Formalism.MainNotions.UnusedSlot80.ArcC.hs_ge A hA c' hc' e (e - s) (by omega) (by omega)
    rw [show e - (e - s) = s by omega, ← hidef] at hle
    have := hw.1
    push_cast at this ⊢
    omega
  have hy := fil_low W T i τ hover hbij.2 _ hJ (dvO_letter W T c' b hb (e - s) c₀)
  refine ⟨dvO W T (e - s) b c₀, ⟨hy, ?_⟩, ?_⟩
  · rw [show c' + (e : ZMod n) - (s : ZMod n) = i by rw [hidef]; push_cast [Nat.cast_sub hse.le]; ring]
    exact dvO_letter W T c' b hb (e - s) c₀
  · rw [← dvO_add, Nat.sub_add_cancel hse.le]

theorem dvO_zero_high [NeZero n] (hbij : Function.Bijective (algebraMap K₀ K))
    (hinj : Function.Injective (algebraMap O LL)) (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing (LL := LL) O v)
    (hs : W.s = 1) (h5 : ∀ (T : LocLat G Qp LL O) (M h : ZMod n → ℕ), IsCrys PD T.ρ →
      Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h → Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (A : ArcP n) (hA : A.OK) (c' : ZMod n) (hc' : c' ∈ A.cuts) (T : LocLat G Qp LL O) (hT : Win W A T)
    (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) {d : ℕ} (b : Fin d → W.DD T)
    (hb : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c' b) (e s : ℕ) (hse : s < e) (u : ℤ)
    (hu : (A.Hs (c' + (e : ZMod n)) e s : ℤ) < u) (c₀ : Fin d → O)
    (h : dvO W T e b c₀ ∈ FilS W T (c' + (e : ZMod n)) s u) : c₀ = 0 := by
  obtain ⟨y, ⟨hyF, hyD⟩, hye⟩ := h
  set i : ZMod n := c' + (e : ZMod n) - (s : ZMod n) with hidef
  obtain ⟨τ, hτ, hover⟩ := tau_over W hbij i
  have hHw : Hw A.G₀ A.S A.η (A.ty i) ≤ A.Hs (c' + (e : ZMod n)) e s :=
    Formalism.MainNotions.UnusedSlot80.ArcC.hw_le_hs A hA c' hc' e s hse
  have hJ : ∀ a, IsJumpV PD T.ρ τ a → a ≤ (Hw A.G₀ A.S A.η (A.ty i) : ℤ) := fun a ha =>
    (Formalism.MainNotions.UnusedSlot80.PhiPowers.win_sub A.G₀ A.S A.η (A.ty i) (hA.2.2.2.2.1 i) (hT.2 i τ hτ a ha)).2
  have hy0 := fil_high W T i τ hover hbij.2 _ hJ u (by omega) hyD hyF
  rw [hy0, map_zero] at hye
  have hfb := (Formalism.MainNotions.UnusedSlot80.ArcF.frame_basis W hs hV T h3 (h5 T _ _ hT.1 (jumpsLet_of_win W A hA T hT))
    hmod c' e b hb).1
  have hdv : dvO W T e b c₀ = ∑ m, algebraMap O LL (c₀ m) • dv W T e b (Pi.single m 1) := by
    simp only [Formalism.MainNotions.UnusedSlot80.ArcF.dv_single]; rfl
  have hsum : ∑ m, algebraMap O LL (c₀ m) • dv W T e b (Pi.single m 1) = 0 := by rw [← hdv, ← hye]
  funext m
  apply hinj
  rw [Fintype.linearIndependent_iff.1 hfb _ hsum m]
  simp

theorem secIn_piLam (hπ : W.π₀ ∈ W.AΔ) (A : ArcP n) (a : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) {d : ℕ}
    (b : Fin d → W.DD T)
    (hlow : ∀ c₀ : Fin d → O, ∀ s < e, dvO W T e b c₀ ∈ FilS W T a s (-(A.Hs a e s : ℤ)))
    (h : Fin d → W.EE) (hh : ∀ k, InFr W a (W.π₀ * abelian₂ W A a e) 1 (h k)) :
    SecIn W a e (condNN W T a e b) h := by
  refine ⟨d, h, fun i => Pi.single i 1, fun _ s => (A.Hs a e s : ℤ), fun i => ⟨?_, ?_⟩, fun k => ?_⟩
  · obtain ⟨u, hu, hhu⟩ := hh i
    refine ⟨W.π₀ * u, W.AΔ.mul_mem hπ hu, ?_⟩
    have hnum : ∏ s ∈ Finset.range e, ps W s ^ ((A.Hs a e s : ℤ)).toNat = abelian₂ W A a e := by
      simp [abelian₂]
    have hden : ∏ s ∈ Finset.range e, ps W s ^ (-(A.Hs a e s : ℤ)).toNat = 1 :=
      Finset.prod_eq_one fun s _ => by rw [Int.toNat_eq_zero.2 (by omega), pow_zero]
    show algebraMap (LetA O n) W.EE (∏ s ∈ Finset.range e, ps W s ^ (-(A.Hs a e s : ℤ)).toNat) * h i =
      algebraMap (LetA O n) W.EE ((letE a * ∏ s ∈ Finset.range e, ps W s ^ ((A.Hs a e s : ℤ)).toNat) *
        (W.π₀ * u))
    rw [hden, hnum, ← one_mul (h i), ← map_one (algebraMap (LetA O n) W.EE), hhu, map_one, one_mul]
    congr 1; ring
  · intro s hs; exact hlow _ s hs
  · simp [Pi.single_apply]

end Formalism.MainNotions.UnusedSlot80.LevC
