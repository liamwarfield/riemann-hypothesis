module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.LocDataT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.OrdinaryJacquetModules.AtLOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WinConv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PolarizedLinkage.AIsoTwOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSpectrumGLOfResidual
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LaArtin

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnitaryPointProperties
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
open UpperTheory.V.HV (Coef)
section Alg
variable {L : Type} [Field L] [NumberField L] {l : ℕ} [Fact l.Prime] (n : ℕ) {V : Type} [Fintype V] (S : V → Plc L)
variable {n S}
end Alg
namespace HSet
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c)
variable (A : Type) [CommRing A] [Algebra c.O A]
variable {A} (θ : H.X.I.T →* Aˣ)
variable (ι : Qbar l ≃+* ℂ)
structure PartAltAlt (lam : Wt L l n) {d : ℕ} (ξ : GV n H.Sl →* GL (Fin d) ℂ) : Type 1 where
  Y : Submodule ℂ (Fin H.m → H.X.Fn ℂ d)
  le : Y ≤ H.Big ι ξ
  ne : Y ≠ ⊥
  σl : ∀ v : H.V, SmIrr (GLw n (H.Sl v))
  isoL : ∀ v, IsoSum (H.atV d v) Y (σl v)
  σq : ∀ q : H.Q, SmIrr (GLw n (H.wq q))
  isoQ : ∀ q : H.Q, IsoSum (H.atW ι d (H.wq q)) Y (σq q)
  a : H.Wp → ℕ → ℂ
  a_zero : ∀ w, a w 0 = 1
  sph : ∀ (w : H.Wp) j, ∀ F ∈ Y, sphOp (H.atW ι d w.1) j F = a w j • F
  r : H.Gq →* GL (Fin n) (Qbar l)
  cont : Continuous r
  ss : IsSSRep r
  frob : ∀ (w : H.Wp) (B : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver B w.1 → IsFrob B (normV w.1) σ →
    (r (H.prj σ⁻¹) : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.map ι.toRingHom = heckePol n (normV w.1) (a w)
  atL : ∀ v, _root_.UpperTheory.V.Z.Ord.AtLT ι (H.ovr v) (r.comp (H.dec v)) lam (σl v)
  atQ : ∀ (q : H.Q) (B : ValuationSubring Ω) (h : IsPlaceOver B (H.wq q)) (rc : IrrGL (k := (H.wq q).adicCompletion L) → WD h), _root_.UpperTheory.Zero.LLC.IsRecT h rc →
    _root_.UpperTheory.V.Z.Win.WOT ι (r.comp H.prj) (rc (algNorm (σq q)))
def AutomorphicHeckeSet (P : Wt L l n → (H.Gq →* GL (Fin n) (Qbar l)) → Prop) : Prop :=
  ∀ lam ∈ H.admitted, ∀ (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ), IsAlgWt ι lam ξ → ∀ F ∈ H.Big ι ξ,
    (∃ K, F ∈ fixd (H.X.raF d (H.τC ι)) (H.lev K)) → (∃ e, F ∈ fixd (H.X.rpF ℂ d H.m) (H.X.I.I1 e)) →
    F ∈ ⨆ Y : {Y : H.PartAltAlt ι lam ξ // P lam Y.r}, Y.1.Y
variable [IsLocalRing A] (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))]
end HSet
end UpperTheory.V.Hi
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.CLocConj
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
namespace UpperTheory.V.Hi.AxU
open GlobalTheory.SplitPts
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
  [IsAlgClosure L Ω] {n : ℕ}
private theorem sameOver {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) :
    w' = w ∨ w = conjSrc (conjE L) w' :=
  ((GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj L)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one L) w w').1 h).imp_right eq_conjSrc
private theorem cLoc_conj (x : UA L n) (u : Plc L) :
    cLoc u x = invT n _ (Matrix.GeneralLinearGroup.map (conjLoc (conjE L) u) (cLoc (conjSrc (conjE L) u) x)) := by
  have h := comp_eq x u
  rw [← inv_inj]
  apply Units.ext
  rw [Matrix.coe_units_inv, Matrix.inv_eq_left_inv h]
  rfl
private theorem mem_O {w : Plc L} (x : w.adicCompletion L) : x ∈ 𝒪[w.adicCompletion L] ↔ Valued.v x ≤ 1 := by
  have h : valuation (w.adicCompletion L) x ≤ valuation (w.adicCompletion L) 1 ↔
      Valued.v x ≤ Valued.v (1 : w.adicCompletion L) := by
    rw [← Valuation.Compatible.vle_iff_le]
    exact Iff.rfl
  change valuation _ x ≤ 1 ↔ _
  simpa using h
private theorem cLoc_one {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) (x : UA L n)
    (hx : cLoc w x = 1) : cLoc w' x = 1 := by
  rcases sameOver h with rfl | rfl
  · exact hx
  · rw [cLoc_conj, hx, map_one, map_one]
private theorem cLoc_KO {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) (x : UA L n)
    (hx : cLoc w x ∈ KO (w.adicCompletion L) (Fin n)) : cLoc w' x ∈ KO (w'.adicCompletion L) (Fin n) := by
  rcases sameOver h with rfl | rfl
  · exact hx
  · rw [cLoc_conj]
    rw [GlobalTheory.SplitFlip.mem_KO_iff] at hx ⊢
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · exact (mem_O _).2 (((conjLoc_spec (conjE L) w').2.2 _).trans_le ((mem_O _).1 (hx.2 j i)))
    · exact (mem_O _).2 (((conjLoc_spec (conjE L) w').2.2 _).trans_le ((mem_O _).1 (hx.1 j i)))
private theorem l_iff {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) :
    ((l : ℕ) : 𝓞 L) ∈ w'.asIdeal ↔ ((l : ℕ) : 𝓞 L) ∈ w.asIdeal := by
  have key : ∀ u : Plc L, ((l : ℕ) : 𝓞 L) ∈ u.asIdeal ↔ ((l : ℕ) : 𝓞 (Lp L)) ∈ (u.under (𝓞 (Lp L))).asIdeal := fun u => by
    change _ ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ u.asIdeal
    rw [map_natCast]
  rw [key, key, h]
private theorem cmp_eq {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal) (x : UA L n) :
    cmp n w ((away l L n).rangeRestrict x) = cLoc w x := by
  unfold CaseU.cmp
  rw [dite_eq_left h]
  rfl
private theorem cmp_l {w : Plc L} (h : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) (x : Ga l L n) : cmp n w x = 1 := by
  unfold CaseU.cmp
  rw [dite_eq_right (not_not.2 h)]
  rfl
private theorem ga_ext {x y : Ga l L n} (h : ∀ w, cmp n w x = cmp n w y) : x = y := by
  obtain ⟨x, rfl⟩ := (away l L n).rangeRestrict_surjective x
  obtain ⟨y, rfl⟩ := (away l L n).rangeRestrict_surjective y
  refine Subtype.ext (funext fun w => ?_)
  have := h w.1
  rwa [cmp_eq w.2, cmp_eq w.2] at this
private theorem cmp_one {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) (x : Ga l L n)
    (hx : cmp n w x = 1) : cmp n w' x = 1 := by
  by_cases hl : ((l : ℕ) : 𝓞 L) ∈ w'.asIdeal
  · exact cmp_l hl x
  obtain ⟨x, rfl⟩ := (away l L n).rangeRestrict_surjective x
  rw [cmp_eq (mt (l_iff h).2 hl)] at hx
  rw [cmp_eq hl]
  exact cLoc_one h x hx
private theorem cmp_KO {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) (x : Ga l L n)
    (hx : cmp n w x ∈ KO (w.adicCompletion L) (Fin n)) : cmp n w' x ∈ KO (w'.adicCompletion L) (Fin n) := by
  by_cases hl : ((l : ℕ) : 𝓞 L) ∈ w'.asIdeal
  · rw [cmp_l hl x]
    exact one_mem _
  obtain ⟨x, rfl⟩ := (away l L n).rangeRestrict_surjective x
  rw [cmp_eq (mt (l_iff h).2 hl)] at hx
  rw [cmp_eq hl]
  exact cLoc_KO h x hx
variable (s : HidaSetting l L Ω)
private theorem under_w (v : Plc (Lp L)) : (s.w v).under (𝓞 (Lp L)) = v := by
  ext x
  exact (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x)).symm.trans (s.hA v x)
private theorem mem_locA {w : Plc L} {x : Ub n s} :
    x ∈ locA n s w ↔ ∀ w' : Plc L, w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) → cmp n w' (x : Ga l L n) = 1 := by
  simp only [locA, Subgroup.mem_iInf, MonoidHom.mem_ker]
  rfl
private theorem sec_mem (w : Plc L) (g : GLw n w) : sec n s w g ∈ locA n s w := by
  unfold sec
  split_ifs
  · exact Subtype.property _
  · exact one_mem _
private theorem comm {w : Plc L} {u x : Ub n s} (hu : cmp n w (u : Ga l L n) = 1) (hx : x ∈ locA n s w) :
    Commute u x := by
  refine Subtype.ext (ga_ext fun w' => ?_)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
  by_cases h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
  · rw [cmp_one h _ hu, one_mul, mul_one]
  · rw [(mem_locA s).1 hx w' h, one_mul, mul_one]
private theorem comm' {w w' : Plc L} (h : w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) (g : GLw n w) (g' : GLw n w') :
    Commute (sec n s w g) (sec n s w' g') :=
  comm s ((mem_locA s).1 (sec_mem s w g) w' h) (sec_mem s w' g')
private theorem toKT_sec {w : Plc L} (h : w.under (𝓞 (Lp L)) ∉ s.S) (g : GLw n w) : toKT n s (sec n s w g) = 1 := by
  refine Subtype.ext (funext fun u => ?_)
  refine (mem_locA s).1 (sec_mem s w g) (s.w u) fun e => h ?_
  rw [← e, under_w]
  exact Or.inr (Or.inl u.2)
private theorem away_l {w : Plc L} (h : w.under (𝓞 (Lp L)) ∉ s.S) : ((l : ℕ) : 𝓞 L) ∉ w.asIdeal := fun e =>
  h (Or.inl (by
    change algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ w.asIdeal
    rwa [map_natCast]))
variable {s} {V : s.Lev} (Q : QData V)
private theorem mem_UQ {x : Ub n s} : x ∈ UQ n Q ↔
    (∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ V.S' → cmp n w (x : Ga l L n) ∈ KO (w.adicCompletion L) (Fin n)) ∧
      ∀ q, cmp n (Q.wq q) (x : Ga l L n) = 1 := by
  simp only [UQ, Subgroup.mem_inf, Subgroup.mem_iInf, MonoidHom.mem_ker, Subgroup.mem_comap]
  rfl
private theorem wq_mem (q : Q.Q) : (Q.wq q).under (𝓞 (Lp L)) ∈ V.S' := by
  rw [Q.range]
  exact Or.inr ⟨q, rfl⟩
private theorem sec_KO (hn : 1 ≤ n) {w : Plc L} (hw : w.under (𝓞 (Lp L)) ∉ V.S') (hs : IsSplitAt w) {k : GLw n w}
    (hk : k ∈ KO (w.adicCompletion L) (Fin n)) : sec n s w k ∈ UQ n Q := by
  have hc := ((secU l L Ω s n hn w hs).2 fun h => hw (V.sub h)).2.1 k
  refine (mem_UQ Q).2 ⟨fun w' _ => ?_, fun q => ?_⟩
  · by_cases h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
    · exact cmp_KO h _ (by rwa [hc])
    · rw [(mem_locA s).1 (sec_mem s w k) w' h]
      exact one_mem _
  · exact (mem_locA s).1 (sec_mem s w k) _ fun e => hw (e ▸ wq_mem Q q)
private theorem dec (hn : 1 ≤ n) {w : Plc L} (hw : w.under (𝓞 (Lp L)) ∉ V.S') (hs : IsSplitAt w) {u : Ub n s}
    (hu : u ∈ UQ n Q) : ∃ k ∈ KO (w.adicCompletion L) (Fin n), ∃ u' ∈ UQ n Q,
      u = sec n s w k * u' ∧ ∀ g, Commute u' (sec n s w g) := by
  have hc := ((secU l L Ω s n hn w hs).2 fun h => hw (V.sub h)).2.1
  have hk := ((mem_UQ Q).1 hu).1 w hw
  refine ⟨_, hk, (sec n s w (cmp n w (u : Ga l L n)))⁻¹ * u, mul_mem (inv_mem (sec_KO Q hn hw hs hk)) hu,
    (mul_inv_cancel_left _ _).symm, fun g => comm s ?_ (sec_mem s w g)⟩
  rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hc, inv_mul_cancel]
variable (s) in
private theorem sec_cmp (hn : 1 ≤ n) {w : Plc L} (hw : w.under (𝓞 (Lp L)) ∉ s.S) (hs : IsSplitAt w) {x : Ub n s}
    (hx : x ∈ locA n s w) : sec n s w (cmp n w (x : Ga l L n)) = x := by
  obtain ⟨hb, hc, hm⟩ := (secU l L Ω s n hn w hs).2 hw
  exact congrArg Subtype.val (hb.1 (a₁ := ⟨_, hm _⟩) (a₂ := ⟨x, hx⟩) (hc _))
variable (s) in
private theorem same (hn : 1 ≤ n) {w w' : Plc L} (hw : w.under (𝓞 (Lp L)) ∉ s.S) (hs : IsSplitAt w) (hs' : IsSplitAt w')
    (h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))) :
    ∃ e : GLw n w' ≃* GLw n w, (∀ g, e g ∈ KO (w.adicCompletion L) (Fin n) ↔ g ∈ KO (w'.adicCompletion L) (Fin n)) ∧
      ∀ g, sec n s w' g = sec n s w (e g) := by
  have hw' : w'.under (𝓞 (Lp L)) ∉ s.S := by rwa [h]
  have hc := ((secU l L Ω s n hn w hs).2 hw).2.1
  have hc' := ((secU l L Ω s n hn w' hs').2 hw').2.1
  have h1 : ∀ g, sec n s w (cmp n w (sec n s w' g : Ga l L n)) = sec n s w' g := fun g =>
    sec_cmp s hn hw hs ((mem_locA s).2 fun u hu => (mem_locA s).1 (sec_mem s w' g) u (by rwa [h]))
  have h2 : ∀ g, sec n s w' (cmp n w' (sec n s w g : Ga l L n)) = sec n s w g := fun g =>
    sec_cmp s hn hw' hs' ((mem_locA s).2 fun u hu => (mem_locA s).1 (sec_mem s w g) u (by rwa [← h]))
  refine ⟨{ toFun := fun g => cmp n w (sec n s w' g : Ga l L n)
            invFun := fun g => cmp n w' (sec n s w g : Ga l L n)
            left_inv := fun g => by simp only [h1, hc']
            right_inv := fun g => by simp only [h2, hc]
            map_mul' := fun g g' => by rw [map_mul, Subgroup.coe_mul, map_mul] }, fun g => ⟨fun hg => ?_, fun hg => ?_⟩,
    fun g => (h1 g).symm⟩
  · have := cmp_KO h _ hg
    rwa [hc'] at this
  · exact cmp_KO h.symm _ (by rwa [hc'])
variable (V) in
private theorem pr_surj : Function.Surjective V.pr := by
  rintro ⟨x, hx⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (NS Ω V.S') x
  obtain ⟨σ, rfl⟩ := (V.hη g).1 hx
  exact ⟨σ, rfl⟩
variable (V) in
private theorem dense : Dense {g : V.η.ker | ∃ w ∈ {w : Plc L | w.under (𝓞 (Lp L)) ∉ V.S' ∧ IsSplitAt w},
    ∃ (A : ValuationSubring Ω) (σ : G L Ω), IsPlaceOver A w ∧ IsFrob A (normV w) σ ∧ g = V.pr σ⁻¹} := by
  have hfin1 : {w : Plc L | w.asIdeal ∣ differentIdeal (𝓞 (Lp L)) (𝓞 L)}.Finite :=
    Ideal.finite_factors differentIdeal_ne_bot
  have hfin2 : ((fun w : Plc L => w.under (𝓞 (Lp L))) ⁻¹' V.S').Finite := by
    refine V.fin.preimage' fun v _ => ?_
    have := v.isMaximal
    refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).preimage
      (f := fun w : Plc L => w.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
    rintro w rfl
    exact ⟨w.isPrime, ⟨rfl⟩⟩
  have hD := GlobalTheory.Published.ChebotarevDegreeOne.dense (F := L) (Ω := Ω) GlobalTheory.Published.chebotarevDegreeOne'
    (hfin1.union hfin2)
  have hs : Function.Surjective fun σ : G L Ω => V.pr σ⁻¹ := (pr_surj V).comp inv_surjective
  refine (hs.denseRange.dense_image ((V.pr_cont W.continuous_resP).comp continuous_inv) hD).mono ?_
  rintro _ ⟨σ, ⟨w, hw, hd, B, hB, hF⟩, rfl⟩
  have := w.isPrime
  exact ⟨w, ⟨fun h => hw (Or.inr h),
    UpperTheory.isSplitAt_of_unramified_of_inertiaDeg_eq_one L w (not_dvd_differentIdeal_iff.1 fun h => hw (Or.inl h)) hd⟩, B, σ, hB, hF, rfl⟩
end UpperTheory.V.Hi.AxU
open UpperTheory.V.Hi.AxU in
theorem UpperTheory.V.Hi.axU_s :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), (hset Q τ₀).Ax := by
  intro H l _ L Ω _ _ _ _ _ _ s n hn V Q c m τ₀
  exact
    { odd := s.odd
      pos := hn
      Sl_over := fun v => by
        have h : ((l : ℕ) : 𝓞 (Lp L)) ∈ ((s.w v.1).under (𝓞 (Lp L))).asIdeal := by
          rw [under_w]
          exact v.2
        change algebraMap (𝓞 (Lp L)) (𝓞 L) _ ∈ (s.w v.1).asIdeal at h
        rwa [map_natCast] at h
      Sl_inj := fun v v' h => Subtype.ext (by
        rw [← under_w s v.1, ← under_w s v'.1]
        exact congrArg _ h)
      art_spec := fun v => Classical.epsilon_spec (_root_.UpperTheory.V.Z.Win.T2.laArtinLit' H (s.hw v.1))
      Q_away := fun q => away_l s (Q.notS q)
      Wp_away := fun w hw => away_l s fun h => hw.1 (V.sub h)
      fin := UpperTheory.V.Hi.finU l L Ω s n hn V Q c m τ₀
      τ_Q := fun q g => (congrArg τ₀ (toKT_sec s (Q.notS q) g)).trans (map_one τ₀)
      coefficientRep_trivial_on_unramified := fun w hw g => (congrArg τ₀ (toKT_sec s (fun h => hw.1 (V.sub h)) g)).trans (map_one τ₀)
      Q_UQ := fun q u hu g => comm s (((mem_UQ Q).1 hu).2 q) (sec_mem s _ g)
      Q_Q := fun q q' h => comm' s fun e => h (Q.inj e).symm
      sectionsCommuteAtSplit := fun q w hw => comm' s fun e => hw.1 (e ▸ wq_mem Q q)
      W_le := fun w hw => by
        rintro _ ⟨k, hk, rfl⟩
        exact sec_KO Q hn hw.1 hw.2 hk
      W_dec := fun w hw u hu => dec Q hn hw.1 hw.2 hu
      Wm_mul_Wm_comm := fun w hw w' hw' => by
        by_cases h : w'.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
        · exact Or.inr (same s hn (fun h => hw.1 (V.sub h)) hw.2 hw'.2 h)
        · exact Or.inl (comm' s h)
      prj_cont := V.pr_cont W.continuous_resP
      dense := dense V }
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PaLevel
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Pa
section Lv
variable (l : ℕ) {L : Type} [Field L] [NumberField L] (n : ℕ) {q : ℕ} (w : Fin q → Plc L)
end Lv
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {s : HidaSetting l L Ω} {V0 : s.Lev} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] {n : ℕ}
  {r : Resid V0.frame O n} {B : UniversalOrdinaryDeterminantRing r} {J : Ideal B.B} {D : ℕ} (b : TWBase (pairOf B.u) J Empty D)
  {V : s.Lev} (h : (globOf r V).Hom (globOf r V0)) {q : ℕ} (w : Fin q → Plc L)
variable {b h w}
structure LevPtAlt (A : LevMod b h w) (ι : Qbar l ≃+* ℂ) : Type 1 where
  θ : A.R →+* Qbar l
  rep : (globOf r V).G₀ →* GL (Fin n) (Qbar l)
  cont : Continuous rep
  det : A.p.D.map θ = GDet.ofRep (mat rep)
  Y : Type
  [add : AddCommGroup Y]
  [mod : Module ℂ Y]
  π : Representation ℂ (GV n w) Y
  sp : A.P →+ Y
  sp_smul : ∀ (t : A.R) m, sp (t • m) = ι (θ t) • sp m
  sp_act : ∀ g m, sp (A.ρ g m) = π g (sp m)
  σ : ∀ j, SmIrr (GLw n (w j))
  iso : ∀ j, IsoSum (π.comp (atJ n w j)) ⊤ (σ j)
  lg : ∀ j (Bq : ValuationSubring Ω) (hB : IsPlaceOver Bq (w j)) (rc : IrrGL (k := (w j).adicCompletion L) → WD hB), _root_.UpperTheory.Zero.LLC.IsRecT hB rc →
    _root_.UpperTheory.V.Z.Win.WOT ι (rep.comp V.pr) (rc (algNorm (σ j)))
attribute [instance] LevPtAlt.add LevPtAlt.mod
def LevMod.ClassicalAlt (A : LevMod b h w) : Prop :=
  ∃ ι : Qbar l ≃+* ℂ, ∀ m : A.P, (∀ x : _root_.UpperTheory.V.Pa.LevPtAlt A ι, x.sp m = 0) → m = 0
variable (B J) in
def LevelAlt : Prop :=
  ∃ b : TWBase (pairOf B.u) J Empty (n * Module.finrank ℚ (Lp L)),
    ∀ (V : s.Lev) (h : (globOf r V).Hom (globOf r V0)) (q : ℕ) (v : Fin q → Plc (Lp L)) (w : Fin q → Plc L)
      (Bq : Fin q → ValuationSubring Ω), (∀ g, h.p (toGS Ω V.S' g) = toGS Ω V0.S' g) → Function.Injective v → (∀ j, v j ∉ s.S) →
      V.S' = s.S ∪ Set.range v → (∀ j, IsPlaceOver (Bq j) (w j)) → (∀ j, IsPlaceOver (Bq j) (v j)) →
      (∀ j, Dec (F := Lp L) (Bq j) ≤ (resP L Ω).range) → ∃ A : LevMod b h w, A.ClassicalAlt
structure LocPAlt : Prop where
  bz : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  gl : GlobalTheory.Published.GeometricLemma
  tame : GlobalTheory.Published.TameLocal
def HasAutOfAlt : Prop :=
  _root_.UpperTheory.V.Pa.LocPAlt → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V0 : s.Lev) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O]
    [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) (B : UniversalOrdinaryDeterminantRing r) (J : Ideal B.B), V0.S' = s.S → _root_.UpperTheory.V.Pa.LevelAlt B J → HasAut B J
end UpperTheory.V.Pa
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TWtBridge
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
private theorem uc_eq (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (e : ℕ) :
    Uc k e = GroundTheory.LocalField.unitFiltrationUnits k e := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, Ideal.Quotient.eq.1 (congrArg Units.val hu), rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, Units.ext (Ideal.Quotient.eq.2 hu), rfl⟩
section Loc
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  {A : ValuationSubring Ω} {w : Plc F} {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion F)ˣ}
private theorem artin_unique (H : GlobalTheory.Published.GlobalArtinReciprocity) {a' : Weil h →* (w.adicCompletion F)ˣ}
    (ha : IsLocalArtin h a) (ha' : IsLocalArtin h a') : a' = a := by
  obtain ⟨art, hart⟩ := H F Ω
  have hinj := GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' F Ω art hart w
  exact MonoidHom.ext fun σ => hinj ((ha'.glob art hart _).trans (ha.glob art hart _).symm)
private theorem art_unit (ha : IsLocalArtin h a) (σ : Ine (F := F) A) : a (ineIncl h σ) ∈ Uo (w.adicCompletion F) := by
  have h2 := ha.ord_eq (ineIncl h σ)
  rw [deg_ineIncl, neg_zero] at h2
  exact GlobalTheory.SmGL.ord_eq_zero_iff.1 h2
private theorem art_onto (ha : IsLocalArtin h a) (y : Uo (w.adicCompletion F)) :
    ∃ σ : Ine (F := F) A, a (ineIncl h σ) = y := by
  obtain ⟨s, hs⟩ := ha.surj y
  have hd : deg s = 0 := by
    have h2 := ha.ord_eq s
    rw [hs, GlobalTheory.SmGL.ord_eq_zero_iff.2 y.2] at h2
    omega
  exact ⟨⟨s, actsAs_zero_iff.1 (actsAs_of_deg (a := 0) (b := 0) (by simpa using hd))⟩, hs⟩
private theorem pw_ne (wt : W.Emb l w → ℤ) (x : (w.adicCompletion F)ˣ) :
    ∏ᶠ τ : W.Emb l w, τ.1 (x : w.adicCompletion F) ^ wt τ ≠ 0 := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite (W.Emb l w)
  rw [finprod_eq_prod_of_fintype]
  exact Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ ((map_ne_zero j.1).2 x.ne_zero)
private noncomputable def pwHom (wt : W.Emb l w → ℤ) : (w.adicCompletion F)ˣ →* (Qbar l)ˣ :=
  MonoidHom.mk' (fun x => Units.mk0 _ (pw_ne wt x)) fun x y => Units.ext (by
    haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
    simp only [Units.val_mul, Units.val_mk0]
    rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
    exact finprod_congr fun j => by rw [map_mul, mul_zpow])
variable {κ : Dec (F := F) A →* (Qbar l)ˣ} {wt : W.Emb l w → ℤ} {f : Uo (w.adicCompletion F) → Qbar l}
private def IsFin (a : Weil h →* (w.adicCompletion F)ˣ) (κ : Dec (F := F) A →* (Qbar l)ˣ) (wt : W.Emb l w → ℤ)
    (f : Uo (w.adicCompletion F) → Qbar l) : Prop :=
  ∀ (σ : Ine (F := F) A) (y : Uo (w.adicCompletion F)), a (ineIncl h σ) = y →
    (κ (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h σ)) : Qbar l) * f y =
      ∏ᶠ τ : W.Emb l w, τ.1 ((y : (w.adicCompletion F)ˣ) : w.adicCompletion F) ^ (-wt τ)
private theorem part_val (ha : IsLocalArtin h a) (hf : IsFin a κ wt f) {ph : Ine (F := F) A →* (Qbar l)ˣ}
    (hp : W.IsWtPart h κ wt ph) (σ : Ine (F := F) A) (y : Uo (w.adicCompletion F)) (e : a (ineIncl h σ) = y) :
    (ph σ : Qbar l) = f y := by
  have h1 := hp.2 a ha σ
  rw [e, ← hf σ y e, Units.val_mul] at h1
  exact mul_left_cancel₀ (Units.ne_zero _) h1
private theorem locAlg_iff (H : GlobalTheory.Published.GlobalArtinReciprocity) (ha : IsLocalArtin h a) (hf : IsFin a κ wt f) :
    W.IsLocAlg h κ wt ↔ ∃ e, ∀ y : Uo (w.adicCompletion F), (y : (w.adicCompletion F)ˣ) ∈ Uc _ e → f y = 1 := by
  constructor
  · rintro ⟨ph, hp⟩
    haveI := compactSpace_Ine (E := F) A
    have hC : IsClosed ((fun σ : Ine (F := F) A => a (ineIncl h σ)) '' (ph.ker : Set (Ine (F := F) A))ᶜ) :=
      (hp.1.isClosed_compl.isCompact.image ha.cont).isClosed
    have h1 : (1 : (w.adicCompletion F)ˣ) ∉ (fun σ : Ine (F := F) A => a (ineIncl h σ)) '' (ph.ker : Set (Ine (F := F) A))ᶜ := by
      rintro ⟨σ, hσ, e⟩
      refine hσ (Units.ext ?_)
      rw [part_val ha hf hp σ 1 e, ← part_val ha hf hp 1 1 (by simp), map_one]
    obtain ⟨e, -, he⟩ := GroundTheory.LocalField.hasBasis_nhds_one_unitFiltrationUnits.mem_iff.1 (hC.isOpen_compl.mem_nhds h1)
    refine ⟨e, fun y hy => ?_⟩
    obtain ⟨σ, hσ⟩ := art_onto ha y
    rw [uc_eq] at hy
    have h2 : ph σ = 1 := by
      by_contra h3
      exact he hy ⟨σ, h3, hσ⟩
    rw [← part_val ha hf hp σ y hσ, h2, Units.val_one]
  · rintro ⟨e, he⟩
    let ph : Ine (F := F) A →* (Qbar l)ˣ :=
      ((κ.comp (Subgroup.inclusion (Weil_le_Dec h)))⁻¹ * (pwHom fun τ => -wt τ).comp a).comp (ineIncl h)
    have hv : ∀ σ, ((κ (Subgroup.inclusion (Weil_le_Dec h) (ineIncl h σ)) * ph σ : (Qbar l)ˣ) : Qbar l) =
        ∏ᶠ τ : W.Emb l w, τ.1 (a (ineIncl h σ) : w.adicCompletion F) ^ (-wt τ) := fun σ =>
      congrArg Units.val (mul_inv_cancel_left _ (pwHom (fun τ => -wt τ) (a (ineIncl h σ))))
    refine ⟨ph, Subgroup.isOpen_mono (H₁ := (Uc _ e).comap (a.comp (ineIncl h))) (fun σ hσ => ?_) ?_, fun a' ha' σ => ?_⟩
    · have h1 := hf σ ⟨_, art_unit ha σ⟩ rfl
      rw [he ⟨_, art_unit ha σ⟩ hσ, mul_one, ← hv, Units.val_inj, left_eq_mul] at h1
      exact h1
    · rw [uc_eq]
      exact (GroundTheory.LocalField.isOpen_unitFiltrationUnits e).preimage ha.cont
    · rw [artin_unique H ha ha', hv]
private theorem emb_lt (j : W.Emb l w) (x : 𝓞 F) (hx : x ∈ w.asIdeal) : ‖j.1 (algebraMap F _ (x : F))‖ < 1 := by
  have h1 : Valued.v (algebraMap F (w.adicCompletion F) (x : F)) < 1 := by
    rw [show algebraMap F (w.adicCompletion F) (x : F) = ((x : F) : w.adicCompletion F) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (w.valuation_lt_one_iff_mem x).2 hx
  have h2 := (j.2.tendsto 0).comp (Valued.tendsto_zero_pow_of_v_lt_one h1)
  rw [map_zero] at h2
  exact tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 (h2.congr fun m => map_pow _ _ _)
private theorem emb_place {w' : Plc F} (j : W.Emb l w) (j' : W.Emb l w')
    (e : j.1.comp (algebraMap F _) = j'.1.comp (algebraMap F _)) : w = w' := by
  by_contra hne
  have h1 : w.asIdeal ⊔ w'.asIdeal = ⊤ :=
    Ideal.IsMaximal.coprime_of_ne w.isMaximal w'.isMaximal fun h => hne (HeightOneSpectrum.ext h)
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 (h1 ▸ Submodule.mem_top : (1 : 𝓞 F) ∈ w.asIdeal ⊔ w'.asIdeal)
  have h2 := emb_lt j x hx
  have h3 := emb_lt j' y hy
  rw [← show j.1 (algebraMap F _ (y : F)) = j'.1 (algebraMap F _ (y : F)) from DFunLike.congr_fun e _] at h3
  have h4 := (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h2 h3)
  rw [← map_add (f := _), ← map_add (f := _), show (x : F) + (y : F) = ((x + y : 𝓞 F) : F) from (map_add (algebraMap (𝓞 F) F) x y).symm,
    hxy] at h4
  simp at h4
private theorem emb_inj (j j' : W.Emb l w) (e : j.1.comp (algebraMap F _) = j'.1.comp (algebraMap F _)) : j = j' := by
  refine Subtype.ext (DFunLike.coe_injective ?_)
  refine (HeightOneSpectrum.denseRange_algebraMap (K := F) (v := w)).equalizer j.2 j'.2 ?_
  funext x
  exact DFunLike.congr_fun e x
end Loc
section Glob
variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  (s : HidaSetting l L Ω)
private theorem mem_w (v : Plc (Lp L)) (x : 𝓞 (Lp L)) :
    x ∈ v.asIdeal ↔ algebraMap (𝓞 (Lp L)) (𝓞 L) x ∈ (s.w v).asIdeal :=
  (s.hA v x).symm.trans (s.hw v (algebraMap (𝓞 (Lp L)) (𝓞 L) x))
private theorem w_inj : Function.Injective s.w := fun v v' e =>
  HeightOneSpectrum.ext (Ideal.ext fun x => by rw [mem_w s, mem_w s, e])
private theorem w_over (v : Vl l L) : ((l : ℕ) : 𝓞 L) ∈ (s.w v.1).asIdeal := by
  simpa using (mem_w s v.1 _).1 v.2
private theorem wt_ex {n : ℕ} (h : s.Wt n) (hh : h.Incr) : ∃ lam, WtOf h lam := by
  classical
  let μ : ∀ v : Vl l L, W.Emb l (s.w v.1) → DomWeight n := fun v τ =>
    ⟨fun i => h v i.rev τ - (i.rev : ℕ), fun i j hij => by
      have key : ∀ (d : ℕ) (a b : Fin n), (b : ℕ) = a + d → h v a τ + d ≤ h v b τ := fun d => by
        induction d with
        | zero => intro a b e; rw [show b = a from Fin.ext e]; simp
        | succ d ih =>
          intro a b e
          have h1 := ih a ⟨a + d, by omega⟩ rfl
          have h2 := hh v τ (show (⟨a + d, by omega⟩ : Fin n) < b from by rw [Fin.lt_def]; simp only; omega)
          simp only at h2
          push_cast
          omega
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show ((j.rev : Fin n) : ℕ) ≤ i.rev from Fin.rev_le_rev.2 hij)
      have := key d _ _ hd
      simp only
      omega⟩
  refine ⟨fun σ => if H : ∃ p : Σ v : Vl l L, W.Emb l (s.w v.1), p.2.1.comp (algebraMap L _) = σ then
    μ H.choose.1 H.choose.2 else ⟨0, fun _ _ _ => le_rfl⟩, fun v j τ => ?_⟩
  have H : ∃ p : Σ v : Vl l L, W.Emb l (s.w v.1), p.2.1.comp (algebraMap L _) = τ.1.comp (algebraMap L _) := ⟨⟨v, τ⟩, rfl⟩
  have e : H.choose = ⟨v, τ⟩ := by
    have h1 := H.choose_spec
    generalize H.choose = p at h1
    obtain ⟨v', τ'⟩ := p
    obtain rfl : v' = v := Subtype.ext (w_inj s (emb_place τ' τ h1))
    rw [emb_inj τ' τ h1]
  simp only [htW, lowW, dif_pos H]
  rw [e]
  simp [μ]
end Glob
theorem UpperTheory.V.Hi.arith_good_iff_hset_of_theta_incr_weight :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (n : ℕ), 1 ≤ n →
    ∀ (V : s.Lev) (Q : QData V) (c : Coef l), ∀ (m : ℕ) (τ₀ : KT n (wt s) →* GL (Fin m) c.O), ∀ (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r) (θ : (hset Q τ₀).X.I.T →* Λ.Λˣ), IsTheta Q τ₀ Λ θ → ∀ h : s.Wt n, h.Incr → (∃ lam, WtOf h lam) ∧ ∀ lam, WtOf h lam → ∀ x : B.Pt, (x.Arith h ↔ (hset Q τ₀).Arith θ (x.comp (Λ.toPair B.u)).toRingHom lam) ∧ (x.Good h ↔ (hset Q τ₀).Good θ (x.comp (Λ.toPair B.u)).toRingHom lam) := by
  intro N l _ L Ω _ _ _ _ _ _ s n _ V Q c m τ₀ r B Λ θ hθ h hh
  refine ⟨wt_ex s h hh, fun lam hl x => ?_⟩
  have H := N.aut.art
  have ha : ∀ v : Vl l L, IsLocalArtin (s.hw v.1) (artOf (s.hw v.1)) := fun v =>
    Classical.epsilon_spec (_root_.UpperTheory.V.Z.Win.T2.laArtinLit' N (s.hw v.1))
  have hf : ∀ (v : Vl l L) (i : Fin n), IsFin (artOf (s.hw v.1)) (x.psi v i) (h v i)
      ((hset Q τ₀).finPart θ (x.comp (Λ.toPair B.u)).toRingHom lam v i) := by
    intro v i σ y e
    let g : Dec (F := L) (s.A v.1) := Subgroup.inclusion (Weil_le_Dec (s.hw v.1)) (ineIncl (s.hw v.1) σ)
    have hg : g ∈ V.frame.Iv v := σ.2
    have h1 := congrArg (fun u : Λ.Λˣ => (x.comp (Λ.toPair B.u)) (u : Λ.Λ)) (hθ v i (ineIncl (s.hw v.1) σ) g hg y rfl e)
    have h2 : (x.comp (Λ.toPair B.u)) (Λ.κ v i ⟨g, hg⟩ : Λ.Λ) = x.psi v i g := by
      have h6 := DFunLike.congr_fun (W.LamObj.toPair_spec r Λ B.u v i) (⟨g, hg⟩ : V.frame.Iv v)
      exact congrArg (fun u : B.Bˣ => x (u : B.B)) h6
    have h3 : (x.comp (Λ.toPair B.u)) ((hset Q τ₀).epsV Λ.Λ v g : Λ.Λ) =
        ∏ᶠ τ : W.Emb l (s.w v.1), τ.1 ((y : ((s.w v.1).adicCompletion L)ˣ) : (s.w v.1).adicCompletion L) ^ (1 : ℤ) := by
      have h4 := (UpperTheory.V.Loc.laCyc H (s.hw v.1) (w_over s v)).2 _ (ha v) σ
      rw [e] at h4
      simp only [MonoidHom.one_apply, mul_one, neg_neg] at h4
      rw [← h4]
      refine ((x.comp (Λ.toPair B.u)).commutes (algebraMap ℤ_[l] c.O (cycZ L Ω l g : ℤ_[l]))).trans ?_
      exact (IsScalarTower.algebraMap_apply ℤ_[l] c.O (Qbar l) _).symm
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, Units.val_one, map_one] at h1
    rw [h2, h3] at h1
    haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) (s.w v.1)
    haveI := Fintype.ofFinite (W.Emb l (s.w v.1))
    have h0 : ∀ τ : W.Emb l (s.w v.1), τ.1 ((y : ((s.w v.1).adicCompletion L)ˣ) : (s.w v.1).adicCompletion L) ≠ 0 :=
      fun τ => (_root_.map_ne_zero _).2 (Units.ne_zero _)
    have h5 : ∏ᶠ τ : W.Emb l (s.w v.1), τ.1 ((y : ((s.w v.1).adicCompletion L)ˣ) : (s.w v.1).adicCompletion L) ^ (-h v i τ) =
        ((∏ᶠ τ : W.Emb l (s.w v.1), τ.1 ((y : ((s.w v.1).adicCompletion L)ˣ) : (s.w v.1).adicCompletion L) ^ (1 : ℤ)) ^ (i : ℕ))⁻¹ /
          algPow (s.w v.1) (lowW lam i) ((y : ((s.w v.1).adicCompletion L)ˣ) : (s.w v.1).adicCompletion L) := by
      unfold algPow
      simp only [finprod_eq_prod_of_fintype]
      rw [← Finset.prod_pow, ← Finset.prod_inv_distrib, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun τ _ => ?_
      rw [← hl v i τ, htW, zpow_one, ← zpow_natCast, ← zpow_neg, ← zpow_sub₀ (h0 τ)]
      congr 1
      ring
    rw [mul_right_comm] at h1
    rw [h5, ← eq_inv_of_mul_eq_one_left h1, mul_div_assoc]
    rfl
  have hA : (∀ (v : Vl l L) (j : Fin n), W.IsLocAlg (s.hw v.1) (x.psi v j) (h v j)) ↔
      (hset Q τ₀).Arith θ (x.comp (Λ.toPair B.u)).toRingHom lam := by
    simp only [fun v j => locAlg_iff H (ha v) (hf v j)]
    refine ⟨fun h1 => ?_, fun ⟨e, he⟩ v j => ⟨e, he v j⟩⟩
    choose e he using h1
    haveI : Finite (Vl l L) := inferInstanceAs (Finite V.frame.Vl)
    obtain ⟨E, hE⟩ := (Set.finite_range fun p : Vl l L × Fin n => e p.1 p.2).bddAbove
    refine ⟨E, fun v i y hy => he v i y ?_⟩
    rw [uc_eq] at hy ⊢
    exact GroundTheory.LocalField.unitFiltrationUnits_antitone (hE ⟨(v, i), rfl⟩) hy
  refine ⟨(and_iff_right hh).trans hA, (and_iff_right hh).trans ⟨fun h1 => ?_, fun ⟨_, h1, h2⟩ v => ?_⟩⟩
  · refine ⟨trivial, hA.1 fun v j => ?_, fun v i j hij => ?_⟩
    · obtain ⟨ph, hp, -⟩ := h1 v
      exact ⟨_, hp j⟩
    · obtain ⟨ph, hp, hi⟩ := h1 v
      by_contra hne
      push Not at hne
      refine hij (hi (MonoidHom.ext fun σ => Units.ext ?_))
      rw [part_val (ha v) (hf v i) (hp i) σ ⟨_, art_unit (ha v) σ⟩ rfl,
        part_val (ha v) (hf v j) (hp j) σ ⟨_, art_unit (ha v) σ⟩ rfl]
      exact hne _
  · choose ph hp using hA.2 h1 v
    refine ⟨ph, hp, fun i j hij => ?_⟩
    by_contra hne
    obtain ⟨y, hy⟩ := h2 v i j hne
    obtain ⟨σ, hσ⟩ := art_onto (ha v) y
    exact hy (by rw [← part_val (ha v) (hf v i) (hp i) σ y hσ, ← part_val (ha v) (hf v j) (hp j) σ y hσ, hij])
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WStmtxx
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Sym.W
open UpperTheory.V.Z.Win UpperTheory.GalN.V
section Loc
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
end Loc
section
variable {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
theorem AdInW.toIn_alt {ι : Qbar l ≃+* ℂ} {M m : ℕ} {r : G L Ω →* GL (Fin 2) (Qbar l)} (h : AdInW ι M m r) : _root_.UpperTheory.V.Z.Sym.AdInAlt ι M m r :=
  ⟨h.cont, _root_.UpperTheory.V.Z.Win.Birth.mkCsdW' h.aut fun _ => h.wit, h.irr, h.gap, h.unr, h.away, h.above⟩
end
structure PureWeightCompatibility : Prop where
  af : _root_.UpperTheory.V.Af.Hypotheses'
  gal : GalUnitaryT
  compat : CompatT
  same : Z.Desc.W.Same
  plain : PlainRec
  desc : Z.Desc.DescUse
def PlainOfAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (w : Plc L) (τ : SmIrr (GL (Fin n) (w.adicCompletion L)))
    (ψ : Fin n → (w.adicCompletion L)ˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → IsSubquotient τ.ρ (prinSeries ψ) →
    (∀ i j, ψ i ≠ ψ j * absPow (w.adicCompletion L) 1) → PT τ
def PsOfAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (w : Plc L) (τ : SmIrr (GL (Fin n) (w.adicCompletion L))), PT τ →
    ∃ ψ : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ Nonempty (τ.ρ.Equiv (prinSeries ψ)) ∧
      ∀ i j, ψ i ≠ ψ j * absPow (w.adicCompletion L) 1
def EigWAlt : Prop :=
  _root_.UpperTheory.V.Af.Hypotheses' → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (n : ℕ) (r : G L Ω →* GL (Fin n) (Qbar l)) (w : Plc L), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal →
    ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w) (a : Weil h →* (w.adicCompletion L)ˣ), IsLocalArtin h a →
    ∀ τ : SmIrr (GL (Fin n) (w.adicCompletion L)), LocGlobT ι r w τ → PT τ →
    ∀ ψ : Fin n → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) → IsSubquotient τ.ρ (prinSeries ψ) →
    ∀ s : Weil h, (r (s : G L Ω)).val.charpoly.map ι.toRingHom =
      psPol ψ (a s)
def AboveWAlt : Prop :=
  _root_.UpperTheory.V.Af.Hypotheses' → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → ∀ (r : G L Ω →* GL (Fin 2) (Qbar l)), Continuous r → ∀ m : ℕ, 2 ≤ m →
    ∀ (w : Plc L), ((l : ℕ) : 𝓞 L) ∈ w.asIdeal → ∀ HT, HasHTAt r HT w → ∀ (A : ValuationSubring Ω), IsPlaceOver A w →
    (∃ (b : ℤ) (k : ℕ) (κ : Fin 2 → ↥(Dec (F := L) A) →* (Qbar l)ˣ), 0 < k ∧ IsFlagOn r (Dec (F := L) A) κ ∧
      ∀ s : ↥(Dec (F := L) A), (s : G L Ω) ∈ Ine (F := L) A →
        κ 0 s ^ k = (cycBar L Ω l s ^ (b + m)) ^ k ∧ κ 1 s ^ k = (cycBar L Ω l s ^ b) ^ k) →
    ∀ τ : SmIrr (GL (Fin 2) (w.adicCompletion L)), LocGlobT ι r w τ → PT τ →
    (∃ ψ : Fin 2 → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ Nonempty (τ.ρ.Equiv (prinSeries ψ)) ∧ NoLk (ψ 0 / ψ 1)) ∧
      ∃ b : ℤ, ∀ j : W.Emb l w, HT (j.1.comp (algebraMap L _)) = {b, b + m}
def AwayWAlt : Prop :=
  _root_.UpperTheory.V.Af.Hypotheses' → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G L Ω →* GL (Fin 2) (Qbar l)), Continuous r → Unlinked (ad0 r) →
    ∀ (w : Plc L), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal → ∀ τ : SmIrr (GL (Fin 2) (w.adicCompletion L)), LocGlobT ι r w τ → PT τ →
    ∃ ψ : Fin 2 → (w.adicCompletion L)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ Nonempty (τ.ρ.Equiv (prinSeries ψ)) ∧ NoLk (ψ 0 / ψ 1)
def GoodWAlt : Prop :=
  _root_.UpperTheory.V.Af.Hypotheses' → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (r : G L Ω →* GL (Fin 2) (Qbar l)) (w : Plc L), ((l : ℕ) : 𝓞 L) ∉ w.asIdeal →
    (∀ A : ValuationSubring Ω, IsPlaceOver A w → ∀ s ∈ Ine (F := L) A, r s = 1) → (∃ s, Ga.FrobAt w s ∧ s ∉ Ga.Bad r) →
    ∀ τ : SmIrr (GL (Fin 2) (w.adicCompletion L)), LocGlobT ι r w τ → PT τ →
    ∃ ψ : Fin 2 → (Kw w)ˣ →* ℂˣ, (∀ i, IsSmoothChar (ψ i)) ∧ Nonempty (τ.ρ.Equiv (prinSeries ψ)) ∧
      (∀ i, ∀ u ∈ Hi.Uo (Kw w), ψ i u = 1) ∧ Reg (ψ 0 / ψ 1)
def LocSubDAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Sig.Lev k)
    (ψ : Fin n → kˣ →* ℂˣ), (∀ i, IsSmoothChar (ψ i)) → ∀ (T : Type) [AddCommGroup T] [Module ℂ T] (τ : Representation ℂ (GL (Fin n) k) T),
    GlobalTheory.PRep.IsSmooth τ → τ.IsIrreducible → ∀ v : T, v ≠ 0 → v ∈ Hi.fixd τ (V.J n) →
    (∀ d, Sig.SDom d → Hi.dc τ (V.J n) (V.J n) (Sig.dg d) v = expo ψ d • v) → IsSubquotient τ (prinSeries ψ)
def GalExWAlt : Prop :=
  _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → Unr L → ∀ n : ℕ, 1 ≤ n → ∀ σ : Submodule ℂ (UA L n → ℂ), IsAutRepU σ →
    ∃ r : G L Ω →* GL (Fin n) (Qbar l), GalT ι σ r ∧
      (IsIrr r → ∃ π : CuspSub L n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ AttC ι r π ∧ Lifts σ π)
def AboveWeightAlt : Prop :=
  _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → ∀ M m : ℕ, M ≠ 0 → l ∣ M → UnrSplit L M → ∀ r : G L Ω →* GL (Fin 2) (Qbar l), AdInW ι M m r →
    ∃ (σ : Submodule ℂ (UA L 2 → ℂ)) (HT : (L →+* Qbar l) → Multiset ℤ), IsAutRepU σ ∧ GalT ι σ r ∧
      (∀ w, IsSplitAt w → ∀ τ, Comp σ w τ → PT τ ∧ HasHTAt r HT w) ∧ (∀ w : Plc L, (M : 𝓞 L) ∉ w.asIdeal → IsUnramU σ w) ∧
      ∀ v : InfinitePlace L, ∃ lam, HasWeightAt σ v.embedding lam ∧ lam.w 0 - lam.w 1 = ((m - 1 : ℕ) : ℤ)
def Branch1WAlt : Prop :=
  _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → Unr L → ∀ M m : ℕ, M ≠ 0 → ∀ (r : G L Ω →* GL (Fin 2) (Qbar l)) (σ : Submodule ℂ (UA L 2 → ℂ)),
    AdInW ι M m r → GalT ι σ r → ∀ P ψ, Ga.GoodSet ι M r σ P ψ → (∀ w ∈ P, Reg (ψ w 0 / ψ w 1)) →
    ∀ σ₃ : Submodule ℂ (UA L 3 → ℂ), IsAutRepU σ₃ → (∀ᶠ w in Filter.cofinite, w ∈ P → CompSub σ₃ w ![ψ w 0 / ψ w 1, 1, (ψ w 0 / ψ w 1)⁻¹]) →
    ∃ π : CuspSub L 3, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ AttC ι (tw (ad0 r) (cycBar L Ω l)⁻¹) π ∧ Lifts σ₃ π
def Branch2WAlt : Prop :=
  _root_.UpperTheory.V.Z.Sym.W.PureWeightCompatibility → ∀ (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), l ≠ 2 → Unr L → ∀ M m : ℕ, M ≠ 0 → ∀ (r : G L Ω →* GL (Fin 2) (Qbar l)) (σ : Submodule ℂ (UA L 2 → ℂ)),
    AdInW ι M m r → GalT ι σ r → ∀ P ψ, Ga.GoodSet ι M r σ P ψ → (∀ w ∈ P, Reg (ψ w 0 / ψ w 1)) →
    ∀ σ' : Submodule ℂ (UA L 2 → ℂ), IsAutRepU σ' →
    (∀ᶠ w in Filter.cofinite, w ∈ P → ∃ ψ', CompSub σ' w ψ' ∧ ψ' 0 / ψ' 1 = (ψ w 0 / ψ w 1) ^ 2) → False
def PlainAtWAlt : Prop :=
  _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (σ : Submodule ℂ (UA L 3 → ℂ)) (π : CuspSub L 3), IsAutRepU σ →
    Lifts σ π → ∀ w, IsSplitAt w → ∀ a : (Kw w)ˣ →* ℂˣ, NoLk a → CompSub σ w ![a, 1, a⁻¹] → ∀ τ, π.IsLocComp w τ → PT τ
end UpperTheory.V.Z.Sym.W
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TAIsoTwOf
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.Zero.LLC UpperTheory.V.Af UpperTheory.V.Z.Gam
open UpperTheory.GalN.V GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HeckeGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Win
private theorem semisimple_conj {Γ k : Type} [Group Γ] [Field k] {n : ℕ} {r r' : Γ →* GL (Fin n) k} (h : RepIso r r')
    (H : IsSSRep r) : IsSSRep r' := by
  obtain ⟨g, hg⟩ := h
  refine GlobalTheory.LatticeComplement.isSSRep_of_intertwine r r' (g : Matrix (Fin n) (Fin n) k)
    ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (Units.mul_inv g) (fun s => ?_) H
  rw [hg s, ← Units.val_mul, ← Units.val_mul]
  congr 1
  group
private theorem attC_conj {F Ω : Type} [Field F] [NumberField F] [_root_.NumberField.IsTotallyComplex F] [Field Ω] [Algebra F Ω] {l : ℕ}
    [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)} {π : CuspSub F n} (h : RepIso r r')
    (H : AttC ι r π) : AttC ι r' π :=
  ⟨semisimple_conj h H.1, H.2.mono fun _ ⟨B, hB, hE⟩ => ⟨B, hB, hE.of_iso h⟩⟩
private theorem tw_tw_inv {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (μ : Γ →* kˣ) :
    tw (tw r μ) μ⁻¹ = r := by
  refine MonoidHom.ext fun s => Units.ext ?_
  rw [tw_val, tw_val, smul_smul, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
    inv_mul_cancel₀ (Units.ne_zero _), one_smul]
private theorem algPos_inv {K : Type} [Field K] [NumberField K] {χ : HChar K} {a : (K →+* ℂ) → ℤ} (h : IsAlgPos χ a) :
    IsAlgPos χ⁻¹ (-a) := fun k hk => by
  have e : (χ⁻¹).inf k = (χ.inf k)⁻¹ := rfl
  rw [e, Units.val_inv_eq_inv_val, h k hk, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun φ _ => (zpow_neg _ _).symm
private theorem regAlg_tw {K : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {a : (K →+* ℂ) → ℤ} (hκ : IsAlgPos κ a) : (CG.mk (P.twist κ)).IsRegAlg := by
  have halg : κ.IsAlg a := fun k => hκ k fun φ => absurd
    (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => Complex.conj_ofReal (φ x))))
    (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk (Complex.ofRealHom.comp φ))))
  refine (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_
  replace h := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).1 h
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 a halg τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + a τ, by push_cast; ring⟩
theorem aIsoTwOf_alt : _root_.UpperTheory.V.Z.Win.AIsoTwOfAlt := by
  intro FL WT _ F Ω _ _ _ _ _ _ l _ ι n r hW
  refine ⟨fun r' hi => ⟨fun v hv h => ?_, fun π hreg ha => ?_⟩, fun μ hμ => ?_⟩
  · exact (((FL F Ω l n r).1 r' hi).2.2 v).2 (hW.1 v hv ((((FL F Ω l n r').1 r hi.symm').2.2 v).1 h))
  · obtain ⟨t, ht⟩ := hW.2 π hreg (attC_conj hi.symm' ha)
    exact ⟨t, fun v hv => ht v (hv.imp id (((FL F Ω l n r').1 r hi.symm').2.2 v).2)⟩
  · obtain ⟨χ, -, art, a, hart, hpos, hL⟩ := hμ
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have e : tw r μ = r := MonoidHom.ext fun s => Units.ext (by ext i; exact i.elim0)
      rw [e]
      exact hW
    have hv : ∀ v, (Unl1 (tw r μ) v → Unl1 r v) ∧ (PotUnl r v → PotUnl (tw r μ) v) ∧ (PotUnl (tw r μ) v → PotUnl r v) := fun v =>
      have h := ((FL F Ω l n r).2.1 μ).2.2 v
      ⟨h.1.2, h.2.1, h.2.2⟩
    refine ⟨fun v hl h => (hv v).2.1 (hW.1 v hl ((hv v).1 h)), fun π' hreg ha => ?_⟩
    have hatt : AttC ι r (π'.twist χ⁻¹) := by
      have h := UpperTheory.V.Af.Cq.attTwist F Ω l ι n (tw r μ) π' ha art χ⁻¹ (-a) μ⁻¹ hart hL.inv
      rwa [tw_tw_inv] at h
    obtain ⟨t, ht⟩ := hW.2 _ (regAlg_tw hreg (algPos_inv hpos)) hatt
    obtain ⟨b, hb⟩ := WT F χ
    refine ⟨t + b, fun v h => ?_⟩
    have h1 := hb n hn _ t v (ht v (h.imp id (hv v).2.2))
    rwa [← CuspSub.twist_mul, inv_mul_cancel, CuspSub.twist_one] at h1
end UpperTheory.V.Z.Win
end
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ExistsRec
noncomputable abbrev UpperTheory.V.Af.Hypotheses'.exists_reciprocity_dense := @UpperTheory.V.Z.Win.exists_rec_alt_alt_alt
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCompEx
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al
theorem UpperTheory.V.Z.Sym.Al.exists_local_component_at_split_of_unitary_aut :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L : Type) [Field L] [NumberField L] [IsCMField L], Unr L → ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA L n → ℂ), IsAutRepU π → ∀ w, IsSplitAt w → ∃ τ, Comp π w τ := by
  intro H L _ _ _ unr n hn π hπ w hw
  obtain ⟨P, hb⟩ := UpperTheory.BaseChangeIdentities.splitComp
    (_root_.UpperTheory.BaseChangeIdentities.bcSpeh_alt (_root_.UpperTheory.BaseChangeIdentities.bridge H.aut.bc H.loc.bern)) L unr n hn π hπ
  exact ⟨P w hw, hb w hw⟩
end
end
