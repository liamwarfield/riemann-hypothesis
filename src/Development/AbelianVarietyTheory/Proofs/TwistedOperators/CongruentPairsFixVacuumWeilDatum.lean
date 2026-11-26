module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankCol
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodGroupsReduceSplitPlaceFamilySucc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawDoubleStepIntegrandVanishesOffBessel
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLevelElementOffPlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruentPairsFixVacuumWeilDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruentPairsFixVacuumWeilDatum
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

open scoped Topology

noncomputable section

namespace GlobalTheory.VacFixPair

theorem om_pow_eq {D : D7} {S V : HSp D} (om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ))
    (g : GA D S × GA D V) (f : WO S V → ℂ) (c : ℂ) (hc : om g f = c • f) : ∀ m : ℕ, om (g ^ m) f = c ^ m • f := by
  intro m
  induction m with
  | zero => rw [pow_zero, pow_zero, map_one, Module.End.one_apply, one_smul]
  | succ m ih =>
    rw [pow_succ, map_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ, mul_comm]


set_option maxHeartbeats 1000000 in
theorem pair_fix_vacO : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → IsWeilDatumO ψ S T χS χT om →
    ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Member.FinCong S N k → GlobalTheory.Member.FinCong T N k' → om (k, k') v = v := by
  intro D ψ θ S T sS sT ΛS ΛT v χS χT om hvac hsdS hsdT hcS hcT hW
  have hθ : IsInfFam θ := hvac.2.inf
  have hev := (GlobalTheory.LatNhds.eventually_actO D S T ΛS ΛT hsdS hsdT
    (GlobalTheory.LatFinGen.latO_finitely_generated D S T ΛS ΛT hsdS hsdT)).1
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℕ, ∀ x ∈ GfC S, ∀ x' ∈ GfC T, GlobalTheory.Member.FinCong S n.factorial x →
      GlobalTheory.Member.FinCong T n.factorial x' →
      ∀ u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        actO S T x x' u ∈
          (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
    by_contra hne
    push_neg at hne
    choose k hk k' hk' hkc hkc' u hu hu' using hne
    have ht : Filter.Tendsto (fun n => ((k n, k' n) : GA D S × GA D T)) Filter.atTop (𝓝 1) :=
      (GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong hk hkc).prodMk_nhds
        (GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong hk' hkc')
    obtain ⟨n, hn⟩ := (ht.eventually hev).exists
    exact hu' n (hn _ (hu n))
  have hscal : ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Member.FinCong S n₁.factorial k →
      GlobalTheory.Member.FinCong T n₁.factorial k' → ∃ c : ℂ, ‖c‖ = 1 ∧ om (k, k') v = c • v := by
    intro k hk k' hk' hc hc'
    have hΛ : ∀ u : WO S T, u ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E))
        (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO S T
        (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True),
        u = actO S T k k' u₀ := by
      intro u
      constructor
      · intro hu
        refine ⟨actO S T k⁻¹ k'⁻¹ u, hn₁ k⁻¹ (inv_mem hk) k'⁻¹ (inv_mem hk')
          (GlobalTheory.Member.PrincLevel.finCong_inv hc) (GlobalTheory.Member.PrincLevel.finCong_inv hc') u hu, ?_⟩
        have := GlobalTheory.WeilVacMove.actO_inv_actO k⁻¹ k'⁻¹ u
        rw [inv_inv, inv_inv] at this
        exact this.symm
      · rintro ⟨u₀, hu₀, rfl⟩
        exact hn₁ k hk k' hk' hc hc' u₀ hu₀
    have hvac' := GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ
      sS sS sT sT _ _ _ _ k k'
      (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S hk τ, Matrix.one_mul, Matrix.mul_one])
      (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hk' τ, Matrix.one_mul, Matrix.mul_one]) hΛ v hvac
    exact GlobalTheory.VacUnique.vacUniqueO D ψ θ hvac.1 hθ (Formalism.L2.Fam.ThC.fixSig S) (Formalism.L2.Fam.ThC.fixSig T)
      sS sT (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _) hcS hcT ΛS ΛT
      hsdS hsdT v _ (GlobalTheory.VacFixTarget.isVacO_fixSig hvac) (GlobalTheory.VacFixTarget.isVacO_fixSig hvac')
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hvac
  have hcont : Continuous fun p : GA D S × GA D T => om p v w₀ := hW.om_cont _ hvac.2.theta w₀
  have key : ∃ n : ℕ, ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Member.FinCong S (n₁.factorial * n.factorial) k →
      GlobalTheory.Member.FinCong T (n₁.factorial * n.factorial) k' → om (k, k') v = v := by
    by_contra hne
    push_neg at hne
    choose k hk k' hk' hkc hkc' hkne using hne
    have hpow : ∀ n, ∃ m : ℕ, ∃ c : ℂ, om (k n ^ m, k' n ^ m) v = c • v ∧ ¬ ‖c - 1‖ ≤ 1 / 2 := by
      intro n
      obtain ⟨c, -, hc⟩ := hscal (k n) (hk n) (k' n) (hk' n) (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc n))
        (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc' n))
      have hc1 : c ≠ 1 := by
        rintro rfl
        exact hkne n (by rw [hc, one_smul])
      by_contra h
      push_neg at h
      exact hc1 (GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le (A := ℂ) fun m =>
        h m (c ^ m) (by rw [← Prod.pow_mk]; exact om_pow_eq om _ v c hc m))
    choose m c hmc hc using hpow
    have hmem : ∀ n, k n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup S (n₁.factorial * n.factorial) :=
      fun n => pow_mem (show k n ∈ GlobalTheory.Member.PrincLevel.levelGroup S (n₁.factorial * n.factorial) from ⟨hk n, hkc n⟩) _
    have hmem' : ∀ n, k' n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup T (n₁.factorial * n.factorial) :=
      fun n => pow_mem (show k' n ∈ GlobalTheory.Member.PrincLevel.levelGroup T (n₁.factorial * n.factorial) from ⟨hk' n, hkc' n⟩) _
    have ht : Filter.Tendsto (fun n => ((k n ^ m n, k' n ^ m n) : GA D S × GA D T)) Filter.atTop (𝓝 1) :=
      (GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k n ^ m n) (fun n => (hmem n).1)
        (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem n).2)).prodMk_nhds
      (GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k' n ^ m n) (fun n => (hmem' n).1)
        (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem' n).2))
    have e1 : om (1 : GA D S × GA D T) v w₀ = v w₀ := by
      rw [map_one]
      rfl
    have h2 : Filter.Tendsto (fun n => om (k n ^ m n, k' n ^ m n) v w₀) Filter.atTop (𝓝 (v w₀)) := by
      have := (hcont.tendsto 1).comp ht
      rw [← e1]
      exact this
    have hpos : 0 < ‖v w₀‖ / 2 := half_pos (norm_pos_iff.2 hw₀)
    obtain ⟨n, hn⟩ := (h2.eventually (Metric.ball_mem_nhds _ hpos)).exists
    rw [hmc n, Pi.smul_apply, smul_eq_mul, dist_eq_norm, ← sub_one_mul, norm_mul] at hn
    have := hc n
    push_neg at this
    nlinarith [norm_nonneg (v w₀)]
  obtain ⟨n, hn⟩ := key
  exact ⟨n₁.factorial * n.factorial, Nat.mul_pos n₁.factorial_pos n.factorial_pos,
    fun k hk k' hk' hc hc' => hn k hk k' hk' hc hc'⟩

end GlobalTheory.VacFixPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruentPairsFixVacuumWeilDatumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruent_pairs_fix_vacuum_weilDatum : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    (∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → IsWeilDatumO ψ S T χS χT om →
    ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Member.FinCong S N k → GlobalTheory.Member.FinCong T N k' → om (k, k') v = v := by
  first | exact @GlobalTheory.VacFixPair.pair_fix_vacO | exact GlobalTheory.VacFixPair.pair_fix_vacO | (intros; apply GlobalTheory.VacFixPair.pair_fix_vacO <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneCosetDecompositionStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OfMulTrivialAtPlacesSubset
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OfMulTrivialAtPlacesSubset
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.CondCut

variable {D : D7}

theorem idOff_sub {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ v, Q v → P v) {a : AE D} (ha : a ∈ idOff D P) : a ∈ idOff D Q := by
  unfold GlobalTheory.FinPl.idOff at ha ⊢
  rw [Submodule.mem_iInf] at ha ⊢
  exact fun w => ha ⟨w.1, h w.1 w.2⟩

theorem idAt_sup {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ v, Q v → P v) {a : AE D} (ha : a ∈ idAt D Q) : a ∈ idAt D P := by
  unfold GlobalTheory.FinPl.idAt at ha ⊢
  obtain ⟨h0, hw⟩ := Ideal.mem_inf.1 ha
  refine Ideal.mem_inf.2 ⟨h0, ?_⟩
  rw [Submodule.mem_iInf] at hw ⊢
  exact fun w => hw ⟨w.1, fun hq => w.2 (h w.1 hq)⟩

theorem mt_mul_of_grpOff {W : HSp D} {Q : GlobalTheory.FinPl.Pl D → Prop} {b : GA D W} (hb : b ∈ grpOff W Q) {k : ℕ}
    (M : Matrix (Fin W.rank) (Fin k) (AE D)) (hM : ∀ i j, M i j ∈ idAt D Q) : mt W b * M = M := by
  have hb' := (GlobalTheory.FinPlLoc.mem_congGrp _ b).1 hb
  have key : (mt W b - 1) * M = 0 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    have h1 := (GlobalTheory.FinPlLoc.mem_idOff_iff Q _).1 (hb' i l)
    have h2 := (GlobalTheory.FinPlLoc.mem_idAt_iff Q _).1 (hM l j)
    rw [Matrix.sub_apply, ← h2]
    calc (mt W b i l - (1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) i l) * (GlobalTheory.FinPlLoc.idem D Q * M l j)
        = (GlobalTheory.FinPlLoc.idem D Q * (mt W b i l - (1 : Matrix (Fin W.rank) (Fin W.rank) (AE D)) i l)) * M l j := by ring
      _ = 0 := by rw [h1, zero_mul]
  rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at key
  exact key

theorem mul_mem_idAt {Q : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} (A : Matrix (Fin m) (Fin n) (AE D))
    (B : Matrix (Fin n) (Fin k) (AE D)) (hB : ∀ i j, B i j ∈ idAt D Q) (i : Fin m) (j : Fin k) : (A * B) i j ∈ idAt D Q := by
  rw [Matrix.mul_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hB l j)

end GlobalTheory.AscFin.CondCut


open GlobalTheory.AscFin.CondCut in
theorem GlobalTheory.AscFin.Cond.of_mul_grpOff : ∀ {D : D7} {V₀ W W₀ : HSp D} {ρ σ : ℕ} (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (ψ : AddChar (AF D.host.F) ℂ) (P Q : GlobalTheory.FinPl.Pl D → Prop) (g₁ g₂ : GA D W), (∀ v, Q v → P v) → g₁ ∈ grpAt W Q → g₂ ∈ grpOff W Q → g₁ * g₂ = g₂ * g₁ → Cond dW p x y ψ P (g₁ * g₂) → Cond dW p x y ψ Q g₁ := by
  intro D V₀ W W₀ ρ σ dW p x y ψ P Q g₁ g₂ hQP _hg₁ hg₂ _hcomm H
  have hg₂i : g₂⁻¹ ∈ grpOff W Q := inv_mem hg₂
  have emt : ∀ {k : ℕ} (M : Matrix (Fin W.rank) (Fin k) (AE D)),
      mt W (g₁ * g₂)⁻¹ * M = mt W g₂⁻¹ * (mt W g₁⁻¹ * M) := by
    intro k M
    rw [_root_.mul_inv_rev]
    exact Matrix.mul_assoc _ _ _
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨u, a, ha, hoff⟩ := H.pt
    refine ⟨u, a, ha, fun i j => ?_⟩
    have h1 := idOff_sub hQP (hoff i j)
    have h2 : (((mt W g₂⁻¹ - 1) * (mt W g₁⁻¹ * (x * u.1.1)) : Matrix (Fin W.rank) (Fin ρ) (AE D))) i j ∈ idOff D Q := by
      rw [Matrix.mul_apply]
      exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (by
        rw [Matrix.sub_apply]; exact (GlobalTheory.FinPlLoc.mem_congGrp _ _).1 hg₂i i l)
    have e : mt W g₁⁻¹ * (x * u.1.1) - x - a =
        (mt W (g₁ * g₂)⁻¹ * (x * u.1.1) - x - a) - (mt W g₂⁻¹ - 1) * (mt W g₁⁻¹ * (x * u.1.1)) := by
      rw [emt, Matrix.sub_mul, Matrix.one_mul]; abel
    rw [e, Matrix.sub_apply]
    exact sub_mem h1 h2
  · intro N hN hlow hA
    refine H.shift N (fun i j => idAt_sup hQP (hN i j)) hlow ?_
    rw [emt, mt_mul_of_grpOff hg₂i _ (mul_mem_idAt _ _ (mul_mem_idAt _ _ hN))]
    exact hA
  · intro ξ hξ ξ' hξQ he
    refine H.iso ξ hξ ξ' (fun i j => idAt_sup hQP (hξQ i j)) ?_
    have hinc : ∀ i j, (dW.incX V₀ ξ) i j ∈ idAt D Q := mul_mem_idAt _ _ hξQ
    show mt W g₁ * mt W g₂ * dW.incX V₀ ξ = _
    rw [Matrix.mul_assoc, mt_mul_of_grpOff hg₂ _ hinc]
    exact he

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OfMulTrivialAtPlacesSubsetStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.of_mul_trivialAtPlaces_subset : ∀ {D : D7} {V₀ W W₀ : HSp D} {ρ σ : ℕ} (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (ψ : AddChar (AF D.host.F) ℂ) (P Q : GlobalTheory.FinPl.Pl D → Prop) (g₁ g₂ : GA D W), (∀ v, Q v → P v) → g₁ ∈ grpAt W Q → g₂ ∈ grpOff W Q → g₁ * g₂ = g₂ * g₁ → Cond dW p x y ψ P (g₁ * g₂) → Cond dW p x y ψ Q g₁ := by
  first | exact @GlobalTheory.AscFin.Cond.of_mul_grpOff | exact GlobalTheory.AscFin.Cond.of_mul_grpOff | (intros; apply GlobalTheory.AscFin.Cond.of_mul_grpOff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneCosetDecompositionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

namespace GlobalTheory.CosetFJ

variable {D : D7}

theorem coset_of_places {V₀ W W₀ : HSp D} {ρ σ : ℕ} (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ)
    (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (ψ : AddChar (AF D.host.F) ℂ) (K : Subgroup (GA D W))
    (S : Finset (GlobalTheory.FinPl.Pl D)) :
    (∀ v ∈ S, ∀ g ∈ grpAt W (· = v), Cond dW p x y ψ (· = v) g →
      ∃ r ∈ Rgrp W x, r ∈ grpAt W (· = v) ∧ ∃ k ∈ K, k ∈ grpAt W (· = v) ∧ g = r * k) →
    ∀ g ∈ grpAt W (· ∈ S), Cond dW p x y ψ (· ∈ S) g →
      ∃ r ∈ Rgrp W x, r ∈ grpAt W (· ∈ S) ∧ ∃ k ∈ K, k ∈ grpAt W (· ∈ S) ∧ g = r * k := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _ g hg _
    have e : g = 1 := GlobalTheory.QRed.grpAt_eq_one (fun v => by simp) hg
    exact ⟨1, one_mem _, one_mem _, 1, one_mem _, one_mem _, by rw [e, one_mul]⟩
  | insert v s hv ih =>
    intro hloc g hg hc
    obtain ⟨g₁, hg₁, g₂, hg₂o, rfl⟩ := ((GlobalTheory.FinPl.localComponents D (· = v)).2 W).1 g
    have mono : ∀ {P : GlobalTheory.FinPl.Pl D → Prop} {a : GA D W}, (∀ w, P w → w ∈ insert v s) → a ∈ grpAt W P →
        a ∈ grpAt W (· ∈ insert v s) := fun hP ha => GlobalTheory.DStepSuppSecond.grpAt_mono hP ha
    have hg₁' : g₁ ∈ grpAt W (· ∈ insert v s) := mono (fun w hw => by simp [hw]) hg₁
    have hg₂ : g₂ ∈ grpAt W (· ∈ insert v s) := by
      have := mul_mem (inv_mem hg₁') hg
      rwa [inv_mul_cancel_left] at this
    have hg₂s : g₂ ∈ grpAt W (· ∈ s) :=
      GlobalTheory.QRed.grpAt_of_off (fun w hw => by rcases Finset.mem_insert.1 hw with h | h; exacts [Or.inl h.symm, Or.inr h])
        hg₂ hg₂o
    have hcomm : g₁ * g₂ = g₂ * g₁ := ((GlobalTheory.FinPl.localComponents D (· = v)).2 W).2.1 g₁ hg₁ g₂ hg₂o
    have hdisj : ∀ w, w = v → ¬ w ∈ s := fun w hw hws => hv (hw ▸ hws)
    have hg₁o : g₁ ∈ grpOff W (· ∈ s) := GlobalTheory.QRed.grpAt_off hdisj hg₁
    have hc₁ := GlobalTheory.T.of_mul_trivialAtPlaces_subset dW p x y ψ _ _ g₁ g₂ (fun w hw => by simp [hw]) hg₁ hg₂o hcomm hc
    have hc₂ := GlobalTheory.T.of_mul_trivialAtPlaces_subset dW p x y ψ _ _ g₂ g₁ (fun w hw => Finset.mem_insert_of_mem hw) hg₂s hg₁o hcomm.symm
      (hcomm ▸ hc)
    obtain ⟨r₁, hr₁, hr₁a, k₁, hk₁, hk₁a, e₁⟩ := hloc v (Finset.mem_insert_self v s) g₁ hg₁ hc₁
    obtain ⟨r₂, hr₂, hr₂a, k₂, hk₂, hk₂a, e₂⟩ :=
      ih (fun w hw => hloc w (Finset.mem_insert_of_mem hw)) g₂ hg₂s hc₂
    have hk₁r₂ : k₁ * r₂ = r₂ * k₁ := GlobalTheory.SeeSawLastValue.grpAt_comm hdisj hk₁a hr₂a
    refine ⟨r₁ * r₂, mul_mem hr₁ hr₂, mul_mem (mono (fun w hw => by simp [hw]) hr₁a)
      (mono (fun w hw => Finset.mem_insert_of_mem hw) hr₂a), k₁ * k₂, mul_mem hk₁ hk₂,
      mul_mem (mono (fun w hw => by simp [hw]) hk₁a) (mono (fun w hw => Finset.mem_insert_of_mem hw) hk₂a), ?_⟩
    rw [e₁, e₂]
    calc r₁ * k₁ * (r₂ * k₂) = r₁ * (k₁ * r₂) * k₂ := by simp only [mul_assoc]
      _ = r₁ * r₂ * (k₁ * k₂) := by rw [hk₁r₂]; simp only [mul_assoc]

theorem one_coset_decomposition_base : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ g ∈ grpAt _ (fun v => v ∈ G.pl.S0), Cond (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (fun v => v ∈ G.pl.S0) g → ∃ r ∈ Rgrp _ (xFB F σ h'), r ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ ∃ k ∈ lev G (.grid (2 * σ + 2) 0), k ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ g = r * k := by
  intro D hD T L μ0 hL sc G W M hM F _hF σ h h' g hg hc
  refine coset_of_places (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (lev G (.grid (2 * σ + 2) 0)) G.pl.S0 ?_ g hg hc
  intro v hv g hg hc
  obtain ⟨u, a, ha, hoff⟩ := hc.pt
  obtain ⟨k, hk, hka, hk'⟩ := GlobalTheory.T.exists_level_element_off_place D hD T L μ0 hL sc G W M hM F _hF σ h h' v hv g hg u a ha hoff
  obtain ⟨r, hr, hra, e⟩ := GlobalTheory.T.exists_unitriangularStabilizer_of_principal_move _ (xFB F σ h') (· = v) g k u hg hka hk'
  exact ⟨r, hr, hra, k⁻¹, inv_mem hk, inv_mem hka, e⟩

end GlobalTheory.CosetFJ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneCosetDecompositionStatementStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_coset_decomposition_statement : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ g ∈ grpAt _ (fun v => v ∈ G.pl.S0), Cond (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (fun v => v ∈ G.pl.S0) g → ∃ r ∈ Rgrp _ (xFB F σ h'), r ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ ∃ k ∈ lev G (.grid (2 * σ + 2) 0), k ∈ grpAt _ (fun v => v ∈ G.pl.S0) ∧ g = r * k := by
  first | exact @GlobalTheory.CosetFJ.one_coset_decomposition_base | exact GlobalTheory.CosetFJ.one_coset_decomposition_base | (intros; apply GlobalTheory.CosetFJ.one_coset_decomposition_base <;> assumption)
end
end
