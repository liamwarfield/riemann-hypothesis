module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SpanKeep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ScMemIff

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CommonEigenvalueSecond
theorem UpperTheory.Reformulated.B.ComplexCommonEigenvectorOfFinrankEq.common_eig :
    ∀ {ι M : Type} [inst : AddCommGroup M]
    [inst_1 : _root_.Module ℂ M] [FiniteDimensional ℂ M] (f : ι → Module.End ℂ M),
    (∀ (i j : ι), Commute (f i) (f j)) →
      ∀ (n : ℕ) (W : Submodule ℂ M),
        Module.finrank ℂ ↥W = n →
          W ≠ ⊥ →
            (∀ (i : ι), ∀ x ∈ W, (f i : M → M) x ∈ W) →
              ∃ v ∈ W, v ≠ (0 : M) ∧ ∀ (i : ι), ∃ (c : ℂ), (f i : M → M) v = c • v := by
  intro ι M _ _ _ f hc n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro W hn hW hinv
  by_cases h : ∀ i, ∃ c : ℂ, ∀ x ∈ W, f i x = c • x
  · obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).1 hW
    exact ⟨v, hv, hv0, fun i => (h i).imp fun c hc' => hc' v hv⟩
  · obtain ⟨i, hi⟩ := not_forall.1 h
    haveI : Nontrivial W := Submodule.nontrivial_iff_ne_bot.2 hW
    obtain ⟨c, hce⟩ := Module.End.exists_eigenvalue
      ((f i).restrict (p := W) (q := W) (hinv i) : Module.End ℂ W)
    obtain ⟨w, hw⟩ := hce.exists_hasEigenvector
    have hw1 : f i (w : M) = c • (w : M) := congrArg Subtype.val hw.apply_eq_smul
    have hw0 : (w : M) ≠ 0 := fun e => hw.2 (Subtype.ext e)
    have hlt : W ⊓ (f i).eigenspace c < W := by
      refine lt_of_le_of_ne inf_le_left fun e => hi ⟨c, fun x hx => ?_⟩
      rw [← e] at hx
      exact Module.End.mem_eigenspace_iff.1 hx.2
    have hne : W ⊓ (f i).eigenspace c ≠ ⊥ :=
      (Submodule.ne_bot_iff _).2 ⟨w, ⟨w.2, Module.End.mem_eigenspace_iff.2 hw1⟩, hw0⟩
    obtain ⟨v, hv, hv0, hall⟩ := ih _ (hn ▸ Submodule.finrank_lt_finrank_of_lt hlt)
      (W ⊓ (f i).eigenspace c) rfl hne (fun j x hx => by
        refine ⟨hinv j x hx.1, Module.End.mem_eigenspace_iff.2 ?_⟩
        have h1 : f i x = c • x := Module.End.mem_eigenspace_iff.1 hx.2
        have h2 : f i (f j x) = f j (f i x) := LinearMap.congr_fun (hc i j).eq x
        rw [h2, h1, map_smul])
    exact ⟨v, hv.1, hv0, hall⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.SecMemLev
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

section SlopeTestRemainingChoices

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

private theorem away_one {w : Plc L} {y : UA L n} (hy : y ∈ away n w) : cLoc w y = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hy w) rfl)

private theorem finOrb (w : Plc L) (x : GL (Fin n) (Kw w)) :
    UpperTheory.V.AlgebraTools.FinOrb ((iw w).J n) ((iw w).J n) x :=
  ((Sig.finFacts _ (iw w)).2.2.2.2.2 n).1 x

private theorem sec_mem_lev {U : Subgroup (UA L n)} {S : Finset (Plc L)} (hP : Places (S : Set (Plc L)))
    (hS : ∀ w ∈ S, locU n w ⊓ Kall L n ≤ U) {w : Plc L} (hw : w ∈ S) {j : GL (Fin n) (Kw w)}
    (hj : j ∈ (iw w).J n) : secW n w j ∈ lev U S iw := by
  obtain ⟨h1, h2, -, -⟩ := secSpec L n w (hP.split w (Finset.mem_coe.2 hw))
  have hK : secW n w j ∈ Kall L n := ((factor L n w).2.2.2.2.1 _ (h1 j)).2 (by
    have hKO : GlobalTheory.SplitWeil.KO (w.adicCompletion L) (Fin n) = GlobalTheory.LFun.KGL w (n := n) := GlobalTheory.SmGL.SphCompletion.KO_completion w n
    rw [h2, ← hKO]
    exact ((Sig.finFacts _ (iw w)).2.2.2.2.2 n).2.2.2 hj)
  refine Subgroup.mem_inf.2 ⟨hS w hw ⟨h1 j, hK⟩, ?_⟩
  refine Subgroup.mem_iInf.2 fun w' => Subgroup.mem_iInf.2 fun hw' => ?_
  rw [Subgroup.mem_comap]
  by_cases e : w' = w
  · subst e
    rw [h2]
    exact hj
  · have hne : w.under (𝓞 (Lp L)) ≠ w'.under (𝓞 (Lp L)) := fun h =>
      e (hP.inj (Finset.mem_coe.2 hw') (Finset.mem_coe.2 hw) h.symm)
    rw [away_one ((factor L n w').2.2.1 w hne (h1 j))]
    exact one_mem _

private theorem op_inSpan {w : Plc L} (hw : IsSplitAt w) (d : Fin n → (Kw w)ˣ) (φ : UA L n → V) :
    InSpan w φ (op w (iw w) d φ) := by
  haveI : Finite (MulAction.orbit ((iw w).J n) ((Sig.dg d : GL (Fin n) (Kw w)) : GL (Fin n) (Kw w) ⧸ (iw w).J n)) :=
    finOrb w _
  haveI := Fintype.ofFinite (MulAction.orbit ((iw w).J n) ((Sig.dg d : GL (Fin n) (Kw w)) : GL (Fin n) (Kw w) ⧸ (iw w).J n))
  simp only [InSpan, op, UpperTheory.V.Hi.dc, finsum_eq_sum_of_fintype, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun q _ => Submodule.subset_span
    ⟨secW n w (q : GL (Fin n) (Kw w) ⧸ (iw w).J n).out, (secSpec L n w hw).1 _, rfl⟩

private theorem fix_of_AF {R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V} {U : Subgroup (UA L n)}
    {S : Finset (Plc L)} (hP : Places (S : Set (Plc L))) (hS : ∀ w ∈ S, locU n w ⊓ Kall L n ≤ U)
    {w : Plc L} (hw : w ∈ S) {φ : UA L n → V} (hφ : IsAF R (lev U S iw) φ) :
    φ ∈ UpperTheory.V.Hi.fixd ((rightReg ℂ (UA L n) V).comp (secW n w)) ((iw w).J n) := fun j hj =>
  funext fun g => hφ.level _ (sec_mem_lev hP hS hw hj) g

private theorem hk_val {w : Plc L} (x : GL (Fin n) (Kw w))
    (v : UpperTheory.V.Hi.fixd ((rightReg ℂ (UA L n) V).comp (secW n w)) ((iw w).J n)) :
    (UpperTheory.V.AlgebraTools.hk ((rightReg ℂ (UA L n) V).comp (secW n w)) ((iw w).J n) x v : UA L n → V) =
      UpperTheory.V.Hi.dc ((rightReg ℂ (UA L n) V).comp (secW n w)) ((iw w).J n) ((iw w).J n) x v :=
  (UpperTheory.V.AlgebraTools.hkApply ℂ _ _ _ _ _ x (finOrb w x)).1 v

private theorem op_keep {R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V} {U : Subgroup (UA L n)}
    {S : Finset (Plc L)} (hP : Places (S : Set (Plc L))) (hS : ∀ w ∈ S, locU n w ⊓ Kall L n ≤ U)
    {w : Plc L} (hw : w ∈ S) (d : Fin n → (Kw w)ˣ) {φ : UA L n → V} (hφ : IsAF R (lev U S iw) φ) :
    IsAF R (lev U S iw) (op w (iw w) d φ) := by
  have hsp := hP.split w (Finset.mem_coe.2 hw)
  obtain ⟨-, hc, hsec, -⟩ := secSpec L n w hsp
  have hA : IsAF R (lev U S iw ⊓ away n w) φ :=
    ⟨hφ.left, hφ.inf, fun u hu g => hφ.level u hu.1 g⟩
  have hB := (spanKeep L n V w φ _ (op_inSpan hsp d φ)).2.1 R _ inf_le_right hA
  have hfix : op w (iw w) d φ ∈ UpperTheory.V.Hi.fixd ((rightReg ℂ (UA L n) V).comp (secW n w)) ((iw w).J n) := by
    have h := (UpperTheory.V.AlgebraTools.hk ((rightReg ℂ (UA L n) V).comp (secW n w)) ((iw w).J n) (Sig.dg d)
      ⟨φ, fix_of_AF hP hS hw hφ⟩).2
    rwa [hk_val] at h
  refine ⟨hB.left, hB.inf, fun a ha g => ?_⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := (factor L n w).2.1 a
  have hxJ : cLoc w x ∈ (iw w).J n := by
    have h : cLoc w (x * y) ∈ (iw w).J n :=
      Subgroup.mem_comap.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 ha.2 w) hw)
    rwa [map_mul, away_one hy, mul_one] at h
  have hxA : x ∈ lev U S iw := by
    have h := sec_mem_lev hP hS hw hxJ
    rwa [hsec x hx] at h
  have hyA : y ∈ lev U S iw ⊓ away n w :=
    ⟨by simpa using mul_mem (inv_mem hxA) ha, hy⟩
  rw [← mul_assoc, hB.level y hyA]
  have h := congrFun (hfix _ hxJ) g
  rw [← hsec x hx]
  exact h

private theorem op_comm {w w' : Plc L} (hw : IsSplitAt w) (hw' : IsSplitAt w')
    (hne : w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L))) (d : Fin n → (Kw w)ˣ) (d' : Fin n → (Kw w')ˣ) :
    Commute (op (V := V) w (iw w) d) (op (V := V) w' (iw w') d') := by
  haveI : Finite (MulAction.orbit ((iw w).J n) ((Sig.dg d : GL (Fin n) (Kw w)) : GL (Fin n) (Kw w) ⧸ (iw w).J n)) :=
    finOrb w _
  haveI := Fintype.ofFinite (MulAction.orbit ((iw w).J n) ((Sig.dg d : GL (Fin n) (Kw w)) : GL (Fin n) (Kw w) ⧸ (iw w).J n))
  haveI : Finite (MulAction.orbit ((iw w').J n) ((Sig.dg d' : GL (Fin n) (Kw w')) : GL (Fin n) (Kw w') ⧸ (iw w').J n)) :=
    finOrb w' _
  haveI := Fintype.ofFinite (MulAction.orbit ((iw w').J n) ((Sig.dg d' : GL (Fin n) (Kw w')) : GL (Fin n) (Kw w') ⧸ (iw w').J n))
  simp only [op, UpperTheory.V.Hi.dc, finsum_eq_sum_of_fintype]
  refine Commute.sum_left _ _ _ fun q _ => Commute.sum_right _ _ _ fun q' _ => ?_
  have hc := (factor L n w).1 _ ((secSpec L n w hw).1 (q : GL (Fin n) (Kw w) ⧸ (iw w).J n).out) _
    ((factor L n w).2.2.1 w' hne ((secSpec L n w' hw').1 (q' : GL (Fin n) (Kw w') ⧸ (iw w').J n).out))
  show _ * _ = _ * _
  simp only [MonoidHom.comp_apply]
  rw [← map_mul, ← map_mul, hc]

private theorem op_unit {R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V} {U : Subgroup (UA L n)}
    {S : Finset (Plc L)} (hP : Places (S : Set (Plc L))) (hS : ∀ w ∈ S, locU n w ⊓ Kall L n ≤ U)
    {w : Plc L} (hw : w ∈ S) (d : Fin n → (Kw w)ˣ) (hd : ∀ i, d i ∈ UpperTheory.V.Hi.Uo (Kw w))
    {φ : UA L n → V} (hφ : IsAF R (lev U S iw) φ) : op w (iw w) d φ = φ := by
  have hmem : Sig.dg d ∈ (iw w).J n :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_map.2 ⟨d, fun i _ => hd i, rfl⟩))
  have hf : UpperTheory.V.AlgebraTools.FinOrb ((iw w).J n) ((iw w).J n) (1 : GL (Fin n) (Kw w)) := finOrb w 1
  set ρ := (rightReg ℂ (UA L n) V).comp (secW n w) with hρ
  have e1 := (UpperTheory.V.AlgebraTools.hkApply ℂ _ _ ρ _ _ 1 hf).2.2 (Sig.dg d) hmem 1 (one_mem _)
  have e2 := (UpperTheory.V.AlgebraTools.hkApply ℂ _ _ ρ _ _ 1 hf).2.1 {1}
    (fun y hy => by
      rw [Finset.mem_singleton.1 hy]
      exact MulAction.mem_orbit_self _)
    (fun q hq => by
      obtain ⟨a, rfl⟩ := hq
      refine ⟨1, ⟨Finset.mem_singleton_self _, ?_⟩, fun y hy => Finset.mem_singleton.1 hy.1⟩
      exact (QuotientGroup.eq.2 (by simpa using a.2))) ⟨φ, fix_of_AF hP hS hw hφ⟩
  have e3 := (UpperTheory.V.AlgebraTools.hkApply ℂ _ _ ρ _ _ (Sig.dg d) (finOrb w _)).1 ⟨φ, fix_of_AF hP hS hw hφ⟩
  rw [mul_one, mul_one] at e1
  rw [e1, e2] at e3
  simpa using e3.symm

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.Sym.Al.afOps :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin n) ℂ) V) (U : Subgroup (UA L n)), U ≤ Kall L n → ∀ S : Finset (Plc L), Places (S : Set (Plc L)) →
        (∀ w ∈ S, locU n w ⊓ Kall L n ≤ U) →
        ∃ u : ∀ w : Plc L, (Fin n → (Kw w)ˣ) → Module.End ℂ (AF R (lev U S iw)),
          (∀ w ∈ S, ∀ d, AlgebraTools.Dom d → ∀ φ, ((u w d φ : AF R (lev U S iw)) : UA L n → V) = op w (iw w) d φ) ∧
          (∀ w ∈ S, ∀ d d', AlgebraTools.Dom d → AlgebraTools.Dom d' → u w (d * d') = u w d * u w d') ∧
          (∀ w ∈ S, ∀ d, (∀ i, d i ∈ Hi.Uo (Kw w)) → u w d = 1) ∧
          ∀ w ∈ S, ∀ w' ∈ S, w ≠ w' → ∀ d d', AlgebraTools.Dom d → AlgebraTools.Dom d' → Commute (u w d) (u w' d') := by
  intro L _ _ _ n V _ _ R U _ S hP hS
  classical
  let u : ∀ w : Plc L, (Fin n → (Kw w)ˣ) → Module.End ℂ (AF R (lev U S iw)) := fun w d =>
    if hw : w ∈ S then (op w (iw w) d).restrict (fun _ hφ => op_keep hP hS hw d hφ) else 0
  have hu : ∀ w, w ∈ S → ∀ d (φ : AF R (lev U S iw)),
      ((u w d φ : AF R (lev U S iw)) : UA L n → V) = op w (iw w) d φ := by
    intro w hw d φ
    simp only [u, dif_pos hw]
    rfl
  refine ⟨u, fun w hw d _ φ => hu w hw d φ, fun w hw d d' hd hd' => ?_, fun w hw d hd => ?_,
    fun w hw w' hw' hne d d' _ _ => ?_⟩
  · refine LinearMap.ext fun φ => Subtype.ext ?_
    rw [hu w hw, Module.End.mul_apply, hu w hw, hu w hw]
    have h := congrArg Subtype.val (LinearMap.congr_fun
      ((Sig.hkMul (Kw w) (iw w) n (UA L n → V) ((rightReg ℂ (UA L n) V).comp (secW n w))).1 d d' hd hd')
      ⟨φ.1, fix_of_AF hP hS hw φ.2⟩)
    rw [Module.End.mul_apply, hk_val, hk_val, hk_val] at h
    exact h.symm
  · refine LinearMap.ext fun φ => Subtype.ext ?_
    rw [hu w hw]
    exact op_unit hP hS hw d hd φ.2
  · have hne' : w'.under (𝓞 (Lp L)) ≠ w.under (𝓞 (Lp L)) := fun h =>
      hne (hP.inj (Finset.mem_coe.2 hw') (Finset.mem_coe.2 hw) h).symm
    refine LinearMap.ext fun φ => Subtype.ext ?_
    rw [Module.End.mul_apply, Module.End.mul_apply, hu w hw, hu w' hw', hu w' hw', hu w hw]
    exact LinearMap.congr_fun (op_comm (hP.split w (Finset.mem_coe.2 hw)) (hP.split w' (Finset.mem_coe.2 hw')) hne' d d') _
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.SmoothDepth.OpenLevelSubgroups.ExtChar
open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

namespace UpperTheory.V.Z.Sym.Al.ExtChar

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

private theorem val_eq (x : kˣ) : valuation k (x : k) = uniformizer k ^ ord k x := by
  have h := UpperTheory.V.Hi.GlAx.val_div_ord x
  rw [Units.val_div_eq_div_val, map_div₀, UpperTheory.V.Hi.GlAx.val_zpow] at h
  exact (div_eq_one_iff_eq (zpow_pos UpperTheory.V.Hi.GlAx.unif_pos _).ne').1 h

private theorem sdom_of_exp (u : Fin n → kˣ) (e : Fin n → ℤ)
    (hv : ∀ i, valuation k (u i : k) = uniformizer k ^ e i) (he : ∀ i j, i < j → e j < e i) : Sig.SDom u := by
  intro i j hij
  rw [hv, hv]
  exact zpow_lt_zpow_right_of_lt_one₀ UpperTheory.V.Hi.GlAx.unif_pos uniformizer_lt_one (he i j hij)

private noncomputable def rho (n : ℕ) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m : ℤ) : Fin n → kˣ := fun i => UpperTheory.V.Hi.unif k ^ (-(m * (i : ℕ)))

private theorem rho_sdom {m : ℤ} (hm : 0 < m) : Sig.SDom (rho n k m) := by
  refine sdom_of_exp _ (fun i => -(m * ((i : ℕ) : ℤ))) (fun i => UpperTheory.V.Hi.GlAx.val_zpow _) fun i j hij => ?_
  have : ((i : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by exact_mod_cast hij
  nlinarith

private theorem sdom_mul {d d' : Fin n → kˣ} (h : Sig.SDom d) (h' : Sig.SDom d') : Sig.SDom (d * d') := by
  intro i j hij
  simp only [Pi.mul_apply, Units.val_mul, map_mul]
  exact mul_lt_mul'' (h i j hij) (h' i j hij) zero_le' zero_le'

private theorem sdom_mul_unit {d u : Fin n → kˣ} (h : Sig.SDom d) (hu : ∀ i, u i ∈ UpperTheory.V.Hi.Uo k) : Sig.SDom (d * u) := by
  intro i j hij
  have h1 : ∀ i, valuation k (u i : k) = 1 := hu
  simp only [Pi.mul_apply, Units.val_mul, map_mul, h1, mul_one]
  exact h i j hij

private theorem exists_div (t : Fin n → kˣ) : ∃ a b : Fin n → kˣ, Sig.SDom a ∧ Sig.SDom b ∧ t = a * b⁻¹ := by
  let B : ℤ := ∑ i, |ord k (t i)|
  have hB : ∀ i, |ord k (t i)| ≤ B := fun i =>
    Finset.single_le_sum (f := fun i => |ord k (t i)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hm : 0 < 2 * B + 1 := by omega
  refine ⟨t * rho n k (2 * B + 1), rho n k (2 * B + 1), ?_, rho_sdom hm, by simp⟩
  refine sdom_of_exp _ (fun i => ord k (t i) + -((2 * B + 1) * ((i : ℕ) : ℤ))) (fun i => ?_) fun i j hij => ?_
  · rw [Pi.mul_apply, Units.val_mul, map_mul, val_eq, rho, UpperTheory.V.Hi.GlAx.val_zpow,
      zpow_add₀ UpperTheory.V.Hi.GlAx.unif_pos.ne']
  · have h0 : ((i : ℕ) : ℤ) + 1 ≤ ((j : ℕ) : ℤ) := by exact_mod_cast hij
    have h1 := abs_le.1 (hB i)
    have h2 := abs_le.1 (hB j)
    nlinarith

private def P (n : ℕ) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    Submonoid (Fin n → kˣ) where
  carrier := {d | Sig.SDom d ∨ d = 1}
  one_mem' := Or.inr rfl
  mul_mem' := by
    rintro a b (ha | rfl) (hb | rfl)
    · exact Or.inl (sdom_mul ha hb)
    · simpa using Or.inl ha
    · simpa using Or.inl hb
    · simp

private theorem delta_unit (v : Fin n → kˣ) (hv : ∀ i, v i ∈ UpperTheory.V.Hi.Uo k) :
    (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom v = 1 := by
  rw [MonoidHom.comp_apply, deltaHalf_apply]
  refine Finset.prod_eq_one fun a _ => ?_
  have h : Matrix.GeneralLinearGroup.det (leviTorus k (Fin n) v a) = v a := congrFun ((leviTorus k (Fin n)).left_inv v) a
  erw [h]
  exact isUnram_absPow k _ _ (hv a)

end UpperTheory.V.Z.Sym.Al.ExtChar

open UpperTheory.V.Z.Sym.Al.ExtChar in
theorem UpperTheory.V.Z.Sym.Al.extChar :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (χ : (Fin n → kˣ) → ℂ), (∀ d, Sig.SDom d → χ d ≠ 0) → (∀ d d', Sig.SDom d → Sig.SDom d' → χ (d * d') = χ d * χ d') →
        (∀ d u, Sig.SDom d → (∀ i, u i ∈ Hi.Uo k) → χ (d * u) = χ d) →
        ∃ ψ : Fin n → kˣ →* ℂˣ, (∀ i, ∀ u ∈ Hi.Uo k, ψ i u = 1) ∧ ∀ d, Sig.SDom d → χ d = expo ψ d := by
  classical
  intro k _ _ _ _ n χ hne hmul hunit
  let f : (Fin n → kˣ) → ℂ := fun d => if d = 1 then 1 else χ d
  have hf : ∀ d, Sig.SDom d → f d = χ d := by
    intro d hd
    by_cases h1 : d = 1
    · subst h1
      have h2 := hmul 1 1 hd hd
      rw [mul_one] at h2
      have h3 : χ 1 = 1 := by
        have h4 := hne 1 hd
        exact mul_right_cancel₀ h4 (by rw [one_mul]; exact h2.symm)
      simp [f, h3]
    · simp [f, h1]
  have hf1 : f 1 = 1 := by simp [f]
  obtain ⟨θ, hθ, -⟩ := UpperTheory.V.AlgebraTools.monoidExt (Fin n → kˣ) ℂ (P n k) f
    (fun t => by
      obtain ⟨a, b, ha, hb, h⟩ := exists_div t
      exact ⟨a, Or.inl ha, b, Or.inl hb, h⟩)
    hf1
    (by
      rintro a (ha | rfl) b (hb | rfl)
      · rw [hf _ ha, hf _ hb, hf _ (sdom_mul ha hb), hmul _ _ ha hb]
      · rw [mul_one, hf1, mul_one]
      · rw [one_mul, hf1, one_mul]
      · rw [mul_one, hf1, mul_one])
    (by
      rintro a (ha | rfl)
      · rw [hf _ ha]
        exact (hne a ha).isUnit
      · rw [hf1]
        exact isUnit_one)
  have hθχ : ∀ d, Sig.SDom d → (θ d : ℂ) = χ d := fun d hd => (hθ d (Or.inl hd)).trans (hf d hd)
  have hθu : ∀ u : Fin n → kˣ, (∀ i, u i ∈ Hi.Uo k) → θ u = 1 := by
    intro u hu
    obtain ⟨a, -, ha, -, -⟩ := exists_div (1 : Fin n → kˣ)
    have h1 : θ (a * u) = θ a := Units.ext (by
      rw [hθχ _ (sdom_mul_unit ha hu), hθχ _ ha, hunit _ _ ha hu])
    rw [map_mul] at h1
    exact mul_left_cancel (h1.trans (mul_one _).symm)
  let D : (Fin n → kˣ) →* ℂˣ := (deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom
  have hsingle : ∀ (i : Fin n) (u : kˣ), u ∈ Hi.Uo k → ∀ j, (Pi.mulSingle i u : Fin n → kˣ) j ∈ Hi.Uo k := by
    intro i u hu j
    by_cases h : j = i
    · subst h; simpa using hu
    · rw [Pi.mulSingle_eq_of_ne h]; exact one_mem _
  refine ⟨fun i => (θ * D).comp (MonoidHom.mulSingle (fun _ : Fin n => kˣ) i), ?_, ?_⟩
  · intro i u hu
    simp only [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.mulSingle_apply]
    rw [hθu _ (hsingle i u hu), delta_unit _ (hsingle i u hu), one_mul]
  · intro d hd
    have h1 : torusChar (fun i => (θ * D).comp (MonoidHom.mulSingle (fun _ : Fin n => kˣ) i)) d = θ d * D d := by
      rw [torusChar_apply]
      simp only [MonoidHom.comp_apply, MonoidHom.mulSingle_apply]
      rw [← map_prod, Finset.univ_prod_mulSingle, MonoidHom.mul_apply]
    rw [Dict.expo, h1, ← hθχ d hd]
    change (θ d : ℂ) = ((θ d * D d * (D d)⁻¹ : ℂˣ) : ℂ)
    rw [mul_inv_cancel_right]
end

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.V.Z.Sym.Al

namespace UpperTheory.V.Z.Sym.Al

private theorem common_eig {ι M : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (f : ι → Module.End ℂ M) (hc : ∀ i j, Commute (f i) (f j)) :
    ∀ (n : ℕ) (W : Submodule ℂ M), Module.finrank ℂ W = n → W ≠ ⊥ → (∀ i, ∀ x ∈ W, f i x ∈ W) →
      ∃ v ∈ W, v ≠ 0 ∧ ∀ i, ∃ c : ℂ, f i v = c • v :=
  _root_.UpperTheory.Reformulated.B.ComplexCommonEigenvectorOfFinrankEq.common_eig f hc

private theorem sdom_pair {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (t : kˣ) (ht : valuation k (t : k) < 1) : Sig.SDom ![t, t⁻¹] := by
  intro i j hij
  have h0 : valuation k (t : k) ≠ 0 := (Valuation.ne_zero_iff _).2 t.ne_zero
  have h1 : valuation k (t : k) < (valuation k (t : k))⁻¹ :=
    ht.trans (one_lt_inv₀ (zero_lt_iff.2 h0) |>.2 ht)
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simpa using h1

private theorem dom_of_sdom {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (d : Fin n → kˣ) (hd : Sig.SDom d) : AlgebraTools.Dom d := by
  intro i j hij
  rcases hij.lt_or_eq with h | rfl
  · exact (hd i j h).le
  · exact le_rfl

private theorem dom_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : ℕ} (d d' : Fin n → kˣ) (h : AlgebraTools.Dom d) (h' : AlgebraTools.Dom d') : AlgebraTools.Dom (d * d') := by
  intro i j hij
  simp only [Pi.mul_apply, Units.val_mul, map_mul]
  exact mul_le_mul' (h i j hij) (h' i j hij)

private theorem loc_char {k M : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [AddCommGroup M] [Module ℂ M] (u : (Fin 2 → kˣ) → Module.End ℂ M) (b : kˣ →* ℂˣ) (v : M) (hv : v ≠ 0)
    (hmul : ∀ d d', AlgebraTools.Dom d → AlgebraTools.Dom d' → u (d * d') = u d * u d')
    (hone : ∀ d, (∀ i, d i ∈ Hi.Uo k) → u d = 1)
    (hdomU : ∀ d : Fin 2 → kˣ, (∀ i, d i ∈ Hi.Uo k) → AlgebraTools.Dom d)
    (heig : ∀ d, AlgebraTools.Dom d → ∃ c : ℂ, u d v = c • v)
    (hb : ∀ t : kˣ, valuation k (t : k) < 1 → u ![t, t⁻¹] v = expo ![b, 1] ![t, t⁻¹] • v) :
    ∃ ψ : Fin 2 → kˣ →* ℂˣ, (∀ i, ∀ x ∈ Hi.Uo k, ψ i x = 1) ∧ ψ 0 / ψ 1 = b ∧
      ∀ d, Sig.SDom d → u d v = expo ψ d • v := by
  classical
  choose! χ hχ using heig
  have uniq : ∀ c c' : ℂ, c • v = c' • v → c = c' := fun c c' h => smul_left_injective ℂ hv h
  have hmulχ : ∀ d d', AlgebraTools.Dom d → AlgebraTools.Dom d' → χ (d * d') = χ d * χ d' := by
    intro d d' h h'
    apply uniq
    rw [← hχ _ (dom_mul d d' h h'), hmul d d' h h', Module.End.mul_apply, hχ d' h', map_smul, hχ d h,
      smul_smul, mul_comm]
  have hunit : ∀ d, (∀ i, d i ∈ Hi.Uo k) → χ d = 1 := by
    intro d hd
    apply uniq
    rw [← hχ d (hdomU d hd), hone d hd, one_smul]
    rfl
  have hexpo : ∀ (ψ : Fin 2 → kˣ →* ℂˣ) (d : Fin 2 → kˣ), expo ψ d ≠ 0 := fun ψ d => Units.ne_zero _
  have hχb : ∀ t : kˣ, valuation k (t : k) < 1 → χ ![t, t⁻¹] = expo ![b, 1] ![t, t⁻¹] := by
    intro t ht
    apply uniq
    rw [← hχ _ (dom_of_sdom _ (sdom_pair t ht)), hb t ht]
  have hne : ∀ d, Sig.SDom d → χ d ≠ 0 := by
    intro d hd h0
    have hlt : valuation k (d 0 : k) < valuation k (d 1 : k) := hd 0 1 (by decide)
    let z : Fin 2 → kˣ := fun _ => d 0 * d 1
    have hz : AlgebraTools.Dom z := fun _ _ _ => le_rfl
    have hz' : AlgebraTools.Dom z⁻¹ := fun _ _ _ => le_rfl
    have hzz : χ z * χ z⁻¹ = 1 := by
      rw [← hmulχ _ _ hz hz', mul_inv_cancel]
      exact hunit 1 fun _ => one_mem _
    have hz0 : χ z ≠ 0 := left_ne_zero_of_mul_eq_one hzz
    let t : kˣ := d 0 / d 1
    have ht : valuation k (t : k) < 1 := by
      have h1 : valuation k (d 1 : k) ≠ 0 := (Valuation.ne_zero_iff _).2 (d 1).ne_zero
      simp only [t, Units.val_div_eq_div_val, map_div₀]
      exact (div_lt_one₀ (zero_lt_iff.2 h1)).2 hlt
    have hdd : d * d = z * ![t, t⁻¹] := by
      have e0 : d 0 * d 0 = d 0 * d 1 * (d 0 / d 1) := by rw [mul_assoc, mul_div_cancel]
      have e1 : d 1 * d 1 = d 0 * d 1 * (d 0 / d 1)⁻¹ := by
        rw [inv_div, mul_comm (d 0), mul_assoc, mul_div_cancel]
      funext i
      fin_cases i
      · exact e0
      · exact e1
    have hs := sdom_pair t ht
    have key : χ d * χ d = χ z * χ ![t, t⁻¹] := by
      rw [← hmulχ d d (dom_of_sdom d hd) (dom_of_sdom d hd), hdd, hmulχ _ _ hz (dom_of_sdom _ hs)]
    rw [h0, zero_mul, hχb t ht] at key
    exact mul_ne_zero hz0 (hexpo _ _) key.symm
  obtain ⟨ψ, hψ1, hψ2⟩ := extChar k 2 χ hne
    (fun d d' h h' => hmulχ d d' (dom_of_sdom d h) (dom_of_sdom d' h'))
    (fun d x h hx => by rw [hmulχ d x (dom_of_sdom d h) (hdomU x hx), hunit x hx, mul_one])
  refine ⟨ψ, hψ1, (unrSmooth k).2 ψ b fun t ht => ?_, fun d hd => ?_⟩
  · rw [← hψ2 _ (sdom_pair t ht), hχb t ht]
  · rw [hχ d (dom_of_sdom d hd), hψ2 d hd]

end UpperTheory.V.Z.Sym.Al

theorem UpperTheory.V.Z.Sym.Al.refine :
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (R : Representation ℂ (InfinitePlace L → GL (Fin 2) ℂ) V) (U : Subgroup (UA L 2)), IsLevel U →
        ∀ S : Finset (Plc L), Places (S : Set (Plc L)) → (∀ w ∈ S, locU 2 w ⊓ Kall L 2 ≤ U) →
        ∀ (b : ∀ w : Plc L, (Kw w)ˣ →* ℂˣ) (φ : UA L 2 → V), φ ≠ 0 → IsAF R (lev U S iw) φ → (∀ w ∈ S, EigS φ w (iw w) (b w)) →
        ∃ (φ' : UA L 2 → V) (ψ : ∀ w : Plc L, Fin 2 → (Kw w)ˣ →* ℂˣ), φ' ≠ 0 ∧ IsAF R (lev U S iw) φ' ∧
          ∀ w ∈ S, (∀ i, ∀ u ∈ Hi.Uo (Kw w), ψ w i u = 1) ∧ ψ w 0 / ψ w 1 = b w ∧ EigT φ' w (iw w) (ψ w) := by
  intro L _ _ _ V _ _ _ R U hU S hS hloc b φ hφ hAF hE
  classical
  obtain ⟨u, hu_op, hu_mul, hu_one, hu_comm⟩ := afOps L 2 V R U hU.1 S hS hloc
  haveI : FiniteDimensional ℂ (AF R (lev U S iw)) :=
    afFin L 2 V R (lev U S iw) ((cof L 2).2.2.1 U hU S iw)
  have hdomU : ∀ (w : Plc L) (d : Fin 2 → (Kw w)ˣ), (∀ i, d i ∈ Hi.Uo (Kw w)) → AlgebraTools.Dom d := by
    intro w d hd i j _
    exact ((hd i).trans (hd j).symm).le
  have hpair : ∀ (w : Plc L) (t : (Kw w)ˣ), valuation (Kw w) (t : Kw w) < 1 → AlgebraTools.Dom ![t, t⁻¹] :=
    fun w t ht => dom_of_sdom _ (sdom_pair t ht)

  have hcomm : ∀ w ∈ S, ∀ w' ∈ S, ∀ (d : Fin 2 → (Kw w)ˣ) (d' : Fin 2 → (Kw w')ˣ), AlgebraTools.Dom d → AlgebraTools.Dom d' →
      Commute (u w d) (u w' d') := by
    intro w hw w' hw' d d' hd hd'
    by_cases h : w = w'
    · subst h
      show u w d * u w d' = u w d' * u w d
      rw [← hu_mul w hw d d' hd hd', ← hu_mul w hw d' d hd' hd, mul_comm d d']
    · exact hu_comm w hw w' hw' h d d' hd hd'
  let E : Submodule ℂ (AF R (lev U S iw)) :=
    { carrier := {m | ∀ w ∈ S, ∀ t : (Kw w)ˣ, valuation (Kw w) (t : Kw w) < 1 →
        u w ![t, t⁻¹] m = expo ![b w, 1] ![t, t⁻¹] • m}
      add_mem' := fun {x y} hx hy w hw t ht => by rw [map_add (f := _), hx w hw t ht, hy w hw t ht, smul_add]
      zero_mem' := fun w _ t _ => by simp
      smul_mem' := fun c x hx w hw t ht => by rw [map_smul, hx w hw t ht, smul_comm] }
  have hmemE : ∀ m, m ∈ E ↔ ∀ w ∈ S, ∀ t : (Kw w)ˣ, valuation (Kw w) (t : Kw w) < 1 →
      u w ![t, t⁻¹] m = expo ![b w, 1] ![t, t⁻¹] • m := fun _ => Iff.rfl
  let φ₀ : AF R (lev U S iw) := ⟨φ, hAF⟩
  have hφ₀ : φ₀ ∈ E := by
    refine (hmemE _).2 fun w hw t ht => Subtype.ext ?_
    rw [hu_op w hw _ (hpair w t ht)]
    exact hE w hw t ht
  have hφ₀0 : φ₀ ≠ 0 := fun h => hφ (congrArg Subtype.val h)
  have hE0 : E ≠ ⊥ := fun h => hφ₀0 (by
    have := hφ₀
    rw [h] at this
    simpa using this)
  let ι : Type := Σ w : {w // w ∈ S}, {d : Fin 2 → (Kw w.1)ˣ // AlgebraTools.Dom d}
  let f : ι → Module.End ℂ (AF R (lev U S iw)) := fun i => u i.1.1 i.2.1
  obtain ⟨v, hvE, hv0, hveig⟩ := common_eig f
    (fun i j => hcomm i.1.1 i.1.2 j.1.1 j.1.2 i.2.1 j.2.1 i.2.2 j.2.2) _ E rfl hE0
    (fun i x hx => (hmemE _).2 fun w hw t ht => by
      have hc := (hcomm i.1.1 i.1.2 w hw i.2.1 ![t, t⁻¹] i.2.2 (hpair w t ht)).eq
      have := congrArg (fun g : Module.End ℂ (AF R (lev U S iw)) => g x) hc
      simp only [Module.End.mul_apply] at this
      show u w ![t, t⁻¹] (u i.1.1 i.2.1 x) = _
      rw [← this, (hmemE x).1 hx w hw t ht]
      exact map_smul _ _ _)
  have hloc' : ∀ w : Plc L, ∃ ψ : Fin 2 → (Kw w)ˣ →* ℂˣ, w ∈ S →
      (∀ i, ∀ x ∈ Hi.Uo (Kw w), ψ i x = 1) ∧ ψ 0 / ψ 1 = b w ∧
        ∀ d, Sig.SDom d → u w d v = expo ψ d • v := by
    intro w
    by_cases hw : w ∈ S
    · obtain ⟨ψ, h⟩ := loc_char (u w) (b w) v hv0 (hu_mul w hw) (hu_one w hw) (hdomU w)
        (fun d hd => hveig ⟨⟨w, hw⟩, ⟨d, hd⟩⟩) ((hmemE v).1 hvE w hw)
      exact ⟨ψ, fun _ => h⟩
    · exact ⟨1, fun h => absurd h hw⟩
  choose ψ hψ using hloc'
  refine ⟨(v : UA L 2 → V), ψ, fun h => hv0 (Subtype.ext h), v.2, fun w hw => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hψ w hw
  refine ⟨h1, h2, fun d hd => ?_⟩
  have := congrArg Subtype.val (h3 d hd)
  rw [hu_op w hw d (dom_of_sdom d hd) v] at this
  exact this
