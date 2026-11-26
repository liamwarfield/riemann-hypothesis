module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralInvariantDerivationLog
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryPairKeepsCompletedLattice
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.LinearFormDegree.InvFun

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationEqPartialLogCoordsProof
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationEqPartialLogCoordsProof
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.InvDer

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.LawLog GlobalTheory.FactorDepth
  GlobalTheory.IsoTriv

section Two

variable {K : Type} [Field K] [CharZero K] {d : ℕ}

theorem subst_secondBlockZero_twoPointVariables {ι : Type} (Y : Fin d → MvPowerSeries ι K) (hY : ∀ i, constantCoeff (Y i) = 0)
    (f : PS K 2 d) :
    subst Y (subst (GlobalTheory.LogJacobian.substSecondBlockZero (C := K) d) (subst (twoVars K d) f : MvPowerSeries (Fin d ⊕ Fin d) K) :
        MvPowerSeries (Fin d) K) =
      subst (fun q : Fin 2 × Fin d => if q.1 = 0 then Y q.2 else 0) f := by
  have hYs : HasSubst Y := hasSubst_of_constantCoeff_zero hY
  have hA := GlobalTheory.LogJacobian.hasSubst_substSecondBlockZero (C := K) d
  have hB : HasSubst (fun q : Fin 2 × Fin d => subst (GlobalTheory.LogJacobian.substSecondBlockZero (C := K) d) (twoVars K d q)) :=
    hasSubst_of_constantCoeff_zero fun q =>
      constantCoeff_subst_eq_zero hA (GlobalTheory.LogJacobian.constantCoeff_substSecondBlockZero d) (cc_twoVars q)
  rw [subst_comp_subst_apply hs_twoVars hA, subst_comp_subst_apply hB hYs]
  congr 1
  funext q
  rw [twoVars, subst_X hA]
  split_ifs with h
  · simp [GlobalTheory.LogJacobian.substSecondBlockZero, subst_X hYs]
  · simp only [GlobalTheory.LogJacobian.substSecondBlockZero, Sum.elim_inr]
    rw [← coe_substAlgHom hYs, map_zero]

theorem pderiv_inr_twoVars (k : Fin d) (f : PS K 2 d) :
    pderiv (Sum.inr k) (subst (twoVars K d) f) = subst (twoVars K d) (pderiv ((1 : Fin 2), k) f) := by
  classical
  rw [ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst cc_twoVars, Finset.sum_eq_single ((1 : Fin 2), k)]
  · simp [twoVars]
  · intro q _ hq
    obtain ⟨a, i⟩ := q
    fin_cases a
    · simp [twoVars]
    · have : i ≠ k := fun h => hq (by simp [h])
      simp [twoVars, this]
  · simp

end Two

section Main

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℝ)} {d n : ℕ} {ι : Type}

theorem subst_jacEntry (F : FGLaw K d) (hF : ∀ a, MvIsInt v (subst (twoVars K d) (F.F a)))
    (Y : Fin d → MvPowerSeries ι K) (hY : ∀ i, constantCoeff (Y i) = 0) (k j : Fin d) :
    subst Y (GlobalTheory.LogJacobian.jacEntry (logFGLOf v F hF) k j) =
      subst (fun q : Fin 2 × Fin d => if q.1 = 0 then Y q.2 else 0) (pderiv ((1 : Fin 2), k) (F.F j)) := by
  rw [← subst_secondBlockZero_twoPointVariables Y hY, ← pderiv_inr_twoVars]
  rfl


omit [CharZero K] in
theorem subst_ev_pt_zero [Finite ι] (T : Fin n × Fin d → MvPowerSeries ι K) (hT : ∀ q, constantCoeff (T q) = 0)
    (b : Fin n) (g : PS K 2 d) :
    subst T (ev (n := n) ![pt K d b, 0] g) =
      subst (fun q : Fin 2 × Fin d => if q.1 = 0 then T (b, q.2) else 0) g := by
  have hTs : HasSubst T := hasSubst_of_constantCoeff_zero hT
  have h2 : HasSubst (fun p : Fin 2 × Fin d => (![pt K d b, 0] : Fin 2 → Pt K n d) p.1 p.2) :=
    hasSubst_of_constantCoeff_zero fun p => by
      obtain ⟨j, i⟩ := p
      fin_cases j <;> simp [pt]
  unfold ev
  rw [subst_comp_subst_apply h2 hTs]
  congr 1
  funext p
  obtain ⟨j, i⟩ := p
  fin_cases j
  · simp [pt, subst_X hTs]
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply, one_ne_zero, ite_false]
    rw [← coe_substAlgHom hTs, map_zero]


omit [CharZero K] in
theorem constantCoeff_subst_self {σ : Type} [Finite σ] (T : σ → MvPowerSeries ι K)
    (hT : ∀ q, constantCoeff (T q) = 0) (f : MvPowerSeries σ K) :
    constantCoeff (subst T f : MvPowerSeries ι K) = constantCoeff f := by
  have hs : HasSubst T := hasSubst_of_constantCoeff_zero hT
  have h0 : constantCoeff (subst T (f - (constantCoeff f) • 1) : MvPowerSeries ι K) = 0 :=
    constantCoeff_subst_eq_zero hs hT (by simp)
  rw [← coe_substAlgHom hs, map_sub, map_smul, map_one, coe_substAlgHom hs] at h0
  simpa [sub_eq_zero] using h0

variable [Fintype ι]

def logLin (cp : ι → Fin n) (u : ι → Fin d → K) (b : Fin n) : Fin d → MvPowerSeries ι K :=
  fun e => ∑ l, (if cp l = b then u l e else 0) • (X l : MvPowerSeries ι K)

omit [CharZero K] in
theorem cc_logLin (cp : ι → Fin n) (u : ι → Fin d → K) (b : Fin n) (e : Fin d) :
    constantCoeff (logLin cp u b e) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [logLin, map_sum, constantCoeff_smul, constantCoeff_X, smul_zero, Finset.sum_const_zero]

omit [CharZero K] in
theorem pderiv_logLin (cp : ι → Fin n) (u : ι → Fin d → K) (b : Fin n) (e : Fin d) (l : ι) :
    pderiv l (logLin cp u b e) = if cp l = b then C (u l e) else 0 := by
  classical
  unfold logLin
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_eq_single l]
  · rw [Derivation.map_smul, pderiv_X_self, smul_eq_C_mul, mul_one]
    split_ifs <;> simp
  · intro l' _ hl
    rw [Derivation.map_smul, pderiv_X_of_ne hl, smul_zero]
  · simp

theorem pderiv_subst_expPt (F : FGLaw K d) (hF : ∀ a, MvIsInt v (subst (twoVars K d) (F.F a)))
    (cp : ι → Fin n) (u : ι → Fin d → K) (l : ι) (Φ : PS K n d) :
    subst (fun q : Fin n × Fin d => expPt (logFGLOf v F hF) (logLin cp u q.1) q.2) (DofN F.F (cp l) (u l) Φ) =
      pderiv l (subst (fun q : Fin n × Fin d => expPt (logFGLOf v F hF) (logLin cp u q.1) q.2) Φ) := by
  classical
  set G := logFGLOf v F hF with hG
  set T : Fin n × Fin d → MvPowerSeries ι K := fun q => expPt G (logLin cp u q.1) q.2 with hTdef
  have hT : ∀ q, constantCoeff (T q) = 0 := fun q => cc_expPt G (cc_logLin cp u q.1) q.2
  have hTs : HasSubst T := hasSubst_of_constantCoeff_zero hT
  have key : ∀ b j, pderiv l (T (b, j)) = if cp l = b then
      ∑ i : Fin d, C (u l i) * subst T (ev (n := n) ![pt K d b, 0] (pderiv ((1 : Fin 2), i) (F.F j))) else 0 := by
    intro b j
    have h1 : pderiv l (T (b, j)) = ∑ i, subst (logLin cp u b) (pderiv i (expOf G j)) *
        pderiv l (logLin cp u b i) :=
      ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst (cc_logLin cp u b) (expOf G j) l
    have h2 : ∀ i, subst (logLin cp u b) (pderiv i (expOf G j)) =
        subst T (ev (n := n) ![pt K d b, 0] (pderiv ((1 : Fin 2), i) (F.F j))) := by
      intro i
      rw [GlobalTheory.LogJacobian.pderiv_expOf, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (isExp_expOf G).1)
        (hasSubst_of_constantCoeff_zero (cc_logLin cp u b)), subst_ev_pt_zero T hT]
      exact subst_jacEntry F hF (fun e => T (b, e)) (fun e => hT (b, e)) i j
    rw [h1]
    simp only [h2, pderiv_logLin]
    split_ifs
    · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · simp
  rw [ReciprocityTheory.ChartRestriction.G.TB.LogPf.pderiv_subst hT, Fintype.sum_prod_type, Finset.sum_eq_single (cp l)]
  · unfold DofN
    simp only [key, ite_true]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← coe_substAlgHom hTs, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, map_sum, mul_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, coe_substAlgHom hTs, subst_C]
  · intro b _ hb
    simp [key, Ne.symm hb]
  · simp

end Main

theorem invDer : InvDerSt := by
  intro K _ _ v d F hF n ι _ cp u P Φ
  classical
  show _ = derivAt0 P (subst (fun q : Fin n × Fin d => expPt (logFGLOf v F hF) (logLin cp u q.1) q.2) Φ)
  have hk := pderiv_subst_expPt F hF cp u
  set T : Fin n × Fin d → MvPowerSeries ι K := fun q => expPt (logFGLOf v F hF) (logLin cp u q.1) q.2
  have hT : ∀ q, constantCoeff (T q) = 0 := fun q => cc_expPt _ (cc_logLin cp u q.1) q.2
  have hit : ∀ (l : ι) (c : ℕ) (g : PS K n d),
      subst T ((DofN F.F (cp l) (u l))^[c] g) = (pderiv l)^[c] (subst T g : MvPowerSeries ι K) := by
    intro l c
    induction c with
    | zero => intro g; rfl
    | succ c ih => intro g; rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hk]
  have hfold : ∀ (m : ι →₀ ℕ) (L : List ι),
      subst T (L.foldr (fun l g => (DofN F.F (cp l) (u l))^[m l] g) Φ) =
        L.foldr (fun l g => (pderiv l)^[m l] g) (subst T Φ : MvPowerSeries ι K) := by
    intro m L
    induction L with
    | nil => rfl
    | cons a L ih => rw [List.foldr_cons, List.foldr_cons, hit, ih]
  unfold DpolyN derivAt0
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, constantCoeff_C, mul_assoc, ← constantCoeff_subst_self T hT]
  congr 1
  unfold DmonN
  rw [hfold, ← coeff_zero_eq_constantCoeff_apply,
    ReciprocityTheory.ChartRestriction.G.TB.MV.coeff_fold (fun l : ι => l) (fun _ _ h => h) m _ _ (Finset.nodup_toList _) 0,
    Finset.sum_map_toList, Finset.prod_map_toList]
  have h1 : (∑ l, m l • Finsupp.single l 1 : ι →₀ ℕ) = m := by
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one]
    exact Finsupp.univ_sum_single m
  have h2 : (mfact m : K) = ∏ l, ((m l).factorial : K) := Finsupp.prod_fintype _ _ (by simp)
  simp only [zero_add, Finsupp.coe_zero, Pi.zero_apply, Nat.one_ascFactorial]
  rw [h1, h2, mul_comm]

end GlobalTheory.InvDer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantDerivationEqPartialLogCoordsProofStatement
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantDerivationEqPartialLogCoords_proof : InvDerSt := by
  first | exact @GlobalTheory.InvDer.invDer | exact GlobalTheory.InvDer.invDer | (intros; apply GlobalTheory.InvDer.invDer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordReachingIrreducibleKModuleReachesHighestWeig
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeightWordApplyWeightVector
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeightWordApplyWeightVector
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.WordWeight

theorem step {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) (ν : Fin n → ℝ) (v : V)
    (hv : IsWeight E ν v) (a b : Fin n) :
    IsWeight E (ν + root a b) (E a b v) := by
  intro c
  have h := hE c c a b
  have h2 : E c c (E a b v) = E a b (E c c v) +
      ((if c = a then E c b else 0) - (if b = c then E a c else 0)) v := by
    rw [← h]; simp
  rw [h2, hv c, map_smul]
  simp only [root, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  by_cases hca : c = a <;> by_cases hbc : b = c
  · subst hca; subst hbc; simp
  · subst hca
    have : ¬ c = b := fun h => hbc h.symm
    simp [this, hbc]
    rw [add_smul, one_smul]
    rfl
  · subst hbc
    simp [hca]
    rw [add_smul, neg_smul, one_smul]
    rfl
  · have : ¬ c = b := fun h => hbc h.symm
    simp [hca, this, hbc]

theorem word {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (hE : GlRel E) :
    ∀ (l : List (Fin n × Fin n)) (μ : Fin n → ℝ) (w : V), IsWeight E μ w →
    IsWeight E (μ + (l.map fun p : Fin n × Fin n => root p.1 p.2).sum)
      ((l.map fun p : Fin n × Fin n => E p.1 p.2).prod w) := by
  intro l μ w hw
  induction l with
  | nil => simpa using hw
  | cons p l ih =>
    have := step E hE _ _ ih p.1 p.2
    simp only [List.map_cons, List.sum_cons, List.prod_cons, mul_apply_eq_comp]
    convert this using 1
    abel

end GlobalTheory.WordWeight

theorem GlobalTheory.wordWeight : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ∀ (μ : Fin n → ℝ) (w : V), IsWeight E μ w → ∀ l : List (Fin n × Fin n), IsWeight E (μ + (l.map fun p : Fin n × Fin n => root p.1 p.2).sum) ((l.map fun p : Fin n × Fin n => E p.1 p.2).prod w) := by
  intro n V _ _ E hE μ w hw l
  exact GlobalTheory.WordWeight.word E hE l μ w hw
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsWeightWordApplyWeightVectorStatement
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isWeight_word_apply_weightVector : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ∀ (μ : Fin n → ℝ) (w : V), IsWeight E μ w → ∀ l : List (Fin n × Fin n), IsWeight E (μ + (l.map fun p : Fin n × Fin n => root p.1 p.2).sum) ((l.map fun p : Fin n × Fin n => E p.1 p.2).prod w) := by
  first | exact @GlobalTheory.wordWeight | exact GlobalTheory.wordWeight | (intros; apply GlobalTheory.wordWeight <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactRaisingWordMemSpanHigherWords
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactRaisingWordMemSpanHigherWords
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

theorem GlobalTheory.HolDS.compactRaise_word_higher : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ∀ (w : V) (c d : Fin n), c < d → ε c = ε d → E c d w = 0 → ∀ (s t : Bool) (l : List (Fin n × Fin n)), (∀ p ∈ l, ε p.1 = s ∧ ε p.2 = t) → E c d ((l.map fun p : Fin n × Fin n => E p.1 p.2).prod w) ∈ Submodule.span ℂ {y : V | ∃ l' : List (Fin n × Fin n), l'.length = l.length ∧ (∀ p ∈ l', ε p.1 = s ∧ ε p.2 = t) ∧ (l.map fun p : Fin n × Fin n => ((p.2 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ)).sum < (l'.map fun p : Fin n × Fin n => ((p.2 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ)).sum ∧ y = (l'.map fun p : Fin n × Fin n => E p.1 p.2).prod w} := by
  intro n ε V _ _ E hG w c d hcd hεcd hw s t l
  induction l with
  | nil =>
    intro _
    simp only [List.map_nil, List.prod_nil, Module.End.one_apply, hw]
    exact Submodule.zero_mem _
  | cons p l ih =>
    obtain ⟨a, b⟩ := p
    intro hl
    have hab : ε a = s ∧ ε b = t := hl (a, b) List.mem_cons_self
    have hl' : ∀ p ∈ l, ε p.1 = s ∧ ε p.2 = t := fun p hp => hl p (List.mem_cons_of_mem _ hp)
    have IH := ih hl'
    have hcd' : (c : ℕ) < (d : ℕ) := hcd
    set y := (l.map fun p : Fin n × Fin n => E p.1 p.2).prod w with hy
    have hword : ((( (a, b) :: l).map fun p : Fin n × Fin n => E p.1 p.2).prod w) = E a b y := by
      simp [hy, Module.End.mul_apply]
    rw [hword]
    have key : E c d (E a b y) = E a b (E c d y) +
        ((if d = a then E c b else 0) - (if b = c then E a d else 0)) y := by
      have h := congrArg (fun f : Module.End ℂ V => f y) (hG c d a b)
      simp only [LinearMap.sub_apply, Module.End.mul_apply] at h
      rw [LinearMap.sub_apply, ← h]; abel
    rw [key]
    refine Submodule.add_mem _ ?_ ?_
    · have hm : E a b (E c d y) ∈ (Submodule.span ℂ _).map (E a b) := Submodule.mem_map_of_mem IH
      rw [Submodule.map_span] at hm
      refine Submodule.span_mono ?_ hm
      rintro _ ⟨z, ⟨l', hlen, hty, hh, rfl⟩, rfl⟩
      refine ⟨(a, b) :: l', by simp [hlen], ?_, ?_, by simp [Module.End.mul_apply]⟩
      · intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        exacts [hab, hty p hp]
      · simp only [List.map_cons, List.sum_cons]; linarith
    · rw [LinearMap.sub_apply]
      refine Submodule.sub_mem _ ?_ ?_
      · split_ifs with h1
        · subst h1
          refine Submodule.subset_span ⟨(c, b) :: l, by simp, ?_, ?_, by simp [hy, Module.End.mul_apply]⟩
          · intro p hp
            rcases List.mem_cons.1 hp with rfl | hp
            exacts [⟨hεcd.trans hab.1, hab.2⟩, hl' p hp]
          · simp only [List.map_cons, List.sum_cons]; omega
        · simp only [LinearMap.zero_apply]; exact Submodule.zero_mem _
      · split_ifs with h2
        · subst h2
          refine Submodule.subset_span ⟨(a, d) :: l, by simp, ?_, ?_, by simp [hy, Module.End.mul_apply]⟩
          · intro p hp
            rcases List.mem_cons.1 hp with rfl | hp
            exacts [⟨hab.1, hεcd.symm.trans hab.2⟩, hl' p hp]
          · simp only [List.map_cons, List.sum_cons]; omega
        · simp only [LinearMap.zero_apply]; exact Submodule.zero_mem _
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactRaisingWordMemSpanHigherWordsStatement
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactRaising_word_mem_span_higherWords : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → ∀ (w : V) (c d : Fin n), c < d → ε c = ε d → E c d w = 0 → ∀ (s t : Bool) (l : List (Fin n × Fin n)), (∀ p ∈ l, ε p.1 = s ∧ ε p.2 = t) → E c d ((l.map fun p : Fin n × Fin n => E p.1 p.2).prod w) ∈ Submodule.span ℂ {y : V | ∃ l' : List (Fin n × Fin n), l'.length = l.length ∧ (∀ p ∈ l', ε p.1 = s ∧ ε p.2 = t) ∧ (l.map fun p : Fin n × Fin n => ((p.2 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ)).sum < (l'.map fun p : Fin n × Fin n => ((p.2 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ)).sum ∧ y = (l'.map fun p : Fin n × Fin n => E p.1 p.2).prod w} := by
  first | exact @GlobalTheory.HolDS.compactRaise_word_higher | exact GlobalTheory.HolDS.compactRaise_word_higher | (intros; apply GlobalTheory.HolDS.compactRaise_word_higher <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordReachingIrreducibleKModuleReachesHighestWeig
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.HdStep

theorem proj_comm {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {E : Fin n → Fin n → Module.End ℂ V} (hU : KUnit ε E) (L : Submodule ℂ V) [L.HasOrthogonalProjection]
    (hL : KStab ε E L) (a b : Fin n) (hab : ε a = ε b) (y : V) :
    L.starProjection (E a b y) = E a b (L.starProjection y) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hL a b hab _ (L.starProjection_apply_mem y)
  · intro z hz
    rw [← map_sub, hU a b hab]
    exact Submodule.starProjection_inner_eq_zero y _ (hL b a hab.symm z hz)

theorem main : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → KUnit ε E → ∀ L : Submodule ℂ V, FiniteDimensional ℂ L → KStab ε E L → ∀ Λ : Fin n → ℝ, (∀ ν : Fin n → ℝ, ∀ x ∈ L, x ≠ 0 → KHighest ε E ν x → ν = Λ) → ∀ (μ : Fin n → ℝ) (w : V), KHighest ε E μ w → ∀ (s t : Bool) (l : List (Fin n × Fin n)), (∀ p ∈ l, ε p.1 = s ∧ ε p.2 = t) → ∀ x ∈ L, ⟪x, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod w⟫_ℂ ≠ 0 → ∃ l' : List (Fin n × Fin n), l'.length = l.length ∧ (∀ p ∈ l', ε p.1 = s ∧ ε p.2 = t) ∧ μ + (l'.map fun p : Fin n × Fin n => root p.1 p.2).sum = Λ := by
  intro n ε V _ _ E hG hU L hfd hL Λ hΛ μ w hw s t l hl x hx hxl
  haveI : FiniteDimensional ℂ L := hfd
  let word : List (Fin n × Fin n) → V := fun l => (l.map fun p : Fin n × Fin n => E p.1 p.2).prod w
  let ht : List (Fin n × Fin n) → ℤ := fun l => (l.map fun p : Fin n × Fin n => ((p.2 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ)).sum
  let S : Set (List (Fin n × Fin n)) :=
    {l' | l'.length = l.length ∧ (∀ p ∈ l', ε p.1 = s ∧ ε p.2 = t) ∧ L.starProjection (word l') ≠ 0}
  have hSfin : S.Finite := (List.finite_length_eq (Fin n × Fin n) l.length).subset (fun l' h => h.1)
  have hlS : l ∈ S := by
    refine ⟨rfl, hl, fun h0 => hxl ?_⟩
    have hPx : L.starProjection x = x := Submodule.starProjection_eq_self_iff.mpr hx
    rw [← hPx, Submodule.inner_starProjection_left_eq_right]
    change ⟪x, L.starProjection (word l)⟫_ℂ = 0
    rw [h0, inner_zero_right]
  obtain ⟨l', hl'S, hmax⟩ := Set.exists_max_image S ht hSfin ⟨l, hlS⟩
  refine ⟨l', hl'S.1, hl'S.2.1, ?_⟩
  set u := L.starProjection (word l') with hu
  have huL : u ∈ L := L.starProjection_apply_mem _
  have hwt := GlobalTheory.T.isWeight_word_apply_weightVector n V E hG μ w hw.1 l'
  refine hΛ _ u huL hl'S.2.2 ⟨?_, ?_⟩
  · intro a
    rw [hu, ← proj_comm hU L hL a a rfl, hwt a, map_smul]
  · intro c d hcd hcd'
    rw [hu, ← proj_comm hU L hL c d hcd']
    have hspan := GlobalTheory.T.compactRaising_word_mem_span_higherWords n ε V E hG w c d hcd hcd' (hw.2 c d hcd hcd') s t l' hl'S.2.1
    have hle : Submodule.span ℂ {y : V | ∃ l'' : List (Fin n × Fin n), l''.length = l'.length ∧
        (∀ p ∈ l'', ε p.1 = s ∧ ε p.2 = t) ∧
        (l'.map fun p : Fin n × Fin n => ((p.2 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ)).sum <
          (l''.map fun p : Fin n × Fin n => ((p.2 : ℕ) : ℤ) - ((p.1 : ℕ) : ℤ)).sum ∧
        y = (l''.map fun p : Fin n × Fin n => E p.1 p.2).prod w} ≤
        LinearMap.ker (L.starProjection : V →ₗ[ℂ] V) := by
      rw [Submodule.span_le]
      rintro y ⟨l'', hlen, htyp, hlt, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
      by_contra hne
      have hS'' : l'' ∈ S := ⟨hlen.trans hl'S.1, htyp, hne⟩
      exact absurd (hmax l'' hS'') (not_le.mpr hlt)
    exact LinearMap.mem_ker.mp (hle hspan)

end GlobalTheory.HdStep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WordReachingIrreducibleKModuleReachesHighestWeigStatement
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.word_reaching_irreducible_k_module_reaches_highest_weight : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), GlRel E → KUnit ε E → ∀ L : Submodule ℂ V, FiniteDimensional ℂ L → KStab ε E L → ∀ Λ : Fin n → ℝ, (∀ ν : Fin n → ℝ, ∀ x ∈ L, x ≠ 0 → KHighest ε E ν x → ν = Λ) → ∀ (μ : Fin n → ℝ) (w : V), KHighest ε E μ w → ∀ (s t : Bool) (l : List (Fin n × Fin n)), (∀ p ∈ l, ε p.1 = s ∧ ε p.2 = t) → ∀ x ∈ L, ⟪x, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod w⟫_ℂ ≠ 0 → ∃ l' : List (Fin n × Fin n), l'.length = l.length ∧ (∀ p ∈ l', ε p.1 = s ∧ ε p.2 = t) ∧ μ + (l'.map fun p : Fin n × Fin n => root p.1 p.2).sum = Λ := by
  first | exact @GlobalTheory.HdStep.main | exact GlobalTheory.HdStep.main | (intros; apply GlobalTheory.HdStep.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmicGroupLawSplitByIdempotent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntInv
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

namespace GlobalTheory.IntInv

theorem exists_int_inv : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), ∀ (d : ℕ) (Θ : Fin d → MvPowerSeries (Fin d) C), (∀ a, MvIsInt v (Θ a)) → (∀ a, constantCoeff (Θ a) = 0) → (∀ a b, coeff (Finsupp.single b 1) (Θ a) = if a = b then 1 else 0) → ∃ Ψ : Fin d → MvPowerSeries (Fin d) C, (∀ a, MvIsInt v (Ψ a)) ∧ (∀ a, constantCoeff (Ψ a) = 0) ∧ (∀ a, subst Ψ (Θ a) = MvPowerSeries.X a) ∧ ∀ a, subst Θ (Ψ a) = MvPowerSeries.X a := by
  intro C _ _ v d Θ hint h0 h1
  set S := ReciprocityTheory.ChartRestriction.G.Sh.PTb.intRing v
  let Θ' : Fin d → MvPowerSeries (Fin d) S := fun a α => ⟨coeff α (Θ a), hint a α⟩
  have hΘ' : ∀ a, map S.subtype (Θ' a) = Θ a := fun a => by ext α; rfl
  have h0' : ∀ a, constantCoeff (Θ' a) = 0 := fun a => Subtype.ext (by
    change coeff 0 (Θ a) = 0
    rw [coeff_zero_eq_constantCoeff_apply]; exact h0 a)
  have h1' : ∀ a b, coeff (Finsupp.single b 1) (Θ' a) = (1 : Matrix (Fin d) (Fin d) S) a b := by
    intro a b
    apply Subtype.ext
    change coeff (Finsupp.single b 1) (Θ a) = _
    rw [h1 a b, Matrix.one_apply]
    split_ifs <;> rfl
  have hu : IsUnit (1 : Matrix (Fin d) (Fin d) S).det := by rw [Matrix.det_one]; exact isUnit_one
  obtain ⟨ψ, hψ0, hψΘ, hΘψ⟩ := ReciprocityTheory.ChartRestriction.G.LF.InvFun.exists_inv Θ' h0' 1 h1' hu
  have hsψ : HasSubst ψ := hasSubst_of_constantCoeff_zero hψ0
  have hsΘ : HasSubst Θ' := hasSubst_of_constantCoeff_zero h0'
  refine ⟨fun a => map S.subtype (ψ a), ?_, ?_, ?_, ?_⟩
  · intro a α
    rw [coeff_map]
    exact (coeff α (ψ a)).2
  · intro a
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hψ0 a]
    rfl
  · intro a
    have key := map_subst hsψ (h := S.subtype) (Θ' a)
    rw [hΘ', hψΘ a, map_X] at key
    exact key.symm
  · intro a
    have key := map_subst hsΘ (h := S.subtype) (ψ a)
    have e : (fun s => map S.subtype (Θ' s)) = Θ := funext hΘ'
    rw [e, hΘψ a, map_X] at key
    exact key.symm

end GlobalTheory.IntInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmicGroupLawSplitByIdempotent
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IdemImage

open MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

def lin {m n : ℕ} (N : Matrix (Fin m) (Fin n) C) : Fin m → MvPowerSeries (Fin n) C :=
  fun a => ∑ b, N a b • X b

theorem lin_const {m n : ℕ} (N : Matrix (Fin m) (Fin n) C) (a : Fin m) : constantCoeff (lin N a) = 0 := by
  simp [lin]

theorem lin_hs {m n : ℕ} (N : Matrix (Fin m) (Fin n) C) : HasSubst (lin N) :=
  hasSubst_of_constantCoeff_zero (lin_const N)

theorem int_comb {σ ι : Type} [Fintype ι] {c : ι → C} (hc : ∀ i, IsIntV v (c i))
    {f : ι → MvPowerSeries σ C} (hf : ∀ i, MvIsInt v (f i)) : MvIsInt v (∑ i, c i • f i) :=
  (ptIntSer v σ).sum_mem fun i _ => ptIntSer_smul (hc i) (hf i)

theorem lin_int {m n : ℕ} {N : Matrix (Fin m) (Fin n) C} (h : ∀ a b, IsIntV v (N a b)) (a : Fin m) :
    MvIsInt v (lin N a) := int_comb (h a) fun b => ptIntSer_X b

theorem lin_coeff {m n : ℕ} (N : Matrix (Fin m) (Fin n) C) (a : Fin m) (i : Fin n) :
    coeff (Finsupp.single i 1) (lin N a) = N a i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [lin, map_sum, pt_coeff_single_X]

theorem const_comb {σ ι : Type} [Fintype ι] (c : ι → C) {f : ι → MvPowerSeries σ C}
    (hf : ∀ i, constantCoeff (f i) = 0) : constantCoeff (∑ i, c i • f i) = 0 := by
  simp [hf]

theorem comb_comb {σ : Type} {l m n : ℕ} (A : Matrix (Fin l) (Fin m) C) (B : Matrix (Fin m) (Fin n) C)
    (f : Fin n → MvPowerSeries σ C) (b : Fin l) :
    ∑ a, A b a • ∑ e, B a e • f e = ∑ e, (A * B) b e • f e := by
  simp only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem comb_one {σ : Type} {n : ℕ} (f : Fin n → MvPowerSeries σ C) (b : Fin n) :
    ∑ e, (1 : Matrix (Fin n) (Fin n) C) b e • f e = f b := by
  simp [Matrix.one_apply, ite_smul]

theorem subst_lin {σ : Type} {m n : ℕ} {s : Fin n → MvPowerSeries σ C} (hs : HasSubst s)
    (N : Matrix (Fin m) (Fin n) C) (a : Fin m) : subst s (lin N a) = ∑ b, N a b • s b := by
  rw [lin, subst_sum_smul hs]
  simp only [subst_X hs]

theorem coeff_comb_lg {d m n : ℕ} (G : LogFGL v d) (N : Matrix (Fin m) (Fin d) C)
    (L : Matrix (Fin d) (Fin n) C) (a : Fin m) (i : Fin n) :
    coeff (Finsupp.single i 1) (∑ e, N a e • (subst (lin L) (G.lg e) : MvPowerSeries (Fin n) C)) = (N * L) a i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, pt_coeff_single_subst (lin_hs L) (lin_const L) (G.lg_const _), G.lg_lin, lin_coeff,
    Matrix.mul_apply]

theorem lg_add {σ : Type} [Finite σ] {d : ℕ} (G : LogFGL v d) {x y : Fin d → MvPowerSeries σ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) (a : Fin d) :
    subst (fun b => (subst (Sum.elim x y) (G.F b) : MvPowerSeries σ C)) (G.lg a) =
      subst x (G.lg a) + subst y (G.lg a) := by
  have hs : HasSubst (Sum.elim x y) := hasSubst_of_constantCoeff_zero (by rintro (b | b) <;> simp [hx, hy])
  have hl : HasSubst (fun b : Fin d => (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hr : HasSubst (fun b : Fin d => (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero (fun _ => by simp)
  rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero G.F_const) hs, G.lg_F, subst_add hs,
    subst_comp_subst_apply hl hs, subst_comp_subst_apply hr hs]
  simp only [subst_X hs, Sum.elim_inl, Sum.elim_inr]

theorem add_const {σ : Type} {d : ℕ} (G : LogFGL v d) {x y : Fin d → MvPowerSeries σ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) (b : Fin d) :
    constantCoeff (subst (Sum.elim x y) (G.F b) : MvPowerSeries σ C) = 0 :=
  have h : ∀ s, constantCoeff (Sum.elim x y s) = 0 := by rintro (b | b) <;> simp [hx, hy]
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h) h (G.F_const b)

theorem add_int {σ : Type} {d : ℕ} (G : LogFGL v d) {x y : Fin d → MvPowerSeries σ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0)
    (ix : ∀ a, MvIsInt v (x a)) (iy : ∀ a, MvIsInt v (y a)) (b : Fin d) :
    MvIsInt v (subst (Sum.elim x y) (G.F b) : MvPowerSeries σ C) :=
  have h : ∀ s, constantCoeff (Sum.elim x y s) = 0 := by rintro (b | b) <;> simp [hx, hy]
  ptIntSer_subst (hasSubst_of_constantCoeff_zero h) (by rintro (b | b); exacts [ix b, iy b]) (G.F_int b)

theorem lg_hom {σ : Type} {d m : ℕ} {f : MvPowerSeries (Fin d) C} {φ : Fin d → MvPowerSeries (Fin m) C}
    (h0 : ∀ a, constantCoeff (φ a) = 0) {c : Fin m → C} {g : Fin m → MvPowerSeries (Fin m) C}
    (h : subst φ f = ∑ a, c a • g a) {s : Fin m → MvPowerSeries σ C} (hs : HasSubst s) :
    subst (fun b => (subst s (φ b) : MvPowerSeries σ C)) f = ∑ a, c a • (subst s (g a) : MvPowerSeries σ C) := by
  rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero h0) hs, h, subst_sum_smul hs]

theorem exists_retraction [CharZero C] {d d' : ℕ} (G : LogFGL v d) {I : Matrix (Fin d) (Fin d') C}
    {P : Matrix (Fin d') (Fin d) C} (hI : ∀ a b, IsIntV v (I a b)) (hP : ∀ a b, IsIntV v (P a b))
    (hPI : P * I = 1) {φ ψ : Fin d → MvPowerSeries (Fin d) C} (hφ : IsIntHom G G φ (I * P))
    (hψ : IsIntHom G G ψ (1 - I * P)) :
    ∃ q : Fin d' → MvPowerSeries (Fin d) C, (∀ b, constantCoeff (q b) = 0) ∧ (∀ b, MvIsInt v (q b)) ∧
      ∀ b, subst q (∑ a, P b a • (subst (lin I) (G.lg a) : MvPowerSeries (Fin d') C)) = ∑ a, P b a • G.lg a := by
  have hMi : ∀ a b, IsIntV v ((I * P) a b) := fun a b => by
    rw [Matrix.mul_apply]
    exact (ptIntSub v).sum_mem fun c _ => (ptIntSub v).mul_mem (hI a c) (hP c b)
  have hNi : ∀ a b, IsIntV v ((1 - I * P : Matrix (Fin d) (Fin d) C) a b) := fun a b => by
    rw [Matrix.sub_apply, Matrix.one_apply]
    refine (ptIntSub v).sub_mem ?_ (hMi a b)
    split_ifs
    exacts [(ptIntSub v).one_mem, (ptIntSub v).zero_mem]
  have hPM : P * (I * P) = P := by rw [← Matrix.mul_assoc, hPI, Matrix.one_mul]
  have hPN : P * (1 - I * P : Matrix (Fin d) (Fin d) C) = 0 := by rw [Matrix.mul_sub, hPM, Matrix.mul_one, sub_self]
  have hMM : I * P * (I * P) = I * P := by rw [Matrix.mul_assoc, hPM]
  have hsq : I * P * (I * P) + (1 - I * P : Matrix (Fin d) (Fin d) C) * (1 - I * P : Matrix (Fin d) (Fin d) C) = 1 := by
    rw [mul_sub, sub_mul, sub_mul, hMM]; simp
  generalize hM : I * P = M at *
  generalize (1 - M : Matrix (Fin d) (Fin d) C) = N at *
  set x : Fin d → MvPowerSeries (Fin d) C := fun a => subst (lin M) (φ a) with hx
  set y : Fin d → MvPowerSeries (Fin d) C := fun a => subst (lin N) (ψ a) with hy
  have x0 : ∀ a, constantCoeff (x a) = 0 := fun a =>
    constantCoeff_subst_eq_zero (lin_hs M) (lin_const M) (hφ.1 a)
  have y0 : ∀ a, constantCoeff (y a) = 0 := fun a =>
    constantCoeff_subst_eq_zero (lin_hs N) (lin_const N) (hψ.1 a)
  have xi : ∀ a, MvIsInt v (x a) := fun a => ptIntSer_subst (lin_hs M) (lin_int hMi) (hφ.2.1 a)
  have yi : ∀ a, MvIsInt v (y a) := fun a => ptIntSer_subst (lin_hs N) (lin_int hNi) (hψ.2.1 a)
  set Θ : Fin d → MvPowerSeries (Fin d) C := fun b => subst (Sum.elim x y) (G.F b) with hΘ
  have Θ0 : ∀ a, constantCoeff (Θ a) = 0 := add_const G x0 y0
  have Θs : HasSubst Θ := hasSubst_of_constantCoeff_zero Θ0
  have hlg : ∀ a, subst Θ (G.lg a) = ∑ e, M a e • (subst (lin M) (G.lg e) : MvPowerSeries (Fin d) C) +
      ∑ e, N a e • (subst (lin N) (G.lg e) : MvPowerSeries (Fin d) C) := fun a => by
    rw [hΘ, lg_add G x0 y0, hx, hy, lg_hom hφ.1 (hφ.2.2 a) (lin_hs M), lg_hom hψ.1 (hψ.2.2 a) (lin_hs N)]
  have Θ1 : ∀ a b, coeff (Finsupp.single b 1) (Θ a) = if a = b then 1 else 0 := fun a b => by
    have h := congrArg (coeff (Finsupp.single b 1)) (hlg a)
    rw [map_add (f := _), coeff_comb_lg, coeff_comb_lg, ← Matrix.add_apply, hsq, Matrix.one_apply,
      pt_coeff_single_subst Θs Θ0 (G.lg_const a)] at h
    simpa [G.lg_lin] using h
  obtain ⟨Ψ, Ψi, Ψ0, hΨ, -⟩ := GlobalTheory.IntInv.exists_int_inv C v d Θ (add_int G x0 y0 xi yi) Θ0 Θ1
  have Ψs : HasSubst Ψ := hasSubst_of_constantCoeff_zero Ψ0
  refine ⟨fun b => ∑ a, P b a • Ψ a, fun b => const_comb _ Ψ0, fun b => int_comb (hP b) Ψi, fun b => ?_⟩
  have key : subst (lin P) (∑ a, P b a • (subst (lin I) (G.lg a) : MvPowerSeries (Fin d') C)) =
      subst Θ (∑ a, P b a • G.lg a) := by
    have hl : (fun a => (subst (lin P) (lin I a) : MvPowerSeries (Fin d) C)) = lin M := by
      funext a
      rw [subst_lin (lin_hs P), ← hM]
      exact comb_comb I P _ a
    rw [subst_sum_smul (lin_hs P), subst_sum_smul Θs]
    simp only [hlg, smul_add, Finset.sum_add_distrib, comb_comb, hPM, hPN,
      subst_comp_subst_apply (lin_hs I) (lin_hs P), hl]
    simp
  have h := congrArg (subst Ψ) key
  rw [subst_comp_subst_apply (lin_hs P) Ψs, subst_comp_subst_apply Θs Ψs] at h
  simp only [subst_lin Ψs, hΨ] at h
  rw [h, show (fun a => (X a : MvPowerSeries (Fin d) C)) = X from rfl, subst_self]
  rfl

theorem exists_image (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d d' : ℕ) (G : LogFGL v d)
    (I : Matrix (Fin d) (Fin d') C) (P : Matrix (Fin d') (Fin d) C) (hI : ∀ a b, IsIntV v (I a b))
    (hP : ∀ a b, IsIntV v (P a b)) (hPI : P * I = 1) (hφ : ∃ φ, IsIntHom G G φ (I * P))
    (hψ : ∃ ψ, IsIntHom G G ψ (1 - I * P)) :
    ∃ G' : LogFGL v d', (∃ j, IsIntHom G' G j I) ∧ ∃ q, IsIntHom G G' q P := by
  obtain ⟨φ, hφ⟩ := hφ
  obtain ⟨ψ, hψ⟩ := hψ
  obtain ⟨q, q0, qi, hq⟩ := exists_retraction G hI hP hPI hφ hψ
  set lg' : Fin d' → MvPowerSeries (Fin d') C := fun b => ∑ a, P b a • subst (lin I) (G.lg a) with hlg'
  set j : Fin d → MvPowerSeries (Fin d') C := fun a => subst (lin I) (φ a) with hjdef
  have j0 : ∀ a, constantCoeff (j a) = 0 := fun a =>
    constantCoeff_subst_eq_zero (lin_hs I) (lin_const I) (hφ.1 a)
  have ji : ∀ a, MvIsInt v (j a) := fun a => ptIntSer_subst (lin_hs I) (lin_int hI) (hφ.2.1 a)
  have hj : ∀ a, subst j (G.lg a) = ∑ e, I a e • lg' e := fun a => by
    rw [hjdef, lg_hom hφ.1 (hφ.2.2 a) (lin_hs I), hlg']
    exact (comb_comb I P _ a).symm
  have hl0 : ∀ b : Fin d', constantCoeff (X (Sum.inl b) : MvPowerSeries (Fin d' ⊕ Fin d') C) = 0 := fun _ => by simp
  have hr0 : ∀ b : Fin d', constantCoeff (X (Sum.inr b) : MvPowerSeries (Fin d' ⊕ Fin d') C) = 0 := fun _ => by simp
  have hl := hasSubst_of_constantCoeff_zero hl0
  have hr := hasSubst_of_constantCoeff_zero hr0
  set x : Fin d → MvPowerSeries (Fin d' ⊕ Fin d') C := fun a => subst (fun b => X (Sum.inl b)) (j a) with hx
  set y : Fin d → MvPowerSeries (Fin d' ⊕ Fin d') C := fun a => subst (fun b => X (Sum.inr b)) (j a) with hy
  have x0 : ∀ a, constantCoeff (x a) = 0 := fun a => constantCoeff_subst_eq_zero hl hl0 (j0 a)
  have y0 : ∀ a, constantCoeff (y a) = 0 := fun a => constantCoeff_subst_eq_zero hr hr0 (j0 a)
  have xi : ∀ a, MvIsInt v (x a) := fun a => ptIntSer_subst hl (fun _ => ptIntSer_X _) (ji a)
  have yi : ∀ a, MvIsInt v (y a) := fun a => ptIntSer_subst hr (fun _ => ptIntSer_X _) (ji a)
  have s0 := add_const G x0 y0
  have ss := hasSubst_of_constantCoeff_zero s0
  refine ⟨{ lg := lg'
            lg_const := fun b => const_comb _ fun a =>
              constantCoeff_subst_eq_zero (lin_hs I) (lin_const I) (G.lg_const a)
            lg_lin := fun a b => by rw [hlg', coeff_comb_lg, hPI, Matrix.one_apply]
            F := fun b => subst (fun a => (subst (Sum.elim x y) (G.F a) : MvPowerSeries (Fin d' ⊕ Fin d') C)) (q b)
            F_int := fun b => ptIntSer_subst ss (add_int G x0 y0 xi yi) (qi b)
            F_const := fun b => constantCoeff_subst_eq_zero ss s0 (q0 b)
            lg_F := fun b => ?_ }, ⟨j, j0, ji, hj⟩, q, q0, qi, hq⟩
  rw [lg_hom q0 (hq b) ss]
  simp only [lg_add G x0 y0, smul_add, Finset.sum_add_distrib]
  simp only [hx, hy, lg_hom j0 (hj _) hl, lg_hom j0 (hj _) hr, comb_comb, hPI, comb_one]

end GlobalTheory.IdemImage
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmicGroupLawSplitByIdempotentStatement
open NumberField MvPowerSeries IsLocalRing ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logarithmic_group_law_split_by_idempotent : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)), ∀ (d d' : ℕ) (G : LogFGL v d) (I : Matrix (Fin d) (Fin d') C) (P : Matrix (Fin d') (Fin d) C), (∀ a b, IsIntV v (I a b)) → (∀ a b, IsIntV v (P a b)) → P * I = 1 → (∃ φ, IsIntHom G G φ (I * P)) → (∃ ψ, IsIntHom G G ψ (1 - I * P)) → ∃ G' : LogFGL v d', (∃ j, IsIntHom G' G j I) ∧ ∃ q, IsIntHom G G' q P := by
  first | exact @GlobalTheory.IdemImage.exists_image | exact GlobalTheory.IdemImage.exists_image | (intros; apply GlobalTheory.IdemImage.exists_image <;> assumption)
end
end
