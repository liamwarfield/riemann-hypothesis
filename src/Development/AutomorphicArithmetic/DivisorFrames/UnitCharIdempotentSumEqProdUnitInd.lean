module

public import Development.AutomorphicArithmetic.LocalEmbeddings.ComplEquivEvW
public import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalWeilOperatorsSupportedAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairFrameBlocksDetAndNegTranspose
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMixedLagrangianChartIntegralRowChange

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.UnitCharIdempotentSumEqProdUnitInd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem cpt_finAd {D : D7} (Q : Pl D.host.E) (z : AE D) :
    cpt (D := D) Q (toEAf D z) = GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D z) Q := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero, RingHom.map_zero, RingEquiv.map_zero]; rfl
  | tmul a x =>
    have h1 := congrArg (fun s : FiniteAdeleRing (𝓞 D.host.E) D.host.E => s Q) (toAd_spec D x a.2)
    have h2 := congrArg (fun s : FiniteAdeleRing (𝓞 D.host.E) D.host.E => s Q)
      ((GlobalTheory.LFun.toFinAd_tmul (F := D.host.F) a.2 x).trans (mul_comm _ _))
    exact h1.trans h2.symm
  | add a b ha hb => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), RingHom.map_add (f := _), RingEquiv.map_add (e := _), ha, hb]; rfl

private theorem cpt_loc {D : D7} (w Q : Pl D.host.E) (y : (Kw w)ˣ) :
    cpt (D := D) Q (toEAf D (GlobalTheory.LFun.locIdele D.host.F w y : AE D)) =
      (Neutral.B1.finiteSingle D.host.E w (y : Kw w)) Q := by
  rw [cpt_finAd]
  exact congrArg (fun z : FiniteAdeleRing (𝓞 D.host.E) D.host.E => z Q) (GlobalTheory.LFun.finTens_locIdele (F := D.host.F) w y)

open Classical in
private theorem cpt_sum {D : D7} {P : Finset (Pl D.host.E)} {e : AE D} (he : IsIdemSum e P) (Q : Pl D.host.E) :
    cpt (D := D) Q (toEAf D e) = if Q ∈ P then 1 else 0 := by
  obtain ⟨⟨es, hes, hsum⟩, -⟩ := he
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hsum, map_sum (toEAf D), map_sum (cpt (D := D) Q)]
  split_ifs with hQ
  · rw [Finset.sum_eq_single Q (fun P hP hPQ => (cpt_of_isIdemAt (hes P hP)).2 Q (Ne.symm hPQ))
      (fun h => absurd hQ h)]
    exact (cpt_of_isIdemAt (hes Q hQ)).1
  · exact Finset.sum_eq_zero fun P hP => (cpt_of_isIdemAt (hes P hP)).2 Q (fun h => hQ (h ▸ hP))

private theorem cpt_prod {D : D7} {ι : Type} [Fintype ι] (w : ι → Pl D.host.E) (hw : Function.Injective w)
    (y : ∀ i, (Kw (w i))ˣ) :
    infPart D ((∏ i, GlobalTheory.LFun.locIdele D.host.F (w i) (y i) : (AE D)ˣ) : AE D) = 1 ∧
    (∀ i, cpt (D := D) (w i) (toEAf D ((∏ i, GlobalTheory.LFun.locIdele D.host.F (w i) (y i) : (AE D)ˣ) : AE D)) = y i) ∧
    ∀ Q, (∀ i, w i ≠ Q) → cpt (D := D) Q (toEAf D ((∏ i, GlobalTheory.LFun.locIdele D.host.F (w i) (y i) : (AE D)ˣ) : AE D)) = 1 := by
  refine ⟨?_, fun i => ?_, fun Q hQ => ?_⟩
  · rw [Units.coe_prod, map_prod (infPart D)]
    exact Finset.prod_eq_one fun i _ => GlobalTheory.LFun.infTens_locIdele (F := D.host.F) (w i) _
  · rw [Units.coe_prod, map_prod (toEAf D), map_prod (cpt (D := D) _), Finset.prod_eq_single i]
    · rw [cpt_loc, GlobalTheory.LFun.finSingle_self]
    · intro b _ hb
      rw [cpt_loc]
      exact GlobalTheory.LFun.finSingle_ne (fun h => hb (hw h).symm) _
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [Units.coe_prod, map_prod (toEAf D), map_prod (cpt (D := D) _)]
    exact Finset.prod_eq_one fun i _ => by
      rw [cpt_loc]
      exact GlobalTheory.LFun.finSingle_ne (hQ i).symm _

private theorem valued_evW {D : D7} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (z : Lev.EAf D) :
    Valued.v (GlobalTheory.BotMatch.evW τ z) = Valued.v (cpt (D := D) (splitPrime τ) z) := by
  rw [← GlobalTheory.BotMatch.complEquiv_evW, complEquiv_apply, SplitTie.valued_complMap]

theorem UpperTheory.unitChar_idempotentSum_eq_prod_unitInd :
    ∀ (D : D7) (ε : AE D) (Pw : Finset (Pl D.host.E)), IsIdemSum ε Pw → ∀ (ι : Type) [Fintype ι] (pl : ι → Pl D.host.F)
        (τ : ∀ i, D.host.E →ₐ[D.host.F] Fv D.host.F (pl i)), (∀ w, w ∈ Pw ↔ ∃ i, splitPrime (τ i) = w) →
        Function.Injective (fun i => splitPrime (τ i)) → ∀ (ν : (AE D)ˣ →* Circle) (n : ℕ) (N : Matrix (Fin n) (Fin n) (Lev.EAf D)),
          (∀ i, GlobalTheory.BotMatch.evW (τ i) N.det ∈ 𝒪[Fv D.host.F (pl i)]) →
          GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar ν ε N = ∏ i, GlobalTheory.StdPairCone.unitInd (chrW ν (τ i)) (GlobalTheory.BotMatch.evW (τ i) N.det) := by
  intro D ε Pw hε ι _ pl τ hPw hinj ν n N hN
  classical
  have hc : ∀ Q, cpt (D := D) Q (1 - toEAf D ε + toEAf D ε * N.det) = if Q ∈ Pw then cpt (D := D) Q N.det else 1 := by
    intro Q
    rw [RingHom.map_add (f := _), RingHom.map_sub, RingHom.map_mul, RingHom.map_one, cpt_sum hε]
    split_ifs <;> simp
  by_cases h : ∀ i, GlobalTheory.BotMatch.evW (τ i) N.det ≠ 0 ∧ valuation (Fv D.host.F (pl i)) (GlobalTheory.BotMatch.evW (τ i) N.det) = 1
  · let y : ∀ i, (Kw (D := D) (splitPrime (τ i)))ˣ := fun i =>
      Units.map (complMap (splitPrime_under (τ i))).toMonoidHom (Units.mk0 _ (h i).1)
    have hy : ∀ i, (y i : Kw (D := D) (splitPrime (τ i))) = cpt (D := D) (splitPrime (τ i)) N.det := fun i =>
      GlobalTheory.BotMatch.complEquiv_evW (τ i) N.det
    have hv : ∀ i, Valued.v (y i : Kw (D := D) (splitPrime (τ i))) = 1 := fun i => by
      rw [hy, ← valued_evW]
      exact (GlobalTheory.FlipMatch.isEquiv_Fv (pl i)).eq_one_iff_eq_one.1 (h i).2
    obtain ⟨x, hx⟩ : ∃ x : (AE D)ˣ, x = ∏ i, GlobalTheory.LFun.locIdele D.host.F (splitPrime (τ i)) (y i) := ⟨_, rfl⟩
    obtain ⟨h1, h2, h3⟩ := cpt_prod (fun i => splitPrime (τ i)) hinj y
    obtain ⟨-, h5, h6⟩ := cpt_prod (fun i => splitPrime (τ i)) hinj (fun i => (y i)⁻¹)
    have hxi : x⁻¹ = ∏ i, GlobalTheory.LFun.locIdele D.host.F (splitPrime (τ i)) (y i)⁻¹ := by
      rw [hx, ← Finset.prod_inv_distrib]
      exact Finset.prod_congr rfl fun i _ => (map_inv _ _).symm
    rw [← hx] at h1 h2 h3
    rw [← hxi] at h5 h6
    have hU : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet ε N x := by
      refine ⟨h1, cpt_ext fun Q => ?_, (mem_OA_iff _).2 fun Q => ?_⟩
      · rw [hc]
        split_ifs with hQ
        · obtain ⟨i, rfl⟩ := (hPw Q).1 hQ
          exact (h2 i).trans (hy i)
        · exact h3 Q fun i hi => hQ ((hPw Q).2 ⟨i, hi⟩)
      · by_cases hQ : ∃ i, splitPrime (τ i) = Q
        · obtain ⟨i, rfl⟩ := hQ
          rw [h5 i, HeightOneSpectrum.mem_adicCompletionIntegers, Units.val_inv_eq_inv_val, map_inv₀, hv, inv_one]
        · rw [h6 Q fun i hi => hQ ⟨i, hi⟩]
          exact one_mem _
    have hex : ∃ x, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.IsUnitDet ε N x := ⟨x, hU⟩
    have he : hex.choose = x := Units.ext (ae_ext (hex.choose_spec.1.trans hU.1.symm) fun Q => by
      rw [hex.choose_spec.2.1, hU.2.1])
    rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar, dite_eq_left hex, he, hx, map_prod ν, ← Finset.prod_inv_distrib]
    refine (map_prod Circle.coeHom _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
    rw [GlobalTheory.StdPairCone.unitInd, dite_eq_left (h i)]
    rfl
  · obtain ⟨i, hi⟩ := not_forall.1 h
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [GlobalTheory.StdPairCone.unitInd, dite_eq_right hi]),
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar, dite_eq_right]
    rintro ⟨x, -, h2, h3⟩
    apply hi
    have h4 := (mem_OA_iff _).1 h3 (splitPrime (τ i))
    have h5 : cpt (D := D) (splitPrime (τ i)) (toEAf D (x : AE D)) = cpt (D := D) (splitPrime (τ i)) N.det := by
      rw [h2, hc, if_pos ((hPw _).2 ⟨i, rfl⟩)]
    have h6 : cpt (D := D) (splitPrime (τ i)) N.det * cpt (D := D) (splitPrime (τ i)) (toEAf D ((x⁻¹ : (AE D)ˣ) : AE D)) = 1 := by
      rw [← h5, ← RingHom.map_mul, ← RingHom.map_mul, Units.mul_inv, RingHom.map_one, RingHom.map_one]
    have h7 : Valued.v (cpt (D := D) (splitPrime (τ i)) N.det) ≤ 1 := by
      rw [← valued_evW]
      exact (GlobalTheory.FlipMatch.isEquiv_Fv (pl i)).le_one_iff_le_one.1 ((Valuation.mem_integer_iff _ _).1 (hN i))
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at h4
    have h8 := congrArg Valued.v h6
    rw [map_mul, map_one] at h8
    have h9 : Valued.v (GlobalTheory.BotMatch.evW (τ i) N.det) = 1 := by
      rw [valued_evW]
      exact le_antisymm h7 (h8 ▸ mul_le_of_le_one_right' h4)
    exact ⟨fun h0 => by rw [h0, map_zero] at h9; exact zero_ne_one h9,
      (GlobalTheory.FlipMatch.isEquiv_Fv (pl i)).eq_one_iff_eq_one.2 h9⟩
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.MemIntAdelesAndIdealIffSplitEmbeddings
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem cpt_incl {D : D7} (Q : Pl D.host.E) (x : D.host.E) :
    cpt (D := D) Q (x ⊗ₜ[D.host.F] 1) = algebraMap D.host.E (Q.adicCompletion D.host.E) x := by
  show (toAd D (x ⊗ₜ[D.host.F] 1)) Q = _
  rw [GlobalTheory.AdeleBaseChange.map_tmul_one (toAd_spec D)]
  rfl

private theorem val_oToS {D : D7} (Q : Pl D.host.E) (a : 𝓞 D.host.E) :
    Valued.v (cpt (D := D) Q (oToS D.host.F D.host.E a : Lev.EAf D)) = Q.intValuation a := by
  have h : (oToS D.host.F D.host.E a : Lev.EAf D) = (a : D.host.E) ⊗ₜ[D.host.F] 1 := rfl
  rw [h, cpt_incl, Formalism.UG.P.levelaf_valued_algebraMap]
  exact Q.valuation_of_algebraMap a

private theorem exists_exact {R : Type} [CommRing R] [IsDedekindDomain R] (Pw : Finset (HeightOneSpectrum R))
    (c : HeightOneSpectrum R → ℕ) :
    ∃ a ∈ ∏ w ∈ Pw, w.asIdeal ^ c w, ∀ w ∈ Pw, w.intValuation a = WithZero.exp (-(c w : ℤ)) := by
  choose x hx hx' using fun w : HeightOneSpectrum R =>
    Ideal.exists_mem_pow_notMem_pow_succ w.asIdeal w.ne_bot w.isPrime.ne_top (c w)
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := Pw) (fun w => w.asIdeal) (fun w => c w + 1)
    (fun w _ => w.prime) (fun i _ j _ h e => h (HeightOneSpectrum.ext e)) (fun w => x w.1)
  have h1 : ∀ w ∈ Pw, y ∈ w.asIdeal ^ c w := fun w hw => by
    have := add_mem (Ideal.pow_le_pow_right (Nat.le_succ _) (hy w hw)) (hx w)
    rwa [sub_add_cancel] at this
  have h2 : ∀ w ∈ Pw, y ∉ w.asIdeal ^ (c w + 1) := fun w hw h => hx' w (by
    have := sub_mem h (hy w hw)
    rwa [sub_sub_cancel] at this)
  refine ⟨y, ?_, fun w hw => le_antisymm ((w.intValuation_le_pow_iff_mem _ _).2 (h1 w hw)) ?_⟩
  · rw [Ideal.prod_eq_iInf_of_pairwise_isCoprime]
    · simp only [Ideal.mem_iInf]
      exact h1
    · intro P _ Q _ hPQ
      exact (HeightOneSpectrum.isCoprime_of_ne P Q hPQ).pow
  · have h3 := h2 w hw
    rw [← w.intValuation_le_pow_iff_mem, not_le] at h3
    have h0 : w.intValuation y ≠ 0 := (lt_of_le_of_lt zero_le h3).ne'
    rw [← WithZero.exp_log h0] at h3 ⊢
    rw [WithZero.exp_lt_exp] at h3
    rw [WithZero.exp_le_exp]
    push_cast at h3
    omega

private theorem le_of_mem_map {O S K Γ : Type} [CommRing O] [CommRing S] [CommRing K] [LinearOrderedCommGroupWithZero Γ]
    (f : O →+* S) (φ : S →+* K) (v : Valuation K Γ) (I : Ideal O) (γ : Γ) (h1 : ∀ s, v (φ s) ≤ 1)
    (h2 : ∀ a ∈ I, v (φ (f a)) ≤ γ) : ∀ s ∈ I.map f, v (φ s) ≤ γ := by
  intro s hs
  induction hs using Submodule.span_induction with
  | mem s hs =>
    obtain ⟨a, ha, rfl⟩ := hs
    exact h2 a ha
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _)]
    exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | smul a x _ hx =>
    rw [smul_eq_mul, map_mul, map_mul]
    exact (mul_le_mul' (h1 a) hx).trans_eq (one_mul _)

private theorem val_le_one {D : D7} (w : Pl D.host.E) (s : OA D) : Valued.v (cpt (D := D) w s.1) ≤ 1 := by
  obtain ⟨s, hs⟩ := s
  have := (mem_OA_iff s).1 hs w
  rwa [HeightOneSpectrum.mem_adicCompletionIntegers] at this

private theorem val_le_of_mem {D : D7} (w : Pl D.host.E) (I : Ideal (𝓞 D.host.E)) (γ : WithZero (Multiplicative ℤ))
    (h2 : ∀ a ∈ I, w.intValuation a ≤ γ) (z : Lev.EAf D) (h : z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hI : (⟨z, h⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) ∈ idS D.host.F I) : Valued.v (cpt (D := D) w z) ≤ γ := by
  obtain ⟨φ, hφ⟩ : ∃ φ : Formalism.L2.Herm.intAf D.host.F D.host.E →+* w.adicCompletion D.host.E,
      ∀ s, φ s = cpt (D := D) w s.1 := ⟨(cpt (D := D) w).comp (OA D).subtype, fun _ => rfl⟩
  have := le_of_mem_map (oToS D.host.F D.host.E) φ Valued.v I γ
    (fun s => by rw [hφ]; exact val_le_one w s) (fun a ha => by rw [hφ, val_oToS]; exact h2 a ha) ⟨z, h⟩ hI
  rwa [hφ] at this

private theorem inId_iff {D : D7} (Pw : Finset (Pl D.host.E)) (c : Pl D.host.E → ℕ) (z : Lev.EAf D)
    (hz : ∀ Q, Q ∉ Pw → cpt (D := D) Q z = 0) :
    GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (∏ w ∈ Pw, w.asIdeal ^ c w) z ↔
      ∀ w ∈ Pw, Valued.v (cpt (D := D) w z) ≤ WithZero.exp (-(c w : ℤ)) := by
  constructor
  · rintro ⟨h, hI⟩ w hw
    refine val_le_of_mem w _ _ (fun a ha => ?_) z h hI
    rw [w.intValuation_le_pow_iff_mem]
    exact Ideal.le_of_dvd (Finset.dvd_prod_of_mem (fun w : Pl D.host.E => w.asIdeal ^ c w) hw) ha
  · intro h
    obtain ⟨a, ha, hv⟩ := exists_exact Pw c
    have hy : ((a : D.host.E)⁻¹ ⊗ₜ[D.host.F] 1 : Lev.EAf D) * z ∈ OA D := (mem_OA_iff _).2 fun Q => by
      rw [RingHom.map_mul]
      by_cases hQ : Q ∈ Pw
      · rw [HeightOneSpectrum.mem_adicCompletionIntegers, Valuation.map_mul, cpt_incl,
          Formalism.UG.P.levelaf_valued_algebraMap, map_inv₀]
        have : Q.valuation D.host.E (a : D.host.E) = WithZero.exp (-(c Q : ℤ)) :=
          (Q.valuation_of_algebraMap a).trans (hv Q hQ)
        rw [this, inv_mul_le_one₀ (zero_lt_iff.2 WithZero.exp_ne_zero)]
        exact h Q hQ
      · rw [hz Q hQ, mul_zero]
        exact zero_mem _
    have e : z = ((oToS D.host.F D.host.E a * ⟨_, hy⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) : Lev.EAf D) := by
      refine cpt_ext fun Q => ?_
      have h : (oToS D.host.F D.host.E a : Lev.EAf D) = (a : D.host.E) ⊗ₜ[D.host.F] 1 := rfl
      rw [Subring.coe_mul, h, RingHom.map_mul, RingHom.map_mul, cpt_incl, cpt_incl]
      by_cases hQ : Q ∈ Pw
      · have h0 : (a : D.host.E) ≠ 0 := by
          intro h0
          have h1 : a = 0 := RingOfIntegers.coe_eq_zero_iff.1 h0
          have := hv Q hQ
          rw [h1, map_zero] at this
          exact WithZero.exp_ne_zero this.symm
        rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ h0, map_one, one_mul]
      · rw [hz Q hQ, mul_zero, mul_zero]
    rw [e]
    exact ⟨Subtype.property _, Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ha)⟩

private theorem val_unifAt {F : Type} [Field F] [NumberField F] (v : Pl F) :
    Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v : Fv F v) = WithZero.exp (-1 : ℤ) := by
  have e := GlobalTheory.FlipMatch.isEquiv_Fv v
  have h : valuation (Fv F v) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v : Fv F v) = uniformizer (Fv F v) :=
    (GlobalTheory.SplitFlip.exists_isUnif (k := Fv F v)).choose_spec
  refine le_antisymm ?_ ?_
  · have h1 : Valued.v (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt v : Fv F v) < 1 := e.lt_one_iff_lt_one.1 (h ▸ uniformizer_lt_one)
    rw [← WithZero.exp_zero] at h1
    exact WithZero.lt_mul_exp_iff_le (by simp) |>.1 (by simpa [← WithZero.exp_add] using h1)
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    rw [← Formalism.UG.P.levelaf_valued_algebraMap] at hπ
    rw [← hπ, ← e, h]
    exact le_uniformizer_iff.2 (e.lt_one_iff_lt_one.2 (by rw [hπ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega))

private theorem val_evW {D : D7} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (z : Lev.EAf D) :
    Valued.v (GlobalTheory.BotMatch.evW τ z) = Valued.v (cpt (D := D) (splitPrime τ) z) :=
  GlobalTheory.FlipMatch.valued_complEquiv_symm τ _

theorem UpperTheory.mem_intAdeles_and_ideal_iff_splitEmbeddings :
    ∀ (D : D7) (ε : AE D) (Pw : Finset (Pl D.host.E)), IsIdemSum ε Pw → ∀ (ι : Type) [Fintype ι] (pl : ι → Pl D.host.F)
        (τ : ∀ i, D.host.E →ₐ[D.host.F] Fv D.host.F (pl i)), (∀ w, w ∈ Pw ↔ ∃ i, splitPrime (τ i) = w) →
        Function.Injective (fun i => splitPrime (τ i)) → ∀ (c : Pl D.host.E → ℕ) (z : Lev.EAf D), toEAf D ε * z = z →
          (z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ ∀ i, GlobalTheory.BotMatch.evW (τ i) z ∈ 𝒪[Fv D.host.F (pl i)]) ∧
          (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (∏ w ∈ Pw, w.asIdeal ^ c w) z ↔
            ∀ i, GlobalTheory.BotMatch.evW (τ i) z ∈ GlobalTheory.SplitWeil.cball (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt (pl i) ^ c (splitPrime (τ i)))) := by
  intro D ε Pw hε ι _ pl τ hP _ c z hz
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := hε
  have h0 : ∀ Q, Q ∉ Pw → cpt (D := D) Q z = 0 := fun Q hQ => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hz, RingHom.map_mul, map_sum, map_sum, Finset.sum_eq_zero, zero_mul]
    intro P hP
    exact (cpt_of_isIdemAt (hes P hP)).2 Q fun e => hQ (e ▸ hP)
  constructor
  · have h1 : ∀ i, GlobalTheory.BotMatch.evW (τ i) z ∈ 𝒪[Fv D.host.F (pl i)] ↔
        cpt (D := D) (splitPrime (τ i)) z ∈ (splitPrime (τ i)).adicCompletionIntegers D.host.E := fun i => by
      rw [Valuation.mem_integer_iff, (GlobalTheory.FlipMatch.isEquiv_Fv _).le_one_iff_le_one, val_evW,
        HeightOneSpectrum.mem_adicCompletionIntegers]
    refine (mem_OA_iff z).trans ⟨fun h i => (h1 i).2 (h _), fun h Q => ?_⟩
    by_cases hQ : Q ∈ Pw
    · obtain ⟨i, rfl⟩ := (hP Q).1 hQ
      exact (h1 i).1 (h i)
    · rw [h0 Q hQ]
      exact zero_mem _
  · have h1 : ∀ i, GlobalTheory.BotMatch.evW (τ i) z ∈
        GlobalTheory.SplitWeil.cball (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.unifAt (pl i) ^ c (splitPrime (τ i))) ↔
        Valued.v (cpt (D := D) (splitPrime (τ i)) z) ≤ WithZero.exp (-(c (splitPrime (τ i)) : ℤ)) := fun i => by
      refine (GlobalTheory.FlipMatch.isEquiv_Fv (pl i) _ _).trans ?_
      rw [val_evW, Units.val_pow_eq_pow_val, map_pow, val_unifAt, ← WithZero.exp_nsmul]
      simp
    refine (inId_iff Pw c z h0).trans ⟨fun h i => (h1 i).2 (h _ ((hP _).2 ⟨i, rfl⟩)), fun h Q hQ => ?_⟩
    obtain ⟨i, rfl⟩ := (hP Q).1 hQ
    exact (h1 i).1 (h i)
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.BigPStdSchwartzTranslateEqSmallPOfIsUnif
section -- merged from Development.AutomorphicArithmetic.DivisorFrames.ShellSumEqConstOfTwistEqIndicatorDoubleCoset
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.shellSum_eq_const_of_twist_eq_indicator_double_coset :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ →
        ∀ (a : ℕ) (ν : kˣ →* ℂˣ) (z C : ℂ) (φ : Matrix (Fin a) (Fin a) k → ℂ) (g₀ g₁ : GL (Fin a) k),
        (∀ g : GL (Fin a) k, φ g.1 * (ν (GlobalTheory.SplitFlip.gdet g) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) z =
          {g : GL (Fin a) k | g₀ * g * g₁ ∈ GlobalTheory.SplitWeil.KO k (Fin a)}.indicator (fun _ => C) g) →
        GlobalTheory.SplitFlip.shellSum (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ ν z φ = C := by
  intro k _ _ _ _ _ _ ϖ hϖ a ν z C φ g₀ g₁ hφ
  letI : MeasurableSpace (GL (Fin a) k) := Units.instMeasurableSpace
  haveI : BorelSpace (GL (Fin a) k) := GlobalTheory.SplitFlip.borel_GL
  have hSm : MeasurableSet {g : GL (Fin a) k | g₀ * g * g₁ ∈ GlobalTheory.SplitWeil.KO k (Fin a)} :=
    (GlobalTheory.PureMatch.ShellVolume.isOpen_translate g₀ g₁).measurableSet
  have hvol := GlobalTheory.PureMatch.ShellVolume.finsum_vol_shell_inter_translate k a ϖ g₀ g₁ hϖ
  have hshell : ∀ m : {m : Fin a → ℤ // Antitone m},
      GlobalTheory.SplitFlip.shell (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ ν z φ m.1 =
      (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))).real (GlobalTheory.SplitFlip.shellSet ϖ m.1 ∩
        {g : GL (Fin a) k | g₀ * g * g₁ ∈ GlobalTheory.SplitWeil.KO k (Fin a)}) • C := by
    intro m
    rw [GlobalTheory.SplitFlip.shell]
    simp_rw [hφ]
    have e1 := MeasureTheory.setIntegral_indicator (μ := GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a)))
      (s := GlobalTheory.SplitFlip.shellSet ϖ m.1) (f := fun _ => C) hSm
    rw [e1, MeasureTheory.setIntegral_const]
  rw [GlobalTheory.SplitFlip.shellSum]
  simp_rw [hshell]
  rw [← finsum_smul, hvol, one_smul]
end

namespace UpperTheory.StandardFormChange
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdPairLoc GlobalTheory.StdPairCone MeasureTheory
open scoped Matrix

section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL Formalism.DoubleCosetMeasures.instMeasMat GlobalTheory.CompanionTheory.QL.instMeasGL GlobalTheory.CompanionTheory.QL.instBorelGL GroundTheory.Automorphic.GJMatrix.measurableSpace_matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

private theorem std_key (α β ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (hϖ : IsUnif ϖ) (hν : ν = α / β) (h : GL (Fin (a + a')) k) :
    bigP (haarVol (KO k (Fin a))) ϖ finSumFinEquiv ν β (stdA ν ϖ c a a') h =
      smallP (haarVol (KO k (Fin a'))) finSumFinEquiv ν α (stdB ν ϖ c a a') h := by
  rw [bigZetaIntegral_eq, smallP]
  obtain ⟨hdet, hrel⟩ := standardPair_frameBlocks_det_and_neg_transpose a a' h
  obtain ⟨hA0, hA⟩ := bigF_stdA ν ϖ c a a' hϖ
  obtain ⟨hB0, hB⟩ := smallF_stdB (k := k) ν ϖ c a a'
  by_cases h0 : (blk₁ (X0 k (finSumFinEquiv (m := a) (n := a')) * (invT h).val)).det = 0
  · have h0' : (blk₂ (Y0 k (finSumFinEquiv (m := a) (n := a')) * h.val)).det = 0 := by rw [← hdet, h0, zero_mul]
    rw [hA0 _ h0, hB0 _ h0']; simp
  · have h0' : (blk₂ (Y0 k (finSumFinEquiv (m := a) (n := a')) * h.val)).det ≠ 0 := by
      rw [← hdet]; exact mul_ne_zero h0 h.det_ne_zero
    set g₁ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ h0 with hg₁
    set g₂ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ h0' with hg₂
    rw [hA _ g₁ rfl, hB _ g₂ rfl, hrel g₁ g₂ rfl rfl, cball_neg_transpose]
    have hd : gdet g₂ = gdet g₁ * gdet h := Units.ext (by
      simp only [gdet, Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, g₁, g₂,
        Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
      exact hdet.symm)
    have hαν : α = ν * β := by rw [hν, div_mul_cancel]
    have e : apow (gdet h) ((Fintype.card (Fin a') : ℂ) / 2) * apow (gdet h) (-((Fintype.card (Fin (a + a')) : ℂ) / 2)) =
        apow (gdet h) (-(a : ℂ) / 2) := by
      rw [← apow_add]; congr 1; simp only [Fintype.card_fin]; push_cast; ring
    have e1 : (((ν (gdet g₁ * gdet h))⁻¹ : ℂˣ) : ℂ) = (((ν (gdet g₁))⁻¹ : ℂˣ) : ℂ) * (((ν (gdet h))⁻¹ : ℂˣ) : ℂ) := by
      rw [map_mul, _root_.mul_inv, Units.val_mul]
    have e2 : (α (gdet h) : ℂ) = (ν (gdet h) : ℂ) * (β (gdet h) : ℂ) := by
      rw [hαν, MonoidHom.mul_apply, Units.val_mul]
    have e3 : (ν (gdet h) : ℂ) * (((ν (gdet h))⁻¹ : ℂˣ) : ℂ) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    rw [hd, e1, apow_mul, e2]
    have key2 : ∀ B V Vi Vhi P1 Pa' PN I : ℂ, V * Vhi = 1 →
        B * (Pa' * PN) * (Vi * P1 * I) = V * B * Pa' * (Vi * Vhi * (P1 * PN) * I) := by
      intro B V Vi Vhi P1 Pa' PN I hV; linear_combination (-(B * Pa' * PN * Vi * P1 * I)) * hV
    rw [← e]
    exact key2 _ _ _ _ _ _ _ _ e3

private theorem std_ne (β ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (hϖ : IsUnif ϖ) :
    bigP (haarVol (KO k (Fin a))) ϖ finSumFinEquiv ν β (stdA ν ϖ c a a') 1 ≠ 0 := by
  intro h1
  obtain ⟨-, hA⟩ := bigF_stdA ν ϖ c a a' hϖ
  rw [bigZetaIntegral_eq, hA _ 1 ?_] at h1
  · simp [Set.indicator, gdet, cball, blk₂, X0] at h1
    obtain ⟨i, j, hij⟩ := h1
    have hne : Fin.castAdd a' i ≠ Fin.natAdd a j := by
      intro e; have := congrArg Fin.val e; simp at this; omega
    simp [hne] at hij
  · ext i j
    simp [blk₁, X0, invT_val, Matrix.one_apply]

private theorem bigF_change (ν : kˣ →* ℂˣ) (ϖ : kˣ) (c a a' : ℕ) (hϖ : IsUnif ϖ) (g : GL (Fin a) k)
    (M : Matrix (Fin (a + a')) (Fin (a + a')) k) (X : Matrix (Fin a) (Fin (a + a')) k) :
    bigF (haarVol (KO k (Fin a))) ϖ ν (fun Y : Matrix (Fin a) (Fin (a + a')) k => stdA ν ϖ c a a' (g.1 * Y * M)) X =
      ((ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2))⁻¹ *
        bigF (haarVol (KO k (Fin a))) ϖ ν (stdA ν ϖ c a a') (X * M) := by
  obtain ⟨hA0, hA⟩ := bigF_stdA ν ϖ c a a' hϖ
  have has : ∀ y : GL (Fin a) k, g.1 * (y.1 * X) * M = (g * y).1 * (X * M) := fun y => by
    simp only [Units.val_mul, Matrix.mul_assoc]
  by_cases h0 : (blk₁ (X * M)).det = 0
  · rw [hA0 _ h0, mul_zero]
    have h1 : ∀ y : GL (Fin a) k, stdA ν ϖ c a a' (g.1 * (y.1 * X) * M) = 0 := fun y => by
      rw [has, stdA, dite_eq_right]
      rintro ⟨h, -⟩
      exact h (by rw [blk₁_mul, Matrix.det_mul, h0, mul_zero])
    simp [bigF, shellSum, shell, h1]
  · set g₁ := Matrix.GeneralLinearGroup.mkOfDetNeZero _ h0 with hg₁
    have hg : g₁.val = blk₁ (X * M) := rfl
    rw [hA _ g₁ hg]
    unfold bigF
    refine UpperTheory.shellSum_eq_const_of_twist_eq_indicator_double_coset k ϖ hϖ a ν _ _ _ g g₁ fun y => ?_
    have H := integrand_eq ν (ϖ ^ c) ((Fintype.card (Fin (a + a')) : ℂ) / 2) (blk₂ (X * M)) g₁ (g * y)
      (stdA ν ϖ c a a' ((g * y).1 * (X * M))) (fun h => ?_) (fun h => ?_)
    · have hne : (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2) ≠ 0 :=
        mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
      have H2 : stdA ν ϖ c a a' (g.1 * (y.1 * X) * M) * (ν (gdet y) : ℂ) * apow (gdet y) ((Fintype.card (Fin (a + a')) : ℂ) / 2) =
          ((ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2))⁻¹ *
            (stdA ν ϖ c a a' ((g * y).1 * (X * M)) * (ν (gdet (g * y)) : ℂ) *
              apow (gdet (g * y)) ((Fintype.card (Fin (a + a')) : ℂ) / 2)) := by
        rw [eq_inv_mul_iff_mul_eq₀ hne, has, gdet_mul, map_mul, apow_mul, Units.val_mul (ν (gdet g))]
        ring
      refine H2.trans ?_
      rw [H]
      by_cases hy : g * y * g₁ ∈ KO k (Fin a)
      · rw [Set.indicator_of_mem (show g * y ∈ (fun g => g * g₁) ⁻¹' (KO k (Fin a) : Set (GL (Fin a) k)) from hy),
          Set.indicator_of_mem (show y ∈ {y : GL (Fin a) k | g * y * g₁ ∈ KO k (Fin a)} from hy)]
      · rw [Set.indicator_of_notMem (show g * y ∉ (fun g => g * g₁) ⁻¹' (KO k (Fin a) : Set (GL (Fin a) k)) from hy),
          Set.indicator_of_notMem (show y ∉ {y : GL (Fin a) k | g * y * g₁ ∈ KO k (Fin a)} from hy), mul_zero]
    · have h' : (blk₁ ((g * y).val * (X * M))).det ≠ 0 ∧ IsGLO (blk₁ ((g * y).val * (X * M))) ∧
          ∀ i j, blk₂ ((g * y).val * (X * M)) i j ∈ cball (ϖ ^ c) := by
        rw [blk₁_mul, blk₂_mul, ← hg]; exact h
      rw [stdA, dite_eq_left h']
      congr 3
    · rw [stdA, dite_eq_right]
      rwa [blk₁_mul, blk₂_mul, ← hg]

private theorem smallF_change (ν : kˣ →* ℂˣ) (a' d : ℕ) (Ψ : Matrix (Fin a') (Fin d) k → ℂ) (l : ℂ) (g : GL (Fin a') k)
    (M : Matrix (Fin d) (Fin d) k) (Y : Matrix (Fin a') (Fin d) k) :
    smallF (haarVol (KO k (Fin a'))) ν (l • fun Y : Matrix (Fin a') (Fin d) k => Ψ (g.1 * Y * M)) Y =
      l * ((ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2))⁻¹ *
        smallF (haarVol (KO k (Fin a'))) ν Ψ (Y * M) := by
  have hne : (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2) ≠ 0 :=
    mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
  unfold smallF
  rw [← integral_mul_left_eq_self (fun y : GL (Fin a') k =>
    Ψ (y.val * (Y * M)) * (ν (gdet y) : ℂ) * apow (gdet y) ((Fintype.card (Fin d) : ℂ) / 2)) g, ← integral_const_mul]
  congr 1
  funext a
  simp only [Pi.smul_apply, smul_eq_mul, gdet_mul, map_mul, Units.val_mul, apow_mul,
    Matrix.mul_assoc]
  field_simp [apow_ne_zero]
  <;> ring

private theorem main (ϖ : kˣ) (hϖ : IsUnif ϖ) (α β ν : kˣ →* ℂˣ) (hν : ν = α / β) (c a a' : ℕ) (g : GL (Fin a) k)
    (g' : GL (Fin a') k) (κ : GL (Fin (a + a')) k) :
    bigP (haarVol (KO k (Fin a))) ϖ finSumFinEquiv ν β
        (fun Y : Matrix (Fin a) (Fin (a + a')) k => stdA ν ϖ c a a' (g.1 * Y * κ.1ᵀ)) ≠ 0 ∧
      ∃ l : ℂ, bigP (haarVol (KO k (Fin a))) ϖ finSumFinEquiv ν β
          (fun Y : Matrix (Fin a) (Fin (a + a')) k => stdA ν ϖ c a a' (g.1 * Y * κ.1ᵀ)) =
        smallP (haarVol (KO k (Fin a'))) finSumFinEquiv ν α
          (l • fun Y : Matrix (Fin a') (Fin (a + a')) k => stdB ν ϖ c a a' (g'.1 * Y * (κ⁻¹).1)) := by
  set A : ℂ := ((ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin (a + a')) : ℂ) / 2))⁻¹ *
    ((β (gdet κ) : ℂ) * apow (gdet κ) (-(a : ℂ) / 2)) with hA
  set B : ℂ := ((ν (gdet g') : ℂ) * apow (gdet g') ((Fintype.card (Fin (a + a')) : ℂ) / 2))⁻¹ *
    ((α (gdet κ) : ℂ) * apow (gdet κ) ((Fintype.card (Fin a') : ℂ) / 2)) with hB
  have hA0 : A ≠ 0 := mul_ne_zero (inv_ne_zero (mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)))
    (mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _))
  have hB0 : B ≠ 0 := mul_ne_zero (inv_ne_zero (mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)))
    (mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _))
  have h1 : ∀ u : GL (Fin (a + a')) k, bigP (haarVol (KO k (Fin a))) ϖ finSumFinEquiv ν β
      (fun Y : Matrix (Fin a) (Fin (a + a')) k => stdA ν ϖ c a a' (g.1 * Y * κ.1ᵀ)) (u * κ) =
      A * bigP (haarVol (KO k (Fin a))) ϖ finSumFinEquiv ν β (stdA ν ϖ c a a') u := by
    intro u
    have e : X0 k (finSumFinEquiv (m := a) (n := a')) * (invT (u * κ)).val * κ.1ᵀ =
        X0 k (finSumFinEquiv (m := a) (n := a')) * (invT u).val := by
      rw [← invT_inv_val κ, Matrix.mul_assoc, ← Units.val_mul, map_mul, mul_inv_cancel_right]
    rw [bigZetaIntegral_eq, bigZetaIntegral_eq, bigF_change ν ϖ c a a' hϖ, e, gdet_mul, map_mul, apow_mul, Units.val_mul, hA]
    ring
  have h2 : ∀ (l : ℂ) (u : GL (Fin (a + a')) k), smallP (haarVol (KO k (Fin a'))) finSumFinEquiv ν α
      (l • fun Y : Matrix (Fin a') (Fin (a + a')) k => stdB ν ϖ c a a' (g'.1 * Y * (κ⁻¹).1)) (u * κ) =
      l * B * smallP (haarVol (KO k (Fin a'))) finSumFinEquiv ν α (stdB ν ϖ c a a') u := by
    intro l u
    have e : Y0 k (finSumFinEquiv (m := a) (n := a')) * (u * κ).val * (κ⁻¹).1 =
        Y0 k (finSumFinEquiv (m := a) (n := a')) * u.val := by
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel_right]
    rw [smallP, smallP, smallF_change, e, gdet_mul, map_mul, apow_mul, Units.val_mul, hB]
    ring
  refine ⟨fun H => ?_, A / B, funext fun h => ?_⟩
  · have := congrFun H (1 * κ)
    rw [h1] at this
    exact mul_ne_zero hA0 (std_ne β ν ϖ c a a' hϖ) this
  · obtain ⟨u, rfl⟩ : ∃ u, h = u * κ := ⟨h * κ⁻¹, by simp⟩
    rw [h1, h2, div_mul_cancel₀ _ hB0, std_key α β ν ϖ c a a' hϖ hν]

end

end UpperTheory.StandardFormChange

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.bigZeta_stdSchwartz_translate_eq_smallZeta :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ →
        ∀ (α β ν : kˣ →* ℂˣ), ν = α / β → ∀ (c a a' : ℕ) (g : GL (Fin a) k) (g' : GL (Fin a') k) (κ : GL (Fin (a + a')) k),
        GlobalTheory.SplitFlip.bigP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ finSumFinEquiv ν β
                     (fun Y : Matrix (Fin a) (Fin (a + a')) k => GlobalTheory.StdPairCone.stdA ν ϖ c a a' (g.1 * Y * κ.1ᵀ)) ≠ 0 ∧
        ∃ l : ℂ, GlobalTheory.SplitFlip.bigP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a))) ϖ finSumFinEquiv ν β
            (fun Y : Matrix (Fin a) (Fin (a + a')) k => GlobalTheory.StdPairCone.stdA ν ϖ c a a' (g.1 * Y * κ.1ᵀ)) =
          GlobalTheory.SplitFlip.smallP (GlobalTheory.SplitFlip.haarVol (GlobalTheory.SplitWeil.KO k (Fin a'))) finSumFinEquiv ν α
            (l • fun Y : Matrix (Fin a') (Fin (a + a')) k => GlobalTheory.StdPairCone.stdB ν ϖ c a a' (g'.1 * Y * (κ⁻¹).1)) := by
  intro k _ _ _ _ _ _ ϖ hϖ α β ν hν c a a' g g' κ
  exact UpperTheory.StandardFormChange.main ϖ hϖ α β ν hν c a a' g g' κ
end

section -- merged from Development.AutomorphicArithmetic.DivisorFrames.ExistsMaxCompactEqFrameGramSplitBasis
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels ComplexConjugate
open GlobalTheory.FunObj GlobalTheory.StdFrames GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LFun.SplitTie
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.exists_maxCompact_eq_frame_gram_splitBasis :
    ∀ (D : D7) (S : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (β : GL (Fin S.rank) (Lev.EAf D)),
        IsSelfDualC S Λ → Formalism.L2.DIV.IsFrame β Λ → ∀ (v : Pl D.host.F) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
        (b : GL (Fin S.rank) (Fv D.host.F v)), IsSplitBasis τ (GlobalTheory.TripleSpaceW.conjSub Λ) b →
        ∃ g ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) (Fin S.rank),
          g.val = (β.val.map (GlobalTheory.BotMatch.evW τ))ᵀ * (S.gram.map τ)ᵀ * b.val := by
  intro D S Λ β hΛ hβ v τ b hb
  have hJ := GlobalTheory.Doubling.isHermND_gram S
  have hL := GlobalTheory.Core.Rk.IwSplit.isSelfDualAt_of_isSelfDualC hΛ v
  have h1 := GlobalTheory.FlipMatch.RowChart.isSplitBasis_conj τ
    (GlobalTheory.FlipMatch.RowChart.isFrameAt_loc hβ (splitPrime τ))
  have e : ∀ t : D.host.E →ₐ[D.host.F] Fv D.host.F v,
      splitLat (t.comp D.sp.cm.sig) (GlobalTheory.TripleSpaceW.conjSub Λ) = splitLat t Λ := fun t => by
    refine le_antisymm (GlobalTheory.FlipMatch.RowChart.splitLat_le fun x hx => ⟨star x, hx, fun i => rfl⟩)
      (GlobalTheory.FlipMatch.RowChart.splitLat_le fun x hx => ⟨star x, ?_, fun i => ?_⟩)
    · rw [GlobalTheory.TripleSpaceW.mem_conjSub, star_star]; exact hx
    · change t (x i) = t (star (star (x i)))
      rw [star_star]
  have e2 := e (τ.comp D.sp.cm.sig)
  rw [comp_conj_conj (isCMExt_host D)] at e2
  set β' := GeneralLinearGroup.map (complEquiv τ (splitPrime_under τ)).symm.toRingHom (loc (splitPrime τ) β) with hβ'
  have hv : β'.val = β.val.map (GlobalTheory.BotMatch.evW τ) := rfl
  have h2 : IsSplitBasis τ Λ β' := fun u => by rw [← e τ]; exact h1 u
  have h3 : IsSplitBasis (τ.comp D.sp.cm.sig) Λ b := fun u => by rw [← e2]; exact hb u
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : GL (Fin S.rank) (Fv D.host.F v), g₀.val = b.valᵀ * S.gram.map τ * β'.val :=
    ⟨dualConj 1 b⁻¹ * splitGram hJ τ * β', by
      rw [Units.val_mul, Units.val_mul, dualConj_one_val, inv_inv, splitGram_val]⟩
  obtain ⟨k1, k2⟩ := GlobalTheory.FlipMatch.RowChart.pairing_int (isCMExt_host D) hJ hL h2 h3 hg₀
  refine ⟨dualConj 1 g₀⁻¹, ?_, ?_⟩
  · rw [← (GLint_eq_KO_and_princ_eq_KOne v S.rank).1, mem_GLint_iff, ← map_inv, dualConj_one_val, dualConj_one_val,
      inv_inv]
    exact ⟨fun i j => k1 j i, fun i j => k2 j i⟩
  · rw [dualConj_one_val, inv_inv, hg₀, hv, transpose_mul, transpose_mul, transpose_transpose, Matrix.mul_assoc]
end
