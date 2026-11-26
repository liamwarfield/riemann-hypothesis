module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GKeyFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeIsIntegralOverStandardLatticeStabilis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormFieldSquareClass
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicDivOfBeta
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeIsIntegralOverStandardLatticeStabilisStatement
open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_isIntegralOverStandardLatticeStabiliser : ∀ (D : Formalism.BasicNotions.D7) (N : ℕ) (h : ↥(Formalism.MainNotions.StandardLatticesGL3.GA D N)), ∃ p : ℕ, p.Prime ∧ GlobalTheory.NormSum.IntegralOver D p h := by
  first | exact @GlobalTheory.NormSum.exists_prime_integralOver | exact GlobalTheory.NormSum.exists_prime_integralOver | (intros; apply GlobalTheory.NormSum.exists_prime_integralOver <;> assumption)
end

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun

noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTop.SqField

theorem gBig_and {Q Q' : GP} (h : GBig @Q) (h' : GBig @Q') :
    GBig fun {_ _ _ _} G μ C x b => Q G μ C x b ∧ Q' G μ C x b := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨a', ha'⟩ := h'
  refine ⟨max a a', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h1⟩ := ha ε CF (le_of_max_le_left hCF)
  obtain ⟨C1, x1, h2⟩ := ha' ε CF (le_of_max_le_right hCF)
  refine ⟨max C0 C1, max x0 x1, fun C hC D large₂ he hx hR T Lc μ hμ G => ⟨?_, ?_⟩⟩
  · exact h1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ hμ G
  · exact h2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ hμ G

theorem isAlgebraic_norm {D : D7} {δ t0 : ℂ} {Q N : ℕ} {B : ℝ} {del : ℕ → ℝ} (hC : GlobalTheory.NormSum.CoordInt D N B Q del)
    (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) (hP : P.Small N B) : IsAlgebraic ℚ ((P.norm : ℝ) : ℂ) := by
  have hco : ∀ h T, P.coord h T ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := fun h T => by
    obtain ⟨p, hp, hi⟩ := GlobalTheory.T.exists_prime_isIntegralOverStandardLatticeStabiliser D P.d h
    haveI : Fact p.Prime := ⟨hp⟩
    exact ((hC δ t0 p Q le_rfl P hP).2.2 h hi T).1
  have hsq : ∀ g, ((P.sq g : ℝ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := fun g => by
    unfold GlobalTheory.NormSum.Pair.sq
    rw [Complex.ofReal_sum]
    refine sum_mem fun T _ => ?_
    have e : ((‖P.coord g T‖ ^ 2 : ℝ) : ℂ) = P.coord g T * (starRingEnd ℂ) (P.coord g T) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [e]
    exact mul_mem (hco g T)
      (mem_algebraicClosure_iff.2 ((mem_algebraicClosure_iff.1 (hco g T)).algHom (starRingEnd ℂ).toRatAlgHom))
  have hterm : ∀ h : GlobalTheory.NormSum.Cls D P.d P.J,
      (((((GlobalTheory.NormSum.gam D P.J h.out : ℝ))⁻¹ * P.sq h.out : ℝ)) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := fun h => by
    rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
    exact mul_mem (inv_mem (natCast_mem _ _)) (hsq _)
  refine mem_algebraicClosure_iff.1 ?_
  unfold GlobalTheory.NormSum.Pair.norm
  by_cases hs : (Function.support fun h : GlobalTheory.NormSum.Cls D P.d P.J =>
      ((GlobalTheory.NormSum.gam D P.J h.out : ℝ))⁻¹ * P.sq h.out).Finite
  · rw [finsum_eq_sum _ hs, Complex.ofReal_sum]
    exact sum_mem fun h _ => hterm h
  · rw [finsum_of_infinite_support hs, Complex.ofReal_zero]
    exact zero_mem _

theorem isAlgebraic_div_of_beta {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {d s : ℕ} (hd : 0 < d)
    (hs : 1 ≤ s) (κ : I → ℕ) (Λ : PeriodPair) {x y : ℂ} (hx : x ≠ 0)
    (ha : IsAlgebraic ℚ (GlobalTheory.CMVal.beta E d s κ Λ x)) (hb : IsAlgebraic ℚ (GlobalTheory.CMVal.beta E d s κ Λ y)) :
    IsAlgebraic ℚ (y / x) := by
  have hC : (GlobalTheory.CMVal.C0 E d (2 * s) κ : ℂ) ≠ 0 := by exact_mod_cast (GlobalTheory.CMVal.cmValueConst_pos E hd (by omega) κ).ne'
  have hΔ : GlobalTheory.CMVal.latDisc Λ ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ ≠ 0 := pow_ne_zero _ (GlobalTheory.CMVal.latDisc_ne_zero Λ)
  have e : (y / x) ^ 12 = GlobalTheory.CMVal.beta E d s κ Λ y / GlobalTheory.CMVal.beta E d s κ Λ x := by
    unfold GlobalTheory.CMVal.beta
    field_simp
  refine IsAlgebraic.of_pow (n := 12) (by norm_num) ?_
  rw [e]
  exact mem_algebraicClosure_iff.1 (div_mem (mem_algebraicClosure_iff.2 hb) (mem_algebraicClosure_iff.2 ha))

theorem sqIn_of {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T)
    (hI : GlobalTheory.NormSum.IntSt) (hΛ : ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ)
    (hT : ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j → ∀ c, ∃ x, IsTor G i j s (fam G μ₀ i j c) x ∧ x ≠ 0 ∧
      ∀ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ →
        IsAlgebraic ℚ (GlobalTheory.CMVal.beta D.host.E D.host.d s (kap D sc.cGap i j s) Λ x))
    (hQ : GlobalTheory.NormSum.GoodLevel D (levQ G.pl))
    (hS : ∀ (δ t0 : ℂ) (Q : ℕ) (P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) t (i j : Fin D.R.m) 𝔪, IsBottom G t i j 𝔪 P P' →
      P.Small (bigN D) (maxWt D sc.cGap) ∧ P'.Small (bigN D) (maxWt D sc.cGap)) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ GlobalTheory.BigTop.Fun.SqIn G μ₀ (algebraMap M ℂ) := by
  obtain ⟨C, -, hI⟩ := hI
  have hN : 1 ≤ bigN D := by have := D.R.m_add_three_le_k; unfold bigN; omega
  obtain ⟨-, del, -, hco, -⟩ := hI D (levQ G.pl) (bigN D) (maxWt D sc.cGap) (max 1 (Real.log D.host.rdE)) hQ hN
    (by exact_mod_cast le_max_left _ _) (le_max_left _ _) (le_max_right _ _)

  obtain ⟨Sn, hSn, hSa, hSb⟩ : ∃ Sn : Set ℂ, Sn.Finite ∧ (∀ z ∈ Sn, IsAlgebraic ℚ z) ∧
      (GlobalTheory.BigTop.Fun.BottomsWith G μ₀ (fun _ => True) → GlobalTheory.BigTop.Fun.BottomsWith G μ₀ (· ∈ Sn)) := by
    by_cases hb : GlobalTheory.BigTop.Fun.BottomsWith G μ₀ (fun _ => True)
    · obtain ⟨δ, t0, hb⟩ := hb
      choose P P' hP using hb
      refine ⟨Set.range (fun ij => ((P ij).norm : ℂ)) ∪ Set.range (fun ij => ((P' ij).norm : ℂ)),
        (Set.finite_range _).union (Set.finite_range _), ?_,
        fun _ => ⟨δ, t0, fun ij => ⟨P ij, P' ij, (hP ij).1, Or.inl ⟨ij, rfl⟩, Or.inr ⟨ij, rfl⟩⟩⟩⟩
      rintro z (⟨ij, rfl⟩ | ⟨ij, rfl⟩)
      · exact isAlgebraic_norm hco _ (hS δ t0 _ _ _ _ _ _ _ (hP ij).1).1
      · exact isAlgebraic_norm hco _ (hS δ t0 _ _ _ _ _ _ _ (hP ij).1).2
    · exact ⟨∅, Set.finite_empty, fun z hz => absurd hz (Set.notMem_empty z), fun h => absurd h hb⟩

  let St : Set ℂ := ⋃ (i : Fin D.R.m) (j : Fin D.R.m) (s ∈ Set.Icc 1 (halfRank D i j)) (c : Bool),
    {z | ∃ x y, IsTor G i j s (nuH G μ₀ i j) x ∧ IsTor G i j s (nuH G μ₀ i j * delOf Lc c) y ∧ z = y / x}
  have hSt : St.Finite := by
    refine Set.finite_iUnion fun i => Set.finite_iUnion fun j => (Set.finite_Icc _ _).biUnion fun s _ =>
      Set.finite_iUnion fun c => Set.Subsingleton.finite ?_
    rintro _ ⟨x, y, hx, hy, rfl⟩ _ ⟨x', y', hx', hy', rfl⟩
    rw [hx.2.unique hx'.2, hy.2.unique hy'.2]
  have hd : 0 < D.host.d := D.host.hypOdd.2.1.pos
  obtain ⟨Λ, hΛ⟩ := hΛ
  have hSta : ∀ z ∈ St, IsAlgebraic ℚ z := by
    intro z hz
    simp only [St, Set.mem_iUnion, Set.mem_setOf_eq] at hz
    obtain ⟨i, j, s, ⟨h1, h2⟩, c, x, y, hx, hy, rfl⟩ := hz
    obtain ⟨x0, hx0, hx00, ha⟩ := hT i j s h1 h2 none
    obtain ⟨x1, hx1, -, hb⟩ := hT i j s h1 h2 (some c)
    rw [hx.2.unique hx0.2, hy.2.unique hx1.2]
    exact isAlgebraic_div_of_beta hd h1 _ Λ hx00 (ha Λ hΛ) (hb Λ hΛ)
  let S : Set ℂ := Sn ∪ St
  haveI : Finite S := (hSn.union hSt).to_subtype
  have hmem : ∀ z ∈ S, z ∈ Set.range (algebraMap (IntermediateField.adjoin ℚ S) ℂ) := fun z hz =>
    ⟨⟨z, IntermediateField.subset_adjoin ℚ S hz⟩, rfl⟩
  refine ⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin fun z hz =>
    (Or.elim hz (hSa z) (hSta z)).isIntegral, ⟨fun h => ?_, fun i j s c x y h1 h2 hx hy => ?_⟩⟩
  · obtain ⟨δ, t0, b⟩ := hSb h
    exact ⟨δ, t0, fun ij => let ⟨P, P', a, b1, b2⟩ := b ij; ⟨P, P', a, hmem _ (Or.inl b1), hmem _ (Or.inl b2)⟩⟩
  · refine hmem _ (Or.inr ?_)
    simp only [St, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨i, j, s, ⟨h1, h2⟩, c, x, y, hx, hy, rfl⟩

end GlobalTheory.SqTop.SqField

namespace GlobalTheory.BigTop.Fun

end GlobalTheory.BigTop.Fun

end
end

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.LiteralAutomorphy

theorem nfSq_of_fieldDat : GlobalTheory.NormSum.IntSt → GlobalTheory.SqTop.FieldDat → GlobalTheory.SqTop.TorEx → GlobalTheory.SqTop.BotSmall → NFSq := by
  intro hI hFD hTE hBS
  obtain ⟨CF0, h⟩ := GlobalTheory.SqTop.SqField.gBig_and hFD (GlobalTheory.SqTop.SqField.gBig_and hTE hBS)
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, h⟩ := h ε CF hCF
  refine ⟨x₀, fun D large₂ he hx hR T L μ₀ hμ G => ?_⟩
  obtain ⟨⟨_, _, _, _, hΛ⟩, hT, hQ, -, hB⟩ := h C0 le_rfl D large₂ he hx hR T L μ₀ hμ G
  exact GlobalTheory.SqTop.SqField.sqIn_of G μ₀ hI hΛ
    (fun i j s h1 h2 c => let ⟨x, a, b, _, d⟩ := hT i j s h1 h2 c; ⟨x, a, b, d⟩) hQ hB

end GlobalTheory.Mem.LiteralAutomorphy

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCharactersAgreeOverEnlargedBase
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCharactersAgreeOverEnlargedBase
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt

namespace GlobalTheory.Mem.R3.Rw.LevExt

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem gridCharacter_eq_reference_at_base_tuple {D : D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {t : T} (h : L.Is t) (j : ℕ) : L.mu t j = L.mu0 j := by
  have hx := h.xi t
  rw [h.xi_base] at hx
  have e : L.xi t = 1 := MonoidHom.ext (GlobalTheory.ChrEqUnique.eq_one_of_chrEq hx)
  show L.mu0 j * L.xi t = L.mu0 j
  rw [e, mul_one]

theorem Q_eq_empty {D : D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {t : T} (h : L.Is t) : L.Q t = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun PP hPP => ?_
  have h1 := (h.Q_ram t PP).2 (Or.inl hPP)
  rw [h.xi_base] at h1
  exact h1 fun _ _ => rfl

theorem isRes_unique' {D : D7} {χ : Formalism.L2.Host.HChar D.host.E} {P : Pl D.host.E} {c c' : (kP P)ˣ →* ℂˣ}
    (h : IsRes χ P c) (h' : IsRes χ P c') : c = c' := by
  refine MonoidHom.ext fun u => ?_
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP P)
  haveI : Nontrivial (kP P) := Ideal.Quotient.nontrivial_iff.2 P.isPrime.ne_top
  have ha0 : (a : D.host.E) ≠ 0 := by
    intro h0
    have h1 : a = 0 := RingOfIntegers.coe_eq_zero_iff.1 h0
    apply u.ne_zero
    rw [← ha, h1, map_zero]
  rw [h a (Units.mk0 _ ha0) u rfl ha.symm, h' a (Units.mk0 _ ha0) u rfl ha.symm]

section Gen

variable {B B' : Base} {C : Cols B} {C' : Cols B'} {a : Late B C} {a' : Late B' C'}

theorem idc_heq (hP : B'.toPre = B.toPre) {c : (AE a.D)ˣ →* Circle} {c' : (AE a'.D)ˣ →* Circle}
    {χ : Formalism.L2.Host.HChar a.D.host.E} {χ' : Formalism.L2.Host.HChar a'.D.host.E} (hχ : HEq χ' χ) (h : ChrEq c χ)
    (h' : ChrEq c' χ') : HEq c' c := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (χ')) ((by with_unfolding_all exact ((χ) :))) (χ') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (χ')) (χ') (((χ))) (((hχ)))).symm : _))
  clear (hχ)
  subst e))
  have e : @Eq ((AE a.D)ˣ →* Circle) ((by with_unfolding_all exact (c' :))) c := GlobalTheory.ChrEqUnique.idc_unique a.D _ c χ ((by with_unfolding_all exact (h' :))) h
  exact (by with_unfolding_all exact ((heq_of_eq e) :))

theorem res_heq (hP : B'.toPre = B.toPre) {χ : Formalism.L2.Host.HChar a.D.host.E} {χ' : Formalism.L2.Host.HChar a'.D.host.E} (hχ : HEq χ' χ)
    {PP : Pl a.D.host.E} {PP' : Pl a'.D.host.E} (hPP : HEq PP' PP) {c : (kP PP)ˣ →* ℂˣ} {c' : (kP PP')ˣ →* ℂˣ}
    (h : IsRes χ PP c⁻¹) (h' : IsRes χ' PP' c'⁻¹) : HEq c' c := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (χ')) ((by with_unfolding_all exact ((χ) :))) (χ') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (χ')) (χ') (((χ))) (((hχ)))).symm : _))
  clear (hχ)
  subst e))
  ( (
  have e : @Eq (type_of% (PP')) ((by with_unfolding_all exact ((PP) :))) (PP') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (PP')) (PP') (((PP))) (((hPP)))).symm : _))
  clear (hPP)
  subst e))
  have e : ((by with_unfolding_all exact (c' :)) : (kP PP)ˣ →* ℂˣ)⁻¹ = c⁻¹ := isRes_unique' (D := a.D) ((by with_unfolding_all exact (h' :))) h
  have e' : @Eq ((kP PP)ˣ →* ℂˣ) ((by with_unfolding_all exact (c' :))) c := inv_inj.1 e
  exact (by with_unfolding_all exact ((heq_of_eq e') :))

theorem hermitianCodeCharFrame_referenceCharacter_heq (hP : B'.toPre = B.toPre) {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} (hf : HEq f' f) {i : Fin a.D.R.m}
    {i' : Fin a'.D.R.m} (h : (i : ℕ) = i') : HEq ((Top.Fr.at a'.st f').mu0 i') ((Top.Fr.at a.st f).mu0 i) := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (f')) ((by with_unfolding_all exact ((f) :))) (f') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (f')) (f') (((f))) (((hf)))).symm : _))
  clear (hf)
  subst e))
  have e : @Eq (type_of% i') ((by with_unfolding_all exact (i :))) i' := (by with_unfolding_all exact ((Fin.ext h : @Eq (type_of% i') ((by with_unfolding_all exact (i :))) i') :))
  clear h
  subst e
  exact (by with_unfolding_all exact ((HEq.refl ((Top.Fr.at a.st f).mu0 i)) :))

theorem frat_eta_heq (hP : B'.toPre = B.toPre) {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} (hf : HEq f' f) :
    HEq (Top.Fr.at a'.st f').eta (Top.Fr.at a.st f).eta := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (f')) ((by with_unfolding_all exact ((f) :))) (f') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (f')) (f') (((f))) (((hf)))).symm : _))
  clear (hf)
  subst e))
  exact (by with_unfolding_all exact ((HEq.refl (Top.Fr.at a.st f).eta) :))

theorem mem_vGs (hP : B'.toPre = B.toPre) {px : PreX B.toPre} {px' : PreX B'.toPre} (hpx : HEq px' px)
    {PP : Pl a.D.host.E} {PP' : Pl a'.D.host.E} (hPP : HEq PP' PP) (h : PP ∈ (B.primes px).vGs) : PP' ∈ (B'.primes px').vGs := by
  rcases B' with ⟨P'⟩
  change P' = B.toPre at hP
  subst hP
  ( (
  have e : @Eq (type_of% (px')) ((by with_unfolding_all exact ((px) :))) (px') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (px')) (px') (((px))) (((hpx)))).symm : _))
  clear (hpx)
  subst e))
  ( (
  have e : @Eq (type_of% (PP')) ((by with_unfolding_all exact ((PP) :))) (PP') := (by with_unfolding_all exact ((@eq_of_heq (type_of% (PP')) (PP') (((PP))) (((hPP)))).symm : _))
  clear (hPP)
  subst e))
  exact (by with_unfolding_all exact (h :))

end Gen

end GlobalTheory.Mem.R3.Rw.LevExt


open GlobalTheory.Mem.R3.Rw.LevExt in
set_option maxHeartbeats 4000000 in
theorem GlobalTheory.Mem.R3.Rw.LevExt.levSame_of_levOf : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq f' f → HEq w'.px w.px → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh → LevSame z Wt' R' := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Ks _ _ _ Xg tr z Wt' R' hE hf hpx hL'
  have hP : B'.toPre = B.toPre := hE.1
  have hC : z.R.toLevCh.C = Top.Fr.at (w.st Z) f := z.lev.C.trans (by rw [w.C_eq])
  have hC' : R'.toLevCh.C = Top.Fr.at (w'.st Z') f' := hL'.C.trans (by rw [w'.C_eq])
  have hmu0 : ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
      HEq (R'.toLevCh.C.mu0 i') (z.R.toLevCh.C.mu0 i) := by
    intro i i' h
    rw [hC, hC']
    exact hermitianCodeCharFrame_referenceCharacter_heq (a := Z) (a' := Z') hP hf h
  have heta : HEq R'.toLevCh.C.eta z.R.toLevCh.C.eta := by
    rw [hC, hC']
    exact frat_eta_heq (a := Z) (a' := Z') hP hf
  have hs := z.lev.is
  have hs' := hL'.is
  refine ⟨fun i i' h => ⟨?_, fun PP' PP hPP hm => ?_⟩, ?_, Q_eq_empty hs', Q_eq_empty hs⟩
  · rw [gridCharacter_eq_reference_at_base_tuple hs', gridCharacter_eq_reference_at_base_tuple hs]
    exact idc_heq (a := Z) (a' := Z') hP (hmu0 i i' h) (hs.mu0 i) (hs'.mu0 i')
  · have hm0 : PP ∈ (B.primes w.px).vGs := by
      have e := z.lev.Pg
      rw [← e]
      exact hm
    have hm' : PP' ∈ R'.toLevCh.Pg := by
      rw [hL'.Pg]
      exact mem_vGs (a := Z) (a' := Z') hP hpx hPP hm0
    exact res_heq (a := Z) (a' := Z') hP (hmu0 i i' h) hPP (hs.chi i PP hm) (hs'.chi i' PP' hm')
  · exact idc_heq (a := Z) (a' := Z') hP heta hs.eta hs'.eta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftCharactersAgreeOverEnlargedBaseStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open GlobalTheory.Mem.KeepRef GlobalTheory.Mem.R3.Rw.WeilExt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftCharacters_agree_over_enlarged_base : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
  (z : Dat (w.st Z) w.I hX T Wt) (Wt' : Set B'.places.Pl)
  (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks), Enl0 B B' → HEq f' f → HEq w'.px w.px → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh → LevSame z Wt' R' := by
  first | exact @GlobalTheory.Mem.R3.Rw.LevExt.levSame_of_levOf | exact GlobalTheory.Mem.R3.Rw.LevExt.levSame_of_levOf | (intros; apply GlobalTheory.Mem.R3.Rw.LevExt.levSame_of_levOf <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetupLGood
noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N _root_.Formalism.L2 _root_.Formalism.L2.Host _root_.Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top
  GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}
variable {x : St P} (L : LocAll (lay0 (Dof x)))

def twL {A : Type} [CommGroup A] (t : GlobalTheory.ExportSeries.Twist (Dof x) A) : GlobalTheory.ExportSeries.Twist (DL x L) A :=
  ⟨(by with_unfolding_all exact (t.Q :)), (by with_unfolding_all exact (t.chi :)), (by with_unfolding_all exact (t.res :))⟩

def twB {A : Type} [CommGroup A] (t : GlobalTheory.ExportSeries.Twist (DL x L) A) : GlobalTheory.ExportSeries.Twist (Dof x) A :=
  ⟨(by with_unfolding_all exact (t.Q :)), (by with_unfolding_all exact (t.chi :)), (by with_unfolding_all exact (t.res :))⟩

def frL {S U : Formalism.BasicNotions.TH.HSp (Dof x)} (F : GlobalTheory.ExportSeries.Frame S U) : @GlobalTheory.ExportSeries.Frame (DL x L) ((S)) ((U)) where
  ψ := (by with_unfolding_all exact (F.ψ :))
  θ := (by with_unfolding_all exact (F.θ :))
  sT := (by with_unfolding_all exact (F.sT :))
  BS := (by with_unfolding_all exact (F.BS :))
  BT := (by with_unfolding_all exact (F.BT :))
  ΛS := (by with_unfolding_all exact (F.ΛS :))
  ΛT := (by with_unfolding_all exact (F.ΛT :))
  βS := (by with_unfolding_all exact (F.βS :))
  βT := (by with_unfolding_all exact (F.βT :))
  f₀ := (by with_unfolding_all exact (F.f₀ :))

def tdL {r : ℕ} (G : GlobalTheory.ExportSeries.TypeDat (Dof x) r) : GlobalTheory.ExportSeries.TypeDat (DL x L) r := ⟨(by with_unfolding_all exact (G.Pg :)), (by with_unfolding_all exact (G.P :)), (by with_unfolding_all exact (G.mu :))⟩

def wtL {n : ℕ} (u : GlobalTheory.ExportSeries.Weight (Dof x) n) : GlobalTheory.ExportSeries.Weight (DL x L) n :=
  ⟨(by with_unfolding_all exact (u.p :)), (by with_unfolding_all exact (u.q :)), (by with_unfolding_all exact (u.ap :)), (by with_unfolding_all exact (u.am :)), (by with_unfolding_all exact (u.c :)), (by with_unfolding_all exact (u.lam :))⟩

def baseL {S U : Formalism.BasicNotions.TH.HSp (Dof x)} (Z : GlobalTheory.ExportSeries.Base S U) : @GlobalTheory.ExportSeries.Base (DL x L) ((S)) ((U)) where
  hr := (by with_unfolding_all exact (Z.hr :))
  F := frL L Z.F
  G := (by with_unfolding_all exact ((tdL L Z.G) :))
  de := twL L Z.de
  w := (by with_unfolding_all exact ((wtL L Z.w) :))
  mu0 := (by with_unfolding_all exact (Z.mu0 :))
  eta := (by with_unfolding_all exact (Z.eta :))

def setupL (ρ : GlobalTheory.SeriesTie.Setup (Dof x).ntw) : GlobalTheory.SeriesTie.Setup (DL x L).ntw where
  rc := ⟨(by with_unfolding_all exact (ρ.rc.κ :)), (by with_unfolding_all exact (ρ.rc.art :))⟩
  ch := (by with_unfolding_all exact (ρ.ch :))
  bad := (by with_unfolding_all exact (ρ.bad :))
  e := (by with_unfolding_all exact (ρ.e :))
  ek := (by with_unfolding_all exact (ρ.ek :))
  B := fun i j b => (by with_unfolding_all exact ((baseL L (ρ.B ((i)) ((j)) b)) : _))
  om := fun i j b χ => (by with_unfolding_all exact ((ρ.om ((i)) ((j)) b ((χ))) : _))
  Cl := fun i j b t => ρ.Cl ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twB L t)
  finCl := fun i j b t => ρ.finCl ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twB L t)
  rep := fun i j b t c => (by with_unfolding_all exact ((ρ.rep ((i)) ((j)) b (twB L t) c) : _))
  β := (by with_unfolding_all exact (ρ.β :))
  eG := (by with_unfolding_all exact (ρ.eG :))

theorem twL_good {A : Type} [CommGroup A] {t : GlobalTheory.ExportSeries.Twist (Dof x) A} (h : t.Good) : (twL L t).Good :=
  ⟨(by with_unfolding_all exact (h.isOpen :)), (by with_unfolding_all exact (h.rat :)), (by with_unfolding_all exact (h.real :)), (by with_unfolding_all exact (h.split :)), (by with_unfolding_all exact (h.unram :)), (by with_unfolding_all exact (h.res :))⟩

theorem twB_good {A : Type} [CommGroup A] {t : GlobalTheory.ExportSeries.Twist (DL x L) A} (h : t.Good) : (twB L t).Good :=
  ⟨(by with_unfolding_all exact (h.isOpen :)), (by with_unfolding_all exact (h.rat :)), (by with_unfolding_all exact (h.real :)), (by with_unfolding_all exact (h.split :)), (by with_unfolding_all exact (h.unram :)), (by with_unfolding_all exact (h.res :))⟩

theorem placesOK_L {Pg Q : Finset (HeightOneSpectrum (𝓞 (Dof x).host.E))} (h : @GlobalTheory.ExportSeries.PlacesOK (Dof x) Pg Q) :
    @GlobalTheory.ExportSeries.PlacesOK (DL x L) ((Pg)) ((Q)) := ⟨(h.split), (h.disj), (h.prime)⟩

theorem placesOK_B {Pg Q : Finset (HeightOneSpectrum (𝓞 (DL x L).host.E))} (h : @GlobalTheory.ExportSeries.PlacesOK (DL x L) Pg Q) :
    @GlobalTheory.ExportSeries.PlacesOK (Dof x) ((Pg)) ((Q)) := ⟨(h.split), (h.disj), (h.prime)⟩

theorem wtL_good {n : ℕ} {u : GlobalTheory.ExportSeries.Weight (Dof x) n} (h : u.Good) : (wtL L u).Good := ⟨(by with_unfolding_all exact (h.le :)), (by with_unfolding_all exact (h.lam_eq :))⟩

theorem thetaFun_L_iff {S U : Formalism.BasicNotions.TH.HSp (Dof x)}
    (F : GlobalTheory.ExportSeries.Frame S U) (f : Formalism.IndefR.Datum.WO S U → ℂ) :
    @Formalism.IndefR.Datum.IsThetaFunO (DL x L) (frL L F).ψ S U f ↔
      @Formalism.IndefR.Datum.IsThetaFunO (Dof x) F.ψ S U f := by
  constructor <;> intro h <;>
    exact ⟨(by with_unfolding_all exact h.quasi),
      (by with_unfolding_all exact h.level),
      (by with_unfolding_all exact h.cont),
      (by with_unfolding_all exact h.smooth)⟩

theorem frL_good {S U : Formalism.BasicNotions.TH.HSp (Dof x)} {F : GlobalTheory.ExportSeries.Frame S U} (h : F.Good) : (frL L F).Good :=
  { rank_le := (by with_unfolding_all exact (h.rank_le :))
    onbS := (by with_unfolding_all exact (h.onbS :))
    cartT := (by with_unfolding_all exact (h.cartT :))
    onbT := (by with_unfolding_all exact (h.onbT :))
    sdS := (by with_unfolding_all exact (h.sdS :))
    sdT := (by with_unfolding_all exact (h.sdT :))
    frS := (by with_unfolding_all exact (h.frS :))
    frT := (by with_unfolding_all exact (h.frT :))
    vac := by
      rcases h.vac with ⟨hstd, hinf, htheta, hlat, hfock, hnorm⟩
      exact ⟨(by with_unfolding_all exact hstd),
        (by with_unfolding_all exact hinf), (by
          exact ⟨(by with_unfolding_all exact htheta.quasi),
            (by with_unfolding_all exact htheta.level),
            (by with_unfolding_all exact htheta.cont),
            (by with_unfolding_all exact htheta.smooth)⟩),
        (by with_unfolding_all exact hlat), (by with_unfolding_all exact hfock),
        (by with_unfolding_all exact hnorm)⟩ }

theorem baseL_good {S U : Formalism.BasicNotions.TH.HSp (Dof x)} {Z : GlobalTheory.ExportSeries.Base S U} (h : Z.Good) : (baseL L Z).Good :=
  { even := (by with_unfolding_all exact (h.even :))
    odd := (by with_unfolding_all exact (h.odd :))
    frame := frL_good L h.frame
    de := twL_good L h.de
    places := (by with_unfolding_all exact ((placesOK_L L h.places) :))
    wt := (by with_unfolding_all exact ((wtL_good L h.wt) :))
    sig := (by with_unfolding_all exact (h.sig :))
    sigOK := (by with_unfolding_all exact (h.sigOK :))
    eta := (by with_unfolding_all exact (h.eta :))
    hecke := (by with_unfolding_all exact (h.hecke :))
    real := (by with_unfolding_all exact (h.real :))
    unram := (by with_unfolding_all exact (h.unram :))
    tame := (by with_unfolding_all exact (h.tame :))
    inf := (by with_unfolding_all exact (h.inf :)) }

theorem setupL_good {ρ : GlobalTheory.SeriesTie.Setup (Dof x).ntw} (h : ρ.Good) : (setupL L ρ).Good :=
  { rc := ⟨(by with_unfolding_all exact (h.rc.cont :)), (by with_unfolding_all exact (h.rc.rat :)), (by with_unfolding_all exact (h.rc.loc :)), (by with_unfolding_all exact (h.rc.artin :))⟩
    ch := fun i => ⟨(by with_unfolding_all exact ((h.ch ((i))).pair : _)), (by with_unfolding_all exact ((h.ch ((i))).one : _))⟩
    bad_ne := (by with_unfolding_all exact (h.bad_ne :))
    goodSetup_bad_mem_badPlaces := (by with_unfolding_all exact (h.goodSetup_bad_mem_badPlaces :))
    goodSetup_badPlaces_conj := (by with_unfolding_all exact (h.goodSetup_badPlaces_conj :))
    goodSetup_placesOverTwo_subset := (by with_unfolding_all exact (h.goodSetup_placesOverTwo_subset :))
    goodSetup_count_eq_zero_off_badPlaces := (by with_unfolding_all exact (h.goodSetup_count_eq_zero_off_badPlaces :))
    e_LL0 := (by with_unfolding_all exact (h.e_LL0 :))
    ek_e := (by with_unfolding_all exact (h.ek_e :))
    base := fun i j b => (by with_unfolding_all exact ((baseL_good L (h.base ((i)) ((j)) b)) : _))
    latS := (by with_unfolding_all exact (h.latS :))
    latT := (by with_unfolding_all exact (h.latT :))
    Pg := (by with_unfolding_all exact (h.Pg :))
    delta := fun i j b => (by with_unfolding_all exact (congrArg (twL L) (h.delta i j b) : _))
    weil := fun i j b t ht => by
      delta GlobalTheory.ExportSeries.Base.IsWeil
      have hw := h.weil i j b (twB L t) (twB_good L ht)
      have th := thetaFun_L_iff L (ρ.B i j b).F
      refine ⟨(by with_unfolding_all exact hw.std), (by with_unfolding_all exact hw.hecS),
        (by with_unfolding_all exact hw.hecT), (by with_unfolding_all exact hw.resS),
        (by with_unfolding_all exact hw.resT), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro p f hf
        exact (th _).2 (hw.om_pres p f ((th _).1 hf))
      · intro g h w f hf
        exact hw.om_heis g h w f ((th _).1 hf)
      · intro g hg g' hg' f hf
        exact hw.om_aut g hg g' hg' f ((th _).1 hf)
      · intro f hf w
        exact hw.om_cont f ((th _).1 hf) w
      · intro μ F hμ hF p f hf
        exact hw.om_unit μ F hμ hF p f ((th _).1 hf)
      · intro e he g h hg hh a b ha hb
        obtain ⟨r, hr, hsplit⟩ := hw.om_split e he g h hg hh a b ha hb
        refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
        apply hsplit ℓ ?_ f ((th _).1 hf)
        intro u hu f' hf'
        exact hℓ u hu f' ((th _).2 hf')
    classes := fun i j b t ht hA =>
      have h' := h.classes ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (j :))) b (twB L t) (twB_good L ht) ⟨(by with_unfolding_all exact ((placesOK_B L hA.1) :)), (by with_unfolding_all exact (hA.2 :))⟩
      ⟨(by with_unfolding_all exact (h'.fin :)), (by with_unfolding_all exact (h'.reps :)), (by with_unfolding_all exact (h'.stab :))⟩ }


open GlobalTheory.SeriesTie in
theorem theta_eq (ρ : Setup (Dof x).ntw) :
    (setupL L ρ).theta = fun i j b h P => (by exact ρ.theta i j b h P) := by
  funext i j b h P
  delta GlobalTheory.SeriesTie.Setup.theta GlobalTheory.ExportSeries.Base.theta GlobalTheory.ExportSeries.Base.vecBase GlobalTheory.ExportSeries.Base.vecAt
    GlobalTheory.ExportSeries.Frame.vec GlobalTheory.ExportSeries.Frame.placeMap
  rewrite [GlobalTheory.Mem.R3.Tr.placeModel_eq x.o.Z (oL x L).Z]
  with_unfolding_all exact Eq.refl (ρ.theta i j b h P)


open GlobalTheory.SeriesTie in
theorem isDatum_eq (ρ : Setup (Dof x).ntw) :
    (setupL L ρ).IsDatum = fun i j b s h P => (by exact ρ.IsDatum i j b s h P) := by
  funext i j b s h P
  refine propext ⟨fun d => ?_, fun d => ?_⟩
  · exact (by with_unfolding_all exact ((⟨(d.split), (d.off), (d.fin), (d.supp), (d.mem)⟩ : ρ.IsDatum ((i)) ((j)) b ((s)) ((h)) ((P))) : _))
  · exact ⟨(by with_unfolding_all exact (d.split :)), (by with_unfolding_all exact (d.off :)), (by with_unfolding_all exact (d.fin :)), (by with_unfolding_all exact (d.supp :)), (by with_unfolding_all exact (d.mem :))⟩

end GlobalTheory.HeightCounting.Fin3

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GapRAllSt
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000

namespace GlobalTheory.HeightCounting.Up.GapAllStates

theorem gapR_allSt : AllSt fun _ _ _ _ _ _ x => ∀ (τ : (Dof x).what₂.Tau) (n : ℕ), n + 1 < (Dof x).R.r →
    100 * ((Dof x).R.r : ℚ) ^ 4 ≤ Formalism.L2.NTheta.lamAt ((Dof x).hc τ) n - Formalism.L2.NTheta.lamAt ((Dof x).hc τ) (n + 1) :=
  Step.of_evG (EvG.imp (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)
    fun _ _ _ _ _ hK _ _ _ hO _ _ _ w _ _ x => (hK (w.st x.o.Z) hO).1.gapR)

end GlobalTheory.HeightCounting.Up.GapAllStates
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEigenReadThirdLocal
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.IndefR.NX ReciprocityTheory.Aut Formalism.AUTREP NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 4000000

noncomputable section

namespace GlobalTheory.HeightCounting.Up.ThirdIdx

open _root_.Formalism.L2.DIV _root_.Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links _root_.Formalism.L2.Rows

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat3 D A3 Ks} {F : Face3 D A3}
  {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {X0 : BaseLevelRowSide D} {Y : Read (A3 := A3) R.toRealDat F.lv2 X0}

theorem nonempty_divX (Z : RationalReadingWithoutCongruence R F X0 Y) (hP : Pins R F cG) (hH : Holds R F) : Nonempty (DivX D) := by
  obtain ⟨G, V, -⟩ := GlobalTheory.PointGeometry.exists_geo D.what₂.LL
  exact ⟨GlobalTheory.provisionalDivX D G V (fun p _ => (GlobalTheory.WittFracComplex.nonempty_ringHom_complex p).some)
    (fun p _ r => (GlobalTheory.nonempty_admissibleModel _ p _ (max r 2) 1 (by omega)).some) fun k =>
    ⟨mjH_noEta Z k, jM_noEta Z k, mjH_good_noEta Z hH k, jM_basis_noEta Z hH k, jM_lat_noEta Z hP hH k,
      mjLat_sub_noEta Z hP hH k, MjModel.jM_metric_all_noEta Z hH k⟩⟩

theorem nonempty_ix (hH : Holds R F) : Nonempty A3.A.fam.base.Ix := by
  obtain ⟨p⟩ := GlobalTheory.Div.nonempty_ix_of_pos A3 F.P0 F.ψ0 (R.toCx3 F).zs hH.ok hH.prim.block (hH.prim.pos false)
  exact ⟨p.1.1, Formalism.L2.DIV.InertDat3.mem_ixFin_fst _ (hH.ok.ok2.what₂ A3.A.μ0).comm p.2⟩

end GlobalTheory.HeightCounting.Up.ThirdIdx

namespace GlobalTheory.HeightCounting.Up.ThirdIdx

end GlobalTheory.HeightCounting.Up.ThirdIdx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GroupTieOfLocalCoefficient
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GroupTieOfLocalCoefficient
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HeightCounting.Fin3

theorem grpTie_of_LC : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {P : Pre2 K w} {x : St P} (_ : LC hL x), Formalism.L2.DIV.GrpTie (Dof x)
      (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A x.m.z.F.P0 x.m.z.F.ψ0 x.m.z.F.P1 x.m.z.F.ψ1
      (x.m.z.R.eG.trans x.m.z.cG) := by
  intro hL K B f T w P x l
  have hc := GlobalTheory.Mem.R3.pins_card_index_ranks _ _ _ _ _ _ _ _ _ _ x.m.z.pins
  have hU : (Dof x).nexp.U = Formalism.IndefR.NX.U (Dof x).nd := l.b.Bs.exp.U_eq
  obtain ⟨_, _, _, he0, _, _⟩ := x.m.z.pins.keep.grp
  refine ⟨hc.1, he0, ?_, ?_, hc.2.1, x.m.z.pins.keep.psi.lvl⟩
  · intro g
    rw [hU]
    exact l.rat.rat.lvl g
  · intro u hu i b
    have hu' : (x.m.z.R.eG.trans x.m.z.cG) u ∈ Formalism.IndefR.NX.U (Dof x).nd := hU ▸ hu
    refine ⟨psiUOf (Dof x).nd (NX.xiRed (Dof x)) l.rat.In.θ ⟨_, hu'⟩, l.rat.rat.psi u hu', ?_⟩
    exact l.b.Bs.psiU i b _ hu hu'

end GlobalTheory.HeightCounting.Fin3
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GroupTieOfLocalCoefficientStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.group_tie_of_local_coefficient : ∀ {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} {x : St P} (_ : LC hL x), Formalism.L2.DIV.GrpTie (Dof x) (famR (w.st x.o.Z) w.I P.hX (usedOf w.I T P.Wt) x.m.z.Xg x.m.z.tr).A x.m.z.F.P0 x.m.z.F.ψ0 x.m.z.F.P1 x.m.z.F.ψ1 (x.m.z.R.eG.trans x.m.z.cG) := by
  first | exact @GlobalTheory.HeightCounting.Fin3.grpTie_of_LC | exact GlobalTheory.HeightCounting.Fin3.grpTie_of_LC | (intros; apply GlobalTheory.HeightCounting.Fin3.grpTie_of_LC <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeRowOfLocalAll
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.HeightCounting.Fin3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HeightCounting.Fin3

open _root_.Formalism.L2.Theta Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

section Gen

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem hkRow_move (Rl : RealDat3 D A3 Ks) {i' i : Fin D.R.m} (h : i' = i) (k : ℕ) (P : PlE D.host)
    (u v : Fin (Rl.nW i') → D.what₂.LL) (u' v' : Fin (Rl.nW i) → D.what₂.LL) (hu : HEq u u') (hv : HEq v v')
    (hec : ∀ (α : GA D (Wc D i')) (R : Finset (GA D (Wc D i'))), IsHeckeAt (Wc D i') P k α →
      Bridge.IsDC (levG (Wc D i') (Rl.βW i') (Rl.datWp i' Rl.triv)) α R →
      (Rl.HW i' (sg0 D A3.A)).e ((Rl.FW i').j (sg0 D A3.A) u) =
        hkNorm Rl i' k P • heckeOn (Rl.MW i' (sg0 D A3.A)) R ((Rl.HW i' (sg0 D A3.A)).e ((Rl.FW i').j (sg0 D A3.A) v))) :
    ∀ (α : GA D (Wc D i)) (R : Finset (GA D (Wc D i))), IsHeckeAt (Wc D i) P k α →
      Bridge.IsDC (levG (Wc D i) (Rl.βW i) (Rl.datWp i Rl.triv)) α R →
      (Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) u') =
        hkNorm Rl i k P • heckeOn (Rl.MW i (sg0 D A3.A)) R ((Rl.HW i (sg0 D A3.A)).e ((Rl.FW i).j (sg0 D A3.A) v')) := by
  subst h
  cases hu
  cases hv
  exact hec

theorem hkRow_of_ad (Rl : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 Rl.Pg D.R.r ≃* G0g D.nd) (kKs : Ks →+* ↥D.LL0)
    (hk : ∀ x : Ks, ((kKs x : ↥D.LL0) : D.what₂.LL) = algebraMap Ks D.what₂.LL x)
    (Y : NExpRealS Rl cG (ratDatR Rl cG kKs hk)) (H : NExpRealH Rl cG _ Y) (Sb : Finset (PlE D.host))
    (hfi : ∀ i x, HEq ((Y.fi i).e x) x) (hS : ∀ i, Sb ⊆ D.ntw.S0 i)
    (hec : ∀ j k P α Rr, 1 ≤ j → j ≤ D.R.m → HkDat Rl Sb (idxOf D j) k P α Rr → ∀ x : Fin (Rl.nW (idxOf D j)) → D.what₂.LL,
      (Rl.HW (idxOf D j) (sg0 D A3.A)).e ((Rl.FW (idxOf D j)).j (sg0 D A3.A) (H.hL j k P x)) =
        hkNorm Rl (idxOf D j) k P • heckeOn (Rl.MW (idxOf D j) (sg0 D A3.A)) Rr
          ((Rl.HW (idxOf D j) (sg0 D A3.A)).e ((Rl.FW (idxOf D j)).j (sg0 D A3.A) x))) :
    NExpHeckeRowX Rl cG _ Y H fun _ => LinearMap.id := by
  refine ⟨fun i k P hsp _ hoff h2 hkr α R hα hR x _ => ?_⟩
  obtain ⟨i', hi'⟩ := hoff
  exact hkRow_move Rl (idxOf_succ D i) k P (H.hL ((i : ℕ) + 1) k P x) x ((Y.fi i).e (H.hL ((i : ℕ) + 1) k P x)) ((Y.fi i).e x)
    (hfi i _).symm (hfi i _).symm
    (fun α' R' hα' hR' => hec ((i : ℕ) + 1) k P α' R' (by omega) (by have := i.2; omega)
      ⟨hsp, fun h => hi' (hS i' h), h2, hkr, hα', hR'⟩ x) α R hα hR

end Gen

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w}

end GlobalTheory.HeightCounting.Fin3
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentReadingBundle
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlugPt

open GlobalTheory.Mem.R3 _root_.Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links



set_option maxHeartbeats 4000000 in
theorem side_mk_eq_upd {D : D7} {nch : NChoice D} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
    {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {J : Formalism.L2.Pj.CoreJ D} [Algebra J.Q.c.F D.what₂.LL] (R : RealDat3 D A3 J.Q.c.F)
    (kap : ℝ) (lam : type_of% R.lam3) (err : type_of% R.err0) (P0 P0' : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (ψ0' : P0' →* D.what₂.LLˣ)
    (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (v v' : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec)
    (S S' : Formalism.IndefR.NX.RatDat D.ntw) (Y : Formalism.IndefR.NX.NExpRealS ((R.updS kap lam).withErr err) cG S)
    (Y' : Formalism.IndefR.NX.NExpRealS R cG S') (cf : Formalism.L2.Host.CharFrame D) (tp : Formalism.L2.Host.TupTied D R.C nch)
    (tp' : Formalism.L2.Host.TupTied D cf nch) (hP : P0 = P0') (hψ : HEq ψ0 ψ0') (hv : HEq v v') (hS : HEq S S') (hfi : HEq Y.fi Y'.fi)
    (heF : HEq Y.eF Y'.eF) (hcf : R.C = cf) (htp : HEq tp tp') :
    ({ G := G, Pl0 := Pl0, I0 := I0, T := T, A3 := A3, J := J, R := (R.updS kap lam).withErr err, P0 := P0, ψ0 := ψ0, cG := cG, v₀ := v, S := S, YS := Y, cf := R.C, tp := tp } : Side D nch) =
      Side.upd { G := G, Pl0 := Pl0, I0 := I0, T := T, A3 := A3, J := J, R := R, P0 := P0', ψ0 := ψ0', cG := cG, v₀ := v', S := S', YS := Y', cf := cf, tp := tp' } kap lam err := by
  subst hP hcf
  cases eq_of_heq hψ
  cases eq_of_heq hv
  cases eq_of_heq hS
  cases eq_of_heq htp
  obtain ⟨fi, _, _, _, eF, _, _⟩ := Y
  obtain ⟨fi', _, _, _, eF', _, _⟩ := Y'
  replace hfi : fi = fi' := (eq_of_heq hfi)
  replace heF : eF = eF' := (eq_of_heq heF)
  subst hfi heF
  rfl


set_option maxHeartbeats 4000000 in
theorem side_eq_upd {D : D7} {O : Obj D} (x : R3.TwIn O.ex) (s : Side D O.ex.nch) (kap : ℝ) (lam : type_of% s.R.lam3)
    (err : type_of% s.R.err0) (F : Face3 D s.A3) (Sx : Formalism.IndefR.NX.RatDat D.ntw) (YS : Formalism.IndefR.NX.NExpRealS x.R x.cG Sx)
    (Tp : Formalism.L2.Host.TupTied D x.R.C O.ex.nch)
    (pack : (⟨x.G, x.grp, x.fin, x.Pl0, x.I0, x.T, x.A3, x.core, x.alg, x.R, x.F, x.cG⟩ :
      Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
        (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : Formalism.L2.Pj.CoreJ D)
        (_ : Algebra C.Q.c.F D.what₂.LL) (R : RealDat3 D A3 C.Q.c.F) (_ : Face3 D A3),
        G0 R.Pg D.R.r ≃* G0g D.nd) =
      ⟨s.G, s.grp, s.fin, s.Pl0, s.I0, s.T, s.A3, s.J, s.alg, (s.R.updS kap lam).withErr err, F, s.cG⟩)
    (hP : F.P0 = s.P0) (hψ : HEq F.ψ0 s.ψ0) (hv : HEq x.geo.v₀ s.v₀) (hS : HEq Sx s.S) (hfi : HEq YS.fi s.YS.fi)
    (heF : HEq YS.eF s.YS.eF) (hcf : s.R.C = s.cf) (htp : HEq Tp s.tp) :
    ({ G := x.G, Pl0 := x.Pl0, I0 := x.I0, T := x.T, A3 := x.A3, J := x.core, R := x.R, P0 := x.F.P0, ψ0 := x.F.ψ0, cG := x.cG, v₀ := x.geo.v₀, S := Sx, YS := YS, cf := x.R.C, tp := Tp } : Side D O.ex.nch) = s.upd kap lam err := by
  obtain ⟨G, Pl0, I0, T, A3, J, R, P0, ψ0, cG, v₀, S, Y, cf, tp⟩ := s
  obtain ⟨G', Pl0', I0', T', A3', core, R', F', cG', geo⟩ := x
  cases pack
  exact side_mk_eq_upd R kap lam err _ _ _ _ cG _ _ _ _ _ _ _ _ _ hP hψ hv hS hfi heF hcf htp


end GlobalTheory.PlugPt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValPosIffMemExample
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up

open GlobalTheory.Mem.Top.TwChar

theorem addValuation_pos_iff_valuation_lt_one {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : K) :
    0 < Examples₂.PlacesToy.valW w x ↔ w.valuation K x < 1 := by
  by_cases hx : x = 0
  · simp [hx]
  have h0 : w.valuation K x ≠ 0 := by simpa using hx
  rw [Examples₂.PlacesToy.valW_of_ne w hx, vAdd, ← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.log_exp]
  norm_cast
  exact neg_pos

theorem addValuation_pos_iff_mem_asIdeal {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K) :
    0 < Examples₂.PlacesToy.valW w (x : K) ↔ x ∈ w.asIdeal := by
  rw [addValuation_pos_iff_valuation_lt_one, ← w.valuation_lt_one_iff_mem (K := K)]

theorem addVal_pos_iff {K : Type} [Field K] (v : AddValuation K (WithTop ℤ)) {x : K} (hx : x ≠ 0) :
    0 < v x ↔ ¬ 0 ≤ v x⁻¹ := by
  have h : v x + v x⁻¹ = 0 := by rw [← v.map_mul, mul_inv_cancel₀ hx, v.map_one]
  generalize v x = a at h
  generalize v x⁻¹ = b at h
  cases a with
  | top => simp at h
  | coe a =>
    cases b with
    | top => simp at h
    | coe b =>
      norm_cast at h ⊢
      omega

theorem overOne_plUnder (X : Stages) {B' : Base} (h : Enl X.B B') (v v' : B'.places.Pl)
    (hv : ∀ x ∈ B'.LL0, 0 ≤ B'.places.val v x ↔ 0 ≤ B'.places.val v' x) :
    OverOne X.toD7 (plUnder h v) (plUnder h v') := by
  intro x
  let y : 𝓞 X.B.LL := algebraMap (𝓞 ↥X.B.LL0) (𝓞 X.B.LL) x
  have key : ∀ u : B'.places.Pl, 0 < Examples₂.PlacesToy.valW (K := X.B.LL) (plUnder h u) (y : X.B.LL) ↔
      0 < Examples₂.PlacesToy.valW (K := B'.LL) u (incl h (y : X.B.LL)) := fun u =>
    (addValuation_pos_iff_mem_asIdeal _ y).trans ((mem_plUnder h u y).trans
      (addValuation_pos_iff_mem_asIdeal (K := B'.LL) u (RingOfIntegers.mapRingHom (incl h) y)).symm)
  have hm : incl h (y : X.B.LL) ∈ B'.LL0 := by
    have h1 : X.B.embLL (y : X.B.LL) ∈ B'.embLL '' ↑B'.LL0 := h.2.2.1 ▸ ⟨_, (x : ↥X.toD7.LL0).2, rfl⟩
    obtain ⟨z, hz, e⟩ := h1
    rw [← B'.embLL.injective (e.trans (embLL_incl h _).symm)]
    exact hz
  refine (key v).trans (Iff.trans ?_ (key v').symm)
  by_cases h0 : incl h (y : X.B.LL) = 0
  · rw [h0, AddValuation.map_zero, AddValuation.map_zero]
  · rw [addVal_pos_iff _ h0, addVal_pos_iff _ h0]
    exact not_congr (hv _ (B'.LL0.inv_mem hm))

theorem Seed.psiOk {D : D7} {A : D.ntw.Tw → Finset (PlE D.host)} (σ : Seed D A) {v : D.what₂.places.Pl} (hv : TwistedAt D v) :
    BlochKatoReduction.Gen.PsiOk (σ.s v) (A (σ.s v)) (σ.Q (σ.s v)) (σ.k (σ.s v)) (σ.ψ (σ.s v)) := by
  classical
  have h := ((σ.good v hv).2 1 (by simp)).1
  rw [zpow_one] at h
  obtain ⟨h1, h2, h3⟩ := h
  simp only [Finset.disjoint_union_right] at h2
  exact ⟨h1, by simp only [Finset.disjoint_union_right]; exact ⟨h2.1, h2.2.2⟩, h3⟩

end GlobalTheory.HeightCounting.Up

end
end
