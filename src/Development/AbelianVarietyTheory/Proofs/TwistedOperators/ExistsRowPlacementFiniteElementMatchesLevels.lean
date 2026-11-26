module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteElementConjRowLevelCharacter
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodRowsCompareByLevelMatchingEvaluation
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsContinuousRealScalarCharacterWeakWeil
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodAtReductionConjugatedUnitaryElement

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowLevelMatchAtOfLevelConjugation
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionConjugatedUnitaryElementEqOneIff
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionConjugatedUnitaryElementEqOneIff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KapRed

open Formalism.L2.SG.RowsJoinPinned (castGA)

variable {D : D7}

theorem iotaX_symm_eq {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D) (x : I.GA) :
    ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)).symm x = (Formalism.IndefR.RationalEmbedding.iota D).symm (castGA h x) := by
  subst h
  rfl

theorem castGA_mem {I I' : Formalism.MainNotions.S.AutInst} (h : I = I') (k : I.Gf) (g : ℕ) :
    (k ∈ I.Kset ↔ (castGA h (1, k)).2 ∈ I'.Kset) ∧ (k ∈ I.Kg g ↔ (castGA h (1, k)).2 ∈ I'.Kg g) := by
  subst h
  exact ⟨Iff.rfl, Iff.rfl⟩

private theorem swapAE_map_sndA_eq_tauF (D : D7)
    (z : TensorProduct D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.host.E) :
    Formalism.IndefR.Lev.swapAE D
              (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E) z) =
      Formalism.L2.SG.AdBridge.tauF (Formalism.IndefR.RationalEmbedding.inst D) z := by
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero]
    exact (map_zero _).symm
  | tmul a x =>
    exact (Formalism.L2.SG.AdBridge.tauF_tmul (Formalism.IndefR.RationalEmbedding.inst D) a x).symm
  | add a b ha hb =>
    rw [map_add (f := _), map_add (f := _), ha, hb]
    exact (map_add _ a b).symm

private theorem finE_Yc_zero_iota_symm (y : (Formalism.L2.SG.InstExistsPf.instOf D).GA) :
    finE (Yc D 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm y) = y.2.1 := by
  have hb := (Formalism.L2.SG.AdBridge.toHA_isBridge (Formalism.IndefR.RationalEmbedding.inst D)
    (Formalism.L2.SG.Closed.adelic_isomorphism_statement (Formalism.IndefR.RationalEmbedding.inst D)).1 y).2
  apply Units.ext
  ext i j
  have hij := congrFun (congrFun hb i) j
  refine Eq.trans ?_ hij.symm
  show Formalism.IndefR.Lev.swapAE D
      (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E) _) = _
  exact swapAE_map_sndA_eq_tauF D _

abbrev kmat (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) : GL (Fin (Yc D 0).rank) (EAf D) := x.1

theorem finE_kap (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (Yc D 0))
    (k : X.B.I.Gf) :
    finE (Yc D 0) (kap X h t k) = (finE (Yc D 0) t)⁻¹ * kmat (castGA h (1, k)).2 * finE (Yc D 0) t := by
  have e2 : finE (Yc D 0) (id ((iotaX X h).symm (1, k)) : GA D (Yc D 0)) = kmat (castGA h (1, k)).2 :=
    (congrArg (finE (Yc D 0)) (iotaX_symm_eq h (1, k))).trans (finE_Yc_zero_iota_symm _)
  have e3 : finE (Yc D 0) (kap X h t k) =
      (finE (Yc D 0) t)⁻¹ * finE (Yc D 0) (id ((iotaX X h).symm (1, k)) : GA D (Yc D 0)) * finE (Yc D 0) t := by
    rw [← map_inv (finE (Yc D 0)) t, ← map_mul (finE (Yc D 0)), ← map_mul (finE (Yc D 0))]
    rfl
  rw [e3, e2]

section Gen

open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem frGL_mul_apply (t β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    Formalism.L2.DIV.frGL (t * β) y = t * Formalism.L2.DIV.frGL β y * t⁻¹ := by
  simp only [Formalism.L2.DIV.frGL, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, mul_inv_rev]
  group

theorem redFn_conj (β t x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Formalism.L2.DIV.Pl E) :
    Formalism.L2.DIV.redFn β PP (t⁻¹ * x * t) = Formalism.L2.DIV.redFn (t * β) PP x := by
  classical
  by_cases hx : x ∈ Formalism.L2.DIV.St (t * β)
  · obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hx
    have hy : t⁻¹ * Formalism.L2.DIV.frGL (t * β) y * t = Formalism.L2.DIV.frGL β y := by
      rw [frGL_mul_apply]
      group
    rw [hy, Formalism.L2.DIV.redFn_frGL, Formalism.L2.DIV.redFn_frGL]
  · have hx' : t⁻¹ * x * t ∉ Formalism.L2.DIV.St β := by
      intro hmem
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hmem
      apply hx
      refine MonoidHom.mem_range.2 ⟨y, ?_⟩
      rw [frGL_mul_apply, hy]
      group
    simp only [Formalism.L2.DIV.redFn, Formalism.L2.DIV.ext1, dif_neg hx, dif_neg hx']

end Gen

theorem upperLeftBlock_eq_one_iff_of_mem_blockTri {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (hn : n ≤ r) (g : GL (Fin n) κ) :
    Formalism.L2.DIV.upperLeftBlock hr g = 1 ↔ g = 1 := by
  obtain rfl : r = n := le_antisymm hr hn
  have hmem : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
    rw [Formalism.L2.DIV.mem_blockTri]
    intro i j hij
    simp [Formalism.L2.DIV.blk2] at hij
  have hself : Formalism.L2.DIV.upperLeftBlock hr g = g := by
    apply Units.ext
    rw [Formalism.L2.DIV.upper_block_val_submatrix hr hmem]
    ext i j
    rfl
  rw [hself]

end GlobalTheory.KapRed

namespace GlobalTheory.KapRed

theorem core (D : D7) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (β : GL (Fin (Yc D 0).rank) (EAf D))
    (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) (g : ℕ) (hβ : IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0))
    (hx : x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset) (hg : 1 ≤ g) (hrad : (Ideal.span {(g : 𝓞 D.host.E)}).IsRadical)
    (hcov : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (g : 𝓞 D.host.E) ∈ PP.asIdeal → PP ∈ Pg ∨ ∃ PP' ∈ Pg, Formalism.IndefR.Lev.IsConjPl PP' PP)
    (hin : ∀ PP ∈ Pg, (g : 𝓞 D.host.E) ∈ PP.asIdeal) :
    x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kg g ↔ ∀ PP ∈ Pg, Formalism.L2.DIV.redFn β PP x.1 = 1 := by
  rw [GlobalTheory.KgFrame.mem_Kg_iff_redFn D β x g hβ hx hg hrad]
  constructor
  · intro H PP hP
    exact H PP (hin PP hP)
  · intro H PP hgP
    rcases hcov PP hgP with hP | ⟨PP', hP', hc⟩
    · exact H PP hP
    · exact GlobalTheory.ConjPlaceRed.redFn_conj_eq_one D β x PP PP' hβ hx hc (H PP' hP')

theorem rank_lowerChainSpace_zero_le (D : D7) : (Yc D 0).rank ≤ D.R.r := by
  have e : (Yc D 0).rank = D.R.rankY 0 := D.sp.Y_rank 0 (Nat.zero_le _)
  rw [e]
  show D.R.r + 0 * D.R.t ≤ D.R.r
  simp

theorem red_kap_eq_one_iff : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ k ∈ X.B.I.Kset, (cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) = 1 ↔ k ∈ X.B.I.Kg X.B.g) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ _ cG t _ hplg _ _ _ hfr k hk
  obtain ⟨plg, -, hplgw, -, -, -⟩ := hplg
  have hk' := (castGA_mem h k X.B.g).1.1 hk
  have hpos : 1 ≤ D.host.g 0 * D.host.g 1 :=
    Nat.succ_le_of_lt (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos)
  have hin : ∀ PP ∈ R.Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hP
    have hsame := hplgw (plg.symm ⟨PP, hP⟩)
    rw [Equiv.apply_symm_apply] at hsame
    have hq : ((D.host.g (plg.symm ⟨PP, hP⟩).1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      have hov := D.naut.plGw_over (plg.symm ⟨PP, hP⟩).1 (plg.symm ⟨PP, hP⟩).2
      simp only at hsame
      have hI : PP.asIdeal =
          (D.naut.plGw (plg.symm ⟨PP, hP⟩).1 (plg.symm ⟨PP, hP⟩).2).asIdeal := by
        rw [← hsame]
      rw [hI]
      exact hov
    have hdvd : ∀ q : Fin 2, D.host.g q ∣ D.host.g 0 * D.host.g 1 := by
      intro q
      fin_cases q
      · first
        | exact dvd_mul_right _ _
        | simp
      · first
        | exact dvd_mul_left _ _
        | simp
    obtain ⟨c, hc⟩ := hdvd (plg.symm ⟨PP, hP⟩).1
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hq
  have hcore := core D R.Pg (finE (Yc D 0) t * R.βY 0) (castGA h (1, k)).2 (D.host.g 0 * D.host.g 1) hfr hk' hpos
    (GlobalTheory.TypePrimesRadical.isRadical_span_g_mul D) (GlobalTheory.TypeProductCover.place_cover_prod D R.Pg plg hplgw) hin
  rw [(castGA_mem h k X.B.g).2, X.g_eq, hcore]
  have hrt : ∀ y, cG y = 1 ↔ y = 1 := fun y =>
    ⟨fun hy => cG.injective (hy.trans (map_one cG).symm), fun hy => by rw [hy]; exact map_one cG⟩
  refine (hrt _).trans ?_
  rw [finE_kap X h t k]
  have key : ∀ PP : R.Pg,
      (rTup (R.βY 0) (R.dat0 R.triv) ((finE (Yc D 0) t)⁻¹ * kmat (castGA h (1, k)).2 * finE (Yc D 0) t) PP = 1 ↔
        Formalism.L2.DIV.redFn (finE (Yc D 0) t * R.βY 0) PP.1 (castGA h (1, k)).2.1 = 1) := by
    intro PP
    show Formalism.L2.DIV.upperLeftBlock (R.dat0 R.triv).hr (Formalism.L2.DIV.redFn (R.βY 0) PP.1 _) = 1 ↔ _
    rw [redFn_conj, upperLeftBlock_eq_one_iff_of_mem_blockTri (R.dat0 R.triv).hr (by exact rank_lowerChainSpace_zero_le D)]
  constructor
  · intro H PP hP
    exact (key ⟨PP, hP⟩).1 (congrFun H ⟨PP, hP⟩)
  · intro H
    funext PP
    exact (key PP).2 (H PP.1 PP.2)

end GlobalTheory.KapRed
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionConjugatedUnitaryElementEqOneIffStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_conjugated_unitary_element_eq_one_iff : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ k ∈ X.B.I.Kset, (cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) = 1 ↔ k ∈ X.B.I.Kg X.B.g) := by
  first | exact @GlobalTheory.KapRed.red_kap_eq_one_iff | exact GlobalTheory.KapRed.red_kap_eq_one_iff | (intros; apply GlobalTheory.KapRed.red_kap_eq_one_iff <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RightTranslateCompactLiftActsByReduction
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RightTranslateCompactLiftActsByReduction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowActLift

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem levelCharacter_rowDatum_eq_one_of_reduction_one (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) (x : GL (Fin (Yc D 0).rank) (EAf D))
    (hx : rTup (R.βY 0) (R.dat0 P) x = 1) : levFn (R.βY 0) (R.dat0 P) x = 1 := by
  unfold levFn
  rw [hx, blockDiagonalExtendByOnePrimeField_one]
  simp [Formalism.IndefR.Links.LevCh.dat0, datY]

theorem levelCharacter_flag_rowDatum_eq_one (R : RealDat D A Ks) (P : LevelP R.Pg D.R.r ℂ) (x : GL (Fin (Yc D 0).rank) (EAf D)) :
    levFn (R.βY 0) (flagL (R.dat0 P)) x = 1 := by
  have h2 : ext1 (flagL (R.dat0 P)).P.H (flagL (R.dat0 P)).P.chi (rTup (R.βY 0) (flagL (R.dat0 P)) x) = 1 :=
    subgroupCharExtension_one_apply _ _
  unfold levFn
  rw [h2]
  simp [flagL, withP, Formalism.IndefR.Links.LevCh.dat0, datY]

theorem mem_lev_of_flag1 (R : RealDat D A Ks) (P P' : LevelP R.Pg D.R.r ℂ) {κ : GA D (Yc D 0)}
    (hκ : κ ∈ levG (Yc D 0) (R.βY 0) (flag1L (R.dat0 P'))) :
    κ ∈ levS (Yc D 0) (R.βY 0) (R.dat0 P) ∧
      levChi (Yc D 0) (R.βY 0) (R.dat0 P) κ = levChi (Yc D 0) (R.βY 0) (flag1L (R.dat0 P')) κ := by
  obtain ⟨h1, h2, h3⟩ := hκ
  have h3' : rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) = 1 := Subgroup.mem_bot.1 h3
  refine ⟨⟨h1, h2, ?_⟩, ?_⟩
  · show rTup (R.βY 0) (R.dat0 P) (finE (Yc D 0) κ) ∈ (R.dat0 P).P.H
    rw [h3']; exact Subgroup.one_mem _
  · unfold levChi
    rw [levelCharacter_rowDatum_eq_one_of_reduction_one R P _ h3', levFn_flag1, levelCharacter_flag_rowDatum_eq_one]

theorem hasType_flag1_of_mem (R : RealDat D A Ks) (P P' : LevelP R.Pg D.R.r ℂ) {T : MMap (R.MY 0)}
    (hT : T ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 P)) (levChi (Yc D 0) (R.βY 0) (R.dat0 P)))
    (v : (R.MY 0).Vec) : HasType (Yc D 0) (R.βY 0) (flag1L (R.dat0 P')) (T v) := by
  induction hT using Submodule.span_induction with
  | mem S hS =>
    intro κ hκ g
    obtain ⟨hm, hc⟩ := mem_lev_of_flag1 R P P' hκ
    rw [hS.lev v κ hm g, hc]
  | zero =>
    intro κ _ g
    simp
  | add S S' _ _ hS hS' =>
    intro κ hκ g
    simp only [MultilinearMap.add_apply, Pi.add_apply]
    rw [hS κ hκ g, hS' κ hκ g, mul_add]
  | smul c S _ hS =>
    intro κ hκ g
    simp only [MultilinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    rw [hS κ hκ g, mul_left_comm]

theorem act_kap : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ k ∈ X.B.I.Kset, ∀ T ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))), ∀ (v : (MP R).Vec) (g : GA D (Yc D 0)), (T : MMap (MP R)) v (g * kap X h t k) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) ((T : MMap (MP R)) v) g := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod cG t hιE hpin hE0 ht hConj hFrame k hk T' hT v g
  have hl := GlobalTheory.T.conjugate_maximalCompact_mem_parahoricLevel R F X h hLev hGrp hMod cG t hιE hpin hE0 ht hConj hFrame k hk
  have hlift : IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv)
      (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) (kap X h t k) := ⟨hl.1, hl.2, rfl⟩
  have hType := hasType_flag1_of_mem R (R.levR F true) R.triv hT v
  have hs := level_action_spec hType ⟨_, hlift⟩ _ hlift g
  have hc : levChi (Yc D 0) (R.βY 0) (flagL (R.dat0 R.triv)) (kap X h t k) = 1 := by
    unfold levChi; rw [levelCharacter_flag_rowDatum_eq_one]; rfl
  show _ = actG0 (Yc D 0) (R.βY 0) (R.dat0 R.triv) _ _ g
  rw [hs, hc, inv_one, one_mul]

end GlobalTheory.RowActLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RightTranslateCompactLiftActsByReductionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightTranslate_compactLift_acts_by_reduction : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ k ∈ X.B.I.Kset, ∀ T ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))), ∀ (v : (MP R).Vec) (g : GA D (Yc D 0)), (T : MMap (MP R)) v (g * kap X h t k) = actL (Yc D 0) (R.βY 0) (R.dat0 R.triv) (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) ((T : MMap (MP R)) v) g := by
  first | exact @GlobalTheory.RowActLift.act_kap | exact GlobalTheory.RowActLift.act_kap | (intros; apply GlobalTheory.RowActLift.act_kap <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowLevelMatchAtOfLevelConjugation
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem conj_mem_and_char_eq_of_levelConjugation {H : Type} [Group H] (t s : H) (J J' : Set H) (χ χ' : H → ℂ)
    (hc : ∀ k, (k ∈ J ↔ t⁻¹⁻¹ * k * t⁻¹ ∈ J') ∧ (k ∈ J → χ' (t⁻¹⁻¹ * k * t⁻¹) = χ k)) (hs : s ∈ J') :
    t⁻¹ * s * t ∈ J ∧ χ (t⁻¹ * s * t) = χ' s := by
  have e : t⁻¹⁻¹ * (t⁻¹ * s * t) * t⁻¹ = s := by group
  have h := hc (t⁻¹ * s * t)
  rw [e] at h
  exact ⟨h.1.2 hs, (h.2 (h.1.2 hs)).symm⟩

theorem conj_mul_eq_mul_conj_group {H : Type} [Group H] (t a b : H) : t⁻¹ * (a * b) * t = (t⁻¹ * a * t) * (t⁻¹ * b * t) := by
  group

theorem rowLevelMatchAt_of_conjLevel : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → RowLevelMatchAt R F X h t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod cG t hιE hPin hE0 ht hConj hFrame
  obtain ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ := hPin
  refine ⟨(R.eG.trans cG).symm, fun k => cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))), ?_, ?_, ?_⟩
  · intro k hk
    have e2 : (iotaX X h).toMulEquiv ((iotaX X h).symm (1, k)) = (1, k) :=
      (iotaX X h).toMulEquiv.apply_symm_apply (1, k)
    have hs : (iotaX X h).symm (1, k) ∈ (iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2} := by
      rw [Set.mem_preimage, e2]; exact ⟨rfl, hk⟩
    have hA := conj_mem_and_char_eq_of_levelConjugation (H := GA D (Yc D 0)) t ((iotaX X h).symm (1, k)) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) (fun k' => hConj k') hs
    refine ⟨hA.1, hA.2.trans ?_⟩
    show star (X.chi2 ((iotaX X h).toMulEquiv ((iotaX X h).symm (1, k))).2) = _
    rw [e2]
  · obtain hl := GlobalTheory.T.conjugate_maximalCompact_mem_parahoricLevel R F X h hLev hGrp hMod cG t hιE ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ hE0 ht hConj hFrame
    refine ⟨⟨GlobalTheory.T.goodAt_reduction_conjugated_unitary_element R F X h hLev hGrp hMod cG t hιE ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ hE0 ht hConj hFrame, ?_,
      GlobalTheory.T.surjective_reduction_onto_finiteLevelGroup R F X h hLev hGrp hMod cG t hιE ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ hE0 ht hConj hFrame,
      GlobalTheory.T.reduction_conjugated_unitary_element_eq_one_iff R F X h hLev hGrp hMod cG t hιE ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ hE0 ht hConj hFrame⟩, ?_⟩
    · intro k hk k' hk'
      have e1 : (iotaX X h).symm (1, k * k') = (iotaX X h).symm (1, k) * (iotaX X h).symm (1, k') := by
        rw [← map_mul, Prod.mk_mul_mk, one_mul]
      have e : kap X h t (k * k') = kap X h t k * kap X h t k' := by
        unfold kap; rw [e1]; exact conj_mul_eq_mul_conj_group (H := GA D (Yc D 0)) t _ _
      show cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t (k * k')))) = cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) * cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k')))
      rw [e, map_mul, Formalism.L2.DIV.rTup_mul (hl k hk).2 (hl k' hk').2]
      exact map_mul cG _ _
    · intro k hk T hT v g
      rw [GlobalTheory.T.rightTranslate_compactLift_acts_by_reduction R F X h hLev hGrp hMod cG t hιE ⟨plg, iso, hpl, hcoef, hdiv, hbc⟩ hE0 ht hConj hFrame k hk T hT v g]
      have e3 : R.eG ((R.eG.trans cG).symm (cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))))) = rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k)) := by
        rw [MulEquiv.symm_trans_apply]
        exact (congrArg (fun y => R.eG (R.eG.symm y)) (cG.symm_apply_apply _)).trans (R.eG.apply_symm_apply _)
      rw [e3]
  · intro γ
    unfold RealDat.eC
    rw [hE0 γ, hcoef, MulEquiv.apply_symm_apply]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowLevelMatchAtOfLevelConjugationStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowLevelMatchAt_of_levelConjugation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → RowLevelMatchAt R F X h t := by
  first | exact @GlobalTheory.rowLevelMatchAt_of_conjLevel | exact GlobalTheory.rowLevelMatchAt_of_conjLevel | (intros; apply GlobalTheory.rowLevelMatchAt_of_conjLevel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRowPlacementFiniteElementMatchesLevels
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem rowPlacement_iota_eq {D : D7} {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.IndefR.RationalEmbedding.inst D)
    (ι : GA D (Yc D 0) ≃* I.GA) (hι : HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv) :
    ι = ((Formalism.IndefR.RationalEmbedding.iota D).trans (Formalism.L2.SG.RowsJoinPinned.castGA h.symm)).toMulEquiv := by
  subst h
  have := eq_of_heq hι
  subst this
  rfl

theorem rowPlacement_exists : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp X) (h : X.B.I = Formalism.IndefR.RationalEmbedding.inst D) (ι : GA D (Yc D 0) ≃* X.B.I.GA) (tS : GA D (Yc D 0)) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → IdempotentRealFixed D → HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → tS ∈ GfC (Yc D 0) → ((∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (ι ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 (ι k).2)) ∧ RowLevelMatchAt R F X h t) → ConjLevel (tS)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (ι ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 (ι k).2)) ∧ RowLevelMatchAt R F X h tS) → (∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (ι ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 (ι k).2)) ∧ RowLevelMatchAt R F X h t) ∧ ∃ c' : ℝ, EvalTieT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) X Gd ι tS c' := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X Gd h ι tS cG hlev hgrp hmod hhost hE0 hι hιE hpin htS hmove
  have hιeq : ι = (iotaX X h).toMulEquiv := rowPlacement_iota_eq h ι hι
  subst hιeq
  have hfirst : ∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)))
      (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)))
      ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2})
      (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) ∧ RowLevelMatchAt R F X h t := by
    obtain ⟨t, ht, hconj, hframe⟩ := GlobalTheory.T.exists_finite_element_conj_rowLevel_character R F X h hlev hgrp hmod
    exact ⟨t, ht, hconj, GlobalTheory.T.rowLevelMatchAt_of_levelConjugation R F X h hlev hgrp hmod cG t hιE hpin hE0 ht hconj hframe⟩
  obtain ⟨hconjS, hmatchS⟩ := hmove hfirst
  exact ⟨hfirst, GlobalTheory.T.goodRows_compare_by_levelMatching_evaluation hDS R F X h hlev hgrp hmod hhost hιE Gd tS htS hconjS hmatchS⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRowPlacementFiniteElementMatchesLevelsStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rowPlacement_finiteElement_matches_levels : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp X) (h : X.B.I = Formalism.IndefR.RationalEmbedding.inst D) (ι : GA D (Yc D 0) ≃* X.B.I.GA) (tS : GA D (Yc D 0)) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → IdempotentRealFixed D → HEq ι (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv → (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → tS ∈ GfC (Yc D 0) → ((∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (ι ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 (ι k).2)) ∧ RowLevelMatchAt R F X h t) → ConjLevel (tS)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (ι ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 (ι k).2)) ∧ RowLevelMatchAt R F X h tS) → (∃ t ∈ GfC (Yc D 0), ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (ι ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 (ι k).2)) ∧ RowLevelMatchAt R F X h t) ∧ ∃ c' : ℝ, EvalTieT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) X Gd ι tS c' := by
  first | exact @GlobalTheory.rowPlacement_exists | exact GlobalTheory.rowPlacement_exists | (intros; apply GlobalTheory.rowPlacement_exists <;> assumption)
end
