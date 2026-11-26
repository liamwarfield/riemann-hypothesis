module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionSplitPlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetEqChartPointCoset
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetEqChartPointCoset
noncomputable section

namespace GlobalTheory.TwV

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem smul_sub_mem_of_frames {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {SB : Finset (HeightOneSpectrum (𝓞 E))}
    {N : Submodule (𝓞 E) (Sp E n)} {fr : Frs E n SB} (hf : GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation.IsFrames N fr) (P : SB) (s : E) (a b y₀ : Sp E n)
    (ha : ∀ l, IntAt P.1 (s * ((fr P).symm a - y₀) l)) (hb : ∀ l, IntAt P.1 (s * ((fr P).symm b - y₀) l)) :
    s • (a - b) ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal N := by
  have h : s • (fr P).symm (a - b) ∈ stdAt E n P.1 := GlobalTheory.TopStep.mem_stdAt.2 fun l => by
    have := GlobalTheory.TopStep.intAt_sub (ha l) (hb l)
    convert this using 1
    simp only [Pi.smul_apply, smul_eq_mul, map_sub, Pi.sub_apply]
    ring
  have := (hf P _).2 h
  rwa [map_smul, LinearEquiv.apply_symm_apply] at this

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}

theorem chartBaseRepresentative_penultimate_step (A : AdData t u μ St) (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (P : SB t μ) :
    y0At A (t.m2 + 1) hi β P = A.y0 β P := by
  unfold y0At
  rw [dite_eq_left rfl]

end

theorem cosetOf_eq_yb : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ c, cosetOf A (t.m2 + 1) (cpl_lt t μ).le ((St _ (cpl_lt t μ).le).chOf c) (A.pt _ (cpl_lt t μ).le c) = A.yb c) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _ H c
  obtain ⟨w, -, hw⟩ := H.chain.2.1 c
  have hwm : w ∈ A.yb c := by
    rw [hw, Set.mem_setOf_eq, sub_self]
    exact zero_mem _
  ext y
  constructor
  · intro hy
    rw [hw, Set.mem_setOf_eq, locLat, Submodule.mem_iInf]
    intro P
    rw [Submodule.mem_comap]
    have h1 := hy P
    have h2 := H.coset c w hwm P
    rw [chartBaseRepresentative_penultimate_step] at h1
    unfold SameCoset at h1 h2
    have key := smul_sub_mem_of_frames (GlobalTheory.ColPeriod.isFrames_frsF (A.pt _ (cpl_lt t μ).le c)) P _ y w _ h1 h2
    by_cases hP : P.1 ∈ t.Pr.vGs
    · simp only [hP, if_true] at key ⊢
      simpa using key
    · simp only [hP, if_false] at key ⊢
      simpa [zpow_natCast] using key
  · intro hy P
    rw [chartBaseRepresentative_penultimate_step]
    exact H.coset c y hy P

end GlobalTheory.TwV

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CouplingCosetEqChartPointCosetStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCoset_eq_chartPointCoset : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ c, cosetOf A (t.m2 + 1) (cpl_lt t μ).le ((St _ (cpl_lt t μ).le).chOf c) (A.pt _ (cpl_lt t μ).le c) = A.yb c) := by
  first | exact @GlobalTheory.TwV.cosetOf_eq_yb | exact GlobalTheory.TwV.cosetOf_eq_yb | (intros; apply GlobalTheory.TwV.cosetOf_eq_yb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroTrivialStabilisersTrueColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroTrivialStabilisersTrueColumns
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Pdv.StabZero

open GlobalTheory.Mem.Col2.ClsZero

variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem idx_empty (a : I.ι) (u : B.Word) {b : (I.stp u a 0).β} (p : (I.stp u a 0).D b) : p.1.2 = ∅ := by
  obtain ⟨⟨q, Y⟩, hY⟩ := p
  rw [ys0 a] at hY
  exact hY

theorem gam_eq_one (h : I.Ok) (u : B.Word) (a : I.ι)
    (hm : ∀ c' : (I.stp u I.mu0 0).Cl, Nat.card ((I.stp u I.mu0 0).Stab c') = 1)
    (c : (I.stp u a 0).Cl) (s : (I.stp u a 0).Stab c) : s.1.1 = 1 := by
  obtain ⟨b⟩ := stepZero_chartIndex_nonempty h a
  obtain ⟨c', rfl⟩ := (bij0 h u a b).2 c
  have hd := stepZero_corresponding_representatives_same_deco h u a b c'
  set p := (I.stp u a 0).rep (I.cl0 u a b c') with hp
  set p0 := (I.stp u I.mu0 0).rep c' with hp0
  have hs : _ = _ := s.2
  have hsd : ((s.1.1, (s.1.2.1.1 : GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs))) : UF B.fields.E (B.R.N 0) × GLG (E := B.fields.E) (n := B.R.N 0) (SG := (B.primes X).vGs)) • p.1.1.deco = p.1.1.deco :=
    congrArg (fun x => DecoF.deco x.1.1) hs
  rw [hd] at hsd
  have hγ : ∀ (P : HeightOneSpectrum (𝓞 B.fields.E)) (z : Sp B.fields.E (B.R.N 0)),
      s.1.1.1 z ∈ p0.1.1.deco.1.at P ↔ z ∈ p0.1.1.deco.1.at P := by
    intro P z
    have e := congrArg (fun d : DecoSet (E := B.fields.E) (n := B.R.N 0) (ST := (B.primes X).vT u) (SG := (B.primes X).vGs) => s.1.1.1 z ∈ d.1.at P) hsd
    simp only at e
    rw [← e]
    show s.1.1.1 z ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Formalism.HermitianLatticesTheory.gmap s.1.1.1 _) ↔ _
    rw [mem_localization_gmap, LinearEquiv.symm_apply_apply]
  have hc : ∀ P, ((p0.1.1.1.2 P)⁻¹ * (s.1.1.1 * p0.1.1.1.2 P)) ∈ GLint B.fields.E (B.R.N 0) P.1 := by
    intro P x
    show (p0.1.1.1.2 P).symm (s.1.1.1 (p0.1.1.1.2 P x)) ∈ stdAt _ _ P.1 ↔ x ∈ stdAt _ _ P.1
    rw [← p0.1.1.2 P, LinearEquiv.apply_symm_apply, ← p0.1.1.2 P x]
    exact hγ P.1 _
  let t : (I.stp u I.mu0 0).G c'.1 :=
    (s.1.1, ⟨s.1.2.1.1, by
      have e1 := levelTypePrimes_stepZero_eq_colLev h I.mu0 c'.1
      have e2 := levelTypePrimes_stepZero_eq_colLev h a b
      rw [e1, ← e2]
      exact s.1.2.1.2⟩,
     ⟨fun P => ⟨(p0.1.1.1.2 P)⁻¹ * (s.1.1.1 * p0.1.1.1.2 P), hc P⟩, by
      rw [chartIndexLevelTwistPrimes_stepZero_eq_top h I.mu0 c'.1]
      intro P _
      trivial⟩)
  let st : (I.stp u I.mu0 0).Stab c' := ⟨t, by
    show _ = _
    refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext hsd ?_)) ?_)
    · funext P
      show s.1.1.1 * p0.1.1.1.2 P * (⟨(p0.1.1.1.2 P)⁻¹ * (s.1.1.1 * p0.1.1.1.2 P), hc P⟩⁻¹ : ↥(GLint B.fields.E (B.R.N 0) P.1)).1 = p0.1.1.1.2 P
      simp only [Subgroup.coe_inv]
      group
    · show (fun v => s.1.1.1 v) '' p0.1.2 = p0.1.2
      rw [idx_empty I.mu0 u p0, Set.image_empty]⟩
  have hsub := (Nat.card_eq_one_iff_unique.1 (hm c')).1
  have e : st = 1 := Subsingleton.elim _ _
  exact congrArg (fun x : (I.stp u I.mu0 0).Stab c' => x.1.1) e

theorem card_stab_zero (h : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι)
    (hm : ∀ c' : (I.stp u I.mu0 0).Cl, Nat.card ((I.stp u I.mu0 0).Stab c') = 1) (c : (I.stp u a 0).Cl) :
    Nat.card ((I.stp u a 0).Stab c) = 1 := by
  have e : ∀ s : (I.stp u a 0).Stab c, s = 1 := fun s =>
    Subtype.ext (((l.ch u a).step 0).stab_inj c.1 s.1 _ s.2 (by
      change (ufGL _ _) s.1.1 = 1
      rw [gam_eq_one h u a hm c s, map_one]))
  exact Nat.card_eq_one_iff_unique.2 ⟨⟨fun s s' => (e s).trans (e s').symm⟩, ⟨1⟩⟩

end GlobalTheory.Pdv.StabZero

namespace GlobalTheory.Pdv

open GlobalTheory.Pdv.StabZero

theorem stepZero_trivial_stabilisers_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    LevelData (I.rec7 l Z) → OrbitPlaces.Stab0 (I.rec7 l Z) := by
  intro B X I h _ l Z lev
  exact ⟨Formalism.L2.G.StabilizerCardinality.card_stab0_mem _ lev,
    fun u μ _ c => card_stab_zero h l u μ (fun c' => Formalism.L2.G.StabilizerCardinality.card_stab0_mem _ lev u c') c⟩

end GlobalTheory.Pdv

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StepZeroTrivialStabilisersTrueColumnsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stab0_rec7_of_levelData : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), LevelData (I.rec7 l Z) → OrbitPlaces.Stab0 (I.rec7 l Z) := by
  first | exact @GlobalTheory.Pdv.stepZero_trivial_stabilisers_trueColumns | exact GlobalTheory.Pdv.stepZero_trivial_stabilisers_trueColumns | (intros; apply GlobalTheory.Pdv.stepZero_trivial_stabilisers_trueColumns <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelPairScalarsIsUnitTrueColumns
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelPairScalarsIsUnitTrueColumns
noncomputable section

namespace GlobalTheory.Pdv.UnStd

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.KerJ
open GlobalTheory.Mem.Chr (finPartI finPartI_eq_self unitIdl)

theorem mtType_of_frame_mul {D : D7} {C : CharFrame D} (Dt : DtTied D C) (ξ : HChar D.host.E) {n : ℕ} (hn : 0 < n)
    (hord : ξ.OrderDvd n) (mt : ℕ → D.Dt →* ℂˣ)
    (h : ∀ (j : Fin D.R.m) a, IsFinIdele a → mt (j.1 + 1) (Dt.eDt a) = (C.mu0 j * ξ).1 a) (u : D.what₂.Word) :
    MtType u mt := by
  letI := D.host.cmStar
  have hcm : IsCMField D.host.E := D.host.isCMField_hostE
  intro i hi
  have hun : (C.mu0 ⟨i, hi⟩ * ξ).IsUnitary := fun x => by
    have e : (C.mu0 ⟨i, hi⟩ * ξ).1 x = (C.mu0 ⟨i, hi⟩).1 x * ξ.1 x := rfl
    rw [e, Units.val_mul, norm_mul, (C.isMu0 ⟨i, hi⟩).unitary x, CharModel.isUnitary_of_orderDvd hn hord x, one_mul]
  refine ⟨fun k hk => ?_, ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (Dt.UO_eq k).1 hk
    obtain ⟨m, hm, hu⟩ := GlobalTheory.UnUnitCmp.Val.finUnit_pow _ hun
    refine ⟨m, hm, Units.ext ?_⟩
    rw [← CharModel.eDt_finPart Dt a, h ⟨i, hi⟩ _ (CharModel.isFin_finPart a), Units.val_pow_eq_pow_val]
    exact hu _ (CharModel.isFin_finPart a) ha
  · choose e he using fun τ => (D.hcW u τ).e_int ⟨i, hi⟩
    refine ⟨e, fun τ => (he τ).symm, fun z => ?_⟩
    obtain ⟨k, hk⟩ := GlobalTheory.Mem.Col2.exists_eq_div_conj D.host z
    obtain ⟨m, hm, hinf⟩ := (C.isMu0 ⟨i, hi⟩).inf
    rw [← Dt.rat k z hk, ← CharModel.eDt_finPart Dt, h ⟨i, hi⟩ _ (CharModel.isFin_finPart _),
      show diagUnits D.host.E k = GlobalTheory.Mem.Chr.diagUnits D.host.E k from rfl,
      GlobalTheory.Mem.Chr.DetGroupModel.fin_diag,
      HChar.inf_mul, GlobalTheory.TypeValues.inf_eq_one _ hn hord, mul_one, Units.val_inv_eq_inv_val, hinf k,
      ← Finset.prod_inv_distrib, ← D.eTau.prod_comp]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have hme : m (D.eTau τ) = 2 * -e τ := by
      have h1 := hm (D.eTau τ)
      have h2 : eExp D ⟨i, hi⟩ (D.eTau τ) = e τ := by
        rw [← he τ, D.hcW_e]; simp [eExp]
      simp only [h2] at h1
      exact_mod_cast h1
    have h1 := congrArg (embPsi D.host (D.eTau τ)) hk
    rw [map_mul, GlobalTheory.Mem.Chr.DetGroupModel.emb_conj] at h1
    have h0 : embPsi D.host (D.eTau τ) (k : D.host.E) ≠ 0 := by simp
    show _ = embPsi D.host (D.eTau τ) z.1 ^ e τ
    generalize embPsi D.host (D.eTau τ) (k : D.host.E) = a at *
    generalize embPsi D.host (D.eTau τ) z.1 = b at *
    have hn' : ((‖a‖ : ℝ) : ℂ) ≠ 0 := by simpa using h0
    have h2 : a * star a = ((‖a‖ : ℝ) : ℂ) ^ 2 := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have h3 : (a / ((‖a‖ : ℝ) : ℂ)) ^ (2 : ℤ) = b := by
      rw [zpow_ofNat, div_pow, div_eq_iff (pow_ne_zero _ hn'), ← h2]
      linear_combination (-a) * h1
    rw [hme, zpow_mul, h3, zpow_neg, inv_inv]

end GlobalTheory.Pdv.UnStd

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Pdv.UnStd

open Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.KerJ

theorem mtType_stdO {B : Base} {X : PreX B.toPre} (I : TC B X) (hok : I.Ok) (hp : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) {Qp : I.ι → Finset ℕ} {O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)}
    (hO : I.StdO l Z Qp O) (u : (I.rec7 l Z).what₂.Word) (a : (I.rec7 l Z).what₂.Tup) : MtType u (O u a).mt := by
  obtain ⟨T, hT⟩ := TC.dtTied_true I hok hp l Z
  have ht : IsOfFinOrder (I.tup a : Chr B.fields.F B.fields.E B.fields.K) :=
    (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 (I.tup a).2).1).1).1).2
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 ht
  have hk : KDq B.host I.SQ ≤ ((I.xi a).1.comp (finPartI B.host.E)).ker :=
    (KDq_anti B.host (I.Q_subset_SQ a)).trans ((GlobalTheory.Mem.LevTwist.levOk_twists B X I hok).2.2 a).1
  refine mtType_of_frame_mul T (I.xi a) hn ((hok.xi_reads a).orderDvd hpow) _ (fun j x hx => ?_) u
  have hm : 1 ≤ j.1 + 1 ∧ j.1 + 1 ≤ B.R.m := ⟨by omega, j.2⟩
  have e1 : (O u a).mt (j.1 + 1) = (I.rec7 l Z).muTil (j.1 + 1) * (show (I.rec7 l Z).Dt →* ℂˣ from tildeQ B.host I.SQ (I.xi a)) := by
    rw [hO.mt u a]
    exact if_pos hm
  rw [e1, MonoidHom.mul_apply, T.muTil_eq j x hx, hT x]
  have e2 : (tildeQ B.host I.SQ (I.xi a)) (QuotientGroup.mk x) = (I.xi a).1 x :=
    (tildeQ_mk B.host I.SQ hk x).trans (congrArg _ (finPartI_eq_self hx))
  exact congrArg _ e2

end GlobalTheory.Pdv.UnStd


open GlobalTheory.Pdv.UnStd in
theorem GlobalTheory.Pdv.unUnit_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → t.ent.UnUnit := by
  intro B X I hok hp l Z L hT Gi Gl K Y cX ex t hs
  exact GlobalTheory.KerJ.unUnit_of_mtType _ L hT Gi Gl K Y cX ex t (fun u μ => mtType_stdO I hok hp l Z hs.O u μ)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelPairScalarsIsUnitTrueColumnsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelPairScalars_isUnit_trueColumns : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex), I.StdKer l Z t → t.ent.UnUnit := by
  first | exact @GlobalTheory.Pdv.unUnit_stdKer | exact GlobalTheory.Pdv.unUnit_stdKer | (intros; apply GlobalTheory.Pdv.unUnit_stdKer <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntriesHypOfColumnSideProperties
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntriesHypOfHeckeCharacterConditions
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumPeriodLatticeIdealFgOfHeckeCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumPeriodLatticeIdealFgOfHeckeCharacters
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory

theorem forall_val_of_heq_hom {E : Type} [Field E] {a b b' : ℕ} (hb : b = b') (P : ℂ → Prop)
    {f : HomE E a b → ℂ} {g : HomE E a b' → ℂ} (h : HEq f g) (hg : ∀ x, P (g x)) : ∀ x, P (f x) := by
  subst hb
  rw [eq_of_heq h]
  exact hg

theorem kernel_datum_of_hecke_character_values : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → (∀ μ k, D.host.g k ∉ Y.Qp μ) → t.Hyp0 := by
  intro D L hT Gi Gl K Y cX ex t h1 h2 hQ
  obtain ⟨hFG, hsd⟩ := GlobalTheory.T.kernelDatum_periodIdeal_fg_and_selfDual D L hT Gi Gl K Y cX ex t
  refine ⟨hFG, fun u μ i hi c c' hpin => ⟨hsd u μ i c, hsd u μ (i + 1) c', ?_⟩⟩
  have hm : D.R.m = t.m2 + 2 := (t.idx_ok μ).hm
  obtain ⟨-, -, pt, ix, yb, row, -, hyb, hE, hC1, -, hC2, -, hp⟩ := t.rd_chain u μ
  rcases lt_trichotomy i t.m2 with hlt | heq | hgt
  · intro x
    rw [hE i hlt c c' x]
    exact GlobalTheory.T.isIntegralOffPrimes_matrixStepEntryData D L hT Gi Gl K Y cX ex t h1 h2 u μ (hQ μ) i hlt _ _ _ _ x
  · subst heq
    intro x
    rw [hC1 c c' x]
    exact GlobalTheory.T.precedingStepDatum_integral_away_from_levels D L hT Gi Gl K Y cX ex t h1 h2 u μ (hQ μ) _ _ _ _ x
  · have hi' : i = t.m2 + 1 := by omega
    subst hi'
    obtain ⟨d, hd⟩ := (hp c').1 hpin
    refine forall_val_of_heq_hom (congrArg D.R.N (by omega : t.m2 + 1 + 1 = D.R.m))
      (IntOff (t.O u μ).S) (hC2 c c' d hd) fun x => ?_
    exact GlobalTheory.T.lastStep_data_integralAwayFrom_levels D L hT Gi Gl K Y cX ex t u μ _ _ d x (hyb c)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelDatumPeriodLatticeIdealFgOfHeckeCharactersStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelDatum_periodLatticeIdeal_fg_of_heckeCharacters : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → (∀ μ k, D.host.g k ∉ Y.Qp μ) → t.Hyp0 := by
  first | exact @GlobalTheory.kernel_datum_of_hecke_character_values | exact GlobalTheory.kernel_datum_of_hecke_character_values | (intros; apply GlobalTheory.kernel_datum_of_hecke_character_values <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntriesHypOfHeckeCharacterConditions
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical

namespace GlobalTheory

theorem hypFree_of_top_int : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), t.TopPinned → t.TopInt → t.HypFree := by
  intro D L hT Gi Gl K Y cX ex t hTop hInt u μ i hi c c' hnp
  have hsd := (GlobalTheory.TieLat.tie_AA_fg_and_sd D L hT Gi Gl K Y cX ex t).2 u μ
  refine ⟨hsd i c, hsd (i + 1) c', ?_⟩
  have hm : D.R.m = t.m2 + 2 := (t.idx_ok μ).hm
  obtain ⟨-, -, pt, ix, yb, pT, -, -, -, -, -, hpin, -⟩ := hTop u μ
  have hi' : i = t.m2 + 1 := by
    by_contra hne
    exact hnp (hpin (i + 1) (by omega) c')
  subst hi'
  exact hInt u μ c c' hnp

theorem kerEntTied_hyp : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → (∀ μ k, D.host.g k ∉ Y.Qp μ) → t.TopPinned → t.Hyp := by
  intro D L hT Gi Gl K Y cX ex t h1 h2 hQ hTop
  have h0 : t.Hyp0 := by
    first
      | exact GlobalTheory.T.kernelDatum_periodLatticeIdeal_fg_of_heckeCharacters D L hT Gi Gl K Y cX ex t h1 h2 hQ
      | exact GlobalTheory.T.kernelDatum_periodLatticeIdeal_fg_of_heckeCharacters D L hT Gi Gl K Y cX ex t h1 h2
  exact hypotheses_of_base_hypotheses D L hT Gi Gl K Y cX ex t h0
    (hypFree_of_top_int D L hT Gi Gl K Y cX ex t hTop (GlobalTheory.T.lastStepKernelData_integral_awayFromLevels D L hT Gi Gl K Y cX ex t hTop))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntriesHypOfHeckeCharacterConditionsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.L2.DIV Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelEntries_hyp_of_heckeCharacterConditions : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), (∀ j, ∃ e, Formalism.L2.Col.IsMu0 t.Ch t.seam.σ₀ e j (t.glob.mu0 j)) → (∀ (j : Fin D.R.m) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 t.X.E)), (∀ i, ((t.Pr.g i : ℕ) : 𝓞 t.X.E) ∉ v.asIdeal) → t.seam.σ₀ (t.Ch.muVal j v : t.X.K) = (((t.glob.mu0 j).val v : ℂˣ) : ℂ)) → (∀ μ k, D.host.g k ∉ Y.Qp μ) → t.TopPinned → t.Hyp := by
  first | exact @GlobalTheory.kerEntTied_hyp | exact GlobalTheory.kerEntTied_hyp | (intros; apply GlobalTheory.kerEntTied_hyp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntriesHypOfColumnSideProperties
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Formalism.L2.DIV

namespace GlobalTheory.KerJ.ColSideHyp

theorem plc_dvd_iff' {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n : ℕ) :
    Formalism.EigenvalueLevelCeiling.plc v ∣ n ↔ (n : 𝓞 F) ∈ v.asIdeal := by
  unfold Formalism.EigenvalueLevelCeiling.plc
  rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl K Y cX}

theorem g_not_mem_Qp (t : KerEntTied ex) (hC : GlobalTheory.KerJ.ColSide t) (μ : D.what₂.Tup) (k : Fin 2) : D.host.g k ∉ Y.Qp μ := by
  classical
  intro hk
  obtain ⟨hp, P, hPQ, hgP⟩ := (t.Q_rec μ (D.host.g k)).1 hk
  unfold QE at hPQ
  split_ifs at hPQ with h
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hPQ
    rw [Set.Finite.mem_toFinset] at hv
    have hgood : GoodPl t.X.E t.S v := by
      by_contra hg
      apply hv
      have h2 := (Subgroup.mem_inf.1 (t.tup μ).2).2
      exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 v) hg
    have hvF : ((D.host.g k : ℕ) : 𝓞 t.X.F) ∈ v.asIdeal := by
      rw [← hC.sel v]
      change algebraMap (𝓞 t.X.F) (𝓞 t.X.E) _ ∈ (t.sel v).asIdeal
      rw [map_natCast]
      exact hgP
    have hd := (plc_dvd_iff' v _).2 hvF
    have hpl : Formalism.EigenvalueLevelCeiling.plc v = D.host.g k :=
      ((Nat.dvd_prime hp).1 hd).resolve_left fun e => by
        have h1 := (plc_dvd_iff' v 1).1 (by rw [e])
        rw [Nat.cast_one] at h1
        exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
    apply hgood.2.2
    rw [hpl, ← t.g_rec k]
    exact hC.bad.1 k
  · simp at hPQ

end GlobalTheory.KerJ.ColSideHyp

namespace GlobalTheory

theorem colSide_hyp : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.KerJ.ColSide t → t.TopPinned → t.Hyp := by
  intro D L hT Gi Gl K Y cX ex t hC hTop
  obtain ⟨eta, hTied⟩ := hC.chars
  rw [t.glob_σ] at hTied
  refine GlobalTheory.T.kernelEntries_hyp_of_heckeCharacterConditions D L hT Gi Gl K Y cX ex t (fun j => ⟨_, hTied.mu0 j⟩) (fun j v hv => hTied.muVal j v hv) ?_ hTop
  intro μ k
  exact GlobalTheory.KerJ.ColSideHyp.g_not_mem_Qp t hC μ k

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.KernelEntriesHypOfColumnSidePropertiesStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelEntries_hyp_of_columnSideProperties : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex), GlobalTheory.KerJ.ColSide t → t.TopPinned → t.Hyp := by
  first | exact @GlobalTheory.colSide_hyp | exact GlobalTheory.colSide_hyp | (intros; apply GlobalTheory.colSide_hyp <;> assumption)
end
end
