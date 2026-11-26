module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftSchurMultiplierCompatibility
public import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantSimplicialLabelledFanRefinement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowLevelCharacterTranslationEqFlagCharacter

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeCharacterRestriction

variable {D : D7}

section Chars

variable {T : Type} {L : LevCh D T} {μ0 : T}

theorem isHecke_mu (hL : L.Is μ0) (t : T) (j : Fin D.R.m) : IsHeckeChar D (L.mu t ((j : ℕ) + 1)) :=
  ⟨(hL.mu0 j).1.1.mul (hL.xi t).1.1, fun x =>
    (congrArg₂ (· * ·) ((hL.mu0 j).1.2 x) ((hL.xi t).1.2 x)).trans (mul_one _)⟩

theorem resEta_mu (hL : L.Is μ0) (t : T) (j : Fin D.R.m) : ResEta D (L.mu t ((j : ℕ) + 1)) 0 := by
  have hres := GlobalTheory.Mem.EtaTilde.isEta_res D L.eta L.C.eta hL.eta L.C.isEta
  refine ⟨⟨_, hres⟩, fun η _ a => ?_⟩
  show L.mu0 ((j : ℕ) + 1) (idF D a) * L.xi t (idF D a) = _
  rw [pow_zero, GlobalTheory.GridWeil.triv_base (hL.mu0 j) (L.C.isMu0 j).triv a, GlobalTheory.GridWeil.triv_base (hL.xi t) (hL.xi_triv t) a, mul_one]

theorem resEta_eta (hL : L.Is μ0) : ResEta D L.eta 1 := by
  have hres := GlobalTheory.Mem.EtaTilde.isEta_res D L.eta L.C.eta hL.eta L.C.isEta
  refine ⟨⟨_, hres⟩, fun η h a => ?_⟩
  rw [(GlobalTheory.IdeleNormChar.existsUnique_isEta D).unique h hres, pow_one, MonoidHom.comp_apply]

theorem isHecke_quot (hL : L.Is μ0) (t : T) (j : Fin D.R.m) : IsHeckeChar D (L.mu t ((j : ℕ) + 1) * L.eta⁻¹) :=
  ⟨(isHecke_mu hL t j).1.mul (hL.eta.1.1.inv), fun x => by
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, (isHecke_mu hL t j).2, hL.eta.1.2, inv_one, mul_one]⟩

theorem resEta_quot (hL : L.Is μ0) (t : T) (j : Fin D.R.m) {n : ℕ} (hn : Odd n) :
    ResEta D (L.mu t ((j : ℕ) + 1) * L.eta⁻¹) n :=
  resEta_parity (resEta_mul (resEta_mu hL t j) (resEta_inv (resEta_eta hL)))
    (by obtain ⟨c, rfl⟩ := hn; omega)

theorem resEta_even (hL : L.Is μ0) (t : T) (j : Fin D.R.m) {n : ℕ} (hn : Even n) :
    ResEta D (L.mu t ((j : ℕ) + 1)) n :=
  resEta_parity (resEta_mu hL t j) (by obtain ⟨c, rfl⟩ := hn; omega)

theorem odd_r : Odd D.R.r := by
  obtain ⟨a, ha⟩ := D.R.k_even
  obtain ⟨b, hb⟩ := D.R.m_even
  have := D.R.two_le_m
  refine ⟨a + b - 1, ?_⟩
  unfold Ranks.r
  omega

theorem even_rankY (j : ℕ) : Even (D.R.rankY j) ↔ ¬ Even j := by
  have h1 : ¬ Even D.R.r := Nat.not_even_iff_odd.2 odd_r
  have h2 : ¬ Even D.R.t := Nat.not_even_iff_odd.2 D.R.t_odd
  unfold Ranks.rankY
  rw [Nat.even_add, Nat.even_mul]
  tauto

theorem rank_Yc {k : ℕ} (h : k ≤ D.R.m) : (Yc D k).rank = D.R.rankY k := by
  show (D.sp.Y (min k D.R.m)).rank = _
  rw [min_eq_left h]
  exact D.sp.Y_rank k h

theorem step_facts (hL : L.Is μ0) (t : T) (j : Fin D.R.m) {a b : ℕ} (ha : Even a ↔ ¬ Even (j : ℕ)) (hb : Even b ↔ Even (j : ℕ)) :
    IsHeckeChar D (Lift.chrStep (L.mu t) L.eta ((j : ℕ) + 1)).1 ∧ IsHeckeChar D (Lift.chrStep (L.mu t) L.eta ((j : ℕ) + 1)).2 ∧
      ResEta D (Lift.chrStep (L.mu t) L.eta ((j : ℕ) + 1)).1 a ∧ ResEta D (Lift.chrStep (L.mu t) L.eta ((j : ℕ) + 1)).2 b := by
  unfold Lift.chrStep
  by_cases h : Even (j : ℕ)
  · rw [if_pos h.add_one]
    exact ⟨isHecke_quot hL t j, isHecke_mu hL t j,
      resEta_quot hL t j (Nat.not_even_iff_odd.1 fun e => ha.1 e h), resEta_even hL t j (hb.2 h)⟩
  · rw [if_neg (fun e => h (by simpa [Nat.odd_add_one] using e))]
    exact ⟨isHecke_mu hL t j, isHecke_quot hL t j, resEta_even hL t j (ha.2 h),
      resEta_quot hL t j (Nat.not_even_iff_odd.1 fun e => h (hb.1 e))⟩

theorem splitFacts (hL : L.Is μ0) (t : T) :
    (∀ k, k + 1 < D.R.m → IsHeckeChar D (Lift.chrStep (L.mu t) L.eta (k + 1)).1 ∧
      IsHeckeChar D (Lift.chrStep (L.mu t) L.eta (k + 1)).2 ∧
      ResEta D (Lift.chrStep (L.mu t) L.eta (k + 1)).1 (Yc D k).rank ∧
      ResEta D (Lift.chrStep (L.mu t) L.eta (k + 1)).2 (Yc D (k + 1)).rank) ∧
    (IsHeckeChar D (Lift.chrStep (L.mu t) L.eta D.R.m).1 ∧ IsHeckeChar D (Lift.chrStep (L.mu t) L.eta D.R.m).2 ∧
      ResEta D (Lift.chrStep (L.mu t) L.eta D.R.m).1 (Yc D (D.R.m - 1)).rank ∧
      ResEta D (Lift.chrStep (L.mu t) L.eta D.R.m).2 D.sp.X'.rank) ∧
    ∀ i : Fin D.R.m, IsHeckeChar D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).1 ∧
      IsHeckeChar D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).2 ∧
      ResEta D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).1 (Vc D i).rank ∧
      ResEta D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).2 (Wc D i).rank := by
  have hm2 := D.R.two_le_m
  refine ⟨fun k hk => ?_, ?_, fun i => ?_⟩
  · refine step_facts hL t ⟨k, by omega⟩ (a := (Yc D k).rank) (b := (Yc D (k + 1)).rank) ?_ ?_
    · rw [rank_Yc (by omega)]; exact even_rankY k
    · rw [rank_Yc (by omega), even_rankY]
      show _ ↔ Even k
      rw [Nat.even_add_one, not_not]
  · have hj : D.R.m - 1 < D.R.m := by omega
    have e : D.R.m - 1 + 1 = D.R.m := by omega
    have hne : ¬ Even (D.R.m - 1) := fun h => by
      have := h.add_one
      rw [e] at this
      exact (Nat.not_odd_iff_even.2 D.R.m_even) this
    have key := step_facts hL t ⟨D.R.m - 1, hj⟩ (a := (Yc D (D.R.m - 1)).rank) (b := D.sp.X'.rank)
      (by rw [rank_Yc (by omega)]; exact even_rankY _)
      (by
        rw [D.sp.X'_rank]
        show Even (D.R.rankY D.R.m) ↔ Even (D.R.m - 1)
        rw [even_rankY]
        exact iff_of_false (not_not.2 D.R.m_even) hne)
    simpa only [e] using key
  · have hV : (Vc D i).rank = D.R.nV := D.sp.V_rank _ (by omega) (by omega)
    have hW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (by omega) (by omega)
    refine ⟨isHecke_mu hL t i, isHecke_quot hL t i, resEta_even hL t i ?_, resEta_quot hL t i ?_⟩
    · rw [hV]
      exact odd_r.add_odd D.R.t_odd
    · rw [hW]
      exact odd_r

end Chars

section Places

variable {T : Type} {L : LevCh D T} {μ0 : T}

theorem not_isConjPl_union (hL : L.Is μ0) (t : T) {P P' : Pl D.host.E} (h : P ∈ L.Pg ∨ P ∈ L.Q t)
    (h' : P' ∈ L.Pg ∨ P' ∈ L.Q t) : ¬ Lev.IsConjPl P P' := by
  rcases h with h | h
  · exact (GlobalTheory.ChainEquiv.places_sep L μ0 hL t).1 P h P' h'
  · rcases h' with h' | h'
    · intro hc
      obtain ⟨⟨q, hq, hcard, -, hne⟩, -⟩ := hL.Q_pl t P h
      obtain ⟨k, hk⟩ := (hL.Pg P').1 h'
      have h1 : (q : 𝓞 D.host.E) ∈ P.asIdeal := by
        have hzero : Nat.card (kP P) • (1 : kP P) = 0 := card_nsmul_eq_zero'
        rw [hcard, nsmul_one] at hzero
        exact Ideal.Quotient.eq_zero_iff_mem.1 ((map_natCast _ q).trans hzero)
      exact hne k (GlobalTheory.ChainEquiv.eq_of_natCast_mem P' hq (D.host.g_prime k)
        (GlobalTheory.ChainEquiv.natCast_mem_of_isConjPl hc h1) (L.C.P.overP hk))
    · exact (hL.Q_pl t P h).2 P' h'

end Places

theorem liftsAt_and_seedFacts : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type)
    [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (F : Face D A), LiftsAt D A Ks F ∧ SeedFacts D A Ks F := by
  intro D G _ _ Pl0 T A Ks _ _ _ F
  refine ⟨fun R h => ⟨GlobalTheory.LevelRowsObj.liftsExist h.lev, fun i => GlobalTheory.GeoActRoad.levelLiftsExist_gridVertexSpaces h.lev i⟩, fun R h => ⟨?_, ?_⟩⟩
  · exact fun t => splitFacts h.lev t
  · classical
    intro t
    refine ⟨(GlobalTheory.ChainEquiv.places_sep R.toLevCh A.μ0 h.lev t).2, GlobalTheory.CentralShift.exists_idemSum _ fun P hP P' hP' => ?_⟩
    exact not_isConjPl_union h.lev t (Finset.mem_union.1 hP) (Finset.mem_union.1 hP')

end GlobalTheory.HeckeCharacterRestriction
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GridFieldHasLattices
open Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.ChiGrid

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LiteralAutomorphy.GridRow

section Transfer

variable {D : Formalism.BasicNotions.D7} {T : Type} {Lc : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts}

theorem fieldHas_of_same {G G₀ : GridData Lc sc} {K : Type} [Field K] {e : K →+* ℂ} (hv : G.pl.v0 = G₀.pl.v0)
    (hch : ∀ a : Fin D.R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) (h : FieldHas G₀ e) : FieldHas G e := by
  have hS : G.pl.S0 = G₀.pl.S0 := by
    delta Places.S0
    rw [hv]
  have hd : ∀ v, G.pl.depth sc v = G₀.pl.depth sc v := fun v => by
    delta Places.depth
    rw [hv]
  refine ⟨fun i h1 h2 => ?_, fun v hv' => ?_⟩
  · obtain ⟨a, rfl⟩ : ∃ a, i = a + 1 := ⟨i - 1, by omega⟩
    have := hch ⟨a, by omega⟩
    simp only at this
    rw [this]
    exact h.values _ h1 h2
  · rw [hd]
    exact h.roots v (hS ▸ hv')

theorem lamOf_of_same {G G₀ : GridData Lc sc} (hw : G.pl.w G.pl.v0 = G₀.pl.w G₀.pl.v0)
    (hch : ∀ a : Fin D.R.m, G.ch.chiH (a.1 + 1) = G₀.ch.chiH (a.1 + 1)) : lamOf G = lamOf G₀ := by
  delta lamOf
  rw [hw]
  congr 1
  funext a
  exact hch a

end Transfer

variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
  {Kc : Formalism.MainNotions.G.Consts} {Y : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC} {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem gridFit_of_parts {p : PtAt ex Csz} {CF : ℝ} {G : Grid p CF} (hs : TwistedPlaceChoiceLiesOverPair D ex.nch)
    (hc : ∀ w, TwistedAt D w → BlochKatoReduction.Gen.QOk D.ntw (ex.nch.twI w) (ex.nch.Q w))
    (hp : ∃ N0 : D.ntw.Tw → ℕ, ∀ w, TwistedAt D w → ∀ a : ℤ, IsCoprime a (D.ntw.l (ex.nch.twI w) : ℤ) →
      BlochKatoReduction.Gen.partC N0 (ex.nch.twI w) (ex.nch.Q w) (ex.nch.k' w) (ex.nch.psi' w ^ a) (twEps D (ex.nch.twI w)))
    (h1 : Formalism.L2.Host.ValLL0 D p.R.C) (h2 : FieldHas G (Formalism.L2.Host.embLL0 D))
    (h3 : Formalism.L2.Host.PsiChoiceCompatible D p.R.C ex.nch p.Tp) (h4 : GlobalTheory.LamTie.IsLamTieFull D.ntw (lamOf G)) : GridFit p G :=
  ⟨h1, h2, hs, hc, hp, h3, h4⟩

end GlobalTheory.Mem.LiteralAutomorphy.GridRow
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionLowersMaxCellMultiplicity
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionLowersMaxCellMultiplicity
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

section Main

variable {O : Type} [CommRing O] {bar : O → O}

theorem maxMult_lt_of_among_zero {q M : ℕ} {φ : InvFun O} (hM : 1 ≤ M) (h : maxMult bar q φ ≤ M)
    (h0 : MultCellsAmong bar q φ M 0) : maxMult bar q φ < M := by
  obtain ⟨R, hR⟩ := h0
  have key : maxMult bar q φ ≤ ((M - 1 : ℕ) : ℕ∞) := by
    unfold maxMult
    refine iSup_le fun X => iSup_le fun i1 => iSup_le fun i2 => iSup_le fun i3 => iSup_le fun i4 => iSup_le fun hX =>
      iSup_le fun m => iSup_le fun δ => iSup_le fun hc => iSup_le fun hli => iSup_le fun hp => ?_
    have hle : ((cellMult bar fun i => (⟨δ i, hc.mem i⟩ : balForms bar X)) : ℕ∞) ≤ M := by
      refine le_trans ?_ h
      unfold maxMult
      exact le_iSup_of_le X <| le_iSup_of_le i1 <| le_iSup_of_le i2 <| le_iSup_of_le i3 <| le_iSup_of_le i4 <|
        le_iSup_of_le hX <| le_iSup_of_le m <| le_iSup_of_le δ <| le_iSup_of_le hc <| le_iSup_of_le hli <|
        le_iSup_of_le hp le_rfl
    have hne : cellMult bar (fun i => (⟨δ i, hc.mem i⟩ : balForms bar X)) ≠ M := fun he =>
      (hR X hX m δ ⟨hc, hli, hp, he⟩).elim fun k _ => k.elim0
    have hle' : cellMult bar (fun i => (⟨δ i, hc.mem i⟩ : balForms bar X)) ≤ M := by exact_mod_cast hle
    exact_mod_cast (show cellMult bar (fun i => (⟨δ i, hc.mem i⟩ : balForms bar X)) ≤ M - 1 by omega)
  exact key.trans_lt (by exact_mod_cast (show M - 1 < M by omega))

end Main

theorem exists_round_lt_maxMult : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ)
    (φ lab : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab → SimpLab H.bar q φ lab → maxMult H.bar q φ < ⊤ →
    2 ≤ maxMult H.bar q φ → ∃ φ' lab' : InvFun (𝓞 E), IsPolyFan H.bar q φ' ∧ IsTwInv H φ' ∧ IsTwInv H lab' ∧
      SimpLab H.bar q φ' lab' ∧ Subordinate H.bar q φ' φ ∧ maxMult H.bar q φ' < maxMult H.bar q φ := by
  intro E _ _ _ H q φ lab hD hP hT hL hS hfin h2
  set M := (maxMult H.bar q φ).toNat with hMdef
  have hMe : maxMult H.bar q φ = M := (ENat.coe_toNat hfin.ne).symm
  have hM2 : 2 ≤ M := by rw [hMe] at h2; exact_mod_cast h2
  obtain ⟨n, hn⟩ := GlobalTheory.PolFan.CellClass.multCellsAmong_of_isPolyFan E H q φ hP M
  have key : ∀ (n : ℕ) (φ lab : InvFun (𝓞 E)), IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab →
      SimpLab H.bar q φ lab → maxMult H.bar q φ ≤ M → MultCellsAmong H.bar q φ M n →
      ∃ φ' lab' : InvFun (𝓞 E), IsPolyFan H.bar q φ' ∧ IsTwInv H φ' ∧ IsTwInv H lab' ∧ SimpLab H.bar q φ' lab' ∧
        Subordinate H.bar q φ' φ ∧ maxMult H.bar q φ' < M := by
    intro n
    induction n with
    | zero =>
      intro φ lab hP hT hL hS hle h0
      exact ⟨φ, lab, hP, hT, hL, hS, Subordinate.refl φ, maxMult_lt_of_among_zero (by omega) hle h0⟩
    | succ n ih =>
      intro φ lab hP hT hL hS hle h0
      obtain ⟨φ₁, lab₁, hP₁, hT₁, hL₁, hS₁, hs₁, hle₁, h₁⟩ := GlobalTheory.T.exists_starSubdivision_removes_maxMultiplicity_cells E H q φ lab hD hP hT hL hS M n hM2 hle h0
      obtain ⟨φ', lab', hP', hT', hL', hS', hs', hlt⟩ := ih φ₁ lab₁ hP₁ hT₁ hL₁ hS₁ hle₁ h₁
      exact ⟨φ', lab', hP', hT', hL', hS', hs'.trans hs₁, hlt⟩
  obtain ⟨φ', lab', hP', hT', hL', hS', hs', hlt⟩ := key n φ lab hP hT hL hS hMe.le hn
  exact ⟨φ', lab', hP', hT', hL', hS', hs', hMe ▸ hlt⟩

end GlobalTheory.PolFan
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionLowersMaxCellMultiplicityStatement
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_starSubdivision_lowers_maxCellMultiplicity : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab → SimpLab H.bar q φ lab → maxMult H.bar q φ < ⊤ → 2 ≤ maxMult H.bar q φ → ∃ φ' lab' : InvFun (𝓞 E), IsPolyFan H.bar q φ' ∧ IsTwInv H φ' ∧ IsTwInv H lab' ∧ SimpLab H.bar q φ' lab' ∧ Subordinate H.bar q φ' φ ∧ maxMult H.bar q φ' < maxMult H.bar q φ := by
  first | exact @GlobalTheory.PolFan.exists_round_lt_maxMult | exact GlobalTheory.PolFan.exists_round_lt_maxMult | (intros; apply GlobalTheory.PolFan.exists_round_lt_maxMult <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorLevelMultiplicitySpaceMemGoodRows
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR
  Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum
open scoped InnerProductSpace TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KeepLevel

open GlobalTheory.Mem GlobalTheory.Mem.Th GlobalTheory.ChainEquiv

section General

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {θ : InfFam D} {M : DSModel V S} {β : GL (Fin V.rank) (Lev.EAf D)}
  {L : LevDat D.host.E ℂ V.rank}

theorem levChi_withP (P : LevelP L.Pg L.r ℂ) (p : P.H) {κ : GA D V} (hκ : IsLevelLift V β L p κ) :
    levChi V β (withP L P) κ = ((P.chi p : ℂˣ) : ℂ) * levChi V β (flagL L) κ := by
  unfold levChi
  rw [levFn_withP, hκ.2.2, extendOne_of_mem _ p.2, Units.val_mul]

theorem eigen_of_hasType {P : LevelP L.Pg L.r ℂ} {f : GA D V → ℂ} (hf : HasType V β (withP L P) f) (p : P.H) {κ : GA D V}
    (hκ : IsLevelLift V β L p κ) (h : GA D V) : ((P.chi p : ℂˣ) : ℂ) * f h = (levChi V β (flagL L) κ)⁻¹ * f (h * κ) := by
  have hp : rTup β L (finE V κ) ∈ P.H := hκ.2.2.symm ▸ p.2
  have ha := levChi_ne_zero (β := β) (flagL L) κ
  rw [hf κ ⟨hκ.1, hκ.2.1, hp⟩ h, levChi_withP P p hκ]
  field_simp

theorem hasType_of_eigen {P : LevelP L.Pg L.r ℂ} {f : GA D V → ℂ}
    (hf : ∀ (p : P.H) κ, IsLevelLift V β L p κ → ∀ h, ((P.chi p : ℂˣ) : ℂ) * f h = (levChi V β (flagL L) κ)⁻¹ * f (h * κ)) :
    HasType V β (withP L P) f := by
  intro κ hκ h
  have hp : rTup β L (finE V κ) ∈ P.H := hκ.2.2
  have hl : IsLevelLift V β L (⟨_, hp⟩ : P.H) κ := ⟨hκ.1, hκ.2.1, rfl⟩
  have ha := levChi_ne_zero (β := β) (flagL L) κ
  rw [levChi_withP P _ hl, mul_right_comm, hf _ κ hl h]
  field_simp

theorem mem_mult_of_level {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} {X : MMap M} (hX : X ∈ Mult θ M J χ)
    (h : ∀ v, ∀ k ∈ J', ∀ g, X v (g * k) = χ' k * X v g) : X ∈ Mult θ M J' χ' :=
  have a := (GlobalTheory.MultMem.mem_mult_iff D θ V S M J χ X).1 hX
  Submodule.subset_span ⟨a.aut, a.cusp, h, a.equiv, a.cont⟩

theorem hasType_of_comm (hL : LiftsExist V β L) {P : LevelP L.Pg L.r ℂ} (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) {f : GA D V → ℂ}
    (h1 : HasType V β (flag1L L) f) (h2 : HasType V β (flag1L L) (e f)) (hf : HasType V β (withP L P) f)
    (hc : ∀ g, e (actL V β L g f) = actL V β L g (e f)) : HasType V β (withP L P) (e f) := by
  refine IsPLevel.hasType ⟨h2, fun p => ?_⟩
  obtain ⟨κ, hκ⟩ := hL p
  have a : actL V β L p f = ((P.chi p : ℂˣ) : ℂ) • f := funext fun h =>
    (level_action_spec h1 ⟨κ, hκ⟩ κ hκ h).trans (eigen_of_hasType hf p hκ h).symm
  exact (hc p).symm.trans ((congrArg e a).trans (e.map_smul _ f))

end General

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem mem_lvlPart_iff (P : LevelP R.Pg D.R.r ℂ) (t : T) (j : ℕ) (U : R.CC t j) :
    U ∈ lvlPart R P t j ↔ ∀ p : P.H, Rel R t p j U (((P.chi p : ℂˣ) : ℂ) • U) := by
  constructor
  · intro hU p κ hκ v h
    have a : (U : SmT (R.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) ∈ MultT R.θ (R.MY j) (levS _ (R.βY j) (R.datYt t j P))
      (levChi _ (R.βY j) (R.datYt t j P)) := (mem_multT R.θ (R.MY j) _ _ _).2 hU
    exact eigen_of_hasType (L := R.datYt t j R.triv) (P := P) (multT_value _ _ _ _ _ a v).2 p hκ h
  · intro hU
    refine mem_mult_of_level ((mem_multT R.θ (R.MY j) _ _ _).1 U.2) fun v => ?_
    exact hasType_of_eigen (L := R.datYt t j R.triv) (P := P) fun p κ hκ h => hU p κ hκ (PiTensorProduct.tprod ℂ v) h

theorem goodProjector_levelMultiplicitySpace_mem_goodRows (hl : R.toLevCh.Is A.μ0) (hi : R.models_inf) (hr : R.grp_record) (P : LevelP R.Pg D.R.r ℂ) (t : T)
    {X : MMap (R.MY 0)} (hX : X ∈ multAt R P t 0) : postOn (R.MY 0) R.e0 X ∈ R.EEat P := by
  have h0 := multAt_le R P t 0 hX
  rw [multAt_zero] at h0 hX
  have hL := GlobalTheory.ProjectedLift.liftsExist_rows R hl
  have h1 : postOn (R.MY 0) R.e0 X ∈ R.EEat R.triv :=
    GlobalTheory.ProjectedLift.postOn_gaL_mem_goodPart (L := R.dat0 R.triv) hi hL R.eG _ (GlobalTheory.ProjectedLift.eC_conv R hr) h0
  refine ⟨mem_mult_of_level h1.1 fun v => ?_, h1.2⟩
  have a0 : HasType _ (R.βY 0) (R.dat0 R.triv) (X v) := ((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ X).1 h0).lev v
  refine hasType_of_comm (L := R.dat0 R.triv) (P := P) hL R.e0 a0
    (((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ _).1 h1.1).lev v) (((GlobalTheory.MultMem.mem_mult_iff D _ _ _ _ _ _ X).1 hX).lev v) fun g => ?_
  obtain ⟨g, rfl⟩ := R.eG.surjective g
  exact (GlobalTheory.ProjComm.proj_comm R hl hr).1 g _ a0

end GlobalTheory.KeepLevel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormsFiniteGroupActionEqFlagLevelRightTransla
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFlagRTup
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.FlagOnto

theorem exists_flag_rTup : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), I.Ok → ValsIn I → LevOf X I U L →
    ∀ (t : TupU I U) (y : G0 L.Pg X.toD7.R.r), ∃ q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q,
      rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _)) = y := by
  intro X px I hX U L hI hV hL t y
  obtain ⟨c, hc⟩ := hL.is.βX
  have hsep := GlobalTheory.ChainEquiv.places_sep L (mu0F (tuOf I U)) hL.is t
  obtain ⟨κ, -, hκP, hκr⟩ := GlobalTheory.ParahoricLift.liftsExist X.toD7.sp.X' L.βX (L.datXt t) L.ΛX _ hc hsep.1 hsep.2 y
  exact ⟨⟨(finHom X.toD7.sp.X').rangeRestrict κ, hκP, Subgroup.mem_top _⟩, hκr⟩

end GlobalTheory.Mem.R3.FlagOnto

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedRowLatticesFlagLevelRightTranslation
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedRowLatticesFlagLevelRightTranslation
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowDeco

theorem deco_tie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r),
    I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    ∀ (t : TupU I U) (q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q),
    ∃ u : ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp,
      (∀ h : Bridge.Gf X.toD7.sp.X', RowAd.decoAd X I t (h * (q : Bridge.Gf X.toD7.sp.X')) =
        ((1 : Formalism.L2.Col.UF X.B.fields.E (X.B.R.N X.B.R.m - 1)),
          (u : Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.N X.B.R.m - 1) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)) *
            (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R)
              (eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _)))))⁻¹) •
          RowAd.decoAd X I t h) ∧
      X.toD7.what₂.embLL (((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv.chr u : X.B.fields.Kˣ) : X.B.fields.K) =
        (((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch q : ℂˣ) : ℂ) := by
  intro X px I hX U L eG hI hV hL hG t q
  have hz := unitaryFiniteAdelicPointAsMatrix_mem_flagIwahori X I hI L hL t q
  have hu := GlobalTheory.T.inv_reduction_mul_flagTranslation_mem_rowLevelGroup X px I U L eG hI hL hG t q hz
  refine ⟨⟨_, hu⟩, fun h => ?_, GlobalTheory.T.rowLevelCharacter_translation_eq_flagCharacter X px I U L eG hI hV hL hG t q hz hu⟩
  refine (decoAd_mul X I hI t h _ hz).trans ?_
  refine congrArg (fun a : Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.N X.B.R.m - 1) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1) =>
    ((1 : Formalism.L2.Col.UF X.B.fields.E (X.B.R.N X.B.R.m - 1)), a) • RowAd.decoAd X I t h) ?_
  exact (mul_inv_cancel_right _ _).symm

end GlobalTheory.Mem.R3.RowDeco
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DecoratedRowLatticesFlagLevelRightTranslationStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.decoratedRowLattices_flagLevel_rightTranslation : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r),
    I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG →
    ∀ (t : TupU I U) (q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q),
    ∃ u : ((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv).grp,
      (∀ h : Bridge.Gf X.toD7.sp.X', RowAd.decoAd X I t (h * (q : Bridge.Gf X.toD7.sp.X')) =
        ((1 : Formalism.L2.Col.UF X.B.fields.E (X.B.R.N X.B.R.m - 1)),
          (u : Formalism.L2.Col.GLG (E := X.B.fields.E) (n := X.B.R.N X.B.R.m - 1) (SG := Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1)) *
            (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R)
              (eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _)))))⁻¹) •
          RowAd.decoAd X I t h) ∧
      X.toD7.what₂.embLL (((Formalism.L2.Col.rowTyKK I.Ch I.sel t.1).inv.chr u : X.B.fields.Kˣ) : X.B.fields.K) =
        (((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch q : ℂˣ) : ℂ) := by
  exact @GlobalTheory.Mem.R3.RowDeco.deco_tie
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormsFiniteGroupActionEqFlagLevelRightTransla
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.RowAct

section Forms

variable {Xf : Formalism.L2.Col.Fields} {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 Xf.E))}
  (C : Formalism.L2.Col.CoefPk Xf n (Formalism.L2.Col.DecoSet (E := Xf.E) (n := n) (ST := ST) (SG := SG))) (Λ : Formalism.L2.Col.LevFam Xf.E Xf.K n SG)

theorem eqFun_smul_grp (φ : (Formalism.L2.Col.formGSD C Λ).EqFun) (u : Λ.grp) (a : Formalism.L2.Col.GLG (E := Xf.E) (n := n) (SG := SG))
    (d : Formalism.L2.Col.DecoSet (E := Xf.E) (n := n) (ST := ST) (SG := SG)) :
    (φ : Formalism.L2.Col.DecoSet (E := Xf.E) (n := n) (ST := ST) (SG := SG) → C.V) (((1 : Formalism.L2.Col.UF Xf.E n), (u : Formalism.L2.Col.GLG (E := Xf.E) (n := n) (SG := SG)) * a) • d) =
      ((Λ.chr u : Xf.Kˣ) : Xf.K) • (φ : Formalism.L2.Col.DecoSet (E := Xf.E) (n := n) (ST := ST) (SG := SG) → C.V) (((1 : Formalism.L2.Col.UF Xf.E n), a) • d) := by
  have e := φ.2 ((1, u) : Formalism.L2.Col.FormG Λ) (((1 : Formalism.L2.Col.UF Xf.E n), a) • d)
  have e' : ((1, u) : Formalism.L2.Col.FormG Λ) • (((1 : Formalism.L2.Col.UF Xf.E n), a) • d) =
      ((1 : Formalism.L2.Col.UF Xf.E n), (u : Formalism.L2.Col.GLG (E := Xf.E) (n := n) (SG := SG)) * a) • d := by
    show ((1 : Formalism.L2.Col.UF Xf.E n), (u : Formalism.L2.Col.GLG (E := Xf.E) (n := n) (SG := SG))) • (((1 : Formalism.L2.Col.UF Xf.E n), a) • d) = _
    rw [smul_smul, Prod.mk_mul_mk, one_mul]
  rw [e'] at e
  rw [e]
  show ((Λ.chr u : Xf.Kˣ) : Xf.K) • C.rho 1 _ = _
  rw [map_one]
  rfl

end Forms

theorem semilin_inv_smul {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W]
    {σ : K →+* ℂ} (m : V →ₛₗ[σ] W) (k : K) (c : ℂˣ) (hk : σ k = c) (x : V) :
    m x = ((c⁻¹ : ℂˣ) : ℂ) • m (k • x) := by
  rw [LinearMap.map_smulₛₗ, hk, smul_smul, Units.inv_mul, one_smul]

end GlobalTheory.Mem.R3.RowAct

namespace GlobalTheory.Mem.R3.RowAct

theorem act_tie : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    ∀ t, ∀ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t P →
      ∃ a : Bridge.ActTie (Bridge.ratF X.toD7.sp.X') P (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q (levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch ((famR X I hX U Xg tr).A.leftGroupActionRight t),
        ∀ q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q,
          eG (a.red q) = rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _)) := by
  intro X px I hX U Xg tr L eG hI hV hL hG cX gramR c0R hcX hgram hTie hinner t P hRD
  refine ⟨{
      red := eG.symm.toMonoidHom.comp (rTupQ X.toD7.sp.X' L.βX (L.datXt t))
      red_surj := ?_
      red_ker := ?_
      act_eq := ?_ }, ?_⟩
  · intro g
    have key := GlobalTheory.Mem.R3.FlagOnto.exists_flag_rTup X px I hX U L hI hV hL t (eG g)
    obtain ⟨q, hq⟩ := key
    refine ⟨q, ?_⟩
    have e : rTupQ X.toD7.sp.X' L.βX (L.datXt t) q = eG g := hq
    show eG.symm (rTupQ X.toD7.sp.X' L.βX (L.datXt t) q) = g
    rw [e, MulEquiv.symm_apply_apply]
  · intro q
    have e := rTupQ_eq_one_iff X.toD7.sp.X' L.βX (L.datXt t) q
    show eG.symm (rTupQ X.toD7.sp.X' L.βX (L.datXt t) q) = 1 ↔ _
    exact (MulEquiv.map_eq_one_iff eG.symm).trans e
  · intro g κ hκ f
    obtain ⟨m, hm⟩ := hRD
    obtain ⟨u, hdeco, hch⟩ := GlobalTheory.T.decoratedRowLattices_flagLevel_rightTranslation X px I hX U L eG hI hV hL hG t κ
    have hg : eG.symm (rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf X.toD7.sp.X') : GL _ _))) = g := hκ
    rw [hg] at hdeco
    funext h
    have e1 := hm ((famR X I hX U Xg tr).A.leftGroupActionRight t g f) h
    have e2 := hm f (h * (κ : Bridge.Gf X.toD7.sp.X'))
    refine e1.trans ?_
    refine Eq.trans ?_ (congrArg (fun v => (((((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch κ)⁻¹ : ℂˣ) : ℂ)) • v) e2).symm
    have e3 : ((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm
        ((famR X I hX U Xg tr).A.leftGroupActionRight t g f) = Formalism.L2.Col.g0HatRepEqFunX X.B.wts I.Ch I.sel t.1 g
          (((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f) :=
      LinearEquiv.symm_apply_apply _ _
    have e4 := eqFun_smul_grp _ _ (((Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f)
      u (Formalism.L2.Col.unipotentGroupBlockEmbedding (X.B.primes px) I.sel t.1 (Formalism.L2.Col.r_le_X' X.B.R) g)⁻¹ (RowAd.decoAd X I t h)
    refine (congrArg (fun ψ : (Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).EqFun =>
      m ((ψ : (Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).D → (Formalism.L2.Col.mtildeKGSD X.B.wts I.Ch I.sel t.1).V)
        (RowAd.decoAd X I t h))) e3).trans ?_
    refine (semilin_inv_smul m _ _ hch _).trans ?_
    refine congrArg (fun v => (((((levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch κ)⁻¹ : ℂˣ) : ℂ)) • m v) ?_
    exact e4.symm.trans (congrArg _ (hdeco h).symm)
  · intro q
    have e : eG (eG.symm (rTupQ X.toD7.sp.X' L.βX (L.datXt t) q)) = rTupQ X.toD7.sp.X' L.βX (L.datXt t) q :=
      MulEquiv.apply_symm_apply _ _
    exact e

end GlobalTheory.Mem.R3.RowAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFormsFiniteGroupActionEqFlagLevelRightTranslaStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowFormsFiniteGroupAction_eq_flagLevelRightTranslation : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → ∀ (cX : CoefA X.toD7.sp.X') (gramR : Matrix (Fin X.toD7.sp.X'.rank) (Fin X.toD7.sp.X'.rank) X.toD7.host.E)
    (c0R : VV X.toD7.what₂.LL (fun τ => Bridge.lamRdef (Ptw X.toD7) τ) →ₛₗ[X.toD7.what₂.embLL] cX.W),
    cX.Is → (gramR = X.toD7.sp.X'.gram ∨ gramR = -X.toD7.sp.X'.gram) →
    Bridge.CoefMapTie X.toD7.sp.X' cX.coef c0R (rhoV (labLL X.toD7) _) →
    (∀ x y, inner ℂ (c0R x) (c0R y) = X.toD7.what₂.embLL (pairV (labLL X.toD7) _ gramR x y)) →
    ∀ t, ∀ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, GlobalTheory.Mem.R3.RowAd.ReadsDeco X I hX Xg tr cX t P →
      ∃ a : Bridge.ActTie (Bridge.ratF X.toD7.sp.X') P (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q (levEnv X.toD7.sp.X' L.βX (L.datXt t)).ch ((famR X I hX U Xg tr).A.leftGroupActionRight t),
        ∀ q : (levEnv X.toD7.sp.X' L.βX (L.datXt t)).Q,
          eG (a.red q) = rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE X.toD7) ((q : Bridge.Gf X.toD7.sp.X') : GL _ _)) := by
  first | exact @GlobalTheory.Mem.R3.RowAct.act_tie | exact GlobalTheory.Mem.R3.RowAct.act_tie | (intros; apply GlobalTheory.Mem.R3.RowAct.act_tie <;> assumption)
end
end
