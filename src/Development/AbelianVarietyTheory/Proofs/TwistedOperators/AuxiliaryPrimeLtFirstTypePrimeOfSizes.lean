module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTestGridFromLevelChoiceGrid
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTestGridArrowsVacuaIntertwiners
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsAtAndSeedFacts
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeCoprimeSmallConductor

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemPrincGLOfCong
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Topology

noncomputable section

namespace GlobalTheory.GridJoin

variable {D : D7}
theorem conj_back {G : Type*} [Group G] (b g : G) : b⁻¹ * (b * g * b⁻¹) * b = g := by group

theorem mem_princGL_of_cong {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {I : Ideal (𝓞 E)} (h2 : x ∈ St β)
    {z : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hz : ∀ i j, z i j ∈ Formalism.L2.Herm.intAf F E)
    (e : (β⁻¹ * x * β).1 - 1 = Ideal.absNorm I • z) : x ∈ GlobalTheory.Grid.princGL β I := by
  obtain ⟨y, rfl⟩ := h2
  refine GlobalTheory.Grid.mem_princGL.2 ⟨y, rfl, fun i j => ?_⟩
  have e2 : β⁻¹ * frGL β y * β = intGL F E n y := conj_back β _
  rw [e2] at e
  have e3 := congrFun (congrFun e i) j
  have hmem : ((Ideal.absNorm I : ℕ) : Formalism.L2.Herm.intAf F E) ∈ idS F I := by
    rw [← map_natCast (oToS F E)]
    exact Ideal.mem_map_of_mem _ (Ideal.absNorm_mem I)
  have e4 : ((y : Matrix (Fin n) (Fin n) (Formalism.L2.Herm.intAf F E)) - 1) i j = ((Ideal.absNorm I : ℕ) : Formalism.L2.Herm.intAf F E) * ⟨z i j, hz i j⟩ := by
    apply Subtype.ext
    refine Eq.trans ?_ (e3.trans ?_)
    · simp only [Matrix.sub_apply, Matrix.one_apply]
      split_ifs <;> rfl
    · simp [nsmul_eq_mul]
  rw [e4]
  exact Ideal.mul_mem_right _ _ hmem

theorem princ_isOpen (N : GlobalTheory.Grid.Node D) {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) :
    IsOpen (((N.princ I).comap (Lev.finE N.V) : Subgroup (GA D N.V)) : Set (GA D N.V)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig N.V.gram
  obtain ⟨π, hπ, -⟩ := GlobalTheory.Mass.existsUnique_isFinProj D.sp.cm.sig N.V.gram
  have hf : Continuous (finHom N.V) := (continuous_subtype_val.comp hπ.continuous).congr fun κ => hπ κ
  have hN : Ideal.absNorm I ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 hI
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ N.V N.β ∅,
    GlobalTheory.FunObj.eventually_cong_mat N.β hN hf (map_one _)] with κ ⟨h1, h2, _⟩ ⟨z, hz, e⟩
  exact ⟨h1, mem_princGL_of_cong h2 hz e⟩

theorem princ_isCompact (N : GlobalTheory.Grid.Node D) {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) :
    IsCompact ((Lev.levA N.V (N.princ I) : Subgroup (GA D N.V)) : Set (GA D N.V)) := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig N.V.gram
  obtain ⟨C, hC, hCm⟩ := GlobalTheory.ParahoricCompact.exists_compact N.V N.β
  refine hC.of_isClosed_subset ((GlobalTheory.Ker.CongTop.isClosed_GfC N.V).inter
    (Subgroup.isClosed_of_isOpen _ (princ_isOpen N hI))) fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := Lev.mem_levA.1 hk
  exact hCm k hk1 (GlobalTheory.Grid.princGL_top N.β ▸ GlobalTheory.Grid.princGL_mono N.β le_top hk2.2)

theorem exists_isMeasFD (V : HSp D) (hV : V.SigOK) (K : Subgroup (GL (Fin V.rank) (Lev.EAf D)))
    (ho : IsOpen ((K.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)))
    (hc : IsCompact ((Lev.levA V K : Subgroup (GA D V)) : Set (GA D V))) : ∃ μ 𝓕, Lev.IsMeasFD V K μ 𝓕 := by
  choose m hm using GlobalTheory.MinfMeasure.exists_isMinf
  obtain ⟨μ, hμ⟩ := GlobalTheory.LevelMeasure.exists_isMeasLevW D V hV K ho hc (fun _ m => Lev.IsMinf m) (fun _ => m _ _)
    (fun _ => (hm _ _).1) (fun _ => hm _ _) fun _ _ h => GlobalTheory.LevelMeasure.isMinf_unique (hm _ _) h
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D V μ hμ.1
  exact ⟨μ, 𝓕, hμ, h𝓕⟩

theorem exists_measDat (N : GlobalTheory.Grid.Node D) (hs : N.V.SigOK) (df : Prop) (hdf : df → ∀ τ, (N.V.sig τ).2 = 0)
    {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) : ∃ m : N.MeasDat, m.Is df (N.princ I) := by
  have ho := princ_isOpen N hI
  have hc := princ_isCompact N hI
  by_cases h : df
  · obtain ⟨μ, 𝓕, e⟩ := GlobalTheory.FunObj.exists_meas N.V hs (hdf h) (N.princ I) ⟨ho, hc⟩
    rw [if_pos rfl] at e
    exact ⟨⟨μ, 𝓕⟩, by unfold GlobalTheory.Grid.Node.MeasDat.Is; exact ⟨fun _ => e, fun hn => absurd h hn⟩⟩
  · obtain ⟨μ, 𝓕, e⟩ := exists_isMeasFD N.V hs _ ho hc
    exact ⟨⟨μ, 𝓕⟩, by unfold GlobalTheory.Grid.Node.MeasDat.Is; exact ⟨fun h' => absurd h' h, fun _ => e⟩⟩

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem exists_isMeas (G : GlobalTheory.Grid.GridPre R) (hS : G.IsSpaces) :
    ∃ m00 mV mP mX, (withMeas G m00 mV mP mX).IsMeas := by
  have hlvl : G.lvl R ≠ ⊥ := G.toPlaceDat.ideal_ne_bot R.Pg
  have htop : (⊤ : Ideal (𝓞 D.host.E)) ≠ ⊥ := top_ne_bot
  obtain ⟨m00, h00⟩ := exists_measDat (G.V 0 0) (D.sp.Y_sig 0) False (fun h => h.elim) hlvl
  have hV : ∀ i j, ∃ m : (G.nV i j).MeasDat, i + 1 ≤ D.R.m → j ≤ D.R.m →
      m.Is (if j = 0 then False else D.R.m - 1 ≤ j) ((G.nV i j).princ (if j = 0 then G.lvl R else ⊤)) := by
    intro i j
    by_cases h : i + 1 ≤ D.R.m ∧ j ≤ D.R.m
    · have hN := hS.vert i j h.1 h.2
      obtain ⟨m, hm⟩ := exists_measDat (G.nV i j) hN.sigOK (if j = 0 then False else D.R.m - 1 ≤ j)
        (fun hd τ => by
          rw [hN.sig τ]
          show (D.R.m - j) / 2 = 0
          by_cases hj : j = 0
          · rw [if_pos hj] at hd; exact hd.elim
          · rw [if_neg hj] at hd; omega)
        (I := if j = 0 then G.lvl R else ⊤) (by split_ifs; exacts [hlvl, htop])
      exact ⟨m, fun _ _ => hm⟩
    · exact ⟨⟨0, ∅⟩, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  have hP : ∀ i, ∃ m : (G.P i).MeasDat, i ≤ D.R.m → m.Is (i = D.R.m) ((G.P i).princ (G.lvl R)) := by
    intro i
    by_cases h : i ≤ D.R.m
    · have hN := hS.P i h
      obtain ⟨m, hm⟩ := exists_measDat (G.P i) hN.sigOK (i = D.R.m)
        (fun hd τ => by
          rw [hN.sig τ]
          show (D.R.m - i + 1) / 2 = 0
          omega) hlvl
      exact ⟨m, fun _ => hm⟩
    · exact ⟨⟨0, ∅⟩, fun h1 => absurd h1 h⟩
  have hX : ∀ j, ∃ m : (G.nX j).MeasDat, j + 1 ≤ D.R.m → m.Is True ((G.nX j).princ ⊤) := by
    intro j
    by_cases h : j + 1 ≤ D.R.m
    · have hN := hS.X j h
      obtain ⟨m, hm⟩ := exists_measDat (G.nX j) hN.sigOK True
        (fun _ τ => by
          rw [hN.sig τ]) htop
      exact ⟨m, fun _ => hm⟩
    · exact ⟨⟨0, ∅⟩, fun h1 => absurd h1 h⟩
  choose mV hmV using hV
  choose mP hmP using hP
  choose mX hmX using hX
  refine ⟨m00, mV, mP, mX, ⟨fun i hi => ?_, fun i j hi hj => ?_, fun i hi => hmP i hi, fun j hj => hmX j hj⟩⟩
  · cases i with
    | zero => exact h00
    | succ i =>
      have := hmV i 0 hi (Nat.zero_le _)
      rw [if_pos rfl, if_pos rfl] at this
      exact this
  · have := hmV i (j + 1) hi hj
    rw [if_neg (Nat.succ_ne_zero j), if_neg (Nat.succ_ne_zero j)] at this
    exact this

end GlobalTheory.GridJoin
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GridJoin

open GlobalTheory.Grid GlobalTheory.ChiGrid

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}

theorem isSpaces_withArr {G : GridPre R} {X ωT vacT ItT ωC vacC ItC dn ItU vC} (h : G.IsSpaces) :
    (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC).IsSpaces := by
  obtain ⟨a, b, c, d, e, f, g⟩ := h
  exact ⟨a, b, c, d, e, f, g⟩

theorem isSpaces_withMeas {G : GridPre R} {m00 mV mP mX} (h : G.IsSpaces) : (withMeas G m00 mV mP mX).IsSpaces := by
  obtain ⟨a, b, c, d, e, f, g⟩ := h
  exact ⟨a, b, c, d, e, f, g⟩

theorem spAgree_withArr {G : GridPre R} {X ωT vacT ItT ωC vacC ItC dn ItU vC} {G' : GridData R.toLevCh sc} {W : G'.Weil}
    (h : SpAgree G W) : SpAgree (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC) W := by
  obtain ⟨a, b, c, d, e, f, g, i, j, k⟩ := h
  exact ⟨a, b, c, d, e, f, g, i, j, k⟩

theorem spAgree_withMeas {G : GridPre R} {m00 mV mP mX} {G' : GridData R.toLevCh sc} {W : G'.Weil} (h : SpAgree G W) :
    SpAgree (withMeas G m00 mV mP mX) W := by
  obtain ⟨a, b, c, d, e, f, g, i, j, k⟩ := h
  exact ⟨a, b, c, d, e, f, g, i, j, k⟩

theorem isChars_withArr {G : GridPre R} {X ωT vacT ItT ωC vacC ItC dn ItU vC} (h : G.IsChars) :
    (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC).IsChars := by
  obtain ⟨a, b, c⟩ := h
  exact ⟨a, b, c⟩

theorem isChars_withMeas {G : GridPre R} {m00 mV mP mX} (h : G.IsChars) : (withMeas G m00 mV mP mX).IsChars := by
  obtain ⟨a, b, c⟩ := h
  exact ⟨a, b, c⟩

theorem isArrows_withMeas {G : GridPre R} {m00 mV mP mX} (h : G.IsArrows) : (withMeas G m00 mV mP mX).IsArrows := by
  obtain ⟨a, b, c, d, e⟩ := h
  exact ⟨a, b, c, d, e⟩

theorem isData_withMeas {G : GridPre R} {m00 mV mP mX} (h : G.IsData) : (withMeas G m00 mV mP mX).IsData :=
  fun i hi c => h i hi c

theorem arrAgree_withMeas {G : GridPre R} {m00 mV mP mX} {G' : GridData R.toLevCh sc} {W : G'.Weil} (h : ArrAgree G W) :
    ArrAgree (withMeas G m00 mV mP mX) W := by
  obtain ⟨a, b, c, d, e, f⟩ := h
  exact ⟨a, b, c, d, e, f⟩

theorem pg_under_inj {F : Face D A} (hR : GlobalTheory.Hk3.Core R F) :
    ∀ PP ∈ R.Pg, ∀ PP' ∈ R.Pg, (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP) = (_root_.IsDedekindDomain.HeightOneSpectrum.under (𝓞 D.host.F) PP') → PP = PP' := by
  intro P hP P' hP' e
  rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (D := D) e with h | h
  · exact h
  · exact absurd (GlobalTheory.GoodPrimes.isConjPl_iff.2 h) (GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hR.lev A.μ0 (Or.inl hP') (Or.inl hP))

theorem auxiliaryPrime_splitsCompletely {L : LevCh D T} (P : Places L) : Formalism.L2.Host.SplitsCompletely {P.w P.v0} := by
  intro v hv p hp hpv
  obtain rfl := Finset.mem_singleton.1 hv
  obtain ⟨h1, h2, -⟩ := leastSplitAuxiliaryPrimeThetaChain_spec D
  have hm : q0 D ≡ 1 [MOD D.host.QS * D.host.q * D.host.d] := by
    have : q0 D ≡ 1 [MOD Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D] := by
      rw [← h2]; exact (Nat.mod_modEq _ _).symm
    exact Nat.ModEq.of_mul_left _ this
  have hq : ((q0 D : ℕ) : 𝓞 D.host.E) ∈ (P.w P.v0).asIdeal := by
    have h := P.basePlace_over_qZero
    rw [← P.under_w (P.mem_S0_of_sum_eq.2 (Or.inl rfl))] at h
    rw [← map_natCast (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))]
    exact h
  obtain rfl : p = q0 D := GlobalTheory.GridPlaces.prime_eq_of_mem _ hp h1 hpv hq
  exact (GlobalTheory.SplitChoice.splitsCompletely_of_modEq_one D h1 hm).2

theorem auxiliaryPrime_ne_typePrime {L : LevCh D T} (G' : GridData L sc) (k : Fin 2) : q0 D ≠ D.host.g k := by
  intro e
  apply G'.ch.basePlace_not_mem_chiGridBadPlaces
  have h := G'.pl.basePlace_over_qZero
  rw [e] at h
  rw [S1_mem_OmF]
  fin_cases k
  exacts [Or.inl h, Or.inr (Or.inl h)]

theorem auxiliaryPrime_ne_levelPrimes_of_lt (h : q0 D < D.host.g 0) : q0 D ≠ D.sp.T ∧ ∀ u : D.what₂.Word, q0 D ≠ (D.mem u).A.T :=
  have key : ∀ u : D.what₂.Word, q0 D ≠ (D.mem u).A.T := fun u => (h.trans (GlobalTheory.EX.DC.firstTypePrime_lt_rowPrime D u)).ne
  ⟨D.sp_T ▸ key D.u₀, key⟩

theorem auxiliaryPrime_lt_firstTypePrime_of_sizeRows {large₂ : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) : q0 D < D.host.g 0 := by
  have h1 : Real.log (q0 D) ≤ large₂.sc.L := hs.2.2.2.2.2.2.2.2.1
  have h2 := (hs.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 0 0).1
  have hq : (0 : ℝ) < q0 D := by exact_mod_cast (leastSplitAuxiliaryPrimeThetaChain_spec D).1.pos
  have h3 : (q0 D : ℝ) ≤ large₂.sc.b := (Real.log_le_iff_le_exp hq).1 h1
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)
  have hk : (2 : ℝ) ≤ D.R.k := by have := D.R.m_add_three_le_k; exact_mod_cast (by omega : 2 ≤ D.R.k)
  have h4 : (D.R.k : ℝ) * large₂.sc.b ≤ ((D.R.k : ℝ) * large₂.sc.b) ^ 8 := le_self_pow₀ (by nlinarith) (by norm_num)
  have : (q0 D : ℝ) < D.host.g 0 := by nlinarith
  exact_mod_cast this

theorem exists_gridPre_agree (hDS : GlobalTheory.Published.DiscreteSeriesUpqExists) (hDC : GlobalTheory.Published.DiscreteSeriesCover)
    (hHC : GlobalTheory.Published.HarishChandraModules) (hH : HostHyp D) (hS : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D) (hq : q0 D < D.host.g 0)
    {F : Face D A} (hR : GlobalTheory.Hk3.Core R F)
    (hsc : sc.cGap = 1) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) (hW : W.Over R)
    (hL : ∀ X : GlobalTheory.ChiGrid.Node, X.InRange D.R.m → (∀ j, X ≠ .grid 0 j) → (G'.Λ X : Set _) = L0c D (G'.V X))
    (oV : ∀ i j, 1 ≤ i → i ≤ D.R.m → j ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.grid i j)).rank → ℝ)
      (ε : Fin (G'.V (.grid i j)).rank → Bool), IsEnum (GlobalTheory.Grid.parV D i j τ) lam ε ∧
        (W.onb (.grid i j) τ)ᴴ * gramAt D (G'.V (.grid i j)) τ * W.onb (.grid i j) τ = Formalism.REAL.Jm ε)
    (oP : ∀ i, i ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.core i)).rank → ℝ) (ε : Fin (G'.V (.core i)).rank → Bool),
      IsEnum (GlobalTheory.Grid.parP D i τ) lam ε ∧
        (W.onb (.core i) τ)ᴴ * gramAt D (G'.V (.core i)) τ * W.onb (.core i) τ = Formalism.REAL.Jm ε)
    (oX : ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, ∃ (lam : Fin (G'.V (.top j)).rank → ℝ) (ε : Fin (G'.V (.top j)).rank → Bool),
      IsEnum (GlobalTheory.Grid.parXp D j τ) lam ε ∧
        (W.onb (.top j) τ)ᴴ * gramAt D (G'.V (.top j)) τ * W.onb (.top j) τ = Formalism.REAL.Jm ε)
    (hc : W.cart (.top 0) = W.cart (.core D.R.m)) (hb : W.onb (.top 0) = W.onb (.core D.R.m)) :
    ∃ G : GlobalTheory.Grid.GridPre R, G.Is ∧ Agree G W := by
  obtain ⟨e, he, hcos⟩ := W.cosVec_is
  obtain ⟨G, rfl, hsp, hch, hag⟩ := GlobalTheory.T.exists_testGrid_from_levelChoiceGrid hDS hH hR hsc W hW hL (pg_under_inj hR) (auxiliaryPrime_splitsCompletely _)
    (auxiliaryPrime_ne_typePrime G') (auxiliaryPrime_ne_levelPrimes_of_lt hq) oV oP oX hc hb e he
  obtain ⟨X, ωT, vacT, ItT, ωC, vacC, ItC, dn, ItU, vC, harr, hdat, hag2⟩ : ∃ X ωT vacT ItT ωC vacC ItC dn ItU vC,
      (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC).IsArrows ∧ (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC).IsData ∧
        ArrAgree (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC) W := by
    first
      | exact GlobalTheory.T.exists_testGrid_arrows_vacua_intertwiners hDC hHC hH hS hR hsc W hW G hsp hch hag hcos
      | exact GlobalTheory.T.exists_testGrid_arrows_vacua_intertwiners hDC hHC hH hR hsc W hW G hsp hch hag hcos
  obtain ⟨m00, mV, mP, mX, hm⟩ := exists_isMeas (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC) (isSpaces_withArr hsp)
  exact ⟨withMeas (withArr G X ωT vacT ItT ωC vacC ItC dn ItU vC) m00 mV mP mX,
    ⟨isSpaces_withMeas (isSpaces_withArr hsp), isChars_withMeas (isChars_withArr hch), isArrows_withMeas harr, hm,
      isData_withMeas hdat⟩, spAgree_withMeas (spAgree_withArr hag), arrAgree_withMeas hag2⟩

theorem exists_gridPre_of_sizes (hDS : GlobalTheory.Published.DiscreteSeriesUpqExists) (hDC : GlobalTheory.Published.DiscreteSeriesCover)
    (hHC : GlobalTheory.Published.HarishChandraModules) (hH : HostHyp D) (hS : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D) (hq : q0 D < D.host.g 0)
    {F : Face D A} (hR : GlobalTheory.Hk3.Core R F)
    (hsc : sc.cGap = 1) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) (hW : W.Over R) :
    ∃ G : GlobalTheory.Grid.GridPre R, G.Is ∧ Match G W := by
  obtain ⟨G₁, W₁, h₁, hL⟩ := exists_sameWeil W
  obtain ⟨W₂, hW₂, -, -, ec, eo, ev, ek, e0, e1, -, oV, oP, oX, hc, hb⟩ := exists_weil_ordered hH hsc W₁ (h₁.over hW)
  have eb : ∀ X : GlobalTheory.ChiGrid.Node, X.InRange D.R.m → X ≠ .top 0 → ∀ τ, ∃ σ : Equiv.Perm (Fin (G₁.V X).rank),
      W₂.onb X τ = (W₁.onb X τ).submatrix id σ := fun X hX h0 τ => by
    by_cases h : ∀ j, X ≠ .grid 0 j
    · exact e1 X hX h h0 τ
    · obtain ⟨j, hj⟩ := not_forall.1 h
      obtain rfl := not_not.1 hj
      exact ⟨1, congrFun (e0 j) τ⟩
  obtain ⟨G, hG, a, b⟩ := exists_gridPre_agree hDS hDC hHC hH hS hq hR hsc W₂ hW₂ hL oV oP oX hc hb
  have ep := h₁.pl
  refine ⟨G, hG, ⟨fun j hj => nodeAgree_grid0_of_weil_over W hW j hj,
    fun i j hi hj => (a.vert i j hi hj).nodeMatch_of h₁ ec (eb (.grid i j) ⟨hi, hj⟩),
    fun i hi => (a.core i hi).nodeMatch_of h₁ ec (eb (.core i) hi),
    fun j hj => (a.top j hj).nodeMatch_of h₁ ec (eb (.top j) hj), a.q0, ep ▸ a.w0, ep ▸ a.e0, ep ▸ a.places,
    a.lvl.trans (congrArg (fun P => Places.modul P sc) ep), fun i x y => h₁.chiH ▸ a.chiH i x y,
    fun i x y => h₁.chi ▸ a.chi i x y⟩, b.of_sameWeil h₁ eo ev ek⟩

theorem exists_gridPre (hDS : GlobalTheory.Published.DiscreteSeriesUpqExists) (hDC : GlobalTheory.Published.DiscreteSeriesCover)
    (hHC : GlobalTheory.Published.HarishChandraModules) (hH : HostHyp D) {large₂ : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂)
    {F : Face D A} (hR : GlobalTheory.Hk3.Core R F)
    (hsc : sc.cGap = 1) {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil) (hW : W.Over R) :
    ∃ G : GlobalTheory.Grid.GridPre R, G.Is ∧ Match G W :=
  exists_gridPre_of_sizes hDS hDC hHC hH (GlobalTheory.RowSizes.sizes_of_sizeRows large₂ hs) (auxiliaryPrime_lt_firstTypePrime_of_sizeRows hs) hR hsc W hW

end GlobalTheory.GridJoin
