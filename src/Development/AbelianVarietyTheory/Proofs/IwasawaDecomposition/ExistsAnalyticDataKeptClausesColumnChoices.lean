module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteGroupGoodSetLevelsCharacters
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicReadingDecoratedLatticeForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ParabolicCharacterEqProdSuperdiagonalSum

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemHeightOneSpectrumIffAdditiveValuationPos
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.R3

open Classical in
noncomputable def pickIxTw {B : Base} {px : PreX B.toPre} (I : Col2.ColIn B px) (χ : Formalism.L2.Host.HChar B.host.E) : I.ι :=
  if h : ∃ a, I.xi a = χ then h.choose else I.mu0

theorem xi_pickIxTw {B : Base} {px : PreX B.toPre} (I : Col2.ColIn B px) {χ : Formalism.L2.Host.HChar B.host.E}
    (h : χ ∈ Set.range I.xi) : I.xi (pickIxTw I χ) = χ := by
  have h' : ∃ a, I.xi a = χ := h
  unfold pickIxTw
  rw [dif_pos h']
  exact h'.choose_spec

theorem plc_eq_of_natCast_mem {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : p.Prime)
    (h : (p : 𝓞 F) ∈ v.asIdeal) : Formalism.EigenvalueLevelCeiling.plc v = p := by
  have hd : Formalism.EigenvalueLevelCeiling.plc v ∣ p := by
    unfold Formalism.EigenvalueLevelCeiling.plc
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact h
  haveI : Nontrivial (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr v.isPrime.ne_top
  rcases (Nat.dvd_prime hp).1 hd with h1 | h1
  · exact absurd h1 (CharP.ringChar_ne_one)
  · exact h1

section UnitConjugation
open Formalism.BasicNotions.DV

theorem additiveValuation_conjugatePlace_eq_star (D : D7) (w : D.what₂.places.Pl) (x : D.what₂.LL) :
    vAdd (D.plEq (D.what₂.places.conj w)) x = vAdd (D.plEq w) (star x) := by
  by_cases hx : x = 0
  · subst hx; simp [vAdd]
  · have h1 := D.conj_val w x
    rw [D.val_eq _ x hx, D.val_eq _ (star x) (star_ne_zero.2 hx)] at h1
    exact_mod_cast h1

theorem mem_heightOneSpectrum_iff_additiveValuation_pos {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (x : 𝓞 K)
    (hx : x ≠ 0) : x ∈ w.asIdeal ↔ 0 < vAdd w (x : K) := by
  have hx' : w.valuation K (x : K) ≠ 0 := (map_ne_zero _).2 (by exact_mod_cast hx)
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
  unfold vAdd
  rw [neg_pos, ← WithZero.log_one, WithZero.log_lt_log hx' one_ne_zero]

theorem plEq_conjPl (D : D7) (w : D.what₂.places.Pl) :
    D.plEq (D.what₂.places.conj w) = Formalism.DivisionValues.conjPl (D.plEq w) := by
  apply HeightOneSpectrum.ext
  ext x
  have key : ∀ y : 𝓞 D.what₂.LL, y ∈ (D.plEq (D.what₂.places.conj w)).asIdeal ↔
      Formalism.DivisionValues.cO D.what₂.LL y ∈ (D.plEq w).asIdeal := by
    intro y
    by_cases hy : y = 0
    · subst hy; simp
    · rw [mem_heightOneSpectrum_iff_additiveValuation_pos _ y hy, mem_heightOneSpectrum_iff_additiveValuation_pos _ _ ((map_ne_zero_iff _ (Formalism.DivisionValues.cO D.what₂.LL).injective).2 hy),
        additiveValuation_conjugatePlace_eq_star, Formalism.DivisionValues.ValuationRepresentative.cO_apply]
  rw [key]
  change _ ↔ x ∈ (D.plEq w).asIdeal.map (Formalism.DivisionValues.cO D.what₂.LL)
  rw [Ideal.mem_map_of_equiv]
  constructor
  · intro h
    exact ⟨_, h, Formalism.DivisionValues.ValuationRepresentative.cO_cO x⟩
  · rintro ⟨y, hy, rfl⟩
    rwa [Formalism.DivisionValues.ValuationRepresentative.cO_cO]

end UnitConjugation

end GlobalTheory.Mem.R3

theorem GlobalTheory.Mem.R3.tupL_of_twisted : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (T : Top.TwDat X.B) (Wt : Set X.B.places.Pl) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I (usedOf I T Wt))), Wt.Finite → (∀ w ∈ Wt, X.B.places.conj w ∈ Wt) → I.Ok → Set.range I.xi = T.set I.C → L.C = Top.Fr.at X I.C → (∀ t, L.xiH t = I.xi (ixOf I (usedOf I T Wt) t)) → ∃ (mu : HeightOneSpectrum (𝓞 X.toD7.what₂.LL) → TupU I (usedOf I T Wt)) (twPl : Finset (HeightOneSpectrum (𝓞 X.toD7.what₂.LL))), MuOf X I T Wt mu twPl ∧ ∀ Xg tr, Seed.TupL (famR X I hX (usedOf I T Wt) Xg tr) L mu twPl := by
  classical
  intro X px I hX T Wt L hWf hWc hI hrng hC hxi

  have hmemR : ∀ w ∈ Wt, T.xiTw I.C w ∈ Set.range I.xi := fun w _ => by
    rw [hrng]; exact Or.inr ⟨w, rfl⟩
  have hpickU : ∀ w ∈ Wt, pickIxTw I (T.xiTw I.C w) ∈ (usedOf I T Wt) := fun w hw => ⟨w, hw, xi_pickIxTw I (hmemR w hw)⟩

  let muP : X.B.places.Pl → TupU I (usedOf I T Wt) := fun w =>
    if h : w ∈ Wt then ⟨I.tup (pickIxTw I (T.xiTw I.C w)), Or.inr ((tup_mem_tuOf I).2 (hpickU w h))⟩
    else mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt))
  have muP_in : ∀ w (h : w ∈ Wt), muP w = ⟨I.tup (pickIxTw I (T.xiTw I.C w)), Or.inr ((tup_mem_tuOf I).2 (hpickU w h))⟩ :=
    fun w h => dif_pos h
  have muP_of_notMem : ∀ w, w ∉ Wt → muP w = mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt)) := fun w h => dif_neg h
  have ix_in : ∀ w ∈ Wt, ixOf I (usedOf I T Wt) (muP w) = pickIxTw I (T.xiTw I.C w) := fun w h => by
    rw [muP_in w h]; exact ixOf_eq I rfl
  have hcc : ∀ w, X.B.places.conj (X.B.places.conj w) = w := fun w => by
    apply X.toD7.plEq.injective
    have e1 := plEq_conjPl X.toD7 (X.toD7.what₂.places.conj w)
    have e2 := plEq_conjPl X.toD7 w
    change X.toD7.plEq (X.toD7.what₂.places.conj (X.toD7.what₂.places.conj w)) = X.toD7.plEq w
    rw [e1, e2, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
  have hconjIff : ∀ w, X.B.places.conj w ∈ Wt ↔ w ∈ Wt := fun w =>
    ⟨fun h => hcc w ▸ hWc _ h, hWc w⟩
  have muP_conj : ∀ w, muP (X.B.places.conj w) = muP w := fun w => by
    by_cases h : w ∈ Wt
    · rw [muP_in w h, muP_in _ ((hconjIff w).2 h)]
      congr 2
      rw [(GlobalTheory.Mem.Top.TwFin.tw_fin X.B I.C T).2.2.1 w]
    · rw [muP_of_notMem w h, muP_of_notMem _ (fun h' => h ((hconjIff w).1 h'))]
  have hss : ∀ w : X.B.places.Pl, muP (X.toD7.plEq.symm (X.toD7.plEq w)) = muP w :=
    fun w => congrArg muP (X.toD7.plEq.symm_apply_apply w)
  refine ⟨fun v => muP (X.toD7.plEq.symm v), hWf.toFinset.image X.toD7.plEq, ?_, ?_⟩
  · intro w
    refine ⟨?_, ?_⟩
    · erw [Finset.mem_image]
      constructor
      · rintro ⟨w', hw', e⟩
        rw [X.toD7.plEq.injective e] at hw'
        exact (Set.Finite.mem_toFinset hWf).1 hw'
      · intro h
        exact ⟨w, (Set.Finite.mem_toFinset hWf).2 h, rfl⟩
    · show I.xi (ixOf I (usedOf I T Wt) (muP (X.toD7.plEq.symm (X.toD7.plEq w)))) = _
      rw [hss]
      by_cases h : w ∈ Wt
      · rw [if_pos h, ix_in w h, xi_pickIxTw I (hmemR w h)]
      · rw [if_neg h, muP_of_notMem w h, ixOf_mu0F]
        exact hI.trueColumnChoices_heckeChar_reference_eq_one
  · intro Xg tr
    have hμ0 : (famR X I hX (usedOf I T Wt) Xg tr).A.μ0 = mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt)) := rfl
    have memTw : ∀ v, v ∈ hWf.toFinset.image X.toD7.plEq ↔ X.toD7.plEq.symm v ∈ Wt := fun v => by
      erw [Finset.mem_image]
      constructor
      · rintro ⟨w', hw', rfl⟩
        rw [Equiv.symm_apply_apply]
        exact (Set.Finite.mem_toFinset hWf).1 hw'
      · intro h
        exact ⟨_, (Set.Finite.mem_toFinset hWf).2 h, Equiv.apply_symm_apply _ _⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro v hv
      rw [hμ0]
      exact muP_of_notMem _ (fun h => hv ((memTw v).2 h))
    · intro t
      rw [hμ0]
      rcases t.2 with h | h
      · exact Or.inl (Subtype.ext h)
      · right
        obtain ⟨b, hb, e⟩ := (mem_tuOf I).1 h
        obtain ⟨w, hw, hbw⟩ := hb
        refine ⟨X.toD7.plEq w, ?_⟩
        show muP (X.toD7.plEq.symm (X.toD7.plEq w)) = t
        rw [hss, muP_in w hw]
        apply Subtype.ext
        show I.tup (pickIxTw I (T.xiTw I.C w)) = t.1
        rw [← e]
        congr 1
        apply hI.xi_inj
        rw [xi_pickIxTw I (hmemR w hw), hbw]
    · intro v hv e
      rw [hμ0] at e
      have hw := (memTw v).1 hv
      have h1 := congrArg (ixOf I (usedOf I T Wt)) e
      rw [ix_in _ hw, ixOf_mu0F] at h1
      have h2 := congrArg I.xi h1
      rw [xi_pickIxTw I (hmemR _ hw), hI.trueColumnChoices_heckeChar_reference_eq_one] at h2
      exact (GlobalTheory.Mem.Top.TwFin.tw_fin X.B I.C T).2.1 _ h2
    · intro v
      have e : Formalism.DivisionValues.conjPl v = X.toD7.plEq (X.B.places.conj (X.toD7.plEq.symm v)) := by
        have := plEq_conjPl X.toD7 (X.toD7.plEq.symm v)
        rw [Equiv.apply_symm_apply] at this
        exact this.symm
      show muP (X.toD7.plEq.symm (Formalism.DivisionValues.conjPl v)) = muP (X.toD7.plEq.symm v)
      rw [e, hss]
      exact muP_conj _
    · intro v hv
      have hw := (memTw v).1 hv
      set w := X.toD7.plEq.symm v with hwdef
      have hv' : v = X.toD7.plEq w := by rw [hwdef, Equiv.apply_symm_apply]
      have hpl : Formalism.EigenvalueLevelCeiling.plc v = X.B.places.resChar w := by
        rw [hv']
        exact plc_eq_of_natCast_mem _ (X.B.places.resChar_prime w) (GlobalTheory.LvT.Inh.resChar_mem_plEq X.toD7 w)
      refine ⟨T.psi w, T.Q w, ?_, ?_⟩
      · rw [hpl]; exact T.psi_is w
      · rw [hxi, hpl, hC]
        show I.xi (ixOf I (usedOf I T Wt) (muP w)) = _
        rw [ix_in w hw, xi_pickIxTw I (hmemR w hw)]
        rfl
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticDataKeptClausesColumnChoices
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

noncomputable section

namespace GlobalTheory.Mem.R3.FrameCaseLifts

open Formalism.IndefR.Seed Formalism.IndefR.Seed.Frm in
theorem frames_by_cases_lifts {D : D7} (hY : ∀ j, FrmC.StdLat (D.sp.Y j)) (hX : FrmC.StdLat D.sp.X')
    (hV : ∀ j, FrmC.StdLat (D.sp.V j)) (hW : ∀ j, 1 ≤ j → j ≤ D.R.m → FrmC.StdLat (D.sp.W j)) (Pg : Finset (Pl D.host.E)) :
    ∃ (ΛY : ∀ j, Submodule (𝓞 D.host.E) (Fin (Yc D j).rank → D.host.E))
      (ΛW : ∀ i, Submodule (𝓞 D.host.E) (Fin (Wc D i).rank → D.host.E))
      (βY : ∀ j, GL (Fin (Yc D j).rank) (Datum.EAf D)) (βW : ∀ i, GL (Fin (Wc D i).rank) (Datum.EAf D)),
      SDFrames ΛY (FrmP.coordL D.sp.X') (fun i => FrmP.coordL (Vc D i)) ΛW βY 1 (fun _ => 1) βW ∧
        (FramesExistDiagonal D Pg → NormalFrameConditionsDiagonal Pg βY βW) := by
  by_cases h : FramesExistDiagonal D Pg
  · obtain ⟨ΛY, -, -, ΛW, βY, -, -, βW, ⟨h1, -, -, h4⟩, h2⟩ := h
    exact ⟨ΛY, ΛW, βY, βW, ⟨h1, FrmP.isSDFrame_std _ hX 1, fun i => FrmP.isSDFrame_std _ (hV _) 1, h4⟩, fun _ => h2⟩
  · exact ⟨fun j => FrmP.coordL (Yc D j), fun i => FrmP.coordL (Wc D i), fun _ => 1, fun _ => 1,
      ⟨fun j _ => FrmP.isSDFrame_std _ (hY _) _, FrmP.isSDFrame_std _ hX 1, fun i => FrmP.isSDFrame_std _ (hV _) 1,
        fun i => FrmP.isSDFrame_std _ (hW _ (by omega) i.2) 1⟩, fun h' => absurd h' h⟩

theorem exists_levCh_tuples_of_lifts : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (T : Top.TwDat X.B) (Wt : Set X.B.places.Pl), Wt.Finite → (∀ w ∈ Wt, X.B.places.conj w ∈ Wt) → I.Ok → Set.range I.xi = T.set I.C → SelHalf I → X.B.host.ccK = ⊤ → (∀ j, Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Seed.FrmC.StdLat (X.toD7.sp.V j) ∧ (1 ≤ j → j ≤ X.toD7.R.m → Seed.FrmC.StdLat (X.toD7.sp.W j))) → Seed.FrmC.StdLat X.toD7.sp.X' → ∃ (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I (usedOf I T Wt))) (mu : HeightOneSpectrum (𝓞 X.toD7.what₂.LL) → TupU I (usedOf I T Wt)) (twPl : Finset (HeightOneSpectrum (𝓞 X.toD7.what₂.LL))), LevOf X I (usedOf I T Wt) L ∧ (Seed.Frm.FramesExistDiagonal X.toD7 L.Pg → Seed.Frm.NormalFrameConditionsDiagonal L.Pg L.βY L.βW) ∧ MuOf X I T Wt mu twPl ∧ (∀ Xg tr, Seed.TupL (famR X I hX (usedOf I T Wt) Xg tr) L mu twPl) ∧ ∀ t, ∀ P ∈ L.Q t, ((X.B.host.QS * X.B.host.q * Ideal.absNorm X.B.host.ccK : ℕ) : 𝓞 X.B.host.E) ∉ P.asIdeal := by
  intro X px I hX T Wt hWf hWc hI hrng hsel hcc hYVW hX'
  classical
  set U := usedOf I T Wt with hU
  have htw : ∀ a, Chr.IsTwist X.B.host I.S (I.xi a) := fun a =>
    (GlobalTheory.Mem.ReadTwist.isTwist_of_reads _ X.B.host _ _ _ (I.tup a) (I.xi a) (hI.xi_reads a)).1
  have hram := GlobalTheory.Mem.Col2.RamQ.ram_iff X px I hI
  have hQr : ∀ a, ∀ PP ∈ I.Q a, ¬ (I.xi a).UnrAt PP := fun a PP h => (hram a PP).2 (Or.inl h)
  have hpl := fun a => GlobalTheory.Mem.TwistPlaces.twistPlaces X px I hI a (hQr a)
  obtain ⟨L0, h1, h2, h3, -, h4⟩ := GlobalTheory.LevelChoices.exists_levCh X.toD7 (Top.Fr.at X I.C) (TupU I U)
    (mu0F (X := X.B.fields) (tuOf I U)) (fun t => I.xi (ixOf I U t)) (fun t => I.Q (ixOf I U t))
    (hI.xi_inj.comp (ixOf_injective I U)) (by simp only [ixOf_mu0F]; exact hI.trueColumnChoices_heckeChar_reference_eq_one)
    (fun t => (htw _).1) (fun t => (htw _).2.1) (fun t => (htw _).2.2.1)
    (fun t => (hpl _).1) (fun t => (hpl _).2)
    (fun p hp => by
      have hpp : p.Prime := by
        rcases hp with rfl | rfl
        exacts [X.B.host.pde_prime, X.B.host.pde'_prime]
      obtain ⟨𝔭, h𝔭⟩ := GlobalTheory.Mem.R3.Model.exists_under_of_selHalf I hsel p hpp
      exact ⟨𝔭, fun t PP hPP hp' => h𝔭 _ PP hPP hp'⟩)
    (fun t PP => hram _ PP)
  have hPg : L0.Pg = (X.B.primes px).vGs := by
    refine Finset.ext fun P => (h4.Pg P).trans ?_
    rw [h1]
    exact (GlobalTheory.Mem.R3.Model.mem_vGs_iff I hI P).symm
  obtain ⟨ΛY, ΛW, βY, βW, hSD, hfr⟩ := frames_by_cases_lifts (D := X.toD7)
    (fun j => (hYVW j).1) hX' (fun j => (hYVW j).2.1) (fun j => (hYVW j).2.2) (X.B.primes px).vGs
  let L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U) :=
    { L0 with
      ΛY := ΛY
      ΛW := ΛW
      βY := βY
      βW := βW
      βX := 1
      βV := (fun _ => 1)
      ΛX := Formalism.IndefR.Seed.FrmP.coordL _
      ΛV := (fun _ => Formalism.IndefR.Seed.FrmP.coordL _) }
  have hLC : L.C = Top.Fr.at X I.C := h1
  have hLx : ∀ t, L.xiH t = I.xi (ixOf I U t) := fun t => congrFun h2 t
  obtain ⟨mu, twPl, hmu, htup⟩ := GlobalTheory.Mem.R3.tupL_of_twisted X px I hX T Wt L hWf hWc hI hrng hLC hLx
  refine ⟨L, mu, twPl, ⟨⟨h4.mu0, h4.eta, h4.xi, h4.xi_inj, h4.xi_base, h4.xi_fin, h4.xi_triv, h4.xi_tame, h4.Pg, h4.Q_pl,
      h4.Q_off, h4.Q_de, h4.Q_ram, h4.chi, h4.xiR, hSD.1, hSD.2.1, hSD.2.2.1, hSD.2.2.2⟩, h1, fun t => congrFun h2 t, hPg,
      fun t => congrFun h3 t, fun _ => rfl, rfl⟩, fun h => by
      show Seed.Frm.NormalFrameConditionsDiagonal L0.Pg βY βW
      rw [hPg]
      exact hfr (hPg ▸ h), hmu, htup, fun t P hP => ?_⟩
  have hP' : P ∈ I.Q (ixOf I U t) := by rw [← congrFun h3 t]; exact hP
  have hoff := ((hpl (ixOf I U t)).2 P hP').1
  intro hm
  apply hoff
  have e : Ideal.absNorm X.B.host.ccK = 1 := by rw [hcc, Ideal.absNorm_top]
  rw [e, mul_one] at hm
  have : ((X.toD7.host.QS * X.toD7.host.q * X.toD7.host.d * X.toD7.sp.T : ℕ) : 𝓞 X.toD7.host.E) =
      ((X.toD7.host.d * X.toD7.sp.T : ℕ) : 𝓞 X.toD7.host.E) * ((X.B.host.QS * X.B.host.q : ℕ) : 𝓞 X.toD7.host.E) := by
    rw [← Nat.cast_mul]
    congr 1
    change X.B.host.QS * X.B.host.q * X.B.host.d * X.B.sp.T = X.B.host.d * X.B.sp.T * (X.B.host.QS * X.B.host.q)
    ring
  rw [this]
  exact Ideal.mul_mem_left P.asIdeal _ hm

set_option maxHeartbeats 1000000 in
theorem exists_realDat_keep : ∀ (X : Stages) (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (T : Top.TwDat X.B)
    (Wt : Set X.B.places.Pl) (Ks' : Type) [Field Ks'] [NumberField Ks'] [Algebra Ks' X.toD7.what₂.LL],
    GlobalTheory.Published.DiscreteSeriesExists → Wt.Finite → (∀ w ∈ Wt, X.B.places.conj w ∈ Wt) → I.Ok → Set.range I.xi = T.set I.C →
    SelHalf I → GrpAt X I → ValsIn I → HostHyp X.toD7 →
    (∀ j, Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Seed.FrmC.StdLat (X.toD7.sp.V j) ∧
      (1 ≤ j → j ≤ X.toD7.R.m → Seed.FrmC.StdLat (X.toD7.sp.W j))) → Seed.FrmC.StdLat X.toD7.sp.X' →
    (∀ i, (Vc X.toD7 i).IsPosDef) →
    (∀ x ∈ X.B.Ks, ∃ y : Ks', algebraMap Ks' X.toD7.what₂.LL y = x) →
    (∀ x : X.toD7.host.E, ∃ y : Ks', algebraMap Ks' X.toD7.what₂.LL y = X.toD7.embE x) →
    (∀ (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I (usedOf I T Wt))), L.Is (mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt))) →
      L.C = Top.Fr.at X I.C → ∀ (i : Fin X.toD7.R.m) (x : (AE X.toD7)ˣ), infPart X.toD7 (x : AE X.toD7) = 1 →
        ∃ y : Ks', ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = X.toD7.what₂.embLL (algebraMap Ks' X.toD7.what₂.LL y)) →
    ∃ (Xg : Finset (Gc X.B px → X.B.LL)) (tr₀ : TrI X.B px) (R₀ : RealDat3 X.toD7 (famR X I hX (usedOf I T Wt) Xg tr₀) Ks')
      (cG : G0 R₀.Pg X.toD7.R.r ≃* G0g X.toD7.nd),
      LevOf X I (usedOf I T Wt) R₀.toRealDat.toLevCh ∧ IsPlacewiseIdentity X (px := px) R₀.eG ∧ GoodSet X (px := px) (R₀.eG.trans cG) Xg ∧
      MuOf X I T Wt R₀.mu R₀.twPl ∧ IdemClass (D := X.toD7) (famR X I hX (usedOf I T Wt) Xg tr₀).A ∧
      R₀.toRealDat.Pre0 (face0 X I hX (usedOf I T Wt) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧ R₀.AllPlaces ∧
      Keep R₀.toRealDat (face0 X I hX (usedOf I T Wt) Xg tr₀).lv2 cG ∧ BrgStd X I hX (usedOf I T Wt) Xg tr₀ R₀.toRealDat := by
  intro X px I hX T Wt Ks' _ _ _ hDS hWf hWc hI hrng hsel hgrp hval hhost hYVW hX' hpos hKs hE hmuKs
  obtain ⟨L, mu, twPl, hL, hfr, hmu, htup, hq⟩ :=
    exists_levCh_tuples_of_lifts X px I hX T Wt hWf hWc hI hrng hsel X.B.ccK_top hYVW hX'
  obtain ⟨eG, cG, Xg, hid, hgood, hpsi, hc1, hc2, hrest⟩ := GlobalTheory.T.exists_finite_group_goodSet_levels_characters X px I hX (usedOf I T Wt) L hI hgrp hL
  obtain ⟨hidem, hlv, plg, iso, hp1, hp2, hp3⟩ := hrest (fun _ g => g)
  obtain ⟨hMY, hMW⟩ := GlobalTheory.ChainModels.models_seed hDS X.toD7 hhost
  obtain ⟨MW, hMW1, hMW2⟩ := hMW Ks' hE
  obtain ⟨ψ, hψ⟩ := GlobalTheory.StdAdelicChar.exists_isStdChar X.toD7
  obtain ⟨R, e1, e2, e3, e4, e5, e6, hpr, hpre, hin, htu, hall, hstd⟩ :=
    GlobalTheory.SeedChoices.seed_at_reading_keeping X.toD7 (Gc X.B px) (PlS X.B px) (PlI X.B px) (TupU I (usedOf I T Wt))
      (famR X I hX (usedOf I T Wt) Xg (fun _ g => g)) Ks' (face0 X I hX (usedOf I T Wt) Xg (fun _ g => g)) L eG mu twPl ψ MW
      hL.is (htup _ _) ⟨eG.trans cG, plg, iso, hgood.2, hp2, hp3⟩ hlv hMY hMW1 hpos hψ
      (fun cX cV jR jL => BrgStdR X I hX (usedOf I T Wt) Xg (fun _ g => g) L cX jR ∧
        ∀ i, BrgStdV X I hX (usedOf I T Wt) Xg (fun _ g => g) L i (cV i) (jL i))
      (GlobalTheory.T.exists_adelicReading_decoratedLatticeForms X px I hX (usedOf I T Wt) Xg (fun _ g => g) L eG hI hval hL hid hL.beta.2 hL.beta.1 hX' (fun i => (hYVW _).2.1))
  subst e1
  obtain rfl := eq_of_heq e4
  subst e3 e5 e6
  refine ⟨Xg, fun _ g => g, R, cG, hL, hid, hgood, hmu, hidem, hpre, hin, htu, hall,
    ⟨hpre.std, GlobalTheory.SignsAtTypePrimes.signsAtG _ _ _ _ _ _ R.toRealDat _ cG hpre.std hpsi ⟨plg, iso, hp1, hp2, hp3⟩, hfr, hL.beta,
      hpr, ⟨plg, iso, hp1, hgood.2, hp2, hp3⟩, hpsi, ⟨fun t P hP P' hP' h => ?_, hq⟩, hmuKs _ hL.is hL.C, hMW2,
      fun p => hKs _ (hc2 p), fun g => hKs _ (hc1 g)⟩, hstd⟩
  rw [hL.Q t] at hP hP'
  exact hsel _ _ P hP P' hP' h

end GlobalTheory.Mem.R3.FrameCaseLifts

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAnalyticDataKeptClausesColumnChoicesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analyticData_kept_clauses_columnChoices : ∀ (X : Stages) (px : PreX X.B.toPre) (I : ColIn X.B px) (hX : X.B.fields.Ok) (T : Top.TwDat X.B)
    (Wt : Set X.B.places.Pl) (Ks' : Type) [Field Ks'] [NumberField Ks'] [Algebra Ks' X.toD7.what₂.LL],
    GlobalTheory.Published.DiscreteSeriesExists → Wt.Finite → (∀ w ∈ Wt, X.B.places.conj w ∈ Wt) → I.Ok → Set.range I.xi = T.set I.C →
    SelHalf I → GrpAt X I → ValsIn I → HostHyp X.toD7 →
    (∀ j, Seed.FrmC.StdLat (X.toD7.sp.Y j) ∧ Seed.FrmC.StdLat (X.toD7.sp.V j) ∧
      (1 ≤ j → j ≤ X.toD7.R.m → Seed.FrmC.StdLat (X.toD7.sp.W j))) → Seed.FrmC.StdLat X.toD7.sp.X' →
    (∀ i, (Vc X.toD7 i).IsPosDef) →
    (∀ x ∈ X.B.Ks, ∃ y : Ks', algebraMap Ks' X.toD7.what₂.LL y = x) →
    (∀ x : X.toD7.host.E, ∃ y : Ks', algebraMap Ks' X.toD7.what₂.LL y = X.toD7.embE x) →
    (∀ (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I (usedOf I T Wt))), L.Is (mu0F (X := X.B.fields) (tuOf I (usedOf I T Wt))) →
      L.C = Top.Fr.at X I.C → ∀ (i : Fin X.toD7.R.m) (x : (AE X.toD7)ˣ), infPart X.toD7 (x : AE X.toD7) = 1 →
        ∃ y : Ks', ((L.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = X.toD7.what₂.embLL (algebraMap Ks' X.toD7.what₂.LL y)) →
    ∃ (Xg : Finset (Gc X.B px → X.B.LL)) (tr₀ : TrI X.B px) (R₀ : RealDat3 X.toD7 (famR X I hX (usedOf I T Wt) Xg tr₀) Ks')
      (cG : G0 R₀.Pg X.toD7.R.r ≃* G0g X.toD7.nd),
      LevOf X I (usedOf I T Wt) R₀.toRealDat.toLevCh ∧ IsPlacewiseIdentity X (px := px) R₀.eG ∧ GoodSet X (px := px) (R₀.eG.trans cG) Xg ∧
      MuOf X I T Wt R₀.mu R₀.twPl ∧ IdemClass (D := X.toD7) (famR X I hX (usedOf I T Wt) Xg tr₀).A ∧
      R₀.toRealDat.Pre0 (face0 X I hX (usedOf I T Wt) Xg tr₀).lv2 ∧ R₀.IsInert ∧ R₀.IsTup ∧ R₀.AllPlaces ∧
      Keep R₀.toRealDat (face0 X I hX (usedOf I T Wt) Xg tr₀).lv2 cG ∧ BrgStd X I hX (usedOf I T Wt) Xg tr₀ R₀.toRealDat  := by
  first | exact @GlobalTheory.Mem.R3.FrameCaseLifts.exists_realDat_keep | exact GlobalTheory.Mem.R3.FrameCaseLifts.exists_realDat_keep | (intros; apply GlobalTheory.Mem.R3.FrameCaseLifts.exists_realDat_keep <;> assumption)
end
