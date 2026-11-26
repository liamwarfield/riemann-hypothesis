module

public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsConstMovedVacuumAllTuples
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPlaceModelCompIdempotentSplitTensor
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FamilyConstants

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIndexPlaceEqOfReadsStdOfMem
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.XGeoPlace
end GlobalTheory.XGeoPlace
theorem GlobalTheory.XGeoPlace.exists_index_place_eq_of_readsStd_of_mem : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ (u : B.Word) (PP : Pl (I.rec7 l Z).host.E), PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP → ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (_ : MeasurableSpace k) (_ : BorelSpace k) (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k), Formalism.L2.NTheta.IsIdemAt q.e PP ∧ q.v = PP.under (𝓞 (I.rec7 l Z).host.F) ∧ q.UnitAA ∧ valuation k ((GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.piE I l Z u)) = 1 := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u PP hPP
  have hC := hW.pk.bot.hyp.2.2.2.1
  have hnc : ¬ Lev.IsConjPl PP PP := by
    rcases hPP with hg | ⟨t, ht⟩
    · exact GlobalTheory.SeeConjPlaces.pg_not_isConjPl (_root_.GlobalTheory.Fam.pk_z W) W.Q.F.lv2 hC.lev hC.grp PP hg PP hg
    · exact (hC.lev.Q_pl t PP ht).2 PP ht
  obtain ⟨e, he⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt hnc
  obtain ⟨k, _, _, _, _, q, hqe, hqv, hint, -⟩ := GlobalTheory.LocMod.SplitCompl.exists_place _ PP e he
  obtain ⟨ℓ, hℓ, hℓP, h2q, hd⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal ∧
      (B.host.QS * B.host.q).Coprime ℓ ∧ B.host.d.Coprime ℓ := by
    rcases hPP with hg | ⟨t, ht⟩
    · have hgg := hW.lev.1.1 PP hg
      rw [Nat.cast_mul] at hgg
      obtain ⟨i, hi⟩ : ∃ i : Fin 2, ((B.host.g i : ℕ) : 𝓞 (I.rec7 l Z).host.E) ∈ PP.asIdeal := by
        rcases PP.isPrime.mem_or_mem hgg with h | h
        · exact ⟨0, h⟩
        · exact ⟨1, h⟩
      have hc : (B.host.g i).Coprime (B.host.QS * B.host.q * B.host.d) := by
        rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, B.g_cond i, Nat.gcd_one_left]
      refine ⟨B.host.g i, B.host.g_prime i, hi, (hc.coprime_dvd_right ⟨B.host.d, rfl⟩).symm,
        (hc.coprime_dvd_right (Dvd.intro_left _ rfl)).symm⟩
    · have hoff := (hC.lev.Q_off t PP ht).1
      obtain ⟨ℓ, hℓ, hℓP⟩ := GlobalTheory.XGeoPlace.exists_prime_mem_pl PP
      have key : ∀ m : ℕ, m ∣ B.host.QS * B.host.q * B.host.d * (I.rec7 l Z).sp.T → m.Coprime ℓ := fun m hm =>
        Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hℓ).2 fun hdv =>
          hoff (Ideal.mem_of_dvd _ (Nat.cast_dvd_cast (hdv.trans hm)) hℓP))
      exact ⟨ℓ, hℓ, hℓP, key _ ⟨B.host.d * (I.rec7 l Z).sp.T, by ring⟩, key _ ⟨B.host.QS * B.host.q * (I.rec7 l Z).sp.T, by ring⟩⟩
  have hv : (ℓ : 𝓞 (I.rec7 l Z).host.F) ∈ q.v.asIdeal := by
    rw [hqv, HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, map_natCast]
    exact hℓP
  have hcc : (Ideal.absNorm (I.rec7 l Z).host.ccK).Coprime ℓ := by
    show Nat.Coprime (Ideal.absNorm B.host.ccK) _
    rw [B.ccK_top, Ideal.absNorm_top]
    exact Nat.coprime_one_left _
  have hU : q.UnitAA := GlobalTheory.SeeSaw.StdOff.unitAA_of q hℓ hv h2q hd hcc
  have hT : (((B.T u : ℕ)) : 𝓞 (I.rec7 l Z).host.E) ∉ PP.asIdeal := by
    rcases hPP with hg | ⟨t, ht⟩
    · exact Formalism.L2.Col.T_notMem_vGs l.pr u ⟨PP, (hW.lev.2.1 PP).1 hg⟩
    · exact (hC.lev.Q_off t PP ht).2 u
  set π : 𝓞 (I.rec7 l Z).host.E := X.piT u with hπdef
  have hπ : π ∉ PP.asIdeal := fun h => hT (by
    have h2 := PP.asIdeal.mul_mem_left (B.fields.conjO ((B.primes X).piT u)) h
    have h3 : (B.primes X).piT u * B.fields.conjO ((B.primes X).piT u) ∈ PP.asIdeal := by
      rw [mul_comm]
      exact h2
    rw [l.pr.piT_norm u] at h3
    exact h3)
  have hπ0 : (π : (I.rec7 l Z).host.E) ≠ 0 := fun h0 => hπ (by
    rw [show π = 0 from RingOfIntegers.coe_injective (by simpa using h0)]
    exact zero_mem _)
  have e1 : (GlobalTheory.XGeoStd.piE I l Z u) = (π : (I.rec7 l Z).host.E) := rfl
  have hin1 := (hint (π : (I.rec7 l Z).host.E)).2 ⟨π, 1, fun h => PP.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h), by simp⟩
  have hin2 := (hint (π : (I.rec7 l Z).host.E)⁻¹).2 ⟨1, π, hπ, by simp [hπ0]⟩
  have hinv : (GlobalTheory.LocMod.ofSplit q).pr ((π : (I.rec7 l Z).host.E)⁻¹) = ((GlobalTheory.LocMod.ofSplit q).pr (π : (I.rec7 l Z).host.E))⁻¹ := by
    show ((GlobalTheory.LocMod.ofSplit q).π.comp (incA (I.rec7 l Z))) _ = (((GlobalTheory.LocMod.ofSplit q).π.comp (incA (I.rec7 l Z))) _)⁻¹
    exact map_inv₀ _ _
  have hne : (GlobalTheory.LocMod.ofSplit q).pr (π : (I.rec7 l Z).host.E) ≠ 0 := by
    show ((GlobalTheory.LocMod.ofSplit q).π.comp (incA (I.rec7 l Z))) (π : (I.rec7 l Z).host.E) ≠ 0
    exact (map_ne_zero _).2 hπ0
  rw [hinv] at hin2
  rw [Valuation.mem_integer_iff] at hin1 hin2
  refine ⟨k, inferInstance, inferInstance, inferInstance, inferInstance, borel k, @BorelSpace.mk _ _ (borel k) rfl, q, hqe ▸ he, hqv, hU, ?_⟩
  rw [e1]
  rw [map_inv₀] at hin2
  exact le_antisymm hin1 ((inv_le_one₀ (zero_lt_iff.2 ((map_ne_zero _).2 hne))).1 hin2)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLocXStd
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLocXStd
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.XGeoStd.Frames
open GlobalTheory.SymBridge GlobalTheory.FinPl GlobalTheory.Fam.Inhab
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
end GlobalTheory.XGeoStd.Frames
namespace GlobalTheory.XGeoStd.Frames
open GlobalTheory.SymBridge GlobalTheory.FinPl GlobalTheory.Fam.Inhab
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre}
end GlobalTheory.XGeoStd.Frames
namespace GlobalTheory.XGeoStd.Frames
end GlobalTheory.XGeoStd.Frames
namespace GlobalTheory.XGeoStd.Frames
set_option maxHeartbeats 4000000 in
theorem exists_locX_std_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (u : B.Word) (vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ) (PP : Pl (I.rec7 l Z).host.E) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k), Formalism.L2.NTheta.IsIdemAt q.e PP → q.v = PP.under (𝓞 (I.rec7 l Z).host.F) → q.UnitAA → valuation k ((GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.piE I l Z u)) = 1 → ∃ s : LocX (GlobalTheory.XGeoStd.xgeo l Z hW.tr.ok vac u (_root_.GlobalTheory.Fam.pk_z W).ΛX) (_root_.GlobalTheory.Fam.pk_z W).βX PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (s.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos s.FT := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u vac PP k _ _ _ _ _ _ q hidem hunder hunit hval
  have hI := hW.tr.ok
  obtain ⟨hsI, hXsp, hX'sp, -⟩ := hI.spaces
  have hLX : ∀ j, ((GlobalTheory.PlaceModel.latFrame ((I.rec7 l Z).sp.X j)) : Set (Fin ((I.rec7 l Z).sp.X j).rank → (I.rec7 l Z).host.E)) =
      GlobalTheory.AdForm.intVec _ _ := fun j => GlobalTheory.AdForm.PinInhab.lat_X hI j
  have hLT : (((_root_.GlobalTheory.Fam.pk_z W).ΛX : GlobalTheory.FinPl.Lat (I.rec7 l Z).sp.X') : Set (Fin (I.rec7 l Z).sp.X'.rank → (I.rec7 l Z).host.E)) =
      GlobalTheory.AdForm.intVec _ _ := by
    rw [GlobalTheory.XGeoStd.eq_latFrame_of_isSDFrame W.Q.charW.base.lev.βX]
    exact GlobalTheory.AdForm.VacStd.coe_latFrame_of_eq _ hsI _ hX'sp
  have hβ : (_root_.GlobalTheory.Fam.pk_z W).βX = 1 := hW.pk.bot.pins.betaStd.2
  have hm := (I.rec7 l Z).R.two_le_m
  obtain ⟨s, hs⟩ : ∃ s, s + 1 + 1 = (I.rec7 l Z).R.m := ⟨(I.rec7 l Z).R.m - 2, by omega⟩
  have rX : ∀ j, j ≤ s + 1 → (I.rec7 l Z).R.k + j + j * (I.rec7 l Z).R.t = ((I.rec7 l Z).sp.X j).rank := by
    intro j hj
    rw [Formalism.L2.Forms.rankN _ j (by omega)]
    show _ = (I.rec7 l Z).R.k + j * ((I.rec7 l Z).R.t + 1)
    ring
  have rT : (I.rec7 l Z).R.k + (s + 1) + (s + 2) * (I.rec7 l Z).R.t = (I.rec7 l Z).sp.X'.rank := by
    rw [Formalism.L2.Forms.rankP, show (I.rec7 l Z).R.N (I.rec7 l Z).R.m = (I.rec7 l Z).R.k + (I.rec7 l Z).R.m * ((I.rec7 l Z).R.t + 1) from rfl,
      ← hs]
    have e : (s + 1 + 1) * ((I.rec7 l Z).R.t + 1) = (s + 2) * (I.rec7 l Z).R.t + (s + 1) + 1 := by ring
    rw [e]
    omega
  have rM : (I.rec7 l Z).sp.X'.rank + 1 = ((I.rec7 l Z).sp.X (s + 1 + 1)).rank := by
    rw [hs]; exact GlobalTheory.AdForm.LiveModel.rk_top _
  set κ := (I.rec7 l Z).R.k
  set τ := (I.rec7 l Z).R.t
  let eX : ∀ j (hj : j ≤ s + 1), XIx (Fin κ) (Fin τ) j ≃ Fin ((I.rec7 l Z).sp.X j).rank := fun j hj =>
    (GlobalTheory.Fam.Inhab.blockOrd κ τ j j).trans (finCongr (rX j hj))
  have oX : ∀ j hj, GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.xPos (eX j hj) := fun j hj a => by
    simpa [eX] using GlobalTheory.Fam.Inhab.isOrd_xPos κ τ j a
  let eT : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ≃ Fin (I.rec7 l Z).sp.X'.rank :=
    (GlobalTheory.Fam.Inhab.blockOrd κ τ (s + 1) (s + 2)).trans (finCongr rT)
  have oT : GlobalTheory.SymBridge.IsOrd GlobalTheory.SymBridge.zPos eT := fun a => by
    simpa [eT] using GlobalTheory.Fam.Inhab.isOrd_zPos κ τ (s + 1) (s + 2) a
  let eM : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ⊕ Unit ≃ Fin ((I.rec7 l Z).sp.X (s + 1 + 1)).rank :=
    ((Equiv.sumCongr eT (finOneEquiv.symm)).trans finSumFinEquiv).trans (finCongr rM)
  have eM_l : ∀ a, (eM (Sum.inl a) : ℕ) = eT a := fun a => by simp [eM]
  have eM_r : (eM (Sum.inr ()) : ℕ) = (I.rec7 l Z).sp.X'.rank := by simp [eM]
  set π := (GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.piE I l Z u) with hπ
  have hπ0 : π ≠ 0 := fun h0 => by rw [h0, map_zero] at hval; exact zero_ne_one hval
  let dM : GlobalTheory.StepData.Ix (Fin κ ⊕ Fin (s + 1)) (Fin τ) (s + 2) ⊕ Unit → k := Sum.elim (fun _ => 1) fun _ => π
  have hd0 : ∀ y, dM y ≠ 0 := by rintro (a | a) <;> simp [dM, hπ0]
  have hdv : ∀ y, valuation k (dM y) = 1 := by rintro (a | a) <;> simp [dM, hval]
  refine ⟨{ k := k, q := q, idem := hidem, under := hunder, unit := hunit, s := s, hs := hs,
             FX := fun j hj => GlobalTheory.Fam.Inhab.stdFr k (eX j hj), FT := GlobalTheory.Fam.Inhab.stdFr k eT, FM := diagFr eM dM hd0,
             last := ?_, latX := ?_, latM := ?_, latT := ?_, frameTop := ?_ },
    fun j hj => GlobalTheory.Fam.Inhab.isStdFr_stdFr (oX j hj), GlobalTheory.Fam.Inhab.isStdFr_stdFr oT⟩
  · have hpr1 : (GlobalTheory.LocMod.ofSplit q).pr (1 : (I.rec7 l Z).host.E) = 1 := by simp [GlobalTheory.LocMod.Place.pr]
    have hpr0 : (GlobalTheory.LocMod.ofSplit q).pr (0 : (I.rec7 l Z).host.E) = 0 := by simp [GlobalTheory.LocMod.Place.pr]
    ext r c
    rcases c with c | c
    · rw [Matrix.fromCols_apply_inl]
      change ((GlobalTheory.Fam.Inhab.stdFr k eM).β * Matrix.diagonal dM) r (Sum.inl c) = _
      rw [Matrix.mul_diagonal]
      simp only [dM, Sum.elim_inl, mul_one]
      change (1 : Matrix _ _ k) r (eM (Sum.inl c)) =
        (((oTop l Z hI (s + 1 + 1) hs).iA.map (GlobalTheory.LocMod.ofSplit q).pr *
          (1 : Matrix (Fin (I.rec7 l Z).sp.X'.rank) (Fin (I.rec7 l Z).sp.X'.rank) k).submatrix id eT :
            Matrix (Fin ((I.rec7 l Z).sp.X (s + 1 + 1)).rank) _ k) r c)
      exact entry_inl _ hpr0 hpr1 eT _ (oTop_iA l Z hI (s + 1 + 1) hs) r c _ (eM_l c)
    · rw [Matrix.fromCols_apply_inr]
      change ((GlobalTheory.Fam.Inhab.stdFr k eM).β * Matrix.diagonal dM) r (Sum.inr c) = _
      rw [Matrix.mul_diagonal]
      simp only [dM, Sum.elim_inr]
      change (1 : Matrix _ _ k) r (eM (Sum.inr c)) * π =
        ((oTop l Z hI (s + 1 + 1) hs).iB.map (GlobalTheory.LocMod.ofSplit q).pr *ᵥ fun i => (GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.zeta I l Z u i)) r
      exact entry_inr _ hpr0 hpr1 _ (oTop_iB l Z hI (s + 1 + 1) hs) _ (GlobalTheory.XGeoStd.piE I l Z u) (fun _ => rfl) r _ eM_r
  · intro j hj
    exact intIn_stdFr q _ _ (hLX j) (eX j hj)
  · exact intIn_diagFr q _ _ (hLX (s + 1 + 1)) eM dM hd0 hdv
  · exact intIn_stdFr q _ _ hLT eT
  · refine ⟨eT, oT, fun b hb => ?_⟩
    have h1 : b.map (GlobalTheory.LocMod.ofSplit q).π = 1 := by
      have h2 : b.map (toEAf (I.rec7 l Z)) = (1 : Matrix (Fin (I.rec7 l Z).sp.X'.rank) (Fin (I.rec7 l Z).sp.X'.rank)
          (AE (I.rec7 l Z))).map (toEAf (I.rec7 l Z)) := by
        rw [hb, hβ, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
      rw [(GlobalTheory.LocMod.ofSplit q).map_pi_eq_of_toEAf h2, Matrix.map_one _ (map_zero _) (map_one _)]
    have h3 : (GlobalTheory.Fam.Inhab.stdFr k eT).β.submatrix id eT.symm = 1 := by
      change ((1 : Matrix (Fin (I.rec7 l Z).sp.X'.rank) (Fin (I.rec7 l Z).sp.X'.rank) k).submatrix id eT).submatrix id eT.symm = 1
      rw [Matrix.submatrix_submatrix]
      simp
    rw [h3, show (GlobalTheory.XGeoStd.xgeo l Z hI vac u (_root_.GlobalTheory.Fam.pk_z W).ΛX).bT = 1 from rfl, GlobalTheory.LocMod.mt_one_gaMat, Matrix.one_mul, h1]
end GlobalTheory.XGeoStd.Frames
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsLocXStdStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.true_family_vacuum_data_alt : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex) (hW : _root_.GlobalTheory.Fam.AllFamilyConditions W) (u : B.Word) (vac : ∀ j, WO ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) → ℂ) (PP : Pl (I.rec7 l Z).host.E) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (q : GlobalTheory.FinPl.SplitPt (I.rec7 l Z) k), Formalism.L2.NTheta.IsIdemAt q.e PP → q.v = PP.under (𝓞 (I.rec7 l Z).host.F) → q.UnitAA → valuation k ((GlobalTheory.LocMod.ofSplit q).pr (GlobalTheory.XGeoStd.piE I l Z u)) = 1 → ∃ s : LocX (GlobalTheory.XGeoStd.xgeo l Z hW.tr.ok vac u (_root_.GlobalTheory.Fam.pk_z W).ΛX) (_root_.GlobalTheory.Fam.pk_z W).βX PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (s.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos s.FT := by
  first | exact @_root_.GlobalTheory.XGeoStd.Frames.exists_locX_std_alt | exact _root_.GlobalTheory.XGeoStd.Frames.exists_locX_std_alt | (intros; apply _root_.GlobalTheory.XGeoStd.Frames.exists_locX_std_alt <;> assumption)
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsXgeo
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
theorem GlobalTheory.XGeoStd.exists_xgeo_alt : GlobalTheory.Published.StrongApproxSU → ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ u : B.Word, ∃ (a : XGeo (I.rec7 l Z)) (c₀ : ℕ → ℂ), (∀ j, j ≤ B.R.m → (a.x j).Is) ∧ GlobalTheory.AdForm.PinX I l Z (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ a.x a.vac c₀ ∧ a.bT = 1 ∧ (∀ r s, (a.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) ∧ a.LT = (_root_.GlobalTheory.Fam.pk_z W).ΛX ∧ IsLineVec a.Lz a.ζ₀ ∧ star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = ((((I.rec7 l Z).mem u).A.T : ℕ) : (I.rec7 l Z).host.E) ∧ GlobalTheory.AdForm.IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) ((a.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) ∧ (∀ r, vecB (a.oT B.R.m rfl) a.ζ₀ r = (show Fin (B.R.N B.R.m) → (I.rec7 l Z).host.E from TC.z0 X u) (Fin.cast (Formalism.L2.Forms.rankN (I.rec7 l Z) _ le_rfl) r)) ∧ (∀ n (h : n = B.R.m) x, ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) ∧ ∀ PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP → ∃ s : LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (s.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos s.FT := by
  open GlobalTheory.XGeoStd GlobalTheory.AdForm.LiveModel GlobalTheory.AdForm.PinInhab GlobalTheory.MixModel GlobalTheory.Mem in (
    intro hSA B X I l Z L hT Gi Gl Kc Yd cX ex W hW u
    have hI : I.Ok := hW.tr.ok
    obtain ⟨hP⟩ := hW.tr.pins
    have hψ : IsStdChar (I.rec7 l Z) (_root_.GlobalTheory.Fam.pk_z W).ψ (-1) := W.Q.stdChar
    have hθ : IsInfFam (_root_.GlobalTheory.Fam.pk_z W).θ := W.Q.charW.base.models.inf
    choose vac hvac using exists_vac (l := l) (Z := Z) hI hψ hθ
    choose c hc using fun i hi => GlobalTheory.T.exists_const_movedVacuum_all_tuples hSA I hI hP l Z _ _ hψ hθ i hi (vac i) (hvac i)
    refine ⟨xgeo l Z hI vac u (_root_.GlobalTheory.Fam.pk_z W).ΛX, fun j => if h : j + 1 ≤ B.R.m then c j h else 1,
      fun j _ => stdSp_is ((I.rec7 l Z).sp.X_sig _) (gram_X hI j),
      ⟨hψ, hθ, fun j _ => ⟨rfl, rfl, fun z => ?_⟩, fun j _ => hvac j, fun j hj => ?_⟩, rfl, fun r s => by
      show (if ((s : ℕ) = r) then (1 : (I.rec7 l Z).host.E) else 0) = if (r : ℕ) = s then 1 else 0
      by_cases h : (r : ℕ) = s
      · rw [if_pos h.symm, if_pos h]
      · rw [if_neg (fun h' => h h'.symm), if_neg h], rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← lat_X hI j]; exact Iff.rfl
    · rw [dite_eq_left hj]; exact hc j hj
    case refine_3 => exact isLineVec_zeta l Z u
    case refine_4 => exact norm_zeta l Z u
    case refine_5 => exact isEmbTop_topDec (gram_X hI _) (gram_X' hI) hP.iX _
    case refine_6 =>
      intro r
      have h0 := rk_top (I.rec7 l Z)
      have h2 := Formalism.L2.Forms.rankN (I.rec7 l Z) (I.rec7 l Z).R.m le_rfl
      change (∑ _i : Fin 1, (if (I.rec7 l Z).sp.X'.rank = (r : ℕ) then (1 : (I.rec7 l Z).host.E) else 0) *
        piE I l Z u) = if (r : ℕ) + 1 = B.R.N B.R.m then piE I l Z u else 0
      rw [Fin.sum_univ_one]
      have hr := r.2
      have e : ((I.rec7 l Z).sp.X'.rank = (r : ℕ)) ↔ ((r : ℕ) + 1 = B.R.N B.R.m) := by
        change _ ↔ (r : ℕ) + 1 = (I.rec7 l Z).R.N (I.rec7 l Z).R.m
        constructor <;> intro h <;> omega
      by_cases h : (I.rec7 l Z).sp.X'.rank = (r : ℕ)
      · rw [if_pos h, if_pos (e.1 h), one_mul]
      · rw [if_neg h, if_neg (fun h' => h (e.2 h')), zero_mul]
    case refine_7 =>
      intro n h x
      refine ⟨GlobalTheory.PlaceModel.latFrame _, GlobalTheory.PlaceModel.isSelfDualC_latFrame _, ?_⟩
      have e : (_root_.GlobalTheory.Fam.pk_z W).ΛX = GlobalTheory.PlaceModel.latFrame (I.rec7 l Z).sp.X' := eq_latFrame_of_isSDFrame W.Q.charW.base.lev.βX
      show GlobalTheory.FinPl.OrthAt (oTop l Z hI n h) (GlobalTheory.PlaceModel.latFrame ((I.rec7 l Z).sp.X n)) (_root_.GlobalTheory.Fam.pk_z W).ΛX _ x
      rw [e]
      exact GlobalTheory.XGeoStd.orthAt_oTop hI n h x
    case refine_8 =>
      intro PP hPP
      obtain ⟨k, _, _, _, _, _, _, q, h1, h2, h3, h4⟩ := _root_.GlobalTheory.XGeoPlace.exists_index_place_eq_of_readsStd_of_mem W hW u PP hPP
      exact _root_.GlobalTheory.T.true_family_vacuum_data_alt W hW u vac PP k q h1 h2 h3 h4
  )
end
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsXgeoStatement
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.all_true_family_geometry_alt : GlobalTheory.Published.StrongApproxSU → ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : _root_.GlobalTheory.MiS.RealPackAlt ex), _root_.GlobalTheory.Fam.AllFamilyConditions W → ∀ u : B.Word, ∃ (a : XGeo (I.rec7 l Z)) (c₀ : ℕ → ℂ), (∀ j, j ≤ B.R.m → (a.x j).Is) ∧ GlobalTheory.AdForm.PinX I l Z (_root_.GlobalTheory.Fam.pk_z W).ψ (_root_.GlobalTheory.Fam.pk_z W).θ a.x a.vac c₀ ∧ a.bT = 1 ∧ (∀ r s, (a.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) ∧ a.LT = (_root_.GlobalTheory.Fam.pk_z W).ΛX ∧ IsLineVec a.Lz a.ζ₀ ∧ star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = ((((I.rec7 l Z).mem u).A.T : ℕ) : (I.rec7 l Z).host.E) ∧ GlobalTheory.AdForm.IsEmbTop (D := I.rec7 l Z) (TC.z0 X u) ((a.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _)) ∧ (∀ r, vecB (a.oT B.R.m rfl) a.ζ₀ r = (show Fin (B.R.N B.R.m) → (I.rec7 l Z).host.E from TC.z0 X u) (Fin.cast (Formalism.L2.Forms.rankN (I.rec7 l Z) _ le_rfl) r)) ∧ (∀ n (h : n = B.R.m) x, ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x) ∧ ∀ PP, PP ∈ (_root_.GlobalTheory.Fam.pk_z W).Pg ∨ _root_.GlobalTheory.Fam.QAllAlt W PP → ∃ s : LocX a (_root_.GlobalTheory.Fam.pk_z W).βX PP, (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (s.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos s.FT := by
  first | exact @_root_.GlobalTheory.XGeoStd.exists_xgeo_alt | exact _root_.GlobalTheory.XGeoStd.exists_xgeo_alt | (intros; apply _root_.GlobalTheory.XGeoStd.exists_xgeo_alt <;> assumption)
end
end
